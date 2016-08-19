#!/usr/bin/env python

# Referenced EhsanKia's twitch_vod_clipper.py
# TODO:
#   - Don't delete status file if ffmpeg concat doesn't work (catch exception from check_call)
#     and output status file from already_downloaded
#   - Meaningful network connectivity error messages (when the program stops)
#   - Make num_workers be the number of cores on running system
#   - Download progress indicator of what file out of how many files total
#     are being downloaded (e.g. "[1 of 20]", "[17 of 20]", etc.)
#   - Update help message to reflect resuming download feature
#   - Handle other types of VODs (highlights, maybe?)
#   - Conform to PEP 8 suggestions

import subprocess
import requests
import m3u8
import sys
import re
import os
import errno
import argparse
import textwrap
import unicodedata
import hashlib
import signal

from multiprocessing import Pool, Process, Queue
from itertools import count, izip, takewhile
from progressbar import Bar, ETA, FileTransferSpeed, Percentage, ProgressBar

class MalformedTimestampError(Exception): pass
class MalformedURLError(Exception): pass
class MissingFilenameError(Exception): pass
class InvalidFilenameExtensionError(Exception): pass
class NoContentLengthError(Exception): pass
class UnexpectedEOFError(Exception): pass
class ContentLengthMismatchError(Exception): pass
class DownloadFailedError(Exception): pass

class CustomHelpFormatter(argparse.RawTextHelpFormatter):
    def _format_action_invocation(self, action):
        if not action.option_strings:
            metavar, = self._metavar_formatter(action, action.dest)(1)
            return metavar
        else:
            return ", ".join(action.option_strings)

tlist = []
job_queue = None
result_queue = None

def reset_workers_and_queues():
    global tlist
    global job_queue
    global result_queue
    for t in tlist:
        t.terminate()
        t.join()
    tlist = []
    job_queue = None
    result_queue = None

def get_vod_index(vod_id):
    VOD_API = "https://api.twitch.tv/api/vods/{}/access_token"
    INDEX_API = "http://usher.twitch.tv/vod/{}"
    VIDEO_QUALITY = ["Source", "High", "Medium", "Low", "Mobile"]
    url = VOD_API.format(vod_id)
    r = requests.get(url)
    data = r.json()

    url = INDEX_API.format(vod_id)
    payload = {'nauth': data['token'], 'nauthsig': data['sig'], 'allow_source': 'true'}
    r = requests.get(url, params = payload)

    m = m3u8.loads(r.content)
    quality = VIDEO_QUALITY[0]
    url = m.playlists[0].uri
    return [m3u8.load(url), quality]

def get_vod_info(video_type, vod_id):
    if video_type == "b":
        video_type = "a"
    API_URL = "https://api.twitch.tv/kraken/videos/{}{}"
    headers = {'Accept': 'application/vnd.twitchtv.v3+json'}
    r = requests.get(API_URL.format(video_type, vod_id), headers = headers)
    try:
        r.raise_for_status()
    except requests.exceptions.HTTPError as e:
        raise requests.exceptions.HTTPError(r.status_code, r.reason, response = e.response)

    rjson = r.json()
    url = rjson['url']
    title = rjson['title']
    duration = rjson['length']
    return [url, title, duration]

def get_vod_chunks(index, start_time, end_time):
    CHUNK_RE = "(.+\.ts)\?start_offset=(\d+)&end_offset=(\d+)"
    URL_FMT = "{}?start_offset={}&end_offset={}"
    position = 0
    pieces = []

    for seg in index.segments:
        position += seg.duration

        if position < start_time:
            continue

        p = re.match(CHUNK_RE, seg.absolute_uri)
        filename, start_byte, end_byte = p.groups()

        if not pieces or pieces[-1][0] != filename:
            pieces.append([filename, start_byte, end_byte])
        else:
            pieces[-1][2] = end_byte

        if position > end_time:
            break

    urls_filenames = map(lambda x: [URL_FMT.format(*x), x[0].split('/')[-1]], pieces)

    return urls_filenames

def get_old_style_vod_chunks(vod_id, start_time, end_time):
    VOD_API = "https://api.twitch.tv/api/videos/a{}"
    headers = {'Accept': 'application/vnd.twitchtv.v2+json'}
    api_url = VOD_API.format(vod_id)
    r = requests.get(api_url, headers = headers).json()
    chunks = r["chunks"]["live"]

    position = 0
    urls = []
    for seg in chunks:
        position += seg["length"]

        if position < start_time:
            continue

        urls.append(seg["url"])

        if position > end_time:
            break

    urls_filenames = map(lambda x: [x, x.split('/')[-1]], urls)
    return urls_filenames

def create_directory(path):
    if path:
        try:
            os.makedirs(path)
        except OSError as e:
            if e.errno != errno.EEXIST:
                raise

def delete_file(path):
    try:
        os.remove(path)
    except OSError as e:
        if e.errno != errno.ENOENT:
            raise

def path_and_file(path):
    exp_path = os.path.expanduser(path)
    exp_path, fname = os.path.split(exp_path)
    exp_path = os.path.abspath(exp_path)

    path = path.decode('utf-8')
    exp_path = exp_path.decode('utf-8')
    fname = fname.decode('utf-8')

    if not fname:
        raise MissingFilenameError(path)
    if not valid_output_filename(fname):
        raise InvalidFilenameExtensionError(fname)

    return [exp_path, fname]

def valid_output_filename(fname):
    FNAME_RE = re.compile(".+\.(flv|mp4)$", re.IGNORECASE)
    return True if FNAME_RE.match(fname) else False

def seconds_to_timestamps(s):
    hours = s / 3600
    rem = s % 3600
    minutes = rem / 60
    seconds = rem % 60

    if s == 0:
        t_hms = "0s"
        t_verb = "0 seconds"
    else:
        t_hms_list = []
        t_verb_list = []
        if hours > 0:
            h_suff = "hour" if hours == 1 else "hours"
            t_verb_list.append("{} {}".format(hours, h_suff))
            t_hms_list.append("{}h".format(hours))
        if minutes > 0:
            m_suff = "minute" if minutes == 1 else "minutes"
            t_verb_list.append("{} {}".format(minutes, m_suff))
            t_hms_list.append("{}m".format(minutes))
        if seconds > 0:
            s_suff = "second" if seconds == 1 else "seconds"
            t_verb_list.append("{} {}".format(seconds, s_suff))
            t_hms_list.append("{}s".format(seconds))
        t_hms = " ".join(t_hms_list)
        t_verb = " ".join(t_verb_list)

    t_std = "{}:{:02d}:{:02d}".format(hours, minutes, seconds)

    return [t_std, t_hms, t_verb]

def timestamp_to_seconds(timestamp):
    if ":" in timestamp:
        parsed_time = timestamp.split(":")
        if len(parsed_time) != 3:
            raise MalformedTimestampError(timestamp)
        try:
            parsed_time = map(int, parsed_time)
        except ValueError:
            raise MalformedTimestampError(timestamp)
        return parsed_time[0] * 3600 + parsed_time[1] * 60 + parsed_time[2]
    else:
        hms = {'h': 3600, 'H': 3600,
               'm': 60,   'M': 60,
               's': 1,    'S': 1}
        parsed_time = filter(lambda x: x, re.split('(\d+)([hmsHMS])', timestamp))
        ptlen = len(parsed_time)
        seconds = 0
        if ptlen == 1:
            try:
                seconds = int(parsed_time[0])
                if seconds < 0:
                    raise MalformedTimestampError(timestamp)
            except ValueError:
                raise MalformedTimestampError(timestamp)
        elif ptlen % 2 != 0:
            raise MalformedTimestampError(timestamp)
        else:
            try:
                for i in xrange(0, ptlen, 2):
                    seconds += int(parsed_time[i]) * hms[parsed_time[i + 1]]
            except (ValueError, KeyError):
                raise MalformedTimestampError(timestamp)
        return seconds

def get_download_jobs(url, size, part_size):
    jobs = []
    upper_bytes = size - 1
    if part_size > size:
        jobs.append((url, 0, upper_bytes))
        return jobs
    ranges_iter = izip(count(0, part_size), count(part_size - 1, part_size))
    ranges_iter = takewhile(lambda x: x[1] < size, ranges_iter)
    for start_byte, end_byte in ranges_iter:
        jobs.append((url, start_byte, end_byte))
    l_url, start, end = jobs.pop()
    jobs.append((url, start, upper_bytes))
    return jobs

def part_dl():
    global job_queue
    global result_queue
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    CONNECT_TIMEOUT = 4  # seconds
    READ_TIMEOUT = 10    # seconds
    CHUNK_SIZE = 512     # 8-bit bytes

    while True:
        url, start_byte, end_byte = job_queue.get()
        expected_length = end_byte - start_byte + 1
        curr_byte = start_byte
        data_len = 0

        headers = {'Range': 'bytes={}-'.format(start_byte)}
        try:
            r = requests.get(url, stream = True, headers = headers, timeout = (CONNECT_TIMEOUT, READ_TIMEOUT))
        except requests.exceptions.RequestException as e:
            result_queue.put((None, None, None, "download_failed"))
            #status_code, reason = e.args
            #if status_code == 416:
            #    raise UnexpectedEOFError("HTTP Error 416 Requested Range not satisfiable")

        try:
            for chunk in r.iter_content(chunk_size = CHUNK_SIZE):
                if not chunk: # filter out keep-alive new chunks
                    continue
                cl = len(chunk)
                if data_len + cl > expected_length:
                    # Not really necessary (since writing the empty string b'' to a file is
                    # essentially a noop, i.e. it doesn't change the file), but this inexpensive
                    # comparison will save us the effort of a few calculations, a write to the result
                    # queue, and an empty "write" to the file in the case that this condition is met
                    if data_len == expected_length:
                        break
                    bytes_over = data_len + cl - expected_length
                    tmp = chunk[:(cl - bytes_over)]
                    tmp_len = len(tmp)
                    result_queue.put((curr_byte, tmp_len, tmp, None))
                    data_len += tmp_len
                    curr_byte += tmp_len
                    break
                result_queue.put((curr_byte, cl, chunk, None))
                data_len += cl
                curr_byte += cl
            r.close()

            # Verify that the size of the data (in bytes) we downloaded is exactly identical
            # to the expected size (in bytes). If the stream cuts out early, data_len will be
            # less than expected_length, so we check for that here
            if data_len != expected_length:
                raise ContentLengthMismatchError("Expected length: {} bytes. Actual length: {} bytes."
                                                 .format(expected_length, data_len))
        except (ContentLengthMismatchError, requests.exceptions.RequestException) as e:
            result_queue.put((None, None, None, "download_failed"))

def parallel_download(url, dir_path, filename, num_workers = 4):
    global tlist
    global job_queue
    global result_queue
    CONNECT_TIMEOUT = 4   # seconds
    READ_TIMEOUT = 120    # seconds
    CHUNK_SIZE = 512      # 8-bit bytes
    bytes_downloaded = 0  # 8-bit bytes

    # Get content length of file, in bytes
    r = requests.get(url, stream = True, timeout = (CONNECT_TIMEOUT, READ_TIMEOUT))
    content_length = r.headers['content-length']
    r.close()
    if content_length:
        content_length = int(content_length)
    else:
        raise NoContentLengthError("No 'content-length' header returned by server.")

    # Calculate job size for each process (portion out evenly to each process)
    # If the size of content_length (in bytes) is smaller than the number of workers,
    # or smaller than CHUNK_SIZE (an unlikely scenario, but not impossible) simply
    # spawn only one worker to download the entire file by itself
    job_size = content_length / num_workers
    if job_size == 0 or content_length < CHUNK_SIZE:
        job_size = content_length

    # Construct list of jobs, where each job is a triple (3-tuple)
    # With the above-defined job size, the number of jobs is the
    # same as the number of processes.
    jobs = get_download_jobs(url, content_length, job_size)

    if not job_queue:
        job_queue = Queue()

    if not result_queue:
        result_queue = Queue()

    # Put jobs on job queue
    for job in jobs:
        job_queue.put(job)

    # If worker list is empty, create and start worker processes
    if not tlist:
        for _ in xrange(num_workers):
            t = Process(target = part_dl)
            tlist.append(t)
            t.start()

    # Create empty file of size content_length bytes
    # (the output file, to be written later)
    with open(os.path.join(dir_path, filename), "wb") as f:
        f.seek(content_length - 1)
        f.write("\0")
        f.flush()
        os.fsync(f.fileno())

    try:
        # Collect each downloaded chunk from result_queue and write to output file
        print "Downloading {} ({:.1f} MB)".format(filename, content_length / float(1024**2))
        widgets = [Percentage(), ' ', Bar('=', '[', ']'), ' ', ETA(), ' ', FileTransferSpeed()]
        pbar = ProgressBar(widgets = widgets, maxval = content_length, term_width  = 80)
        pbar.start()
        with open(os.path.join(dir_path, filename), "r+b") as f:
            while bytes_downloaded < content_length:
                start_byte, chunk_length, chunk, err = result_queue.get()
                if err:
                    print "\n\nDownload attempt failed, retrying...\n"
                    reset_workers_and_queues()
                    raise DownloadFailedError(filename)
                f.seek(start_byte)
                f.write(chunk)
                bytes_downloaded += chunk_length
                pbar.update(bytes_downloaded)
            f.flush()
            os.fsync(f.fileno())
        pbar.finish()
        sys.stdout.write("\n")

    except KeyboardInterrupt:
        reset_workers_and_queues()
        raise

def download_file(url, dir_path, filename):
    CONNECT_TIMEOUT = 4  # seconds
    READ_TIMEOUT = 30    # seconds
    CHUNK_SIZE = 1024    # 8-bit bytes
    bytes_downloaded = 0
    r = requests.get(url, stream = True, timeout = (CONNECT_TIMEOUT, READ_TIMEOUT))
    content_length = r.headers['content-length']
    if content_length:
        content_length = int(content_length)
    else:
        raise NoContentLengthError("No 'content-length' header returned by server.")
    print "Downloading {} ({:.1f} MB)".format(filename, content_length / float(1024**2))
    widgets = [Percentage(), ' ', Bar('=', '[', ']'), ' ', ETA(), ' ', FileTransferSpeed()]
    pbar = ProgressBar(widgets = widgets, maxval = content_length, term_width  = 80)
    pbar.start()
    with open(os.path.join(dir_path, filename), "wb") as f:
        for chunk in r.iter_content(chunk_size = CHUNK_SIZE):
            if not chunk: # filter out keep-alive new chunks
                continue
            f.write(chunk)
            bytes_downloaded += len(chunk)
            pbar.update(bytes_downloaded)
        f.flush()
        os.fsync(f.fileno())
    pbar.finish()
    sys.stdout.write("\n")

    if bytes_downloaded != content_length:
        raise ContentLengthMismatchError("Expected length: {} bytes. Actual length: {} bytes."
                                         .format(expected_length, data_len))

def create_status_file(status_path, already_downloaded):
    with open(status_path, "w") as f:
        for fname, md5 in already_downloaded:
            f.write("{} {}\n".format(fname, md5))
        f.flush()
        os.fsync(f.fileno())

def download_and_merge(urls_filenames, dir_path, vod_id, outfname):
    global tlist
    status_filename = "{}.twitchvod-status".format(vod_id)
    filenames = [fname for url, fname in urls_filenames]
    already_downloaded = []
    can_skip = []

    # Check for existence of a status file associated with this VOD.
    # If found, load its contents into memory (a status file
    # contains the filename and MD5 checksum of each successfully
    # downloaded file, for resuming interrupted/incomplete downloads)
    status_path = os.path.join(dir_path, status_filename)
    if os.path.exists(status_path):
        with open(status_path, "r") as f:
            for line in f:
                already_downloaded.append(tuple(line.split()))

        currymatching = lambda d: lambda x: (os.path.exists(os.path.join(d, x[0])) and
                                             x[1] == md5checksum(d, x[0]))
        matchingfile = currymatching(dir_path)
        already_downloaded = filter(matchingfile, already_downloaded)
        can_skip = [fname for fname, _ in already_downloaded if fname in filenames]

    # Save current working directory (the user's current working directory
    # when this program was originally called)
    cwd = os.getcwd()
    os.chdir(dir_path)

    try:
        for url, fname in urls_filenames:
            if fname in can_skip:
                print "{} already exists (verified by MD5 checksum)\n".format(fname)
            else:
                try:
                    parallel_download(url, dir_path, fname)
                except DownloadFailedError:
                    download_file(url, dir_path, fname)
                already_downloaded.append((fname, md5checksum(dir_path, fname)))
    except (KeyboardInterrupt, requests.exceptions.ConnectionError,
            requests.exceptions.Timeout, requests.exceptions.RequestException,
            ContentLengthMismatchError, NoContentLengthError) as e:
        if isinstance(e, KeyboardInterrupt):
            msg = "Download canceled."
        else:
            msg = "Download failed due to connectivity issues:\n{}".format(e)
        print "\n\n{}".format(msg)
        if already_downloaded:
            print ("\nSome parts were successfully downloaded.\n"
                   "A log of these files has been written to:\n"
                   "'{}'.\n"
                   "Re-run this program to auto-resume download.".format(status_path))
            create_status_file(status_path, already_downloaded)
        sys.exit(1)

    # At this point, all the downloading work is done,
    # so kill all the worker processes
    if tlist:
        reset_workers_and_queues()

    tmpfname = "{}.tmp".format(vod_id)
    with open(tmpfname, "w") as f:
        for fname in filenames:
            f.write("file '{}'\n".format(fname))
        f.flush()
        os.fsync(f.fileno())

    print "Concatenating video files with ffmpeg..."
    subprocess.check_call(["ffmpeg", "-loglevel", "error", "-y", "-f", "concat", "-i", tmpfname,
                           "-bsf:a", "aac_adtstoasc", "-c", "copy", outfname])
    print "Done.\n"

    # Filter out files that have already been downloaded and merged into the final ouput VOD.
    # If already_downloaded still contains entries after that (e.g. files from a different
    # download session that was interrupted), create a new status file from its contents.
    # Otherwise, if already_downloaded is empty, then we no longer need the status file.
    already_downloaded = [t for t in already_downloaded if t[0] not in filenames]
    if already_downloaded:
        create_status_file(status_path, already_downloaded)
    else:
        delete_file(status_filename)

    print "Cleaning up temporary files..."
    for f in filenames:
        delete_file(f)
    delete_file(tmpfname)
    print "Done.\n"

    # Restore current working directory
    os.chdir(cwd)

def md5checksum(dir_path, filename, blocksize = 2**20):
    m = hashlib.md5()
    with open(os.path.join(dir_path, filename), "rb") as f:
        while True:
            buf = f.read(blocksize)
            if not buf:
                break
            m.update(buf)
    return m.hexdigest()

def vlen(s):
    if isinstance(s, unicode):
        width = 0
        for c in unicodedata.normalize("NFC", s):
            if unicodedata.east_asian_width(c) in ("W", "F"):
                width += 2
            elif not unicodedata.combining(c):
                width += 1
        return width
    else:
        return len(s)

def truncate_string(string, num_chars, location):
    num_chars = abs(num_chars)
    addendum = '...' if num_chars > 3 else ''
    visual_length = 0
    tstr = []
    if vlen(string) > num_chars:
        if location == "left":
            for c in reversed(string):
                charlen = vlen(c)
                if visual_length + charlen > num_chars - vlen(addendum):
                    break
                else:
                    tstr.append(c)
                    visual_length += charlen
            tstr.append(addendum)
            return "".join(reversed(tstr))
        else:
            for c in string:
                charlen = vlen(c)
                if visual_length + charlen > num_chars - vlen(addendum):
                    break
                else:
                    tstr.append(c)
                    visual_length += charlen
            tstr.append(addendum)
            return "".join(tstr)
    return string

def print_status(title, quality, url, start, end, dir_path, outfname):
    start_ts = seconds_to_timestamps(start)[0]
    end_ts = seconds_to_timestamps(end)[0]
    duration = seconds_to_timestamps(end - start)[2]

    fmt_title = truncate_string(title, 70, "right")
    fmt_path = truncate_string(os.path.join(dir_path, outfname), 70, "left")

    lines = [u'Downloading "{}" ({})'.format(fmt_title, quality),
             "url: {}".format(url),
             "from {} to {} ({})".format(start_ts, end_ts, duration),
             u"saving to: {}".format(fmt_path)]

    width = reduce(lambda x, y: x if x > y else y, map(lambda x: vlen(x), lines))
    # equivalent to int(math.ceil(width / 2.0))
    n = width / 2 + width % 2
    spaced_lines = map(lambda x: x + " " * (2 * n - vlen(x)), lines)
    topbottom = "+ - " + "- " * n + "- - +"
    empty_line = "|" + " " * (3 + 2 * n + 4) + "|"

    print topbottom
    print empty_line
    for line in spaced_lines:
        print "|   " + line + "    |"
    print empty_line
    print topbottom

def validate_time_range(start, end, vod_len, duration):
    try:
        start_s = timestamp_to_seconds(start)
        if vod_len:
            length_s = timestamp_to_seconds(vod_len)
            end_s = start_s + length_s
        elif not end:
            end_s = duration
        else:
            end_s = timestamp_to_seconds(end)
    except MalformedTimestampError as e:
        print_and_exit('Error: Invalid timestamp "{}"'.format(e))

    if end_s > duration:
        end_s = duration

    if start_s >= end_s:
        start_ts = seconds_to_timestamps(start_s)[0]
        end_ts = seconds_to_timestamps(end_s)[0]
        print_and_exit("Warning: Start time ({}) is greater than or equal to the end time ({}),\n"
                       "so there is nothing to download.".format(start_ts, end_ts))

    return [start_s, end_s]

def extract_from_url(url):
    info = {}
    URL_RE = re.compile(r"""
        (?:
            http(s)?://
        )?
        (?:
            (?P<subdomain>[\w\-]+)
            \.
        )?
        twitch\.tv
        /
        (?P<channel>[^/]+)
        /
        (?P<video_type>[bcv])
        /
        (?P<video_id>\d+)
        $
        """, re.VERBOSE)

    m = URL_RE.match(url)
    if not m:
        raise MalformedURLError(url)
    match = m.groupdict()
    info["subdomain"] = match.get("subdomain")
    info["channel"] = match.get("channel").lower()
    info["video_type"] = match.get("video_type")
    info["video_id"] = match.get("video_id")
    return info

def print_and_exit(error_msg):
    print u"\n{}".format(error_msg)
    print "\nTry '{} --help' for more information.".format(sys.argv[0])
    sys.exit(1)

if __name__ == "__main__":
    description = textwrap.dedent("""
        Twitch VOD Downloader
        ---------------------
        Download VODs (Past Broadcasts) from the popular streaming site, twitch.tv

        Timestamp arguments are optional. If you don't include them, the entire VOD
        will be downloaded. Sometimes VODs can be extremely lengthy, e.g. 14+ hours
        long. To download only a part of the VOD, you can include timestamps to
        specify the desired range. Note that because of the way Twitch stores its
        VODs, the final output file's duration may be larger than your specified
        time range.

          Valid timestamp formats
          -----------------------
          Timestamps follow a few common formats: hh:mm:ss, a number followed
          by the suffix 'h', 'm', or 's', or simply a number (which is assumed to be
          in seconds). All of the following are examples of valid timestamps:

          2:45:09         2h24m9s         9909        3600s       184m        3h
          11:54:18        0:128:34        7h15m       1h59s       2m30s       999m999s

          Examples of usage
          -----------------
          twitchvod.py <vod_url> -s 1h -e 1h30m -o out.flv
          twitchvod.py <vod_url> -s 0:19:00 -e 1:20:37 -o out.flv
          twitchvod.py <vod_url> -s 10m -d 2h30m -o out.flv
    """)
    parser = argparse.ArgumentParser(add_help = False,
                 formatter_class = CustomHelpFormatter,
                 usage = "%(prog)s [options] vod_url",
                 description = description)
    group = parser.add_mutually_exclusive_group()
    parser.add_argument("vod_url",
                        help = "URL of the VOD to download, e.g.\n"
                               "http://www.twitch.tv/srkevo2/v/7959482")
    parser.add_argument("-h", "--help", action = "help",
                        help = "Show this help message and exit\n\n")
    parser.add_argument("-s", "--start", default = "0", metavar = "",
                        help = "Start timestamp. Designates the beginning of your desired\n"
                               "part of the VOD. If omitted, the default value is 0,\n"
                               "corresponding to the beginning of the VOD\n\n")
    group.add_argument("-e", "--end", default = None, metavar = "",
                        help = "End timestamp. Designates the end of your desired\n"
                               "part of the VOD. If omitted, and no duration is specified,\n"
                               "the end of the VOD is assumed\n\n")
    group.add_argument("-d", "--duration", default = None, metavar = "",
                       help = "Desired length of video. Specify this using the\n"
                              "timestamp formatting shown above. This option cannot\n"
                              "be used in conjunction with the end timestamp option\n"
                              "(-e or --end)\n\n")
    parser.add_argument("-o", "--output", default = "out.flv", metavar = "",
                        help = "Output filepath of VOD. Output file must end with either the\n"
                               "*.flv or *.mp4 extension. You may provide just a filename,\n"
                               "e.g. 'foo.flv' -- then the VOD will be saved with that name\n"
                               "to the current working directory. You can also provide a\n"
                               "filepath like '~/vods/abc.flv'. If omitted, the default is\n"
                               "simply './out.flv'")
    # Print help/usage message if the program is called without any arguments
    if len(sys.argv) == 1:
        parser.print_help()
        sys.exit(1)

    args = parser.parse_args()

    # Parse VOD URL
    vod_url = args.vod_url
    try:
        urldict = extract_from_url(vod_url)
    except MalformedURLError as e:
        print_and_exit('Error: Invalid Twitch VOD URL "{}"'.format(e))

    video_type = urldict["video_type"]
    vod_id = urldict["video_id"]

    start = args.start
    end = args.end
    vod_len = args.duration
    output_file = args.output

    # Parse output filepath into a directory path and a filename
    # Check both existence and validity of filename
    try:
        dir_path, outfname = path_and_file(output_file)
    except MissingFilenameError as e:
        print_and_exit(u'Error: Missing filename in path "{}"'.format(e))
    except InvalidFilenameExtensionError as e:
        print_and_exit(u'Error: Invalid output filename "{}"\n'
                       'Valid output filename extensions: *.flv, *.mp4'.format(e))

    # Retrieve VOD information
    try:
        url, title, duration = get_vod_info(video_type, vod_id)
    except requests.exceptions.HTTPError as e:
        status_code, reason = e.args
        if 400 <= status_code < 500:
            print "\n{} Client Error: {}\nFor url: {}".format(status_code, reason, vod_url)
        else:
            print e
        sys.exit(1)

    start_s, end_s = validate_time_range(start, end, vod_len, duration)

    if video_type == "v":
        index, quality = get_vod_index(vod_id)
        urls_fnames = get_vod_chunks(index, start_s, end_s)
    elif video_type == "b":
        quality = "Source"
        urls_fnames = get_old_style_vod_chunks(vod_id, start_s, end_s)

    create_directory(dir_path)
    print_status(title, quality, url, start_s, end_s, dir_path, outfname)
    download_and_merge(urls_fnames, dir_path, vod_id, outfname)

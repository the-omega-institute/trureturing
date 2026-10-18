"""Durable reservations and bounded, single-child process execution."""
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess


class Stop(Exception):
    def __init__(self, code, detail=''):
        super().__init__(code)
        self.code, self.detail = code, detail


@dataclass(frozen=True)
class Limits:
    call_seconds: int = 300
    unit_seconds: int = 3600
    wake_seconds: int = 3600
    unit_calls: int = 10
    wake_calls: int = 10
    total_calls: int = 60
    wakes: int = 6

    def __post_init__(self):
        caps = dict(call_seconds=1200, unit_seconds=3600, wake_seconds=3600,
                    unit_calls=60, wake_calls=60, total_calls=60, wakes=6)
        for key, value in asdict(self).items():
            if type(value) is not int or not 0 < value <= caps[key]:
                raise Stop('INVALID_LIMIT', key)


def utc(seconds):
    return datetime.fromtimestamp(seconds, timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def atomic(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    pending = path.with_suffix('.tmp')
    with pending.open('w', encoding='utf-8') as stream:
        os.chmod(pending, 0o600)
        json.dump(value, stream, ensure_ascii=False, allow_nan=False, sort_keys=True)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(pending, path)
    fd = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


@contextmanager
def locked(path):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.with_suffix('.lock').open('a') as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise Stop('ALREADY_RUNNING') from error
        # Children keep the lock if the controller dies, preventing overlapping seats.
        yield stream.fileno()


def execute(argv, root, timeout, stdin='', lock_fd=None):
    if timeout <= 0:
        raise Stop('WALL_BUDGET')
    try:
        child = subprocess.Popen(argv, cwd=root, stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 text=True, start_new_session=True,
                                 pass_fds=() if lock_fd is None else (lock_fd,))
    except OSError as error:
        raise Stop('CAPABILITY_UNAVAILABLE', str(error)) from error
    try:
        out, err = child.communicate(stdin, timeout=timeout)
    except BaseException as error:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        child.communicate()
        if isinstance(error, subprocess.TimeoutExpired):
            raise Stop('WORKER_TIMEOUT') from error
        raise
    if child.returncode:
        raise Stop('COMMAND_FAILED', f'{argv[0]} exit={child.returncode}: {err[-500:]} {out[-500:]}')
    return out


def decode(raw):
    def pairs(values):
        result = {}
        for key, value in values:
            if key in result:
                raise ValueError('duplicate JSON key')
            result[key] = value
        return result
    try:
        return json.loads(raw, object_pairs_hook=pairs,
                          parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
    except (ValueError, TypeError) as error:
        raise Stop('WORKER_MALFORMED', str(error)) from error

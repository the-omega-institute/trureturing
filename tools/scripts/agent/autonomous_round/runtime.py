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
import sys
import time


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
    deadline = time.monotonic() + timeout
    request = dict(argv=argv, deadline=deadline, lock_fd=lock_fd)
    try:
        # This bounded supervisor survives controller death and owns the process-group deadline.
        child = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), json.dumps(request)],
                                 cwd=root, stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 text=True, start_new_session=True,
                                 pass_fds=() if lock_fd is None else (lock_fd,))
    except OSError as error:
        raise Stop('CAPABILITY_UNAVAILABLE', str(error)) from error
    try:
        out, err = child.communicate(stdin, timeout=timeout + 2)
    except BaseException as error:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        child.communicate()
        if isinstance(error, subprocess.TimeoutExpired):
            raise Stop('WORKER_TIMEOUT') from error
        raise
    if child.returncode == -signal.SIGKILL and time.monotonic() >= deadline:
        raise Stop('WORKER_TIMEOUT')
    if child.returncode:
        raise Stop('SUPERVISOR_FAILED', f'exit={child.returncode}: {err[-500:]}')
    result = decode(out)
    if result['code']:
        raise Stop(result['reason'], f'{argv[0]} exit={result["code"]}: '
                   f'{result["stderr"][-500:]} {result["stdout"][-500:]}')
    return result['stdout']


def supervise(request):
    """One bounded child, no continuation. Parent and worker share this process group."""
    fd = request['lock_fd']
    def stop_group(signum, frame):
        os.killpg(os.getpgrp(), signal.SIGKILL)
    signal.signal(signal.SIGTERM, stop_group)
    signal.signal(signal.SIGINT, stop_group)
    if time.monotonic() >= request['deadline']:
        os.killpg(os.getpgrp(), signal.SIGKILL)
    try:
        child = subprocess.Popen(request['argv'], stdin=sys.stdin, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True, errors='replace',
                                 pass_fds=() if fd is None else (fd,))
    except OSError as error:
        return dict(code=127, reason='CAPABILITY_UNAVAILABLE', stdout='', stderr=str(error))
    try:
        out, err = child.communicate(timeout=max(0, request['deadline'] - time.monotonic()))
    except BaseException:
        # Includes the supervisor: no controller is needed to kill orphaned descendants.
        os.killpg(os.getpgrp(), signal.SIGKILL)
        raise AssertionError('unreachable')
    return dict(code=child.returncode, reason='COMMAND_FAILED', stdout=out, stderr=err)


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


if __name__ == '__main__':
    print(json.dumps(supervise(json.loads(sys.argv[1]))))

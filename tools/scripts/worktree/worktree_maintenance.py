#!/usr/bin/env python3
"""Clone-local maintenance notifications and a host-supervised exclusive worker."""
import argparse
from contextlib import contextmanager
from contextvars import ContextVar
import fcntl
import hashlib
import json
import os
from pathlib import Path
import plistlib
import shutil
import stat
import subprocess
import sys
import uuid

sys.path.insert(0, str(Path(__file__).resolve().parent))
# Nested adapters must share the script entry point's reentrant lock state.
if __name__ == "__main__":
    sys.modules["worktree_maintenance"] = sys.modules[__name__]
from worktree_protocol import GitFailure, common, inventory

_HELD = ContextVar("worktree_maintenance_locks", default={})
INTERVAL_SECONDS = 900


def directory(source):
    root = common(source) / "worktree-maintenance"
    root.mkdir(mode=0o700, exist_ok=True)
    return root


@contextmanager
def lease(source, *, shared=False, blocking=True):
    """Serialize disposal and allocation; nonblocking callers can create elsewhere."""
    with _lock(directory(source) / "lock", shared=shared, blocking=blocking):
        yield


@contextmanager
def initialization(source, path):
    """Protect one initialization transaction, without waiting for maintenance."""
    root = common(source) / "worktree-initialization"
    root.mkdir(mode=0o700, exist_ok=True)
    key = hashlib.sha256(os.fsencode(Path(path).resolve())).hexdigest()
    with _lock(root / (key + ".lock"), shared=False, blocking=False):
        yield


@contextmanager
def _lock(path, *, shared, blocking):
    held = _HELD.get()
    if path in held:
        if held[path] and not shared:
            raise RuntimeError("maintenance lock upgrade is forbidden")
        yield
        return
    descriptor = os.open(path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    try:
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid() or info.st_nlink != 1:
            raise OSError("invalid maintenance lock")
        mode = fcntl.LOCK_SH if shared else fcntl.LOCK_EX
        fcntl.flock(descriptor, mode | (0 if blocking else fcntl.LOCK_NB))
        token = _HELD.set(held | {path: shared})
        try:
            yield
        finally:
            _HELD.reset(token)
    finally:
        os.close(descriptor)


def notify(source):
    """Publish one durable event, without waiting for or running maintenance."""
    try:
        root = directory(source)
        requests = root / "requests"
        requests.mkdir(mode=0o700, exist_ok=True)
        (requests / uuid.uuid4().hex).touch(mode=0o600, exist_ok=False)
        return dict(status="queued", service_installed=(root / "service.json").is_file())
    except (OSError, GitFailure, subprocess.SubprocessError) as error:
        return dict(status="unavailable", reason=str(error))


def _write_json(path, value):
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex)
    try:
        with temporary.open("x") as output:
            json.dump(value, output, sort_keys=True)
            output.write("\n")
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def run(source):
    """The host owns worker lifetime; events arriving during a sweep remain pending."""
    from worktree_pool import sweep
    root = directory(source)
    try:
        with lease(source, blocking=False):
            rows = inventory(source)
            anchor = Path(rows[0]["worktree"])
            requests = root / "requests"
            requests.mkdir(mode=0o700, exist_ok=True)
            batch = list(requests.iterdir())
            result = sweep(anchor, "HEAD", force=True)
            if result["status"] != "failed":
                for request in batch:
                    request.unlink(missing_ok=True)
            result = dict(event="worktree_maintenance", **{k: v for k, v in result.items()
                          if k != "event"}, requests_consumed=len(batch) if result["status"] != "failed" else 0)
            _write_json(root / "status.json", result)
            return result
    except BlockingIOError:
        return dict(event="worktree_maintenance", status="busy", requests_consumed=0)


def _service_identity(root):
    return "org.trureturing.worktree-maintenance." + hashlib.sha256(os.fsencode(root)).hexdigest()[:16]


def _systemd_quote(value):
    return '"' + str(value).replace("%", "%%").replace("\\", "\\\\").replace('"', '\\"') + '"'


def _systemd_path(value):
    # PathChanged= is an absolute scalar, not an ExecStart= shell-like word.
    return str(value).replace("%", "%%").replace("\\", "\\\\").replace("\n", "\\n").replace("\r", "\\r")


def install(source):
    """Install one stable runtime projection, independent of disposable worktrees."""
    root = directory(source)
    anchor = Path(inventory(source)[0]["worktree"]).resolve()
    label = _service_identity(root)
    requests = root / "requests"
    requests.mkdir(mode=0o700, exist_ok=True)
    runtime = root / "runtime"
    runtime.mkdir(mode=0o700, exist_ok=True)
    code = Path(__file__).resolve().parent
    # Every installed module has a tracked source; only this active projection is kept.
    with lease(source):
        for name in ("worktree_maintenance", "worktree_protocol", "worktree_pool",
                     "worktree_preservation", "worktree_agent_state", "worktree_publication"):
            temporary = runtime / (name + ".py.new")
            shutil.copyfile(code / (name + ".py"), temporary)
            temporary.replace(runtime / (name + ".py"))
        shutil.copyfile(code.parent / "maintenance_log.py", runtime / "maintenance_log.py")
    command = [sys.executable, "-B", str(runtime / "worktree_maintenance.py"),
               "--source", str(anchor), "run"]
    if sys.platform == "darwin":
        domain = "gui/" + str(os.getuid())
        target = domain + "/" + label
        path = Path.home() / "Library/LaunchAgents" / (label + ".plist")
        path.parent.mkdir(parents=True, exist_ok=True)
        configuration = dict(Label=label, ProgramArguments=command, RunAtLoad=True,
            StartInterval=INTERVAL_SECONDS, WatchPaths=[str(requests)], WorkingDirectory=str(anchor),
            ProcessType="Background", StandardOutPath=str(root / "worker.log"),
            StandardErrorPath=str(root / "worker.log"))
        if path.exists():
            subprocess.run(["launchctl", "bootout", target], capture_output=True, check=False)
        with path.open("wb") as output:
            plistlib.dump(configuration, output)
        subprocess.run(["launchctl", "bootstrap", domain, str(path)], check=True)
        service = dict(manager="launchd", target=target, files=[str(path)], scope="user-login")
    elif sys.platform.startswith("linux"):
        units = Path.home() / ".config/systemd/user"
        units.mkdir(parents=True, exist_ok=True)
        service_path = units / (label + ".service")
        path_unit = units / (label + ".path")
        timer = units / (label + ".timer")
        service_path.write_text("[Unit]\nDescription=Trureturing worktree maintenance\n[Service]\n"
            "Type=oneshot\nExecStart=" + " ".join(map(_systemd_quote, command)) + "\n")
        path_unit.write_text("[Path]\nPathChanged=" + _systemd_path(requests) +
                            "\n[Install]\nWantedBy=default.target\n")
        timer.write_text("[Timer]\nOnStartupSec=60\nOnUnitActiveSec=" + str(INTERVAL_SECONDS) +
                         "\n[Install]\nWantedBy=timers.target\n")
        subprocess.run(["systemctl", "--user", "daemon-reload"], check=True)
        subprocess.run(["systemctl", "--user", "enable", "--now", label + ".path", label + ".timer"], check=True)
        service = dict(manager="systemd", target=label, files=list(map(str, (service_path, path_unit, timer))),
                       scope="user-session")
    else:
        raise OSError("maintenance service requires launchd or systemd --user")
    _write_json(root / "service.json", service)
    return dict(status="installed", **service, notification=notify(source))


def uninstall(source):
    root = directory(source)
    path = root / "service.json"
    service = json.loads(path.read_text())
    if service["manager"] == "launchd":
        subprocess.run(["launchctl", "bootout", service["target"]], check=True)
    else:
        subprocess.run(["systemctl", "--user", "disable", "--now",
                        service["target"] + ".path", service["target"] + ".timer"], check=True)
        subprocess.run(["systemctl", "--user", "stop", service["target"] + ".service"], check=True)
    for filename in service["files"]:
        Path(filename).unlink(missing_ok=True)
    path.unlink()
    return dict(status="uninstalled")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path.cwd())
    parser.add_argument("action", choices=("notify", "run", "install", "uninstall", "status"))
    options = parser.parse_args(argv)
    try:
        if options.action == "status":
            root = directory(options.source)
            result = dict(service=json.loads((root / "service.json").read_text())
                          if (root / "service.json").exists() else None,
                          last_run=json.loads((root / "status.json").read_text())
                          if (root / "status.json").exists() else None,
                          pending=len(list((root / "requests").glob("*"))))
        else:
            result = globals()[options.action](options.source)
        print(json.dumps(result), flush=True)
        return 1 if result.get("status") in ("failed", "unavailable") else 0
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        print(json.dumps(dict(status="failed", reason=str(error))), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

"""Owned disposable children exercise the real ensure/Release interruption boundary."""
import contextlib
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest


def wait_for(path, process):
    deadline = time.monotonic() + 15
    while not path.exists():
        if process.poll() is not None:
            raise AssertionError(process.communicate())
        if time.monotonic() >= deadline:
            raise AssertionError("fixture did not reach its interruption barrier")
        time.sleep(0.01)


def archive_child(repository, root, mode):
    sys.path.insert(0, str(repository / "tools/scripts/worktree"))
    import lean_cache_release as release

    def operation():
        if mode == "transport":
            release.checked_run([sys.executable, __file__, "transport", str(root)],
                                time.monotonic() + 60)
            return 0
        target = root / ".lake/build"
        target.mkdir()
        (target / "previous").write_text("original build")
        base = root / release.report_reuse.BASE_RECORD
        base.parent.mkdir(parents=True, exist_ok=True)
        base.write_text("original base")
        stage = root / "assets"
        stage.mkdir()
        source = root / "replacement/build"
        source.mkdir(parents=True)
        (source / "replacement").write_text("new build")
        with tarfile.open(stage / release.ASSET, "w:gz") as archive:
            archive.add(source, arcname="build")
        packed = (stage / release.ASSET).read_bytes()
        part = dict(name=release.ASSET, bytes=len(packed), sha256=hashlib.sha256(packed).hexdigest())
        manifest = dict(producer_commit_sha="a" * 40, archive_bytes=len(packed),
                        archive_sha256=part["sha256"])
        release.snapshot_manifest = lambda *args, **kwargs: ({"assets": []}, manifest, [part])
        release.gh = lambda *args: ""
        release.report_reuse.record_seed_base = lambda *args: False

        def installed():
            (root / "ready").write_text(str(os.getpid()))
            signal.pause()

        release.restore_snapshot(root, "partition", "tag", stage, time.monotonic() + 60,
                                 cache_key={}, refresh_stale=True, on_installed=installed)
        return 0

    release._main = operation
    raise SystemExit(release.main())


class InterruptionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="cache-interrupt-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.home = self.root / "home"
        self.home.mkdir()
        self.env = {**os.environ, "HOME": str(self.home), "LAKE_BIN": shutil.which("true"),
                    "TRURETURING_MAINTENANCE_SCRIPT": "lean-cache-ensure",
                    "TRURETURING_MAINTENANCE_REPOSITORY": str(self.root),
                    "TRURETURING_MAINTENANCE_LOG_DIR": str(self.root / "maintenance"),
                    "STRATALINT_INSPECTOR_PHASES": str(self.root / "phases")}
        for name in ("TRURETURING_MAINTENANCE_RUN_ID", "TRURETURING_MAINTENANCE_PARENT_RUN_ID"):
            self.env.pop(name, None)
        subprocess.run(["git", "init", "--initial-branch=dev", str(self.root)],
                       check=True, capture_output=True)
        for name in ("lean-toolchain", "lake-manifest.json", "Reg/lakefile.toml", "Reg/lake-manifest.json",
                     "tools/lean-inspector-reg/lakefile.toml", "tools/lean-inspector-reg/lake-manifest.json"):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPOSITORY / name, target)
        revision = next(package["rev"] for package in json.loads(
            (self.root / "lake-manifest.json").read_text())["packages"] if package["name"] == "mathlib")
        lake = self.root / ".lake"
        mathlib = lake / "packages/mathlib/.lake/build/lib/lean/Mathlib"
        mathlib.mkdir(parents=True)
        (mathlib / "Test.olean").write_text("warm fixture")
        arch = {"aarch64": "arm64", "x86_64": "x64"}.get(platform.machine(), platform.machine())
        (lake / ".stratalint-lean-cache-stamp.json").write_text(json.dumps(dict(
            schema="stratalint-lean-cache-v2", mathlib_revision=revision,
            os=platform.system().lower(), arch=arch)))
        scripts = self.root / "tools/scripts"
        (scripts / "worktree").mkdir(parents=True)
        shutil.copy2(REPOSITORY / "tools/scripts/maintenance_log.py", scripts)
        self.producer = REPOSITORY / "tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll"
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Fixture", "-c",
                        "user.email=fixture@example.invalid", "commit", "--allow-empty", "-m", "base"],
                       check=True, capture_output=True)

    def command(self):
        return [shutil.which("dotnet"), str(self.producer), "ensure-cache"]

    def assert_guard_free(self):
        address = hashlib.sha256(str(self.root / ".lake").encode()).hexdigest()
        guard = self.home / ".cache/stratalint-lean-cache-guards" / (address + ".lock")
        with guard.open("a+b") as stream:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def interrupt(self, mode, signum):
        script = self.root / "tools/scripts/worktree/lean-cache-publish.sh"
        script.write_text("#!/bin/bash\nexec " + shlex.join([sys.executable, __file__, "archive",
                          str(REPOSITORY), str(self.root), mode]) + "\n")
        process = subprocess.Popen(self.command(), cwd=self.root, env=self.env,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                   start_new_session=True)
        try:
            wait_for(self.root / "ready", process)
            child_pid = int((self.root / "ready").read_text())
            busy = subprocess.run(self.command(), cwd=self.root, env=self.env,
                                  capture_output=True, text=True, timeout=10)
            self.assertEqual(2, busy.returncode, busy.stdout + busy.stderr)
            self.assertIn('"status":"busy"', (busy.stdout + busy.stderr).replace(" ", ""))
            process.send_signal(signum)
            stdout, stderr = process.communicate(timeout=15)
            self.assertEqual(128 + signum, process.returncode, stdout + stderr)
            with self.assertRaises(ProcessLookupError):
                os.kill(child_pid, 0)
            self.assert_guard_free()
            phases = [json.loads(line) for line in (self.root / "phases").read_text().splitlines()]
            finishes = [row for row in phases if row["phase"] == "cache-ensure"
                        and row["boundary"] == "finish"]
            self.assertEqual(128 + signum, finishes[-1]["raw_exit"])
            records = [json.loads(line) for line in (self.root / "maintenance/lean-cache-ensure.jsonl")
                       .read_text().splitlines()]
            self.assertTrue(any(row["event"] == "run_finished" and row["exit_code"] == 128 + signum
                                and row.get("status") == "interrupted" for row in records))
            if mode == "install":
                self.assertEqual("original build", (self.root / ".lake/build/previous").read_text())
                self.assertEqual("original base", (self.root / ".lake/lean-report-seed-base.json").read_text())
                self.assertFalse((self.root / ".lake/build/replacement").exists())
                self.assertEqual([], list((self.root / ".lake").glob(".release-*")))
        finally:
            # Only this fixture's session is eligible for emergency settlement.
            with contextlib.suppress(ProcessLookupError):
                os.killpg(process.pid, signal.SIGKILL)
            process.communicate()

    def test_term_during_transport(self):
        self.interrupt("transport", signal.SIGTERM)

    def test_int_during_transport(self):
        self.interrupt("transport", signal.SIGINT)

    def test_term_during_install_rolls_back(self):
        self.interrupt("install", signal.SIGTERM)

    def test_int_during_install_rolls_back(self):
        self.interrupt("install", signal.SIGINT)

    def test_normal_and_argument_failure_have_terminal_outcomes(self):
        oleans = self.root / ".lake/build/lib/lean/D5"
        oleans.mkdir(parents=True)
        (oleans / "Test.olean").write_text("warm fixture")
        for arguments, expected in (([], 0), (["--invalid"], 2)):
            result = subprocess.run(self.command() + arguments, cwd=self.root, env=self.env,
                                    capture_output=True, text=True, timeout=15)
            self.assertEqual(expected, result.returncode, result.stdout + result.stderr)
            self.assert_guard_free()
            phases = [json.loads(line) for line in (self.root / "phases").read_text().splitlines()]
            self.assertEqual("finish", phases[-1]["boundary"])
            self.assertEqual(expected, phases[-1]["raw_exit"])


if __name__ == "__main__":
    if sys.argv[1] == "transport":
        Path(sys.argv[2], "ready").write_text(str(os.getpid()))
        signal.pause()
    elif sys.argv[1] == "archive":
        archive_child(Path(sys.argv[2]), Path(sys.argv[3]), sys.argv[4])
    else:
        REPOSITORY = Path(sys.argv.pop(1)).resolve()
        unittest.main()

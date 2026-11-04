"""Maintenance outcomes through real commands, inherited IO and OS locks."""

import contextlib
import fcntl
import importlib.util
import io
import json
import os
from pathlib import Path
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

SOURCE = Path(sys.argv.pop(1)).resolve()
LOGGER = SOURCE / "tools/scripts/maintenance_log.py"
PROTOCOL = SOURCE / "tools/scripts/worktree/worktree_protocol.py"
LOG_ENV = "TRURETURING_MAINTENANCE_LOG_DIR"


class MaintenanceLogTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="maintenance log tests ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.main = self.root / "main"
        self.main.mkdir()
        self.environment = dict(os.environ)
        for name in (LOG_ENV, "TRURETURING_MAINTENANCE_RUN_ID", "WORKTREE_SCOPE_FDS"):
            self.environment.pop(name, None)
        self.environment[LOG_ENV] = str(self.root / "logs")
        self.git("init", "--initial-branch=dev")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--allow-empty", "-m", "fixture")

    def git(self, *arguments):
        return subprocess.run(["git", "-C", str(self.main), *map(str, arguments)],
                              check=True, capture_output=True).stdout.strip()

    def command(self, *arguments, script="fixture", repository=None):
        return [sys.executable, "-B", str(LOGGER), "run", "--script", script,
                "--repository", str(repository or self.main), "--", *map(str, arguments)]

    def run_command(self, arguments, **options):
        return subprocess.run(arguments, cwd=self.main, env=self.environment,
                              capture_output=True, timeout=15, **options)

    def rows(self, script="fixture", directory=None):
        path = (directory or self.root / "logs") / (script + ".jsonl")
        return [json.loads(line) for line in path.read_text().splitlines()]

    def finished(self, code, script="fixture", directory=None):
        rows = self.rows(script, directory)
        self.assertEqual(["run_started", "run_finished"], [row["event"] for row in rows])
        self.assertEqual(code, rows[-1]["exit_code"])
        self.assertGreaterEqual(rows[-1]["duration_seconds"], 0)
        self.assertEqual(rows[0]["run_id"], rows[-1]["run_id"])
        self.assertEqual(str(self.main), rows[0]["repository"])
        return rows

    def test_bytes_and_stdin(self):
        payload = b"private transcript\x00\xff\r\nprogress\rno newline"
        result = self.run_command(self.command(sys.executable, "-c",
            "import os; data=os.read(0,4096); os.write(1,data); os.write(2,data[::-1])"), input=payload)
        self.assertEqual(0, result.returncode)
        self.assertEqual(payload, result.stdout)
        self.assertEqual(payload[::-1], result.stderr)
        self.finished(0)
        self.assertNotIn("private transcript", (self.root / "logs/fixture.jsonl").read_text())

    def test_partial_progress(self):
        with subprocess.Popen(self.command(sys.executable, "-c",
                "import os; os.write(1,b'progress\\r'); os.read(0,1); os.write(2,b'done')"),
                cwd=self.main, env=self.environment, stdin=subprocess.PIPE,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE) as job:
            try:
                self.assertTrue(select.select([job.stdout], [], [], 5)[0], "progress was buffered")
                self.assertEqual(b"progress\r", os.read(job.stdout.fileno(), 9))
                stdout, stderr = job.communicate(b"x", timeout=5)
                self.assertEqual((b"", b"done"), (stdout, stderr))
                self.assertEqual(0, job.returncode)
            finally:
                if job.poll() is None:
                    job.kill()
                    job.communicate()

    def test_status_and_launch_failures(self):
        denied = self.root / "not executable"
        denied.write_text("unexecutable")
        for script, command, expected in (
                ("failure", [sys.executable, "-c", "raise SystemExit(23)"], 23),
                ("missing", [str(self.root / "missing executable")], 127),
                ("denied", [str(denied)], 126)):
            with self.subTest(script=script):
                result = self.run_command(self.command(*command, script=script))
                self.assertEqual(expected, result.returncode)
                self.assertNotIn(b"Traceback", result.stderr)
                self.finished(expected, script)
        self.environment[LOG_ENV] = str(denied / "unwritable")
        result = self.run_command(self.command(sys.executable, "-c", "print('ordinary'); raise SystemExit(19)"))
        self.assertEqual((19, b"ordinary\n", b""), (result.returncode, result.stdout, result.stderr))

    def signal_case(self, handled):
        marker = self.root / "handled"
        code = "import os,signal,time; from pathlib import Path; "
        if handled:
            code += f"signal.signal(signal.SIGTERM,lambda *_: (Path({str(marker)!r}).touch(),exit(7))); "
        code += "print(os.getpid(),flush=True); time.sleep(60)"
        child_pid = None
        with subprocess.Popen(self.command(sys.executable, "-c", code), cwd=self.main,
                env=self.environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE) as job:
            try:
                self.assertTrue(select.select([job.stdout], [], [], 5)[0])
                child_pid = int(job.stdout.readline())
                job.send_signal(signal.SIGTERM)
                job.communicate(timeout=5)
                self.assertEqual(7 if handled else -signal.SIGTERM, job.returncode)
                with self.assertRaises(ProcessLookupError):
                    os.kill(child_pid, 0)
                self.assertEqual(handled, marker.exists())
            finally:
                if child_pid is not None:
                    try:
                        os.kill(child_pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                if job.poll() is None:
                    job.kill()
                    job.communicate()
        self.finished(7 if handled else 128 + signal.SIGTERM)

    def test_termination(self):
        self.signal_case(False)
        result = self.run_command(self.command(sys.executable, "-c",
            "import os,signal; os.kill(os.getpid(),signal.SIGTERM)", script="native-signal"))
        self.assertEqual(-signal.SIGTERM, result.returncode)
        self.finished(128 + signal.SIGTERM, "native-signal")

    def test_handled_signal(self):
        self.signal_case(True)

    def linked(self):
        tree = self.root / "linked"
        self.git("worktree", "add", "--detach", tree, "HEAD")
        return tree

    def test_shared_routing_and_correlation(self):
        tree = self.linked()
        self.environment.pop(LOG_ENV)
        outer = self.command(*self.command(sys.executable, "-c", "pass", script="inner", repository=tree),
                             script="outer")
        jobs = [subprocess.Popen(command, cwd=tree, env=self.environment)
                for command in (outer, self.command(sys.executable, "-c", "pass", script="outer", repository=tree))]
        try:
            self.assertEqual([0, 0], [job.wait(timeout=10) for job in jobs])
        finally:
            for job in jobs:
                if job.poll() is None:
                    job.kill()
                job.wait()
        directory = self.main / ".git/maintenance-logs"
        outer_rows = self.rows("outer", directory)
        inner_rows = self.rows("inner", directory)
        starts = [row for row in outer_rows if row["event"] == "run_started"]
        self.assertEqual(2, len({row["run_id"] for row in starts}))
        self.assertEqual(4, len(outer_rows))
        for start in starts:
            finish, = [row for row in outer_rows if row["event"] == "run_finished" and row["run_id"] == start["run_id"]]
            self.assertEqual(0, finish["exit_code"])
            self.assertIn(start["repository"], (str(tree), str(self.main)))
            self.assertGreater(start["pid"], 0)
        self.assertIn(inner_rows[0]["parent_run_id"], {row["run_id"] for row in starts})
        self.assertEqual(inner_rows[0]["run_id"], inner_rows[1]["run_id"])
        self.assertFalse((tree / "maintenance-logs").exists())

    def test_deleted_worktree(self):
        tree = self.linked()
        self.environment.pop(LOG_ENV)
        result = subprocess.run(self.command("git", "-C", self.main, "worktree", "remove", "--force", tree,
                                             repository=tree), cwd=tree, env=self.environment,
                                capture_output=True, timeout=15)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertFalse(tree.exists())
        rows = self.rows(directory=self.main / ".git/maintenance-logs")
        self.assertEqual(["run_started", "run_finished"], [row["event"] for row in rows])
        self.assertEqual(0, rows[-1]["exit_code"])

    def test_lock_lifetime(self):
        for scoped in (True, False):
            with self.subTest(scoped=scoped):
                self.lock_lifetime_case(scoped)

    def lock_lifetime_case(self, scoped):
        lock_path, release, done = (self.root / (str(scoped) + name) for name in ("lock", "release", "done"))
        survivor = ("import os,sys,time; from pathlib import Path; "
                    f"release=Path({str(release)!r}); "
                    "exec('while not release.exists(): time.sleep(0.01)'); "
                    "os.close(int(sys.argv[1])); "
                    f"Path({str(done)!r}).touch()")
        child = ("import os,subprocess,sys; "
                 "fds=(int(sys.argv[1]),); "
                 f"p=subprocess.Popen([sys.executable,'-c',{survivor!r},sys.argv[1]],pass_fds=fds,"
                 "stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL); print(p.pid)")
        with lock_path.open("w") as handle:
            fcntl.flock(handle, fcntl.LOCK_EX)
            if scoped:
                self.environment["WORKTREE_SCOPE_FDS"] = str(handle.fileno())
            else:
                self.environment.pop("WORKTREE_SCOPE_FDS", None)
            result = self.run_command(self.command(sys.executable, "-c", child, str(handle.fileno())),
                                      pass_fds=(handle.fileno(),))
            self.assertEqual(0, result.returncode, result.stderr)
            survivor_pid = int(result.stdout)
        try:
            with lock_path.open("w") as contender:
                with self.assertRaises(BlockingIOError):
                    fcntl.flock(contender, fcntl.LOCK_EX | fcntl.LOCK_NB)
                release.touch()
                deadline = time.monotonic() + 5
                while not done.exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(done.exists())
                fcntl.flock(contender, fcntl.LOCK_EX | fcntl.LOCK_NB)
        finally:
            release.touch()
            if not done.exists():
                with contextlib.suppress(ProcessLookupError):
                    os.kill(survivor_pid, signal.SIGKILL)

    def test_protocol_exec(self):
        code = ("import os,json; fds=list(map(int,os.environ['WORKTREE_SCOPE_FDS'].split(','))); "
                "print(json.dumps([os.getpid(),[os.fstat(fd).st_ino for fd in fds]]))")
        command = [sys.executable, "-B", str(PROTOCOL), "with", "--path", str(self.main),
                   "--write", "held", "--", sys.executable, "-c", code]
        with subprocess.Popen(command, cwd=self.main, env=self.environment, stdout=subprocess.PIPE) as job:
            stdout, _ = job.communicate(timeout=10)
            self.assertEqual(0, job.returncode)
            pid, descriptors = json.loads(stdout)
            self.assertEqual(job.pid, pid)
            self.assertTrue(descriptors)
        rows = self.rows("worktree-protocol")
        self.assertEqual(["run_started", "exec_started"], [row["event"] for row in rows])

    def test_script_guards(self):
        for relative in ("tools/scripts/maintenance_log.py", "tools/scripts/scribe-release.sh",
                         "tools/scripts/worktree/warm-donor.sh"):
            destination = self.main / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(SOURCE / relative, destination)
        bin_path = self.root / "bin"
        bin_path.mkdir()
        for name, body in {
                "git": "case \"$1\" in symbolic-ref) echo dev;; esac; exit 0",
                "make": f'exec /bin/bash "{self.main}/tools/scripts/scribe-release.sh" invalid'
        }.items():
            command = bin_path / name
            command.write_text("#!/bin/bash\n" + body + "\n")
            command.chmod(0o700)
        self.environment["PATH"] = str(bin_path) + os.pathsep + self.environment["PATH"]
        command = ["/bin/bash", str(self.main / "tools/scripts/worktree/warm-donor.sh")]
        result = self.run_command(command)
        self.assertEqual(2, result.returncode, result.stderr)
        warm = self.finished(2, "warm-donor")
        scribe = self.finished(2, "scribe-release")
        self.assertEqual(warm[0]["run_id"], scribe[0]["parent_run_id"])
        (self.main / "tools/scripts/maintenance_log.py").unlink()
        self.assertEqual(2, self.run_command(command).returncode)

    def load_cleanup(self):
        sys.path.insert(0, str(LOGGER.parent))
        spec = importlib.util.spec_from_file_location("maintenance_cleanup", SOURCE / "tools/scripts/host-cleanup.py")
        cleanup = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cleanup)
        return cleanup

    def test_host_cleanup_outcomes(self):
        tree = self.linked()
        cleanup = self.load_cleanup()
        environment = dict(self.environment)
        environment.pop(LOG_ENV)
        def remove_source(*args, **kwargs):
            self.git("worktree", "remove", "--force", tree)
            return 0
        arguments = ["clean", "--repository", str(tree), "--codex-home", str(self.root / "codex"),
                     "--sshx-home", str(self.root / "sshx"), "--tmp-root", str(self.root / "tmp")]
        with patch.dict(os.environ, environment, clear=True), \
             patch.object(cleanup, "active_paths", return_value=set()), \
             patch.object(cleanup, "clean_worktrees", side_effect=remove_source), \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(0, cleanup.main(arguments))
        self.assertFalse(tree.exists())
        rows = self.rows("host-cleanup", self.main / ".git/maintenance-logs")
        self.assertEqual("run_started", rows[0]["event"])
        self.assertIn("host_cleanup_summary", [row["event"] for row in rows])
        self.assertEqual("run_finished", rows[-1]["event"])
        self.assertEqual(0, rows[-1]["exit_code"])
        self.assertGreaterEqual(rows[-1]["duration_seconds"], 0)
        self.assertEqual(1, len({row["run_id"] for row in rows}))


    def test_host_cleanup_failures(self):
        cleanup = self.load_cleanup()
        arguments = ["clean", "--repository", str(self.main)]
        for error, expected in ((OSError("private failure output"), 1),
                                (cleanup.LowDiskSpace("private failure output"), 73),
                                (KeyboardInterrupt(), 130), (SystemExit(4), 4)):
            with self.subTest(error=type(error).__name__):
                self.environment[LOG_ENV] = str(self.root / type(error).__name__)
                with patch.dict(os.environ, self.environment, clear=True), \
                     patch.object(cleanup, "run_clean", side_effect=error), \
                     contextlib.redirect_stderr(io.StringIO()):
                    if isinstance(error, (KeyboardInterrupt, SystemExit)):
                        with self.assertRaises(type(error)):
                            cleanup.main(arguments)
                    else:
                        self.assertEqual(expected, cleanup.main(arguments))
                rows = self.finished(expected, "host-cleanup", Path(self.environment[LOG_ENV]))
                self.assertNotIn("private failure output", json.dumps(rows))


if __name__ == "__main__":
    unittest.main()

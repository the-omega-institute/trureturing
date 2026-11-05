"""Native-owner maintenance logging probes."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import shutil
import tempfile
import time
import unittest

SOURCE = Path(sys.argv.pop(1)).resolve()
LOGGER = SOURCE / "tools/scripts/maintenance_log.py"
LOG_ENV = "TRURETURING_MAINTENANCE_LOG_DIR"


class MaintenanceLogTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="maintenance log tests ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.main = self.root / "main"
        self.main.mkdir()
        self.environment = dict(os.environ)
        self.environment[LOG_ENV] = str(self.root / "logs")
        self.environment.pop("TRURETURING_MAINTENANCE_RUN_ID", None)
        self.git("init", "--initial-branch=dev")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--allow-empty", "-m", "fixture")

    def git(self, *arguments):
        return subprocess.run(["git", "-C", str(self.main), *map(str, arguments)],
                              check=True, capture_output=True).stdout.strip()

    def rows(self, script="fixture"):
        path = self.root / "logs" / (script + ".jsonl")
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def begin(self, script="fixture", repository=None, environment=None):
        env = dict(self.environment if environment is None else environment)
        result = subprocess.run(
            [sys.executable, "-B", str(LOGGER), "begin", "--script", script,
             "--repository", str(repository or self.main), "--owner-pid", str(os.getpid())],
            cwd=self.main, env=env, stdin=subprocess.DEVNULL,
            capture_output=True, check=True, timeout=15)
        return result.stdout.decode().strip()

    def finish(self, run_id, code, script="fixture", repository=None, environment=None):
        env = dict(self.environment if environment is None else environment)
        return subprocess.run(
            [sys.executable, "-B", str(LOGGER), "finish", "--script", script,
             "--repository", str(repository or self.main), "--run-id", run_id,
             "--owner-pid", str(os.getpid()), "--exit-code", str(code)],
            cwd=self.main, env=env, stdin=subprocess.DEVNULL,
            capture_output=True, check=True, timeout=15)

    def assert_finished(self, code, script="fixture", owner_pid=None):
        rows = self.rows(script)
        self.assertEqual(["run_started", "run_finished"], [row["event"] for row in rows])
        self.assertEqual(code, rows[-1]["exit_code"])
        self.assertEqual(rows[0]["run_id"], rows[-1]["run_id"])
        self.assertEqual(rows[0]["pid"], owner_pid or os.getpid())
        self.assertIsNone(rows[-1]["parent_run_id"])

    def native(self, code, *, script="fixture", input_data=None):
        run_id = self.begin(script)
        result = subprocess.run([sys.executable, "-c", code], cwd=self.main, env=self.environment,
                                input=input_data, capture_output=True, timeout=15)
        code = 128 - result.returncode if result.returncode < 0 else result.returncode
        self.finish(run_id, code, script)
        return result

    def test_native_bytes_and_stdin(self):
        payload = b"private transcript\x00\xff\r\nprogress\rno newline"
        result = self.native(
            "import os; data=os.read(0,4096); os.write(1,data); os.write(2,data[::-1])",
            input_data=payload)
        self.assertEqual(0, result.returncode)
        self.assertEqual(payload, result.stdout)
        self.assertEqual(payload[::-1], result.stderr)
        self.assert_finished(0)
        self.assertNotIn("private transcript", (self.root / "logs/fixture.jsonl").read_text())

    def signal_case(self, signum, handled):
        marker = self.root / f"signal-{signum}-{handled}"
        if handled:
            code = ("import signal,time; from pathlib import Path; "
                    f"signal.signal(signal.{signum}, lambda *_: (Path({str(marker)!r}).touch(), __import__('sys').exit(7))); "
                    "print('ready',flush=True); "
                    "time.sleep(60)")
        else:
            code = "import time; print('ready',flush=True); time.sleep(60)"
        script = f"signal-{signum}-{handled}"
        run_id = self.begin(script)
        with subprocess.Popen([sys.executable, "-c", code], cwd=self.main, env=self.environment,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) as job:
            self.assertEqual("ready\n", job.stdout.readline())
            job.send_signal(getattr(signal, signum))
            job.communicate(timeout=5)
            expected = 7 if handled else -getattr(signal, signum)
            self.assertEqual(expected, job.returncode)
        self.finish(run_id, 7 if handled else 128 + getattr(signal, signum), script)
        self.assert_finished(7 if handled else 128 + getattr(signal, signum), script)

    def test_direct_owner_pid_handled_and_unhandled_int_term(self):
        for signum in ("SIGINT", "SIGTERM"):
            for handled in (False, True):
                with self.subTest(signum=signum, handled=handled):
                    self.signal_case(signum, handled)

    def test_group_signal_has_one_native_delivery(self):
        marker = self.root / "group-count"
        child = ("import signal,time; from pathlib import Path; count=[0]; "
                 f"signal.signal(signal.SIGTERM, lambda *_: (count.__setitem__(0,count[0]+1), "
                 f"Path({str(marker)!r}).write_text(str(count[0])), exit(0))); time.sleep(60)")
        parent = ("import os,signal,subprocess,sys,time; "
                  f"child=subprocess.Popen([sys.executable,'-c',{child!r}]); "
                  "signal.signal(signal.SIGTERM, lambda *_: (child.wait(), exit(0))); "
                  "print(child.pid,flush=True); time.sleep(60)")
        for logged in (False, True):
            marker.unlink(missing_ok=True)
            run_id = self.begin("group-logged") if logged else None
            with subprocess.Popen([sys.executable, "-c", parent], cwd=self.main,
                                  env=self.environment, start_new_session=True,
                                  stdout=subprocess.PIPE, text=True) as job:
                job.stdout.readline()
                time.sleep(0.2)
                os.killpg(job.pid, signal.SIGTERM)
                self.assertEqual(0, job.wait(timeout=5))
            self.assertEqual("1", marker.read_text())
            if run_id is not None:
                self.finish(run_id, 0, "group-logged")

    def test_shared_common_directory_and_correlation(self):
        linked = self.root / "linked"
        self.git("worktree", "add", "--detach", str(linked), "HEAD")
        common_environment = dict(self.environment)
        common_environment.pop(LOG_ENV, None)
        parent = self.begin("outer", linked, common_environment)
        child_environment = dict(common_environment, TRURETURING_MAINTENANCE_RUN_ID=parent)
        child = self.begin("inner", linked, child_environment)
        self.finish(child, 0, "inner", linked, child_environment)
        self.finish(parent, 0, "outer", linked, common_environment)
        path = self.main / ".git" / "maintenance-logs"
        self.assertTrue((path / "outer.jsonl").exists())
        inner = [json.loads(line) for line in (path / "inner.jsonl").read_text().splitlines()]
        self.assertEqual(parent, inner[0]["parent_run_id"])

    def test_failing_destination_is_best_effort(self):
        denied = self.root / "file"
        denied.write_text("occupied")
        env = dict(self.environment, **{LOG_ENV: str(denied / "logs")})
        run_id = self.begin("unwritable", environment=env)
        self.finish(run_id, 19, "unwritable", environment=env)
        self.assertEqual([], self.rows("unwritable"))

    def test_bash_owner_boundary(self):
        scripts = self.main / "tools/scripts/worktree"
        scripts.mkdir(parents=True)
        shutil.copy2(SOURCE / "tools/scripts/maintenance_log.py", self.main / "tools/scripts/maintenance_log.py")
        shutil.copy2(SOURCE / "tools/scripts/worktree/warm-donor.sh", scripts / "warm-donor.sh")
        bin_dir = self.root / "bin"
        bin_dir.mkdir()
        (bin_dir / "git").write_text("#!/bin/sh\ncase \"$1\" in symbolic-ref) echo dev;; status) exit 0;; *) exit 2;; esac\n")
        (bin_dir / "git").chmod(0o700)
        env = dict(self.environment, PATH=str(bin_dir) + os.pathsep + os.environ.get("PATH", ""))
        result = subprocess.run(["/bin/bash", str(scripts / "warm-donor.sh")], cwd=self.main,
                                env=env, stdin=subprocess.DEVNULL, capture_output=True, timeout=15)
        self.assertNotEqual(0, result.returncode)
        rows = self.rows("warm-donor")
        self.assert_finished(result.returncode, "warm-donor", rows[0]["pid"])

    def test_consumer_audit(self):
        consumers = {
            "tools/scripts/clean-lanes.sh": "TRURETURING_MAINTENANCE_SCRIPT=clean-lanes",
            "tools/scripts/worktree-init.sh": "TRURETURING_MAINTENANCE_SCRIPT=worktree-init",
            "tools/scripts/worktree/lean-cache-ensure.sh": "TRURETURING_MAINTENANCE_SCRIPT=lean-cache-ensure",
            "tools/scripts/worktree/lean-cache-publish.sh": "TRURETURING_MAINTENANCE_SCRIPT=lean-cache-publish",
            "tools/scripts/report/lean-report.sh": "TRURETURING_MAINTENANCE_SCRIPT=lean-report",
            "tools/scripts/scribe-release.sh": "maintenance_log.py\" begin",
            "tools/scripts/worktree/warm-donor.sh": "maintenance_log.py\" begin",
            "tools/scripts/host-cleanup.py": "MaintenanceLog",
            "tools/scripts/worktree/worktree_protocol.py": "MaintenanceLog",
        }
        for relative, needle in consumers.items():
            text = (SOURCE / relative).read_text()
            self.assertIn(needle, text, relative)
            self.assertNotIn("maintenance_log.py\" run", text, relative)


if __name__ == "__main__":
    unittest.main()

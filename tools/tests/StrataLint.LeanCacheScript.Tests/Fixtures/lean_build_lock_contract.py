"""Exercise build exclusion with real Git worktrees and synchronized producers."""
import fcntl
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[4]
WRAPPER = "tools/scripts/worktree/lean-cache-run.sh"
WAITING = "lean-cache-run: waiting for another Lean build to finish"


class LeanBuildLockTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="lean-build-lock-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.root = self.directory / "main checkout"
        self.root.mkdir()
        self.copy_sources(self.root)
        self.git(self.root, "init", "--quiet")
        self.git(self.root, "add", ".")
        self.git(self.root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--quiet", "--no-gpg-sign", "-m", "fixture")
        self.worktrees = [self.directory / name for name in ("worktree one", "worktree two")]
        for worktree in self.worktrees:
            self.git(self.root, "worktree", "add", "--quiet", "--detach", str(worktree), "HEAD")
        self.lock = self.root / ".git/stratalint-lean-build.lock"
        bin_directory = self.directory / "bin"
        bin_directory.mkdir()
        producer = bin_directory / "dotnet"
        producer.write_text(f"#!{sys.executable}\n" +
                            "import sys\nprint('producer entered', flush=True)\n"
                            "raise SystemExit(int(sys.stdin.readline()))\n")
        producer.chmod(0o755)
        self.env = dict(os.environ, PATH=str(bin_directory) + os.pathsep + os.environ["PATH"],
                        STRATALINT_LEAN_PRODUCER_DLL="", STRATALINT_LEAN_CACHE_DONOR_REPOSITORY="")
        for name in ("MAKEFLAGS", "MFLAGS", "MAKELEVEL", "GIT_DIR", "GIT_WORK_TREE", "GIT_COMMON_DIR",
                     "LEAN_SKIP_LOCK"):
            self.env.pop(name, None)

    @staticmethod
    def copy_sources(root):
        (root / WRAPPER).parent.mkdir(parents=True)
        for name in ("Makefile", WRAPPER):
            shutil.copyfile(REPO / name, root / name)
        (root / "Reg").mkdir()
        (root / "Reg/lakefile.toml").touch()

    @staticmethod
    def git(root, *args):
        subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True)

    def start(self, root, targets="D5.Probe", wrapper=False, skip_lock=None):
        command = (["bash", WRAPPER, "--build", *targets.split()] if wrapper else
                   ["make", "--no-print-directory", "-s", "lean", "LEAN_TARGETS=" + targets])
        env = dict(self.env)
        if skip_lock is not None:
            if wrapper:
                env["LEAN_SKIP_LOCK"] = skip_lock
            else:
                command.append("LEAN_SKIP_LOCK=" + skip_lock)
        process = subprocess.Popen(command, cwd=root, env=env, stdin=subprocess.PIPE,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, start_new_session=True)
        self.addCleanup(self.cleanup_process, process)
        return process

    @staticmethod
    def cleanup_process(process):
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
        process.stdin.close()
        process.stdout.close()

    def expect(self, process, line):
        self.assertEqual(line + "\n", process.stdout.readline())

    @staticmethod
    def finish_phase(process, code=0):
        process.stdin.write(str(code) + "\n")
        process.stdin.flush()

    def assert_locked(self):
        with self.lock.open("a") as stream:
            with self.assertRaises(BlockingIOError):
                fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def assert_unlocked(self):
        with self.lock.open("a") as stream:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def test_main_and_linked_worktrees_wait_across_all_build_phases(self):
        first = self.start(self.root, targets="")
        self.expect(first, "producer entered")
        second = self.start(self.worktrees[0], targets="D5.Probe Reg.Probe")
        self.expect(second, WAITING)
        for phase in range(4):
            self.assert_locked()
            self.finish_phase(first)
            if phase < 3:
                self.expect(first, "producer entered")
        self.assertEqual(0, first.wait())
        self.expect(second, "producer entered")
        third = self.start(self.worktrees[1])
        self.expect(third, WAITING)
        for phase in range(2):
            self.assert_locked()
            self.finish_phase(second)
            if phase == 0:
                self.expect(second, "producer entered")
        self.assertEqual(0, second.wait())
        self.expect(third, "producer entered")
        self.assert_locked()
        self.finish_phase(third)
        self.assertEqual(0, third.wait())
        self.assert_unlocked()

    def test_failed_build_preserves_status_and_releases_waiter(self):
        first = self.start(self.worktrees[0], targets="", wrapper=True)
        self.expect(first, "producer entered")
        second = self.start(self.root)
        self.expect(second, WAITING)
        self.finish_phase(first, 23)
        self.assertEqual(23, first.wait())
        self.assertEqual("", first.stdout.read())
        self.expect(second, "producer entered")
        self.finish_phase(second)
        self.assertEqual(0, second.wait())
        self.assert_unlocked()

    def test_terminated_build_releases_waiter(self):
        first = self.start(self.root)
        self.expect(first, "producer entered")
        second = self.start(self.worktrees[0])
        self.expect(second, WAITING)
        os.killpg(first.pid, signal.SIGTERM)
        self.assertNotEqual(0, first.wait())
        self.expect(second, "producer entered")
        self.finish_phase(second)
        self.assertEqual(0, second.wait())
        self.assert_unlocked()

    def test_cancelled_waiter_leaves_holder_and_next_waiter_intact(self):
        first = self.start(self.root)
        self.expect(first, "producer entered")
        second = self.start(self.worktrees[0])
        self.expect(second, WAITING)
        os.killpg(second.pid, signal.SIGTERM)
        self.assertNotEqual(0, second.wait())
        self.assert_locked()
        third = self.start(self.worktrees[1])
        self.expect(third, WAITING)
        self.finish_phase(first)
        self.assertEqual(0, first.wait())
        self.expect(third, "producer entered")
        self.finish_phase(third)
        self.assertEqual(0, third.wait())
        self.assert_unlocked()

    def test_unrelated_repositories_build_independently(self):
        other = self.directory / "other repository"
        other.mkdir()
        self.copy_sources(other)
        self.git(other, "init", "--quiet")
        first = self.start(self.root)
        self.expect(first, "producer entered")
        second = self.start(other)
        self.expect(second, "producer entered")
        for process in (first, second):
            self.finish_phase(process)
            self.assertEqual(0, process.wait())

    def test_missing_git_identity_fails_before_producer(self):
        other = self.directory / "not a repository"
        other.mkdir()
        self.copy_sources(other)
        process = self.start(other, wrapper=True)
        output, _ = process.communicate("0\n")
        self.assertNotEqual(0, process.returncode)
        self.assertNotIn("producer entered", output)

    def test_skip_lock_runs_while_another_build_holds_lock_without_releasing_it(self):
        holder = self.start(self.root)
        self.expect(holder, "producer entered")
        bypass = self.start(self.worktrees[0], skip_lock="1")
        self.expect(bypass, "producer entered")
        waiter = self.start(self.worktrees[1], skip_lock="0")
        self.expect(waiter, WAITING)
        self.finish_phase(bypass)
        self.assertEqual(0, bypass.wait())
        self.assert_locked()
        self.finish_phase(holder)
        self.assertEqual(0, holder.wait())
        self.expect(waiter, "producer entered")
        self.finish_phase(waiter)
        self.assertEqual(0, waiter.wait())
        self.assert_unlocked()

    def test_skip_lock_does_not_block_other_builds_during_any_package_phase(self):
        bypass = self.start(self.root, targets="", skip_lock="1")
        self.expect(bypass, "producer entered")
        self.assert_unlocked()
        normal = self.start(self.worktrees[0])
        self.expect(normal, "producer entered")
        self.assert_locked()
        self.finish_phase(normal)
        self.assertEqual(0, normal.wait())
        for phase in range(4):
            self.assert_unlocked()
            self.finish_phase(bypass)
            if phase < 3:
                self.expect(bypass, "producer entered")
        self.assertEqual(0, bypass.wait())


if __name__ == "__main__":
    unittest.main()

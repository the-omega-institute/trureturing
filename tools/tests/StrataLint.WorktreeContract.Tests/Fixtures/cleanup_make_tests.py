"""Canonical cleanup Make entrances with current production CLI, Git and OS."""

import json
import gc
import os
from pathlib import Path
import select
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

from native_fixture import NativeFixture

SOURCE = Path(sys.argv.pop(1)).resolve()
SPACED = sys.argv.pop(1) == "spaced"
ENTRANCE = sys.argv.pop(1)
INVOCATION = sys.argv.pop(1)


class CleanupMakeTests(NativeFixture):
    def mark_phase(self, phase):
        now = time.monotonic()
        if hasattr(self, "phase_started"):
            print(json.dumps(dict(event="fixture_phase", phase=self.active_phase,
                                  elapsed_seconds=now - self.phase_started,
                                  fixture_elapsed_seconds=now - self.fixture_started,
                                  commands=self.phase_commands)), flush=True)
        self.active_phase = phase
        self.phase_started = now
        self.phase_commands = []
        print(json.dumps(dict(event="fixture_phase", phase=phase, status="started",
                              fixture_elapsed_seconds=now - self.fixture_started)), flush=True)

    def run_command(self, arguments, cwd=None, input=None, phase="git"):
        return self.run_owned_command(arguments, cwd or self.repository, input, phase,
                                      timeout=120, env=self.environment)

    def git(self, *arguments, cwd=None, input=None):
        return self.run_command(["git", *arguments], cwd, input).stdout.strip()

    def setUp(self):
        self.fixture_started = time.monotonic()
        self.mark_phase("initialize")
        self.commands_settled = True
        self.root = self.workspace("cleanup-make-")
        self.repository = self.root / ("checkout with  spaces" if SPACED else "checkout")
        self.repository.mkdir()
        self.environment = dict(os.environ, TMPDIR=str(self.root / "tmp"),
                                MSBUILDDISABLENODEREUSE="1", DOTNET_CLI_USE_MSBUILD_SERVER="0",
                                UseSharedCompilation="false",
                                GIT_AUTHOR_DATE="1700000000 +0000",
                                GIT_COMMITTER_DATE="1700000000 +0000")
        Path(self.environment["TMPDIR"]).mkdir()
        self.remote = self.root / "remote.git"
        self.git("init", "--bare", self.remote)
        self.git("init", "--initial-branch=dev")
        self.git("config", "user.name", "Cleanup Make Tests")
        self.git("config", "user.email", "cleanup-make@example.invalid")
        (self.repository / "owned").write_text("preserved\n")
        (self.repository / ".gitignore").write_text("bin/\nobj/\n.lake/\n")
        self.git("add", ".")
        self.git("commit", "-m", "fixture baseline")
        self.baseline = self.git("rev-parse", "HEAD")
        self.git("remote", "add", "origin", self.remote)
        history = []
        for index in range(301):
            history.append("commit refs/heads/dev\ncommitter Test <test@example.invalid> "
                           "1700000000 +0000\ndata 1\nx\n"
                           + ("from " + self.baseline + "\n" if index == 0 else "") + "\n")
        self.git("fast-import", "--quiet", input="".join(history))
        self.git("reset", "--hard", "dev")
        self.git("push", "origin", "dev")
        self.mark_phase("source-copy")
        # Copy current build inputs, not another revision or an installed CLI substitute.
        files = subprocess.check_output(["git", "ls-files", "-z", "tools"], cwd=SOURCE).split(b"\0")
        paths = [Path(os.fsdecode(name)) for name in files if name]
        paths += list(map(Path, ["Makefile", "Directory.Build.props", "Directory.Packages.props", "global.json"]))
        for relative in paths:
            target = self.repository / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(SOURCE / relative, target)
        self.mark_phase("canonical-build")
        self.run_command(["make", "--no-print-directory", "-C", self.repository / "tools", "dotnet",
                          "DOTNET_PROJECT=tools/StrataLint.Cli/StrataLint.Cli.csproj"], phase="canonical-build")
        self.mark_phase("preservation-lanes")
        self.dirty = self.add_lane("dirty")
        (self.dirty / "owned").write_text("unpublished dirty\n")
        (self.dirty / "untracked").write_text("unpublished untracked\n")
        self.local = self.add_lane("local")
        (self.local / "owned").write_text("local commit\n")
        self.git("add", "owned", cwd=self.local)
        self.git("commit", "-m", "unpublished commit", cwd=self.local)
        self.local_head = self.git("rev-parse", "HEAD", cwd=self.local)
        self.cache = self.add_lane("cache")
        (self.cache / ".lake").mkdir()
        (self.cache / ".lake/unknown").write_text("uncertified cache\n")
        self.busy = self.add_lane("busy")
        self.mark_phase("participant-start")
        self.job = subprocess.Popen([sys.executable, "-B",
            str(self.repository / "tools/scripts/worktree/worktree_protocol.py"),
            "--source", str(self.repository), "with", "--path", str(self.busy), "--",
            sys.executable, "-c", 'import sys; print("ready",flush=True); sys.stdin.readline()'],
            cwd=self.root, env=self.environment, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True)
        self.jobs_settled = False
        self.addCleanup(self.stop_job)
        self.assertTrue(select.select([self.job.stdout], [], [], 10)[0], "participant readiness")
        self.assertEqual("ready\n", self.job.stdout.readline())

    def stop_job(self):
        self.mark_phase("participant-stop")
        if self.job.poll() is None:
            self.job.stdin.write("finish\n")
            self.job.stdin.flush()
        self.job.communicate(timeout=10)
        self.assertEqual(0, self.job.returncode)
        self.jobs_settled = True

    def add_lane(self, name):
        tree = self.root / ("tree-" + name)
        branch = "lane/governance/" + name
        self.git("worktree", "add", "-b", branch, tree, self.baseline)
        self.git("push", "origin", branch)
        # Eligibility uses history/reflog age, independent of source-path handling.
        administration = Path(self.git("rev-parse", "--absolute-git-dir", cwd=tree))
        for log in (administration / "logs/HEAD", self.repository / ".git/logs/refs/heads" / branch):
            lines = []
            for line in log.read_text().splitlines():
                metadata, separator, message = line.partition("\t")
                fields = metadata.split(" ")
                fields[-2] = "1700000000"
                lines.append(" ".join(fields) + separator + message)
            log.write_text("\n".join(lines) + "\n")
        return tree

    @staticmethod
    def events(result):
        return [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{"event":')]

    def assert_retained(self, events):
        items = {item["path"]: item for item in events if item["event"] == "clean_lanes_item"}
        for tree in (self.dirty, self.local, self.cache, self.busy):
            self.assertTrue(tree.exists(), str(tree))
            self.assertEqual("skipped", items[str(tree)]["action"], items[str(tree)])
        self.assertEqual("unpublished dirty\n", (self.dirty / "owned").read_text())
        self.assertEqual("unpublished untracked\n", (self.dirty / "untracked").read_text())
        self.assertEqual(self.local_head, self.git("rev-parse", "HEAD", cwd=self.local))
        self.assertEqual("uncertified cache\n", (self.cache / ".lake/unknown").read_text())
        self.assertIsNone(self.job.poll(), "independent participant must survive cleanup")

    def test_production_cleanup_entrances(self):
        entrances = [
            (["-C", self.repository / "tools"], "clean-lanes", self.root),
            (["-C", self.repository / "tools"], "clean-all", self.root),
            (["-C", self.repository], "worktree-clean", self.root),
        ]
        if SPACED:
            entrances += [
                (["-f", self.repository / "tools/Makefile"], "clean-lanes", self.repository),
                (["-f", self.repository / "tools/Makefile"], "clean-all", self.repository),
            ]
        entrances = [(options, target, cwd) for options, target, cwd in entrances
                     if target == ENTRANCE and (options[0] == "-f") == (INVOCATION == "file")]
        self.assertEqual(1, len(entrances))
        for index, (options, target, cwd) in enumerate(entrances):
            with self.subTest(target=target, options=list(map(str, options))):
                name = "eligible-" + str(index)
                self.mark_phase("eligible-lane")
                eligible = self.add_lane(name)
                arguments = ["make", "--no-print-directory", *options, target, "BASE=dev"]
                if target == "clean-all":
                    arguments += ["CLEAN_CODEX_HOME=" + str(self.root / "codex"),
                                  "CLEAN_SSHX_HOME=" + str(self.root / "sshx"),
                                  "CLEAN_TMP_ROOT=" + self.environment["TMPDIR"], "VERBOSE=1"]
                if target != "worktree-clean":
                    self.mark_phase(target + ":preview")
                    preview = self.run_command(arguments, cwd, phase=target + ":preview")
                    preview_events = self.events(preview)
                    item = next(item for item in preview_events if item.get("path") == str(eligible))
                    self.assertEqual("would_remove", item["action"], item)
                    self.assertTrue(eligible.exists())
                    self.assert_retained(preview_events)
                self.mark_phase(target + ":force")
                removed = self.run_command(arguments + ["FORCE=1"], cwd, phase=target + ":force")
                self.mark_phase("production-assertions")
                events = self.events(removed)
                item = next(item for item in events if item.get("path") == str(eligible))
                self.assertEqual("removed", item["action"], item)
                self.assertFalse(eligible.exists())
                self.assertNotIn("refs/heads/lane/governance/" + name,
                                 self.git("for-each-ref", "--format=%(refname)"))
                self.assertEqual(self.baseline, self.git("ls-remote", "origin",
                    "refs/heads/lane/governance/" + name).split()[0])
                self.assert_retained(events)
                if target == "clean-all":
                    summary = next(item for item in events if item["event"] == "host_cleanup_summary")
                    self.assertEqual("succeeded", summary["status"])
                    self.assertEqual(0, summary["worktree_exit"])
                print(json.dumps(dict(entrance=target, options=list(map(str, options)),
                    source=str(self.repository), exit=removed.returncode,
                    removed=str(eligible), retained=[str(tree) for tree in
                        (self.dirty, self.local, self.cache, self.busy)])), flush=True)


class CommandLifetimeTests(NativeFixture):
    # Exercise the exact cleanup-fixture consumer, without copying/building another CLI.
    run_command = CleanupMakeTests.run_command
    mark_phase = CleanupMakeTests.mark_phase

    def setUp(self):
        self.fixture_started = time.monotonic()
        self.mark_phase("native-lifetime")
        self.commands_settled = True
        self.root = self.workspace("cleanup-lifetime-")
        self.repository = self.root
        self.environment = dict(os.environ)

    def check_lifetime(self, mode):
        material = self.root / "unrelated-input"
        material.write_text("independent material\n")
        participant = subprocess.Popen(["/bin/sh", "-c",
            'exec 3<"$1"; printf "ready\\n"; read line; cat <&3', "participant", str(material)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, start_new_session=True)
        def stop_participant():
            if participant.poll() is None:
                participant.communicate("finish\n", timeout=10)
        self.addCleanup(stop_participant)
        self.assertTrue(select.select([participant.stdout], [], [], 10)[0])
        self.assertEqual("ready\n", participant.stdout.readline())
        child_file = self.root / "child.pid"
        fifo = self.root / "ready"
        os.mkfifo(fifo)
        if mode == "normal":
            command = ['cat "$1"; printf "normal-error\\n" >&2', "native", str(material)]
        else:
            command = [
                "/bin/sh -c 'trap \"\" TERM; printf \"ready\\\\n\" > \"$1\"; exec sleep 600' "
                'child "$1" & child=$!; read ready < "$1"; '
                'printf "%s\\n" "$child" > "$2"; kill -STOP "$child"; '
                'printf "partial-output\\n"; printf "partial-error\\n" >&2; '
                + ("wait" if mode == "deadline" else "exit 7" if mode == "nonzero" else "exit 0"),
                "launcher", str(fifo), str(child_file)]
        if mode in ("nonzero", "deadline"):
            with self.assertRaises(AssertionError) as failure:
                self.run_command(["/bin/sh", "-c", *command], phase=mode)
            evidence = json.loads(str(failure.exception))
            self.assertEqual("deadline" if mode == "deadline" else "exited", evidence["status"], evidence)
            if mode == "nonzero":
                self.assertEqual(7, evidence["returncode"])
            self.assertEqual("partial-output\n", evidence["stdout"])
            self.assertEqual("partial-error\n", evidence["stderr"])
            self.assertEqual(mode, evidence["phase"])
        else:
            result = self.run_command(["/bin/sh", "-c", *command], phase=mode)
            evidence = result.lifetime
            self.assertEqual(0, result.returncode)
            self.assertEqual("independent material\n" if mode == "normal" else "partial-output\n",
                             result.stdout)
        self.assertTrue(evidence["settled"])
        with self.assertRaises(ProcessLookupError):
            os.killpg(evidence["pid"], 0)
        if mode != "normal":
            child = int(child_file.read_text())
            with self.assertRaises(ProcessLookupError):
                os.kill(child, 0)
        self.assertIsNone(participant.poll(), "independent process sharing inputs must survive")
        self.assertEqual("independent material\n", material.read_text())
        output, error = participant.communicate("finish\n", timeout=10)
        self.assertEqual(0, participant.returncode, error)
        self.assertEqual("independent material\n", output)
        print(json.dumps(dict(event="native_lifetime_assertions", mode=mode, owned_group=evidence["pid"],
                              settled=True, independent_survived=True, material_retained=True)), flush=True)

    def test_normal(self):
        self.check_lifetime("normal")

    def test_nonzero(self):
        self.check_lifetime("nonzero")

    def test_deadline(self):
        self.check_lifetime("deadline")

    def test_launcher(self):
        self.check_lifetime("launcher")


class SignalErrorTests(CommandLifetimeTests):
    def check_signal_error(self, operation):
        native_killpg = os.killpg
        injected = []
        def killpg(group, signum):
            if not injected and ((operation == "signal" and signum == signal.SIGTERM)
                                 or (operation == "probe" and signum == 0)):
                injected.append((group, signum))
                raise PermissionError(1, "injected owned-group signal/probe error")
            return native_killpg(group, signum)
        os.killpg = killpg
        try:
            self.check_lifetime("launcher")
        finally:
            os.killpg = native_killpg
        self.assertEqual(1, len(injected))
        print(json.dumps(dict(event="native_signal_error_assertions", operation=operation,
                              settled=True, independent_survived=True)), flush=True)

    def test_delivery_error(self):
        self.check_signal_error("signal")

    def test_observation_error(self):
        self.check_signal_error("probe")


class FixtureDisposalTests(NativeFixture):
    def test_completed_outcomes_and_finalizers(self):
        for publication in ("immediate", "deferred"):
            for failure in (None, "setup", "body", "subtest", "teardown", "cleanup",
                            "incomplete", "unsettled", "nested-input"):
                with self.subTest(publication=publication, failure=failure):
                    class Result(unittest.TestResult):
                        def __init__(self):
                            super().__init__()
                            self.pending = []
                        def addError(self, test, error):
                            if publication == "deferred": self.pending.append((test, error))
                            else: super().addError(test, error)
                        def stopTest(self, test):
                            for item, error in self.pending:
                                super().addError(item, error)
                            super().stopTest(test)

                    class Probe(NativeFixture):
                        def setUp(self):
                            self.root = self.workspace("fixture-disposal-")
                            (self.root / "input").write_text("recoverable input\n")
                            if failure == "nested-input":
                                self.nested = self.workspace("fixture-nested-", "/tmp")
                                (self.nested / "input").write_text("nested recovery\n")
                            def cleanup():
                                # Every supported runtime temporarily resets this flag.
                                self.assertTrue(self._outcome.success)
                                if failure == "cleanup": raise RuntimeError("cleanup failed")
                            self.addCleanup(cleanup)
                            if failure == "setup": raise RuntimeError("setup failed")
                        def test_body(self):
                            if failure == "incomplete": raise KeyboardInterrupt()
                            if failure == "unsettled": self.commands_settled = False
                            if failure == "subtest":
                                with self.subTest(): self.fail("subtest failed")
                            if failure in ("body", "nested-input"): raise RuntimeError("body failed")
                        def tearDown(self):
                            if failure == "teardown": raise RuntimeError("teardown failed")

                    probe = Probe("test_body")
                    result = Result()
                    if failure == "incomplete":
                        with self.assertRaises(KeyboardInterrupt): probe.run(result)
                    else:
                        probe.run(result)
                    paths = list(probe.workspaces)
                    del probe
                    gc.collect()
                    for path in paths:
                        self.assertEqual(failure is not None, path.exists(), str(path))
                        if path.exists():
                            self.assertIn("recovery" if failure == "nested-input" and len(paths) > 1
                                          and path == paths[1] else "recoverable", (path / "input").read_text())
                            # Dispose only the intentionally failed regression input,
                            # after verifying survival beyond fixture/GC finalization.
                            shutil.rmtree(path)
        print(json.dumps(dict(event="fixture_disposal_assertions", publication_orders=2,
                              outcomes_per_order=9, retained_after_gc=True)), flush=True)


if __name__ == "__main__":
    NativeFixture.install_interrupt_handler()
    unittest.main()

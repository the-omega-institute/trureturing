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

    def run_command(self, arguments, cwd=None, input=None, phase="git", check=True):
        return self.run_owned_command(arguments, cwd or self.repository, input, phase,
                                      timeout=120, env=self.environment, check=check)

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
        # The selected CLI project and its production references do not build test
        # sources. Copy its current tool inputs without unrelated test checkouts.
        files = subprocess.check_output(["git", "ls-files", "-z", "tools", ":(exclude)tools/tests"],
                                        cwd=SOURCE).split(b"\0")
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
        # A current Git lock keeps the separate orphan/snapshot sweep out of
        # host-wide temporary roots while exercising the real canonical door.
        self.current = self.add_lane("current-lock")
        self.git("worktree", "lock", "--reason", "fixture", self.current)
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

    def diverge_main_adapter(self):
        # The invoking checkout retains candidate sources. Git's protected main
        # anchor is independently versioned and need not provide that program.
        directory = self.repository / "tools/scripts/worktree"
        if INVOCATION == "missing":
            for path in directory.glob("worktree_*.py"):
                path.unlink()
        elif INVOCATION == "divergent":
            (directory / "worktree_protocol.py").write_text(
                'raise RuntimeError("another checkout implementation selected")\n')
            (self.repository / "base64.py").write_text(
                'raise RuntimeError("repository file selected as adapter support")\n')

    @staticmethod
    def events(result):
        return [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{"event":')]

    def assert_aggregate_result(self, result):
        events = self.events(result)
        summaries = [item for item in events if item["event"] == "host_cleanup_summary"]
        self.assertEqual(1, len(summaries), result.stdout + result.stderr)
        summary = summaries[0]
        self.assertEqual(0, summary["worktree_exit"], summary)
        lanes = [item for item in events if item["event"] == "clean_lanes_summary"]
        self.assertEqual(1, len(lanes), result.stdout + result.stderr)
        self.assertEqual(0, lanes[0]["failed_count"], lanes[0])
        self.assertEqual(0, lanes[0]["partial_count"], lanes[0])
        if summary["inventory_error"] is not None:
            # Ordinary-artifact observation can fail independently of successful
            # worktree checkpoint/removal. Make must still propagate that failure.
            self.assertTrue(summary["inventory_error"], summary)
            self.assertEqual("not_started", summary["artifact_sweep"], summary)
            self.assertEqual("failed", summary["status"], summary)
            self.assertEqual(2, result.returncode, result.stdout + result.stderr)
            self.assertFalse(any(item["event"] == "host_cleanup_item" for item in events), events)
        else:
            self.assertEqual("succeeded", summary["status"], summary)
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            self.assertFalse(any(key.endswith(":failed") and value for key, value in summary["counts"].items()))
            for field in ("disk_available_before", "disk_available_after"):
                self.assertGreater(summary[field], 0)
        return summary

    def assert_recoverable(self, events, preview=False):
        items = {item["path"]: item for item in events if item["event"] == "clean_lanes_item"}
        for tree in (self.dirty, self.local, self.cache, self.busy):
            self.assertEqual(preview, tree.exists(), str(tree))
            expected = "would_remove" if preview else "removed"
            self.assertEqual(expected, items[str(tree)]["action"], items[str(tree)])
        self.assertTrue(self.current.exists())
        self.assertEqual("locked_recent", items[str(self.current)]["reason"])
        if not preview:
            self.assertEqual("stale_behind", items[str(self.local)]["reason"])
            recovery = self.root / "recovered-dirty"
            self.git("worktree", "add", recovery, "lane/governance/dirty")
            self.assertEqual("unpublished dirty\n", (recovery / "owned").read_text())
            self.assertEqual("unpublished untracked\n", (recovery / "untracked").read_text())
            self.assertEqual(self.local_head, self.git("rev-parse", "refs/heads/lane/governance/local"))
        self.assertIsNone(self.job.poll(), "independent participant must survive cleanup")

    def test_aggregate_survives_repository_removal(self):
        selected = self.add_lane("aggregate-anchor")
        shutil.copytree(self.repository / "tools", selected / "tools",
                        ignore=shutil.ignore_patterns("bin", "obj"))
        for name in ("Directory.Build.props", "Directory.Packages.props", "global.json"):
            shutil.copy2(self.repository / name, selected / name)
        self.diverge_main_adapter()
        (selected / "owned").write_text("old staged value\n")
        self.git("add", "owned", cwd=selected)
        (selected / "owned").write_text("final tracked value\n")
        (selected / "untracked").write_text("ordinary untracked value\n")
        (selected / ".lake").mkdir()
        (selected / ".lake/ignored").write_text("outside snapshot\n")
        artifacts = self.root / "artifacts"
        artifacts.mkdir()
        obsolete = artifacts / "ordinary-output"
        obsolete.write_text("independent artifact\n")
        caller = artifacts / "stable-caller"
        caller.mkdir()
        caller_input = caller / "input"
        caller_input.write_text("caller material\n")
        for path in (obsolete, caller_input, caller):
            os.utime(path, (1700000000, 1700000000))
        self.assertIn(INVOCATION, ("self", "stable", "missing", "divergent"))
        cwd = caller if INVOCATION == "stable" else selected / "tools"
        makefile = (self.repository if INVOCATION == "stable" else selected) / "tools/Makefile"
        relative = lambda path: os.path.relpath(path, cwd)
        arguments = ["make", "--no-print-directory", "-f", makefile, "clean-all",
                     "FORCE=1", "BASE=dev", "VERBOSE=1",
                     "REPOSITORY=" + relative(selected),
                     "CLEAN_CODEX_HOME=" + relative(self.root / "codex"),
                     "CLEAN_SSHX_HOME=" + relative(self.root / "sshx"),
                     "CLEAN_TMP_ROOT=" + relative(artifacts)]
        removed = self.run_command(arguments, cwd, phase="aggregate-anchor", check=False)
        summary = self.assert_aggregate_result(removed)
        events = self.events(removed)
        item = next(item for item in events if item.get("path") == str(selected))
        self.assertEqual("removed", item["action"], item)
        self.assertFalse(selected.exists())
        self.assertEqual(summary["inventory_error"] is not None, obsolete.exists(), summary)
        if INVOCATION == "stable":
            self.assertEqual("caller material\n", caller_input.read_text())
        recovery = self.root / "recovered-anchor"
        branch = "lane/governance/aggregate-anchor"
        self.git("worktree", "add", recovery, branch)
        self.assertEqual("final tracked value\n", (recovery / "owned").read_text())
        self.assertEqual("ordinary untracked value\n", (recovery / "untracked").read_text())
        self.assertFalse((recovery / ".lake/ignored").exists())
        self.assert_recoverable(events)
        print(json.dumps(dict(event="aggregate_anchor_result", invocation=INVOCATION,
            command=list(map(str, arguments)), exit=removed.returncode,
            selected_tree_exists=selected.exists(), artifact_exists=obsolete.exists(),
            recovery_branch=branch, recovery_commit=self.git("rev-parse", branch),
            recovered={name: (recovery / name).read_text() for name in ("owned", "untracked")},
            ignored_recovered=False, host_summary=summary)), flush=True)

    def test_registered_consumer_survives_source_removal(self):
        selected = self.add_lane("aaa-anchor")
        later = self.add_lane("zzz-later")
        shutil.copytree(self.repository / "tools", selected / "tools",
                        ignore=shutil.ignore_patterns("bin", "obj"))
        for name in ("Makefile", "Directory.Build.props", "Directory.Packages.props", "global.json"):
            shutil.copy2(self.repository / name, selected / name)
        self.diverge_main_adapter()
        for tree in (selected, later):
            (tree / "deleted").write_text("delete from ordinary snapshot\n")
            self.git("add", "deleted", cwd=tree)
            self.git("commit", "-m", "deletion baseline", cwd=tree)
            (tree / "deleted").unlink()
            (tree / "owned").write_text("superseded staged value\n")
            self.git("add", "owned", cwd=tree)
            (tree / "owned").write_text(tree.name + " tracked\n")
            (tree / "untracked").write_text(tree.name + " untracked\n")
            (tree / ".lake").mkdir()
            (tree / ".lake/ignored").write_text("ignored bytes\n")
        if ENTRANCE == "clean-lanes":
            arguments = ["make", "--no-print-directory", "-C", "tools", "clean-lanes", "FORCE=1", "BASE=dev"]
        else:
            self.assertEqual("worktree-remove", ENTRANCE)
            arguments = ["make", "--no-print-directory", "worktree-remove",
                         "NAMES=" + selected.name + " " + later.name]
        result = self.run_command(arguments, selected, phase="registered-anchor", check=False)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        if ENTRANCE == "clean-lanes":
            events = self.events(result)
            removed = [item["path"] for item in events if item.get("action") == "removed"]
            self.assertLess(removed.index(str(selected)), removed.index(str(later)))
            self.assert_recoverable(events)
        else:
            items = [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{')]
            self.assertEqual([str(selected), str(later)], [item["path"] for item in items])
            self.assertEqual(["removed", "removed"], [item["outcome"] for item in items])
            self.assertIn("WORKTREE_REMOVE_RESULT exit=0 removed=2 failed=0 refused=0", result.stdout)
        for tree, branch in ((selected, "aaa-anchor"), (later, "zzz-later")):
            self.assertFalse(tree.exists())
            recovered = self.root / (branch + "-recovered")
            self.git("worktree", "add", recovered, "lane/governance/" + branch)
            self.assertEqual(tree.name + " tracked\n", (recovered / "owned").read_text())
            self.assertEqual(tree.name + " untracked\n", (recovered / "untracked").read_text())
            self.assertFalse((recovered / "deleted").exists())
            self.assertFalse((recovered / ".lake/ignored").exists())
        print(json.dumps(dict(event="registered_anchor_result", entrance=ENTRANCE,
            exit=result.returncode, source_removed=True, later_removed=True,
            recovery_verified=True)), flush=True)

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
                    preview = self.run_command(arguments, cwd, phase=target + ":preview", check=False)
                    if target == "clean-all":
                        self.assert_aggregate_result(preview)
                    else:
                        self.assertEqual(0, preview.returncode, preview.stdout + preview.stderr)
                    preview_events = self.events(preview)
                    item = next(item for item in preview_events if item.get("path") == str(eligible))
                    self.assertEqual("would_remove", item["action"], item)
                    self.assertTrue(eligible.exists())
                    self.assert_recoverable(preview_events, preview=True)
                self.mark_phase(target + ":force")
                removed = self.run_command(arguments + ["FORCE=1"], cwd, phase=target + ":force", check=False)
                if target == "clean-all":
                    self.assert_aggregate_result(removed)
                else:
                    self.assertEqual(0, removed.returncode, removed.stdout + removed.stderr)
                self.mark_phase("production-assertions")
                events = self.events(removed)
                item = next(item for item in events if item.get("path") == str(eligible))
                self.assertEqual("removed", item["action"], item)
                self.assertFalse(eligible.exists())
                self.assertIn("refs/heads/lane/governance/" + name,
                                 self.git("for-each-ref", "--format=%(refname)"))
                self.assertEqual(self.baseline, self.git("ls-remote", "origin",
                    "refs/heads/lane/governance/" + name).split()[0])
                self.assert_recoverable(events)
                print(json.dumps(dict(entrance=target, options=list(map(str, options)),
                    source=str(self.repository), exit=removed.returncode,
                    removed=[str(eligible)], recoverable=[str(tree) for tree in
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

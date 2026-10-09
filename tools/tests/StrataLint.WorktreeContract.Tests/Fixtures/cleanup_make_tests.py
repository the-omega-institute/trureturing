"""Canonical cleanup Make entrances with current production CLI, Git and OS."""

import json
import os
from pathlib import Path
import select
import shutil
import subprocess
import sys
import tempfile
import unittest

SOURCE = Path(sys.argv.pop(1)).resolve()
SPACED = sys.argv.pop(1) == "spaced"
ENTRANCE = sys.argv.pop(1)
INVOCATION = sys.argv.pop(1)


class CleanupMakeTests(unittest.TestCase):
    def run_command(self, arguments, cwd=None, input=None):
        result = subprocess.run(list(map(str, arguments)), cwd=cwd or self.repository,
                                env=self.environment, input=input, capture_output=True, text=True,
                                timeout=120)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        return result

    def git(self, *arguments, cwd=None, input=None):
        return self.run_command(["git", *arguments], cwd, input).stdout.strip()

    def setUp(self):
        self.workspace = tempfile.TemporaryDirectory(prefix="cleanup-make-")
        self.addCleanup(self.workspace.cleanup)
        self.root = Path(self.workspace.name).resolve()
        self.repository = self.root / ("checkout with  spaces" if SPACED else "checkout")
        self.repository.mkdir()
        self.environment = dict(os.environ, TMPDIR=str(self.root / "tmp"),
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
        # Copy current build inputs, not another revision or an installed CLI substitute.
        files = subprocess.check_output(["git", "ls-files", "-z", "tools"], cwd=SOURCE).split(b"\0")
        paths = [Path(os.fsdecode(name)) for name in files if name]
        paths += list(map(Path, ["Makefile", "Directory.Build.props", "Directory.Packages.props", "global.json"]))
        for relative in paths:
            target = self.repository / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(SOURCE / relative, target)
        self.run_command(["make", "--no-print-directory", "-C", self.repository / "tools", "dotnet",
                          "DOTNET_PROJECT=tools/StrataLint.Cli/StrataLint.Cli.csproj"])
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
        self.job = subprocess.Popen([sys.executable, "-B",
            str(self.repository / "tools/scripts/worktree/worktree_protocol.py"),
            "--source", str(self.repository), "with", "--path", str(self.busy), "--",
            sys.executable, "-c", 'import sys; print("ready",flush=True); sys.stdin.readline()'],
            cwd=self.root, env=self.environment, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True)
        self.addCleanup(self.stop_job)
        self.assertTrue(select.select([self.job.stdout], [], [], 10)[0], "participant readiness")
        self.assertEqual("ready\n", self.job.stdout.readline())

    def stop_job(self):
        if self.job.poll() is None:
            self.job.stdin.write("finish\n")
            self.job.stdin.flush()
        self.job.communicate(timeout=10)
        self.assertEqual(0, self.job.returncode)

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
                eligible = self.add_lane(name)
                arguments = ["make", "--no-print-directory", *options, target, "BASE=dev"]
                if target == "clean-all":
                    arguments += ["CLEAN_CODEX_HOME=" + str(self.root / "codex"),
                                  "CLEAN_SSHX_HOME=" + str(self.root / "sshx"),
                                  "CLEAN_TMP_ROOT=" + self.environment["TMPDIR"], "VERBOSE=1"]
                if target != "worktree-clean":
                    preview = self.run_command(arguments, cwd)
                    preview_events = self.events(preview)
                    item = next(item for item in preview_events if item.get("path") == str(eligible))
                    self.assertEqual("would_remove", item["action"], item)
                    self.assertTrue(eligible.exists())
                    self.assert_retained(preview_events)
                removed = self.run_command(arguments + ["FORCE=1"], cwd)
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


if __name__ == "__main__":
    unittest.main()

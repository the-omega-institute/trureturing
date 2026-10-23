"""Native cleanup batches whose invocation source is itself disposable."""

import json
import os
from pathlib import Path
import shutil
import shlex
import sys
import time


class CleanupAnchorCases:
    def runlocal_stable_source(self):
        self.runlocal_anchor("stable")

    def runlocal_self_source(self):
        self.runlocal_anchor("self")

    def runlocal_inventory_failure(self):
        self.runlocal_anchor("inventory")

    def runlocal_commit_failure(self):
        self.runlocal_anchor("commit")

    def runlocal_policy_refusal(self):
        self.runlocal_anchor("locked")

    def runlocal_anchor(self, mode):
        ROOT = self.source_root
        root = self.workspace("runlocal-anchor-", "/tmp")
        first, second, artifact = root / "first source", root / "second tree", root / "artifact"
        for target, branch in ((first, "anchor-first"), (second, "anchor-second")):
            self.g(self.main, "worktree", "add", "-b", branch, target, self.base)
            (target / "owned").write_text("superseded staged bytes\n")
            self.g(target, "add", "owned")
            (target / "owned").write_text(branch + " tracked\n")
            (target / "untracked").write_text(branch + " untracked\n")
            (target / ".gitignore").write_text("ignored\n__pycache__/\n")
            (target / "ignored").write_text("outside snapshot\n")
        # Execute the actual shipped code from the checkout being recycled.
        for relative in ("tools/scripts/agent/clean-runlocal.sh", "tools/scripts/worktree"):
            source, target = ROOT / relative, first / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            if source.is_dir():
                shutil.copytree(source, target, ignore=shutil.ignore_patterns("__pycache__"))
            else:
                shutil.copy2(source, target)
        artifact.write_text("ordinary artifact\n")
        cwd = first if mode == "self" else root
        relative = lambda path: os.path.relpath(path, cwd)
        paths = list(map(relative, (first, second, artifact)))
        if mode == "self":
            locator = root / "locator"
            locator.symlink_to(first / "dir", target_is_directory=True)
            paths[1] = relative(locator) + "/../../second tree"
        manifest = first / "manifest.json"
        manifest.write_text(json.dumps(dict(paths=paths)))
        environment = dict(os.environ)
        environment.pop("PYTHONDONTWRITEBYTECODE", None)
        environment["PYTHONPYCACHEPREFIX"] = str(first / "python-cache")
        if mode == "locked":
            self.g(self.main, "worktree", "lock", second)
        elif mode == "commit":
            hook = self.main / ".git/hooks/pre-commit"
            hook.write_text('#!/bin/sh\ncase "$PWD" in *"second tree") echo checkpoint-denied >&2; exit 1;; esac\n')
            hook.chmod(0o755)
        elif mode == "inventory":
            binary = root / "bin"
            binary.mkdir()
            shim = binary / "git"
            native = shutil.which("git")
            shim.write_text(f'''#!/bin/sh
if [ ! -e {shlex.quote(str(first))} ]; then
    case "$*" in *"worktree list"*) echo inventory-unavailable >&2; exit 128;; esac
fi
exec {shlex.quote(native)} "$@"
''')
            shim.chmod(0o755)
            environment["PATH"] = str(binary) + os.pathsep + environment["PATH"]
        aged = time.time() - 3600
        for target in (first, second, artifact):
            for path in ([*target.rglob("*"), target] if target.is_dir() else [target]):
                os.utime(path, (aged, aged))
        command = ["/bin/bash", relative(first / "tools/scripts/agent/clean-runlocal.sh"),
                   "--manifest", relative(manifest), "--root", str(root),
                   "--source", relative(first), "--delete"]
        result = self.run_owned_command(command, cwd, phase="runlocal-anchor", timeout=30,
                                        check=False, env=environment)
        self.assertEqual(74 if mode in ("inventory", "commit") else 0, result.returncode,
                         result.stdout + result.stderr)
        entries = json.loads(result.stdout)["entries"]
        expected = (['removed', 'error', 'error'] if mode == "inventory" else
                    ['removed', 'error', 'removed'] if mode == "commit" else
                    ['removed', 'kept', 'removed'] if mode == "locked" else
                    ['removed', 'removed', 'removed'])
        self.assertEqual(expected, [item["state"] for item in entries], entries)
        self.assertEqual(paths, [item["path"] for item in entries])
        if mode == "inventory":
            self.assertIn("inventory-unavailable", entries[1]["reason"])
        elif mode == "commit":
            self.assertIn("checkpoint-denied", entries[1]["reason"])
        elif mode == "locked":
            self.assertEqual("locked_recent", entries[1]["reason"])
        for target, branch, entry in zip((first, second), ("anchor-first", "anchor-second"), entries):
            if entry["state"] == "removed":
                self.assertFalse(target.exists())
                recovered = root / (branch + "-recovered")
                self.g(self.main, "worktree", "add", recovered, branch)
                for name in ("owned", "untracked"):
                    suffix = "tracked" if name == "owned" else name
                    self.assertEqual(branch + " " + suffix + "\n", (recovered / name).read_text())
                self.assertFalse((recovered / "ignored").exists())
            else:
                self.assertEqual(self.base, self.g(self.main, "rev-parse", branch).strip())
                self.assertEqual(branch + " tracked\n", (target / "owned").read_text())
                self.assertEqual(branch + " untracked\n", (target / "untracked").read_text())
        self.assertEqual(mode == "inventory", artifact.exists())
        print(json.dumps(dict(event="runlocal_anchor_result", mode=mode, exit=result.returncode,
                              entries=entries, recovery_verified=True)), flush=True)

    def protocol_relative_batch(self):
        ROOT = self.source_root
        second = self.root / "second"
        self.g(self.main, "worktree", "add", "-b", "relative-second", second, self.base)
        scripts = self.tree / "tools/scripts/worktree"
        shutil.copytree(ROOT / "tools/scripts/worktree", scripts,
                        ignore=shutil.ignore_patterns("__pycache__"))
        for target in (self.tree, second):
            (target / "owned").write_text(target.name + " tracked\n")
            (target / "untracked").write_text(target.name + " untracked\n")
        result = self.run_owned_command([sys.executable, "-B", "tools/scripts/worktree/worktree_protocol.py",
            "--source", ".", "remove", "--path", ".", "--path", "../second"], self.tree,
            phase="protocol-relative-anchor", timeout=30)
        self.assertEqual(["removed", "removed"],
                         [item["outcome"] for item in json.loads(result.stdout)["items"]])
        for target, branch in ((self.tree, self.branch), (second, "relative-second")):
            recovered = self.root / (target.name + "-recovered")
            self.g(self.main, "worktree", "add", recovered, branch)
            self.assertFalse(target.exists())
            self.assertEqual(target.name + " tracked\n", (recovered / "owned").read_text())
            self.assertEqual(target.name + " untracked\n", (recovered / "untracked").read_text())

"""Native lock, initialization and removal recovery behavior with real Git objects."""

import argparse
from contextlib import ExitStack
import json
import os
import select
import signal
import shutil
import sys
import subprocess
from pathlib import Path
from unittest.mock import patch


class LockRecoveryCases:
    def removal_options(self):
        return argparse.Namespace(source=self.main, names="tree", path=[], force=False,
                                  preview=False, expected=[])

    def assert_payload_boundary_retained(self, boundary):
        import worktree_protocol as protocol
        (self.tree / "owned").write_text("uncheckpointed outer bytes\n")
        (boundary / "unique").write_text("nested local bytes\n")
        second = self.root / "second"
        self.g(self.main, "worktree", "add", "-b", "second", second, self.base)
        result = self.run_protocol("remove", "--names", "second tree", expect=73)
        self.assertIn("nested_git_boundary:", result.stderr)
        self.assertTrue(second.is_dir(), "batch preflight must precede all deletion")
        self.assertEqual("uncheckpointed outer bytes\n", (self.tree / "owned").read_text())
        self.assertEqual("nested local bytes\n", (boundary / "unique").read_text())
        self.assertEqual(self.base, self.g(self.main, "rev-parse", self.branch).strip())
        self.assertIn(str(self.tree), [row["worktree"] for row in protocol.inventory(self.main)])

    def test_removal_refuses_nested_repository_before_any_payload(self):
        boundary = self.tree / ".lake/vendor"
        boundary.mkdir(parents=True)
        self.g(boundary, "init")
        (self.tree / ".gitignore").write_text(".lake/\n")
        self.assert_payload_boundary_retained(boundary)

    def test_removal_refuses_gitlink_before_any_payload(self):
        boundary = self.tree / "module"
        boundary.mkdir()
        self.g(self.tree, "update-index", "--add", "--cacheinfo", "160000," + self.base + ",module")
        self.assert_payload_boundary_retained(boundary)

    def test_removal_refuses_submodule_before_any_payload(self):
        self.g(self.tree, "-c", "protocol.file.allow=always", "submodule", "add", self.main, "module")
        self.assert_payload_boundary_retained(self.tree / "module")

    def test_removal_refuses_foreign_worktree_before_any_payload(self):
        foreign = self.root / "foreign"
        self.g(self.root, "clone", self.main, foreign)
        boundary = self.tree / "foreign-tree"
        self.g(foreign, "worktree", "add", "-b", "nested", boundary)
        self.assert_payload_boundary_retained(boundary)

    def test_removal_refuses_bare_repository_before_any_payload(self):
        boundary = self.tree / "inner.git"
        self.g(self.root, "clone", "--bare", self.main, boundary)
        self.assert_payload_boundary_retained(boundary)

    def assert_removal_recoverable(self, metadata):
        import worktree_preservation as preservation
        import worktree_protocol as protocol
        self.assertIn(str(self.tree), [row["worktree"] for row in protocol.inventory(self.main)])
        record = json.loads((metadata / preservation.REMOVAL_RECORD).read_text())
        self.assertEqual(record["commit"], self.g(self.main, "rev-parse", self.branch).strip())
        self.assertEqual("snapshot before deletion\n", self.g(self.main, "show", self.branch + ":owned"))
        return record

    def interrupt_after_ignore_deletion(self):
        import worktree_preservation as preservation
        (self.tree / "owned").write_text("snapshot before deletion\n")
        (self.tree / ".gitignore").write_text(".lake/\n")
        cache = self.tree / ".lake/build"
        cache.mkdir(parents=True)
        (cache / "output").write_text("ignored build output\n")
        native_iterdir, native_unlink = Path.iterdir, Path.unlink
        def ignore_first(path):
            children = list(native_iterdir(path))
            return iter(sorted(children, key=lambda child: child.name != ".gitignore"))
        def interrupted_unlink(path, *args, **kwargs):
            result = native_unlink(path, *args, **kwargs)
            if path == self.tree / ".gitignore":
                raise OSError("interrupted after ignore deletion")
            return result
        with patch.object(Path, "iterdir", ignore_first), patch.object(Path, "unlink", interrupted_unlink):
            item = preservation.remove(self.removal_options())["items"][0]
        self.assertEqual("partial_or_indeterminate", item["outcome"])
        self.assertIn("interrupted after ignore deletion", item["error"])
        self.assertFalse((self.tree / ".gitignore").exists())
        self.assertTrue((cache / "output").is_file())
        return item["checkpoint"]["commit"]

    def test_removal_resumes_after_worktree_ignore_is_deleted(self):
        snapshot = self.interrupt_after_ignore_deletion()
        item = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual(("removed", "resumed"), (item["outcome"], item["checkpoint"]["status"]))
        self.assertFalse(self.tree.exists())
        self.assertEqual(snapshot, self.g(self.main, "rev-parse", self.branch).strip())
        self.assertEqual(".lake/\n", self.g(self.main, "show", self.branch + ":.gitignore"))

    def test_removal_with_deleted_ignore_retains_new_ordinary_file(self):
        snapshot = self.interrupt_after_ignore_deletion()
        late = self.tree / "late\nordinary"
        late.write_text("new ordinary bytes\n")
        item = json.loads(self.remove(expect=74).stdout)["items"][0]
        self.assertEqual("checkpoint_failed", item["outcome"])
        self.assertIn("interrupted_removal_tree_changed", item["error"])
        self.assertEqual("new ordinary bytes\n", late.read_text())
        self.assertTrue((self.tree / ".lake/build/output").is_file())
        self.assertEqual(snapshot, self.g(self.main, "rev-parse", self.branch).strip())

    def test_removal_payload_failure_retains_registration_and_resumes(self):
        import worktree_preservation as preservation
        (self.tree / "owned").write_text("snapshot before deletion\n")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        native_unlink = os.unlink
        native_git = preservation.git
        deleted = []
        def fail_during_payload(path, *args, **kwargs):
            result = native_unlink(path, *args, **kwargs)
            deleted.append(os.fsdecode(path))
            raise OSError("payload deletion interrupted")
        def observe_git(path, *args, **kwargs):
            self.assertNotEqual(("worktree", "remove"), args[:2], "payload remains registered")
            return native_git(path, *args, **kwargs)
        with patch.object(os, "unlink", side_effect=fail_during_payload), \
                patch.object(preservation, "git", side_effect=observe_git):
            item = preservation.remove(self.removal_options())["items"][0]
        self.assertEqual("partial_or_indeterminate", item["outcome"])
        self.assertIn("payload deletion interrupted", item["error"])
        self.assertTrue(deleted)
        record = self.assert_removal_recoverable(metadata)
        resumed = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual(("removed", "resumed"), (resumed["outcome"], resumed["checkpoint"]["status"]))
        self.assertFalse(self.tree.exists())
        self.assertEqual(record["commit"], self.g(self.main, "rev-parse", self.branch).strip())

    def test_removal_payload_process_death_retains_registration_and_resumes(self):
        (self.tree / "owned").write_text("snapshot before deletion\n")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        code = f'''import argparse,os,signal,sys
from pathlib import Path
sys.path.insert(0, {str(self.source_root / "tools/scripts/worktree")!r})
import worktree_preservation as preservation
native_unlink = os.unlink
def die_during_payload(path, *args, **kwargs):
    native_unlink(path, *args, **kwargs)
    os.kill(os.getpid(), signal.SIGKILL)
os.unlink = die_during_payload
preservation.remove(argparse.Namespace(source=Path({str(self.main)!r}), names="tree",
    path=[], force=False, preview=False, expected=[]))
'''
        result = self.run_owned_command([sys.executable, "-B", "-c", code], self.root,
                                        phase="payload-death", timeout=30, check=False)
        self.assertEqual(-signal.SIGKILL, result.returncode)
        record = self.assert_removal_recoverable(metadata)
        resumed = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual("resumed", resumed["checkpoint"]["status"])
        self.assertFalse(self.tree.exists())
        self.assertEqual(record["commit"], self.g(self.main, "rev-parse", self.branch).strip())

    def test_native_unregistration_failure_leaves_only_git_link(self):
        import worktree_preservation as preservation
        (self.tree / "owned").write_text("snapshot before deletion\n")
        cache = self.tree / ".lake/build"
        cache.mkdir(parents=True)
        (cache / "output").write_text("ignored build output\n")
        (self.main / ".git/info/exclude").write_text(".lake/\n")
        outside = self.root / "outside"
        outside.mkdir()
        (outside / "keep").write_text("external bytes\n")
        (self.tree / "outside-link").symlink_to(outside, target_is_directory=True)
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        native_git = preservation.git
        def fail_unregistration(path, *args, **kwargs):
            if args[:2] == ("worktree", "remove"):
                raise OSError("native unregistration interrupted")
            return native_git(path, *args, **kwargs)
        with patch.object(preservation, "git", side_effect=fail_unregistration):
            item = preservation.remove(self.removal_options())["items"][0]
        self.assertEqual("partial_or_indeterminate", item["outcome"])
        self.assertEqual([".git"], sorted(path.name for path in self.tree.iterdir()))
        self.assertEqual("external bytes\n", (outside / "keep").read_text())
        record = self.assert_removal_recoverable(metadata)
        self.remove()
        self.assertFalse(self.tree.exists())
        self.assertEqual(record["commit"], self.g(self.main, "rev-parse", self.branch).strip())

    def test_holderless_native_locks_checkpoint_once(self):
        import worktree_protocol as protocol
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        for lock in (metadata / "index.lock", self.main / (".git/refs/heads/" + self.branch + ".lock")):
            with self.subTest(lock=str(lock)):
                lock.parent.mkdir(parents=True, exist_ok=True)
                lock.write_text("residual\n")
                (self.tree / "owned").write_text(str(lock) + "\n")
                result = self.checkpoint()
                self.assertIn("native_lock_cleared", result.stdout)
                self.assertFalse(lock.exists())
                self.assertEqual(str(lock) + "\n", self.g(self.tree, "show", "HEAD:owned"))
        with ExitStack() as stack:
            protocol.tree_scope(stack, self.main, self.tree, True)

    def test_detached_head_native_lock_can_recover_snapshot(self):
        self.g(self.tree, "checkout", "--detach")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        (metadata / "HEAD.lock").write_text("residual head transaction\n")
        (self.tree / "owned").write_text("detached recovered bytes\n")
        result = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual("detached recovered bytes\n", self.g(self.main, "show", result["recovery_branch"] + ":owned"))
        self.assertEqual(str(metadata / "HEAD.lock"), result["checkpoint"]["native_locks"][0]["path"])

    def test_held_native_lock_retains_exact_blocker(self):
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        lock = metadata / "index.lock"
        with lock.open("w") as holder:
            holder.write("live\n")
            holder.flush()
            result = self.checkpoint(expect=73)
            self.assertIn("native_lock_held:" + str(lock), result.stderr)
            self.assertTrue(lock.exists())

    def test_unverifiable_and_replaced_native_lock_retained(self):
        import worktree_protocol as protocol
        import worktree_publication as publication
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        lock = metadata / "index.lock"
        options = argparse.Namespace(source=self.main, path=self.tree, message_file=None)
        lock.write_text("residual\n")
        with patch.object(protocol, "native_lock_holders", side_effect=OSError("inspection denied")):
            with self.assertRaisesRegex(protocol.Refused, "native_lock_unverifiable:"):
                publication.checkpoint(options)
        def replaced(path):
            replacement = path.with_name("replacement")
            replacement.write_text("replacement bytes\n")
            replacement.replace(path)
            return []
        with patch.object(protocol, "native_lock_holders", side_effect=replaced):
            with self.assertRaisesRegex(protocol.Refused, "native_lock_changed:"):
                publication.checkpoint(options)
        self.assertEqual("replacement bytes\n", lock.read_text())

    def test_native_lock_failure_receipts_keep_lock_observations(self):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        lock = metadata / "index.lock"
        lock.write_text("residual\n")
        options = argparse.Namespace(source=self.main, names="tree", path=[], force=False,
                                     preview=False, expected=[])
        for inspection in (["holder"], OSError("inspection denied")):
            with patch.object(protocol, "native_lock_holders", side_effect=(
                    inspection if isinstance(inspection, Exception) else lambda _: inspection)):
                result = preservation.remove(options)
            item = result["items"][0]
            self.assertEqual("checkpoint_failed", item["outcome"])
            evidence = item["native_locks"][0]
            self.assertEqual(str(lock), evidence["path"])
            self.assertEqual(len("residual\n"), evidence["size"])
            self.assertIsInstance(evidence["age_seconds"], float)
            self.assertTrue(lock.exists())
            self.assertTrue(self.tree.exists())

    def test_native_clearance_requires_exclusive_tree(self):
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        lock = metadata / "index.lock"
        lock.write_text("residual\n")
        self.hold()
        self.checkpoint(expect=73)
        self.assertTrue(lock.exists())

    def test_native_clearance_survives_failed_checkpoint_retry(self):
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        lock = metadata / "index.lock"
        hooks = self.root / "rejecting-hooks"
        hooks.mkdir()
        hook = hooks / "pre-commit"
        hook.write_text("#!/bin/sh\nexit 1\n")
        hook.chmod(0o755)
        self.g(self.tree, "config", "core.hooksPath", hooks)
        (self.tree / "owned").write_text("checkpoint retry bytes\n")
        for action in ("checkpoint", "remove"):
            with self.subTest(action=action):
                lock.write_text("cleared before failed retry\n")
                result = self.checkpoint(expect=73) if action == "checkpoint" else self.remove(expect=74)
                receipt = json.loads(result.stdout)
                if action == "remove":
                    receipt = receipt["items"][0]
                observation = receipt["native_locks"][0]
                self.assertEqual("native_lock_cleared", observation["status"])
                self.assertEqual(str(lock), observation["path"])
                self.assertEqual(len("cleared before failed retry\n"), observation["size"])
                self.assertIsInstance(observation["age_seconds"], float)
                self.assertFalse(lock.exists())
                self.assertTrue(self.tree.exists())

    def test_reconvergence_receipt_retains_native_clearance(self):
        self.interrupted_removal()
        self.g(self.tree, "commit", "--allow-empty", "-m", "moved snapshot")
        (self.tree / "owned").write_text("current bytes\n")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        lock = metadata / "index.lock"
        lock.write_text("reconvergence lock\n")
        receipt = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual("reconverged", receipt["checkpoint"]["status"])
        observation = receipt["checkpoint"]["native_locks"][0]
        self.assertEqual("native_lock_cleared", observation["status"])
        self.assertEqual(str(lock), observation["path"])
        self.assertEqual(len("reconvergence lock\n"), observation["size"])
        self.assertIsInstance(observation["age_seconds"], float)

    def test_dead_initializer_is_removable_without_lock_age(self):
        self.g(self.main, "worktree", "lock", "--reason", "worktree-init:dead", self.tree)
        self.remove()
        self.assertFalse(self.tree.exists())

    def test_live_initializer_is_retained(self):
        self.g(self.main, "worktree", "lock", "--reason", "worktree-init:alive", self.tree)
        self.hold("--exclusive")
        result = self.remove(expect=73)
        self.assertIn("initialization_in_progress", result.stderr)
        self.assertTrue(self.tree.exists())

    def test_native_clearance_keeps_dead_initializer_exclusive_until_removal(self):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        self.g(self.main, "worktree", "lock", "--reason", "worktree-init:dead", self.tree)
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        (metadata / "index.lock").write_text("residual\n")
        (self.tree / "owned").write_text("recover before removal\n")
        original_git = preservation.git
        checked = []
        def guarded_git(path, *arguments, **options):
            if arguments[:2] == ("worktree", "remove"):
                with ExitStack() as contender:
                    with self.assertRaisesRegex(protocol.Refused, "busy_scope:tree:"):
                        protocol.tree_scope(contender, self.main, self.tree)
                checked.append(True)
            return original_git(path, *arguments, **options)
        options = argparse.Namespace(source=self.main, names="tree", path=[], force=False,
                                     preview=False, expected=[])
        with patch.object(preservation, "git", side_effect=guarded_git):
            result = preservation.remove(options)
        self.assertEqual("succeeded", result["status"])
        self.assertEqual([True], checked)
        self.assertFalse(self.tree.exists())

    def owned_initialization(self, registered=True):
        import worktree_protocol as protocol
        token = "worktree-init:" + "a" * 32
        branch = "lane/governance/owned-init"
        target = self.root / "initializing"
        self.g(self.main, "update-ref", "--create-reflog", "-m", token,
               "refs/heads/" + branch, self.base, "0" * len(self.base))
        if registered:
            self.g(self.main, "worktree", "add", "--no-checkout", "--lock", "--reason", token, target, branch)
        return target, branch, token

    def test_failed_initialization_recovers_in_place_idempotently(self):
        target, branch, token = self.owned_initialization()
        (target / "owned").write_text("bytes from interrupted checkout\n")
        for attempt in range(2):
            self.run_protocol("recover-init", "--path", target, "--branch", branch,
                              "--base", self.base, "--skip-restore")
            self.assertEqual("bytes from interrupted checkout\n", (target / "owned").read_text())
            self.assertTrue((target / "other").is_file())
        references = self.g(self.main, "for-each-ref", "--format=%(refname)",
                            "refs/heads/lane/governance/recovery-*").splitlines()
        self.assertTrue(references)
        self.assertTrue(any(self.g(self.main, "show", ref + ":owned") ==
                            "bytes from interrupted checkout\n" for ref in references))

    def test_large_initialization_checkout_preserves_partial_bytes(self):
        import worktree_protocol as protocol
        import worktree_publication as publication
        # A package-free SDK project exercises the real restore stage offline.
        tools = self.main / "tools"
        tools.mkdir()
        (self.main / "global.json").write_bytes((self.source_root / "global.json").read_bytes())
        (self.main / ".gitignore").write_text("**/obj/\n**/bin/\n")
        (self.main / "NuGet.Config").write_text(
            "<configuration><packageSources><clear /></packageSources></configuration>")
        (tools / "Fixture.csproj").write_text(
            '<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup>'
            '<TargetFramework>net10.0</TargetFramework>'
            '<RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup></Project>')
        (tools / "packages.lock.json").write_text('{"version":1,"dependencies":{"net10.0":{}}}\n')
        project = "{11111111-1111-1111-1111-111111111111}"
        (tools / "StrataLint.sln").write_text(
            'Microsoft Visual Studio Solution File, Format Version 12.00\n'
            'Project("{FAE04EC0-301F-11D3-BF4B-00C04F79EFBC}") = '
            '"Fixture", "Fixture.csproj", "' + project + '"\nEndProject\n'
            'Global\nGlobalSection(SolutionConfigurationPlatforms) = preSolution\n'
            'Debug|Any CPU = Debug|Any CPU\nEndGlobalSection\n'
            'GlobalSection(ProjectConfigurationPlatforms) = postSolution\n'
            + project + '.Debug|Any CPU.ActiveCfg = Debug|Any CPU\n'
            + project + '.Debug|Any CPU.Build.0 = Debug|Any CPU\nEndGlobalSection\nEndGlobal\n')
        self.g(self.main, "add", ".")
        self.g(self.main, "commit", "-m", "offline initialization restore fixture")
        self.base = self.g(self.main, "rev-parse", "HEAD").strip()
        target, branch, token = self.owned_initialization()
        payload = b"interrupted checkout bytes\x00\xff\n"
        (target / "owned").write_bytes(payload)
        metadata = Path(self.g(target, "rev-parse", "--absolute-git-dir").strip())
        witness = self.main / (".git/logs/refs/heads/" + branch)
        creation_record = witness.read_bytes()
        (metadata / "index.lock").write_text("dead initializer\n")

        binary = self.root / "delayed-git"
        binary.mkdir()
        ready, release = self.root / "git.ready", self.root / "git.release"
        os.mkfifo(ready)
        os.mkfifo(release)
        real_git = shutil.which("git")
        shim = binary / "git"
        shim.write_text(f'''#!{sys.executable}
import os,sys
if len(sys.argv) > 3 and sys.argv[2] == {str(target)!r} and sys.argv[3] in ("add", "checkout-index", "update-index"):
    with open({str(ready)!r}, "w") as output: output.write(sys.argv[3] + "\\n")
    with open({str(release)!r}) as input: input.readline()
os.execv({real_git!r}, [{real_git!r}] + sys.argv[1:])
''')
        shim.chmod(0o755)
        reader = os.open(ready, os.O_RDONLY | os.O_NONBLOCK)
        self.addCleanup(os.close, reader)
        # Keep a writer open so successive readiness reads cannot observe FIFO EOF.
        writer = os.open(ready, os.O_WRONLY | os.O_NONBLOCK)
        self.addCleanup(os.close, writer)
        native_communicate = subprocess.Popen.communicate
        completed = []

        def delayed_communicate(process, input=None, timeout=None):
            args = process.args
            if (len(args) < 4 or args[0] != "git" or args[2] != str(target)
                    or args[3] not in ("add", "checkout-index", "update-index")):
                return native_communicate(process, input, timeout)
            self.assertTrue(select.select([reader], [], [], 10)[0], "delayed Git readiness timeout")
            self.assertEqual((args[3] + "\n").encode(), os.read(reader, 100))
            self.assertEqual(token, (metadata / "locked").read_text().strip())
            self.assertEqual(creation_record, witness.read_bytes())
            with ExitStack() as contender:
                with self.assertRaisesRegex(protocol.Refused, "busy_scope"):
                    protocol.tree_scope(contender, self.main, target, True)
            # Compress any finite production deadline while Git is deterministically
            # blocked. The host releases supervised operations; no long wait is needed.
            if timeout is not None:
                return native_communicate(process, input, timeout=0.05)
            with release.open("w") as output:
                output.write("host release\n")
            result = native_communicate(process, input, timeout=10)
            completed.append((args[3], process.returncode))
            return result

        options = argparse.Namespace(source=self.main, path=target, branch=branch,
                                     base=self.base, skip_restore=False)
        with patch.dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"]), \
                patch.object(subprocess.Popen, "communicate", delayed_communicate):
            result = publication.recover_initialization(options)
        self.assertEqual([("add", 0), ("checkout-index", 0), ("update-index", 1)], completed)
        self.assertEqual("recovered", result["status"])
        self.assertEqual("native_lock_cleared", result["native_locks"][0]["status"])
        self.assertEqual(creation_record, witness.read_bytes())
        self.assertEqual(payload, (target / "owned").read_bytes())
        recovery = result["recovery_branch"]
        self.assertTrue(recovery)
        self.assertEqual(payload, protocol.git(self.main, "show", recovery + ":owned").stdout)
        self.assertTrue((target / "other").is_file())
        self.assertTrue((target / "tools/obj/project.assets.json").is_file())
        self.assertEqual(self.base, self.g(target, "rev-parse", "HEAD").strip())
        self.assertEqual(self.g(target, "rev-parse", "HEAD^{tree}"), self.g(target, "write-tree"))
        self.assertFalse((metadata / "locked").exists())
        self.assertFalse((metadata / "index.lock").exists())
        self.assertEqual([], list(metadata.glob("initialization-index-*")))
        self.assertIn("worktree-recovered:" + token.removeprefix("worktree-init:"),
                      self.g(target, "reflog", "show", "--format=%gs", "HEAD"))
        # The preserved working edit is expected; returning it to the base leaves
        # a clean checkout while the recovery ref still retains the exact bytes.
        self.g(target, "restore", "--worktree", "--", "owned")
        self.assertEqual("", self.g(target, "status", "--porcelain"))
        self.assertEqual(payload, protocol.git(self.main, "show", recovery + ":owned").stdout)

    def test_owned_unregistered_branch_can_resume(self):
        target, branch, token = self.owned_initialization(registered=False)
        (self.main / "lean-toolchain").write_text("leanprover/lean4:v4.34.2\n")
        self.g(self.main, "add", "lean-toolchain")
        self.g(self.main, "commit", "--allow-empty", "-m", "advance requested base")
        advanced = self.g(self.main, "rev-parse", "HEAD").strip()
        for attempt in range(2):
            self.run_protocol("recover-init", "--path", target, "--branch", branch,
                              "--base", advanced, "--skip-restore")
            self.assertEqual("original\n" if attempt == 0 else "ordinary bytes\n",
                             (target / "owned").read_text())
            self.assertEqual(self.base, self.g(target, "rev-parse", "HEAD").strip())
            self.assertEqual("leanprover/lean4:v4.34.1\n", (target / "lean-toolchain").read_text())
            (target / "owned").write_text("ordinary bytes\n")

    def test_ordinary_recovery_routing_keeps_shared_reuse_and_base_protection(self):
        self.hold("--write", "other")
        (self.tree / "owned").write_text("ordinary bytes\n")
        self.run_protocol("recover-init", "--path", self.tree, "--branch", self.branch,
                          "--base", self.base, "--skip-restore")
        self.g(self.main, "commit", "--allow-empty", "-m", "advance ordinary base")
        advanced = self.g(self.main, "rev-parse", "HEAD").strip()
        refused = self.run_protocol("recover-init", "--path", self.tree, "--branch", self.branch,
                                    "--base", advanced, "--skip-restore", expect=73)
        self.assertIn("incompatible_base", refused.stderr)
        self.assertEqual("ordinary bytes\n", (self.tree / "owned").read_text())

    def test_partial_registration_repairs_worktree_head_in_its_own_ref_store(self):
        import worktree_publication as publication
        target, branch, token = self.owned_initialization()
        metadata = Path(self.g(target, "rev-parse", "--absolute-git-dir").strip())
        (metadata / "HEAD").unlink()
        native_git = publication.git
        def strict_git(path, *arguments, **options):
            if "symbolic-ref" in arguments and "-m" in arguments:
                reference = arguments[arguments.index("symbolic-ref") + 3]
                self.assertEqual("HEAD", reference)
            return native_git(path, *arguments, **options)
        def interrupt_reattachment(path, *arguments, **options):
            result = strict_git(path, *arguments, **options)
            if arguments[:2] == ("update-ref", "--no-deref") and arguments[2].startswith("worktrees/"):
                raise OSError("HEAD reattachment interrupted")
            return result
        options = argparse.Namespace(source=self.main, path=target, branch=branch,
                                     base=self.base, skip_restore=True)
        with patch.object(publication, "git", side_effect=interrupt_reattachment):
            with self.assertRaisesRegex(OSError, "HEAD reattachment interrupted"):
                publication.recover_initialization(options)
        self.assertEqual(token, (metadata / "locked").read_text().strip())
        with patch.object(publication, "git", side_effect=strict_git):
            publication.recover_initialization(options)
        self.assertEqual("refs/heads/" + branch, self.g(target, "symbolic-ref", "HEAD").strip())
        self.assertFalse((metadata / "locked").exists())

    def test_initialization_identity_changes_refuse_recovery(self):
        target, branch, token = self.owned_initialization()
        metadata = Path(self.g(target, "rev-parse", "--absolute-git-dir").strip())
        for failure in ("token", "branch", "backlink", "tip"):
            with self.subTest(failure=failure):
                saved = (metadata / "gitdir").read_text()
                if failure == "token":
                    (metadata / "locked").write_text("worktree-init:foreign\n")
                elif failure == "branch":
                    self.g(target, "symbolic-ref", "HEAD", "refs/heads/" + self.branch)
                elif failure == "backlink":
                    (metadata / "gitdir").write_text(str(self.tree / ".git") + "\n")
                else:
                    self.g(target, "read-tree", "HEAD")
                    self.g(target, "commit", "--allow-empty", "-m", "changed creation branch")
                self.run_protocol("recover-init", "--path", target, "--branch", branch,
                                  "--base", self.base, "--skip-restore", expect=73)
                (metadata / "locked").write_text(token + "\n")
                (metadata / "gitdir").write_text(saved)
                self.g(target, "symbolic-ref", "HEAD", "refs/heads/" + branch)
                self.g(self.main, "update-ref", "refs/heads/" + branch, self.base)
        self.assertFalse((target / "owned").exists())

    def test_removal_record_mismatch_reconverges_and_keeps_both_roots(self):
        original = self.interrupted_removal()["checkpoint"]["commit"]
        self.g(self.tree, "commit", "--allow-empty", "-m", "later head")
        (self.tree / "owned").write_text("current bytes\n")
        result = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual("reconverged", result["checkpoint"]["status"])
        self.assertEqual("current bytes\n", self.g(self.main, "show", result["recovery_branch"] + ":owned"))
        refs = self.g(self.main, "for-each-ref", "--format=%(objectname)",
                      "refs/heads/lane/governance/recovery-*").splitlines()
        self.assertIn(original, refs)

    def test_reconvergence_interruption_retains_record_and_recovery_objects(self):
        import worktree_preservation as preservation
        original = self.interrupted_removal()["checkpoint"]["commit"]
        self.g(self.tree, "commit", "--allow-empty", "-m", "moved snapshot")
        (self.tree / "owned").write_text("new bytes\n")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        options = argparse.Namespace(source=self.main, names="tree", path=[], force=False,
                                     preview=False, expected=[])
        with patch.object(preservation, "record_removal", side_effect=OSError("record interrupted")):
            result = preservation.remove(options)
        self.assertEqual("failed", result["status"])
        self.assertEqual(original, json.loads((metadata / "worktree-removal").read_text())["commit"])
        refs = self.g(self.main, "for-each-ref", "--format=%(objectname)",
                      "refs/heads/lane/governance/recovery-*").splitlines()
        self.assertIn(original, refs)
        self.assertIn(self.g(self.tree, "rev-parse", "HEAD").strip(), refs)
        self.remove()

    def test_resume_validates_and_coordinates_recorded_predecessors(self):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        self.interrupted_removal()
        self.g(self.tree, "commit", "--allow-empty", "-m", "moved snapshot")
        (self.tree / "owned").write_text("new bytes\n")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        native_git = preservation.git
        def interrupt(path, *arguments, **options):
            if arguments[:2] == ("worktree", "remove"):
                raise subprocess.TimeoutExpired(["git", *arguments], 300)
            return native_git(path, *arguments, **options)
        options = argparse.Namespace(source=self.main, names="tree", path=[], force=False,
                                     preview=False, expected=[])
        with patch.object(preservation, "git", side_effect=interrupt):
            result = preservation.remove(options)
        self.assertEqual("failed", result["status"])
        predecessor = json.loads((metadata / "worktree-removal").read_text())["predecessors"][0]
        reference = predecessor["recovery_branch"]
        with ExitStack() as holder:
            protocol.acquire(holder, self.main, "ref:" + reference, True)
            failed = preservation.remove(options)["items"][0]
            self.assertEqual("checkpoint_failed", failed["outcome"])
            self.assertIn("busy_scope:ref:" + reference, failed["error"])
        self.g(self.main, "update-ref", reference, "HEAD")
        # Use a distinct commit so the recorded predecessor cannot validate.
        self.g(self.main, "commit", "--allow-empty", "-m", "foreign predecessor")
        self.g(self.main, "update-ref", reference, "HEAD")
        failed = preservation.remove(options)["items"][0]
        self.assertEqual("checkpoint_failed", failed["outcome"])
        self.assertIn("interrupted_removal_recovery_root_changed", failed["error"])
        self.g(self.main, "update-ref", reference, predecessor["commit"])
        resumed = json.loads(self.remove().stdout)["items"][0]
        self.assertIn(reference, resumed["recovery_roots"])

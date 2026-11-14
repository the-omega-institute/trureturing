"""Disposable Git checks for the age/stale worktree lifecycle."""
import os
import fcntl
import json
import shutil
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(sys.argv.pop(1)).resolve()
sys.path.insert(0, str(ROOT / "tools/scripts/worktree"))
import worktree_protocol as protocol
import worktree_pool as pool
import worktree_preservation as preservation
import worktree_maintenance as maintenance


def run(cwd, *args, env=None, check=True):
    result = subprocess.run(["git", "-C", str(cwd), *map(str, args)],
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            env=protocol.git_environment(env), check=False)
    if check and result.returncode:
        raise AssertionError(result.stderr)
    return result


class LifecycleTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="stale-lifecycle-")
        self.root = Path(self.tmp.name).resolve()
        self.main = self.root / "main"
        run(self.root, "init", "--bare", self.root / "remote.git")
        run(self.root, "init", "--initial-branch=dev", self.main)
        run(self.main, "config", "user.name", "Lifecycle Tests")
        run(self.main, "config", "user.email", "lifecycle@example.invalid")
        for name in ("lean-toolchain", "lake-manifest.json", "Reg/lakefile.toml",
                     "Reg/lake-manifest.json", "tools/lean-inspector-reg/lakefile.toml",
                     "tools/lean-inspector-reg/lake-manifest.json"):
            target = self.main / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, target)
        run(self.main, "add", ".")
        run(self.main, "commit", "-m", "base")
        self.base = run(self.main, "rev-parse", "HEAD").stdout.strip()
        self.source = self.main
        run(self.main, "update-ref", "refs/remotes/origin/dev", self.base)

    def tearDown(self):
        self.tmp.cleanup()

    def commit_branch(self, name, path, age, content="branch\n"):
        run(self.main, "branch", name, self.base)
        run(self.main, "worktree", "add", path, name)
        (Path(path) / "payload").write_text(content)
        run(path, "add", "payload")
        stamp = str(int(time.time()) - age)
        run(path, "commit", "-m", "payload", env={"GIT_AUTHOR_DATE": "@" + stamp,
                                                     "GIT_COMMITTER_DATE": "@" + stamp})
        return run(path, "rev-parse", "HEAD").stdout.strip()

    def cli(self, *args, cwd=None, check=True, env=None):
        result = subprocess.run([shutil.which("dotnet"), str(ROOT /
            "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"), *map(str, args)],
            cwd=cwd or self.source, text=True, capture_output=True,
            env=protocol.git_environment(env), timeout=60)
        if check:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def create(self, name, path, reuse_any=False, check=True, cwd=None):
        return self.cli("worktree", "--kind", "governance", "--name", name,
                        "--path", path, "--base", self.base, "--skip-restore",
                        *(["--reuse-any"] if reuse_any else []), check=check, cwd=cwd)

    def prepare_make(self):
        # This launcher only replaces dotnet run's build with this test's freshly
        # built CLI. Every lifecycle action and native Git effect is real.
        scripts = self.main / "tools/scripts"
        shutil.copytree(ROOT / "tools/scripts/worktree", scripts / "worktree")
        shutil.copytree(ROOT / "tools/scripts/report", scripts / "report")
        inspector = self.main / "tools/lean-inspector"
        inspector.mkdir()
        for module in (ROOT / "tools/lean-inspector").glob("*.py"):
            shutil.copy2(module, inspector / module.name)
        for name in ("host-cleanup.py", "worktree-init.sh", "clean-lanes.sh", "maintenance_log.py"):
            shutil.copy2(ROOT / "tools/scripts" / name, scripts / name)
        for name in ("Makefile", "tools/Makefile"):
            shutil.copy2(ROOT / name, self.main / name)
        tools = self.main / "tools"
        (tools / "Fixture.csproj").write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup>'
            '<TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>\n')
        (tools / "StrataLint.sln").write_text('Microsoft Visual Studio Solution File, Format Version 12.00\n'
            'Project("{FAE04EC0-301F-11D3-BF4B-00C04F79EFBC}") = "Fixture", "Fixture.csproj", '
            '"{6375E1CB-330C-4D28-8AE5-861A56749FD9}"\nEndProject\nGlobal\nEndGlobal\n')
        run(self.main, "add", ".")
        run(self.main, "commit", "-m", "make entrances")
        self.base = run(self.main, "rev-parse", "HEAD").stdout.strip()
        self.bin = self.root / "bin"
        self.bin.mkdir()
        launcher = self.bin / "dotnet"
        launcher.write_text('#!/bin/bash\nif [[ "$1" == run ]]; then\n'
            '  while [[ $# -gt 0 && "$1" != -- ]]; do shift; done\n'
            '  [[ $# -gt 0 ]] || exit 64\n  shift\n'
            '  exec "$FRONTDOOR_DOTNET" "$FRONTDOOR_CLI" "$@"\nfi\n'
            'exec "$FRONTDOOR_DOTNET" "$@"\n')
        launcher.chmod(0o755)
        self.env = protocol.git_environment({
            "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
            "FRONTDOOR_DOTNET": shutil.which("dotnet"),
            "FRONTDOOR_CLI": str(ROOT / "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"),
            "TMPDIR": str(self.root / "tmp"),
            "CODEX_HOME": str(self.root / "codex"), "SSHX_HOME": str(self.root / "sshx")})
        (self.root / "tmp").mkdir()

    def make(self, *args, cwd=None, check=True):
        result = subprocess.run(["make", "--no-print-directory", *map(str, args)],
                                cwd=cwd or self.main, env=self.env,
                                text=True, capture_output=True, timeout=90)
        if check:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def options(self, branch, path=None):
        return SimpleNamespace(source=self.source, path=Path(path).resolve() if path else None,
                               branch=branch, base=self.base, skip_restore=True, exclude_path=[])

    def absent_root_cleanup_entrances(self, native_failure):
        self.prepare_make()
        for entrance in ("worktree-remove", "clean-lanes"):
            with self.subTest(entrance=entrance):
                tree = self.root / ("absent-" + entrance)
                branch = "lane/governance/absent-" + entrance
                head = self.commit_branch(branch, tree, 7 * 3600)
                _, metadata = protocol.identity(self.main, tree)
                run(self.main, "worktree", "lock", tree)
                if native_failure:
                    import stat
                    os.chflags(metadata, stat.UF_IMMUTABLE)
                    try:
                        failed = preservation.remove(SimpleNamespace(source=self.main, names=tree.name,
                            path=[], preview=False, force=True))
                        self.assertEqual("failed", failed["status"], failed)
                        reason = failed["items"][0]["reason"]
                        self.assertIn("removal_final-native_failed:CalledProcessError", reason)
                        self.assertIn("Operation not permitted", reason)
                        self.assertIn("root=False, pointer=False, registered=True", reason)
                    finally:
                        os.chflags(metadata, 0)
                else:
                    # Portable equivalent of the native partial-effect state.
                    shutil.rmtree(tree)
                self.assertFalse(os.path.lexists(tree))
                current = next(row for row in protocol.inventory(self.main)
                               if Path(row["worktree"]) == tree)
                self.assertIn("locked", current)
                with self.assertRaises(protocol.Refused):
                    protocol.identity(self.main, tree)
                with self.assertRaises(protocol.Refused):
                    pool.claim(self.options("lane/governance/strict-reuse", tree))
                recent = self.root / ("recent-" + entrance)
                self.commit_branch("lane/governance/recent-" + entrance, recent, 60)
                recent_pointer = (recent / ".git").read_bytes()
                if not native_failure:
                    preview = preservation.remove(SimpleNamespace(source=self.main, names=tree.name,
                        path=[], preview=True, force=True))
                    self.assertEqual("would_remove", preview["items"][0]["outcome"], preview)
                    self.assertFalse(os.path.lexists(tree), "preview must not recreate the root")
                    self.assertTrue(metadata.is_dir())
                if entrance == "worktree-remove":
                    result = self.make(entrance, "NAMES=" + tree.name, "FORCE=1", check=False)
                else:
                    result = self.make("-C", "tools", entrance, "FORCE=1", "BASE=" + self.base,
                                       check=False)
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertFalse(os.path.lexists(tree))
                self.assertFalse(metadata.exists())
                self.assertFalse(any(Path(row["worktree"]) == tree for row in protocol.inventory(self.main)))
                self.assertEqual(head, run(self.main, "rev-parse", branch).stdout.strip())
                self.assertEqual(recent_pointer, (recent / ".git").read_bytes())
                self.assertEqual("dev", run(self.main, "branch", "--show-current").stdout.strip())

    def test_absent_root_locked_registration_supported_cleanup_and_preview(self):
        self.absent_root_cleanup_entrances(native_failure=False)

    @unittest.skipUnless(hasattr(os, "chflags"), "requires native immutable flags")
    def test_actual_absent_root_native_partial_failure_supported_retry(self):
        self.absent_root_cleanup_entrances(native_failure=True)

    def test_absent_root_recovery_preserves_registration_boundaries(self):
        for boundary in ("unregistered", "backlink", "alias", "nested", "metadata-link"):
            with self.subTest(boundary=boundary):
                tree = self.root / boundary
                branch = "lane/governance/" + boundary
                head = self.commit_branch(branch, tree, 7 * 3600)
                _, metadata = protocol.identity(self.main, tree)
                shutil.rmtree(tree)
                requested = tree
                if boundary == "unregistered":
                    run(self.main, "worktree", "remove", "--force", "--force", tree)
                elif boundary == "backlink":
                    (metadata / "gitdir").write_text(str(self.root / "foreign/.git") + "\n")
                elif boundary == "alias":
                    requested = self.root / "dangling-alias"
                    requested.symlink_to(tree, target_is_directory=True)
                elif boundary == "nested":
                    tree.mkdir()
                    run(self.main, "worktree", "add", "-b", "nested", tree / "nested")
                    shutil.rmtree(tree)
                else:
                    saved = self.root / "saved-administration"
                    metadata.rename(saved)
                    metadata.symlink_to(saved, target_is_directory=True)
                with self.assertRaises(protocol.Refused):
                    preservation.remove_registered(self.main, requested)
                self.assertFalse(os.path.lexists(tree), "refusal must not recreate the root")
                if boundary != "unregistered":
                    self.assertTrue(metadata.exists())
                self.assertEqual(head, run(self.main, "rev-parse", branch).stdout.strip())
        arbitrary = self.root / "unregistered-directory"
        arbitrary.mkdir()
        (arbitrary / "keep").write_text("personal bytes")
        for path in (self.main, arbitrary):
            with self.assertRaises(protocol.Refused):
                preservation.remove_registered(self.main, path)
        self.assertEqual("personal bytes", (arbitrary / "keep").read_text())
        self.assertEqual("dev", run(self.main, "branch", "--show-current").stdout.strip())

    def test_automatic_allocation_preserves_registration_and_ignored_cache(self):
        tree = self.root / "selected five-hour tree"
        head = self.commit_branch("lane/governance/selected", tree, 5 * 3600)
        metadata = protocol.identity(self.main, tree)[1]
        (protocol.common(self.main) / "info/exclude").write_text(".lake/\n")
        (tree / ".lake").mkdir()
        (tree / ".lake/cache").write_text("retained cache")
        pointer = (tree / ".git").read_bytes()
        with patch.object(preservation, "_remove_payload", side_effect=AssertionError("creation deleted payload")):
            result = pool.claim(self.options("lane/governance/new-auto"))
        self.assertEqual("claimed", result["status"])
        self.assertEqual([], result["removed_worktrees"])
        self.assertEqual(pointer, (tree / ".git").read_bytes())
        self.assertEqual("retained cache", (tree / ".lake/cache").read_text())
        self.assertEqual(head, run(self.main, "rev-parse", "lane/governance/selected").stdout.strip())

    @unittest.skipUnless(hasattr(os, "chflags"), "requires native immutable flags")
    def test_actual_default_allocation_leaves_dirty_candidate_for_maintenance(self):
        import stat
        self.prepare_make()
        tree = self.root / "dirty candidate"
        branch = "lane/governance/dirty-candidate"
        head = self.commit_branch(branch, tree, 5 * 3600)
        blocked = tree / "blocked"
        blocked.write_text("retained on allocation")
        os.chflags(blocked, stat.UF_IMMUTABLE)
        try:
            result = self.make("worktree", "KIND=governance", "NAME=fresh-dirty", "BASE=" + self.base)
            self.assertEqual("succeeded", json.loads(result.stdout.splitlines()[-1])["status"])
            self.assertTrue(blocked.exists())
            self.assertEqual(head, run(tree, "rev-parse", "HEAD").stdout.strip())
        finally:
            os.chflags(blocked, 0)

    def test_missing_pointer_locked_registration_supported_cleanup_entrances(self):
        self.prepare_make()
        # Control only the unrelated artifact activity inventory. Make, the host
        # cleanup owner and native registered-tree removal still execute normally.
        python = self.bin / "python3"
        python.write_text(f'''#!{sys.executable}
import importlib.util, os, sys
arguments = sys.argv[1:]
if arguments[:1] == ["-B"]:
    arguments.pop(0)
if arguments[:1] != [{str(self.main / "tools/scripts/host-cleanup.py")!r}]:
    os.execv({sys.executable!r}, [{sys.executable!r}, *sys.argv[1:]])
sys.path.insert(0, os.path.dirname(arguments[0]))
spec = importlib.util.spec_from_file_location("cleanup", arguments[0])
cleanup = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cleanup)
cleanup.active_paths = lambda *args, **kwargs: set()
raise SystemExit(cleanup.main(arguments[1:]))
''')
        python.chmod(0o700)
        for entrance in ("clean-all", "clean-lanes", "worktree-remove"):
            with self.subTest(entrance=entrance):
                tree = self.root / ("missing-" + entrance)
                branch = "lane/governance/" + entrance
                head = self.commit_branch(branch, tree, 7 * 3600)
                run(self.main, "worktree", "lock", tree, "--reason", "ordinary native lock")
                (tree / ".git").unlink()
                recent = self.root / ("recent-" + entrance)
                self.commit_branch("lane/governance/recent-" + entrance, recent, 60)
                if entrance == "worktree-remove":
                    result = self.make(entrance, "NAMES=" + tree.name, "FORCE=1", check=False)
                else:
                    result = self.make("-C", "tools", entrance, "FORCE=1", "BASE=" + self.base,
                                       "CLEAN_TMP_ROOT=" + str(self.root / "artifacts"), check=False)
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertFalse(tree.exists(), result.stdout)
                self.assertFalse(any(Path(row["worktree"]) == tree for row in protocol.inventory(self.main)))
                self.assertEqual(head, run(self.main, "rev-parse", branch).stdout.strip())
                self.assertTrue((recent / ".git").exists())
                self.assertEqual("dev", run(self.main, "branch", "--show-current").stdout.strip())

    def test_missing_pointer_recovery_rejects_foreign_backlink_alias_and_nested_registration(self):
        for boundary in ("foreign", "bare", "backlink", "alias", "nested"):
            with self.subTest(boundary=boundary):
                tree = self.root / boundary
                self.commit_branch("lane/governance/" + boundary, tree, 7 * 3600)
                _, metadata = protocol.identity(self.main, tree)
                (tree / ".git").unlink()
                requested = tree
                if boundary == "foreign":
                    run(tree, "init", "--initial-branch=foreign")
                elif boundary == "bare":
                    run(self.main, "init", "--bare", tree)
                elif boundary == "backlink":
                    (metadata / "gitdir").write_text(str(self.root / "foreign/.git") + "\n")
                elif boundary == "alias":
                    requested = self.root / "alias-link"
                    requested.symlink_to(tree, target_is_directory=True)
                else:
                    run(self.main, "worktree", "add", "-b", "nested", tree / "nested")
                with self.assertRaises(protocol.Refused):
                    preservation.remove_registered(self.main, requested)
                self.assertTrue((tree / "payload").exists())

    def test_missing_pointer_cleanup_is_preview_only_then_native_retry(self):
        tree, sibling = self.root / "missing", self.root / "other"
        head = self.commit_branch("lane/governance/missing", tree, 7 * 3600)
        self.commit_branch("lane/governance/other", sibling, 60)
        sibling_pointer = (sibling / ".git").read_bytes()
        run(self.main, "worktree", "lock", tree)
        (tree / ".git").unlink()
        with self.assertRaises(protocol.Refused):
            protocol.identity(self.main, tree)
        options = SimpleNamespace(source=self.main, names="", path=[tree], preview=True, force=True)
        result = preservation.remove(options)
        self.assertEqual("would_remove", result["items"][0]["outcome"])
        self.assertFalse((tree / ".git").exists(), "preview must not repair")
        options.preview = False
        failure = subprocess.CalledProcessError(1, ["rm"], stderr=b"retryable payload error")
        with patch.object(preservation, "_remove_payload", side_effect=failure):
            result = preservation.remove(options)
        self.assertEqual("failed", result["status"], result)
        self.assertIn("pointer=True, registered=True", result["items"][0]["reason"])
        protocol.identity(self.main, tree)
        self.assertEqual("succeeded", preservation.remove(options)["status"])
        self.assertFalse(tree.exists())
        self.assertEqual(sibling_pointer, (sibling / ".git").read_bytes())
        self.assertEqual(head, run(self.main, "rev-parse", "lane/governance/missing").stdout.strip())

    def test_removal_deadline_matches_force_and_allocation_contract_without_waiting(self):
        for mode in ("normal", "force", "sweep"):
            with self.subTest(mode=mode):
                tree = self.root / ("deadline-" + mode)
                self.commit_branch("lane/governance/old-" + mode, tree, 7 * 3600)
                native, observed = subprocess.run, []
                def elapsed(command, *args, **kwargs):
                    if command[0] == "/bin/rm" or "remove" in command and "worktree" in command:
                        timeout = kwargs.get("timeout")
                        observed.append(timeout)
                        # Model 301 seconds of deletion without waiting. A hidden
                        # 300s deadline fails exactly as the production subprocess.
                        if timeout is not None and timeout <= 301:
                            raise subprocess.TimeoutExpired(command, timeout)
                    return native(command, *args, **kwargs)
                with patch.object(preservation.subprocess, "run", side_effect=elapsed):
                    if mode == "sweep":
                        result = pool.sweep(self.main, self.base, force=True)
                    else:
                        result = preservation.remove(SimpleNamespace(source=self.main, names="", path=[tree],
                            preview=False, force=mode == "force"))
                self.assertNotEqual("failed", result.get("status"), result)
                self.assertTrue(observed)
                if mode == "normal":
                    self.assertTrue(all(301 < value <= 1800 for value in observed), observed)
                else:
                    self.assertEqual([None] * len(observed), observed)

    def test_partial_payload_failure_retains_notification_for_maintenance_retry(self):
        for fault in ("error", "timeout", "interrupt"):
            with self.subTest(fault=fault):
                tree = self.root / ("expired " + fault)
                branch = "lane/governance/old-" + fault
                head = self.commit_branch(branch, tree, 7 * 3600)
                maintenance.notify(self.main)
                original = subprocess.run
                def partial(command, *args, **kwargs):
                    if command[0] != "/bin/rm":
                        return original(command, *args, **kwargs)
                    original(["/bin/rm", "-f", "--", "./payload"], cwd=tree, check=True)
                    if fault == "interrupt":
                        raise KeyboardInterrupt()
                    if fault == "timeout":
                        raise subprocess.TimeoutExpired(command, kwargs["timeout"], stderr=b"partial timeout diagnostic")
                    raise subprocess.CalledProcessError(1, command, stderr=b"partial payload diagnostic")
                with patch.object(preservation.subprocess, "run", side_effect=partial):
                    result = maintenance.run(self.main)
                self.assertEqual("failed", result["status"])
                self.assertIn("removal_payload_failed:", str(result))
                self.assertTrue(list((maintenance.directory(self.main) / "requests").iterdir()))
                protocol.identity(self.main, tree)
                result = maintenance.run(self.main)
                self.assertEqual("succeeded", result["status"])
                self.assertFalse(tree.exists())
                self.assertEqual(head, run(self.main, "rev-parse", branch).stdout.strip())

    @unittest.skipUnless(hasattr(os, "chflags"), "requires native immutable flags")
    def test_actual_payload_error_and_retry(self):
        import stat
        tree = self.root / "expired immutable payload"
        branch = "lane/governance/immutable-payload"
        head = self.commit_branch(branch, tree, 7 * 3600)
        blocked = tree / "blocked"
        blocked.write_text("retained on failure")
        os.chflags(blocked, stat.UF_IMMUTABLE)
        try:
            failed = pool.sweep(self.main, self.base, force=True)
            self.assertEqual(failed["status"], "failed")
            self.assertIn("removal_payload_failed:CalledProcessError", failed["items"][0]["reason"])
            self.assertIn("Operation not permitted", failed["items"][0]["reason"])
            self.assertFalse((tree / "payload").exists())
            protocol.identity(self.main, tree)
        finally:
            os.chflags(blocked, 0)
        result = pool.sweep(self.main, self.base, force=True)
        self.assertEqual(result["status"], "succeeded")
        self.assertFalse(tree.exists())
        self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)

    @unittest.skipUnless(hasattr(os, "chflags"), "requires native immutable flags")
    def test_actual_final_native_failure_reports_observed_effects_without_orphan_retry(self):
        import stat
        tree = self.root / "immutable pointer"
        branch = "lane/governance/immutable-pointer"
        head = self.commit_branch(branch, tree, 7 * 3600)
        pointer = tree / ".git"
        os.chflags(pointer, stat.UF_IMMUTABLE)
        try:
            result = preservation.remove(SimpleNamespace(source=self.main, names="", path=[tree], preview=False))
            self.assertEqual(result["status"], "failed", result)
            reason = result["items"][0]["reason"]
            self.assertIn("removal_final-native_failed:CalledProcessError", reason)
            self.assertIn("Operation not permitted", reason)
            self.assertIn("pointer=True, registered=False", reason)
            self.assertEqual(list(tree.iterdir()), [pointer])
            with self.assertRaises(protocol.Refused):
                preservation.remove_registered(self.main, tree)
            self.assertTrue(pointer.exists())
            self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)
        finally:
            os.chflags(pointer, 0)

    def test_payload_symlinks_dotfiles_batching_and_containment(self):
        tree = self.root / "payload links"
        branch = "lane/governance/links"
        head = self.commit_branch(branch, tree, 7 * 3600)
        outside = self.root / "outside"
        outside.mkdir()
        sentinel = outside / "keep"
        sentinel.write_text("external bytes")
        (tree / ".lake").symlink_to(outside, target_is_directory=True)
        (tree / ".hidden").write_text("remove")
        # More than one argv batch, including shell metacharacters and options.
        for index in range(400):
            (tree / (f"-- {index:04}-" + "x" * 100)).write_bytes(b"")
        alias = self.root / "alias"
        alias.symlink_to(tree, target_is_directory=True)
        with self.assertRaisesRegex(protocol.Refused, "missing_or_linked_tree"):
            preservation.remove_registered(self.main, alias)
        nested = tree / "nested"
        self.commit_branch("lane/governance/nested", nested, 60)
        with self.assertRaisesRegex(protocol.Refused, "nested_worktree"):
            preservation.remove_registered(self.main, tree)
        preservation.remove_registered(self.main, nested)
        preservation.remove_registered(self.main, tree)
        self.assertFalse(tree.exists())
        self.assertEqual(sentinel.read_text(), "external bytes")
        self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)

    def test_removal_shares_normal_deadline_and_exposes_timeout_stderr(self):
        tree = self.root / "deadline"
        self.commit_branch("lane/governance/deadline", tree, 7 * 3600)
        original = subprocess.run
        budgets = []
        def final_timeout(command, *args, **kwargs):
            if command[0] == "/bin/rm":
                budgets.append(kwargs["timeout"])
            if "remove" in command and "worktree" in command:
                budgets.append(kwargs["timeout"])
                raise subprocess.TimeoutExpired(command, kwargs["timeout"], stderr=b"native timeout diagnostic")
            return original(command, *args, **kwargs)
        with patch.object(preservation.subprocess, "run", side_effect=final_timeout), \
                patch.object(preservation, "time", SimpleNamespace(monotonic=iter([0, 10, 40]).__next__)):
            with self.assertRaisesRegex(protocol.GitFailure, "final-native.*native timeout diagnostic"):
                preservation.remove_registered(self.main, tree)
        self.assertEqual(budgets, [1790, 1760])
        protocol.identity(self.main, tree)
        preservation.remove_registered(self.main, tree)

    def test_make_explicit_removal_uses_shared_payload_owner(self):
        self.prepare_make()
        tree = self.root / "explicit-removal"
        branch = "lane/governance/explicit-removal"
        head = self.commit_branch(branch, tree, 60)
        outside = self.root / "external-cache"
        outside.mkdir()
        sentinel = outside / "keep"
        sentinel.write_text("external bytes")
        (tree / ".lake").symlink_to(outside, target_is_directory=True)
        result = self.make("worktree-remove", "NAMES=" + tree.name)
        self.assertIn("WORKTREE_REMOVE_RESULT exit=0 removed=1 failed=0", result.stdout)
        self.assertFalse(tree.exists())
        self.assertFalse(any(Path(row["worktree"]) == tree for row in protocol.inventory(self.main)))
        self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)
        self.assertEqual(sentinel.read_text(), "external bytes")

    def test_explicit_batch_can_remove_its_invoking_source_first(self):
        first, second = self.root / "a-invoking", self.root / "z-second"
        retained = {name: self.commit_branch(name, path, 60) for name, path in
                    (("lane/governance/first", first), ("lane/governance/second", second))}
        result = preservation.remove(SimpleNamespace(source=first, names="", path=[first, second], preview=False))
        self.assertEqual(result["status"], "succeeded", result)
        self.assertFalse(first.exists())
        self.assertFalse(second.exists())
        for branch, head in retained.items():
            self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)

    def test_stale_reuse_is_immediate_and_new_commit_invalidates(self):
        candidate = self.root / "candidate"
        old_branch = "lane/governance/old"
        head = self.commit_branch(old_branch, candidate, 60)
        marked = protocol.mark_stale(self.source, candidate)
        self.assertEqual(marked["head"], head)
        result = pool.claim(self.options("lane/governance/new"))
        self.assertEqual(result["status"], "claimed", result)
        current = next(row for row in protocol.inventory(self.source)
                       if Path(row["worktree"]).resolve() == candidate.resolve())
        self.assertEqual(current["branch"], "refs/heads/lane/governance/new")
        self.assertEqual(run(self.source, "show-ref", "--verify", "refs/heads/" + old_branch).returncode, 0)

        fresh = self.root / "fresh"
        self.commit_branch("lane/governance/fresh", fresh, 0)
        protocol.mark_stale(self.source, fresh)
        run(fresh, "commit", "--allow-empty", "-m", "new")
        reusable, reason = protocol.reusable(fresh, self.source)
        self.assertFalse(reusable)
        self.assertEqual(reason, "head_recent")

    def test_age_reuse_ignores_legacy_lock_and_live_process(self):
        candidate = self.root / "busy"
        old_branch = "lane/governance/busy"
        self.commit_branch(old_branch, candidate, 5 * 60 * 60)
        metadata = Path(run(candidate, "rev-parse", "--git-dir").stdout.strip())
        (metadata / "locked").write_text("legacy marker\n")
        holder = subprocess.Popen(
            [sys.executable, "-c", "import os,time; os.chdir(os.environ['TREE']); open(os.path.join(os.environ['TREE'],'payload'),'ab').close(); time.sleep(30)"],
            env={**os.environ, "TREE": str(candidate)})
        try:
            result = self.create("reused", candidate)
            self.assertEqual(json.loads(result.stdout)["status"], "claimed", result.stdout)
        finally:
            holder.terminate()
            holder.wait(timeout=10)

    def test_strict_boundaries_future_unknown_main_and_direct_removal(self):
        exact4 = self.root / "exact4"
        self.commit_branch("lane/governance/exact4", exact4, 4 * 60 * 60)
        head_time = protocol.head_committer_time(exact4)
        self.assertFalse(protocol.reusable(exact4, self.source, head_time + 4 * 60 * 60)[0])
        self.assertTrue(protocol.reusable(exact4, self.source, head_time + 4 * 60 * 60 + 1)[0])
        self.assertFalse(protocol.reusable(exact4, self.source, head_time - 1)[0])

        old = self.root / "old"
        old_branch = "lane/governance/old-dirty"
        head = self.commit_branch(old_branch, old, 7 * 60 * 60)
        (old / "unfinished").write_text("dirty\n")
        metadata = Path(run(old, "rev-parse", "--git-dir").stdout.strip())
        (metadata / "MERGE_HEAD").write_text(head + "\n")
        result = pool.sweep(self.source, self.base, force=True)
        self.assertTrue(any(row["path"] == str(old.resolve()) and row["outcome"] == "removed" for row in result["items"]))
        self.assertFalse(any(Path(row["worktree"]).resolve() == old.resolve()
                             for row in protocol.inventory(self.source)))
        self.assertEqual(run(self.source, "show-ref", "--verify", "refs/heads/" + old_branch).returncode, 0)
        with self.assertRaises(protocol.Refused):
            protocol.mark_stale(self.source, self.source)

        original = protocol.head_committer_time
        try:
            protocol.head_committer_time = lambda _: (_ for _ in ()).throw(protocol.Refused("head_timestamp_unknown"))
            with self.assertRaises(protocol.Refused):
                protocol.reusable(exact4, self.source)
        finally:
            protocol.head_committer_time = original

    def test_make_default_release_marks_current_branch_with_executable_path_intact(self):
        self.prepare_make()
        tree = self.root / "finished task"
        branch = "lane/governance/finished"
        head = self.commit_branch(branch, tree, 60)
        (tree / "ordinary-untracked").write_text("keep until reassignment")
        for target in ("worktree-stale", "worktree-return"):
            with self.subTest(target=target):
                self.make(target, cwd=tree)
                self.assertEqual(protocol.stale_head(self.main, "refs/heads/" + branch), head)
                run(self.main, "config", "--unset-all", protocol.branch_config_key("refs/heads/" + branch))
        self.make("worktree-stale", "WORKTREE_PATH=" + str(tree))
        self.assertEqual(protocol.stale_head(self.main, "refs/heads/" + branch), head)
        self.assertTrue((tree / "ordinary-untracked").exists())
        self.assertNotEqual(self.make("worktree-stale", check=False).returncode, 0)
        self.assertEqual(run(self.main, "branch", "--show-current").stdout.strip(), "dev")

    def test_make_custom_attached_task_resumes_immediately_without_destination(self):
        self.prepare_make()
        tree = self.root / "custom session"
        self.make("worktree", "KIND=governance", "NAME=resume", "BASE=" + self.base,
                  "DEST=" + str(tree), "ALLOW_LOW_DISK=1")
        (tree / "lean-toolchain").write_text((self.main / "lean-toolchain").read_text())
        # Ordinary tracked/untracked bytes do not participate in lifecycle eligibility.
        (tree / "tools/Fixture.csproj").write_text("tracked edit\n")
        (tree / "untracked").write_text("untracked bytes\n")
        resumed = self.make("worktree", "KIND=governance", "NAME=resume", "BASE=" + self.base,
                            "ALLOW_LOW_DISK=1")
        self.assertIn('"status": "reused"', resumed.stdout)
        self.assertIn(str(tree), resumed.stdout)
        self.assertEqual((tree / "tools/Fixture.csproj").read_text(), "tracked edit\n")
        self.assertEqual((tree / "untracked").read_text(), "untracked bytes\n")

    def test_make_explicit_reassignment_uses_stale_or_age_and_preserves_branch_refs(self):
        self.prepare_make()
        for reason, age in (("stale", -3600), ("age", 5 * 3600)):
            with self.subTest(reason=reason):
                tree = self.root / ("explicit " + reason)
                branch = "lane/governance/old-" + reason
                head = self.commit_branch(branch, tree, age)
                if reason == "stale":
                    self.make("worktree-return", cwd=tree)
                result = self.make("worktree", "KIND=governance", "NAME=new-" + reason,
                                   "DEST=" + str(tree), "BASE=" + self.base, "ALLOW_LOW_DISK=1", cwd=tree)
                self.assertIn('"status": "claimed"', result.stdout)
                self.assertEqual(run(tree, "branch", "--show-current").stdout.strip(),
                                 "lane/governance/new-" + reason)
                self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)

    def test_cli_notifies_without_expiring_inventory_before_selection_or_continuation(self):
        for continuation, reuse_any in ((a, b) for a in (False, True) for b in (False, True)):
            with self.subTest(continuation=continuation, reuse_any=reuse_any):
                name = f"task-{continuation}-{reuse_any}"
                eligible = self.root / ("eligible-" + name)
                expired = self.root / ("expired-" + name)
                branch = "lane/governance/" + (name if continuation else "old-" + name)
                self.commit_branch(branch, eligible, 60 if continuation else 5 * 3600)
                if continuation:
                    (eligible / "payload").write_text("ordinary tracked bytes")
                    (eligible / "untracked").write_text("ordinary untracked bytes")
                old_branch = "lane/governance/expired-" + name
                head = self.commit_branch(old_branch, expired, 7 * 3600)
                (expired / "payload").write_text("dirty")
                result = self.create(name, eligible, reuse_any=reuse_any)
                receipt = json.loads(result.stdout)
                self.assertEqual([], receipt["removed_worktrees"])
                self.assertEqual("queued", receipt["maintenance"]["status"])
                self.assertTrue(expired.exists())
                self.assertEqual("dirty", (expired / "payload").read_text())
                self.assertEqual(head, run(self.main, "rev-parse", old_branch).stdout.strip())
                if continuation:
                    self.assertEqual("ordinary tracked bytes", (eligible / "payload").read_text())
                    self.assertEqual("ordinary untracked bytes", (eligible / "untracked").read_text())
                run(self.main, "worktree", "remove", "--force", eligible)
                run(self.main, "worktree", "remove", "--force", expired)

    def test_make_and_cli_expire_inventory_before_fresh_explicit_destination(self):
        self.prepare_make()
        eligible = self.root / "b-eligible"
        eligible_head = self.commit_branch("lane/governance/eligible", eligible, 5 * 3600)
        for entrance in ("cli", "make"):
            with self.subTest(entrance=entrance):
                expired = []
                for prefix in ("a", "z"):
                    branch = f"lane/governance/expired-{prefix}-{entrance}"
                    path = self.root / f"{prefix}-expired-{entrance}"
                    head = self.commit_branch(branch, path, 7 * 3600)
                    (path / "payload").write_text("dirty")
                    (path / "untracked").write_text("discard")
                    expired.append((path, branch, head))
                destination = self.root / ("fresh explicit " + entrance)
                name = "fresh-" + entrance
                result = (self.create(name, destination) if entrance == "cli" else
                          self.make("worktree", "KIND=theory", "NAME=" + name,
                                    "DEST=" + str(destination), "BASE=" + self.base, "ALLOW_LOW_DISK=1"))
                self.assertIn('"status":"succeeded"', result.stdout)
                for path, branch, head in expired:
                    self.assertTrue(path.exists(), result.stdout)
                    self.assertEqual("queued", json.loads(result.stdout.splitlines()[-1])["maintenance"]["status"])
                    self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)
                self.assertEqual(run(destination, "rev-parse", "HEAD").stdout.strip(), self.base)
                self.assertEqual(run(eligible, "rev-parse", "HEAD").stdout.strip(), eligible_head)
                self.assertEqual(run(self.main, "branch", "--show-current").stdout.strip(), "dev")

    def test_make_and_cli_fresh_fallback_survives_expired_invoking_source(self):
        self.prepare_make()
        for entrance in ("cli", "make"):
            with self.subTest(entrance=entrance):
                invoking = self.root / ("expired invoking " + entrance)
                branch = "lane/governance/invoking-" + entrance
                head = self.commit_branch(branch, invoking, 7 * 3600)
                (invoking / "untracked").write_text("discard")
                destination = self.root / ("fresh fallback " + entrance)
                name = "fallback-" + entrance
                result = (self.cli("worktree", "--kind", "math", "--name", name,
                                   "--path", destination, "--base", "HEAD", "--skip-restore", cwd=invoking)
                          if entrance == "cli" else
                          self.make("worktree", "KIND=math", "NAME=" + name, "DEST=" + str(destination),
                                    "BASE=HEAD", "ALLOW_LOW_DISK=1", cwd=invoking))
                self.assertIn('"status":"succeeded"', result.stdout)
                self.assertTrue(invoking.exists())
                self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)
                self.assertEqual(run(destination, "rev-parse", "HEAD").stdout.strip(), head)
                self.assertEqual(run(self.main, "branch", "--show-current").stdout.strip(), "dev")

    def test_make_default_fresh_fallback_retains_recent_candidate(self):
        self.prepare_make()
        recent = self.root / "recent"
        head = self.commit_branch("lane/governance/recent", recent, 60)
        (recent / "untracked").write_text("ordinary bytes")
        result = self.make("worktree", "KIND=governance", "NAME=default-fallback",
                           "BASE=" + self.base, "ALLOW_LOW_DISK=1")
        self.assertIn('"status":"succeeded"', result.stdout)
        destination = self.root / "trureturing-default-fallback"
        self.assertEqual(run(destination, "rev-parse", "HEAD").stdout.strip(), self.base)
        self.assertEqual(run(recent, "rev-parse", "HEAD").stdout.strip(), head)
        self.assertEqual((recent / "untracked").read_text(), "ordinary bytes")

    def test_cli_fresh_fallback_refusals_report_completed_expiry(self):
        self.prepare_make()
        python = self.bin / "python3"
        python.write_text('#!/bin/bash\nfor arg in "$@"; do\n'
            '  if [[ "$arg" == check-disk ]]; then\n'
            '    echo "injected disk refusal" >&2\n    exit 78\n  fi\ndone\n'
            'exec "$EXPIRY_TEST_PYTHON" "$@"\n')
        python.chmod(0o755)
        for reason in ("branch", "disk"):
            with self.subTest(reason=reason):
                expired = self.root / ("expired before " + reason)
                old_branch = "lane/governance/expired-before-" + reason
                head = self.commit_branch(old_branch, expired, 7 * 3600)
                name = "refused-" + reason
                if reason == "branch":
                    run(self.main, "branch", "lane/governance/" + name, self.base)
                destination = self.root / ("refused " + reason)
                env = None if reason == "branch" else {
                    "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
                    "FRONTDOOR_DOTNET": self.env["FRONTDOOR_DOTNET"],
                    "EXPIRY_TEST_PYTHON": shutil.which("python3"), "WORKTREE_REQUIRE_DISK_CHECK": "1"}
                failed = self.cli("worktree", "--kind", "governance", "--name", name,
                                  "--path", destination, "--base", self.base, "--skip-restore",
                                  check=False, env=env)
                self.assertEqual(failed.returncode, 78 if reason == "disk" else 2,
                                 failed.stdout + failed.stderr)
                self.assertIn("injected disk refusal" if reason == "disk" else "branch already exists",
                              failed.stderr)
                self.assertTrue(expired.exists())
                self.assertFalse(destination.exists())
                self.assertEqual(run(self.main, "rev-parse", old_branch).stdout.strip(), head)

    def test_make_fresh_creation_survives_background_expiry_failure(self):
        self.prepare_make()
        tree = self.root / "expired blocked"
        branch = "lane/governance/blocked"
        head = self.commit_branch(branch, tree, 7 * 3600)
        with patch.object(pool, "_remove_registered", side_effect=protocol.GitFailure("native removal failed")):
            maintenance.notify(self.main)
            result = maintenance.run(self.main)
        self.assertEqual("failed", result["status"])
        destination = self.root / "fresh allowed"
        result = self.make("worktree", "KIND=governance", "NAME=allowed", "DEST=" + str(destination),
                           "BASE=" + self.base, "ALLOW_LOW_DISK=1")
        self.assertTrue(destination.exists())
        self.assertTrue(tree.exists())
        self.assertEqual(head, run(self.main, "rev-parse", branch).stdout.strip())
        self.assertEqual("dev", run(self.main, "branch", "--show-current").stdout.strip())

    def test_cli_expired_same_task_is_retained_until_background_maintenance(self):
        tree = self.root / "expired same task"
        branch = "lane/governance/expired-task"
        head = self.commit_branch(branch, tree, 7 * 3600)
        (tree / "payload").write_text("ordinary tracked edit")
        (tree / "untracked").write_text("ordinary untracked bytes")
        for reuse_any in (False, True):
            failed = self.create("expired-task", tree, reuse_any=reuse_any, check=False, cwd=tree)
            self.assertNotEqual(0, failed.returncode)
            self.assertIn("expired_maintenance_pending", failed.stderr)
        self.assertTrue(tree.exists())
        self.assertEqual(head, run(self.main, "rev-parse", branch).stdout.strip())
        self.assertEqual("succeeded", maintenance.run(self.main)["status"])
        self.assertFalse(tree.exists())

    def test_cli_same_task_still_checks_base_and_pins(self):
        tree = self.root / "same task"
        self.commit_branch("lane/governance/same", tree, 60)
        (tree / "lean-toolchain").write_text("incompatible pin\n")
        failed = self.create("same", self.root / "unused", reuse_any=True, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("incompatible_pin", failed.stderr)
        self.assertEqual((tree / "lean-toolchain").read_text(), "incompatible pin\n")
        (tree / "lean-toolchain").write_bytes((self.main / "lean-toolchain").read_bytes())
        (self.main / "new-base").write_text("different ancestry")
        run(self.main, "add", ".")
        run(self.main, "commit", "-m", "new base")
        self.base = run(self.main, "rev-parse", "HEAD").stdout.strip()
        failed = self.create("same", tree, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("incompatible_base", failed.stderr)

    def test_cli_continuation_retains_downstream_pin_validation(self):
        (self.main / "Reg/lakefile.toml").unlink()
        run(self.main, "add", ".")
        run(self.main, "commit", "-m", "invalid fixture pin")
        self.base = run(self.main, "rev-parse", "HEAD").stdout.strip()
        tree = self.root / "malformed pin"
        self.commit_branch("lane/governance/malformed", tree, 60)
        failed = self.create("malformed", self.root / "unused", reuse_any=True, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("REG-MANIFEST-INVALID", failed.stderr)
        self.assertTrue((tree / "payload").exists())

    def test_make_clean_all_expires_trees_even_when_artifact_mutex_is_held(self):
        self.prepare_make()
        tree = self.root / "expired"
        branch = "lane/governance/expired"
        head = self.commit_branch(branch, tree, 7 * 3600)
        (tree / "payload").write_text("discard tracked bytes")
        (tree / "untracked").write_text("discard untracked bytes")
        lock_path = self.root / "tmp" / ("trureturing-clean-all-" + str(os.getuid()) + ".lock")
        with lock_path.open("w") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            result = self.make("-C", "tools", "clean-all", "FORCE=1", "BASE=" + self.base,
                               "CLEAN_TMP_ROOT=" + str(self.root / "artifacts"), check=False, cwd=tree)
        self.assertNotEqual(result.returncode, 0)  # Artifact owner retains its native refusal.
        self.assertIn("HOST_CLEANUP_FAILED", result.stderr)
        self.assertFalse(tree.exists(), result.stdout + result.stderr)
        self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)
        self.assertEqual(run(self.main, "branch", "--show-current").stdout.strip(), "dev")

    def test_explicit_cli_rejects_alias_foreign_and_main_without_reassignment(self):
        tree = self.root / "candidate"
        branch = "lane/governance/candidate"
        head = self.commit_branch(branch, tree, 5 * 3600)
        alias = self.root / "alias"
        alias.symlink_to(tree, target_is_directory=True)
        failed = self.create("new", alias, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("missing_or_linked_tree", failed.stderr)
        self.assertEqual(run(tree, "rev-parse", "HEAD").stdout.strip(), head)
        foreign = self.root / "foreign"
        run(self.root, "init", "--initial-branch=dev", foreign)
        failed = self.create("new", foreign, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("repository_identity", failed.stderr)
        failed = self.create("new", self.main, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("main_worktree", failed.stderr)
        self.assertEqual(run(self.main, "branch", "--show-current").stdout.strip(), "dev")

    def test_background_expiry_failure_reports_partial_effects_independently(self):
        good = self.root / "a-expired"
        blocked = self.root / "z-expired"
        for name, path in (("good", good), ("blocked", blocked)):
            self.commit_branch("lane/governance/" + name, path, 7 * 3600)
        remove = pool._remove_registered
        def native_failure(source, path):
            if path.resolve() == blocked.resolve():
                raise protocol.GitFailure("native removal error")
            return remove(source, path)
        maintenance.notify(self.main)
        with patch.object(pool, "_remove_registered", side_effect=native_failure):
            result = maintenance.run(self.main)
        self.assertEqual("failed", result["status"])
        self.assertIn("native removal error", str(result))
        self.assertFalse(good.exists())
        self.assertTrue(blocked.exists())
        self.assertEqual(0, result["requests_consumed"])

    def test_pool_exact_six_hour_boundary_and_future_stale(self):
        tree = self.root / "boundary"
        self.commit_branch("lane/governance/boundary", tree, 6 * 3600)
        stamp = protocol.head_committer_time(tree)
        with patch.object(pool.time, "time", return_value=stamp + 6 * 3600):
            result = pool.sweep(self.main, self.base, force=True)
            self.assertEqual(result["items"][0]["outcome"], "retained")
        with patch.object(pool.time, "time", return_value=stamp + 6 * 3600 + 1):
            result = pool.sweep(self.main, self.base, force=True)
            self.assertEqual(result["items"][0]["outcome"], "removed")
        future = self.root / "future"
        self.commit_branch("lane/governance/future", future, -3600)
        self.assertFalse(protocol.reusable(future, self.main)[0])
        protocol.mark_stale(self.main, future)
        self.assertTrue(protocol.reusable(future, self.main)[0])


    def test_notifications_during_sweep_and_failed_sweeps_are_not_lost(self):
        maintenance.notify(self.main)
        original = pool.sweep
        def arriving(*args, **kwargs):
            result = original(*args, **kwargs)
            maintenance.notify(self.main)
            return result
        with patch.object(pool, "sweep", side_effect=arriving):
            result = maintenance.run(self.main)
        self.assertEqual("succeeded", result["status"])
        requests = maintenance.directory(self.main) / "requests"
        self.assertEqual(1, len(list(requests.iterdir())))
        maintenance.run(self.main)
        self.assertEqual([], list(requests.iterdir()))

    def test_exclusive_worker_does_not_block_fresh_allocation_or_consume_events(self):
        maintenance.notify(self.main)
        script = ("import sys; sys.path.insert(0,sys.argv[1]); "
                  "from worktree_maintenance import lease; "
                  "ctx=lease(sys.argv[2]); ctx.__enter__(); "
                  "print('ready',flush=True); sys.stdin.read(); ctx.__exit__(None,None,None)")
        holder = subprocess.Popen([sys.executable, "-B", "-c", script,
            str(ROOT / "tools/scripts/worktree"), str(self.main)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        try:
            self.assertEqual("ready", holder.stdout.readline().strip())
            self.assertEqual("busy", maintenance.run(self.main)["status"])
            destination = self.root / "fresh during maintenance"
            result = self.create("while-busy", destination)
            self.assertEqual("succeeded", json.loads(result.stdout)["status"])
            self.assertTrue(destination.is_dir())
            self.assertTrue(list((maintenance.directory(self.main) / "requests").iterdir()))
        finally:
            holder.communicate(timeout=10)
        self.assertEqual(0, holder.returncode)
        self.assertEqual("succeeded", maintenance.run(self.main)["status"])

    def test_claim_notification_cannot_preempt_same_task_reuse(self):
        tree = self.root / "attached"
        branch = "lane/governance/attached"
        self.commit_branch(branch, tree, 0)
        native_notify = maintenance.notify
        holders = []
        script = ("import sys; sys.path.insert(0,sys.argv[1]); "
                  "from worktree_maintenance import lease; "
                  "ctx=lease(sys.argv[2],blocking=False); ctx.__enter__(); "
                  "print('ready',flush=True); sys.stdin.read(); ctx.__exit__(None,None,None)")
        def notify_and_start_worker(source):
            notice = native_notify(source)
            holder = subprocess.Popen([sys.executable, "-B", "-c", script,
                str(ROOT / "tools/scripts/worktree"), str(source)],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
            holders.append(holder)
            self.assertEqual("ready", holder.stdout.readline().strip())
            return notice
        try:
            with patch.object(maintenance, "notify", side_effect=notify_and_start_worker):
                result = pool.claim(self.options(branch, tree))
            self.assertEqual("reused", result["status"])
            self.assertEqual("queued", result["maintenance"]["status"])
        finally:
            for holder in holders:
                holder.communicate(timeout=10)
                self.assertEqual(0, holder.returncode)

    def test_make_notifies_after_existing_destination_allocation(self):
        self.prepare_make()
        tree = self.root / "attached"
        self.commit_branch("lane/governance/attached", tree, 0)
        # Emulate a host worker that starts on any event queued before CLI entry.
        worker = self.root / "notified-worker.py"
        worker.write_text("import os, subprocess, sys\n"
            "sys.path.insert(0, " + repr(str(ROOT / "tools/scripts/worktree")) + ")\n"
            "from worktree_maintenance import directory, lease\n"
            "source = os.environ['NOTIFICATION_SOURCE']\n"
            "command = [os.environ['FRONTDOOR_DOTNET'], os.environ['FRONTDOOR_CLI'], *sys.argv[1:]]\n"
            "if list((directory(source) / 'requests').glob('*')):\n"
            "    with lease(source):\n"
            "        result = subprocess.run(command)\n"
            "else:\n"
            "    result = subprocess.run(command)\n"
            "raise SystemExit(result.returncode)\n")
        launcher = self.bin / "dotnet"
        launcher.write_text('#!/bin/bash\nif [[ "$1" == run ]]; then\n'
            '  while [[ $# -gt 0 && "$1" != -- ]]; do shift; done\n'
            '  [[ $# -gt 0 ]] || exit 64\n  shift\n'
            '  exec "$NOTIFICATION_PYTHON" -B "$NOTIFICATION_WORKER" "$@"\nfi\n'
            'exec "$FRONTDOOR_DOTNET" "$@"\n')
        self.env.update(NOTIFICATION_PYTHON=sys.executable,
                        NOTIFICATION_WORKER=str(worker), NOTIFICATION_SOURCE=str(self.main))
        result = self.make("worktree", "KIND=governance", "NAME=attached",
                           "DEST=" + str(tree), "BASE=" + self.base)
        self.assertEqual("reused", json.loads(result.stdout.splitlines()[-1])["status"])
        self.assertTrue(list((maintenance.directory(self.main) / "requests").iterdir()))

    def test_service_projection_and_host_units_use_common_directory_with_spaces(self):
        import plistlib
        home = self.root / "user home with spaces"
        native_run = subprocess.run
        def host_only(command, *args, **kwargs):
            if command[0] in ("launchctl", "systemctl"):
                return subprocess.CompletedProcess(command, 0)
            return native_run(command, *args, **kwargs)
        for platform in ("darwin", "linux"):
            with self.subTest(platform=platform), patch.object(maintenance.sys, "platform", platform), \
                    patch.object(maintenance.Path, "home", return_value=home), \
                    patch.object(maintenance.subprocess, "run", side_effect=host_only) as host:
                result = maintenance.install(self.main)
                self.assertEqual("installed", result["status"])
                self.assertTrue(host.called)
                root = maintenance.directory(self.main)
                runtime = root / "runtime/worktree_maintenance.py"
                self.assertTrue(runtime.is_file())
                if platform == "darwin":
                    config = plistlib.loads(Path(result["files"][0]).read_bytes())
                    self.assertEqual(str(runtime), config["ProgramArguments"][2])
                    self.assertEqual([str(root / "requests")], config["WatchPaths"])
                else:
                    self.assertIn("Type=oneshot", Path(result["files"][0]).read_text())
                    self.assertIn("PathChanged=" + str(root / "requests") + "\n",
                                  Path(result["files"][1]).read_text())
                    self.assertIn("OnUnitActiveSec=900", Path(result["files"][2]).read_text())
        result = subprocess.run([sys.executable, "-I", "-B", str(runtime),
            "--source", str(self.main), "status"], cwd=self.root, capture_output=True, text=True)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertIsNotNone(json.loads(result.stdout)["service"])
        result = subprocess.run([sys.executable, "-I", "-B", str(runtime),
            "--source", str(self.main), "run"], cwd=self.root, capture_output=True, text=True, timeout=10)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual("succeeded", json.loads(result.stdout)["status"])

    def test_unwritable_maintenance_storage_does_not_block_new_destination(self):
        root = maintenance.directory(self.main)
        root.chmod(0o500)
        try:
            destination = self.root / "without maintenance storage"
            result = self.create("storage-failure", destination)
            self.assertEqual("succeeded", json.loads(result.stdout)["status"])
            self.assertEqual("unavailable", json.loads(result.stdout)["maintenance"]["status"])
            self.assertTrue((destination / "lean-toolchain").is_file())
        finally:
            root.chmod(0o700)

    def test_default_selection_reuses_its_guarded_nominal_destination(self):
        tree = self.root / "nominal destination"
        self.commit_branch("lane/governance/previous-task", tree, 5 * 3600)
        result = self.create("next-task", tree, reuse_any=True)
        self.assertEqual("claimed", json.loads(result.stdout)["status"])
        result = self.create("next-task", tree, reuse_any=True)
        self.assertEqual("reused", json.loads(result.stdout)["status"])

    def test_concurrent_claims_cannot_reassign_one_selected_tree(self):
        tree = self.root / "shared candidate"
        self.commit_branch("lane/governance/candidate", tree, 5 * 3600)
        ready = self.root / "ready"
        script = '''import sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
import worktree_pool as pool
from types import SimpleNamespace
original = pool._allocate
def paused(*args):
    Path(sys.argv[4]).touch()
    sys.stdin.read()
    return original(*args)
pool._allocate = paused
options = SimpleNamespace(source=Path(sys.argv[2]), path=None, branch='lane/governance/first',
                          base=sys.argv[3], skip_restore=True, exclude_path=[])
assert pool.claim(options)['status'] == 'claimed'
'''
        holder = subprocess.Popen([sys.executable, "-B", "-c", script,
            str(ROOT / "tools/scripts/worktree"), str(self.main), self.base, str(ready)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 10
            while not ready.exists() and time.monotonic() < deadline:
                time.sleep(0.02)
            self.assertTrue(ready.exists())
            second = pool.claim(self.options("lane/governance/second"))
            self.assertEqual("no_reusable", second["status"])
        finally:
            output, error = holder.communicate(timeout=20)
        self.assertEqual(0, holder.returncode, output + error)
        self.assertEqual("lane/governance/first", run(tree, "branch", "--show-current").stdout.strip())

    def test_worker_skips_fresh_registration_until_initialization_exits(self):
        import shlex
        old = self.root / "old base"
        self.base = self.commit_branch("lane/governance/old-base", old, 7 * 3600)
        destination = self.root / "initializing old base"
        bin_dir = self.root / "pause-bin"
        bin_dir.mkdir()
        ready = self.root / "checkout ready"
        resume = self.root / "resume checkout"
        launcher = bin_dir / "git"
        launcher.write_text('#!/bin/bash\nif [[ "$1" == reset ]]; then\n'
            '  touch ' + shlex.quote(str(ready)) + '\n'
            '  while [[ ! -f ' + shlex.quote(str(resume)) + ' ]]; do sleep 0.02; done\nfi\n'
            'exec ' + shlex.quote(shutil.which("git")) + ' "$@"\n')
        launcher.chmod(0o755)
        caller = self.main / "caller"
        caller.mkdir()
        child = subprocess.Popen([shutil.which("dotnet"), str(ROOT /
            "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"), "worktree", "--kind", "governance",
            "--name", "initializing", "--path", os.path.relpath(destination, caller),
            "--source", "..", "--base", self.base, "--skip-restore"],
            cwd=caller, env=protocol.git_environment({"PATH": str(bin_dir) + os.pathsep + os.environ["PATH"]}),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 60
            while not ready.exists() and child.poll() is None and time.monotonic() < deadline:
                time.sleep(0.02)
            if not ready.exists():
                resume.touch()
                output, error = child.communicate(timeout=20)
                self.fail("checkout was not reached: " + output + error)
            result = maintenance.run(self.main)
            row = next(item for item in result["items"] if item["path"] == str(destination))
            self.assertEqual("initialization_in_progress", row["reason"])
            self.assertTrue((destination / ".git").is_file())
        finally:
            resume.touch()
            output, error = child.communicate(timeout=20)
        self.assertEqual(0, child.returncode, output + error)
        self.assertTrue((destination / "lean-toolchain").is_file())
        self.assertEqual("succeeded", maintenance.run(self.main)["status"])
        self.assertFalse(destination.exists())


if __name__ == "__main__":
    if sys.argv[1:] == ["--list-tests"]:
        print(json.dumps(["LifecycleTests." + name for name in
                          unittest.defaultTestLoader.getTestCaseNames(LifecycleTests)]))
    else:
        unittest.main(verbosity=2)

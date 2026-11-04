"""Recognized Lake Git shapes and refusal before any batch mutation."""

from pathlib import Path
import shutil
import subprocess
from unittest.mock import patch


class LakeDependencyAllowlistCases:
    def assert_lake_metadata_retained(self, relative, content, detail):
        boundary = self.clean_lake_clone(self.tree)
        entry = boundary / ".git" / relative
        entry.write_bytes(content)
        if relative == "hooks/pre-commit":
            entry.chmod(0o755)
        self.assert_lake_content_retained(
            boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:" + detail)
        self.assertEqual(content, entry.read_bytes())

    def test_lake_dependency_retains_custom_hook(self):
        self.assert_lake_metadata_retained(
            "hooks/pre-commit", b"#!/bin/sh\necho local-hook\n", "hooks_entry:pre-commit")

    def test_lake_dependency_retains_info_attributes(self):
        self.assert_lake_metadata_retained(
            "info/attributes", b"tracked -diff\n", "info_entry:attributes")

    def test_lake_dependency_retains_active_info_exclude(self):
        self.assert_lake_metadata_retained(
            "info/exclude", b"# local exclusion\nprivate-content\n", "info_exclude")

    def test_lake_dependency_retains_indented_exclude(self):
        boundary = self.clean_lake_clone(self.tree)
        pattern = " # private-content"
        exclude = boundary / ".git/info/exclude"
        exclude.write_text(pattern + "\n")
        self.assertEqual(pattern, self.g(boundary, "check-ignore", "--no-index", pattern).strip("\n"))
        self.assert_lake_content_retained(
            boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:info_exclude")
        self.assertEqual(pattern + "\n", exclude.read_text())

    def test_lake_dependency_retains_unknown_config_key(self):
        boundary = self.clean_lake_clone(self.tree)
        self.g(boundary, "config", "alias.x", "status")
        config = (boundary / ".git/config").read_bytes()
        self.assert_lake_content_retained(
            boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:config_key:alias.x")
        self.assertEqual(config, (boundary / ".git/config").read_bytes())

    def test_lake_dependency_retains_object_alternates(self):
        self.assert_lake_metadata_retained(
            "objects/info/alternates", b"", "objects_info_entry:alternates")

    def test_lake_dependency_retains_changed_description(self):
        self.assert_lake_metadata_retained(
            "description", b"local dependency notes\n", "description")

    def test_lake_dependency_retains_unknown_objects_entry(self):
        self.assert_lake_metadata_retained(
            "objects/local-notes", b"local object notes\n", "objects_entry:local-notes")

    def test_lake_dependency_retains_unknown_logs_entry(self):
        self.assert_lake_metadata_retained(
            "logs/local-notes", b"local log notes\n", "logs_entry:local-notes")

    def observed_lake_metadata(self, linux=False):
        boundary = self.clean_lake_clone(self.tree)
        metadata = boundary / ".git"
        keys = self.g(boundary, "config", "--local", "--name-only", "--list").splitlines()
        for key in ("core.ignorecase", "core.precomposeunicode", "core.symlinks"):
            if key in keys:
                self.g(boundary, "config", "--unset-all", key)
        platform = {"core.symlinks": "false"} if linux else {
            "core.ignorecase": "true", "core.precomposeunicode": "true"}
        for key, setting in dict(platform, **{
                "remote.origin.promisor": "true",
                "remote.origin.partialclonefilter": "blob:none"}).items():
            self.g(boundary, "config", key, setting)
        for ref in self.g(boundary, "for-each-ref", "--format=%(refname)").splitlines():
            self.g(boundary, "update-ref", "-d", ref)
        if (metadata / "logs/refs").exists():
            shutil.rmtree(metadata / "logs/refs")
        if (metadata / "refs/remotes").exists():
            shutil.rmtree(metadata / "refs/remotes")
        (metadata / "packed-refs").unlink(missing_ok=True)
        (metadata / "refs/tags").mkdir(exist_ok=True)
        self.assertEqual(["heads", "tags"], sorted(entry.name for entry in (metadata / "refs").iterdir()))
        self.assertEqual([], list((metadata / "refs/heads").iterdir()))
        self.assertEqual([], list((metadata / "refs/tags").iterdir()))
        (metadata / "info/exclude").write_text("# clone exclusions\n\n# comment\n")
        self.assertTrue(all(entry.name.endswith(".sample") for entry in (metadata / "hooks").iterdir()))
        self.assertEqual([], list((metadata / "objects/info").iterdir()))
        self.assertEqual(["HEAD"], sorted(entry.name for entry in (metadata / "logs").iterdir()))
        self.assertEqual("Unnamed repository; edit this file 'description' to name the repository.\n",
                         (metadata / "description").read_text())
        return boundary

    def test_lake_dependency_allows_observed_partial_clone_metadata(self):
        self.observed_lake_metadata()
        self.remove()
        self.assertFalse(self.tree.exists())

    def test_lake_dependency_allows_linux_clone_metadata(self):
        self.observed_lake_metadata(linux=True)
        self.remove()
        self.assertFalse(self.tree.exists())

    def test_lake_dependency_retains_deinitialized_submodule(self):
        boundary = self.clean_lake_clone(self.tree)
        remote = self.root / "dependency-remote.git"
        self.g(boundary, "-c", "protocol.file.allow=always", "submodule", "add", remote, "child")
        self.g(boundary, "-c", "user.name=Dependency Tests", "-c",
               "user.email=dependency@example.invalid", "commit", "-am", "acquired submodule declaration")
        self.g(boundary, "tag", "acquired-submodule")
        (boundary / ".git/COMMIT_EDITMSG").unlink()
        child = boundary / "child"
        self.g(child, "config", "user.name", "Dependency Tests")
        self.g(child, "config", "user.email", "dependency@example.invalid")
        commit = self.local_dependency_commit(child)
        self.g(boundary, "submodule", "deinit", "--force", "child")
        self.assertEqual("", self.g(boundary, "status", "--porcelain"))
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:git_entry:modules")
        metadata = boundary / ".git/modules/child"
        self.assertEqual("local committed bytes\n",
                         self.g(metadata, "show", commit + ":tracked"))

    def test_lake_dependency_retains_own_worktree(self):
        boundary = self.clean_lake_clone(self.tree)
        outside = self.root / "dependency-worktree"
        self.g(boundary, "worktree", "add", "--detach", outside, "HEAD")
        commit = self.local_dependency_commit(outside)
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:git_entry:worktrees")
        self.assertEqual(commit, self.g(outside, "rev-parse", "HEAD").strip())
        self.assertEqual("local committed bytes\n", (outside / "tracked").read_text())

    def test_lake_dependency_retains_reflog_only_commit(self):
        boundary = self.clean_lake_clone(self.tree)
        base = self.g(boundary, "rev-parse", "HEAD").strip()
        commit = self.local_dependency_commit(boundary)
        self.g(boundary, "checkout", "--detach", base)
        self.assertEqual("", self.g(boundary, "status", "--porcelain"))
        self.assertNotIn(commit, self.g(boundary, "rev-list", "HEAD", "--all").splitlines())
        self.assertIn(commit, self.g(boundary, "rev-list", "--reflog").splitlines())
        self.assert_lake_content_retained(boundary, "lake_dependency_local_history:")
        self.assertEqual("local committed bytes\n", self.g(boundary, "show", commit + ":tracked"))

    def flagged_dependency(self, flag):
        boundary = self.clean_lake_clone(self.tree)
        self.g(boundary, "update-index", flag, "tracked")
        (boundary / "tracked").write_text("hidden local bytes\n")
        self.assertEqual("", self.g(boundary, "status", "--porcelain"))
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:index_flags")
        self.assertEqual("hidden local bytes\n", (boundary / "tracked").read_text())

    def test_lake_dependency_retains_assume_unchanged(self):
        self.flagged_dependency("--assume-unchanged")

    def test_lake_dependency_retains_skip_worktree(self):
        self.flagged_dependency("--skip-worktree")

    def test_lake_dependency_retains_unknown_git_entry(self):
        boundary = self.clean_lake_clone(self.tree)
        unknown = boundary / ".git/unique-content"
        unknown.write_text("local metadata bytes\n")
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:git_entry:unique-content")
        self.assertEqual("local metadata bytes\n", unknown.read_text())

    def test_lake_dependency_retains_nonempty_scope_lock(self):
        boundary = self.clean_lake_clone(self.tree)
        scopes = boundary / ".git/worktree-operations"
        scopes.mkdir()
        lock = scopes / "tree.lock"
        lock.write_text("local bytes\n")
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:scope_lock:tree.lock")
        self.assertEqual("local bytes\n", lock.read_text())

    def test_lake_dependency_retains_unknown_scope_entry(self):
        boundary = self.clean_lake_clone(self.tree)
        scopes = boundary / ".git/worktree-operations"
        scopes.mkdir()
        (scopes / "unknown").touch()
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:scope_lock:unknown")

    def test_lake_dependency_retains_attached_head(self):
        boundary = self.clean_lake_clone(self.tree)
        self.g(boundary, "checkout", "-b", "local")
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:attached_head")

    def test_lake_dependency_retains_unknown_reference(self):
        boundary = self.clean_lake_clone(self.tree)
        self.g(boundary, "update-ref", "refs/custom/saved", "HEAD")
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:reference_namespace")

    def test_lake_dependency_retains_git_pointer(self):
        boundary = self.clean_lake_clone(self.tree)
        metadata = self.root / "dependency-git"
        (boundary / ".git").rename(metadata)
        (boundary / ".git").write_text("gitdir: " + str(metadata) + "\n")
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:.lake/packages/mathlib:git_directory")

    def test_lake_dependency_retains_failed_allowlist_checks(self):
        import worktree_preservation as preservation
        boundary = self.clean_lake_clone(self.tree)
        original = preservation.git
        for operation in ("config", "symbolic-ref", "for-each-ref", "ls-files"):
            with self.subTest(operation=operation):
                def fail(root, *args, **kwargs):
                    if Path(root) == boundary and args[0] == operation:
                        raise subprocess.TimeoutExpired(["git", operation], 300)
                    return original(root, *args, **kwargs)
                with patch.object(preservation, "git", side_effect=fail), \
                        patch("worktree_publication.commit_snapshot", side_effect=AssertionError("checkpoint")), \
                        patch.object(preservation, "remove_payload", side_effect=AssertionError("payload")):
                    with self.assertRaisesRegex(preservation.Refused, "lake_dependency_check_failed:"):
                        preservation.remove(self.removal_options())
                self.assertTrue(boundary.is_dir())
                self.assertEqual(self.base, self.g(self.main, "rev-parse", self.branch).strip())

    def test_lake_dependency_allows_tag_only_reflog_and_scope_locks(self):
        boundary = self.clean_lake_clone(self.tree)
        base = self.g(boundary, "rev-parse", "HEAD").strip()
        self.g(boundary, "checkout", "--detach", "acquired-tag")
        self.g(boundary, "checkout", "--detach", base)
        for ref in self.g(boundary, "for-each-ref", "--format=%(refname)", "refs/remotes").splitlines():
            self.g(boundary, "update-ref", "-d", ref)
        self.assertEqual("refs/tags/acquired-tag", self.g(boundary, "for-each-ref", "--format=%(refname)").strip())
        self.assertNotEqual(base, self.g(boundary, "rev-parse", "acquired-tag").strip())
        self.assertTrue((boundary / ".git/FETCH_HEAD").is_file())
        self.assertNotEqual("", self.g(boundary, "reflog", "show", "HEAD"))
        scopes = boundary / ".git/worktree-operations"
        scopes.mkdir()
        (scopes / "tree.lock").touch()
        (scopes / "index.lock").touch()
        (boundary / "build").mkdir()
        (boundary / "build/output").write_text("regenerable bytes\n")
        self.assertEqual("", self.g(boundary, "status", "--porcelain"))
        self.remove()
        self.assertFalse(self.tree.exists())

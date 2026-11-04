"""Real Lake clones retain local work before any batch checkpoint or deletion."""

import json
from pathlib import Path
import subprocess
from unittest.mock import patch


class LakeDependencyContentCases:
    def clean_lake_clone(self, project, package="mathlib"):
        seed = self.root / "dependency-source"
        seed.mkdir()
        self.g(seed, "init", "--initial-branch=dev")
        self.g(seed, "config", "user.name", "Dependency Tests")
        self.g(seed, "config", "user.email", "dependency@example.invalid")
        (seed / "tracked").write_text("remote bytes\n")
        (seed / ".gitignore").write_text("build/\n")
        self.g(seed, "add", ".")
        self.g(seed, "commit", "-m", "remote baseline")
        revision = self.g(seed, "rev-parse", "HEAD").strip()
        self.g(seed, "checkout", "--detach")
        (seed / "tagged").write_text("remote tag bytes\n")
        self.g(seed, "add", ".")
        self.g(seed, "commit", "-m", "remote tag history")
        self.g(seed, "tag", "acquired-tag")
        self.g(seed, "checkout", "dev")
        remote = self.root / "dependency-remote.git"
        self.g(self.root, "clone", "--bare", seed, remote)
        boundary = project / ".lake/packages" / package
        boundary.parent.mkdir(parents=True, exist_ok=True)
        self.g(self.root, "clone", "--no-local", remote, boundary)
        self.g(boundary, "fetch", "--tags", "origin")
        self.g(boundary, "checkout", "--detach", revision)
        self.g(boundary, "branch", "-D", "dev")
        (project / "lake-manifest.json").write_text(json.dumps(dict(packages=[
            dict(name=package, type="git", url=str(remote), rev=revision)])) + "\n")
        (project / ".gitignore").write_text(".lake/\n")
        self.assertEqual("", self.g(boundary, "status", "--porcelain"))
        self.assertTrue(self.g(boundary, "rev-list", "--tags", "--not", "--remotes", revision).strip(),
                        "fixture must contain acquired tag-only history")
        return boundary

    def assert_lake_content_retained(self, boundary, reason):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        (self.tree / "owned").write_text("uncheckpointed outer bytes\n")
        second = self.root / "second"
        self.g(self.main, "worktree", "add", "-b", "second", second, self.base)
        (second / "owned").write_text("uncheckpointed second bytes\n")
        result = self.run_protocol("remove", "--names", "second " + self.tree.name, expect=73)
        self.assertIn(reason, result.stderr)
        self.assertTrue(boundary.is_dir())
        self.assertEqual("uncheckpointed outer bytes\n", (self.tree / "owned").read_text())
        self.assertEqual("uncheckpointed second bytes\n", (second / "owned").read_text())
        for branch in (self.branch, "second"):
            self.assertEqual(self.base, self.g(self.main, "rev-parse", branch).strip())
        rows = protocol.inventory(self.main)
        for tree in (self.tree, second):
            self.assertIn(str(tree), [row["worktree"] for row in rows])
            _, metadata = protocol.identity(self.main, tree)
            self.assertFalse((metadata / preservation.REMOVAL_RECORD).exists())

    def test_lake_dependency_retains_modified_tracked_file(self):
        boundary = self.clean_lake_clone(self.tree)
        (boundary / "tracked").write_text("local modified bytes\n")
        self.assert_lake_content_retained(boundary, "lake_dependency_dirty:")
        self.assertEqual("local modified bytes\n", (boundary / "tracked").read_text())

    def test_lake_dependency_retains_staged_file(self):
        boundary = self.clean_lake_clone(self.tree)
        (boundary / "tracked").write_text("local staged bytes\n")
        self.g(boundary, "add", "tracked")
        self.assert_lake_content_retained(boundary, "lake_dependency_dirty:")
        self.assertEqual("local staged bytes\n", self.g(boundary, "show", ":tracked"))

    def test_lake_dependency_retains_untracked_file(self):
        boundary = self.clean_lake_clone(self.tree)
        (boundary / "unique").write_text("local untracked bytes\n")
        self.assert_lake_content_retained(boundary, "lake_dependency_dirty:")
        self.assertEqual("local untracked bytes\n", (boundary / "unique").read_text())

    def local_dependency_commit(self, boundary):
        (boundary / "tracked").write_text("local committed bytes\n")
        self.g(boundary, "add", "tracked")
        self.g(boundary, "-c", "user.name=Dependency Tests", "-c",
               "user.email=dependency@example.invalid", "commit", "-m", "unpublished dependency work")
        # Isolate history coverage from unrecognized commit-message metadata.
        if (boundary / ".git").is_dir():
            (boundary / ".git/COMMIT_EDITMSG").unlink()
        return self.g(boundary, "rev-parse", "HEAD").strip()

    def test_lake_dependency_retains_detached_local_commit(self):
        boundary = self.clean_lake_clone(self.tree)
        commit = self.local_dependency_commit(boundary)
        self.assert_lake_content_retained(boundary, "lake_dependency_local_history:")
        self.assertEqual(commit, self.g(boundary, "rev-parse", "HEAD").strip())

    def test_lake_dependency_retains_local_branch_commit(self):
        boundary = self.clean_lake_clone(self.tree)
        base = self.g(boundary, "rev-parse", "HEAD").strip()
        commit = self.local_dependency_commit(boundary)
        self.g(boundary, "branch", "local-work", commit)
        self.g(boundary, "checkout", "--detach", base)
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:")
        self.assertEqual(commit, self.g(boundary, "rev-parse", "local-work").strip())

    def test_lake_dependency_retains_stash(self):
        boundary = self.clean_lake_clone(self.tree)
        (boundary / "tracked").write_text("stashed local bytes\n")
        self.g(boundary, "-c", "user.name=Dependency Tests", "-c",
               "user.email=dependency@example.invalid", "stash", "push", "-m", "dependency work")
        stash = self.g(boundary, "rev-parse", "refs/stash").strip()
        self.assert_lake_content_retained(boundary, "lake_dependency_unknown_shape:")
        self.assertEqual("stashed local bytes\n", self.g(boundary, "show", stash + ":tracked"))

    def test_lake_dependency_retains_failed_status_check(self):
        boundary = self.clean_lake_clone(self.tree)
        (boundary / ".git/index").write_bytes(b"invalid index")
        self.assert_lake_content_retained(boundary, "lake_dependency_check_failed:")
        self.assertEqual(b"invalid index", (boundary / ".git/index").read_bytes())

    def test_lake_dependency_retains_failed_history_checks(self):
        import worktree_preservation as preservation
        boundary = self.clean_lake_clone(self.tree)
        original = preservation.git
        for operation in ("cat-file", "rev-list"):
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
                self.assertTrue(self.tree.is_dir())
                self.assertEqual(self.base, self.g(self.main, "rev-parse", self.branch).strip())

    def set_lake_manifest_revision(self, revision):
        manifest = self.tree / "lake-manifest.json"
        document = json.loads(manifest.read_text())
        document["packages"][0]["rev"] = revision
        manifest.write_text(json.dumps(document))

    def test_lake_dependency_allows_unresolvable_manifest_revision_with_remote_head(self):
        boundary = self.clean_lake_clone(self.tree)
        self.set_lake_manifest_revision("f" * 40)
        self.g(boundary, "merge-base", "--is-ancestor", "HEAD", "refs/remotes/origin/dev")
        self.remove()
        self.assertFalse(self.tree.exists())

    def test_lake_dependency_retains_local_head_with_unresolvable_manifest_revision(self):
        boundary = self.clean_lake_clone(self.tree)
        commit = self.local_dependency_commit(boundary)
        self.set_lake_manifest_revision("f" * 40)
        self.assert_lake_content_retained(boundary, "lake_dependency_local_history:")
        self.assertEqual(commit, self.g(boundary, "rev-parse", "HEAD").strip())

    def test_lake_dependency_retains_malformed_manifest_revision(self):
        boundary = self.clean_lake_clone(self.tree)
        self.set_lake_manifest_revision("not-a-commit")
        self.assert_lake_content_retained(boundary, "lake_dependency_check_failed:")

    def test_lake_dependency_retains_declared_bare_repository(self):
        boundary = self.tree / ".lake/packages/mathlib"
        boundary.mkdir(parents=True)
        self.g(boundary, "init", "--bare")
        self.declare_lake_package(self.tree, "mathlib")
        self.assert_lake_content_retained(boundary, "nested_git_boundary:")

    def test_lake_dependency_retains_manifest_outside_target(self):
        moved = self.root / ".lake"
        self.g(self.main, "worktree", "move", self.tree, moved)
        self.tree = moved
        boundary = self.clean_lake_clone(self.root)
        self.assert_lake_content_retained(boundary, "nested_git_boundary:")

    def test_lake_dependency_allows_ignored_build_and_acquired_tag(self):
        boundary = self.clean_lake_clone(self.tree)
        (boundary / "build").mkdir()
        (boundary / "build/output").write_text("regenerable bytes\n")
        result = self.remove()
        self.assertEqual(0, result.returncode)
        self.assertFalse(self.tree.exists())

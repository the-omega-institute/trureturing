"""Real Git mirror preflight, conflict and publication recovery probes."""

import json


class MirrorCases:
    def test_mirror_operation_publishes_then_qualifies_removal(self):
        self.g(self.main, "switch", "-c", "feature")
        (self.main / "feature").write_text("feature\n")
        self.g(self.main, "add", "feature")
        self.g(self.main, "commit", "-m", "feature")
        feature = self.g(self.main, "rev-parse", "HEAD").strip()
        mirror = self.root / "mirror-tree"
        branch = "mirror/integration/11"
        destination = self.root / "mirror-push.git"
        self.g(self.root, "init", "--bare", destination)
        self.g(self.main, "remote", "set-url", "--push", "origin", destination)
        self.run_protocol("prepare-mirror", "--path", mirror, "--branch", branch, "--base", self.base,
                          "--merge", feature, "--message", "mirror: feature")
        self.assertEqual("feature\n", self.g(mirror, "show", "HEAD:feature"))
        self.assertEqual(self.g(mirror, "rev-parse", "HEAD"), self.g(destination, "rev-parse", "refs/heads/" + branch))
        self.assertEqual("", self.g(self.remote, "for-each-ref", "refs/heads/" + branch))
        (mirror / "ordinary-after-push").write_text("recover locally\n")
        self.run_protocol("remove", "--names", mirror.name)
        self.assertFalse(mirror.exists())
        self.g(self.main, "worktree", "add", mirror, branch)
        self.assertEqual("recover locally\n", (mirror / "ordinary-after-push").read_text())

    def test_mirror_failure_retains_conflict_and_failed_publication(self):
        self.g(self.main, "switch", "-c", "feature")
        (self.main / "owned").write_text("feature\n")
        self.g(self.main, "commit", "-am", "feature")
        feature = self.g(self.main, "rev-parse", "HEAD").strip()
        self.g(self.main, "switch", "dev")
        (self.main / "owned").write_text("integration\n")
        self.g(self.main, "commit", "-am", "integration")
        base = self.g(self.main, "rev-parse", "HEAD").strip()
        mirror = self.root / "mirror-conflict"
        self.run_protocol("prepare-mirror", "--path", mirror, "--branch", "mirror/conflict/11", "--base", base,
                          "--merge", feature, "--message", "mirror: conflict", expect=73)
        self.assertTrue(self.g(mirror, "ls-files", "--unmerged"))
        self.run_protocol("remove", "--names", mirror.name, expect=68)
        failed = self.root / "mirror-rejected"
        branch = "mirror/rejected/11"
        hook = self.remote / "hooks/pre-receive"
        hook.write_text("#!/bin/sh\necho publication-rejected >&2\nexit 1\n")
        hook.chmod(0o755)
        result = self.run_protocol("prepare-mirror", "--path", failed, "--branch", branch, "--base", self.base,
                          "--merge", feature, "--message", "mirror: rejected", expect=73)
        self.assertIn("publication-rejected", result.stderr)
        self.assertEqual("feature\n", (failed / "owned").read_text())
        head = self.g(failed, "rev-parse", "HEAD").strip()
        self.assertEqual([self.base, feature], self.g(failed, "show", "-s", "--format=%P", head).split())
        self.assertEqual(head, self.g(self.main, "rev-parse", "refs/heads/" + branch).strip())
        self.assertEqual("", self.g(self.remote, "for-each-ref", "refs/heads/" + branch))
        self.run_protocol("remove", "--names", failed.name, expect=68)
        hook.unlink()
        published = self.run_protocol("publish", "--path", failed, "--branch", branch)
        self.assertEqual("confirmed", json.loads(published.stdout)["status"])
        self.assertEqual(head, self.g(self.remote, "rev-parse", "refs/heads/" + branch).strip())

    def test_mirror_missing_endpoint_refused_before_creation(self):
        failed = self.root / "mirror-offline"
        branch = "mirror/offline/11"
        before = self.g(self.main, "worktree", "list", "--porcelain")
        self.g(self.main, "remote", "set-url", "origin", self.root / "missing.git")
        self.run_protocol("prepare-mirror", "--path", failed, "--branch", branch, "--base", self.base,
                          "--merge", self.base, "--message", "mirror: offline", expect=73)
        self.assertFalse(failed.exists())
        self.assertEqual(before, self.g(self.main, "worktree", "list", "--porcelain"))
        self.assertEqual("", self.g(self.main, "for-each-ref", "refs/heads/" + branch))
# C7_MIRROR_POSITIVE_6ACAC960

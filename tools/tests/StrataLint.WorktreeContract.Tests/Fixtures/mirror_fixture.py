"""Real Git mirror preflight, conflict and publication recovery probes."""

import json
import subprocess


class MirrorCases:
    def mirror_operation_publishes_then_qualifies_removal(self):
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

    def mirror_failure_retains_conflict_and_failed_publication(self):
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
        blocked = json.loads(self.run_protocol("remove", "--names", mirror.name, expect=74).stdout)
        self.assertEqual("checkpoint_failed", blocked["items"][0]["outcome"])
        self.assertEqual("unmerged_index", blocked["items"][0]["error"])
        failed = self.root / "mirror-rejected"
        branch = "mirror/rejected/11"
        hook = self.remote / "hooks/pre-receive"
        hook.write_text("#!/bin/sh\necho publication-rejected >&2\nexit 1\n")
        hook.chmod(0o755)
        result = self.run_protocol("prepare-mirror", "--path", failed, "--branch", branch, "--base", self.base,
                          "--merge", feature, "--message", "mirror: rejected", expect=73)
        self.assertIn("publication-rejected", result.stderr)
        receipt = json.loads(next(line[len("WORKTREE_FAILED "):] for line in result.stderr.splitlines()
                                  if line.startswith("WORKTREE_FAILED ")))
        self.assertEqual("publication", receipt["stage"])
        self.assertEqual(str(failed), receipt["target"])
        self.assertIn("reclaim", receipt["recovery_action"])
        self.assertEqual("feature\n", (failed / "owned").read_text())
        head = self.g(failed, "rev-parse", "HEAD").strip()
        self.assertEqual([self.base], self.g(failed, "show", "-s", "--format=%P", head).split())
        self.assertEqual(head, self.g(self.main, "rev-parse", "refs/heads/" + branch).strip())
        self.assertEqual("", self.g(self.remote, "for-each-ref", "refs/heads/" + branch))
        hook.unlink()
        published = self.run_protocol("publish", "--path", failed, "--branch", branch)
        self.assertEqual("confirmed", json.loads(published.stdout)["status"])
        self.assertEqual(head, self.g(self.remote, "rev-parse", "refs/heads/" + branch).strip())
        self.run_protocol("remove", "--names", failed.name)

    def mirror_missing_endpoint_refused_before_creation(self):
        failed = self.root / "mirror-offline"
        branch = "mirror/offline/11"
        before = self.g(self.main, "worktree", "list", "--porcelain")
        self.g(self.main, "remote", "set-url", "origin", self.root / "missing.git")
        self.run_protocol("prepare-mirror", "--path", failed, "--branch", branch, "--base", self.base,
                          "--merge", self.base, "--message", "mirror: offline", expect=73)
        self.assertFalse(failed.exists())
        self.assertEqual(before, self.g(self.main, "worktree", "list", "--porcelain"))
        self.assertEqual("", self.g(self.main, "for-each-ref", "refs/heads/" + branch))

    def mirror_landing(self, branch, name, subject, squash=False):
        self.g(self.main, "switch", "-c", branch)
        (self.main / name).write_text(name + "\n")
        self.g(self.main, "add", name)
        self.g(self.main, "commit", "-m", name)
        self.g(self.main, "switch", "dev")
        if squash:
            self.g(self.main, "merge", "--squash", branch)
            self.g(self.main, "commit", "-m", subject)
        else:
            self.g(self.main, "merge", "--no-ff", "-m", subject, branch)
        return self.g(self.main, "rev-parse", "HEAD").strip()

    def patch_id(self, parent, head):
        patch = self.g(self.main, "diff", "--binary", parent, head)
        return subprocess.run(["git", "patch-id", "--stable"], input=patch,
                              text=True, capture_output=True, check=True).stdout.split()[:1]

    def mirror_only_target_delta_with_missing_merge_and_squash(self):
        self.mirror_landing("earlier-merge", "earlier-merge", "custom earlier merge")
        self.mirror_landing("earlier-squash", "earlier-squash", "earlier squash (#12)", squash=True)
        for squash in (False, True):
            with self.subTest(squash=squash):
                name = "target-" + str(squash)
                subject = "custom target (#13)"
                landing = self.mirror_landing(name, name, subject, squash=squash)
                mirror = self.root / name
                result = self.run_protocol("prepare-mirror", "--path", mirror, "--branch", "mirror/" + name,
                    "--base", self.base, "--merge", landing, "--message", "mirror: #13 " + subject)
                head = json.loads(result.stdout)["commit"]
                self.assertEqual([self.base], self.g(mirror, "show", "-s", "--format=%P", head).split())
                self.assertEqual([name], self.g(mirror, "diff", "--name-only", self.base, head).splitlines())
                self.assertEqual(self.patch_id(landing + "^1", landing), self.patch_id(self.base, head))
                self.assertEqual(landing, self.g(mirror, "show", "-s",
                    "--format=%(trailers:key=Original-Dev-Commit,valueonly)", head).strip())
                self.assertEqual("mirror: #13 " + subject, self.g(mirror, "show", "-s", "--format=%s", head).strip())

    def mirror_validator_rejects_wrong_delta_identity_parent_and_base(self):
        landing = self.mirror_landing("feature", "feature", "custom feature")
        message = "mirror: #11 custom feature"
        mirror = self.root / "mirror-valid"
        result = self.run_protocol("prepare-mirror", "--path", mirror, "--branch", "mirror/valid",
            "--base", self.base, "--merge", landing, "--message", message)
        head = json.loads(result.stdout)["commit"]
        def validate(commit, base=self.base, expected=0):
            return self.run_protocol("validate-mirror", "--commit", commit, "--base", base,
                "--merge", landing, "--message", message, expect=expected)
        self.assertEqual(self.base, json.loads(validate(head).stdout)["base"])
        for fault in ("identity", "delta", "two-parents", "outside-base"):
            with self.subTest(fault=fault):
                tree = self.g(self.main, "rev-parse", (self.base if fault == "delta" else head) + "^{tree}").strip()
                parents = ["-p", self.base]
                if fault == "two-parents": parents += ["-p", landing]
                if fault == "outside-base": parents = ["-p", landing]
                original = self.base if fault == "identity" else landing
                invalid = self.g(self.main, "commit-tree", tree, *parents, "-m",
                    message + "\n\nOriginal-Dev-Commit: " + original).strip()
                validate(invalid, expected=73)
                branch = "mirror/invalid-" + fault
                self.g(self.main, "update-ref", "refs/heads/" + branch, invalid)
                self.run_protocol("prepare-mirror", "--path", self.root / ("invalid-" + fault),
                    "--branch", branch, "--base", self.base, "--merge", landing,
                    "--message", message, expect=73)
                self.assertEqual("", self.g(self.remote, "for-each-ref", "refs/heads/" + branch))
                self.assertEqual(invalid, self.g(self.main, "rev-parse", branch).strip())

    def mirror_retained_commit_reused_on_descendant_integration_base(self):
        landing = self.mirror_landing("feature", "feature", "feature (#11)", squash=True)
        mirror = self.root / "retained"
        branch = "mirror/retained"
        message = "mirror: #11 feature (#11)"
        hook = self.remote / "hooks/pre-receive"
        hook.write_text("#!/bin/sh\nexit 1\n")
        hook.chmod(0o755)
        self.run_protocol("prepare-mirror", "--path", mirror, "--branch", branch, "--base", self.base,
                          "--merge", landing, "--message", message, expect=73)
        head = self.g(mirror, "rev-parse", "HEAD").strip()
        self.g(self.main, "worktree", "unlock", mirror)
        self.g(self.main, "worktree", "remove", mirror)
        self.g(self.main, "switch", "-c", "integration", self.base)
        (self.main / "independent").write_text("integration\n")
        self.g(self.main, "add", "independent")
        self.g(self.main, "commit", "-m", "integration advance")
        tip = self.g(self.main, "rev-parse", "HEAD").strip()
        hook.unlink()
        result = self.run_protocol("prepare-mirror", "--path", mirror, "--branch", branch, "--base", tip,
                                  "--merge", landing, "--message", message)
        self.assertEqual(head, json.loads(result.stdout)["commit"])
        self.assertEqual([self.base], self.g(mirror, "show", "-s", "--format=%P", head).split())
        self.assertEqual(head, self.g(self.remote, "rev-parse", "refs/heads/" + branch).strip())

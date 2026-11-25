"""Exercise tools pin admission with the GitHub objects seen by the required check."""

import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("installer", Path(__file__).with_name("install-tools.py"))
installer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(installer)

OLD, A, B_OLD, B_NEW, DEV = (letter * 40 for letter in "01234")
ROOT_PIN, A_PIN = (letter * 40 for letter in "ab")
DIGEST = "d" * 64


def pin(source, number, run):
    return {"version": f"v0.1.1-pr.{number}.{run}.g{source[:12]}", "source_sha": source, "sha256": DIGEST}


class Admission(unittest.TestCase):
    def setUp(self):
        self.objects = {}
        self.legacy = {"version": f"v0.1.1-dev.g{OLD}", "sha256": DIGEST}
        self.a, self.b_old, self.b_new = pin(A, 10, 1), pin(B_OLD, 11, 2), pin(B_NEW, 11, 3)
        self.add_tag(self.legacy["version"], OLD)
        self.add_preview(self.a, ROOT_PIN)
        self.add_preview(self.b_old, ROOT_PIN)
        self.add_preview(self.b_new, A_PIN)
        self.add_ancestry(OLD, A)
        self.add_ancestry(OLD, B_OLD)
        self.add_ancestry(A, B_OLD)  # B was already stacked when it published its old preview.
        self.add_ancestry(A, B_NEW)
        self.add_ancestry(OLD, "dev")
        api = patch.object(installer, "api", side_effect=lambda repo, path, **_: self.objects[repo, path])
        api.start()
        self.addCleanup(api.stop)

    def add_tag(self, version, source):
        self.objects[installer.TOOLS, f"git/ref/tags/{version}"] = {"object": {"type": "commit", "sha": source}}
        self.objects[installer.TOOLS, f"releases/tags/{version}"] = {
            "tag_name": version, "draft": False, "prerelease": "-" in version, "author": {"id": 41898282},
            "assets": [{"name": "trureturing-tools.tar.gz", "state": "uploaded", "digest": f"sha256:{DIGEST}",
                        "uploader": {"id": installer.ACTIONS_BOT}}],
        }

    def add_preview(self, pin, baseline):
        version, source = pin["version"], pin["source_sha"]
        self.add_tag(version, source)
        self.objects[installer.TOOLS, f"git/commits/{source}"] = {
            "message": f"Preview\n\nConsumer-Tools-Base: {baseline}\n",
        }
        number = installer.PR_PREVIEW.fullmatch(version)[1]
        self.objects[installer.TOOLS, f"pulls/{number}"] = {
            "base": {"ref": "dev", "repo": {"full_name": installer.TOOLS}},
            "head": {"repo": {"full_name": installer.TOOLS}, "sha": source, "ref": f"pair-{number}"},
            "draft": False, "state": "open", "merged": False,
        }
        run = {"id": int(number), "run_attempt": 1, "path": ".github/workflows/ci.yml",
               "head_sha": source, "head_branch": f"pair-{number}", "status": "completed",
               "conclusion": "success", "event": "pull_request",
               "head_repository": {"full_name": installer.TOOLS},
               "pull_requests": [{"number": int(number), "head": {"sha": source}}]}
        self.objects[installer.TOOLS, f"actions/workflows/ci.yml/runs?head_sha={source}&status=success&per_page=100"] = [
            {"workflow_runs": [run]}
        ]
        self.objects[installer.TOOLS, f"actions/runs/{number}/attempts/1/jobs?per_page=100"] = {
            "jobs": [
                {"name": name, "conclusion": "success", "steps": [{"name": step, "conclusion": "success"}]}
                for name, step in [
                    ("verify", "Run python3 .github/scripts/test-suites.py standalone"),
                    ("package", "Run python3 package_release.py"),
                    *((f"Consumer fixture {i}", "Exercise candidate tools against the consumer fixture")
                      for i in range(4)),
                ]
            ]
        }

    def add_ancestry(self, base, head, ancestor=None):
        self.objects[installer.TOOLS, f"compare/{base}...{head}?per_page=1"] = {
            "merge_base_commit": {"sha": ancestor or base},
        }

    def test_concurrent_adoption_requires_new_publication_even_for_stacked_head(self):
        self.add_preview(self.b_old, ROOT_PIN)
        installer.verify_adopted_source(self.a, ROOT_PIN, self.legacy, "pull_request")
        installer.verify_adopted_source(self.b_old, ROOT_PIN, self.legacy, "pull_request")
        with self.assertRaisesRegex(ValueError, "publish a new preview"):
            installer.verify_adopted_source(self.b_old, A_PIN, self.a, "pull_request")
        self.add_preview(self.b_new, A_PIN)
        installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")
        installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")

    def test_reject_wrong_ancestry_target_and_drift_independently(self):
        pull = self.objects[installer.TOOLS, "pulls/11"]
        self.add_ancestry(A, B_NEW, OLD)
        with self.assertRaisesRegex(ValueError, "contain the previous"):
            installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")
        self.add_ancestry(A, B_NEW)
        pull["base"]["ref"] = "main"
        with self.assertRaisesRegex(ValueError, "exact published head"):
            installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")
        pull["base"]["ref"] = "dev"
        pull["head"]["sha"] = B_OLD
        with self.assertRaisesRegex(ValueError, "exact published head"):
            installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")

    def test_ci_requires_the_exact_tested_head_pr_and_successful_package(self):
        endpoint = f"actions/workflows/ci.yml/runs?head_sha={B_NEW}&status=success&per_page=100"
        run = self.objects[installer.TOOLS, endpoint][0]["workflow_runs"][0]
        jobs = self.objects[installer.TOOLS, "actions/runs/11/attempts/1/jobs?per_page=100"]["jobs"]
        for key, value in (("head_sha", B_OLD), ("head_branch", "other"),
                           ("path", ".github/workflows/other.yml"),
                           ("pull_requests", [{"number": 12, "head": {"sha": B_NEW}}])):
            with self.subTest(key=key), patch.dict(run, {key: value}):
                with self.assertRaisesRegex(ValueError, "no successful tools ci.yml"):
                    installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")
        jobs[1]["steps"][0]["conclusion"] = "skipped"
        with self.assertRaisesRegex(ValueError, "no successful tools ci.yml"):
            installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")
        jobs[1]["steps"][0]["conclusion"] = "success"
        with patch.dict(run, {"event": "push", "pull_requests": []}):
            installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")

    def test_legacy_stable_and_dev_and_pinned_digest_and_source(self):
        installer.verify_adopted_source(self.legacy)
        self.add_tag("v0.2.0", OLD)
        self.add_ancestry(OLD, "main")
        installer.verify_adopted_source({"version": "v0.2.0", "sha256": DIGEST})
        self.assertEqual(installer.parse_pin(json.dumps(self.legacy | {"workflow_sha": DEV})),
                         self.legacy | {"workflow_sha": DEV})
        no_source = {key: value for key, value in self.a.items() if key != "source_sha"}
        with self.assertRaisesRegex(ValueError, "full source_sha"):
            installer.verify_adopted_source(no_source)
        with self.assertRaisesRegex(ValueError, "checksum"):
            installer.verify_adopted_source(self.a | {"sha256": "e" * 64}, ROOT_PIN, self.legacy, "pull_request")
        with self.assertRaisesRegex(ValueError, "full source SHA"):
            installer.verify_adopted_source(self.a | {"source_sha": A[:12] + "f" * 28},
                                            ROOT_PIN, self.legacy, "pull_request")

    def test_legacy_parse_and_malformed_previous_pin(self):
        self.assertEqual(installer.parse_pin(json.dumps(self.legacy)), self.legacy)
        for previous_pin in (None, 0, "a" * 39, "A" * 40, "g" * 40):
            with self.subTest(previous_pin=previous_pin), self.assertRaisesRegex(ValueError, "invalid tools release pin"):
                installer.parse_pin(json.dumps(self.legacy | {"previous_pin": previous_pin}))
        duplicate = json.dumps(self.legacy | {"previous_pin": ROOT_PIN})[:-1] + f', "previous_pin":"{A_PIN}"}}'
        with self.assertRaisesRegex(ValueError, "duplicate field"):
            installer.parse_pin(duplicate)


class ConsumerGit(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.repo = Path(directory.name)
        self.git("init", "-b", "dev")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "user.name", "Test")
        self.lock = self.repo / installer.PIN
        self.lock.parent.mkdir()
        (self.repo / ".gitattributes").write_bytes((installer.ROOT / ".gitattributes").read_bytes())
        self.original_pin = {"version": "v0.1.0", "sha256": DIGEST}
        self.original = self.commit(self.original_pin)
        self.baseline = self.blob(self.original)
        self.a = self.original_pin | {"version": "v0.1.1", "previous_pin": self.baseline}
        self.b = self.original_pin | {"sha256": "b" * 64, "previous_pin": self.baseline}

    def git(self, *args, check=True):
        return subprocess.run(["git", "-C", self.repo, *args], capture_output=True, text=True, check=check)

    def commit(self, lock=None):
        if lock is not None:
            self.lock.write_text(json.dumps(lock, indent=2) + "\n")
        self.git("add", "-A")
        self.git("commit", "--allow-empty", "-m", "Fixture")
        return self.git("rev-parse", "HEAD").stdout.strip()

    def blob(self, commit):
        entry = self.git("ls-tree", commit, "--", installer.PIN).stdout
        return entry.split()[2] if entry else None

    def checkout(self, commit):
        self.git("switch", "--detach", commit)

    def merge(self, ref, *, check=True):
        return self.git("merge", "--no-ff", "-m", "Fixture merge", ref, check=check)

    def api(self, repo, endpoint, **kwargs):
        if endpoint.startswith("compare/"):
            self.assertEqual(kwargs, {"paginate": True})
            base, head = endpoint.split("/")[1].split("?")[0].split("...")
            commits = self.git("rev-list", f"{base}..{head}").stdout.splitlines()
            count = len(commits)
            return [{"base_commit": {"sha": base}, "ahead_by": count,
                     "commits": [{"sha": commit} for commit in page]}
                    for page in (commits[:1], commits[1:]) if page] or [
                        {"base_commit": {"sha": base}, "ahead_by": 0, "commits": []}
                    ]
        if endpoint == "git/ref/heads/dev":
            return {"object": {"sha": self.dev}}
        if endpoint == f"contents/{installer.PIN}?ref={self.dev}":
            return {"sha": self.blob(self.dev)}
        self.fail(f"unexpected API call {repo}/{endpoint}")

    def graphql(self, *args):
        snapshots = {}
        for key, commit in re.findall(r'(c\d+):object\(oid:"([0-9a-f]{40})"\)', args[-1]):
            blob = self.blob(commit)
            parents = self.git("show", "-s", "--format=%P", commit).stdout.split()
            parent_entries = [self.blob(parent) for parent in parents]
            snapshots[key] = {"oid": commit, "file": {"oid": blob, "mode": 0o100644} if blob else None,
                              "parents": {"nodes": [{"file": {"oid": oid, "mode": 0o100644} if oid else None}
                                                    for oid in parent_entries]}}
        return {"data": {"repository": snapshots}}

    def verify(self, *, event="pull_request", checkout=None):
        with (patch.object(installer, "ROOT", checkout or self.repo),
              patch.object(installer, "api", side_effect=self.api),
              patch.object(installer, "github", side_effect=self.graphql),
              patch.object(installer, "verify_adopted_source") as source):
            installer.verify_adoption(event, installer.CONSUMER)
            return source

    def test_parallel_disjoint_edits_conflict_as_one_lock_after_both_pass(self):
        a = self.commit(self.a)
        self.checkout(self.original)
        b = self.commit(self.b)
        self.dev = self.original
        for branch in (a, b):
            self.checkout(self.original)
            self.merge(branch)
            self.verify().assert_called_once()
        self.checkout(a)
        merge = self.merge(b, check=False)
        self.assertEqual(merge.returncode, 1, merge.stderr)
        self.assertIn(f"Cannot merge binary files: {installer.PIN}", merge.stdout + merge.stderr)

    def test_clean_stacked_merge_would_reuse_stale_approval(self):
        a = self.commit(self.a)
        # The side parent carries the third pin, so a first-parent scan misses it.
        self.checkout(self.original)
        self.commit(self.b)
        self.git("merge", "--no-ff", "-s", "ours", "-m", "Fixture side merge", a)
        b = self.git("rev-parse", "HEAD").stdout.strip()
        self.checkout(self.original)
        self.dev = self.original
        self.merge(b)
        with self.assertRaisesRegex(ValueError, "intermediate pin edits"):
            self.verify()
        self.git("branch", "tested-merge")
        with tempfile.TemporaryDirectory() as path:
            self.git("clone", "--depth=2", "--branch=tested-merge", self.repo.as_uri(), path)
            shallow = Path(path)
            with patch.object(installer, "ROOT", shallow):
                self.assertNotIn(a, installer.git("rev-list", "HEAD").decode().split())
            with self.assertRaisesRegex(ValueError, "intermediate pin edits"):
                self.verify(checkout=shallow)
        # After A lands as a merge commit, Git takes A as the merge base.
        # Even with -merge, it now merges B cleanly.
        self.checkout(self.original)
        self.merge(a)
        self.dev = self.git("rev-parse", "HEAD").stdout.strip()
        self.assertEqual(self.git("merge-base", self.dev, b).stdout.strip(), a)
        self.merge(b)
        with self.assertRaisesRegex(ValueError, "previous_pin must match"):
            self.verify()
        self.checkout(self.dev)
        refreshed = self.commit(self.b | {"previous_pin": self.blob(self.dev)})
        self.checkout(self.dev)
        self.merge(refreshed)
        self.verify().assert_called_once()
        self.verify().assert_called_once()

    def test_pin_neutral_head_with_intermediate_change_is_rejected(self):
        a = self.commit(self.a)
        b = self.commit(self.original_pin)
        self.checkout(self.original)
        self.dev = self.original
        self.merge(b)
        with self.assertRaisesRegex(ValueError, "intermediate pin edits"):
            self.verify()
        self.checkout(self.original)
        self.merge(a)
        self.merge(b)
        self.assertEqual(self.blob("HEAD"), self.baseline)

    def test_rollback_has_new_generation_and_stale_consumer_conflicts(self):
        a = self.commit(self.a)
        rollback = self.commit(self.original_pin | {"previous_pin": self.blob(a)})
        self.assertNotEqual(self.blob(rollback), self.baseline)
        self.dev = a
        self.checkout(a)
        self.merge(rollback)
        self.verify().assert_called_once()
        self.checkout(self.original)
        stale = self.commit(self.b)
        self.checkout(rollback)
        self.assertEqual(self.merge(stale, check=False).returncode, 1)

    def test_unrelated_updates_preserve_eligibility_and_pin(self):
        a = self.commit(self.a)
        self.checkout(self.original)
        (self.repo / "unrelated").write_text("change")
        unrelated = self.commit()
        self.dev = unrelated
        self.merge(a)
        self.verify().assert_called_once()
        self.checkout(a)
        self.dev = a
        self.merge(unrelated)
        self.verify().assert_not_called()

    def test_content_pr_can_merge_dev_across_a_tools_adoption(self):
        adopted = self.commit(self.a)
        self.checkout(self.original)
        (self.repo / "content").write_text("content before adoption")
        self.commit()
        self.merge(adopted)
        (self.repo / "content").write_text("content after adoption")
        content = self.commit()
        self.checkout(adopted)
        self.dev = adopted
        self.merge(content)
        self.verify().assert_not_called()

    def test_missing_wrong_and_stale_predecessors_are_rejected(self):
        for edited in (self.original_pin | {"version": "v0.1.2"}, self.a | {"previous_pin": ROOT_PIN}):
            self.checkout(self.original)
            candidate = self.commit(edited)
            self.checkout(self.original)
            self.dev = self.original
            self.merge(candidate)
            with self.assertRaisesRegex(ValueError, "previous_pin must match"):
                self.verify()
            with self.assertRaisesRegex(ValueError, "previous_pin must match"):
                self.verify(event="push")
        self.checkout(self.original)
        candidate = self.commit(self.b)
        self.checkout(self.original)
        newer = self.commit(self.a)
        self.dev = newer
        self.checkout(self.original)
        self.merge(candidate)
        with self.assertRaisesRegex(ValueError, "consumer dev changed"):
            self.verify()

    def test_missing_intermediate_pin_and_truncated_compare_are_rejected(self):
        self.lock.unlink()
        self.commit()
        candidate = self.commit(self.b)
        self.checkout(self.original)
        self.dev = self.original
        self.merge(candidate)
        with self.assertRaisesRegex(ValueError, "intermediate pin edits"):
            self.verify()
        with patch.object(installer, "api", return_value=[
            {"base_commit": {"sha": self.original}, "ahead_by": 2, "commits": [{"sha": candidate}]},
        ]):
            with self.assertRaisesRegex(ValueError, "incomplete consumer PR commit range"):
                installer.pr_only_commits(installer.CONSUMER, self.original, candidate)


if __name__ == "__main__":
    unittest.main()

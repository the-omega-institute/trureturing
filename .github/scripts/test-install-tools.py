"""Exercise tools pin admission with the GitHub objects seen by the required check."""

import importlib.util
import json
from pathlib import Path
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
        self.set_live_pin(ROOT_PIN)
        api = patch.object(installer, "api", side_effect=lambda repo, path: self.objects[repo, path])
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
            "head": {"repo": {"full_name": installer.TOOLS}, "sha": source},
            "draft": False, "state": "open", "merged": False,
        }

    def add_ancestry(self, base, head, ancestor=None):
        self.objects[installer.TOOLS, f"compare/{base}...{head}?per_page=1"] = {
            "merge_base_commit": {"sha": ancestor or base},
        }

    def set_live_pin(self, baseline, dev=DEV):
        self.objects[installer.CONSUMER, "git/ref/heads/dev"] = {"object": {"sha": dev}}
        self.objects[installer.CONSUMER, f"contents/{installer.PIN}?ref={dev}"] = {"sha": baseline}

    def test_concurrent_adoption_requires_new_publication_even_for_stacked_head(self):
        self.add_preview(self.b_old, ROOT_PIN)
        installer.verify_adopted_source(self.a, ROOT_PIN, self.legacy, "pull_request")
        installer.verify_adopted_source(self.b_old, ROOT_PIN, self.legacy, "pull_request")
        self.set_live_pin(ROOT_PIN, dev="e" * 40)
        installer.verify_adopted_source(self.b_old, ROOT_PIN, self.legacy, "pull_request")
        self.set_live_pin(A_PIN)
        with self.assertRaisesRegex(ValueError, "consumer dev changed"):
            installer.verify_adopted_source(self.b_old, ROOT_PIN, self.legacy, "pull_request")
        with self.assertRaisesRegex(ValueError, "publish a new preview"):
            installer.verify_adopted_source(self.b_old, A_PIN, self.a, "pull_request")
        self.add_preview(self.b_new, A_PIN)
        installer.verify_adopted_source(self.b_new, A_PIN, self.a, "pull_request")

    def test_reject_wrong_ancestry_target_and_drift_independently(self):
        self.set_live_pin(A_PIN)
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

    def test_git_rejects_concurrent_lock_changes_when_consumer_pr_merges(self):
        with tempfile.TemporaryDirectory() as path:
            def git(*args):
                return subprocess.run(["git", "-C", path, *args], capture_output=True, text=True)

            git("init", "-b", "dev").check_returncode()
            git("config", "user.email", "test@example.invalid").check_returncode()
            git("config", "user.name", "Test").check_returncode()
            lock = Path(path, installer.PIN)
            lock.parent.mkdir()

            def commit(candidate):
                lock.write_text(json.dumps(candidate, indent=2) + "\n")
                git("add", installer.PIN).check_returncode()
                git("commit", "-m", "Update tools").check_returncode()

            commit(self.legacy)
            git("branch", "b").check_returncode()
            commit(self.a | {"sha256": "a" * 64})
            git("switch", "b").check_returncode()
            commit(self.b_old | {"sha256": "b" * 64})
            git("switch", "dev").check_returncode()
            merge = git("merge", "--no-commit", "b")
            self.assertEqual(merge.returncode, 1, merge.stderr)
            self.assertIn(f"CONFLICT (content): Merge conflict in {installer.PIN}", merge.stdout)


if __name__ == "__main__":
    unittest.main()

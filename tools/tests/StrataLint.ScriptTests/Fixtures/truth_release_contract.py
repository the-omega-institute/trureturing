"""Release orchestration consumes selected common bundles without a producer fallback."""
import importlib
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

REPO = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(REPO / "tools/scripts/workflow"))
COMMIT = "a" * 40


class ReleaseContracts(unittest.TestCase):
    def test_composition_preserves_the_callers_package_environment(self):
        owner = importlib.import_module("truth_release")
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            packages = str(root / "absent-packages")
            with mock.patch.dict(os.environ, NUGET_PACKAGES=packages), \
                 mock.patch.object(owner, "run", side_effect=[COMMIT, "0"]), \
                 mock.patch.object(owner.subprocess, "run", side_effect=RuntimeError("composition invoked")) as compose:
                with self.assertRaisesRegex(RuntimeError, "composition invoked"):
                    owner.assemble(root, root, dict(source_commit=COMMIT, required_checks=[]))
                environment = compose.call_args.kwargs.get("env", os.environ)
                self.assertEqual(packages, environment["NUGET_PACKAGES"])
                self.assertEqual("truth-release", compose.call_args.args[0][2])

    def test_unavailable_artifact_listing_becomes_an_unavailable_bundle(self):
        owner = importlib.import_module("truth_release")
        with mock.patch.object(owner, "pages", side_effect=[
                [{"id": 22, "run_attempt": 2}], [], subprocess.CalledProcessError(1, "gh")]):
            evidence = owner.collect("owner/repo", COMMIT, {})
        self.assertEqual([], evidence["artifacts"]["22"])

    def exercise(self, failures, composition_failure=False):
        owner = importlib.import_module("truth_release")
        candidates = [dict(publish_ready=True, source_commit=COMMIT, run_id=22, run_attempt=2, artifact_id=220),
                      dict(publish_ready=True, source_commit=COMMIT, run_id=21, run_attempt=1, artifact_id=210),
                      dict(publish_ready=False)]
        evidence = {"runs": [{"id": 22}, {"id": 21}]}
        restored = []
        def restore(root, area, selected):
            restored.append(selected["run_id"])
            if selected["run_id"] in failures:
                raise ValueError("missing or corrupt bundle")
            return root
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            with mock.patch.object(owner, "api", side_effect=[{"protected": True}, {"path": "workflow"}, [{"sha": COMMIT}]]), \
                 mock.patch.object(owner, "collect", return_value=evidence), \
                 mock.patch.object(owner, "select", side_effect=candidates), \
                 mock.patch.object(owner, "restore_candidate", side_effect=restore), \
                 mock.patch.object(owner, "assemble", side_effect=RuntimeError("real release check failed") if composition_failure else None,
                                   return_value={"release_digest": "sha256:" + "b" * 64}) as assemble, \
                 mock.patch.object(owner, "outputs") as output:
                if composition_failure:
                    with self.assertRaisesRegex(RuntimeError, "real release check failed"):
                        owner.prepare(root, root, "owner/repo")
                else:
                    owner.prepare(root, root, "owner/repo")
                return restored, assemble.call_count, output.call_args.args[0] if output.called else None

    def test_valid_upstream_is_consumed_once(self):
        restored, composed, output = self.exercise(set())
        self.assertEqual([22], restored)
        self.assertEqual(1, composed)
        self.assertTrue(output["publish_ready"])

    def test_bad_bundle_chooses_another_eligible_run(self):
        restored, composed, output = self.exercise({22})
        self.assertEqual([22, 21], restored)
        self.assertEqual(1, composed)
        self.assertTrue(output["publish_ready"])

    def test_no_bundle_waits_without_composition(self):
        restored, composed, output = self.exercise({22, 21})
        self.assertEqual([22, 21], restored)
        self.assertEqual(0, composed)
        self.assertFalse(output["publish_ready"])

    def test_real_release_check_failure_remains_terminal(self):
        restored, composed, _ = self.exercise(set(), composition_failure=True)
        self.assertEqual([22], restored)
        self.assertEqual(1, composed)


if __name__ == "__main__":
    unittest.main()

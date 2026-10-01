"""The required-check verdict over synthetic job results and detection outputs."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("ci_required.py")


def needs(detect="success", hits=None, **results):
    value = {"detect": {"result": detect, "outputs": {} if hits is None else {"hits": hits}}}
    value.update({name: {"result": result, "outputs": {}} for name, result in results.items()})
    return value


class CiRequiredTests(unittest.TestCase):
    def verdict(self, needs_value, hits):
        env = {key: value for key, value in os.environ.items() if key not in ("NEEDS", "HITS")}
        env.update(NEEDS=needs_value if isinstance(needs_value, str) else json.dumps(needs_value),
                   HITS=hits if isinstance(hits, str) else json.dumps(hits))
        return subprocess.run([sys.executable, str(SCRIPT)], cwd=tempfile.gettempdir(),
                              env=env, capture_output=True, text=True)

    def assert_red(self, result, message):
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("CI_REQUIRED_RED " + message, result.stdout)

    def assert_malformed(self, result, message):
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("CI_REQUIRED_ERROR", result.stderr)
        self.assertIn(message, result.stderr)

    def test_hit_units_succeeded_and_missed_units_skipped_is_green(self):
        hits = {"alpha": True, "beta": False}
        result = self.verdict(needs(alpha="success", beta="skipped"), hits)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("CI_REQUIRED unit=alpha hit=true result=success", result.stdout)
        self.assertIn("CI_REQUIRED unit=beta hit=false result=skipped", result.stdout)

    def test_every_unit_missed_is_green(self):
        result = self.verdict(needs(alpha="skipped", beta="skipped"), {"alpha": False, "beta": False})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_a_hit_unit_that_did_not_succeed_is_red(self):
        for outcome in ("failure", "cancelled", "skipped"):
            with self.subTest(outcome=outcome):
                result = self.verdict(needs(alpha=outcome, beta="success"), {"alpha": True, "beta": True})
                self.assert_red(result, f"unit=alpha hit=true result={outcome}")

    def test_a_missed_unit_that_ran_is_red(self):
        for outcome in ("success", "failure", "cancelled"):
            with self.subTest(outcome=outcome):
                result = self.verdict(needs(alpha=outcome), {"alpha": False})
                self.assert_red(result, f"unit=alpha hit=false result={outcome}")

    def test_detection_that_did_not_succeed_is_red(self):
        for outcome in ("failure", "cancelled", "skipped"):
            with self.subTest(outcome=outcome):
                result = self.verdict(needs(detect=outcome, alpha="skipped"), "")
                self.assert_red(result, f"detect result={outcome}")

    def test_a_job_without_a_unit_section_is_red(self):
        result = self.verdict(needs(alpha="success", stray="skipped"), {"alpha": True})
        self.assert_red(result, "job stray has no unit section")

    def test_a_unit_section_without_a_job_is_red(self):
        result = self.verdict(needs(alpha="success"), {"alpha": True, "orphan": False})
        self.assert_red(result, "unit orphan has no job in needs")

    def test_every_problem_is_reported(self):
        result = self.verdict(needs(alpha="failure", beta="success", stray="skipped"),
                              {"alpha": True, "beta": False, "orphan": True})
        self.assertEqual(result.returncode, 1)
        for message in ("unit=alpha hit=true result=failure", "unit=beta hit=false result=success",
                        "job stray has no unit section", "unit orphan has no job in needs"):
            self.assertIn("CI_REQUIRED_RED " + message, result.stdout)

    def test_malformed_inputs_fail(self):
        cases = [
            ("{", {"alpha": True}, "NEEDS"),
            ([], {"alpha": True}, "NEEDS"),
            ({"alpha": {"result": "success"}}, {"alpha": True}, "detect"),
            (needs(alpha={"result": "success"}), {"alpha": True}, "result"),
            (needs(alpha="success"), "{", "HITS"),
            (needs(alpha="success"), [], "HITS"),
            (needs(alpha="success"), {}, "HITS"),
            (needs(alpha="success"), {"alpha": "true"}, "HITS"),
        ]
        for needs_value, hits, message in cases:
            with self.subTest(needs=needs_value, hits=hits):
                self.assert_malformed(self.verdict(needs_value, hits), message)

    def test_missing_environment_fails(self):
        for missing in ("NEEDS", "HITS"):
            with self.subTest(missing=missing):
                env = dict(os.environ, NEEDS=json.dumps(needs(alpha="success")), HITS='{"alpha":true}')
                del env[missing]
                result = subprocess.run([sys.executable, str(SCRIPT)], env=env, capture_output=True, text=True)
                self.assert_malformed(result, missing)


if __name__ == "__main__":
    unittest.main()

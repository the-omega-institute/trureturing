#!/usr/bin/env python3
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "g5_check.py"


class G5CheckTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.package_root = pathlib.Path(self.temporary.name) / "sample-pkg"
        (self.package_root / "tests").mkdir(parents=True)
        self.add_test_file("tests/alpha_test.lua")
        self.report_path = pathlib.Path(self.temporary.name) / "report.json"

    def add_test_file(self, relative):
        path = self.package_root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("return {}\n", encoding="ascii")

    def entry(self, file="tests/alpha_test.lua", name="test_alpha", **changes):
        value = {
            "owner_namespace": "sample-pkg",
            "file": file,
            "name": name,
            "status": "pass",
        }
        value.update(changes)
        return value

    def report(self, tests=None, passed=None, failed=0, schema="fkst.test.report.v1"):
        tests = [self.entry()] if tests is None else tests
        return {
            "schema": schema,
            "summary": {
                "passed": len([test for test in tests if test.get("status") == "pass"])
                if passed is None
                else passed,
                "failed": failed,
            },
            "tests": tests,
        }

    def run_checker(self, report):
        if isinstance(report, str):
            self.report_path.write_text(report, encoding="utf-8")
        else:
            self.report_path.write_text(json.dumps(report), encoding="utf-8")
        return subprocess.run(
            [sys.executable, str(CHECKER), str(self.report_path), str(self.package_root)],
            check=False,
            capture_output=True,
            text=True,
        )

    def assert_rejected(self, report, message):
        result = self.run_checker(report)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(message, result.stderr)

    def test_rejects_empty_report(self):
        self.assert_rejected("", "G5:")

    def test_rejects_bad_schema(self):
        self.assert_rejected(self.report(schema="wrong"), "G5: unexpected test report schema")

    def test_rejects_summary_pass_count_mismatch(self):
        self.assert_rejected(
            self.report(passed=0),
            "G5: summary.passed does not match pass entry count",
        )

    def test_rejects_wrong_owner_namespace(self):
        self.assert_rejected(
            self.report(tests=[self.entry(owner_namespace="other-pkg")]),
            "G5: pass entry owner_namespace must be sample-pkg",
        )

    def test_rejects_missing_owner_namespace(self):
        entry = self.entry()
        del entry["owner_namespace"]
        self.assert_rejected(
            self.report(tests=[entry]),
            "G5: pass entry owner_namespace must be sample-pkg",
        )

    def test_rejects_missing_test_name(self):
        entry = self.entry()
        del entry["name"]
        self.assert_rejected(
            self.report(tests=[entry]),
            "G5: pass entry name must be a non-empty string",
        )

    def test_rejects_same_named_host_root_test(self):
        self.assert_rejected(
            self.report(tests=[self.entry(owner_namespace="host")]),
            "G5: pass entry owner_namespace must be sample-pkg",
        )

    def test_accepts_multiple_test_files(self):
        self.add_test_file("tests/beta_test.lua")
        result = self.run_checker(
            self.report(
                tests=[
                    self.entry(),
                    self.entry(file="tests/beta_test.lua", name="test_beta"),
                ]
            )
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("G5 coverage: 2/2", result.stdout)

    def test_rejects_missing_test_file_coverage(self):
        self.add_test_file("tests/beta_test.lua")
        self.assert_rejected(
            self.report(tests=[self.entry()]),
            "G5: test file coverage mismatch: "
            "missing=['tests/beta_test.lua'], extra=[]",
        )

    def test_rejects_duplicate_pass_identity_with_matching_summary(self):
        entry = self.entry()
        self.assert_rejected(
            self.report(tests=[entry, entry.copy()], passed=2),
            "G5: duplicate pass entry identity: "
            "('sample-pkg', 'tests/alpha_test.lua', 'test_alpha')",
        )

    def test_rejects_report_with_failed_test(self):
        self.assert_rejected(
            self.report(
                tests=[self.entry(status="fail")],
                passed=0,
                failed=1,
            ),
            "G5: summary.failed must be 0",
        )

    def test_rejects_illegal_status(self):
        self.assert_rejected(
            self.report(tests=[self.entry(status="unknown")], passed=0),
            "G5: test entry status must be pass or fail",
        )

    def test_accepts_valid_report(self):
        result = self.run_checker(self.report())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("G5 coverage: 1/1", result.stdout)


if __name__ == "__main__":
    unittest.main()

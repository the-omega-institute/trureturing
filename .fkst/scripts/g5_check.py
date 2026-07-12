#!/usr/bin/env python3
import json
import pathlib
import sys


SCHEMA = "fkst.test.report.v1"
LEGAL_STATUSES = {"pass", "fail"}


def fail(message):
    raise SystemExit(f"G5: {message}")


def nonnegative_integer(value, label):
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        fail(f"{label} must be a non-negative integer")
    return value


def load_report(report_path):
    try:
        with report_path.open(encoding="utf-8") as stream:
            report = json.load(stream)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        fail(f"could not read test report: {error}")
    if not isinstance(report, dict):
        fail("test report must be an object")
    return report


def enumerate_test_files(package_root):
    if not package_root.is_dir():
        fail(f"package root is not a directory: {package_root}")
    test_files = {
        path.relative_to(package_root).as_posix()
        for path in package_root.rglob("*_test.lua")
        if path.is_file()
    }
    if not test_files:
        fail("package contains no *_test.lua files")
    return test_files


def check(report_path, package_root):
    report = load_report(report_path)
    if report.get("schema") != SCHEMA:
        fail("unexpected test report schema")

    summary = report.get("summary")
    if not isinstance(summary, dict):
        fail("test report summary is missing")
    passed = nonnegative_integer(summary.get("passed"), "summary.passed")
    failed = nonnegative_integer(summary.get("failed"), "summary.failed")
    if failed != 0:
        fail(f"summary.failed must be 0, got {failed}")

    tests = report.get("tests")
    if not isinstance(tests, list):
        fail("test inventory is missing")

    expected_files = enumerate_test_files(package_root)
    expected_owner = package_root.name
    covered_files = set()
    identities = set()
    pass_count = 0
    fail_count = 0

    for index, entry in enumerate(tests):
        if not isinstance(entry, dict):
            fail(f"test entry {index} must be an object")
        status = entry.get("status")
        if status not in LEGAL_STATUSES:
            fail("test entry status must be pass or fail")
        if status == "fail":
            fail_count += 1
            continue

        owner = entry.get("owner_namespace")
        if owner != expected_owner:
            fail(f"pass entry owner_namespace must be {expected_owner}")
        file = entry.get("file")
        if not isinstance(file, str) or file not in expected_files:
            fail("pass entry file must be an enumerated package-relative *_test.lua path")
        name = entry.get("name")
        if not isinstance(name, str) or not name:
            fail("pass entry name must be a non-empty string")

        identity = (owner, file, name)
        if identity in identities:
            fail(f"duplicate pass entry identity: {identity!r}")
        identities.add(identity)
        covered_files.add(file)
        pass_count += 1

    if pass_count != passed:
        fail(
            "summary.passed does not match pass entry count: "
            f"summary={passed}, entries={pass_count}"
        )
    if fail_count != failed:
        fail(
            "summary.failed does not match fail entry count: "
            f"summary={failed}, entries={fail_count}"
        )
    if covered_files != expected_files:
        missing = sorted(expected_files - covered_files)
        extra = sorted(covered_files - expected_files)
        fail(f"test file coverage mismatch: missing={missing}, extra={extra}")

    print(
        f"G5 coverage: {len(covered_files)}/{len(expected_files)} "
        f"*_test.lua files covered; summary {passed} passed, {failed} failed"
    )


def main(argv):
    if len(argv) != 3:
        fail("usage: g5_check.py REPORT PACKAGE_ROOT")
    check(pathlib.Path(argv[1]), pathlib.Path(argv[2]))


if __name__ == "__main__":
    main(sys.argv)

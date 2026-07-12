#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly PACKAGE_ROOT="$ROOT/packages/harness-probe"
readonly FALLBACK_BIN="/Users/auric/fkst-substrate/target/debug/fkst-framework"
temporary=""

die() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

warn() {
  printf 'warning: %s\n' "$*" >&2
}

cleanup() {
  if [[ -n "${temporary:-}" ]]; then
    rm -rf -- "$temporary"
  fi
}

check_layer() {
  local required=(
    "substrate-ref"
    "env.example"
    "fkst.workspace.toml"
    "run.sh"
    "packages/harness-probe/fkst.toml"
    "packages/harness-probe/raisers/development_request.lua"
    "packages/harness-probe/departments/preflight/main.lua"
    "packages/harness-probe/tests/preflight_test.lua"
  )
  local relative
  for relative in "${required[@]}"; do
    [[ -f "$ROOT/$relative" && ! -L "$ROOT/$relative" ]] \
      || die "required regular file is missing: $relative"
  done

  python3 - "$ROOT" <<'PY'
import pathlib
import re
import sys
import tomllib

root = pathlib.Path(sys.argv[1])
package_root = root / "packages" / "harness-probe"

pin_lines = (root / "substrate-ref").read_text(encoding="ascii").splitlines()
if len(pin_lines) != 1 or re.fullmatch(r"[0-9a-fA-F]{40}", pin_lines[0]) is None:
    raise SystemExit("substrate-ref must contain exactly one 40-digit hexadecimal SHA")

with (root / "fkst.workspace.toml").open("rb") as stream:
    workspace = tomllib.load(stream)
expected_workspace = {"workspace": {"units": ["packages/harness-probe"]}}
if workspace != expected_workspace:
    raise SystemExit("fkst.workspace.toml must discover only packages/harness-probe")

with (package_root / "fkst.toml").open("rb") as stream:
    manifest = tomllib.load(stream)
expected_manifest = {
    "kind": "package",
    "name": "harness-probe",
    "persistence_class": "stateless_adapter",
    "code": {"root": "."},
    "lib_deps": {"libraries": []},
}
if manifest != expected_manifest:
    raise SystemExit("harness-probe fkst.toml does not match the pinned package contract")

expected_files = {
    "fkst.toml",
    "raisers/development_request.lua",
    "departments/preflight/main.lua",
    "tests/preflight_test.lua",
}
expected_directories = {
    "raisers",
    "departments",
    "departments/preflight",
    "tests",
}
actual_files = set()
actual_directories = set()
for path in package_root.rglob("*"):
    if path.is_symlink():
        raise SystemExit(f"package structure contains a symlink: {path.relative_to(package_root)}")
    if path.is_file():
        actual_files.add(path.relative_to(package_root).as_posix())
    elif path.is_dir():
        actual_directories.add(path.relative_to(package_root).as_posix())
if actual_files != expected_files:
    missing = sorted(expected_files - actual_files)
    extra = sorted(actual_files - expected_files)
    raise SystemExit(f"package file closure mismatch: missing={missing}, extra={extra}")
if actual_directories != expected_directories:
    missing = sorted(expected_directories - actual_directories)
    extra = sorted(actual_directories - expected_directories)
    raise SystemExit(f"package directory closure mismatch: missing={missing}, extra={extra}")
PY

  printf 'fkst check: ok\n'
}

verify_provenance() {
  local bin="$1"
  local physical_bin pin checkout head
  physical_bin="$(python3 - "$bin" <<'PY'
import os
import sys

print(os.path.realpath(sys.argv[1]))
PY
)"
  pin="$(<"$ROOT/substrate-ref")"

  if checkout="$(git -C "$(dirname -- "$physical_bin")" rev-parse --show-toplevel 2>/dev/null)"; then
    head="$(git -C "$checkout" rev-parse HEAD 2>/dev/null)" \
      || die "could not read engine checkout HEAD: $checkout"
    if [[ "$head" != "$pin" ]]; then
      if [[ "${FKST_ALLOW_PIN_MISMATCH:-0}" == "1" ]]; then
        warn "engine checkout HEAD $head does not match pin $pin; explicitly allowed"
      else
        die "engine checkout HEAD $head does not match pin $pin"
      fi
    fi
    printf 'fkst provenance: verified %s at %s\n' "$head" "$checkout"
  else
    warn "engine provenance-unverified for physical path: $physical_bin"
  fi
}

check_g5_coverage() {
  local report="$1"
  python3 - "$report" "$PACKAGE_ROOT" <<'PY'
import json
import pathlib
import sys

report_path = pathlib.Path(sys.argv[1])
package_root = pathlib.Path(sys.argv[2])
with report_path.open(encoding="utf-8") as stream:
    report = json.load(stream)

if report.get("schema") != "fkst.test.report.v1":
    raise SystemExit("G5: unexpected test report schema")
summary = report.get("summary")
if not isinstance(summary, dict):
    raise SystemExit("G5: test report summary is missing")
passed = summary.get("passed")
failed = summary.get("failed")
if isinstance(passed, bool) or not isinstance(passed, int):
    raise SystemExit("G5: summary.passed must be an integer")
if isinstance(failed, bool) or not isinstance(failed, int) or failed != 0:
    raise SystemExit(f"G5: summary.failed must be 0, got {failed!r}")
tests = report.get("tests")
if not isinstance(tests, list):
    raise SystemExit("G5: test inventory is missing")

test_files = sorted(
    path.relative_to(package_root).as_posix()
    for path in package_root.rglob("*_test.lua")
    if path.is_file()
)
if not test_files:
    raise SystemExit("G5: package contains no *_test.lua files")
uncovered = [
    test_file
    for test_file in test_files
    if not any(
        entry.get("file") == test_file and entry.get("status") == "pass"
        for entry in tests
        if isinstance(entry, dict)
    )
]
if uncovered:
    raise SystemExit(f"G5: no passing test reported for {uncovered}")

print(
    f"G5 coverage: {len(test_files)}/{len(test_files)} *_test.lua files covered; "
    f"summary {passed} passed, {failed} failed"
)
PY
}

run_test() {
  check_layer

  local bin="${BIN:-$FALLBACK_BIN}"
  [[ -f "$bin" && -x "$bin" ]] || die "BIN is not an executable regular file: $bin"
  verify_provenance "$bin"

  local report
  temporary="$(mktemp -d "${TMPDIR:-/tmp}/fkst-m1.XXXXXX")"
  trap cleanup EXIT
  report="$temporary/test-report.json"
  export FKST_RUNTIME_ROOT="$temporary/runtime"

  "$bin" --self-test
  "$bin" conformance \
    --project-root "$ROOT" \
    --package-root "$PACKAGE_ROOT"
  "$bin" test \
    --project-root "$ROOT" \
    --package-root "$PACKAGE_ROOT" \
    --report-json "$report"
  check_g5_coverage "$report"
  printf 'fkst test: ok\n'
}

[[ $# -eq 1 ]] || die "usage: $0 check|test"
case "$1" in
  check)
    check_layer
    ;;
  test)
    run_test
    ;;
  *)
    die "usage: $0 check|test"
    ;;
esac

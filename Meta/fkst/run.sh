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
    "g5_check.py"
    "run.sh"
    "tests/g5_check_test.py"
    "tests/provenance_test.sh"
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
  local physical_bin pin discovered_checkout checkout head
  local worktree_list line candidate registered
  local clean_git=(
    env
    -u GIT_DIR
    -u GIT_WORK_TREE
    -u GIT_INDEX_FILE
    -u GIT_COMMON_DIR
    -u GIT_OBJECT_DIRECTORY
    -u GIT_ALTERNATE_OBJECT_DIRECTORIES
    git
  )
  physical_bin="$(python3 - "$bin" <<'PY'
import os
import sys

print(os.path.realpath(sys.argv[1]))
PY
)"
  pin="$(<"$ROOT/substrate-ref")"

  discovered_checkout="$(
    "${clean_git[@]}" \
      -C "$(dirname -- "$physical_bin")" \
      rev-parse --show-toplevel 2>/dev/null
  )" \
    || die "engine provenance-unverified: physical BIN is not inside a git checkout: $physical_bin"
  checkout="$(python3 - "$discovered_checkout" <<'PY'
import os
import sys

print(os.path.realpath(sys.argv[1]))
PY
)"
  if ! python3 - "$(dirname -- "$physical_bin")" "$checkout" <<'PY'
import os
import sys

bin_directory, checkout = sys.argv[1:]
try:
    inside_checkout = os.path.commonpath((bin_directory, checkout)) == checkout
except ValueError:
    inside_checkout = False
raise SystemExit(0 if inside_checkout else 1)
PY
  then
    die "engine provenance-unverified: BIN is not inside the pinned checkout: $physical_bin"
  fi

  worktree_list="$(
    "${clean_git[@]}" -C "$checkout" worktree list --porcelain 2>/dev/null
  )" || die "could not read registered engine worktrees: $checkout"
  registered=""
  while IFS= read -r line; do
    [[ "$line" == worktree\ * ]] || continue
    candidate="$(python3 - "${line#worktree }" <<'PY'
import os
import sys

print(os.path.realpath(sys.argv[1]))
PY
)"
    if [[ "$candidate" == "$checkout" ]]; then
      registered=1
      break
    fi
  done <<<"$worktree_list"
  [[ -n "$registered" ]] \
    || die "engine provenance-unverified: checkout is not a registered worktree: $checkout"

  head="$("${clean_git[@]}" -C "$checkout" rev-parse HEAD 2>/dev/null)" \
    || die "could not read engine checkout HEAD: $checkout"
  [[ "$head" == "$pin" ]] \
    || die "engine checkout HEAD $head does not match pin $pin"
  printf 'fkst provenance: verified %s at %s\n' "$head" "$checkout"
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
  mkdir "$temporary/sub"
  export TMPDIR="$temporary/sub"

  "$bin" --self-test
  "$bin" conformance \
    --project-root "$ROOT" \
    --package-root "$PACKAGE_ROOT"
  "$bin" test \
    --project-root "$ROOT" \
    --package-root "$PACKAGE_ROOT" \
    --report-json "$report"
  python3 "$ROOT/g5_check.py" "$report" "$PACKAGE_ROOT"
  printf 'fkst test: ok\n'
}

[[ $# -eq 1 ]] || die "usage: $0 check|test"
case "$1" in
  check)
    check_layer
    python3 "$ROOT/tests/g5_check_test.py"
    bash "$ROOT/tests/provenance_test.sh"
    ;;
  test)
    run_test
    ;;
  *)
    die "usage: $0 check|test"
    ;;
esac

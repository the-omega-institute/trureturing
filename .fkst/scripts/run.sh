#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
readonly PACKAGE_ROOT="$ROOT/local-packages/harness-probe"
readonly PLATFORM_PACKAGES="github-proxy consensus github-devloop github-devloop-pr github-devloop-intake github-devloop-decompose github-devloop-intake-default"
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

resolve_bin() {
  local selected="" repo_root primary_worktree
  if [[ -n "${BIN:-}" ]]; then
    selected="$BIN"
  elif [[ -f "$ROOT/env" ]]; then
    selected="$(bash -c 'source "$1"; printf "%s" "${BIN:-}"' bash "$ROOT/env")" \
      || die "could not load BIN from $ROOT/env"
    [[ -n "$selected" ]] || die "$ROOT/env does not set a non-empty BIN"
  elif command -v fkst-framework >/dev/null 2>&1; then
    selected="$(command -v fkst-framework)"
  else
    repo_root="$(cd -- "$ROOT/.." && pwd -P)"
    primary_worktree="$(
      git -C "$repo_root" worktree list --porcelain 2>/dev/null \
        | awk '/^worktree / { sub(/^worktree /, ""); print; exit }'
    )"
    if [[ -n "$primary_worktree" ]]; then
      selected="$(dirname -- "$primary_worktree")/fkst-substrate/target/debug/fkst-framework"
    else
      selected="$ROOT/../../fkst-substrate/target/debug/fkst-framework"
    fi
  fi
  [[ -f "$selected" && -x "$selected" ]] \
    || die "BIN is not an executable regular file: $selected"
  printf '%s\n' "$selected"
}

check_layer() {
  local required=(
    "substrate-ref"
    "env.example"
    "fkst.workspace.toml"
    "scripts/g5_check.py"
    "scripts/run.sh"
    "tests/g5_check_test.py"
    "tests/host_contract_test.sh"
    "tests/provenance_test.sh"
    "local-packages/harness-probe/fkst.toml"
    "local-packages/harness-probe/raisers/development_request.lua"
    "local-packages/harness-probe/departments/preflight/main.lua"
    "local-packages/harness-probe/tests/preflight_test.lua"
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
package_root = root / "local-packages" / "harness-probe"

pin_lines = (root / "substrate-ref").read_text(encoding="ascii").splitlines()
if len(pin_lines) != 1 or re.fullmatch(r"[0-9a-fA-F]{40}", pin_lines[0]) is None:
    raise SystemExit("substrate-ref must contain exactly one 40-digit hexadecimal SHA")

with (root / "fkst.workspace.toml").open("rb") as stream:
    workspace = tomllib.load(stream)
expected_workspace = {
    "workspace": {"units": ["local-packages/*"]},
    "external_sources": [{
        "id": "fkst-packages-platform",
        "git": "https://github.com/ChronoAIProject/fkst-packages.git",
        "rev": "9090b5dea4ffad6ff3f0cad4a0cf7b5fcf93d549",
        "packages": [
            "github-proxy",
            "consensus",
            "github-devloop",
            "github-devloop-pr",
            "github-devloop-intake",
            "github-devloop-decompose",
            "github-devloop-intake-default",
        ],
        "libraries": ["contract", "workflow", "testkit", "forge", "devloop"],
    }],
}
if workspace != expected_workspace:
    raise SystemExit("fkst.workspace.toml does not match the pinned host composition")

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

  local bin
  bin="$(resolve_bin)"
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
  python3 "$ROOT/scripts/g5_check.py" "$report" "$PACKAGE_ROOT"
  printf 'fkst test: ok\n'
}

run_supervise() {
  local platform_root="${FKST_PLATFORM_ROOT:-}"
  local durable_root="${FKST_DURABLE_ROOT:-}"
  local runtime_root="" restart=0
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --runtime-root)
        [[ $# -ge 2 ]] || die "--runtime-root requires a path"
        runtime_root="$2"
        shift 2
        ;;
      --restart)
        restart=1
        shift
        ;;
      *) die "usage: $0 supervise [--runtime-root <scratch>] [--restart]" ;;
    esac
  done
  [[ -n "$platform_root" ]] || die "FKST_PLATFORM_ROOT is required for supervise"
  [[ -x "$platform_root/scripts/run.sh" ]] \
    || die "platform runner is not executable: $platform_root/scripts/run.sh"
  [[ -n "$durable_root" ]] || die "FKST_DURABLE_ROOT is required for supervise"

  BIN="$(resolve_bin)"
  export BIN
  unset FKST_GITHUB_WRITE
  local args=(
    "$platform_root/scripts/run.sh" supervise
    --project-root "$ROOT"
    --platform-root "$platform_root"
    --platform-packages "$PLATFORM_PACKAGES"
    --local-packages "$ROOT/local-packages"
    --host-packages trureturing-devtask
    --durable-root "$durable_root"
  )
  [[ -z "$runtime_root" ]] || args+=(--runtime-root "$runtime_root")
  [[ "$restart" -eq 0 ]] || args+=(--restart)
  exec "${args[@]}"
}

[[ $# -ge 1 ]] || die "usage: $0 check|test|supervise"
readonly command="$1"
shift
case "$command" in
  check)
    [[ $# -eq 0 ]] || die "usage: $0 check"
    check_layer
    python3 "$ROOT/tests/g5_check_test.py"
    resolved_bin="$(resolve_bin)"
    BIN="$resolved_bin" bash "$ROOT/tests/provenance_test.sh"
    bash "$ROOT/tests/host_contract_test.sh"
    ;;
  test)
    [[ $# -eq 0 ]] || die "usage: $0 test"
    run_test
    ;;
  supervise)
    run_supervise "$@"
    ;;
  *)
    die "usage: $0 check|test|supervise"
    ;;
esac

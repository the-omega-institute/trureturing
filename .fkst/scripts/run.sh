#!/usr/bin/env bash
set -euo pipefail

readonly FKST_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
readonly REPO_ROOT="$(cd -- "$FKST_ROOT/.." && pwd -P)"
readonly OPERATE_ROOT="${FKST_OPERATE_ROOT:-$HOME/.fkst/trureturing}"
readonly ENV_FILE="$OPERATE_ROOT/host.env"
readonly LOG_DIR="$OPERATE_ROOT/logs"
readonly PLATFORM_PACKAGES="github-proxy consensus github-devloop github-devloop-pr github-devloop-integration github-devloop-intake github-devloop-intake-default github-devloop-workflow github-devloop-decompose github-devloop-ops github-external-pr-intake idle-detector archaudit"
readonly HOST_PACKAGES="theory-selfgrowth"
readonly SUBSTRATE_URL="https://github.com/ChronoAIProject/fkst-substrate.git"
readonly PLATFORM_URL="https://github.com/ChronoAIProject/fkst-packages.git"

die() {
  printf 'fkst: %s\n' "$*" >&2
  exit 1
}

ensure_host_env() {
  mkdir -p "$OPERATE_ROOT/durable" "$OPERATE_ROOT/runtime" "$LOG_DIR" "$HOME/.fkst/rate-pools"
  [[ -f "$ENV_FILE" ]] \
    || die "host.env is missing; follow docs/devloop/fkst-host-bringup.md"
}

load_host_env() {
  ensure_host_env
  set -a
  # shellcheck disable=SC1090
  source "$ENV_FILE"
  set +a
  # host.env supplies machine paths and identity; the sourced versioned deploy.env
  # supplies repository behavior such as GitHub write posture.
  [[ -x "${BIN:-}" ]] || die "host.env BIN is not executable: ${BIN:-<unset>}"
  [[ -x "${FKST_PLATFORM_ROOT:-}/scripts/run.sh" ]] \
    || die "host.env FKST_PLATFORM_ROOT is invalid: ${FKST_PLATFORM_ROOT:-<unset>}"
  [[ "${FKST_GITHUB_REPO:-}" == "the-omega-institute/trureturing" ]] \
    || die "host.env targets unexpected repository: ${FKST_GITHUB_REPO:-<unset>}"
}

pid_file() {
  printf '%s/.fkst-supervise.pid\n' "$OPERATE_ROOT/durable"
}

read_live_pid() {
  local file pid
  file="$(pid_file)"
  [[ -f "$file" ]] || return 1
  pid="$(sed -n '1p' "$file")"
  [[ "$pid" =~ ^[0-9]+$ ]] || return 1
  kill -0 "$pid" 2>/dev/null || return 1
  printf '%s\n' "$pid"
}

start() {
  local checkout_root log pid
  load_host_env
  checkout_root="${FKST_HOST_ROOT:-$OPERATE_ROOT/checkout}"
  [[ -d "$checkout_root" ]] || die "dedicated checkout does not exist: $checkout_root"
  test -e "$checkout_root/.git" || die "dedicated checkout is not a git checkout: $checkout_root"
  checkout_root="$(cd -- "$checkout_root" && pwd -P)"
  [[ "$checkout_root" != "$REPO_ROOT" ]] \
    || die "dedicated checkout must not be the source worktree: $checkout_root"
  load_lua_test_contract "$checkout_root/.fkst"
  validate_platform_composition
  # The platform resolves fkst.workspace.toml and fkst.lock at the project
  # root; the repo keeps them under .fkst/ (single source). Provision root
  # copies into the dedicated checkout (host state, reconstructible from the
  # repository alone) and keep them out of the checkout's git status.
  cp "$checkout_root/.fkst/fkst.workspace.toml" "$checkout_root/fkst.workspace.toml"
  cp "$checkout_root/.fkst/fkst.lock" "$checkout_root/fkst.lock"
  if [[ -d "$checkout_root/.git/info" ]]; then
    grep -qxF '/fkst.workspace.toml' "$checkout_root/.git/info/exclude" 2>/dev/null \
      || printf '/fkst.workspace.toml\n/fkst.lock\n' >>"$checkout_root/.git/info/exclude"
  fi
  log="$LOG_DIR/supervise-$(date -u +%Y%m%dT%H%M%SZ).log"
  ln -sfn "$(basename -- "$log")" "$LOG_DIR/latest.log"
  (
    cd -- "$checkout_root"
    exec nohup bash "$FKST_PLATFORM_ROOT/scripts/run.sh" supervise \
      --project-root "$checkout_root" \
      --platform-root "$FKST_PLATFORM_ROOT" \
      --platform-packages "$PLATFORM_PACKAGES" \
      --host-packages "$HOST_PACKAGES" \
      --local-packages "$checkout_root/packages" \
      --durable-root "$FKST_DURABLE_ROOT" \
      --runtime-root "$FKST_RUNTIME_ROOT" \
      --restart
  ) >>"$log" 2>&1 &
  pid=$!
  sleep 2
  if ! kill -0 "$pid" 2>/dev/null; then
    wait "$pid" || true
    die "supervise exited during startup; see $log"
  fi
  printf 'fkst: started pid %s; log %s\n' "$pid" "$log"
}

stop() {
  local pid attempts=0 file
  ensure_host_env
  file="$(pid_file)"
  if ! pid="$(read_live_pid)"; then
    rm -f "$file"
    printf 'fkst: stopped\n'
    return
  fi
  kill "$pid" 2>/dev/null || true
  while kill -0 "$pid" 2>/dev/null && [[ "$attempts" -lt 50 ]]; do
    sleep 0.1
    attempts=$((attempts + 1))
  done
  if kill -0 "$pid" 2>/dev/null; then
    kill -9 "$pid" 2>/dev/null || true
    printf 'fkst: forced stop pid %s\n' "$pid"
  else
    printf 'fkst: stopped pid %s\n' "$pid"
  fi
  rm -f "$file"
}

status() {
  local pid
  ensure_host_env
  if pid="$(read_live_pid)"; then
    printf 'fkst: running pid %s\n' "$pid"
    return 0
  fi
  printf 'fkst: stopped\n'
  return 1
}

logs() {
  ensure_host_env
  [[ -e "$LOG_DIR/latest.log" ]] || die "no supervise log exists"
  tail -n "${LINES:-120}" "$LOG_DIR/latest.log"
}

verify_source_checkout() {
  local label="$1" root="$2" pin="$3" head dirty
  [[ -d "$root" ]] || die "$label checkout does not exist: $root"
  git -C "$root" rev-parse --is-inside-work-tree >/dev/null 2>&1 \
    || die "$label source is not a git checkout: $root"
  head="$(git -C "$root" rev-parse HEAD 2>/dev/null)" \
    || die "cannot read $label checkout HEAD: $root"
  [[ "$head" == "$pin" ]] \
    || die "$label checkout HEAD mismatch: expected $pin, got $head"
  dirty="$(git -C "$root" status --porcelain --untracked-files=normal 2>/dev/null)" \
    || die "cannot inspect $label checkout status: $root"
  [[ -z "$dirty" ]] || die "$label checkout is dirty: $root"
  printf '%s\n' "$root"
}

materialize_pinned_source() {
  local label="$1" url="$2" pin="$3" override="$4" destination="$5"
  local cache_root object_source
  if [[ -n "$override" ]]; then
    object_source="$(verify_source_checkout "$label" "$override" "$pin")"
  else
    cache_root="${FKST_CACHE_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/fkst-lua-gate}"
    mkdir -p "$cache_root" || die "cannot create fkst cache root: $cache_root"
    object_source="$cache_root/$label-$pin"
    if [[ ! -e "$object_source" ]]; then
      printf 'fkst: cloning %s at %s\n' "$label" "$pin" >&2
      git clone --no-checkout "$url" "$object_source" \
        || die "failed to clone pinned $label source"
      git -C "$object_source" checkout --detach "$pin" \
        || die "failed to checkout $label pin $pin"
    fi
    object_source="$(verify_source_checkout "$label" "$object_source" "$pin")"
  fi

  [[ ! -e "$destination" ]] || die "$label archive destination already exists: $destination"
  mkdir -p "$destination" || die "cannot create $label archive destination: $destination"
  git -C "$object_source" cat-file -e "$pin^{commit}" 2>/dev/null \
    || die "$label source does not contain pinned commit: $pin"
  LC_ALL=C git -C "$object_source" archive --format=tar "$pin" \
    | LC_ALL=C tar -xf - -C "$destination" \
    || die "failed to materialize $label from pinned commit $pin"
  printf '%s\n' "$destination"
}

load_lua_test_contract() {
  local contract_root="${1:-$FKST_ROOT}"
  local substrate_file="$contract_root/substrate-ref" lock_file="$contract_root/fkst.lock"
  local workspace_file="$contract_root/fkst.workspace.toml" data
  [[ -s "$substrate_file" ]] || die "missing substrate pin: $substrate_file"
  [[ -s "$lock_file" ]] || die "missing platform lock: $lock_file"
  [[ -s "$workspace_file" ]] || die "missing workspace manifest: $workspace_file"
  SUBSTRATE_PIN="$(tr -d '\r\n' < "$substrate_file")"
  [[ "$SUBSTRATE_PIN" =~ ^[0-9a-f]{40}$ ]] \
    || die "substrate-ref must contain one 40-character lowercase SHA"
  [[ "$(grep -Ec '^[0-9a-f]{40}$' "$substrate_file")" -eq 1 ]] \
    || die "substrate-ref must contain exactly one pin"

  data="$(python3 - "$lock_file" "$workspace_file" "$PLATFORM_URL" <<'PY'
import re
import sys
import tomllib
from pathlib import Path

lock_path = Path(sys.argv[1])
workspace_path = Path(sys.argv[2])
expected_url = sys.argv[3]

def load(path):
    try:
        with path.open("rb") as handle:
            return tomllib.load(handle)
    except Exception as exc:
        raise SystemExit(f"cannot parse {path}: {exc}")

lock = load(lock_path)
workspace = load(workspace_path)
sources = [item for item in lock.get("external_source", []) if item.get("id") == "fkst-packages-platform"]
if len(sources) != 1:
    raise SystemExit("fkst.lock must contain exactly one fkst-packages-platform source")
source = sources[0]
if source.get("git") != expected_url:
    raise SystemExit("fkst.lock platform source URL mismatch")
intent = source.get("intent", {}).get("rev")
resolved = source.get("resolved", {}).get("rev")
if not isinstance(resolved, str) or re.fullmatch(r"[0-9a-f]{40}", resolved) is None:
    raise SystemExit("fkst.lock resolved platform rev must be a 40-character lowercase SHA")
if intent != resolved:
    raise SystemExit("fkst.lock intent and resolved platform revisions differ")

workspace_sources = [item for item in workspace.get("external_sources", []) if item.get("id") == "fkst-packages-platform"]
if len(workspace_sources) != 1:
    raise SystemExit("fkst.workspace.toml must contain exactly one fkst-packages-platform source")
workspace_source = workspace_sources[0]
if workspace_source.get("git") != expected_url or workspace_source.get("rev") != resolved:
    raise SystemExit("workspace platform source does not match the resolved lock revision")
packages = workspace_source.get("packages")
libraries = workspace_source.get("libraries")
if not isinstance(packages, list) or not packages or any(not isinstance(value, str) or not value for value in packages):
    raise SystemExit("workspace platform package list is missing or invalid")
if len(packages) != len(set(packages)):
    raise SystemExit("workspace platform package list contains duplicates")
if not isinstance(libraries, list) or not libraries or any(not isinstance(value, str) or not value for value in libraries):
    raise SystemExit("workspace platform library list is missing or invalid")
locked_libraries = [item.get("name") for item in source.get("libraries", [])]
if sorted(locked_libraries) != sorted(libraries):
    raise SystemExit("workspace platform libraries do not match fkst.lock")
print(resolved)
print(" ".join(packages))
print(" ".join(libraries))
PY
)" || die "invalid fkst platform lock contract"
  PLATFORM_PIN="$(printf '%s\n' "$data" | sed -n '1p')"
  PLATFORM_PACKAGE_NAMES="$(printf '%s\n' "$data" | sed -n '2p')"
  PLATFORM_LIBRARY_NAMES="$(printf '%s\n' "$data" | sed -n '3p')"
  [[ "$PLATFORM_PIN" =~ ^[0-9a-f]{40}$ ]] || die "platform pin parser returned an invalid SHA"
}

validate_platform_composition() {
  # The requested composition (PLATFORM_PACKAGES above) and the declared one
  # (fkst.workspace.toml packages, loaded into PLATFORM_PACKAGE_NAMES) must be
  # the same set. A package present in only one list is silent composition
  # drift: the 64736bd pin bump dropped archaudit from the manifest while
  # run.sh kept requesting it, and the divergence stayed latent until the next
  # supervise start refused to boot.
  local requested declared
  requested="$(tr ' ' '\n' <<<"$PLATFORM_PACKAGES" | LC_ALL=C sort)"
  declared="$(tr ' ' '\n' <<<"$PLATFORM_PACKAGE_NAMES" | LC_ALL=C sort)"
  [[ "$requested" == "$declared" ]] || die "platform composition drift: run.sh requests [$PLATFORM_PACKAGES] but fkst.workspace.toml declares [$PLATFORM_PACKAGE_NAMES]"
}

load_target_packages() {
  local data name path
  data="$(python3 - "$REPO_ROOT/packages" <<'PY'
import sys
import tomllib
from pathlib import Path

root = Path(sys.argv[1])
rows = []
for manifest in sorted(root.glob("*/fkst.toml")):
    try:
        with manifest.open("rb") as handle:
            value = tomllib.load(handle)
    except Exception as exc:
        raise SystemExit(f"cannot parse {manifest}: {exc}")
    name = value.get("name")
    if value.get("kind") != "package" or name != manifest.parent.name:
        raise SystemExit(f"invalid target package manifest identity: {manifest}")
    rows.append((name, manifest.parent))
if not rows:
    raise SystemExit("no target packages found under packages/")
for name, path in rows:
    print(f"{name}\t{path}")
PY
)" || die "cannot load target packages"
  TARGET_PACKAGE_NAMES=()
  TARGET_PACKAGE_ROOTS=()
  while IFS=$'\t' read -r name path; do
    [[ -n "$name" && -n "$path" ]] || continue
    TARGET_PACKAGE_NAMES+=("$name")
    TARGET_PACKAGE_ROOTS+=("$path")
  done <<< "$data"
  [[ "${#TARGET_PACKAGE_NAMES[@]}" -gt 0 ]] || die "target package set is empty"
}

copy_tree() {
  local source="$1" destination="$2"
  mkdir -p "$destination"
  (cd "$source" && LC_ALL=C tar -cf - .) | (cd "$destination" && LC_ALL=C tar xf -)
}

copy_target_tree() {
  local source="$1" destination="$2" mode="$3" test_file
  mkdir -p "$destination"
  case "$mode" in
    full)
      copy_tree "$source" "$destination"
      ;;
    normal)
      (cd "$source" && LC_ALL=C tar --exclude './tests/run_graph*_test.lua' -cf - .) \
        | (cd "$destination" && LC_ALL=C tar xf -)
      ;;
    graph)
      (cd "$source" && LC_ALL=C tar --exclude './tests' --exclude './departments/test_*' -cf - .) \
        | (cd "$destination" && LC_ALL=C tar xf -)
      for test_file in "$source"/tests/run_graph*_test.lua; do
        [[ -f "$test_file" ]] || continue
        mkdir -p "$destination/tests"
        cp "$test_file" "$destination/tests/"
      done
      ;;
    *) die "unknown target copy mode: $mode" ;;
  esac
}

prepare_test_graph() {
  local destination="$1" mode="$2" platform_root="$3" index name source library
  mkdir -p "$destination/packages" "$destination/libraries"
  [[ -s "$platform_root/fkst.workspace.toml" ]] \
    || die "platform source is missing fkst.workspace.toml"
  cp "$platform_root/fkst.workspace.toml" "$destination/fkst.workspace.toml"

  for library in "$platform_root"/libraries/*; do
    [[ -d "$library" && -s "$library/fkst.toml" ]] || continue
    copy_tree "$library" "$destination/libraries/$(basename "$library")"
  done
  for name in $PLATFORM_LIBRARY_NAMES; do
    [[ -s "$destination/libraries/$name/fkst.toml" ]] \
      || die "locked platform library is missing: $name"
  done

  if [[ "$mode" != "normal" ]]; then
    for name in $PLATFORM_PACKAGE_NAMES; do
      source="$platform_root/packages/$name"
      [[ -s "$source/fkst.toml" ]] || die "declared platform package is missing: $name"
      if [[ "$mode" == "graph" ]]; then
        mkdir -p "$destination/packages/$name"
        (cd "$source" && LC_ALL=C tar --exclude './tests' --exclude './departments/test_*' -cf - .) \
          | (cd "$destination/packages/$name" && LC_ALL=C tar xf -)
      else
        copy_tree "$source" "$destination/packages/$name"
      fi
    done
  fi

  for ((index = 0; index < ${#TARGET_PACKAGE_NAMES[@]}; index++)); do
    name="${TARGET_PACKAGE_NAMES[$index]}"
    source="${TARGET_PACKAGE_ROOTS[$index]}"
    [[ ! -e "$destination/packages/$name" ]] \
      || die "target package collides with platform package: $name"
    copy_target_tree "$source" "$destination/packages/$name" "$mode"
  done
}

package_root_args() {
  local graph_root="$1" include_platform="$2" name
  PACKAGE_ROOT_ARGS=()
  for name in "${TARGET_PACKAGE_NAMES[@]}"; do
    PACKAGE_ROOT_ARGS+=(--package-root "$graph_root/packages/$name")
  done
  if [[ "$include_platform" == 1 ]]; then
    for name in $PLATFORM_PACKAGE_NAMES; do
      PACKAGE_ROOT_ARGS+=(--package-root "$graph_root/packages/$name")
    done
  fi
}

validate_test_reports() {
  local normal_report="$1" graph_report="$2" repository_root="${3:-$REPO_ROOT}"
  python3 - "$repository_root" "$normal_report" "$graph_report" <<'PY'
import json
import sys
from pathlib import Path

repo = Path(sys.argv[1])
reports = [Path(sys.argv[2]), Path(sys.argv[3])]
observed = set()
for report_path in reports:
    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
    except Exception as exc:
        raise SystemExit(f"invalid test report JSON {report_path}: {exc}")
    if report.get("schema") != "fkst.test.report.v1":
        raise SystemExit(f"bad test report schema in {report_path}: {report.get('schema')!r}")
    summary = report.get("summary")
    tests = report.get("tests")
    if not isinstance(summary, dict) or not isinstance(tests, list):
        raise SystemExit(f"missing summary/tests in {report_path}")
    passed = summary.get("passed")
    failed = summary.get("failed")
    if not isinstance(passed, int) or isinstance(passed, bool) or passed <= 0:
        raise SystemExit(f"test report must have passed > 0: {report_path}")
    if not isinstance(failed, int) or isinstance(failed, bool) or failed != 0:
        raise SystemExit(f"test report must have failed = 0: {report_path}")
    pass_rows = 0
    for test in tests:
        if not isinstance(test, dict):
            raise SystemExit(f"non-object test row in {report_path}")
        if test.get("status") != "pass":
            raise SystemExit(f"non-passing test row in {report_path}: {test!r}")
        owner = test.get("owner_namespace")
        file_name = test.get("file")
        name = test.get("name")
        if not all(isinstance(value, str) and value for value in (owner, file_name, name)):
            raise SystemExit(f"malformed test row in {report_path}: {test!r}")
        pass_rows += 1
        observed.add(f"packages/{owner}/{file_name}")
    if pass_rows != passed:
        raise SystemExit(f"summary/test row mismatch in {report_path}: passed={passed}, rows={pass_rows}")

expected = set()
for package in sorted((repo / "packages").iterdir()):
    if not package.is_dir():
        continue
    for test_file in package.rglob("*_test.lua"):
        relative = test_file.relative_to(package)
        if relative.parts[0] == "tests" or relative.parts[0] == "departments":
            expected.add(f"packages/{package.name}/{relative.as_posix()}")
missing = sorted(expected - observed)
if missing:
    raise SystemExit("declared Lua test files produced no passing report row:\n  " + "\n  ".join(missing))
print(f"fkst: reports valid; {len(observed)} declared test file(s) contributed passing rows")
PY
}

require_framework_artifact() {
  local artifact="$1"
  [[ -x "$artifact" ]] || die "fkst-framework build did not produce an executable: $artifact"
}

expect_selftest_rejection() {
  local name="$1" expected="$2" output status
  shift 2
  set +e
  output="$("$@" 2>&1)"
  status=$?
  set -e
  [[ "$status" -ne 0 ]] || die "selftest $name unexpectedly passed"
  grep -F "$expected" <<<"$output" >/dev/null \
    || die "selftest $name rejected for the wrong reason: $output"
  printf 'PASS lua-gate-selftest %s exit=%s fingerprint=%s\n' \
    "$name" "$status" "$expected"
}

lua_gate_selftest() {
  local work fixture_root fixture_fk source pin normal_report graph_report archive_root
  command -v git >/dev/null 2>&1 || die "git is required for Lua gate selftest"
  command -v python3 >/dev/null 2>&1 || die "python3 is required for Lua gate selftest"
  command -v tar >/dev/null 2>&1 || die "tar is required for Lua gate selftest"

  work="$(mktemp -d "${TMPDIR:-/tmp}/trureturing-lua-selftest.XXXXXX")" \
    || die "cannot create Lua gate selftest directory"
  trap 'rm -rf -- "${work:-}"' EXIT
  fixture_root="$work/repository"
  fixture_fk="$fixture_root/.fkst"
  mkdir -p "$fixture_fk" "$fixture_root/packages/fixture/tests"
  cp "$FKST_ROOT/substrate-ref" "$fixture_fk/substrate-ref"
  cp "$FKST_ROOT/fkst.lock" "$fixture_fk/fkst.lock"
  cp "$FKST_ROOT/fkst.workspace.toml" "$fixture_fk/fkst.workspace.toml"
  : >"$fixture_root/packages/fixture/tests/dummy_test.lua"

  rm "$fixture_fk/substrate-ref"
  expect_selftest_rejection missing-pin "missing substrate pin" \
    load_lua_test_contract "$fixture_fk"
  cp "$FKST_ROOT/substrate-ref" "$fixture_fk/substrate-ref"

  rm "$fixture_fk/fkst.lock"
  expect_selftest_rejection missing-lock "missing platform lock" \
    load_lua_test_contract "$fixture_fk"
  printf '%s\n' 'not valid toml = [' >"$fixture_fk/fkst.lock"
  expect_selftest_rejection bad-lock "invalid fkst platform lock contract" \
    load_lua_test_contract "$fixture_fk"
  cp "$FKST_ROOT/fkst.lock" "$fixture_fk/fkst.lock"

  grep -v '"idle-detector",' "$FKST_ROOT/fkst.workspace.toml" >"$fixture_fk/fkst.workspace.toml"
  load_lua_test_contract "$fixture_fk"
  expect_selftest_rejection composition-drift "platform composition drift" \
    validate_platform_composition
  cp "$FKST_ROOT/fkst.workspace.toml" "$fixture_fk/fkst.workspace.toml"

  source="$work/source"
  git init -q "$source"
  git -C "$source" config user.name fkst-selftest
  git -C "$source" config user.email fkst-selftest@example.invalid
  printf '%s\n' committed >"$source/tracked.txt"
  git -C "$source" add tracked.txt
  git -C "$source" commit -qm first
  pin="$(git -C "$source" rev-parse HEAD)"
  printf '%s\n' next >"$source/tracked.txt"
  git -C "$source" commit -qam second
  expect_selftest_rejection head-mismatch "checkout HEAD mismatch" \
    materialize_pinned_source fixture unused "$pin" "$source" "$work/head-mismatch"

  git -C "$source" checkout -q --detach "$pin"
  printf '%s\n' tampered >"$source/tracked.txt"
  git -C "$source" update-index --assume-unchanged tracked.txt
  archive_root="$(materialize_pinned_source fixture unused "$pin" "$source" "$work/archive")"
  [[ "$(<"$archive_root/tracked.txt")" == committed ]] \
    || die "selftest pinned-archive used tampered worktree bytes"
  printf '%s\n' 'PASS lua-gate-selftest pinned-archive-ignores-worktree'

  normal_report="$work/normal-report.json"
  graph_report="$work/graph-report.json"
  printf '%s\n' '{"schema":"wrong","summary":{"passed":1,"failed":0},"tests":[{"owner_namespace":"fixture","file":"tests/dummy_test.lua","name":"passes","status":"pass"}]}' >"$normal_report"
  printf '%s\n' '{"schema":"fkst.test.report.v1","summary":{"passed":1,"failed":0},"tests":[{"owner_namespace":"fixture","file":"tests/dummy_test.lua","name":"passes","status":"pass"}]}' >"$graph_report"
  expect_selftest_rejection bad-report-schema "bad test report schema" \
    validate_test_reports "$normal_report" "$graph_report" "$fixture_root"

  printf '%s\n' '{"schema":"fkst.test.report.v1","summary":{"passed":0,"failed":0},"tests":[]}' >"$normal_report"
  expect_selftest_rejection zero-tests "test report must have passed > 0" \
    validate_test_reports "$normal_report" "$graph_report" "$fixture_root"

  printf '%s\n' '{"schema":"fkst.test.report.v1","summary":{"passed":1,"failed":1},"tests":[{"owner_namespace":"fixture","file":"tests/dummy_test.lua","name":"passes","status":"pass"}]}' >"$normal_report"
  expect_selftest_rejection nonzero-failed-summary "test report must have failed = 0" \
    validate_test_reports "$normal_report" "$graph_report" "$fixture_root"

  printf '%s\n' '{"schema":"fkst.test.report.v1","summary":{"passed":2,"failed":0},"tests":[{"owner_namespace":"fixture","file":"tests/dummy_test.lua","name":"passes","status":"pass"},{"owner_namespace":"fixture","file":"tests/dummy_test.lua","name":"fails","status":"fail","error":"boom"}]}' >"$normal_report"
  expect_selftest_rejection non-passing-row "non-passing test row" \
    validate_test_reports "$normal_report" "$graph_report" "$fixture_root"

  printf '%s\n' '{"schema":"fkst.test.report.v1","summary":{"passed":2,"failed":0},"tests":[{"owner_namespace":"fixture","file":"tests/dummy_test.lua","name":"passes","status":"pass"}]}' >"$normal_report"
  expect_selftest_rejection summary-mismatch "summary/test row mismatch" \
    validate_test_reports "$normal_report" "$graph_report" "$fixture_root"

  printf '%s\n' '{"schema":"fkst.test.report.v1","summary":{"passed":1,"failed":0},"tests":[{"owner_namespace":"fixture","file":"tests/dummy_test.lua","name":"passes","status":"pass"}]}' >"$normal_report"
  : >"$fixture_root/packages/fixture/tests/unreported_test.lua"
  expect_selftest_rejection missing-file-contribution "declared Lua test files produced no passing report row" \
    validate_test_reports "$normal_report" "$graph_report" "$fixture_root"

  expect_selftest_rejection missing-artifact "did not produce an executable" \
    require_framework_artifact "$work/missing-fkst-framework"

  rm -rf -- "$work"
  trap - EXIT
  printf '%s\n' 'fkst: Lua gate selftest passed'
}

lua_test() {
  local substrate_root platform_root target_dir bin work conformance_root normal_root graph_root
  local normal_report graph_report
  command -v git >/dev/null 2>&1 || die "git is required for Lua tests"
  command -v cargo >/dev/null 2>&1 || die "cargo is required for Lua tests"
  command -v python3 >/dev/null 2>&1 || die "python3 is required for Lua tests"
  command -v tar >/dev/null 2>&1 || die "tar is required for Lua tests"
  lua_gate_selftest
  load_lua_test_contract
  validate_platform_composition
  load_target_packages

  work="$(mktemp -d "${TMPDIR:-/tmp}/trureturing-lua-test.XXXXXX")" \
    || die "cannot create Lua test work directory"
  trap 'rm -rf -- "${work:-}"' EXIT
  substrate_root="$(materialize_pinned_source substrate "$SUBSTRATE_URL" "$SUBSTRATE_PIN" "${FKST_SUBSTRATE:-}" "$work/substrate")"
  platform_root="$(materialize_pinned_source platform "$PLATFORM_URL" "$PLATFORM_PIN" "${FKST_PLATFORM:-}" "$work/platform")"
  target_dir="$work/cargo-target"
  printf 'fkst: building framework at substrate pin %s\n' "$SUBSTRATE_PIN"
  cargo build --locked --manifest-path "$substrate_root/Cargo.toml" \
    --target-dir "$target_dir" -p fkst-framework
  bin="$target_dir/debug/fkst-framework"
  require_framework_artifact "$bin"

  conformance_root="$work/conformance"
  normal_root="$work/normal"
  graph_root="$work/graph"
  normal_report="$work/normal-report.json"
  graph_report="$work/graph-report.json"
  mkdir -p "$work/runtime" "$work/durable"
  export FKST_RUNTIME_ROOT="$work/runtime"
  export FKST_DURABLE_ROOT="$work/durable"
  unset FKST_GITHUB_WRITE FKST_SUPERVISOR_PID

  printf '%s\n' '=== Lua gate 1/3: composed conformance ==='
  prepare_test_graph "$conformance_root" full "$platform_root"
  package_root_args "$conformance_root" 1
  "$bin" conformance --project-root "$conformance_root" "${PACKAGE_ROOT_ARGS[@]}"

  printf '%s\n' '=== Lua gate 2/3: target tests excluding run_graph* ==='
  prepare_test_graph "$normal_root" normal "$platform_root"
  package_root_args "$normal_root" 0
  "$bin" test --project-root "$normal_root" "${PACKAGE_ROOT_ARGS[@]}" \
    --report-json "$normal_report"

  printf '%s\n' '=== Lua gate 3/3: run_graph* on the complete declared graph ==='
  prepare_test_graph "$graph_root" graph "$platform_root"
  package_root_args "$graph_root" 1
  "$bin" test --project-root "$graph_root" "${PACKAGE_ROOT_ARGS[@]}" \
    --report-json "$graph_report"

  validate_test_reports "$normal_report" "$graph_report"
  rm -rf -- "$work"
  trap - EXIT
  printf '%s\n' 'fkst: Lua package gate passed'
}

[[ $# -eq 1 ]] || die "usage: $0 supervise|stop|status|logs|test|selftest"
case "$1" in
  supervise) start ;;
  stop) stop ;;
  status) status ;;
  logs) logs ;;
  test) lua_test ;;
  selftest) lua_gate_selftest ;;
  *) die "usage: $0 supervise|stop|status|logs|test|selftest" ;;
esac

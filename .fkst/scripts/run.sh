#!/usr/bin/env bash
set -euo pipefail

readonly FKST_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
readonly REPO_ROOT="$(cd -- "$FKST_ROOT/.." && pwd -P)"
readonly OPERATE_ROOT="${FKST_OPERATE_ROOT:-$HOME/.fkst/trureturing}"
readonly ENV_FILE="$OPERATE_ROOT/host.env"
readonly LOG_DIR="$OPERATE_ROOT/logs"
readonly PLATFORM_PACKAGES="github-proxy consensus github-devloop github-devloop-pr github-devloop-integration github-devloop-intake github-devloop-intake-default github-devloop-workflow github-devloop-decompose github-devloop-ops github-external-pr-intake idle-detector archaudit"
readonly HOST_PACKAGES="theory-selfgrowth"

die() {
  printf 'fkst: %s\n' "$*" >&2
  exit 1
}

shell_value() {
  printf '%q' "$1"
}

primary_worktree() {
  git -C "$REPO_ROOT" worktree list --porcelain 2>/dev/null \
    | awk '/^worktree / { sub(/^worktree /, ""); print; exit }'
}

discover_platform_root() {
  local primary candidate
  primary="$(primary_worktree)"
  [[ -n "$primary" ]] || return 1
  candidate="$(dirname -- "$primary")/fkst-packages"
  [[ -x "$candidate/scripts/run.sh" ]] || return 1
  printf '%s\n' "$candidate"
}

discover_bin() {
  local primary candidate configured
  if [[ -n "${BIN:-}" ]]; then
    [[ -x "$BIN" ]] || return 1
    printf '%s\n' "$BIN"
    return
  fi
  if command -v fkst-framework >/dev/null 2>&1; then
    command -v fkst-framework
    return
  fi
  if [[ -r "$ENV_FILE" ]] && configured="$({
    unset BIN
    # shellcheck disable=SC1090
    source "$ENV_FILE"
    [[ -x "${BIN:-}" ]]
    printf '%s\n' "$BIN"
  })"; then
    printf '%s\n' "$configured"
    return
  fi
  primary="$(primary_worktree)"
  [[ -n "$primary" ]] || return 1
  candidate="$(dirname -- "$primary")/fkst-substrate/target/debug/fkst-framework"
  [[ -x "$candidate" ]] || return 1
  printf '%s\n' "$candidate"
}

ensure_host_env() {
  local bin platform
  mkdir -p "$OPERATE_ROOT/durable" "$OPERATE_ROOT/runtime" "$LOG_DIR" "$HOME/.fkst/rate-pools"
  [[ ! -e "$ENV_FILE" ]] || return 0
  bin="$(discover_bin)" || die "cannot discover BIN; put fkst-framework on PATH"
  platform="$(discover_platform_root)" \
    || die "cannot discover sibling fkst-packages checkout"
  {
    printf '# Generated host-local configuration. Do not commit.\n'
    printf 'BIN=%s\n' "$(shell_value "$bin")"
    printf 'FKST_HOST_ROOT=%s\n' "$(shell_value "$OPERATE_ROOT/checkout")"
    printf 'FKST_PLATFORM_ROOT=%s\n' "$(shell_value "$platform")"
    printf 'FKST_DURABLE_ROOT=%s\n' "$(shell_value "$OPERATE_ROOT/durable")"
    printf 'FKST_RUNTIME_ROOT=%s\n' "$(shell_value "$OPERATE_ROOT/runtime")"
    printf 'FKST_RATE_POOL_ROOT=%s\n' "$(shell_value "$HOME/.fkst/rate-pools")"
    printf 'FKST_GITHUB_REPO=the-omega-institute/trureturing\n'
    printf 'unset FKST_GITHUB_WRITE\n'
    printf 'FKST_GITHUB_BOT_LOGIN=ElonSG\n'
    printf 'FKST_GITHUB_PROXY_POLL_LABEL_PREFIX=fkst-dev:\n'
    printf 'FKST_DEVLOOP_UPSTREAM_BRANCH=dev\n'
    printf 'FKST_DEVLOOP_INTEGRATION_BRANCH=integration-ElonSG\n'
    printf 'FKST_DEVLOOP_ROLLUP_MERGE=auto\n'
  } >"$ENV_FILE"
  chmod 600 "$ENV_FILE"
}

load_host_env() {
  ensure_host_env
  set -a
  # shellcheck disable=SC1090
  source "$ENV_FILE"
  set +a
  # GitHub write posture is a host-local operational fact carried by host.env
  # (gitignored, not committed): unset/anything-but-1 = dry-run; 1 = real writes.
  # A freshly generated host.env defaults to dry-run (see ensure_host_env); the
  # operator opts into real writes by editing their own host.env.
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

workspace_unit_rows() {
  python3 - "$FKST_ROOT/fkst.workspace.toml" "$REPO_ROOT" <<'PY'
import glob
import pathlib
import sys
import tomllib

workspace_file = pathlib.Path(sys.argv[1])
repository_root = pathlib.Path(sys.argv[2]).resolve()
with workspace_file.open("rb") as stream:
    workspace = tomllib.load(stream)

patterns = workspace.get("workspace", {}).get("units")
if not isinstance(patterns, list) or not patterns:
    raise SystemExit("workspace.units must be a non-empty array")

units = {}
for pattern in patterns:
    if not isinstance(pattern, str) or not pattern:
        raise SystemExit("workspace.units entries must be non-empty strings")
    matches = glob.glob(pattern, root_dir=repository_root, recursive=True)
    if not matches:
        raise SystemExit(f"workspace unit pattern matched nothing: {pattern}")
    for match in matches:
        source = repository_root / match
        if source.is_symlink() or not source.is_dir():
            raise SystemExit(f"workspace unit is not a real directory: {match}")
        resolved = source.resolve()
        try:
            relative = resolved.relative_to(repository_root).as_posix()
        except ValueError as error:
            raise SystemExit(f"workspace unit escapes repository root: {match}") from error
        if "\n" in relative or "\t" in relative:
            raise SystemExit(f"workspace unit path contains a control separator: {relative!r}")
        manifest_path = resolved / "fkst.toml"
        try:
            with manifest_path.open("rb") as stream:
                manifest = tomllib.load(stream)
        except (OSError, tomllib.TOMLDecodeError) as error:
            raise SystemExit(f"cannot parse workspace unit manifest {relative}/fkst.toml: {error}") from error
        kind = manifest.get("kind")
        name = manifest.get("name")
        if not isinstance(kind, str) or not isinstance(name, str) or not name:
            raise SystemExit(f"workspace unit has invalid kind or name: {relative}")
        if any(separator in name for separator in ("\n", "\t")):
            raise SystemExit(f"workspace unit name contains a control separator: {name!r}")
        units[relative] = (kind, name)

for relative in sorted(units):
    kind, name = units[relative]
    print(f"{relative}\t{kind}\t{name}")
PY
}

verify_test_report() {
  local report="$1" package_name="$2"
  python3 - "$report" "$package_name" <<'PY'
import json
import pathlib
import sys

report_path = pathlib.Path(sys.argv[1])
package_name = sys.argv[2]
try:
    with report_path.open("r", encoding="utf-8") as stream:
        report = json.load(stream)
except (OSError, json.JSONDecodeError) as error:
    raise SystemExit(f"fkst: package {package_name}: invalid test report: {error}") from error

if report.get("schema") != "fkst.test.report.v1":
    raise SystemExit(f"fkst: package {package_name}: invalid test report schema")
summary = report.get("summary")
tests = report.get("tests")
if not isinstance(summary, dict) or not isinstance(tests, list):
    raise SystemExit(f"fkst: package {package_name}: invalid test report shape")
passed = summary.get("passed")
failed = summary.get("failed")
if type(passed) is not int or type(failed) is not int or passed < 0 or failed < 0:
    raise SystemExit(f"fkst: package {package_name}: invalid test report counts")
if passed + failed != len(tests):
    raise SystemExit(f"fkst: package {package_name}: inconsistent test report counts")
if failed != 0:
    raise SystemExit(f"fkst: package {package_name}: report contains failed tests")
if passed == 0:
    raise SystemExit(f"fkst: package {package_name}: zero tests discovered")
PY
}

test_packages() {
  local bin rows stage_root unit kind name report rc
  local -a package_units=() package_names=()
  bin="$(discover_bin)" || die "cannot discover BIN; set BIN or put fkst-framework on PATH"
  rows="$(workspace_unit_rows)" || die "cannot resolve workspace units"
  [[ -n "$rows" ]] || die "workspace declares no units"

  PACKAGE_TEST_TMP="$(mktemp -d "${TMPDIR:-/tmp}/trureturing-package-tests.XXXXXXXX")" \
    || die "cannot create package test workspace"
  trap 'rm -rf -- "${PACKAGE_TEST_TMP:-}"' EXIT
  stage_root="$PACKAGE_TEST_TMP/workspace"
  mkdir -p "$stage_root"
  cp "$FKST_ROOT/fkst.workspace.toml" "$stage_root/fkst.workspace.toml"
  if [[ -f "$FKST_ROOT/fkst.lock" ]]; then
    cp "$FKST_ROOT/fkst.lock" "$stage_root/fkst.lock"
  fi

  while IFS=$'\t' read -r unit kind name; do
    [[ -n "$unit" && -n "$kind" && -n "$name" ]] || die "invalid workspace unit record"
    mkdir -p "$stage_root/$(dirname -- "$unit")"
    cp -R "$REPO_ROOT/$unit" "$stage_root/$unit"
    case "$kind" in
      package|package.*|package_*|flat-package|composed-package)
        package_units+=("$unit")
        package_names+=("$name")
        ;;
    esac
  done <<< "$rows"
  [[ "${#package_units[@]}" -gt 0 ]] || die "workspace declares no host packages"

  unset FKST_GITHUB_WRITE FKST_SUPERVISOR_PID
  for index in "${!package_units[@]}"; do
    unit="${package_units[$index]}"
    name="${package_names[$index]}"
    report="$PACKAGE_TEST_TMP/$name-report.json"
    mkdir -p "$PACKAGE_TEST_TMP/runtime/$name" "$PACKAGE_TEST_TMP/durable/$name"
    set +e
    FKST_RUNTIME_ROOT="$PACKAGE_TEST_TMP/runtime/$name" \
      FKST_DURABLE_ROOT="$PACKAGE_TEST_TMP/durable/$name" \
      "$bin" test \
        --project-root "$stage_root" \
        --package-root "$stage_root/$unit" \
        --report-json "$report"
    rc=$?
    set -e
    if [[ "$rc" -ne 0 ]]; then
      return "$rc"
    fi
    verify_test_report "$report" "$name"
  done
}

[[ $# -eq 1 ]] || die "usage: $0 supervise|stop|status|logs|test"
case "$1" in
  supervise) start ;;
  stop) stop ;;
  status) status ;;
  logs) logs ;;
  test) test_packages ;;
  *) die "usage: $0 supervise|stop|status|logs|test" ;;
esac

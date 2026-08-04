#!/usr/bin/env bash
# Canonical hourly engine maintenance: platform pin/lock sync, checkout FF, restart policy,
# worktree collection, and stuck Lean build/slot collection.
set -uo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
REPOSITORY_ROOT="$(cd -- "$SCRIPT_DIR/../.." && pwd -P)"
# shellcheck source=.fkst/scripts/host-contract.sh
source "$SCRIPT_DIR/host-contract.sh"
# shellcheck source=.fkst/scripts/restart-policy.sh
source "$SCRIPT_DIR/restart-policy.sh"

CHANGED=0
CHECKOUT_DEV_REV=""
PLATFORM_CURRENT_REV=""
PLATFORM_DEV_REV=""
ACTIVATION_ROLLBACK_REV=""
LEAN_REPORT_REBUILT_THIS_CYCLE=0
LEAN_REPORT_STATUS_CHECKED_THIS_CYCLE=0
LEAN_REPORT_STATUS_STATE="not-checked"
LEAN_REPORT_STATUS_DETAIL="not observed"

say() {
  printf '[%s] %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*" \
    | tee -a "$FKST_MAINTENANCE_LOG"
}

require_parameter() {
  local name="$1"
  [[ -n "${!name:-}" ]] || {
    printf 'hourly-maintenance: required parameter %s is unset\n' "$name" >&2
    return 2
  }
}

require_absolute_path() {
  local name="$1"
  [[ "${!name}" == /* ]] || {
    printf 'hourly-maintenance: %s must be an absolute path\n' "$name" >&2
    return 2
  }
}

validate_configuration() {
  local name
  for name in \
    FKST_HOST_ROOT \
    FKST_PLATFORM_ROOT \
    BIN \
    FKST_RUN_SCRIPT \
    FKST_MAINTENANCE_LOG \
    FKST_WORKTREE_ROOT \
    FKST_REPORT_SLOT_ROOT \
    FKST_TIMEOUT_BIN \
    FKST_GITHUB_REPO \
    FKST_LAUNCHD_LABEL; do
    require_parameter "$name" || return
  done
  for name in \
    FKST_HOST_ROOT \
    FKST_PLATFORM_ROOT \
    BIN \
    FKST_RUN_SCRIPT \
    FKST_MAINTENANCE_LOG \
    FKST_WORKTREE_ROOT \
    FKST_REPORT_SLOT_ROOT \
    FKST_TIMEOUT_BIN; do
    require_absolute_path "$name" || return
  done
  [[ -d "$(dirname -- "$FKST_MAINTENANCE_LOG")" ]] || {
    printf 'hourly-maintenance: log directory does not exist: %s\n' \
      "$(dirname -- "$FKST_MAINTENANCE_LOG")" >&2
    return 2
  }
}

check_launchd_conformance() {
  local make_bin="${FKST_MAKE_BIN:-}"
  if [[ -z "$make_bin" ]]; then
    make_bin="$(command -v make)" \
      || { printf 'hourly-maintenance: make is unavailable\n' >&2; return 2; }
  fi
  [[ "$make_bin" == /* && -f "$make_bin" && -x "$make_bin" ]] \
    || {
      printf 'hourly-maintenance: make is not an executable absolute path: %s\n' \
        "$make_bin" >&2
      return 2
    }
  HOST_CONFIG="$HOST_CONFIG" FKST_MAKE_BIN="$make_bin" \
    "$make_bin" -s -C "$REPOSITORY_ROOT" launchd-conformance-check
}

read_deployed_platform_revision() {
  grep -oE '[0-9a-f]{40}' "$FKST_HOST_ROOT/fkst.workspace.toml" 2>/dev/null \
    | head -1
}

write_platform_pin_revision() {
  local target_revision="$1" current_revision temporary_workspace
  [[ "$target_revision" =~ ^[0-9a-f]{40}$ ]] \
    || { say "PLATFORM-PIN-WRITE-FAIL: invalid target revision"; return 1; }
  current_revision="$(read_deployed_platform_revision)"
  [[ "$current_revision" =~ ^[0-9a-f]{40}$ ]] \
    || { say "PLATFORM-PIN-WRITE-FAIL: deployed revision is unreadable"; return 1; }

  temporary_workspace="$FKST_HOST_ROOT/fkst.workspace.toml.next-$$-$RANDOM"
  if ! (set -o noclobber; : > "$temporary_workspace") 2>/dev/null; then
    say "PLATFORM-PIN-WRITE-FAIL: cannot create temporary workspace"
    return 1
  fi
  if ! sed "s/$current_revision/$target_revision/g" \
      "$FKST_HOST_ROOT/fkst.workspace.toml" > "$temporary_workspace" \
      || ! mv "$temporary_workspace" "$FKST_HOST_ROOT/fkst.workspace.toml"; then
    rm -f -- "$temporary_workspace" 2>/dev/null || true
    return 1
  fi
}

regenerate_platform_lock() {
  "$FKST_TIMEOUT_BIN" 240 "$BIN" host lock \
    --project-root "$FKST_HOST_ROOT" >/dev/null 2>&1
}

rollback_platform() {
  local previous_revision="$1"
  if ! write_platform_pin_revision "$previous_revision"; then
    say "ROLLBACK-PIN-WRITE-FAIL for previous revision ${previous_revision:0:12}"
    return 1
  fi
  if ! regenerate_platform_lock; then
    say "ROLLBACK-HOST-LOCK-FAIL for previous revision ${previous_revision:0:12}"
    return 1
  fi
  say "PLATFORM-ROLLBACK-OK: restored revision ${previous_revision:0:12} and regenerated lock"
}

sync_platform() {
  git -C "$FKST_PLATFORM_ROOT" fetch origin dev >/dev/null 2>&1 \
    || { say "PLAT-FETCH-FAIL"; return 1; }

  # Issue #2461: the deployed engine reads checkout/fkst.workspace.toml, not the committed
  # checkout/.fkst copy. The deployed top-level file is therefore the only pin updated here.
  PLATFORM_CURRENT_REV="$(read_deployed_platform_revision)"
  PLATFORM_DEV_REV="$(git -C "$FKST_PLATFORM_ROOT" rev-parse origin/dev 2>/dev/null)"
  [[ "$PLATFORM_CURRENT_REV" =~ ^[0-9a-f]{40}$ ]] \
    || { say "invalid deployed platform pin"; return 1; }
  [[ "$PLATFORM_DEV_REV" =~ ^[0-9a-f]{40}$ ]] \
    || { say "no platform origin/dev"; return 1; }

  if [[ "$PLATFORM_CURRENT_REV" == "$PLATFORM_DEV_REV" ]]; then
    say "PLATFORM CURRENT (${PLATFORM_CURRENT_REV:0:12})"
    return 0
  fi

  say "PLATFORM BEHIND ${PLATFORM_CURRENT_REV:0:12} -> ${PLATFORM_DEV_REV:0:12}; syncing"
  if ! record_restart_obligation \
      "$PLATFORM_CURRENT_REV" "$PLATFORM_DEV_REV" \
      "platform pin ${PLATFORM_CURRENT_REV:0:12}->${PLATFORM_DEV_REV:0:12}"; then
    say "PLATFORM-ACTIVATION-INTENT-FAIL; pin mutation refused"
    return 1
  fi
  if ! write_platform_pin_revision "$PLATFORM_DEV_REV"; then
    if rollback_platform "$PLATFORM_CURRENT_REV"; then
      say "PLATFORM-PIN-WRITE-FAIL; reverted to ${PLATFORM_CURRENT_REV:0:12} from previous revision"
    else
      say "PLATFORM-PIN-WRITE-FAIL; rollback failed from previous revision"
    fi
    say "RESTART-OBLIGATION RETAINED: mutation failed; verified restart still required"
    return 1
  fi

  if ! regenerate_platform_lock; then
    say "HOST-LOCK-FAIL for ${PLATFORM_DEV_REV:0:12}; reverting platform"
    if rollback_platform "$PLATFORM_CURRENT_REV"; then
      say "HOST-LOCK-FAIL recovery restored ${PLATFORM_CURRENT_REV:0:12}"
    else
      say "PLATFORM-ROLLBACK-FAIL after host-lock failure; previous revision not fully activated"
    fi
    say "RESTART-OBLIGATION RETAINED: host-lock failure; verified restart still required"
    return 1
  fi

  CHANGED=1
}

sync_checkout() {
  if ! git -C "$FKST_HOST_ROOT" fetch origin dev >/dev/null 2>&1; then
    say "CHECKOUT-FETCH-FAIL; skipped checkout sync"
    return 0
  fi

  local checkout_head checkout_status behind lean_report_required=0 lean_diff_rc
  checkout_head="$(git -C "$FKST_HOST_ROOT" rev-parse HEAD 2>/dev/null)"
  CHECKOUT_DEV_REV="$(git -C "$FKST_HOST_ROOT" rev-parse origin/dev 2>/dev/null)"
  if [[ -z "$checkout_head" || -z "$CHECKOUT_DEV_REV" ]]; then
    say "CHECKOUT-REV-PARSE-FAIL; skipped checkout sync"
    return 0
  fi
  if [[ "$checkout_head" == "$CHECKOUT_DEV_REV" ]]; then
    say "CHECKOUT CURRENT (${checkout_head:0:12})"
    return 0
  fi
  if ! git -C "$FKST_HOST_ROOT" merge-base --is-ancestor \
      "$checkout_head" "$CHECKOUT_DEV_REV" >/dev/null 2>&1; then
    say "CHECKOUT DIVERGED from origin/dev; not auto-FF (manual review)"
    return 0
  fi

  # Only TRACKED modifications may block the fast-forward. Untracked files provably do not
  # prevent one -- `git merge --ff-only` succeeds with them present -- and `--ff-only` below is
  # already the correct arbiter for the one case that matters, an untracked file the merge would
  # overwrite, which it refuses on its own.
  #
  # Counting untracked files as "uncommitted changes" can freeze a deployed checkout on intentional
  # host-owned files such as `.metadata_never_index`; `--ff-only` remains the overwrite arbiter.
  if ! checkout_status="$(
      git -C "$FKST_HOST_ROOT" status --porcelain --untracked-files=no 2>/dev/null
    )"; then
    say "CHECKOUT-STATUS-FAIL; skipped checkout sync"
    return 0
  fi
  if [[ -n "$checkout_status" ]]; then
    say "CHECKOUT-FF-BLOCKED (uncommitted changes); skipped, engine stays on ${checkout_head:0:12}"
    return 0
  fi

  behind="$(git -C "$FKST_HOST_ROOT" rev-list \
    "$checkout_head..$CHECKOUT_DEV_REV" --count 2>/dev/null)"
  git -C "$FKST_HOST_ROOT" diff --quiet \
    "$checkout_head" "$CHECKOUT_DEV_REV" -- '*.lean' 2>/dev/null
  lean_diff_rc=$?
  case "$lean_diff_rc" in
    0) lean_report_required=0 ;;
    1) lean_report_required=1 ;;
    *)
      say "CHECKOUT-LEAN-DIFF-FAIL; fast-forward refused"
      return 0
      ;;
  esac
  say "CHECKOUT BEHIND ${checkout_head:0:12} -> ${CHECKOUT_DEV_REV:0:12} ($behind commits); FF"
  if ! record_restart_obligation "" "" \
      "checkout fast-forward ${checkout_head:0:12}->${CHECKOUT_DEV_REV:0:12}" \
      "$checkout_head" "$CHECKOUT_DEV_REV" "$lean_report_required"; then
    say "CHECKOUT-ACTIVATION-INTENT-FAIL; fast-forward refused"
    return 0
  fi
  if git -C "$FKST_HOST_ROOT" merge --ff-only "$CHECKOUT_DEV_REV" >/dev/null 2>&1; then
    CHANGED=1
  else
    say "CHECKOUT-FF-BLOCKED; skipped, engine stays on ${checkout_head:0:12}"
    say "RESTART-OBLIGATION RETAINED: fast-forward failed; verified restart still required"
  fi
}

workspace_composition_tool() {
  local mode="$1" temporary_workspace="${2:-}"
  "$FKST_PYTHON_BIN" - \
    "$mode" \
    "$FKST_HOST_ROOT/.fkst/fkst.workspace.toml" \
    "$FKST_HOST_ROOT/fkst.workspace.toml" \
    "$temporary_workspace" <<'PY'
import json
import os
import re
import stat
import sys
import tomllib
from pathlib import Path

SOURCE_ID = "fkst-packages-platform"


def fail(message):
    raise ValueError(message)


def load_manifest(path, role):
    try:
        with path.open("rb") as handle:
            manifest = tomllib.load(handle)
    except Exception as error:
        fail(f"{role} is invalid: {path}: {error}")
    if not isinstance(manifest, dict):
        fail(f"{role} must be a TOML table: {path}")
    return manifest


def string_list(value, role):
    if (
        not isinstance(value, list)
        or any(not isinstance(item, str) or not item for item in value)
        or len(value) != len(set(value))
    ):
        fail(f"{role} must be an array of unique non-empty strings")
    return tuple(value)


def composition(manifest, role):
    workspace = manifest.get("workspace")
    if not isinstance(workspace, dict):
        fail(f"{role} workspace must be a table")
    units = string_list(workspace.get("units"), f"{role} workspace.units")

    sources = manifest.get("external_sources")
    if not isinstance(sources, list) or any(not isinstance(item, dict) for item in sources):
        fail(f"{role} external_sources must be a table array")
    matching = [
        (index, source)
        for index, source in enumerate(sources)
        if source.get("id") == SOURCE_ID
    ]
    if len(matching) != 1:
        fail(f"{role} must declare exactly one {SOURCE_ID} source")
    source_index, source = matching[0]
    packages = string_list(source.get("packages"), f"{role} {SOURCE_ID} packages")
    libraries = string_list(source.get("libraries"), f"{role} {SOURCE_ID} libraries")
    return {
        "packages": packages,
        "libraries": libraries,
        "units": units,
    }, source_index


def table_body(text, header_pattern, role):
    matches = list(re.finditer(header_pattern, text, re.MULTILINE))
    if len(matches) != 1:
        fail(f"{role} must occur exactly once")
    start = matches[0].end()
    next_header = re.search(r"^[ \t]*\[", text[start:], re.MULTILINE)
    end = start + next_header.start() if next_header else len(text)
    return start, end


def external_source_body(text, source_index):
    headers = list(
        re.finditer(
            r"^[ \t]*\[\[external_sources\]\][ \t]*(?:#.*)?$",
            text,
            re.MULTILINE,
        )
    )
    if source_index >= len(headers):
        fail("runtime workspace external_sources syntax does not match parsed tables")
    start = headers[source_index].end()
    next_header = re.search(r"^[ \t]*\[", text[start:], re.MULTILINE)
    end = start + next_header.start() if next_header else len(text)
    return start, end


def array_value_span(text, body_start, body_end, key, role):
    body = text[body_start:body_end]
    assignments = list(
        re.finditer(rf"^[ \t]*{re.escape(key)}[ \t]*=", body, re.MULTILINE)
    )
    if len(assignments) != 1:
        fail(f"{role}.{key} assignment must occur exactly once")
    cursor = body_start + assignments[0].end()
    while cursor < body_end and text[cursor] in " \t":
        cursor += 1
    if cursor >= body_end or text[cursor] != "[":
        fail(f"{role}.{key} must use TOML array syntax")

    start = cursor
    depth = 0
    quote = None
    while cursor < body_end:
        if quote is not None:
            if text.startswith(quote, cursor):
                cursor += len(quote)
                quote = None
                continue
            if quote in {'"', '"""'} and text[cursor] == "\\":
                cursor += 2
                continue
            cursor += 1
            continue

        if text.startswith('"""', cursor) or text.startswith("'''", cursor):
            quote = text[cursor:cursor + 3]
            cursor += 3
            continue
        if text[cursor] in {'"', "'"}:
            quote = text[cursor]
            cursor += 1
            continue
        if text[cursor] == "#":
            newline = text.find("\n", cursor, body_end)
            cursor = body_end if newline < 0 else newline + 1
            continue
        if text[cursor] == "[":
            depth += 1
        elif text[cursor] == "]":
            depth -= 1
            if depth == 0:
                return start, cursor + 1
        cursor += 1
    fail(f"{role}.{key} array is not syntactically bounded")


def render_array(values):
    encoded = (json.dumps(value, ensure_ascii=True) for value in values)
    return "[" + ", ".join(encoded) + "]"


def render_runtime(runtime, tracked_composition, runtime_source_index, output):
    try:
        text = runtime.read_text(encoding="utf-8")
    except Exception as error:
        fail(f"runtime workspace is unreadable: {runtime}: {error}")

    workspace_start, workspace_end = table_body(
        text,
        r"^[ \t]*\[workspace\][ \t]*(?:#.*)?$",
        "runtime workspace [workspace] table",
    )
    source_start, source_end = external_source_body(text, runtime_source_index)
    replacements = []
    for key, start, end, role in (
        ("units", workspace_start, workspace_end, "runtime workspace workspace"),
        ("packages", source_start, source_end, f"runtime workspace {SOURCE_ID}"),
        ("libraries", source_start, source_end, f"runtime workspace {SOURCE_ID}"),
    ):
        value_start, value_end = array_value_span(text, start, end, key, role)
        replacements.append(
            (value_start, value_end, render_array(tracked_composition[key]))
        )
    for start, end, replacement in sorted(replacements, reverse=True):
        text = text[:start] + replacement + text[end:]

    try:
        rendered = tomllib.loads(text)
    except Exception as error:
        fail(f"rendered runtime workspace is invalid: {error}")
    rendered_composition, _ = composition(rendered, "rendered runtime workspace")
    if rendered_composition != tracked_composition:
        fail("rendered runtime workspace composition does not match tracked workspace")

    original = runtime.read_text(encoding="utf-8")
    if text == original:
        print("CURRENT")
        return
    try:
        with output.open("x", encoding="utf-8", newline="") as handle:
            handle.write(text)
        os.chmod(output, stat.S_IMODE(runtime.stat().st_mode))
    except Exception as error:
        fail(f"cannot stage runtime workspace: {output}: {error}")
    print("UPDATED")


def format_values(values):
    return "[" + ",".join(values) + "]"


def verify_composition(tracked, runtime):
    differences = []
    for key in ("packages", "libraries", "units"):
        tracked_values = tracked[key]
        runtime_values = runtime[key]
        only_tracked = sorted(set(tracked_values) - set(runtime_values))
        only_runtime = sorted(set(runtime_values) - set(tracked_values))
        if only_tracked or only_runtime:
            differences.append(
                f"{key} only-in-tracked={format_values(only_tracked)} "
                f"only-in-runtime={format_values(only_runtime)}"
            )
        elif tracked_values != runtime_values:
            differences.append(
                f"{key} order tracked={format_values(tracked_values)} "
                f"runtime={format_values(runtime_values)}"
            )
    if differences:
        print("\n".join(differences), file=sys.stderr)
        raise SystemExit(1)


def main():
    mode = sys.argv[1]
    tracked_path = Path(sys.argv[2])
    runtime_path = Path(sys.argv[3])
    output_path = Path(sys.argv[4]) if sys.argv[4] else None
    tracked_manifest = load_manifest(tracked_path, "tracked workspace")
    runtime_manifest = load_manifest(runtime_path, "runtime workspace")
    tracked_composition, _ = composition(tracked_manifest, "tracked workspace")
    runtime_composition, runtime_source_index = composition(
        runtime_manifest,
        "runtime workspace",
    )
    if mode == "render":
        if output_path is None:
            fail("render mode requires an output path")
        render_runtime(
            runtime_path,
            tracked_composition,
            runtime_source_index,
            output_path,
        )
    elif mode == "verify":
        verify_composition(tracked_composition, runtime_composition)
    else:
        fail(f"unknown workspace composition mode: {mode}")


try:
    main()
except SystemExit:
    raise
except Exception as error:
    print(error, file=sys.stderr)
    raise SystemExit(1)
PY
}

sync_workspace_composition() {
  local runtime_workspace="$FKST_HOST_ROOT/fkst.workspace.toml"
  local temporary_workspace result diagnostic
  temporary_workspace="${runtime_workspace}.composition-next-$$-$RANDOM"

  if ! result="$(workspace_composition_tool render "$temporary_workspace" 2>&1)"; then
    rm -f "$temporary_workspace"
    say "WORKSPACE-COMPOSITION-SYNC-FAIL: $result"
    return 1
  fi
  case "$result" in
    UPDATED)
      if ! mv "$temporary_workspace" "$runtime_workspace"; then
        rm -f "$temporary_workspace"
        say "WORKSPACE-COMPOSITION-WRITE-FAIL: atomic replacement failed"
        return 1
      fi
      ;;
    CURRENT)
      ;;
    *)
      rm -f "$temporary_workspace"
      say "WORKSPACE-COMPOSITION-SYNC-FAIL: unexpected renderer result: $result"
      return 1
      ;;
  esac

  if ! diagnostic="$(workspace_composition_tool verify 2>&1)"; then
    while IFS= read -r line; do
      say "WORKSPACE-COMPOSITION-DRIFT: $line"
    done <<< "$diagnostic"
    return 1
  fi
  if [[ "$result" == "UPDATED" ]]; then
    say "WORKSPACE COMPOSITION SYNCED"
  else
    say "WORKSPACE COMPOSITION CURRENT"
  fi
}

canonical_gc_root() {
  local root="$1" resolved relative
  [[ -d "$root" ]] || return 1
  resolved="$(cd -- "$root" 2>/dev/null && pwd -P)" || return 1
  relative="${resolved#/}"
  [[ "$resolved" == /* && "$resolved" != "/" && "$relative" == */* ]] || return 1
  printf '%s\n' "$resolved"
}

lane_is_clean_and_unowned() {
  local lane="$1" status own_commits
  git -C "$lane" rev-parse --is-inside-work-tree >/dev/null 2>&1 || return 1
  status="$(git -C "$lane" status --porcelain --untracked-files=normal 2>/dev/null)" \
    || return 1
  [[ -z "$status" ]] || return 1
  own_commits="$(git -C "$lane" rev-list --count origin/dev..HEAD 2>/dev/null)" \
    || return 1
  [[ "$own_commits" == "0" ]]
}

gc_worktrees() {
  local root
  [[ -d "$FKST_WORKTREE_ROOT" ]] || return 0
  root="$(canonical_gc_root "$FKST_WORKTREE_ROOT")" \
    || { say "WT-GC skipped (unsafe root)"; return 0; }

  local removed=0 directory lane issue_number state eligible
  for directory in "$root"/*/; do
    [[ -d "$directory" ]] || continue
    lane="$(basename -- "$directory")"
    if ! lane_is_clean_and_unowned "$directory"; then
      say "WT-GC retained $lane (own commits, uncommitted work, or unverifiable ancestry)"
      continue
    fi

    eligible=0
    if [[ "$lane" =~ ([0-9]+)-[0-9]+$ ]]; then
      issue_number="${BASH_REMATCH[1]}"
      state="$(gh issue view "$issue_number" \
        --repo "$FKST_GITHUB_REPO" --json state --jq '.state' 2>/dev/null)"
      [[ "$state" == "CLOSED" ]] && eligible=1
    fi
    [[ "$eligible" == "1" ]] || continue

    if git -C "$FKST_HOST_ROOT" worktree remove "${directory%/}" >/dev/null 2>&1; then
      removed=$((removed + 1))
    else
      say "WT-GC retained $lane (git refused removal)"
    fi
  done
  if [[ "$removed" -gt 0 ]]; then
    git -C "$FKST_HOST_ROOT" worktree prune >/dev/null 2>&1 || true
    say "WT-GC removed $removed orphan worktree(s)"
  fi
}

reclaim_stale_slots() {
  local root
  [[ -d "$FKST_REPORT_SLOT_ROOT" ]] || return 0
  root="$(canonical_gc_root "$FKST_REPORT_SLOT_ROOT")" \
    || { say "STUCK-LEAN-GC skipped slot reclaim (unsafe root)"; return 0; }

  local lock owner confirmed_owner live_pid guard reclaimed
  for lock in "$root"/*.lock; do
    [[ -e "$lock/owner" ]] || continue
    owner="$(grep -oE '^[0-9]+' "$lock/owner" 2>/dev/null | head -1)"
    [[ -n "$owner" ]] || continue
    kill -0 "$owner" 2>/dev/null && continue
    live_pid="$(ps -p "$owner" -o pid= 2>/dev/null | tr -d '[:space:]')"
    [[ -z "$live_pid" ]] || continue

    guard="$lock.reclaim-guard"
    mkdir "$guard" 2>/dev/null || continue
    confirmed_owner="$(grep -oE '^[0-9]+' "$lock/owner" 2>/dev/null | head -1)"
    if [[ "$confirmed_owner" != "$owner" ]] \
        || kill -0 "$owner" 2>/dev/null \
        || [[ -n "$(ps -p "$owner" -o pid= 2>/dev/null | tr -d '[:space:]')" ]]; then
      rmdir "$guard" 2>/dev/null || true
      continue
    fi

    reclaimed="$lock.reclaimed-$$-$RANDOM"
    if mv "$lock" "$reclaimed" 2>/dev/null; then
      rm -rf -- "$reclaimed"
    fi
    rmdir "$guard" 2>/dev/null || true
  done
}

gc_stuck_lean_builds() {
  reclaim_stale_slots
}

engine_pid() {
  local escaped_root
  escaped_root="$(printf '%s' "$FKST_HOST_ROOT" | sed 's/[][\\.^$*+?{}|()]/\\&/g')"
  pgrep -f "fkst-framework.*supervise --project-root $escaped_root" 2>/dev/null | head -1
}

launchd_service_state() {
  local output line
  if ! output="$(launchctl list 2>/dev/null)"; then
    printf 'unknown\n'
    return 0
  fi
  while IFS= read -r line; do
    if [[ "$line" == *[[:space:]]"$FKST_LAUNCHD_LABEL" ]]; then
      printf 'in-service\n'
      return 0
    fi
  done <<< "$output"
  printf 'not-in-service\n'
}

main() {
  local host_config="${HOST_CONFIG:-}" validate_only="${VALIDATE_ONLY:-0}"
  LEAN_REPORT_REBUILT_THIS_CYCLE=0
  LEAN_REPORT_STATUS_CHECKED_THIS_CYCLE=0
  LEAN_REPORT_STATUS_STATE="not-checked"
  LEAN_REPORT_STATUS_DETAIL="not observed"
  [[ "$validate_only" == "0" || "$validate_only" == "1" ]] \
    || { printf 'hourly-maintenance: VALIDATE_ONLY must be 0 or 1\n' >&2; return 2; }
  while [[ "$#" -gt 0 ]]; do
    case "$1" in
      --host-config)
        [[ "$#" -ge 2 ]] \
          || { printf 'hourly-maintenance: --host-config requires a path\n' >&2; return 2; }
        host_config="$2"
        shift 2
        ;;
      --validate-only)
        validate_only=1
        shift
        ;;
      *)
        printf 'hourly-maintenance: unknown argument %s\n' "$1" >&2
        return 2
        ;;
    esac
  done
  [[ -n "$host_config" ]] \
    || { printf 'hourly-maintenance: --host-config is required\n' >&2; return 2; }
  host_contract_load "$host_config" || return
  validate_configuration || return
  host_contract_require \
    FKST_BASH_BIN \
    FKST_ZSH_BIN \
    FKST_PYTHON_BIN \
    FKST_SUPERVISE_LAUNCHER_LOG \
    FKST_SUPERVISE_LAUNCHER_PATH || return
  [[ "$validate_only" == "0" ]] || return 0
  sync_platform || return
  sync_checkout
  sync_workspace_composition || return
  gc_worktrees
  gc_stuck_lean_builds
  restart_if_needed || return
  reconcile_lean_report_invariant || return
  check_launchd_conformance
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi

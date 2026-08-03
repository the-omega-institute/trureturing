#!/usr/bin/env bash
# Runtime identity reconciliation for the long-lived pr-watch process.

pr_watch_state_path() {
  if [[ -n "${PR_SHEPHERD_PID:-}" ]]; then
    printf '%s\n' "$PR_SHEPHERD_PID"
  elif [[ -n "${HOME:-}" ]]; then
    printf '%s\n' "$HOME/.pr-shepherd.pid"
  else
    return 1
  fi
}

load_pr_watch_state() {
  local state="$1" line
  local -a lines=()
  PR_WATCH_STATE_PID=""
  PR_WATCH_STATE_PROCESS_START=""
  PR_WATCH_STATE_CANONICAL_SCRIPT=""
  PR_WATCH_STATE_LOADED_SCRIPT=""
  PR_WATCH_STATE_LOADED_BLOB=""
  PR_WATCH_STATE_INTERVAL=""
  PR_WATCH_STATE_MAX_CYCLES=""
  PR_WATCH_STATE_CYCLE=""
  [[ -f "$state" && -r "$state" ]] || return 1
  while IFS= read -r line || [[ -n "$line" ]]; do
    lines+=("$line")
  done < "$state"
  [[ "${#lines[@]}" -eq 9 \
      && "${lines[0]}" == "schema=pr-watch-state-v1" \
      && "${lines[1]}" == pid=* \
      && "${lines[2]}" == process_start=* \
      && "${lines[3]}" == canonical_script=* \
      && "${lines[4]}" == loaded_script=* \
      && "${lines[5]}" == loaded_blob=* \
      && "${lines[6]}" == interval=* \
      && "${lines[7]}" == max_cycles=* \
      && "${lines[8]}" == cycle=* ]] || return 1

  PR_WATCH_STATE_PID="${lines[1]#pid=}"
  PR_WATCH_STATE_PROCESS_START="${lines[2]#process_start=}"
  PR_WATCH_STATE_CANONICAL_SCRIPT="${lines[3]#canonical_script=}"
  PR_WATCH_STATE_LOADED_SCRIPT="${lines[4]#loaded_script=}"
  PR_WATCH_STATE_LOADED_BLOB="${lines[5]#loaded_blob=}"
  PR_WATCH_STATE_INTERVAL="${lines[6]#interval=}"
  PR_WATCH_STATE_MAX_CYCLES="${lines[7]#max_cycles=}"
  PR_WATCH_STATE_CYCLE="${lines[8]#cycle=}"
  [[ "$PR_WATCH_STATE_PID" =~ ^[1-9][0-9]*$ \
      && -n "$PR_WATCH_STATE_PROCESS_START" \
      && "$PR_WATCH_STATE_CANONICAL_SCRIPT" == /* \
      && "$PR_WATCH_STATE_LOADED_SCRIPT" == /* \
      && "$PR_WATCH_STATE_LOADED_BLOB" =~ ^[0-9a-f]{40}$ \
      && "$PR_WATCH_STATE_INTERVAL" =~ ^(0|[1-9][0-9]*)$ \
      && "$PR_WATCH_STATE_MAX_CYCLES" =~ ^[1-9][0-9]*$ \
      && "$PR_WATCH_STATE_CYCLE" =~ ^[1-9][0-9]*$ ]] || return 1
  canonical_decimal_at_most \
    "$PR_WATCH_STATE_CYCLE" "$PR_WATCH_STATE_MAX_CYCLES"
}

pr_watch_process_start() {
  LC_ALL=C ps -p "$1" -o lstart= 2>/dev/null \
    | sed 's/^[[:space:]]*//;s/[[:space:]]*$//'
}

pr_watch_process_command() {
  LC_ALL=C ps -ww -p "$1" -o command= 2>/dev/null
}

reconcile_pr_watch() {
  local relative="Meta/StrataLint/scripts/pr-shepherd.sh"
  local state expected_script desired_blob checkout_blob loaded_blob actual_start command
  if ! state="$(pr_watch_state_path)"; then
    say "PR-WATCH IDENTITY UNKNOWN: state path is unavailable"
    return 1
  fi
  if [[ ! -e "$state" ]]; then
    say "PR-WATCH INACTIVE"
    return 0
  fi
  if ! load_pr_watch_state "$state"; then
    say "PR-WATCH IDENTITY UNKNOWN: invalid state path=$state"
    return 1
  fi
  if ! kill -0 "$PR_WATCH_STATE_PID" 2>/dev/null; then
    say "PR-WATCH INACTIVE: removed stale state for pid=$PR_WATCH_STATE_PID"
    rm -f "$state" 2>/dev/null || true
    return 0
  fi

  expected_script="$(
    cd -- "$FKST_HOST_ROOT/Meta/StrataLint/scripts" 2>/dev/null \
      && printf '%s/%s\n' "$(pwd -P)" "pr-shepherd.sh"
  )" || expected_script=""
  actual_start="$(pr_watch_process_start "$PR_WATCH_STATE_PID")" || actual_start=""
  command="$(pr_watch_process_command "$PR_WATCH_STATE_PID")" || command=""
  loaded_blob="$(git -C "$FKST_HOST_ROOT" \
    hash-object "$PR_WATCH_STATE_LOADED_SCRIPT" 2>/dev/null)" || loaded_blob=""
  if [[ -z "$expected_script" \
      || "$PR_WATCH_STATE_CANONICAL_SCRIPT" != "$expected_script" \
      || "$actual_start" != "$PR_WATCH_STATE_PROCESS_START" \
      || "$command" != *"$PR_WATCH_STATE_LOADED_SCRIPT"* \
      || "$command" != *" watch "* \
      || "$loaded_blob" != "$PR_WATCH_STATE_LOADED_BLOB" ]]; then
    say "PR-WATCH IDENTITY UNKNOWN: live state cannot be verified pid=$PR_WATCH_STATE_PID"
    return 1
  fi
  if [[ ! "$CHECKOUT_DEV_REV" =~ ^[0-9a-f]{40}$ ]]; then
    say "PR-WATCH DESIRED IDENTITY UNKNOWN: tracking revision is unavailable"
    return 1
  fi
  desired_blob="$(git -C "$FKST_HOST_ROOT" \
    rev-parse "$CHECKOUT_DEV_REV:$relative" 2>/dev/null)" || desired_blob=""
  checkout_blob="$(git -C "$FKST_HOST_ROOT" hash-object "$expected_script" 2>/dev/null)" \
    || checkout_blob=""
  if [[ ! "$desired_blob" =~ ^[0-9a-f]{40}$ \
      || ! "$checkout_blob" =~ ^[0-9a-f]{40}$ ]]; then
    say "PR-WATCH DESIRED IDENTITY UNKNOWN: script blob cannot be derived"
    return 1
  fi
  if [[ "$PR_WATCH_STATE_LOADED_BLOB" == "$desired_blob" ]]; then
    say "PR-WATCH CURRENT (${desired_blob:0:12}; pid=$PR_WATCH_STATE_PID cycle=$PR_WATCH_STATE_CYCLE)"
    return 0
  fi
  if [[ "$checkout_blob" != "$desired_blob" ]]; then
    say "PR-WATCH RELOAD BLOCKED ${PR_WATCH_STATE_LOADED_BLOB:0:12} -> ${desired_blob:0:12}; checkout script is ${checkout_blob:0:12}"
    return 1
  fi
  say "PR-WATCH BEHIND ${PR_WATCH_STATE_LOADED_BLOB:0:12} -> ${desired_blob:0:12}; boundary reload pending"
}

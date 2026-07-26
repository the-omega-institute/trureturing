#!/usr/bin/env bash

# Process discovery and fencing helpers sourced by report-supervisor.sh.

collect_process_tree() {
  local queue=("$1")
  local index=0
  local pid
  local child
  while [[ "$index" -lt "${#queue[@]}" ]]; do
    pid="${queue[$index]}"
    index=$((index + 1))
    printf '%s\n' "$pid"
    while IFS= read -r child; do
      [[ -n "$child" ]] && queue+=("$child")
    done < <(pgrep -P "$pid" 2>/dev/null || true)
  done
}

process_exists() {
  local pid="$1"
  local stat=""
  local state=""
  local suffix=""
  kill -0 "$pid" >/dev/null 2>&1 || return 1
  if [[ -d "$PROCESS_FS_ROOT" ]]; then
    if [[ ! -r "$PROCESS_FS_ROOT/$pid/stat" ]]; then
      kill -0 "$pid" >/dev/null 2>&1 || return 1
      return 0
    fi
    stat="$(< "$PROCESS_FS_ROOT/$pid/stat")"
    suffix="${stat##*) }"
    state="${suffix%% *}"
    [[ "$state" =~ ^[A-Za-z]$ ]] || return 0
  else
    state="$(ps -o stat= -p "$pid" 2>/dev/null | awk '{$1=$1; print; exit}')" \
      || return 0
    [[ -n "$state" ]] || return 0
    state="${state:0:1}"
  fi
  [[ "$state" != "Z" && "$state" != "X" ]]
}

process_group_members_for_id() {
  local group_id="$1"
  local table=""
  [[ "$group_id" =~ ^[1-9][0-9]*$ ]] || return 1
  table="$(ps -axo pid=,pgid=,stat= 2>/dev/null)" || return 1
  awk -v group="$group_id" '
    NF == 0 {next}
    {
      rows++
      if (NF != 3 || $1 !~ /^[1-9][0-9]*$/ || $2 !~ /^[1-9][0-9]*$/ || $3 !~ /^[A-Za-z]/) {
        malformed = 1
        next
      }
      if ($2 == group && $3 !~ /^(Z|X)/) print $1
    }
    END {if (rows == 0 || malformed) exit 1}
  ' <<< "$table"
}

proc_process_has_supervisor_uid() {
  local process_dir="$1"
  local process_uid=""
  if [[ ! -r "$process_dir/status" ]]; then
    [[ -d "$process_dir" ]] && return 2
    return 1
  fi
  process_uid="$(awk '/^Uid:/ {print $2; found=1; exit} END {if (!found) exit 1}' \
    "$process_dir/status" 2>/dev/null)" || return 2
  [[ "$process_uid" =~ ^[0-9]+$ ]] || return 2
  [[ "$process_uid" == "${UID:-$(id -u)}" ]]
}

marker_processes_for_path() {
  local marker="$1"
  local process_dir fd target pid uid_result
  if [[ -d "$PROCESS_FS_ROOT" ]]; then
    for process_dir in "$PROCESS_FS_ROOT"/[1-9]*; do
      [[ -d "$process_dir" ]] || continue
      proc_process_has_supervisor_uid "$process_dir" || {
        uid_result=$?
        [[ "$uid_result" == "1" ]] && continue
        return 1
      }
      if [[ ! -r "$process_dir/fd" || ! -x "$process_dir/fd" ]]; then
        [[ -d "$process_dir" ]] && return 1
        continue
      fi
      pid="${process_dir##*/}"
      for fd in "$process_dir"/fd/*; do
        [[ -e "$fd" || -L "$fd" ]] || continue
        if ! target="$(readlink "$fd" 2>/dev/null)"; then
          [[ -e "$fd" || -L "$fd" ]] && return 1
          continue
        fi
        if [[ "$target" == "$marker" ]]; then
          printf '%s\n' "$pid"
          break
        fi
      done
    done
  else
    { lsof -F p "$marker" 2>/dev/null || true; } \
      | awk '/^p[1-9][0-9]*$/ {print substr($0, 2)}'
  fi
}

marker_processes() {
  local process_dir fd target pid candidates elapsed_window uid_result
  if [[ -d "$PROCESS_FS_ROOT" ]]; then
    for process_dir in "$PROCESS_FS_ROOT"/[1-9]*; do
      [[ -d "$process_dir" ]] || continue
      proc_process_has_supervisor_uid "$process_dir" || {
        uid_result=$?
        [[ "$uid_result" == "1" ]] && continue
        return 1
      }
      if [[ ! -r "$process_dir/fd" || ! -x "$process_dir/fd" ]]; then
        [[ -d "$process_dir" ]] && return 1
        continue
      fi
      pid="${process_dir##*/}"
      for fd in "$process_dir"/fd/*; do
        [[ -e "$fd" || -L "$fd" ]] || continue
        if ! target="$(readlink "$fd" 2>/dev/null)"; then
          [[ -e "$fd" || -L "$fd" ]] && return 1
          continue
        fi
        if [[ "$target" == "$RUN_STDOUT" \
          || "$target" == "$RUN_STDERR" \
          || "$target" == "$RUN_MARKER" ]]; then
          printf '%s\n' "$pid"
          break
        fi
      done
    done
  else
    elapsed_window=$(( ($(now_ms) - STARTED_MS) / 1000 + 5 ))
    candidates="$(ps -axo pid=,ppid=,etime= 2>/dev/null \
      | awk -v window="$elapsed_window" '
          function elapsed(value, fields, count, hour) {
            count = split(value, fields, ":")
            seconds = fields[count] + 0
            if (count >= 2) seconds += 60 * fields[count - 1]
            if (count >= 3) {
              hour = fields[count - 2]
              if (hour ~ /-/) {
                split(hour, day_hour, "-")
                seconds += 86400 * day_hour[1] + 3600 * day_hour[2]
              } else {
                seconds += 3600 * hour
              }
            }
            return seconds
          }
          $2 == 1 && elapsed($3) <= window {print $1}
        ' | paste -sd, -)"
    [[ -n "$candidates" ]] || return 0
    lsof -a -p "$candidates" -d 1,2,9 2>/dev/null \
      | awk -v stdout="$RUN_STDOUT" -v stderr="$RUN_STDERR" -v marker="$RUN_MARKER" \
          '$NF == stdout || $NF == stderr || $NF == marker {print $2}'
  fi
}

slot_lock_requires_group_proof() {
  [[ "$1" == "$SLOT_ROOT"/slot-*.lock ]]
}

stale_slot_is_quiescent() {
  local lock="$1"
  local marker=""
  local marker_pids=""
  local group_members=""
  local pid
  local group_record=""
  local group_id=""
  local leader_pid=""
  slot_lock_requires_group_proof "$lock" || return 0
  # The owner is already confirmed dead before this helper is called. A crash
  # between claiming the dev-compatible lock and publishing both producer
  # views leaves no complete proof to inspect, so retain dev's direct reclaim.
  # Once both views exist, require the stronger group + marker quiescence proof.
  [[ -e "$lock/group" && -e "$lock/marker" ]] || return 0
  [[ -f "$lock/group" ]] || return 1
  read -r group_record < "$lock/group" || return 1
  [[ "$group_record" =~ ^([1-9][0-9]*)\|([1-9][0-9]*)\|(.+)$ ]] || return 1
  group_id="${BASH_REMATCH[1]}"
  leader_pid="${BASH_REMATCH[2]}"
  [[ "$group_id" == "$leader_pid" ]] || return 1
  group_members="$(process_group_members_for_id "$group_id")" || return 1
  [[ -f "$lock/marker" ]] || return 1
  read -r marker < "$lock/marker" || return 1
  [[ "$marker" == /* && -e "$marker" ]] || return 1
  marker_pids="$(marker_processes_for_path "$marker" | sort -un)" || return 1
  while IFS= read -r pid; do
    [[ -n "$pid" ]] || continue
    [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 1
    process_exists "$pid" && return 1
  done <<< "$group_members"
  while IFS= read -r pid; do
    [[ -n "$pid" ]] || continue
    [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 1
    process_exists "$pid" && return 1
  done <<< "$marker_pids"
  return 0
}

signal_marker_processes() {
  local signal="$1"
  local pid
  supervised_processes | sort -run | while IFS= read -r pid; do
    [[ "$pid" =~ ^[1-9][0-9]*$ \
      && "$pid" != "$$" \
      && "$pid" != "$STDOUT_RELAY_PID" \
      && "$pid" != "$STDERR_RELAY_PID" ]] || continue
    kill "-$signal" "$pid" >/dev/null 2>&1 || true
  done
  return 0
}

sample_process_tree() {
  local pid rss fd
  local rss_total=0
  local fd_total=0
  while IFS= read -r pid; do
    [[ -n "$pid" \
      && "$pid" != "$STDOUT_RELAY_PID" \
      && "$pid" != "$STDERR_RELAY_PID" ]] || continue
    rss="$( { ps -o rss= -p "$pid" 2>/dev/null || true; } | awk '{sum += $1} END {print sum + 0}')"
    rss_total=$((rss_total + rss))
    if [[ -d "$PROCESS_FS_ROOT/$pid/fd" ]]; then
      fd="$( { find "$PROCESS_FS_ROOT/$pid/fd" -mindepth 1 -maxdepth 1 -print 2>/dev/null || true; } | awk 'END {print NR + 0}')"
    elif command -v lsof >/dev/null 2>&1; then
      fd="$( { lsof -a -p "$pid" -d 0-999999 2>/dev/null || true; } | awk 'NR > 1 {count++} END {print count + 0}')"
    else
      fd=0
    fi
    fd_total=$((fd_total + fd))
  done < <(process_tree_members)
  if [[ "$rss_total" -gt "$RSS_PEAK_KB" ]]; then RSS_PEAK_KB="$rss_total"; fi
  if [[ "$fd_total" -gt "$FD_PEAK" ]]; then FD_PEAK="$fd_total"; fi
}

terminate_process_group() {
  local group_id="$1"
  signal_marker_processes TERM || true
  kill -TERM -- "-$group_id" >/dev/null 2>&1 || true
  sleep 0.2 || true
  signal_marker_processes KILL || true
  kill -KILL -- "-$group_id" >/dev/null 2>&1 || true
  return 0
}

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

process_group_members_for_id() {
  local group_id="$1"
  local table=""
  [[ "$group_id" =~ ^[1-9][0-9]*$ ]] || return 1
  table="$(ps -axo pid=,pgid=,stat= 2>/dev/null)" || return 1
  awk -v group="$group_id" '
    $2 == group && $3 !~ /^Z/ {print $1}
  ' <<< "$table"
}

marker_processes_for_path() {
  local marker="$1"
  local process_dir fd target pid
  if [[ -d /proc ]]; then
    for process_dir in /proc/[1-9]*; do
      [[ -d "$process_dir/fd" ]] || continue
      pid="${process_dir##*/}"
      # Workers inherit the two relay pipes and the dedicated marker on fd 9.
      for fd in "$process_dir"/fd/1 "$process_dir"/fd/2 "$process_dir"/fd/9; do
        [[ -e "$fd" || -L "$fd" ]] || continue
        target="$(readlink "$fd" 2>/dev/null || true)"
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
  local process_dir fd target pid candidates elapsed_window
  if [[ -d /proc ]]; then
    for process_dir in /proc/[1-9]*; do
      [[ -d "$process_dir/fd" ]] || continue
      pid="${process_dir##*/}"
      for fd in "$process_dir"/fd/1 "$process_dir"/fd/2 "$process_dir"/fd/9; do
        [[ -e "$fd" || -L "$fd" ]] || continue
        target="$(readlink "$fd" 2>/dev/null || true)"
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

slot_lock_requires_fence() {
  [[ "$1" == "$SLOT_ROOT"/slot-*.lock ]]
}

fence_stale_slot() {
  local lock="$1"
  local marker=""
  local marker_pids=""
  local group_members=""
  local pid
  local group_record=""
  local group_id=""
  local leader_pid=""
  local expected_start=""
  local actual_start=""
  slot_lock_requires_fence "$lock" || return 0
  [[ -f "$lock/group" ]] || return 1
  read -r group_record < "$lock/group" || return 1
  [[ "$group_record" =~ ^([1-9][0-9]*)\|([1-9][0-9]*)\|(.+)$ ]] || return 1
  group_id="${BASH_REMATCH[1]}"
  leader_pid="${BASH_REMATCH[2]}"
  expected_start="${BASH_REMATCH[3]}"
  [[ "$group_id" == "$leader_pid" ]] || return 1
  if process_exists "$leader_pid"; then
    [[ "$expected_start" != "unknown" ]] || return 1
    actual_start="$(process_start_identity "$leader_pid")"
    [[ -n "$actual_start" && "$actual_start" == "$expected_start" ]] || return 1
  fi
  group_members="$(process_group_members_for_id "$group_id")" || return 1
  if [[ -f "$lock/marker" ]]; then
    read -r marker < "$lock/marker" || return 1
    [[ "$marker" == /* && -e "$marker" ]] || return 1
    marker_pids="$(marker_processes_for_path "$marker" | sort -un)" || return 1
  fi
  while IFS= read -r pid; do
    [[ "$pid" =~ ^[1-9][0-9]*$ && "$pid" != "$$" ]] || continue
    kill -TERM "$pid" >/dev/null 2>&1 || true
  done <<< "$marker_pids"
  if [[ -n "$group_members" ]]; then
    kill -TERM -- "-$group_id" >/dev/null 2>&1 || true
  fi
  sleep 0.5 || true
  group_members="$(process_group_members_for_id "$group_id")" || return 1
  while IFS= read -r pid; do
    [[ "$pid" =~ ^[1-9][0-9]*$ && "$pid" != "$$" ]] || continue
    kill -KILL "$pid" >/dev/null 2>&1 || true
  done <<< "$marker_pids"
  if [[ -n "$group_members" ]]; then
    kill -KILL -- "-$group_id" >/dev/null 2>&1 || true
  fi
  sleep 0.1 || true
  group_members="$(process_group_members_for_id "$group_id")" || return 1
  [[ -z "$group_members" ]] || return 1
  if [[ -n "$marker" ]]; then
    marker_pids="$(marker_processes_for_path "$marker" | sort -un)" || return 1
    [[ -z "$marker_pids" ]] || return 1
  fi
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
    if [[ -d "/proc/$pid/fd" ]]; then
      fd="$( { find "/proc/$pid/fd" -mindepth 1 -maxdepth 1 -print 2>/dev/null || true; } | awk 'END {print NR + 0}')"
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

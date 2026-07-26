#!/usr/bin/env bash

# Process discovery and fencing helpers sourced by report-supervisor.sh.

collect_process_tree() {
  if [[ -d "$PROCESS_FS_ROOT" ]]; then
    linux_process_tree "$1"
    return
  fi
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

linux_process_tree() {
  local root="$1"
  local process_dir pid snapshot state remainder parent_pid row child
  local index=0
  local seen=" $root "
  local -a rows=()
  local -a queue=("$root")
  for process_dir in "$PROCESS_FS_ROOT"/[1-9]*; do
    [[ -d "$process_dir" ]] || continue
    pid="${process_dir##*/}"
    snapshot="$(linux_proc_stat_snapshot "$pid")" || continue
    state="${snapshot%%|*}"
    [[ "$state" != "Z" && "$state" != "X" ]] || continue
    remainder="${snapshot#*|}"
    parent_pid="${remainder%%|*}"
    rows+=("$pid|$parent_pid")
  done
  while [[ "$index" -lt "${#queue[@]}" ]]; do
    pid="${queue[$index]}"
    index=$((index + 1))
    printf '%s\n' "$pid"
    for row in "${rows[@]}"; do
      parent_pid="${row#*|}"
      [[ "$parent_pid" == "$pid" ]] || continue
      child="${row%%|*}"
      case "$seen" in
        *" $child "*) ;;
        *)
          seen+="$child "
          queue+=("$child")
          ;;
      esac
    done
  done
}

supervised_processes() {
  {
    if [[ -n "$CHILD_PID" ]]; then collect_process_tree "$CHILD_PID"; fi
    marker_processes
  } | sort -un
}

process_tree_members() {
  if [[ -n "$CHILD_PID" ]]; then collect_process_tree "$CHILD_PID" | sort -un; fi
}

cpu_time_centiseconds() {
  local raw=""
  raw="$(ps -o time= -p "$1" 2>/dev/null | awk '{$1=$1; print; exit}')"
  [[ -n "$raw" ]] || return 1
  awk -v value="$raw" '
    BEGIN {
      days = 0
      if (index(value, "-") > 0) {
        split(value, day_parts, "-")
        days = day_parts[1] + 0
        value = day_parts[2]
      }
      count = split(value, fields, ":")
      seconds = fields[count] + 0
      if (count >= 2) seconds += 60 * (fields[count - 1] + 0)
      if (count >= 3) seconds += 3600 * (fields[count - 2] + 0)
      printf "%.0f\n", 100 * (86400 * days + seconds)
    }
  '
}

cpu_progress_snapshot() {
  local pid ticks members exists_rc
  local total=0
  members="$(process_group_members_for_id "$PROCESS_GROUP_ID")" || return 1
  while IFS= read -r pid; do
    [[ -n "$pid" \
      && "$pid" != "$STDOUT_RELAY_PID" \
      && "$pid" != "$STDERR_RELAY_PID" ]] || continue
    if ! ticks="$(cpu_time_centiseconds "$pid")"; then
      if process_exists "$pid"; then
        return 1
      else
        exists_rc=$?
        [[ "$exists_rc" == "1" ]] && continue
        return 1
      fi
    fi
    [[ "$ticks" =~ ^[0-9]+$ ]] || return 1
    total=$((total + ticks))
  done <<< "$members"
  printf '%s\n' "$total"
}

linux_proc_stat_snapshot() {
  local pid="$1"
  local path="$PROCESS_FS_ROOT/$pid/stat"
  local stat=""
  local suffix=""
  local -a fields=()
  [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 2
  if [[ ! -r "$path" ]]; then
    [[ -d "$PROCESS_FS_ROOT/$pid" ]] && return 2
    return 1
  fi
  IFS= read -r stat < "$path" || return 2
  [[ "$stat" == "$pid ("* && "$stat" == *") "* ]] || return 2
  suffix="${stat##*) }"
  read -r -a fields <<< "$suffix"
  [[ "${#fields[@]}" -ge 20 \
    && "${fields[0]}" =~ ^[A-Za-z]$ \
    && "${fields[1]}" =~ ^[0-9]+$ \
    && "${fields[2]}" =~ ^[0-9]+$ \
    && "${fields[19]}" =~ ^[1-9][0-9]*$ ]] || return 2
  printf '%s|%s|%s|%s\n' \
    "${fields[0]}" "${fields[1]}" "${fields[2]}" "${fields[19]}"
}

process_start_identity() {
  local snapshot=""
  if [[ -d "$PROCESS_FS_ROOT" ]]; then
    snapshot="$(linux_proc_stat_snapshot "$1")" || return 1
    printf '%s\n' "${snapshot##*|}"
  else
    ps -o lstart= -p "$1" 2>/dev/null | awk '{$1=$1; print; exit}'
  fi
}

process_exists() {
  local pid="$1"
  local snapshot=""
  local state=""
  if [[ -d "$PROCESS_FS_ROOT" ]]; then
    if snapshot="$(linux_proc_stat_snapshot "$pid")"; then
      :
    else
      return $?
    fi
    state="${snapshot%%|*}"
  else
    kill -0 "$pid" >/dev/null 2>&1 || return 1
    state="$(ps -o stat= -p "$pid" 2>/dev/null | awk '{$1=$1; print; exit}')" \
      || return 0
    [[ -n "$state" ]] || return 0
    state="${state:0:1}"
  fi
  [[ "$state" != "Z" && "$state" != "X" ]]
}

process_group_members_for_id() {
  local group_id="$1"
  local process_dir=""
  local pid=""
  local snapshot=""
  local state=""
  local remainder=""
  local process_group=""
  local table=""
  [[ "$group_id" =~ ^[1-9][0-9]*$ ]] || return 1
  if [[ -d "$PROCESS_FS_ROOT" ]]; then
    for process_dir in "$PROCESS_FS_ROOT"/[1-9]*; do
      [[ -d "$process_dir" ]] || continue
      pid="${process_dir##*/}"
      if ! snapshot="$(linux_proc_stat_snapshot "$pid")"; then
        [[ -d "$process_dir" ]] && return 1
        continue
      fi
      state="${snapshot%%|*}"
      remainder="${snapshot#*|}"
      remainder="${remainder#*|}"
      process_group="${remainder%%|*}"
      if [[ "$process_group" == "$group_id" \
        && "$state" != "Z" \
        && "$state" != "X" ]]; then
        printf '%s\n' "$pid"
      fi
    done
    return 0
  fi
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

linux_process_candidates() {
  local group_id="$1"
  local leader_start="$2"
  local process_dir=""
  local pid=""
  local snapshot=""
  local state=""
  local remainder=""
  local parent_pid=""
  local process_group=""
  local starttime=""
  [[ "$group_id" =~ ^[1-9][0-9]*$ \
    && "$leader_start" =~ ^[1-9][0-9]*$ ]] || return 1
  for process_dir in "$PROCESS_FS_ROOT"/[1-9]*; do
    [[ -d "$process_dir" ]] || continue
    pid="${process_dir##*/}"
    if ! snapshot="$(linux_proc_stat_snapshot "$pid")"; then
      [[ -d "$process_dir" ]] && return 1
      continue
    fi
    state="${snapshot%%|*}"
    remainder="${snapshot#*|}"
    parent_pid="${remainder%%|*}"
    remainder="${remainder#*|}"
    process_group="${remainder%%|*}"
    starttime="${remainder##*|}"
    [[ "$state" != "Z" && "$state" != "X" ]] || continue
    if [[ "$process_group" == "$group_id" \
      || ( "$parent_pid" == "1" && "$starttime" -ge "$leader_start" ) ]]; then
      printf '%s\n' "$pid"
    fi
  done
}

marker_processes_for_path() {
  local marker="$1"
  local candidates="${2:-}"
  local process_dir fd target pid
  if [[ -d "$PROCESS_FS_ROOT" ]]; then
    for pid in $candidates; do
      [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 1
      process_dir="$PROCESS_FS_ROOT/$pid"
      [[ -d "$process_dir" ]] || continue
      if [[ ! -r "$process_dir/fd" || ! -x "$process_dir/fd" ]]; then
        [[ -d "$process_dir" ]] && return 1
        continue
      fi
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
  local candidates elapsed_window
  if [[ -d "$PROCESS_FS_ROOT" ]]; then
    candidates="$(linux_process_candidates \
      "$PROCESS_GROUP_ID" "$PROCESS_GROUP_START_IDENTITY")" || return 1
    {
      marker_processes_for_path "$RUN_STDOUT" "$candidates"
      marker_processes_for_path "$RUN_STDERR" "$candidates"
      marker_processes_for_path "$RUN_MARKER" "$candidates"
    } | sort -un
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
  local leader_start=""
  local candidates=""
  local exists_rc=0
  slot_lock_requires_group_proof "$lock" || return 0
  # The owner is already confirmed dead before this helper is called. A crash
  # between claiming the dev-compatible lock and publishing both producer
  # views leaves no complete proof to inspect, so retain dev's direct reclaim.
  # Once both views exist, require the stronger group + marker quiescence proof.
  [[ -e "$lock/group" && -e "$lock/marker" ]] || return 0
  [[ -f "$lock/group" ]] || return 2
  read -r group_record < "$lock/group" || return 2
  [[ "$group_record" =~ ^([1-9][0-9]*)\|([1-9][0-9]*)\|(.+)$ ]] || return 2
  group_id="${BASH_REMATCH[1]}"
  leader_pid="${BASH_REMATCH[2]}"
  leader_start="${BASH_REMATCH[3]}"
  [[ "$group_id" == "$leader_pid" ]] || return 2
  group_members="$(process_group_members_for_id "$group_id")" || return 2
  [[ -f "$lock/marker" ]] || return 2
  read -r marker < "$lock/marker" || return 2
  [[ "$marker" == /* && -e "$marker" ]] || return 2
  if [[ -d "$PROCESS_FS_ROOT" ]]; then
    candidates="$(linux_process_candidates "$group_id" "$leader_start")" || return 2
  else
    candidates="$group_members"
  fi
  marker_pids="$(marker_processes_for_path "$marker" "$candidates" | sort -un)" || return 2
  while IFS= read -r pid; do
    [[ -n "$pid" ]] || continue
    [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 2
    if process_exists "$pid"; then
      return 1
    else
      exists_rc=$?
      [[ "$exists_rc" == "2" ]] && return 2
    fi
  done <<< "$group_members"
  while IFS= read -r pid; do
    [[ -n "$pid" ]] || continue
    [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 2
    if process_exists "$pid"; then
      return 1
    else
      exists_rc=$?
      [[ "$exists_rc" == "2" ]] && return 2
    fi
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

remember_process_candidate() {
  local pid="$1"
  local identity=""
  [[ "$pid" =~ ^[1-9][0-9]*$ && -n "$PROCESS_CANDIDATES_FILE" ]] || return 0
  identity="$(process_start_identity "$pid")" || return 0
  [[ -n "$identity" ]] || return 0
  grep -Fqx -- "$pid|$identity" "$PROCESS_CANDIDATES_FILE" 2>/dev/null \
    || printf '%s|%s\n' "$pid" "$identity" >> "$PROCESS_CANDIDATES_FILE"
}

record_process_candidates() {
  local pid
  while IFS= read -r pid; do
    remember_process_candidate "$pid"
  done
}

record_supervised_processes() {
  record_process_candidates < <(supervised_processes || true)
}

signal_recorded_processes() {
  local signal="$1"
  local pid identity current_identity
  [[ -f "$PROCESS_CANDIDATES_FILE" ]] || return 0
  while IFS='|' read -r pid identity; do
    [[ "$pid" =~ ^[1-9][0-9]*$ \
      && -n "$identity" \
      && "$pid" != "$$" \
      && "$pid" != "$STDOUT_RELAY_PID" \
      && "$pid" != "$STDERR_RELAY_PID" ]] || continue
    current_identity="$(process_start_identity "$pid")" || continue
    [[ "$current_identity" == "$identity" ]] || continue
    kill "-$signal" "$pid" >/dev/null 2>&1 || true
  done < <(sort -t '|' -k1,1nr "$PROCESS_CANDIDATES_FILE")
  return 0
}

sample_process_tree() {
  local pid rss fd members
  local rss_total=0
  local fd_total=0
  members="$(process_tree_members || true)"
  record_process_candidates <<< "$members"
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
  done <<< "$members"
  if [[ "$rss_total" -gt "$RSS_PEAK_KB" ]]; then RSS_PEAK_KB="$rss_total"; fi
  if [[ "$fd_total" -gt "$FD_PEAK" ]]; then FD_PEAK="$fd_total"; fi
}

terminate_process_group() {
  local group_id="$1"
  record_supervised_processes
  signal_recorded_processes TERM || true
  signal_marker_processes TERM || true
  kill -TERM -- "-$group_id" >/dev/null 2>&1 || true
  sleep 0.2 || true
  record_supervised_processes
  signal_recorded_processes KILL || true
  signal_marker_processes KILL || true
  kill -KILL -- "-$group_id" >/dev/null 2>&1 || true
  return 0
}

#!/usr/bin/env bash

# PREREGISTERED_RESOURCE_FORENSICS_CRITERIA_BEGIN
# `OOM_CONFIRMED`:同一 job 的完整样本中,later `memory_events_oom` 或 `memory_events_oom_kill` 严格大于 baseline。
# `DISK_CONFIRMED`:同一精确 mount 的 baseline 可用 block/inode 为正,且 later 对应值为 0。
# `LOCAL_STALL_OBSERVED`:完整的相邻样本覆盖连续 600 秒,每段 `100 * Δprocess_cpu_seconds / Δutc_epoch_seconds < 5`,
# 且每个样本 `process_count > 0`,同时 `OOM_CONFIRMED` 与 `DISK_CONFIRMED` 均不命中。只允许命名为 stall,不得升级为 "deadlock confirmed"。
# `EXTERNAL_UNATTRIBUTED`:`run=failure` 且 `job=failure` 且该 step `=cancelled`,并且上述三种本地分类均不命中。
# PREREGISTERED_RESOURCE_FORENSICS_CRITERIA_END

resource_observation_emit_criteria() {
  printf '%s\n' 'RESOURCE_OBSERVATION_CRITERIA version=1 stall_cpu_threshold_percent=5 stall_window_seconds=600 stall_algorithm=100*delta_process_cpu_seconds/delta_utc_epoch_seconds<5_for_every_adjacent_interval_in_contiguous_600_seconds stall_sample_predicate=all_fields_available_and_process_count>0 stall_delta_predicate=delta_utc_epoch_seconds>0_and_delta_process_cpu_seconds>=0 stall_exclusions=OOM_CONFIRMED_or_DISK_CONFIRMED observer_exclusion=sampler_pid_and_descendants oom_algorithm=later_oom_or_oom_kill_greater_than_baseline disk_algorithm=baseline_positive_then_later_zero_on_same_exact_mount external_algorithm=run_failure_and_job_failure_and_step_cancelled_and_no_local_classification'
}

resource_observation_number_or_unknown() {
  local value="${1:-}"
  if [[ "$value" =~ ^[0-9]+$ ]]; then printf '%s' "$value"; else printf 'unknown'; fi
}

resource_observation_value_or_unavailable() {
  local value="${1:-}"
  if [[ -n "$value" ]]; then printf '%s' "$value"; else printf 'UNAVAILABLE'; fi
}

resource_disk_free_kb() {
  local root="$1"
  df -Pk "$root" 2>/dev/null \
    | awk 'NR > 1 { value=$4 } END { if (value ~ /^[0-9]+$/) print value }' \
    || true
}

resource_fd_soft_limit() {
  local value=""
  value="$(ulimit -Sn 2>/dev/null || true)"
  resource_observation_number_or_unknown "$value"
}

resource_observation_read_file() {
  local path="$1"
  local value=""
  if [[ -r "$path" ]]; then
    IFS= read -r value < "$path" || true
  fi
  resource_observation_value_or_unavailable "$value"
}

resource_observation_cgroup_path() {
  local root_pid="$1"
  local proc_root="${RESOURCE_OBSERVATION_PROC_ROOT:-/proc}"
  local cgroup_file="$proc_root/$root_pid/cgroup"
  local value=""
  if [[ -r "$cgroup_file" ]]; then
    value="$(awk '/^0::/ { print substr($0, 4); exit }' "$cgroup_file" 2>/dev/null || true)"
  fi
  resource_observation_value_or_unavailable "$value"
}

resource_observation_cgroup_root() {
  local findmnt_command="${RESOURCE_OBSERVATION_FINDMNT_COMMAND:-findmnt}"
  local value=""
  if [[ -n "${RESOURCE_OBSERVATION_CGROUP_ROOT+x}" ]]; then
    resource_observation_value_or_unavailable "$RESOURCE_OBSERVATION_CGROUP_ROOT"
    return 0
  fi
  value="$("$findmnt_command" -n -t cgroup2 -o TARGET 2>/dev/null \
    | awk 'NF { print; exit }' || true)"
  if [[ -z "$value" && -d /sys/fs/cgroup ]]; then value="/sys/fs/cgroup"; fi
  resource_observation_value_or_unavailable "$value"
}

resource_observation_memory_events() {
  local path="$1"
  local value=""
  if [[ -r "$path" ]]; then
    value="$(awk '
      NF >= 2 {
        if (result != "") result = result ","
        result = result $1 ":" $2
      }
      END { if (result != "") print result }
    ' "$path" 2>/dev/null || true)"
  fi
  resource_observation_value_or_unavailable "$value"
}

resource_observation_memory_event() {
  local path="$1"
  local event_name="$2"
  local value=""
  if [[ -r "$path" ]]; then
    value="$(awk -v event_name="$event_name" \
      '$1 == event_name && $2 ~ /^[0-9]+$/ { print $2; exit }' \
      "$path" 2>/dev/null || true)"
  fi
  resource_observation_value_or_unavailable "$value"
}

resource_observation_mount_values() {
  local path="$1"
  local findmnt_command="${RESOURCE_OBSERVATION_FINDMNT_COMMAND:-findmnt}"
  local df_command="${RESOURCE_OBSERVATION_DF_COMMAND:-df}"
  local mount=""
  local available_blocks=""
  local available_inodes=""
  if [[ -n "$path" ]]; then
    mount="$("$findmnt_command" -n -T "$path" -o TARGET 2>/dev/null \
      | awk 'NF { print; exit }' || true)"
  fi
  if [[ -n "$mount" ]]; then
    available_blocks="$("$df_command" -Pk "$mount" 2>/dev/null \
      | awk 'NR > 1 { value=$4 } END { if (value ~ /^[0-9]+$/) print value }' \
      || true)"
    available_inodes="$("$df_command" -Pi "$mount" 2>/dev/null \
      | awk 'NR > 1 { value=$4 } END { if (value ~ /^[0-9]+$/) print value }' \
      || true)"
  fi
  printf '%s\t%s\t%s\n' \
    "$(resource_observation_value_or_unavailable "$mount")" \
    "$(resource_observation_value_or_unavailable "$available_blocks")" \
    "$(resource_observation_value_or_unavailable "$available_inodes")"
}

resource_observation_process_values() {
  local root_pid="$1"
  local observer_pid="${2:-}"
  local ps_command="${RESOURCE_OBSERVATION_PS_COMMAND:-ps}"
  local ps_output=""
  ps_output="$("$ps_command" -eo pid=,ppid=,pgid=,rss=,time= 2>/dev/null || true)"
  printf '%s\n' "$ps_output" | awk -v root_pid="$root_pid" -v observer_pid="$observer_pid" '
    function cpu_seconds(value, day_parts, time_parts, day_count, time_count, days) {
      days = 0
      day_count = split(value, day_parts, "-")
      if (day_count == 2) {
        if (day_parts[1] !~ /^[0-9]+$/) return -1
        days = day_parts[1]
        value = day_parts[2]
      } else if (day_count != 1) {
        return -1
      }
      time_count = split(value, time_parts, ":")
      if (time_count == 3 && time_parts[1] ~ /^[0-9]+$/ && time_parts[2] ~ /^[0-9]+$/ && time_parts[3] ~ /^[0-9]+$/)
        return days * 86400 + time_parts[1] * 3600 + time_parts[2] * 60 + time_parts[3]
      if (time_count == 2 && time_parts[1] ~ /^[0-9]+$/ && time_parts[2] ~ /^[0-9]+$/)
        return days * 86400 + time_parts[1] * 60 + time_parts[2]
      return -1
    }
    $1 ~ /^[0-9]+$/ && $2 ~ /^[0-9]+$/ && $3 ~ /^[0-9]+$/ && $4 ~ /^[0-9]+$/ && NF >= 5 {
      count += 1
      pid[count] = $1
      ppid[count] = $2
      pgid[count] = $3
      rss[count] = $4
      cpu[count] = $5
      present[$1] = 1
    }
    END {
      if (!(root_pid in present)) {
        print "UNAVAILABLE\tUNAVAILABLE\tUNAVAILABLE"
        exit
      }
      included[root_pid] = 1
      changed = 1
      while (changed) {
        changed = 0
        for (i = 1; i <= count; i += 1) {
          if (!(pid[i] in included) && (ppid[i] in included)) {
            included[pid[i]] = 1
            changed = 1
          }
        }
      }
      if (observer_pid ~ /^[0-9]+$/ && (observer_pid in present)) {
        excluded[observer_pid] = 1
        changed = 1
        while (changed) {
          changed = 0
          for (i = 1; i <= count; i += 1) {
            if (!(pid[i] in excluded) && (ppid[i] in excluded)) {
              excluded[pid[i]] = 1
              changed = 1
            }
          }
        }
      }
      process_count = 0
      process_cpu_seconds = 0
      cpu_available = 1
      tree = ""
      for (i = 1; i <= count; i += 1) {
        if ((pid[i] in included) && !(pid[i] in excluded)) {
          if (tree != "") tree = tree ";"
          tree = tree "pid:" pid[i] ",ppid:" ppid[i] ",pgid:" pgid[i] ",rss_kb:" rss[i] ",cpu:" cpu[i]
          process_count += 1
          seconds = cpu_seconds(cpu[i])
          if (seconds < 0) cpu_available = 0
          else process_cpu_seconds += seconds
        }
      }
      if (process_count == 0) print "UNAVAILABLE\tUNAVAILABLE\tUNAVAILABLE"
      else if (!cpu_available) print process_count "\tUNAVAILABLE\t" tree
      else print process_count "\t" process_cpu_seconds "\t" tree
    }
  '
}

resource_observe_sample() {
  local sequence="$1"
  local root_pid="$2"
  local workspace="$3"
  local runner_temp="$4"
  local phase="${5:-periodic}"
  local observer_pid="${6:-}"
  local date_command="${RESOURCE_OBSERVATION_DATE_COMMAND:-date}"
  local timestamp=""
  local utc_epoch_seconds=""
  local cgroup_path=""
  local cgroup_root=""
  local cgroup_directory=""
  local memory_current="UNAVAILABLE"
  local memory_peak="UNAVAILABLE"
  local memory_max="UNAVAILABLE"
  local memory_events="UNAVAILABLE"
  local memory_events_oom="UNAVAILABLE"
  local memory_events_oom_kill="UNAVAILABLE"
  local workspace_mount="UNAVAILABLE"
  local workspace_blocks="UNAVAILABLE"
  local workspace_inodes="UNAVAILABLE"
  local runner_temp_mount="UNAVAILABLE"
  local runner_temp_blocks="UNAVAILABLE"
  local runner_temp_inodes="UNAVAILABLE"
  local tmp_mount="UNAVAILABLE"
  local tmp_blocks="UNAVAILABLE"
  local tmp_inodes="UNAVAILABLE"
  local process_count="UNAVAILABLE"
  local process_cpu_seconds="UNAVAILABLE"
  local process_tree="UNAVAILABLE"
  local process_values=""
  local sample_status=0

  timestamp="$("$date_command" -u +'%Y-%m-%dT%H:%M:%SZ' 2>/dev/null || true)"
  timestamp="$(resource_observation_value_or_unavailable "$timestamp")"
  utc_epoch_seconds="$("$date_command" -u +'%s' 2>/dev/null || true)"
  utc_epoch_seconds="$(resource_observation_value_or_unavailable "$utc_epoch_seconds")"
  cgroup_path="$(resource_observation_cgroup_path "$root_pid")"
  cgroup_root="$(resource_observation_cgroup_root)"
  if [[ "$cgroup_path" != "UNAVAILABLE" && "$cgroup_root" != "UNAVAILABLE" ]]; then
    cgroup_directory="${cgroup_root%/}${cgroup_path}"
    memory_current="$(resource_observation_read_file "$cgroup_directory/memory.current")"
    memory_peak="$(resource_observation_read_file "$cgroup_directory/memory.peak")"
    memory_max="$(resource_observation_read_file "$cgroup_directory/memory.max")"
    memory_events="$(resource_observation_memory_events "$cgroup_directory/memory.events")"
    memory_events_oom="$(resource_observation_memory_event "$cgroup_directory/memory.events" oom)"
    memory_events_oom_kill="$(resource_observation_memory_event "$cgroup_directory/memory.events" oom_kill)"
  fi

  IFS=$'\t' read -r workspace_mount workspace_blocks workspace_inodes \
    <<< "$(resource_observation_mount_values "$workspace")"
  IFS=$'\t' read -r runner_temp_mount runner_temp_blocks runner_temp_inodes \
    <<< "$(resource_observation_mount_values "$runner_temp")"
  IFS=$'\t' read -r tmp_mount tmp_blocks tmp_inodes \
    <<< "$(resource_observation_mount_values /tmp)"
  process_values="$(resource_observation_process_values "$root_pid" "$observer_pid")"
  IFS=$'\t' read -r process_count process_cpu_seconds process_tree <<< "$process_values"

  printf 'RESOURCE_SAMPLE sequence=%s phase=%s utc=%s utc_epoch_seconds=%s cgroup_path=%s memory_current=%s memory_peak=%s memory_max=%s memory_events=%s memory_events_oom=%s memory_events_oom_kill=%s workspace_mount=%s workspace_available_blocks_1k=%s workspace_available_inodes=%s runner_temp_mount=%s runner_temp_available_blocks_1k=%s runner_temp_available_inodes=%s tmp_mount=%s tmp_available_blocks_1k=%s tmp_available_inodes=%s process_count=%s process_cpu_seconds=%s process_tree=%s\n' \
    "$sequence" "$phase" "$timestamp" "$utc_epoch_seconds" "$cgroup_path" "$memory_current" "$memory_peak" "$memory_max" \
    "$memory_events" "$memory_events_oom" "$memory_events_oom_kill" \
    "$workspace_mount" "$workspace_blocks" "$workspace_inodes" \
    "$runner_temp_mount" "$runner_temp_blocks" "$runner_temp_inodes" \
    "$tmp_mount" "$tmp_blocks" "$tmp_inodes" "$process_count" "$process_cpu_seconds" "$process_tree"

  local value=""
  for value in \
    "$timestamp" "$utc_epoch_seconds" "$cgroup_path" "$memory_current" "$memory_peak" "$memory_max" \
    "$memory_events" "$memory_events_oom" "$memory_events_oom_kill" \
    "$workspace_mount" "$workspace_blocks" "$workspace_inodes" \
    "$runner_temp_mount" "$runner_temp_blocks" "$runner_temp_inodes" \
    "$tmp_mount" "$tmp_blocks" "$tmp_inodes" \
    "$process_count" "$process_cpu_seconds" "$process_tree"; do
    if [[ "$value" == "UNAVAILABLE" || -z "$value" ]]; then sample_status=1; fi
  done
  if [[ "$sample_status" -ne 0 ]]; then
    printf 'RESOURCE_OBSERVATION_SAMPLE status=UNAVAILABLE sequence=%s phase=%s reason=partial-collection\n' \
      "$sequence" "$phase"
  fi
  return "$sample_status"
}

resource_observe_periodically() {
  local root_pid="$1"
  local workspace="$2"
  local runner_temp="$3"
  local interval="${4:-30}"
  local observer_pid="${5:-${BASHPID:-$$}}"
  local sequence=1
  local sleep_pid=""
  local failed_samples=0
  if ! [[ "$interval" =~ ^[1-9][0-9]*$ ]]; then interval=30; fi

  resource_observation_stop_sleep() {
    if [[ -n "${sleep_pid:-}" ]]; then
      kill "$sleep_pid" 2>/dev/null || true
      wait "$sleep_pid" 2>/dev/null || true
    fi
  }
  resource_observation_finish_periodic() {
    local signal_name="${1:-none}"
    resource_observation_stop_sleep
    trap - HUP INT TERM
    if [[ "$failed_samples" -ne 0 ]]; then
      printf 'RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE reason=sample-failures failed_samples=%s signal=%s\n' \
        "$failed_samples" "$signal_name"
      exit 1
    fi
    exit 0
  }
  trap 'resource_observation_finish_periodic HUP' HUP
  trap 'resource_observation_finish_periodic INT' INT
  trap 'resource_observation_finish_periodic TERM' TERM
  while true; do
    if ! resource_observe_sample "$sequence" "$root_pid" "$workspace" "$runner_temp" periodic "$observer_pid"; then
      failed_samples=$((failed_samples + 1))
    fi
    sequence=$((sequence + 1))
    sleep "$interval" &
    sleep_pid=$!
    wait "$sleep_pid" || break
    sleep_pid=""
  done
  trap - HUP INT TERM
  if [[ "$failed_samples" -ne 0 ]]; then
    printf 'RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE reason=sample-failures failed_samples=%s signal=none\n' \
      "$failed_samples"
    return 1
  fi
  return 0
}

resource_observation_handle_signal() {
  local signal_name="$1"
  local prior_status="$2"
  local root_pid="$3"
  local workspace="$4"
  local runner_temp="$5"
  local observer_pid="${6:-}"
  printf 'RESOURCE_OBSERVATION_SIGNAL status=OBSERVED signal=%s\n' "$signal_name"
  resource_observe_sample 0 "$root_pid" "$workspace" "$runner_temp" "signal-$signal_name" "$observer_pid" || true
  return "$prior_status"
}

resource_observe_run_periodic() {
  local sampler_pid=""
  local sampler_status=0
  local command_status=0
  local had_errexit=0
  local previous_hup=""
  local previous_int=""
  local previous_term=""
  local root_pid="$$"
  local workspace="${GITHUB_WORKSPACE:-}"
  local runner_temp="${RUNNER_TEMP:-}"
  if [[ $# -eq 0 ]]; then return 2; fi

  resource_observation_emit_criteria
  resource_observe_sample 0 "$root_pid" "$workspace" "$runner_temp" baseline "" || true
  previous_hup="$(trap -p HUP || true)"
  previous_int="$(trap -p INT || true)"
  previous_term="$(trap -p TERM || true)"
  trap 'resource_observation_handle_signal HUP "$?" "$root_pid" "$workspace" "$runner_temp" "$sampler_pid"' HUP
  trap 'resource_observation_handle_signal INT "$?" "$root_pid" "$workspace" "$runner_temp" "$sampler_pid"' INT
  trap 'resource_observation_handle_signal TERM "$?" "$root_pid" "$workspace" "$runner_temp" "$sampler_pid"' TERM
  resource_observe_periodically \
    "$root_pid" \
    "$workspace" \
    "$runner_temp" \
    "${RESOURCE_OBSERVATION_INTERVAL_SECONDS:-30}" &
  sampler_pid=$!
  if [[ $- == *e* ]]; then
    had_errexit=1
    set +e
    (
      set -e
      "$@"
    )
    command_status=$?
  else
    "$@"
    command_status=$?
  fi

  kill "$sampler_pid" 2>/dev/null || true
  if wait "$sampler_pid" 2>/dev/null; then
    sampler_status=0
  else
    sampler_status=$?
  fi
  if [[ "$sampler_status" -ne 0 ]]; then
    printf 'RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE exit=%s\n' "$sampler_status"
  fi
  resource_observe_sample 0 "$root_pid" "$workspace" "$runner_temp" final "" || true
  trap - HUP INT TERM
  if [[ -n "$previous_hup" ]]; then eval "$previous_hup"; fi
  if [[ -n "$previous_int" ]]; then eval "$previous_int"; fi
  if [[ -n "$previous_term" ]]; then eval "$previous_term"; fi
  if [[ "$had_errexit" -eq 1 ]]; then set -e; fi
  return "$command_status"
}

resource_observe() {
  local stage="$1"
  local root="$2"
  local fd_peak="${3:-unknown}"
  local rss_peak_kb="${4:-unknown}"
  local disk_free_kb=""
  disk_free_kb="$(resource_disk_free_kb "$root")"
  printf 'RESOURCE_OBSERVATION stage=%s disk_free_kb=%s fd_soft_limit=%s fd_peak=%s rss_peak_kb=%s\n' \
    "$stage" \
    "$(resource_observation_number_or_unknown "$disk_free_kb")" \
    "$(resource_fd_soft_limit)" \
    "$(resource_observation_number_or_unknown "$fd_peak")" \
    "$(resource_observation_number_or_unknown "$rss_peak_kb")" >&2
}

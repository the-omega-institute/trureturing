#!/usr/bin/env bash

perf_json_quote() {
  local value="${1:-}"
  value="${value//\\/\\\\}"
  value="${value//\"/\\\"}"
  value="${value//$'\n'/\\n}"
  value="${value//$'\r'/\\r}"
  value="${value//$'\t'/\\t}"
  printf '"%s"' "$value"
}

perf_cpu_count() {
  local count=""
  count="$(getconf _NPROCESSORS_ONLN 2>/dev/null || true)"
  if [[ ! "$count" =~ ^[1-9][0-9]*$ ]]; then
    count="$(sysctl -n hw.logicalcpu 2>/dev/null || true)"
  fi
  if [[ "$count" =~ ^[1-9][0-9]*$ ]]; then printf '%s' "$count"; fi
}

perf_loadavg_per_cpu() {
  local load=""
  local cpus=""
  cpus="$(perf_cpu_count)"
  if [[ -r /proc/loadavg ]]; then
    load="$(awk '{print $1}' /proc/loadavg 2>/dev/null || true)"
  else
    load="$(sysctl -n vm.loadavg 2>/dev/null | tr -d '{}' | awk '{print $1}' || true)"
  fi
  if [[ -n "$load" && -n "$cpus" ]]; then
    awk -v load="$load" -v cpus="$cpus" \
      'BEGIN { if (load >= 0 && cpus > 0) printf "%.6f", load / cpus }' 2>/dev/null || true
  fi
}

perf_host_concurrency() {
  command -v pgrep >/dev/null 2>&1 || return 0
  local pids=""
  pids="$(pgrep -f '(^|/)(local-harness-gate|preflight)\.sh' 2>/dev/null || true)"
  if [[ -n "$pids" ]]; then printf '%s\n' "$pids" | awk 'END { print NR }'; fi
}

perf_cpu_class() {
  local value=""
  value="$(sysctl -n machdep.cpu.brand_string 2>/dev/null || true)"
  if [[ -z "$value" && -r /proc/cpuinfo ]]; then
    value="$(awk -F: '/model name|Hardware/ { sub(/^[ \t]+/, "", $2); print $2; exit }' /proc/cpuinfo 2>/dev/null || true)"
  fi
  if [[ -z "$value" ]]; then value="unknown"; fi
  printf '%s' "$value" | tr '\r\n\t' '   '
}

perf_disk_free_gb() {
  local root="$1"
  df -Pk "$root" 2>/dev/null | awk 'NR > 1 { value=$4 } END { if (value >= 0) printf "%.3f", value / 1048576 }' || true
}

perf_capture_event() {
  local spool="$1"
  local root="$2"
  local run_id="$3"
  local workload_id="$4"
  local base="$5"
  local stage="$6"
  local status="$7"
  local elapsed="$8"
  [[ -n "$spool" ]] || return 1

  local venue="local"
  local runner_class="${RUNNER_NAME:-}"
  if [[ "${CI:-}" == "true" || "${GITHUB_ACTIONS:-}" == "true" ]]; then venue="ci"; fi
  local os="$(uname -s 2>/dev/null || printf unknown)"
  local arch="$(uname -m 2>/dev/null || printf unknown)"
  local cpu_class="$(perf_cpu_class)"
  local commit="$(git -C "$root" rev-parse --verify HEAD 2>/dev/null || printf unknown)"
  local loadavg="$(perf_loadavg_per_cpu)"
  local concurrency="$(perf_host_concurrency)"
  local disk_free="$(perf_disk_free_gb "$root")"
  local cache_state="cold"
  if [[ -d "$root/.lake/build" ]]; then cache_state="warm"; fi
  local timestamp="$(date -u '+%Y-%m-%dT%H:%M:%SZ' 2>/dev/null || printf '1970-01-01T00:00:00Z')"
  local runner_json="null"
  if [[ -n "$runner_class" ]]; then runner_json="$(perf_json_quote "$runner_class")"; fi
  local loadavg_json="${loadavg:-null}"
  local concurrency_json="${concurrency:-null}"
  local disk_json="${disk_free:-null}"
  if [[ -z "$base" ]]; then base="unknown"; fi

  printf '{"schema":"stratalint-perf-event-v1","run_id":%s,"ts":%s,"cohort":{"venue":%s,"os":%s,"arch":%s,"cpu_class":%s,"runner_class":%s},"context":{"commit":%s,"base":%s,"workload_id":%s,"cache_state":%s,"loadavg_per_cpu":%s,"host_concurrency":%s},"kind":"timing","stage":%s,"status":%s,"elapsed_seconds":%s,"resources":{"disk_free_gb":%s,"fd_peak":null,"rss_peak_mb":null}}\n' \
    "$(perf_json_quote "$run_id")" \
    "$(perf_json_quote "$timestamp")" \
    "$(perf_json_quote "$venue")" \
    "$(perf_json_quote "$os")" \
    "$(perf_json_quote "$arch")" \
    "$(perf_json_quote "$cpu_class")" \
    "$runner_json" \
    "$(perf_json_quote "$commit")" \
    "$(perf_json_quote "$base")" \
    "$(perf_json_quote "$workload_id")" \
    "$(perf_json_quote "$cache_state")" \
    "$loadavg_json" \
    "$concurrency_json" \
    "$(perf_json_quote "$stage")" \
    "$(perf_json_quote "$status")" \
    "$elapsed" \
    "$disk_json" >> "$spool"
}

perf_flush_events() {
  local root="$1"
  local spool="$2"
  [[ -n "$spool" && -s "$spool" ]] || return 0
  local project="$root/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"
  local target=""
  target="$(dotnet msbuild "$project" \
    -getProperty:TargetPath \
    -property:Configuration=Release \
    -verbosity:quiet 2>/dev/null)" || return 1
  [[ -n "$target" && "$target" == /* && -f "$target" ]] || return 1
  local ledger="${STRATALINT_PERF_LEDGER:-$HOME/.stratalint-perf/events.jsonl}"
  dotnet "$target" perf-append --input "$spool" --ledger "$ledger"
}

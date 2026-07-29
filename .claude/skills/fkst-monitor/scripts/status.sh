#!/usr/bin/env bash
# fkst-monitor: read-only health snapshot of the fkst devloop deployed on this repo.
# Usage: status.sh [--watch] [--json]
#   --watch  loop every 60s, print only when the verdict is not HEALTHY
#   --json   emit a compact machine-readable line instead of the human report
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
REPO_ROOT="$(cd -- "$SCRIPT_DIR/../../../.." && pwd -P)"
RUN_SH="$REPO_ROOT/.fkst/scripts/run.sh"
FKST_HOME="${FKST_HOME:-$HOME/.fkst/trureturing}"
DURABLE_ROOT="$FKST_HOME/durable"
LOG_DIR="$FKST_HOME/logs"
ENV_FILE="$FKST_HOME/host.env"

resolve_bin() {
  if [[ -n "${BIN:-}" && -x "${BIN:-}" ]]; then printf '%s\n' "$BIN"; return; fi
  if [[ -f "$ENV_FILE" ]]; then
    local b; b="$(sed -n 's/^BIN=//p' "$ENV_FILE" | tail -1)"
    [[ -n "$b" && -x "$b" ]] && { printf '%s\n' "$b"; return; }
  fi
  command -v fkst-framework 2>/dev/null && return
  local sib="$REPO_ROOT/../fkst-substrate/target/debug/fkst-framework"
  [[ -x "$sib" ]] && printf '%s\n' "$sib"
}

newest_log() { ls -t "$LOG_DIR"/supervise-*.log 2>/dev/null | head -1; }

# The launchd supervise log is append-only ACROSS engine restarts, so counting over the whole
# file mixes in prior (since-restarted, often since-fixed) instances — e.g. a `[framework]
# startup error` from a bug fixed three restarts ago would mark the LIVE engine DOWN forever.
# Slice from the current instance's boot: the framework emits `LEVEL=INFO package_roots=[...]`
# once per boot as its first structured line; the run.sh `exec: ... supervise` wrapper is a
# fallback marker. Echoes a path to a current-instance slice (a temp file recorded in
# INSTANCE_SLICE for cleanup), or the full log unchanged if no boot marker is found.
INSTANCE_SLICE=""
scope_log() { # $1 = full log path
  local full="$1" start
  [[ -f "$full" ]] || { printf '%s\n' "$full"; return; }
  start="$(grep -anE 'LEVEL=INFO package_roots=\[|exec: [^ ]*fkst-framework supervise' "$full" 2>/dev/null | tail -1 | cut -d: -f1)"
  if [[ -n "$start" ]]; then
    INSTANCE_SLICE="$(mktemp -t fkst-monitor-slice.XXXXXX)"
    tail -n +"$start" "$full" > "$INSTANCE_SLICE" 2>/dev/null || true
    printf '%s\n' "$INSTANCE_SLICE"
  else
    printf '%s\n' "$full"
  fi
}

# diag-count: scope-aware pattern counting — the mechanical guard against the append-only-log
# misread. Raw `grep -ac` over a supervise log counts ALL history across restarts, NOT the current
# instance; reading that as "happening now" fooled this session repeatedly (version-mismatch churn
# "resolved" while the current instance still had it). For each ERE pattern print: current-instance
# count (scoped to last boot), full-history count (contrast), and the last in-instance TIMESTAMP
# (freshness). Use THIS, never bare `grep -ac`, to answer "is X happening now / still recurring".
diag_count() {
  local log ilog
  log="$(newest_log || true)"
  [[ -n "$log" ]] || { echo "diag: no supervise log found" >&2; return 2; }
  ilog="$(scope_log "$log")"
  printf 'diag over %s  (current = since last boot; full = all history across restarts)\n' "$(basename "$log")"
  local pat now hist last
  for pat in "$@"; do
    # `grep -c` exits 1 on zero matches; under `set -e` an unguarded assignment aborted the whole
    # loop, so the FIRST zero-count pattern silently truncated the report (the tool built to prevent
    # log misreads was itself emitting bad material). Every capture is `|| true`-guarded — a
    # zero-count pattern must report `current=0`, never vanish.
    now="$(grep -acE "$pat" "$ilog" 2>/dev/null | tr -dc '0-9' || true)"; now="${now:-0}"
    hist="$(grep -acE "$pat" "$log" 2>/dev/null | tr -dc '0-9' || true)"; hist="${hist:-0}"
    last="$(grep -aE "$pat" "$ilog" 2>/dev/null | grep -aoE 'TIMESTAMP=[0-9T:-]+Z' | tail -1 || true)"
    printf '  %-44s current=%-6s full=%-7s last=%s\n' "$pat" "$now" "$hist" "${last:-none-in-instance}"
  done
  [[ -n "${INSTANCE_SLICE:-}" && -f "${INSTANCE_SLICE:-}" ]] && rm -f "$INSTANCE_SLICE"; INSTANCE_SLICE=""
}

# count matching lines in a file, always a single integer (0 if none/missing)
cnt() { # $1 pattern  $2 file
  [[ -f "$2" ]] || { echo 0; return; }
  grep -acE "$1" "$2" 2>/dev/null | tr -dc '0-9' | head -c 12 || true
  echo
}
cnt_s() { # count fixed substring in a string
  local n; n="$(grep -c "$1" <<<"$2" 2>/dev/null || true)"; echo "${n:-0}"
}

# REAL load, not the load average. On macOS `uptime` load average counts BLOCKED/waiting threads
# (I/O, locks, mutual waits), so with many fkst/lean/codex processes it reads e.g. 76 while the CPU
# is actually 55% IDLE on a 14-core Mac — it does NOT indicate saturation and must not be used to
# judge overload (2026-07-23: a load-avg misread led to a wrong "machine overloaded, restart" call).
# Judge saturation by CPU idle% + core count + memory free%. Echoes "cpu_idle|cores|mem_free_pct".
real_load() {
  local idle cores memfree
  idle="$(top -l 1 -n 0 2>/dev/null | grep -m1 'CPU usage' | grep -oE '[0-9.]+% idle' | grep -oE '[0-9.]+' | head -1)"
  cores="$(sysctl -n hw.logicalcpu 2>/dev/null || echo '?')"
  memfree="$(memory_pressure 2>/dev/null | grep -i 'free percentage' | grep -oE '[0-9]+%' | head -1 | tr -d '%')"
  printf '%s|%s|%s\n' "${idle:-?}" "${cores:-?}" "${memfree:-?}"
}

snapshot() {
  local verdict="HEALTHY" reasons=() bin log pid uptime acks fatal warns
  bin="$(resolve_bin || true)"

  # Liveness
  local status_line running=0 pidfile pid=""
  status_line="$(bash "$RUN_SH" status 2>&1 | tail -1 || true)"
  if grep -q 'running' <<<"$status_line"; then
    running=1; pid="$(grep -oE '[0-9]+' <<<"$status_line" | tail -1)"
    uptime="$(ps -o etime= -p "$pid" 2>/dev/null | tr -d ' ' || echo '?')"
  else
    verdict="DOWN"; reasons+=("supervise not running")
  fi

  log="$(newest_log || true)"
  # Scope all log counts to the CURRENT engine instance (see scope_log): counts over the whole
  # accumulated log would resurrect fatals from prior, since-restarted instances.
  local ilog=""
  [[ -n "$log" ]] && ilog="$(scope_log "$log")"
  fatal=0; warns=0; acks=0
  if [[ -n "$ilog" ]]; then
    # Match STRUCTURED fatal markers only, and skip giant lines: the supervise log embeds
    # whole issue bodies / diffs / dedup keys (e.g. "child-fatal-characterization-tests",
    # a run.sh diff mentioning "panic"/"startup error"), which a bare substring match counts
    # as fatals and falsely reports DOWN. Real fatals are short structured lines.
    fatal="$(awk 'length<1000' "$ilog" 2>/dev/null | grep -acE 'LEVEL=FATAL|thread .main. panicked|panicked at |\[framework\] startup error|SIGSEGV|SIGABRT' 2>/dev/null | tr -dc '0-9' | head -c 12 || true)"
    [[ -n "$fatal" ]] || fatal=0
    warns="$(cnt 'LEVEL=(WARN|ERROR)' "$ilog")"
    acks="$(cnt 'MSG=delivery acked' "$ilog")"
    (( fatal > 0 )) && { verdict="DOWN"; reasons+=("$fatal fatal log lines"); }
  fi

  # Progress/stall detection: engine reports "running" (PID alive) but the supervise log
  # has gone silent past the threshold => a department likely hung inside a live process.
  # KeepAlive only restarts on process EXIT, so this class needs a kickstart, not a restart.
  # (Real incident 2026-07-16: pr_freshness_scan hung ~22min; log went quiet while PID alive.)
  local progress_age=-1 stall_threshold="${FKST_STALL_THRESHOLD:-600}"
  if (( running )) && [[ -n "$log" ]]; then
    local now_e log_e
    now_e="$(date +%s)"
    log_e="$(stat -f %m "$log" 2>/dev/null || stat -c %Y "$log" 2>/dev/null || echo "$now_e")"
    progress_age=$(( now_e - log_e ))
    if (( progress_age > stall_threshold )); then
      [[ "$verdict" == HEALTHY ]] && verdict="DEGRADED"
      reasons+=("no log progress ${progress_age}s (>${stall_threshold}s; likely stall — kickstart -k)")
    fi
  fi

  # Durable / DLQ via observe
  local dlq=0 retrying=0 absent=0 observe_ok=0 obs=""
  if [[ -n "$bin" && -d "$DURABLE_ROOT" ]]; then
    if obs="$("$bin" observe --durable-root "$DURABLE_ROOT" 2>/dev/null)"; then
      observe_ok=1
      dlq="$(awk '/^dead_letters/{f=1;next}/^[a-z]/{f=0}f&&/^  id=/{n++}END{print n+0}' <<<"$obs")"
      retrying="$( { grep -oE 'retrying=[0-9]+' <<<"$obs" || true; } | awk -F= '{s+=$2}END{print s+0}')"
      absent="$(cnt_s 'subscriber_status=absent' "$obs")"
      (( absent > 0 )) && { [[ "$verdict" == HEALTHY ]] && verdict="DEGRADED"; reasons+=("$absent absent subscriber(s)"); }
    fi
  fi

  # Recent devloop activity (current instance only)
  local codex_failed=0 recent_issue=""
  if [[ -n "$ilog" ]]; then
    codex_failed="$(cnt 'error_class=codex-failed' "$ilog")"
    recent_issue="$( { grep -aoE 'issue/[0-9]+|pr/[0-9]+' "$ilog" 2>/dev/null || true; } | sort -u | tail -3 | tr '\n' ' ')"
    (( codex_failed > 0 )) && { [[ "$verdict" == HEALTHY ]] && verdict="DEGRADED"; reasons+=("$codex_failed codex-failed"); }
  fi

  # Drop the current-instance slice temp file (if scope_log created one).
  [[ -n "${INSTANCE_SLICE:-}" && -f "${INSTANCE_SLICE:-}" ]] && rm -f "$INSTANCE_SLICE"; INSTANCE_SLICE=""

  # REAL load (CPU idle% + cores + mem free%), NOT the misleading load average.
  local rl cpu_idle cores memfree
  rl="$(real_load)"; cpu_idle="${rl%%|*}"; rl="${rl#*|}"; cores="${rl%%|*}"; memfree="${rl##*|}"
  # Real saturation = sustained low CPU idle (not a high load average). Only flag when genuinely low.
  if [[ "$cpu_idle" =~ ^[0-9.]+$ ]] && (( $(printf '%.0f' "$cpu_idle") < 8 )); then
    [[ "$verdict" == HEALTHY ]] && verdict="DEGRADED"; reasons+=("CPU saturated (${cpu_idle}% idle)")
  fi

  if [[ "${1:-}" == "--json" ]]; then
    printf '{"verdict":"%s","running":%d,"pid":"%s","uptime":"%s","fatal":%d,"warn_error":%d,"acks":%d,"dlq":%d,"retrying":%d,"absent_subscribers":%d,"codex_failed":%d,"progress_age_s":%d,"cpu_idle_pct":"%s","cores":"%s","mem_free_pct":"%s"}\n' \
      "$verdict" "$running" "${pid:-}" "${uptime:-}" "$fatal" "$warns" "$acks" "$dlq" "$retrying" "$absent" "$codex_failed" "$progress_age" "$cpu_idle" "$cores" "$memfree"
    [[ "$verdict" == HEALTHY ]]; return
  fi

  printf 'fkst-monitor @ %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf '  verdict     : %s%s\n' "$verdict" "$([[ ${#reasons[@]} -gt 0 ]] && printf ' (%s)' "$(IFS=';'; echo "${reasons[*]}")")"
  printf '  liveness    : %s  pid=%s  uptime=%s\n' "$([[ $running -eq 1 ]] && echo running || echo DOWN)" "${pid:-none}" "${uptime:-}"
  printf '  log         : %s\n' "$([[ -n "$log" ]] && basename "$log" || echo none)"
  printf '  errors      : fatal=%s  warn/error=%s (test-probe produced-only warns are benign)\n' "$fatal" "$warns"
  printf '  throughput  : %s delivery acks (current instance)\n' "$acks"
  printf '  progress    : %s\n' "$([[ $progress_age -lt 0 ]] && echo 'n/a' || echo "last log write ${progress_age}s ago (stall if >${stall_threshold}s)")"
  printf '  resources   : CPU %s%% idle / %s cores · mem %s%% free  (real load — macOS load-avg overstates, ignore it)\n' "${cpu_idle:-?}" "${cores:-?}" "${memfree:-?}"
  if (( observe_ok )); then
    printf '  durable     : dead_letters=%s  retrying=%s  absent_subscribers=%s\n' "$dlq" "$retrying" "$absent"
  else
    printf '  durable     : (observe unavailable — BIN or durable root missing)\n'
  fi
  printf '  codex       : codex-failed=%s\n' "$codex_failed"
  printf '  recent work : %s\n' "${recent_issue:-none in current log}"
  [[ "$verdict" == HEALTHY ]]
}

# Dispatch only when executed, not when sourced (tests source this file for its helpers).
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
  case "${1:-}" in
    --watch)
      while true; do
        out="$(snapshot 2>&1)" && : || echo "$out"
        sleep 60
      done ;;
    --json) snapshot --json ;;
    diag|--diag) shift; diag_count "$@" ;;
    ""|--report) snapshot ;;
    *) echo "usage: status.sh [--watch] [--json] | diag <ERE-pattern>...  (diag = scope-aware count, never raw grep -ac an append-only log)" >&2; exit 2 ;;
  esac
fi

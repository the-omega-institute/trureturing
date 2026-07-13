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

# count matching lines in a file, always a single integer (0 if none/missing)
cnt() { # $1 pattern  $2 file
  [[ -f "$2" ]] || { echo 0; return; }
  grep -acE "$1" "$2" 2>/dev/null | tr -dc '0-9' | head -c 12 || true
  echo
}
cnt_s() { # count fixed substring in a string
  local n; n="$(grep -c "$1" <<<"$2" 2>/dev/null || true)"; echo "${n:-0}"
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
  fatal=0; warns=0; acks=0
  if [[ -n "$log" ]]; then
    fatal="$(cnt 'panic|FATAL|startup error|thread .main. panicked|SIGSEGV' "$log")"
    warns="$(cnt 'LEVEL=(WARN|ERROR)' "$log")"
    acks="$(cnt 'MSG=delivery acked' "$log")"
    (( fatal > 0 )) && { verdict="DOWN"; reasons+=("$fatal fatal log lines"); }
  fi

  # Durable / DLQ via observe
  local dlq=0 retrying=0 absent=0 observe_ok=0 obs=""
  if [[ -n "$bin" && -d "$DURABLE_ROOT" ]]; then
    if obs="$("$bin" observe --durable-root "$DURABLE_ROOT" 2>/dev/null)"; then
      observe_ok=1
      dlq="$(awk '/^dead_letters/{f=1;next}/^[a-z]/{f=0}f&&/^  id=/{n++}END{print n+0}' <<<"$obs")"
      retrying="$(grep -oE 'retrying=[0-9]+' <<<"$obs" | awk -F= '{s+=$2}END{print s+0}')"
      absent="$(cnt_s 'subscriber_status=absent' "$obs")"
      (( absent > 0 )) && { [[ "$verdict" == HEALTHY ]] && verdict="DEGRADED"; reasons+=("$absent absent subscriber(s)"); }
    fi
  fi

  # Recent devloop activity
  local codex_failed=0 recent_issue=""
  if [[ -n "$log" ]]; then
    codex_failed="$(cnt 'error_class=codex-failed' "$log")"
    recent_issue="$( { grep -aoE 'issue/[0-9]+|pr/[0-9]+' "$log" 2>/dev/null || true; } | sort -u | tail -3 | tr '\n' ' ')"
    (( codex_failed > 0 )) && { [[ "$verdict" == HEALTHY ]] && verdict="DEGRADED"; reasons+=("$codex_failed codex-failed"); }
  fi

  if [[ "${1:-}" == "--json" ]]; then
    printf '{"verdict":"%s","running":%d,"pid":"%s","uptime":"%s","fatal":%d,"warn_error":%d,"acks":%d,"dlq":%d,"retrying":%d,"absent_subscribers":%d,"codex_failed":%d}\n' \
      "$verdict" "$running" "${pid:-}" "${uptime:-}" "$fatal" "$warns" "$acks" "$dlq" "$retrying" "$absent" "$codex_failed"
    [[ "$verdict" == HEALTHY ]]; return
  fi

  printf 'fkst-monitor @ %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf '  verdict     : %s%s\n' "$verdict" "$([[ ${#reasons[@]} -gt 0 ]] && printf ' (%s)' "$(IFS=';'; echo "${reasons[*]}")")"
  printf '  liveness    : %s  pid=%s  uptime=%s\n' "$([[ $running -eq 1 ]] && echo running || echo DOWN)" "${pid:-none}" "${uptime:-}"
  printf '  log         : %s\n' "$([[ -n "$log" ]] && basename "$log" || echo none)"
  printf '  errors      : fatal=%s  warn/error=%s (test-probe produced-only warns are benign)\n' "$fatal" "$warns"
  printf '  throughput  : %s delivery acks in current log\n' "$acks"
  if (( observe_ok )); then
    printf '  durable     : dead_letters=%s  retrying=%s  absent_subscribers=%s\n' "$dlq" "$retrying" "$absent"
  else
    printf '  durable     : (observe unavailable — BIN or durable root missing)\n'
  fi
  printf '  codex       : codex-failed=%s\n' "$codex_failed"
  printf '  recent work : %s\n' "${recent_issue:-none in current log}"
  [[ "$verdict" == HEALTHY ]]
}

case "${1:-}" in
  --watch)
    while true; do
      out="$(snapshot 2>&1)" && : || echo "$out"
      sleep 60
    done ;;
  --json) snapshot --json ;;
  ""|--report) snapshot ;;
  *) echo "usage: status.sh [--watch] [--json]" >&2; exit 2 ;;
esac

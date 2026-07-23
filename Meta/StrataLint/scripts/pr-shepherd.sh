#!/usr/bin/env bash
# pr-shepherd - the canonical PR lifecycle entrypoint.
#
# Opens PRs to dev and arms auto-merge. For a BEHIND content PR, it performs an
# exact-base local merge, canonical rederivation, and lease-guarded writeback.
# Other BEHIND PRs retain GitHub update-branch. CONFLICTING only alerts because
# semantic conflict resolution belongs to a dedicated shepherd lane.
#
# Usage:
#   pr-shepherd.sh open <head-branch> <title> [body-file]   Open and arm auto-merge.
#   pr-shepherd.sh watch [interval] [max_cycles]            Poll (default 60s x 360).
#   pr-shepherd.sh sweep                                    Run one scan.
#
# Decisions use machine fields only, never human-readable GitHub prose.
set -euo pipefail

REPO="${PR_SHEPHERD_REPO:-the-omega-institute/trureturing}"
LOG="${PR_SHEPHERD_LOG:-$HOME/.pr-shepherd.log}"
PIDFILE="${PR_SHEPHERD_PID:-$HOME/.pr-shepherd.pid}"
STATE_DIR="${PR_SHEPHERD_STATE:-$HOME/.pr-shepherd-state}"
RECONCILER="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)/Meta/StrataLint/scripts/pr-reconcile.sh"

GH() { LEAN4_GUARDRAILS_BYPASS=1 gh "$@"; }

log() { printf '%s %s\n' "$(date '+%F %T')" "$*" | tee -a "$LOG" >&2; }

open_pr() {
  local head="$1" title="$2" body_file="${3:-}"
  local args=(--repo "$REPO" --base dev --head "$head" --title "$title")
  if [[ -n "$body_file" ]]; then args+=(--body-file "$body_file"); else args+=(--fill-first); fi
  local url num
  url="$(GH pr create "${args[@]}")"
  num="${url##*/}"
  GH pr merge "$num" --repo "$REPO" --auto --merge
  log "OPEN #$num head=$head auto-merge=armed $url"
  printf '%s\n' "$num"
}

# Wake armed PRs whose head has no checks. A local-identity close/reopen mints a
# fresh event after a bot-token push is recursion-suppressed. Closing disarms
# auto-merge, so the wake transaction must re-arm it.
wake_pr() {
  local num="$1"
  GH pr close "$num" --repo "$REPO" || { log "WAKE #$num close failed"; return 1; }
  sleep 3
  if ! GH pr reopen "$num" --repo "$REPO"; then
    sleep 5
    GH pr reopen "$num" --repo "$REPO" \
      || { log "ALERT #$num reopen failed twice; PR remains closed"; return 1; }
  fi
  GH pr merge "$num" --repo "$REPO" --auto --merge \
    || log "WAKE #$num failed to re-arm auto-merge"
  log "WAKE #$num close/reopen complete; auto-merge re-armed"
}

sweep() {
  mkdir -p "$STATE_DIR"
  GH pr list --repo "$REPO" --state open \
    --json number,mergeable,mergeStateStatus,autoMergeRequest,headRefName,headRefOid,baseRefOid,isCrossRepository,statusCheckRollup \
    --jq '.[] | select(.autoMergeRequest != null) | [.number,.mergeable,.mergeStateStatus,.headRefName,.headRefOid,.baseRefOid,.isCrossRepository,(.statusCheckRollup|length)] | @tsv' |
  while IFS=$'\t' read -r num mergeable mstate head head_oid base_oid cross_repository checks; do
    case "$mergeable:$mstate" in
      MERGEABLE:BEHIND)
        reconcile_rc=0
        "$RECONCILER" "$num" "$head" "$head_oid" "$base_oid" "$cross_repository" \
          || reconcile_rc=$?
        if [[ "$reconcile_rc" -eq 0 ]]; then
          log "SWEEP #$num BEHIND -> exact-base derivations reconciled"
        elif [[ $reconcile_rc -eq 3 ]]; then
          if out="$(GH api -X PUT "repos/$REPO/pulls/$num/update-branch" 2>&1)"; then
            log "SWEEP #$num BEHIND non-content -> update-branch(local identity triggers checks)"
          else
            log "SWEEP #$num update-branch failed: $(printf '%s' "$out" | head -c 100)"
          fi
        else
          log "ALERT #$num reconciliation failed; branch left unchanged"
        fi
        ;;
      CONFLICTING:*)
        log "ALERT #$num CONFLICTING head=$head requires semantic merge resolution"
        ;;
      *)
        # Wake only after two consecutive empty observations of the same head,
        # avoiding false positives while checks are being attached.
        marker="$STATE_DIR/nochecks-$num"
        if [[ "$checks" == "0" && ( "$mstate" == "BLOCKED" || "$mstate" == "UNKNOWN" ) ]]; then
          if [[ -f "$marker" && "$(cat "$marker")" == "$head_oid" ]]; then
            wake_pr "$num" && rm -f "$marker"
          else
            printf '%s' "$head_oid" > "$marker"
            log "SWEEP #$num head=$head_oid has no checks; marked for observation"
          fi
        else
          rm -f "$marker" 2>/dev/null || true
        fi
        ;;
    esac
  done
}

watch() {
  local interval="${1:-60}" max="${2:-360}"
  if [[ -f "$PIDFILE" ]] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
    log "WATCH already running (pid=$(cat "$PIDFILE")); exiting"; exit 1
  fi
  printf '%s' "$$" > "$PIDFILE"
  trap 'rm -f "$PIDFILE"' EXIT
  log "WATCH start interval=${interval}s max_cycles=${max} pid=$$"
  local i
  for ((i = 1; i <= max; i++)); do
    sweep || log "SWEEP cycle=$i failed; continuing"
    sleep "$interval"
  done
  log "WATCH end after $max cycles"
}

case "${1:-}" in
  open)  shift; open_pr "$@" ;;
  watch) shift; watch "$@" ;;
  sweep) sweep ;;
  *) sed -n '2,15p' "$0"; exit 2 ;;
esac

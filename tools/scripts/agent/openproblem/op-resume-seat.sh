#!/usr/bin/env bash
# op-resume-seat.sh — relaunch a codex seat after an external kill: prepend a resume header to the original brief
# (attempt N), wait for the load gate, run the sshx runner. One host background job per seat (器律⑥).
# usage: op-resume-seat.sh FLIGHT_ID ATTEMPT BRIEF WORKTREE STAGE [STAGGER_SECONDS] [MAX_CODEX]
# sentinel: RUNNER_EXIT=<n> (judge the seat by its result.json/status.json, never by this exit code alone)
set -uo pipefail
FLIGHT="${1:?flight id}"; ATT="${2:?attempt}"; BRIEF="${3:?brief}"; WT="${4:?worktree}"; STAGE="${5:?stage}"; STAGGER="${6:-0}"; MAXC="${7:-12}"
R=${SSHX_RUNNER:-$HOME/.claude/plugins/cache/consensus-rnd/consensus-rnd/1.0.0-beta.42/skills/sshx/scripts/run-codex-worker.sh}
[ -f "$BRIEF" ] || { echo "RESUME_FAIL brief-missing $BRIEF"; exit 3; }
[ -d "$WT" ] || { echo "RESUME_FAIL worktree-missing $WT"; exit 3; }
OUT="${BRIEF%.md}.a${ATT}.md"
if [ "$ATT" -gt 1 ]; then
  {
    printf '> RESUME NOTE (orchestrator, %s) — this is ATTEMPT %s of flight `%s`. The previous attempt(s) were killed externally by a host job teardown (not by a verdict). The worktree `%s` may already contain their work: FIRST inspect `git status --porcelain`, `git log --oneline origin/dev..HEAD`, `ls Golden/Frozen/state/<module>.lean.json`, the `Meta/Digestion/backfill/**` state of the target atoms, and `gh pr list --head <branch>`; then RESUME from the last completed step instead of starting over (a written Freeze event means `make deposit` is done — never run it twice; covers already present are done; if a PR already exists do not open a second one). Re-run a door only if its inputs changed since it last passed. If the tree is inconsistent (e.g. half-written Scribe/Markdown), say so and repair minimally. Record the attempt history and this interruption in the PR body 产地. Everything below is the original brief.\n\n' "$(date -u +%FT%TZ)" "$ATT" "$FLIGHT" "$WT"
    cat "$BRIEF"
  } > "$OUT"
else
  cp "$BRIEF" "$OUT"
fi
[ "$STAGGER" -gt 0 ] && sleep "$STAGGER"
PASSED=0
for i in $(seq 1 300); do
  IDLE=$(top -l 2 -n 0 -s 2 | grep 'CPU usage' | tail -1 | sed -E 's/.*, ([0-9.]+)% idle/\1/')
  LEAN=$(pgrep -x lean | wc -l | tr -d ' '); CODEX=$(pgrep -f 'codex exec' | wc -l | tr -d ' ')
  # codex upstream health (2026-09-06: llm.aelf.dev returned 502 for hours and every in-flight seat died with turn.failed);
  # any HTTP status other than 502/503/000 means the gateway answers (401/400/405 are fine — we only need it reachable)
  EP=$(curl -s -o /dev/null -m 10 -w '%{http_code}' -X POST "${CODEX_HEALTH_URL:-https://llm.aelf.dev/responses}" -H 'content-type: application/json' -d '{}' 2>/dev/null || echo 000)
  EPOK=1; case "$EP" in 502|503|000) EPOK=0;; esac
  if [ "$EPOK" -eq 1 ] && awk -v i="$IDLE" -v l="$LEAN" -v c="$CODEX" -v m="$MAXC" 'BEGIN{exit !(i>=20 && l<=4 && c<=m)}'; then PASSED=1; break; fi
  echo "gate-wait $(date +%T) idle=$IDLE lean=$LEAN codex=$CODEX endpoint=$EP"; sleep 60
done
# fail-closed: never launch when the gate did not open (the old version fell through after 90 minutes and
# launched ~10 seats into a saturated host on 2026-09-05)
[ "$PASSED" -eq 1 ] || { echo "GATE_TIMEOUT idle=${IDLE:-?} lean=${LEAN:-?} codex=${CODEX:-?} — not launched"; exit 3; }
echo "GATE_PASS idle=${IDLE:-?} lean=${LEAN:-?} codex=${CODEX:-?} endpoint=${EP:-?} brief=$OUT"
bash "$R" --flight-id "$FLIGHT" --attempt "$ATT" --stage "$STAGE" --work-target "$WT" < "$OUT"
echo "RUNNER_EXIT=$?"

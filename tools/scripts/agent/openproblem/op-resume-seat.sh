#!/usr/bin/env bash
# op-resume-seat.sh — relaunch a codex seat after an external kill: prepend a resume header to the original brief
# (attempt N), wait for the load gate, run the sshx runner. One host background job per seat (器律⑥).
# usage: op-resume-seat.sh FLIGHT_ID ATTEMPT BRIEF WORKTREE STAGE [STAGGER_SECONDS] [MAX_CODEX]
# sentinel: RUNNER_EXIT=<n> (judge the seat by its result.json/status.json, never by this exit code alone)
set -uo pipefail
# ---- 载体健康探针(2026-09-06 立;器律④:坏原材料在产生处修)----
# 旧探针 `curl -X POST https://llm.aelf.dev/responses -d '{}'` 是**未认证**的,
# 而 auth 在服务可用性**之前**判定 —— 实测未认证 POST 与带假 bearer 的 POST **都返回 401**,
# 于是 502/503/000 之外一律判可达的逻辑 **结构上永远看不到 503**,对它要检出的那个故障是盲的。
# 代价读数(2026-09-06):网关 503 期间连派三席 + 续跑两席,**五次全部白跑**;
# 席位侧日志为 `Reconnecting... 5/5 (unexpected status 503 …)` 继以 `turn.failed`。
# 正解是用**真工具**探:`codex exec` 一条 trivial prompt —— 认证、代表性、且领先(不必等席位死掉)。
# 实测该探针在故障期 rc=1、耗时 29s(5 次重试);健康期是一次极小调用。
__carrier_verdict() {  # <探针输出> <rc> -> up|down|unknown   纯函数,由 --selftest 钉住
  local out="$1" rc="$2"
  case "$out" in
    *"Service Unavailable"*|*"Bad Gateway"*|*"turn.failed"*|*"502 "*|*"503 "*) echo down; return;;
  esac
  case "$rc" in 0) echo up;; *) echo down;; esac
}
__carrier_probe() {  # 打印 up|down;缺 codex 或探针不可用时 fail-closed 报 down
  command -v codex >/dev/null 2>&1 || { echo down; return; }
  local out rc
  out=$(printf 'Reply with exactly: OK\n' | codex exec --skip-git-repo-check --sandbox read-only 2>&1); rc=$?
  __carrier_verdict "$out" "$rc"
}

if [ "${1:-}" = "--selftest" ]; then
  fail=0
  chk(){ got=$(__carrier_verdict "$3" "$2"); if [ "$got" = "$1" ]; then printf '  ok   %-32s %s\n' "$4" "$got"; else printf '  FAIL %-32s expected=%s got=%s\n' "$4" "$1" "$got"; fail=1; fi; }
  # 阴性:真实捕获的 503 文本(2026-09-06 实测,逐字)
  chk down 1 'ERROR: unexpected status 503 Service Unavailable: Service temporarily unavailable, url: https://llm.aelf.dev/responses, cf-ray: a36c2e6b-SIN' real-503-capture
  # **rc=0 但输出报故障** —— 这一组才让文本模式承重(器律④:载体可能打错却退 0)。
  # 每个析取项各配一条**只有它能捕获**的用例,使删掉任一项都有自己的红。
  chk down 0 'Service Unavailable'                         only-service-unavailable
  chk down 0 'upstream connect error: Bad Gateway'         only-bad-gateway
  chk down 0 '{"type":"turn.failed","error":{}}'           only-turn-failed
  chk down 0 'HTTP 503 returned by proxy'                  only-503-token
  chk down 0 'HTTP 502 returned by proxy'                  only-502-token
  # 阴性:退出码本身为坏
  chk down 1 ''                                            empty-rc1
  chk down 7 'OK'                                          nonzero-rc-despite-ok
  # 阳性:健康返回
  chk up   0 'OK'                                          healthy
  chk up   0 'OK
[2026-09-06T08:00:00] tokens used: 12'                     healthy-with-noise
  # 关键阴性对照:401 **不是**健康证据 —— 旧 curl 探针的输出若被喂进来,必须判 down。
  chk down 1 '401'                                         curl-401-is-not-health
  [ $fail -eq 0 ] && echo "SELFTEST_OK" || echo "SELFTEST_FAIL"
  exit $fail
fi

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
  # curl 只作**快速失败**(它能看见的那几种);**401 绝不算健康**,故不再据它放行。
  EPOK=1; case "$EP" in 502|503|000) EPOK=0;; esac
  # 权威判据:用真工具探。仅在 curl 未直接判死、且主机负载已满足时才花这次调用。
  if [ "$EPOK" -eq 1 ] && awk -v i="$IDLE" -v l="$LEAN" -v c="$CODEX" -v m="$MAXC" 'BEGIN{exit !(i>=20 && l<=4 && c<=m)}'; then
    CARRIER=$(__carrier_probe); [ "$CARRIER" = up ] || EPOK=0
  else
    CARRIER=skipped
  fi
  if [ "$EPOK" -eq 1 ] && awk -v i="$IDLE" -v l="$LEAN" -v c="$CODEX" -v m="$MAXC" 'BEGIN{exit !(i>=20 && l<=4 && c<=m)}'; then PASSED=1; break; fi
  echo "gate-wait $(date +%T) idle=$IDLE lean=$LEAN codex=$CODEX endpoint=$EP carrier=${CARRIER:-?}"; sleep 60
done
# fail-closed: never launch when the gate did not open (the old version fell through after 90 minutes and
# launched ~10 seats into a saturated host on 2026-09-05)
[ "$PASSED" -eq 1 ] || { echo "GATE_TIMEOUT idle=${IDLE:-?} lean=${LEAN:-?} codex=${CODEX:-?} carrier=${CARRIER:-?} — not launched"; exit 3; }
echo "GATE_PASS idle=${IDLE:-?} lean=${LEAN:-?} codex=${CODEX:-?} endpoint=${EP:-?} carrier=${CARRIER:-?} brief=$OUT"
bash "$R" --flight-id "$FLIGHT" --attempt "$ATT" --stage "$STAGE" --work-target "$WT" < "$OUT"
echo "RUNNER_EXIT=$?"

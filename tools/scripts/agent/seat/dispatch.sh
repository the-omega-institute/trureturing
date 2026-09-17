#!/usr/bin/env bash
# dispatch.sh — 派一个 codex-cli 席位:解析 sshx runner → 过负载门 → 单次直调 → 落哨兵。
# usage: dispatch.sh FLIGHT_ID ATTEMPT BRIEF WORKTREE STAGE [STAGGER_SECONDS] [MAX_CODEX]
#        dispatch.sh --selftest
# STAGE ∈ thinking|implementation|review|termination。哨兵:RUNNER_EXIT=<n>
# (判终局仍须 result.json + completion sentinel 双在,本行只是载体退出码,见器律⑥)
#
# 立条依据 issue #6220(器只放在 scratchpad,活会话中途被整目录清空)。本器此前只存在于
# scratchpad,故每台驱动机各写一份、各带各的 bug;入仓后这笔学费只付一次(器律⑨ / 第 8.9 条)。
#
# 2026-09-09 实测的两条缺陷,是把它搬进来的**直接理由**,不是顺手改的风格:
#
#  ①**runner 版本钉死在最老的一版**。scratchpad 版写死
#    `consensus-rnd/1.0.0-beta.31/skills/sshx/scripts/run-codex-worker.sh`,而本机当时装了
#    **五个**版本(beta.31/.32/.36/.37/.42)。于是当天派出的每一席都跑在最老的 runner 上,
#    而这**不会有任何症状** —— 老路径还在,脚本照常退出 0。这正是第 9.2 条所指的
#    「无检测的引用是断链」:指错了没人比,永远不会红。
#    修法是解析而非钉死,且**解析不到就 fail-closed**(第 2.1 条),不许静默回退。
#    版本序必须用 `sort -V`:纯字典序在出现 `beta.9` 时会把它排在 `beta.42` 之后。
#
#  ②**负载门跑满即静默放行**。scratchpad 版是 `for i in $(seq 1 240)`,门若一直不过,
#    循环结束后**照常 dispatch**,且不打任何字。2 小时的等待与「门通过」在输出上无法区分,
#    正是第 2.1 条禁的浮账。此处改为超时即 GATE_TIMEOUT + 非零退出。
#
# 本器是**胶水**(编排 runner、top、pgrep),按第 9.1 条辨析不建单元测试套件;
# 其义务是三样:开头 fail-fast 断言全部输入、哨兵退出码、可安全重跑。--selftest 钉住前两样。

set -uo pipefail

# 解析已安装的最新 sshx runner。找不到即 fail-closed —— 不回退到任何猜测路径。
# 实现住共用库,因为 openproblem/op-resume-seat.sh 也要同一个解析;抄第二份即第二真源(第 4.2 条)。
SEAT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=./sshx-runner-lib.sh
. "$SEAT_DIR/sshx-runner-lib.sh"
RUNNER_GLOB="$SSHX_PLUGIN_ROOT_DEFAULT"

# selftest 的每个子调用都必须 hermetic:存根 runner + 单轮 gate + 零 sleep。否则删掉任一输入断言,
# 该用例就会掉进**真实**的 240×30s 负载门,selftest 变成挂起而不是变红 —— 挂起不是红(第 9.3 条),
# 且第 9.6 条禁止真实等待承判词。这一条是变异实验逼出来的:M3 删掉 brief 断言后正是如此挂住。
hermetic() { local t="$1"; shift
  SSHX_PLUGIN_ROOT="$t/plugins" DISPATCH_GATE_ROUNDS=1 DISPATCH_GATE_SLEEP=0 "$0" "$@"; }

# 同一工作树上已有在飞席位时,拒绝再派。两个席位同时写一棵树会互相覆盖,
# 而第 5.11 条要求调用方对在飞 work_target 只读 —— 这道断言把「纪律」变成「机器判」。
#
# 立条依据(2026-09-09,本器落地当天我自己犯的):我用 `pgrep -fc 'codex exec'` 判席位死活,
# 该 flag 在 macOS 上**静默返回 0**(见 pgrep-c-is-not-count-on-macos:rc=2、无输出),
# 于是把一个已跑 2h42m 的活席位判成死的,并往同一棵树上又派了一席。
# 一分钟内发现并杀掉,受管文件零改动 —— 但下次未必这么走运。
# **`pgrep -f` 正常,坏的只有 `-c`**;本函数一律用前者。
#
# 判据只看 runner 的 `--work-target <路径>`,不看 flight id:同一棵树无论哪条 flight 都算冲突。
inflight_on() {
  local target="$1" pids
  pids=$(pgrep -f -- "--work-target $target" 2>/dev/null | tr '\n' ' ')
  # 排除本进程与其父(本脚本自己的命令行里也含该字符串)
  pids=$(printf '%s\n' $pids | grep -v -e "^$$\$" -e "^$PPID\$" | tr '\n' ' ')
  [ -n "${pids// /}" ] && { printf '%s\n' "$pids"; return 0; }
  return 1
}

# 在飞席位数。**数的是席位,不是进程。**
#
# 立条依据(2026-09-11 实测):此前这里是 `pgrep -f 'codex exec' | wc -l`,而一个席位在
# 本机起**两个**匹配该模式的进程(`node .../codex exec` 包装器 + 其 vendor 原生二进制)。
# 于是 `MAX_CODEX=3` 这个按「席位」命名的旋钮,实际在**第三席**上恒不通过:两席在飞时
# 读数是 4,4 < 3 为假,门一直等到 240 轮跑满才以 GATE_TIMEOUT 退出。
# 当天派的第三席正是这样卡住的,而两席已经跑在同一台机上 —— 名字是席位、量的是进程,
# 差一个常数因子 2(第 8.4 条:坏原材料;第 2.9 条:读数要答得出它答的是哪句话)。
#
# 正确的席位键是 runner 的 `--work-target <树>`:一个工作树至多一个在飞席位,这正是
# dispatch.sh 自己的 inflight_on 已经采用的判据。同一席位的多个进程共享同一个 work-target,
# 去重后就是席位数。取不到 runner 进程时回落到 0,由 inflight_on 与 runner 自身兜底。
# 进程表取自 $SEAT_COUNT_PS,使本函数成为一段可喂合成输入的纯文本处理 —— 否则它没有钉子
# (第 9.3 条:写不出反例的检查等于没检查)。生产路径不设该变量。
seat_count() {
  # 行必须同时含 runner 名与该 flag:只写 `grep -- '--work-target'` 会把任何**引用**了这个
  # 字符串的 argv 一并数进来 —— 实测撞到过一次,是我自己那条 shell 命令的 zsh 包装行。
  # 该方向是保守的(多数=多等),但它会让门在宿主明明空闲时挡住席位,与本次修的病同形。
  ${SEAT_COUNT_PS:-ps -eo args} 2>/dev/null \
    | grep -- 'run-codex-worker\.sh' | grep -- '--work-target' \
    | grep -o -- '--work-target [^ ]*' | sort -u | wc -l | tr -d ' '
}

selftest() {
  local fails=0 tmp; tmp=$(mktemp -d); trap 'rm -rf "$tmp"' RETURN
  # 版本序:beta.9 必须排在 beta.42 之前(纯 sort 会判反,这正是用 -V 的理由)
  mkdir -p "$tmp/plugins/1.0.0-beta.9/skills/sshx/scripts" \
           "$tmp/plugins/1.0.0-beta.42/skills/sshx/scripts"
  : > "$tmp/plugins/1.0.0-beta.9/skills/sshx/scripts/run-codex-worker.sh"
  : > "$tmp/plugins/1.0.0-beta.42/skills/sshx/scripts/run-codex-worker.sh"
  # seat_count 数的是席位不是进程:同一席位的两个进程共享一个 --work-target。
  cat >"$tmp/ps-two-seats" <<'PS'
#!/bin/sh
cat <<'ROWS'
node /opt/homebrew/bin/codex exec --json -C /w/one --sandbox danger-full-access
/vendor/bin/codex exec --json -C /w/one --sandbox danger-full-access
bash /p/run-codex-worker.sh --work-target /w/one --stage implementation
bash /p/run-codex-worker.sh --work-target /w/two --stage implementation
ROWS
PS
  chmod +x "$tmp/ps-two-seats"
  local seats; seats=$(SEAT_COUNT_PS="$tmp/ps-two-seats" seat_count)
  if [ "$seats" = "2" ]; then
    echo "  ok   seat_count counts work-targets, not processes"
  else
    echo "  FAIL seat_count returned '$seats', expected 2"; fails=$((fails + 1))
  fi
  # 阴性对照:只是**引用**了该 flag 的 argv 不算席位。
  cat >"$tmp/ps-quoting" <<'PS'
#!/bin/sh
cat <<'ROWS'
bash /p/run-codex-worker.sh --work-target /w/one --stage implementation
/bin/zsh -c echo "the knob is --work-target <tree> in that script"
python3 -c print('--work-target /w/fake')
ROWS
PS
  chmod +x "$tmp/ps-quoting"
  seats=$(SEAT_COUNT_PS="$tmp/ps-quoting" seat_count)
  if [ "$seats" = "1" ]; then
    echo "  ok   seat_count ignores argv that merely quotes the flag"
  else
    echo "  FAIL seat_count returned '$seats' with one seat plus two quoters, expected 1"; fails=$((fails + 1))
  fi
  cat >"$tmp/ps-idle" <<'PS'
#!/bin/sh
echo "bash /some/other/thing"
PS
  chmod +x "$tmp/ps-idle"
  seats=$(SEAT_COUNT_PS="$tmp/ps-idle" seat_count)
  if [ "$seats" = "0" ]; then
    echo "  ok   seat_count is zero with no seat in flight"
  else
    echo "  FAIL seat_count returned '$seats' on an idle host, expected 0"; fails=$((fails + 1))
  fi
  local got; got=$(resolve_runner "$tmp/plugins" || echo NONE)
  case "$got" in
    *1.0.0-beta.42*) echo "  ok   resolve picks newest by version order" ;;
    *) echo "  FAIL resolve picked '$got', expected beta.42"; fails=$((fails + 1)) ;;
  esac
  # fail-closed:目录在而 runner 不在
  mkdir -p "$tmp/empty/1.0.0-beta.1"
  if resolve_runner "$tmp/empty" >/dev/null 2>&1; then
    echo "  FAIL resolve succeeded with no runner present"; fails=$((fails + 1))
  else
    echo "  ok   resolve fails closed when the runner file is absent"
  fi
  # fail-closed:根本没有插件根
  if resolve_runner "$tmp/absent" >/dev/null 2>&1; then
    echo "  FAIL resolve succeeded with no plugin root"; fails=$((fails + 1))
  else
    echo "  ok   resolve fails closed when the plugin root is absent"
  fi
  # 输入断言:brief 缺失必须以 3 退出,且不得触及 runner
  : > "$tmp/brief.md"; mkdir -p "$tmp/wt"
  hermetic "$tmp" f 1 "$tmp/missing-brief.md" "$tmp/wt" review 0 1 >"$tmp/o" 2>&1
  [ $? -eq 3 ] && grep -q 'brief-missing' "$tmp/o" \
    && echo "  ok   missing brief exits 3" \
    || { echo "  FAIL missing brief: rc=$? out=$(cat "$tmp/o")"; fails=$((fails + 1)); }
  hermetic "$tmp" f 1 "$tmp/brief.md" "$tmp/absent-wt" review 0 1 >"$tmp/o" 2>&1
  [ $? -eq 3 ] && grep -q 'worktree-missing' "$tmp/o" \
    && echo "  ok   missing worktree exits 3" \
    || { echo "  FAIL missing worktree: rc=$? out=$(cat "$tmp/o")"; fails=$((fails + 1)); }
  # 负载门超时必须**拒派**。这一条是补上来的:第一版 selftest 五条全绿,
  # 而把 gate_ok 判断整块删掉一条都不红 —— 即缺陷②本身没有钉子(第 9.3 条六元组第六项)。
  # 指向 $tmp/plugins 的**空 runner 存根**:即使 gate 守卫被删,fall-through 也只是执行一个
  # 空文件后立刻返回,而不是真派席位挂住。删掉守卫时得到一条具名 FAIL,不是一次超时
  # —— 消掉挂起,而不是给挂起加看门狗(第 9.6 条:真实等待永不承判词)。
  hermetic "$tmp" f 1 "$tmp/brief.md" "$tmp/wt" review 0 0 >"$tmp/o" 2>&1
  rc=$?
  if [ "$rc" -eq 4 ] && grep -q 'GATE_TIMEOUT' "$tmp/o"; then
    echo "  ok   gate timeout refuses to dispatch (exit 4)"
  else
    echo "  FAIL gate timeout: rc=$rc out=$(cat "$tmp/o")"; fails=$((fails + 1))
  fi
  # 在飞守卫:构造一个命令行里带 --work-target 的假进程,派发必须以 5 拒绝
  ( exec -a "fake-runner --work-target $tmp/wt" sleep 8 ) &
  fake=$!
  sleep 1
  hermetic "$tmp" f 1 "$tmp/brief.md" "$tmp/wt" review 0 8 >"$tmp/o" 2>&1
  rc=$?
  kill "$fake" 2>/dev/null; wait "$fake" 2>/dev/null
  if [ "$rc" -eq 5 ] && grep -q 'worktree-busy' "$tmp/o"; then
    echo "  ok   refuses to dispatch into a worktree that already has a seat (exit 5)"
  else
    echo "  FAIL in-flight guard: rc=$rc out=$(head -2 "$tmp/o")"; fails=$((fails + 1))
  fi
  echo "SELFTEST_FAILS=$fails"; [ "$fails" -eq 0 ]
}

[ "${1:-}" = "--selftest" ] && { selftest; exit $?; }

FLIGHT="${1:?flight id}"; ATT="${2:?attempt}"; BRIEF="${3:?brief}"
WT="${4:?worktree}"; STAGE="${5:?stage}"; STAGGER="${6:-0}"; MAXC="${7:-12}"

[ -f "$BRIEF" ] || { echo "DISPATCH_FAIL brief-missing $BRIEF"; exit 3; }
[ -d "$WT" ]    || { echo "DISPATCH_FAIL worktree-missing $WT"; exit 3; }
case "$STAGE" in
  thinking|implementation|review|termination) ;;
  *) echo "DISPATCH_FAIL bad-stage '$STAGE' (thinking|implementation|review|termination)"; exit 3 ;;
esac

if busy=$(inflight_on "$WT"); then
  echo "DISPATCH_FAIL worktree-busy $WT already has an in-flight seat (pids: $busy)"
  echo "  两个席位同时写一棵树会互相覆盖(第 5.11 条)。等它归位,或换一棵树。"
  echo "  确认它是不是真活着:用 ps 或 pgrep -f,**不要用 pgrep -fc**(macOS 上静默返回 0)。"
  exit 5
fi

RUNNER=$(resolve_runner "$RUNNER_GLOB") || {
  echo "DISPATCH_FAIL runner-unresolved under $RUNNER_GLOB"; exit 3; }
echo "RUNNER $RUNNER"

[ "$STAGGER" -gt 0 ] && sleep "$STAGGER"

# 负载门。等的是宿主负载,没有自带同步原语,故轮询合法(第 8.7 条辨析);
# 但按该条要求:间隔与被等事件节奏对齐、有上限、每轮带读数,且**判据写在开跑之前**。
GATE_ROUNDS="${DISPATCH_GATE_ROUNDS:-240}"; gate_ok=0
for _ in $(seq 1 "$GATE_ROUNDS"); do
  idle=$(top -l 2 -s 2 -n 0 | grep 'CPU usage' | tail -1 | grep -o '[0-9.]*% idle' | tr -d '% idle')
  lean=$(pgrep -f '^(/bin/)?bash [^ ]*report-supervisor\.sh' | wc -l | tr -d ' ')
  cdx=$(seat_count)
  if python3 -c "import sys; sys.exit(0 if float('${idle:-0}')>=20 and $lean<=4 and $cdx<$MAXC else 1)" 2>/dev/null; then
    echo "GATE_PASS idle=$idle lean=$lean seats=$cdx brief=$BRIEF"; gate_ok=1; break
  fi
  sleep "${DISPATCH_GATE_SLEEP:-30}"
done
# 门不过就不派 —— 静默放行会让「等了两小时」与「门通过」在输出上无法区分(第 2.1 条)。
[ "$gate_ok" = "1" ] || {
  echo "GATE_TIMEOUT rounds=$GATE_ROUNDS idle=${idle:-?} lean=${lean:-?} codex=${cdx:-?}"; exit 4; }

RUNROOT="${TMPDIR:-/tmp}/consensus-rnd/sshx"
while [ -e "$RUNROOT/$FLIGHT/attempt-$ATT" ]; do
  ATT=$((ATT + 1))
  [ "$ATT" -gt 40 ] && { echo "DISPATCH_FAIL no-free-attempt for $FLIGHT"; exit 3; }
done
echo "FLIGHT $FLIGHT attempt=$ATT"

bash "$RUNNER" --flight-id "$FLIGHT" --attempt "$ATT" --stage "$STAGE" --work-target "$WT" < "$BRIEF"
echo "RUNNER_EXIT=$?"

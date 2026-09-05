#!/usr/bin/env bash
# nyx.sh — nyxid 派票与状态分类。**不要再用 `tail -1` 肉眼判成败。**
#
# 立条依据(2026-08-28):我用「tail -1 != EXIT=0」当失败的代理,它把**四个状态**混成一个:
#   110B  Failed to read prompt   —— 我自己的 mkrev bug
#   153B  extraction_failure      —— 载体侧随机,可重投
#   178B  waiting_response        —— **还在跑,根本不是失败**
#   248B  HTTP 429 quota_exceeded —— **我自己把池打满了**
# 契约就写在 429 的 body 里:`limit 4` 并发。我从没读到它,因为代理把它藏了。
# 而误读直接导致错误决策:读到「6 投全败」于是投得更多 → 更多 429。
#
# 用法:
#   nyx.sh ask <brief> <outfile>     投一票(自动等到 in-flight < LIMIT 才投)
#   nyx.sh status [glob]             分类打印 /tmp/nyx-*.out 的真实状态
#   nyx.sh inflight                  当前 in-flight 数
export PATH="$HOME/.local/bin:$PATH"
# 2026-08-28 实测:契约写 limit 4,但实际吞吐更低,且 `nyxid oracle status` 的 in-flight
# **包含别人的任务**(组织级共享池)—— 某刻显示 3 而我只有 2 张在跑。故保守取 2。
POOL="${NYX_POOL:-chatgpt-pro-pool}"
# LIMIT 缺省**由 pool 自报容量派生**,不写死(2026-09-04 立)。
# 案由:await.sh 曾写死 NYX_LIMIT=4,而 company pool 容量为 10、已被他人占 6 —— 6 >= 4,
# 于是持锁者永远等不到「空位」,10 分钟后报 NYX_BUSY,五票全部卡在提交之前、零输出。
# 写死一个与被测对象无关的数,就是器律④ 的坏原材料:它看起来像个限额,实际与真实容量无关。
LIMIT="${NYX_LIMIT:-}"
# 提交模式(2026-09-04 立)。新版 worker 脚本(cdp-2.6+)执行 `nyxid.oracle.submission-gate.v1`,
# **fresh task 必须显式带 mode tag**,否则秒退 `oracle_mode_required` 且 retryable=false。
# 旧脚本(cdp-1.3)不要求,故同一条命令在不同 pool 上一个能过一个不能 —— 这正是
# 「不看 pool 自报的契约就派」的代价。契约原文:`nyxid oracle pool show <slug> --output json`。
# 取 mode:chat 因其默认模型即 ChatGPT **Pro**,与本仓 goal 的「1 席 gpt pro」精确对应;
# mode:work 默认 Ultra,属另一档,不在 goal 射程内。
TAG="${NYX_TAG:-mode:chat}"

__classify() {  # 读一个 .out,打印:OK|EXTRACTION|QUOTA|NOFILE|RUNNING|UNKNOWN
  local f="$1"
  [ -f "$f" ] || { echo NOFILE_OUT; return; }
  if [ "$(tail -1 "$f")" = "EXIT=0" ]; then echo OK; return; fi
  grep -q 'oracle_quota_exceeded\|HTTP 429' "$f" && { echo QUOTA; return; }
  grep -q 'Failed to read prompt' "$f" && { echo NOFILE; return; }
  grep -q 'extraction_failure' "$f" && { echo EXTRACTION; return; }
  grep -q 'EXIT=' "$f" && { echo UNKNOWN; return; }
  echo RUNNING   # 无 EXIT= 行 ⟹ 进程还没结束
}

__expired() {  # 会话过期是能力缺口,不是池满 —— 必须与 in-flight 区分,否则白等 10 分钟
  nyxid oracle status "$POOL" 2>&1 | grep -q 'session has expired' && return 0 || return 1
}
__capacity() {  # pool 自报的总容量(Dispatched: N / M 的 M)
  local m
  m=$(nyxid oracle status "$POOL" 2>&1 | grep -oE 'Dispatched: *[0-9]+ */ *[0-9]+' | grep -oE '[0-9]+$')
  echo "${m:-2}"   # 读不到退回保守值,fail-closed
}
__inflight() {
  local n
  n=$(nyxid oracle status "$POOL" 2>&1 | grep -oE 'Dispatched: *[0-9]+' | grep -oE '[0-9]+$')
  echo "${n:-99}"   # 读不到就当满,fail-closed:宁可等,不可再打 429
  # 注:`nyxid oracle status` 把状态写到 **stderr**,必须 2>&1,否则恒为空 → 恒判 99
}

case "$1" in
  inflight) __inflight ;;
  status)
    printf "%-8s %-26s %6s %s\n" 时间 状态 字节 文件
    for f in ${2:-/tmp/nyx-*.out}; do
      printf "  %-8s %-26s %5sB %s\n" "$(stat -f '%Sm' -t '%H:%M' "$f")" "$(__classify "$f")" \
        "$(wc -c <"$f"|tr -d ' ')" "$(basename "$f" .out)"
    done | sort -k2
    echo "  ---- in-flight=$(__inflight)/$LIMIT"
    ;;
  ask)
    brief="$2"; out="$3"
    [ -n "$LIMIT" ] || LIMIT="$(__capacity)"
    [ -f "$brief" ] || { echo "NYX_ERR brief 不存在: $brief"; exit 2; }   # 110B 那个 bug 的门
    # 会话过期 → 立刻报能力缺口,不要当池满去等 10 分钟(2026-08-28 实测遇到)
    __expired && { echo "NYX_EXPIRED 会话已过期 —— 需人跑 \`nyxid login\`(第15条:能力缺口,等灯亮)"; exit 4; }
    # **锁**:检查 in-flight 与提交之间必须原子,否则两个并发 ask 会都看到有空位、都提交 → 429。
    # (2026-08-28 实测:并发两个 ask,in-flight=3,两者都判有空位,一者得 QUOTA。
    #  这是 TOCTOU 竞态 —— 器自己犯了它要防的那个错。)
    # 锁**按 pool 分片**:跨 pool 本无竞态,共用一把锁会让空闲 pool 的票排在满 pool 的票后面。
    LOCK="${TMPDIR:-/tmp}/nyx-ask-${POOL}.lock"
    n=0
    while ! mkdir "$LOCK" 2>/dev/null; do
      n=$((n+1)); [ $n -gt 120 ] && { echo "NYX_LOCKBUSY 等锁超时: $out"; exit 3; }
      sleep 5
    done
    trap 'rmdir "$LOCK" 2>/dev/null' EXIT INT TERM
    # 持锁期间等空位,再提交 —— 提交后立刻放锁(任务已计入 in-flight)
    n=0
    while [ "$(__inflight)" -ge "$LIMIT" ] && [ $n -lt 30 ]; do sleep 20; n=$((n+1)); done
    if [ "$(__inflight)" -ge "$LIMIT" ]; then
      rmdir "$LOCK" 2>/dev/null; trap - EXIT
      echo "NYX_BUSY 等了 10 分钟仍满($LIMIT),放弃: $out"; exit 3
    fi
    # **--no-wait + 记 task id**:阻塞等待会让「我的进程生死」决定「任务是否丢失」。
    # 2026-08-28 实测:前台 ask 被 2min 超时杀、后台 ask 被 SIGTERM(exit 143)杀,
    # 而 `nyxid oracle result <task-id>` 显示**任务在池里仍活着**(`Phase: waiting_response`)。
    # 故改为提交后立刻拿 id 落盘,等待与取回分离 —— 被杀只丢等待,不丢工作。
    nyxid oracle ask "$POOL" --file "$brief" --tag "$TAG" --no-wait > "$out" 2>&1; rc=$?
    tid=$(grep -oE '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' "$out" | head -1)
    [ -n "$tid" ] && echo "$tid" > "$out.taskid"
    rmdir "$LOCK" 2>/dev/null; trap - EXIT
    if [ -z "$tid" ]; then echo "EXIT=$rc" >> "$out"; echo "NYX_$(__classify "$out") $(basename "$out" .out)"; exit $rc; fi
    # 轮询取回。**这不是挂钟猜测**:池无 webhook,`result` 是唯一取回原语;
    # 间隔对齐真实任务时长(实测数分钟级),且有上限、每轮不打印噪声。
    n=0
    while [ $n -lt 60 ]; do
      r=$(nyxid oracle result "$tid" 2>&1)
      case "$r" in *"Task is dispatched"*|*"Phase:"*|*queued*) ;; *) printf '%s\n' "$r" >> "$out"; break;; esac
      n=$((n+1)); sleep 20
    done
    # **退出码必须反映取回的内容,不能写死 0**
    # (2026-08-28:no-wait 改造首跑即回归 —— `extraction_failure` 报了 EXIT=0,
    #  正是器律④「原材料好,不靠读者警惕」要禁的坏材料:调用方按退出码判就会误判成功。)
    if [ $n -ge 60 ]; then
      echo "NYX_TIMEOUT $tid 仍未落定;可随时 nyxid oracle result $tid 取回"; rc=3
    else
      case "$(__classify "$out")" in OK) rc=0;; QUOTA) rc=1;; EXTRACTION) rc=1;; *) rc=1;; esac
    fi
    echo "EXIT=$rc" >> "$out"
    echo "NYX_$(__classify "$out") $(basename "$out" .out)"
    ;;
  *) echo "usage: nyx.sh {ask <brief> <out>|status [glob]|inflight}" >&2; exit 2 ;;
esac

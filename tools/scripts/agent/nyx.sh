#!/usr/bin/env bash
# nyx.sh — nyxid 派票与状态分类。**不要再用 `tail -1` 肉眼判成败。**
#
# Caller contract: every ask/fetch invocation starts a NEW RUN for <out>.
# Append previous <out> bytes to <out>.history after a line
# NYX_RUN_BOUNDARY <utc-stamp> <verb>, then truncate <out>. History is audit only.
# Completion readers (status, await make/vote, tail) see RUNNING/no EXIT= until
# this run's sole terminal EXIT=<rc>. Unwritable artifacts fail with NYX_IO.
# <out>.taskid is append-only across runs; its last line is the current task ID.
# Use `nyx.sh taskid <out>` (prints that ID or exits 1), never parse the sidecar.
# ask submits afresh, including after terminal EXTRACTION/QUOTA/BUSY failures;
# fetch resumes the supplied task. A TIMEOUT still has a live task: use fetch.
# UNCERTAIN/DELIVERY stop without replay; inspect the retained task with fetch/result.
# await vote follows the command verdict; successful traversal settles the vote.
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
#   nyx.sh ask <brief> <outfile>     投一票;NYX_POOL 未设时**按池排名遍历**(见 pools),载体侧失败换下一池
#   nyx.sh fetch <task-id> <out>     续等一个已提交的任务(ask 超时后用它,不重复提交)
#   nyx.sh taskid <out>             Print the authoritative current task ID, or exit 1.
#   nyx.sh pools                     打印全部 active 池的排名表(脚本版本/在线 worker/空位/队列/可用性)
#   nyx.sh status [glob]             分类打印 /tmp/nyx-*.out 的真实状态
#   nyx.sh inflight                  当前 in-flight 数(NYX_POOL 或排名第一的池)
export PATH="$HOME/.local/bin:$PATH"
CLI="${NYX_CLI:-nyxid}"  # One executable/function name; no shell evaluation.
# 2026-08-28 实测:契约写 limit 4,但实际吞吐更低,且 `nyxid oracle status` 的 in-flight
# **包含别人的任务**(组织级共享池)—— 某刻显示 3 而我只有 2 张在跑。故保守取 2。
# 缺省 pool(2026-09-06 实测立、2026-09-08 复发后改默认):`extraction_failure` 由 pool 的
# **worker 脚本版本**决定,不是 brief 大小。同字节对照:`chatgpt-pro-pool`(`cdp-1.3-url-key-image`)
# 2/2 失败(17.9 KB 与 35.7 KB),同一份 17.9 KB 在 `chrono-chatgpt-pro-pool`(`0.11.7+…`)逐字节重发即成功,
# 该 pool 另测 24.5 KB 与 34.5 KB 亦成功。2026-09-08 复发:默认仍指向 cdp-1.3 那个 pool,
# 于是一份 8.1 KB 的 brief 连投两次都 `extraction_failure`,显式 `NYX_POOL=chrono-…` 才通。
# 缺省与已记录的用法背离,就是器自己产的坏原材料(第 8.4 条);故把缺省改成实测能用的那个。
#
# 池遍历(2026-09-08 下午立,用户问「有好几个池子,脚本能都遍历处理掉吗」):写死任何一个缺省池都会
# 在池容量随时间漂移时失效——同日实测:chrono 池 20 worker 仅 2 在线、队列 7,一行 JSON 排 20 min 排不到;
# company 池(`cdp-2.8.0-astra-resilient`,6 在线)4 min 即 NYX_OK。故 NYX_POOL **未设**时不再取固定缺省,
# 而是遍历 `nyxid oracle pool list` 的全部 active 池,按「在线空位多、队列短」排名,剔除已知坏脚本
# (NYX_BAD_SCRIPTS,前缀匹配,缺省 `cdp-1.3`)与零在线 worker 的池;载体侧失败(EXTRACTION/QUOTA)
# 换下一池重投同一份 brief。NYX_POOL 显式设定时保持旧行为:只投那一个池,不遍历(调用方要确定性时用)。
POOL="${NYX_POOL:-}"
BAD_SCRIPTS="${NYX_BAD_SCRIPTS:-cdp-1.3}"
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
POLL_ROUNDS="${NYX_POLL_ROUNDS-60}"
POLL_SECONDS="${NYX_POLL_SECONDS-20}"
OUT=""; OWNED_LOCK=""; LOCK_TRANSITION=0; CANCEL_RC=0

__uint() { [[ "$1" =~ ^[0-9]+$ ]] && [ "$1" -le 2147483647 ] 2>/dev/null; }
__uuid() { [[ "$1" =~ ^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$ ]]; }
__validate_settings() {
  { [ -z "$LIMIT" ] || { __uint "$LIMIT" && [ "$LIMIT" -gt 0 ]; }; } &&
    __uint "$POLL_ROUNDS" && [ "$POLL_ROUNDS" -gt 0 ] && __uint "$POLL_SECONDS" || {
    echo 'NYX_ERR NYX_LIMIT/NYX_POLL_ROUNDS must be positive integers; NYX_POLL_SECONDS must be nonnegative' >&2; return 2;
  }
  [ -z "$POOL" ] || [[ "$POOL" =~ ^[a-zA-Z0-9][a-zA-Z0-9._-]*$ ]] || {
    echo "NYX_ERR invalid pool slug: $POOL" >&2; return 2;
  }
  command -v "$CLI" >/dev/null || { echo "NYX_ERR CLI unavailable: $CLI" >&2; return 2; }
}
__append() {
  printf '%s\n' "$2" >> "$1" || { echo "NYX_IO cannot write: $1" >&2; LAST_VERDICT=IO; return 2; }
}
__cancel() {
  # Complete mkdir/rmdir bookkeeping before honoring a signal in that transition.
  if [ "$LOCK_TRANSITION" -eq 1 ]; then CANCEL_RC="$1"; else exit "$1"; fi
}
__release_lock() {
  local rc=0
  LOCK_TRANSITION=1
  if [ -n "$OWNED_LOCK" ]; then
    rmdir "$OWNED_LOCK" || { echo "NYX_IO cannot release lock: $OWNED_LOCK" >&2; rc=2; }
    OWNED_LOCK=""
  fi
  LOCK_TRANSITION=0
  [ "$CANCEL_RC" -eq 0 ] || exit "$CANCEL_RC"
  return "$rc"
}
__finish() {  # The only terminal sentinel writer, including pre-submit failures and signals.
  local rc="$1"
  trap - EXIT INT TERM
  case "$rc" in 130|143) echo "NYX_CANCELLED signal_rc=$rc" >&2;; esac
  CANCEL_RC=0
  __release_lock || rc=2
  if [ -n "$OUT" ]; then
    printf 'EXIT=%s\n' "$rc" >> "$OUT" || { echo "NYX_IO cannot write terminal sentinel: $OUT" >&2; rc=2; }
  fi
  exit "$rc"
}
__open_output() {
  local out="$1" verb="$2"
  [ -n "$out" ] && { [ ! -e "$out" ] || [ -f "$out" ]; } &&
    [ ! "$out" -ef "$out.taskid" ] && [ ! "$out" -ef "$out.history" ] &&
    [ ! "$out.taskid" -ef "$out.history" ] || {
    echo "NYX_IO outfile must be a writable regular file: $out" >&2; return 2;
  }
  if [ -e "$out" ]; then
    [ ! -e "$out.history" ] || [ -f "$out.history" ] || {
      echo "NYX_IO history must be a writable regular file: $out.history" >&2; return 2;
    }
    if [ -s "$out.history" ] && [ -n "$(tail -c 1 "$out.history")" ]; then __append "$out.history" '' || return 2; fi
    __append "$out.history" "NYX_RUN_BOUNDARY $(date -u +%Y-%m-%dT%H:%M:%SZ) $verb" || return 2
    cat "$out" >> "$out.history" || { echo "NYX_IO cannot archive: $out" >&2; return 2; }
  fi
  : > "$out" || { echo "NYX_IO cannot truncate: $out" >&2; return 2; }
  OUT="$out"
  # These handlers belong to the command, not to a candidate pool's lock path.
  trap '__finish $?' EXIT
  trap '__cancel 130' INT
  trap '__cancel 143' TERM
}
__taskid() {
  local id
  [ -f "$1.taskid" ] || return 1
  id=$(tail -1 "$1.taskid") || return 1
  __uuid "$id" || return 1
  printf '%s\n' "$id"
}
__open_taskids() {
  local out="$1" id
  [ ! "$out" -ef "$out.taskid" ] && { [ ! -e "$out.taskid" ] || [ -f "$out.taskid" ]; } && : >> "$out.taskid" || {
    echo "NYX_IO taskid must be a separate writable regular file: $out.taskid" >&2; return 2;
  }
  while IFS= read -r id || [ -n "$id" ]; do
    __uuid "$id" || { echo "NYX_ERR invalid recovery id: $out.taskid" >&2; return 2; }
  done < "$out.taskid"
}

__classify() {  # 读一个 .out,打印:OK|EXTRACTION|QUOTA|NOFILE|RUNNING|UNKNOWN
  local f="$1"
  [ -f "$f" ] || { echo NOFILE_OUT; return; }
  grep -qE '^EXIT=[0-9]+$' "$f" || { echo RUNNING; return; }
  if [ "$(tail -1 "$f")" = "EXIT=0" ]; then echo OK; return; fi
  grep -q 'oracle_quota_exceeded\|HTTP 429' "$f" && { echo QUOTA; return; }
  grep -q 'Failed to read prompt' "$f" && { echo NOFILE; return; }
  grep -q 'extraction_failure' "$f" && { echo EXTRACTION; return; }
  echo UNKNOWN
}

__expired() {  # 会话过期是能力缺口,不是池满 —— 必须与 in-flight 区分,否则白等 10 分钟
  "$CLI" oracle status "$POOL" 2>&1 | grep -q 'session has expired' && return 0 || return 1
}
__capacity() {  # pool 自报的总容量(Dispatched: N / M 的 M)
  local m status
  status=$("$CLI" oracle status "$POOL" 2>&1) || return 1
  m=$(printf '%s\n' "$status" | __pool_stats_parse "$POOL" | cut -d'|' -f5)
  __uint "$m" || return 1
  echo "$m"
}
__script_ver() {  # pool 自报的 worker 脚本版本 —— `extraction_failure` 的第一诊断位。
  # 取表格首个数据行的最后一列(Script)。读不到就空,调用方按缺失处理,不猜。
  # 注:`nyxid oracle status` 把表写到 **stderr**,必须 2>&1(与 __inflight 同坑)。
  "$CLI" oracle status "$POOL" 2>&1 | __script_ver_parse
}
__script_ver_parse() {  # 纯函数:从 stdin 读状态表,打印首个数据行的 Script 列
  awk -F'┆' '
    /┆/ {
      v = $NF
      gsub(/[│┆]/, "", v)
      gsub(/^[ \t]+|[ \t]+$/, "", v)
      if (v != "" && v != "Script") { print v; exit }
    }'
}
__inflight() {
  local n status
  status=$("$CLI" oracle status "$POOL" 2>&1) || return 1
  n=$(printf '%s\n' "$status" | __pool_stats_parse "$POOL" | cut -d'|' -f4)
  __uint "$n" || return 1
  echo "$n"
  # Status is emitted on stderr; an unreadable observation must not admit a submission.
}

# ---- 池遍历:三个纯函数 + 一个取数函数 -------------------------------------------------
__pools_active_parse() {  # 纯函数:从 stdin 读 `nyxid oracle pool list` 的表,打印 Active=yes 的 slug
  awk -F'┆' '
    /┆/ {
      s = $1; gsub(/[│┆]/, "", s); gsub(/^[ \t]+|[ \t]+$/, "", s)
      a = $5; gsub(/[│┆]/, "", a); gsub(/^[ \t]+|[ \t]+$/, "", a)
      if (s != "" && s != "Slug" && a == "yes") print s
    }'
}
__pool_stats_parse() {  # 纯函数:<slug> + stdin(该池的 status 文本)→ 一行 `slug|script|online|dispatched|capacity|queued|expired`
  # online = worker rows; missing/invalid dispatch and capacity stay unknown (?), never zero.
  local slug="$1"
  awk -v slug="$slug" -F'┆' '
    BEGIN { dispatched = capacity = "?" }
    /session has expired/ { expired = 1 }
    /Queued:/     { if (match($0, /Queued: *[0-9]+/)) { q = substr($0, RSTART, RLENGTH); sub(/Queued: */, "", q); queued = q } }
    /^[ \t]*Dispatched:[ \t]*[0-9]+[ \t]*\/[ \t]*[0-9]+[ \t]*$/ { d = $0; sub(/^[ \t]*Dispatched:[ \t]*/, "", d); split(d, p, /\//); gsub(/[ \t]/, "", p[1]); gsub(/[ \t]/, "", p[2]); dispatched = p[1]; capacity = p[2] }
    /┆/ {
      v = $NF; gsub(/[│┆]/, "", v); gsub(/^[ \t]+|[ \t]+$/, "", v)
      if (v != "" && v != "Script") { online++; if (script == "") script = v }
    }
    END { printf "%s|%s|%d|%s|%s|%d|%d\n", slug, script, online+0, dispatched, capacity, queued+0, expired+0 }'
}
__rank_pools() {  # 纯函数:stdin 读 __pool_stats_parse 的行,打印可用池 slug,按 空位 desc、队列 asc、slug asc
  # 可用 = 未过期 ∧ 在线 worker>0 ∧ 脚本已知 ∧ 脚本不以 BAD_SCRIPTS 任一前缀开头;空位 = min(在线, 容量) − dispatched(下限 0)
  awk -F'|' -v bad="$BAD_SCRIPTS" '
    BEGIN { nb = split(bad, B, / +/) }
    {
      if (NF != 7 || $1 !~ /^[a-zA-Z0-9][a-zA-Z0-9._-]*$/) next
      for (i = 3; i <= 7; i++) if ($i !~ /^[0-9]+$/ || $i + 0 > 2147483647) next
      slug = $1; script = $2; online = $3 + 0; dispatched = $4 + 0; capacity = $5 + 0; queued = $6 + 0; expired = $7 + 0
      if (expired || online == 0 || capacity == 0 || script == "") next
      isbad = 0; for (i = 1; i <= nb; i++) if (B[i] != "" && index(script, B[i]) == 1) isbad = 1
      if (isbad) next
      cap = (capacity < online) ? capacity : online
      free = cap - dispatched; if (free < 0) free = 0
      printf "%d %d %s\n", free, queued, slug
    }' | sort -k1,1nr -k2,2n -k3,3 | awk '{ print $3 }'
}
__pool_rows() {  # 取数:遍历全部 active 池,打印 __pool_stats_parse 行(每池一次 status 调用)
  local s listing status
  listing=$("$CLI" oracle pool list 2>&1) || return 1
  for s in $(printf '%s\n' "$listing" | __pools_active_parse); do
    status=$("$CLI" oracle status "$s" 2>&1) || continue
    printf '%s\n' "$status" | __pool_stats_parse "$s"
  done
}
__pools_table() {  # `pools` 动词:人读表 + 排名;判据与 ask 用的完全同一份(__rank_pools)
  local rows ranked
  rows=$(__pool_rows)
  ranked=$(printf '%s\n' "$rows" | __rank_pools | tr '\n' ' ')
  printf '%-26s %-28s %6s %10s %8s %6s %s\n' pool script online disp/cap queued expired eligible
  printf '%s\n' "$rows" | awk -F'|' -v ranked=" $ranked " '{
    el = (index(ranked, " " $1 " ") > 0) ? "yes" : "no"
    printf "%-26s %-28s %6s %10s %8s %6s %s\n", $1, ($2 == "" ? "-" : $2), $3, $4 "/" $5, $6, $7, el }'
  echo "NYX_POOLS ranked=[${ranked% }] bad_scripts=[$BAD_SCRIPTS]"
}

__verdict_of_payload() {  # 判**取回的文本**,不判文件 —— 活判决唯一合法的分类器。
  # 分界:载体是否把答案交回来了,与 worker 判词是 approve 还是 reject **无关**;
  # 故只认 nyxid CLI 自己的错误形态,不因答案里出现 "Error:" 字样而误判(见 --selftest 阴性对照)。
  local r="$1" cli_rc="${2:-0}" first last
  case "$r" in
    *oracle_quota_exceeded*|*"HTTP 429"*) echo QUOTA;      return;;
    *"Failed to read prompt"*)            echo NOFILE;     return;;
    *extraction_failure*)                 echo EXTRACTION; return;;
  esac
  # Delivery tokens need CLI failure evidence; successful answers can quote them.
  # NyxID 0d7afdaa docs/ORACLE_RELAY.md:395-410 forbids uncertain post-send replay;
  # "Message delivery timed out" has no upstream safe-retry promise either.
  [ -n "$r" ] || { echo UNKNOWN; return; }
  last=$(printf '%s' "$r" | awk 'NF{l=$0} END{print l}')
  # 2026-09-09 实测漏判:`nyxid oracle result` **exit 0** 而答案被截断,
  # 载体错误串**接在正文半句话后面、且落在整份 payload 的最末尾**
  # (末 60 字符 `…α>-1 的整个参数区Message delivery timed out. Please try again.Retry`),
  # 于是绕过下面的 cli_rc 门被判 OK —— 一次失败的派席在调用方眼里是成功的(第 8.4 条)。
  #
  # **判据是「以它结尾」∧「不只是它」两项合取**,三态各自可分:
  #   截断态  末行以该串**结尾**且**不等于**它(错误被接在半句话后)      → DELIVERY
  #   引用态  末行含该串但以答案自己的结尾收口(`…Retry"}`)             → 不触发(`answer-quotes-delivery-last-line`)
  #   纯诊断  末行**恰好等于**该串(`answer-delivery-text-zero-exit`)    → 不触发,交给 cli_rc 门按既有判例处理
  # 少任一项都会误判:只判「结尾」会翻掉纯诊断那条,只判「不等于」会翻掉引用那条(两次实测各红 1 条)。
  case "$last" in
    *"Message delivery timed out. Please try again.Retry")
      [ "$last" = "Message delivery timed out. Please try again.Retry" ] || { echo DELIVERY; return; };;
  esac
  if [ "$cli_rc" -ne 0 ]; then   # 只认 CLI 非零退出;exit 0 时末行即便是该诊断原文也是答案(复核 attempt 2 反例)
    case "$last" in
      *"Task failed (prompt_delivery_uncertain)"*) echo UNCERTAIN; return;;
      *"Message delivery timed out"*) echo DELIVERY; return;;
    esac
  fi
  first=${r%%$'\n'*}
  case "$first" in "Error:"*) echo UNKNOWN; return;; esac
  echo OK
}

__poll_task() {  # <task-id> <outfile>; ask/fetch share polling, __finish owns the sentinel.
  # **这不是挂钟猜测**(器律⑥′):池无 webhook,`nyxid oracle result` 是唯一取回原语;
  # 间隔对齐真实任务时长(实测数分钟级),有上限,且判据(__verdict_of_payload)在开跑前已写死。
  local tid="$1" out="$2" n=0 r rc verdict
  while [ $n -lt "$POLL_ROUNDS" ]; do
    r=$("$CLI" oracle result "$tid" 2>&1); rc=$?
    if [ "$rc" -eq 0 ]; then
      case "$r" in
        *"Task is dispatched"*|*"Phase:"*|*queued*) n=$((n+1)); sleep "$POLL_SECONDS"; continue;;
      esac
    else
      # 2026-09-09 实测:任务已成功提交(Task submitted)后,一次 `oracle result` 的 HTTP 连接
      # 超时(`error sending request for url … client error (Connect): operation timed out`)
      # 被当成终态,一票已派出的席位在调用方眼里成了失败(第 8.4 条坏原材料)。
      # 传输层错误不是任务判词:按一轮计数继续轮询,轮次耗尽走 TIMEOUT(任务仍可 fetch)。
      case "$r" in
        *"error sending request for url"*|*"client error (Connect)"*) n=$((n+1)); sleep "$POLL_SECONDS"; continue;;
      esac
    fi
    __append "$out" "$r" || return 2
    break
  done
  if [ $n -ge "$POLL_ROUNDS" ]; then
    echo "NYX_TIMEOUT $tid 仍未落定;可随时 nyx.sh fetch $tid <out> 续等,或 nyxid oracle result $tid 取回"
    rc=3; verdict=TIMEOUT
  else
    verdict=$(__verdict_of_payload "$r" "$rc")
    [ "$rc" -eq 0 ] || { [ "$verdict" != OK ] || verdict=UNKNOWN; }
    case "$verdict" in OK) rc=0;; *) rc=1;; esac
  fi
  case "$verdict" in
    UNCERTAIN|DELIVERY)
      printf 'NYX_%s task=%s pool=%s\n' "$verdict" "$tid" "${POOL:-<unknown>}"
      printf 'Inspect nyxid oracle result %s or nyx.sh fetch %s %q; do not resubmit.\n' "$tid" "$tid" "$out";;
    *) echo "NYX_$verdict $(basename "$out" .out)";;
  esac
  LAST_VERDICT="$verdict"
  return $rc
}

__submit_and_poll() {  # <brief> <out> —— 对当前 $POOL 投一票并取回;返回 __poll_task 的 rc,LAST_VERDICT 记判词
  local brief="$1" out="$2" n rc tid response inflight lock
  # 会话过期 → 立刻报能力缺口,不要当池满去等 10 分钟(2026-08-28 实测遇到)
  __expired && { echo "NYX_EXPIRED pool=$POOL 会话已过期 —— 需人跑 \`nyxid login\`(第15条:能力缺口,等灯亮)"; LAST_VERDICT=EXPIRED; return 4; }
  if [ -z "$LIMIT" ]; then
    LIMIT=$(__capacity) || { echo "NYX_UNKNOWN capacity pool=$POOL"; LAST_VERDICT=UNKNOWN; return 4; }
  fi
  [ "$LIMIT" -gt 0 ] || { echo "NYX_BUSY capacity=0 pool=$POOL"; LAST_VERDICT=BUSY; return 3; }
  # **锁**:检查 in-flight 与提交之间必须原子,否则两个并发 ask 会都看到有空位、都提交 → 429。
  # (2026-08-28 实测:并发两个 ask,in-flight=3,两者都判有空位,一者得 QUOTA。
  #  这是 TOCTOU 竞态 —— 器自己犯了它要防的那个错。)
  # 锁**按 pool 分片**:跨 pool 本无竞态,共用一把锁会让空闲 pool 的票排在满 pool 的票后面。
  lock="${TMPDIR:-/tmp}/nyx-ask-${POOL}.lock"
  n=0
  while [ -z "$OWNED_LOCK" ]; do
    LOCK_TRANSITION=1
    if mkdir "$lock" 2>/dev/null; then OWNED_LOCK="$lock"; fi
    LOCK_TRANSITION=0
    [ "$CANCEL_RC" -eq 0 ] || exit "$CANCEL_RC"
    [ -z "$OWNED_LOCK" ] || break
    n=$((n+1)); [ $n -gt 120 ] && { echo "NYX_LOCKBUSY 等锁超时: $out"; LAST_VERDICT=LOCKBUSY; return 3; }
    sleep 5
  done
  # 持锁期间等空位,再提交 —— 提交后立刻放锁(任务已计入 in-flight)
  n=0
  while :; do
    inflight=$(__inflight) || { echo "NYX_UNKNOWN inflight pool=$POOL"; LAST_VERDICT=UNKNOWN; return 4; }
    [ "$inflight" -ge "$LIMIT" ] && [ $n -lt 30 ] || break
    sleep 20; n=$((n+1))
  done
  if [ "$inflight" -ge "$LIMIT" ]; then
    __release_lock || { LAST_VERDICT=IO; return 2; }
    echo "NYX_BUSY pool=$POOL 等了 10 分钟仍满($LIMIT),放弃: $out"; LAST_VERDICT=BUSY; return 3
  fi
  # **--no-wait + 记 task id**:阻塞等待会让「我的进程生死」决定「任务是否丢失」。
  # 2026-08-28 实测:前台 ask 被 2min 超时杀、后台 ask 被 SIGTERM(exit 143)杀,
  # 而 `nyxid oracle result <task-id>` 显示**任务在池里仍活着**(`Phase: waiting_response`)。
  # 故改为提交后立刻拿 id 落盘,等待与取回分离 —— 被杀只丢等待,不丢工作。
  # **提交前把产地打出来**:失败判词只说 `extraction_failure`,不说是哪个 pool、哪个 worker 脚本,
  # 于是每次都要另跑一条 `nyxid oracle status` 才能归因。产地进输出即自诊断(第 8.4 条)。
  echo "NYX_SUBMIT pool=$POOL script=$(__script_ver) tag=$TAG brief_bytes=$(wc -c <"$brief" | tr -d ' ') out=$out"
  response=$("$CLI" oracle ask "$POOL" --file "$brief" --tag "$TAG" --no-wait 2>&1); rc=$?
  tid=$(printf '%s\n' "$response" | grep -oE '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' | tail -1)
  # Parse only this response; earlier attempts remain audit data, never submission input.
  __append "$out" "$response" || { echo "NYX_IO recovery task=${tid:-<none>} out=$out" >&2; return 2; }
  if [ -n "$tid" ]; then
    __append "$out.taskid" "$tid" || { echo "NYX_IO recovery task=$tid out=$out" >&2; return 2; }
  fi
  __release_lock || { LAST_VERDICT=IO; return 2; }
  if [ -z "$tid" ]; then
    LAST_VERDICT=$(__verdict_of_payload "$response" "$rc")
    [ "$LAST_VERDICT" != OK ] || LAST_VERDICT=UNKNOWN
    [ "$rc" -ne 0 ] || rc=1
    echo "NYX_$LAST_VERDICT $(basename "$out" .out)"; return "$rc"
  fi
  # 轮询取回与判词由 __poll_task 承担(唯一真源;ask 与 fetch 共用)。
  # **退出码必须反映取回的内容,不能写死 0**
  # (2026-08-28:no-wait 改造首跑即回归 —— `extraction_failure` 报了 EXIT=0,
  #  正是器律④「原材料好,不靠读者警惕」要禁的坏材料:调用方按退出码判就会误判成功。)
  # **进程退出码也必须反映判词**:此前 ask 分支以 echo 收尾,脚本恒 exit 0,
  # 于是写进文件的 EXIT= 与进程退出码可以相反 —— 同一个「坏原材料」病的第二个面。
  __poll_task "$tid" "$out"
}


case "${1:-}" in
  --selftest)
    # shellcheck source=tools/scripts/agent/nyx-selftest.sh
    . "$(dirname "$0")/nyx-selftest.sh"
    __selftest; exit $? ;;
  taskid) [ "$#" -eq 2 ] && __taskid "$2"; exit $? ;;
  pools) __validate_settings || exit 2; __pools_table ;;
  inflight)
    __validate_settings || exit 2
    [ -n "$POOL" ] || POOL=$(__pool_rows | __rank_pools | head -1)
    [ -n "$POOL" ] || { echo "NYX_NOPOOL 没有可用池"; exit 4; }
    __inflight ;;
  status)
    __validate_settings || exit 2
    printf "%-8s %-26s %6s %s\n" 时间 状态 字节 文件
    for f in ${2:-/tmp/nyx-*.out}; do
      printf "  %-8s %-26s %5sB %s\n" "$(stat -f '%Sm' -t '%H:%M' "$f")" "$(__classify "$f")" \
        "$(wc -c <"$f"|tr -d ' ')" "$(basename "$f" .out)"
    done | sort -k2
    [ -n "$POOL" ] || POOL=$(__pool_rows | __rank_pools | head -1)
    echo "  ---- pool=${POOL:-<none>} in-flight=$(__inflight)/${LIMIT:-$(__capacity)}"
    ;;
  fetch)
    # `ask` 的取回循环有上限;一个深研究任务(读 500KB 理论卷 + 仓库树)常跑得比它久。
    # 那时任务**仍活在池里**,只是没有动词能续等 —— 本会话两次撞上,故补此动词(器律⑥″:一切经器)。
    # 幂等:重复调用只是再取一次;不重复提交,不消耗配额。
    tid="${2:-}"; out="${3:-}"
    __open_output "$out" fetch || exit 2
    __validate_settings || exit 2
    [ "$#" -eq 3 ] || { echo 'NYX_ERR fetch needs <task-id> <outfile>' >&2; exit 2; }
    [ -n "$tid" ] || { echo "NYX_ERR fetch 需要 <task-id>"; exit 2; }
    [ -n "$out" ] || { echo "NYX_ERR fetch 需要 <outfile>"; exit 2; }
    __uuid "$tid" || { echo "NYX_ERR fetch 的 <task-id> 不是 uuid 形: $tid"; exit 2; }
    __open_taskids "$out" || exit 2
    if [ "$(__taskid "$out")" != "$tid" ]; then __append "$out.taskid" "$tid" || exit 2; fi
    __poll_task "$tid" "$out"; exit $?
    ;;
  ask)
    brief="${2:-}"; out="${3:-}"
    if [ "$brief" -ef "$out" ] || [ "$brief" -ef "$out.taskid" ] || [ "$brief" -ef "$out.history" ]; then
      echo 'NYX_ERR brief and recovery artifacts must be separate files' >&2; exit 2
    fi
    __open_output "$out" ask || exit 2
    __validate_settings || exit 2
    [ "$#" -eq 3 ] && [ -f "$brief" ] && [ -r "$brief" ] || { echo "NYX_ERR ask needs a readable brief and outfile: $brief"; exit 2; }
    [ -d "${TMPDIR:-/tmp}" ] && [ -w "${TMPDIR:-/tmp}" ] || { echo 'NYX_ERR TMPDIR must be writable' >&2; exit 2; }
    __open_taskids "$out" || exit 2
    if [ -n "$POOL" ]; then
      candidates="$POOL"   # 显式指定:只投这一个池,不遍历(调用方要确定性)
    else
      candidates=$(__pool_rows | __rank_pools | tr '\n' ' ')
      echo "NYX_POOLS ranked=[${candidates% }] bad_scripts=[$BAD_SCRIPTS]"
      [ -n "${candidates% }" ] || { echo "NYX_NOPOOL 没有可用池(全部过期/零在线/坏脚本/容量未知或零);查 nyx.sh pools"; exit 4; }
    fi
    rc=1; LAST_VERDICT=""; previous_pool=""
    for POOL in $candidates; do
      [ -z "$previous_pool" ] || echo "NYX_NEXT_POOL after=$previous_pool verdict=$LAST_VERDICT"
      previous_pool="$POOL"
      LIMIT="${NYX_LIMIT:-}"   # 每池按自报容量重新派生
      __submit_and_poll "$brief" "$out"; rc=$?
      case "$LAST_VERDICT" in
        EXTRACTION|QUOTA|BUSY|EXPIRED) ;;
        *) break;;   # Includes UNCERTAIN/DELIVERY: no evidence that replay is safe.
      esac
    done
    exit $rc
    ;;
  *) echo "usage: nyx.sh {ask <brief> <out>|fetch <task-id> <out>|taskid <out>|pools|status [glob]|inflight|--selftest}" >&2; exit 2 ;;
esac

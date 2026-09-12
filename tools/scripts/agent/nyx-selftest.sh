#!/usr/bin/env bash
# Sourced by nyx.sh --selftest so fixtures exercise its internal functions.
# shellcheck disable=SC2329 # Fake commands are exported for invocation in child shells.

__selftest() {  # 分类器的阳性/阴性对照。**立条依据(2026-09-06)**:`__classify` 的 OK 分支要求
  # `tail -1 = EXIT=0`,而 `EXIT=` 是**分类之后**才追加的 —— 在 ask 的活判决里该分支
  # **结构上不可达**,于是每一次成功取回都被判 rc=1。器律④:坏原材料让调用方误判。
  # 该错配无运行期信号(答案就在文件里,只有退出码是错的),故必须由对照钉住。
  local fail=0 cases=0 got
  # shellcheck disable=SC2034 # Dynamically scoped input to nyx.sh's __rank_pools.
  local BAD_SCRIPTS=cdp-1.3 LIMIT=''
  chk() {  # chk <expected> <name> <payload> [CLI exit status]
    cases=$((cases+1))
    got=$(__verdict_of_payload "$3" "${4:-0}" 2>/dev/null)
    if [ "$got" = "$1" ]; then printf '  ok   %-30s %s\n' "$2" "$got"
    else printf '  FAIL %-30s expected=%s got=%s\n' "$2" "$1" "${got:-<none>}"; fail=1; fi
  }
  # 阳性:真答案必须判 OK —— 载体成功与 worker 判词是两回事,reject 也是成功取回
  chk OK         answer-json                '{"ok":true}'
  chk OK         answer-reject-verdict      '{"verdict":"reject","conclusion":{"a":1}}'
  chk OK         answer-contains-error-word '{"verdict":"reject","note":"Error: in their proof"}'
  chk OK         answer-multiline-err-later "$(printf 'line one\nError: quoted from their log')"
  # 阴性:载体侧失败必须各自可辨,不得混成一个
  chk EXTRACTION carrier-extraction         'Error: Task failed (extraction_failure).'
  chk CARRIER    carrier-unknown-reason     'Error: Task failed (composer_draft_conflict).' 1
  chk CARRIER    carrier-future-reason      'Error: Task failed (some_reason_not_yet_invented).' 1
  chk UNKNOWN    carrier-named-reason-zero-exit 'Error: Task failed (composer_draft_conflict).' 0
  chk INFRA      carrier-infra-exhausted    "$(printf '%s\n' 'Attempts: 4 (infrastructure retries 3/3)' \
    'Error: Task failed (infrastructure_retry_exhausted).')" 1
  chk QUOTA      carrier-quota-429          'Error: HTTP 429 {"error":"oracle_quota_exceeded"}'
  chk NOFILE     carrier-prompt-missing     'Error: Failed to read prompt'
  # 载体投递失败:失败文本是 payload 的**末行**
  chk DELIVERY   carrier-delivery-timeout   "$(printf '%s\n' 'Attempts: 1 (infrastructure retries 0/3)' \
    'Message delivery timed out. Please try again.Retry')" 1
  chk UNCERTAIN  carrier-prompt-uncertain   "$(printf '%s\n' 'Attempts: 1 (infrastructure retries 0/3)' 'Error: Task failed (prompt_delivery_uncertain).')" 1
  chk OK         answer-quotes-prompt-uncertain "$(printf '%s\n' 'The seat hit Error: Task failed (prompt_delivery_uncertain). earlier' '{"verdict":"approve"}')"
  chk UNKNOWN bare-diagnostic-line-zero-exit-uncertain 'Error: Task failed (prompt_delivery_uncertain).' 0   # 单行 Error: 却 exit 0 = 自相矛盾,fail-closed 判 UNKNOWN(不是 OK 也不是 UNCERTAIN)
  chk OK answer-multiline-prompt-uncertain-last-line-zero-exit "$(printf '%s\n' 'The exact diagnostic is:' 'Error: Task failed (prompt_delivery_uncertain).')" 0
  chk UNCERTAIN carrier-prompt-uncertain-nonzero 'Task failed (prompt_delivery_uncertain).' 1
  chk OK answer-quotes-prompt-uncertain-last-line "$(printf '%s\n' 'Attempts: 1 (infrastructure retries 0/3)' \
    '{"verdict":"approve","note":"Error: Task failed (prompt_delivery_uncertain)."}')" 0
  chk OK answer-prompt-uncertain-text-zero-exit 'Task failed (prompt_delivery_uncertain).' 0
  chk UNKNOWN bare-diagnostic-line-zero-exit-delivery 'Error: Task failed (Message delivery timed out).' 0
  chk OK answer-quotes-delivery-last-line '{"verdict":"approve","note":"Message delivery timed out. Please try again.Retry"}' 0
  # 阳性:CLI exit 0 但正文被截断,载体串粘在**结尾** —— 必须判 DELIVERY(2026-09-09 实测漏判)
  chk DELIVERY carrier-delivery-tail-zero-exit "$(printf '%s\n' 'Attempts: 1 (infrastructure retries 0/3)' \
    'to m=3 one still needs a new certificate over the whole parameter rangeMessage delivery timed out. Please try again.Retry')" 0
  chk OK answer-delivery-text-zero-exit "$(printf '%s\n' 'Attempts: 1 (infrastructure retries 0/3)' 'Message delivery timed out. Please try again.Retry')" 0
  # 阴性对照:**真答案里引用了同一句失败文本**,但末行是答案 —— 必须仍判 OK。
  # 这条钉的正是「不做全文子串匹配」;改成全文匹配它立刻变红。
  chk OK         answer-quotes-delivery-text "$(printf '%s\n' \
    'The seat reported: Message delivery timed out. Please try again.' \
    '{"verdict":"reject","conclusion":{"blocking":1}}')"
  chk UNKNOWN    carrier-bare-error         'Error: forbidden'
  chk UNKNOWN    empty-payload              ''
  # Script 列解析的阳性/阴性对照:缺省 pool 的选择依赖它,解析错了就诊断错了。
  chkv() {  # chkv <期望> <名字> <表格文本>
    cases=$((cases+1))
    got=$(printf '%s\n' "$3" | __pool_stats_parse fixture | cut -d'|' -f2)
    if [ "$got" = "$1" ]; then printf '  ok   %-30s %s\n' "$2" "${got:-<empty>}"
    else printf '  FAIL %-30s expected=%s got=%s\n' "$2" "$1" "${got:-<none>}"; fail=1; fi
  }
  chkv 'cdp-1.3-url-key-image' script-first-data-row "$(printf '%s\n' \
    '│ Worker          ┆ Seen (s ago) ┆ Task ┆ Script                │' \
    '╞═════════════════╪══════════════╪══════╪═══════════════════════╡' \
    '│ share_account_6 ┆ 0            ┆ -    ┆ cdp-1.3-url-key-image │' \
    '│ share_account_5 ┆ 0            ┆ -    ┆ cdp-1.3-url-key-image │')"
  chkv '0.11.7+63d573839245' script-other-version "$(printf '%s\n' \
    '│ Worker ┆ Seen ┆ Task ┆ Script             │' \
    '│ w1     ┆ 3    ┆ -    ┆ 0.11.7+63d573839245 │')"
  chkv '' script-no-table "$(printf '%s\n' "Pool 'x':" '  Queued:     0' '  Dispatched: 0 / 20')"

  # 池遍历三个纯函数的对照(2026-09-08 立):排名错了就把票投进坏池,与固定缺省同病。
  chke() {  # chke <期望> <名字> <实际>
    cases=$((cases+1))
    if [ "$3" = "$1" ]; then printf '  ok   %-30s %s\n' "$2" "${3:-<empty>}"
    else printf '  FAIL %-30s expected=[%s] got=[%s]\n' "$2" "$1" "$3"; fail=1; fi
  }
  local plist st_company st_bad st_idle st_expired rows
  plist=$(printf '%s\n' \
    '│ Slug                ┆ Name        ┆ Visibility ┆ Workers ┆ Active ┆ Manage │' \
    '╞═════════════════════╪═════════════╪════════════╪═════════╪════════╪════════╡' \
    '│ company-chatgpt-pro ┆ Company     ┆ org        ┆ 10      ┆ yes    ┆ no     │' \
    '│ old-pool            ┆ Old         ┆ org        ┆ 20      ┆ yes    ┆ yes    │' \
    '│ paused-pool         ┆ Paused      ┆ org        ┆ 3       ┆ no     ┆ yes    │' \
    '│ heca-1              ┆ Private     ┆ private    ┆ 1       ┆ yes    ┆ yes    │')
  chke 'company-chatgpt-pro old-pool heca-1' pools-active-parse "$(printf '%s\n' "$plist" | __pools_active_parse | tr '\n' ' ' | sed 's/ $//')"
  st_company=$(printf '%s\n' "Pool 'company-chatgpt-pro':" '  Queued:     2' '  Dispatched: 4 / 10' '  Diagnosis:  running' \
    '│ Worker ┆ Seen (s ago) ┆ Task ┆ Script                    │' \
    '│ w1     ┆ 2            ┆ t1   ┆ cdp-2.8.0-astra-resilient │' \
    '│ w2     ┆ 4            ┆ -    ┆ cdp-2.8.0-astra-resilient │' \
    '│ w3     ┆ 4            ┆ -    ┆ cdp-2.8.0-astra-resilient │' \
    '│ w4     ┆ 9            ┆ t2   ┆ cdp-2.8.0-astra-resilient │' \
    '│ w5     ┆ 13           ┆ t3   ┆ cdp-2.8.0-astra-resilient │' \
    '│ w6     ┆ 21           ┆ t4   ┆ cdp-2.8.0-astra-resilient │')
  chke 'company-chatgpt-pro|cdp-2.8.0-astra-resilient|6|4|10|2|0' pool-stats-parse-company "$(printf '%s\n' "$st_company" | __pool_stats_parse company-chatgpt-pro)"
  st_bad=$(printf '%s\n' "Pool 'old-pool':" '  Queued:     0' '  Dispatched: 0 / 20' \
    '│ Worker ┆ Seen ┆ Task ┆ Script                │' \
    '│ a      ┆ 1    ┆ -    ┆ cdp-1.3-url-key-image │')
  chke 'old-pool|cdp-1.3-url-key-image|1|0|20|0|0' pool-stats-parse-bad-script "$(printf '%s\n' "$st_bad" | __pool_stats_parse old-pool)"
  st_idle=$(printf '%s\n' "Pool 'heca-1':" '  Queued:     1' '  Dispatched: 0 / 1')
  st_expired=$(printf '%s\n' "Pool 'chrono':" 'Error: session has expired')
  chke 'heca-1||0|0|1|1|0' pool-stats-parse-no-workers "$(printf '%s\n' "$st_idle" | __pool_stats_parse heca-1)"
  chke 'chrono||0|?|?|0|1' pool-stats-parse-expired "$(printf '%s\n' "$st_expired" | __pool_stats_parse chrono)"
  chke 'x||0|?|?|0|0' pool-stats-missing-capacity "$(printf '%s\n' 'Queued: 0' | __pool_stats_parse x)"
  chke 'x||0|?|?|0|0' pool-stats-invalid-capacity "$(printf '%s\n' 'Dispatched: 0 / 6oops' | __pool_stats_parse x)"
  chke 'x||0|0|0|0|0' pool-stats-zero-capacity "$(printf '%s\n' 'Dispatched: 0 / 0' | __pool_stats_parse x)"
  rows=$(printf '%s\n' \
    'company-chatgpt-pro|cdp-2.8.0-astra-resilient|6|4|10|2|0' \
    'old-pool|cdp-1.3-url-key-image|5|0|20|0|0' \
    'heca-1||0|0|1|1|0' \
    'chrono|0.11.7+63d573839245|3|2|20|7|0' \
    'expired-pool|0.11.7+63d573839245|3|0|20|0|1' \
    'fresh|0.11.7+63d573839245|3|0|20|0|0')
  # 期望:fresh(空位 3,队列 0)> company(空位 2)> chrono(空位 1);old-pool 坏脚本、heca 零在线、expired 过期均剔除
  chke 'fresh company-chatgpt-pro chrono' rank-pools-order "$(printf '%s\n' "$rows" | __rank_pools | tr '\n' ' ' | sed 's/ $//')"
  # 同空位按队列短优先;再同则 slug 字典序(确定性,不随 status 输出顺序变)
  chke 'b-pool a-pool' rank-pools-tiebreak "$(printf '%s\n' 'a-pool|v|4|1|10|5|0' 'b-pool|v|4|1|10|1|0' | __rank_pools | tr '\n' ' ' | sed 's/ $//')"
  # BAD_SCRIPTS 是前缀匹配、可多项:把 0.11.7 也列为坏时 chrono 被剔
  chke 'company-chatgpt-pro' rank-pools-bad-prefix-list "$(printf '%s\n' "$rows" | BAD_SCRIPTS='cdp-1.3 0.11.7' __rank_pools | tr '\n' ' ' | sed 's/ $//')"
  # 全部剔除 ⟹ 空(调用方按 NYX_NOPOOL 处理,不猜)
  chke '' rank-pools-none "$(printf '%s\n' 'old-pool|cdp-1.3-url-key-image|5|0|20|0|0' | __rank_pools | tr '\n' ' ' | sed 's/ $//')"
  chke 'known-capacity' rank-pools-unknown-zero-capacity "$(printf '%s\n' \
    'unknown-capacity|v|6|0|?|0|0' 'missing-capacity|v|6|0||0|0' \
    'invalid-capacity|v|6|0|bad|0|0' 'zero-capacity|v|6|0|0|0|0' \
    'known-capacity|v|6|5|6|0|0' | __rank_pools)"

  # 回归钉:文件级 __classify 在「最后一行是答案」的文件上必判 RUNNING,
  # 这正是它不能用于活判决的原因;若有人把它改回去,本例变红。
  local tmp; tmp=$(mktemp) || return 1
  printf 'Task submitted.\n\n{"ok":true}\n' > "$tmp"
  got=$(__classify "$tmp")
  chke RUNNING file-classifier-unusable-live "$got"
  printf 'Error: Task failed (extraction_failure).\n' > "$tmp"
  chke RUNNING file-classifier-carrier-running "$(__classify "$tmp")"; rm -f "$tmp"
  # Run the real command dispatcher in child shells with an isolated, fail-closed CLI.
  # Fixture columns: slug|script|online|dispatched|capacity|queued|response|task-id.
  __nyx_fake_cli() {
    local slug script online dispatched capacity queued response id i
    printf '%s\n' "$*" >> "$NYX_TEST_DIR/calls"
    [ "$1" = oracle ] || return 97
    if [ "$2 $3" = 'pool list' ] && [ "${NYX_TEST_LIST_ERROR:-}" = 1 ]; then
      echo 'Error: pool discovery unavailable'; return 7
    fi
    [ "$2" != result ] || printf '%s\n' "$3" >> "$NYX_TEST_DIR/polls"
    while IFS='|' read -r slug script online dispatched capacity queued response id; do
      if [ "$2 $3" = 'pool list' ]; then
        printf '│ %s ┆ Fixture ┆ org ┆ %s ┆ yes ┆ no │\n' "$slug" "$online"; continue
      fi
      if [ "$2" = result ]; then
        if [ "${NYX_TEST_UNIQUE_IDS:-}" = 1 ]; then [ "${3%-*}" = "${id%-*}" ] || continue; id="$3"
        else [ "$3" = "$id" ] || continue; fi
      else [ "$3" = "$slug" ] || continue; fi
      case "$2" in
        status)
          printf '%s\n' status >> "$NYX_TEST_DIR/status-$slug"
          i=$(wc -l < "$NYX_TEST_DIR/status-$slug")
          if [ "$i" -gt 1 ]; then
            printf '%s|%s\n' "$slug" "$(if [ -d "$NYX_TEST_DIR/nyx-ask-$slug.lock" ]; then echo locked; else echo unlocked; fi)" >> "$NYX_TEST_DIR/refreshes"
            case "$response" in
              late-read) echo 'Error: status transport unavailable'; return 7;;
              alternating-read) if [ "$((i%2))" -eq 0 ]; then echo 'Error: status transport unavailable'; return 7; fi;;
              late-parse) capacity=garbled;;
              late-offline) online=0;;
              late-full) dispatched="$capacity";;
              late-zero) capacity=0;;
              late-filter) script=cdp-1.3-old;;
              late-script) script='';;
              late-shrink) capacity=1; dispatched=1;;
              late-expiry) echo 'Error: session has expired'; return 1;;
            esac
          fi
          if [ "$response" = full-then-free ] && [ "$i" -eq 1 ]; then dispatched="$capacity"; fi
          if [ "$response" = expired ] || { [ "$response" = late-expired ] && [ -s "$NYX_TEST_DIR/submits" ]; }; then
            echo 'Error: session has expired'; return 1
          fi
          if [ "$capacity" != '?' ]; then printf '  Dispatched: %s / %s\n' "$dispatched" "$capacity"; fi
          printf '  Queued: %s\n│ Worker ┆ Seen ┆ Task ┆ Script │\n' "$queued"
          i=0; while [ "$i" -lt "$online" ]; do
            printf '│ w%s ┆ 1 ┆ - ┆ %s │\n' "$i" "$script"; i=$((i+1))
          done; return 0;;
        ask)
          [ "$4" = --file ] && [ -r "$5" ] && [ "$6" = --tag ] && [ "$7" = "${NYX_TEST_EXPECT_TAG:-mode:chat}" ] && [ "$8" = --no-wait ] || return 97
          cmp -s "$5" "$NYX_TEST_DIR/expected-brief" || return 97
          printf '%s\n' "$slug" >> "$NYX_TEST_DIR/submits"
          if [ "${NYX_TEST_UNIQUE_IDS:-}" = 1 ]; then id="${id%-*}-$(printf '%012d' "$(wc -l < "$NYX_TEST_DIR/submits")")"; fi
          case "$response" in
            quota) echo 'Error: HTTP 429 oracle_quota_exceeded'; return 1;;
            nofile) echo 'Error: Failed to read prompt'; return 2;;
            unknown) echo 'Error: forbidden'; return 7;;
            noid) echo 'Accepted without an id'; return 0;;
            submit-uncertain) echo 'Error: Task failed (prompt_delivery_uncertain).'; return 1;;
            submit-delivery) echo 'Message delivery timed out. Please try again.Retry'; return 1;;
            id-write-error) rm "$NYX_TEST_OUT.taskid"; command mkdir "$NYX_TEST_OUT.taskid";;
          esac
          printf 'Task submitted: %s\n' "$id"; return 0;;
        result)
          case "$response" in
            extraction) echo 'Error: Task failed (extraction_failure).'; return 1;;
            composer)
              echo 'Error: Task failed (composer_draft_conflict).'; return 1;;
            infra)
              printf '%s\n' 'Attempts: 4 (infrastructure retries 3/3)' \
                'Error: Task failed (infrastructure_retry_exhausted).'; return 1;;
            delivery|delivery-zero-exit)
              printf '%s\n' 'Attempts: 1 (infrastructure retries 0/3)' 'Message delivery timed out. Please try again.Retry'
              if [ "$response" = delivery ]; then return 1; fi;;
            prompt-uncertain) printf '%s\n' "Conversation: https://chatgpt.com/c/$id" 'Attempts: 1 (infrastructure retries 0/3)' 'Error: Task failed (prompt_delivery_uncertain).'; return 1;;
            quote-prompt-uncertain) printf '%s\n' 'Attempts: 1 (infrastructure retries 0/3)' '{"verdict":"approve","note":"Error: Task failed (prompt_delivery_uncertain)."}';;
            quote-delivery-last-line) printf '%s\n' 'Attempts: 1 (infrastructure retries 0/3)' '{"verdict":"approve","note":"Message delivery timed out. Please try again.Retry"}';;
            quote) printf '%s\n' 'Quoted: Message delivery timed out. Please try again.' '{"verdict":"reject"}';;
            timeout) echo 'Phase: waiting_response';;
            resume) if [ "$(wc -l < "$NYX_TEST_DIR/polls")" -le 2 ]; then echo 'Phase: waiting_response'; else echo '{"ok":true}'; fi;;
            barrier) printf 'ready\n' > "$NYX_TEST_DIR/ready"; IFS= read -r response < "$NYX_TEST_DIR/release"; echo '{"ok":true}';;
            result-error) echo 'Unexpected transport failure'; return 1;;
            result-rate-limit) echo 'Error: HTTP 429 oracle_quota_exceeded'; return 1;;
            result-observation-infra) echo 'Error: GET /oracle/tasks failed: infrastructure_retry_exhausted'; return 1;;
            result-zero-exit-failure) echo 'Error: Task failed (extraction_failure).'; return 0;;
            transient|transient-forever)
              if [ "$response" = transient-forever ] || [ "$(wc -l < "$NYX_TEST_DIR/polls")" -le 1 ]; then
                echo "Error: GET /oracle/tasks/$id failed: error sending request for url (https://example.invalid/oracle/tasks/$id): client error (Connect): operation timed out"; return 1
              fi
              echo '{"ok":true}';;
            *) echo '{"ok":true}';;
          esac; return 0;;
        *) return 97;;
      esac
    done <<< "$NYX_TEST_ROWS"
    [ "$2 $3" = 'pool list' ] || return 97
  }
  local testroot run_name run_dir run_out run_rc run_rows run_env run_args run_script
  local await_script; await_script="$(dirname "$0")/await.sh"
  local id1=11111111-1111-4111-8111-111111111111 id2=22222222-2222-4222-8222-222222222222 id3=33333333-3333-4333-8333-333333333333
  local selection traversal third
  testroot=$(mktemp -d) || return 1
  selection=$(printf '%s\n' "bad|cdp-1.3-old|3|0|3|0|extraction|$id1" "idle|v|0|0|2|0|answer|$id2" "good|v|1|0|1|0|answer|$id3")
  traversal=$(printf '%s\n' "second|v|1|0|1|0|answer|$id2" "first|v|2|0|2|0|extraction|$id1")
  third="third|v|1|0|1|1|answer|$id3"
  run_case() {
    run_name="$1"; run_rows="$2"; shift 2
    run_dir="$testroot/$run_name"; run_out="$run_dir/result.out"
    mkdir "$run_dir" || return 1
    printf 'fixture brief\n' > "$run_dir/brief"
    cp "$run_dir/brief" "$run_dir/expected-brief"
    : > "$run_dir/calls"; : > "$run_dir/submits"; : > "$run_dir/polls"; : > "$run_dir/sleeps"
    case "$run_name" in
      ask-output-init-error) mkdir "$run_out";;
      ask-sidecar-init-error) mkdir "$run_out.taskid";;
      ask-first-locked) mkdir "$run_dir/nyx-ask-first.lock";;
      ask-*-stale) printf '%s\n' "$id3" > "$run_out.taskid";;
      *foreign*|ask-lockbusy) mkdir "$run_dir/nyx-ask-second.lock";;
      await-vote-*) printf '%s\n' "$id3" > "$run_out.taskid"; printf 'EXIT=1\n' > "$run_out"; : > "$run_out.settled";;
    esac
    run_env=("TMPDIR=$run_dir" 'NYX_CLI=__nyx_fake_cli' 'NYX_POOL=' 'NYX_LIMIT=' 'NYX_BAD_SCRIPTS=cdp-1.3' 'NYX_TAG=mode:chat'
      'NYX_POLL_SECONDS=0' 'NYX_POLL_ROUNDS=2' "NYX_TEST_DIR=$run_dir" "NYX_TEST_OUT=$run_out" "NYX_TEST_ROWS=$run_rows"
      'NYX_TEST_SIGNAL=' 'NYX_TEST_CANCEL=' 'NYX_TEST_WRITE_ERROR=' 'NYX_TEST_UNIQUE_IDS='
      'NYX_TEST_RELEASE_ERROR=' 'NYX_TEST_LIST_ERROR=' 'NYX_TEST_EXPECT_TAG=mode:chat' 'AWAIT_TICK=0' 'AWAIT_DEADLINE=5400' "$@")
    if [ "$run_name" = ask-default-unset-filter ]; then
      local setting_index
      for setting_index in "${!run_env[@]}"; do
        case "${run_env[$setting_index]}" in NYX_BAD_SCRIPTS=*) unset 'run_env[setting_index]';; esac
      done
    fi
    run_script="$0"
    run_args=(ask "$run_dir/brief" "$run_out")
    case "$run_name" in fetch-*) run_args=(fetch "$id1" "$run_out");; esac
    case "$run_name" in await-vote-*) run_script="$await_script"; run_args=(vote "$run_dir/brief" "$run_out" 2);; esac
    case "$run_name" in
      ask-missing-brief) run_args=(ask "$run_dir/missing" "$run_out");;
      fetch-invalid-id) run_args=(fetch '1-2-3-4-5' "$run_out");;
    esac
    run_child > "$run_dir/stdout" 2>&1; run_rc=$?
  }
  run_child() (
    # No real nyxid call or wall-clock delay can escape a selftest child.
    nyxid() { echo NYX_TEST_UNEXPECTED_CLI >&2; return 97; }
    sleep() { printf '%s\n' "$*" >> "$NYX_TEST_DIR/sleeps"; }
    rmdir() {
      printf '%s\n' "$*" >> "$NYX_TEST_DIR/releases"
      if [ "$NYX_TEST_RELEASE_ERROR" = 1 ] && [ "$1" = "$NYX_TEST_DIR/nyx-ask-first.lock" ]; then return 1; fi
      command rmdir "$@"
    }
    printf() {
      if [ "$BASH_SUBSHELL" -eq 0 ] && [ "$NYX_TEST_WRITE_ERROR" = submit ] && [[ "${2:-}" = 'Task submitted:'* ]]; then return 1; fi
      command printf "$@"
    }
    mkdir() {
      local rc
      printf '%s\n' "$*" >> "$NYX_TEST_DIR/lock-attempts"
      if [ "$NYX_TEST_CANCEL" = foreign ] && [ "$1" = "$NYX_TEST_DIR/nyx-ask-second.lock" ]; then
        kill -s "$NYX_TEST_SIGNAL" "$$"; return 1
      fi
      command mkdir "$@"; rc=$?
      if [ "$rc" -eq 0 ] && [ "$NYX_TEST_CANCEL" = owned ]; then kill -s "$NYX_TEST_SIGNAL" "$$"; fi
      return "$rc"
    }
    export -f __nyx_fake_cli nyxid sleep mkdir rmdir printf
    [ "$run_name" != ask-default-unset-filter ] || unset NYX_BAD_SCRIPTS
    env "${run_env[@]}" bash "$run_script" "${run_args[@]}"
  )
  joined() { if [ -f "$1" ]; then awk 'NF {printf "%s%s", sep, $0; sep=","}' "$1"; fi; }
  check_run() {  # rc | final line | submissions | recorded IDs | polled IDs | next pools | last verdict
    local last='' next verdict actual
    [ ! -f "$run_out" ] || last=$(tail -1 "$run_out")
    next=$(awk '/^NYX_NEXT_POOL / {sub(/^after=/,"",$2); printf "%s%s", sep, $2; sep=","}' "$run_dir/stdout")
    verdict=$(awk '/^NYX_(OK|EXTRACTION|INFRA|CARRIER|QUOTA|NOFILE|UNKNOWN|DELIVERY|UNCERTAIN|NOPOOL|BUSY|EXPIRED|LOCKBUSY|PRECHECK|TIMEOUT|IO|ERR|CANCELLED)( |$)/ {v=$1} END {print v}' "$run_dir/stdout")
    actual="$run_rc|$last|$(joined "$run_dir/submits")|$(joined "$run_out.taskid")|$(joined "$run_dir/polls")|$next|$verdict"
    chke "$1" "$run_name" "$actual"
    [ "$actual" = "$1" ] || cat "$run_dir/stdout"
  }
  run_case ask-select-good "$selection"
  check_run "0|EXIT=0|good|$id3|$id3||NYX_OK"
  run_case ask-ranked-traversal "$traversal"
  check_run "0|EXIT=0|first,second|$id1,$id2|$id1,$id2|first|NYX_OK"
  # infrastructure_retry_exhausted 是池作用域的终局,遍历必须继续投下一个排名池。
  # 这条红过:未分类时它落进 UNKNOWN,遍历在第一个池就 break,submits 只有 first。
  run_case ask-infra-then-answer "${traversal/extraction/infra}"
  check_run "0|EXIT=0|first,second|$id1,$id2|$id1,$id2|first|NYX_OK"
  # 规则(而非 token 名单)的钉子:一个从未被列举过的 reason 也必须换池。
  run_case ask-composer-then-answer "${traversal/extraction/composer}"
  check_run "0|EXIT=0|first,second|$id1,$id2|$id1,$id2|first|NYX_OK"
  run_name=fetch-rerun-resumes; run_args=(fetch "$id2" "$run_out")
  run_child > "$run_dir/stdout" 2>&1; run_rc=$?
  check_run "0|EXIT=0|first,second|$id1,$id2|$id1,$id2,$id2||NYX_OK"
  run_case ask-all-bad "bad|cdp-1.3-old|1|0|1|0|answer|$id1"
  check_run '4|EXIT=4|||||NYX_NOPOOL'
  run_case ask-explicit-bad "$selection" NYX_POOL=bad
  check_run "1|EXIT=1|bad|$id1|$id1||NYX_EXTRACTION"
  run_case ask-busy "second|v|1|1|1|0|answer|$id2"
  check_run '3|EXIT=3|||||NYX_BUSY'
  run_case ask-extraction-then-busy "${traversal/second|v|1|0/second|v|1|1}"
  check_run "3|EXIT=3|first|$id1|$id1|first|NYX_BUSY"
  run_case ask-extraction-then-nofile "${traversal/answer/nofile}"$'\n'"$third"
  check_run "2|EXIT=2|first,second|$id1|$id1|first|NYX_NOFILE"
  rows="${traversal/extraction/quota}"
  run_case ask-quota-then-unknown "${rows/answer/unknown}"$'\n'"$third" NYX_LIMIT=1
  check_run '7|EXIT=7|first,second|||first|NYX_UNKNOWN'
  run_case ask-extraction-then-expired "${traversal/answer/late-expired}"
  check_run "4|EXIT=4|first|$id1|$id1|first|NYX_EXPIRED"
  run_case ask-expired "first|v|1|0|1|0|expired|$id1" NYX_POOL=first
  check_run '4|EXIT=4|||||NYX_EXPIRED'
  run_case ask-lockbusy "second|v|1|0|1|0|answer|$id2"
  check_run '3|EXIT=3|||||NYX_LOCKBUSY'
  local signal cancel expected response rows_one="first|v|1|0|1|0|answer|$id1"
  for signal in INT TERM; do
    case "$signal" in INT) expected=130;; TERM) expected=143;; esac
    for cancel in owned foreign; do
      run_case "ask-cancel-$cancel-$signal" "$traversal" "NYX_TEST_SIGNAL=$signal" "NYX_TEST_CANCEL=$cancel"
      if [ "$cancel" = owned ]; then check_run "$expected|EXIT=$expected|||||NYX_CANCELLED"
      else check_run "$expected|EXIT=$expected|first|$id1|$id1|first|NYX_CANCELLED"; fi
      chke "$cancel" "lock-ownership-$cancel-$signal" "$(if [ -d "$run_dir/nyx-ask-second.lock" ]; then echo foreign; else echo owned; fi)"
      chke absent "lock-released-first-$signal-$cancel" "$(if [ -d "$run_dir/nyx-ask-first.lock" ]; then echo leaked; else echo absent; fi)"
    done
  done
  for response in delivery prompt-uncertain quote quote-prompt-uncertain quote-delivery-last-line delivery-zero-exit timeout noid result-error; do
    run_case "ask-$response" "${rows_one/answer/$response}"$'\n'"$third"
    case "$response" in
      delivery) check_run "1|EXIT=1|first|$id1|$id1||NYX_DELIVERY";;
      prompt-uncertain)
        check_run "1|EXIT=1|first|$id1|$id1||NYX_UNCERTAIN"
        chke yes uncertain-recovery-references "$(if grep -qF "Conversation: https://chatgpt.com/c/$id1" "$run_out" &&
          grep -qF "NYX_UNCERTAIN task=$id1 pool=first" "$run_dir/stdout" &&
          grep -qF "nyxid oracle result $id1" "$run_dir/stdout" &&
          grep -qF "nyx.sh fetch $id1" "$run_dir/stdout"; then echo yes; fi)";;
      quote|quote-prompt-uncertain|quote-delivery-last-line|delivery-zero-exit) check_run "0|EXIT=0|first|$id1|$id1||NYX_OK";;
      timeout) check_run "3|EXIT=3|first|$id1|$id1,$id1||NYX_TIMEOUT";;
      noid) check_run '1|EXIT=1|first||||NYX_UNKNOWN';;
      result-error) check_run "1|EXIT=1|first|$id1|$id1||NYX_UNKNOWN";;
    esac
    case "$response" in
      quote-prompt-uncertain) chke '{"verdict":"approve","note":"Error: Task failed (prompt_delivery_uncertain)."}' "$run_name-content" "$(sed -n '/^{/p' "$run_out")";;
      quote-delivery-last-line) chke '{"verdict":"approve","note":"Message delivery timed out. Please try again.Retry"}' "$run_name-content" "$(sed -n '/^{/p' "$run_out")";;
    esac
  done
  local setting
  for setting in NYX_LIMIT=invalid NYX_LIMIT=0 NYX_LIMIT=999999999999999999999 NYX_POLL_ROUNDS=-1 NYX_POLL_SECONDS=oops; do
    run_case "ask-invalid-$setting" "$rows_one" "$setting"
    check_run '2|EXIT=2|||||NYX_ERR'
    chke '' "no-cli-$setting" "$(joined "$run_dir/calls")"
  done
  run_case ask-output-init-error "$rows_one"
  check_run '2||||||NYX_IO'
  chke '' no-cli-output-init-error "$(joined "$run_dir/calls")"
  run_case ask-sidecar-init-error "$rows_one"
  check_run '2|EXIT=2|||||NYX_IO'
  chke '' no-cli-sidecar-init-error "$(joined "$run_dir/calls")"
  run_case ask-taskid-write-error "${rows_one/answer/id-write-error}"
  check_run '2|EXIT=2|first||||NYX_IO'
  chke absent lock-released-on-write-error "$(if [ -d "$run_dir/nyx-ask-first.lock" ]; then echo leaked; else echo absent; fi)"
  run_case ask-output-write-error "$rows_one" NYX_TEST_WRITE_ERROR=submit
  check_run '2|EXIT=2|first||||NYX_IO'
  chke absent lock-released-on-output-error "$(if [ -d "$run_dir/nyx-ask-first.lock" ]; then echo leaked; else echo absent; fi)"
  run_case ask-unknown-capacity "${rows_one/|0|1|/|0|?|}"
  check_run '4|EXIT=4|||||NYX_NOPOOL'
  run_case ask-zero-capacity "${rows_one/|0|1|/|0|0|}"
  check_run '4|EXIT=4|||||NYX_NOPOOL'
  run_case ask-unknown-inflight "${rows_one/|0|1|/|0|?|}" NYX_POOL=first NYX_LIMIT=100
  check_run '4|EXIT=4|||||NYX_PRECHECK'
  for response in ask-missing-brief fetch-invalid-id; do
    run_case "$response" "$rows_one"
    check_run '2|EXIT=2|||||NYX_ERR'
    chke '' "no-cli-$response" "$(joined "$run_dir/calls")"
  done
  # A transport error on `oracle result` after a successful submission is not a task verdict:
  # one transient failure then an answer is OK; a persistent one exhausts the rounds as TIMEOUT.
  run_case ask-transient-then-answer "${rows_one/answer/transient}"
  check_run "0|EXIT=0|first|$id1|$id1,$id1||NYX_OK"
  run_case fetch-transient-forever "${rows_one/answer/transient-forever}"
  check_run "3|EXIT=3||$id1|$id1,$id1||NYX_TIMEOUT"
  run_case fetch-delivery "${rows_one/answer/delivery}"
  check_run "1|EXIT=1||$id1|$id1||NYX_DELIVERY"
  run_case fetch-prompt-uncertain "${rows_one/answer/prompt-uncertain}"
  check_run "1|EXIT=1||$id1|$id1||NYX_UNCERTAIN"
  # A fresh ask after terminal failure retains audit bytes and both IDs, but submits again.
  run_case ask-rerun-history "${rows_one/answer/extraction}" NYX_POOL=first
  cp "$run_out" "$run_dir/prior"
  run_env+=("NYX_TEST_ROWS=first|v|1|0|1|0|answer|$id2")
  run_child > "$run_dir/stdout" 2>&1; run_rc=$?
  check_run "0|EXIT=0|first,first|$id1,$id2|$id1,$id2||NYX_OK"
  run_args=(taskid "$run_out")
  chke "$id2" taskid-current "$(run_child)"
  chke yes ask-history-bytes "$(if tail -n +2 "$run_out.history" 2>/dev/null | cmp -s - "$run_dir/prior"; then echo yes; fi)"
  chke 1 ask-current-sentinel-count "$(grep -c '^EXIT=' "$run_out")"
  chke 1 ask-history-boundary "$(grep -Ec '^NYX_RUN_BOUNDARY [0-9T:Z-]+ ask$' "$run_out.history" 2>/dev/null)"
  cp "$run_out.history" "$run_dir/first-history"
  run_args=(ask "$run_dir/brief" "$run_out"); run_child > "$run_dir/stdout" 2>&1
  chke 2 ask-history-appends "$(grep -c '^NYX_RUN_BOUNDARY ' "$run_out.history")"
  chke yes ask-history-prefix-preserved "$(if head -n "$(wc -l < "$run_dir/first-history")" "$run_out.history" | cmp -s - "$run_dir/first-history"; then echo yes; fi)"
  run_args=(taskid "$run_dir/missing"); run_child > "$run_dir/taskid-missing" 2>&1; got=$?
  chke '1|' taskid-missing "$got|$(cat "$run_dir/taskid-missing")"
  # FIFO handshakes hold an actual fetch at result; the timeout only guards broken infrastructure.
  run_case fetch-timeout "${rows_one/answer/timeout}"
  cp "$run_out" "$run_dir/prior"
  mkfifo "$run_dir/ready" "$run_dir/release"
  exec 8<> "$run_dir/ready" 9<> "$run_dir/release"
  run_env+=("NYX_TEST_ROWS=${rows_one/answer/barrier}")
  run_child > "$run_dir/stdout" 2>&1 &
  local fetch_pid=$! ready='' running make_rc fetch_rc
  IFS= read -r -t 30 -u 8 ready || { echo 'infrastructure-hang-guard expired: fetch barrier'; fail=1; }
  run_args=(status "$run_out")
  running=$(run_child 2>/dev/null | awk '/(RUNNING|OK|UNKNOWN).*result$/ {print $(NF-2)}')
  run_script="$await_script"; run_args=(make "$run_out"); run_env+=('AWAIT_DEADLINE=0')
  run_child > "$run_dir/make-running" 2>&1; make_rc=$?
  printf 'release\n' >&9
  wait "$fetch_pid"; fetch_rc=$?
  exec 8>&- 9>&-
  run_script="$0"; run_args=(status "$run_out")
  got=$(run_child 2>/dev/null | awk '/(RUNNING|OK|UNKNOWN).*result$/ {print $(NF-2)}')
  chke 'ready|RUNNING|124|0|OK|EXIT=0' run-boundary-fetch-running "$ready|$running|$make_rc|$fetch_rc|$got|$(tail -1 "$run_out")"
  chke yes fetch-history-bytes "$(if tail -n +2 "$run_out.history" 2>/dev/null | cmp -s - "$run_dir/prior"; then echo yes; fi)"
  chke 1 fetch-current-sentinel-count "$(grep -c '^EXIT=' "$run_out")"
  run_case await-vote-fallback "$traversal"
  chke "0|$id1,$id2|yes|yes" await-vote-fallback "$run_rc|$(joined "$run_dir/polls")|$(if [ -f "$run_out.settled" ]; then echo yes; fi)|$(if grep -q "task=$id2 state=settled" "$run_dir/stdout"; then echo yes; fi)"
  run_case await-vote-exhausted "${traversal/answer/extraction}" NYX_TEST_UNIQUE_IDS=1
  chke "125|first,second,first,second|${id1%-*}-000000000001,${id2%-*}-000000000002,${id1%-*}-000000000003,${id2%-*}-000000000004|no|yes" await-vote-exhausted \
    "$run_rc|$(joined "$run_dir/submits")|$(joined "$run_dir/polls")|$(if [ -f "$run_out.settled" ]; then echo yes; else echo no; fi)|$(if grep -q 'state=exhausted attempts=2' "$run_dir/stdout"; then echo yes; fi)"
  run_case await-vote-timeout "${rows_one/answer/resume}"
  chke "0|first|$id1,$id1,$id1|yes" await-vote-timeout "$run_rc|$(joined "$run_dir/submits")|$(joined "$run_dir/polls")|$(if grep -q "task=$id1 state=settled" "$run_dir/stdout"; then echo yes; fi)"
  for response in quota busy delivery unknown; do
    rows="${rows_one/answer/$response}"; expected="125|first,first|"
    case "$response" in
      busy) rows="${rows_one/|0|1|/|1|1|}"; expected='125||';;
      delivery) expected="1|first|$id1";;
      unknown) expected='7|first|';;
    esac
    run_case "await-vote-$response" "$rows"
    chke "$expected|no" "await-vote-$response" "$run_rc|$(joined "$run_dir/submits")|$(joined "$run_dir/polls")|$(if [ -f "$run_out.settled" ]; then echo yes; else echo no; fi)"
  done
  run_case await-vote-prompt-uncertain "${rows_one/answer/prompt-uncertain}"$'\n'"$third"
  chke "6|first|$id3,$id1|$id1|no|yes|no" await-vote-prompt-uncertain \
    "$run_rc|$(joined "$run_dir/submits")|$(joined "$run_out.taskid")|$(joined "$run_dir/polls")|$(if [ -f "$run_out.settled" ]; then echo yes; else echo no; fi)|$(if grep -q "task=$id1 state=stopped verdict=NYX_UNCERTAIN" "$run_dir/stdout"; then echo yes; else echo no; fi)|$(if grep -q 'state=retry' "$run_dir/stdout" || grep -q '^NYX_NEXT_POOL ' "$run_out.log"; then echo yes; else echo no; fi)"
  run_case await-vote-quote-prompt-uncertain "${rows_one/answer/quote-prompt-uncertain}"$'\n'"$third"
  chke "0|first|$id1|yes" await-vote-quote-prompt-uncertain \
    "$run_rc|$(joined "$run_dir/submits")|$(joined "$run_dir/polls")|$(if cmp -s "$run_out" "$run_out.settled" && grep -qF '{"verdict":"approve","note":"Error: Task failed (prompt_delivery_uncertain)."}' "$run_out.settled"; then echo yes; else echo no; fi)"
  # Fresh observations, invocation-local failures and recovery guidance are CLI behaviors.
  check_guidance() {  # expected outcome | current task ID (empty means none) | action phrase
    chke yes "$run_name-guidance" "$(if grep '^NYX_UNSTABLE ' "$run_dir/stdout" |
      grep -F "outcome=$1 task=${2:-<none>} " | grep -F 'Oracle service is unstable' |
      grep -F '本次结果不代表永久不可用' | grep -F 'a future invocation re-evaluates services' |
      grep -qF "$3"; then echo yes; fi)"
  }
  check_admission() {
    chke '' "$run_name-no-admission-sleeps" "$(joined "$run_dir/sleeps")"
    chke 'first|locked,second|locked' "$run_name-refresh-under-lock" "$(joined "$run_dir/refreshes")"
    chke 'released|1' "$run_name-release-and-sentinel" "$(if [ ! -d "$run_dir/nyx-ask-first.lock" ] &&
      [ ! -d "$run_dir/nyx-ask-second.lock" ]; then echo released; fi)|$(grep -c '^EXIT=' "$run_out")"
  }
  local outcome tid
  for response in late-read late-parse late-offline late-full late-zero late-filter late-script late-shrink late-expiry; do
    outcome=PRECHECK
    case "$response" in late-full|late-shrink) outcome=BUSY;; late-expiry) outcome=EXPIRED;; esac
    run_case "ask-admission-$response" "${traversal/extraction/$response}"
    check_run "0|EXIT=0|second|$id2|$id2|first|NYX_OK"
    check_admission
    check_guidance "$outcome" '' 'a fresh ask may be tried later'
  done
  run_case ask-first-locked "$traversal"
  check_run "0|EXIT=0|second|$id2|$id2|first|NYX_OK"
  chke '' locked-candidate-no-sleeps "$(joined "$run_dir/sleeps")"
  chke 'first,second' locked-candidate-one-attempt "$(sed "s|$run_dir/nyx-ask-||; s/\.lock$//" "$run_dir/lock-attempts" | awk 'NF {printf "%s%s", sep, $0; sep=","}')"
  chke 'foreign|released|1' locked-candidate-ownership "$(if [ -d "$run_dir/nyx-ask-first.lock" ]; then echo foreign; fi)|$(if [ ! -d "$run_dir/nyx-ask-second.lock" ]; then echo released; fi)|$(grep -c '^EXIT=' "$run_out")"
  check_guidance LOCKBUSY '' 'a fresh ask may be tried later'
  run_case ask-release-io "${traversal/extraction/late-offline}" NYX_TEST_RELEASE_ERROR=1
  check_run '2|EXIT=2|||||NYX_IO'
  chke no release-io-stops "$(if grep -q '^NYX_NEXT_POOL ' "$run_dir/stdout"; then echo yes; else echo no; fi)"
  run_case ask-full-ranks-after-usable "${traversal/first|v|2|0/first|v|2|2}"
  check_run "0|EXIT=0|second|$id2|$id2||NYX_OK"
  run_case ask-limit-ranking "second|v|2|0|2|0|answer|$id2"$'\n'"first|v|3|1|3|0|answer|$id1" NYX_LIMIT=1
  check_run "0|EXIT=0|second|$id2|$id2||NYX_OK"
  run_case ask-limit-admission "first|v|2|1|2|0|answer|$id1" NYX_LIMIT=1
  check_run '3|EXIT=3|||||NYX_BUSY'
  chke '' limit-admission-no-sleeps "$(joined "$run_dir/sleeps")"
  run_case ask-limit-cannot-exceed-capacity "first|v|1|1|1|0|answer|$id1" NYX_LIMIT=9
  check_run '3|EXIT=3|||||NYX_BUSY'
  run_case ask-explicit-waits-for-capacity "${rows_one/answer/full-then-free}" NYX_POOL=first
  check_run "0|EXIT=0|first|$id1|$id1||NYX_OK"
  chke 20 explicit-capacity-sleep "$(joined "$run_dir/sleeps")"
  run_case ask-explicit-bounded-lock "second|v|1|0|1|0|answer|$id2" NYX_POOL=second
  # Reuse the same invocation with a foreign lock to measure only the explicit wait.
  mkdir "$run_dir/nyx-ask-second.lock"
  : > "$run_dir/submits"; : > "$run_dir/polls"
  run_child > "$run_dir/stdout" 2>&1; run_rc=$?
  check_run "3|EXIT=3||$id2|||NYX_LOCKBUSY"
  chke '120|5' explicit-lock-bounded-sleeps "$(wc -l < "$run_dir/sleeps" | tr -d ' ')|$(sort -u "$run_dir/sleeps")"
  run_case ask-explicit-bounded-full "first|v|1|1|1|0|answer|$id1" NYX_POOL=first
  check_run '3|EXIT=3|||||NYX_BUSY'
  chke '30|20' explicit-full-bounded-sleeps "$(wc -l < "$run_dir/sleeps" | tr -d ' ')|$(sort -u "$run_dir/sleeps")"
  run_case ask-custom-tag "$rows_one" NYX_TAG=mode:work NYX_TEST_EXPECT_TAG=mode:work
  check_run "0|EXIT=0|first|$id1|$id1||NYX_OK"
  run_case ask-custom-poll "${rows_one/answer/timeout}" NYX_POLL_ROUNDS=3 NYX_POLL_SECONDS=7
  check_run "3|EXIT=3|first|$id1|$id1,$id1,$id1||NYX_TIMEOUT"
  chke '7,7,7' explicit-poll-controls "$(joined "$run_dir/sleeps")"
  for response in empty unset; do
    run_case "ask-default-$response-filter" "first|cdp-1.3-old|1|0|1|0|answer|$id1" NYX_BAD_SCRIPTS=
    check_run "0|EXIT=0|first|$id1|$id1||NYX_OK"
  done
  run_case ask-auto-recovery "first|cdp-1.3-old|1|0|1|0|extraction|$id1" NYX_BAD_SCRIPTS=
  check_run "1|EXIT=1|first|$id1|$id1||NYX_EXTRACTION"
  check_guidance EXTRACTION "$id1" 'a fresh ask may be tried later'
  cp "$run_out" "$run_dir/prior"
  run_env+=("NYX_TEST_ROWS=first|cdp-1.3-old|1|0|1|0|answer|$id2")
  run_child > "$run_dir/stdout" 2>&1; run_rc=$?
  run_name=ask-auto-recovered
  check_run "0|EXIT=0|first,first|$id1,$id2|$id1,$id2||NYX_OK"
  chke '2|yes|1' recovery-rediscovers-and-preserves-history "$(grep -c '^oracle pool list$' "$run_dir/calls")|$(if tail -n +2 "$run_out.history" | cmp -s - "$run_dir/prior"; then echo yes; fi)|$(grep -c '^EXIT=' "$run_out")"
  run_case ask-discovery-unavailable "$rows_one" NYX_TEST_LIST_ERROR=1
  check_run '4|EXIT=4|||||NYX_NOPOOL'
  check_guidance NOPOOL '' 'a fresh ask may be tried later'
  run_env+=('NYX_TEST_LIST_ERROR=')
  run_child > "$run_dir/stdout" 2>&1; run_rc=$?
  run_name=ask-discovery-recovered
  check_run "0|EXIT=0|first|$id1|$id1||NYX_OK"
  run_case ask-all-terminal-fail "${traversal/answer/extraction}"
  check_run "1|EXIT=1|first,second|$id1,$id2|$id1,$id2|first|NYX_EXTRACTION"
  chke yes all-candidates-explicit-non-success "$(if grep -q '^NYX_UNSTABLE pool=<candidates> outcome=ALL_UNAVAILABLE checked=2 no candidate yielded an answer in this invocation; untried pools are not declared failed' "$run_dir/stdout"; then echo yes; fi)"
  run_case ask-fallback-bytes "$traversal"
  printf 'Task submitted: %s\nError: Task failed (extraction_failure).\nTask submitted: %s\n{"ok":true}\nEXIT=0\n' "$id1" "$id2" > "$run_dir/expected-output"
  chke yes fallback-raw-bytes "$(if cmp -s "$run_out" "$run_dir/expected-output"; then echo yes; fi)"
  chke no fallback-no-exhaustion-guidance "$(if grep -q 'outcome=ALL_UNAVAILABLE' "$run_dir/stdout"; then echo yes; else echo no; fi)"
  for response in noid unknown submit-uncertain submit-delivery; do
    run_case "ask-$response-stale" "${rows_one/answer/$response}"$'\n'"$third"
    outcome=UNKNOWN; expected=1
    case "$response" in unknown) expected=7;; submit-uncertain) outcome=UNCERTAIN;; submit-delivery) outcome=DELIVERY;; esac
    check_run "$expected|EXIT=$expected|first|$id3|||NYX_$outcome"
    check_guidance "$outcome" '' 'Reconcile uncertain submission'
    chke no "$run_name-no-stale-recovery" "$(if grep '^NYX_UNSTABLE ' "$run_dir/stdout" | grep -qF "$id3"; then echo yes; else echo no; fi)"
  done
  for response in timeout result-error result-rate-limit result-observation-infra result-zero-exit-failure prompt-uncertain delivery; do
    run_case "ask-recovery-$response" "${rows_one/answer/$response}"$'\n'"$third"
    outcome=UNKNOWN
    case "$response" in timeout) outcome=TIMEOUT;; prompt-uncertain) outcome=UNCERTAIN;; delivery) outcome=DELIVERY;; esac
    check_guidance "$outcome" "$id1" "Resume the same task: nyx.sh fetch $id1"
    chke 'first|no|1' "$run_name-do-not-replay" "$(joined "$run_dir/submits")|$(if grep -q 'outcome=ALL_UNAVAILABLE\|a fresh ask may be tried later' "$run_dir/stdout"; then echo yes; else echo no; fi)|$(grep -c '^EXIT=' "$run_out")"
    cp "$run_out" "$run_dir/prior"
    run_args=(fetch "$id1" "$run_out"); run_env+=("NYX_TEST_ROWS=$rows_one")
    run_child > "$run_dir/stdout" 2>&1; run_rc=$?
    chke '0|first|yes|1' "$run_name-fetch-preserves" "$run_rc|$(joined "$run_dir/submits")|$(if tail -n +2 "$run_out.history" | cmp -s - "$run_dir/prior"; then echo yes; fi)|$(grep -c '^EXIT=' "$run_out")"
  done
  for response in infra composer alternating-read late-read; do
    run_case "await-vote-safe-$response" "${rows_one/answer/$response}"
    outcome=INFRA; expected='125|first,first'
    case "$response" in
      composer) outcome=CARRIER;;
      alternating-read) outcome=PRECHECK; expected='125|';;
      late-read) outcome=PRECHECK; expected='4|';;
    esac
    chke "$expected|no|60" "$run_name-bounded-retry" "$run_rc|$(joined "$run_dir/submits")|$(if [ -f "$run_out.settled" ]; then echo yes; else echo no; fi)|$(joined "$run_dir/sleeps")"
    chke yes "$run_name-verdict" "$(if grep -q "state=retry verdict=NYX_$outcome" "$run_dir/stdout"; then echo yes; fi)"
    if [ "$outcome" = PRECHECK ]; then check_guidance PRECHECK '' 'a fresh ask may be tried later'
    else check_guidance "$outcome" "$id1" 'a fresh ask may be tried later'; fi
  done
  for response in noid result-error result-rate-limit timeout prompt-uncertain delivery submit-uncertain submit-delivery; do
    run_case "await-vote-guidance-$response" "${rows_one/answer/$response}"$'\n'"$third" AWAIT_DEADLINE=0
    outcome=UNKNOWN; expected=1; tid="$id1"
    case "$response" in
      noid) tid='';;
      timeout) outcome=TIMEOUT; expected=124;;
      prompt-uncertain) outcome=UNCERTAIN; expected=6;;
      delivery) outcome=DELIVERY;;
      submit-uncertain) outcome=UNCERTAIN; expected=6; tid='';;
      submit-delivery) outcome=DELIVERY; tid='';;
    esac
    if [ -n "$tid" ]; then check_guidance "$outcome" "$tid" "nyx.sh fetch $tid"
    else check_guidance "$outcome" '' 'Reconcile uncertain submission'; fi
    chke "$expected|first|no" "$run_name-no-replay" "$run_rc|$(joined "$run_dir/submits")|$(if [ -f "$run_out.settled" ]; then echo yes; else echo no; fi)"
    case "$response" in submit-uncertain|submit-delivery)
      chke yes "$run_name-no-old-task" "$(if grep -q 'task=<none> state=stopped' "$run_dir/stdout" && ! grep '^NYX_UNSTABLE ' "$run_dir/stdout" | grep -qF "$id3"; then echo yes; fi)";;
    esac
  done
  run_case await-vote-guidance-fallback "$traversal"
  check_guidance EXTRACTION "$id1" 'a fresh ask may be tried later'
  chke "0|first,second|yes" await-guidance-fallback-settles "$run_rc|$(joined "$run_dir/submits")|$(if cmp -s "$run_out" "$run_out.settled"; then echo yes; fi)"
  rm -rf "$testroot"
  [ $fail -eq 0 ] && echo "SELFTEST_OK cases=$cases" || echo "SELFTEST_FAIL cases=$cases"
  return $fail
}

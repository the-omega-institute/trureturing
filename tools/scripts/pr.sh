#!/usr/bin/env bash
set -euo pipefail
PR_REPO="${PR_OPEN_REPO:-the-omega-institute/trureturing}"
PR_BASE="${PR_OPEN_BASE:-dev}"
PR_OPEN_TIMEOUT_SECONDS="${PR_OPEN_TIMEOUT_SECONDS:-60}"
PR_WATCH_INTERVAL_SECONDS="${PR_WATCH_INTERVAL_SECONDS:-10}"
PR_WATCH_TIMEOUT_SECONDS="${PR_WATCH_TIMEOUT_SECONDS:-4200}"
PR_WATCH_MAX_FAILURES=3
BOUNDED_OUTPUT=""
receipt() { printf '%s\n' "$*" >&2; }
watch_result() { printf 'PR_WATCH_RESULT pr=%s %s head_sha=%s\n' "$1" "$3" "$2"; }
positive_integer() { [[ "$1" =~ ^[1-9][0-9]*$ ]]; }
commit_sha() { [[ "$1" =~ ^[0-9a-f]{40}$ ]]; }
usage_open() { receipt "usage: pr.sh open --head HEAD --message-file FILE [--auto-merge] [--timeout-seconds S] [--interval-seconds S]"; }
usage_watch() { receipt "usage: pr.sh watch --pr NUMBER --head-sha SHA [--timeout-seconds S] [--interval-seconds S]"; }
PR_SNAPSHOT_QUERY='query($owner:String!,$repo:String!,$pr:Int!,$head:GitObjectID!) {
  repository(owner:$owner,name:$repo) {
    nameWithOwner pullRequest(number:$pr) { number state headRefOid }
    object(oid:$head) { ... on Commit { oid statusCheckRollup { contexts(first:100) {
      nodes { __typename
        ... on CheckRun { databaseId name status conclusion
          checkSuite { databaseId commit { oid } workflowRun { databaseId runNumber runAttempt workflow { id } }
            checkRuns(first:100,filterBy:{checkType:LATEST}) {
              nodes { databaseId } pageInfo { hasNextPage }
            } } }
        ... on StatusContext { id context state commit { oid } }
      }
      pageInfo { hasNextPage }
    } } } }
  }
}'
run_bounded_capture() {
  local step="$1" timeout_seconds="$2"; shift 2
  local started deadline errors pid watcher rc=0 result=success
  started="$(date +%s)"; deadline=$((started + timeout_seconds))
  errors="$(mktemp "${TMPDIR:-/tmp}/pr-command-err.XXXXXX")"
  receipt "COMMAND_STARTED deadline_kind=api step=$step timeout_seconds=$timeout_seconds deadline_at=$deadline"
  # Capture stdout in memory: the same bounded call also obtains credentials.
  if BOUNDED_OUTPUT="$(
    # Isolate the command process group so a broker child cannot hold the
    # capture pipe open after its parent exits or the deadline expires.
    set -m
    "$@" 2>"$errors" & pid=$!
    (
      sleep "$timeout_seconds"
      kill -TERM -- "-$pid" 2>/dev/null || exit 0
      sleep 1
      kill -KILL -- "-$pid" 2>/dev/null || true
    ) >/dev/null 2>&1 & watcher=$!
    if wait "$pid"; then rc=0; else rc=$?; fi
    kill -KILL -- "-$pid" 2>/dev/null || true
    kill -- "-$watcher" 2>/dev/null || true; wait "$watcher" 2>/dev/null || true
    exit "$rc"
  )"; then rc=0; else rc=$?; fi
  if [[ "$rc" -eq 143 || "$rc" -eq 137 ]]; then rc=124; result=timeout
  elif [[ "$rc" -ne 0 ]]; then result=exit
  fi
  if [[ "$rc" -ne 0 && -s "$errors" ]]; then head -c 4096 "$errors" >&2; fi
  rm -f "$errors"
  receipt "COMMAND_FINISHED deadline_kind=api step=$step timeout_seconds=$timeout_seconds result=$result deadline_at=$deadline exit_code=$rc"
  return "$rc"
}
gh_authenticated() {
  local mode="$1" step="$2" timeout_seconds="$3"; shift 3
  local deadline remaining fresh_token=""
  deadline=$(($(date +%s) + timeout_seconds))
  # Creation prefers the App identity. Local calls keep native gh auth when
  # GITHUB_TOKEN is absent; when supplied, refresh that credential per call.
  # An absent/failing/empty broker preserves the caller's existing fallback.
  if [[ "$mode" == create || -n "${GITHUB_TOKEN:-}" ]] \
      && command -v gh-app >/dev/null 2>&1 \
      && run_bounded_capture gh-app-token "$timeout_seconds" bash -c 'exec gh-app token --auto 2>/dev/null' \
      && [[ -n "$BOUNDED_OUTPUT" ]]; then
    fresh_token="$BOUNDED_OUTPUT"
  fi
  BOUNDED_OUTPUT=""
  # Creation already had separate token/API budgets; watch calls must share
  # their supplied remaining budget with credential acquisition.
  remaining="$timeout_seconds"
  if [[ "$mode" != create ]]; then remaining=$((deadline - $(date +%s))); fi
  (( remaining > 0 )) || return 124
  # Shell assignments keep credentials out of external argv and restore the
  # caller's environment after capture; creation still takes GH_TOKEN priority.
  if [[ -n "$fresh_token" && "$mode" == create ]]; then
    GH_TOKEN="$fresh_token" run_bounded_capture "$step" "$remaining" env LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
  elif [[ -n "$fresh_token" ]]; then
    GITHUB_TOKEN="$fresh_token" run_bounded_capture "$step" "$remaining" env -u GH_TOKEN LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
  else
    run_bounded_capture "$step" "$remaining" env -u GH_TOKEN LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
  fi
}
gh_local() {
  gh_authenticated local "$@"
}
gh_create() {
  gh_authenticated create pr-create "$PR_OPEN_TIMEOUT_SECONDS" "$@"
}
parse_snapshot() {
  local required="$1" head="$2" number="$3"
  jq -Rsec --argjson required "$required" --arg head "$head" --argjson number "$number" --arg repo "$PR_REPO" '
    def member($xs): . as $value | $xs | index($value) != null;
    def database_id: type == "number" and . > 0 and . <= 9007199254740991 and floor == .;
    def sha: type == "string" and test("^[0-9a-f]{40}$");
    fromjson | select(type == "object" and (.errors == null or .errors == [])) |
    .data.repository |
    select(type == "object" and .nameWithOwner == $repo and .pullRequest.number == $number) |
    .pullRequest as $pr |
    select(($pr.headRefOid | sha) and ($pr.state | member(["OPEN","CLOSED","MERGED"]))) |
    select((.object | type == "object") and .object.oid == $head) |
    select((.object | has("statusCheckRollup")) and
      (.object.statusCheckRollup == null or
        ((.object.statusCheckRollup.contexts.nodes | type == "array") and
         .object.statusCheckRollup.contexts.pageInfo.hasNextPage == false))) |
    (.object.statusCheckRollup.contexts.nodes // []) as $all |
    select($all | type == "array") |
    select(all($all[]; type == "object" and (if .__typename == "CheckRun" then
        (.databaseId | database_id) and (.name | type == "string" and length > 0) and
        (.status | member(["QUEUED","IN_PROGRESS","COMPLETED","WAITING","REQUESTED","PENDING"])) and
        (if .status == "COMPLETED" then (.conclusion | member(["FAILURE","CANCELLED","TIMED_OUT","SUCCESS","NEUTRAL","SKIPPED","ACTION_REQUIRED","STARTUP_FAILURE","STALE"])) else .conclusion == null end) and
        (.checkSuite.databaseId | database_id) and .checkSuite.commit.oid == $head and
        .checkSuite.checkRuns.pageInfo.hasNextPage == false and
        (.checkSuite.checkRuns.nodes | type == "array" and all(.[]; .databaseId | database_id))
      elif .__typename == "StatusContext" then
        (.id | type == "string" and length > 0) and (.context | type == "string" and length > 0) and
        (.state | member(["FAILURE","ERROR","PENDING","EXPECTED","SUCCESS"])) and .commit.oid == $head
      else false end))) |
    [$all[] | select(.__typename == "CheckRun")] as $actions |
    select(($actions | map(.databaseId) | length) == ($actions | map(.databaseId) | unique | length)) |
    select(all($actions | map(select(.checkSuite.workflowRun != null)) | group_by(.checkSuite.databaseId)[];
      (map(.checkSuite.checkRuns.nodes | map(.databaseId) | sort) | unique | length) == 1 and
      (. as $suite | ($suite[0].checkSuite.checkRuns.nodes | map(.databaseId)) as $latest |
        ($latest | length) == ($latest | unique | length) and
        all($latest[]; . as $id | any($suite[]; .databaseId == $id)) and
        ([$suite[] | select(.databaseId as $id | $latest | index($id) != null) | .name] |
          length == (unique | length))))) |
    [$all[] | select(. as $c | .__typename == "StatusContext"
        or any(.checkSuite.checkRuns.nodes[]; .databaseId == $c.databaseId))] as $items |
    def name: if .__typename == "CheckRun" then .name else .context end;
    def state: if .__typename == "CheckRun" then (.conclusion // .status) else .state end;
    def red: state as $s | ["FAILURE","CANCELLED","TIMED_OUT","ERROR","ACTION_REQUIRED","STARTUP_FAILURE","STALE"] | index($s) != null;
    def pending: state as $s | ["QUEUED","IN_PROGRESS","WAITING","REQUESTED","PENDING","EXPECTED"] | index($s) != null;
    def green: state as $s | ["SUCCESS","NEUTRAL","SKIPPED"] | index($s) != null;
    [$required[] as $name | [$items[] | select(name == $name)] as $found |
      if ($found | length) == 0 then {kind:"missing",check:$name}
      else $found[] | if red then {kind:"red",check:name,state:state}
        elif pending then {kind:"pending",check:name,state:state}
        elif green then {kind:"terminal",check:name,state:state}
        else error("invalid required-check state") end end] as $checks |
    {state:$pr.state, stale:($pr.headRefOid != $head), observed_head:$pr.headRefOid,
     red:($checks | map(select(.kind == "red")) | first // null),
     pending:($checks | map(select(.kind == "pending")) | length),
     missing:($checks | map(select(.kind == "missing")) | length),
     evidence:$checks}'
}

read_snapshot() {
  local required="$1" head_sha="$2" number="$3" snapshot="$BOUNDED_OUTPUT"
  printf '%s' "$snapshot" | parse_snapshot "$required" "$head_sha" "$number" 2>/dev/null
}

pr_watch_main() {
  local number="" head_sha="" timeout_seconds="$PR_WATCH_TIMEOUT_SECONDS" interval_seconds="$PR_WATCH_INTERVAL_SECONDS"
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --pr) [[ $# -ge 2 ]] || { usage_watch; return 2; }; number="$2"; shift 2 ;;
      --head-sha) [[ $# -ge 2 ]] || { usage_watch; return 2; }; head_sha="$2"; shift 2 ;;
      --timeout-seconds) [[ $# -ge 2 ]] || { usage_watch; return 2; }; timeout_seconds="$2"; shift 2 ;;
      --interval-seconds) [[ $# -ge 2 ]] || { usage_watch; return 2; }; interval_seconds="$2"; shift 2 ;;
      *) usage_watch; return 2 ;;
    esac
  done
  positive_integer "$number" && commit_sha "$head_sha" && positive_integer "$timeout_seconds" && positive_integer "$interval_seconds" \
    || { usage_watch; return 2; }
  local started deadline now remaining call_timeout failures=0 seen_snapshot=0 required="" parsed="" state="" red_check="" red_state="" pending=0 missing=0
  started="$(date +%s)"; deadline=$((started + timeout_seconds))
  while [[ -z "$required" ]]; do
    now="$(date +%s)"; remaining=$((deadline - now))
    if (( remaining <= 0 )); then watch_result "$number" "$head_sha" "outcome=query-unavailable step=required-set attempts=$failures"; return 69; fi
    call_timeout=$((remaining < PR_OPEN_TIMEOUT_SECONDS ? remaining : PR_OPEN_TIMEOUT_SECONDS))
    if gh_local required-set "$call_timeout" api "repos/$PR_REPO/branches/$PR_BASE" \
        && [[ -n "$BOUNDED_OUTPUT" ]] \
        && required="$(printf '%s' "$BOUNDED_OUTPUT" | jq -Rsec '
          fromjson |
          select(type == "object" and .protected == true and (.protection | type == "object")) |
          .protection.required_status_checks |
          select(type == "object" and (.contexts | type == "array") and (.checks | type == "array") and
            all(.contexts[]; type == "string" and length > 0) and
            all(.checks[]; type == "object" and (.context | type == "string" and length > 0))) |
          (.contexts + [.checks[].context]) | unique
        ' 2>/dev/null)" \
        && [[ -n "$required" ]]; then
      failures=0; break
    fi
    required=""; failures=$((failures + 1))
    receipt "PR_WATCH_PROGRESS pr=$number step=required-set unavailable_attempts=$failures"
    if (( failures >= PR_WATCH_MAX_FAILURES )); then
      watch_result "$number" "$head_sha" "outcome=query-unavailable step=required-set attempts=$failures"
      return 69
    fi
    now="$(date +%s)"; remaining=$((deadline - now))
    (( remaining > 0 )) || { watch_result "$number" "$head_sha" "outcome=query-unavailable step=required-set attempts=$failures"; return 69; }
    sleep "$((interval_seconds < remaining ? interval_seconds : remaining))"
  done
  missing="$(jq -r 'length' <<<"$required")"
  while :; do
    now="$(date +%s)"; remaining=$((deadline - now))
    if (( remaining <= 0 )); then
      if (( failures > 0 || seen_snapshot == 0 )); then
        watch_result "$number" "$head_sha" "outcome=query-unavailable step=snapshot attempts=$failures"; return 69
      fi
      watch_result "$number" "$head_sha" "outcome=timeout pending=$pending missing=$missing"; return 124
    fi
    call_timeout=$((remaining < PR_OPEN_TIMEOUT_SECONDS ? remaining : PR_OPEN_TIMEOUT_SECONDS))
    if gh_local snapshot "$call_timeout" api graphql -f query="$PR_SNAPSHOT_QUERY" \
        -f owner="${PR_REPO%%/*}" -f repo="${PR_REPO#*/}" -F pr="$number" -f head="$head_sha" \
        && [[ -n "$BOUNDED_OUTPUT" ]] \
        && parsed="$(read_snapshot "$required" "$head_sha" "$number")" \
        && [[ -n "$parsed" ]]; then
      failures=0; seen_snapshot=1
      if [[ "$(jq -r '.stale' <<<"$parsed")" == true ]]; then
        receipt "PR_WATCH_PROGRESS pr=$number state=stale expected_head=$head_sha observed_head=$(jq -r '.observed_head' <<<"$parsed")"
      else
        state="$(jq -r '.state' <<<"$parsed")"; red_check="$(jq -r '.red.check // empty' <<<"$parsed")"
        red_state="$(jq -r '.red.state // empty' <<<"$parsed")"; pending="$(jq -r '.pending' <<<"$parsed")"; missing="$(jq -r '.missing' <<<"$parsed")"
        now="$(date +%s)"
        receipt "PR_WATCH_EVIDENCE pr=$number head_sha=$head_sha checks=$(jq -c '.evidence' <<<"$parsed")"
        if (( now >= deadline )); then watch_result "$number" "$head_sha" "outcome=timeout pending=$pending missing=$missing"; return 124; fi
        if [[ -n "$red_check" ]]; then watch_result "$number" "$head_sha" "outcome=red check=$red_check state=$red_state"; return 1; fi
        if [[ "$state" == CLOSED ]]; then watch_result "$number" "$head_sha" "outcome=closed"; return 4; fi
        if (( pending == 0 && missing == 0 )); then watch_result "$number" "$head_sha" "outcome=green"; return 0; fi
        receipt "PR_WATCH_PROGRESS pr=$number state=$state pending=$pending missing=$missing"
      fi
    else
      parsed=""; failures=$((failures + 1))
      receipt "PR_WATCH_PROGRESS pr=$number step=snapshot unavailable_attempts=$failures"
      if (( failures >= PR_WATCH_MAX_FAILURES )); then watch_result "$number" "$head_sha" "outcome=query-unavailable step=snapshot attempts=$failures"; return 69; fi
    fi
    now="$(date +%s)"; remaining=$((deadline - now))
    if (( remaining <= 0 && (failures > 0 || seen_snapshot == 0) )); then watch_result "$number" "$head_sha" "outcome=query-unavailable step=snapshot attempts=$failures"; return 69; fi
    (( remaining > 0 )) || { watch_result "$number" "$head_sha" "outcome=timeout pending=$pending missing=$missing"; return 124; }
    sleep "$((interval_seconds < remaining ? interval_seconds : remaining))"
  done
}
pr_open_main() {
  local head="" head_sha="" head_owner="" head_ref="" message_file="" title="" body_file="" url number rc=0 auto_merge=0
  local timeout_seconds="$PR_WATCH_TIMEOUT_SECONDS" interval_seconds="$PR_WATCH_INTERVAL_SECONDS"
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --head) [[ $# -ge 2 ]] || { usage_open; return 2; }; head="$2"; shift 2 ;;
      --message-file) [[ $# -ge 2 ]] || { usage_open; return 2; }; message_file="$2"; shift 2 ;;
      --auto-merge) auto_merge=1; shift ;;
      --timeout-seconds) [[ $# -ge 2 ]] || { usage_open; return 2; }; timeout_seconds="$2"; shift 2 ;;
      --interval-seconds) [[ $# -ge 2 ]] || { usage_open; return 2; }; interval_seconds="$2"; shift 2 ;;
      *) usage_open; return 2 ;;
    esac
  done
  [[ -n "$head" && -n "$message_file" ]] && positive_integer "$timeout_seconds" && positive_integer "$interval_seconds" \
    || { usage_open; return 2; }
  if [[ ! -r "$message_file" ]]; then receipt "pr.sh open: message file is not readable: $message_file"; return 2; fi
  # The message file carries every caller-authored byte, so no title or body ever
  # crosses a make or shell layer that could expand or drop it.
  title="$(head -n 1 "$message_file")"
  if [[ -z "$title" ]]; then receipt "pr.sh open: message file has an empty title line: $message_file"; return 2; fi
  # Resolve the explicit remote branch before creation; the caller working tree
  # and the first potentially stale PR snapshot are not the requested identity.
  head_owner="${PR_REPO%%/*}"; head_ref="$head"
  if [[ "$head" == *:* ]]; then head_owner="${head%%:*}"; head_ref="${head#*:}"; fi
  [[ -n "$head_owner" && -n "$head_ref" ]] || { usage_open; return 2; }
  if ! gh_local head-resolve "$PR_OPEN_TIMEOUT_SECONDS" api graphql \
      -f query='query($owner:String!,$repo:String!,$ref:String!){repository(owner:$owner,name:$repo){ref(qualifiedName:$ref){target{... on Commit{oid}}}}}' \
      -f owner="$head_owner" -f repo="${PR_REPO#*/}" -f ref="refs/heads/$head_ref" \
      || ! head_sha="$(printf '%s' "$BOUNDED_OUTPUT" | jq -Rser '
        fromjson | select(type == "object" and (.errors == null or .errors == [])) |
        .data.repository.ref.target.oid | select(type == "string" and test("^[0-9a-f]{40}$"))
      ' 2>/dev/null)" || ! commit_sha "$head_sha"; then
    receipt "pr.sh open: explicit remote head could not be resolved: $head"; return 69
  fi
  body_file="$(mktemp "${TMPDIR:-/tmp}/pr-body.XXXXXX")"
  tail -n +2 "$message_file" | sed '1{/^$/d;}' > "$body_file"
  local args=(pr create --repo "$PR_REPO" --base "$PR_BASE" --head "$head" --title "$title" --body-file "$body_file")
  gh_create "${args[@]}" || rc=$?
  rm -f "$body_file"
  (( rc == 0 )) || return "$rc"
  url="$(printf '%s\n' "$BOUNDED_OUTPUT" | tail -n 1)"; number="${url##*/}"
  if ! positive_integer "$number"; then receipt "pr.sh open: create returned no pull request number"; return 1; fi
  if (( auto_merge == 1 )); then
    gh_local auto-merge "$PR_OPEN_TIMEOUT_SECONDS" pr merge "$number" --repo "$PR_REPO" --auto --merge --match-head-commit "$head_sha" || return $?
  fi
  printf '%s\n' "$number"
  pr_watch_main --pr "$number" --head-sha "$head_sha" --timeout-seconds "$timeout_seconds" --interval-seconds "$interval_seconds" || return $?
}
case "${1:-}" in
  open) shift; pr_open_main "$@" ;;
  watch) shift; pr_watch_main "$@" ;;
  *) receipt "usage: pr.sh <open|watch>"; exit 2 ;;
esac

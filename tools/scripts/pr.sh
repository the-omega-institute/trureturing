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
    pullRequest(number:$pr) { state headRefOid }
    object(oid:$head) { ... on Commit { oid statusCheckRollup { contexts(first:100) {
      nodes { __typename
        ... on CheckRun { databaseId name status conclusion
          checkSuite { app { id } branch { id } commit { oid }
            workflowRun { databaseId event runNumber runAttempt workflow { id } } } }
        ... on StatusContext { id context state commit { oid } }
      }
      pageInfo { hasNextPage }
    } } } }
  }
}'
run_bounded_capture() {
  local step="$1" timeout_seconds="$2"; shift 2
  local started deadline output errors pid watcher rc=0 result=success
  started="$(date +%s)"; deadline=$((started + timeout_seconds))
  output="$(mktemp "${TMPDIR:-/tmp}/pr-command-out.XXXXXX")"
  errors="$(mktemp "${TMPDIR:-/tmp}/pr-command-err.XXXXXX")"
  receipt "COMMAND_STARTED deadline_kind=api step=$step timeout_seconds=$timeout_seconds deadline_at=$deadline"
  "$@" >"$output" 2>"$errors" & pid=$!
  (
    sleep "$timeout_seconds"
    kill -TERM "$pid" 2>/dev/null || exit 0
    sleep 1
    kill -KILL "$pid" 2>/dev/null || true
  ) >/dev/null 2>&1 & watcher=$!
  if wait "$pid"; then rc=0; else rc=$?; fi
  kill "$watcher" 2>/dev/null || true; wait "$watcher" 2>/dev/null || true
  BOUNDED_OUTPUT="$(<"$output")"
  if [[ "$rc" -eq 143 || "$rc" -eq 137 ]]; then rc=124; result=timeout
  elif [[ "$rc" -ne 0 ]]; then result=exit
  fi
  if [[ "$rc" -ne 0 && -s "$errors" ]]; then head -c 4096 "$errors" >&2; fi
  rm -f "$output" "$errors"
  receipt "COMMAND_FINISHED deadline_kind=api step=$step timeout_seconds=$timeout_seconds result=$result deadline_at=$deadline exit_code=$rc"
  return "$rc"
}
gh_local() {
  local step="$1" timeout_seconds="$2"; shift 2
  run_bounded_capture "$step" "$timeout_seconds" env -u GH_TOKEN LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
}
gh_create() {
  local token="" CREATE_TOKEN=local
  if command -v gh-app >/dev/null 2>&1 \
      && run_bounded_capture gh-app-token "$PR_OPEN_TIMEOUT_SECONDS" gh-app token --auto \
      && [[ -n "$BOUNDED_OUTPUT" ]]; then
    token="$BOUNDED_OUTPUT"; CREATE_TOKEN="$token"
  fi
  if [[ "$CREATE_TOKEN" == local ]]; then
    gh_local pr-create "$PR_OPEN_TIMEOUT_SECONDS" "$@"
  else
    run_bounded_capture pr-create "$PR_OPEN_TIMEOUT_SECONDS" env GH_TOKEN="$CREATE_TOKEN" \
      LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
  fi
}
parse_snapshot() {
  jq -Rsec --argjson required "$1" --arg head "$2" '
    def member($xs): . as $value | $xs | index($value) != null;
    def sha: type == "string" and test("^[0-9a-f]{40}$");
    def database_id: type == "number" and . > 0 and floor == .;
    def nonempty_string: type == "string" and length > 0;
    def check_name: if .__typename == "CheckRun" then .name elif .__typename == "StatusContext" then .context else null end;
    def shape_ok: type == "object" and (if .__typename == "CheckRun" then
      (.name | type == "string" and length > 0) and (.status | type == "string") and has("conclusion") and
      (.conclusion == null or (.conclusion | type == "string")) and (.databaseId | database_id) and
      (.checkSuite | type == "object" and has("workflowRun")) and (.checkSuite.commit.oid == $head) and
      (.checkSuite.workflowRun == null or
        ((.checkSuite.app.id | nonempty_string) and (.checkSuite | has("branch")) and
         (.checkSuite.branch == null or (.checkSuite.branch.id | nonempty_string)) and
         (.checkSuite.workflowRun | type == "object" and (.databaseId | database_id) and
           (.workflow.id | nonempty_string) and (.event | nonempty_string) and
           (.runNumber | database_id) and (.runAttempt | database_id))))
      elif .__typename == "StatusContext" then
      (.context | type == "string" and length > 0) and (.state | type == "string") and
      (.id | type == "string" and length > 0) and (.commit.oid == $head) else false end);
    def enum_ok: if .__typename == "CheckRun" then
      (.status | member(["QUEUED","IN_PROGRESS","COMPLETED","WAITING","REQUESTED","PENDING"])) and
        (if .status == "COMPLETED" then (.conclusion | member(["FAILURE","CANCELLED","TIMED_OUT","SUCCESS","NEUTRAL","SKIPPED"])) else true end)
      else (.state | member(["FAILURE","ERROR","PENDING","EXPECTED","SUCCESS"])) end;
    def phase: if .__typename == "CheckRun" then if .status != "COMPLETED" then "pending"
      elif (.conclusion | member(["FAILURE","CANCELLED","TIMED_OUT"])) then "red" else "terminal" end
      elif (.state | member(["FAILURE","ERROR"])) then "red"
      elif (.state | member(["PENDING","EXPECTED"])) then "pending" else "terminal" end;
    def check_state: if .__typename == "CheckRun" then .conclusion else .state end;
    # Ref node IDs distinguish repositories as well as branch names, but not
    # PRs sharing a source ref. Such PR runs need the ambiguity guard below.
    # A deleted ref, external check or status has no comparable workflow origin.
    def origin: if .__typename == "CheckRun" then
      if .checkSuite.workflowRun != null and .checkSuite.branch != null then
        [.checkSuite.app.id, .checkSuite.workflowRun.workflow.id,
         .checkSuite.workflowRun.event, .checkSuite.branch.id]
      else ["check", .databaseId] end else ["status", .id] end;
    def evidence: {check:check_name, check_id:(.databaseId // .id),
      run_id:(.checkSuite.workflowRun.databaseId // null),
      app_id:.checkSuite.app.id, workflow_id:.checkSuite.workflowRun.workflow.id,
      event:.checkSuite.workflowRun.event, branch_id:.checkSuite.branch.id,
      run_number:.checkSuite.workflowRun.runNumber, run_attempt:.checkSuite.workflowRun.runAttempt,
      commit:(.checkSuite.commit.oid // .commit.oid), status:(.status // .state), conclusion:check_state};
    fromjson |
    select(type == "object" and (.errors == null or .errors == [])) |
    .data.repository |
    select(type == "object" and (.pullRequest | type == "object") and
      (.pullRequest.state | member(["OPEN","MERGED","CLOSED"])) and (.pullRequest.headRefOid | sha)) |
    .pullRequest as $pr |
    select((.object | type == "object") and .object.oid == $head and
      (.object | has("statusCheckRollup")) and
      (.object.statusCheckRollup == null or
        ((.object.statusCheckRollup.contexts.nodes | type == "array") and
         .object.statusCheckRollup.contexts.pageInfo.hasNextPage == false))) |
    (.object.statusCheckRollup.contexts.nodes // []) as $items |
    select(all($items[]; shape_ok)) |
    select(all($items[]; check_name as $name | if ($required | index($name)) != null then enum_ok else true end)) |
    [$items[] | select(.__typename == "CheckRun" and .checkSuite.workflowRun != null)] as $runs |
    select(all($runs | group_by(.checkSuite.workflowRun.databaseId)[];
      map(.checkSuite | [.app.id, .branch.id, .workflowRun]) | unique | length == 1)) |
    select(all($runs | group_by([.checkSuite.workflowRun.workflow.id, .checkSuite.workflowRun.runNumber])[];
      map(.checkSuite.workflowRun.databaseId) | unique | length == 1)) |
    # runNumber orders new executions, not reruns. WorkflowRun.runAttempt is
    # shared by its jobs; it cannot identify an individual check job attempt.
    # Multiple runs with a reattempt have no unambiguous ordering here.
    select(all($runs | group_by(origin)[];
      all(.[]; .checkSuite.workflowRun.runAttempt == 1) or
      (map(.checkSuite.workflowRun.databaseId) | unique | length == 1))) |
    if $pr.headRefOid != $head then {state:$pr.state, stale:true, observed_head:$pr.headRefOid}
    # WorkflowRun exposes no historical PR trigger identity. Neither current
    # matchingPullRequests nor a reusable workflow reference establishes it.
    # A later run from another PR/base must never erase an earlier failure.
    elif any($runs | group_by(origin)[];
      (.[0].checkSuite.workflowRun.event | startswith("pull_request")) and
      (map(.checkSuite.workflowRun.databaseId) | unique | length > 1)) then
      {unavailable:"ambiguous-pr-origin"}
    else
    ($items | group_by(origin) | map(. as $group |
      if .[0].__typename == "CheckRun" and .[0].checkSuite.workflowRun != null and .[0].checkSuite.branch != null then
        (map(.checkSuite.workflowRun.runNumber) | max) as $latest |
        {all:$group, current:map(select(.checkSuite.workflowRun.runNumber == $latest))}
      else {all:$group, current:$group} end)) as $groups |
    [$groups[].current[]] as $current |
    [$required[] as $name |
      [$groups[] | select(any(.all[]; check_name == $name)) |
        [.current[] | select(check_name == $name)]] as $by_origin |
      ($by_origin | add // []) as $found |
      if any($found[]; phase == "red") then ($found | map(select(phase == "red")) | first | {kind:"red",check:check_name,state:check_state})
      elif ($by_origin | length) == 0 or any($by_origin[]; length == 0) then {kind:"missing"}
      elif any($found[]; phase == "pending") then {kind:"pending"} else {kind:"terminal"} end] as $checks |
    {state:$pr.state, stale:false, red:($checks | map(select(.kind == "red")) | first // null),
     pending:($checks | map(select(.kind == "pending")) | length), missing:($checks | map(select(.kind == "missing")) | length),
     evidence:[$items[] | check_name as $name | select(($required | index($name)) != null) |
       . as $item | evidence + {superseded:($current | index($item) == null)}]} end
  '
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
        && parsed="$(printf '%s' "$BOUNDED_OUTPUT" | parse_snapshot "$required" "$head_sha" 2>/dev/null)" \
        && [[ -n "$parsed" ]] \
        && [[ "$(jq -r '.unavailable // empty' <<<"$parsed")" == "" ]]; then
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
      if [[ -n "$parsed" && "$(jq -r '.unavailable // empty' <<<"$parsed")" == ambiguous-pr-origin ]]; then
        receipt "PR_WATCH_PROGRESS pr=$number step=snapshot reason=ambiguous-pr-origin"
      fi
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

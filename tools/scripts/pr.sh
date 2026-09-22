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
          checkSuite { databaseId commit { oid } workflowRun { databaseId runNumber workflow { id } }
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
  jq -Rsec --argjson required "$1" --arg head "$2" --argjson number "$3" --argjson runs "$4" --arg repo "$PR_REPO" '
    def member($xs): . as $value | $xs | index($value) != null;
    def sha: type == "string" and test("^[0-9a-f]{40}$");
    def database_id: type == "number" and . > 0 and . <= 9007199254740991 and floor == .;
    def pr_event: . == "pull_request" or . == "pull_request_target";
    def native_run: .path == ".github/workflows/ci-pr.yml";
    # This repository calls exactly this reusable workflow at its PR merge commit.
    # GitHub retains that ref after merge even when pull_requests becomes empty.
    def native_pr:
      select(native_run and .event == "pull_request") |
      .referenced_workflows | select(type == "array" and length == 1) | .[0] |
      select(type == "object" and (.sha | sha and length == 40) and
        .path == ($repo + "/.github/workflows/ci-push.yml@" + .sha)) |
      .ref | select(type == "string") | capture("\\Arefs/pull/(?<number>[1-9][0-9]*)/merge\\z") |
      .number | tonumber | select(database_id);
    def associated_prs: if native_run then [native_pr] else [.pull_requests[].number] end;
    def run_metadata: .checkSuite.workflowRun.databaseId as $id | $runs[] | select(.id == $id);
    def check_name: if .__typename == "CheckRun" then .name elif .__typename == "StatusContext" then .context else null end;
    def producer: .checkSuite.workflowRun.workflow.id // null;
    def applicable: producer == null or (run_metadata | (.event | pr_event) and (associated_prs | index($number) != null));
    def latest_ids: .checkSuite.checkRuns.nodes | map(.databaseId) | sort;
    def latest_check: .databaseId as $id | latest_ids | index($id) != null;
    def shape_ok: type == "object" and (if .__typename == "CheckRun" then
      (.name | type == "string" and length > 0) and (.status | type == "string") and has("conclusion") and
      (.conclusion == null or (.conclusion | type == "string")) and (.databaseId | database_id) and
      (.checkSuite | type == "object" and has("workflowRun")) and (.checkSuite.commit.oid == $head) and
      (.checkSuite.workflowRun == null or
        ((.checkSuite.databaseId | database_id) and (.checkSuite.workflowRun.databaseId | database_id) and
         (.checkSuite.workflowRun.runNumber | database_id) and
         (.checkSuite.workflowRun.workflow.id | type == "string" and length > 0) and
         (.checkSuite.checkRuns.nodes | type == "array" and length > 0 and all(.[]; .databaseId | database_id)) and
         .checkSuite.checkRuns.pageInfo.hasNextPage == false))
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
    def evidence: {check:check_name, check_id:(.databaseId // .id),
      run_id:(.checkSuite.workflowRun.databaseId // null),
      workflow_id:producer, run_number:(.checkSuite.workflowRun.runNumber // null),
      commit:(.checkSuite.commit.oid // .commit.oid), status:(.status // .state), conclusion:check_state} +
      (if producer == null then {membership:"commit-context"}
       else {membership:"workflow-run", event:(run_metadata | .event),
         pull_requests:(run_metadata | [.pull_requests[].number])} +
         (if (run_metadata | native_run) then {referenced_workflow:(run_metadata | .referenced_workflows[0])}
          else {} end) end);
    fromjson |
    select(type == "object" and (.errors == null or .errors == [])) |
    .data.repository |
    select(type == "object" and .nameWithOwner == $repo and (.pullRequest | type == "object") and
      .pullRequest.number == $number and
      (.pullRequest.state | member(["OPEN","MERGED","CLOSED"])) and (.pullRequest.headRefOid | sha)) |
    .pullRequest as $pr |
    select((.object | type == "object") and .object.oid == $head and
      (.object | has("statusCheckRollup")) and
      (.object.statusCheckRollup == null or
        ((.object.statusCheckRollup.contexts.nodes | type == "array") and
         .object.statusCheckRollup.contexts.pageInfo.hasNextPage == false))) |
    (.object.statusCheckRollup.contexts.nodes // []) as $items |
    select(all($items[]; shape_ok)) |
    select([$items[] | select(.__typename == "CheckRun") | .databaseId] |
      length == (unique | length)) |
    select(all($items[]; check_name as $name | if ($required | index($name)) != null then enum_ok else true end)) |
    [$items[] | select(producer != null)] as $actions |
    # Repeated run metadata must agree, and every LATEST ID must resolve in this complete snapshot.
    select($actions | group_by(.checkSuite.workflowRun.databaseId) | all(.[];
      (.[0] | latest_ids) as $latest | map(.databaseId) as $observed |
      (map(.checkSuite | {databaseId,workflowRun}) | unique | length) == 1 and
      (map(latest_ids) | unique | length) == 1 and
      ($latest | length) == ($latest | unique | length) and
      all($latest[]; member($observed)) and
      (map(select(latest_check)) | group_by(.name) | all(.[]; length == 1)))) |
    select($actions | group_by([producer, .checkSuite.workflowRun.runNumber]) |
      all(.[]; (map(.checkSuite.workflowRun.databaseId) | unique | length) == 1)) |
    # Validate the complete snapshot before reading or excluding any execution.
    if $runs == null then [$actions[].checkSuite.workflowRun.databaseId] | unique
    else
    select(($runs | type == "array") and
      ([$runs[].id] | sort) == ([$actions[].checkSuite.workflowRun.databaseId] | unique)) |
    select(all($runs[];
      (.id | database_id) and .head_sha == $head and
      (.repository.id | database_id) and .repository.full_name == $repo and
      (.event | type == "string" and length > 0) and
      (.pull_requests | type == "array") and
      (if native_run then associated_prs as $prs |
        ($prs | length) == 1 and all(.pull_requests[]; .number == $prs[0])
       elif (.event | pr_event) then (.pull_requests | length > 0) else true end) and
      (.repository.id as $repository_id | all(.pull_requests[];
        type == "object" and (.id | database_id) and (.number | database_id) and
        .url == ("https://api.github.com/repos/" + $repo + "/pulls/" + (.number | tostring)) and
        .head.sha == $head and .base.repo.id == $repository_id)) and
      ([.pull_requests[].number] | length == (unique | length)))) |
    select(all($actions[]; . as $check | run_metadata |
      .check_suite_id == $check.checkSuite.databaseId and .run_number == $check.checkSuite.workflowRun.runNumber)) |
    # Membership precedes producer obligations and latest-run selection. A different PR
    # or non-PR event cannot supply a job, create an obligation, or retire an execution.
    [$items[] | select(applicable)] as $items |
    [$items[] | select(producer != null)] as $actions |
    # Include early, non-required jobs when selecting the latest execution for each workflow.
    ($actions | group_by(producer) | map({key:(.[0] | producer),
      value:(map(.checkSuite.workflowRun.runNumber) | max)}) | from_entries) as $latest_runs |
    if $pr.headRefOid != $head then {state:$pr.state, stale:true, observed_head:$pr.headRefOid}
    else
    [$required[] as $name | [$items[] | select(check_name == $name)] | group_by(producer) |
      # Keep each observed producer obligation, even if its latest run has no matching job yet.
      (if length == 0 then [] else .[] end) |
      map(select(producer == null or
        (.checkSuite.workflowRun.runNumber == $latest_runs[producer] and latest_check))) as $found |
      (if ($found | length) == 0 then {kind:"missing"}
      elif any($found[]; phase == "red") then ($found | map(select(phase == "red")) | first | {kind:"red",check:check_name,state:check_state})
      elif any($found[]; phase == "pending") then {kind:"pending"} else {kind:"terminal"} end) +
      {evidence:($found | map(evidence))}] as $checks |
    {state:$pr.state, stale:false, red:($checks | map(select(.kind == "red")) | first // null),
     pending:($checks | map(select(.kind == "pending")) | length), missing:($checks | map(select(.kind == "missing")) | length),
     evidence:[$checks[].evidence[]]} end end
  '
}
read_snapshot() {
  local required="$1" head_sha="$2" number="$3" deadline="$4" snapshot="$BOUNDED_OUTPUT"
  local run_ids run_id metadata runs='[]' remaining call_timeout
  run_ids="$(printf '%s' "$snapshot" | parse_snapshot "$required" "$head_sha" "$number" null 2>/dev/null)" || return 1
  while IFS= read -r run_id; do
    [[ -n "$run_id" ]] || continue
    remaining=$((deadline - $(date +%s)))
    (( remaining > 0 )) || return 1
    call_timeout=$((remaining < PR_OPEN_TIMEOUT_SECONDS ? remaining : PR_OPEN_TIMEOUT_SECONDS))
    # Read explicit associations and the retained native merge ref from the run itself.
    # Consume pagination; extra resource pages fail closed.
    gh_local run-membership "$call_timeout" api --paginate --slurp "repos/$PR_REPO/actions/runs/$run_id" || return 1
    metadata="$(printf '%s' "$BOUNDED_OUTPUT" | jq -Rsec '
      fromjson | select(type == "array" and length == 1 and (.[0] | type == "object")) | .[0]
    ' 2>/dev/null)" || return 1
    runs="$(jq -c --argjson run "$metadata" '. + [$run]' <<<"$runs")" || return 1
  done < <(jq -r '.[]' <<<"$run_ids")
  printf '%s' "$snapshot" | parse_snapshot "$required" "$head_sha" "$number" "$runs" 2>/dev/null
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
        && parsed="$(read_snapshot "$required" "$head_sha" "$number" "$deadline")" \
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

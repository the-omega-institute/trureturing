#!/usr/bin/env bash
set -euo pipefail
PR_REPO="${PR_OPEN_REPO:-the-omega-institute/trureturing}"
PR_BASE="${PR_OPEN_BASE:-dev}"
PR_OPEN_TIMEOUT_SECONDS="${PR_OPEN_TIMEOUT_SECONDS:-60}"
PR_WATCH_INTERVAL_SECONDS="${PR_WATCH_INTERVAL_SECONDS:-10}"
PR_WATCH_TIMEOUT_SECONDS="${PR_WATCH_TIMEOUT_SECONDS:-4200}"
PR_WATCH_MAX_FAILURES=3
PR_WATCH_MAX_ORIGIN_PAGES=100
PR_WATCH_MAX_LOG_BYTES=67108864
BOUNDED_OUTPUT=""
receipt() { printf '%s\n' "$*" >&2; }
watch_result() { printf 'PR_WATCH_RESULT pr=%s %s head_sha=%s\n' "$1" "$3" "$2"; }
positive_integer() { [[ "$1" =~ ^[1-9][0-9]*$ ]]; }
commit_sha() { [[ "$1" =~ ^[0-9a-f]{40}$ ]]; }
usage_open() { receipt "usage: pr.sh open --head HEAD --message-file FILE [--auto-merge] [--timeout-seconds S] [--interval-seconds S]"; }
usage_watch() { receipt "usage: pr.sh watch --pr NUMBER --head-sha SHA [--timeout-seconds S] [--interval-seconds S]"; }
PR_SNAPSHOT_QUERY='query($owner:String!,$repo:String!,$pr:Int!,$head:GitObjectID!) {
  repository(owner:$owner,name:$repo) {
    databaseId nameWithOwner
    pullRequest(number:$pr) { state headRefOid }
    object(oid:$head) { ... on Commit { oid statusCheckRollup { contexts(first:100) {
      nodes { __typename
        ... on CheckRun { databaseId name status conclusion
          checkSuite { databaseId app { id } branch { id } commit { oid }
            workflowRun { databaseId event runNumber runAttempt workflow { id databaseId }
              file { path repositoryName run { databaseId } } } } }
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
run_bounded_file() {
  local step="$1" timeout_seconds="$2" output_path="$3"; shift 3
  local started deadline output errors pid watcher rc=0 result=success
  started="$(date +%s)"; deadline=$((started + timeout_seconds))
  errors="$(mktemp "${TMPDIR:-/tmp}/pr-command-err.XXXXXX")"
  receipt "COMMAND_STARTED deadline_kind=api step=$step timeout_seconds=$timeout_seconds deadline_at=$deadline"
  "$@" >"$output_path" 2>"$errors" & pid=$!
  (
    sleep "$timeout_seconds"
    kill -TERM "$pid" 2>/dev/null || exit 0
    sleep 1
    kill -KILL "$pid" 2>/dev/null || true
  ) >/dev/null 2>&1 & watcher=$!
  if wait "$pid"; then rc=0; else rc=$?; fi
  kill "$watcher" 2>/dev/null || true; wait "$watcher" 2>/dev/null || true
  if [[ "$rc" -eq 143 || "$rc" -eq 137 ]]; then rc=124; result=timeout
  elif [[ "$rc" -ne 0 ]]; then result=exit
  fi
  if [[ "$rc" -ne 0 && -s "$errors" ]]; then head -c 4096 "$errors" >&2; fi
  rm -f "$errors"
  receipt "COMMAND_FINISHED deadline_kind=api step=$step timeout_seconds=$timeout_seconds result=$result deadline_at=$deadline exit_code=$rc"
  return "$rc"
}
gh_local() {
  local step="$1" timeout_seconds="$2"; shift 2
  run_bounded_capture "$step" "$timeout_seconds" env -u GH_TOKEN LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
}
gh_local_file() {
  local step="$1" timeout_seconds="$2" output_path="$3"; shift 3
  run_bounded_file "$step" "$timeout_seconds" "$output_path" env -u GH_TOKEN LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
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
  jq -Rsec --argjson required "$1" --arg head "$2" --argjson certified "${3:-[]}" '
    def member($xs): . as $value | $xs | index($value) != null;
    def sha: type == "string" and test("^[0-9a-f]{40}$");
    def database_id: type == "number" and . > 0 and floor == .;
    def nonempty_string: type == "string" and length > 0;
    def check_name: if .__typename == "CheckRun" then .name elif .__typename == "StatusContext" then .context else null end;
    def shape_ok: type == "object" and (if .__typename == "CheckRun" then
      (.name | type == "string" and length > 0) and (.status | type == "string") and has("conclusion") and
      (.conclusion == null or (.conclusion | type == "string")) and (.databaseId | database_id) and
      (.checkSuite | type == "object" and (.databaseId | database_id) and has("workflowRun")) and (.checkSuite.commit.oid == $head) and
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
    . as $repository | .pullRequest as $pr |
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
      map(.checkSuite | [.databaseId, .app.id, .branch.id, .workflowRun]) | unique | length == 1)) |
    select(all($runs | group_by([.checkSuite.workflowRun.workflow.id, .checkSuite.workflowRun.runNumber])[];
      map(.checkSuite.workflowRun.databaseId) | unique | length == 1)) |
    # A snapshot for a different PR head is stale. Its execution ordering is
    # irrelevant because no result for the watched head can be certified.
    if $pr.headRefOid != $head then {state:$pr.state, stale:true, observed_head:$pr.headRefOid}
    else
    # runNumber orders new executions, not reruns. WorkflowRun.runAttempt is
    # shared by its jobs; it cannot identify an individual check job attempt.
    # Multiple runs with a reattempt have no unambiguous ordering here.
    select(all($runs | group_by(origin)[];
      all(.[]; .checkSuite.workflowRun.runAttempt == 1) or
      (map(.checkSuite.workflowRun.databaseId) | unique | length == 1))) |
    # Only exact attempt system records can authorize PR-run supersession.
    # Current PR associations and reusable leaf refs are not trigger identity.
    ([$runs | group_by(origin)[] |
      select((.[0].checkSuite.workflowRun.event | startswith("pull_request")) and
        (map(.checkSuite.workflowRun.databaseId) | unique | length > 1)) | .[]] |
      unique_by(.checkSuite.workflowRun.databaseId) |
      map(.checkSuite.workflowRun.databaseId)) as $needed |
    if ($needed - $certified | length > 0) then
      {unavailable:"ambiguous-pr-origin", runs:[$runs |
        group_by(.checkSuite.workflowRun.databaseId)[] |
        select(.[0].checkSuite.workflowRun.databaseId as $id | $needed | index($id)) |
        {run:.[0].checkSuite.workflowRun, suite:.[0].checkSuite.databaseId,
         repository_id:$repository.databaseId, repository:$repository.nameWithOwner,
         checks:map({id:.databaseId, name:.name})}]}

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
    end
  '
}
origin_archive_identity() {
  local archive="$1" jobs_file="$2" expected_repo="$3" expected_path="$4"
  python3 - "$archive" "$jobs_file" "$expected_repo" "$expected_path" <<'PY'
import json
import re
import sys
import zipfile

archive, jobs_file, expected_repo, expected_path = sys.argv[1:]

def invalid():
    raise SystemExit(1)

try:
    jobs_payload = json.load(open(jobs_file, encoding="utf-8"))
    jobs = jobs_payload["jobs"]
    if not isinstance(jobs, list) or not jobs:
        invalid()
    by_dir = {}
    seen_job_ids = set()
    seen_job_names = set()
    for job in jobs:
        if not isinstance(job, dict):
            invalid()
        job_id = job.get("id")
        name = job.get("name")
        if not isinstance(job_id, int) or job_id <= 0 or not isinstance(name, str) or not name:
            invalid()
        if job_id in seen_job_ids or name in seen_job_names:
            invalid()
        seen_job_ids.add(job_id)
        seen_job_names.add(name)
        # Only the observed slash substitution is supported; no guessed sanitization.
        if not re.fullmatch(r"[A-Za-z0-9_. ()/,-]+", name):
            invalid()
        encoded = name.replace("/", "_")
        by_dir.setdefault(encoded, []).append(name)

    # Observed GitHub preparation grammar, not a versioned vendor schema.
    # Unknown identity/chain syntax fails closed. Step stdout is never parsed.
    timestamp = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+Z (.*)$")
    reference = r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+/\.github/workflows/[^/@\s]+\.ya?ml@[^\s]+"
    direct_re = re.compile(r"Job defined at: (" + reference + r")")
    chain_re = re.compile(r"(" + reference + r") \([0-9a-f]{40}\)")
    roots = []
    system_jobs = set()
    with zipfile.ZipFile(archive) as zf:
        infos = zf.infolist()
        if len(infos) > 20000 or sum(i.file_size for i in infos) > 67108864:
            invalid()
        names = set()
        for info in infos:
            original_name = info.orig_filename
            if original_name != info.filename:
                invalid()
            name = original_name
            parts = name.rstrip("/").split("/")
            mode = (info.external_attr >> 16) & 0o170000
            if (not name or "\\" in name or name.startswith("/") or
                any(ord(c) < 32 for c in name) or
                any(part in ("", ".", "..") for part in parts) or
                mode not in (0, 0o100000, 0o040000) or info.flag_bits & 1):
                invalid()
            if name.rstrip("/") in names:
                invalid()
            names.add(name.rstrip("/"))
        for info in infos:
            name = info.filename
            if info.is_dir() or not name.endswith("/system.txt"):
                continue
            if len(name.split("/")) != 2 or info.file_size > 1048576:
                invalid()
            parent = name[:-len("/system.txt")]
            candidates = by_dir.get(parent, [])
            if len(candidates) != 1:
                invalid()
            job_name = candidates[0]
            if job_name in system_jobs:
                invalid()
            system_jobs.add(job_name)
            lines = []
            for line in zf.read(info).decode("utf-8").splitlines():
                match = timestamp.fullmatch(line)
                if not match:
                    invalid()
                lines.append(match[1])
            direct = [direct_re.fullmatch(line) for line in lines if "Job defined at" in line]
            if len(direct) != 1 or direct[0] is None:
                invalid()
            leaf = direct[0][1]
            markers = [i for i, line in enumerate(lines) if "Reusable workflow chain" in line]
            if markers:
                if len(markers) != 1 or lines[markers[0]] != "Reusable workflow chain:":
                    invalid()
                i = markers[0] + 1
                root_match = chain_re.fullmatch(lines[i]) if i < len(lines) else None
                if root_match is None:
                    invalid()
                root = root_match[1]
                chain = [root]
                i += 1
                while i < len(lines) and lines[i].startswith("-> "):
                    match = chain_re.fullmatch(lines[i][3:])
                    if match is None:
                        invalid()
                    chain.append(match[1])
                    i += 1
                if len(chain) < 2 or chain[-1] != leaf:
                    invalid()
                consumed = set(range(markers[0] + 1, i))
                if any(("@" in line or line.startswith("->")) and
                       j not in consumed and not line.startswith("Job defined at: ")
                       for j, line in enumerate(lines)):
                    invalid()
            else:
                root = leaf
                if any(line.startswith("->") or chain_re.fullmatch(line) for line in lines):
                    invalid()
            roots.append(root)
    if not roots or len(set(roots)) != 1:
        invalid()
    root_target, root_ref = roots[0].split("@", 1)
    target_parts = root_target.split("/", 2)
    if len(target_parts) != 3 or target_parts[0] + "/" + target_parts[1] != expected_repo:
        invalid()
    if target_parts[2] != expected_path:
        invalid()
    match = re.fullmatch(r"refs/pull/([1-9][0-9]*)/merge", root_ref)
    if match is None:
        invalid()
    pull_number = match[1]
    print(expected_repo + "|" + pull_number)
except (OSError, KeyError, TypeError, ValueError, UnicodeError, zipfile.BadZipFile,
        zipfile.LargeZipFile):
    invalid()
PY
}
# Every origin API call shares the watch deadline, including pagination/download.
origin_api() {
  local step="$1" deadline="$2"; shift 2
  local remaining timeout
  remaining=$((deadline - $(date +%s)))
  (( remaining > 0 )) || return 1
  timeout=$((remaining < PR_OPEN_TIMEOUT_SECONDS ? remaining : PR_OPEN_TIMEOUT_SECONDS))
  gh_local "$step" "$timeout" api "$@"
}
origin_for_run() {
  local expected="$1" watched_head="$2" deadline="$3"
  local run_id attempt workflow_path metadata jobs all_jobs='[]' total=-1 page count
  jq -e --arg repo "$PR_REPO" '
    def id: type == "number" and . > 0 and floor == .;
    (.repository_id | id) and .repository == $repo and (.suite | id) and
    (.run.databaseId | id) and .run.runAttempt == 1 and .run.event == "pull_request" and
    (.run.workflow.databaseId | id) and .run.file.run.databaseId == .run.databaseId and
    .run.file.repositoryName == $repo and
    (.run.file.path | type == "string" and test("^\\.github/workflows/[^/@]+\\.ya?ml$"))' \
    <<<"$expected" >/dev/null 2>&1 || return 1
  run_id="$(jq -r '.run.databaseId' <<<"$expected")"
  attempt="$(jq -r '.run.runAttempt' <<<"$expected")"
  workflow_path="$(jq -r '.run.file.path' <<<"$expected")"
  origin_api origin-attempt "$deadline" "repos/$PR_REPO/actions/runs/$run_id/attempts/$attempt" || return 1
  metadata="$BOUNDED_OUTPUT"
  origin_metadata_matches "$metadata" "$expected" "$watched_head" || return 1
  for ((page=1; page<=PR_WATCH_MAX_ORIGIN_PAGES; page++)); do
    origin_api origin-jobs "$deadline" "repos/$PR_REPO/actions/runs/$run_id/attempts/$attempt/jobs?per_page=100&page=$page" || return 1
    jobs="$BOUNDED_OUTPUT"
    jq -e --argjson id "$run_id" --argjson attempt "$attempt" --arg head "$watched_head" '
      (.total_count | type == "number" and floor == . and . > 0) and
      (.jobs | type == "array" and length > 0 and length <= 100) and
      all(.jobs[]; (.id | type == "number" and floor == . and . > 0) and
        (.name | type == "string" and length > 0) and .run_id == $id and
        .run_attempt == $attempt and .head_sha == $head)' <<<"$jobs" >/dev/null 2>&1 || return 1
    if (( total == -1 )); then total="$(jq -r '.total_count' <<<"$jobs")"; fi
    [[ "$total" == "$(jq -r '.total_count' <<<"$jobs")" ]] || return 1
    all_jobs="$(jq -nc --argjson old "$all_jobs" --argjson page "$jobs" '$old + $page.jobs')" || return 1
    count="$(jq 'length' <<<"$all_jobs")"
    (( count <= total )) || return 1
    (( count != total )) || break
  done
  (( page <= PR_WATCH_MAX_ORIGIN_PAGES )) || return 1
  jq -e --argjson expected "$expected" '
    . as $jobs | all($expected.checks[]; . as $check |
      [$jobs[] | select(.id == $check.id and .name == $check.name)] | length == 1)' \
    <<<"$all_jobs" >/dev/null 2>&1 || return 1
  local directory archive identity remaining timeout
  directory="$(mktemp -d "${TMPDIR:-/tmp}/pr-origin.XXXXXX")" || return 1
  archive="$directory/logs.zip"
  jq -nc --argjson jobs "$all_jobs" '{jobs:$jobs}' >"$directory/jobs.json"
  remaining=$((deadline - $(date +%s)))
  timeout=$((remaining < PR_OPEN_TIMEOUT_SECONDS ? remaining : PR_OPEN_TIMEOUT_SECONDS))
  if (( remaining <= 0 )) || ! gh_local_file origin-logs "$timeout" "$archive" api \
      "repos/$PR_REPO/actions/runs/$run_id/attempts/$attempt/logs"; then
    rm -rf "$directory"; return 1
  fi
  if (( $(wc -c <"$archive") > PR_WATCH_MAX_LOG_BYTES )) ||
      ! identity="$(origin_archive_identity "$archive" "$directory/jobs.json" "$PR_REPO" "$workflow_path")"; then
    rm -rf "$directory"; return 1
  fi
  rm -rf "$directory"
  # Reject an attempt change during collection; an attempt URL alone pins old data.
  origin_api origin-current "$deadline" "repos/$PR_REPO/actions/runs/$run_id" || return 1
  origin_metadata_matches "$BOUNDED_OUTPUT" "$expected" "$watched_head" || return 1
  printf '%s\n' "$identity"
}
origin_metadata_matches() {
  # Parse the entire response once; jq -e on a stream only checks its last result.
  jq -Rse --argjson expected "$2" --arg head "$3" '
    fromjson | select(type == "object") |
    .id == $expected.run.databaseId and .run_attempt == $expected.run.runAttempt and
    .run_number == $expected.run.runNumber and .head_sha == $head and
    .event == $expected.run.event and .workflow_id == $expected.run.workflow.databaseId and
    .check_suite_id == $expected.suite and .repository.id == $expected.repository_id and
    .repository.full_name == $expected.repository and .path == $expected.run.file.path' \
    <<<"$1" >/dev/null 2>&1
}
certify_snapshot_origins() {
  local parsed="$1" watched_pr="$2" watched_head="$3" deadline="$4"
  local expected="$PR_REPO|$watched_pr" identity run runs_file
  runs_file="$(mktemp "${TMPDIR:-/tmp}/pr-origin-runs.XXXXXX")" || return 1
  if ! jq -c '.runs[]' <<<"$parsed" >"$runs_file" || [[ ! -s "$runs_file" ]]; then
    rm -f "$runs_file"
    return 1
  fi
  while IFS= read -r run; do
    if [[ -z "$run" ]] || ! identity="$(origin_for_run "$run" "$watched_head" "$deadline")" ||
        [[ "$identity" != "$expected" ]]; then
      rm -f "$runs_file"
      return 1
    fi
  done <"$runs_file"
  rm -f "$runs_file"
  jq -c '[.runs[].run.databaseId]' <<<"$parsed"
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
    local snapshot="" certified="[]"
    parsed=""
    if gh_local snapshot "$call_timeout" api graphql -f query="$PR_SNAPSHOT_QUERY" \
        -f owner="${PR_REPO%%/*}" -f repo="${PR_REPO#*/}" -F pr="$number" -f head="$head_sha"; then
      snapshot="$BOUNDED_OUTPUT"
      parsed="$(printf '%s' "$snapshot" | parse_snapshot "$required" "$head_sha" 2>/dev/null)" || parsed=""
      if [[ -n "$parsed" && "$(jq -r '.unavailable // empty' <<<"$parsed")" == ambiguous-pr-origin ]]; then
        if certified="$(certify_snapshot_origins "$parsed" "$number" "$head_sha" "$deadline")"; then
          parsed="$(printf '%s' "$snapshot" | parse_snapshot "$required" "$head_sha" "$certified" 2>/dev/null)" || parsed=""
        else
          receipt "PR_WATCH_PROGRESS pr=$number step=snapshot reason=ambiguous-pr-origin"
          parsed=""
        fi
      fi
    fi
    if [[ -n "$parsed" && "$(jq -r '.unavailable // empty' <<<"$parsed")" == "" ]]; then
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

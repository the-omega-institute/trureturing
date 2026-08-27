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
positive_integer() { [[ "$1" =~ ^[1-9][0-9]*$ ]]; }
usage_open() { receipt "usage: pr.sh open --head HEAD --message-file FILE [--auto-merge] [--timeout-seconds S] [--interval-seconds S]"; }
usage_watch() { receipt "usage: pr.sh watch --pr NUMBER [--timeout-seconds S] [--interval-seconds S]"; }
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
  jq -Rsec --argjson required "$1" '
    def member($xs): . as $value | $xs | index($value) != null;
    def check_name: if .__typename == "CheckRun" then .name elif .__typename == "StatusContext" then .context else null end;
    def shape_ok: type == "object" and (if .__typename == "CheckRun" then
      (.name | type == "string" and length > 0) and (.status | type == "string") and has("conclusion") and
      (.conclusion == null or (.conclusion | type == "string")) elif .__typename == "StatusContext" then
      (.context | type == "string" and length > 0) and (.state | type == "string") else false end);
    def enum_ok: if .__typename == "CheckRun" then
      (.status | member(["QUEUED","IN_PROGRESS","COMPLETED","WAITING","REQUESTED","PENDING"])) and
        (if .status == "COMPLETED" then (.conclusion | member(["FAILURE","CANCELLED","TIMED_OUT","SUCCESS","NEUTRAL","SKIPPED"])) else true end)
      else (.state | member(["FAILURE","ERROR","PENDING","EXPECTED","SUCCESS"])) end;
    def phase: if .__typename == "CheckRun" then if .status != "COMPLETED" then "pending"
      elif (.conclusion | member(["FAILURE","CANCELLED","TIMED_OUT"])) then "red" else "terminal" end
      elif (.state | member(["FAILURE","ERROR"])) then "red"
      elif (.state | member(["PENDING","EXPECTED"])) then "pending" else "terminal" end;
    def check_state: if .__typename == "CheckRun" then .conclusion else .state end; fromjson |
    select(type == "object" and (.state | member(["OPEN","MERGED","CLOSED"])) and (.statusCheckRollup | type == "array" or type == "null")) |
    (.statusCheckRollup // []) as $items |
    select(all($items[]; shape_ok)) |
    select(all($items[]; check_name as $name | if ($required | index($name)) != null then enum_ok else true end)) |
    [$required[] as $name | [$items[] | select(check_name == $name)] as $found |
      if ($found | length) == 0 then {kind:"missing"}
      elif any($found[]; phase == "red") then ($found | map(select(phase == "red")) | first | {kind:"red",check:check_name,state:check_state})
      elif any($found[]; phase == "pending") then {kind:"pending"} else {kind:"terminal"} end] as $checks |
    {state:.state, red:($checks | map(select(.kind == "red")) | first // null), pending:($checks | map(select(.kind == "pending")) | length),
     missing:($checks | map(select(.kind == "missing")) | length)}
  '
}
pr_watch_main() {
  local number="" timeout_seconds="$PR_WATCH_TIMEOUT_SECONDS" interval_seconds="$PR_WATCH_INTERVAL_SECONDS"
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --pr) [[ $# -ge 2 ]] || { usage_watch; return 2; }; number="$2"; shift 2 ;;
      --timeout-seconds) [[ $# -ge 2 ]] || { usage_watch; return 2; }; timeout_seconds="$2"; shift 2 ;;
      --interval-seconds) [[ $# -ge 2 ]] || { usage_watch; return 2; }; interval_seconds="$2"; shift 2 ;;
      *) usage_watch; return 2 ;;
    esac
  done
  positive_integer "$number" && positive_integer "$timeout_seconds" && positive_integer "$interval_seconds" \
    || { usage_watch; return 2; }
  local started deadline now remaining call_timeout failures=0 seen_snapshot=0 required="" parsed="" state="" red_check="" red_state="" pending=0 missing=0
  started="$(date +%s)"; deadline=$((started + timeout_seconds))
  while [[ -z "$required" ]]; do
    now="$(date +%s)"; remaining=$((deadline - now))
    if (( remaining <= 0 )); then printf 'PR_WATCH_RESULT pr=%s outcome=query-unavailable step=required-set attempts=%s\n' "$number" "$failures"; return 69; fi
    call_timeout=$((remaining < PR_OPEN_TIMEOUT_SECONDS ? remaining : PR_OPEN_TIMEOUT_SECONDS))
    if gh_local required-set "$call_timeout" api "repos/$PR_REPO/branches/$PR_BASE/protection/required_status_checks" \
        && [[ -n "$BOUNDED_OUTPUT" ]] \
        && required="$(printf '%s' "$BOUNDED_OUTPUT" | jq -Rsec 'if length == 0 then [] else fromjson | select(type == "object" and (.contexts | type == "array") and all(.contexts[]; type == "string" and length > 0)) | [.contexts[]] | unique end' 2>/dev/null)" \
        && [[ -n "$required" ]]; then
      failures=0; break
    fi
    required=""; failures=$((failures + 1))
    receipt "PR_WATCH_PROGRESS pr=$number step=required-set unavailable_attempts=$failures"
    if (( failures >= PR_WATCH_MAX_FAILURES )); then
      printf 'PR_WATCH_RESULT pr=%s outcome=query-unavailable step=required-set attempts=%s\n' "$number" "$failures"
      return 69
    fi
    now="$(date +%s)"; remaining=$((deadline - now))
    (( remaining > 0 )) || { printf 'PR_WATCH_RESULT pr=%s outcome=query-unavailable step=required-set attempts=%s\n' "$number" "$failures"; return 69; }
    sleep "$((interval_seconds < remaining ? interval_seconds : remaining))"
  done
  missing="$(jq -r 'length' <<<"$required")"
  while :; do
    now="$(date +%s)"; remaining=$((deadline - now))
    if (( remaining <= 0 )); then
      if (( failures > 0 || seen_snapshot == 0 )); then
        printf 'PR_WATCH_RESULT pr=%s outcome=query-unavailable step=snapshot attempts=%s\n' "$number" "$failures"; return 69
      fi
      printf 'PR_WATCH_RESULT pr=%s outcome=timeout pending=%s missing=%s\n' "$number" "$pending" "$missing"; return 124
    fi
    call_timeout=$((remaining < PR_OPEN_TIMEOUT_SECONDS ? remaining : PR_OPEN_TIMEOUT_SECONDS))
    if gh_local snapshot "$call_timeout" pr view "$number" --repo "$PR_REPO" --json state,statusCheckRollup \
        && [[ -n "$BOUNDED_OUTPUT" ]] \
        && parsed="$BOUNDED_OUTPUT" \
        && parsed="$(printf '%s' "$BOUNDED_OUTPUT" | parse_snapshot "$required" 2>/dev/null)" \
        && [[ -n "$parsed" ]]; then
      failures=0; seen_snapshot=1
      state="$(jq -r '.state' <<<"$parsed")"; red_check="$(jq -r '.red.check // empty' <<<"$parsed")"
      red_state="$(jq -r '.red.state // empty' <<<"$parsed")"; pending="$(jq -r '.pending' <<<"$parsed")"; missing="$(jq -r '.missing' <<<"$parsed")"
      now="$(date +%s)"
      if (( now >= deadline )); then printf 'PR_WATCH_RESULT pr=%s outcome=timeout pending=%s missing=%s\n' "$number" "$pending" "$missing"; return 124; fi
      if [[ -n "$red_check" ]]; then printf 'PR_WATCH_RESULT pr=%s outcome=red check=%s state=%s\n' "$number" "$red_check" "$red_state"; return 1; fi
      if [[ "$state" == MERGED ]]; then printf 'PR_WATCH_RESULT pr=%s outcome=green\n' "$number"; return 0; fi
      if [[ "$state" == CLOSED ]]; then printf 'PR_WATCH_RESULT pr=%s outcome=closed\n' "$number"; return 4; fi
      if (( pending == 0 && missing == 0 )); then printf 'PR_WATCH_RESULT pr=%s outcome=green\n' "$number"; return 0; fi
      receipt "PR_WATCH_PROGRESS pr=$number state=$state pending=$pending missing=$missing"
    else
      parsed=""; failures=$((failures + 1))
      receipt "PR_WATCH_PROGRESS pr=$number step=snapshot unavailable_attempts=$failures"
      if (( failures >= PR_WATCH_MAX_FAILURES )); then printf 'PR_WATCH_RESULT pr=%s outcome=query-unavailable step=snapshot attempts=%s\n' "$number" "$failures"; return 69; fi
    fi
    now="$(date +%s)"; remaining=$((deadline - now))
    if (( remaining <= 0 && (failures > 0 || seen_snapshot == 0) )); then printf 'PR_WATCH_RESULT pr=%s outcome=query-unavailable step=snapshot attempts=%s\n' "$number" "$failures"; return 69; fi
    (( remaining > 0 )) || { printf 'PR_WATCH_RESULT pr=%s outcome=timeout pending=%s missing=%s\n' "$number" "$pending" "$missing"; return 124; }
    sleep "$((interval_seconds < remaining ? interval_seconds : remaining))"
  done
}
pr_open_main() {
  local head="" message_file="" title="" body_file="" url number rc=0 auto_merge=0
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
  body_file="$(mktemp "${TMPDIR:-/tmp}/pr-body.XXXXXX")"
  tail -n +2 "$message_file" | sed '1{/^$/d;}' > "$body_file"
  local args=(pr create --repo "$PR_REPO" --base "$PR_BASE" --head "$head" --title "$title" --body-file "$body_file")
  gh_create "${args[@]}" || rc=$?
  rm -f "$body_file"
  (( rc == 0 )) || return "$rc"
  url="$(printf '%s\n' "$BOUNDED_OUTPUT" | tail -n 1)"; number="${url##*/}"
  if ! positive_integer "$number"; then receipt "pr.sh open: create returned no pull request number"; return 1; fi
  if (( auto_merge == 1 )); then
    gh_local auto-merge "$PR_OPEN_TIMEOUT_SECONDS" pr merge "$number" --repo "$PR_REPO" --auto --merge || return $?
  fi
  printf '%s\n' "$number"
  pr_watch_main --pr "$number" --timeout-seconds "$timeout_seconds" --interval-seconds "$interval_seconds" || return $?
}
case "${1:-}" in
  open) shift; pr_open_main "$@" ;;
  watch) shift; pr_watch_main "$@" ;;
  *) receipt "usage: pr.sh <open|watch>"; exit 2 ;;
esac

#!/usr/bin/env bash
set -euo pipefail

PR_REPO="${PR_OPEN_REPO:-the-omega-institute/trureturing}"
PR_BASE="${PR_OPEN_BASE:-dev}"
PR_TIMEOUT_SECONDS="${PR_OPEN_TIMEOUT_SECONDS:-60}"
BOUNDED_OUTPUT=""

receipt() { printf '%s\n' "$*" >&2; }

run_bounded_capture() {
  local step="$1"; shift
  local started deadline output errors pid watcher rc=0 result=success
  started="$(date +%s)"
  deadline=$((started + PR_TIMEOUT_SECONDS))
  output="$(mktemp "${TMPDIR:-/tmp}/pr-command-out.XXXXXX")"
  errors="$(mktemp "${TMPDIR:-/tmp}/pr-command-err.XXXXXX")"
  receipt "COMMAND_STARTED deadline_kind=api step=$step timeout_seconds=$PR_TIMEOUT_SECONDS deadline_at=$deadline"
  "$@" >"$output" 2>"$errors" & pid=$!
  (
    sleep "$PR_TIMEOUT_SECONDS"
    kill -TERM "$pid" 2>/dev/null || exit 0
    sleep 1
    kill -KILL "$pid" 2>/dev/null || true
  ) >/dev/null 2>&1 & watcher=$!
  if wait "$pid"; then rc=0; else rc=$?; fi
  kill "$watcher" 2>/dev/null || true
  wait "$watcher" 2>/dev/null || true
  BOUNDED_OUTPUT="$(<"$output")"
  if [[ "$rc" -eq 143 || "$rc" -eq 137 ]]; then rc=124; result=timeout
  elif [[ "$rc" -ne 0 ]]; then result=exit
  fi
  if [[ "$rc" -ne 0 && -s "$errors" ]]; then head -c 4096 "$errors" >&2; fi
  rm -f "$output" "$errors"
  receipt "COMMAND_FINISHED deadline_kind=api step=$step timeout_seconds=$PR_TIMEOUT_SECONDS result=$result deadline_at=$deadline exit_code=$rc"
  return "$rc"
}

gh_local() {
  local step="$1"; shift
  run_bounded_capture "$step" env -u GH_TOKEN LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
}

gh_create() {
  local token="" CREATE_TOKEN="local"
  if command -v gh-app >/dev/null 2>&1 \
      && run_bounded_capture gh-app-token gh-app token --auto \
      && [[ -n "$BOUNDED_OUTPUT" ]]; then
    token="$BOUNDED_OUTPUT"
    CREATE_TOKEN="$token"
  fi
  if [[ "$CREATE_TOKEN" == local ]]; then
    gh_local pr-create "$@"
  else
    run_bounded_capture pr-create env GH_TOKEN="$CREATE_TOKEN" \
      LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
  fi
}

pr_open_main() {
  local head="" title="" body_file="" url number
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --head) [[ $# -ge 2 ]] || { receipt "usage: pr.sh open --head HEAD --title TITLE [--body-file FILE]"; return 2; }; head="$2"; shift 2 ;;
      --title) [[ $# -ge 2 ]] || { receipt "usage: pr.sh open --head HEAD --title TITLE [--body-file FILE]"; return 2; }; title="$2"; shift 2 ;;
      --body-file) [[ $# -ge 2 ]] || { receipt "usage: pr.sh open --head HEAD --title TITLE [--body-file FILE]"; return 2; }; body_file="$2"; shift 2 ;;
      *) receipt "usage: pr.sh open --head HEAD --title TITLE [--body-file FILE]"; return 2 ;;
    esac
  done
  if [[ -z "$head" || -z "$title" ]]; then
    receipt "usage: pr.sh open --head HEAD --title TITLE [--body-file FILE]"
    return 2
  fi
  if [[ -n "$body_file" && ! -r "$body_file" ]]; then
    receipt "pr.sh open: body file is not readable: $body_file"
    return 2
  fi
  local args=(pr create --repo "$PR_REPO" --base "$PR_BASE" --head "$head" --title "$title")
  if [[ -n "$body_file" ]]; then args+=(--body-file "$body_file"); else args+=(--fill-first); fi
  gh_create "${args[@]}" || return $?
  # gh may print notices before the URL, so the number comes from the last line only.
  url="$(printf '%s\n' "$BOUNDED_OUTPUT" | tail -n 1)"
  number="${url##*/}"
  if [[ ! "$number" =~ ^[1-9][0-9]*$ ]]; then
    receipt "pr.sh open: create returned no pull request number"
    return 1
  fi
  gh_local auto-merge pr merge "$number" --repo "$PR_REPO" --auto --merge || return $?
  printf '%s\n' "$number"
}

case "${1:-}" in
  open) shift; pr_open_main "$@" ;;
  *) receipt "usage: pr.sh open --head HEAD --title TITLE [--body-file FILE]"; exit 2 ;;
esac

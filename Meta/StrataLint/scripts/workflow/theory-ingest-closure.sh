#!/usr/bin/env bash
set -euo pipefail
repository="${1:-.}"
shift $(( $# > 0 ? 1 : 0 ))
excluded=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --exclude)
      [[ $# -ge 2 ]] || { echo "usage: $0 REPOSITORY [--exclude PATH ...]" >&2; exit 2; }
      excluded+=("$2"); shift 2 ;;
    *) echo "usage: $0 REPOSITORY [--exclude PATH ...]" >&2; exit 2 ;;
  esac
done
cd "$repository"
status_args=(--porcelain)
if [[ ${#excluded[@]} -gt 0 ]]; then
  status_args+=(-- .)
  for path in "${excluded[@]}"; do status_args+=(":!$path"); done
fi
changed="$(git status "${status_args[@]}")"
if [[ -z "$changed" ]]; then exit 0; fi
count="$(printf '%s\n' "$changed" | sed '/^$/d' | wc -l | tr -d ' ')"
printf '%s\n' "::error::THEORY-INGEST-CLOSURE-001: ${count} path(s) not closed; run make ingest and commit its output" >&2
printf '%s\n' "$changed" >&2
exit 1

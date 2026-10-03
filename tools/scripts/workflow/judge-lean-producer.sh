#!/usr/bin/env bash
set -euo pipefail
[[ $# == 1 && -n "$1" ]] || { echo 'judge-lean-producer: BUNDLE_DIRECTORY is required' >&2; exit 2; }
if [[ ! -d "$1" ]]; then
  echo 'JUDGE_LEAN_PRODUCER fallback reason=bundle-absent' >&2
  exit 0
fi
bundle="$(cd "$1" && pwd -P)"
producer="$bundle/StrataLint.Lean.dll"
for suffix in dll deps.json runtimeconfig.json; do
  if [[ ! -f "$bundle/StrataLint.Lean.$suffix" ]]; then
    echo 'JUDGE_LEAN_PRODUCER fallback reason=bundle-incomplete' >&2
    exit 0
  fi
done
# The leaf's existing input-failure contract proves that the host loaded the
# executable and its dependencies. A broken bundle leaves normal production.
status=0
message="$(dotnet "$producer" 2>&1)" || status=$?
if [[ "$status" == 2 && "$message" == 'LEAN_PRODUCER_FAILED expected lean-utility-input, ensure-cache, with-cache-reader or with-cache-writer' ]]; then
  echo 'JUDGE_LEAN_PRODUCER reused' >&2
  printf '%s\n' "$producer"
else
  echo 'JUDGE_LEAN_PRODUCER fallback reason=bundle-not-runnable' >&2
fi

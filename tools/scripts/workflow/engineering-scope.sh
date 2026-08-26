#!/bin/bash
set -euo pipefail

repository=""
mode=""
result_file=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository)
      [[ $# -ge 2 ]] || { echo "engineering-scope: --repository requires a value" >&2; exit 2; }
      repository="$2"
      shift 2
      ;;
    --mode)
      [[ $# -ge 2 ]] || { echo "engineering-scope: --mode requires a value" >&2; exit 2; }
      mode="$2"
      shift 2
      ;;
    --result-file)
      [[ $# -ge 2 ]] || { echo "engineering-scope: --result-file requires a value" >&2; exit 2; }
      result_file="$2"
      shift 2
      ;;
    *)
      echo "engineering-scope: unknown argument '$1'" >&2
      exit 2
      ;;
  esac
done

[[ -n "$repository" && -d "$repository" ]] \
  || { echo "engineering-scope: --repository must name a directory" >&2; exit 2; }
[[ -n "$result_file" ]] \
  || { echo "engineering-scope: --result-file is required" >&2; exit 2; }

run=""
decision=""
reason=""
base_sha="not-applicable"
head_sha="not-applicable"
changed_count=0
disjoint_count=0

case "$mode" in
  push)
    ;;
  pull-request)
    head_sha="$(git -C "$repository" rev-parse HEAD)"
    base_sha="$(git -C "$repository" rev-parse HEAD^1)"
    changed_file="$(mktemp "${TMPDIR:-/tmp}/engineering-scope-paths.XXXXXXXX")"
    trap 'rm -f -- "$changed_file"' EXIT
    git -C "$repository" diff --name-only -z --no-renames --diff-filter=ACDMRTUXB \
      "$base_sha" "$head_sha" -- > "$changed_file"

    while IFS= read -r -d '' path; do
      ((changed_count += 1))
      classification="engineering"
      case "$path" in
        Meta/Digestion/*|docs/*|Golden/Frozen/*)
          ((disjoint_count += 1))
          classification="disjoint"
          ;;
      esac
      printf 'ENGINEERING_SCOPE_CHANGED %q classification=%s\n' "$path" "$classification"
    done < "$changed_file"

    ;;
  *)
    echo "engineering-scope: --mode must be pull-request or push" >&2
    exit 2
    ;;
esac

if [[ "$mode" == "push" ]]; then
  run="true"
  decision="full"
  reason="dev push always runs the full engineering check"
elif [[ "$changed_count" -gt 0 && "$changed_count" -eq "$disjoint_count" ]]; then
  run="false"
  decision="none"
  reason="all changed paths are in the base-owned disjoint whitelist"
elif [[ "$changed_count" -eq 0 ]]; then
  run="true"
  decision="full"
  reason="empty delta fails closed to the full engineering check"
else
  run="true"
  decision="full"
  reason="at least one changed path requires the full engineering check"
fi

printf 'ENGINEERING_SCOPE mode=%s decision=%s run=%s base=%s head=%s changed=%s disjoint=%s reason=%s\n' \
  "$mode" "$decision" "$run" "$base_sha" "$head_sha" "$changed_count" "$disjoint_count" "$reason"

temporary_result="$result_file.tmp.$$"
trap 'rm -f -- "${changed_file:-}" "$temporary_result"' EXIT
{
  printf 'event=%s\n' "$mode"
  printf 'decision=%s\n' "$decision"
  printf 'run=%s\n' "$run"
  printf 'base_sha=%s\n' "$base_sha"
  printf 'head_sha=%s\n' "$head_sha"
  printf 'changed_count=%s\n' "$changed_count"
  printf 'matched_count=%s\n' "$disjoint_count"
  printf 'disjoint_count=%s\n' "$disjoint_count"
  printf 'reason=%s\n' "$reason"
} > "$temporary_result"
mv -f -- "$temporary_result" "$result_file"

#!/usr/bin/env bash
set -uo pipefail

readonly bad_argument_code=2
readonly history_unavailable_code=3
readonly no_changes_code=4
readonly not_inverse_code=5
readonly path_outside_allowlist_code=6
readonly ambiguous_target_code=7
readonly second_parent_code=8
readonly classifier_modified_code=9
readonly git_failure_code=10

fail() {
  local reason="$1" code="$2"
  printf '%s\n' "$reason" >&2
  exit "$code"
}

if (( $# < 1 || $# > 2 )); then
  fail PURE_REVERT_BAD_ARGUMENT "$bad_argument_code"
fi

repository="$1"
target_hint="${2:-}"
if [[ ! -d "$repository" ]]; then
  fail PURE_REVERT_BAD_ARGUMENT "$bad_argument_code"
fi

repository_root="$(git -C "$repository" rev-parse --show-toplevel 2>/dev/null)" \
  || fail PURE_REVERT_BAD_ARGUMENT "$bad_argument_code"
physical_repository="$(cd "$repository" 2>/dev/null && pwd -P)" \
  || fail PURE_REVERT_BAD_ARGUMENT "$bad_argument_code"
physical_root="$(cd "$repository_root" 2>/dev/null && pwd -P)" \
  || fail PURE_REVERT_BAD_ARGUMENT "$bad_argument_code"
if [[ "$physical_repository" != "$physical_root" ]]; then
  fail PURE_REVERT_BAD_ARGUMENT "$bad_argument_code"
fi
repository="$physical_root"

shallow="$(git -C "$repository" rev-parse --is-shallow-repository 2>/dev/null)" \
  || fail PURE_REVERT_GIT_FAILURE "$git_failure_code"
if [[ "$shallow" != false ]]; then
  fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
fi

head_sha="$(git -C "$repository" rev-parse --verify 'HEAD^{commit}' 2>/dev/null)" \
  || fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
base_sha="$(git -C "$repository" rev-parse --verify 'HEAD^1^{commit}' 2>/dev/null)" \
  || fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
head_parents="$(git -C "$repository" rev-list --parents -n 1 "$head_sha" 2>/dev/null)" \
  || fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
read -r _head_parent_record _head_first_parent _head_second_parent _head_extra \
  <<< "$head_parents"
if [[ -z "${_head_second_parent:-}" || "${_head_first_parent:-}" != "$base_sha" ]]; then
  fail PURE_REVERT_BAD_ARGUMENT "$bad_argument_code"
fi

readonly protection_policy_path='tools/StrataLint.Engine/Admission/BootstrapProtectionPolicy.cs'
protection_policy="$(
  git -C "$repository" show "$base_sha:$protection_policy_path" 2>/dev/null
)" || fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"

policy_prefix() {
  local matcher_id="$1" matches count prefix
  matches="$(
    printf '%s\n' "$protection_policy" \
      | sed -nE \
        "s/.*Atom\(\"${matcher_id}\",[[:space:]]*ProtectionMatchKind\.Prefix,[[:space:]]*\"([^\"]+)\"\).*/\1/p"
  )" || return 1
  count="$(printf '%s\n' "$matches" | awk 'NF { count += 1 } END { print count + 0 }')" \
    || return 1
  [[ "$count" == 1 ]] || return 1
  prefix="$matches"
  [[ "$prefix" == */ && "$prefix" != /* && "$prefix" != *../* ]] || return 1
  printf '%s' "$prefix"
}

tools_prefix="$(policy_prefix tools)" \
  || fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
workflows_prefix="$(policy_prefix workflows)" \
  || fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
if [[ "$tools_prefix" == "$workflows_prefix" ]]; then
  fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
fi

scratch="$(mktemp -d "${TMPDIR:-/tmp}/pure-revert-detect.XXXXXX")" \
  || fail PURE_REVERT_GIT_FAILURE "$git_failure_code"
cleanup() {
  rm -rf -- "$scratch"
}
trap cleanup EXIT HUP INT TERM

candidate_raw="$scratch/candidate.raw"
if ! git -C "$repository" diff-tree -r --no-commit-id --raw -z \
  --no-renames --no-abbrev "$base_sha" "$head_sha" > "$candidate_raw" 2>/dev/null; then
  fail PURE_REVERT_GIT_FAILURE "$git_failure_code"
fi

candidate_paths=()
candidate_old_modes=()
candidate_new_modes=()
candidate_old_oids=()
candidate_new_oids=()
parse_candidate_diff() {
  local header path existing_index
  while IFS= read -r -d '' header; do
    IFS= read -r -d '' path || return 1
    if [[ ! "$header" =~ ^:([0-7]{6})\ ([0-7]{6})\ ([0-9a-f]+)\ ([0-9a-f]+)\ ([A-Z])$ ]]; then
      return 1
    fi
    for (( existing_index = 0;
      existing_index < ${#candidate_paths[@]};
      existing_index++ )); do
      [[ "${candidate_paths[existing_index]}" != "$path" ]] || return 1
    done
    candidate_paths+=("$path")
    candidate_old_modes+=("${BASH_REMATCH[1]}")
    candidate_new_modes+=("${BASH_REMATCH[2]}")
    candidate_old_oids+=("${BASH_REMATCH[3]}")
    candidate_new_oids+=("${BASH_REMATCH[4]}")
  done < "$candidate_raw"
}
parse_candidate_diff \
  || fail PURE_REVERT_GIT_FAILURE "$git_failure_code"

changed_path_count="${#candidate_paths[@]}"
if (( changed_path_count == 0 )); then
  fail PURE_REVERT_NO_CHANGES "$no_changes_code"
fi

readonly classifier_path='tools/scripts/workflow/pure-revert-detect.sh'
is_allowed_path() {
  local path="$1"
  [[ "$path" == "$tools_prefix"* || "$path" == "$workflows_prefix"* ]]
}

for path in "${candidate_paths[@]}"; do
  if [[ "$path" == "$classifier_path" ]]; then
    fail PURE_REVERT_CLASSIFIER_MODIFIED "$classifier_modified_code"
  fi
  is_allowed_path "$path" \
    || fail PURE_REVERT_PATH_OUTSIDE_ALLOWLIST "$path_outside_allowlist_code"
done

target_raw="$scratch/target.raw"
exact_inverse_of() {
  local commit="$1" parent="$2"
  local header path existing_index candidate_index target_index found
  local -a target_paths=()
  local -a target_old_modes=()
  local -a target_new_modes=()
  local -a target_old_oids=()
  local -a target_new_oids=()

  if ! git -C "$repository" diff-tree -r --no-commit-id --raw -z \
    --no-renames --no-abbrev "$parent" "$commit" > "$target_raw" 2>/dev/null; then
    return 2
  fi
  while IFS= read -r -d '' header; do
    IFS= read -r -d '' path || return 2
    if [[ ! "$header" =~ ^:([0-7]{6})\ ([0-7]{6})\ ([0-9a-f]+)\ ([0-9a-f]+)\ ([A-Z])$ ]]; then
      return 2
    fi
    for (( existing_index = 0;
      existing_index < ${#target_paths[@]};
      existing_index++ )); do
      [[ "${target_paths[existing_index]}" != "$path" ]] || return 2
    done
    target_paths+=("$path")
    target_old_modes+=("${BASH_REMATCH[1]}")
    target_new_modes+=("${BASH_REMATCH[2]}")
    target_old_oids+=("${BASH_REMATCH[3]}")
    target_new_oids+=("${BASH_REMATCH[4]}")
  done < "$target_raw"

  (( ${#target_paths[@]} == changed_path_count )) || return 1
  for (( candidate_index = 0; candidate_index < changed_path_count; candidate_index++ )); do
    found=0
    for (( target_index = 0; target_index < ${#target_paths[@]}; target_index++ )); do
      [[ "${candidate_paths[candidate_index]}" == "${target_paths[target_index]}" ]] \
        || continue
      found=1
      [[ "${candidate_new_modes[candidate_index]}" == "${target_old_modes[target_index]}" \
        && "${candidate_new_oids[candidate_index]}" == "${target_old_oids[target_index]}" \
        && "${candidate_old_modes[candidate_index]}" == "${target_new_modes[target_index]}" \
        && "${candidate_old_oids[candidate_index]}" == "${target_new_oids[target_index]}" ]] \
        || return 1
      break
    done
    (( found == 1 )) || return 1
  done
  return 0
}

first_parent_history="$scratch/first-parent-history"
if ! git -C "$repository" rev-list --first-parent "$base_sha" \
  > "$first_parent_history" 2>/dev/null; then
  fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
fi

candidate_commits="$scratch/candidate-commits"
if ! git -C "$repository" --literal-pathspecs rev-list --first-parent \
  "$base_sha" -- "${candidate_paths[@]}" > "$candidate_commits" 2>/dev/null; then
  fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
fi

matching_targets=()
while IFS= read -r commit; do
  [[ -n "$commit" ]] || continue
  parent_record="$(git -C "$repository" rev-list --parents -n 1 "$commit" 2>/dev/null)" \
    || fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
  read -r listed_commit first_parent _other_parents <<< "$parent_record"
  [[ "$listed_commit" == "$commit" ]] \
    || fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
  [[ -n "${first_parent:-}" ]] || continue
  exact_inverse_of "$commit" "$first_parent"
  inverse_status=$?
  if (( inverse_status == 0 )); then
    matching_targets+=("$commit")
  elif (( inverse_status == 2 )); then
    fail PURE_REVERT_GIT_FAILURE "$git_failure_code"
  fi
done < "$candidate_commits"

if (( ${#matching_targets[@]} > 1 )); then
  fail PURE_REVERT_AMBIGUOUS_TARGET "$ambiguous_target_code"
fi
if (( ${#matching_targets[@]} == 1 )); then
  printf 'PURE_REVERT_TRUE base_sha=%s head_sha=%s target_merge_sha=%s changed_path_count=%s\n' \
    "$base_sha" "$head_sha" "${matching_targets[0]}" "$changed_path_count"
  exit 0
fi

# A hint never selects the target. It can only explain an independently rejected
# exact inverse as a second-parent transition.
if [[ -n "$target_hint" && "$target_hint" != *[!0-9A-Fa-f]* ]]; then
  resolved_hint="$(
    git -C "$repository" rev-parse --verify "${target_hint}^{commit}" 2>/dev/null
  )" || resolved_hint=''
  if [[ -n "$resolved_hint" ]]; then
    hint_on_first_parent=0
    while IFS= read -r commit; do
      if [[ "$commit" == "$resolved_hint" ]]; then
        hint_on_first_parent=1
        break
      fi
    done < "$first_parent_history"
    git -C "$repository" merge-base --is-ancestor "$resolved_hint" "$base_sha" \
      >/dev/null 2>&1
    ancestor_status=$?
    if (( ancestor_status > 1 )); then
      fail PURE_REVERT_GIT_FAILURE "$git_failure_code"
    fi
    if (( ancestor_status == 0 && hint_on_first_parent == 0 )); then
      hint_parent_record="$(
        git -C "$repository" rev-list --parents -n 1 "$resolved_hint" 2>/dev/null
      )" || fail PURE_REVERT_HISTORY_UNAVAILABLE "$history_unavailable_code"
      read -r listed_hint hint_first_parent _hint_other_parents <<< "$hint_parent_record"
      if [[ "$listed_hint" == "$resolved_hint" && -n "${hint_first_parent:-}" ]]; then
        exact_inverse_of "$resolved_hint" "$hint_first_parent"
        hint_inverse_status=$?
        if (( hint_inverse_status == 0 )); then
          fail PURE_REVERT_SECOND_PARENT "$second_parent_code"
        elif (( hint_inverse_status == 2 )); then
          fail PURE_REVERT_GIT_FAILURE "$git_failure_code"
        fi
      fi
    fi
  fi
fi

fail PURE_REVERT_NOT_INVERSE "$not_inverse_code"

#!/usr/bin/env bash
set -euo pipefail

scratch_root=""
WRITE_PATTERNS=()
WRITE_PATHSPECS=()

cleanup() {
  if [[ -n "$scratch_root" && -d "$scratch_root" ]]; then
    find "$scratch_root" -depth -delete
  fi
}
trap cleanup EXIT

fail() {
  printf '%s\n' "::error::THEORY-INGEST-CLOSURE-001: $*" >&2
  exit 1
}

usage() {
  printf '%s\n' \
    "usage: $0 propose REPOSITORY BASE_REVISION PROPOSAL_PATCH" \
    "       $0 authorize PROPOSAL_PATCH TRUSTED_PATCH" \
    "       $0 validate REPOSITORY BASE_REVISION PATCH" \
    "       $0 writeback REPOSITORY CANDIDATE_DATA PROPOSAL_PATCH BASE_SHA HEAD_SHA HEAD_REF REMOTE_URL" >&2
  exit 2
}

ensure_scratch() {
  if [[ -z "$scratch_root" ]]; then
    scratch_root="$(mktemp -d "${TMPDIR:-/tmp}/theory-ingest-closure.XXXXXXXX")"
  fi
}

load_producer_write_patterns() {
  local repository="$1"
  local output
  if ! output="$(dotnet run --no-build \
      --project "$repository/tools/StrataLint.Cli/StrataLint.Cli.csproj" \
      --configuration Release -- filemap-conform --producer-write-set IngestCommand)"; then
    fail "cannot derive IngestCommand committed write set"
  fi

  WRITE_PATTERNS=()
  WRITE_PATHSPECS=()
  local pattern
  while IFS= read -r pattern; do
    [[ -n "$pattern" ]] || fail \
      "IngestCommand committed write set contains an empty pattern"
    WRITE_PATTERNS+=("$pattern")
    WRITE_PATHSPECS+=(":(glob)$pattern")
  done <<< "$output"
  [[ "${#WRITE_PATHSPECS[@]}" -gt 0 ]] || fail \
    "IngestCommand has no committed FILEMAP write set"
}

initialize_index() {
  local repository="$1"
  local revision="$2"
  local index_path="$3"
  rm -f -- "$index_path"
  GIT_INDEX_FILE="$index_path" git -C "$repository" read-tree "$revision"
}

stage_declared_outputs() {
  local repository="$1"
  local revision="$2"
  local index_path="$3"
  initialize_index "$repository" "$revision" "$index_path"
  GIT_INDEX_FILE="$index_path" git -C "$repository" add -f -A -- "${WRITE_PATHSPECS[@]}"
}

write_index_patch() {
  local repository="$1"
  local revision="$2"
  local index_path="$3"
  local output_path="$4"
  mkdir -p -- "$(dirname "$output_path")"
  GIT_INDEX_FILE="$index_path" git -C "$repository" diff --cached \
    --binary --full-index --no-color --no-ext-diff --no-renames \
    "$revision" -- "${WRITE_PATHSPECS[@]}" > "$output_path"
}

canonical_patch_path() {
  local path="$1"
  [[ -n "$path" && "$path" != /* && "$path" != *\\* && "$path" != *//* ]] || return 1
  [[ "$path" != *$'\n'* && "$path" != *$'\r'* && "$path" != *$'\t'* ]] || return 1
  local segment
  IFS='/' read -r -a segments <<< "$path"
  for segment in "${segments[@]}"; do
    [[ -n "$segment" && "$segment" != "." && "$segment" != ".." ]] || return 1
  done
}

validate_patch_into_index() {
  local repository="$1"
  local base_revision="$2"
  local patch_path="$3"
  local index_path="$4"
  [[ -f "$patch_path" ]] || fail \
    "patch does not exist: $patch_path"
  initialize_index "$repository" "$base_revision" "$index_path"
  if [[ ! -s "$patch_path" ]]; then
    return 0
  fi
  if ! GIT_INDEX_FILE="$index_path" git -C "$repository" apply \
      --cached --whitespace=nowarn --binary -- "$patch_path"; then
    fail "patch is not applicable to the pinned base"
  fi

  ensure_scratch
  local raw_path="$scratch_root/raw.$RANDOM"
  local numstat_path="$scratch_root/numstat.$RANDOM"
  local allowed_path="$scratch_root/allowed.$RANDOM"
  GIT_INDEX_FILE="$index_path" git -C "$repository" diff --cached \
    --raw -z --no-renames "$base_revision" > "$raw_path"
  GIT_INDEX_FILE="$index_path" git -C "$repository" diff --cached \
    --numstat -z --no-renames "$base_revision" > "$numstat_path"
  GIT_INDEX_FILE="$index_path" git -C "$repository" ls-files \
    --cached -z -- "${WRITE_PATHSPECS[@]}" > "$allowed_path"

  local path allowed_candidate authorized
  local header old_mode new_mode status
  local changed_count=0
  while IFS= read -r -d '' header && IFS= read -r -d '' path; do
    if [[ ! "$header" =~ ^:([0-7]{6})\ ([0-7]{6})\ ([0-9a-f]+)\ ([0-9a-f]+)\ ([AM])$ ]]; then
      fail \
        "patch contains delete, rename, copy, type change, or an unmerged entry"
    fi
    old_mode="${BASH_REMATCH[1]}"
    new_mode="${BASH_REMATCH[2]}"
    status="${BASH_REMATCH[5]}"
    if [[ "$new_mode" != "100644" \
        || "$status" == "M" && "$old_mode" != "100644" \
        || "$status" == "A" && "$old_mode" != "000000" ]]; then
      fail \
        "patch changes mode or introduces a symlink/submodule at $path"
    fi
    canonical_patch_path "$path" || fail \
      "patch contains a non-canonical path"
    authorized=false
    while IFS= read -r -d '' allowed_candidate; do
      if [[ "$allowed_candidate" == "$path" ]]; then
        authorized=true
        break
      fi
    done < "$allowed_path"
    [[ "$authorized" == true ]] || fail \
      "patch path is outside the FILEMAP-derived write set: $path"
    changed_count=$((changed_count + 1))
  done < "$raw_path"
  [[ "$changed_count" -gt 0 ]] || fail \
    "non-empty patch changes no index entries"

  local numstat
  while IFS= read -r -d '' numstat; do
    [[ "$numstat" != $'-\t-'* ]] || fail \
      "binary patches are not authorized"
  done < "$numstat_path"
}

authorize_exact_patch() {
  local proposal_patch="$1"
  local trusted_patch="$2"
  [[ -f "$proposal_patch" && -f "$trusted_patch" ]] || fail \
    "proposal or trusted patch is missing"
  cmp -s -- "$proposal_patch" "$trusted_patch" || fail \
    "candidate proposal differs byte-for-byte from the base-owned recomputation"
}

assert_producer_closure_unchanged() {
  local repository="$1"
  local base_sha="$2"
  local head_sha="$3"
  local changed_path
  local bad=()
  while IFS= read -r -d '' changed_path; do
    case "$changed_path" in
      Makefile|tools/StrataLint.*|tools/scripts/*|Meta/FILEMAP.toml|.github/workflows/theory-ingest.yml)
        bad+=("$changed_path")
        ;;
    esac
  done < <(git -C "$repository" diff --name-only -z "$base_sha" "$head_sha")
  if [[ "${#bad[@]}" -ne 0 ]]; then
    printf '%s\n' "${bad[@]}" >&2
    fail "split producer-closure changes from the theory PR"
  fi
}

assert_candidate_theory_is_regular_data() {
  local repository="$1"
  local head_sha="$2"
  local entry metadata path
  while IFS= read -r -d '' entry; do
    metadata="${entry%%$'\t'*}"
    path="${entry#*$'\t'}"
    [[ "$metadata" =~ ^100644\ blob\ [0-9a-f]+$ ]] || fail \
      "candidate theory source is not a regular file: $path"
    canonical_patch_path "$path" || fail \
      "candidate theory source has a non-canonical path"
  done < <(git -C "$repository" ls-tree -r -z "$head_sha" -- docs/develop/theory)
}

replace_final_outputs() {
  local repository="$1"
  local head_sha="$2"
  local recomputed_index="$3"
  local final_index="$4"
  initialize_index "$repository" "$head_sha" "$final_index"

  ensure_scratch
  local head_paths="$scratch_root/head-paths.$RANDOM"
  local recomputed_entries="$scratch_root/recomputed-entries.$RANDOM"
  GIT_INDEX_FILE="$final_index" git -C "$repository" ls-files \
    --cached -z -- "${WRITE_PATHSPECS[@]}" > "$head_paths"
  local path entry metadata mode object stage
  while IFS= read -r -d '' path; do
    GIT_INDEX_FILE="$final_index" git -C "$repository" update-index --force-remove -- "$path"
  done < "$head_paths"

  GIT_INDEX_FILE="$recomputed_index" git -C "$repository" ls-files \
    --stage -z -- "${WRITE_PATHSPECS[@]}" > "$recomputed_entries"
  while IFS= read -r -d '' entry; do
    metadata="${entry%%$'\t'*}"
    path="${entry#*$'\t'}"
    read -r mode object stage <<< "$metadata"
    [[ "$mode" == "100644" && "$stage" == "0" ]] || fail \
      "trusted recomputation produced a non-regular index entry at $path"
    GIT_INDEX_FILE="$final_index" git -C "$repository" update-index \
      --add --cacheinfo "$mode" "$object" "$path"
  done < "$recomputed_entries"
}

propose() {
  [[ "$#" -eq 3 ]] || usage
  local repository="$1"
  local base_revision="$2"
  local proposal_patch="$3"
  git -C "$repository" rev-parse --verify "$base_revision^{commit}" >/dev/null
  load_producer_write_patterns "$repository"
  ensure_scratch
  local proposal_index="$scratch_root/proposal.index"
  local validation_index="$scratch_root/proposal-validation.index"
  stage_declared_outputs "$repository" HEAD "$proposal_index"
  write_index_patch "$repository" "$base_revision" "$proposal_index" "$proposal_patch"
  [[ -s "$proposal_patch" ]] || fail \
    "producer emitted no declared output and the candidate contains no declared closure delta"
  validate_patch_into_index "$repository" "$base_revision" "$proposal_patch" "$validation_index"
  printf '%s\n' "theory ingest proposal written to $proposal_patch"
}

validate_command() {
  [[ "$#" -eq 3 ]] || usage
  local repository="$1"
  local base_revision="$2"
  local patch_path="$3"
  load_producer_write_patterns "$repository"
  ensure_scratch
  validate_patch_into_index "$repository" "$base_revision" "$patch_path" \
    "$scratch_root/validated.index"
}

writeback() {
  [[ "$#" -eq 7 ]] || usage
  local repository="$1"
  local candidate_data="$2"
  local proposal_patch="$3"
  local base_sha="$4"
  local head_sha="$5"
  local head_ref="$6"
  local remote_url="$7"

  [[ "$(git -C "$repository" rev-parse HEAD)" == "$base_sha" ]] || fail \
    "trusted checkout does not equal the event base SHA"
  [[ "$(git -C "$candidate_data" rev-parse HEAD)" == "$head_sha" ]] || fail \
    "candidate data checkout does not equal the event head SHA"
  git -C "$repository" fetch --no-tags "$candidate_data" "$head_sha"
  git -C "$repository" merge-base --is-ancestor "$base_sha" "$head_sha" || fail \
    "event base is not an ancestor of event head"
  assert_producer_closure_unchanged "$repository" "$base_sha" "$head_sha"
  assert_candidate_theory_is_regular_data "$repository" "$head_sha"
  load_producer_write_patterns "$repository"

  rsync -a --delete --exclude='.git' \
    "$candidate_data/docs/develop/theory/" "$repository/docs/develop/theory/"
  make -C "$repository" ingest BASE=HEAD

  ensure_scratch
  local recomputed_index="$scratch_root/recomputed.index"
  local recomputed_patch="$scratch_root/base-to-recomputed.patch"
  local recomputed_validation_index="$scratch_root/recomputed-validation.index"
  local final_index="$scratch_root/final.index"
  local trusted_patch="$scratch_root/trusted.patch"
  local proposal_validation_index="$scratch_root/proposal-validation.index"
  local trusted_validation_index="$scratch_root/trusted-validation.index"

  stage_declared_outputs "$repository" "$base_sha" "$recomputed_index"
  write_index_patch "$repository" "$base_sha" "$recomputed_index" "$recomputed_patch"
  [[ -s "$recomputed_patch" ]] || fail \
    "base-owned producer emitted no declared output for the changed theory source"
  validate_patch_into_index "$repository" "$base_sha" "$recomputed_patch" \
    "$recomputed_validation_index"

  replace_final_outputs "$repository" "$head_sha" "$recomputed_index" "$final_index"
  write_index_patch "$repository" "$head_sha" "$final_index" "$trusted_patch"
  validate_patch_into_index "$repository" "$base_sha" "$proposal_patch" \
    "$proposal_validation_index"
  validate_patch_into_index "$repository" "$head_sha" "$trusted_patch" \
    "$trusted_validation_index"
  authorize_exact_patch "$proposal_patch" "$recomputed_patch"

  if [[ ! -s "$trusted_patch" ]]; then
    printf '%s\n' "theory ingest writeback is a no-op: candidate head is already closed"
    return 0
  fi

  git check-ref-format --branch "$head_ref" >/dev/null || fail \
    "event head ref is not canonical"
  local remote_ref="refs/heads/$head_ref"
  local tree_sha commit_sha
  tree_sha="$(GIT_INDEX_FILE="$final_index" git -C "$repository" write-tree)"
  commit_sha="$(printf '%s\n' 'chore(digestion): auto-ingest theory update' | \
    GIT_AUTHOR_NAME='theory-ingest-bot' \
    GIT_AUTHOR_EMAIL='theory-ingest-bot@users.noreply.github.com' \
    GIT_COMMITTER_NAME='theory-ingest-bot' \
    GIT_COMMITTER_EMAIL='theory-ingest-bot@users.noreply.github.com' \
    git -C "$repository" commit-tree "$tree_sha" -p "$head_sha")"
  git -C "$repository" merge-base --is-ancestor "$head_sha" "$commit_sha" || fail \
    "writeback commit is not a fast-forward child of event head"
  git -C "$repository" push --porcelain \
    --force-with-lease="$remote_ref:$head_sha" \
    "$remote_url" "$commit_sha:$remote_ref"
}

[[ "$#" -ge 1 ]] || usage
command="$1"
shift
case "$command" in
  propose) propose "$@" ;;
  authorize)
    [[ "$#" -eq 2 ]] || usage
    authorize_exact_patch "$1" "$2"
    ;;
  validate) validate_command "$@" ;;
  writeback) writeback "$@" ;;
  *) usage ;;
esac

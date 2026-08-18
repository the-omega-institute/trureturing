#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

theory_ingest_script_directory="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
source "$theory_ingest_script_directory/theory-ingest-github-cas.sh"

scratch_root=""
WRITE_PATTERNS=()
WRITE_PATHSPECS=()
CANDIDATE_INPUT_PATTERNS=()
CANDIDATE_INPUT_PATHSPECS=()
MERGED_TREE_SHA=""
THEORY_TREE_SHA=""
ENVELOPE_BASE_SHA=""
ENVELOPE_HEAD_SHA=""
ENVELOPE_PATCH_SHA256=""
ENVELOPE_REPORT_INPUT_ADDRESS=""
ENVELOPE_REPORT_SHA256=""
ENVELOPE_THEORY_TREE_SHA=""
GITHUB_REMOTE_COMMIT_SHA=""

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
    "usage: $0 guard-inputs REPOSITORY CANDIDATE_DATA BASE_SHA HEAD_SHA" \
    "       $0 prepare REPOSITORY CANDIDATE_DATA BASE_SHA HEAD_SHA ARTIFACT_DIRECTORY" \
    "       $0 validate REPOSITORY BASE_REVISION PATCH" \
    "       $0 writeback REPOSITORY ARTIFACT_DIRECTORY BASE_SHA HEAD_SHA HEAD_REF REMOTE_URL" >&2
  exit 2
}

ensure_scratch() {
  if [[ -z "$scratch_root" ]]; then
    scratch_root="$(mktemp -d "${TMPDIR:-/tmp}/theory-ingest-closure.XXXXXXXX")"
  fi
}

hash_file() {
  local path="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$path" | awk '{print $1}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$path" | awk '{print $NF}'
  else
    shasum -a 256 "$path" | awk '{print $1}'
  fi
}

set_write_patterns() {
  local output="$1"
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

load_producer_write_patterns() {
  local repository="$1"
  local output
  if ! output="$(
      cd "$repository"
      dotnet run --no-build \
        --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
        --configuration Release -- filemap-conform --producer-write-set IngestCommand
    )"; then
    fail "cannot derive IngestCommand committed write set"
  fi
  set_write_patterns "$output"
}

load_pinned_write_patterns() {
  local repository="$1"
  local output
  if ! output="$(python3 - "$repository/Meta/FILEMAP.toml" <<'PY'
import pathlib
import sys
import tomllib

path = pathlib.Path(sys.argv[1])
with path.open("rb") as stream:
    document = tomllib.load(stream)
entries = document.get("files")
if not isinstance(entries, list):
    raise SystemExit("FILEMAP files must be an array")
patterns = []
for entry in entries:
    if not isinstance(entry, dict):
        raise SystemExit("FILEMAP entry must be a table")
    if (entry.get("produced_by") == "IngestCommand"
            and isinstance(entry.get("runtime_disposition"), str)
            and entry["runtime_disposition"].startswith("committed-")):
        pattern = entry.get("pattern")
        if not isinstance(pattern, str) or not pattern:
            raise SystemExit("IngestCommand FILEMAP pattern must be a non-empty string")
        patterns.append(pattern)
if not patterns or patterns != sorted(set(patterns)):
    raise SystemExit("IngestCommand FILEMAP patterns must be non-empty, unique, and sorted")
print("\n".join(patterns))
PY
  )"; then
    fail "pinned-base validator cannot derive the IngestCommand committed write set"
  fi
  set_write_patterns "$output"
}

load_candidate_input_patterns() {
  local repository="$1"
  local output
  if ! output="$(python3 - "$repository/Meta/FILEMAP.toml" <<'PY'
import pathlib
import sys
import tomllib

path = pathlib.Path(sys.argv[1])
with path.open("rb") as stream:
    document = tomllib.load(stream)
entries = document.get("files")
if not isinstance(entries, list):
    raise SystemExit("FILEMAP files must be an array")
patterns = []
for entry in entries:
    if not isinstance(entry, dict):
        raise SystemExit("FILEMAP entry must be a table")
    consumers = entry.get("consumed_by")
    if (entry.get("produced_by") == "none"
            and isinstance(consumers, list)
            and "IngestCommand" in consumers
            and isinstance(entry.get("runtime_disposition"), str)
            and entry["runtime_disposition"].startswith("committed-")):
        pattern = entry.get("pattern")
        if not isinstance(pattern, str) or not pattern:
            raise SystemExit("IngestCommand FILEMAP input pattern must be a non-empty string")
        patterns.append(pattern)
if not patterns or patterns != sorted(set(patterns)):
    raise SystemExit("IngestCommand FILEMAP input patterns must be non-empty, unique, and sorted")
print("\n".join(patterns))
PY
  )"; then
    fail "cannot derive the candidate data set from pinned-base FILEMAP"
  fi

  CANDIDATE_INPUT_PATTERNS=()
  CANDIDATE_INPUT_PATHSPECS=()
  local pattern
  while IFS= read -r pattern; do
    [[ -n "$pattern" ]] || fail "FILEMAP candidate data set contains an empty pattern"
    CANDIDATE_INPUT_PATTERNS+=("$pattern")
    CANDIDATE_INPUT_PATHSPECS+=(":(glob)$pattern")
  done <<< "$output"
  [[ "${#CANDIDATE_INPUT_PATHSPECS[@]}" -gt 0 ]] || fail \
    "FILEMAP declares no candidate data consumed by IngestCommand"
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
  [[ -f "$patch_path" ]] || fail "patch does not exist: $patch_path"
  initialize_index "$repository" "$base_revision" "$index_path"
  if [[ ! -s "$patch_path" ]]; then
    return 0
  fi
  if ! GIT_INDEX_FILE="$index_path" git -C "$repository" apply \
      --cached --whitespace=nowarn --binary -- "$patch_path"; then
    fail "patch is not applicable to the pinned event head"
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
      fail "patch contains delete, rename, copy, type change, or an unmerged entry"
    fi
    old_mode="${BASH_REMATCH[1]}"
    new_mode="${BASH_REMATCH[2]}"
    status="${BASH_REMATCH[5]}"
    if [[ "$new_mode" != "100644" \
        || "$status" == "M" && "$old_mode" != "100644" \
        || "$status" == "A" && "$old_mode" != "000000" ]]; then
      fail "patch changes mode or introduces a symlink/submodule at $path"
    fi
    canonical_patch_path "$path" || fail "patch contains a non-canonical path"
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
  [[ "$changed_count" -gt 0 ]] || fail "non-empty patch changes no index entries"

  local numstat
  while IFS= read -r -d '' numstat; do
    [[ "$numstat" != $'-\t-'* ]] || fail "binary patches are not authorized"
  done < "$numstat_path"
}

assert_report_input_closure_unchanged() {
  local repository="$1"
  local candidate_data="$2"
  local fork_sha="$3"
  local head_sha="$4"
  load_candidate_input_patterns "$repository"
  ensure_scratch
  local allowed_path="$scratch_root/candidate-inputs.$RANDOM"
  git -C "$candidate_data" diff --name-only -z "$fork_sha" "$head_sha" -- \
    "${CANDIDATE_INPUT_PATHSPECS[@]}" > "$allowed_path"
  local changed_path
  local bad=()
  while IFS= read -r -d '' changed_path; do
    local allowed_candidate authorized=false
    while IFS= read -r -d '' allowed_candidate; do
      if [[ "$allowed_candidate" == "$changed_path" ]]; then
        authorized=true
        break
      fi
    done < "$allowed_path"
    [[ "$authorized" == true ]] || bad+=("$changed_path")
  done < <(git -C "$candidate_data" diff --name-only -z "$fork_sha" "$head_sha")
  if [[ "${#bad[@]}" -ne 0 ]]; then
    printf '%s\n' "${bad[@]}" >&2
    fail "event head changes the trusted Lean-report input closure; split the theory-only PR"
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

resolve_candidate_authority() {
  local repository="$1"
  local candidate_data="$2"
  local base_sha="$3"
  local head_sha="$4"
  [[ "$(git -C "$repository" rev-parse HEAD)" == "$base_sha" ]] || fail \
    "trusted checkout does not equal the event base SHA"
  [[ "$(git -C "$candidate_data" rev-parse HEAD)" == "$head_sha" ]] || fail \
    "candidate data checkout does not equal the event head SHA"
  git -C "$candidate_data" cat-file -e "$base_sha^{commit}" || fail \
    "candidate data checkout does not contain the event base"

  local fork_sha
  if ! fork_sha="$(git -C "$candidate_data" merge-base "$base_sha" "$head_sha")" \
      || [[ -z "$fork_sha" ]]; then
    fail "cannot resolve the immutable fork point of event base and head"
  fi
  assert_report_input_closure_unchanged \
    "$repository" "$candidate_data" "$fork_sha" "$head_sha"
  assert_candidate_theory_is_regular_data "$candidate_data" "$head_sha"
  if ! MERGED_TREE_SHA="$(git -C "$candidate_data" merge-tree \
      --write-tree "$base_sha" "$head_sha")" \
      || [[ ! "$MERGED_TREE_SHA" =~ ^[0-9a-f]+$ ]]; then
    fail "event base and head do not have a conflict-free merge result"
  fi
  if ! THEORY_TREE_SHA="$(git -C "$candidate_data" rev-parse \
      "$MERGED_TREE_SHA:docs/develop/theory")" \
      || [[ ! "$THEORY_TREE_SHA" =~ ^[0-9a-f]+$ ]]; then
    fail "cannot resolve the merged candidate theory tree"
  fi
}

apply_merged_theory_delta() {
  local repository="$1"
  local object_repository="$2"
  local base_sha="$3"
  local merged_tree_sha="$4"
  ensure_scratch
  local theory_patch="$scratch_root/merged-theory.$RANDOM.patch"
  git -C "$object_repository" diff \
    --binary --full-index --no-color --no-ext-diff --no-renames \
    "$base_sha" "$merged_tree_sha" -- docs/develop/theory > "$theory_patch"
  [[ -s "$theory_patch" ]] || fail \
    "candidate merge result contains no theory delta from the event base"
  if ! git -C "$repository" apply \
      --index --whitespace=nowarn --binary -- "$theory_patch"; then
    fail "candidate merge-result theory delta does not apply to the event base"
  fi
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

resolve_report_authority() {
  local repository="$1"
  local report="$2"
  local helper="$repository/tools/scripts/report/lean-report-input.sh"
  [[ -x "$helper" ]] || fail "trusted Lean report input helper is unavailable"
  [[ -s "$report" ]] || fail "trusted canonical Lean report is unavailable"
  "$helper" verify --repository "$repository" --report "$report" || fail \
    "trusted canonical Lean report failed input verification"
  local address producer_sha256 sources_sha256 config_sha256
  read -r address producer_sha256 sources_sha256 config_sha256 \
    <<< "$("$helper" address --repository "$repository")"
  [[ "$address" =~ ^[0-9a-f]{64}$ \
    && "$producer_sha256" =~ ^[0-9a-f]{64}$ \
    && "$sources_sha256" =~ ^[0-9a-f]{64}$ \
    && "$config_sha256" =~ ^[0-9a-f]{64}$ ]] || fail \
      "trusted Lean report input address is malformed"
  REPORT_INPUT_ADDRESS="sha256:$address"
  REPORT_SHA256="$(hash_file "$report")"
  [[ "$REPORT_SHA256" =~ ^[0-9a-f]{64}$ ]] || fail \
    "trusted Lean report SHA is malformed"
}

write_envelope() {
  local envelope="$1"
  local base_sha="$2"
  local head_sha="$3"
  local theory_tree_sha="$4"
  local report_input_address="$5"
  local report_sha256="$6"
  local patch_sha256="$7"
  python3 - \
    "$envelope" "$base_sha" "$head_sha" "$theory_tree_sha" \
    "$report_input_address" "$report_sha256" "$patch_sha256" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
document = {
    "base_sha": sys.argv[2],
    "head_sha": sys.argv[3],
    "theory_tree_sha": sys.argv[4],
    "report_input_address": sys.argv[5],
    "report_sha256": sys.argv[6],
    "patch_sha256": sys.argv[7],
}
path.write_bytes(
    (json.dumps(document, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n")
    .encode("ascii"))
PY
}

write_envelope_digest() {
  local envelope="$1"
  local digest_path="${envelope}.sha256"
  printf '%s  %s\n' "$(hash_file "$envelope")" "$(basename "$envelope")" > "$digest_path"
}

verify_artifact_envelope() {
  local artifact_directory="$1"
  local envelope="$artifact_directory/theory-ingest-envelope.json"
  local digest_path="${envelope}.sha256"
  [[ -s "$envelope" && -s "$digest_path" ]] || fail \
    "trusted artifact envelope or envelope digest is missing"
  local actual_digest expected_line
  actual_digest="$(hash_file "$envelope")"
  expected_line="$actual_digest  $(basename "$envelope")"
  [[ "$(cat "$digest_path")" == "$expected_line" ]] || fail \
    "trusted artifact envelope digest does not match"

  local values
  if ! values="$(python3 - "$envelope" <<'PY'
import json
import pathlib
import re
import sys

path = pathlib.Path(sys.argv[1])
raw = path.read_bytes()
try:
    text = raw.decode("ascii")
except UnicodeDecodeError as error:
    raise SystemExit(f"envelope is not ASCII: {error}")

def reject_duplicates(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate key: {key}")
        result[key] = value
    return result

try:
    document = json.loads(text, object_pairs_hook=reject_duplicates)
except (json.JSONDecodeError, ValueError) as error:
    raise SystemExit(f"invalid envelope JSON: {error}")
keys = {
    "base_sha",
    "head_sha",
    "patch_sha256",
    "report_input_address",
    "report_sha256",
    "theory_tree_sha",
}
if not isinstance(document, dict) or set(document) != keys:
    raise SystemExit("envelope keys are not the exact authority contract")
if any(not isinstance(value, str) for value in document.values()):
    raise SystemExit("envelope values must all be strings")
oid = re.compile(r"^[0-9a-f]{40,64}$")
sha256 = re.compile(r"^[0-9a-f]{64}$")
if not oid.fullmatch(document["base_sha"]):
    raise SystemExit("base_sha is malformed")
if not oid.fullmatch(document["head_sha"]):
    raise SystemExit("head_sha is malformed")
if not oid.fullmatch(document["theory_tree_sha"]):
    raise SystemExit("theory_tree_sha is malformed")
if not sha256.fullmatch(document["patch_sha256"]):
    raise SystemExit("patch_sha256 is malformed")
if not sha256.fullmatch(document["report_sha256"]):
    raise SystemExit("report_sha256 is malformed")
if not re.fullmatch(r"sha256:[0-9a-f]{64}", document["report_input_address"]):
    raise SystemExit("report_input_address is malformed")
canonical = (
    json.dumps(document, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n"
).encode("ascii")
if raw != canonical:
    raise SystemExit("envelope does not use canonical envelope bytes")
print("\t".join(document[key] for key in (
    "base_sha",
    "head_sha",
    "patch_sha256",
    "report_input_address",
    "report_sha256",
    "theory_tree_sha",
)))
PY
  )"; then
    fail "trusted artifact does not contain canonical envelope bytes"
  fi
  IFS=$'\t' read -r \
    ENVELOPE_BASE_SHA \
    ENVELOPE_HEAD_SHA \
    ENVELOPE_PATCH_SHA256 \
    ENVELOPE_REPORT_INPUT_ADDRESS \
    ENVELOPE_REPORT_SHA256 \
    ENVELOPE_THEORY_TREE_SHA <<< "$values"
}

copy_report() {
  local source="$1"
  local target="$2"
  mkdir -p -- "$(dirname "$target")"
  local suffix
  for suffix in '' .sha256 .input.attestation .provenance.json; do
    [[ -s "${source}${suffix}" ]] || fail \
      "trusted canonical Lean report sidecar is missing: ${source}${suffix}"
    cp "${source}${suffix}" "${target}${suffix}"
  done
}

self_verify_preparation() {
  local repository="$1"
  local candidate_data="$2"
  local base_sha="$3"
  local head_sha="$4"
  local merged_tree_sha="$5"
  local report="$6"
  local expected_report_input_address="$7"
  local expected_report_sha256="$8"
  local expected_patch_sha256="$9"
  ensure_scratch
  local verify_repository="$scratch_root/self-verify"
  git clone -q --no-hardlinks "$repository" "$verify_repository"
  git -C "$verify_repository" checkout -q --detach "$base_sha"
  git -C "$verify_repository" fetch -q --no-tags "$candidate_data" "$head_sha"
  local verify_report="$verify_repository/.lake/build/stratalint/raw-lean-report.json"
  copy_report "$report" "$verify_report"
  apply_merged_theory_delta \
    "$verify_repository" "$candidate_data" "$base_sha" "$merged_tree_sha"
  make -C "$verify_repository" ingest BASE=HEAD

  local recomputed_index="$scratch_root/self-recomputed.index"
  local final_index="$scratch_root/self-final.index"
  local patch="$scratch_root/self-final.patch"
  stage_declared_outputs "$verify_repository" "$base_sha" "$recomputed_index"
  replace_final_outputs "$verify_repository" "$head_sha" "$recomputed_index" "$final_index"
  write_index_patch "$verify_repository" "$head_sha" "$final_index" "$patch"
  [[ "$(hash_file "$patch")" == "$expected_patch_sha256" ]] || fail \
    "self-verification patch differs from the canonical envelope"

  resolve_report_authority "$verify_repository" "$verify_report"
  [[ "$REPORT_INPUT_ADDRESS" == "$expected_report_input_address" ]] || fail \
    "self-verification report input address differs from the canonical envelope"
  [[ "$REPORT_SHA256" == "$expected_report_sha256" ]] || fail \
    "self-verification report SHA differs from the canonical envelope"
}

guard_inputs() {
  [[ "$#" -eq 4 ]] || usage
  resolve_candidate_authority "$1" "$2" "$3" "$4"
}

prepare() {
  [[ "$#" -eq 5 ]] || usage
  local repository="$1"
  local candidate_data="$2"
  local base_sha="$3"
  local head_sha="$4"
  local artifact_directory="$5"
  resolve_candidate_authority "$repository" "$candidate_data" "$base_sha" "$head_sha"

  local report="$repository/.lake/build/stratalint/raw-lean-report.json"
  resolve_report_authority "$repository" "$report"
  local report_input_address="$REPORT_INPUT_ADDRESS"
  local report_sha256="$REPORT_SHA256"
  load_producer_write_patterns "$repository"
  git -C "$repository" fetch -q --no-tags "$candidate_data" "$head_sha"
  apply_merged_theory_delta \
    "$repository" "$candidate_data" "$base_sha" "$MERGED_TREE_SHA"
  make -C "$repository" ingest BASE=HEAD

  ensure_scratch
  local recomputed_index="$scratch_root/recomputed.index"
  local final_index="$scratch_root/final.index"
  local validation_index="$scratch_root/validation.index"
  local patch="$artifact_directory/theory-ingest.patch"
  local envelope="$artifact_directory/theory-ingest-envelope.json"
  mkdir -p -- "$artifact_directory"
  stage_declared_outputs "$repository" "$base_sha" "$recomputed_index"
  replace_final_outputs "$repository" "$head_sha" "$recomputed_index" "$final_index"
  write_index_patch "$repository" "$head_sha" "$final_index" "$patch"
  validate_patch_into_index "$repository" "$head_sha" "$patch" "$validation_index"
  local patch_sha256
  patch_sha256="$(hash_file "$patch")"
  write_envelope \
    "$envelope" "$base_sha" "$head_sha" "$THEORY_TREE_SHA" \
    "$report_input_address" "$report_sha256" "$patch_sha256"
  write_envelope_digest "$envelope"
  verify_artifact_envelope "$artifact_directory"
  [[ "$ENVELOPE_BASE_SHA" == "$base_sha" \
    && "$ENVELOPE_HEAD_SHA" == "$head_sha" \
    && "$ENVELOPE_PATCH_SHA256" == "$patch_sha256" \
    && "$ENVELOPE_REPORT_INPUT_ADDRESS" == "$report_input_address" \
    && "$ENVELOPE_REPORT_SHA256" == "$report_sha256" \
    && "$ENVELOPE_THEORY_TREE_SHA" == "$THEORY_TREE_SHA" ]] || fail \
      "fresh canonical envelope does not bind the preparation inputs"
  self_verify_preparation \
    "$repository" "$candidate_data" "$base_sha" "$head_sha" "$MERGED_TREE_SHA" \
    "$report" "$report_input_address" "$report_sha256" "$patch_sha256"
  printf '%s\n' "trusted theory ingest closure written to $artifact_directory"
}

validate_command() {
  [[ "$#" -eq 3 ]] || usage
  local repository="$1"
  local base_revision="$2"
  local patch_path="$3"
  load_producer_write_patterns "$repository"
  ensure_scratch
  validate_patch_into_index \
    "$repository" "$base_revision" "$patch_path" "$scratch_root/validated.index"
}

read_remote_ref() {
  local repository="$1"
  local remote_url="$2"
  local remote_ref="$3"
  local remote_line remote_name extra
  if ! remote_line="$(git -C "$repository" ls-remote --exit-code --heads \
      "$remote_url" "$remote_ref")"; then
    fail "remote head drifted from the event head"
  fi
  read -r REMOTE_HEAD remote_name extra <<< "$remote_line"
  [[ "$remote_name" == "$remote_ref" && -z "$extra" ]] || fail \
    "remote head drifted from the event head"
}

is_local_bare_remote() {
  local remote_url="$1"
  [[ "$remote_url" == /* && -d "$remote_url" \
    && "$(git --git-dir="$remote_url" rev-parse --is-bare-repository 2>/dev/null)" == "true" ]]
}

atomic_update_remote_ref() {
  local repository="$1"
  local remote_url="$2"
  local remote_ref="$3"
  local expected_sha="$4"
  local new_sha="$5"
  if is_local_bare_remote "$remote_url"; then
    git --git-dir="$remote_url" fetch -q --no-tags --no-write-fetch-head \
      "$repository" "$new_sha" || fail "cannot transfer the writeback object"
    git --git-dir="$remote_url" update-ref \
      "$remote_ref" "$new_sha" "$expected_sha" || fail \
        "remote head changed before atomic update"
  else
    atomic_update_github_ref "$remote_ref" "$expected_sha" "$new_sha"
  fi
  read_remote_ref "$repository" "$remote_url" "$remote_ref"
  [[ "$REMOTE_HEAD" == "$new_sha" ]] || fail \
    "remote head does not equal the committed writeback"
}

writeback() {
  [[ "$#" -eq 6 ]] || usage
  local repository="$1"
  local artifact_directory="$2"
  local base_sha="$3"
  local head_sha="$4"
  local head_ref="$5"
  local remote_url="$6"
  [[ "$(git -C "$repository" rev-parse HEAD)" == "$base_sha" ]] || fail \
    "pinned-base validator checkout does not equal the event base SHA"
  verify_artifact_envelope "$artifact_directory"
  [[ "$ENVELOPE_BASE_SHA" == "$base_sha" ]] || fail \
    "trusted artifact base SHA does not equal the event base SHA"
  [[ "$ENVELOPE_HEAD_SHA" == "$head_sha" ]] || fail \
    "trusted artifact head SHA does not equal the event head SHA"
  local patch="$artifact_directory/theory-ingest.patch"
  [[ -f "$patch" ]] || fail "trusted artifact patch is missing"
  [[ "$(hash_file "$patch")" == "$ENVELOPE_PATCH_SHA256" ]] || fail \
    "trusted artifact patch SHA does not match the canonical envelope"

  git check-ref-format --branch "$head_ref" >/dev/null || fail \
    "event head ref is not canonical"
  git -C "$repository" fetch -q --no-tags "$remote_url" "$head_sha" || fail \
    "cannot fetch the immutable event head"
  git -C "$repository" cat-file -e "$head_sha^{commit}" || fail \
    "event head does not name a commit"
  local fork_sha
  if ! fork_sha="$(git -C "$repository" merge-base "$base_sha" "$head_sha")" \
      || [[ -z "$fork_sha" ]]; then
    fail "cannot resolve the immutable fork point of event base and head"
  fi
  assert_report_input_closure_unchanged \
    "$repository" "$repository" "$fork_sha" "$head_sha"
  assert_candidate_theory_is_regular_data "$repository" "$head_sha"
  if ! MERGED_TREE_SHA="$(git -C "$repository" merge-tree \
      --write-tree "$base_sha" "$head_sha")" \
      || [[ ! "$MERGED_TREE_SHA" =~ ^[0-9a-f]+$ ]]; then
    fail "event base and head do not have a conflict-free merge result"
  fi
  THEORY_TREE_SHA="$(git -C "$repository" rev-parse \
    "$MERGED_TREE_SHA:docs/develop/theory")"
  [[ "$THEORY_TREE_SHA" == "$ENVELOPE_THEORY_TREE_SHA" ]] || fail \
    "trusted artifact theory tree does not equal the event merge theory tree"

  load_pinned_write_patterns "$repository"
  ensure_scratch
  local final_index="$scratch_root/writeback.index"
  validate_patch_into_index "$repository" "$head_sha" "$patch" "$final_index"

  local remote_ref="refs/heads/$head_ref"
  read_remote_ref "$repository" "$remote_url" "$remote_ref"
  [[ "$REMOTE_HEAD" == "$head_sha" ]] || fail \
    "remote head drifted from the event head"
  if [[ ! -s "$patch" ]]; then
    printf '%s\n' "theory ingest writeback is a no-op: event head is already closed"
    return 0
  fi

  local tree_sha commit_sha parent_shas
  tree_sha="$(GIT_INDEX_FILE="$final_index" git -C "$repository" write-tree)"
  commit_sha="$(printf '%s\n' 'chore(digestion): auto-ingest theory update' | \
    GIT_AUTHOR_NAME='theory-ingest-bot' \
    GIT_AUTHOR_EMAIL='theory-ingest-bot@users.noreply.github.com' \
    GIT_COMMITTER_NAME='theory-ingest-bot' \
    GIT_COMMITTER_EMAIL='theory-ingest-bot@users.noreply.github.com' \
    git -C "$repository" commit-tree "$tree_sha" -p "$head_sha")"
  parent_shas="$(git -C "$repository" show -s --format=%P "$commit_sha")"
  [[ "$parent_shas" == "$head_sha" ]] || fail \
    "writeback commit does not have exactly the event head as parent"
  git -C "$repository" merge-base --is-ancestor "$head_sha" "$commit_sha" || fail \
    "writeback commit is not a fast-forward child of event head"
  if ! is_local_bare_remote "$remote_url"; then
    create_github_writeback_commit "$repository" "$final_index" "$head_sha"
    commit_sha="$GITHUB_REMOTE_COMMIT_SHA"
  fi
  atomic_update_remote_ref \
    "$repository" "$remote_url" "$remote_ref" "$head_sha" "$commit_sha"
}

[[ "$#" -ge 1 ]] || usage
command="$1"
shift
case "$command" in
  guard-inputs) guard_inputs "$@" ;;
  prepare) prepare "$@" ;;
  validate) validate_command "$@" ;;
  writeback) writeback "$@" ;;
  *) usage ;;
esac

#!/usr/bin/env bash
set -euo pipefail

if (( $# != 6 )); then
  printf '%s\n' 'REVERT_SELF_LOCK_PROBE_BAD_ARGUMENT' >&2
  exit 2
fi

candidate="$1"
event_name="$2"
github_repository="$3"
output_file="$4"
scratch="$5"
job="$6"
if [[ "$job" != engineering && "$job" != lean && "$job" != admission ]]; then
  printf '%s\n' 'REVERT_SELF_LOCK_PROBE_BAD_ARGUMENT' >&2
  exit 2
fi

target_merge=""
j1_evaluator_digest=""
j0_evaluator_digest=""
j1_publication_id=""
j0_publication_id=""
publication_order="not_run"
process_tree_barrier="not_run"

write_outputs() {
  local confirmed="$1" pure_state="$2" engineering_decision="$3"
  local job_decision=unsupported job_authorized=false run_heavy=true
  if [[ "$job" == engineering ]]; then
    job_decision="$engineering_decision"
    if [[ "$engineering_decision" == SELF_LOCK_CONFIRMED ]]; then
      job_authorized=true
      run_heavy=false
    fi
  fi
  {
    printf 'pure_revert_confirmed=%s\n' "$confirmed"
    printf 'pure_revert_state=%s\n' "$pure_state"
    printf 'self_lock_decision=%s\n' "$engineering_decision"
    printf 'job_decision=%s\n' "$job_decision"
    printf 'job_authorized=%s\n' "$job_authorized"
    printf 'run_heavy=%s\n' "$run_heavy"
  } >> "$output_file"
  printf 'REVERT_SELF_LOCK_PROBE_RESULT job=%s authorized=%s run_heavy=%s state=%s decision=%s\n' \
    "$job" "$job_authorized" "$run_heavy" "$pure_state" "$job_decision"
  marker="$(jq -cn \
    --arg job "$job" \
    --arg job_decision "$job_decision" \
    --arg engineering_decision "$engineering_decision" \
    --arg target_merge_sha "$target_merge" \
    --arg j1_evaluator_digest "$j1_evaluator_digest" \
    --arg j0_evaluator_digest "$j0_evaluator_digest" \
    --arg j1_publication_id "$j1_publication_id" \
    --arg j0_publication_id "$j0_publication_id" \
    --arg publication_order "$publication_order" \
    --arg process_tree_barrier "$process_tree_barrier" \
    --argjson job_authorized "$job_authorized" \
    --argjson run_heavy "$run_heavy" \
    '{schema_version:1,job:$job,job_decision:$job_decision,
      decisions:{engineering:$engineering_decision,lean:"unsupported",admission:"unsupported"},
      unsupported:["lean","admission"],job_authorized:$job_authorized,run_heavy:$run_heavy,
      target_merge_sha:$target_merge_sha,j1_evaluator_digest:$j1_evaluator_digest,
      j0_evaluator_digest:$j0_evaluator_digest,j1_publication_id:$j1_publication_id,
      j0_publication_id:$j0_publication_id,publication_order:$publication_order,
      process_tree_barrier:$process_tree_barrier}')"
  printf 'REVERT_SELF_LOCK_PROBE_OBSERVATION %s\n' "$marker"
}

if [[ "$event_name" == push ]]; then
  write_outputs false not_applicable not_run
  exit 0
fi
if [[ "$event_name" != pull_request_target
    || ! -d "$candidate"
    || -z "$github_repository"
    || ! -f "$output_file" ]]; then
  printf '%s\n' 'REVERT_SELF_LOCK_PROBE_BAD_ARGUMENT' >&2
  exit 2
fi
if [[ "$job" != engineering ]]; then
  write_outputs false not_evaluated not_run
  exit 0
fi

if [[ -n "${SELF_LOCK_PROBE_CLASSIFIER:-}${SELF_LOCK_PROBE_CONTROLLER:-}${SELF_LOCK_PROBE_GH:-}${SELF_LOCK_PROBE_ISOLATOR:-}"
    && "${SELF_LOCK_PROBE_TEST_MODE:-}" != 1 ]]; then
  printf '%s\n' 'REVERT_SELF_LOCK_PROBE_TEST_OVERRIDE_DENIED' >&2
  exit 2
fi

mkdir -p "$scratch"
scratch="$(cd "$scratch" && pwd -P)"
test_root="$scratch/probe"
rm -rf -- "$test_root"
mkdir -p "$test_root"
cleanup() {
  if [[ "${SELF_LOCK_PROBE_TEST_MODE:-}" != 1 && "$(uname -s)" == Linux ]]; then
    sudo -n chown -R "$(id -u):$(id -g)" "$test_root" 2>/dev/null || true
  fi
  chmod -R u+rwX "$test_root" 2>/dev/null || true
  rm -rf -- "$test_root"
}
trap cleanup EXIT HUP INT TERM

classifier="${SELF_LOCK_PROBE_CLASSIFIER:-}"
controller="${SELF_LOCK_PROBE_CONTROLLER:-}"
gh_bin="${SELF_LOCK_PROBE_GH:-gh}"
isolator="${SELF_LOCK_PROBE_ISOLATOR:-}"
candidate="$(cd "$candidate" && pwd -P)"
candidate_head="$(git -C "$candidate" rev-parse HEAD)"
candidate_base="$(git -C "$candidate" rev-parse HEAD^1)"

controller_root="$test_root/controller"
base_bin="$test_root/base-bin"
control="$test_root/control"
zone="$test_root/candidate-zone"
j1_repository="$zone/j1"
j0_repository="$zone/j0"
j1_bundle="$zone/j1-bundle"
j0_bundle="$zone/j0-bundle"
j1_home="$zone/j1-home"
j0_home="$zone/j0-home"
j1_nuget="$zone/j1-nuget"
j0_nuget="$zone/j0-nuget"
blockers="$control/blockers.json"
targets="$control/targets.json"
run_edge="$control/run-edge.json"
mkdir -p "$control" "$zone"

git_env=(
  env -u GIT_AUTHOR_NAME -u GIT_AUTHOR_EMAIL
  -u GIT_COMMITTER_NAME -u GIT_COMMITTER_EMAIL
  -u GIT_CONFIG -u GIT_CONFIG_PARAMETERS -u GIT_TEMPLATE_DIR
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null
  GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_COUNT=0
)

if [[ -z "$classifier" || -z "$controller" ]]; then
  "${git_env[@]}" git clone --no-local --no-checkout "$candidate" "$controller_root" >/dev/null 2>&1
  "${git_env[@]}" git -C "$controller_root" checkout --detach "$candidate_base" >/dev/null 2>&1
  "${git_env[@]}" git -C "$controller_root" remote remove origin
  classifier="$controller_root/tools/scripts/workflow/pure-revert-detect.sh"
  dotnet publish "$controller_root/tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" \
    --configuration Release --output "$base_bin" >/dev/null
  controller=(dotnet "$base_bin/StrataLint.EngineeringScope.dll" self-lock-probe)
else
  controller=("$controller")
  mkdir -p "$controller_root/.git" "$base_bin"
fi

classifier_stdout="$test_root/classifier.stdout"
classifier_stderr="$test_root/classifier.stderr"
set +e
"${git_env[@]}" "$classifier" "$candidate" >"$classifier_stdout" 2>"$classifier_stderr"
classifier_status=$?
set -e
classifier_text="$(<"$classifier_stdout")"
classifier_error="$(<"$classifier_stderr")"
if [[ "$classifier_status" -eq 0
    && -z "$classifier_error"
    && "$classifier_text" =~ ^PURE_REVERT_TRUE\ base_sha=([0-9a-f]{40}|[0-9a-f]{64})\ head_sha=([0-9a-f]{40}|[0-9a-f]{64})\ target_merge_sha=([0-9a-f]{40}|[0-9a-f]{64})\ changed_path_count=([1-9][0-9]*)$ \
    && "${BASH_REMATCH[1]}" == "$candidate_base"
    && "${BASH_REMATCH[2]}" == "$candidate_head" ]]; then
  target_merge="${BASH_REMATCH[3]}"
else
  case "$classifier_status:$classifier_text:$classifier_error" in
    4::PURE_REVERT_NO_CHANGES|5::PURE_REVERT_NOT_INVERSE|6::PURE_REVERT_PATH_OUTSIDE_ALLOWLIST|7::PURE_REVERT_AMBIGUOUS_TARGET|8::PURE_REVERT_SECOND_PARENT|9::PURE_REVERT_CLASSIFIER_MODIFIED|11::PURE_REVERT_TARGET_NOT_A_MERGE)
      write_outputs false false not_run
      ;;
    *)
      write_outputs false indeterminate not_run
      ;;
  esac
  exit 0
fi

last_green="$(git -C "$candidate" rev-parse "$target_merge^1" 2>/dev/null || true)"
last_green_runs="$control/last-green-runs.json"
first_red_runs="$control/first-red-runs.json"
if [[ -z "$last_green" ]] \
    || ! "$gh_bin" api \
      "repos/$github_repository/actions/workflows/ci.yml/runs?event=push&head_sha=$last_green&status=completed&per_page=100" \
      > "$last_green_runs" \
    || ! "$gh_bin" api \
      "repos/$github_repository/actions/workflows/ci.yml/runs?event=push&head_sha=$target_merge&status=completed&per_page=100" \
      > "$first_red_runs" \
    || ! "${controller[@]}" bind-red-edge \
      --repository "$candidate" \
      --target-merge "$target_merge" \
      --last-green-runs "$last_green_runs" \
      --first-red-runs "$first_red_runs" \
      --output "$run_edge"; then
  write_outputs false true PROBE_INDETERMINATE
  exit 0
fi
red_run_id="$(jq -er '.first_red_run_id | select(type == "number" and . > 0)' "$run_edge" 2>/dev/null || true)"
red_log="$test_root/first-red.log"
if [[ -z "$red_run_id" ]] \
    || ! "$gh_bin" run view "$red_run_id" --repo "$github_repository" --log-failed > "$red_log" \
    || ! "${controller[@]}" extract-blockers --log "$red_log" --output "$blockers"; then
  write_outputs false true PROBE_INDETERMINATE
  exit 0
fi

for pair in "$j1_repository:$target_merge" "$j0_repository:$last_green"; do
  repository="${pair%%:*}"
  revision="${pair#*:}"
  "${git_env[@]}" git clone --no-local --no-checkout "$candidate" "$repository" >/dev/null 2>&1
  "${git_env[@]}" git -C "$repository" checkout --detach "$revision" >/dev/null 2>&1
  "${git_env[@]}" git -C "$repository" remote remove origin
done
target_base="$(git -C "$j0_repository" rev-parse HEAD)"
target_tree="$(git -C "$j0_repository" rev-parse 'HEAD^{tree}')"
noop_commit="$(
  printf '%s\n' 'synthetic no-op for self-lock probe' |
    "${git_env[@]}" env \
      GIT_AUTHOR_NAME='Self Lock Probe' GIT_AUTHOR_EMAIL='self-lock-probe@example.invalid' \
      GIT_COMMITTER_NAME='Self Lock Probe' GIT_COMMITTER_EMAIL='self-lock-probe@example.invalid' \
      git -C "$j0_repository" commit-tree "$target_tree" -p "$target_base"
)"
"${git_env[@]}" git -C "$j0_repository" checkout --detach "$noop_commit" >/dev/null 2>&1
test "$(git -C "$j0_repository" rev-parse 'HEAD^{tree}')" = \
  "$(git -C "$j0_repository" rev-parse 'HEAD^1^{tree}')"

if ! "${controller[@]}" select-targets \
  --j1-repository "$j1_repository" \
  --j0-repository "$j0_repository" \
  --blockers "$blockers" \
  --output "$targets"; then
  write_outputs false true PROBE_INDETERMINATE
  exit 0
fi
j1_evaluator_digest="$("${controller[@]}" evaluator-digest --controller-root "$controller_root")"
j0_evaluator_digest="$j1_evaluator_digest"
j0_control_temporary="$control/j0-control.tmp.json"
if ! "${controller[@]}" seal-j0-control \
    --repository "$j0_repository" \
    --targets "$targets" \
    --evaluator-digest "$j0_evaluator_digest" \
    --output "$j0_control_temporary"; then
  write_outputs false true PROBE_INDETERMINATE
  exit 0
fi
j0_control_digest="$("${controller[@]}" artifact-digest --path "$j0_control_temporary")"
j0_control="$control/${j0_control_digest#sha256:}.j0-control.json"
mv "$j0_control_temporary" "$j0_control"
chmod 0444 "$blockers" "$targets" "$run_edge" "$last_green_runs" "$first_red_runs" "$j0_control"
chmod 0555 "$control"
dotnet_path="$(command -v dotnet)"
mkdir -p "$j1_bundle" "$j0_bundle" "$j1_home" "$j0_home" "$j1_nuget" "$j0_nuget"
chmod -R a-w "$j0_repository" "$j0_bundle" "$j0_home" "$j0_nuget"

if [[ "${SELF_LOCK_PROBE_TEST_MODE:-}" == 1 ]]; then
  authority_common="$(cd "$controller_root/.git" && pwd -P)"
  process_tree_barrier=test_run_tree
  run_isolated() {
    local subject="$1"
    shift
    "$isolator" --run-tree "$subject" "$@"
  }
  for protected_path in "$authority_common" "$base_bin" "$control" "$j0_repository"; do
    if "$isolator" --canary "$protected_path"; then
      write_outputs false true PROBE_INDETERMINATE
      exit 0
    fi
  done
elif [[ "$(uname -s)" == Linux ]]; then
  authority_common="$(git -C "$controller_root" rev-parse --git-common-dir)"
  authority_common="$(cd "$controller_root" && cd "$authority_common" && pwd -P)"
  if [[ ! -x /usr/bin/unshare ]] || ! sudo -n true; then
    write_outputs false true PROBE_INDETERMINATE
    exit 0
  fi
  process_tree_barrier=linux_pid_namespace
  probe_uid="$(id -u nobody)"
  probe_gid="$(id -g nobody)"
  chmod -R u=rwX,go=rX "$controller_root" "$base_bin"
  chmod 0700 "$authority_common"
  run_isolated() {
    local subject="$1" home nuget
    shift
    if [[ "$subject" == j1 ]]; then
      home="$j1_home"; nuget="$j1_nuget"
    else
      home="$j0_home"; nuget="$j0_nuget"
    fi
    sudo -n /usr/bin/unshare --pid --fork --kill-child=KILL --mount-proc \
      /usr/bin/sudo -n -u nobody /usr/bin/env -i \
        HOME="$home" DOTNET_CLI_HOME="$home" NUGET_PACKAGES="$nuget" \
        PATH="$(dirname "$dotnet_path"):/usr/bin:/bin" \
        "$@"
  }
  if run_isolated j1 /usr/bin/touch "$authority_common/candidate-write-canary" 2>/dev/null \
      || run_isolated j1 /usr/bin/touch "$base_bin/candidate-write-canary" 2>/dev/null \
      || run_isolated j1 /usr/bin/touch "$control/candidate-write-canary" 2>/dev/null \
      || run_isolated j1 /usr/bin/touch "$j0_repository/candidate-write-canary" 2>/dev/null; then
    write_outputs false true PROBE_INDETERMINATE
    exit 0
  fi
else
  write_outputs false true PROBE_INDETERMINATE
  exit 0
fi

candidate_zone_owner() {
  local subject="$1" repository bundle home nuget
  [[ "${SELF_LOCK_PROBE_TEST_MODE:-}" == 1 ]] && return 0
  if [[ "$subject" == j1 ]]; then
    repository="$j1_repository"; bundle="$j1_bundle"; home="$j1_home"; nuget="$j1_nuget"
  else
    repository="$j0_repository"; bundle="$j0_bundle"; home="$j0_home"; nuget="$j0_nuget"
  fi
  sudo -n chown -R "$probe_uid:$probe_gid" "$repository" "$bundle" "$home" "$nuget"
}

base_zone_owner() {
  local subject="$1" repository bundle home nuget
  [[ "${SELF_LOCK_PROBE_TEST_MODE:-}" == 1 ]] && return 0
  if [[ "$subject" == j1 ]]; then
    repository="$j1_repository"; bundle="$j1_bundle"; home="$j1_home"; nuget="$j1_nuget"
  else
    repository="$j0_repository"; bundle="$j0_bundle"; home="$j0_home"; nuget="$j0_nuget"
  fi
  sudo -n chown -R "$(id -u):$(id -g)" "$repository" "$bundle" "$home" "$nuget"
}

run_subject() {
  local label="$1" kind="$2" repository="$3" bundle="$4"
  local receipt publication_id
  local target_arguments=(
    run-targeted
    --repository "$repository"
    --subject-kind "$kind"
    --targets "$targets"
    --staging-bundle "$bundle/.staging"
    --evaluator-digest "$j1_evaluator_digest"
    --dotnet "$dotnet_path"
  )
  [[ "$label" == j0 ]] && target_arguments+=(--j0-control "$j0_control")
  candidate_zone_owner "$label"
  if ! run_isolated "$label" "${controller[@]}" "${target_arguments[@]}"; then
    base_zone_owner "$label"
    return 1
  fi
  base_zone_owner "$label"
  receipt="$("${controller[@]}" publish \
    --controller-root "$controller_root" \
    --bundle-root "$bundle" \
    --staging-bundle "$bundle/.staging")"
  publication_id="$(jq -er \
    '.publication_id | select(type == "string" and test("^[0-9a-f]{64}$"))' \
    <<< "$receipt" 2>/dev/null || true)"
  [[ -n "$publication_id" ]] || return 1
  if [[ "$label" == j1 ]]; then
    j1_publication_id="$publication_id"
  else
    j0_publication_id="$publication_id"
  fi
}

if ! run_subject j1 merge "$j1_repository" "$j1_bundle"; then
  write_outputs false true PROBE_INDETERMINATE
  exit 0
fi
chmod -R u+rwX "$j0_repository" "$j0_bundle" "$j0_home" "$j0_nuget"
j0_evaluator_digest="$("${controller[@]}" evaluator-digest --controller-root "$controller_root")"
if [[ "$j0_evaluator_digest" != "$j1_evaluator_digest" ]] \
    || ! run_subject j0 synthetic_noop "$j0_repository" "$j0_bundle"; then
  write_outputs false true PROBE_INDETERMINATE
  exit 0
fi
publication_order=j1_then_j0

probe_json="$test_root/probe.json"
probe_error="$test_root/probe.stderr"
set +e
"${controller[@]}" evaluate \
  --controller-root "$controller_root" \
  --pure-revert-script "$classifier" \
  --candidate-repository "$candidate" \
  --j1-repository "$j1_repository" \
  --j1-bundle "$j1_bundle" \
  --j0-repository "$j0_repository" \
  --j0-bundle "$j0_bundle" \
  --required-gate engineering \
  --red-gate engineering > "$probe_json" 2> "$probe_error"
probe_status=$?
set -e
decision="$(jq -er \
  'if (.schema_version == 1 and (.decision | type == "string") and (.authorization.allow_exact_revert | type == "boolean")) then .decision else error("invalid probe result") end' \
  "$probe_json" 2>/dev/null || true)"
if [[ "$probe_status" -eq 0
    && ! -s "$probe_error"
    && "$decision" == SELF_LOCK_CONFIRMED
    && "$(jq -r '.authorization.allow_exact_revert' "$probe_json")" == true
    && "$(jq -r '.authorization.target_merge_sha' "$probe_json")" == "$target_merge" ]]; then
  cat "$probe_json"
  write_outputs true true SELF_LOCK_CONFIRMED
else
  case "$decision" in
    TRUE_RED_CONFIRMED|PROBE_INDETERMINATE) ;;
    *) decision=PROBE_INDETERMINATE ;;
  esac
  write_outputs false true "$decision"
fi

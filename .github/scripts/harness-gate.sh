#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# harness-gate.sh — 单一真源的 harness 门:本地与 CI 共用同一条 admission 逻辑。
#
# 用户原则:本地需要有一个跟 CI 一样的脚本,并且 CI 也调用这个脚本,这样
# 本地/CI 都可以快速测,不用一遍一遍等 CI。
#
# 用法:
#   本地快速门:  .github/scripts/harness-gate.sh --base origin/dev
#   CI baseline: .github/scripts/harness-gate.sh --candidate candidate \
#                    --judge-root baseline --base "$DEV_BASELINE_SHA"
#
# 阶段(每阶段带计时;STRATALINT_TIMING 由本脚本自动开启):
#   ensure-toolchain → cache-get → prebuild → build-judge → selftest → admission
#
# admission 退出语义(零信任门):
#   0 = 内容全验通过,无保护面变更;
#   3 = SL-022 保护面变更 → 标注 + lake build 地板(bootstrap 脚手架,待组件 C);
#   其余 = 内容违规/基础设施故障 → fail closed。
#
# 环境自适应(无分支):有 GITHUB_STEP_SUMMARY 则写 CI 摘要,否则回落 stdout;
# 有 GITHUB_OUTPUT 则不污染;toolchain/lake 全幂等,本地重复调用安全。
# ─────────────────────────────────────────────────────────────────────────────
set -euo pipefail

CANDIDATE_ROOT="."
JUDGE_ROOT=""
BASE_REF=""
SKIP_PREP="${HARNESS_GATE_SKIP_PREP:-0}"   # 本地已备环境时可跳过 toolchain/cache/prebuild

while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate)  CANDIDATE_ROOT="$2"; shift 2 ;;
    --judge-root) JUDGE_ROOT="$2";     shift 2 ;;
    --base)       BASE_REF="$2";       shift 2 ;;
    --skip-prep)  SKIP_PREP=1;         shift ;;
    *) echo "harness-gate: unknown arg '$1'" >&2; exit 2 ;;
  esac
done

[[ -n "$BASE_REF" ]] || { echo "harness-gate: --base <rev> required" >&2; exit 2; }
[[ -d "$CANDIDATE_ROOT" ]] || { echo "harness-gate: candidate root '$CANDIDATE_ROOT' absent" >&2; exit 2; }
# judge 默认 = candidate 自身的 harness(本地);CI 传 baseline 作独立法官。
[[ -n "$JUDGE_ROOT" ]] || JUDGE_ROOT="$CANDIDATE_ROOT"
[[ -d "$JUDGE_ROOT" ]] || { echo "harness-gate: judge root '$JUDGE_ROOT' absent" >&2; exit 2; }
CANDIDATE_ROOT="$(cd "$CANDIDATE_ROOT" && pwd -P)"
JUDGE_ROOT="$(cd "$JUDGE_ROOT" && pwd -P)"

export PATH="$HOME/.elan/bin:$PATH"
ELAN="${ELAN_BIN:-$(command -v elan || true)}"
[[ -n "$ELAN" ]] || ELAN="$HOME/.elan/bin/elan"
LAKE="${LAKE_BIN:-lake}"
command -v "$LAKE" >/dev/null 2>&1 || LAKE="$HOME/.elan/bin/lake"
DLL_REL="Meta/StrataLint/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"

summary() {  # 写 CI 摘要或回落 stdout
  if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then printf '%s\n' "$1" >> "$GITHUB_STEP_SUMMARY"; else printf '%s\n' "$1"; fi
}

_t0=$(date +%s)
mark() { local now; now=$(date +%s); printf '[gate] %-16s %ss\n' "$1" "$((now-_t0))" >&2; _t0=$now; }

# ── ensure-toolchain(幂等)─────────────────────────────────────────────
ensure_toolchain() {
  local root="$1" tc
  tc="$(tr -d '\r\n' < "$root/lean-toolchain")"
  if [[ ! -x "$ELAN" ]]; then
    curl --proto '=https' --tlsv1.2 -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
    ELAN="$HOME/.elan/bin/elan"
  fi
  "$ELAN" toolchain list 2>/dev/null | grep -qF "$tc" || "$ELAN" toolchain install "$tc"
  "$ELAN" default "$tc" >/dev/null 2>&1 || true
}

# ── cache-get + prebuild(两棵树均增量)───────────────────────────────
prepare_lean_root() {
  local root="$1"
  ( cd "$root" && "$LAKE" exe cache get ) \
    || summary "WARNING: mathlib cache fetch failed for $root (lake build will rebuild)"
}

prebuild_lean_root() {
  local root="$1"
  ( cd "$root" && "$LAKE" build )
}

# ── build-judge(法官 harness 的 Release 二进制)───────────────────────
build_judge() {
  dotnet restore "$JUDGE_ROOT/Meta/StrataLint/StrataLint.sln" --locked-mode
  dotnet build   "$JUDGE_ROOT/Meta/StrataLint/StrataLint.sln" --no-restore --configuration Release --warnaserror
}

# ── selftest(两遍字节一致)────────────────────────────────────────────
selftest() {
  local tmp; tmp="$(mktemp -d)"
  ( cd "$JUDGE_ROOT" && dotnet "$DLL_REL" selftest > "$tmp/a" && dotnet "$DLL_REL" selftest > "$tmp/b" )
  cmp "$tmp/a" "$tmp/b"
}

if [[ "$SKIP_PREP" != "1" ]]; then
  ensure_toolchain "$CANDIDATE_ROOT"
  if [[ "$JUDGE_ROOT" != "$CANDIDATE_ROOT" ]]; then ensure_toolchain "$JUDGE_ROOT"; fi
  mark ensure-toolchain
  prepare_lean_root "$CANDIDATE_ROOT"
  if [[ "$JUDGE_ROOT" != "$CANDIDATE_ROOT" ]]; then prepare_lean_root "$JUDGE_ROOT"; fi
  mark cache-get
  prebuild_lean_root "$CANDIDATE_ROOT"
  if [[ "$JUDGE_ROOT" != "$CANDIDATE_ROOT" ]]; then prebuild_lean_root "$JUDGE_ROOT"; fi
  mark prebuild
  build_judge
  mark build-judge
  selftest
  mark selftest
fi

# ── admission(exit 语义分离)─────────────────────────────────────────
export STRATALINT_TIMING="${STRATALINT_TIMING:-1}"
set +e
( cd "$CANDIDATE_ROOT" && dotnet "$JUDGE_ROOT/$DLL_REL" check --protected-base "$BASE_REF" )
rc=$?
set -e
mark admission

if [[ $rc -eq 0 ]]; then
  summary "### Admission: content fully validated, no protected-surface change"
  exit 0
elif [[ $rc -eq 3 ]]; then
  echo "::warning title=SL-022 protected-surface change::Scaffold path: lake build floor enforced; machine meta-gate arrives with component C." 2>/dev/null || true
  summary "### SL-022 protected-surface change (bootstrap scaffold path)"
  ( cd "$CANDIDATE_ROOT" && "$LAKE" build )
  exit 0
else
  exit "$rc"
fi

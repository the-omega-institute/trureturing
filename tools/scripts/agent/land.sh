#!/usr/bin/env bash
# 统一落地器(铸器,替代 sed 克隆链;器律③)
# 用法: land.sh LANE BRANCH MSGFILE --paths-from NUL_FILE [--wait-pr N] [--cover ATOM GID]...
# 语义: [等待 PR N 合入] → cd LANE → checkout/建 BRANCH(自 origin/dev,已存在则合 dev)
#       → make lean-report(合 dev 可能带进新 D5 模块)→ 逐对 make cover
#       → make gate → builder commit → push → pr-open → 等 MERGED。
#       零 cover 对 = 纯 deposit 分支照落。
set -x
LAND_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/$(basename "${BASH_SOURCE[0]}")"
L="${LAND_LOG_DIR:-${TMPDIR:-/tmp}/land-logs}"; mkdir -p "$L/flights"
LANE=$1; BRANCH=$2; MSG=$3; shift 3
WAITPR=""; PATHS_FILE=""; COVERS=(); COVER_ARGUMENTS=()
while [ $# -gt 0 ]; do case "$1" in
  --paths-from) PATHS_FILE=$2; shift 2;;
  --wait-pr) WAITPR=$2; shift 2;;
  --cover) COVERS+=("$2	$3"); shift 3;;
  *) echo "UNKNOWN_ARG $1"; exit 64;; esac; done
[ -n "$PATHS_FILE" ] && [ -r "$PATHS_FILE" ] && [ -s "$PATHS_FILE" ] || {
  echo AUTHORIZED_PATHS_REQUIRED; exit 64;
}
PATHS_FILE="$(cd "$(dirname "$PATHS_FILE")" && pwd -P)/$(basename "$PATHS_FILE")"
PROTOCOL="$(cd "$(dirname "${BASH_SOURCE[0]}")/../worktree" && pwd -P)/worktree_protocol.py"
TAG=$(basename "$MSG" .msg)
[ -d "$LANE/.git" ] || [ -f "$LANE/.git" ] || { echo "BAD_LANE=$LANE"; exit 88; }
[ -r "$MSG" ] && [ -s "$MSG" ] || { echo "BAD_MSG=$MSG"; exit 89; }
MSG="$(cd "$(dirname "$MSG")" && pwd -P)/$(basename "$MSG")"
dotnet run \
  --project "$LANE/tools/StrataLint.Cli/StrataLint.Cli.csproj" \
  --configuration Release \
  --no-launch-profile \
  -- \
  worktree validate-branch --branch "$BRANCH"
BRANCH_VALIDATION_EXIT=$?
[ "$BRANCH_VALIDATION_EXIT" -eq 0 ] || {
  echo "BAD_BRANCH=$BRANCH validation_exit=$BRANCH_VALIDATION_EXIT"
  exit 87
}
if [ -n "$WAITPR" ]; then
  until [ "$(gh api repos/the-omega-institute/trureturing/pulls/$WAITPR --jq '.merged')" = "true" ]; do sleep 30; done
  echo "WAITED_PR=$WAITPR"
fi
cd "$LANE" || exit 90
if [ -z "${LAND_PARTICIPATION_HELD:-}" ]; then
git fetch origin dev -q || exit 91
python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" --exclusive --git --ref "refs/heads/$BRANCH" -- /bin/bash -c '
  if git rev-parse --verify "$1" >/dev/null 2>&1; then
    git checkout "$1" && git merge origin/dev --no-edit
  else
    git checkout -b "$1" origin/dev
  fi
' worktree-land "$BRANCH" || { echo BRANCH_OPERATION_RETAINED; exit 92; }
fi
# After the short checkout operation, retain shared participation for the
# remaining task. The host owns child joining; each scoped child exits before
# the next step, and independent editors may continue between stable units.
if [ -z "${LAND_PARTICIPATION_HELD:-}" ]; then
  LAND_BASE=${LAND_BASE:-$(git rev-parse origin/dev)} || exit 91
  exec python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" -- \
    env LAND_PARTICIPATION_HELD=1 LAND_BASE="$LAND_BASE" /bin/bash "$LAND_SCRIPT" "$LANE" "$BRANCH" "$MSG" \
    --paths-from "$PATHS_FILE" "${COVER_ARGUMENTS[@]}"
fi
export LC_ALL=C LANG=C
BASE=${LAND_BASE:-$(git rev-parse origin/dev)}
make lean-report > "$L/flights/$TAG-leanreport.log" 2>&1; R=$?
echo "LEANREPORT_EXIT=$R"
[ "$R" -eq 0 ] || { echo HALT_LEAN_REPORT; exit 97; }
for pair in "${COVERS[@]}"; do
  A=${pair%%$'\t'*}; G=${pair##*$'\t'}
  make cover ATOM_ID=$A GID=$G > "$L/flights/$TAG-cover-${A:17:8}.log" 2>&1; C=$?
  echo "COVER_EXIT=$C atom=${A:17:8}"
  [ "$C" -eq 0 ] || { echo HALT_COVER_RED; exit 93; }
done
python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" --read . -- make gate BASE="$BASE" > "$L/flights/$TAG-gate.log" 2>&1; P=$?; echo "GATE_EXIT=$P"
[ "$P" -eq 0 ] || { echo HALT_GATE; exit 94; }
python3 -B "$PROTOCOL" --source "$LANE" checkpoint --path "$LANE" \
  --paths-from "$PATHS_FILE" --message-file "$MSG" --read . || { echo HALT_LAND_CHECKPOINT; exit 98; }
python3 -B "$PROTOCOL" --source "$LANE" publish --path "$LANE" --branch "$BRANCH" || exit 95
make pr-open HEAD="$BRANCH" MESSAGE="$MSG" AUTO_MERGE=1 > "$L/flights/$TAG-propen.log" 2>&1; O=$?; echo "PROPEN_EXIT=$O"
[ "$O" -eq 0 ] || exit 96
PR=$(grep -oE "pr=[0-9]+" "$L/flights/$TAG-propen.log" | head -1 | cut -d= -f2); echo "PHASE1_PR=$PR"
until [ "$(gh api repos/the-omega-institute/trureturing/pulls/$PR --jq '.merged')" = "true" ]; do sleep 30; done
echo PHASE1_MERGED

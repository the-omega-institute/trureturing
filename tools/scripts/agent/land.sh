#!/usr/bin/env bash
# 统一落地器(铸器,替代 sed 克隆链;器律③)
# 用法: land.sh LANE BRANCH MSGFILE --paths-from NUL_FILE [--wait-pr N] [--cover ATOM GID]...
# 语义: [等待 PR N 合入] → cd LANE → checkout/建 BRANCH(自 origin/dev,已存在则合 dev)
#       → make lean-report(合 dev 可能带进新 D5 模块)→ 逐对 make cover
#       → make gate → builder commit → push → pr-open → 等 MERGED。
#       零 cover 对 = 纯 deposit 分支照落。
set -x
LAND_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/$(basename "${BASH_SOURCE[0]}")"
[ "$#" -ge 3 ] || { echo LAND_ARGUMENTS_REQUIRED; exit 64; }
LANE=$1; BRANCH=$2; MSG=$3; shift 3
WAITPR=""; PATHS_FILE=""; COVERS=(); WAIT_ARGUMENTS=()
while [ $# -gt 0 ]; do case "$1" in
  --paths-from) [ "$#" -ge 2 ] || exit 64; PATHS_FILE=$2; shift 2;;
  --wait-pr) [ "$#" -ge 2 ] || exit 64; WAITPR=$2; WAIT_ARGUMENTS=(--wait-pr "$2"); shift 2;;
  --cover) [ "$#" -ge 3 ] || exit 64; COVERS+=(--cover "$2" "$3"); shift 3;;
  *) echo "UNKNOWN_ARG $1"; exit 64;; esac; done
# The adapter changes cwd on entry. Anchor relative inputs without inspecting
# the target before entry, and forward argument boundaries through each restart.
case "$LANE" in /*) ;; *) LANE="$PWD/$LANE";; esac
case "$MSG" in /*) ;; *) MSG="$PWD/$MSG";; esac
[ -n "$PATHS_FILE" ] || { echo AUTHORIZED_PATHS_REQUIRED; exit 64; }
case "$PATHS_FILE" in /*) ;; *) PATHS_FILE="$PWD/$PATHS_FILE";; esac
PROTOCOL="$(cd "$(dirname "${BASH_SOURCE[0]}")/../worktree" && pwd -P)/worktree_protocol.py"
if [ -z "${LAND_PARTICIPATION_HELD:-}" ] && [ -z "${LAND_VALIDATION_HELD:-}" ]; then
  if [ -n "$WAITPR" ]; then
    until [ "$(gh api repos/the-omega-institute/trureturing/pulls/$WAITPR --jq '.merged')" = "true" ]; do sleep 30; done
    echo "WAITED_PR=$WAITPR"
  fi
  # Validation builds only after shared entry and an affected tools scope.
  python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" --write tools -- \
    env LAND_VALIDATION_HELD=1 /bin/bash "$LAND_SCRIPT" "$LANE" "$BRANCH" "$MSG" \
    --paths-from "$PATHS_FILE" "${WAIT_ARGUMENTS[@]}" "${COVERS[@]}" || exit $?
  # Only the checkout transformation requires exclusive tree entry.
  python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" --exclusive --git --ref "refs/heads/$BRANCH" -- /bin/bash -c '
    git fetch origin dev -q || exit 91
    if git rev-parse --verify "$1" >/dev/null 2>&1; then
      git checkout "$1" && git merge origin/dev --no-edit
    else
      git checkout -b "$1" origin/dev
    fi
  ' worktree-land "$BRANCH" || { echo BRANCH_OPERATION_RETAINED; exit 92; }
  # The host joins task children. Independent participants retain shared entry.
  exec python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" -- \
    env LAND_PARTICIPATION_HELD=1 /bin/bash "$LAND_SCRIPT" "$LANE" "$BRANCH" "$MSG" \
    --paths-from "$PATHS_FILE" "${WAIT_ARGUMENTS[@]}" "${COVERS[@]}"
fi
[ -r "$PATHS_FILE" ] && [ -s "$PATHS_FILE" ] || { echo AUTHORIZED_PATHS_REQUIRED; exit 64; }
PATHS_FILE="$(cd "$(dirname "$PATHS_FILE")" && pwd -P)/$(basename "$PATHS_FILE")"
[ -d "$LANE/.git" ] || [ -f "$LANE/.git" ] || { echo "BAD_LANE=$LANE"; exit 88; }
[ -r "$MSG" ] && [ -s "$MSG" ] || { echo "BAD_MSG=$MSG"; exit 89; }
MSG="$(cd "$(dirname "$MSG")" && pwd -P)/$(basename "$MSG")"
if [ -n "${LAND_VALIDATION_HELD:-}" ]; then
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
  exit 0
fi
cd "$LANE" || exit 90
L="${LAND_LOG_DIR:-${TMPDIR:-/tmp}/land-logs}"; mkdir -p "$L/flights"
TAG=$(basename "$MSG" .msg)
export LC_ALL=C LANG=C
BASE=${LAND_BASE:-$(git rev-parse origin/dev)}
make lean-report > "$L/flights/$TAG-leanreport.log" 2>&1; R=$?
echo "LEANREPORT_EXIT=$R"
[ "$R" -eq 0 ] || { echo HALT_LEAN_REPORT; exit 97; }
for ((i=0; i<${#COVERS[@]}; i+=3)); do
  A=${COVERS[i+1]}; G=${COVERS[i+2]}
  make cover "ATOM_ID=$A" "GID=$G" > "$L/flights/$TAG-cover-${A:17:8}.log" 2>&1; C=$?
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

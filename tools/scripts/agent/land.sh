#!/usr/bin/env bash
# 统一落地器(铸器,替代 sed 克隆链;器律③)
# 用法: land.sh LANE BRANCH MSGFILE [--wait-pr N]
# 语义: [等待 PR N 合入] → cd LANE → checkout/建 BRANCH(自 origin/dev,已存在则合 dev)
#       → [FULL_BUILD=1 时运行 make check-lean-report FULL_BUILD=1]
#       → make gate BASE=<基线> → builder commit → push → pr-open → 等 MERGED。
set -x
LAND_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/$(basename "${BASH_SOURCE[0]}")"
[ "$#" -ge 3 ] || { echo LAND_ARGUMENTS_REQUIRED; exit 64; }
LANE=$1; BRANCH=$2; MSG=$3; shift 3
WAITPR=""; WAIT_ARGUMENTS=()
while [ $# -gt 0 ]; do case "$1" in
  --wait-pr) [ "$#" -ge 2 ] || exit 64; WAITPR=$2; WAIT_ARGUMENTS=(--wait-pr "$2"); shift 2;;
  *) echo "UNKNOWN_ARG $1"; exit 64;; esac; done
# The adapter changes cwd on entry. Anchor relative inputs without inspecting
# the target before entry, and forward argument boundaries through each restart.
case "$LANE" in /*) ;; *) LANE="$PWD/$LANE";; esac
case "$MSG" in /*) ;; *) MSG="$PWD/$MSG";; esac
PROTOCOL="$(cd "$(dirname "${BASH_SOURCE[0]}")/../worktree" && pwd -P)/worktree_protocol.py"
if [ -z "${LAND_PARTICIPATION_HELD:-}" ] && [ -z "${LAND_VALIDATION_HELD:-}" ]; then
  if [ -n "$WAITPR" ]; then
    until [ "$(gh api repos/the-omega-institute/trureturing/pulls/$WAITPR --jq '.merged')" = "true" ]; do sleep 30; done
    echo "WAITED_PR=$WAITPR"
  fi
  # Validation builds only after shared entry and an affected tools scope.
  python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" -- \
    env LAND_VALIDATION_HELD=1 /bin/bash "$LAND_SCRIPT" "$LANE" "$BRANCH" "$MSG" \
    "${WAIT_ARGUMENTS[@]}" || exit $?
  # The checkout transformation runs through the same identity wrapper as the
  # validation and publication steps; lifecycle custody is not required.
  python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" -- /bin/bash -c '
    git fetch origin dev -q || exit 91
    if git rev-parse --verify "$1" >/dev/null 2>&1; then
      git checkout "$1" && git merge origin/dev --no-edit
    else
      git checkout -b "$1" origin/dev
    fi
  ' worktree-land "$BRANCH" || { echo BRANCH_OPERATION_RETAINED; exit 92; }
  # Keep the continuation environment explicit for the recursive script call.
  exec python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" -- \
    env LAND_PARTICIPATION_HELD=1 /bin/bash "$LAND_SCRIPT" "$LANE" "$BRANCH" "$MSG" \
    "${WAIT_ARGUMENTS[@]}"
fi
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
L="${LAND_LOG_DIR:-$LANE/build/land-logs}"
TAG=$(basename "$MSG" .msg)
export LC_ALL=C LANG=C
BASE=${LAND_BASE:-$(git rev-parse origin/dev)}
landing_child() {
  # The registered discovery roots stay protected before any expansion/read,
  # through exec and all children. These are affected paths, not tree exclusion.
  python3 -B - "$PROTOCOL" "$LANE" "$@" <<'PY_LANDING_CHILD'
import json
import os
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(sys.argv[1]).parent))
import worktree_protocol as protocol

root = Path(sys.argv[2]).resolve()
log = Path(sys.argv[3]).resolve()
command = sys.argv[4:]
protocol.identity(root, root)
def protect(names):
    for name in names:
        path = (root / name).resolve()
        if path != root and root not in path.parents:
            raise protocol.Refused("landing_input_outside_tree:" + str(path))

names = [str(log), "tools", ".lake", "build/lean-cache", "lean-report-inputs.json", "Makefile",
         "Directory.Build.props", "Directory.Build.targets", "Directory.Packages.props",
         "global.json", ".editorconfig", ".globalconfig", "NuGet.Config", "NuGet.config", "nuget.config", "Meta"]
report = os.environ.get("LEAN_REPORT", ".lake/build/stratalint/raw-lean-report.json")
seed = os.environ.get("STRATALINT_LEAN_REPORT_REUSE", report)
for output in (report, seed, ".lake/build/stratalint/raw-lean-report.json"):
    names.extend(output + suffix for suffix in ("", ".sha256", ".input.attestation",
                 ".provenance.json", ".materials.zip", ".reuse.json"))
names.append(os.environ.get("STRATALINT_LEAN_REPORT_LOG_DIR", report + ".logs"))
names.append(os.environ.get("STRATALINT_LEAN_BUILD_WORK_FILE", "build/lean-cache/build-work.json"))
if os.environ.get("STRATALINT_LEAN_PRODUCER_DLL"):
    names.append(os.environ["STRATALINT_LEAN_PRODUCER_DLL"])
protect(names)
declaration = json.loads((root / "lean-report-inputs.json").read_text())
# Lock the literal discovery prefix of each registered glob, including
# optional/missing members. File enumeration alone misses new inputs.
patterns = []
for key in ("report_modules", "inspector_sources", "dependency_sources", "config_inputs"):
    patterns.extend(item["pattern"] for item in declaration.get(key, {}).get("include", []))
patterns.extend(item["pattern"] for item in declaration["producer_scopes"]["lean-report"]["include"])
prefixes = []
for pattern in patterns:
    if pattern.startswith("/") or "\\" in pattern or any(p in ("", ".", "..") for p in pattern.split("/")):
        raise protocol.Refused("unsafe_registered_landing_input:" + pattern)
    prefix = pattern.split("*", 1)[0]
    prefixes.append(prefix.rsplit("/", 1)[0] or "." if "*" in pattern else pattern)
protect(prefixes)
os.chdir(root)
log.parent.mkdir(parents=True, exist_ok=True)
descriptor = os.open(log, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
os.dup2(descriptor, 1)
os.dup2(descriptor, 2)
os.close(descriptor)
os.execvpe(command[0], command, protocol.git_environment())
PY_LANDING_CHILD
}
if [ "${FULL_BUILD:-0}" = 1 ]; then
  landing_child "$L/flights/$TAG-leanreport.log" make check-lean-report FULL_BUILD=1; R=$?
  echo "LEANREPORT_EXIT=$R"
  [ "$R" -eq 0 ] || { echo HALT_LEAN_REPORT; exit 97; }
fi
landing_child "$L/flights/$TAG-gate.log" python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" -- make gate BASE="$BASE"
P=$?; echo "GATE_EXIT=$P"
[ "$P" -eq 0 ] || { echo HALT_GATE; exit 94; }
python3 -B "$PROTOCOL" --source "$LANE" checkpoint --path "$LANE" \
  --message-file "$MSG" || { echo HALT_LAND_CHECKPOINT; exit 98; }
python3 -B "$PROTOCOL" --source "$LANE" publish --path "$LANE" --branch "$BRANCH" || exit 95
make pr-open HEAD="$BRANCH" MESSAGE="$MSG" AUTO_MERGE=1 > "$L/flights/$TAG-propen.log" 2>&1; O=$?; echo "PROPEN_EXIT=$O"
[ "$O" -eq 0 ] || exit 96
PR=$(grep -oE "pr=[0-9]+" "$L/flights/$TAG-propen.log" | head -1 | cut -d= -f2); echo "PHASE1_PR=$PR"
until [ "$(gh api repos/the-omega-institute/trureturing/pulls/$PR --jq '.merged')" = "true" ]; do sleep 30; done
echo PHASE1_MERGED

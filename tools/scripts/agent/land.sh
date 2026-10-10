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
  python3 -B "$PROTOCOL" --source "$LANE" with --path "$LANE" --write tools \
    --read Directory.Build.props --read Directory.Build.targets --read Directory.Packages.props \
    --read global.json --read .editorconfig --read .globalconfig \
    --read NuGet.Config --read NuGet.config --read nuget.config -- \
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
L="${LAND_LOG_DIR:-${TMPDIR:-/tmp}/land-logs}"
TAG=$(basename "$MSG" .msg)
export LC_ALL=C LANG=C
BASE=${LAND_BASE:-$(git rev-parse origin/dev)}
landing_child() {
  # The registered discovery roots stay protected before any expansion/read,
  # through exec and all children. These are affected paths, not tree exclusion.
  python3 -B - "$PROTOCOL" "$LANE" "$@" <<'PY_LANDING_CHILD'
from contextlib import ExitStack
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
with ExitStack() as stack:
    protocol.tree_scope(stack, root, root)
    protocol.identity(root, root)
    held = []
    def protect(names):
        paths = sorted(set((root / name).resolve() for name in names), key=lambda p: (len(p.parts), str(p)))
        for path in paths:
            if any(path == prior or prior in path.parents for prior in held):
                continue
            if any(path in prior.parents for prior in held):
                raise protocol.Refused("landing_scope_expansion_overlaps_held_child:" + str(path))
            if path == root or root in path.parents:
                protocol.path_scopes(stack, root, root, writes=(str(path.relative_to(root)),))
            else:
                # Configured report/log outputs can be outside the checkout.
                protocol.tree_scope(stack, root, path.parent)
                protocol.path_scopes(stack, root, path.parent, writes=(path.name,))
            held.append(path)

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
    if command[1] == "cover":
        names.extend(("Meta/Digestion", "Meta/BACKFILL.yaml", "Golden/Frozen/state",
                      "D5", "Reg", "Trureturing.lean"))
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
    if command[1] == "cover":
        # The child searches and chains current rows, and may migrate/delete
        # paths and prune directories. Hold the complete ledger discovery root.
        # Metadata identity strings use the existing loader's literal TOML form.
        sources = []
        for metadata in (root / "Meta/Digestion/backfill").glob("*/source.toml"):
            for line in metadata.read_text().splitlines():
                if line.startswith('path = "') and line.endswith('"'):
                    sources.append(line[len('path = "'):-1])
        # Valid tail artifacts live under tools/Authorizations. Also coordinate
        # any scalar candidate path the child reads before rejecting its receipt.
        for row in (root / "Meta/Digestion/backfill").glob("*/*/*.yaml"):
            lines = [line for line in row.read_text().splitlines()
                     if line.strip() and not line.strip().startswith("#")]
            for index, line in enumerate(lines):
                match = re.fullmatch(r"\s*path\s*:\s*(.+)", line)
                if match:
                    value = match[1].strip()
                    if value[:1] == value[-1:] == '"':
                        try: value = json.loads(value)
                        except ValueError: value = value[1:-1]
                    elif value[:1] == value[-1:] == "'":
                        value = value[1:-1]
                    if value in ("|", "|-", "|+", ">", ">-", ">+"):
                        # The supported YAML subset joins trimmed block lines
                        # with newlines for every block marker.
                        indent = len(line) - len(line.lstrip(" "))
                        block = []
                        for following in lines[index + 1:]:
                            if len(following) - len(following.lstrip(" ")) <= indent:
                                break
                            block.append(following.strip())
                        value = "\n".join(block)
                    if value not in ("null", "~", ""):
                        sources.append(value)
        for name in sources:
            target = (root / name).resolve()
            if Path(name).is_absolute() or root not in target.parents:
                raise protocol.Refused("landing_ledger_input_outside_tree:" + name)
        protect(sources)
    os.environ["WORKTREE_SCOPE_FDS"] = ",".join(map(str, protocol.scope_fds()))
    os.chdir(root)
    log.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(log, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    os.dup2(descriptor, 1)
    os.dup2(descriptor, 2)
    os.close(descriptor)
    os.execvpe(command[0], command, protocol.git_environment())
PY_LANDING_CHILD
}
landing_child "$L/flights/$TAG-leanreport.log" make lean-report; R=$?
echo "LEANREPORT_EXIT=$R"
[ "$R" -eq 0 ] || { echo HALT_LEAN_REPORT; exit 97; }
for ((i=0; i<${#COVERS[@]}; i+=3)); do
  A=${COVERS[i+1]}; G=${COVERS[i+2]}
  landing_child "$L/flights/$TAG-cover-${A:17:8}.log" make cover "ATOM_ID=$A" "GID=$G"; C=$?
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

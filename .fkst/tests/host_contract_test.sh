#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
readonly PACKAGE="$ROOT/local-packages/trureturing-devtask"

fail() {
  printf 'host contract test: %s\n' "$*" >&2
  exit 1
}

python3 - "$ROOT" <<'PY'
import pathlib
import sys
import tomllib

root = pathlib.Path(sys.argv[1])
with (root / "fkst.workspace.toml").open("rb") as stream:
    workspace = tomllib.load(stream)

if workspace.get("workspace") != {"units": ["local-packages/*"]}:
    raise SystemExit("workspace must retain local-packages/* discovery")

expected_packages = [
    "github-proxy",
    "consensus",
    "github-devloop",
    "github-devloop-pr",
    "github-devloop-intake",
    "github-devloop-decompose",
    "github-devloop-intake-default",
]
expected = {
    "id": "fkst-packages-platform",
    "git": "https://github.com/ChronoAIProject/fkst-packages.git",
    "rev": "9090b5dea4ffad6ff3f0cad4a0cf7b5fcf93d549",
    "packages": expected_packages,
    "libraries": ["contract", "workflow", "testkit", "forge", "devloop"],
}
if workspace.get("external_sources") != [expected]:
    raise SystemExit("workspace external source does not match the pinned platform profile")
PY

required=(
  "fkst.lock"
  "compose/package-roots"
  "scripts/operate.sh"
  "local-packages/trureturing-devtask/fkst.toml"
  "local-packages/trureturing-devtask/raisers/dry_run_tick.lua"
  "local-packages/trureturing-devtask/departments/dry_run_guard/main.lua"
  "local-packages/trureturing-devtask/tests/dry_run_guard_test.lua"
)
for relative in "${required[@]}"; do
  [[ -f "$ROOT/$relative" ]] || fail "missing $relative"
done

[[ "$(<"$ROOT/compose/package-roots")" == "local-packages/trureturing-devtask" ]] \
  || fail "compose/package-roots must contain only trureturing-devtask"

readonly MACHINE_PREFIX="/Users/""auric"
if grep -R -n -F "$MACHINE_PREFIX" "$ROOT" --exclude='host.env' >/dev/null; then
  fail "committed .fkst source contains a machine-specific home path"
fi
grep -Fq 'command -v fkst-framework' "$ROOT/scripts/run.sh" \
  || fail "run.sh does not resolve fkst-framework from PATH"
grep -Fq -- '--local-packages "$ROOT/local-packages"' "$ROOT/scripts/run.sh" \
  || fail "run.sh does not override the nested .fkst host package base"
grep -Fq 'FKST_GITHUB_WRITE' "$ROOT/scripts/operate.sh" \
  || fail "operate.sh does not enforce dry-run posture"
if grep -Eq '(^|[[:space:]])export[[:space:]]+FKST_GITHUB_WRITE=|FKST_GITHUB_WRITE=1' "$ROOT/scripts/operate.sh"; then
  fail "operate.sh enables GitHub writes"
fi
grep -Fq 'test -e "$checkout_root/.git"' "$ROOT/scripts/operate.sh" \
  || fail "operate.sh does not require a dedicated git checkout"
grep -Fq -- '--project-root "$checkout_root"' "$ROOT/scripts/operate.sh" \
  || fail "operate.sh does not supervise from the dedicated checkout root"
if grep -Fq -- '--host-packages trureturing-devtask' "$ROOT/scripts/operate.sh"; then
  fail "operate.sh loads a nested-workspace package as a root host package"
fi

printf 'host contract tests: ok\n'

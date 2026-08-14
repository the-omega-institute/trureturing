#!/usr/bin/env bash
# 数学门(make test 的 canonical 实现):只验证 Lean 内容及其加工物的正确性与一致性,
# 不运行任何 harness 工具自身的单元测试(那是 make -C tools test 的职责)。
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
cd "$REPO_ROOT"

REPORT="$REPO_ROOT/.lake/build/stratalint/raw-lean-report.json"

lake build
make lean-report
# 干净树上 CLI 拒绝无 base 自判(候选不能自我保护);有 origin/dev 时自动锚定
# merge-base,diff 类规则(SL-008/016/022/025)也随之有意义。解不出 base(如
# 无 remote 的合成仓)则退回无 base 形态,由 CLI 自身的 fail-closed 决定去留。
CHECK_BASE_ARGS=()
if base_sha="$(git merge-base HEAD origin/dev 2>/dev/null)" && [ -n "$base_sha" ]; then
  CHECK_BASE_ARGS=(--protected-base "$base_sha")
fi
set +e
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- \
  check "${CHECK_BASE_ARGS[@]}" --candidate-lean-report "$REPORT"
check_rc=$?
set -e
# rc=3 = 纯保护面变更(SL-022 预期路径),与 CI/local gate 同语义;其余非零为真红。
if [ "$check_rc" -ne 0 ] && [ "$check_rc" -ne 3 ]; then
  exit "$check_rc"
fi
dotnet run --project tools/StrataLint.Scribe/StrataLint.Scribe.csproj --configuration Release -- \
  projections --check --report "$REPORT"
/bin/bash tools/scripts/report/report-consumer.sh --role scribe-consumer --report "$REPORT" -- \
  dotnet run --project tools/StrataLint.Scribe/StrataLint.Scribe.csproj --configuration Release -- emit --check
dotnet run --project tools/StrataLint.Scribe/StrataLint.Scribe.csproj --configuration Release -- emit-values --check
dotnet run --project tools/StrataLint.Scribe/StrataLint.Scribe.csproj --configuration Release -- describe-report --check

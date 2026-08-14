#!/usr/bin/env bash
# 数学门(make test 的 canonical 实现):只验证 Lean 内容及其加工物的正确性与一致性,
# 不运行任何 harness 工具自身的单元测试(那是 make -C tools test 的职责)。
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
cd "$REPO_ROOT"

REPORT="$REPO_ROOT/.lake/build/stratalint/raw-lean-report.json"

lake build
make lean-report
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- \
  check --candidate-lean-report "$REPORT"
dotnet run --project tools/StrataLint.Scribe/StrataLint.Scribe.csproj --configuration Release -- \
  projections --check --report "$REPORT"
/bin/bash tools/scripts/report/report-consumer.sh --role scribe-consumer --report "$REPORT" -- \
  dotnet run --project tools/StrataLint.Scribe/StrataLint.Scribe.csproj --configuration Release -- emit --check
dotnet run --project tools/StrataLint.Scribe/StrataLint.Scribe.csproj --configuration Release -- emit-values --check
dotnet run --project tools/StrataLint.Scribe/StrataLint.Scribe.csproj --configuration Release -- describe-report --check

#!/bin/bash
# preflight: 提交前一键预证 CI 双 required check 会绿(本地=CI 同一器,器之四律②)
# 覆盖 engineering check 全步骤 + baseline admission(gate);CI=true 复现 CI 独有构建属性。
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
mark() { printf '[preflight] %-22s %ss\n' "$1" "$(( $(date +%s) - T ))"; T=$(date +%s); }
T=$(date +%s)

dotnet restore Meta/StrataLint/CompileFailProof/CompileFailProof.csproj --locked-mode >/dev/null
dotnet restore Meta/StrataLint/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj --locked-mode >/dev/null
mark restore-proofs

CI=true make dotnet
mark dotnet

CI=true make test
mark test

make selftest
mark selftest

if dotnet build Meta/StrataLint/CompileFailProof/CompileFailProof.csproj --no-restore --configuration Release >/dev/null 2>&1; then
  echo "[preflight] FAIL: CompileFailProof 竟然编译通过(能力链证明失效)" >&2; exit 1
fi
if dotnet build Meta/StrataLint/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj --no-restore --configuration Release >/dev/null 2>&1; then
  echo "[preflight] FAIL: BannedApiCompileFailProof 竟然编译通过(禁 API 证明失效)" >&2; exit 1
fi
mark compile-fail-proofs

make gate BASE="${BASE:-origin/dev}"
mark gate

echo "[preflight] PASS — CI 双 required check 预证绿"

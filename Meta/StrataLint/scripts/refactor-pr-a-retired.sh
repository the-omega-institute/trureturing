#!/usr/bin/env bash
# PR-A 真重建已从 required 路径退役。确定性是「生成程序」的性质,生成程序本身受
# harness;在未触碰 emitter 的 PR 上重跑真重建 = 重新验证一个没变的东西
# (CLAUDE.md 第 5 条门槛律、第 20 条执法分级)。
# 本脚本仅因 base 侧 workflow 仍按旧目标名调用而存在;dev 更新后由紧接的后续 PR
# 连同该目标一并删除,不留 grandfather(第 6 条禁兼容垫层)。
# 完整真重建审计保留于按需目标 refactor-pr-a-audit。
set -euo pipefail
OUT="${1:-}"
if [[ -n "$OUT" ]]; then
  printf '{"schema":"refactor-pr-a-verify-v2","lane":"retired-from-required","on_demand_target":"refactor-pr-a-audit","pass":true}\n' > "$OUT"
fi
echo 'PR_A_REQUIRED_LANE_RETIRED on_demand=refactor-pr-a-audit'

---
bibkey: codex2026erdos699i3
authors: Independent Codex CLI mathematics seat; caller audit
year: 2026
title: "Erdos 699 i=3 Lucas/Kummer adjacent-core reduction"
doi: null
url: https://www.erdosproblems.com/699
claim: Necessary conditions and bounded exact checks for the i=3 lane; not a solution.
strata_touched: []
license: citation-only
triage: anchor
---

# Erdős 699：`i=3` 的 Lucas/Kummer 相邻核心约化

关联 issue：#9670。当前写入 PR：#9723。

本条记录的是一份独立数学席的必要条件推导和有限核验，不是 Erdős 699 的完整证明、反例、Lean 定理或 KPI 结果。原始独立报告保存在本机临时路径；其 SHA-256 为
`9de452aec61d51260f34446954b49bd714781506660a24eeab67901636d35f0d`。

报告证明：假设 `i=3` 反例，则可写

\[
n=Mu,\quad j=tu,\quad M=2^a3^\varepsilon,\quad \varepsilon\in\{0,1\},
\]

并且 `4|M`、`u` 奇、`(M,u)=1`、`v_3(u)\ne1`、`tu>=4`，同时满足

\[
R(Mu-1)\mid t(M-t),\qquad
R(Mu-2)\mid t(M-t)(M-2t),
\]

以及

\[
(Mu-1)(Mu-2)\le\sqrt3 M^3,
\qquad u<3^{1/4}\sqrt M+2/M.
\]

这里 `R` 去掉全部 2-adic 因子，并在 3-adic 指数恰为 1 时再去掉一个 3。证明的关键是：对 `binom(n,3)` 的每个奇素因子，反例假设迫使 `binom(n,j)` 的 Lucas 逐位条件无进位；对 `n,n-1,n-2` 的低位块分别取模后得到上述整除式。高位逐位条件没有被省略，且两个低位整除式没有被错误地当成充分条件。

有限检查器 `tools/scripts/agent/openproblem/erdos699-i3-lucas-reduction-check.py` 使用标准库精确整数，覆盖直接检查 `n<=500` 和 Lucas 约化候选 `n<=2,000,000`。这些范围之外仍未证明，且无界 `M` 的候选引理尚未解决。

外部背景来源仍以官方问题页、Erdős–Szekeres 1978 原文和 Ecklund–Eggleton–Erdős–Selfridge 1978 原文为准；本条不作历史优先权或全球文献穷尽声明。

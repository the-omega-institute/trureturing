---
bibkey: bugeaudevertsegyory2017sparts
authors: Yann Bugeaud, Jan-Hendrik Evertse, Kálmán Győry
year: 2017
title: "S-parts of values of univariate polynomials, binary forms and decomposable forms at integral points"
doi: null
url: https://arxiv.org/abs/1708.08290
claim: Theorem 2.1(i) bounds the S-part of values of a squarefree univariate polynomial with an ineffective constant; used in the written fixed-index finiteness argument for Erdős 699.
strata_touched: []
license: citation-only
triage: anchor
---

# Erdős 699：四次消去与 S-part 外部依赖

研究关联：issue #9670，PR #9723。
唯一推导正文：`docs/develop/theory/ERDOS_699_BINOMIAL_COMMON_PRIME.md`，§§16–19。
本条保存来源与精确使用边界，不登记 Lean/Scribe 真值或开放问题解决状态。

## 1. 有限性所用的已知定理

Yann Bugeaud, Jan-Hendrik Evertse, Kálmán Győry,
*S-parts of values of univariate polynomials, binary forms and decomposable forms at integral points*，arXiv:1708.08290。

- 元数据：https://arxiv.org/abs/1708.08290
- 全文：https://arxiv.org/pdf/1708.08290
- 核对日期：2026-09-24。
- 实际读取并截图核对：印刷页 3 Theorem 2.1(i)，印刷页 13 Proposition 3.1 及 Theorem 2.1 的证明。Introduction 明确区分非有效估计与另一条较弱的有效估计。

若 `f in Z[X]` 无重根、次数 `r>=2`，`S` 是有限非空素数集，则对每个 `eta>0`，

    [f(x)]_S <= C(f,S,eta) * |f(x)|^(1/r+eta),  f(x)!=0.

这里 `[m]_S` 保留 `S` 中素数的完整幂。常数非有效，来源是 p-adic Thue–Siegel–Roth；不能用另一条有效估计的常数代替它，也不能将它说成一个已经计算出的搜索截止。

**本卷的应用，而非原文结论：** 固定 `i>=4`，取 `f_i(X)=prod_(r=0)^(i-1)(X-r)`、`S_i={p prime:p<i}`、`eta=1/(12i)`。假想反例满足 `g_i <= [f_i(n)]_(S_i) <= C_i*n^(13/12)`。与自行推导的四次界 `n^7<4000*binom(i,4)^6*g_i^6` 联立，得到 `n<4000^2*(binom(i,4)*C_i)^12`，证明固定指标反例有限。常数 `C_i` 未计算，有限集合未排空。结合本卷先前的大指标定理，只能推出 `i!=3` 的反例总集有限，不能宣布整题或所有 `i>=4` 无反例。

## 2. 相关既有方法与比较

George M. Bergman, *On common divisors of multinomial coefficients*，arXiv:0806.0607v2。

- 元数据：https://arxiv.org/abs/0806.0607
- 全文：https://arxiv.org/pdf/0806.0607
- 实际核对：§2，印刷页 2–3，Theorem 2 及其后关于更多轨道数量组合消去的讨论。

Bergman 已给出固定 `i>=2` 的 gcd 平方根量级下界，并提出改进 `i>=4` 时的高阶组合。这是已有工作。当前卷的具体代数命题是四次整系数表达式 `J^2-2I^3` 的严格正性和 `O(h^6/n^7)` 界，以及保留原 gcd 的除阶乘导数传递。它们的证明见理论卷，不依赖把 Bergman 的建议当成一个已证明的更强估计。

## 3. 核验边界

检查器：`tools/scripts/agent/openproblem/erdos699-quartic-cancellation-check.py`。
精确整数/有理数和可选 SymPy 只检查代数恒等式及实际参数，不重新证明外部 S-part 定理，不产生未知的 `C_i`，不进行独立审稿或 Lean 核验。已有外部有限性草稿没有在本轮独立复核，故不作历史优先权主张。

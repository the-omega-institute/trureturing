---
bibkey: dusart2010estimates
authors: Pierre Dusart
year: 2010
title: "Estimates of Some Functions Over Primes without R.H."
doi: null
url: https://arxiv.org/abs/1002.0442
claim: Explicit prime-counting and prime-in-short-interval estimates used as external inputs in the Erdős 699 continuation.
strata_touched: []
license: citation-only
triage: anchor
---

# Erdős 699：显式素数估计的来源与用途

研究关联：issue #9670，Draft PR #9723。
唯一推导正文：`docs/develop/theory/ERDOS_699_BINOMIAL_COMMON_PRIME.md`，尤其 §§12–15。
本条仅保存外部依赖的来源与使用边界，不登记 Lean 定理，不宣告开放问题解决，不充当 Scribe 的形式化证明收据。

## 主来源

Pierre Dusart, *Estimates of Some Functions Over Primes without R.H.*, arXiv:1002.0442v1，2010-02-02。

- 元数据：https://arxiv.org/abs/1002.0442
- 全文：https://arxiv.org/pdf/1002.0442
- 本轮检索日期：2026-09-24。
- 已实际读取正文，并检查 PDF 第 8、9 页的页面图像，核对以下常数、上下端点、自然对数的平方和适用范围。

Proposition 6.8，印刷页 8：当 `x >= 396738`，存在素数 `p`，满足

    x < p <= x * (1 + 1/(25*(log x)^2)).

Theorem 6.9，式 (6.5)，印刷页 9：当 `x > 1`，

    pi(x) <= x/log(x) * (1 + 1.2762/log(x)).

两者均按该文无 RH 假设的已知定理使用，未由本项目本轮重新证明。检查器只核对应用过程的精确有理常数，不能认证整个外部定理。

## 具体使用位置

理论卷定理 12.1 从整系数轨道多项式的根方差和正整数判别式，自行推导 `g^4*i^i >= (2*(n-1))^i`，不使用本来源。

§13 对假想反例用 `g <= n^pi(i-1)`。上面的素数计数估计证明每个 `i >= 121` 都具有显式有限行上界；对于 `i >= 400000`，更推出 `n < 512*i`。再把短区间定理应用于 `x=n-i`，取得同时整除两个二项式的素数，完成这个大指标区域的书面证明。

400000 是本轮证明给出的保守显式阈值，不声称最优，也不声称原题其余区域已被排除。本轮未取得 Rosser–Schoenfeld 1962 原始全文；因此它未被当成已核验的替代前提。外部数学结果的历史归属保留给原作者，当前推导无文献优先权主张。

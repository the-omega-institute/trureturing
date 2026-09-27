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

## 2026-09-24 续接：全部 i>=325 的区域定理

原 #9723 已合并，本次在同一理论卷追加 §§25–28。两个 Dusart 定理重新读取并截图核对原文印刷页 8–9。它们仍是仅有的解析数论外部前提。

§25 先证明经典 Hermite/Vandermonde 极值公式的当前归一化版本，从而对 `i>=256` 得 `g_i^4*i^i>[6(n-1)]^i`。Hermite 背景参考是 NIST DLMF §18.9，https://dlmf.nist.gov/18.9 ，已读取其递推与导数部分。该网页只作背景来源；首一 He 的递推、微分方程、resultant 判别式递推和极值证明均写在 §25.1，不将物理学归一化的 Hermite 公式误作本式，也不对经典极值事实主张优先权。

对 `i>=3000`，Dusart 素数计数上界与新判别式界给出 `n<2048*i`。当 `x=n-i>=396738`，短区间定理给出 `n-i<p<n`。较小 x 的情形以及全部 `325<=i<=2999`，由明确的整数幂比较归约到 `n<2^31`，再使用 §26 的完整有限素数间隙证书。两套实际执行的确定性分段筛均得到 `pi(2^31)=105097565`、下一个素数 `2147483659`、最大间隙 `292`，最大间隙端点 `1453168141,1453168433`。

这个区域定理同时包含书面推导与明确使用的有限计算引理。它不是对原题三元组的有限采样，也没有证明 `3<=i<=324` 的剩余情形。有限比较2675项、两套全区间筛和程序哈希均在 §28 记录；它们未被称为独立数学评审或 Lean 核验。数值292是本轮完整筛的结果，不是从外部网页抄录的定理前提。没有新增 Scribe 数学真值或解决计数。

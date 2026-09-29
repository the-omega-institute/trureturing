---
bibkey: "ferre2012limit"
authors: "Déborah Ferré; Loïc Hervé; James Ledoux"
year: 2012
title: "Limit theorems for stationary Markov processes with L2-spectral gap"
doi: "10.1214/11-AIHP413"
url: "https://arxiv.org/abs/1201.4579v1"
claim: "Theorems 4.3–4.4 give a first-order nonlattice Edgeworth expansion for stationary Markov additive processes, including continuous time, under a spectral gap and a moment of order greater than three."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Limit theorems for stationary Markov processes with L2-spectral gap

发表于 *Annales de l'Institut Henri Poincaré, Probabilités et Statistiques*
48(2) (2012)。作者、标题、卷期和 DOI 与 Crossref 记录相符。
使用的原始全文是 arXiv:1201.4579v1；定位为假设 AS1–AS3、§4.3.1
的非格点条件、定理 4.3 的式 (4.7)，以及 §4.5 的定理 4.4。
这些是一般概率结果，属于 `literature-attested`。

定理 4.3 假设驱动链平稳、在平稳测度的平方可积空间上具有谱隙，
加性分量有某个大于三阶的矩，渐近方差为正，并满足 Markov 非格点条件。
其一阶分布函数修正具有形式

```math
\Phi(x)+\frac{\mu_3}{6\sigma^3\sqrt n}(1-x^2)\varphi(x)
 +o(n^{-1/2}).
```

定理 4.4 将该结论扩展到实际连续时间，矩条件改为单位时间区间内的统一矩界。
非格点条件仅给出每个避开零点的紧频率集上的指数衰减；不要求特征函数在无穷远
一致远离一。大于三阶的矩条件对下面的有界跳幅 Poisson 和自动成立，
不将本引用表述为仅有三阶矩时的最优一般定理。

在两跳幅复合 Poisson 特例中，驱动空间取单点，驱动半群与平稳投影相同。
中心化加性分量是具有独立平稳增量的过程，而不局限于驱动状态的确定性积分。
固定跳幅为 $`h_\pm=\log(1\pm r)`$，两类强度为 $`(1\pm r)/2`$。
单位时间增量在零及两个跳幅上有正质量；跳幅比无理时不落入任何平移格点。
中心化不改变这一性质。方差率和第三累积量率分别为

```math
v=\frac{(1+r)h_+^2+(1-r)h_-^2}{2},\qquad
m_3=\frac{(1+r)h_+^3+(1-r)h_-^3}{2}.
```

第三累积量率使用跳幅的原始三阶矩。此直接特例只提供比较律中的概率展开。
[恢复卷第 25 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_RECOVERY.md#25-非格点得分的显式-hamming-风险系数)
还需保留实际中心、控制补偿误差、转移实际依赖行的矩，并证明固定基数后验的风险等价。
原文不提供这些模型结论、支持恢复系数、格点相位修正或关于无理跳幅比的统一收敛速率。

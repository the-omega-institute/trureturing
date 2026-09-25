---
bibkey: "borcea2009negative"
authors: "Julius Borcea; Petter Brändén; Thomas M. Liggett"
year: 2009
title: "Negative dependence and the geometry of polynomials"
doi: "10.1090/S0894-0347-08-00618-8"
url: "https://arxiv.org/abs/0707.2340v2"
claim: "Corollary 4.17 includes the classical Newton inequalities for elementary symmetric polynomials; these imply pairwise negative covariance for a fixed-size product-weight posterior."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Negative dependence and the geometry of polynomials

发表于 *Journal of the American Mathematical Society* 22(2), 521–567 (2009)，
DOI 与 Crossref 条目相符；该条目另列在线发表日期为 2008-09-19。
直接核对的原始全文是 arXiv:0707.2340v2，2008-07-27，共 47 页。

此处只需要经典 Newton 不等式这一既有工具。原文 §3.1 第 14 页讨论
实根多项式的 Newton 不等式；第 28 页推论 4.17 的式 (13) 给出包含它的推广，
并明确指出取各个一次因子的乘积时回到经典情形。
对正权重的基本对称多项式，这蕴含

```math
e_k^2\ge e_{k-1}e_{k+1}.
```

实际 Newton 界对二项式系数归一化后的序列成立，比这里需要的界更强。
相邻指标越出取值范围时，将相应对称多项式记为零。

固定基数的权重乘积概率律有后验指示量总和恒定这一额外条件。
删去两个权重后，展开两者的包含概率和联合包含概率，Newton 界直接给出
它们的协方差非正。再利用每行协方差之和为零，得到任意实系数的方差界

```math
\mathrm{Var}\left(\sum_i c_i I_i\right)
 \le 2\sum_i c_i^2\mathrm{Var}(I_i).
```

这些是已知不等式在条件 Bernoulli／固定基数权重律中的后果，属于
`literature-attested` 工具应用。这里并不把一般负依赖理论作为新结果。
原文定理 4.9 证明更强的负关联性质，推论 4.18 处理长度至多一的基数截断；
上述方差估计只需两点协方差，无须借用全部强 Rayleigh 理论。

本来源不提供实际平稳对／路径数据的行计数近似、参数随维数变化的风险误差、
确定阈值与极小极大规则的平方根尺度比较，或两个 Hamming 损失的联合中心极限。
这些需要另外证明共同实现、边界选择、均值转移及方向判错率。

## Conditional rank-interval concentration

The functional budget comparison uses a stronger classical consequence of the
same source. In the checked arXiv:0707.2340v2, the discussion on printed pages
18–19 states closure of stable polynomials under differentiation and real
specialization. Theorem 4.9 on printed page 24 proves that a strongly Rayleigh
measure is conditionally negatively associated after external fields (CNA+).
In particular it is negatively associated.

For positive weights, the generating polynomial of a fixed-size product-weight
law is an elementary symmetric polynomial after coordinate rescaling. It is
obtained from the product of the linear factors t+w_i z_i by differentiation in
t and evaluation at zero. Stability therefore verifies the theorem's hypothesis;
this is not a claim that arbitrary fixed-cardinality laws are negatively associated.
The resulting exponential-moment product bound for every fixed set yields
Chernoff concentration. These are `literature-attested` auxiliary tools.

In the actual budget-process proof, the data and tie priorities must first be
conditioned on, making the candidate rank intervals and their maximum allowed
length fixed. The union bound over those intervals controls the maximum hidden
label count. Pairwise covariance alone would not justify that exponential bound,
and an expected maximum cannot be replaced by a maximum of conditional means.
The actual dependent-count supremum bound, score-band localization and uniform
risk-center transfer are separate model-specific obligations.

Theorem 29.2 of the parity fluctuation volume is `repo-derived`: the new
content is the actual dependent-row uniform comparison and its posterior
label transfer to an exactly centered budget process. Negative association,
Chernoff bounds and empirical-bridge convergence retain their classical status;
no general probability theorem or global originality claim is made.

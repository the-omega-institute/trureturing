---
bibkey: "boistard2012rejective"
authors: "Hélène Boistard; Hendrik P. Lopuhaä; Anne Ruiz-Gazen"
year: 2012
title: "Approximation of rejective sampling inclusion probabilities and application to high order correlations"
doi: "10.1214/12-EJS736"
url: "https://arxiv.org/abs/1207.5654v1"
claim: "Lemma 1 and formula (2.10) provide uniform central conditioning ratios for independent Bernoulli arrays whose total variance diverges, without requiring each parameter to stay away from zero and one."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Approximation of rejective sampling inclusion probabilities and application to high order correlations

发表于 *Electronic Journal of Statistics* 6 (2012)。作者、标题、卷和 DOI 与
Crossref 记录相符。使用的原始全文是 arXiv:1207.5654v1，具体定位为 §2
的式 (2.1)、(2.5)、引理 1 和式 (2.10)–(2.11)，以及 §4.1 的证明。
条件 Poisson／拒绝抽样表示、局部展开和包含概率近似均为 `literature-attested`；
该文将这些方法与 Hájek 的早期工作相接。

设独立 Bernoulli 变量参数为 $`p_i`$，总均值为整数 $`n`$，总数为
$`K`$，总方差为 $`d_B=\sum_i p_i(1-p_i)`$。
引理 1 在总方差趋于无穷时，分别展开中心总数概率及固定若干坐标成功条件下的
中心总数概率。对单个坐标，式 (2.10) 直接给出

```math
\frac{\mathbb P\{K=n\mid I_i=1\}}{\mathbb P\{K=n\}}
 =1+O(d_B^{-1}),
```

对所选坐标一致。其展开系数由有界的 Bernoulli 参数及加权平均构成。
对互补数组应用同一结果，得到条件于该坐标失败的对应比例。
若各参数严格介于零与一，则两式相除可得

```math
\frac{\mathbb P\{K-I_i=n-1\}}{\mathbb P\{K-I_i=n\}}
 =1+O(d_B^{-1}).
```

不要求各参数统一远离端点；这控制的是相对概率比，而非只有包含概率的绝对误差。
§3 为高阶相关性的特定应用另外引入坐标数与总方差之比有界的条件 (3.1)。
这里使用的引理 1 和 §2 的单坐标条件化不依赖该附加条件。
特别是总方差仅为稀疏基数的数量级时，不能把 §3 的条件默默当作已经满足。

固定基数乘积权重分布可写成独立 Bernoulli 数组在总数固定条件下的分布，
公共指数倾斜不改变这个条件分布。此代数本身也是已知表示。
[恢复卷第 25 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_RECOVERY.md#25-非格点得分的显式-hamming-风险系数)
将它用于全部观测给定后的辅助后验；它没有使实际路径观测或实际行计数独立。
使用相邻比例前，必须先在实际模型中证明公共倾斜参数接近一及辅助总方差增长，
还必须将后验阈值误差转成期望 Hamming 损失。
这些集中与风险步骤不由本论文提供。

有限基数 Hamming 后验判别另见
[Butucea–Mammen–Ndaoud–Tsybakov](butucea2023selection.md)。
这里不将条件独立表示、后验赔率或已知局部极限定理认作本仓的新一般定理；
新增内容限于实际补偿对／路径实验中的风险精度。

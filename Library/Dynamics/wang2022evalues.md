---
bibkey: "wang2022evalues"
authors: "Ruodu Wang; Aaditya Ramdas"
year: 2022
title: "False discovery rate control with e-values"
doi: "10.1111/rssb.12489"
url: "https://arxiv.org/abs/2009.02824v5"
claim: "The basic e-BH step-up rule controls FDR for arbitrarily dependent e-values; the actual compensated-path Hamming theorem additionally requires signal power and expected false-discovery-count bounds."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# False discovery rate control with e-values

期刊书目信息为 *Journal of the Royal Statistical Society, Series B* **84**(3)
(2022)，822–852，DOI [10.1111/rssb.12489](https://doi.org/10.1111/rssb.12489)。
作者、标题、卷期、页码和 DOI 与 Crossref 记录相符。
以下逐条引用的原始正文为 32 页的
[arXiv:2009.02824v5](https://arxiv.org/abs/2009.02824v5)：
arXiv 版本标记日期为 2021 年 12 月 15 日，首页正文署期为 12 月 16 日。

## 基本规则及其精确前提

第 1 页的定义将 e-variable 取为在相应零假设下期望不超过一的非负随机变量；
e-value 是其观测值。似然比、非负超鞅和确定权重的算术平均都是文中讨论的来源，
其中平均的有效性不要求各项独立，见第 4 页关于组合的讨论。

第 8 页 §4.1 式 (5) 将 $`K`$ 个输入按降序排列，并定义

```math
R=\max\left(\{0\}\cup
 \left\{k\in\{1,\ldots,K\}:E_{[k]}\ge\frac K{\alpha k}\right\}\right).
```

基本 e-BH 规则选择最大的 $`R`$ 个输入。这里引用不作 boosting 的基本规则。
第 9 页定理 2、命题 2 及式 (12) 的证明给出：若 $`K_0`$ 个真零假设的输入
在其实际共同概率律下满足 $`\mathbb E E_i\le1`$，则不论依赖结构如何，

```math
\mathrm{FDR}
=\mathbb E\frac{F}{R\vee1}\le\frac{\alpha K_0}{K}\le\alpha.
```

证明使用每个所选输入满足 $`E_i\ge K/(\alpha R)`$，从而逐观测有
$`F/(R\vee1)\le(\alpha/K)\sum_{i\text{ true null}}E_i`$。
这项结论的期望前提必须针对实际概率律成立；仅在辅助近似律下成立不能自动代入。

## 对补偿核自适应恢复的适用边界

[支持恢复卷第 22 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_RECOVERY.md#22-未知振幅基数与方向的自适应-hamming-窗口)
采用该基本阈值形式及似然混合原则，不将二者作为新算法或新一般理论。
章内先通过一步条件期望核对实际正向背景行的非负超鞅性质和反向行的均值一鞅性质，
再取振幅网格混合，因此满足上述期望前提。

FDR 是期望错误比例，不能单凭该界就推出期望误选个数为 $`o(q)`$，
因为随机选择数可能远大于真实支持大小。该章另外使用同一实际支持下的两行方差估计，
按选择数量作二进分段，控制期望误选个数与反向选择集的期望大小；
结合信号中心极限，才得到未知振幅、基数和方向时的 Hamming 临界曲线。
这部分实际补偿模型的组合推导属于本仓结果，原论文的任意依赖 FDR 定理不自动提供它。

期望误选个数作为自适应 Hamming 证明条件已有直接先例：
[Abraham–Castillo–Roquain](abraham2024sharp.md) 的 arXiv:2109.13601v2
第 52–53 页引理 S-9、式 (S-24) 在其独立序列 BH 设置中给出

```math
\mathbb E V\le\frac{\alpha}{1-\alpha}|S|
 +\frac{\alpha}{(1-\alpha)^2}.
```

其证明将非零坐标设为无穷，再使用独立零假设下的 step-up 分布计算。
第 22 章不能将这一独立序列公式直接用于依赖行；它另用实际两行比较控制随机选择数。
因此，区分 FDR 与误选个数、以及自适应 Gaussian Hamming 曲线均不作为本仓新原则。

本文献不被用于宣称第 22 章的 Hamming 极限对变动振幅、非平稳起点或任意无限偏移一致成立。
这里的版本和引用范围也不构成全球原创性声明。

---
bibkey: "bobkov2022chebyshev"
authors: "Sergey G. Bobkov; Vladimir V. Ulyanov"
year: 2022
title: "The Chebyshev–Edgeworth correction in the central limit theorem for integer-valued independent summands"
doi: "10.1137/S0040585X97T990605"
url: "https://www-users.cse.umn.edu/~bobko001/papers/2022_TVP-SIAM_BU_Chebyshev-Edgeworth_With.pages.pdf"
claim: "Section 3, formula (3.2), restates the classical uniform first Edgeworth expansion at integer lattice boundaries with the half-unit continuity correction."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# The Chebyshev–Edgeworth correction in the central limit theorem for integer-valued independent summands

使用的原始全文是作者主页所存的 *Theory of Probability and Its Applications*
66(4), 537–549 (2022) 出版社版本。作者、标题、卷期、页码及 DOI 与正文和
Crossref 元数据相符。该文是俄文 2021 年版本的作者英译。
本引用定位于第 538 页的式 (1.3)、第 539–540 页的 §3，尤其是式 (3.2)。

对独立同分布、最大格距为一的整数随机变量之和，设总均值为
$`\mu`$、总方差为 $`\sigma^2`$，并有有限三阶绝对矩。
式 (1.3) 定义的一阶修正为

```math
\Phi_3(x)=\Phi(x)+\frac{\mathbb E(S_n-\mu)^3}{6\sigma^3}
 (1-x^2)\varphi(x).
```

式 (3.2) 给出对所有整数端点一致的展开

```math
\mathbb P\{S_n\le k\}
 =\Phi_3\!\left(\frac{k+1/2-\mu}{\sigma}\right)+o(n^{-1/2}).
```

这是 Esseen 的经典格点展开的重述，属于 `literature-attested`。
原文将一般周期修正定位到 Esseen 的定理 3，并在整数端点处化为半格距形式。
此处直接核对的是 Bobkov–Ulyanov 的原始出版正文，不把未读取的早期论文标为已读。
不需要借用该文后续为非同分布情形建立的更强结果。

对最大格距为 $`h`$ 的未中心化随机变量，先除以格距再使用该式。
在严格边界 $`b\in h\mathbb Z`$ 上，事件小于边界等于不超过前一个格点，
所以连续性修正是将边界减去半格距。
对两跳幅复合 Poisson 过程，单位时间增量有任意阶矩，最大格距由两个整数跳幅的
最大公因数决定。实数时间可拆为整数时间及独立的不足一单位时间余项；
余项仍在同一格点上，条件化后边界仍是格点。
统一余项、余项的有界矩以及中心化后的零均值允许将整数时间公式转到实际时间。

本工具控制比较律的格点分布函数；它不直接控制补偿后得分跨越格点时的分布函数差。
即使补偿趋零，个别原子仍可穿过一个非常接近的阈值。
实际补偿对／路径实验的 Hamming 风险需要另外使用损失加权的后验比较、
连续截断似然损失和同分排序的后验误差界。
支持约束的周期系数还需要将恰好基数输出与期望基数匹配的随机规则作比较。
这些模型结论、相位一致性及固定基数极小极大解释不包含在本论文的式 (3.2) 中。

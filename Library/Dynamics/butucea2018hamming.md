---
bibkey: "butucea2018hamming"
authors: "Cristina Butucea; Mohamed Ndaoud; Natalia A. Stepanova; Alexandre B. Tsybakov"
year: 2018
title: "Variable selection with Hamming loss"
doi: "10.1214/17-AOS1572"
url: "https://arxiv.org/abs/1512.01832v5"
claim: "The pinned preprint separates almost-full and exact recovery in the sparse Gaussian sequence model through different Hamming-risk thresholds; its exact expected-loss criterion must not be replaced by a probability-one failure assertion."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Variable selection with Hamming loss

期刊书目信息为 *The Annals of Statistics* **46**(5), 1837–1875 (2018)，
DOI [10.1214/17-AOS1572](https://doi.org/10.1214/17-AOS1572)。
作者、标题、期刊、卷期、年份及 DOI 有 Crossref 书目记录对应。
本文逐条讨论的原始正文为 43 页的
[arXiv:1512.01832v5](https://arxiv.org/abs/1512.01832v5)。首页边栏标明版本日期
2018 年 10 月 12 日；标题下另显示 2018 年 10 月 15 日，二者不混同。
下述定理与公式编号均定位于 v5，不作期刊最终正文与预印本逐字一致的断言。

## 模型、损失与两个阈值

第 1 节的高斯序列模型为独立噪声下的
$`X_j=\theta_j+\sigma\xi_j`$。参数类限制至多 $`s`$ 个非零坐标，且非零幅度
与零分离。选择器可输出任意二元向量；Hamming 风险并未限制输出基数。
第 3.2 节还讨论独立非高斯坐标的似然比选择，这些背景不构成对任意相关路径的
现成支持恢复定理。

第 4 节区分归一化 Hamming 风险趋零的几乎全恢复与未归一化期望 Hamming
损失趋零的精确恢复。定理 4.3 及式 (39)（第 15 页）给出几乎全恢复的
一阶幅度尺度

```math
a_A=\sigma\sqrt{2\log((d-s)/s)}\,(1+o(1)).
```

其中定理规定相应稀疏参数类、阈值裕量及极限条件；定理 4.3 的反向结论是
极小极大归一化风险具有正的下极限，不应未经额外论证加强为风险趋于一。
定理 4.4 及式 (43)（第 16–17 页）给出精确恢复的一阶幅度尺度

```math
a_E=\sigma\left(\sqrt{2\log(d-s)}+\sqrt{2\log s}\right),
```

这里要求支持大小增长，并保留该定理的稀疏性条件与上下侧裕量。
在 $`s=d^{1-\beta+o(1)}`$ 下，用 $`a^2/(2\sigma^2\log d)`$ 度量强度，
这两条界分别成为

```math
\beta,\qquad (1+\sqrt{1-\beta})^2.
```

这是已有的高斯支持恢复相图，不能把在别的模型中出现相同标量极限当作新的一般原则。

## 不能替换的概率结论

该处精确恢复的上侧为
$`\sup_\theta\mathbb E_\theta|\widehat S\triangle S|\to0`$，它蕴含错误支持
概率趋零。下侧陈述未归一化期望损失发散；由于损失上界也随维数增长，
这本身不蕴含错误支持概率趋于一。要取得后一结论，须另证错误事件概率趋一，
例如在同一实际概率律下证明背景极大值得分超过信号极小值得分。

在补偿奇偶核中，几乎全恢复界与精确恢复界的小振幅标量曲线若分别收敛到上述
高斯常数，这只说明固定振幅相界作为函数的端点一致性。
它不提供 $`r=r_d\to0`$ 时的一致尾估计或路径传递，也不证明未知
$`q,r`$ 的适应性。固定支持大小、真实路径依赖、未知方向及两种不同
Hamming 归一化，都须由对应模型的证明单独处理。

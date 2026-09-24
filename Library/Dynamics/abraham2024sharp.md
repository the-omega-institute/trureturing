---
bibkey: "abraham2024sharp"
authors: "Kweku Abraham; Ismaël Castillo; Étienne Roquain"
year: 2024
title: "Sharp multiple testing boundary for sparse sequences"
doi: "10.1214/24-AOS2404"
url: "https://arxiv.org/abs/2109.13601v2"
claim: "Theorem 7 of the pinned preprint gives the Gaussian critical minimax Hamming profile for independent sparse normal means; it does not supply the actual compensated stationary pair or Markov path comparison."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Sharp multiple testing boundary for sparse sequences

期刊书目信息为 *The Annals of Statistics* **52**(4) (2024)，
DOI [10.1214/24-AOS2404](https://doi.org/10.1214/24-AOS2404)。
作者、标题、卷期、年份和 DOI 与 Crossref 对应记录一致。
以下逐条引用的原始正文为 86 页的
[arXiv:2109.13601v2](https://arxiv.org/abs/2109.13601v2)，首页标明
2023 年 8 月 30 日；不以期刊元数据代替对该版本定理条件的核对。

## 独立高斯模型与 Hamming 临界轮廓

第 4 页例 1 观察独立坐标
$`X_i=\theta_i+\epsilon_i`$，其中 $`\epsilon_i\sim N(0,1)`$。
全篇的稀疏渐近条件 (3) 为
$`N\to\infty`$、$`s_N\to\infty`$ 与 $`N/s_N\to\infty`$。
这里将论文的环境维数记为 $`N`$，以免与奇偶核的状态空间大小混淆。
第 9 页式 (9)–(10) 用非零均值的绝对值下界定义 beta-min 类。
第 22 页式 (31) 将支持大小从恰好 $`s_N`$ 扩为至多 $`s_N`$：

```math
\Theta'_b
=\left\{\theta\in\mathbb R^N:
 |\operatorname{supp}\theta|\le s_N,\quad
 |\theta_i|\ge\sqrt{2\log(N/s_N)}+b
 \text{ whenever }\theta_i\ne0\right\}.
```

第 22 页定理 7 对任意固定实数 $`b`$，以及趋于正负无穷的偏移序列，给出

```math
\inf_{\widehat S}\sup_{\theta\in\Theta'_b}
 \frac{\mathbb E_\theta|\widehat S\triangle\operatorname{supp}\theta|}{s_N}
=\overline\Phi(b)+o(1)=\Phi(-b)+o(1).
```

下确界遍历全部选择规则。补充材料 §S-6.3 的证明已经在恰好 $`s_N`$ 个信号的子类上取得下界，
所以固定基数本身也不是新内容。这里 $`\Phi`$ 是标准正态下分布函数，
$`\overline\Phi=1-\Phi`$；论文第 9 页分别定义二者。
原文定理中的上横线决定风险随信号增大而下降，不能因文本提取丢失横线而改读为下分布函数。

同一定理另给 BH 与经验 Bayes $`\ell`$-value 程序的适应性结论，二者的条件分别陈述。
经验 Bayes 程序 (S-29) 使用任意固定阈值 $`t\in(0,1)`$；
BH 程序另要求第 11 页 (12) 的多项式稀疏性
$`s_N\lesssim N^\eta`$（某个 $`\eta\lt1`$），以及名义水平
$`\alpha_N=o(1)`$、$`-\log\alpha_N=o(\sqrt{\log N})`$。
这一条件分工由定理 2、定理 7 及 §S-6.3、§S-8.1 的定义与证明共同给出。
这些附加条件不属于前一条基本极小极大风险陈述，也不能一并归给两个程序。

## 对补偿奇偶核支持恢复的适用边界

[支持恢复卷第 21 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_RECOVERY.md#21-几乎全恢复的高斯窗口与支持基数的二阶偏移)
使用上述结果作为高斯 Hamming 轮廓的直接先例。高斯函数本身并非该章的新发现。
两者的统计实验与参数类不同：文献观察独立单位方差高斯坐标，允许至多给定数量的非零均值；
奇偶核观察均匀平稳相邻对或一条连续路径，支持大小恰为给定值，背景含保持平稳性的补偿，
并可同时不知道时间方向。

因此，文献定理不自动给出实际路径的单行与双行稀有事件估计、补偿似然比、完整观测后验，
或未知方向下有界输出的 Hamming 损失控制。第 21 章将这些模型关系组合后得到的
临界中心 $`\log(M/q)/\phi(r)`$ 与实际极小极大窗口，属于本仓推导。
此处的来源核对限定于上述原始版本与结论，不构成全球原创性声明。

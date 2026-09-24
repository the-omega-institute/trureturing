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

## 固定基数块先验及其使用范围

同一 arXiv v2 第 27 页 §8.1 在互不相交的块内各均匀选择一个非零坐标，
剩余坐标固定为零。先验的支持基数精确固定。该页在独立序列模型中写出
块内信号的后验概率为本坐标似然比除以本块所有似然比之和；式 (35) 随后以
块内较大背景分数的个数控制漏检。因此，“每块一信号”的先验和相应后验形式是既有方法。

[支持恢复卷第 23 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_RECOVERY.md#23-两种-hamming-风险在共同极限之下的分离)
使用该先验原则，并从实际补偿路径的完整似然重新核对块后验的因式分解。
它另对同一实际支持下的截断背景权重之和作矩估计，取得所需的
$`O(\lambda^{-1/2})`$ 下界误差，再与排序阈值的对数修正比较。
原论文的这一先验构造不等于已经证明该依赖观测模型的定量风险差；
本仓也不将块先验或 Bayes 阈值作为新的一般原理。

## 固定输出基数的一阶风险先例

同一版本第 65 页推论 S-3，在定理 3 的独立高斯边界模型、固定实数
$`b`$ 与恰好 $`s_N`$ 个信号的类上，讨论按绝对观测值取最大的
$`s_N`$ 项。其最坏原始 Hamming 损失除以 $`s_N`$ 渐近等于
$`2\overline\Phi(b)`$。第 72 页 §S-9.8 的证明利用该规则逐观测的
误选数等于漏选数，结合定理 S-8 的阈值比较上界与定理 3 的漏检下界。
因此再将这条风险除以二，便得到与无约束 Hamming 风险除以信号数相同的一阶曲线。
共同的一阶曲线和固定基数造成误选、漏选相等这两点，均有明确的文献先例。

第 23 章只把较细的实际模型结论作为本仓推导：在平稳相邻对与连续路径的补偿律下，
保持实际中心 $`\log(M/q)`$ 后，两个不同归一化风险的差具有
$`\log\lambda/\sqrt\lambda`$ 的显式主项，分别保留
$`O(\lambda^{-1/2})`$ 的余项，并涵盖固定的格点振幅与未知方向。
推论 S-3 本身没有陈述这些实际模型、二阶系数或余项。
这一区分不主张在全部文献中证明原创性；所核对的直接先例不支配该二阶结论。

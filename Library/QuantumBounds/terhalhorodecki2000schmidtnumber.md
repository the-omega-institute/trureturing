---
bibkey: terhalhorodecki2000schmidtnumber
authors: Barbara M. Terhal, Pawel Horodecki
year: 2000
title: A Schmidt Number for Density Matrices
doi: 10.48550/arXiv.quant-ph/9911117
url: https://arxiv.org/abs/quant-ph/9911117v4
claim: "Lemma 1 bounds overlap with a maximally entangled state by k/d for states of Schmidt number at most k."
strata_touched: []
license: citation-only
triage: anchor
---

# Schmidt 秩约束与矩阵秩—迹界

Terhal–Horodecki，*A Schmidt Number for Density Matrices*，
arXiv:quant-ph/9911117v4，Lemma 1。

在 $\mathbb C^d\otimes\mathbb C^d$ 上，Schmidt 数至多 $k$ 的密度态与任意
最大纠缠态的重叠不超过 $k/d$。纯态情形由 Schmidt 系数的 Cauchy–Schwarz
不等式得到，混态情形由凸组合得到。

向量化 $C\mapsto|C\rangle\!\rangle$ 后，Schmidt 秩为 $\operatorname{rank}C$，
范数平方为 $\|C\|_{\mathrm{HS}}^2$，与未归一最大纠缠向量的内积为
$\operatorname{tr}C$，故相应矩阵不等式为

$$
|\operatorname{tr}C|^2\leq\operatorname{rank}(C)\|C\|_{\mathrm{HS}}^2.
$$

[AURIC Ω 第 11 节](../../docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)
把这个标准界应用于任意复 Kraus 算子，再用 TP 求和；该文献本身不提供指定
五模式两设置的方差估计或误差常数。

## Locator

- DOI：https://doi.org/10.48550/arXiv.quant-ph/9911117
- arXiv v4 记录：https://arxiv.org/abs/quant-ph/9911117v4

定位范围为上文所引 Lemma 1 的 Schmidt 数重叠界及其向量化矩阵表述；
指定五模式两设置的方差估计与误差常数不归于该文献。

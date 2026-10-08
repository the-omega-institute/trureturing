---
bibkey: keletikolountzakis2006determination
authors: "Tamás Keleti and Mihail N. Kolountzakis"
year: 2006
title: "On the determination of sets by their triple correlation in finite cyclic groups"
doi: null
url: https://arxiv.org/abs/math/0603415
claim: "在有限循环群上，处处非零的 Fourier 变换使三点相关完整决定信号的平移轨道；素数模上的非空真子集具有这一非消失性质，结合 CRT 可用于可容许的平方自由质数 wheel。"
strata_touched: []
license: citation-only
triage: anchor
---

# 有限循环群的三点相关与 wheel 相位

原文：[On the determination of sets by their triple correlation in finite cyclic groups](https://arxiv.org/abs/math/0603415)；[全文 PDF](https://arxiv.org/pdf/math/0603415)。本条采用其引言中的 Fourier 论证及素数模非消失事实，不把一般循环群的无条件恢复结论套用于任意信号。

对有限循环群 $G=\mathbb Z/W\mathbb Z$ 上的非负函数，定义
$$
C_f(s,t)=\sum_{r\in G}f(r)f(r+s)f(r+t),
\qquad
\widehat f(k)=\sum_{r\in G}f(r)e^{-2\pi i kr/W}.
$$
原文引言式 (2)–(3) 将三点相关的 Fourier 变换写成
$$
\widehat C_f(k,\ell)
=\widehat f(k)\widehat f(\ell)
  \overline{\widehat f(k+\ell)}.
$$
若 $\widehat f$ 处处非零，且 $C_f=C_g$，则 Fourier 系数之比是 $G$ 的 character，故 $g$ 是 $f$ 的平移。结论恢复的是平移轨道，不包含绝对原点。原文也说明，Fourier 零点是一般三点恢复问题的主要障碍；其 Theorem 2.22 给出偶数模 $W\ge12$ 上同三点相关而不互为平移的集合。

## 平方自由 wheel 的直接推论

令 $H$ 为非空偏移集，$W$ 为平方自由正整数，并假设 $H$ 在每个 $p\mid W$ 上可容许。定义局部存活集和全局 wheel
$$
R_p=\mathbb F_p\setminus\{-h:h\in H\},
\qquad
a_H(r)=\mathbf1_{\gcd(\prod_{h\in H}(r+h),W)=1}.
$$
每个 $R_p$ 都是非空真子集。原文 PDF 第 2 页使用素数次单位根的有理线性关系，说明这种示性函数的 Fourier 变换处处非零。等价地，$\Phi_p(X)=1+X+\cdots+X^{p-1}$ 的不可约性排除了真子集的非零频率和消失；零频率则等于 $|R_p|>0$。

CRT 将 $a_H$ 分解为这些局部示性函数的张量积，因此其全部 Fourier 系数也非零。于是完整三点相关决定可容许平方自由 wheel 的平移轨道。这是上述经典结论与 CRT 的特化，不是对一般复合模集合新增的三点完备性断言。

## 对有序原点的适用边界

二点自相关只保留 $|\widehat f|^2$，不能区分反射造成的相位变化。三点相关在全 Fourier 支撑下恢复线性相位以外的信息，但任何阶的平移不变相关仍不能区分同一平移轨道中的绝对位置。例如模 $30$ 的 $\{11,17\}$ 与 $\{7,13\}$ 互为平移，故提高相关阶数不能决定其相对于固定整数区间的放置。

保留已知原点标记的交叉相关或有序区间读数属于另一个恢复问题。相关 wheel 推论、显式分离及带标记 Fibonacci 窗口接口见[主卷第十六节](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)。这里的完备性不提供真实素数三胞胎渐近式，也不提供从有限模统计到整数区间素数相关的误差控制。

## 指定三胞胎轮筛的定量后续及初等先例

主卷第二十节将同一 CRT Fourier 分解用于 $H=\{0,2,6\}$ 和 $\{0,4,6\}$，计算全部移位卷积算子的最小奇异值与条件数。循环卷积的 Fourier 对角化、奇异值等于乘子模长，以及局部极值的三角函数计算均作为既有方法或初等中间步骤使用；这里不将它们列为新的基础理论。

其中 $|1+z+z^3|^2$ 在单位圆上的最小值
$(47-14\sqrt7)/27$，对应三次多项式
$1-4c+4c^2+8c^3$ 的最小值。相同的多项式和临界点已出现在 Everyday Prep 的 [Original Problem 382: Centroid of a doubling orbit and maximum triangle area](https://everydayprep.jp/international-baccalaureate-ib-en/ib-mathematics-aa-hl-english/ib-aa-hl-g01-en/ib-aa-hl-doubling-orbit-centroid-area-0382-en/) 的三点重心距离计算中。该初等先例只供应圆周极值，并不声称其讨论了素数筛轮。

本仓在这些中间事实上的具体推导是：局部最小模 $\alpha_q$ 在 CRT 上可同时实现，故全轮最小奇异值恰为 $\prod_{q\mid W,\ q\ge5}\alpha_q$；估计 $\alpha_q^2=\alpha^2+O(q^{-2})$ 使修正乘积收敛，再由初等素数无穷性得到素数乘积模长下 $\log\kappa_2/\log W\to1$。该条件数属于有标签的线性卷积算子；它不等于三点相关逆问题的条件数，也不等于固定 Fibonacci 长度的两组窗口和映射的条件数。

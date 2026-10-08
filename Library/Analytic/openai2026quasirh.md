---
bibkey: openai2026quasirh
authors: "OpenAI"
year: 2026
title: "The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s)>7/8"
doi: null
url: https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md
claim: "官方主稿陈述所有 Dirichlet L 函数及 Q(sqrt(-3)) 上有限阶 Hecke L 函数在 Re(s)>7/8 无零，允许主特征在 s=1 的极点；其 cubic theta 的 SL2(Z) 不变性使 Fibonacci 平方矩阵的固定轨道本身不产生 theta 值振荡。"
strata_touched: []
license: citation-only
triage: anchor
---

# 固定无零半平面与 Fibonacci 双曲作用的接口

主源为 OpenAI 的 [The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s)>7/8](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)。精确主定理见[主稿 TeX 的 Introduction](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex)；形式化边界见[官方 Lean 范围说明](https://github.com/openai/math/blob/main/lean/docs/003.md)。下面的 theta 变换来自[另一证明的官方 TeX](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex)，其目标半平面为 $\Re s>11/12$。

## 主张及适用范围

主稿 Theorem 1.1 陈述：每个 $F=\mathbb Q(\sqrt{-3})$ 上的有限阶 Hecke $L$ 函数，以及每个 Dirichlet $L$ 函数，包括 $\zeta$，在严格半平面
$$
\Re s>\frac78
$$
没有零点；主特征在 $s=1$ 的极点允许存在。界与模数、特征和高度无关，不包含边界 $\Re s=7/8$，也不把非平凡零点定位到 $\Re s=1/2$。

官方 Lean 说明给出的范围包括所有正模数及所有 Dirichlet 特征、上述有限阶 Hecke 特征，以及统一的实零点排除界：存在同一个 $c>0$，使导子 $q\ge3$ 的每个本原非主实特征所对应的每个实零点 $0<\beta<1$ 满足
$$
1-\beta\ge\frac{c}{\log q}.
$$
两种奇偶性都包括在内，但没有给出 $c$ 的显式数值，也没有排除 $(0,1)$ 中其他位置的实零点；论文后续应用不在该形式化范围内。本条记录源文定理及官方公布的形式化范围，不将它改述为完整 RH。

## Cubic theta 的算术内容

另一证明令 $\omega=e^{2\pi i/3}$、$\mathcal O=\mathbb Z[\omega]$，使用双曲三维空间
$$
\mathbb H^3=\{(z,v):z\in\mathbb C,\ v>0\}
$$
上的 cubic theta。其分析步骤将 Möbius 加权和嵌入变化的 sextic twist family，经 Gauss–Jacobi 转换、cube 指标补全及 theta 自守变换，得到可使用 quadratic large sieve 的扭曲族。空间维数本身不提供这些变换或消去估计。

该 TeX 的附录 “The cubic theta transformation with fixed ray class twists” 明确使用
$$
\theta(\gamma w)=\theta(w)
\quad(\gamma\in\mathrm{SL}_2(\mathbb Z)).
$$
在 $g_1=\left(\begin{smallmatrix}a_1&b_1\\c_1&d_1\end{smallmatrix}\right)
\in\mathrm{SL}_2(\mathcal O)$、$g_1\equiv I\pmod3$ 的更一般情形，变换带 cubic multiplier
$$
\theta(g_1w)=\kappa(g_1)\theta(w),
\qquad \kappa(g_1)=(c_1/a_1)_3.
$$
该附录还使用含 $\omega,\omega^2$ 的不同尖点展开；这些算术相位及变化的扭曲参数不能由一个整数矩阵循环子群替代。

## 与 Fibonacci 矩阵的比较推导

以下是本条对源文不变性的直接比较推导，不是源文另行证明的 Fibonacci 结果。取
$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},
\qquad
G=M^2=\begin{pmatrix}1&1\\1&2\end{pmatrix}
\in\mathrm{SL}_2(\mathbb Z)
\subset\mathrm{SL}_2(\mathbb Z[\omega]).
$$
设 $\varphi=(1+\sqrt5)/2$。$G$ 的特征值为 $\varphi^2,\varphi^{-2}$，在边界的 Möbius 作用为 $z\mapsto(z+1)/(z+2)$，固定点为 $\varphi^{-1}$ 和 $-\varphi$。按曲率 $-1$ 的标准双曲度量，它在 $\mathbb H^3$ 中的平移长度为
$$
\ell(G)=2\operatorname{arcosh}\!\left(\frac{\operatorname{tr}G}{2}\right)
=2\log(\varphi^2)=4\log\varphi.
$$
因此 Fibonacci 平方矩阵确有精确的双曲几何实现。然而对上述同一个 theta 函数和固定 $w$，源文的整数矩阵不变性立即给出
$$
\theta(G^n w)=\theta(w)\quad(n\in\mathbb Z),
\qquad
\sum_{n=0}^{N-1}\theta(G^n w)=N\theta(w).
$$
这个轨道上的 theta 值是常数，不能仅由双曲位移产生新的相位振荡或平方根消去。若要把 Fibonacci 状态用于源文的解析机制，仍须构造并控制带有真实变化扭曲、尖点或其他算术参数的观测量，以及相应的平均平方估计。这一嵌入不证明 RH，也不提供固定偏移素数三胞胎的相关渐近式。

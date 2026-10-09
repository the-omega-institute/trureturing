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

## Euler 修正的扩大解析域与完整素数操作

以下是对主稿 “The complete local identity” 与 “The full holomorphic correction” 中精确公式的比较推导，使用同一份素数掩码、目标特征及有限素数操作。其结论是修正因子的解析域和数量界；整篇源证明及源 Lean 项目未在这里独立复核。

令 $a=\Re x$、$b=\Re w$、$c=\Re z$。沿用源文的第 $u$ 行，$u$ 为避开固定集合 $S$ 的非零六次幂自由元。在素理想 $p\notin S$ 上写 $Q=q_p$，并保留源文零延拓：
$$
V=Q^{-6z},\qquad R=a_p^2Q^{4-6x-6z},\qquad
W=\chi_p(u)Q^{-w},\qquad
D=\eta(p)\overline{\chi_p(u)}Q^{-x},
$$
其中 $a_p=\overline{\alpha(p)}^3\eta(p)^3$、$\alpha(p)=p/|p|$。若 $p\mid u$，则 $D=W=0$；不能把这些零改成单位相位。

对 $p\nmid u$，令 $E_p=P_p^*+D$。源文的 $j=0$ 闭式直接给出
$$
E_p=
\frac{R\left\{\dfrac{1-Q^{-1}}{1-V}+W-D\right\}
-\dfrac{D(Q-1)WV}{1-V}}{1-R}.
$$
与源文的完整缺陷恒等式
$$
H_p-1=
\frac{D(V+W-VW)-VW+(1-V)(1-W)E_p}{1-D}
$$
合用，在下面开域的紧实部子域上得到高度及单位相位一致的界：
$$
\begin{gathered}
a,b,c>0,\qquad a+6c>1,\qquad a+b>1,\qquad b+6c>1,\\
6a+6c>5,\qquad a+b+6c>2,
\end{gathered}
$$
$$
|H_p-1|\ll
Q^{-a-6c}+Q^{-a-b}+Q^{-b-6c}
+Q^{4-6a-6c}+Q^{1-a-b-6c}.
$$
证明所用的分母只有 $1-D,1-V,1-R$，在此域内统一远离零。五个指数都严格小于 $-1$，故利用源文的理想计数，未分歧素数的乘积正常收敛。

对 $p\mid u$，必须保留源文 $j=1,\ldots,5$ 的全部边界项。除已控制的项外，可能的指数为
$$
1-a-b,\quad \frac32-3a,\quad 2-3a-b,
\quad 2-4a,\quad \frac52-4a-b,\quad 3-6a.
$$
若再有 $a>1/2$，它们由 $a+b>1$ 全部为负。因此分歧素数的有限乘积为 $O_\varepsilon(q_u^\varepsilon)$；这不要求它对所有 $u$ 一致接近 $1$。

特别地，取
$$
\Re x\ge\frac7{10},\qquad
\Re w\ge\frac{19}{20},\qquad
\Re z\ge\frac{33}{200},
$$
有
$$
H_p-1=
\begin{cases}
O(Q^{-119/100}),&p\nmid u,\\
O(Q^{-3/5}),&p\mid u,
\end{cases}
\qquad
\mathcal H_{\eta,u}\ll_\varepsilon q_u^\varepsilon.
$$
更一般地，保持后两个下限时，任意 $\Re x\ge\sigma>401/600$ 都满足上述严格收敛条件；这里只给充分条件，不断言该阈值最优。修正族在每一点的开邻域内全纯，且界覆盖全部虚部。它延拓的是每个固定 $u$ 的修正及相应局部标量表达式，尚未控制无限物理行之和。

有限素数操作同样可以在此域控制。对源文允许的单位射线素数，使用不含 $P_p$ 或 $H_p$ 分母的 $G_p$。若 $p\nmid u$，写 $v=\chi_p(u)$，源文的精确抵消式给出
$$
|G_p+v^{-1}H_p|\ll
Q^{-6c}+Q^{-a}+Q^{4-5a-6c}+Q^{1-b-6c}
\ll Q^{-49/100}
$$
于上面的 $7/10$ 矩形上。若 $p\mid u$，应使用实际零掩码公式
$$
G_p=\overline{\eta(p)}Q^x(1-V)E_p-Q^{-w}H_p.
$$
保留全部分歧边界项后得到 $G_p=O(Q^{1/10})$；可能的增长项 $Q^{1-b}$、$Q^{3/2-2a}$ 不能删去。

对固定且互不相交的原素数槽，$P_i=Z^{\ell_i}$、$\ell=\sum_i\ell_i$，完整修正仍为源文的有限元组和
$$
\mathfrak H_{\eta,u,Z}=
\sum_{(p_i)\in\prod_i\mathcal P_i(Z)}
\prod_i\left[W_i(q_{p_i}/P_i)q_{p_i}^{z-1}G_{p_i}\right]
\prod_{\substack{p\notin S\\p\notin\{p_i\}}}H_p.
$$
未选择素数的正常收敛乘积与有限元组计数给出，在固定实部盒内、所有高度上，
$$
|\mathfrak H_{\eta,1,Z}|\ll Z^{\ell\Re z},\qquad
|\mathfrak H_{\eta,u,Z}|\ll_\varepsilon
q_u^\varepsilon Z^{\ell(\Re z+1/10)}.
$$
这控制了整个修正；主行较小的界不能直接用于分歧的一般行。整个延拓不依赖对可能为零的 $P_p,H_p$ 作除法。

非零归一化须另外处理。在 $w=1,z=1/6,\Re x\ge7/10$ 上，素数和的裕度增为 $1/5$，故
$$
H_\eta(x)=\mathcal H_{\eta,1}(x,1,1/6)
=1+O(P_0^{-1/5}).
$$
足够大的固定 $P_0$ 可保证 $|H_\eta-1|\le1/2$，并保证此留数位置的各 $H_p$ 非零。这里没有认证显式有限截断值；为 $7/8$ 选取的旧截断不自动满足新条件。如扩大 $P_0$，必须同步更新 $S,b_*,\xi,\tau,\Xi$、物理探针及 $c_S$，按源文重新校准；固定 $T$ 和目标 $\eta$ 保留。

仅在上述非零性已成立的留数位置，才定义 $\mathcal B_p=G_p/H_p$。精确抵消式与 $\min(a,5a-3,1)\ge1/2$ 给出
$$
\mathcal B_p=-1+O(Q^{-1/2}).
$$
于是对同一校准探针的正权素数槽和 $S_i(Z)$，保留实际随规模变化的
$$
A_T(Z)=(-1)^KZ^{-\ell/6}\prod_i S_i(Z),
$$
得到
$$
\mathfrak H_{\eta,1,Z}(x,1,1/6)
=H_\eta(x)Z^{\ell/6}A_T(Z)
\bigl(1+\mathcal R_{\eta,Z}(x)\bigr),
\qquad
\mathcal R_{\eta,Z}\ll Z^{-\mu}
$$
于任意 $0<\mu<\tfrac12\min_i\ell_i$。无槽时余项为零。$A_T(Z)$ 是源文的非零对数变化函数，不能换成常数；扩大固定 $S$ 时，必须使用该探针对应的 $c_S$ 及最终阈值。

上述推导支付了扩大域上的局部修正、完整有限素数操作、高度界及带截断条件的留数归一化。源文主信号提取引理仍明文要求 $\sigma_0\ge7/8$；扩大其适用范围，还须实际控制无限行、周围轮廓及整体高端比较。原低端界 $Z^{3/16+\varepsilon}$ 没有改善，这些修正估计不推出新的无零半平面、严格 Robin 界或 RH。

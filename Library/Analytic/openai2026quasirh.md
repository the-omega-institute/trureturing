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

## 主留数中的角向因子、有限素数槽与联合零点重数

以下继续使用主稿的精确局部恒等式，只在 $u=1,w=1,z=1/6$ 的主留数切面上展开。目标 $\eta$、有限集合 $S$、primary 生成元约定、物理掩码与原素数槽同时保留。推导依赖所引局部公式；整篇源证明及源 Lean 未在这里独立认证。

令 $v=Q^{-1}$，并写
$$
D=\eta(p)Q^{-s},\qquad
R=\overline{\alpha(p)}^6\eta(p)^6Q^{3-6s}
\quad(p\notin S).
$$
此时源文闭式化为
$$
P_p^*=(1+v)\frac{R-D}{1-R},
$$
$$
H_p=\frac{1-v^2}{1-R}\,J_p,\qquad
J_p=1+\frac{v(D-R)}{1-D}
=\frac{N_p}{1-D},\qquad
N_p=1-(1-v)D-vR.
$$
这些是同一主行的因子，不是替换后的探针。

在避开 $\eta$ 模数的理想上定义实际角向特征
$$
\nu_\eta((a))=
\left(\frac{\overline a}{|a|}\right)^6\eta((a))^6.
$$
六个单位的六次幂均为 $1$，故公式不依赖生成元，并且与理想乘法相容。它具有角指数 $-6$，不属于有限阶族。具体地，取正整数 $M$ 为 $3$ 的倍数、属于 $\eta$ 的完整模数理想，并被 $S$ 下方的有理素数整除。$a_k=1+Mk\omega$ 是 primary，模这些理想均为 $1$，所以 $\eta((a_k))=1$ 且 $(a_k)$ 避开 $S$。$a_k$ 的方向有无限多个不同值，而圆上的六次幂映射为有限对一，故 $\nu_\eta$ 有无限多个值。这些理想与 $S$ 互素，并不是所谓 $S$-单位。

于 $\Re s>2/3$，角向 Euler 乘积绝对收敛，得到
$$
H_\eta(s)=
\zeta_F^S(2)^{-1}
L_F^S(6s-3,\nu_\eta)J_\eta(s),
\qquad
J_\eta(s)=\prod_{p\notin S}J_p(s).
$$
这里 $L_F^S(t,\nu_\eta)$ 在 $\Re t>1$ 先由实际理想 Euler 乘积定义；没有把有限阶无零定理用于无限阶特征。

### 残余乘积在 $1/2$ 右侧非零

对任意固定 $\sigma_0>1/2$，在 $\Re s\ge\sigma_0$ 上，所有高度及目标单位相位一致地有
$$
|J_p-1|\ll_{\sigma_0}
Q^{-1-\sigma_0}+Q^{2-6\sigma_0}.
$$
两个指数均严格小于 $-1$，故利用同一理想计数，$J_\eta$ 在 $\Re s>1/2$ 正常收敛。

非零性还有逐素数的相位无关证书：
$$
|(1-Q^{-1})D+Q^{-1}R|
\le(1-Q^{-1})Q^{-1/2}+Q^{-1}<1.
$$
最后的严格裕度，令 $t=Q^{-1/2}\in(0,1)$ 后就是
$$
1-(t+t^2-t^3)=(1-t)^2(1+t)>0.
$$
因此 $N_p\ne0$；此半平面内也有 $|D|,|R|<1$，从而每个 $J_p,H_p$ 均全纯且非零。正常收敛的 $J_\eta$ 也非零。有限素数的统一下界加上可求和的小尾部，保证 $J_\eta$ 及其倒数在每个 $\Re s\ge\sigma_0>1/2$ 上有统一高度界；不能把上述粗分子下界直接跨全部素数相乘。

在 $\Re s>2/3$，角向 $L$ 的绝对 Euler 乘积同样非零，所以原有限 $S$ 已足以保证实际 $H_\eta\ne0$。为取得这种非零性，无须仅因此扩大截断。它与源文公共信号判据要求的
$$
\sup_{\Re s>\sigma_0}|H_\eta(s)-1|\le\frac12
$$
不同：非零性不提供这条接近 $1$ 的合同，也不自动支付低端节省或高端比较。前节带截断条件的接近 $1$ 估计仍是另一项充分条件。

### 实际有限操作保留角向因子

既然局部 $H_p$ 在 $\Re s>1/2$ 非零，主留数上的原素数替换 $\mathcal B_p=G_p/H_p$ 在整个半平面合法。源公式给出
$$
\mathcal B_p=
\frac{(1-v)(R/D-1)}{N_p}-v,
$$
$$
\mathcal B_p+1=
\frac{(1-v)\{R/D-(1-v)D-vR\}}{N_p}.
$$
这里 $p\notin S,u=1$，所以 $D\ne0$；没有对零延拓的分歧行作此除法。由统一分母下界可得
$$
|\mathcal B_p+1|\ll_{\sigma_0}
Q^{3-5\Re s}+Q^{-\Re s}
\quad(\Re s\ge\sigma_0>1/2).
$$
若 $\sigma_0>3/5$，令
$$
\kappa=\min(\sigma_0,5\sigma_0-3)>0,
$$
便有 $\mathcal B_p=-1+O(Q^{-\kappa})$，覆盖所有高度。沿用源文互不相交的正权素数槽及其 $S_i(Z),A_T(Z)$，定义实际槽乘积
$$
\mathcal P_{\eta,Z}(s)=
\prod_i\left(
\sum_{p\in\mathcal P_i(Z)}
W_i(q_p/P_i)q_p^{-5/6}\mathcal B_p(s)
\right).
$$
源文的槽计数与非零移动归一化直接给出，充分大的 $Z$ 上，
$$
\mathcal P_{\eta,Z}(s)=
Z^{\ell/6}A_T(Z)(1+\mathcal R_{\eta,Z}(s)),
\qquad
\mathcal R_{\eta,Z}\ll Z^{-\mu},
$$
于任意 $0<\mu<\kappa\min_i\ell_i$，一致覆盖 $\Re s\ge\sigma_0$ 及全部高度。因此该范围内槽乘积非零。无槽时乘积为 $1$、余项为 $0$。

$3/5$ 是这一特定逐素数近似的实际边界。固定 $1/2<\sigma\le3/5$，令 $Q\to\infty$，上面的精确式给出
$$
\frac{|\mathcal B_p(s)+1|}{Q^{3-5\sigma}}\longrightarrow1
\quad(\Re s=\sigma),
$$
一致覆盖虚部及单位相位。因为 $N_p=1+O(Q^{-\sigma}+Q^{2-6\sigma})$，而 $|R/D|=Q^{3-5\sigma}$，其他分子项相对它趋于零。在边界上局部缺陷的模趋于 $1$，更低时增长。这否定该范围内的统一逐素数 $-1+o(1)$ 近似；不否定素数之间的联合消去、其他槽归一化或 RH。

于已建立的乘积域 $\Re s>2/3$，完整有限操作严格保留同一角向因子：
$$
\mathfrak H_{\eta,1,Z}(s,1,1/6)
=H_\eta(s)\mathcal P_{\eta,Z}(s)
=\zeta_F^S(2)^{-1}
L_F^S(6s-3,\nu_\eta)J_\eta(s)\mathcal P_{\eta,Z}(s).
$$
所以有限替换没有将这个全局因子从实际主信号中除去。

### 更低条带需要引用延拓，并检查联合重数

所查主稿的 Hecke 增长引理明确限于有限阶、平凡无限类型，不能承担 $\nu_\eta$ 的解析延拓。无限类型的延拓应引用适用的既有 Hecke 理论；这里尚未核对一个支付该精确接口的原始定理，不重证一般理论。

**以下结论有条件**：若另行认证 $L_F(t,\nu_\eta)$ 在 $\Re t>0$ 的全纯延拓，则上面的因子式唯一延拓 $H_\eta$ 及其有限操作至 $\Re s>1/2$。有限删除因子只可能在 $\Re(6s-3)=0$ 有零点，故不改变开半平面内的零点，而 $J_\eta$ 已知非零。

在此条件下，对一个实际目标零点 $\rho$，$\Re\rho>1/2$，记
$$
m=\operatorname{ord}_{\rho}L_F(s,\eta),\qquad
k=\operatorname{ord}_{6\rho-3}L_F(t,\nu_\eta).
$$
未选择素数槽时，$H_\eta/L_F^S(s,\eta)$ 恰在 $m>k$ 时留下极点，阶数为 $m-k$。若保留实际有限槽，还须加入
$$
j_Z=\operatorname{ord}_\rho\mathcal P_{\eta,Z}.
$$
槽乘积在该邻域不恒为零时，完整修正除以目标 $L$ 恰在
$$
m>k+j_Z
$$
时留下极点，阶数为 $m-k-j_Z$；若槽乘积恒为零，该比值为零，不是极点探测器。源文非零的 $c_S,A_T(Z)$ 不改变这些重数。$\Re\rho>3/5$ 时，充分大的 $Z$ 使 $j_Z=0$；更低处不能仅由槽的全纯性删去 $j_Z$。

这给出需要控制的实际联合条件，不断言共同零点存在或不存在。残余因子非零、角向因子全纯、有限槽非零和低高端严格节省是不同义务。这里没有支付无限类型延拓输入、辅助 RH、统一至 $1/2$ 的主信号非零性、无限行比较或更强低端消去；没有得到新的无零定理或严格 Robin/RH 证明。

## 平方自由立方索引：一个保留目标分母的新探针

这一接口定义一个实际修改后的探针，依赖源文原始系数与完整局部表；不把上一节的角向因子从原探针中形式除去，也不转移原探针的低端估计。

在源文的 $A=cn^3$ 完成行中插入理想指标 $\mu(n)^2$，即同时要求 $c,n$ 平方自由，但允许它们共享素因子。保留其余字符、零掩码、相位、尺度、Gaussian 与外层权重。记新行及新物理探针为 $T^{\mathrm{sf}},I^{\mathrm{sf}}$。过滤独立于 Poisson 所作用的 $m$ 变量，且模不超过 $1$；因此原绝对起始线上逐系数的有限 Fourier/Poisson 恒等式及其绝对主控仍适用。新高端系数是原 $K_\eta(c,n,s,a;u)$ 乘以 $\mu(n)^2$，不是改变目标零点的取样。

### 原始局部族的合法限制

令 $l=v_p(n)$。原完整局部表的四族为
$$
(e_0,l)=(0,2r+2),(1,2r),(0,2r+1),(1,2r+1),\qquad r\ge0.
$$
新指标要求 $l\in\{0,1\}$，故删除第一族，并在后三族只保留 $r=0$。尤其原 $j=5$ 的 $-a_p^2Q^{3-6x}$ 属于 $l=2$，必须一起删除；来自 $c$ 及 $m$ 尾部的 $j=5$ 项仍在。

沿用 $j=v_p(u)\in\{0,\ldots,5\}$、$\rho=\chi_p(u/p^j)$、$V=Q^{-6z}$ 与 $W_{\rm loc}=\rho Q^{-w}$。由源表直接得到
$$
P_p^{\mathrm{sf},*}=
-\frac{\eta(p)(Q-1)Q^{-x-w}V^{\mathbf1_{j\le1}}}{1-V}
+J_j^{\mathrm{sf}},
$$
$$
\begin{array}{c|l}
j&J_j^{\mathrm{sf}}\\\hline
0&-\eta(p)\rho^{-1}Q^{-x}\\
1&\eta(p)Q^{-x-w}\\
2&a_p\rho^{-3}Q^{3/2-3x}\\
3&-\eta(p)b_p\rho^{-2}Q^{2-3x-w}+b_p^2\rho^{-4}Q^{2-4x}\\
4&-\eta(p)a_p\rho^{-3}Q^{5/2-4x-w}\\
5&0.
\end{array}
$$
并有
$$
P_p^{\mathrm{sf}}=\frac1{1-V}
+\mathbf1_{j=0}\frac{W_{\rm loc}}{1-W_{\rm loc}}
+P_p^{\mathrm{sf},*}.
$$
这里保留了全部合法 $e_0,k,m,j$ 与共享素因子；结论来自实际过滤，不是裸写 $R=0$。

保留原来的 $D=\eta(p)\overline{\chi_p(u)}Q^{-x}$、$W=\chi_p(u)Q^{-w}$，其中 $p\mid u$ 时仍有 $D=W=0$。定义
$$
H_p^{\mathrm{sf}}=
P_p^{\mathrm{sf}}\frac{(1-V)(1-W)}{1-D}.
$$
乘法指标 $\mu(n)^2$ 与原逐素数系数相容，故实际新高端级数在绝对起始域满足
$$
\mathcal F_{\eta,u}^{\mathrm{sf}}(x,w,z)=
\frac{\zeta_F^S(6z)L_F^S(w,\chi_\bullet(u))}
{L_F^S(x,\eta\overline{\chi_\bullet(u)})}
\mathcal H_{\eta,u}^{\mathrm{sf}}(x,w,z).
$$
目标分母与两个原分子极点保持；变化发生在新探针的修正乘积。

### 完整固定行的收敛域

对 $p\nmid u$，设 $E_p^{\mathrm{sf}}=P_p^{\mathrm{sf},*}+D$，则
$$
E_p^{\mathrm{sf}}=-\frac{D(Q-1)WV}{1-V},
$$
$$
H_p^{\mathrm{sf}}-1=
\frac{D(V+W-VW)-VW-D(Q-1)WV(1-W)}{1-D}.
$$
因此在 $a,b,c>0$、
$$
a+6c>1,\quad a+b>1,\quad b+6c>1,\quad a+b+6c>2
$$
的紧实部子域上，所有高度一致地有
$$
|H_p^{\mathrm{sf}}-1|\ll
Q^{-a-6c}+Q^{-a-b}+Q^{-b-6c}+Q^{1-a-b-6c}.
$$
四项均可求和，不再需要原 $R$ 所带来的 $6a+6c>5$ 条件。

对 $p\mid u$，完整式是
$$
H_p^{\mathrm{sf}}=
1-\eta(p)(Q-1)Q^{-x-w}V^{\mathbf1_{j\le1}}
+(1-V)J_j^{\mathrm{sf}}.
$$
若 $a>1/2,a+b>1$，其额外指数 $1-a-b,3/2-3a,2-3a-b,2-4a,5/2-4a-b$ 均为负，有限分歧乘积为 $O_\varepsilon(q_u^\varepsilon)$。

特别地，对任意固定 $\sigma_0>1/2$，在
$$
\Re x\ge\sigma_0,\quad\Re w\ge19/20,\quad\Re z\ge33/200
$$
上，未分歧缺陷为 $O(Q^{-36/25})$，整个固定行修正在每点的开邻域内全纯，且为 $O_\varepsilon(q_u^\varepsilon)$。这些是固定行与全部高度的界，尚不是无限物理行之和的估计。

### 不含角向 $L$ 的实际主修正

在 $u=1,w=1,z=1/6$，写 $v=Q^{-1}$、$D=\eta(p)Q^{-s}$。此时
$$
P_p^{\mathrm{sf},*}=-(1+v)D,
\qquad
H_p^{\mathrm{sf}}=(1-v^2)
\frac{1-(1-v)D}{1-D}.
$$
对 $\Re s>0$，两个分母及分子均非零。缺陷为 $O(Q^{-2}+Q^{-1-\Re s})$，所以
$$
H_\eta^{\mathrm{sf}}(s)=
\zeta_F^S(2)^{-1}
\prod_{p\notin S}\left(1+\frac{vD}{1-D}\right)
$$
在整个 $\Re s>0$ 全纯且非零；它及其倒数在每个固定 $\Re s\ge\sigma_0>0$ 上都有统一高度界。角向 $L$ 没有被除去：产生它的局部族已在实际输入中被过滤。

还有 $H_\eta^{\mathrm{sf}}=1+O_{\sigma_0}(P_0^{-\min(1,\sigma_0)})$。足够大的固定截断可满足源文接近 $1$ 的合同；扩大时须同步校准 $S,b_*,\xi,\tau,\Xi,c_S$。这里未认证一个显式足够的有限截断，也不自动继承旧截断。

### 有限素数操作与原目标零点

对新物理行同时插入 $\mu(n)^2$ 与原标记 $p\mid cn^3$，再执行原两项操作及其尺度变化。两个指标都是实际索引约束；高端精确替换仍为
$$
\overline{\eta(p)}Q^{x+z-1}P_p^{\mathrm{sf},*}
-Q^{z-w-1}P_p^{\mathrm{sf}}.
$$
完整替换使用不含 $P_p^{\mathrm{sf}}$ 或 $H_p^{\mathrm{sf}}$ 分母的公式
$$
G_p^{\mathrm{sf}}=
\frac{(\overline{\eta(p)}Q^x-Q^{-w})(1-V)(1-W)P_p^{\mathrm{sf},*}
-Q^{-w}(1-VW)}{1-D},
$$
$$
\mathfrak H_{\eta,u,Z}^{\mathrm{sf}}=
\sum_{(p_i)\in\prod_i\mathcal P_i(Z)}
\prod_i\left[W_i(q_{p_i}/P_i)q_{p_i}^{z-1}G_{p_i}^{\mathrm{sf}}\right]
\prod_{\substack{p\notin S\\p\notin\{p_i\}}}H_p^{\mathrm{sf}}.
$$
一般分歧 $H_p^{\mathrm{sf}}$ 未证明非零，故不能以其商定义完整修正。只有已证明非零的主留数位置才使用槽比值。这是新标记／缩放物理探针的恒等式，不声明新旧低端范数相同。

在主留数上实际槽比值为
$$
\mathcal B_p^{\mathrm{sf}}=
-\frac{1-v}{1-(1-v)D}-v,
\qquad
\mathcal B_p^{\mathrm{sf}}+1=
-\frac{(1-v)^2D}{1-(1-v)D}.
$$
故任意固定 $\sigma_0>0$ 上均有 $-1+O_{\sigma_0}(Q^{-\sigma_0})$。原探针的 $3/5$ 局部边界仍然成立；这个新探针有不同的误差。

复用原互不相交的正权素数槽及其实际 $A_T(Z)$，充分大的 $Z$ 上有
$$
\mathfrak H_{\eta,1,Z}^{\mathrm{sf}}(s,1,1/6)
=H_\eta^{\mathrm{sf}}(s)Z^{\ell/6}A_T(Z)
(1+\mathcal R_{\eta,Z}^{\mathrm{sf}}(s)),
$$
$$
\mathcal R_{\eta,Z}^{\mathrm{sf}}\ll Z^{-\mu},
\qquad0<\mu<\sigma_0\min_i\ell_i
\quad(\Re s\ge\sigma_0>0).
$$
槽乘积在该固定条带上非零；无槽时余项为零。取固定 $\sigma_0=1/2$，便有依赖固定数据的同一充分大 $Z$ 阈值，覆盖所有高度及所有 $\Re\rho>1/2$ 的实际目标零点；它们以原重数成为新归一化主商的极点，不需要上一节的无限类型延拓前提。这里未给整个 $\Re s>0$ 开半平面的共同阈值。

完整有限修正也有高度界。在上述 $\sigma_0>1/2$ 矩形上，未分歧选择项为 $O(1)$；分歧选择项的增长至多 $Q^g$，其中
$$
g=\max(1/20,3/2-2\sigma_0).
$$
这来自全部剩余指数 $1-b,3/2-2a,2-2a-b,2-3a,5/2-3a-b$。故原元组计数给出
$$
|\mathfrak H_{\eta,1,Z}^{\mathrm{sf}}|\ll Z^{\ell\Re z},
\qquad
|\mathfrak H_{\eta,u,Z}^{\mathrm{sf}}|
\ll_\varepsilon q_u^\varepsilon Z^{\ell(\Re z+g)}.
$$
主行较小的界不能用于一般分歧行。

### 原 theta 低端界尚未迁移

源文完成反射与行矩界针对完整立方索引及其规范测试。插入 $\mu(n)^2$ 改变该行，不能仅由指标的模不超过 $1$ 推断复相位行的范数减少，也不能把这个乘法指标当成一个固定平滑范数轮廓。

经典恒等式 $\mu(n)^2=\sum_{d^2\mid n}\mu(d)$ 可以复用，但它引入随 $d$ 变化的完成尺度与算术零掩码。需要实际统一行界，才能连接到源文 theta/低端机制。这里既未迁移原 $Z^{3/16+\varepsilon}$ 界，也未改进低端指数。

这项构造支付了一个新同目标探针的局部高端恒等式、完整固定行和有限修正、以及非零主信号。它尚未支付同一新探针的无限行高端比较及目标无关的低端严格节省，也没有控制原 Robin 的完整有符号主响应。完整源证明及 Lean 未独立认证；严格 Robin 与 RH 均未证明。

## 平方自由立方索引的完整低端估计

下面估计上一节实际过滤后的无槽探针，复用主稿的完成反射、固定行扇区、Gaussian 行矩界与平面加性筛。源文输入及其零延拓作为前提；不重证 theta 或 large sieve，也不把原带槽补偿探针的 $Z^{3/16+\varepsilon}$ 界搬到新探针。

### 原零掩码与第六次尺度变化

记源文中央完成行为 $\mathcal C_V(X;m,\nu)$，其中权重仍为 $q_c^{-1/2}q_n^{-1}$，没有额外的 $X^{-1/2}$。在理想立方索引 $n$ 上插入 $\mu(n)^2$，得到 $\mathcal C_V^{\mathrm{sf}}$。复用经典平方自由反演并置 $n=d^2r$，有精确式
$$
\mathcal C_V^{\mathrm{sf}}(X;m,\nu)
=\sum_{(d,S)=1}\frac{\mu(d)\overline{\alpha(d)}^{\,6}\nu(d)^6}{q_d^2}
\mathbf1_{(d,m)=1}\,
\mathcal C_V(X/q_d^6;m,\nu).
$$
所有理想使用原 primary 生成元；$c$ 仍独立平方自由，$c,r,d$ 可以共享素因子。等式保留
$$
\chi_{d^6}(m)=\chi_d(m)^6=\mathbf1_{(d,m)=1}.
$$
所以 $d$ 引入的是行筛选及尺度变化；内行使用同一个固定字符 $\nu$，没有把增长的 $d$ 模数纳入固定 $S$。上述变化的算术零掩码在这里落实为可支付的外部行筛选，原带槽合同仍需另外处理。绝对收敛与理想约数界允许交换全部求和。

对于实际修正行，先使用源文的有限展开
$$
\overline{G(A)}=\sum_{\theta\in\widehat T}a_\theta\theta(A),
$$
再逐项取 $\nu=\nu_\sigma\theta$。因子 $\nu(d)^6$ 留在相应项内，不另假定 $G(d^6A)$ 的简化公式。

### 共同常数下的三个范围

固定原 Gaussian $V_{\rm G}$、有限字符族以及行球 $0<q_m\le C Z^M$。写
$$
R(X)=\left(\sum_{0<q_m\le C Z^M}
|\mathcal C_{V_{\rm G}}(X;m,\nu)|^2\right)^{1/2}.
$$
行筛选 $(d,m)=1$ 只缩小这里的正外层和。

源文完整行矩界在实际 powerful 部分的 $O$ 分块上，指数是
$$
O/2+\max(M-O,2M-O-N')
=\max(M,2M-N')-O/2.
$$
求和这些块便给出
$$
R(Z^{N'})\ll Z^{\max(M,2M-N')/2+\varepsilon}.
$$
此界在指定的有界 $M,N'$ 范围及固定有限字符族上使用共同常数；包括所有非零元素行及原零掩码，不重复计算 powerful 部分。

绝对 primal 计数另给出对每个 $X>0$ 都成立的界
$$
|\mathcal C_{V_{\rm G}}(X;m,\nu)|\ll X^{1/2},
\qquad R(X)\ll Z^{M/2}X^{1/2}.
$$
这里理想计数与 Gaussian 衰减给出
$$
\sum_{c\ {\rm sf}}q_c^{-1/2}|V_{\rm G}(q_c/Y)|\ll Y^{1/2}
\quad(Y>0).
$$
保留 $n$ 后，余量为 $X^{1/2}\sum_nq_n^{-5/2}$，可求和；$|\gamma_2(c)|=1$ 由原完整 Gauss 系数恒等式提供。

还必须使用完成尺度远大于行模数平方时的反射核衰减。固定行扇区有共同反射模数；活动素数积整除行的 good radical，故反射分母满足 $q_c\ll_{\rm fixed}q_m$。完整局部因子均有 $|B_p|\le q_p^{1/2}$，包括 $j=4$ 的 Ramanujan 两项；分支数由理想约数界控制。原尖点系数支持及大小使
$$
\sum_{\mu\ne0}|d(\mu)|q_\mu^{-1/2-K}<\infty
\quad(K>1/2).
$$
复用反射核任意阶的大参数衰减，得到
$$
|\mathcal C_{V_{\rm G}}(X;m,\nu)|
\ll_{K,\varepsilon}q_m^{2K+1/2+\varepsilon}X^{-K}.
$$
因此，对固定 $\delta,B>0$，先选有限核阶数，再令 $Z$ 充分大，有
$$
R(X)\ll Z^{-B}\quad\text{当 }X\ge Z^{2M+\delta}.
$$
共同常数来自明确反射因子，不能只引用允许依赖当前算术行的解析延拓常数。行与 $S$ 相交或有六整除的重数时，原扇区及局部零掩码仍保留。

### 支付全部平方因子，不截掉 Gaussian 尾部

固定 $N>0$、$0\le M\le2N$。在 $q_d\asymp Z^t$、$0\le t\le N/6$ 的块上，反演系数绝对质量为 $O(Z^{-t})$。Minkowski 与前两个界给出块范数指数
$$
F(t)=\min\left\{
\max\left(\frac M2-t,M-\frac N2+2t\right),
\frac{M+N}{2}-4t\right\}.
$$
内尺度的实际长度 $N'=N-6\log_Zq_d$ 在 $[0,N]$；块端点的固定常数不改变共同界。

令
$$
f=\frac{5M-N}{6},\qquad t_* =\frac{2N-M}{12}.
$$
递增项 $M-N/2+2t$ 与递减项 $(M+N)/2-4t$ 在 $t_*$ 相交，值均为 $f$，故它们较小者处处不超过 $f$。

另一个分支 $M/2-t$ 只能在 $t<(N-2M)/6$ 超过 $f$。取固定小 $\delta>0$；对
$$
q_d^6\le Z^{N-2M-\delta}
$$
使用上面的完整反射核衰减。再乘可求和的 $q_d^{-2}$，这整部分具有任意指定幂次的节省。其余块满足 $M/2-t\le f+\delta/6$。

对所有 $q_d>Z^{N/6}$，直接使用对每个 $X>0$ 的绝对 primal 界；不把行矩界用于无界负长度。若范数块中心为 $D$，该块贡献为 $O(Z^{(M+N)/2}D^{-4})$；单个 $d$ 项的权重是 $q_d^{-5}$。它们的整条尾部为
$$
\ll Z^{(M+N)/2}\sum_{q_d>Z^{N/6}}q_d^{-5}
\ll Z^{M/2-N/6}\le Z^f.
$$
保留块仅有对数个。选择前置损失及 $\delta$ 后，完整无限 $d$ 和因此满足
$$
\boxed{
\sum_{0<q_m\le C Z^M}
|\mathcal C_{V_{\rm G}}^{\mathrm{sf}}(Z^N;m,\nu)|^2
\ll Z^{(5M-N)/3+\varepsilon},
\qquad N>0,\quad0\le M\le2N.
}
$$
所有 $d$、共享素因子及 Gaussian 尾部都已计入。固定有限 Fourier 展开把同一界传到实际 $B_{m,\sigma}^{\mathrm{sf}}$。常数与阈值依赖固定参数范围、算术数据及指定损失，不声明显式起点。

### 新无槽探针的实际低端与主信号成本

选择无移动素数槽的过滤探针，取
$$
X=Y=Z^a,\qquad0<a<1,
$$
其中 $a$ 固定于目标与 $Z$ 之前。原物理低分离式逐系数仍成立；此时
$$
Q=q_{b_*}Z^{2a},\qquad M=2a,\qquad N=1.
$$
加性因子的平方范数由原筛界控制为 $O((Q+Y^2)/Y)=O(Z^a)$，对其 norm-twist 高度一致。新完成行范数是 $O(Z^{(10a-1)/6+\varepsilon})$。在同一实际行上 Cauchy，保留原 $Q^{-1/2}$ 与可积的 annular Mellin 权，得到
$$
\boxed{
|I_\eta^{\mathrm{sf}}(Z^a,Z^a,Z)|
\ll Z^{(7a-1)/6+\varepsilon}.
}
$$
例如固定 $a=1/10$ 时是 $Z^{-1/20+\varepsilon}$。负指数使用了完整反射核节省，不来自单独的绝对计数。

已有高端系数恒等式中的原尺度权，在 $w=1,z=1/6$ 的主留数上仍给出
$$
C_a(s)=s-\frac56+\frac a3.
$$
这只识别主留数的指数；尚未许可新几何下无限行轮廓的移动与比较。对固定的下述 $\beta$，选择 $\varepsilon$ 小于右侧差额后，上述界相对于 $Z^{C_a(\beta)}$ 提供严格幂次节省：
$$
\boxed{\beta>\frac23+\frac{5a}{6},\qquad
0<\varepsilon<\beta-\frac23-\frac{5a}{6}.}
$$
$a=1/10$ 的预算门槛是 $3/4$；这不是已证明的无零半平面。低于门槛时当前上界不足，不能据此判定实际消去失败。固定 $a$ 趋近零时，所得上界预算门槛趋近 $2/3$，也不允许让 $a$ 随 $Z$ 改变而沿用常数。

在 RH 边界 $\beta=1/2$，这份低端上界与主信号指数尚差
$$
\frac{1+5a}{6}>0.
$$
这是当前上界不足，不是真实探针范数的下界，也不排除另一种联合消去能改善它。原带槽补偿行的低端、改变几何后所有物理行与高度的高端比较、以及原完整有符号 Robin 响应仍未支付。完整源证明及 Lean 未独立认证；严格 Robin 与 RH 未证明。

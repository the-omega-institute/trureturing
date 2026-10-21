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

## 固定源码入口、版本与 Robin 接口

固定源码版本为 [`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb)。真正的公开定理入口是 [OAI/NumberTheory/DirichletL/Nonvanishing.lean](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)：

- `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` 对每个正模数、每个 Dirichlet 特征及满足 $7/8<\Re s$ 的复数，排除零点；另有准确的极点例外条件 $\neg(\chi=1\land s=1)$。
- `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` 对 Mathlib 的 `riemannZeta` 声明 $7/8<\Re s\Rightarrow\zeta(s)\ne0$。解析表述仍须保留 $s=1$ 的极点约定。

两条入口直接调用 [Detector/FinalAssemblyUnconditional.lean](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyUnconditional.lean)。该组装文件将固定参数与已认证 detector bands 接到 Dirichlet 和 zeta 无零结论。相同版本的 [ComparatorChallenges/QuasiRiemannHypothesis.lean](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/ComparatorChallenges/QuasiRiemannHypothesis.lean) 含 `sorry`，属于待完成的挑战陈述，不能用作证明供应者。

该版本的 [Lean toolchain](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/lean-toolchain) 为 `4.34.1`，[Mathlib 修订](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/lake-manifest.json) 为 `d13f23b723b8a846827a245b89c10fc7d3f11612`。本仓这条 Robin 形式化线使用 Lean `4.33.0`、Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。两者的编译缓存不兼容；源码入口和参数关系已核对，本条没有外部依赖闭包的本地 Lean/kernel 验收证据。正式接入须在相容版本分区编译实际依赖闭包，或对迁移后的实际源码重新核验，不能把未编译的引用当作本仓已接受定理。

与 Robin 路线有关的 [Moments/MobiusHarmonicMass.lean](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Moments/MobiusHarmonicMass.lean) 处理 Eisenstein 整环理想上的 Möbius 绝对值加权质量。`full_mass_subpower` 的准确量词是：每个 $B\ge0$、$\delta>0$ 对应某个 $C>0$，使充分大的 $Z>1$ 及每个有限理想集合 $\mathcal D$，在所有 $\mu(D)\ne0$ 的成员满足 $N(D)\le Z^B$ 时，有 $\sum_{D\in\mathcal D}|\mu(D)|/N(D)\le CZ^\delta$。其指标集、截断条件、权重与绝对值都须保留；该界本身没有给出普通整数 Robin 余量所需的有符号消去估计。

因此可复用的来源分为明确的两类接口：无零入口提供严格半平面 $\Re s>7/8$ 的解析排除；detector 与加权理想质量提供各自原指标集上的估计。要进入 Robin 全域目标，还须构造这些量到同一个普通整数余量的准确关系，并证明相应有符号估计。上述半平面没有把剩余的非平凡零点定位到临界线，也没有完成 Robin 无限尾项。

## 带槽平方自由立方索引的直接联合低端

本节直接复用主稿的 Canonical marked estimate、式 (A) 的 two-transform reduction 及其已闭合的子合同，完成实际平方自由立方索引标记族的低端转移。底层 canonical、Poisson、theta 与筛估计是源文结果；下面补的是系数准入、小立方索引与完整物理族之间的接口。源文输入及其零延拓作为前提，整篇源证明及 Lean 未独立认证。

### 允许的立方系数与实际归一化

保留固定有限 ray 字符 $\nu$、原集合 $S$ 和 primary 生成元。令
$$
\mathfrak d(A)=\sum_{(p_i)\in\prod_i\mathcal P_i}
\prod_i a_i(p_i)\mathbf1_{p_i\mid A},
$$
其中素数列表互不相交，系数有界、逐槽乘积型且与当前行及列无关；其名义总长度上限为 $z_0$。定义实际 annular 完成行
$$
\begin{aligned}
\mathcal R_m^{\mathrm{sf}}={}&
\sum_{\substack{c\ {\rm sf}\\b}}
\frac{\overline{\alpha(c)}\gamma_2(c)\nu(c)
\mu(b)^2\overline{\alpha(b)}^{\,3}\nu(b)^3}
{\sqrt{q_c}\,q_b}\\
&\quad\times\chi_c(m)\chi_b(m)^3
\mathfrak d(cb^3)W(q_cq_b^3/Z^{N_c}).
\end{aligned}
$$
$c,b$ 都避开 $S$，允许共享素因子；所有字符保留原零延拓。$N_c$ 是完成尺度指数，不是 Robin 最大化整数。

在 $q_c\asymp Z^r$、$q_b\asymp Z^u$ 的物理分块上，外部归一化为 $Z^{-r/2-u}$，平方后恰为源文式 (A) 的 $Z^{-r-2u}$。取该式的
$$
f=1,\qquad V=Q=0,\qquad k=m,\qquad F=r+3u.
$$
把两个归一化实因子
$$
(q_c/Z^r)^{-1/2}(q_b/Z^u)^{-1}
$$
放进同一个完整光滑 profile，再作 logarithmic Fourier 分离。因此分离后的立方系数只含
$$
\beta(b)=\mu(b)^2\overline{\alpha(b)}^{\,3}\nu(b)^3
(q_b/Z^u)^{it_b}
$$
及有界立方 annular cutoff；实倒根不再次进入这个系数或分离后的 $c$ 测试。$\beta$ 与 $m,c$ 无关。$c$ 的算术系数仍然恰为
$$
\overline{\alpha(c)}\gamma_2(c)\nu(c).
$$
源文式 (A) 允许这样的任意有界立方系数，并在正 majorant 前保留两份 $\beta$ 和全部掩码，不要求 $\beta(b,f)$ 可分解。这不扩大 canonical-moment 引理的列系数范围：该引理仍不允许额外任意 $c$ 系数。两个字符因子使用同一个实际行 $m$，没有替换成独立模数平均或要求 $(c,b)=1$。

### 两个正裕度下的完整行界

固定有界参数范围、槽数及 $c_*>0$，要求
$$
N_c-M-z_0\ge c_*,\qquad
4N_c-3M-6z_0\ge c_*.
$$
对每个指定 $\varepsilon>0$，上述实际行满足
$$
\boxed{
\sum_{0<q_m\ll Z^M}|\mathcal R_m^{\mathrm{sf}}|^2
\ll Z^{N_c+\varepsilon}.
}
$$
常数在所述固定范围及原系数合同内一致，具有有限光滑 seminorm 和固定多项式 norm-twist 高度依赖；不声明裕度趋零时的一致性或显式起点。

为说明小索引接口，先取 $0<d<c_*/200$。若立方中心 $u\ge d$，直接应用源文式 (A) 的已闭合 reduction contract；$F=r+3u=N_c+O_{\rm fixed}(1/\log Z)$ 的偏移由预留裕度支付。其 canonical 子项、行缩短、主项与 Poisson 尾部已包含在同一合同内，得到分块能量 $O(Z^{N_c+\varepsilon})$，不重算 powerful 行部分。

若 $u<d$，在原物理分块中先冻结实际 $b$，保留它唯一的一份 $q_b^{-1}$ 权重。使用精确式
$$
\mathbf1_{p\mid cb^3}
=\mathbf1_{p\mid b}
+\mathbf1_{p\nmid b}\mathbf1_{p\mid c}.
$$
落在 $b$ 上的槽自动满足，实际元组数由固定次约数函数控制；其余逐槽系数成为 $a_i(p)\mathbf1_{p\nmid b}$，仍与当前行及 $c$ 无关。$\chi_b(m)^3$ 是同一行 Hilbert 空间中的收缩乘子。对剩余 $c$ 列应用源文 canonical-moment，使用原名义上限 $z_0$，不以实际素数积替代它。列尺度为 $r=N_c-3u+O_{\rm fixed}(1/\log Z)$，两个裕度分别最多减少 $3d$ 和 $12d$，仍严格为正。

在一个立方范数块 $B$ 上，对每个指定 $\delta>0$ 有
$$
\sum_{q_b\asymp B}q_b^{-1}d_{\mathcal O}(b)^C
\ll_\delta B^\delta.
$$
所以冻结 $b$ 后的 Minkowski 只支付小幂，不能再乘一个 $Z^u$ 计数；$c$ 的归一化倒根只进入其一份允许的光滑测试。每块范数至多 $Z^{N_c/2+\varepsilon}$，对数个块由输出损失支付。单位块使用非负中心；固定 annular 偏移由共同阈值处理，不在负列长度上应用引理。

### Gaussian 与实际标记族的回接

对补偿探针的固定重缩放子集 $J$，写
$$
q=\sum_{i\in J}\ell_i,\qquad
\ell'=\frac16-q,\qquad
M'=\frac56-2q,\qquad
N_{c0}=1+\ell'=\frac76-q,
\qquad 0\le q\le\frac16.
$$
保留源文共同 Gaussian profile
$$
w_{k,J}(x,\boldsymbol\varrho)
=\chi(\log x)
W_{\mathrm G}\!\left(\frac{e^kx}{\prod_{i\notin J}\varrho_i}\right)
\prod_{i\notin J}W_i(\varrho_i),
$$
其中 $q_{cb^3}/Z^{N_{c0}}=e^kx$、$\varrho_i=q_{p_i}/P_i$。在每个 $c,b$ 分块上，把两个归一化倒根和 annular cutoffs 一起纳入完整 profile。实因子只由其共同 Fourier 密度计权一次；所有行和实际槽元组共用该密度。自动槽的范数比例仍保留在原 Gaussian 参数中。

源文 Gaussian-annular 与 smooth-calculus 给出任意固定 $A,j$ 下的
$$
\sum_{k\in\mathbb Z}e^{A|k|}p_j(w_{k,J})<\infty,
$$
并使 $|k|>\kappa_{\mathrm G}\log Z+O_{\rm fixed}(1)$ 的完整 annuli 在乘上固定行、槽与理想计数后，仍有任意指定的逆幂范数。$|\mu(b)^2|\le1$ 不扩大这些绝对计数。保留 annuli 的完成尺度是 $N_c=N_{c0}+k/\log Z$；先选择足够小的 $\kappa_{\mathrm G}$ 及内部损失，再取 $Z$ 充分大。源文的有限 seminorm 传播先于外部 Fourier 高度选择，允许用共同密度积分全部多项式高度成本。这支付所有保留块和完整 Gaussian 尾部，没有把行界外推到无界负完成长度。

实际有限修正仍先展开
$$
\overline{G(A)}=\sum_{\theta\in\widehat T}a_\theta\theta(A),
$$
然后逐项使用 $\nu=\nu_\sigma\theta$，保留原 $a_\theta$、unit/ray 因子及零支持。这里只作固定有限 triangle。非零元素行、与 $S$ 相交的行及全部 powerful 部分均在原 canonical 行和合同范围内，平方自由过滤没有引入新移动字符模数。

这份物理族的两个 leading 裕度为
$$
N_{c0}-M'-\ell'=\frac16+2q,\qquad
4N_{c0}-3M'-6\ell'=\frac76+8q.
$$
它们在整段 $0\le q\le1/6$ 上一致为正，因而实际过滤后的完成因子满足
$$
\boxed{
\left(\sum_{0<q_m\ll Z^{M'}}
|B_{m,\sigma}^{J,\mathrm{sf}}(Z)|^2\right)^{1/2}
\ll Z^{N_{c0}/2+\varepsilon}.
}
$$

### 同一探针的 Gram 消费与未支付差额

沿用源文原加性 Gram 消费，不改变另一因子、物理行或补偿系数。相对于原 $M'/2$ 行范数，新增成本为
$$
\frac{N_{c0}-M'}2=\frac16+\frac q2.
$$
原未缩放元组的 allowance 是 $3/16-q/2$，故当前元组的指数为 $17/48$。重缩放元组数 $Z^{q+\varepsilon}$ 与原系数 $Z^{-3q/2}$ 再给出整个 $J$ 的指数 $17/48-q/2$。对固定有限子集族求和，得到
$$
\boxed{
|I_{\eta,\mathrm{modified}}^{\mathrm{sf}}(Z)|
\ll Z^{17/48+\varepsilon}.
}
$$
同一过滤探针的主信号指数仍是 $C_{\mathrm{II}}(s)=s-11/16$。当前低端界只有在
$$
\beta>\frac{17}{48}+\frac{11}{16}
=\frac{25}{24}>1
$$
且 $\varepsilon$ 小于相应正差额时，才提供严格主信号比较；所以它不产生新的无零区域。不足的上界不说明真实消去失败，原高端轮廓范围 $\sigma_0\ge7/8$ 也未扩大。

无槽时，同一直接合同在固定 $0\le M<N_{\rm comp}$ 下给出能量 $O(Z^{N_{\rm comp}+\varepsilon})$。与前节 $O(Z^{(5M-N_{\rm comp})/3+\varepsilon})$ 的已支付界组合，仅在 $4N_{\rm comp}/5<M<N_{\rm comp}$ 改善该 allowance。若 $X=Y=Z^a$、$2/5<a<1/2$，则低端为 $O(Z^{(1-a)/2+\varepsilon})$，主信号预算门槛为 $4/3-5a/6$，落在 $11/12$ 与 $1$ 之间。改变几何后的完整无限行高端比较仍未支付。

本节补齐的是实际平方自由立方索引的共同标记族转移。原完整有符号 Robin 响应、所有实际零点数据与严格核心仍是原目标；严格 Robin 与 RH 尚未证明。

## 完整相位运输后的有符号联合低端

本节的完整估计是仓内综合推导，前置是主稿已有的完整物理 Poisson 系数、逐系数相位运输、零槽 plain 矩与 sixth-power amplification。上述局部和矩定理直接复用；这里补的是实际带标记平方自由立方索引族的共同指标、零掩码和归一化关系。源文输入作为前提，整篇源证明及 Lean 未独立认证，不主张历史原创性。

在原固定算术数据、固定槽数及有界参数范围内，对每个指定 $\varepsilon>0$，实际过滤后的补偿探针满足
$$
\boxed{
|I_{\eta,\mathrm{modified}}^{\mathrm{sf}}(Z)|
\ll_\varepsilon Z^{21/64+\varepsilon}.
}
$$
常数和充分大阈值可以依赖原算术数据、槽系统及有限光滑 seminorm；全部参数高度按源文的有限阶传播支付。原零延拓、共享素因子、所有素幂行和 Gaussian 尾部均保留。

### 原物理变换与剩余列

使用主稿的物理系数 $F_{\mathrm{phys}}(s,C,H)$，其中 $C=cb^3$；它与两份同参数 Gauss 和的有限相关式不同。原 $G_{\mathrm{ray}}$、$\Xi$、辅助字符和 reciprocity 的完整运输给出 Poisson 外因子
$$
\frac{\sqrt{X'}}{\sqrt{q_{b_*}}q_C},
$$
并将 $Y'^{-1}$ 留在外面。原 Fourier 参数是 $X'q_H/q_C$；固定原始字符使 $H=0$ 和与 $S$ 相交的行为零。

对固定重缩放子集 $J$ 及实际元组，记
$$
q=\sum_{i\in J}\ell_i,\quad
\ell'=\frac16-q,\quad
X'=\frac{Z^{17/48-q}}{r_J},\quad
Y'=\frac{Z^{23/48-q}}{r_J},\quad
N_0=1+\ell'=\frac76-q.
$$
原 $r_J$ 在固定紧正区间内。保留一个共同 Gaussian profile；在其 annulus 上写 $N=N_0+\theta_N$。源文 Schwartz 衰减及绝对计数允许使用独立于 $c,b$ 和槽元组的外层频率截断
$$
q_H\le Z^{13/16+\kappa_{\mathrm G}+\tau}.
$$
固定所需节省与参数范围后，先选择有限 Schwartz、seminorm 和高度权阶数，再选择小的 $\kappa_{\mathrm G},\tau$ 及内部损失，最后令 $Z$ 充分大。完整 Gaussian annuli 使用源文的所有有限阶 summability，而不让某一个既定阶数承担任意节省。

对每个非零项定义
$$
g=(c,b),\qquad B_s=(b,s),\qquad E=(c/g,s),\qquad
c_0=c/(gE),\qquad s_0=s/(B_sE).
$$
源文完整素幂表在 $c,b$ 平方自由时限制 $v_p(C)\in\{0,1,3,4\}$，但不限制 $v_p(s)$。它给出 $b,g,B_s,E\mid\operatorname{rad}H$，$E$ 与 $b$ 互素；$c_0,s_0$ 均与 $H$ 互素且 $(c_0,s_0)=1$。$s_0$ 中不与 $C$ 相交的 powerful 部分仍在原求和中。每行这些标签及分支的选择有固定次约数函数界。

在原全部相位已运输以后，$H$ 外的 $c_0,s_0$ 系数恰为
$$
\mu(c_0)\eta(c_0)\overline{\chi_{c_0}(H)}\chi_{s_0}(H).
$$
这使用主稿的 complete local family monomials；没有分别替换原低端两因子的系数。剩余局部角相位、Gauss 相位、符号、unit 及 finite-ray 修正仍作为有界行标量保留。

连同原 $q_c^{-1/2}q_b^{-1}$，物理绝对幅度是
$$
\frac{\sqrt{X'}}{Y'}\,
q_b^{-3/2}q_g^{-1/2}q_{B_s}^{1/2}L_E
$$
乘上带 $q_{c_0}^{-1}$ 权重的逆列与未规范化的 $s_0$ 列。这里每个 $p\mid E$ 保留其实际两项 Ramanujan 值及相位，并有
$$
|L_p|=
\begin{cases}
q_p^{-1},&v_p(H)=1,\\
1-q_p^{-1},&v_p(H)\ge2.
\end{cases}
$$
因而 $|L_E|\le1$。对 $p\mid b$、$p\nmid g$，$s$ 不含或含 $p$ 时幅度分别为 $q_p^{-3/2},q_p^{-1}$；对 $p\mid g$，分别为 $q_p^{-2},q_p^{-3/2}$。这些是原局部单项式与物理倒根的合并结果。

### 全部标记与精确互素展开

自动满足的槽恰是所选素数落在 $bE$ 中的槽。它们的实际元组来自同一个 $H$ 的约数，以约数界计重；其原权重、相位及归一化比例留在共同 profile。记其名义总长为 $z_A$。其余槽的总长 $z_K=\ell'-z_A$，实际素数积为 $P\mid c_0$，且 $(P,H)=1$。令 $c_0=Pn$，平方自由性给出
$$
\mu(c_0)\psi_H(c_0)
=\mu(P)\psi_H(P)\mu(n)\psi_H(n)
 \mathbf1_{(n,P)=1},
\qquad
\psi_H(n)=\eta(n)\overline{\chi_n(H)}.
$$
原 $q_{c_0}^{-1}$ 权重提供 $q_P^{-1}$，这些未分配槽的加权元组质量是小幂，不能再乘其完整计数。原 Gaussian 参数继续包含全部槽，包括自动槽。

保留 $\mathbf1_{(s_0,P)=1}$，并展开剩余互素关系：
$$
\mathbf1_{(n,s_0)=1}=\sum_{d\mid(n,s_0)}\mu(d),
\qquad n=dn_1,\quad s_0=ds_1.
$$
展开的 $\mu(d)$ 与逆列中既有的 $\mu(d)$ 相乘。字符的两份 $d$ 因子在自然单位支持上抵消，所以精确行标量是
$$
\boxed{\mu(d)^2\eta(d)\mathbf1_{(d,H)=1},}
$$
并保留原 $P,S$ 限制。逆列的额外零掩码是 $Pd$，plain 列的是 $P$；两列分别调用各自的矩定理，不要求这两个额外掩码相同。中心规范化后仍有 $q_d^{-1}$；对有界多项式范数范围，其整条质量由理想计数支付为小幂。

写实际标签长度为
$$
u=\log_Zq_b,\quad v=\log_Zq_g,\quad e=\log_Zq_E,\quad
d_b=\log_Zq_{B_s},\quad w=\log_Zq_d.
$$
剩余逆列和 plain 列的中心分别为
$$
r=N-3u-v-e-z_K-w,\qquad
n=\frac{23}{48}-q-d_b-e-w,
$$
带固定 annular 偏移。自动槽的实际素数积整除 $bE$，故
$$
z_A\le u+e+O_{\rm fixed}(1/\log Z),\qquad
r\le1+\theta_N-2u-v-w+O_{\rm fixed}(1/\log Z).
$$
特别地 $r\le1+O(\kappa_{\mathrm G})$。这是同一标签实现上的约束。非空单位窗口以下的中心只在固定常数范围内裁到零；不在无界负长度上使用矩定理。

将两个中心平方根与所有原 $b,g,E,B_s$ 根因子合并，得到共同外幂
$$
Z^{-9/16-(z_A+\theta_N)/2}.
$$
$q_P^{-1},q_d^{-1}$ 单独支付各自标签质量；实倒根进入同一个 profile 一次。固定 $a,P,d$ 和 unit 扇区后，共同 logarithmic Fourier 分离、源文的 scale supremum 与参数 Sobolev 先支付标签引起的尺度和 profile 选择，再取正矩。只有在完成这层对应以后，剩余有界行标量及行约数重数才按小幂移出；约数重数本身不承担 profile 对应。

### 额外掩码的逆矩接口

源文 amplified inverse 定理没有任意额外 puncture 的直接接口。这里在完整估计内使用理想 Euler 系数等式：若逆列再乘 $\mathbf1_{(n,Q)=1}$，则
$$
M_{\psi,Q}(D;W)
=\sum_{\operatorname{rad}\lambda\mid Q}
\psi(\lambda)q_\lambda^{-1/2}
M_\psi(D/q_\lambda;W).
$$
所有素幂和 $\psi$ 的原零支持都保留。其系数质量不超过
$$
\prod_{p\mid Q}(1-q_p^{-1/2})^{-1}\ll_\varepsilon Z^\varepsilon
\qquad(q_{\operatorname{rad}Q}\le Z^B,\ B\text{ 有界}),
$$
直接使用源文 deleted Euler-factor mass。Annular 测试只留下有限个非空尺度。Minkowski 与源文适用于全部 $U,D\ge1$ 的一般 amplification 界，在每个尺度调用原定理；其指数随逆列长度不减。小尺度在固定单位窗口裁切，有限 seminorm 和高度因素仍保留。此处没有将增长掩码加入固定 $S$，也没有扩大原定理的列系数类。

### 全部频率素幂与两份分别的第二矩

按原约定写 $H=\zeta u_0a^6$，其中 $u_0$ 的各素数重数不超过五。固定 unit 扇区及 $a$ 的长度块 $t$，有
$$
m_t=\frac{13}{16}-6t,\qquad
0\le t\le\frac{13}{96},
$$
加上预留小偏移；$a$ 的数量成本为 $Z^{t+\varepsilon}$。自然 $H$ 零支持是 $u_0$ 零支持与 $\operatorname{rad}a$ 的并。逆列的额外掩码是 $\operatorname{rad}(aPd)$，plain 列的是 $\operatorname{rad}(aP)$，在当前行和中均已冻结且处在有界多项式范数范围；unit 字符运输到固定有限 twist 族。

零槽 plain 引理的第二因子可取长度零、只选单位理想的测试。该因子等于 $1$，它与第一 plain 因子使用同一字符和掩码，因而原定理直接给出非主诱导行上的第二矩
$$
\sum_{u_0}|S_{u_0}(n)|^2\ll Z^{m_t+\varepsilon}
$$
且不限制有界非负 $n$。逆列通过上述 puncture 接口及源文一般 amplification 给出
$$
\sum_{u_0}|M_{u_0}(r)|^2\ll Z^{E(m_t,r)+\varepsilon},
\qquad
E(m,r)=\max\{m,(m+5r)/6\}.
$$
使用一般全部 $U,D$ 公式，不使用在 $m\to0$ 时比值无界的固定比值推论。逆列与 plain 列的固定 twist 可不同：$\eta$ 留在逆列；这里是两份分别的第二矩，在同一实际 $u_0$ 行上 Cauchy，没有向 plain 定理塞入 Möbius 系数。

使用 $r\le1$ 的 leading 界，合并 $a$ 数量与外幂，非主行的指数为
$$
-\frac9{16}+t+\frac{m_t+E(m_t,1)}2
=\frac{21}{64}-\frac52t.
$$
固定范围内的频率、标签和互素变量 dyads 为对数个，由输出损失支付。所有因子使用共同分离密度；有限参数阶数先于外部高度选择，完整 Gaussian/Fourier 尾部仍由其全部有限阶 summability 支付。因此该界覆盖整个非主族。

### 主诱导行与完整补偿求和

由于 $(H,S)=1$，一个主 plain 诱导字符不能在 $u_0$ 中有 good prime：该处重数 $1,\ldots,5$ 都给出非主 tame 局部字符。因此这里只剩有限 unit 扇区。非主的有限 unit 字符已在前面的第二矩内。主扇区的逆字符保持其原 $\eta$/unit twist，不设其响应为零。

对这份固定有限字符族，复用所引 $7/8$ 半平面及 reciprocal strip 控制；在 $\sigma=7/8+\varepsilon<1$ 上 Mellin 估计给出
$$
|M_{\rm fixed,Q}(Z^r)|\ll Z^{(\sigma-1/2)r+\varepsilon},
$$
额外掩码由同一 Euler 等式统一支付。Plain 因子使用 $Z^{n/2+\varepsilon}$ 体积界。保留实际尺度后，主扇区的指数为
$$
\begin{aligned}
&\frac{17/48-q}{2}+\sigma-1+t
 +(\sigma-1)(z_A+\theta_N)\\
&\quad-3(\sigma-1/2)u-(\sigma-1/2)v
 -d_b/2-\sigma e-\sigma w.
\end{aligned}
$$
除 collar 偏移外，后面的标签项均非正，$t\le13/96$，故其上界为 $3/16-q/2+\varepsilon$。主行与全部 $a^6$ 部分均已计入。

于是固定未缩放元组的完整 allowance 为 $21/64+\varepsilon$。原重缩放元组数 $Z^{q+\varepsilon}$ 与物理系数 $Z^{-3q/2}$ 给出整个 $J$ 的
$$
\frac{21}{64}-\frac q2+\varepsilon.
$$
对固定有限子集族求和即得本节整族界。与前节的 $17/48$ 界同时成立，当前更小 allowance 的改善为
$$
\frac{17}{48}-\frac{21}{64}=\frac5{192}.
$$
这比较的是已证明上界，不主张真实响应取到任一个指数。

同一探针的主信号仍为 $C_{\mathrm{II}}(s)=s-11/16$，名义比较门槛为
$$
\boxed{\frac{21}{64}+\frac{11}{16}=\frac{65}{64}>1.}
$$
所以本节没有产生新的无零区域，未扩大高端轮廓合同，也未证明原完整有符号 Robin 余量。实际零点实部、双符号、全部高度与重数、完整系数、正 $r_A$ 和严格核心仍是原目标；严格 Robin 与 RH 尚未证明。

## 保留素标记的共同字符低端

本节复用前节的完整物理相位运输、共同 Fourier/Gaussian 分离、全部 sixth-power 行、逆列 puncture 与一般 amplification。新增接口是在实际分母素标记中保留一个短子集，与 plain 列共同取矩。前置仍是所引主稿的估计，包括正长度素槽矩使用的 $7/8$ 半平面；未独立认证整篇源证明，未执行 Lean 核验，不主张历史原创性。

对每个指定 $\varepsilon>0$，在原合法的不交素窗口构造中把固定槽网格选得足够细后，同一完整修改探针满足
$$
\boxed{
|I_{\eta,\mathrm{modified}}^{\mathrm{sf}}(Z)|
\ll_\varepsilon Z^{19/64+\varepsilon}.
}
$$
本结论的槽选择条件不可删除：它使用源文允许预先增大固定偶数槽数 $K$ 的构造，不声称任意粗槽系统都具有所需短子集，也不把量词改成同一个已固定槽系统实现任意小损失。常数、有限 seminorm 阶数、高度阶数和充分大阈值按原固定算术数据及固定槽系统取值。

### 保留的标记与精确规范化

沿用重缩放槽总长 $q$、自动槽总长 $z_A$ 及非自动槽集合 $\mathcal K$，其总长为
$$
z_K=\frac16-q-z_A.
$$
从 $\mathcal K$ 选一个继续共同求和的子集 $\mathcal L$，总长为 $z$；仅冻结其余槽的实际素数积 $P_R$。实际组成仍为
$$
c_0=P_RP_Ln_0,qquad
(n_0,P_RP_L)=1,qquad(s_0,P_RP_L)=1.
$$
原互素展开 $n_0=dn_1,\ s_0=ds_1$ 保留精确标量
$$
\mu(d)^2\eta(d)\mathbf1_{(d,H)=1}
$$
及 $(d,P_RP_L)=1$。因此所有选择的素数仍然已从 $c_0$ 中除去；继续共同求和的槽不改变剩余逆列长度
$$
r=N-3u-v-e-z_K-w\le1+\theta_N-2u-v-w+O_{\rm fixed}(1/\log Z).
$$
Plain 长度仍是 $n=23/48-q-d_b-e-w\le23/48$，带原 collar 约定。

原补偿标记还带有 $\overline{\eta(p)}$，它与抽取逆列的 $\eta(p)$ 精确抵消：
$$
\overline{\eta(p)}\mu(p)\eta(p)\overline{\chi_p(H)}=-\overline{\chi_p(H)}.
$$
因此保留的槽形成中央规范化素乘积
$$
Q_L(H)=\prod_{i\in\mathcal L}
\left[Z^{-\ell_i/2}\sum_{p\in\mathcal P_i(Z)}
\overline{\chi_p(H)}w_i(q_p/Z^{\ell_i})\right].
$$
原素号 $\mu(p)=-1$ 是固定标量，$q_p^{-1}$ 中的有界 annular 因子 $1/y_i$ 并入光滑 $w_i$。原共同 Fourier 高度进入这些测试的 norm twist；它们不成为逐行另选的素系数。由实际 $q_{P_L}^{-1}$ 权重，未冻结素元组的贡献恰好多出一个 $Z^{-z/2}Q_L$。所有实倒根只计一次，完整外幂为
$$
\boxed{Z^{-9/16-(z_A+\theta_N)/2-z/2}.}
$$
冻结的 $P_R,d$ 保留前节的 $q_{P_R}^{-1},q_d^{-1}$ 小幂质量。自动槽、共享素因子和物理局部相位完整保留。

### 同一字符、共同掩码与全部重叠

先冻结 $a,P_R,d$ 和 unit 扇区。逆列已在 $d$ 处 puncture，保留槽也必须避开 $d$，而原 plain 列无需避开 $d$。为使用源文要求的共同掩码，使用普通 plain 系数的精确 Euler 恢复式
$$
S_\chi(D;W)=
\sum_{\operatorname{rad}\lambda\mid d}
\chi(\lambda)q_\lambda^{-1/2}
S_{\chi,(d)}(D/q_\lambda;W).
$$
$S_{\chi,(d)}$ 增加模 $d$ 的互素条件，其余自然零支持及 $P_R$ 掩码不变。系数质量由原 deleted-factor 界支付为小幂；只有有限尺度能满足 annular 支持。这一步保留全部素幂，降低 plain 长度，并把 plain 与素槽放在同一个固定掩码中。后续冻结重叠素数时按同一等式处理新增共同掩码。

在绝对值 $|M_{\eta\overline\chi}S_\chi Q_L|$ 中共轭整个 $Q_L$，其行字符便成为 $\chi_p(H)$，与 plain 列一致。相对素系数为 $1$，原 $1_T$ 限制通过 $\widehat T\subseteq\Theta$ 的固定有限字符展开保留。逆列仍使用 $\eta\overline\chi$，两份矩分别调用。这里没有向 plain 矩插入 Möbius 整数系数，也没有只共轭部分字符或删去原零延拓。

剩余实际条件 $(P_L,n_1s_1)=1$ 必须保留。展开
$$
\prod_{i\in\mathcal L}
(1-\mathbf1_{p_i\mid n_1})(1-\mathbf1_{p_i\mid s_1}).
$$
对一个有限重叠模式 $B_n,B_s\subseteq\mathcal L$，冻结 $B_n\cup B_s$ 中的素数，置 $n_1=P_nn_2,\ s_1=P_ss_2$。记相应总长为 $z_n,z_s,z_O$，交集总长为 $z_\cap=z_n+z_s-z_O$。Möbius 的精确抽取仍要求 $(n_2,P_n)=1$；所有固定掩码同步运输。

两列中央规范化贡献 $Z^{-(z_n+z_s)/2}$，冻结素数的原槽规范化及完整计数至多贡献 $Z^{z_O/2+\varepsilon}$，净幂为
$$
-\frac{z_n+z_s-z_O}{2}=-\frac{z_\cap}{2}\le0.
$$
每一展开项中的剩余活动槽自由求和；原排除条件由完整有符号展开恢复，不在矩调用中保留耦合指标。因此没有遗漏正的重叠计数成本。逆列、plain 列及剩余活动槽的长度分别降为 $r-z_n,\ n-z_s,\ z-z_O$；其正槽容量和逆矩指数不增加。实际支持为空的尺度不产生项，有界非空 subunit 尺度按前节 clipping 与 collar 处理。两列都含某个槽素数的情形也在这份有限展开中。

共同分离先于正矩：活动槽的有限-ray 系数保持跨行固定，原 slot 测试只承接共同 Fourier 高度；其余标签引起的尺度及轮廓选择由前节已经支付的 scale supremum 和参数 Sobolev 控制承担。约数重数不能替代这一对应。

### 正槽容量与整族估计

仍写 $H=\zeta u_0a^6$，令 $a$ 的长度为 $t$，则
$$
m_t=\frac{13}{16}-6t,qquad0\le t\le\frac{13}{96},
$$
且 $a$ 的计数成本为 $Z^{t+\varepsilon}$。非 unit 的 $u_0$ 含有重数 $1,\ldots,5$ 的 good prime，故其 plain 诱导字符不属于固定 $\Theta$，符合正槽矩的实际排除集合。有限 unit 字符族，包括其中非主但属于 $\Theta$ 的字符，使用前节固定字符 reciprocal-strip 与 plain 体积估计；其 $3/16-q/2+\varepsilon$ 上界仍足够。

取 $\kappa=3/4$，明确使用所引全部有限阶字符族的 $\beta_*\le7/8$ 前提，不能替换为单一目标字符的结论。源文正槽 plain 矩的第二因子只取单位理想，在
$$
n+\frac92z\le m_t
$$
时给出 $\sum_{u_0}|S_\chi\overline{Q_L}|^2\ll Z^{m_t+\varepsilon}$。所有重叠和 Euler 恢复项使左边容量表达式下降。逆列复用一般 amplification 指数
$$
E(m,r)=\max\{m,(m+5r)/6\}.
$$
在同一实际 $u_0$ 行上 Cauchy，合并外幂与 $a$ 数量，得到
$$
-\frac9{16}-\frac{z_A+z}{2}
+t+\frac{m_t+E(m_t,1)}2
=\frac{21}{64}-\frac{z_A+z}{2}-\frac52t
$$
加上已预留的小偏移。完整 $J$ 元组计数与原物理系数继续提供 $-q/2$。不保留槽时，前节上界同样适用。

预先把所有槽长压到 $\eta$ 以下，并把 $\eta/2$ 及所有 collar、矩和高度损失纳入指定 $\varepsilon$。若 $q+z_A\ge1/16$，旧界已经至多为 $19/64+\varepsilon$。否则可用非自动槽总长超过 $5/48$，贪心选取固定窗口子集能达到 $z\in[z_*-\eta,z_*]$。按同一实际 $t$ 采用以下三种估计：

| 频率范围 | 保留槽目标 $z_*$ | 容量余量或旧界 | 完整低端指数上界，未含预留损失 |
|---|---:|---|---:|
| $0\le t\le1/128$ | $1/16$ | $49/64-(23/48+9/32)=1/192$ | $19/64+\eta/2$ |
| $1/128<t<1/64$ | $1/32$ | $23/32-(23/48+9/64)=19/192$ | $75/256+\eta/2<19/64+\eta/2$ |
| $t\ge1/64$ | 不保留槽 | 旧界 $21/64-5/128$ | $37/128<19/64$ |

所有实际配置使用同一组 $q,z_A,t$，不是分别取可达极值后拼接。有限槽子集、互素重叠、全部 sixth-power 行、两种 Ramanujan 分支及共同 Gaussian/Fourier 尾部均保留。源文所有有限阶 summability 的使用顺序仍是先固定所需节省与参数范围，选择有限测试和高度阶数，再取 $Z$ 充分大。求和得到本节完整 $19/64+\varepsilon$ 界。

相较前节 $21/64$ allowance，改善为 $1/32$。同一探针的主信号没有改变，其名义比较门槛是
$$
\frac{19}{64}+\frac{11}{16}=\frac{63}{64}.
$$
正槽前置本身已经使用更强的所引 $7/8$ 无零半平面，因此此门槛不提供新的无零区域。原高端合同未扩大，完整有符号 Robin 余量、实际零点数据、正 $r_A$ 与严格核心仍未证明；本节不证明 RH。

## 高端误差素项与同一行支持的联合估计

本节复用平方自由立方索引的实际高端恒等式、全部局部因子、所引 primitive 分子反射界和原动态行分区。新增接口把完整误差素元组的幅度与同一行上的平方整除条件共同估计；不改变主字符项、目标分母或原物理探针。所有结论以这些文献输入为前提，未执行 Lean 核验，未独立认证整篇源证明，不主张历史原创性。

令 $U=Z^d$，固定动态中央实部
$$
x_r=a+16e,\quad w_r=1-a-6e,\quad z_r=c=17/50,
\quad51/100\le a\le1,\quad0<e<10^{-3},
$$
并记 $\delta=2a-1$。固定原窗口系统、误差槽子集 $I$ 及其总长 $z_I$。在实际 buffered 非主行区间内，先按活动主素因子和 witness 数据确定行集合 $\mathcal C$，再选择误差素元组。假设原共同计数给出
$$
\#\mathcal C\ll U^{R+\varepsilon}(1+T_1)^A,\qquad0\le R\le1.
$$
这个集合和共同指数 $R$ 必须独立于误差素元组。令 $g=\sum_{i\notin I}\ell_i g_i$ 为实际主素因子幅度的总贡献。

完整误差子族相对原中央 allowance 的额外节省为
$$
\boxed{\Lambda_I=\frac\delta2\,[z_I-d(1-R)]_+.}
$$
它控制原完整修正的误差部分，不控制 $I=\varnothing$ 的全主字符项，也不声称已把整个物理高端移到新的轮廓。

### 在修正因子零点处仍成立的分解

令
$$
\mathcal R_p=G_p^{\mathrm{sf}}+
\overline{\chi_p(u)}H_p^{\mathrm{sf}}.
$$
精确局部替换是
$$
G_p^{\mathrm{sf}}=-\overline{\chi_p(u)}H_p^{\mathrm{sf}}+\mathcal R_p.
$$
定义原主素和
$$
\mathcal Q_i(u;z)=-\sum_{p\in\mathcal P_i(Z)}
W_i(q_p/P_i)q_p^{z-1}\overline{\chi_p(u)}.
$$
其相对系数为 $1$；原补偿项的 $\overline{\eta(p)}$ 已在 $G_p^{\mathrm{sf}}$ 中保留，不能额外插入 $\eta(p)$。原 $1_T$、排除集和非单位零延拓不变。

将所有选中素数逐项分为主项和误差项。每个主项把其 $H_p^{\mathrm{sf}}$ 恢复到乘积中，互不相交的窗口允许主素和独立提出，得到
$$
\mathfrak H_{\eta,u,Z}^{\mathrm{sf}}
=\sum_I\left(\prod_{i\notin I}\mathcal Q_i\right)
\sum_{(p_i)_{i\in I}}
\left[\prod_{i\in I}W_i(q_{p_i}/P_i)q_{p_i}^{z-1}\mathcal R_{p_i}\right]
\prod_{\substack{p\notin S\\p\notin\{p_i:i\in I\}}}H_p^{\mathrm{sf}}.
$$
这个等式不含 $G_p/H_p$，因此也在 $H_p^{\mathrm{sf}}$ 的零点处成立。乘积估计必须保留实际 buffered 实部：
$$
x_r+w_r=1+10e,\qquad -x_r-w_r=-1-10e.
$$
既有未分歧缺陷幂为 $-x_r-6c,-x_r-w_r,-w_r-6c,1-x_r-w_r-6c$，需要时加上至多 $6e$ 的 $(-w_r)_+$，仍全部严格小于 $-1$。分歧幂为 $1-x_r-w_r,3/2-3x_r,2-3x_r-w_r,2-4x_r,5/2-4x_r-w_r$；第一项等于 $-10e$，其余也在上述范围严格为负。这些 buffer 不能在乘积收敛步骤中丢掉。每个未选择子乘积都直接上界为 $O_\varepsilon(U^\varepsilon)$，无需先证明倒数有界。

### 幅度不能与支持条件拆开

对 $p\nmid u$，复用实际 $j=0$ 式得到
$$
\mathcal R_p=
\frac{\overline{\chi_p(u)}(1-W)}{1-D}
\left[V(1-QW)-D(1-V)(1-W)-D(Q-1)WV(1-W)\right].
$$
由于 $(-w_r)_+\le6e$、$a\le1$ 及 $6c=51/25$，其完整高度一致界是 $O(Q^{-a+O(e)})$。按原窗口求和，得到相对中央素规范化的 $P_i^{-\delta/2+O(e)}$ 节省。

对 $p\mid u$，$\mathcal R_p=G_p^{\mathrm{sf}}$。重数 $j=1$ 的严格项仍带 $V$，有 $G_p^{\mathrm{sf}}=O(Q^{a-1+O(e)})$；$2\le j\le5$ 时，实际共同严格项为 $Q^{1-w_r}=Q^{a+6e}$，边界项不大于此量。不能把这些分歧因子单独称为衰减误差。

原 primitive 分子反射界使用同一行的真实 conductor。每个选中分歧素数在 conductor 中至多出现一次，在 $q_u$ 中则出现 $j$ 次；不同槽素数互异。因此同时分配这些实际缺口后，分子界包含
$$
U^{\delta/2+O(e)+\varepsilon}(1+T_1)^A
\prod_{p_i\mid u}q_{p_i}^{-(j_i-1)\delta/2+O(e)}.
$$
分子成本只支付一次，原 redundant 零支持及固定素数仍保留。与 $q_p^{z-1}G_p^{\mathrm{sf}}$ 合并，相对 $P_i^{c-1/2}$ 的幂为
$$
a-3/2\le-\delta/2\quad(j=1),\qquad
-(j-2)\delta/2\quad(j\ge2).
$$
因此只有 $j=2$ 没有 leading 节省；其余分歧分支和未分歧误差都至少节省 $\delta/2$ 乘相应槽长。

### 用同一批实际行取得联合界

把误差槽分为 $v_p(u)=2$ 与其补集。设重数恰为 $2$ 的槽总长为 $z_2$。每一份实际元组都满足 $p_i^2\mid u$。计数同一批配对 $(u,(p_i))$：逐行只有约数多种分配，故原行集合界给出 $Z^{dR+\varepsilon}$；另一方面有 $O(Z^{z_2+\varepsilon})$ 份素元组，每份要求其平方积整除 $u$，所以完整配对数至多为 $Z^{d-z_2+\varepsilon}$。

只计非空 annulus，单位窗口的固定比例由原支持约定支付。这两个界适用于同一批配对，故组合为
$$
\min\{Z^{dR},Z^{d-z_2}\}Z^\varepsilon,
$$
不能把两种收益相乘。未选择子乘积的共同上界不依赖误差元组，剩余分歧分配由约数界支付，未分歧误差素和由上述完整窗口界支付。对每个实际误差分支，得到
$$
\begin{aligned}
\sum_{u\in\mathcal C}
\left|L^S(w,\chi_\bullet(u))
\mathfrak H_{\eta,u,Z}^{\mathrm{sf},(I,z_2)}\right|
\ll{}&U^{\delta/2+O(e)+\varepsilon}(1+T_1)^A\\
&\cdot Z^{\ell(c-1/2)+g-\frac\delta2(z_I-z_2)
+O(e+\vartheta+\varepsilon)}
\min\{Z^{dR},Z^{d-z_2}\}.
\end{aligned}
$$
有限分支全部求和，原零掩码、物理素幂、完整系数和共同高度参数均保留。

相对原中央上界，实际分支的节省是
$$
\Lambda_{I,z_2}=
\frac\delta2(z_I-z_2)+[z_2-d(1-R)]_+.
$$
对 $0\le z_2\le z_I$ 的两个线性区间取界，使用 $0<\delta\le1$，便有 $\Lambda_{I,z_2}\ge\Lambda_I$。当 $R=1$ 时，每个非空误差槽子集节省 $\delta z_I/2$；当 $z_I\le d(1-R)$ 时，不声称额外统一节省。

### 原轮廓合同与剩余主族

保留原实际 Mellin 权重，中央 leading 指数为
$$
B=l_x(1/2-c)+(a+c-1)-a l_y+
\ell(c-1/2)+g+d(R+\delta/2-c).
$$
上述完整误差子族的指数是 $B-\Lambda_I$，并保留原 $(16-6l_y)e$ buffer、分子与乘积的 $O(e+\vartheta+\varepsilon)$ 成本、全部有限 seminorm 和高度成本。实际严格节省还须让这些可调成本小于正的 leading 裕度。只在整个固定动态 bin 已确定后估计其保留 integrand；不能给自适应行集合另外移动轮廓。

原外部坐标的累计高度分配、辅助积分和完整尾部仍需按所引合同支付。作为中央 integrand／保留积分的供给，上述关系不改变 $\sigma_0$；只有已经验证原 stage 假设的范围才能应用原 bin-contour accounting。本节不把其 $\sigma_0\ge7/8$ 范围延伸到下方，也不把低端使用的 $\beta_*\le7/8$ 与原高端反证框架的 $\beta_*>\sigma_0$ 当作同一组相容前提。

全主字符项 $I=\varnothing$ 的 $\Lambda_I=0$，仍需要真实的联合行消去或更强共同计数；本节没有将它遗漏。完整无限行高端比较、原 Robin 有符号余量、正 $r_A$ 与严格核心仍未证明，RH 仍未证明。

## 完整根数、共同掩码与全部素标记的混合留数估计

本节处理 $\eta=1$ 的平方自由立方索引探针。复用主稿的本原函数方程、导子与互反律、既有过滤局部系数，以及 Gao–Zhao [《Moments and one level density of sextic Hecke L-functions》arXiv v2](https://arxiv.org/abs/2201.01885) 的 Lemma 4.1；不重证该 Gauss 和估计。下述综合估计以这些输入及经典本原有限字符 Gauss 根数规范为前提，不是整篇主稿的独立证明或 Lean 核验。

### 同一份完整留数与两项行界

固定紧实实部范围 $1/2<a=\Re x<1$、$c=\Re z\ge17/50$，保留两变量的全部高度。$W_U(q_u/U)$ 是固定光滑物理范数 annulus，$U\ge1$，$P_i=Z^{\ell_i}$ 为原有互不相交素槽，$\ell=\sum_i\ell_i$。令 $\psi_u$ 为原行诱导的本原字符，$f_u$ 为其导子范数，$E_u,E_{\bar u}$ 为原删除 Euler 因子。精确对角函数方程给出
$$
K_u(x)=\varepsilon(\psi_u)(3f_u)^{x-1/2}(2\pi)^{1-2x}
\frac{\Gamma(x)}{\Gamma(1-x)}
\frac{E_u(1-x)}{E_{\bar u}(x)}.
$$
本原 $L$ 值的消去是 $w=1-x$ 上的亚纯恒等式；根数、导子、gamma 商与删除因子仍在。一般函数方程复用主稿所引 [Gao–Zhao, Equation (1.1)](https://arxiv.org/abs/1707.00091)，混合根数识别还使用独立列明的经典有限 Gauss 规范。

在混合面上，完整素元组为
$$
\widetilde{\mathfrak H}^{\rm sf}_u
=\sum_{(p_i)}\prod_i
\left[W_i(q_{p_i}/P_i)q_{p_i}^{z-1}(1-q_{p_i}^{-1})G_{p_i}^{\rm sf}\right]
\prod_{\substack{p\notin S\\p\notin\{p_i\}}}F_p,
\qquad F_p=(1-q_p^{-1})H_p^{\rm sf}.
$$
所有因子取在 $(x,1-x,z)$，$G_p$ 已含原补偿操作。该式由
$\mathfrak H_u^{\rm sf}=\zeta_F^S(x+w)\widetilde{\mathfrak H}^{\rm sf}_u$
的精确混合因子提取得到，不除以可能为零的 $H_p$。定义
$$
R_U(x,z)=\sum_{\substack{u\ {\rm sixth\ power\ free},\ (u,S)=1\\u\ {\rm nonprincipal}}}
W_U(q_u/U)q_u^{-z}\overline{\xi(u)}K_u(x)
\widetilde{\mathfrak H}^{\rm sf}_u(x,1-x,z).
$$
对每个指定 $\varepsilon>0$，同一完整行与元组满足
$$
\begin{aligned}
|R_U(x,z)|\ll{}&(1+|\Im x|+|\Im z|)^C U^\varepsilon Z^\varepsilon\\
&\times\left[
U^{a+1/6-c}\prod_iP_i^{c+1/6}
+U^{a+5/14-c}\prod_iP_i^{c+1/14}\right].
\end{aligned}
$$
常数依赖固定算术数据、实部范围、光滑 seminorm、合法槽系统和指定损失。全部根数、五种行重数、素标记碰撞、共同零掩码与完整高度均包括在界内。非主单位扇区保留；$u=1$ 的主行另行处理。这不是对零点自适应选择的任意子族的估计。

### 文献估计与实际根数运输

Gao–Zhao Lemma 4.1 允许任意 $d\in\mathcal O$，对 $(b,6)=1$ 给出
$$
\sum_{\substack{n\ E\text{-primary}\\Nn\le M,\ b\mid n}}
\overline{(d/n)_6}\frac{g_6(n)}{\sqrt{Nn}}
\ll N(d)^{1/6+\varepsilon}N(b)^\varepsilon M^{2/3+\varepsilon}
+N(d)^{1/14}N(b)^{-4/7}M^{6/7+\varepsilon}.
$$
在同一平方自由 puncture $f$ 上约数容斥，再以实际光滑 profile 部分求和，得到
$$
\sum_{\substack{n\ E\text{-primary}\\(n,f)=1}}
\gamma_1(n)\overline{\chi_n(d)}V_0(Nn/M)
\ll p_J(V_0)N(f)^\varepsilon
\left[M^{2/3+\varepsilon}N(d)^{1/6+\varepsilon}
+M^{6/7+\varepsilon}N(d)^{1/14+\varepsilon}\right].
$$
$g_6(n)$ 的自然零支持去掉非平方自由项。降为零指数的字符仍保留互素掩码；舍去 $N(b)^{-4/7}$ 是合法放宽，不与另一独立最优值拼接。

写原行
$$
u=\epsilon_u n b_2^2b_3^3b_4^4b_5^5,\qquad B=b_2b_3b_4b_5,
$$
五个理想因子平方自由、两两互素且避开 $S$。原导子论证给每个 good prime 精确重数 $1$，所以导子是 $f_0nB$，其中 $f_0\mid(36)$ 为实际固定扇区的本原部分。保留 primary/E-primary 生成元的变换相位。令 $a_P=v(a)a$ 为 primary 生成元，互反律给出
$$
\psi_u((a))=\theta_u(a)\prod_{p\mid nB}\chi_p(a)^{j_p},
\qquad
\theta_u(a)=\epsilon_u^{(Na-1)/6}\mathcal R(u_0,a_P)v(a)^{(Nu_0-1)/6},
$$
其中 $u_0=nb_2^2\cdots b_5^5$，$\theta_u$ 通过模 $36$ 分解。令 $\kappa_B=\prod_{p\mid B}\chi_p^{j_p}$。在所选生成元与经典本原有限 Gauss 规范下，CRT 给实际前向根数
$$
\begin{aligned}
\varepsilon(\psi_u)={}&\gamma(\theta_u^*,f_0)\theta_u^*(nB)
\chi_n(f_0)\kappa_B(f_0)\gamma(\kappa_B,B)\\
&\times\gamma_1(n)\chi_n(B)\kappa_B(n).
\end{aligned}
$$
先运输根数，再取上界。$p\mid b_j$ 的交叉项为正向 $\chi_n(p)^{j+1}$；在 $\overline{\chi_n(d)}$ 中 numerator 指数是 $5-j\bmod6$，局部 $\rho^{-v}$ 再加 $v$。零指数仍留下 puncture。

模 $36$ 的 E-primary 单位类群由
$\chi_n(-\omega),\chi_n(\lambda),\chi_n(4)$
识别为 $C_6\times C_6\times C_3$。写 $n=a+b\omega$，$\sigma=1$ 若 $a\equiv1\bmod3$，否则为 $-1$；以 $-\omega$ 为六次单位根，前两坐标指数为
$$
m\equiv(Nn-1)/6\pmod6,\qquad
t\equiv\sigma b/3\pmod3,\quad t\equiv(1-\sigma)/2\pmod2.
$$
第三坐标对 $(a,b)\bmod2=(1,0),(0,1),(1,1)$ 的指数分别为 $0,4,2$。这些坐标在全部 $108$ 个类上给出完整有限字符基。单位、$f_0$、互反与生成元相位先合并，再作一次有限 Fourier 展开，不为每个变化素数另乘群成本。

原 $\xi$ 与固定 $S$ 删除因子同样保留。$\chi_n(2)$ 是额外固定 numerator 变量，不由模 $36$ 类决定。所读 arXiv v2 第 3.1 节的统一简化不能在这里使用：$n=1+36\omega$ 平方自由且 $n\equiv1\bmod36$，$Nn=1261=13\cdot97$，两处六次剩余指数分别为 $1,2$，所以 $\chi_n(2)=-1$。这里只限制该版本这一步的复用范围，不判断未读取的出版版本或整个 moment 定理。Lemma 4.1 的任意 $d$ 范围容纳 $2,3$ 上的实际 numerator。删除分母在固定 $a$ 条带上无零，合并的有限密度对全部高度一致有界。

### 无限局部展开、全部标记与共同剩余长度

未分歧素数上令 $t=Q^{-1},A=Q^x,V=Q^{-6z},h=\chi_p(u),D=h^{-1}/A,W=hAt$。精确公式为
$$
F_p=C_p+(1-t)t\frac{D-VW}{1-D},\qquad C_p=(1-t)(1+t-V).
$$
重数 $1$ 的未标记因子也是 $C_p$。直接展开安全分母 $1-D$，非恒定部分为
$$
(1-t)t\left[\sum_{k\ge1}D^k-VW\sum_{k\ge0}D^k\right].
$$
每一项保留 $p\nmid u$。以 $N(d)^\tau N(f)^\varepsilon$ 加权，$\tau=1/6,1/14$，primewise coefficient mass 至多为
$$
O(Q^{-1-a+\tau+O(\varepsilon)})
+O(Q^{-2-6c+a+5\tau+O(\varepsilon)})
+O(Q^{-2-6c+O(\varepsilon)}).
$$
三个指数均严格小于 $-1$，$|C_p|\le1+2Q^{-2}$。无限系数质量与共同掩码成本绝对可和，对高度和遗漏素数一致；不需要 $H_p$ 或 $F_p$ 的倒数。

未分歧标记的精确因子是
$$
G_p=\frac{-(1-t)(1-V)h^{-1}-At^2-A(1-t)V
+hA^2Vt(1-t+t^2)}{1-h^{-1}/A}.
$$
加权展开质量为 $O(Q^\tau)$，实际槽价格为 $P_i^{c+\tau+\varepsilon}$。若标记整除 $n$，正确公式为
$$
H_1=1+t-V,\qquad G_1=-A[t^2+(1-t)V].
$$
同时保留两支。把这些标记的积记为 $P_n$，写 $n=P_n n'$，Gauss CRT 给剩余 $n'$ 的 numerator 指数 $4$。文献估计使用同一实际长度
$$
M=\frac{U}{N(P_n)\prod_{j=2}^5N(b_j)^j}
$$
及包含 $B$ 与全部固定标记的同一 puncture。$(m,\tau)=(2/3,1/6),(6/7,1/14)$ 时，这两支计数指数分别为
$a+c-2-m+4\tau$ 与 $a+c-6c-m+4\tau$，均不超过 $c+\tau$。

$j\ge2$ 时保留
$$
H_j=t+(1-V)J_j,\qquad G_j=A[-(1-t+t^2)+(1-t)(1-V)J_j],
$$
其中
$$
\begin{aligned}
J_2&=a_p\rho^{-3}Q^{3/2-3x},&
J_3&=-b_p\rho^{-2}Q^{1-2x}+b_p^2\rho^{-4}Q^{2-4x},\\
J_4&=-a_p\rho^{-3}Q^{3/2-3x},&J_5&=0.
\end{aligned}
$$
先支付共同剩余长度，未标记 higher-valuation prime 的完整指数如下。恒定支对应 $t$；$J_3$ 两支分别列出。

| 重数与局部支 | $m=2/3,\tau=1/6$ | $m=6/7,\tau=1/14$ |
|---|---|---|
| $2$ 恒定 | $-a-4/3$ | $-a-2$ |
| $2,\rho^{-3}$ | $2/3-4a$ | $2/7-4a$ |
| $3$ 恒定 | $-2a-5/3$ | $-2a-17/7$ |
| $3,\rho^{-2}$ | $2/3-4a$ | $-2/7-4a$ |
| $3,\rho^{-4}$ | $1-6a$ | $3/7-6a$ |
| $4$ 恒定 | $-3a-2$ | $-3a-20/7$ |
| $4,\rho^{-3}$ | $1-6a$ | $-1/7-6a$ |
| $5$ 恒定 | $-4a-7/3$ | $-4a-23/7$ |

所有指数严格小于 $-1$。标记该 prime 后，恒定支增加 $a+c$，$J$ 支增加 $a+c-1$，prime 计数再加 $1$；相对于 $c+\tau$ 的超额分别为 $e_j+a+1-\tau$ 与 $e_j+a-\tau$，全部非正。所有重数、所有标记碰撞由同一 $P_i^{c+\tau+\varepsilon}$ 支付。空支持贡献零；单位长度和有界非主单位扇区使用同一固定常数。

无限未分歧质量、全部 higher-valuation 正 majorant 和实际 $n'$ Gauss 和因此给出两项行界。对同一完整表达式用 $m=1,\tau=0$ 计数，三角 allowance 为
$$
U^{a+1/2-c+\varepsilon}\prod_iP_i^{c+\varepsilon}.
$$
$U=Z^d$ 时两项 leading 节省分别为 $(2d-\ell)/6$ 与 $(2d-\ell)/14$。只有 $2d>\ell$ 且指定损失小于相应正裕度时得到严格节省；这比较的是上界，不是实际留数的下界或非零性。

### 完整高度与轮廓边界

原 mixed-residue 权重保留为
$$
\operatorname*{Res}_{v=1}\zeta_F^S(v)\,
X^{1/2-z}Z^{x+z-1}Y^{-x}
\Phi(x+z-1)M(z)\widehat W_1(1-x)\zeta_F^S(6z).
$$
gamma 商和 norm-twist seminorm 增加固定高度幂；原 $M,\widehat W_1$ 的任意有限阶衰减与 Gaussian 支付两个完整高度轴。先选有限阶，再选尺度，annulus 积分界为
$$
X^{1/2-c}Z^{a+c-1}Y^{-a}Z^\varepsilon
\left[U^{a+1/6-c+\varepsilon}\prod_iP_i^{c+1/6}
+U^{a+5/14-c+\varepsilon}\prod_iP_i^{c+1/14}\right].
$$
此界本身不许可原三变量轮廓的新移动。在 $a=51/100,c=17/50$ 上两项 $U$ 指数为 $101/300,369/700$，不能直接作为绝对无限尾部相加；使用完整 $h$ 级数的亚纯轮廓时仍须保留可能的 $z=x+1/6$ 极点贡献。完整严格 Robin 差额与 RH 未由本节解决。


### 先运输有限 annulus，再支付全部尺度

上述完整行界还可与原 Mellin 权重联合，支付整个非主混合留数的无限范数尾部。固定一份物理 dyadic partition，尺度 $U=2^k$，包含低端单位块，所有 profile 的有限 seminorm 一致，且不依赖零点或行值。令
$$
\begin{aligned}
J_U(a,c)=\frac{\operatorname*{Res}_{v=1}\zeta_F^S(v)}{(2\pi i)^2}
\int_{(a)}\int_{(c)}
&X^{1/2-z}Z^{x+z-1}Y^{-x}\\
&\times\Phi(x+z-1)M(z)\widehat W_1(1-x)\zeta_F^S(6z)R_U(x,z)\,dz\,dx .
\end{aligned}
$$
这是先在两个完整高度轴上积分的 annular contribution。下文证明这些积分贡献绝对可和，不声称在 $c_0=17/50$ 上逐个物理行绝对可和。

复用源文原 Fourier Mellin 结论：$M(z)$ 在整个 $\Re z>0$ 全纯，在任意紧实正实部条带上有任意阶竖向多项式衰减；$\widehat W_1$ 在固定实部条带上同样成立。源文 $0<\sigma<1$ 的限制属于其 positivity 推导，不限制 $M$ 的全纯域。

选统一右线 $c_R=2$。对每个有限 annulus，物理行数有限，$K_u$ 无 $z$ 依赖；$F/G$ 在 $c_0\le\Re z\le2$ 正常收敛，固定 $a$ 范围内安全分母 $1-h^{-1}Q^{-x}$ 无零。$\zeta_F^S(6z)$ 的极点 $z=1/6$ 不在此条带，$M$ 也没有被跨过的极点。因此每个 $J_U$ 可单独作 $z$ 运输。

完整高度控制使用
$$
|\Phi(x+z-1)|=\exp((a+c-1)^2-(\Im x+\Im z)^2)
$$
和 $M,\widehat W_1$ 的两个独立衰减；不能只用 Gaussian，因为 $\Im x+\Im z=0$ 时它不衰减。先选有限阶支付 Gauss 行界与 gamma 商的高度幂，两个高度轴和水平 joins 全部可积，得到
$$
J_U(a,c_0)=J_U(a,2).
$$
这是无限 annulus 求和之前的逐块等式，不是移动尚未证明可交换的完整行级数。

记
$$
P=\prod_iP_i,\qquad Q_0=\frac{ZP}{X},\qquad
(\alpha_1,\tau_1)=(a+1/6,1/6),\quad
(\alpha_2,\tau_2)=(a+5/14,1/14).
$$
完整 profile 积分给出
$$
|J_U(a,c)|\ll X^{1/2}Z^{a-1}Y^{-a}(UZ)^\delta
\sum_{j=1}^2P^{\tau_j}Q_0^cU^{\alpha_j-c}.
$$
固定 $X,Y,P,Q_0$ 的多项式尺度范围；$\delta$ 是在最终指定 $\varepsilon$ 之后、$Z$ 之前选定的文献及 profile 损失。若 $Q_0\ge1$，$U\le Q_0$ 的同一 $J_U$ 用 $c_0$，$U>Q_0$ 用右线 $2$。两侧幂满足 $\alpha_j-c_0>0$ 与 $\alpha_j-2+\delta<0$。两份实际 dyadic 几何和遂给出
$$
\sum_{k\ge0}|J_{2^k}(a,c_0)|
\ll_\varepsilon X^{1/2}Z^{a-1}Y^{-a}Z^\varepsilon
\left[Q_0^{a+1/6}P^{1/6}
+Q_0^{a+5/14}P^{1/14}\right].
$$
这里的分割只依赖共同物理尺度，不选择零点子族；共同剩余长度、全部素元组和原 root phases 均已由前面的完整行界支付。$Q_0<1$ 时全部 annuli 用右线，同一安全界把右边的 $Q_0$ 换为 $\max(1,Q_0)$。固定尺度范围使 $Q_0^\delta$ 可吸入最终 $Z^\varepsilon$，选损失时仍保留右线的严格负幂裕度。

在右线 $2$ 上，前节同一完整三角 majorant 的行幂为 $U^{a+1/2-2+\delta}$，对固定 $a<1$ 为严格负幂。它也支付逐个物理行的绝对和及完整高度 majorant，故 Fubini 在这条右线上合法，partition 求和恢复未分块的完整右线积分。左线的结论仍是积分后 annular contributions 的绝对可和，不能由此删除完整 $h$ 级数延拓中可能的 $z=x+1/6$ 极点。

### 混合留数的统一 $x$ 运输与原几何预算

在固定紧实 $1/2<\Re x<1$ 条带上，右线 $2$ 的 annular summability 与高度 majorant 一致。留数系数已没有本原 $L$ 分母：$\Gamma(x)$ 无极点，$1/\Gamma(1-x)$ 为整函数，删除 Euler 分母在 $\Re x>0$ 无零；全部 $F/G$ 修正也全纯。原两个独立 Mellin 衰减支付水平 $x$ joins。因此先逐 annulus 运输 $x$，再由一致可和性运输整个积分和，不跨过新极点。该等式保持每个已积分 $J_U$ 的数值及绝对值，不把不同高度的逐点行级数相认。

代入原带槽几何
$$
X=Z^{17/48},\qquad Y=Z^{23/48},\qquad
P=Z^{1/6},\qquad Q_0=Z^{13/16},
$$
上界成为
$$
\sum_U|J_U|
\ll_\varepsilon
Z^{4a/3-95/144+\varepsilon}
+Z^{4a/3-25/48+\varepsilon}.
$$
统一运输到 $a=51/100$ 时，两项精确指数为 $73/3600$ 和 $191/1200$，故完整积分混合留数满足
$$
\boxed{\sum_U|J_U|\ll_\varepsilon Z^{191/1200+\varepsilon}.}
$$
更一般地，先选足够靠近 $1/2$ 的固定 $a>1/2$，再分配其他损失，可得到
$$
\sum_U|J_U|\ll_\varepsilon Z^{7/48+\varepsilon}.
$$
这是对固定右侧线的选择，不是 $a=1/2$ 端点定理。

本节在所引 primitive-root 与 Gauss41 等前提下，支付完整非主混合留数的无限尺度积分预算。主信号仍须分别保留；把这个留数嵌回原三变量 probe 的轮廓移动、分母零点交会、其他 Laurent 项、joins 与剩余轮廓尚未由此支付。原 $19/64$ 低端估计使用的整族 $\beta_*\le7/8$ 前提也没有被移除，不能与相反的高端阶段前提拼接。严格有符号 Robin 预算及 RH 仍未证成。


## 所读 v2 掩码运输等式的来源限制

Gao–Zhao [arXiv v2 的 Lemma 2.7、式 (2.11) 第一式](https://arxiv.org/pdf/2201.01885v2#page=7) 写成
$$
h(r,f,s;\chi)=\sum_{a\mid f}\mu(a)\chi(a)g_6(r,a)N(a)^{-s}
h(a^2r,s;\psi_a\chi).
$$
其 $h$、$g_6$ 和 $\psi_a$ 均取该文定义。下面的精确系数反例满足该式全部条件，限定这一印出公式的复用范围；未读取的出版版本不在断言范围。该反例核对公式本身，不断言这些小素数属于原物理槽；限定窗口中的使用仍须完成自身桥接。

取 $\omega^2+\omega+1=0$，并令
$$
r=1,\quad\alpha=1,\qquad f=p=-2-3\omega,\qquad q=5,\qquad\chi=1\pmod{36}.
$$
$p,q$ 均为 $E$-primary 素元且避开 $6$，$Np=7$、$Nq=25$；$5$ 在 $\mathbb Z[\omega]$ 中惰性。$p$ 的偶数实系数为 $-2$，另一系数 $-3\equiv1\pmod4$；$q$ 的第二系数为零，系数和 $5\equiv1\pmod4$，故规范生成元条件成立。

在模 $p$ 的 $\mathbb F_7$ 中 $\omega=4$；模 $q$ 为
$\mathbb F_5[\omega]/(\omega^2+\omega+1)=\mathbb F_{25}$。直接按六次剩余符号定义计算：
$$
\xi=\left(\frac pq\right)_6=(-2-3\omega)^4\bmod5
=1+\omega=-\omega^2,
\qquad
\left(\frac qp\right)_6=\xi,
\qquad \psi_p(q)=(-1)^{3\cdot12}=1.
$$
所以 $\xi^2=\omega$，$\xi^4=\omega^2$。复用同文式 (2.4)、(2.5) 的 Gauss 变换与 CRT 公式，得到
$$
g_6(pq)=\omega g_6(p)g_6(q),
\qquad
g_6(p^2,q)=\omega^2g_6(q).
$$
两个局部六次字符均为本原非主字符，经典有限 Gauss 范数给出
$|g_6(p)|^2=7$、$|g_6(q)|^2=25$。

印出的公式在这里要求
$$
h(1,p,s;1)=h(1,s;1)-g_6(p)7^{-s}h(p^2,s;\psi_p).
$$
比较**按范数合并后的普通 Dirichlet 系数** $175^{-s}$。被 $(p)$ 去掉且范数为 $175$ 的理想只有 $(p)(5)$：除以 $(p)$ 后，范数 $25$ 的理想唯一为 $(5)$。另一个范数 $7$ 的共轭素理想乘 $(5)$ 在两边相同，抵消于差额中；唯一 $E$-primary 生成元保证单位不产生额外计数。右侧平移级数的范数 $25$ 项也只有 $(5)$。

因此，左侧减去印出右侧的这一系数恰为
$$
(\omega^2-\omega)g_6(p)g_6(q),
\qquad
\left|(\omega^2-\omega)g_6(p)g_6(q)\right|^2=525>0.
$$
各级数在 $\Re s>3/2$ 绝对收敛，普通 Dirichlet 级数系数的唯一性排除了该印出等式在此域恒成立。

对于这一素数掩码，Gauss CRT 相位实际需要指数 $4$。同样直接复用上述算术公式、互反律及 $p^k$（$k>1$）的自然零项，在绝对域得到
$$
h(1,p,s;\chi)=h(1,s;\chi)
-\chi(p)g_6(p)Np^{-s}h(p^4,s;\psi_p\chi).
$$
这里核对的是这一素数掩码的运输；它不认证任意一般化后的亚纯公式，也不解除源文 $(rf\alpha,6)=1$ 的条件。对实际有符号列继续取极点留数时，必须保留修正后的 numerator、完整掩码和字符扭转。

前节完整混合留数估计以 Lemma 4.1 为明确解析前提，其掩码处理使用该引理中的直接约数容斥和部分求和，不调用式 (2.11) 第一式。本反例限定该运输等式的使用，没有证明或否定 Lemma 4.1、整篇 moment 定理或未读取的出版正文。完整有符号 Möbius／零点—根数联合估计、严格 Robin 预算与 RH 仍未由此得到。

## 实际 buffered 分箱轮廓中的混合留数消费

本节把前节完整混合留数供给接回同一平方自由立方索引探针的三变量轮廓。复用所引主稿 `fixed-bin-contour`、`external-contour-tails`、primitive 函数方程和前节完整 annular 估计；新增步骤是在实际有限高度箱内跨过混合极点，并先重合全部分箱留数，再使用完整行的 Gauss 估计。结论以同一探针的精确高端恒等式及原右侧分箱变换为前提，保留其 $\sigma_0\ge7/8,\ \beta_*>\sigma_0$ 阶段范围。未执行 Lean 核验，未独立认证整篇源证明，不主张历史原创性。

### 同一物理行与同一份高度预算

取目标 $\eta=1$，保留原 $\xi$、所有素槽、共同掩码、零延拓和 Mellin 测试。只对原合同保留的完整非主中央行族执行下述移动；主行及其标量留数、原合同单列的有界例外行另行保留。固定共同光滑 profile $W_U(q_u/U)$，支撑于固定倍数的 $U$，并取有限个 dyadic annuli
$$
Z^{d_{\min}}\le U\le Z^{d_{\max}},\qquad
0<d_{\min}\le d_{\max}<\infty.
$$
每个 annulus 的 buffered 分区先固定，再移动 Mellin 变量；使用精确分区或和为 $1$ 的分区权重，覆盖该物理 annulus 的完整保留行族，不随积分点重新选择。

令 $c_0=17/50$、$0<e<1/4000$，取原分箱右线
$$
x_r=a+16e,\qquad w_+=1-a-6e,\qquad z_r=c_0,
\qquad51/100\le a\le1.
$$
原分箱变换提供该 $x$ 线在保留高度上的无零 buffer 和 reciprocal 界。使用同一份原高度
$$
|t_x|\le T_1/4,\quad |t_w|\le T_1/2,\quad
|t_z|\le T_1/4,\qquad
T_1=Z^\tau,\quad0<\tau\le d_{\min}/100.
$$
$e,\tau$、profiles 和参数范围均在 $Z$ 前固定。任意指定的 $Z^{-1}$ 幂节省，须按这个固定 $\tau>0$ 选取足够大的 $N$。不为后续变量重新申请高度 allowance。原 integrand 保留为
$$
\mathcal W(X,Y,Z;x,w,z)
\sum_u W_U(q_u/U)q_u^{-z}\overline{\xi(u)}
\zeta_F^S(6z)
\frac{L^S(w,\chi_u)}{L^S(x,\overline{\chi_u})}
\mathfrak H_u^{\mathrm{sf}}(x,w,z),
$$
其中
$$
\mathcal W=X^{1/2-z}Z^{x+z-1}Y^{w-1}
\Phi(x+z-1)M(z)\widehat W_1(w).
$$
$\chi_u$ 保留实际诱导／本原表示、unit sector 和删除因子约定，不替换为独立的任意特征。

### 跨对角线的完整全纯修正

在每个 $p\notin S$，包括 $p\mid u$，设
$$
T_p=Q^{-x-w},\qquad
F_p^\circ=(1-T_p)H_p^{\mathrm{sf}},\qquad
G_p^\circ=(1-T_p)G_p^{\mathrm{sf}}.
$$
按原完整素元组和构造 $\mathfrak H_u^\circ$：选中槽使用 $Q^{z-1}G_p^\circ$，其余素数使用 $F_p^\circ$。于是
$$
\boxed{\mathfrak H_u^{\mathrm{sf}}
=\zeta_F^S(x+w)\mathfrak H_u^\circ.}
$$
这是绝对域上的恒等式及其亚纯延拓，不含任何 $H_p$ 或 $G_p$ 的倒数。分歧处虽然 $D=W=0$，仍须保留 $1-Q^{-x-w}$，不能把它设成 $1$。

对未分歧素数，$\eta=1$ 给出 $T_p=DW$。复用完整局部式，记
$$
R_p=DV(1-W)-VW-D(Q-1)WV(1-W),
$$
则精确缺陷为
$$
F_p^\circ-1=
\frac{D^2W(1-W)+(1-DW)R_p}{1-D}.
$$
全部缺陷幂由
$$
\begin{gathered}
-2x_r-w_r,\ -2x_r-2w_r,\ -x_r-6c,\\
-x_r-w_r-6c,\ -w_r-6c,\\
1-x_r-w_r-6c,\ 1-x_r-2w_r-6c
\end{gathered}
$$
控制。在 $x_r=a+16e$、$w_r\in[1-a-26e,1-a-6e]$、$c\ge c_0$ 的整个移动管内，七项均严格小于 $-1$，具有统一正裕度；$1-D$ 和 $1-V$ 一致远离零。因此未分歧乘积在该管的开邻域正常收敛，适用于全部高度。

分歧处使用原 $j=1,\ldots,5$ 完整表及全部标记，不取修正因子倒数。在预先固定、包含移动管的紧实部盒上，每行只有有限个分歧素数，故完整修正、行数和素元组质量具有同一个
$$
Z^B(1+|t_x|+|t_w|+|t_z|)^J
$$
majorant，其中 $B,J$ 在选择外部衰减阶 $N$ 前固定。这里需要的是 polynomial majorant，不声称已取得左侧的 subpower 修正界；分歧严格项的幂可逼近 $1/400>0$。$c\ge c_0$ 的局部正常收敛不提供无限实部范围上的统一 $Z^B$ 界，因为槽权重还含 $P_i^c$。

### 有限高度箱内的实际跨越

固定 $x,z$ 的原保留 segments，将 $w$ 移到
$$
w_-=1-a-26e.
$$
每个保留 $x=x_r+it_x$ 的唯一混合极点 $w=1-x$ 严格位于 $w$ rectangle 内，因为
$$
w_-<1-x_r<w_+,\qquad |t_x|\le T_1/4<T_1/2.
$$
水平 $w$ joins 上 $|\Im(x+w)|\ge T_1/4$。分母仍在同一 buffered $x$ segment 上；只延长允许的 $z$ 轴，不延长仅有有限高度无零保证的 $x$ 轴。三个原 Mellin／Gaussian 因子的独立衰减与上述完整 majorant 支付 joins，代价为 $O_N(Z^BT_1^{-N})$。单独 Gaussian 不能承担这个结论。

分子非主、$6c_0>1$，故没有额外分子或 $\zeta_F^S(6z)$ 极点。方向给出“右积分＝左积分＋混合留数＋tails”。在 $w=1-x$ 上应用实际 primitive 函数方程，保留原根数、导子、gamma 商和删除因子，得到前节同一份 $K_u(x)$；本原 $L$ 分母消去。留数 integrand 恰为
$$
\begin{aligned}
&R_S X^{1/2-z}Z^{x+z-1}Y^{-x}
\Phi(x+z-1)M(z)\widehat W_1(1-x)\zeta_F^S(6z)\\
&\qquad\cdot W_U(q_u/U)q_u^{-z}\overline{\xi(u)}
K_u(x)\mathfrak H_u^\circ(x,1-x,z),
\end{aligned}
$$
其中 $R_S=\operatorname{Res}_{v=1}\zeta_F^S(v)$，且对角线上的 $\mathfrak H_u^\circ$ 就是前节的完整 $\widetilde{\mathfrak H}_u$。

### 先完成每行留数，再重合全部分箱

留数已无 $L$ reciprocal。对中央有限行，$K_u$、完整对角修正和删除因子在全部高度上具有固定 polynomial majorant；原两个独立 Mellin 衰减与 Gaussian 因而把有限 $x,z$ segments 完成为完整轴，仍只花 $O_N(Z^BT_1^{-N})$。

随后把每个完整行积分运输到同一个固定 $\alpha\in(1/2,1)$。移动管包含原 $x_r$，即使 $x_r$ 略大于 $1$ 也无新增极点：$\Gamma(x)$ 在正实部无极点，$1/\Gamma(1-x)$ 是整函数，删除因子安全，对角修正在该紧条带正常收敛；原衰减支付水平 joins。运输的是完整行积分，不是零点处的值或截短轮廓。

全部行运输后再重合原固定 exhaustive 分箱，恢复完整物理 annulus 的 $J_U(\alpha,c_0)$。没有对零点自适应子集调用 Gauss 估计。若 $I_U^{\mathrm{abs}}$ 是原绝对起线上的完整非主 annular contribution，而 $L_U^{\mathrm{buf}}$ 是各实际左线 retained integrals 的和，则
$$
\boxed{I_U^{\mathrm{abs}}
=L_U^{\mathrm{buf}}+J_U(\alpha,c_0)
+O_N(Z^BT_1^{-N}).}
$$
对上述有限中央 annular 集合 $\mathcal K$ 求和，并直接复用前节已支付的 $z$ 运输、完整 Gauss 行界和全部尺度预算，得到
$$
\sum_{U\in\mathcal K}I_U^{\mathrm{abs}}
=\sum_{U\in\mathcal K}L_U^{\mathrm{buf}}
+E_{\mathrm{mix}}+O_N(Z^BT_1^{-N}),
\qquad
|E_{\mathrm{mix}}|\le\sum_{U\in\mathcal K}|J_U|
\ll_\varepsilon Z^{7/48+\varepsilon}.
$$
这里使用原几何 $X=Z^{17/48},Y=Z^{23/48},P=Z^{1/6}$；实际移动 normalizer $c_SA_T(Z)$ 仍保留，其倒数的 subpower 损失计入 $\varepsilon$。原主信号指数 $C(\beta_*)=\beta_*-11/16$ 与混合项的 leading 差为 $\beta_*-5/6$，在 $7/8$ 处为 $1/24$。当前阶段内须把 prescribed losses 放入该正裕度；这个数值比较不扩大原 stage 的范围。

左侧 $L_U^{\mathrm{buf}}$ 仍包含完整原 $L$ 商，尚无所需联合估计，不能用只控制根数的 Gauss 供给替代。主信号、其他 Laurent／轮廓交会项、小／大行范围、完整无限高端比较及原有符号 Robin 余量仍需分别支付；后续完整 $h$ 级数可能的极点贡献也没有由此删除。实际零点实部、双符号、全部高度与重数、完整系数、正 $r_A$ 和严格核心仍是原目标。严格 Robin 与 RH 尚未证明。

## 完整左侧商与原联合见证计数的高端消费

本节研究同一平方自由立方索引探针的完整高端比较，复用原稿的 `detector-counts`、动态容量比较、端点证书、外围行和主留数接口，以及前节实际混合跨越。所引计数与 moment 定理不在这里重证。结论依赖这些来源输入、实际探针的精确高端恒等式和下面的原阶段条件；未执行 Lean 核验，未独立认证整篇源证明，不主张历史原创性。

### 实际素槽系统与相容阶段

固定目标 $\eta=1$，保留原 $\xi$、unit sectors、共同掩码、零延拓和全部六次方自由物理行 $u$。平方自由条件施加于完成索引 $A=cn^3$ 中的 $n$，不把高端 $u$ 改成平方自由行。

使用原稿 Part II 的实际细槽系统：固定偶数 $K$、$\ell_i=1/(6K)$、$P_i=Z^{\ell_i}$ 和原互不相交的非负光滑素数窗口。$K$ 满足原 plain moment mesh、整槽 rounding 与 inverse supply 的严格条件，并在目标和 $Z$ 前固定。虽然 $\prod_iP_i=Z^{1/6}$，一个长度为 $1/6$ 的长槽不能替代这份细槽系统。现有平方自由构造和完整混合估计允许这份固定有限原槽系统。

具体保留原网格条件
$$
\frac{2\ell}{K}<\min\{\eta_{\mathrm{mesh}},b_{\mathrm{round}},1/185\},
$$
其中 moment／容量损失先确定，再选 $K$；幅度 bin 宽和 $e$ 随后选定。另要求 $0<e<\min\{1/4000,e_0\}$，其中 $e_0$ 是原 detector 的 admissible 上限，并同时满足 principal 和误差裕度约束。

保留原 Part I 供给和 Part II 反证阶段：
$$
\beta_*=\frac78+\Delta,\qquad0<\Delta\le\frac1{24},\qquad
\kappa=2\beta_*-1=\frac34+2\Delta\le\frac56.
$$
每个实际 bin 满足 $\delta=2a-1\le\kappa$。原正槽 moment 的条件 $\beta_*\le(1+\kappa)/2$ 在这个动态参数处恰好满足；没有在此阶段插入不相容的 $\beta_*\le7/8$ 前提。

原几何为
$$
l_x=17/48,\quad l_y=23/48,\quad\ell=1/6,\quad h=13/16,
\qquad C(s)=s-11/16.
$$
令 $J_{\mathrm{sf}}=I_{\mathrm{modified}}^{\mathrm{sf}}/(c_SA_T(Z))$，令 $f_{\mathrm{sf}}$ 是原主双留数在 $\Re x=2$ 上的积分，使用现有的 $H_{\mathrm{main}}^{\mathrm{sf}}$。物理量、主积分和同一 moving normalizer 都不依赖分析高度。

### 左侧完整修正的实际代价

在前节已支付的左线上
$$
x_r=a+16e,\qquad w_r=1-a-26e,\qquad c_0=17/50,
\qquad x_r+w_r=1-10e,
$$
保留完整修正 $\zeta_F^S(x+w)\mathfrak H_u^\circ$，包括每个分歧素数上的 $1-Q^{-x-w}$。前节七项未分歧缺陷幂的正常收敛给出任意未选中子乘积的共同界。

分歧 $H_p^{\mathrm{sf}}$ 的严格项幂为 $10e$，其余完整 $J_j$ 幂为
$$
\begin{gathered}
-1+10e,\quad3/2-3a-48e,\\
1-2a-22e,\quad2-4a-64e,\quad3/2-3a-38e.
\end{gathered}
$$
后三种重数的这些幂均为负，且 $|1-Q^{-x-w}|\le2$。因此包括分歧素数的任意未选中子乘积都满足
$$
\prod|F_p^\circ|\ll_\varepsilon U^{10e+\varepsilon}.
$$
这里使用 $\operatorname{rad}(u)\le q_u$ 和约数幂界；不声称固定 $e$ 下的任意 subpower 界，也没有取修正因子倒数。

在原 quotient-free 主／误差分解中取
$$
\mathcal R_p^\circ=(1-Q^{-x-w})\mathcal R_p^{\mathrm{sf}},
\qquad
G_p^\circ=-\overline{\chi_p(u)}F_p^\circ+\mathcal R_p^\circ.
$$
完整局部式在新左线给出：未分歧误差 $O(Q^{-a+O(e)})$、$j=1$ 误差 $O(Q^{a-1+O(e)})$、$j\ge2$ 误差 $O(Q^{a+O(e)})$。同时实际分子反射到 $a+26e$，仍在同一个无零 buffer 内；conductor、gamma 与删除因子成本为 $U^{\delta/2+O(e)+\varepsilon}(1+T_1)^A$。

对全部互异选中分歧素数共同分配实际 conductor 缺口
$$
\prod_iQ_i^{-(j_i-1)\delta/2}.
$$
分子价格只支付一次。误差槽相对于 $P_i^{c_0-1/2}$ 的 leading 幂为 $a-3/2$（$j=1$）或 $-(j-2)\delta/2$（$j\ge2$），均非正；$j=2$ 没有 leading 节省。分歧元组逐行由约数界支付，未分歧误差也不超过原槽 baseline。

于是对每个完整误差子集 $I$，用原 main amplitudes $g_i$，并在误差槽赋 $g_i=0$，有
$$
\begin{aligned}
|L^S(w,\chi_u)\mathfrak H_u^{\circ,(I)}|
\ll{}&U^{\delta/2+O(e)+\varepsilon}(1+T_1)^A\\
&\cdot Z^{\ell(c_0-1/2)+q\ell+O(e+\vartheta+\varepsilon)},
\qquad q=\frac{\sum_i\ell_i g_i}{\ell}\in[0,\delta/2].
\end{aligned}
$$
未选中乘积的 $10e$ 已计入这里。左侧 mixed scalar 与极点有固定实部距离 $10e$，其固定高度幂并入 $A$；原分母 reciprocal 仍在同一个 buffered $x$ segment 上。此界控制实际完整商，没有对变化的 $L$ 值相位调用 root-only Gauss 估计。

### 消费同一批行上的联合计数

原稿的物理 $Q_i$、固定 ray 系数、whole-product conjugation、自然零和 witness profiles 与这里相同，且不依赖平方自由局部修正。对固定完整 bin 移动之后才使用 pointwise amplitude／witness 子集，不给它们单独移动轮廓。仅选择真正的正 main slots；若正槽不足，原 greedy 规则保留全部正槽，仍给出 $q\ell/d\ge qz$。误差槽的零标签不提供虚假的正幅度下界。

保留动态容量 $2m+6\kappa z\le1$、inverse 容量和实际细槽 mesh，直接应用原联合 witness 计数。完整商的 leading 指数恰为原稿同一几何中的
$$
E(d)=-\frac1{48}+\frac23\delta+\frac q6-h(1-R)
+(d-h)(R+\delta/2-c_0).
$$
左线位移只增加显式 $O(e)$ 成本。原动态计数与端点证书直接给出
$$
E_{\mathrm{actual}}(h)-\Delta
\le-\frac{49}{440640}-\frac{51}{64}\Delta
+\text{可调损失}.
$$
floor、$d\le1/2$ 和 $\delta=5/6$ 端点分别使用原 $7/1200$、$49/14400$ 和 $1/48+\delta/16$ 节省。将中央范围延长到 $h+\zeta$ 的成本至多 $2\zeta$；保留 $0<\zeta<1/48$ 及原 supply 裕度。这里复用原证书，不把它们重算为新成果。

原左积分盒缩到这一联合计数的共同高度盒。一次列出全部原／辅助坐标及其固定线性参数矩阵，取 $c=1/(8m(1+A_{max}))$：原 $x,z$ 高度为 $cT_1$，$w$ 高度为 $2cT_1$，其余辅助高度为 $cT_1$。它满足原累计 allocation，且保留 $c_w>c_x$。被删除的原盒 shell 由完整紧实部盒 polynomial majorant 和原三个独立 Mellin／Gaussian 衰减支付；$x$ 始终留在原 buffer 中，没有延长它的轴。辅助 tails 已在原联合供给中计入，不另申请高度。

先按中央裕度选择原 moment／容量损失，再按其 mesh 选择实际细槽 $K$；$K$ 固定后才选 $e,\vartheta,\zeta$ 和局部解析损失。主项的 $\mu$ 此时已经确定，后续主项损失须小于它；仅用于中央估计的既定 moment 损失无须重新选成小于 $\mu$，因此不产生 mesh 与主项价格的循环。所有实部和槽系统在目标及 $Z$ 前确定；目标的有限高度阶确定后取足够小的 $\tau>0$，最后选外部衰减阶 $N$。完整中央左积分因而保留统一正节省，例如在相应损失预留后取 $(49/440640)/4$。

还须显式满足原 detector 高度门：令 $\varepsilon_{\mathrm{ht}}>0$ 为既定有限 detector allowances 的最小值，$A_{\mathrm{ht},\eta}$ 为目标内部 profile 阶确定后的共同 detector 高度阶，要求
$$
0<\tau\le\min\left\{\frac{d_{\min}}{100},
\frac{d_{\min}\varepsilon_{\mathrm{ht}}}{20(1+A_{\mathrm{ht},\eta})}\right\}.
$$
于是所有中央 $U\ge Z^{d_{\min}}$ 上有 $(1+T_1)^{A_{\mathrm{ht},\eta}}\le U^{\varepsilon_{\mathrm{ht}}/10}$。同时保留中央指数的高度裕度；此门在 $N,Z$ 前确定，增加外部衰减阶不能补救不合法的 retained detector。

### 全部外围行与主项

取 $d_{\min}=1/100$。在小行全局线上 $(x_r,w_r,z_r)=(\beta_*+e,1/2,c_0)$，完整平方自由 $H_p$ 的未分歧缺陷可求和、分歧幂为负；完整 raw $G_p$ 对未分歧素数为 $O(1)$，对分歧素数为 $O(Q^{1/2})$。后者在每行只有约数多种选法，故完整元组满足
$$
|\mathfrak H_u^{\mathrm{sf}}|\ll_\varepsilon U^\varepsilon
Z^{\ell c_0+\varepsilon}.
$$
在 $(2,2,v)$、固定 $v>2$ 上，同一完整 raw 式给出 $U^\varepsilon Z^{\ell v+\varepsilon}$。这些是一般行的全部高度界，没有借用 principal-only 的界。

原 `outer-row-tails` 因而对同一份字符、unit／例外行分类和完整系数合法。小行的相对指数为 $-79/800+(63/50)d_{\min}$，低于 $-63/800$；大行绝对指数为
$$
B_0+(h+\zeta)(1+\varepsilon)-\zeta v+\varepsilon,
\qquad B_0=l_x/2+1+l_y,
$$
在固定足够大 $v$ 下任意负。初始级数与最终 tail 的绝对收敛允许求和全部大行 dyads。

主行使用现有 $H_{\mathrm{main}}^{\mathrm{sf}}$、完整 principal rectangle 界 $Z^{\ell\Re z}$、同一非零 $A_T$ 和实际槽比值 $-1+O(Q^{-7/8})$。复用已有 $H_{\mathrm{main}}^{\mathrm{sf}}=1+O_{\sigma_0}(P_0^{-\min(1,\sigma_0)})$ 界，在构造物理探针前选择足够大固定 $P_0$，使 $\Re s>7/8$ 上的 closeness 满足原合同；这不提供一个已核验的显式数值 cutoff，也不继承未过滤主修正的 cutoff。相应排除集 $S$、$b_*,\xi,\tau,\Xi,c_S,A_T$、物理探针和全部计数数据同时校准，所有接口使用同一份最终固定数据。直接应用原主留数接口，保留 Jacobian、global-line error 与右移主积分；三份节省为 $23/960$、$13/9600$ 及任意 $0<\mu<(7/8)\min_i\ell_i$。

最后接上前节先完成／运输／重合全部 bins 后的混合预算。它的指数 $7/48$ 与主信号相差 $\beta_*-5/6\ge1/24$。中央完整商、混合项、两端全部行和 principal remainders 都使用同一个 $c_SA_T(Z)$；把所有有限损失放入上述正裕度后，得到
$$
\boxed{|J_{\mathrm{sf}}(Z)-f_{\mathrm{sf}}(Z)|
\ll Z^{C(\beta_*)-\sigma},\qquad\sigma>0.}
$$
这里按已支付的物理 annular identities 和外围 tail 求和，没有删除后续 $h$ 级数的任何极点。

最终 $\sigma$ 取各实际剩余裕度的共同正下界，须包含 principal 槽余量 $\mu$、另两份 principal 裕度、normalizer、累计高度和 dyadic multiplicity 成本；中央例子 $(49/440640)/4$ 不是自动适用的全局节省。

这只支付上述相容阶段、实际细槽系统和所引供给下的新平方自由探针高端比较。没有把阶段扩展到 $7/8$ 下方，也没有补齐更低比较层所需的同一探针低端节省；现有 $19/64$ 低端界的 $\beta_*\le7/8$ 前提不在本阶段使用。原完整有符号 Robin 响应、实际零点数据、正 $r_A$ 和严格核心仍未证明，RH 未证明。

## 同一探针的带掩码 plain 反射低端

本节复用主稿的 natural plain reflection、positive-slot plain moment、一般 sixth-power amplification，以及前节已经支付的完整平方自由立方索引相位运输、标记重叠与 Gaussian 分离。本节建立对实际 plain 列先删除其原掩码、反射后再恢复共同掩码的完整低端消费；不重证这些文献输入。只使用主稿 Part I 的全族 $\beta_*\le11/12$，不使用 $\beta_*\le7/8$。整篇源证明及 Lean 未独立认证，不主张历史原创性。

对每个指定 $\varepsilon>0$，在原构造中预先选择满足所引 plain mesh 及下述舍入损失的足够细固定偶数槽数 $K$，同一完整探针满足
$$
\boxed{
|I_{\eta,\mathrm{modified}}^{\mathrm{sf}}(Z)|
\ll_{\eta,\varepsilon,\mathrm{data},K} Z^{37/128+\varepsilon}.
}
$$
固定槽系在所需损失和固定算术数据给定后、$Z$ 之前选定；不声称一个已经固定的粗槽系实现任意小损失。总长仍为 $\ell=1/6$，几何仍为 $l_x=17/48,l_y=23/48,h=13/16$，所有原字符、零延拓、物理归一化及高端主信号保持。

### 完整来源上的实际长度

沿用重缩放槽总长 $q$、自动槽总长 $z_A$，非自动槽可用总长为 $z_K=\ell-q-z_A$。取活动短子集 $\mathcal L$，长为 $z$；冻结其余实际素数积 $P_R$。原相位运输给出逆列 $M_{\eta\overline\chi}$、plain 列 $S_\chi$ 与负方向素乘积 $Q_{\mathcal L}$。原补偿的 $\overline{\eta(p)}$ 已抵消逆列抽出的 $\eta(p)$，故素系数仍为 $1$，不另插入 Möbius 系数。这里先保留 $Q_{\mathcal L}$ 的原方向。

写 $H=\zeta u_0a^6$，固定 unit 扇区及 $a$，令
$$
t=\log_Zq_a,\qquad m=\frac{13}{16}-6t,
\qquad0\le t\le\frac{13}{96}.
$$
$a$ 的计数成本为 $Z^{t+\varepsilon}$。沿用实际标签 $u,v,e,d_b,w$，其同一实现约束及剩余长度为
$$
d_b\le u,\qquad z_A\le u+e,
$$
$$
r=1+z_A-3u-v-e-w,\qquad
n=\frac{23}{48}-q-d_b-e-w.
$$
固定 annular 偏移及 Gaussian collar 计入预留损失。非空单位窗口以下的尺度只在固定范围内裁切；无界负长度不进入矩定理。原 $d$ 标量仍为 $\mu(d)^2\eta(d)\mathbf1_{\gcd(d,H)=1}$；一般 $\eta$ 下它不恒等于 $1$，先保留其相位，再使用模长界。$q_{P_R}^{-1},q_d^{-1}$ 支付整条标签质量，原重缩放元组提供 $-q/2$；活动素乘积的额外外幂是 $-z/2$。

### 先删除原掩码，再反射和恢复

在 plain 列尚未为共同矩增加 $d$ 掩码时，其实际额外掩码是
$$
R_S=\operatorname{rad}(aP_R).
$$
复用主稿的有限删除等式，保留所有 natural 零：
$$
S_{\chi,R_S}(D;W)
=\sum_{\lambda\mid R_S}
\mu(\lambda)\chi(\lambda)q_\lambda^{-1/2}
T_\chi(D/q_\lambda;W).
$$
固定 $a,P_R,d,\lambda$ 后再调用矩。该标量的行相关字符值模不超过 $1$，总系数质量由所引 deleted-factor bound 支付为小幂；不把增长掩码吸收到固定 ray 数据。

非 unit 的 $u_0$ 在某个 good prime 上分歧，其诱导字符不属于固定 $\Theta$。所引 natural reflection 保留根数、实际本原导子及全部 redundant natural divisor/geometric 项。其导子尺度满足
$$
C_{u_0}q_{R_{0,u_0}}\ll Z^m,
$$
每个保留的反射 annulus 因而具有
$$
n_{\mathrm{ref}}\le m-n+\log_Zq_\lambda+\xi.
$$
$\xi>0$ 是预先保留的小损失。中心归一化在反射两边一致，没有新增 $D$ 或导子的实平方根。根数只作为有界行标量保留；row-dependent 导子与自然冗余项的尺度由所引 scale supremum 和参数 Sobolev 支付。$W^\sharp$ 在零处有界、在无穷处快速衰减；低 annulus 的中心归一化系数可求和，高 annulus 及尾部由有限阶衰减支付。

反射后的 plain 方向是 $\overline\chi$，与原 $Q_{\mathcal L}$ 一致，连同 unit twist 一起运输。此时才恢复更大的共同掩码 $R_Q=\operatorname{rad}(aP_Rd)$：
$$
T_{\overline\chi}(Y;W^\sharp)
=\sum_{\operatorname{rad}(h_0)\mid R_Q}
\overline\chi(h_0)q_{h_0}^{-1/2}
S_{\overline\chi,R_Q}(Y/q_{h_0};W^\sharp).
$$
整条几何系数质量是小幂，恢复只降低反射后的长度。不能先恢复 $d$ 再反射，却不计那一步增加的反射长度。逆列保留自己的实际 puncture，分别调用其矩；不要求两份矩的固定 twist 相同。

使用充分的保守界
$$
\log_Zq_{R_S}\le t+\ell-q-z_A-z+w+O_{\rm fixed}(1/\log Z).
$$
取 $\kappa=5/6$；所引 positive-slot 假设 $\beta_*\le(1+\kappa)/2$ 由 Part I 供给。其第二个 plain 因子只选单位理想。对原固定字符列表、共同掩码及槽系，容量 $n_{\mathrm{ref}}+5z\le m$ 因而由
$$
\boxed{4z\le\frac5{16}-t+z_A-d_b-e-2w}
$$
保证，另以微小 decrement 支付反射、box、collar 与舍入损失。

### 所有活动素槽重叠

仍对 $(P_{\mathcal L},n_1s_1)=1$ 作完整有限展开。冻结 $B_n\cup B_s$，长度记为 $z_O$，两列抽取长度为 $z_n,z_s$。原净幂为 $-z_\cap/2\le0$，其中 $z_\cap=z_n+z_s-z_O$；全局 $-z/2$ 不变。剩余长度为 $r-z_n,n-z_s,z-z_O$。

以 $z_O$ 保守包住 plain 自身删除掩码长度的重叠成本，其反射容量左侧也只增加
$$
z_s+z_O-5z_O=z_s-4z_O\le0.
$$
这是删除掩码长度的上界，不授权在反射前给原 plain 列插入新零。故同一容量足够。共同掩码的其他冻结素数在反射后用完整几何恢复，继续降低长度。逆列只保留其实际必要的零掩码，不因 plain 的共同掩码而删除额外逆项。所有双列重叠、plain 素幂、自动槽与原字符零都保留。

### 同一行上的长度分配

共同 profile 分离及尺度控制先于正矩，行约数重数不代替这一步。固定实际标签 dyads 和自动槽模式后选择一个固定槽子集，其素系数与行无关；不同模式通过有限子集和覆盖，不逐行另选系数或轮廓。复用
$$
E(m,r)=\max\{m,(m+5r)/6\}
$$
与反射后的 plain 矩，在同一 $u_0$ 行上 Cauchy。计入全部外幂、$a$ 计数与重缩放元组，非 unit allowance 是下列两式的最大值：
$$
B_1=\frac14-\frac{q+z_A+z}{2}-5t,
$$
$$
B_2=\frac{21}{64}-\mathcal P-\frac z2,
\qquad
\mathcal P=\frac q2+\frac{z_A}{12}
+\frac{5u}{4}+\frac{5(v+e+w)}{12}+\frac{5t}{2}.
$$
$B_1\le1/4<37/128$。对第二式选择
$$
z_*=\max\{0,5/64-2\mathcal P\}.
$$
若 $z_*=0$，不保留槽的旧矩界已经足够；否则取整槽 $z\in[z_*-\eta,z_*]$，再以预留微小 decrement 留出容量 slack。舍入只增加已指定损失。

供给与容量由同一实际标签同时保证。正目标时有
$$
z_K-z_*=
\frac{17}{192}-\frac{5z_A}{6}
+\frac{5u}{2}+\frac{5(v+e+w)}6+5t
\ge\frac{17}{192},
$$
以及
$$
\begin{aligned}
&\frac5{16}-t+z_A-d_b-e-2w-4z_*\\
&=4q+\frac{5z_A}3+10u+\frac{10v}3
+\frac{7e}3+\frac{4w}3+19t-d_b\ge0.
\end{aligned}
$$
分别使用 $z_A\le u+e$ 和 $d_b\le u$。不是把分别可达的极值拼接。因此 $B_2\le37/128$，加上全部指定损失。

### 有限 unit 行与完整尾部

所有有限 unit 诱导字符，包括属于 $\Theta$ 的非主字符，使用 Part I 的 $11/12$ 半平面及 reciprocal/logarithmic-control 界，在 $\sigma=11/12+\varepsilon_0<1$ 处理。复用前节已完整运输的单位行公式：
$$
\begin{aligned}
&\frac{17/48-q}{2}+\sigma-1+t+(\sigma-1)(z_A+\theta_N)\\
&\quad-3(\sigma-1/2)u-(\sigma-1/2)v
-d_b/2-\sigma e-\sigma w.
\end{aligned}
$$
后续非 collar 项非正，$t\le13/96$，故其 allowance 至多为 $11/48-q/2$ 加预留损失，低于 $37/128$ 的余量为 $23/384$。保留全部 $a^6$、固定 unit twist 和零值，不假设单位行响应为零。

原完整 Gaussian/Fourier 分离仍支付实际外频率、未保留 annuli 与全部标签。新增反射的 annular、有限删除、整条几何恢复与尺度 supremum 均使用前述统一有限 seminorm 和高度阶数；小的齐次 profile 系数保留一次。先定矩、反射及舍入损失，选足够细固定槽系，固定全部内部阶数，再选小的共同高度/collar 参数，最后选外部尾阶数及 $Z$ 阈值。后续外部尾阶数只提高外部输入 seminorm，不扩大已经分配的内部高度阶数。所有负长度尾部用衰减支付，不送入有界长度矩。有限子集、全部重叠、对数个 norm dyads 与整条 $a^6$ 和给出本节完整界。

相较 $19/64$，allowance 改善 $1/128$；没有改变主信号 $C(s)=s-11/16$。名义门槛是 $125/128$，仍高于所用 $11/12$ 半平面；在该阶段最大主信号 $11/48$ 与新上界仍差 $23/384$。这是估计强度不足，不是真实响应的下界。没有产生新无零区域、低于 $7/8$ 的高端合同、完整有符号 Robin 上界或 RH 证明；实际零点数据、正 $r_A$ 与严格核心仍为原目标。

## 原完成探针的改尺度消费与条件半平面

本节使用原始未过滤的 $cn^3$ 完成探针，复用所引主稿的 reflected energy、additive Gram、buffered detector、plain／inverse moments、局部恒等式及 continuation criterion。以下是这些输入成立时的完整消费推导；没有独立核验整篇主稿或源 Lean 项目。前节平方自由探针的低端、高端和混合留数不用于此处。

固定
$$
p=\frac1{100000},\qquad b=\frac18,\qquad
\ell=\frac16+p=\frac{50003}{300000},\qquad M=1-\ell,
$$
$$
l_x=\frac{M-b}{2}=\frac{212497}{600000},\qquad
l_y=\frac{M+b}{2}=\frac{287497}{600000},\qquad
h=1+\ell-l_x=\frac{162503}{200000}.
$$
仍取原有限 mark／rescale 定义：标记 $p_i\mid cn^3$，系数为 $\overline{\eta(p_i)}$；rescale 系数为 $-q_{p_i}^{-3/2}$。所有槽窗口在操作中保持原 $P_i=Z^{\ell_i}$，没有过滤原完成指数。取足够细的偶数个固定槽，$\ell_i=\ell/K$，各自具有非负、非零的光滑权重和互不相交的原 annulus；槽系在目标及 $Z$ 前固定。原有限物理恒等式和 quotient-free selected-local-operation 对任意这些正尺度成立，故仍得到原完整标量商、Gaussian、全部六次幂自由 $u$ 行与完整修正，而非另定义一个高端积分。

实际尺度满足
$$
C(s)=s+\frac{l_x}{2}-1+\frac h6=s-\frac{11}{16},
$$
$$
B=\frac{l_x}{2}+\frac b{12}
=\frac{74999}{400000}=\frac3{16}-\frac p4,
\qquad
\theta=\frac78-\frac p4=\frac{349999}{400000},
\qquad B=C(\theta).
$$

### 新能量代价与完整低端

对实际 rescaled 子集 $J$，令 $d=\sum_{i\in J}\ell_i\in[0,\ell]$。其原低分离具有
$$
M'=M-2d,\quad \ell'=\ell-d,\quad
Q=q_{b_*}X'Y'\asymp Z^{M'},\quad
\frac{Y'^2}{Q}=q_{b_*}^{-1}Z^b.
$$
不能套用主稿固定几何的 `probe-row-norm`。使用其一般 `reflected-energy`，保持原 Gaussian annuli、一个共同的齐次 Fourier 密度、实际 residual-row 长度 $H$、powerful 长度 $O$ 和全部合法 dual 支持。记 $\Delta_H=M'-O-H\ge-\varepsilon_Z$。源输入仍有
$$
2A_0\le O+\varepsilon_Z,\qquad N_0\le A_0,\qquad z_a\le\ell',
$$
$$
T_d=2H+2A_0+2z_a-1-\ell'-\vartheta_N-N_0-3B_0.
$$
由 $M'+\ell'-1=-3d$，得到 $T_d\le H-3d+2\varepsilon_Z+|\vartheta_N|$，故 retained dual 长度仍使 $\max(H,v+\ell_b)=H+$ 已支付小损失。原 dual ideals 可共享素数并保留源文允许的 $S$ 支持；不追加互素限制。源能量两支在此实际参数下为
$$
M'-\Delta_H,\qquad
M'+\frac{1+3\ell'-2M'-2\Delta_H}{4}
=M'+\frac{d+5\ell-1-2\Delta_H}{4},
$$
另加可任意指定的小损失。它们随 $\Delta_H$ 递减，因而整份完成行满足
$$
\boxed{\sum_m|B_m^J|^2\ll
Z^{M'+((d+5\ell-1)/4)_++\varepsilon}.}
$$
这保留了新增的能量代价；在 $d=\ell$，所示额外 allowance 为 $3p/2$。kernel 的 $H$ 在正 sieve 扩大前固定；powerful／supported 部分的计数已含在源能量中，不再重复计数。所有 Gaussian、reflection、Fourier 和 dyadic 尾项按源共同密度与固定 seminorm 阶支付。

实际正裕度为
$$
M'_{\min}=\frac{49997}{100000},\quad
l_x-\ell=\frac{37497}{200000},\quad
l_y-\ell=\frac{62497}{200000},\quad
l_y-\ell-\frac{11b}{6}=\frac{49991}{600000}.
$$
在足够大 $Z$ 上，它们满足一般 additive Gram 的 $Q,Y'\ge1$、$P_a=Y'^2/Q\ge1$ 及 $P_a^2/Y'\ll P_a^{1/6}$。使用原 $Q^{-1/2}$ 归一化、Cauchy–Schwarz、完整 height 积分和原元组权重后，整个 $J$ 子集的指数为
$$
B-d+\frac{(d+5\ell-1)_+}{8}.
$$
因为 $\ell<1/5$，$(d+5\ell-1)_+\le d$，所示指数至多为 $B-7d/8\le B$。求和全部有限子集，得到每个请求的 $\varepsilon>0$ 下的完整低端
$$
\boxed{|I_{\eta,\mathrm{modified}}(Z)|\ll Z^{B+\varepsilon}.}
$$
这里计算的是同一实际探针，包含所有 rescaled 元组及其 $-3d/2$ 权重。

### 正容量参数与真实主信号差额

反设 $\beta_*>\theta$，复用主稿 Part I 的 $\beta_*\le11/12$。定义
$$
D=\beta_*-\frac78\in(-p/4,1/24],\qquad
\Gamma=\max(D,p),\qquad \kappa=\frac34+2\Gamma.
$$
于是 $\kappa\in[3/4,5/6]$，$\beta_*\le(1+\kappa)/2$，每个实际 buffered bin 的 $\delta=2a-1\le2\beta_*-1\le\kappa$。这里 $D$ 可以为负；不能把 $\Gamma$ 当成真实主信号差额。

源 plain moment 的正槽前提是 $\beta_*\le(1+\kappa)/2$，不要求等号。因此可在原联合见证计数的证明中使用实际容量
$$
z_P(m)=\frac{1-2m}{6\kappa}
=\frac{1-2m}{9/2+12\Gamma}.
$$
原 inverse capacity、amplification、实际饱和 witnesses、$t\in[1,3/2]$ 和两条比较线保持。计数证明唯一需要替换的容量价格为
$$
2q(1-2m)\left(\frac29-\frac1{9/2+12\Gamma}\right)
\le\frac\Gamma4+\text{已分配小损失}.
$$
这使用同一实际 $m\ge1/3-$ 小损失、$2q\le1$ 和正分母下界。其余推导只需 $\delta\le\alpha=5/6$ 和上述正槽前提，不需 $D>0$ 或 $\Gamma=D$。因此对同一物理 amplitude／witness 集合，复用原 $D_x,P_x,\mathcal J,t,R_*$ 可得
$$
R\le R_*+\Gamma/4+\varepsilon,\qquad 0\le q\le\delta/2.
$$
不越界套用原固定阶段的 proposition。保留同一字符、whole-product 共轭、共同掩码、固定 ray 系数及全部自然零。小／零容量采用源 no-slot 分支；$\delta=5/6$ 用零容量 amplified 界；floor bin 用直接计数。$d\le1/2$ 使用不选槽的 $R=76/75-2\delta/3$。

取 $\zeta=1/1000000$。原实际槽的供给满足
$$
\frac\ell h-\frac7{37}=\frac{287659}{18037833}>0,\qquad
\frac\ell{h+\zeta}-\frac15=\frac{31301}{6093870}>0.
$$
在目标及 $Z$ 前选足够细的固定 $K$，使 $\ell_i/d\le2\ell/K$ 同时满足 plain mesh、平方 spike rounding、inverse strict widths 和内部 amplifier-pool 分离。容量先作固定递减，接近零时不用 marked 界。每个冻结标签类中只选真实整槽；error 槽的 $g_i=0$ 不提供正 spike，正 main 槽用尽时沿用源 greedy 规则。annular offsets 在足够大的阈值吸收。

### 全部轮廓、主行及外围行

主稿 shared high lemmas 的印出前提是 $\sigma_0\ge7/8$，这里需逐项核对其证明，而非直接代入 $\theta$。

对非主 fixed bin，原第一 Euler 域不变。先 $z:2\to17/50$、$w=3$、$s:3\to\beta_*+20e$，再 $w\to1-a-6e$，全程 $s+w\ge1+(\beta_*-a)+14e$。限制原三份 Mellin heights 后，才移动 $s\to a+16e$；此时 $s+w\ge1+10e$，完整原 reciprocal 在实际 buffered rectangle 内无零。每行 numerator 非主；scalar $6z>1$；没有新增 $\zeta(s+w)$，亦无 sf mixed diagonal。原 proof 的其余步骤不使用 $\sigma_0\ge7/8$；bin-accounting 仅以 $C(\sigma_0)$ 为减去的尺度。原 integrated／trace tails 保持：$s$ 进入 buffered 区后不向整个虚轴延长，joins 只延长有 global bounds 的 $w,z$。continuation 始终使用完整 quotient-free correction。

主行使用本条已证明的扩大域 $\Re s\ge7/10$、$\Re w\ge19/20$、$\Re z\ge33/200$。原 principal proof 的所有路径和 joins，包括 $(\beta_*+e,1+e,1/6+e)$、$w\to19/20$、其 residue 中 $z\to33/200$，均在域内。完整 tuple 在全部 heights 上为 $O(Z^{\ell\Re z})$。只跨 $w=1,z=1/6$ 两个 scalar poles，保留 Jacobian $1/6$、global reciprocal 和全部 integrated／trace tails。residue error 留在原 global line；只将 main $s$ 积分右移到 $2$。

在物理校准前扩大固定 cutoff，使已保留的 $H_\eta=1+O(P_0^{-1/5})$ 在 $\Re s>\theta$ 满足 $|H_\eta-1|\le1/2$。同步固定 $S,b_*,\xi,\tau,\Xi,c_S$ 及探针；后添目标的有限 exclusions 保留此 bound，$T$ 与槽系不变。使用同一实际移动 normalizer
$$
A_T(Z)=(-1)^KZ^{-\ell/6}\prod_i S_i(Z),\qquad
|A_T|\asymp(\log Z)^{-K}.
$$
扩大域上的 residue ratio $-1+O(Q^{-1/2})$ 给出任意 $0<\mu<\tfrac12\min_i\ell_i$；可取 $\mu=\ell/(4K)$。主行三份裕度为
$$
m_w=\frac{l_y}{20}=\frac{287497}{12000000},\qquad
m_z=\frac h{600}=\frac{162503}{120000000},\qquad \mu.
$$
原角向因子、标量 pole 和非零主信号全部保留。

小行 global lines $(\beta_*+e,1/2,17/50)$ 可用第一 Euler 域的 $\varepsilon_0=1/4$，替代旧证明的 $3/8$，因为 $\beta_*>\theta>4/5$。在 $s_r\ge4/5$，raw $G_p$ 的未分歧误差指数
$$
-s_r,\quad-51/25,\quad4-5s_r-51/25,\quad1/2-51/25
$$
全部为负。分歧处乘 $Q^s$ 后全部 $j=1,\ldots,5$ boundary exponents 为
$$
-1/2,\quad3/2-2s_r,\quad(3/2-2s_r,2-3s_r),\quad
2-3s_r,\quad3-5s_r,
$$
均为负；strict 项至多 $Q^{1/2}$，common $R$ 项指数至多 $-51/25$。故 $G_p=O(1)$ off $u$、$G_p\ll Q^{1/2}$ on $u$。原 unselected 正乘积、divisor-many 分歧选择及完整 disjoint tuple 给出 $|\mathfrak H|\ll U^\varepsilon Z^{17\ell/50+\varepsilon}$ 于全部 heights，也在 $H_p,P_p$ 的零点成立。所有 $u\ne1$ 及 finite unit／exceptional rows 的 numerator 非主；可能的主 denominator 仍在 global line 上受控。原 outer proof 因而保留 row 指数 $63/50$。

大行在 $(2,2,z_\infty)$、固定 $z_\infty>2$ 上使用原 absolute local bound，完整 tuple 为 $O(U^\varepsilon Z^{\ell z_\infty+\varepsilon})$。令 $B_0=l_x/2+1+l_y$，整个 $U>Z^{h+\zeta}$ 尾部为
$$
O\!\left(Z^{B_0+(h+\zeta)(1+\varepsilon)-\zeta z_\infty+\varepsilon}\right).
$$
$z_\infty$ 在 $\zeta$ 后、目标前固定得足够大。起始行级数和最终尾部都绝对收敛，允许求和全部 dyadic contour identities。

### 原 endpoint certificate 支付几何扰动

原 dynamic-local-errors、prime bound、functional equation 和 simultaneous conductor-deficit allocation 不含旧 $l_x,l_y,\ell$。它们在同一实际行及所有 main／error 子集上给出相对 $C(7/8)$ 的高指数
$$
E_p(d)=a-\frac78+h(c-1/6)-a l_y-(1-a)\ell
-(\delta/2-q)\ell+d(R+\delta/2-c),\qquad c=17/50.
$$
bin 在 continuation 前固定；amplitude／witness 集合只在移动后用于 pointwise envelope，没有给各集合单独移动轮廓。

复用原 $h_0=13/16$ 的 endpoint certificate
$$
-E_{\mathrm{old},*}(h_0)\ge m_0=\frac{49}{440640}.
$$
源 $D_x-P_x>0$ 和 $R_*=1-\delta+\delta P_x(3/2-t)/D_x$ 给出 $R_*\le1$。实际扰动满足
$$
E_p(h;R_*)-E_{\mathrm{old}}(h_0;R_*)
=p[1+\delta+q-\tfrac32(1-R_*)]\le\frac{9p}{4}.
$$
加入 $h\Gamma/4$ 后必须减去真实 $D$。$D\ge p$ 时 $h\Gamma/4-D\le0$；$-p/4<D<p$ 时该价格 $<p/2$。因此 endpoint 仍节省
$$
m_h=m_0-\frac{11p}{4}=\frac{46103}{550800000}>0.
$$
完整 floor、intermediate 和 small-row 裕度分别为
$$
m_f=\frac7{1200}-\frac{32p}{25}=\frac{21827}{3750000},
\qquad
m_i=\frac{49}{14400}-\frac{177p}{200}
=\frac{610907}{180000000},
$$
$$
m_s=\frac{63}{800}-\frac{51p}{100}
=\frac{787449}{10000000}.
$$
其中 intermediate 在 $d=1/2$ 的几何成本为 $p(1/100+\delta/4+q)\le127p/200$，另计负 $D$ 的最大 $p/4$；floor 成本为 $103p/100+p/4$。小行直接相对 $C(\beta_*)$ 比较，不再减 $D$。取 $d_{\min}=1/100$。

selected range 的理想 slope 为正，因为 $R\ge1-\delta$；原紧实参数界使 slope 小于 $2$。$d\le h$ 由 endpoint 控制，延长至 $h+\zeta$ 成本至多 $2\zeta$，留下
$$
m_c=m_h-2\zeta=\frac{225007}{2754000000}>0.
$$
$\delta=5/6$ 保留 amplified 的 endpoint，floor／intermediate 裕度均大于 $m_c$。所有 adjustable real、count、normalizer 和 logarithmic multiplicity 成本另置于这些实际正裕度内。

### 同一物理 low／high 的完成与范围

在反设下，令 $\Delta_\theta=\beta_*-\theta>0$，取共同 low loss $\omega=\Delta_\theta/2$。先按 $m_c$ 等裕度选 moment／capacity／rounding losses，再选实际足够细的偶数 $K$，固定 $\mu=\ell/(4K)$；随后 principal 的 $e$ 与其损失适配 $\mu$。已选 central moment losses 无需重新变成小于 $\mu$，没有 mesh 循环。low 的 Gaussian／reflection 损失适配 $\omega$；结构及实参数在目标／$Z$ 前固定，目标的最终排除集及物理校准共同确定。

只列一次全部 buffered arguments 的物理及辅助 height 坐标，包括 $\Im z$，使用源累计 allowance。所有辅助 discarded pieces、global／absolute tails 与 horizontal joins 在 pointwise bound 前支付。固定目标的内部 moment、profile 和 seminorm 阶后，以 $A_\eta$ 控制全部 retained height costs，$A_{\mathrm{ht},\eta}$ 控制 detector 阶，$\varepsilon_{\mathrm{ht}}>0$ 为其最小 allowance，要求
$$
0<\tau\le\min\left\{\frac{d_{\min}}{100},
\frac{d_{\min}\varepsilon_{\mathrm{ht}}}
{20(1+A_{\mathrm{ht},\eta})}\right\}.
$$
这保证全部 moderate $U\ge Z^{d_{\min}}$ 上源 detector 的字面 height 条件。外部衰减阶 $N$ 随后选取，只改变外部 test 常数和阈值，不改变内部 $A_\eta$ 或固定 scale degree $B_\eta$。

以同一 $c_SA_T(Z)$ 归一化，取一个共同的 $0<m<\tfrac14\min(m_c,m_s,m_w,m_z,\mu)$，所有损失在其预留范围后有
$$
|J_\eta(Z)|\ll_\eta Z^{C(\theta)+\omega},
$$
$$
|J_\eta(Z)-f_\eta(Z)|\ll_{\eta,N}
Z^{C(\beta_*)-m}(1+T_1)^{A_\eta}+Z^{B_\eta}T_1^{-N}.
$$
$J_\eta$ 为上述有限原物理表达式除以 $c_SA_T$，$f_\eta$ 为原 $\Re s=2$ 主信号；两者均不依赖 analysis height $T_1$。复用已允许 $\sigma_0\in(1/2,1)$ 的 late-height-closure，先按目标选 $\tau$，再 $N$ 和阈值，得到共同 high saving $m/2$。同样范围的一般 continuation criterion 因而反驳 $\beta_*>\theta$。

所以，在上述完整源输入成立时，得到条件结论
$$
\boxed{\beta_*\le\frac78-\frac1{400000}.}
$$
同一所引 Hecke-to-Dirichlet transfer 给出对应全部有限阶 Hecke／Dirichlet targets 及 $\zeta$ 在严格半平面 $\Re s>\theta$ 的条件无零结论，覆盖全部模数和高度；不包含边界。这里的新增内容是完整改尺度消费，源 theta、Gram、moments、detector、certificate 和 continuation 均为复用输入，不主张历史原创性。

隐常数、最终校准和足够大的起始阈值可依赖目标特征；没有认证显式数值阈值或共同起始阈值、整篇源证明或新增 Lean 核验。该条件半平面仍远于 $1/2$，不证明 RH；原选定 Robin 极值整数的完整有符号响应、实际零点及完整系数、正 $r_A$ 和严格核心仍未证明。

## 正素槽四阶矩的固定参数范围扩展

本节为仓内推导，复用固定[主稿快照](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex)的完整有限 Gauss 公式、smooth calculus、logarithmic control、natural reflection、两次变换的共同系数关系及 centered lattice cancellation。它们作为解析前提；不以待扩展的 `lem:plain` 本身作新范围的前提。下面通过替换其反射比较余量，接续原有限归纳。完整解析推导尚无本仓 Lean 认证。

[Liu 的来源卡](liu2026quasirh.md)所引 [arXiv:2610.12234v1](https://arxiv.org/html/2610.12234v1)在引言明确提到越过 $[3/4,1]$ 可能进一步改善其结果，并说不研究该方向；其 Lemma 9.3 与 §18 仍使用原范围。本节不重算其已有无零边界或固定参数计数。所查来源未供应下述扩展，不据此主张全球原创性。

### 保留原正槽合同

固定
$$
\frac12<\kappa_0\le1,\qquad \kappa\in[\kappa_0,1].
$$
沿用源文 `lem:plain` 前的实际字符 $\psi_k$、有效行宽 $M=m+q$、自然及冗余零延拓、固定素集 $\mathcal S$、有限 ray 字符群 $\Theta$ 和行集 $\mathcal R_z$。正槽时 $\mathcal R_z$ 排除诱导字符属于 $\Theta$ 的行；排除针对诱导字符，而不是零延拓表示之间的相等。

保留两个原 centrally normalized plain 因子及全部正素槽
$$
Q=\prod_{i\in\mathcal I}Q_{\psi_k,i},\qquad
z=\sum_{i\in\mathcal I}z_i>0,
\qquad A=n_1+n_2+z.
$$
$n_1,n_2,z_i\ge0$。槽的底层素支持在施加共同掩码与行零延拓之前两两不交；它们与 plain 变量的重叠仍保留。每槽系数仍为固定有限 $\Theta$ 字符线性组合，与 $Z$ 和行无关。所有原 moving twists、moduli、固定外标签及 polynomial-size 掩码均保留，不改为一个目标字符或选出的子族。

在上述源估计成立且
$$
n_1+n_2+6\kappa z=A+(6\kappa-1)z\le M
$$
时，下面的归纳给出原形式的条件估计
$$
\boxed{
\sum_{k\in\mathcal R_z}
\left|S_{\psi_k}(n_1;W_1)S_{\psi_k}(n_2;W_2)Q\right|^2
\ll Z^{M+\varepsilon}.}
$$
$\kappa<1$ 时仍要求源定义 $\beta_*$ 所涵盖的 $F=\mathbb Q(\sqrt{-3})$ 上全部本原有限阶 Hecke 字符族的
$$
\beta_*\le s_\kappa=\frac{1+\kappa}{2};
$$
$\kappa=1$ 使用原绝对素计数，不要求无零前提。长度参数处在预先指定的有界集。对每个 $\varepsilon>0$，先选择一个在 $[\kappa_0,1]$ 上一致的槽 mesh $\eta>0$，再允许任意固定有限槽数及满足 $z_i\le\eta$ 的槽系；mesh 不依赖槽数。有限 seminorm、poly-height 阶、常数和充分大阈值可依赖固定算术数据与槽数，但在原 moving labels、moduli、masks 和实际 heights 上一致。新增允许依赖的是固定 $\kappa_0$；不要求当 $\kappa_0\downarrow1/2$ 时一致。

零槽估计直接复用原供应，不作为新增范围成果。每次归纳变成零槽时，预先规定有界范围内的非负 plain 长度不受 affine 容量限制，也没有导子下界；不声称长度趋于无穷时常数仍一致。

### 替换反射比较的正余量

令
$$
d_0=6\kappa_0-1>2,\qquad d=6\kappa-1\ge d_0,
\qquad g_0=\frac{d_0-2}{6d_0}>0.
$$
按原归纳顺序，在扩展参数范围内，每个正槽 band 先由两次变换、严格较小宽度的扩展归纳假设及例外行体积界完成 $A\le5M/6$ 的未中心化范围。对于 $A>5M/6$，容量给出
$$
d_0z\le dz\le M-A<\frac M6,
\qquad z<\frac{M}{6d_0}<\frac M{12}.
$$
因此 $A-z>3M/4>2L$，其中仍取 $L=M/4$；比较矩形的两个 plain 长度均至少为 $L$。

若一个原 plain 因子长 $b<L$，反射另一因子；否则引入 plain 长度 $L,A-z-L$ 的同乘积比较，并在单独估计比较时反射长因子。原 `centered-reflection-length` 包含实际 clipped 尺度、unit-box multiplier 及全部 discarded tails，给出
$$
A_{\rm comp}\le\frac32M-A+2z+\xi.
$$
于是两条所需边界分别满足
$$
\begin{aligned}
A_{\rm comp}
&<\frac23M+\frac{M}{3d_0}+\xi
=\frac56M-g_0M+\xi,\\
A_{\rm comp}+dz
&\le\frac52M-2A+2z+\xi
<\frac56M+\frac{M}{3d_0}+\xi
=M-g_0M+\xi.
\end{aligned}
$$
这替换原 `comparison-uncentered-margin` 中的粗界 $M/15$，而不改变反射、共同 mask 或比较矩形本身。对原宽度 floor $\rho>0$，取
$$
0<\xi<\frac{g_0\rho}{2}.
$$
每个 $M>\rho$ 的 retained 比较便有两份至少 $g_0M/2$ 的余量，能调用同宽度已经完成的未中心化范围。所需 reflection／support 阈值在固定槽数后选取，不把逐槽误差累加成 $N\eta$。

### 原有限归纳的其余支付

素槽估计使用的是 `logarithmic-control` 的 global 部分，其实际前提允许 $a\in[1/2,1]$；固定 $s_\kappa\ge\beta_*$ 后，global 常数只依赖规定 contour displacement 和幂损失，并无 $s_\kappa\ge7/8$ 条件。对有限 $\Theta$ 展开，本原诱导字符 $\psi\notin\Theta$ 保证每个 $\psi\vartheta_{ij}$ 非主。原 Mellin 移动、全部素幂补偿和 annular twist 估计因此仍给出
$$
|Q_{\boldsymbol\omega}|^2
\ll Z^{\kappa z+\varepsilon_1}
p_j(\boldsymbol W)^b(1+|\boldsymbol\omega|)^h,
$$
且 contour 位移的平方指数成本仍是 $2ez$，与槽数无关。有限阶及高度成本留在 Fourier 估计中，不塞入 $Z$ 的 leading 指数。$\kappa=1$ 仍以绝对计数接入。

固定额外 mask 的 simultaneous erasure 沿用原 `2.1a` 与 `prime-mask-erasure`：提取 plain divisor 和冻结完整槽后，$A+dz$ 不增；诱导字符不变、所有原自然零支持保留。实际非空 subunit 尺度先按原规则 rescale，再调用矩估计。若没有 live 槽，改用原零槽供应。deleted Euler-factor 质量及冻结槽质量按原固定数据、固定槽数分配任意小幂。

宽度 $M\le\rho$ 的终端只需要
$$
6\kappa z\le M,\qquad \kappa z\le M/6.
$$
原辅助界 $z\le2M/9$ 无需使用；正槽增加的终端损失仍至多 $\rho/6$。零槽 padded core、先完成零槽 bands 再完成正槽 bands 的顺序不变。

对两次完整有限变换所产生的非例外 child，保留原 actual normalization、common mask、全部 sixth-power 行及 `centered-clipped-rectangle`。容量 deficit 为
$$
F_{\rm act}
=\bigl(A_{\rm act}-M'_{\rm act}+dz_{\rm act}\bigr)_+.
$$
按完整槽依次移除，取第一个达到 $F_{\rm act}/(6\kappa)$ 的前缀；若不足则移除全部。总移除长 $d_z$ 满足
$$
d_z\le\min\left\{z_{\rm act},
\frac{F_{\rm act}}{6\kappa}+\eta\right\},
\qquad \kappa d_z\le F_{\rm act}/6+\kappa\eta.
$$
原 actual child 的共同支持预算仍给出
$$
F_{\rm act}\le6(w+\ell)+\delta_{{\rm fr},1}+2\theta_N,
\qquad \Delta_{\rm child}\ge w+\ell.
$$
于是整槽价格至多 $\Delta_{\rm child}+\delta_{{\rm fr},1}/6+\theta_N/3+\eta$；与 `centered-clipped-shell` 合并，原严格边的额外成本仍至多
$$
\delta_{{\rm fr},2}+\delta_{{\rm fr},1}/6+\eta+7\theta_N/3.
$$
这里 $\theta_N=H_N/\log Z$ 是先聚合再比较的一份 support 误差，最终阈值使它落入 $C_*\xi$。分母 $6\kappa$ 与素槽指数价格 $\kappa$ 在同一实际 child 上抵消；这一支付只需 $\kappa>0$，无需旧 $3/4$ 下界。仍有 live 槽且修复容量后，调用严格较小宽度已完成的扩展正槽归纳假设；槽全部消失则调用原零槽供应。不向负完成长度外推矩定理。原归纳的宽度严格下降、两项 common-support savings 和 inverse amplification slope $5/6$ 不改变。

对诱导字符属于 $\Theta$ 的例外 child，继续在取绝对值之前使用同一行、同一 mask、同一 norm power 的等乘积矩形主项消去。原 `2.18h` 与 `2.19` 给出
$$
A-\frac56M-\frac23v-(L-v)_+\le(A-M)_+.
$$
正槽容量仍保证 $A\le M$；零槽 padded core 仍有 $A-M\le\delta$。所以例外分支损失仍分别由 $3\sigma$ 或 $\delta+3\sigma$ 支付，不删除例外行或 moving radical。

原有限归纳的 aggregate support perturbations 只使用 $0\le d\le5$，在 $[\kappa_0,1]$ 上保留。先固定宽度 floor、step 及
$$
D=2+\left\lceil2M_{\max}/\sigma\right\rceil,
$$
再让 $\eta,\xi,\varepsilon_0$ 同时满足原有限深度误差包络与新增 $\xi<g_0\rho/2$。各 surviving 槽子集用同一 mesh；仅局部 divisor／冻结槽的小幂 shares、有限 kernel／height 阶、常数和最终阈值允许依赖原固定槽数 $N$。按原证明向后选择有限 seminorm 阶后，再选外部 Fourier-tail 阶，不以增大外部阶改变已定内部高度阶。如此接续原 `Completion of the finite induction`，得到上述条件正槽估计的完整量词，而不重证原零槽估计。

固定 $\kappa_0>1/2$ 是这里获得统一反射正余量的条件。$\kappa=1/2$ 时 $g_0=0$，当前论证不给出所需 uniform comparison margin；这不反驳端点矩估计。没有供应端点、$\kappa_0\downarrow1/2$ 的统一 mesh、完整解析 Lean 证明、新无零半平面或 Robin／RH 结论。

### 对已知无零输入的容量接口

若一份完整来源已供应上述源定义所含全部 Hecke 字符族的 $\beta_*\le B$，其中 $3/4<B<1$，可固定
$$
\kappa_B=2B-1>1/2.
$$
选任意固定 $\kappa_0\in(1/2,\kappa_B]$，便有上述正槽合同所需的 $\beta_*\le(1+\kappa_B)/2$。在原联合 witness 计数中，两个同长 plain 因子取长 $m$、有效行宽取 $1$，连续 affine 容量上限为
$$
z_P(m;B)=\frac{1-2m}{6(2B-1)},\qquad 0\le m\le1/2.
$$
当 $B<7/8$ 时，对每个 $m<1/2$，它严格大于固定 $\kappa=3/4$ 的原容量；在 $m=1/2$ 时两者均为零。容量比为
$$
\frac{z_P(m;B)}{z_P(m;7/8)}
=\frac{3/4}{2B-1},\qquad m<1/2.
$$
这不保证该上限可由某份实际槽系达到；整槽选择仍需符合新 mesh、可用总槽长、rounding 及严格误差预留。这是扩展供应的参数消费，不是新增无零结论。特别地，若采用 Liu 预印本所述的完整族界
$$
B=B_{\rm Liu}=\frac{1507-2\sqrt{921}}{1653},
$$
则使用 $\kappa_B=(1361-4\sqrt{921})/1653$；不把本仓较弱的条件半平面当作当前最佳文献界，也不把 Liu 已有改进重新计作项目成果。

更大的容量仍须在同一实际探针的全部 high／low 行、主信号、profile、共同掩码和 finite-height accounting 中一起消费，才可能改变无零边界。单独优化容量或重算已知平衡方程不能承担这份解析回接；原 inverse slope $5/6$ 及其支付并未改善。这里既未完成该 high／low 再比较，也未证明仓内既定 Robin 路线针对原极值族的有符号目标
$$
[-I_\psi(A)]_+=o(A^{-\eta_{\rm R}}),
\qquad 0<\eta_{\rm R}<1/2.
$$
$\eta_{\rm R}$ 为该路线已经固定的原指数，不随本节的槽 mesh 重选；$A$ 与 $I_\psi$ 使用 [Nicolas／Robin 对应条目](../ArithSums/nicolas2025comparison.md)的原定义。后者仍要求同一实际对象的完整带符号系数、素幂、端点与 collisions；非负四阶矩上界不自动控制它的符号。五模式 FIB 地址、四相运输及收缩区间仍可复用为来源与观察语言，但它们不替代这一解析桥梁。

### 同字符计数的消费与比较余量

下面复用 Liu v1 的 Proposition 18.1、Proposition 18.2、§23 和 Proposition 3.1，核对扩展容量的下游用途。这里只推导这些既有公式在扩展参数下的条件性包络诊断，不重新优化其预印本所述边界，也不将公式应用计为新增数学定理。解析前提及实际类的可实现性没有由以下代数核对认证。

在同一原 sixth-power-free 元行集合 $\mathcal B$、同一字符、presentation、共同掩码和零延拓上，两矩给出的上界仍为
$$
\#\mathcal B\ll
U^{1-\delta r-2\bar g z+\varepsilon}(1+T_1)^A,
\qquad
\#\mathcal B\ll
U^{1-2\delta m-2\bar g z+\varepsilon}(1+T_1)^A.
$$
这里 $\delta=2a-1$、$\bar g=x\delta$，短检测参数满足 $1\le t\le3/2$、$t-1/2\le r\le1$、$m=t-r$。两个估计可以在同一行集合上分别选择合格素槽；扩展普通矩只把其容量改为
$$
z_S\le c_\kappa(1-2m),\qquad c_\kappa=\frac1{6\kappa}<\frac13.
$$
逆矩的 $z_M\le(1-r)/2$ 不变。两侧仍各自支付 $z_{\rm sup}=\ell/d$ 的实际可用长度、严格 moment reserve、单槽 rounding 和 height costs；实际 $\kappa$ 还须满足前节的完整族无零前提，不能仅凭所需容量自行选取。

为诊断公式的最佳可能消费，暂时免除可用素长上限，并把 $c_\kappa$ 放宽到 $1/3$。这只是最乐观的比较，不调用未供应的 $\kappa=1/2$ 端点矩。固定声明矩形中的形式类
$$
\alpha=\frac56,\qquad \delta=\frac38,
\qquad x=\frac12,
\qquad a=\frac{11}{16},\quad \bar g=\frac3{16}.
$$
没有证明这个零类和幅度类在某个实际行尺度上出现。原 §23 的两份节省函数为
$$
F_I(r)=r+2x\min\{(1-r)/2,z_{\rm sup}\},
$$
$$
F_S(r)=2m+2x\min\{c_\kappa(1-2m),z_{\rm sup}\}.
$$
在上述乐观比较中，交点
$$
r(t)=\frac{8t-1}{11},\qquad m(t)=\frac{3t+1}{11}
$$
在整个 $t\in[1,3/2]$ 上合法，且 $F_I=F_S=(5+4t)/11$。因此这套短、长检测公式的理想包络分别为
$$
R_s(t)=\frac{73-12t}{88},\qquad
R_l(t)=1-\delta+(\alpha-\delta)(t-1)=\frac{4+11t}{24}.
$$
它们在 $t=175/157$ 相交。正权重 $121/157$、$36/157$ 消去 $t$，得到
$$
\inf_{1\le t\le3/2}\max\{R_s(t),R_l(t)\}
=\frac{851}{1256}>\frac23.
$$
交点的 $r=113/157$、$m=62/157$ 位于短检测参数域内部，理想容量 $z_M=22/157$、$z_S=11/157$ 均为正；实际调用仍须从这些上限扣除严格预留。比较没有把零槽备用估计当成正槽端点供应。恢复较小 $c_\kappa$ 或有限素长 cap 只会减少节省，使该均匀包络的指数不减；零槽替代也不优于这个放宽。这里的下限约束的是这些公式能供应的均匀指数 $R_{\rm env}$，不是实际 $\#\mathcal B$ 的下界，也不排除别的计数估计供应较小指数。

比较余量必须使用原归一化。由 Proposition 18.2，任意尺度的非主行上界是
$$
Z^{C(B)+E_B(d)+\varepsilon}
=Z^{C(\beta_*)+E_B(d)-(\beta_*-B)+\varepsilon},
$$
$$
E_B(d)=a-B+h(z_0-1/6)-al_y-\ell/2+\bar g\ell
+d(R_{\rm env}+\delta/2-z_0),\qquad h=1-l_x+\ell>0.
$$
本比较另外规定：在 $d=h$ 用这份公式对整个声明矩形提供相对 $C(\beta_*)$ 的正 saving，故要求 $E_B(h)<\beta_*-B$。这份均匀合同不由实际类必然出现推得，也不声明每个合法尺度选择都需要它。在上述形式类，仅用 $R_{\rm env}\ge2/3$ 就有
$$
E_B(h)\ge H_{\rm env}-B,\qquad
H_{\rm env}=\frac{11}{8}-\frac{11}{16}M+\frac38\ell,
\qquad M=l_x+l_y.
$$
因此这一均匀高行设计要求 $H_{\rm env}<\beta_*$，不能径直替换为 $H_{\rm env}\le B$。

同样，Proposition 3.1 的 low 条件允许 $C(B)+\omega_0$，其中 $0<\omega_0<\beta_*-B$。§22 完整直接 majorant 中的两项
$$
L_0=\frac56+\frac{M}{12}-\frac{\ell}{6},\qquad
L_K=\frac13+\frac{7M}{12}+\frac{\ell}{3}
$$
在使用这份余量时，比较要求为 $L_0,L_K\le B+\omega_0$；它们只是完整 majorant 的两个子约束，不足以独立供应 low。正权重 $43/63$、$8/63$、$12/63$ 给出恒等式
$$
\frac{43}{63}L_0+\frac8{63}L_K+\frac{12}{63}H_{\rm env}
=\frac{55}{63}.
$$
在这三个明列的均匀包络约束下，得到
$$
\frac{55}{63}
\le\frac{17(B+\omega_0)+4\beta_*}{21}
<\beta_*.
$$
这限制的是此套设计可消费的输入 $\beta_*$。若另外采用较强设计 $L_0,L_K\le B$，则中间式为 $55/63\le(17B+4\beta_*)/21$；只有再要求 $E_B(h)\le0$，使三项都不超过 $B$，才得到 $B\ge55/63$。不能省略这些附加条件，把后者报告为所有 continuation 比较的目标边界下限。若要从任意小反设间隙推到目标边界下限，还须证明相同均匀域及相应设计在那些间隙下继续成立，不能把量词当成新的供应。

这些是指定充分估计公式的范围核对，不是 $\beta_*$ 的实际下界，不证明形式最坏类可实现，也不构成 RH 或其他证明方法的障碍。仅删掉某个形式端点亦不自动改善计数；所需是实际类关系可消费的增益，或不经逐类绝对值的总和控制。

实际再比较还要保留最低零类、小行、中间行、$d>h$ 延伸、大行和主项提取。Liu 的 Lemma 17.1／(17.1) 供应主 Euler 域的 $B$ 范围为 $[437/500,7/8]$，下面没有把它延伸；更低目标需要新的域供应，不能把现有供应范围称为域不可能扩大的定理。当前公式中的直接 majorant、逆矩及长检测的 $5/6$ 价格也未改进。

因此，固定参数矩扩展已提供一个可调用的条件容量接口；继续仅调这个容量，不能替代上述联合预算核对。能回接原目标的未证输入仍是同一实际对象上的新联合估计、可消费的实际类约束，或保留完整符号与系数的总和控制。任何这些输入都须连同余量、全部行和主项一起支付；这里没有证明某个单独 $R<2/3$ 是原目标的必要条件，也未供应原固定 $\eta_{\rm R}$ 的 signed Robin 界。


### 六阶通用筛法与原 detector 的比较

[de Faveri 的既有 Theorem 1.1](faveri2026fixedorder.md#application-to-the-original-common-character-detector)可直接供给原始共同字符 $M_rS_m$ 的混合矩：有限 $S$-单位修正进入固定列系数，列分解 $h=ab^6$ 保留 $\mathbf1_{(b,u)=1}$，再以收敛的 $\sum_b(Nb)^{-3}$ 汇总。该应用以原解析供应成立为条件，未作完整解析 Lean 认证；论文自身已有 Corollary 1.5 零密度结果。

这份通用供应未改善完整 detector 的现有统一计数预算。在 $1/50<\delta\le5/6$ 的比较范围内，对原实际 $\tau=r+m\ge1-\text{小损失}$，其计数公式的指数不低于 $7/6-\delta-\text{小损失}$；已有 inverse amplification 和零槽 plain 四阶矩在合法设置 $t=1$ 或 $t=5/4$ 上，已经对整类提供不超过 $7/6-\delta-1/36+\text{小损失}$ 的指数。前者是上界公式的下限，不是实际行数下界；仅固定 $t=1$ 的局部改善不能算作整体进展。条件、实际 witness 域和比较推导均归上述来源条目，不重复证明筛法或重新优化 Liu 的边界。

能超过这一通用预算的候选缺口，是保留原截断 Möbius 卷积系数的 off-block 相关和；上述条目给出其准确合同及已可直接控制的同六次幂自由部分。该估计仍 open，平衡长度上的结果也不自动覆盖其他实际 witness 长度或接通完整 signed Robin 目标。

### Coherent simultaneous high-valuation branches

本节为 `repo-derived` 的原系数联合应用，复用[完整原始反演、固定 cusp 估计及标记素数的全部重数贡献](faveri2026fixedorder.md#an-unchanged-numerator-term-in-the-primitive-continuous-adjoint) I1–I16、I14a，以及同条目的 H1–H8、G7。不重证局部六层递推、通用筛法或 Euler 乘积收敛。这里新增的消费是：在同一份未限平方自由的原卷积上，同时汇总任意多个其他素因子的高重数第二分支，并控制其移动删因子。所有所引解析供应均作为前提；没有本仓完整解析 Lean 认证，也不主张文献原创性。

沿用 good 素理想及其 norm $q_a$，$p\nmid S$，$Q=q_p$，$u=1+\eta+it$，$\lambda_q=q_q^{5-6u}$，以及
$$
b(h)=\omega(h)\sum_{dn=h}\mu(d)V(q_d/D)W(q_n/N),\qquad K=DN.
$$
原 physical mask、ray section、正负方向的全族共轭及 profiles 全部保留。H2 的固定观察模数在本节记为 $\mathfrak M$；以下 $B$ 是随分支变化的平方自由 good 理想，不是该固定模数。所有原分支按 I1 的未约化 valuation 反演，只在原 numerator 上判断允许的选择。

#### 同一个原反演中的完整高重数族

先消去标记 $p$，允许它的第一分支及全部合法第二分支；在每个 $q\ne p$，若原 $v_q(ph)\ge6$ 则允许两支，否则只允许第一支。记这份实际分支族为 $\mathcal A_p(h)$。它的补集恰为至少一个 $q\ne p$ 在原 valuation $1,\ldots,4$ 选择第二分支的所有模式；valuation $5$ 没有第二分支。

选择第二分支的其他素因子唯一组成平方自由 $B$，满足 $(B,pS)=1$、$B^6\mid h$。原始六层步的总因子为 $\mu(B)q_B^{6-6u}$，分母仍来自原 $\mathcal v_u(ph)$。每个素因子只消去一次。原始高步不改变有限 ray character；标记 $p$ 的偶数低重数反射仍保留其 ray 置换，而该字符在其他素因子处的六次幂为 $1$。同样 $\chi_p(B^6)=1$，没有被舍去的交叉字符。

$p$ 取第一支时，写 $h=B^6m$，这一 $B$ 的确切贡献为
$$
\mu(B)\sum_m b(B^6m)\overline{
q_B^{6-6u}\mathcal v_u(pBm)
D_{\nu_{[B^6m]};S}(pm,u)}.
\tag{SH1}
$$
$p$ 取第二支且 $1\le j=v_p(ph)\le4$ 时，写 $h=p^{j-1}B^6m$、$p\nmid m$，贡献为
$$
-\mu(B)\sum_{p\nmid m}b(p^{j-1}B^6m)\overline{
\frac{q_B^{6-6u}\mathcal v_u(Bm)a_j^\nu(m,u)}{1-\lambda_p}
D_{\nu\epsilon_{p,j};S}(p^{4-j}m,u)}.
\tag{SH2}
$$
这里 $a_j^\nu$、$\epsilon_{p,j}$ 是 I1 的完整原因子，$\nu=\nu_{[p^{j-1}B^6m]}$；奇数 Gauss 相位未改成绝对值。所有 $j\ge6$ 的 $p$ 第二支一次写为
$$
-\mu(B)\sum_m b(p^5B^6m)\overline{
q_B^{6-6u}Q^{6-6u}\mathcal v_u(pBm)
D_{\nu_{[p^5B^6m]};S}(m,u)}.
\tag{SH3}
$$
SH3 的 $m$ 在 $p$ 处不受限。这里使用原始六层恒等式，不把 valuation 约化模 $6$，也不以 residual theta 的周期性代替它。各式都在原系数的有限支撑上求和。

#### 原卷积分解与每个分母恰好一次

对于 SH1，原变量准确分解为
$$
d=Ed_0,\qquad n=(B^6/E)n_0,\qquad E\mid B,\quad(d_0,B)=1,
$$
$$
D_E=D/q_E,\qquad N_E=Nq_E/q_B^6,\qquad K_B=D_EN_E=K/q_B^6,
\qquad \mu(d)=\mu(E)\mu(d_0).
\tag{SH4}
$$
非零 Möbius 系数强迫 $d$ 平方自由，故 $E=\gcd(d,B)$ 唯一，给出原卷积的双射分解。$n_0$ 在 $B$ 处不受限，且没有另加 $(d_0,n_0)=1$。SH2 再按 I14 写 $d_0=p^ed_1$、$n_0=p^{j-1-e}n_1$，$0\le e\le\min(1,j-1)$、$p\nmid d_1n_1$。SH3 按 I14a 写 $d_0=p^ed_1$、$n_0=p^{5-e}n_1$，$e=0,1$、$p\nmid d_1$，而 $n_1$ 在 $p$ 处不受限。两份符号 $\mu(E)$、$\mu(p^e)$ 均保留。

由 I1 的 $\mathcal v_u=1*z_u$，即使 $B$ 与 $m$ 重叠，也有
$$
\mathcal v_u(Bm)=P_B(u)
\sum_{\substack{g\mid m\\(g,B)=1}}z_u(g),\qquad
P_B(u)=\prod_{q\mid B}(1-\lambda_q)^{-1}.
\tag{SH5}
$$
SH1、SH3 将这里的 $m$ 换成 $pm$。固定 $\eta>0$ 后，$|P_B(u)|\ll_\eta1$ 一致成立，因为 $|\lambda_q|=q_q^{-1-6\eta}$。每个 $B$ 素因子的分母只出现一次，不能在 $g$-和中再保留同一局部因子。另有 $|q_B^{6-6u}|=q_B^{-6\eta}$；其复相位在估计前保留。

原 mask 与 section 经 $h=B^6m$、$p^{j-1}B^6m$ 或 $p^5B^6m$ 运输。$B$ 模 $\mathfrak M$ 为单位，所以仍只涉及原固定有限函数族。SH2 的新 Fourier 变量为 $z=p^{4-j}m$，对应原 $h=B^6p^{2j-5}z$；完整过滤系数仍为 $\phi(z)t_u(z)$。移动 $B$ 仅删算术 $d,g$ 因子，不增加自守形式的坏素排除或 level。

#### 移动删因子的一致控制

在 I5–I7、I12–I14 的底层 pointwise 证明处使用 SH5，而不把平衡区间上的 I16 外推到 $K_B,D_E$。展开只取实际剩余 numerator 的 $g$ 约数，保留全部有限 Euler 和及极点尾项。

I6 中写 $g=eg_0$、$e\mid a$、$(g_0,a)=1$。I7 的 $a=pd_0$ 或 $p^2e_0$ 以及 I14 的 $a=d_1$ 都与 $B$ 互素；故所有 $e\mid a$ 保留，只将 $g_0$ 限制为避开 $B$。除数 Cauchy 系数范数、large-$g$ 及有限 polar-tail 的绝对 majorant 均不增加。$P_B$ 一致有界，原 $p$ 的重叠仍按 I7、I14、I14a 支付。固定 cusp 族、两个 cusp 指数及其 $\eta$ 范围不变。

主项只将 $Z_u$ 换为
$$
Z_u^B=\prod_{\substack{q\notin S\\q\nmid B}}
\left(1+\frac{z_u(q)}{q_q}\right),
$$
同时保留 $P_B$。因为 $(a,B)=1$，原 $v_u(a)$ 不变。这个主项表达仍由 I6 的有限 Euler 与 polar-tail 估计支持，不是把有限总表达式无偿换成无限乘积。

Möbius 主项中的 $(d_0,B)=1$，相对于原固定字符 Dirichlet 级数，准确增加
$$
M_B(s,u,\xi)=\prod_{q\mid B}
\left(1-v_u(q)\xi(q)q_q^{-s}\right)^{-1}
\ll_{\sigma,\theta}q_B^\theta,
\quad \Re s\ge\sigma>7/8,\quad\theta>0.
\tag{SH6}
$$
确实，原局部式给出
$$
|v_u(q)|\le
\left[1-q_q^{-1-6\eta}(1-q_q^{-1})\right]^{-1}.
$$
Good 素 norm 至少为 $7$，所以每个 $|v_u(q)|q_q^{-\sigma}$ 一致小于 $1$，并趋于 $0$。对固定 $\theta>0$，充分大的 $q$ 满足
$$
-\log\left(1-|v_u(q)|q_q^{-\sigma}\right)\le\theta\log q_q;
$$
有限个较小素因子只给固定乘积。这证明非零性和 SH6，且对 spectral $t$、固定 ray 字符族一致。原 reciprocal-$L$ 成本仍归同一包络，没有引入 growing-character 无零假设；$p$ 的删因子与 $B$ 不相交。

所以每个实际 $(B,E)$ 分支可在 $K'=K_B,D'=D_E$ 调用原底层 I7 或 I14、I14a，仅增加 $q_B^\theta$。令 $\mathcal N_H$ 为一次固定的共同 profile、Mellin、cusp 和 reciprocal-$L$ 包络。Profiles $V,W$ 只按 SH4 精确改长度，不随 $B$ 或行重新优化。

只对非空支撑使用估计。其 $D',N'$ 至少为原 annular 支撑给出的固定正常数；再提取 $p$ 后，每个实际非空 sector 的 $D'/Q^e$、$N'/Q^k$ 也满足这一条件。固定 annular enlargement 处理有界边界。因此不要求每个 $B$ 都有 $N_E/Q^5\ge1$：某个 $e=0$ 高-$p$ sector 可以为空，而非空 $e=1$ sector 使用自身的 $N_E/Q^4$。这些底层 pointwise 估计无需最终平衡条件；平衡条件只在恢复原 $K,D,N,L$ 后施加。

#### 汇总全部实际分支

写 $x=q_B$、$y=q_E$。除共同因子 $(KL)^\varepsilon(1+|t|)^A\mathcal N_Hx^\theta$ 及有利的外部 $x^{-6\eta}$ 外，SH1 的界为
$$
KD^{-1/8}x^{-6}y^{1/8}
+K^{5/12}D^{2/3}Q^{7/12}x^{-5/2}y^{-2/3}
+K^{5/12+\eta}DQ^{-7/12+\eta}x^{-5/2-6\eta}y^{-1}.
\tag{SH7}
$$
SH2、SH3 的全部 $p$ 第二分支合计为
$$
(K/Q)x^{-6}
+K^{5/12+\eta}DQ^{11/4+12\eta}x^{-5/2-6\eta}y^{-1}.
\tag{SH8}
$$
这里直接使用各 sector 的 I14、I14a，而非其平衡推论。$D_E,Q$ 在非空支撑上的固定正下界使高-$p$ 两项被 SH8 吸收；空 sector 为零。局部有限乘积与除数小幂一并纳入 $\theta$，内部损失先于最终 $\varepsilon$ 选择。

这些数值质量对全部平方自由 $B$、$E\mid B$ 一致可和。例如
$$
\sum_{B\ {\rm sf}}q_B^{-6+\theta}\sum_{E\mid B}q_E^{1/8}
=\prod_q\left[1+q_q^{-6+\theta}(1+q_q^{1/8})\right]<\infty,
$$
$$
\sum_{B\ {\rm sf}}q_B^{-5/2+\theta}\sum_{E\mid B}q_E^{-2/3}
=\prod_q\left[1+q_q^{-5/2+\theta}(1+q_q^{-2/3})\right]<\infty.
$$
其余内和权为 $1$ 或 $q_E^{-1}$，同样在任意固定 $0<\theta<1/4$ 下收敛。保留 $(B,pS)=1$ 只减小上界。先在同一原系数上将有限实际分支作 coherent 求和，再用三角不等式和这些质量；只把正 majorant 扩成无限 Euler 乘积，没有增加实际模式，也没有用分别可达的最优系数替换共同系数。

令 $C_p^H(t)$ 为 $\mathcal A_p(h)$ 对原 $b(h)$ 的全部贡献，则
$$
\begin{aligned}
|C_p^H(t)|\ll{}&(KL)^\varepsilon(1+|t|)^A\mathcal N_H\bigl[
KD^{-1/8}+K^{5/12}D^{2/3}Q^{7/12}\\
&+K^{5/12+\eta}DQ^{-7/12+\eta}
+K/Q+K^{5/12+\eta}DQ^{11/4+12\eta}\bigr].
\end{aligned}
\tag{SH9}
$$
这包含所有同时 $B\ne1$ 选择，不限所选素因子数目；仅取该新增子族时同一界也成立。它消费的是原未限平方自由的列、全部原符号及掩码。

#### 原 Mellin 与实际 inverse Gram 的共同消费

将 SH9 配入原 adjoint 的 row Mellin profile，记所得向量为 $e^H$。保留原 $U^\eta$ 及全部固定多项式高度成本，仍用 G7 的实际 $G_P^{-1}$。有限项平方的交叉项用固定常数吸收，原素 annulus $L\le Q<2L$ 的计数给出
$$
\begin{aligned}
Q_H:=(e^H)^*G_P^{-1}e^H
\ll{}&(UKL)^\varepsilon\mathcal N_H^2U^{2\eta}\bigl[
K^2D^{-1/4}L+K^{5/6}D^{4/3}L^{13/6}\\
&+K^{5/6+2\eta}D^2L^{-1/6+2\eta}
+K^2/L+K^{5/6+2\eta}D^2L^{13/2+24\eta}\bigr].
\end{aligned}
\tag{SH10}
$$
没有把实际 Gram 换成正 label 形式。只在原 I16 的窄区间
$$
U\asymp K,\qquad K^{1/2}\le D\le K^{1/2}L^{1/6-\delta},\qquad
0<\delta<1/6,
$$
$$
L=K^\ell,\quad0<\ell<\frac1{41-12\delta},\qquad
r_{\ell,\delta}=\frac16-\left(\frac{41}6-2\delta\right)\ell>0
$$
施加原 spectral 允许的固定选择
$$
0<\eta<\min\left\{
\frac{1/8-\ell}{32},\frac\ell8,
\frac{r_{\ell,\delta}}{8+48\ell}\right\}.
$$
于是 I9 与 I16 的两份节省在同一原参数上共同给出
$$
Q_H\ll K^{2-\zeta_H+\varepsilon}\mathcal N_H^2,
\qquad
\zeta_H=\min\left\{\frac{1/8-\ell}{2},\frac\ell2,
\frac{r_{\ell,\delta}}2\right\}>0.
\tag{SH11}
$$
对有界的原显式包络及充分小 $\varepsilon$，H8 与 SH11 共同控制 $w+e^H$ 的实际二次型为 $o(K^2)$。这里只支付已指定的完整高重数分支族。

完整 primitive continuous 向量仍准确分成 $e^H+e^{\rm low}$；后者包含至少一个 $q\ne p$ 在原 valuation $1,\ldots,4$ 的第二分支，其余 $p$ 或高重数选择仍可同时存在。下一节进一步控制原 valuation $4$ 的同时选择；原 valuation $1,2,3$ 的剩余模式及其跨素数 coherent 耦合仍未支付。完整 projection／complement、其他原长度与高度、原 growing-height 包络、F4 transfer，以及原固定 $\eta_{\rm R}$ 的 signed Robin restoration 也仍未支付。SH11 不供应区间外统一界，不证明 RH 或全部 $n>5040$ 的严格 Robin 不等式。FIB 五模式、四相与收缩区间仍作为来源和运输语言复用，不替代这些未证估计。

### Coherent valuation-four and high branches

本节为 `repo-derived` 的更大原系数联合应用，沿用 SH1–SH11、I1–I16、I14a、H1–H8、G7 及其解析前提。新增消费包括任意多个原 valuation $4$ 的其他素因子同时取第二分支，允许它们与全部高重数分支混合，并保留标记 $p$ 的两种合法选择。所用原始局部反演、有限 $216$ 个 ray 字符、固定 cusp 理论及通用均值均为既有输入；不主张文献原创性或本仓完整解析 Lean 认证。

#### 原重数四的复合相位

令 $A$ 为所选原 valuation $4$ 素因子的平方自由乘积，$B$ 为所选原 valuation 至少 $6$ 素因子的平方自由乘积，要求 $(A,BpS)=1$、$(B,pS)=1$。记 $x=q_A$、$z=q_B$，以及
$$
\epsilon_A(c)=\prod_{q\mid A}R(q,c)^5,
\qquad \chi_A=\prod_{q\mid A}\chi_q,
\qquad \gamma_5(A)=x^{-1/2}g_5(1,A).
$$
对原 numerator $A^4k$、$(k,A)=1$，按原消去顺序取这些第二分支，其确切标量为
$$
\mu(A)\nu(A)^5\gamma_5(A)x^{9/2-5u}\chi_A(k)^{-5},
\qquad \nu\longmapsto\nu\epsilon_A.
\tag{VF1}
$$
这不是假设各局部操作交换。若 $q$ 在 $r$ 之前，原 $r^4$ 与后续 ray 改变给出成对因子
$$
\chi_q(r)^{-20}R(q,r)^{25}
=\chi_q(r)^4R(q,r)
=\chi_q(r)^5\chi_r(q)^5.
$$
最后一式由完整 sextic reciprocity 给出，恰好是 $g_5(1,qr)$ 的 CRT 乘积因子。沿原顺序归纳即得 VF1；所有 ray 乘积仍在原固定有限字符族中。$B^6$ 上的字符值为 $1$，故高分支另给原始因子 $\mu(B)z^{6-6u}$，不产生遗漏的交叉字符。

$p$ 取第一支时，写 $h=A^4B^6m$、$(m,A)=1$。一对 $(A,B)$ 的确切贡献为
$$
\mu(AB)\sum_{(m,A)=1}b(A^4B^6m)\overline{
\nu(A)^5\gamma_5(A)x^{9/2-5u}z^{6-6u}
\mathcal v_u(pABm)\chi_A(pm)^{-5}
D_{\nu\epsilon_A;S}(pm,u)}.
\tag{VF2}
$$
这里 $\nu=\nu_{[A^4B^6m]}$，按原 section indicator 分开；$m$ 在 $B$、$p$ 处不受限。

$p$ 取低重数第二支时，$1\le j\le4$，令 $k=j+1$、$s=4-j$、$b_j=5-j$，写 $h=p^{j-1}A^4B^6m$、$(m,pA)=1$。原 $p$ 标量为
$$
-\nu(p)^kQ^{j+1/2-ku}\gamma_k(p)
\chi_p(A)^{-4k}\chi_p(m)^{-k}.
$$
将其乘以
$$
\mu(AB)(\nu\epsilon_{p,j})(A)^5\gamma_5(A)
 x^{9/2-5u}z^{6-6u}\chi_A(p^sm)^{-5},
$$
再乘原分母 $\mathcal v_u(pABm)$ 与
$D_{\nu\epsilon_{p,j}\epsilon_A;S}(p^sm,u)$，按原外部共轭与系数求和，就是完整该支。所有 CRT 单位因子、minus sign 和 ray 运输都保留。

$p$ 取高重数第二支时，写 $h=p^5A^4B^6m$、$(m,A)=1$，$m$ 在 $p$ 处不受限。使用 VF2 的 $A,B$ 标量，将 $\chi_A(pm)^{-5}D(pm,u)$ 换成 $\chi_A(m)^{-5}D(m,u)$，并乘 $-Q^{6-6u}$；原分母仍为 $\mathcal v_u(pABm)$，原 section 为 $\nu_{[p^5A^4B^6m]}$。这一次包含全部原 $v_p(ph)\ge6$，不约化 raw valuation；$j=5$ 仍无第二支。

#### 共同原卷积与删因子

原变量准确分解为
$$
d=EFd_0,\qquad n=(A^4/E)(B^6/F)n_0,
\qquad E\mid A,\ F\mid B,
$$
$$
(d_0,AB)=1,\quad(n_0,A)=1,\qquad
D'=\frac D{q_Eq_F},\quad N'=\frac{Nq_Eq_F}{x^4z^6},\quad
K'=D'N'=\frac K{x^4z^6}.
\tag{VF3}
$$
$E=\gcd(d,A)$、$F=\gcd(d,B)$ 唯一，原符号是 $\mu(E)\mu(F)\mu(d_0)$。$n_0$ 在 $B$ 处不受限；没有额外的 $(d_0,n_0)=1$。再按 I14、I14a 提取各 $p$-sector 的原 $e=0,1$ 因子，保留自身实际长度。空支撑为零，非空 sector 按固定 annular enlargement 处理，不能对全部 $A,B$ 假设 $N'/Q^5\ge1$。

因 $(m,A)=1$，包括 $B\mid m$ 或 $p\mid m$ 的情形都有
$$
\mathcal v_u(pABm)=P_{AB}(u)
\sum_{\substack{g\mid pm\\(g,AB)=1}}z_u(g),
\qquad P_{AB}=\prod_{q\mid AB}(1-\lambda_q)^{-1}\ll_\eta1.
\tag{VF4}
$$
低-$p$ 支将 $pm$ 换成 $m$，并保留原单独的 $p$ 分母。每个局部因子只计一次。原 H2 mask 经 $A^4B^6$ 和相应 $p$ 幂运输，仍只有固定观察模数 $\mathfrak M$ 上的有限函数族。下面的增长字符是显式 Fourier mark，不是新加的自守坏素排除。

#### 复合标记的有限变换

定义零延拓 $\psi_A(w)=\chi_A(w)^{-5}$，以及
$$
\tau_A=\sum_{v\bmod A}\chi_A(v)^{-5}e(-v/A)
=\overline{g_5(1,A)},\qquad
\widehat\psi_A(v)=\frac{\tau_A}{x}\chi_A(v)^5\mathbf1_{(v,A)=1}.
$$
该字符在每个 $A$ 素因子处本原，故 $|\tau_A|=\sqrt x$、$\gamma_5(A)\tau_A=\sqrt x$，包括完整奇数 Gauss 相位。

对低-$p$ 支，模 $R_0=p^{b_j}A$ 取
$$
\psi_{p,A,j}(w)=\mathbf1_{p^s\mid w}
\chi_p(w/p^s)^{-k}\chi_A(w)^{-5}.
$$
CRT 给出确切的归一化 Fourier 系数
$$
\widehat\psi_{p,A,j}(v)=
\frac{\tau_{p,j}\tau_A}{Q^{b_j}x}
\chi_p(A)^{-k}\chi_A(p)^{-5b_j}
\chi_p(v)^k\chi_A(v)^5\mathbf1_{(v,pA)=1}.
\tag{VF5}
$$
对 $(a,pAS)=1$ 的平方自由 $a$，照 I10–I11 平均原固定过滤形式 $f(v/R_0+c/a,y)$。写 $c/a=h/r$、$r\mid a$、$R=R_0r$，原 multiplier $\chi_R(d)^{-1}$ 同时消去两个增长字符，因为 $k+b_j=6$、$5+1=6$。完整有限变换系数为
$$
\begin{aligned}
\mathcal A_{p,A,j,r}(n)={}&
\frac{\tau_{p,j}\tau_A}{Q^{b_j}x}
\chi_p(A)^{-k}\chi_A(p)^{-5b_j}
\chi_p(r)^{-k}\chi_A(r)^{-5}
 e(-n\overline R/\mathfrak M)\\
&\times c_{p^{b_j}}(n)c_A(n)
 g_{\overline\chi_r}
 (-n\overline{\mathfrak M}\,\overline{p^{b_j}A},r).
\end{aligned}
\tag{VF6}
$$
各逆元的模数与 I10 相同：$\overline R$ 模 $\mathfrak M$，$\overline{\mathfrak M}$ 模 $R$，$\overline{p^{b_j}A}$ 模 $r$。$r=1$ 的 Gauss 和为 $1$。保留
$$
c_A(n)=\prod_{q\mid A}(q_q\mathbf1_{q\mid n}-1)
$$
的全部中心与零值。仅有 $A$ 标记时删去 VF5–VF6 的 $p$ 因子并取 $R_0=A$。Cusp 分量为原 $f_{[R]}$，只依赖 $R\bmod\mathfrak M$；没有增长 level 的常数。

对仅有 $A$ 标记的 $p$ 第一支，外模数可以是 $pd_0$ 或 $p^2e_0$。后者不是平方自由，须保留完整 imprimitive $r$-Gauss 和。I4 和 H5 的 gcd 和给出
$$
\sum_{q_{n/\mathfrak M}\asymp H}
|t_{[R]}(n/\mathfrak M)g_r(\cdots)|
\ll(Hq_r)^\varepsilon(1+|t|)^C
q_r^{1/2}H^{1+\eta/2}.
$$
这替代了错误的点态平方自由 Gauss 界；有限矩阵变换仍适用于避开 $A$ 的 sixth-power-free $a$。$|c_A(n)|\le x$ 足够，不另作不相容的最优标记选择。

#### 两个极点与原 Möbius 主项

仅有 $A$ 标记时，乘回原 reflected scalar 后，两个完整 cusp multipliers 是
$$
\nu(A)^5\frac{\prod_{q\mid A}(1-q_q^{-1})}{\prod_{q\mid A}(1-\lambda_q)}
 x^{5-6u},\qquad
\nu(A)^5\frac{\prod_{q\mid A}(1-q_q^{-1})}{\prod_{q\mid A}(1-\lambda_q)}
 x^{3-4u},
$$
连同各自的原固定 cusp 分量。其模均为 $\ll_\eta x^{-1}$。联合 $p,A$ 标记同时保留 I11 的两个 $p$ cusp factors 与 VF1、VF5、VF6 的全部额外单位相位；不丢 outgoing constant。

在剩余 numerator 长度 $Y$、$(a,A)=1$ 上，VF6、I4 和上述 imprimitive Cauchy 估计给出含实际 $A$ scalar 的 unweighted error
$$
\ll(Yxq_a)^\varepsilon(1+|t|)^C
Y^{-\eta}x^{1-4\eta}q_a^{1/2+\eta}.
$$
有限 $g$ 和的 large-$g$ convexity tail 为
$$
\ll(Yxq_a)^\varepsilon(1+|t|)^C
\frac{x^{-1/2-5\eta}Y^{5/4-\eta/2}}{q_aG^{1+6\eta}}.
$$
取 $G=Y^{5/6}x^{-1}/q_a$，若 $G\ge1$，两项依次为
$$
Y^{5/12-31\eta/6}x^{1/2+\eta}q_a^{6\eta},
\qquad Y^{5/12-11\eta/2}x^{1/2+\eta}q_a^{6\eta}.
$$
实际非空支撑有 $q_a\ll Y$；$G<1$ 时直接计数原总支与两个 polar terms。故整个 weighted error 满足
$$
\operatorname{Err}_{A,\rm wt}
\ll(Yxq_a)^\varepsilon(1+|t|)^C
Y^{5/12+\eta}x^{1/2+12\eta}.
\tag{VF7}
$$
遗漏的有限 two-polar tail 为 $\ll Y(xq_a)^{-1}G^{-1-6\eta}$，由同一次 split 支付。两个主泛函仍是 $Y$、$Y^{2-u}$。因此才可用 I6 的 $Z_u^{AB}v_u(a)/q_a$ 表示主项；不能无偿把有限整个表达式替换为无限 Euler 乘积。

$r=1$ 的主项没有残留 $\chi_A(d_0)$：增长字符已经在 VF6 的 multiplier 中消去，$A$、$p$ 及原 mask 只选择原固定有限 cusp 和 ray 分量。因此仅有 $A$ 标记的 $p$ 第一支及高-$p$ 支仍可使用原固定字符 Möbius 位移 $D'^{-1/8}$。移动 $AB$ 的局部修正直接复用 SH6，只损失 $(xz)^\theta$；没有新的增长导子无零前提。

联合低-$p$ 与 $A$ 时，原 Fourier 长度为 $X=Q^sY$，模数为 $p^{b_j}Ar$。同一计算的 unweighted error 为 $Y^{-\eta}Q^{5-j-j\eta}x^{1-4\eta}q_a^{1/2+\eta}$，large-$g$ tail 则为 I13 的完整 $Q$ 因子乘 $x^{-1/2-5\eta}$。取
$$
G=Y^{5/6}Q^{-3+j/2}x^{-1}/q_a
$$
或在 $G<1$ 时直接计数，保留有限 two-polar tails，得到
$$
\operatorname{Err}_{p,A,j,\rm wt}
\ll(YQxq_a)^\varepsilon(1+|t|)^C
Y^{5/12+\eta}Q^{7/2-3j/4+12\eta}x^{1/2+12\eta}.
\tag{VF8}
$$
所有实际小于单位的长度与 dual scales 按原 fractional-lattice gap 和固定 annular enlargement 处理。两个标记的因子在同一个变换中相乘，未分别优化。

#### 全部四重数与高重数选择的共同消费

令 $\mathcal N_4$ 为一次固定的原 profile、Mellin、cusp、reciprocal-$L$ 包络。它不随 $(A,B,p)$ 重选。仅有 $A$ 标记的 $p$ 第一支在 $K',D'$ 上由 VF7 和原 Möbius 主项界给出
$$
\ll(KL)^\varepsilon(1+|t|)^C(xz)^\theta\mathcal N_4
\left(K'D'^{-1/8}/x
+K'^{5/12+\eta}D'Q^{5/12+\eta}x^{1/2+12\eta}\right),
$$
包括 $p\mid d$ 的原 imprimitive overlap。联合低-$p$ 支用 VF8，高-$p$ 支按 I14a 的实际缩长；全部 $p$ 选择合并被
$$
\ll(KL)^\varepsilon(1+|t|)^C(xz)^\theta\mathcal N_4
\left(K'D'^{-1/8}/x+K'/(Qx)
+K'^{5/12+\eta}D'Q^{11/4+12\eta}x^{1/2+12\eta}\right)
\tag{VF9}
$$
控制。有利的高-$B$ 因子 $z^{-6\eta}$ 可舍去。写 $y=q_E$、$v=q_F$，准确代回 VF3 后，三份数值质量为
$$
KD^{-1/8}x^{-5}z^{-6}(yv)^{1/8},\qquad
(K/Q)x^{-5}z^{-6},
$$
$$
K^{5/12+\eta}DQ^{11/4+12\eta}
 x^{-7/6+8\eta}z^{-5/2-6\eta}(yv)^{-1}.
$$
对全部互素平方自由 $A,B$、$E\mid A,F\mid B$，最后一份质量由
$$
\prod_{q\notin S}
\left[1+q_q^{-7/6+8\eta+\theta}(1+q_q^{-1})
+q_q^{-5/2-6\eta+\theta}(1+q_q^{-1})\right]<\infty
\tag{VF10}
$$
控制，只需 $8\eta+\theta<1/6$。原 SH11 已强制 $\eta<1/256$，固定 $0<\theta<1/16$ 即足够。前两份的 $x^{-5}z^{-6}$ 与除数权 $q^{1/8}$ 也可和。所有 branch-count、divisor 和有限局部小幂先在内部 $\theta$ 中分配，再选最终 $\varepsilon$。

先对原同一组系数的有限实际模式作 coherent 求和，再扩张正 majorant；不增加实际模式，不假设分别最优的向量可共同实现。将所有 $A\ne1$ 用 VF9–VF10 汇总，再加已付的 $A=1$ 族 SH9，所得完整新族仍满足 SH9 的 pointwise 右端，只将共同包络换为 $\mathcal N_4$。

记原 Mellin pairing 后的向量为 $e^{4,H}$。仍使用实际 $G_P^{-1}$，故 SH10 的完整五项二次型界同样成立。在 SH11 原较小平衡区间、原 spectrally permissible 固定 $\eta$ 及充分小损失下，
$$
(e^{4,H})^*G_P^{-1}e^{4,H}
\ll K^{2-\zeta_H+\varepsilon}\mathcal N_4^2.
$$
对有界的原显式共同成本包络，H8 因而控制 $w+e^{4,H}$ 的实际二次型为 $o(K^2)$。没有供应原全部 growing-height allowance 或其他长度上的界。

本节新族允许每个 $q\ne p$ 在原 valuation $4$ 或至少 $6$ 时任选两支，且包括 $p$ 的全部合法选择；相对于本节，完整 primitive continuous 向量的剩余部分包含至少一个其他素因子在原 valuation $1,2,3$ 的第二分支，其余选择可同时存在。[下一节](#joint-control-of-all-powerful-prime-reflection-choices)在明确的更小参数区间联合支付其中全部二重数、三重数选择，保留一重数分支及完整 projection／complement、其他原长度与高度、F4 transfer、signed Robin restoration 的缺口。本节估计不证明 RH 或全部 $n>5040$ 的严格 Robin 不等式。

### Joint control of all powerful-prime reflection choices

本节为 `repo-derived` 的原系数联合应用，沿用 VF1–VF10、SH1–SH11、I1–I16、I14a、H1–H8、G7 及其解析前提。控制的完整分支族允许每个 $q\ne p$ 在原 valuation $2,3,4$ 或至少 $6$ 时任选两支，并允许标记 $p$ 的全部合法选择；valuation $5$ 没有第二支。采用同一对阈值，把实际分支族分成小乘积部分与完整大乘积尾部，再回接原 Mellin 和实际 inverse Gram。局部反演、固定 cusp 理论及 generic 均方界均为既有输入，不主张文献原创性或本仓解析 Lean 认证。

#### 原始多重数、复合标记与共同系数

令 $A_j$、$j=2,3,4$ 是所选原 valuation $j$ 素因子的平方自由乘积，$B$ 是所选原 valuation 至少 $6$ 素因子的平方自由乘积。各集合互素并避开 $pS$。记 $x_j=q_{A_j}$、$z=q_B$，$k_j=j+1$、$s_j=4-j$、$b_j=5-j$。相同 $j$ 的复合反射在原 numerator $A_j^jk$ 上给出
$$
\mu(A_j)\nu(A_j)^{k_j}\gamma_{k_j}(A_j)
 x_j^{j+1/2-k_ju}\chi_{A_j}(k)^{-k_j},\qquad
A_j^jk\longmapsto A_j^{s_j}k,\quad\nu\longmapsto\nu\epsilon_{A_j,j}.
\tag{PR1}
$$
若 $q$ 在 $r$ 之前，同类型成对因子为 $\chi_q(r)^{-jk_j}\chi_r(q)^{-s_jk_j}R(q,r)^{k_j^2}$，由完整 reciprocity 等于 $\chi_q(r)^{k_j}\chi_r(q)^{k_j}$，恰为 $\gamma_{k_j}(qr)$ 的 CRT 因子。对不同类型 $j,l$ 交换两个指定第二分支，系数比中的字符指数为 $6(j-l)$、reciprocity 符号指数为 $(2j-4)k_l$，均为平凡值。这证明可按 $2,3,4$ 分组；没有预设局部 extraction 交换。高六层步的交叉字符值为 $1$。

$p$ 第一支取 $t=1,\nu_0=\nu$；低重数第二支取 $t=4-j_p,\nu_0=\nu\epsilon_{p,j_p}$；高重数第二支取 $t=0,\nu_0=\nu$。令 $\nu_j=\nu_0\prod_{i<j}\epsilon_{A_i,i}$，$r_j=p^tm\prod_{i<j}A_i^{s_i}\prod_{i>j}A_i^i$，则其他素因子的确切标量为
$$
\mathcal L=\mu(B)z^{6-6u}\prod_{j=2}^4
\left[\mu(A_j)\nu_j(A_j)^{k_j}\gamma_{k_j}(A_j)
 x_j^{j+1/2-k_ju}\chi_{A_j}(r_j)^{-k_j}\right].
\tag{PR2}
$$
将其乘原 $\mathcal v_u(pA_2A_3A_4Bm)$ 和 $D_{\nu_0\prod_j\epsilon_{A_j,j};S}(p^tA_2^2A_3m,u)$，就是对应 full-series 因子。$p$ 第一支标量为 $1$；低-$p$ 支仍乘 I1 的完整 $-\nu(p)^kQ^{j_p+1/2-ku}\gamma_k(p)\chi_p(\prod_jA_j^jm)^{-k}$、$k=j_p+1$；高-$p$ 支乘 $-Q^{6-6u}$。原 $h$ 依次为 $\prod_jA_j^jB^6m$、$p^{j_p-1}\prod_jA_j^jB^6m$、$p^5\prod_jA_j^jB^6m$；$(m,A_2A_3A_4)=1$，仅低-$p$ 支另有 $p\nmid m$。原 $b(h)$、外部共轭、mask 与 section indicator 全部保留，$\nu$ 始终来自原 $h$。

原卷积有双射分解
$$
d=(\prod_jE_j)Fd_0,\quad n=\prod_j(A_j^j/E_j)(B^6/F)n_0,
\quad E_j\mid A_j,\ F\mid B,
$$
$$
(d_0,A_2A_3A_4B)=1,\quad(n_0,A_2A_3A_4)=1,\quad
D'=\frac D{(\prod_jq_{E_j})q_F},\quad
N'=\frac{N(\prod_jq_{E_j})q_F}{(\prod_jx_j^j)z^6},\quad K'=\frac K{(\prod_jx_j^j)z^6}.
\tag{PR3}
$$
各原 Möbius 符号保留，$n_0$ 在 $B$ 处不受限，不添加 $(d_0,n_0)=1$。各 $p$-sector 按自身实际支撑缩长。令 $T=A_2A_3A_4B$，则原分母为 $P_T\sum_{g\mid pm,(g,T)=1}z_u(g)$，$P_T=\prod_{q\mid T}(1-\lambda_q)^{-1}\ll_\eta1$；低-$p$ 支将 $pm$ 换成 $m$ 并保留单独 $p$ 分母。每个局部因子只计一次。原 $h$ 的 mask 运输仍发生在固定模数 $\mathfrak M$ 上；ray 乘积仍在原固定 $216$ 个分量中。

对块 $(P_i,s_i,b_i,k_i)=(A_j,4-j,5-j,j+1)$，低-$p$ 时再加入 $(p,4-j_p,5-j_p,j_p+1)$，略去单位块，取
$$
R_0=\prod_iP_i^{b_i},\quad\tau_i=\overline{g_{k_i}(1,P_i)},\quad
\psi(w)=\prod_i\mathbf1_{P_i^{s_i}\mid w}\chi_{P_i}(w/P_i^{s_i})^{-k_i}.
$$
从 PR2 抽出的额外单位因子是 $\prod_{j<i}\chi_{A_j}(A_i)^{-k_j(i-s_i)}$，低-$p$ 时再乘 $\prod_j\chi_p(A_j)^{-k_p(j-s_j)}$；它们与 $m,d_0$ 无关，必须同原 $\nu_j$、Gauss 相位一起保留。CRT 精确给出
$$
\widehat\psi(v)=\mathcal K\prod_i\frac{\tau_i}{q_{P_i}^{b_i}}
\prod_i\chi_{P_i}(v)^{k_i}\mathbf1_{(v,\prod_iP_i)=1},
\qquad\mathcal K=\prod_i\chi_{P_i}(R_0/P_i^{b_i})^{-k_i}.
$$
原平移约化中 $r\mid a$ 的完整有限变换系数是
$$
\mathcal K\prod_i\left[\frac{\tau_i}{q_{P_i}^{b_i}}\chi_{P_i}(r)^{-k_i}\right]
 e(-n\overline{R_0r}/\mathfrak M)c_{R_0}(n)
 g_{\overline\chi_r}(-n\overline{\mathfrak M}\,\overline{R_0},r).
\tag{PR4}
$$
逆元的角色与 VF6 一致。每个 $k_i+b_i=6$，原 multiplier 消去全部增长字符；保留 $c_{A_2^3},c_{A_3^2},c_{A_4},c_{p^{b_p}}$ 的中心与零值。$|\tau_i|=\sqrt{q_{P_i}}$、$\gamma_{k_i}(P_i)\tau_i=\sqrt{q_{P_i}}$ 包括奇数 Gauss 相位。Cusp 分量只依赖 $R_0r\bmod\mathfrak M$。$p$ 第一支的 $a=p^2e_0$ 仍用 VF6 的完整 imprimitive Gauss 和及 I4／H5 gcd-Cauchy，不能使用平方自由点态界。

#### 小乘积区域的主项与误差

Fourier 长度为 $X=(\prod_jx_j^{s_j})Y$，低-$p$ 时另乘 $Q^{4-j_p}$。含实际 reflected scalar 的 unweighted error 为 $Y^{-\eta}Q^{5-j_p-j_p\eta}\prod_jx_j^{5-j-j\eta}q_a^{1/2+\eta}$；其 convexity 大-$g$ 尾部为 I13 的完整 $Q$ 因子乘
$$
\frac{\prod_jx_j^{1/2-j/4-(3+j/2)\eta}Y^{5/4-\eta/2}}{q_aG^{1+6\eta}}.
$$
取 $G=Y^{5/6}Q^{-3+j_p/2}\prod_jx_j^{-3+j/2}/q_a$，$G\ge1$ 时按 VF7–VF8 同一有限 $g$ split，得到
$$
\operatorname{Err}_{\rm wt}\ll(YQq_a\prod_jx_j)^\varepsilon(1+|t|)^J
Y^{5/12+\eta}Q^{7/2-3j_p/4+12\eta}\prod_jx_j^{7/2-3j/4+12\eta}.
\tag{PR5}
$$
有限 two-polar tail $\ll Y[Q(\prod_jx_j)q_a]^{-1}G^{-1-6\eta}$ 同时支付；$G<1$ 则直接计数原支与两个 polar terms。非低-$p$ 支删去这些 $Q$ 因子。每块两个极点的 norm powers 为 $x_j^{5-6u},x_j^{j-1-ju}$，模均至多 $x_j^{-1}$。付清有限尾项后，主项才用 $Z_u^Tv_u(a)/q_a$；PR4 的 $r=1$ 无增长 $\chi_{A_j}(d_0)$，故可复用原固定字符 Möbius 位移 $D'^{-1/8}$ 及 SH6 的移动删因子小幂。全部非空、有界 subunit 和 dual scales 仍按原 annular enlargement／lattice gap 处理。

令 $\mathcal N_{\rm pow}$ 是一次固定的原 profile、cusp、Mellin、reciprocal-$L$ 与 generic mean 成本包络。合并所有合法 $p$ 支，PR3 的一份原 sector 被
$$
(KL)^\varepsilon(1+|t|)^J\mathcal N_{\rm pow}(z\prod_jx_j)^\theta
\left[\frac{K'D'^{-1/8}}{\prod_jx_j}+\frac{K'}{Q\prod_jx_j}
+K'^{5/12+\eta}D'Q^{11/4+12\eta}\prod_jx_j^{7/2-3j/4+12\eta}\right]
$$
控制。主项质量 $\prod_jx_j^{-j-1}z^{-6}$ 及原除数权 $1/8$ 或 $1$ 对全部集合可和。误差的准确原变量质量为
$$
\frac{x_2^{7/6+10\eta}x_3^{9\eta}x_4^{-7/6+8\eta}z^{-5/2-6\eta}}
{(\prod_jq_{E_j})q_F}.
$$
$A_4,B$ 的质量按 VF10 收敛。在共同区域 $x_2\le R_2,x_3\le R_3$，其余截断质量为 $\ll R_2^{13/6+10\eta+\varepsilon}R_3^{1+9\eta+\varepsilon}$。内部 $\theta$ 与除数小幂先于最终 $\varepsilon$ 选取。因此小区域的实际贡献满足
$$
|C_{p,\rm small}|\ll(KL)^\varepsilon(1+|t|)^J\mathcal N_{\rm pow}
\left[KD^{-1/8}+K/Q+K^{5/12+\eta}DQ^{11/4+12\eta}
R_2^{13/6+10\eta}R_3^{1+9\eta}\right].
\tag{PR6}
$$
已付的 $A_2=A_3=1$ 子族也可直接复用 VF／SH9，并保留 SH10 的完整原费用。

#### 同一实际系数的大乘积尾部

[Primitive-mean 源稿](https://rstation.ai/api/v1/papers/riemann_hypothesis_10/versions/2/download) Proposition 3 是 full $D$ 的均方供应。其 $B=1$ 情形直接消费为
$$
\sum_{q_n\asymp Y}|D_\nu(Hn,1+\eta+it)|^2
\ll(q_HY)^\varepsilon q_H^{1/2}Y(1+|t|)^6.
\tag{PR7}
$$
这里 $n$ 不限平方自由：写 $n=md^2$、$m$ 平方自由，$e=\gcd(m,\operatorname{rad}(Hd))$、$m=em_0$。原 Proposition 3 在 multiplier $Hd^2e$、长度 $Y/(q_d^2q_e)$ 上的费用为 $q_H^{1/2}Y/(q_d\sqrt{q_e})$。$e$ 的除数和为小幂，$d$ 的调和和为对数；实际有界 subunit 支撑按固定扩大处理。这是既有 full-series 均值的应用，没有把 primitive $H_\nu$ 的均值误用于 $D_\nu$。实际 $\nu_{[h]}$ 由固定有限分量最大值处理，只在这个正均方中扩大 mask 支撑。

原支撑 $q_h\asymp K$ 上，$|b(h)|\ll K^\varepsilon\mathcal N_{\rm pow}$。固定选中集合时，$m$ 长度为 $Y=K/(x_2^2x_3^3x_4^4z^6)$，第二 $p$ 支另按原 $Q^{j_p-1}$ 或 $Q^5$ 缩长。原 scalar 模至多 $\prod_jx_j^{-1/2}$，分母一致有界。对同一实际 pairing 使用 PR7，shift 为 $p^tA_2^2A_3$，Cauchy 给出
$$
|\operatorname{pair}_{A_2,A_3,A_4,B}|
\ll(KL)^\varepsilon(1+|t|)^J\mathcal N_{\rm pow}
KQ^{1/4}x_2^{-2}x_3^{-13/4}x_4^{-9/2}z^{-6}.
$$
低-$p$ 的 $Q$ 指数是 $(4-j_p)/4-1/2-(j_p-1)=3/2-5j_p/4\le1/4$，高-$p$ 为 $-5$，故同一界覆盖全部选择。未选原素因子仍在不受平方自由限制的 $m$ 中，未替换原系数或 profile。

小区域的补集先取 $x_2>R_2$，再取 $x_2\le R_2,x_3>R_3$。对有限实际模式求和，只把正 majorant 扩张到无限集合，得到
$$
|C_{p,\rm large}|\ll(KL)^\varepsilon(1+|t|)^J\mathcal N_{\rm pow}
KQ^{1/4}(R_2^{-1}+R_3^{-9/4}).
\tag{PR8}
$$
因为 $\sum_{x_2>R_2}x_2^{-2}\ll R_2^{-1}$、$\sum_{x_3>R_3}x_3^{-13/4}\ll R_3^{-9/4}$，其余质量均收敛。这里覆盖全部大乘积模式，且所有行、原 profiles 共用同一对阈值；没有组合分别最优的系数。

#### 两个阈值共同支付原二次型

记全部指定模式经原 Mellin 后的向量为 $e^{\rm pow}$。保留原 $U^\eta$、实际 $G_P^{-1}$ 和 G7；小／大区域及已付子族的交叉项由固定有限和平方界支付。完整联合二次型满足
$$
\begin{aligned}
Q_{\rm pow}\ll{}&(UKL)^\varepsilon\mathcal N_{\rm pow}^2U^{2\eta}\bigl[
K^2D^{-1/4}L+K^{5/6}D^{4/3}L^{13/6}
+K^{5/6+2\eta}D^2L^{-1/6+2\eta}+K^2/L\\
&+K^{5/6+2\eta}D^2L^{13/2+24\eta}R_2^{13/3+20\eta}R_3^{2+18\eta}
+K^2L^{3/2}(R_2^{-2}+R_3^{-9/2})\bigr].
\end{aligned}
\tag{PR9}
$$
保持原 $U\asymp K$、$K^{1/2}\le D\le K^{1/2}L^{1/6-\delta}$、$0<\delta<1/6$，取 $L=K^\ell$、$0<\ell<2/(129-24\delta)$。设
$$
r=\frac16-\left(\frac{41}6-2\delta\right)\ell,\quad
c=\frac{36r-141\ell}{130}=\frac{3[2-(129-24\delta)\ell]}{130}>0,
$$
$$
v=c+3\ell/2,\qquad a_2=v/2,\quad a_3=2v/9,\quad R_2=K^{a_2},\quad R_3=K^{a_3}.
$$
同一原参数上准确有 $r-(13/3)a_2-2a_3=2a_2-3\ell/2=(9/2)a_3-3\ell/2=c$。选择同一个 spectral 允许的固定
$$
0<\eta<\min\left\{\frac{1/8-\ell}{32},\frac\ell8,
\frac{c}{2(4+24\ell+20a_2+18a_3)}\right\}.
$$
这蕴含 SH11 的原限制和 $\eta<1/256$，可为 VF10 的可和性分配内部 $\theta$。新小区域的损失为 $(4+24\ell+20a_2+18a_3)\eta<c/2$，两个大区域各损失 $2\eta<c/2$。其他 SH10 裕度不变，于是
$$
Q_{\rm pow}\ll K^{2-\zeta_{\rm pow}+\varepsilon}\mathcal N_{\rm pow}^2,
\qquad\zeta_{\rm pow}=\min\{(1/8-\ell)/2,\ell/2,c/2\}>0.
\tag{PR10}
$$
对有界的原共同成本包络及充分小损失，H8 控制 $w+e^{\rm pow}$ 的实际二次型为 $o(K^2)$。全部所选 powerful 素因子的同时反射都已在此指定族中求和，不限于阈值内。完整 primitive continuous 向量的确切剩余模式，含至少一个其他素因子在原 valuation $1$ 的第二分支；其余所有 $p$、二重数、三重数、四重数及高重数选择仍可同时出现。该一重数剩余族的[原系数临界带定位](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#454-原系数一重数反射的临界带定位)在更小参数区间、同一共同成本下联合控制 P、S、O 补集，留下定义 454.1 的临界带 T；其[共轭公共因子细分](../../docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md#455-临界反射族的共轭公共因子细分)在同一参数下进一步控制公共部分范数大于 $R_1$ 的全部模式，剩余族为定理 455.2 的 $\mathrm T_{\rm rat}$，并必须含非单位未配对分裂核心；完整 projection／complement、其他原长度与高度、原 growing-height allowance、F4 transfer 及原固定指数的 signed Robin restoration 仍未支付。这份条件联合估计不证明 RH 或全部 $n>5040$ 的严格 Robin 不等式。

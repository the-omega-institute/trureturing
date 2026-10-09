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

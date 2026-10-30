# Xu–Zhao 三变量柯西系数的最终符号

## 1. 正整数组合、普通系数与来源

**定义 1.1（源函数与去零点归一化）。** 设 $d\ge1$，$\boldsymbol{k}=(k_1,\ldots,k_d)\in\mathbb Z_{\ge1}^d$。在 $|z|<1$ 上置

$$
\operatorname{Li}_{\boldsymbol{k}}(z)
 =\sum_{n_1>\cdots>n_d>0}
   \frac{z^{n_1}}{n_1^{k_1}\cdots n_d^{k_d}},\qquad
 F_{\boldsymbol{k}}(z)=z^{-d}\operatorname{Li}_{\boldsymbol{k}}(z).
$$

在零点取可去值。对任意正整数组合 $\boldsymbol{s}$，记

$$
H_{\boldsymbol{s}}(N)
 =\sum_{N\ge m_1>\cdots>m_r>0}
   \frac1{m_1^{s_1}\cdots m_r^{s_r}},\qquad
H_{\varnothing}(N)=1.
$$

于是 $F_{\boldsymbol{k}}(z)=\sum_{m\ge0}f_mz^m$，其中

$$
f_m=\frac{H_{(k_2,\ldots,k_d)}(m+d-1)}{(m+d)^{k_1}}>0,
\qquad
f_0=\prod_{i=1}^d(d+1-i)^{-k_i}.
$$

严格正性包括 $d=1$：此时分子为 $1$。一般情形的分子包含严格指标 $(d-1,\ldots,1)$；$m=0$ 时恰好只有这一组指标。

**定义 1.2（普通三变量系数）。** 固定整数 $\ell\ge1$，对整数 $j\ge0$ 定义

$$
A(z)=F_{\boldsymbol{k}}(z)^{-\ell},\qquad
C_n^{j;\boldsymbol{k};\ell}
 =[z^n](1-z)^{-j}A(z),\qquad a_n=C_n^{0;\boldsymbol{k};\ell}.
$$

这里 $[z^n]$ 是普通幂级数系数，解析函数的系数为其 $n$ 阶导数除以 $n!$。特别地

$$
C_0^{j;\boldsymbol{k};\ell}=f_0^{-\ell}
 =\left(\prod_{i=1}^d(d+1-i)^{k_i}\right)^\ell.
$$

若 $k_1>1$，称组合可容许，并记

$$
Z=\zeta(\boldsymbol{k})
 =\sum_{n_1>\cdots>n_d>0}\frac1{n_1^{k_1}\cdots n_d^{k_d}}>0.
$$

**约定 1.3（原始文献与所引解析命题）。** Ce Xu、Jianqiang Zhao，*Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*，arXiv:2609.11072v1，[HTML §1.3](https://arxiv.org/html/2609.11072v1#S1.SS3)、[PDF §1.3](https://arxiv.org/pdf/2609.11072v1)。定义 1.1–1.2 分别对应 HTML (7)–(8)、PDF (4)–(5)，包括零点常数项；它们没有指数生成函数中的额外 $n!$。原文 Conjecture 1.3 的最终符号问题是下文定理 4.1 的对象，不作为证明前提。原文 Theorems 1.1、8.2 与 Corollaries 5.2、8.4 给出对数及全一组合的相应已知情形，§9 讨论深度一、二的情形。

以下解析命题均指仓内 [Polylogarithm](https://github.com/the-omega-institute/trureturing/tree/13540e54dcb7e367c6799640ec15b707fcf2bb18/D5/S3/AnalyticClosure/Polylogarithm) 的该版本，命名空间前缀统一为 `D5.S3.AnalyticClosure.Polylogarithm`。引用 `CompositionDisk`、`CompositionBoundary`、`CompositionSlit`、`CompositionZeroFreeCollar`、`CompositionBanks` 及其私有解析引理时，参数对应始终为

$$
\mathrm{head}=k_1,\qquad
\mathrm{tail}=[k_2,\ldots,k_d],\qquad
\mathrm{depth}(\mathrm{tail})=d,
$$

各正整数按其值视为 $\mathbb N_+$。`CompositionDisk.H tail N` 恰为 $H_{(k_2,\ldots,k_d)}(N)$，`coefficient head tail m` 恰为 $f_m$。下文系数桥接、有限割线积分与重复求和的合成推导属于本卷的 `repo-derived` 内容；上述原文中的定义和特殊情形属于所引文献结果。

## 2. 实际分支及精确系数桥接

**定义 2.1（分支）。** 取主值 $\operatorname{Log}w$，$-\pi<\arg w<\pi$，并置

$$
\Omega=\mathbb C\setminus[1,\infty)
 =\{z:1-z\in\mathbb C\setminus(-\infty,0]\}.
$$

记 $L_{\boldsymbol{k}}(z)=\mathrm{CompositionContinuation.continued}\,[k_1,\ldots,k_d]\,z$。这是与定义 1.1 的圆盘级数相符的实际分支。其去零点归一化为

$$
\mathcal F(z)=
\begin{cases}L_{\boldsymbol{k}}(z)/z^d,&z\ne0,\\ f_0,&z=0.\end{cases}
$$

在其非零区域记 $\mathcal A=\mathcal F^{-\ell}$。因而对 $z\ne0$，$\mathcal A(z)=(z^d/L_{\boldsymbol{k}}(z))^\ell$，而 $\mathcal A(0)=f_0^{-\ell}$；对商式在零点作总除法会给出错误的常数。

**定理 2.2（从严格源级数到形式倒数的对应）。** 对定义 1.1–1.2 的全部参数，$A$ 在 $|z|<1$ 全纯。定义

$$
u_m=\sum_{m_1+\cdots+m_\ell=m}\prod_{i=1}^\ell f_{m_i}.
$$

则 $a_n$ 正是下列形式逆级数的唯一系数：

$$
a_0=u_0^{-1}=f_0^{-\ell},\qquad
 a_n=-u_0^{-1}\sum_{m=1}^nu_ma_{n-m}\quad(n\ge1).
$$

对每个整数 $j\ge1$，精确地有

$$
C_n^{j;\boldsymbol{k};\ell}
 =\sum_{m=0}^n\binom{n-m+j-1}{j-1}a_m,\qquad
C_n^{j+1;\boldsymbol{k};\ell}=\sum_{m=0}^n C_m^{j;\boldsymbol{k};\ell}.
$$

证明。`CompositionDisk.source_coefficient_control` 对所有正整数列表 $s$ 与 $N\ge0$ 给出

$$
0\le H_s(N)\le N^{|s|},\quad
N<|s|\Rightarrow H_s(N)=0,\quad
N\ge|s|\Rightarrow H_s(N)>0,
$$

以及 $H_s(|s|)=\mathrm{leading}(s)$；这里 $|s|$ 表示列表长度。`source_series head tail` 同时给出每个 $f_m>0$、归一化函数零点值 $\mathrm{leading}([k_1,\ldots,k_d])=f_0$、每个 $|z|<1$ 的绝对收敛、圆盘全纯性、$z^dF_{\boldsymbol{k}}=\mathrm{source}([k_1,\ldots,k_d])=\mathrm{strictNestedSeries}$，以及源函数零点阶数恰为 $d$。因此这里的 $f_m$、$F$ 与源级数逐一相同，不涉及指标反转或深度幂的改变。

`CompositionZeroFreeCollar.result head tail` 对同一归一化函数给出圆盘内与 `CompositionDisk.normalized` 的相等性、在整个 $\Omega$ 上全纯性，以及某个 $R_0>1$ 满足

$$
 z\in\Omega,\quad |z|<R_0\quad\Longrightarrow\quad\mathcal F(z)\ne0.
$$

其 `normalizedContinuation` 正是定义 2.1 的 $\mathcal F$。故 $\mathcal A$ 在 $\Omega\cap\{|z|<R_0\}$ 全纯，并在单位圆盘等于 $A$。这只使用该组合的局部外延半径，不要求全割平面无零。

有限次乘法给出 $F^\ell$ 的系数 $u_m$，且 $u_0=f_0^\ell\ne0$。全纯恒等式 $F^\ell A=1$ 比较系数即为递推；反之该递推逐项唯一决定形式逆级数。再乘以绝对收敛的二项级数 $(1-z)^{-j}$ 得到卷积式；乘一次 $(1-z)^{-1}$ 得到重复求和式。所有这些系数都在普通幂级数环中计算。

**定理 2.3（同幂次的局部两岸数据与前导一界）。** 固定 $\boldsymbol{k}$ 与 $\ell$，置

$$
\lambda=\begin{cases}Z^{-\ell},&k_1>1,\\0,&k_1=1.\end{cases}
$$

存在 $0<\rho<1$，使 $L_{\boldsymbol{k}}$ 在 $\Omega\cap\{|z-1|\le\rho\}$ 非零，且 $\mathcal A(z)\to\lambda$ 当 $z\to1$、$z\in\Omega$。存在函数 $U,V$，分别连续于闭半圆盘

$$
K_+=\{|z-1|\le\rho,\ \operatorname{Im}z\ge0\},\qquad
K_-=\{|z-1|\le\rho,\ \operatorname{Im}z\le0\},
$$

在各自与 $\Omega$ 的交集中等于 $\mathcal A$，满足

$$
U(1)=V(1)=\lambda,\qquad V(z)=\overline{U(\overline z)}\quad(z\in K_-),
\qquad \operatorname{Im}U(1+t)<0\quad(0<t\le\rho).
$$

若 $k_1=1$，还存在 $D\ge1$、整数 $M\ge0$ 与 $r_*<1$，使

$$
0<F_{\boldsymbol{k}}(r)
 \le r^{-d}D\bigl(1+|\log(1-r)|\bigr)^M\qquad(r_*<r<1,\ r>0).
$$

证明。两岸及端点部分直接使用 `CompositionBanks.result head tail ell` 的完整结论，其中 $\ell$ 就是定义 1.2 的幂次。取 $\ell=1$ 的两岸符号后任意升幂并不能替代这一引用。该命题在全 $\Omega$ 内趋于 $1$ 的滤子上给出端点极限，且连续性包括两岸的 $t=0$ 与 $t=\rho$，不是只有逐条射线的边界值。

有关前导一部分，任意有限组合唯一分成 $(1^q,s)$：$s$ 为空或首项大于 $1$。若 $k_1=1$ 则 $q\ge1$。`CompositionBanksSourceInduction.composition_remainder_cases_of_controls` 取它实际证明中给出的全部控制输入：`CompositionBanksLeadingClosure.composition_continued_norm_bound`、`CompositionBanksOrdinaryTransport.ordinary_admissible_remainder_step`、`CompositionBanksLeadingClosure.leading_one_remainder_iterate` 与 `CompositionBanksLeadingTransport.split_leading_ones`，得到同一实际分支的余项二分。可容许情形有某些 $0<\eta<1$、$C\ge0$、$M\ge0$ 满足

$$
|L_{(h,s)}(1-w)-\zeta(h,s)|
 \le C|w|(1+|-\operatorname{Log}w|)^M\quad(h>1),
$$

前导一情形有实系数多项式 $P$，满足

$$
\deg P=q,\qquad [T^q]P(T)=\frac{Z_s}{q!}>0,\qquad
Z_s=\begin{cases}1,&s=\varnothing,\\\zeta(s),&s\ne\varnothing,\end{cases}
$$

以及

$$
|L_{(1^q,s)}(1-w)-P(-\operatorname{Log}w)|
 \le C|w|(1+|-\operatorname{Log}w|)^M.
$$

这两个余项界的域都是 $w\in\mathbb C\setminus(-\infty,0]$、$0<|w|<\eta$；常数依赖相应有限组合。可容许尾部的常数使用 `CompositionBoundary.result`，仅在其首项大于 $1$ 时调用；该结果给出严格多重和与 $\sum f_m$ 的收敛、相等、正性及归一化函数的径向极限。没有把它用于首项为 $1$ 的非可容许组合。

上述控制输入的源权重归纳分别降低首项或删除首个 $1$；前导一迭代允许每一个有限 $q$。其中 `leading_remainder_integral_identity` 的常数为各射线共同的实常数，`CompositionBanksIntegralControl.radial_majorant_integrable` 以 $a\ge0$、$N\ge1$ 保证

$$
\int_0^1 t^{N-1}(1+a-\log t)^M\,dt<\infty,
$$

`radial_div_uniform_bound` 与 `radial_one_sub_uniform_bound` 分别保留 $N\ge1$ 和 $|w|<1$ 的前提，后者保留 $(1-|w|)^{-1}$ 因子；`inner_arc_decay` 要求正的消失阶 $N\ge1$。因此这里引用的是完整的源权重归纳及其积分控制，不是以待证的余项界作为额外假设。全纯分支、共轭及普通首项的边界导数均使用 `CompositionSlit.result` 和 `actual_upper_bank_atlas` 的同一分支；主值上岸有 $-\operatorname{Log}(-t-i0)=-\log t+i\pi$。

前导一的多项式余项界，或其完整推论 `leading_one_continued_norm_bound_of_remainder`，给出 $|L_{\boldsymbol{k}}(1-w)|\le D(1+|-\operatorname{Log}w|)^{M'}$，其中 $M'=\max(M,q)$，可增大 $D$ 至至少 $1$。限制到实数 $w=1-r>0$，再除以 $r^d$ 就得到所述 $F$ 的界（将 $M'$ 记为 $M$）。正性来自定义 1.1 的正系数。因子 $r^{-d}$ 在此保留，不能把 $L$ 的界直接当成 $F$ 的界。

## 3. 有限割线的系数符号转移

**定理 3.1（归一化倒数的最终负系数）。** 对每个有限正整数组合 $\boldsymbol{k}$ 与整数 $\ell\ge1$，存在整数 $N\ge1$，使 $a_n<0$ 对所有 $n\ge N$ 成立。

证明。取定理 2.2 的 $R_0$ 与定理 2.3 的同幂次两岸数据，固定

$$
1<R<\min(R_0,1+\rho).
$$

以下只在 $|z|\le R$ 的有限范围变形。沿圆周 $|z|=R$，除正实交点外 $\mathcal A$ 全纯；交点 $z=R$ 的上下极限分别由 $U,V$ 给出。其邻域处于 $|z-1|<\rho$，两侧均有界。圆周其余部分是全纯域内的紧集。因此存在有限常数 $B$，控制整个圆周两侧的极限范数。

从正向小圆 $|z|=r<1$ 的柯西系数积分出发，把它扩为半径 $R$ 的圆周加上割线 $[1,R]$ 的两岸。先在割线两侧留正宽度，并在 $1$ 和 $R$ 留小的连接弧，取不经过 $0$ 的边界；被积函数为 $\mathcal A(z)z^{-n-1}$，除 $0$ 外没有极点。取正向边界时，外圆逆时针，上岸从 $1$ 走向 $R$，下岸从 $R$ 回到 $1$，绕 $1$ 的内弧顺时针。由留数定理，整个边界积分除以 $2\pi i$ 等于 $a_n$。

先固定 $n$ 与离 $1,R$ 正距离的两岸线段，使割线宽度趋于零。$U,V$ 在闭半圆盘上的连续性使该收敛在这些紧线段上一致。$R$ 处的连接弧长度趋于零，分母在那里远离零，分子由两侧连续性有界，所以该连接弧积分趋于零；外圆删去的小弧也同样消失。$1$ 处半径 $\varepsilon$ 的连接弧长至多 $2\pi\varepsilon$，且 $|z|\ge1-\varepsilon$；定理 2.3 的全域端点极限使 $\mathcal A$ 在其两侧一致有界，故其积分范数为

$$
O_n\bigl(\varepsilon(1-\varepsilon)^{-n-1}\bigr)\longrightarrow0.
$$

两岸积分在 $1$ 处绝对可积，因为 $U,V$ 连续且有限，在 $R$ 处亦然。这些估计允许最后使两端的小弧半径趋于零；不要求对 $n$ 一致地交换极限。得到精确恒等式

$$
a_n=E_n+\frac1{2\pi i}\int_1^R
       \frac{U(x)-V(x)}{x^{n+1}}\,dx
    =E_n+\frac1\pi\int_1^R\frac{\operatorname{Im}U(x)}{x^{n+1}}\,dx,
$$

其中 $E_n$ 是带有上述单侧端值的正向外圆积分除以 $2\pi i$。两岸差为 $2i\operatorname{Im}U$，所以符号是加号。外圆长为 $2\pi R$，于是

$$
|\operatorname{Re}E_n|\le |E_n|\le BR^{-n}.
$$

令 $h(x)=-\operatorname{Im}U(x)$。它在 $[1,R]$ 连续，在 $1<x\le R$ 严格为正，$h(1)=0$。选取固定的 $1<\alpha<\beta<R$，则

$$
m=\min_{\alpha\le x\le\beta}h(x)>0,\qquad
\frac1\pi\int_1^R\frac{h(x)}{x^{n+1}}\,dx
 \ge\frac{m(\beta-\alpha)}{\pi\beta^{n+1}}.
$$

$a_n$ 为实数，故取前式的实部可得

$$
a_n\le BR^{-n}-\frac{m(\beta-\alpha)}{\pi\beta^{n+1}}<0
$$

当 $n$ 足够大时最后一步成立，因为 $(\beta/R)^n\to0$。这同时控制外圆误差和严格负积分的优势；没有使用无限远轮廓、割线远端的符号或全局奇点分类。

## 4. 总和、有限前缀与全部正整数平滑次数

**定理 4.1（全参数最终符号与严格可容许下界）。** 对每个整数 $d\ge1$、$\boldsymbol{k}\in\mathbb Z_{\ge1}^d$ 与整数 $\ell\ge1$，存在整数 $N_0(\boldsymbol{k},\ell)\ge0$ 使

$$
C_n^{0;\boldsymbol{k};\ell}<0\qquad(n\ge N_0).
$$

对每个进一步固定的整数 $j\ge1$，存在整数 $N_j(\boldsymbol{k},\ell,j)\ge0$ 使

$$
C_n^{j;\boldsymbol{k};\ell}>0\qquad(n\ge N_j).
$$

若 $k_1>1$，同样可取 $N_j$ 使

$$
C_n^{j;\boldsymbol{k};\ell}
 >Z^{-\ell}\binom{n+j-1}{n}\qquad(n\ge N_j).
$$

每个有限前导一块都在量词之内；阈值只针对各组固定参数。

证明。沿用 $a_n$ 与 $\lambda$，取定理 3.1 的 $N\ge1$。先证明绝对收敛及总和，不能仅从径向极限推断它们。置 $P(r)=\sum_{m<N}a_mr^m$、$q_m=-a_m>0$（$m\ge N$）。对 $0\le r<1$，

$$
\sum_{m\ge N}q_mr^m=P(r)-A(r).
$$

当 $r\uparrow1$，右侧趋于有限值 $P(1)-\lambda$。左侧各项非负并单调增加，单调收敛定理给出 $\sum_{m\ge N}q_m=P(1)-\lambda<\infty$。有限前缀可取绝对值，故

$$
\sum_{m\ge0}|a_m|<\infty,\qquad
\sum_{m\ge0}a_m=\lambda.
$$

令 $b_n=C_n^{1;\boldsymbol{k};\ell}=\sum_{m=0}^na_m$，$e_n=b_n-\lambda$。对 $n\ge N$，

$$
e_n=-\sum_{m>n}a_m=\sum_{m>n}q_m>0.
$$

因而 $b_n>\lambda\ge0$，已得 $j=1$ 的全部结论。注意 $e_n\to0$，所以仅有最终严格正性还不足以控制下一次求和的有限带符号前缀。

由于 $e_n$ 的负项只可能在有限前缀内，其总和 $T=\sum_{n\ge0}e_n$ 在 $\mathbb R\cup\{+\infty\}$ 中存在。对 $0\le r<1$，绝对收敛的卷积给出

$$
\sum_{n\ge0}e_nr^n=\frac{A(r)-\lambda}{1-r}.
$$

这里绝对收敛也可由 $b_n$ 有界直接推出。对 $n\ge N$ 的非负尾部再用单调收敛，有限前缀按多项式取极限，得到扩展实数意义的精确等式

$$
T=\lim_{r\uparrow1}\frac{A(r)-\lambda}{1-r}.
$$

若 $k_1>1$，`CompositionBoundary.result head tail` 给出 $\sum f_m=Z$。因此对 $0\le r<1$，

$$
0<F_{\boldsymbol{k}}(r)\le Z,\qquad
Z-F_{\boldsymbol{k}}(r)
 =\sum_{m\ge1}f_m(1-r^m)\ge f_1(1-r).
$$

函数 $x\mapsto x^{-\ell}$ 在正实轴凸，其在 $Z$ 处的切线界给出

$$
\frac{A(r)-Z^{-\ell}}{1-r}
 \ge\ell Z^{-\ell-1}\frac{Z-F_{\boldsymbol{k}}(r)}{1-r}
 \ge\ell Z^{-\ell-1}f_1>0.
$$

于是 $T\ge\ell Z^{-\ell-1}f_1>0$，允许 $T=+\infty$；不需要假设 $F'(1)$ 有限。

若 $k_1=1$，则 $\lambda=0$。取定理 2.3 的 $D\ge1$ 与 $M$，保留深度归一化，得到

$$
\frac{A(r)}{1-r}
 \ge\frac{r^{d\ell}}{D^\ell(1-r)(1+|\log(1-r)|)^{M\ell}}
 \longrightarrow+\infty\qquad(r\uparrow1).
$$

确实 $r^{d\ell}\to1$，而对每个固定整数 $p\ge0$ 有 $t(1+|\log t|)^p\to0$（置 $t=e^{-u}$ 即为指数胜过多项式）。因此前导一情形 $T=+\infty$，没有以可容许边界总和代替这里的发散证明。

现在 $T>0$ 在两种情形都已成立。因此

$$
d_n^{(2)}:=\sum_{m=0}^n e_m\longrightarrow T
$$

并存在 $\delta>0$、整数 $M_2$，使 $d_n^{(2)}\ge\delta$ 对 $n\ge M_2$ 成立。若 $T$ 有限，可取 $\delta=T/2$；若 $T=+\infty$，可取 $\delta=1$。这已经包含 $e_0,\ldots,e_{N-1}$ 的全部符号贡献。

设 $d^{(1)}=e$，递归定义 $d_n^{(j+1)}=\sum_{m=0}^n d_m^{(j)}$。每次求和保留有限前缀：若 $d_m^{(j)}\ge\delta_j>0$ 对 $m\ge M_j$ 成立，则

$$
d_n^{(j+1)}
 \ge-\sum_{m<M_j}|d_m^{(j)}|
       +\delta_j(n-M_j+1)\longrightarrow+\infty.
$$

从 $j=2$ 起该式归纳给出每个固定 $j\ge2$ 的最终严格正性，并为下一次求和提供正的常数下界；$j=1$ 则由正尾和给出。没有把最终正性直接当成正总和或发散。

最后，定理 2.2 的重复求和式与二项恒等式

$$
\sum_{m=0}^n\binom{m+j-1}{m}=\binom{n+j}{n}
$$

给出对所有 $n\ge0,j\ge1$ 的恒等式

$$
d_n^{(j)}=C_n^{j;\boldsymbol{k};\ell}
                -\lambda\binom{n+j-1}{n}.
$$

因而当 $\lambda=0$ 时得到最终正性；当 $\lambda=Z^{-\ell}>0$ 时得到所述严格下界以及正性。取相应的有限阈值并与 $0$ 比较，即完成全部量词。

## 5. 必要边界与后续系数问题

**命题 5.1（初始指标及求和前缀的反例）。** 定理 4.1 中的最终限定不可替换为所有指标，也不能在重复求和中删除总和为正的论证。

证明。当 $\boldsymbol{k}=(1)$、$\ell=2$ 时，$-\operatorname{Log}(1-z)=z+z^2/2+z^3/3+z^4/4+\cdots$，精确形式除法给出

$$
\left(\frac{z}{-\operatorname{Log}(1-z)}\right)^2
 =1-z+\frac{z^2}{12}+0z^3+O(z^4).
$$

所以 $a_0>0$、$a_2>0$、$a_3=0$，均与所有指标严格为负不相容。对 $\boldsymbol{k}=(2)$，有 $F(z)=1+z/4+O(z^2)$；取 $\ell=5,j=1$，则

$$
C_1^{1;(2);5}=1-5/4=-1/4<0,
$$

故即使可容许也不能把最终正性换成所有指标正性。另取实序列 $v_0=-2$、$v_n=2^{-n}$（$n\ge1$），则尾部严格为正，但 $\sum_{m=0}^nv_m=-1-2^{-n}<0$。因此前缀控制所需的正总和或发散条件不能仅由尾部正性替代。

**定义 5.2（精确阈值问题）。** 对固定参数，定义

$$
\begin{aligned}
\nu_0(\boldsymbol{k},\ell)
 &=\min\{N\ge0:\ \forall n\ge N,\ C_n^{0;\boldsymbol{k};\ell}<0\},\\
\nu_j(\boldsymbol{k},\ell)
 &=\min\{N\ge0:\ \forall n\ge N,\ C_n^{j;\boldsymbol{k};\ell}
        >\lambda\binom{n+j-1}{n}\}\quad(j\ge1).
\end{aligned}
$$

定理 4.1 保证这些集合非空；命题 5.1 表明有限前缀仍有实质内容。确定这些最小阈值及其随组合、$\ell$、$j$ 的依赖，是与本卷存在性结论相区别的后续问题。有限割线证明使用依赖参数的 $R_0,\rho$ 和正积分区间；它不提供统一或有效阈值、全局奇点信息或系数主项。

## 追加锚（本行以下为增补区）

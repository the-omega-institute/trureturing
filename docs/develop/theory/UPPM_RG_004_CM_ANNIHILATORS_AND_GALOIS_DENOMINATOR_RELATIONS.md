# 原 CM 共同消去理想与移动分母的三次预算

## 51. 原整数入口的 CM 因子与全移动参数的三次预算

**定义 51.1（共同约化模与扩域分母）。** 本节固定 [002 §§12–17](UPPM_RG_002_DIOPHANTINE_DEFINITIONS_RELATIONAL_COMPILATION_AND_STOPPING_BOUNDARIES.md) 的全部原数据：八次全实域 $F$、原整方程 $E_0:y^2=x^3-x$、指定正根和实嵌入下的原点 $P_1,P_2$、全部有限地方及其原过滤 $U_v$。固定原整数 $M\ge1$，取同一个 $q_H=q(H,H;M)$。组合 $R_m$、点 $T_{n,m}=[n]R_m$、$r=\|m\|_2$、$h_0>0$ 及原 $F$ 分母 $B(T)$、其截取与范数，均指 [003 定义 49.1](UPPM_RG_003_CONJUGATE_CM_RESONANCE_RANK_AND_COVERAGE.md#49-原共同周期上移动-cm-组合的统一分母尾部) 的对象。特别地，$B$ 的坐标始终是原整方程的 $x$，其范数指数始终是 $1/8$。

另取原 CM 扩域 $K=F(i)$，$[K:\mathbb Q]=16$，并固定原作用 $[i](x,y)=(-x,iy)$。记 $\mathcal O=\mathbb Z[i]$，$N(a+bi)=a^2+b^2$。对 $p\ne2,7$ 及 $K$ 的每个地方 $w\mid v\mid p$，所有约化都在同一个 $k_w$ 及其代数闭包内进行，且 $i$ 的约化必须来自当前 $K\hookrightarrow K_w$。定义有限 $\mathcal O$ 模及其共同消去理想

$$
\mathcal H_w=\mathcal O\overline P_1+\mathcal O\overline P_2
\subset E_0(k_w),\qquad
I_w=\operatorname{Ann}_{\mathcal O}(\mathcal H_w)
=\{\alpha\in\mathcal O:[\alpha]\overline P_1=[\alpha]\overline P_2=O\}.
\tag{51.1}
$$

这里的 CM 模不是把两点改成同一个点的 CM 倍数。对非挠 $S\in E_0(K)$，在 $\mathcal O_K$ 中定义互素整理想和归一化范数

$$
\begin{gathered}
(x(S))=A_K(S)B_K(S)^{-2},\qquad
b_w^K(S)=\tfrac12\max(0,-\operatorname{ord}_w x(S)),\\
\|B_K(S)\|_K=N_{K/\mathbb Q}(B_K(S))^{1/16}.
\end{gathered}
\tag{51.2}
$$

原整方程保证负的 $x$ 赋值为偶数，故这是整理想；非挠性排除 $O$ 和 $x=0$ 的二挠点。记 $U_w(1)$ 为原好整方程在 $K_w$ 上约化为 $O$ 的第一形式层。这只用于中间点，不另行定义或替换 $F_v$ 上的原过滤。仍写

$$
L_p(T)=\frac18\sum_{v\mid p}f_v b_v(T)\log p
\qquad(T\in E_0(F)\text{ 非挠}).
\tag{51.3}
$$

CM 指标、约化消去理想和平方根分母的先例分别见 Streng，*Divisibility sequences for elliptic curves with complex multiplication*，*Algebra & Number Theory* **2** (2), 183–208，DOI [10.2140/ant.2008.2.183](https://doi.org/10.2140/ant.2008.2.183)，式 (1.1) 及 §3 的 rank of apparition；以及 Verzobio，*Primitive divisors of sequences associated to elliptic curves with complex multiplication*，[arXiv:2010.10175v2](https://arxiv.org/html/2010.10175v2)，定义 2.5。这里取两个原生成元的共同消去理想，用于下面保留原整数入口的预算。

**命题 51.2（实际共同核给出原整数的低成本 CM 因子）。** 对每个有理素数 $p\ne2,7$、每个 $w\mid v\mid p$，存在只依赖 $p,w$ 及原固定点对的非零 $\gamma_w\in\mathcal O$，使

$$
I_w=(\gamma_w),\qquad
\gamma_w\mid n_p\quad\text{在 }\mathbb Z[i]\text{ 中},\qquad
N(\gamma_w)\le C_p\le4p^2.
\tag{51.4}
$$

这里 $n_p,\varepsilon_p,C_p$ 精确沿用原 (16.2)、(16.9)，没有改变原共同约化阶。对所有 $m\in\mathbb Z^2\setminus\{0\}$ 及所有 $n\in n_p\mathbb Z\setminus\{0\}$，同一个 $\gamma_w$ 同时给出

$$
\begin{gathered}
S_{w,m}=[\gamma_w]R_m\in E_0(K)\cap U_w(1),\qquad
\delta_{w,n}=n/\gamma_w\in\mathbb Z[i]\setminus\{0\},\qquad
T_{n,m}=[\delta_{w,n}]S_{w,m},\\
\widehat h(S_{w,m})=N(\gamma_w)h_0r^2\le4h_0p^2r^2,\\
b_w^K(T_{n,m})
=b_w^K(S_{w,m})+\operatorname{ord}_w(\delta_{w,n})
\le b_w^K(S_{w,m})+v_p(n).
\end{gathered}
\tag{51.5}
$$

所有涉及的点均非挠、非零；结论包括一个 $m_j=0$、任意大的 $m$ 和负 $n$。

**证明。** 原定理 16.3 给出 $K$ 在 $p\ne2,7$ 不分歧，故 $e_w=e_v=1$，且原方程好约化。先把原定理 16.4 的半点关系用于当前同一个约化。原 (16.13) 的两个实际半点 $Q_j$ 满足 $[2]Q_j=P_j$，而原 $D_4$ Frobenius 作用的平方同时给出

$$
\pi_p^2\overline Q_j=[\varepsilon_p]\overline Q_j
\quad(j=1,2),\qquad
G_p=\ker(\pi_p^2-[\varepsilon_p]).
\tag{51.6}
$$

因此 $\overline P_j\in[2]G_p$。因为 $i^{p^2}=i$，$\pi_p^2$ 与当前 $[i]$ 交换，$[2]G_p$ 是 $\mathcal O$ 稳定群，遂有 $\mathcal H_w\subset[2]G_p$。这里仅使用 (51.6) 的共同作用；当 $\varepsilon_p=-1$ 时不把 $Q_j$ 说成 $\mathbb F_{p^2}$ 有理点，剩余次数为 $4$ 的原地方仍包括在内。$\#G_p=C_p$、$\#[2]G_p=C_p/4$ 的原结论继续适用，不重选半点或最终整数。

实际点、半点及 CM 模挠独立性的来源是 Brox，[固定原文的 “The quadratic-field elliptic curve” 及其独立性引理](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex)。这里仅使用原 002 已固定的归一化，不引入该文其它聚合高度结论。

现在在当前 $i$ 的嵌入下把 $\pi_p^2-[\varepsilon_p]$ 提升为一个实际 Gaussian 算子。同源的次数、普通性和 Frobenius 的成熟输入为 Silverman，*The Arithmetic of Elliptic Curves*，第二版，[III.6.2、V.2.3.1、V.3.1、V.4.1(a)](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)。其在本例的对应分两支如下。

若 $p\equiv1\pmod4$，$(x^3-x)^{(p-1)/2}$ 的 $x^{p-1}$ 系数是

$$
(-1)^{(p-1)/4}\binom{(p-1)/2}{(p-1)/4}\not\equiv0\pmod p.
\tag{51.7}
$$

故约化普通。其几何自同源环是虚二次域中的序，并包含当前约化作用给出的 $\mathbb Z[i]$。这个作用是忠实的：非零 $a+bi$ 若作用为零，与 $a-bi$ 复合会使非零整数 $a^2+b^2$ 的乘法态射为零，与椭圆曲线整数乘法的正次数矛盾。$\mathbb Z[i]$ 已是 $\mathbb Q(i)$ 的极大整环，因此约化的几何自同源环恰为这一嵌入的 $\mathbb Z[i]$。于是有唯一 $\lambda_w=u_w+v_wi$，其约化态射等于 $\pi_p$，并满足

$$
\lambda_w+\overline{\lambda_w}=a_p,\qquad
N(\lambda_w)=p.
\tag{51.8}
$$

这里使用 Frobenius 的迹、次数与特征方程；对偶作用把 $[i]$ 送到 $[-i]$，故 Gaussian 作用的次数正是其范数，迹正是与共轭之和。$\lambda_w$ 不可能是整数，因为其次数为非平方的 $p$。不能任意从两个共轭 Gaussian 根中挑一个；必须由当前 $[i]$ 的约化来确定 $\lambda_w$。置 $\beta_w=\lambda_w^2-\varepsilon_p$。

若 $p\equiv3\pmod4$，同一系数判据给出超奇异约化。又因二次特征满足 $\chi(-1)=-1$，$x$ 与 $-x$ 在 $\sum_x\chi(x^3-x)$ 中相消，故 $a_p=0$，包括 $p=3$。Frobenius 特征方程遂给出 $\pi_p^2=[-p]$。此时置 $\beta_w=-p-\varepsilon_p$；这里不把 $\pi_p$ 本身认作 Gaussian 整数。

两支均有

$$
\widetilde{[\beta_w]}=\pi_p^2-[\varepsilon_p],\qquad
N(\beta_w)=p^2-\varepsilon_p(a_p^2-2p)+1=C_p>0.
\tag{51.9}
$$

由 $a_p^2\le4p$，两种符号均有 $C_p\le(p+1)^2\le4p^2$。由于 (51.9) 消去 $G_p$，它也消去 $[2]G_p$ 和 $\mathcal H_w$，故 $\beta_w\in I_w$。另一方面，原 $n_p$ 同时消去两点的约化；整数作用与 $[i]$ 交换，所以 $n_p\in I_w$。因此 $I_w$ 是非零理想。

Gaussian 整数环是按 $N$ Euclidean 的：对商的实部、虚部分别取最近整数，余数范数至多为除数范数的一半。取非零理想中的最小正范数元素，对理想的任意其它元素作此除法，余数仍在理想内，最小性迫使余数为零，故理想为主理想。这是经典 Gaussian PID 的中间应用，见 Conrad，*The Gaussian Integers*，[§§1、3、5](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/Zinotes.pdf) 的范数、除法与 Bézout 理论。取 $I_w=(\gamma_w)$，则

$$
n_p=\gamma_w\rho_w,\qquad
\beta_w=\gamma_w\zeta_w,\qquad
\rho_w,\zeta_w\in\mathbb Z[i]\setminus\{0\}.
\tag{51.10}
$$

这是真正的元素整除，方向来自 $(n_p),(\beta_w)\subset I_w$。范数乘法性给出 $N(\gamma_w)\le N(\beta_w)=C_p$，证明 (51.4)。仅有 $N(\gamma_w)\mid n_p^2$ 不能代替 (51.10)。这些选择在 $m,n,H$ 出现前已经确定。

因为 $\gamma_w$ 本身消去两点，$S_{w,m}$ 在 $w$ 约化为 $O$，所以确实进入第一形式层。入口的合法性不从 $[\delta_{w,n}]S_{w,m}$ 约化为 $O$ 反推；一个整数为 $p$ 进单位也不能保证它在整个约化群上无核。由 $n_p\mid n$ 与 (51.10)，$\delta_{w,n}\in\mathbb Z[i]$，CM 环作用则精确给出原来的同一个 $T_{n,m}=[\delta_{w,n}]S_{w,m}$。

为计算入口高度，写 $\gamma_w=a+bi$。直接使用原四方向的 (16.21)，得到

$$
\widehat h(S_{w,m})
=h_0\bigl[(am_1)^2+(bm_1)^2+(am_2)^2+(bm_2)^2\bigr]
=N(\gamma_w)h_0r^2>0.
\tag{51.11}
$$

因此入口和终点均非挠、非零，所有局部形式参数非零。CM 同源的高度按次数缩放是成熟工具；这里用原准确高度式落实为 $N(\gamma_w)$，没有将范数再平方。一般的缩放陈述见上述 Verzobio 原文引理 2.9；原 (16.21) 已提供本例所需的全部配对。

最后在原形式参数 $t=-x/y$ 上计算。$[i]$ 的整作用满足 $t([i]S)=it(S)$，且

$$
[i]^*\frac{dx}{2y}=i\frac{dx}{2y}.
\tag{51.12}
$$

由整形式加法与整数乘法，任意 $\alpha=a+bi\in\mathbb Z[i]$ 的形式作用是无常数项的整级数，线性项为 $\alpha t$，保第一层。形式对数的线性化给出

$$
\mathcal L([\alpha]t)=\alpha\mathcal L(t).
\tag{51.13}
$$

这是微分嵌入中的 $\alpha$，不是 $N(\alpha)$ 或 $\bar\alpha$。先例见 Streng，[作者预印本（版本标注 12 November 2007）](https://www.math.leidenuniv.nl/~streng/cmeds.pdf) 引理 2.6、定理 2.9、推论 2.10；下文对该文引理 3.4、定理 3.21 的编号亦取此版本。这里整性也由原 $[i]$ 公式直接给出，不需要把一般坏约化整性定理移用于新模型。

Silverman 同书 IV.5.5、IV.6.3–6.4 表明，对数与逆指数在深度 $s>e_w/(p-1)$ 时保赋值。本处 $p\ge3$、$e_w=1$，整个第一层已满足这个严格不等式。具体地，$\mathcal L(t)=t+\sum_{j\ge2}a_jt^j/j$，$a_j\in\mathcal O_w$；若 $\operatorname{ord}_w t=s\ge1$，由 $v_p(j)\le(j-1)/(p-1)$，每个后续项的赋值严格大于 $s$。于是 $\operatorname{ord}_w\mathcal L(t)=s$。原形式展开 $x=t^{-2}(1+t\mathcal O_w[[t]])$ 又给出第一层上的 $b_w^K=\operatorname{ord}_w t$。把 (51.13) 用于 $\delta_{w,n}$，得到

$$
\begin{aligned}
b_w^K(T_{n,m})
&=b_w^K(S_{w,m})+\operatorname{ord}_w\delta_{w,n},\\
0\le\operatorname{ord}_w\delta_{w,n}
&=v_p(n)-\operatorname{ord}_w\gamma_w\le v_p(n).
\end{aligned}
\tag{51.14}
$$

非负性来自 $\delta_{w,n}$ 整，最后一式使用 $e_w=1$。这与 Streng 引理 3.4 的深层分母增长相符，严格的深度条件已在此核入。

小素数不删去。原 (16.12) 给出 $n_3=2,n_5=5$。在 $3$ 处，$\varepsilon_3=1$、$\beta_w=-4$，$\gamma_w\mid2$，第一层仍在对数保赋值域内。在 $5$ 处，$\varepsilon_5=-1,a_5=-2$，按当前嵌入选出的 $\lambda_w=-1\pm2i$ 给出 $\beta_w=-2\mp4i$、$N(\beta_w)=20$；$\gamma_w\mid5$。式 (51.14) 不要求 $5\nmid n$，也不要求先删去 $\delta_{w,n}$ 的 $5$ 进部分。负 $n$ 仅改变单位 $-1$，整形式逆元保深度，故全部公式适用于负数。$\square$

**定理 51.3（原共同周期上全部移动组合的三次小素数与尾部预算）。** 存在只依赖定义 51.1 的原固定数据的常数 $C>0$ 和整数 $H_0\ge7$，使所有整数 $H\ge H_0$、所有 $m\in\mathbb Z^2\setminus\{0\}$ 及所有 $n\in q_H\mathbb Z\setminus\{0\}$ 同时满足

$$
0\le\log\|B(T_{n,m})^{\le H}\|
\le\log|n|+CH^3r^2,
\tag{51.15}
$$

$$
\left|\log\|B(T_{n,m})^{>H}\|-h_0n^2r^2\right|
\le C\bigl[H^3r^2+\log(2|n|r)\bigr],
\tag{51.16}
$$

以及真正对无限移动参数范围统一的

$$
\sup_{\substack{m\in\mathbb Z^2\setminus\{0\}\\n\in q_H\mathbb Z\setminus\{0\}}}
\left\{\frac{\log\|B(T_{n,m})^{\le H}\|}{h_0n^2r^2}
+\left|\frac{\log\|B(T_{n,m})^{>H}\|}{h_0n^2r^2}-1\right|\right\}
\le\frac{CH^3}{q_H^2}\longrightarrow0.
\tag{51.17}
$$

原全部有限地方的 $T_{n,m}\in U_v(H)$ 条件仍成立。没有重选 $n$、点、分母或周期；原定理 49.2 的 $H^5$ 界仍然有效。

**证明。** 对 $p\le H$、$p\ne2,7$，原 (16.5)–(16.6) 给出 $n_p\mid q_H\mid n$，所以可在每个 $w\mid p$ 使用命题 51.2。先支付扩域带来的高度与地方权重，不能把只对 $E_0(F)$ 陈述的 (49.8) 第二式直接套给 $S_{w,m}\in E_0(K)$。

对任意非挠 $S\in E_0(K)$，绝对高度的有限项和无限项分解为

$$
\begin{aligned}
h(x(S))&=2\log\|B_K(S)\|_K+a_{\infty,K}(S),\\
a_{\infty,K}(S)&=\frac1{16}\sum_{\sigma:K\hookrightarrow\mathbb C}
\log\max(1,|x(\sigma S)|)\ge0.
\end{aligned}
\tag{51.18}
$$

此处对全部 $16$ 个嵌入求和；每对共轭嵌入合起来恰为复地方的权重 $2/16$。有限处取 $|p|_w=p^{-1}$，绝对高度权重为 $e_wf_w/16$，而 $\log\max(1,|x|_w)=2b_w^K(S)\log p/e_w$。因此有限项准确等于 $2\log\|B_K(S)\|_K$，包括可能分歧的地方。原 (12.7) 对所有代数点成立，不以全实性为假设，故

$$
\frac{f_w}{16}b_w^K(S)\log p
\le\log\|B_K(S)\|_K
\le\tfrac12h(x(S))\le\widehat h(S)+\log2.
\tag{51.19}
$$

这只用非负性与原绝对高度比较，没有对一般 $K$ 点使用实圆的椭圆对数分离。

对最终点 $T=T_{n,m}\in E_0(F)$，在 $p\ne2,7$ 处 $K/F$ 不分歧，$b_w^K(T)=b_v(T)$，且 $\sum_{w\mid v}f_w=2f_v$，从而

$$
\sum_{w\mid p}\frac{f_w}{16}b_w^K(T)\log p
=\sum_{v\mid p}\frac{f_v}{8}b_v(T)\log p=L_p(T).
\tag{51.20}
$$

这是回到原 $F$ 分母的逐有理素数身份，而不是把 $K$ 上的新分母定义当作原分母。

令 $g_K(p)=\#\{w:w\mid p\}\le16$。分别对每个 $S_{w,m}$ 应用 (51.19)，再用 (51.5)、$\sum_{w\mid p}f_w=16$，得到

$$
\begin{aligned}
L_p(T_{n,m})
&\le\sum_{w\mid p}\frac{f_w}{16}b_w^K(S_{w,m})\log p
 +\sum_{w\mid p}\frac{f_w}{16}v_p(n)\log p\\
&\le\sum_{w\mid p}\bigl[\widehat h(S_{w,m})+\log2\bigr]
 +v_p(n)\log p\\
&\le g_K(p)\bigl[4h_0p^2r^2+\log2\bigr]+v_p(n)\log p\\
&\le64h_0p^2r^2+16\log2+v_p(n)\log p.
\end{aligned}
\tag{51.21}
$$

这里每个地方可以有不同的 $\gamma_w$ 和不同的全局 $K$ 点 $S_{w,m}$，每一项都由它自己的完整高度支付一次。所付的是至多 $16$ 个完整高度的和；没有把各地的分别最优值拼成一个共同点的高度，也没有省去扩域的固定次数成本。

对 $p=2,7$，直接取原 (49.11)–(49.13) 已固定的深度 $s_v$ 与共同整数入口 $c_p$。令 $H_0$ 不小于所有这些 $s_v$。于是 $c_p\mid q_H\mid n$，原证明对同一 $S_{p,m}=[c_p]R_m$ 给出

$$
L_p(T_{n,m})
\le h_0c_p^2r^2+\log2+v_p(n)\log p
\qquad(p=2,7).
\tag{51.22}
$$

其中二进处使用原极小模型、固定坐标变换和 $s_v>e_v/(p-1)$；七进处保留 $e_v=2$。原恒等式 $\sum_{v\mid p}e_vf_v=8$ 已支付这两处的赋值增量。这里不在二进处应用第一层保赋值结论，也不改变这些地方的原 $U_v$。

将 (51.21) 与 (51.22) 相加，有

$$
\begin{aligned}
\log\|B(T_{n,m})^{\le H}\|
\le{}&\sum_{p\le H}v_p(n)\log p\\
&+h_0r^2\left[c_2^2+c_7^2+
64\sum_{\substack{p\le H\\p\ne2,7}}p^2\right]
+\bigl[2+16\#\{p\le H:p\ne2,7\}\bigr]\log2.
\end{aligned}
\tag{51.23}
$$

现在仅用 $\sum_{p\le H}v_p(n)\log p\le\log|n|$、$\sum_{p\le H}p^2\le\sum_{j=1}^Hj^2\le H^3$、素数个数不超过 $H$ 和 $r^2\ge1$，即可把固定项吸收入 $CH^3r^2$。整理想范数给出非负性，故 (51.15) 成立。不使用新的素数分布、Wieferich 稀疏性或算术独立性假设。

原 (16.5) 保证 $[n]P_j\in U_v(H)$ 对全部 $p\le H,v\mid p,j$ 成立，子群性遂给出 $T_{n,m}\in U_v(H)$。这个深层成员性来自原 $n$；没有把深度 $H$ 赋给较小的 $\gamma_w$ 或 $n_p$。

总分母继续使用原 (49.8) 第一式。它已经以原 (17.5) 的固定常数控制所有实共轭，给出所有 $n,m\ne0$ 的统一误差 $O(\log(2|n|r))$。从总分母减去 (51.15)，并用 $\log|n|\le\log(2|n|r)$，得到 (51.16)。这里没有把 Streng 定理 3.21 的固定非挠点隐常数改作移动点统一常数。

为对无限范围取上确界，置 $N=|n|\ge q_H$、$r\ge1$。$\log r/r^2\le1/(2e)$，且 $\log(2N)/N^2$ 在 $N\ge1$ 上递减，故

$$
\frac{\log(2Nr)}{N^2r^2}
\le\frac{\log(2q_H)+1/(2e)}{q_H^2},\qquad
\frac{H^3r^2}{N^2r^2}\le\frac{H^3}{q_H^2}.
\tag{51.24}
$$

所以 (51.15)–(51.16) 归一化后，其和先被 $C[H^3+\log(2q_H)+1]/q_H^2$ 控制。再由原 (16.27) 在固定 $M$ 下的 $\log q_H\sim H^2$，得到 (51.17) 及其趋零。$C,H_0$ 只依赖原固定数据，不依赖任何移动参数；$n<0$ 仍在全部量词内。$H\ge1$ 时 $H^3\le H^5$，所以这项加强不撤销原较粗预算。

用白话说，原整数入口的大小可以到 $p^2$，整数倍的高度要为它支付平方，因而逐素数付到 $p^4$。共同消去理想给出一把 Gaussian 整数钥匙，它在环内整除原整数，且范数至多 $4p^2$；它的高度成本就是这个范数。先用它进入形式群，再乘 $n/\gamma_w$，到达的仍是原来的 $[n]R_m$，后半段分母只按该乘数的地方指数增长。不同地方各选自己的钥匙，也各自支付一次完整高度，地方总数由 $16$ 控制。于是逐素数的成本降为 $p^2$，求和成为 $H^3$；二进和七进仍走原深入口，全部最终条件保持原样。

本定理的新增内容是原实际点对、原共同周期、原分母和全部移动 $m,n$ 的联合预算 (51.15)–(51.17)，属 repo-derived 综合推导。Gaussian PID、CM 同源次数、形式对数和绝对高度分解都是上述文献的成熟输入，不另作一般新理论。Streng 定理 3.21 固定点后取指标极限；Verzobio 同文定理 1.7–1.8 处理固定点的原始因子，后者还要求端同态关系 $f(P)=g(Q)$、$g\ne0$。这些结论均不能直接代替这里的两个 CM 模挠独立生成元及其全移动参数量词。Au-Yeung，*Explicit valuation of elliptic nets for elliptic curves with complex multiplication*，[arXiv:2512.09601v2](https://arxiv.org/html/2512.09601v2)，定理 1.5、1.8、2.14 与 §3.1，给出 CM 网、局部高度和分母的相邻理论；*Higher rank elliptic sieve via CM endomorphisms*，[arXiv:2610.18281](https://arxiv.org/html/2610.18281)，定理 1.3 的筛界仍以固定 $P$ 为输入，且常数显式依赖 $P$。这里不从这些固定点结果提取对 $R_m$ 的一致常数，也不主张全球文献优先性。$\square$

## 52. 三次预算对原共同尾部夹角界的直接作用

**定理 52.1（全行格消费者的三次系数误差）。** 沿用 [003 定义 50.1](UPPM_RG_003_CONJUGATE_CM_RESONANCE_RANK_AND_COVERAGE.md#50-原行格约束下的共同尾部纯夹角界与实际剪切族) 的全部记号。存在只依赖原固定数据的 $C_0>0$ 及整数 $H_1\ge H_0$，使对每个整数 $H\ge H_1$，置

$$
\epsilon_H^{(3)}=\frac{C_0H^3}{q_H^2}\le\frac12,\qquad
\mathcal C_H=
\frac{2/\sqrt3+\log2/(h_0q_H^2)}{1-\epsilon_H^{(3)}}
=\frac2{\sqrt3}+O(H^3/q_H^2),
\tag{52.1}
$$

则对所有 $n\in q_H\mathbb Z\setminus\{0\}$、所有线性独立的整数行 $m,l\in\mathbb Z^2$ 同时有

$$
\mathcal A_H(n,m)>0,\quad \mathcal A_H(n,l)>0,\qquad
0\le\frac{\mathcal G_H(n,\mathbb Zm+\mathbb Zl)}
 {\sqrt{\mathcal A_H(n,m)\mathcal A_H(n,l)}}
\le\mathcal C_H|\sin\varphi(m,l)|.
\tag{52.2}
$$

这是纯乘法正弦界，没有独立于夹角的加性误差；允许钝角、任意小的夹角、负 $n$，并允许两行随 $H,n$ 无界移动。式 (52.1) 的 $O$ 常数只依赖原固定数据。

**证明。** 本条只将新的 (51.17) 代入原定理 50.2 的行格关系，不重新证明该行格关系。取 $C_0$ 足够大，则所有 $H\ge H_1$、$n\in q_H\mathbb Z\setminus\{0\}$、$0\ne u\in\mathbb Z^2$ 同时满足

$$
(1-\epsilon_H^{(3)})h_0n^2\|u\|_2^2
\le\mathcal A_H(n,u)
\le(1+\epsilon_H^{(3)})h_0n^2\|u\|_2^2.
\tag{52.3}
$$

由 $H^3/q_H^2\to0$ 可使 $\epsilon_H^{(3)}\le1/2$，故这些尾部质量严格为正。设 $L=\mathbb Zm+\mathbb Zl$、$D=|\det(m,l)|\ge1$、$r=\|m\|_2$、$s=\|l\|_2$。原 (50.2) 对同一个 $n$ 上的共同理想 $J_L(n)$ 给出高度上界，尾部截取不增范数。因此

$$
\begin{aligned}
\frac{\mathcal G_H(n,L)}{\sqrt{\mathcal A_H(n,m)\mathcal A_H(n,l)}}
&\le\frac{(2/\sqrt3)h_0n^2D+\log2}
 {(1-\epsilon_H^{(3)})h_0n^2rs}\\
&=\frac{2/\sqrt3+\log2/(h_0n^2D)}{1-\epsilon_H^{(3)}}\frac D{rs}
\le\mathcal C_H|\sin\varphi(m,l)|.
\end{aligned}
\tag{52.4}
$$

最后使用的是 $n^2D\ge q_H^2$。故固定的 $\log2$ 仍随同 $D/(rs)$ 一起吸收，没有为极小夹角另留加性项。由 (52.1)，

$$
0\le\mathcal C_H-\frac2{\sqrt3}
=\frac{(2/\sqrt3)\epsilon_H^{(3)}+\log2/(h_0q_H^2)}
 {1-\epsilon_H^{(3)}}
=O(H^3/q_H^2).
\tag{52.5}
$$

用白话说，原行格关系为共同部分设置的绝对上限没有改变；改变的是两份尾部分母接近各自高度的误差。把两份质量都按新预算统一下界，原来的正弦比例便有更小的系数误差。这是定理 51.3 的直接消费者，不增加关于共同尾部下界的前提或结论。$\square$

**推论 52.2（实际剪切族的三次预算消费者）。** 对定理 52.1 的全部整数 $H\ge H_1$、全部 $n\in q_H\mathbb Z\setminus\{0\}$ 和全部 $k\in\mathbb Z$，原实际剪切行 $m_k=(k,1)$、$l_k=(k+1,1)$ 满足

$$
0\le
\frac{\mathcal G_H(n,\mathbb Z^2)}
 {\min\{\mathcal A_H(n,m_k),\mathcal A_H(n,l_k)\}}
\le
\frac{1+\log2/(h_0q_H^2)}
 {(1-\epsilon_H^{(3)})\,[1+\min\{k^2,(k+1)^2\}]}
=O(k^{-2})\quad(|k|\to\infty).
\tag{52.6}
$$

这里 $O$ 常数对 $H,n,k$ 统一。原 (50.11) 在同一个实际 $n$ 上的理想身份及其任意尾部截取继续适用；这里不再另立一份理想身份。

**证明。** 原推论 50.3 已给出这些行生成 $\mathbb Z^2$，其共同尾部质量至多为 $h_0n^2+\log2$。对两行分别使用新的 (52.3)，即得 (52.6) 的显式上界。当 $|k|\ge2$ 时，$1+\min\{k^2,(k+1)^2\}\ge k^2/4$；又因 $\epsilon_H^{(3)}\le1/2$，前面的系数至多为固定的 $2(1+\log2/h_0)$，所以 $O(k^{-2})$ 对所有所写参数一致。这个推论只改变原消费者中的预算精度。

定理 51.3 还直接适用于原共振所用的同一个 $T_{q_H,m}$：所有 $m\ne0$ 同时有小素数预算 $\log q_H+CH^3\|m\|_2^2$，以及尾部主项 $h_0q_H^2\|m\|_2^2$ 的相对误差 $O(H^3/q_H^2)$。选出两条共振时可分别使用此结论，但两份尾部的大质量不提供同一地方的共同质量下界。式 (52.2)、(52.6) 也只给共同质量上界，允许其为零。

这些结论的量词限于原周期倍数；一般非零有限目标对应的成功余类不因此变成 $q_H\mathbb Z$。剪切行确实给出原点对的实际组合，但不保证它们实现所选的前两条短共振。共同尾部的正下界、不同组合的独立性、实际短共振的实现或排除、原 $p_H(\alpha)$ 的正下界、原 (31.2)、负 $\vartheta$ 阶段的调和和发散及同一实际 $Y$ 上的满测，均仍需各自的联合算术或覆盖论证。这里的上界没有补足这些命题的前提；也不把允许某种情形等同于已证明原点实现该情形。

用白话说，各份分母的远端质量更接近各自高度，并不说明它们把质量放在同一批大素数上。原行格论证限制的是最多共享多少；三次预算使这个限制的归一化更精确，仍没有给出至少共享多少，或哪些行真正成为短共振。这些直接消费者与定理 51.3 一同属于原固定数据下的综合推导，不将原行格证明或成熟 CM 分母理论另称为新成果。$\square$

## 追加锚（本行以下为增补区）

## 53. 实际半点排除二挠入口与同地方精确深度

**定义 53.1（实际半点、系数作用与三类非标量素数）。** 保持定义 51.1 的全部原数据、原整方程分母、全部有限地方和原过滤。沿用 [002 (16.1)、(16.13)、(17.1)](UPPM_RG_002_DIOPHANTINE_DEFINITIONS_RELATIONAL_COMPILATION_AND_STOPPING_BOUNDARIES.md#16-实际共同周期的二次对数主阶交叉因子吸收与加权入口余项)，记

$$
\begin{gathered}
a^2=2,\quad b^2=3-a,\quad c^2=3+a,\quad bc=\sqrt7,\qquad
F=\mathbb Q(a,b,c),\\
Q_1=\left(\frac{1+a}{b^2},\frac{2a}{b^3}\right),\qquad
Q_2=\left(\frac{1-a}{c^2},\frac{-2a}{c^3}\right),\qquad
[2]Q_j=P_j.
\end{gathered}
\tag{53.1}
$$

根及实嵌入仍取原指定选择；这里的 $Q_j$ 就是原 (16.13) 的半点，不作二挠平移。对 $n\in\mathbb Z\setminus\{0\}$、$z=x+iy\in\mathbb Z[i]$，置

$$
V_n(z)=[nx]Q_1+[ny]Q_2,\qquad
\Psi_n(z)=[nx]P_1+[ny]P_2=[2]V_n(z).
\tag{53.2}
$$

这里 $i$ 只表示系数平面的四分之一转动；$\Psi_n(z)$ 是原 $T_{n,(x,y)}$，不是曲线自同态 $[z]([n]P_1)$。原 (16.21) 给出

$$
\widehat h(\Psi_n(z))=h_0n^2(x^2+y^2)>0\qquad(z\ne0).
\tag{53.3}
$$

因此这些非零系数组合的分母始终合法。沿用 [003 (50.5)–(50.6)](UPPM_RG_003_CONJUGATE_CM_RESONANCE_RANK_AND_COVERAGE.md#50-原行格约束下的共同尾部纯夹角界与实际剪切族) 的群论约定：$\widetilde b_v(O)=+\infty$；非零点用原 $b_v=\tfrac12\max(0,-\operatorname{ord}_v x)$，$x=0$ 时取零。不定义 $B(O)$。奇素数处，$\widetilde b_v(S)\ge r$ 恰表示 $S\in U_v(r)$，$r\ge1$；二进处仍保留原先固定的极小模型和原 $U_v$。

对每个 $p\ne2,7$，记 $\chi_2(p)=(2/p)$、$\chi_7(p)=(7/p)$，并定义互不相交的集合

$$
\begin{aligned}
\mathscr R&=\{p\ne2,7:\chi_2(p)=-1,\ \chi_7(p)=-1\},\\
\mathscr S&=\{p\ne2,7:\chi_2(p)=-1,\ \chi_7(p)=1\},\\
\mathscr D&=\{p\ne2,7:\chi_2(p)=1,\ \chi_7(p)=-1\},\qquad
\mathscr N=\mathscr R\sqcup\mathscr S\sqcup\mathscr D.
\end{aligned}
\tag{53.4}
$$

固定 $v\mid p$ 后，所有约化与 Galois 作用都在这个地方进行。记 $D_v=\{g\in\operatorname{Gal}(F/\mathbb Q):g(v)=v\}$，以及系数矩阵

$$
J(x,y)=(-y,x),\qquad C(x,y)=(y,x),\qquad D(x,y)=(x,-y).
\tag{53.5}
$$

原命题 16.2、定理 16.3 给出 $F/\mathbb Q$ 为 $D_4$ 扩张，$p\ne2,7$ 不分歧；故 $D_v$ 由该地方的算术 Frobenius $g_v$ 生成。它在实际半点及原点上的系数作用 $S_{g_v}$ 如下，$f_v=|D_v|$。

| $\chi_2(p)$ | $\chi_7(p)$ | $S_{g_v}$ | $f_v$ |
| --- | --- | --- | --- |
| $1$ | $1$ | $I$ 或 $-I$ | $1$ 或 $2$ |
| $1$ | $-1$ | $D$ 或 $-D$ | $2$ |
| $-1$ | $1$ | $C$ 或 $-C$ | $2$ |
| $-1$ | $-1$ | $J$ 或 $-J$ | $4$ |

**定理 53.2（旋转型实际半点的入口与 $1+i$ 等深）。** 对每个 $p\in\mathscr R$、每个固定 $v\mid p$、每个 $n\in\mathbb Z\setminus\{0\}$ 和每个 $z\in\mathbb Z[i]\setminus\{0\}$，有

$$
\Psi_n((1+i)z)\in U_v(1)
\quad\Longleftrightarrow\quad
\Psi_n(z)\in U_v(1),\qquad
b_v(\Psi_n((1+i)z))=b_v(\Psi_n(z)).
\tag{53.6}
$$

**证明。** 先落实定义中的实际半点及作用。其来源为 Brox，固定提交 `61b82ccacfbefdff3d6e7cf986d6e6279afa1372` 的 [“The quadratic-field elliptic curve” 及 `lem:independent`](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex)。在该文的 $d=3-a$、$E:y^2=x^3-d^2x$ 上，$R_0=(1+a,2a)$ 满足曲线方程，倍点切线斜率是 $3-a/4$，故

$$
[2]R_0=\left(\frac{57}{8}-\frac{7a}{2},\frac{-660+417a}{32}\right).
\tag{53.7}
$$

原同构 $(x,y)\mapsto(x/b^2,y/b^3)$ 把 $R_0$ 送到 $Q_1$；其倍点横坐标为 $(115-27a)/56$，纵坐标为 $(-660+417a)/(32b^3)$，恰为原 $P_1$。同时共轭 $a\mapsto-a,b\mapsto c$ 得到所写负纵坐标的 $Q_2$ 和原 $P_2$。这里只落实原半点输入，不另取另一组半点或重新证明原独立性。

实际坐标还给出同一带符号排列。若 $g(a)=a$、$g(b)=s b$、$g(c)=t c$，则

$$
(gQ_1,gQ_2)=([s]Q_1,[t]Q_2),\qquad
S_g(x,y)=(sx,ty).
\tag{53.8}
$$

若 $g(a)=-a$、$g(b)=u c$、$g(c)=w b$，则

$$
(gQ_1,gQ_2)=([u]Q_2,[w]Q_1),\qquad
S_g(x,y)=(wy,ux).
\tag{53.9}
$$

其中各符号均为 $\pm1$；倍二与 $g$ 交换，故 $P_j$ 有完全相同的作用，没有二挠平移项。在固定 $D_v$ 中，Frobenius 对二次子域的限制是 $g_v(a)/a=\chi_2(p)$、$g_v(bc)/(bc)=\chi_7(p)$。在 (53.8) 中第二个符号为 $st$，在 (53.9) 中为 $uw$，这逐项给出定义 53.1 的表。特别地，旋转型有 $S_{g_v}=\pm J$；必要时取逆，得到同一个 $D_v$ 中满足 $S_\tau=J$ 的 $\tau$。对任意整数系数组合，严格有

$$
\tau V_n(z)=V_n(iz),\qquad
\tau^2V_n(z)=-V_n(z),\qquad
\tau\Psi_n(z)=\Psi_n(iz).
\tag{53.10}
$$

所有 $g\in D_v$ 保持 $\operatorname{ord}_v$，原 $x$ 函数在 $\mathbb Q$ 上定义，故 $\widetilde b_v(gS)=\widetilde b_v(S)$，且保持原各层 $U_v(r)$。这一步不能用于把 $v$ 送到其它地方的自同构。下面直接复用原 (50.6) 的深度子群不等式及整数乘法不降深度；不另立一般闭包定理。

置 $V=V_n(z)$、$W=[2]V=\Psi_n(z)$、$Z=W+\tau W=\Psi_n((1+i)z)$。首先证明入口。若 $\overline Z=O$，则在同一个特殊纤维内

$$
C_0=\overline V+\tau\overline V\in\widetilde E_0[2].
\tag{53.11}
$$

原曲线在奇素数好约化，其全部几何二挠点为 $O,(0,0),(1,0),(-1,0)$，互异且都在 $\mathbb F_p$ 上。因而 $\tau C_0=C_0$。结合 (53.10)，得到

$$
\overline V+\tau\overline V=C_0=\tau C_0
=\tau\overline V-\overline V,
\qquad [2]\overline V=O.
\tag{53.12}
$$

故 $\overline W=O$。反向若 $W\in U_v(1)$，则 $\tau W\in U_v(1)$，子群性给 $Z\in U_v(1)$。这证明第一式；它使用的是半点上的 $\tau^2V=-V$ 和全二挠有理性。只知道 $\tau^2W=-W$，消去后仅能推出 $[2]\overline W=O$，尚不能排除非零二挠。

入口不成立时两个深度均为零。入口成立后，原形式参数 $t=-x/y$ 上的整倍二级数满足

$$
[2](t)=2t+\sum_{j\ge2}c_jt^j,\qquad c_j\in\mathcal O_v.
\tag{53.13}
$$

因 $p\ne2$，当 $s=\operatorname{ord}_v t>0$ 时，首项赋值为 $s$，各后续项严格大于 $s$，所以此时才有 $b_v([2]W)=b_v(W)$。所用成熟输入是 Silverman，*The Arithmetic of Elliptic Curves*，第二版，[IV.2.3、IV §3、VII.2.1–2.2](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的整乘法级数、深度子群及约化核识别；原负 $x$ 深度与形式参数的对应已在原 (50.5)–(50.6) 给出。

由 $\tau$ 保同地方深度、$Z=W+\tau W$ 和 $Z-\tau Z=[2]W$，有

$$
b_v(Z)\ge b_v(W),\qquad
b_v(W)=b_v([2]W)\ge b_v(Z).
\tag{53.14}
$$

两向合并得 (53.6)。式 (53.3) 保证 $W,Z$ 非挠、非零，$V$ 也不可能为挠点；约化中的零点只在群论中出现。

小素数仍在所写类型中：$5\in\mathscr R$，原定理 16.4 已给出 $a_5=-2$、$C_5/4=5$ 及 $n_5=5$。这里不要求 $5\nmid n$；(53.13) 的线性系数是单位 $2$，不是参数 $n$，所以 $5\mid n$ 时结论同样成立。$2,7$ 不属于定义中的类型，原二进过滤及七进分歧边界均保留。

用白话说，先把组合点抬到那一对实际半点上。若加一次四分之一转动后进入单位元，半点之和就成为二挠点；二挠点都被局部共轭固定，而半点的第二次转动是取负。这两条关系逼迫原组合本身已经进入单位元。过了这个入口，才能在形式群内用倍二严格保深度，再由两次加减得到准确等深。这个实际半点入口及其原组合消费者是 repo-derived 推导；半点来源、二挠、形式群及原独立性均为所引输入。$\square$

**定理 53.3（对角反射型的准确分量最小值）。** 对每个 $p\in\mathscr D$、每个固定 $v\mid p$、每个 $n\in\mathbb Z\setminus\{0\}$ 和全部 $x,y\in\mathbb Z$，有

$$
\widetilde b_v(\Psi_n(x+iy))
=\min\{\widetilde b_v([nx]P_1),\widetilde b_v([ny]P_2)\}.
\tag{53.15}
$$

当 $(x,y)\ne(0,0)$ 时左侧为原非零点的有限深度；允许恰有一个系数为零。当 $x=y=0$ 时，两侧均为 $+\infty$，只作群论约定。

**证明。** 由 (53.8) 及类型表，同一 $D_v$ 内的 Frobenius $\sigma$ 满足

$$
\sigma Q_1=[\epsilon]Q_1,\qquad
\sigma Q_2=[-\epsilon]Q_2,\qquad \epsilon\in\{1,-1\}.
\tag{53.16}
$$

记 $a_0=[nx]Q_1$、$b_0=[ny]Q_2$、$A=[2]a_0$、$B=[2]b_0$、$T=A+B$。若 $\overline T=O$，则 $C_0=\overline a_0+\overline b_0$ 是同一个特殊纤维的二挠点。由全二挠有理性，$\sigma C_0=C_0$，且 $[\epsilon]C_0=C_0$。因此

$$
\overline a_0-\overline b_0
=[\epsilon]\sigma C_0=C_0
=\overline a_0+\overline b_0.
\tag{53.17}
$$

这给出 $\overline B=O$，再由 $\overline T=O$ 得 $\overline A=O$。反向由子群性立即成立，故

$$
T\in U_v(1)\quad\Longleftrightarrow\quad A,B\in U_v(1).
\tag{53.18}
$$

若入口不成立，右侧最小值和左侧都是零。若入口成立且 $(x,y)\ne(0,0)$，则 $T\ne O$ 由 (53.3) 保证，$A,B$ 也已在形式群内，允许其中一个是 $O$。准确群等式为

$$
[2]A=T+[\epsilon]\sigma T,\qquad
[2]B=T-[\epsilon]\sigma T.
\tag{53.19}
$$

因 $\sigma\in D_v$ 保深度，原 (50.6) 给出 $\widetilde b_v([2]A),\widetilde b_v([2]B)\ge b_v(T)$。此时才应用 (53.13)，包括 $O$ 的无穷深度约定，得到 $\min\{\widetilde b_v(A),\widetilde b_v(B)\}\ge b_v(T)$。反向由 $T=A+B$ 的子群不等式给出，证明 (53.15)。$x=y=0$ 的情形单独按约定成立。

原点给出必须保留的反例边界。$3\in\mathscr S$，因为 $(2/3)=-1$、$(7/3)=1$，并非本定理的对角反射型。原坐标模 $3$ 满足 $X_1=X_2=-1$、$Y_1=Y_2=0$，所以两个点都约化为同一非零二挠点，而它们的倍二约化为 $O$。对 $n=1,x=y=1$，原高度式保证 $P_1+P_2\ne O$，却有

$$
b_v(P_1)=b_v(P_2)=0,
\qquad b_v(P_1+P_2)>0
\qquad(v\mid3).
\tag{53.20}
$$

因此不能把 (53.15) 套到交换型，也不能仅凭 $2$ 为局部单位便在整个局部椭圆群逆掉倍二。此处使用原定理 16.4 的实际约化及 $n_3=2$，不以 $p=3$ 的例子否定它所属类型以外的结论。原命题 16.5 中七进个别深度不相同的例子同样不在本定理范围内。

用白话说，对角反射能从总和与反射像中取出两个分量的两倍，但只看原点时，还可能有两个相同的非零二挠约化正好相消。实际半点排除了这个残留，故总和进入形式群就迫使两个分量都进入。此后才可以把两倍的深度换回原分量，得到总和恰等于两个分量中较浅的一层。新增的是这对原点在所写同地方类型上的准确式；经典反射群等式和形式群输入不另作一般新结果。$\square$

**定理 53.4（旋转型 Gaussian gcd 与全部 $1+i$ 因子删除）。** 对每个 $p\in\mathscr R$、每个固定 $v\mid p$、每个 $n\in\mathbb Z\setminus\{0\}$ 及任意不同时为零的 $z_1,z_2\in\mathbb Z[i]$，取任一 Gaussian gcd $\gamma$，即 $(z_1,z_2)=(\gamma)$。写

$$
\gamma=(1+i)^a\gamma_0,\qquad
a\in\mathbb Z_{\ge0},\quad \gamma_0\ne0,\quad (1+i)\nmid\gamma_0.
\tag{53.21}
$$

则精确有

$$
\min\{\widetilde b_v(\Psi_n(z_1)),\widetilde b_v(\Psi_n(z_2))\}
=b_v(\Psi_n(\gamma))=b_v(\Psi_n(\gamma_0)).
\tag{53.22}
$$

不要求 $z_1,z_2$ 在实平面线性独立，也不要求它们或 $\gamma$ 与 $p$ 互素；gcd 的单位选择不影响等式。

**证明。** Gaussian PID 与 Bézout 是成熟输入，见 Conrad，[*The Gaussian Integers*，定理 3.1、4.3、5.1](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/Zinotes.pdf)；这里不重复其 Euclidean 证明。固定定理 53.2 中的 $\tau\in D_v$，它在系数上作用为 $J$。对 $\alpha=A+iB\in\mathbb Z[i]$，严格有

$$
\Psi_n(\alpha z)=[A]\Psi_n(z)+[B]\tau\Psi_n(z),\qquad
\widetilde b_v(\Psi_n(\alpha z))\ge\widetilde b_v(\Psi_n(z)).
\tag{53.23}
$$

后一式直接来自同地方等深及原深度子群；$\alpha=0$ 或 $z=0$ 只用无穷深度约定。取 $u,w,A_0,B_0\in\mathbb Z[i]$ 使

$$
z_1=\gamma u,\qquad z_2=\gamma w,\qquad
\gamma=A_0z_1+B_0z_2.
\tag{53.24}
$$

前两个等式及 (53.23) 给出左侧最小值不小于 $b_v(\Psi_n(\gamma))$。最后一个等式给出反向：$\Psi_n(\gamma)$ 是 $\Psi_n(z_1),\tau\Psi_n(z_1),\Psi_n(z_2),\tau\Psi_n(z_2)$ 的整数线性组合，故其深度不小于原最小值。若某个 $z_j=0$，取另一个作为 gcd，或使用同一组等式，结论仍然成立。这给出第一项身份；再对 (53.21) 逐次使用定理 53.2 共 $a$ 次，得最后一项。单位 $\pm1,\pm i$ 分别由取负和同一地方的 $\tau$ 实现，均保深度。

这个 gcd 位于系数环 $\mathbb Z[i]$，不把 $\mathcal O_F$ 中的分母理想说成主理想，也不把 $P_2$ 认作 $[i]P_1$。Streng，*Divisibility sequences for elliptic curves with complex multiplication*，*Algebra & Number Theory* **2** (2), 183–208，DOI [10.2140/ant.2008.2.183](https://doi.org/10.2140/ant.2008.2.183)，[§2 与引理 3.3](https://msp.org/ant/2008/2-2/ant-v2-n2-p04-s.pdf)，给出负 $x$ 过滤与单点 CM 理想强整除性的先例。该文的指标作用来自一个固定点的真正自同态；(53.23) 来自两个原独立点在固定 $D_v$ 下的等距作用，须由实际共轭另行连接。

用白话说，两个组合都具有某一深度时，它们的局部四分之一转动及任意整数加减也有这层深度。Bézout 可以从这些组合取出 Gaussian gcd；反过来，两个原系数又是这个 gcd 的 Gaussian 整数倍，所以两边的共同深度完全相同。实际半点还使每个 $1+i$ 因子都不改变深度，可以全部删除。gcd 与删因子的精确局部关系是原共轭点的 repo-derived 综合，不主张一般 CM 强整除性的文献优先性。$\square$

## 54. 近正交两行在三个非标量类型上的同点联合预算

**定义 54.1（指定两行与非标量共同尾部）。** 对任意 $n,k\in\mathbb Z\setminus\{0\}$，取原点对上的两行

$$
m_k=(k,0),\qquad l_k=(1,k),\qquad
j_v(n,k)=\min\{b_v(T_{n,m_k}),b_v(T_{n,l_k})\}.
\tag{54.1}
$$

两点的高度分别为 $h_0n^2k^2$、$h_0n^2(1+k^2)$，故均非挠、非零。对任意素数集合 $\mathscr T\subseteq\mathscr N$、整数 $H\ge2$ 和非挠 $S\in E_0(F)$，定义原分母的相应截取及共同截取

$$
\begin{aligned}
B_{\mathscr T,H}(S)&=\prod_{\substack{p>H\\p\in\mathscr T}}\prod_{v\mid p}
\mathfrak p_v^{b_v(S)},\\
J_{\mathscr T,H}(n,k)&=\prod_{\substack{p>H\\p\in\mathscr T}}\prod_{v\mid p}
\mathfrak p_v^{j_v(n,k)},\qquad
G_{\mathscr T}(H;n,k)=\log\|J_{\mathscr T,H}(n,k)\|.
\end{aligned}
\tag{54.2}
$$

范数仍为 $N_{F/\mathbb Q}^{1/8}$，地方指数仍取原整数归一化。共同理想是两个分母理想之和的所写截取，指数取最小值；不要求理想为主理想。记 $G_{\mathscr N}$ 为三个非标量类型并集的质量。比较用的 $\mathcal A_H(n,u)=\log\|B(T_{n,u})^{>H}\|$ 始终是原定义 50.1 的完整尾部，不作类型限制。

**定理 54.2（精确共同深度与同一个原点的一次高度）。** 对全部 $n,k\in\mathbb Z\setminus\{0\}$、全部 $p\in\mathscr N$ 及每个固定 $v\mid p$，有

$$
j_v(n,k)=
\begin{cases}
b_v([n]P_1)=b_v([n]P_2),&p\in\mathscr R\sqcup\mathscr S,\\
\min\{b_v([n]P_1),b_v([nk]P_2)\},&p\in\mathscr D.
\end{cases}
\tag{54.3}
$$

因此对所有这些 $n,k$、所有整数 $H\ge2$，同一个点同时支付三个类型：

$$
\begin{gathered}
J_{\mathscr R\sqcup\mathscr S,H}(n,k)
=B_{\mathscr R\sqcup\mathscr S,H}([n]P_1),\\
J_{\mathscr N,H}(n,k)\mid B_{\mathscr N,H}([n]P_1),\\
0\le G_{\mathscr N}(H;n,k)
\le\log\|B_{\mathscr N,H}([n]P_1)\|
\le h_0n^2+\log2.
\end{gathered}
\tag{54.4}
$$

**证明。** 置 $A=[n]P_1$、$B=[n]P_2$。在 $p\in\mathscr R\sqcup\mathscr S$ 的固定 $v$，类型表给出 $g\in D_v$ 将 $P_1$ 送到 $\pm P_2$，也将 $P_2$ 送到 $\pm P_1$。所以 $b_v(A)=b_v(B)=a$。原深度子群及整数乘法给出

$$
b_v([k]A)\ge a,\qquad b_v(A+[k]B)\ge a,
\quad\text{因而 }j_v(n,k)\ge a.
\tag{54.5}
$$

若 $t=j_v(n,k)>0$，两点 $[k]A$、$A+[k]B$ 都在同一个 $U_v(t)$。将第一点用这个 $g$ 作用，得到 $\pm[k]B\in U_v(t)$，再从第二点求差，得到 $A\in U_v(t)$，即 $a\ge t$。若 $j_v=0$，反向不等式由非负性成立。因此准确有 $j_v=a$。此证明不除二，交换型的 $p=3$ 也包括在内。

在 $p\in\mathscr D$ 时，定理 53.3 给出

$$
b_v(A+[k]B)=\min\{b_v(A),b_v([k]B)\}.
\tag{54.6}
$$

又因 $b_v([k]A)\ge b_v(A)$，取共同最小值立即得到 (54.3) 第二支，特别是 $j_v\le b_v(A)$。

这两支给出的都是同一个 $[n]P_1$ 的逐地方上界。将它们在全部所写地方同时相乘，得到 (54.4) 的身份和整除式。三个集合互不相交，故

$$
\begin{aligned}
G_{\mathscr N}(H;n,k)
&=\frac18\sum_{\substack{p>H\\p\in\mathscr N}}\sum_{v\mid p}
f_vj_v(n,k)\log p\\
&\le\frac18\sum_{\substack{p>H\\p\in\mathscr N}}\sum_{v\mid p}
f_vb_v([n]P_1)\log p
\le\log\|B([n]P_1)\|\\
&\le\widehat h([n]P_1)+\log2=h_0n^2+\log2.
\end{aligned}
\tag{54.7}
$$

最后一步直接复用原 (49.8) 的高度上界及原 (16.21)，不重新推导它们。这里合并的是同一个分母在互不相交支持上的局部项，因而只支付一次完整高度；不是对三个类型各付一次完整高度。素数的计数或密度没有代替带 $f_vb_v$ 权重的分母质量。

旋转支也可由定理 53.4 理解：两个 Gaussian 系数为 $k$、$1+ik$，而 $(1+ik)-ik=1$，所以其 gcd 为单位。但这个族的旋转、交换两支已经由上述直接求差证明；预算不依赖删除 $1+i$ 因子的步骤。删因子仍是适用于其它系数对的独立局部关系。

用白话说，第一行给出 $kP_1$，同地方交换便给出带符号的 $kP_2$，从第二行 $P_1+kP_2$ 一减就取回 $P_1$。所以这两份分母共同拥有的深度，不能超过同一个 $[n]P_1$。对角反射型用实际半点得到的最小值式补上同一个上界。三个类型落在不同的素数上，却都由这个点的同一份分母支付，合起来仍只是一份高度。这是所写原两行族的联合算术约束，不是一般独立点 gcd 的无条件小量定理。$\square$

**定理 54.3（三次预算下较小完整尾部的统一 $k^{-2}$ 份额）。** 固定原 $M\ge1$ 及定义 51.1 的全部固定数据。可取只依赖这些数据的 $C_0>0$、整数 $H_1\ge7$，使对所有整数 $H\ge H_1$，置

$$
\epsilon_H^{(3)}=\frac{C_0H^3}{q_H^2}\le\frac12,\qquad
\Gamma_H=\frac{1+\log2/(h_0q_H^2)}{1-\epsilon_H^{(3)}}
=1+O(H^3/q_H^2)\longrightarrow1.
\tag{54.8}
$$

则对全部 $n\in q_H\mathbb Z\setminus\{0\}$、全部 $k\in\mathbb Z\setminus\{0\}$ 同时有

$$
\begin{gathered}
\mathcal A_H(n,m_k)>0,\qquad \mathcal A_H(n,l_k)>0,\\
0\le
\frac{G_{\mathscr N}(H;n,k)}
{\min\{\mathcal A_H(n,m_k),\mathcal A_H(n,l_k)\}}
\le\frac{\Gamma_H}{k^2}.
\end{gathered}
\tag{54.9}
$$

其中 $O$ 常数只依赖固定原数据，$k$ 可随 $H,n$ 任意无界移动。这个族的夹角与整数行格满足

$$
\cos\varphi(m_k,l_k)=\frac{\operatorname{sgn}(k)}{\sqrt{1+k^2}},\qquad
\varphi(m_k,l_k)\longrightarrow\frac\pi2\quad(|k|\to\infty),
\qquad
\lambda_1(\mathbb Zm_k+\mathbb Zl_k)=|k|.
\tag{54.10}
$$

**证明。** 直接使用定理 51.3 的全移动参数估计 (51.17)，等价的双边形式已写在 (52.3)。增大固定 $C_0,H_1$ 后，对这里的全部 $H,n$ 和全部 $u\in\mathbb Z^2\setminus\{0\}$，同时有

$$
(1-\epsilon_H^{(3)})h_0n^2\|u\|_2^2
\le\mathcal A_H(n,u)
\le(1+\epsilon_H^{(3)})h_0n^2\|u\|_2^2.
\tag{54.11}
$$

这是原全部地方上的完整 $>H$ 尾部，特别没有只保留 $\mathscr N$ 类型。因 $\|m_k\|_2^2=k^2$、$\|l_k\|_2^2=1+k^2$，两份尾部都为正，且其较小者至少为 $(1-\epsilon_H^{(3)})h_0n^2k^2$。无需断言实际两份尾部的大小次序。定理 54.2 遂给出

$$
\begin{aligned}
\frac{G_{\mathscr N}(H;n,k)}
{\min\{\mathcal A_H(n,m_k),\mathcal A_H(n,l_k)\}}
&\le\frac{h_0n^2+\log2}
{(1-\epsilon_H^{(3)})h_0n^2k^2}\\
&\le\frac{1+\log2/(h_0q_H^2)}
{(1-\epsilon_H^{(3)})k^2}.
\end{aligned}
\tag{54.12}
$$

最后只用了同一个 $n$ 满足 $|n|\ge q_H$。原 (16.27) 的 $\log q_H\sim H^2$ 给出 $\epsilon_H^{(3)}\to0$、$q_H\to\infty$；又有

$$
0\le\Gamma_H-1
=\frac{\epsilon_H^{(3)}+\log2/(h_0q_H^2)}{1-\epsilon_H^{(3)}}
=O(H^3/q_H^2).
\tag{54.13}
$$

并且所有 $H\ge H_1$ 上 $\Gamma_H\le2(1+\log2/h_0)$，故 $O(k^{-2})$ 对 $H,n,k$ 一致。负 $n$ 与负系数由取负保深度及同一群等式包括；$k=0$ 则第一行是零向量，未在量词内，也不写它的 $B(O)$。局部深度结论及 (54.4) 对任意非零 $n$ 成立；只有 (54.9) 需要周期倍数及足够大的 $H$。

为比较原行格界，直接算得 $\det(m_k,l_k)=k^2$、$|\sin\varphi|=|k|/\sqrt{1+k^2}$，点积为 $k$，给出 (54.10) 的角度公式，包括 $k<0$ 时的钝角。任意非零行格向量写为 $(ak+b,bk)$，$a,b\in\mathbb Z$。若 $b\ne0$，其第二坐标绝对值至少为 $|k|$；若 $b=0$，则 $a\ne0$，第一坐标绝对值至少为 $|k|$。而 $m_k$ 本身达到这个长度，故最短长度恰为 $|k|$。

因此原 (50.2) 的最短向量预算在此族仍为 $h_0n^2k^2+\log2$；原正弦界的正弦也趋于一。这两项既有通用界本身都不能给出 (54.9) 的 $k^{-2}$ 衰减。新增的约束来自固定地方的实际共轭和半点入口：它们把三个非标量类型的共同深度都交给长度为一的同一原方向。Gaussian PID、$D_4$、二挠、形式群及高度均是所引成熟或既有输入，(53.6)、(53.15)、(53.22) 与这个指定族的联合预算是 repo-derived 综合，不主张全球文献优先性。

用白话说，两行越长越接近直角，单靠整数行格并不能使它们的共同份额变小。同地方的旋转或交换却能从两行中取出固定短方向，对角反射则由实际半点补足入口。于是三个类型共同拥有的质量最多按 $n^2$ 增长，而两份完整尾部分别按 $n^2k^2$、$n^2(1+k^2)$ 增长。三次预算统一保证这个完整尾部主项，所以相除得到 $\Gamma_H/k^2$，且同一个系数趋于一。

所写比例不改成类型尾部之间的比例：没有给出 $B_{\mathscr N,H}(T_{n,m_k})$ 或 $B_{\mathscr N,H}(T_{n,l_k})$ 的正质量下界，素数类型密度不能提供这种下界。标量类型 $\chi_2=\chi_7=1$ 也不在联合整除式的支持内，因此不推出全部共同尾部满足同一上界。原周期、完整尾部和 (51.17) 仍包括二进、七进及所有其它地方；新局部类型并未删改它们。

这些都是共同质量的上界，允许 $G_{\mathscr N}=0$；既不提供共同正下界，也不证明组合间独立性。两行确实代表原点对的实际组合，但没有由此证明它们同时实现原先选定的短共振。一般非零有限目标的成功余类不必为 $q_H\mathbb Z$，故 (54.9) 不延伸到那些整数。原 $p_H(\alpha)$ 的正下界、原 (31.2)、负 $\vartheta$ 阶段的调和和发散及同一实际 $Y$ 上的满测，均不由这里的上界推出。$\square$

## 追加锚（本行以下为增补区）

## 55. 标量 Frobenius 的实际半点像与充分饱和入口

**定义 55.1（中央符号、倍二像与合格标量支持）。** 保持定义 51.1、53.1、54.1 的全部原数据，特别保留实际半点 $Q_1,Q_2$、原整数 $n,k$、全部地方及原过滤。记

$$
\mathscr L=\{p>7:\chi_2(p)=\chi_7(p)=1\}.
\tag{55.1}
$$

对 $p\in\mathscr L$，定义 53.1 的实际 Frobenius 系数作用为中央元 $\epsilon_p I$，其中 $\epsilon_p\in\{1,-1\}$。中央元的共轭类只有自身，故这个符号与 $v\mid p$ 的选择无关；以下每次作用仍只在一个固定地方内进行。这里 $\epsilon_p$ 是 Frobenius 本身在实际半点上的符号，不是原 (16.9) 中 Frobenius 平方的符号 $\varepsilon_p$；后一个符号在 $\mathscr L$ 上恒为 $1$。在当前特殊纤维的代数闭包内置

$$
\begin{gathered}
G_p^{\mathrm{sc}}=\ker(\pi_p-[\epsilon_p]),\qquad
N_p=p+1-\epsilon_p a_p,\qquad D_p=N_p/4,\\
A=[n]P_1,\qquad B=[n]P_2,\qquad
X=[k]A=T_{n,m_k},\qquad Y=A+[k]B=T_{n,l_k},\\
\mathcal H_v(n)=\langle\overline A,\overline B\rangle,
\qquad
\mathscr C_k=\{p\in\mathscr L:\gcd(k^2,D_p)\mid |k|\},
\qquad n,k\in\mathbb Z\setminus\{0\}.
\end{gathered}
\tag{55.2}
$$

下条证明 $D_p$ 是正整数。$A,B,X,Y$ 的非挠性直接由原 (16.21) 或 (53.3) 保证，特别不把约化中的 $O$ 当作全局点的零性。$\mathcal H_v(n)$ 仅为两个原点的整数生成群，不添加 CM 生成元，也不假定 $P_2=[i]P_1$。

**定理 55.2（半点把标量充分条件降到 $D_p$ 并控制实际入口）。** 对每个 $p\in\mathscr L$ 和每个固定 $v\mid p$，有

$$
\begin{gathered}
\overline Q_1,\overline Q_2\in G_p^{\mathrm{sc}},\qquad
\#G_p^{\mathrm{sc}}=N_p,\qquad
G_p^{\mathrm{sc}}[2]=\widetilde E_0[2],\\
\#[2]G_p^{\mathrm{sc}}=D_p,\qquad
\mathcal H_v(n)\subseteq[2]G_p^{\mathrm{sc}},\qquad
p\nmid N_p.
\end{gathered}
\tag{55.3}
$$

对每个非零整数 $k$，若 $p\in\mathscr C_k$，则在 $[2]G_p^{\mathrm{sc}}$ 上

$$
\ker[k^2]=\ker[k].
\tag{55.4}
$$

对全部非零整数 $n$，这个条件给出原两行的同地方入口

$$
X,Y\in U_v(1)
\quad\Longleftrightarrow\quad
A,[k]B\in U_v(1).
\tag{55.5}
$$

充分条件证书失败的位置精确为

$$
p\in\mathscr L\setminus\mathscr C_k
\quad\Longleftrightarrow\quad
\exists\text{ 素数 }\ell\mid |k|:
 v_\ell(D_p)>v_\ell(|k|).
\tag{55.6}
$$

右端只判定这个证书失败，不断言实际点的入口或 (55.4) 必然失败。

**证明。** 固定 $v$。定义 53.1 的半点作用给出 $g_vQ_j=[\epsilon_p]Q_j$，约化与算术 Frobenius 相容，故 $\pi_p\overline Q_j=[\epsilon_p]\overline Q_j$。这使用同一个实际半点的作用，不从 $\pi_p^2\overline Q_j=\overline Q_j$ 反推一次 Frobenius 的符号。

以下同源与有限群事实只作为本条实际入口的中间输入。Silverman，*The Arithmetic of Elliptic Curves*，第二版，[III.4.10(c)、III.5.6、III.6.3–6.4、V.1.1、V.2.3–2.3.1](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)，给出可分同源的核阶、微分判据、次数二次型及 Frobenius 的迹。它们用于当前算子时给出

$$
\deg(\pi_p-[\epsilon_p])=p+1-\epsilon_p a_p=N_p,
\qquad d(\pi_p-[\epsilon_p])=-\epsilon_p\ne0.
\tag{55.7}
$$

因此同源可分，几何核确有 $N_p$ 个点。原曲线的四个二挠点 $O,(0,0),(1,0),(-1,0)$ 都在 $\mathbb F_p$ 上；Frobenius 固定它们，两个符号在二挠上也都为恒等。因此全二挠都在 $G_p^{\mathrm{sc}}$ 内，而倍二在这个有限群上的核恰是这四点。纤维等势给出 $\#[2]G_p^{\mathrm{sc}}=N_p/4$。又因 $P_j=[2]Q_j$，其约化及全部整数倍都在这个倍二像内，证明所写包含关系。

Hasse 界在 $p>7$ 给出

$$
0<(\sqrt p-1)^2\le N_p
\le p+1+2\sqrt p<2p.
\tag{55.8}
$$

已经知道 $4\mid N_p$。如果 $p\mid N_p$，(55.8) 便迫使 $N_p=p$，与 $p$ 为奇素数且 $4\mid N_p$ 矛盾。故 $p\nmid N_p$，也有 $p\nmid D_p$。这里没有把 Hasse 大小界单独当作互素结论。

在有限群 $[2]G_p^{\mathrm{sc}}$ 内，若 $[k^2]Z=O$，Lagrange 给出 $\operatorname{ord}(Z)\mid D_p$，同时 $\operatorname{ord}(Z)\mid k^2$。在 $p\in\mathscr C_k$ 时，遂有 $\operatorname{ord}(Z)\mid\gcd(k^2,D_p)\mid |k|$，即 $[k]Z=O$。反向包含恒成立，证明 (55.4)。所用有限群输入见 Milne，[*Group Theory*，版本 4.01，定理 1.26、推论 1.27](https://www.jmilne.org/math/CourseNotes/GT.pdf)；这里只在原点所属的阶 $D_p$ 群内消费它。

若 $X,Y\in U_v(1)$，在同一个约化群内有

$$
[k]\overline A=O,\qquad
\overline A+[k]\overline B=O,\qquad
[k^2]\overline B=O.
\tag{55.9}
$$

因 $\overline B\in[2]G_p^{\mathrm{sc}}$，(55.4) 给出 $[k]\overline B=O$，再由第二式得 $\overline A=O$。好约化的核正是原 $U_v(1)$，故得到右侧入口；反向由子群性立即成立。约化核与形式群的经典对应见 Silverman 同书 VII.2.1–2.2。本证明没有在整个 $E_0(F_v)$ 上除以 $k$。

最后，令 $a=v_\ell(|k|)$、$d=v_\ell(D_p)$。整除条件在这个素数上是 $\min(2a,d)\le a$。若 $a=0$ 它恒成立；若 $a>0$，它恰等价于 $d\le a$，这证明 (55.6)。因为 $D_p\mid N_p$，旧的 $\gcd(k^2,N_p)\mid |k|$ 蕴含本条条件；反向不成立的实际例子见命题 57.2。

上述微分判据按作者[第二版勘误](https://www.math.brown.edu/johsilve/AEC/AECErrata.pdf)对 III.5.6(b) 的说明用于非零同源；这里 (55.8) 已排除零同源。实际点及半点的来源仍为 Brox 的[固定源码 “The quadratic-field elliptic curve” 与 `lem:independent`](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex)，归一化及带符号作用直接沿用 (53.1)、(53.8)–(53.9)。本条新增的是这些实际半点对原两行的 $D_p$ 充分入口，属 repo-derived 综合推导，不将有限群或 Frobenius 理论另立为新的一般结果。

用白话说，原点已经是实际半点的两倍，所以它们所处的有限群只需要取整个 Frobenius 核的倍二像，阶数便从 $N_p$ 降为 $N_p/4$。在这个较小群内，只要被 $k^2$ 杀掉的点也被 $k$ 杀掉，两行同时约化为零就能取回原方向 $[n]P_1$ 的入口。这个条件只是一张足够用的证书；证书不合格时，仍须看实际点，不能直接宣布入口失败。$\square$

## 56. 第一形式层内的深度增量与同一个平方分母

**定理 56.1（合格标量支持的无参数对数深度界）。** 对全部 $n,k\in\mathbb Z\setminus\{0\}$、全部 $p\in\mathscr C_k$ 及每个固定 $v\mid p$，置 $a=b_v(A)$、$j=j_v(n,k)=\min\{b_v(X),b_v(Y)\}$。则

$$
0\le j\le2a,\qquad
p\nmid k\ \Longrightarrow\ j\le a.
\tag{56.1}
$$

若 $j>0$，还有严格的一份深度节省

$$
a\ge1,\qquad j\le2a-1.
\tag{56.2}
$$

这些断言包括 $j=0$ 的情形和负 $n,k$，不要求 $n\in q_H\mathbb Z$。

**证明。** $j=0$ 时 (56.1) 由非负性成立，不使用形式群赋值公式，也不主张 (56.2)。以下假设 $j>0$。由 (55.5)，$A,[k]B\in U_v(1)$，故 $a\ge1$。

本处 $p>7$、$e_v=1$，原好整模型的第一形式层满足严格阈值 $1>e_v/(p-1)$。Silverman 同书 [IV.6.3–6.4、VII.2.2](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的形式对数在这个第一层是保赋值同构；其乘法线性化及原 $b_v(S)=\operatorname{ord}_v t(S)$ 仅对 $S\in U_v(1)\setminus\{O\}$ 使用，给出

$$
b_v([r]S)=b_v(S)+v_p(r)
\quad\bigl(0\ne r\in\mathbb Z,\ S\in U_v(1)\setminus\{O\}\bigr).
\tag{56.3}
$$

取负保赋值，故 $r$ 可为负。作者勘误对 IV.6.3(a) 区分分式域收敛与整环收敛；这里已在严格保赋值阈值之内，因而不依赖那个未经限制的整环收敛断言。与原定理 16.3 相同，第一层内的非零点及其非零整数倍不会落到 $O$。

写 $k=p^t u$，其中 $t=v_p(|k|)\ge0$、$u\in\mathbb Z\setminus\{0\}$、$p\nmid u$。先对已经进入第一层的 $A$ 使用 (56.3)，得到

$$
b_v(X)=a+t.
\tag{56.4}
$$

若 $t=0$，即得 $j\le a$，且 $a\le2a-1$。

设 $t>0$，置 $C=[u]B$。此刻尚未对 $B$ 或 $C$ 使用形式赋值公式。由 $[k]B\in U_v(1)$，有 $[p^t]\overline C=O$；又因 $\overline C\in[2]G_p^{\mathrm{sc}}$，其阶整除 $D_p$，而 $p\nmid D_p$。故 $\overline C=O$，即 $C$ 确实进入 $U_v(1)$。$C$ 为非挠非零点，所以 $d=b_v(C)\ge1$。现在才可用 (56.3) 得

$$
b_v([k]B)=b_v([p^t]C)=d+t\ge t+1.
\tag{56.5}
$$

若 $a\le t$，则 $b_v(A)=a<d+t=b_v([k]B)$。第一层内形式对数把 $Y=A+[k]B$ 化为两个不同赋值的数之和，因而准确有 $b_v(Y)=a$，再由 (56.4) 得 $j=a\le2a-1$。若 $a>t$，整数性给出 $t\le a-1$，于是

$$
j\le b_v(X)=a+t\le2a-1.
\tag{56.6}
$$

这穷尽 $t>0$ 的情形，并证明 (56.1)–(56.2)。只有先证明 $C\in U_v(1)$ 后才把乘 $p^t$ 的深度增量写成 $t$；$p\nmid D_p$ 用在有限约化群，形式对数用在第一形式层，两步没有混用。

用白话说，乘数里的 $p$ 次幂确实会增加第一行的深度，但第二行也含有同一 $p$ 次幂的项。如果原方向太浅，两个不同深度的项不能相消，第二行就把共同深度截在原深度；如果原方向足够深，那个增量已经小于原深度。两种情形都由同一个原方向的两份深度支付，且共同深度为正时还至少省去一层。这是原两行及合格标量支持的 repo-derived 局部推导，形式群定理仅为内部输入。$\square$

**定义 56.2（联合支持与原分母截取）。** 对固定非零整数 $k$，置

$$
\mathscr U_k=\mathscr N\sqcup\mathscr C_k,\qquad
\mathscr V_k=\{p\in\mathscr C_k:p\mid |k|\}.
\tag{56.7}
$$

将 (54.2) 的截取记号按同一个乘积公式用于任意素数集合 $\mathscr T$：对整数 $H\ge2$ 及非挠 $S\in E_0(F)$，置

$$
\begin{aligned}
B_{\mathscr T,H}(S)&=\prod_{\substack{p>H\\p\in\mathscr T}}\prod_{v\mid p}
\mathfrak p_v^{b_v(S)},\\
J_{\mathscr T,H}(n,k)&=\prod_{\substack{p>H\\p\in\mathscr T}}\prod_{v\mid p}
\mathfrak p_v^{j_v(n,k)},\qquad
G_{\mathscr T}(H;n,k)=\log\|J_{\mathscr T,H}(n,k)\|.
\end{aligned}
\tag{56.8}
$$

每个乘积因原分母的有限支持而有限；赋值和范数仍为原整 $x$ 分母及 $N_{F/\mathbb Q}^{1/8}$。对整理想，$I\mid J$ 指逐素理想指数不等式 $v_{\mathfrak p}(I)\le v_{\mathfrak p}(J)$。$\mathcal A_H(n,u)$ 继续指原全部地方的完整尾部。

**定理 56.3（合并非标量与合格标量支持只支付同一个平方分母）。** 对全部 $n,k\in\mathbb Z\setminus\{0\}$、全部整数 $H\ge2$，有精细整除式

$$
\begin{gathered}
J_{\mathscr U_k,H}(n,k)
\mid B_{\mathscr U_k,H}(A)\,B_{\mathscr V_k,H}(A)
\mid B(A)^2,\\
0\le G_{\mathscr U_k}(H;n,k)
\le\log\|B_{\mathscr U_k,H}(A)\|
   +\log\|B_{\mathscr V_k,H}(A)\|\\
\le2\log\|B(A)\|
\le2h_0n^2+2\log2.
\end{gathered}
\tag{56.9}
$$

这里两份都是同一个原点 $A=[n]P_1$ 的分母。没有额外的 $\log|k|$ 项，也不另付一份非标量高度。

**证明。** 在 $p\in\mathscr N$ 的每个固定 $v$，直接引用 (54.3) 的 $j_v\le b_v(A)$；在 $p\in\mathscr C_k$ 且 $p\nmid k$ 的每个 $v$，引用 (56.1) 的同一个上界；在 $p\in\mathscr V_k$，引用 $j_v\le2b_v(A)$。这三种支持互不相交，合起来正是

$$
j_v(n,k)\le
\bigl(1+\mathbf1_{\mathscr V_k}(p)\bigr)b_v(A)
\qquad(p\in\mathscr U_k).
\tag{56.10}
$$

零共同深度已经包括在这个逐地方不等式内；正共同深度时还可用 (56.2) 的加强，但 (56.9) 无需为它另设截取。逐素理想相乘给出第一个整除式。因为 $\mathscr V_k\subseteq\mathscr U_k$，右侧在每个地方至多使用 $B(A)$ 的两份指数，得到第二个整除式。范数取对数后，地方权重精确为

$$
\begin{aligned}
G_{\mathscr U_k}(H;n,k)
&=\frac18\sum_{\substack{p>H\\p\in\mathscr U_k}}
\sum_{v\mid p} f_v j_v(n,k)\log p\\
&\le\frac18\sum_{\substack{p>H\\p\in\mathscr U_k}}
\sum_{v\mid p} f_v b_v(A)\log p
+\frac18\sum_{\substack{p>H\\p\in\mathscr V_k}}
\sum_{v\mid p} f_v b_v(A)\log p.
\end{aligned}
\tag{56.11}
$$

原高度上界 (49.8) 及 $\widehat h(A)=h_0n^2$ 给出 (56.9) 最后一行。这一步只复用高度，不重证原尾部或高度理论。若 $\mathscr V_k$ 在 $>H$ 中为空，精细式还给出一次分母预算；一般情形保留两份统一上界。

用白话说，非标量地方和不整除 $k$ 的合格标量地方共同用第一份分母，只有整除 $k$ 的合格标量地方才可能再用第二份。它们都取自同一个 $[n]P_1$，所以联合账目最多是这个点的平方分母，合并以后仍是两份高度。逐地方已经吸收了 $p$ 次幂的增量，无需再把这些增量求和成 $\log|k|$。这个指定族的联合预算是 repo-derived 综合推导，不是对全部标量支持或一般独立点 gcd 的断言。$\square$

**推论 56.4（相对于较小完整尾部的 $2\Gamma_H/k^2$ 界）。** 固定原 $M\ge1$ 及定义 51.1 的全部固定数据，取定理 54.3 的 $C_0,H_1,\epsilon_H^{(3)},\Gamma_H$。对全部整数 $H\ge H_1$、全部 $n\in q_H\mathbb Z\setminus\{0\}$、全部 $k\in\mathbb Z\setminus\{0\}$，两份完整尾部均为正，且

$$
0\le
\frac{G_{\mathscr U_k}(H;n,k)}
{\min\{\mathcal A_H(n,m_k),\mathcal A_H(n,l_k)\}}
\le\frac{2\Gamma_H}{k^2},\qquad
\Gamma_H=1+O(H^3/q_H^2)\longrightarrow1.
\tag{56.12}
$$

其常数只依赖原固定数据，允许 $k$ 随 $H,n$ 无界移动。分母取完整尾部中的较小者，不改成 $\mathscr U_k$ 类型尾部。

**证明。** 直接引用 (54.11)，两行的完整尾部分别至少为

$$
(1-\epsilon_H^{(3)})h_0n^2k^2,
\qquad
(1-\epsilon_H^{(3)})h_0n^2(1+k^2),
\tag{56.13}
$$

二者都严格为正。以它们的共同下界除 (56.9)，再用 $|n|\ge q_H$，得到

$$
\frac{G_{\mathscr U_k}(H;n,k)}
{\min\{\mathcal A_H(n,m_k),\mathcal A_H(n,l_k)\}}
\le
\frac{2h_0n^2+2\log2}
{(1-\epsilon_H^{(3)})h_0n^2k^2}
\le\frac{2\Gamma_H}{k^2}.
\tag{56.14}
$$

系数的渐近式、统一性和周期范围完全沿用 (54.8)、(54.13)；这里不重新推导 $H^3$ 尾部预算。原全部地方、二进模型、七进分歧以及同一个 $q_H$ 均保留。

当 $H\ge H_1\ge7$ 时，未计入 $\mathscr U_k$ 的 $>H$ 素数恰为 (55.6) 所刻画的标量证书不合格支持。本推论不给这部分共同分母质量的上界，因而不推出全 gcd 的同一比例。也未给 $\mathscr U_k$ 类型尾部或共同尾部的正质量下界；素数计数密度不能替代 (56.11) 中的带深度分母质量。共同质量允许为零，一般有限目标的成功余类也不改成 $q_H\mathbb Z$。原短共振的同时实现、原 $p_H(\alpha)$ 的正下界、原 (31.2)、负 $\vartheta$ 阶段的调和和发散及原覆盖问题，仍各需其联合算术或覆盖论证。

用白话说，分子至多增长为两份 $n^2$ 高度，分母仍是原来两份完整尾部中较小的一份，其统一主项至少为 $n^2k^2$，所以比例至多为 $2\Gamma_H/k^2$。这只限制所列支持最多能共享多少，没有证明它们实际共享正质量，也没有替遗漏的标量支持支付预算。$\square$

## 57. 原点在 31 处的入口反例与 103 处的合格实例

**命题 57.1（实际原点的标量入口不能无条件成立）。** 在 $p=31$ 取一个满足 $\overline a=8$ 的原地方 $v$。它是标量地方，实际 $\epsilon_{31}=-1$，且

$$
a_{31}=0,\qquad N_{31}=32,\qquad D_{31}=8.
\tag{57.1}
$$

同一实际 $n=k=2$ 满足

$$
X=[4]P_1\in U_v(1),\qquad
Y=[2]P_1+[4]P_2\in U_v(1),\qquad
A=[2]P_1\notin U_v(1).
\tag{57.2}
$$

因此这里 $j_v(2,2)>0$ 而 $b_v(A)=0$，且 $31\notin\mathscr C_2$。这个整数 $n=2$ 对任意 $H\ge7$ 都不属于 $q_H\mathbb Z$，故不是原周期范围内的反例。

**证明。** 在 $\mathbb F_{31}$，$8^2=2$，而原被开方元素约化为

$$
\overline b^{\,2}=3-8=26,\qquad
\overline c^{\,2}=3+8=11.
\tag{57.3}
$$

$26^2=25$、$26^4=5$、$26^8=25$，因而 $26^{15}=25\cdot5\cdot25\cdot26=-1$。又 $26\cdot11=7=10^2$，故 $26,11$ 都是非平方。这给出固定 $a$ 而同时反转 $b,c$ 的实际 Frobenius，故 $\epsilon_{31}=-1$，且 $\chi_2(31)=\chi_7(31)=1$。原扩张在这里不分歧；在二次子域先取 $a\mapsto8$ 再延拓地方，便得到所写实际地方，$b,c$ 的约化位于其二次剩余域。

为求 $a_{31}$，仅使用奇特征下的点数公式

$$
a_p=-\sum_{x\in\mathbb F_p}\chi(x^3-x).
\tag{57.4}
$$

其经典出处为 Silverman 同书 [V.1.3](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)。当 $p\equiv3\pmod4$ 时，$\chi(-1)=-1$，$x$ 与 $-x$ 的贡献相消，$x=0$ 的贡献为零。因此 $a_{31}=0$，代入定义即得 (57.1)，无需逐点求和。

原坐标直接给出

$$
x(\overline P_1)=\frac{115-27\cdot8}{56}=22,
\qquad
x(\overline P_2)=\frac{115+27\cdot8}{56}=12
\quad\text{在 }\mathbb F_{31}.
\tag{57.5}
$$

这两个横坐标都不为 $0,1,-1$，故两个点的纵坐标都非零，倍点公式可用。原方程上

$$
x([2]S)=\frac{(x(S)^2+1)^2}{4x(S)(x(S)^2-1)}.
\tag{57.6}
$$

代入这两个实际横坐标，分别得到

$$
\begin{aligned}
x([2]\overline P_1)&=\frac{28}{3}=-1,\\
x([2]\overline P_2)&=\frac7{13}=22
\qquad\text{在 }\mathbb F_{31}.
\end{aligned}
\tag{57.7}
$$

因此 $[2]\overline P_1=T=(-1,0)\ne O$，$\overline P_1$ 的阶恰为 $4$；同时 $[2]\overline P_2=\pm\overline P_1$。于是

$$
\overline A=T\ne O,\qquad
\overline X=[4]\overline P_1=O,\qquad
\overline Y=T+[4]\overline P_2=T+T=O.
\tag{57.8}
$$

这证明 (57.2)。全局 $A,X,Y$ 仍由原高度式保证非零，故 $j_v>0$ 与 $b_v(A)=0$ 都是原分母的合法有限深度断言。条件在这里确实失败：$\gcd(2^2,8)=4\nmid2$，具体坏素因子为 $\ell=2$，$v_2(D_{31})=3>1=v_2(k)$。这个例子既显示无条件入口为假，也只在证书不合格处出现，不反驳定理 55.2 或 56.1。

最后，原 (16.12) 的 $n_5=5$ 及 (16.5) 保证 $H\ge7$ 时 $5\mid q_H$，故 $n=2\notin q_H\mathbb Z$。这里的反例是实际原点的局部反例，没有将一个不满足原周期前提的整数冒充周期反例。

用白话说，在这个实际地方，两行乘完以后都落到约化单位元，原方向却停在一个非零二挠点上。被 $k^2$ 消去的残留不能自动被 $k$ 消去，31 处正好把这个障碍实现出来。但原周期早已要求整数带有因子 $5$，所以这里的 $n=2$ 不属于那个周期问题。$\square$

**命题 57.2（103 处的倍二像条件对所有乘数成立）。** 原扩张 $F/\mathbb Q$ 在 $p=103$ 完全分裂，实际 $\epsilon_{103}=1$，且

$$
a_{103}=0,\qquad N_{103}=104,\qquad D_{103}=26=2\cdot13.
\tag{57.9}
$$

因此对全部 $k\in\mathbb Z\setminus\{0\}$ 有 $103\in\mathscr C_k$，定理 55.2、56.1 的入口与深度结论对这里全部非零 $n,k$ 成立。特别地，$k=2$ 时

$$
\gcd(4,N_{103})=4\nmid2,
\qquad
\gcd(4,D_{103})=2\mid2.
\tag{57.10}
$$

这是新充分条件严格扩大合格支持的固定素数实例，不断言此处任何组合具有共同正深度。

**证明。** 在 $\mathbb F_{103}$，原根可以同时取为

$$
\overline a=38,\quad \overline b=45,\quad
\overline c=12,\quad \overline{bc}=25,
\tag{57.11}
$$

因为

$$
38^2=2,\qquad45^2=68=3-38,\qquad
12^2=41=3+38,\qquad45\cdot12=25,\qquad25^2=7.
\tag{57.12}
$$

所有等式均在这个有限域中。原分裂多项式 $Z^4-6Z^2+7$ 的四根为 $\pm45,\pm12$，互不相同且全在 $\mathbb F_{103}$。原扩张在 $103$ 不分歧，故 Frobenius 在全部根上为恒等，分裂域的分解群平凡。这证明完全分裂及所写实际根的地方实现；其它地方的根由原符号排列运输。实际半点的 Frobenius 也为恒等，故 $\epsilon_{103}=1$，不是另行选取的符号。

因 $103\equiv3\pmod4$，(57.4) 的同一字符配对给出 $a_{103}=0$，遂有 $N_{103}=104$ 和 $D_{103}=26$。$26$ 平方自由；对每个 $\ell\mid |k|$，若 $\ell\mid26$ 则 $v_\ell(26)=1\le v_\ell(|k|)$，若不整除则其指数为零。因此 (55.6) 的失败条件对所有非零 $k$ 都不出现，即 $103\in\mathscr C_k$。直接代入 $k=2$ 给出 (57.10)。这里没有断言条件在任意标量素数都成立，只是用原实际半点实现了一个非空而且严格扩大的支持实例。

用白话说，103 处所有原根都已落在素域中，实际符号为正；整个核的阶为 $104$，但原点只需住在阶为 $26$ 的倍二像里。这个较小阶没有平方因子，所以任意乘数都通过证书，连旧条件挡住的 $k=2$ 也通过了。通过证书只保证前述蕴含关系；它不保证两行真的同时进入约化核，更不保证有正的共同分母质量。

特别地，$H\ge103$ 时这个固定素数不在 $>H$ 尾部，故它不提供随 $H$ 增长的合格尾部支持或正质量。命题 57.1–57.2 是原点上的 repo-derived 实例推导；字符点数、倍点公式和有限群输入仍为上述成熟理论，不主张新的点数公式或全球文献优先性。$\square$

## 追加锚（本行以下为增补区）

## 58. 倍二像的精确统一周期与扩大的同点平方分母预算

**定义 58.1（精确指数证书）。** 保持定义 51.1、53.1、54.1、55.1 的全部原数据。特别地，$F=\mathbb Q(a,b,c)$、$E_0:y^2=x^3-x$、原点 $P_j$、实际半点 $Q_j$、所有地方及原 $U_v$、原整 $x$ 分母、权重 $f_v/8$、$n,k$ 和 $q_H$ 均不变。固定 $p\in\mathscr L$ 及同一个 $v\mid p$，只取一次实际中央符号 $\epsilon=\epsilon_p\in\{1,-1\}$，置

$$
\begin{gathered}
G=G_p^{\mathrm{sc}}=\ker(\pi_p-[\epsilon]),\qquad
N=N_p=p+1-\epsilon a_p,\qquad D=D_p=N/4,\\
L=[2]G,\qquad e=e_p=\exp L,\\
A=[n]P_1,\quad B=[n]P_2,\quad X=[k]A,\quad Y=A+[k]B,\qquad
\mathcal H_v(n)=\langle\overline A,\overline B\rangle\subseteq L.
\end{gathered}
\tag{58.1}
$$

这里 $\pi_p$ 是 $p$ 次幂 Frobenius；$\epsilon$ 仍是它在实际 $Q_j$ 上的一次作用，不是 (51.6) 的平方作用符号。指数指消去有限群中所有元素的最小正整数，平凡群的指数取 $1$。定理 55.2 已给出 $\#G=N$、$\#L=D$、$p\nmid N$ 及所写包含关系。$\mathcal H_v(n)$ 仍只是整数生成群，不要求它为 $\mathbb Z[i]$ 子模。

对每个非零整数 $k$ 定义

$$
\begin{aligned}
\mathscr C_k^{\mathrm{exp}}
 &=\{p\in\mathscr L:\gcd(k^2,e_p)\mid |k|\},\\
\mathscr U_k^{\mathrm{exp}}&=\mathscr N\sqcup\mathscr C_k^{\mathrm{exp}},\qquad
\mathscr V_k^{\mathrm{exp}}=\{p\in\mathscr C_k^{\mathrm{exp}}:p\mid |k|\}.
\end{aligned}
\tag{58.2}
$$

任意素数集合上的 $B_{\mathscr T,H}$、$J_{\mathscr T,H}$、$G_{\mathscr T}$ 精确取定义 56.2；$j_v(n,k)=\min\{b_v(X),b_v(Y)\}$。完整尾部 $\mathcal A_H(n,u)$ 仍取定义 50.1，不作类型限制。

**定理 58.2（精确指数扩大原两行的充分入口与平方分母支持）。** 在定义 58.1 的原标量地方，普通支 $p\equiv1\pmod4$ 的当前 CM 作用满足

$$
\begin{gathered}
\operatorname{End}_{\overline{\mathbb F}_p}(\widetilde E_0)=\mathcal O=\mathbb Z[i],\qquad
\pi_p=\alpha+\beta i,\qquad \alpha,\beta\in\mathbb Z,\\
\alpha^2+\beta^2=p,\qquad 2\alpha=a_p,\qquad
g=g_p=\gcd(|\alpha-\epsilon|,|\beta|),\\
G\simeq\mathbb Z/g\mathbb Z\oplus\mathbb Z/(N/g)\mathbb Z,\qquad
2\mid g,\quad g\mid N/g,\\
L\simeq\mathbb Z/(g/2)\mathbb Z\oplus\mathbb Z/(N/(2g))\mathbb Z,
\qquad e=\frac{N}{2g},\qquad D=\frac g2e.
\end{gathered}
\tag{58.3}
$$

这里的 $i$ 来自当前约化作用 $[i](x,y)=(-x,iy)$；换成共轭嵌入只改变 $\beta$ 的符号，不改变 $g,e$。原普通标量地方还有

$$
\pi_p\equiv1\pmod{4\mathcal O},\qquad
\epsilon=1\Longrightarrow4\mid g,\qquad
\epsilon=-1\Longrightarrow v_2(g)=1.
\tag{58.4}
$$

超奇异支 $p\equiv3\pmod4$ 对两种实际 $\epsilon$ 均有

$$
a_p=0,\qquad N=p+1,\qquad
G\simeq\mathbb Z/2\mathbb Z\oplus\mathbb Z/((p+1)/2)\mathbb Z,
\qquad L\simeq\mathbb Z/D\mathbb Z,\qquad e=D.
\tag{58.5}
$$

这些有限群计算作为原两行消费者的内部输入，给出精确的统一核稳定判据

$$
\ker([k^2]|_L)=\ker([k]|_L)
\quad\Longleftrightarrow\quad
\gcd(k^2,e)\mid |k|.
\tag{58.6}
$$

因此 $\mathscr C_k\subseteq\mathscr C_k^{\mathrm{exp}}$。对每个 $p\in\mathscr C_k^{\mathrm{exp}}$、每个固定 $v\mid p$ 和全部非零 $n,k$，原两行满足

$$
\begin{gathered}
X,Y\in U_v(1)\quad\Longleftrightarrow\quad A,[k]B\in U_v(1),\\
0\le j_v(n,k)\le2b_v(A),\qquad
p\nmid k\Longrightarrow j_v(n,k)\le b_v(A),\\
j_v(n,k)>0\Longrightarrow b_v(A)\ge1,\quad
j_v(n,k)\le2b_v(A)-1.
\end{gathered}
\tag{58.7}
$$

对全部 $n,k\in\mathbb Z\setminus\{0\}$、全部整数 $H\ge2$，精细整除及同点预算为

$$
\begin{gathered}
J_{\mathscr U_k^{\mathrm{exp}},H}(n,k)
\mid B_{\mathscr U_k^{\mathrm{exp}},H}(A)
     B_{\mathscr V_k^{\mathrm{exp}},H}(A)
\mid B(A)^2,\\
0\le G_{\mathscr U_k^{\mathrm{exp}}}(H;n,k)
\le2\log\|B(A)\|\le2h_0n^2+2\log2.
\end{gathered}
\tag{58.8}
$$

取定理 54.3 的同一 $C_0,H_1,\epsilon_H^{(3)},\Gamma_H$，则对全部整数 $H\ge H_1$、$n\in q_H\mathbb Z\setminus\{0\}$ 及 $k\ne0$，有

$$
0\le
\frac{G_{\mathscr U_k^{\mathrm{exp}}}(H;n,k)}
{\min\{\mathcal A_H(n,m_k),\mathcal A_H(n,l_k)\}}
\le\frac{2\Gamma_H}{k^2},\qquad
\Gamma_H=1+O(H^3/q_H^2)\longrightarrow1.
\tag{58.9}
$$

分母的两份完整尾部均严格为正。常数与 $H,n,k$ 无关，允许 $k$ 无界移动。

对固定普通标量素数，存在某个非零 $k$ 使指数证书合格而 $D$ 证书不合格，当且仅当 $g>2$；超奇异支两个证书相同。对任一固定标量素数，所有非零 $k$ 都通过指数证书，当且仅当 $e$ 平方自由。

**证明。** 先在此消费者内计算统一周期。只使用以下成熟输入：Silverman，*The Arithmetic of Elliptic Curves*，第二版，[III.4.11、III.6.2、III.6.4、III.8.1、V.2.3–2.3.1、V.3.1、V.4.1(a)](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)，分别提供可分同源的核包含因子分解、对偶与次数、素于特征的完整挠点、Weil 配对及其 Galois 相容性、Frobenius 与普通性。有限交换群的不变因子取 Milne，[*Group Theory*，版本 4.01，§1 的 Summary 1.58](https://www.jmilne.org/math/CourseNotes/GT.pdf)。以下不把这些经典结果另列为新增定理。

由 (55.3)，$G\subseteq\widetilde E_0[N]$，且 $p\nmid N$，故完整挠点结构及有限交换群分解给出

$$
G\simeq\mathbb Z/d_1\mathbb Z\oplus\mathbb Z/d_2\mathbb Z,
\qquad d_1\mid d_2,\qquad d_1d_2=N.
\tag{58.10}
$$

全二挠在 $G$ 中，所以 $2\mid d_1$。对素于 $p$ 的正整数 $m$，$\widetilde E_0[m]\subseteq G$ 当且仅当 $m\mid d_1$：包含成立时 $G[m]$ 的阶必须为 $m^2$；由 (58.10) 这恰要求 $m\mid d_1,d_2$。反向同样由 $G[m]\subseteq\widetilde E_0[m]$ 及两边同为 $m^2$ 个点得到。因此 $d_1$ 是使完整 $m$ 挠都在 $G$ 中的最大素于 $p$ 的 $m$。

普通支的 CM 对应直接使用 (51.7)–(51.8)：Hasse 系数非零给出普通性；几何自同源环是虚二次序，包含当前忠实的 $\mathbb Z[i]$，而 $\mathbb Z[i]$ 已是 $\mathbb Q(i)$ 的极大整环，故自同源环恰为 $\mathcal O$。于是当前 $\pi_p$ 有唯一的 $\alpha+\beta i$ 表达，范数为 $p$、迹为 $2\alpha$。对素于 $p$ 的 $m$，将 Silverman III.4.11 用于可分的 $[m]$ 和非零的 $\pi_p-[\epsilon]$，得

$$
\begin{aligned}
\widetilde E_0[m]\subseteq\ker(\pi_p-[\epsilon])
&\Longleftrightarrow\pi_p-[\epsilon]=\lambda\circ[m]
     \quad(\lambda\in\operatorname{End}\widetilde E_0)\\
&\Longleftrightarrow m\mid\alpha-\epsilon,\quad m\mid\beta.
\end{aligned}
\tag{58.11}
$$

$N=(\alpha-\epsilon)^2+\beta^2$，故 $g^2\mid N$，特别 $p\nmid g$。比较 (58.10)–(58.11) 就得 $d_1=g,d_2=N/g$。倍二对这两个偶阶循环因子分别除去一个因子 $2$，并且第一因子仍整除第二因子；其指数正是第二因子 $N/(2g)$。这证明 (58.3)，包括完整的 $2$ 主部，没有先删去偶挠。

式 (58.4) 需要原曲线自身的四挠点。普通标量地方有 $(2/p)=1$ 且 $p\equiv1\pmod4$。在 $\mathbb F_p$ 取 $s^2=2,z^2=-1$，在原方程上置

$$
R_0=(z,1-z),\qquad R_1=(1+s,2+s).
\tag{58.12}
$$

确有 $(1-z)^2=-2z=z^3-z$，以及 $(2+s)^2=6+4s=(1+s)^3-(1+s)$。两个纵坐标均非零；原倍点公式的切线斜率分别为 $-1-z$、$1+s$，从而

$$
[2]R_0=(0,0),\qquad[2]R_1=(1,0).
\tag{58.13}
$$

右侧是独立二挠点。若 $uR_0+wR_1=O$，先倍二可知 $u,w$ 都为偶数，再用右侧的独立性可知二者均为 $4$ 的倍数。因此 $R_0,R_1$ 生成全部 $16$ 个四挠点，它们都在 $\mathbb F_p$ 上。于是 $\pi_p-1$ 消去完整四挠，再用 (58.11) 的因子分解，得到 $\pi_p-1\in4\mathcal O$。这给出 $\alpha\equiv1\pmod4$、$\beta\equiv0\pmod4$。实际 $\epsilon=1$ 时 $4\mid g$；实际 $\epsilon=-1$ 时 $\alpha+1\equiv2\pmod4$，故 $v_2(g)=1$。这里没有将负中央符号改成正号，也没有断言负号核含完整四挠。

超奇异支不把 $\pi_p$ 本身视为 Gaussian 整数。由 (57.4) 中 $x,-x$ 的字符相消，$a_p=0$，故两个 $\epsilon$ 都有 $N=p+1$。在 (58.10) 中取完整 $\widetilde E_0[d_1]\subseteq G$ 的一组基 $S,T$。Weil 配对的非退化性使 $\zeta=e_{d_1}(S,T)$ 为本原 $d_1$ 次单位根；其 Galois 相容性给出

$$
\zeta^p=e_{d_1}(\pi_pS,\pi_pT)
=e_{d_1}([\epsilon]S,[\epsilon]T)
=\zeta^{\epsilon^2}=\zeta.
\tag{58.14}
$$

因此 $d_1\mid p-1$；又 $d_1\mid N=p+1$，所以 $d_1\mid2$。全二挠已给出 $2\mid d_1$，遂有 $d_1=2,d_2=(p+1)/2$。倍二像为阶 $(p+1)/4=D$ 的循环群，证明 (58.5)。这里使用标准完整挠点的 Weil 配对，值域为 $\mu_{d_1}$，不使用一般同源配对的更强值域断言。上述挠点记号及配对按作者[第二版勘误](https://www.math.brown.edu/johsilve/AEC/AECErrata.pdf)中原书页 69、90、93–98 的说明理解，尤其 $E[m]$ 指阶整除 $m$ 的点。

现在求原入口。在两支的循环因子分解中，$L$ 都有一个阶恰为 $e$ 的循环因子。如果 $\gcd(k^2,e)\mid |k|$，任何被 $k^2$ 消去的元素，其阶整除 $\gcd(k^2,e)$，故也被 $k$ 消去。反之，令 $d=\gcd(k^2,e)$；阶 $e$ 的循环因子内有阶恰为 $d$ 的元素，核相等便要求 $d\mid |k|$。这证明 (58.6)。由于 $e\mid D$，旧 $D$ 证书蕴含指数证书。

当 $X,Y\in U_v(1)$ 时，原 (55.9) 在这个固定地方给出 $[k]\overline A=O$、$\overline A+[k]\overline B=O$、$[k^2]\overline B=O$。由 $\overline B\in L$ 及 (58.6)，得到 $[k]\overline B=O$，再得 $\overline A=O$。这正是 (58.7) 的入口，反向仍由子群性。只在 $L$ 内用了核稳定性，没有在整个约化群或局部椭圆曲线群上除以 $k$。

深度部分直接使用定理 56.1 的第一形式层论证 (56.3)–(56.6)。它需要的入口 (55.5) 已由刚证的入口替换；它排除约化 $p$ 挠所用的 $p\nmid D$ 仍由 (55.3) 保证；$p>7,e_v=1$、原形式参数、非挠性和保赋值阈值均相同。因此其 $j\le2b_v(A)$、$p\nmid k$ 时的一份深度，以及正共同深度时节省一层的三个结论，全部给出 (58.7)。这不是把只对旧 $\mathscr C_k$ 陈述的定理无条件用于更大集合，而是对其已写出的局部论证逐项提供同样的入口前提。

精细整除只需原 (56.10)–(56.11) 的逐地方乘积步骤：非标量地方引用 (54.3)；新增合格标量地方引用 (58.7)。参数对应是 $\mathscr U_k\mapsto\mathscr U_k^{\mathrm{exp}}$、$\mathscr V_k\mapsto\mathscr V_k^{\mathrm{exp}}$，而 $A,n,k,b_v,f_v/8$ 都不变。于是在联合支持上仍有

$$
j_v(n,k)\le
\bigl(1+\mathbf1_{\mathscr V_k^{\mathrm{exp}}}(p)\bigr)b_v(A).
\tag{58.15}
$$

按定义 56.2 的乘积取整除与归一化范数，再引用 (56.9) 的同一个高度上界，即得 (58.8)。这两份分母都来自同一个 $[n]P_1$；无需重造一般整除命题，也没有额外的 $\log|k|$。

最后在 (56.13)–(56.14) 中用 (58.8) 替换原分子上界即可：完整尾部及其 (54.11) 下界丝毫未变，较小完整尾部至少为 $(1-\epsilon_H^{(3)})h_0n^2k^2>0$。同一个 $|n|\ge q_H$ 给出 (58.9)。没有扩大原周期范围，二进、七进和所有其它地方仍在完整尾部内。

为精确比较证书，对任意正整数 $c$ 有

$$
\gcd(k^2,c)\mid |k|
\quad\Longleftrightarrow\quad
\forall\text{ 素数 }\ell\mid |k|:\ v_\ell(c)\le v_\ell(|k|).
\tag{58.16}
$$

这是 (55.6) 已用的逐素数判据，取 $c=e,D$ 即可。在固定普通地方，一个给定的 $k$ 新增合格，准确要求

$$
\left[\forall\ell\mid |k|:\ v_\ell(e)\le v_\ell(|k|)\right]
\quad\text{且}\quad
\left[\exists\ell\mid |k|:\ v_\ell(|k|)<v_\ell(D)\right].
\tag{58.17}
$$

若 $g=2$，则 $D=e$，无严格扩大。若 $g>2$，由 $g\mid N/g$ 可得 $g/2\mid e$。取任一 $\ell\mid g/2$，令 $k=\ell^{v_\ell(e)}$；这个指数至少为 $1$，而 $D=(g/2)e$ 保证 $v_\ell(D)>v_\ell(e)=v_\ell(k)$。因此该 $k$ 通过指数证书而不通过 $D$ 证书。普通正中央符号由 (58.4) 总有此种严格加强；普通负中央符号的二主部不产生这种差别，是否严格取决于 $g$ 的奇部是否大于 $1$。超奇异支则因 $e=D$ 没有差别。最后，$e$ 平方自由时 (58.16) 对所有非零 $k$ 成立；若 $\ell^2\mid e$，取 $k=\ell$ 即失败。这也包括 $e=1$ 的约定。

用白话说，群的阶只给出一个通用的消去整数；真正需要的是原半点倍二像的最短统一周期。普通地方的两个循环方向可以共享因子，用总阶作周期会把这些重叠也付进证书；精确指数保留全部偶挠后仍能删去这笔重复。入口一旦成立，原形式群和同点平方分母论证便原样接上。核稳定判据对整个 $L$ 是充要的，但对实际更小的 $\mathcal H_v(n)$ 仍只是充分证书；指数证书不合格不等于实际入口必然失败。

这里的新增承重内容是原两行在 $\mathscr U_k^{\mathrm{exp}}$ 上的同地方入口、同点平方分母及完整尾部预算，以及原曲线四挠所落实的严格性条件，属 repo-derived 综合推导。有限交换群、挠点、CM、同源因子分解与 Weil 配对均只在上述消费者内部引用，不主张这些经典工具的新意或全球文献优先性。$\square$

## 59. 1009 处的实际完全分裂、迹号与严格扩大

**命题 59.1（原数据在 1009 处区分两个证书）。** 原扩张 $F/\mathbb Q$ 在素数 $p=1009$ 完全分裂，其实际一次中央符号为 $\epsilon_{1009}=1$。在当前 CM 嵌入下有

$$
\begin{gathered}
\pi_{1009}=-15\pm28i,\qquad a_{1009}=-30,\qquad
N_{1009}=1040,\qquad g_{1009}=4,\\
G\simeq\mathbb Z/4\mathbb Z\oplus\mathbb Z/260\mathbb Z,\qquad
[2]G\simeq\mathbb Z/2\mathbb Z\oplus\mathbb Z/130\mathbb Z,\\
D_{1009}=260,\qquad e_{1009}=130.
\end{gathered}
\tag{59.1}
$$

符号 $\pm$ 只表示两种共轭 CM 嵌入；实际嵌入固定后只取其中一个。特别地，$k=2$ 时

$$
\gcd(4,260)=4\nmid2,\qquad
\gcd(4,130)=2\mid2,
\qquad1009\in\mathscr C_2^{\mathrm{exp}}\setminus\mathscr C_2.
\tag{59.2}
$$

更一般地，$1009$ 对所有非零 $k$ 都在 $\mathscr C_k^{\mathrm{exp}}$ 中，而旧 $D$ 证书恰在 $v_2(|k|)=1$ 时失败。

**证明。** 先确定原扩张的实际 Frobenius，再确定原曲线的迹。以下同余均在 $\mathbb F_{1009}$ 内。原 $a=\sqrt2$ 可以取剩余根 $439$，因为

$$
439^2=2+191\cdot1009,\qquad
469^2=-1+218\cdot1009.
\tag{59.3}
$$

因此 $469$ 也给出当前曲线作用所需的一个 $\sqrt{-1}$。原 $b,c$ 的平方在 $a\mapsto439$ 的地方分别为

$$
3-439=573,\qquad3+439=442,\qquad573\cdot442\equiv7.
\tag{59.4}
$$

二次互反律与补充律取 Stein，[*Elementary Number Theory: Primes, Congruences, and Secrets*，2017-01-23 版本，§4.1、定理 4.1.7](https://wstein.org/ent/ent.pdf)。由 $1009\equiv1\pmod{12}$、$1009\equiv1\pmod4$，且 $1009\equiv54\pmod{191}$、$1009\equiv1\pmod7$，给出

$$
\begin{aligned}
\left(\frac{573}{1009}\right)
&=\left(\frac3{1009}\right)\left(\frac{191}{1009}\right)
=\left(\frac{54}{191}\right)
=\left(\frac2{191}\right)\left(\frac3{191}\right)=1,\\
\left(\frac7{1009}\right)&=\left(\frac1{7}\right)=1.
\end{aligned}
\tag{59.5}
$$

最后一个乘积为 $1$ 是因为 $191\equiv7\pmod8$、$191\equiv-1\pmod{12}$。由 (59.4) 得 $442$ 也是非零平方。于是原分裂多项式 $Z^4-6Z^2+7$ 的四根 $\pm\overline b,\pm\overline c$ 全部在 $\mathbb F_{1009}$ 中且互不相同；取根的符号可使 $\overline{bc}$ 与原 $\sqrt7$ 的所选延拓相容。原扩张在 $1009$ 不分歧，故分解群在全部四根上为恒等，$F$ 完全分裂。特别地，实际 $Q_j\in E_0(F)$ 的约化被 Frobenius 固定，原中央元就是 $+I$，得到实际 $\epsilon_{1009}=1$。这里没有从平方作用推出一次作用，也没有更换原半点。

现由 $1009\equiv1\pmod4$ 及 (58.3) 写实际 $\pi=\alpha+\beta i$。直接的范数恒等式为

$$
1009=15^2+28^2=(15+28i)(15-28i).
\tag{59.6}
$$

Conrad，[*The Gaussian Integers*，§1、定理 6.3、6.6](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/Zinotes.pdf) 给出范数、素数范数的 Gaussian 素元及唯一分解。由此，范数为 $1009$ 的实际 $\pi$ 必是 $15+28i$ 或其共轭的单位倍，单位为 $\pm1,\pm i$。这一步只给出候选的单位与共轭类，并未决定迹号。

迹号由原曲线决定：$s=439,z=469$ 使 (58.12) 的两个实际四挠生成元都在 $\mathbb F_{1009}$ 上，故 (58.4) 强制

$$
\alpha\equiv1\pmod4,\qquad\beta\equiv0\pmod4.
\tag{59.7}
$$

单位 $\pm i$ 的两类把奇数 $15$ 放到虚部，不满足第二个同余；余下 $\alpha=15$ 或 $-15$ 中，只有 $-15\equiv1\pmod4$。因此实际 $\pi=-15\pm28i$，其迹必须为 $-30$。共轭号由当前 $[i]$ 决定，但不影响迹、$g$ 或指数。这不是从范数表示中任意选择正负迹，也无需逐点计数。

现在代入已经确定的实际 $\epsilon=1$：$N=1009+1-(-30)=1040$，$g=\gcd(16,28)=4$。式 (58.3) 遂给出 (59.1)，再直接得到 (59.2)。因为 $130=2\cdot5\cdot13$ 平方自由，指数证书对所有非零 $k$ 成立；$260=2^2\cdot5\cdot13$ 的旧证书按 (58.16) 恰在 $v_2(|k|)=1$ 时失败。所用整数、实际原点及原地方都没有重选。$\square$

(58.8)–(58.9) 因而在一个实际普通标量素数上增加了可用支持；当 $H<1009$ 且 $v_2(|k|)=1$ 时，两个所定义的 $>H$ 支持也由这个素数区分。不过这不证明该地方的共同深度为正，不证明两个共同分母质量严格不同。$H\ge1009$ 时这个固定例已离开 $>H$ 尾部，故它不保证任意大 $H$ 仍有严格扩大。

用白话说，1009 处的总倍二像有 $260$ 个元素，但它的所有元素每走 $130$ 步就统一归零。$k=2$ 的证书只需要这个周期，因此旧群阶证书挡住的实际地方被纳入同一平方分母预算。这个例子证明条件更强，没有提供任何带深度质量的正下界。

未通过指数证书的标量地方仍未取得这里的统一预算；即使证书合格，类型尾部与共同尾部的正分母质量仍未解决。素数合格性或素数计数密度不能代替 $f_vb_v\log p/8$ 的实际分母质量。原短共振的同时实现、原 $p_H(\alpha)$ 的正下界、原 (31.2)、负 $\vartheta$ 阶段的调和和发散及原覆盖目标仍需各自的联合算术与覆盖论证。新增内容是原曲线及原扩张的这个 repo-derived 实例和其消费者；经典挠点、Gaussian 分解与二次互反律均为内部成熟输入。

## 追加锚（本行以下为增补区）

## 60. 原深层周期在标量超奇异尾部的确定性共同质量

**定义 60.1（原周期、实际共同约化周期与完整标量尾部）。** 保持定义 51.1、53.1、54.1、55.1、56.2、58.1 的全部原数据。特别地，$F=\mathbb Q(a,b,c)$ 是原八次全实域，$E_0:y^2=x^3-x$ 是原整方程，$P_1,P_2$ 是原独立非挠点，$Q_j$ 是满足 $[2]Q_j=P_j$ 的原实际半点；不加入 $P_2=[i]P_1$ 的关系。全部地方、原 $U_v(r)$、原整 $x$ 分母 $B$ 及范数 $\|I\|=N_{F/\mathbb Q}(I)^{1/8}$ 均不变。对整数 $H\ge2$、$M\ge1$，严格沿用 [002 定义 13.1 的 (13.2)](UPPM_RG_002_DIOPHANTINE_DEFINITIONS_RELATIONAL_COMPILATION_AND_STOPPING_BOUNDARIES.md#13-实际共轭点在增长有限位与加深局部精度下的同整数缩靶返回)：

$$
\begin{aligned}
d_{v,j}(r)&=\operatorname{ord}_{E_0(F_v)/U_v(r)}(P_j+U_v(r)),\\
q_H&=q(H,H;M)
=\operatorname{lcm}\bigl(M,\{d_{v,j}(H):p\le H,\ v\mid p,\ j=1,2\}\bigr),\\
H_*&=82^{128}.
\end{aligned}
\tag{60.1}
$$

这里的 $q_H$ 是深度也等于 $H$ 的原周期，不是第一层共同约化周期的最小公倍数。置

$$
\begin{gathered}
S_0=\{p>7:\ p\bmod56\in\{31,47,55\}\},\qquad
\vartheta_{S_0}(x)=\sum_{\substack{p\le x\\p\in S_0}}\log p,\\
B_0(H)=\vartheta_{S_0}(4H-1)-\vartheta_{S_0}(H).
\end{gathered}
\tag{60.2}
$$

对每个 $p\in S_0$ 及原地方 $v\mid p$，在同一个约化群内定义

$$
o_v=\operatorname{lcm}\bigl(\operatorname{ord}(\overline P_1),
                            \operatorname{ord}(\overline P_2)\bigr),\qquad
r_{v,H}=\frac{o_v}{\gcd(o_v,q_H)}.
\tag{60.3}
$$

约化为 $O$ 的点的阶取 $1$。$o_v$ 是实际两点的共同约化周期，与坏地方的深度阈值 $s_v$ 无关；保留地方指标，不以环境群的阶代替它。

对原两行 $m_k=(k,0)$、$l_k=(1,k)$，仍置 $A=[n]P_1$、$B=[n]P_2$、$X=[k]A$、$Y=A+[k]B$ 及 $j_v(n,k)=\min\{b_v(X),b_v(Y)\}$。本节的完整量就是定义 56.2 在 $S_0$ 上的量：

$$
G_{S_0,H}(n,k):=G_{S_0}(H;n,k)
=\frac18\sum_{\substack{p>H\\p\in S_0}}\log p
             \sum_{v\mid p}f_vj_v(n,k).
\tag{60.4}
$$

对有限实数端点 $H\le a\le b$，另记有限带截取

$$
G_{S_0;(a,b]}(n,k)
=\frac18\sum_{\substack{a<p\le b\\p\in S_0}}\log p
             \sum_{v\mid p}f_vj_v(n,k).
\tag{60.5}
$$

完整量的求和支持是全部 $p>H$；对每个固定非零 $n,k$，它因原分母的有限支持而有限。有限带只是其中一部分。

**定理 60.2（深层周期自动支付一整段共同第一层）。** 对所有整数 $M\ge1$、$H\ge H_*$，有

$$
\operatorname{lcm}(1,\ldots,H)\mid q_H.
\tag{60.6}
$$

对每个 $p\in S_0$、每个原 $v\mid p$，两种实际中央符号 $\epsilon_p=1,-1$ 均满足

$$
o_v\mid e_p=D_p=\frac{p+1}{4}.
\tag{60.7}
$$

特别地，对任意非零整数 $t,k$，取同一个 $n=q_Ht$。若 $H<p\le4H-1$ 且 $p\in S_0$，则在每个原地方 $v\mid p$ 同时有

$$
[n]P_1,[n]P_2\in U_v(1),\qquad
X,Y\in U_v(1),\qquad j_v(n,k)\ge1.
\tag{60.8}
$$

因而完整共同尾部满足

$$
G_{S_0,H}(q_Ht,k)
\ge G_{S_0;(H,4H-1]}(q_Ht,k)
\ge B_0(H)
=\left(\frac38+o(1)\right)H.
\tag{60.9}
$$

$S_0$ 在全部素数中的相对密度为 $1/8$；(60.9) 的 $o(1)$ 只依赖固定模数 $56$，与 $M,t,k$ 无关。这里断言实际共同周期整除 $D_p$，不断言 $o_v=D_p$。

**证明。** 首先直接使用 [002 定理 16.8 的 (16.30)–(16.36)](UPPM_RG_002_DIOPHANTINE_DEFINITIONS_RELATIONAL_COMPILATION_AND_STOPPING_BOUNDARIES.md#16-实际共同周期的二次对数主阶交叉因子吸收与加权入口余项)。该上游结论对全部 $H\ge H_*$ 和全部 $M\ge1$ 给出

$$
q_H=\operatorname{lcm}\left(M,\prod_{\ell\le H}\ell^{b_\ell(H)}\right),
\qquad
b_\ell(H)\ge\frac{2\log H}{\log2}
\ge\left\lfloor\frac{\log H}{\log\ell}\right\rfloor.
\tag{60.10}
$$

自身指数的第一个下界分别来自原 $b_2=\kappa(H)$、$b_7=\lceil(H-1)/2\rceil$ 及其余 $b_\ell\ge H/2$，它们的统一比较正是原 (16.36)。因此包括 $2,7$ 在内的每个 $\ell\le H$ 都已提供 $1,\ldots,H$ 所需的全部 $\ell$ 指数。用

$$
\operatorname{lcm}(1,\ldots,H)
=\prod_{\ell\le H}\ell^{\lfloor\log H/\log\ell\rfloor}
$$

即得 (60.6)。这里保留最小公倍数中的 $M$；完全不需要原 (16.32) 的 $H_M$，也不删除或重新估计原深层周期的任何因子。

其次，$S_0$ 的每个剩余类都为 $7\pmod8$ 及 $3\pmod4$。模 $7$ 的非零平方为 $1,2,4$，而 $31,47,55$ 的模 $7$ 剩余分别为 $3,5,6$。二次互反律遂给出

$$
(2/p)=1,\qquad (7/p)=-(p/7)=1,\qquad p\equiv3\pmod4.
\tag{60.11}
$$

反过来，这三个条件经模 $8$ 与模 $7$ 的 CRT 恰给出所写三个模 $56$ 类。因此 $S_0$ 正是原标量支持 $\mathscr L$ 的超奇异支，没有对实际中央符号作额外筛选。

在每个固定 $v$，定理 55.2 让原半点满足 $\overline Q_j\in\ker(\pi_p-[\epsilon_p])$，原两点满足 $\overline P_j\in L=[2]\ker(\pi_p-[\epsilon_p])$。定理 58.2 的超奇异公式 (58.5) 对两种实际 $\epsilon_p$ 都给出 $a_p=0$ 及 $\exp L=\#L=D_p=(p+1)/4$。在这个同一个有限群中，每个实际点的阶整除其指数，故两点的共同周期 $o_v$ 整除 $D_p$。这里仅消费该有限群输入；阶的整除性亦见 Milne，[*Group Theory*，版本 4.01，定理 1.26、推论 1.27](https://www.jmilne.org/math/CourseNotes/GT.pdf)。这证明 (60.7)，没有把原两点说成环境循环群的生成元。

对任何 $p\in S_0$，好约化的核就是原 $U_v(1)$，所以实际整数条件准确为

$$
\begin{aligned}
[q_Ht]P_1,[q_Ht]P_2\in U_v(1)
&\Longleftrightarrow o_v\mid q_Ht\\
&\Longleftrightarrow r_{v,H}\mid t.
\end{aligned}
\tag{60.12}
$$

约化核及第一形式层的对应是 Silverman，*The Arithmetic of Elliptic Curves*，第二版，[VII.2.1–2.2，印刷页 188–191](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的成熟输入，参数对应始终是原 $F_v,E_0,U_v(1)$。若 $H<p\le4H-1$，则 $D_p$ 是不超过 $H$ 的正整数，故

$$
o_v\mid D_p\mid\operatorname{lcm}(1,\ldots,H)\mid q_H,
\qquad r_{v,H}=1.
\tag{60.13}
$$

于是同一个 $n=q_Ht$ 在每个原 $v\mid p$ 同时使两原点进入第一层。第一层是子群，故其整数线性组合 $X=[k]A$、$Y=A+[k]B$ 也进入第一层。原点与两行点均由 (53.3) 保证非挠、非零；原整方程在好约化第一层中有 $b_v=\operatorname{ord}_v(-x/y)\ge1$，所以 $j_v\ge1$。这仅使用前向入口，不使用 $\gcd(k^2,D_p)\mid|k|$、$D_p$ 平方自由或反向饱和证书。

现在逐个地方支付范数权重。原 $F$ 在 $p>7$ 不分歧，故 $e_v=1$、$\sum_{v\mid p}f_v=8$。不论实际中央符号给出 $f_v=1$ 还是 $2$，每个带内素数都满足

$$
\frac18\sum_{v\mid p}f_vj_v(q_Ht,k)\log p
\ge\frac18\sum_{v\mid p}f_v\log p=\log p.
\tag{60.14}
$$

求和得到 (60.9) 的两个不等式。完整量还含带外所有非负贡献；这里只对有限带写出这笔确定性下界。

最后在这个质量消费者内引用固定模 AP 素数定理：Clary–Fabrykowski，*Arithmetic progressions, prime numbers, and squarefree integers*，Czech. Math. J. **54** (2004)，915–927，[印刷页 918，式 (2)](https://dml.cz/bitstream/handle/10338.dmlcz/127940/CzechMathJ_54-2004-4_8.pdf)。其中误差的幂参数取 $4$，模数取 $56$，剩余类取 $31,47,55$；三者均与 $56$ 互素，而 $\varphi(56)=24$。该式给出各类的 $\pi(x;56,a)=\operatorname{li}(x)/24+O(x/\log^4x)$，固定模数处的有限初段可吸收入常数。对这三个类部分求和，存在只依赖模数 $56$ 的常数 $A_0>0$，使

$$
\vartheta_{S_0}(x)=\frac{x}{8}+R(x),\qquad
|R(x)|\le A_0\frac{x}{\log^2x}\quad(x\ge2).
\tag{60.15}
$$

具体地，$\vartheta_{S_0}(x)=\pi_{S_0}(x)\log x-\int_2^x\pi_{S_0}(u)\,du/u$；主项为 $(x-2)/8$，误差乘 $\log x$ 及其积分都被所写较宽界吸收。于是

$$
B_0(H)=\frac{3H-1}{8}+O\!\left(\frac{H}{\log^2H}\right)
=\left(\frac38+o(1)\right)H.
\tag{60.16}
$$

同一 AP 定理与全部素数的素数定理给出相对密度 $3/24=1/8$。密度只用于解释已经逐地方取得的质量渐近，没有代替入口证明；该论文的平方自由筛选结论未被使用。

用白话说，原深层周期不只处理 $H$ 以下的地方：它已含有从 $1$ 到 $H$ 的每一个整数周期。这里一段 $H$ 以上的实际素数，其原半点倍二像的周期仍不超过 $H$，所以同一把深层钥匙也自动打开它们的第一层。每个地方都开锁后，付清全部 $f_v/8$，每个素数才确实贡献一份 $\log p$。所得线性 $H$ 量来自原分母，不来自把素数密度当作分母深度。$\square$

## 61. 不相交素数支持上的实际有限平均与额外对数增益

**定义 61.1（同一原周期上的有限平均）。** 对任意整数 $N\ge H\ge H_*$、$M\ge1$ 及任意非零整数列 $\boldsymbol{k}=(k_1,\ldots,k_N)$，置

$$
\mathcal M_{H,N}(\boldsymbol{k})
=\frac1N\sum_{t=1}^N G_{S_0,H}(q_Ht,k_t).
\tag{61.1}
$$

允许 $k_t$ 随 $t,H,N,M$ 任意移动。每个求和项中的全部地方和两原点始终共用同一个 $n=q_Ht$。

**定理 61.2（确定性质量与额外平均增益相加）。** 存在常数 $C\ge0$，与 $H,N,M,q_H$ 及全部 $k_t$ 无关，使定义 61.1 的每个平均都满足以下有限 floor 下界及其统一后果：

$$
\begin{aligned}
\mathcal M_{H,N}(\boldsymbol{k})
&\ge B_0(H)
 +\frac1{8N}\sum_{\substack{4H-1<p\le4N-1\\p\in S_0}}
       \log p\sum_{v\mid p}f_v
       \left\lfloor\frac N{r_{v,H}}\right\rfloor\\
&\ge B_0(H)
 +\frac1N\sum_{\substack{4H-1<p\le4N-1\\p\in S_0}}
       \log p\left\lfloor\frac{4N}{p+1}\right\rfloor\\
&\ge B_0(H)+\frac12\log\frac NH-C.
\end{aligned}
\tag{61.2}
$$

空带的和为零，故 $N=H$ 也在量词内。首行保留实际共同周期；后两行只使用 $o_v\mid D_p$，不要求 $o_v=D_p$ 或 $p\nmid q_H$。

**证明。** 在每个固定 $p\in S_0$、$v\mid p$，(60.12) 给出两原点共同第一层的准确整数条件 $r_{v,H}\mid t$。一旦此条件成立，子群性就使任意原两行也进入第一层，故对每个非零 $k_t$ 都有

$$
j_v(q_Ht,k_t)\ge\mathbf1_{r_{v,H}\mid t},\qquad
\sum_{t=1}^N\mathbf1_{r_{v,H}\mid t}
=\left\lfloor\frac N{r_{v,H}}\right\rfloor.
\tag{61.3}
$$

这是同一实际地方上的有限计数，不要求不同素数或不同地方的条件独立。更一般地，对每个有限 $Z\ge H$，完整平均都有下界

$$
\mathcal M_{H,N}(\boldsymbol{k})
\ge\frac1{8N}\sum_{\substack{H<p\le Z\\p\in S_0}}
 \log p\sum_{v\mid p}f_v
 \left\lfloor\frac N{r_{v,H}}\right\rfloor.
\tag{61.4}
$$

这里只交换有限个求和，右侧是入口事件供应的第一层质量，不是完整平均的等式。

为合法相加，取 $Z=4N-1$，先把其中的支持分成 $(H,4H-1]$ 与 $(4H-1,4N-1]$。第一带的每个 $r_{v,H}=1$，其 (61.4) 贡献恰为 $B_0(H)$；第二带保留原 floor 计数。这证明 (61.2) 首行。两带没有共同素数，第一带内可能更深的贡献及 $p>4N-1$ 的贡献仍留在完整量中，均未再次计入。

对第二带每个素数，实际周期满足

$$
1\le r_{v,H}\le o_v\le D_p=\frac{p+1}{4}\le N,
\qquad
\left\lfloor\frac N{r_{v,H}}\right\rfloor
\ge\left\lfloor\frac{4N}{p+1}\right\rfloor.
\tag{61.5}
$$

因此逐个 $v$ 降低 floor 后，再用 $\tfrac18\sum_{v\mid p}f_v=1$，得到 (61.2) 第二行。即使 $p$ 已因 $M$ 或其它原周期因子而整除 $q_H$，(60.3)、(61.3)–(61.5) 仍完全有效。

以下仅在这一消费者内把已经取得的有限素数质量换成对数下界。记 $a=4H-1$、$b=4N-1$，则 $b\ge a\ge3$。由 $\lfloor u\rfloor\ge u-1$，第二带的贡献至少为

$$
4\sum_{\substack{a<p\le b\\p\in S_0}}\frac{\log p}{p+1}
-\frac{\vartheta_{S_0}(b)-\vartheta_{S_0}(a)}N.
\tag{61.6}
$$

利用同一个 (60.15) 作 Stieltjes 部分求和，端点包括关系保持为 $(a,b]$，准确得到

$$
\begin{aligned}
\sum_{\substack{a<p\le b\\p\in S_0}}\frac{\log p}{p+1}
&=\frac18\log\frac{b+1}{a+1}+E(a,b),\\
E(a,b)&=\frac{R(b)}{b+1}-\frac{R(a)}{a+1}
       +\int_a^b\frac{R(x)}{(x+1)^2}\,dx.
\end{aligned}
\tag{61.7}
$$

当 $a=b$ 时两边均为零。对全部 $b\ge a\ge3$，同一个误差常数给出

$$
\begin{aligned}
|E(a,b)|
&\le A_0\left(\frac2{\log^2a}
               +\int_a^b\frac{dx}{x\log^2x}\right)\\
&\le A_0\left(\frac2{\log^2a}+\frac1{\log a}\right)
\le C_1,
\qquad
C_1=A_0\left(\frac2{\log^2 3}+\frac1{\log3}\right).
\end{aligned}
\tag{61.8}
$$

又有

$$
0\le\frac{\vartheta_{S_0}(b)-\vartheta_{S_0}(a)}N
\le\frac{\vartheta_{S_0}(b)}N
\le4\left(\frac18+\frac{A_0}{\log^2 3}\right)=:C_2.
\tag{61.9}
$$

这里 $b/N<4$，而非对固定 $H$ 先令 $N$ 趋于无穷。由于 $(b+1)/(a+1)=N/H$，把 (61.7)–(61.9) 代入 (61.6)，即可取

$$
C=4C_1+C_2
\tag{61.10}
$$

完成 (61.2)。此常数只依赖已经固定的 AP 误差常数；它对全部整数 $N\ge H\ge H_*$ 同时有效，不含 $q_H$、$M$ 或移动参数。这里只引用固定模数的成熟误差估计，不另立一个 AP 定理，也不要求数值明确的误差常数。

用白话说，第一段素数在每个 $t$ 都已交足一份质量；额外平均只向更远的一段素数收费。远处每个实际共同周期不超过 $(p+1)/4$，在前 $N$ 个倍数中恰有一个可写出的 floor 次数保证两点共同进入第一层。三个剩余类的密度乘上这个因子 $4$，才在付清地方权重后给出 $\tfrac12\log(N/H)$；两段质量的支持不交，所以可以相加。$\square$

## 62. 同一整数对全部移动两行的存在性与固定阶段增长

**定理 62.1（共同最小关系在本消费者内的统一选择）。** 取定理 61.2 的同一个常数 $C$。对全部整数 $M\ge1$、$N\ge H\ge H_*$，存在一个整数 $1\le t_N\le N$，使全部非零整数 $k$ 在这个同一个 $n=q_Ht_N$ 上同时满足

$$
G_{S_0,H}(q_Ht_N,k)
\ge B_0(H)+\frac12\log\frac NH-C.
\tag{62.1}
$$

对每个固定的 $M\ge1$、$H\ge H_*$，存在无界的正整数集合 $\mathcal T_{H,M}$，使

$$
\forall t\in\mathcal T_{H,M}\quad\forall k\in\mathbb Z\setminus\{0\}:\qquad
G_{S_0,H}(q_Ht,k)
\ge B_0(H)+\frac12\log\frac tH-C.
\tag{62.2}
$$

特别地，逐 $t$ 的最小值可由同一个 $k=1$ 取得，而且

$$
\limsup_{t\to\infty}
\frac{\min_{k\in\mathbb Z\setminus\{0\}}G_{S_0,H}(q_Ht,k)-B_0(H)}{\log t}
\ge\frac12.
\tag{62.3}
$$

所以对任意无限移动非零整数列 $(k_t)_{t\ge1}$，同样有

$$
\limsup_{t\to\infty}
\frac{G_{S_0,H}(q_Ht,k_t)-B_0(H)}{\log t}
\ge\frac12.
\tag{62.4}
$$

**证明。** 只在本消费者内复用 [003 定理 50.2 的逐地方行格基无关性及 (50.5)–(50.6)](UPPM_RG_003_CONJUGATE_CM_RESONANCE_RANK_AND_COVERAGE.md#50-原行格约束下的共同尾部纯夹角界与实际剪切族)，以及本卷定义 53.1 的原深度子群性质。参数对应如下：固定同一个 $n$，标准行 $(1,0),(0,1)$ 对应 $A=[n]P_1,B=[n]P_2$；$k=1$ 时的行 $(1,0),(1,1)$ 是 $\mathbb Z^2$ 的另一组基。因此在每个原地方 $v$ 同时有

$$
j_v(n,1)=\min\{b_v(A),b_v(A+B)\}
        =\min\{b_v(A),b_v(B)\}.
\tag{62.5}
$$

对任意非零整数 $k$，两行 $(k,0),(1,k)$ 都在同一个 $\mathbb Z^2$ 中，原有的子群性质让其线性组合保留两标准行的共同最小深度。所以

$$
j_v(n,k)\ge\min\{b_v(A),b_v(B)\}=j_v(n,1)
\quad\text{对全部原 }v\text{ 同时成立}.
\tag{62.6}
$$

所引原行格关系使用原整 $x$ 分母的子群 $V_v(a)$，包括 $2,7$ 及所有分歧地方；在本节 $S_0$ 上它又是原好约化过滤 $U_v(a)$。故没有更换分母、地方或深度归一化。中间的 $O$ 仍只用原 $\widetilde b_v(O)=+\infty$ 参与子群论证，原 $A,B,X,Y$ 自身均由非挠性保证分母合法。这不是针对每个地方另外挑选一个 $k$：在全部地方同时取得最小值的始终是 $k=1$。

按原权重对 (62.5)–(62.6) 求和，令

$$
\begin{aligned}
\mathcal F_{H,M}(t)&=G_{S_0,H}(q_Ht,1)\\
&=\frac18\sum_{\substack{p>H\\p\in S_0}}\log p
        \sum_{v\mid p}f_v
        \min\{b_v([q_Ht]P_1),b_v([q_Ht]P_2)\}\\
&=\min_{k\in\mathbb Z\setminus\{0\}}G_{S_0,H}(q_Ht,k).
\end{aligned}
\tag{62.7}
$$

这是完整 $S_0$ 尾部的身份；各行的支持虽可随 $k$ 改变，逐地方非负不等式仍给出所写整体最小值。每个固定 $t\ne0$ 的 $\mathcal F_{H,M}(t)$ 都是有限实数。

现在在 (61.2) 中只取 $k_1=\cdots=k_N=1$，得到

$$
\frac1N\sum_{t=1}^N\mathcal F_{H,M}(t)
\ge B_0(H)+\frac12\log\frac NH-C.
\tag{62.8}
$$

从有限集合 $\{1,\ldots,N\}$ 选取使 $\mathcal F_{H,M}$ 最大的 $t_N$，最大值至少等于平均值；再用 (62.7) 的逐 $t$ 最小关系，即得同一个 $t_N$ 对全部 $k$ 的 (62.1)。这里没有交换平均与下确界。

固定 $H,M$。当 $N\to\infty$，(62.8) 的右端趋于无穷。对任意固定整数 $T$，有限个数 $\{\mathcal F_{H,M}(t):1\le t\le T\}$ 的最大值有限，所以所有充分大 $N$ 所选的 $t_N$ 都大于 $T$。故这些 $t_N$ 的集合无界，且因为 $t_N\le N$，

$$
\mathcal F_{H,M}(t_N)
\ge B_0(H)+\frac12\log\frac NH-C
\ge B_0(H)+\frac12\log\frac{t_N}H-C.
\tag{62.9}
$$

取这些 $t_N$ 的集合为 $\mathcal T_{H,M}$，再用 (62.7)，得到 (62.2)。沿其趋于无穷的子列，将 (62.9) 减去 $B_0(H)$ 并除以 $\log t_N$，右端趋于 $1/2$，证明 (62.3)。任意移动 $k_t$ 都逐项不小于同一个 $\mathcal F_{H,M}(t)$，所以 (62.4) 也成立。$\square$

上述消费者在 $S_0$、$H\ge H_*$、原周期倍数 $n=q_Ht\ne0$ 的范围内取得确定性 $B_0(H)$ 下界，并在同一原周期上取得额外的有限平均和无界子列增益。因此，§56.4、§59 末段关于尚无正质量下界的边界，在这个具体范围内由 (60.9)、(61.2) 与 (62.2) 精确补足；其中 $B_0(H)\sim3H/8$ 保证充分大阶段的线性正质量，未指定 AP 误差常数的数值或其正性起点。

对每个非零 $t$ 新取得的统一下界是 $B_0(H)$；对数 $t$ 的增长只在所证无界集合及 limsup 上断言，不推广成全部 $t$ 的逐项对数增长。这里没有 $n^2$ 比例的共同质量下界，没有对原全 gcd 的上界，也没有把平方自由子集赋予同一个 $1/8$ 密度或同一个 $1/2$ 平均系数。未通过指数证书的标量地方之上界、其余支持的联合估计、原短共振同时实现、原 $p_H(\alpha)$、原 (31.2)、负 $\vartheta$ 阶段的调和和发散及原覆盖目标，均不由这些下界解决。一般非零有限目标的成功余类仍不改成 $q_H\mathbb Z$。

这里承重的是原深层自身指数、实际半点倍二像与原带权分母之间的综合接口，连同不相交支持上的平均增益和同一整数的全参数选择。原 002 的完整高度与周期理论、原 003 的行格关系、本卷的半点及深度结构均直接复用；有限群、形式群、二次互反律与固定模 AP 素数定理只在这些消费者内部承担成熟中间输入，不被另立为新成果。来源范围限于所引原卷、Milne 的所列阶整除条目、Silverman 的所列约化与形式群条目，以及 Clary–Fabrykowski p918 式 (2) 的 AP 输入，不主张全球文献优先权。

用白话说，先给每个周期倍数一笔确定的底款，再在更远的素数上平均赚取对数增益。原行格关系提供了一把对全部地方都相同的尺：$k=1$ 已是共同质量最小的两行。只要它在某个 $t$ 达到平均保证，其它所有 $k$ 就在同一个 $t$ 一起达标；有限初段容不下持续变大的保证，所以达标的 $t$ 必须无界。所给下界仍远小于平方高度尺度。

## 追加锚（本行以下为增补区）

## 63. 实际中央特征子群的同地方扭曲与全深度循环性

**定义 63.1（精确局部特征与交过滤）。** 保持定义 51.1、53.1、58.1、60.1 的全部原数据。特别地，$F=\mathbb Q(a,b,c)$、$a^2=2$、$b^2=3-a$、$c^2=3+a$、实际半点 $Q_j$、独立原点 $P_j=[2]Q_j$、原整方程 $E_0:y^2=x^3-x$、所有原地方及过滤均不变。取

$$
S_0=\{p>7:p\bmod56\in\{31,47,55\}\},\qquad
D_p=(p+1)/4.
\tag{63.1}
$$

固定 $p\in S_0$ 和原地方 $v\mid p$。原 $F_v/\mathbb Q_p$ 不分歧，分解群由原算术 Frobenius $g_v$ 生成。沿用一次作用的实际中央符号 $\epsilon=\epsilon_p$，定义

$$
T_v=\{S\in E_0(F_v):g_vS=[\epsilon]S\},\qquad
K_v(j)=T_v\cap U_v(j)\quad(j\ge1).
\tag{63.2}
$$

这里要求的是完备域中点的精确等式，不是约化后的特征条件。$[2]T_v$ 表示倍二像，尚不把整个 $U_v(j)$ 放入这个像，也不把 $E_0(F_v)$ 的商当作特征子群的商。

**定理 63.2（原实际半点的全深度循环环境）。** 在定义 63.1 的每个原地方，两种实际符号均满足

$$
Q_1,Q_2\in T_v,\qquad P_1,P_2\in[2]T_v,\qquad
K_v(j)\subseteq[2]T_v\quad(j\ge1).
\tag{63.3}
$$

因此可定义有限群

$$
C_v(j)=[2]T_v/K_v(j),\qquad
C_v(j)\simeq\mathbb Z/(D_pp^{j-1})\mathbb Z.
\tag{63.4}
$$

同一个 $F_v$ 内存在单位 $d\in\mathbb Z_p^\times$、$s\in F_v^\times$、$s^2=d$，使单位二次扭曲

$$
E^{(d)}:Y^2=X^3-d^2X,\qquad
\phi_d(X,Y)=(X/d,Y/(ds))
\tag{63.5}
$$

将 $E^{(d)}(\mathbb Q_p)$ 同构到 $T_v$，并将其第 $j$ 形式层同构到 $K_v(j)$。此识别保留原赋值、原整 $x$ 分母的深度及原地方权重 $f_v/8$；不变更全局点或全局基域。

**证明。** 原 (53.8)–(53.9) 从实际坐标给出精确符号作用。这里 $\chi_2(p)=\chi_7(p)=1$，故 $g_v$ 固定 $a$，并有

$$
g_v(b)=\epsilon b,\qquad g_v(c)=\epsilon c.
\tag{63.6}
$$

将它直接代入原

$$
Q_1=((1+a)/b^2,2a/b^3),\qquad
Q_2=((1-a)/c^2,-2a/c^3)
$$

得到 $g_vQ_j=[\epsilon]Q_j$，没有二挠平移项。由于 $F$ 由 $a,b,c$ 生成，正号时 $g_v=1$、$F_v=\mathbb Q_p$、$f_v=1$；负号时 $g_v$ 的阶为 $2$、$F_v/\mathbb Q_p$ 为不分歧二次扩张、$f_v=2$。所以这一步同时确定了实际局部域与两个实际半点的精确特征关系，而非由剩余域中的符号反推它们。倍二给出 (63.3) 的前两个包含。

正号时取 $d=s=1$；此时 $T_v=E_0(\mathbb Q_p)$。负号时取任意剩余类非平方的单位 $d\in\mathbb Z_p^\times$。不分歧二次扩张的唯一性允许在同一个 $F_v$ 中取 $s^2=d$，且 $g_v(s)=-s$。对 $E^{(d)}(\mathbb Q_p)$ 中的点，(63.5) 使横坐标固定、纵坐标取负，故其像在 $T_v$ 中。反向，$S=(x,y)\in T_v$ 满足

$$
x\in\mathbb Q_p,\qquad g_v(y)=-y,\qquad
X=dx\in\mathbb Q_p,\quad Y=ds\,y\in\mathbb Q_p.
\tag{63.7}
$$

这些坐标满足 $E^{(d)}$；$O$ 及 $y=0$ 的二挠点也包括在内。该单位坐标变换是保持单位元的曲线同构，故是群同构。这证明两种符号下的全部 $T_v$ 识别，不要求原 $Q_j$ 或 $P_j$ 为全局 $\mathbb Q$ 有理点。

原模型和这个单位扭曲都在 $p>7$ 好约化。若 $t=-x/y$、$t_d=-X/Y$ 是各自的形式参数，则对非零形式点 $S$ 准确有

$$
t(\phi_dS)=s\,t_d(S),\qquad
\operatorname{ord}_v x(\phi_dS)=v_p(X(S)),\qquad
\operatorname{ord}_v t(\phi_dS)=v_p(t_d(S)).
\tag{63.8}
$$

最后两式使用 $d,s$ 为单位及 $e_v=1$。因此扭曲的第 $j$ 形式层正好映到 $K_v(j)$。当负号出现时，整个 $U_v(j)$ 的形式对数是秩二的 $\mathbb Z_p$ 模，而 $K_v(j)$ 对应秩一的 $p^j\mathbb Z_p$；不能将二者相等或将整个 $U_v(j)$ 包含于 $T_v$。

在扭曲的第一形式层，$1>1/(p-1)$ 是严格形式对数阈值。Silverman，*The Arithmetic of Elliptic Curves*，第二版，[IV.6.3–6.4，印刷页 131–132；VII.2.1–2.2，印刷页 188–191](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)，给出约化正合列及保赋值形式对数。用于当前扭曲时，每个第 $j$ 层对应加法群 $p^j\mathbb Z_p$，特别有

$$
K_v(1)/K_v(j)\simeq\mathbb Z/p^{j-1}\mathbb Z,\qquad
[2]:K_v(j)\longrightarrow K_v(j)\text{ 为自同构}.
\tag{63.9}
$$

这已证明 $K_v(j)\subseteq[2]T_v$，现在才使用 (63.4) 的商。作者[第二版勘误](https://www.math.brown.edu/johsilve/AEC/AECErrata.pdf)对 IV.6.3(a) 的修正区分分式域收敛和整环收敛；这里始终在严格保赋值阈值内，不使用无阈值的整环收敛断言。

将 (63.5) 在同一地方约化，正号给出 $E_0(\mathbb F_p)$，负号给出

$$
\phi_{\bar d}\bigl(\widetilde E^{(d)}(\mathbb F_p)\bigr)
=\ker(\pi_p+1)\subset\widetilde E_0(k_v).
\tag{63.10}
$$

反向包含同样由 (63.7) 的剩余域版本得到；负号时 $k_v=\mathbb F_{p^2}$。两种符号合写为 $G=\ker(\pi_p-[\epsilon])$。扭曲的好约化正合列遂给出满射 $T_v\to G$，其核恰为 $K_v(1)$。原 (58.5) 已在这个同一个特殊纤维内证明

$$
[2]G\simeq\mathbb Z/D_p\mathbb Z,\qquad p\nmid D_p.
\tag{63.11}
$$

此处直接引用该超奇异有限群计算，包括负中央符号；不重做完整素于 $p$ 挠点与 Weil 配对的论证。其成熟输入为 Silverman III.6.4、III.8.1，配对值域为标准 $\mu_m$，挠点指阶整除 $m$ 的点，按作者页 69、93–98 的勘误理解。

倍二像在约化下的像为 $[2]G$；由于已经证明 $K_v(1)\subseteq[2]T_v$，其核就是 $K_v(1)$。对每个 $j\ge1$ 因而有正合列

$$
0\longrightarrow K_v(1)/K_v(j)
\longrightarrow C_v(j)
\longrightarrow[2]G\longrightarrow0.
\tag{63.12}
$$

两端分别为阶 $p^{j-1}$ 和 $D_p$ 的循环群，且两阶互素。在有限交换群的主部分解中，$p$ 主部正是左端，素于 $p$ 的部分同构于右端，故中项循环且阶为 $D_pp^{j-1}$。这证明 (63.4) 的全部深度。

这里的扭曲仅识别同一原地方的特征子群。原 $F_v$、原 $U_v(j)$、原 $b_v$ 和 $f_v$ 均仍保留；尤其负号地方虽然用一个 $\mathbb Q_p$ 点群描述，贡献仍乘原 $f_v/8=2/8$。没有把全局独立的两点变为一个点的 CM 倍数。

用白话说，正号半点住在原局部有理点群里，负号半点住在同一地方的反不变部分里。后者可用一个单位扭曲的有理点群准确描述，深度不会改变。半点的倍二像在第一层之外已经循环，第一层之内又只有一个 $p$ 进方向；两部分的阶互素，所以每一个深度的整个倍二商仍然循环。新增的是这对实际半点与原全深度过滤的接口，属 repo-derived 综合；局部扭曲、有限交换群和形式群均为内部成熟输入。$\square$

## 64. 全部大素数与全部深度的线性平均预算

**定义 64.1（实际共同周期与带权周期质量）。** 固定任意整数 $M\ge1$、$H\ge7$，仍取原 $q=q_H=q(H,H;M)$。对每个 $p>H$、原地方 $v\mid p$ 和 $j\ge1$，先在原有限商中定义

$$
A_v(j)=E_0(F_v)/U_v(j),\qquad
\Gamma_{vj}(q)=\langle[q]P_1+U_v(j),[q]P_2+U_v(j)\rangle,\qquad
r_{vj}=\exp\Gamma_{vj}(q).
\tag{64.1}
$$

平凡群的指数取 $1$。这里的指数是消去全部群元素的最小正整数，不是子群在环境群中的指数。原共同周期接口 (16.5)–(16.6) 给出

$$
r_{vj}=\operatorname{lcm}_{i=1,2}
 \operatorname{ord}_{A_v(j)}([q]P_i+U_v(j))
=\frac{\delta_p(j)}{\gcd(\delta_p(j),q)}.
\tag{64.2}
$$

仍保留 $v$ 指标，并在每个实际地方求权重。$p\in S_0$ 时，(63.3) 使 $\Gamma_{vj}(q)$ 嵌入 $C_v(j)$，所以

$$
|\Gamma_{vj}(q)|=r_{vj},\qquad
r_{vj}\mid D_pp^{j-1}.
\tag{64.3}
$$

实际群可为环境循环群的真子群；不将 $r_{vj}$ 写成 $D_pp^{j-1}$。在 $j=1$，$r_{v1}$ 正是 (60.3) 的 $r_{v,H}$。一般支持上只定义精确指数，不断言群阶等于指数。

对任意素数集合 $\Sigma\subseteq\{p>7\}$、实数 $R\ge0$，定义包含全部深度的质量

$$
W_{\Sigma,H}(R)
=\sum_{\substack{p>H,\ p\in\Sigma\\v\mid p,\ j\ge1:\ r_{vj}\le R}}
 \frac{f_v\log p}{8},\qquad
W_{\Sigma,H}(R)=0\quad(0\le R<1),
\tag{64.4}
$$

并对整数 $r\ge1$ 置

$$
a_{\Sigma,H}(r)=W_{\Sigma,H}(r)-W_{\Sigma,H}(r-1).
\tag{64.5}
$$

$M$ 对这些记号的影响只通过原 $q_H$，未另选共同周期。对整数 $t,N\ge1$，定义对应的原共同质量及其有限平均

$$
\begin{aligned}
F_{\Sigma,H}(t)
&=\frac18\sum_{\substack{p>H\\p\in\Sigma}}\log p
 \sum_{v\mid p}f_v\min\{b_v([qt]P_1),b_v([qt]P_2)\},\qquad t\ge1,\\
\mathcal M_{\Sigma,H}(N)&=\frac1N\sum_{t=1}^N F_{\Sigma,H}(t),\qquad N\ge1.
\end{aligned}
\tag{64.6}
$$

在这个消费者内直接引用 (62.5)–(62.6)：它们来自原 003 定理 50.2、(50.5)–(50.6)，逐地方适用于全部原整 $x$ 分母。故对每个同一 $t$，(64.6) 正是 $G_\Sigma(H;qt,1)$，也是全部非零整数 $k$ 上 $G_\Sigma(H;qt,k)$ 的最小值；全部地方同时由 $k=1$ 取得。这里仅对该最小共同质量求上界，不将它解释为任意移动 $k$ 的上界，也不另立通用最小关系命题。

**定理 64.2（原超奇异标量支持的完整平均上界）。** 每个固定 $R$ 的 (64.4) 都是有限和，对任意上述 $\Sigma$ 有完整平均身份

$$
\mathcal M_{\Sigma,H}(N)
=\frac1N\sum_{r=1}^N a_{\Sigma,H}(r)
 \left\lfloor\frac Nr\right\rfloor.
\tag{64.7}
$$

特别地，所有整数 $M\ge1,H\ge7,N\ge1$ 和实数 $R\ge1$ 同时满足

$$
\begin{aligned}
W_{S_0,H}(R)&\le12h_0q_H^2R^2+8(\log2)R,\\
\mathcal M_{S_0,H}(N)&\le24h_0q_H^2N
 +8(\log2)(1+\log N).
\end{aligned}
\tag{64.8}
$$

这里 $p$ 始终遍历对应支持内的全部 $p>H$，$j$ 始终遍历全部正整数；没有 $p\le N$ 或深度上限。

**证明（有限性与原质量身份）。** 对任何满足 $r_{vj}\le R$ 的三元组 $(p,v,j)$，令 $r=r_{vj}$。精确指数的定义给出

$$
[qr]P_1,[qr]P_2\in U_v(j).
\tag{64.9}
$$

对固定 $R$，只涉及有限个非零全局点 $[qs]P_1$，$1\le s\le\lfloor R\rfloor$。它们由原高度 $h_0q^2s^2>0$ 保证非挠、非零。在 $p>H\ge7$，原深度恰为 $b_v$，所以 (64.9) 使 $v$ 属于其中一个点的分母支持，并使 $j\le b_v([qr]P_1)$。有限点集的分母支持与各赋值都有限，故 (64.4) 有限；对 $R<1$ 和空支持结论也成立。这一步不使用循环性，因而包括完整支持。

对每个固定 $t$，同一个有限商中的群指数给出准确条件

$$
[qt]P_1,[qt]P_2\in U_v(j)
\quad\Longleftrightarrow\quad r_{vj}\mid t.
\tag{64.10}
$$

共同深度是这些条件在 $j\ge1$ 上的指示函数之和。用原 $f_v\log p/8$ 求和，得到

$$
F_{\Sigma,H}(t)
=\sum_{\substack{p>H,\ p\in\Sigma\\v\mid p,\ j\ge1}}
 \frac{f_v\log p}{8}\,\mathbf1_{r_{vj}\mid t}
=\sum_{r\mid t}a_{\Sigma,H}(r).
\tag{64.11}
$$

全部非零项已由有限分母支付；也可先对非负和应用 Tonelli，再用刚证的有限性。对 $1\le t\le N$ 求和即得 (64.7)。这里只能截去 $r>N$：即使 $p>N$，实际子群的 $r_{vj}$ 仍可能不超过 $N$，这样的地方及全部合格深度均留在 (64.7) 中。

**证明（整个有限短关系点集的高度）。** 现在只取 $\Sigma=S_0$。固定 $R\ge1$，置 $L=\lfloor\sqrt R\rfloor$。对每个满足 $r_{vj}\le R$ 的三元组，(64.3) 给出实际群阶 $|\Gamma_{vj}(q)|=r_{vj}\le R$。将 $(L+1)^2>R$ 个向量

$$
(u_1,u_2)\in\{0,\ldots,L\}^2
\quad\longmapsto\quad[u_1q]P_1+[u_2q]P_2+U_v(j)
\tag{64.12}
$$

映入这个实际群，必有不同向量同像。它们的差 $m=(m_1,m_2)$ 满足

$$
m\ne0,\qquad |m_1|,|m_2|\le L,\qquad
S_m=[q](m_1P_1+m_2P_2)\in U_v(j).
\tag{64.13}
$$

这个短关系可随 $p,v,j$ 改变。为支付这种改变，取整个全局点集

$$
\mathcal S_L=\{S_m:m\in\mathbb Z^2\setminus\{0\},\ |m_1|,|m_2|\le L\}.
\tag{64.14}
$$

原 (16.21) 与原 (49.8) 对每个这样的实际 $F$ 点给出

$$
\widehat h(S_m)=h_0q^2(m_1^2+m_2^2)>0,\qquad
\log\|B(S_m)\|\le h_0q^2(m_1^2+m_2^2)+\log2.
\tag{64.15}
$$

特别没有把某一地方最优点的高度当作一个共同点的高度。对每个三元组在固定有限系数集内选取一个满足 (64.13) 的 $m$。固定 $m,v$ 后，分派给它的不同 $j$ 都不超过 $b_v(S_m)$；因此这些层的总权重至多为 $f_vb_v(S_m)\log p/8$。逐个 $m$ 支付其整个原分母，再对全部系数求和，得到

$$
\begin{aligned}
W_{S_0,H}(R)
&\le\sum_{\substack{m\ne0\\|m_1|,|m_2|\le L}}
 \log\|B(S_m)\|\\
&\le\frac23h_0q^2L(L+1)(2L+1)^2
 +4(\log2)L(L+1).
\end{aligned}
\tag{64.16}
$$

这里系数 $m$ 与 $-m$ 的点也都支付，不依赖去重节省。求和恒等式来自 $\sum_{u=-L}^Lu^2=L(L+1)(2L+1)/3$；非零系数的个数为 $(2L+1)^2-1=4L(L+1)$。由于 $L\ge1$，$L+1\le2L$、$2L+1\le3L$，且 $L^2\le R$，(64.16) 给出

$$
\frac23L(L+1)(2L+1)^2\le12L^4\le12R^2,
\qquad4L(L+1)\le8L^2\le8R.
\tag{64.17}
$$

这正是 (64.8) 的第一式。证明逐层支付全部满足 $r_{vj}\le R$ 的原地方，不以 $p$ 的大小换取有限性。

**证明（有限分部求和）。** 为简化此段记号，令 $W=W_{S_0,H}$、$a=a_{S_0,H}$、$A=12h_0q^2$、$B=8\log2$，并写 $\mathfrak h_N=\sum_{r=1}^N1/r$。由 (64.7) 及非负性，

$$
\begin{aligned}
\mathcal M_{S_0,H}(N)
&\le\sum_{r=1}^N\frac{a(r)}r\\
&=\frac{W(N)}N+
 \sum_{r=1}^{N-1}\frac{W(r)}{r(r+1)}\\
&\le AN+B+A\sum_{r=1}^{N-1}\frac r{r+1}
 +B\sum_{r=1}^{N-1}\frac1{r+1}\\
&=A(2N-\mathfrak h_N)+B\mathfrak h_N\\
&\le2AN+B(1+\log N).
\end{aligned}
\tag{64.18}
$$

代回 $A,B$ 即得第二式，$N=1$ 的空和也包括在内。常数来自原准确高度与有限系数总和，对全部 $H,N,M$ 统一，无需假设 $H$ 充分大。

短关系与高度法的成熟先例为 Akbary–Murty，*Reduction mod p of Subgroups of the Mordell–Weil Group of an Elliptic Curve*，*International Journal of Number Theory* **5** (2009), 465–487，[Proposition 1.2、作者 PDF §8，页 24–25](https://www.cs.uleth.ca/~akbary/npr.pdf)。该文先用有限约化群中的碰撞找到短关系，再对全部可能关系的分母和高度计数；其陈述在 $E(\mathbb Q)$ 和第一约化层，不能直接用于原 $F$、所有深度或这里的带权质量。这里采用的中间方法属于 literature-attested；(63.4)、原独立性和 (64.13)–(64.16) 另行给出同一原地方、全部深度和 $f_v/8$ 的对应。高度常数使用原 (16.21)、(49.8) 的归一化，不移用该文页 25 的高度归一化或隐含常数。

用白话说，共同周期小不代表环境群小，但在这个循环环境里，它确实代表两点实际生成的群小。两个系数各只需试到周期的平方根，就能找到一个原全局组合进入指定深度。不同地方可以挑到不同组合，所以必须将整个有限组合集的高度付清。付清后周期质量至多二次；平均中一个周期只出现约 $N/r$ 次，于是得到线性 $N$ 预算。这个原全深度共同质量消费者是 repo-derived 综合，经典碰撞、群论和分部求和不另作一般新理论。$\square$

## 65. 完整支持的次二次平均与剩余周期质量

**定理 65.1（原完整共同分母的精确缺口）。** 在定义 64.1 中取

$$
\Sigma_{\rm all}=\{p:p>7\},\qquad
\Sigma_{\rm rem}=\Sigma_{\rm all}\setminus S_0.
\tag{65.1}
$$

下标 $\mathrm{all}$、$\mathrm{rem}$ 分别表示把这两集合代入 $W_{\Sigma,H}$、$a_{\Sigma,H}$、$F_{\Sigma,H}$、$\mathcal M_{\Sigma,H}$。对每个固定的 $M\ge1,H\ge7$，令 $q=q_H$ 在以下极限中保持不变，则

$$
\begin{aligned}
\mathcal M_{\mathrm{all},H}(N)=o(q^2N^2)\quad(N\to\infty)
&\quad\Longleftrightarrow\quad
W_{\mathrm{all},H}(R)=o(q^2R^3)\quad(R\to\infty)\\
&\quad\Longleftrightarrow\quad
W_{\mathrm{rem},H}(R)=o(q^2R^3)\quad(R\to\infty).
\end{aligned}
\tag{65.2}
$$

完整支持在每个有限阶段已有粗预算，置 $m=\lfloor R\rfloor$，则

$$
W_{\mathrm{all},H}(R)
\le h_0q^2\frac{m(m+1)(2m+1)}6+m\log2.
\tag{65.3}
$$

这里的完整量是原全部 $p>H$ 的尾部最小共同质量；所有 $v\mid p$ 和所有深度都在内。特别没有将其改为仅 $S_0$ 的质量。

**证明。** 定理 64.2 的有限性和身份 (64.7) 没有使用循环性，故对 $\Sigma_{\mathrm{all}}$ 和 $\Sigma_{\mathrm{rem}}$ 都成立。在 (64.9) 中按精确值 $r_{vj}=s$ 分组；每组均由同一个非零全局点 $[qs]P_1$ 的分母支付全部地方及层。原高度上界给出

$$
W_{\mathrm{all},H}(R)
\le\sum_{s=1}^m\log\|B([qs]P_1)\|
\le\sum_{s=1}^m(h_0q^2s^2+\log2),
\tag{65.4}
$$

即 (65.3)。这只是三次量级上界，不能将其首项换成 $o(q^2R^3)$。

现把 (64.7) 用于完整支持，暂记 $W=W_{\mathrm{all},H}$、$a=a_{\mathrm{all},H}$、$\mathcal M=\mathcal M_{\mathrm{all},H}$。因 $\lfloor N/r\rfloor\ge1$ 对 $1\le r\le N$ 成立，有

$$
W(N)\le N\mathcal M(N).
\tag{65.5}
$$

若 $\mathcal M(N)=o(q^2N^2)$，即得 $W(N)=o(q^2N^3)$。对实数 $R$，$W(R)=W(\lfloor R\rfloor)$ 且 $\lfloor R\rfloor/R\to1$，故实数版本也成立。

反向，假设 $W(R)=o(q^2R^3)$。给定任意 $\eta>0$，存在整数 $R_0=R_0(\eta,H,M)$，使所有整数 $r\ge R_0$ 都满足 $W(r)\le\eta q^2r^3$。对 $N\ge R_0$，仍用有限分部求和，得到

$$
\begin{aligned}
\mathcal M(N)
&\le\frac{W(N)}N+\sum_{r=1}^{N-1}\frac{W(r)}{r(r+1)}\\
&\le C_0+\eta q^2\left(N^2+
 \sum_{r=R_0}^{N-1}\frac{r^2}{r+1}\right)\\
&\le C_0+\frac32\eta q^2N^2,
\end{aligned}
\tag{65.6}
$$

其中 $C_0=\sum_{1\le r<R_0}W(r)/(r(r+1))$ 是固定的有限数，末步用 $r^2/(r+1)\le r$。除以 $q^2N^2$ 后取上极限，再令 $\eta\downarrow0$，即得完整平均的次二次结论。这证明第一个等价；它用的是非负质量的标准分部求和，未提供周期质量的小量估计。

两素数支持不相交，所以准确有

$$
\begin{aligned}
W_{\mathrm{all},H}(R)
 &=W_{S_0,H}(R)+W_{\mathrm{rem},H}(R),\\
\mathcal M_{\mathrm{all},H}(N)
 &=\mathcal M_{S_0,H}(N)+\mathcal M_{\mathrm{rem},H}(N).
\end{aligned}
\tag{65.7}
$$

(64.8) 给出固定阶段的 $W_{S_0,H}(R)=o(q^2R^3)$ 与 $\mathcal M_{S_0,H}(N)=o(q^2N^2)$。结合非负性，得到第二个等价；同理 (65.2) 也等价于 $\mathcal M_{\mathrm{rem},H}(N)=o(q^2N^2)$。等价中的所有极限均固定 $H,M$；这里没有对完整支持取得随 $N$ 移动的 $H$ 或 $M$ 上的统一小量。$\square$

在完整支持中，精确指数 $r_{vj}$ 仅保证两个生成元都被同一个整数消去；一个两生成元有限交换群的阶可达 $r_{vj}^2$。因此“小指数”不能直接给出 (64.12) 所需的“小群阶”。定理 63.2 在 $S_0$ 上消除了这个区别，其他非标量地方及普通标量地方没有从该定理取得同样的全深度循环结论。即使某个环境群不循环，实际两点仍可能生成循环子群；这里既没有排除这种情况，也没有证明它在剩余支持上足够普遍。

故完整支持尚缺的是 (65.2) 中剩余周期质量的严格次三次增长，或能够推出它的联合算术约束；(65.3) 恰停在三次量级。低周期处的质量包括 $p>R$ 乃至 $p>N$ 的原地方，不能靠删去它们缩小缺口。单独的剩余域群阶、分别最优的局部短关系、支持的素数密度或各点分母的大质量，都不补足这个条件。

来源与新增范围。定理 63.2 消费原 (53.8)–(53.9)、(58.5)；定理 64.2 消费原 (62.5)–(62.6)、002 (16.21) 及 003 (49.8)。实际半点与独立性沿用原 Brox 固定源码，未重作或变更。Silverman 的约化正合列、严格形式对数、完整素于 $p$ 挠点和标准 Weil 配对，以及 Akbary–Murty 的短关系/高度方法，均为 literature-attested 内部输入。定理 65.1 的一般非负分部求和是成熟步骤，新增范围为它与原全部深度、精确地方权重及实际共同周期的完整接口和剩余支持分解，属 repo-derived 综合，不主张全球文献优先性。

用白话说，受限支持上的循环性确实把平均预算降了一阶，而且所有大素数、所有深度都已计入。但是完整 gcd 还含有其余地方；现在可以准确说出剩下要证明什么：周期不超过 $R$ 的那些地方和深度，总质量相对于 $q_H^2R^3$ 的比值必须趋于零。这里证明的是这个条件与完整次二次平均的等价，没有证明条件本身。线性上界也只约束同一个 $k=1$ 的最小共同质量，不给出任意移动 $k$ 的上界、每个 $t$ 的线性界或任何未另证的密度一结论。原短共振的同时实现、原 $p_H(\alpha)$、原 (31.2)、负 $\vartheta$ 阶段的调和和发散及原覆盖目标均仍保留各自的未解义务。

---

## 追加锚（本行以下为增补区）

## 66. 全部普通非标量支持的双特征理想与线性平均预算

**定义 66.1（原首入口与固定六方向）。** 保持定义 51.1、53.1、64.1 的全部数据，特别是原八次全实域 $F$、原整方程 $E_0:y^2=x^3-x$、原独立点 $P_1,P_2$、全部原地方、原过滤 $U_v(j)$、原整 $x$ 分母及权重 $f_v/8$。对任意整数 $M\ge1,H\ge7$，始终取同一个 $q=q_H=q(H,H;M)$。置

$$
\mathcal T_{\mathrm{ord,ns}}
=\{p>7:p\equiv1\pmod4,\ (\chi_2(p),\chi_7(p))\ne(1,1)\},
\qquad
\rho_p=\frac{n_p}{\gcd(n_p,q)},\qquad d_p=t_p+v_p(q),
\tag{66.1}
$$

其中 $n_p,t_p$ 严格取原 002 (16.2) 的实际共同约化入口及共同入口深度。以下简记 $\mathcal T=\mathcal T_{\mathrm{ord,ns}}$，并把 $\mathcal T$ 代入 (64.4)–(64.6)，得到 $W_{\mathcal T,H}$、$F_{\mathcal T,H}$、$\mathcal M_{\mathcal T,H}$。$\rho_p$ 是原点对乘以 $q$ 后的实际第一层共同周期，既不是 §58 的环境指数 $e_p$，也不预设为环境群的阶。

只对中间全局点取 $K=F(i)$、$\mathcal O=\mathbb Z[i]$，并保持原 $[i](x,y)=(-x,iy)$ 及 (51.2) 的 $K$ 分母。固定与所有参数和地方无关的六个方向

$$
\mathcal D=\{P_1,P_2,P_1+P_2,P_1-P_2,
                     P_1+[i]P_2,P_1-[i]P_2\}.
\tag{66.2}
$$

对 $w\mid v\mid p>7$，$U_w(j)$ 仅表示原好整方程在 $K_w$ 中约化为 $O$ 且参数 $t=-x/y$ 的赋值至少为 $j$ 的子群。它满足 $U_w(j)\cap E_0(F_v)=U_v(j)$；不是重选原地方或原过滤。所有 $K$ 点及其分母均按实际嵌入 $K\hookrightarrow K_w$ 理解。

**定理 66.2（原全部普通非标量地方的完整周期质量消费者）。** 对定义 66.1 的全部参数，每个 $p\in\mathcal T$、每个原地方 $v\mid p$ 及每个 $j\ge1$，原 (64.1) 的精确指数为

$$
r_{vj}=\rho_p p^{\max(0,j-d_p)}.
\tag{66.3}
$$

故对全部实数 $R\ge1$，有包含全部深度的精确表达

$$
\begin{aligned}
W_{\mathcal T,H}(R)
 &=\sum_{\substack{p>H,\ p\in\mathcal T\\\rho_p\le R}}
 \left(d_p+\left\lfloor\frac{\log(R/\rho_p)}{\log p}\right\rfloor\right)\log p\\
 &=E_{\mathcal T,H}(R)+D_{\mathcal T,H}(R),\\
E_{\mathcal T,H}(R)
 &:=\sum_{\substack{p>H,\ p\in\mathcal T\\\rho_p\le R}}d_p\log p,\qquad
0\le D_{\mathcal T,H}(R)\le\psi(R),\qquad
\psi(R):=\sum_{p^a\le R}\log p.
\end{aligned}
\tag{66.4}
$$

在 $\psi$ 中，$p$ 遍历有理素数，$a$ 遍历正整数。对所有整数 $M\ge1,H\ge7,N\ge1$ 及实数 $R\ge1$，统一有

$$
\begin{aligned}
E_{\mathcal T,H}(R)
 &\le320h_0q_H^2R^2+96(\log2)R,\\
W_{\mathcal T,H}(R)
 &\le320h_0q_H^2R^2+100(\log2)R,\\
\mathcal M_{\mathcal T,H}(N)
 &\le640h_0q_H^2N+100(\log2)(1+\log N).
\end{aligned}
\tag{66.5}
$$

全部 $p>H$、全部 $v\mid p$ 及全部深度均保留；特别没有 $p\le R$ 或 $p\le N$ 的截断。这里的平均只针对 (64.6) 的 $k=1$ 全地方最小共同质量。

更精确地，在每个 $p\in\mathcal T$ 的实际 $w\mid v$，存在 $S_+,S_-\in\mathcal D$、不同的 $u_+,u_-\in\{1,-1,i,-i\}$ 及当前 (51.8) 的 $\lambda_w\in\mathcal O$，满足 $N(u_+-u_-)=4$。在原深度 $d_p$ 定义

$$
I_{\pm,w}
=\{\alpha\in\mathcal O:[\alpha q]S_\pm\in U_w(d_p)\}.
\tag{66.6}
$$

这两个集合均为非零理想，且

$$
(\rho_p)\subseteq I_{\pm,w},\qquad
\lambda_w-u_\pm\in I_{\pm,w},\qquad
\min\{\mathrm N I_{+,w},\mathrm N I_{-,w}\}\le2\rho_p.
\tag{66.7}
$$

这里 $\mathrm N I=[\mathcal O:I]$。因此当 $\rho_p\le R$ 时，至少有一个方向 $S\in\{S_+,S_-\}$ 及一个非零生成元 $\alpha$，使

$$
I_{\pm,w}=(\alpha),\qquad
N(\alpha)\le2\rho_p\le2R,\qquad
[\alpha q]S\in U_w(d_p).
\tag{66.8}
$$

该点是一个真实的全局 $K$ 点；它可以依赖地方，不要求不同地方选出同一点。

**证明（原周期及所有入口外的层）。** 原 002 定理 16.4 的下降支持给出 $p\nmid n_p$ 对全部 $p>7$ 成立。原命题 16.2、定理 16.3 和 (64.2) 随即给出

$$
\frac{n_pp^{\max(0,j-t_p)}}
 {\gcd(n_pp^{\max(0,j-t_p)},q)}
=\frac{n_p}{\gcd(n_p,q)}
 p^{\max(0,j-t_p-v_p(q))},
\tag{66.9}
$$

即 (66.3)。同样，$n_p\mid\rho_pq$ 且 $v_p(\rho_p)=0$，所以原 (16.7)–(16.8) 给出

$$
[\rho_pq]P_1,[\rho_pq]P_2\in U_v(d_p),\qquad
\min_{j=1,2}b_v([\rho_pq]P_j)=d_p.
\tag{66.10}
$$

它是原点对在原地方的深度，不是某个环境消去数的深度。

当 $\rho_p\le R$ 时，(66.3) 中恰有 $d_p$ 个入口层，以及
$\lfloor\log(R/\rho_p)/\log p\rfloor$ 个入口外的层；当 $\rho_p>R$ 时没有层。因 $e_v=1$ 且 $\sum_{v\mid p}f_v=8$，(64.4) 的逐地方权重之和正好为 $\log p$。这证明 (66.4) 的身份；有限性已经由定理 64.2 对任意支持的证明保证。每个入口外的层都有 $\rho_pp^a\le R$，因而 $p^a\le R$，于是

$$
D_{\mathcal T,H}(R)
=\sum_{\substack{p>H,\ p\in\mathcal T\\a\ge1:\rho_pp^a\le R}}\log p
\le\sum_{p^a\le R}\log p=\psi(R).
\tag{66.11}
$$

这里仅入口外的层受到 $p\le R$ 的限制；所有 $p>R$ 的入口质量仍在 $E_{\mathcal T,H}$ 中。

**证明（同一实际地方的两个特征方向）。** 固定 $p\in\mathcal T$ 及 $w\mid v\mid p$。由 $p\equiv1\pmod4$，$i\in\mathbb Q_p$，$K/F$ 在 $v$ 分裂；$K_w=F_v$，但两种 $i$ 的嵌入仍分别由两个 $w\mid v$ 指定。取 $K_w/\mathbb Q_p$ 的算术 Frobenius $g_w$，其限制是原 $g_v$ 且固定当前 $i$。原 (53.8)–(53.9) 给出以下精确作用。表中 $s\in\{1,-1\}$ 由当前地方的实际作用决定。

| 原系数作用 | $S_+$ | $S_-$ | $u_+$ | $u_-$ |
| --- | --- | --- | --- | --- |
| $sD$ | $P_1$ | $P_2$ | $s$ | $-s$ |
| $sC$ | $P_1+P_2$ | $P_1-P_2$ | $s$ | $-s$ |
| $sJ$ | $P_1+[i]P_2$ | $P_1-[i]P_2$ | $-si$ | $si$ |

在三支中均有 $g_wS_\pm=[u_\pm]S_\pm$。例如 $sJ$ 表示 $g_wP_1=[s]P_2$、$g_wP_2=[-s]P_1$；又 $g_w(i)=i$，故第一复方向的特征值确为 $-si$。这核定了字符的方向，且每支均有 $N(u_+-u_-)=4$。三支恰为原普通非标量支持的全部类型。

普通约化及当前 CM 嵌入直接复用命题 51.2 的 (51.7)–(51.8)。因此当前特殊纤维的 $p$ 次幂 Frobenius $\pi_p$ 对应唯一 $\lambda_w\in\mathcal O$，满足

$$
\widetilde{[\lambda_w]}=\pi_p,
\qquad N(\lambda_w)=p,\qquad
\lambda_w+\overline{\lambda_w}=a_p.
\tag{66.12}
$$

这里只在特殊纤维上识别 Frobenius。约化与实际算术 Frobenius 相容，所以

$$
\widetilde{[\lambda_w]}\,\overline S_\pm
=\pi_p\overline S_\pm
=\overline{g_wS_\pm}
=[\widetilde u_\pm]\overline S_\pm.
\tag{66.13}
$$

(66.13) 不声称 $[\lambda_w]S_\pm=g_wS_\pm$ 在特征零成立；$g_w$ 是域自同构给出的作用，不是这里引入的局部曲线自同源。特别地，从 (66.13) 只先得到

$$
T_\pm:=[(\lambda_w-u_\pm)q]S_\pm\in U_w(1).
\tag{66.14}
$$

所用成熟输入的原始范围是 Silverman，*The Arithmetic of Elliptic Curves* 第二版，[III.6.2、V.2.3.1、V.3.1(b)、V.4.1(a)](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)：对偶和次数、特殊纤维 Frobenius 的特征方程、普通自同源环的虚二次性及 Hasse 系数判据。本例对应已在 §51 给出，故这里不另证或另立一般 CM 定理。

**证明（先有第一层，再提升到原入口深度）。** 原整形式群的加法、整数乘法及 $t([i]T)=it(T)$ 表明所有 $[\beta]$、$\beta\in\mathcal O$ 都保每个 $U_w(j)$。由 (66.10) 与子群性，六个方向均满足

$$
[\rho_pq]S\in U_w(d_p)\qquad(S\in\mathcal D).
\tag{66.15}
$$

故 $\rho_p\in I_{\pm,w}$。这些集合是加法子群，且 $\alpha\in I_{\pm,w}$ 蕴涵 $\beta\alpha\in I_{\pm,w}$；所以是非零理想，并包含整个 $(\rho_p)$。

对 (66.14) 已经进入第一层的点，再用

$$
[\rho_p]T_\pm
=[\lambda_w-u_\pm][\rho_pq]S_\pm\in U_w(d_p).
\tag{66.16}
$$

这里 $K_w/\mathbb Q_p$ 不分歧，且 $p>7$，故 $1>e_w/(p-1)$。原 §51 的保赋值形式对数在整个 $U_w(1)$ 有效。又 $p\nmid\rho_p$，所以对其中非零点 $T$，

$$
b_w^K([\rho_p]T)=b_w^K(T)+v_p(\rho_p)=b_w^K(T).
\tag{66.17}
$$

由 (66.14)、(66.16) 才能推出 $T_\pm\in U_w(d_p)$，即 $\lambda_w-u_\pm\in I_{\pm,w}$。本处 $\lambda_w-u_\pm\ne0$，因为其为零会使 $N(\lambda_w)=1$；各 $S_\pm$ 的正高度和原模挠独立性也保证这些全局点非挠、非零。即使在子群计算中出现 $O$，成员结论也自动成立。

这一步没有在整个约化群上除以 $\rho_p$。它先证第一层入口，再在保赋值形式群内使用 $p\nmid\rho_p$。所用严格阈值见 Silverman [IV.6.3–6.4，印刷页 131–132；VII.2.1–2.2，印刷页 188–191](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)。作者[勘误](https://www.math.brown.edu/johsilve/AEC/AECErrata.pdf)页 122–124 的形式逆元与参数说明、页 131 对 IV.6.3(a) 的分式域收敛更正及页 188–191 的约化记号，均与这里的使用一致；尤其没有从仅正赋值推断无阈值的整环收敛。

**证明（两个深度理想迫出一个小范数生成元）。** 为简化记号，暂写 $I_\pm=I_{\pm,w}$、$\rho=\rho_p$。由刚证的两个包含关系，

$$
(u_+-u_-)\subseteq I_++I_-,\qquad
(\rho)\subseteq I_+\cap I_-.
\tag{66.18}
$$

第一个包含来自 $\lambda_w-u_+$ 与 $\lambda_w-u_-$ 作差，第二个来自两理想均含 $(\rho)$。Gaussian 环按范数 Euclidean，因而这些非零理想均为主理想；其主理想范数满足 $\mathrm N((\alpha))=N(\alpha)$。成熟输入见 Conrad，[*The Gaussian Integers*，§1、§3 定理 3.1、§5 定理 5.1、§7 定理 7.14](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/Zinotes.pdf)，分别给出范数、带余除法、Bézout 和商环的大小。由带余除法取理想中的最小正范数元素即可得到主理想性；这里不把这一步另立为一般新结果。

有限加法群的标准正合列

$$
0\longrightarrow\mathcal O/(I_+\cap I_-)
\longrightarrow\mathcal O/I_+\oplus\mathcal O/I_-
\longrightarrow\mathcal O/(I_++I_-)\longrightarrow0
\tag{66.19}
$$

中，前一映射是对角映射，后一映射是两分量作差。后一映射的核确为前一像：若 $a-b=x+y$、$x\in I_+$、$y\in I_-$，则 $a-x=b+y$ 同时代表两个给定分量。因此取群阶并用 (66.18)，得到

$$
\begin{aligned}
\mathrm N I_+\,\mathrm N I_-
 &=\mathrm N(I_++I_-)\,\mathrm N(I_+\cap I_-)\\
 &\le N(u_+-u_-)N(\rho)=4\rho^2.
\end{aligned}
\tag{66.20}
$$

两个正整数中至少一个不超过 $2\rho$；取该理想的任一生成元即得 (66.7)–(66.8)。这里使用的是两个方向在同一个实际地方的联合关系，未把两个地方的分别最优值当成共同实现。

**证明（支付全部地方选择的整个全局有限点集）。** 固定 $R\ge1$，定义有限系数集和带索引的全局点族

$$
\begin{aligned}
\mathcal A_R&=\{\alpha=a+bi\in\mathcal O:0<N(\alpha)\le2R\},\\
\mathcal P_R(q)&=\bigl([\alpha q]S\bigr)_{(\alpha,S)\in\mathcal A_R\times\mathcal D}.
\end{aligned}
\tag{66.21}
$$

即使不同索引给出相同点，仍按各索引支付。原 002 (16.21) 的四方向高度直接给出

$$
\begin{aligned}
\widehat h([\alpha q]P_j)&=h_0q^2N(\alpha),\qquad j=1,2,\\
\widehat h([\alpha q]S)&=2h_0q^2N(\alpha),
\qquad S\in\mathcal D\setminus\{P_1,P_2\}.
\end{aligned}
\tag{66.22}
$$

故族中全部点非挠、非零，且固定 $\alpha$ 的六份高度之和准确为 $10h_0q^2N(\alpha)$。这里没有把独立的原两点改成同一个点的 CM 倍数。

当 $p>H$、$p\in\mathcal T$ 且 $\rho_p\le R$ 时，对每个 $w\mid p$ 用 (66.8) 选一个索引 $(\alpha,S)$。它使全部 $1\le j\le d_p$ 的入口层由同一个 $[\alpha q]S$ 支付，即

$$
d_p\le b_w^K([\alpha q]S)
\le\sum_{(\beta,T)\in\mathcal A_R\times\mathcal D}
                b_w^K([\beta q]T).
\tag{66.23}
$$

不同 $w$ 允许选择不同索引，但右侧始终是同一个完整有限族。原 (51.18)–(51.20) 的扩域高度与地方身份给出

$$
\sum_{w\mid v}\frac{f_w}{16}=\frac{f_v}{8},\qquad
\log\|B_K(T)\|_K\le\widehat h(T)+\log2
\quad(T\in E_0(K)\text{ 非挠}).
\tag{66.24}
$$

第一式使用 $K/F$ 在这里不分歧（实际上分裂）以及局部次数之和为 $2$。第二式是全部 $16$ 个嵌入的绝对高度分解；不能将只对原 $F$ 点写出的 003 (49.8) 直接套给复方向。用 (66.23) 在所有实际 $w$ 求和，再对每个索引支付其完整 $K$ 分母，得到

$$
\begin{aligned}
E_{\mathcal T,H}(R)
 &=\sum_{\substack{p>H,\ p\in\mathcal T\\\rho_p\le R}}
   \sum_{v\mid p}\sum_{w\mid v}\frac{f_w}{16}d_p\log p\\
 &\le\sum_{(\alpha,S)\in\mathcal A_R\times\mathcal D}
                         \log\|B_K([\alpha q]S)\|_K\\
 &\le10h_0q^2\sum_{\alpha\in\mathcal A_R}N(\alpha)
                      +6(\log2)\#\mathcal A_R.
\end{aligned}
\tag{66.25}
$$

各点的全部地方贡献只在它自己的完整分母内相加，全部地方选择的成本再对整个点族相加。因此 (66.25) 已支付 $K$ 的全部扩域权重，包括同一 $v$ 上的两个 $i$ 嵌入；没有把 $f_v/8$ 改为 $f_v/16$。

因为 $|a|,|b|\le\sqrt{2R}$，且对 $R\ge1$ 有 $2\sqrt{2R}+1\le4\sqrt R$，故直接有

$$
\#\mathcal A_R\le16R,\qquad
\sum_{\alpha\in\mathcal A_R}N(\alpha)
\le2R\#\mathcal A_R\le32R^2.
\tag{66.26}
$$

代回 (66.25) 就是 (66.5) 的第一式。这里是有限格点集的纸面上界，不需要挑出生成元的数值，也没有删去任何 $p>R$ 的原地方。

在本消费者内可用经典 Chebyshev 界 $\psi(R)\le4(\log2)R$。为给出所用常数，整数 $n\ge1$ 时，每个 $n<p^a\le2n$ 都在 $\binom{2n}{n}$ 的 $p$ 赋值中贡献至少一次，因
$v_p\binom{2n}{n}=\sum_{a\ge1}(\lfloor2n/p^a\rfloor-2\lfloor n/p^a\rfloor)$ 的各项非负。因此
$\psi(2n)-\psi(n)\le\log\binom{2n}{n}\le2n\log2$。在二幂处累加，并取不小于 $R$ 的最小二幂，即得上述界；$R=1$ 时 $\psi(1)=0$。结合 (66.11) 和第一式，得到 (66.5) 的第二式。成熟的 Gaussian 环、Chebyshev 估计和高度法仅是这里的内部步骤。

最后直接使用原 (64.7) 的完整 floor 身份及 (64.18) 的有限分部求和：若 $W(R)\le AR^2+BR$，同一消费者的平均满足
$\mathcal M(N)\le2AN+B(1+\log N)$。取 $A=320h_0q_H^2$、$B=100\log2$，得到 (66.5) 的第三式。这一步仍只截去 $r>N$，不截去 $p>N$。

**证明（从完整支持的缺口中剥离本支持）。** 与 §65 的 $\Sigma_{\mathrm{all}}=\{p>7\}$ 对应，置

$$
\begin{aligned}
\Sigma_*&=\Sigma_{\mathrm{all}}\setminus(S_0\sqcup\mathcal T),\\
\Sigma_*&=
 \{p>7:p\equiv3\pmod4,\ (\chi_2(p),\chi_7(p))\ne(1,1)\}\\
&\hspace{1.5em}\sqcup
 \{p>7:p\equiv1\pmod4,\ (\chi_2(p),\chi_7(p))=(1,1)\}.
\end{aligned}
\tag{66.27}
$$

这里 $S_0$ 恰为 $p>7$ 中超奇异的标量类型：$p\equiv3\pmod4$ 时，$\chi_2(p)=1$ 等价于 $p\equiv7\pmod8$，二次互反律又使 $\chi_7(p)=1$ 等价于 $p\bmod7\in\{3,5,6\}$；两条件合起来正是原 $p\bmod56\in\{31,47,55\}$。因此 (66.27) 的第一支为超奇异的两类反射和旋转，第二支为普通标量。

这些支持互不相交，故原质量与平均准确相加。由 (64.8) 和本定理，

$$
\begin{aligned}
W_{S_0\sqcup\mathcal T,H}(R)
 &\le332h_0q_H^2R^2+108(\log2)R,\\
\mathcal M_{S_0\sqcup\mathcal T,H}(N)
 &\le664h_0q_H^2N+108(\log2)(1+\log N).
\end{aligned}
\tag{66.28}
$$

所以对每个固定的 $H,M$，这些已支付支持的质量是 $o(q_H^2R^3)$，其平均是 $o(q_H^2N^2)$。将其从 (65.2)、(65.7) 的非负精确分解中减去，得到

$$
\begin{aligned}
\mathcal M_{\mathrm{all},H}(N)=o(q_H^2N^2)
&\quad\Longleftrightarrow\quad
W_{\Sigma_*,H}(R)=o(q_H^2R^3)\\
&\quad\Longleftrightarrow\quad
\mathcal M_{\Sigma_*,H}(N)=o(q_H^2N^2).
\end{aligned}
\tag{66.29}
$$

各极限仍固定同一个 $H,M$。这剥离了全部普通非标量支持，却没有证明 (66.29) 的剩余条件。超奇异反射、旋转没有从这里取得 (66.12) 的普通 Gaussian Frobenius；普通标量则没有两个不同字符来给出 (66.18) 的小范数理想和。这里不排除其它方法能控制它们，也不从这两项障碍推出原目标为假。

来源与新增范围。原精确周期、入口及四方向高度直接复用 002 定义 13.1、命题 16.2、定理 16.3–16.4 与 (16.21)；原 $x$ 分母及 $k=1$ 最小共同质量复用 003 §§49–50 和本卷 (62.5)–(62.6)；当前 CM 嵌入、实际 Frobenius、扩域高度和精确半点作用分别复用本卷 §51、§53。新增承重推导是：在原实际深度 $d_p$ 联合两个不同特征方向的理想，得到 (66.20) 的小范数生成元，再以 (66.25) 支付整个全局点族，并接入原全部深度周期质量及平均。它是原消费者的 repo-derived 综合，不将 Euclidean 环、理想范数正合列、形式群或分部求和另列为新成果，也不主张全球文献优先性。

短关系与分母高度法的成熟先例为 Akbary–Murty，[*Reduction mod p of Subgroups of the Mordell–Weil Group of an Elliptic Curve*，Proposition 1.2、§8，作者 PDF 页 2、24–25](https://www.cs.uleth.ca/~akbary/npr.pdf)。该文先在有限约化群中取短关系，再支付全部可能关系的分母。其输入是 $E(\mathbb Q)$ 的自由子群，其计数是第一约化层的有理素数；它没有直接给出原 $F$ 的带权地方质量、$d_p$ 的过深入口或全部深度。(66.14)–(66.26) 承担这里所需的桥梁，且保持原高度归一化。

用白话说，普通非标量作用能把原两点分出两个不同的特征方向。两把深度钥匙都整除同一个原入口整数，而两把钥匙的共同因子又受一个范数为 $4$ 的字符差约束，所以至少一把钥匙的范数只需付到入口周期的一次方。每个地方可以选不同钥匙；将所有可能选到的真实 CM 点及其完整高度一起支付，入口质量便是二次预算。更深的层只剩一个 Chebyshev 线性预算，原 floor 平均再把二次周期质量变成线性平均。原点、原周期、原地方与分母权重均保留。

(66.5) 不给出任意移动 $k$ 的上界、逐个 $t$ 的线性界或完整 gcd 的次二次平均；后者仍缺 (66.29) 的剩余质量估计。原短共振的同时实现、原 $p_H(\alpha)$、原 (31.2)、负 $\vartheta$ 阶段的调和和发散及原覆盖目标均没有由本定理闭合。$\square$

---

## 追加锚（本行以下为增补区）

## 67. 全部超奇异反射支持的同字符半点与线性平均预算

**定义 67.1（原反射支持与两对固定辅助点）。** 保持定义 51.1、53.1、64.1 的全部原数据：八次全实域 $F=\mathbb Q(a,b,c)$，$a^2=2$、$b^2=3-a$、$c^2=3+a$、$bc=\sqrt7$，原整方程 $E_0:y^2=x^3-x$、指定正根与实嵌入、原独立点 $P_1,P_2$、全部原地方和过滤 $U_v(j)$、原整 $x$ 分母及权重 $f_v/8$。实际半点始终是

$$
Q_1=\left(\frac{1+a}{b^2},\frac{2a}{b^3}\right),\qquad
Q_2=\left(\frac{1-a}{c^2},\frac{-2a}{c^3}\right),\qquad
[2]Q_\ell=P_\ell\quad(\ell=1,2).
\tag{67.1}
$$

对所有整数 $M\ge1,H\ge7$，只取原 $q=q_H=q(H,H;M)$。定义互不相交的两个反射支持及其并

$$
\begin{aligned}
\mathcal T_{\mathrm{ss},D}
 &=\{p>7:p\equiv3\pmod4,\ (\chi_2(p),\chi_7(p))=(1,-1)\},\\
\mathcal T_{\mathrm{ss},S}
 &=\{p>7:p\equiv3\pmod4,\ (\chi_2(p),\chi_7(p))=(-1,1)\},\\
\mathcal T_{\mathrm{ss,refl}}
 &=\mathcal T_{\mathrm{ss},D}\sqcup\mathcal T_{\mathrm{ss},S}.
\end{aligned}
\tag{67.2}
$$

这里只在辅助点上使用真实扩域 $K=F(i)$、$[K:\mathbb Q]=16$ 和原作用 $[i](x,y)=(-x,iy)$。对 $\nu\in\{D,S\}$ 固定全局点对及其实际半点对

$$
\begin{array}{c|c|c}
\nu &(A_\nu,B_\nu)&(H_{\nu,1},H_{\nu,2})\\ \hline
D &(P_1,[i]P_2)&(Q_1,[i]Q_2)\\
S &(P_1+P_2,[i](P_1-P_2))
  &(Q_1+Q_2,[i](Q_1-Q_2))
\end{array}
\qquad
[2]H_{\nu,1}=A_\nu,\quad [2]H_{\nu,2}=B_\nu.
\tag{67.3}
$$

对 $w\mid v\mid p>7$，$U_w(j)$ 仍只表示原好整方程在 $K_w$ 上的第 $j$ 形式层，参数为 $t=-x/y$，故 $U_w(j)\cap E_0(F_v)=U_v(j)$。辅助点的 $b_w^K$、$B_K$ 和归一化范数完全沿用 (51.2)，不替换原 $F$ 分母。

记 $\mathcal T=\mathcal T_{\mathrm{ss,refl}}$。本节的 $r_{vj}$ 始终是原 (64.1) 的精确指数

$$
\Gamma_{vj}(q)=\langle[q]P_1+U_v(j),[q]P_2+U_v(j)\rangle,
\qquad r_{vj}=\exp\Gamma_{vj}(q),
\tag{67.4}
$$

并把 $\mathcal T$ 代入 (64.4)–(64.6)：

$$
\begin{aligned}
W_{\mathcal T,H}(R)
 &=\sum_{\substack{p>H,\ p\in\mathcal T\\v\mid p,\ j\ge1:\ r_{vj}\le R}}
       \frac{f_v\log p}{8},\\
a_{\mathcal T,H}(r)&=W_{\mathcal T,H}(r)-W_{\mathcal T,H}(r-1),\\
F_{\mathcal T,H}(t)
 &=\frac18\sum_{\substack{p>H\\p\in\mathcal T}}\log p
      \sum_{v\mid p}f_v\min\{b_v([qt]P_1),b_v([qt]P_2)\},\\
\mathcal M_{\mathcal T,H}(N)&=\frac1N\sum_{t=1}^NF_{\mathcal T,H}(t).
\end{aligned}
\tag{67.5}
$$

约定 $W(R)=0$ 对 $0\le R<1$ 成立；$r,t,N$ 为正整数。由 (62.5)–(62.6) 的逐地方行格关系，$F_{\mathcal T,H}(t)=G_{\mathcal T}(H;qt,1)$，且这是同一个 $t$ 上全部非零整数 $k$ 的共同质量最小值；全部地方同时由 $k=1$ 取得。

**定理 67.2（原两类超奇异反射的全部地方、全部深度消费者）。** 对所有整数 $M\ge1,H\ge7,N\ge1$ 和所有实数 $R\ge1$，统一有

$$
\begin{aligned}
W_{\mathcal T_{\mathrm{ss,refl}},H}(R)
 &\le36h_0q_H^2R^2+16(\log2)R,\\
\mathcal M_{\mathcal T_{\mathrm{ss,refl}},H}(N)
 &\le72h_0q_H^2N+16(\log2)(1+\log N).
\end{aligned}
\tag{67.6}
$$

精确平均仍为

$$
\mathcal M_{\mathcal T,H}(N)
 =\frac1N\sum_{r=1}^Na_{\mathcal T,H}(r)
                         \left\lfloor\frac Nr\right\rfloor.
\tag{67.7}
$$

以上每个和均保留支持内全部 $p>H$、每个原 $v\mid p$ 和全部正深度，没有 $p\le R$、$p\le N$ 或深度截止。两个实际反射符号均在量词内。

**证明（同一个原地方上的精确半点字符）。** 固定 $p\in\mathcal T$ 及原 $v\mid p$。原 (53.8)–(53.9) 给出 $g_v$ 的阶为 $2$，故 $F_v/\mathbb Q_p$ 是不分歧二次扩张，$e_v=1,f_v=2$。由于 $p\equiv3\pmod4$，$\mathbb Q_p(i)/\mathbb Q_p$ 也是不分歧二次扩张。因此对每个 $w\mid v$，$K_w=F_v$；$K/F$ 在 $v$ 分裂成两个地方。当前 $i$ 的像由当前 $w$ 指定，$K_w/\mathbb Q_p$ 的算术 Frobenius $\sigma_w$ 限制为原 $g_v$，并准确满足

$$
\sigma_w(i)=-i.
\tag{67.8}
$$

这里的 $[i]$ 只作为 $K_w$ 上定义的曲线自同态使用，不视为 $\mathbb Q_p$ 上定义的自同态；(67.8) 给出它在 Frobenius 下的共轭。

现将原实际坐标 (67.1) 代入 Frobenius。D 型有 $g_v(a)=a$、$g_v(b)=\epsilon b$、$g_v(c)=-\epsilon c$，其中 $\epsilon\in\{1,-1\}$ 取当前地方的实际符号。于是

$$
\sigma_wQ_1=[\epsilon]Q_1,\qquad
\sigma_wQ_2=[-\epsilon]Q_2,\qquad
\sigma_w([i]Q_2)=[-i][-\epsilon]Q_2=[\epsilon][i]Q_2.
\tag{67.9}
$$

S 型有 $g_v(a)=-a$、$g_v(b)=\epsilon c$、$g_v(c)=\epsilon b$，因此实际半点的两个纵坐标给出

$$
\sigma_wQ_1=[\epsilon]Q_2,\qquad
\sigma_wQ_2=[\epsilon]Q_1,
\tag{67.10}
$$

进而

$$
\begin{aligned}
\sigma_w(Q_1+Q_2)&=[\epsilon](Q_1+Q_2),\\
\sigma_w([i](Q_1-Q_2))
 &=[-i]([\epsilon]Q_2-[\epsilon]Q_1)
  =[\epsilon][i](Q_1-Q_2).
\end{aligned}
\tag{67.11}
$$

这些是特征零完备域中的等式，不是仅约化后的特征关系。它们使用原半点而没有二挠平移；原 $P_1,P_2$ 自身不被宣称同属一个字符。

固定相应的 $\nu\in\{D,S\}$ 和实际 $\epsilon$，在当前地方定义

$$
T_w=\{Z\in E_0(K_w):\sigma_wZ=[\epsilon]Z\},\qquad
\mathcal K_w(j)=T_w\cap U_w(j).
\tag{67.12}
$$

由 (67.9)–(67.11)，$H_{\nu,1},H_{\nu,2}\in T_w$，所以

$$
A_\nu,B_\nu\in[2]T_w.
\tag{67.13}
$$

原半点及其倍二来源为 Brox，[固定源码 “The quadratic-field elliptic curve” 及 `lem:independent`](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex)：该处的 $R_0=(1+a,2a)$ 经 $(x,y)\mapsto(x/b^2,y/b^3)$ 正好给出 $Q_1$，同时共轭给出所写负纵坐标的 $Q_2$。这里复用其模挠独立性；原四方向高度取 002 (16.21)。

**证明（单位扭曲、倍二像与交过滤）。** 在 (67.12) 的精确字符条件已经落实后，使用 §63 的同地方单位扭曲构造。$\epsilon=1$ 时取 $d=s=1$；$\epsilon=-1$ 时取剩余类非平方的单位 $d\in\mathbb Z_p^\times$，并在当前 $K_w$ 取 $s^2=d$，故 $\sigma_w(s)=-s$。群同构

$$
\begin{gathered}
E^{(d)}:Y^2=X^3-d^2X,\qquad
\phi_d:E^{(d)}(\mathbb Q_p)\longrightarrow T_w,\\
\phi_d(X,Y)=(X/d,Y/(ds))
\end{gathered}
\tag{67.14}
$$

的逆向坐标为 $X=dx,Y=ds\,y$。负号时，$\sigma_wx=x$、$\sigma_wy=-y$ 恰使这两个逆向坐标属于 $\mathbb Q_p$；正号时就是固定域的点。$O$ 和二挠点也包括在内。由于 $d,s$ 为单位，对非零形式点 $Z$，$t_d=-X/Y$ 满足

$$
t(\phi_dZ)=s\,t_d(Z),\qquad
\operatorname{ord}_w x(\phi_dZ)=v_p(X(Z)).
\tag{67.15}
$$

因此扭曲的第 $j$ 形式层准确映到 $\mathcal K_w(j)$，保留原 $x$ 深度。两条方程在 $p>7$ 都好约化。Silverman，*The Arithmetic of Elliptic Curves* 第二版，[VII.2.1–2.2，印刷页 188–191](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)，给出约化正合列及形式群对约化核的识别；[IV.6.3–6.4，印刷页 131–132](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的严格阈值在这里是 $1>1/(p-1)$。故形式对数给出

$$
\mathcal K_w(1)/\mathcal K_w(j)\simeq\mathbb Z/p^{j-1}\mathbb Z,
\qquad [2]:\mathcal K_w(j)\longrightarrow\mathcal K_w(j)
\text{ 为自同构}.
\tag{67.16}
$$

特别地，$\mathcal K_w(j)\subseteq[2]T_w$。这里包含的是交过滤；整个 $U_w(j)$ 的形式对数是秩二的 $\mathbb Z_p$ 模，交过滤是秩一，不能把整个 $U_w(j)$ 放进 $T_w$ 或其倍二像。作者[勘误](https://www.math.brown.edu/johsilve/AEC/AECErrata.pdf)对印刷页 122–124 的形式逆元、理想幂和参数对应的说明，以及页 131 对 IV.6.3(a) 分式域收敛的修正，均按此严格阈值使用；页 188–191 的约化记号按其更正理解。

扭曲的约化群在 (67.14) 下准确成为 $G_\epsilon=\ker(\pi_p-[\epsilon])$，且 $T_w\to G_\epsilon$ 满射、核为 $\mathcal K_w(1)$。负号的反向识别与 (67.14) 的逆坐标相同，使用 $k_w=\mathbb F_{p^2}$。§58 超奇异有限群计算 (58.10)、(58.14) 所需的条件在此全都成立：$a_p=0$ 由 §51 的 $x,-x$ 字符相消给出，$\#G_\epsilon=p+1$、$p\nmid p+1$，且全二挠在 $G_\epsilon$ 中。具体地，完整素于 $p$ 挠点结构使其不变因子为 $d_1\mid d_2$、$d_1d_2=p+1$，全二挠使 $2\mid d_1$；完整 $d_1$ 挠上的 Weil 配对及 $\pi_p=[\epsilon]$ 使 $d_1\mid p-1$，故 $d_1=2$。这正是该计算的同纤维应用，得到

$$
G_\epsilon\simeq\mathbb Z/2\mathbb Z\oplus
                      \mathbb Z/((p+1)/2)\mathbb Z,
\qquad [2]G_\epsilon\simeq\mathbb Z/D_p\mathbb Z,
\qquad D_p=(p+1)/4.
\tag{67.17}
$$

所用成熟输入为 Silverman [III.6.4、III.8.1、V.2.3–2.3.1](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)。挠点指阶整除 $m$ 的点，配对值域为标准 $\mu_m$，按作者页 69、93–98 的勘误；没有使用更强的一般同源配对值域断言。此计算只需超奇异的原曲线与两种 $\epsilon$，不要求原 $g_v$ 为中央作用。

现在才取商

$$
C_w(j)=[2]T_w/\mathcal K_w(j).
\tag{67.18}
$$

由约化、(67.16) 以及 $\mathcal K_w(1)\subseteq[2]T_w$，有正合列

$$
0\longrightarrow\mathcal K_w(1)/\mathcal K_w(j)
\longrightarrow C_w(j)\longrightarrow[2]G_\epsilon\longrightarrow0.
\tag{67.19}
$$

两端分别为阶 $p^{j-1}$ 和 $D_p$ 的循环群，两阶互素；有限交换群的主部分解遂给出

$$
C_w(j)\simeq\mathbb Z/(D_pp^{j-1})\mathbb Z.
\tag{67.20}
$$

这将 §63 的单位扭曲和形式核论证接到 (67.9)–(67.13) 的反射辅助半点，而没有将 §63 原来的中央支持直接扩大。

**证明（原周期只消去变换后的实际子群）。** 对满足 $r_{vj}\le R$ 的原三元组 $(p,v,j)$，写 $r=r_{vj}$。由原精确指数的定义，

$$
[qr]P_1,[qr]P_2\in U_v(j)\subseteq U_w(j).
\tag{67.21}
$$

原 $[i]$ 在 $K_w$ 上满足 $t([i]Z)=it(Z)$；$i$ 是单位，所以 $[i]$ 保每个 $U_w(j)$。对 S 型还用其子群性，故两种类型都满足

$$
[qr]A_\nu,[qr]B_\nu\in U_w(j)\cap T_w=\mathcal K_w(j).
\tag{67.22}
$$

因此实际子群

$$
\Lambda_{wj}(q)
=\langle[q]A_\nu+\mathcal K_w(j),
          [q]B_\nu+\mathcal K_w(j)\rangle\subseteq C_w(j)
\tag{67.23}
$$

循环，且被整数 $r$ 消去。若 $r'_{wj}=|\Lambda_{wj}(q)|$，则

$$
r'_{wj}\mid r_{vj},\qquad r'_{wj}\le r_{vj}\le R.
\tag{67.24}
$$

这里只用了原周期的消去性质。没有把 $r'_{wj}$、原 $r_{vj}$ 或环境阶 $D_pp^{j-1}$ 相等；也没有要求原 $\Gamma_{vj}(q)$ 自身循环。

置 $L=\lfloor\sqrt R\rfloor\ge1$。将 $(L+1)^2>R$ 个向量 $(u_1,u_2)\in\{0,\ldots,L\}^2$ 映到 $[qu_1]A_\nu+[qu_2]B_\nu+\mathcal K_w(j)$。由 (67.24)，必有两向量同像；其差给出

$$
m\ne0,\quad |m_1|,|m_2|\le L,\qquad
Z_{\nu,m}=[q]([m_1]A_\nu+[m_2]B_\nu)\in\mathcal K_w(j).
\tag{67.25}
$$

这是在原深度 $j$ 的短关系，不只是在第一约化层。点对、$q$ 及全局系数范围先固定；$m$ 可以随实际地方和深度改变。

**证明（同一完整点族支付全部扩域地方）。** 在所有局部选择之前，取带索引的全局有限族

$$
\mathcal P_L(q)=
 \bigl(Z_{\nu,m}\bigr)_{
 \substack{\nu\in\{D,S\},\ m\in\mathbb Z^2\setminus\{0\}\\
                     |m_1|,|m_2|\le L}}.
\tag{67.26}
$$

即使不同索引给出相同点也逐份支付。由原四方向正交高度 (16.21)，直接有

$$
\begin{aligned}
\widehat h(Z_{D,m})&=h_0q^2(m_1^2+m_2^2),\\
\widehat h(Z_{S,m})&=2h_0q^2(m_1^2+m_2^2).
\end{aligned}
\tag{67.27}
$$

第二式中的四方向系数依次为 $qm_1,qm_2,qm_1,-qm_2$。因此族中全部点都非挠、非零，原整 $x$ 分母合法，包括一个系数为零的情形；这里从未把原两点视为一个点的 CM 倍数。

对每个满足 $r_{vj}\le R$ 的原三元组，将其权重分配到全部 $w\mid v$。这里每个 $w$ 都有 $e_w=1,f_w=f_v=2$，且恰有两个 $w\mid v$，故准确有

$$
\sum_{w\mid v}\frac{f_w}{16}=\frac{f_v}{8}.
\tag{67.28}
$$

在每个提升后的 $(p,w,j)$，选择 (67.25) 的一个索引 $(\nu,m)$。固定该索引和 $w$ 后，分配给它的不同正整数 $j$ 都满足 $j\le b_w^K(Z_{\nu,m})$，所以其层数至多为这个分母指数。于是

$$
\begin{aligned}
W_{\mathcal T,H}(R)
&=\sum_{\substack{p>H,\ p\in\mathcal T\\v\mid p,\ j\ge1:\ r_{vj}\le R}}
       \sum_{w\mid v}\frac{f_w\log p}{16}\\
&\le\sum_{\substack{\nu\in\{D,S\},\ m\ne0\\|m_1|,|m_2|\le L}}
                       \log\|B_K(Z_{\nu,m})\|_K.
\end{aligned}
\tag{67.29}
$$

这里对每个合格 $p$ 上的全部八个 $K$ 地方都求和，既没有只选一个 $w\mid v$，也没有把同一 $v$ 的两个 $i$ 嵌入当作免费重合。每个点用自己的完整 $K$ 分母支付其所有分配项；各地方的不同选择由同一个完整有限族承担。

对族中每个 $Z$，直接使用 (51.18)–(51.19) 的绝对高度分解，

$$
h(x(Z))=2\log\|B_K(Z)\|_K+
 \frac1{16}\sum_{\tau:K\hookrightarrow\mathbb C}
                         \log\max(1,|x(\tau Z)|),
\qquad
\log\|B_K(Z)\|_K\le\widehat h(Z)+\log2.
\tag{67.30}
$$

此式包括全部 $16$ 个嵌入和全部有限地方；右端常数来自原 002 (12.7) 对所有代数点的高度比较。故没有把只对 $F$ 点写出的 003 (49.8) 直接套给复辅助点，也没有漏付扩域费用。

非零系数的个数为 $(2L+1)^2-1=4L(L+1)$，并且

$$
\sum_{\substack{m\ne0\\|m_1|,|m_2|\le L}}(m_1^2+m_2^2)
=\frac23L(L+1)(2L+1)^2.
\tag{67.31}
$$

将 (67.27)、(67.30) 对两族全部索引求和，(67.29) 给出

$$
\begin{aligned}
W_{\mathcal T,H}(R)
&\le2h_0q^2L(L+1)(2L+1)^2
                    +8(\log2)L(L+1)\\
&\le36h_0q^2L^4+16(\log2)L^2\\
&\le36h_0q^2R^2+16(\log2)R.
\end{aligned}
\tag{67.32}
$$

末两步只用 $L+1\le2L$、$2L+1\le3L$ 和 $L^2\le R$。有限系数总和是纸面恒等式；短关系—完整点族高度的步骤沿用定理 64.2 的消费者方法，不另立一般群论或局部曲线定理。

**证明（精确 floor 平均及其上界）。** 定理 64.2 的有限性和 (64.10)–(64.11) 对任意支持成立：共同深度是条件 $r_{vj}\mid t$ 在 $j\ge1$ 上的指示函数之和。这直接给出 (67.7)。令 $W=W_{\mathcal T,H}$、$a=a_{\mathcal T,H}$、$A=36h_0q^2$、$B=16\log2$，以及 $\mathfrak h_N=\sum_{r=1}^N1/r$。非负性与有限分部求和给出

$$
\begin{aligned}
\mathcal M_{\mathcal T,H}(N)
&=\frac1N\sum_{r=1}^Na(r)\left\lfloor\frac Nr\right\rfloor
 \le\sum_{r=1}^N\frac{a(r)}r\\
&=\frac{W(N)}N+\sum_{r=1}^{N-1}\frac{W(r)}{r(r+1)}\\
&\le A(2N-\mathfrak h_N)+B\mathfrak h_N\\
&\le2AN+B(1+\log N).
\end{aligned}
\tag{67.33}
$$

这里第一行的不等式没有改成等式；原平均与 $\sum a(r)/r$ 不必相等。$N=1$ 包括在内。代回 $A,B$ 即得 (67.6) 的第二式，常数对 $H,M,R,N$ 统一。

用白话说，反射先把两个方向分成相反符号，而同一地方的 Frobenius 又把 $i$ 变成 $-i$。给其中一个方向乘 $i$，两个负号就抵消；交换反射先取和与差，再做同样的操作。原实际半点保证辅助点确在这个同字符群的倍二像里。该像在每个深度的商都循环，原周期只需消去里面的两个辅助点，就足以找到平方根长度的关系。每个地方选到的关系可以不同，所以两种类型的全部候选组合及全部扩域地方都一起支付；这才给出二次周期质量和线性平均预算。

本定理只控制同一个 $k=1$ 的最小共同质量的平均上界，不给出任意移动 $k$ 的上界或逐个 $t$ 的线性界。实际半点和高度输入来自上述固定原文与原 002；局部曲线、形式群、完整挠点、Weil 配对和有限交换群仅作为此原支持消费者内部的成熟输入。文献对应限于所列原始来源及本卷 §§51、53、58、63–66，不据此主张文献优先性。$\square$

**定理 67.3（从原完整支持剩余条件中剥离反射支持）。** 沿用 (65.1) 的 $\Sigma_{\mathrm{all}}=\{p>7\}$ 和 (66.1) 的 $\mathcal T_{\mathrm{ord,ns}}$，置

$$
\begin{aligned}
\Sigma_\dagger
&=\Sigma_{\mathrm{all}}\setminus
 (S_0\sqcup\mathcal T_{\mathrm{ord,ns}}\sqcup
                      \mathcal T_{\mathrm{ss,refl}})\\
&=\{p>7:p\equiv3\pmod4,\ (\chi_2(p),\chi_7(p))=(-1,-1)\}\\
&\quad\sqcup
 \{p>7:p\equiv1\pmod4,\ (\chi_2(p),\chi_7(p))=(1,1)\}.
\end{aligned}
\tag{67.34}
$$

记已支付支持为 $\Sigma_{\mathrm{paid}}=S_0\sqcup\mathcal T_{\mathrm{ord,ns}}\sqcup\mathcal T_{\mathrm{ss,refl}}$。对全部原参数统一有

$$
\begin{aligned}
W_{\Sigma_{\mathrm{paid}},H}(R)
 &\le368h_0q_H^2R^2+124(\log2)R,\\
\mathcal M_{\Sigma_{\mathrm{paid}},H}(N)
 &\le736h_0q_H^2N+124(\log2)(1+\log N).
\end{aligned}
\tag{67.35}
$$

因而对每个固定的 $H,M$，在相应极限中保持同一个 $q=q_H$ 不变，有

$$
\begin{aligned}
\mathcal M_{\mathrm{all},H}(N)=o(q^2N^2)
&\quad\Longleftrightarrow\quad
W_{\Sigma_\dagger,H}(R)=o(q^2R^3)\\
&\quad\Longleftrightarrow\quad
\mathcal M_{\Sigma_\dagger,H}(N)=o(q^2N^2).
\end{aligned}
\tag{67.36}
$$

**证明。** (66.27) 已识别 $S_0$ 为超奇异标量支持；从该处的 $\Sigma_*$ 再删去 (67.2) 的两类反射，恰剩超奇异旋转型和普通标量型，即 (67.34)。这些支持互不相交，故原 $W$、$a$、$F$ 和 $\mathcal M$ 都准确相加。将 (66.28) 与 (67.6) 相加即得 (67.35)。对固定 $H,M$，右侧分别为 $o(q^2R^3)$ 和 $o(q^2N^2)$。从完整支持的非负精确分解中剥离这两项，再用定理 65.1 已证明的完整 floor 平均与次三次周期质量的等价，便得 (67.36)。没有对随 $N$ 移动的 $H$ 或 $M$ 断言统一小量。

式 (67.36) 的剩余小量条件仍待证明；(67.35) 不能代替它。超奇异旋转的实际作用平方为取负，原两个半点没有从 (67.9)–(67.11) 得到这里所需的共同 $\pm1$ 字符；普通标量也没有由本定理获得同样的循环倍二环境。这里既不判定其实际子群必然不循环，也不把这两项接口缺失当作原命题的反例。

用白话说，全支持里可以再准确拿掉两种超奇异反射，尚需控制的素数类型缩为超奇异旋转和普通标量。完整共同分母的次二次平均仍要求这些剩余地方及全部深度的周期质量严格小于三次量级；本条只证明这个剩余条件的准确等价，并未证明条件本身。$\square$

---

## 追加锚（本行以下为增补区）

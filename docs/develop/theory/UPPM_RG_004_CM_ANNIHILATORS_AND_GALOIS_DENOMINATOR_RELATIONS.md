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

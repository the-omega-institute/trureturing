# 八次原域乘法系数的 Gale 商与内在光滑判据

## 106. 原系数代数、有序 Gale 商与原域下降

**定义 106.1（同一个原域中的系数对象）。** 设 $F$ 为特征零域，$D/F$ 为一个固定的可分**域**扩张，$[D:F]=8$。固定原 $F$-基 $e_1,\ldots,e_8$，令 $\Omega=e_1\wedge\cdots\wedge e_8$，以取 $\Omega$ 的系数定义行列式。置

$$
X_D=\operatorname{Gr}_F(4,D),\qquad
P_B(x)=\det[B,M_xB],\qquad
S_C=\{r\in D^\times:C\cap rC\ne0\}.
\tag{106.1}
$$

这里 $B$ 是 $C\subset D$ 的包含帧，$M_x$ 是同一个域 $D$ 的乘法。换帧 $B\mapsto Bg$ 使 $P_B$ 乘 $\det(g)^2$，所以 $[P_C]$ 与帧无关。正标签仅指 $S_C$ 的元素，不涉及序关系。对 $r\in D^\times$，域性及半维性给出

$$
r\in S_C\quad\Longleftrightarrow\quad
P_C(r)=0\quad\Longleftrightarrow\quad
r=u/v\quad(u,v\in C\setminus\{0\}).
\tag{106.2}
$$

令 $D^\vee=\operatorname{Hom}_F(D,F)$。取任意迹对偶基 $(f_j),(f_j^\sharp)$，原内在系数空间为

$$
H_D=\left\{Q\in\operatorname{Sym}_F^4(D^\vee):
\partial_{1_D}Q=0,\quad
\sum_j\partial_{af_j}\partial_{f_j^\sharp}Q=0\quad(a\in D)\right\}.
\tag{106.3}
$$

沿用 [source033](./AURIC_R5_033_ALL_DEGREE_ARITHMETIC_POSITIVE_CERTIFICATES.md) 定义 81.1 及式 (81.4)–(81.5) 的同一对象和输入：$\dim_FH_D=14$，每个实际 $C\in X_D(F)$ 的 $P_C$ 非零，这些多项式张成 $H_D$。这些是该卷所引用 source026、source029 的结果，不另作新的系数维数或非零性命题。原系数映射及实际闭包为

$$
\phi_D:X_D\dashrightarrow\mathbb P(H_D),\qquad
C\longmapsto[P_C],\qquad
\Gamma_D=\overline{\phi_D(X_D(F))}^{\,\mathrm{red},F}.
\tag{106.4}
$$

$\mathbb P(H_D)$ 参数化 $H_D$ 中的直线。次数始终相对于这一原嵌入计算。$\phi_D$ 在所有实际点有定义，但在几何 Grassmannian 上仍是有理映射。

**定义 106.2（系数分次与范数权重环）。** 四帧空间是 $D^4$；允许帧退化，所说函数均是这个仿射空间上的多项式。对 $n\ge0$，令 $\mathscr R_{D,n}$ 为满足下列代数群半不变恒等式的多项式函数：

$$
f(Bg)=\det(g)^{2n}f(B),\qquad
f(aB)=N_{D/F}(a)^n f(B),
\quad g\in\operatorname{GL}_4,\ a\in\operatorname{Res}_{D/F}\mathbb G_m.
\tag{106.5}
$$

恒等式按群概形理解，故在任意扩域后仍成立。置 $\mathscr R_D=\bigoplus_{n\ge0}\mathscr R_{D,n}$。它也可看成 $\bigoplus_nH^0(X_D,\mathcal O_{X_D}(2n))$ 中具有指定范数权重的部分；这里 $\mathcal O_{X_D}(1)=\det(\mathcal S^\vee)$。$n$ 是**系数次数**，对应 Plücker 次数 $2n$。

乘法交换性给 $[aB,M_xaB]=M_a[B,M_xB]$，故 $P_{aB}(x)=N(a)P_B(x)$。每个线性系数泛函拉回后因此属于 $\mathscr R_{D,1}$。定义

$$
\alpha_D:H_D^\vee\longrightarrow\mathscr R_{D,1},\qquad
\alpha_D(\ell)(B)=\ell(P_B),\qquad
\mathscr A_D=\operatorname{im}\left(
\operatorname{Sym}_F(H_D^\vee)\longrightarrow\mathscr R_D\right).
\tag{106.6}
$$

这一定义保留原乘法、原系数嵌入及原体积形式；$\mathscr A_D$ 是像代数，不是自由对称代数。

**定理 106.3（原系数概形像的完整 Gale 环识别）。** 令 $k=\overline F$，按原八个嵌入 $\sigma_i:D\to k$ 分裂 $D_k\simeq k^8$。设

$$
R=\bigoplus_{n\ge0}
H^0\bigl((\mathbb P_k^3)^8,\mathcal O(n,\ldots,n)\bigr)^{\operatorname{SL}_4},
\qquad S=k[R_1],\qquad N=\operatorname{Proj}R.
\tag{106.7}
$$

令 $\tau$ 为保持八个标签的 Gale 对偶。它在 $\mathscr R_D$ 上有原域定义的分次对合 $\tau_D$，并且有精确等式和同构

$$
\Gamma_D=\operatorname{Proj}\mathscr A_D,\qquad
\mathscr A_D=\mathscr R_D^{\tau_D},\qquad
\mathscr A_D\otimes_Fk\simeq S=R^\tau.
\tag{106.8}
$$

第一式是原有理系数映射的概形像闭包，也等于定义 106.1 的实际点约化闭包。置 $N_D=\operatorname{Proj}\mathscr R_D$，则

$$
\pi_D:N_D\longrightarrow\Gamma_D
\tag{106.9}
$$

是真正的有限二阶群商。$N_D$ 与 $\Gamma_D$ 分别是有序八点商及其 Gale 商沿原嵌入标签的 Galois 作用所作的扭曲；没有再对标签取 $S_8$ 商。以上识别保持原系数极化，且

$$
\dim\Gamma_D=9,\qquad
\deg_{\mathbb P(H_D)}\Gamma_D=56.
\tag{106.10}
$$

证明。先在分裂域中保留体积标量。令 $J=(\sigma_i(e_j))$，$d_\Omega=\det J\ne0$。帧在分裂坐标中的矩阵仍记 $B$，行子式记为 $p_I(B)=\det B_I$，$|I|=4$；$\epsilon_I$ 是依次列出 $I$、$I^c$ 的置换号。由原行列式的 Laplace 展开，准确地有

$$
P_B(x)=d_\Omega^{-1}
\sum_{|I|=4}\epsilon_I p_I(B)p_{I^c}(B)x_{I^c},
\qquad x_I=\prod_{i\in I}x_i.
\tag{106.11}
$$

$\epsilon_{I^c}=\epsilon_I$，因为交换两个四元块的号是 $(-1)^{16}=1$。公共因子 $d_\Omega^{-1}$ 正是从分裂坐标行列式回到原体积的因子。

经典 $\operatorname{SL}_4$ 第一基本不变量定理把矩阵不变量写成四行子式的多项式。等行多重次数 $(n,\ldots,n)$ 对应恰好 $2n$ 个括号。因此 $\mathscr R_D\otimes_Fk=R$；特别地，$R_1$ 由所有 $p_Ip_{I^c}$ 张成。(106.11) 表明系数拉回的像恰为 $R_1$，不是仅在函数域中相等。由 $H_D$ 的原张成性，$\alpha_D$ 单射；亦可与 HMSV §1.2 的 $\dim R_1=14$ 对照。因此 $\alpha_D$ 是十四维线性同构，而全部分次像恰为 $S$。

令 $I_D$ 为 (106.6) 中的齐次核。帧多项式环是整环，故 $I_D$ 是素理想。齐次方程属于 $I_D$，恰当且仅当在系数映射定义域上的拉回恒为零，这给概形像的闭包 $\operatorname{Proj}\mathscr A_D$。另一方面，Grassmann 大胞腔是仿射空间；$F$ 无限，所以 $X_D(F)$ 在 $X_D$ 中几何稠密，且实际点均属于定义域。一个原域齐次方程在全部实际系数点上为零，当且仅当其拉回恒为零。因此实际约化闭包有同一个理想 $I_D$。各分次映射的核与像都与平坦域扩张交换，故这个概形像识别也与扩域交换。

以下说明所用的经典输入及其域范围。对分裂空间取双线性形式 $\sum_i u_iv_i$，不取复共轭。外代数对偶在 Plücker 坐标上给

$$
\tau(p_I)=\epsilon_Ip_{I^c}.
\tag{106.12}
$$

它把可分解四向量送到其正交补的四向量，因而保持 Plücker 理想，且平方为一。一个等行权重 $n$ 的括号单项式含 $2n$ 个括号；补集把每个指标出现次数从 $n$ 变成 $2n-n=n$，故保持 $R_n$。对偶在 $R_1$ 上为恒等。这里使用 Howard–Millson，*The Chevalley Involution and a Duality of Weight Varieties*，math/0409260v2，Theorems 1.4、1.6、1.12、Lemma 4.13、Corollary 4.14 的带号外代数构造。其复数语境本身不承担任意特征零域上的结论：上述子式、补集号及 Plücker 恒等式都定义在 $\mathbb Q$ 上，因而给出本处需要的有理系数环自同构。

更强的完整环等式

$$
S=k[R_1]=R^\tau
\tag{106.13}
$$

作为 Howard–Millson–Snowden–Vakil（下称 HMSV），*The geometry of eight points in projective space*，arXiv:1103.5255v1，§1.2、§8、Propositions 8.1–8.2 的**完整已发表输入**使用。该输入的证明以计算辅助为重要组成部分：§8 使用 4ti2、Magma 及相应线性代数计算。本处不独立重证这一完整不变量环结论。仅知道 $R$ 的生成次数和生成元商空间上的正负作用，并不足以排除反不变量乘积产生额外不变量；(106.13) 取的是文献明示的完整环断言，而非这一不充分推论。

为把该输入用于任意特征零域，先令 $R_{\mathbb Q}$ 为有理系数的同一个括号环。其各分次部分及 $\tau$ 都定义在 $\mathbb Q$ 上。括号描述及标准单项式基使它的域扩张成为相应底域上的不变量环。取不变量与域扩张交换，因为 $\frac12(1+\tau)$ 是投影。于是每个次数的

$$
(R_{\mathbb Q}^{\tau})_n/\bigl(\mathbb Q[R_{\mathbb Q,1}]\bigr)_n
$$

在张量到 $\mathbb C$ 后为零，忠实平坦性使它原来即为零。再从 $\mathbb Q$ 扩域，得到分裂情形在任意特征零域上的 (106.13)，不要求 $F$ 嵌入 $\mathbb C$。

还须在**线性环层面**处理有序标签和体积，而不能只用射影等变性。若 $g_\rho$ 是 $\rho\in S_8$ 的行置换矩阵，分裂体积下的行列式 $\widetilde P$ 满足

$$
\widetilde P_{g_\rho B}(x)
=\operatorname{sgn}(\rho)\,
\widetilde P_B(g_\rho^{-1}x).
\tag{106.14}
$$

设 $E=k^8$，$H_E$ 表示分裂代数的内在多项式空间。其普通变量置换作用与括号的行置换作用之间，精确的线性对应是

$$
H_E^\vee\otimes(\det E)^\vee\simeq R_1.
\tag{106.15}
$$

这是收缩取系数所得的对应：不选体积时，原多项式取值于 $\det E$，所以系数拉回取值于 $R_1\otimes\det E$。选标准体积后，(106.15) 正是 (106.14) 的符号。相应地，系数坐标代数的次数 $n$ 带有 $(\det E)^{\otimes n}$ 因子；它不是未经扭曲的同一 $S_8$ 线性表示。HMSV 的括号表示类型 $V_{(2,2,2,2)}$ 与系数空间的对偶类型之间的符号因子由此保留。

取一个有限 Galois 分裂域 $E'/F$。它对八个原嵌入的置换为 $\rho_\gamma$。在 (106.11) 中，$\gamma(d_\Omega)=\operatorname{sgn}(\rho_\gamma)d_\Omega$；该标量恰与互补子式系数的行置换符号抵消。因此原系数拉回是带完整半线性作用的映射，不存在用射影等变性替代线性下降的步骤。对偶与行置换在单个括号上的交换差一个 $\operatorname{sgn}(\rho_\gamma)$；在 $R_n$ 中有 $2n$ 个括号，故这差异为一。于是 $\tau$ 与原半线性 Galois 作用在**整个** $R$ 上交换，下降成 $\tau_D$。在 $\mathscr R_D$ 的内在定义 (106.5) 中，这就是同一个下降环。由 (106.11)、(106.13) 及忠实平坦性，得到 $\mathscr A_D=\mathscr R_D^{\tau_D}$。这证明 (106.8)，也同时确定了原有序 $S_8$/Galois 扭曲；$\rho_\gamma$ 的像无须是全 $S_8$。

$R$ 有限生成，且每个 $r\in R$ 都满足

$$
T^2-(r+\tau r)T+r\tau r=0
\tag{106.16}
$$

的整性方程，所以 $R$ 是 $S$ 上的有限模。对正次齐次 $r$，同一方程说明 $R_+\subset\sqrt{S_+R}$；因此 $\operatorname{Proj}R\to\operatorname{Proj}S$ 处处有定义且有限。在不变齐次截面的仿射开集上，它就是有限群的不变量环商，几何纤维是 $\tau$ 轨道。这些性质沿分裂域下降，给 (106.9)。若需区分正规化，矩阵多项式环对 $\operatorname{SL}_4$ 与行范数一环面取不变量正是 $R$：范数一条件迫使各行次数相等。不变量子环保持整闭，因为一个不变分式若整于不变子环，先由原整环整闭性属于原环，再由不变性属于不变子环。故 $R$、$S$ 整闭，$\Gamma_D$ 本身已正规；(106.8) 没有将原像换成另一个正规化。

最后，HMSV §1.4 给出

$$
\operatorname{Hilb}_S(z)
=\frac{1+4z+10z^2+20z^3+21z^4}{(1-z)^{10}}.
\tag{106.17}
$$

这一级数同样是该文的计算辅助输入，在此不作独立的纯纸面复算。$S$ 在系数次数一生成，故 (106.17) 给 $\dim\operatorname{Proj}S=9$、原 $\mathcal O(1)$ 次数 $1+4+10+20+21=56$。前面十四维线性系的精确识别保证这是原 $\mathbb P(H_D)$ 中的次数，而非其他双有理模型的次数。Hilbert 函数、维数和次数在域扩张下不变，完成证明。$\square$

## 107. 统一轨迹、乘法对偶关系与原域迹自关联

**定义 107.1（统一开集及正确类型的关系）。** 在 $D_k=k^8$ 中，$U\subset X_{D,k}$ 是所有四行子式均非零的开集；称其中的四平面为统一。该条件与帧和原嵌入的排序无关，下降成 $F$-开集 $U_D$。令

$$
T=(\mathbb G_m^8)/\mathbb G_m,\qquad
T_D=(\operatorname{Res}_{D/F}\mathbb G_m)/\mathbb G_m.
\tag{107.1}
$$

对实际四平面 $C$，定义原乘法映射及其对偶核

$$
\mu_C:\operatorname{Sym}_F^2C\longrightarrow D,\quad uv\longmapsto uv,
\qquad C^2=\operatorname{im}\mu_C,
\qquad K_C=\ker\bigl(\mu_C^\vee:D^\vee\to(\operatorname{Sym}_F^2C)^\vee\bigr).
\tag{107.2}
$$

这里关系属于 $K_C$，**不是** $\ker\mu_C$。若 $c_i=\sigma_i|_{C_k}\in C_k^\vee$，分裂后的关系为

$$
K_C\otimes_Fk
=\left\{(a_i)\in k^8:
\sum_{i=1}^8a_i\,c_i\otimes c_i=0\right\},
\qquad B^{\mathsf t}\operatorname{diag}(a_i)B=0.
\tag{107.3}
$$

张量等式按对称双线性形式解释，即其在 $(u,v)$ 上的值为 $\sum_i a_ic_i(u)c_i(v)$；所有转置均为双线性转置。

**定理 107.2（原系数统一开集上的光滑前商及饱和性）。** 记 $\pi=\pi_D\times_Fk$。设 $\Gamma^u\subset\Gamma_{D,k}$ 为原平方自由单项式系数全部非零的开集，$Y=\pi^{-1}(\Gamma^u)\subset N$。则 $Y=U/T$ 是统一有序八点的几何商，光滑且维数九。每个统一有序配置的有效 $\operatorname{PGL}_4$ 稳定子平凡，$U\to Y$ 是七维有效环面的光滑主丛。$\tau$ 保持 $Y$，且

$$
\Gamma^u=Y/\langle\tau\rangle.
\tag{107.4}
$$

这些开集与态射均沿原标签扭曲下降到 $F$，记开集的下降为 $\Gamma_D^u$、$Y_D$。特别地，统一系数点的整个商纤维均在统一轨迹内，不含隐藏的非统一分支。原 $X_D\dashrightarrow\Gamma_D$ 在这里先取七维环面商，再取有限 Gale 商；它本身不是有限双覆盖。

证明。若一个真向量子空间 $L\subset k^4$ 维数为 $r<4$，统一性使 $\mathbb P(L)$ 至多含 $r$ 个配置点，否则其中至多四个评价行相关。这严格小于等权八点稳定性的界 $2r$，故满足 Hilbert–Mumford 严格稳定条件。

前四个点构成基，第五点在这组基下每个坐标均非零：若某坐标为零，第五行和其余三个基行就相关。因而前五个点是射影标架。将它们规范为

$$
[1:0:0:0],\ [0:1:0:0],\ [0:0:1:0],\ [0:0:0:1],\ [1:1:1:1].
\tag{107.5}
$$

逐点固定前四点的射影变换是对角的，再固定第五点就只能是恒等。故有效 $\operatorname{PGL}_4$ 稳定子平凡。$\operatorname{SL}_4$ 的中心 $\mu_4$ 在射影配置上无效，不能将其计为额外的有效稳定子。

剩下三个点的四个坐标也均非零；将各点第一坐标定为一，余下九个坐标只受所有四行子式非零的开条件。这给出 $Y$ 为 $\mathbb A_k^9$ 的一个非空开集，故光滑九维。其非空性也可取八个不同参数的三次有理正规曲线点，由 Vandermonde 行列式得到。

在 Grassmannian 的帧上，先以右乘规范前四行为单位阵，再用可逆对角列变换和行缩放使第五行为 $(1,1,1,1)$，最后将其余三行第一项定为一。每一步仅除以统一性保证非零的子式或坐标，所得九参数在 $U$ 上正则。剩余自由度恰为 $T$，且规范唯一到公共行缩放。于是 $U\to Y$ 在此规范下是主 $T$ 丛；等价地，在分裂情形可由这个规范取截面。这也直接证明环面稳定子平凡，且商的切空间核恰为七维轨道切空间。范数一环面到 $T$ 的核 $\mu_8$ 在 Grassmannian 上无效，不能与有效环面或 Gale 群混同。

为确定这确是 $N$ 中的开集而非仅一个抽象模空间，使用 (106.7) 的同一个等行权重环。矩阵的列基变换与行缩放分别给射影配置的 $\operatorname{PGL}_4$ 商及 Grassmannian 的 $T$ 商；它们的半不变量均为该环。故其 GIT 商是 $N$，在稳定开集上的几何商正是以上规范空间。这是 Gelfand–MacPherson 对应在此矩阵图表上的实现；环定义及规范公式都为有理系数，不依赖复数拓扑论证。

记 $q_I=\epsilon_Ip_Ip_{I^c}\in R_1$。由 (106.11)，$\Gamma^u$ 就是所有 $q_I$ 非零的系数开集。在 $N$ 上全部 $q_I$ 非零的原像，要求每个 $p_I$ 非零，恰为统一稳定配置的商。因而

$$
\pi^{-1}(\Gamma^u)=Y,
\qquad
\text{Grassmann 半稳定域中 }Y\text{ 的原像}=U.
\tag{107.6}
$$

特别地，非统一配置不能与统一配置具有同一个系数点。$\tau$ 交换互补子式，保持 $U$，并在 $R_1$ 上恒等，故保持上述开集。有限商限制后给 (107.4)，这里的局部环就是原 $\Gamma_D$ 的局部环。所有非零条件在 Galois 作用下仅被置换并乘非零标量，故开集和图表下降；光滑性及主丛性质可在分裂域上忠实平坦检验。

最后，分裂坐标四平面有所有互补子式乘积为零，所以原系数线性系确有几何基点；实际点非零性不将全局有理映射变成全局态射。统一域上的系数纤维包含七维 $T$ 轨道，而有限的是 $Y\to\Gamma^u$。$\square$

**定理 107.3（唯一满支撑关系与原域迹自关联）。** 对每个实际统一四平面 $C\subset D$，$\dim_F C^2\in\{7,8\}$。分裂后每个非零 $K_C$ 关系都有八项满支撑，且 $\dim_F K_C\le1$。若 $y_C\in Y_D(F)$ 是 $C$ 的前商像，以下条件等价：

$$
\begin{aligned}
&\tau_D(y_C)=y_C;\\
&K_C\ne0;\\
&C^2\ne D;\\
&\exists a\in D^\times:\quad aC=C^{\perp\operatorname{Tr}},
\end{aligned}
\qquad
C^{\perp\operatorname{Tr}}
=\{z\in D:\operatorname{Tr}_{D/F}(zC)=0\}.
\tag{107.7}
$$

成立时 $C^2$ 恰为七维，所有可用的 $a$ 是唯一一条 $F$ 直线的非零部分。

证明。先证满支撑；这段线性代数对 $U(k)$ 的每个四平面均适用。若 (107.3) 的非零关系支撑 $J$ 有 $s\le7$ 项，$k^J$ 上的对角形式 $\sum_{i\in J}a_iu_iv_i$ 非退化。$C_k$ 向这些坐标的评价像是该形式的全迷向子空间。统一性使此像维数为 $\min(4,s)$：至多四行全独立，至少四行则秩为四。非退化 $s$ 维双线性空间的迷向子空间 $L$ 满足 $L\subset L^\perp$，所以

$$
2\min(4,s)\le s.
\tag{107.8}
$$

对 $1\le s\le7$ 均矛盾。因此每个非零关系八项全非零。两条独立关系若存在，可线性组合消去第一坐标而仍非零，再次矛盾。于是关系空间至多一维，$\operatorname{rank}\mu_C=8-\dim K_C$ 为七或八。

设 $W\subset k^8$ 为评价四平面。Gale 对偶为 $W^\perp$，且 $Y$ 是几何环面商。因此 $y_C$ 固定，恰当且仅当存在各项非零的 $(a_i)$，使

$$
W^\perp=\operatorname{diag}(a_i)W.
\tag{107.9}
$$

此式蕴含 (107.3)。反过来，一个非零关系有满支撑，故对角矩阵可逆；关系使 $\operatorname{diag}(a_i)W\subset W^\perp$，两边均四维，因而相等。这证明几何固定等价于对偶乘法核非零。秩与域扩张交换，遂得前面三个条件在原域上的等价。这是经典自关联判据在原乘法模型中的具体连接：Eisenbud–Popescu，*The Projective Geometry of the Gale Transform*，math/9807127v1，Theorem 7.1 将自关联联系到消去乘积空间且生成对偶模的泛函，Corollary 7.4 将稳定点集的自关联联系到二次条件不独立；后者归于 Coble、Dolgachev–Ortland。这里满支撑与唯一性已由 (107.8) 直接给出。

现在在原域中证明最后一个条件，避免对几何对角参数作未经证明的逐项下降。可分扩张的迹配对 $b(u,v)=\operatorname{Tr}_{D/F}(uv)$ 非退化，因此 $D\simeq D^\vee$。若 $C^2\ne D$，其迹湮灭子

$$
A_C=\{a\in D:\operatorname{Tr}_{D/F}(aC^2)=0\}
\tag{107.10}
$$

含非零原域元素 $a$。$D$ 是域，所以 $a\in D^\times$。对 $c,c'\in C$，$\operatorname{Tr}(acc')=0$，故 $aC\subset C^{\perp\operatorname{Tr}}$；两者均四维，得到等号。反向若有此等号，非零泛函 $z\mapsto\operatorname{Tr}(az)$ 消去 $C^2$，故 $C^2\ne D$。统一时 (107.3) 的一维性下降为 $\dim_F A_C=1$，给出唯一 $F$ 线。分裂后的关系向量恰为 $(\sigma_i(a))$。

原迹正交满足 $(aC)^{\perp\operatorname{Tr}}=a^{-1}C^{\perp\operatorname{Tr}}$，并且分裂后就是上述双线性正交。因此它也在 $T_D$ 商上给 $\tau_D$。此论证从实际 $C$ 出发，在同一个 $D$ 中构造 $a$；不要求任意商的 $F$ 点可提升为实际窗口。$\square$

## 108. 固定切空间、完成局部环与内在光滑性

**定理 108.1（原统一系数点的准确局部商）。** 在定理 107.2 的统一开集上，有限商 $\pi:Y\to\Gamma^u$ 泛次数为二。在每个几何 Gale 固定点 $y$，商后切空间的正负特征维数为

$$
\dim(T_yY)^+=6,\qquad \dim(T_yY)^-=3.
\tag{108.1}
$$

若 $p=\pi(y)$，其真实几何完成局部环为

$$
\widehat{\mathcal O}_{\Gamma^u,p}
\simeq k[[x_1,\ldots,x_6,y_1,y_2,y_3]]^{\langle\tau\rangle},
\quad \tau(x_i)=x_i,\quad \tau(y_j)=-y_j.
\tag{108.2}
$$

它的 Krull 维数为九，几何嵌入维数为十二。等价地，令 $Z=(z_{ij})_{1\le i,j\le3}$ 为对称矩阵，则

$$
\widehat{\mathcal O}_{\Gamma^u,p}
\simeq
\frac{k[[x_1,\ldots,x_6,z_{11},z_{12},z_{13},z_{22},z_{23},z_{33}]]}
{I_2(Z)},\qquad z_{ij}\longmapsto y_iy_j,
\tag{108.3}
$$

其中 $I_2(Z)$ 为全部二阶子式的理想。固定点的概形商纤维长度为四，故有限商在此不平坦。统一开集上的非 étale 像支撑恰为固定轨迹的像，纯余维三；它不是分歧除子。非固定轨道的像是光滑点。

证明。先在代数闭域 $k$ 上计算。取固定点的统一评价平面 $W$。由 (107.9)，存在满支撑 $(a_i)$，使 $W^\perp=\operatorname{diag}(a_i)W$。在 $k$ 中选 $s_i^2=a_i$，令 $W_0=\operatorname{diag}(s_i)W$。因为对角乘法与双线性正交满足反演律，

$$
W_0^\perp
=\operatorname{diag}(s_i^{-1})W^\perp
=\operatorname{diag}(s_i)W=W_0.
\tag{108.4}
$$

这一步只规范化几何代表，不声称 $s_i$ 属于 $F$。

$W_0$ 是八维非退化对称空间中的极大全迷向四平面。可取全迷向补空间 $W_0'$，并由配对识别 $W_0'\simeq W_0^\vee$。具体地，先选与 $W_0$ 一组基对偶的四个向量；在补向量中减去其相互配对矩阵的一半所给的 $W_0$ 分量，就使补空间自身的配对为零。于是邻近四平面可写为 $A:W_0\to W_0^\vee$ 的图。配对公式直接给出其正交补是 $-A^{\mathsf t}$ 的图，所以 Grassmannian 上 Gale 微分是

$$
A\longmapsto-A^{\mathsf t}.
\tag{108.5}
$$

十六维切空间中，正特征部分为 $\bigwedge^2W_0^\vee$，维数六；负特征部分为 $\operatorname{Sym}^2W_0^\vee$，维数十。

但这还不是所需前商的切空间。对角环面满足 $(tW)^\perp=t^{-1}W^\perp$，所以在固定代表 $W_0$ 的环面轨道切空间上，(108.5) 的作用为负一。定理 107.2 的主丛给出等变正合列

$$
0\longrightarrow\operatorname{Lie}(T)
\longrightarrow T_{W_0}U
\longrightarrow T_yY\longrightarrow0.
\tag{108.6}
$$

左端维数七且全为负特征。特征零时正负分解正合，故商后正特征维数仍为六，负特征维数为 $10-7=3$，证明 (108.1)。不能将 Grassmannian 的十个负方向全部保留，也不能只留下一个反射方向。

$Y$ 光滑九维。在 $\mathfrak m_y/\mathfrak m_y^2$ 中选六个正、三个负的特征基，任意提升到局部环，再分别用

$$
f\longmapsto\frac{f+\tau f}{2},\qquad
f\longmapsto\frac{f-\tau f}{2}
\tag{108.7}
$$

平均，得到仍给余切基的特征参数。它们是正则参数，诱导等变同构 $\widehat{\mathcal O}_{Y,y}\simeq k[[x_1,\ldots,x_6,y_1,y_2,y_3]]$。形式幂级数同构可由这组参数的伴随分次同构逐阶得到。

有限群取不变量的 Reynolds 投影 (108.7) 使不变量与完成交换；有限模的完成也与有限商所需的局部化相容。因此商点的完成局部环是轨道上各源点完成环之积的不变量。固定轨道只有 $y$ 一个点，得到 (108.2)。非固定轨道有两个点，$\tau$ 交换两个完成因子，其不变量同构于任一源点的光滑完成环。相应自由群商有限 étale，故非固定轨道的像光滑。这一论证没有要求二点覆盖在 Zariski 邻域中分裂。

在 (108.2) 中，不变级数的每个单项式含偶数个 $y$ 因子，因此由 $x_i$ 和六个 $y_iy_j$ 拓扑生成。任意偶数个 $y$ 因子可配成二元组。先给相同因子的各次出现加临时标签，两种配对的并是若干交替偶环；逐次交换两对即可沿这些环将一种配对变成另一种。去掉临时标签后，每次交换对应 $z_{ab}z_{cd}-z_{ac}z_{bd}$，正是对称矩阵的二阶子式或零关系。具有不同 $y$ 指数的单项式线性独立，故多项式核完全由这些交换关系生成。再作完成，得到 (108.3)。其极大理想模平方中，六个 $x_i$ 和六个 $y_iy_j$ 彼此独立，嵌入维数为十二。有限不变量扩张保持 Krull 维数九，所以这里确为奇点。

固定子概形在这些正则参数中由 $y_1=y_2=y_3=0$ 给出，局部光滑六维。有限商保持闭子簇维数，所以固定轨迹的像也六维；每个分支都在九维统一商中有余维三。自由轨迹上商 étale，固定轨迹上下面的纤维计算排除 étale，故该像正是非 étale 像支撑。

把商点极大理想拉回源完成环，得到固定点概形纤维的代数

$$
k[[x_1,\ldots,x_6,y_1,y_2,y_3]]/
(x_1,\ldots,x_6,\ y_iy_j:1\le i,j\le3)
\simeq k\oplus ky_1\oplus ky_2\oplus ky_3,
\tag{108.8}
$$

其中后三项的所有乘积为零。故该纤维长度为四。

为同时确认固定轨迹非空及泛次数，取原域的任一本原元 $\theta$，令

$$
C_0=\operatorname{span}_F(1,\theta,\theta^2,\theta^3).
\tag{108.9}
$$

四行子式为 Vandermonde 行列式，故它统一；而 $C_0^2=\operatorname{span}_F(1,\theta,\ldots,\theta^6)$ 恰为七维，故给固定点。在此 (108.1) 有三个负方向，$\tau$ 因而不是恒等。$Y$ 几何整，忠实二阶函数域作用的固定域指数为二，故 $\pi$ 泛次数二。若它在固定点平坦，则有限平坦模的秩在该点附近等于泛秩二，所有几何纤维长度也应为二，与 (108.8) 矛盾。于是这里是有限但非平坦的二阶群商，分歧支撑余维三，不能称为有限平坦双覆盖或分歧除子。$\square$

**定理 108.2（原域完成环与乘法光滑充要条件）。** 设 $C\subset D$ 为实际统一四平面，$p_C=[P_C]\in\Gamma_D(F)$。则

$$
p_C\in(\Gamma_D)_{\mathrm{sm}}(F)
\quad\Longleftrightarrow\quad C^2=D.
\tag{108.10}
$$

若 $C^2\ne D$，存在唯一的 $F$ 线 $Fa\subset D$，$a\ne0$，使 $aC=C^{\perp\operatorname{Tr}}$，并且原域完成局部环本身满足

$$
\widehat{\mathcal O}_{\Gamma_D,p_C}
\simeq F[[x_1,\ldots,x_6,y_1,y_2,y_3]]^{\langle\tau_D\rangle},
\qquad \tau_D(x_i)=x_i,\quad\tau_D(y_j)=-y_j.
\tag{108.11}
$$

这里不是仅在代数闭包中成立的未下降局部模型。

证明。定理 107.2 的饱和性保证 $p_C$ 的整个几何商纤维都在 $Y$ 中，所以定理 108.1 计算的是原 $\Gamma_D$ 的局部环。由定理 107.3，$C^2=D$ 恰对应非固定轨道，此时系数点光滑；$C^2\ne D$ 恰对应固定轨道，此时嵌入维数十二而维数九，故奇异。光滑性可在 $k/F$ 上检验，得到 (108.10)。

还需分别证明 (108.11)，不能将几何计算所取的平方根当成原域参数。实际 $C$ 在 $F$-态射 $U_D\to Y_D$ 下给 $y_C\in Y_D(F)$。固定时 $\tau_D$ 在这个 $F$-有理点的局部环上作用；$Y_D$ 在该点为九维光滑 $F$-簇。其余切空间上的 $\pm1$ 特征空间定义在 $F$ 上，扩域后的维数由 (108.1) 分别为六和三。就在 $F$ 上选这两组基，并用 (108.7) 的 $F$-线性平均选择提升，得到 $F$ 上的等变正则参数。完成后的形式参数同构及有限商取不变量均在 $F$ 上成立，给出 (108.11)。唯一 $Fa$ 已由原迹配对构造，并不依赖这些形式参数。$\square$

## 109. 指定平移幂族上的逐目标光滑性

**定理 109.1（平移幂目标的确切可用参数）。** 固定同一个 $D/F$ 的任一本原元 $\theta$。令 $\alpha_i=\sigma_i(\theta)$，对 $t\in F$ 置

$$
\eta=\theta+t,\qquad
C_t=\operatorname{span}_F(1,\eta,\eta^2,\eta^4),\qquad
E_\theta(T)=\prod_{\substack{I\subset\{1,\ldots,8\}\\|I|=4}}
\left(4T+\sum_{i\in I}\alpha_i\right)\in F[T].
\tag{109.1}
$$

每个 $C_t$ 都是实际四平面，且有准确等价

$$
\begin{aligned}
C_t\text{ 统一}
&\quad\Longleftrightarrow\quad E_\theta(t)\ne0,\\
C_t^2=D
&\quad\Longleftrightarrow\quad\operatorname{Tr}_{D/F}(\theta)+8t\ne0.
\end{aligned}
\tag{109.2}
$$

因此对每个 $E_\theta(t)\ne0$ 的指定参数，

$$
[P_{C_t}]\in(\Gamma_D)_{\mathrm{sm}}(F)
\quad\Longleftrightarrow\quad\operatorname{Tr}_{D/F}(\theta)+8t\ne0.
\tag{109.3}
$$

特别地，非零多项式 $E_\theta(T)(\operatorname{Tr}(\theta)+8T)$ 的原域根以外，每个 $C_t$ 都统一、平方张满且系数点光滑。

证明。(109.2) 的子式和乘法计算是 source033 命题 85.6 在 $m=4$ 的既有内容。为将它准确用于每个指定目标，写出参数对应及其理由。$\eta$ 仍为本原元，次数小于八的幂线性独立，故 $1,\eta,\eta^2,\eta^4$ 独立。对四个变量有

$$
\det\begin{pmatrix}
1&z_1&z_1^2&z_1^4\\
1&z_2&z_2^2&z_2^4\\
1&z_3&z_3^2&z_3^4\\
1&z_4&z_4^2&z_4^4
\end{pmatrix}
=\prod_{a<b}(z_b-z_a)\,(z_1+z_2+z_3+z_4).
\tag{109.4}
$$

左端交错，除去六次 Vandermonde 后是一次对称多项式；比较单项式 $z_2z_3^2z_4^4$ 的系数得比例常数为一。对任意四元集代入 $z_i=\alpha_i+t$，可分性保证差积不为零，因此相应四行子式非零，恰当且仅当 $4t+\sum_{i\in I}\alpha_i\ne0$。Galois 作用置换 (109.1) 的全部因子，故 $E_\theta\in F[T]$；每个因子的首项系数为四，整个多项式非零。这证明统一性的精确条件。

原乘法给出的乘积空间为

$$
C_t^2=\operatorname{span}_F
(1,\eta,\eta^2,\eta^3,\eta^4,\eta^5,\eta^6,\eta^8).
\tag{109.5}
$$

$\eta$ 的最小多项式有形式

$$
f_\eta(X)=X^8-\operatorname{Tr}_{D/F}(\eta)X^7+
\text{次数至多六的项}.
\tag{109.6}
$$

模掉 $\operatorname{span}_F(1,\eta,\ldots,\eta^6)$ 后，$\eta^8$ 等于 $\operatorname{Tr}(\eta)\eta^7$。$1,\eta,\ldots,\eta^7$ 是 $D$ 的基，故 (109.5) 张满 $D$，恰当且仅当 $\operatorname{Tr}(\eta)\ne0$；迹为零时它恰为七维。又 $\operatorname{Tr}(\eta)=\operatorname{Tr}(\theta)+8t$，得到第二个等价。

在统一参数上应用定理 108.2，立即得到 (109.3)。有限异常集之外的参数存在，因为 $F$ 无限。新增结论是这些**指定** $C_t$ 的系数光滑性及其充要条件；子式和族平方秩计算仍归于 source033 命题 85.6。source033 定理 85.7 在整个 Grassmannian 中给一般目标的非空开集，不能代替一条指定曲线的论证；本证明逐个参数应用原乘法及完成局部环，正好补足该卷开放边界 85.8 所指出的八次光滑桥。$\square$

## 110. 数域上的九个实际正标签与完整次数五十五剩余域

**定理 110.1（每个合格原域目标的九标签算术证书）。** 额外设 $F$ 为数域；$D/F$ 仍为定义 106.1 的同一个八次域扩张。对每个实际统一四平面 $C\subset D$，假设 $C^2=D$，并固定其原基 $b_1,b_2,b_3,b_4$。则存在非空 $F$-开集

$$
B_C\subset\mathbb A_F^{36}
\tag{110.1}
$$

及 Zariski 稠密的集合 $\mathcal H_C\subset B_C(F)$，使每个批次 $b\in\mathcal H_C$ 都由九个目标内部二平面的规范帧给出九个非标量实际正标签

$$
\begin{aligned}
u_j&=b_1+z_{31}^{(j)}b_3+z_{41}^{(j)}b_4,\\
v_j&=b_2+z_{32}^{(j)}b_3+z_{42}^{(j)}b_4,\\
r_j&=u_j/v_j\in D^\times\setminus F,
\qquad C\cap r_jC\ne0,\qquad 1\le j\le9.
\end{aligned}
\tag{110.2}
$$

令 $H_r=\{[Q]\in\mathbb P(H_D):Q(r)=0\}$。其**完整概形截交**满足

$$
Z_b=\Gamma_D\cap H_{r_1}\cap\cdots\cap H_{r_9}
\simeq\operatorname{Spec}F\ \amalg\ \operatorname{Spec}L_b,
\qquad [L_b:F]=55,
\tag{110.3}
$$

其中第一因子为 $[P_C]$，$L_b/F$ 为可分域扩张。目标外五十五个几何系数点互异，构成一个 Galois 轨道，且剩余因子没有 $F$ 点。因此

$$
\{[Q]\in\Gamma_D(F):Q(r_j)=0\ (1\le j\le9)\}
=\{[P_C]\}.
\tag{110.4}
$$

特别地，任何实际四平面 $W\subset D$ 若通过这九个正标签，则 $[P_W]=[P_C]$、$S_W=S_C$。定理 109.1 每个未被排除的指定目标 $C_t$ 均适用。

证明。这里直接应用 source033 定理 85.2，不重新证明该卷的受限截交及剩余覆盖定理。逐一实例化其全部前提：底域 $F$ 是数域；$D/F$ 是固定实际可分域扩张；$2m=8$、$m=4\ge4$；目标是同一个实际 $C$；统一条件正是假设 81.2 的统一行条件；定理 108.2 由 $C^2=D$ 给出其原系数点光滑。定理 106.3 在同一个系数嵌入中给出

$$
d=\dim\Gamma_D=9,\qquad \delta=\deg\Gamma_D=56.
\tag{110.5}
$$

目标内部标签参数空间是原 $G=\operatorname{Gr}_F(2,C)$，所以

$$
g=\dim G=2m-4=4,\qquad dg=36.
\tag{110.6}
$$

因此 source033 定理 85.2 的固定 Grassmann 大胞腔九重乘积就是 (110.1) 的仿射空间，规范帧就是 (110.2)。这是同一个目标的受限测试系统，不以任意一般超平面替换。两个规范向量因 $b_1,b_2$ 系数而独立，故均非零；$D$ 的域性使分母可逆。若 $r_j\in F$，则 $u_j=r_jv_j$，与独立矛盾。又 $u_j=r_jv_j\in C$，所以这些标签确为非标量实际正标签。该定理所取开集还使这些比值在原参数坐标中正则，所有范数非零条件保持。

source033 定理 84.6、85.2 在这个非空批次开集上给目标截面与整个剩余有限 étale 覆盖的分解，后者的总空间几何整，常次数 $\delta-1$。该卷用 Drinfeld，*On a conjecture of Deligne*，arXiv:1007.4004v7，Appendix A.1，Theorem A.1 的全局域 Hilbert 不可约性，把整个剩余纤维特化成一个域的谱。此处底域为数域，底是仿射空间开集，覆盖不可约且有限 étale，故所有这些算术前提仍满足。对每个更小的非空 $F$-开集应用同一输入，保持域谱的批次 Zariski 稠密。代入 $\delta=56$，便得 (110.3) 的完整概形分解及 $[L_b:F]=55$。这里目标局部长度为一，余部为一个域谱；不是仅有一个次数为五十六的交循环。

特征零使 $L_b/F$ 可分，故在 $k$ 上余部是五十五个互异点。一个域的全部嵌入构成一个 Galois 轨道，得到所述共轭性。若余部有 $F$ 点，就有 $F$-代数同态 $L_b\to F$；域同态单射，但五十五维 $F$ 向量空间不能单射进一维空间。因此余部没有 $F$ 点，得到 (110.4)。

对每个实际竞争窗口，source033 式 (81.4) 保证 $P_W\ne0$，所以它确实给出 $\Gamma_D(F)$ 中的点。由 (106.2)，九个正标签都意味着 $P_W(r_j)=0$；(110.4) 遂给 $[P_W]=[P_C]$，再由同一等价得到完整支持 $S_W=S_C$。$\square$

**命题 110.2（系数隔离的恢复边界）。** 定理 110.1 隔离的是原系数线及其正支持，不唯一恢复窗口。其结论不给九标签最小性、有效取得算法、标签高度或搜索预算，也不把五十五解释为整个 Grassmannian 系数纤维中的窗口数。

证明。对任意 $\gamma\in D^\times$，采用乘法后的帧，交换性给

$$
P_{\gamma C}(x)=N_{D/F}(\gamma)P_C(x).
\tag{110.7}
$$

因此系数线在乘法缩放轨道上不变；几何统一轨迹的七维有效环面轨道已经由定理 107.2 给出。原域中也确实存在 $\gamma C\ne C$：若每个非零 $\gamma$ 都保持 $C$，取 $0\ne c\in C$ 就有 $Dc\subset C$，强迫 $C=D$，与四维性矛盾。故系数隔离不蕴含窗口唯一。

九来自本定理的 $d=9$ 个受限测试构造，证明没有排除更短证书。批次存在性使用非空开集及 Hilbert 不可约性，没有给未知目标的标签发现过程或相应有效界。次数五十五属于 (110.3) 的剩余**系数截交**；该有限截交与原系数映射的正维窗口纤维是不同对象。$\square$

**定理 110.3（完整白话表述）。** 在任意特征零域上，固定同一个八次可分域扩张，把每个四维窗口送到它的原乘法行列式系数线，得到的系数簇恰为沿原嵌入标签扭曲的有序八点 Gale 商；在原十四维系数空间的射影化中，它的维数是九、次数是五十六。若窗口满足任意四个嵌入评价行都独立，那么系数点光滑，当且仅当窗口元素两两相乘的线性张成是整个八维域。若只张成七维，就存在唯一的原域比例类，使乘上它的代表元把窗口变成迹正交补；此时出现六个固定方向和三个同时变号的方向，系数点的嵌入维数为十二，是真奇点。有限 Gale 商在此的纤维长度为四，分歧像余维三，而原窗口到系数的映射还含七维环面方向。对任一本原元，窗口 $\operatorname{span}(1,\theta+t,(\theta+t)^2,(\theta+t)^4)$ 在每个四根和加 $4t$ 都非零且 $\operatorname{Tr}(\theta)+8t\ne0$ 的原域参数上，都给一个这样的光滑目标；被排除的参数只有有限个。若底域进一步是数域，那么对每个实际统一且平方张满的目标，都存在九个来自该目标自身的非标量正标签，使完整系数截交恰为目标这个原域点和一个五十五次剩余域的谱。余下五十五个几何系数点仍然存在并彼此共轭，只是没有额外原域点；因而九标签唯一确定系数线和完整正支持，而不唯一确定窗口本身。

证明。第一句由定理 106.3；统一条件、七维方向及饱和性由定理 107.2；原乘法与迹正交的等价由定理 107.3；局部环、光滑性、纤维长度与余维由定理 108.1–108.2；指定平移参数由定理 109.1；数域上的完整截交与恢复边界由定理 110.1 及命题 110.2。每一步均保持同一个原域、同一个原系数嵌入及其明列条件。$\square$

**约定 110.4（数学来源及适用范围）。** 以下固定来源承担所列中间输入；经典结果为 `literature-attested`，将它们接到原乘法、原域下降、指定目标局部环及算术参数的推导为 `repo-derived`。这区分经典先例与本卷的应用、综合推导，不作全球原创性断言。

| 来源 | 精确使用范围 |
| --- | --- |
| [source033，固定版本](https://github.com/the-omega-institute/trureturing/blob/974984733cb1d619221ff97000612a9194bc8828/docs/develop/theory/AURIC_R5_033_ALL_DEGREE_ARITHMETIC_POSITIVE_CERTIFICATES.md)，定义 81.1、假设 81.2、定理 85.2、命题 85.6、定理 85.7、开放边界 85.8 | 原 $H_D$、实际多项式非零与张成、实际系数闭包；85.2 的全部数域及固定目标前提下的受限批次、完整域谱剩余；85.6 的平移幂子式和乘法计算。85.7 只给整个源中的非空开集，不代替本卷指定曲线论证；85.8 的八次光滑缺口由 (108.10)、(109.3) 补足。source026、source029 仅通过该卷的既有系数输入复用。 |
| B. Howard、J. Millson、A. Snowden、R. Vakil，[arXiv:1103.5255v1](https://arxiv.org/abs/1103.5255v1)，*The geometry of eight points in projective space: Representation theory, Lie theory, dualities*，[DOI:10.1112/plms/pds016](https://doi.org/10.1112/plms/pds016)，§1.2、§1.4、§8 Propositions 8.1–8.2 | $R_1$ 的十四维括号表示、完整环等式 $k[R_1]=R^\tau$ 及 (106.17) 的 Hilbert 级数。后两项是文献的计算辅助输入，本卷不声称独立纸面重证；原系数环识别和下降另见定理 106.3 的证明。 |
| B. Howard、J. Millson，[math/0409260v2](https://arxiv.org/abs/math/0409260v2)，*The Chevalley Involution and a Duality of Weight Varieties*，Theorems 1.4、1.6、1.12、Lemma 4.13、Corollary 4.14 | 外代数对偶、补集子式符号、权重商的 Gale 构造。任意特征零域版本由本卷显式 $\mathbb Q$ 公式及忠实平坦下降给出，不直接从复数设定外推。 |
| D. Eisenbud、S. Popescu，[math/9807127v1](https://arxiv.org/abs/math/9807127v1)，*The Projective Geometry of the Gale Transform*，Theorem 7.1、Corollary 7.4 | 自关联、乘积湮灭泛函与稳定点集二次条件失败的经典先例；后一个自关联判据归于 Coble、Dolgachev–Ortland。本卷在原 $\mu_C^\vee$ 上证明满支撑和唯一性，再由原迹配对产生 $a\in D^\times$。 |
| V. Drinfeld，[arXiv:1007.4004v7](https://arxiv.org/abs/1007.4004v7)，*On a conjecture of Deligne*，Appendix A.1，Theorem A.1 | 仅通过 source033 定理 85.2 使用：全局域上仿射空间开集的不可约有限 étale 覆盖可在原域点保持整个纤维为一个域谱。数域前提在定理 110.1 中保留。 |

几何判据限于统一轨迹，不给非统一边界的奇点分类；没有任意商有理点提升到实际窗口的断言。有限商的固定纤维长度、有限系数截交的剩余域次数及原窗口纤维的维数分别属于三个不同对象。数学结论按以上纸面证明及明确归属的文献前提理解。

## 追加锚（本行以下为增补区）

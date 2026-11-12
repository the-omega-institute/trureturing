# 原首一评价族的精确检测秩与实际余切增益

## 143. 原连续幂族、实际像纤维与所用输入

**定义 143.1（原域和原带符号系数像）。** 设 $F$ 为特征零域，$D/F$ 为次数 $2m$ 的可分域扩张，$m\ge7$。任取本原元 $\theta$，固定非零体积形式 $\nu:\det_FD\to F$，置

$$
C=\langle1,\theta,\ldots,\theta^{m-1}\rangle_F,
\qquad d=m-4,\qquad N=m-1=d+3,
\qquad a=\frac{m(m-1)}2.
\tag{143.1}
$$

对实际窗口 $C'\subset D$ 及其包含帧 $E_{C'}$，使用同一个域的乘法 $M_x$ 定义

$$
P_{C'}(x)=\nu\bigl(\det[E_{C'},M_xE_{C'}]\bigr).
\tag{143.2}
$$

在有限 Galois 分裂域 $L/F$ 中保留全部原嵌入标签，根集记为 $\Lambda$。原系数写作

$$
P_{C'}(x)=\sum_{|I|=m}c_I(C')\prod_{\lambda\in I}x_\lambda,
\qquad c_I=\alpha\epsilon_Ip_Ip_{I^c},
\tag{143.3}
$$

其中符号、体积因子及互补行序均采用 [039，§111](AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) 的约定。令 $S_F$ 为该原带标签系数映射在全部 $p_I\ne0$ 的统一开集上的像环；具体地，分裂后它是 $(c_I/c_{I_0})^{\pm1}$ 生成的实际像代数。令 $B_F$ 为 039 给出的有限正规化环，$p=[P_C]$，$y$ 为其上方的正规化点，置

$$
S=(S_F)_p,\quad B=(B_F)_y,\quad
\mathscr T=\widehat S,\quad\mathscr B=\widehat B,
\qquad
J:\mathfrak m_S/\mathfrak m_S^2
\longrightarrow\mathfrak m_B/\mathfrak m_B^2.
\tag{143.4}
$$

两个剩余域均为 $F$。所有源余切核均指此处的 $\ker J$。

**定义 143.2（负余切和实际正枢轴）。** 取

$$
V=F[T]_{\le m-2},\qquad e_i=T^i\quad(0\le i\le d+2),
\qquad W=\bigwedge^2V,
$$

$$
w:\operatorname{Sym}^2W\longrightarrow\bigwedge^4V,
\qquad w(\xi\zeta)=\xi\wedge\zeta,
\qquad K=\ker w,
\qquad P_4=\operatorname{span}_F\{kk':k,k'\in K\}.
\tag{143.5}
$$

对称代数的乘积与外积分别写作 $\xi\zeta$ 和 $\xi\wedge\zeta$。采用 [042，(133.8)--(133.9)](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) 的原连续幂负余切识别；在实际横截面的光滑覆盖上，正变量为 $U$，负变量为 $Y$，有 $\mathscr B=F[[U,Y]]^{\iota}$，$\iota(U,Y)=(U,-Y)$。负线性函数空间为 $W$。

合法实际原 $F$ 正枢轴是 $s_1,\ldots,s_a\in\mathfrak m_S$，其耦合余切类 $J[s_i]=(\ell_i,q_i)$ 的正投影 $\ell_i$ 构成正余切的一组基。“正”表示对合的正特征方向，不要求域有序。对任意一组这样的枢轴，定义

$$
B_{0,s}=\mathscr B/(s_1,\ldots,s_a)\mathscr B,
\quad\mathfrak L_s=\ker(\mathscr T\to B_{0,s}),
\quad A_{0,s}=\operatorname{im}(\mathscr T\to B_{0,s})
=\mathscr T/\mathfrak L_s.
\tag{143.6}
$$

这里使用实际像。只有 $(s)\mathscr T\subseteq\mathfrak L_s$ 自动成立，不作两者相等的假设。在 $B_{0,s}\simeq F[[Y]]^{Y\mapsto-Y}$ 的覆盖中记 $\mathfrak q=(Y)$，置

$$
J_4(A_{0,s})=
\operatorname{im}\left(A_{0,s}\cap\mathfrak q^4
\longrightarrow\mathfrak q^4/\mathfrak q^6\right)
\subseteq\operatorname{Sym}^4W.
\tag{143.7}
$$

由于函数为偶函数，右侧符号只有四次部分。$\operatorname{in}_2(A_{0,s})$ 表示零常数像元素的全部二次符号。$A_{0,s}$ 的极大理想记为 $\mathfrak n_s$，其嵌入维数为 $\dim_F\mathfrak n_s/\mathfrak n_s^2$。

**约定 143.3（复用的原族纸面输入）。** [039，§§111、113、115--117](AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md)、[040，定理 122.1、命题 122.2](AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md) 及上述固定版本 [042，§§134--139](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) 提供以下普通数学前提：

$$
\operatorname{rank}J=a+\dim_FK,
\qquad \operatorname{in}_2(A_{0,s})=K,
\qquad P_4\subseteq J_4(A_{0,s}),
\tag{143.8}
$$

以及良定义的原 $F$ 线性满射

$$
\overline\lambda_s:\ker J\longrightarrow J_4(A_{0,s})/P_4,
\qquad[g]\longmapsto
[\operatorname{in}_4(g|_{B_{0,s}})].
\tag{143.9}
$$

对每个首一 $d$ 次多项式 $h\in F[T]$，实际原评价函数是

$$
\mathcal E_h(C')=
\frac{P_{C'}(h(\theta))}{P_{C'}(\theta^m)}\in S.
\tag{143.10}
$$

其分母在 $C$ 处为非零幂基体积 $\nu(1\wedge\theta\wedge\cdots\wedge\theta^{2m-1})$，故是原局部环中的单位。分子分母均为原系数上的 $F$ 线性评价泛函，分裂表达式严格为

$$
\mathcal E_h=
\frac{\sum_{|I|=m}c_I(C')\prod_{\lambda\in I}h(\lambda)}
{\sum_{|I|=m}c_I(C')\prod_{\lambda\in I}\lambda^m}.
\tag{143.11}
$$

该表达式保留原符号和标签；它来自原 $F$ 评价，而非将单个分裂标签函数视为原域函数。帧及体积公共因子在比值中消去，原乘法 $C'\mapsto tC'$ 的公共范数因子也消去，故函数属于同一原系数像并下降到实际乘法商。这些成员身份、单位及下降事实使用 042，定义 135.1。

042，命题 135.2 给出：$\mathcal E_h$ 在完整 Grassmann 图变量中至少四阶消失，对每组合法实际枢轴都有

$$
\operatorname{in}_4(\mathcal E_h|_{B_{0,s}})=p(h)^2.
\tag{143.12}
$$

为固定此式的归一化，令 $H_j=T^jh$，并取以下 $W$ 中的线性函数：

$$
\begin{array}{lll}
\beta_{01}=e_0\wedge H_0,&
\beta_{02}=e_0\wedge H_1+e_1\wedge H_0,&
\beta_{03}=e_0\wedge H_2+e_1\wedge H_1+e_2\wedge H_0,\\
\beta_{12}=e_1\wedge H_1,&
\beta_{13}=e_1\wedge H_2+e_2\wedge H_1,&
\beta_{23}=e_2\wedge H_2,
\end{array}
$$

$$
p(h)=\beta_{01}\beta_{23}-\beta_{02}\beta_{13}
+\beta_{03}\beta_{12}\in\operatorname{Sym}^2W.
\tag{143.13}
$$

这里 $p(h)$ 不预设属于 $K$。这些都是 042 的原评价首项输入，不在此重建原乘法块或完整图四阶消失的证明。

**定义 143.4（检测器与首一参数族）。** 令 $\mathcal H=\bigwedge^6V\otimes W$。采用 042，定义 137.1 的线性映射 $\Psi:\operatorname{Sym}^4W\to\mathcal H$，其在 $\xi_1\xi_2\xi_3\xi_4$ 上的值为

$$
\Psi(\xi_1\xi_2\xi_3\xi_4)
=\sum_{i=1}^4
\left(\bigwedge_{j\ne i}\xi_j\right)\otimes\xi_i,
\qquad \xi_i\in W.
\tag{143.14}
$$

三个二向量的外积与其顺序无关。对 $h=\sum_{r=1}^da_rT^r$ 定义

$$
H_j=\sum_{r=1}^da_re_{r+j}\quad(j=0,1,2),
\qquad
\Omega(h)=e_0\wedge e_1\wedge e_2\wedge H_0\wedge H_1\wedge H_2,
$$

$$
\eta(h)=2e_1\wedge H_1-e_0\wedge H_2-e_2\wedge H_0,
\qquad Q(h)=2\Omega(h)\otimes\eta(h).
\tag{143.15}
$$

由 042，(137.3)、命题 137.2，复用精确恒等式

$$
\Psi(P_4)=0,\qquad\Psi(p(h)^2)=Q(h).
\tag{143.16}
$$

因此 $\Psi$ 在 $J_4(A_{0,s})/P_4$ 上诱导映射 $\overline\Psi_s$。首一族记为

$$
\mathcal M_d(F)=
\left\{T^d+\sum_{r=0}^{d-1}b_rT^r:b_r\in F\right\}.
\tag{143.17}
$$

以上输入均为纸面数学前提，本卷不宣称它们或下文证明经过 Lean kernel 验证。041，定义 124.1 的原族范围为 $m=5,6$，不承担这里的全 $m\ge7$ 实际纤维桥接。

## 144. 整个实际首一族的主定理

**定义 144.1（系数空间、实际值空间及评价类空间）。** 将 $Q(\sum_{r=1}^da_rT^r)$ 展开成参数 $a_1,\ldots,a_d$ 的四次齐次向量多项式，所有向量系数在 $\mathcal H$ 中的张成记为 $\mathcal C_d$。将 $a_d=1$ 后的向量多项式的全部系数张成记为 $\mathcal C_d^{\mathrm{mon}}$。对每组实际枢轴，置

$$
\mathcal D_{d,s}=
\operatorname{span}_F\left\{
\Psi\bigl(\operatorname{in}_4(\mathcal E_h|_{B_{0,s}})\bigr):
h\in\mathcal M_d(F)\right\},
$$

$$
\mathcal L_{d,s}=
\operatorname{span}_F\left\{
[\operatorname{in}_4(\mathcal E_h|_{B_{0,s}})]:
h\in\mathcal M_d(F)\right\}
\subseteq J_4(A_{0,s})/P_4.
\tag{144.1}
$$

这里的秩均为整族线性张成空间的维数，不是某个参数点的张量秩或参数微分秩。

**定理 144.2（精确检测秩和实际原族余切下界）。** 对定义 143.1 中的每个 $F,D,\theta,m$，以及每组合法实际原 $F$ 正枢轴 $s$，都有同一负余切识别中的精确等式

$$
\mathcal C_d=\mathcal C_d^{\mathrm{mon}}
=\operatorname{span}_F\{Q(h):h\in\mathcal M_d(F)\}
=\mathcal D_{d,s},
$$

$$
\boxed{\dim_F\mathcal D_{d,s}
=r_d=d\binom d3-3\binom d4
=\frac{d(d-1)(d-2)(d+9)}{24}.}
\tag{144.2}
$$

特别地，存在 $r_d$ 个实际首一 $d$ 次原域评价函数，其检测值线性独立，它们在原源余切核及实际像纤维余切中的类也分别线性独立。令

$$
k_N=\dim_FK=\frac{N^2(N^2-1)}{12}.
\tag{144.3}
$$

则实际原族满足

$$
\begin{aligned}
\dim_F\mathcal L_{d,s}&\ge r_d,\\
\dim_F\bigl(J_4(A_{0,s})/P_4\bigr)&\ge r_d,\\
\dim_F\ker J&\ge r_d,\\
\operatorname{edim}A_{0,s}&\ge k_N+r_d,\\
\operatorname{edim}S&\ge a+k_N+r_d.
\end{aligned}
\tag{144.4}
$$

证明。第 145 节在实际移位矩阵上证明适用的 grade 条件并计算四次理想维数；第 146 节把它识别为向量系数秩，再证明首一原 $F$ 值已张成全部检测空间；第 147 节将这些实际评价值传入两个各自不同的局部环余切空间，得到 (144.4)。这三步共同证明定理。精确性只属于 (144.2) 的受限检测空间，(144.4) 中均为下界。

## 145. 实际移位最大子式理想及四次正合列

**定义 145.1（专门矩阵与其理想）。** 在标准分次多项式环 $R=F[a_1,\ldots,a_d]$ 中令每个 $a_r$ 的次数为一，越界指标的 $a_r$ 一律为零。定义恰有 $d$ 行、三列的矩阵

$$
M_{s,j}=a_{s-j},\qquad 3\le s\le d+2,\quad 0\le j\le2,
\qquad I=I_3(M)\subset R.
\tag{145.1}
$$

若 $I_0\subset\{3,\ldots,d+2\}$ 有三个元素，按递增行序取最大子式 $\Delta_{I_0}$。这张矩阵是 $H_0,H_1,H_2$ 模 $\langle e_0,e_1,e_2\rangle$ 的实际坐标矩阵，条目之间的重复和边界零均保留。

**引理 145.2（实际专门化的精确 grade）。** 对每个 $d\ge3$，有

$$
\sqrt I=(a_3,\ldots,a_d),
\qquad \operatorname{ht}I=\operatorname{grade}I=d-2.
\tag{145.2}
$$

证明。记 $\mathfrak p_0=(a_3,\ldots,a_d)$。模掉 $\mathfrak p_0$ 后，$M$ 只有行指标 $3,4$ 的行可能非零，所以全部三阶子式为零，$I\subseteq\mathfrak p_0$。

反过来，设 $\mathfrak p$ 为任意包含 $I$ 的素理想。对 $3\le t\le d$，取行 $t,t+1,t+2$ 的子式。模掉 $(a_{t+1},\ldots,a_d)$，该三行矩阵准确变成

$$
\begin{pmatrix}
a_t&a_{t-1}&a_{t-2}\\
0&a_t&a_{t-1}\\
0&0&a_t
\end{pmatrix},
\tag{145.3}
$$

故此子式模该理想等于 $a_t^3$。从 $t=d$ 向下归纳：$a_d^3\in\mathfrak p$ 给 $a_d\in\mathfrak p$；已知所有更高指标系数在 $\mathfrak p$ 中时，(145.3) 给 $a_t^3\in\mathfrak p$，从而 $a_t\in\mathfrak p$。因此每个这样的素理想都包含 $\mathfrak p_0$，证明根基等式。

$R$ 是域上的多项式环，故为 Noetherian 正则 Cohen--Macaulay 环。根基等式给高度 $d-2$；在此环中理想的 grade 等于包含它的素理想处深度的下确界，而这些深度等于相应高度，故 grade 也为 $d-2$。此论证直接在给定矩阵上成立，不需假设其条目独立，也不从泛矩阵专门化的平坦性推断正合性。证毕。

**命题 145.3（四次理想的精确维数）。** 对 (145.1) 的实际理想，

$$
\dim_F I_4=d\binom d3-3\binom d4.
\tag{145.4}
$$

证明。对实际转置矩阵应用自由模同态

$$
\varphi=M^{\mathsf T}:R^d\longrightarrow R^3.
\tag{145.5}
$$

它的最大子式理想仍为 $I$。自由模秩分别为 $d$ 和 $3$，所需的预期 grade 为 $d-3+1=d-2$，已由引理 145.2 建立。环为 Noetherian，且 $I$ 为真理想。因而 Buchsbaum--Eisenbud，*Generic Free Resolutions and a Family of Generically Perfect Ideals*，Theorem 3.1（印刷页 269）及 Corollary 3.2（页 269--270，$p=1,q=3$）给出这张实际矩阵的 Eagon--Northcott 自由分解。

把该分解的最后一个像写成 $I$。其第 $j$ 个自由模为

$$
\mathcal F_j=
R(-j-3)^{\binom{j+2}{2}\binom d{j+3}},
\qquad 0\le j\le d-3.
\tag{145.6}
$$

这里 $R(-u)_v=R_{v-u}$；秩来自 $\bigwedge^{j+3}F^d$ 和三维空间的 $j$ 次对称幂的维数，固定的一维行列式因子不改变秩。特征零下，对称幂与原文的对偶除幂写法有相同的这些维数。最大子式为三次，随后的微分在矩阵条目中一次，故分次位移依次为 $3,4,5,\ldots$。在 $d\ge5$ 时，分解含有非零的更高项；其末端形如

$$
\cdots\longrightarrow R(-5)^{6\binom d5}
\longrightarrow R(-4)^{3\binom d4}
\longrightarrow R(-3)^{\binom d3}
\longrightarrow I\longrightarrow0.
\tag{145.7}
$$

具体地，对四元行集 $S_0=\{s_1<s_2<s_3<s_4\}$ 和列 $j=0,1,2$，第一层关系是实际条目给出的 Laplace 关系

$$
\sum_{\nu=1}^4(-1)^{\nu-1}
a_{s_\nu-j}\Delta_{S_0\setminus\{s_\nu\}}=0.
$$

它来自向三列添加其中第 $j$ 列后得到的重复列行列式；这些正是 $\mathcal F_1\to\mathcal F_0$ 的关系向量。这里没有把 $R(-4)$ 项左侧的完整模核设为零。只有取四次齐次部分时，所有 $j\ge2$ 的项因位移至少为五而消失。由分次正合性，恰得到有限维向量空间的短正合列

$$
0\longrightarrow F^{3\binom d4}
\longrightarrow R_1^{\binom d3}
\longrightarrow I_4\longrightarrow0.
\tag{145.8}
$$

当 $d=3$ 时左项为零；当 $d=4$ 时没有五次项；其余情形左侧单射来自五次及更高项的四次部分为零。由于 $\dim_FR_1=d$，维数相减即为 (145.4)。证毕。

## 146. 从坐标多项式到全部首一原域检测值

**引理 146.1（检测坐标恰好生成 $I_4$）。** 将 $Q$ 视为 $\mathcal H\otimes_FR_4$ 中的元素，定义坐标多项式映射

$$
\kappa:\mathcal H^\vee\longrightarrow R_4,
\qquad \ell\longmapsto(\ell\otimes1)Q.
\tag{146.1}
$$

则 $\operatorname{im}\kappa=I_4$。

证明。对每个三元行集 $I_0=\{i_1<i_2<i_3\}$，令

$$
v_{I_0}=e_0\wedge e_1\wedge e_2
\wedge e_{i_1}\wedge e_{i_2}\wedge e_{i_3}.
$$

这些是不同的外幂基元。按实际三列展开，

$$
\Omega(h)=\sum_{|I_0|=3}\Delta_{I_0}v_{I_0}.
\tag{146.2}
$$

另一方面，对每个 $1\le r\le d$，$\eta(h)$ 在 $e_0\wedge e_{r+2}$ 上的坐标恰为 $-a_r$。另外两项总含 $e_1$ 或 $e_2$，不能贡献这个坐标，因为 $r+2\ge3$。因此 $Q$ 在 $v_{I_0}\otimes(e_0\wedge e_{r+2})$ 上的坐标恰为

$$
-2a_r\Delta_{I_0}.
\tag{146.3}
$$

它们包含所有 $a_r\Delta_{I_0}$ 的非零常数倍。其余坐标也都是某个 $\Delta_{I_0}$ 乘以参数一次式的线性组合。由于 $I$ 由这些三次最大子式生成，$I_4=R_1\operatorname{span}_F\{\Delta_{I_0}\}$；特征零保证 $2\ne0$，遂得所述相等。证毕。

**引理 146.2（向量系数、首一限制和原域值）。** 设 $E$ 是无限域 $F$ 上的有限维向量空间，$q\in E\otimes_FF[x_1,\ldots,x_d]_t$ 为 $t$ 次齐次向量多项式。则其向量系数张成空间，等于 $q(x_1,\ldots,x_{d-1},1)$ 的向量系数张成空间，也等于

$$
\operatorname{span}_F\{q(b_1,\ldots,b_{d-1},1):b_i\in F\}.
\tag{146.4}
$$

其维数是坐标多项式映射 $E^\vee\to F[x_1,\ldots,x_d]_t$ 的秩。

证明。对任意 $\ell\in E^\vee$，它消去全部向量系数，当且仅当标量多项式 $\ell(q)$ 恒为零。因此系数空间的消去子就是坐标多项式映射的核，其余维数公式由有限维对偶性得到。

齐次标量多项式 $f$ 的限制 $f(x_1,\ldots,x_{d-1},1)$ 唯一确定 $f$：一个剩余变量单项式的次数若为 $u$，它原来的 $x_d$ 指数只能是 $t-u$。所以齐次多项式空间上的这一限制是单射，前后系数空间有相同消去子，故相等。

最后，一个多元标量多项式若在全部 $F^{d-1}$ 上为零，则恒为零。证明可对变量数归纳：固定其他变量，一元多项式在无限域上有无限多个根，故每个系数值为零，再对这些系数多项式使用归纳。应用于 $\ell(q(x_1,\ldots,x_{d-1},1))$，实际值空间与限制后的系数空间也有相同消去子，因而相等。整个论证只在 $F$ 上进行。证毕。

**命题 146.3（首一族的完整检测空间）。** (144.2) 的全部空间相等，且具有所列精确维数。

证明。引理 146.1 与命题 145.3 给出

$$
\dim_F\mathcal C_d=\operatorname{rank}\kappa
=\dim_FI_4=d\binom d3-3\binom d4.
\tag{146.5}
$$

$\Omega$ 为参数三次齐次式，$\eta$ 为一次式，故 $Q$ 为四次齐次式。特征零域无限，引理 146.2 可取 $E=\mathcal H,t=4$，说明仅取 $a_d=1$ 的原域值已张成 $\mathcal C_d$，同时给出 $\mathcal C_d^{\mathrm{mon}}=\mathcal C_d$。

加入常数项 $c$ 时，三个 $H_j$ 分别增加 $ce_j$。$\Omega$ 已含 $e_0,e_1,e_2$，故不变；$\eta$ 的变化为

$$
2c\,e_1\wedge e_1-c\,e_0\wedge e_2-c\,e_2\wedge e_0=0.
\tag{146.6}
$$

所以 $Q$ 与常数项无关，(146.4) 确实涵盖整个 $\mathcal M_d(F)$。原函数本身也满足 $\mathcal E_{h+c}=\mathcal E_h$：在 (143.2) 中，第二块帧增加 $cE_{C'}$，从它减去第一块帧的 $c$ 倍即消去。因此舍去常数参数不会丢掉此原评价族中的函数。

由复用的 (143.12)、(143.16)，每个实际首一函数的检测值正好为 $Q(h)$，于是 $\mathcal D_{d,s}$ 等于这些原域值的张成。最后将二项式系数通分，

$$
d\binom d3-3\binom d4
=d(d-1)(d-2)\left(\frac d6-\frac{d-3}{8}\right)
=\frac{d(d-1)(d-2)(d+9)}{24}.
\tag{146.7}
$$

这证明精确公式。证毕。

## 147. 实际函数实现、源余切核及两个嵌入维数

**命题 147.1（由原域实际首一函数实现独立方向）。** 存在 $h_1,\ldots,h_{r_d}\in\mathcal M_d(F)$，使 $Q(h_i)$ 线性独立。相应的实际函数 $\mathcal E_{h_i}\in S$ 满足

$$
[\mathcal E_{h_i}]\in\ker J,
\qquad
\overline\Psi_s\overline\lambda_s[\mathcal E_{h_i}]=Q(h_i),
\tag{147.1}
$$

并对每组合法实际枢轴同时给出 $r_d$ 个独立四次商类。这里所有线性组合均可用原域 $F$ 的标量及实际首一函数实现。

证明。命题 146.3 已将有限维空间 $\mathcal C_d$ 写成全部实际原域首一值的张成，故由张成集中选基即得这些 $h_i$。这仅是有限维线性代数的存在结论，不要求扩域或引入另一类评价函数。

每个 $\mathcal E_{h_i}$ 在完整图中至少四阶消失。在正规化不变环的余切空间中，只有一次 $U$ 与纯二次 $Y$ 可以保留；二者都为零。因此它在 $\mathfrak m_B/\mathfrak m_B^2$ 中为零，其源类属于 $\ker J$。应用 (143.9)、(143.12)、(143.16)，即得 (147.1)。任何源类或四次商类的线性关系，经这些线性映射后都会成为 $Q(h_i)$ 的关系，故系数全零。

对每个 $i$，所用函数就是 (143.10) 的原域函数，有同一单位分母，其完整源函数未被参数四次截断。参数系数运算只施于已明确的检测多项式 $Q$；这里没有把完整评价函数的某个截断参数系数冒认为具有指定四次首项的源函数。若需实现 $\mathcal C_d$ 的任意向量，直接在这些实际 $\mathcal E_{h_i}$ 之间取有限 $F$ 线性组合，其检测值就是该向量。证毕。

**命题 147.2（实际四次、源核与嵌入维数）。** (144.4) 的全部下界成立。

证明。由命题 147.1，$\overline\Psi_s(\mathcal L_{d,s})=\mathcal C_d$，故 $\dim_F\mathcal L_{d,s}\ge r_d$，并且 $\dim_F(J_4(A_{0,s})/P_4)\ge r_d$。(147.1) 也直接给 $\dim_F\ker J\ge r_d$；这与复用满射 $\overline\lambda_s$ 的方向一致。

为处理实际像纤维，取 $K$ 的一组基 $k_1,\ldots,k_{k_N}$。由 $\operatorname{in}_2(A_{0,s})=K$，取 $f_j\in\mathfrak n_s$ 使其二次符号为 $k_j$。记实际限制 $g_i=\mathcal E_{h_i}|_{B_{0,s}}\in A_{0,s}\cap\mathfrak q^4$。若在实际像纤维中有

$$
\sum_j u_jf_j+\sum_i v_ig_i\in\mathfrak n_s^2,
\qquad u_j,v_i\in F,
\tag{147.2}
$$

先取二次符号。每个零常数像元素至少二阶，故 $\mathfrak n_s^2$ 无二次项；$k_j$ 的独立性迫使全部 $u_j=0$。随后取四次符号。极大理想平方的四次符号必是 $K$ 中二次符号的乘积之和，因而属于 $P_4$。于是

$$
\sum_i v_i p(h_i)^2\in P_4.
$$

应用 $\Psi$，其右侧为零，而 $Q(h_i)$ 独立，故全部 $v_i=0$。这证明 $\mathfrak n_s/\mathfrak n_s^2$ 至少有 $k_N+r_d$ 个独立类。

另一方面，原源环 $S$ 的余切映射为 (143.4) 的 $J$。其源维数由秩核公式给出

$$
\operatorname{edim}S=\operatorname{rank}J+\dim_F\ker J
\ge a+\dim_FK+r_d.
\tag{147.3}
$$

由 $\dim V=N$，$b=\dim W=\binom N2$，以及满射 $w$，040 的二次像维数为

$$
\dim_FK=\frac{b(b+1)}2-\binom N4
=\frac{N^2(N^2-1)}{12}=k_N.
\tag{147.4}
$$

代入即得所有下界。$\ker J$ 属于原源环与正规化环之间的余切映射；(147.2) 属于实际像纤维环自己的余切空间。证明分别在这两个空间中进行，没有把它们的核或极大理想平方等同。证毕。

## 148. 与既有线性下界的精确比较及结论边界

**推论 148.1（对 $4m-25$ 的严格增益）。** 042，定理 138.2 的下界 $4m-25=4d-9$ 在 $d=3$ 时等于 $r_d=3$；对每个 $d\ge4$，都有

$$
r_d>4d-9.
\tag{148.1}
$$

特别地，$d=4$ 时精确检测秩为 $13$，既有下界为 $7$；$d=5$ 时精确检测秩为 $35$，既有下界为 $11$。这些数也分别替换 (144.4) 中的四次、源核及嵌入维数增量。

证明。在纸面公式中直接代入，$r_3=3\binom33=3$，$r_4=4\cdot4-3\cdot1=13$，$r_5=5\cdot10-3\cdot5=35$。一般地，由二项式系数的递推式，

$$
\begin{aligned}
r_{d+1}-r_d
&=(d+1)\binom d2-2\binom d3\\
&=\frac{d(d-1)(d+7)}6\ge10\qquad(d\ge3).
\end{aligned}
\tag{148.2}
$$

而 $4(d+1)-9-(4d-9)=4$。从 $d=3$ 的相等出发，差额的每步增量至少为六，故对所有 $d\ge4$ 严格增益。证毕。

**命题 148.2（检测精确性与评价类精确性的差别）。** 令

$$
\mathcal T_d^{\mathrm{ev}}=
\operatorname{span}_F\{p(h)^2:h\in\mathcal M_d(F)\}
\subseteq\operatorname{Sym}^4W.
\tag{148.3}
$$

则在固定负余切识别中，$\mathcal L_{d,s}=(\mathcal T_d^{\mathrm{ev}}+P_4)/P_4$，且有精确维数恒等式

$$
\dim_F\mathcal L_{d,s}
=r_d+
\dim_F\frac{\mathcal T_d^{\mathrm{ev}}\cap\ker\Psi}
{\mathcal T_d^{\mathrm{ev}}\cap P_4}.
\tag{148.4}
$$

证明。首项公式给第一个相等。$\overline\Psi_s$ 在该子空间上的像为 $\mathcal C_d$，维数为 $r_d$。因 $P_4\subseteq\ker\Psi$，其核恰由 $\mathcal T_d^{\mathrm{ev}}\cap\ker\Psi$ 模掉 $\mathcal T_d^{\mathrm{ev}}\cap P_4$ 得到；秩核公式给 (148.4)。证毕。

**范围 148.3（尚不成立的精确性推论）。** (144.2) 确定的是整个首一评价族的检测系数及检测值张成维数。它本身不消去 (148.4) 的第二项，因此不把 $r_d$ 宣称为整个评价类空间模 $P_4$ 的精确维数，也不把它宣称为全部实际 $J_4(A_{0,s})/P_4$ 的维数。检测空间在各组合法实际枢轴下共同，并不证明整个四次像或完整实际像环与枢轴无关。这里没有 $\ker\Psi=P_4$、完整商或原点完整局部环的分类；没有全局导子、H10、物理、最小性或全局新颖性结论。非零检测下界只用 $\Psi(P_4)=0$，不需要分类检测器的全部核。

## 149. 中文普通语言的完整定理与证明解释

**定理 149.1（全部实际首一评价能检测到多少个新方向）。** 在任意特征零域上，固定一个次数为 $2m$、$m\ge7$ 的可分域扩张，任选本原元，用它从零次幂开始的连续 $m$ 个幂组成半维窗口。保留这个窗口族原来的带符号、带嵌入标签系数。把每个首一 $m-4$ 次原域多项式代入同一个域元素，并以在基点非零的固定评价作分母，就得到一整族原系数局部函数。无论选择哪一组合法的原域正系数枢轴，在正规化的实际纤维中观察这些函数的四次首项，再用消去全部可见二次乘积的指定检测器检测，所得所有向量一共恰好张成

$$
\frac{d(d-1)(d-2)(d+9)}{24}\quad\text{维，}\qquad d=m-4.
\tag{149.1}
$$

同一个数也是这族检测多项式全部向量系数的张成维数；只用首一多项式、只用原域参数值就能达到它。因而可以在实际首一评价函数中选出这么多个函数，使它们在可见二次乘积之外独立，并在原源余切核中给出同样多个独立类。实际像纤维的嵌入维数至少是全部可见二次方向数再加这个数，原源环的嵌入维数至少还要加上 $m(m-1)/2$ 个正方向。其中全部可见二次方向数为 $(m-1)^2((m-1)^2-1)/12$。当 $m=7$ 时新增数为三，与既有下界相同；当 $m\ge8$ 时，它严格超过既有的 $4m-25$，前两个新增数依次为十三和三十五。这里的“恰好”只修饰该评价族经过检测后的张成空间，完整评价类空间和整个实际四次商仍只得到下界。

证明解释。首先，这些函数始终取自原系数局部环：分子是在原域元素上的线性评价，分母在连续幂窗口处是非零幂基体积，所以可以合法相除。已有的原评价首项定理保证，每个首一 $m-4$ 次评价在消去正变量之前就已至少四阶消失；无论用哪组实际正枢轴消元，其四次首项都是指定二次式的平方。已有检测恒等式把这个平方变成一个“六重外积乘一个二向量”的张量，并消去所有实际可见二次方向的乘积。这些原族桥接是前提，新的维数计算必须作用于它们给出的真实参数族。

把多项式本身及其乘一次、二次变量的三个移位并排。六重外积已经含有最低三个幂，故真正剩下的三列恰好是第 145 节那张带重复系数和边界零的矩阵。它的每个最大子式是三次参数多项式，张量另一因子的特定坐标又逐个给出所有原参数。所以全部检测坐标张成的，正好是“所有最大子式乘一个一次参数”组成的四次空间，没有把原矩阵换成条目独立的泛矩阵。

要数这个四次空间，关键是核对实际矩阵满足经典分解定理的条件。若最高的非零系数指标至少为三，取从这个指标起连续三行，矩阵就是对角元相同的三角矩阵，其行列式不为零。代数上的向下归纳精确表明：所有最大子式同时消失的根基理想，就是除去最低两个参数后其余参数生成的理想。这给出恰好 $d-2$ 的 grade，因此经典 Eagon--Northcott 分解确实适用于当前矩阵。四次层里有 $d\binom d3$ 个生成方向，并有 $3\binom d4$ 个独立线性关系。分解还有的更高关系从五次才开始，不进入四次层。两者相减得到 (149.1)。

接下来要防止把坐标多项式的个数误当成实际方向数。有限维对偶性说明：一个线性泛函消去所有向量系数，恰好等于它消去整个向量多项式，因此坐标多项式空间的维数就是向量系数张成维数。检测多项式是四次齐次的，把最高参数固定为一仍能唯一恢复原齐次多项式，不丢任何线性关系。特征零使原域无限，一个多项式若在全部原域参数上为零就只能恒为零。因此首一原域实际值已经张成同一个空间；常数项又不改变任何检测值。这就把抽象系数维数完整传回整个实际首一评价族。

最后从这些实际值中选一组基，使用对应的原评价函数。它们的完整图四阶消失使正规化余切看不见它们，而四次检测又证明它们不能在原源余切中彼此抵消，也不能在实际像纤维中变成极大理想平方。再在实际像纤维中加入全部二次方向的一组提升，先看二次项、再看四次项，就证明这些类总共独立。在原源环中，则用已知余切像维数加上这里证明的源核下界。两个嵌入维数由各自的局部环分别计算。整个论证既给出比旧线性下界更强的原族结论，也保留检测器可能遗漏其他评价类和其他实际四次方向的边界。证毕。

## 150. 数学来源和第一处未解义务

**约定 150.1（来源的确切作用）。** [039，§§111、113、115--117](AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) 提供同一原域带符号系数像、有限正规化和实际横截面；[040，定理 122.1、命题 122.2](AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md) 提供完整耦合余切像。全 $m\ge7$ 的实际像纤维二次桥、单位分母评价、完整图四阶消失、精确检测恒等式和源余切满射，使用 [042，§§134--139](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) 的固定文本；其 SHA256 为 `85bcd2c7e82e2e4d2a4ca2fa835ecf0cc430e8054bdcf7ccd90d78555b91ac94`。这些引用均作纸面数学输入，不提升为 kernel 真值。041 的低次数定义不用于这些全次数结论。

David A. Buchsbaum 与 David Eisenbud，[*Generic Free Resolutions and a Family of Generically Perfect Ideals*](https://eisenbud.github.io/papers/pdfs/1975-001.pdf)，*Advances in Mathematics* **18** (1975)，245--301，Theorem 3.1，印刷页 269，以及 Corollary 3.2，页 269--270，是此处 `literature-attested` 的自由分解来源：Noetherian 环上，自由模秩 $d\to3$，最大子式理想 grade 等于 $d-2$ 时，$p=1,q=3$ 给 Eagon--Northcott 分解。页 270--271 的微分说明给出使用的分次形状。第 145 节核对实际矩阵及其 grade；引用不把矩阵条目预设为独立变量。

引理 145.2 的专门矩阵根基计算、检测坐标与 $I_4$ 的相等、整个首一原域族的系数和值空间相等，以及由实际函数得到的 (144.4)，是这些输入上的 `repo-derived` 综合推导。经典分解本身不是本卷的新结果，本卷也不据此主张文献中的全局原创性。

**问题 150.2（受限评价类的首个未解核交）。** 在相同原域和连续幂识别下，确定

$$
\frac{\mathcal T_d^{\mathrm{ev}}\cap\ker\Psi}
{\mathcal T_d^{\mathrm{ev}}\cap P_4}.
\tag{150.1}
$$

这是把精确检测秩提升成整个评价类模 $P_4$ 精确维数时首先缺少的义务；本卷保留其为 open。即使这个受限核交为零，仍需另外确定一般原系数函数在实际消元后贡献的四次方向，才能求出完整 $J_4(A_{0,s})/P_4$。当前的受限精确秩与非零下界不依赖这两项分类。

## 追加锚（本行以下为增补区）

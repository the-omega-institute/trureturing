# 原域二元测试的正规反典范几何与强制节点

## 86. 结构化核关联与高余秩像的余维

**约定 86.1（固定原对象与已有输入）。** 设 $F$ 为特征零域，$D/F$ 为固定的实际可分域扩张，$[D:F]=2m\ge8$。沿用 source033 §§81–83 的原基、体积形式、实际目标 $C\subset D$、系数空间 $H_D$、系数像 $\Gamma_D$ 及 $p=[P_C]$。特别地，$C$ 满足假设 81.2：在 $K=\overline F$ 上按原嵌入分裂后，其行 $c_1,\ldots,c_{2m}$ 的任意 $m$ 行独立，且 $p\in(\Gamma_D)_{\mathrm{sm}}(F)$。不另加 $C^2=D$ 的假设。记

$$
X=\operatorname{Gr}_F(m,D),\qquad
G=\operatorname{Gr}_F(2,C),\qquad
g=2m-4,\qquad n=g-1=2m-5.
\tag{86.1}
$$

$\mathcal S\subset C\otimes_F\mathcal O_G$ 是秩二 tautological 子丛，$\mathcal O_G(1)=\det\mathcal S^\vee$。统一窗口开集记为 $X^{\mathrm{un}}$：其几何帧的任意 $m$ 行独立。再要求系数映射有定义且 $[P_W]\ne p$，所得开集记为 $X^*$。source033 的非退化性和系数映射的占优性保证它非空。

原乘法先给 $\widetilde\mu_W:C\otimes_F W\to D$，再限制到 tautological 二平面，给出丛映射

$$
\mu_W:\mathcal S\otimes_F W\longrightarrow D\otimes_F\mathcal O_G,
\qquad u\otimes w\longmapsto uw.
\tag{86.2}
$$

其行列式零概形就是 source033 的 $T_W=T_{[P_W]}$。在分裂坐标、$U\in G_K$ 的帧 $(u,v)$ 和 $W_K$ 的帧 $B_W$ 下，它的矩阵为

$$
K_U=[\operatorname{diag}(u)B_W,\operatorname{diag}(v)B_W].
\tag{86.3}
$$

交换列块只改变固定符号。source031 定理 72.3 和 source033 引理 81.5、81.6 给出指定线性系、其核 $FP_C$，以及 $X^*$ 上非零的 Cartier 除子 $T_W$。这些结论不把指定线性系认作完整线性系。

核关联也有不依赖分裂的写法：$Y_W$ 是 $\mathbb P(C\otimes_F W)$ 中满足张量秩至多二及 $\widetilde\mu_W(a)=0$ 的闭概形。这里张量 $a$ 视为 $W^\vee\to C$ 的线性映射。分裂后其方程正是 $c_iAw_i^{\mathsf t}=0$。source033 引理 82.2 排除了统一窗口的非零秩一张量；引理 83.1 因此给出射影满射

$$
\pi_W:Y_W\longrightarrow T_W,
\qquad [a]\longmapsto\operatorname{im}a,
\qquad
\pi_W^{-1}(U)=\mathbb P(\ker K_U)
\tag{86.4}
$$

的完整纤维概形。source033 §82、定理 83.2 还给出几何泛参数处 $Y_W$ 几何正规且几何整、$T_W$ 几何整，两者维数均为 $n$；在余秩一开集，式 (83.6) 给出概形同构。此处复用的是其泛纤维正规性证明，不把联合空间的奇异集公式当作每个纤维的公式。

**引理 86.2（同一原窗口空间上的正规关联开集）。** 存在非空 $F$-开集 $\mathcal U_Y\subset X^*$，使其每个几何窗口的 $Y_W$ 几何正规、几何整且纯维数为 $n$，$T_W$ 几何整且维数为 $n$。

证明。上述内在构造以 $X$ 的 tautological 子丛替代 $W$，给出原 $F$ 上的射影有限表示族。扩到 $K$ 并取窗口帧后，逐行射影化占优于 source033 的行参数开集。因此该行参数族的几何泛纤维结论经帧空间传到 $X$ 的几何泛点；几何整性与几何正规性均可沿域扩张下降。先复用 source033 的几何整纤维开集，并用泛平坦化缩小参数底。

为把泛点的正规性展开为开集，具体检查其假设。在统一窗口处没有秩一点，故 $Y_W$ 位于光滑的射影秩二矩阵层中，该层维数为 $4m-5$，而 $Y_W$ 由 $2m$ 个方程截出。每个分支的维数至少为 $n$。射影族纤维维数的上半连续性允许再缩小底，使每个纤维维数至多为 $n$，从而全部分支恰为 $n$ 维。这些方程在正则环境中高度为 $2m$，构成正则序列。因此每个几何纤维都是局部完全交，满足 $S_2$。

在这个平坦有限表示族中，非光滑 locus $\Sigma$ 是源的闭子集；其几何纤维就是相应几何纤维的非正则 locus。几何泛纤维正规，故该 locus 维数至多为 $n-2$。$\Sigma$ 对底仍射影，纤维维数上半连续；移去满足 $\dim\Sigma_W\ge n-1$ 的闭集，便得非空 $F$-开集。其几何纤维满足 $R_1$，与 $S_2$ 合用 Serre 正规判据即得正规性。这里所有收缩都保留泛点，且由原 $F$ 上的族定义；没有用任意分裂行元组代替一个实际 $F$-窗口。$\square$

## 87. 结构化原乘法族的正规反典范定理

**定理 87.1（结构化原乘法族的正规反典范几何）。** 在约定 86.1 的同一实际 $D/F$、目标 $C$ 和窗口空间 $X$ 上，对 $\mathcal U_Y$ 的每个几何窗口，令

$$
Z_W=\{U\in T_W:\operatorname{corank}K_U\ge2\}_{\mathrm{red}}.
\tag{87.1}
$$

则 $\dim Z_W\le n-2$，即其在 $T_W$ 中余维至少为二。$T_W$ 正规；$\pi_W$ 是在余秩一开集上为概形同构的射影双有理态射。

该结构族的反典范类及结构层上同调如下；这些经典计算适用于更大的范围，即任意实际 $W\in X^*(F)$，不要求这个特化正规。令

$$
A_W=\det_F D\otimes_F(\det_F W^\vee)^{\otimes2},\qquad
\Lambda_{C,W}=(\det_F C^\vee)^{\otimes2}\otimes_F A_W.
\tag{87.2}
$$

这些都是一维 $F$-向量空间。原乘法行列式是 $\mathcal O_G(m)\otimes_F A_W$ 的截面，且有

$$
\begin{aligned}
\omega_G&\simeq\mathcal O_G(-m)\otimes_F(\det_F C^\vee)^{\otimes2},\\
\mathcal O_G(T_W)&\simeq\mathcal O_G(m)\otimes_F A_W,\\
\omega_{T_W}&\simeq\mathcal O_{T_W}\otimes_F\Lambda_{C,W}.
\end{aligned}
\tag{87.3}
$$

并且

$$
\begin{aligned}
H^0(T_W,\mathcal O_{T_W})&=F,\\
H^a(T_W,\mathcal O_{T_W})&=0&& (0<a<2m-5),\\
H^{2m-5}(T_W,\mathcal O_{T_W})&\simeq\Lambda_{C,W}^\vee\simeq F.
\end{aligned}
\tag{87.4}
$$

特别地，$T_W$ 是 Gorenstein，$\omega_G\simeq\mathcal O_G(-m)$、$\omega_{T_W}\simeq\mathcal O_{T_W}$ 作为线丛同构成立。后一写法不指定典范的非零体积形式；(87.4) 末尾的 $F$ 同构也是向量空间同构，未选择 $\Lambda_{C,W}$ 的平凡化时应保留中间的一维线。因此，对每个实际 $W\in\mathcal U_Y(F)$，同一个原乘法测试除子 $T_W$ 几何正规、几何整且反典范，并具有所列全部结构层上同调。

证明。先证明结构化核关联给出的余维界与正规性，再在这一族中应用经典伴随、射影丛上同调和 Serre 对偶。

全在几何底域上论证第一部分。$Y_W$、$T_W$ 整且同维，满射 (86.4) 的泛纤维维数为零。其完整纤维是射影线性空间，故泛点的核维数为一。于是余秩一开集非空，$Z_W$ 是由子式定义的真闭集，$E=\pi_W^{-1}(Z_W)$ 是 $Y_W$ 的真闭集，满足 $\dim E\le n-1$。

取 $Z_W$ 的任一不可约分支 $Z$。在其泛点，(86.4) 的纤维是维数至少一的射影空间。故 $E$ 有一个支配 $Z$ 的分支 $E_Z$，其泛纤维维数至少一；纤维维数公式给

$$
\dim Z+1\le\dim E_Z\le n-1.
\tag{87.5}
$$

这证明所需界。关键使用了完整核纤维的正维性；单说“射影双有理”不提供这项计算。

source033 的余秩一 Schur 补图使 $\pi_W$ 在 $T_W\setminus Z_W$ 上成为概形同构。$T_W$ 的每个余维一点都在该开集中，对应 $Y_W$ 的余维一点。$Y_W$ 正规，故这些局部环正则，$T_W$ 满足 $R_1$。另一方面，$T_W$ 是光滑 $G$ 上的有效 Cartier 除子，局部环为正则局部环模一个非零因子，因而 Cohen–Macaulay，满足 $S_2$。Serre 的经典 $R_1+S_2$ 判据（Stacks Project，Tag 031S）给出正规性。论证对任意几何扩底成立。

现在固定任意实际 $W\in X^*(F)$，计算同一指定族的行列式线。令 $\mathcal Q=(C\otimes_F\mathcal O_G)/\mathcal S$。Grassmannian 的经典切丛公式为 $T_G\simeq\mathcal S^\vee\otimes\mathcal Q$，其中两因子秩分别为二和 $m-2$。由行列式张量公式和 tautological 正合列，

$$
\begin{aligned}
\det T_G
&=(\det\mathcal S^\vee)^{\otimes(m-2)}\otimes(\det\mathcal Q)^{\otimes2}\\
&=\mathcal O_G(m)\otimes_F(\det_F C)^{\otimes2}.
\end{aligned}
\tag{87.6}
$$

取对偶得到 (87.3) 的第一式。对原乘法映射 (86.2) 取行列式，其截面所属线丛为

$$
\det_F D\otimes\det(\mathcal S\otimes_F W)^\vee
=\mathcal O_G(m)\otimes_F A_W.
\tag{87.7}
$$

source033 的核等式保证此截面非零；光滑整 $G$ 上的非零截面是非零因子，给出 (87.3) 的第二式。有效 Cartier 除子嵌入的经典伴随公式（Stacks Project，Tags 0B4B、0AA4）给

$$
\omega_{T_W}\simeq
(\omega_G\otimes\mathcal O_G(T_W))|_{T_W},
\tag{87.8}
$$

即第三式。具体而言，局部正合列 $0\to\mathcal O_G(-T_W)\to\mathcal O_G\to\mathcal O_{T_W}\to0$ 计算出的 $\mathcal E xt^1_G(\mathcal O_{T_W},\omega_G)$ 正是右端；低余维 Cartier 嵌入的对偶理论将其识别为对偶层。正则局部环是 Gorenstein，模一个非零因子仍是 Gorenstein，所以这里不要求 $T_W$ 光滑或先验正规。

一维常数向量空间张成的线丛均可平凡化，故得到所述线丛同构。将 $\Lambda_{C,W}$ 认作 $F$ 需要选择一个非零元素；改变窗口帧、目标体积或其他行列式平凡化会相应改变这个选择。式 (87.3) 保留了这些因子，不从反典范类推出一个未作选择的规范体积形式。

为计算这些原乘法除子的完整上同调，先使用经典射影丛上同调公式（Stacks Project，Tags 01XT、01XX）在原 $F$ 上取得中间等式

$$
H^0(G,\mathcal O_G)=F,\qquad
H^a(G,\mathcal O_G)=0\quad(a>0).
\tag{87.9}
$$

具体地，考虑旗簇 $\mathcal F=\{(\ell,U):\ell\subset U\subset C,\ \dim\ell=1,\ \dim U=2\}$。投影 $\mathcal F\to G$ 是纤维为 $\mathbb P^1$ 的射影丛；投影 $\mathcal F\to\mathbb P(C)$ 是纤维为 $\mathbb P^{m-2}$ 的射影丛，后者参数为 $C/\ell$ 中的一维子空间。

经典射影丛上同调公式在任一仿射平凡化底上给 $p_*\mathcal O=\mathcal O$、$R^a p_*\mathcal O=0$（$a>0$）；它们由射影空间的结构层上同调计算得出，并在交上相容。两次 Leray 谱序列因而给出

$$
H^a(G,\mathcal O_G)
\simeq H^a(\mathcal F,\mathcal O_{\mathcal F})
\simeq H^a(\mathbb P(C),\mathcal O_{\mathbb P(C)}).
\tag{87.10}
$$

最后一项在 $a=0$ 为 $F$，在 $a>0$ 为零，故得 (87.9)。这是射影丛消失定理的应用，不需要把奇异 $T_W$ 当作 Kodaira 消失的光滑底。

由 (87.3) 有 $\mathcal O_G(-T_W)=\omega_G\otimes_F\Lambda_{C,W}^\vee$。光滑射影 $g$ 维 $G$ 上的经典 Serre 对偶（Stacks Project，Tag 0FVZ；$G$ 为纯维 Cohen–Macaulay）与 (87.9) 给

$$
H^a(G,\mathcal O_G(-T_W))
\simeq H^{g-a}(G,\mathcal O_G)^\vee\otimes_F\Lambda_{C,W}^\vee
=\begin{cases}
\Lambda_{C,W}^\vee,&a=g,\\
0,&a\ne g.
\end{cases}
\tag{87.11}
$$

将它和 (87.9) 代入 Cartier 正合列的上同调长正合列。由于 $g\ge4$，次数零处给 $H^0(T_W,\mathcal O)=F$；$0<a<g-1$ 处全部为零；次数 $g-1$ 处连接态射给 $H^{g-1}(T_W,\mathcal O)\simeq\Lambda_{C,W}^\vee$，即 (87.4)；高于 $n=g-1$ 的次数由维数消失。伴随公式、射影丛消失和 Serre 对偶均只作为本结构族定理的经典证明输入；与第一部分合用，得到所述正规反典范原乘法族。$\square$

**推论 87.2（系数底上的一般正规性与实际窗口）。** 存在非空 $F$-开集 $\Gamma^{\mathrm{nor}}\subset\Gamma_D\setminus\{p\}$，使每个几何 $q\in\Gamma^{\mathrm{nor}}$ 的 $T_q$ 几何正规且几何整。并且 $\mathcal U_Y(F)$ 非空；它的每个非空 $F$-开子集都有实际窗口。

证明。系数映射占优，定理 87.1 的几何泛窗口结论沿函数域扩张下降，得到系数几何泛点处的正规性。复用 source033 的几何整系数开集。通用除子族在 $\Gamma_D\setminus\{p\}$ 上相对 Cartier 且平坦，各纤维都是维数 $n$ 的 Cohen–Macaulay 概形。其非光滑 locus 对系数底射影；如引理 86.2，用该 locus 的纤维维数上半连续性，从泛点的 $R_1$ 得到非空 $F$-开集上的 $R_1$，再用 $S_2$。这给出 $\Gamma^{\mathrm{nor}}$。

$X$ 的原 $F$ 大胞腔是 $\mathbb A_F^{m^2}$，且 $F$ 无限。任一非空 $F$-开集与此胞腔交于非空开集，其中含有一个非零多项式的非消失主开集。非零多项式不可能在无限域的全部 $F$-元组上消失，故存在实际 $F$-点。这也适用于 $\mathcal U_Y$ 的任意非空 $F$-开子集。$\square$

## 88. 基点分支的全部低阶交与强制奇异层

**定理 88.1（交的概形、维数与消失阶）。** 在 $K$ 上令 $B_i=\operatorname{Gr}(2,\ker c_i)\subset G_K$。对每个 $I\subset\{1,\ldots,2m\}$，$|I|=r\le m-2$，其概形交为

$$
B_I:=\bigcap_{i\in I}B_i
=\operatorname{Gr}\left(2,\bigcap_{i\in I}\ker c_i\right)
\simeq\operatorname{Gr}(2,m-r),
\qquad \dim B_I=2(m-r-2).
\tag{88.1}
$$

对任意竞争窗口 $W\in X^*$，其行列式截面局部满足

$$
\det K\in\mathcal I_{B_I}^{\,r}.
\tag{88.2}
$$

特别地，每个二元交 $B_i\cap B_j$ 都包含于 $T_W$ 的几何奇异 locus，其维数恰为 $2m-8$。这是奇异 locus 的包含关系，并非对全部奇异点的分类。

证明。统一性使任意 $r\le m$ 个 $c_i$ 独立，故共同核维数为 $m-r$。$B_i$ 是 $\mathcal S\to\mathcal O_{G_K}$、$s\mapsto c_i(s)$ 的零概形。将这些映射合并为 $\mathcal S\to K^r\otimes\mathcal O_{G_K}$，其零概形的函子正是取共同核中的秩二子丛，所以概形上得到 (88.1)，不只是支撑等式。Grassmannian 的标准维数公式给出其维数。

在 $\mathcal S$ 和行列式线丛的任意局部平凡化中，第 $i$ 行为 $(u_iw_i,v_iw_i)$。若 $i\in I$，它的每个条目都属于 $\mathcal I_{B_I}$。行列式的每一项都从这些 $r$ 行各取一个条目，因此属于 $\mathcal I_{B_I}^{r}$。换平凡化只乘单位，故 (88.2) 与选择无关。

取 $r=2$。在二元交的每个几何点，局部方程属于环境极大理想的平方，所以函数值及全部一阶微分均为零。由于 $T_W$ 是光滑 $G_K$ 中的非零超曲面，其该点局部环的嵌入维数为 $g$，而维数为 $g-1$，不正则。故此点确为奇异点。$\square$

**推论 88.2（八次情形的固定二十八点）。** 当 $m=4$ 时，每个 $B_i\simeq\mathbb P^2$，每个二元交是一个点

$$
U_{ij}=\ker c_i\cap\ker c_j\in\operatorname{Gr}(2,C_K),
\qquad 1\le i<j\le8.
\tag{88.3}
$$

这 $\binom82=28$ 个点两两不同，且没有三重交。

证明。$\ker c_i$ 为三维，故 $B_i=\operatorname{Gr}(2,3)\simeq\mathbb P^2$。两个独立行的共同核为二维，只容纳它自身这个二平面。三个不同行独立，其共同核为一维，不包含二平面。若两个不同无序对给同一个 $U$，它至少同时位于三个不同行的核中，矛盾。$\square$

## 89. 八次结构化窗口中的非空节点开集

**定义 89.1（固定对处的三个开条件）。** 本节 $m=4$，固定 $U=U_{ij}$。用窗口的四维参数空间 $E$ 写其行 $w_l\in E^\vee$，令 $a_l=c_l|_U\in U^\vee$，并置

$$
R_{ij}(W)=\operatorname{span}_K\{a_l\otimes w_l:l\ne i,j\}
\subset U^\vee\otimes E^\vee.
\tag{89.1}
$$

当这六行秩为六时，$Q_{ij}(W)=(U^\vee\otimes E^\vee)/R_{ij}(W)$ 为二维空间。要求两个映射

$$
\begin{aligned}
L_i:U^\vee&\longrightarrow Q_{ij}(W),&\alpha&\longmapsto[\alpha\otimes w_i],\\
L_j:U^\vee&\longrightarrow Q_{ij}(W),&\beta&\longmapsto[\beta\otimes w_j]
\end{aligned}
\tag{89.2}
$$

均为同构。所指三个条件是六行秩六、$L_i$ 同构和 $L_j$ 同构；它们只涉及实际结构化矩阵的行。

**引理 89.2（固定对的结构化非空性）。** 在完整行参数空间 $(\mathbb P(E^\vee))^8$ 中，定义 89.1 的条件给出非空开集；它与统一行开集相交非空。

证明。逐行非零缩放不改变 $R_{ij}$，只把两个 $L$ 分别乘以非零标量，故这些条件在行的射影类上有定义。秩六是子式非消失的开条件；在此开集上 $Q_{ij}$ 是秩二商丛，在各射影图中选行代表后，两项同构条件是其行列式非消失，因而也开。为证明非空，先注意任意两个 $a_l,a_t$（$l,t\notin\{i,j\}$，$l\ne t$）独立：否则四行 $c_i,c_j,c_l,c_t$ 在 $C_K$ 上相关，违反统一性。

将其余六个指标任意分为三对 $\{r_s,t_s\}$，$1\le s\le3$。取 $E^\vee$ 的基 $e_1,e_2,e_3,e_4$，指定

$$
w_{r_s}=w_{t_s}=e_s\quad(1\le s\le3),
\qquad w_i=w_j=e_4.
\tag{89.3}
$$

这完全保留行 $a_l\otimes w_l$ 的规定结构。每对 $a_{r_s},a_{t_s}$ 张成 $U^\vee$，所以

$$
R_{ij}=U^\vee\otimes\langle e_1,e_2,e_3\rangle,
\qquad Q_{ij}\simeq U^\vee\otimes Ke_4.
\tag{89.4}
$$

其维数为六和二，两个 $L$ 都是同构。这证明相应开集非空。(89.3) 本身无需统一：完整行参数空间不可约，而任意四行独立的统一行集合是非空稠密开集，故它与刚构造的非空开集相交非空。这里使用开集相交，而没有声称这个辅助元组就是所需统一窗口。$\square$

**定理 89.3（二十八条件同时成立并下降到实际窗口）。** 存在非空 $F$-开集 $\mathcal U_{\mathrm{node}}\subset\operatorname{Gr}_F(4,D)$，使每个几何窗口统一、$[P_W]\ne p$、$Y_W$ 几何正规且几何整、$T_W$ 几何正规且几何整，并且定义 89.1 在全部二十八个 $U_{ij}$ 同时成立。该开集有实际 $F$-点。

证明。在 $K$ 上，对每一对 $i,j$ 应用引理 89.2。有限个非空开集在不可约的 $(\mathbb P^3)^8$ 中相交非空；再与统一行开集相交仍非空。拉回非零行代表空间后，这是一组满秩 $8\times4$ 帧的非空开条件。它在右侧 $\operatorname{GL}_4$ 换帧下不变：换帧同时同构 $E$、$R_{ij}$、$Q_{ij}$，保持两项同构条件。帧空间到 $X_K$ 是开满射的 $\operatorname{GL}_4$ 主丛，因此这些条件下降为 $X_K$ 上的非空开集。

取原 $D/F$ 的一个有限 Galois 分裂域 $L$。上述条件全部在 $L$ 上定义，$\operatorname{Gal}(L/F)$ 只置换原嵌入指标并对系数作相应作用；$C$ 是原实际目标。由于同时要求所有无序对的条件，这个开集及其闭补集 Galois 不变，遂下降为非空 $F$-开集。该下降也与窗口换帧相容；没有把独立给定的分裂行误认作原域点。

最后与引理 86.2 的 $\mathcal U_Y$ 相交。$X$ 几何整，所以交仍为非空 $F$-开集，记为 $\mathcal U_{\mathrm{node}}$；定理 87.1 保证 $T_W$ 正规。推论 87.2 的原大胞腔论证给出 $\mathcal U_{\mathrm{node}}(F)\ne\varnothing$。故所证非空性确实产生同一个实际域 $D$ 内的窗口，并非仅有分裂坐标元组。$\square$

**定理 89.4（每个强制点的秩四二次初始式）。** 对任意代数闭扩域 $k/F$ 及 $W\in\mathcal U_{\mathrm{node}}(k)$，$T_W$ 在全部扩底后的 $U_{ij}$ 处都是普通二重点。在 $G_k$ 的四个正则局部参数中，其方程的二次初始式等价于

$$
x_1y_2-x_2y_1,
\tag{89.5}
$$

其秩为四。特别地，各点的完备局部环为 $k[[z_1,z_2,z_3,z_4]]/(z_1z_2-z_3z_4)$，其奇异概形在该点的局部环为 $k$。

证明。将分裂记号扩到 $k$，固定 $U=U_{ij}$。选补空间 $H$ 使 $C_k=U\oplus H$；$c_i,c_j$ 在 $H$ 上构成对偶基。邻近的二平面是 $Z:U\to H$ 的图，映射

$$
Z\longmapsto(x,y)=(c_i\circ Z,c_j\circ Z)\in U^\vee\oplus U^\vee
\tag{89.6}
$$

是四维线性同构，给出 Grassmannian 的正则局部参数。矩阵的第 $i,j$ 行分别为 $x\otimes w_i$、$y\otimes w_j$；在 $Z=0$ 时它们为零，其余六行秩六。

选取其余六行的一个可逆六阶子式，作局部可逆列变换和 Schur 消元。局部行列式等于一个单位乘以剩余二阶矩阵的行列式。商丛 $Q_{ij}(Z)$ 可在邻域平凡化；由于前两行在原点为零，商丛平凡化的变化只影响二阶以上项。因此剩余两行的一次项恰为 $L_i(x)$ 和 $L_j(y)$，行列式的二次项为

$$
\varepsilon\,\det_Q(L_i(x),L_j(y)),\qquad \varepsilon\in k^\times.
\tag{89.7}
$$

两个 $L$ 都是同构。分别对 $x,y$ 作可逆线性换元，并吸收非零常数，便得到 (89.5)。其极化配对在两个二维因子之间是非退化的交替配对；若 $(x,y)$ 与所有 $(x',y')$ 的配对为零，先取 $x'=0$ 得 $x=0$，再取 $y'=0$ 得 $y=0$。故四变量二次型的根为零，秩恰为四。

为明确“普通二重点”的局部含义，也可直接使用经典形式 Morse 引理的逐次消元。设方程已归一为 $q+h$，$q$ 为 (89.5)，$h$ 的最低次数为 $d\ge3$。$\partial q/\partial z_a$ 是四个独立线性式，故 $h$ 的 $d$ 次齐次部分可写为 $\sum_a b_a\,\partial q/\partial z_a$，其中各 $b_a$ 为 $d-1$ 次齐次式。换元 $z_a\mapsto z_a-b_a$ 消去该项，误差次数至少为 $d+1$。逐次进行，这些切映射为恒等的换元在极大理想进拓扑中收敛为形式自同构，得到方程 $q$。重排变量给所述完备局部环。

最后，方程一阶导数的线性部分独立，在环境局部环的 $\mathfrak m/\mathfrak m^2$ 中构成基。Nakayama 引理使 Jacobian 理想生成 $\mathfrak m$；其商连同原方程只剩 $k$。因此这些点既是孤立奇异点，也是奇异概形的约化点。此证明只计算固定的强制点，不排除其他位置的奇异点。$\square$

## 90. 原嵌入的无序对 étale 概形与完整白话定理

**定义 90.1（原域的无序异元对概形）。** 对 $E_D=\operatorname{Spec}D$，定义

$$
\mathscr P_2(D/F)=
\bigl((E_D\times_F E_D)\setminus\Delta_{E_D/F}\bigr)/\mathfrak S_2,
\tag{90.1}
$$

其中换位交换两个因子，商取有限仿射商。这个定义只依赖原扩张 $D/F$，不依赖窗口、目标或原嵌入的编号。

**定理 90.2（二十八次有限 étale 概形及其原域不可见性）。** 当 $[D:F]=8$ 时，$\mathscr P_2(D/F)$ 是次数二十八的有限 étale $F$-概形，且

$$
\mathscr P_2(D/F)(F)=\varnothing.
\tag{90.2}
$$

对固定统一实际目标 $C$，存在规范的闭浸入

$$
\nu_C:\mathscr P_2(D/F)\hookrightarrow G,
\tag{90.3}
$$

其几何点映射为

$$
\{\sigma_i,\sigma_j\}\longmapsto
\ker(\sigma_i|_{C_K})\cap\ker(\sigma_j|_{C_K})=U_{ij}.
\tag{90.4}
$$

其像 $N_C$ 与 $W$ 无关。对每个实际 $W\in\mathcal U_{\mathrm{node}}(F)$，它是 $T_W$ 的次数二十八的有限 étale 强制节点子概形；$\nu_C$ 在几何扩底后把无序原嵌入对等变地、逐点且概形同构地对应到全部这些强制节点。$\mathscr P_2(D/F)$ 不要求连通。

证明。$D/F$ 有限可分，故 $E_D$ 有限 étale，其对角在乘积中开且闭。令 $A_{\ne}$ 为对角补集的有限 étale 坐标代数；换位 $\tau$ 作用于它，(90.1) 的坐标代数为 $A_{\ne}^{\tau}$。在一个有限 Galois 分裂域 $L$ 上，$A_{\ne}\otimes_F L$ 是按有序不同嵌入对索引的 $L^{56}$；换位没有不动点。取不变量与此次扩底交换：特征零下平均算子 $(1+\tau)/2$ 给出不变量直和因子。因此

$$
\mathscr P_2(D/F)_L
\simeq\coprod_{\{i,j\}\subset\{1,\ldots,8\},\ i\ne j}\operatorname{Spec}L.
\tag{90.5}
$$

有限 étale 性可沿忠实平坦扩底下降，次数因而为二十八。这也是有限 étale 概形与有限连续 Galois 集对应在无序异元对上的应用。

在 $L$ 上按 (90.4) 定义态射。原 $C$ 在 Galois 作用下保持，$\gamma(U_{ij})=U_{\gamma i,\gamma j}$，故态射等变，下降为 (90.3)。推论 88.2 说明它在代数闭包上是有限个不同的约化点嵌入，因而为闭浸入；闭浸入可忠实平坦下降，得到原 $F$ 上的闭浸入。这里“规范”指该映射由原嵌入限制到 $C$ 的共同核确定，与编号、分裂域和帧无关，不表示选择了一个节点的原域点。

定理 88.1 使这个约化子概形包含在每个非零 $T_W$ 中，并使其几何点都奇异。当 $W\in\mathcal U_{\mathrm{node}}(F)$ 时，定理 89.4 又证明各点为普通二重点，且当地奇异概形约化。因此 (90.3) 因子化到奇异概形，像恰为这些固定点组成的强制节点子概形，而不是整个奇异概形的断言。

最后，$D$ 是原实际域，故绝对 Galois 群在八个原嵌入上作用传递。一个 $F$-有理无序对必须是 Galois 不变的二元子集；但传递集的非空不变子集只能是整个八元集，不可能恰有两个元素。这证明 (90.2)。二元子集的轨道可以有多个，故无 $F$-点并不推出该有限 étale 概形连通。经闭浸入，$N_C(F)=\varnothing$；这不排除 $T_W$ 的其他 $F$-点或其他有理奇异点。$\square$

**定理 90.3（完整白话形式的较大几何结构）。** 固定特征零原域、其中一个次数为 $2m\ge8$ 的实际可分域扩张，以及一个满足约定 86.1 的实际目标窗口。原域乘法将“目标中一个二平面与竞争窗口相乘是否退化”的二元关系，组织为目标自身 Grassmannian 上的指定行列式除子。在竞争窗口的一个非空原域开集中，这些除子几何整、正规、Gorenstein，且对偶层同构于平凡线丛；它们的结构层上同调只有零次和最高次各为原域的一维向量空间，中间各次都为零。这里 Grassmannian 属于目标，除子截面由竞争窗口提供，而测试的乘法始终来自原来的实际域。

无论窗口是否位于该一般开集，只要统一且截面非零，两个原嵌入在目标上同时为零的二平面都会强制出现几何奇异性；更高的共同核给出相应的高阶消失。当扩张次数为八时，这种二元交恰有二十八个不同的固定几何点。在另一个非空原域开集中，每一点的局部最低项都是四变量非退化二次式；它描述两个二维局部变量组之间的非退化二次交叉，所以这些点都是普通二重点。

这二十八个点的原始标签不是任选的八个复数或一个新造分裂模型，而是原扩张的八个嵌入的无序不同二元对。它们整体构成一个规范的二十八次有限 étale 原域概形，并经目标的共同核映射嵌入测试除子。原扩张为域，嵌入的 Galois 作用传递，故没有任何一对能单独下降为原域有理点；这些强制节点在几何上存在，却都不是原域有理节点。这个结论没有把正规性改成光滑性，也没有断言二十八点穷尽全部奇异点。

证明。原乘法与指定 Grassmannian 截面的对应为约定 86.1 的 (86.2)–(86.4)，其线性系和准确核来自 source031、source033 的已述输入。引理 86.2 与定理 87.1 以完整射影核纤维排除余维一的高余秩像，再用余秩一概形图和 $R_1+S_2$ 得正规性；推论 87.2 保证一般条件是同一原域上有实际点的非空开集。定理 87.1 的证明在这一结构族内应用经典伴随、射影丛上同调及 Serre 对偶，给出 Gorenstein、平凡对偶层及全部结构层上同调；其中保留常数行列式线，所以一维向量空间和体积形式的选择不混同。

定理 88.1 给共同核 Grassmannian 及理想幂中的消失，推论 88.2 给八次的二十八个互异点。定理 89.3 先在实际结构化行族中证明每一对条件非空，再有限相交、换帧下降和 Galois 下降到原窗口空间；定理 89.4 的 Schur 补及秩四二次型证明给出各点的普通二重点性质。定理 90.2 将同一组原嵌入的无序对等变下降为有限 étale 子概形，并用原域扩张的传递性排除其 $F$-点。因此白话陈述中的每个几何和原域结论都保持了同一个 $D/F$、$C$ 与 $W$。$\square$

**来源与精确适用范围。** 伴随、对偶、射影丛上同调、Serre 正规判据和有限 étale–Galois 对应为 `literature-attested`。指定乘法族的正规性桥、实际窗口上的同时非空节点条件、强制点局部计算及其原标签下降为本卷的 `repo-derived` 推导，不作全球原创性声明。

| 来源 | 精确使用范围与区别 |
| --- | --- |
| [source031，§72](https://github.com/the-omega-institute/trureturing/blob/20094c4ddd6fda9277d9f41f64bb457041a6c5ad/docs/develop/theory/AURIC_R5_031_TARGET_OWNED_POSITIVE_GRASSMANN_GEOMETRY.md)；[source033，§§81–83](https://github.com/the-omega-institute/trureturing/blob/974984733cb1d619221ff97000612a9194bc8828/docs/develop/theory/AURIC_R5_033_ALL_DEGREE_ARITHMETIC_POSITIVE_CERTIFICATES.md) | 原实际对象、指定线性系及其核、基点支撑、秩一排除、几何整与几何正规泛关联、完整核纤维和余秩一概形图。正规泛纤维依据 §82 的泛点局部化证明；联合空间奇异集公式不被特化为所有纤维的奇异集。 |
| Stacks Project，[Serre 正规判据，Tag 031S](https://stacks.math.columbia.edu/tag/031S)；[射影态射纤维维数上半连续，Tag 0D4I](https://stacks.math.columbia.edu/tag/0D4I)；[几何正规性的扩底判据，Tag 038O](https://stacks.math.columbia.edu/tag/038O) | Noetherian 环的 $R_1+S_2$ 等价正规；proper 有限型族的纤维维数上半连续；特征零泛参数域为完美域，普通正规性给几何正规性。引理 86.2 另外检查平坦性、局部完全交和非光滑闭集，以取得几何纤维开集。 |
| Stacks Project，[Cartier 嵌入对偶计算，Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)、[其张量版本，Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)；[proper、等维 CM 概形的 Serre 对偶，Tag 0FVZ](https://stacks.math.columbia.edu/tag/0FVZ) | Cartier 法线丛的 $\mathcal E xt^1$ 计算给伴随；对偶应用的 $G$ 光滑、射影、纯维数 $g$。不要求奇异除子光滑。Gorenstein 性也可由正则局部环模非零因子的经典定理得到。 |
| Stacks Project，[射影空间上同调，Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)；[射影丛版本，Tag 01XX](https://stacks.math.columbia.edu/tag/01XX) | 对 $\mathcal O$ 的直接像为底的结构层、高阶直接像为零；作为定理 87.1 证明的中间输入，两次用于旗簇投影，严格给出 (87.9)。因此无需额外的奇异空间消失假设。 |
| Stacks Project，[有限 étale 概形与有限 Galois 集，Tag 0BNE](https://stacks.math.columbia.edu/tag/0BNE) | 原域的八个嵌入及其无序异元对的有限 étale 下降；不把二元子集作用传递性当作单点作用传递性的推论。 |
| Honma–Manabe，*Determinantal Calabi–Yau varieties in Grassmannians and the Givental I-functions*，[arXiv:1810.03685v1，§2.1–2.2](https://arxiv.org/abs/1810.03685v1) | 行列式退化 locus、核关联和 Grassmannian 上典范类条件的既有总体框架。其一般映射的预期余维和光滑性不能替代本卷结构化行族的非空性与正规性证明；其物理模型不作为这里的结论。 |
| Ahmadinezhad–Cheltsov–Park–Shramov，*Double Veronese cones with 28 nodes*，[arXiv:1910.10533v2，§10，印刷页 42–43](https://arxiv.org/abs/1910.10533v2) | 正则 Cayley 八点对应的二次曲面网给 $\operatorname{Gr}(2,4)$ 中一个 $(2,3)$ 三维簇，其二十八个奇点按八点对标记。这是“二十八个二元对标签”的明确文献重叠；本卷是 $\operatorname{Gr}(2,4)$ 上 $\mathcal O_G(4)$ 行列式除子，未把任意统一八行认作正则 Cayley 八点，也未证明两族同构或双有理。 |
| Kapustka–Kapustka，*A cascade of determinantal Calabi–Yau threefolds*，[arXiv:0802.3669v3，Theorem 3.8](https://arxiv.org/abs/0802.3669v3) | 一般 $4\times4$ 线性矩阵的三阶子式三维簇及其到带五十六节点的 $(2,4)$ 完全交的收缩，是不同的一般线性截面族。本卷不从该结果移入节点总数或收缩结论。 |

**剩余数学边界。** 一般开集的非空性是存在定理，不给寻找实际窗口的有效算法。$Z_W$ 的界仅为在 $T_W$ 中余维至少二，不是更强的完整秩分层公式。$N_C$ 只记录强制节点；其外奇异 locus、全部节点数、特殊窗口的退化、整体光滑模型与 crepant 解消均不由本卷判定。平凡对偶层及结构层上同调不被提升为光滑 Calabi–Yau 断言。原乘法二元关系与反典范几何之间的桥是所述数学结论；量子物理、H10 与有效发现能力不由这些结论推出。

## 追加锚（本行以下为增补区）

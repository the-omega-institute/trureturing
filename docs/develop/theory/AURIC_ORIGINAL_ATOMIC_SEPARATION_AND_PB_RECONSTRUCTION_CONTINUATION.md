# AURIC：原原子有限测试分离与同一 PB 的静态重构续卷

**约定（卷间记号）。** “三角卷”指[《配平三角的共同取向与秩一响应续卷》](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)，“单位桥”指[《任意维小窗口单位桥》](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md)，“静态重构卷”指[《任意维静态量子重构》](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)。本卷 1–11 的编号用于本卷条目；跨卷条目以卷名或链接指明。

## 1. 原有限原子测试的分离与完成本质性的区别

**定义 1.1（只在原对象上检验的几何前件）。** 固定 [128.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#128-同一二元关系的完整候选与实际角)–[128.4](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#128-同一二元关系的完整候选与实际角) 的全部原资料，特别是同一个稠密含单位实 Jordan 子代数 $E\subset X$、原 $S=\circ,D:E^2\to E$、准确锥、单位、范数、原评价及全部质量、P2 和完整 PB。另给一个原幂等元集合 $\mathscr P$，满足

$$
p\in E,\qquad p^2=p\ne0,\qquad U_p(E)=\mathbb Rp
\quad(p\in\mathscr P).
\tag{1.1}
$$

$U_p=2L_p^2-L_p$。仅用有限次原 Jordan 运算定义代数理想

$$
\mathcal A=\operatorname{span}_{\mathbb R}
\{L_{a_1}\cdots L_{a_n}p:
 n\ge0,\ a_j\in E,\ p\in\mathscr P\}\subset E.
\tag{1.2}
$$

每个测试只含有限多个原元素和有限次已知 Jordan 运算；$n=0$ 给 $p$ 本身，线性包只取有限和。这里不使用 $D$ 来生成测试。所加的分离原语准确为

$$
\boxed{\quad
x\in E,\quad x\circ r=0\ (r\in\mathcal A)
\quad\Longrightarrow\quad x=0 .\quad}
\tag{1.3}
$$

令 $J=\overline{\operatorname{Id}_X(\mathscr P)}^{\|\cdot\|}$。定理 2.1 将证明 $J=\overline{\mathcal A}$，所以 (1.3) 等价于 $E\cap\operatorname{ann}_X(J)=0$。这只是原对象的分离，不要求完成中的对象满足同一分离。另记明确更强的条件

$$
\operatorname{ann}_X(J)=0.
\tag{1.4}
$$

两个条件都不是信息守恒、共同谱、归一化或一般原 $\Omega$ 已经供应的事实。理想记号 $J$ 不与原全词 $K/J/q$ 中的来源标签作识别。不输入 $D$ 的线性、连续、NN、Jacobi、协变、商下降或完成延拓；不输入全部原有限框架、整个闭理想包含于 $E$、复 Hilbert 空间、特殊性或算子乘法闭合。$X=0$ 时允许空族；反之，空族配合 (1.3) 迫使 $E=0$，稠密性再给 $X=0$。以下空乘积和空直和取零对象。

**定理 1.2（同一旧关系的原域恢复及较强完成分支）。** 在定义 1.1 的原子条件下，存在指标集 $\Lambda$、非零复 Hilbert 空间 $H_\lambda$ 和闭 Jordan 理想 $I_\lambda\lhd X$，使

$$
J=\mathop{\bigoplus}\limits_{\lambda\in\Lambda}^{c_0} I_\lambda,
\qquad j_\lambda:I_\lambda\cong_J K(H_\lambda)_{\rm sa}.
\tag{1.5}
$$

$c_0$ 意指对每个 $\delta>0$，只有有限多个分量的范数至少为 $\delta$，范数取上确界。允许任意指标集及有限维／无限维／不可分 $H_\lambda$；一维空间准确给经典 $\mathbb R$ 因子。每个 $I_\lambda$ 至少含一颗原 $p\in\mathscr P$，但未必本质。选定一次所得 $j_\lambda$ 后，有保单位正收缩 Jordan 表示

$$
\begin{gathered}
\rho_\lambda:X\longrightarrow B(H_\lambda)_{\rm sa},\qquad
\rho_\lambda|_{I_\lambda}=j_\lambda,\qquad
\ker\rho_\lambda=\operatorname{ann}_X(I_\lambda),\\
\rho=(\rho_\lambda)_\lambda:
X\longrightarrow\mathop{\prod}\limits_{\lambda\in\Lambda}^{\ell^\infty}
 B(H_\lambda)_{\rm sa},\qquad
\ker\rho=\mathcal N:=\operatorname{ann}_X(J).
\end{gathered}
\tag{1.6}
$$

对每个 $\dim H_\lambda\ge2$ 的分量，存在唯一固定 $\varepsilon_\lambda\in\{-1,+1\}$，使

$$
\boxed{\quad
\rho_\lambda D(a,b)=
\varepsilon_\lambda\frac{[\rho_\lambda a,\rho_\lambda b]}{2i}
\quad(a,b\in E).\quad}
\tag{1.7}
$$

经典分量的全部原 $D$ 坐标为零。至此的分量结论甚至不使用 (1.3)，亦不先在 $\rho_\lambda(E)$ 或任何商上定义 $D$。

若加 (1.3)，$\rho|_E$ 单射，足以认回同一个旧 $D$ 的实双线性、全部原三输入的 ([128.5](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#128-同一二元关系的完整候选与实际角))、原复化上 $\star=\circ-iD$ 的结合星乘法，以及每个未改变的原评价对任意有限原输入族的完整有向 Gram 正性。原范数仍满足

$$
N(D(a,b))\le N(a)N(b).
\tag{1.8}
$$

此界直接由原 P2 和准确序单位范数取得，有限 Gram 则在原域双线性成立后消费静态重构卷 32.2；两者都不需要所选原子坐标反映原锥。全部原中心、逐块独立符号及每个原内外层 $D$ 调用均保留。

若进一步给 (1.4)，才有这些所选原子坐标对整个完成的忠实、等距与反映正性：

$$
\rho:X\hookrightarrow\prod_\lambda^{\ell^\infty}B(H_\lambda)_{\rm sa},
\quad \|x\|=\sup_\lambda\|\rho_\lambda x\|,
\quad x\ge0\ \Longleftrightarrow\ \rho_\lambda x\ge0\ (\lambda\in\Lambda).
\tag{1.9}
$$

(1.3) 下不主张 (1.9)，甚至不主张这些坐标恢复每个原元素的范数或反映其正性；10.1 给满足完整静态候选的严格区别。证明由 2–10 给出。

## 2. 原原子生成的理想及其真正原核心

**定理 2.1（从原有限理想到环境简单对偶理想）。** 有 $J=\overline{\mathcal A}$，故 (1.3) 等价于 $E\cap\operatorname{ann}_X(J)=0$。每颗 $p\in\mathscr P$ 是 $X$ 的一维投影，即 $U_pX=\mathbb Rp$。$J$ 是简单对偶 JB 代数的 $c_0$ 直和；其各简单分量是 $X$ 的闭 Jordan 理想，并由某颗原 $p$ 生成。对这样的分量 $I$，有

$$
\overline{E\cap I}^{\|\cdot\|}=I,\qquad
U_kX=U_kI\quad(k^2=k\in I).
\tag{2.1}
$$

第二式不声称 $k$ 是原标签；当另外 $k\in E$ 时才调用原角定理。

证明。$\mathcal A$ 是含 $\mathscr P$ 的最小代数 Jordan 理想。其闭包在每个 $L_a$、$a\in E$ 下不变；再对已知连续 Jordan 乘法以原元逼近 $x\in X$，它也在 $L_x$ 下不变。因此它恰好是 $J$。固定 $x$ 的 $L_x$ 连续，故湮灭 $\mathcal A$ 等价于湮灭 $J$，给所述等价。此处所有极限只涉及已知 Jordan 乘法。

$U_p$ 连续，$E$ 稠密而 $\mathbb Rp$ 闭，故 $U_pX=\mathbb Rp$。用 Bunce 的记号，令 $C(X)$ 为 $X$ 中全部一维投影的闭实线性包。[*On compact action in JB-algebras*，Theorem 3(b)(iii)、Lemma 4，页 356–357](https://doi.org/10.1017/S0013091500004429) 给：$C(X)$ 是 $X$ 的闭 Jordan 理想，是对偶 JB 代数，且

$$
C(X)=\mathop{\bigoplus}\limits_{\gamma\in\Gamma}^{c_0} A_\gamma
\tag{2.2}
$$

为简单对偶分量直和。该文 Theorem 3(b)(ii) 还给每个分量元素的范数收敛正交一维投影谱展开。这些是关于 $C(X)$ 的成熟结构，未把任意 $X$ 宣布为对偶代数。这里“对偶 JB”采用 Bunce 页 355 的遗传子代数双湮灭子定义，不指 Banach 对偶空间，不能据此认作 JBW 代数；3.1 中的类型 I JW 包络才具有所需 JBW 结构。

须核对每个 $A_\gamma$ 对环境 $X$ 仍是理想。取 $y\in A_\gamma$、$x\in X$，则 $w=x\circ y\in C(X)$。若 $\nu\ne\gamma$，对 $A_\nu$ 的任意一维投影 $e$，有 $e\circ y=0$，即 $y\in X_0(e)$。Peirce 乘法规则使 $x\circ y$ 没有 $X_2(e)$ 分量，故 $U_ew=0$。若 $w_\nu\ne0$，对它使用上述正交一维投影谱展开，可找到一个非零谱系数及对应 $e$，使 $U_ew_\nu\ne0$，矛盾。因此 $w$ 只有 $\gamma$ 分量，$A_\gamma\lhd X$。

$p\in C(X)$ 的非零坐标只能有一个：若有两个，将其中一个坐标 $p_\gamma$ 单独视作 $C(X)\subset X$ 的元素，则 $U_pp_\gamma=p_\gamma$ 不在 $\mathbb Rp$。所以 $p$ 位于唯一一个 $A_\gamma$。简单性使 $p$ 在 $C(X)$ 中生成整个 $A_\gamma$；环境理想性又使它在 $X$ 中恰好生成该分量。因此 $J$ 正是被 $\mathscr P$ 命中的分量的 $c_0$ 和，记它们为 $I_\lambda$。此步未选择数域。

固定其中一颗 $p\in I_\lambda\cap\mathscr P$。它生成的闭环境理想是下列实线性包的闭包：

$$
\operatorname{span}_{\mathbb R}
\{L_{x_1}\cdots L_{x_n}p:n\ge0,\ x_j\in X\}.
\tag{2.3}
$$

因为这个闭包恰好是含 $p$ 且在全部 $L_x$ 下不变的最小闭子空间。逐个以原 $E$ 元素逼近有限多个 $x_j$，连续 Jordan 乘法使 (2.3) 的每个生成元都可由 $E\cap I_\lambda$ 中的元素范数逼近。这证明第一式 (2.1)，不是一般稠密子空间与任意理想交集的无条件断言。最后，理想性给 $U_kX\subset I$，且 $U_k$ 是其像上的恒等投影，所以 $U_kX=U_kI$。∎

## 3. 用原输入角选择复数类型

**定理 3.1（原子理想的复紧选型）。** 定理 2.1 的每个 $I_\lambda$ 都是 (1.5) 的复紧 Hermitian 理想。选型所用幂等元和角内旧调用全部属于原 $E$。

证明。以下只在本定理证明中消费成熟类型字典：简单对偶 JB 分量或者有限维简单正式实，或者是无限维自旋因子，或者同构于 $K_{\mathbb F}(H)_{\rm sa}$，其中 $\mathbb F=\mathbb R,\mathbb C,\mathbb H$ 且 $\dim_{\mathbb F}H=\infty$。实／四元数算子及伴随按相应 Hilbert 空间理解。先核对该中间分类的来源与紧元对应，随后才用原输入排除非复类型。Bunce Theorem 3(a)，页 356，将简单对偶 JB 列为 Albert 代数、自旋因子和由紧算子组成的简单 JC 代数。有限维部分按单位桥 [122.1](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#122-有限jordan模型的复数域成为准入结论) 所用的成熟有限分类处理。对其余简单紧 JC 代数 $B$，Bunce Theorem 5(iii) 的证明，页 358–359，明确使用其弱算子闭包 $M$ 为类型 I JW 因子。以下说明此处从该包络到紧算子字典的对应，不把包络分类直接套到一般 $X$。

在给出 $B$ 的紧 JC 表示中，任取一维投影 $e\in B$；它是有限秩投影。因 $U_e$ 弱算子连续且 $U_eB=\mathbb Re$，在 $M$ 中仍有 $U_eM=\mathbb Re$。Bunce Theorem 3(b)(ii) 的每个 $B$ 元素的最小投影谱展开，因此也由 $M$ 的最小投影组成。

还需反向对应。记 $B_1(e),M_1(e)$ 为半 Peirce 空间。$B_1(e)$ 范数闭且在 $M_1(e)$ 中弱算子稠密。相对 $e$，这些都是形如

$$
\begin{pmatrix}0&T^*\\T&0\end{pmatrix},
\qquad T:e\mathcal H\longrightarrow(1-e)\mathcal H

$$

的有限列算子；$\dim e\mathcal H<\infty$。其算子范数与有限列的 Hilbert 范数等价，弱算子拓扑正是这个实 Hilbert 空间的弱拓扑。因此闭实线性子空间 $B_1(e)$ 在此拓扑下也闭，得到 $B_1(e)=M_1(e)$。

若 $M$ 的秩为一，则它是一维。秩为二时是自旋因子；取非零半 Peirce 元，其平方是正数倍的 $1_M$，故 $1_M\in B$。它在原紧 JC 表示中为有限秩，因而其支撑空间及 $M$ 都有限维。有限秩 $n\ge3$ 的类型 I 因子由 Hanche-Olsen–Størmer [*Jordan Operator Algebras*，Theorem 5.3.8，页 132](https://hanche.folk.ntnu.no/joa/joa-m.pdf) 分类，亦有限维。这些情形没有留下无限维非自旋的 $B$。

无限秩时才使用该书 Theorem 7.5.11（页 169–170）：其前件是类型 $I_n$ 的 JBW 因子且 $4\le n\le\infty$；这里已支付该前件。结合 §7.5.5、7.5.10 的实／四元数识别，$M$ 同构于 $B_{\mathbb F}(H)_{\rm sa}$，$\mathbb F\in\{\mathbb R,\mathbb C,\mathbb H\}$。相对于上述最小 $e$，$B_1(e)=M_1(e)$ 使所有相应单列及其平方都属于 $B$；平方减去 $e$ 的标量倍，给 $e^\perp$ 上任意射线投影。再用同一单列和实线性组合，得到任意射线投影，故得到全部有限秩自伴元。范数闭性给 $K_{\mathbb F}(H)_{\rm sa}\subset B$。反向包含由前述最小投影谱展开给出：每个 $B$ 元素都是这些有限秩投影的范数极限。因此 $B=K_{\mathbb F}(H)_{\rm sa}$，正是上述实／复／四元数紧算子分支。本论证不含可分性前件；有限列和单个向量的论证适用于任意 Hilbert 维数。

现在在这些已知类型中用原标签选型。若 $I=I_\lambda$ 有限维，(2.1) 和有限维线性闭性给 $I\subset E$，特别其单位 $k$ 是原幂等元。由 $I\lhd X$ 及其单位性，$X_2(k)=I$。单位桥 [119.2](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#119-原二表的幂等角遗传与有限复-hermitian-几何)–[119.3](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#119-原二表的幂等角遗传与有限复-hermitian-几何) 支付同一旧 $D$ 的角闭合、准确锥／范数／全部原限制评价，完整 PB 的每次嵌套调用均在原角中；[121.1](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#121-每个真实自旋角只能是经典角或完整量子比特角)、[122.1](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#122-有限jordan模型的复数域成为准入结论) 的有限选型因而适用。$I$ 简单，只能是一个 $H_n(\mathbb C)$，包含 $n=1$。不是先把分类中央单位借给原 $D$；其原有性来自 (2.1)。

若 $I$ 是无限维自旋因子，选一颗 $p\in I\cap\mathscr P$。它是非平凡最小投影。由 $E\cap I$ 稠密及原 $p$ 的半 Peirce 投影，存在非零原 $z\in E\cap I_1(p)$。自旋乘法给

$$
z^2=c\,1_I,\qquad c>0.
\tag{3.1}
$$

故 $k=z^2/c=1_I\in E$，$X_2(k)=I$。单位桥 [121.1](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#121-每个真实自旋角只能是经典角或完整量子比特角) 对这个真实原单位角要求它为一维、两经典维或 $H_2(\mathbb C)$，与无限维矛盾。这也解释为何不能略去原单位供应直接对完成中的自旋因子调用旧 $D$。

其余无限维类型由上述引用分类及紧元对应给出。只在此分支的结构坐标中，将原 $p$ 写成 $ee^*$，$\|e\|=1$，$e\in H_{\mathbb F}$。$(E\cap I)_1(p)$ 在 $I_1(p)$ 中稠密，故可取非零原元 $z$，其坐标为

$$
z=we^*+ew^*,\qquad w\perp_{\mathbb F}e,\quad w\ne0.
$$

这里只描述这个原元的坐标，不假定任意此类列都原有。准确平方给

$$
z^2=\|w\|^2p+ww^*,\qquad
k=\frac{z^2}{\|w\|^2}=p+\frac{ww^*}{\|w\|^2}\in E,
\qquad X_2(k)=I_2(k)\cong_J H_2(\mathbb F).
\tag{3.2}
$$

这个全实际角是自旋角，其纯向量维数分别为 $2,3,5$。单位桥 [121.1](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#121-每个真实自旋角只能是经典角或完整量子比特角) 对同一个角内旧 $D$ 只允许非经典的三维纯向量支，故 $\mathbb F=\mathbb C$。由此取得 $j_\lambda$ 和复 Hilbert 空间；复数域、完整二级角及特殊性均在此后才成为结论。原实／四元数候选的排除针对它们已证明原有的角，未对不在 $E$ 的投影作旧调用。∎

## 4. 非本质分量的表示、实际核与两层分离

**定理 4.1（原单射性和完成忠实性的准确支付）。** (1.5) 给 (1.6)，并且对 $x\in X,y\in I_\lambda$，

$$
j_\lambda(x\circ y)=\rho_\lambda(x)\circ j_\lambda(y),\qquad
\|\rho_\lambda(x)\|=
\|x+\operatorname{ann}_X(I_\lambda)\|_{X/\operatorname{ann}_X(I_\lambda)}.
\tag{4.1}
$$

在这些固定坐标中，(1.3) 恰好等价于 $\rho|_E$ 单射，(1.4) 恰好等价于 $\rho$ 在 $X$ 上单射；后一条件给 (1.9)。没有从前一个单射性推断后一条件。

证明。固定 $I=I_\lambda,j=j_\lambda,H=H_\lambda$。复用 [168.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#168-由理想有限压缩构造指定表示) 的相容有限压缩构造及其乘法验证，直到其使用本质性的步骤为止。对每个有限维 $L\subset H$，$e_L=j^{-1}(P_L)\in I$，有

$$
A_L(x)=j(U_{e_L}x),\quad
\|A_L(x)\|\le\|x\|,\quad
P_LA_M(x)P_L=A_L(x)\quad(L\subset M).
\tag{4.2}
$$

相容有界 Hermitian 型给唯一 $\rho_\lambda(x)\in B(H)_{\rm sa}$。[168.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#168-由理想有限压缩构造指定表示) 的 ([168.4](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#168-由理想有限压缩构造指定表示))–([168.5](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#168-由理想有限压缩构造指定表示)) 只用理想性、Peirce 平方和 $j$ 在 $I$ 上的忠实性；它们不需要 $\operatorname{ann}_X(I)=0$，给 (4.1) 第一式、$\rho_\lambda(x^2)=\rho_\lambda(x)^2$ 以及保单位、保正、收缩和 $\rho_\lambda|_I=j$。同一构造涵盖有限 $H$，包括一维 $H$，此时可取 $L=H$。这些压缩只在完成上的已知 Jordan 运算中使用，未给旧 $D$ 增加输入。

若 $\rho_\lambda(x)=0$，第一式及 $j$ 单射给 $x\circ I=0$。反之，$x\circ I=0$ 使每个 $U_{e_L}x=0$，故全部有限压缩为零，$\rho_\lambda(x)=0$。因此核恰为实际湮灭子。JB 商定理及同态等距定理（Hanche-Olsen–Størmer，Theorem 3.4.2、Proposition 3.4.3、§3.4.4，印刷页 85）给第二式 (4.1)。

对 $\mu\ne\lambda$，$I_\mu\circ I_\lambda=0$，所以 $\rho_\lambda(I_\mu)=0$。因 $J$ 是这些理想的范数闭和，

$$
\ker\rho=\bigcap_\lambda\operatorname{ann}_X(I_\lambda)
=\operatorname{ann}_X(J)=\mathcal N,
\qquad \ker(\rho|_E)=E\cap\mathcal N.
\tag{4.3}
$$

各表示收缩，故落在有界乘积。$\mathcal N$ 是闭 Jordan 理想，因为它是这些已构造 Jordan 同态的核的交；这也给其准确理想性，不假定它有原中央投影。2.1 现在给两个分离条件各自的单射性等价。$\mathcal N$ 可以非零而 $E\cap\mathcal N=0$；不能因为 $E$ 稠密就令一个闭核与 $E$ 相交稠密，也不能向 (1.3) 输入 $X\setminus E$ 的元素。

只在加 (1.4) 时继续。若全部 $\rho_\lambda(x)\ge0$，在 $X$ 的单生成连续谱演算中取负部 $x_-=\max(-x,0)$。保单位 Jordan 同态保持该谱演算，使全部 $\rho_\lambda(x_-)=0$。此时 $\ker\rho=0$ 才给 $x_-=0$。这证明联合反映正性。将坐标不等式 $-M1\le\rho_\lambda(x)\le M1$ 拉回，其中 $M=\sup_\lambda\|\rho_\lambda(x)\|$，原序单位范数给 $\|x\|\le M$；收缩性给反向界，故 (1.9) 成立。反过来，(1.9) 的忠实性已迫使 $\mathcal N=0$。若只给 (1.3)，这里的 $x_-$ 一般不在 $E$，该拉回步骤没有依据。∎

## 5. 原理想吸收与分量内的实际有限框架

**定理 5.1（一般 JB 理想对同一旧值的吸收）。** 对任一闭 Jordan 理想 $I\lhd X$，仅原 P2 已给

$$
D(E,E\cap I)\subset E\cap I,\qquad
D(E\cap I,E)\subset E\cap I.
\tag{5.1}
$$

这里没有要求 $I\subset E$ 或 $I$ 本质，也没有给输入纤维不变。

证明。消费静态重构卷 71.1 的同一正二表吸收机制，在这里用实 JB 商而非已给 C* 种子坐标。设 $b\in E\cap I,a\in E$，$q_I:X\to X/I$ 是仅针对已知 Jordan 结构的商。Hanche-Olsen–Størmer Theorem 3.4.2 给 $X/I$ 的 JB 结构。[129.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#129-读取同一二表的数学正泛函) 使它的任意正泛函 $\phi$ 拉回原 $E$ 后读取同一个 P2；由于 $q_I(b^2)=0$，零对角预算给

$$
\phi(q_I(D(a,b)))=0.
\tag{5.2}
$$

JB 商的正泛函分离元素，故 $q_I(D(a,b))=0$，即原输出属于 $I$；它本来就属于 $E$。原反对称性给另一槽。$I=X$ 或零商时断言直接成立。$q_I$ 在这里只检验每个实际输出是否落在理想中；没有出现 $D(q_Ia,q_Ib)$，也没有比较两个不同原输入的旧输出。∎

**定理 5.2（一个原子在非本质分量内供应的原向量核）。** 固定一个非经典分量，暂记 $I,j,\rho,H$，并选原 $p\in I\cap\mathscr P$，使 $j(p)=ee^*$、$\|e\|=1$。置

$$
\begin{gathered}
H_e(z)=ze^*+ez^*,\qquad
V=\{z\in e^\perp:j^{-1}(H_e(z))\in E\cap I\},\qquad
H_0=\mathbb Ce\oplus V.
\tag{5.3}
\end{gathered}
$$

则 $H_0$ 是稠密复线性子空间，全部 $\rho(a)$、$a\in E$ 保持 $H_0$。对有限维复 $L\subset H_0$，有真正原投影及全角

$$
e_L=j^{-1}(P_L)\in E\cap I,\qquad
E\cap X_2(e_L)=X_2(e_L)=j^{-1}(B(L)_{\rm sa}).
\tag{5.4}
$$

这些原有限角的同一旧 $D$ 具有一个共同符号 $\varepsilon\in\{-1,+1\}$。

证明。这是 [169.2](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#169-一个原有限角生成稠密不变向量核)、[170.2](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#170-核内有限乘子取向与数学读取) 的原核构造所需接口的非本质版本；逐项核对它们在此成立的理由。若 $0\ne z\in V$，原元 $h=j^{-1}(H_e(z))$ 给

$$
k=h^2/\|z\|^2\in E\cap I,\qquad
j(k)=ee^*+zz^*/\|z\|^2.
\tag{5.5}
$$

由 (2.1)，$X_2(k)=I_2(k)$ 是真实有限复矩阵角。单位桥 [119.3](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#119-原二表的幂等角遗传与有限复-hermitian-几何) 的稠密性与有限维闭性使它全部原有，故 $H_e(iz)$ 也有原提升，$V$ 复线性。又 $j^{-1}(zz^*)=h^2-\|z\|^2p\in E$。式 ([169.3](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#169-一个原有限角生成稠密不变向量核)) 的实线性组合现在在 $I$ 内给每个 $\xi\in H_0$ 的原提升 $j^{-1}(\xi\xi^*)$，有限 Gram–Schmidt 给 (5.4)。密度使用 (2.1)：对任意 $z\perp e$，以 $E\cap I$ 中的元逼近 $j^{-1}(H_e(z))$，施加半 Peirce 投影即给 $V$ 中趋向 $z$ 的向量。

对任意原演员 $a$，记 $A=\rho(a)$、$\beta=\langle e,Ae\rangle$、$w=(1-ee^*)Ae$。真实原元

$$
2a\circ p-2\beta p\in E\cap I
\tag{5.6}
$$

的 $j$ 坐标是 $H_e(w)$，所以 $w\in V$。再令原 $b=U_{u-p}a$，则 $\rho(b)=(1-ee^*)A(1-ee^*)$。对 $z\in V$，$b\circ j^{-1}(H_e(z))\in E\cap I$，其坐标是 $H_e(\rho(b)z)/2$。这正是 [169.2](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#169-一个原有限角生成稠密不变向量核) 的保持性证明，给 $AH_0\subset H_0$；没有以 $\rho$ 在整个 $X$ 上的单射性作推理。

(5.4) 的每个角均由 [119.2](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#119-原二表的幂等角遗传与有限复-hermitian-几何)–[119.3](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#119-原二表的幂等角遗传与有限复-hermitian-几何) 继承同一旧输出及原限制评价，完整 PB 的内外层调用都在原角。[143.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#143-有限原-jb-完成的完整旧关系分类) 给该角完整旧值识别。两个有限框架的和仍在 $H_0$，在共同角中比较非交换秩二子角即使所有符号一致；$\dim H\ge2$ 保证存在这样的原角和非零交换子，符号唯一。有限维 $H$ 时 $H_0=H$；无限维和不可分时只得到稠密的 $H_0$，未给环境全部有限秩标签。∎

**定理 5.3（任意原背景的完整原秩一行）。** 在定理 5.2 的坐标中，对每个单位 $f\in H_0$，令 $P_f=ff^*$、$e_f=j^{-1}(P_f)\in E\cap I$，并令 $K_\varepsilon(A,B)=\varepsilon[A,B]/(2i)$。则

$$
D(te_f,a)=j^{-1}\bigl(tK_\varepsilon(P_f,\rho(a))\bigr)
\quad(t\in\mathbb R,\ a\in E).
\tag{5.7}
$$

右边是有原提升的有限秩元，等式在原 $E\cap I$ 中成立，包含它在别的分量上的精确零值。

证明。置实际旧输出 $d=D(te_f,a)$。5.1 先使 $d\in E\cap I$，这一步消除了非本质表示的核方向，未假定商上的 $D$。[129.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#129-读取同一二表的数学正泛函) 的数学向量预算在正表示 $\rho$ 下给

$$
|\langle\xi,\rho D(x,y)\xi\rangle|^2
\le\|\rho(x)\xi\|^2\|\rho(y)\xi\|^2
-\bigl(\operatorname{Re}\langle\rho(x)\xi,\rho(y)\xi\rangle\bigr)^2
\quad(x,y\in E).
\tag{5.8}
$$

对 $\xi\perp f$，第一平方为零；固定自伴输出极化给

$$
\begin{gathered}
j(d)=\delta P_f+H_f(w),\quad
\delta=\langle f,j(d)f\rangle,\quad
w=(1-P_f)j(d)f,\quad
z=(1-P_f)\rho(a)f,\quad
\beta=\langle f,\rho(a)f\rangle,\quad
c_0=e_f\circ a,\quad
j(c_0)=\beta P_f+H_f(z)/2.
\tag{5.9}
\end{gathered}
$$

5.2 对实际原 $d$ 和 $a$ 都适用，故 $w,z\in H_0$。所以 $e_f,d,c_0$ 全部支撑在实际原角 $e_L$，其中 $L=\operatorname{span}_{\mathbb C}\{f,z,w\}$，$\dim L\le3$；这些原元都在 $I$ 中，$j$ 对它们忠实。

现在准确消费 [171.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#171-三阶外层调用在原核上识别完整秩一行)／静态重构卷 63.1 的同一次三阶外层 PB 计算：在原 ([128.6](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#128-同一二元关系的完整候选与实际角)) 中取 $(a,te_f,0)$，得到

$$
D(te_f-d,tc_0)-D(te_f+d,-tc_0)=2t\,e_f\circ d.
\tag{5.10}
$$

两次外层调用都在刚支付的原全角，由 [143.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#143-有限原-jb-完成的完整旧关系分类) 认回。[171.4](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#171-三阶外层调用在原核上识别完整秩一行) 的已知矩阵计算于是给

$$
2t\delta P_f+tH_f(w)=t^2H_f(i\varepsilon z/2).
\tag{5.11}
$$

$t\ne0$ 时 $\delta=0,w=i\varepsilon tz/2$；$t=0$ 用原零行。由 $j$ 在 $I$ 上单射读回即为 (5.7)。此处只消费既有锁行计算，新增的接口是实际输出先落入 $I$，以及它和演员所生成的三个向量确有原角；没有把单分量完成像中的角公式当作一般原商公式。∎

## 6. 在原标签上提升有限乘子

**定理 6.1（保留全部原核部分的精确提升）。** 固定定理 5.2 的分量。令 $\mathcal E=E\oplus iE$ 为形式复化，只使用它的向量空间、原共轭和原实虚部；此时不赋予未知结合乘法。置

$$
T(Z)=\rho(a)+i\rho(b)\quad(Z=a+ib\in\mathcal E).
\tag{6.1}
$$

$T$ 可以有核。记 $\mathcal F_0$ 为支撑于某个有限 $L\subset H_0$ 的全部有限秩复算子。$j$ 的复化给唯一原提升

$$
\ell:\mathcal F_0\longrightarrow(E\cap I)\oplus i(E\cap I),
\quad T\ell(k)=k,\quad
\ell(k^*)=\ell(k)^*.
\tag{6.2}
$$

对 $A,B\in1+\mathcal F_0$、$Z\in\mathcal E$，定义实际原标签变换

$$
\mathscr L_A Z=Z+\ell((A-1)T(Z)),\qquad
\mathscr R_B Z=Z+\ell(T(Z)(B-1)).
\tag{6.3}
$$

这些变换均有定义，且

$$
\begin{gathered}
T(\mathscr L_A Z)=AT(Z),\quad
T(\mathscr R_B Z)=T(Z)B,\\
\mathscr L_A\mathscr L_B Z=\mathscr L_{AB}Z,\qquad
\mathscr L_A\mathscr R_B Z=\mathscr R_B\mathscr L_A Z
=Z+\ell(AT(Z)B-T(Z)).
\tag{6.4}
\end{gathered}
$$

右乘次序准确为 $\mathscr R_A\mathscr R_B=\mathscr R_{BA}$。其他分量的原坐标不变；这些公式始终在 $\mathcal E$ 内成立，而非仅在 $T(\mathcal E)$ 内成立。特别地，若 $W\in\ker T$，变换对 $Z+W$ 的结果是对 $Z$ 的结果再加同一个 $W$。

证明。对 $Z=a+ib$，$T(Z)$ 和 $T(Z)^*$ 都保持 $H_0$，由 5.2 的全部原演员保持性得到。若 $k=P_LkP_L\in\mathcal F_0$，则 $kT(Z)$ 的实部和虚部支撑在有限空间 $L+T(Z)^*L\subset H_0$，而 $T(Z)k$ 用 $L+T(Z)L$。所以两者均在 $\mathcal F_0$；(5.4) 给其每个自伴部分在 $E\cap I$ 中的唯一提升。这是 [170.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#170-核内有限乘子取向与数学读取) 的有限乘子论证，但提升落在原理想中，不要求 $\rho|_E$ 单射。

$\ell$ 的唯一性仅来自 $j$ 在 $I$ 上的单射，给实虚线性和伴随对应。将 (6.3) 逐次代入，所有修正项都属于同一个原理想复化，故可由 $\ell$ 的线性相加；例如左乘复合的修正是

$$
\ell((B-1)T(Z))+\ell((A-1)BT(Z))
=\ell((AB-1)T(Z)).
\tag{6.5}
$$

这证明实际标签等式，不是从相同表示像倒推相同原标签。其余公式同理。$\rho_\mu(I)=0$、$\mu\ne\lambda$ 给其他分量不变。$W\in\ker T$ 时修正项完全相同，故原 $W$ 从未被删除、另选代表或归零。

令 $\tau Z=iZ^*$，这是实际原实虚部交换。提升还准确满足

$$
\tau\mathscr L_A Z=\mathscr R_{A^*}\tau Z,
\qquad
\tau\mathscr R_A Z=\mathscr L_{A^*}\tau Z.
\tag{6.6}
$$

这些也是对同一原理想修正直接取共轭所得，不要求旧 $D$ 在核纤维上不变。∎

## 7. 非忠实分量中同一 PB 的原标签运输

**定理 7.1（未预付商下降的双侧有限相位不变性）。** 对 $Z=a+ib\in\mathcal E$ 定义有界自伴分量残差

$$
\mathfrak F_\lambda(Z)=
\rho_\lambda D(a,b)-K_{\varepsilon_\lambda}(T(Z)_{\rm Re},T(Z)_{\rm Im}).
\tag{7.1}
$$

此定义的自变量是实际原标签对；不假定残差能下降到 $T(Z)$ 的函数。令 $\mathcal U_0$ 为某个有限 $L\subset H_0$ 之外恒等的全部酉算子。则对所有原 $Z$ 和 $U,V\in\mathcal U_0$，

$$
\mathfrak F_\lambda(\mathscr L_U\mathscr R_V Z)
=\mathfrak F_\lambda(Z).
\tag{7.2}
$$

证明。消费 [172.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#172-现有相位传播的同原域接回)／静态重构卷 64.1 的相位相减机制，支付这里不能由单分量坐标自动提供的实际标签等式。取原 $h=te_f$。5.3 识别任意原 $x,y$ 上的两个内层旧值 $D(h,x),D(h,y)$，且这两值和 $h\circ x,h\circ y$ 全在 $E\cap I$。所以原 PB 的实虚增量不仅具有已知坐标，还分别等于那些坐标在 $I$ 中的唯一原提升。

写 $P=P_f$。按符号令 $\mathscr M_A=\mathscr L_A$（$\varepsilon=-1$）或 $\mathscr M_A=\mathscr R_A$（$\varepsilon=+1$）。由 5.3 的原理想等式和 (6.3)，对 $Z=a+ib$ 有实际标签等式

$$
\mathscr M_{1\pm itP}Z
=\bigl(a\pm D(h,a)\mp h\circ b\bigr)
+i\bigl(b\pm h\circ a\pm D(h,b)\bigr).
$$

右端正是原 ([128.6](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#128-同一二元关系的完整候选与实际角)) 取三输入 $(h,a,b)$ 的两份外层调用。证明此等式时，先逐项识别属于 $I$ 的增量，再加回完全相同的原 $a,b$；没有从两个总标签的相同 $\rho$ 坐标反推其相等。标准比较映射满足同一个算子 PB：$\varepsilon=-1$ 时 $Q_K= T(Z)^*T(Z)$，$\varepsilon=+1$ 时 $Q_K=T(Z)T(Z)^*$。将原 PB 经 $\rho_\lambda$ 读取，再减去这个已知比较恒等式，得到

$$
\begin{cases}
\mathfrak F_\lambda(\mathscr L_{1+itP}Z)
=\mathfrak F_\lambda(\mathscr L_{1-itP}Z),&\varepsilon=-1,\\
\mathfrak F_\lambda(\mathscr R_{1+itP}Z)
=\mathfrak F_\lambda(\mathscr R_{1-itP}Z),&\varepsilon=+1.
\end{cases}
\tag{7.3}
$$

没有展开未知外层 $D$，也没有以相同分量输入替换原调用。

置 $A_t=(1-itP)^{-1}=1+((1-it)^{-1}-1)P$。负号情形把 (7.3) 用于实际 $Z_0=\mathscr L_{A_t}Z$，正号情形用于 $Z_0=\mathscr R_{A_t}Z$。(6.4) 给实际标签恒等式

$$
\mathscr L_{1-itP}Z_0=Z
\quad\text{或}\quad
\mathscr R_{1-itP}Z_0=Z,
\tag{7.4}
$$

并给另一个端点是 Cayley 相位的实际提升，相位为

$$
U_{f,t}=1+\left(\frac{1+it}{1-it}-1\right)P_f.
\tag{7.5}
$$

(7.4) 是修正项在原理想中准确相消的结果，不是 $T$ 单射的结果。若原 $Z$ 含非零的 $\ker T$ 部分，它在两个端点和所有中间标签中一直保留。

有限实 $t$ 给除 $-1$ 外的每个秩一相位；$-1=i\cdot i$ 用两次 $t=1$ 的实际变换得到。对有限 $L\subset H_0$ 用有限酉谱定理，每个 $U\in\mathcal U_0$ 是有限个这类相位的乘积。每个中间标签由 6.1 留在原域，5.3 在其两个实输入上仍适用，故负号给所有左不变性，正号给所有右不变性。没有以稠密相位加未知连续性补全圆周。

最后，原反对称性给

$$
\mathfrak F_\lambda(\tau Z)=-\mathfrak F_\lambda(Z).
\tag{7.6}
$$

用实际标签恒等式 (6.6)，从已得的一侧不变性推得另一侧，再逐次作用即为 (7.2)。因此本运输不经过 $E/(E\cap\ker\rho_\lambda)$ 上的旧映射；原商相容性尚未被使用。∎

## 8. 全部原输入的分量残差消失

**定理 8.1（非本质块的全部旧值识别）。** 对每个非经典分量及每个原 $Z\in\mathcal E$，$\mathfrak F_\lambda(Z)=0$。经典分量的全部原 $D$ 坐标为零。因此 (1.7) 对每一对原输入成立。

证明。这里准确消费 [173.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#173-原核足以执行固定输出的双侧零预算)／[152.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#152-同时对准算子及其伴随使固定残差预算趋零) 的固定输出双侧预算；不是把 [167.2](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#167-指定本质复紧理想与一个原有限投影) 应用于一个未定义旧 $D$ 的商。固定原 $Z$，记 $T=T(Z)$。若 $T=0$，两个原实输入在本分量的表示像都为零，(5.8) 直接使 $\rho_\lambda D(\operatorname{Re}Z,\operatorname{Im}Z)=0$，残差也为零。

设 $T\ne0$、$M=\|T\|$。固定任意单位 $\xi\in H_0$，选单位 $v_n\in H_0$，使

$$
r_n=\|Tv_n\|>0,\quad r_n\longrightarrow M,
\qquad w_n=Tv_n/r_n\in H_0.
\tag{8.1}
$$

存在 $R_n,L_n\in\mathcal U_0$，分别把 $\xi$ 送到 $v_n$、把 $w_n$ 送到 $\xi$；只在至多二维的核内子空间延拓相应一维等距匹配。实际原标签为

$$
Z_n=\mathscr L_{L_n}\mathscr R_{R_n}Z=a_n+ib_n\in\mathcal E,
\quad T(Z_n)=W_n=L_nTR_n,
\quad\mathfrak F_\lambda(Z_n)=\mathfrak F_\lambda(Z).
\tag{8.2}
$$

最后一式由 7.1 在原标签上给出；没有把 $Z_n$ 改成任何别的同像代表。

[173.3](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#173-原核足以执行固定输出的双侧零预算)–[173.4](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#173-原核足以执行固定输出的双侧零预算) 的已知算子估计适用于这个 $T$：若 $A=T^*T$、$\delta_n=\sqrt{M^2-r_n^2}$，则

$$
\begin{gathered}
\|(A-r_n^2)v_n\|^2\le r_n^2(M^2-r_n^2),\\
W_n\xi=r_n\xi,\qquad
\|W_n^*\xi-r_n\xi\|\le\delta_n,\\
\|\rho_\lambda(b_n)\xi\|\le\delta_n/2,
\qquad\|\rho_\lambda(a_n)\xi\|\le M.
\tag{8.3}
\end{gathered}
$$

对这两个真正原输入用 (5.8)，比较交换子的读数也有相同的 Cauchy–Schwarz 界。因此

$$
\begin{aligned}
|\langle\xi,\mathfrak F_\lambda(Z)\xi\rangle|
&=|\langle\xi,\mathfrak F_\lambda(Z_n)\xi\rangle|\\
&\le2\|\rho_\lambda(a_n)\xi\|\,
          \|\rho_\lambda(b_n)\xi\|
\le M\delta_n\longrightarrow0.
\end{aligned}
\tag{8.4}
$$

左边是一个固定有界自伴输出残差的同一读数，故为零。对全部单位 $\xi\in H_0$ 成立；稠密性和固定有界算子的二次型连续性、极化给残差为零。极限仅在已知算子估计和固定输出读取中使用，不要求 $Z_n$ 收敛，不对旧 $D$ 作输入极限。有限维 $H$ 也适用，且此时 $H_0=H$。不可分 $H$ 中只为一个固定 $T$ 选近范数序列，未要求可数稠密核。

若 $H_\lambda$ 一维，$\rho_\lambda(a),\rho_\lambda(b)$ 是实数。它们的实 Gram 行列式恒为零，P2 经这个正表示读取直接给 $\rho_\lambda D(a,b)=0$；不用相位论证。

至此对原任意 $a,b$ 均取得 (1.7)。特别是

$$
\rho_\lambda a=\rho_\lambda a',\quad
\rho_\lambda b=\rho_\lambda b'
\ \Longrightarrow\
\rho_\lambda D(a,b)=\rho_\lambda D(a',b')
\tag{8.5}
$$

现在才成为结论。原输入纤维相容性没有先于识别使用；这只是本原子族条件分支的结论，不结清 [178.2](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#178-固定输入作用的读取纤维)、[185.3](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#185-消费全单位行与尚未支付的纤维桥) 在一般 C* 背景中的输入作用纤维问题。∎

## 9. 原分离传回同一旧代数与每份原质量

**定理 9.1（原双线性、结合星乘法、原 R 与原范数正表）。** 在 (1.3) 下，定理 1.2 的全部原代数结论成立；不要求 $\mathcal N=0$。特别地，$N(D(a,b))\le N(a)N(b)$。对每个 $z\in E\cap Z(X)$，$D(z,a)=0$，且原中央平移中性。不同非经典分量的符号不必一致。

证明。8.1 已在每个分量认回全部原输入的旧值。以第二槽的加法缺陷为例，

$$
\delta=D(a,b+c)-D(a,b)-D(a,c)\in E,
\qquad \rho_\lambda(\delta)=0\quad(\lambda\in\Lambda).
\tag{9.1}
$$

右式只展开已经知道的算子交换子，不先展开原 $D$。4.3 与 (1.3) 给 $\delta\in E\cap\mathcal N=0$。对 $D(a,tb)-tD(a,b)$ 及第一槽的两个缺陷作同一判断，所有这些缺陷仍在原 $E$ 中，得到原 $D$ 的实双线性。这一步只用原域单射性。

原范数界直接复用[静态重构卷 (32.1)–(32.2)](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)，其背景正是 [128.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#128-同一二元关系的完整候选与实际角) 的准确原序单位空间与 P2。具体地，对每个原正评价有

$$
|\alpha D(a,b)|
\le\sqrt{\alpha(a^2)\alpha(b^2)}
\le m_\alpha N(a)N(b),\qquad
N(D(a,b))\le N(a)N(b).
\tag{9.2}
$$

最后一步用原评价决定的序单位范数，不用 $\sup_\lambda\|\rho_\lambda(\cdot)\|$。这个逐点界在双线性之前也成立，但只有现在才给有界双线性映射的唯一完成延拓 $\bar D:X^2\to X$；它不是任何先前原调用的替身。

令 $\mathcal E=E\oplus iE$ 为原形式复化。映射 $\rho_{\mathbb C}(a+ib)=(\rho_\lambda a+i\rho_\lambda b)_\lambda$ 在 $\mathcal E$ 上单射：若每个坐标为零，取其已知算子实虚部，原 $a,b$ 分别落入 $E\cap\mathcal N$。定义原 $\star$ 为 $a\star b=a\circ b-iD(a,b)$ 的复双线性延拓，共轭为星。由原值域闭合，$\star:\mathcal E^2\to\mathcal E$。对自伴原 $a,b$，

$$
\rho_{\lambda,\mathbb C}(a\star b)=
\begin{cases}
\rho_\lambda(a)\rho_\lambda(b),&\varepsilon_\lambda=-1,\\
\rho_\lambda(b)\rho_\lambda(a),&\varepsilon_\lambda=+1.
\end{cases}
\tag{9.3}
$$

经典分量取通常乘法。复双线性使同一式适用于全部 $\mathcal E$。每个坐标的通常／相反乘法都结合且符合星律；原结合子仍在 $\mathcal E$ 中，故原单射性给原 $\star$ 的结合律。$S$ 对称、$D$ 反对称也直接给 $(Z\star W)^*=W^*\star Z^*$。又 (1.7) 使原 $D(u,a)$ 的全部坐标为零，原单射性给 $D(u,a)=0$，所以 $u$ 是同一 $\star$ 的单位。结合律在原自伴三输入上的实部准确为

$$
(a\circ b)\circ c-D(D(a,b),c)
=a\circ(b\circ c)-D(a,D(b,c)).
\tag{9.4}
$$

每个内层旧输出本来就在 $E$，两个外层仍调用同一个原 $D$。异号分量不被转置掉；[162.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#162-混合中央方向为何不能抹掉) 的混合取向与通常乘法闭合的区别继续适用。所构造乘法由指定 $S,D$ 唯一决定，不主张原 Jordan 结构自己排除相反取向。

全部有限原正表准确消费静态重构卷 32.2 中“双线性加 P2”的方向，不用原子坐标反映正性。为明确参数和符号，给定原 $a_1,\ldots,a_m$ 和 $c_r=s_r+it_r$，置

$$
x=\sum_rs_ra_r\in E,\qquad y=\sum_rt_ra_r\in E,
\qquad T_0=x+iy.
$$

已付的双线性、对称性和反对称性给该既有二表合并公式

$$
\begin{aligned}
\sum_{r,s}\bar c_rc_s
\bigl(\alpha(a_r\circ a_s)-i\alpha D(a_r,a_s)\bigr)
&=\alpha\bigl(x^2+y^2+2D(x,y)\bigr)\\
&=\alpha_{\mathbb C}(T_0^*\star T_0)\ge0.
\end{aligned}
\tag{9.5}
$$

不等式正是原 P2 在原对 $(x,y)$、系数 $(1,i)$ 上的值。它对每个未改变的原 $\alpha$ 成立；准确锥还给 $T_0^*\star T_0\in C$。不能改用“全部原子坐标非负”作此推断。一般 $\rho_\lambda(T_0^*\star T_0)$ 确实分别是 $T_\lambda^*T_\lambda$ 或 $T_\lambda T_\lambda^*$，但 (1.3) 没有给这些坐标的锥反射。

因此已有静态重构卷 23.1、6.3 的整个原入口也已逐项支付：其 $E,C,u,N,\mathcal P,S,D$ 是 [128.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#128-同一二元关系的完整候选与实际角) 的同一资料，前三组原关系原样给定，第四组 R 由 (9.4) 得到；或者用已得全部 Gram 给其 $\mathsf P_3$，配合未改变的完整 PB。直接消费其 6.3，得到同一 $X\oplus iX$ 的相容 C* 完成、原锥和原实范数保持，以及原 $\mathcal E$ 的稠密含单位星子代数接口。准确复范数为该卷 (6.5)：

$$
\|x+iy\|_{\star}^2
=\|x^2+y^2+2\bar D(x,y)\|_X\qquad(x,y\in X).
\tag{9.6}
$$

这是已有重构定理在所有前件支付后的应用，不由可能有核的所选原子坐标定义这个范数，也不另行重证动力对应。特别地，同一原范数可以完整保留，而这些原子坐标仍不恢复它。数学完成后的额外忠实表示与 (1.6) 的固定原子表示是不同要求，10.1 中前者存在而后者在完成上有核。

每个原评价仍作用于整个原 $E$，并沿此原范数延续为上述 C* 完成的正泛函，范数为原质量 $m_\alpha$；这是静态重构卷 6.3、7 的既有评价接口。奇异评价不被替换为原子块上的正常态求和。若 $m_\alpha=0$，$|\alpha(a)|\le m_\alpha N(a)$ 直接给恒零；不做除法。零、不等及次归一质量全部保留。

最后，若 $z\in E\cap Z(X)$，对 $I_\lambda$ 的每颗最小投影 $e$，$[L_z,L_e]e=0$ 给 $L_e^2z=L_ez$，故 $U_ez=e\circ z$。置 $A=\rho_\lambda(z)$、$P=j_\lambda(e)$，表示中即 $PAP=(PA+AP)/2$；所以 $A$ 与每个秩一 $P$ 交换，必为该块标量。经典块本来就是标量。由 (1.7)，原 $D(z,a)$ 的全部坐标为零，原单射性给 $D(z,a)=0$；已付双线性再给中央平移中性。在只给 (1.3) 时，不从一般 $z\in X$ 的原子坐标为标量推断它属于 $Z(X)$。若另给 (1.4)，则反向也成立：全部坐标为标量使 $[L_z,L_x]y$ 对任意 $x,y\in X$ 的每个坐标为零，完成单射性给 $[L_z,L_x]y=0$，即 $z\in Z(X)$。不同理想之间没有非零 Peirce 连接，[143.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#143-有限原-jb-完成的完整旧关系分类) 的相交角取向比较只在一个分量内施行；已有 [122.2](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#122-有限jordan模型的复数域成为准入结论)、[162.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#162-混合中央方向为何不能抹掉) 的异号实例继续适用。$X=0$ 的全部等式在零对象中成立，无需正质量态。∎

## 10. 原原子分离严格弱于完成本质性的静态边界

**定理 10.1（保留全部原评价的原子化区别）。** 存在满足 [128.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#128-同一二元关系的完整候选与实际角)–[128.4](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#128-同一二元关系的完整候选与实际角) 和 (1.1)–(1.3) 的非交换、不完备原域，使 $\mathcal N\ne0$，且所选原子坐标既不恢复某个原元素的范数，也不反映某个原元素的正性。该模型的同一旧 $D$ 已满足 1.2 的全部原代数结论。

证明。沿用[静态重构卷 82.1](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md) 中多项式唯一性与完成湮灭子的区别机制，在这里把可见理想改成真正由原最小投影生成的原子理想。紧 Hausdorff 空间取

$$
Y=[0,1]\ \cup\ \{t_n=-1/n:n\ge5\}\subset\mathbb R,
\qquad X=C(Y,M_2(\mathbb C))_{\rm sa}.
\tag{10.1}
$$

各 $t_n$ 为孤立点，唯一聚点 $0$ 已在区间中。令 $\mathcal K_{\rm fin}$ 为支撑在有限多个 $t_n$ 上的全部自伴矩阵函数，令

$$
E=\{P|_Y+k:P\text{ 是自伴矩阵多项式},\ k\in\mathcal K_{\rm fin}\},
\quad u=I_2,
\quad S(a,b)=\tfrac12(ab+ba),
\quad D(a,b)=\tfrac i2(ab-ba).
\tag{10.2}
$$

范数和锥取完整 $Y$ 上的一致范数与逐点正锥，原评价族取 $X$ 的全部有界正实线性泛函在这个同一 $E$ 上的限制。它们分离并准确决定原锥，包含零及任意非负质量倍数，不把评价限制到孤立点。

复矩阵多项式加有限支撑矩阵函数对通常乘法和星闭合，故 (10.2) 的两个原输出确实返回 $E$。Stone–Weierstrass 的成熟多项式逼近定理适用于实紧集 $Y$ 上的坐标函数；逐个矩阵坐标逼近并取自伴部，给 $E$ 在 $X$ 中稠密。$u$、准确序单位范数、Archimedean 性、原相加实三表及其零方向都继承自这个同一函数代数。对 $0\le e\le\theta u$、$0<\theta\le1$，逐点谱演算给 $e^2\le\theta e\le e$，所以原小效果窗口也成立。

对有限原族和复系数，令 $W=\sum_jc_ja_j\in E+iE$。直接使用已知结合乘法的正平方，

$$
\sum_{j,k}\bar c_jc_k
\bigl(\alpha S(a_j,a_k)-i\alpha D(a_j,a_k)\bigr)
=\alpha_{\mathbb C}(W^*W)\ge0.
\tag{10.3}
$$

因此完整 P2 和全部原有限 Gram 成立。对原 $h,a,b$，置 $Z=a+ib$；([128.4](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#128-同一二元关系的完整候选与实际角)) 的两份实际原实虚标签正是 $(1\pm ih)Z$ 的实虚部，而

$$
((1+ih)Z)^*((1+ih)Z)
=Z^*(1+h^2)Z
=((1-ih)Z)^*((1-ih)Z).
\tag{10.4}
$$

故完整 PB 对全部原三输入和每份原评价成立。这是已有静态平方恒等式的中间应用，不以某个较小菜单或一份评价代替原量词。原 $\star$ 正是通常乘法，原 R 与双线性当然保持；模型是非交换的，例如常数 Pauli 标签有非零响应。

令 $p_n$ 在 $t_n$ 处为 $E_{11}$、其余处为零，并取 $\mathscr P=\{p_n:n\ge5\}$。每个 $p_n\in\mathcal K_{\rm fin}\subset E$，且 $U_{p_n}(E)=\mathbb Rp_n$，因此都是原最小投影。它们按 (1.2) 生成的理想准确为

$$
\mathcal A=\mathcal K_{\rm fin},\qquad
J=\overline{\mathcal K_{\rm fin}}
\cong c_0(\{n\ge5\},H_2(\mathbb C)).
\tag{10.5}
$$

为核对第一式，有限次乘法不增加孤立支撑，故 $\mathcal A\subset\mathcal K_{\rm fin}$。反向固定 $n$，用常数自伴矩阵 $H_1=E_{12}+E_{21}$、$H_2=(E_{12}-E_{21})/i$ 作用于 $p_n$；$2L_{H_j}p_n$ 给该点的 $H_j$，而 $2L_{H_1}^2p_n-p_n$ 给该点的 $E_{22}$。连同 $p_n$，它们实张成该点的全部 Hermitian 矩阵，有限求和给反向包含。第二式的一致闭包准确是那些在区间上为零、在 $t_n$ 上趋零的连续函数，因此是所列 $c_0$ 理想。每个闭分量是原 $H_2(\mathbb C)$，其表示 $\rho_n(x)=x(t_n)$ 也由 4.1 的延续和作用式唯一认回；没有另外选择原 $D$ 的商。

若 $x\in E$ 湮灭 $\mathcal A$，用各点的 $E_{11}+E_{22}$ 测试得到 $x(t_n)=0$。写 $x=P+k$，有限支撑外有 $P(t_n)=0$；每个矩阵多项式坐标具有无穷多个不同零点，故 $P=0$。剩余 $k$ 在所有支撑点也为零，所以 $x=0$。这证明 (1.3)。另一方面，

$$
\mathcal N=\{x\in X:x(t_n)=0\ (n\ge5)\}
=\{x\in X:x|_{\{0\}\cup\{t_n\}}=0\}\ne0.
\tag{10.6}
$$

等价来自连续性；它可在 $(0,1]$ 上非零，例如 $x(t)=\max(t,0)I_2$。该函数不属于 $E$，正与已证 $E\cap\mathcal N=0$ 一致。因此 $E$ 是 $X$ 的稠密真子空间，故在原范数下不完备。这个闭不可见理想没有删去原对象或原评价：区间上的全部原正读取始终保留。

最后取真正原多项式标签

$$
a(t)=tI_2,\qquad b(t)=(\tfrac14-t)I_2.
$$

则

$$
N(a)=1,\qquad
\sup_{n\ge5}\|\rho_n(a)\|=\tfrac15,
\qquad \rho_n(b)=(\tfrac14+1/n)I_2\ge0,
\qquad b(1)=-\tfrac34I_2.
\tag{10.7}
$$

故原子坐标收缩了原范数，且原 $b$ 不在原锥中，尽管全部这些坐标为正。(1.4) 蕴涵 (1.3)，本模型证明反向失败，并同时保留原旧代数、原完整范数及所有原评价。它只分开两层几何需求，不反驳同一旧关系的原域恢复，也不将成熟的多项式唯一性／湮灭子机制认作新理论。这里没有构造实际归一化 $\Omega$、原生门、仪器或量子起源的完整来源。∎

## 11. 来源对应与同一量子起源的条件边界

**定义 11.1（成熟供应、既有结论与新增桥梁）。** 本节的数学引文和对应范围如下。

| 供应位置 | 准确用途与未被代付的事项 |
| --- | --- |
| Bunce，*On compact action in JB-algebras*，Proc. Edinburgh Math. Soc. 26，353–360，DOI 10.1017/S0013091500004429；页 355 的一维投影定义，Theorem 3(a)、3(b)(ii)–(iii)、Lemma 4，页 356–357 | 全部完成原子的闭包是对偶 Jordan 理想、简单对偶分解和正交最小投影谱展开。不是整个任意 $X$ 的对偶分类，也不供应原子属于 $E$ 或联合本质性。 |
| 同文 Theorem 5(iii) 的证明，页 358–359；Hanche-Olsen–Størmer，*Jordan Operator Algebras*，Theorem 5.3.8，页 132，§7.5.5、7.5.10–7.5.11，页 167–170 | 简单紧 JC 的类型 I JW 包络和正确秩范围内的实／复／四元数类型。3.1 说明最小投影和紧元的双向对应；7.5.11 不用于一般 JB，不承担秩二或秩三选型。 |
| 同书 §2.6.2、Lemma 2.6.3，页 47–48；Theorem 3.2.4、Corollary 3.2.5，页 79；Propositions 3.3.6、3.3.10，页 83–84；Theorem 3.4.2、Proposition 3.4.3、§3.4.4，页 85 | Peirce 分解／乘法、谱演算、二次表示正性、准确序单位范数、JB 商及同态核／等距性质。JB 商只用于已知 Jordan 运算和单次旧输出的吸收，不预给旧 $D$ 的商。 |
| 单位桥 [119.2](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#119-原二表的幂等角遗传与有限复-hermitian-几何)–[119.3](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#119-原二表的幂等角遗传与有限复-hermitian-几何)、[121.1](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#121-每个真实自旋角只能是经典角或完整量子比特角)、[122.1](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md#122-有限jordan模型的复数域成为准入结论)；三角卷 [143.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#143-有限原-jb-完成的完整旧关系分类) | 全实际原角的闭合与评价限制、原自旋和有限选型、有限角全部旧值识别。3 先产生所需原角，再消费它们；不会由“完成有角”跳到“旧 $D$ 可调用”。 |
| 三角卷 [168–170](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#168-由理想有限压缩构造指定表示)、[171–174](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#171-三阶外层调用在原核上识别完整秩一行)；静态重构卷 63.1、64.1、71.1 | 既有有限压缩构造、原核／有限乘子、三阶锁行、Cayley 相位、反对称换槽和固定输出双侧零预算。5.1 把吸收机制接到实 JB 理想；6–7 在非忠实表示中以唯一理想修正实现每个实际原标签等式。 |
| 静态重构卷 32.1–32.2、23.1、6.3 | 原 P2 的原范数界；双线性加 P2 的全部有限原 Gram；同一原 R 与完整静态 C* 完成接口。9.1 先支付全部前件，再复用其原锥、原范数与原评价结论，不用所选原子坐标的锥反射替代。 |
| 静态重构卷 82.1；本卷 10.1 | 前者给非原子理想上的多项式唯一性与完成不可见理想机制；10.1 将它接到实际原最小投影生成的 $c_0$ 理想，分开 (1.3) 与 (1.4)。只作静态条件边界，不作实际来源实现或历史新颖性主张。 |
| Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，Theorem 1 | 其动力对应预设实线性赋值到有界斜顺序导子及两条对应恒等式；这里不拿它预付原 $D$ 的线性。9.1 的完成接口只通过已核对前件的静态重构卷 23.1、6.3 终端消费。 |
| 静态重构卷 70.1、73.1；三角卷 [167.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#167-指定本质复紧理想与一个原有限投影)–[167.2](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#167-指定本质复紧理想与一个原有限投影)、[178.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#178-固定输入作用的读取纤维)–[179.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#179-读取纤维恰好支付旧关系的自动双线性) | 前者另给忠实乘子嵌入、整个原闭种子及内部识别；[167](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#167-指定本质复紧理想与一个原有限投影) 另给单个本质复紧理想；[178](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#178-固定输入作用的读取纤维) 另给完整 C* 原载体并保留输入作用纤维条件。这里未援用这些不同前件来替代非本质分量识别，也未重证一般纤维条件等价。 |
| 三角卷 [200.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#200-任意原反交换对的算子平方)–[200.2](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#200-任意原反交换对的算子平方)、[204.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#204-两份真实配平接通同一行的特定权重)、[207–215](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#207-同一候选中的原响应圆) | 另给 C* 背景下的原反交换平方饱和、一项指定跨权重等式、同一原响应的整圆和标量平方径向结论；[215.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#215-数学归属边界与完整白话)–[215.2](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#215-数学归属边界与完整白话) 明留一般跨半径与可加性缺口。它们不供应原最小投影或 (1.3)，这里也不拿局部圆代替全原域识别。 |
| 三角卷 [183.2](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#183-一般原域中的单位行与纯态支撑)、[185.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#185-消费全单位行与尚未支付的纤维桥)、[188.2](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#188-无最小投影前件的投影与翻转响应)–[191.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#191-坐标变换共同系数与量子代数消费者) | 前两者已给一般原 JB 域的全单位行及其既有后果，不重列为本节的新贡献。后者在另给 $M_2(N)$、原投影与原翻转的背景中给算子值系数和三轴截面；它不代付一般原 JB 的复类型、共同系数或全部原输入识别。这里由 2–3 先从原子产生真实原角，未把该另给背景当作分类前件。 |
| D5／Blueprint 的 `Quantum/Algebra/UnitBridgeRawGeometry` 与 `Topology/JBAlgebra` | 前者的原连续自旋载体保留 PY／NN 等前件；后者供应单生成 Jordan 幂与闭包。它们不供应这里的原子族、原有限测试分离、非忠实块上的旧 $D$ 下降或全部原输入识别。 |

对偶／类型 I 分类、有限维闭性、有界型表示、Hilbert 极化及有限酉谱定理属于 $\texttt{literature-attested}$ 工具。本节 $\texttt{repo-derived}$ 的承重综合是：原最小角先给生成理想中的稠密原元素，原 Peirce 平方支付排除非复类型所需的实际角；各非本质复紧分量的表示保留其实际核；原吸收使锁行输出落回可忠实读取的单个理想；有限乘子仅作为这个理想中的原修正作用于完整原标签，最后只以原有限测试的分离消除原域中的代数缺陷，原 P2 的界和已付双线性后的有限正表提升保留原范数及每份原质量。完成层忠实性另由 (1.4) 支付；10.1 在真正原子理想上严格分开两者。并未把简单对偶分类或单个本质原子的既有定理单列为本节的新增结果；不作穷尽文献、历史优先权或无条件最小公理主张。

**定义 11.2（原来源、无限与物理接口仍须各自支付）。** 定义 1.1 是同一原实域上的条件原语。实际原 $\Omega$ 是否供应 $\mathscr P\subset E$ 和 (1.3) 的原有限测试分离，仍未证明；不能由信息守恒、共同谱、归一化、抽象完成原子或数学态可分离性推出。原代数恢复不要求单颗原子的理想本质，也不要求全部理想共同没有完成湮灭子。只有对所选原子表示主张整个完成的忠实、等距和锥反射时，才另要求 (1.4)。$J$ 可以是 $X$ 的真理想，$X$ 也未被识别成整个算子乘积；每个分量表示的实际核按 (1.6)、(4.3) 保留。一般无原子、型 II／III 及没有这份原子供应的投影稀少原域，仍是完整目标的缺口，这里没有给这些类的完整候选反模型。

同一原 $\Omega/E/S/D$、锥／单位／范数／原评价与所有原质量、全词 $K/J/q$、父位置与 ready／端口类型、实际准备与完整菜单、共同记录与真正分组遗忘、实际参考及真实条件联合律、复合系统、完整仪器及其环境和全部输出都不更换。原全部合法顺序／自适应／并行历史、每个仍合法未来、失败／拒绝／停止／销毁／泄漏分支、同数两侧和真实逆向返回继续保留原量词。数学角、滤子、表示和相位不生产原生操作、接受叶活动输出、第一合法消费者或新的源未来；原 $q$ 也不被任何数学理想商替换。

完整 CountRead 无穷、非离散记录、正常性与指定前对偶、可数可加及无限联合接口仍须原合同；有限 Gram 不是这些合同。所有原评价可以奇异，不强制成迹类态。原复化的定向结合乘法不等于数学有限时间流保持不完备原域，[164.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#164-原代数闭性并不供应全部有限时间返回) 的边界保留。物理钟、能量／哈密顿量、生成元域、作用量与共同 $\hbar$ 仍没有从局部几何和取向导出。静态重构卷 68.1、78.1 的量子消费者只在各自原实际合同已给处消费，本条件定理不结清完整量子起源目标。

## 追加锚（本行以下为增补区）

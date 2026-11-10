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

## 12. 完整矩阵截面域与原取向的准确前件

**约定 12.1（固定来源及追加范围）。** 本增补接在《原原子有限测试分离与同一 PB 的静态重构续卷》1–11 的追加锚之后。以下简称 OP 为《原多项式零响应与 Cayley 原域边界》，SQ 为《零维紧中心的同一原响应与平方酉轨道闭包分类》，SM 为《任意维静态量子重构》。本增补使用的这些仓内正文及承载卷，均取提交 `39a0505470ea889dd9d4301ad60cd9506a5e8b58`；§21 给出固定链接。它们是本增补的纸面数学前置，不被称为 Lean 核验结果。

**定义 12.2（本增补的完整原域）。** 固定非空紧 Hausdorff 空间 $X$、整数 $n\ge3$ 和局部平凡复 $*$-代数丛 $\mathfrak B\to X$，纤维为 $M_n(\mathbb C)$，过渡为连续的保单位复 $*$-同构。取全部连续截面

$$
M=\Gamma(X,\mathfrak B),\quad E=M_{\rm sa},\quad
u=1,\quad S(a,b)=a\circ b=(ab+ba)/2,
\quad C=\{a\in E:a(x)\ge0\ (x\in X)\},
\quad N(a)=\sup_x\|a(x)\|.
\tag{12.1}
$$

原正实线性评价族 $\mathcal P$ 分离 $E$，并准确决定 $C$：

$$
a\in C\iff \alpha(a)\ge0\ (\alpha\in\mathcal P),\qquad
[\alpha(a)=0\ (\alpha\in\mathcal P)]\Longrightarrow a=0.
\tag{12.2}
$$

全部原质量 $m_\alpha=\alpha(u)$，包括零、不等、次归一及非正常评价，均保留。$D:E^2\to E$ 是同一给定总映射。完整原关系准确采用 OP1.1、80.1 和 SQ51.1：A1/P2 是对全部实际 $a,b$、两种次序和全部原评价的 Hermitian 二表

$$
\begin{pmatrix}
\alpha(a^2)&\alpha(a\circ b)-i\alpha D(a,b)\\
\alpha(b\circ a)-i\alpha D(b,a)&\alpha(b^2)
\end{pmatrix}\succeq0.
\tag{12.3}
$$

A2 是全部相加三表 $(a+b,a,b)$ 及全部排列的实部在整个 $\mathbb R^3$ 上半正定，指定相加向量 $(1,-1,-1)$ 及相应排列准确给零。A3 保留 $u^2=u$ 和同一固定有理 $0<\vartheta\le1$ 上全部 $0\le e\le\vartheta u\Rightarrow e^2\le e$。不预给复三表。

对全部实际 $h,a,b\in E$，定义的始终是同一个旧映射的实际标签

$$
v=D(h,a)-h\circ b,\quad w=h\circ a+D(h,b),\quad
r_\pm=a\pm v,\quad s_\pm=b\pm w.
$$

完整 PB 要求

$$
\alpha(r_+^2+s_+^2+2D(r_+,s_+))
=\alpha(r_-^2+s_-^2+2D(r_-,s_-))
\quad(\alpha\in\mathcal P).
\tag{12.4}
$$

零、重复、任意幅度、背景、缩放、平移和嵌套调用均在量词内。不输入 $D$ 的可加、齐次、输入连续、可测、协变、局部性、商下降或完成延拓。

这是一条明确指定完整截面域的新条件分支，不把承载卷1.1的原最小投影族及有限原子分离当作前件，也不宣称二者等价。图内的纤维秩一投影不等于 $U_p(E)=\mathbb Rp$ 的原最小投影；一般 bump 乘投影甚至不是幂等元。完整性及允许全部连续截面将在每一步真实构造中使用，不能把结论移给任意稠密原子域。

**定义 12.3（只使用已与旧角相容的取向）。** 先消费 SQ31.1–31.4：逐点评价是满 Jordan 商；OP80.2、82.1 在全部实际代表上给各点的共同角符号；同一固定非零旧输出使符号连续并在复 $*$-过渡上相容。所得唯一

$$
Q\in C(X,\{\pm1\})u,\qquad J=iQ,\qquad
K(a,b)=\frac J2[a,b]
\tag{12.5}
$$

满足每个点全部二阶角的旧值识别。此处 $Q$ 必须来自这份给定 $D$，不能任意选向后宣布旧响应同号。复 $*$-过渡保持 $i$ 及交换子，故 $Q$ 是真正全局中央符号；只允许连续的开闭换向，不能对非开连通分支任意赋号。

在一般实 Jordan 丛的已付复类型／相容代数取向分支，也可先按 SQ43–44、63.1 构造 $\mathfrak B_{\sigma_D}$ 再应用本增补；该分支的类型及取向前件须先支付。下面不另证明一般 JB 的这一步。

固定符号对应为 OP80.3 的 $\sigma_x=Q(x)$、$K=Qi[,]/2$。承载卷1.7 使用 $\varepsilon[,]/(2i)$，故若比较同一复坐标，$\varepsilon=-Q$；二者不能同名同号。Pauli 约定 $[v\cdot\tau,w\cdot\tau]=2i(v\times w)\cdot\tau$ 下，本式为 $-Qv\times w$，与 OP102.4 一致。

置

$$
x(W)=\frac{W+W^*}{2},\quad y(W)=-\frac J2(W-W^*),\quad
W=x(W)+Jy(W),\quad
F(W)=D(x(W),y(W))-K(x(W),y(W)).
\tag{12.6}
$$

每个固定 $F(W)$ 是连续自伴截面；不假定 $W\mapsto F(W)$ 连续。符号 $K,J$ 是本段数学比较对象，不替换原全词来源中的同名字母。

## 13. 两份全局内行识别之后才有精确运输

**引理 13.1（全部数学正读取和点上零槽）。** 原 P2 对任意数学正实线性泛函成立。特别地，在任意纤维图、任意向量 $\xi$ 上，若 $A=a(x),B=b(x),d=D(a,b)(x)$，则

$$
|\xi^*d\xi|^2\le\|A\xi\|^2\|B\xi\|^2
 -(\operatorname{Re}\langle A\xi,B\xi\rangle)^2.
\tag{13.1}
$$

若 $a(x)=0$ 或 $b(x)=0$，则这同一实际对的 $D(a,b)(x)=0$。全域 $D(a,0)=D(0,a)=0$，且 $D(a,b)=-D(b,a)$。

证明。直接复用 SQ31.2：先由原二表的 Hermitian 性与评价分离得到反对称性，再以准确锥把每个二表复系数的原二次型送给任意正泛函。点评价后接向量读取即给(13.1)；零对角预算和固定自伴矩阵的极化给零槽。没有把实际输入替换为同点的另一个代表。∎

**引理 13.2（同一原 PB 的全局 Cayley 运输）。** 固定实际 $T\in M$、$r\in E$。令

$$
A=(u-Jr)^{-1}T=X_r+JY_r,\qquad
C_r=(u+Jr)(u-Jr)^{-1}.
\tag{13.2}
$$

若两份实际内行已经在整个 $X$ 满足

$$
D(r,X_r)=K(r,X_r),\qquad D(r,Y_r)=K(r,Y_r),
\tag{13.3}
$$

则 $F(C_rT)=F(T)$，等式也在整个 $X$ 成立。

证明。$r$ 自伴、$J=iQ$ 中央，故 $u-Jr$ 可逆，$C_r$ 酉，所有实虚部属于完整原域。对实际三元组 $(r,X_r,Y_r)$ 用(12.4)。仅展开已识别的两个内值，位移满足

$$
v+Jw=JrA,\qquad
r_\pm+Js_\pm=(u\pm Jr)A.
$$

负端点准确是 $T$，正端点准确是 $C_rT$。原评价分离给两份 $x^2+y^2+2D(x,y)$ 元素相等；两份已知普通正平方都为 $A^*(u+r^2)A$。由于 $W^*W=x(W)^2+y(W)^2+2K(x(W),y(W))$，相减即得结论。这是 SQ32.2 的同一参数应用；没有展开未知外层 $D$。仅有(13.3)在一个点成立不够启动这一步。∎

**引理 13.3（原严格小连接的准确使用）。** 在图 $O$ 内固定普通秩一正交投影 $p$，实连续 $\tau$ 支撑紧含于 $O$，令实际全局演员 $r=Q\tau p$，图外延零。记 $q=u-p$。若在每个活跃点

$$
\|qX_rp\|<2,\qquad\|qY_rp\|<2,
\tag{13.4}
$$

则(13.3)全局成立，因此13.2可用。

证明。逐点用 OP83.1，参数为 $\pi=\operatorname{ev}_x$、$\mu=Q(x)\tau(x)$、$p=ee^*$，连接向量为 $z=qX_r(x)e$ 或 $qY_r(x)e$；其范数正是(13.4)。阈值准确是严格 $2$，不是 $\le2$，也不是别的尺度。定理覆盖任意补角背景、任意实首系数及全部实际代表。非活跃点先用13.1的实际首槽点上零预算，再与 $K$ 的零值比较。于是两份内值在每个点都相等，才应用13.2。∎

活跃点的已知分块公式为

$$
\alpha=(1-i\tau)^{-1},\quad A=(q+\alpha p)T,
\quad qX_rp=\frac{qTp+\bar\alpha qT^*p}{2},
\quad qY_rp=-\frac J2(qTp-\bar\alpha qT^*p).
\tag{13.5}
$$

特别地，若 $\|qTp\|,\|qT^*p\|<1/2$，则任意有限实 $\tau$ 都使两连接严格小于 $1/2<2$，因为 $|\alpha|\le1$。下面用这项双侧余量支付整个过渡圈，而不把输入截成 $hW$。

## 14. 一套固定局部坐标支付全部过渡圈和有限前缀

**引理 14.1（固定方向的小余量与统一有限坐标）。** 固定实际 $W\in M$、基点 $x_0$ 及该纤维的秩一投影 $P$，假设

$$
(u-P)W(x_0)P=(u-P)W(x_0)^*P=0.
\tag{14.1}
$$

令 $G_P=\{V\in U(n):VP=PV\}$。在一个固定图中，对每个 $V\in G_P$，存在保留原输入的合格有限链，从 $W$ 到实际 $W_m$，使

$$
F(W_m)=F(W),\qquad W_m(x_0)=VW(x_0).
\tag{14.2}
$$

可以对全部 $V\in G_P$ 使用同一个图、bump、投影基和有限步数上界；它们不依赖逐步缩小的未知邻域。

证明。置 $M_0=\|W\|$。先在含 $x_0$ 的一个平凡化图中将 $P$ 写成常值矩阵。由固定已知截面的连续性与(14.1)，缩小到开图 $O$，使

$$
\|(u-P)W(x)P\|<1/8,\quad
\|(u-P)W(x)^*P\|<1/8\quad(x\in O).
\tag{14.3}
$$

紧 Hausdorff 正规性给一个固定 $0\le f\le1$，在 $x_0$ 的某邻域为一且 $\operatorname{supp}f\subset O$。以下从未把 $W$ 乘 $f$。

若任意连续 $U(x)\in G_P$，则 $T(x)=U(x)W(x)$ 在 $O$ 内仍满足(14.3)，范数至多 $M_0$。事实上 $U$ 与 $P$、$u-P$ 交换，故两连接分别是原连接左右乘相应分块酉，范数不变。这里不需要 $U$ 在图外存在。

取

$$
\rho=\frac1{32(1+M_0)}.
$$

对任何普通秩一投影 $p$，$\|p-P\|<\rho$，任意上述 $T$ 都满足

$$
\begin{aligned}
\|(u-p)Tp\|&\le\|(u-P)TP\|+2M_0\|p-P\|<1/4,\\
\|(u-p)T^*p\|&<1/4.
\end{aligned}
\tag{14.4}
$$

这一个投影开片实张成 $H_n(\mathbb C)$。若 Hermitian $B$ 的迹配对消去该片，则 $v^*Bv$ 在单位球面的非空开片消失；径向扩张给实开锥，实二次多项式遂恒零，极化得 $B=0$。有限维对偶性允许从该片抽取 $d=n^2$ 个投影 $p_1,\ldots,p_d$ 为实基。

只对已知普通矩阵使用有限维实逆函数定理。令

$$
\Psi(s)=e^{is_dp_d}\cdots e^{is_1p_1},\quad
H_j(s)=e^{is_jp_j}\cdots e^{is_1p_1},\quad H_0=I.
\tag{14.5}
$$

$D\Psi(0):s\mapsto i\sum_js_jp_j$ 是到 $\mathfrak u(n)$ 的实同构。取一个局部逆分支 $s=\ell(g)$，$\ell(I)=0$。缩小其像邻域 $\mathcal V\ni I$，使对每个 $g\in\mathcal V$，

$$
\sum_{j=1}^d|\ell_j(g)|<\eta:=\frac1{8(1+M_0)},
\qquad |\ell_j(g)|<\pi/2.
\tag{14.6}
$$

再固定 $\delta>0$ 使普通酉群中 $\|g-I\|<\delta\Rightarrow g\in\mathcal V$。所有这些选择至此固定，不随目标途中改变。

给定 $V\in G_P\cong U(1)\times U(n-1)$，分块酉谱定理给 Hermitian $H$，满足

$$
HP=PH,\qquad \|H\|\le\pi,\qquad e^{iH}=V.
\tag{14.7}
$$

选固定整数 $L$ 使 $\pi/L<\delta$。对所有 $t\in[0,1]$，

$$
g(t)=e^{itH/L},\qquad \|g(t)-I\|\le\|H\|/L<\delta.
\tag{14.8}
$$

于是整个紧参数区间都在同一个逆分支内。令 $s_j(t)=\ell_j(g(t))$；它们连续，$s_j(0)=0$。在图内定义每组的 $d$ 个全局演员

$$
\tau_j(x)=\tan(s_j(f(x))/2),\qquad
r_j(x)=Q(x)\tau_j(x)p_j,
\tag{14.9}
$$

图外置零。$\tau_j=0$ 于 $f=0$，支撑含于固定的 $\operatorname{supp}f\subset O$，且(14.6)保证每个正切有限。因此这些是实际连续原自伴标签。

第 $k$ 组开始时的实际输入，在图内准确为

$$
T_k(x)=g(f(x))^kW(x),\qquad 0\le k<L,
\tag{14.10}
$$

图外始终为原 $W$。它的左酉因子属于 $G_P$，所以(14.4)同时适用于全部 $k$。第 $j$ 个演员的 Cayley 因子准确是 $e^{is_j(f(x))p_j}$，因为 $Jr_j=i\tau_jp_j$；不受 $Q=\pm1$ 的影响。第 $j$ 个前缀输入为 $H_j(s(f(x)))T_k(x)$。普通相位估计和望远镜展开给

$$
\|H_j(s(f(x)))-I\|\le\sum_{a\le j}|s_a(f(x))|<\eta.
$$

因此每个前缀与组首 $T_k$ 的差，以及其伴随的差，范数都小于 $M_0\eta<1/8$。对全部 $j,a,k$，

$$
\|(u-p_a)H_jT_kp_a\|<1/4+1/8<1/2,\qquad
\|(u-p_a)(H_jT_k)^*p_a\|<1/2.
\tag{14.11}
$$

在任意活跃点，第 $j$ 步以第 $j-1$ 个实际前缀为输入；(13.5)与(14.11)支付其逆 Cayley 实虚部的两个严格阈值。在非活跃点用13.1。因此每一步先取得两份全局内行等式，再用13.2；包括全部 bump 过渡带和每个组内前缀。

一个完整组的左因子准确为 $\Psi(s(f))=g(f)$，故由归纳得到(14.10)的下一组，未积累任何坐标误差。作 $L$ 组，共至多 $Ln^2$ 步，终点在 $x_0$ 为 $g(1)^LW(x_0)=VW(x_0)$，逐步有全局 $F$ 不变性。所有常数和 $L$ 对目标 $V$ 都有效，因(14.7)统一给 $\|H\|\le\pi$。

这是一套已知有限矩阵坐标的统一步长构造，不是“每一步另有一个可不断缩小的邻域”。没有对 $D$ 或轨道映射用 IFT，没有对未知 $F$ 沿路径取极限，也没有用 $fV+(1-f)I$ 冒充酉群嵌入。∎

## 15. 共同左右零方向供应同一原值的有限识别

**定理 15.1（共同零方向点识别）。** 在12.2–12.3的全部前件下，$n\ge3$，对同一实际 $W\in M$ 和任意 $x_0$，若存在单位向量 $e$ 满足

$$
W(x_0)e=W(x_0)^*e=0,
\tag{15.1}
$$

则 $F(W)(x_0)=0$。证明始终保留原 $W$，不调用截断比较。

证明。置 $P=ee^*$。两式给 $W(x_0)=0\oplus B$，相对分解 $\mathbb Ce\oplus e^\perp$；故(14.1)成立。有限矩阵 SVD 给 $V_0\in U(e^\perp)$ 使 $V_0B\ge0$，包括奇异 $B$：若 $B=L_0\Sigma R_0^*$，取 $V_0=R_0L_0^*$。令 $V=1\oplus V_0\in G_P$。14.1给保留原输入的至多 $Ln^2$ 步链，终点 $W_m(x_0)=0\oplus V_0B\ge0$。

这份实际终点有 $y(W_m)(x_0)=0$。13.1只对它自己的实际输入 $x(W_m),y(W_m)$ 给旧输出在该点为零；$K$ 也为零。因此

$$
F(W)(x_0)=F(W_m)(x_0)=0.
\tag{15.2}
$$

第一个等号来自链上每步的全局真实 PB，最后一个来自同一实际终点的零槽。没有以任何另一份同点正截面替代终点。∎

**推论 15.2（有支撑余维的实际外层）。** 若同一实际 $a,b\in E$ 的点像共同支撑在某个真复子空间 $S\subsetneq\mathbb C^n$，则

$$
D(a,b)(x_0)=K(a,b)(x_0).
\tag{15.3}
$$

证明。对 $W=a+Jb$，取单位 $e\in S^\perp$，有 $We=W^*e=0$；15.1和(12.6)即给结论。$S$、$e$ 只需在这一纤维选择；不要求它们形成全局子丛。这个点上旧值结论本身不被拿来启动全局运输，除非先逐点支付所有内行。∎

## 16. 三维实际外层在 n≥4 时锁定任意幅度原秩一行

**定理 16.1（无连接幅度限制的全部实际代表）。** 设 $n\ge4$。任取同一实际 $r,a\in E$ 和 $x_0$，在该点固定普通秩一 $p=ee^*$，若 $r(x_0)=\mu p$，$\mu\in\mathbb R$，则

$$
D(r,a)(x_0)=K(r,a)(x_0)
=\mu H(-iQ(x_0)z/2),
\tag{16.1}
$$

其中 $q=I-p$、$H(v)=ve^*+ev^*$，且

$$
a(x_0)=\beta p+H(z)+B,\quad z\perp e,\quad B=qBq=B^*.
$$

$\|z\|$ 任意，$\beta,B$ 任意，实际 $r,a$ 在其他点也任意；没有预给同点评价下降。

证明。$\mu=0$ 用13.1。以下 $\mu\ne0$，记固定旧输出 $d=D(r,a)(x_0)$。对每个 $\xi\perp e$，首平方读取为零，(13.1)使 $\xi^*d\xi=0$；极化给 $qdq=0$，故

$$
d=\delta p+H(w),\qquad \delta\in\mathbb R,\quad w\perp e.
\tag{16.2}
$$

对真实三元组 $(a,r,0)$ 调用原 PB。反对称和零行使四个真实外层标签准确为

$$
A_+=r-D(r,a),\quad B_+=r\circ a,\qquad
A_-=r+D(r,a),\quad B_-=-r\circ a.
\tag{16.3}
$$

其元素差式为

$$
D(A_+,B_+)-D(A_-,B_-)=2r\circ D(r,a).
\tag{16.4}
$$

在 $x_0$ 记 $C_0=p\circ a(x_0)=\beta p+H(z)/2$。四份点像准确是

$$
(\mu p-d,\ \mu C_0),\qquad
(\mu p+d,\ -\mu C_0).
\tag{16.5}
$$

特别注意 $B_+=r\circ a$ 已含首系数 $\mu$，不能再把真实标签写成 $\mu(r\circ a)$。

这四个矩阵全支撑于同一个

$$
S=\operatorname{span}_{\mathbb C}\{e,w,z\},\qquad \dim_{\mathbb C}S\le3<n.
\tag{16.6}
$$

对两份实际全局复截面 $A_\pm+JB_\pm$，在 $S^\perp$ 取共同零方向，15.1分别识别它们自己的旧外层输出；等价地，用15.2。它们在别处的标签及背景均未改变。因此(16.4)在该点成为已知 $K$ 的准确等式

$$
\begin{aligned}
2\mu p\circ d
&=K(\mu p-d,\mu C_0)-K(\mu p+d,-\mu C_0)\\
&=2\mu^2K(p,C_0)
=\mu^2H(-iQ(x_0)z/2).
\end{aligned}
\tag{16.7}
$$

左边为 $2\mu\delta p+\mu H(w)$。除以非零 $\mu$ 并比较 Peirce 分量，得 $\delta=0$、$w=-iQ(x_0)\mu z/2$，即(16.1)。只展开了已经识别的 $K$，没有对未知 $D$ 拆和或缩放。∎

这里没有重复证明 OP89–101 的三维共享预算，也没有假定其中共同侧面系数饱和。那些有限预算本身仍允许 OP99.1 的等号；OP100.1已经说明其总映射不是完整 PB 模型。本节的新增支付来自完整原截面域中的15.1。$n=3$ 时(16.6)可等于整个纤维，没有正余维可取共同零方向，故该论证不解决三阶一般目标。

## 17. 任意原输入的有限抵达与同一旧表的全域分类

**引理 17.1（任意局部秩一演员的全域支付）。** 设 $n\ge4$。对任意图内连续秩一投影场 $p$、任意实连续函数 $\tau$，$\operatorname{supp}\tau\subset O$，令 $r=Q\tau p$、图外延零。对任意实际当前 $T$，(13.2)的两个实际内值都在整个 $X$ 等于 $K$，不再需要连接阈值。

证明。在每个活跃点分别将16.1用于同一实际 $(r,X_r)$ 和 $(r,Y_r)$；投影可逐点选单位生成向量，不要求连续选向量。所有幅度及全部实际原代表均被覆盖。非活跃点用13.1。全空间逐点相等给两份全局元素等式(13.3)，现在才由13.2得到 $F(C_rT)=F(T)$。∎

**定理 17.2（保留原 W 的至多 2n 步点上正化）。** 对任意实际 $W\in M$、任意 $x_0\in X$，存在至多 $2n$ 个真实局部秩一演员，使实际终点 $W_m$ 满足

$$
F(W_m)=F(W),\qquad W_m(x_0)\ge0.
\tag{17.1}
$$

证明。在 $x_0$ 的一个固定图选 $0\le f\le1$，$f=1$ 于 $x_0$ 邻域，$\operatorname{supp}f\subset O$。对固定普通矩阵 $W(x_0)$ 作 SVD，取普通酉 $V$ 使 $VW(x_0)\ge0$。酉谱定理给互相正交秩一 $p_1,\ldots,p_n$ 和 $\theta_j\in[-\pi,\pi]$，使

$$
V=\prod_{j=1}^ne^{i\theta_jp_j}.
\tag{17.2}
$$

每个相位用两步；各步全局演员在图内取

$$
r_{j,1}=r_{j,2}=Q\tan(\theta_j f/4)p_j,
\tag{17.3}
$$

图外置零。正切参数绝对值至多一，没有 $\theta_j=\pm\pi$ 的无限参数问题。每一步 Cayley 因子准确是 $e^{i\theta_j f p_j/2}$。依次作用于实际此前输入，17.1逐步支付全局运输；两次同方向相位乘积为 $e^{i\theta_j f p_j}$。在 $x_0$ 的总因子正是 $V$，故得(17.1)。图外及整个 bump 过渡带，始终作用于原 $W$ 及其实际前缀；没有生成 $hW$、padding 或 ancilla。∎

**定理 17.3（任意紧底上的给定旧响应分类）。** 在12.2的完整原域上，若 $n\ge4$ 且全部原 A1–A3/P2/PB 成立，则由旧角确定的唯一连续 $Q$ 满足

$$
\boxed{D(a,b)=\frac{iQ}{2}[a,b]\quad(a,b\in E).}
\tag{17.4}
$$

不要求稠密局部开闭点，也不另要求 SQ56.1 的截断比较。

证明。逐个固定原 $W,x_0$，用17.2。实际终点正，13.1的实际点上零槽给 $F(W_m)(x_0)=0$。全局运输遂给 $F(W)(x_0)=0$。量词覆盖全部原输入和全部点，故 $F(W)=0$。取同一实际 $W=a+Jb$ 得(17.4)。输入下降、局部性和线性都在认回旧值之后才成为结论。∎

**推论 17.4（逆向及原截断接头的范围）。** 对12.1的固定复代数丛及任意连续 $Q:X\to\{\pm1\}$，定义的 $K_Q$ 确实满足完整原关系。反向与17.3合取，得到此域中全部合法总映射恰为这些 $K_Q$；相对于给定 $D$，$Q$ 唯一。

证明。直接消费 SQ44.2–44.3、63.2 的逆向：在 $Q=1$ 的开闭部分取通常乘法，在 $Q=-1$ 部分取相反乘法，得 $\star_Q=\circ-iK_Q$。同一 C* 正平方支付全 P2，相加实平方和小效果谱序支付 A2、A3；全部实际 PB 的正反平方相等，不缩小三元组或评价量词。∎

识别之后，任意合法 $h$、$h(x_0)=1$ 都有 $F(hW)(x_0)=F(W)(x_0)=0$。所以 SQ56.1／69.1的存在式接头在本完整 $n\ge4$ 截面域成为结论；不是用它作为证明前件，也没有消去其在 $n=3$、非完整原域或一般 JB 域中的未证边界。SQ54.3排除的是旧小连接认证下某些原输入的首步；17.1用已识别全幅行支付新步骤，因此没有宣称那套旧阈值认证突然处处成功。

## 18. reducing 秩一方向的自然加强

**推论 18.1（任意共同 reducing 线，不限零特征值）。** 在12.2–12.3的原前件下，$n\ge3$，若同一实际 $W$ 在 $x_0$ 有一条 reducing 秩一线，即

$$
W(x_0)e=\lambda e,\qquad W(x_0)^*e=\bar\lambda e,
\quad\|e\|=1,\quad\lambda\in\mathbb C,
\tag{18.1}
$$

则 $F(W)(x_0)=0$。只给 $We=\lambda e$ 的单侧特征线不在此结论内。

证明。相对 $P=ee^*$，$W(x_0)=\lambda\oplus B$，满足14.1的两份零连接。取 $V=\zeta\oplus V_0\in G_P$，其中 $\zeta\lambda=|\lambda|$，$\lambda=0$ 时取 $\zeta=1$；$V_0B\ge0$ 由有限 SVD 取得。14.1适用于这个完整 $G_P$，给同一原输入的有限链至实际点上正终点。最后按15.1的同一零槽结算即可。这里的证明只扩充可取的终点块相位，没有使用17.3，也没有借该加强解决三阶一般外层。∎

## 19. 已付前件后的原静态接口及全部质量

**推论 19.1（原双线性、R、全有限 Gram 与同一 C* 接口）。** 在17.3前件下，保持同一 $E,C,u,N,\mathcal P,S,D$，有原实双线性、原换括号 R、全部有限原有向复 Gram 正性及忠实保锥等距 C* 静态表示。复乘法由同一个旧 $S-iD$ 给出。

证明及消费对应。逐点已识别的 $K$ 实双线性，点评价分离截面，故同一旧 $D$ 实双线性。此后按以下顺序直接消费 SM 的既有接口，不重证其消费者：

| 固定来源 | 本域准确参数及先行支付 |
| --- | --- |
| SM32.1–32.2 | 原环境的 JB 完成为同一完整 $E$；准确锥／单位／范数／评价是12.1–12.3的原资料。P2给 $N(D(a,b))\le N(a)N(b)$；17.3给同一旧 $D$ 双线性，故32.2的“双线性加P2”方向给全部有限 Gram 及 P3。 |
| SM23.1 | 同一 $S,D$、全部原 A1–A3及P2为12.2；完整 PB仍为12.4；P3由上一行已付。因此其 P3+PB 方向给原 R 和原复化的结合乘法。 |
| SM6.3 | 上述同一原 R 已付，原 $S,D$ 闭合于完整 $E$，其原锥、单位、实范数不变；消费相容 C* 接口。本域 $E$ 完备，故自伴部恰为 $E$，无需增加其他原元素。 |
| SQ48.2及SM68.1／78.1所列消费者 | 只复用其已经支付静态前置后的条件推论；不借用这些来源不同分支的原子／理想前件，不宣称12.2满足其62.1或70.1。其余实际来源按§20全文合取。 |

为明确输出符号，这些既有接口给

$$
(a\circ b)\circ c-D(D(a,b),c)
=a\circ(b\circ c)-D(a,D(b,c)),
\tag{19.1}
$$

以及对任意有限原 $a_j$、任意复 $c_j$、每份未改变的原评价 $\alpha$，

$$
\sum_{j,k}\bar c_jc_k
\{\alpha(a_j\circ a_k)-i\alpha D(a_j,a_k)\}\ge0.
\tag{19.2}
$$

这里平方合并用原 $x=\sum\operatorname{Re}(c_j)a_j$、$y=\sum\operatorname{Im}(c_j)a_j$，正性是原 P2 在 $(x,y)$ 的值；不把点评价当成全部原准备。

$\star_Q$ 在 $Q=1$ 处为普通积，在 $Q=-1$ 处为相反积，故同一原 $D=i[, ]_{\star_Q}/2$。SM6.3的相容复范数为

$$
\|a+ib\|_{\star_Q}^2=\|a^2+b^2+2D(a,b)\|,
\tag{19.3}
$$

与相应截面 C* 范数一致。数学辅助 $W=a+Jb$ 与这里的形式复化 $a+ib$ 要按12.6对应，不暗换负向区域的乘法。

每个原正评价仍有范数 $m_\alpha$。按 SQ48.2的既有 GNS 直和，可取忠实保单位保锥等距表示 $\Pi$，并为每份原评价取向量 $\xi_\alpha$，使

$$
\alpha(a)=\langle\xi_\alpha,\Pi(a)\xi_\alpha\rangle,
\qquad\|\xi_\alpha\|^2=m_\alpha.
\tag{19.4}
$$

零质量取零向量；不等和次归一质量不被改写。数学正泛函可奇异；表示像不必是全 $B(H)$，也不赋予指定原全词核新的身份。Jacobi、Jordan 导子律及有界数学内导子只作为已识别结合乘法的既有消费者。∎

## 20. 七项实际来源的全文合同及同响应条件接回

**定义 20.1（全文合取，不以本节展开替代）。** 记 $\mathcal C_{47}^{\rm fix}(\Omega;S,D)$ 为固定提交 SQ47.1–47.13全部正文、合同、公式、量词，以及其中逐项纳入的固定上游全文之严格合取；该定义包含 SQ47.2的原根／静默分支、47.3的其他静态分支，绝不把它们改成新的 $n\ge4$ 分支。其已指定上游版本身份也作为合同原文保留；本增补的承重读取入口始终是固定提交的 SQ47。SQ64.1及69.2关于全文合取的规则原样保留。

只把被消费的静态入口接成12.2及17.3识别的同一旧 $S,D,\star_Q$。以下七项展开与该全文同时合取，不能代替全文或削弱任何“全部”“每个所需有限深度”“每个正精度”。这正是 SQ48.3及 SM68.1、78.1中静态输入已付后所调用的原来源，而不是用新域重证那些消费者。

共同身份始终为同一 $\Omega/\mathrm{native}$、全词共同 $K/J/q$、跨评价配对、parent／ready、合法控制、旗标、原程序和比较权、整个环境、所有原质量和每个中间切口。相同矩阵、点像、当前读数不合并不同程序、历史、输出、原 $q$ 零集、AC方向或未来权限；未定义请求不补零。中心、经典、不等维、无轴、零和静默分支仍在各自原合法域，不被本固定秩模型删除。

**合同 20.2（① Hilbert、可观测量与实际相干准备）。** §19只给数学表示。另须 SQ47.4全文的原具名可取得标签、native、指定共同跨评价核 $K_{\rm nat}$、原总映射 $\mathsf J_a$、全部原词、parent／ready、控制及实际相干准备。准确保持

$$
\begin{aligned}
K_{\rm nat}(\xi_\alpha,\mathsf J_a\xi_\alpha)&=\alpha(a),\\
K_{\rm nat}(\mathsf J_a z,\mathsf J_b w)
&=K_{\rm nat}(z,\mathsf J_{a\circ b}w)
-iK_{\rm nat}(z,\mathsf J_{D(a,b)}w),\\
V_{\rm nat}&=\operatorname{span}_{\mathbb C}
\{\mathsf J_{a_1}\cdots\mathsf J_{a_k}\xi_\alpha:k\ge0\},\\
K_{\rm nat}(\xi_\alpha,\xi_\alpha)&\le m_\alpha,\qquad
K_{\rm nat}(\mathsf J_a\xi_\alpha,
 \mathsf J_c(\mathsf J_a\xi_\alpha))\ge0\quad(c\in C).
\end{aligned}
\tag{20.1}
$$

各量词及先按原总映射实际复合、再取任意有限复线性包的次序不变，空词和全部指定跨评价配对包括在内。不预给原 $\mathsf J_a$ 线性、$\mathsf J_0=0$ 或 $\mathsf J_u=I$，不以逐评价 GNS 核替换共同核。不推出全 $B(H)$ 可取得像、任意向量可准备或免费控制。

**合同 20.3（② 原态、效果、Born与全部菜单质量）。** SQ47.6全文保持原准备、原事件／接受绑定、原读序、准确效果 $[0,u]$、完整实际菜单、共同根、mark、互探 $\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定处处有限强度及适用有限维／最小可见／实尺度条件。原独立抽签、完整坐标分区、每条所用平衡行、每个原目标及菜单覆盖、全部P9分支各自独立 $W_e$、AS/EC、菜单外OB、忠实二维到三维全质量适配器、非零一维块、固定支持全质量及每个中间切口不变。同矩阵不同原字分别覆盖，事件依原 $g^*$、原 $d_s^*$、同一共同根的物理次序合法接续。

两只独立九叶彩票 $(6,2,0)/9$、$(4,4,0)/9$、各自第九空程序、十六拒绝叶及相干 $I_3/3$ 返回保留细记录和类型，不把相干返回细测成三个经典结果。只有实际完整菜单 $\sum e_j=u$ 且 $m_\alpha>0$，才取 $p_\alpha(j)=\alpha(e_j)/m_\alpha$；角菜单另需 $\sum e_j=p$、原条件化身份及 $\alpha(p)>0$。零、不等、次归一、中心权、经典和静默质量保留未归一读数，条件更新另需严格正输出质量。密度／迹类公式只用于已付物理绑定的合格有限全矩阵域或正常表示、指定前对偶及收敛齐备的域；一般正泛函不自动给全局密度矩阵。

**合同 20.4（③ 真正相关共同来源与张量）。** SQ47.7全文保持同一个实际非零有序联合、全词同一核和交叉零、同一旧局部乘法、忠实同向交换的局部全矩阵腿、共同生成、评价分离、所需重数、实际乘积／复制、全部真正相关输入及每层递归同源参考。每个实际非零中央对都须有其共同支持、生成和全部相关输入；经典、不等维及静默块不删。两腿在同一个非零共同实现中忠实同向交换且共同生成，才由既有消费者识别 $M_d\otimes M_r$；具体表示消去重数还须原条件。分别可达、边缘相同、共同符号或数学辅助乘积都不生产共同来源。

**合同 20.5（④ typed CP、Kraus及整台递归参考）。** SQ47.8全文要求每条实际细箭头的未归一回溯

$$
\alpha_{A_0}(\beta_r b)=\alpha_{B_0}^{\,r}(b),
\tag{20.2}
$$

并保全部合法 typed 前接、真实后上下文、反变合法复合、typed分区、全质量运输、全未来自然性及原箭头商下降。正次单位延拓不自动为CP；全槽同标签比较路线与实际递归参考路线分别保留各自全部前件。

递归规则类包含整台系统、整个环境、全部成功／失败／细记录／输入输出port／post-port及每份完整输出的每个仍合法未来，也包含真遗忘、实际返回和合法复合。两端系统腿及 $M_2$ 腿忠实、同向、交换，共用真支持 $p$，$i(1)=j(I_2)=p$；三个实际参考投影与 $I_2$ 实张成 $H_2$。全部相关正输入和决定整锥的全部联合评价上保持

$$
\beta_{r^+}i_B=i_A\beta_r,\qquad
0\le\beta_{r^+}(j_B(q))\le j_A(q)
\quad(q=q_t,I_2-q_t),
\tag{20.3}
$$

其中支持内补为 $p-j(q_t)$，不换环境单位补，不强求两腿生成环境。每条根箭头每个所需有限长度都有完整实际链、忠实累计嵌入及准确交织和真支持运输

$$
\beta_kM_B^k=M_A^k(\beta_0\otimes\operatorname{id}_{2^k}),\qquad
P_A^{k+1}=i_{A,k}(P_A^k)\le p_{A,k+1}.
\tag{20.4}
$$

每个正精度路线保持精确根身份、全部支持／事件／输入／后口及每个所需有限深度；固定正误差不足。每个有限长度实际链不等于免费无限链，根代码形式参考不足。已付九号读口及有限返回刚性按原范围复用，返回复合CP不推因子CP。Kraus式仍限原合格矩阵域或正常物理表示、前对偶、分解和收敛齐备的域。

**合同 20.6（⑤ 完整仪器、TP、更新及 Lüders）。** SQ47.11全文保持整台仪器的全部原输入运输、完整typed菜单、接受端、环境、全部成功／失败／细记录／port／post-port及其全部合法未来，连同真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词及接受条件。数学正夹心不生产这些词。逐支CP后，整个原测试的真实完整单位分区

$$
\sum_r\beta_r(u_{B_r})=u_{A_0}
\tag{20.5}
$$

才给TP；异类型输出不免费成为物理直和。同一完整输出的投影效果、全部像内射线保持及完整校准另付后，才使用Lüders消费者；效果、概率、统计重复或只保支撑不足。只归一严格正输出质量，零和失败分支的记录、原类型和合法未来保留。密度、迹类、Kraus及迹式守20.5所述准确域；数学Kraus指标不等于原P9细记录或环境输出。

**合同 20.7（⑥ 全历史、真遗忘、真实双向返回与CountRead）。** SQ47.12全文保持全部合法顺序／自适应／并行历史、整个环境、参考、细记录和泄漏、停止／拒绝／销毁、真正分组遗忘、同数两侧及同数逆向真实返回、每份完整输出的每个仍合法未来。粗事件只沿实际分组相加，丢档案不等于真遗忘；程序、读序、原 $q$ 零集和AC方向不合并。

CountRead绑定读后同一完整活动输入及全未来Return；活动ready、接受叶活动输出、第一合法消费者、具名分析词到完整菜单和接受端均需原生producer。读后分母、查询、细地址、失败及终端类型不变为旧ready。负提升两条活路的分别控制及相干聚合分别支付，数学负号和数值相消不构造返回。精确正生成 $B_{\rm src}$ 与闭正生成 $B_{{\rm src},\rm cl}$ 不混；原彩票、拒绝叶和相干返回保记录及类型。初始读取／有限树／被动混合解码仍守平稳、真实同源和同初始版本边界，初始取得不代替后续全未来返回。无限历史、无限／非离散记录、可数可加、物理正常性、指定前对偶及收敛各需原扩展来源。

**合同 20.8（⑦ 物理钟、能量及共同正作用量）。** SQ47.13全文保持同一旧全域乘法、原域保持、真实相位／门序列、同一实际过程内连续可逆CPTP一参数群及实际逆、物理钟及单位、所需强连续酉实现、生成元域、Hamiltonian能量解释、共同仪器及同一正 $\hbar$。原 $\sigma,t_0,d$、固定域、resolvent与 $3s+r\le1$ 预算保持原设备和量纲，不能改名为取向、基点或有限步数。齐备后才在原表示及相应可微域使用

$$
U(t)=e_{\star_Q}^{-itH/\hbar},\qquad
i\hbar\dot\rho=[H,\rho]_{\star_Q},\qquad
\dot b=2D(H,b)/\hbar.
\tag{20.6}
$$

向量方程限自伴生成元域，密度微分限适用迹类可微域。有界数学内导子和已知矩阵指数不供应无界生成元、钟、能量、实际控制、真实逆或跨设备共同作用量。

**定理 20.9（同一完整条件候选的七项消费者）。** 在12.2且 $n\ge4$ 的域中，完整候选为全部原 A1–A3/P2/PB 加 $\mathcal C_{47}^{\rm fix}(\Omega;S,D)$。它准确等价于：存在相对于给定 $D$ 唯一的连续 $Q$，使 $D=K_Q$ 且同一 $\mathcal C_{47}^{\rm fix}(\Omega;S,K_Q)$ 成立。各项实际合同确实成立处，SQ48.3及SM68.1、78.1所列七项原条件结论按其全部原量词、质量、表示和定义域成立。

证明。正向用17.3，逆向用17.4；来源谓词始终约束同一个旧响应。§19已逐项支付这些既有消费者所需的静态输入，其余充分前件严格为本节全文合取，故只作原位应用。不重证七路消费者，不声称数学存在能生产任何未给的实际来源。∎

## 21. 来源对应、未决边界及完整白话

**定义 21.1（固定承重来源）。** 下表所有仓内链接都指向同一固定提交。

| 来源 | 准确用途与边界 |
| --- | --- |
| [OP](https://github.com/the-omega-institute/trureturing/blob/39a0505470ea889dd9d4301ad60cd9506a5e8b58/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md) 1、80–85 | 原条件、满商全部实际二阶角、共同符号、严格 $\|z\|<2$ 秩一小行和准确实际外层。85保留一般原像目标，不由单点同像推出旧值相等。 |
| 同一OP 89–101、102–108 | 三维共享预算及其局部等号／完整PB失败的区分；秩三 Euclidean／二阶复矩阵纤维的自动取向范围。这里不把Bloch实三维当成 $M_3$ 全分类。 |
| [SQ](https://github.com/the-omega-institute/trureturing/blob/39a0505470ea889dd9d4301ad60cd9506a5e8b58/docs/develop/theory/AURIC_ZERO_DIMENSIONAL_CENTER_SQUARE_ORBIT_RECONSTRUCTION.md) 31–32、43–44、51–56 | 完整截面、正读取、满点评价、旧角符号拼接、同一全局PB-Cayley运输、旧阈值反例、$hW$有限链及56.1未付接头。14–17保留原W，未偷用截断比较。 |
| 同一SQ 47–48、64、69 | 七路全文来源合取、已付静态接口及各项原条件消费者；一般三阶及非完整原域接头仍保留。 |
| [承载卷](https://github.com/the-omega-institute/trureturing/blob/39a0505470ea889dd9d4301ad60cd9506a5e8b58/docs/develop/theory/AURIC_ORIGINAL_ATOMIC_SEPARATION_AND_PB_RECONSTRUCTION_CONTINUATION.md) 1–11 | 原最小投影／原子分离的另一条件分支及符号约定。本增补不以它的原角供应代替完整截面域中的实际代表支付。 |
| [SM](https://github.com/the-omega-institute/trureturing/blob/39a0505470ea889dd9d4301ad60cd9506a5e8b58/docs/develop/theory/AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md) 32.1–32.2、23.1、6.3、68.1、78.1 | 原范数界、已付双线性后的全有限Gram、P3+PB到R及同一C*接口；七项实际消费者不从静态表示单独取得。 |

紧Hausdorff正规性／Urysohn截断、有限维实逆函数定理、Hermitian二次型极化、有限酉谱定理与SVD是成熟数学工具；投影开片的张成证明已写在14.1。SQ55.1使用的也是这些有限矩阵工具，但其输入是 $hW$；这里14.3–14.11的统一双侧余量和 $G_P$ 终点接法支付保留原W的新接口，不能用旧截断证明省略它。

Alfsen–Shultz，*Orientation in operator algebras*，PNAS 95(12), 6596–6601，DOI [10.1073/pnas.95.12.6596](https://doi.org/10.1073/pnas.95.12.6596)，其动力对应Theorem 1预设到有界斜序导子的线性赋值。此成熟取向背景不能预付本增补未知 $D$ 的线性；这里只在§19前件支付后复用已有静态接口。不主张文献穷尽、历史优先权或外部开放问题解决。

本增补的承重综合归为纸面 $\texttt{repo-derived}$：小连接全部原像 → reducing线附近同一有限坐标及全过渡带支付 → 共同零方向旧值识别 → 三维真实PB外层在 $n\ge4$ 有共同零方向 → 全幅原秩一行 → 至多 $2n$ 步保留原输入的点上正化 → 给定旧D的全部值。没有改变独立原 A1–A3/P2/PB，也没有把候选结论放进假设。

**边界 21.2（准确剩余问题）。** $n=3$ 时共同零方向及18.1的reducing线结论成立，但16.6可能占满整个纤维，本证明未得任意幅度原秩一行或三阶全旧值分类。没有构造完整PB的三阶反模型，也不从缺证明推出不可能。一般有限商原像目标OP85.1、任意稠密不完整原域、一般JB／type II或III、混合退化层及非局部平凡域，均未由本增补结清；本证明没有为这些域逐一供应所需的有限矩阵坐标、完整实际演员及支撑余维接线。既有不同前件下已成结论仍照其原范围成立。

底空间任意紧Hausdorff，不需要可度量、局部连通、全局矩阵单位或全局Hilbert向量丛；但局部平凡、完整 $M_n$ 截面及准确原评价是实质前件。点上可选酉不推出全局酉轨道闭包相同，同Gram的全局拓扑障碍不被逐点分类删除。若允许空底空间及单位为零，则另取零代数、唯一零响应，全部式为空断言，不作正质量归一。

全文为独立作者的定义、条件定理与纸面证明；不是评审票，不具有Lean／kernel核验、摄入或冻结状态，不认证物理producer、完整量子起源、钟或共同正 $\hbar$。

**完整白话 21.3（同一张旧比较表怎样被认回）。** 原候选是一张同一世界的两两有向比较表，还要求相加三角、单位小窗口和任意三个实际对象的正反配平。交换比较端点可反号；规定等价的接法必须一致，这不等于实际仪器的先后次序可以交换。已经知道的是：任取一条纤维射线，即使另一输入带着任意背景，只要连向这条线的幅度严格小于二，旧表在这一行就必须等于原角已经选定方向的标准面积。

困难在远近过渡。只在一个点把矩阵转好，不足以调用一条全局配平；局部转动从有到无的整圈也必须合法。共同左右零方向提供了这份余量：在这一方向附近，输入及伴随的两份连接都小。选出有限多个靠近该方向的秩一投影，它们仍能张成全部有限矩阵方向。每组完整操作的终点固定这条零线；组内每个前缀又被同一小参数界控制。截断函数只调节操作角度，从未剪掉原输入。于是过渡圈、内部步骤和下一组的起点同时得到支付；一个固定有限步长覆盖全部目标，最终把同一份原输入在指定点送到正矩阵。每一步先在全空间认出两份真实内行，才调用原PB；最后用同一实际终点的零槽认回最初旧值。

随后再看原秩一行的一次真实配平。它生成的两份外层比较只占据由原射线、原连接和未知输出连接张成的至多复三维空间。纤维阶数至少四时，总有一条共同零方向可用。刚才的结果认回两份外层的旧答案，原PB便把最初那一行的方向、幅度和背景余量全部锁定，不再受小连接阈值限制。三阶时可能没有多余方向，所以不能沿这一步宣布三阶已经解决。

全幅秩一行一旦认回，任意局部相位的两份实际内行都可逐点支付成全局等式。任意原输入在任意指定点只需至多两倍矩阵阶数的秩一相位步，就能到正终点；因此整张给定旧表被认回。双线性、原换括号、全部有限正表和同一复乘法随后才成为结论。这里不再需要先剪成 $hW$ 再假设剪前剪后答案相同；在这个完整且阶数至少四的截面域中，那份比较由最终公式反过来成立。一般稠密域、三阶及一般JB问题仍不能借此改换目标。

这种简化减少的是指定模型中旧表可任意选择的自由度和额外截断比较前件，没有减少原关系或实际来源。数学Hilbert表示不造实际相干准备；Born公式还要原事件、完整菜单和全部质量；张量还要同一个真正相关共同实现；CP、仪器与更新还要整台环境、所有成功失败和每份输出的全部未来；历史和CountRead还要原生活动接头、真遗忘及真实双向返回；物理动力还要钟、强连续实现、生成元域、能量和共同正作用量。七路全文合同一直约束同一原世界，有限纸面运输不能替它们生产设备或物理来源。

## 追加锚（本行以下为增补区）

## 22. 三阶完整原域、同一旧响应与校准取向

**约定 22.1（固定正文及记号）。** 本增补接续承载卷第12–21节，从22起编号，不改写此前正文。AH、OP、SQ、AQ、CO分别指文末固定链接的承载卷、《原多项式零响应与 Cayley 原域边界》、《零维紧中心的同一原响应与平方酉轨道闭包分类》、《任意维静态量子重构》及《二元比较、操作顺序与正性条件的边界》，读取版本统一为 `2addd6f369b7387226c2b0cc984623dd3efe40a1`。AH12.1、21.1规定的 `39a0505470ea889dd9d4301ad60cd9506a5e8b58` 上游身份，以及SQ47.1规定的各层固定来源身份，仍按其原文保留。下面是纸面条件定理，不赋予形式核验或物理实现状态。

**定义 22.2（准确采用AH12.2的三阶分支）。** 固定非空紧Hausdorff空间 $X$ 和局部平凡复 $*$-代数丛 $\mathfrak B\to X$，纤维为 $M_3(\mathbb C)$，过渡为连续保单位复 $*$-同构。取同一完整原域

$$
M=\Gamma(X,\mathfrak B),\qquad E=M_{\rm sa},\qquad
S(a,b)=a\circ b=(ab+ba)/2,\quad u=1,
$$

$$
C=\{a\in E:a(x)\ge0\ (x\in X)\},\qquad
N(a)=\sup_{x\in X}\|a(x)\|.
\tag{22.1}
$$

原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定 $C$；全部原质量 $m_\gamma=\gamma(u)$，包括零、不等、次归一及原表示意义下的非正常评价，原样保留。$D:E^2\to E$ 始终是同一给定总映射。完整原A1/P2要求全部实际 $a,b$、两种次序及每份原评价的二表

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(b\circ a)-i\gamma D(b,a)&\gamma(b^2)
\end{pmatrix}\succeq0.
\tag{22.2}
$$

A2为每个相加三表 $(a+b,a,b)$ 及全部排列的实部在整个 $\mathbb R^3$ 上半正定，指定相加向量 $(1,-1,-1)$ 及其相应排列准确给零。A3保留 $u^2=u$ 和同一固定有理 $0<\vartheta\le1$ 上全部 $0\le e\le\vartheta u\Rightarrow e^2\le e$。不先给复三表正性。

对每个实际三元组 $(h;a,b)$，仅用同一个旧映射定义

$$
v=D(h,a)-h\circ b,\quad w=h\circ a+D(h,b),\quad
r_\pm=a\pm v,\quad s_\pm=b\pm w.
$$

完整PB是对全部这些实际三元组及全部原评价要求

$$
\gamma(r_+^2+s_+^2+2D(r_+,s_+))
=\gamma(r_-^2+s_-^2+2D(r_-,s_-)).
\tag{22.3}
$$

零、重复、任意幅度、缩放、平移、背景、嵌套调用及四个实际外层标签都在量词内。由原评价分离和已知Jordan双线性，其准确元素式为

$$
D(a+v,b+w)-D(a-v,b-w)=-2a\circ v-2b\circ w.
\tag{22.4}
$$

在旧值识别完成前，不输入 $D$ 的可加、齐次、连续、可测、协变、局部性、中央模线性、商下降或完成延拓；不扩大原域，不用padding，不以截断输入替换原输入。

**定义 22.3（由同一旧角校准的全局方向）。** 按AH12.3、SQ31.1–31.4，先取得由给定 $D$ 唯一确定的连续中央符号

$$
Q\in C(X,\{\pm1\})u,\qquad J=iQ,\qquad
K(a,b)=\frac J2[a,b].
\tag{22.5}
$$

这里的逐点符号是OP80.3的 $\sigma_x=Q(x)$，与AH1.7的 $\varepsilon$ 满足 $\varepsilon=-Q$。不能任意选一个符号替代旧表的方向；不能从非开闭分支任意拼接符号。辅助 $K,J$ 及下文投影补 $q$ 均不替换原全词来源的同名字母。

对实际 $W\in M$ 定义

$$
x(W)=\frac{W+W^*}{2},\quad y(W)=-\frac J2(W-W^*),\quad
W=x(W)+Jy(W),\quad F(W)=D(x(W),y(W))-K(x(W),y(W)).
\tag{22.6}
$$

每个固定 $F(W)$ 属于原 $E$；不假定 $W\mapsto F(W)$ 连续。特别地

$$
q_D(W):=x(W)^2+y(W)^2+2D(x(W),y(W))=W^*W+2F(W).
\tag{22.7}
$$

**接口 22.4（既有原像定理的准确消费）。** 下列前件和量词均已由固定正文支付，不另立为原候选的新假设。

| 既有接口 | 本文准确代入及所得结论 |
| --- | --- |
| SQ31.1、31.3与OP80.1–80.2 | 完整JB环境为同一 $E$，稠密包含为恒等，单块满Jordan商为图内的 $\pi=\operatorname{ev}_{x_0}:E\to H_3(\mathbb C)$。满性由图内常矩阵乘bump后延零取得；原锥、单位、范数和评价正是22.1。任意两份实际输入的点像若共同支撑于同一秩至多二角，就有 $D(a,b)(x_0)=K(a,b)(x_0)$；秩零、一角旧输出为零。两槽同时含任意角内标量部分，且全部实际代表都包括。 |
| OP82.1与SQ31.4 | 同一简单纤维的所有二阶角共用一个符号；同一非零旧输出的连续性使它局部连续，复星过渡使其拼成22.5的全局 $Q$。不假定旧 $D$ 协变。 |
| SQ31.2、AH13.1 | 准确锥将原二表送给任意数学正泛函。令 $A=a(x_0),B=b(x_0),d=D(a,b)(x_0)$，任意向量 $\xi$ 满足下式；同一实际调用的任一槽点像为零，输出点像即为零。 |

$$
|\xi^*d\xi|^2\le\|A\xi\|^2\|B\xi\|^2
-\bigl(\operatorname{Re}\langle A\xi,B\xi\rangle\bigr)^2.
\tag{22.8}
$$

Hermitian性及分离性还给 $D(a,b)=-D(b,a)$ 和全域零行。若某一输入点像为 $\mu p$、$p=ee^*$ 秩一，取 $\xi\perp e$ 再作Hermitian极化，便有 $qdq=0$，$q=I-p$。数学正读取不增加原实际准备，不除以任何质量。这里没有先定义纤维映射 $D_{x_0}$。

## 23. 两条正交射线识别零对角的全幅实际行

**定理 23.1（任意实际代表、任意连接及补角背景）。** 任取实际 $r,a\in E$ 和 $x_0\in X$。若

$$
r(x_0)=\mu p,\quad p=ee^*,\quad\|e\|=1,\quad
p\,a(x_0)\,p=0,
$$

则 $D(r,a)(x_0)=K(r,a)(x_0)$。$\mu$、连接幅度和补角背景任意；$r,a$ 在其他点完全保留。

证明。以下大写矩阵只表示所写实际标签在 $x_0$ 的像。记

$$
R=\mu p,\quad q=I-p,\quad A=H(z)+B,\quad H(v)=ve^*+ev^*,\quad
z\perp e,\quad B=qBq=B^*,\quad \jmath=J(x_0)=iQ(x_0).
$$

在这个纤维内，$K(A_0,B_0)$ 表示已知矩阵 $\jmath[A_0,B_0]/2$。$\mu=0$ 用22.8的零槽。以下 $\mu\ne0$。对同一个实际输出用秩一零压缩，写

$$
d=D(r,a)(x_0)=\delta p+H(w),\qquad \delta\in\mathbb R,\quad w\perp e.
\tag{23.1}
$$

先记录原 $\operatorname{PB}(a;r,0)$ 的准确四标签和元素式：

$$
(r-D(r,a),\ r\circ a),\qquad(r+D(r,a),\ -r\circ a),
$$

$$
D(r-D(r,a),r\circ a)-D(r+D(r,a),-r\circ a)=2r\circ D(r,a).
\tag{23.2}
$$

若 $z=0$，则 $(r\circ a)(x_0)=R\circ A=0$；两份实际外层的第二槽点像均为零，22.8使它们自己的旧输出点像为零。于是 $2R\circ d=2\mu\delta p+\mu H(w)=0$，从而 $d=0=K(R,A)$。

设 $z\ne0$，令 $t=\|z\|$、$f=z/t$、$L=\operatorname{span}_{\mathbb C}\{e,f\}$，并取

$$
u_\epsilon=\frac{e-\epsilon\jmath f}{\sqrt2},\quad
P_\epsilon=u_\epsilon u_\epsilon^*,\quad
C_\epsilon=\epsilon\,2tP_\epsilon
=\epsilon t(p+ff^*)+H(-\jmath z),\quad \epsilon=\pm1.
\tag{23.3}
$$

这里 $P_+P_-=0$，$P_++P_-=p+ff^*$。用满点评价各选一份实际 $c_\epsilon\in E$，使 $c_\epsilon(x_0)=C_\epsilon$；例如局部常矩阵乘支撑紧含于图的实bump后延零。$R,C_\epsilon$ 共同支撑于二阶角 $L$，故接口22.4对这两份实际调用给

$$
D(r,c_\epsilon)(x_0)=K(R,C_\epsilon).
$$

只计算已知矩阵乘法，可得

$$
K(R,A)=H(-\jmath\mu z/2),\qquad
R\circ C_\epsilon=\epsilon\mu t p+K(R,A),\qquad
R\circ A+K(R,C_\epsilon)=0.
\tag{23.4}
$$

最后一式来自 $R\circ A=\mu H(z)/2$ 和 $K(R,C_\epsilon)=-\mu H(z)/2$，对两种 $Q(x_0)$ 均成立。

令同一个固定误差 $\Delta=d-K(R,A)$。对实际 $\operatorname{PB}(r;a,c_\epsilon)$，保留实际位移

$$
v_\epsilon=D(r,a)-r\circ c_\epsilon,\qquad
w_\epsilon=r\circ a+D(r,c_\epsilon).
$$

只在指定点，它们读成

$$
v_\epsilon(x_0)=\Delta-\epsilon\mu t p,\qquad w_\epsilon(x_0)=0.
\tag{23.5}
$$

不把原元素 $w_\epsilon$ 换成零。两份真实外层为 $(a\pm v_\epsilon,c_\epsilon\pm w_\epsilon)$，其第二槽点像同为秩一矩阵 $C_\epsilon$。置 $R_\epsilon=I-P_\epsilon$；22.8对各自旧输出给

$$
R_\epsilon D(a\pm v_\epsilon,c_\epsilon\pm w_\epsilon)(x_0)R_\epsilon=0.
$$

对PB元素式(22.4)压缩，$w_\epsilon(x_0)=0$，于是

$$
R_\epsilon\bigl(A\circ(\Delta-\epsilon\mu t p)\bigr)R_\epsilon=0.
\tag{23.6}
$$

因 $pAp=0$，$A\circ p=H(z)/2$。直接读两条射线得 $u_\pm^*H(z)u_\pm=0$；$H(z)$ 又支撑于 $L$，故 $R_\epsilon(A\circ p)R_\epsilon=0$。因此同一个自伴矩阵 $T=A\circ\Delta$ 满足

$$
R_+TR_+=R_-TR_-=0.
\tag{23.7}
$$

任取 $\xi\in L^\perp$，有 $R_\pm\xi=\xi$，故 $T\xi$ 同时属于 $\operatorname{ran}P_+$ 和 $\operatorname{ran}P_-$。两条射线正交，得到 $T\xi=0$。写

$$
\Delta=\delta p+H(\eta),\qquad \eta=w+\jmath\mu z/2.
$$

利用 $Ae=z$、$A\xi=B\xi$ 和 $\xi\perp e,z$，逐项乘法给

$$
qT\xi=\tfrac12z\eta^*\xi=\tfrac12z w^*\xi.
\tag{23.8}
$$

这里 $q\Delta A\xi=0$，$qA\Delta\xi=z\eta^*\xi$，所以任意 $B$ 的贡献没有被假定为零，而是被这一次压缩消去。由 $z\ne0$ 得 $w^*\xi=0$；对全部 $\xi\in L^\perp$ 成立，再由 $w\perp e$ 得 $w\in\mathbb Cz$。

现在才回到同一实际PB式(23.2)：两对外层点像 $(R-d,R\circ A)$、$(R+d,-R\circ A)$ 都共同支撑于 $L$。接口22.4识别它们各自的旧值，只对已识别的 $K$ 展开：

$$
\begin{aligned}
2R\circ d
&=K(R-d,R\circ A)-K(R+d,-R\circ A)\\
&=2K(R,R\circ A)=2R\circ K(R,A).
\end{aligned}
\tag{23.9}
$$

最后一个恒等式由 $R^2=\mu R$ 得到。于是 $R\circ\Delta=\mu\delta p+\mu H(\eta)/2=0$，$\mu\ne0$ 给 $\delta=0,\eta=0$，即 $d=K(R,A)$。全程没有将未知 $D$ 拆和、缩放或更换代表。∎

**关系几何 23.2。** 本证明消除的是同一个固定 $T\xi$：两次真实PB和各自P2使它既指向 $P_+$，又指向 $P_-$，而 $\operatorname{ran}P_+\cap\operatorname{ran}P_-=0$。这份有限相容关系取代AH16.6在三阶中缺少的第四条共同零方向；未要求OP92.2的侧面系数先饱和，也未将OP93.1的非严格预算改成严格预算。

## 24. 局部箭头的全部过渡带与有限侧面运输

**接口 24.1（先识别全局两内行，再运输）。** 对实际当前 $T\in M$、实际 $r=r^*\in E$，置

$$
A_r=(u-Jr)^{-1}T=X_r+JY_r,\qquad
C_r=(u+Jr)(u-Jr)^{-1}.
$$

若两份实际内值在整个 $X$ 满足 $D(r,X_r)=K(r,X_r)$、$D(r,Y_r)=K(r,Y_r)$，则

$$
F(C_rT)=F(T).
\tag{24.1}
$$

这是AH13.2、SQ32.2的直接应用：原PB的实际负、正端点分别为 $(u-Jr)A_r=T$ 和 $(u+Jr)A_r=C_rT$，普通正平方同为 $A_r^*(u+r^2)A_r$。这里从未以同点代表代替负端点，也未在只有一点内行相等时调用全局PB运输。

**定理 24.2（准确局部箭头可识别）。** 在一张合法图 $O$ 内固定常值秩一投影 $p=ee^*$，令 $q=I-p$。若同一实际 $W\in M$ 在整个 $O$ 满足

$$
qWq=0,
\tag{24.2}
$$

则对每个 $x_0\in O$ 有 $F(W)(x_0)=0$。图外的原 $W$ 任意，不截断输入。

证明。先对任意满足24.2的实际当前 $T$ 支付一步。取图内任意常值秩一 $s\le q$ 和实连续 $\lambda$，$\operatorname{supp}\lambda\subset O$，令实际全局演员 $r=Q\lambda s$，图外置零。在 $O$ 内有

$$
(u-Jr)^{-1}=(I-s)+(1-i\lambda)^{-1}s.
\tag{24.3}
$$

该逆元与 $p,q$ 交换，故 $qA_rq=0$，从而

$$
sX_rs=sY_rs=0.
\tag{24.4}
$$

在每个活跃点，定理23.1分别用于实际 $(r,X_r)$、$(r,Y_r)$；非活跃点用22.8的同一实际首槽零预算。于是先得到两份全空间元素等式，才用24.1。$C_r$ 也与 $p,q$ 交换，故 $q(C_rT)q=0$。这同时支付演员由非零连续关闭到零的整个过渡圈，并保留下一步需要的准确箭头条件；不要求连接小于二，不以大参数压缩两侧连接。

在指定点写

$$
W(x_0)=\begin{pmatrix}\alpha&b^*\\c&0_{2\times2}\end{pmatrix}
\quad\text{相对 }\mathbb Ce\oplus q\mathbb C^3.
\tag{24.5}
$$

若 $b=0$ 或 $c=0$，其实部及 $J$-虚部已共同支撑于 $\operatorname{span}\{e,c\}$ 或 $\operatorname{span}\{e,b\}$，直接消费接口22.4。否则选普通 $V\in U(q\mathbb C^3)=U(2)$，使 $Vc=\kappa b$，$\kappa=\|c\|/\|b\|>0$；单位向量间的等距匹配可扩成酉矩阵。有限酉谱定理给

$$
V=e^{i\theta_1s_1}e^{i\theta_2s_2},\qquad
s_j\le q\text{ 秩一},\quad\theta_j\in[-\pi,\pi].
$$

选实连续 $0\le h\le1$，在 $x_0$ 邻域为一，$\operatorname{supp}h\subset O$。对每个 $j$ 使用两次实际演员

$$
r_{j,1}=r_{j,2}=Q\tan(\theta_jh/4)s_j,
\tag{24.6}
$$

图外延零。参数有限且绝对值不超过一；每次Cayley因子准确为 $e^{i\theta_jh s_j/2}$。全部实际前缀仍满足24.2，上段逐步给全域 $F$ 不变性。至多四步后，实际终点在 $x_0$ 为

$$
W_m(x_0)=(p+V)W(x_0)=\begin{pmatrix}\alpha&b^*\\\kappa b&0\end{pmatrix}.
\tag{24.7}
$$

其两份自伴标签共同支撑于二阶角 $\operatorname{span}_{\mathbb C}\{e,b\}$。接口22.4识别的是这份实际终点自己的旧输出，故 $F(W_m)(x_0)=0$，24.1沿有限链返回即得结论。∎

**边界 24.3（左右核没有被混同）。** 箭头条件只给块式24.5，不直接给共同核。例如 $W=E_{12}+E_{31}$ 满足 $qWq=0$、秩为二，却有 $\ker W=\mathbb Ce_3$、$\ker W^*=\mathbb Ce_2$。24.6只旋转列腿 $c$，保留行腿 $b^*$，在实际终点才使两腿共线。因此不能由秩至多二直接调用二阶角识别，也不能只凭某一点的箭头条件支付整张图的运输。

## 25. 局部秩一演员对任意实际第二输入的全幅旧行

**定理 25.1（全局元素等式）。** 在图 $O$ 内固定常值秩一投影 $p$，取实连续 $g$，$\operatorname{supp}g\subset O$。令实际 $r=gp$ 在图外为零，则对每个实际 $a\in E$ 有

$$
D(r,a)=K(r,a).
\tag{25.1}
$$

不限制 $g$、第二输入的射线对角、连接、补角背景或幅度。

证明。保留实际 $d=D(r,a)$、$j=r\circ a$。原 $\operatorname{PB}(a;r,0)$ 的两份实际复标签准确是

$$
W_+=r-d+Jj,\qquad W_-=r+d-Jj.
\tag{25.2}
$$

图内每一点，P2的秩一零压缩给 $qdq=0$；若 $g(x)=0$，同一实际输出甚至为零。又 $qjq=0$，所以两份实际全局截面都在整个 $O$ 满足 $qW_\pm q=0$。定理24.2逐点认出 $F(W_\pm)=0$ 于 $O$。图外 $r(x)=0$，22.8给 $d(x)=j(x)=0$，两份外层也由同一零槽认出。因此原23.2的两份实际外值都已识别。

固定一点，记 $R=\mu p$、$A=a(x)$。原PB在该点成为

$$
2R\circ d(x)=K(R-d(x),R\circ A)-K(R+d(x),-R\circ A)
=2R\circ K(R,A).
\tag{25.3}
$$

这里仅展开已识别的矩阵交换子，并用 $R^2=\mu R$。当 $\mu\ne0$ 时，选单位 $e$ 生成 $p$，仍记 $H(v)=ve^*+ev^*$；$d(x)-K(R,A)$ 属于 $\mathbb Rp+H(q\mathbb C^3)$，而 $R\circ$ 在这个空间上单射。当 $\mu=0$ 时，22.8直接给零。于是逐点均有 $d(x)=K(R,A)$，即25.1。所有补角背景和真实前缀一直保留。∎

定理25.1先识别实际构造出的局部演员。它没有在此把任意首槽替换成同点局部秩一代表；全部首槽的旧值须经下一节实际运输识别。

## 26. 三阶同一旧表的全域分类

**定理 26.1（保留原输入的至多六步点上正化）。** 对任意实际 $W\in M$ 和任意 $x_0\in X$，有至多六个实际局部秩一演员，产生实际前缀 $W_0=W,W_1,\ldots,W_m$，使

$$
F(W_k)=F(W)\quad(0\le k\le m),\qquad W_m(x_0)\ge0.
\tag{26.1}
$$

证明。在含 $x_0$ 的一张合法图 $O$ 内选 $0\le h\le1$，在 $x_0$ 邻域为一且 $\operatorname{supp}h\subset O$。只对固定矩阵 $W(x_0)$ 作SVD：若 $W(x_0)=L\Sigma R^*$，取 $V=RL^*$，则 $VW(x_0)=R\Sigma R^*\ge0$。奇异和零矩阵均包括。对这个普通酉矩阵作谱分解

$$
V=\prod_{j=1}^3e^{i\theta_jp_j},\qquad\theta_j\in[-\pi,\pi],
$$

其中 $p_j$ 为常值正交秩一投影。每个相位使用两次实际演员 $r_{j,1}=r_{j,2}=Q\tan(\theta_jh/4)p_j$，图外置零。各Cayley因子为 $e^{i\theta_jh p_j/2}$，参数有限且绝对值不超过一。

对每一步的实际当前 $T$，25.1已覆盖它的两份实际逆Cayley第二输入 $X_r,Y_r$，给全域两内行识别；然后24.1给 $F(C_rT)=F(T)$。这覆盖全部过渡带、每个实际前缀和任意当前幅度。至多六步在 $x_0$ 的总左因子准确为 $V$，得到26.1。只在一个指定点选择SVD及谱分解，没有要求全局连续选择它们。∎

**定理 26.2（三阶完整连续截面域的给定旧响应分类）。** 在22.2的全部原前件下，由旧角校准的唯一连续 $Q$ 满足

$$
\boxed{D(a,b)=\frac{iQ}{2}[a,b]\qquad(a,b\in E).}
\tag{26.2}
$$

证明。固定任意实际 $W,x_0$，取26.1的实际终点。其自身的 $J$-虚部满足 $y(W_m)(x_0)=0$，所以22.8对这份实际输入给 $D(x(W_m),y(W_m))(x_0)=0$；对应 $K$ 也为零。于是

$$
F(W)(x_0)=F(W_m)(x_0)=0.
$$

量词覆盖全部原 $W$ 和全部点，得到 $F(W)=0$。取同一实际 $W=a+Jb$，其分解恰为 $x(W)=a,y(W)=b$，遂得26.2。没有用另一份只在该点为正的截面替代实际终点。∎

**推论 26.3（逆向、旧接头及与高阶的关系）。** 每个连续 $Q:X\to\{\pm1\}$ 给出的 $K_Q$ 都满足全部原A1–A3/P2/PB，准确复用AH17.4、SQ44.2–44.3逆向及63.2逆向；其证明不要求 $n\ge4$。因此三阶全部合法同域总映射恰为这些 $K_Q$，给定 $D$ 的 $Q$ 唯一。与AH17.3合并，AH12.2完整矩阵截面分支的同一结论现覆盖全部固定 $n\ge3$。

识别之后才得到局部性、纤维下降、实双线性及 $D(fa,gb)=fgD(a,b)$，其中 $f,g\in C(X,\mathbb R)$。特别地，若实连续 $h(x_0)=1$，则同一旧值满足

$$
D(hx(W),hy(W))(x_0)=D(x(W),y(W))(x_0).
\tag{26.3}
$$

故SQ56.1／69.1的存在式截断接头在本三阶完整域内成为后置结论。证明本身一直运输原 $W$，未消费任何 $hW$ 比较。SQ54.3关于旧小连接阈值认证的无首步反例仍成立；25.1支付的是新的全幅行认证，没有声称旧阈值处处成立。

在已由SQ43.2、44.2或63.1支付复类型和相容代数取向的同阶实Jordan丛分支，可先构造同一 $\mathfrak B_{\sigma_D}$，在该乘法中取 $Q=u$，再应用26.2，得到 $D=K_{\sigma_D}$。这只是已付接口的消费，不把一般JB的类型或取向桥写入本定理的无条件范围。

## 27. 已付静态入口的精确消费与全部原质量

**推论 27.1（原结合乘法与已有静态消费者）。** 26.2取得同一旧 $D$ 后，按AH19.1的接口对应消费AQ32.1–32.2、23.1、6.3及SQ44.2、48.2的既有静态构造；不重证这些消费者。

| 既有结果 | 本域先付条件及结论 |
| --- | --- |
| AQ32.1–32.2 | 同一原准确序单位资料、A1–A3/P2由22.2给定；26.2已给旧 $D$ 实双线性。取得 $N(D(a,b))\le N(a)N(b)$、全有限原有向复Gram及P3。 |
| AQ23.1、6.3 | 全P3已付，完整PB仍为22.3；取得原R和同一原复化的结合乘法 $\star_Q=S-iD$，保持原自伴锥、单位及范数。本域原 $E$ 完备，自伴部即原 $E$。 |
| SQ44.2、48.2 | 在 $Q=1$ 的开闭部分取通常乘法，$Q=-1$ 部分取相反乘法。所得同一C*代数的正锥和自伴域未变；既有GNS直和给忠实保单位保锥等距表示，保留每份原评价及其质量。 |
| SQ48.3、AH20.9的消费者接线 | 只替换其已付的静态入口为26.2认回的同一 $S,D,\star_Q$；其余来源严格按下一节全文合取，不引入其他分支的原子、理想或稠密前件。 |

特别地，既有接口给全部实际 $a,b,c\in E$ 的

$$
(a\circ b)\circ c-D(D(a,b),c)
=a\circ(b\circ c)-D(a,D(b,c)),
$$

以及全部有限原标签、任意复系数及每份未改变原评价的

$$
\sum_{j,k}\bar z_jz_k\{\gamma(a_j\circ a_k)-i\gamma D(a_j,a_k)\}\ge0.
\tag{27.1}
$$

全部内外层仍用同一个原 $D$。形式复化 $a+ib$ 上的 $\star_Q$ 与运输辅助 $W=a+Jb$ 按22.6对应，负向区域不暗换乘法。相容复范数为 $\|a+ib\|_{\star_Q}^2=N(a^2+b^2+2D(a,b))$。每份原评价有向量 $\xi_\gamma$，满足 $\gamma(a)=\langle\xi_\gamma,\Pi(a)\xi_\gamma\rangle$、$\|\xi_\gamma\|^2=m_\gamma$；零质量取零向量，不等和次归一质量不改写。一般正泛函不被替换成纤维正常态或迹类态求和，表示像不必为全 $B(H)$。

## 28. 七项来源的全文合同

**定义 28.1（严格全文纳入及引文身份）。** 记 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ 为固定SQ第47节全部定义、合同、公式、量词及其逐项纳入的固定上游全文的严格合取。这与SQ64.1、69.2及AH20.1规定的全文语义一致；不是七个标题或消费者摘要。下文逐字引用固定SQ47.1–47.13，连同七项合同，保留其原编号。引文中的“主源”、缩写及版本按SQ自身1.3、39、47.1解析，不能改成本增补的局部编号；其中SM指《谱混合响应与直接窗口边界》，AQ才是本文的静态重构卷。引文逐项纳入的上游全文继续合取，不能由引文展开删减。原根、静默和其他静态分支不被改成三阶模型。

> ## 47. 同一原世界的七项来源全文合同
>
> **定义 47.1（完整来源谓词及同一性）。** $\mathcal C_{\rm src}(\Omega;S,D)$ 严格取固定主源第11–12、24、28及37–38章所有实际来源条款及它们逐项纳入的上游全文之合取。只把它们消费的静态入口替换为44章的同一 $S,D$ 及相容 $M_{\sigma_D}$，不额外要求原 Jordan 丛已有复乘法、平凡或有全局矩阵单位。下列展开与被引用的全文同时合取，不将任何一条充分前件改成摘要。所有缩写与上游版本严格采用主源1.3、39；OP、PT、PB、SM、C、AQ、R3、W、FR、XV、SF 均固定于 `f24d1138a7b994da16abd9a47affedea64ea44ce`。
>
> 具体包括 SF105全文、106.1；OP29.2、78.2、87.1及其纳入的18.2、24.1、57.1、63.2、70.1；FR139.1–139.2、147.1–147.3、155.1–155.2；XV14.1、20.1–20.3、23.1–23.5；R3 8.1–8.5、80.1；AQ8.3–8.4、14.2、25.1、53.1；W95.2、116.1，以及它们逐项纳入的全部原来源、实现、对象和充分条件。SM78.2、86.1及43.2、49.1、61.1、69.1，中央续卷 C145.1–145.7、155.1、160.3、171.1–171.7、181.3、186.1–186.7、194.2、199.2与PB122.1中有关的原量词也全部保留。
>
> 原世界仍只有同一个 $\Omega/\mathrm{native}$。原对象、准备、事件、设备、程序／过程、比较权 $q$、跨标签全词共同 $K/J$，原 $J,S,U,D_{\rm network},C,G,M_j,N_j,AS,R_2$ 和全部模式网络保持身份。原网络的 $D_{\rm network}$ 不是本响应 $D$，网络中的 $C$ 也不是数学正锥；来源中的 $\sigma,t_0,d$ 不是本取向截面、底点或矩阵阶数。
>
> 所有原中心、经典、不等维块、无轴和静默对象保留；零、不等和次归一质量保留；实际乘积、真正相关联合、参考／副本及每层递归同源引用保留。parent、ready、合法控制、旗标、整个环境、原钟及单位、同一原 $\sigma,t_0$、全部原菜单、固定支持的全质量、每个原中间切口均不得用数学坐标代换。全部合法顺序、自适应、并行历史，以及每份完整输出的每个仍合法未来，均在原类型内量化；细记录、失败、拒绝、停止、销毁、泄漏、真正分组遗忘、同数两侧返回及真实逆向返回同样保留。
>
> 未定义请求不补成零箭头。相同矩阵、相同当前读数或相同纤维像，不合并不同原程序、历史、输出、原 $q$ 零集和未来权限。本模型只指定被选静态对象 $E=\Gamma(X,\mathfrak J)$；不将 $\Omega$ 的其他对象和其他静态分支强制为同一固定 $n$ 的模型。所有“全部”“每个所需有限长度／深度”“每个正精度”在原消费者的合法适用域保持完整强度。$M_\sigma$ 中的归一纤维迹 $T_\sigma=\operatorname{Tr}/n$ 只是数学读取，不是原准备、原质量或物理概率。
>
> **定义 47.2（原根类、十一端点及静默支）。** 完整根类 $\mathfrak K_{\rm r}$、候选 $\mathsf Q^{\rm root}_{46}$ 和它们全部原背景与主源37.2一致。全部 $89$ 配置、$235$ 实际逆等距边、固定外位 $10/010$、原黄金块、阻塞值、两个边界、严格左响应、十一回返、十个相邻 Artin 与四十五个远关系，同一个原正定度量 $g$ 与给定单位 ready，均在同一原对象上。原 $26+63$ 扇区、读后七地址、$1024$ 终端标签、原读器、报告、调用顺序、细档案及全部失败类型没有被压缩成代数标签。
>
> 程序签名仍为十一地址有限前读词后接旧终端，或先读并保留 $b_9$，再接不依赖该记录的外生七地址后词并接旧终端；它不自行给出新分析器或菜单 producer。原根条件为
>
> $$
> \begin{gathered}
> s=(3,7,1,2,4,5,6,8,9),\qquad
> \operatorname{tr}_{V_r}(L_r^\dagger L_r)=2,\\
> \|U_si_rL_r\|_{\rm HS}^2\le2
> \quad\text{对全部原 }\mathfrak K_{\rm r}\text{ 资料}.
> \end{gathered}
> \tag{47.1}
> $$
>
> 原 $r,i_r,L_r,U_s$ 及 Hilbert–Schmidt 迹保留原数学身份，不改成 $T_\sigma$ 或物理准备、读口、概率。XV23.2的既有等价将(47.1)接到全部原输入及全部十一端点的 E1：
>
> $$
> U_j^\dagger U_j=I\qquad(0\le j\le10).
> \tag{47.2}
> $$
>
> 同一 ready 的 $\rho=\|L_ru_*\|=0$ 及 $k=0$ 都在域内，不补正活动公理、不改 ready。$k=0$ 的单位 ready 有 $\rho=1$，$k>0$ 的全静默 ready 同样保留；零根响应、零活动及其合法未来均不删。
>
> 同一 ready 的两标量词备选仍按原分支使用：$\rho>0$ 要求原 $s$、$(0,s)$ 两词不膨胀，$\rho=0$ 则保留全输入、全十一端点的(47.2)。XV14.1的一次固定全支撑词 $a$ 与 $(0,a)$ 备选及176有界长度词表备选，各守自己的句法和零活动支。两条静默 ready 的零缺陷不代替全 E1；根迹条件、两词条件及有界长度观察不被合成更弱条件，也不从词长或数学迹推出物理费用。
>
> **定义 47.3（其他原静态分支）。** FR139.1、155.1和XV20.1所列各支完整保留。有限原响应支具有同一原实载体、准确评价锥、全域序界、序单位范数、全部原对实际共轭、相加三表及全部排列的实部 PSD、指定相加零方向、总事件固定与同一正有理小窗口。全原三元实部换括号，以及同一实际旧输出集合及其原量词上的输出辨识，仍按该支的原条件，零原空间也在域内。
>
> 指定完整 II₁ 支保留同一原含单位复因子、完整自伴域、Jordan 平方、准确锥／单位／范数、指定前对偶、正常忠实归一数学迹、原实际共轭、全实部关系及旧输出辨识。该迹既不等于原质量，也不由有限返回或本模型的纤维迹制造。
>
> 其余原载体支继续要求全部至多二标签的实际复表正性，含零、重复与缩放；全部相加三表，以及满足某对
>
> $$
> N(a_i-\epsilon a_j)\le\tfrac14\max\{N(a_i),N(a_j)\},
> \qquad\epsilon\in\{-1,1\},
> \tag{47.3}
> $$
>
> 的全部三表、全部排列和任意第三标签，在整个
>
> $$
> F_3=\bigcup_j\{x+it e_j:x\in\mathbb R^3,t\in\mathbb R\}
> \ \cup\ \{z\in\mathbb C^3:\textstyle\sum_jz_j=0\}
> \tag{47.4}
> $$
>
> 上非负，连同相加零平方、总事件、小窗口、全实部式及全部原背景。差分面、无限支撑、整个 $F_3$ 与旧全响应量词保持，CountRead不被移入有限支。
>
> 既有一般同平方 JB 恢复、完备原序单位路线、固定 $B(\ell^2)$ 路线、指定原理想传播及原词恢复，分别继续使用其关系逼近、有限依赖反映、全输出统一误差、完备性、正常性、原包含和作用纤维条件。它们在已成范围直接复用，既不被降为未证明，也不把它们的额外前件赠给一般原对象。
>
> **合同 47.4（复 Hilbert、可观测量和实际相干叠加）。** 原具名可取得标签、比较权 $q$、native、共同跨评价配对、全部原词、parent、ready、合法控制、实际相干准备、全部根及静默分支保持。数学表示不生产任意向量准备、全 $B(H)$ 的可取得像、免费控制、复制或原设备。
>
> 指定原词空间仍为同一复空间 $V_{\rm nat}$、第一槽共轭线性的半正定 Hermitian 型 $K_{\rm nat}$、全部原 $\xi_\gamma$ 及原总集合映射 $\mathsf J_a:V_{\rm nat}\to V_{\rm nat}$，并完整要求
>
> $$
> \begin{aligned}
> K_{\rm nat}(\xi_\gamma,\mathsf J_a\xi_\gamma)&=\gamma(a),\\
> K_{\rm nat}(\mathsf J_a z,\mathsf J_b w)
> &=K_{\rm nat}(z,\mathsf J_{a\circ b}w)
> -iK_{\rm nat}(z,\mathsf J_{D(a,b)}w),\\
> V_{\rm nat}&=\operatorname{span}_{\mathbb C}
> \{\mathsf J_{a_1}\cdots\mathsf J_{a_k}\xi_\gamma:
> k\ge0,\ a_j\in E,\ \gamma\in\mathcal P\},\\
> K_{\rm nat}(\xi_\gamma,\xi_\gamma)&\le m_\gamma,\\
> K_{\rm nat}(\mathsf J_a\xi_\gamma,
> \mathsf J_c(\mathsf J_a\xi_\gamma))&\ge0\qquad(c\in C).
> \end{aligned}
> \tag{47.5}
> $$
>
> 第一行量化全部 $a\in E$、$\gamma\in\mathcal P$，第二行量化全部 $a,b\in E$、$z,w\in V_{\rm nat}$，末行量化全部 $a\in E$、$\gamma\in\mathcal P$、$c\in C$。词必须先按原总映射实际复合，再取有限复线性包；空词及任意有限长度都包括。这个共同 $K_{\rm nat}$ 保留全部指定跨评价配对和有限正表，不能用每份评价独立的 GNS 核替换。没有预给 $\mathsf J_a$ 线性、$\mathsf J_0=0$ 或 $\mathsf J_u=I$，其恢复依原消费者的次序。
>
> $q_{\rm nat},K_{\rm nat},\mathsf J$ 就是上游原 $q,K,J$，其权、零集、跨标签意义、词身份和读序不变。它们不同于辅助 $q_D$、数学复化标量 $i$ 或取向截面。静态存在式 Hilbert 表示本身不认证这个指定原词实现。
>
> **合同 47.6（原态、效果、Born、全菜单及全部质量）。** 原评价与原事件的绑定、准确效果区间、接受归属、每份实际完整菜单仍由同一原世界承担。原互探 $\mathrm C_{12}$、mark、预定处处有限强度尺、$\mathrm A_{12}$、全部背景 $\mathrm{BI}_{12}$、非负性，以及消费者要求的有限维／最小可见／实尺度条件全部保留；原强度、原 $q$、中央比较权及概率质量不合并。
>
> Fourier9.6–9.12、10.10、17.9、18.12的共同根、有限实际端口、原角／二十七模适配器、完整坐标分区、真实独立抽签、每条所用平衡行、全部原目标和每个原 $(\xi,g,s)$ 的菜单覆盖都必须保持。具名事件按先原 $g^*$、再原 $d_s^*$、最后同一原根的物理顺序合法接续。同矩阵的不同原字分别支付覆盖；每个 P9 分支自己的独立 $W_e$、原权／质量校准、原接受事件与合法复合、其他块自己的 AS/EC、菜单外 OB、真正忠实二维到三维的全质量适配器及非零一维块均保留。纯校准子域不能代替全菜单、固定支持全质量和每个已量化中间切口。
>
> 两只独立九叶彩票 $(6,2,0)/9$、$(4,4,0)/9$，各自第九空程序、十六拒绝叶，以及相干 $I_3/3$ 返回保留细记录和原类型；相干返回不被细测成三个经典结果。
>
> 实际完整有限菜单 $\{e_j\}$ 只有在原事件绑定、$\sum_je_j=u$ 和 $m_\gamma>0$ 同时成立时才定义
>
> $$
> p_\gamma(j)=\gamma(e_j)/m_\gamma.
> \tag{47.6}
> $$
>
> 实际角菜单另须 $\sum_je_j=p$、原条件化身份及 $\gamma(p)>0$，才取 $\gamma(e_j)/\gamma(p)$。零、不等、次归一、中心权、经典混合、不等维及静默块的未归一读数全部保留，零质量不作除法。条件更新另须严格正的实际输出质量。
>
> 一般原态仍是正泛函。密度／迹类公式只在原有限全矩阵物理表示及过程绑定的域，或适用完整正常 $B(H)$ 接口、指定前对偶及相应收敛齐备的域使用。一般非原子中心或一般正规子代数的前对偶不自动给全 $B(H)$ 密度式。无限或非离散菜单的可数可加、正常性及前对偶另守47.12的原扩展条件。
>
> **合同 47.7（native、真正相关联合与张量）。** 原全词同一 $K/\mathsf J$、交叉零、同一旧局部乘法、每个中心对、经典／不等维／静默块、真实乘积及全部真正相关输入，都必须在一个实际共同实现中取得。每个被消费的局部全矩阵接口必须忠实、同向并交换；联合共同生成、原评价分离、所需重数、实际复制及每层递归同源参考，采用AQ53.1、AQ25.1第三行与W95.2、116.1的完整原量词。
>
> 只有同一个实际非零有序联合中忠实同向交换的两个局部全矩阵腿共同生成时，乘法才识别联合为 $M_d\otimes M_r$。具体 Hilbert 载体的重数还须原重数或不可约条件。一般中心情形对每个实际非零中央对都保留共同支持、共同生成和全部相关输入，不能由一个中央对替代全部中央对。
>
> 分别可达、相同边缘、数学交换或相同符号都不生产共同来源。42.9的辅助乘积环境不是该实际联合，原域中的辅助角也不是物理子系统腿、复制设备或自由参考。
>
> **合同 47.8（typed 箭头、CP 及整台递归参考）。** 对每条实际原细分支 $r:A_0\to B_0$，保留全部合法 typed 前接、真实未归一后上下文、每份完整输出的每个仍合法未来及全未来自然性。原回溯严格满足
>
> $$
> \gamma_{A_0}(\beta_r b)=\gamma_{B_0}^{\,r}(b),
> \tag{47.7}
> $$
>
> 并保持反变合法复合、typed分区、全质量运输及原箭头商下降。异类型输出仍分别按类型进入分区。正次单位和完成上的正延拓不自动给 CP；CP 的全槽同标签单位区间比较路线，以及整台实际箭头递归同源参考路线，各须自己的全部原前件。
>
> 递归路线要求每条完整 $r$ 都有实际 $r^+:A^+\to B^+$。系统、整个环境、所有成功／失败／细记录／输入输出port／post-port输出，以及每份完整输出的每个仍合法未来，都属于同一个能再次应用的实际规则类；真正遗忘、实际返回与合法复合也在类内。形式 CP 不能反向制造这些实际箭头。
>
> 两端各有共同真支持 $p_A,p_B$ 及忠实同向交换星嵌入；$A$ 端为
>
> $$
> i_A:\mathcal A_A\hookrightarrow p_A\mathcal A_{A^+}p_A,
> \qquad j_A:M_2\hookrightarrow p_A\mathcal A_{A^+}p_A,
> \qquad i_A(1)=j_A(I_2)=p_A,
> \tag{47.8}
> $$
>
> $B$ 端同型。三个实际参考投影 $q_1,q_2,q_3$ 与 $I_2$ 实张成 $(M_2)_{\rm sa}$。每次真实接线要求
>
> $$
> \beta_{r^+}i_B=i_A\beta_r,\qquad
> 0\le\beta_{r^+}(j_B(q))\le j_A(q)
> \quad(q\in\{q_t,I_2-q_t:1\le t\le3\}).
> \tag{47.9}
> $$
>
> 全部原相关正输入及决定整个锥的全部原联合评价都在这些交织和夹界的量词内。支持内补为 $p-j(q)$，不替换为环境单位补。两腿不要求生成整个环境或支持角；下一层系统是整台实际 $r^+$ 的全部响应，不是根代码。
>
> 对每条根箭头及每个所需有限长度 $L$，存在完整实际长 $L$ 链；每个 $k\le L$ 都有忠实累计嵌入及准确支持运输
>
> $$
> \begin{gathered}
> M_A^k:\mathcal A_{A_0}\otimes M_{2^k}\hookrightarrow\mathcal A_{A_k},\\
> \beta_kM_B^k=M_A^k(\beta_0\otimes\operatorname{id}_{2^k}),\qquad
> P_A^{k+1}=i_{A,k}(P_A^k)\le p_{A,k+1}.
> \end{gathered}
> \tag{47.10}
> $$
>
> 累计真支持不换为新环境共同支持或环境单位。任意精度路线保留精确根身份、同向结构、全部真支持／事件／相关输入／后口，并量化每个正精度和每个所需有限深度；一个固定正误差不足。每个有限长度的完整实际链，不等于要求一条实际无限链、物理无限张量积或免费旁接函子。根代码上任意多形式参考也不支付实际链。
>
> 已有原九号读口、它的实际参考／联合，以及准确来源已供应的有限返回刚性，按原条件继续使用，不倒称为缺失。返回复合 CP 不推出因子 CP 或一般箭头 CP。Kraus 算子式仍限合格有限全矩阵域，或另具适用正常物理表示、指定前对偶、分解和收敛的域；一般正规子代数正常 CP 对偶不自动给全 $B(H)$ Kraus 分解。
>
> **合同 47.11（完整仪器、TP、条件更新与 Lüders）。** 每台原实际仪器包括全部原输入运输、完整 typed 菜单、原接受端、整个环境、全部成功／失败／细记录／port／post-port输出，以及每份完整输出的每个仍合法未来。真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词及各自接受条件，严格取C171.5、AQ25.1第五行及其上游原合同；数学连续平方根不生产具名原平方根词。
>
> 同一正夹心只给静态代数入口。正次单位仅为 TNI；整个原测试的实际完整 typed 单位分区
>
> $$
> \sum_r\beta_r(u_{B_r})=u_{A_0}
> \tag{47.11}
> $$
>
> 才给 TP。不同输出类型不免费识别为一个物理直和。Lüders 另外要求同一完整输出具有投影效果、像内每条射线保持及完整输出校准；相同效果、概率、统计重复性或仅支撑保持都不代付。
>
> 条件更新只在严格正的实际输出质量处归一。零和失败分支及其记录、原类型、全部合法未来仍保留。密度、迹类、Kraus、迹公式均守47.8的准确域与收敛。数学 Kraus 指标不是自动给定的 P9 细记录或物理环境输出，数学迹不抹掉 port 未来。
>
> **合同 47.12（全历史、真遗忘、真实返回与 CountRead）。** 全部合法顺序、自适应、并行历史，整个环境、参考副本、细记录和泄漏，停止、拒绝、销毁，真正分组遗忘，同数两侧实际返回和同数逆向实际返回，都保留原类型及每份完整输出的每个仍合法未来。粗事件只沿其实际分组相加；丢弃一份档案不等于真遗忘。数学算子相同不合并程序、读取次序、原 $q$ 零集或AC方向。
>
> CountRead 绑定读后同一原完整活动输入及它的全未来实际 Return。读后活动 ready 接头、接受叶活动输出、第一合法消费者、具名分析词到实际全菜单和原接受端，均需原生 producer。原读后表、分母、查询、细地址、失败和终端类型不变成可再次作用的旧 ready。负提升两条活路的分别受控实现和相干聚合实现分别守原合同；数学负号不构造活路，数值相消也不返回完整输出。
>
> 原精确正生成 $B_{\rm src}$ 和另名闭正生成 $B_{{\rm src},\rm cl}$ 保持上游 $B,B_{\rm cl}$ 的身份，二者不混同，也不与数学正绝对值混名。两只独立九叶彩票、各自第九空程序、十六拒绝叶与相干 $I_3/3$ 返回继续保留记录和类型，不被细读成三个经典结果。
>
> 既有 native 初始读取、指定有限树与被动精确混合解码只在原平稳、真实同源、同初始版本的范围内使用。初始取得不代替整份后续输出的全未来 Return。返回表示层恒等仍需全输出／全未来忠实绑定，原档案分离条件及已有正常性边界均不删除。
>
> 无限历史、无限或非离散记录、可数可加、物理正常性、指定前对偶及所需收敛分别取原扩展来源。有限 PB 调用、数学函数演算、纤维迹或数学正读取不生产物理无限记录和读后真正双向返回。未定义请求保持未定义；静默、零质量对象与它们的合法未来都在域内。
>
> **合同 47.13（物理钟、动力学、能量与共同正作用量）。** 同一旧全域乘法、保持原域的流、真实相位与原门序列、同一实际过程内连续可逆 CPTP 一参数群及实际逆、物理钟和单位、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、共同仪器、共同作用量及同一个正 $\hbar$ 都须保留。一般可能不完备原域的流保持另按原条件，不从本完整域上的数学流推出。
>
> 原 $\sigma,t_0,d$、固定域、resolvent 和 $3s+r\le1$ 预算始终属于原设备、原参数、原适用域和量纲，不改为取向、局部坐标或证明中的有限步数。数学指数、离散词、范数路径、数学逆与公共返回效率不生产物理时间、可控相位、能量解释、控制成本、真实原逆或跨装置共同作用量。
>
> 只有这些原条件齐备且表示／生成元域适用时，才使用
>
> $$
> U(t)=e_{\cdot_\sigma}^{-itH/\hbar},\qquad
> i\hbar\dot\rho=[H,\rho]_\sigma,\qquad
> \dot b=\frac2\hbar D(H,b).
> \tag{47.12}
> $$
>
> 向量方程 $i\hbar\dot\psi=H\psi$ 限于对应自伴生成元域；无限维密度微分限于适用迹类可微域。所有公式都用同一已选乘法，不能在反向区域暗换普通矩阵乘法。有界数学内导子不代替无界 Hamiltonian、其定义域和实际酉群实现。
>

## 29. 完整候选的同响应等价与既有七项消费者

**定理 29.1（保持来源全文的三阶条件重构）。** 固定22.2的模型、全部原身份和评价，令 $\mathsf H(D)$ 表示全部原A1–A3/P2/PB。则

$$
\begin{aligned}
&\mathsf H(D)\ \land\ \mathcal C_{47}^{\rm pin}(\Omega;S,D)\\
&\quad\Longleftrightarrow\quad
\exists!Q\in C(X,\{\pm1\})u:\quad
D=K_Q\ \land\ \mathcal C_{47}^{\rm pin}(\Omega;S,K_Q).
\end{aligned}
\tag{29.1}
$$

在各项原合同确实成立处，SQ48.3的七项条件结论按其原对象、全部量词、质量、表示及定义域原位成立。

证明。正向用26.2，逆向用26.3的既有全部三元组逆向。来源谓词始终约束同一个旧响应，不能独立换一份响应来满足来源。27.1已经支付SQ48.3消费的同一静态入口；余下充分前件就是28.1全文，故直接应用该既有消费者，不重证其Hilbert、Born、张量、CP、仪器、历史或动力结论。唯一性相对于给定 $D$；未固定 $D$ 时，不同连续取向仍可给不同数学响应，实际来源也不保证对每份数学取向都有实现。∎

原全部质量和每个中间切口始终保留。Born归一仅用于实际完整菜单和严格正总质量；更新另需严格正输出质量。共同相关实现、每条根箭头每个所需有限深度的完整实际参考链、真支持运输、每个正精度、整台环境、全部成功／失败／细记录／port／post-port及每份完整输出的每个仍合法未来，均未被有限矩阵相位代付。无限记录、正常性、指定前对偶、收敛、原域保持、物理钟、生成元域、能量和共同正 $\hbar$ 继续遵守所引全文。

## 30. 来源、简化的准确范围与未决边界

**来源对应 30.1（固定复用与新增承重连接）。**

| 固定来源或成熟工具 | 本文准确用途 |
| --- | --- |
| [AH12.2–12.3、13.1–13.2、19–21][N3-AH] | 原完整截面模型、由旧D校准的Q及符号、同一实际PB的全局运输、静态消费者和全文来源框架。AH16–17的高阶分类不被重计为新结论。 |
| [OP80.1–80.2、81、82.1、84–85][N3-OP]与[SQ31.1–31.4][N3-SQ] | 满点评价、准确正读取、全部实际代表的完整二阶角、同一块共同符号和拼接。本文没有以“点像相等”自行推出旧值相等；只在这些既有定理的明确量词内消费它。 |
| OP83、89–101 | 旧严格小连接阈值、两外层共享预算及其等号模型的边界；零第三槽的有限PB片段不能替代完整PB。23.1增加的是真实第三标签相容约束，不重做或收紧旧预算。 |
| SQ32.2、51–56、64、69 | 实际逆Cayley输入、两份全局内行、同一原负端点及终点零槽；保留旧阈值无首步反例和一般截断接头的原范围。26.3只在本完整三阶域删除该未付接头。 |
| SQ43.2、44.2、63.1及其已给类型分支 | 先付代数取向，再构造保持同一原E/C/u/N/评价/质量的复代数丛。不得由旧D识别反向偷付复类型或取向。 |
| [AQ32.1–32.2、23.1、6.3][N3-AQ]与SQ48.2–48.3 | 先认回旧D，再原位消费全有限Gram、R、C*静态结构、全部质量和七项条件消费者；不重新证明这些已成结果。 |
| [CO60.1–60.5][N3-CO] | 比较反向相容与实际操作顺序的区别；严格复合不推出路径独立，零中心乘子类仍可容许非交换量子模型。 |
| 紧Hausdorff正规性与连续截断 | 来源SQ31.1、39、AH21.1所列成熟工具。只供应实际第三标签、局部演员和有限点上构造；不剪掉原W，不把bump当开闭函数或假群嵌入。 |
| 有限酉谱定理、SVD、向量等距匹配、Hermitian极化 | 同一固定来源SQ39及AH21.1的成熟有限矩阵工具。SVD只选一个纤维的正化酉，谱定理把它分成有限秩一相位；不对未知D求导、取极限或使用IFT。 |
| C*正泛函与GNS | 准确使用SQ48.2、AQ6.3的既有接口；成熟背景为这些来源所引Hanche-Olsen–Størmer《Jordan Operator Algebras》及其静态C*表示文献。一般动力对应的线性赋值前件不用于本证明的未知D。 |

新增承重综合是23.3–23.8的两条正交射线约束、24.3–24.7的全过渡带侧面运输、25.2的实际外层接回及26.1的六步原输入正化。前三步没有假定全幅原秩一行，最后一步启动前才由25.1得到它。与AH14–16相比，三阶路线不用第四条共同零方向，不用靠近reducing线的投影实基和普通酉群IFT；对箭头只需二维侧面的至多四步谱相位，最终正化至多六步。有限步数描述构造，不把原PB的全称前提缩成有限公理，也不减少原A1–A3/P2/PB及来源合同数。

**说明 30.2（旧局部反向模型的准确排除）。** 直接消费OP96–101已给的性质：其单一总映射保P2、共同二阶角和两份零第三项PB，却违反完整PB。本文不重新构造该模型。另可由23.1直接看出其指定横向行不可能延拓为完整PB响应：在OP96.1记号下取 $Q(x_0)=1$、$R=p$、$A=2X_{12}+q$、$d=\varepsilon X_{13}$。有 $pAp=0$、$z=2e_2$，23.3给明确第三标签点像

$$
C_\pm=\pm2(E_{11}+E_{22})+2i(E_{12}-E_{21}).
\tag{30.1}
$$

若保留同一旧行及已识别角内值，完整PB和P2就要求 $T=A\circ(d-K(p,A))$ 满足23.7。可是直接有限乘法给

$$
Te_3=\tfrac\varepsilon2e_1+\varepsilon e_2\ne0.
$$

$e_3\in L^\perp$，故这违反23.7必有的 $Te_3=0$。这项延拓障碍不依赖给剩余外层指定某份新公式，也不把OP100.1对一个指定延续的失败冒充一般全域反模型。

**边界 30.3（结清范围和仍未支付的桥）。** 本文在AH12.2的三阶完整局部平凡复矩阵截面域中给出全部实际旧值的纸面证明；AH21.2中关于这一具体域的三阶原值缺口由26.2接续。旧角、全部实际标签、准确原锥／单位／范数、每份评价和全部质量保持。底空间不要求可度量、局部连通、稠密开闭点、全局矩阵单位或全局Hilbert向量丛。

一般有限商原像目标OP85.1仍未由这里的完整截面构造结清：一般原域不保证实际逆Cayley输入、支撑在图内的全体演员及其全部有限前缀都属于原域。本证明不把任意稠密不完整域替换为其完成，不预付商下降，也不主张对这些域有完整PB反模型。一般JB、type II／III、非局部平凡、变阶、混合或退化层仍须各自的实际类型、取向、分离及原输入接线；已有其他前件下的结论保持其原范围，不被降回未证明。

点上可选正化酉不等于两份全局截面可由同一连续酉相接，更不等于全局酉轨道闭包一致；SQ既有同Gram拓扑障碍保留。若允许空底空间和零单位，则另取零代数及唯一零响应，全部式为空断言，不作正质量归一。

26.2不生产原具名准备、控制、完整菜单、相关联合、整台递归参考、完整仪器、活动ready／接受输出／第一合法消费者、真遗忘、全未来真实双向返回、无限记录或物理钟。28节全文中未供应的实际来源，仍是相应具名producer或来源义务。本文给出的证据为条件定义和有限纸面证明，不声称独立评审完成、Lean／kernel核验、物理起源、文献穷尽、历史优先权或外部开放问题结算。

## 31. 简洁关系几何与完整白话

**关系图景 31.1。** 核心可以写成一条有限关系链：

$$
\begin{gathered}
\text{全部实际二阶角及共同旧取向}\\
\Downarrow\quad\text{两份秩一第三标签，迫使同一横向像落入两条正交射线}\\
\text{零射线对角的全幅原行}\\
\Downarrow\quad qWq=0\text{使侧面演员的两份逆Cayley槽始终零对角}\\
\text{至多四步对齐左右腿，认回实际箭头}\\
\Downarrow\quad\text{原PB自身的两份外层恰为局部箭头}\\
\text{局部秩一演员的任意实际旧行}\\
\Downarrow\quad\text{至多六步保持原W，抵达它自己的点上正终点}\\
\text{同一个旧 }D=K_Q.
\end{gathered}
$$

两两比较给每条实际边的正预算；三标签PB要求不同边、同一内值及其真实外层相容。23.7是这份相容性的具体有限表达，不能由“每条边各有一种解释”代替。比较反向时的Hermitian相容、交换强度与有向反号，以及规定接法的恒等式，都不表示实际仪器先后可交换。按CO60，严格复合也不独自给路径独立或闭路恒等；非零中心相位类不是量子性的必要条件。本文没有以这些较强或不正确的筛选替代原PB。

**完整白话 31.2。** 可以把原问题看成同一个世界已经有的一张比较表：两件实际对象送进去，它给一份带方向的答案。每对对象的预算为正还不够；把第三件对象接进来，正反两种规定接法也必须给出同一个结果。我们早已知道，只要比较真正落在同一个二维窗口，旧答案就有一个由旧表自己选定的方向。三维的困难是，一份箭头的进路和出路可以不同，所以它虽只有两条腿，也未必能直接放进同一个二维窗口。现在先看一种特殊但足够有用的行：第一件对象只沿一条射线，第二件对象在这条射线上的自身读数恰为零。给它分别接上两件明确的第三对象，一件沿二维窗口中的第一条射线，一件沿与它正交的另一条射线；它们带着准确的正负号和旧取向。两次接法并不更换原来的未知答案，而是同时约束它的同一个横向误差：这个误差乘上同一第二对象后，既只能指向第一条射线，又只能指向第二条射线，于是只能为零。这样就认回这类行的全部幅度和背景。随后，把一份真实箭头放在图内，沿它侧面的二维空间旋转；每一步的两份实际内标签在演员射线上始终零对角，所以操作由开到关的整个过渡圈都有依据，原输入从未被剪掉。最多四步把列腿转到行腿的方向，这份实际终点才真正进入已认识的二维窗口，旧答案就能沿原接法传回来。再看任意局部秩一演员的一次原配平，它自己的两份真实外层恰好都是这种箭头，因此这名演员面对任意实际第二输入的旧行都被认回。到这时才有权使用任意局部秩一相位；针对任意原输入和指定点，至多六步就把同一份输入送到一个在该点为正的实际终点。终点自己的虚部在该点为零，原正预算使它自己的响应为零，再沿同一有限链传回最初旧值，整张旧表遂被认回。线性、局部性和同一个结合乘法是这之后的结论。这份简化把第四条额外零方向换成三维内部两条互斥射线的共同约束，没有减少原关系或实际来源；数学表示、相位和有限链仍不制造准备设备、完整菜单、真正相关联合、整台过程的所有未来、真实返回、物理钟或共同正作用量，七项全文合同必须在原世界逐项齐备。

[N3-AH]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_ORIGINAL_ATOMIC_SEPARATION_AND_PB_RECONSTRUCTION_CONTINUATION.md
[N3-OP]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md
[N3-SQ]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_ZERO_DIMENSIONAL_CENTER_SQUARE_ORBIT_RECONSTRUCTION.md
[N3-AQ]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md
[N3-CO]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_FIB_COMPARISON_ORDER_AND_POSITIVITY_BOUNDARIES_CONTINUATION.md

## 追加锚（本行以下为增补区）

## 32. 含单位 subhomogeneous 原域中的同一旧响应

**约定 32.1（固定正文与证明级别）。** 本增补接续承载卷12–21及三阶增补22–31，从32起编号。AH、OP、SQ、AQ、CO分别指文末固定链接中的承载卷、《原多项式零响应与 Cayley 原域边界》、《零维紧中心的同一原响应与平方酉轨道闭包分类》、《任意维静态量子重构》及《二元比较、操作顺序与正性条件的边界》；读取版本均为 `2addd6f369b7387226c2b0cc984623dd3efe40a1`。各文自身递归纳入的版本身份仍按原文，不改钉版本。

N3指已固定三阶正文22–31：所消费文件为 `two-ray-n3-final.md`，693行，SHA256为 `92d56bfad95fceb174b4ef2f1b85d654eb01dc32ee7a424b007172f3e24230f3`；公开承载正文位于文末[N3链接][SH-N3]。这里只消费其数学前件及证明，不以任何评审结论代替前件。本增补是纸面条件证明，不是Lean或kernel核验。

**定义 32.2（完整原模型）。** 固定含单位复C*代数 $A$，每个不可约表示维数不超过某个有限整数 $d$。原静态域准确为

$$
E=A_{\rm sa},\quad S(a,b)=a\circ b=(ab+ba)/2,
\quad C=A_+,\quad u=1,\quad N(a)=\|a\|.
\tag{32.1}
$$

原正实线性评价族 $\mathcal P$ 分离 $E$，并准确决定 $C$。保留同一个原世界、全部原标签、评价及质量 $m_\gamma=\gamma(u)$，包括零、不等、次归一质量及原表示意义下的非正常评价。未知 $D:E^2\to E$ 是同一给定总映射。

记 $\mathsf H_A(D)$ 为以下完整原关系的合取。A1/P2对全部实际 $a,b$、两种次序和全部原评价要求

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(b\circ a)-i\gamma D(b,a)&\gamma(b^2)
\end{pmatrix}\succeq0.
\tag{32.2}
$$

A2是全部相加三表 $(a+b,a,b)$ 及全部排列的实部在整个 $\mathbb R^3$ 上半正定，指定相加向量 $(1,-1,-1)$ 及相应排列准确给零。A3保留 $u^2=u$ 和同一固定有理 $0<\vartheta\le1$ 上全部 $0\le e\le\vartheta u\Rightarrow e^2\le e$。不预给复三表正性。

对全部实际 $h,a,b\in E$，仍由同一个旧 $D$ 定义

$$
v=D(h,a)-h\circ b,\qquad w=h\circ a+D(h,b),
\qquad r_\pm=a\pm v,\quad s_\pm=b\pm w.
$$

完整PB要求全部原评价满足

$$
\gamma(r_+^2+s_+^2+2D(r_+,s_+))
=\gamma(r_-^2+s_-^2+2D(r_-,s_-)).
\tag{32.3}
$$

零、重复、任意幅度、缩放、平移、任意背景和所有实际嵌套调用均在量词内。由评价分离，PB等价于其元素等式；消去已知Jordan平方后也等价于

$$
D(a+v,b+w)-D(a-v,b-w)=-2a\circ v-2b\circ w.
\tag{32.4}
$$

证明前不输入 $D$ 的可加、齐次、连续、可测、局部、协变、商下降或理想保持。完整 $A_{\rm sa}$ 是实质前件；以下逆元、精确提升和全部前缀都在此原域中构造。

**定理 32.3（同一原表的分类）。** 设 $I$ 为 $A$ 中交换子生成的闭双边理想，$U=\operatorname{Prim}(I)$，按理想的标准开嵌入视为 $\operatorname{Prim}(A)$ 的非交换部分。若 $I\ne0$，则

$$
\boxed{\quad
\mathsf H_A(D)
\ \Longleftrightarrow
\exists!Q\in Z(M(I)):\quad
Q=Q^*,\ Q^2=1_{M(I)},\quad
D(a,b)=Q\,\frac i2[a,b]\quad(a,b\in E).
\quad}
\tag{32.5}
$$

右式的乘子只作用于属于 $I$ 的交换子，输出属于原 $A_{\rm sa}$。等价地，$Q$ 对应 $U$ 上唯一连续二值取向 $\sigma:U\to\{\pm1\}$。不要求该取向延拓到整个 $\operatorname{Prim}(A)$，也不要求 $Q\in Z(A)$。若 $I=0$，分类为唯一 $D=0$，取向为唯一空函数。

特别地，对每个不可约 $\pi:A\to M_n(\mathbb C)$，当 $n\ge2$ 时存在一个输入无关的 $\sigma_\pi$，使全部实际原输入满足

$$
\pi D(a,b)=\sigma_\pi\frac i2[\pi a,\pi b].
\tag{32.6}
$$

这就是本任务的FM结论；它不列入任何新增假设。$n=1$ 时全部实际旧输出像为零。证明见33–39。

## 33. 正预算、实际理想支撑及有限齐次过滤

**接口 33.1（同一实际输出的正读取）。** 准确复用SQ31.2、AH13.1：原二表的Hermitian性和评价分离给

$$
D(a,b)=-D(b,a).
$$

对固定复系数，二表的二次型是原自伴元素；它被所有原评价读为非负，准确锥使它为正。因此每个数学正泛函都能读取同一P2。对 $A_0=\pi a,B_0=\pi b,\delta=\pi D(a,b)$，任意向量 $\xi$ 有

$$
|\xi^*\delta\xi|^2\le
\|A_0\xi\|^2\|B_0\xi\|^2
-(\operatorname{Re}\langle A_0\xi,B_0\xi\rangle)^2.
\tag{33.1}
$$

一个输入像为零，便由零预算和Hermitian极化得到这个实际输出像为零。对一维 $\pi$，右侧对全部输入恒零，故 $\pi D(a,b)=0$。若 $\pi r=\mu p$、$p$ 秩一、$q=1-p$，则

$$
q\,\pi D(r,a)\,q=0.
\tag{33.2}
$$

以上都没有将实际输入替换为同像代表，也没有除以原质量。

**引理 33.2（实际首槽的理想吸收）。** 对任意闭双边理想 $L\triangleleft A$，有

$$
r\in L_{\rm sa},\ a\in E\quad\Longrightarrow\quad D(r,a)\in L_{\rm sa}.
\tag{33.3}
$$

证明。每个消去 $L$ 的不可约表示都使 $\pi r=0$；33.1给同一实际 $\pi D(r,a)=0$。C*商的不可约表示分离其元素，故输出属于 $L$。这只证明一槽吸收，不证明一般核平移不变性。∎

**定义 33.3（合法的层与实际提升）。** 按亲读的Thiel–Vilalta §4.3，置

$$
I_{\ge k}=\bigcap_{\dim\pi<k}\ker\pi,\qquad
I_{\ge1}=A,\quad I_{\ge d+1}=0,\qquad
B_k=I_{\ge k}/I_{\ge k+1}.
\tag{33.4}
$$

$B_k$ 是 $k$-齐次C*代数，可能为零；非零时是某局部紧Hausdorff空间 $X_k$ 上局部平凡 $M_k$-丛的 $C_0$ 截面代数。该文明确将结构结果引至Blackadar IV.1.4、IV.1.7。

记 $n(P_\pi)=\dim H_\pi$ 为不可约表示的矩阵阶数。理想的不可约谱对应和这条有限过滤给

$$
U_k:=\operatorname{Prim}(I_{\ge k})
=\{P\in\operatorname{Prim}(A):n(P)\ge k\},
\qquad X_k=U_k\setminus U_{k+1}.
\tag{33.5}
$$

确切理由是：对非零理想的不可约限制仍不可约；逐层谱分解将 $U_k$ 分成阶数 $k,k+1,\ldots,d$。另一方面，$A/I_{\ge k}$ 是阶数小于 $k$ 的各齐次层的有限扩张，不可能有更高阶不可约表示。因此 $U_k$ 正是所写开集，$X_k$ 的子空间拓扑正是 $\operatorname{Prim}(B_k)$。

任意实际 $a\in A$ 通过左右乘法作用于 $B_k$，给保单位星同态 $A\to M(B_k)$。故 $a_x=\pi_x(a)$ 在每个 $X_k$ 图中是有界连续矩阵函数，即使 $a\notin I_{\ge k}$。这可在每个点附近乘一份等于单位的紧支撑局部单位截面验证。这里使用的是已知C*乘法的乘子作用，不是未知 $D$ 的商下降。

给定一张图 $O\subset X_k$、实 $g\in C_c(O)$ 和常值自伴矩阵 $T$，图内 $gT$、图外零是一份 $B_k$ 自伴截面。商映射的满性供应一份精确自伴提升

$$
t\in(I_{\ge k})_{\rm sa},\qquad t_x=g(x)T\quad(x\in X_k).
\tag{33.6}
$$

不要求提升为幂等元或乘法截面。在高层它可有任意矩阵像；在低层它必为零。以下会分别支付这些分量。

**接口 33.4（原像角与方向）。** 每个有限维不可约 $\pi$ 是满复星同态，自伴限制是满Jordan商。将OP80.1–80.2、82.1代入 $X_{\rm JB}=E=A_{\rm sa}$、恒等包含及此单块商，得到：对每个 $n\ge2$，该不可约表示的全部二阶角共用一个唯一符号 $\sigma_\pi$；只要两份实际输入像共同支撑于一个秩至多二角，便有32.6。量词包含所有实际代表和任意角内标量部分。

此刻只定义角符号，不定义商上的 $D_\pi$。阶数二时，整个矩阵域就是这个角，因而FM已直接成立；阶数一由33.1处理。

## 34. 只在已付高层和当前角上拼出理想乘子

**引理 34.1（下降一步所需的取向）。** 固定 $k\ge3$，假设FM已对所有阶数大于 $k$ 的不可约表示、全部实际输入成立。则角符号在整个 $U_k$ 连续，因而存在唯一

$$
Q_k\in Z(M(I_{\ge k})),\qquad
Q_k=Q_k^*,\quad Q_k^2=1,
\quad \widetilde\pi(Q_k)=\sigma_\pi I\quad(P_\pi\in U_k).
\tag{34.1}
$$

空理想按空谱处理。符号在 $U_{k+1}$ 的连续性可以取前一步所得结论；也可在 $I_{\ge k+1}$ 内选一对交换子在给定高层点非零的实际标签，直接对高层FM用下述零集论证得到。最高层从空集开始。

证明。只需处理任意 $x_0\in X_k$。在一张局部平凡图内选实bump $f\in C_c(O)$，在 $x_0$ 附近为一。取局部二阶角内两份自伴常矩阵 $H,T$，使 $i[H,T]/2\ne0$，将 $fH,fT$ 分别提升成实际 $a,b\in(I_{\ge k})_{\rm sa}$。置

$$
c=\frac i2[a,b]\in(I_{\ge k})_{\rm sa},\qquad
z=D(a,b)\in(I_{\ge k})_{\rm sa}.
\tag{34.2}
$$

第二个归属由33.2给出。在全部阶数 $k$ 的表示，所选输入像在同一二阶角或为零，33.4给 $\pi z=\sigma_\pi\pi c$；在全部更高阶表示，这个等式由归纳假设给出。因此它在整个 $U_k$ 成立，且 $\pi_{x_0}c\ne0$。

在 $\operatorname{Prim}(I_{\ge k})$ 内，元素零集

$$
Z(t)=\{P:t\in P\}
$$

是闭集。令 $V_c=U_k\setminus Z(c)$。在这个开集上，正、负符号集分别是

$$
V_c\cap Z(z-c),\qquad V_c\cap Z(z+c).
\tag{34.3}
$$

它们互斥、并集为 $V_c$，且都相对闭，故也都相对开。这给覆盖 $x_0$ 的真正谱开邻域，而不只给 $X_k$ 内的相对邻域。它同时检验了高层逼近当前层时的方向相容性。与已知开集 $U_{k+1}$ 合并，角符号在 $U_k$ 连续。

应用Dauns–Hofmann同构

$$
C_b(\operatorname{Prim}(L))\cong Z(M(L)),\qquad
\Phi(f)t-f(P)t\in P,
\tag{34.4}
$$

其中 $L=I_{\ge k}$，得到34.1。所用准确陈述来自亲读开放全文Forger–Paulino的定理2；只用这一经典同构，不消费其局部C*推广。∎

**说明 34.2（没有预付当前层FM）。** 34.2中的全谱等式只对特别选出的那一对实际角标签成立；更高层由已成FM承担。没有对当前层任意 $a,b$ 假定公式。符号乘子只属于 $M(I_{\ge k})$，不在此声称它能乘任意原 $a$ 后仍返回 $A$。

## 35. 保留实际负端点的理想内逆 Cayley 接线

**定义 35.1（已知比较行）。** 在34.1的下降步骤中，简记 $L=I_{\ge k}$、$Q=Q_k$。对 $r\in L_{\rm sa}$、$a\in E$，定义已知辅助值

$$
\Lambda(r,a)=Q\frac i2[r,a]\in L_{\rm sa}.
\tag{35.1}
$$

$A$ 通过乘子作用于 $L$，而中央 $Q$ 与该作用交换，故所有表达式合法。$\Lambda$ 是已知比较交换子，不替换尚未识别的旧 $D$。

**引理 35.2（原 $A$ 中的精确逆标签）。** 固定任意实际当前对 $(a,b)\in E^2$ 和任意 $r\in L_{\rm sa}$。置

$$
H=(u+r^2)^{-1}\in A_{\rm sa},\qquad R=rH\in L_{\rm sa},
\qquad H-u\in L_{\rm sa},
$$

$$
\begin{aligned}
X&=H\circ a-R\circ b+\Lambda(R,a)+\Lambda(H-u,b),\\
Y&=R\circ a+H\circ b-\Lambda(H-u,a)+\Lambda(R,b),\\
v_0&=\Lambda(r,X)-r\circ Y,\qquad
w_0=r\circ X+\Lambda(r,Y).
\end{aligned}
\tag{35.2}
$$

这些都是实际原元素，并且在整个原 $A$ 有

$$
X-v_0=a,\qquad Y-w_0=b.
\tag{35.3}
$$

证明。在 $P_\pi\in U_k$ 记 $\jmath_\pi=i\sigma_\pi$。35.2就是把下式取普通自伴实部和 $\jmath_\pi$-虚部：

$$
\pi X+\jmath_\pi\pi Y
=(I-\jmath_\pi\pi r)^{-1}(\pi a+\jmath_\pi\pi b).
\tag{35.4}
$$

这由 $(I-\jmath_\pi\pi r)^{-1}=(I+\jmath_\pi\pi r)\pi H$ 直接展开；$H$ 的交换子等于 $H-u$ 的交换子，故35.2没有让 $Q$ 作用于理想外元素。再有

$$
\pi v_0+\jmath_\pi\pi w_0
=\jmath_\pi\pi r(\pi X+\jmath_\pi\pi Y),
$$

给出35.3的像。在 $U_k$ 外，$\pi r=\pi R=\pi(H-u)=0$，35.2直接给 $\pi X=\pi a,\pi Y=\pi b,\pi v_0=\pi w_0=0$。全部不可约表示分离原元素，故35.3为真正原元素等式。这里没有读取或展开未知 $D$。∎

**引理 35.3（必须先支付的两内行与实际前缀）。** 如果35.2的两份实际输入已经满足全原等式

$$
D(r,X)=\Lambda(r,X),\qquad D(r,Y)=\Lambda(r,Y),
\tag{35.5}
$$

则对原PB $(r;X,Y)$，负端点准确为原 $(a,b)$，正端点为实际

$$
(a',b')=(X+v_0,Y+w_0)=(2X-a,2Y-b).
\tag{35.6}
$$

对每个 $P_\pi\in U_k$，令

$$
\mathcal E_\pi(a,b)=\pi D(a,b)-\sigma_\pi\frac i2[\pi a,\pi b].
$$

这只是对每次实际调用定义的读数，不是商上的函数。则

$$
\mathcal E_\pi(a',b')=\mathcal E_\pi(a,b).
\tag{35.7}
$$

证明。35.5使真正PB位移就是 $v_0,w_0$，故负端点由35.3准确给出。令 $Z=\pi a+\jmath_\pi\pi b$。正端点复标签是

$$
Z'=C_{\pi,r}Z,\qquad
C_{\pi,r}=(I+\jmath_\pi\pi r)(I-\jmath_\pi\pi r)^{-1}.
\tag{35.8}
$$

$C_{\pi,r}$ 酉，故 $Z'^*Z'=Z^*Z$。另一方面，原PB给两份 $a^2+b^2+2D(a,b)$ 相等，而

$$
Z^*Z=\pi(a^2+b^2)+\sigma_\pi i[\pi a,\pi b].
$$

相减得到35.7。只有两内行在整个原 $A$ 支付后才调用这一步。在低层，即便两端点只有像相同，也不能以此宣布旧值相同；原PB才是旧值运输的依据。∎

**支付规则 35.4（每一个前缀都用同一规则）。** 以下演员属于 $L$，其在当前 $X_k$ 的像支撑于一张图。对每一份实际逆标签 $T=X,Y$，证明35.5的逐表示支付如下：

| 不可约表示 | 对同一实际 $(r,T)$ 的依据 |
| --- | --- |
| 阶数小于 $k$ | $\pi r=0$，33.1给旧输出零，$\Lambda$ 的像亦零。 |
| 阶数 $k$，图外或演员像为零处 | 同一首槽零预算。 |
| 阶数 $k$，图内活跃处 | 先用36.1的零射线对角行；取得37.2后才可用全幅秩一行。 |
| 阶数大于 $k$ | 归纳FM覆盖任意实际 $T$ 和演员的任意高层矩阵像；34.1保证 $Q$ 符号正是该FM符号。 |

全部表示都付清后，才由分离性得35.5的两条原元素等式。演员从开到关的整个过渡带、任意原背景和每一份实际前缀均按此支付。既不要求高低层同号，也不丢弃提升的高层尾部。

## 36. 两射线原像证明的维数无关接口

**引理 36.1（复用N3 23.1的准确原像适配）。** 对任意有限维不可约满商 $\pi:A\to M_n$，$n\ge2$，任意实际 $r,a\in E$，若

$$
\pi r=\mu p,\qquad p=ee^*,\qquad p(\pi a)p=0,
\tag{36.1}
$$

则 $\pi D(r,a)=\sigma_\pi i[\pi r,\pi a]/2$。任意幅度及补角背景保留；不要求 $r$ 属于某个理想。

证明。直接消费N3 23.1的两射线证明，但需核对它在这里的维数与标签前件。该证明只在一次固定有限商内计算，所用所有第三标签都可由满 $\pi$ 精确自伴提升。全部PB仍先在原 $A$ 调用，全部外层由33.1和OP80.2读取；因此没有要求 $A$ 本身是完整矩阵丛。

以下列出该证明中承担维数适配的等式。记 $q=1-p$、$\jmath=i\sigma_\pi$，写

$$
\pi a=H(z)+B,\quad H(z)=ze^*+ez^*,\quad z\perp e,\quad B=qBq,
\qquad \pi D(r,a)=\delta p+H(w).
\tag{36.2}
$$

这由33.2给出。$\mu=0$ 用零预算；$z=0$ 时，原PB $(a;r,0)$ 的第二外槽像为零，给 $\mu p\circ(\delta p+H(w))=0$，结论亦成立。其余令 $t=\|z\|$、$f=z/t$、$V=\operatorname{span}\{e,f\}$，取

$$
u_\epsilon=(e-\epsilon\jmath f)/\sqrt2,\quad P_\epsilon=u_\epsilon u_\epsilon^*,
\qquad C_\epsilon=\epsilon 2tP_\epsilon,
\qquad \epsilon=\pm1.
\tag{36.3}
$$

实际第三标签 $c_\epsilon$ 只须满足 $\pi c_\epsilon=C_\epsilon$。原 $(r,c_\epsilon)$ 两像同在角 $V$，OP80.2识别其旧内值。对 $\operatorname{PB}(r;a,c_\epsilon)$，其实际第二位移的像为零，第一位移的像为

$$
\Delta-\epsilon\mu t p,\qquad
\Delta=\pi D(r,a)-\frac\jmath2[\mu p,\pi a].
$$

两份实际第二外槽像均为 $C_\epsilon$。各自P2经 $R_\epsilon=1-P_\epsilon$ 压缩原PB；因 $(\pi a)\circ p=H(z)/2$ 且两条射线上 $u_\pm^*H(z)u_\pm=0$，有 $R_\epsilon((\pi a)\circ p)R_\epsilon=0$。于是准确得到N3 23.6–23.7：

$$
R_\epsilon\bigl((\pi a)\circ\Delta\bigr)R_\epsilon=0
\qquad(\epsilon=\pm1).
\tag{36.4}
$$

对任意 $\xi\in V^\perp$，同一个 $((\pi a)\circ\Delta)\xi$ 同时属于两条正交射线，故为零。其 $q$ 分量正是 $zw^*\xi/2$；任意 $B$ 的项在这个压缩中消去。因此 $w\perp V^\perp$，即 $w\in\mathbb Cz$。这是唯一涉及补空间维数的一步，在任意有限 $n$ 都成立；$n=2$ 时该结论已自动成立。

现在原PB $(a;r,0)$ 的两对真实外层像

$$
(\mu p-\pi D(r,a),\ \mu p\circ\pi a),\qquad
(\mu p+\pi D(r,a),\ -\mu p\circ\pi a)
$$

才共同支撑于 $V$。用OP80.2识别这两份实际旧输出，N3 23.9给

$$
\mu p\circ\Delta=0.
$$

而 $\Delta\in\mathbb Rp+H(q\mathbb C^n)$，$\mu p\circ$ 在此空间上对 $\mu\ne0$ 单射，故 $\Delta=0$。整个论证没有对未知 $D$ 拆和或换同像代表。∎

## 37. 当前层的实际箭头与全部秩一提升

**引理 37.1（允许高层尾部的局部箭头）。** 在34.1的下降步骤中，取 $O\subset X_k$ 的一张矩阵图、常值秩一 $p=ee^*$、$q_0=1-p$。若实际 $(a,b)\in E^2$ 在整个 $O$ 满足

$$
q_0a_xq_0=q_0b_xq_0=0,
\tag{37.1}
$$

则对每个 $x_0\in O$，$\mathcal E_{\pi_{x_0}}(a,b)=0$。原标签的图外像、高层像与低层像任意保留。

证明。复用N3 24.2的侧面相位机制，以下支付其新的实际提升。对任意常值秩一 $s\le q_0$、实 $\lambda\in C_c(O)$，先精确提升 $\lambda s$ 为 $t\in L_{\rm sa}$，再取实际演员

$$
r=Q_kt\in L_{\rm sa}.
\tag{37.2}
$$

在当前层，$r_x=\sigma_x\lambda(x)s$。对任意当前实际对，35.4的有向复标签在 $O$ 内满足

$$
X_x+i\sigma_xY_x
=(I-i\lambda s)^{-1}(a_x+i\sigma_xb_x).
\tag{37.3}
$$

该左因子与 $p,q_0$ 交换，故37.1保持，且

$$
sX_xs=sY_xs=0.
\tag{37.4}
$$

图内两内行逐点由36.1支付；图外、低层用零预算，高层用归纳FM，恰是35.4。于是先有35.5的全原两等式，才有35.7。正前缀的有向复标签左乘Cayley酉，也保持37.1。这支付整个 $\lambda$ 过渡带，不要求任何小连接阈值。

在指定点，相对 $\mathbb Ce\oplus q_0\mathbb C^k$ 写

$$
Z=a_{x_0}+i\sigma_{x_0}b_{x_0}
=\begin{pmatrix}\alpha&\beta^*\\c&0\end{pmatrix}.
\tag{37.5}
$$

若 $\beta=0$ 或 $c=0$，两份自伴标签已同在秩至多二角，直接用33.4。否则选 $V\in U(k-1)$，使 $Vc=\kappa\beta$、$\kappa=\|c\|/\|\beta\|>0$。有限酉谱定理给

$$
V=\prod_{j=1}^{k-1}e^{i\theta_js_j},\qquad
s_j\le q_0\text{ 秩一},\quad\theta_j\in[-\pi,\pi].
$$

取 $0\le h\le1$、$h\in C_c(O)$，在 $x_0$ 附近为一。对每个 $j$，把

$$
\lambda_j=\tan(\theta_jh/4)
\tag{37.6}
$$

代入37.2，使用同一实际演员两次。参数有界，商截面确实属于 $B_k$，精确提升存在；无需控制其高层矩阵秩。每次在当前层的Cayley酉为 $e^{i\theta_jh s_j/2}$。至多 $2(k-1)$ 个实际前缀都满足37.1，每一步都重新按35.4支付两内行并应用真正PB。终点在 $x_0$ 的标签为

$$
\begin{pmatrix}\alpha&\beta^*\\\kappa\beta&0\end{pmatrix},
$$

其两自伴标签共同支撑于 $\operatorname{span}\{e,\beta\}$。33.4认回这份实际终点自己的旧输出；35.7沿实际有限链返回，得到结论。没有把“秩至多二”误作“共同二阶角”，也没有要求全局连续选择 $V$。∎

**定理 37.2（局部秩一截面的任意实际提升，全幅原行）。** 在同一步骤中，若实际 $r\in L_{\rm sa}$ 在当前齐次层恰为某图内 $gp$、图外零，其中 $g\in C_c(O,\mathbb R)$、$p$ 常值秩一，则

$$
D(r,a)=\Lambda(r,a)\qquad(a\in E).
\tag{37.7}
$$

这里量化所有这样的实际提升，其高层尾部任意；$g$、第二输入幅度、射线对角及补角背景都不受限。

证明。保留实际 $z=D(r,a)$、$j=r\circ a$，它们由33.2属于 $L$。原PB $(a;r,0)$ 的两份真实外层准确为

$$
(r-z,j),\qquad(r+z,-j),
$$

并给

$$
D(r-z,j)-D(r+z,-j)=2r\circ z.
\tag{37.8}
$$

在整个图内，33.2的秩一压缩给 $q_0z_xq_0=0$，Jordan乘法给 $q_0j_xq_0=0$。因此这两份实际外层都满足37.1；37.1逐点识别它们各自的旧输出。在当前层图外，$r_x=0$ 使 $z_x=j_x=0$，同一零预算识别外层。

固定当前一点，记 $R_0=\mu p,A_0=a_x,z_0=z_x$，只对已识别的比较交换子展开37.8，得

$$
2R_0\circ z_0
=K_x(R_0-z_0,R_0\circ A_0)-K_x(R_0+z_0,-R_0\circ A_0)
=2R_0\circ K_x(R_0,A_0),
\tag{37.9}
$$

其中 $K_x=\sigma_x i[,]/2$，末等式使用 $R_0^2=\mu R_0$。当 $\mu\ne0$，33.2使差值属于 $\mathbb Rp+H(q_0\mathbb C^k)$，$R_0\circ$ 在此空间单射；当 $\mu=0$，直接用零预算。因此当前层全幅行已识别。

在高层，归纳FM识别同一 $(r,a)$，且34.1使其等于 $\Lambda$；在低层首槽为零。全部不可约表示分离，得到37.7的原元素等式。此处全幅行由箭头外层取得，箭头运输只用了更早的零射线对角行，没有循环。∎

## 38. 有限下降支付任意实际输入，取得FM

**定理 38.1（当前层原目标的有限点上正化）。** 在34.1的归纳前件下，任取实际 $(a,b)\in E^2$、任取 $x_0\in X_k$，存在不超过 $2k$ 个实际演员及实际正前缀

$$
(a_0,b_0)=(a,b),\ (a_1,b_1),\ldots,(a_m,b_m),
$$

每步都准确由35.2–35.6构造、全原两内行由37.2支付，并满足

$$
\mathcal E_{\pi_{x_0}}(a_m,b_m)=\mathcal E_{\pi_{x_0}}(a,b),
\qquad a_{m,x_0}+i\sigma_{x_0}b_{m,x_0}\ge0.
\tag{38.1}
$$

证明。只对固定矩阵 $Z=a_{x_0}+i\sigma_{x_0}b_{x_0}$ 取SVD，选普通酉 $V$ 使 $VZ\ge0$，包括奇异及零矩阵。将 $V$ 谱分解成至多 $k$ 个秩一相位，像37.6那样对每个相位取两次实际演员；其当前层像为 $\sigma_x\tan(\theta_jh(x)/4)p_j$。实际演员由33.6提升后乘 $Q_k$ 得到。

34.1使当前层的实系数 $g(x)=\sigma_x\tan(\theta_jh(x)/4)$ 属于 $C_c(O,\mathbb R)$，故演员确实在37.2的量词内；不要求图内符号常值。每一步的任意当前逆标签 $X,Y$ 都属于原 $E$。37.2已对这名实际演员和所有实际第二输入给原元素等式，故两内行确实在全部原 $A$ 支付；随后35.3保持旧误差。至多 $2k$ 步的点上总左因子恰为 $V$。原 $(a,b)$ 是第一步准确负端点，后续负端点逐步准确是上一份实际前缀。∎

**定理 38.2（FM的下降证明）。** 对全部不可约表示和全部实际原输入，32.6成立。

证明。从最高可能阶数 $d$ 向下降。假设所有阶数大于 $k\ge3$ 已识别。34.1先从当前角内旧值及高层FM构造 $Q_k$，35节给不依赖旧值识别的精确逆标签，36–37依次给零射线行、实际箭头和局部秩一全幅行；这些前件才允许38.1运输任意原目标。

38.1的实际终点在 $x_0$ 为正，故其自己的 $b_{m,x_0}=0$。33.1对这份实际调用给 $\pi_{x_0}D(a_m,b_m)=0$，比较交换子也为零。因此由38.1得 $\mathcal E_{\pi_{x_0}}(a,b)=0$。$a,b,x_0$ 任意，当前阶数全部识别。最高层的高层前件为空；空层无需演员。

阶数二已由33.4的全部实际二阶角定理识别，阶数一由33.1识别。若 $d\le2$，直接从这两项结束。因此有限下降完成FM，没有先定义任何当前层商响应。

每一步取得FM后，下一步才将它用作高层支付。整个依赖次序为

$$
\text{高层FM及当前旧角}
\Rightarrow Q_k
\Rightarrow\text{精确实际逆标签}
\Rightarrow\text{零射线行支付箭头}
\Rightarrow\text{箭头支付全幅秩一行}
\Rightarrow\text{原目标自己的正终点}
\Rightarrow\text{当前FM}.
$$

不存在把“FM若成立”塞入同层假设的环。∎

**推论 38.3（原像身份与有限商）。** FM后，对每个不可约 $\pi$，两槽的全部核平移不变性才成为结论。对任意有限维复星商 $\Pi:A\to\bigoplus_jM_{n_j}$，逐分量得OP85.1的全域公式及全部实际代表无关性。此时才能定义相应商响应，并继承全部原PB。

这补上本完整subhomogeneous域中的OP85.2旧值缺口。它不证明一般JB或不完备原域的OP85.2，也不把普通同点代表相等当作证明。有限步数是对每个固定目标、固定层点的构造上界，不声称一份有限全局菜单可认证全部原全称关系。

## 39. 非交换primitive谱、双向分类与交换边界

**定理 39.1（全局识别及唯一性）。** 交换子闭理想恰为 $I=I_{\ge2}$：其商是最大交换商，交换商的字符分离，故其核正是所有一维表示核的交。其非零不可约表示恰对应原阶数至少二的表示。

FM后，对任意实际 $a,b$，置 $z=D(a,b)$、$c=i[a,b]/2$。所有字符消去 $z$，故 $z,c\in I$；38.2给整个 $U$ 上 $\pi z=\sigma_\pi\pi c$。对任意非交换点可由满商选 $c$ 在该点非零。使用34.3同一输出的两个hull零集，正负符号集在这些开集上都开，故 $\sigma$ 在整个 $U$ 连续。Dauns–Hofmann给唯一 $Q\in Z(M(I))$。FM和不可约分离随即给

$$
D(a,b)=Q\frac i2[a,b].
\tag{39.1}
$$

这是先取得FM、再认回原元素的完整结算；34节的中间乘子只服务于有限下降。唯一性来自每个非交换点的一份非零交换子及满实际提升。交换点上没有可见的符号，不增加唯一性数据。

**定理 39.2（逆向无需额外边界条件）。** 任取 $U$ 上连续二值函数，由Dauns–Hofmann取得 $Q\in Z(M(I))$。39.1定义的总映射返回原 $E$，并满足32.2的全部原A1–A3/P2/PB。

证明。中央自伴乘子保持 $I$ 及伴随，故输出合法。每个阶数至少二的不可约像是通常或相反乘法的响应；字符像为零。原二表的任意复二次型在每个不可约像都是相应的 $Z^*Z$ 或 $ZZ^*$，因而在 $A$ 为正，所有原评价的P2成立。A2的实相加Gram和指定零方向来自同一Jordan积，A3来自原C*谱序。

对任意实际三元组，先用39.1计算它的真正内值和真正外层，再由每个不可约表示读取。固定 $\sigma=\pm1$ 时原PB就是通常或相反C*乘法中的平方配平恒等式，准确复用N3 26.3、AH17.4及AQ23.1的既有逆向；字符上则两边为同一个标量平方。全部不可约表示分离，故原PB元素等式成立，再由全部原评价读取。没有把两端实际标签换成另取的代表。于是32.5双向成立。∎

**反事实 39.3（要求符号跨交换边界延拓会错删合法模型）。** 取

$$
A=\{f\in C([-1,1],M_2):f(0)\in\mathbb CI_2\}.
\tag{39.2}
$$

其非交换谱为两个半区间 $[-1,0)\sqcup(0,1]$，原点是一个字符。$I=\{f:f(0)=0\}$。在左右两侧分别取 $Q=-1,+1$，它是 $Z(M(I))$ 的自伴酉，却不能延拓为整个primitive谱上的连续二值函数，也不是 $Z(A)$ 的元素。

对每个实际 $a,b$，39.1在非零点给带该符号的交换子，在原点为零。因为 $[a(0),b(0)]=0$ 且原交换子连续，该输出在原点确实连续；39.2支付其全部原PB。这是合法完整模型。它说明交换边界只要求响应本身连续，不能强迫不可见的二值标记连续穿过边界。

相反，若一个低维非交换点可见某个非零交换子，则34.3或39.1中同一旧输出的零集会强迫逼近它的高维支相容。并非所有分层交界都可任意反号；相容性由非交换可见性精确决定。

**反事实 39.4（完整第三标签不能缩成零第三标签）。** 直接消费AQ35–36的已给参考族：在非交换完整矩阵域取 $D_\kappa=\kappa i[,]/2$，$|\kappa|\le1$。它保留全部P2乃至全有限Gram，并满足全部零第三标签PB；完整PB却仅在 $\kappa=\pm1$ 成立。故35节之后确实需要原全称PB，不能由较弱子族替代。该既有反事实不重计为新模型。

## 40. 同一结合乘法、全部原质量及全文来源合同

**推论 40.1（识别之后的静态后果）。** 39.1之后，同一旧 $D$ 才取得实双线性、有界性、逐表示局部性和全部C*商上的下降，且

$$
\|D(a,b)\|\le\|a\|\|b\|.
\tag{40.1}
$$

商下降的依据是：对任意闭理想 $J$，每个消去 $J$ 的不可约表示中，FM使旧值只依赖两份输入像；这些商表示分离 $A/J$，故两槽的 $J$ 核平移均不改变输出商像。

在同一复向量空间 $A=E+iE$ 上，由 $S-iD$ 复双线性延拓得

$$
x\star_Qy=\frac{xy+yx}{2}+\frac12Q(xy-yx).
\tag{40.2}
$$

第二项始终作用于 $I$。各不可约像在正向点为 $\pi x\,\pi y$，在反向点为 $\pi y\,\pi x$；字符无区别。因此该乘法结合，保持同一伴随、单位、Banach范数、自伴域、Jordan积与正锥，给相容C*代数 $A_Q$。例如C*恒等式由

$$
\|x^*\star_Qx\|=\sup_\pi\|\pi x\|^2=\|x\|^2
$$

给出；正锥由自伴平方相同及逐表示正性给出。这里没有要求 $Q$ 可作用于任意 $x$ 后仍属于 $A$。

准确消费AQ32.1–32.2、23.1、6.3及N3 27.1的静态接口：旧 $D$ 双线性已由39.1支付，P2和完整PB仍为32.2–32.3，准确原序单位资料未改。因此取得全有限原复Gram、P3、原R及保全部质量的忠实Hilbert表示。具体有

$$
\begin{aligned}
&\sum_{j,l}\bar z_jz_l
\{\gamma(a_j\circ a_l)-i\gamma D(a_j,a_l)\}
=\gamma_{\mathbb C}(Z^*\star_QZ)\ge0,
\quad Z=\sum_jz_ja_j,\\
&(a\circ b)\circ c-D(D(a,b),c)
=a\circ(b\circ c)-D(a,D(b,c)).
\end{aligned}
\tag{40.3}
$$

既有GNS消费者给忠实保单位、保锥、等距表示及每份原 $\xi_\gamma$，满足 $\gamma(a)=\langle\xi_\gamma,\Pi(a)\xi_\gamma\rangle$、$\|\xi_\gamma\|^2=m_\gamma$。零质量为零向量；不等、次归一与原非正常评价不被删去。表示像不必为全 $B(H)$。不重新证明或计作新增的静态后端。

**定义 40.2（严格采用已发布28.1的全文接口）。** 本文的

$$
\mathcal C_{47}^{\rm pin}(\Omega;S,D)
$$

**准确等于N3定义28.1的谓词**：固定SQ第47节47.1–47.13的全部定义、合同、公式和量词，以及其中逐项纳入的全部固定上游全文的严格合取。N3 28.1所展开的整段原文和递归引用同时生效；不是七个简称的合取，也不以本节的说明替代全文。SQ47.1的“主源”、缩写、`f24d1138a7b994da16abd9a47affedea64ea44ce` 等上游身份，均按SQ自身1.3、39、47.1解析；SM不改指AQ。

只把这个全文合同消费的静态入口替换为40.1已认回的同一 $E,C,u,N,\mathcal P,S,D,\star_Q$。被选静态支为本完整subhomogeneous $A_{\rm sa}$，不把原世界其他支强迫为本模型。全词共同 $K_{\rm nat},\mathsf J$、原比较权及其零集、parent、ready、全部跨评价配对、原对象、准备、设备、程序与记录均保持原身份；它们不改成本文的 $Q_k$、$\Lambda$ 或矩阵坐标。

**定理 40.3（保持全文来源的条件重构）。** 当 $I\ne0$ 时，在32.2同一原模型上有

$$
\begin{aligned}
&\mathsf H_A(D)\ \land\ \mathcal C_{47}^{\rm pin}(\Omega;S,D)\\
&\quad\Longleftrightarrow\quad
\exists!Q\in Z(M(I)):\quad Q=Q^*,\ Q^2=1,\quad
D=K_Q\ \land\ \mathcal C_{47}^{\rm pin}(\Omega;S,K_Q).
\end{aligned}
\tag{40.4}
$$

其中 $K_Q(a,b)=Qi[a,b]/2$。交换情形用唯一 $D=0$ 和空取向。正向用38–39，逆向用39.2；来源合同始终绑定同一个旧响应，没有独立更换响应。

在各原合同确实支付处，按N3 27.1、29.1和SQ48.2–48.3的七项既有消费者逐项接回：40.1已经供应它们所需的同一静态乘法、全Gram、原R和质量表示；余下原来源、对象、合法域及量词仍由40.2的全文提供。这里消费的是各后端已明确的静态接口，不把SQ的固定阶丛模型前件直接套到变阶谱上。

具体边界完整保持：原可取得相干准备、全词共同核不由GNS制造；Born归一只在实际完整菜单及严格正总质量使用，条件更新另须严格正输出质量；真正相关联合及全部中心对、忠实同向交换局部腿、实际复制及每层递归同源参考不由数学乘子制造。每条根箭头每个所需有限长度的整台实际参考链、每个前缀、真支持运输、每个正精度、全部成功／失败／细记录／port／post-port输出，以及每份完整输出的每个仍合法未来，都保留原合同。

完整仪器的typed分区、实际真遗忘、同数两侧与真实逆向返回、原AC方向、读后活动ready、接受叶活动输出、第一合法消费者、分析词到完整菜单和原接受端的producer，不能由点上SVD或有限PB链代付。未定义请求仍未定义；零、静默、经典、不等维和失败对象及其合法未来不删除。无限或非离散记录、可数可加、正常性、指定前对偶及收敛另守原扩展；一般正泛函不自动有全局密度矩阵或Kraus全族。

物理钟和单位、原 $\sigma,t_0,d$ 的设备身份及量纲、连续可逆实际过程、真实原逆、同一乘法下的强连续酉实现、生成元域、能量解释和共同正 $\hbar$ 都另由全文承担。有限数学相位与 $Q$ 不生产它们。不同数学取向可能给不同响应；本定理不保证每一种取向有实际来源实现。

## 41. 来源、准确范围与完整白话

**来源对应 41.1。**

| 固定来源或成熟工具 | 准确消费与边界 |
| --- | --- |
| [OP80–82、84–85][SH-OP]，[SQ31.1–31.3][SH-SQ] | 全部实际代表的二阶混合角、共同块符号、数学正读取、零预算及旧值身份缺口。没有把一般有限商FM当作既有结论。 |
| [AH12–21][SH-AH]，N3 22–31 | 完整原A1–A3/P2/PB、两内行先支付的运输机制、两射线证明、箭头到秩一全幅行及静态消费者。N3的完整三阶丛定理不被直接套给任意商。 |
| [SQ32、43–44、51–56、64、69][SH-SQ] | 精确原负端点、全部有限前缀、原取向与静态入口、旧阈值无首步障碍、全文来源及截断接头边界。当前证明没有使用不完整原域的未付截断接头。 |
| Thiel–Vilalta，[arXiv:2101.04522v2 §4.3][SH-TV]，DOI `10.1016/j.aim.2021.108016` | 亲读给定原文：$I_{\ge k}$ 过滤、$k$-齐次理想商、局部紧Hausdorff上的局部平凡矩阵丛 $C_0$ 截面。作者为Hannes Thiel、Eduard Vilalta。Blackadar IV.1.4、IV.1.7是该原文转引，不冒称本增补亲读了这些书页。 |
| Michael Forger、Daniel V. Paulino，[arXiv:1307.4458v1，定理2，第6页][SH-DH] | 亲读合法开放全文中的Dauns–Hofmann准确接口 $C_b(\operatorname{Prim}L)\cong Z(M(L))$ 及其模primitive理想的取值公式。不是声称亲读Dauns–Hofmann原始论文，也不借用该文其他推广。 |
| C*商的自伴满提升、理想与primitive谱的对应、不可约表示分离、连续函数演算 | 仅用于已给复C*环境中的实际原元素、理想作用和逆元；不赋给旧 $D$ 任何先验正则性。 |
| 局部紧Hausdorff的紧支撑bump、有限SVD、有限酉谱定理、向量等距匹配 | 供应当前齐次商内的一份局部截面和一个点上的有限相位分解；精确提升之后才在原 $A$ 调用PB。 |
| [AQ32.1–32.2、23.1、6.3、35–36][SH-AQ]及SQ48 | 先识别旧 $D$，再消费线性、Gram、R、同一C*乘法及全部质量；参考族的缩放边界不代替当前未知表的识别。 |
| [CO60][SH-CO] | 比较反向的Hermitian相容不等于实际操作顺序可交换；严格复合不推出闭路恒等，非零中心相位类不是量子性的必要条件。 |

新增承重连接是34.2–34.3的跨层同一输出零集、35.2–35.3的理想乘子实际逆标签，以及35.4、37–38对提升高层尾部的逐层全局支付。N3两射线与侧面相位的既有机制被复用，未重复计为新的三阶分类。文献检索与纸面核对不构成历史新颖性或文献穷尽结论。

**边界 41.2。** 结论完整覆盖含单位subhomogeneous复C*代数的整个原自伴域，允许变阶、非Hausdorff全primitive谱、非紧齐次层、非分离代数、无全局矩阵单位和交换边界。数学公式的实际同域提升与全局两内行义务在此已支付，FM在本域不再是open桥。

证明仍以存在有限最高阶、原域完整且已经是给定复C*代数的自伴域为前件。没有最高阶的type I代数不能直接从此下降；一般type I的有限秩压缩不是这里的Jordan商。一般JB的复类型、一般不完备原域中的逆标签与精确提升、一般原载体的分离和原输出接线，均未由本定理解决。这里没有对这些更大域给出完整PB反模型。$A=0$ 时另取唯一零响应，全部式为空或零式，不作正质量归一。

完整量子来源仍由40.2全文约束；没有在这里构造物理producer、完整仪器、无限未来、真实双向返回、物理钟或共同作用量。本交付只有纸面数学与准确引用，不声称kernel核验、独立评审完成、物理起源完成或外部开放问题结算。

**完整白话 41.3。** 原问题是一张已经给定的比较表：把同一个世界里的两件实际对象送进去，它返回一个有方向的答案。二维窗口里的答案已经认得，但大对象会同时投影到许多不同大小的窗口；只在其中一个窗口选好矩阵，不能保证原来那件对象真的被接住，也不能保证同一次配平在别的窗口合法。这里使用有限层次：先处理最大的窗口，再往下处理。当前层的一名局部演员可以精确提升成原世界中的一个对象。这个对象在更小窗口看不见，在当前层是所需的一条射线，在更大窗口可能拖着任意尾部。尾部没有被剪掉：更大窗口的整张旧表已经在上一层认回，正好用来支付它。

方向也不能随意拼。选一对在当前层确实落在二维角里的实际对象，看它们自己的同一份旧输出；更大层已经认得这份输出。输出等于正交换子或负交换子的两个零集，就会把相反方向隔成真正的谱开集。于是方向只需放在当前层及以上那个理想的中央乘子里，无须越过交换边界。这个乘子只乘交换子等已经属于理想的东西，原对象本身不需要被搬到一个更大的域。

真正运输时，先在原代数内写出两份明确的逆标签，使配平的负端点逐字等于当前原输入。然后才检查它们的两条内行：更小层为零，当前层先由两条正交射线约束，再由箭头对齐认回，更大层由已经取得的旧表公式支付。所有窗口同时通过后，才调用那一次原PB。每个前缀都保持这个次序，不能只凭某一点的矩阵相等换掉旧答案。当前层中，最多有限多个这样的相位把同一原输入送到它自己的点上正终点；终点自己的虚标签为零，正预算使终点自己的旧响应为零，旧值再沿原配平传回。有限最高阶让这个过程最终走完整个代数，线性、局部性和同一个结合乘法都是随后得到的结论。

最后的几何只有非交换谱上的两种方向。若一条边界已经完全交换，交换子在那里消失，两边方向可以不同而实际输出仍连续；强求符号穿过这条边界会删掉真实合法模型。若边界仍能看见非零交换子，同一输出就会约束两边方向相容。这个简化解决的是同一原比较表的数学识别。它仍不制造准备设备、相关联合、完整菜单、整台过程的每个未来、读后活动输出、真实返回或物理时间；这些必须按完整来源合同在原世界逐项取得。

[SH-AH]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_ORIGINAL_ATOMIC_SEPARATION_AND_PB_RECONSTRUCTION_CONTINUATION.md
[SH-OP]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md
[SH-SQ]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_ZERO_DIMENSIONAL_CENTER_SQUARE_ORBIT_RECONSTRUCTION.md
[SH-AQ]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md
[SH-CO]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_FIB_COMPARISON_ORDER_AND_POSITIVITY_BOUNDARIES_CONTINUATION.md
[SH-N3]: https://github.com/the-omega-institute/trureturing/blob/bc937d93159bedf6c321837e0f498bc4261bafe7/docs/develop/theory/AURIC_ORIGINAL_ATOMIC_SEPARATION_AND_PB_RECONSTRUCTION_CONTINUATION.md
[SH-TV]: https://arxiv.org/pdf/2101.04522v2
[SH-DH]: https://arxiv.org/pdf/1307.4458v1

## 追加锚（本行以下为增补区）

## 42. 本质连续迹理想上的完整原关系

**约定 42.1（来源、同一性及证明范围）。** 本增补中的AH、OP、PT、W、SQ、AQ分别指本卷、《原多项式零响应与Cayley原域边界》、《配平三角的共同取向与秩一响应续卷》、《任意维小窗口单位桥》、《零维紧中心的同一原响应与平方酉轨道闭包分类》、《任意维静态量子重构》。本文直接消费的仓内正文统一取提交 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7`；各正文严格纳入的上游版本继续按其自身定义解析。这里的PT185是配平主卷的185节，OP没有185节。本文为纸面条件数学，仓内前置同属这一研究来源，不将引用、研究输入或纸面证明称作kernel核验。

**定义 42.2（完整原候选）。** 给定含单位复C*代数 $A$，取完整原域及原结构

$$
E=A_{\rm sa},\qquad S(a,b)=a\circ b=(ab+ba)/2,
\qquad C=A_+,\quad u=1,\quad N(a)=\|a\|.
\tag{42.1}
$$

同一原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定 $C$。保留原世界 $\Omega/\mathrm{native}$、每份评价及其质量 $m_\gamma=\gamma(1)$，包括零、不等、次归一及原表示意义下的非正常评价。未知量是同一个任意总映射 $D:E^2\to E$。

记 $\mathsf H_A(D)$ 为下列全部原关系的合取。A1/P2要求所有实际 $a,b\in E$、两种次序及所有 $\gamma\in\mathcal P$ 的Hermitian二表

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(b\circ a)-i\gamma D(b,a)&\gamma(b^2)
\end{pmatrix}\succeq0.
\tag{42.2}
$$

A2要求相加三表 $(a+b,a,b)$ 及全部排列的实部在整个 $\mathbb R^3$ 上半正定，指定相加向量 $(1,-1,-1)$ 及相应排列给零。A3要求 $1^2=1$，并保留同一个固定有理 $0<\vartheta\le1$ 上的全部 $0\le e\le\vartheta1\Rightarrow e^2\le e$。不预给复三表正性。

对每个实际三元组 $(h;a,b)$，定义的始终是同一旧映射的实际内值及实际外层标签：

$$
v=D(h,a)-h\circ b,\quad w=h\circ a+D(h,b),
\qquad r_\pm=a\pm v,\quad s_\pm=b\pm w.
\tag{42.3}
$$

完整PB要求全部原评价满足

$$
\gamma(r_+^2+s_+^2+2D(r_+,s_+))
=\gamma(r_-^2+s_-^2+2D(r_-,s_-)).
\tag{42.4}
$$

由分离性及已知Jordan双线性，其元素式等价于

$$
D(a+v,b+w)-D(a-v,b-w)=-2a\circ v-2b\circ w.
\tag{42.5}
$$

零、重复、任意幅度、缩放、平移、背景及全部嵌套调用都在量词内。不给 $D$ 输入线性、连续、可测、协变、局部性、商下降或输出小代数闭合。后文每次只在原 $E$ 中调用PB；输入像相等从不授权更换实际标签。

**定义 42.3（所需理想与取向）。** 闭双边理想 $J\triangleleft A$ 称为本质的，若 $\operatorname{Ann}_A(J)=\{x:xJ=Jx=0\}=0$。连续迹取C*代数的通常定义，不要求含单位、可分、固定纤维维数或局部平凡紧算子丛。记

$$
\mathfrak c=\overline{\operatorname{Id}_A
\{[a,b]:a,b\in E\}},\qquad
K_\sigma(a,b)=\frac{\sigma i}{2}[a,b]\quad(\sigma=\pm1).
\tag{42.6}
$$

$\operatorname{Id}_A$ 在本增补中始终表示生成的双边理想，横线表示范数闭包；$\mathfrak c$ 不是其他来源合同中的有限词理想。

**定理 42.4（本质连续迹分类）。** 若 $A$ 含有本质连续迹闭理想，则满足42.2的同一原响应，恰为

$$
D(a,b)=Q\frac i2[a,b]\qquad(a,b\in E),
\tag{42.7}
$$

其中 $\mathfrak c\ne0$ 时 $Q\in Z(M(\mathfrak c))$ 是唯一自伴中央酉乘子。等价地，存在唯一有序正交闭理想分解

$$
\mathfrak c=\mathfrak c_+\oplus\mathfrak c_- ,
\qquad Q|_{\mathfrak c_+}=1,\quad Q|_{\mathfrak c_-}=-1.
\tag{42.8}
$$

$\mathfrak c=0$ 时唯一响应为零，取向为空。两个理想由原 $D$ 恢复，不是额外选择。反向对任意这样的分解，42.7都满足全部原A1–A3/P2及全部实际PB。

识别以后，旧 $D$ 实双线性、有界、保持闭理想并在所有C*商上下降。同一复向量空间上的 $S-iD$ 给相容C*乘法，保留原自伴域、Jordan积、锥、单位、范数及每份原质量。证明见43–55节；56节给type I与无统一阶数上界FDI的适用性，57节给完整来源合同。零C*对象单列为唯一零响应与空取向。

## 43. P2的实际支撑结论

**引理 43.1（正读取、零槽与理想吸收）。** 对任意数学正泛函，原P2仍成立。特别，对任意表示 $\pi:A\to B(H)$、任意向量 $\xi$，令 $A_0=\pi a,B_0=\pi b,d=\pi D(a,b)$，有

$$
|\langle\xi,d\xi\rangle|^2
\le\|A_0\xi\|^2\|B_0\xi\|^2
-(\operatorname{Re}\langle A_0\xi,B_0\xi\rangle)^2.
\tag{43.1}
$$

并有反对称性、原比例零值及

$$
\pi a=0\Rightarrow\pi D(a,b)=0,
\qquad D(L_{\rm sa},E)\subset L_{\rm sa}
\quad(L\triangleleft A\text{ 闭}),
\qquad D(E,E)\subset\mathfrak c.
\tag{43.2}
$$

证明。Hermitian性及分离性给 $D(b,a)=-D(a,b)$。二表在任意固定复系数上的二次型，是被全部原评价读为非负的原自伴元素，准确锥使它为正。这就把同一二表送给每个数学正泛函，给43.1。比例输入的Gram行列式为零，所以 $D(a,ta)=0$，特别全域零槽成立。一个输入像为零时，43.1及固定自伴输出的极化给零输出像。对所有消去 $L$ 的不可约表示应用这一事实，商的不可约分离性给理想吸收。

若 $\chi$ 是字符，43.1右侧是 $\chi(a)^2\chi(b)^2-(\chi(a)\chi(b))^2=0$，不需要输入像为零。故所有字符消去 $D(a,b)$。$A/\mathfrak c$ 交换，字符分离其元素，得最后一式。这里未证明一般核平移不变性。∎

**引理 43.2（有限支撑实际原像域）。** 固定表示 $\pi$ 及有限秩正交投影 $P\in B(H)$，令

$$
T_P=\{a\in E:\pi a=P\pi(a)P\}.
\tag{43.3}
$$

$T_P$ 是对同一旧 $D$ 闭合的实Jordan子代数，且 $\rho_P:T_P\to B(PH)_{\rm sa}$、$a\mapsto\pi(a)|_{PH}$ 是Jordan同态。若 $K(H)\subset\pi(A)$，则 $\rho_P$ 满射。

证明。对实际 $a,b\in T_P$，P2在系数 $(1,\pm i)$ 上给

$$
-\tfrac12((\pi a)^2+(\pi b)^2)
\le\pi D(a,b)\le
\tfrac12((\pi a)^2+(\pi b)^2)\le MP
\tag{43.4}
$$

的双侧支配，其中 $M=(\|\pi a\|^2+\|\pi b\|^2)/2$。若 $-MP\le d\le MP$，两个正算子 $MP\pm d$ 在 $P^\perp H$ 上的二次型为零，正平方根使它们都消去该子空间，故 $d=PdP$；这同时排除了交叉块。Jordan闭合及同态性来自原乘法。若含有全部紧算子，每个有限角矩阵属于 $\pi(A)$；任选提升再取自伴部即给精确自伴提升。因此可选实际 $e\in T_P$ 满足 $\pi e=P$，不要求 $e^2=e$。∎

**约定 43.3（全局旋转的准确来源）。** 在整个含单位完整 $E=A_{\rm sa}$ 上消费PT183.2及185.1：原全单位行已为零，并有

$$
D(a\cos t-b\sin t,a\sin t+b\cos t)=D(a,b),
\quad D(-a,b)=D(a,-b)=-D(a,b).
\tag{43.5}
$$

这是已发表的一般原域结论。准确代入PT183.1的JB环境为 $X_{\rm JB}=A_{\rm sa}$，原稠密包含为恒等，单位、锥、范数与42.1相同；42.2支付其全部A1–A3/P2/PB，没有有限谱、原最小投影或额外纯态作用条件。PT183–184证明单位行，185.1随后给43.5；不是在 $T_P$ 上假定相对单位公理。$T_P$ 对这些实际实线性旋转闭合，故43.5可用于其中的任意实际标签。PT185.3的一般输入作用纤维条件不在此消费。

## 44. OP二阶定理向实际有限支撑原像的转移

**定理 44.1（有限角的全部实际代表）。** 设 $\pi:A\to B(H)$ 不可约且 $K(H)\subset\pi(A)$。对每个秩二 $P$，存在唯一 $\sigma(P)=\pm1$，使

$$
\pi D(a,b)=\frac{\sigma(P)i}{2}[\pi a,\pi b]
\qquad(a,b\in T_P).
\tag{44.1}
$$

秩零、一的共同支撑给零值。若 $\dim H\ge2$，所有秩二角共用同一个输入无关符号 $\sigma_\pi$。

证明分为下列实际调用步骤。它们移植PT241–245、OP59–61及80–82的证明，不把 $a\mapsto P\pi(a)P$ 当作整个 $A$ 上的Jordan商。

**第一步：正读取与相对单位。** 固定秩二 $P$，取Pauli坐标 $\alpha P+x\leftrightarrow(\alpha,x)$，$x\in\mathbb R^3$。已知Jordan乘法、锥及Bloch读取为

$$
(\alpha,x)\circ(\beta,y)=(\alpha\beta+x\cdot y,\alpha y+\beta x),
\qquad \beta_n(\alpha,x)=\alpha+n\cdot x\quad(\|n\|\le1).
\tag{44.2}
$$

$\beta_n(P\pi(\cdot)P)$ 是原 $A$ 上的数学正读取。对 $a,b\in T_P$，输出也支撑于 $P$，故这些读取分离它。每个实际PB的全部内外层仍在 $T_P$，43.2保证读取Jordan表达式的合法性；任意核尾始终保留。

还需PT241.1的反交换结论：若两输入像的Jordan积为零，对实际PB $(a;b,0)$，两个真实第二外槽的像均为零，43.2消去各自输出像，得到 $(\pi b)\circ\pi D(a,b)=0$。交换实际 $a,b$，同样得到 $(\pi a)\circ\pi D(a,b)=0$。

任选实际 $e$ 使 $\pi e=P$。现说明PT242.1的相对单位证明确实适用。若 $\pi a=\mu P$、$\pi b=tP+y$，两枚读取 $n=\pm y/\|y\|$ 先使输出像成为 $h\perp y$ 的纯向量；令 $r=\|y\|,s=\|h\|$，P2给 $s\le|\mu|r$。若 $s>0$，对真实第三标签 $c=ka$、$k=s/(1+\mu^2)$，比例零值给 $D(a,c)=0$。两外层像满足

$$
S_+-\mu R_+=S_-+\mu R_-=\mu(sP-h).
\tag{44.3}
$$

在 $\beta_{h/s}$ 的半内积中右侧为零，故两份实际外层的P2读数都为零；PB右端的读取为 $-2ts$，所以 $t=0$。对实际PB $(b;a,\mu b)$，正侧实际标签

$$
a-D(a,b)-\mu b^2,\qquad \mu b+b\circ a
\tag{44.4}
$$

像为 $\alpha P-h,2\mu y$，$\alpha=\mu(1-r^2)$；负侧第二槽像零，PB给正侧输出像 $2\mu h$。其P2在 $n=q h/s+\sqrt{1-q^2}y/r$ 上给

$$
s|q|\le r|\alpha q-s|\qquad(-1\le q\le1).
\tag{44.5}
$$

若 $0<s\le|\alpha|$，取 $q=s/\alpha$ 矛盾；若 $s>|\alpha|>0$，取 $q=\operatorname{sgn}\alpha$，在 $r\le1$ 时矛盾，在 $r>1$ 时迫使 $s\ge|\mu|r(r+1)>|\mu|r$。只余 $\alpha=0,r=1$。但此时44.4两像反交换，而其首像与输出的Jordan积为 $-2\mu s^2P\ne0$，违反上一段。故 $h=0$。退化的 $\mu=0$、$y=0$ 已由零预算处理。

因此一槽像为角单位倍数时输出像为零；两向量部分共线时，用43.5的实际旋转消去一个向量部分，也得零。特别

$$
\pi D(a,te)=0,\qquad
\pi D(a,\gamma e+\tau(a-\alpha e))=0
\quad(\pi a=(\alpha,x)).
\tag{44.6}
$$

这里只断言像为零，从未把这些实际内输出替换成原零。

**第二步：纯像面积及辅助映射。** 逐项消费PT243–245的已发表内积引理，所需实际调用如下。对纯像 $x\perp y$，上一反交换结论先给 $d=\pi D(a,b)\in\mathbb R^3$、$d\perp x,y$，P2给 $\|d\|=\kappa\|x\|\|y\|$、$0\le\kappa\le1$。取实际

$$
c=t_0e+\lambda a,\quad t_0=\sqrt{\lambda^2\|x\|^2+\eta^2},
\quad n=-\lambda x/t_0+\eta y/(t_0\|y\|),\quad \lambda,\eta>0.
\tag{44.7}
$$

44.6支付 $\pi D(a,c)=0$。PB的两份真实外层像为

$$
R_\pm=\mp\lambda\|x\|^2P+y\pm d\mp t_0x,
\qquad S_\pm=t_0P+\lambda x.
\tag{44.8}
$$

分别读取两份真实P2，PT243.5的同一Gram计算给

$$
(1-\kappa^2)\lambda^2\|x\|^2\|y\|^2
\le\eta^4+\kappa^2\|y\|^2\eta^2.
\tag{44.9}
$$

固定 $\eta$ 并选足够大但有限的 $\lambda$，迫使 $\kappa=1$。任意纯像对以43.5旋转其Gram，故所有实际纯像代表均有准确面积与正交性。

固定 $0<\|x\|=r<1$，$W_x=x^\perp$，任取纯像 $y,z\in W_x$ 的实际代表 $b,c$。记 $f_b=\pi D(a,b),f_c=\pi D(a,c)$。实际PB $(a;b,c)$ 的右端像零，两外层纯像输出相等；刚得准确面积给

$$
(\langle y,z\rangle+\langle f_b,f_c\rangle)
(\langle y,f_c\rangle+\langle f_b,z\rangle)=0.
\tag{44.10}
$$

对同一 $y$ 的两份实际代表，在开集 $\langle y,z\rangle>r^2\|y\|\|z\|$ 中用同一个实际 $c$。第一因子严格正，第二因子之差和开球分离性使 $f_b$ 与代表无关。这才得到总映射 $F_a:W_x\to W_x$。W110.1的全部前件现已支付：44.10、$\langle y,F_ay\rangle=0$、$\|F_ay\|=r\|y\|$、$0<r<1$。该纯内积引理给实线性、斜性及 $F_a^2=-r^2I$。

第一槽的一致性须另付：若 $\pi a=\pi a'=x$，对给定非零 $y\perp x$ 选 $\delta>0$、$\delta\|y\|<1$。刚得的第二槽一致性用于真实首标签 $\delta b$，反对称性及两条已线性的小行给 $\delta F_a(y)=\delta F_{a'}(y)$。所以可写 $F_x$。继而按照PT245.1及245.2、W111–112定义

$$
B(x,y)=\lambda^{-1}F_{\lambda x}
\left(y-\frac{\langle x,y\rangle}{\|x\|^2}x\right),
\qquad 0<\lambda\|x\|<1,
\tag{44.11}
$$

零 $x$ 取零。两个真实缩小首标签和另一个真实 $\delta b$ 的反对称调用使它与 $\lambda$ 无关；这些小行均已取得纤维一致性。W112.1的二平面拼接只展开已线性的第二槽，给 $B$ 实交替双线性、斜，且

$$
B_x^2=-\|x\|^2I+x\otimes x,
\qquad \|B(x,y)\|^2=\|x\|^2\|y\|^2-\langle x,y\rangle^2.
\tag{44.12}
$$

这两个纯内积拼接引理不要求 $T_P$ 含单位、完备或存在Jordan截面。未知原 $D$ 没有被极化。

OP59–61的大纯像步骤也逐次合法：正交非零 $x,y$ 任意，固定实际 $d=\pi D(a,b)$，取第三实际标签 $c=tb$，使 $t\|y\|\sqrt{1+\|x\|^2}<1$。小行及实际旋转支付 $\pi D(a,c)=tB(x,y)$。两份真实外层像为

$$
(y\pm d,\ ty\pm tB(x,y)).
\tag{44.13}
$$

各自第二像长度小于一，故以实际旋转转入已付小正交行，两个旧输出分别由 $B$ 识别。PB成为

$$
B(y+d,ty+tB(x,y))=B(y-d,ty-tB(x,y)).
\tag{44.14}
$$

此后才展开 $B$，44.12使 $d=B(x,y)$。一般纯像对用43.5对角化Gram，相关对用零预算。三维中斜的交替面积映射必为 $B(x,y)=k x\times y$、$k^2=1$：其三线性型 $\langle B(x,y),z\rangle$ 是三形式，单位正交对的面积确定 $|k|=1$。置 $\sigma(P)=-k$，即符合 $K_\sigma=\sigma i[,]/2$ 的Pauli符号。

**第三步：全部混合像。** 以下是OP81各次局部PB的准确代入；相对单位始终用实际 $e$，原核尾始终保留。先取 $\pi a=(\lambda,x),\pi b=(0,y)$、$x\perp y$，写未知输出 $(\delta,z)$。取真实 $c=t(a-\lambda e)$、$t=\delta/\|x\|^2$。44.6支付内值像零，四个外层像为纯对

$$
(y\pm H,\ tx\pm\lambda y),\qquad H=z-t\lambda x.
\tag{44.15}
$$

已付纯像公式使PB为 $2tB(H,x)=-2(y\cdot z)P$。所以 $y\cdot z=0$；若 $\delta\ne0$，则 $z=\zeta x$。再用第三实际标签 $\zeta e$，两份外层的向量像共线，44.6使输出像零，PB却为 $0=-2\delta y$。故 $\delta=0,y\cdot z=0$，退化向量由零预算和相对单位处理。

若两输入像实张成含严格定号矩阵，OP74.1的两枚零Gram读取在44.2下给

$$
x\cdot z=\alpha\delta,\quad y\cdot z=\beta\delta
\quad(\pi a=(\alpha,x),\pi b=(\beta,y)).
\tag{44.16}
$$

具体地，实际旋转使标量部分为 $(\lambda,0)$、$\lambda>0$；写 $y=s e_3,x=h e_1+t e_3$。定号条件是 $\lambda>|h|$，行列式为 $s^2[(\lambda n_1+h)^2+\lambda^2n_2^2]$；取 $n=(-h/\lambda,0,\pm\sqrt{1-h^2/\lambda^2})$ 即得44.16。这里全用正读取，没有混合输出纯性前提。

仍在旋转后的坐标，记 $h=x\cdot y,r=\|y\|^2$，取有限 $T>|h|+\lambda\|y\|+\|y\|+1$ 及实际 $c=Te$。两份真实外层像为

$$
P_\pm=(\pm(\delta-T\lambda),y\pm z\mp Tx),
\qquad Q_\pm=(T\pm h,\pm\lambda y).
\tag{44.17}
$$

两份 $Q_\pm$ 严格正定。PB给输出差 $(0,-2\delta y)$，记两输出为 $(\eta,m\mp\delta y)$。只对这些外层用44.16，给 $\eta=-\lambda\delta r/T$、$y\cdot m=-h\delta r/T$，另两约束相加给 $y\cdot m=-T\delta h$。故 $\delta h(T^2-r)=0$；$h=0$ 用44.15，其余得 $\delta=0$。由44.16，定号张成对的输出纯且垂直两个向量部分。

对任意混合像，再用同一形式的 $Te$；44.17的两份 $Q$ 仍严格正定，刚证结论使两份真实外层输出纯且垂直 $y$。PB的输出差是 $-2(y\cdot z,\delta y)$，标量比较及与 $y$ 作内积给 $\delta=y\cdot z=0$。对交换后的实际 $(b,a)$ 另作这次PB，右端为 $2(\pi a)\circ\pi D(a,b)$，得 $x\cdot z=0$。所以全部实际对已满足输出纯且 $z\perp x,y$。

向量共线及两像纯均已处理。其余按OP76.1作两次实际SO(2)旋转，使 $\alpha,\beta>0$ 及 $N=\beta(1+\alpha^2)+\alpha x\cdot y>0$。这一有限选择的具体参数为：先使标量部分 $(0,\rho)$，令 $M=\|x_0\|^2+\|y_0\|^2$、$s=1/[4(1+M)]$、$c_0=\sqrt{1-s^2}$，再旋转为 $(c_0a_0+s b_0,-s a_0+c_0b_0)$；于是 $N\ge\rho(c_0-sM/2)>0$。

令

$$
q=\|x\|^2, n=x\times y, L=\|n\|^2,
\ell=qy-(x\cdot y)x,
\quad\gamma=-(\alpha\beta+x\cdot y),\quad\tau=N/q,
\quad c=\gamma e+\tau(a-\alpha e).
\tag{44.18}
$$

44.6支付这份实际内值像零。两份真实外层像为

$$
\begin{aligned}
P_\pm&=(\beta\mp(\alpha\gamma+\tau q),y\pm z\mp(\gamma+\alpha\tau)x),\\
Q_\pm&=(\gamma\pm(\alpha\beta+x\cdot y),(\tau\pm\beta)x\pm\alpha y).
\end{aligned}
\tag{44.19}
$$

正侧两像都纯；负侧任意。已付的输出结构及PB给 $Y_\pm=m\pm(\tau\ell-\beta z)$，两份 $Q$ 的正交约束相加得 $x\cdot Y_+=-\alpha L$。正侧纯像公式又给

$$
x\cdot Y_+=k x\cdot(P_+^0\times Q_+^0)
=-k\alpha z\cdot n.
\tag{44.20}
$$

故 $z\cdot n=kL$，$z\perp x,y$ 使 $z=kn$。撤销实际旋转即得44.1。秩一共同支撑的两像均为相对单位倍数，所有Gram为零；秩零用43.2。

**第四步：三维证书及任意平面。** 在任意正交三框架中，若 $12$、$13$ 角反号，置 $\eta=-\sigma(P_{12})$。选择实际自伴提升，像为

$$
A=\tfrac12p_1,\quad B=-p_1-\tfrac12p_2+X_{12},
\quad C=3p_1+\tfrac12p_3+X_{13},
\quad\xi=(1,2,-2)^T,
\tag{44.21}
$$

其中 $X_{ij}=E_{ij}+E_{ji}$、$Y_{ij}=(E_{ij}-E_{ji})/i$。所有这些矩阵由 $K(H)\subset\pi(A)$ 精确提升，实际标签在相应三维支撑原像中。两内值由刚证二阶公式读成 $\eta Y_{12}/4,-\eta Y_{13}/4$。PT130.3–130.5的已知乘法给

$$
\begin{array}{c|ccc}
&\|r_\pm\xi\|^2&\|s_\pm\xi\|^2&
\operatorname{Re}\langle r_\pm\xi,s_\pm\xi\rangle\\\hline
+&3/8&11/8&1/4\\
-&35/8&11/8&9/4
\end{array}
\tag{44.22}
$$

且同一次实际PB要求 $\langle\xi,\pi(D(r_+,s_+)-D(r_-,s_-))\xi\rangle=2$。分别对这两份未知实际外值使用43.1，得

$$
2\le(\sqrt{29}+\sqrt{61})/8<2,
\tag{44.23}
$$

矛盾；不把任何外值换成交换子。读取在三维单位上的质量为9，统一缩放不改变矛盾。重标共同顶点得三坐标角同号。

三维空间内，对射线 $l$ 令 $f(l)=\sigma(l^\perp)$。正交射线补成正交三框架，给相同值；不同非正交射线有共同正交射线，亦给相同值。因此三维空间中的任意二平面同号。一般 $H$ 中，两二平面相交于射线时其和三维；交零时，各取一条射线张成中间二平面，再作两次三维比较。此论证也适用于不可分无限维 $H$，全程只用有限子空间。∎

**依赖说明 44.2。** 原OP80.1要求的是整个JB环境上的有限满Jordan商；本证明没有宣称该原前件对无限维压缩成立。43.2及44.2–44.6重新支付了其证明真正使用的原像闭合、全部正读取、实际相对单位与旋转；44.7–44.20逐次接回PT243–245、OP59–61和81的局部调用，44.21–44.23接回OP82。PT240.2、246–247的排除其他有限JB类型不被调用：这里的角已经由给定复C*乘法确定为 $H_2(\mathbb C)$。既不假定纯像充分，也不预付整个 $\pi(A)$ 上的响应商。

## 45. 任意有界无限背景中的零对角秩一行

**引理 45.1（AH23及36的无限背景接线）。** 在44.1的表示中，实际 $r,a\in E$ 若满足

$$
R=\pi r=\mu p,\quad p=ee^*,\quad\|e\|=1,
\qquad pTp=0,\quad T=\pi a,
\tag{45.1}
$$

则 $\pi D(r,a)=K_{\sigma_\pi}(R,T)$。不要求 $T$ 紧、有限秩或有限支撑。

证明。记 $q=1-p$、$u=qTe$、$H_e(v)=ve^*+ev^*$，则

$$
T=H_e(u)+B,\quad B=qBq=B^*,\qquad
 d=\pi D(r,a)=\delta p+H_e(w),\quad w\perp e.
\tag{45.2}
$$

最后一式来自43.1在 $qH$ 上的零预算及极化。$\mu=0$ 直接为零。保留实际PB $(a;r,0)$：

$$
D(r-D(r,a),r\circ a)-D(r+D(r,a),-r\circ a)
=2r\circ D(r,a).
\tag{45.3}
$$

若 $u=0$，两份第二外槽像均为零，故 $R\circ d=0$。$R\circ-$ 在 $\mathbb Rp+H_e(qH)$ 上对 $\mu\ne0$ 单射，给 $d=0$。

若 $t=\|u\|>0$，令 $f=u/t,L=\operatorname{span}\{e,f\},j=\sigma_\pi i$，取

$$
u_\epsilon=(e-\epsilon j f)/\sqrt2,\quad
P_\epsilon=u_\epsilon u_\epsilon^*,\qquad
C_\epsilon=\epsilon2tP_\epsilon
=\epsilon t(p+ff^*)+H_e(-ju).
\tag{45.4}
$$

两条射线正交。精确提升实际 $c_\epsilon$ 使 $\pi c_\epsilon=C_\epsilon$。44.1支付实际 $(r,c_\epsilon)$ 的内值；直接乘法给

$$
K_j(R,T)=H_e(-j\mu u/2),\quad
R\circ C_\epsilon=\epsilon\mu t p+K_j(R,T),\quad
R\circ T+K_j(R,C_\epsilon)=0,
\tag{45.5}
$$

其中 $K_j(X,Y)=j[X,Y]/2$。令 $\Delta=d-K_j(R,T)$。实际PB $(r;a,c_\epsilon)$ 的真实位移像为 $\Delta-\epsilon\mu t p,0$；两份真实第二外槽像同为 $C_\epsilon$。令 $R_\epsilon=1-P_\epsilon$，分别用秩一零压缩读取这两份外值，再压缩PB，得

$$
R_\epsilon(T\circ\Delta)R_\epsilon=0.
\tag{45.6}
$$

这里被去掉的项确为零：$T\circ p=H_e(u)/2$ 支撑在 $L$，且 $u_\pm^*H_e(u)u_\pm=0$，所以 $R_\epsilon(T\circ p)R_\epsilon=0$。

对每个 $\zeta\in L^\perp$，同一个 $(T\circ\Delta)\zeta$ 由45.6同时属于两条正交射线，故为零。写 $\Delta=\delta p+H_e(\eta)$、$\eta=w+j\mu u/2$，实际矩阵乘法给

$$
q(T\circ\Delta)\zeta=\tfrac12u\eta^*\zeta
=\tfrac12u w^*\zeta.
\tag{45.7}
$$

任意 $B$ 未被删去：$q\Delta T\zeta=0$，而 $qT\Delta\zeta=u\eta^*\zeta$，所以其项在这次压缩中消去。由 $u\ne0$ 得 $w\in\mathbb Cu$，于是 $d$ 支撑在 $L$。

现在45.3的两对真实外层像才同时支撑在同一二角 $L$。44.1分别识别它们，得到

$$
2R\circ d
=K_j(R-d,R\circ T)-K_j(R+d,-R\circ T)
=2R\circ K_j(R,T).
\tag{45.8}
$$

最后等式只展开已知交换子，利用 $R^2=\mu R$。再用上述行空间单射性得结论。$\dim H=2$ 时 $L^\perp=0$，$w\in\mathbb Cu$ 自动成立；无限维时45.7对每个补空间向量分别成立，没有留下无限尾部条件。∎

## 46. 连续迹局部框架的实际供应

**引理 46.1（变维与不可分纤维的有限框架）。** 设 $J\triangleleft A$ 连续迹，$X=\operatorname{Prim}J$。每个 $x_0\in X$ 附近可以采用连续Hilbert场 $(H_x)$，使相应局部理想为这些纤维的紧算子连续场。给定 $H_{x_0}$ 中任意有限正交组，可以缩小邻域并延成局部连续正交单位截面。其矩阵单位乘 $C_c$ 截断函数后延零，都是 $J$ 中的实际元素。若已有单位截面 $e$，可要求新增有限组始终垂直 $e$。

证明。连续迹给局部紧Hausdorff谱及Fell条件；精确所用成熟结构是Blackadar IV.1.4.16–19、IV.1.7.4–8，以及Dixmier–Douady的Lemma 16、Theorem 7。后一原定理把Fell条件等价为局部来自连续Hilbert场的紧算子场，未给固定Hilbert空间的局部平凡化。

指定纤维值可精确取得，而不止稠密逼近：在Blackadar IV.1.7.8的紧邻域 $Z$ 上取满Hilbert $C(Z)$-模 $\mathcal E$，$J_Z\cong K(\mathcal E)$。IV.1.7.4的纤维是完备商 $\mathcal E/\mathcal E I_x$，所以评价满射。等价地，在局部秩一投影 $p$ 的构造中，模为 $J_Zp$，$J_Z$ 的评价满到 $K(H_x)$，故模评价满到 $K(H_x)p_x\cong H_x$。选局部连续截面 $v_1,\ldots,v_m$ 取得给定值。

令 $G(x)=(\langle v_i(x),v_j(x)\rangle)_{ij}$。它连续且 $G(x_0)=I_m$，在较小邻域正定。以有限矩阵连续函数演算形成

$$
e_k(x)=\sum_l v_l(x)(G(x)^{-1/2})_{lk}.
\tag{46.1}
$$

所得截面正交且保留指定点值。若须垂直已有 $e$，先将 $v_l$ 换成 $v_l-e\langle e,v_l\rangle$，再作46.1。维数可能在其他点变化；Gram可逆仅保证这有限组在所选邻域存在。

连续Hilbert模的秩一算子 $\theta_{e_k,e_l}$ 是局部连续紧算子截面。任取实或复 $f\in C_c(U)$，$f\theta_{e_k,e_l}$ 范数有界、在边界消失，延零属于 $J_U\subset J$。$J_U$ 也是 $A$ 的理想：$J$ 的任意闭理想对 $A$ 不变，可用 $J$ 的近似单位将 $a l$ 写成 $(a e_\nu)l$ 的范数极限证明。这里用连续性的是已知Hilbert场、函数演算及实际C*乘法，不是 $D$ 的输入作用。∎

**引理 46.2（局部表示与外部零演员）。** $J$ 的不可约表示唯一非退化延到 $A$，给表示族 $\pi_x:A\to B(H_x)$，且 $\pi_x(J)=K(H_x)$。任一 $A$ 的不可约表示若在 $J$ 上非零，其限制非退化、不可约，因而属于这个族。若实际演员属于 $J_U$，其非零不可约像只能在 $U$ 中出现。

证明。理想的非零不可约限制、唯一非退化延拓及谱开嵌入是C*理想的标准表示事实。连续迹是CCR，所以纤维像为全部紧算子。局部理想对应谱开集，给最后一项。特别，任意原 $a\in A$ 在这些纤维中是有界算子；不要求它为紧截面，也不要求它有算子范数连续的局部矩阵表示。∎

## 47. 用固定旧输出隔开局部符号

**引理 47.1（同向开理想）。** 对 $x_0\in X$、$\dim H_{x_0}\ge2$，存在 $A$ 的闭理想 $B_\sigma\subset J$，其谱开集含 $x_0$，且每个活跃点都非经典并具有44.1的同一符号 $\sigma=\sigma_{\pi_{x_0}}$。

证明。由46.1选两条局部正交单位截面 $e_1,e_2$ 及实 $f\in C_c(U)$、$f(x_0)=1$。取实际

$$
a_0=f\theta_{e_1,e_1},\qquad
b_0=f(\theta_{e_1,e_2}+\theta_{e_2,e_1})\quad\text{于 }U,
\tag{47.1}
$$

图外延零。它们在每个非零纤维共同支撑于秩二角，在 $x_0$ 的交换子非零。定义固定实际输出及其生成理想

$$
h_\sigma=D(a_0,b_0)+K_\sigma(a_0,b_0),
\qquad B_\sigma=\overline{\operatorname{Id}_A(h_\sigma)}.
\tag{47.2}
$$

43.2给 $h_\sigma\in J$。44.1使反向点上的 $\pi_x h_\sigma$ 为零；一维点由标量P2给零；图外由实际零槽给零；在 $x_0$，$\pi_{x_0}h_\sigma=2K_\sigma(\pi_{x_0}a_0,\pi_{x_0}b_0)\ne0$。所以

$$
O_\sigma=\{x:\pi_x h_\sigma\ne0\}
=\{x:\pi_x(B_\sigma)\ne0\}
\tag{47.3}
$$

是所需谱开集。其开性是固定理想的hull–kernel性质；不需要 $D$ 的输入连续性，甚至不需要先证明 $x\mapsto\sigma_x$ 连续。46.1中的局部有限框架若支撑紧含于 $O_\sigma$，对应截断秩一演员便属于 $B_\sigma$。∎

## 48. 两份全域内行支付后的准确Cayley运输

**定义 48.1（固定符号残差）。** 固定一个普通数 $\sigma=\pm1$，令 $j=\sigma i$。对每个实际 $W\in A$，定义

$$
x(W)=(W+W^*)/2,\quad y_\sigma(W)=(W-W^*)/(2j),
\quad W=x(W)+j y_\sigma(W),
\quad F_\sigma(W)=D(x(W),y_\sigma(W))-K_\sigma(x(W),y_\sigma(W)).
\tag{48.1}
$$

这是真正原标签上的残差，不先下降为某个纤维算子的函数。直接乘法给

$$
x(W)^2+y_\sigma(W)^2+2D(x(W),y_\sigma(W))
=W^*W+2F_\sigma(W).
\tag{48.2}
$$

**引理 48.2（实际负端点）。** 给定实际 $T\in A,r=r^*\in E$，取原逆标签

$$
A_r=(1-jr)^{-1}T=X+jY,
\qquad C_r=(1+jr)(1-jr)^{-1}.
\tag{48.3}
$$

若两份原元素等式

$$
D(r,X)=K_\sigma(r,X),\qquad D(r,Y)=K_\sigma(r,Y)
\tag{48.4}
$$

均已证明，则 $F_\sigma(C_rT)=F_\sigma(T)$。

证明。$1-jr$ 的谱不含零，逆元属于原含单位 $A$，实虚部 $X,Y$ 均在完整原域。对实际PB $(r;X,Y)$，48.4先给真实位移的原元素等式

$$
v+jw=\tfrac j2[r,X]-r\circ Y
+j(r\circ X+\tfrac j2[r,Y])=jr(X+jY).
\tag{48.5}
$$

因此四个真正外层标签组成的两个复标签准确为

$$
(X-v)+j(Y-w)=(1-jr)A_r=T,
\quad (X+v)+j(Y+w)=(1+jr)A_r=C_rT.
\tag{48.6}
$$

这些是在原 $A$ 中的等式，保留任意表示核尾。$C_r$ 酉，故 $T^*T=(C_rT)^*(C_rT)$。原PB及48.2相减便得结论。这是AH7、13、24的同一相减机制；仅在一点识别内值不满足48.4。∎

**引理 48.3（有限而有截断的相位）。** 设 $s(x)$ 是46.1的局部秩一投影，$0\le f\le1$、$f\in C_c(U)$、$f(x_0)=1$，$\theta\in[-\pi,\pi]$。两次相同实际演员

$$
r(x)=\sigma\tan(\theta f(x)/4)s(x)\quad(x\in U),
\qquad r=0\text{ 于图外},
\tag{48.7}
$$

各有范数不超过一。其Cayley因子在图内为 $\exp(i\theta f s/2)$，两次的乘积为 $\exp(i\theta f s)$。

证明。$jr=i\tan(\theta f/4)s$，所以秩一线上

$$
\frac{1+i\tan(\theta f/4)}{1-i\tan(\theta f/4)}
=e^{i\theta f/2},
\tag{48.8}
$$

补空间上为一。$\sigma$ 在48.7中不可删去；$j=\sigma i$ 时这正是实现普通相位 $e^{i\theta}$ 的符号。分母不为零，参数在全截断带有限。能否把这些实际因子用于 $F_\sigma$，仍须每次独立支付48.4。∎

## 49. 局部箭头的全部实际前缀

**定理 49.1（先识别箭头）。** 取47.1所得 $B_\sigma$，在 $O\subset O_\sigma$ 上固定局部单位截面 $e$，记 $p=\theta_{e,e},q=1-p$。若同一实际 $W\in A$ 在整个 $O$ 满足

$$
q(x)\pi_x(W)q(x)=0,
\tag{49.1}
$$

则对每个 $x_0\in O$ 有 $\pi_{x_0}F_\sigma(W)=0$。$W$ 在其他点和 $J$ 外的背景任意。

证明。先支付一步局部侧面运输。取46.1的侧面单位截面 $v\perp e$，$s=\theta_{v,v}\le q$，以及实 $\lambda\in C_c(U)$、$U\subset O$。实际 $r=\lambda s$ 延零属于 $B_\sigma$。对当前实际箭头 $T$，48.3的逆元在 $U$ 内与 $p,q$ 交换，故

$$
q(1-j\pi_xr)^{-1}\pi_x(T)q=0,
\qquad s\pi_x(X)s=s\pi_x(Y)s=0.
\tag{49.2}
$$

在每个 $\pi_xr\ne0$ 的点，符号都为 $\sigma$，45.1分别识别实际 $(r,X)$ 和 $(r,Y)$ 的旧输出；这包括任意非零截断值。其余所有不可约表示中 $r$ 的像为零，43.2分别支付这两份实际输出。不可约表示分离 $A$，于是先取得48.4的两条全域等式，再应用48.2。$C_r$ 与 $p,q$ 交换，且图外为一，所以整个 $O$ 上的箭头条件被保留。

在指定点，把 $\pi_{x_0}W$ 写成

$$
\begin{pmatrix}\alpha&b^*\\c&0\end{pmatrix}
\quad\text{相对于 }\mathbb Ce\oplus qH_{x_0}.
\tag{49.3}
$$

若 $b=0$ 或 $c=0$，实部与 $j$-虚部已共同支撑于至多二维角，44.1直接识别其自己的旧值。否则在有限空间 $L=\operatorname{span}\{b,c\}\subset qH_{x_0}$ 上选酉 $V$，使 $Vc=(\|c\|/\|b\|)b$，在 $L^\perp\cap qH_{x_0}$ 上为一。有限酉谱定理把它分成至多两条秩一谱相位，角度取于 $[-\pi,\pi]$。由46.1把这些有限谱射线延成始终垂直 $e$ 的局部框架；缩小 $U$ 并取一个在 $x_0$ 为一的截断。

对每个谱相位使用48.7两次。每份实际逆标签、每个截断过渡值及每份实际前缀都满足49.2，故上一段支付全部步骤。实际终点 $W_m$ 在目标点为

$$
\pi_{x_0}W_m=
\begin{pmatrix}\alpha&b^*\\(\|c\|/\|b\|)b&0\end{pmatrix}.
\tag{49.4}
$$

其两份自伴标签才共同支撑于 $\operatorname{span}\{e,b\}$，由44.1得 $\pi_{x_0}F_\sigma(W_m)=0$。沿这条有限实际链的原元素等式返回即得结论。没有把秩二的箭头直接认作同一二角，也没有要求 $b,c$ 随点形成可延的谱场；只延目标点选定的有限射线。∎

## 50. 箭头支付任意背景的局部秩一全行

**定理 50.1（原代数中的全行等式）。** 在 $O\subset O_\sigma$ 的局部框架上，任取实 $g\in C_c(O)$ 及实际 $r=gp$、图外延零，则对每个实际 $a\in E$，

$$
D(r,a)=K_\sigma(r,a)
\quad\text{在整个原 }A\text{ 中成立}.
\tag{50.1}
$$

证明。固定实际 $d=D(r,a),t=r\circ a$，保留PB $(a;r,0)$ 的两份真正复外层标签

$$
W_+=r-d+jt,\qquad W_-=r+d-jt.
\tag{50.2}
$$

在整个 $O$，43.1给 $q\pi_x(d)q=0$，也有 $q\pi_x(t)q=0$，故两者满足49.1。49.1分别识别两份真实外值的像。固定活跃点，记 $R=\mu p,T=\pi_xa,d_x=\pi_xd$。PB遂给

$$
2R\circ d_x
=K_\sigma(R-d_x,R\circ T)-K_\sigma(R+d_x,-R\circ T)
=2R\circ K_\sigma(R,T).
\tag{50.3}
$$

这是先识别两份实际外值、再展开已知交换子。$d_x-K_\sigma(R,T)\in\mathbb Rp+H_e(qH_x)$，$\mu\ne0$ 时 $R\circ-$ 在该空间单射；$\mu=0$ 时43.2直接给零。对所有其他不可约表示，$\pi r=0$，同一旧输出由零槽为零，比较交换子也为零。全族分离给原元素等式50.1。其第二输入的射线对角、连接及任意有界补角背景都未受限制。∎

## 51. 同一残差的双侧有限相位

**定理 51.1（任意实际目标的有限运输）。** 固定 $x_0\in O_\sigma$。对每个实际 $W\in A$ 及任意酉 $U,V\in B(H_{x_0})$，若 $U-1,V-1$ 均有限秩，则可构造一份原域中的有限实际终点 $W'$，满足

$$
\pi_{x_0}W'=U\pi_{x_0}(W)V,
\qquad F_\sigma(W')=F_\sigma(W).
\tag{51.1}
$$

证明。有限秩扰动酉在某有限维子空间外为一；有限谱定理给有限条秩一谱相位。46.1把目标点这有限组射线延到一个局部框架，并取支撑紧含于 $O_\sigma$ 的截断。每个相位用48.7的两份实际演员实现。50.1对每个实际第二输入都成立，因而每次48.3的两份逆标签都满足48.4；48.2逐步给原元素等式。于是所有左有限相位都合法。

右侧不需新的原演员定理。定义实际标签变换 $\tau(W)=jW^*$。若 $W=X+jY$，则 $\tau(W)=Y+jX$，由反对称性

$$
F_\sigma(\tau W)=-F_\sigma(W),\qquad
\tau(C\tau W)=WC^*\quad(C\text{ 酉}).
\tag{51.2}
$$

将已付左链用于 $\tau W$，再用 $\tau$ 返回，便实现右有限相位及同一残差。有限次复合给51.1。此处只构造局部秩一Cayley因子，未声称任意纤维酉具有全局酉提升。∎

## 52. 直接消费固定输出的单向量预算

**定理 52.1（连续迹支撑表示上的全部原输入）。** 对每个 $x\in X$，若 $\dim H_x\ge2$，则全部实际 $a,b\in E$ 满足

$$
\pi_xD(a,b)=\sigma_{\pi_x}\frac i2[\pi_xa,\pi_xb].
\tag{52.1}
$$

一维点上的全部旧值为零。此定理不要求 $J$ 本质。

证明。固定非经典 $x$，47.1供应包含它的同向开理想，51.1供应任意实际目标所需的全部双侧有限相位，43.1供应每个实际终点的P2。现在准确复用AH8.1的固定输出双侧单向量估计，不另计该估计为新增证明。

具体代入为：取实际 $W=a+jb$，$T=\pi_xW$，$M=\|T\|$，固定单位 $\xi$。AH8.1只要求共同可达的两个有限秩扰动酉及P2；51.1支付前者。其近范数单位向量 $v$ 给 $r=\|Tv\|>0$，同一对左右酉所得算子 $Z=UTV$ 满足

$$
Z\xi=r\xi,\quad
\|Z^*\xi-r\xi\|\le\sqrt{M^2-r^2},\quad
\|\operatorname{Im}_jZ\,\xi\|\le\tfrac12\sqrt{M^2-r^2}.
\tag{52.2}
$$

实际终点自身的P2及比较交换子界因而给同一个固定残差的读取

$$
|\langle\xi,\pi_xF_\sigma(W)\xi\rangle|
\le M\sqrt{M^2-r^2}.
\tag{52.3}
$$

$r$ 可任意接近 $M$，所以固定左侧为零；$M=0$ 直接用零槽。对全部 $\xi$ 极化即得52.1。AH8.1的证明适用于非紧 $T$ 和不可分 $H_x$：只针对一个固定算子取近范数向量，不取可数稠密基。这里没有输入 $D$ 的任何极限、全局正化、Borel投影或强星极分解逼近。一维点已由43.1的标量Gram处理。∎

## 53. 本质性只认回输出与两个取向理想

**引理 53.1（本质理想的支撑表示联合忠实）。** 若 $J$ 本质，则 $\{\pi_x:x\in X\}$ 联合忠实于 $A$。

证明。若这些表示都消去 $z\in A$，任取 $l\in J$，每个 $A$ 的不可约表示都消去 $zl,lz$：在 $J$ 上非零者由46.2及假设消去 $z$，其余消去 $l$。不可约分离性给 $zJ=Jz=0$，本质性给 $z=0$。联合忠实星表示也等距并反映正性。∎

**定理 53.2（最小取向几何及唯一性）。** 在42.4的前件下，定义

$$
h_\pm(a,b)=D(a,b)\pm\tfrac i2[a,b],
\qquad\mathfrak c_\pm=
\overline{\operatorname{Id}_A\{h_\pm(a,b):a,b\in E\}}.
\tag{53.1}
$$

则42.8及42.7成立；它们不依赖本质连续迹理想的选取。

证明。43.2给两生成集都属于 $\mathfrak c$。由52.1，$J$ 的每个正向点消去所有 $h_-$，每个反向点消去所有 $h_+$，经典点同时消去两者。因核为理想，全部支撑表示消去 $\mathfrak c_+\mathfrak c_-$，53.1给

$$
\mathfrak c_+\mathfrak c_-=0.
\tag{53.2}
$$

正交闭理想的代数直和是闭的：范数为两分量范数的最大值。又

$$
\tfrac i2[a,b]=(h_+(a,b)-h_-(a,b))/2
\tag{53.3}
$$

生成 $\mathfrak c$，所以 $\mathfrak c=\mathfrak c_+\oplus\mathfrak c_-$。定义乘子 $Q(z_++z_-)=z_+-z_-$；它中央、自伴且平方为乘子单位。53.3及 $D=(h_++h_-)/2$ 给42.7。

若另一个中央乘子 $Q'$ 给相同响应，则 $(Q-Q')i[a,b]/2=0$。中央性使它消去这些元素的左右理想生成集，连续性使它消去整个 $\mathfrak c$；故 $Q=Q'$。于是其谱投影 $(1\pm Q)/2$ 的像理想也唯一，并由53.1直接恢复。$\mathfrak c=0$ 时43.2给唯一零响应，无需为经典部分添加符号。∎

**推论 53.3（谱表述）。** 非零 $\mathfrak c$ 上，$Q$ 等价于 $\operatorname{Prim}\mathfrak c$ 上连续二值函数。可用Forger–Paulino arXiv:1307.4458v1、Theorem 2的Dauns–Hofmann接口

$$
C_b(\operatorname{Prim}\mathfrak c)\cong Z(M(\mathfrak c)),
\qquad \Phi(f)z-f(P)z\in P.
\tag{53.4}
$$

这里 $C_b$ 指有界连续函数。该谱改写不是53.2构造所必需；不要求 $Q\in Z(A)$ 或符号越过交换边界延拓。

## 54. 逆向逐个支付全部原关系

**定理 54.1（任意二值中央分解的完整逆向）。** 给定含单位复C*代数 $A$ 及 $\mathfrak c$ 的任意有序正交闭理想分解，42.7定义的总映射满足42.2的全部原关系。这一逆向本身不要求本质连续迹理想。

证明。$Q$ 是自伴中央乘子，作用于自伴交换子 $i[a,b]/2\in\mathfrak c$ 后仍为原自伴元素；总映射合法、实交替双线性。对任一不可约 $\pi$，若 $\pi(\mathfrak c)=0$，则 $\pi(A)$ 交换且不可约，故为标量。否则 $\pi|_{\mathfrak c}$ 非退化且不可约，中央乘子 $Q$ 的延拓由Schur引理为标量 $\sigma_\pi=\pm1$。因而该不可约像中的响应是 $K_{\sigma_\pi}$，对全部输入使用同一符号。

原二表的任意复二次型在正向像是 $Z^*Z$，反向像是 $ZZ^*$，其中 $Z=z_1\pi(a)+z_2\pi(b)$；标量像无区别。所有不可约表示反映正性，故二表对每个原正评价都半正定，两种次序的Hermitian性也成立。这给全部A1/P2，未删去任意质量。A2的实三表二次型为 $\gamma((\sum t_l a_l)^2)$，相加指定向量给实际零平方，全部排列同理。A3由同一原C*谱序给出。

最后任取实际三元组 $(h;a,b)$，先按42.3用这个已定义的同一 $D$ 形成真正内外层。固定不可约表示及它的符号，令 $j=\sigma_\pi i$、$W=\pi a+j\pi b$、$H=\pi h$。直接代入实际内值给

$$
\pi r_\pm+j\pi s_\pm=(1\pm jH)W.
\tag{54.1}
$$

对这份真正外层继续使用同一个已定义响应，得到

$$
\begin{aligned}
\pi(r_\pm^2+s_\pm^2+2D(r_\pm,s_\pm))
&=(\pi r_\pm+j\pi s_\pm)^*(\pi r_\pm+j\pi s_\pm)\\
&=W^*(1+H^2)W.
\end{aligned}
\tag{54.2}
$$

标量表示任取 $j=i$，交换子零，仍满足同式。故所有不可约表示给相同的正负端平方，分离性给完整原PB元素式，全部原评价随后读取。每个 $h,a,b$、每个真实内输出和四个原外层标签都在此计算中，绝非仅检验零第三标签片段。∎

## 55. 识别后的同一乘法、商与全部原质量

**推论 55.1（静态代数后果）。** 在42.4的前件下，

$$
\|D(a,b)\|\le\|a\|\|b\|,
\qquad
x\star_Qy=\frac{xy+yx}{2}+\frac12Q(xy-yx)
\quad(x,y\in A)
\tag{55.1}
$$

给原Banach空间上的含单位C*乘法，自伴部分、Jordan积、伴随、正锥与原范数全部保持；自伴输入上为 $S-iD$。

证明。42.7直接给实双线性及范数界。每个不可约像在其正向部分使用通常乘法，在反向部分使用相反乘法，在经典部分无区别；54.1证明了这套取值对任意二值中央分解成立。不可约分离性给结合律与星律，保单位来自 $[1,a]=0$。原范数的次乘性与C*恒等式分别由

$$
\|x\star_Qy\|\le\sup_\pi\|\pi x\|\|\pi y\|
\le\|x\|\|y\|,
\qquad
\|x^*\star_Qx\|=\sup_\pi\|\pi x\|^2=\|x\|^2
\tag{55.2}
$$

给出。原空间完备，故为C*代数。每个自伴平方保持，因而两个C*正锥相同；单位和实范数也相同。这里 $Q$ 只作用于交换子理想，不要求 $Qx\in A$ 对所有 $x\in A$ 成立。

对于任意闭理想 $L\triangleleft A$，中央乘子保持 $L\cap\mathfrak c$：可用 $\mathfrak c$ 的近似单位将乘子作用写成 $L$ 中的范数极限。因此改变任一输入一个 $L$ 元素，只改变输出一个 $L$ 元素；旧响应在 $A/L$ 上真正下降。其范数连续性与所有这些核平移结论都在42.7之后获得。∎

**推论 55.2（原Gram、R与保质量表示）。** 对任意有限实际输入 $a_1,\ldots,a_m$、复系数 $z_l$ 及原评价 $\gamma$，

$$
\sum_{k,l}\overline z_kz_l
\{\gamma(a_k\circ a_l)-i\gamma D(a_k,a_l)\}
=\gamma_{\mathbb C}(Z^*\star_Q Z)\ge0,
\quad Z=\sum_l z_l a_l.
\tag{55.3}
$$

且同一旧输出作为外层输入满足原R：

$$
(a\circ b)\circ c-D(D(a,b),c)
=a\circ(b\circ c)-D(a,D(b,c)).
\tag{55.4}
$$

证明。55.3是55.1的正平方展开，55.4是自伴三输入结合律的实部。于是准确取得AQ32.1–32.2、23.1、6.3与AH40.1已列静态消费者的入口；这里直接复用其GNS后端。每个原评价延成相同范数与正锥上的正复泛函，GNS向量满足 $\|\xi_\gamma\|^2=m_\gamma$、$\gamma(a)=\langle\xi_\gamma,\Pi(a)\xi_\gamma\rangle$。原评价分离且决定锥，直和表示忠实、保单位、等距并反映正性。零质量对应零向量；一般非正常评价没有被删去或换成正常态。数学表示像不必是全 $B(H)$，也不产生实际准备或菜单。∎

## 56. Type I、无统一上界FDI与准确外边界

**定理 56.1（type I的本质连续迹入口）。** 每个非零type I C*代数都含有本质连续迹闭理想，不需要可分或统一不可约维数上界。

证明。这里type I指C*代数意义的type I，即GCR/postliminal；无可分限制的等价采用Blackadar IV.1.4.27及IV.1.5.8。所需成熟输入准确为Dixmier《Traces sur les C*-algèbres》Proposition 9，印刷页241：每个非零GCR代数含一个非零连续迹闭双边理想。该命题不附可分假设。

在 $A$ 的非零连续迹闭理想中，用Zorn引理取极大的两两正交族 $(J_\nu)$，令

$$
J=\overline{\bigoplus_\nu^{\rm alg}J_\nu}
\cong\bigoplus_\nu^{c_0}J_\nu.
\tag{56.1}
$$

正交性给有限和范数为分量范数最大值，所以闭包恰为 $c_0$ 直和。其不可约谱是不交并，各分量在这个谱中开闭。每个分量中有限连续迹正元素的有限分量和具有连续有限迹，且其线性包稠密于整个直和。因此 $J$ 连续迹。

若 $I=\operatorname{Ann}_A(J)\ne0$，它仍是type I。Dixmier命题给 $I$ 中非零连续迹闭理想 $L$；理想的理想也是 $A$ 的理想，而 $LJ=JL=0$，违反极大性。所以 $J$ 本质。此证明没有从全局迹元素理想 $m(A)$ 推断存在性，也没有使用超限归纳。

Blackadar IV.1.4.29另给postliminal代数的连续迹子商组成列；其选择非典范，且IV.1.4.30的 $m(A)$ 迭代不能与这份组成列混同。本定理只用Dixmier的非零理想命题及上述极大族论证，不需要为Fell某定理附加未经使用的完整组成列归属。∎

**推论 56.2（所覆盖的完整域）。** 42.4覆盖全部含单位type I C*代数，包括每个不可约表示有限维但维数无统一上界的FDI代数。这里“每个不可约有限维”直接蕴含GCR，因为其像是该有限Hilbert空间的全部矩阵代数。

它也覆盖任意Hilbert空间上的 $B(H)$：$K(H)$ 是连续迹闭理想；若 $zK(H)=0$，逐个秩一算子给 $z=0$，故本质。非平凡 $H$ 的恒等表示忠实，52.1还直接给这个模型的一个全局共同符号。无限维 $B(H)$ 的这个适用理由是本质 $K(H)$，不将它冒称为type I C*代数。$\dim H=1$ 时为经典零响应。

**边界 56.3（未被本定理闭合的域）。** 一般不完整原域、适当JC子域、一般JB域及没有本质连续迹理想的完整C*域不在42.4的前件内。无限维简单CAR及无限维简单UHF没有非零连续迹理想：简单性会迫使该理想等于自身，而简单连续迹C*代数为 $K(H)$，含单位又迫使 $H$ 有限维。这只是适用范围排除，不是这些域中完整PB的反模型或不可能性定理。一般域的输入作用纤维桥仍未在这里证明。

AH32–41的有限统一阶数subhomogeneous结论原样复用；本增补去掉的是这条有限上界要求在当前完整C*分支上的必要性。其新增接线是44节有限支撑原像转移、45节无限有界背景、46–51节局部有限框架与同向理想实际演员。AH8.1估计、已成立的有限角计算和GNS后端都不重新计作新结果。

## 57. 完整原候选及递归固定的七项来源合同

**定义 57.1（全文合同的严格身份）。** 本文的 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ 准确等于本提交AH28.1定义的谓词：SQ47.1–47.13全部定义、合同、公式和量词，连同每项递归纳入的固定上游全文，同时作严格合取。它不是七个标题、七个新谓词或下文消费者说明的合取。固定来源按层解析：AH22.1的读取身份为 `2addd6f369b7387226c2b0cc984623dd3efe40a1`，其保留的AH12.1上游身份为 `39a0505470ea889dd9d4301ad60cd9506a5e8b58`；SQ41.1的主源链接 `JOR-main` 指向 `dcaebc0b9ca5a3a463fd8cfd161d38967df28668` 的SQ文件，SQ39另保留 `0aa11dbc3dc337d667b98900673e07d67b99bf46` 的主固定来源；SQ1.3、39及47.1中的OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF单项身份为 `f24d1138a7b994da16abd9a47affedea64ea44ce`。这些层级不被本文读取提交覆盖或压平。特别，SQ合同中的SM是谱混合响应卷，PT是配平三角卷，PB另指原多项式PB运输卷，不能与本文的临时简称混用。

单项路径均以 `docs/develop/theory/` 为前缀，在上一段的 `f24d1138a7b994da16abd9a47affedea64ea44ce` 中解释，准确对应为：

| 合同内缩写 | 固定文件名 |
| --- | --- |
| OP | `AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md` |
| PT | `AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md` |
| PB | `AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md` |
| SM | `AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md` |
| C | `AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md` |
| AQ | `AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md` |
| R3 | `AURIC_C128_THREE_LABEL_POSITIVITY_AND_ORIGINAL_RELATION_RIGIDITY.md` |
| W | `AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md` |
| FR | `AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md` |
| XV | `AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XV.md` |
| SF | `AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md` |

只把完整合同消费的被选静态入口接到42.2、55.1–55.2的同一资料及同一 $\star_Q$；不把 $\Omega$ 的其他原根、静默、II₁或其他静态分支改成当前模型。为明确全文的实际范围，以下保留AH28.1的完整定义及其逐项展开；展开内部的原编号、版本和递归引文均属来源合同，不重编号为本增补的新数学声明。

> **定义 28.1（严格全文纳入及引文身份）。** 记 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ 为固定SQ第47节全部定义、合同、公式、量词及其逐项纳入的固定上游全文的严格合取。这与SQ64.1、69.2及AH20.1规定的全文语义一致；不是七个标题或消费者摘要。下文逐字引用固定SQ47.1–47.13，连同七项合同，保留其原编号。引文中的“主源”、缩写及版本按SQ自身1.3、39、47.1解析，不能改成本增补的局部编号；其中SM指《谱混合响应与直接窗口边界》，AQ才是本文的静态重构卷。引文逐项纳入的上游全文继续合取，不能由引文展开删减。原根、静默和其他静态分支不被改成三阶模型。
>
> > ## 47. 同一原世界的七项来源全文合同
> >
> > **定义 47.1（完整来源谓词及同一性）。** $\mathcal C_{\rm src}(\Omega;S,D)$ 严格取固定主源第11–12、24、28及37–38章所有实际来源条款及它们逐项纳入的上游全文之合取。只把它们消费的静态入口替换为44章的同一 $S,D$ 及相容 $M_{\sigma_D}$，不额外要求原 Jordan 丛已有复乘法、平凡或有全局矩阵单位。下列展开与被引用的全文同时合取，不将任何一条充分前件改成摘要。所有缩写与上游版本严格采用主源1.3、39；OP、PT、PB、SM、C、AQ、R3、W、FR、XV、SF 均固定于 `f24d1138a7b994da16abd9a47affedea64ea44ce`。
> >
> > 具体包括 SF105全文、106.1；OP29.2、78.2、87.1及其纳入的18.2、24.1、57.1、63.2、70.1；FR139.1–139.2、147.1–147.3、155.1–155.2；XV14.1、20.1–20.3、23.1–23.5；R3 8.1–8.5、80.1；AQ8.3–8.4、14.2、25.1、53.1；W95.2、116.1，以及它们逐项纳入的全部原来源、实现、对象和充分条件。SM78.2、86.1及43.2、49.1、61.1、69.1，中央续卷 C145.1–145.7、155.1、160.3、171.1–171.7、181.3、186.1–186.7、194.2、199.2与PB122.1中有关的原量词也全部保留。
> >
> > 原世界仍只有同一个 $\Omega/\mathrm{native}$。原对象、准备、事件、设备、程序／过程、比较权 $q$、跨标签全词共同 $K/J$，原 $J,S,U,D_{\rm network},C,G,M_j,N_j,AS,R_2$ 和全部模式网络保持身份。原网络的 $D_{\rm network}$ 不是本响应 $D$，网络中的 $C$ 也不是数学正锥；来源中的 $\sigma,t_0,d$ 不是本取向截面、底点或矩阵阶数。
> >
> > 所有原中心、经典、不等维块、无轴和静默对象保留；零、不等和次归一质量保留；实际乘积、真正相关联合、参考／副本及每层递归同源引用保留。parent、ready、合法控制、旗标、整个环境、原钟及单位、同一原 $\sigma,t_0$、全部原菜单、固定支持的全质量、每个原中间切口均不得用数学坐标代换。全部合法顺序、自适应、并行历史，以及每份完整输出的每个仍合法未来，均在原类型内量化；细记录、失败、拒绝、停止、销毁、泄漏、真正分组遗忘、同数两侧返回及真实逆向返回同样保留。
> >
> > 未定义请求不补成零箭头。相同矩阵、相同当前读数或相同纤维像，不合并不同原程序、历史、输出、原 $q$ 零集和未来权限。本模型只指定被选静态对象 $E=\Gamma(X,\mathfrak J)$；不将 $\Omega$ 的其他对象和其他静态分支强制为同一固定 $n$ 的模型。所有“全部”“每个所需有限长度／深度”“每个正精度”在原消费者的合法适用域保持完整强度。$M_\sigma$ 中的归一纤维迹 $T_\sigma=\operatorname{Tr}/n$ 只是数学读取，不是原准备、原质量或物理概率。
> >
> > **定义 47.2（原根类、十一端点及静默支）。** 完整根类 $\mathfrak K_{\rm r}$、候选 $\mathsf Q^{\rm root}_{46}$ 和它们全部原背景与主源37.2一致。全部 $89$ 配置、$235$ 实际逆等距边、固定外位 $10/010$、原黄金块、阻塞值、两个边界、严格左响应、十一回返、十个相邻 Artin 与四十五个远关系，同一个原正定度量 $g$ 与给定单位 ready，均在同一原对象上。原 $26+63$ 扇区、读后七地址、$1024$ 终端标签、原读器、报告、调用顺序、细档案及全部失败类型没有被压缩成代数标签。
> >
> > 程序签名仍为十一地址有限前读词后接旧终端，或先读并保留 $b_9$，再接不依赖该记录的外生七地址后词并接旧终端；它不自行给出新分析器或菜单 producer。原根条件为
> >
> > $$
> > \begin{gathered}
> > s=(3,7,1,2,4,5,6,8,9),\qquad
> > \operatorname{tr}_{V_r}(L_r^\dagger L_r)=2,\\
> > \|U_si_rL_r\|_{\rm HS}^2\le2
> > \quad\text{对全部原 }\mathfrak K_{\rm r}\text{ 资料}.
> > \end{gathered}
> > \tag{47.1}
> > $$
> >
> > 原 $r,i_r,L_r,U_s$ 及 Hilbert–Schmidt 迹保留原数学身份，不改成 $T_\sigma$ 或物理准备、读口、概率。XV23.2的既有等价将(47.1)接到全部原输入及全部十一端点的 E1：
> >
> > $$
> > U_j^\dagger U_j=I\qquad(0\le j\le10).
> > \tag{47.2}
> > $$
> >
> > 同一 ready 的 $\rho=\|L_ru_*\|=0$ 及 $k=0$ 都在域内，不补正活动公理、不改 ready。$k=0$ 的单位 ready 有 $\rho=1$，$k>0$ 的全静默 ready 同样保留；零根响应、零活动及其合法未来均不删。
> >
> > 同一 ready 的两标量词备选仍按原分支使用：$\rho>0$ 要求原 $s$、$(0,s)$ 两词不膨胀，$\rho=0$ 则保留全输入、全十一端点的(47.2)。XV14.1的一次固定全支撑词 $a$ 与 $(0,a)$ 备选及176有界长度词表备选，各守自己的句法和零活动支。两条静默 ready 的零缺陷不代替全 E1；根迹条件、两词条件及有界长度观察不被合成更弱条件，也不从词长或数学迹推出物理费用。
> >
> > **定义 47.3（其他原静态分支）。** FR139.1、155.1和XV20.1所列各支完整保留。有限原响应支具有同一原实载体、准确评价锥、全域序界、序单位范数、全部原对实际共轭、相加三表及全部排列的实部 PSD、指定相加零方向、总事件固定与同一正有理小窗口。全原三元实部换括号，以及同一实际旧输出集合及其原量词上的输出辨识，仍按该支的原条件，零原空间也在域内。
> >
> > 指定完整 II₁ 支保留同一原含单位复因子、完整自伴域、Jordan 平方、准确锥／单位／范数、指定前对偶、正常忠实归一数学迹、原实际共轭、全实部关系及旧输出辨识。该迹既不等于原质量，也不由有限返回或本模型的纤维迹制造。
> >
> > 其余原载体支继续要求全部至多二标签的实际复表正性，含零、重复与缩放；全部相加三表，以及满足某对
> >
> > $$
> > N(a_i-\epsilon a_j)\le\tfrac14\max\{N(a_i),N(a_j)\},
> > \qquad\epsilon\in\{-1,1\},
> > \tag{47.3}
> > $$
> >
> > 的全部三表、全部排列和任意第三标签，在整个
> >
> > $$
> > F_3=\bigcup_j\{x+it e_j:x\in\mathbb R^3,t\in\mathbb R\}
> > \ \cup\ \{z\in\mathbb C^3:\textstyle\sum_jz_j=0\}
> > \tag{47.4}
> > $$
> >
> > 上非负，连同相加零平方、总事件、小窗口、全实部式及全部原背景。差分面、无限支撑、整个 $F_3$ 与旧全响应量词保持，CountRead不被移入有限支。
> >
> > 既有一般同平方 JB 恢复、完备原序单位路线、固定 $B(\ell^2)$ 路线、指定原理想传播及原词恢复，分别继续使用其关系逼近、有限依赖反映、全输出统一误差、完备性、正常性、原包含和作用纤维条件。它们在已成范围直接复用，既不被降为未证明，也不把它们的额外前件赠给一般原对象。
> >
> > **合同 47.4（复 Hilbert、可观测量和实际相干叠加）。** 原具名可取得标签、比较权 $q$、native、共同跨评价配对、全部原词、parent、ready、合法控制、实际相干准备、全部根及静默分支保持。数学表示不生产任意向量准备、全 $B(H)$ 的可取得像、免费控制、复制或原设备。
> >
> > 指定原词空间仍为同一复空间 $V_{\rm nat}$、第一槽共轭线性的半正定 Hermitian 型 $K_{\rm nat}$、全部原 $\xi_\gamma$ 及原总集合映射 $\mathsf J_a:V_{\rm nat}\to V_{\rm nat}$，并完整要求
> >
> > $$
> > \begin{aligned}
> > K_{\rm nat}(\xi_\gamma,\mathsf J_a\xi_\gamma)&=\gamma(a),\\
> > K_{\rm nat}(\mathsf J_a z,\mathsf J_b w)
> > &=K_{\rm nat}(z,\mathsf J_{a\circ b}w)
> > -iK_{\rm nat}(z,\mathsf J_{D(a,b)}w),\\
> > V_{\rm nat}&=\operatorname{span}_{\mathbb C}
> > \{\mathsf J_{a_1}\cdots\mathsf J_{a_k}\xi_\gamma:
> > k\ge0,\ a_j\in E,\ \gamma\in\mathcal P\},\\
> > K_{\rm nat}(\xi_\gamma,\xi_\gamma)&\le m_\gamma,\\
> > K_{\rm nat}(\mathsf J_a\xi_\gamma,
> > \mathsf J_c(\mathsf J_a\xi_\gamma))&\ge0\qquad(c\in C).
> > \end{aligned}
> > \tag{47.5}
> > $$
> >
> > 第一行量化全部 $a\in E$、$\gamma\in\mathcal P$，第二行量化全部 $a,b\in E$、$z,w\in V_{\rm nat}$，末行量化全部 $a\in E$、$\gamma\in\mathcal P$、$c\in C$。词必须先按原总映射实际复合，再取有限复线性包；空词及任意有限长度都包括。这个共同 $K_{\rm nat}$ 保留全部指定跨评价配对和有限正表，不能用每份评价独立的 GNS 核替换。没有预给 $\mathsf J_a$ 线性、$\mathsf J_0=0$ 或 $\mathsf J_u=I$，其恢复依原消费者的次序。
> >
> > $q_{\rm nat},K_{\rm nat},\mathsf J$ 就是上游原 $q,K,J$，其权、零集、跨标签意义、词身份和读序不变。它们不同于辅助 $q_D$、数学复化标量 $i$ 或取向截面。静态存在式 Hilbert 表示本身不认证这个指定原词实现。
> >
> > **合同 47.6（原态、效果、Born、全菜单及全部质量）。** 原评价与原事件的绑定、准确效果区间、接受归属、每份实际完整菜单仍由同一原世界承担。原互探 $\mathrm C_{12}$、mark、预定处处有限强度尺、$\mathrm A_{12}$、全部背景 $\mathrm{BI}_{12}$、非负性，以及消费者要求的有限维／最小可见／实尺度条件全部保留；原强度、原 $q$、中央比较权及概率质量不合并。
> >
> > Fourier9.6–9.12、10.10、17.9、18.12的共同根、有限实际端口、原角／二十七模适配器、完整坐标分区、真实独立抽签、每条所用平衡行、全部原目标和每个原 $(\xi,g,s)$ 的菜单覆盖都必须保持。具名事件按先原 $g^*$、再原 $d_s^*$、最后同一原根的物理顺序合法接续。同矩阵的不同原字分别支付覆盖；每个 P9 分支自己的独立 $W_e$、原权／质量校准、原接受事件与合法复合、其他块自己的 AS/EC、菜单外 OB、真正忠实二维到三维的全质量适配器及非零一维块均保留。纯校准子域不能代替全菜单、固定支持全质量和每个已量化中间切口。
> >
> > 两只独立九叶彩票 $(6,2,0)/9$、$(4,4,0)/9$，各自第九空程序、十六拒绝叶，以及相干 $I_3/3$ 返回保留细记录和原类型；相干返回不被细测成三个经典结果。
> >
> > 实际完整有限菜单 $\{e_j\}$ 只有在原事件绑定、$\sum_je_j=u$ 和 $m_\gamma>0$ 同时成立时才定义
> >
> > $$
> > p_\gamma(j)=\gamma(e_j)/m_\gamma.
> > \tag{47.6}
> > $$
> >
> > 实际角菜单另须 $\sum_je_j=p$、原条件化身份及 $\gamma(p)>0$，才取 $\gamma(e_j)/\gamma(p)$。零、不等、次归一、中心权、经典混合、不等维及静默块的未归一读数全部保留，零质量不作除法。条件更新另须严格正的实际输出质量。
> >
> > 一般原态仍是正泛函。密度／迹类公式只在原有限全矩阵物理表示及过程绑定的域，或适用完整正常 $B(H)$ 接口、指定前对偶及相应收敛齐备的域使用。一般非原子中心或一般正规子代数的前对偶不自动给全 $B(H)$ 密度式。无限或非离散菜单的可数可加、正常性及前对偶另守47.12的原扩展条件。
> >
> > **合同 47.7（native、真正相关联合与张量）。** 原全词同一 $K/\mathsf J$、交叉零、同一旧局部乘法、每个中心对、经典／不等维／静默块、真实乘积及全部真正相关输入，都必须在一个实际共同实现中取得。每个被消费的局部全矩阵接口必须忠实、同向并交换；联合共同生成、原评价分离、所需重数、实际复制及每层递归同源参考，采用AQ53.1、AQ25.1第三行与W95.2、116.1的完整原量词。
> >
> > 只有同一个实际非零有序联合中忠实同向交换的两个局部全矩阵腿共同生成时，乘法才识别联合为 $M_d\otimes M_r$。具体 Hilbert 载体的重数还须原重数或不可约条件。一般中心情形对每个实际非零中央对都保留共同支持、共同生成和全部相关输入，不能由一个中央对替代全部中央对。
> >
> > 分别可达、相同边缘、数学交换或相同符号都不生产共同来源。42.9的辅助乘积环境不是该实际联合，原域中的辅助角也不是物理子系统腿、复制设备或自由参考。
> >
> > **合同 47.8（typed 箭头、CP 及整台递归参考）。** 对每条实际原细分支 $r:A_0\to B_0$，保留全部合法 typed 前接、真实未归一后上下文、每份完整输出的每个仍合法未来及全未来自然性。原回溯严格满足
> >
> > $$
> > \gamma_{A_0}(\beta_r b)=\gamma_{B_0}^{\,r}(b),
> > \tag{47.7}
> > $$
> >
> > 并保持反变合法复合、typed分区、全质量运输及原箭头商下降。异类型输出仍分别按类型进入分区。正次单位和完成上的正延拓不自动给 CP；CP 的全槽同标签单位区间比较路线，以及整台实际箭头递归同源参考路线，各须自己的全部原前件。
> >
> > 递归路线要求每条完整 $r$ 都有实际 $r^+:A^+\to B^+$。系统、整个环境、所有成功／失败／细记录／输入输出port／post-port输出，以及每份完整输出的每个仍合法未来，都属于同一个能再次应用的实际规则类；真正遗忘、实际返回与合法复合也在类内。形式 CP 不能反向制造这些实际箭头。
> >
> > 两端各有共同真支持 $p_A,p_B$ 及忠实同向交换星嵌入；$A$ 端为
> >
> > $$
> > i_A:\mathcal A_A\hookrightarrow p_A\mathcal A_{A^+}p_A,
> > \qquad j_A:M_2\hookrightarrow p_A\mathcal A_{A^+}p_A,
> > \qquad i_A(1)=j_A(I_2)=p_A,
> > \tag{47.8}
> > $$
> >
> > $B$ 端同型。三个实际参考投影 $q_1,q_2,q_3$ 与 $I_2$ 实张成 $(M_2)_{\rm sa}$。每次真实接线要求
> >
> > $$
> > \beta_{r^+}i_B=i_A\beta_r,\qquad
> > 0\le\beta_{r^+}(j_B(q))\le j_A(q)
> > \quad(q\in\{q_t,I_2-q_t:1\le t\le3\}).
> > \tag{47.9}
> > $$
> >
> > 全部原相关正输入及决定整个锥的全部原联合评价都在这些交织和夹界的量词内。支持内补为 $p-j(q)$，不替换为环境单位补。两腿不要求生成整个环境或支持角；下一层系统是整台实际 $r^+$ 的全部响应，不是根代码。
> >
> > 对每条根箭头及每个所需有限长度 $L$，存在完整实际长 $L$ 链；每个 $k\le L$ 都有忠实累计嵌入及准确支持运输
> >
> > $$
> > \begin{gathered}
> > M_A^k:\mathcal A_{A_0}\otimes M_{2^k}\hookrightarrow\mathcal A_{A_k},\\
> > \beta_kM_B^k=M_A^k(\beta_0\otimes\operatorname{id}_{2^k}),\qquad
> > P_A^{k+1}=i_{A,k}(P_A^k)\le p_{A,k+1}.
> > \end{gathered}
> > \tag{47.10}
> > $$
> >
> > 累计真支持不换为新环境共同支持或环境单位。任意精度路线保留精确根身份、同向结构、全部真支持／事件／相关输入／后口，并量化每个正精度和每个所需有限深度；一个固定正误差不足。每个有限长度的完整实际链，不等于要求一条实际无限链、物理无限张量积或免费旁接函子。根代码上任意多形式参考也不支付实际链。
> >
> > 已有原九号读口、它的实际参考／联合，以及准确来源已供应的有限返回刚性，按原条件继续使用，不倒称为缺失。返回复合 CP 不推出因子 CP 或一般箭头 CP。Kraus 算子式仍限合格有限全矩阵域，或另具适用正常物理表示、指定前对偶、分解和收敛的域；一般正规子代数正常 CP 对偶不自动给全 $B(H)$ Kraus 分解。
> >
> > **合同 47.11（完整仪器、TP、条件更新与 Lüders）。** 每台原实际仪器包括全部原输入运输、完整 typed 菜单、原接受端、整个环境、全部成功／失败／细记录／port／post-port输出，以及每份完整输出的每个仍合法未来。真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词及各自接受条件，严格取C171.5、AQ25.1第五行及其上游原合同；数学连续平方根不生产具名原平方根词。
> >
> > 同一正夹心只给静态代数入口。正次单位仅为 TNI；整个原测试的实际完整 typed 单位分区
> >
> > $$
> > \sum_r\beta_r(u_{B_r})=u_{A_0}
> > \tag{47.11}
> > $$
> >
> > 才给 TP。不同输出类型不免费识别为一个物理直和。Lüders 另外要求同一完整输出具有投影效果、像内每条射线保持及完整输出校准；相同效果、概率、统计重复性或仅支撑保持都不代付。
> >
> > 条件更新只在严格正的实际输出质量处归一。零和失败分支及其记录、原类型、全部合法未来仍保留。密度、迹类、Kraus、迹公式均守47.8的准确域与收敛。数学 Kraus 指标不是自动给定的 P9 细记录或物理环境输出，数学迹不抹掉 port 未来。
> >
> > **合同 47.12（全历史、真遗忘、真实返回与 CountRead）。** 全部合法顺序、自适应、并行历史，整个环境、参考副本、细记录和泄漏，停止、拒绝、销毁，真正分组遗忘，同数两侧实际返回和同数逆向实际返回，都保留原类型及每份完整输出的每个仍合法未来。粗事件只沿其实际分组相加；丢弃一份档案不等于真遗忘。数学算子相同不合并程序、读取次序、原 $q$ 零集或AC方向。
> >
> > CountRead 绑定读后同一原完整活动输入及它的全未来实际 Return。读后活动 ready 接头、接受叶活动输出、第一合法消费者、具名分析词到实际全菜单和原接受端，均需原生 producer。原读后表、分母、查询、细地址、失败和终端类型不变成可再次作用的旧 ready。负提升两条活路的分别受控实现和相干聚合实现分别守原合同；数学负号不构造活路，数值相消也不返回完整输出。
> >
> > 原精确正生成 $B_{\rm src}$ 和另名闭正生成 $B_{{\rm src},\rm cl}$ 保持上游 $B,B_{\rm cl}$ 的身份，二者不混同，也不与数学正绝对值混名。两只独立九叶彩票、各自第九空程序、十六拒绝叶与相干 $I_3/3$ 返回继续保留记录和类型，不被细读成三个经典结果。
> >
> > 既有 native 初始读取、指定有限树与被动精确混合解码只在原平稳、真实同源、同初始版本的范围内使用。初始取得不代替整份后续输出的全未来 Return。返回表示层恒等仍需全输出／全未来忠实绑定，原档案分离条件及已有正常性边界均不删除。
> >
> > 无限历史、无限或非离散记录、可数可加、物理正常性、指定前对偶及所需收敛分别取原扩展来源。有限 PB 调用、数学函数演算、纤维迹或数学正读取不生产物理无限记录和读后真正双向返回。未定义请求保持未定义；静默、零质量对象与它们的合法未来都在域内。
> >
> > **合同 47.13（物理钟、动力学、能量与共同正作用量）。** 同一旧全域乘法、保持原域的流、真实相位与原门序列、同一实际过程内连续可逆 CPTP 一参数群及实际逆、物理钟和单位、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、共同仪器、共同作用量及同一个正 $\hbar$ 都须保留。一般可能不完备原域的流保持另按原条件，不从本完整域上的数学流推出。
> >
> > 原 $\sigma,t_0,d$、固定域、resolvent 和 $3s+r\le1$ 预算始终属于原设备、原参数、原适用域和量纲，不改为取向、局部坐标或证明中的有限步数。数学指数、离散词、范数路径、数学逆与公共返回效率不生产物理时间、可控相位、能量解释、控制成本、真实原逆或跨装置共同作用量。
> >
> > 只有这些原条件齐备且表示／生成元域适用时，才使用
> >
> > $$
> > U(t)=e_{\cdot_\sigma}^{-itH/\hbar},\qquad
> > i\hbar\dot\rho=[H,\rho]_\sigma,\qquad
> > \dot b=\frac2\hbar D(H,b).
> > \tag{47.12}
> > $$
> >
> > 向量方程 $i\hbar\dot\psi=H\psi$ 限于对应自伴生成元域；无限维密度微分限于适用迹类可微域。所有公式都用同一已选乘法，不能在反向区域暗换普通矩阵乘法。有界数学内导子不代替无界 Hamiltonian、其定义域和实际酉群实现。
> >
>

**定理 57.2（同响应的完整条件等价）。** 当 $\mathfrak c\ne0$，固定42.2的背景且 $A$ 含本质连续迹理想时，完整候选恰为

$$
\begin{aligned}
&\mathsf H_A(D)\ \land\ \mathcal C_{47}^{\rm pin}(\Omega;S,D)\\
&\quad\Longleftrightarrow\quad
\exists!Q\in Z(M(\mathfrak c)):\quad Q=Q^*,\ Q^2=1,\\
&\hspace{44mm}D=K_Q\ \land\
\mathcal C_{47}^{\rm pin}(\Omega;S,K_Q).
\end{aligned}
\tag{57.1}
$$

交换情形用唯一 $D=0$ 与空取向。这里 $K_Q(a,b)=Qi[a,b]/2$。

证明。正向由52–53节识别同一个旧 $D$，来源合同始终绑定这份响应；逆向由54.1支付全部原关系。全文合取中其余实际来源没有被这个等式删除、产生或替换。55节支付的是各后端已明确的静态接口，不把SQ固定阶丛定理的模型前件直接套到变维谱。∎

**边界 57.3（七项消费者的条件性）。** 上引全文所规定的原词Hilbert实现与实际相干准备、态与Born完整菜单、真实相关联合与张量、全参考CP箭头、完整仪器及TP/Lüders、全历史与CountRead/真实返回、物理时间动力学，都只在各自全部原条件成立处消费55节的静态结果。

具体未由本定理生产的仍包括共同 $K_{\rm nat}/\mathsf J/q$、parent/ready及可取得准备、全部实际完整菜单及正分母、同一实际相关联合和全部中央对、忠实同向交换腿及共同生成和重数、每条整台箭头每个所需有限深度与每个正精度的递归同源参考、全部成功/失败/细记录/port/post-port输出和每份完整输出的每个仍合法未来、真正遗忘、同数两侧与真实逆向返回、读后活动ready及接受端producer。无限或非离散记录的可数可加、正常性、指定前对偶及收敛仍另有原来源；一般正泛函不自动是密度矩阵，一般正映射不自动CP，也不自动有适用的全 $B(H)$ Kraus式。

物理钟与单位、连续可逆实际过程和真实原逆、同一乘法下强连续酉实现、生成元域、能量解释、共同仪器及共同正 $\hbar$ 仍未构造。零、不等及次归一质量、经典/不等维/无轴/静默对象、未定义请求和全部合法未来均保留。定理57.2不是完整 $\Omega$ 起源已经实现的断言，也不保证每一种数学取向都具有实际来源实现。

## 58. 精确依赖、成熟来源与几何解释

**来源对应 58.1（数学依赖）。** 本增补的直接仓内依赖均为42.1的固定提交；其递归纸面前置不被提升为形式核验证据。

| 所用来源 | 准确用途与已支付的接口 |
| --- | --- |
| [PT128–129、183.2、185.1][ECT-PT] | 完整原候选、准确锥的数学正读取及整个含单位原域上的实际SO(2)旋转；不消费185.3未证的一般输入纤维桥。 |
| [PT241–245][ECT-PT]，[W110–112][ECT-W] | 43–44节重新支付实际有限支撑闭合、相对单位、纯像面积和小行纤维；W110–112只消费已核对的纯内积映射前件。 |
| [OP59–61、73–76、80–82][ECT-OP] | 44节按原标签转移全部纯像及混合像计算；原OP80有限全Jordan商前件没有直接套给压缩。 |
| [PT130–131][ECT-PT] | 44.21–44.23的三维反号证书及任意二平面传播；外层只用各自P2。 |
| [AH7–8、23–25、36][ECT-AH] | 实际双侧相位和两射线机制；45节保留任意无限有界背景，46–51节支付局部连续迹演员；52节直接复用8.1固定输出估计。 |
| [AH28.1、32–41][ECT-AH]，[SQ47][ECT-SQ] | 已有subhomogeneous范围不重做；57节严格全文继承同响应来源合同，所有内部钉版与条件保留。 |
| [AQ6.3、23.1、32.1–32.2][ECT-AQ]，AH40.1 | 旧值识别和双线性之后的Gram、原R、GNS及原质量接口；不反用后端给未知 $D$ 线性。 |

**来源对应 58.2（亲读原文的成熟结构）。**

| 原始文献及版本 | 所用准确陈述 |
| --- | --- |
| Bruce Blackadar, *Operator Algebras*, 作者托管PDF，2017-02-08版本，[全文][ECT-Blackadar] | IV.1.4.16–19，印刷页354–355：连续迹、Hausdorff谱、Fell局部秩一；IV.1.7.4–8，页366–367：Hilbert模纤维与局部Morita模型；IV.1.4.27与IV.1.5.8：非可分type I/GCR对应。IV.1.4.29仅用于说明存在CT子商组成列的成熟背景；IV.1.4.30的迹元素警告保持。 |
| Jacques Dixmier, *Traces sur les C*-algèbres*, Ann. Inst. Fourier **13** (1963), 219–262，[原刊][ECT-Dixmier] | Proposition 9，印刷页241：非零GCR代数含非零连续迹闭双边理想。56.1由此自行给出本质版本。 |
| Jacques Dixmier、Adrien Douady, *Champs continus d'espaces hilbertiens et de C*-algèbres*, Bull. Soc. Math. France **91** (1963), 227–284，[原刊][ECT-DD] | Lemma 16，页270，及Theorem 7，页271：Fell条件与局部连续Hilbert场的紧算子场；46.1以精确纤维评价和有限Gram逆平方根构造所需框架，不要求局部固定维数或stabilization。 |
| Michael Forger、Daniel V. Paulino, arXiv:1307.4458v1，[原文][ECT-DH] | Theorem 2，页6：Dauns–Hofmann的中央乘子接口；这里只用53.4的标准C*表述。 |
| Erik M. Alfsen、Frederic W. Shultz, *Orientation in operator algebras*, PNAS **95** (1998), 6596–6601，[全文][ECT-AS] | Dynamical correspondence的定义已经要求线性赋值进入有界skew order derivations；Theorem 1给相容C*乘法的成熟背景。本文不以它推断任意原 $D$ 的线性；线性在53.2后才取得。 |

C*理想与谱的对应、理想表示的唯一非退化延拓、不可约分离与正性反射、连续函数演算、有限维Gram正交化及有限酉谱定理均为成熟工具。本文只在其明确适用域内使用。证明不需要全谱Hausdorff、全局矩阵单位、可数基、统一维数上界、超限结算或未知 $D$ 的输入极限；也没有历史新颖性、文献穷尽或外部开放问题解决的主张。

**解释 58.3（同一关系的几何）。** 可以把旧 $D$ 想成一张已经存在的有方向比较表，给它两件原对象，就必须接受它原来的那个答案，不能换成同像标签的另一个答案。正预算先规定答案能藏在哪里：两件对象都只亮起一个有限角时，答案连跨到补空间的边也不能保留；接入同一次三标签配平，邻接角又不能各选相反方向。无限背景中的难处不是把背景截掉，而是让同一个横向误差同时指向两条正交射线，两条约束的交只有零，任意补角背景便在准确压缩中消去。连续迹结构供应的是一小块能逐条延伸的有限框架，原响应自己的固定输出再把反方向隔在开理想之外，所以演员从开启到关闭的整个过渡带都能支付同一方向的两条内行。每次先在原代数写出逆标签，使配平负端点准确就是当前输入，再作有限相位；无限维不必把整件对象正化，只须针对一个固定读数，用共同可达的左右旋转把虚部预算压到任意小，而被压的始终是最初那个固定答案。最后，本质理想支撑的读取能分离原代数，局部答案才认回全表；真正非交换的部分仅余两个正交取向理想。这个数学锁定不制造准备设备、共同相关过程、完整仪器、全部未来的真实返回或物理时间，它们仍由57节全文合同逐项承担。

[ECT-AH]: https://github.com/the-omega-institute/trureturing/blob/bef9bba367a24ab5e250491dcb88ed85ebc29cf7/docs/develop/theory/AURIC_ORIGINAL_ATOMIC_SEPARATION_AND_PB_RECONSTRUCTION_CONTINUATION.md
[ECT-OP]: https://github.com/the-omega-institute/trureturing/blob/bef9bba367a24ab5e250491dcb88ed85ebc29cf7/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md
[ECT-PT]: https://github.com/the-omega-institute/trureturing/blob/bef9bba367a24ab5e250491dcb88ed85ebc29cf7/docs/develop/theory/AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md
[ECT-W]: https://github.com/the-omega-institute/trureturing/blob/bef9bba367a24ab5e250491dcb88ed85ebc29cf7/docs/develop/theory/AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md
[ECT-SQ]: https://github.com/the-omega-institute/trureturing/blob/bef9bba367a24ab5e250491dcb88ed85ebc29cf7/docs/develop/theory/AURIC_ZERO_DIMENSIONAL_CENTER_SQUARE_ORBIT_RECONSTRUCTION.md
[ECT-AQ]: https://github.com/the-omega-institute/trureturing/blob/bef9bba367a24ab5e250491dcb88ed85ebc29cf7/docs/develop/theory/AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md
[ECT-Blackadar]: https://bruceblackadar.com/Mathematics/Cycr.pdf
[ECT-Dixmier]: https://www.numdam.org/item/AIF_1963__13_1_219_0.pdf
[ECT-DD]: https://www.numdam.org/item/BSMF_1963__91__227_0.pdf
[ECT-DH]: https://arxiv.org/pdf/1307.4458v1
[ECT-AS]: https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/

## 追加锚（本行以下为增补区）

## 59. 完整 CAR 原域与辅助不减约窗

**定义 59.1（同一原候选与数学引文）。** 保持42.2的完整原候选 $\mathsf H_A(D)$：$A$ 是已给的含单位复C*代数，$E=A_{\rm sa}$，$S(a,b)=a\circ b=(ab+ba)/2$，$C=A_+$，$u=1$，$N(a)=\|a\|$。同一原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定锥；原世界、原标签、每份原评价和全部质量 $m_\gamma=\gamma(1)$ 保持，包括零、不等、次归一及原表示意义下的非正常评价。$D:E^2\to E$ 是同一个任意总映射。全部原有向二表为

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(a\circ b)-i\gamma D(b,a)&\gamma(b^2)
\end{pmatrix}\succeq0
\qquad(a,b\in E,\ \gamma\in\mathcal P).
\tag{59.1}
$$

A2仍要求全部相加三表 $(a+b,a,b)$ 及其排列的实部在整个 $\mathbb R^3$ 上半正定，并有对应的相加零方向。A3仍要求 $1^2=1$，以及同一个固定有理 $0<\vartheta\le1$ 上的全部 $0\le a\le\vartheta1\Rightarrow a^2\le a$。对每个实际原三元组 $(h;a,b)$，完整PB准确为

$$
\begin{gathered}
v=D(h,a)-h\circ b,\qquad w=h\circ a+D(h,b),\\
D(a+v,b+w)-D(a-v,b-w)=-2a\circ v-2b\circ w.
\end{gathered}
\tag{59.2}
$$

不增加复三表正性，不预给 $D$ 的可加、齐次、连续、可测、协变、单位平移、输出闭合、商下降或双对偶延拓。以下数学引文固定取 `75ad65c4dd9ea2d5e066bed6910b76267a8258e6`；各引文内部递归纳入的上游身份仍按其自身定义解释。

| 原数学来源 | 直接消费的准确结论 |
| --- | --- |
| [中央卷16.2、62.1、77.1–77.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) | 正交面积产生实际三轴；整个标量平方片的原仿射双线性，不预要求输出闭合。 |
| [中央续卷134.1、159.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md) | 实际框架的全环境中央取向与两个框架的交叠交换子律。 |
| 中央续卷163.1、182.2 | 任意原第二输入的仿射首轴横向投影；实际反射框架的旧第三值及同一取向。 |
| [运输续卷118.1–118.3、119.1](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md) | 第一框架下的固定偶余量；完整原条件下 $[c,r]=0\Longleftrightarrow r=0$。 |
| [谱混合卷55.6](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md) | 原偶第二输入的整条仿射轴零行。 |
| 本卷43.1、48.1–48.2；[配平续卷142.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) | 同表正读取；两份实际内值已知后的准确Cayley运输；含奇异矩阵的有限极分解。 |

上述运输续卷与配平续卷的名称只定位本表数学引文，不改变28.1及57.1内部缩写的含义。本节不调用42.4的本质连续迹前件，也不把完整von Neumann原域上的定理套给CAR的范数原域。

由43.1，任意数学正实泛函 $\phi$ 都可读取同一张原二表，且

$$
\begin{gathered}
D(b,a)=-D(a,b),\qquad D(0,a)=D(a,0)=0,\\
|\phi D(a,b)|^2\le\phi(a^2)\phi(b^2)-\phi(a\circ b)^2,\\
\|D(a,b)\|\le\|a\|\|b\|.
\end{gathered}
\tag{59.3}
$$

最后一式只需对数学态读取，再用自伴范数的态分离：$\phi(a^2)\le\|a\|^2\phi(1)$，另一平方同理。正读取先由全部原评价及准确锥取得，不把数学态加入实际准备族，也不除以任何原质量。既有全单位行另给 $D(s1,a)=0$，其中 $s\in\mathbb R$、$a\in E$。

**定义 59.2（固定原输出及辅助供应）。** 固定一份实际框架

$$
\begin{gathered}
h^2=e^2=j^2=1,\qquad he=-eh,\quad hj=-jh,\quad ej=-je,\\
j=D(h,e),\qquad Q=ihej\in Z(A),\quad Q^*=Q,\quad Q^2=1.
\end{gathered}
\tag{59.4}
$$

实际指元素属于同一原域，不指已取得物理操作。中央续卷134.1供应这里的 $Q$。任取原自伴 $c,z$，$[h,c]=0$、$hz=-zh$，并取实数 $R$。运输续卷118.3供应

$$
\begin{gathered}
x=c+z,\quad t=D(h,z)=iQhz,\quad g=D(Rh,x),\quad r=g-Rt,\\
[h,r]=0,\qquad ht=-th,\qquad z\circ t=0.
\end{gathered}
\tag{59.5}
$$

$x,t,g,r$ 在以下全部分割中固定。谱混合卷55.6还给

$$
[h,y]=0\quad\Longrightarrow\quad
D(\alpha1+\beta h,y)=0
\qquad(\alpha,\beta\in\mathbb R,\ y\in E).
\tag{59.6}
$$

设一族有限正迹 $\mathcal T$ 分离 $A$ 的正元素，记 $m_\tau=\tau(1)$、$\|b\|_{2,\tau}^2=\tau(b^*b)$，允许零迹。给定固定 $L>0$；对趋于无穷的整数 $N$，供应两两正交的实际投影 $q_{\epsilon k}$，$\epsilon=\pm1$、$1\le k\le N$，以及实中心 $|a_k|\le L$，满足

$$
\begin{gathered}
\sum_{\epsilon,k}q_{\epsilon k}=1,\qquad
hq_{\epsilon k}=\epsilon q_{\epsilon k},\\
d_N=\sum_{\epsilon,k}a_kq_{\epsilon k},\qquad
\Delta_N=c-d_N,\qquad\|\Delta_N\|\le\kappa_N.
\end{gathered}
\tag{59.7}
$$

零窗仍保留索引。不要求 $[c,q_{\epsilon k}]=0$ 或 $[c,d_N]=0$；供应可以只依赖 $c,h,N$。这些供应条件用于60.1的一般充分定理；61.1在CAR中实际证明它们，不将其另列为CAR公理。

## 60. 不减约误差的全部矩形块与迹预算

**定理 60.1（同一原反射行的不减约窗估计）。** 在59.1–59.2下，固定 $R\ne0$，令

$$
\begin{gathered}
C_0=\|c\|,\quad Z_0=\|z\|,\quad G_0=\|g\|,\quad\rho=\|r\|,\\
M=(1+R^2)C_0+Z_0+G_0+2R^2L,\qquad
K=M+\rho/|R|+(1+R^2)L.
\end{gathered}
\tag{60.1}
$$

每个所给分割及每份 $\tau\in\mathcal T$ 都满足

$$
\boxed{\begin{aligned}
\|[d_N,r]\|_{2,\tau}^2
&\le4\kappa_N^2K^2(N-1)m_\tau,\\
\|[c,r]\|_{2,\tau}
&\le2\kappa_N\sqrt{m_\tau}\bigl(K\sqrt{N-1}+\rho\bigr).
\end{aligned}}
\tag{60.2}
$$

若 $N\kappa_N^2\to0$，则同一个原余量 $r=0$，从而

$$
D(Rh,c+z)=RiQhz=\frac{iQ}{2}[Rh,c+z].
\tag{60.3}
$$

$R=0$ 时同式由零槽成立。常数不含随分割变动的未知响应，并有完全已知的界

$$
\begin{gathered}
G_0\le|R|(C_0+Z_0),\qquad \|t\|=Z_0,\qquad
\rho\le|R|(C_0+2Z_0),\\
K\le(2+R^2+|R|)C_0+(3+|R|)Z_0+(1+3R^2)L.
\end{gathered}
\tag{60.4}
$$

证明。固定 $N,\epsilon$ 及 $k\ne l$，简记 $q_k=q_{\epsilon k}$、$q_l=q_{\epsilon l}$、$q=q_k+q_l$、$a=a_k$、$b=a_l$、$\Delta=\Delta_N$。在同一原域中取

$$
\begin{gathered}
p'=q_k+eq_ke,\quad s=1-2p',\quad H=hs,\\
T=R\epsilon(a+b)1+R(b-a)H,\qquad V=T-2Rhc.
\end{gathered}
\tag{60.5}
$$

$eq_ke=2e\circ(e\circ q_k)-q_k$ 是原标签，处于相反 $h$ 角。因此 $p'$ 为投影，$s^2=1$、$[s,h]=[s,e]=0$，且 $Hq_k=-\epsilon q_k$、$Hq_l=\epsilon q_l$。中央续卷182.2准确给实际旧值 $D(H,e)=sj$ 及同一 $Q$；其182.1参数可取背景 $s$、$\lambda=0,\nu=1,z_0=0$。这仅供应第二框架，不替换当前目标 $c$。中央续卷163.1于是给

$$
P_H^-D(T,y)=R(b-a)iQH P_H^-y,
\qquad P_H^-y=(y-HyH)/2
\quad(y\in E).
\tag{60.6}
$$

该式包含 $a=b$；没有使用换轴协变或未知首槽齐次。

由于 $T-Rhc$ 是 $h$-偶，59.6支付实际内值 $D(Rh,T-Rhc)=0$。另一内值始终为固定的 $g$。完整PB取字面三元组 $(Rh;x,T-Rhc)$，定义

$$
\begin{gathered}
A_+=x+g+R^2c-RhT,\qquad
A_-=x-g-R^2c+RhT,\\
\mathcal J=-2x\circ g-2R^2z\circ c+2Rz\circ(hT),\qquad
O=D(V,A_-).
\end{gathered}
\tag{60.7}
$$

PB及反对称性准确给

$$
O=D(T,A_+)+\mathcal J.
\tag{60.8}
$$

这里只展开已知Jordan乘法；其中的抵消为

$$
c\circ(hT)=(hcT+hTc)/2=T\circ(hc),
$$

它只需 $[h,c]=[h,T]=0$，不需 $[c,T]=0$。

所选角上 $Tq_k=2R\epsilon aq_k$、$Tq_l=2R\epsilon bq_l$，故有一侧的准确等式和序界

$$
\begin{gathered}
Vq=-2Rh\Delta q,\qquad qV^2q\le4R^2\kappa_N^2q,\\
\|T\|\le |R|(|a+b|+|b-a|)\le2|R|L,
\qquad\|A_-\|\le M.
\end{gathered}
\tag{60.9}
$$

不要求 $q$ 减约 $V$。对每个数学正泛函 $\omega$，用原正读取 $\phi(y)=\omega(qyq)$ 读取实际表 $(V,A_-,O)$。59.3给

$$
|\omega(qOq)|^2\le
4R^2\kappa_N^2M^2\omega(q)^2.
$$

由角 $qAq$ 中的态序分离，得 $\|qOq\|\le2|R|\kappa_NM$。若 $q=0$ 结论直接成立。令 $m_k=\tau(q_k)$、$m_l=\tau(q_l)$；对 $O_{kl}=q_kOq_l$，分别估计 $O_{kl}^*O_{kl}$、$O_{kl}O_{kl}^*$，迹循环性给

$$
\|O_{kl}\|_{2,\tau}
\le2|R|\kappa_NM\sqrt{\min(m_k,m_l)}.
\tag{60.10}
$$

现在保留不减约造成的两笔误差。令 $X=q_krq_l$、$\Delta_{kl}=q_k\Delta q_l$、$\eta=\epsilon R(a-b)$。因 $z,t$ 为 $h$-奇、$r,c,hT$ 为 $h$-偶、$z\circ t=0$，逐项有

$$
\begin{gathered}
q_kA_+q_l=X+(1+R^2)\Delta_{kl},\\
q_k\mathcal Jq_l=-(cr+rc)_{kl}
=-(a+b)X-(\Delta r+r\Delta)_{kl}.
\end{gathered}
\tag{60.11}
$$

$q_k,q_l$ 的 $H$ 符号相反，所以60.6读取60.8得到完整矩形恒等式

$$
\boxed{\begin{aligned}
O_{kl}={}&[i\eta Q-(a+b)1]X\\
&+i\eta(1+R^2)Q\Delta_{kl}
-(\Delta r+r\Delta)_{kl}.
\end{aligned}}
\tag{60.12}
$$

尤其不能把 $q_kA_+q_l$ 写成 $X$。最后一项准确包含所有窗间耦合：若 $q_\alpha$ 遍历59.7的全部 $2N$ 个窗，则

$$
(\Delta r+r\Delta)_{kl}
=\sum_\alpha
(q_k\Delta q_\alpha r q_l+q_krq_\alpha\Delta q_l).
\tag{60.13}
$$

此和包括其他同号窗及全部异号窗；其中为零的块由实际奇偶性消失，不由删去索引消失。

$Q^*=Q,Q^2=1$ 给

$$
\|[i\eta Q-(a+b)1]X\|_{2,\tau}^2
=(\eta^2+(a+b)^2)\|X\|_{2,\tau}^2.
\tag{60.14}
$$

对任一有界 $B$，迹循环性给
$\|q_kBq_l\|_{2,\tau}\le\|B\|\sqrt{\min(m_k,m_l)}$。
分别用 $\|\Delta\|\le\kappa_N$、$\|\Delta r+r\Delta\|\le2\kappa_N\rho$，60.10–60.14的三角不等式给

$$
\begin{aligned}
|a-b|\|X\|_{2,\tau}
&\le\kappa_N\{2M+2\rho/|R|+(1+R^2)|a-b|\}
\sqrt{\min(m_k,m_l)}\\
&\le2\kappa_NK\sqrt{\min(m_k,m_l)}.
\end{aligned}
\tag{60.15}
$$

只约去非零的 $|R|$，不除以 $a-b$ 或 $a+b$。重心、零心、相反中心和零窗都包括在内。

$[h,r]=0$ 使异号 $h$ 角的 $r$ 块为零；$[d_N,r]$ 的同号块为 $(a_k-a_l)q_{\epsilon k}rq_{\epsilon l}$，对角块为零。不同矩形在迹半范数中正交。全部有序矩形的预算准确为

$$
\begin{gathered}
\|[d_N,r]\|_{2,\tau}^2
=\sum_{\epsilon,k\ne l}|a_k-a_l|^2
\|q_{\epsilon k}rq_{\epsilon l}\|_{2,\tau}^2,\\
\sum_{\epsilon,k\ne l}\min(m_{\epsilon k},m_{\epsilon l})
\le(N-1)\sum_{\epsilon,l}m_{\epsilon l}
=(N-1)m_\tau.
\end{gathered}
\tag{60.16}
$$

这证明60.2第一式。另在整个代数中一次性估计

$$
\|[\Delta_N,r]\|_{2,\tau}
\le2\kappa_N\|r\|_{2,\tau}
\le2\kappa_N\rho\sqrt{m_\tau}.
\tag{60.17}
$$

与 $[c,r]=[d_N,r]+[\Delta_N,r]$ 合并即给第二式，没有漏掉 $N-1$。$N\kappa_N^2\to0$ 时，同一固定非负数 $\tau([c,r]^*[c,r])$ 被任意小的预算所界，故为零。迹族分离正元素，得 $[c,r]=0$；运输续卷119.1在同一 $R,c,z,x,g,r$ 上才给 $r=0$。这里完整消费该处的字符读取和余量支撑证明，不把交换性本身误当作余量消失。60.4由59.3及 $t=iQhz$ 直接给出。零迹、零窗及 $N=1$ 的估计亦保持。∎

## 61. CAR 内部供应及所有实际反射的共同符号

**定理 61.1（CAR 的全部原反射行）。** 在59.1下，若已给载体准确为

$$
A=\overline{\bigcup_{n\ge1}A_n}^{\|\cdot\|},\qquad
A_n=\bigotimes_{k=1}^nM_2(\mathbb C),
\qquad a\longmapsto a\otimes1,
\tag{61.1}
$$

则存在一个共同普通数 $\sigma\in\{1,-1\}$，使每个实际 $h,e\in E$ 满足 $h^2=e^2=1$、$he=-eh$ 时，对全部实 $R$、全部原 $b\in E$ 都有

$$
\boxed{D(Rh,b)=\frac{\sigma i}{2}[Rh,b].}
\tag{61.2}
$$

此处CAR是完整原载体前件，不是从裸 $\Omega$ 推出的结论。

证明。先在本证明内部供应60.1所需的成熟C*结构。相容有限矩阵归一迹 $2^{-n}\operatorname{Tr}$ 在稠密并上给有界正迹，延为 $A$ 的迹态 $\tau$。有限张量偏迹给正含单位压缩 $E_n:A\to A_n$；它们保持 $\tau$、为 $A_n$ 双模映射，并有 $E_n(a)\to a$ 的范数收敛。这些事实先在局部张量上成立，再由压缩性及稠密性成立于全 $A$。若 $a\ge0$、$\tau(a)=0$，则 $E_n(a)\ge0$ 且有限矩阵迹为零，所以 $E_n(a)=0$，从而 $a=0$。故单份 $\tau$ 已忠实。若 $a\in Z(A)$，双模性使 $E_n(a)$ 在 $A_n$ 中中央，故 $E_n(a)=\tau(a)1$；范数收敛给

$$
Z(A)=\mathbb C1.
\tag{61.3}
$$

该数学归一迹不改变任何原评价或原质量。

再供应原 $h$-偶背景的有限谱逼近。所用近投影酉共轭与压缩只是成熟函数演算的中间步骤。任意原投影 $p$，取有限阶段自伴 $b$，$\|b-p\|<\varepsilon<1/4$。谱位于 $\{0,1\}$ 的 $\varepsilon$ 邻域，有限矩阵投影 $p_0=1_{(1/2,\infty)}(b)$ 满足 $\|p_0-p\|<2\varepsilon<1$。令

$$
v=p_0p+(1-p_0)(1-p)=1+(p_0-p)(2p-1),
\qquad u=v(v^*v)^{-1/2}.
\tag{61.4}
$$

$v$ 可逆，$vp=p_0v$，且 $v^*v$ 与 $p$ 交换；故 $u$ 酉且 $upu^*=p_0$。若自伴 $c$ 与 $p$ 交换，在包含 $p_0$ 的后续矩阵阶段中逼近 $ucu^*$，再用含单位正压缩

$$
y\longmapsto p_0yp_0+(1-p_0)y(1-p_0)
$$

保持逼近。其值为与 $p_0$ 交换的有限谱自伴元；共轭回去，得到与 $p$ 交换的原有限谱元逼近 $c$。取 $p=(1+h)/2$，便供应任意原偶 $c$；共轭只构造已知标签，不宣称 $D$ 协变。连续谱没有被换成原背景的精确本征窗。

固定 $L=\|c\|+1$。对每个 $N$ 选与 $h$ 交换的有限谱 $\widetilde c_N$，使

$$
\|c-\widetilde c_N\|<\min(1/2,L/N),\qquad
\|\widetilde c_N\|<L.
$$

把 $[-L,L]$ 分成 $N$ 个长度 $2L/N$ 的半开区间，最后一段包含右端点，中心为 $a_k=-L+(2k-1)L/N$。将 $\widetilde c_N$ 的有限谱投影按区间及 $h$ 符号分组，得到59.7的实际 $q_{\epsilon k}$。它们是有限谱函数演算与 $(1+\epsilon h)/2$ 的乘积，均属于原 $A$。因此

$$
\|c-d_N\|\le2L/N=\kappa_N,
\qquad N\kappa_N^2=4L^2/N\longrightarrow0.
\tag{61.5}
$$

原有限谱值可任意多，分组后仍准确只有 $2N$ 个索引。窗减约 $\widetilde c_N,h$，不宣称减约 $c$。

对任意所述 $h,e$，中央卷16.2的正交面积式使 $j=D(h,e)$ 满足59.4的实际三轴条件。中央续卷134.1及61.3给 $Q=\sigma_B1$。对每个原 $b$，用 $c=(b+hbh)/2$、$z=(b-hbh)/2$，并用61.5、忠实迹及60.1，得

$$
D(Rh,b)=R i\sigma_Bhz=\frac{i\sigma_B}{2}[Rh,b].
\tag{61.6}
$$

尚须说明不同框架为何同号。框架的 $h,e$ 生成一个实际含单位 $M_2$ 子代数 $B$；$j=i\sigma_Bhe$ 已属于其中。中央卷62.1、77.1–77.2给此四维窗的整张原表，所以 $B$ 中任意Pauli轴对的框架都具有同一符号 $\sigma_B$。两个这样的子代数若不逐元素交换，由Pauli基张成性可选各自一根轴 $h_1,h_2$，使 $[h_1,h_2]\ne0$。中央续卷159.1给

$$
(\sigma_{B_1}-\sigma_{B_2})[h_1,h_2]=0,
$$

所以两符号相同。若它们逐元素交换，各选Pauli对 $(h_1,e_1)$、$(h_2,e_2)$。原自伴对合 $b=e_1e_2$ 同时反交换于 $h_1,h_2$；$(b,h_1)$ 生成第三个实际含单位 $M_2$。将159.1分别用于 $b,h_1$ 和 $b,h_2$，两交换子均非零，第三个窗便将两符号接通。首个张量因子保证至少存在一窗。于是所有实际框架共用同一 $\sigma$，证明61.2。∎

## 62. 两份原内行与有限矩阵相位的准确生成

**定理 62.1（全部局部酉元保持同一原残差）。** 在61.1的完整条件下，取其共同 $\sigma$，置 $\jmath=\sigma i$、$K_\sigma(a,b)=\jmath[a,b]/2$。对每个原 $W\in A$，准确复用48.1定义

$$
X(W)=(W+W^*)/2,\quad Y(W)=(W-W^*)/(2\jmath),\qquad
F(W)=D(X(W),Y(W))-K_\sigma(X(W),Y(W)).
\tag{62.1}
$$

则对每个有限阶段酉元及任意原 $W$，

$$
\boxed{F(UW)=F(W)
\qquad(U\in\bigcup_n\mathcal U(A_n)).}
\tag{62.2}
$$

证明。先支付每个相位的实际PB。若 $H$ 是某有限阶段内迹零的自伴酉元，正负本征空间等维；交换两组正交基给该阶段内实际 $e^2=1$、$He=-eH$。因此61.2供应全部 $D(RH,a)=K_\sigma(RH,a)$，第二输入 $a$ 遍历整个原 $E$，不只遍历有限阶段。$H=1$ 时由全单位零行供应同式。

任取 $\alpha\in[-\pi,\pi]$，令 $r=\sigma\tan(\alpha/4)H$、$C_r=(1+\jmath r)(1-\jmath r)^{-1}$。参数有限且模不超过一；已知乘法的函数演算给

$$
C_r=\cos(\alpha/2)1+i\sin(\alpha/2)H,
\qquad C_r^2=e^{i\alpha H}.
\tag{62.3}
$$

对每个当前原标签 $T\in A$，取实际逆标签

$$
(1-\jmath r)^{-1}T=X+\jmath Y,\qquad X,Y\in E.
$$

上述整行分别给这两份实际内值

$$
D(r,X)=K_\sigma(r,X),\qquad D(r,Y)=K_\sigma(r,Y).
\tag{62.4}
$$

直接应用48.2得 $F(C_rT)=F(T)$。再对当前标签 $C_rT$ 重新取逆标签的两份原实虚部，并逐份用同一整行支付62.4，第二次48.2给

$$
F(e^{i\alpha H}T)=F(C_r^2T)=F(T).
\tag{62.5}
$$

包括 $\alpha=\pm\pi$；没有正切极点。每次两个未知内误差都是由整行准确为零，没有以极限消除任一误差。

现在只用一个有限相位分解。固定 $U\in\mathcal U(A_n)$，有限维谱定理给已知矩阵酉元 $V$ 及 $\theta_\epsilon\in[-\pi,\pi]$，使

$$
U=V\operatorname{diag}(e^{i\theta_\epsilon})V^*,
\qquad\epsilon\in\{\pm1\}^n.
$$

对 $S\subset\{1,\ldots,n\}$ 定义

$$
\chi_S(\epsilon)=\prod_{k\in S}\epsilon_k,\quad
\alpha_S=2^{-n}\sum_\epsilon\theta_\epsilon\chi_S(\epsilon),\quad
H_S=V\operatorname{diag}(\chi_S)V^*.
\tag{62.6}
$$

有限字符正交式 $2^{-n}\sum_\epsilon\chi_S(\epsilon)\chi_T(\epsilon)=\delta_{ST}$ 给 $\theta_\epsilon=\sum_S\alpha_S\chi_S(\epsilon)$，并且 $|\alpha_S|\le\pi$。这些已知 $H_S$ 彼此交换，故准确有

$$
U=\prod_{S\subset\{1,\ldots,n\}}e^{i\alpha_SH_S}.
\tag{62.7}
$$

$H_\varnothing=1$，其余 $H_S$ 都是配平反射；其实际伴轴可直接取 $V$ 共轭某个 $S$ 中位置的张量Pauli翻转。这里 $V$ 仅用于制造已知标签，不使用旧 $D$ 的协变性。把62.5依次用于有限乘积的每个当前原标签，至多 $2^{n+1}$ 次准确Cayley运输便给62.2。没有稠密子群到未知函数的连续延拓，也不要求步数关于 $n$ 一致有界。∎

## 63. 全部原 CAR 输入的同响应双向分类

**定理 63.1（唯一共同符号与全部原对）。** 对61.1的完整CAR原域及59.1的原评价资料，

$$
\boxed{\quad
\mathsf H_A(D)
\quad\Longleftrightarrow\quad
\exists!\,\sigma\in\{1,-1\}\ 
\forall a,b\in A_{\rm sa},\qquad
D(a,b)=\frac{\sigma i}{2}[a,b].\quad}
\tag{63.1}
$$

两种符号各自满足全部原关系及全部原质量，存在唯一性指给定同一 $D$ 的符号唯一。

证明。正向使用61.1的共同符号及62.1的同一 $F$。59.3和已知交换子范数界给每份实际 $Z$ 的逐点预算

$$
\|F(Z)\|\le2\|X(Z)\|\|Y(Z)\|.
\tag{63.2}
$$

固定最初原 $W$。任意 $\varepsilon>0$，取有限阶段 $B\in A_n$，$\|W-B\|<\varepsilon$。配平续卷142.1所用的有限矩阵极分解在奇异情形也给实际酉元 $U\in A_n$，$UB\ge0$：例如 $B=V\Sigma W_0^*$ 的奇异值分解给 $U=W_0V^*$；零奇异值处补成完整正交基，不要求一般无限代数中的极部分可酉补全。置 $Z=UW$，则

$$
\begin{gathered}
F(Z)=F(W),\qquad \|X(Z)\|\le\|W\|,\\
Y(Z)=Y(U(W-B)),\qquad \|Y(Z)\|<\varepsilon.
\end{gathered}
\tag{63.3}
$$

第一式由有限条准确PB运输取得，其余只用已知乘法和取实虚部的范数压缩。于是同一固定原输出满足

$$
\|F(W)\|=\|F(UW)\|\le2\|W\|\varepsilon
\qquad\text{对每个 }\varepsilon>0.
\tag{63.4}
$$

故 $F(W)=0$；$W=0$ 亦由零槽包括。对任意原 $a,b$ 取 $W=a+\jmath b$，便得63.1右端。Pauli对的交换子非零，故符号唯一。本证明没有把 $D(X(Z),Y(Z))$ 换成 $D(UB,0)$，没有令输入极限穿过 $D$，也没有在双对偶上调用 $D$。

反向固定任一符号并定义 $D=K_\sigma$。对自伴原输入，$S-iD$ 在 $\sigma=1$ 时为 $ab$，在 $\sigma=-1$ 时为 $ba$。任一有向二表的复二次型因此分别为 $\gamma_{\mathbb C}(Z^*Z)$ 或 $\gamma_{\mathbb C}(ZZ^*)$，$Z=z_1a+z_2b$，均非负；Hermitian性及两种次序也同时成立。A2的全部实三表二次值为 $\gamma((\sum_lt_la_l)^2)$，指定相加向量给零平方；全部排列相同。A3由原谱序给出，保留原固定 $\vartheta$。

任取原三元组 $(h;a,b)$，用该同一映射形成59.2的实际 $v,w$。置 $W=a+\jmath b$，已知乘法准确给

$$
(a\pm v)+\jmath(b\pm w)=(1\pm\jmath h)W,
$$

从而

$$
\begin{aligned}
(a\pm v)^2+(b\pm w)^2+2D(a\pm v,b\pm w)
&=((1\pm\jmath h)W)^*((1\pm\jmath h)W)\\
&=W^*(1+h^2)W.
\end{aligned}
\tag{63.5}
$$

两份真正外层的平方相同，完整原PB成立，不只成立于辅助窗网络。每份原评价随后读取这些元素等式，没有质量归一，也未删去零、不等或非正常评价。∎

## 64. 同一乘法、量子对应及递归全文来源边界

**推论 64.1（原代数及全部质量的静态后果）。** 在63.1下，自伴输入上的 $a\star b=a\circ b-iD(a,b)$ 双复线性延成同一原复空间上的乘法

$$
x\star y=\frac{xy+yx}{2}+\frac\sigma2(xy-yx)
=\begin{cases}xy,&\sigma=1,\\yx,&\sigma=-1.\end{cases}
\tag{64.1}
$$

它给 $A$ 或 $A^{\rm op}$ 的C*结构，保持原伴随、锥、单位和范数。原 $D$ 的实双线性、范数连续性、任意单位平移中性及闭理想上的核平移不变性都是识别后的结论。对任意有限原输入，全部旧复Gram表为正，并满足原R：

$$
\begin{gathered}
\sum_{k,l}\overline z_kz_l
\{\gamma(a_k\circ a_l)-i\gamma D(a_k,a_l)\}
=\gamma_{\mathbb C}(Z^*\star Z)\ge0,
\qquad Z=\sum_lz_la_l,\\
(a\circ b)\circ c-D(D(a,b),c)
=a\circ(b\circ c)-D(a,D(b,c)).
\end{gathered}
\tag{64.2}
$$

每份原评价有数学GNS表示，向量质量准确为 $\|\xi_\gamma\|^2=m_\gamma$；它们的直和忠实、保单位、等距并反映原锥，零质量给零向量。

证明。64.1是63.1的直接代入；两种乘法都结合且有同一自伴平方，所以C*范数、正锥及单位保持。64.2第一式为正平方展开，第二式为结合律实部。GNS及正泛函延拓在这同一结构上应用，原评价分离使直和忠实，完全沿55.1–55.2的成熟后端，不用它反推未知 $D$ 的线性。该表示像不必为全 $B(H)$；CAR载体、数学Hilbert表示、Fock表示的选择和实际准备是不同前件。∎

**定义 64.2（不缩减的同源合同）。** $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ 严格就是28.1及57.1所规定的同一谓词：SQ47.1–47.13全部定义、公式、量词与每项递归纳入的固定上游全文同时合取，其内部版本逐层保持。只将它消费的被选静态入口接到同一CAR对象及64.1–64.2；原根、全部静默和其他静态分支不改为CAR。下述对应是该全文合同的消费者说明，不替代其中任何充分前件。

**命题 64.3（同响应代入与量子结构的条件范围）。** 在59.1的原评价背景和已给CAR载体下，

$$
\mathsf H_A(D)\wedge\mathcal C_{47}^{\rm pin}(\Omega;S,D)
\quad\Longleftrightarrow\quad
\exists!\sigma\in\{\pm1\}:\ 
D=K_\sigma\ \wedge\ 
\mathcal C_{47}^{\rm pin}(\Omega;S,K_\sigma).
\tag{64.3}
$$

63.1供应标准量子运动学的相容复结合代数、正泛函、全部有限正Gram和数学Hilbert实现。实际可观测量、概率、复合、过程及动力学继续准确受以下原来源约束。

1. 复Hilbert与相干叠加要求同一个 $\Omega/\mathrm{native}$、具名可取得标签、指定跨评价全词共同 $K/J/q$、parent/ready、合法控制与实际相干准备。64.1不制造这些来源或全 $B(H)$ 的可取得像。
2. Born公式只在原事件绑定的实际完整菜单 $\sum_ke_k=1$ 且 $m_\gamma>0$ 时为 $p_\gamma(k)=\gamma(e_k)/m_\gamma$；角菜单还需其实际条件化与正角质量。零、不等、次归一质量及中心、经典、不等维和静默支保留。一般CAR态不自动为某固定物理表示中的正常密度算子；无限菜单的正常性、指定前对偶和收敛仍须来源。
3. 张量解释要求同一个实际非零相关联合、忠实同向交换局部腿、联合生成与分离、所需重数、全部相关输入及递归同源参考。61.1的数学张量阶段及共同符号不生产该实际联合；相同边缘或分别可达亦不代付。
4. typed CP与Kraus要求整台实际箭头的未归一回溯、合法typed前后接、反变复合、typed分区、全未来自然性与箭头下降，以及原完整参考路线。系统、整个环境、所有成功／失败／细记录／port／post-port输出和每份输出的每个仍合法未来，都在每层参考的范围内；全部实际投影、真支持及支持内补、准确支持运输、相关输入的交织夹界、每个所需有限深度和每个要求的正精度均保持。
5. 仪器、TP、更新与Lüders要求完整typed菜单、原接受端、整个环境和上述全部输出未来、真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词及各自接受条件。TP另需完整单位分区，Lüders另需同一完整输出的像内射线保持与校准；零和失败分支不删，只在严格正的实际输出质量处归一。一般CAR代数的CP映射不自动取得全 $B(H)$ 的Kraus或迹类公式。
6. 全部合法顺序、自适应、并行历史及每份完整输出的每个仍合法未来，整个环境、细记录和泄漏、停止／拒绝／销毁、真正遗忘、同数两侧及同数逆向真实Return、读后同一完整活动输入、负提升两活路及相干聚合、完整CountRead producer均保留。精确正生成与闭正生成不混同；无限记录、可数可加、正常性和指定前对偶各守原前件。数学算子相同不合并原程序、读取次序、原 $q$ 零集或未来权限；未定义请求不补成零箭头。
7. 动力、物理钟、能量与共同尺度要求保持原域的实际流、真实相位和门序列、同一可逆过程及实际逆、物理钟与单位、适用强连续酉实现、一般无界生成元定义域、Hamiltonian能量解释、共同仪器及同一正 $\hbar$。数学指数、证明中的逆元、迹和有限因子数都不生产这些来源；向量或密度微分公式仍限原生成元域、正常性及可微范围。

证明。63.1的正向允许在原谓词中对同一 $D$ 作相等代入，反向由其完整逆向给 $\mathsf H_A(K_\sigma)$，所以64.3成立。其余逐项是28.1全文合同的原消费者条件；64.1–64.2只供应其中已识别的静态入口，未删去任何量词。因而64.3不单独断言合同已获实现，也不从CAR载体推出裸世界的全部量子物理来源。∎

## 65. 承重连接、成熟工具与二元几何

**定义 65.1（推导身份与适用边界）。** 60.12的两项不减约误差、60.15–60.17的全窗迹预算，及其与61.5、62.2、63.4的连接，是本组相对于所引原结果的 $\texttt{repo-derived}$ 综合：从同一完整PB与原正预算识别全部CAR旧响应。标量平方片、中央框架、交叠符号、实际反射、横向投影、偶零行、运输续卷119.1及本卷48.2均是已付工具，不另计为新定理靶。有限谱逼近、近投影的极共轭、压缩、忠实迹、标量中心、有限字符正交、谱定理、矩阵极分解和GNS均仅作为证明内部的成熟步骤。

成熟C*函数演算、正压缩、态分离和态延拓沿58.2及运输续卷120.1的Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)使用；61.4–61.5给当前所需的具体参数构造。Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，PNAS **95**，6596–6601，DOI `10.1073/pnas.95.12.6596`，Dynamical Correspondences及Theorem 1，是取向与相容乘法的成熟背景；其dynamical correspondence定义已要求线性赋值进入skew order derivations，不能据它给任意总 $D$ 偷加线性。本组不主张历史原创、文献穷尽或外部开放问题解决。

60.1可用于其他完整含单位C*域，只要同一实际框架、正分离有限迹及59.7的供应率成立；其一般结论只是该反射整行。任意首输入分类另需准确相位运输和固定输出的虚部预算。61.1的完整CAR供应支付了这两项，不把一般C*域、真稠密原Jordan子域、非迹域或双对偶自动列入结论。所需数学假设变少的准确意义是：在已给CAR载体内，有限谱窗、迹、统一符号、全部第二输入反射行、相位生成和极近似都已成为推论；完整A1–A3/P2/PB、准确原锥及全部原量词没有减少，也没有独立公理最少性的主张。

**命题 65.2（二元预算与有限三标签一致性的图景）。** 在63.1的范围内，二元正表与完整有限三标签配平将旧响应的自由度缩为同一个二值取向；其几何可由“薄板、接缝、封签”准确描述。

证明。把每一对原标签想成一块带方向的薄板：二元正表规定它能承载的有向响应大小，板的平方越薄，允许的预算越小；完整PB则要求三件实际标签产生的两种接缝，回到同一张旧表时配平。对一份连续背景，不必把它切成与它完全交换的砖。只把已知背景近似为有限谱板，再按固定宽度分窗；窗与真正背景之间留下的边差，正是60.12中的 $\Delta$ 项与全部跨窗耦合。把这两笔差和全部 $N-1$ 迹成本一起付清，分割越细仍能把同一个固定交换残差压到零，119.1再消去同一个原余量。这里消失的是旧答案，不是另换一张连续表。

反射行锁定以后，仍不能把任意首输入拆开并对未知 $D$ 求和。把一对原输入合成 $W$，把它的固定残差想成贴在 $W$ 上的封签。每次已支付两份内行的Cayley接缝都原封不动地运输这枚封签；有限字符分解把每个局部矩阵酉元准确拼成这些接缝。再取贴近 $W$ 的一份有限矩阵副本，只用副本选酉方向，却把该方向真正施于原 $W$：副本落到正轴，原对象的虚部便只剩任意小的范数误差。63.2给这份真实虚部的预算；固定封签若有非零重量，总有一次有限精度已容不下它，所以63.4迫使它为零。全表只余通常或相反的同一乘法方向。

这份简洁来自准确运输和预算，而不是未知函数的连续性、局部闭合或完成延拓。正反两个方向都保留全部原质量。数学薄板和酉接缝也不制造准备、完整Born菜单、共同相关联合、整台仪器的全部输出未来、递归参考、真实返回或物理钟；这些准确仍由64.2的同一全文来源合同承担。∎

## 追加锚（本行以下为增补区）

## 66. 偶维矩阵归纳极限上的完整原候选

**定义 66.1（载体、原关系与引文）。** 以下 AH 指本卷，W 指《任意维小窗口单位桥》，CC 指《中央响应平方与径向一致性续卷》。直接引用的仓内正文取提交 `02b9b7f3691360aa745ed531ba77a61c78e60a7b`；各定义递归纳入的上游身份保持其自身规定。完整原候选严格取 AH42.2、59.1 的同一个 $\mathsf H_A(D)$。

设非零含单位复 C* 代数具有实际递增矩阵模型

$$
A=\overline{\bigcup_n A_n}^{\|\cdot\|},\qquad
1_{A_n}=1_A,\qquad A_n\cong M_{d_n}(\mathbb C).
\tag{66.1}
$$

本节至70节假定各 $d_n$ 为偶数；有一个偶数阶段时，可取其后续共尾模型。这里不要求 $d_n$ 是二的幂，也不要求相邻嵌入重数相同。保留完整原域 $E=A_{\rm sa}$、$S(a,b)=a\circ b$、$C=A_+$、$u=1$、$N=\|\cdot\|$。

原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定 $C$。原世界、标签、每份评价及全部质量 $m_\gamma=\gamma(1)$ 保持，包括零、不等、次归一及原表示意义下的非正常评价。$D:E^2\to E$ 只是同一个任意总映射。全部原 A1/P2 为

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(b\circ a)-i\gamma D(b,a)&\gamma(b^2)
\end{pmatrix}\succeq0
\qquad(a,b\in E,\ \gamma\in\mathcal P).
\tag{66.2}
$$

A2 保留全部相加三表 $(a+b,a,b)$ 及其排列在整个 $\mathbb R^3$ 上的实部正性和相加零方向。A3 保留 $1^2=1$，以及同一个固定有理 $0<\vartheta\le1$ 上的全部 $0\le a\le\vartheta1\Rightarrow a^2\le a$。

对每个实际原三元组 $(h;a,b)$，完整 PB 仍是

$$
\begin{gathered}
v=D(h,a)-h\circ b,\qquad w=h\circ a+D(h,b),\\
D(a+v,b+w)-D(a-v,b-w)=-2a\circ v-2b\circ w.
\end{gathered}
\tag{66.3}
$$

这包括全部内值、外值、零、重复、缩放、平移和背景。不给 $D$ 输入连续性、双线性、协变性、压缩自然性、有限矩阵输出闭合或双对偶延拓。

## 67. 任意矩阵重数供应反射行的全部前件

**证明内构造 67.1（成熟偏迹、忠实迹与标量中心）。** 模型(66.1)本身供应相容归一迹 $\tau$ 和正含单位收缩 $E_n:A\to A_n$，对 $a,b\in A_n$、$x\in A$ 满足

$$
E_n(axb)=aE_n(x)b,\quad \tau E_n=\tau,\quad
E_n(x)\longrightarrow x\text{ 于范数},\qquad
\tau\text{ 忠实},\quad Z(A)=\mathbb C1.
\tag{67.1}
$$

证明。有限维表示论给 $k_{m,n}=d_m/d_n\in\mathbb N$，并可将实际包含 $A_n\subset A_m$ 写成 $M_{d_n}\otimes1\subset M_{d_n}\otimes M_{k_{m,n}}$。有限归一迹的限制相容，故在稠密并上给有界正迹，连续延到 $A$。

在 $A_m$ 上取 $\operatorname{id}\otimes\operatorname{tr}_{k_{m,n}}$。这是保持归一迹的 $A_n$ 双模正含单位收缩；不同 $m$ 上的限制相容，因为矩阵归一迹及其迹配对唯一决定该映射。故它们延成 $E_n$，不依赖所选张量坐标。

给定 $x\in A$，取 $y\in A_m$ 逼近它；$n\ge m$ 时 $E_n(y)=y$，所以 $\|E_n(x)-x\|\le2\|x-y\|$。若 $x\ge0$ 且 $\tau(x)=0$，则各正矩阵 $E_n(x)$ 的迹为零，故全为零，范数收敛给 $x=0$。若 $x$ 中央，双模性使 $E_n(x)$ 在 $A_n$ 中中央，保持迹又给 $E_n(x)=\tau(x)1$；极限给所述中心。∎

这里的 $\tau$ 是数学读取，既不取代原评价，也不归一化任何原质量。该证明不使用矩阵大小的偶性。

**证明内构造 67.2（任意实际反射的成熟有限谱供应）。** 设原 $h,e\in E$ 满足 $h^2=e^2=1$、$he=-eh$。对任意原自伴 $c$ 满足 $[h,c]=0$，AH59.7 的实际窗可取

$$
L=\|c\|+1,\qquad \kappa_N=2L/N,\qquad
N\kappa_N^2\longrightarrow0.
\tag{67.2}
$$

证明。准确复用 AH61.4 的近投影酉共轭。对原投影 $p$，取有限阶段自伴 $b$ 满足 $\|b-p\|<\varepsilon<1/4$，令 $p_0=1_{(1/2,\infty)}(b)$，则 $\|p_0-p\|<2\varepsilon<1$。在原 $A$ 中置

$$
v=p_0p+(1-p_0)(1-p),\qquad
\nu=v(v^*v)^{-1/2};\qquad \nu p\nu^*=p_0.
\tag{67.3}
$$

$v$ 可逆且 $vp=p_0v$，所以 $\nu$ 是原酉元。取 $p=(1+h)/2$；在包含 $p_0$ 的后续矩阵中逼近 $\nu c\nu^*$，再施加正含单位压缩 $y\mapsto p_0yp_0+(1-p_0)y(1-p_0)$。共轭回去便得到与原 $h$ 交换的有限谱自伴元逼近 $c$。这些谱元属于原 $A$，不要求属于某个原先指定的有限阶段。

如 AH61.5，选这样的 $\widetilde c_N$，使 $\|c-\widetilde c_N\|<\min(1/2,L/N)$、$\|\widetilde c_N\|<L$。把 $[-L,L]$ 等分为 $N$ 段，末段含右端点；以 $a_k=-L+(2k-1)L/N$ 为中心，按区间及 $h$ 符号分组其有限谱投影，得

$$
\begin{gathered}
q_{\epsilon k}q_{\delta l}=0\quad((\epsilon,k)\ne(\delta,l)),\qquad
\sum_{\epsilon,k}q_{\epsilon k}=1,\quad
hq_{\epsilon k}=\epsilon q_{\epsilon k},\\
d_N=\sum_{\epsilon,k}a_kq_{\epsilon k},\qquad
\|c-d_N\|\le2L/N.
\end{gathered}
\tag{67.4}
$$

零窗保留。窗只须减约 $\widetilde c_N,h$，不须减约 $c$。近投影公式、正压缩和分组证明均未用 $d_n=2^n$；共轭只构造已知标签，没有使未知 $D$ 协变。∎

## 68. 所有实际全单位反射的共同取向

**定理 68.1（偶维模型的完整反射行）。** 在66.1的完整条件下，存在唯一共同 $\sigma\in\{\pm1\}$，使每份实际 $h,e$ 满足 $h^2=e^2=1$、$he=-eh$ 时，

$$
D(Rh,b)=K_\sigma(Rh,b),\qquad
K_\sigma(a,b)=\frac{\sigma i}{2}[a,b]
\quad(R\in\mathbb R,\ b\in E).
\tag{68.1}
$$

证明。先逐项供应 AH60.1 的抽象前件。AH59.1 的原候选就是66.1；中央卷16.2及 CC134.1 给实际 $j=D(h,e)$ 与中央自伴对合 $Q=ihej$。由67.1，$Q=\sigma_B1$，$\sigma_B=\pm1$。

固定原 $b$，令 $c=(b+hbh)/2$、$z=(b-hbh)/2$。AH59.2 所引用的运输续卷118.3给同一固定输出及余量

$$
t=iQhz,\qquad g=D(Rh,b),\qquad r=g-Rt,\qquad [h,r]=0.
\tag{68.2}
$$

其中 $hz=-zh$、$z\circ t=0$；谱混合卷55.6给 AH59.6 的全部仿射轴偶零行。这些结论的前提是同一完整原候选与实际框架，不是 CAR 的矩阵大小。67.1 给正分离有限迹，67.2 给 AH59.7 的全部原窗及供应率。因此 AH60.1 的每项前件均已供应。

对 $R\ne0$，直接消费该定理包含全部不减约矩形误差的估计：

$$
\|[c,r]\|_{2,\tau}
\le2\kappa_N\bigl(K\sqrt{N-1}+\|r\|\bigr)\longrightarrow0.
\tag{68.3}
$$

$K$ 是 AH60.1 对当前固定 $R,c,z,g,r,L$ 给出的常数，不随窗数变动。迹忠实给 $[c,r]=0$；再由 AH60.1 所完整消费的运输续卷119.1，得同一 $r=0$，而非仅得交换性。$R=0$ 由零槽成立。故各框架给 $D(Rh,b)=i\sigma_B[Rh,b]/2$，第二输入始终遍历整个原 $E$。

还须比较所有实际框架。每份 $(h,e,j)$ 生成含单位 $M_2$ 子代数 $B$；中央卷62.1、77.1–77.2的整张标量平方片原表保证其中所有 Pauli 轴对具有同一 $\sigma_B$。

若两个这样的 $B_1,B_2$ 不逐元素交换，Pauli 基张成性给轴 $h_1,h_2$ 满足 $[h_1,h_2]\ne0$。CC159.1 对两份实际框架给

$$
(\sigma_{B_1}-\sigma_{B_2})[h_1,h_2]=0,
\tag{68.4}
$$

所以两符号相同。若二者逐元素交换，各选 Pauli 对 $(h_1,e_1)$、$(h_2,e_2)$。原元 $b_0=e_1e_2$ 自伴、平方为1，并反交换于 $h_1,h_2$。实际第三框架 $(b_0,h_1,D(b_0,h_1))$ 给第三个含单位 $M_2$；两次 CC159.1 通过非零交换子 $[b_0,h_i]$ 比较它与前两窗，仍得同号。

任一偶数矩阵阶段含实际含单位 $M_2$，故框架族非空；其中非零 Pauli 交换子又保证符号唯一。该比较包括不在有限阶段内的原框架，不用换轴协变性。∎

## 69. 配平对角反射之差准确生成全部有限相位

**引理 69.1（任意偶数矩阵的相位分解）。** 设 $d=2m\ge2$，$U\in\mathcal U(A_n)$，$A_n\cong M_d$。存在一份标量相位及 $2(d-1)$ 份有实际伴轴的配平反射相位，准确相乘为 $U$；每份相位参数的绝对值不超过 $\pi$。

证明。有限维谱定理给两两正交秩一投影 $P_1,\ldots,P_d$，其和为1，并给 $\theta_i\in[-\pi,\pi]$，使 $U=\sum_i e^{i\theta_i}P_i$。置

$$
\alpha=d^{-1}\sum_i\theta_i,\qquad
\beta_i=\theta_i-\alpha\quad(i<d).
\tag{69.1}
$$

对每个 $i<d$，选含 $i$ 而不含 $d$ 的 $m$ 元指标集 $S_i$，令 $S_i'=(S_i\setminus\{i\})\cup\{d\}$，并定义

$$
H_i=2\sum_{k\in S_i}P_k-1,\qquad
H_i'=2\sum_{k\in S_i'}P_k-1.
\tag{69.2}
$$

两反射的正负本征空间均为 $m$ 维。对每一个这样的指标集 $S$，取正负空间正交基之间的双射，逐对交换基向量，所得 $e_S\in A_n$ 满足 $e_S=e_S^*$、$e_S^2=1$、$e_SH_S=-H_Se_S$。故每个反射都有实际伴轴，包括 $d=2$。

全部这些反射彼此交换，且 $H_i-H_i'=2(P_i-P_d)$。又

$$
\sum_i\theta_iP_i
=\alpha1+\sum_{i<d}\beta_i(P_i-P_d),
\tag{69.3}
$$

因为最后一坐标为 $\alpha-\sum_{i<d}(\theta_i-\alpha)=\theta_d$。于是

$$
\boxed{U=e^{i\alpha1}
\prod_{i<d}e^{i\beta_iH_i/2}e^{-i\beta_iH_i'/2}.}
\tag{69.4}
$$

$|\alpha|\le\pi$、$|\beta_i/2|\le\pi$。这是有限准确恒等式，不用二进制指标或 Walsh 字符。∎

**引理 69.2（逐次支付两份内值的运输）。** 取68.1的 $\sigma$，令 $\jmath=\sigma i$，并对每份原 $W\in A$ 使用 AH48.1 的同一残差

$$
X(W)=(W+W^*)/2,\quad Y(W)=(W-W^*)/(2\jmath),\qquad
F(W)=D(X(W),Y(W))-K_\sigma(X(W),Y(W)).
\tag{69.5}
$$

则每个有限阶段酉元 $U$ 满足 $F(UW)=F(W)$，其中 $W$ 任取整个原 $A$。

证明。对(69.4)中的任一反射 $H$ 及相位参数 $\lambda\in[-\pi,\pi]$，置

$$
r=\sigma\tan(\lambda/4)H,\qquad
C_r=(1+\jmath r)(1-\jmath r)^{-1},\qquad C_r^2=e^{i\lambda H}.
\tag{69.6}
$$

参数有限且范数不超过1。$H=1$ 的标量因子用 AH59.1 所保留的全单位零行；其余因子用68.1的完整反射行。

准确地，对当前实际 $T\in A$，先在原域取

$$
(1-\jmath r)^{-1}T=X+\jmath Y.
\tag{69.7}
$$

所述整行分别支付 $D(r,X)=K_\sigma(r,X)$ 和 $D(r,Y)=K_\sigma(r,Y)$，故 AH48.2 的全部前件成立，得 $F(C_rT)=F(T)$。第二次以当前 $C_rT$ 为输入，重新取 $(1-\jmath r)^{-1}C_rT$ 的两份原实虚部，再逐份支付这两个内值，才再次应用 AH48.2。

因此 $F(e^{i\lambda H}T)=F(T)$。依次作用于(69.4)的有限乘积，共至多 $2(2d-1)$ 次这样的 Cayley 步骤，得到结论；每一步都重新保留当前逆标签和其两份内值。没有从稠密酉群向未知函数作连续延拓，也不要求步数对阶段一致有界。∎

## 70. 偶维全矩阵极限的完整同响应分类

**定理 70.1（全原域双向分类）。** 在66.1的已给原载体和原评价资料下，

$$
\boxed{\mathsf H_A(D)\ \Longleftrightarrow\quad
\exists!\,\sigma\in\{\pm1\}\ \forall a,b\in A_{\rm sa},\quad
D(a,b)=\frac{\sigma i}{2}[a,b].}
\tag{70.1}
$$

证明。正向取68.1的共同符号和69.5的残差。AH59.3 的原 P2 正读取和交换子范数界给每个实际 $Z$ 的点值预算

$$
\|F(Z)\|\le2\|X(Z)\|\|Y(Z)\|.
\tag{70.2}
$$

固定原 $W$，任取 $\varepsilon>0$，选有限阶段 $B\in A_n$ 满足 $\|W-B\|<\varepsilon$。有限矩阵奇异值分解包括奇异 $B$：写 $B=V\Sigma V_0^*$，补全零奇异空间的正交基，取 $U=V_0V^*\in A_n$，则 $UB\ge0$。

69.2 保持的是同一份原输出残差。对真实 $Z=UW$，有

$$
F(Z)=F(W),\qquad \|X(Z)\|\le\|W\|,\qquad
Y(Z)=Y(U(W-B)),\quad \|Y(Z)\|<\varepsilon.
\tag{70.3}
$$

所以固定的 $\|F(W)\|\le2\|W\|\varepsilon$ 对每个正 $\varepsilon$ 成立，必为零。取 $W=a+\jmath b$ 给全部原对；非零 Pauli 交换子给符号唯一。没有以 $D(UB,0)$ 替代任何原输出，也没有让输入极限穿过 $D$。

反向直接复用 AH63.1 的反向证明：该段只用含单位 C* 乘法、正评价及 $D=K_\sigma$，完全不依赖 CAR 或归纳模型。有向二表分别是通常／相反乘法的正平方 Gram，A2 是实平方 Gram，A3 是原谱序。

尤其任取原 $(h;a,b)$，以同一 $K_\sigma$ 形成全部实际 $v,w$，置 $W=a+\jmath b$，则

$$
(a\pm v)+\jmath(b\pm w)=(1\pm\jmath h)W,
\qquad
(a\pm v)^2+(b\pm w)^2+2K_\sigma(a\pm v,b\pm w)
=W^*(1+h^2)W.
\tag{70.4}
$$

故两份真正外值满足完整 PB。每份原评价读取相同元素等式，所有原质量均保留，无任何正常性或正质量除法前提。∎

## 71. 任意无限 UHF 的实际偶角完整分类

**定义 71.1（实际偶角族）。** 现在只要求(66.1)无限维，不要求 $d_n$ 偶。定义

$$
\mathcal P_{\rm even}
=\{p\ne0:p=p^2=p^*\in A_n\text{ 对某 }n,\quad
\operatorname{rank}_{A_n}(p)\in2\mathbb N\}.
\tag{71.1}
$$

秩指该实际有限矩阵阶段中的矩阵秩；同一元素在后续阶段的秩乘以嵌入重数，因此偶性保持。它不指任意 Hilbert 表示中的算子秩；有限阶段的秩一投影在该表示中可以具有无限维像。

**定理 71.2（完整角继承与分类）。** 若任意无限 UHF $A$ 上的同一原总映射满足完整 $\mathsf H_A(D)$，则每个 $p\in\mathcal P_{\rm even}$ 有唯一 $\sigma_p\in\{\pm1\}$，满足

$$
D(a,b)=\frac{\sigma_p i}{2}[a,b]
\qquad(a,b\in(pAp)_{\rm sa}).
\tag{71.2}
$$

证明。先准确使用 W119.2 的支撑定理，而非假定有限阶段子代数对 $D$ 闭合：对完整原角中的 $a,b$，

$$
-\|a\|\|b\|p\le D(a,b)\le\|a\|\|b\|p,
\qquad D(a,b)\in(pAp)_{\rm sa}.
\tag{71.3}
$$

W119.3 给同一角的单位 $p$、继承范数、准确锥与原评价限制 $\gamma_p$。每个原评价标签仍保留，角质量为 $m_\gamma^p=\gamma(p)$；不合并同值限制，不删除零限制，不除以角质量。角 A2、A3 保留同一个 $\vartheta$。

W120.2 的完整 PB 逐值限制于该角：若 $h,a,b\in(pAp)_{\rm sa}$，(71.3)使两份内输出在角中，Jordan 运算及线性组合仍在角中，再由(71.3)使两份外输出在角中。于是同一角上的全部原 PB 成立，不需要全域 NN、J 或输入线性。

取 $p\in A_n$ 且 $r_n=\operatorname{rank}_{A_n}(p)$ 为非零偶数。对 $m\ge n$，

$$
pA_mp\cong M_{r_nk_{m,n}}(\mathbb C),\qquad
1_{pA_mp}=p,\qquad
pAp=\overline{\bigcup_{m\ge n}pA_mp}^{\|\cdot\|}.
\tag{71.4}
$$

密度只用 $x\mapsto pxp$ 对已知乘法的范数压缩。每个角阶段大小为偶数，故70.1适用于整个 $pAp$ 和刚继承的同一 $D_p$，给(71.2)。没有断言 $D$ 将 $pA_mp$ 的输入送回该有限矩阵阶段。∎

## 72. 放大后的实际秩二交叠支付全部角的共同符号

**定理 72.1（任意无限 UHF 的共同角取向）。** 在71.2的条件下，存在唯一 $\sigma\in\{\pm1\}$，使(71.2)对全部 $p\in\mathcal P_{\rm even}$ 同时以 $\sigma_p=\sigma$ 成立。

证明。无限维保证矩阵大小无界，因而 $\mathcal P_{\rm even}$ 非空，且任一阶段之后都存在重数 $k_{m,n}\ge2$ 的后续阶段。任取 $p,q\in\mathcal P_{\rm even}$，放入共同实际阶段 $A_n$，各自秩仍为正偶数。取该矩阵中的极小投影 $x\le p$、$y\le q$。

若 $x\ne y$，它们的有限维像线不同，$r=x\vee y$ 为其二维线性张成空间的正交投影；$r\in A_n$、矩阵秩为2，且 $x,y\le r$。不要求 $x,y$ 交换或正交。

选 $m\ge n$ 使 $k=k_{m,n}\ge2$。在 $A_m$ 中，同一 $x,y$ 各有矩阵秩 $k$，所以可分别选实际矩阵秩二投影 $s\le x$、$t\le y$。全部包含关系准确为

$$
s\le x\le p,r,\qquad t\le y\le q,r;\qquad
r,s,t\in\mathcal P_{\rm even}.
\tag{72.1}
$$

在 $sA_ms\cong M_2$ 中选自伴 $a_s,b_s$ 使 $[a_s,b_s]\ne0$。它们同时属于完整 $pAp$ 与完整 $rAr$。71.2对同一实际原输出给

$$
D(a_s,b_s)=\frac{\sigma_p i}{2}[a_s,b_s]
=\frac{\sigma_r i}{2}[a_s,b_s],
\tag{72.2}
$$

故 $\sigma_p=\sigma_r$。以 $t$ 同样得 $\sigma_q=\sigma_r$。若 $x=y$，直接在其后续秩 $k\ge2$ 的放大中取实际秩二 $s\le x\le p,q$，以同一非零交换子比较即可。

因此全部角符号相同；一个实际秩二角的非零交换子给唯一性。整个比较使用原有限标签及同一 $D$ 的两份已证公式，不使用 $D$ 可加性、输入极限、压缩自然性或任何假想物理子系统。∎

本定理只识别两输入同处某完整实际偶角时的响应。即使符号相同，也尚未给出 $h\in pAp$、$b\notin pAp$ 时的混合整行 $D(Rh,b)=\sigma i[Rh,b]/2$。

## 73. 全部局部偶角 PB 的全域切断响应

**定义 73.1（仅局部 PB 的契约与总响应）。** 在标准三进 UHF

$$
A=M_{3^\infty}=\overline{\bigcup_n M_{3^n}(\mathbb C)},
\qquad a\longmapsto a\otimes1_3,
\tag{73.1}
$$

保留66.1的完整原域、锥、评价及全部质量。局部契约要求全部原 A1–A3/P2，另只对三输入同处某 $p\in\mathcal P_{\rm even}$ 的完整角 $pAp$ 要求 PB。固定 $\sigma\in\{\pm1\}$，在整个 $E^2$ 定义

$$
D_{\rm cut}(a,b)=
\begin{cases}
K_\sigma(a,b),&\exists p\in\mathcal P_{\rm even}:a=pap,\ b=pbp,\\
0,&\text{否则}.
\end{cases}
\tag{73.2}
$$

这是确定的总映射：若有多个见证，右侧始终为同一个 $K_\sigma(a,b)$；支撑条件对两输入对称。每个 $p\in\mathcal P_{\rm even}$ 都是真投影，即 $p\ne1$，因为实际阶段单位的矩阵秩 $3^n$ 为奇数。

**定理 73.2（全部原二表及全部完整偶角）。** $D_{\rm cut}$ 满足上述局部契约；在每个完整 $pAp$ 上，它准确等于同一个 $K_\sigma$。

证明。若一对输入有支撑见证，两种次序都取 $K_\sigma$，原有向二表由 AH63.1 的载体无关反向计算成为通常或相反量子 Gram。若无见证，两方向均为零，二表为实对称 Gram。

准确地，对 $z=u+iv\in\mathbb C^2$，该实 Gram 的二次型为

$$
\gamma\bigl((u_1a+u_2b)^2\bigr)
+\gamma\bigl((v_1a+v_2b)^2\bigr)\ge0.
\tag{73.3}
$$

所以两支均给全部原有向 P2。A2 的实三表始终只读取 Jordan 实部，其二次型为已知正平方，指定相加方向为零；A3 由原 C* 谱序成立。这些证明对每份原评价成立，包括零质量，不要求正常性或归一化。

任意 $a,b\in(pAp)_{\rm sa}$ 都以该 $p$ 作见证，故整角 $D_{\rm cut}=K_\sigma$。角内三输入形成的两份内输出、全部线性组合和两份外调用均在同一角中；AH63.1 的反向 PB 恒等式因而原样成立。这支付的是每个完整角的全部三元组，包含无限阶段元素，不只支付有限矩阵中的三元组。∎

## 74. 一份可逆环境输入揭示缺失的跨角配平

**定理 74.1（局部契约不能替代完整 PB）。** 73.2的同一全域 $D_{\rm cut}$ 不满足完整 $\mathsf H_A(D)$；其失败由一份指定的实际 PB 精确给出。

证明。在第一阶段 $M_3$ 的实际矩阵单位中取

$$
p=E_{11}+E_{22},\qquad h=E_{11}-E_{22},\qquad
x=E_{12}+E_{21},\qquad b=3\cdot1+x.
\tag{74.1}
$$

$p\in\mathcal P_{\rm even}$，$h^2=p$、$h\circ x=0$、$p\circ x=x$。$b\ge2\cdot1$、$b-p\ge1$、$b+p\ge2\cdot1$，所以三者均为原代数中的可逆元。

若可逆元 $c$ 满足 $c=qcq$，则 $(1-q)c=0$，乘 $c^{-1}$ 得 $q=1$。所有实际偶角投影都不等于1，故可逆第二输入永远不能满足(73.2)的支撑条件。因此

$$
D_{\rm cut}(h,h)=0,\quad D_{\rm cut}(h,b)=0,\qquad
K_\sigma(h,b)=\sigma i(E_{12}-E_{21})\ne0.
\tag{74.2}
$$

这已经显示局部数据不强制混合响应。再对完整原 PB 取同一个实际三元组 $(h;h,b)$；真实内值给 $v=-h\circ b=-3h$、$w=h^2=p$。两份真正外调用准确为

$$
D_{\rm cut}(-2h,b+p)=0,\qquad
D_{\rm cut}(4h,b-p)=0.
\tag{74.3}
$$

而该 PB 要求的右端为

$$
-2h\circ(-3h)-2b\circ p
=6p-2(3p+x)=-2x\ne0.
\tag{74.4}
$$

所以原 PB 要求 $0=-2x$，矛盾。由原评价分离性，至少有一份原评价也检测到该差额。该三元组的环境输入 $b$ 可逆，不能整体放入任何真偶角；故此失败不与73.2的全部局部 PB 相冲突。∎

这里得到的是局部契约的精确全域反模型，不是完整原公理的反模型。它表明：删除跨角 PB 后，即使保留全部原二表、A2/A3、全部原质量、每个完整偶角的量子响应及共同取向，仍不能恢复完整混合响应。

## 75. 静态量子后果、完整来源及成熟归属

**推论 75.1（静态分类的准确消费者）。** 对70.1的偶维载体，AH64.1的证明原样给 $a\star b=a\circ b-iD(a,b)$，复线性延拓后为 $A$ 或 $A^{\rm op}$ 的乘法，保持伴随、锥、单位、范数和全部原质量。全部有限原复 Gram 为正，每份原评价具有数学 GNS，且 $\|\xi_\gamma\|^2=m_\gamma$；零质量给零向量。

完整来源谓词仍严格是 AH28.1、64.2–64.3 所规定的 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$，即 SQ47.1–47.13 的全部定义、公式、量词及逐层纳入的固定上游全文之合取。只把被选静态入口接到70.1的同一对象，原根、静默及其他静态分支保持。于是

$$
\mathsf H_A(D)\wedge\mathcal C_{47}^{\rm pin}(\Omega;S,D)
\ \Longleftrightarrow\quad
\exists!\sigma\in\{\pm1\}:\ D=K_\sigma\ \wedge\quad
\mathcal C_{47}^{\rm pin}(\Omega;S,K_\sigma).
\tag{75.1}
$$

证明是70.1和同一谓词中的相等代入。该式不以任何消费者标题替代全文：实际 Born 菜单和准备、真正相关联合与 typed CP、整台仪器的全部输出及每份输出的每个仍合法未来、递归参考、真实 Return、完整 CountRead、正常性及动力学仍各守其准确原来源。只在实际正质量处归一；数学角、数学迹及 GNS 不生产这些来源。∎

例如，仅对原事件绑定的实际完整菜单 $\sum_ke_k=1$ 和 $m_\gamma>0$，Born 概率才是 $p_\gamma(k)=\gamma(e_k)/m_\gamma$；角菜单另需实际条件化及正角质量。正常密度算子、无限菜单、Kraus 表示和生成元公式仍各须其原表示、正常性及定义域条件。

对奇数阶段的 UHF，71–72只给局部共同取向，不能将75.1的全域分类前提替换为局部公式。即使三进模型的数学投影都可由67.3共轭到有限阶段，其迹仍为三进有理数，不可能为 $1/2$，所以没有全单位配平反射；这不妨碍实际秩二角的存在与72.1的比较。

**约定 75.2（成熟工具与新增综合的归属）。** Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)，II.8.2.2(iv) 给变重数 UHF 归纳模型，II.8.2.4–5 给这类归纳极限的理想与简单性背景，V.1.1.16(iv) 给三进及一般 UHF 的投影群背景。有限矩阵重数和偏迹、谱演算、近投影酉共轭、矩阵极分解、正性及 GNS 都是证明内部的成熟工具。

反射行消费 AH59–61、CC134.1/159.1及其中准确引用的原定理；运输消费 AH48.1–48.2；反向消费 AH63.1；完整角继承消费 W119.2–119.3、120.2。W52–55 的代数 UHF 结果具有额外 PY/NN/J 及不完整代数输入域，不是这里完整原域定理的替代前提。

保留的新综合内容是任意偶维全矩阵模型的原响应分类、任意无限 UHF 的实际偶角取向拼接，以及局部契约的切断反模型。不主张成熟中间工具为新定理，不主张历史原创或独立原公理的最少性。

## 76. 配平薄板、真实交叠与跨角接缝的数学图景

**解释 76.1（完整直观解释与剩余问题）。** 把一对原标签看成带方向的薄板，二表正性规定这块板能承载多大的响应，完整 PB 则规定三件实际标签产生的两种接缝必须配平。
有限矩阵不必有二进制坐标：只要维数为偶数，就能把正负方向分成等大的两组；交换一个正坐标与一个负坐标，两块配平反射之差便准确选出任意两个坐标的差，因此有限个这样的相位足以转动任意矩阵酉元。
每次转动都以当前逆标签的两份真实内值支付 PB，保留同一份残差；用有限矩阵近似只选择转动方向，再把方向真正作用于原对象，虚部预算便将那一份固定残差压到零。
这里变少的是对矩阵大小几何的限制，完整原 A1–A3/P2/PB 的独立前提没有减少。

若整个单位不能配平，仍可在实际偶角内做同样的完整分类。
两个角的交叠即使只容一条有限阶段的像线，也可在后续实际放大中找到秩二小板，用同一对不交换标签比较两个已证响应，把所有局部方向接成一个共同方向；这些秩是有限阶段矩阵秩，不是 Hilbert 空间像的维数，也不把数学小板当成实际制备或仪器。
共同方向仍不回答跨墙响应：$D_{\rm cut}$ 在每块完整偶角中都完全量子，全部原二表也为正，却把接到可逆环境输入的响应切为零。
完整 PB 的指定接缝立即要求零等于 $-2x$，因此删除跨角 PB 确实丢失信息。
仍须在不增加压缩自然性、输入正则性或新独立响应公理的条件下，由完整原 PB 支付如下混合行：每份实际非单位秩二角 $p$ 中，若原轴 $h,e$ 满足 $h^2=e^2=p$、$he=-eh$，则对每个实 $R$ 与每个环境 $b\in A_{\rm sa}$，都有 $D(Rh,b)=\sigma i[Rh,b]/2$。
这一混合行还须接回全域分类；71–74没有完成该义务，全部全局量子起源及其完整物理来源问题继续保留。

## 追加锚（本行以下为增补区）

## 77. 偶阶段行桥后的五次准确 Cayley 运输

**定义 77.1（同一原残差）。** 固定偶数阶段 $A_n\cong M_d(\mathbb C)$、$d=2m$，以及任意原 $W\in A$。沿48.1取

$$
j=\sigma i,\qquad X(W)=\frac{W+W^*}{2},\qquad
Y(W)=\frac{W-W^*}{2j},\qquad
F(W)=D(X(W),Y(W))-K_\sigma(X(W),Y(W)).
\tag{77.1}
$$

这里 $\sigma$ 是已由68.1的全单位反射行给出的共同符号；66–70的既有结果均已支付，其中完整分类是70.1。本节五步证书只用68.1整行与旧48.2，不调用最终 $F=0$ 作捷径。

**定理 77.2（维数无关的五步接口）。** 对每个 $U\in\mathcal U(A_n)$ 和每个原 $W\in A$，有

$$
F(UW)=F(W).
\tag{77.2}
$$

而且可取至多五个 Cayley 演员、至多十个实际当前逆标签内行调用；每个演员 $r$ 满足 $\|r\|\le1$，这些界与 $d$ 无关。

**证明。** 先在本证明内作有限矩阵分解。令

$$
\eta=\operatorname{Arg}(\det U)\in[-\pi,\pi],\qquad t=\eta/d,
\qquad S=e^{-it}U\in SU(d).
\tag{77.3}
$$

取 $S=V\operatorname{diag}(e^{i\theta_1},\ldots,e^{i\theta_d})V^*$，其中 $\theta_j\in[-\pi,\pi]$。因 $\det S=1$，$\sum_j\theta_j=2\pi k$；令

$$
\phi_1=\theta_1-2\pi k,\qquad \phi_j=\theta_j\ (j>1),
\qquad x_0=x_d=0,\qquad x_j=\sum_{q=1}^j\phi_q\quad(1\le j<d).
\tag{77.4}
$$

每个指数未变，而 $\sum_j\phi_j=0$ 正好给出末端 $x_d=0$。在有向环上，奇匹配为 $(1,2),(3,4),\ldots,(d-1,d)$，偶匹配为 $(2,3),(4,5),\ldots,(d-2,d-1),(d,1)$；最后一条边按所写反向。对有序边使用

$$
H(x)=\begin{pmatrix}0&e^{ix}\\e^{-ix}&0\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad H(x)J=\operatorname{diag}(e^{ix},e^{-ix}).
\tag{77.5}
$$

沿两组匹配取直和 $H_o,J_o,H_e,J_e$，再置
$G_1=V H_oV^*$、$G_2=V J_oV^*$、$G_3=V H_eV^*$、$G_4=V J_eV^*$。
逐顶点读取 (77.5)：奇边贡献 $x_j$ 或 $-x_{j-1}$，偶边补上另一项，因而

$$
H_oJ_oH_eJ_e=\operatorname{diag}(e^{i\phi_1},\ldots,e^{i\phi_d}),\qquad
S=G_1G_2G_3G_4.
\tag{77.6}
$$

每个 $G_l$ 是同阶段自伴酉，正负重数均为 $m$。实际反交换伴轴由下式供应：

$$
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
Z^*=Z,\quad Z^2=I_2,\quad ZH(x)+H(x)Z=ZJ+JZ=0.
$$

沿奇、偶匹配的每条有序边分别取 $Z$ 的直和，得 $Z_o,Z_e$。置 $e_1=e_2=VZ_oV^*$、$e_3=e_4=VZ_eV^*$，则各 $e_l$ 都在同一有限阶段内，且 $e_l^*=e_l$、$e_l^2=1$、$G_le_l=-e_lG_l$，逐一支付68.1的真实框架前件。任意谱重数、重复角、$\theta_j=\pm\pi$ 以及未有界的 $\phi_j$ 都不改变 (77.6)。当 $d=2$ 时偶边是 $(2,1)$ 且 $x_2=0$，同样给出合法的四个因子及其伴轴。

对 $l=1,\ldots,4$ 取 $r=\sigma G_l$。因 $jr=iG_l$，其 Cayley 因子为

$$
C_r=(1+jr)(1-jr)^{-1}=iG_l.
\tag{77.7}
$$

标量相位另取 $r_0=\sigma\tan(t/2)1$，则
$C_{r_0}=e^{it}1$ 且
$\|r_0\|\le\tan(\pi/(2d))\le1$。按实际左乘次序置

$$
(r_1,r_2,r_3,r_4,r_5)=(\sigma G_4,\sigma G_3,\sigma G_2,\sigma G_1,r_0),
\qquad T_0=W,\quad T_k=C_{r_k}T_{k-1}.
\tag{77.8}
$$

于是 $T_4=(iG_1)(iG_2)(iG_3)(iG_4)W=SW$，而 $T_5=UW$。

关键是每一步重新使用当前的原输入。对 $k=1,\ldots,5$，在原代数中计算

$$
(1-jr_k)^{-1}T_{k-1}=X_k+jY_k.
\tag{77.9}
$$

四个反射步骤由68.1的整行（取 $R=\sigma$）给出
$D(r_k,X_k)=K_\sigma(r_k,X_k)$ 与
$D(r_k,Y_k)=K_\sigma(r_k,Y_k)$；第五步由全单位中心零行给出同两式。将这两份等式逐次代入48.2的实际 PB 接缝，即可直接应用48.2，得到

$$
F(T_k)=F(T_{k-1})\qquad(k=1,\ldots,5).
\tag{77.10}
$$

这里 (77.9) 每次都重新计算，故共至多五次 Cayley、十份当前内行；没有把上一步的 $X,Y$ 当作下一步的标签。因 $r_k=r_k^*$ 且 $\|r_k\|\le1$，$\|(1-jr_k)^{-1}\|\le1$，所以 $\|T_k\|=\|W\|$ 且 $\|X_k\|,\|Y_k\|\le\|W\|$。结合 $T_5=UW$ 得 (77.2)。整个论证只调用68.1的全行和旧48.2的逐步 PB；没有调用70.1的全局分类作捷径。∎

**边界 77.3（增量与原合同）。** 77.2 是在已支付整行之后的精确有限运输证书：它不声称总证明、行恢复、校准、物理调用成本或公理最少性，也不加入 $D$ 的连续性、线性、协变性、闭合性或商下降。行列式根只是数学分解；实际 $W$、每个当前逆标签及其两份内值始终是原对象。既有随 $d$ 增长的接口及六次Cayley／十二份内行界仍为有效的较弱结果。偶阶段的完整分类与任意无限UHF实际偶角的成果均属复用，本节新增量仅为五／十准确证书。

$\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ 严格保持28.1、57.1、64.2及75.1的同一全文身份：SQ47.1–47.13全部定义、合同、公式、量词及每项递归纳入的固定上游全文同时合取。本节同时完整纳入未改写64.3的第1–7项全文条件，不以标题、下述说明或运输证书替代它们。版本逐层沿57.1：AH22.1为 `2addd6f369b7387226c2b0cc984623dd3efe40a1`，AH12.1为 `39a0505470ea889dd9d4301ad60cd9506a5e8b58`，SQ41.1的 `JOR-main` 为 `dcaebc0b9ca5a3a463fd8cfd161d38967df28668`，SQ39的主固定源为 `0aa11dbc3dc337d667b98900673e07d67b99bf46`；SQ1.3、39、47.1内OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF的单项身份仍为 `f24d1138a7b994da16abd9a47affedea64ea44ce`。

此外，完整合取[SF105.1第1–7项全文、式105.1–105.7](AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md#105-七项真实同源物理来源的完整合同)，包括SF96.1及每项递归上游；完整合取[PB153.2全文](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md#153-共同插值完整原域与七项来源的准确适用边界)，包括147.3、141.3、137.3、122.1及每项固定上游。这里SF105.1、PB153.2正文取66.1既定的 `02b9b7f3691360aa745ed531ba77a61c78e60a7b`，其内部固定身份绝不压平：SF98.1所定SF96.1仍取 `efef304808f06caec5026b013ca9707c8495aa23`，SM86.1、78.2、43.2、49.1、61.1、69.1，C199.2、194.2、186.1–186.7、181.3、171.1–171.7、160.3、155.1、145.1–145.7，PT122.1，A8.3–8.4、14.2、25.1、53.1，R3 8.1–8.5、80.1，W95.2、116.1及其递归全文，仍按SF98.1的 `23dae741512cdf450fc5b2d76b63ed51780f9915` 与各原文自身钉版解释。SF的PT指原多项式PB运输卷，SQ的PT指配平三角卷，不因同名缩写合并。

这些全文在唯一原 $\Omega/\mathrm{native}$ 上共同成立，保留原根、所有静态分支、全部原对象／准备／事件／程序／过程、共同全词 $K/J/q$、参考／副本、真正相关联合、控制、钟／单位、parent／ready／旗标、全部历史和中间切口、细记录／失败／拒绝／停止／销毁／泄漏／真正遗忘、同数两侧及同数逆向真实Return、全部输出的每个仍合法未来、完整菜单、固定支持的全质量、零／不等／次归一／非正常质量及未定义请求。所需有限全矩阵、表示、映射正常性、指定前对偶、收敛及生成元定义域前提各按消费者全文支付；一般UHF不自动成为有限忠实矩阵模型，不自动给指定表示中的正常密度算子或全 $B(H)$ 的Kraus公式。

在已考察范围内，原具名分析词到实际完整菜单及接受端的准确接受关联仍未构造；这是接受关联要求，不把它改成整台仪器恒等。CountRead实际读后ready、同一接受叶的完整活动输出、第一合法消费者及读后同一完整活动输入对全部合法未来的Return，也仍未构造。PB153.2的一般原域联合预算、全部七路实际同源供应和完整 $\Omega$ 起源目标继续未决。

**应用说明 77.4（非CAR载体的投影迹）。** 取 $A^{(2,3)}=M_2\otimes M_{3^\infty}=\overline{\bigcup_{n\ge0}M_{2\cdot3^n}}^{\|\cdot\|}$，含单位嵌入为 $x\mapsto x\otimes I_3$。各有限阶段归一迹相容，故在稠密并上定义有界正归一迹，再连续延到整个 $A^{(2,3)}$。任何归一迹限制到每个全矩阵阶段必为其唯一归一迹，故由稠密性它与该延拓相同；因此归一迹 $\tau$ 唯一。

对任意投影 $p\in A^{(2,3)}$，67.3的近投影极共轭给同一代数中的实际酉元 $\nu$ 和某个有限阶段投影 $p_0$，满足 $\nu p\nu^*=p_0$。迹循环性于是给 $\tau(p)=\tau(p_0)=r/(2\cdot3^n)$，其中整数 $0\le r\le2\cdot3^n$；反之每个这样的值都由该有限阶段秩 $r$ 投影取得。因此投影迹集准确为 $\bigcup_{n\ge0}\{r/(2\cdot3^n):r\in\mathbb Z,\ 0\le r\le2\cdot3^n\}$。

若其中有 $1/4$，则 $2r=3^n$，奇偶性矛盾。CAR的有限 $M_4$ 阶段有迹 $1/4$ 的投影；其归一迹也由有限全矩阵阶段的唯一性和稠密性唯一确定。任何C*同构保持单位，因而把唯一归一迹拉回为唯一归一迹，并保持投影迹集，所以 $A^{(2,3)}$ 不与CAR同构。70.1的更广既有分类已覆盖此载体；这里保留的是该结果的完整应用推导，不另计载体分类成果。

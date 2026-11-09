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

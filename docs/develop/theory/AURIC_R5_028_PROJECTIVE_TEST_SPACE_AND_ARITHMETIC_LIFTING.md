# 原标签射影测试空间与算术提升

## 61. 实际二元见证的射影权重与通用协变性

**定义 61.1（固定实际域与系数、测试的区别）。** 固定特征零域 $F$、同一个可分六次域扩张 $D/F$、有限 Galois 正规闭包 $L/F$ 和原嵌入集合 $\Sigma=\operatorname{Hom}_F(D,L)$。所有窗口均为实际三维 $F$-子空间 $C\le_FD$，所有仿射标签均为原元素 $r\in D$。分裂同构 $D\otimes_FL\simeq L^\Sigma$ 只用于证明，不允许独立选择或自由置换六个标签。

沿用 [《Catalan 系数空间》定义 52.1、定理 52.2、52.4](AURIC_R5_026_CATALAN_SUPPORT_CERTIFICATES.md#52-迹对偶微分方程定义的内在系数空间) 的内在空间 $H_D$。它是原 $D$ 上满足迹对偶微分方程的齐次三次多项式空间，维数为五，且

$$
\begin{aligned}
H_D\otimes_FL
&=\left\{h\in L[x_\sigma]_3:
\deg_{x_\sigma}h\le1,\quad
\sum_{\sigma\in\Sigma}\partial_{x_\sigma}h=0\right\},\\
H_D&=\operatorname{span}_F\{P_C:C\le_FD,\ \dim_FC=3\},\qquad
P_C(x)=\det[\,B,M_xB\,].
\end{aligned}
\tag{61.1}
$$

这里 $B$ 是原窗口的六行三列包含矩阵，$M_x$ 是原域乘法矩阵；固定原基及体积形式后取行列式。换帧仅改变非零常数因子。射影空间 $\mathbb P(H_D)$ 参数化非零候选系数线，$[P_C]$ 是其中由实际窗口得到的一类点；不预设每条系数线都由窗口得到。对偶射影空间 $\mathbb P(H_D^\vee)$ 参数化非零线性测试，$H_D^\vee=\operatorname{Hom}_F(H_D,F)$。窗口、系数线、支持和测试点分别保留其含义。

**定义 61.2（射影二元权重）。** 对原射影标签 $[a:b]\in\mathbb P^1(D)$，定义

$$
W_C([a:b])=\{(u,v)\in C^2:bu=av\},\qquad
w_C([a:b])=\dim_FW_C([a:b]).
\tag{61.2}
$$

原交维函数仍为 $d_C(r)=\dim_F(C\cap rC)$，$r\in D^\times$；若延至零，严格保留 [《特征零半维窗口恢复》定义 46.1](AURIC_R5_023_CHARACTERISTIC_ZERO_HALF_WINDOW_RECOVERY.md#46-任意有限高度的实际域塔与同交维标量类倍增) 的人工约定 $d_C(0)=0$。射影权重在零点的值由见证空间决定，不改写这个约定。

**定理 61.3（原域见证传递及全部系数的协变式）。** 权重 (61.2) 与齐次代表无关，并满足

$$
w_C([r:1])=d_C(r)\quad(r\ne0),\qquad
w_C(p)=3\quad(p\in\mathbb P^1(F)).
\tag{61.3}
$$

特别地，$w_C([0:1])=w_C([1:0])=3$，而旧约定仍是 $d_C(0)=0$。任意 $g\in\operatorname{PGL}_2(F)$ 保持 $w_C$。若

$$
g=\begin{bmatrix}a&b\\c&d\end{bmatrix},\quad ad-bc\ne0,
\qquad g(r)=\frac{ar+b}{cr+d},\quad cr+d\ne0,
$$

则对每个 $Q\in H_D$ 都有

$$
N_{D/F}(cr+d)Q(g(r))=(ad-bc)^3Q(r).
\tag{61.4}
$$

证明。将 $(a,b)$ 同乘原 $D^\times$ 中的元素不改变见证方程。$r\ne0$ 时，$(u,v)\mapsto u$ 将 $W_C([r:1])$ 同构到 $C\cap rC$，逆映射为 $u\mapsto(u,r^{-1}u)$。零点的见证为 $(0,v)$，无穷远的见证为 $(u,0)$。若 $[a:b]\in\mathbb P^1(F)$，则见证空间恰为 $\{(az,bz):z\in C\}$，所以维数为三。

为避免与齐次坐标混淆，暂将矩阵写为 $G=\left(\begin{smallmatrix}\alpha&\beta\\\gamma&\delta\end{smallmatrix}\right)$。同一对实际见证按

$$
\begin{aligned}
(a',b')&=(\alpha a+\beta b,\gamma a+\delta b),\\
(u',v')&=(\alpha u+\beta v,\gamma u+\delta v)
\end{aligned}
$$

同时传递。由于矩阵系数属于 $F$，$(u',v')$ 仍在 $C^2$ 内，且

$$
b'u'-a'v'=(\alpha\delta-\beta\gamma)(bu-av).
\tag{61.5}
$$

逆矩阵给出逆见证映射。这证明 $\operatorname{PGL}_2(F)$ 不变性，包含零和无穷远。此处权重指见证空间维数，不将其认作行列式的消失阶数。

对协变式，仍在原 $D$ 的固定坐标中置 $s=g(r)$、$A=cM_r+dI_6=M_{cr+d}$。域性及 $cr+d\ne0$ 使 $A$ 可逆，且 $\det A=N_{D/F}(cr+d)$。乘法交换性给出 $AM_s=aM_r+bI_6$，从而有实际矩阵恒等式

$$
A[\,B,M_sB\,]
=[\,B,M_rB\,]
\begin{pmatrix}dI_3&bI_3\\cI_3&aI_3\end{pmatrix}.
\tag{61.6}
$$

右侧分块矩阵的行列式是 $(ad-bc)^3$，故取行列式得到 (61.4) 对 $P_C$ 成立。再直接应用 (61.1) 的实际 $F$-线性张成等式，得到它对每个 $Q\in H_D$ 成立。没有将分裂平面当成实际窗口，也未假设 $r$ 生成 $D$。$\square$

## 62. 非零测试与实际标签的精确冗余

**定义 62.1（原标签评价与有向匹配）。** 对原 $r\in D$，令 $\operatorname{ev}_r(Q)=Q(r)$。当此泛函非零时记

$$
e(r)=[\operatorname{ev}_r|_{H_D}]\in\mathbb P(H_D^\vee)(F).
\tag{62.1}
$$

在分裂坐标中，任选一次原嵌入编号 $\Sigma=\{\sigma_1,\ldots,\sigma_6\}$；编号不改变标记。对一个有向完美匹配 $M$ 定义

$$
q_M(x)=\prod_{(i,j)\in M}(x_i-x_j),\qquad
[ij]=U_iV_j-U_jV_i,\qquad
\widetilde q_M(v)=\prod_{(i,j)\in M}[ij].
\tag{62.2}
$$

反向一条边要乘以负号；交换三个因子的顺序不变号。每个 $q_M$ 属于 $H_D\otimes_FL$。将每个变量分别齐次化到一次，得到从 $h\in H_D\otimes_FL$ 到多重次数 $(1,1,1,1,1,1)$ 的截面 $\widetilde h$ 的单射。以下在齐次向量族上写 $h_L(v)$ 时，均指这个唯一齐次化的取值。

**定理 62.2（实际基点及有原标记的轨道分离）。** 对全部原标签，

$$
\operatorname{ev}_r|_{H_D}=0\quad\Longleftrightarrow\quad r\in F.
\tag{62.3}
$$

因此 $e$ 在 $D\setminus F$ 上处处有定义，且对任意 $r,s\in D\setminus F$，

$$
e(r)=e(s)
\quad\Longleftrightarrow\quad
s=g(r)\ \text{对某个 }g\in\operatorname{PGL}_2(F).
\tag{62.4}
$$

这里两侧比较的始终是同一原嵌入所对应的值。对每个实际窗口 $C$，$w_C([r:1])=d_C(r)$ 因而经这个轨道集合分解。

证明。设 $k=[F(r):F]$。塔式次数公式与可分性说明 $k\in\{1,2,3,6\}$，六个原共轭恰有 $k$ 个不同值，各重复 $6/k$ 次。$k=1$ 时，由公共平移不变性和三次齐次性，所有 $Q\in H_D$ 在 $r\in F$ 上取零；这是原卷命题 52.3 的结论。

若 $k=2$，将两个三元等值块逐个跨块配对，得到非零匹配值。若 $k=3$，将三个二元块写成 $A=\{A_1,A_2\}$、$B=\{B_1,B_2\}$、$C'=\{C_1,C_2\}$，匹配 $(A_1B_1)(A_2C_1)(B_2C_2)$ 的三条边均非零。$k=6$ 时每个匹配均非零。因此扩域后的评价不为零，原 $F$-评价也不为零。这证明 (62.3)。若同时使用齐次匹配评价，则实际 $\mathbb P^1(D)$ 中的基点恰为 $\mathbb P^1(F)$：额外的实际点只有无穷远，而其六个齐次点全相同。分裂空间还存在四重重合等其他几何基点；本结论仅指实际域标签。

若 $r\notin F$，则任一可逆原域矩阵的分母 $cr+d$ 不会为零，且 $g(r)\notin F$。式 (61.4) 使两非零评价泛函成比例，证明 (62.4) 的反向。

反之，设 $e(r)=e(s)$，写 $x_i=\sigma_i(r)$、$y_i=\sigma_i(s)$。所有有向匹配在这两族上的值成同一个非零比例。先从这些值恢复有原标记的等值分拆：对任意两个原位置 $i,j$，

$$
x_i=x_j
\quad\Longleftrightarrow\quad
\text{每个包含边 }(i,j)\text{ 的匹配在 }x\text{ 上都取零}.
\tag{62.5}
$$

正向直接成立。反向只须在 $x_i\ne x_j$ 时补成非零匹配。三加三型删去两端后余下两个二元块，可跨块配对；二加二加二型余下的块大小为一、一、二，可将二元块的两点分别与两个单点配对；全异型任意补配均可。以上覆盖所有实际非标量类型。因此 $x,y$ 的原等值分拆完全相同，特别是其不同值的个数相同。

若个数为二，置 $K=F(r)\subset D$。分裂子代数 $K\otimes_FL$ 恰由在 $\Sigma\to\operatorname{Hom}_F(K,L)$ 的两个限制纤维上分别为常数的向量组成。共同等值分拆使 $s\otimes1$ 位于这个子空间。将其映到 $(D/K)\otimes_FL$ 并用扩域忠实性，得到 $s\in K$。所以 $s=\alpha r+\beta$，其中 $\alpha,\beta\in F$、$\alpha\ne0$，已经给出原域射影变换。此分支没有使用两个点不能保证的唯一射影变换。

若个数为三，唯一将三个不同 $x$ 值送到对应三个 $y$ 值的 $g\in\operatorname{PGL}_2(L)$ 自动满足全部六个原位置的对应。

若个数为六，先用原位置 $1,2,3$ 确定唯一的 $g$。对 $j=4,5,6$，令 $k,l$ 为除 $1,2,3,j$ 外的两个原位置。匹配比值

$$
\frac{q_{(13)(2j)(kl)}(x)}{q_{(1j)(23)(kl)}(x)}
=\frac{(x_1-x_3)(x_2-x_j)}{(x_1-x_j)(x_2-x_3)}
\tag{62.6}
$$

的分母非零，并与 $y$ 上的对应比值相同。这里所有边均按写下的方向取值。固定前三个不同点后，右侧是第四点的单射射影坐标；交比不变性遂使 $g(x_j)=y_j$。这证明全部原标记都由同一个 $g$ 匹配。

在三值或六值分支，对每个 $\gamma\in\operatorname{Gal}(L/F)$，$\gamma(g)$ 仍满足全部原标记条件，因为 $\gamma$ 只把条件的原嵌入位置同步置换。有至少三个不同点，唯一性给 $\gamma(g)=g$。将一个非零矩阵条目归一为一，其余条目均为 Galois 固定的比值，故属于 $F$；于是 $g\in\operatorname{PGL}_2(F)$，并在原 $D$ 内有 $s=g(r)$。最后应用定理 61.3 的见证传递即得权重分解。$\square$

**命题 62.3（通用测试不等于一个目标的支持位）。** 相同测试点保持标签的次数型，也保持每个实际窗口上的二元权重；但一个固定目标的单个支持位不能决定次数型或测试点。

证明。前两项已由 (62.5) 和定理 61.3 得到。后一项有实际例子：取任意原本原元 $\theta$，令 $C=\operatorname{span}_F\{1,\theta,\theta^2\}$。原标签 $1$ 和 $\theta$ 都属于这个窗口的正支持，前者次数为一，后者次数为六；但前者的通用评价为零，后者为非零。对非标量标签，§64 的同一个目标超平面也可容纳不同测试点。因此不能从一个目标的二元回答倒推出完整等值分拆或次数剖面。$\square$

## 63. 三维测试形状、原标记下降与不能提升的有理点

**定义 63.1（测试空间与实际像）。** 令 $X_D\subset\mathbb P(H_D^\vee)$ 为实际集合 $e(D\setminus F)$ 的约化几何 Zariski 闭包所定义的 $F$-子簇。记其实际评价像为 $I_D=e(D\setminus F)\subset X_D(F)$。$X_D$、$X_D(F)$ 和 $I_D$ 分别表示代数测试空间、它的原域有理点和已有原标签的像，不作相等预设。

**定理 63.2（原嵌入作用下降的 Segre 三次体）。** $X_D$ 是位于四维对偶射影空间中的三维 Segre 三次体的 $F$-形式，$I_D$ 在其中几何稠密。其下降作用来自原六个嵌入的作用；在标准 Segre 六坐标中，它表现为带符号的外自同构作用，六坐标不是六个原共轭值 $\sigma(r)$。

证明。以下经典不变量环事实只作为识别本题实际测试空间的中间输入。令

$$
R_L=\bigoplus_{n\ge0}
H^0\bigl((\mathbb P^1_L)^\Sigma,\mathcal O(n,n,n,n,n,n)\bigr)^{\operatorname{SL}_2}.
\tag{63.1}
$$

[Howard–Millson–Snowden–Vakil，*The ideal of relations for the ring of invariants of n points on the line*，§2.3，Theorem 2.1](https://math.stanford.edu/~vakil/files/hmsv2-121109.pdf) 的 Kempe 生成定理说明该环由一次有向匹配生成。次数一的仿射限制属于 (61.1) 的分裂空间，且限制为单射。

更精确地，[Dolgachev–Ortland，*Point sets in projective spaces and theta functions*，I §3，Example 2，印刷页 14–17](https://www.numdam.org/item/AST_1988__165__1_0.pdf) 给出以下五个一次基元和完整分次环表示：

$$
\begin{aligned}
t_0&=[12][34][56],& t_1&=[13][24][56],&
t_2&=[12][35][46],\\
t_3&=[13][25][46],& t_4&=[14][25][36],\\
R_L&\simeq L[T_0,T_1,T_2,T_3,T_4]/(\Phi),& T_i&\longmapsto t_i,\\
\Phi&=T_1T_2T_4-T_3(T_0T_4+T_1T_2-T_0T_1-T_0T_2+T_0^2).
\end{aligned}
\tag{63.2}
$$

五个仿射限制线性无关，故由 $\dim_FH_D=5$ 恰好得到 $R_{L,1}\simeq H_D\otimes_FL$。因此度一生成给出的闭嵌入

$$
\operatorname{Proj}R_L\ \hookrightarrow\
\mathbb P((H_D\otimes_FL)^\vee)
\tag{63.3}
$$

正是齐次匹配评价的像闭包。这里识别理想的是完整环表示 (63.2)，不以维数相同代替。Dolgachev–Ortland 同一 Example 2 的页 17 将它线性变换成

$$
z_1+\cdots+z_6=0,\qquad z_1^3+\cdots+z_6^3=0
\quad\text{在 }\mathbb P^5_L\text{ 中}.
\tag{63.4}
$$

HMSV 的 §1.4、Theorem 1.2 后也明确指出六点理想由 Segre 三次式主生成；Theorem 1.2 本身排除六点，不能用其二次关系结论替代 (63.2)。

六个点均在仿射图中的配置在总配置空间内稠密。其半稳定开集上的商映射因此仍有同一像闭包；将 $v_i=(x_i,1)$ 代入得到的就是原多项式评价映射在分裂后的表达。原六维仿射空间 $\mathbb A(D)$ 的 $F$-点为同一个 $D$ 的元素。无限域多项式消失原理说明，去掉评价基点后的实际非标量点在该定义域内几何稠密；这一原理在原卷定理 52.4 的实际帧下降中已给出证明。将任何包含实际评价像的几何闭集拉回这个定义域，它包含全部这些实际点，故包含整个定义域。因此实际像的几何闭包恰为 (63.3)。

设 $\rho:\operatorname{Gal}(L/F)\to S_\Sigma$ 为原嵌入作用。分裂坐标的半线性作用同时作用于系数，并将有向边 $(\sigma,\tau)$ 送到 $(\gamma\sigma,\gamma\tau)$；反向边保留其负号。评价、分次环及其理想均与此作用相容，故 (63.3) 正按这个原作用下降到 $X_D$。

标准坐标的作用需另行辨明。[Howard–Millson–Snowden–Vakil，*A description of the outer automorphism of S6, and the invariants of six points in projective space*，§§1.5、2.1](https://math.stanford.edu/~vakil/files/sixjan2308.pdf) 将一次截面表示识别为

$$
\operatorname{sgn}\otimes(\operatorname{Std}_5\circ\vartheta),
\tag{63.5}
$$

其中 $\vartheta$ 是由该文六个 mystic pentagons 固定的外自同构。采用其自对偶表示识别，在 $z$ 上原置换 $\pi$ 表现为 $\operatorname{sgn}(\pi)$ 乘以 $\vartheta(\pi)$ 的坐标置换；射影化后公共符号才消失。

若写迹模型，必须取作用为 $\vartheta\circ\rho$ 的辅助六元素 Galois 集及其对应六维 étale 代数 $E/F$，才有射影同构

$$
X_D\simeq
\{[z]\in\mathbb P(E):\operatorname{Tr}_{E/F}(z)=
\operatorname{Tr}_{E/F}(z^3)=0\}.
\tag{63.6}
$$

因为两边在 $L$ 上均为 (63.4)，射影下降置换相同。这里 $E$ 不必等于 $D$，也不必是域；它仅描述标准坐标的下降，不提供新的标签域或自由控制。上述原标记作用和理想的下降证明了所述 $F$-形式，稠密性也已在实际定义域上证明。$\square$

**定理 63.3（稳定形状的圆锥提升与节点的实际实现）。** 对每个稳定有理点 $y\in X_D(F)$，存在唯一到保标记同构意义的光滑圆锥曲线 $Q_y/F$，带标记态射 $\operatorname{Spec}D\to Q_y$，其几何配置的匹配商点为 $y$。保标记同构若存在则唯一。并且

$$
y\in I_D\quad\Longleftrightarrow\quad
Q_y\simeq_F\mathbb P^1_F
\quad\Longleftrightarrow\quad Q_y(F)\ne\varnothing.
\tag{63.7}
$$

几何六点配置的稳定性恰为每个位置的重数小于三，半稳定性恰为重数不超过三。非稳定商点是十个节点。其 $F$-有理点与 $D$ 的实际二次子域一一对应，且每个这样的节点都是实际评价点。因此

$$
I_D=
\{y\in X_D^{\mathrm{st}}(F):Q_y(F)\ne\varnothing\}
\ \cup\ \operatorname{Sing}(X_D)(F).
\tag{63.8}
$$

证明。使用 Dolgachev–Ortland，II §1，Proposition 1，页 21 的稳定几何商及 II §2，Theorem 1，页 23 的稳定判据作为中间输入：在六个单位权重的射影直线点上，判据正是所述重数不等式。一个稳定配置至少有三个不同的带标记点，故逐个保持原标记的 $\operatorname{PGL}_2$ 稳定子为平凡群。

取足够大的有限 Galois 扩域 $L'/F$，使 $y$ 有一个带原 $\Sigma$ 标记的稳定配置 $x$ 作为代表。稳定几何商说明，$x$ 的每个 Galois 共轭都在同一几何轨道。写

$$
(T_\gamma x)_\sigma=\gamma(x_{\gamma^{-1}\sigma}).
$$

存在唯一 $a_\gamma\in\operatorname{PGL}_2(L')$ 将 $T_\gamma x$ 送回 $x$。唯一性给出

$$
a_{\gamma\delta}=a_\gamma\,\gamma(a_\delta).
\tag{63.9}
$$

所以 $a_\gamma\circ\gamma$ 是带标记射影直线的下降数据。有限 Galois 下降得到 $\mathbb P^1$ 的一个 $F$-形式及 $\operatorname{Spec}D$ 的标记；该形式是光滑圆锥曲线。例如反典范线丛下降，扩域后为 $\mathcal O_{\mathbb P^1}(2)$，其三个截面将下降曲线嵌成平面光滑二次曲线。换代表配置仅共轭这些下降数据，故所得带标记圆锥曲线与选择无关。两个代表同一稳定点的配置由唯一射影变换相连，这个变换又与下降数据相容，所以带标记同构存在且唯一。

实际 $r$ 的六个值本来就在分裂直线 $\mathbb P^1_F$ 的原标记中，故若 $y=e(r)$ 稳定，则 $Q_y$ 分裂。反之，若 $Q_y$ 分裂，选取一个 $F$-同构到 $\mathbb P^1_F$，并在有限标记支撑之外选择一个原 $F$-有理无穷远；$F$ 无限，故可以选择。标记此时全部落在仿射直线内。它的六个仿射坐标是 Galois 等变的原嵌入族，正对应固定的 $D$ 中某个 $r$，而非另造一个抽象副本。稳定性使 $r\notin F$，且 $e(r)=y$。光滑圆锥曲线有原有理点当且仅当分裂，故得 (63.7)。

节点分支使用 Dolgachev–Ortland，II §4，Example 2，页 31：非稳定半稳定配置的闭轨道由两个不同点上的互补三元块组成，十个无序三加三分拆给出十个节点。任意三重重合的非闭轨道可能落到同一个节点，因而此处不能使用稳定轨道的唯一性。

一个节点在 $F$ 上有理恰好表示其无序三加三原分拆被 Galois 保持。原嵌入集传递，因此 Galois 群必传递作用于两个块。固定一个原嵌入 $\sigma_0:D\hookrightarrow L$，令 $H$ 为它的稳定子，$J$ 为含它的三元块的集合稳定子；则 $H\subset J$ 且 $[G:J]=2$，其中 $G=\operatorname{Gal}(L/F)$。所以 $L^J\subset L^H=\sigma_0(D)$ 给出原 $D$ 中的二次子域。这个子域的任意非标量生成元恰按该两个块取两个不同共轭值，实际评价就是原节点。反之，每个实际二次子域都给出其限制纤维分拆，因而给出一个有理节点；块分拆恢复该子域，故为一一对应。

实际次数三或六的标签均稳定，次数二的标签恰为上述闭三加三配置，次数一的评价为零。定理 62.2 与 (63.7) 因而给出 (63.8)。$\square$

**命题 63.4（一个显式稳定有理形状严格不能提升）。** 令 $t$ 为正实立方根二，并固定

$$
F=\mathbb Q,\qquad K=\mathbb Q(t),\qquad D=K(i),\qquad
Q_0:\ x^2+y^2+z^2=0,
$$

以及圆锥曲线上的点

$$
q=[i(1+t^2):1-t^2:2t].
\tag{63.10}
$$

点 $q$ 的剩余域恰为原 $D$，其六个原共轭互异。取包含 $D$ 的有限 Galois 正规闭包 $L\subset\mathbb C$ 和全部原 $\Sigma=\operatorname{Hom}_{\mathbb Q}(D,L)$。对每个 $\sigma$ 置

$$
v_\sigma=
\begin{cases}
(\sigma(t),1),&\sigma(i)=i,\\
(-1,\sigma(t)),&\sigma(i)=-i.
\end{cases}
\qquad
\ell(h)=i\,h_L((v_\sigma)_{\sigma\in\Sigma})\quad(h\in H_D).
\tag{63.11}
$$

这里 $h_L$ 按定义 62.1 有向齐次化。则 $\ell$ 是非零的原 $\mathbb Q$-值线性泛函，

$$
y=[\ell]\in X_D^{\mathrm{st}}(\mathbb Q),\qquad
Q_y\simeq_{\mathbb Q}Q_0,\qquad y\notin I_D.
\tag{63.12}
$$

所以对这个指定六次域，实际评价像几何稠密而严格小于有理点集。

证明。多项式 $T^3-2$ 由 Eisenstein 判据在 $\mathbb Q$ 上不可约，$K\subset\mathbb R$ 使 $i\notin K$，故 $[D:\mathbb Q]=6$。直接展开得

$$
-(1+t^2)^2+(1-t^2)^2+4t^2=0,
$$

所以 $q\in Q_0(D)$。曲线光滑，因为其梯度在射影空间内不可能同时为零。将 $z$ 坐标归一，置

$$
A=\frac{x}{z}=\frac{i(t+t^{-1})}{2},\qquad
B=\frac{y}{z}=\frac{t^{-1}-t}{2}.
$$

由 $t^2+2Bt=1$ 和 $t^3=2$，得到

$$
(1+4B^2)t=2+2B,\qquad
t=\frac{2(1+B)}{1+4B^2},\qquad
i=\frac{2A}{t+t^{-1}}.
\tag{63.13}
$$

分母非零，因为 $B$ 为实数且 $t>0$。于是 $\mathbb Q(A,B)=D$，剩余域恰为 $D$。若两个原嵌入给出同一个 $q_\sigma$，其归一坐标 $A,B$ 相同，因而在生成整个 $D$ 的元素上相同；两嵌入必相同。这证明六个原共轭互异。

在 $L$ 上使用参数同构

$$
\nu_i:\mathbb P^1_L\longrightarrow Q_{0,L},\qquad
[U:V]\longmapsto[i(U^2+V^2):V^2-U^2:2UV].
\tag{63.14}
$$

这是二次 Veronese 嵌入后接可逆线性坐标变换，像正为 $Q_{0,L}$，故为曲线同构。逐项代入 (63.11) 得 $\nu_i([v_\sigma])=q_\sigma$；在 $\sigma(i)=-i$ 的情形，所得三个坐标与 $\sigma(q)$ 同乘负一。故六个 $[v_\sigma]$ 互异，每个有向匹配在 $v$ 上都非零。

下面在原 $H_D^\vee$ 中证明有理性，而非仅在一个未辨明的扭曲空间中宣称有理。令 $\Gamma=\operatorname{Gal}(L/\mathbb Q)$、$\chi(\gamma)=\gamma(i)/i\in\{1,-1\}$，并置

$$
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
(T_\gamma v)_\sigma=\gamma(v_{\gamma^{-1}\sigma}).
\tag{63.15}
$$

若 $\chi(\gamma)=1$，则 $T_\gamma v=v$。若 $\chi(\gamma)=-1$，在 $\sigma(i)=i$ 的三个位置上有 $(T_\gamma v)_\sigma=Jv_\sigma$，在 $\sigma(i)=-i$ 的三个位置上有 $(T_\gamma v)_\sigma=-Jv_\sigma$。共同 $J$ 对一个三边匹配贡献 $(\det J)^3=1$，而三个位置的负号各出现一次，总贡献为负一。因此对每个匹配及其线性组合，

$$
h_L(T_\gamma v)=\chi(\gamma)h_L(v).
\tag{63.16}
$$

这里边的原方向随原嵌入一起传递，任何重新定向都保留负号。原 $h\in H_D$ 对系数及原标记的半线性作用固定，故

$$
\gamma(h_L(v))=h_L(T_\gamma v),\qquad
\gamma(i h_L(v))=\chi(\gamma)^2 i h_L(v)=i h_L(v).
\tag{63.17}
$$

于是 $\ell(h)\in\mathbb Q$。若 $\ell$ 为零，其 $L$-线性延拓将消去 $H_D\otimes L$ 中的每个匹配，与匹配在六个不同点上的非零值矛盾。因此 $\ell\ne0$。任取一次固定的原 $\mathbb Q$-基 $h_1,\ldots,h_5$，以下就是确定的有理射影坐标：

$$
[\,i h_{1,L}(v):\cdots:i h_{5,L}(v)\,].
\tag{63.18}
$$

式 (63.11) 和有向匹配齐次化逐项规定这些坐标，至少一项非零，式 (63.17) 证明每项有理；不需要数值搜寻或另作有理点存在假设。

在 $L$ 上，$[\ell]$ 就是六个 $[v_\sigma]$ 的匹配商点，所以由定理 63.2 它属于 $X_D$；已经证明的原域有理性使它属于 $X_D(\mathbb Q)$。六点互异保证稳定。进一步，若 $\chi(\gamma)=1$，则 $\gamma\nu_i=\nu_i$；若 $\chi(\gamma)=-1$，则在射影坐标中 $\gamma\nu_i=\nu_i\circ J$。因此 $\nu_i^{-1}\gamma\nu_i$ 分别为恒等或 $J$，且 $J^2=-I$ 在射影群中为恒等。这个下降数据把原标记逐个送到 $q_\sigma$，其下降对象恰为 $(Q_0,\operatorname{Spec}D\to Q_0)$。定理 63.3 的唯一性遂给 $Q_y\simeq Q_0$。

也可以直接用原交比看出没有实际提升。反设 $y=e(r)$，令 $w_\sigma=(\sigma(r),1)$。所有匹配在 $v$ 上非零，评价线相同使所有匹配在 $w$ 上也非零；若两共轭相同，包含那条边的匹配即为零，矛盾。因此 $r$ 的六个共轭互异。固定三个原位置，由三点唯一性得到唯一的 $g\in\operatorname{PGL}_2(L)$ 将它们从 $w$ 送到 $v$；对其余每个位置，(62.6) 的匹配比值相同，分母非零，故 $g$ 也逐个匹配该位置。

令 $\psi=\nu_i\circ g:\mathbb P^1_L\to Q_{0,L}$。则 $\psi(\sigma(r))=q_\sigma$。对任意 $\gamma\in\Gamma$，有

$$
(\gamma\psi)(\sigma(r))
=\gamma\bigl(\psi((\gamma^{-1}\sigma)(r))\bigr)=q_\sigma.
\tag{63.19}
$$

$\gamma\psi$ 与 $\psi$ 在三个不同原标记上相同，故这两个同构相同。于是 $\psi$ 及其逆下降为 $\mathbb Q$-同构 $\mathbb P^1_{\mathbb Q}\simeq Q_0$。然而实数中三平方和为零只允许零向量，故 $Q_0(\mathbb R)=\varnothing$，与该同构的无穷远像给出原有理点矛盾。不存在任何实际提升。几何稠密性由定理 63.2 给出，严格性由此点给出；不由这个指定域的反例推出所有六次域都存在同样障碍。$\square$

## 64. 正支持的关联截面与既有四点证书

**定义 64.1（目标系数线的对偶超平面）。** 固定实际窗口 $C$，并设 $P=P_C\ne0$。在对偶空间中置

$$
P^\perp=\{\lambda\in H_D^\vee:\lambda(P)=0\},\qquad
\Pi_P=\mathbb P(P^\perp)\simeq\mathbb P^3_F.
\tag{64.1}
$$

$\Pi_P$ 只依赖目标系数线 $[P]$。原支持仍为 $S_C=\{r\in D^\times:d_C(r)>0\}$。

**定理 64.2（实际正测试的关联解释）。** 对每个原非标量 $r\in D\setminus F$，

$$
r\in S_C\quad\Longleftrightarrow\quad
e(r)\in X_D\cap\Pi_P.
\tag{64.2}
$$

若进一步 $P$ 绝对不可约，则既有四正标签证书在测试空间中的对偶表述为：存在四个实际非标量正标签 $r_1,\ldots,r_4$，使

$$
\begin{aligned}
\operatorname{span}_F\{\operatorname{ev}_{r_1},\ldots,
\operatorname{ev}_{r_4}\}&=P^\perp,\\
\langle e(r_1),\ldots,e(r_4)\rangle&=\Pi_P,\\
\bigcap_{j=1}^4\ker(\operatorname{ev}_{r_j}|_{H_D})&=FP.
\end{aligned}
\tag{64.3}
$$

这四个标签来自四个不同的实际 $\operatorname{PGL}_2(F)$ 轨道。

证明。原行列式判据 (51.3) 在 $r\ne0$ 时给出 $d_C(r)>0$ 当且仅当 $P(r)=0$。非标量评价由定理 62.2 非零，故这个等式恰为射影关联 $e(r)\in\Pi_P$；$e(r)\in X_D$ 已由定义保证，得到 (64.2)。

绝对不可约性下，直接复用 [原卷定理 53.3、54.1 和命题 54.2](AURIC_R5_026_CATALAN_SUPPORT_CERTIFICATES.md#54-少量实际正标签切出系数线)：实际 $S_C$ 在 $V(P)$ 中几何稠密，其全部取值泛函的共同核为 $FP$，且五维 $H_D$ 的该共同核由四个实际正标签取得。标量标签上的取值恒为零，不能进入四个独立泛函中，所以这四个标签非标量。

有限维对偶性将一维共同核 $FP$ 等价地变成四维泛函张成空间 $P^\perp$，射影化即为 (64.3)。这正是既有证书的对偶解释，不再将其视为另一个存在性结论。若两个所选标签属于同一个实际射影变换轨道，定理 62.2 使它们的泛函成比例，与四个泛函独立矛盾。$\square$

**命题 64.3（关联描述保留的算术与恢复边界）。** 正的实际评价像不自动等于截面的全部原有理点。稳定有理截面点能成为原正标签测试，当且仅当其下降圆锥分裂；有理节点截面点总能成为原正标签测试。非零原标量虽然恒为正，评价却为零。式 (64.3) 确定系数线，不附加实际窗口的非线性最优恢复结论。

证明。对截面内的稳定点，定理 63.3 先给原标签存在的充要条件；一旦有实际提升，(64.2) 才将它判为正。节点由同一定理的原二次子域实现，再由关联判据判正。所以截面点的原域有理性不能替代圆锥分裂条件。对 $a\in F^\times$，有 $aC=C$，故 $d_C(a)=3$，但原卷命题 52.3 给 $\operatorname{ev}_a|_{H_D}=0$，不能射影化为测试点；零点的人工交维约定仍按定义 61.2 保留。

另一方面，实际行列式系数仅是 $\mathbb P(H_D)$ 内的非线性子族，(61.1) 的张成结论不宣称这个子族等于整个系数空间。四个线性测试在全五维候选空间中隔离系数线，不排除更少测试结合实际子族约束得到唯一性，也不把系数线等同于原窗口。支持的恢复由原多项式决定；窗口分类仍须使用其自身已有假设。故上述对偶解释不产生实际非线性最优性或新的窗口恢复定理。$\square$

**命题 64.4（忘去坐标之后，形状、提升与关联的完整几何图景）。** 固定原来的六次域和六个原嵌入，给一个实际非标量标签取六个共轭点，并同时忘去射影直线上的坐标，得到的正是它的通用射影测试。两个实际标签得到同一测试，当且仅当能由原域系数的同一个分式线性变换互相得到；原嵌入标记始终保留。所有这些实际测试稠密地铺在一个三维三次形状空间上，但其中的原有理形状还可能缺少实际标签：稳定形状带有唯一的有原标记圆锥曲线，只有圆锥能在原域上展开成射影直线时才有提升；非稳定有理节点则由实际二次子域实现。目标窗口的正测试恰是实际像落入目标对偶超平面的点；在绝对不可约假设下，已有四正例证书就是来自四个不同实际轨道、张成该超平面的四个点。

证明。定理 61.3 用同一对原见证的可逆传递，证明忘去原域射影坐标不改变任何窗口的二元权重。定理 62.2 反向由原等值分拆和交比恢复唯一所需的原域变换，二次分支则由共同实际子域处理，故忘去的恰是坐标重复，而非原嵌入之间的对应。定理 63.2 用匹配不变量的完整环关系给出三维三次空间，实际仿射标签的稠密性给出实际测试的几何稠密性；标准六坐标的外作用并未替换原标记。定理 63.3 将稳定有理形状的剩余问题精确放在有原标记圆锥是否分裂上，并另外处理二次子域节点；命题 63.4 的无实点圆锥证明这一提升条件确有内容。最后，定理 64.2 将正支持写成测试与目标超平面的关联，再将既有证书对偶化为四点张成。因而坐标忘却、原标记形状、原域提升和目标正支持在同一图景中相接，同时保留了从有理形状回到实际标签所需的算术条件。$\square$

## 追加锚（本行以下为增补区）

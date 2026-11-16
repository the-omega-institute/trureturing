# 十次与十二次原连续幂系数的完整实际形式纤维

## 124. 原系数、实际正参数与纤维的定义

**定义 124.1（同一个原域中的连续幂窗口）。** 设 $F$ 为特征零域，$D/F$ 为可分域扩张，
$[D:F]=2m$，其中 $m\in\{5,6\}$。任取本原元 $\theta\in D$，记其首一最小多项式为
$f(T)$，并置

$$
C=\operatorname{span}_F(1,\theta,\ldots,\theta^{m-1}).
\tag{124.1}
$$

固定非零体积形式 $\nu:\det_FD\to F$。对窗口的包含帧 $E_C$，原系数多项式为

$$
P_C(x)=\nu\bigl(\det[E_C,M_xE_C]\bigr),
\qquad M_x(z)=xz\quad(x,z\in D).
\tag{124.2}
$$

它的射影系数点记为 $p=[P_C]$。换帧、换体积只改变公共非零因子。
这里使用 [039，§111](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md)
的原系数像环 $S_F$：它是全部互补系数非零的系数开集上，原映射的约化闭像的坐标环。
具体地，取有限 Galois 分裂域 $L/F$，保留全部原嵌入标签并暂予排序。若 $p_I$ 是包含帧的行子式，则

$$
c_I=\alpha\epsilon_Ip_Ip_{I^c},
\qquad
S_F\otimes_FL
 =L[(c_I/c_{E_0})^{\pm1}:|I|=m].
\tag{124.3}
$$

其中，若 $e_1,\ldots,e_{2m}$ 是按原标签排序的分裂幂等元，则
$\alpha=\nu_L(e_1\wedge\cdots\wedge e_{2m})$；$\epsilon_I$ 是行序列 $(I^c,I)$ 相对于
$1,\ldots,2m$ 的符号，两组内部均按递增次序。$E_0$ 是任一参考标签集。
$S_F$ 按 039 的原域闭像定义，(124.3) 是它的扩底表示；不把某个分裂标签图单独认作原 $F$ 图。

**定义 124.2（完成环及负余切的记号）。** 令 $U\subset\operatorname{Gr}_F(m,D)$ 为全部最大行子式
非零的统一开集，$T_D=(\operatorname{Res}_{D/F}\mathbb G_m)/\mathbb G_m$ 按同一个 $D$ 中的乘法作用。
沿用 039 的光滑几何商 $X_D=U/T_D$、由迹正交补诱导的 Gale 对合 $\iota$，以及
$B_F=\mathcal O(X_D)^\iota$。由 039 定理 113.1，它是 $S_F$ 的有限双有理正规化。
令 $x_C\in X_D(F)$，令 $y$ 为其在 $\operatorname{Spec}B_F$ 中的像，并记

$$
S=(S_F)_p,
\qquad B=(B_F)_y,
\qquad
\mathscr T=\widehat S,
\qquad \mathscr B=\widehat B.
\tag{124.4}
$$

完成均取指定点的极大理想拓扑。连续幂窗口统一，且
$\lambda=1/f'(\theta)$ 满足 $\lambda C=C^\perp$；故 $x_C$ 固定。
039 定理 115.1、116.1 给出原 $F$ 上的对合相容模型

$$
\mathscr R=F[[u_1,\ldots,u_a,v_1,\ldots,v_b]],
\qquad
\iota(u,v)=(u,-v),
\qquad
\mathscr B=\mathscr R^\iota,
\tag{124.5}
$$

其中

$$
a=\frac{m(m-1)}2,
\qquad
V=F[T]_{\le m-2},
\qquad n=\dim_FV=m-1,
\qquad
W=\bigwedge^2V,
\qquad b=\dim_FW=\binom n2.
\tag{124.6}
$$

选取反变参数 $v_j$，使其线性余切与 039 的
$W\simeq\ker(\operatorname{Sym}^2C\to D)$ 识别相容。
这个识别把对称二元多项式写为

$$
Q_0(s,t)=(s-t)A(s,t),
\qquad A(t,s)=-A(s,t),
\qquad \deg_sA,\deg_tA\le m-2.
\tag{124.7}
$$

记 $P$ 为光滑商的正切空间，故 $\dim P=a$。正规化完成环的余切为

$$
\mathfrak m_{\mathscr B}/\mathfrak m_{\mathscr B}^2
 =P^\vee\oplus Q,
\qquad Q=\operatorname{Sym}^2W.
\tag{124.8}
$$

右端的 $Q$ 由纯二次 $v$ 单项式表示；$v_j$ 本身属于光滑覆盖，不属于不变量环。
定义

$$
w:Q\longrightarrow\bigwedge^4V,
\qquad w(\xi\eta)=\xi\wedge\eta,
\qquad K=\ker w.
\tag{124.9}
$$

这里 $\xi\eta$ 是对称代数中的乘积。两个二向量外乘可交换，所以 $w$ 定义良好。
$n$ 是 $V$ 的维数，$b$ 才是负参数的数目；二者分别为 $4,6$ 或 $5,10$。

**约定 124.3（复用的完整耦合像与实际枢轴）。** 记

$$
H=\operatorname{im}\left(
\mathfrak m_S/\mathfrak m_S^2
 \longrightarrow P^\vee\oplus Q\right).
\tag{124.10}
$$

[040，定理 122.1、命题 122.2](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md)
的完整原族结论给出

$$
H\cap Q=K,
\qquad H+Q=P^\vee\oplus Q.
\tag{124.11}
$$

这里的交空间与和空间都在同一个直和余切空间中计算。这些等式在 $F$ 上成立；它们不是两个投影秩的相加。
本卷复用 039 的有限正规化与原域形式模型、040 的矩形插值和 (124.11)，不重新证明这些结果。

称 $s_1,\ldots,s_a\in S$ 为一组实际正系数枢轴，若它们是原系数局部环中的 $F$ 定义函数，且

$$
t_i=s_i-s_i(p)\in\mathfrak m_S,
\qquad
[t_i]=e_i=(\ell_i,q_i)\in H,
\qquad
\ell_1,\ldots,\ell_a\text{ 是 }P^\vee\text{ 的一组基}.
\tag{124.12}
$$

这种选择存在：由 (124.11)，$H\to P^\vee$ 满射；在原 $F$ 余切像中选基的提升，再在
$\mathfrak m_S$ 中选实际代表即可。它也允许从原系数函数作 $F$ 线性组合。
分裂域中的单个矩形函数不自动是 $F$ 函数；若用分裂矩形展示张成，仍须按这个原域像选择枢轴。
“正”指 (124.12) 的正特征微分，不指 $F$ 上的序或数值正性。

**定义 124.4（实际完成纤维与收缩核）。** 固定任意一组满足 (124.12) 的枢轴。
令 $\varphi:\mathscr T\to\mathscr B$ 为原完成系数同态，置

$$
\begin{aligned}
I_{\mathscr T}&=(t_1,\ldots,t_a)\mathscr T,\\
J_{\mathscr B}&=(\varphi(t_1),\ldots,\varphi(t_a))\mathscr B,\\
B_0&=\mathscr B/J_{\mathscr B},\\
\mathfrak L&=\ker(\mathscr T\longrightarrow B_0)
             =\varphi^{-1}(J_{\mathscr B}),\\
A_0&=\operatorname{im}(\mathscr T\longrightarrow B_0)
             =\mathscr T/\mathfrak L.
\end{aligned}
\tag{124.13}
$$

$B_0$ 是所选正规化完成局部环中，实际正参数取原点值的纤维。
$A_0$ 始终是原完成系数环在该纤维中的像。只有
$I_{\mathscr T}\subseteq\mathfrak L$ 自动成立；不在定义中加入
$\mathfrak L=I_{\mathscr T}$。因此有自然满射

$$
\mathscr T/I_{\mathscr T}\twoheadrightarrow A_0,
\qquad
\ker=\mathfrak L/I_{\mathscr T}.
\tag{124.14}
$$

这个核与正规化纤维中缺失的函数是不同对象。

## 125. 实际消元、有限像与完成拓扑

**命题 125.1（原族实际纤维的坐标与闭像）。** 在定义 124.1--124.4 的全部条件下，
保留所选负参数的线性识别，可以在原 $F$ 上把实际 $t_i$ 用作正形式坐标，得到

$$
\mathscr B\simeq F[[t_1,\ldots,t_a,v_1,\ldots,v_b]]^{v\mapsto-v},
\qquad
B_0\simeq F[[v_1,\ldots,v_b]]^{v\mapsto-v}.
\tag{125.1}
$$

$A_0$ 是剩余域为 $F$ 的完备 Noether 局部环，$B_0$ 是有限 $A_0$ 模。
若记

$$
\mathfrak n=\mathfrak m_{A_0},
\qquad \mathfrak m=\mathfrak m_{B_0},
\tag{125.2}
$$

则 $A_0\subset B_0$ 的诱导 $\mathfrak m$ 进拓扑与其自身的 $\mathfrak n$ 进拓扑等价，且
$A_0$ 在 $B_0$ 中闭。

证明。先说明有限完成的适用对象。$S_F$ 是有限型 $F$ 代数，故 Noether；039 定理 113.1 给出
$B_F$ 对 $S_F$ 有限。令 $C_B=B_F\otimes_{S_F}S$，则这是有限半局部 $S$ 代数。
对 $p$ 上方的极大理想 $y_j$，有限完成分解给

$$
\mathscr T\otimes_SC_B
 \simeq\prod_j\widehat{(B_F)_{y_j}}.
\tag{125.3}
$$

具体使用的是 Stacks Project
[Lemma 10.97.8，07N9](https://stacks.math.columbia.edu/tag/07N9)：左端是有限代数的
$\mathfrak m_S$ 进完成，右端各因子取各自的极大理想完成。
所选的 $\mathscr B$ 是有限直积因子，因而是有限 $\mathscr T$ 模。
039 的实际几何纤维约化支撑为一点，而 $y$ 的剩余域为 $F$，在此处也可直接使用唯一局部因子。
上述因子论证本身只需有限性，不需另加完成后唯一性的前提。

若使用局部包含的写法，有限模完成的正合性保证其单射性；所用结果为
[Lemma 10.97.1，00MA](https://stacks.math.columbia.edu/tag/00MA)。
有限局部扩张的两种完成拓扑由
[Lemma 10.97.7，0394](https://stacks.math.columbia.edu/tag/0394) 相容：极大理想有限生成，且模掉
$\mathfrak m_S$ 后为有限维剩余代数。这也解释了 (125.3) 中两种完成的对应。
以下只使用 $\varphi$ 和它的实际核，不以单个完成因子的单射性代替收缩计算。

现在在光滑覆盖 $\mathscr R$ 上处理实际参数。每个 $t_i(u,v)$ 不变，常数为零，故没有纯 $v$ 一次项。
由 (124.12)，它们的 $u$ 一次系数矩阵可逆。因此

$$
(u,v)\longmapsto(t(u,v),v)
\tag{125.4}
$$

具有可逆的普通线性部分。按 $(u,v)$ 的总次数递归求逆：一次项用该可逆矩阵求解；已确定低于
$r$ 次的逆式后，$r$ 次的未知系数仍由同一线性矩阵唯一决定。完备性使这些逐次解组成形式逆。
所有系数都在 $F$ 中。映射 (125.4) 与对合交换，它的逆也由唯一性与对合交换。
于是 $\mathscr R\simeq F[[t,v]]$，取不变量得到 (125.1) 的第一个同构。

在这个光滑覆盖中，若不变量 $h\in(t)\mathscr R$，写
$h=\sum_i t_ih_i$，对各 $h_i$ 应用平均算子 $(1+\iota)/2$，便得

$$
(t)\mathscr R\cap\mathscr R^\iota=(t)\mathscr R^\iota.
\tag{125.5}
$$

并且每个模 $(t)$ 的不变量都有不变提升。因此取不变量与此处的商相容，给出
$B_0\simeq F[[v]]^{v\mapsto-v}$。等式 (125.5) 属于光滑覆盖及其不变量环；
它不证明 $\varphi^{-1}(J_{\mathscr B})=I_{\mathscr T}$。
实际纤维消去的是 $t(u,v)$，不是在旧图中直接令 $u=0$。

由有限性，$B_0$ 是有限 $\mathscr T$ 模。$\mathscr T$ 在其中的作用经
$A_0=\mathscr T/\mathfrak L$ 因子化，故 $B_0$ 对 $A_0$ 有限。
Noether 局部环的完成仍 Noether，而完备 Noether 局部环对任意理想的商完备；后者也可由 00MA
对理想、环及商的有限模正合列直接得到。这给出 $A_0$ 的完备性及 Noether 性。
原同态和商同态都保持指定点的剩余值，故 $A_0$ 是局部环且剩余域恰为 $F$。

余下的闭性需要有限模拓扑，不能只由“来源完备”推出。$B_0/\mathfrak nB_0$ 是有限维局部
$F$ 代数，所以其极大理想幂零。存在整数 $e\ge1$ 使

$$
\mathfrak m^e\subset\mathfrak nB_0\subset\mathfrak m,
\qquad
\mathfrak m^{er}\subset\mathfrak n^rB_0\subset\mathfrak m^r
\quad(r\ge1).
\tag{125.6}
$$

对有限 $A_0$ 模中的子模 $A_0\subset B_0$ 使用
[Artin--Rees 引理，10.51.2，00IN](https://stacks.math.columbia.edu/tag/00IN)。
存在 $c$ 使 $r\ge c$ 时

$$
\mathfrak n^rB_0\cap A_0
 \subseteq\mathfrak n^{r-c}A_0.
\tag{125.7}
$$

(125.6)--(125.7) 及 $\mathfrak n^r\subset A_0\cap\mathfrak m^r$ 证明两种子环拓扑共尾。
再令 $M=B_0/A_0$，这是有限 $A_0$ 模。
[Krull 交定理，10.51.4，00IP](https://stacks.math.columbia.edu/tag/00IP) 给

$$
\bigcap_{r\ge1}\mathfrak n^rM=0.
\tag{125.8}
$$

若 $z\in B_0$ 属于 $A_0$ 的 $\mathfrak m$ 进闭包，对每个 $r$ 可选 $a_r\in A_0$，使
$z-a_r\in\mathfrak m^{er}\subset\mathfrak n^rB_0$。故 $[z]\in\mathfrak n^rM$ 对所有 $r$ 成立，
由 (125.8) 得 $z\in A_0$。这证明闭性。证毕。

**约定 125.2（偶级数的完成分次）。** 以下在 (125.1) 的实际纤维坐标中，把
$\operatorname{Sym}^dW$ 识别为 $v$ 次数为 $d$ 的齐次多项式。于是作为完备拓扑向量空间，

$$
B_0=\prod_{r\ge0}\operatorname{Sym}^{2r}W,
\qquad
\mathfrak m^r=\prod_{j\ge r}\operatorname{Sym}^{2j}W,
\qquad
\mathfrak m^r/\mathfrak m^{r+1}\simeq\operatorname{Sym}^{2r}W.
\tag{125.9}
$$

乘法按齐次次数卷积。这里是完成的直积，不是只容许有限支撑的普通直和。
第二个等式来自每个次数至少 $2r$ 的偶单项式都可提出 $r$ 个二次因子；
按有限多个可能的 $2r$ 次首因子归组，同样适用于整个形式级数。
特别地，$\mathfrak m^2$ 是全部 $v$ 次数至少四的偶级数。

## 126. 完整耦合余切到实际纤维的二次桥

**命题 126.1（实际枢轴图的商）。** 在定义 124.1--124.4 的条件及命题 125.1 的坐标下，
原像环的二次初始空间精确为

$$
\operatorname{im}\left(
\mathfrak n/\mathfrak n^2\longrightarrow\mathfrak m/\mathfrak m^2
\right)=K\subset Q.
\tag{126.1}
$$

更明确地，令 $E=\operatorname{span}_F\{e_1,\ldots,e_a\}$。
对任一 $(\ell,q)\in P^\vee\oplus Q$，唯一写成
$\ell=\sum_i c_i\ell_i$，则实际纤维的余切商映射为

$$
(P^\vee\oplus Q)/E\simeq Q,
\qquad
[(\ell,q)]\longmapsto q-\sum_i c_iq_i.
\tag{126.2}
$$

在这个识别下，$H/E$ 的像恰为 $H\cap Q=K$。因此每个 $k\in K$ 都有实际像元素
$f_k\in\mathfrak n$，满足 $f_k-k\in\mathfrak m^2$。

证明。对 $\mathscr B\to B_0=\mathscr B/J_{\mathscr B}$，余切空间的核是实际生成元
$t_i$ 的类所张成的 $E$，即

$$
\mathfrak m/\mathfrak m^2
 \simeq
\mathfrak m_{\mathscr B}/
 (\mathfrak m_{\mathscr B}^2+J_{\mathscr B})
 \simeq(P^\vee\oplus Q)/E.
\tag{126.3}
$$

因为 $\ell_i$ 成基，$E\cap Q=0$，且 $E+Q=P^\vee\oplus Q$。
因此 $Q\to(P^\vee\oplus Q)/E$ 是同构。减去具有相同正向分量的实际枢轴组合，正好给出 (126.2)。
这个 $Q$ 的同构与 (125.9) 相同：形式坐标变换 (125.4) 保留了负参数 $v$，
故纯二次 $v$ 类在实际纤维中仍由同一个二次齐次多项式表示。

由 $E\subset H$，对任意 $h=(\ell,q)\in H$ 有

$$
h-\sum_i c_ie_i
   =\left(0,q-\sum_i c_iq_i\right)\in H\cap Q=K.
\tag{126.4}
$$

反之，任意 $(0,k)$、$k\in K$ 都已在 $H$ 中，且不被对 $E$ 的商消去。
所以 $H=E\oplus(0,K)$，其商像恰为 $K$。

完成化不改变 $S$ 的余切空间及其到 $\mathscr B$ 的像；另一方面，
$\mathscr T\twoheadrightarrow A_0$ 是剩余域为 $F$ 的局部满射，故
$\mathfrak m_{\mathscr T}\twoheadrightarrow\mathfrak n$。
将这两个事实与 (126.3)--(126.4) 组合，便得 (126.1) 和每个 $k$ 的实际提升。
这一步不要求 $\mathfrak L=I_{\mathscr T}$。

特别地，一般图坐标中的 $q_i$ 可以非零，必须与正分量一起消去。
取 $H$ 到 $Q$ 的原始投影不能代替 (126.2)；即使一条直线
$F(1,1)\subset F\oplus F$ 的两个投影都满射，模掉这条实际枢轴图后，其自身的像仍为零。
这里确定二次初始空间的依据是完整的 $H/E$，不是投影秩。证毕。

## 127. 十次与十二次实际像纤维的完整正规形

**定理 127.1（全部高阶尾项与实际环等式）。** 设 $F$ 为特征零域，$D/F$ 为次数
$2m\in\{10,12\}$ 的可分域扩张，$\theta$ 为任一本原元，窗口为
$C=\langle1,\theta,\ldots,\theta^{m-1}\rangle_F$。
使用 (124.2)--(124.3) 的原带标签带符号系数环，并任取一组满足 (124.12) 的实际
$F$ 定义正系数枢轴。按 (124.13) 定义 $B_0$ 和实际像 $A_0$。
则在保持 (124.6)--(124.7) 的负线性识别的实际消元坐标中，

$$
\boxed{
B_0=F[[v_1,\ldots,v_b]]^{v\mapsto-v},
\qquad
A_0=F+K+\mathfrak m_{B_0}^2.
}
\tag{127.1}
$$

这是 $B_0$ 中的嵌入子环等式。等价地，$A_0$ 是映射
$B_0\to B_0/\mathfrak m_{B_0}^2=F\oplus Q$ 下 $F\oplus K$ 的逆像；作为完成拓扑向量空间，

$$
A_0=F\oplus K\oplus\prod_{r\ge2}\operatorname{Sym}^{2r}W.
\tag{127.2}
$$

证明。命题 125.1 已给第一项等式、实际像的完备性与闭性，命题 126.1 已给二次初始空间。
还需证明二次信息的乘积足够，以及这些乘积的无限提升确实留在实际像中。
下面的外代数乘积是本原族证明的中间步骤；外四次核的经典曲率、Plücker 对偶背景可参见
Bettiol--Kummer--Mendes，*Convex Algebraic Geometry of Curvature Operators*，
[arXiv:1908.03713v2，§§2.1--2.2](https://arxiv.org/html/1908.03713v2)。
这里不把 $K$ 认作对偶侧的 Plücker 二次关系理想，也不需要实内积的识别。

先证明 $n=4,5$ 时

$$
K\cdot K=\operatorname{Sym}^4W,
\tag{127.3}
$$

左端表示两个 $K$ 元素的乘积的 $F$ 线性张成。
取 $V$ 的任意基 $e_1,\ldots,e_n$，以 $x_{ij}=e_i\wedge e_j$、$i<j$ 为 $W$ 的基变量，
并允许有向记号 $x_{ji}=-x_{ij}$。若两条边共享端点，包括同一条边出现两次，其乘积的外乘为零，
故属于 $K$。四个不同指标还给出

$$
x_{ab}x_{cd}+x_{ac}x_{bd}\in K,
\tag{127.4}
$$

因为两项外乘分别为 $e_a\wedge e_b\wedge e_c\wedge e_d$ 及其负值。

考察任意四次基单项式，将四个边因子的出现位置当成四个不同顶点；重复的边仍保留其不同出现位置。
两个位置相邻，当且仅当原来的两条边共享端点。若这个相交图有完美匹配，原单项式已分成两组共享端点的
二次因子，因而属于 $K\cdot K$。

假设没有完美匹配。相交图不含三个两两不相邻的顶点：否则对应三条两两不交的原边，需要六个基指标，
与 $n\le5$ 矛盾。同时相交图的任意两条图边必须相交，否则它们就是完美匹配。
一族两两相交的图边，或有共同顶点，或全在一个三角形中。确实，若已有两条边
$ij,ik$，任何不含 $i$ 的边只能是 $jk$；一旦 $jk$ 存在，任何通向第四个顶点的边都会与三角形中某条边不交。
若全部图边共有一个顶点，其余三个顶点两两不相邻，已被排除。因此相交图只能是三角形加一个孤立顶点。

孤立顶点对应一条原边 $cd$；其余三条原边全在与 $c,d$ 不交的至多三个基指标上。
这三条边可以排列为 $ab,g,h$，并给 $a,b$ 定向，使 $g$ 含 $a$、$h$ 含 $b$。
若三条各不相同，它们就是三角形，任取一条作 $ab$ 即可。
若有重复，取一条重复边作 $ab$，剩下的一条同边可提供任一端点，另一条边提供另一个所需端点；
三条全相同的情形也包括在内。并且 $g,h$ 共享端点。
在对称代数中有精确恒等式

$$
x_{ab}x_{cd}x_gx_h
 =\bigl(x_{ab}x_{cd}+x_{ac}x_{bd}\bigr)(x_gx_h)
   -(x_{ac}x_g)(x_{bd}x_h).
\tag{127.5}
$$

右端四个二次因子都在 $K$：第一个由 (127.4)，其余分别因共享端点。
所以未直接配对的单项式也在 $K\cdot K$ 中。这覆盖所有四次单项式，证明 (127.3)。

进一步，对每个 $r\ge2$ 有

$$
K^r=\operatorname{Sym}^{2r}W,
\tag{127.6}
$$

这里 $K^r$ 仍指 $r$ 个 $K$ 元素的乘积的线性张成。
基例为 (127.3)。若 $r\ge3$，任意 $2r$ 次边单项式的前三个因子中必有两条边共享端点，
否则又需要六个不同基指标。提出这两个因子，得到一个 $K$ 元素；剩余次数为 $2r-2$ 的单项式
由归纳假设属于 $K^{r-1}$。所有单项式张成相应对称幂，故 (127.6) 成立。

现在作实际无限提升。取 $K$ 的有限 $F$ 基 $k_1,\ldots,k_h$，用命题 126.1 选择

$$
f_j\in\mathfrak n\subset A_0,
\qquad f_j\equiv k_j\pmod{\mathfrak m^2}.
\tag{127.7}
$$

此时只知道实际提升 $f_j$ 存在，不预先假定纯齐次代表 $k_j$ 已在 $A_0$ 中。
任取 $g\in\mathfrak m^2$。从 $r=2$ 开始递归，若已取得部分和 $a_{<r}\in A_0$，使
$g-a_{<r}\in\mathfrak m^r$，则其类属于

$$
\mathfrak m^r/\mathfrak m^{r+1}
   =\operatorname{Sym}^{2r}W=K^r.
\tag{127.8}
$$

故存在一个次数恰为 $r$ 的齐次多项式 $P_r$，系数在 $F$，使
$P_r(k_1,\ldots,k_h)$ 等于这个类。令

$$
g_r=P_r(f_1,\ldots,f_h)\in\mathfrak n^r.
\tag{127.9}
$$

由 (127.7)，$g_r$ 与 $P_r(k)$ 模 $\mathfrak m^{r+1}$ 相同，因此
$g-a_{<r}-g_r\in\mathfrak m^{r+1}$。取 $a_{<2}=0$，得到

$$
g-\sum_{r=2}^Ng_r\in\mathfrak m^{N+1}
\quad(N\ge2).
\tag{127.10}
$$

由于 $g_r\in\mathfrak n^r$，级数 $\sum_{r\ge2}g_r$ 在已证明完备的实际像环 $A_0$ 中收敛。
包含 $A_0\to B_0$ 连续，因为 $\mathfrak n^r\subset\mathfrak m^r$；其像极限由 (127.10)
及 $B_0$ 的分离性只能是 $g$。于是

$$
\mathfrak m^2\subset A_0.
\tag{127.11}
$$

这证明整个高阶尾部在实际像中，而不只是每个有限截断有一个近似原像。
命题 125.1 的闭像结论也与这些部分和的极限一致。

由 (127.7)、(127.11)，$f_j-k_j\in\mathfrak m^2\subset A_0$，遂有真正的纯二次元素
$k_j\in A_0$。故 $F+K+\mathfrak m^2\subset A_0$。
反向，任意 $a\in A_0$ 减去其常数项后属于 $\mathfrak n$，由 (126.1) 其二次类属于 $K$，
剩余部分在 $\mathfrak m^2$。因此反向包含也成立，得到 (127.1)--(127.2)。
所有修正均由实际原系数的像及其乘积构成；证明没有要求完整原系数关系的四次提升作为额外前提。证毕。

## 128. 本形式纤维的正规化、导子与有限长度

**推论 128.1（精确纤维导子）。** 在定理 127.1 的全部条件下，$B_0$ 是 $A_0$ 的有限正规化。
令

$$
\mathfrak c=(A_0:B_0)
 =\{z\in B_0:zB_0\subseteq A_0\}.
\tag{128.1}
$$

则它是两环的共同理想，且精确等于

$$
\boxed{\mathfrak c=\mathfrak n=K+\mathfrak m^2.}
\tag{128.2}
$$

作为 $A_0$ 模而非环商，有

$$
B_0/A_0\simeq_F Q/K\simeq_F\bigwedge^4V,
\qquad \mathfrak n(B_0/A_0)=0.
\tag{128.3}
$$

而真正的环商为

$$
A_0/\mathfrak c=F,
\qquad
B_0/\mathfrak c\simeq F\oplus\bigwedge^4V,
\qquad
(\lambda,\omega)(\mu,\eta)
 =(\lambda\mu,\lambda\eta+\mu\omega).
\tag{128.4}
$$

因此

$$
\operatorname{length}_{A_0}(B_0/A_0)=\delta=\binom n4,
\qquad
\operatorname{length}_{B_0}(B_0/\mathfrak c)=1+\delta.
\tag{128.5}
$$

具体数值为

| $[D:F]$ | $m$ | $n=\dim V$ | $b=\dim W$ | $\delta$ | $\operatorname{length}_{B_0}(B_0/\mathfrak c)$ |
| --- | --- | --- | --- | --- | --- |
| $10$ | $5$ | $4$ | $6$ | $1$ | $2$ |
| $12$ | $6$ | $5$ | $10$ | $5$ | $6$ |

证明。由 (127.1)，$\mathfrak n=K+\mathfrak m^2$。
若 $z\in K+\mathfrak m^2$、$b=\lambda+b_+\in B_0$，其中 $b_+\in\mathfrak m$，则

$$
zb=\lambda z+zb_+\in K+\mathfrak m^2,
\tag{128.6}
$$

因为 $z\in\mathfrak m$。所以 $\mathfrak n$ 本身也是 $B_0$ 理想，且包含于导子。
反之，导子元素必在 $A_0$。若它的常数项为 $\lambda\ne0$，取 $q\in Q\setminus K$，
其乘积的二次项为 $\lambda q\notin K$，与 (127.1) 矛盾。
这样的 $q$ 存在：$w(x_{12}x_{34})=e_1\wedge e_2\wedge e_3\wedge e_4\ne0$。
所以每个导子元素都在 $\mathfrak n$，证明 (128.2)。

对任意 $b\in B_0$，取其二次齐次部分 $b_2$，映射

$$
B_0\longrightarrow Q/K\longrightarrow\bigwedge^4V,
\qquad b\longmapsto[b_2]\longmapsto w(b_2)
\tag{128.7}
$$

满射，核是 $A_0$。这是线性映射及 $A_0$ 模映射，右端的 $A_0$ 作用经剩余域 $F$。
它不是环商映射，因为 $A_0$ 是含一子环而非 $B_0$ 的理想。
又 $w$ 满射：任一四个基向量的外积是 $w(x_{ij}x_{kl})$。
于是得到 (128.3)。给 (128.7) 加上常数项，便得到核为 $\mathfrak c$ 的环同态
$B_0\to F\oplus\bigwedge^4V$，其乘法为 (128.4)。
这证明两个环商及其中外四次理想的平方为零。

模 $B_0/A_0$ 被 $\mathfrak n$ 消去，其 $A_0$ 长度正好是 $F$ 维数 $\delta$。
局部 Artin 环 $B_0/\mathfrak c$ 的剩余域是 $F$，长度为其 $F$ 维数 $1+\delta$。
这给出 (128.5) 和表中数值；缺陷是 $\binom n4$，不是 $\binom b4$。

还须核对“正规化”针对的正是这个纤维。$B_0$ 是整环，并且正规：若
$z\in\operatorname{Frac}B_0$ 对 $B_0$ 整，则它对包含 $B_0$ 的正则形式环 $F[[v]]$ 也整，
故 $z\in F[[v]]$；它作为 $\operatorname{Frac}B_0$ 的元素被对合固定，遂属 $B_0$。
取非零 $d\in\mathfrak m^2$，例如 $v_1^4$。由 (127.11)，$d\in A_0$，且对所有 $b\in B_0$，
$db\in\mathfrak m^2\subset A_0$。所以

$$
b=\frac{db}{d}\in\operatorname{Frac}A_0,
\qquad \operatorname{Frac}A_0=\operatorname{Frac}B_0.
\tag{128.8}
$$

命题 125.1 给 $B_0$ 对 $A_0$ 有限。故它是 $A_0$ 在共同分式域中的整闭包。
正规化差异模被 $\mathfrak n$ 消去，支撑只在本形式纤维的闭点。证毕。

**推论 128.2（有限环对的内在表达）。** 在同样条件下，令 $E_4=\bigwedge^4V$ 并赋予
$F\oplus E_4$ 以 (128.4) 的平方零乘法。则

$$
A_0\simeq B_0\mathop{\times}_{F\oplus E_4}F,
\tag{128.9}
$$

其中 $B_0\to F\oplus E_4$ 取常数及二次项的外乘，$F\to F\oplus E_4$ 为常数嵌入。
这只是本实际纤维的环纤维积。

证明。纤维积在 $B_0$ 中对应于二次项外乘为零的全部元素。
由定理 127.1，这恰为 $F+K+\mathfrak m^2=A_0$。证毕。

## 129. 原域、实际枢轴理想与负坐标的依赖

**命题 129.1（每组实际选择分别成立）。** 定理 127.1 及推论 128.1 对每组满足 (124.12) 的
实际 $F$ 枢轴分别成立。对固定的理想 $J_{\mathscr B}$，环对 $A_0\subset B_0$、收缩核
$\mathfrak L$、导子及缺失模由 (124.13) 内在确定。更换负形式坐标时，二次子空间 $K$ 须按其线性识别输运；
固定同一个负线性识别的高阶选择不改变 (127.1) 所描述的子环。
这些断言不包含不同实际枢轴理想在 $\mathscr B$ 中的相等、它们之间的典范识别，或完整原系数芽的乘积分解。

证明。固定 $J_{\mathscr B}$ 后，$B_0$ 和 $A_0$ 的定义均不涉及辅助参数。
任何另一组同理想的生成元给相同的商及像。
若改变为另一组独立正向枢轴，重复 (125.4) 及 (126.2)，新的实际图仍在 $H$ 中，且到 $P^\vee$ 为同构。
所以它自己的实际纤维二次像仍是 $K$，定理 127.1 的乘积及提升证明逐项适用。
这给每一个选择一个同型的抽象标准环对，但没有使原来两个理想自动成为同一个理想。

对同一实际纤维，反变参数之间的变换在光滑覆盖上是奇形式变换，形如

$$
v'=Mv+\text{奇数次数至少三的项},
\qquad M\in\operatorname{GL}(W).
\tag{129.1}
$$

因此二次齐次式的变换，除线性部分诱导的 $\operatorname{Sym}^2M$ 外，只差 $\mathfrak m^2$ 中的尾项。
固定线性识别时 $M$ 为恒等，故 $F+K+\mathfrak m^2$ 不变；改变线性识别时，必须同时输运 $K$。
不假定任意 $\operatorname{GL}(W)$ 都保持原来写下的 $K$。
内在的表达是 (127.1) 后所给的逆像环，而非选定纯二次代表本身。

所有这些构造在 $F$ 上完成。039 给 $F$ 上的正负模型，040 的 (124.11) 给原 $F$ 子空间，
实际枢轴取自 $S$。形式逆的递归只解 $F$ 上的可逆线性方程，(127.4)--(127.6) 是任意 $F$ 基下的恒等式，
而无限提升的各系数也在 $F$ 中。因而不需把一个单独的分裂标签函数强行下降。
指定本原元 $\theta$ 和连续幂的识别仍属于假设；对每个本原元分别成立，并不附带不同本原元之间的典范同一。

最后，$A_0$ 的定义使用收缩而非生成理想，这个区别不能由有限正规化本身消去。
例如一般有限完成正规化可以是

$$
A'=F[[s,z^2,z^3,sz]]\subset B'=F[[s,z]].
\tag{129.2}
$$

左端表示相应形式幂级数代数的像。它含有 $F[[s,z^2]]$，而
$B'=F[[s,z^2]]+zF[[s,z^2]]$，故 $B'$ 对 $A'$ 有限。
$z=z^3/z^2$ 给共同分式域，$B'$ 正规，因而是 $A'$ 的正规化。
在 $s=0$ 的像中只能得到 $F[[z^2,z^3]]$，所以 $z\notin A'$。
于是

$$
sz\in A'\cap sB',
\qquad sz\notin sA',
\tag{129.3}
$$

后一断言由在整环 $B'$ 中约去 $s$ 得出。
这个例子只说明一般收缩等式不能省证，不断言本原族的 $\mathfrak L/I_{\mathscr T}$ 必非零。

本纤维的环等式与导子没有计算 $\mathfrak L/I_{\mathscr T}$，也没有计算保留全部正参数时的混合高阶关系。
因此它们不识别 $\mathscr T$ 与 $A_0[[t_1,\ldots,t_a]]$，不计算完整原芽或全局的导子。
各个完成纤维具有相同标准型，也不能替代这些额外的关系与相容性义务。证毕。

## 130. 六维起的精确乘积障碍与实际高维边界

**命题 130.1（乘积路线的严格维数界）。** 现令 $V$ 为任意特征零域上的 $n$ 维向量空间，
$W=\bigwedge^2V$，$K=\ker(\operatorname{Sym}^2W\to\bigwedge^4V)$。
若 $n\ge6$，则

$$
K\cdot K\ne\operatorname{Sym}^4W.
\tag{130.1}
$$

特别地，定理 127.1 内部所用的二次乘积充分路线在 $n=6$ 已失败。
这个失败不否定次数 $2m\ge14$ 的实际原族纤维可能有额外的四次初始项。

证明。偶外代数的乘法在二向量上可交换，故有代数同态

$$
\varepsilon:\operatorname{Sym}(W)\longrightarrow\bigwedge^{\mathrm{even}}V,
\qquad \varepsilon(\xi)=\xi.
\tag{130.2}
$$

对普通多项式代数取形式微分，再对其系数施 $\varepsilon$，在四次部分得到线性映射

$$
\begin{aligned}
\Phi:\operatorname{Sym}^4W&\longrightarrow\bigwedge^6V\otimes W,\\
\Phi(z_1z_2z_3z_4)
 &=\sum_{i=1}^4
 \left(\bigwedge_{j\ne i}z_j\right)\otimes z_i.
\end{aligned}
\tag{130.3}
$$

二向量外乘的交换性使该表达对四个因子对称，因而定义良好。
对 $k,l\in K$，有 $\varepsilon(k)=\varepsilon(l)=0$；微分的 Leibniz 法则给

$$
\Phi(kl)=0.
\tag{130.4}
$$

具体地，$d(kl)=k\,dl+l\,dk$，对系数施 $\varepsilon$ 后两项分别含有
$\varepsilon(k)$、$\varepsilon(l)$，故全为零。这消去整个 $K\cdot K$，而不只是其中的坐标单项式。

取六个独立基向量，仍写 $x_{ij}=e_i\wedge e_j$，则

$$
\Phi(x_{12}^2x_{34}x_{56})
 =2(e_1\wedge e_2\wedge e_3\wedge e_4\wedge e_5\wedge e_6)
       \otimes x_{12}\ne0.
\tag{130.5}
$$

保留 $x_{34}$ 或 $x_{56}$ 的两项因重复 $e_1,e_2$ 而为零，另两项相等。
特征零保证因子 $2$ 非零。因此这个四次单项式不在 $K\cdot K$ 中。
任意 $n\ge6$ 都可选同样的六个独立向量，所以 (130.1) 在全部这些维数成立。

若回到实际 $m\ge7$ 连续幂原族，039--040 仍给有限正规化及完整二次像。
用该 $m$ 的实际枢轴按 (124.13) 重新定义 $A_0\subset B_0$，仍记 $\mathfrak m=\mathfrak m_{B_0}$。
其四次初始空间应另行记为

$$
G_4=
\frac{(A_0\cap\mathfrak m^2)+\mathfrak m^3}{\mathfrak m^3}
 \subseteq\mathfrak m^2/\mathfrak m^3
 =\operatorname{Sym}^4W.
\tag{130.6}
$$

实际二次提升的乘积只保证 $K\cdot K\subseteq G_4$。
要得到同样的完整正规形，首先必须证明实际原系数在消去实际枢轴及二次项后，还提供
$\operatorname{Sym}^4W/(K\cdot K)$ 中的全部缺失类；尤其须提供 (130.5) 所检测的非零商类。
这些初始项可能来自余切为零的原系数组合，而不来自二次可见类的乘积。
(130.4) 不消去这样的未知实际四次提升，故不能推出 $G_4$ 为真子空间。
一般高维原族的这项四次关系提升义务仍未解决；本命题只给乘积路线的反例。证毕。

## 131. 完整中文普通语言表述

**定理 131.1（实际纤维中只剩有限个最低次遗漏）。** 固定一个特征零域，以及它上面一个次数为十或十二的
可分域扩张。任取本原元，用从零次幂开始的连续五个或六个幂张成半维窗口，仍使用原来的全部嵌入标签、
互补符号和乘法行列式系数。选择原系数中真正存在的一整组独立正向参数，在正规化的完成局部环中把它们固定为
原点值。令 $B_0$ 是这个正规化形式纤维，令 $A_0$ 是原系数完成环在其中实际留下的函数。

那么 $B_0$ 的函数恰是负变量的全部偶形式级数。次数十时有六个负变量，次数十二时有十个负变量。
用来标记负变量的是一个四维或五维多项式空间的二次外幂；四维、五维指这个多项式空间，不能当成负变量的数目。

在最低的二次层，原系数能看到的恰是外乘为零的部分 $K$，漏掉的是该多项式空间的四次外幂。
更强的是，每个四次及以上的偶形式级数都已完整属于实际像。
因此实际像正好由常数、$K$ 中的二次项，以及任意四次以上偶尾项构成。
这个陈述包括无限形式级数，不只包括多项式或每个有限阶截断。

相对于正规化，次数十的实际像只缺一个二次方向，次数十二只缺五个。
这个差异是有限长的模，不是环商。实际像中全部零常数项函数恰好组成这对纤维环的导子；
模掉这个共同理想后，实际像只剩常数，正规化则多出上述一维或五维空间，而且新增部分的任意两个元素相乘为零。
$B_0$ 是 $A_0$ 的有限正规化，但“正规化”不等于光滑：这里的偶次不变量环本身仍有商奇点。

证明。必须先使用真实正参数。它们可能已经带有负变量的二次项，所以不能只在旧图里删掉正坐标。
让真实参数成为正形式坐标以后，负变量保持不变，才得到实际的偶级数纤维。
原系数一侧取的是到这个纤维的像，其核是实际理想的收缩；不能直接用原环除以同名参数代替。
这是定义 124.4 及命题 125.1 的内容。

接着，每个系数的正向一次项和负向二次项必须成对处理。用所选枢轴消去正向项时，也要减去这些枢轴所带的
二次项。040 的完整耦合像经过命题 126.1 的实际商映射，恰好留下 $K$。
所以这里得到的二次函数确实来自原系数，而非较大不变量环中人为加入的函数。

高阶部分由一个低维外代数事实控制。把二重外积的基变量看成边，共享端点的两条边相乘已经在 $K$ 中。
四条边若能配成两组相交边，就直接是两个可见二次函数的乘积；不能直接配对的情形，在四或五个基指标内只能留下
一条孤立边和另外三条边。恒等式 (127.5) 把它重新写成两组可见二次函数的乘积。
于是所有四次项都能取得。再高的偶次项中，任意三条边必有两条共享端点，逐次提出这一对，便得到全部更高偶次项。

真实二次函数起初可以带未知高阶尾项，这不妨碍结论。先用它们的乘积消去目标级数的四次误差，再消去六次误差，
不断继续。第 $r$ 次修正属于实际像极大理想的 $r$ 次幂。有限正规化保证实际像是完备局部环，并在正规化纤维中闭；
因此全部修正真正收敛在实际像中。于是高阶尾项全部恢复，二次代表的尾项也可减掉，得到定理 127.1 的完整环等式。
推论 128.1 随即给出一维、五维缺失模和精确导子。

关于正规化仍有奇点，按各变量指数的奇偶性归组，$F[[v]]$ 是 $F[[v_1^2,\ldots,v_b^2]]$ 的有限模，
故也是 $B_0$ 的有限模。因此 $\dim B_0=\dim F[[v]]=b$，而 (125.9) 给其余切空间维数为 $b(b+1)/2$。
这里 $b=6$ 或 $10$，后者严格大于前者，故这个局部环不正则。

最后要保留结论的层次。更换实际正参数可能切出不同的纤维；每组满足独立条件的选择都有上述标准型，
但并没有因此获得它们在整个原系数芽中的典范同一。负坐标变化须连同 $K$ 的线性识别一起输运。
本结论没有给完整原系数芽作乘积分解，也没有计算其完整导子或全局导子。

当多项式空间维数达到六时，命题 130.1 的明确线性读数消去所有二次可见类的两两乘积，却不消去一个具体四次项。
所以同一乘积办法确实不能继续使用。这不说明高维实际系数必然缺少该项：原系数还可能通过新的四次关系提升补入它。
这项高维实际义务仍未解决。以上结论也不提供全局次数、算术标签、物理实现、算法或最小性结论。证毕。

## 追加锚（本行以下为增补区）

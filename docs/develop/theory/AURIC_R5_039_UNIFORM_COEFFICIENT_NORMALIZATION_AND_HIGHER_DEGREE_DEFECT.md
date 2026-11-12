# 统一原系数像的正规化、光滑判据与高次二阶缺陷

## 111. 原域系数线、统一开集与带标签商图

**定义 111.1（固定原域与系数层）。** 固定特征零域 $F$、实际可分域扩张 $D/F$，以及整数 $m\ge5$，其中 $[D:F]=2m$。固定非零体积形式 $\nu:\det_F D\to F$。对 $m$ 维实际子空间 $C\subset D$ 的包含帧 $B$，定义

$$
P_B(x)=\nu\bigl(\det[B,M_xB]\bigr),\qquad
C^2=\operatorname{span}_F\{cd:c,d\in C\}.
\tag{111.1}
$$

这里 $M_x$ 是同一个原 $D$ 的乘法算子。换帧 $B\mapsto Bg$ 和换体积 $\nu\mapsto a\nu$ 分别给

$$
P_{Bg}=(\det g)^2P_B,\qquad P_B^{a\nu}=aP_B^\nu.
\tag{111.2}
$$

不选体积时，这是 Grassmannian $G=\operatorname{Gr}_F(m,D)$ 上从 $(\det\mathcal S)^{\otimes2}$ 到 $\det D\otimes\operatorname{Sym}^m(D^\vee)$ 的丛映射；选体积只把公共行列式线平凡化。因此 $[P_C]$ 是原 $F$ 上的射影系数点。沿用 [033，定义 81.1](https://github.com/the-omega-institute/trureturing/blob/974984733cb1d619221ff97000612a9194bc8828/docs/develop/theory/AURIC_R5_033_ALL_DEGREE_ARITHMETIC_POSITIVE_CERTIFICATES.md) 的内在系数空间 $H_D$、映射 $\phi:G\dashrightarrow\mathbb P(H_D)$ 与约化闭包 $\Gamma_D$。该引用承担 $P_C\in H_D$、原点系数闭包几何整等既有结论。

取有限 Galois 分裂域 $K/F$，令 $\Omega=\operatorname{Hom}_F(D,K)$，暂取一个全序，将其写成 $1,\ldots,2m$。分裂幂等元为 $e_\omega$，置 $\alpha=\nu_K(e_1\wedge\cdots\wedge e_{2m})$。若 $p_I$ 是分裂包含帧的递增行子式，$\epsilon_I$ 是行序列 $(I^c,I)$ 相对于 $\Omega$ 的符号，则原多项式在分裂变量中的系数是

$$
P_C(x)=\sum_{|I|=m}c_Ix_I,\qquad
c_I=\alpha\epsilon_Ip_Ip_{I^c},\qquad
x_I=\prod_{i\in I}x_i.
\tag{111.3}
$$

所有标签均为原嵌入标签。令 $U\subset G$ 为所有 $p_I\ne0$ 的统一开集；令 $\mathcal T\subset\mathbb P(H_D)$ 为分裂后所有 $c_I\ne0$ 的开集；令 $\Gamma_D^u=\Gamma_D\cap\mathcal T$。这些开集在 $F$ 上定义：各因子的积在 Galois 作用下只差非零常数，故其零集下降。

$U$ 非空：原域本原元的前 $m$ 个幂给 Vandermonde 帧，任意 $m$ 行独立。分裂后的 $\mathcal T$ 是射影主开集 $D_+(\prod_Ic_I)$，故仿射；仿射性下降到 $F$。以下闭像层因而也可由仿射环同态的像计算。

“系数像层”具体指 $\mathcal T$ 上自然映射

$$
\mathcal O_{\mathcal T}\longrightarrow
(\phi|_U)_*\mathcal O_U
\tag{111.4}
$$

的像，等价地由其核定义的闭像。以下证明这个闭像正是 $\Gamma_D^u$，而非另造的矩阵系数像。

**命题 111.2（统一原商及其实际下降转移）。** 令

$$
T_D=(\operatorname{Res}_{D/F}\mathbb G_m)/\mathbb G_m.
$$

$U/T_D$ 存在为光滑仿射 $F$-概形 $X_D$。记迹正交补诱导的 Gale 对合为 $\iota$。它在 $X_D$ 上定义。选分裂标签后，$X_{D,K}$ 有以下坐标环表示：

$$
R_K=K[z_{ji}:2\le j,i\le m]
 [\,\det Z[J,I]^{-1}:|J|=|I|\,],
\qquad z_{1i}=z_{j1}=1.
\tag{111.5}
$$

这里只反演非空方形子式，已为常数的子式无须重复。每一张选定 $E$、锚行和锚列的图是几何商图；它本身无需 Galois 不变。其转移、系数转移及扩底关系如下。

证明。对一个 $m$ 元集 $E$ 及其补集分别排序，将统一帧列归一化为

$$
V_E=\begin{pmatrix}I_m\\A\end{pmatrix}.
$$

统一性等价于 $A$ 的每个方形子式非零。分裂有效环面作用为 $A\mapsto LAM^{-1}$，其中 $L,M$ 对角，共同标量的作用平凡。取锚 $(1,1)$，定义

$$
z_{ji}=\frac{a_{ji}a_{11}}{a_{j1}a_{1i}},\qquad
Z=\operatorname{diag}(a_{11}/a_{j1})\,
 A\,\operatorname{diag}(1/a_{1i}).
\tag{111.6}
$$

每个轨道恰有一个第一行、第一列全为一的代表。确实，若两个这样的代表由行列缩放相关，第一行和第一列先强制所有缩放参数只剩共同标量，继而强制两个代表相等。原 $a_{j1},a_{1i}$ 中除重复的 $a_{11}$ 外的 $2m-1$ 个单位给出沿轨道的自由参数；(111.6) 及其逆式把整个统一 $A$ 图写成 (111.5) 的谱与分裂有效环面的乘积。因此这是概形意义的自由几何商，不只是轨道集合。

若改用基行集 $E'$，先按新行序取

$$
V_{E'}=V_E(V_E[E',:])^{-1},
\tag{111.7}
$$

再将 $E'$ 排在前面，取后块 $A'$，最后应用 (111.6)，其中锚可另选。所有逆矩阵分母都是已反演的最大子式；新锚的分母也非零。这给出各商图之间的正则同构，反向使用 $E$，三图复合由同一个帧换基恒等式保证。

更具体地，$\sigma\in\operatorname{Gal}(K/F)$ 在标签上给置换 $\pi$。商图的半线性下降转移是：对 $V_E$ 的系数施 $\sigma$、将其行依 $\pi$ 重标，取新基行 $\pi E$，随后执行 (111.7) 和新的锚归一化。若仍要用原 $E$ 图表达，则再执行一次从 $\pi E$ 到 $E$ 的 (111.7)。这给出了条目上的实际有理式，而非只指定一个等变性质。上述正则性和复合恒等式给仿射 Galois 下降，所得 $X_D$ 的扩底就是 (111.5)。商映射也下降；环面挠子关系在分裂域上为乘积关系，故由忠实平坦下降在 $F$ 上成立。光滑性和仿射性同样下降。

在同一个 $E$ 图中也可将这个转移一次写完。令 $\Pi_\pi$ 把旧标签行 $s$ 送到新标签行 $\pi s$，置

$$
W_\sigma=\Pi_\pi\sigma\!\begin{pmatrix}I_m\\Z\end{pmatrix},
\qquad
A_\sigma=\bigl(W_\sigma(W_\sigma[E,:])^{-1}\bigr)[E^c,:].
$$

则转移后的第 $(j,i)$ 个归一化坐标严格为

$$
(z_\sigma)_{ji}=
\frac{(A_\sigma)_{ji}(A_\sigma)_{11}}
 {(A_\sigma)_{j1}(A_\sigma)_{1i}}.
\tag{111.7a}
$$

这包含列换基、标签重排和锚归一化三个步骤；不同 $\sigma$ 的复合正是半线性 Galois 群律。

为写出系数的下降，令 $s_\pi(I)$ 为序列 $\pi(I)$ 重新递增排序的符号。原帧满足

$$
\sigma\alpha=\operatorname{sgn}(\pi)\alpha,
\quad \sigma p_I=s_\pi(I)p_{\pi I},
\quad
\epsilon_{\pi I}=\operatorname{sgn}(\pi)
 s_\pi(I)s_\pi(I^c)\epsilon_I.
$$

故原系数满足 $\sigma c_I=c_{\pi I}$。以 $E_0$ 作系数参考集，写 $t_I^{E_0}=c_I/c_{E_0}$，则

$$
\sigma(t_I^{E_0})=t_{\pi I}^{\pi E_0}
=\frac{t_{\pi I}^{E_0}}{t_{\pi E_0}^{E_0}}.
\tag{111.8}
$$

换帧、换体积造成的公共行列式线因子均在比值中消去。(111.7) 与 (111.8) 相容，因为二者都由 (111.3) 计算同一帧的系数。特别地，指定一个 $E_0$ 图或指定前若干标签不构成一张独立的原 $F$ 图。

迹正交补满足 $(tC)^\perp=t^{-1}C^\perp$，故在商上诱导 $\iota$。在 $A$ 图上，正交补由

$$
A^\#=-A^{-\mathsf T}
\tag{111.9}
$$

表示，随后执行锚归一化。Jacobi 互补子式公式使 (111.3) 的所有比值不变，故系数映射经 Gale 商分解。互补子式描述亦见 Howard–Millson，[The Chevalley Involution and a Duality of Weight Varieties，math/0409260v2，Theorem 1.4 及 Theorem 1.12](https://arxiv.org/abs/math/0409260v2)；这里用的是同一带符号互补操作。

最后明确像与扩底。$F$ 无限，$G$ 的一张原域标准大胞腔是仿射空间。其 $F$ 点在任何扩域上几何稠密：扩域系数多项式若在所有 $F$ 坐标上为零，逐变量使用一元根数界即为零。乘上非空开集的定义多项式得到开集版本。因而 $U(F)$ 几何稠密，$\phi(U(F))$ 的闭包与 $\phi(U_K)$ 的闭包相同；$U$ 又稠密于映射定义域，故这个闭包就是 $\Gamma_D\times_FK$。在系数环面图上，闭像的环为

$$
S_K=K[(c_I/c_{E_0})^{\pm1}:|I|=m]\subset R_K.
\tag{111.10}
$$

这是坐标环同态的像。平坦扩底保核与像；故若 $S_F$ 是 (111.4) 的闭像环，$R_F=\mathcal O(X_D)$，则

$$
S_F\otimes_FK=S_K,\qquad R_F\otimes_FK=R_K.
\tag{111.11}
$$

闭像在 $\mathcal T$ 中等于闭包与 $\mathcal T$ 的交，故 $S_F=\mathcal O(\Gamma_D^u)$。这些等式也可再扩到任意代数闭域。$\square$

## 112. 每个方形子式的范数与有限性

**定理 112.1（带全部归一化因子的整性）。** 对 (111.5)、(111.10) 的精确原系数环，有 $S_K\subset R_K$ 有限。具体地，$R_K=S_K[z_{ji}:2\le j,i\le m]$；每个 $z_{ji}$ 满足一个由原带符号互补系数比值给出的首一二次式。这一结论控制 (111.5) 中所有被反演的子式。

证明。以下子式的行列指标均递增；$I,J\subset\{1,\ldots,m\}$ 且 $|I|=|J|=k$。记 $\Delta_{J,I}=\det A[J,I]$，$\Delta=\det A$，空子式为一。对原分裂变量 $(x_1,\ldots,x_m,y_1,\ldots,y_m)$，令

$$
g_A(x,y)=\frac{P_{[I;A]}(x,y)}{[y_1\cdots y_m]P_{[I;A]}}
=\det(D_y-AD_xA^{-1}).
$$

体积因子在这个商中消失。由 Cauchy–Binet 与 Jacobi 公式，实际系数比值

$$
\begin{aligned}
q_{J,I}&=[x_Iy_{J^c}]g_A\\
&=(-1)^k\Delta_{J,I}\det A^{-1}[I,J]\\
&=(-1)^{k+\sum I+\sum J}
\frac{\Delta_{J,I}\Delta_{J^c,I^c}}{\Delta}
\ \in S_K^\times .
\end{aligned}
\tag{112.1}
$$

它就是 $c_{I\cup(m+J^c)}/c_{m+\{1,\ldots,m\}}$，保持了 (111.3) 的原符号。以 $q_{ji}$ 简记 $q_{\{j\},\{i\}}$。对一个商图函数 $h$ 写 $N(h)=h\iota(h)$。计算范数时可暂对未归一化的 $A$ 与 $A^\#$ 相乘；对 $\Delta_{J,I}$ 有

$$
\Delta_{J,I}(A)\Delta_{J,I}(A^\#)=q_{J,I}.
\tag{112.2}
$$

单个未归一化子式不是商函数；(112.2) 是计算随后的平衡比值所用的恒等式，不能将它单独解释成 $R_K$ 中某个非平衡函数的范数。

令 $h_{J,I}=\det Z[J,I]$。行列归一化逐项给出

$$
h_{J,I}=
\frac{a_{11}^{k}\Delta_{J,I}}
 {\prod_{j\in J}a_{j1}\prod_{i\in I}a_{1i}},
\qquad
N(h_{J,I})=
\frac{q_{11}^{k}q_{J,I}}
 {\prod_{j\in J}q_{j1}\prod_{i\in I}q_{1i}}
\in S_K^\times.
\tag{112.3}
$$

公式包括锚行、锚列、全行全列以及空子式的情形；重复出现的 $a_{11}$、$q_{11}$ 按所示重数计算，没有省略因子。

再取 $j<\ell$、$i<k$，定义矩形比值

$$
r=\frac{a_{ji}a_{\ell k}}{a_{jk}a_{\ell i}}.
$$

它在行列缩放下不变。所有条目及二阶子式都是单位，故 $r,1-r$ 都是 $R_K$ 的单位，且

$$
N(r)=\frac{q_{ji}q_{\ell k}}{q_{jk}q_{\ell i}},
\qquad
N(1-r)=\frac{q_{\{j,\ell\},\{i,k\}}}{q_{jk}q_{\ell i}}
\quad\in S_K^\times.
\tag{112.4}
$$

后一式来自 $1-r=-\Delta_{\{j,\ell\},\{i,k\}}/(a_{jk}a_{\ell i})$；负号在两因子范数中抵消。颠倒行列顺序或取倒数只改变表示，不改变这两项属于 $S_K^\times$ 的结论。展开 $N(1-r)$ 得

$$
r+\iota r=1+N(r)-N(1-r),
\quad
r^2-\bigl(1+N(r)-N(1-r)\bigr)r+N(r)=0.
\tag{112.5}
$$

特别地，$z_{ji}$ 是使用锚行、锚列的矩形比值，所以满足 (112.5)，且 $\iota z_{ji}\in S_K[z_{ji}]$。令 $R'=S_K[z_{ji}:j,i\ge2]$，它由有限个二次整元生成，是有限 $S_K$ 模。

每个 $\iota h_{J,I}$ 都是同一个行列式多项式在 $\iota z_{ji}$ 上的取值，因而属于 $R'$。由 (112.3)，

$$
h_{J,I}^{-1}=
\frac{\iota h_{J,I}}{N(h_{J,I})}\in R'.
\tag{112.6}
$$

这证明 (111.5) 的所有生成元都在 $R'$ 中，故 $R_K=R'$，并完成有限性。Lin–Sturmfels，[Polynomial relations among principal minors of a $4\times4$-matrix，0812.0601v3，Proposition 7](https://arxiv.org/abs/0812.0601v3) 给出了任意大小泛矩阵的循环代数对主子式代数的整性；这里的证明直接使用 (112.1)–(112.6)，不把那个泛矩阵代数替换为原系数环。$\square$

## 113. 点纤维、饱和与精确正规化

**定理 113.1（统一系数像的原域正规化）。** 令 $B_F=R_F^\iota$。自然态射

$$
\operatorname{Spec}B_F\longrightarrow\Gamma_D^u
\tag{113.1}
$$

有限、双有理，并且是 $\Gamma_D^u$ 的正规化。扩底后 $B_K=R_K^\iota$ 是 $S_K$ 在其分式域中的精确整闭包。每个几何纤维的约化支撑恰有一点。统一开集对于系数映射饱和；在目标 $\mathcal T$ 中，不存在还须由非统一窗口补入的像点。特别地，$\dim\Gamma_D=(m-1)^2$。

证明。先扩到代数闭域 $k\supset K$，仍沿用原标签。对于两个统一几何点，将帧写成 $[I;A]$ 与 $[I;A']$。原射影系数相等恰好给 $g_A=g_{A'}$。此处只消费 [023，§44，(44.17)–(44.21)](https://github.com/the-omega-institute/trureturing/blob/918031afd4e16023fe368df1eeb747b593b6bb4a/docs/develop/theory/AURIC_R5_023_CHARACTERISTIC_ZERO_HALF_WINDOW_RECOVERY.md) 的分裂主子式计算：$g_A$ 的系数是

$$
C_A=\begin{pmatrix}0&A^{-1}\\A&0\end{pmatrix}
$$

的全部对应主子式；统一性使 $A,A^{-1}$ 条目非零，并使每个大小在 $2$ 至 $2m-2$ 之间的切口具有跨块秩至少二。不可约无切口主子式重建遂给

$$
A'=LAM^{-1}\quad\text{或}\quad A'=LA^{-\mathsf T}M^{-1},
\tag{113.2}
$$

其中 $L,M$ 可逆对角。该重建输入的原文为 Al Ahmadieh，[The Fiber of the principal minor map，2309.00806v2，Theorem 4.1 的无切口充分方向](https://arxiv.org/html/2309.00806v2)，其充分方向归于 Loewy，*Principal minors and diagonal similarity of matrices*，Linear Algebra and its Applications 78，23–64，Theorem 1。这里没有使用 023 从商支持返回原域时的域可逆性论证；分裂代数 $k^{2m}$ 不是域，也未被当作域。

(113.2) 精确说明 $X_{D,k}\to\operatorname{Spec}S_k$ 的点纤维是一条 Gale 轨道。有限群商 $\operatorname{Spec}R_k\to\operatorname{Spec}(R_k^\iota)$ 的几何点也是有限群轨道：若两个有限轨道不相交，可先用仿射函数在两个有限集合上分别取零与一，再对群取平均，得到分离它们的不变量。因此 $\operatorname{Spec}B_k\to\operatorname{Spec}S_k$ 的几何点纤维恰为单点。

定理 112.1 给 $R_k$ 对 $S_k$ 有限。$S_k$ 是有限型代数，故 Noether；其子模 $B_k\subset R_k$ 也是有限 $S_k$ 模。$R_k$ 是光滑整环的局部化，所以正规。不变量环亦正规：若 $w\in\operatorname{Frac}B_k$ 对 $B_k$ 整，则它对 $R_k$ 整，故 $w\in R_k$；又 $w$ 在分式域中不变，故 $w\in B_k$。

还须证明双有理。有限占优映射给有限分式域扩张 $\operatorname{Frac}S_k\subset\operatorname{Frac}B_k$。特征零使它可分。若次数为 $n>1$，原始元的最小多项式在反演判别式并缩小非空目标开集后给 $n$ 个不同几何点；有限扩张在再缩小后与这个生成代数一致，因为剩余有限多个生成元的分母可同时清除。于是一般几何纤维有 $n$ 点，与单点纤维矛盾。因此次数为一。若 $w$ 对 $S_k$ 整且在这个共同分式域中，则它亦对 $B_k$ 整，故 $w\in B_k$；反向 $B_k$ 的元素因有限性都对 $S_k$ 整。这正是精确整闭包断言。

饱和性不由点重建代替。对映射定义域中的任意几何窗口，由 (111.3) 有

$$
\phi^{-1}(\mathcal T)=U.
\tag{113.3}
$$

因为所有 $p_Ip_{I^c}$ 非零当且仅当每个 $p_I$ 非零。另一方面，整扩张 $S_k\subset R_k$ 的谱映射满射且闭；故 $\phi(U_k)$ 在 $\mathcal T_k$ 中已经是闭集。它又在 $\Gamma_k\cap\mathcal T_k$ 中稠密，由命题 111.2 得两者相等。这同时证明：即使把系数像理解为全部原实际点的约化闭包，目标中全系数非零的极限也已由统一商覆盖。这个论证不分类 $\mathcal T$ 之外的边界，也不要求对映射的未定义点作边界分类。

最后下降全部环论结论。(111.7)–(111.8) 给出的原 $F$ 环映射满足 (111.11)。平均算子 $(1+\iota)/2$ 是投影，故

$$
B_F\otimes_FK=(R_F\otimes_FK)^\iota=B_K.
\tag{113.4}
$$

有限模性质经忠实平坦扩底可检验，故 $R_F$、$B_F$ 均对 $S_F$ 有限。$R_F$ 光滑，因而正规；前述不变量整闭证明同样给 $B_F$ 正规。有限泛秩在域扩张后仍为同一数，分裂后的泛秩为一，故原域亦为一，即 (113.1) 双有理。整闭包的同一包含论证给出 $B_F$ 的精确性。等式 (113.3)、闭像等式和维数也由忠实平坦下降保留。$X_D$ 维数为 $(m-1)^2$，两个有限映射均不改变维数，遂得最后的公式。$\square$

## 114. 非固定点处的全矩形传播与局部环相等

**定理 114.1（非固定统一轨道上的精确局部桥）。** 在 $X_D$ 的非 Gale 固定轨道上，(113.1) 是局部同构，且对应的原系数像点光滑。具体地，系数局部环等于 Gale 商的局部环；扩到代数闭域后，它们的完成环同构于 $X_D$ 对应点的完成环，$X_D$ 到 Gale 商的局部映射为 étale。结论不假定任意一个预先选定的矩形比值与其 Gale 像不同。

证明。先在代数闭域 $k$ 上，取非固定点 $x\in X_D(k)$，令 $v\in T_xX_D$ 被全部系数比值的微分消去。任一矩形比值 $r$ 的二次式 (112.5) 的系数属于 $S_k$，故微分后得到

$$
\bigl(r(x)-(\iota r)(x)\bigr)\,dr(v)=0.
\tag{114.1}
$$

只要两个值不同，就有 $dr(v)=0$。下面证明这足以消去每个归一化条目的微分。

因为全部内条目 $z_{ji}$ 是 $X_D$ 的坐标生成元，$x\ne\iota x$ 意味着至少有一个内条目 $a=z_{ji}$ 满足 $a(x)\ne(\iota a)(x)$。它本身是锚矩形比值，所以 $da(v)=0$。第一行和第一列都是常数，其微分恒为零。

先取与 $a$ 同行的另一内条目 $b=z_{jk}$。若 $b(x)\ne(\iota b)(x)$，直接由 (114.1) 得 $db(v)=0$。若两值相等，则单位 $b/a$ 的两个 Gale 值不同；$b/a$ 是使用锚行的矩形比值。于是 $d(b/a)(v)=0$，结合 $da(v)=0$ 仍得 $db(v)=0$。同列条目使用锚列的比值，证明完全相同。这里也覆盖“条目值自身固定，但与已知非固定条目之比不固定”的情形。

最后取与 $a$ 不同行也不同列的内条目 $d=z_{\ell k}$，令另外两角为 $b=z_{jk}$、$c=z_{\ell i}$。前一步已经给出 $db(v)=dc(v)=0$。若 $d$ 的两个 Gale 值不同，直接结束。否则 $d$ 的值固定。若 $b$ 的值非固定，则 $d/b$ 是同列矩形比值且值非固定，从其微分及 $db(v)=0$ 得 $dd(v)=0$。若 $c$ 的值非固定，用同一行的 $d/c$。余下情形是 $b,c,d$ 的值都固定，而 $a$ 的值非固定；于是

$$
r=\frac{ad}{bc}
$$

的值非固定。由 (114.1) 及 $da(v)=db(v)=dc(v)=0$，又因全部条目为单位，得到 $dd(v)=0$。这穷尽共享行、共享列、自身固定的条目和对角位置四类情形。因此所有内坐标微分都为零，即 $v=0$。

现在补足有限局部环论。记 $y\in\operatorname{Spec}B_k$、$p\in\operatorname{Spec}S_k$ 为像点。自由的二元群轨道上 $X_D\to\operatorname{Spec}B_k$ 是 étale。也可直接看完成化：$y$ 上方的两个局部完成环组成直积，$\iota$ 交换两因子；其不变量同构于其中任一因子。平均算子保证完成化与取不变量交换。这给 $T_xX_D\simeq T_y\operatorname{Spec}B_k$。上一段的零核证明因此说明

$$
\mathfrak m_p/\mathfrak m_p^2\longrightarrow
\mathfrak m_y/\mathfrak m_y^2
\tag{114.2}
$$

满射。

置 $A=(S_k)_p$。有限 $A$ 代数 $B_k\otimes_{S_k}A$ 的极大理想恰对应 $p$ 上方的点；定理 113.1 给唯一的 $y$，所以这个代数已经是局部环 $B=(B_k)_y$，且是有限 $A$ 模。两边剩余域都是 $k$，不是仅有剩余域的一个未确定扩张。由 (114.2)，

$$
\mathfrak m_B=\mathfrak m_A B+\mathfrak m_B^2.
$$

对有限 $B$ 模 $\mathfrak m_B/\mathfrak m_A B$ 使用第一次 Nakayama 引理，得

$$
\mathfrak m_B=\mathfrak m_A B.
\tag{114.3}
$$

剩余域相等给 $B=A+\mathfrak m_B=A+\mathfrak m_A B$。因此有限 $A$ 模 $B/A$ 满足 $B/A=\mathfrak m_A(B/A)$；第二次 Nakayama 引理给 $B/A=0$。故 $A=B$。这个证明使用的是余切满射、剩余域相等和有限性，而不是点双射。

固定点的像在有限映射下为闭集。在其补集上，上述等式对全部几何闭点成立；有限模 $B/S$ 的支撑若非空必含闭点，故它在这个补集上为零。因此局部同构是整个非固定开集上的断言，并经 (111.11)、(113.4) 忠实平坦下降。$B$ 的这些局部环光滑，故系数局部环光滑。$\square$

## 115. 原乘法、固定正规化与内在光滑判据

**定理 115.1（原域平方缺秩、固定性与精确光滑条件）。** 对每个实际统一 $C\subset D$，以下条件等价：

$$
C^2\ne D;
\qquad
\exists\lambda\in D^\times:\lambda C=C^\perp;
\qquad
x_C\in X_D(F)\text{ 为 Gale 固定点}.
\tag{115.1}
$$

第一种情形中，$\dim_F C^2=2m-1$，乘数空间恰为一条原 $F$ 直线。令

$$
a=\frac{m(m-1)}2,\qquad
b=\frac{(m-1)(m-2)}2.
\tag{115.2}
$$

固定点处的正规化完成局部环为

$$
\widehat{(B_F)_{y_C}}\simeq
F[[u_1,\ldots,u_a,v_1,\ldots,v_b]]^{\,v\mapsto-v}.
\tag{115.3}
$$

特别地，对原系数像本身有精确判据

$$
\boxed{\quad [P_C]\in(\Gamma_D)_{\mathrm{sm}}(F)
\quad\Longleftrightarrow\quad C^2=D.\quad}
\tag{115.4}
$$

(115.3) 只描述正规化；并未将固定点的系数局部环预先认作这个环。

证明。乘法映射及其迹对偶为

$$
\mu_C:\operatorname{Sym}^2_F C\longrightarrow D,
\qquad
\mu_C^\vee:D\longrightarrow(\operatorname{Sym}^2_F C)^\vee,
\quad
\lambda\longmapsto\bigl(cd\mapsto\operatorname{Tr}_{D/F}(\lambda cd)\bigr).
\tag{115.5}
$$

迹配对非退化，故 $\ker\mu_C^\vee=(C^2)^\perp$。分裂后，核向量 $\lambda=(\lambda_s)$ 给指定 $2m$ 行点上的二次评价关系

$$
\sum_s\lambda_s P(c_s)=0
\quad\text{对所有齐次二次式 }P.
\tag{115.6}
$$

每个非零关系都有全支撑。否则其支撑 $S$ 至多有 $2m-1$ 个标签。固定其中一个 $s$，把 $S\setminus\{s\}$ 分成大小各至多 $m-1$ 的两组。统一性保证每组和 $c_s$ 一起线性独立，故分别存在一个线性式，消去该组但在 $c_s$ 上非零。两线性式的乘积在支撑上只保留 $s$，代入 (115.6) 强制 $\lambda_s=0$，矛盾。若关系空间维数至少二，可以用两条独立关系消去任意指定坐标，得到非零但非全支撑的关系；所以核维数至多一。

一条非零关系的全部 $\lambda_s$ 非零，故分裂对角乘法可逆，并使 $\lambda C_K\subset C_K^\perp$，等维遂为相等。反向，Gale 固定的统一轨道按几何商的轨道描述给这样的可逆对角乘数，故给非零关系。核与域扩张交换，因而几何核非零就意味着原 $\ker\mu_C^\vee$ 非零。取其中实际 $0\ne\lambda\in D$；原 $D$ 是域，故 $\lambda\in D^\times$，且 $\lambda C=C^\perp$。这下降的是有限维线性核中的实际向量，不是断言任意选出的分裂对角向量已经逐项来自原域。核维数一与 $\dim C^2=2m-1$ 也同时下降。这证明 (115.1)。稳定点集的自伴随性与二次条件失效的经典对应见 Eisenbud–Popescu，[The Projective Geometry of the Gale Transform，math/9807127v1，Theorem 7.1(c)、Corollary 7.4](https://arxiv.org/abs/math/9807127v1)；上述推导明确给出同一个原域中的乘数。

固定实际 $\lambda$，在原 $D$ 上用非退化对称形式

$$
\langle s,t\rangle_\lambda=\operatorname{Tr}_{D/F}(\lambda st).
\tag{115.7}
$$

$C$ 是最大各向同性子空间。可在 $F$ 上选择各向同性补空间 $C'$：先选与 $C$ 对偶的任意补基，再减去其 Gram 矩阵的一半所对应的 $C$ 分量，即使补基两两内积为零。在这组双曲基下，图空间的矩阵为 $Y:C\to C'$；相对于 (115.7) 取正交补将其变为 $-Y^{\mathsf T}$。这个操作等于原迹正交补后再乘 $\lambda^{-1}$，所以在 $X_D$ 上诱导的正是 $\iota$。

因此 Grassmann 切空间的正特征部分是交错矩阵，维数 $m(m-1)/2$；负特征部分是对称矩阵，维数 $m(m+1)/2$。有效环面轨道维数为 $2m-1$，由命题 111.2 的自由性得到。它全在负空间，因为正交补将乘法 $t$ 变为 $t^{-1}$。模掉这些方向后，$T_{x_C}X_D$ 的正、负维数分别为 $a,b$。

这一负空间的对偶有内在描述。环面无穷小方向 $h\in D$ 对应对称形式

$$
(c,d)\longmapsto\operatorname{Tr}_{D/F}(\lambda hcd).
$$

它们的正交核正好是 $\ker\mu_C$。因此

$$
(T_{x_C}X_D)^-\simeq(\ker\mu_C)^\vee,
\qquad
\bigl((T_{x_C}X_D)^-\bigr)^\vee\simeq\ker\mu_C.
\tag{115.8}
$$

这里 $\ker\mu_C$ 是负切空间的余切，不是负切空间本身。

$X_D$ 在实际 $F$ 点 $x_C$ 光滑。固定轨道只有这个上方点，$x_C$ 与 $y_C$ 的剩余域都为 $F$；将有限映射 $X_D\to\operatorname{Spec}B_F$ 局部化于 $y_C$ 后得到的源环就是 $x_C$ 的局部环。其极大理想的余切空间在 $F$ 上分成两个特征空间；任取相应基的局部提升 $w$，用 $(w+\iota w)/2$ 或 $(w-\iota w)/2$ 替换，得到分别不变或反变的提升。它们仍是正则参数，故完成环同构于 $F[[u,v]]$，对合恰为 $(u,v)\mapsto(u,-v)$。平均以 $2$ 在实际 $F$ 中可逆为依据，不需要扩大剩余域。平均是有限模上的投影，因而与平坦完成化交换，给 (115.3)。

环 (115.3) 的极大理想模平方由

$$
u_i\ (1\le i\le a),\qquad v_jv_k\ (1\le j\le k\le b)
\tag{115.9}
$$

给一组基。证明是按单项式分次：不变量只含偶数个 $v$；除一次 $u$ 和二次 $v$ 外，每个非常数不变量单项式都可分成两个非常数不变量。所列低次单项式又线性独立。因此正规化的维数为 $a+b$，嵌入维数为 $a+b(b+1)/2$。$m\ge5$ 给 $b>1$，所以正规化在固定点奇异。

若原系数点固定且光滑，其局部环为正则局部环，因而整闭；有限双有理正规化在此处就必须相等。这与刚证明的正规化奇异矛盾。故固定原系数点不光滑。非固定时用定理 114.1，得到光滑。结合 (115.1)，即得 (115.4)，全程未假定固定点处局部环相等。$\square$

## 116. 连续幂原窗口的四根二阶缺陷

**定理 116.1（每个实际域中的连续幂非正规点）。** 取同一个 $D/F$ 的任一本原元 $\theta$，最小多项式为首一 $f(T)$，令

$$
C=\operatorname{span}_F(1,\theta,\ldots,\theta^{m-1}).
\tag{116.1}
$$

它统一，且 $\lambda=1/f'(\theta)$ 满足 $\lambda C=C^\perp$。在 $p=[P_C]$、$y=y_C$ 处，原系数环到其正规化的余切映射有

$$
\dim_F\operatorname{coker}
\left(
\mathfrak m_{(S_F)_p}/\mathfrak m_{(S_F)_p}^2
\longrightarrow
\mathfrak m_{(B_F)_y}/\mathfrak m_{(B_F)_y}^2
\right)
\ \ge\ \binom{m-1}{4}.
\tag{116.2}
$$

所以该原系数局部环非正规，完成后与正规化完成环的包含仍严格。这里只给余切余核的下界，不断言等号或完整导子。

证明。扩到代数闭域 $k$，令 $\Lambda$ 为 $f$ 的 $2m$ 个互异根，标签仍为原嵌入。将 $C_k$ 认作 $k[T]_{<m}$，实际包含帧为

$$
E:P\longmapsto(P(s))_{s\in\Lambda}.
\tag{116.3}
$$

所有最大子式均为非零 Vandermonde 行列式，故窗口统一。乘积张成 $1,\theta,\ldots,\theta^{2m-2}$，维数为 $2m-1$。Lagrange 插值的最高次系数给

$$
\sum_{s\in\Lambda}\frac{g(s)}{f'(s)}=0
\qquad(\deg g\le2m-2).
\tag{116.4}
$$

因此实际 $1/f'(\theta)$ 在 $\ker\mu_C^\vee$ 中，且非零；定理 115.1 给所述乘数等式。

先精确识别负切空间。将 $\operatorname{Sym}^2 C_k$ 的元素表示为对称二元多项式 $Q(s,t)$，两个变量的次数都至多 $m-1$。属于 $\ker\mu_C$ 等价于 $Q(t,t)$ 在全部根上为零。它的次数至多 $2m-2$，所以这等价于多项式恒等式 $Q(t,t)=0$。于是唯一地写成

$$
Q(s,t)=(s-t)A(s,t),\qquad A(t,s)=-A(s,t),
\quad\deg_s A,\deg_t A\le m-2.
\tag{116.5}
$$

两个次数界由在另一个变量的多项式环上作除法得到。令 $V=k[T]_{\le m-2}$，用 $P\wedge Q\mapsto P(s)Q(t)-Q(s)P(t)$ 识别交错多项式，得到

$$
\ker\mu_{C,k}\simeq\bigwedge^2V,
\qquad
(T_{x_C}X_D)^-\simeq\bigwedge^2(V^*).
\tag{116.6}
$$

这保持了 (115.8) 中切与余切的对偶方向。

对不同根 $a,b$，在实际包含帧 (116.3) 的仿射邻域内取常方向

$$
H_{ab}(P)=
\frac{f'(a)e_aP(b)+f'(b)e_bP(a)}{a-b},
\qquad H_{ba}=-H_{ab}.
\tag{116.7}
$$

此邻域是 $\operatorname{Hom}_k(C_k,D_k)$ 中包含映射且各最大子式可逆的开集；以下微分都在这个实际帧处进行。相对于 (115.7)，该 Grassmann 切方向给对称形式

$$
(P,Q)\longmapsto
\frac{P(b)Q(a)+P(a)Q(b)}{a-b}.
\tag{116.8}
$$

故其商切类是负的。与 (116.5) 的余切元配对，得到 $2A(a,b)$；若 $\operatorname{ev}_a\in V^*$ 是根 $a$ 处的评价，则负切类正是

$$
[H_{ab}]=2\operatorname{ev}_a\wedge\operatorname{ev}_b.
\tag{116.9}
$$

现在说明二阶式为什么给正规化上的点导子。记 $\partial_{ab}$ 为包含帧仿射空间的常方向微分。对四个不同根，定义在帧 $E$ 处取值的算子

$$
L_{abcd}=
\partial_{ab}\partial_{cd}
-\partial_{ac}\partial_{bd}
+\partial_{ad}\partial_{bc}.
\tag{116.10}
$$

局部环 $(B_k)_y$ 的函数经 $U_k\to X_{D,k}\to\operatorname{Spec}B_k$ 拉回到上述帧开集。因为每个 $H_{ab}$ 的商切类负，而拉回的函数 Gale 不变，它们的所有 $\partial_{ab}$ 一阶导数均为零。对任意两个这样的局部函数 $g,h$，二阶乘法法则的交叉项因此逐项为零，给

$$
L_{abcd}(gh)=g(E)L_{abcd}(h)+h(E)L_{abcd}(g).
\tag{116.11}
$$

所有关系也被保持：一个在 $(B_k)_y$ 中为零的关系拉回后是在帧开集上恒为零的正则函数，常方向二阶微分仍为零。分母在 $E$ 非零，故局部化没有例外。因此 (116.10) 确实是 $(B_k)_y\to k$ 的点导子。

这个证明不把仿射帧的二阶微分偷换成商坐标中的纯 Hessian。具体地，若在双曲分解中 $H=EA_H+E'Y_H$、$K=EA_K+E'Y_K$，则帧 $E+tH+sK$ 的 Grassmann 图坐标是

$$
Y(t,s)=(tY_H+sY_K)(1+tA_H+sA_K)^{-1},
\quad
\partial_t\partial_sY(0,0)=-Y_HA_K-Y_KA_H.
\tag{116.12}
$$

继续换到环面横截面时还须对归一化映射求二阶导数。(116.10) 始终作用于真实拉回，故 (116.12) 及环面换图的加速度都已计入；它们可能给导子的固定线性部分。下面只用不受这些低阶修正影响的负二次符号证明非零，并直接在原帧上证明对系数的消去。

也可将完整修正写成坐标公式。取定理 117.1 的对合相容形式横截面，令 $\Psi$ 为从帧开集先到商、再到这张形式横截面的映射；第一步由 (111.6)–(111.7) 给出，第二步为切映射可逆的形式逆。写 $d\Psi(H)=(0,v_H)$，$\alpha_{H,K}=d^2\Psi(H,K)$。对任一商不变量 $g$，链式法则严格给

$$
\partial_H\partial_K(g\circ\Psi)
=\operatorname{Hess}_{V}g(v_H,v_K)
+d_Ug(\alpha_{H,K}^{+}).
\tag{116.12a}
$$

因此 (116.10) 在横截面上是三个负 Hessian 项加上固定一阶项，其后者系数为 $\alpha_{H_{ab},H_{cd}}^+-\alpha_{H_{ac},H_{bd}}^++\alpha_{H_{ad},H_{bc}}^+$。这里没有将这个加速度组合假定为零；原帧计算保留了它的全部贡献。

取完成环中反变参数 $v_1,\ldots,v_b$。点导子消去正规化极大理想的平方，因而唯一地连续延拓到完成环；这些参数的有限阶拉回亦可在帧处计算。在 $v_iv_j$ 上，二阶乘法法则仅保留两个一阶导数的乘积，任何加速度项都因 $v_i(E)=v_j(E)=0$ 消失。因此 $L_{abcd}$ 在负二次余切上的符号，与一个固定非零常数因子相差，为

$$
\begin{aligned}
W_{abcd}={}&
(e_a\wedge e_b)\odot(e_c\wedge e_d)
-(e_a\wedge e_c)\odot(e_b\wedge e_d)\\
&+(e_a\wedge e_d)\odot(e_b\wedge e_c),
\qquad e_s=\operatorname{ev}_s\in V^*.
\end{aligned}
\tag{116.13}
$$

这里 $\odot$ 表示对称二阶符号，按 Hessian 对 $v_iv_j$ 的配对约定理解；(116.9) 使公共因子在所有四元组中一致且非零。外乘映射 $\operatorname{Sym}^2(\bigwedge^2V^*)\to\bigwedge^4V^*$ 将 (116.13) 送到

$$
3e_a\wedge e_b\wedge e_c\wedge e_d.
\tag{116.14}
$$

特别地，当这四个评价独立时，点导子不为零。

还必须证明它消去每个原系数。固定任意 $m$ 元根集 $I$，令 $J=\Lambda\setminus I$，$F_I(T)=\prod_{i\in I}(T-i)$。记

$$
\ell_i(T)=\frac{F_I(T)}{(T-i)F_I'(i)}\quad(i\in I),
$$

它们是该子集上的插值基。令 $E_I$ 为 (116.3) 的 $I$ 行方阵。对任意两个常帧方向 $H,K$，在 $E$ 处有严格的二阶对数恒等式

$$
\partial_H\partial_K\log p_I
=-\operatorname{tr}(E_I^{-1}H_I E_I^{-1}K_I).
\tag{116.15}
$$

“对数”表示单位的形式对数：其二阶值为 $p_I^{-1}\partial_H\partial_Kp_I-p_I^{-2}(\partial_Hp_I)(\partial_Kp_I)$，不涉及收敛。

完整核对四根分拆。对于不交的根对 $\{u,v\}$、$\{w,z\}$，迹 (116.15) 的每个可能项由一个输出根 $r\in I\cap\{u,v\}$ 和一个输出根 $s\in I\cap\{w,z\}$ 索引。若 $r'$、$s'$ 是各自根对中的另一根，其插值因子为

$$
\ell_s(r')\ell_r(s').
\tag{116.16}
$$

若 $r'\in I$，它与另一个根对的 $s$ 不同，故第一个因子为零；若 $s'\in I$，第二个因子为零。因此一个非零迹项必须由两个跨越 $I,J$ 的根对产生。

这立即处理 $0+4$ 与 $1+3$ 的分拆：前者没有两个输出根，后者不能为两个不交根对同时提供输出根。$4+0$ 与 $3+1$ 同理由 (116.16) 处理。只有 $2+2$ 尚需计算。由于 (116.10) 对四个标签交错，重标后可设 $a,b\in I$、$c,d\in J$。$\partial_{ab}\partial_{cd}\log p_I$ 的迹为零。另两项去掉 (116.15) 的公共负号后分别为

$$
\begin{aligned}
T_1&=\frac{f'(a)f'(b)\ell_b(c)\ell_a(d)}{(a-c)(b-d)}
=\frac{F_J(a)F_J(b)F_I(c)F_I(d)}
 {(a-c)(b-d)(c-b)(d-a)},\\
T_2&=\frac{f'(a)f'(b)\ell_b(d)\ell_a(c)}{(a-d)(b-c)}
=\frac{F_J(a)F_J(b)F_I(c)F_I(d)}
 {(a-d)(b-c)(d-b)(c-a)}.
\end{aligned}
\tag{116.17}
$$

这里使用了 $f'(i)=F_I'(i)F_J(i)$。两个分母相等：把各自最后两个差的方向翻转，都得到 $(a-c)(b-d)(b-c)(a-d)$。因此 $T_1=T_2$，而 (116.10) 中它们的符号相反。全部分拆遂给

$$
L_{abcd}(\log p_I)=0\qquad\text{对每个 }I.
\tag{116.18}
$$

对补集 $I^c$ 也应用同一证明；它只是将上述分拆互换。取任意参考 $m$ 元集 $E_0$，原系数比值 $g_I=c_I/c_{E_0}$ 的形式对数差为

$$
\log\frac{g_I}{g_I(E)}=
\log\frac{p_I}{p_I(E)}+
\log\frac{p_{I^c}}{p_{I^c}(E)}-
\log\frac{p_{E_0}}{p_{E_0}(E)}-
\log\frac{p_{E_0^c}}{p_{E_0^c}(E)}.
\tag{116.19}
$$

体积与带标签符号在归一化常数中消去。四项均被 (116.18) 消去。又 $g_I$ Gale 不变，其在每个 $H_{uv}$ 上的一阶导数为零，所以对数二阶校正项在 (116.19) 合并后为零，得到 $L_{abcd}(g_I)=0$。参考比值及其逆没有例外；点导子法则给 $L_{abcd}(g_I^{-1})=0$。这些单位生成精确 $S_k$，局部化后的任意分母也由同一法则处理，故 $L_{abcd}$ 消去 $(S_k)_p$。

最后证明下界与下降。任选 $m-1$ 个不同根；其在 $V$ 上的评价为一组基，因为相应 Vandermonde 行列式非零。从这组基取四元组，(116.14) 得到 $\bigwedge^4V^*$ 的一组基的非零倍。因此相应的 $L_{abcd}$ 的负二次符号线性独立，点导子本身也线性独立。它们均在切映射 $T_y\operatorname{Spec}B_k\to T_p\operatorname{Spec}S_k$ 的核内；对偶后给 (116.2) 的几何版本。

原窗口、原系数点和正规化点均在 $F$ 上定义，且此固定点的剩余域为 $F$。这些余切空间及其线性映射与可分扩域交换；有限维线性映射的秩在扩域后不变。故几何余核维数下界就是原 $F$ 余核的下界，无需把每个分裂四根导子单独下降成原域导子。$m\ge5$ 使右端为正，故局部包含严格；由定理 113.1，它正是原局部环与整闭包的严格包含，所以原环非正规。有限模的忠实平坦完成化保持非零商，故完成后的包含仍严格。$\square$

## 117. 固定点的联合余切秩判据

**定理 117.1（固定线性与负二次项必须成对计算）。** 设 $C$ 为实际统一固定窗口，取定理 115.1 的原 $\lambda$。在 (115.7) 的原域双曲分解中，令 $E,E'$ 分别为 $C,C'$ 的对偶各向同性帧。令 $\mathcal A$ 为交错矩阵空间，$\mathcal O$ 为有效乘法环面在对称矩阵空间中的切像，选一个原 $F$ 线性补空间

$$
\operatorname{SymMat}_m(F)=\mathcal O\oplus N.
\tag{117.1}
$$

用实际包含帧

$$
E+E'(U+V),\qquad U\in\mathcal A,\quad V\in N
\tag{117.2}
$$

定义横截面。分裂后，对每个 $m$ 元集 $I$ 置 $M_I=E_I^{-1}E'_I$，选一个参考集 $E_0$，并对带集指标的表达式定义

$$
\Delta_I h=h_I+h_{I^c}-h_{E_0}-h_{E_0^c}.
$$

原系数局部环等于正规化局部环，当且仅当以下成对的向量在分裂域上张满整个直和空间：

$$
\left(
\Delta_I\operatorname{tr}(M_IU),
-\frac12\Delta_I\operatorname{tr}((M_IV)^2)
\right)\quad(|I|=m),
\tag{117.3}
$$

其中目标空间为 $\mathcal A^\vee\oplus\operatorname{Sym}^2(N^\vee)$。因此必要充分秩是

$$
a+\frac{b(b+1)}2.
\tag{117.4}
$$

这是联合秩；不能分别计算两组投影的秩再相加。判据与双曲基、补空间、参考集和分裂域的选择无关，并忠实下降到原 $F$。

证明。正交补在图坐标中严格为 $Y\mapsto-Y^{\mathsf T}$，所以 (117.2) 稳定，作用为 $(U,V)\mapsto(U,-V)$。它到 $X_D$ 的映射在原点处的切映射是

$$
\mathcal A\oplus N\longrightarrow
(\mathcal A\oplus\operatorname{SymMat}_m)/\mathcal O,
$$

由 (117.1) 为同构。源、目标都光滑，且是相同维数、相同实际剩余域的点；逐齐次次数求逆的形式逆函数定理给完成局部环同构。这个同构与对合交换。因此横截面确实计算 $X_D$ 的形式邻域及其 Gale 商，不是未经校正地删去矩阵中的某些条目。这里不需要假定横截面在整个商上全局单射。

在这张真正的横截面上，子式满足

$$
\frac{p_I(E+E'Y)}{p_I(E)}=\det(1+M_IY).
\tag{117.5}
$$

将原系数比值除以其在 $C$ 处的值，得到 $g_I(0)=1$，且

$$
\log g_I(U,V)=\Delta_I\log\det(1+M_I(U+V)).
\tag{117.6}
$$

每个 $g_I$ 对 $V\mapsto-V$ 不变，故其形式对数亦不变。在不变量局部环的极大理想模平方中，只保留一次 $U$ 和纯二次 $V$。理由是：含两个 $U$ 的项属于极大理想平方；含一个 $U$ 和至少两个 $V$ 的项亦然；纯 $V$ 的四次及更高偶次单项式可分成两个正偶次单项式。奇数个 $V$ 的项由不变性为零。展开 (117.6) 因此正好给出 (117.3)，没有缺少横截面或参考系数的校正项。

此外 $[g_I-1]=[\log g_I]$，因为形式对数的其余项均在不变量极大理想平方中。系数环由全部系数比值及其逆生成，局部化不会扩大这些余切类的张成空间。因此 (117.3) 的联合张成正是原系数余切映射的像。两个投影分别满秩并不保证这个联合像满秩；例如一个直和空间中的对角子空间可以有两个满射投影而仍为真子空间。

定理 113.1 给有限局部扩张，唯一几何点上方的剩余域相同；在实际固定点处两者都为 $F$。若联合秩达到 (117.4)，对余切满射应用定理 114.1 的两次 Nakayama 论证，依次得到 $\mathfrak m_B=\mathfrak m_A B$ 和 $B/A=0$。反向，局部环相等显然使联合余切映射满射。这证明必要充分性。

若不愿使用非 Galois 不变的参考集，可在原 $H_D$ 上取一个在 $p$ 非零的 $F$ 线性坐标作参考。分裂后它与任一 $c_{E_0}$ 的比值在目标局部环中为单位；换参考只对各局部生成元作可逆的局部坐标变换，故不改变余切像。分裂公式 (117.3) 正是这个原 $F$ 线性映射扩底后的表示。秩在域扩张后不变，满射和局部环相等都可由忠实平坦扩底检验。改双曲基或改 $N$ 则是同一形式邻域的另一个对合相容坐标系，其对余切空间的作用可逆，同样不改变判据。$\square$

## 118. 实际族、算术接口与完整中文表述

**推论 118.1（033 的指定平移幂族）。** 在固定原 $D/F$ 中，取本原元 $\theta$，令

$$
\eta=\theta+t,\qquad
C_t=\operatorname{span}_F(1,\eta,\ldots,\eta^{m-2},\eta^m).
\tag{118.1}
$$

对每个使 $C_t$ 统一的实际参数 $t\in F$，有

$$
[P_{C_t}]\text{ 光滑}
\quad\Longleftrightarrow\quad
C_t^2=D
\quad\Longleftrightarrow\quad
\operatorname{Tr}_{D/F}(\theta)+2mt\ne0.
\tag{118.2}
$$

这样的统一且光滑参数只排除有限个 $t$。若 $F$ 为数域，则在 033 定理 85.2 的其余精确前提与定义下，可用“统一且平方张满”替换其固定目标的光滑前提；其结论仍为原目标自有的 $d$ 个实际正标签、完整截交 $\operatorname{Spec}F\amalg\operatorname{Spec}L$，以及 $[L:F]=\delta-1$。这里 $d=\dim\Gamma_D$，$\delta=\deg\Gamma_D$ 保持为该原射影嵌入的次数符号。

证明。只复用 [033，命题 85.6](https://github.com/the-omega-institute/trureturing/blob/974984733cb1d619221ff97000612a9194bc8828/docs/develop/theory/AURIC_R5_033_ALL_DEGREE_ARITHMETIC_POSITIVE_CERTIFICATES.md) 的精确计算：$m$ 元子式是 Vandermonde 乘以相应 $m$ 个根值之和；因此统一性只排除有限个 $t$。平方像张成指数为 $0,1,\ldots,2m-2,2m$ 的幂；最小多项式在缺少的 $2m-1$ 次项上的系数是 $-\operatorname{Tr}(\eta)$，故平方像满秩当且仅当 $\operatorname{Tr}(\eta)\ne0$，迹为零时维数恰为 $2m-1$。这给最后一个等价。定理 115.1 补足第一个等价，而不使用 033 定理 85.7 的一般目标存在性替代指定曲线上的局部计算。

数域结论直接应用 033 定理 85.2：新的光滑判据只替换该定理中的目标光滑假设，不改变其标签参数空间、目标内分子分母条件、Hilbert 特化前提或完整剩余域结论。它没有把一般特征零域提升为数域，也没有把原域点隔离提升为所有几何点消失。$\square$

**命题 118.2（同一个具体原域中的固定非正规窗口与光滑窗口）。** 对任意 $m\ge5$，令

$$
F=\mathbb Q,\qquad D=\mathbb Q(\theta),\qquad \theta^{2m}=2.
\tag{118.3}
$$

在这个实际域中，连续幂窗口 $C=\langle1,\theta,\ldots,\theta^{m-1}\rangle$ 统一、固定且系数局部环非正规；而

$$
C_2=\langle1,\theta+2,\ldots,(\theta+2)^{m-2},(\theta+2)^m\rangle
\tag{118.4}
$$

统一且系数点光滑。两者的系数映射均为 (111.1) 的原域映射。

证明。$T^{2m}-2$ 在素数 $2$ 处满足 Eisenstein 判据，所以 $D$ 的次数正好为 $2m$；特征零保证可分。对 $C$，定理 116.1 直接适用，原乘数在这里为 $1/(2m\theta^{2m-1})$。

对 $C_2$，将根嵌入复数域。每个根的绝对值都是 $\rho=2^{1/(2m)}<2$。任意 $m$ 元根集 $I$ 满足

$$
\left|\sum_{i\in I}\theta_i\right|\le m\rho<2m,
$$

所以 $\sum_{i\in I}(\theta_i+2)\ne0$。033 的精确子式公式因而给全部最大子式非零。又 $\operatorname{Tr}(\theta)=0$，故 $\operatorname{Tr}(\theta+2)=4m\ne0$。推论 118.1 给平方张满与光滑性。这个实例在同一实际域中同时显示固定点的严格正规化包含与非固定点的局部相等；所有不等式都是对根的纸面界。$\square$

**定理 118.3（完整中文表述）。** 固定一个特征零、偶数次数至少十的实际可分域扩张，并取其中一个半维子空间。假设把这个子空间按原来的全部嵌入写成行矩阵时，任何半数行都独立。那么，由原乘法构成的行列式多项式，其系数点是否光滑，恰好由“子空间中的元素两两相乘，能否线性张成整个原域”决定。

如果能张满，系数点光滑；系数局部环已完整记录模掉整体非零乘法并再模掉 Gale 对偶后的局部信息。如果不能张满，乘积空间恰少一维，而且原域中实际存在一个非零元素，将这个窗口乘成它的迹正交补。该点是 Gale 固定点；它的正规化已经奇异，因而原系数点也不光滑。

对所有这些统一窗口，原系数像的正规化都是上述光滑乘法商再取 Gale 不变量所得的环。这一正规化在非固定点处与原系数环相等，在固定点处需要另外检验。固定点的检验必须把每个系数贡献的一次固定方向和二次反变方向放在一起，看这些成对数据是否联合张满整个正规化余切空间。

固定点处确实会丢失信息。取同一个原域的任一本原元，让窗口由从零次到 $m-1$ 次的连续幂张成。它仍然统一，却有非正规的系数局部环。四个不同的原嵌入可以给出一个真正作用在正规化局部环上的二阶点导子，它消去每个原互补系数而不消去全部正规化函数。独立的这类遗漏至少有 $\binom{m-1}{4}$ 维。这个数字是下界；它不描述全部遗漏，也不确定完整导子。

对少掉 $m-1$ 次幂、改放 $m$ 次幂的指定平移族，统一成员是否光滑则由原迹 $\operatorname{Tr}(\theta)+2mt$ 是否为零精确决定。底域是数域且保持 033 全部其余前提时，这些光滑窗口可使用该卷的实际正标签算术证书；剩余几何点仍组成其次数为 $\delta-1$ 的剩余域，没有被消灭。

证明。先区分三层信息。第一层是窗口本身；整体乘法不改变射影系数。第二层是整体乘法的几何商，它在统一开集上光滑；Gale 对偶再把两个可能的商点合并。第三层才是原互补系数生成的环，不能从集合上的两点合并推断它已经包含所有局部函数。

定理 112.1 对每个矩形和每个被反演的子式给首一方程及单位范数，所以第三层与第二层之间的映射有限。定理 113.1 用带原标签的主子式重建确定几何点纤维，再用特征零的可分性确定分式域次数为一，才得到正规化结论。非固定点处，定理 114.1 从一个非固定矩形向同一行、同一列及对角位置传播，把所有系数看不见的切方向消去，并用有限局部环的两次 Nakayama 引理得到环本身相等。

乘积不张满给一个迹配对关系。统一性迫使这个关系用到每个原嵌入，且只能有一维；线性核下降给真正的原域乘数。固定正规化中反变方向的偶次乘积产生过多余切方向，故它奇异。光滑环必正规，所以原系数环也不可能光滑；这就是定理 115.1 的两个方向，而非只凭固定点数量作判断。

连续幂族中的二阶遗漏更强：定理 116.1 的常帧算子先满足点导子的乘法法则，再对全部四根分拆及参考系数比值证明消去恒等式。其外四次符号保证独立与非零，秩的扩底不变性将下界送回原域。因此非正规性针对的是原实际窗口与原系数环。定理 117.1 给出其余固定点适用的联合检验，推论 118.1 则只把已经证明的光滑判据接到指定平移族和原有数域证书。各项陈述由此成立。$\square$

**注记 118.4（引用范围与环的边界）。** Howard–Millson 的互补子式与环面对偶公式、Eisenbud–Popescu 的自伴随二次条件，以及 Loewy–Al Ahmadieh 的无切口主子式重建，分别作为上述原域桥中的输入使用。Geiger–Zaffalon，[The Self-Projecting Grassmannian，2511.21442v1，Proposition 2.13、Remark 2.14](https://arxiv.org/abs/2511.21442v1) 给自投影配置与正交 Grassmannian 开集间的有限映射，并指出相应正交参数化不能据此当成双有理参数化；定理 113.1 的双有理性另由精确几何纤维及可分性证明。

Howard–Millson–Snowden–Vakil，[The geometry of eight points in projective space，1103.5255v1，§8，Propositions 8.1–8.2](https://arxiv.org/abs/1103.5255v1) 的完整分次环结论属于八点情形。此处只讨论所有原互补系数非零的开集，不把八点完整环结论用于更高次数。定理 116.1 中的外四次空间在 $m=4$ 时为零，在本卷 $m\ge5$ 的范围内才提供正下界。这些结论不分类非统一边界，不计算全局分次不变量的生成元、完整形式芽、完整导子或余切缺陷的确切维数；射影次数 $\delta$ 没有新的高次公式。

## 追加锚（本行以下为增补区）

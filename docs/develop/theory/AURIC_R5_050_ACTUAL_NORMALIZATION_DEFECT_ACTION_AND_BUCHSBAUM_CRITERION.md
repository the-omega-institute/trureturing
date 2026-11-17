# 实际正规化缺陷的完整模作用、Loewy 层与 Buchsbaum 判据

## 212. 固定原纤维、实际源与缺陷模

**定义 212.1（同一个原十四次域与实际系数源）。** 设 $F$ 为任意特征零域，$D/F$ 为实际可分域扩张，$[D:F]=14$。固定本原元 $\theta$ 和非零体积形式 $\nu:\det_FD\to F$，取连续窗口

$$
C_{\mathrm{win}}=\langle1,\theta,\ldots,\theta^6\rangle_F,
\qquad V=F[T]_{\le5},\quad e_i=T^i,\quad W=\bigwedge^2V.
\tag{212.1}
$$

对同一个 $D$ 中的七维窗口 $C'$，以包含帧 $E_{C'}$ 定义

$$
P_{C'}(x)=\nu\bigl(\det[E_{C'},M_xE_{C'}]\bigr).
\tag{212.2}
$$

$M_x$ 是这个域中的乘法。在有限 Galois 分裂域中保留原嵌入标签及固定次序，原射影系数为

$$
P_{C'}(x)=\sum_{|I|=7}c_I(C')x_I,
\qquad c_I=\alpha\epsilon_Ip_Ip_{I^c}.
\tag{212.3}
$$

这里 $p_I$ 是实际帧的递增行子式，$\epsilon_I$ 是互补行序符号，$\alpha$ 来自体积形式。令 $S$ 为此原带符号、带标签射影系数像在 $[P_{C_{\mathrm{win}}}]$ 处的原 $F$ 局部环，$\mathscr T=\widehat S$。分裂标签函数不自动是原 $F$ 函数。

采用 039 的原乘法商及有限正规化、042 的实际对合相容横截面，记完成正规化为

$$
\mathscr B=F[[U_1,\ldots,U_{21},Y_1,\ldots,Y_{15}]]^{Y\mapsto-Y}.
\tag{212.4}
$$

固定这组负坐标，沿用原域识别

$$
e_i\wedge e_j\longleftrightarrow
z_{ij}(Y)=Y(\theta^{i+1},\theta^j)-Y(\theta^i,\theta^{j+1}),
\qquad 0\le i<j\le5.
\tag{212.5}
$$

任意预先固定合法原 $F$ 正枢轴 $s=(s_1,\ldots,s_{21})\subset\mathfrak m_S$：其原余切像在二十一维正余切空间上的投影为一组基。“正”指对合的正特征方向，不要求 $F$ 有序。全文在这一组已经固定的 $s$ 上定义

$$
B=B_s=\mathscr B/(s)\mathscr B\simeq F[[Y_1,\ldots,Y_{15}]]^{Y\mapsto-Y},
$$

$$
\pi_s:\mathscr T\longrightarrow B,
\qquad A=A_s=\operatorname{im}\pi_s,
\qquad \mathfrak m=\mathfrak m_A,\quad \mathfrak n=\mathfrak m_B.
\tag{212.6}
$$

原正变量在实际纤维上满足 $U=\phi_s(Y)=O(Y^2)$。因此这里取实际像，而不把它换成 $\mathscr T/(s)\mathscr T$，也不直接令原正变量为零。按 046，约定 175.2 及 049，定义 202.2，$A$ 是剩余域为 $F$ 的完备 Noetherian 局部域，$B$ 是有限 $A$ 模，两环的常数映射均为原 $F$ 上的剩余映射。以下所有量词都允许任意这样的 $F,D,\theta,s$，但每个证明内部保持它们不变。

**定义 212.2（唯一检测器及已知实际源接口）。** 置

$$
H_j=\operatorname{Sym}^jW,\qquad G=\bigwedge^4V,\qquad
\mu:H_2\longrightarrow G,\quad \mu(ab)=a\wedge b,
$$

$$
K=\ker\mu,\qquad P_4=K K\subseteq H_4,
\qquad \mathcal D=\det(V)\otimes W,
\qquad \Omega=e_0\wedge\cdots\wedge e_5.
\tag{212.7}
$$

$K K$ 表示恰好两个 $K$ 元素乘积的线性张成。沿用 045 的四项归一化

$$
\Psi:H_4\longrightarrow\mathcal D,\qquad
\Psi(a_1a_2a_3a_4)=
\sum_{i=1}^4\left(\bigwedge_{j\ne i}a_j\right)\otimes a_i.
\tag{212.8}
$$

令 $\mathfrak q=(Y)\subset F[[Y]]$，并置

$$
J=J_{4,s}=\operatorname{in}_4(A\cap\mathfrak n^2)\subseteq H_4,
\qquad E_s=\Psi(J)\subseteq\mathcal D,\qquad d=d_s=\dim_FE_s.
\tag{212.9}
$$

$J$ 的定义要求实际常数和二次项均已消失。$\mathfrak n^r=B\cap\mathfrak q^{2r}$，且 $\mathfrak n^r/\mathfrak n^{r+1}=H_{2r}$。所用原源接口为

$$
\begin{gathered}
\operatorname{in}_2(\mathfrak m)=K,\qquad
u:K\longrightarrow\mathfrak m_S\text{ 为原 }F\text{ 线性提升},\\
\pi_s(u(k))=k+t_s(k)+O(Y^6),\qquad t_s(k)\in H_4,\\
P_4\subseteq J,\qquad \ker\Psi=P_4,\qquad
J=\Psi^{-1}(E_s),\qquad \Psi(H_4)=\mathcal D,\\
\pi_s(\mathfrak m_{\mathscr T}^3)=\mathfrak m^3=\mathfrak n^3\subseteq A.
\end{gathered}
\tag{212.10}
$$

提升 $u$ 来自 045，引理 170.1，同一批原函数适用于所有合法枢轴；核等式及满射来自该卷定理 168.2、(169.4)。最后一行是 046，定理 177.2 的完整实际源结论：对每个 $h\in\mathfrak n^3$，存在 $Q_s(h)\in\mathfrak m_{\mathscr T}^3$ 满足 $\pi_s(Q_s(h))=h$。不要求此选择典范或线性。由此消去尾项时，消去的是具有真正原源见证的元素。

049，定理 203.2 已确定实际有限图：写 $f=c+q_2+q_4+h_6$，其中 $h_6\in\mathfrak n^3$，则

$$
f\in A\quad\Longleftrightarrow\quad
q_2\in K,\qquad q_4-t_s(q_2)\in J.
\tag{212.11}
$$

特别地，每个齐次 $j\in J$ 本身属于 $A$，而不只是某个实际元素的首项。该卷还给出非零公共导子理想 $\mathfrak n^3$、有限双有理正规化 $A\subset B$、$6\le d\le15$ 和

$$
\operatorname{length}_A(B/A)=30-d.
\tag{212.12}
$$

这些有限图、导子和长度结论均作为已知前置使用。

**定义 212.3（实际正规化缺陷及两种滤过）。** 定义有限长度 $A$ 模

$$
M=B/A,
\qquad F^rM=(A+\mathfrak n^r)/A\quad(r\ge0),
\qquad M_4=F^2M.
\tag{212.13}
$$

这里 $\mathfrak n^0=B$。$F^rM$ 是从指定正规化极大理想诱导的阶数滤过，不是预先假定的 $\mathfrak m$ 幂滤过。$M$ 只取 $A$ 模结构；$A$ 不是 $B$ 理想，故不对 $M$ 赋予由 $B$ 乘法下降的模结构。

## 213. 实际缺陷的典范两层正合列

**定理 213.1（阶数层及实际提升）。** 对定义 212.1 的每个预固定实际纤维，阶数滤过满足

$$
F^0M=F^1M=M,\qquad F^2M=M_4,\qquad F^3M=0.
\tag{213.1}
$$

有典范的 $A$ 模短正合列

$$
\boxed{
0\longrightarrow M_4\xrightarrow{\ \iota\ }M
\xrightarrow{\ p\ }G\longrightarrow0,
\qquad M_4\simeq H_4/J\simeq\mathcal D/E_s.
}
\tag{213.2}
$$

两端的 $A$ 作用均通过 $A\to F$。相对于已经固定的负坐标，箭头为

$$
p([b])=\mu(b_2),\qquad
\iota\bigl(\Psi(q)+E_s\bigr)=[q]\quad(q\in H_4),
\tag{213.3}
$$

$b_2$ 表示减去常数后的二次齐次项。特别地，

$$
\dim_FG=15,\qquad \dim_FM_4=15-d.
\tag{213.4}
$$

证明。$F\subset A$，所以每个 $[b]\in M$ 都有零常数代表 $b\in\mathfrak n$；这给 $F^1M=M$。由实际尾项接口，$F^3M=0$。

若更换 $b$ 的代表，其差在 $A$ 中，差的二次项属于 $K$，故 $p$ 良定义。$\mu$ 满射：任一基四向量都可分成两个基二向量的外积；取相应齐次二次式便实现 $p$ 的满射。

若 $p([b])=0$，则 $b_2=k\in K$。从原源取 $u(k)$，在目标减去实际元素 $\pi_s(u(k))$，所得代表属于 $\mathfrak n^2$。因而 $\ker p=M_4$。这一操作并未假定纯齐次 $k$ 本身属于 $A$；实际提升所带的 $t_s(k)$ 仍在差中。

对 $b\in\mathfrak n^2$，其四次项为 $q\in H_4$，且 $b-q\in\mathfrak n^3\subseteq A$。所以 $H_4\to M_4$，$q\mapsto[q]$ 满射。其核恰为 $J$：若 $q\in A$，其四次符号按定义在 $J$ 中；若 $q\in J$，取实际提升 $q+h_6\in A$，再由 $Q_s(h_6)$ 消去尾项，得到 $q\in A$。因此 $M_4\simeq H_4/J$。由 $J=\Psi^{-1}(E_s)$ 及 $\Psi$ 满射，得到第二个同构和 (213.3) 的良定义。

对 $a\in\mathfrak m$、$b\in\mathfrak n$，有 $ab\in\mathfrak n^2$，故 $p(a[b])=0$；对 $q\in\mathfrak n^2$，则 $aq\in\mathfrak n^3\subseteq A$。这证明两端均由剩余域作用，且所有箭头 $A$ 线性。最后 $\dim V=6$，故 $\dim G=\dim W=15$，给出 (213.4)。证毕。

此列的典范性指阶数子模、商映射和检测同构不依赖代表或源提升；坐标识别仍采用 (212.5)。有限维 $F$ 空间短列当然可以选取线性截面，但不指定典范截面，也不将任何线性截面解释为代数嵌入。

## 214. 每个非零上层方向的原域满射

**定义 214.1（带行列式线的作用配对）。** 对 $k\in K$、$t\in G$，取 $c\in H_2$ 满足 $\mu(c)=t$，定义

$$
\beta:K\times G\longrightarrow\mathcal D,\qquad
\beta(k,t)=\Psi(kc),
\qquad \overline\beta_s(k,t)=\beta(k,t)+E_s.
\tag{214.1}
$$

这是 048，定义 192.1 和 049，定义 204.1 的原配对。若换 $c$，其差在 $K$ 中，乘以 $k$ 后在 $P_4=\ker\Psi$ 中，故 $\beta$ 良定义且双线性。$\overline\beta_s$ 的值域为 $\mathcal D/E_s$，而非 $W$ 的一个未指定商。

**定理 214.2（任意非零 $t$ 的原 $F$ 满射）。** 对任意特征零 $F$ 和任意 $0\ne t\in G$，有

$$
\boxed{\quad \beta(K,t)=\mathcal D.\quad}
\tag{214.2}
$$

该等式在原 $F$ 上成立，不需要扩到代数闭域。固定 $\Omega$，以完美外乘配对定义

$$
\lambda_t\in W^\vee,\qquad
t\wedge a=\lambda_t(a)\Omega\quad(a\in W),
\tag{214.3}
$$

并令 $\delta:H_2\to W\otimes W$ 满足 $\delta(ab)=a\otimes b+b\otimes a$。则精确作用公式为

$$
\beta(k,t)=\Omega\otimes
\bigl((\lambda_t\otimes\operatorname{id}_W)\delta(k)\bigr).
\tag{214.4}
$$

证明。$G\times W\to\det(V)$ 的外乘配对完美：在基四向量与基二向量之间，只有互补指标项非零，其值为 $\pm\Omega$。所以 $t\ne0$ 蕴含 $\lambda_t\ne0$。这里的自然类型是

$$
G\simeq\operatorname{Hom}_F(W,\det(V));
\qquad \Omega\text{ 平凡化后才有 }G\simeq W^\vee.
\tag{214.5}
$$

不把 $G$ 直接认作 $W$。

045，(168.5) 的四项展开，亦即 049，(205.5)，给

$$
\Psi(kc)=\mu(k)\wedge\delta(c)+\mu(c)\wedge\delta(k),
\tag{214.6}
$$

其中 $g\wedge(a\otimes b)=(g\wedge a)\otimes b$。$k\in K$ 使第一项为零，第二项正是 (214.4)。特别地，对任意 $x,y\in V$，令 $z=x\wedge y$，则 $z\wedge z=0$，所以 $z^2\in K$，且

$$
\beta(z^2,t)=2\Omega\otimes\lambda_t(z)z.
\tag{214.7}
$$

极化的因子 $2$ 保留在此式中。

若 (214.2) 不成立，有限维线性代数给出非零 $\eta\in W^\vee$，使它消去 (214.4) 右侧的全部 $W$ 分量。由 (214.7)，对全部原 $F$ 向量 $x,y$ 都有

$$
\lambda_t(x\wedge y)\eta(x\wedge y)=0.
\tag{214.8}
$$

将 $x,y$ 的坐标分别记为十二个独立变量 $X_i,Y_i$。因为 $F$ 无限，(214.8) 是多项式恒等式：在无限域上，一个多元多项式若在全部域值点为零，就逐个变量应用一元多项式根数界，归纳得到全部系数为零。因此

$$
\lambda_t(X\wedge Y)\eta(X\wedge Y)=0
\quad\text{于 }F[X_0,\ldots,X_5,Y_0,\ldots,Y_5].
\tag{214.9}
$$

此多项式环为整环。$\lambda_t\ne0$ 保证第一个因子非零：基二向量 $e_i\wedge e_j$ 张成 $W$，故存在一个原基向量对使其评价非零。于是第二个因子为零。再在所有基向量对上评价，得到 $\eta(e_i\wedge e_j)=0$，即 $\eta=0$，矛盾。因此像的消去子为零，有限维性给满射。证毕。

这里使用的是同一个原 $F$ 多项式环中的乘积恒等式，不是关于代数闭包中开集的稠密性推断。证明也没有要求 $t$ 可分解，或要求它具有某个特定外代数类型。

## 215. 从原源乘法到整个实际模作用

**定理 215.1（完整 $A$ 作用及其阶数）。** 对定义 212.1 的每个实际纤维，令 $a_0\in F$ 为 $a\in A$ 的常数，令

$$
k_a=\operatorname{in}_2(a-a_0)\in K.
\tag{215.1}
$$

则 $M$ 的整个 $A$ 作用由 (213.2) 和下式给出：对所有 $x\in M$，

$$
\boxed{\quad
(a-a_0)x=\iota\bigl(\overline\beta_s(k_a,p(x))\bigr).
\quad}
\tag{215.2}
$$

特别地，

$$
\boxed{\quad \mathfrak m M=M_4,\qquad \mathfrak m^2M=0.\quad}
\tag{215.3}
$$

对任意选定的 $F$ 线性截面 $\sigma:G\to M$，用
$M\simeq(\mathcal D/E_s)\oplus G$，$(q,t)\mapsto\iota(q)+\sigma(t)$ 表示时，全部作用写成

$$
\boxed{\quad
a\cdot(q,t)=\bigl(a_0q+\overline\beta_s(k_a,t),\ a_0t\bigr).
\quad}
\tag{215.4}
$$

这是选取线性坐标后的模表示，不是 $A$ 在 $B$ 中的齐次代数分裂。

证明。先取 $a\in\mathfrak m$、$x=[b]\in M$。减去 $b$ 的常数后，可以且只需要求 $b\in\mathfrak n$。写

$$
a=k+a_{\ge4},\qquad b=c+b_{\ge4},
\quad k\in K,\ c\in H_2,\quad
a_{\ge4},b_{\ge4}\in\mathfrak n^2.
$$

在同一实际纤维中有

$$
ab=kc+h_6,\qquad h_6\in\mathfrak n^3\subseteq A.
\tag{215.5}
$$

无论 $a$ 的真实四次尾项是什么，交叉项都至少六阶。它们被消去的理由是 (212.10) 的原完成源提升，而非目标中的形式闭包。由 (213.3)，乘积类正好对应
$\Psi(kc)+E_s=\overline\beta_s(k,p(x))$，得 (215.2)。

也可在原源上直接核对每一个作用值。对 $k\in K$ 使用实际 $\pi_s(u(k))$，对 $t\in G$ 使用任意齐次 $c\in H_2$ 满足 $\mu(c)=t$。于是

$$
\pi_s(u(k))c-kc\in\mathfrak n^3.
\tag{215.6}
$$

若更换 $c$，其二次差在 $K$ 中，乘积四次差在 $P_4\subseteq J$ 中；若更换原提升，差在 $A\cap\mathfrak n^2$ 中，与零常数 $b$ 相乘进入 $\mathfrak n^3$。若更换 $b$ 的实际余类代表，乘积差是 $A$ 中两个元素的乘积。因而公式同时尊重源、目标代表和检测商。

由 (215.5)，$\mathfrak m M\subseteq M_4$。反向固定任意 $0\ne t\in G$，选 $x\in M$ 满足 $p(x)=t$。原提升使 $\mathfrak m\to K$ 满射；定理 214.2 使
$K\to\mathcal D/E_s$，$k\mapsto\overline\beta_s(k,t)$ 满射。因此

$$
\mathfrak m x=M_4.
\tag{215.7}
$$

这也适用于 $M_4=0$，并给 (215.3) 的第一个等式。

第二个等式还可不经配对直接证明。对任意 $a_1,a_2\in\mathfrak m$ 和任意零常数代表 $b\in\mathfrak n$，有

$$
a_1a_2b\in\mathfrak n\,\mathfrak n\,\mathfrak n
=\mathfrak n^3\subseteq A.
\tag{215.8}
$$

这里用了三个二阶因子；并未将一般的 $b$ 假定为四阶。有限和给 $\mathfrak m^2M=0$。同样，$\mathfrak m M_4=0$。

最后把任意 $x$ 写成 $\iota(q)+\sigma(t)$，利用两端的剩余域作用及 (215.2)，便得 (215.4)。若换截面，差为某个 $F$ 线性映射 $G\to M_4$；$\mathfrak m M_4=0$ 使同一作用公式保持成立。公式由实际商中的乘法导出，故遵守加法、乘法及单位元的全部模公理。证毕。

作用的消去条件与 049 的导子一致：对 $a\in\mathfrak m$，$aM=0$ 当且仅当 $\beta(k_a,G)\subseteq E_s$。049，定理 205.1 已将这个二次符号空间识别为 $K\cap\operatorname{Sym}^2E$，其中 $\Omega\otimes E=E_s$；其真实四次尾项及整个嵌入导子仍由该卷给出。这里使用这一已知结果，不将导子的重述计作新的模结构结论。

## 216. 两个分支的精确 Loewy 层与 socle

**定义 216.1（Loewy 与 socle 约定）。** 对有限长度 $A$ 模 $N$，其下降 Loewy 滤过为 $N\supseteq\mathfrak mN\supseteq\mathfrak m^2N\supseteq\cdots$，Loewy 长度是使 $\mathfrak m^\ell N=0$ 的最小 $\ell$。定义

$$
\operatorname{Soc}_A(N)=0:_N\mathfrak m,
\qquad \operatorname{Top}_A(N)=N/\mathfrak mN.
\tag{216.1}
$$

上升 socle 滤过由 $\operatorname{Soc}^0N=0$、
$\operatorname{Soc}^{i+1}N/\operatorname{Soc}^iN=
\operatorname{Soc}(N/\operatorname{Soc}^iN)$ 定义。

**定理 216.2（实际缺陷的全部 Loewy 与 socle 层）。** 对每个固定实际 $s$，两种情况如下。

若 $d<15$，则

$$
\begin{gathered}
M\supsetneq\mathfrak mM=M_4\supsetneq0,\\
\operatorname{Soc}_A(M)=M_4\simeq\mathcal D/E_s,
\qquad \operatorname{Top}_A(M)\simeq G,\\
\dim_F\operatorname{Soc}_A(M)=15-d,\qquad
\dim_F\operatorname{Top}_A(M)=15,\\
\operatorname{Soc}^1M=M_4,\qquad \operatorname{Soc}^2M=M.
\end{gathered}
\tag{216.2}
$$

Loewy 长度为二，两层从上到下的维数为 $15,15-d$；(213.2) 在 $A$ 模范畴不分裂。

若 $d=15$，则

$$
\begin{gathered}
M_4=0,\qquad \mathfrak mM=0,\qquad
M\xrightarrow{\ p\ }G\text{ 为同构},\\
\operatorname{Soc}_A(M)=\operatorname{Top}_A(M)=M,
\qquad \dim_FM=15.
\end{gathered}
\tag{216.3}
$$

Loewy 长度为一。两个分支均有 $\dim_FM=30-d$，与 049 的实际长度一致。

证明。$\mathfrak mM=M_4$、$\mathfrak mM_4=0$ 已证，所以 $M_4\subseteq\operatorname{Soc}_A(M)$。若 $d<15$ 且 $x\notin M_4$，则 $p(x)\ne0$，(215.7) 给 $\mathfrak m x=M_4\ne0$，故 $x$ 不属于 socle。因此 socle 恰为 $M_4$。顶层、各维数和上升 socle 第二层由 (213.2) 直接得到。若该列在 $A$ 模范畴分裂，两端都被 $\mathfrak m$ 消去，就会有 $\mathfrak mM=0$，与 $M_4\ne0$ 矛盾。

若 $d=15$，则 $E_s=\mathcal D$，故 $M_4=0$；正合列给 $M\simeq G\ne0$，其作用通过 $F$，所以 socle、top 都是整个模。两种情况的总维数由正合列相加，未重新计算 049 的长度。证毕。

层维数只取决于 $d$，但 (215.2) 的具体作用仍取决于实际子空间 $E_s\subseteq\mathcal D$ 以及实际二次符号映射 $A\to K$。仅有两个纤维的 $d$ 相同，不能据此识别它们的作用映射或断言实际环、缺陷模同构。尤其 $d=15$ 在此是条件分支，不是已经找到这种枢轴的存在断言。

## 217. 同一缺陷模的深度与局部上同调实现

**定理 217.1（实际局部上同调携带同一作用）。** 对每个固定实际纤维，$\dim A=\dim B=15$，$B$ 是共同分式域中的有限 Cohen–Macaulay 正规化，且 $0\ne\mathfrak n^3\subseteq\mathfrak c_{A\subset B}$。有限包含的连接同态给典范 $A$ 模同构

$$
\boxed{\quad H^1_{\mathfrak m}(A)\simeq M=B/A.\quad}
\tag{217.1}
$$

在此同构下，(213.2)、(215.2) 及 (216.2)--(216.3) 就是 $H^1_{\mathfrak m}(A)$ 的滤过、完整乘法及 socle。并有

$$
H^0_{\mathfrak m}(A)=0,\qquad
H^i_{\mathfrak m}(A)=0\quad(2\le i\le14),
\qquad \operatorname{depth}A=1,
\tag{217.2}
$$

以及 $H^{15}_{\mathfrak m}(A)\simeq H^{15}_{\mathfrak n}(B)$。特别地，$A$ 总是广义 Cohen–Macaulay 环，低次局部上同调的唯一缺陷就是上述实际有限长度模。

证明。有限性、公共导子、双有理性和正规化结论直接沿用 049，§§203--204；这里核对消费局部代数所需的维数与 Cohen–Macaulay 条件。令

$$
R=F[[Y_1,\ldots,Y_{15}]],\qquad
T=F[[Y_1^2,\ldots,Y_{15}^2]]\subseteq B.
\tag{217.3}
$$

按各变量指数的奇偶性分组，每个形式级数唯一写成平方变量级数乘以平方自由单项式的有限和。对合在这样的单项式上作用为其总次数的奇偶符号。因此 $B$ 对 $T$ 自由，基由总次数为偶数的平方自由单项式组成。于是 $Y_1^2,\ldots,Y_{15}^2$ 在 $B$ 上为正则序列，$B$ 有限于十五维正则局部环 $T$，故 $\dim B=15$ 且 $B$ Cohen–Macaulay。$B$ 有限整于 $A$ 给 $\dim A=15$。

也可直接核对正规性：$R$ 正规；若 $x\in\operatorname{Frac}(B)$ 整于 $B$，则也整于 $R$，故 $x\in R$。它又被对合固定，所以 $x\in R^{Y\mapsto-Y}=B$。对于共同分式域，任取 $0\ne h\in\mathfrak n^3$，则对所有 $b\in B$ 有 $hb\in\mathfrak n^3\subseteq A$，从而 $b=(hb)/h\in\operatorname{Frac}(A)$。这只是对 049 已有正规化接口的具体核对。

因为 $\mathfrak n^3\subseteq\mathfrak m\subseteq\mathfrak n$，有 $\sqrt{\mathfrak mB}=\mathfrak n$。故 $H^i_{\mathfrak m}(B)=H^i_{\mathfrak n}(B)$。经典的正则序列局部上同调消失在此给

$$
H^i_{\mathfrak m}(B)=0\quad(0\le i<15).
\tag{217.4}
$$

具体可用参数 $Y_i^2$ 的 Čech 复形：$T$ 的正则参数复形只在顶次有上同调，张量上述自由 $T$ 模 $B$ 后保留这一消失。这一步使用经典 Cohen–Macaulay 工具，不是新的独立一般定理。

$M$ 有限长度，且已知 $\mathfrak m^2M=0$，所以 $H^0_{\mathfrak m}(M)=M$，$H^i_{\mathfrak m}(M)=0$ 对 $i>0$。将局部上同调用于

$$
0\longrightarrow A\longrightarrow B\longrightarrow M\longrightarrow0,
\tag{217.5}
$$

由 (217.4) 得到 $H^0_{\mathfrak m}(A)=0$、连接同构 $M\xrightarrow{\sim}H^1_{\mathfrak m}(A)$，以及所有 $i\ge2$ 的 $H^i_{\mathfrak m}(A)\simeq H^i_{\mathfrak m}(B)$。长正合列是 $A$ 线性的，故连接同构保留完整作用，而不只是保留长度。$p:M\twoheadrightarrow G\ne0$ 保证 $H^1_{\mathfrak m}(A)\ne0$，所以深度恰为一。各低次上同调有限长度亦给广义 Cohen–Macaulay 性。证毕。

## 218. 实际 Buchsbaum 阻碍的必要充分条件

**定义 218.1（所用的弱序列判据）。** 对 $r$ 维 Noetherian 局部环 $(L,\mathfrak l)$，参数系 $x_1,\ldots,x_r$ 称为弱序列，若对每个 $0\le i<r$，令 $I_i=(x_1,\ldots,x_i)L$，均有

$$
(I_i:_Lx_{i+1})=(I_i:_L\mathfrak l).
\tag{218.1}
$$

$L$ 为 Buchsbaum 环等价于每个参数系均为弱序列；这与参数理想的长度减重数不变量定义等价，采用 Goto，Definition (2.1) 的标准判据。以下在本实际有限包含内直接证明所需两个方向。

**定理 218.2（每个预固定原纤维的精确 Buchsbaum 判据）。** 在定义 212.1 的任意固定实际数据中，

$$
\boxed{
A_s\text{ 为 Buchsbaum 环}
\quad\Longleftrightarrow\quad
\mathfrak m_sB_s\subseteq A_s
\quad\Longleftrightarrow\quad
E_s=\det(V)\otimes W
\quad\Longleftrightarrow\quad d_s=15.
}
\tag{218.2}
$$

在这些等价条件成立时，$H^1_{\mathfrak m_s}(A_s)\simeq G$，为十五维剩余域模，$B_s$ 是 Goto 意义下唯一的 Cohen–Macaulayfication。若 $d_s<15$，则 $H^1_{\mathfrak m_s}(A_s)$ 的非零极大理想作用恰为 $\mathcal D/E_s$，其维数为 $15-d_s$；这就是本实际源的 Buchsbaum 阻碍。

证明。先设 $\mathfrak mB\subseteq A$。任取 $A$ 的参数系 $x_1,\ldots,x_{15}$。因 $B$ 是有限局部 $A$ 代数，其扩张参数理想在 $B$ 中的根为 $\mathfrak n$；维数相同，故这是 $B$ 的参数系。$B$ Cohen–Macaulay，所以该序列在 $B$ 上正则。

固定 $0\le i<15$，置 $I_i=(x_1,\ldots,x_i)A$、$J_i=(x_1,\ldots,x_i)B$。若 $a\in(I_i:_Ax_{i+1})$，则 $x_{i+1}a\in J_i$。由 $B$ 上的正则性，$a\in J_i$，故可以写成 $a=\sum_{j\le i}x_jb_j$，其中 $b_j\in B$。对任意 $y\in\mathfrak m$，假设给 $yb_j\in A$，因而

$$
ya=\sum_{j\le i}x_j(yb_j)\in I_i.
\tag{218.3}
$$

所以 $(I_i:x_{i+1})\subseteq(I_i:\mathfrak m)$；反向包含由 $x_{i+1}\in\mathfrak m$ 立即得到。$i=0$ 时正则性直接给 $a=0$，同一结论仍成立。任意参数系都是弱序列，故 $A$ Buchsbaum。

反向设 $A$ Buchsbaum。选择公共导子内的十五个明确参数

$$
x_j=Y_j^6\in\mathfrak n^3\subseteq A\qquad(1\le j\le15).
\tag{218.4}
$$

它们在 $B$ 中生成根为 $\mathfrak n$ 的理想，因为是平方参数 $Y_j^2$ 的三次幂。它们在 $A$ 中也构成参数系：若 $A$ 的素理想含它们，由有限整扩张的 lying over 取上方素理想，该素理想在 $B$ 中必须为 $\mathfrak n$，故原素理想为 $\mathfrak m$。又 $x_jB\subseteq A$，因为 $\mathfrak n^3$ 是公共导子理想。

现取任意 $b\in B$，置 $a=x_1b\in A$。$x_2b\in A$ 给

$$
x_2a=x_1(x_2b)\in x_1A,
\qquad a\in(x_1A:_Ax_2).
\tag{218.5}
$$

弱序列等式使 $\mathfrak m a\subseteq x_1A$。对任意 $y\in\mathfrak m$，存在 $c\in A$ 使 $yx_1b=x_1c$。$B$ 为整环且 $x_1\ne0$，故可在 $B$ 中消去，得到 $yb=c\in A$。因为 $b,y$ 任意，$\mathfrak mB\subseteq A$。这里用到了维数至少二以取得第二个公共参数，以及非零因子的消去；本题维数为十五。

最后，由实际商模定义，

$$
\mathfrak mB\subseteq A
\quad\Longleftrightarrow\quad \mathfrak mM=0
\quad\Longleftrightarrow\quad M_4=0
\quad\Longleftrightarrow\quad \mathcal D/E_s=0.
\tag{218.6}
$$

第二个等价使用已经证明的整个作用，而非只使用总长度。$\dim\mathcal D=15$，故最后一项等价于 $d_s=15$。局部上同调的具体描述由定理 217.1、216.2 得到。证毕。

上述经典判据与 Goto 原文的适用范围逐项相符。其 Definition and Lemma (2.3)，印刷页 124--125，针对 $r$ 维 Noetherian 局部环 $(L,\mathfrak l)$，将

$$
L\text{ Buchsbaum},\qquad
H^i_{\mathfrak l}(L)=0\quad(i\ne1,r)
\tag{218.7}
$$

与存在 $Q(L)\supseteq B'\supseteq L$ 等价，其中 $B'$ Cohen–Macaulay、为有限 $L$ 模、每个极大理想 $\mathfrak r$ 均满足 $\dim B'_{\mathfrak r}=r$，且 $\mathfrak lB'\subseteq L$；$r\ge2$ 时这种 $B'$ 唯一且 $H^1_{\mathfrak l}(L)\simeq B'/L$。本题 $L=A$、$r=15$，$B$ 已是共同分式域中的有限 Cohen–Macaulay 局部中间环，唯一极大理想的局部维数为十五，其他低次上同调按 (217.2) 消失。当 (218.2) 成立时，它满足该引理的全部条件，故取得所述唯一性。

这里消费的是该文的 (2.3)，不需要其 Theorem (2.5) 的特定闭合与 gluing 构造。两个方向的实际弱序列证明也没有使用“一般 quasi-Buchsbaum 环均 Buchsbaum”这一不成立的替代命题。

## 219. 完整的普通中文数学解释

**定义 219.1（缺陷及其乘法的普通含义）。** 固定一个实际十四次域、一个本原元、七个连续幂窗口、全部原符号标签系数，并事先固定二十一条合法正枢轴。正规化纤维里有全部十五个负变量的偶级数；原完成系数源只能给出其中的实际子环。缺陷模记录“一个偶级数还差多少才能来自原源”，两个级数相差一个实际源元素就代表同一个缺陷。

所有六阶及以上的偶级数已经有同一个原完成源见证，因此缺陷只剩二次与四次。二次层总有十五维缺失，正是外四次空间 $G$；四次层还剩十五减去实际检测维数的缺失。049 已给出两层总共的长度，本卷进一步确定它们怎样被实际源元素相乘而联系起来。

一个实际源元素的零常数部分从二阶开始，其首项属于二次核 $K$。用它乘一个二次缺陷，会把结果送到四次缺陷；所有真实四次伴随项与高阶尾项都只在六阶以后出现，所以不改变这次作用。四项检测器精确读出这个乘积，再模掉实际已经可见的检测子空间 $E_s$。这给整个作用，不只是某个选定生成元的作用。

每个非零二次缺陷都有同一个强性质：让实际源的二次核方向变化，它的乘积可以达到全部四次缺陷。其理由是在原域上，一个非零线性函数与另一个线性函数的乘积若在所有可分解二向量上为零，就会给出两个双线性多项式的零乘积。原多项式环没有零因子，因此第二个线性函数也只能为零。这个证明适用于任意特征零原域，不需要选取复数点。

因此，若仍有四次缺陷，乘一次极大理想就恰好得到全部四次缺陷，再乘一次便为零；socle 正好是最后这层，顶层始终十五维。若实际四次检测已满十五维，则四次缺陷消失，整个十五维缺陷都被极大理想消去，socle 就是整个缺陷模。这两种情况给出完整 Loewy 与 socle 结构，但没有判定指定纤维落在哪一种。

正规化环本身是十五维 Cohen–Macaulay 环；实际环的全部低次局部上同调缺陷由同一个 $B/A$ 模承载，所以实际环的深度恰为一。要使实际环 Buchsbaum，恰好必须让极大理想消去全部这个缺陷。充分性来自任意参数系在正规化上正则；必要性则用导子中的两个共同参数，把弱序列条件转成可消去非零因子的乘法等式。结合已经求出的作用，条件精确等价于实际检测像满十五维。

这是一条逐固定纤维的必要充分判据，而不是十五维检测已经发生的结论。实际 $E_s$ 的具体方向仍然决定完整作用；只知道它的维数，可以读出层大小和 Buchsbaum 的条件分支，不能取代对原源实际像的确定。

## 220. 数学来源、重叠边界与尚未求出的实际像

**约定 220.1（原族前置的固定来源）。** 下表的结果均作为既有前置消费；其中 049 的有限图、导子、六方向外乘及长度不作为新增内容。

| 固定来源 | 本文使用的确切范围 |
| --- | --- |
| [039，e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb，§§111--117](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) | 原系数源、实际乘法商、有限正规化、唯一上方点、剩余域及实际对合模型。 |
| [042，fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6，§§132--134](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) | 原域负坐标与实际纤维；每组合法正枢轴的全部二次像为 $K$。 |
| [044，667c43ecc574e323bcd7b9e4fbd0bbab57d16a14，§§151--166 及定理 202.2](https://github.com/the-omega-institute/trureturing/blob/667c43ecc574e323bcd7b9e4fbd0bbab57d16a14/docs/develop/theory/AURIC_R5_044_RATIONAL_EVALUATOR_QUARTICS_AND_ACTUAL_POSITIVE_PIVOT_CONTROL.md) | 同一固定纤维的六个实际方向及枢轴量词边界；引理 163.1 已给特定偏导 $\partial_{23}:K\to W$ 的原域右逆。二项式域的特定四三系数消失不等于整个 $E_s$ 已确定，本文不用该特定系数推断整个检测秩。 |
| [045，a5a20d82984bbb32282adccee504bbcd41fc7ac1，定义 168.1、定理 168.2、(168.5)、(169.4)、引理 170.1](https://github.com/the-omega-institute/trureturing/blob/a5a20d82984bbb32282adccee504bbcd41fc7ac1/docs/develop/theory/AURIC_R5_045_FAITHFUL_QUARTIC_DETECTION_AND_COMPLETE_ORIGINAL_EVALUATOR_RELATIONS.md) | 唯一四项 $\Psi$、$\ker\Psi=K K$、带极化常数的乘积公式、满射和共同原源提升。 |
| [046，9b1e19f102fb2f399677cae4b720d631afcc1245，约定 175.2、定理 177.2、§§178--179](https://github.com/the-omega-institute/trureturing/blob/9b1e19f102fb2f399677cae4b720d631afcc1245/docs/develop/theory/AURIC_R5_046_EXACT_CUBIC_PRODUCTS_AND_ACTUAL_HIGH_ORDER_FIBRE_CLOSURE.md) | 实际有限完成、原源中的完整 $\mathfrak n^3$ 提升、全部实际二次与四次层。 |
| [048，c15bee0e5b7c49861cea51efc810a606dcceadf5，定理 192.2、193.1、195.2、197.2](https://github.com/the-omega-institute/trureturing/blob/c15bee0e5b7c49861cea51efc810a606dcceadf5/docs/develop/theory/AURIC_R5_048_FINITE_AFFINE_QUARTIC_DETECTION_AND_SIX_DIRECTION_PIVOTS.md) | 原配对 $\beta$、整个实际 $E_s$ 的有限仿射模型及完整原系数入口；有限公式不等于固定纤维的秩已经求出。 |
| [049，f55d41e85ca1cda3fc32def4df3702dbb47dc928，定理 203.2、204.2、205.1、206.2、207.1、208.2、§209](https://github.com/the-omega-institute/trureturing/blob/f55d41e85ca1cda3fc32def4df3702dbb47dc928/docs/develop/theory/AURIC_R5_049_EXACT_COMPLETED_FIBRE_CONDUCTOR_AND_SIX_DIRECTION_WEDGE_SURJECTIVITY.md) | 实际有限图及四次尾映射、精确导子、带正确对偶类型的收缩、六方向外乘满射、长度 $30-d_s$ 和实际嵌入数据的边界。 |

**约定 220.2（消费的经典原始文献）。** Shiro Goto，[*On Buchsbaum Rings Obtained by Gluing*，Nagoya Mathematical Journal **83** (1981)，123--135](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0027763000019449)，DOI [10.1017/S0027763000019449](https://doi.org/10.1017/S0027763000019449)。本文使用其 §1 的条件 (#)、Definition (2.1) 的弱序列等价和 Definition and Lemma (2.3)，印刷页 123--125；这些是 literature-attested 的经典局部代数输入。定理 218.2 已在本实际包含中给出两个方向的普通证明；该文不承担原源提升、实际检测像、原域配对满射或整个缺陷作用。Theorem (2.5) 的 gluing 假设不被省略后套用于本题，也不需另引其所指的较早 Cohen–Macaulayfication 文献。

有限正规化和完成的经典背景沿用 046，约定 175.2 所用的 [Stacks Project，Lemma 10.97.1，Tag 00MA](https://stacks.math.columbia.edu/tag/00MA)。正则参数、Čech 局部上同调与有限长度模的消失仅作为定理 217.1 内部的标准工具；其在本题的参数和消失范围均已明确。

**定义 220.3（新增综合与有界重叠范围）。** 本文的 repo-derived 承重内容是：从同一个实际源构造缺陷的典范阶数正合列，把原配对证明为整个 $A_s$ 作用，在原 $F$ 上证明每个非零上层方向的原始配对满射，取得两个分支的精确 Loewy 与 socle，并将此实际作用接入局部上同调及精确 Buchsbaum 条件。经典 Buchsbaum 判据与 Cohen–Macaulay 工具只在这条实际源推导中消费，不作为新的抽象局部代数定理提出。

仓内有限对应范围为 039--049 的实际纤维、有限层、四次检测与导子相关结果；经典文献对应限于上述 Goto 的确切条件及完成接口。不主张这些有限对应穷尽外部文献或构成全球新颖性结论。044，引理 163.1 及 048，定理 196.1 已支付特定方向的原域满射；定理 214.2 给任意非零 $t\in G$ 的统一结论。049 已有 $\beta$ 的定义、收缩公式及精确导子；本卷所补的是 $B_s/A_s$ 的整个实际作用、每个非零上层方向的满射及其被消费的后果。长度和导子本身不被重新提出为新成果。

**定义 220.4（下一项实际桥梁与结论边界）。** 对已给定且不改变的 $F,D,\theta,s$，尚需确定的实际子空间是

$$
E_s=\Psi\bigl(J_4(A_s)\bigr)\subseteq\det(V)\otimes W,
\qquad d_s=\dim_FE_s.
\tag{220.1}
$$

048 的完整原系数模型及 049，(209.2) 给出这个对象的有限入口，但这里不指定其具体方向或实际数值秩。下一项数学桥梁是把该完整原源入口的值真正确定为指定 $s$ 的 $E_s$；若只问层维数与 Buchsbaum 性，则相应需要其秩或满射与否的证明。符号判据 (218.2) 不改称为该秩已经算出。

所有结论只属于指定的完成局部包含 $A_s\subset B_s$，不确定第七检测方向、十五维检测的存在、六方向枢轴类型的存在或分类，也不计算未完成及全局导子、原完整形式芽或源核。不同纤维不能在同一个作用证明中混用。实际尾映射仍按 049 保留在嵌入环和嵌入导子中，(215.2) 的作用公式没有宣称它们具有齐次代数分裂。本文是普通数学论文的参考输入，不作形式内核认证主张，亦不作 H10、物理或全局算术推论。

## 追加锚（本行以下为增补区）

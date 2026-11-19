# 实际完成正纤维的精确导子与六方向外乘满射

## 202. 同一个十四次域、原系数源与实际完成包含

**定义 202.1（原域与原系数局部环）。** 设 $F$ 为任意特征零域，$D/F$ 为实际可分域扩张，$[D:F]=14$。任取本原元 $\theta$，固定非零体积形式 $\nu:\det_FD\to F$，令

$$
C=\langle1,\theta,\ldots,\theta^6\rangle_F,\qquad
V=F[T]_{\le5},\qquad e_i=T^i,\qquad W=\bigwedge^2V.
\tag{202.1}
$$

对同一个 $D$ 中的七维窗口 $C'$，以包含帧 $E_{C'}$ 定义

$$
P_{C'}(x)=\nu\bigl(\det[E_{C'},M_xE_{C'}]\bigr),
\tag{202.2}
$$

其中 $M_x$ 是这个域中的乘法。换帧只改变公共非零标量，故取射影系数像。在有限 Galois 分裂域内保持原嵌入标签及其固定次序，系数为

$$
P_{C'}(x)=\sum_{|I|=7}c_I(C')x_I,\qquad
c_I=\alpha\epsilon_Ip_Ip_{I^c}.
\tag{202.3}
$$

$p_I$ 为实际帧的递增行子式，$\epsilon_I$ 为互补行序符号，$\alpha$ 来自 $\nu$。令 $S$ 为全部这些原带符号、带标签系数的射影像在 $[P_C]$ 处的原 $F$ 局部环；单个分裂标签函数不自动属于 $S$。令 $\mathcal U$ 为所有 $p_I\ne0$ 的统一开集，连续幂窗口属于 $\mathcal U$。使用 039，定义 111.1、命题 111.2、定理 113.1 的同一个乘法商

$$
X_D=\mathcal U/\bigl((\operatorname{Res}_{D/F}\mathbb G_m)/\mathbb G_m\bigr)
$$

及 Gale 对合 $\iota$，在其有限正规化的唯一上方点取局部环 $B^{\mathrm{loc}}$，记

$$
\mathscr T=\widehat S\hookrightarrow\mathscr B=\widehat{B^{\mathrm{loc}}}.
\tag{202.4}
$$

两边剩余域均为 $F$。实际对合相容横截面采用 042，§133 的原域识别：

$$
\mathscr B=F[[U_1,\ldots,U_{21},Y_1,\ldots,Y_{15}]]^{Y\mapsto-Y},
$$

$$
e_i\wedge e_j\longleftrightarrow
z_{ij}(Y)=Y(\theta^{i+1},\theta^j)-Y(\theta^i,\theta^{j+1}),
\qquad 0\le i<j\le5.
\tag{202.5}
$$

这里 $Y$ 来自对称图模实际 Hankel 轨道方向，$W$ 是负线性坐标空间。固定这组负坐标，约定 $z_{ji}=-z_{ij}$、$z_{ii}=0$。

**定义 202.2（每组预固定的实际正枢轴）。** 令

$$
J_S:\mathfrak m_S/\mathfrak m_S^2
\longrightarrow\mathfrak m_{B^{\mathrm{loc}}}/\mathfrak m_{B^{\mathrm{loc}}}^2
=P_+^\vee\oplus\operatorname{Sym}^2W
$$

为原系数余切映射。任意预先固定一组 $s=(s_1,\ldots,s_{21})\subset\mathfrak m_S$，要求 $J_S[s_i]$ 的正分量构成 $P_+^\vee$ 的一组基。“正”指对合的正特征方向，不要求 $F$ 有序。定义

$$
B_s:=B_{0,s}=\mathscr B/(s)\mathscr B\simeq F[[Y]]^{Y\mapsto-Y},
\qquad \pi_s:\mathscr T\longrightarrow B_s,
$$

$$
A_s=\operatorname{im}\pi_s,\qquad
\mathfrak m_s=\mathfrak m_{A_s},\qquad
\mathfrak n_s=\mathfrak m_{B_s},\qquad
\mathfrak q=(Y)\subset F[[Y]].
\tag{202.6}
$$

实际方程给 $U=\phi_s(Y)=O(Y^2)$，而非直接令原正坐标为零。始终取实际像 $A_s$，不假设 $\ker\pi_s=(s)\mathscr T$。$S$ 是 Noetherian 局部 $F$ 代数，$A_s$ 是其完成的局部商，完备且剩余域为 $F$；$B_s$ 对 $A_s$ 有限，这些局部性质沿用 046，约定 175.2。以下全部结论同时适用于每个 $F,D,\theta$ 和每一组这样的预固定实际原 $F$ 枢轴，所有乘积和源见证均属于这个同一纤维。

**定义 202.3（有限符号与已知原源接口）。** 令

$$
H_j=\operatorname{Sym}^jW,\qquad G=\bigwedge^4V,\qquad
\mu:H_2\longrightarrow G,\quad\mu(ab)=a\wedge b,
$$

$$
K=\ker\mu,\qquad
P_4=\operatorname{im}\bigl(\operatorname{Sym}^2K
\xrightarrow{\mathrm{mult}}H_4\bigr).
\tag{202.7}
$$

$P_4=KK$ 是恰好两个 $K$ 元素相乘的线性张成。固定

$$
\Omega=e_0\wedge\cdots\wedge e_5,\qquad
\mathcal D=\det(V)\otimes W,
$$

$$
\Psi:H_4\longrightarrow\mathcal D,\qquad
\Psi(a_1a_2a_3a_4)=
\sum_{i=1}^4\left(\bigwedge_{j\ne i}a_j\right)\otimes a_i.
\tag{202.8}
$$

实际四次空间、实际检测像及其体积平凡化分别为

$$
J_{4,s}=J_4(A_s)=
\operatorname{in}_4(A_s\cap\mathfrak n_s^2)\subseteq H_4,
\qquad E_s=\Psi(J_{4,s})\subseteq\mathcal D,
$$

$$
E=\{v\in W:\Omega\otimes v\in E_s\},\qquad d=\dim_FE=\dim_FE_s.
\tag{202.9}
$$

取四次符号时，常数和实际二次项必须已经消失。

复用 040，(122.8)、命题 122.2 与 042，引理 134.2 的全部实际二次像 $\operatorname{in}_2(\mathfrak m_s)=K$。复用 045，引理 170.1 的共同原 $F$ 线性提升

$$
u:K\longrightarrow\mathfrak m_S,\qquad
J_S[u(k)]=(0,k),\qquad \pi_s(u(k))=k+O(Y^4),
\tag{202.10}
$$

以及 $P_4\to\mathfrak m_S^2$ 的共同乘积提升。复用 045，定理 168.2 的 $\ker\Psi=P_4$ 和 (168.5) 的极化恒等式；复用其 (169.4)：

$$
\Psi(j_6(\Omega)v)=18\Omega\otimes v\quad(v\in W),
\tag{202.11}
$$

其中 $j_6$ 按 045，(168.2) 的交替完全匹配归一化。因此 $\Psi$ 满射。复用 046，定理 177.2 的完整原源尾项结论：

$$
\pi_s(\mathfrak m_{\mathscr T}^3)
=\mathfrak m_s^3=\mathfrak n_s^3
=B_s\cap\mathfrak q^6.
\tag{202.12}
$$

特别地，对每个 $h\in\mathfrak n_s^3$，可取
$Q_s(h)\in\mathfrak m_{\mathscr T}^3$ 使 $\pi_s(Q_s(h))=h$；这里不要求 $Q_s$ 典范或线性。此接口包括原完成源内的收敛与有限代数乘积见证，不把目标中的闭包当作源像。047，定理 182.2 在 $m=7$ 时给同一阈值三；本卷不重新证明这些精确幂及尾项提升。

普通地说，六阶以后的全部偶级数已有真正原源；导子的剩余问题只在常数、二次与四次三层，但二次方向所携带的真实四次尾项仍须保留。

## 203. 实际截断、代表无关的四阶尾项与双向源见证

**定义 203.1（实际四阶尾项）。** 对 $k\in K$，取 (202.10) 的共同原源提升，写

$$
\pi_s(u(k))=k+t_s(k)+O(Y^6),\qquad t_s(k)\in H_4,
$$

$$
\tau_s:K\longrightarrow H_4/J_{4,s},\qquad
\tau_s(k)=t_s(k)+J_{4,s}.
\tag{203.1}
$$

$t_s$ 为选定原提升的实际四次项，已代入这个 $s$ 的完整实际消元。$\tau_s$ 保留它的代表无关部分；它不是任选的环境四次补偿。

**定理 203.2（实际有限环与全部源像的精确判据）。** 在定义 202.1--202.3 的每组数据中，$\tau_s$ 是与提升选择无关的 $F$ 线性映射。置

$$
R_s=B_s/\mathfrak n_s^3=F\oplus H_2\oplus H_4,\qquad
\overline A_s=A_s/\mathfrak n_s^3\subseteq R_s.
\tag{203.2}
$$

右侧乘法截去 $Y$ 次数至少六的项。实际有限子环恰为

$$
\boxed{\quad
\overline A_s=
\{c+k+q_4:c\in F,\ k\in K,\ q_4\in H_4,\
q_4+J_{4,s}=\tau_s(k)\}.
\quad}
\tag{203.3}
$$

对任意完整偶级数 $f=c+q_2+q_4+h_6$，其中
$h_6\in\mathfrak n_s^3$，有

$$
\boxed{\quad
f\in A_s
\ \Longleftrightarrow\
q_2\in K,\quad q_4+J_{4,s}=\tau_s(q_2).
\quad}
\tag{203.4}
$$

这里每个正向或反向成员资格都针对 $\operatorname{im}(\widehat S\to B_s)$。

证明。$\mu$ 满射，因为每个基四向量都是两个基二向量的外积，故
$\dim K=120-15=105$。$A_s$ 含 $F$，源与目标保持常数。由 (202.12)，模 $\mathfrak n_s^3$ 的商及 (203.2) 均定义良好。

若两次实际提升有相同二次符号 $k$，它们之差属于
$A_s\cap\mathfrak n_s^2$，其四次符号按定义属于 $J_{4,s}$。
所以 (203.1) 不依赖共同提升的选择，甚至允许换成任意实际源提升。取线性提升 $u$ 说明其线性。

若 $f=\pi_s(a)\in A_s$，减去 $c$ 后，其二次项属于全部实际二次像 $K$。再在原完成源中减去 $u(q_2)$；差的实际像二次项为零，故四次项 $q_4-t_s(q_2)$ 属于 $J_{4,s}$。这证明 (203.4) 的必要性，未把任意四次尾项认作零二次实际首项。

反之，设右侧成立，置 $j=q_4-t_s(q_2)\in J_{4,s}$。
按 $J_{4,s}$ 的实际定义，存在 $v_j\in\mathfrak m_{\mathscr T}$，使

$$
\pi_s(v_j)=j+O(Y^6)\in A_s\cap\mathfrak n_s^2.
$$

于是 $\rho=f-c-\pi_s(u(q_2))-\pi_s(v_j)\in\mathfrak n_s^3$。
调用同一个实际源接口 (202.12)，得到完整见证

$$
f=\pi_s\bigl(c+u(q_2)+v_j+Q_s(\rho)\bigr).
\tag{203.5}
$$

该式允许任意给定尾项 $h_6$，不只实现有限环境符号。特别地，取 $q_2=0$，每个齐次 $j\in J_{4,s}$ 本身也有原源见证：将上述 $v_j$ 的六阶尾项用 $Q_s$ 减去即可。由此得 (203.3) 及充分性。证毕。

由 (202.12)，$A_s$ 是 $R_s$ 中这个实际子环的完整逆像：
$A_s=B_s\times_{R_s}\overline A_s$。这是公共理想下的经典拉回描述在本实际源上的应用。此包含也是有限双有理包含：有限性由 046，约定 175.2 给出；另取任意非零 $h\in\mathfrak n_s^3$，则对 $b\in B_s$，$b=(hb)/h$，分子分母都在 $A_s$。$B_s$ 为正规偶级数环，故它是此完成包含在共同分式域中的正规化。这个结论仍只属于 (202.6)，不涉及未完成局部环。

## 204. 导子的有限乘法条件与四次层

**定义 204.1（完成局部导子与极化配对）。** 对指定包含 $A_s\subset B_s$，定义

$$
\mathfrak c_s=\{b\in B_s:bB_s\subseteq A_s\}.
\tag{204.1}
$$

它是包含于 $A_s$ 的最大 $B_s$ 理想，亦为
$\operatorname{Ann}_{A_s}(B_s/A_s)$。$B_s/A_s$ 在这里是 $A_s$ 模，不被当作 $B_s$ 模。

对 $k\in K$、$g\in G$，选 $q\in H_2$ 满足 $\mu(q)=g$，定义

$$
\beta:K\times G\longrightarrow\mathcal D,\qquad
\beta(k,g)=\Psi(kq),
$$

$$
C_s=\{k\in K:\beta(k,G)\subseteq E_s\}.
\tag{204.2}
$$

若另选 $q$，其差在 $K$ 中，乘以 $k$ 后属于 $P_4=\ker\Psi$；故 $\beta$ 与选择无关。这正是 048，定义 192.1、定理 192.2 的同一配对。

**定理 204.2（精确有限导子及两个实际源方向）。** 对每个预固定实际 $s$，导子在 $R_s$ 中恰对应最大包含于 $\overline A_s$ 的 $R_s$ 理想：

$$
\mathfrak c_s/\mathfrak n_s^3
=\{\bar b\in R_s:\bar bR_s\subseteq\overline A_s\}.
\tag{204.3}
$$

其常数层为零，四次层恰为 $J_{4,s}$，且在固定负坐标中有精确嵌入式

$$
\boxed{\quad
\mathfrak c_s=
\{\,k+q_4+h_6:
k\in C_s,\ q_4+J_{4,s}=\tau_s(k),\
h_6\in\mathfrak n_s^3\,\}.
\quad}
\tag{204.4}
$$

特别地，二次符号给典范短正合列

$$
\boxed{\quad
0\longrightarrow J_{4,s}
\longrightarrow\mathfrak c_s/\mathfrak n_s^3
\xrightarrow{\operatorname{in}_2}C_s
\longrightarrow0.
\quad}
\tag{204.5}
$$

证明。$\mathfrak n_s^3$ 是 $B_s$ 理想且已在 $A_s$ 中，所以包含于导子。若 $\bar bR_s\subseteq\overline A_s$，则对每个 $h\in B_s$，$bh$ 与某个实际像元素之差在 $\mathfrak n_s^3$ 中。由 (202.12) 可在原源补上这个差，得到 $bh\in A_s$。反向直接取商。这证明 (204.3)，包括从有限条件返回完整实际像的方向。右端要求乘以 $1$，所以自动包含于 $\overline A_s$；也等于
$\operatorname{Ann}_{\overline A_s}(R_s/\overline A_s)$，此处商只取 $\overline A_s$ 模结构。

设 $b\in\mathfrak c_s$ 的常数为 $c\ne0$。对任意齐次 $q\in H_2\subset B_s$，$bq$ 的二次项为 $cq$，必须在 $K$ 中。这会强制 $H_2=K$，与 $\mu$ 满射到非零十五维 $G$ 矛盾。因此常数层为零。

由定理 203.2，零常数的 $b=k+q_4+h_6$ 属于 $A_s$ 当且仅当
$k\in K$ 且 $q_4+J_{4,s}=\tau_s(k)$。模 $\mathfrak n_s^3$，这样的元素与任意 $q\in H_2$ 相乘只留下四次式 $kq$；与任意 $H_4$ 或更高项相乘则为零。
由 $P_4\subseteq J_{4,s}$ 和 $\ker\Psi=P_4$，

$$
J_{4,s}=\Psi^{-1}(E_s).
\tag{204.6}
$$

确实，若一个四次式与实际 $J_{4,s}$ 元素同检测，其差就在 $P_4$ 中。所以所有 $kq$ 都属于 $J_{4,s}$，恰好等价于
$\beta(k,G)\subseteq E_s$，这里用了 $\mu:H_2\twoheadrightarrow G$。
这证明 (204.4) 的必要条件。

充分性可以直接保留原源见证。先由 (203.5) 取 $a_b\in\mathscr T$，使
$\pi_s(a_b)=b$。对任意目标级数
$h=c_h+q_h+r_h$，其中 $q_h\in H_2$、$r_h\in\mathfrak n_s^2$，有

$$
bh=c_hb+kq_h+\eta,\qquad \eta\in\mathfrak n_s^3.
\tag{204.7}
$$

$k\in C_s$ 保证 $kq_h\in J_{4,s}$。定理 203.2 已给这个齐次四次式本身的原源见证 $a_{kq_h}$；再用 (202.12) 给 $\eta$ 的见证。因此

$$
bh=\pi_s\bigl(c_ha_b+a_{kq_h}+Q_s(\eta)\bigr)\in A_s.
\tag{204.8}
$$

这对每个完整 $h\in B_s$ 成立，故 $b$ 真在导子中，而非仅有一个允许的环境二次符号。反过来，若 $k\notin C_s$，取 $g$ 使
$\beta(k,g)\notin E_s$，再取任意 $\mu(q)=g$。则 $kq\notin J_{4,s}$，所以任何实际二次项为 $k$ 的 $b$ 都有 $bq\notin A_s$。若四次项不满足 $\tau_s$ 条件，则 $b$ 自身已经不在 $A_s$。两种失败均不能被六阶尾项修复。

取 $k=0$ 时，(204.4) 的四次部分恰为 $J_{4,s}$；这些四次式乘以任意零常数目标都进入公共尾理想。对任意 $k\in C_s$，共同原提升 $u(k)$ 有四次项 $t_s(k)$，故其完整像属于导子，二次符号为 $k$。这给 (204.5) 的满射。零二次核恰为 $J_{4,s}$，其注入由齐次四次式模 $\mathfrak n_s^3$ 给出；相同四次符号的实际提升之差在公共尾理想中，故所有箭头与代表选择无关。证毕。

短列 (204.5) 首先是典范的 $F$ 向量空间短列。若将 $J_{4,s}$ 和 $C_s$ 都赋予经 $B_s\to F$ 的剩余域模结构，它也是 $B_s$ 模短列，因
$\mathfrak n_sJ_{4,s}=0$ 且
$\mathfrak n_s(\mathfrak c_s/\mathfrak n_s^3)\subseteq J_{4,s}$。
限制标量也得到 $A_s$ 模短列。中间项一般有非零的正次数乘法，不把它整个赋予平凡模结构，也不声称此列典范分裂。

## 205. 体积配对把二次导子识别为实际对称平方的交

**定理 205.1（有确定对偶类型的二次层）。** 在定义 202.3、204.1 中，外乘给完美配对

$$
G\times W\longrightarrow\det(V),\qquad(g,a)\longmapsto g\wedge a.
$$

因此有自然同构 $G\simeq\operatorname{Hom}_F(W,\det(V))$；固定 $\Omega$ 后得到

$$
\iota_\Omega:G\xrightarrow{\sim}W^\vee,\qquad
g\wedge a=\iota_\Omega(g)(a)\Omega.
\tag{205.1}
$$

这是 $G$ 与 $W^\vee$ 的对应，不是 $G$ 与 $W$ 的未经证明的识别。若

$$
\delta:H_2\longrightarrow W\otimes W,\qquad
\delta(ab)=a\otimes b+b\otimes a,
$$

则对所有 $k\in K$、$g\in G$，

$$
\boxed{\quad
\beta(k,g)=
\Omega\otimes
\bigl((\iota_\Omega(g)\otimes\operatorname{id}_W)\delta(k)\bigr).
\quad}
\tag{205.2}
$$

进而在 $H_2=\operatorname{Sym}^2W$ 中有子空间的实际等式

$$
\boxed{\quad C_s=K\cap\operatorname{Sym}^2E.\quad}
\tag{205.3}
$$

故 (204.5) 成为

$$
\boxed{\quad
0\longrightarrow J_4(A_s)
\longrightarrow\mathfrak c_s/\mathfrak n_s^3
\xrightarrow{\operatorname{in}_2}
K\cap\operatorname{Sym}^2E
\longrightarrow0.
\quad}
\tag{205.4}
$$

证明。对每个基四向量，只有互补的基二向量与它外乘非零，值为 $\pm\Omega$。互补基矩阵可逆，故配对完美，给 (205.1)。

045，(168.5) 在本记号中精确写为

$$
\Psi(kq)=\mu(k)\wedge\delta(q)+\mu(q)\wedge\delta(k).
\tag{205.5}
$$

这里 $g\wedge(a\otimes b)=(g\wedge a)\otimes b$。
$k\in K$ 消去第一项，第二项经 (205.1) 正好给 (205.2)，没有另换检测器或省去极化常数。

由于 $\iota_\Omega$ 满射，$k\in C_s$ 等价于

$$
(\lambda\otimes\operatorname{id})\delta(k)\in E
\quad\text{对每个 }\lambda\in W^\vee.
\tag{205.6}
$$

有限维张量的全部第一因子收缩都在 $E$ 中，恰等价于
$\delta(k)\in W\otimes E$。$\delta(k)$ 在交换两因子下不变，所以它还在 $E\otimes W$ 中。任取 $W=E\oplus E'$，四个张量块直接给

$$
(W\otimes E)\cap(E\otimes W)=E\otimes E.
$$

因此 $\delta(k)$ 是 $E\otimes E$ 中的对称张量。特征零下 $\delta$ 将 $\operatorname{Sym}^2W$ 同构到对称张量子空间：乘法复合 $\delta$ 为二倍恒等，且每个对称张量都由这些极化项张成。相同陈述限制到 $E$，故
$\delta(k)\in E\otimes E$ 恰等价于 $k\in\operatorname{Sym}^2E$。
再与 $k\in K$ 合并，得 (205.3)。这是经过完美配对和张量包含的证明，不是由相等维数猜出同构。证毕。

这一步说明二次导子为何由整个实际 $E$ 控制：一个二次式必须沿所有对偶方向收缩后仍落在 $E$ 中。只知道 $E$ 有多少维，还不能知道哪些具体二次式满足此条件。

## 206. 044 的确切六方向已经外乘满射

**定义 206.1（六个原实际方向）。** 使用 044，(155.5)、(156.6)、定理 157.1 的确切向量

$$
\begin{aligned}
v_0&=2z_{14}-z_{05}-z_{23},&
v_1&=2z_{13}-z_{04},&
v_2&=3z_{12}-z_{03},\\
v_3&=2z_{24}-z_{15},&
v_4&=3z_{34}-z_{25},&
w&=z_{05}+z_{14}-8z_{23},
\end{aligned}
$$

$$
L_6=\langle v_0,v_1,v_2,v_3,v_4,w\rangle_F\subseteq W.
\tag{206.1}
$$

该来源在同一个原 $S$ 中给六个函数，对每个预固定实际 $s$ 的检测值依次为
$2\Omega\otimes(v_0,v_1,v_2,v_3,v_4,w)$。所以始终有
$L_6\subseteq E$，且 $\dim L_6=6$；这里不合并不同枢轴下分别可达的值。

**定理 206.2（六方向的实际外乘映射满射）。** 对任意特征零 $F$，由 (206.1) 这些确切二向量定义的映射满足

$$
\boxed{\quad
\mu:\operatorname{Sym}^2L_6\twoheadrightarrow\bigwedge^4V.
\quad}
\tag{206.2}
$$

因而对每个包含 $L_6$ 的子空间 $E\subseteq W$，

$$
\mu(\operatorname{Sym}^2E)=G,\qquad
\dim_F(K\cap\operatorname{Sym}^2E)
=\binom{\dim E+1}{2}-15.
\tag{206.3}
$$

证明。在固定基 $e_0,\ldots,e_5$ 上引入三个辅助线性算子

$$
\mathsf e(e_i)=ie_{i-1},\qquad
\mathsf f(e_i)=(5-i)e_{i+1},\qquad
\mathsf h(e_i)=(5-2i)e_i,
\tag{206.4}
$$

端点越界项为零。它们按导子作用于外幂与对称幂，并满足
$[\mathsf e,\mathsf f]=\mathsf h$、
$[\mathsf h,\mathsf e]=2\mathsf e$、
$[\mathsf h,\mathsf f]=-2\mathsf f$。
这些恒等式逐个作用于 $e_i$ 即得，外乘映射与三个导子交换。

置

$$
t=2v_0+w=5z_{14}-z_{05}-10z_{23}.
\tag{206.5}
$$

代入 (206.4)，有

$$
\mathsf e(t)=\mathsf f(t)=\mathsf h(t)=0,\qquad
\mathsf e(v_2)=0,\qquad \mathsf h(v_2)=4v_2,
$$

$$
\mathsf f(v_2)=2v_1,\quad
\mathsf f(v_1)=-w,\quad
\mathsf f(w)=-6v_3,\quad
\mathsf f(v_3)=2v_4,\quad
\mathsf f(v_4)=0.
\tag{206.6}
$$

例如 $\mathsf f(z_{ij})=(5-i)z_{i+1,j}+(5-j)z_{i,j+1}$，所以这些式子只使用 (206.1) 的原系数。$L_6$ 正是此五项链与 $Ft$ 的直和，故对三个辅助算子稳定。

在目标 $G$ 中记 $e_{ijkl}=e_i\wedge e_j\wedge e_k\wedge e_l$，$i<j<k<l$。三个明确外乘是

$$
\begin{aligned}
a_8:=v_2\wedge v_2&=-6e_{0123},\\
a_4:=t\wedge v_2&=-3e_{0125}+5e_{0134},\\
a_0:=t\wedge t&=-10e_{0145}+20e_{0235}-100e_{1234}.
\end{aligned}
\tag{206.7}
$$

每式右侧非零。由 (206.6)，$\mathsf e(a_n)=0$、
$\mathsf h(a_n)=na_n$，其中 $n=8,4,0$，且
$\mathsf f(a_0)=0$。

为完整说明三个非零值足够，对任意满足
$\mathsf e(a)=0$、$\mathsf h(a)=na$ 的向量，交换关系归纳给

$$
\mathsf e\,\mathsf f^ja=j(n-j+1)\mathsf f^{j-1}a.
\tag{206.8}
$$

对 $n=8,4$ 和 $0\le j\le n$，这些向量全非零：若第一次为零，(206.8) 会把前一个非零向量乘以非零标量变成零。它们的权 $n-2j$ 互异，所以线性独立。对 $a_8$，$G$ 的最低权为 $-8$，因此 $\mathsf f^9a_8=0$；对 $a_4$，由
$\mathsf f(t)=0$ 与五项链，$\mathsf f^5a_4=t\wedge\mathsf f^5v_2=0$。
故它们分别张成稳定的九维空间 $M_8$ 和五维空间 $M_4$。

这两个空间各自不可约，不需假定 $F$ 代数闭：任何非零稳定子空间先用 $\mathsf h$ 的互异特征值多项式投影取出某个权向量，再用 (206.8) 升到最高向量，最后用 $\mathsf f$ 得到整条链。因此 $M_8\cap M_4=0$，否则交会同时等于两个维数不同的不可约空间。$M_8\oplus M_4$ 没有同时被 $\mathsf e,\mathsf f,\mathsf h$ 消去的非零向量，而 $a_0$ 正是一个这样的非零向量。于是

$$
M_8\oplus M_4\oplus Fa_0
\subseteq\mu(\operatorname{Sym}^2L_6).
$$

右端稳定，因为 $L_6$ 稳定且外乘与算子交换；左端维数为
$9+5+1=15=\dim G$，故等于 $G$。这证明 (206.2)。再由
$L_6\subseteq E$ 得到 (206.3) 的满射，秩核公式给其维数。证毕。

辅助算子只组织明确六向量的外代数计算。它们不被解释为指定 $D$、原源 $S$、实际枢轴 $s$ 或实际子空间 $E$ 的对称性。特别地，证明只要求 $L_6$ 稳定，不要求整个实际 $E$ 稳定。

## 207. 四次导子、二次导子和三种精确长度

**定理 207.1（每个实际纤维的精确数值后果）。** 在定义 202.1--202.3 的每个原域与每组预固定实际 $s$ 下，令
$d=\dim_FE_s$。则 $6\le d\le15$，并有

$$
\boxed{\dim_FJ_4(A_s)=3045+d,}
\tag{207.1}
$$

$$
\boxed{\dim_F\operatorname{in}_2(\mathfrak c_s)
=\dim_F(K\cap\operatorname{Sym}^2E)
=\binom{d+1}{2}-15,}
\tag{207.2}
$$

$$
\boxed{
\begin{aligned}
\operatorname{length}_{A_s}(B_s/A_s)&=30-d,\\
\operatorname{length}_{B_s}(B_s/\mathfrak c_s)
&=151-d-\binom{d+1}{2},\\
\operatorname{length}_{A_s}(A_s/\mathfrak c_s)
&=121-\binom{d+1}{2}.
\end{aligned}}
\tag{207.3}
$$

导子的常数层为零，四次层维数为 $3045+d$，六阶及以上层为完整 $\mathfrak n_s^3$。这些数值不要求先算出 $\tau_s$。

证明。共同六方向给 $d\ge6$，而 $\dim\mathcal D=15$ 给上界。
由 (202.11)，$\Psi$ 的秩是十五；$\dim H_4=\binom{18}{4}=3060$，故

$$
\dim P_4=3060-15=3045.
$$

$P_4\subseteq J_{4,s}$ 且其检测像恰为 $E_s$，所以
$\dim J_{4,s}=3045+d$。定理 205.1 与 206.2 给 (207.2)；这一步用的是整个 $\operatorname{Sym}^2E$ 外乘满射，而非只以六方向独立性估计秩。

现在所有长度都可在公共尾理想模掉以后取维数。由 (203.2)--(203.3)，

$$
\begin{aligned}
\dim_FR_s&=1+120+3060=3181,\\
\dim_F\overline A_s&=1+105+(3045+d)=3151+d.
\end{aligned}
\tag{207.4}
$$

图映射 $\tau_s$ 改变嵌入，却不改变这个向量空间维数。
由 (205.4) 和 (207.2)，

$$
\dim_F(\mathfrak c_s/\mathfrak n_s^3)
=(3045+d)+\binom{d+1}{2}-15
=3030+d+\binom{d+1}{2}.
\tag{207.5}
$$

两环均为剩余域 $F$ 的局部环，出现的各商均有限维。任意这样的有限长度模的每个简单因子都是 $F$，故模长度等于其 $F$ 维数。依次将 (207.4)--(207.5) 相减，正好得到 (207.3)。

具体类型是：$B_s/A_s$ 是有限长度 $A_s$ 模；$B_s/\mathfrak c_s$ 是有限局部 $B_s$ 代数，$A_s/\mathfrak c_s$ 是有限局部 $A_s$ 代数。若统一限制到 $A_s$ 模，则有短正合列

$$
0\longrightarrow A_s/\mathfrak c_s
\longrightarrow B_s/\mathfrak c_s
\longrightarrow B_s/A_s\longrightarrow0.
\tag{207.6}
$$

中间项的 $A_s$ 长度也等于其 $F$ 维数，故三式相容。这里未给 $B_s/A_s$ 添加不成立的 $B_s$ 模结构。证毕。

六方向的作用不是直接给固定纤维补出十五个检测方向；它们的两两外乘已经铺满十五维目标，所以无论整个实际 $E$ 在六方向之上怎样增长，二次导子维数都只由 $d$ 决定。整个导子仍保留下一节的实际四次嵌入数据。

## 208. 精确嵌入式中的真实尾项不能删除

**定义 208.1（检测形式的实际尾映射）。** 以 $\Psi_\Omega:H_4\to W$ 表示
$\Psi(q)=\Omega\otimes\Psi_\Omega(q)$。由 (204.6) 得到同构

$$
H_4/J_{4,s}\xrightarrow{\sim}W/E.
$$

令

$$
\tau_s^\Psi:K\longrightarrow W/E,\qquad
\tau_s^\Psi(k)=\Psi_\Omega(t_s(k))+E.
\tag{208.1}
$$

它与 $\tau_s$ 携带相同信息。$E_s$、$E$、$\tau_s$、$\tau_s^\Psi$ 的值域分别是
$\det(V)\otimes W$ 的子空间、$W$ 的子空间、$H_4/J_{4,s}$ 和 $W/E$，不相互混同。

**定理 208.2（完整嵌入导子及齐次式的充要条件）。** 记
$C(E)=K\cap\operatorname{Sym}^2E$。在固定负坐标中，

$$
\boxed{
\mathfrak c_s=
\mathfrak n_s^3+
\{\,k+q_4:
k\in C(E),\
\Psi_\Omega(q_4)+E=\tau_s^\Psi(k)\,\}.
}
\tag{208.2}
$$

等价地，使用任一共同原源提升给出的实际线性四次项 $t_s$，

$$
\boxed{
\mathfrak c_s=
\mathfrak n_s^3+
\{\,k+t_s(k)+j:k\in C(E),\ j\in J_{4,s}\,\}.
}
\tag{208.3}
$$

这些是 $B_s$ 中实际理想的等式；显示的加法分解只按 $F$ 向量空间理解。特别地，

$$
\mathfrak c_s=C(E)+J_{4,s}+\mathfrak n_s^3
\quad\Longleftrightarrow\quad
\tau_s|_{C(E)}=0.
\tag{208.4}
$$

证明。(208.2)--(208.3) 是 (204.4)、(205.3) 经同构 (208.1) 的改写，所有元素及其乘积的原源见证已由 (203.5)、(204.8) 给出。
若更换 $u$，则 $t_s'(k)-t_s(k)\in J_{4,s}$，这个差可被 $j$ 吸收，所以显示的集合不变。

若 $\tau_s|_{C(E)}=0$，对每个 $k\in C(E)$ 都有
$t_s(k)\in J_{4,s}$，(208.3) 立即成为左侧齐次式。反之，齐次式会使每个纯二次 $k\in C(E)$ 本身属于导子，因而属于 $A_s$；用 (203.4) 且取四次项为零，得到 $\tau_s(k)=0$。这证明充要性。

仅知道 $P_4\subseteq J_{4,s}$，不能消去任意二次提升的四次尾项：$t_s(k)$ 是带二次首项的实际元素的下一项，不是按定义已经零二次的实际首项。只有它在 $H_4/J_{4,s}$ 中为零时，才能用真实零二次源函数及公共尾项把它消掉。证毕。

若某个给定实际纤维满足 $E=W$，则 $J_{4,s}=H_4$，
$\tau_s=0$，从而条件性地有

$$
A_s=F+K+\mathfrak n_s^2,\qquad
\mathfrak c_s=K+\mathfrak n_s^2=\mathfrak m_s.
\tag{208.5}
$$

这只是全检测假设下的后果，不断言任意预固定 $s$ 满足该假设。一般纤维仍使用 (208.2)，不删除 $\tau_s$。

## 209. 有限实际源数据及每个预固定纤维的剩余问题

**定义 209.1（有限数据的原源入口）。** 取原极大理想 $\mathfrak m_S$ 的任意有限理想生成元 $f_1,\ldots,f_N$，例如 048，定义 197.1 的完整原系数展示。将它们在这个固定 $s$ 的实际消元后展开：

$$
\pi_s(f_\alpha)=d_\alpha+e_\alpha+O(Y^6),
\qquad d_\alpha\in K,\quad e_\alpha\in H_4.
$$

记

$$
D_2:F^N\twoheadrightarrow K,\quad
D_2(a)=\sum_\alpha a_\alpha d_\alpha,\qquad
D_4:F^N\longrightarrow H_4,\quad
D_4(a)=\sum_\alpha a_\alpha e_\alpha.
\tag{209.1}
$$

直接复用 046，命题 179.1 的全部实际源公式

$$
J_{4,s}=P_4+D_4(\ker D_2),\qquad
E_s=\Psi D_4(\ker D_2).
\tag{209.2}
$$

若采用 048 的一次居中图，则同一对象还由该卷定理 193.1 表示为
$E_s=\operatorname{im}T_{k_s}$，其全部条目由定义 197.1、定理 197.2 的实际原系数权二、权四项给出。这里仅调用该实际入口，不将某个较小评价子族替代整个源。

**命题 209.2（同一有限源展示读取实际尾映射）。** 对任意 $k\in K$，取 $a\in F^N$ 满足 $D_2(a)=k$，则

$$
\tau_s(k)=D_4(a)+J_{4,s}.
\tag{209.3}
$$

因此 (209.1) 的有限实际二次、四次数据确定精确嵌入导子 (208.2)，不需要数学上另添六阶未知量。

证明。原函数 $\sum_\alpha a_\alpha f_\alpha$ 的实际二次项为 $k$，四次项为 $D_4(a)$；用定理 203.2 的提升无关性即得 (209.3)。若换 $a$，差在 $\ker D_2$ 中，(209.2) 保证四次差属于 $J_{4,s}$。所以公式良定义，且每个所用代表都是真正原源函数的有限线性组合。完整六阶尾项由 (202.12) 吸收。证毕。

这使剩余数据分为精确的三种数学要求。数值长度只需 $d$；二次导子作为 $H_2$ 中的子空间需要实际 $E$，再取
$K\cap\operatorname{Sym}^2E$；完整嵌入导子还需要
$\tau_s$ 在这个交上的限制。若要重建整个嵌入环 $A_s$，则需要 $\tau_s$ 在全部 $K$ 上的值。给出这组必要充分有限数据，不等于已经给出每个预固定 $s$ 的实际条目或秩。

**定义 209.3（固定纤维尚未指定的数学数据）。** 对给定且不改变的 $F,D,\theta,s$，本文不指定 $E_s$ 超出
$\Omega\otimes L_6$ 的具体实际方向，也不指定
$\tau_s|_{C(E)}$ 的实际值或其是否为零。048 的全部有限仿射方程提供计算 $E_s$ 的入口；其是否给每个预固定 $s$ 第七方向、何时达到十五维，以及六方向参数集合是否非空，仍是该卷定义 199.3 所列问题。定理 206.2 的满射属于六方向的外乘，不是 $\Psi(J_{4,s})$ 已满十五维的断言。

同维数并不给固定纤维分类。若两个实际纤维在共同负坐标中有同一个 $E$，则它们的 $J_{4,s}=\Psi^{-1}(\Omega\otimes E)$ 和二次导子相同；它们的嵌入导子相同，当且仅当两个实际 $\tau_s$ 在这个共同二次导子上的限制相同。这由 (208.2) 的每个二次符号上四次仿射纤维相等直接得到。仅有 $\dim E_s$ 相同，不提供该子空间等式或尾映射等式，也不证明实际环的抽象同构。

## 210. 导子结论的普通中文数学解释

**定义 210.1（“精确导子”的具体含义）。** 在同一个十四次实际域里保留原来的七幂窗口和全部符号标签系数，并事先固定合法正枢轴后，先按这些真实方程消掉正方向，再看原完成系数环实际能给出的偶级数。导子收集其中这样的元素：无论再乘上正规化纤维里的哪个偶级数，所得结果仍能由同一个原完成源给出。

六阶以后已有原源，所以判导子只需看前面的有限三层。常数不能留下，因为一个非零常数会迫使所有二次方向都可见，而实际只有一百零五维二次核。四次层则恰是实际的零二次四次空间；它与任何零常数目标相乘都会进入已有的六阶尾部。

真正的限制在二次层。一个二次符号要进导子，必须和每个环境二次式相乘后都落在实际四次空间。忠实检测把这个要求变成一个外积配对；体积配对再把所有外四次方向变成全部对偶收缩。于是允许的二次符号正好是实际检测子空间的对称平方与原二次核的交。每个允许符号确有原系数提升，该提升所带的真实四次尾项也随它一起进导子。

已知六方向虽然未必是全部实际检测方向，其两两外乘却已覆盖十五维外四次空间。因此整个实际检测像若有 $d$ 维，二次导子就恰有
$\binom{d+1}{2}-15$ 维。实际四次层有 $3045+d$ 维；再数常数、二次、四次三层，得到正规化缺失长度 $30-d$ 和两个导子商的精确长度。数字不依赖尾项怎样倾斜，具体嵌入则依赖它。

因而“有限决定”并不是“已经算出每个固定枢轴”。完整原系数的有限二次和四次展开足以决定答案，但这些实际展开所给的整个子空间及尾映射仍须按指定纤维读取。只把六方向外乘满射当成检测满像，或只留下齐次二次符号而删除其真实四次伴随项，都会丢失这个区别。

## 211. 消费的数学来源、有限对应与结论范围

**约定 211.1（固定原族数学前置）。** 以下来源承担各自精确接口；正文中的新原族综合不重新证明它们的完整机制。

| 固定来源 | 本文消费的数学内容 |
| --- | --- |
| [039，e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb，§§111、113、115、117](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) | 原带符号标签系数像、实际乘法商、有限正规化、唯一上方点、剩余域与实际对合横截面。 |
| [040，f32f2d3b8219fae2014e5db4ab3c31575edf0672，定理 122.1 的 (122.8)、命题 122.2](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md) | 完整耦合余切像的正投影与纯负交，保留对偶类型。 |
| [042，fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6，§§132--134](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) | 原负坐标、实际正纤维及每组合法枢轴的全部二次像 $K$。 |
| [044，74b08723d9c5fb45657df8015bfd47a366f7b199，(155.5)、(156.6)、定理 157.1、159.1、163.2](https://github.com/the-omega-institute/trureturing/blob/74b08723d9c5fb45657df8015bfd47a366f7b199/docs/develop/theory/AURIC_R5_044_RATIONAL_EVALUATOR_QUARTICS_AND_ACTUAL_POSITIVE_PIVOT_CONTROL.md) | 同一固定纤维中的六个原函数和确切六向量，以及改变枢轴的量词边界。 |
| [045，a5a20d82984bbb32282adccee504bbcd41fc7ac1，定义 168.1、定理 168.2、(168.5)、(169.4)、引理 170.1](https://github.com/the-omega-institute/trureturing/blob/a5a20d82984bbb32282adccee504bbcd41fc7ac1/docs/develop/theory/AURIC_R5_045_FAITHFUL_QUARTIC_DETECTION_AND_COMPLETE_ORIGINAL_EVALUATOR_RELATIONS.md) | 唯一 $\Psi$ 归一化、精确核 $P_4$、极化、六维右逆及原 $K$、$P_4$ 的共同实际提升。 |
| [046，9b1e19f102fb2f399677cae4b720d631afcc1245，定理 177.2、推论 177.3、§§178--179](https://github.com/the-omega-institute/trureturing/blob/9b1e19f102fb2f399677cae4b720d631afcc1245/docs/develop/theory/AURIC_R5_046_EXACT_CUBIC_PRODUCTS_AND_ACTUAL_HIGH_ORDER_FIBRE_CLOSURE.md) | 整个 $\mathfrak n_s^3$ 的原完成源见证、公共尾理想、实际四次空间与有限原源公式。 |
| [047，e644713d989718374b8ae490ade60d371381837f，定理 182.2、命题 186.1--186.2、187.1](https://github.com/the-omega-institute/trureturing/blob/e644713d989718374b8ae490ade60d371381837f/docs/develop/theory/AURIC_R5_047_EXACT_QUADRATIC_POWERS_AND_UNIFORM_ACTUAL_FIBRE_CUTOFF.md) | 一般实际源有限层与 $m=7$ 时相同的阈值三、二次及四次层；不用其一般精确幂替代新的导子计算。 |
| [048，c15bee0e5b7c49861cea51efc810a606dcceadf5，定理 192.2、193.1、194.2、定义 197.1、定理 197.2](https://github.com/the-omega-institute/trureturing/blob/c15bee0e5b7c49861cea51efc810a606dcceadf5/docs/develop/theory/AURIC_R5_048_FINITE_AFFINE_QUARTIC_DETECTION_AND_SIX_DIRECTION_PIVOTS.md) | 配对 $\beta$、整个实际 $E_s$ 的有限仿射模型、原系数源入口及六方向的 Wronski 对应。 |

**约定 211.2（经典工具只在实际源推导内部使用）。** Daniel Ferrand，[*Conducteur, descente et pincement*，Bulletin de la Société Mathématique de France 131(4)，553--585，Introduction，p.554](https://www.numdam.org/item/BSMF_2003__131_4_553_0.pdf)，以
$\operatorname{Ann}_A(A'/A)$ 定义导子，并给出
$A\simeq A'\times_{A'/I}A/I$。这是 literature-attested 的经典工具。本题的 $A'=B_s$、$I=\mathfrak c_s$；(204.3) 用另一个已知公共理想 $\mathfrak n_s^3$ 作有限截断。相应拉回与乘法判据已在当前包含中逐项证明，文献不承担实际源喷射、$\tau_s$ 或六方向满射。

有限模完成的正合性及张量公式对应 [Stacks Project，Lemma 10.97.1，Tag 00MA](https://stacks.math.columbia.edu/tag/00MA)，作为 046，约定 175.2 的经典完成接口使用。此处不重建其一般理论；(203.5)、(204.8) 的无限尾项成员资格直接使用 046 已有的原完成源提升。

Michael Perlman，[*Regularity and Cohomology of Pfaffian Thickenings*，arXiv:1711.02777v2，§2，(2.1)--(2.2) 及其后最高权、轨道张成段落](https://arxiv.org/html/1711.02777v2#S2)，给对称代数的重复行分解和主 Pfaffian 最高权向量；这是 045 的检测核证明所消费的 literature-attested 经典输入。本卷直接复用 045 的实际核等式和极化，不从 Pfaffian 理想幂、apolar 理想生成或表示目录重新推断 $P_4$，也不重做 046 的尾项证明。

A. Eremenko、A. Gabrielov，[*Degrees of real Wronski maps*，arXiv:math/0108133v4，Introduction，(1)--(3)](https://arxiv.org/html/math/0108133v4)，给 Wronskian 和 Grassmann--Plücker 投影的经典构造。取 $p=2,m=4$，其多项式源次数至多五、目标次数至多八，对应 048 的
$\omega(f\wedge g)=fg'-f'g$ 及 $\ker\omega=L_6$。此对应只解释已知六方向的经典背景；实映射次数不参与本卷的任意特征零外乘证明，也不给固定实际纤维添加对称群。

**定义 211.3（本原族综合与适用边界）。** 本文的 repo-derived 内容是：在实际公共尾理想下以原源见证双向确定导子，将其二次层通过精确体积配对识别为
$K\cap\operatorname{Sym}^2E$，证明 044 确切六向量的外乘满射，进而取得四次层、二次层和三种精确长度，并在嵌入等式中保留实际 $\tau_s$。经典导子、拉回、有限截断及辅助权链只作为这些实际源结论的内部工具，不作为独立的新理论提出。

有限的仓内对应范围为 AURIC_R5_030--048 中的导子、有限层、Pfaffian、Wronski 与六方向相关文字。039--040 的点导子是切空间上的 derivation，不是这里的 conductor ideal；041 的完整低维纤维导子属于次数十、十二，不能给本题次数十四的等号。046 在当前次数给 $\mathfrak n_s^3\subseteq\mathfrak c_s$，047 给一般截断，048 给整个实际检测的有限入口；这些均不被重述为新成果。本卷只在它们留下的实际导子等号、类型识别、六方向乘法和长度上作综合，不声称穷尽仓内、外部文献或全球新颖性。

全部结论只属于指定的完成局部包含 $A_s\subset B_s$。它们不计算未完成或全局导子，不计算 $\ker\pi_s$、完整源余切或完整评价源余切，不给原完整形式芽分类，不推出 H10、物理或算术可判定性结论。对每个预固定实际纤维，未知的 $E_s$ 及实际尾映射仍按定义 209.3 保留；有限必要充分公式不被改称为这些数据已经逐纤维求出。

## 追加锚（本行以下为增补区）

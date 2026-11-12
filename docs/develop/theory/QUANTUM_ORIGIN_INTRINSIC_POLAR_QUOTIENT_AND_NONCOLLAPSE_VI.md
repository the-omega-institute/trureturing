# QUANTUM ORIGIN: BOUNDARY GEOMETRY, INTRINSIC POLAR QUOTIENT AND NONCOLLAPSE VI

> 承接[第五卷第88章][V]：在同一有限维全效应载体上，$(\mathrm B+\mathrm H)\Longleftrightarrow S$。本卷将同一主候选写成两个几何条件：全部二态最小面是整球；对每个纯点，这些球的背面对径点之凸包不进入整体基的相对内部。后一个边界条件等价于内在极性关系不塌缩，后者保留为唯一标量尺的商构造机制。第87—88章的分类、完整原数据及消费者均按其原条件复用；[续卷VII第22—28章][VII]的同秩细化、无独立容量原生入口及终端控制也保持其准确范围。

## 89. 对径凸包的整体边界、唯一标量商与完整量子候选

### 89.1 同一载体与全称二态球条件

**定义 89.1（原载体和既有比较）。** 取非零有限维实向量空间 $V$、闭尖生成凸锥 $C$，以及在 $C\setminus\{0\}$ 上严格正的线性泛函 $u$。始终使用整个紧基 $K=C\cap\{u=1\}$、全部纯点 $P=\operatorname{ext}K$ 和整个 proper 效应区间 $[0,u]_{C^*}$。沿用第88章

$$
F_p=\{f\in[0,u]:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x),\qquad
H(p,q)=K\cap\operatorname{face}_C(p,q).
\tag{89.1}
$$

这里 $p\in P$、$x\in K$；最小锥面取整个面。紧凸分解给 $K=\operatorname{conv}P$、$C=\operatorname{cone}P$、$\operatorname{span}P=V$，凸包指有限凸组合，不要求 $P$ 闭或纯点暴露。完整 $S$ 指每个 $p$ 存在 $e_p\in F_p$，对所有 $h\in F_p$ 有 $h-e_p\in C^*$，且 $e_p(q)=e_q(p)$ 对全部纯点成立；这是真正全锥序最小确认，而非极小确认或局部最小。

**假设 89.2（$\mathrm B$）。** 对每个不同纯点 $p,q$，整个 $H(p,q)$ 仿射同构某个闭欧氏单位球 $B^d$，有限整数 $d\ge1$ 可随面而异。线段 $B^1$ 保留；不预设 Jordan、$B^3$、全局内积、全局概率比较数、谱性、齐性或物理滤子。若 $K$ 是单点，此全称条件为空。

### 89.2 对径支撑关系完全来自球的仿射几何

**定义 89.3（固定纯点的内在关系）。** 固定 $p\in P$，令 $\mathcal F_p=\{H(p,q):q\in P\setminus\{p\}\}$，相同面只计一次。对 $F\in\mathcal F_p$，任选仿射球图 $\chi:F\to B^d$，记 $n=\chi(p)$。因为 $F$ 是 $K$ 的面，$\operatorname{ext}F=P\cap F$，故 $\|n\|=1$。定义

$$
\begin{gathered}
r_{p,F}=\chi^{-1}(-n),\qquad
E_{p,F}=\{a\in\operatorname{ext}F:\chi(a)\cdot n=0\},\\
\mathcal G_{p,F}=\{r_{p,F}\}\cup
\{2a-p-r_{p,F}:a\in E_{p,F}\},\qquad
N_{p,F}=\operatorname{span}_{\mathbb R}\mathcal G_{p,F},\\
\mathcal G_p=\bigcup_{F\in\mathcal F_p}\mathcal G_{p,F},\qquad
N_p=\sum_{F\in\mathcal F_p}N_{p,F}
     =\operatorname{span}_{\mathbb R}\mathcal G_p,\qquad
\mathrm Q_p:\ p\notin N_p,\qquad
\mathrm Q:\ \forall p\in P,\ \mathrm Q_p.
\end{gathered}
\tag{89.2}
$$

空族的和为零，特别是单点基时 $N_p=0$。所有张成都指有限线性组合，虽 $P$ 和面族可无穷。$2a-p-r$ 通常不是原空间的零向量；所要求的是它在下面的标量商中归零，并未把原准备向量或历史标签宣告相等。每个这种生成元只涉及 $p,r,a$ 三个原纯点，其线性提升位于至多三维的张成中；不限制球维数或整个 $V$ 的维数。

定义不依赖球图。事实上，两个球图的过渡保持球心，故为把单位球映到自身的线性变换；它及其逆的球界给范数相等，因而正交。球心的唯一性可由两个对称中心会产生非零平移、与有界性矛盾得到。因此对径和内积为零的赤道集合均不变。这只使用该椭球自身的欧氏结构，不比较不同球的坐标或概率。

为明确这些关系的几何意义，在一个固定面写

$$
\chi^{-1}(s)=c+Js,\qquad c=(p+r)/2,\qquad
p=c+Jn,\quad r=c-Jn,\quad
T=J(n^\perp).
\tag{89.3}
$$

$J$ 是到该面平行空间的线性同构，$u(c)=1$、$uJ=0$。若 $d\ge2$，赤道单位向量张成 $n^\perp$，且 $2a-p-r=2J\chi(a)$；若 $d=1$，赤道为空且 $T=0$。所以在全部维数下，$N_{p,F}=\mathbb Rr+T$。球在对径点 $r$ 的唯一相对支撑超平面为 $r+T$，其线性张成正是 $N_{p,F}$，而

$$
\operatorname{span}F=\mathbb Rp\oplus N_{p,F}.
\tag{89.4}
$$

这是新商桥内部所用的标准球支持与线性代数步骤：$c,Jn$ 由 $p,r$ 张成，其他方向在 $T$ 中；支撑高度 $(t+n\cdot s)/2$ 在 $tc+Js$ 上消灭 $\mathbb Rr+T$、在 $p$ 取一，故交为零。尚未声称这把局部尺有全局正扩张。

同一候选的边界写法只使用这些内在对径：令 $\operatorname{ri}K$、$\operatorname{rbd}K=K\setminus\operatorname{ri}K$ 分别为 $K$ 在 $\operatorname{aff}K=\{u=1\}$ 中的相对内部和相对边界，置

$$
R_p=\{r_{p,F}:F\in\mathcal F_p\},\qquad
\mathrm{Boundary}_p:\quad
\operatorname{conv}R_p\cap\operatorname{ri}K=\varnothing,\qquad
\mathrm{Boundary}:\quad\forall p\in P,\ \mathrm{Boundary}_p.
\tag{89.4a}
$$

若 $K$ 非单点，每个 $R_p$ 非空；按88.11的有限仿射基选择，任选 $r_1,\ldots,r_k\in R_p$ 仿射独立且张成 $\operatorname{aff}R_p$，令

$$
1\le k=\dim\operatorname{aff}R_p+1\le\dim V,\qquad
z_p=\frac1k\sum_{i=1}^k r_i\in\operatorname{conv}R_p\subseteq K.
\tag{89.4b}
$$

$R_p$ 不必闭或有限，凸包仍只指有限凸组合，不先取闭包。单点时不选对径点、仿射基或重心；空对径族的凸包约定为空集，$\mathrm{Boundary}_p$ 为空真。这里的数学凸组合与有限仿射基既不供应实际混态准备，也不构成全域条件的有限操作认证。

### 89.3 边界、非塌缩与完整最小确认

**定理 89.4（内在商的同载体等价）。** 在定义89.1的全部前件下，

$$
\boxed{(\mathrm B+\mathrm{Boundary})\ \Longleftrightarrow
(\mathrm B+\mathrm Q)\ \Longleftrightarrow
(\mathrm B+\mathrm H)\ \Longleftrightarrow\ S.}
\tag{89.5}
$$

$\mathrm H$ 准确沿用88.2：每个纯 $p$ 有同一个 $g_p\in C^*$，$g_p(p)>0$，且它零于全部 $r_{p,F}$；记固定 $p$ 的存在条件为 $\mathrm H_p$。在 $\mathrm B$ 下，非单点时对每个 $p$ 及任意(89.4b)的仿射基均有

$$
\mathrm Q_p\ \Longleftrightarrow\quad
z_p\in\operatorname{rbd}K\ \Longleftrightarrow\quad
\mathrm{Boundary}_p\ \Longleftrightarrow\ \mathrm H_p.
\tag{89.5a}
$$

这些真值与仿射基选择无关：成功时所有这类重心均在相对边界，失败时所有这类重心均在 $\operatorname{ri}K$。主候选采用 $\mathrm B+\mathrm{Boundary}$；$\mathrm Q$ 是同一条件的商表示。在其成立时，无须预付正泛函或 proper 尺，原商唯一给出

$$
V=\mathbb Rp\oplus N_p,\qquad
V/N_p=\mathbb R[p],\qquad
[x]=e_p(x)[p],\qquad N_p=\ker e_p.
\tag{89.6}
$$

非单点时还得到

$$
C^*\cap z_p^\perp=\mathbb R_{\ge0}e_p,
\qquad z_p^\perp=\{g\in V^*:g(z_p)=0\}.
\tag{89.6a}
$$

这说明重心处的相对支撑超平面唯一，不断言零面 $K\cap\ker e_p$ 是 facet；支撑法向唯一并不规定接触面的维数。

商(89.6)所定义的实线性 $e_p$ 正是完整 $S$ 的最小确认；对每个上述整球有

$$
e_p(\chi^{-1}s)=\frac{1+n\cdot s}{2}\quad(\|s\|\le1),\qquad
T_p\!\left(\sum_i\lambda_iq_i\right)
=\sum_i\lambda_iT_{q_i}(p)
\quad(\lambda_i\ge0,\ \sum_i\lambda_i=1).
\tag{89.7}
$$

第二式对任意有限纯准备成立，含重复点和零权；第一式允许任意有限球维及 $B^1$。

证明。先仅设 $\mathrm B$。对固定 $p$，每个不同纯 $q$ 由(89.4)属于 $\mathbb Rp+N_p$，而 $p$ 自己亦属于它；纯点张成 $V$，故

$$
V=\mathbb Rp+N_p.
\tag{89.8}
$$

若 $p\notin N_p$，该和为直和，商恰好一维；$p\ne0$ 来自 $u(p)=1$。由商中相对非零基 $[p]$ 的唯一系数定义 $e_p$，即得实线性、$e_p(p)=1$ 及核等式。到此没有使用正性或 proper 上界。

固定一个球，(89.2)给 $e_p(r)=0$、$e_p(T)=0$。由(89.3)和 $e_p(p)=1$，得到 $e_p(c)=e_p(Jn)=1/2$。把 $s=(n\cdot s)n+s_\perp$ 分解，便有

$$
e_p(tc+Js)=\frac{t+n\cdot s}{2}.
\tag{89.9}
$$

特别是归一球上的值属于 $[0,1]$。遍历每个纯 $q\ne p$ 的整个 $H(p,q)$，再加 $e_p(p)=1$，得到所有纯点上的零一界。现在才由 $K=\operatorname{conv}P$ 和 $C=\operatorname{cone}P$ 推出 $e_p\in[0,u]$；不是把局部效应未经拼合就当成全局效应。它零于全部对径且在 $p$ 取一，故固定 $p$ 已给 $\mathrm H_p$。

为自含地核对完整最小性，任取 $h\in F_p$。在同一个球上写 $h(\chi^{-1}s)=\alpha+v\cdot s$。proper 界和确认给 $\alpha\ge\|v\|$、$\alpha+\|v\|\le1$、$\alpha+v\cdot n=1$。Cauchy–Schwarz 的等号条件遂给

$$
v=\beta n,\quad\alpha=1-\beta,\quad0\le\beta\le\tfrac12,\qquad
h(\chi^{-1}s)-e_p(\chi^{-1}s)
=(\tfrac12-\beta)(1-n\cdot s)\ge0.
\tag{89.10}
$$

此即88.5—88.6的球限制计算，含 $v=0$。对所有纯 $q\ne p$ 得 $h(q)\ge e_p(q)$，同点相等；由纯射线生成整个锥，得到 $h-e_p\in C^*$。在全称 $\mathrm Q$ 下，对每个纯点都已构造上述 $e_q$；再在同一个 $H(p,q)$ 中对 $e_q$ 使用(89.9)，有

$$
e_p(q)=\frac{1+\chi(p)\cdot\chi(q)}2=e_q(p).
\tag{89.11}
$$

所以 $S$ 全部成立，$T_p=e_p$，线性和互反给(89.7)第二式。此正向不使用分类、全局正泛函存在、全局比较数或纯点暴露性。

最小确认也唯一：若 $\widehat e_p\in F_p$ 同样为全锥序最小元，则 $e_p\le\widehat e_p\le e_p$，差在 $C$ 上恒零；$C$ 生成 $V$ 使两者作为线性泛函相等。这里唯一的是最小确认，并不声称 $F_p$ 只有一个 proper 确认。

反过来，在 $\mathrm B$ 下固定 $p$，若 $\mathrm H_p$ 成立，取其同一个 $g_p$。球上写 $g_p(\chi^{-1}s)=\alpha+v\cdot s$，非负性和对径零值给 $\alpha\ge\|v\|$、$\alpha=v\cdot n$，故 $v=\alpha n$、$g_p(p)=2\alpha>0$。于是 $g_p$ 消灭赤道方向 $2a-p-r$ 及 $r$，从而消灭整个 $N_p$；$g_p(p)>0$ 立即推出 $p\notin N_p$。此方向只在新商桥内部使用成熟支持函数等号论证。

现在证明边界入口，并核对它没有预付 $g(p)>0$。设 $K$ 非单点。若 $z_p\in\operatorname{rbd}K$，有限维凸集的相对支撑超平面定理给 $\operatorname{aff}K$ 上非恒定的仿射函数 $\ell$，使 $\ell\ge0$ 于 $K$ 且 $\ell(z_p)=0$。这是成熟凸支撑定理在此处的应用。任取 $x_0\in K$，写 $\ell(x_0+w)=a+\varphi(w)$（$w\in\ker u$），按唯一分解 $V=\mathbb Rx_0\oplus\ker u$ 定义 $g(tx_0+w)=ta+\varphi(w)$。它是 $\ell$ 的唯一齐次线性延伸。每个非零 $c\in C$ 都可写为 $u(c)k$、$k\in K$，故 $g(c)=u(c)\ell(k)\ge0$。因此 $g\in C^*\setminus\{0\}$、$g(z_p)=0$；此时还没有断言 $g(p)>0$。

由所有权重 $1/k>0$ 和 $g(r_i)\ge0$，等式 $0=g(z_p)=k^{-1}\sum_i g(r_i)$ 迫使每个 $g(r_i)=0$。仿射张成再给 $g$ 零于全部 $R_p$。若 $g(p)=0$，则每个 $F\in\mathcal F_p$ 的球心 $c_F=(p+r_{p,F})/2$ 也取零。非负仿射函数在球的相对内点取零，必在整个球取零：对任意 $y\in F$，可取小的 $\delta>0$ 使 $c_F\pm\delta(y-c_F)\in F$，两处非负性给 $\pm\delta g(y)\ge0$，所以 $g(y)=0$。各 $H(p,q)$ 连同 $p$ 覆盖全部 $P$，$\operatorname{span}P=V$ 遂迫使 $g=0$，矛盾。故 $g(p)>0$，得到 $\mathrm H_p$；前述 $\mathrm H_p\Rightarrow\mathrm Q_p$ 的论证给 $\mathrm Q_p$。这样严格正值是结论。

若 $\mathrm Q_p$ 成立，前面的商构造已给非零 $e_p\in C^*$，在 $p$ 取一并零于全部 $R_p$，故也零于 $\operatorname{conv}R_p$。非零正泛函不可能在 $\operatorname{ri}K$ 取零：若取零，同样的相对内点双向微扰使它零于 $\operatorname{aff}K$，进而由 $\operatorname{span}K=V$ 恒零。因此 $\operatorname{conv}R_p\subseteq K\cap\ker e_p\subseteq\operatorname{rbd}K$，得到 $\mathrm{Boundary}_p$。反向，$\mathrm{Boundary}_p$ 与 $z_p\in\operatorname{conv}R_p$ 直接给 $z_p\in\operatorname{rbd}K$。这完成(89.5a)的全部方向。任一仿射基重心都适用相同证明，所以若 $\mathrm Q_p$ 失败，每个重心都属于 $K\setminus\operatorname{rbd}K=\operatorname{ri}K$。

同一论证还证明(89.6a)。任取非零 $g\in C^*$ 且 $g(z_p)=0$，正权重、仿射张成和球心反证再次给 $g|_{R_p}=0$、$g(p)>0$。在每个球上，非负性和对径零值给前述 $\mathrm H_p$ 方向的球公式，因此 $g/g(p)$ 等于(89.9)的局部半内积尺。它在 $p$ 及每个不同纯 $q$ 上均等于 $e_p$，由 $\operatorname{span}P=V$ 得 $g=g(p)e_p$。反向包含由 $e_p\ge0$、$e_p(z_p)=0$ 立即成立；零泛函也在右侧。这是从边界几何导出的唯一支撑射线，不是先选一把正尺再将边界定义成它的零集。

若从 $S$ 出发，复用88.4／88.10的完整逆向及[Library完整桥][L]，先得同载体一般有限 EJA 表示、全部二态整球与 $\mathrm H$，再由已证的 $\mathrm H_p\Rightarrow\mathrm Q_p$ 得 $\mathrm Q$ 及等价的 $\mathrm{Boundary}$。该已归属桥包含正对偶剥离、共同完整框架、忠实自对偶配对、有符号谱性、正面投影、projectivity 与滤波纯性，准确消费 Barnum–Müller–Ududec Theorem 16 的完整前件；不换用强对称的 Theorem 17。等价中的这段分类是复用，不是新分类或隐藏前提。

若 $P=\{p\}$，紧凸分解给 $K=\{p\}$、$V=\mathbb Rp$；$N_p=0$，商系数为 $e_p=u$，且 $F_p=\{u\}$。$\mathrm{Boundary}$ 为空真，$\mathrm Q$、$S$、$\mathrm H$ 直接成立，无须选择不存在的球、赤道、仿射基或重心；(89.5a)的重心命题及(89.6a)仅用于非单点。其余证明未要求纯点集有限、闭或暴露，已覆盖所有声明的退化分支。证毕。

### 89.4 有限失败见证与全空间塌缩

**推论 89.5（失败有有限原几何见证）。** 在 $\mathrm B$ 下，固定纯 $p$。$\mathrm Q$ 在 $p$ 失败，当且仅当有来自(89.2)的有限生成元 $g_1,\ldots,g_m$ 和实系数 $c_j$，使

$$
p=\sum_{j=1}^m c_jg_j.
\tag{89.12}
$$

可取 $g_j$ 线性独立、$m\le\dim V$。此时 $N_p=V$、$V/N_p=0$；成功时商恰好一维，不存在其他商维数分支。

证明。线性张成按定义只用有限组合；从其中取一组基并删去零系数，便得所列独立见证及维数界。反向由(89.12)直接有 $p\in N_p$。(89.8)进一步使失败时 $N_p=V$；成功时用(89.6)。因此失败不是只漏一个局部切向，而是把整个原空间压成零。若企图同时保持 $e(p)=1$ 和所有指定归零关系，(89.12)将给 $1=0$。这些有限维线性代数事实只用于该商桥的失败判据，不另充一般新定理。证毕。

有限见证不是预先固定的有限检测目录：选出的球、赤道纯点和实系数依赖整个原几何，核对一个 $H(p,q)$ 确为整个最小面仍有自己的全域义务。$\mathrm Q$ 的量词遍及全部纯点；证伪有有限关系见证，不推出证真可由有限硬件调用认证。

### 89.5 固定数量的局部不塌缩不能代替拼合

**命题 89.6（在第77章同一条带中的作用域界）。** 复用77.3—77.4的 $2q$ 条带 $r_i,c_j$、原空间 $A_q$、原锥、单位及全 proper 效应，取 $q\ge3$，记 $D=\dim A_q=2q-1$。该同一模型满足 $\mathrm B$，且每个不同纯对的整个最小面均为 $B^1$。固定任一纯 $p$，任意至多 $D-1$ 张属于 $\mathcal F_p$ 的局部关系空间之和不含 $p$，但全部 $D$ 张的和是 $A_q$，所以 $\mathrm Q$ 失败。

证明。已有77.4给全部纯点正是这 $2q$ 点，唯一关系为 $\sum_i r_i=\sum_jc_j$；全效应赋值的充要条件为 $0\le a_i,b_j\le1$、$\sum_i a_i=\sum_jb_j$。若选两个行纯点，令其 $a$ 值为一、其余行值为零，全部列值为 $2/q<1$；这个原 proper 效应的最大值面恰为所选线段。两个列点对称处理。若选一行一列，取77.4的 $e_{ij}$，其一值面恰为这两个点的线段。包含二点的任意面包含该线段，故这正是整个最小面，并非只找到了球形截面。

每张线段的对径是另一个端点、赤道为空，故 $N_{p,H(p,z)}=\mathbb Rz$。唯一关系的全部 $2q$ 个系数都非零，因此删去任一点后余下 $D$ 点线性独立。对至多 $D-1$ 个不同 $z\ne p$，由 $p$ 及这些 $z$ 组成的集合至多有 $D$ 点，仍线性独立，故 $p$ 不在这些局部空间之和中；全部 $D$ 个其他纯点却组成 $A_q$ 的基，故它们之和为整个 $A_q$。重复球图不改变张成。证毕。

给定固定检查数量 $k$，可取 $q\ge3$ 使 $k\le D-1$，便得到所有这类局部检查通过而全局失败。该结论只控制新商条件的拼合范围；条带/free-sum、唯一回路、$S_k$ 层级和无最小确认者均归第77章，不重报为新模型或新 Helly 定理。局部实线性非塌缩也不自动给全域正 proper 扩张；本例正是全域拼合不能省略的控制，不是保留全部 PRE／来源合同的物理反模型。

### 89.6 完整候选保留同一个原装饰元组

**定义 89.7（$\mathsf R_{\rm polar}(\mathcal O)$）。** 取88.6的同一个原装饰元组 $\mathcal O$ 和共同合同 $\mathfrak S(\mathcal O)$，只把每个 $X=A,D,E$ 的 $\mathrm B+\mathrm H$ 替换为在同一 $V_X,C_X,u_X,K_X,[0,u_X]$ 上的 $\mathrm B+\mathrm{Boundary}$。由89.4，它也可等价写为 $\mathrm B+\mathrm Q$，$\mathrm Q$ 供应标量商构造；这是同一个完整主候选的两种表示。其余条件逐项保留如下。

原概率像仍是87.1的 $K_X=\{k_\sigma\}$ 本身，有限仿射维、紧、非空、单位为一，全部中点在原标签中实现；不先补闭包或凸包。原测试像自身闭、含零与单位、闭于中点、补和有界倍增，且每张表由同一个原测试对全部原准备实现，准确保留87.6—87.7的整个全效应入口，不由边界条件或商代付这些条件。

正带质量输出保留87.3的全部原中点实现图，包括重复标签及每个实现同一中点的原标签；保持的是未归一输出而非条件态。原实际加权输入的缩放(87.8)对全部非负质量保留，包括零、次归一和不等质量；归一图律不代付它。其他过程和参考仅在各自已完整凸或满足自身紧有限维中点条件的全部原联合输入域、以及闭尖正输出锥上使用87.4；不满足该域条件者保留原全实下降合同，不能以边缘或乘积输入替换全部相关联合。

用87.4—87.5得到的仍是同一个原实双线性 $L:D\times A\to E$ 和同一个原实线性读回 $p:E\to D$。沿用87.12中同一 $\omega=1_D/m$、$m=\tau_D1_D$ 及派生 $K,M,J,H,B_1,U,G,Q(a,b,c)$ 的原定义，尤其 $K(a)=pL(\omega,a)$、$M(a,b)=pL(K(a),b)$ 使用同一个原 $p$ 两次；此读回符号 $p$ 与89.1—89.5的纯点索引按类型区分。保留两实张成 $\operatorname{span}_{\mathbb R}M(A,A)=D$、$\operatorname{span}_{\mathbb R}L(D,A)=E$，以及所有实 $a,b$ 上的 $Z:B_1M(a,b)=\tau_A(a)Jb$。原正性和两张成先给 $U,G>0$，再定义 $F=\mathsf P_{U^{-1/2}}M$，不预设它等距。

在同一忠实 Jordan 迹坐标中，保留87.13所列 $\Pi_i,\mathsf C_i,\mathsf D_A,\mathcal T$ 的全部定义、含秩一分支的完整(83.8)，以及87.14的两尺度条件：

$$
\begin{gathered}
\Pi_i a_i=\tau_i(a_i)1_i/r_i,\qquad
\mathsf C_i=\begin{cases}I_{A_i},&r_i=1,\\
\Pi_i+\dfrac{r_i-1}{d_i-1}(I_{A_i}-\Pi_i),&r_i>1,\end{cases}\\
\mathsf D_A=(\bigoplus_i\mathsf C_i)^{1/2},\qquad
\mathcal T=H\widetilde F,\\
\|J\mathsf D_A\|_{\rm HS}^2+
\|\mathcal T(\mathsf D_A\otimes\mathsf D_A)\|_{\rm HS}^2
=\|U\|_2^2+\|G\|_2^2,\\
n=\tau_A1_A,\quad e=1_A/n,\quad
\mathsf C_2:\tau_DM(e,e)=1,\qquad G=1_E.
\end{gathered}
\tag{89.13}
$$

这里 $1_i,\tau_i,r_i,d_i$ 是原简单理想的单位、规范迹、秩及实维数。原内积、伴随、二次表示、单位和全部原锥随同一忠实坐标运输；整个 $G=1_E$ 不改成总迹或标量锚。完整(83.8)、全实 $Z$ 及两张成恢复精确 PRE 后，才读取87.15的同一资格集合：用其原 $c_i,n_i,D_{ik},\pi_{ik},\alpha_{ik},\beta_{ik}$，令 $\mathcal I=\{(i,k):n_i,n_k\ge2\}$，要求

$$
\begin{gathered}
\rho\in K_D,\qquad\forall(i,k)\in\mathcal I,\ x=\pi_{ik}\rho:\quad
\alpha_{ik}\alpha_{ik}^*x-x\not\succeq0\ \text{或}\quad
\beta_{ik}\beta_{ik}^*x-x\not\succeq0,\\
T_{\rm raw}(a,c)=L(Ja,c),\qquad
I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1},\qquad
\mathrm H13:\ \exists\rho\in\mathcal H(F),\ I^{\rm raw}\rho\in E_+.
\end{gathered}
$$

这里 $\mathcal H(F)$ 正是上行全部资格条件定义的集合；严格负方向、原迹伴随、未归一单位、非活跃块零质量和空活跃集分支全部保持，所有块共享原总迹一。只检验同一个原资格态的整个原输出，不逐块换态、不由输出反选资格。

共同 $\mathfrak S$ 完整保留原准备、测试的设备／事件／来源绑定出现、全部菜单、过程和分支、实际参考、副本及相关联合、记录、权限、控制、钟和单位、ready／flags、失败、拒绝、停止、销毁、返回、零及不等质量、全部合法未来、旧固定支撑和每个中间切口；原有实际混合服务亦在两侧保留。商 $V_X/N_\xi$ 仅为每个固定纯 $\xi$ 产生一根数学标量尺，不取代 $V_X$ 或任何原对象，不因概率表相等而合并历史和未来。

### 89.7 四个既有完整包的同数据回接

**定理 89.8（完整原数据的等价替换）。** 在定义89.7的同一原来源域内，

$$
\boxed{\mathsf R_{\rm polar}(\mathcal O)
\Longleftrightarrow\mathsf R_{\rm zero\text{-}ball}(\mathcal O)
\Longleftrightarrow\mathsf R_{\rm mid}(\mathcal O)
\Longleftrightarrow\mathsf R_{86}^{\rm ev}(\mathcal O)
\Longleftrightarrow[\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}]^{\rm ev}(\mathcal O).}
\tag{89.14}
$$

证明。87.2、87.7在同一个原像上给定义89.1的完整载体及全效应，87.4—87.5和原缩放给同一个 $L,p$ 及所供应完整域的正性。逐 $X$ 应用89.4，把 $\mathrm B+\mathrm{Boundary}$ 经等价的 $\mathrm B+\mathrm Q$ 换成 $\mathrm B+\mathrm H$，即得第一个等价；四个既有包之间的等价严格复用88.7及87.10。所余原条件逐项相同，故不需重新分类、校准或选择方向。

反向从原评价模型使用87.17—87.18的保锥、保单位线性同构 $\iota_X$；整个最小面及其球几何被运输，对径和赤道也被运输。于是 $R'_{\iota_X\xi}=\iota_XR_\xi$，凸包与 $\operatorname{ri}K_X$ 随同一仿射同构运输，故 $\mathrm{Boundary}_\xi$ 保持。亦有 $N'_{\iota_X\xi}=\iota_XN_\xi$，所以 $\xi\notin N_\xi$ 当且仅当 $\iota_X\xi\notin N'_{\iota_X\xi}$。单点分支随同构仍为单点。两次原 $p$、同一参考、全部原乘积／迹／伴随／中心因子／资格及整个输出仍按88.7的同数据运输；共同来源合同没有被统计商替换。证毕。

### 89.8 每个量子消费者仍支付自己的完整前件

**推论 89.9（逐消费者复用）。** 在(89.14)及下列各消费者自己的完整原前件上，88.8／87.12逐项适用；$\mathrm B+\mathrm{Boundary}$（等价的 $\mathrm B+\mathrm Q$）单独只给一般 EJA 几何，不单独给复型、CP、更新或时间。

证明。Born 消费一般 EJA 忠实桥及同一原精确两接口66.3，得有限复 Hermitian 直和、整个密度基与全效应，概率为 $\Pr(f\mid\rho)=\sum_i\operatorname{Tr}(f_i\rho_i)$；同块纯比较为模方、异块为零，零与不等中心质量保留。复型选择以后才把整二态面缩为 $B^3$ 或跨块 $B^1$，纯经典只有 $B^1$，不把这一结论预付给89.2。

指定二份／三份及读回消费原两实张成、全实 $Z$、完整(83.8)、C2、整个 $G=1_E$ 和精确 PRE 后的原 H13，才得87.20的 $M(a,b)=a\otimes b$、$L(d,c)=d\otimes c$、$p=\operatorname{Tr}_1$、$p_{13}=\operatorname{Tr}_2=(I^{\rm raw})^*$，按全部中央块理解，覆盖整个相关／纠缠锥。另一括号、四份以上共同来源及无限维一致性不随之生成。

指定 CP 对每个实际同载体事件及每个实际分支保留85.15的原实线性 $\Phi_e$、唯一复 HP 延拓、同事件原实线性 $P_{E,e}$，在全部实 $a,b,c$ 上保留精确(87.21)：

$$
\begin{gathered}
P_{E,e}Q(a,b,c)=\alpha_{e,1}Q(\Phi_ea,b,c)+
\alpha_{e,2}Q(a,\Phi_eb,c)+\alpha_{e,3}Q(a,b,\Phi_ec),\\
\alpha_{e,\ell}\ge0,\quad\sum_\ell\alpha_{e,\ell}=1,\quad
S_e=\{\ell:\alpha_{e,\ell}>0\},\\
\ker[(H_\ell)\mapsto\sum_{\ell\in S_e}H_\ell^{(\ell)}\psi_i]
\subseteq\ker[(H_\ell)\mapsto\sum_{\ell\in S_e}H_\ell].
\end{gathered}
$$

同事件记录、ready、参考、副本、控制、钟及未来保留。还须实际供应85.11的每输入块原指定归一纯 $\psi_i$；上行是全部复矩阵 $H_\ell$ 上的核条件，$(\Xi_\psi)_{iii}=(n_i/\sum_jn_j)|\psi_i\rangle\langle\psi_i|$、其余中央块零。测试种子的正权不限制原输入；零腿权、不等维和标量转移仍允许。85.12／85.16才给 $P_{E,e}(\Xi_\psi)\ge0\Longleftrightarrow\Phi_e\ \mathrm{CP}\Longleftrightarrow P_{E,e}$ 全锥正。

HP 提升的全锥正性在这里正是待认证结论，不用87.4先假定全部正输出、再删原实线性和全实来源律；中点下降不供应该指定提升式或实际探针。若已有82.5完整递归参考及原 $P_{D,e}$ 全锥正取得同事件 CP，直接复用；其他 typed 事件保留其原输入输出类型和充分实际参考／递归扩张合同。

Kraus 只在逐块 CP 后给成熟矩形表示 $\Phi_{e,ji}(x)=\sum_\nu K_{e,ji,\nu}xK_{e,ji,\nu}^*$。实际仪器仍保原分支、typed 输入输出、真实参考、旁观者、完整菜单、记录、顺序接线、同族真粗粒化及共同重置的输入行一致；未校准旁观者的局部和联合两预算准确保留87.23，滤波权不混作概率单位。标准归一后，同一完整实际菜单两侧总 TP 才给 Kraus 完备和，次单位仅给 TNI。矩阵分解不供应环境或独立调用。

输入质量 $m$、分支质量 $m_a$、零分支和全部未来保持原域；只在 $m>0$ 时读 $m_a/m$，只在 $m_a>0$ 时取后态 $y_a/m_a$。Lüders 另需同一 CP 分支的锐投影效应、对全部确定接受态的逐点中性及原输出校准，才由69.11得 $x\mapsto PxP$；相同效应和概率不决定更新。物理时间另需原物理时间上的连续、齐次、可逆 $*$ 自同构群、实际逆、原钟、单位及动态来源，才有有限块 Hamiltonian 方程和加标量自由度；无限维正常性、生成元域及收敛仍不由有限维几何支付。以上均为既有消费者的条件应用。证毕。

### 89.9 原生 Born 的两条路线、完整联合菜单与来源边界

**说明 89.10（既有终端结果的准确回接）。** [续卷VII][VII]17.2的旧入口仍有效：保留原实际有限 predictive rank、统计 $\mathrm R_{10}$、uniform ready-return、原射影群与 ready 轨道密度及全部原十一地址 terminal future 时，四真实前缀 $\epsilon,9^5,9,9^6$ 的全未来行关系等价于 native Born。这里有限秩确是该旧入口的独立前件；其(17.9)—(17.11)的同锥、全 proper 和完整混态固定半后果保持原范围。

VII24.1—26.2给不预付容量的更强入口。仍完整保留原 $89$ 维复 Hilbert 载体及其 $\mathbb{CP}^{88}$ 射影几何、$26+63$ 嵌入、唯一 ready、全部原十一地址有限正向字、原矩阵和调用次序、射影群及 ready 轨道密度，终端实际律未知；不预设它为 Born。原非负归一、理想零失败及有限供应／可靠性／成本合同各守原域。令 $P_a=P_{K_ae_0}$、$x_a=(1,(p(af))_{f\in\mathsf W_{11}})$，将此入口的实际行空间记为 $V_{\mathrm w}=\operatorname{span}_{\mathbb R}\{x_a\}\subset\ell^\infty$、范数闭包记为 $\widehat V_{\mathrm w}$，不先假定它有限维或闭合。统计 $\mathrm R_{10}$ 遍及全部原 $a,f$ 和每个地址，$\mathrm{UR}$ 则对每列射线趋于 ready 的实际有限字要求 $\|x_{c_n}-x_\epsilon\|_\infty\to0$，范数先取全部原 terminal futures 的上确界。

VII24.2在统计 $\mathrm R_{10}$ 下给满射实线性预测等距：原逆序九次正向字 $\bar b$ 同时附接于两个比较历史，把全未来行距 $\Delta(a,b)=\|x_a-x_b\|_\infty$ 搬成 $\Delta(a\bar b,\epsilon)$，也保持两射线的距离；它不等同历史、记录、成本或权限，不供应物理逆服务。VII25.1据此给 $\mathrm R_{10}+\mathrm{UR}$ 当且仅当存在唯一连续 $q:\mathbb{CP}^{88}\to[0,1]$ 满足 $p(a)=q(P_a)$（全部原 $a$），正向行延拓先落在 Banach 闭包 $\widehat V_{\mathrm w}$。再加原四前缀的一个**全未来行等式** $x_\epsilon+x_{9^5}=x_9+x_{9^6}$，VII26.1直接消费16.3对全部连续响应的谐和选择：这三项恰等价于存在唯一 proper Born 效果 $0\le E\le I_{89}$，使 $p(a)=\operatorname{Tr}(EP_a)$ 对全部原字成立。这一步不另假设有限次数、有限函数秩或 predictive capacity。

Born 取得后，VII26.2才由同一 Hermitian 线性像推出有限容量和 $V_{\mathrm w}=\widehat V_{\mathrm w}$。非标量分支准确为 $r=7921$，同一个原完成生成锥、归一基及整个数学 proper 区间分别为 $\operatorname{PSD}_{89}$、全部迹一密度和 $[0,I_{89}]$；完整 $S$ 及对任意混态余项的 fixed-half 都是结论。标量分支准确为 $r=1$ 的射线锥和单点基。在这些完成载体上，旧17.2或新26.2所给的 $S$ 均由89.4供应 $\mathrm B+\mathrm{Boundary}$ 及商表示，单点按空族约定。删除的是新原生入口的独立有限秩前件；本卷89.1的有限维全效应域由该后果供应，主候选及其证明并未删去 $\mathrm B$ 或 $\mathrm{Boundary}$。

完整实际有限终端菜单另可直接走VII26.4，不先给粗 Born，也不预付 joint capacity。必须从开始把该确切菜单的全部 typed 结果、原有零及失败／拒绝／停止／告警等坐标纳入同一个联合行 $X_a=(1,(p_\lambda(af))_{(\lambda,f)\in\Lambda\times\mathsf W_{11}})$，保留实际 $p_\lambda\ge0$、$\sum_\lambda p_\lambda=1$，并在这个联合行上支付 joint $\mathrm R_{10}$、joint $\mathrm{UR}$ 和 $X_\epsilon+X_{9^5}=X_9+X_{9^6}$ 的全部原未来关系；联合范数遍取全部标签与 future 的上确界，不丢弃失败后重归一化，也不并入其它程序的记录或销毁类型。在VII24.1的完整原几何、密度及程序域下，这些共同前件等价于唯一共同 POVM，满足 $p_\lambda(a)=\operatorname{Tr}(E_\lambda P_a)$、$\sum_\lambda E_\lambda=I_{89}$。任一 $E_\lambda$ 非标量时联合秩为 $7921$，同一联合完成载体取得整个 PSD、full proper、完整 $S$/full mixed fixed-half，再由89.4取得边界／商表示；全为标量时联合秩一。只在粗行成立的回返或四前缀关系、乃至一个单事件 Born，均不能代付这组联合前件。VII18.1的有限联合秩入口仍在其原范围有效。

对全部细标签，VII22.1—22.3保留另一种入口：独立非恒定粗 Born 加同秩。它固定同一原实际字域 $\mathsf W_{11}$、全部十一地址未来、原 $89$ 路径与 $26+63$ 嵌入、唯一 ready、同一终端、全部 $\Lambda=\Omega_{10}$ 的 $1024$ 个旧有类型标签，以及固定归组 $A=\{\ell:b_1=1\}$；在原理想零失败域保持 $p_\ell\ge0$、$\sum_\Lambda p_\ell=1$，不删失败再归一化。还保留原全 $89$ 维射影密度(10.5)，并独立已知非标量 $0\le E_A\le I_{89}$ 的粗 Born 公式

$$
p_A(a)=\sum_{\ell\in A}p_\ell(a)
=\operatorname{Tr}(E_AP_{\chi_a})
\qquad(a\in\mathsf W_{11}).
\tag{89.15}
$$

令 $x_a^A=(1,(p_A(af))_f)$、$z_a=(1,(p_\ell(af))_{\ell,f})$，$V_A,V_J$ 为各自全部实际行的实张成，$r_A,r_J$ 为其维数，所有未来 $f$ 均遍历同一个 $\mathsf W_{11}$。其完成基、生成锥及单位准确取VII(22.3)，记为 $K_A,C_A,u_A$ 和 $K_J,C_J,u_J$。这些预测载体的下标与89.7的原物理对象须按类型区分。VII(22.5)已在同一粗载体上给 $r_A=89^2=7921$ 和整个 PSD／proper 对应。定理VII22.3的四个等价项正是：

$$
\begin{gathered}
r_J=r_A=7921\\
\Longleftrightarrow\quad
\forall m\ge1,\ a_i\in\mathsf W_{11},\ c_i\in\mathbb R:
\quad\Bigl[\sum_{i=1}^m c_ix_{a_i}^A=0\ \Longrightarrow\ \sum_{i=1}^m c_iz_{a_i}=0\Bigr]\\
\Longleftrightarrow\quad
\forall\ell\in\Lambda\ \exists!e_\ell\in[0,u_A]_{C_A^*}:\quad
p_\ell(a)=e_\ell(x_a^A)\quad(\forall a\in\mathsf W_{11})\\
\Longleftrightarrow\quad
\text{同一原生坐标中存在唯一共同 POVM }(E_\ell)_{\ell\in\Lambda}:\\
p_\ell(a)=\operatorname{Tr}(E_\ell P_{\chi_a})\quad(\forall\ell\in\Lambda,\ a\in\mathsf W_{11}),\qquad E_\ell\ge0,\\
\sum_{\ell\in\Lambda}E_\ell=I_{89},\qquad
\sum_{\ell\in A}E_\ell=E_A.
\end{gathered}
\tag{89.16}
$$

这里每个 $e_\ell$ 在整个同一粗锥上 proper；全部标签和才是 $I$，事件 $A$ 内的和是 $E_A$。(89.16)保持的是任意有限有符号粗行关系，不只是两个当前读数相同。成立时粗投影 $\pi z_a=x_a^A$ 是保单位、保原字作用及生成锥的线性同构，VII(22.10)—(22.11)已给同一联合完成锥的 PSD 表示、完整 $S$/fixed-half、共同射线下降与连续性，并导出全部细标签、全部原前缀和未来上的联合 $\mathrm R_{10}$ 及完整 uniform ready 行回返。因此这些联合结论在该入口中不再是另付前件。粗 Born 可由旧VII17.2连同其原粗有限秩前件供应，也可由新VII26.1在不预付容量下供应；两者各自的原统计回返、uniform ready-return、密度及四前缀全未来关系都保留，并须取非标量分支。若还要 $E_A=Q$，另保留VII10.4／17.2末段的原事件不变性及两项标定，不能由细化反向免除粗供应条件。

证明与边界。上述终端细化直接复用VII22.3，不复制其证明或重报为新推导。在该同一联合完成载体上对已得 $S$ 应用89.4，才有本卷的边界／商表示。VII22.4要求字面原 $N_\ell$ 的识别另付完整校准：共同下降后的 $q_\ell$ 对每个原路径基向量 $e_q$、每个标签均满足 $q_\ell([e_q])=\langle e_q,N_\ell e_q\rangle$，或付足以得到同一识别的支撑／不变性条件；只有粗和 $Q$ 不能决定各个 $N_\ell$。VII22.5的恒定粗分支为 $r_A=1$，同秩恰要求所有细响应恒定；恒定粗事件仍可有非恒定 Born 细化，故此时同秩不再是 Born 细化的必要条件，也不再给整个 $\operatorname{PSD}_{89}$ 粗锥。

VII23.3—23.5给同一原字域上的受限终端历史控制，准确为 $r_A=7921$、$r_J=15842$。它保留联合四前缀全未来锚、有限联合秩、所有标签的 $\mathrm R_{10}$、当前 ready 回返和非恒定粗 Born，却在原字 $0$ 后的固定原未来 $1$ 上违反联合 uniform ready-return，也违反字面细标签支撑／完整校准。因此它没有保持全部粗行有符号关系，只说明这些较弱终端前件不能代付联合下降；它不是VII18.1或26.4的反例，也不是完整原 $\Omega$ 的反模型。在(89.15)—(89.16)入口中已经导出的联合回返和连续性无需重付。VII27的删除条件控制亦只在指定终端数学接口内成立；尤其27.4在无限秩下分开每个固定 future 的回返与 full-future $\mathrm{UR}$，不能把III(150.7)—(150.8)的固定有限分离或固定 future 后果无秩移用。VII18.2的有限坐标证书仍须先有已认证秩及实际分离框架；VII19与22.4均不允许用预选有限 future 或当前读数免费认证全未来同秩。旧有限秩路线及这些有限维后果保持其原条件。

若把这些完成行对象用于原 $A,D,E$，仍须VII20.2的 source-adoption map 及87章全部原像、效应、准备、菜单和共同来源合同，准确保留VII28的原静态、来源及消费者条件。原生复结构、射影几何和原密度仍是前提，不由该下降内生。闭凸完成的每个数学点不自动有实际准备，数学 proper 区间或共同 POVM 也不自动是实际菜单或仪器。终端十一地址全未来结论不供应插入记录后的质量、纯后继、细档案条件核及原七地址条件未来；它们仍消费III150.4、III174—175及VII前八章的完整原合同。同一 POVM 不决定更新。固定来源(23.7)的 analyzer 接受接头、有限返回卷164.1的 active-ready 接头、自然探针与完整实际来源、过程／CP、其他括号／高份数／无限维、真实时间／单位及经验对应继续保留各自边界；无秩原生入口、同秩和本商均不构造这些对象或合法调用。证毕。

### 89.10 几何图像、增量归属与未决问题

**命题 89.11（同一边界候选的唯一标尺及准确简化范围）。** 在 $\mathrm B$ 下，$\mathrm{Boundary}$ 将全局正泛函存在条件改写为局部背面对径之凸包不进入整体内部；$\mathrm Q$ 保留为同一条件的内在关系和商构造表示。(89.5)与(89.14)均是同模型、同数据的等价，没有新增全局正泛函或数值比较输入。这只简化几何入口的表达，不声称独立物理假设净减少、最少公理、全部公理内生或完整量子起源目标完成。

证明与解释。把一个纯点 $p$ 当作灯，把整个 $K$ 当作实心物体。每个经过灯的整球都有一个背面对径；要求把所有这些背面点以有限凸组合拼成一片后，这片仍贴着整个物体的外壳，不钻进整体相对内部。任选一组张成全部背面仿射几何的有限点，它们的平均也在外壳上。外壳在这里给一个共同切面，所有所选背面点的高度都非负，平均高度为零便使每点为零，仿射张成再让全部背面都取零。这里的切面和高度先由边界取得，灯的正高度还没有假定。

如果灯也落在这个零切面上，每个整球的球心就取零；一个对整球非负的仿射高度不能在球心为零而在球内某处为正，否则反方向会变负。因此所有这些球的高度都为零，全部纯点张成原空间又使这把高度恒零，与所取支撑非零矛盾。灯必在另一侧且有严格正高度，可以把灯高定成一。每个球的球心这才固定为半高，球内高度由(89.9)固定为半内积式；它在球上介于零一，遍历纯点和凸组合才给全局零一界。

商构造刻画的正是同一高度。背面对径 $r$ 归零；赤道纯点 $a$ 与直径中点 $(p+r)/2$ 同高，即 $[2a-p-r]=0$。拼合这些二点和三点的关系而不把灯消成零，就是 $\mathrm Q_p$。每个球的其余方向都被这些关系消去，全部纯点又张成原空间，所以商只剩唯一高度方向，得到规范 $e_p$。在同一个球里交换两个灯，内积对称，比较刻度相同；任何全局 proper 确认尺都逐球不低于这把尺，再由纯射线生成给全锥序最小性。这才有唯一 proper 最小互反尺，而不是只在局部取极小值。

原生路线另有一项准确减负：VII24—26不先限制预测行有多少独立方向，而是给两条历史同时接上第二条的逆序九次字，保持两者距离并把第二个比较端搬到 ready；所有未来一起回返，才得到连续响应，再由原四前缀关系选出 Born。之后才算出非恒定时恰为 $7921$ 维，并在该完成几何上应用本卷。它删除独立容量输入，没有删除本卷的两个几何条件，也没有解释原复结构从何而来或取得实际准备／菜单。

其余原来源、尺度、方向和消费者仍按89.7—89.10支付，故(89.14)是完整同数据替换。数学凸组合、仿射基、支持切面及标量商不是装置构造，不授予实际准备、有限认证或合法调用。仓内新增组合是内在关系空间、边界与非塌缩的等价、规范商系数及其全域正性／最小性桥，以及89.6对该条件的局部检查边界。球支持、有限维凸支持定理和线性商是成熟中间工具；有限对径仿射基与重心选择直接复用88.11，88章完整 $S$/EJA、固定半、原接口与消费者、77章条带/free-sum／回路、VII17.2的有限秩原生入口、VII24—26的无独立容量 Born／完成PSD／联合菜单、VII22.3—22.5的同秩细化／校准／恒定分支及VII23、27的受限终端控制均为复用，VII28的完整消费者和来源边界也按原条件保留，均不取得本卷新意名义。证毕。

**开放问题 89.12（保留的逻辑与来源缺口）。** 在同一全效应载体上，单独 $\mathrm B+\mathrm{Z0}$ 是否已推出 $\mathrm A$／$\mathrm H$，仍为本卷未解问题：需要把全部球对径放进一个共同正零面，或给出满足全部这些前件而不满足该结论的真实反例。89.6不声称满足 $\mathrm{Z0}$，因而不回答此问。相较之下，$\mathrm B+\mathrm{Boundary}$ 经等价的 $\mathrm Q$ 到同载体完整 $S$ 没有另留扩张缺步；到同原来源量子包仍须89.7的全部非几何合同和89.9的来源映射。VII26.1—26.4在其完整原前件下已取得的 Born／联合POVM、容量及完成几何，以及独立非恒定粗 Born、原密度和同秩下由VII22.3取得的联合下降／回返，均不列作未解；复结构起源、实际来源、记录后条件未来与各过程消费者仍须其原合同，数学边界和商均不能代付。

完整量子 $\operatorname{Herm}_n(\mathbb C)$ 中，固定秩一纯 $p$ 的确认集形如 $p\oplus A$、$0\le A\le I_{n-1}$，其仿射维数为 $(n-1)^2$：$I-F\ge0$ 与确认迫使交叉块为零，余块的区间有内部。因此不能把确认集统一限制为至多二维；本卷所有论证均未使用这种限制。

数学归属采用 `repo-derived` 表示89.4中边界／非塌缩／规范商拼合的纸面推导及其同数据应用，已知工具和既有桥按上列原文引用；有限来源阅读不支持全球原创、历史优先权或文献完整性结论。这里的定义、证明和条件推论属于普通纸面数学，不声称 Lean kernel 核验、物理来源实现或整体目标完成。

[V]: QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md
[L]: ../../../Library/QuantumStates/mullerududec2012selfduality.md
[VII]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_VII.md

## 追加锚（本行以下为增补区）

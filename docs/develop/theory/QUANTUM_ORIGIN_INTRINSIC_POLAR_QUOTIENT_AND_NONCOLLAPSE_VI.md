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

## 90. 稀疏实PSD的零拼合传递性与一般效应延拓缺口

### 90.1 原图锥、全部效应与三纯态条件

**定义 90.1（同一稀疏实矩阵载体）。** 令 $G$ 为顶点集 $\{1,\ldots,n\}$ 上任意有限简单图，$n\ge1$，置

$$
\begin{gathered}
V_G=\{X\in\operatorname{Sym}_n(\mathbb R):X_{ij}=0\text{ 若 }i\ne j,\ \{i,j\}\notin E(G)\},\\
C_G=V_G\cap\operatorname{PSD}_n(\mathbb R),\qquad
u_G(X)=\operatorname{tr}X,\qquad
K_G=C_G\cap\{u_G=1\},\qquad P_G=\operatorname{ext}K_G,\\
i\sim_G j\quad\Longleftrightarrow\quad i=j\text{ 或 }\{i,j\}\in E(G).
\end{gathered}
\tag{90.1}
$$

始终取整个 $V_G,C_G,K_G,P_G$ 和整个 $[0,u_G]_{C_G^*}$，按89.1、88.1定义 $F_p,T_p,p\perp x,D_p$；$\mathrm{Z0},\mathrm B,\mathrm A,\mathrm H,S,\mathrm{Boundary},\mathrm Q$ 均保留88—89章的原义。另记仅限制两个被排除端点为纯点的条件

$$
\mathrm{Z0}_{\rm pure}:\quad
\forall p,q,r\in P_G,\qquad
[p\perp q\ \land\ p\perp r]\ \Longrightarrow\ p\perp(q+r)/2.
\tag{90.2}
$$

它仍用原全效应中的见证和原 $K_G$ 的中点；两个前件可用不同效应，后件须有一个同时确认 $p$、排除该中点的原效应。不要求不同的 $q,r$，也不删其余纯点或混态。

**命题 90.2（载体完备性与效应的正确类型）。** 定义90.1满足89.1的全部有限维锥基条件。迹内积使每个 $f\in V_G^*$ 有唯一稀疏对称代表 $A_f\in V_G$，$f(X)=\operatorname{tr}(A_fX)$；但在一般 $G$ 上，正性和 proper 性准确要求的是

$$
\operatorname{tr}(A_fX)\ge0,\qquad
\operatorname{tr}((I-A_f)X)\ge0\quad(\forall X\in C_G),
\tag{90.3}
$$

不能改成 $A_f\ge0$ 和 $I-A_f\ge0$，也不要求存在同一个环境矩阵 $0\le E\le I_n$ 代表这个限制效应。此处没有把 $C_G$ 换成PSD完成锥，亦没有把 $C_G^*$ 认成 $C_G$。

证明。$V_G$ 含 $I_n$，为非零有限维实空间。$C_G$ 是闭凸PSD锥与线性空间的交，闭、凸、尖。对每个 $X\in V_G$，足够小的 $\epsilon>0$ 使 $I_n\pm\epsilon X$ 正定，故 $C_G$ 生成整个 $V_G$。非零PSD矩阵有严格正迹；迹一PSD矩阵的非负特征值之和为一，因而有界，$K_G$ 又闭，故紧且非空。按有限维紧凸分解，$K_G=\operatorname{conv}P_G$，$C_G=\operatorname{cone}P_G$，不要求 $P_G$ 闭。

迹内积在 $V_G$ 上非退化，给所述唯一代表；对偶锥的定义正是(90.3)的第一式，补正性给第二式。若 $0\le E\le I_n$，限制确是 proper；逆向不是定义，90.4将给不能如此表示的原 proper 效应。以上只证明原稀疏PSD锥本身的条件，没有增补状态或缩小效应。证毕。

### 90.2 realROG与弦图的整个二态最小面

**引理 90.3（实秩一生成截面的全最小面）。** 令 $C=L\cap\operatorname{PSD}_m(\mathbb R)$ 是非零实谱截面，在其张成上取迹一基；若 $C$ 是ROG，即由它所含的秩一PSD矩阵生成，则每个不同纯对的整个归一最小面均为 $B^1$ 或 $B^2$。特别地，每个弦图的原 $C_G$ 满足 $\mathrm B$。该结论不把非弦图的全部纯点假定成秩一。

证明。直接复用 Hildebrand，*Spectrahedral cones generated by rank 1 matrices*，[arXiv:1409.4781v2 Lemma 3.9及其后面公式](https://arxiv.org/html/1409.4781v2#S3.SS2)：ROG的极射线恰为其中秩一射线，且一般谱截面在 $X$ 处的整个最小面为

$$
\operatorname{face}_C(X)
=C\cap\{Y:\operatorname{ran}Y\subseteq\operatorname{ran}X\}.
\tag{90.4}
$$

公式中的集合是整个面：右侧显然为含 $X$ 的面；对其中任一 $Y\ge0$，$X$ 在自身像空间上正定，故某个 $\epsilon>0$ 使 $X-\epsilon Y\ge0$ 且仍在 $L$，于是任一含 $X$ 的锥面必须含 $Y$。这也自含地核对了所用面公式，不以某个球截面代替它。

写两个不同归一纯点为 $p=vv^T,q=ww^T$，$\|v\|=\|w\|=1$，则 $v,w$ 线性独立。令 $U=(v\ w)$，$W=\operatorname{span}\{v,w\}$。包含 $p,q$ 的最小锥面等于 $p+q$ 的最小面，故由(90.4)恰为

$$
\{UAU^T:A\in L_W\cap\operatorname{PSD}_2\},\qquad
L_W=\{A\in\operatorname{Sym}_2:UAU^T\in L\}.
\tag{90.5}
$$

$L_W$ 包含两个对角矩阵单位，所以维数只有二或三。二维时它就是全部对角矩阵，整个锥面恰为 $\mathbb R_+p+\mathbb R_+q$，迹一基恰为线段 $[p,q]=B^1$。三维时 $L_W=\operatorname{Sym}_2$，整个锥面为完整实PSD二阶锥。令 $Q=U^TU>0$，其归一条件为 $\operatorname{tr}(QA)=1$；合同变换 $B=Q^{1/2}AQ^{1/2}$ 将整个基双射到全部迹一PSD二阶矩阵。后者在坐标 $s=(B_{11}-B_{22},2B_{12})$ 中恰为闭单位圆盘 $B^2$。因此两种分支都控制整个最小面。

弦图部分只复用同文 [Lemma 5.1](https://arxiv.org/html/1409.4781v2#S5.SS1)：该稀疏PSD锥ROG当且仅当图弦。对弦图应用上述论证即得结论；无需重证ROG分类。一般非弦图部分不使用这条纯点描述，也不在这里分类其二态面。证毕。

### 90.3 任意诱导三点链的精确零拼合障碍

**命题 90.4（原全效应上的四分之一缺口）。** 若 $G$ 含诱导三点链 $a-b-c$，即有边 $ab,bc$ 而无边 $ac$，则下列三个原纯点给

$$
\begin{gathered}
v=(e_a+e_b)/\sqrt2,\qquad w_\pm=(e_b\pm e_c)/\sqrt2,\\
p=vv^T,\qquad q_\pm=w_\pm w_\pm^T,\qquad
m=(q_++q_-)/2=(e_be_b^T+e_ce_c^T)/2,\\
T_p(q_+)=T_p(q_-)=0,\qquad T_p(m)=\tfrac14.
\end{gathered}
\tag{90.6}
$$

这些量词和最小值均在整个原 $[0,u_G]_{C_G^*}$ 中，不只在三顶点子模型中。任意额外顶点、允许边及非弦结构均不破坏见证。

证明。三个矩阵均稀疏可容许、PSD且迹一。任一秩一PSD射线在环境PSD锥中极端，故在其任一含该射线的子锥中亦极端，因此 $p,q_\pm\in P_G$；未用一般纯点秩一的断言。

在整个 $V_G$ 上定义

$$
f_\pm(X)=\tfrac12(X_{aa}+X_{bb}+X_{cc})+X_{ab}\mp X_{bc}.
\tag{90.7}
$$

由于原来就有 $X_{ac}=0$，对全部 $X\in C_G$，

$$
\begin{aligned}
f_\pm(X)&=\tfrac12(e_a+e_b\mp e_c)^TX(e_a+e_b\mp e_c)\ge0,\\
(u_G-f_\pm)(X)&=\tfrac12(e_a-e_b\mp e_c)^TX(e_a-e_b\mp e_c)
+\sum_{i\notin\{a,b,c\}}X_{ii}\ge0.
\end{aligned}
\tag{90.8}
$$

所以同一个 $f_\pm$ 与自己的补在整个原锥上共同为正，$f_\pm\in[0,u_G]$。直接代入给 $f_\pm(p)=1$、$f_\pm(q_\pm)=0$，故两个零最小值确由原效应达到。二次型中的向量只支撑这三个坐标，余项是原非负对角元，额外边不进入证明。

现在约束所有原确认者。任取 $f\in F_p$，将它限制到支撑在 $\{a,b\}$ 的完整PSD二阶子锥。这一限制由唯一 $2\times2$ 矩阵 $A$ 表示，原正性和补正性使 $0\le A\le I_2$。$v^TAv=1$ 迫使 $(I_2-A)v=0$；在 $v$ 及其单位正交向量构成的基中，$A=vv^T+\beta v_\perp v_\perp^T$，$0\le\beta\le1$。所以

$$
f(e_be_b^T)=A_{bb}=(1+\beta)/2\ge\tfrac12,
\qquad f(e_ce_c^T)\ge0,
\qquad f(m)\ge\tfrac14.
\tag{90.9}
$$

这是对全部 $f\in F_p$ 的下界，不是仅检查(90.7)。另一方面，$g(X)=\operatorname{tr}(pX)$ 是环境秩一投影效应的限制，故在原锥上 proper，且 $g(p)=1,g(m)=1/4$。下界精确可达，得到(90.6)。

(90.7)还说明为何不能缩成环境效应。若某个环境 $0\le E\le I_n$ 在原空间上代表 $f_\pm$，确认和排除将迫使 $Ev=v$、$Ew_\pm=0$，从对称性得到 $v^Tw_\pm=0$；但这里 $v^Tw_\pm=1/2$。因此这两个原 proper 效应都没有这样的环境代表。(90.8)对效应与补分别使用PSD二次型，并没有把两个不同的缺边条目补成同一个环境零一有界矩阵。证毕。

**命题 90.5（局部线段的对径仍可全域不可排除）。** 在同一诱导链和同一全载体上，令

$$
v_0=(e_a+\sqrt3e_b)/2,\qquad
w_0=(\sqrt3e_b+e_c)/2,\qquad
p_0=v_0v_0^T,\quad r_0=w_0w_0^T.
\tag{90.10}
$$

则 $H(p_0,r_0)=[p_0,r_0]=B^1$，两个端点在这个整最小面内互为对径，但不存在 $f\in[0,u_G]$ 使 $f(p_0)=1,f(r_0)=0$。特别地，单取图 $P_3$ 时整个模型满足 $\mathrm B$ 而违反 $\mathrm A$；它也违反 $\mathrm{Z0}$，不是一般 $\mathrm B+\mathrm{Z0}$ 的反例。

证明。$p_0,r_0$ 为原秩一纯点。令 $U_0=(v_0\ w_0)$。在(90.4)给出的整个最小面里，任一矩阵唯一写成 $U_0AU_0^T$，$A\ge0$。其 $ac$ 条目为 $A_{12}/4$，所以原缺边迫使 $A_{12}=0$。反向，全部非负对角 $A$ 都给原锥中的 $p_0,r_0$ 非负组合；故整个归一最小面恰为所述线段。

若有这样的 $f$，其在原完整 $ab$ 子锥上的效应矩阵 $A$ 确认 $v_0$，如90.4给 $f(e_be_b^T)\ge3/4$。在完整 $bc$ 子锥上的效应矩阵 $B$ 则满足 $0\le B\le I_2$、$Bw_0=0$，所以 $B=\gamma w_0^\perp(w_0^\perp)^T$、$0\le\gamma\le1$，给同一个 $f(e_be_b^T)\le1/4$，矛盾。这两个限制必须是同一个原效应在重叠坐标上的限制，不能各选一把不相容的尺。图 $P_3$ 弦，90.3给其全称 $\mathrm B$，90.4给其 $\mathrm{Z0}$ 失败。证毕。

### 90.4 所有有限图的传递性定理

**定理 90.6（零拼合强迫原图块闭合）。** 对定义90.1的任意有限简单图，不要求弦，有严格同载体等价

$$
\boxed{
\mathrm{Z0}\ \Longleftrightarrow\ \mathrm{Z0}_{\rm pure}
\ \Longleftrightarrow\ (\sim_G\text{ 传递})
\ \Longleftrightarrow\ (G\text{ 的每个连通分量完全})
\ \Longleftrightarrow\ S.}
\tag{90.11}
$$

这些条件成立时，原锥本身就是实PSD块直和；全部纯点、整个紧基及全效应同时取得 $\mathrm B,\mathrm A,\mathrm H,\mathrm{Boundary},\mathrm Q$。对每个纯 $p$，其全锥序最小互反确认及对任意原混态的最小值准确为

$$
e_p(X)=\operatorname{tr}(pX),\qquad T_p(x)=e_p(x)
\quad(X\in V_G,\ x\in K_G).
\tag{90.12}
$$

证明。$\mathrm{Z0}$ 当然蕴含(90.2)。若某个连通分量不完全，在其中选一对不相邻顶点及一条最短连接路；该路至少两条边，前三点形成诱导 $P_3$，否则有弦可缩短路。90.4在原全效应中给三个纯点满足两个零前件而中点最小值为 $1/4$，违反(90.2)。因此 $\mathrm{Z0}_{\rm pure}$ 强迫每个连通分量完全。原关系 $\sim_G$ 已反身、对称；其传递性恰使每条路的端点相邻或相等，等价于每个连通分量完全。

设分量为 $I_1,\ldots,I_k$，均完全。仅重排原坐标就有准确等式

$$
V_G=\bigoplus_{j=1}^k\operatorname{Sym}_{|I_j|}(\mathbb R),\qquad
C_G=\bigoplus_{j=1}^k\operatorname{PSD}_{|I_j|}(\mathbb R),\qquad
u_G(X)=\sum_j\operatorname{tr}X_j.
\tag{90.13}
$$

不是在另一个完成锥中取得这张表示。实谱分解表明全部纯点恰为某一个块中的迹一秩一投影：跨块有两份正质量或块内秩大于一都会给非平凡凸分解；秩一的极端性已在90.4说明。迹配对下每个正泛函由一个块对角PSD矩阵表示，因为测试全部块内秩一投影即可判正；全 proper 区间恰为各块 $0\le A_j\le I_j$。

固定任一纯 $p=vv^T$。对任一原确认者 $f_A$，$v^TA_jv=1$ 迫使 $A_jv=v$，故在该块上 $A_j=p\oplus A_{j,\perp}\ge p$，其余块仍非负。因此 $f_A-e_p\in C_G^*$；而 $e_p$ 自己 proper且确认 $p$。这给整个锥序的least元，而非仅在所选三纯点上最小。所有纯 $p,q$ 上有 $e_p(q)=\operatorname{tr}(pq)=e_q(p)$，故完整 $S$ 成立，(90.12)对整个基成立。

同块不同纯对的整个最小锥面是支撑在两向量张成上的完整PSD二阶锥，归一基为 $B^2$；不同块的整个最小面是两射线的直和，归一基为 $B^1$。故有 $\mathrm B$。任一这种球中纯 $p$ 的对径是同秩二支撑内与它正交的秩一投影，或异块的另一端点；$e_p$ 均将其排除，所以 $\mathrm A$ 和 $\mathrm H$ 成立。89.4直接给原 $\mathrm{Boundary},\mathrm Q$，不重证其商构造。

最后，对任意原载体，$S$ 已使 $D_p=\{x\in K:e_p(x)=0\}$：全锥序最小性迫使任一零见证的零点亦为 $e_p$ 的零点，反向由 $e_p$ 自己见证。这个零集凸，故 $S\Rightarrow\mathrm{Z0}$。这闭合(90.11)所有方向。$n=1$ 时是单射线、单点基，$e_p=u_G$、$D_p=\varnothing$，球和对径条件空真；多个孤立顶点则是整个经典单纯形，保留所有跨块线段。证明从未要求一般非弦图的全部纯点秩一。证毕。

### 90.5 一般载体中A的逐效应延拓含义

**定义 90.7（原基范数与限制映射）。** 返回89.1的任意原有限维全效应载体，不附加图表示。在一个整个二态球 $F=H(p,q)$ 上，令 $[0,1]_{\rm aff(F)}$ 表示全部取值于 $[0,1]$ 的实仿射函数；对单点或线段采用同一定义。原限制映射和原基范数分别为

$$
\begin{gathered}
\operatorname{res}_F:[0,u]_{C^*}\longrightarrow[0,1]_{\rm aff(F)},\qquad f\longmapsto f|_F,\\
\|z\|_C=\min\{u(a)+u(b):a,b\in C,\ z=a-b\}.
\end{gathered}
\tag{90.14}
$$

范数使用原锥和原质量，不用某个球的局部范数，也不先配自对偶内积。

**命题 90.8（A恰为全部球效应逐一可延拓）。** 在89.1及 $\mathrm B$ 下，$\mathrm A$ 当且仅当每个整个二态球的 $\operatorname{res}_F$ 都满射。这里准确为 $\forall F\ \forall h\ \exists f$，不要求选择 $h\mapsto f$ 保持线性或正性，不供应共同正线性扩张、滤子、面投影或可调用装置。

证明。固定球图 $\chi:F\to B^d$。任一球 proper 效应写成 $h(s)=\alpha+v\cdot s$，其中 $\|v\|\le\min(\alpha,1-\alpha)$。若 $v\ne0$，令 $n=v/\|v\|$，$b_n(s)=(1+n\cdot s)/2$，则

$$
h=(\alpha-\|v\|)\,1+2\|v\|\,b_n+(1-\alpha-\|v\|)\,0.
\tag{90.15}
$$

三个系数非负且和为一。$\mathrm A$ 给某个原 $f\in[0,u]$，在纯 $\chi^{-1}n$ 取一、在其对径 $\chi^{-1}(-n)$ 取零。球上的非负与补非负迫使 $f|_F=b_n$，正是(89.10)的 $\beta=1/2$ 分支。因此用同一组凸系数组合 $u,f,0$，便延拓 $h$。若 $v=0$，直接用 $\alpha u$。$d=1$ 时单位方向只有两个，公式同样成立，不丢线段。

反向，满射使每个 $b_n$ 有原 proper 延拓，该延拓就是相应对径的全域排除见证，故有全部 $\mathrm A$。若 $K$ 单点，无不同纯对，$\mathrm A$ 和所述全称满射条件均为空真；若另问该单点本身的效应延拓，常数 $\alpha$ 由 $\alpha u$ 延拓。命题只证明逐效应存在：上述选择随 $n$ 可不同，不能由此断言存在一个共同正线性右逆。它是旧 $\mathrm A$ 的准确等价表述，不是删去 $\mathrm A$ 后另得的弱公理。证毕。

**命题 90.9（全域排除与带质量捷径）。** 在89.1的原载体上，对任意 $p,r\in K$，以下等价：

$$
\begin{gathered}
\exists f\in[0,u]:f(p)=1,\ f(r)=0;\\
\|p-r\|_C=2;\\
\nexists\ t\in(0,1),\ x,y\in K:\quad p+t y=r+t x.
\end{gathered}
\tag{90.16}
$$

因此在 $\mathrm B$ 下，$\mathrm A$ 恰说每个局部对径对在这个原基范数中仍相距二，亦即这些局部对径对全部没有(90.16)的带质量捷径。

证明。这里只使用成熟基范数／序单位极性；其标准形式见 L. Lami、C. Palazuelos、A. Winter，*Ultimate data hiding in quantum mechanics and beyond*，[arXiv:1703.03392v2 §II.1 Definition 2、Lemma 3](https://arxiv.org/html/1703.03392v2#S2.SS1)。为核对原质量与量词，给出所需自含论证。

生成性保证 $z=a-b$ 的可行分解；质量有界的 $a,b\in C$ 分别位于某个 $[0,M]K$，这个集合紧，所以(90.14)的下确界可达。其单位球恰为 $\operatorname{conv}(K\cup-K)$：质量和至多一的分解给该凸包中的点，反向将正负凸组合分组即给质量和至多一的分解；不足的权重可放在零点，而 $0\in\operatorname{conv}(K\cup-K)$。该紧对称凸体生成 $V$，故确实定义范数。它的极体是 $[-u,u]_{C^*}$，因为在全部 $K$ 上满足 $-1\le g\le1$ 恰等于 $-u\le g\le u$。有限维支撑／双极性遂给

$$
\|z\|_C=\max_{-u\le g\le u}g(z),\qquad
\|p-r\|_C=2\max_{0\le f\le u}\bigl(f(p)-f(r)\bigr)\le2.
\tag{90.17}
$$

第二式用 $u(p-r)=0$ 和 $g=2f-u$；最大值由紧区间达到。它等于二，当且仅当某个 proper $f$ 的差值等于一，而零一界使这恰等于 $f(p)=1,f(r)=0$。没有预付球效应延拓。

若有 $p+t y=r+t x$、$0<t<1$，则 $p-r=t(x-y)$，由范数及 $\|x-y\|_C\le2$ 得 $\|p-r\|_C\le2t<2$。反之，若 $p\ne r$ 且 $d=\|p-r\|_C<2$，取达到最小值的 $p-r=a-b$。$u(p-r)=0$ 给 $u(a)=u(b)=d/2=:t\in(0,1)$。令 $x=a/t,y=b/t\in K$，即得所需捷径。若 $p=r$，任选 $x=y\in K$ 及 $t=1/2$ 也给捷径，且无效应能同时在该点取一和零。因此(90.16)包含这个退化分支。单点基中只有此分支；若 $K$ 本身是一条线段，其两个端点可由仿射坐标效应全域区分，范数距离二且无捷径。局部线段嵌在更大 $K$ 时则须用原范数，90.5正说明不能以局部端点距离代替它。证毕。

**推论 90.10（一般B+Z0仍需证明的接触）。** 在89.1及 $\mathrm B+\mathrm{Z0}$ 下，88.3给每个非空 $D_p$ 一张在整个原载体上取零集恰为 $D_p$ 的共同 proper 尺。对每个 $F\in\mathcal F_p$，

$$
D_p\cap F\subseteq\{r_{p,F}\},\qquad
D_p\cap F\ne\varnothing\quad\Longleftrightarrow\quad p\perp r_{p,F}.
\tag{90.18}
$$

要由此得到 $\mathrm H$／$S$，尚须证明这些交对所有 $p,F$ 均非空；等价地，须禁止全部局部对径的(90.16)捷径，或证明90.8的满射。90.6只在明示图族内完成这一步，不给一般证明或一般 $\mathrm B+\mathrm{Z0}$ 真反例。

证明。任一 $h\in F_p$ 在球 $F$ 上都满足(89.10)：$h(\chi^{-1}s)=1-\beta+\beta n\cdot s$，$0\le\beta\le1/2$。它在整个球有零点，恰须 $\beta=1/2$ 且 $s=-n$，所以得到(90.18)。若这些对径均在 $D_p$，88.3的共同尺就同时消灭全部对径并在 $p$ 取一，给 $\mathrm H$；反向由88.10得到这些排除。其余两种等价诊断分别是90.9、90.8。它们改写同一个缺口，不消除它。图族中若关系不传递，90.4直接违反 $\mathrm{Z0}$，并未保留此处全部前件；90.5也只给 $\mathrm B$ 不能代付 $\mathrm A$ 的控制。一般问题89.12仍保持未解。证毕。

### 90.6 完整候选的同数据回接与消费核算

**定义 90.11（已有图表示上的同一完整候选）。** 完整保留89.7的同一个原装饰元组 $\mathcal O$、共同 $\mathfrak S(\mathcal O)$ 及全部非几何条件。仅在每个原 $X=A,D,E$ 已有同载体保单位序同构

$$
\iota_X:V_X\longrightarrow V_{G_X},\qquad
\iota_X(C_X)=C_{G_X},\qquad
u_{G_X}\circ\iota_X=u_X
\tag{90.19}
$$

的范围内，将该原 $X$ 上的几何项 $\mathrm B+\mathrm{Boundary}$ 等价写成 $\mathrm{Z0}_{\rm pure}$，或 $\mathrm{Z0}$，或原图关系 $\sim_{G_X}$ 传递。图表示是明示模型前提；不是由一般 $\mathrm B+\mathrm{Z0}$ 推出的新接口，也不以限制到三个坐标的映射代替(90.19)的全域同构。所述三种写法是89.7在这个同一表示域内的等价候选，不另造一般更弱的包。

**定理 90.12（图族内的完整替换与消费者边界）。** 在定义90.11的共同表示域内，上述几何替换与原 $\mathsf R_{\rm polar}(\mathcal O)$ 等价，因而按89.8返回全部既有完整包。新增图条件只供应原几何；下表中每个消费者仍消费89章的原完整前件。

| 消费者 | 图定理供应及仍须保留的条件 |
| --- | --- |
| 完整 $S$ 与EJA | 在(90.19)及零拼合条件下，原锥是(90.13)的实PSD块直和，原全效应有(90.12)的least互反尺；89.4给原 $\mathrm B,\mathrm H,\mathrm{Boundary},\mathrm Q$。这已是实EJA模型，不是从裸关系构造一般矩阵表示。 |
| 概率、复型与Born | 实族的 $\operatorname{tr}(AX)$ 配对来自定义90.1已经付出的实矩阵与迹。复型选择及89.9的复Born结论仍须同一原精确两接口66.3和一般EJA忠实桥；实块不能仅改名称就成为复块。 |
| 指定二份／三份和读回 | 保留同一个原 $L$、同一个原 $p$ 两次、同一 $\omega$、两实张成、全实 $Z$、完整(83.8)（含秩一分支）、C2、整个 $G=1_E$，精确PRE后才用同一原资格态及整个输出的H13。89.9才给指定张量、偏迹和 $p_{13}$；其他括号或更高份数不由图闭合供应。 |
| CP、Kraus与实际仪器 | 指定事件和分支仍须89.9的原实线性、同事件HP提升、全实来源律、实际探针及其完整相容核，或已供应的充分递归参考与同事件全锥正性。取得CP后才有Kraus表示；实际全菜单、记录、顺序接线、旁观者、两预算、真粗粒化和总TP／分支TNI各守原合同。 |
| Lüders更新 | 保留同一CP分支的锐投影效应、全部确定接受态的逐点中性及原输出校准；效应和概率不决定后态。零质量分支保留，只有正质量才归一化。 |
| 物理时间 | 保留原物理时间上的连续、齐次、可逆 $*$ 自同构群、实际逆、钟、单位及动态来源，才复用有限块Hamiltonian结论；无限维域和收敛不由图定理支付。 |
| 实际来源 | 原准备、全部菜单、实际混合、参考、副本、相关联合、记录、质量、控制、ready／flags、失败／拒绝／停止／销毁／返回、全部合法未来和原source-adoption均由共同 $\mathfrak S$ 及89.7—89.10供应。数学凸组合、图证书和正效应不供应这些实际对象。 |

证明。(90.19)及其逆运输整个锥、紧基、全部纯点和最小面；对偶拉回运输整个 proper 区间、确认集与零排除关系，故也运输(90.2)和 $\mathrm{Z0}$。90.6遂在每个同一原 $X$ 上将这些图条件换成完整 $S$，89.4将其换回 $\mathrm B+\mathrm{Boundary}$，其余原数据逐项不动，直接应用89.8。这里没有复制旧分类、方向或尺度证明；不同接口若排除某个实图模型，该模型就不在完整包的共同范围内，不能以图定理补交不相容的前件。

表中各后续结论准确复用89.9，不以已有实迹配对冒称复型内生，不预付尚待认证HP提升的正性，也不把共同来源压成统计商。特别是两份、三份中的 $L,p,\omega$ 仍是原操作读回类型，不与(90.6)的纯点 $p$ 混用；$\mathrm Q$ 的标量商与三份尺度中的 $G$ 亦按原类型区分。

[Library二元寄存器路线][L]的 *An exhaustive binary comparison and a single coupling path* 直接按其既有范围复用：正互反比较及有限正对偶生成、一个穷尽纯对与凸原菜单给原单元球、全单元效应和least性；再有 $d\ge2$、闭连通且球面传递的局域 $H$、实际乘积准备／测试及忠实层析、各原寄存器的紧凸全张成基和闭实际群、同一连续路径中越出整个局域旋转群的非局域作用、该路径的真实三角形及每个有限寄存器连通图上的精确旁观者恒等放置，才取得 $d=3$、原复qubit张量锥及全酉控制的包含。其过程／仪器实现仍消费自己的参考、质量、辅助态、丢弃、读取与记录资源。它对相同二元单元的所有有限寄存器已有这些条件结论，不是任意类型／直和的通用分类，也不由本章再次取得；该处的操作放置图不是(90.1)的稀疏矩阵图，两种连通性不能互换。

[续卷VII][VII]24—28亦沿用89.10的准确入口：原复几何、全部原字与terminal futures、密度、统计 $\mathrm R_{10}$、full-future uniform ready-return及四前缀全未来行关系给Born，有限容量和完成PSD由此成为结论；完整联合菜单须在同一联合行上支付对应条件，不另付独立joint capacity。非恒定粗Born加同秩的VII22.3路线也保持其原结论，不能再列作普遍缺少独立容量的路线。这些既得完成几何可在它们自己的同一完成域上复用89.4；要认作本候选的原 $A,D,E$，仍须原source-adoption及全部来源合同。它们不免费提供(90.19)，本图结果也不解释其原复结构或记录后条件未来。证毕。

### 90.7 简化的准确范围、白话与归属

**命题 90.13（图族内的真实约束及一般边界）。** 在同一个图锥家族内，(90.2)这一仅以三个原纯点表达的零拼合条件，已经强迫图关系传递，并自动给全部原几何 $\mathrm B,\mathrm A,\mathrm H,S$；不必另给弦性、谱性或滤子。在固定图表示域内，$\mathrm B,\mathrm A,\mathrm H$ 因而不再作为独立前件，但所得模型类与要求完整 $S$ 者相同；这没有证明一般物理公理数净减少或最少。其模型前提仍是整个实稀疏PSD载体与迹，不能据此宣称从无结构推出矩阵、复数或任意一般载体，也不能把90.8—90.9的等价诊断计作删除 $\mathrm A$ 的新公理。完整量子起源目标仍保留89.12的一般逻辑缺口及89.7—89.10的实际来源与各消费者条件。

证明与白话。想象三个点排成一条缺了一条边的链：左点能接中点，中点能接右点，左右不能直接接。把灯 $p$ 放在左边那条边的等权方向；右边那条边上有两个只差一个正负号的纯方向 $q_+,q_-$。确认左边这盏灯时，确有一把原尺把 $q_+$ 读成零，另有一把原尺把 $q_-$ 读成零；每把尺连同自己的补都在整个原物体上非负。这两把尺不必相同，它们的存在并没有给一把同时对两点归零的尺。

把 $q_+,q_-$ 各取一半，正负交叉条目抵消，只剩中、右两点各一半的质量。这时任何确认 $p$ 的原尺都已被左边完整二阶PSD面约束：在中点单独的读数至少为一半；右点的读数不能负。所以混合后的读数至少为四分之一，而且投影尺恰好达到四分之一。原全效应已经用尽仍留这份残量，不能通过另选尺抹掉。三个坐标只是这个全域障碍的支撑，原 $V_G$ 不因此变成三维，其他纯点、全部混态和全部效应始终在场。

若要求这样的两个零总能拼成中点的零，这条缺边链就不允许存在。每条路径便必须把端点也连起来，最终每个连通分量都闭合成完全图，原矩阵锥也就恰为完整实PSD块的直和。在那些块里，确认一个纯方向会把对应效应的一个特征值钉为一，其他方向只可添非负部分；这正是全锥序least投影尺的来源，交换两纯方向又保持迹配对，得到互反。这里确实从图族中的零关系推出原先未要求的全部几何；实矩阵、PSD及迹却已经是模型定义，不是这个推导新生出来的结构。

一般载体还不能照搬最后一步。某个二态最小面即使整张是小球，它里面一把漂亮的零一刻度也仍须延拓到整个物体才算原效应。90.5甚至给出局部线段的两个对径端点，在整体上没有这样的尺；90.9把障碍准确写成原基范数距离不足二，等价于两端各添相同的较小质量后可以重合。$\mathrm{Z0}$ 将已有的排除拼成共同零面，并未在一般情形中证明这张面接触每个小球。图族消除了缺边链，因而补上该桥；不存在从一般 $\mathrm B+\mathrm{Z0}$ 到图表示的免费桥。

数学归属为 `repo-derived`：90.4的全效应精确零／四分之一控制、90.5的同族局部对径控制及90.6的任意有限图等价，是这里的纸面关系推导及其同数据应用。ROG极射线、弦图ROG判据及PSD最小面公式归 Hildebrand 所引成熟结果；90.3只将它们用于整个二态面。基范数／序单位极性及其分解式归90.9所引成熟文献，90.8—90.10是这些工具对原 $\mathrm A$ 缺口的准确诊断；旧Jordan／完整 $S$ 桥、89章全部完整包与消费者、Library二元寄存器及VII各入口均为既有结果复用。有限来源阅读不支持全球原创或历史优先权结论。以上为明确模型前提下的定义、条件定理与纸面证明；不声称Lean kernel核验、经验实现或整个母目标完成，也不以尚未推出宇宙本体作为否定该条件模型的理由。证毕。

## 追加锚（本行以下为增补区）

## 91. 实复团生成锥的整球性与全效应重叠障碍

### 91.1 团生成与稀疏截面是两个原锥

**定义 91.1（实复团生成载体）。** 取 $\mathbb F\in\{\mathbb R,\mathbb C\}$、顶点集为 $\{1,\ldots,n\}$ 的任意有限简单图 $G$，$n\ge1$。$\operatorname{Herm}_n(\mathbb F)$ 始终视为实向量空间，实域时即对称矩阵空间，$\dagger$ 表示相应伴随。定义

$$
\begin{gathered}
V_{G,\mathbb F}=\{X\in\operatorname{Herm}_n(\mathbb F):
X_{ij}=0\text{ 若 }i\ne j,\ \{i,j\}\notin E(G)\},\\
C^{\rm cl}_{G,\mathbb F}
=\operatorname{cone}\{vv^\dagger:v\in\mathbb F^n\setminus\{0\},\quad
\operatorname{supp}v\text{ 为 }G\text{ 的团}\},\qquad
u(X)=\operatorname{tr}X,\\
K^{\rm cl}_{G,\mathbb F}=C^{\rm cl}_{G,\mathbb F}\cap\{u=1\},\qquad
P^{\rm cl}_{G,\mathbb F}=\operatorname{ext}K^{\rm cl}_{G,\mathbb F},\\
C^{\cap}_{G,\mathbb F}
=V_{G,\mathbb F}\cap\operatorname{PSD}_n(\mathbb F),\qquad
C^{\rm cl}_{G,\mathbb F}\subseteq C^{\cap}_{G,\mathbb F}.
\end{gathered}
\tag{91.1}
$$

团包括单顶点，$\operatorname{cone}$ 只用有限非负组合。本章的原状态锥是 $C^{\rm cl}$；第90章的原锥是实域的 $C^\cap$。等价地，$C^{\rm cl}$ 是各团所支撑的完整PSD锥之和，因为每个团内PSD矩阵可在该团内谱分解。实域的两锥在弦图上相等，非弦图上不相等：稀疏秩一矩阵的向量支撑必为团，故两锥相等恰为90.3所引用的实ROG弦图判据。下述两域证明均直接使用 $C^{\rm cl}$，不在非弦图上用 $C^\cap$ 替代它，也不预设复域的截面分解。

所有 $F_p,T_p,D_p,\perp$、$\mathrm B,\mathrm A,S$ 均取这个同一原载体的整个基、全部纯点与整个 proper 区间；$\mathrm{Z0}$ 对全部原混态量化，$\mathrm{Z0}_{\rm pure}$ 准确取(90.2)的三个原纯点条件。图关系 $\sim_G$ 沿用(90.1)，含反身关系。

### 91.2 全称整球、精确四分之一与关系闭合

**定理 91.2（团重叠的全域判据）。** 定义91.1满足89.1的全部载体条件，且对每个图、两种域都自动满足 $\mathrm B$。准确的全部纯点和全部 proper 效应为

$$
\begin{gathered}
P^{\rm cl}_{G,\mathbb F}
=\{p_v=vv^\dagger:\|v\|=1,\ \operatorname{supp}v\text{ 为团}\},\\
[0,u]=\{f_E:X\mapsto\operatorname{tr}(EX):
E\in V_{G,\mathbb F},\quad
0\le E[Q]\le I_Q\text{ 对每个团 }Q\}.
\end{gathered}
\tag{91.2}
$$

其中 $E[Q]$ 为主子矩阵；不要求整个环境 $0\le E\le I_n$。对任意不同纯点 $p_v,p_w$，令 $T=\operatorname{span}_{\mathbb F}\{v,w\}$。其整个最小面准确为

$$
H(p_v,p_w)=
\begin{cases}
\{X\ge0:\operatorname{ran}X\subseteq T,\ \operatorname{tr}X=1\},
&\operatorname{supp}v\cup\operatorname{supp}w\text{ 为团},\\
[p_v,p_w],&\operatorname{supp}v\cup\operatorname{supp}w\text{ 不为团}.
\end{cases}
\tag{91.3}
$$

第一支在实域为 $B^2$、复域为 $B^3$，第二支为 $B^1$。在这一整个原载体上，

$$
\boxed{\mathrm{Z0}\ \Longleftrightarrow\ \mathrm{Z0}_{\rm pure}
\ \Longleftrightarrow\ \mathrm A
\ \Longleftrightarrow\ S
\ \Longleftrightarrow\ (\sim_G\text{ 传递})
\ \Longleftrightarrow\ (G\text{ 的每个连通分量完全}).}
\tag{91.4}
$$

若图有诱导链 $a-b-c$，则(90.6)中的实向量在两域均给原纯点；仍在本章整个原效应区间上有精确值

$$
T_p(q_+)=T_p(q_-)=0,\qquad
T_p((q_++q_-)/2)=\tfrac14.
\tag{91.5}
$$

同一诱导链的(90.10)还给 $H(p_0,r_0)=[p_0,r_0]$ 而 $p_0\not\perp r_0$。因此每个非完全连通分量都在本章自动成立的 $\mathrm B$ 下同时违反 $\mathrm A$ 与 $\mathrm{Z0}$。

证明。先核对整个原载体。全部单位团支撑向量的投影组成有限个紧集之并 $\mathcal P$；其凸包紧，每个锥生成元按迹归一后属于 $\mathcal P$，故 $K^{\rm cl}=\operatorname{conv}\mathcal P$。从迹一紧基的锥表示可知 $C^{\rm cl}$ 闭：若 $t_kx_k$ 收敛，$t_k=\operatorname{tr}(t_kx_k)$ 收敛，$x_k$ 可取收敛子列；$t_k\to0$ 时极限为零。它包含在PSD锥中，故尖，且迹在其非零元上严格正。

对角矩阵单位已在锥中；每条边上的 $e_i+e_j$ 投影和对角矩阵的实线性组合给该边实对称方向。在复域，$e_i+\mathrm i e_j$ 的投影再给该边虚Hermitian方向，故锥生成整个 $V_{G,\mathbb F}$，没有删除虚坐标。每个 $p_v\in\mathcal P$ 都在整个环境密度基中极端，故在本章基中也极端；反向，有限凸组合表示说明 $\operatorname{conv}\mathcal P$ 的任一极点必须属于 $\mathcal P$。这证明全部纯点公式。

实迹内积在 $V_{G,\mathbb F}$ 上非退化，故每个实线性效应有唯一 $E\in V_{G,\mathbb F}$ 表示。对每个团 $Q$ 的所有向量 $v$ 测试 $f_E(vv^\dagger)=v^\dagger E[Q]v$，正性等价于 $E[Q]\ge0$；补正性等价于 $I_Q-E[Q]\ge0$。反向由全部生成元即可检验锥正性。这证明(91.2)确为全区间，包括允许的复虚系数，而非环境效应的一个子菜单。

接着证明(91.3)是整个最小面。令 $\Pi_{T^\perp}$ 为环境正交投影。函数 $X\mapsto\operatorname{tr}(\Pi_{T^\perp}X)$ 在原锥上非负，其在原基上的零面 $F_T$ 恰由像空间包含在 $T$ 中的原归一PSD矩阵组成。若这样的 $X$ 分解为团支撑秩一正项，则每项向量 $z$ 必在 $T$ 中：非负数 $\|\Pi_{T^\perp}z\|^2$ 的和为零。不同 $p_v,p_w$ 使 $v,w$ 在相应域上线性独立。

若支撑并集为团，$T$ 中任一向量均有团支撑，所以该零面就是 $T$ 上完整PSD锥的迹一基，且 $(p_v+p_w)/2$ 在其相对内部。若并集不是团，可取不相邻的 $a,b$ 属于该并集；由于 $v,w$ 自身各有团支撑，交换名字后必有

$$
a\in\operatorname{supp}v\setminus\operatorname{supp}w,\qquad
b\in\operatorname{supp}w\setminus\operatorname{supp}v.
\tag{91.6}
$$

任一 $\alpha v+\beta w$ 若 $\alpha\beta\ne0$，其 $a,b$ 坐标分别为 $\alpha v_a,\beta w_b$，都不为零，故不可能有团支撑。该像空间零面中可用的秩一生成射线只有 $p_v,p_w$，所以整个零面恰为线段，而中点也在其相对内部。两支都因包含该中点为相对内点而是整个最小面，不只是一个包含二点的球形切片。在 $T$ 的正交归一基中，对完整二阶PSD基，实坐标 $(X_{11}-X_{22},2X_{12})$ 给 $B^2$；复坐标 $(X_{11}-X_{22},2\operatorname{Re}X_{12},2\operatorname{Im}X_{12})$ 给 $B^3$。这是标准二阶PSD球表示在整个原面的应用，证明了全称 $\mathrm B$。

现在把90.4的计算用于改变后的原锥，先核对其全效应类型。在整个 $V_{G,\mathbb F}$ 上取

$$
f_\pm(X)=\tfrac12(X_{aa}+X_{bb}+X_{cc})
+\operatorname{Re}X_{ab}\mp\operatorname{Re}X_{bc}.
\tag{91.7}
$$

由于 $X_{ac}=0$，(90.8)的两个二次型等式在复域将转置改为伴随后仍逐项成立。因此 $f_\pm$ 与 $u-f_\pm$ 对整个 $C^\cap_{G,\mathbb F}$ 非负，尤其对本章整个 $C^{\rm cl}_{G,\mathbb F}$ 非负。也可直接用(91.2)：一个团不能同时含 $a,c$，其 $E_\pm[Q]$ 只可能有 $ab$ 或 $bc$ 的二阶秩一投影块、剩余的 $1/2$ 对角元及零对角元，均为正收缩。两个前件于是由原 full proper 效应达到，且原团支撑保证 $p,q_\pm$ 都是本章纯点。

对于下界，任意本章 $f\in F_p$ 限制到完整 $ab$ 二阶PSD子锥，仍是 Hermitian 正收缩 $A$。确认使 $Av=v$，从而 $A\ge vv^\dagger$，故 $f(e_be_b^\dagger)\ge1/2$；另有 $f(e_ce_c^\dagger)\ge0$。因此所有原确认者在 $m=(q_++q_-)/2$ 的值至少为 $1/4$。环境投影的限制 $X\mapsto\operatorname{tr}(pX)$ 在本章全基上 proper，确认 $p$ 且在 $m$ 达到 $1/4$。这证明(91.5)的精确最小值，未以原来较小的效应区间代替本章全区间。

同样，(90.10)的 $p_0,r_0$ 支撑并集不是团，所以(91.3)给整个最小面为线段。若原 $f$ 确认 $p_0$ 并排除 $r_0$，它在 $ab$ 块上的正收缩必须使同一个 $f(e_be_b^\dagger)\ge3/4$，在 $bc$ 块上的正收缩必须使该值 $\le1/4$，矛盾。这正是90.5的共享对角量计算；对复Hermitian正收缩，确认向量的正交补仍是一维复空间，所得上下界相同。

由(91.5)，$\mathrm{Z0}_{\rm pure}$ 排除每条诱导 $P_3$；由上述对径控制，$\mathrm A$ 也排除每条诱导 $P_3$。最短路论证如90.6给没有诱导 $P_3$ 当且仅当每个连通分量完全，也等价于 $\sim_G$ 传递。$\mathrm{Z0}\Rightarrow\mathrm{Z0}_{\rm pure}$ 直接来自量词。

若分量 $I_j$ 都完全，原锥本身便为 $\bigoplus_j\operatorname{PSD}_{|I_j|}(\mathbb F)$，全 proper 区间为各块正收缩。对任一原纯 $p$，$e_p(X)=\operatorname{tr}(pX)$ 确认 $p$。任何确认者在其所在块固定 $p$ 的单位向量，故在该块支配 $p$，其余块非负；所以 $e_p$ 是整个锥序的 least 元。迹互反给完整 $S$，而且

$$
T_p(x)=\operatorname{tr}(px)\quad(\forall x\in K^{\rm cl}),\qquad
D_p=K^{\rm cl}\cap\ker e_p.
\tag{91.8}
$$

后一零面凸，给对全部纯态和混态的 $\mathrm{Z0}$。同块整二阶球的任意纯点与其球对径为正交秩一投影，异块线段的两端也被 $e_p$ 区分，故有完整 $\mathrm A$。任意原载体中的 $S\Rightarrow\mathrm{Z0}$ 已由90.6的 least 零集论证给出，因而闭合(91.4)。$n=1$ 时基为单点，$e_p=u$、$D_p=\varnothing$，所有球与对径条件空真；孤立顶点各为一维块，断开分量间保留整条 $B^1$。这些分支不需要额外连通假设。由自动成立的 $\mathrm B$ 及89.4，(91.4)还等价于原 $\mathrm H,\mathrm{Boundary},\mathrm Q$。证毕。

### 91.3 同一完整候选中的条件替换

**推论 91.3（团生成表示域内的完整同数据替换）。** 完整保留89.7的同一个 $\mathcal O$、共同 $\mathfrak S(\mathcal O)$ 与全部非几何条件。若每个原 $X=A,D,E$ 已有实线性双射

$$
\iota_X:V_X\longrightarrow V_{G_X,\mathbb F_X},\qquad
\iota_X(C_X)=C^{\rm cl}_{G_X,\mathbb F_X},\qquad
\operatorname{tr}\circ\iota_X=u_X,\qquad
\mathbb F_X\in\{\mathbb R,\mathbb C\},
\tag{91.9}
$$

则把该原 $X$ 上的 $\mathrm B+\mathrm{Boundary}$ 换为 $\mathrm{Z0}$、$\mathrm{Z0}_{\rm pure}$ 或 $\sim_{G_X}$ 传递，三种写法均与同一完整 $\mathsf R_{\rm polar}(\mathcal O)$ 等价。矩阵表示(91.9)是这个受控模型域的前件，不是由一般 $\mathrm B$ 或 $\mathrm{Z0}$ 推出的结论。

证明。双射及其逆运输整个基、全部极点、整个最小面；对偶拉回双射运输整个 proper 区间和所有确认／排除关系。因此91.2逐个原 $X$ 将三种条件换成同载体完整 $S$，89.4再将其换成 $\mathrm B+\mathrm{Boundary}$，89.8给原完整等价包。无需另造状态、补入效应或重复已有一般EJA分类。

逐消费者仍准确使用89.9及90.12的表：复型与Born保留一般EJA忠实桥及原精确两接口66.3；指定二份／三份保留同一原 $L,p,\omega$、同一 $p$ 两次、两实张成、全实 $Z$、含秩一分支的完整(83.8)、C2、整个 $G=1_E$，以及精确PRE后同一个原资格态的整个输出H13。即使某个原 $\mathbb F_X$ 已选为复数，也没有由单系统团关系给出这些指定张量或读回接口。CP、Kraus、仪器、两预算、Lüders与时间仍逐项使用89.9的同事件全实关系、实际探针或充分递归参考、原菜单／记录／粗粒化、中性校准和实际连续时间群；来源与全部合法未来继续使用89.7及89.10的共同原合同和 source-adoption。VII22、24—28及Library二元寄存器路线只在89.10、90.12所列原域内复用。

几何上，每个允许团是一块完整的实或复矩阵片；任意两盏纯灯所在的整最小面已是圆球或线段，所以局部圆度在这里没有缺口。真正的冲突是两片共用中间坐标，却缺少把首尾一起纳入的团：同一把全局尺在共享坐标上只能有一个高度。分别压暗两盏灯可以换尺，压暗它们的平均则至少留下四分之一；另一对局部线段端点甚至要求共享高度同时不小于四分之三且不大于四分之一。零拼合排除这种重叠，迫使每个连通部分闭合成完整矩阵块。这个结论只在已付出的整个团生成表示上成立，一般89.12仍缺少从任意整球载体到此种障碍的证明。证毕。

## 92. 单一加权准备关系的全载体零拼合障碍

### 92.1 全部纯点的关系空间与完整效应

**定义 92.1（有限纯点的关系零度）。** 在89.1的原载体上再设 $P$ 有限，定义满射

$$
\Phi:\mathbb R^P\longrightarrow V,\qquad
\Phi((c_z)_{z\in P})=\sum_{z\in P}c_zz,\qquad
\nu=\dim\ker\Phi=|P|-\dim V.
\tag{92.1}
$$

因为全部 $u(z)=1$，核中每个向量的系数和为零，故这是同一归一超平面中的仿射关系空间。$\nu=1$ 时将唯一非零关系归一为

$$
\sum_{i=1}^r\alpha_i a_i=\sum_{j=1}^s\beta_j b_j,\qquad
\alpha_i,\beta_j>0,\qquad
\sum_i\alpha_i=\sum_j\beta_j=1,
\tag{92.2}
$$

并写 $P=\{a_i\}_{i=1}^r\sqcup\{b_j\}_{j=1}^s\sqcup\{c_k\}_{k=1}^{\ell}$；$c_k$ 为关系系数为零的原顶点，$\ell$ 可为零。两侧各至少有两个顶点，否则一个原极点会成为其他点的凸组合。77.4及89.6的等权条带对应 $r=s=q$、$\alpha_i=\beta_j=1/q$、$\ell=0$，其原等权结果保持原范围。这是标准单维Gale／Radon关系的线性代数表示，参见 Á. G. Horváth、Z. Lángi，*Maximum volume polytopes inscribed in the unit sphere*，[arXiv:1402.6496v3 §3](https://arxiv.org/html/1402.6496v3#S3) 的核空间与Gale变换定义；下述论证不使用其最大体积、球面或非退化极值假设，也不要求 $\ell=0$。

### 92.2 任意正权下的可达混态缺口

**定理 92.2（全载体一关系定理）。** 在定义92.1上，若 $\nu\le1$，则

$$
\boxed{\mathrm{Z0}\quad\Longleftrightarrow\quad K\text{ 是单纯形}.}
\tag{92.3}
$$

不假定 $\mathrm B$ 或 $\mathrm A$。在 $\nu=1$ 的任意正权关系(92.2)中，交换两侧并重编号，可使

$$
t=\alpha_1=\min\{\alpha_1,\ldots,\alpha_r,\beta_1,\ldots,\beta_s\}>0,
\qquad p=a_1.
\tag{92.4}
$$

对任意非空真子集 $J\subset\{1,\ldots,s\}$，令

$$
b=\sum_{j\in J}\beta_j,\qquad
x=\frac1b\sum_{j\in J}\beta_jb_j,\qquad
y=\frac1{1-b}\sum_{j\notin J}\beta_jb_j.
\tag{92.5}
$$

则 $x,y$ 是整个原基中的态，且全原效应给出达到的精确值

$$
T_p(x)=T_p(y)=0,\qquad
T_p\bigl((x+y)/2\bigr)=\frac{t}{2\max\{b,1-b\}}>0.
\tag{92.6}
$$

允许其中一个态纯、另一个混；当某组含多个顶点时，不把它换成纯态量词。任意零系数顶点 $c_k$ 不改变这些结论。特别地，若有限纯点载体满足 $\mathrm B+\mathrm{Z0}$ 而违反 $\mathrm A$，则必要有

$$
|P|-\dim V\ge2.
\tag{92.7}
$$

证明。$\nu=0$ 时，全部纯点是 $V$ 的一组线性基，因而归一基 $K=\operatorname{conv}P$ 为单纯形。其每个纯 $p$ 的重心坐标效应 $e_p$ 属于全 proper 区间，任何确认者在所有其他顶点上非负，故全锥序支配 $e_p$。因此 $D_p$ 正是对面单纯形，给 $\mathrm{Z0}$；单点时 $D_p=\varnothing$。反向任一单纯形的顶点在这个归一嵌入中线性独立，亦有 $\nu=0$。

设 $\nu=1$。先把整个原效应区间写全。任意顶点赋值 $A_i,B_j,Z_k$ 下降为 $V$ 上实线性泛函的充要条件是它消灭整个 $\ker\Phi$，故全 proper 赋值恰为

$$
0\le A_i,B_j,Z_k\le1,\qquad
\sum_i\alpha_iA_i=\sum_j\beta_jB_j.
\tag{92.8}
$$

充分性还使用 $C=\operatorname{cone}P$：所有顶点值与补值非负就保证在整个原锥上非负。这里列的是全部 $P$ 及其全部关系，故无额外延拓问题；零系数顶点的 $Z_k$ 可独立取遍 $[0,1]$。

按(92.4)选择 $p$。两组均非空且每个 $\beta_j\ge t$，所以 $b,1-b\ge t$。令两张效应都取 $A_1=1$、其余 $A_i=0$、全部 $Z_k=0$，列值分别取

$$
\begin{array}{c|cc}
&j\in J&j\notin J\\ \hline
f_x(b_j)&0&t/(1-b)\\
f_y(b_j)&t/b&0
\end{array}
\tag{92.9}
$$

所有值都在 $[0,1]$，两张表的列侧加权和均为 $t$，与行侧相同。由(92.8)，这是在全部原顶点及整个原锥上定义的两张 proper 效应，确认 $p$，分别排除 $x,y$，故两个零最小值达到。

任取原 $f\in F_p$，记

$$
s_J=\sum_{j\in J}\beta_j f(b_j),\qquad
s_{J^c}=\sum_{j\notin J}\beta_j f(b_j).
\tag{92.10}
$$

两数非负，关系与确认给 $s_J+s_{J^c}=\sum_i\alpha_i f(a_i)\ge t$。于是

$$
f\bigl((x+y)/2\bigr)
=\frac{s_J}{2b}+\frac{s_{J^c}}{2(1-b)}
\ge\frac{s_J+s_{J^c}}{2\max\{b,1-b\}}
\ge\frac{t}{2\max\{b,1-b\}}.
\tag{92.11}
$$

若 $b\ge1-b$，(92.9)的 $f_y$ 把全部列质量 $t$ 放在 $J$，达到下界；若 $b\le1-b$，$f_x$ 达到下界，相等分支两者均达到。这证明(92.6)并直接违反原混态 $\mathrm{Z0}$，不依赖球性、纯比较互反或共同零面引理。$c_k$ 的取值既不进入关系也不进入目标态，因而可自由选择；上面取零给出完整可行见证，没有将这些顶点从原基中删除。

最后，若 $\nu\le1$ 而有 $\mathrm{Z0}$，刚证结论使原 $K$ 是单纯形。单纯形任意不同纯对的整个最小面为端点线段，两个端点由重心坐标效应全域区分，所以 $\mathrm A$ 成立；这推出(92.7)。该必要界只涉及纯点有限的整个原载体，不用于无限纯点集。证毕。

### 92.3 同时失去对径区分与零拼合的六点控制

**命题 92.3（实五维中的加权六点控制）。** 令

$$
\begin{gathered}
V=\mathbb R^6/\mathbb R(8,1,1,-8,-1,-1),\qquad
a_i=[e_i],\quad b_j=[e_{3+j}]\quad(1\le i,j\le3),\\
C=\operatorname{cone}\{a_1,a_2,a_3,b_1,b_2,b_3\},\qquad
u([z])=\sum_{k=1}^6z_k,\qquad K=C\cap\{u=1\}.
\end{gathered}
\tag{92.12}
$$

使用整个原 $K$、全部纯点与全 proper 区间。它满足89.1，$\dim V=5$，全部纯点恰为这六点，唯一归一关系为

$$
\tfrac45a_1+\tfrac1{10}a_2+\tfrac1{10}a_3
=\tfrac45b_1+\tfrac1{10}b_2+\tfrac1{10}b_3.
\tag{92.13}
$$

每个不同纯对的整个最小面都是端点线段，因此全称 $\mathrm B$ 成立；但 $\mathrm A$ 与 $\mathrm{Z0}$ 都失败，准确有

$$
\begin{gathered}
H(a_1,b_1)=[a_1,b_1],\qquad T_{a_1}(b_1)=\tfrac34>0,\\
p=a_2,\quad x=b_1,\quad y=(b_2+b_3)/2:\qquad
T_p(x)=T_p(y)=0,\qquad T_p((x+y)/2)=\tfrac1{16}.
\end{gathered}
\tag{92.14}
$$

证明。关系向量的坐标和为零，所以 $u$ 良定义。商中六点张成 $V$；有限生成锥闭。非零非负组合有严格正总系数，其 $u$ 值正，且不可能是带正负号的关系向量，故 $u$ 严格正；这也使锥尖。单位值为一的原基恰为六点凸包，紧且非空。唯一关系有三个正系数及三个负系数。若某个所列点是其余点的凸组合，将产生一个只有一个正坐标的非零核向量；该核的任一非零元在每个符号侧都有三个非零坐标，矛盾。所列点因此全是不同极点，有限凸包再无其他极点。

为同时核对所有整个二点面，证明(92.2)中 $r,s\ge3$ 时的一般面证书，并允许任意 $c_k$。任选两个不同原顶点，将它们的效应值设为零；未选中的 $a_i$ 的总关系权记为 $A_0$，未选中的 $b_j$ 的总关系权记为 $B_0$。因为每侧至少三个点且只选两个，$A_0,B_0>0$。在未选 $a_i$ 上统一取值 $B_0/(A_0+B_0)$，在未选 $b_j$ 上统一取值 $A_0/(A_0+B_0)$，未选 $c_k$ 取一。两侧加权和均为 $A_0B_0/(A_0+B_0)$，所以(92.8)给全域 proper 效应；它恰在所选两个顶点取零，其他顶点严格正。其零面恰为所选端点线段，故该线段就是整个最小面。这个标准Gale面证书在此仅用于核对全称 $\mathrm B$，不作为新的多面体分类；它尤其适用于(92.13)。

任一确认 $a_1$ 的原效应由关系满足

$$
\tfrac45\le\sum_i\alpha_i f(a_i)
=\tfrac45 f(b_1)+\tfrac1{10}f(b_2)+\tfrac1{10}f(b_3)
\le\tfrac45f(b_1)+\tfrac15.
\tag{92.15}
$$

所以 $f(b_1)\ge3/4$。赋值 $(f(a_1),f(a_2),f(a_3))=(1,0,0)$、$(f(b_1),f(b_2),f(b_3))=(3/4,1,1)$ 满足完整(92.8)，达到此界。这证明 $a_1$ 与 $b_1$ 虽是其整个最小线段的对径，仍不可全域区分。

对于第二行，取 $t=1/10$、$J=\{1\}$、$b=4/5$，92.2给精确中点值 $(1/10)/(2\cdot4/5)=1/16$。两张排除效应的行值均为 $(0,1,0)$，列值分别为 $(0,1/2,1/2)$、$(1/8,0,0)$，直接满足(92.13)并分别排除 $x,y$；后一张达到中点 $1/16$。这在同一个实五维原载体上同时核对了 $\mathrm B$、$\neg\mathrm A$ 及 $\neg\mathrm{Z0}$，所以不是 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$ 的反模型。证毕。

### 92.4 单关系排除的几何意义及完整候选边界

**推论 92.4（有限单关系表示域内的同数据结算）。** 完整保留89.7的原 $\mathcal O$ 和全部非几何条件。若每个原 $X=A,D,E$ 都有有限纯点集且关系零度 $\nu_X\le1$，则将其 $\mathrm B+\mathrm{Boundary}$ 换为同一原载体的 $\mathrm{Z0}$ 仍是完整同数据等价；但此表示域中每个满足候选的单系统必为单纯形。一般89.12仍未解决，特别是有限纯点且 $\nu\ge2$、或纯点无限的原载体。

证明。若有原 $\mathrm{Z0}$，92.2给同一基为单纯形，其重心坐标效应给完整 $S$，89.4给 $\mathrm B+\mathrm{Boundary}$。反向由89.4取得 $S$，再用90.6的 least 零面论证得到 $\mathrm{Z0}$。于是89.8和89.9仍在全部原前件下应用；实际来源与终端路线保持89.7及89.10的原域。这一限制域只得到经典单纯形几何；不由此构造非经典复块、指定复合、CP、仪器或时间，也不解除91.3列明的任何原消费者条件。

几何上，把所有纯点看成支点，proper 效应是给每个支点赋零到一的高度。一条准备关系要求左右两边的加权平均高度完全相同。选权重最小的左支点必须点亮，可以分别把右边一组的混态、其余一组的混态压成零，因为两次允许换尺；但两组混态的中点给右边每个支点都分配正质量，若它仍为零，就会通过同一关系逼已点亮的左支点也变零。(92.11)把这个矛盾量化成精确且达到的正高度；不等权和不参加关系的自由顶点都未破坏它。六点例中每一对支点之间又确实是一整条最小线段，说明这种全局高度冲突能与全部局部球性共存。

关系表示、PSD像空间面与二阶球表示均是成熟中间工具；91.2的全效应团重叠推导、92.2的加权混态最小值及它们的同数据应用只使用相应条目明列的前件。尤其(92.8)之所以充分，是因为关系取自整个 $P$；若只在更大载体中抽出一个单关系子配置，其他原纯点和其他关系可能禁止这些效应赋值，没有获得全域延拓之前不能应用92.2。两条受控路线都未证明一般 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$：前者已付团生成表示，后者已付全载体有限关系零度界。原 $\mathrm B+\mathrm{Boundary}$ 候选及89.7—89.10的全部完整前件保持原范围。证毕。

## 追加锚（本行以下为增补区）

## 93. 完整零拼合的实ROG分类与失败对径的三态提升

### 93.1 全部原数据上的实秩一生成前件

**定义 93.1（实ROG表示域）。** 保留89.1的整个非零有限维 $(V,C,u)$、紧基 $K$、全部纯点 $P$ 和整个 $[0,u]_{C^*}$。另要求有实线性同构

$$
\iota:V\longrightarrow L_0\subseteq\operatorname{Sym}_m(\mathbb R),\qquad
\iota(C)=L_0\cap\operatorname{PSD}_m(\mathbb R),\qquad
L_0=\operatorname{span}\iota(C),
\tag{93.1}
$$

且每个 $X\in\iota(C)$ 都是有限个属于这个同一锥的秩一PSD矩阵之和。此即 Hildebrand，*Spectrahedral cones generated by rank 1 matrices*，[arXiv:1409.4781v2 Property 1.1](https://arxiv.org/html/1409.4781v2#S1) 的实ROG条件；其 Lemma 3.9 给全部极射线恰为锥内秩一射线。原 $u$ 只要求严格正，不预设迹、自对偶、单位矩阵、Jordan乘法、谱性或滤子。这里要求的是整个原锥的表示，不是抽取的子锥或一般谱截面的假设。

对 $p\in P$、$x\in K$，沿用原确认集 $F_p$、最小值 $T_p(x)$，并明记

$$
p\perp x\ \Longleftrightarrow\ T_p(x)=0
\ \Longleftrightarrow\ \exists f\in F_p:\ f(x)=0,\qquad
D_p=\{x\in K:p\perp x\}.
\tag{93.2}
$$

最后一个存在量词由全效应区间的紧性保证。完整零拼合始终指

$$
\mathrm{Z0}:\quad
\forall p\in P\ \forall x,y\in K,\qquad
[p\perp x\ \land\ p\perp y]\ \Longrightarrow\ p\perp(x+y)/2.
\tag{93.3}
$$

两个零前件允许不同原效应，$x,y$ 允许混态；不将(93.3)替换成 $\mathrm{Z0}_{\rm pure}$。完整 $S$、$\mathrm B,\mathrm A,\mathrm H,\mathrm{Boundary},\mathrm Q$ 均取88—90章的原义，特别是 $S$ 要求全锥序least确认及全部纯点间的数值互反。

### 93.2 任意归一化下的完整实块分类

**定理 93.2（同归一化的零拼合分类）。** 在定义93.1的实ROG表示域内，$\mathrm B$ 自动成立，且以下三项等价：完整 $\mathrm{Z0}$；完整 $S$；存在正整数 $n_1,\ldots,n_k$ 及实线性同构

$$
\begin{gathered}
\Theta:V\longrightarrow\bigoplus_{\alpha=1}^k\operatorname{Sym}_{n_\alpha}(\mathbb R),\qquad
\Theta(C)=\bigoplus_{\alpha=1}^k\operatorname{PSD}_{n_\alpha}(\mathbb R),\\
u(X)=\sum_{\alpha=1}^k\operatorname{tr}(\Theta X)_\alpha
\qquad(X\in V).
\end{gathered}
\tag{93.4}
$$

不论这些等价条件是否成立，都可以先用明示的同载体变换将原表示化为

$$
C'=L\cap\operatorname{PSD}_n(\mathbb R),\qquad
I_n\in L,\qquad u'=\operatorname{tr},\qquad
P'=\{vv^{\mathsf T}\in L:\|v\|=1\},
\tag{93.5}
$$

其中 $n$ 是整个锥的共同支撑维数。等价条件成立时，(93.4)可在(93.5)后仅用正交换基取得，且 $\sum_\alpha n_\alpha=n$。全部原效应与最小值准确为

$$
\begin{gathered}
f_E(X)=\sum_\alpha\operatorname{tr}\bigl(E_\alpha(\Theta X)_\alpha\bigr),\qquad
f_E\in[0,u]\ \Longleftrightarrow\ 0\preceq E_\alpha\preceq I_{n_\alpha}\ \ (\forall\alpha),\\
e_p(X)=\sum_\alpha\operatorname{tr}\bigl((\Theta p)_\alpha(\Theta X)_\alpha\bigr),\qquad
T_p(x)=e_p(x)\quad(p\in P,\ x\in K).
\end{gathered}
\tag{93.6}
$$

这些条件还给同一原载体的 $\mathrm A,\mathrm H,\mathrm{Boundary},\mathrm Q$；89.4的标量商返回的正是(93.6)的唯一least确认。单点基包含在结论中。

证明。先核对任意 $u$ 的同时归一化。令

$$
W=\sum_{X\in\iota(C)}\operatorname{ran}X,\qquad n=\dim W\ge1.
\tag{93.7}
$$

所有锥元均在 $W^\perp$ 上为零，$L_0=\operatorname{span}\iota(C)$ 使全部 $L_0$ 亦如此。将 $W$ 用任一正交基识别为 $\mathbb R^n$，限制到 $W$ 的映射 $R$ 在 $L_0$ 上是线性同构，其像 $L_W$ 的PSD截面恰为 $R\iota(C)$；没有丢失原态或效应。有限个锥元的像空间已张成 $W$，它们之和在 $W$ 上正定。把原 $u$ 运输为 $u_W$，在紧集

$$
\{X\in R\iota(C):u_W(X)=n\}
\tag{93.8}
$$

上取行列式最大点 $M$。正定可行点使最大值严格正，故 $M\succ0$。对任意 $Y\in L_W\cap\ker u_W$，充分小的正负 $t$ 均使 $M+tY$ 留在(93.8)，行列式的一阶驻点条件给 $\operatorname{tr}(M^{-1}Y)=0$。这两个线性泛函因而成比例；代入 $M$，由 $u_W(M)=n=\operatorname{tr}(M^{-1}M)$ 得比例为一。因此

$$
\Psi(X)=M^{-1/2}(R\iota X)M^{-1/2},\qquad
\operatorname{tr}\Psi(X)=u(X),\qquad \Psi(M_V)=I_n,
\tag{93.9}
$$

其中 $M_V=(R\iota)^{-1}M$。取 $L=\Psi(V)$，即得(93.5)的前三项；合同保持秩一及ROG，Lemma 3.9给最后一项。对偶运输 $f\mapsto f\circ\Psi^{-1}$ 双射整个 proper 区间、确认集和零关系，双射 $K,P$ 及整个最小面，故保持 $\mathrm{Z0}$ 和 $S$。这项行列式驻点计算只是同载体归一化的矩阵工具，不是额外几何公理。由90.3直接得全部二纯点整最小面为 $B^1$ 或 $B^2$，所以原 $\mathrm B$ 自动成立。下文在(93.5)坐标内将 $C',u',P'$ 简记为 $C,u,P$。

若 $n=1$，则 $L=\mathbb R$、$C=\mathbb R_+$、$K=P=\{p\}$，$F_p=\{u\}$、$e_p=u$、$D_p=\varnothing$；取一个大小为一的块即得全部结论。反之，ROG的单射线必为秩一射线，所以单点基经共同支撑限制也恰落入此分支。以下设 $n\ge2$。

现设完整 $\mathrm{Z0}$。固定 $p=vv^{\mathsf T}\in P$，定义原混态及一个原效应

$$
a_p=\frac{I_n-p}{n-1}\in K,\qquad
h_p(X)=\operatorname{tr}(pX),\qquad 0\le h_p\le u.
\tag{93.10}
$$

后两个序界来自环境PSD正性，故在整个原锥上成立；$h_p(p)=1$、$h_p(a_p)=0$，于是 $p\perp a_p$。若 $x\in D_p$ 却有 $\operatorname{tr}(px)>0$，则 $\ker a_p=\mathbb Rv$、$v\notin\ker x$。PSD矩阵的核交性质给 $a_p+x\succ0$，所以 $m=(a_p+x)/2$ 是原 $K$ 的相对内点。$\mathrm{Z0}$ 却要求某个原 $f\in F_p$ 在 $m$ 取零。对任意 $Y\in L$，充分小的双向微扰 $m\pm\varepsilon Y\in C$ 及 $f\ge0$ 迫使 $f(Y)=0$，与 $f(p)=1$ 矛盾。反向包含由 $h_p$ 自身见证，故

$$
D_p=\{x\in K:\operatorname{tr}(px)=0\}
\qquad(p\in P).
\tag{93.11}
$$

这里只把确实存在的投影限制效应用作见证，尚未假定每个原效应都有环境正收缩代表。

任取 $Z\in L$。复用90.9所证明的原基范数极性及极值达到性，取最优分解和对偶极大点

$$
\begin{gathered}
Z=X-Y,\qquad X,Y\in C,\qquad -u\le b\le u,\\
b(Z)=\|Z\|_C=\operatorname{tr}X+\operatorname{tr}Y.
\end{gathered}
\tag{93.12}
$$

两项上界 $b(X)\le\operatorname{tr}X$、$-b(Y)\le\operatorname{tr}Y$ 的和已取等，故逐项取等。原 proper 效应 $f=(u+b)/2$ 遂满足 $f(X)=\operatorname{tr}X$、$f(Y)=0$。用ROG写有限纯分解

$$
X=\sum_i\alpha_i p_i,\qquad Y=\sum_j\beta_jq_j,
\qquad \alpha_i,\beta_j>0,\quad p_i,q_j\in P,
\tag{93.13}
$$

省去零项。$f$ 及其补在整个原锥非负，故 $f(p_i)=1$、$f(q_j)=0$。由(93.11)，全部交叉迹积为零；秩一投影的迹积是向量内积平方，因此两侧的全部支撑正交，$XY=0$。普通实对称谱理论给 $X=Z_+$、$Y=Z_-$。若某侧为零，$Z$ 已半正或半负，同一结论直接成立。于是

$$
Z_+,Z_-\in C\subseteq L\qquad(\forall Z\in L).
\tag{93.14}
$$

这一步使用的是同一个最优分解、同一个对偶效应及其所有纯分解项，不将分别可达的分解拼成共同实现。基范数与序单位极性归90.9引用的 Lami–Palazuelos–Winter，*Ultimate data hiding in quantum mechanics and beyond*，arXiv:1703.03392v2 §II.1 Definition 2、Lemma 3；(93.11)—(93.14)是这里在原ROG锥上的组合。

先由(93.14)核对全部效应和least性。在 $L$ 上以迹内积识别对偶，记 $C^\vee=\{A\in L:\operatorname{tr}(AX)\ge0\ (\forall X\in C)\}$。显然 $C\subseteq C^\vee$；若 $A\in C^\vee$，则 $A_-\in C$，故

$$
0\le\operatorname{tr}(AA_-)=-\operatorname{tr}(A_-^2),
\qquad A_-=0,
\qquad C^\vee=C.
\tag{93.15}
$$

因此这时才可将整个原 proper 区间准确写成 $f_E(X)=\operatorname{tr}(EX)$、$E\in L$、$0\preceq E\preceq I_n$。若 $f_E\in F_p$，$p=vv^{\mathsf T}$，则 $v^{\mathsf T}Ev=1$ 和 $I_n-E\succeq0$ 给 $Ev=v$。在 $\mathbb Rv\oplus v^\perp$ 上，$E=p\oplus E_\perp$、$E_\perp\succeq0$，故 $E-p\succeq0$ 且属于 $L$，于是 $E-p\in C$。这证明 $h_p$ 是 $F_p$ 的全锥序least元；迹配对给 $h_p(q)=h_q(p)$，从而已得完整 $S$。

再证明(93.14)补齐的是完整实矩阵块。由 $I_n\in L$，对每个 $A\in L$ 和实 $t$ 都有 $(A-tI_n)_+\in L$。设 $A$ 的不同特征值为 $\lambda_1<\cdots<\lambda_\ell$、谱投影为 $P_1,\ldots,P_\ell$。当 $\ell\ge2$ 时，

$$
(A-\lambda_iI_n)_+
=\sum_{j>i}(\lambda_j-\lambda_i)P_j
\qquad(1\le i<\ell)
\tag{93.16}
$$

从 $i=\ell-1$ 向下逐个解出 $P_\ell,\ldots,P_2\in L$，再由 $P_1=I_n-\sum_{j>1}P_j$ 得 $P_1\in L$。$\ell=1$ 时 $P_1=I_n$。因此 $A^2=\sum_j\lambda_j^2P_j\in L$，极化给

$$
A\circ B=\frac{AB+BA}{2}
=\frac{(A+B)^2-A^2-B^2}{2}\in L.
\tag{93.17}
$$

从 $I_n$ 的ROG分解选一个单位秩一投影 $p_1\in L$。$I_n-p_1$ 仍是 $L$ 中的PSD正交投影；其ROG分解的每个向量都在它的像空间中。选出并归一化一个非零项为 $p_2$，则 $p_1p_2=0$，且 $I_n-p_1-p_2$ 仍是 $L$ 中的PSD正交投影。重复至剩余投影为零，得到 $n$ 个两两正交的秩一投影，和为 $I_n$。正交换基后，可设所有 $E_{ii}\in L$。

记 $S_{ij}=E_{ij}+E_{ji}$（$i\ne j$）。对任意 $A\in L$，(93.17)给

$$
E_{jj}\circ(E_{ii}\circ A)=\frac{A_{ij}}4S_{ij}.
\tag{93.18}
$$

所以某个位置能在 $L$ 的矩阵中非零，就有整个 $S_{ij}\in L$。再对不同 $i,j,k$ 使用

$$
S_{ij}\circ S_{jk}=\tfrac12S_{ik}.
\tag{93.19}
$$

关系 $i\sim j$ 定义为 $i=j$ 或 $S_{ij}\in L$，由此反身、对称且传递。其等价类内全部对称矩阵单位均在 $L$；不同等价类间任一条目非零又会由(93.18)将两类合并，故不可能。因此 $L$ 恰是这些类上的完整实对称块直和，$C=L\cap\operatorname{PSD}_n$ 恰是相应完整实PSD块直和。此处的分块关系由谱部分封闭推出，并非(93.1)的额外前件。将此正交换基与 $\Psi$ 合成，得保持原 $u$ 的(93.4)。

反向，(93.4)中各完整实PSD块在迹配对下自对偶；测试每块的全部秩一投影即可得到(93.6)的整个效应区间。全部纯点恰为某一块的迹一秩一投影，确认它的正收缩在该方向固定为一、在正交补只添PSD部分。上面的least论证因而直接给(93.6)及互反，得到 $S$。在任意原载体上，$S$ 的least性都给

$$
D_p=K\cap\ker e_p:
\quad f\in F_p,\ f(x)=0\ \Longrightarrow\ 0\le e_p(x)\le f(x)=0,
\tag{93.20}
$$

反向由 $e_p$ 自身见证。这个零面凸，故 $S\Rightarrow\mathrm{Z0}$。三项等价至此闭合。

在所得块中，同块二纯点的整个最小面是完整实二阶PSD基，其对径为支撑二维空间内正交的秩一投影；异块二纯点的整个面是线段，两端亦矩阵正交。于是(93.6)同时给每个局部对径的原全域排除，即 $\mathrm A$，并给固定 $p$ 消灭全部对径的同一个正尺，即 $\mathrm H$。89.4给原 $\mathrm{Boundary},\mathrm Q$ 及规范商；商尺与(93.6)同为同一 $F_p$ 的least元，故相等。以上随同构运输全部原纯点、混态和效应，单点按空对径族约定。证毕。

### 93.3 从不可全域区分的局部对径到定量三态障碍

**命题 93.3（原锥中的失败提升）。** 在定义93.1的整个实ROG载体上，不假设 $\mathrm{Z0}$。若某个整个二态球内的一对局部对径 $p_0,r_0$ 不能由原全局 proper 效应完美区分，则存在原纯点 $s,x\in P$ 及原态 $y\in K$，使

$$
s\perp x,\qquad s\perp y,\qquad
T_s\bigl((x+y)/2\bigr)>0.
\tag{93.21}
$$

更精确地，先用(93.9)的同归一化坐标，以下的 $C,L$ 指该坐标中的整个原锥与原空间。此时 $n\ge2$，可取

$$
\begin{gathered}
s=vv^{\mathsf T},\quad x=ww^{\mathsf T},\quad
\|v\|=\|w\|=1,\quad c=\operatorname{tr}(sx)=|v^{\mathsf T}w|^2\in(0,1),\\
y=\frac{I_n-s}{n-1},\qquad m=\frac{x+y}{2}\succ0,\qquad
m-\frac{c}{2n}s\in C,\qquad T_s(m)\ge\frac{c}{2n}>0.
\end{gathered}
\tag{93.22}
$$

这里 $y$ 的秩为 $n-1$，在 $n>2$ 时为混态；正性、两个零见证和下界均在整个原锥与全效应区间中成立。运输回 $V$ 后，$s,x,y$ 的实线性张成至多三维，这只是三向量的有限提升，不限制原空间、环境支撑或全部混态的维数。

证明。归一化不改变全域区分与球对径。由90.9，原基范数满足 $0<\|p_0-r_0\|_C<2$。取原最优分解及同一个对偶饱和效应，如(93.12)的成熟极性计算，得到

$$
p_0-r_0=X-Y,\quad X,Y\in C,\quad
\operatorname{tr}X=\operatorname{tr}Y=t\in(0,1),\quad
f\in[0,u],\quad f(X)=t,\ f(Y)=0.
\tag{93.23}
$$

分别作有限ROG纯分解 $X=\sum_i\alpha_i s_i$、$Y=\sum_j\beta_jq_j$，全部非零系数为正，则 $f(s_i)=1$、$f(q_j)=0$。

若所有交叉迹积 $\operatorname{tr}(s_iq_j)$ 都为零，则 $XY=0$，所以 $X=(p_0-r_0)_+$、$Y=(p_0-r_0)_-$。令 $W_0$ 为 $p_0,r_0$ 的两个支撑向量之张成。差 $p_0-r_0$ 在 $W_0$ 上为非零迹零二阶矩阵，故 $X,Y$ 均为支撑于 $W_0$ 的非零秩一矩阵。90.3的整个最小面公式使 $X/t,Y/t$ 都属于 $H(p_0,r_0)$。局部对径的中点在原球的相对内部，故此面也就是起始的整个球。

若该面是圆盘，局部对径在其完整实二阶PSD迹一坐标内正交，遂 $p_0r_0=0$、$X=p_0,Y=r_0$，与 $t<1$ 矛盾。若该面是线段，则 $X/t,Y/t$ 是其秩一纯端点，只能分别为 $p_0,r_0$ 或反序。代入 $p_0-r_0=t(X/t-Y/t)$，正序给 $t=1$，反序给 $t=-1$，均矛盾。这两支耗尽90.3的全最小面，故必有一对交叉迹积严格正。

取这一对为 $s=vv^{\mathsf T},x=ww^{\mathsf T}$，则 $f(s)=1,f(x)=0$、$c=\operatorname{tr}(sx)>0$。二者不同，故 $c<1$。这给 $s\perp x$。由 $I_n-s\in L\cap\operatorname{PSD}_n$，(93.22)的 $y$ 是原态，投影限制效应 $h_s(Z)=\operatorname{tr}(sZ)$ 在整个原锥上 proper、确认 $s$ 并排除 $y$，故 $s\perp y$；未要求 $f=h_s$。

为约束全部原确认者，写 $w=av+b$、$b\perp v$、$a^2=c$，任意实向量写作 $\xi=\alpha v+h$、$h\perp v$。加权Cauchy–Schwarz给

$$
\begin{aligned}
c\alpha^2
&=\bigl(w^{\mathsf T}\xi-b^{\mathsf T}h\bigr)^2\\
&\le\bigl(1+(n-1)\|b\|^2\bigr)
\left((w^{\mathsf T}\xi)^2+\frac{\|h\|^2}{n-1}\right)\\
&\le n\,\xi^{\mathsf T}(x+y)\xi.
\end{aligned}
\tag{93.24}
$$

因此 $m-cs/(2n)\succeq0$；这个差还属于原 $L$，所以确在原 $C=L\cap\operatorname{PSD}_n$ 中。对每一个原 $g\in F_s$，全锥正性给 $g(m)\ge c\,g(s)/(2n)=c/(2n)$，取最小值即得(93.22)。此外 $\ker y=\mathbb Rv$ 而 $v\notin\ker x$，故 $m\succ0$。这同时给内部态和定量严格正的最小读数，不只排除某一把选定效应。最后以 $\Psi^{-1}$ 运输所有向量及效应，保留原归一化、中点与锥差，便得原载体的(93.21)。证毕。

### 93.4 同数据替换、消费者条件与数学范围

**推论 93.4（实ROG域内的完整候选）。** 完整保留89.7的同一个原装饰元组 $\mathcal O$、共同 $\mathfrak S(\mathcal O)$ 及全部非几何条件。若每个原 $X=A,D,E$ 已有定义93.1的实ROG表示，原 $u_X$ 允许任意严格正，则将这些原载体上的 $\mathrm B+\mathrm{Boundary}$ 换为完整 $\mathrm{Z0}$，与同一 $\mathsf R_{\rm polar}(\mathcal O)$ 等价。此替换只在这个共同表示域内适用；这些几何条件自身等价于保持原 $u_X$ 的完整实PSD块，指定量子消费者仍消费89章的完整原前件。若完整复型前件还将同一原载体识别为完整复Hermitian块直和，则两种分类的共同域恰为全部块均为标量的经典直和。

证明。93.2逐个原 $X$ 给 $\mathrm{Z0}\Longleftrightarrow S$，89.4给 $S\Longleftrightarrow\mathrm B+\mathrm{Boundary}$；其余原数据保持相同，故89.8直接回接原完整包。归一化只是同载体坐标运输，原 $L:D\times A\to E$、读回 $p:E\to D$ 及它们的来源不能换成新选接口；这里的矩阵线性空间 $L$ 与该过程符号按类型区分。

复型与复Born的一般EJA路线仍使用89.9的一般EJA忠实桥及同一原精确两接口66.3。93.2自身只给实矩阵配对与实纯比较的内积平方。为核对同载体的相容性，设在(93.4)之外还存在保持同一原 $u$、双射整个锥的实线性同构

$$
\Xi:V\longrightarrow\bigoplus_{\beta=1}^{\ell}\operatorname{Herm}_{m_\beta}(\mathbb C),\qquad
\Xi(C)=\bigoplus_{\beta=1}^{\ell}\operatorname{Herm}_{m_\beta,+}(\mathbb C),\qquad
u(X)=\sum_\beta\operatorname{Tr}(\Xi X)_\beta.
$$

于是 $\Xi\Theta^{-1}$ 仿射双射两个完整归一基，保持纯点、包含它们的整个最小面及其仿射维数。若某个 $n_\alpha\ge2$，取该实块内两个正交单位向量的秩一投影。它们的整个最小面是支撑二维实子空间的迹一实PSD基，即仿射维数二的圆盘。其两个像是不同的复纯点：若在不同块，整个最小面是仿射维数一的线段；若在同一块，两条不同复直线张成复二维支撑，整个最小面是迹一 $\operatorname{Herm}_{2,+}(\mathbb C)$，即仿射维数三的球。两种情况均与二维矛盾，故所有 $n_\alpha=1$。实侧此时是单纯形，任意两个不同纯点的整个最小面都是线段；反向同一论证排除所有 $m_\beta\ge2$。因此 $m_\beta=1$ 且 $k=\ell$；反之相同个数的标量块直接给这种保单位整锥同构，单点亦在内。这只用PSD最小面由支撑子空间决定的成熟公式；通常复Hermitian实化把复秩一送为实秩二的现象不能绕开这个内在维数障碍。故在本章受限域中同时满足完整复型前件时，89章的复Born结论只落在经典概率分支，不能解释为非经典实块的复量子重建。

指定二份／三份及读回仍保留89.7—89.9的同一个原 $L,p,\omega$、同一原 $p$ 两次、两实张成、全实 $Z$、含秩一分支的完整(83.8)、C2、整个 $G=1_E$，以及精确PRE以后同一个原资格态和整个原输出上的H13，才消费指定张量、偏迹及 $p_{13}$ 结论。单系统零拼合不供应这些指定接口、其他括号或更高份数。

该一般EJA／指定接口路线的CP仍逐事件、逐分支使用原实线性、同事件HP提升、全实来源律、实际探针与完整相容核，或已经充分供应的递归参考及同事件全锥正性；取得CP以后才用Kraus表示。实际仪器继续保留全部原菜单、记录、顺序接线、旁观者、两预算、真粗粒化、总TP和分支TNI条件。Lüders仍需同一CP分支的锐投影效应、全部确定接受态上的逐点中性和原输出校准；相同效应及概率不决定后态。物理时间仍需原物理时间上的连续、齐次、可逆自同构群、实际逆、钟、单位与动态来源，才使用有限块Hamiltonian结论。

原准备、实际混合、测试、参考、副本、相关联合、记录、质量、控制、ready／flags、失败／拒绝／停止／销毁／返回、旧固定支撑、全部中间切口与合法未来，及原source-adoption，仍完整使用89.7—89.10的共同合同。零质量分支保留，只有正质量才归一化。VII22、24—28仍按89.10及90.12所列各自完整入口复用。93.2的补态、最优分解和93.3的效应是整个原数学锥中的对象，不由数学存在供应实际准备、菜单、记录或有限操作认证。

另一套充分入口直接复用 [Library，*Appendix: an exhaustive binary comparison and a single coupling path*](../../../Library/QuantumStates/mullerududec2012selfduality.md#appendix-an-exhaustive-binary-comparison-and-a-single-coupling-path) §1—§6。其局部原数据是整个 $K,P$、含 $0,u$ 和全部选定 $e_p$ 的原凸菜单 $D_{\rm menu}\subseteq[0,u]$，满足 $e_p(p)=1$、$e_p(q)=e_q(p)$，且有一对 $e_{p_0}+e_{q_0}=u$ 在全 $V$ 成立。另须实际紧连通保归一锥自同构群 $H_{\rm loc}$，在整个 $W=\ker u$ 的某个正定度量下正交并在整个单位球面上传递；这强于仅在纯态上传递。§1先由这项控制得到整个原基为球，再由互反与穷尽固定原测试，并导出有限PD、$D_{\rm menu}=[0,u]$ 和真正的全锥序least确认。该附录不带 $H_{\rm loc}$ 的独立静态PD入口仍保留自己的互反正自确认效应、有限PD、凸菜单及穷尽前件，允许各维球，本身不选择三维。

寄存器前件是对每个有限 $N\ge1$ 完整给定的原紧凸满张成 $K_N\subset V^{\otimes_{\mathbb R}N}$、同一校准 $F^{\otimes N}$、真实产品准备与测试及忠实产品层析。局域控制在所有旁观者坐标上为恒等；另给每个实参数都实际可用的完整非局域路径 $g(t)=\exp(tX)$，某个 $g(t_0)$ 须在整个 $\mathrm{SO}(d)\times\mathrm{SO}(d)$ 之外，$d=\dim W$。同一路径在各 $N$ 的给定连通图边上有精确全载体提升 $g(t)_{ij}\otimes I_{\rm spectators}$，保留所有旁观者相关坐标，且原三元图包含路径 $1-2-3$；原连续控制的完整实参数、实际复合与逆均保留。§2的数学闭包及其引用的 Masanes–Müller–Pérez-García–Augusiak 群分类给 $d=3$ 和 $Q_2$ 或 $T_1Q_2T_1$ 两分支，有限字生成论证将所得群变成实际有限操作，不要求整个实际 $G_N$ 闭。这里 $Q_N$ 是下式的酉共轭群，$T_1$ 是固定Pauli校准中第一腿转置的解析坐标变换，不是实际转置门。

分支选择再支付§3的前置END：实际仿射保质量全域映射 $K_3\to K_2$，保留端点 $1,3$，值域是同一个有序原二元类型，在既定校准中为 $\operatorname{Tr}_2$。或者不用该前置END，改为在原三角形第三条边 $13$ 也供应同一完整路径。§3已分别证明这两种充分条件排除反射分支，并给每个已供应有限连通寄存器

$$
K_N=\mathcal D(2^N),\qquad
Q_N=\{\operatorname{Ad}_U:U\in\mathrm{SU}(2^N)\}\subseteq G_N
$$

及精确有限字控制，其中 $\mathcal D(r)=\{\rho\in\operatorname{Herm}_{r,+}(\mathbb C):\operatorname{Tr}\rho=1\}$。实际仿射效应的Born概率是迹配对；局部全效应与least性由§1得到，全部有限联合测量仍须下述实现资源。路径加END与三角形是资源交换；三角形本身不供应实际丢弃，选择普通 $Q$ 后才合成的SWAP不能倒过来供应前置END。这里分类的是整个原态锥和已生成的控制扇区，不是任意原 $G_N$、所有不可逆事件或其他系统类型。

在上述已识别的原复寄存器上，§4逐个保留原事件或未归一分支 $e:n\to m$、零和全部实准备关系、实线性 $\phi_e$ 及其唯一复线性HP延拓 $\widetilde\phi_e$。令 $d=2^n$、$b=2^m$，只需一个可实际准备的 $\Omega_d=|\omega_d\rangle\langle\omega_d|$，$|\omega_d\rangle=d^{-1/2}\sum_i|ii\rangle$，以及同一原事件的准确整个输出

$$
J_e=(\operatorname{id}_d\otimes\widetilde\phi_e)(\Omega_d)
\in C_{n+m}=\operatorname{Herm}_+(db).
$$

这是同事件、同记录的输出恒等式和整个原输出锥正性；一个真实实线性联合上下文在张成的产品输入上等于 $A\otimes\phi_e(B)$ 足以确定它，事后选择一张正矩阵或只验产品读数则不足。§4引用的矩形Choi定理已给该 $\widetilde\phi_e$ 的数学CP与矩形Kraus表示，原全锥迹等式／预算另给TP／TNI。逐分支保留探针、质量、记录、真粗粒化和总TP后，总CP自动成立，不另付总通道探针；数学全参考CP不生成原事件在任意参考、历史或未来中的可调用性。

实际实现所有这些有限寄存器间通道与有限仪器，仍另需§4的实际纯二元辅助、所得有限控制的顺序复合、校准偏迹且值域为同一保留原寄存器类型的全域丢弃，以及指针的保留输出分支律 $\tau\mapsto(I\otimes\langle z|)\tau(I\otimes|z\rangle)$、实际记录与真粗粒化。辅助空间同时容纳Kraus标签和输入输出维数差；零标签保留，只在正质量时条件化。该附录已给这些资源下的映射与结果标签级实现，不把同矩阵映射认作同设备、来源或合法未来；它构造一种Lüders选择，不决定既有事件的唯一更新，也不供应物理时钟和单位。

这套二元入口不使用一般EJA／FH1入口、(83.8)、插入读回尺度式或H13，改由同种二元、强实际全差分球面控制、非局域耦合、全有限寄存器层析与精确提升及上述选择接口承担条件；89章的指定两三份不能供应这些全 $N$ 资源，93.2亦不能推出它们。它所选的局部 $\mathcal D(2)$ 已是完整复非经典块，故由前述最小面维数论证，与同一原载体上的实ROG加完整 $\mathrm{Z0}$ 无共同模型。一般复块选择与实块分类的交集尚有经典直和；这套强二元非局域入口的同载体交集则为空，不能给原非经典实块制造复型。其他类型的编码、无限系统一致性、实际来源、事件更新和物理时间仍保留各自未由这些前件支付的桥梁。

几何上，把纯态 $p$ 想成一条点亮的方向。归一化以后，原模型里确有一层补态，把除这条方向以外的位置全部铺满，而投影尺在这层上读零。若另一块也可被某把确认尺排除，却还沾着这条方向，把它与补态各混一半就会铺满整个支撑；一把在全物体上非负、在纯态上读一的尺不能在内部态上读零。因此零拼合迫使可排除态真正与纯方向正交。再把任意有正负号的矩阵拆成最省总质量的两堆：原基范数已经给一把共同尺分别读满和读零，刚证的正交性便使两堆恰好成为真正的正负谱部分。这些部分留在原空间，才经(93.16)—(93.19)补齐完整实块。若局部对径失败，93.3反过来从那条较省质量的捷径中提取两盏交叠的纯灯，再用同一层补态给出严格正的中点障碍。

这段证明依赖实ROG、原PSD截面和明示归一化；没有从一般整球载体构造该补态或秩一支撑，故89.12的一般 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$ 仍为未解。本章不将完整 $\mathrm{Z0}$ 缩成纯点版本，也不扩展到一般谱截面或复量子。成熟输入是 Hildebrand 的ROG极射线与PSD最小面结构、90.3的整二态面应用、90.9的基范数极性，以及普通矩阵谱理论和线性代数；90—92章的图族、团族与单关系证明均不重报为新成果。数学归属 `repo-derived` 指(93.11)—(93.14)的零拼合与最优分解组合、由此识别整个原空间的实块分类，以及93.3的原三态定量提升。同载体经典交集是实、复PSD最小面公式的上述应用；二元控制、END／三角形、单Choi与有限实现结论归所引Library附录及其成熟群分类、Choi输入，本节只按原条件复用。此归属不主张全球原创、文献穷尽、Lean kernel核验、经验实现或整个量子起源目标完成。证毕。

## 追加锚（本行以下为增补区）

## 94. 复ROG的固定补态检验、三点相位与完整实复块

### 94.1 同一原锥、任意单位与固定补态候选

**定义 94.1（复秩一生成表示与固定补态检验）。** 保留89.1的非零有限维实载体 $(V,C,u)$、整个紧基 $K$、全部纯点 $P$ 和整个 $[0,u]_{C^*}$。要求有实线性同构

$$
\iota:V\longrightarrow L_0\subseteq\operatorname{Herm}_m(\mathbb C),\qquad
\iota(C)=L_0\cap\operatorname{Herm}_{m,+}(\mathbb C),\qquad
L_0=\operatorname{span}_{\mathbb R}\iota(C),
\tag{94.1}
$$

且每个 $\iota(C)$ 中的矩阵都是属于这个同一锥的有限个**复矩阵秩一**PSD矩阵之和。$\operatorname{Herm}_m(\mathbb C)$ 只是实线性载体；不将复秩一实化成实矩阵秩一。原 $u$ 在 $C\setminus\{0\}$ 上任意严格正，不预付迹、自对偶、Jordan乘积或谱性。表示覆盖整个原锥，并非在更大模型中选取的子锥。

令 $W=\sum_{X\in\iota(C)}\operatorname{ran}X$，$n=\dim_{\mathbb C}W\ge1$。取酉坐标将限制到共同支撑 $W$ 的映射记为 $R$，令 $C_W=R\iota(C)$、$L_W=R\iota(V)$，并运输原单位为 $u_W$。在 $C_W\cap\{u_W=n\}$ 上取行列式最大点 $M$，定义

$$
\begin{gathered}
\Psi(X)=M^{-1/2}(R\iota X)M^{-1/2},\qquad
L=\Psi(V),\qquad h=(R\iota)^{-1}M,\\
C'=L\cap\operatorname{Herm}_{n,+}(\mathbb C),\qquad
\Psi(h)=I_n,\qquad \operatorname{tr}\Psi(X)=u(X).
\end{gathered}
\tag{94.2}
$$

以下定理证明这项整体运输总存在，且 $M$ 唯一。固定一次(94.2)后，若 $n>1$，对每个原纯点 $p$ 固定

$$
a_p^{\rm orig}=\frac{h-p}{n-1}\in K,\qquad
a_{\Psi p}=\Psi(a_p^{\rm orig})=\frac{I_n-\Psi p}{n-1}.
\tag{94.3}
$$

$p\perp x$、$F_p$、$T_p(x)$ 仍准确取(93.2)的全部原效应定义。固定补态候选是

$$
\mathrm{FC}:\quad
\forall p,q\in P,\qquad
p\perp q\ \Longrightarrow\
p\perp\frac{q+a_p^{\rm orig}}2.
\tag{94.4}
$$

$n=1$ 时定义 $\mathrm{FC}$ 为真，不定义分母为零的补态。完整 $\mathrm{Z0}$ 仍是(93.3)对任意原混态 $x,y$ 的条件。完整 $S$ 仍要求全锥序least确认及全部纯点间的数值互反。$\mathrm{FC}$ 只量化两个纯点，并为第一个纯点使用一份预先固定的原补态；没有把补态称为纯点。

### 94.2 固定补态、完整零拼合与实复块的等价

**定理 94.2（同一复ROG域内的完整分类）。** 在定义94.1的表示域内，(94.2)保原 $u$ 运输整个锥、基、纯点、最小面和全部 proper 效应，原 $\mathrm B$ 自动成立，全部不同二纯点的整个最小面为 $B^1,B^2$ 或 $B^3$。以下条件等价：

1. 固定补态条件 $\mathrm{FC}$。
2. 完整混态条件 $\mathrm{Z0}$。
3. 在(94.2)坐标中，所有纯 $p,q$ 满足 $p\perp q\Rightarrow\operatorname{tr}(pq)=0$。
4. 在同一坐标中，每个 $Z\in L$ 的普通Hermitian正负谱部分 $Z_+,Z_-$ 都在 $L$。
5. 在同一坐标中，$I_n\in L$ 且 $A\circ B=(AB+BA)/2\in L$ 对全部 $A,B\in L$ 成立。
6. 完整 $S$。
7. 存在有限组正整数大小 $r_\alpha,s_\beta$ 及保持整个原锥、原 $u$ 的实线性同构
   $$
   \begin{gathered}
   \Theta:V\longrightarrow
   \bigoplus_{\alpha}\operatorname{Sym}_{r_\alpha}(\mathbb R)
   \ \oplus\
   \bigoplus_{\beta}\operatorname{Herm}_{s_\beta}(\mathbb C),\\
   \Theta(C)=
   \bigoplus_{\alpha}\operatorname{PSD}_{r_\alpha}(\mathbb R)
   \ \oplus\
   \bigoplus_{\beta}\operatorname{Herm}_{s_\beta,+}(\mathbb C),\qquad
   u(X)=\operatorname{tr}\Theta(X).
   \end{gathered}
   \tag{94.5}
   $$
   可取 $\sum_\alpha r_\alpha+\sum_\beta s_\beta=n$；在(94.2)后，仅需酉换基及按坐标分块即得到这种形式。标量块只列一次，复块可约定 $s_\beta\ge2$。

这里第7项也允许任意保原单位的整锥同构，不预先要求它来自合同变换；它的存在已足以推出其余内在条件。谱部分、Jordan乘积及下述相位矩阵单位的断言专属(94.2)坐标。

证明。先证明整体归一化。全部 $L_0$ 都在 $W^\perp$ 上为零，因为 $L_0$ 由锥张成；$R$ 因而没有丢失原向量。有限个锥元的像空间张成 $W$，其和在 $W$ 上正定。严格正的 $u_W$ 给紧切片 $C_W\cap\{u_W=n\}$；正定可行点使行列式最大值严格正，所以最大点 $M\succ0$。若 $Y\in L_W\cap\ker u_W$，充分小的正负 $t$ 均使 $M+tY$ 留在该切片，一阶条件给 $\operatorname{tr}(M^{-1}Y)=0$。这使 $u_W$ 与 $\operatorname{tr}(M^{-1}\,\cdot\,)$ 成比例；在 $M$ 上二者均等于 $n$，故比例为一。得到(94.2)。正定矩阵上的 $\log\det$ 沿非零Hermitian方向的二阶导数为

$$
-\operatorname{tr}\bigl(M^{-1}YM^{-1}Y\bigr)
=-\operatorname{tr}\bigl((M^{-1/2}YM^{-1/2})^2\bigr)<0,
\tag{94.6}
$$

故最大点唯一。合同保持复矩阵秩及ROG；对偶拉回双射整个 $[0,u]$、确认集和排除关系。原纯点在运输后恰为

$$
P'=\{vv^*\in L:\|v\|=1\}.
\tag{94.7}
$$

秩一PSD射线在环境锥中已极端；反向，ROG分解使任何更高秩锥元都不能生成极射线。这也证明(94.3)确是原态：$I_n-p'\in L$、$I_n-p'\succeq0$ 且迹为 $n-1$。

核对整个二纯最小面，不假设任何等价条件。任意 $X\in C'$ 有

$$
\operatorname{face}_{C'}(X)=
\{Y\in C':\operatorname{ran}Y\subseteq\operatorname{ran}X\}.
\tag{94.8}
$$

右侧是面；若 $Y$ 在右侧，$X$ 在自身像空间正定，故有 $\varepsilon>0$ 使 $X-\varepsilon Y\in C'$，任一含 $X$ 的面都须含 $Y$。这证明等式。对不同纯 $p'=vv^*,q'=ww^*$，令 $U=(v\ w)$；它满列秩，二纯点的整个最小锥面为 $UAU^*$、$A\in\mathcal M\cap\operatorname{Herm}_{2,+}(\mathbb C)$，其中

$$
\mathcal M=\{A:UAU^*\in L\}
=\left\{\begin{pmatrix}a&z\\\bar z&b\end{pmatrix}:
a,b\in\mathbb R,\ z\in J\right\},\qquad
J\le_{\mathbb R}\mathbb C.
\tag{94.9}
$$

因为 $E_{11},E_{22}\in\mathcal M$，减去对角项即可得到这个准确分解。原归一化在这里为 $\operatorname{tr}(GA)$、$G=U^*U\succ0$。若 $J=0$，是两条独立射线的归一线段。若 $\dim_{\mathbb R}J=1$，先用二点对角酉把 $J$ 化为 $\mathbb R$；对实对称 $A$ 有 $\operatorname{tr}(GA)=\operatorname{tr}((\operatorname{Re}G)A)$，而 $\operatorname{Re}G$ 在实向量上正定，再作实合同即得标准实二阶迹一PSD圆盘。若 $J=\mathbb C$，用 $A\mapsto G^{1/2}AG^{1/2}$ 得标准复二阶迹一PSD三维球。于是整个面依次为 $B^1,B^2,B^3$，其全部仿射效应仍由整个原效应的限制来检验，未假设这些限制满射到局部全效应。这里的极射线与面工具属于 Hildebrand，[arXiv:1409.4781v2 §3.2、§9](https://arxiv.org/html/1409.4781v2#S9) 所述可推广部分；没有调用其复推广仍未建立的 Theorem 3.18。

以下在(94.2)坐标中省略撇号。若 $n=1$，$L=\mathbb R$、$C=\mathbb R_+$、$K=P=\{1\}$，$F_p=\{u\}$、$D_p=\varnothing$，全部条件成立，并取一个标量块。ROG单射线的生成元必为复秩一，故原单点基也恰属此支。以下 $n>1$。

完整 $\mathrm{Z0}\Rightarrow\mathrm{FC}$：投影限制效应 $h_p(X)=\operatorname{tr}(pX)$ 在整个原锥满足 $0\le h_p\le u$、$h_p(p)=1$、$h_p(a_p)=0$，所以 $p\perp a_p$，可将 $\mathrm{Z0}$ 用于 $q,a_p$。这里只验证一把原效应合法，尚未把全部原效应识别为环境正收缩。

$\mathrm{FC}\Rightarrow$ 第3项：若 $p=vv^*$、$q=ww^*$ 是可排除纯对，却有 $c=\operatorname{tr}(pq)=|v^*w|^2>0$，则 $\ker a_p=\mathbb Cv$ 与 $\ker q$ 的交为零，故 $(q+a_p)/2\succ0$。正定矩阵是 $C$ 的相对内点；在此点为零的原正泛函，沿每个 $Y\in L$ 作充分小的双向扰动便被迫在 $Y$ 上为零，不能确认 $p$。这与 $\mathrm{FC}$ 矛盾。反向，若 $\operatorname{tr}(pq)=0$，$h_p$ 本身就是全域排除见证。

第3项 $\Rightarrow$ 第4项复用93.2的成熟基范数极性，只核对其复域承重点。对任意 $Z\in L$，在这个有限维**实**序空间取同一个最优分解及同一个对偶极大点：

$$
\begin{gathered}
Z=X-Y,\quad X,Y\in C,\quad -u\le b\le u,\qquad
b(Z)=\|Z\|_C=u(X)+u(Y),\\
f=(u+b)/2\in[0,u],\qquad f(X)=u(X),\quad f(Y)=0.
\end{gathered}
\tag{94.10}
$$

极值达到性与双重饱和正是90.9、(93.12)所用的基范数／序单位对偶，归 Lami–Palazuelos–Winter，*Ultimate data hiding in quantum mechanics and beyond*，arXiv:1703.03392v2 §II.1 Definition 2、Lemma 3；它不依赖实矩阵表示。ROG给 $X=\sum_i\alpha_ip_i$、$Y=\sum_j\beta_jq_j$，非零系数全正，故这个共同原效应满足 $f(p_i)=1$、$f(q_j)=0$。第3项使所有交叉 $|v_i^*w_j|^2=0$，所以 $XY=0$。Hermitian谱定理遂给 $X=Z_+$、$Y=Z_-$；一侧为零时直接成立。这是同一实现中的全部交叉项，未拼合分别最优的不同分解。

第4项 $\Rightarrow$ 第5项：$I_n\in L$ 使 $(A-tI_n)_+\in L$ 对每个实 $t$ 成立。若 $A$ 的不同特征值为 $\lambda_1<\cdots<\lambda_\ell$、谱投影为 $P_j$，则

$$
(A-\lambda_iI_n)_+
=\sum_{j>i}(\lambda_j-\lambda_i)P_j.
\tag{94.11}
$$

从 $i=\ell-1$ 递减解出 $P_\ell,\ldots,P_2$，再用 $I_n$ 得 $P_1$；$\ell=1$ 时直接用 $I_n$。所以 $A^2\in L$，极化给 $A\circ B\in L$。反向，第5项使 $A$ 的全部实多项式在 $L$，在有限谱上插值函数 $\max(t,0)$、$\max(-t,0)$ 即得第4项。上述谱理论都是运输后普通复矩阵谱理论。

第4项也给全部效应和完整 $S$。用实迹内积识别 $L^*$，令 $C^\vee=\{E\in L:\operatorname{tr}(EX)\ge0\ (\forall X\in C)\}$。若 $E\in C^\vee$，其 $E_-\in C$，于是 $0\le\operatorname{tr}(EE_-)=-\operatorname{tr}(E_-^2)$，故 $E_-=0$。所以 $C^\vee=C$，这时才有整个原效应区间的准确表示

$$
[0,u]=\{f_E:E\in L,\ 0\preceq E\preceq I_n\},\qquad
f_E(X)=\operatorname{tr}(EX).
\tag{94.12}
$$

若 $f_E(p)=1$、$p=vv^*$，则 $v^*(I_n-E)v=0$ 给 $Ev=v$；Hermitian性消去该方向的交叉块，故 $E=p\oplus E_\perp$、$E_\perp\succeq0$。于是 $E-p\in C$，证明 $e_p=h_p$ 是 $F_p$ 在全锥序中的least元。$\operatorname{tr}(pq)=\operatorname{tr}(qp)$ 给互反。反向在任意原载体，完整 $S$ 使 $D_p=K\cap\ker e_p$，这是凸零面，故 $S\Rightarrow\mathrm{Z0}$。至此除分块外的等价已经闭合。

现由第5项直接分类相位，不使用抽象Jordan分类或表示唯一性黑箱。先从 $I_n$ 的ROG分解选一个秩一方向，归一为 $p_1\in L$。$I_n-p_1$ 是原锥内正交投影；它的ROG分解项都支撑在该投影的像中，选一个方向归一为 $p_2$，则 $p_1p_2=0$。重复减去所选单位投影，每次秩降一，得 $I_n=\sum_{i=1}^np_i$、$p_ip_j=0$。酉换基后 $p_i=E_{ii}\in L$。这只用了原复秩一生成，不将高秩primitive投影当作秩一。

对有序不同指标定义

$$
H_{ij}(z)=zE_{ij}+\bar zE_{ji},\qquad
K_{ij}=\{z\in\mathbb C:H_{ij}(z)\in L\}\le_{\mathbb R}\mathbb C.
\tag{94.13}
$$

对每个 $A\in L$，Jordan闭合给
$$
4E_{jj}\circ(E_{ii}\circ A)=H_{ij}(A_{ij})\in L,\qquad
L=\bigoplus_i\mathbb RE_{ii}\ \oplus\
\bigoplus_{i<j}H_{ij}(K_{ij}).
\tag{94.14}
$$

第一式逐项隔离任意非对角边；任一 $A$ 减去这些边和其对角项便为零，反向各项都属于 $L$，所以第二式是准确直和，不留下隐藏的跨边线性约束。两端共轭及三点关系为

$$
K_{ji}=\overline{K_{ij}},\qquad
H_{ij}(z)\circ H_{jk}(w)=\tfrac12H_{ik}(zw),\qquad
K_{ij}K_{jk}\subseteq K_{ik}\quad(i,j,k\ \text{两两不同}).
\tag{94.15}
$$

第一式由 $H_{ji}(z)=H_{ij}(\bar z)$；第二式由 $E_{ab}E_{cd}=\delta_{bc}E_{ad}$ 直接相乘；第三式再用实线性消去 $1/2$。两点回返的公式则是 $H_{ij}(z)\circ H_{ij}(w)=\operatorname{Re}(z\bar w)(E_{ii}+E_{jj})$，并不强加 $K_{ij}K_{ji}\subseteq\mathbb R$；后一个错误条件会排除完整复二阶块。

定义 $i\sim j$ 当且仅当 $i=j$ 或 $K_{ij}\ne0$。共轭给对称性；若 $i,j,k$ 不同且前两条边非零，选非零 $z,w$，复数乘积 $zw\ne0$，(94.15)给第三条边非零。故 $\sim$ 是等价关系，每个非平凡连通块已经是完全图，不同块间无条目。

每条非零边的实维数只有一或二。若某块有 $K_{ij}=\mathbb C$，对任一第三点 $k$ 取 $0\ne w\in K_{jk}$，则 $\mathbb Cw\subseteq K_{ik}$ 给 $K_{ik}=\mathbb C$。再用路径 $j-i-k$ 得 $K_{jk}=\mathbb C$，所以从 $i$ 出发的全部边均为 $\mathbb C$；任意不同 $a,b\ne i$ 再用 $a-i-b$ 得 $K_{ab}=\mathbb C$。整个块因而是完整复Hermitian块。二点块若有二维边，已经是完整 $\operatorname{Herm}_2(\mathbb C)$，无需第三点传播。

若没有二维边，则这个连通块的所有非零边均为一维实线。选根点 $o$，对 $i\ne o$ 写 $K_{io}=\zeta_i\mathbb R$、$|\zeta_i|=1$，置 $\zeta_o=1$。对不同 $i,j\ne o$，两端共轭与三点乘法给

$$
\zeta_i\bar\zeta_j\mathbb R
=K_{io}K_{oj}\subseteq K_{ij};
\qquad
K_{ij}=\zeta_i\bar\zeta_j\mathbb R
\quad(i\ne j).
\tag{94.16}
$$

最后等式由两边均为非零一维实线，涉及根点的边按定义也成立。取 $D=\operatorname{diag}(\zeta_i)$，$D^*LD$ 在这个块上恰为全部实对称矩阵。其三角形相位条件准确是

$$
\theta_{ij}+\theta_{jk}-\theta_{ik}=0\pmod\pi,\qquad
K_{ij}=e^{i\theta_{ij}}\mathbb R.
\tag{94.17}
$$

任意闭环相位之和亦为 $0\pmod\pi$。任意选定的单位代表沿环相乘只能保证属于 $\{\pm1\}$；在同一实块的三角形上，把一条代表改号就会把环积由 $+1$ 改成 $-1$，边空间完全不变。(94.16)实际给出了相容代表 $\zeta_i\bar\zeta_j$，这些代表才沿每个环望远镜相消为 $+1$。这是实线的相位平坦性，不把模 $\pi$ 条件擅改成任意代表的模 $2\pi$ 条件。

单点块为 $\mathbb R$；二点的零边给两个标量块，一维边给相位调整后的实二阶块，二维边给复二阶块。断开块由(94.14)准确分离。以上穷尽所有实线性 $K_{ij}\subseteq\mathbb C$，因此给(94.5)且总大小为 $n$。标准四元数矩阵的通常复表示中primitive投影为复秩二，重复表示 $A\mapsto A\otimes I_k$、$k>1$ 的极射线也不是复秩一；它们不满足(94.1)的ROG前件，不能成为遗漏分支。

最后，第7项中的完整实／复块由普通谱理论秩一生成，并在实迹配对下自对偶；全部效应是逐块正收缩。同一确认分块计算给全锥序least及互反，即完整 $S$。任意第7项的保原 $u$ 整锥同构都对偶运输整个效应区间，故这一方向不依赖先验的合同表示。由已证明的等价再回到第5项，显式酉分类适用于所选(94.2)。因此所有方向闭合。证毕。

### 94.3 全效应最小尺、谱混合与三纯点相位

**推论 94.3（同载体的谱与相位几何）。** 在定理94.2的等价条件下，令 $\rho=\Theta x$、$p'=\Theta p$。整个原 proper 区间、least尺和任意原混态的最小读数为

$$
\begin{gathered}
f_E(X)=\operatorname{tr}\bigl(E\Theta X\bigr),\qquad
E\in\bigoplus_\alpha\operatorname{Sym}_{r_\alpha}(\mathbb R)
\oplus\bigoplus_\beta\operatorname{Herm}_{s_\beta}(\mathbb C),\\
f_E\in[0,u]\ \Longleftrightarrow\
0\preceq E_\gamma\preceq I_\gamma\quad(\text{每个块 }\gamma),\\
e_p(X)=\operatorname{tr}\bigl(p'\Theta X\bigr),\qquad
T_p(x)=\operatorname{tr}(p'\rho)\quad(p\in P,\ x\in K).
\end{gathered}
\tag{94.18}
$$

每个原混态有同一原基内的正交谱混合 $x=\sum_j\lambda_jp_j$，$\lambda_j\ge0$、$\sum_j\lambda_j=1$、$e_{p_i}(p_j)=\delta_{ij}$。纯几何准确为各实块的 $\mathbb{RP}^{r_\alpha-1}$ 与各复块的 $\mathbb{CP}^{s_\beta-1}$ 的不交并；同一实块内不同纯点的整个二纯面为 $B^2$，同一复块为 $B^3$，异块为 $B^1$。局部对径都可由原全域效应区分，且固定 $p$ 的同一个 $e_p$ 排除其全部局部对径，故原 $\mathrm A,\mathrm H,\mathrm{Boundary},\mathrm Q$ 都成立。

对同块三个纯点 $p_v=vv^*$、$p_w=ww^*$、$p_z=zz^*$，定义相位不变量

$$
\begin{gathered}
\mathcal B(v,w,z)=\operatorname{tr}(p_vp_wp_z)
=(v^*w)(w^*z)(z^*v),\\
|\mathcal B|^2
=e_{p_v}(p_w)e_{p_w}(p_z)e_{p_z}(p_v),\\
\det\operatorname{Gram}(v,w,z)
=1-|v^*w|^2-|w^*z|^2-|z^*v|^2
+2\operatorname{Re}\mathcal B\ge0.
\end{gathered}
\tag{94.19}
$$

$\mathcal B$ 不受三个向量各自的单位相位改变影响；反转三点次序使它共轭。实块中它为实数，但不必为正；复块容许非实值。三个成对比较只固定其模，不能一般决定其相位。

证明。(94.18)是(94.12)和least性的同数据运输；每个 $f\in F_p$ 都满足 $f-e_p\in C^*$，所以在任意原混态上取最小值确得 $e_p(x)$，不限于纯点。对各实／复块分别作普通正交／酉谱分解，再合并全部块的特征值，便得上述原谱混合，零特征值可省略。这里没有要求谱混合成为实际准备程序。

实块的复秩一投影若矩阵条目全实，选一个非零坐标并调整整体相位使它实且正，则与该坐标相乘的矩阵条目迫使其余坐标全实。因此纯向量模去正负号正是 $\mathbb{RP}^{r-1}$；复块模去全部单位相位为 $\mathbb{CP}^{s-1}$。二纯面的结论用(94.8)：同块两条不同的实或复直线张成相应二维支撑，完整块给全部实或复二阶PSD面；异块则只有两条独立射线。实／复二阶迹一基的中心均为二维支撑单位的一半，对径投影之和为该支撑单位，故互相矩阵正交；异块两端也正交。(94.18)遂给全域排除及共同尺，再由89.4得边界和规范商。商尺与 $e_p$ 同为同一确认集的least元，因而相等；单点按空对径族约定。

(94.19)逐次相乘秩一矩阵并展开三阶Gram行列式即得。Gram矩阵PSD给最后的不等式；各向量的相位因子沿乘积相消。取复二阶块内

$$
v=(1,0)^{\mathsf T},\qquad
w=(1,1)^{\mathsf T}/\sqrt2,\qquad
z=(1,i)^{\mathsf T}/\sqrt2
\tag{94.20}
$$

时，三个成对比较均为 $1/2$，而 $\mathcal B=(1+i)/4$。将三个向量同时共轭，全部成对比较不变，$\mathcal B$ 变成 $(1-i)/4$，故比较数不决定三点相位。实二维中取与固定轴成 $0,\pi/3,2\pi/3$ 的三个单位向量，则 $\mathcal B=-1/8$。因此(94.17)对坐标边实线的平坦性，也不要求任意三个纯向量的比较乘积为正。若三个纯点不全在同一块，矩阵乘积及 $\mathcal B$ 为零，相位无需定义。

谱定理、射影空间识别、Gram行列式和三纯点迹积是成熟线性代数及几何工具；这里将其用于(94.5)已经证明的同一个原载体，不另报这些公式为独立的新分类。证毕。

### 94.4 候选失败的全域三态严格正障碍

**命题 94.4（复域的定量失败提升）。** 在定义94.1的整个原载体上，不假设候选成立。若 $\mathrm{FC}$ 失败，则在(94.2)坐标中有原纯点 $s=vv^*$、$q=ww^*$，以及固定原补态 $a_s=(I_n-s)/(n-1)$，使

$$
\begin{gathered}
s\perp q,\qquad s\perp a_s,\qquad
c=\operatorname{tr}(sq)=|v^*w|^2\in(0,1),\\
m=(q+a_s)/2\succ0,\qquad
m-\frac{c}{2n}s\in C',\qquad
T_s(m)\ge\frac{c}{2n}>0.
\end{gathered}
\tag{94.21}
$$

同一结论也从任意未闭合的谱部分、或从一对不能被原全域 proper 效应区分的局部球对径导出。所有零见证、锥差和最小值都在整个原锥及整个原效应区间中成立；运输回 $V$ 后，三个态的实线性张成至多三维。$n=2$ 时 $a_s$ 是纯点；$n>2$ 时其复秩为 $n-1$，确是混态。

证明。若 $\mathrm{FC}$ 失败，取其失败纯对 $s,q$。若 $\operatorname{tr}(sq)=0$，合法原效应 $h_s$ 同时排除 $q,a_s$，也排除其中点，与失败矛盾。所以 $c>0$；$s\perp q$ 使 $s\ne q$，故 $c<1$。$h_s$ 给 $s\perp a_s$，核交为零给 $m\succ0$。

将(93.24)的加权Cauchy–Schwarz明确核对到复域。写 $w=av+b$、$b\perp v$、$|a|^2=c$，任意复向量为 $\xi=\alpha v+k$、$k\perp v$。于是

$$
\begin{aligned}
c|\alpha|^2
&=|w^*\xi-b^*k|^2\\
&\le\bigl(1+(n-1)\|b\|^2\bigr)
\left(|w^*\xi|^2+\frac{\|k\|^2}{n-1}\right)\\
&\le n\,\xi^*(q+a_s)\xi.
\end{aligned}
\tag{94.22}
$$

第一步用 $w^*\xi=\bar a\alpha+b^*k$，第二步是复内积的加权Cauchy–Schwarz，第三步用 $\|b\|^2=1-c\le1$。所以 $m-cs/(2n)\succeq0$；该差又在 $L$，故属于原截面锥 $C'$。每一把原确认效应 $g\in F_s$ 都非负于这个锥差，遂有 $g(m)\ge c\,g(s)/(2n)=c/(2n)$，取全部 $g$ 的最小值即得(94.21)。这不把效应缩到投影限制或环境收缩，也不需要更强的Schur补常数。

若从 $Z\in L$ 的某个 $Z_\pm\notin L$ 出发，在(94.10)的同一最优分解中作ROG纯分解；若全部交叉纯对都矩阵正交，则 $X=Z_+$、$Y=Z_-$，矛盾。因此有共同饱和效应确认的 $s$ 和被其排除的 $q$，且 $\operatorname{tr}(sq)>0$。上面的补态及下界直接适用。Jordan不闭合也由定理94.2中第4、5项的等价归入此情形。

若从局部球对径 $p_0,r_0$ 的原全域区分失败出发，90.9的成熟极性给 $0<\|p_0-r_0\|_C<2$，故(94.10)可取 $u(X)=u(Y)=t\in(0,1)$。若所有交叉纯项正交，$X=(p_0-r_0)_+$、$Y=(p_0-r_0)_-$ 的支撑都在 $\operatorname{ran}(p_0+r_0)$；由(94.8)，$X/t,Y/t$ 属于起始的整个二纯面。它们给该面内的分解
$p_0-r_0=t(X/t-Y/t)$，总质量 $2t<2$；但球的对径差在该局部基范数中恰为二，矛盾。故又可抽取上述非正交的全域可排除纯对。这个论证同时覆盖 $B^1,B^2,B^3$，没有把原局部对径在运输前预设为环境矩阵正交。最后以 $\Psi^{-1}$ 运输三态、全部效应和锥差，保留原质量、中点及严格正下界。证毕。

### 94.5 同一完整量子候选与逐消费者回接

**定义 94.5（复ROG域上的完整固定补态候选）。** 完整保留89.7的同一个原装饰元组 $\mathcal O$、共同来源合同 $\mathfrak S(\mathcal O)$ 及全部非几何条件。限定每个原 $X=A,D,E$ 已有定义94.1的整个复ROG表示，$u_X$ 允许任意严格正；各自在同一原单位下执行(94.2)。仅将这些原载体上的几何项 $\mathrm B+\mathrm{Boundary}$ 换成 $\mathrm{FC}$，记完整候选为 $\mathsf R_{\rm FC}^{\mathbb C\text{-}\rm ROG}(\mathcal O)$。没有另换原准备、测试、参考、过程、读回、来源或未来，也没有由本条件生成矩阵表示的前件。

**推论 94.6（完整同数据替换及相容的非经典复模型）。** 在定义94.5的共同表示域和同一来源合同上，

$$
\mathsf R_{\rm FC}^{\mathbb C\text{-}\rm ROG}(\mathcal O)
\Longleftrightarrow
\mathsf R_{\rm polar}(\mathcal O)
\Longleftrightarrow
[\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}]^{\rm ev}(\mathcal O),
\tag{94.23}
$$

并与89.8所列其余完整包等价。本表示域允许真正非经典的完整复矩阵块；它不自动排除非标量实块。每个量子消费者仍按89.7—89.10及下述独立二元入口的全部原前件应用。

证明。对每个同一原 $X$，定理94.2给 $\mathrm{FC}\Longleftrightarrow S\Longleftrightarrow\mathrm{Z0}$，并自动给 $\mathrm B$；89.4给 $S\Longleftrightarrow\mathrm B+\mathrm{Boundary}$。对偶运输整个效应区间，故没有缩小确认或排除的量词。所有非几何数据逐项相同，89.8直接给(94.23)。矩阵子空间 $L_X$ 与原过程 $L:D\times A\to E$ 按类型区分，数学坐标运输不能另选该过程或读回。

复型与Born仍按89.9消费一般EJA忠实桥及同一原精确两接口66.3。分类自身允许实、复块并存；若同一原载体还被这些完整复型条件识别为复Hermitian直和，则同数据面维数排除每个大小至少二的实块：该实块内二纯面的维数为二，而全复直和内两个不同纯点的整个面只有维数一或三。因此只剩标量实块和允许的非标量复块。完整 $\operatorname{Herm}_{m,+}(\mathbb C)$、$m\ge2$、$u=\operatorname{tr}$ 本身由复秩一投影生成，属于(94.1)，满足(94.18)和 $\mathrm{FC}$，纯几何为 $\mathbb{CP}^{m-1}$，是明确非经典实例；93.4仅在**实秩一**表示域得到的经典交集不限制这里。这项数学实例不自带原实际菜单、事件和来源。复型条件成立后，全部原实际效应和原态的Born概率为 $\sum_\gamma\operatorname{Tr}(E_\gamma\rho_\gamma)$，同块纯比较为模方、异块为零，零和不等中央质量保留。

指定二份／三份与读回仍准确消费89.7—89.9的同一个原 $L,p,\omega$、同一读回 $p$ 两次、两实张成、所有实输入上的 $Z$、含秩一分支的完整(83.8)、C2和整个 $G=1_E$。恢复精确PRE以后，才使用原资格集合中同一个原态及其**整个**原输出的H13，不逐块换态或反选资格；原迹、伴随、中心因子、零质量和空活跃集全部保持。89.9才给指定 $M(a,b)=a\otimes b$、$L(d,c)=d\otimes c$、$p=\operatorname{Tr}_1$、$p_{13}=\operatorname{Tr}_2$，作用于整个相关／纠缠锥。其他括号、四份以上来源和无限一致性不由本章几何代付。

这条一般EJA／指定接口路线的CP逐事件、逐未归一分支保留89.9及85.15—85.16的完整原前件：原实线性映射、唯一复HP延拓、同事件实线性提升、全部实输入上的精确(87.21)、其全部复矩阵变量上的相容核，以及实际指定探针和准确整个输出；或复用已经充分供应的递归参考及同事件全锥正性入口。待认证的HP提升全锥正性不能先由归一化或中点律假定。CP取得后才用矩形Kraus表示。实际仪器继续保留typed输入输出、同一原事件／分支／记录、真实参考、旁观者、顺序接线、两预算、原全菜单、同族真粗粒化与共同重置输入行一致；总TP和分支TNI分别支付，分解不制造环境或可调用性。

更新仍按89.9：只对正输入质量读取分支概率，只对正分支质量归一化，零分支的记录与未来不删。同一个CP分支还须锐投影效应、对全部确定接受态的逐点中性及原输出校准，才消费Lüders唯一性；相同概率与效应不决定后态。物理时间仍须原物理时间上的连续、齐次、可逆 $*$ 自同构群、实际逆、钟、单位与动态来源，才用有限块Hamiltonian结论；谱几何不是这些前件。

全有限二元控制使用另一套已经证明的充分入口，准确引用 [Library，*Appendix: an exhaustive binary comparison and a single coupling path*][L] §1—§6及93.4的完整参数说明。其局部入口保留整个原 $K,P$、含 $0,u$ 和全部选定自确认效应的原凸菜单、端点互反、全 $V$ 上一对效应穷尽单位，另给实际紧连通局域控制群，在整个 $\ker u$ 的正定度量单位球面上传递并正交；不是仅在纯态上传递。每条原连续控制的全部实参数、实际复合与逆均保留。独立静态PD入口仍有自己的有限PD、互反正自确认、凸菜单和穷尽前件，单独允许各维球；本章的least几何不供应上述实际控制。

该二元入口对每个有限 $N$ 还须整个原紧凸满张成 $K_N\subset V^{\otimes_{\mathbb R}N}$、同一 $F^{\otimes N}$ 校准、真实产品准备／测试和忠实产品层析；在 $N=2$ 给全部实参数实际可用的非局域路径 $g(t)=\exp(tX)$，某个 $g(t_0)$ 在整个 $\mathrm{SO}(d)\times\mathrm{SO}(d)$ 之外。它在每个已给定有限连通图上有精确全载体提升 $g(t)_{ij}\otimes I_{\rm spectators}$，恒等作用于全部旁观者相关坐标，原三元图含路径 $1-2-3$。再支付前置END：保留端点 $1,3$ 的实际仿射保质量全域映射，值域为**同一个有序原二元类型** $K_2$，在固定校准中为 $\operatorname{Tr}_2$；或以原三角形第三边的同一完整路径替代该前置END。该附录已分别证明排除反射分支，给 $d=3$、每个已供应有限寄存器的 $K_N=\mathcal D(2^N)$ 和实际有限字群 $Q_N=\operatorname{Ad}_{\mathrm{SU}(2^N)}\subseteq G_N$，不要求整个实际 $G_N$ 闭。三角形不自动供应实际丢弃，选择普通分支后才合成的SWAP不能反过来供应前置END；分类范围是原态锥和生成控制扇区。

在这些已识别的原复寄存器上，Library §4逐个事件或分支保留原记录、合法性、ready与未来、零及全部实准备关系、原实线性 $\phi_e:n\to m$、唯一复HP延拓，以及对全部原正输入的独立迹等式／预算。CP仅需一个实际可准备的归一最大纠缠输入 $\Omega_{2^n}$ 和该**同一原事件、同一记录**的准确整个输出
$J_e=(\operatorname{id}_{2^n}\otimes\widetilde\phi_e)(\Omega_{2^n})\in C_{n+m}$。
同一原实线性联合上下文在张成产品输入上的精确产品律足以确定该输出；它不是事后选出的正证书。该附录已由矩形Choi定理给数学CP、Kraus及独立预算下的TP／TNI，包括标量端与零分支。每个实际分支分别认证，保留实际全菜单、记录、真粗和及总TP，总CP便已成立，不另需总通道探针；数学全参考CP不制造原事件在任意上下文中的来源或权限。

Library §4的所有有限通道／仪器实现结论也已在其资源前件下成立：实际纯二元辅助、所得有限控制的顺序复合、值域为同一保留原寄存器类型且校准为偏迹的全域丢弃、指针保留输出分支律、实际记录及真粗粒化。辅助空间同时容纳Kraus标签和输入输出维数差；零标签保留，只在正质量时条件化。所得为映射与结果标签级实现，不凭映射相同识别设备、事件或历史；构造一种Lüders选择也不决定既有事件的唯一更新。这套全 $N$ 二元前件不消费FH1／一般EJA入口、(83.8)、插入读回尺度或H13，而支付自己的强控制、耦合、层析、精确提升和分支选择资源。89章指定两三份与本章 $\mathrm{FC}$ 均不能供应它们；其标准复寄存器则确实属于本章复ROG域。

原生终端来源仍完整使用89.10的各自入口。VII17.2的旧路线保留原有限predictive rank；VII24—26的新路线在原复射影载体、全部原字与terminal futures、密度、统计 $\mathrm R_{10}$、full-future uniform ready-return及四前缀全未来行等式下已给Born，再导出有限容量和完成PSD，不另预付容量。完整联合菜单须在同一联合行上支付对应全标签、全未来前件；独立非恒定粗Born加同秩的VII22.3入口也已在其原前件下给联合下降／回返，字面细标签识别另守完整校准。这里不重报这些已经取得的结论为缺口，也不把它们自己的完成载体直接认作本候选的原 $A,D,E$。

最后，共同 $\mathfrak S(\mathcal O)$ 仍逐项保留原准备、实际混合、全部测试与菜单、参考、副本、相关联合、记录、质量、控制、权限、钟与单位、ready／flags、失败／拒绝／停止／销毁／返回、旧固定支撑、每个中间切口和全部合法未来，以及原source-adoption。补态、谱分解、正矩阵效应和相位坐标的数学存在均不能替代这些来源。以上所有消费者结论均是原定理在全前件下的应用，本章新增的替换只发生于(94.23)的几何位置。证毕。

### 94.6 简化的准确比较与一般目标的剩余关系

**命题 94.7（固定补态所关闭及仍保留的桥）。** 在同一个完整复ROG表示域内，$\mathrm{FC}$ 与任意混态零拼合具有完全相同的模型类，故得到一个量词更小而等价的完整纸面候选；它关闭的是固定补态检验到全域排除正交、谱部分闭合、实复整块分类、全效应least尺与原 $\mathrm A,\mathrm H,S$ 的桥，以及89.7同数据几何替换。它不证明一般原载体中的 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$，也不证明一般复ROG内的纯纯版本

$$
\mathrm G_2:\quad
\forall p,q,r\in P,\qquad
[p\perp q\ \land\ p\perp r]\Longrightarrow p\perp(q+r)/2
\tag{94.24}
$$

已经足以推出完整 $\mathrm{Z0}$。矩阵、复标量与秩一生成仍是表示域的实质前提，复型唯一选择及量子消费者仍有94.6列明的原前件。

证明。等价模型类由94.2给出；(94.4)只检验两个纯点和由第一个纯点固定的补态，替代(93.3)的两个任意混态量词。补态是原锥内确实存在的数学态，不是新造的可选效应或更大状态空间。$\mathrm{FC}$ 的定义依赖固定的表示与(94.2)；不同允许表示若产生不同的 $h$，也各自由94.2与同一内在 $\mathrm{Z0}$ 等价，不要求表示之间酉等价，更没有借此证明 Hildebrand Theorem 3.18 的一般复推广。

$n>2$ 时补态秩大于一，(94.24)不能直接用于 $q,a_p$；把 $a_p$ 写成纯混合也不能把纯纯中点条件递归用到混态端点。本章没有这种递归推论，也没有给一般复ROG内(94.24)的反例。因此纯纯问题保持未决，不能由本章的三向量有限提升改名为三纯点完成。

一般目标的具体剩余关系沿用90.9—90.10：在一个经过纯点 $p$ 的整个二态球内，原确认效应只能有
$f(s)=1-\beta+\beta n_p\cdot s$、$0\le\beta\le1/2$ 的形式；其零点若存在只能是该球的对径。于是还须证明 $D_p$ 与每个这样的球相交，而不能只证明各个已有零集能拼合。本章额外拥有原正元素 $h$、运输后余维一的正补投影 $I_n-p$、以及非正交纯方向加上补态即成为整个原锥内点的核交性质。一般载体中的 $u\in V^*$ 不自动给这样的 $h\in V$、支撑关系或补投影；自动整球也不提供跨面相位乘法。因此94.2是原总问题在一个明确表示域内的条件解，不把表示前提算作一般 $\mathrm B$ 的后果，也不把本域的公理压缩算作全部独立物理假设的最小化。

成熟输入归 Hildebrand 的ROG极射线及最小面工具、93章已使用的行列式归一化和基范数极性，以及普通Hermitian谱理论、矩阵单位乘法和射影几何；Hildebrand §9明示的复推广范围不包含其 Theorem 3.18。相位实线的规范变换和(94.19)的迹积也是成熟工具。数学归属采用 repo-derived，指固定补态检验与完整零拼合的等价、同一最优分解在复域的全效应桥、显式三点边乘法对完整实复块的综合分类，以及这些结果在同一原数据上的组合应用；实域93的已得证明及94.6引用的量子消费者均不重报为新成果。上述归属不主张文献穷尽或全球原创；纸面证明不声称Lean/kernel核验、经验实现或整个量子起源目标完成。

白话说，先把整间屋子的刻度一起调好，让每个纯方向像一束细灯光，补态像铺满其余方向的一层光幕。只需检查：一把认得这束灯的正尺若能把另一束纯灯读成零，是否仍能把那束灯与固定光幕的各半混合读成零。若两束灯实际有重叠，这次混合就会填满全屋，任何认灯而处处非负的尺都不可能再读零。这个小检验因此锁住真正的正交关系；三条坐标边接成三角形时，相位必须相容，边只有一条实方向的整块可以统一调成实色，一条边容许两个独立相位就会把整块带成复色。这里已经把同一复ROG屋子里的检验压短了；一般球形世界为何自带这间矩阵屋子、这层补光幕，以及实际设备、事件和时钟如何按原合同接入，仍各有需要支付的关系。证毕。

## 追加锚（本行以下为增补区）

## 95. 一对内在穷尽比较到整个原球及有限寄存器候选的新入口

### 95.1 原全效应下确界与独立静态输入

**定义 95.1（内在一对入口）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C$，以及在
$C\setminus\{0\}$ 上严格正的线性归一泛函 $u$。使用整个紧基 $K=C\cap\{u=1\}$、全部
$P=\operatorname{ext}K$，而非选定纯态轨道或一个正子模型。记 $W=\ker u$。数学效应域固定为

$$
\mathcal E=[0,u]_{C^*},\qquad
F_r=\{f\in\mathcal E:f(r)=1\},\qquad
T_r(x)=\inf_{f\in F_r}f(x)\quad(r\in P,\ x\in K).
\tag{95.1}
$$

这里的序始终是整个原 $C$ 的对偶锥序。$\mathcal E$ 不先被认作实际菜单。
独立几何输入是一群实际保 $C,u$ 的线性可逆变换 $H$，它作为矩阵群紧且在全部 $P$ 上传递，
以及两个原纯点 $p,q$ 满足

$$
T_p(x)+T_q(x)=1\qquad(\forall x\in K).
\tag{95.2}
$$

有限寄存器应用还要求这个同一实际 $H$ 连通；静态结论本身不需连通。没有预选 $e_r$ 族，
不预付比较互反、全局最小确认、PC、PD、Jordan 结构、整个 $W$ 的球面或指定度量。
下面证明中任选的辅助范数以及 Haar 平均构造的内积都是数学工具，不是额外控制资源。
(95.2) 的第二端遍历原基的所有混态，不能只检查 $p,q$ 或纯点表。

**定理 95.2（内在一对关系使整个原基成为球）。** 在定义95.1下，$p\ne q$，
$d=\dim W\ge1$，每个 $r\in P$ 的 $T_r$ 都是一个线性 proper 效应在 $K$ 上的限制。
记其唯一延伸为 $e_r$。它在整个原锥序中最小，且有唯一的纯补点 $r^\perp$，满足

$$
\begin{gathered}
e_r\le f\quad(f\in F_r),\qquad
\{x\in K:e_r(x)=1\}=\{r\},\qquad e_{r^\perp}=u-e_r,\\
K=\{c+w:w\in W,\ s_0(w,w)\le1\},\qquad
P=\{c+w:s_0(w,w)=1\}.
\end{gathered}
\tag{95.3}
$$

$c$ 是原基的唯一中心，$s_0$ 是 $W$ 上由这个椭球确定的正定内积；同一 $H$ 保持它并
在整个单位球面上传递。用 $tc+w\mapsto(t,x)$、$s_0(w,w)=\|x\|^2$ 校准后，准确地有

$$
\begin{gathered}
u(t,x)=t,\qquad C=\{(t,x):t\ge\|x\|\},\qquad
r_v=(1,v),\quad \|v\|=1,\\
T_{r_v}(1,x)=e_{r_v}(1,x)=\frac{1+v\cdot x}{2},\qquad
r_v^\perp=r_{-v},\qquad
T_r(s)=T_s(r)\quad(r,s\in P).
\end{gathered}
\tag{95.4}
$$

因此 $S$、有限正对偶生成及规范比较配对都是结论。若 $H$ 连通，则 $d\ge2$。

证明。先只用原有限维紧凸几何。$F_r$ 非空，因为包含 $u$。选择一组来自 $K$ 的 $V$ 基，
在这些点的效应值都介于零一，便使 $\mathcal E$ 在 $V^*$ 中有界；它又闭，故紧。
$F_r$ 是其闭子集，所以(95.1)的下确界逐点达到，且 $T_r(r)=1$、$0\le T_r\le1$。
有限维紧凸分解给 $K=\operatorname{conv}P$、$C=\operatorname{cone}P$、$\operatorname{span}P=V$，
均指有限组合；此处未要求 $P$ 闭或其点暴露。

第一步，从一对下确界取得共同效应。对 $x,y\in K$、$0\le a\le1$，每个 $f\in F_r$ 都给

$$
f(ax+(1-a)y)\ge aT_r(x)+(1-a)T_r(y),
$$

取下确界即得 $T_r$ 凹。对 $r=p$ 用此式，再以 $T_p=1-T_q$ 和 $T_q$ 的凹性得到反向不等式，
故 $T_p,T_q$ 均仿射。$\operatorname{aff}K=\{u=1\}$，仿射函数在其仿射包上的唯一延伸与
齐次化给原 $V$ 上线性 $e_p,e_q\in\mathcal E$。它们确认各自端点，且对任意 $f\in F_p$，
$e_p(x)=T_p(x)\le f(x)$ 对所有 $x\in K$ 成立，缩放便给 $e_p\le f$ 于整个 $C$。
对 $q$ 同理；(95.2)及 $K$ 张成 $V$ 给 $e_p+e_q=u$。在 $p$ 处 $T_p(p)=1$，所以
$T_q(p)=0$；若 $p=q$ 则有 $2=1$，矛盾。这也排除了单点基。
反向，若这两个纯点已有全 proper 区间中的最小确认且两效应之和为 $u$，它们逐点实现下确界，
立即给(95.2)。所以这个全域等式实质上恰好打包了这一对的最小确认与互补，不是一个独立公理计数。

第二步，把最小性传遍全部原纯点。对 $h\in H$，$f\mapsto f\circ h^{-1}$ 双射
$\mathcal E$，并把 $F_r$ 双射到 $F_{hr}$，因此直接从下确界有

$$
T_{hr}(x)=T_r(h^{-1}x).
\tag{95.5}
$$

纯态传递使每个 $r=hp$ 都有最小确认 $e_r=e_p\circ h^{-1}$；若用另一 $h$，得到的仍是
同一个内在下确界，故无选取歧义。同时 $hq$ 是纯点，其最小确认为
$e_q\circ h^{-1}=u-e_r$。这里先只得到至少一个纯补点，没有假设选定比较族等变或互反。

第三步，建立唯一饱和。任选 $o\in\operatorname{aff}K$ 和该仿射空间平行方向上的一个欧氏内积。
紧性给最远点 $z\in K$，令 $R=\max_{x\in K}\|x-o\|>0$。对所有 $x\in K$，

$$
\ell(x)=\langle z-o,x-o\rangle\le R\|x-o\|\le R^2=\ell(z).
\tag{95.6}
$$

等号要求 $x-o=z-o$，故 $z$ 是 $\ell$ 的唯一最大点，因而是暴露纯点。
由于 $K$ 非单点且张满其仿射包，$m=\min_K\ell<R^2$。
$f_z=(\ell-m)/(R^2-m)$ 在 $K$ 上的齐次线性延伸属于 $F_z$，且一值面恰为 $\{z\}$。
已有最小性给 $0\le e_z\le f_z\le u$，所以 $e_z(x)=1$ 只能在 $x=z$。
利用(95.5)和传递性，所有 $e_r$ 的一值面都恰为 $\{r\}$。
特别地，若 $u-e_r=e_s=e_t$，在 $s$ 处评价并用 $e_t$ 的唯一饱和可知 $s=t$；纯补点因而唯一。

第四步，排除任何非纯边界点。任取 $y\in\operatorname{rbd}K$。相对支撑超平面定理给
原 $\operatorname{aff}K$ 上非恒定的仿射 $g\ge0$，使 $g(y)=0$。
除以 $\max_K g>0$ 并齐次延伸，得到 $f\in\mathcal E$、$\min_Kf=0$、$\max_Kf=1$。
最大值面有纯点 $r$，故 $f\in F_r$，并有 $0\le e_r\le f$。
在整个零面 $Z=\{x\in K:f(x)=0\}$ 上，$e_r=0$，因此 $e_{r^\perp}=u-e_r=1$。
第三步的唯一饱和使 $Z\subseteq\{r^\perp\}$。$y\in Z$，所以 $y=r^\perp$ 是纯点。
这证明了每个边界点都纯；尤其每个非空支撑零面为单点，而不是预设严格凸性。

第五步，从等半径纯轨道取得整个原球。用归一 Haar 测度取
$c=\int_H hp\,dh\in K$，则 $c$ 被 $H$ 固定。
它在 $\operatorname{ri}K$：否则有非零非恒定支撑高度 $g\ge0$、$g(c)=0$；
连续非负函数 $h\mapsto g(hp)$ 的 Haar 积分为零，Haar 测度在非空开集上为正，
故该函数恒零。$Hp=P$ 和 $K=\operatorname{conv}P$ 迫使 $g$ 在 $K$ 上恒零，矛盾。
在 $W$ 上 Haar 平均任意正定内积得到 $H$ 不变内积 $s$。
$H$ 固定 $c$ 且在纯点上传递，故所有 $r-c$ 的 $s$ 范数同为某个 $\rho>0$。
由有限凸分解，$K-c$ 包含在闭半径 $\rho$ 球中。

对每个 $s$ 单位方向 $v\in W$，$c\in\operatorname{ri}K$、紧性和凸性保证射线
$c+tv$ 与 $K$ 的交恰为 $0\le t\le t_v$，其中 $0<t_v<\infty$，末点在相对边界。
第四步使该末点纯，故 $t_v=\rho$。于是每个方向的整个半径段都在原 $K$ 中，
得到反向包含，原基恰为整个球。置 $s_0=s/\rho^2$ 得(95.3)；球面点恰为极点，
$H$ 遂在整个 $s_0$ 球面上传递。这个 Haar 积分只构造数学中心和度量，未要求实际无限混合。
有界凸体的对称中心唯一，否则两个中心反射合成非零平移；同一个椭球的单位球唯一决定其范数，
极化恒等式再唯一决定 $s_0$，所以结论不依赖辅助内积。

最后，在已推出的整球上计算规范尺。任一 $f(t,x)=\alpha t+b\cdot x$ 为 proper，恰当且仅当
$\|b\|\le\alpha$ 且 $\alpha+\|b\|\le1$。
若它确认 $r_v$，等号
$1=\alpha+b\cdot v\le\alpha+\|b\|\le1$ 迫使
$b=\lambda v$、$\alpha=1-\lambda$、$0\le\lambda\le1/2$。
因此在全部 $\|x\|\le1$ 上取下确界，得到(95.4)，并给纯端点互反及唯一对径补点。
这是[Library 原球计算][L95static]中 *1. Intrinsic control geometry, comparisons and the static PD alternative*
的参数对应，此处没有在取得球之前使用它。
取 $B((t,x),(z,y))=(tz+x\cdot y)/2$、$L_Bv=B(v,-)$，该处的有限 PD 推论直接给

$$
L_Br=e_r,\qquad L_B(C)=C^*,\qquad
B>0,\qquad L_B^{-1}u=2c,\qquad B(2c,2c)=2.
\tag{95.7}
$$

纯点张成 $V$ 给配对唯一性。若 $H$ 连通，它在 $W$ 上的作用属于 $\mathrm{SO}(d)$；
$d=1$ 时连通群不能交换 $S^0$ 的两点，故在此应用中 $d\ge2$。
上述静态证明未使用 connectedness、Jordan 分类或整个球面可控作为前提。证毕。

### 95.2 实际一对、所需控制轨道与整个单元菜单

**定理 95.3（由一个真实种子菜单取得全部单元效应）。** 在定义95.1外，保留原凸实际效应像
$D\subseteq\mathcal E$、$0,u\in D$，以及一个真正共同可用的原二结果菜单 $(a,b)$，满足

$$
a(p)=b(q)=1,\qquad a+b=u.
\tag{95.8}
$$

只要求对一个覆盖全部纯点的集合 $H_*\subseteq H$，每个 $h\in H_*$ 的原效应
$a\circ h^{-1}$ 实际可用且属于 $D$，其中 $\{hp:h\in H_*\}=P$。
则 $a=e_p,b=e_q$，每个 $e_r$ 都在原 $D$ 中，且 $D=\mathcal E$。
这不要求 $D$ 对全部控制的全部前合成封闭。

证明。由95.2的最小性，$a-e_p,b-e_q\in C^*$，其和由(95.8)和(95.2)为零。
两个非负泛函和为零使两者在 $C$ 上均为零，再由生成性得 $a=e_p,b=e_q$。
于是(95.5)把每个所需实际前合成识别成 $e_{hp}$，覆盖条件给全部 $e_r\in D$。
对任一原 proper $f(t,x)=\alpha t+b\cdot x$，令 $s=\|b\|$；$s>0$ 时取 $v=b/s$，
$s=0$ 时任取一个单位 $v$。95.2的球计算给

$$
f=2s\,e_{r_v}+(\alpha-s)u+(1-\alpha-s)0,
\qquad 2s,\alpha-s,1-\alpha-s\ge0,
\qquad 2s+(\alpha-s)+(1-\alpha-s)=1.
\tag{95.9}
$$

这是原种子轨道、$0/u$ 和一次三项有限凸组合，不用菜单闭包、极限或独立有界加法。
原 $D$ 凸便给 $f\in D$。相同球坐标下，正泛函的有限 PD 表达为
$f=(\alpha+s)e_{r_v}+(\alpha-s)e_{r_{-v}}$、$\alpha\ge s$；这是(95.7)所复用推论的
精确有限表示，零泛函可取空和。
这里“局部秩二”指共同完美区分的纯态数至多为二：任何确认 $r$ 并排除另一个纯点的 proper 效应
都支配 $e_r$，而(95.4)使 $e_r$ 只能在唯一对径点取零，故不存在三个纯点的共同完美区分。
原种子菜单又实际区分 $p,q$，所以实际容量也恰为二；未在此处假设 Jordan 秩。证毕。

(95.8) 是实际共同菜单输入；仅有两张数学 proper 效应的和等于 $u$ 不供应这个菜单。
(95.9) 得到的是单个效应的实际可用性，不把任意一列和为 $u$ 的效应变成共同测量，
也不创造分支更新、仪器、记录或保留输出的读出。后面所有联合测量仍有自己的资源合同。

### 95.3 与旧强球面入口的同数据对应

**命题 95.4（规范比较上的入口等价与装饰替换）。** 本命题的新旧入口等价只在同一实际 $H$ 紧且连通的共同域上陈述；
95.2—95.3的静态定理仍允许断开的 $H$。令旧入口准确指
[Library 的二元寄存器附录][L95bit] *1. Intrinsic control geometry, comparisons and the static PD alternative*
中的强球面入口：同一原 $V,C,u,K,P,D,H$ 上，全部选定 $e_r\in D$ proper、自确认、纯互反，
有全域穷尽对，另给一个使同一 $H$ 正交且在整个 $W$ 单位球面上传递的正定度量。
在上述共同连通域内，比较装饰识别为 $e_r:=T_r$，并保留95.3的同一实际种子及所需轨道资源时，
该完整旧静态入口与95.1—95.3相互恢复；连接下面的原寄存器和过程资源后，仍是同一有限寄存器候选。

证明。新入口由95.2取得旧入口的整个球面作用、规范自确认和互反，由95.3取得实际 $e_r\in D$；
(95.2)给同一对的全域穷尽。反向直接应用旧入口的 *Theorem (original ball before the pairing)*
及 *Corollary (finite PD, full original menu and genuine leastness)*：它们识别旧原选定 $e_r$
为整个 proper 区间的最小确认，故 $e_r=T_r$。旧穷尽遂是(95.2)，旧整球面作用蕴含纯态传递。
两边都保留相同的实际 $H$、种子、所需轨道及下游资源，度量仅作可忘却、可恢复的数学见证。
在原 $V,C,u$ 的保单位序同构 $J$ 下，效应按 $f\mapsto f\circ J^{-1}$ 运输，
所以 $T'_{Jr}(Jx)=T_r(x)$；原态、纯点、效应、控制和事件合同按同一映射对应。

若旧数据只是一套任意选定的确认装饰 $\varepsilon=(\varepsilon_r)$，没有证明其最小性，
所用映射必须明写为

$$
\mathsf F(\mathcal O,\varepsilon)=\mathcal O,\qquad
\mathsf R(\mathcal O)=(\mathcal O,(T_r)_{r\in P}),\qquad
\mathsf R\mathsf F(\mathcal O,\varepsilon)=(\mathcal O,T).
\tag{95.10}
$$

这里 $\mathcal O$ 保留原载体、实际效应／菜单、控制及所有过程资源；$\mathsf F$ 只忘掉选定比较。
$\mathsf R$ 只在满足本章或完整旧入口、从而规范效应已证明实际可用的域上定义。
它不删除旧实际测试，也不改变该测试的更新与记录；只是把作为比较尺的指定换成 $T$。
除非 $\varepsilon=T$，这个复合不是原装饰元组的恒等。
完整旧强球面包恰由其已有定理证明 $\varepsilon=T$，所以在那个域内可说同数据恢复；
任意自确认装饰不能据此取得同装饰双向蕴涵，见 Library 的 [*Scope tests*][L95scope]。
证明并未把一个较弱旧条件偷换为上述完整强球面包。证毕。

### 95.4 同一个有限寄存器候选的全部剩余输入

**定义 95.5（原寄存器、耦合与预选择 END）。** 从现在起保留95.1的同一实际紧连通 $H$，
以及95.3的实际效应资源。令 $V_N=V^{\otimes_{\mathbb R}N}$、$u_N=u^{\otimes N}$。
对每个给定有限 $N\ge1$，独立保留原紧凸且全张成的归一基
$K_N\subset\{u_N=1\}$，$K_1=K$、$C_N=\operatorname{cone}K_N$，
忠实局域／乘积层析、实际乘积准备和实际乘积测试，
以及一次固定的单元校准 $F$，所有份数用同一 $F^{\otimes N}$。
在95.4坐标中，纯乘积测试的原概率为

$$
2^{-N}(\widehat a_1\otimes\cdots\otimes\widehat a_N)\cdot\omega,
\qquad \widehat a=(1,a),\quad\|a\|=1,
\tag{95.11}
$$

并在每个实际可逆作用后仍介于零一。$G_N$ 只表示原实际归一线性可逆群，
不假定整个 $G_N$ 闭或连通。独立局域 $H$ 在所有其他坐标上为恒等。
二份原载体上有一条对每个实 $t$ 都实际可用的完整路径
$g(t)=\exp(tX)$，其某个 $g(t_0)$ 越出整个
$\mathrm{SO}(d)\times\mathrm{SO}(d)$，而非仅越出选定 $H\times H$。
对每个有限 $N\ge2$ 给一个连通操作图；同一完整路径在每条边都实际放置为

$$
\iota_{ij}(g(t))=g(t)_{ij}\otimes I_{\rm spectators}\qquad(t\in\mathbb R).
\tag{95.12}
$$

端点顺序与固定校准相容。旁观者恒等覆盖整个原载体及所有相关坐标，不能只固定一个旁观者准备。
不假设任意 $G_2$ 或已经合成的多体作用能被运到别的载体。

三份图包含路径 $1-2-3$。在选择二体控制扇区之前，另有实际仿射、保质量、全域的
$\mathrm{END}:K_3\to K_2$，保留端点 $1,3$，输出就是同一个有序原二份类型。
在固定乘积校准中，它在所有原乘积准备上的值为中腿收缩；乘积张成使其齐次线性延伸唯一。
只有写下单位泛函或形式偏迹不供应这个实际域、范围和输出类型。
这些条件准确是 [Library §2][L95control] *Original composite data* 与 [§3 *Pre-selection END interface*][L95end]，
不从单系统球或全单元效应推导出来。

**定义 95.6（指定原事件与实现资源）。** 对每个指定的原 typed 事件或未归一分支
$e:n\to m$，保留其原记录、ready、控制、合法性和全部未来合同；保持包括零和所有实准备关系的
实线性 Hermitian 输入律。归一仿射行为只有连同齐次质量缩放及这些关系才给该原实线性映射。
在取得矩阵坐标后，记输入维数 $D_n=2^n$、输出维数 $D_m=2^m$，令 $\phi_e$ 为原映射，
$\widetilde\phi_e(A+iB)=\phi_e(A)+i\phi_e(B)$ 为其唯一复线性 HP 延伸。
每个这样的原事件分别供应一个输入维数参考和准确同事件输出

$$
\begin{gathered}
|\omega_n\rangle=D_n^{-1/2}\sum_{j=1}^{D_n}|jj\rangle,
\qquad \Omega_n=|\omega_n\rangle\langle\omega_n|,\\
J_e=(\operatorname{id}_{D_n}\otimes\widetilde\phi_e)(\Omega_n)\ge0
\quad\text{于整个原参考／输出锥 }C_{n+m}.
\end{gathered}
\tag{95.13}
$$

参考态实际可准备。其来源识别可由一个原实线性联合上下文 $L_e$ 给出：对所有正乘积输入
$A\otimes B$，$L_e(A\otimes B)=A\otimes\phi_e(B)$；乘积张成遂强迫整个上下文是同一
$\operatorname{id}\otimes\phi_e$，包括 $\Omega_n$ 上的准确输出。
也可直接供应这个同事件输出等式及其原来源识别，不能事后另挑一张正证书矩阵。
逐原分支各测其整个输出，不能只测总事件、若干读数或产品向量。

独立保留每个确定事件在全部原正输入上的 TP，或各分支的 TNI 预算；
实际完整仪器还保留同一菜单的记录、真实粗粒化
$\phi_{\rm total}=\sum_a\phi_a$ 及总 TP。输入质量、输出质量和零分支不删去，
只在严格正质量时条件化。数学 CP 的全参考正性不增加该原事件的实际可调用参考上下文。

若还要求实际实现所有有限 CPTP 映射和有限仪器，另保留实际纯二元辅助准备、
导出控制的顺序组合，以及进入同一原保留寄存器、按固定校准为偏迹的 typed 全域丢弃。
仪器还要计算基指针读出，其未忽略指针前的保留输出分支律准确是

$$
\tau\longmapsto(I\otimes\langle z|)\tau(I\otimes|z\rangle),
\tag{95.14}
$$

并有实际标签／记录、真实粗粒化和正质量条件化。
指针效应的概率本身不等于这条更新律。以上完整复用
[Library §4][L95event] *Typed event interface* 与 *Actual realization resources*；
纯辅助态、丢弃、指针和记录均是实际资源，不由 Choi 证书生成。

### 95.5 完整条件应用、几何与量子公理对应

**定理 95.7（唯一有限寄存器候选的新静态入口）。** 在95.1、95.3、95.5的全部原输入下，
95.5中的同一个 $d$ 必为三；一次固定 Pauli 校准后，对每个给定有限寄存器有

$$
\begin{gathered}
V_N\simeq\operatorname{Herm}(2^N,\mathbb C),\qquad
K_N=\mathcal D(2^N),\qquad C_N=\operatorname{Herm}_+(2^N,\mathbb C),\\
Q_N=\{\operatorname{Ad}_U:U\in\mathrm{SU}(2^N)\}
\cong\mathrm{PSU}(2^N)\ \subseteq G_N.
\end{gathered}
\tag{95.15}
$$

$Q_N$ 的每个作用由实际原语的有限字精确实现，不把极限操作宣告为实际。
每个已有实际仿射效应按唯一矩阵 $E$ 表示，$0\le E\le I$、概率为 $\operatorname{Tr}(E\rho)$；
原单元有全部这样的效应，全部有限联合 POVM 的实际实现还消费95.6的实现资源。
每个满足95.6同事件参考条件的指定映射／分支为 CP，其原预算分别给 CPTP／CP-TNI；
实际完整菜单的分支和给量子仪器。若同时保留95.6全部实现资源，则这些原寄存器间每个有限
CPTP 映射和每个有限 CP 仪器都有实际的映射及结果标签层面的实现。

证明。先由95.2—95.3取得 Library 二元附录 §1 所需的整个原球、全部原规范比较效应和
同一实际紧连通整球面传递 $H$。不是对 $K_N$ 作新定义：95.5逐项给该附录 §2 的
原紧凸全张成基、忠实乘积层析、实际产品和固定校准，(95.11)给其原概率界，
(95.12)给其全实路径及整个旁观者恒等放置。以下逐段应用该处已经证明的接口，
保留其前件和结论域，不重证群分类、有限控制、END 或仪器构造。

先令 $\Gamma_2$ 为局域 $H$ 和全部 $g(t)$ 的实际有限字子群，
$C_2^{\rm an}=\overline{\Gamma_2}$ 仅为数学矩阵闭包。
Library §2 的 *Analytic compactness lemma* 用原紧凸全张成 $K_2$ 的对称凸包范数，
给紧连通矩阵 Lie 群 $C_2^{\rm an}$，保原 $K_2$、归一和产品概率；此时闭包仍未被宣布实际。
其技术分类直接使用 Masanes–Müller–Pérez-García–Augusiak，
[arXiv:1111.4060v4](https://arxiv.org/abs/1111.4060v4)，PDF 第10页 Theorems 1–2及
§IV A 第16—18页的球面作用表。95.2给 $H$ 的忠实正交整球面作用，连通性给其 $\mathrm{SO}(d)$
范围；固定单位 $a$ 的测试给分类所需

$$
\widehat H\times\widehat H\le C_2^{\rm an},\qquad
\tfrac14(\widehat a\otimes\widehat a)\cdot
C_2^{\rm an}(\widehat a\otimes\widehat a)\subseteq[0,1].
\tag{95.16}
$$

原非局域路径越出整个局域旋转群，排除 Theorem 1 的非 $\mathrm{SO}(3)$ 情形及
Theorem 2 的局域选项。故 $d=3,H=\mathrm{SO}(3)$，且

$$
C_2^{\rm an}=Q_2\quad\text{或}\quad T_1Q_2T_1=:H_2.
\tag{95.17}
$$

固定 Pauli 识别把单元 $(1,a)$ 送到 $(I+a\cdot\sigma)/2$。明确地，取

$$
\begin{gathered}
\sigma_0=I_2,\quad
\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_2=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
\sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\\
\rho(\omega)=2^{-N}\sum_{\mu_1,\ldots,\mu_N=0}^3
\omega_{\mu_1\ldots\mu_N}\,
\sigma_{\mu_1}\otimes\cdots\otimes\sigma_{\mu_N}.
\end{gathered}
$$

这是同一 $F^{\otimes N}$ 后的一次固定识别；在两个集合包含证明之前，每个原态仅被识别为
迹一 Hermitian 矩阵，尚未预付 PSD。
此处 $Q/H$ 指普通和部分转置的控制扇区，不是实／复／四元数三种数域。
在同一 Pauli 坐标中 $T_i$ 只转置第 $i$ 因子、反射其 $y$ 分量；它是解析坐标变换，未被当作物理门。

应用同 §2 的 *Exact-generation lemma*：两种闭包的 Lie 代数均为简单非交换
$\mathfrak{su}(4)$，实际子群含完整非平凡局域连通 Lie 子群。
该引理的共轭张成空间是全 Lie 代数的理想；从实际共轭方向取基，反函数定理给实际有限字中的
开单位邻域，连通性遂使 $\Gamma_2=C_2^{\rm an}$。
因此(95.17)的整群现在才成为实际有限控制。这里复用引理的全部 subgroup、完整实参数、简单性条件，
没有用“稠密即精确”的错误替代；该引理的两环面控制已在 Library §2 给出。
每条给定边可嵌入同一有限字，因为每个原语都满足(95.12)，无需假设任意二体群可搬运。

在选择扇区之前，Library §3 的 *Pair-state lemma before choosing a branch* 已给原整个
$K_2=\mathcal D(4)$ 或 $T_1\mathcal D(4)$。
95.5的 END 正好匹配该处预选择接口，因而可应用 *Theorem (END excludes the reflected branch)*。
其依赖顺序是：若为 $H$，路径上的实际有限 $H_{12},H_{23}$ 字给
$T_2Q_3T_2$，其中有普通 $Q_{13}$，从原乘积态可制备普通端点 Bell 与中腿纯态的乘积。
END 的同一原 $K_2$ 范围会含普通 Bell，而此前已得 $K_2=T_1\mathcal D(4)$；
$T_1(\mathrm{Bell})=\mathrm{SWAP}/2$ 的负特征值 $-1/2$ 排除它，矛盾。
这只核对原定理在本章数据上的消费次序，END 并非由选出 $Q$ 以后的 SWAP 或酉扩张构造倒推。
原三角形接口是 Library §3 的替代充分条件；本章已经选 END，不再把第三条原边列为额外原语。

选择 $Q$ 后，每个原有限连通图应用同 §3 的 *Finite graph generation on one carrier*，
得实际有限字 $Q_N\subseteq G_N$。随后 *All finite original states and controls* 给两个包含，
其使用条件在这里均保持：原纯乘积态的 $Q_N$ 轨道覆盖全部秩一投影，有限谱混合与原凸性给
$\mathcal D(2^N)\subseteq K_N$；原全张成层析已把每个原态表示为迹一 Hermitian 矩阵，
若有负特征值，实际 $Q_N$ 将其特征向量送到原乘积读出方向，(95.11)会读到该负值，故
$K_N\subseteq\mathcal D(2^N)$。这两个包含针对整个原 $K_N$，不是只描述一个被生成的正子模型。
$N=1$ 由 $d=3$ 的整球结论给出，锥按正质量齐次化，取得(95.15)。
没有分类整个 $G_N$ 的离散部分或未供应参考接口的原不可逆事件。

接着对每个指定原事件应用 Library §4 的 *Theorem (rectangular CP and exact budgets)*。
(95.13)的参考维数恰为输入维数，输出锥由(95.15)已是整个原 PSD 锥，
原实线性乘积扩张合同识别的仍是同一个 $\widetilde\phi_e$。
Watrous，[Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，Theorem 2.22、
Theorem 2.26与 Corollary 2.27，分别在印刷页82—83、87—89，给矩形 CP、Kraus和预算的成熟接口。
按本章归一 Choi 和因子次序，其结果准确为

$$
\begin{gathered}
\widetilde\phi_e(X)=\sum_\alpha A_{e\alpha}X A_{e\alpha}^{\dagger},\qquad
A_{e\alpha}:\mathbb C^{D_n}\to\mathbb C^{D_m},\qquad
E_e=\sum_\alpha A_{e\alpha}^{\dagger}A_{e\alpha},\\
\operatorname{Tr}\phi_e(X)=\operatorname{Tr}(E_eX),\qquad
\operatorname{Tr}_{\rm out}J_e=E_e^{\mathsf T}/D_n,\\
\mathrm{TP}\Longleftrightarrow E_e=I_{D_n},\qquad
\mathrm{TNI}\Longleftrightarrow0\le E_e\le I_{D_n}.
\end{gathered}
\tag{95.18}
$$

每个非零分支应用该接口；零映射直接 CP。原完整菜单的真和与总 TP 给
$\sum_a E_a=I$ 及总 CP，不再需要总 Choi 探针。
同一已有联合上下文的参考预算为 $I_R\otimes E_a$；这是原预算的数学后果，
不制造其它参考上下文。$p_a=\operatorname{Tr}\phi_a(\rho)>0$ 时条件态为
$\phi_a(\rho)/p_a$，$p_a=0$ 时正输出为零且原零记录／权限保留。

最后，若支付95.6的实现资源，直接应用同 §4 的 *Theorem (all finite register channels and instruments)*。
为明确矩形尺寸与实际空间的对应，对通道 Kraus 数 $r$ 选有限 $k$ 满足
$2^k\ge r$、$m+k\ge n$，置 $q=m+k-n\ge0$；对有限仪器使用
$R=\sum_a\max(1,r_a)$ 并取 $2^k\ge R$，其余条件相同。
这是同一原定理的参数替换：等距映射占据 $m+k=n+q$ 个二元单元，
补齐 $q$ 个实际纯辅助单元后，原实际 $Q_{m+k}$ 实现其酉延伸，最后按 typed 合同丢弃或读取 $k$ 个指针单元。
每个命名零分支占一个零 Kraus 编码，所有未用编码亦补零；(95.14)和真实归组准确还原各原指定 CP 分支。
先加未归一输出，后在正质量处条件化，空辅助串／环境串采用原定理的恒等约定。
若输入或输出指数为零，标量质量载体遵循 Library 的 $d=1$、$b=1$ 分支，
不要求新物理类型；非平凡标量结果仍可用有限二元指针实现。
这里原二维幂尺寸的补齐条件不能删成仅有 Kraus 秩下界。

任意原仿射 proper 效应在完整 Hermitian 载体上由唯一 $0\le E\le I$ 表示，给所述 Born 公式；
有限 POVM 可在同一实现定理中取 $A_a=\sqrt{E_a}$，于是全部有限联合 POVM 连同一种 Lüders 实现可用。
这是可实现的选择，不是对原既有事件更新的唯一性结论，也不增设锐中性前提。
一个构造的酉扩张与原事件有相同矩阵映射，并不把其原上下文、历史或合法未来识别为同一。
完整应用因而保留了原资源，且每一步只消费已取得的上游结论。证毕。

**命题 95.8（几何、标准公理与候选范围）。** 95.7给的是 Library 同一有限同种二元寄存器候选的
一个新静态入口，与89.14的一般 EJA 原装饰元组不构成无附加接口的等价。
其量子公理对应与准确条件如下。

| 标准有限量子结构 | 本章中的独立输入、推得结构与保留边界 |
| --- | --- |
| 复 Hilbert 寄存器、态和混合 | 95.1的一对内在全域关系加原纯态传递先给整个 Lorentz 球；95.5的实际产品、忠实层析、全实非局域路径和同载体放置，再加预选择同类型 END，选出 $d=3$ 及每个 $\mathbb C^{2^N}$ 的整个密度基。 |
| 张量复合与纠缠 | 原 $V^{\otimes N}$、固定乘积校准、实际产品准备／测试是输入；有限图控制和两个原集合包含给完整复 PSD 张量锥，纯几何为 $\mathbb{CP}^{2^N-1}$，$N>1$ 的整体不再是 Bloch 球。 |
| 效应、Born 与测量 | 95.3以实际种子轨道和有限三项混合给全单元效应；Born 是已识别矩阵效应的迹配对。全部有限共同 POVM 要95.6的完整实现资源，单个效应不供应共同菜单。纯比较为 $|\langle\psi,\varphi\rangle|^2$，其端点互换不依赖顺序。 |
| 可逆控制 | 数学闭包仅用于技术分类；简单 Lie 代数中的共轭理想／反函数定理接口给精确实际有限字 $Q_N\subseteq G_N$。整个原 $G_N$、所有不连续操作和其余事件未被这个包含分类。 |
| 通道、分支及仪器 | 指定原事件的实线性、准确同事件产品扩张、一次输入维数纠缠参考的整个输出正性，以及原 TP／TNI／总和预算，给矩形 CP 与有限 Kraus。全部仪器的实际构造另消费辅助态、顺序、typed 丢弃、保留输出指针律、标签和真粗粒化。 |
| 更新和时间 | 同一 POVM 不决定既有更新；Lüders 是资源下的一种实现。完整实参数控制不是物理钟；若另给物理时间上的连续齐次可逆动力学及时间／能量单位，才可读作 Hamiltonian 演化，并保留加标量自由度。 |

证明与范围。静态95.2允许断开的实际群：经典二点单纯形的两个坐标效应实现(95.2)，
交换两点的群紧且纯传递，故得到 $d=1$ 的整区间；它不满足95.5保留的连通局域控制。
因此静态结论没有把 classical bit 排除，而完整应用从连通性和耦合分类得到复 qubit。
对该有限寄存器复候选，最小投影确认、实际局域旋转及任意一对正交纯点满足新入口；
所需实际种子、轨道与所有下游资源须在同一实现中保留，不能仅凭矩阵形式宣称已经拥有它们。

89.14仍保留89.7的原 $A,D,E$、完整一般 EJA 桥、同一 $L,p,\omega$（同一 $p$ 使用两次）、
两实张成、全实 $Z$、完整(83.8)、原两尺度及 H13 的同资格态整个输出。
那一路线允许有限复 Hermitian 直和、经典和不等块，并只对原指定两／三份来源付出接口。
95.7则从局部秩二整球出发，支付同种单元、每个有限 $N$ 的原乘积层析和精确控制放置、
非局域实参数路径及同类型 END；没有用 FH1／一般 EJA 入口或尺度／H13 选择方向。
89.14不供应这些全 $N$ 的控制和秩二接口，95.7也不替任意89.14元组制造这些接口或分类所有 EJA。
这说明资源路线的区别，不是第二个竞争的完整有限寄存器候选，也不是把所有原装饰类合成一个等价类。

对任意 $d\ge1$ 的 Lorentz 球，(95.4)给(95.2)，静态结论并不选三维；
少了原复合、层析、非局域控制和 END，表中下游结论不能由该等式单独取得。
(95.2)仍是全域下确界条件，不是两个读数的有限实验认证，也没有取得最少独立物理公理数。
有限字存在不提供算法、长度界、参数精度或效率；每个有限图分别成立不供应无限系统的兼容极限。
非二维幂的其他物理类型须实际编码／解码与通用性桥；时钟、能量、$\hbar$、Hamiltonian 来源、
时空和经验对应都超出这里的静态及有限资源结论。

把整个原状态物体放在桌上，一盏纯灯的比较是“所有必定确认它的合法尺，在目标态上能低到哪里”。
这个下确界原本可能每次换尺。若恰有两盏纯灯的最低读数对每个原混态都正好补成一，
两个凹下包络就只能都是直尺；原纯态传递把这对直尺带到每盏灯旁，却还没有预付一个圆球。
最远点先给一把只在一个纯点到顶的尺，最小性和控制把这种唯一到顶传播给所有灯。
任一外壳支撑面若还藏着多个点，其上某把最小尺全为零，补尺便同时在多个点到顶，矛盾。
所以外壳每点都纯。围绕不动平均中心，所有纯灯半径相同；每条射线的外壳末点因而都在同一半径，
整个原物体才成为实心球。真正共同的种子菜单将原按钮识别成规范尺，所需控制轨道加三项有限混合
覆盖全部单元效应；这个过程没有组装所有联合仪器。

接成寄存器以后，产品读数和非局域作用负责选球的维数；三点路径上实际丢掉中腿而回到原二份类型，
负责检验两体方向能否一致。精确有限控制随后在每个原有限图上传开，两个包含才把全部原态认作量子态。
最后仍逐事件保留原记录、预算和一个准确纠缠参考上的整个输出，才能用 Choi 接口取得 CP；
实际造仪器还要辅助空间、丢弃和保留输出的指针。交换比较的两个端点只交换一个数的参数，
没有断言两次物理仪器交换执行次序后有相同后态。

本章新增承重组合的归属为 `repo-derived`：从原内在一对全域关系，经最小确认、暴露点与支撑零面、
纯传递的等半径轨道到整个原球，以及实际种子轨道的同数据应用。有限维凸分解、仿射延伸、
支撑超平面、Haar 平均、欧氏等号条件和极化恒等式均是成熟中间工具。
群分类的主文献和矩形 Choi 的主文献已附在各消费步骤；精确有限字、END、全原寄存器两个包含及
仪器实现的证明仍由所引 Library §§2—4 持有，未取得本章新证明或新分类名义。
以上是明示模型输入下的普通数学定理、证明和条件应用；有限来源阅读不支持全球原创、历史优先权、
物理起源或 Lean／kernel 核验主张。证毕。

[L95bit]: ../../../Library/QuantumStates/mullerududec2012selfduality.md#appendix-an-exhaustive-binary-comparison-and-a-single-coupling-path
[L95static]: ../../../Library/QuantumStates/mullerududec2012selfduality.md#1-intrinsic-control-geometry-comparisons-and-the-static-pd-alternative
[L95control]: ../../../Library/QuantumStates/mullerududec2012selfduality.md#2-analytic-closure-published-classification-and-exact-actual-words
[L95end]: ../../../Library/QuantumStates/mullerududec2012selfduality.md#3-endpoint-discard-the-triangle-alternative-and-every-original-register
[L95event]: ../../../Library/QuantumStates/mullerududec2012selfduality.md#4-one-exact-reference-per-original-event-and-finite-realizations
[L95scope]: ../../../Library/QuantumStates/mullerududec2012selfduality.md#scope-tests

## 追加锚（本行以下为增补区）

## 96. 低余维ROG的纯纯零拼合、原效应提升与完整混态桥

### 96.1 同一原载体、归一化与有限纯零条件

**定义 96.1（实复ROG域与 $\mathrm G_k$）。** 取 $\mathbb F=\mathbb R$ 或 $\mathbb C$，分别记
$\mathcal H_n(\mathbb R)=\operatorname{Sym}_n(\mathbb R)$、
$\mathcal H_n(\mathbb C)=\operatorname{Herm}_n(\mathbb C)$，均作为实内积空间，配对为
$\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(XY)$。实域的星号表示转置。
原非零有限维 $(V,C,u)$、整个基 $K$、全部纯点 $P$ 和整个 $[0,u]_{C^*}$ 保持89.1、93.1、94.1的含义。
要求整个原锥有相应域的ROG表示：它是一个线性PSD截面，每个锥元都是其中相应域秩一PSD矩阵的有限和；
原 $u$ 可以是任意严格正归一泛函。

只使用93.2或94.2的共同支撑限制和行列式最大点归一化。记其保原单位的整锥同构为 $\Psi$，
共同支撑在 $\mathbb F$ 上的维数为 $n\ge1$，原 $h=\Psi^{-1}(I_n)$。运输后省略撇号，得到

$$
\begin{gathered}
L=\Psi(V)\subseteq\mathcal H_n(\mathbb F),\qquad
C=L\cap\mathcal H_{n,+}(\mathbb F),\qquad I_n\in L,\qquad u=\operatorname{tr}|_L,\\
K=\{X\in C:\operatorname{tr}X=1\},\qquad
P=\{vv^*\in L:\|v\|=1\},\qquad
c=\dim_{\mathbb R}L^\perp.
\tag{96.1}
\end{gathered}
$$

因此环境实维数分别为 $n(n+1)/2$ 和 $n^2$，$c$ 始终相对于各自环境计算。
合同归一化保持秩和环境实余维，$\Psi$ 的对偶运输双射全部原效应、确认集及排除关系；
以下每个结论均沿这一双射返回原 $u$。没有在任意 $u$ 下另取一个未经归一化的保迹同构。
特别地，复秩一不被实化为实秩一。

沿用 $F_p=\{f\in[0,u]:f(p)=1\}$、$T_p(x)=\min_{f\in F_p}f(x)$ 及
$p\perp x\Longleftrightarrow T_p(x)=0$。对每个整数 $k\ge1$，定义

$$
\mathrm G_k:\quad
\forall p,q_1,\ldots,q_k\in P,\qquad
\bigl[\forall j,\ p\perp q_j\bigr] \Longrightarrow\
p\perp\frac1k\sum_{j=1}^kq_j.
\tag{96.2}
$$

纯点允许重复，前件的各个零可以由不同原效应实现，后件要求一把共同原效应。
$\mathrm G_1$ 恒真，$\mathrm G_2$ 正是(94.24)的三纯点关系。
非负性使排除这个平均等价于同时排除每个 $q_j$，也等价于排除它们任何全部权重严格正的有限凸组合。
重复量词保证 $\mathrm G_k$ 包含每个至多 $k$ 元非空纯零集合的共同排除条件，
并有 $\mathrm G_{k+1}\Rightarrow\mathrm G_k$。
完整 $\mathrm{Z0}$ 仍量化所有 $p\in P$ 和所有原混态 $x,y\in K$，如(93.3)。
$n>1$ 时，$\mathrm{FC}$ 取同一 $h$ 给出的原固定补态 $(h-p)/(n-1)$，如(94.3)—(94.4)；
$n=1$ 时 $\mathrm{FC}$ 为真，不定义这个商。

### 96.2 全部原效应的精确提升与同一个补框架

**引理 96.2（共同正提升）。** 在(96.1)的任意实余维 $c$ 下，令

$$
\mathcal M=(I_n+L^\perp)\cap\mathcal H_{n,+}(\mathbb F),\qquad
\mathcal M_{pq}=\{M\in\mathcal M:v^*Mw=0\},
\quad p=vv^*,\ q=ww^*\in P.
\tag{96.3}
$$

$\mathcal M$ 非空紧凸，仿射维数为 $c$，且 $\operatorname{tr}M=n$。
对任意有限列 $q_j=w_jw_j^*\in P$，有精确等价

$$
\begin{aligned}
&\exists f\in[0,u]:\ f(p)=1,\ f(q_j)=0\quad(\forall j)\\
&\qquad\Longleftrightarrow\quad
\exists M\in\mathcal M:\ v^*Mw_j=0\quad(\forall j).
\end{aligned}
\tag{96.4}
$$

每个 $p$ 还能扩为同一原锥中的完整正交秩一框架

$$
I_n=p+r_2+\cdots+r_n,\qquad
r_j=z_jz_j^*\in P,\qquad
(v,z_2,\ldots,z_n)\text{ 是 }\mathbb F^n\text{ 的正交单位基}.
\tag{96.5}
$$

证明。先证明任意原正泛函均有环境PSD提升，而不假定它有环境正收缩代表。
设 $\pi_L$ 为迹内积正交投影。锥 $\pi_L(\mathcal H_{n,+})$ 闭：若 $\pi_L(E_i)$ 收敛且 $E_i\succeq0$，
因 $I_n\in L$，$\operatorname{tr}E_i=\langle I_n,\pi_L(E_i)\rangle$ 有界，PSD矩阵的范数遂有界，
取收敛子列即得PSD极限及所需投影。这个闭凸锥在 $L$ 中的对偶恰为
$L\cap\mathcal H_{n,+}=C$；有限维双极性定理给 $C^*=\pi_L(\mathcal H_{n,+})$，其中以迹配对识别 $L^*$。
所以给定原 proper $f$，可分别提升 $f$ 和 $u-f$ 为 $E,F\succeq0$，满足

$$
f(X)=\operatorname{tr}(EX),\quad
(u-f)(X)=\operatorname{tr}(FX)\quad(X\in L),\qquad
M=E+F\in\mathcal M.
\tag{96.6}
$$

若 $f(p)=1$，则 $v^*Fv=0$，故 $Fv=0$；若 $f(q_j)=0$，则 $Ew_j=0$。
于是 $v^*Mw_j=0$，得到(96.4)正向。
反向，对满足右侧的 $M$，由 $p\in L$ 得 $v^*Mv=1$。取

$$
E=Mvv^*M,\qquad
M-E=M^{1/2}\bigl(I_n-M^{1/2}vv^*M^{1/2}\bigr)M^{1/2}\succeq0.
\tag{96.7}
$$

括号为单位向量 $M^{1/2}v$ 的正交补投影，故即使 $M$ 奇异也成立。
在 $L$ 上限制 $E$，其补由 $M-E$ 提升，得到整个原区间内的 $f_E$，并有
$f_E(p)=1$、$f_E(q_j)=|v^*Mw_j|^2=0$。这里的序界是 $0\preceq E\preceq M$，
并未擅自换成 $E\preceq I_n$。

因 $I_n\in L$，每个 $N\in L^\perp$ 迹为零，故 $M\in\mathcal M$ 的迹为 $n$。
闭性、PSD和固定迹给紧性；$I_n$ 的小邻域在 $I_n+L^\perp$ 内正定，给仿射维数 $c$。
对(96.5)，$I_n-p$ 是原锥内的正交投影。其ROG分解的每个向量均在该投影像中；
任选非零项并归一为 $r_2$，则 $I_n-p-r_2$ 仍是 $L$ 中的正交投影。
重复，每次剩余秩减一，得到整个框架。$n=1$ 时框架只有 $p=I_1$。
此递推不要求Jordan闭合。证毕。

**引理 96.3（纯正交与完整混态桥）。** 在(96.1)的任意 $c$ 下，以下条件等价：
完整 $\mathrm{Z0}$；$\mathrm{FC}$；每个原可排除纯对满足

$$
p=vv^*\perp q=ww^*\quad\Longrightarrow\quad v^*w=0;
\tag{96.8}
$$

以及对每个 $p\in P$，全部非空 $\mathcal M_{pq}$ 的任意有限子族有共同点。
这些条件一旦成立，全部原混态的零集准确是

$$
D_p=\{x\in K:p\perp x\}=\{x\in K:\operatorname{tr}(px)=0\}.
\tag{96.9}
$$

证明。$n=1$ 时 $P=K=\{I_1\}$、$F_p=\{u\}$、$D_p=\varnothing$，各条件成立。
设 $n>1$。$a_p=(I_n-p)/(n-1)$ 是原态，投影限制效应
$h_p(X)=\operatorname{tr}(pX)$ 在整个原锥 proper，确认 $p$ 且排除 $a_p$。
故 $\mathrm{Z0}\Rightarrow\mathrm{FC}$。
若 $p\perp q$ 而 $v^*w\ne0$，则 $\ker a_p=\mathbb Fv$ 与 $\ker q$ 的交为零，
所以 $(q+a_p)/2\succ0$，是原 $C$ 的相对内点。
一个原正泛函若在这里为零，沿每个 $Y\in L$ 作小的双向扰动，就在全部 $L$ 为零，不能确认 $p$。
因此 $\mathrm{FC}$ 蕴含(96.8)。

反之，设(96.8)。若 $p\perp x$，取一把实现此零的原 $f\in F_p$，并作同一原锥的有限ROG分解
$x=\sum_j\lambda_jq_j$，其中 $\lambda_j>0$、$\sum_j\lambda_j=1$、$q_j\in P$。
$0=f(x)=\sum_j\lambda_jf(q_j)$ 及各项非负给 $f(q_j)=0$，所以每个 $q_j$ 与 $p$ 矩阵正交。
于是 $\operatorname{tr}(px)=0$。反向由同一个 $h_p$ 见证，得到(96.9)，其右侧凸，故有完整 $\mathrm{Z0}$。
这一步使用一把原效应的全部纯分解项，不是把 $\mathrm G_2$ 迭代到混态。

(96.8)还使 $I_n$ 同时属于所有非空 $\mathcal M_{pq}$。
反之，若这些集合的任意有限子族相交，对一个可排除 $q$ 和(96.5)的全部补框架点取共同 $M$。
每个 $r_j$ 本就由 $h_p$ 排除，故这些集合均非空。
$v^*Mz_j=0$ 及 $v^*Mv=1$、Hermitian性给 $Mv=v$，再由 $v^*Mw=0$ 得 $v^*w=0$。
这证明有限零集合条件与(96.8)等价；紧性还给所有非空集合的共同点。
完整 $S$、正负谱部分闭合、Jordan闭合及完整块的等价，实域直接复用93.2，复域直接复用94.2；
本引理只明确其中从纯点到所有原混态的共同实现。证毕。

### 96.3 普通Helly界与只影响一列的自由度

**命题 96.4（有限界及一维列钉住）。** 对任意(96.1)，有

$$
\mathrm G_{\min(n,c+1)}\quad\Longleftrightarrow\quad\text{完整 }\mathrm{Z0}.
\tag{96.10}
$$

固定 $p=vv^*$，记

$$
d_p=\dim_{\mathbb R}\{Nv:N\in L^\perp\}.
\tag{96.11}
$$

若全 $\mathrm G_2$ 成立且 $d_p\le1$，则每个 $p\perp q$ 都满足(96.8)。
特别地，两域的 $c\le1$ 已有 $\mathrm G_2\Rightarrow\mathrm{Z0}$。

证明。由(96.4)，$\mathrm G_k$ 恰要求任意至多 $k$ 个非空 $\mathcal M_{pq}$ 相交。
它们是 $c$ 维仿射空间中的紧凸集。若 $c+1\le n$，普通有限维Helly定理给每个有限子族相交，
96.3给完整 $\mathrm{Z0}$。若 $n<c+1$，对任意可排除 $q$，只取它和(96.5)的 $n-1$ 个补框架点；
$\mathrm G_n$ 直接给共同提升，同样推出(96.8)。反向由96.3的共同 $I_n$ 得全部 $\mathrm G_k$。
维数零的Helly结论就是 $\mathcal M=\{I_n\}$；$n=1$ 按96.3的空零族处理。

若 $d_p=0$，每个 $M\in\mathcal M$ 都有 $Mv=v$，(96.4)立即给结论。
若 $d_p=1$，写所有这些列为 $Mv=v+\tau a$，其中固定 $0\ne a\in v^\perp$、$\tau\in\mathbb R$。
在同一补框架中必有一个 $z_j$ 满足 $a^*z_j\ne0$，故
$M\in\mathcal M_{pr_j}$ 强迫 $\tau=0$。对任意可排除纯 $q$，将 $\mathrm G_2$ 用于 $q,r_j$，
得到共同提升并锁定 $Mv=v$，从而 $v^*w=0$。
这里仅钉住这一列，不要求整个 $M$ 唯一。
当 $c=2,n\ge3$ 时，普通Helly只给 $\mathrm G_3$ 的充分性；
它不把两两相交升级为总相交，也不说明任意抽象凸交反例能由同一原ROG模型实现。证毕。

### 96.4 复余维二的单纯零条件钉住引理

**引理 96.5（一个原纯零条件唯一决定提升）。** 设 $\mathbb F=\mathbb C$、
$L^\perp=\operatorname{span}_{\mathbb R}\{A,B\}$，其中 $A,B$ 独立且迹为零。
固定 $p=vv^*\in P$，若 $a=Av$、$b=Bv$ 实线性独立，则存在原纯 $q=ww^*\in P$，
满足 $p\perp q$，且 $\mathcal M_{pq}$ 恰为单点。
可以要求实线性映射 $(s,t)\mapsto v^*(sA+tB)w$ 的秩为二；
因此单点性来自一个复零方程的两个独立实分量，不依赖PSD边界的切触。

证明。先给所需的复PSD事实。由至多两个实线性齐次等式截出的任意复PSD锥均为复ROG。
若其极射线生成元 $X$ 的秩为 $r\ge2$，在 $\operatorname{ran}X$ 上的Hermitian空间实维数为 $r^2$；
至多两个约束留下维数至少 $r^2-2\ge2$ 的可行线性空间。
除 $X$ 外可取独立可行 $Y$，并将它延伸为支撑外零。$X$ 在其支撑上正定，故
$X\pm\varepsilon Y$ 对充分小 $\varepsilon>0$ 均可行，违反极射线性。
迹一基紧，有限维极点分解遂将每个可行PSD矩阵分解为有限个可行复秩一项。
这也适用于约束相关或锥为零的情况。
这是 Hildebrand [§9][H96] 所述低余维事实的秩维数证明，不是实域余维二自动ROG的断言。

另记一个直接推论。若两个Hermitian约束 $C_1,C_2$ 的公共PSD零锥含正定矩阵 $R$，
而Hermitian矩阵 $J$ 在每个公共零向量 $x$ 上满足 $x^*Jx=0$，则

$$
J\in\operatorname{span}_{\mathbb R}\{C_1,C_2\}.
\tag{96.12}
$$

确实，复ROG先使 $J$ 正交于整个公共PSD零锥；对任意满足两个线性约束的Hermitian $Y$，
$R\pm\varepsilon Y$ 仍在该锥，故 $J$ 正交于整个公共线性核。
取正交补即得(96.12)，不要求两个约束独立。

现令 $W=v^\perp$，$A_0,B_0$ 为在 $W$ 上的压缩，将

$$
H=\frac{ab^*-ba^*}{2i}\in\operatorname{Herm}(W)
\tag{96.13}
$$

在 $\mathbb Cv$ 上延伸为零。因 $p\in L$，$v^*Av=v^*Bv=0$，故 $a,b\in W$，
且 $\operatorname{tr}A_0=\operatorname{tr}B_0=0$。
对任意向量 $w$，

$$
w^*Hw=\operatorname{Im}\bigl(\overline{a^*w}\,b^*w\bigr).
\tag{96.14}
$$

它非零恰表示上述实线性映射的秩为二。
若 $w\ne0$ 满足 $w^*Aw=w^*Bw=0$，且对某个 $M\in\mathcal M$ 有 $v^*Mw=0$ 和 $w^*Hw\ne0$，
则归一化 $w$ 得原纯 $q$；(96.4)给 $p\perp q$，而秩二使零方程唯一确定实参数 $s,t$，
故 $\mathcal M_{pq}$ 单点。以下反设不存在这样的 $(w,M)$。

先取 $M=I_n$。于是 $H$ 在 $W$ 内两个压缩二次型的公共零集上消失。
$I_W$ 正定且满足这两个迹零约束，(96.12)给

$$
H\in\operatorname{span}_{\mathbb R}\{A_0,B_0\},\qquad \operatorname{tr}H=0.
\tag{96.15}
$$

实独立的 $a,b$ 保证 $H\ne0$：若 $ab^*=ba^*$，则 $b$ 为 $a$ 的实倍数。
它们还必须复线性独立；否则 $b=\lambda a$，实独立使 $\operatorname{Im}\lambda\ne0$，
而 $H=-\operatorname{Im}\lambda\,aa^*$ 是非零定号秩一矩阵，与迹零矛盾。
因此 $\dim_{\mathbb C}W\ge2$；若 $W$ 维数为零或一，反设已在此被排除。
复独立还保证下列每组三个Hermitian矩阵实线性独立：

$$
aa^*,\ S:=ab^*+ba^*,\ H;
\qquad bb^*,\ S,\ H.
\tag{96.16}
$$

例如满列秩映射 $U=(a\ b)$ 使 $D\mapsto UDU^*$ 在 $\operatorname{Herm}_2$ 上单射，
两组分别对应一个对角矩阵单位与两个独立的非对角Hermitian矩阵单位。

对充分小的实 $s,t$，取同一个原提升空间中的

$$
\begin{gathered}
M=I_n+sA+tB\succ0,\qquad h=sa+tb,\qquad Mv=v+h,\\
T_h:W\longrightarrow(Mv)^\perp,\qquad T_hx=x-vh^*x.
\end{gathered}
\tag{96.17}
$$

$T_h$ 是线性双射：其 $W$ 分量是 $x$，且 $(v+h)^*T_hx=0$。
原纯点约束在这个超平面上准确成为

$$
A_h=T_h^*AT_h=A_0-ah^*-ha^*,\qquad
B_h=T_h^*BT_h=B_0-bh^*-hb^*.
\tag{96.18}
$$

因为 $Hv=0$，检测式保持为 $T_h^*HT_h=H$。
所以反设使 $H$ 在 $A_h,B_h$ 的全部公共零向量上消失；这些向量经 $T_h$ 返回同一个原模型，
并对(96.17)的这个 $M$ 满足 $v^*Mw=0$。只要压缩零锥含正定矩阵，(96.12)便给

$$
H\in\operatorname{span}_{\mathbb R}\{A_h,B_h\}.
\tag{96.19}
$$

所需严格可行性可以连续、精确地修正。若连续约束 $C_1(\epsilon),C_2(\epsilon)$
在零处独立且迹零，令

$$
G_{ij}(\epsilon)=\operatorname{tr}(C_i(\epsilon)C_j(\epsilon)),\quad
\alpha(\epsilon)=G(\epsilon)^{-1}
\begin{pmatrix}\operatorname{tr}C_1(\epsilon)\\\operatorname{tr}C_2(\epsilon)\end{pmatrix},\quad
R(\epsilon)=I_W-\sum_i\alpha_i(\epsilon)C_i(\epsilon).
\tag{96.20}
$$

小参数下Gram矩阵仍可逆，$\alpha(\epsilon)\to0$，$R(\epsilon)\to I_W$，故 $R(\epsilon)\succ0$，
且 $\operatorname{tr}(C_i(\epsilon)R(\epsilon))=0$。
这只构造压缩约束的数学可行点，不变更原 $L$ 或原效应域。

最后穷尽 $\dim_{\mathbb R}\operatorname{span}\{A_0,B_0\}$ 的三个分支。
法向作可逆实换基 $(A',B')=(r_{11}A+r_{12}B,r_{21}A+r_{22}B)$ 时，
对应的 $a',b'$ 仍复独立，且

$$
H'=(\det R)H.
\tag{96.21}
$$

因此换基保持原 $L,\mathcal M,P$ 及秩二判据；下面的 $H$ 始终按新法向重算，比例常数同时吸收这个非零行列式。

压缩维数为二时，由(96.15)可取法向基使 $A_0=\kappa H$、$B_0=D$，
其中 $\kappa\ne0$、$D,H$ 独立。取 $t=0$、$h=sa$，则

$$
A_h=\kappa H-2saa^*,\qquad B_h=D-sS.
\tag{96.22}
$$

零处两个约束独立且迹零，(96.20)保证所有充分小 $s$ 的严格可行性。
故对每个充分小的 $s\ne0$，(96.19)给实数 $\alpha_s,\beta_s$ 使
$H=\alpha_s(\kappa H-2saa^*)+\beta_s(D-sS)$。
必有 $\beta_s\ne0$：否则 $H$ 与 $aa^*$ 的独立性及 $s\ne0$ 先迫 $\alpha_s=0$，再迫 $H=0$。
在 $\operatorname{Herm}(W)/\mathbb RH$ 中取像，因而有

$$
\overline D-s\overline S\in\mathbb R\,\overline{aa^*}.
\tag{96.23}
$$

取两个不同的充分小非零 $s$ 并相减，得 $\overline S\in\mathbb R\,\overline{aa^*}$，
这与(96.16)矛盾。

压缩维数为一时，可取 $A_0=0$、$B_0=\kappa H$，$\kappa\ne0$。
$\operatorname{tr}H=0$ 说明 $a^*b$ 为实数。
再将法向 $B$ 换为 $B-rA$，其中 $r=(a^*b)/\|a\|^2\in\mathbb R$，亦即将 $b$ 换为 $b-ra$。
这一行列式为一的换基保持 $A_0=0$、$B_0=\kappa H$、$H$，并使 $a^*b=0$。
取 $s=0$、$h=tb$，$t\ne0$，则

$$
A_h=-tS,\qquad B_h=\kappa H-2tbb^*.
\tag{96.24}
$$

两个零约束等价于 $S$ 与 $\kappa H-2tbb^*$ 的零约束。
这两个矩阵在 $t=0$ 独立且迹零，因为 $\operatorname{tr}S=2\operatorname{Re}(a^*b)=0$。
故(96.20)在充分小非零 $t$ 给严格可行性，(96.19)迫
$H=\alpha S+\beta(\kappa H-2tbb^*)$。
由(96.16)，比较 $bb^*$ 系数先得 $\beta=0$，再得 $H\in\mathbb RS$，矛盾。
压缩维数为零时，(96.15)直接给 $H=0$，亦矛盾。

反设在所有分支均不成立，故存在所需 $w,M$；将 $w$ 归一化不改变原二次零约束或秩二性，
引理开头的提升论证遂给所述单点 $\mathcal M_{pq}$。
退化的实相关列由96.4另行处理，压缩相关性、复相关性和小支撑边界均已包含在上述分支中。证毕。

### 96.5 全纯纯条件将唯一提升与整排补方向相容

**定理 96.6（复低余维的完整混态零拼合）。** 在(96.1)的复域中，若 $c\le2$，则
$\mathrm G_2\Rightarrow\mathrm{Z0}$。

证明。固定任意原 $p=vv^*$。若 $d_p\le1$，96.4已给所有可排除纯点与 $v$ 正交。
否则只能是 $c=d_p=2$，取96.5给出的原纯 $q_0$ 及唯一提升
$\mathcal M_{pq_0}=\{M_0\}$。对(96.5)的每个补框架点 $r_j$，均有 $p\perp r_j$。
把全 $\mathrm G_2$ 分别用于 $(p,q_0,r_j)$，由(96.4)得
$\mathcal M_{pq_0}\cap\mathcal M_{pr_j}\ne\varnothing$，单点性迫使

$$
M_0\in\mathcal M_{pr_j}\quad(2\le j\le n),\qquad
v^*M_0v=1,\qquad M_0v=v.
\tag{96.25}
$$

现在任取 $p\perp q=ww^*$。再次把 $\mathrm G_2$ 用于 $q_0,q$，得到同一个 $M_0\in\mathcal M_{pq}$，
所以 $0=v^*M_0w=v^*w$。这对每个 $p$ 成立，96.3遂给全部原混态的(96.9)和完整 $\mathrm{Z0}$。
整个论证只在纯三元组上用 $\mathrm G_2$，没有把补态放入其前件，也没有假定任意二维凸集族具有二元Helly性。证毕。

### 96.6 实余维二分类的保迹应用与原三纯点障碍

**命题 96.7（成熟实分类在全效应上的应用）。** 在(96.1)的实域 $c=2$ 下，必有 $n\ge3$，
且经过正交换基，原空间准确为

$$
L=\{X\in\operatorname{Sym}_n(\mathbb R):X_{12}=X_{13}=0\}.
\tag{96.26}
$$

$n=3$ 时它是完整 $\mathbb R\oplus\operatorname{Sym}_2(\mathbb R)$；
$n\ge4$ 时原 $\mathrm G_2$ 本身失败，并有全效应最小值恰为 $1/4$ 的原三纯点见证。

证明。分类输入取 Argue–Kılınç-Karzan–Wang，
*Necessary and sufficient conditions for rank-one generated cones*，
[arXiv:2007.07433v2 Theorem 4][AKW96]：两个实对称等式约束的PSD截面若ROG，则其法向张成含一个非零PSD矩阵，
或者两个法向具有共同线性因子，写为 $A=\operatorname{Sym}(az^\mathsf T)$、$B=\operatorname{Sym}(bz^\mathsf T)$，
其中 $\operatorname{Sym}(Y)=(Y+Y^\mathsf T)/2$。
这里法向独立且全迹零，第一种可能被排除；第二种给 $a,b\perp z$，且 $z\ne0$、$a,b$ 独立。
正交地选择 $z$ 的方向为 $e_1$、$\operatorname{span}\{a,b\}$ 为 $\operatorname{span}\{e_2,e_3\}$，
再对两个等式作可逆实换基，即得(96.26)。故 $n\ge3$。
这一步在93.2的归一化之后只用正交换基，保持原迹；
Hildebrand [§6.2 Theorem 6.5][H96] 的抽象同构分类与此相符，但不被用来擅自保任意原 $u$。
上述分类是成熟输入，以下只是它对原全效应条件的应用。

令

$$
H_1=e_1^\perp,\qquad H_2=\operatorname{span}\{e_1,e_4,\ldots,e_n\}.
\tag{96.27}
$$

秩一约束就是 $w_1w_2=w_1w_3=0$，所以全部原纯点恰为单位向量在 $H_1\cup H_2$ 上的秩一投影。
这也给整个原锥等于这两个子空间上完整PSD锥的和：对原PSD矩阵取Gram向量 $g_i$，
$g_1\perp g_2,g_3$；沿 $\mathbb Rg_1$ 及其正交补拆分全部 $g_i$，
就得到分别支撑在 $H_2,H_1$ 的PSD矩阵。$g_1=0$ 时整个矩阵已支撑在 $H_1$。
因此以唯一 $E\in L$ 表示原泛函 $f_E(X)=\operatorname{tr}(EX)$ 时，整个原 proper 区间准确为

$$
f_E\in[0,u]\quad\Longleftrightarrow\quad
0\preceq E|_{H_1}\preceq I_{H_1},\qquad
0\preceq E|_{H_2}\preceq I_{H_2}.
\tag{96.28}
$$

这里 $E|_{H_i}$ 表示压缩；没有要求 $E$ 在整个环境中为正收缩。
$n=3$ 时 $H_2=\mathbb Re_1$ 与 $H_1$ 正交，正是完整块，93.2给全部结论。

若 $n\ge4$，取同一原模型中的

$$
v=\frac{e_1+e_4}{\sqrt2},\qquad
w_\pm=\frac{e_4\pm e_2}{\sqrt2},\qquad
p=vv^\mathsf T,\quad q_\pm=w_\pm w_\pm^\mathsf T,
\tag{96.29}
$$

并取原泛函

$$
f_\pm(X)=\tfrac12(X_{11}+X_{22}+X_{44})+X_{14}\mp X_{24}.
\tag{96.30}
$$

其代表矩阵在 $H_2$ 上是 $p$，在 $H_1$ 上是 $w_\mp w_\mp^\mathsf T$，其余方向为零。
故(96.28)验证它们在整个原锥 proper，且 $f_\pm(p)=1$、$f_\pm(q_\pm)=0$。
另一方面

$$
m=\frac{q_++q_-}{2}=\tfrac12(E_{44}+E_{22}).
\tag{96.31}
$$

任意原 $f_E\in F_p$ 在完整 $H_2$ 上是确认 $v$ 的正收缩，因此该压缩固定 $v$，并大于等于 $p$；
所以 $f_E(E_{44})\ge1/2$。原正性又给 $f_E(E_{22})\ge0$，故 $f_E(m)\ge1/4$。
投影限制效应 $h_p$ 达到等号，遂有

$$
T_p(q_+)=T_p(q_-)=0,\qquad T_p(m)=\tfrac14.
\tag{96.32}
$$

这是第90—91章全效应三点链障碍在正规形中的应用：它排除这一整个实余维二分支的 $\mathrm G_2$，
并非一个满足 $\mathrm G_2$ 却失败 $\mathrm{Z0}$ 的反例。证毕。

### 96.7 低余维等价、低支撑边界与真实不相容族

**定理 96.8（同一低余维域的完整等价）。** 在两域各自的(96.1)且 $c\le2$ 时，以下条件等价：

$$
\mathrm G_2\ \Longleftrightarrow\ \mathrm{FC}\ \Longleftrightarrow\
\text{完整 }\mathrm{Z0}\ \Longleftrightarrow\ S\
\Longleftrightarrow\ [L\text{ 在 }A\circ B=(AB+BA)/2\text{ 下闭合}].
\tag{96.33}
$$

它们还等价于所有 $Z\in L$ 的正负谱部分留在 $L$，以及下述准确完整块形式：
实域在正交换基后为完整实对称块直和，复域在酉换基后为完整实对称块与复Hermitian块直和，
全部块大小之和为 $n$。此时整个原效应及其least确认准确为

$$
[0,u]=\{f_E:E\in L,\ 0\preceq E\preceq I_n\},\qquad
e_p(X)=T_p(X)=\operatorname{tr}(pX)\quad(X\in K),
\tag{96.34}
$$

并有原 $\mathrm A,\mathrm H,\mathrm{Boundary},\mathrm Q$；原 $\mathrm B$ 在这些ROG域中本已自动成立。
此外，全部实ROG的 $n\le3$ 都满足 $\mathrm G_2\Longleftrightarrow\mathrm{Z0}$，不另限 $c$；
两域的 $n\le2$ 则自动具有完整块结构。

证明。复域的新增方向由96.6给出。实域 $c\le1$ 由96.4给出；$c=2$ 由96.7知
$\mathrm G_2$ 只能在 $n=3$ 的完整块分支成立，故也给 $\mathrm{Z0}$。
反向由96.3，完整 $\mathrm{Z0}$ 给全部 $\mathrm G_k$。
其余等价、(96.34)和几何结论准确复用93.2、94.2的同归一化分类及89.4；
特别是从(96.8)到谱闭合所用的是同一个原最优基范数分解及其共同饱和效应，
不是另加谱性或Jordan假设。

对低支撑边界，先用(96.5)换到包含全部对角矩阵的坐标。$n=1$ 只有一个标量块。
$n=2$ 时 $L$ 的非对角系数空间是 $\mathbb F$ 的实子空间。
实域只有零或整个 $\mathbb R$，给两个标量块或完整实二阶块；
复域还允许一条实线，经对角酉相位换基成为完整实二阶块，或允许整个 $\mathbb C$ 而成为完整复二阶块。
故实域 $c\le1$、复域 $c\le2$，且这些情形全部已有完整块。

实域 $n=3$ 时框架保证 $\dim L\ge3$，所以 $0\le c\le3$。
$c\le2$ 已证；$c=3$ 时 $\dim L=3$，故 $L$ 就是该框架的全部对角空间，亦为完整标量块。
分类的准确后果为

| 实域共同支撑 $n=3$ 的余维 | 原空间或限制 | $\mathrm G_2$ 与完整 $\mathrm{Z0}$ |
| --- | --- | --- |
| $c=0$ | 完整 $\operatorname{Sym}_3(\mathbb R)$ | 都成立 |
| $c=1$ | 一个非零迹零法向 | 都不成立 |
| $c=2$ | 正交换基后的 $\mathbb R\oplus\operatorname{Sym}_2(\mathbb R)$ | 都成立 |
| $c=3$ | 正交换基后的全部对角空间 | 都成立 |

第二行的排除只需维数：完整实块分割 $3$ 的实余维为 $0,2,3$，没有 $1$；
由已证等价即同时排除两条件。证毕。

**推论 96.9（复余维一二的维数排除及一般反例必要范围）。** 在复ROG域 $n\ge3$、$c=1$ 或 $2$ 时，
$\mathrm G_2,\mathrm{FC},\mathrm{Z0}$ 均不成立。
若将来某个实或复ROG模型满足 $\mathrm G_2$ 却不满足完整 $\mathrm{Z0}$，则其必要范围分别是
实域 $n\ge4,c\ge3$ 和复域 $n\ge3,c\ge3$。
在任何这样的模型中，存在一个原可排除但非正交的纯对 $p,q$，以及同一补框架的一部分，
组成一个最小不相容提升族，其项数 $m$ 满足

$$
3\le m\le\min(n,c+1).
\tag{96.35}
$$

证明。若复域满足任一所列条件，96.8给完整实复块。
将全部块大小记为 $t_1,\ldots,t_k$，其中实块大小另记为 $r_\alpha$，则在原复环境中的实余维为

$$
c=2\sum_{i<j}t_it_j+\sum_{\alpha\text{ 为实块}}\frac{r_\alpha(r_\alpha-1)}2,
\qquad \sum_i t_i=n.
\tag{96.36}
$$

若 $k\ge2$，跨块项至少为 $2(n-1)\ge4$：将若干块合并只减少跨块项，
两块大小 $a,n-a$ 的乘积至少为 $n-1$。
若只有一个实块，余维为 $n(n-1)/2\ge3$；若只有一个复块，余维为零。
因此没有 $c=1,2$。这个计算专属 $\operatorname{Herm}_n(\mathbb C)$ 的实维数，不能从实化转移。

一般必要范围由96.8及低支撑边界给出。若 $\mathrm{Z0}$ 失败，96.3给原纯 $p\perp q$ 而 $v^*w\ne0$。
对它和(96.5)的全部补框架点，有

$$
\mathcal M_{pq}\cap\bigcap_{j=2}^n\mathcal M_{pr_j}=\varnothing,
\tag{96.37}
$$

否则共同 $M$ 固定 $v$，与 $v^*Mw=0$ 矛盾。
全部框架集合自身含 $I_n$，故任一不相容子族必含 $\mathcal M_{pq}$。
Helly从这个具体的 $n$ 元族中给至多 $c+1$ 元不相容子族，再取包含意义下最小者；
$\mathrm G_2$ 排除一元或二元失败，得到(96.35)，其中至少两个成员来自同一补框架。
这只是实际原模型反例必须满足的结构，没有构造更高余维反例。证毕。

### 96.8 保留全部原非几何条件的完整候选

**定义 96.10（低余维纯纯候选）。** 取94.5、89.7的同一个原装饰元组 $\mathcal O$。
记 $\mathcal N_{89.7}(\mathcal O)$ 为定义89.7除每个 $X=A,D,E$ 的几何项
$\mathrm B+\mathrm{Boundary}$ 外的全部条件，逐条保留其原量词、原对象和共同 $\mathfrak S(\mathcal O)$。
特别包括原概率像与整个测试像、中点与非负质量缩放、同一个 $L:D\times A\to E$ 和同一读回 $p$ 两次、
两实张成、全实 $Z$、含秩一分支的完整(83.8)、C2、整个 $G=1_E$，以及恢复精确PRE以后
同一个原资格态的整个输出H13；迹、伴随、中央质量、零分支和空活跃集按原定义。
此记号是对那一整组条件的引用，不用这些列举取代其完整正文。

令 $\mathcal D_{\le2}^{\mathbb C}(\mathcal O)$ 要求每个原 $X=A,D,E$ 都有94.1的整个复秩一ROG表示，
原 $u_X$ 任意严格正，并在94.2各自归一化后的复环境中满足实余维 $c_X\le2$。
定义唯一这一同数据候选

$$
\mathsf R_{\mathrm G_2,\le2}(\mathcal O):=
\mathcal D_{\le2}^{\mathbb C}(\mathcal O)\ \land\
\mathcal N_{89.7}(\mathcal O)\ \land\
\bigwedge_{X=A,D,E}\mathrm G_2(V_X,C_X,u_X).
\tag{96.38}
$$

它仅在明示的同一个低余维域中，以纯纯 $\mathrm G_2$ 替换94.5的固定补态 $\mathrm{FC}$。
没有以矩阵子空间 $L_X$ 替换原过程 $L$，也没有改变任何原来源、准备、菜单、参考、事件或合法未来。

**推论 96.11（完整原量子包的同域等价）。** 在定义96.10下，

$$
\begin{aligned}
\mathsf R_{\mathrm G_2,\le2}(\mathcal O)
&\Longleftrightarrow
\mathcal D_{\le2}^{\mathbb C}(\mathcal O)\land
\mathsf R_{\rm FC}^{\mathbb C\text{-}\rm ROG}(\mathcal O)\\
&\Longleftrightarrow
\mathcal D_{\le2}^{\mathbb C}(\mathcal O)\land\mathsf R_{\rm polar}(\mathcal O)\\
&\Longleftrightarrow
\mathcal D_{\le2}^{\mathbb C}(\mathcal O)\land
[\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}]^{\rm ev}(\mathcal O),
\end{aligned}
\tag{96.39}
$$

并与89.8其余完整包在同一域内等价。每个量子消费者仍使用94.6的全部各自原前件。

证明。逐个同一原 $X$ 用96.8将 $\mathrm G_2$ 换为 $\mathrm{FC}$，再完整应用94.6和89.8。
所有非几何条件完全相同，对偶运输的仍是整个原效应区间，故量词没有缩成局部效应。
由96.9，若某个 $n_X\ge3$，满足候选还迫使该表示的 $c_X=0$；低支撑处则保留96.8的完整实复块分支。
完整复矩阵块任意大小均有 $c_X=0$，故这一几何域容纳非经典复模型，但矩阵形式不供应原实际资源。

具体消费范围准确取94.6：一般EJA忠实桥与原精确两接口66.3承担复型和Born；
同一原 $L,p,\omega$、全实关系、两张成、完整尺度及同资格态整个H13承担指定二份／三份、张量和读回；
逐同事件HP提升、准确参考输出或充分递归参考及独立预算承担CP、Kraus与仪器；
锐投影、逐点中性和原输出校准承担既有事件的Lüders唯一性；
原连续齐次可逆时间群、实际逆、钟与单位承担Hamiltonian解释。
这些均按94.6的完整量词复用，不由 $\mathrm G_2$ 单独得到。
其所引Library二元附录的全有限控制、END或三角形选择、一次同事件Choi及有限实现，
以及VII22、24—28各自已证的Born、完成PSD、联合菜单和下降／回返，仍在94.6列明的全部原前件下成立，
不重新列作未解，也不把各自完成载体等同于这里的原 $A,D,E$。

第95章是另一静态入口：一对全域 $T_p+T_q=u$ 与紧纯传递给整个球，再按95.5—95.7支付全有限寄存器资源。
本推论既不从 $\mathrm G_2$ 推出那一对穷尽关系或其控制，也不以第95章替代89.7的指定原接口。
若要连接两套完整数据，仍须给出同载体、同来源、同操作的接口对应；(96.39)不作这种无前件合并。证毕。

### 96.9 所关闭的混态桥与一般目标的边界

**命题 96.12（准确简化与未证范围）。** (96.38)在同一 $c_X\le2$ 复ROG域内有与94.5相同的模型类，
并以只量化原纯点的三元关系替代固定补态检验；实域亦有(96.33)的相同几何等价。
这关闭了“纯纯零拼合到全部原混态零面”的桥，没有证明一般ROG中的
$\mathrm G_2\Rightarrow\mathrm{Z0}$，也没有证明一般整球载体中的 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$。

证明与范围。新增的共同实现链是(96.4)的全原效应提升、96.5的单纯零条件钉住、
(96.25)与同一补框架的相容性，以及(96.9)的原混态零面。
实余维二通过成熟分类及96.32排除非块分支。
在同一低余维域内，这些条件与完整 $S$ 等价；$\mathrm G_2$ 从检验前件删除了混态补态，
但低余维和整个ROG表示是实质适用条件，不能据此宣布它在全部ROG域上比94.5更弱，
也没有取得最少独立物理公理数。复型唯一选择、原表示来源、复合、CP、既有更新和物理时间仍逐项消费96.11所引用的原条件。

更高余维时，一个纯零方程之后仍可能留有多维提升自由度；96.35只是任何真实反例必须满足的原模型约束，
不是反例的存在证明。一般整球载体中，单位 $u\in V^*$ 不自动给原 $h\in V$、补投影、完整正交框架
或这些PSD提升，因此本章没有补上89.12、94.7保留的一般关系。
一般 $\mathrm G_2$ 问题及一般 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$ 均保持未证；
并未由某个较强充分条件失败推出原目标为假。

数学归属中，有限维正锥双极性、Helly、Gram连续修正、PSD支撑和普通矩阵线性代数是成熟工具；
Argue–Kılınç-Karzan–Wang Theorem 4及Hildebrand Theorem 6.5的实分类是成熟输入，
Hildebrand §9的复余维二秩事实已在96.5给出所需证明。
93—94章的归一化、基范数桥、完整块、least确认和全部消费者均为复用。
这里的仓内综合为全原效应共同提升的有限零集合表示、复单纯零条件钉住及其与全 $\mathrm G_2$ 和补框架的组合，
以及实分类在原效应上的应用和(96.39)的同域替换。
没有使用Hildebrand Theorem 3.18的未知复推广，也没有使用代数几何分类解决更高余维。
这些是明确假设下的纸面证明，不作全球原创、文献穷尽、Lean／kernel核验或经验实现主张。

白话说，这份完整候选先保留原来的整间矩阵屋子和全部合法尺，只在每个系统的效应提升里最多留下两只实旋钮。
若两只旋钮都能改变一盏纯灯的方向，原模型的二次约束就保证有另一盏可熄灭的纯灯，单靠它的零条件把位置唯一钉住；
若只剩一只旋钮，一盏补方向的灯就能钉住这一列。三纯点关系要求被钉住的位置与整排原补灯分别相容，
所以它终于固定原纯方向，所有可排除灯都真正正交。
对混态则用原来同一把尺把组成它的每盏纯灯逐项熄灭，整片暗面便对任意混合封闭。
这让检验只涉及纯灯；屋子的原表示从哪里来、为何唯一选复色，以及复合、同事件CP、更新和时钟，仍保留各自完整条件。证毕。

[AKW96]: https://arxiv.org/html/2007.07433v2
[H96]: https://arxiv.org/html/1409.4781v2

## 追加锚（本行以下为增补区）

## 97. 纯点穷尽与复合相容性恢复同一个原控制群

### 97.1 纯点关系、数学闭包与整个原球

**定义 97.1（纯域一对入口）。** 保留95.1的非零有限维实 $V$、闭尖生成凸锥 $C$、严格正的原单位
$u$、整个紧全张成基 $K=C\cap\{u=1\}$、全部 $P=\operatorname{ext}K$ 和 $W=\ker u$。
数学效应始终是整个原区间 $\mathcal E=[0,u]_{C^*}$，并定义

$$
F_r=\{f\in\mathcal E:f(r)=1\},\qquad
T_r(x)=\inf_{f\in F_r}f(x)\quad(r\in P,\ x\in K).
\tag{97.1}
$$

原实际群 $H\le\operatorname{Aut}(C,u)$ 在全部原纯点上精确传递；不输入它的紧性、闭性或连通性。
取原纯点 $p,q$，只要求

$$
T_p(r)+T_q(r)=1\qquad(\forall r\in P).
\tag{97.2}
$$

实际资源仍是95.3的同一个凸效应像 $D\subseteq\mathcal E$、原 $0,u$、真正共同可用的原种子菜单
$(a_0,b_0)$，其中 $a_0(p)=b_0(q)=1$、$a_0+b_0=u$，以及原所需标签 $H_*\subseteq H$：
$\{hp:h\in H_*\}=P$，每个指定 $a_0\circ h^{-1}$ 都实际可用且属于原 $D$。
精确传递不能改成稠密轨道；数学效应的存在不替代种子菜单、其共同可用性或这些实际标签。

**定理 97.2（纯域穷尽的全域恢复与原球）。** 定义97.1下，(97.2)等价于(95.2)的全部原混态等式。
每个 $F_r$ 是非空紧效应面，(97.1)逐点达到。存在唯一原中心 $c$ 和椭球度量 $s_0$，使整个原基、
原纯集和内在效应满足(95.3)—(95.7)，并且原 $D=\mathcal E$。
这里 $d=\dim W\ge1$；同一原 $H$ 忠实且传递地作用于整个 $S^{d-1}$，但本定理不先给 $H$ 拓扑性质。

证明。从 $K$ 选出 $V$ 的一组基，效应在每个基点的值均在 $[0,1]$，故闭集 $\mathcal E$ 有界而紧。
$F_r$ 包含 $u$；若一个非平凡凸组合在 $r$ 处为一，其两项均须为一，所以 $F_r$ 也是闭面。
连续评价在其上取得最小值，且 $T_r(r)=1$、$0\le T_r\le1$。
有限维紧凸分解给每个 $x\in K$ 的有限纯分解 $x=\sum_i\lambda_i r_i$，
$\lambda_i\ge0$、$\sum_i\lambda_i=1$；可取项数至多 $\dim V$。不要求 $P$ 预先闭或每点暴露。

在 $r=p$ 处，(97.2)给 $T_q(p)=0$，并排除 $p=q$。
取达到此零的 $f\in F_q$，则 $f(p)=0$，所以 $u-f\in F_p$。
两个下包络是凹函数：对任意有限凸组合，线性效应逐项支配各自的下确界，取下确界即可。
因此对上述任意原 $x$，

$$
1=\sum_i\lambda_i\bigl(T_p(r_i)+T_q(r_i)\bigr)
\le T_p(x)+T_q(x)\le (u-f)(x)+f(x)=1.
\tag{97.3}
$$

这就是全域等式；反向只需限制到 $P$。其中 $f,u-f$ 只是数学见证，尚未认作实际共同菜单。
两凹函数之和恒定，使每个函数又凸，故 $T_p,T_q$ 仿射。
$\operatorname{aff}K=\{u=1\}$，仿射延伸及齐次化唯一给 $e_p,e_q\in\mathcal E$；
$K$ 张成 $V$ 给 $e_p+e_q=u$。在 $K$ 上 $e_p\le f'$ 对所有 $f'\in F_p$ 成立，
按正质量缩放即在整个 $C$ 上成立；对 $q$ 同理。

为构造数学平均，先令 $B_K=\operatorname{conv}(K\cup(-K))$。
它是有内点的紧对称凸体，其 gauge 为 $V$ 上范数。所有原保 $C,u$ 自同构均为此范数的等距映射。
有限维范数等价给这些矩阵的一致界；保持范数的矩阵极限仍单射，因而可逆。
若自同构 $A_j\to A$，闭性给 $AK\subseteq K$；逆矩阵连续性同样给 $A^{-1}K\subseteq K$。
所以

$$
\mathcal A=\operatorname{Aut}(C,u)\text{ 是紧矩阵群},\qquad
L=\overline H^{\,\mathcal A}\le\mathcal A
\tag{97.4}
$$

是紧矩阵 Lie 群。任一自同构保持全部极点，故 $Lp\subseteq P$；由 $Hp=P$ 又有 $Lp=P$。
闭包及其 Haar 测度只作数学工具，不增加实际极限、随机化或菜单。

现在只用原 $H$ 运输最小确认。原自同构双射全部效应及确认面，故

$$
T_{hr}(x)=T_r(h^{-1}x),\qquad
e_{hp}=e_p\circ h^{-1},\qquad e_{hq}=u-e_{hp}\quad(h\in H).
\tag{97.5}
$$

于是每个原纯点都有同一内在下确界的线性最小确认和一个纯补点，无选取歧义。
95.2证明中取得唯一饱和及边界纯性的步骤完全不使用 $H$ 紧性；具体地，任选辅助欧氏范数和原仿射点 $o$，
原 $K$ 的最远点 $z$ 由 $\langle z-o,x-o\rangle$ 唯一暴露，因为 Cauchy–Schwarz 的两个等号迫使 $x=z$。
将此高度的最小值归零、最大值归一，得到仅在 $z$ 取一的 $f_z\in F_z$。
$e_z\le f_z$ 使 $e_z$ 仅在 $z$ 取一，(97.5)和原 $H$ 传递把唯一饱和传播给每个 $e_r$。
若 $e_s=e_t=u-e_r$，在 $s$ 处评价即得 $s=t$，纯补点 $r^\perp$ 因而唯一。
任意 $y\in\operatorname{rbd}K$ 有非恒定支撑高度 $0\le f\le u$、$f(y)=0$、$\max_K f=1$。
最大值面有纯点 $r$，所以 $e_r\le f$；在整个零面上 $e_r=0$、$e_{r^\perp}=1$。
唯一饱和使这个零面仅为 $\{r^\perp\}$，特别是 $y$ 纯。

只在 $L$ 上取 Haar 平均：$c=\int_L \ell p\,d\ell$，并将 $W$ 上任意正定内积平均成 $L$ 不变的 $s$。
$c$ 是 $L$ 不动点且在 $\operatorname{ri}K$：若它有非恒定非负零支撑高度 $g$，
连续非负函数 $g(\ell p)$ 的积分为零，Haar 测度的满支撑迫使它恒零；$Lp=P$ 和有限纯分解遂使 $g|_K=0$，矛盾。
原 $H\subseteq L$ 固定 $c$，且 $Hp=P$，故全部纯点离 $c$ 的 $s$ 半径为同一 $\rho>0$。
有限纯分解给 $K-c\subseteq\rho\operatorname{Ball}_s$。
每条从 $c$ 出发的射线在紧凸 $K$ 中有正的有限终点，此终点在边界，因而纯，半径必为 $\rho$。
每条半径段都在原 $K$，得到反向包含。取 $s_0=s/\rho^2$ 即得整个原球。
有界凸体中心的唯一性及极化恒等式给 $c,s_0$ 唯一性。

在坐标 $tc+w\mapsto(t,x)$、$s_0(w,w)=\|x\|^2$ 中，原锥及全部效应的计算是

$$
\begin{gathered}
C=\{(t,x):t\ge\|x\|\},\quad K=\{(1,x):\|x\|\le1\},\quad P=\{r_v=(1,v):\|v\|=1\},\\
f(t,x)=\alpha t+b\cdot x\in\mathcal E
\ \Longleftrightarrow\ \|b\|\le\alpha,\ \alpha+\|b\|\le1,\\
f\in F_{r_v}\ \Longleftrightarrow\
f(t,x)=(1-\lambda)t+\lambda v\cdot x,\quad 0\le\lambda\le\tfrac12,\\
T_{r_v}(1,x)=e_{r_v}(1,x)=\frac{1+v\cdot x}{2},\qquad r_v^\perp=r_{-v}.
\end{gathered}
\tag{97.6}
$$

故纯比较互反，(95.7)的正定自对偶配对和有限 PD 按原球计算恢复。
原 $H$ 的作用属于 $\mathrm O(d)$ 且忠实：它固定 $c$，而 $V=\mathbb Rc\oplus W$。
这里没有把95.2依赖紧 $H$ 的 Haar 步骤当作已适用；上面的平均全部属于 $L$。
最后95.3的证明只用已得最小性、球形和原实际资源：
$a_0-e_p,b_0-e_q$ 非负且和为零，故 $a_0=e_p,b_0=e_q$。
原所需拉回标签遂给每个 $e_r\in D$。对 $s=\|b\|$、$v=b/s$（$s=0$ 时任取单位方向），

$$
f=2s\,e_{r_v}+(\alpha-s)u+(1-\alpha-s)0
\tag{97.7}
$$

是原 $D$ 中的三项有限凸组合，因而 $D=\mathcal E$。整个证明没有把数学补效应或闭包操作当作实际资源。证毕。

### 97.2 同一原有限寄存器及事件合同

**定义 97.3（完整原资源包）。** 在97.1—97.2的同一原数据和所得球坐标下，逐项保留95.5的
全部原寄存器条件，但不继承其首句引用的“同一实际紧连通 $H$”这一拓扑前提。
准确地，保留每个给定有限 $N$ 的原 $V_N=V^{\otimes_{\mathbb R}N}$、$u_N=u^{\otimes N}$、
紧凸全张成 $K_N$、$K_1=K$、$C_N=\operatorname{cone}K_N$，忠实局域／产品层析、实际产品准备／测试，
和同一次 $F^{\otimes N}$ 校准。原纯产品概率及其在每个实际可逆作用后的 $[0,1]$ 界仍为(95.11)。
独立的原局域 $H$ 控制在整个旁观者载体上恒等。$G_N$ 仍是原实际归一线性可逆群，不输入其拓扑。

同一个原非零生成元的完整 $g(\mathbb R)=\{\exp(tX):t\in\mathbb R\}$ 实际可用，
某个 $g(t_0)$ 越出整个 $\mathrm{SO}(d)\times\mathrm{SO}(d)$。
每个原有限连通图上的每条边保留(95.12)的精确放置、固定端点顺序和所有相关坐标上的旁观者恒等；
不增加任意二体操作的搬运公理。原三点路径 $1-2-3$ 上的预选择 END 仍是实际、仿射、保质量、全域，
输出为保留端点的**同一个有序原 $K_2$**，在全部产品上为中腿收缩，继而由张成唯一确定其齐次线性延伸。

还逐项保留95.6的全部指定原事件、未归一分支和实现资源：原记录、ready、控制、合法未来，
包括零及全部实准备关系的实线性输入律，和每个同事件的准确产品扩张／来源识别。
在矩阵识别后，每个指定 $e:n\to m$ 仍支付(95.13)：实际可准备的输入维数参考 $\Omega_n$，
以及准确的 $J_e=(\operatorname{id}_{2^n}\otimes\widetilde\phi_e)(\Omega_n)$ 的**整个**原参考／输出正性。
每个原分支保留独立 TNI 预算，确定事件保留全部正输入上的 TP；完整仪器保留同一菜单的记录、
真和 $\phi_{\rm total}=\sum_a\phi_a$ 与总 TP。质量与零标签保留，只有正质量才允许条件化。
所有有限映射和仪器的实现另有原实际纯二元辅助、导出控制的顺序复合、输出为同一保留原寄存器且校准为偏迹的
typed 全域丢弃、(95.14)在忽略指针前的保留输出分支律、实际标签／记录及真实粗粒化。
空辅助串、空环境串、标量质量类型以及尺寸／零编码补齐沿用原合同。
这些引用保留95.5—95.6的完整量词和对象，并不以本段列举替换原条文。

### 97.3 在 END 之前恢复同一原局域群

**定理 97.4（复合相容性强迫原 $H=\mathrm{SO}(3)$）。** 在定义97.1、97.3下，$d=3$，
同一原 $H$ 在一次固定球坐标中就是 $\mathrm{SO}(3)$，因而紧、闭且连通。
这包括单元 $N=1$ 的原裸控制群，不以二体或辅助实现代替原 $H$。
在使用 END 之前，原整个二份基已经是 $\mathcal D(4)$ 或 $T_1\mathcal D(4)$，
在各自情形下，完整二体群由原语有限字精确实现，且每个扇区都排除原 $H$ 的反定向元。

证明。先排除 $d=1$。此时原 $K$ 是经典两点区间，其两坐标效应实际可用。
四个纯产品准备是 $V_2$ 的一组基；任意原归一二份点的四个产品读数就是这组基下的系数，均非负且和为一。
因此 $K_2$ 包含于四顶点经典单纯形；原产品准备和凸性给反向包含，故是**整个**该单纯形。
其归一可逆群只置换四个顶点，因而有限。连续的原 $g(t)$ 从恒等开始，只能恒为恒等，
与 $g(t_0)$ 越出此时平凡的 $\mathrm{SO}(1)\times\mathrm{SO}(1)$ 矛盾。所以 $d\ge2$。

由(97.4)、(97.6)，$L$ 是球面传递的紧 Lie 子群，$L^0\le\mathrm{SO}(d)$。
它的分支数有限。$L^0$ 正规且每个轨道紧闭，$L$ 传递使球面分成有限个 $L^0$ 轨道；
有限个互不相交闭集中的每个也开。$S^{d-1}$ 连通，故只有一个轨道。
于是 $L^0$ 在整个球面上传递，其矩阵作用连续、线性且忠实，特别满足 almost effective 条件。

令 $\Gamma_2$ 为原局域 $H$ 与全部原 $g(t)$ 的实际有限字子群，
$\mathscr C_2=\overline{\Gamma_2}$，$S=\mathscr C_2^0$。
对原 $K_2$ 使用 Library §2 的对称凸包范数证明，得到 $\mathscr C_2$ 为保持整个原 $K_2$、
归一和原产品概率的紧矩阵 Lie 群；这里不使用该处依赖原局域连通性的结论。
局域闭包包含 $\widehat L\times\widehat L$，所以其连通子群
$\widehat{L^0}\times\widehat{L^0}$ 属于 $S$；原完整路径也在 $S$ 中。
因此对任一固定单位 $a$，准确有

$$
\widehat{L^0}\times\widehat{L^0}\le S,\qquad
\tfrac14(\widehat a\otimes\widehat a)\cdot
S(\widehat a\otimes\widehat a)\subseteq[0,1],\qquad
g(\mathbb R)\subseteq S.
\tag{97.8}
$$

应用 Masanes–Müller–Pérez-García–Augusiak 的[技术 Theorems 1–2][MM97]（PDF 第10页），
只把其中的连通复合群取为 $S$、局域群取为 $L^0$。
其 §IV A（第16—18页）按正交坐标分类的是紧、连通、连续线性且球面传递的 almost effective 群；
这些条件逐项已由上一段满足，$d=2$ 的 $\mathrm{SO}(2)$ 在表中是 $\mathrm U(1)$ 表示。
同一正交换基用于两个局域因子；(97.8)给所需固定产品向量的完整概率界。
Theorem 1 若 $L^0\ne\mathrm{SO}(3)$，便迫使 $S$ 处于整个局域旋转群，
与原路径中的非局域元素矛盾。因此 $d=3,L^0=\mathrm{SO}(3)$。
Theorem 2 的局域选项同样被排除，剩下

$$
S=Q_2\quad\text{或}\quad S=T_1Q_2T_1=:H_2,\qquad
Q_N=\{\operatorname{Ad}_U:U\in\mathrm{SU}(2^N)\}.
\tag{97.9}
$$

Pauli 识别仍只是在原 $F^{\otimes N}$ 后统一固定一次；此时原态仅是迹一 Hermitian 矩阵。
$T_i$ 是第 $i$ 因子的转置坐标反射，不是实际门。尚未断言整个 $\mathscr C_2$ 连通或整个原 $K_2$ 正。

精确实际控制从原完整路径取得，不要求 $g(\mathbb R)$ 闭或嵌入。
紧 Lie 群的单位分支 $S$ 开，故 $\Delta=\Gamma_2\cap S$ 稠密于 $S$。
$X\ne0$ 且 $X\in\mathfrak s$；两种 $S$ 的 Lie 代数均为非交换简单的 $\mathfrak{su}(4)$。
复用 Library §2 *Exact-generation lemma* 的共轭理想／反函数定理证明，直接以这个原 $X$ 取

$$
E_X=\operatorname{span}_{\mathbb R}\{\operatorname{Ad}_\delta X:\delta\in\Delta\}.
\tag{97.10}
$$

该非零子空间受 $\operatorname{Ad}_\Delta$ 保持；有限维闭性和稠密性使其受 $\operatorname{Ad}_S$ 保持，
微分后是 $\mathfrak s$ 的非零理想，所以 $E_X=\mathfrak s$。
从这些实际共轭方向中取基 $Y_j=\operatorname{Ad}_{\delta_j}X$，
$\exp(tY_j)=\delta_jg(t)\delta_j^{-1}$ 对全部实 $t$ 都是原实际有限字。
映射 $\prod_j\exp(t_jY_j)$ 在零处导数为该基给出的同构；反函数定理给 $\Delta$ 中的开单位邻域。
连通 $S$ 没有真开子群，故 $\Delta=S$。这使用完整实参数和原逆／复合，不把稠密性本身当作实际性，
也未套用需要闭生成子群的版本。每个字的全部原语均有原旁观者恒等放置，故同一有限字精确提升到各给定边。

在选 END 扇区前，应用 Library §3 *Pair-state lemma before choosing a branch*，其两个包含如下。
取 $S_2=I$ 或 $T_1$。在 $S_2(K_2)$ 上完整 $Q_2$ 已实际作用；原纯产品及产品测试在此坐标下仍是产品。
原 $P_{00}$ 的轨道给所有秩一投影，有限谱混合给 $\mathcal D(4)\subseteq S_2(K_2)$。
反向，对任意原点的 Hermitian 代表 $A\in S_2(K_2)$ 和任意单位向量 $\psi$，
完整实际 $Q_2$ 将 $\psi$ 送到产品读出方向，原产品概率界给 $\langle\psi|A|\psi\rangle\ge0$。
所以 $A\succeq0$，得到 $S_2(K_2)\subseteq\mathcal D(4)$，即所述整个原二份几何。

现在在两个扇区分别排除原 $H\le\mathrm O(3)$ 的反定向元。
若 $h\in H$ 且 $\det h=-1$，写 $h=R\tau$，其中 $\tau$ 是 Pauli 转置反射、$R\in\mathrm{SO}(3)$。
两种实际二体群都包含全部独立局域旋转，因为 $\tau\mathrm{SO}(3)\tau=\mathrm{SO}(3)$。
因此 $R^{-1}\otimes I$ 已有二体有限字实现，虽然尚未断言 $R\in H$。
与原实际 $h\otimes I$ 复合便使 $T_1$ 成为原二体实际自同构。
在 $Q$ 扇区，原 Bell 态 $B$ 被送到 $T_1B=\mathrm{SWAP}/2$，有特征值 $-1/2$，越出原 $K_2=\mathcal D(4)$。
在 $H$ 扇区，原 $T_1B\in K_2=T_1\mathcal D(4)$ 却被送到 $B\notin K_2$，仍矛盾。
所以两个扇区都迫使同一原 $H\le\mathrm{SO}(3)$；此处还没有使用 END。

最后把已知旋转事实用在这个原裸 $H$ 上。Alan F. Beardon，*Rotations in R3 and R4*，[Theorem 1.1及 §2][B97]，
对**任意**球面传递的 $\mathrm{SO}(3)$ 子群给整个 $\mathrm{SO}(3)$，不要求闭性。
在本数据中也可直接看出其证明的每一步属于原 $H$：精确传递给一个将 $v$ 送到 $-v$ 的原旋转，
它必为半周转；再以原 $H$ 的传递共轭取得任意轴的半周转。每个三维旋转都是两个半周转的乘积，
所以所有旋转均已在原 $H$ 中。这是该已知事实在原控制群上的应用，不用闭包或辅助单元补出 $N=1$ 控制。
于是原 $H=\mathrm{SO}(3)$。此时原局域 $H$ 与 $g(\mathbb R)$ 都在 $S$ 中，
结合 $S\subseteq\Gamma_2$ 才有 $\Gamma_2=\mathscr C_2=S$；其连通性到这里才恢复。证毕。

### 97.4 完整量子包与同一个原群上的等价

**定理 97.5（同数据完整候选）。** 令 $\mathcal O$ 包含97.1、97.3的全部原对象、菜单、标签、
原 $H$、各份数载体和指定事件／资源。记 $\mathsf{New}_{97}(\mathcal O)$ 为这套完整输入，
$\mathsf{Old}_{95}(\mathcal O)$ 为95.1、95.3、95.5—95.6的完整输入，保留相同对象，
只把纯域等式改为全 $K$ 等式并要求原 $H$ 紧且连通。则

$$
\mathsf{New}_{97}(\mathcal O)\ \Longleftrightarrow\ \mathsf{Old}_{95}(\mathcal O).
\tag{97.11}
$$

在此域内，95.7的全部有限寄存器、指定事件和仪器实现结论原样成立：

$$
\begin{gathered}
d=3,\quad H=\mathrm{SO}(3),\quad D=\mathcal E,\\
V_N\simeq\operatorname{Herm}(2^N,\mathbb C),\quad
K_N=\mathcal D(2^N),\quad C_N=\operatorname{Herm}_+(2^N,\mathbb C),\\
Q_N\cong\mathrm{PSU}(2^N)\subseteq G_N\quad\text{由原语有限字精确实现}.
\end{gathered}
\tag{97.12}
$$

每个原仿射 proper 效应有唯一矩阵 $0\le E\le I$，原概率为 $\operatorname{Tr}(E\rho)$。
满足原同事件参考条件的指定映射／分支分别为 CPTP／CP-TNI；完整原菜单给量子仪器。
全部有限 CPTP 映射和有限 CP 仪器在保留的实现资源下有映射与结果标签层面的实际实现。

证明。97.2恢复95.1的全原混态关系及原实际种子／效应资源，97.4恢复95.5曾输入的**同一个**原紧连通 $H$。
定义97.3没有删除其它任何原前件；到这一步才应用95.7。
其 END 消费的是已由两个包含取得的同一个原二份几何，以及原三点路径上的有限边字。
若为 $H$ 扇区，Library §3 *END excludes the reflected branch* 在 $T_2$ 坐标下用两边生成 $Q_3$，
制备普通端点 Bell 与中腿纯态的乘积；原 END 将其送到同一原 $K_2$ 外的普通 Bell，排除该扇区。
所用 END 是预先保留的全域同类型事件，不从随后生成的 SWAP、通用控制或酉扩张倒推。
选择 $Q$ 后，Library §3 *Finite graph generation on one carrier* 与 *All finite original states and controls*
逐原有限图给 $Q_N$，并以秩一轨道／有限谱混合及原负概率排除分别给原 $K_N$ 的两个包含。
$N=1$ 用97.2、97.4，不用二体实现替换原 $H$。

每个指定 $e:n\to m$ 的输入参考维数仍是 $2^n$，原整个输出锥由(97.12)已为 PSD；
原产品张成和同事件来源合同识别的仍是同一个 $\widetilde\phi_e$。
故95.7所用 Library §4 *rectangular CP and exact budgets* 的参数准确为 $d=2^n,b=2^m$，
给(95.18)的 Kraus、$E_e$、参考偏迹及独立 TP／TNI 预算；零映射直接处理。
其成熟数学接口是 Watrous，[Theorem 2.22、Theorem 2.26、Corollary 2.27][W97]，印刷页82—83、87—89，
本章归一 Choi 乘以输入维数并交换参考／输出次序即对应其约定。
保留原分支的记录、质量与真和后，逐分支 CP 给总 CP，正质量处才除以概率；零分支不消失。

全部实际实现准确复用95.7及 Library §4 *all finite register channels and instruments*。
通道取 $2^k\ge r$，仪器取 $2^k\ge\sum_a\max(1,r_a)$，两者都另取 $m+k\ge n$，
于是 $q=m+k-n\ge0$ 个实际纯辅助和 $k$ 个环境／指针单元在同一总寄存器中完成矩形等距扩张。
命名零分支保留零 Kraus 编码，未用编码补零；空串遵循原恒等约定。
原 typed 丢弃和忽略指针前的(95.14)分支律、实际记录及真粗粒化给准确未归一分支；最后只在正质量条件化。
这些是原实现定理的参数对应，不由单个效应、Choi 正证书或映射相同而生成实际资源。

这也证明(97.11)的正向；反向由旧全域等式限制到纯点，其它资源和原 $H$ 完全不变。
两边的 $e_r=T_r$、中心和度量是可恢复的数学数据；没有替换原控制群、原 $D$、菜单或事件。
这里只给原单元 $D=\mathcal E$；对联合寄存器，原已有实际效应的表示与全有限 POVM 的资源实现各有上述依据，
不把原 $D_N$ 重定义为生成菜单，也不声称原 $D_N=[0,u_N]$。
同一矩阵映射的构造不识别原设备、事件、历史或合法未来。证毕。

### 97.5 几何、标准公理与非空模型

**命题 97.6（有限量子对应及适用范围）。** 97.5具有标准复二元寄存器的非空模型；其公理对应为下表，
所列原资源是完整候选的条件。纯比较端点互换只给一个数的互反，不给物理仪器的交换执行律。

| 有限量子结构 | 本候选的原条件与推得结构 |
| --- | --- |
| 单元态、混合与比较 | 全原效应下确界、纯域一对穷尽及原精确纯传递给整个原 Bloch 球；真实种子、指定拉回和原凸性给全单元效应，比较为 $(1+v\cdot w)/2$。 |
| 复 Hilbert 空间与张量 | 原产品／层析、一次固定校准、完整非局域路径及整个旁观者恒等放置给 $d=3$ 和两体两扇区；预选择同类型 END 选普通复扇区。每个原有限寄存器为 $\mathcal D(2^N)$，纯几何为 $\mathbb{CP}^{2^N-1}$。 |
| 可逆控制 | 原全实路径经简单共轭理想与反函数定理给精确有限二体字；两个扇区都排除反定向原 $H$，精确纯传递再给原裸 $H=\mathrm{SO}(3)$。原有限连通图给 $Q_N\subseteq G_N$。 |
| Born 与共同测量 | 矩阵效应的原配对为 $\operatorname{Tr}(E\rho)$；全部有限共同 POVM 的实现还使用辅助、顺序、typed 丢弃、保留输出指针律和记录，不能从单个效应可用性取得共同菜单。 |
| 通道、分支与仪器 | 每个原事件的实线性和准确同事件参考整个输出正性给 CP；独立预算和真和给 TP／TNI 与完整仪器。所有有限实现仍需原实际资源、矩形尺寸补齐和零标签。 |
| 更新及物理时间 | 资源允许一种 Lüders 实现，不决定已有事件的唯一更新；Hamiltonian 时间解释另需原连续齐次可逆时间群、物理钟和单位，并保留加标量自由度。 |

证明。取每个有限原载体为 $\operatorname{Herm}(2^N,\mathbb C)$，原基为全部密度矩阵、原单位为迹，
实际资源取标准有限量子准备、酉控制、带记录的有限 CP 仪器、纯辅助、保留输出的计算基指针和同类型偏迹。
单元原 $H=\operatorname{Ad}\mathrm{SU}(2)\cong\mathrm{SO}(3)$；取原 $p=P_0,q=P_1$，
共同种子为 $\operatorname{Tr}(P_0-),\operatorname{Tr}(P_1-)$，$H_*=H$ 的原拉回标签全部实际可用。
确认秩一 $P$ 的正收缩在其像上恒等，在正交补上非负，故 least 确认为 $\operatorname{Tr}(P-)$，满足(97.2)。
取完整原路径 $g(t)=\operatorname{Ad}_{\exp(-it\sigma_z\otimes\sigma_z)}$；
$t=\pi/4$ 将 $|++\rangle$ 送到 Schmidt 秩二的纯态，故越出全部局域旋转。
它在每条给定边上的标准张量放置保持整个旁观者不动；三点路径的原 END 为 $\operatorname{Tr}_2$，
输出确为同一原 $\mathcal D(4)$。产品层析和固定 Pauli 校准满足原合同。
每个选定 CP 事件及分支在同一输入参考上的真实扩张给正 Choi 输出，原完整仪器保留预算、记录和真粗粒化。
上述实际辅助、指针与丢弃也给全部实现资源，包含零分支和空串，故这是一套共同满足所有条件的模型。

表中各结论由97.2、97.4、97.5逐项给出。特别地，单元球的维数由复合控制而定，
任意维 Lorentz 球本身都满足纯域穷尽；静态一对关系并不单独选三维。
精确原纯传递、原全效应域、实际种子和各份数／事件资源均仍为前提。
新旧完整包在(97.11)上相同，不由删除拓扑输入推出物理模型类严格扩大，也不计数最少独立公理。
只给每个指定有限寄存器的结论；无限一致性、其它类型的实际编码／解码、有限字的长度或效率、
控制参数的物理时钟、能量单位和经验来源均不由这些关系取得。
第96章的低余维 ROG／$\mathrm G_2$ 条件既未被消费，也不由本章为其原一般载体供应二元寄存器资源。

这里的仓内综合是纯域穷尽到整个原基、以数学闭包替代输入拓扑、只在复合单位分支分类、
由原全实路径恢复精确控制，以及在两个原二体扇区排除反定向后恢复同一个原裸 $H$ 的组合。
有限凸分解、支撑超平面、Haar、紧矩阵群、分支轨道和反函数定理为成熟中间工具；
群分类和任意球面传递旋转子群事实分别由[MMMPA][MM97]及[Beardon][B97]持有。
后者将 Theorem 1.1 归于 Montgomery–Zippin，其 §2 给出本章所用不需闭性的直接证明。
原球计算、有限精确字、END、全有限原态两个包含和矩形事件／仪器消费者仍由95章与所引 Library 持有。

白话说，桌上保留的是整块原状态物体和所有合法尺：一盏纯灯的比较值，是所有必定确认它的尺能在目标上压到的最低值。
两盏灯若对每盏纯灯都恰好补成一，先找一把在对端真正归零的数学尺，就能把这个关系铺到所有有限混合；
原控制把最小尺带遍纯灯，唯一到顶和支撑面的关系迫使外壳没有混点，数学平均只负责找中心，整块物体才成为实心球。
真实种子菜单与原拉回按钮仍须在手。把这些球接成原寄存器以后，真实连续耦合、完整产品读数和整条旁观者合同选出三维，
实际有限字先取得两体控制，再检验原单元手里是否夹着反射；两个扇区都不允许它，原精确传递遂使同一只手拥有全部三维旋转。
预先可用的端点丢弃随后排除反向扇区，有限图把控制传开；逐事件的真实参考、预算、记录及辅助／指针／丢弃才接上通道和仪器。
交换两盏灯在比较式中的位置只交换同一个数的两个参数，不能据此交换两次实际测量的先后或断言后态相同。证毕。

[MM97]: https://arxiv.org/pdf/1111.4060v4
[B97]: https://doi.org/10.4153/S0008439526101696
[W97]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf

## 追加锚（本行以下为增补区）

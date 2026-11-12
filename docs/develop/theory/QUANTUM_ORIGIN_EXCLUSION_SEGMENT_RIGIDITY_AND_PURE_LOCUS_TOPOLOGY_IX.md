# QUANTUM ORIGIN: EXCLUSION SEGMENT RIGIDITY AND PURE LOCUS TOPOLOGY IX

**约定 114.0（卷间编号）。** 未另注卷名的107—113章及相应条目均指[第八卷][Q114VIII]；
114章属于本卷，式号以IX114为前缀。所有原域、完整球及原单位仍按各条目明确列出的前件使用。

## 114. 纯端点互惠的严格暴露、排除三球刻度与有限正延拓预算

**定义 114.1（同一个原全态与全效应域）。** 沿用107.1、109.1及112.1的非零有限维实空间 $V$、
闭尖生成凸锥 $C$ 和在 $C\setminus\{0\}$ 上严格正的泛函 $u$。始终取

$$
\begin{gathered}
C^{\ast}=\{f\in V^{\ast}:f(c)\ge0\ (c\in C)\},\qquad
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\\
\mathcal E=[0,u]_{C^{\ast}}
=\{f\in V^{\ast}:0\le_C f\le_C u\},\\
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\}.
\end{gathered}
\tag{IX114.1}
$$

第一个参数 $p$ 是原纯点；第二个参数 $x$ 遍历整个原 $K$，包括全部混态。
$K$ 是整个归一基，$P$ 是全部极点，最小化使用整个原确认族 $F_p$。
$H(p,q)$ 表示原 $K$ 中包含 $p,q$ 的最小面。所比较的条件为

$$
\begin{aligned}
\mathrm{PR}:&\quad \forall p,q\in P:\ T_p(q)=T_q(p),\\
\mathrm{EB}_m:&\quad \forall p\in P:\ D_p\simeq_{\mathrm{aff}}B^m
\quad(m\ge1\text{ 为固定整数}),\\
\mathrm{Pair}_{\perp}:&\quad
\forall p,q\in P:\ T_p(q)=0\ \Longrightarrow\ H(p,q)\ne K,
\end{aligned}
\tag{IX114.2}
$$

其中 $B^m$ 是整个闭欧氏单位球，$\mathrm{EB3}$ 指 $\mathrm{EB}_3$。
只找到若干三球零面、直径或纯点子集，不满足这个完整纤维条件。
$p\perp q$ 简记 $T_p(q)=0$。

严格正性使 $K$ 紧：在 $C$ 与辅助单位球面的交上，$u$ 有严格正的最小值，
从而 $K$ 有界；闭性给紧性。$C$ 生成 $V$，所以 $K$ 线性张成 $V$，
且 $\operatorname{aff}K=\{u=1\}$。每个 $K$ 上的仿射泛函唯一齐次化为 $V^{\ast}$ 中的线性泛函。
取 $K$ 中的一组线性基，效应在这些基向量上的值都在 $[0,1]$，故 $\mathcal E$ 有界；
它又是闭集，因此紧。$F_p$ 非空且紧，全部最小值均达到。

此核对应[Landsman §1.3，式(1.4)—(1.9)][Q114L]的完整仿射效应最小确认构造，
两端记号作相应交换。PR只交换两个纯端点的数值比较，不是先后测量的交换律。
每张固定原效应都仿射；分别优化不同确认任务所得的比较函数，并不因此在整个 $K$ 上仿射。
本章不把W、least确认效应、共同内积、Jordan结构或面效应延拓作为前件。

**约定 114.2（既有完整球原面分类的复用）。** 在定义114.1的原域中，
若 $\mathrm{EB}_m$ 成立，下文援用[完整排除球原面分类，定理1.6][Q114Faces]的前两项，
作为本章推导的中间结果，不另列为新增数学结论。本处不要求PR。

前件逐项对应于同一个有限维实空间 $V$、闭尖锥 $C$、在 $C\setminus\{0\}$ 上严格正的 $u$
以及 $C$ 生成 $V$；其中的归一基、纯集及原效应分别就是完整的 $K$、$P$ 和 $\mathcal E$。
定义114.1中最小值达到，所以 $D_p$ 恰是该定理在整个原 $K$ 上以某张原确认效应取得零值的完整排除集，
而 $\mathrm{EB}_m$ 供应其完整非退化仿射球图。故前两项直接给出：
每个 $D_p$ 都是非单点紧凸暴露真面，且存在 $e_p\in F_p$ 使

$$
D_p=K\cap\ker e_p.
\tag{IX114.3}
$$

这个共同零确认结论亦见[原全效应凸排除集的共同零确认结论(OP4)][Q114OP4]，
其适用域并不限于多边形；这里不重复证明，也不由此取得全域least或单位预算延拓。
对任意非空真凸面 $A\subsetneq K$，分类直接给出 $A=\{r\}$ 或 $A=D_r$，其中 $r\in P$；
不预设 $A$ 闭，因而每个含至少两个点的真面恰为一张完整仿射 $m$ 球。
本处不使用该定理最后一项所需的“每对不同原纯点均生成真最小面”前件；
这个全对前件尚未取得，也不能用只量化原正交纯对的 $\mathrm{Pair}_{\perp}$ 代替。

下文还使用这一分类的初等推论。若面 $A$ 满足 $D_p\subseteq A\subsetneq K$，
则分类给 $A=D_r$；$D_p$ 是完整球 $D_r$ 的非单点面，所以 $D_p=D_r$。
因此每个 $D_p$ 都是极大真面。两个不同的这类面的非空交是二者的真面，
故只能为单点；单点面是原 $K$ 的纯点。
此外，任意这样的面 $F$ 都满足
$\operatorname{ext}F=P\cap F$，球面边界就是其中全部原纯点。

**定理 114.3（单侧端点互惠迫使原纯点严格暴露）。** 不要求任何 $\mathrm{EB}_m$。
固定 $p\in P$，若

$$
\forall x\in P:\qquad T_x(p)\ge T_p(x),
\tag{IX114.4}
$$

则存在 $h\in\mathcal E$，使 $K\cap\ker h=\{p\}$。
因此 $p$ 在整个原 $K$ 中暴露，$u-h$ 是仅在 $p$ 取值一的原确认效应。
特别地，PR使全部原纯点暴露。

证明。若 $K=\{p\}$，零泛函已在 $K$ 上暴露这个唯一点，结论直接成立。
以下设 $K$ 非单点。定义正锥及其原零效应截面

$$
\mathcal N_p=\{g\in C^{\ast}:g(p)=0\},\qquad
G_p=\mathcal N_p\cap\mathcal E.
\tag{IX114.5}
$$

$p$ 是相对边界点，支撑泛函经常数平移和齐次化后表明 $\mathcal N_p\ne\{0\}$。
取 $h\in\operatorname{ri}\mathcal N_p$，并重标定为 $\max_Kh=1$。
于是 $h(p)=0$、$0\le_C h\le_Cu$。
令 $U_p=\operatorname{span}\mathcal N_p$，在这个有限维空间选辅助范数。
相对内部给出 $\varepsilon>0$，使

$$
h+B_{U_p}(0,\varepsilon)\subseteq\mathcal N_p.
$$

$G_p$ 紧，故存在 $R<\infty$ 使 $\|g\|\le R$ 对全部 $g\in G_p$ 成立。
取 $c>R/\varepsilon$，便有 $h-g/c\in\mathcal N_p$，因此

$$
g\le_C ch\quad(g\in G_p),\qquad
1-T_p(y)=\max_{g\in G_p}g(y)\le ch(y)\quad(y\in K).
\tag{IX114.6}
$$

第二式使用了 $f\mapsto u-f$ 从 $F_p$ 到 $G_p$ 的双射。
这只是对所有零效应的统一标量控制；$ch$ 不必属于 $\mathcal E$，
没有由此取得一张least确认效应。

设 $Z=K\cap\ker h$ 非单点。选择仿射泛函 $\ell$，使

$$
\alpha=\max_Z\ell>\ell(p),\qquad \delta=\alpha-\ell(p)>0.
\tag{IX114.7}
$$

对每个正整数 $t$，令 $m_t=\max_K(\ell-th)$，
并在这个非空紧最大面中选择一个原纯点 $x_t$。
因为 $h|_Z=0$，有 $m_t\ge\alpha$，所以

$$
0\le t h(x_t)=\ell(x_t)-m_t\le\ell(x_t)-\alpha.
\tag{IX114.8}
$$

$\ell$ 有界先给 $h(x_t)\to0$。由 $K$ 紧，任意聚点都属于 $Z$。
式(IX114.8)又给 $\ell(x_t)\ge\alpha$，而每个聚点在 $Z$ 上的 $\ell$ 值不超过 $\alpha$。
若 $\ell(x_t)$ 不趋于 $\alpha$，可取一个始终偏离 $\alpha$ 的子列，
再取收敛子列，其聚点便违反这个上界。故

$$
\ell(x_t)\longrightarrow\alpha,\qquad
t h(x_t)\longrightarrow0.
\tag{IX114.9}
$$

这里的聚点无需是纯点，亦未使用 $P$ 闭或 $T$ 第一参数的连续性。

令 $n_t=\min_K(\ell-th)$、$\Delta_t=m_t-n_t$。
$\ell|_Z$ 非恒定，所以 $\Delta_t>0$。实际原效应

$$
e_t=\frac{\ell-th-n_tu}{\Delta_t}\in\mathcal E,\qquad
e_t(x_t)=1
\tag{IX114.10}
$$

确实属于 $F_{x_t}$，没有调用面上的未证延拓。
设 $A=\max_K\ell-\min_K\ell$。由 $0\le h\le1$，

$$
\Delta_t\le A+t,\qquad
1-e_t(p)=\frac{m_t-\ell(p)}{\Delta_t}\ge\frac{\delta}{\Delta_t}.
\tag{IX114.11}
$$

单侧假设只用于原纯点 $x_t$，给
$e_t(p)\ge T_{x_t}(p)\ge T_p(x_t)$。结合(IX114.6)、(IX114.9)—(IX114.11)，

$$
\begin{aligned}
0<\delta
&\le\Delta_t(1-e_t(p))\\
&\le\Delta_t(1-T_p(x_t))\\
&\le c\Delta_t h(x_t)
\le c(A+t)h(x_t)\longrightarrow0.
\end{aligned}
\tag{IX114.12}
$$

矛盾。因此 $Z=\{p\}$，而 $u-h$ 的值一集合恰为 $\{p\}$。证毕。

**推论 114.4（PR下全部原纯点的紧性）。** 在定义114.1的完整原域中，
PR蕴含 $P=\operatorname{ext}K$ 紧。本结论不要求EB3，也不以 $P$ 已闭为前件。

证明。单点基直接成立。其余情形由114.3，每个纯点有一张全域暴露确认效应。
选 $V$ 上范数，令

$$
L_0=\max_{f\in\mathcal E}\|f\|_{\ast}<\infty.
$$

每个固定的 $T_p$ 是一族具有共同Lipschitz常数 $L_0$ 的效应的最小值，
故对全部 $y,z\in K$，

$$
|T_p(y)-T_p(z)|\le L_0\|y-z\|.
\tag{IX114.13}
$$

设 $p_n\in P$、$p_n\to x\in K$，而 $x$ 非纯。
有限维紧凸集的有限纯点分解可写成

$$
x=\lambda r+(1-\lambda)y,\qquad
r\in P,\quad y\in K,\quad 0<\lambda<1,\quad x\ne r.
$$

置 $\varepsilon_n=L_0\|p_n-x\|$。对每个 $f\in F_{p_n}$，有 $f(x)\ge1-\varepsilon_n$。
固定原效应的普通仿射性与非负余量给

$$
\varepsilon_n\ge1-f(x)
=\lambda(1-f(r))+(1-\lambda)(1-f(y))
\ge\lambda(1-f(r)).
$$

这对整个 $F_{p_n}$ 成立，故 $T_{p_n}(r)\ge1-\varepsilon_n/\lambda$。
PR给 $T_r(p_n)=T_{p_n}(r)$；固定 $T_r$ 的(IX114.13)于是迫 $T_r(x)=1$。
但114.3给仅在 $r$ 取一的原确认效应 $e_r$，而 $x\ne r$，
所以 $T_r(x)\le e_r(x)<1$，矛盾。$P$ 因而闭于紧 $K$，故紧。
这里仿射的是每个固定 $f$，没有把各自最小化的比较函数当作全域仿射函数。证毕。

**定理 114.5（排除三球上严格正的共同刻度）。** 假设EB3与PR。
对任一完整排除面 $F=D_p$，选仿射同构 $b_F:B^3\to F$，记 $q_v=b_F(v)$。
存在唯一 $a_F$，满足

$$
0<a_F\le\frac12,\qquad
T_{q_v}(b_F(z))=1-a_F+a_F\,v\cdot z
\quad(v\in S^2,\ z\in B^3).
\tag{IX114.14}
$$

这包括球内全部混态 $z$，而不仅是球面。

证明。114.2保证球面点 $q_v$ 都是原纯点。任取 $f\in F_{q_v}$，在整个球上写
$f(b_F(z))=c+\ell\cdot z$。原效应界给 $0\le c+\ell\cdot z\le1$，所以

$$
1=c+\ell\cdot v\le c+\|\ell\|\le1.
$$

两次不等式均取等号，故 $\ell=a_fv$、$c=1-a_f$，其中 $a_f=\|\ell\|\ge0$。
球上最小值 $1-2a_f$ 非负，得到

$$
f(b_F(z))=1-a_f+a_f\,v\cdot z,\qquad 0\le a_f\le\frac12.
\tag{IX114.15}
$$

$F_{q_v}$ 紧，系数是限制效应的连续函数，故
$a(v)=\max_{f\in F_{q_v}}a_f$ 达到。
由于 $1-v\cdot z\ge0$ 对全部 $z\in B^3$ 成立，同一最大系数实现整个球上的原最小值：

$$
T_{q_v}(b_F(z))=1-a(v)(1-v\cdot z).
\tag{IX114.16}
$$

对不同 $v,w\in S^2$，PR给
$(a(v)-a(w))(1-v\cdot w)=0$；后一因子严格正，所以 $a(v)=a(w)$。
这确定唯一共同系数 $a_F$。更换仿射球坐标仅作正交变换，不改变它。

最后，114.3给一张仅在 $q_v$ 取一的原确认效应。
它在非单点球 $F$ 上不恒定，所以(IX114.15)中它的系数严格正；
$a_F$ 不小于该系数，故 $a_F>0$。
因此零刻度情形被严格排除：若 $a_F=0$，所有确认 $q_v$ 的原效应都会在整个 $F$ 上恒为一，
与上述全域暴露确认效应矛盾。这不是尚待实现的EB3加PR分支。
(IX114.14)只给 $T_{q_v}$ 在这张 $F$ 上的仿射性，并不将它延到整个 $K$。证毕。

**定理 114.6（达到的尖锐预算与整个面效应族的正提升）。** 在114.5的前件下，定义

$$
\begin{gathered}
h_v(b_F(z))=\frac{1+v\cdot z}{2}\quad(v\in S^2),\\
\beta_F(v)=
\inf\{M\ge0:\ \exists g\in V^{\ast},\
0\le_Cg\le_CMu,\ g|_F=h_v\}.
\end{gathered}
\tag{IX114.17}
$$

空集的下确界约定为 $+\infty$。则

$$
\beta_F(v)=\beta_F=\frac1{2a_F}\in[1,\infty),
\tag{IX114.18}
$$

且下确界实际达到。每个非负仿射 $k:F\to[0,\infty)$ 都有原锥上的正线性延拓。
对全部面效应，其共同最优预算准确为

$$
\sup_{\,k\in\operatorname{Aff}(F),\ 0\le k\le1_F}
\ \inf_{\substack{g\in C^{\ast}\\g|_F=k}}\max_Kg
=\beta_F<\infty.
\tag{IX114.19}
$$

证明。先取 $g\in C^{\ast}$，$g|_F=h_v$，令 $M=\max_Kg$。
$g(q_v)=1$，故 $M\ge1$，且 $e=u-g/M$ 是整个原 $\mathcal E$ 中的效应。
它确认反极点 $q_{-v}$，在 $F$ 上的系数为 $1/(2M)$。
按114.5的最大系数定义，$1/(2M)\le a_F$，所以

$$
M\ge\frac1{2a_F}.
\tag{IX114.20}
$$

反过来，取在 $q_{-v}$ 达到系数 $a_F$ 的原确认效应 $e_{-v}$，定义

$$
g_v=\frac{u-e_{-v}}{2a_F}.
\tag{IX114.21}
$$

它在原 $C$ 上非负，满足 $g_v|_F=h_v$，
且 $g_v\le_Cu/(2a_F)$。结合(IX114.20)，其最大值恰为 $1/(2a_F)$；
这证明预算有限、与方向无关且实际达到。

任意非负仿射面函数可写成 $k(b_F(z))=c+b\cdot z$，其中 $c\ge t=\|b\|$。
若 $t=0$，直接以 $cu$ 延拓。若 $t>0$，令 $v=b/t$，则

$$
k=(c-t)1_F+2t\,h_v,\qquad
\widetilde k=(c-t)u+2t\,g_v\in C^{\ast}.
\tag{IX114.22}
$$

因此任意非负面函数都取得实际正延拓。若进一步 $k\le1_F$，则 $c+t\le1$、
$2t\le1$。写 $B=\beta_F\ge1$，所得延拓满足

$$
0\le_C\widetilde k
\le_C(c-t+2tB)u,\qquad
c-t+2tB=(c+t)+2t(B-1)\le B.
\tag{IX114.23}
$$

故 $B$ 对整个面效应族共同可用；$h_v$ 本身要求预算 $B$，给出(IX114.19)的锐性。
特别地，

$$
\{f|_F:f\in\mathcal E\}
=[0,1_F]_{\operatorname{Aff}(F)}
\quad\Longleftrightarrow\quad
a_F=\frac12
\quad\Longleftrightarrow\quad
\beta_F=1.
\tag{IX114.24}
$$

正提升逐个效应给出；尚未得到保持原单位的正线性延拓算子，
也不能将分别取得的延拓自动视为效应和为 $u$ 的联合测量。证毕。

**推论 114.7（所有锥面的正限制满射与niceness）。** 在EB3加PR下，原 $C$ 的每个面都暴露。
对每个锥面 $L\unlhd C$，以同一环境对偶空间定义

$$
L^\perp=\{\ell\in V^{\ast}:\ell|_L=0\},\qquad
L^{\ast}=\{\ell\in V^{\ast}:\ell(x)\ge0\ (x\in L)\}.
$$

则有准确恒等式

$$
C^{\ast}+L^\perp=L^{\ast}\qquad(L\unlhd C).
\tag{IX114.25}
$$

所以所有这些和都闭，$C$ 是facially dual complete，亦称nice。

证明。非零真锥面与归一基的非空真面对应。
114.2处理所有非单点基面，114.3处理纯单点基面，因此每个非零真锥面都由同一原正泛函暴露。
零面由严格正的 $u$ 暴露，整个 $C$ 由零泛函暴露。

显然 $C^{\ast}+L^\perp\subseteq L^{\ast}$。
若 $L=\operatorname{cone}F$ 且 $F$ 为一个排除三球，
任取 $\ell\in L^{\ast}$，则 $\ell|_F$ 是非负仿射函数。
114.6给 $g\in C^{\ast}$，$g|_F=\ell|_F$，所以 $\ell-g\in L^\perp$。
若 $L=\mathbb R_+p$ 为纯射线，令 $g=\ell(p)u\in C^{\ast}$，同样有 $\ell-g\in L^\perp$。
$L=\{0\}$ 时两侧均为 $V^{\ast}$；$L=C$ 时两侧均为 $C^{\ast}$。
由114.2的面分类，这穷尽全部锥面，证明反向包含。

$L^{\ast}$ 本身闭，所以(IX114.25)确实给出niceness。
这是[Pataki，arXiv:1202.4043v4，Theorem 2，PDF pp.8—9][Q114P]所讨论的面上正限制性质；
该文Theorem 3及Corollary 1（PDF pp.10—11）给出它与面暴露的关系及相应条件。
这里的恒等式和面暴露均由原模型直接推出，并未把文献中的一般性质另作公理。
有限正延拓不供应 $\beta_F=1$，也不供应同一个全局自对偶内积或锥的perfection。证毕。

**定理 114.8（原Pair、共同正交点与单位饱和的等价）。** 在EB3加PR下，
设 $p,q\in P$、$p\perp q$，令 $F=D_p$、$q=b_F(v)$，其中 $v\in S^2$。
则

$$
\begin{aligned}
H(p,q)\ne K
&\ \Longleftrightarrow\ D_p\cap D_q\ne\varnothing\\
&\ \Longleftrightarrow\ a_F=\frac12
\ \Longleftrightarrow\ \beta_F=1.
\end{aligned}
\tag{IX114.26}
$$

这些条件成立时，共同正交纯点唯一，准确为

$$
r=b_F(-v),\qquad D_p\cap D_q=\{r\},\qquad H(p,q)=D_r.
\tag{IX114.27}
$$

因此在完整原域中，

$$
\mathrm{Pair}_{\perp}
\ \Longleftrightarrow\
\forall p\in P:\ a_{D_p}=\frac12
\ \Longleftrightarrow\
\forall p\in P:\ \beta_{D_p}=1.
\tag{IX114.28}
$$

证明。首先，原效应的补已经给出零对称，不需要PR：
若 $f(p)=1$、$f(q)=0$，则 $(u-f)(q)=1$、$(u-f)(p)=0$，所以

$$
T_p(q)=0\quad\Longleftrightarrow\quad T_q(p)=0
\qquad(p,q\in P).
\tag{IX114.29}
$$

$p\ne q$，因为 $T_p(p)=1$。若 $H(p,q)$ 为真面，它含两个不同点，
114.2给 $H(p,q)=D_s$，其中 $s\in P$。
$p,q\in D_s$ 与零对称给 $s\in D_p\cap D_q$。

反之，$D_p\ne D_q$，因为 $q\in D_p$ 而 $q\notin D_q$。
若二者交非空，114.2给它恰为某个原纯单点 $\{r\}$。
零对称给 $p,q\in D_r$，故 $H(p,q)\subseteq D_r\subsetneq K$。
还须确定等号：$H(p,q)$ 是非单点真面，所以 $H(p,q)=D_s$；
它包含于 $D_r$ 且含 $p,q$ 两个不同点，而两个不同球面至多交于一个点，
于是 $D_s=D_r$，即 $H(p,q)=D_r$。

由于纯 $q\in F$ 位于 $F$ 的球面，114.5对完整球给

$$
D_p\cap D_q=
\{b_F(z):z\in B^3,\ 1-a_F+a_Fv\cdot z=0\}.
\tag{IX114.30}
$$

当 $0<a_F<1/2$ 时，左式中的标量最小值 $1-2a_F$ 严格正，故交为空。
当 $a_F=1/2$ 时，零值要求 $v\cdot z=-1$；
$\|v\|=1$、$\|z\|\le1$ 迫 $z=-v$，故交恰为 $\{b_F(-v)\}$。
再用114.6的预算公式，得到(IX114.26)—(IX114.27)。
对所有原正交纯对量化便得(IX114.28)；
反向检验每个 $D_p$ 时可任取其球面上的 $q$，所以没有遗漏任何排除面。
此处只确定三点两两原正交；联合测量将由下面明确进入的W支路承担。证毕。

**推论 114.9（单位饱和后准确接入112.8）。** 在同一个原域中，下列候选包

$$
\mathrm{EB3}+\mathrm{PR}
+\bigl(\forall p\in P:\beta_{D_p}=1\bigr)
\tag{IX114.31}
$$

等价于同原锥、同原单位的复三能级表示：
存在实线性双射 $\Phi:H_3(\mathbb C)\to V$，满足

$$
\Phi(\operatorname{Herm}_+(\mathbb C^3))=C,\qquad
u(\Phi X)=\operatorname{tr}X.
\tag{IX114.32}
$$

它给 $\dim_{\mathbb R}V=9$ 及112.8的完整静态态、效应、Born和有限POVM字典。
这不是由EB3加PR单独得到的复型结论。

证明。先用114.8取得原 $\mathrm{Pair}_{\perp}$。
此时才由112.1的定义取得
$\mathsf W=\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp}$；
EB3同时供应 $\mathrm{UniformEB}_{\ge2}$ 中的共同维数 $d=3$。
故112.8可在同一 $C,u,K,P,\mathcal E$ 上直接应用，得到(IX114.32)。
不再要求G、$\mathrm{TFD}_{3,\exists}$、TFD3、TRI2或九维作为额外前件。
W所供应的同域joint、least与后续Jordan桥都是进入该分支后的后果，
并未在114.2—114.8中预支。

准确的静态范围是(VIII112.30)：全部原归一态对应全部迹一PSD矩阵，
全部原纯态对应全部秩一投影，整个原效应区间对应全部 $0\preceq E\preceq I_3$；
原评价为 $\operatorname{tr}(E\rho)$，纯—纯读数为 $|v^{\ast}w|^2$，
任意有限原数学测量准确对应 $E_j\succeq0$、$\sum_jE_j=I_3$。
同一个双射保持原凸混合、效应补与效应和，未缩减原态或效应域。

反向由112.8的同锥同单位字典，完整排除集全为三球，纯比较由迹配对互惠；
任一纯正交对可补成三个正交秩一投影，故原Pair成立，
再用114.8得到全部单位饱和。
所以(IX114.31)只是已有校准几何候选的等价表述，
不是新增的独立公理减少或最少公理数结论。
112.9中全有限复合层级、实际事件、仪器、物理时间与 $\hbar$ 的各自条件和全称量词仍完整保留：
单体静态字典不供应纠缠联合域、旁观者正性、实际实现或时钟。证毕。

**定理 114.10（固定球维数至少二时的无facet障碍）。** 在定义114.1的原域中，
设某个固定整数 $m\ge2$ 满足 $\mathrm{EB}_m$，不要求PR。则

$$
\dim\operatorname{aff}K\ge m+2,
\qquad K\text{ 没有余维一面}.
\tag{IX114.33}
$$

特别地，EB3已经蕴含 $\dim\operatorname{aff}K\ge5$ 及无facet。

证明。记 $d=\dim\operatorname{aff}K$，在该仿射空间中看 $K$ 的内部与边界。
114.2的证明对固定 $m$ 适用，所以所有非单点真面的维数恰为 $m$，
且不同这类面至多交于一个纯点。
存在一个 $m$ 维真面先给 $d\ge m+1$。反设 $d=m+1$；
于是这些非单点真面恰为facets，记其全体为 $\mathscr F$。

先证明每个 $F\in\mathscr F$ 的相对内部是 $\partial K$ 中的开集。
取 $x\in\operatorname{ri}F$，在其支撑超平面内取以 $x$ 为中心的小闭盘，整个盘仍在 $F$ 中，
再取 $y\in\operatorname{ri}K$。这个盘与 $y$ 的凸包是包含于 $K$ 的满维小锥体。
把 $x$ 的邻域取得足够小，支撑超平面内侧、离平面为正距离的所有邻域点
都落在该小锥体的内部，因而在 $\operatorname{ri}K$ 中；
平面上的邻域点则仍在 $\operatorname{ri}F$ 中，平面外侧不属于 $K$。
因此这个邻域与 $\partial K$ 的交包含于 $\operatorname{ri}F$，证得所需开性。

不同facets的相对内部两两不交，而 $\partial K$ 第二可数，
所以非空开集族 $\{\operatorname{ri}F:F\in\mathscr F\}$ 至多可数。
例如在每个开集内选一个可数拓扑基元素；不交性使所选基元素互异。
故 $\mathscr F$ 至多可数。

固定一个 $F\in\mathscr F$，考虑邻面映射

$$
\nu_F:\operatorname{ext}F\longrightarrow\mathscr F,\qquad q\longmapsto D_q.
\tag{IX114.34}
$$

它只能单射或常值。为证此事，设不同 $q,r\in\operatorname{ext}F$ 满足
$D_q=D_r=G$。对任意 $s\in\operatorname{ext}G$，
原补效应所给的零对称(IX114.29)迫 $q,r\in D_s$。
于是 $F\cap D_s$ 含两个不同点，114.2迫 $D_s=F$。
再取任意 $t\in\operatorname{ext}F$，对所有这样的 $s$ 再用零对称，
有 $\operatorname{ext}G\subseteq D_t$，故 $G\subseteq D_t$；
极大性给 $D_t=G$。这说明只要有一次重复，整个 $\nu_F$ 就恒为 $G$。

由于 $m\ge2$，$\operatorname{ext}F\simeq S^{m-1}$ 不可数；
而 $\mathscr F$ 可数，$\nu_F$ 不可能单射，故恒定。
将其值记为 $F^\dagger$。刚才的证明同时给

$$
(F^\dagger)^\dagger=F.
\tag{IX114.35}
$$

若不同 $F,H\in\mathscr F$ 相交，交点由114.2为原纯点 $q$，
于是 $D_q=F^\dagger=H^\dagger$，对合性又迫 $F=H$，矛盾。
所以所有facets两两不交。

它们还覆盖整个 $\partial K$。任意边界点 $x$ 属于一个非空支撑真面 $A$；
若 $A$ 非单点，114.2给 $A\in\mathscr F$。
若 $A=\{x\}$，则 $x=p$ 为原纯点；
在完整 $D_p$ 的球面取原纯 $q$，零对称给 $p\in D_q\in\mathscr F$。
故 $\partial K$ 被至多可数个两两不交的非空闭facet覆盖。
这个分拆非平凡：若 $q\in\operatorname{ext}F$，则 $q\notin D_q=F^\dagger$，
所以 $F^\dagger\ne F$。

$K$ 是 $d$ 维凸体，$d=m+1\ge3$；
从内部点作径向参数化可知 $\partial K$ 同胚于 $S^{d-1}$，是紧连通欧氏集合。
有限的非平凡闭分拆直接违反连通性；
无限可数的两两不交非空闭分拆则违反
[Sierpiński连续统定理，原刊p.300、扫描第1页][Q114Si]。
因此 $d=m+1$ 不可能，得到 $d\ge m+2$。
现在若有facet，其维数为 $d-1\ge m+1$，但114.2规定非单点真面的维数只能为 $m$，矛盾。
这给出无facet结论。证明使用了可数性、常值邻面映射、对合与不交覆盖，
最后才应用连续统定理，不能由Baire定理单独代替。证毕。

$m\ge2$ 的限制不能删去。[原奇多边形应用(OP2)—(OP3)][Q114Polygon]
在同一完整原域实现了 $\mathrm{EB}_1+\mathrm{PR}$ 而所有纯零对失败Pair；
该文(OP7)—(OP8)还给五边形面效应的锐正延拓预算为黄金比，大于一。
这些已给出的原域计算说明一维边界确有有限超单位预算，
并不构成整个排除集为三球的模型，也不代替114.8所留下的三球饱和义务。

**命题 114.11（矩阵加厚的整个排除集是两个三球之并）。** 固定 $0<t<1$，令

$$
\begin{gathered}
V_t=\operatorname{Herm}_3(\mathbb C),\qquad
K_t=\{X\in V_t:0\preceq X\preceq I,\ \operatorname{tr}X=1+t\},\\
C_t=\operatorname{cone}K_t,\qquad
u_t(X)=\frac{\operatorname{tr}X}{1+t},\qquad
p=\operatorname{diag}(1,t,0).
\end{gathered}
\tag{IX114.36}
$$

这个载体满足定义114.1的有限维锥基条件。以它的全部原效应定义比较，
$p$ 是原纯点，其完整确认族在 $K_t$ 上恰为

$$
f(X)=1-A(1-X_{11})-BX_{33},\qquad
A,B\ge0,\quad A+B\le1.
\tag{IX114.37}
$$

因此对所有原归一 $X\in K_t$，

$$
T_p(X)=\min\{X_{11},\,1-X_{33}\},\qquad
D_p=F_1\cup F_2,
\tag{IX114.38}
$$

其中

$$
F_1=\{X\in K_t:X_{11}=0\},\qquad
F_2=\{X\in K_t:X_{33}=1\}.
\tag{IX114.39}
$$

每个 $F_i$ 都是完整仿射三球，但整个 $D_p$ 非凸，所以此载体失败EB3。

证明。$K_t$ 紧，且在迹超平面有内部点 $(1+t)I/3$。
故其锥生成 $V_t$；归一基紧且远离零，锥闭；
非零锥元素有严格正迹，故锥尖且 $u_t$ 严格正，归一基准确为 $K_t$。

先证 $p$ 纯。若 $p=\lambda X+(1-\lambda)Y$，$X,Y\in K_t$、$0<\lambda<1$，
则 $X_{11}=Y_{11}=1$、$X_{33}=Y_{33}=0$。
半正定矩阵的零对角元使对应行列为零：
对 $X,Y$ 的第三行列如此，对 $I-X,I-Y$ 的第一行列亦如此。
所以所有非对角项均为零，迹约束又使第二对角元为 $t$；
于是 $X=Y=p$。

原确认效应 $f$ 在 $p$ 达到全局最大值一。写其仿射限制为
$f(X)=\operatorname{tr}(HX)+b$，其中 $H$ Hermitian，常数可用迹约束吸收入线性泛函。
在完整酉轨道 $UpU^{\ast}\subseteq K_t$ 上的一阶极值条件给 $[H,p]=0$。
$1,t,0$ 两两不同，故 $H$ 在这些坐标中对角化。
再分别交换第一、第二特征方向以及第二、第三特征方向，
最大性给 $(h_1-h_2)(1-t)\ge0$、$(h_2-h_3)t\ge0$。
因此 $h_1\ge h_2\ge h_3$。

令 $A=h_1-h_2\ge0$、$B=h_2-h_3\ge0$。
代入迹约束及 $f(p)=1$，恰得(IX114.37)的表达式。
在反序原态 $\operatorname{diag}(0,t,1)$ 上的非负性迫 $A+B\le1$。
反之，若这三个系数条件成立，整个 $K_t$ 上都有
$0\le1-X_{11}\le1$、$0\le X_{33}\le1$，
所以 $1-A-B\le f(X)\le1$，确为原确认效应。
这证明整个确认族的必要性与充分性。

对系数三角形的三个顶点 $(0,0),(1,0),(0,1)$ 最小化，得
$\min\{1,X_{11},1-X_{33}\}$；因后两项已在 $[0,1]$，得到(IX114.38)。
非负性同时给整个零集的并集描述，包括全部混态。

令 $\mathcal D_2=\{\rho\in\operatorname{Herm}_2(\mathbb C):\rho\succeq0,\operatorname{tr}\rho=1\}$
为完整二阶密度矩阵体。$X_{11}=0$ 迫第一行列为零，余下块的迹为 $1+t$，
且在 $[0,I_2]$ 内；其最小特征值至少为 $t$，故

$$
F_1=\{\,0\oplus[tI_2+(1-t)\rho]:\rho\in\mathcal D_2\,\}.
\tag{IX114.40}
$$

$X_{33}=1$ 则迫第三方向与其余块解耦，剩余块非负且迹为 $t$，所以

$$
F_2=\{\,t\rho\oplus1:\rho\in\mathcal D_2\,\}.
\tag{IX114.41}
$$

$0<t<1$ 保证两个映射都非退化。
用完整Pauli坐标 $\rho=(I_2+z\cdot\sigma)/2$，$\rho\succeq0$ 等价于 $\|z\|\le1$，
故两者确为完整三球。
但取实际原态

$$
X=\operatorname{diag}(0,1,t)\in F_1,\qquad
Y=\operatorname{diag}(t,0,1)\in F_2,
$$

其原中点满足

$$
T_p\!\left(\frac{X+Y}{2}\right)
=\min\left\{\frac t2,\frac{1-t}{2}\right\}>0.
\tag{IX114.42}
$$

所以整个 $D_p$ 不凸，不能为一个完整三球。
这排除了该矩阵加厚路线；它不是EB3加PR的反模型。证毕。

**约定 114.12（有限预算、校准与静态字典的准确范围）。** 在EB3加PR下，
114.3—114.7已给全域暴露的原纯点、紧的全部原纯集、所有面的暴露与niceness，
以及每张完整排除三球上严格正的共同刻度和实际达到的有限正延拓预算。
剩余义务准确为

$$
\boxed{\quad
\mathrm{EB3}+\mathrm{PR}
\ \stackrel{?}{\Longrightarrow}\
\forall p\in P:\ \beta_{D_p}=1
\quad}
\tag{IX114.43}
$$

其中 $\beta_F\ge1$ 已由114.6证明。这一蕴含及其否定均未在上述推导中取得；
等价的 $\mathrm{EB3}+\mathrm{PR}\Rightarrow\mathrm{Pair}_{\perp}$ 仍待证明或同域反例。
条件性的两个数值区域是

$$
\begin{array}{c|c|c}
\text{球刻度}&\text{球内最小确认读数}&\text{锐正延拓预算}\\ \hline
0<a_F<1/2&1-2a_F>0&1<\beta_F<\infty\\
a_F=1/2&0&\beta_F=1
\end{array}
\tag{IX114.44}
$$

这只是参数判据，不是第一行有原锥实现的存在性证明。
$a_F=0$ 或 $\beta_F=\infty$ 已被114.3与114.5排除，不能再列为该前件下的可容许分支。
无facet及矩阵例子分别排除具体路线，未排除所有高余维的有限超预算实现。

[Landsman，quant-ph/9603005v2，Definition 6，PDF p.10／印刷p.10][Q114L]
的two-sphere性质已包含校准核 $(1+\cos\theta)/2$，
并置于其well-behaved转移概率框架中；
§1.3式(1.4)—(1.9)（PDF p.5／印刷p.5）用于这里的核、补效应零对称及概率一分离的对应。
不能仅从未校准的(IX114.14)输入该校准条件，
也没有从PR获得其极大正交集的概率和规则。
114.3的单侧暴露蕴含与114.5—114.8的原球预算推导，是这里给出证明的凸几何推导，
不归为该文已经陈述的定理。

[Pataki，arXiv:1202.4043v4][Q114P]供应114.7所用的nice／面正限制术语和一般关系，
不供应单位预算；[Sierpiński原文][Q114Si]的连续统定理由114.10实际消费。
原[多边形应用][Q114Polygon]中的OP4及一维边界计算按其既有证明复用。
上述组合推导是普通有限维数学，不宣称文献原创、内核验证或独立公理的最小性。
只有(IX114.43)的饱和条件另行成立后，才有114.9所述同原域完整静态复三能级字典；
全有限复合、仪器和物理动力学仍按112.9各自的原合同承担。

上述结论的中文图景是：互惠首先使每个纯点都有一项原效应测试，只有在该点，通过概率才为一。
其它原态的通过概率严格小于一，但仍可能通过；这不表示一次测试就能完全区分该点与其它态。
每张完整排除三球上的所有方向又共用一把刻度尺；
确认北极的最优原比较在北极为一，在南极为 $1-2a_F$，
其中 $0<a_F\le1/2$，这把尺不能完全失去刻度。
球内任何合法的非负仿射按钮，都能逐个接回整个原锥并保持正性；
对全部零一面效应，共同且锐的有限代价是 $\beta_F=1/(2a_F)$。
尚缺的是让这些按钮仍守住原来的零到一单位预算。
预算恰为一时，南极读数才恰为零，原正交纯对才得到唯一第三个共同正交纯点；
此后进入W与全三球支路，112.8才供应完整静态量子字典。
这里的互惠始终只比较纯端点，完整球与原单位的校准条件不能从图景中删去。

[Q114Faces]: ../../../Blueprint/D5/S3/Quantum/Foundation/ExclusionBallFaces.md "完整排除球的共同暴露与全部原真凸面分类，定理1.6前两项；最后一项另需每对不同原纯点均生成真最小面。"
[Q114OP4]: ../../../Library/FiniteGeometry/janottagogolinbarrettbrunner2011polygon.md#4-a-convex-exclusion-set-has-a-common-original-zero-confirmer "原全效应凸排除集的共同零确认结论，OP4。"
[Q114Polygon]: ../../../Library/FiniteGeometry/janottagogolinbarrettbrunner2011polygon.md#odd-polygons-reciprocal-comparisons-original-faces-and-extension-budgets "奇多边形的原全域应用，OP2—OP8；一维球不代表三球。"
[Q114Si]: https://www.jstage.jst.go.jp/article/tmj1911/13/0/13_0_300/_article "W. Sierpiński, Un théorème sur les continus, Tohoku Mathematical Journal, First Series 13 (1918), 300–303；定理在印刷p.300／扫描第1页。"
[Q114P]: https://arxiv.org/pdf/1202.4043v4 "Gábor Pataki, On the connection of facially exposed and nice cones, arXiv:1202.4043v4；Theorem 2 PDF pp.8–9，Theorem 3 p.10，Corollary 1 p.11；J. Math. Anal. Appl. 400 (2013), 211–221，DOI 10.1016/j.jmaa.2012.10.033。"
[Q114L]: https://arxiv.org/pdf/quant-ph/9603005v2 "N. P. Landsman, Poisson spaces with a transition probability, arXiv:quant-ph/9603005v2；§1.3 (1.4)–(1.9) PDF p.5／印刷p.5，Definition 6 PDF p.10／印刷p.10；Rev. Math. Phys. 9 (1997), 29–58，DOI 10.1142/S0129055X97000038。"

[Q114VIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "原全态全效应域及107—113章的条件重构。"

## 追加锚（本行以下为增补区）

## 115. 整球极限二择、正则球丛与预算退化

**定义 115.1（整球参数、辅助拓扑与正则区域）。** 本章始终在定义114.1的同一个有限维实空间 $V$、闭尖生成锥 $C$、严格正单位 $u$ 上工作，并假设 $\mathrm{EB3}+\mathrm{PR}$。完整原域和比较函数明确为

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x)\ (x\in K),\qquad
D_p=\{x\in K:T_p(x)=0\}.
\end{gathered}
$$

在 $V$ 上固定一个辅助欧氏范数 $\|\cdot\|$（并限制到 $\ker u$），只用于有限维拓扑、Hausdorff 距离和长度；它不是由模型取得的物理内积。对 $p\in P$ 写

$$
\mathcal D(p)=D_p,\qquad d(p)=\operatorname{diam}_{\|\cdot\|}D_p,\qquad
a(p)=a_{D_p},\qquad \beta(p)=\beta_{D_p}=\frac1{2a(p)}.
\tag{IX115.1}
$$

这里 $a_{D_p}$ 和 $\beta_{D_p}$ 是114.5—114.6在该一张完整排除三球上定义的量；只在同一球内使用其共同系数，不对不同球宣称 $a$ 相等。若 $F=D_p$，取任一仿射球坐标 $b_F:B^3\to F$，则

$$
T_{b_F(v)}(b_F(z))=1-a(p)+a(p)\,v\cdot z
\qquad(v\in S^2,\ z\in B^3).
\tag{IX115.2}
$$

令 $d_H$ 为该欧氏范数诱导的 Hausdorff 距离，并定义

$$
S_j=\{p\in P:d(p)\ge 1/j\},\qquad
\mathcal R=\bigcup_{j\ge1}\operatorname{int}_P S_j,
\qquad \Sigma=P\setminus\mathcal R.
\tag{IX115.3}
$$

正则区的两个全纤维空间记为

$$
\mathscr B_{\mathcal R}=\{(p,x)\in\mathcal R\times K:x\in D_p\},
\qquad
\mathscr Z_{\mathcal R}=\{(p,q)\in\mathcal R\times P:q\in D_p\},
\tag{IX115.4}
$$

并取它们的第一投影到 $\mathcal R$。第二个空间保留每个完整纤维 $P\cap D_p$ 的全部端点；其第二坐标可以属于 $\Sigma$。

**约定 115.2（对114结果的准确复用）。** 下文不重证114.2—114.6。具体复用内容是：每个 $D_p$ 都是一个非单点、紧、暴露的完整仿射三球；其球面恰为 $P\cap D_p$；由114.4，$P$ 是紧集，并且存在

$$
L=\max_{f\in\mathcal E}\|f\|_*<\infty,
\qquad
|T_p(x)-T_p(y)|\le L\|x-y\|\quad(p\in P,\ x,y\in K).
\tag{IX115.5}
$$

这里 $L>0$：每个三球含有不同的纯点，而114.5在对径端点上给出严格小于一的比较值。

由114.5，$0<a(p)\le1/2$ 且(IX115.2)在整球 $B^3$ 上成立；由114.6，每个 $\beta(p)$ 都有限，且 $\beta(p)\ge1$。这里仅使用这些已发布结果，不把它们改写成新的证明或前件。

**定理 115.3（纯端点间隙、三球厚度与预算的定量控制）。** 对任意 $p,p',q,q'\in P$，有

$$
|T_p(q)-T_{p'}(q')|
\le L\bigl(\|p-p'\|+\|q-q'\|\bigr).
\tag{IX115.6}
$$

对 $0<\varepsilon\le\operatorname{diam}P$，定义

$$
\gamma(\varepsilon)=
\min_{\substack{r,s\in P\\\|r-s\|\ge\varepsilon}}
\bigl(1-T_r(s)\bigr).
\tag{IX115.7}
$$

则 $\gamma(\varepsilon)>0$。若 $F=D_p=c+A B^3$，其最大和最小半轴分别为 $s_{\max}(F)$ 与 $s_{\min}(F)$，则

$$
\operatorname{diam}F\ge\varepsilon
\quad\Longrightarrow\quad
\beta_F\le\frac1{\gamma(\varepsilon)},
\qquad
s_{\min}(F)\ge\frac{\gamma(\varepsilon)}{2L}.
\tag{IX115.8}
$$

证明。由PR，$T_p(q)=T_q(p)$。因此

$$
\begin{aligned}
|T_p(q)-T_{p'}(q')|
&=|T_q(p)-T_{q'}(p')|\\
&\le |T_q(p)-T_q(p')|+|T_q(p')-T_{q'}(p')|\\
&=|T_q(p)-T_q(p')|+|T_{p'}(q)-T_{p'}(q')|,
\end{aligned}
$$

再用(IX115.5)即得(IX115.6)。114.3给出对每个 $r$ 仅在 $r$ 取一的原确认效应 $e_r$；若 $r\ne s$，则 $e_r(s)<1$，从而
$T_r(s)\le e_r(s)<1$。集合
$\{(r,s)\in P\times P:\|r-s\|\ge\varepsilon\}$ 是紧集，(IX115.6)使 $1-T_r(s)$ 连续，所以(IX115.7)的最小值严格为正。

写 $F=c+A B^3$ 的奇异值为 $s_1\ge s_2\ge s_3>0$。取最大轴的对径端点 $x_+=c+Av$、$x_-=c-Av$，则 $\|x_+-x_-\|=2s_1=\operatorname{diam}F$。由(IX115.2)和(IX115.7)，当 $\operatorname{diam}F\ge\varepsilon$ 时
$2a_F=1-T_{x_+}(x_-)\ge\gamma(\varepsilon)$。再取最小轴的对径端点 $y_+=c+Aw$、$y_-=c-Aw$，由(IX115.5)和 $T_{y_+}(y_+)=1$，
$2a_F=1-T_{y_+}(y_-)\le L\|y_+-y_-\|=2Ls_3$。由于 $\beta_F=1/(2a_F)$，得到(IX115.8)。证毕。

**引理 115.4（原零关系的闭图）。** 若 $p_n\to p$、$x_n\to x$ 且 $x_n\in D_{p_n}$，则 $x\in D_p$。亦即

$$
\operatorname{Graph}(\mathcal D)=\{(p,x)\in P\times K:x\in D_p\}
\quad\text{是闭集},
\tag{IX115.9}
$$

并且 $\mathcal D$ 对 Hausdorff 拓扑上半连续，$d$ 上半连续。

证明。由 $x_n\in D_{p_n}$ 及最小值达到，取 $f_n\in\mathcal E$ 使
$f_n(p_n)=1$、$f_n(x_n)=0$。$\mathcal E$ 紧，取子列 $f_n\to f\in\mathcal E$。线性泛函在有限维空间上联合连续，故 $f(p)=1$、$f(x)=0$；于是 $T_p(x)=0$，即 $x\in D_p$，证明(IX115.9)。

若 $p_n\to p$，任一 Hausdorff 收敛子列 $D_{p_n}\to Q$ 的每个 $x\in Q$ 都可由 $x_n\in D_{p_n}$ 逼近，故由闭图 $Q\subseteq D_p$。这正是紧值映射的上半连续性；再由紧集上的 Hausdorff 收敛，$\limsup d(p_n)\le d(p)$，所以 $d$ 上半连续。证毕。

**定理 115.5（整球极限二择）。** 对任意 $p_n\to p$，每一个 Hausdorff 子列极限都恰为以下两者之一：

$$
D_{p_n}\longrightarrow D_p,
\qquad\text{或}\qquad
D_{p_n}\longrightarrow\{q\}\quad\text{其中 }q\in P\cap D_p.
\tag{IX115.10}
$$

证明。取任意具有 Hausdorff 极限的子列，写
$D_{p_n}=c_n+A_nB^3$。所有这些球包含在固定紧集 $K$ 内，所以中心 $c_n$ 与线性算子 $A_n$ 有界；再取子列使 $c_n\to c$、$A_n\to A$。由引理115.4，极限

$$
Q=c+A B^3\subseteq D_p.
\tag{IX115.11}
$$

每个 $c_n+A_nv$（$v\in S^2$）属于 $P$。114.4给 $P$ 闭，故
$c+Av\in P$。若 $A=0$，则 $Q=\{c\}$，且 $c\in P\cap D_p$，得到第二种情形。

设 $A\ne0$。此时 $\operatorname{diam}Q>0$，取 $0<\varepsilon<\operatorname{diam}Q$；对充分大的 $n$，$\operatorname{diam}D_{p_n}\ge\varepsilon$，由(IX115.8)其最小半轴统一下界为 $\gamma(\varepsilon)/(2L)>0$。因此 $A$ 满秩三，$Q$ 是一个三维椭球。其边界由 $c+Av$（$v\in S^2$）组成，全部属于 $P\cap D_p$；而114.2说明 $P\cap D_p=\partial D_p$。于是 $\partial Q\subseteq\partial D_p$，从而两者的仿射包相同：$\partial Q$ 的仿射包是 $\operatorname{aff}Q$，它被包含在 $\operatorname{aff}D_p$ 中，两个空间都为三维。

现在 $Q\subseteq D_p$ 且同处于三维仿射空间。若包含严格，则 $\operatorname{ri}D_p\setminus Q$ 非空；否则 $\operatorname{ri}D_p\subseteq Q$，取闭包会得到 $D_p\subseteq Q$。取 $x\in\operatorname{ri}Q$ 和 $y\in\operatorname{ri}D_p\setminus Q$。线段从 $x$ 向 $y$ 离开 $Q$ 的第一个点属于 $\partial Q$，而整条线段（除端点的无关情形外）位于 $\operatorname{ri}D_p$，这与 $\partial Q\subseteq\partial D_p$ 矛盾。因此 $Q=D_p$，得到第一种情形。证毕。

**定理 115.6（Baire正则区、全部连续点与局部预算）。** $S_j$ 闭，$\mathcal R$ 是 $P$ 的开稠密子集，$\Sigma$ 闭且无处稠密。并且 $\mathcal R$ 同时是以下三个映射的连续点集：

$$
\mathcal R
=\operatorname{Cont}(p\mapsto D_p)
=\operatorname{Cont}(p\mapsto a(p))
=\operatorname{Cont}(p\mapsto\beta(p)).
\tag{IX115.12}
$$

其中第一个映射取 Hausdorff 拓扑。对每个 $p\in P$，有局部预算的充要条件

$$
 p\in\mathcal R
\quad\Longleftrightarrow\quad
\exists\text{ 相对开邻域 }U\ni p,
\exists M<\infty,
\forall p'\in U:\ \beta(p')\le M.
\tag{IX115.13}
$$

因此 $\beta$ 在 $\mathcal R$ 的每个紧子集上一致有界。
此外，$a$ 在整个 $P$ 上半连续，$\beta$ 在整个 $P$ 上是下半连续的。

证明。由引理115.4，$d$ 上半连续，所以每个 $S_j=\{d\ge1/j\}$ 闭。114.2给每个 $d(p)>0$，故

$$
P=\bigcup_{j\ge1}S_j.
\tag{IX115.14}
$$

任意非空相对开集 $U\subseteq P$ 是局部紧 Hausdorff 空间，因而是 Baire 空间。闭集 $U\cap S_j$ 覆盖 $U$，所以某个 $U\cap S_j$ 在 $U$ 中有非空内点；这给出 $U\cap\operatorname{int}_P S_j\ne\varnothing$。故 $\mathcal R$ 稠密，而按定义它开；$\Sigma$ 因而闭且无处稠密。

若 $p\in\mathcal R$，存在邻域 $U$ 和 $j$ 使 $d(p')\ge1/j$（$p'\in U$）。对任意 $p_n\to p$，充分大时 $p_n\in U$，定理115.5的单点极限被排除，所有 Hausdorff 子极限均为 $D_p$，故 $D_{p_n}\to D_p$。反之，若 $D$ 在 $p$ 连续，直径是 Hausdorff 距离下的连续函数，且 $d(p)>0$，所以某邻域内 $d(p')\ge d(p)/2$，即 $p\in\mathcal R$。这证明 $\mathcal R$ 是整球映射的全部连续点。

在 $p\in\mathcal R$ 时，取任意 $p_n\to p$。对其中任一子列，再取中心和形状算子的收敛子列；由前段和定理115.5，极限椭球只能是 $D_p$，不能是单点。其任一固定球坐标的对径端点 $x_n,y_n$ 收敛到 $D_p$ 的一对对径纯点 $x,y$。由(IX115.2)和(IX115.6)，
$2a(p_n)=1-T_{x_n}(y_n)\to1-T_x(y)=2a(p)$。
所有子列的聚值都相同，故 $a(p_n)\to a(p)$；于是 $\beta(p_n)\to\beta(p)$。因此 $\mathcal R$ 包含于 $a,\beta$ 各自的连续点集。

对任意 $p_n\to p$，若定理115.5的子列极限是 $D_p$，同一对径端点的论证（不需要 $p\in\mathcal R$）给出 $a(p_n)\to a(p)$；若极限是单点，则定理115.3证明中的 $2a(p_n)\le Ld(p_n)$ 给出 $a(p_n)\to0$。因此 $a(p_n)$ 的每个聚值只能是 $a(p)$ 或 $0$，因而
$\limsup a(p_n)\le a(p)$。由 $\beta=1/(2a)$ 得
$\liminf\beta(p_n)\ge\beta(p)$，即得所述全域上半连续性与下半连续性。

若 $p\notin\mathcal R$，则对每个 $n$，$p\notin\operatorname{int}_P S_n$，可选
$p_n\in P$ 满足 $\|p_n-p\|<1/n$ 且 $d(p_n)<1/n$。定理115.3证明中的普遍最小轴估计
$2a(p_n)\le Ld(p_n)\to0$，所以 $a(p_n)\to0$、$\beta(p_n)\to+\infty$，而114.5—114.6给 $a(p)>0$、$\beta(p)<\infty$。故 $a$ 与 $\beta$ 在 $p$ 均不连续。

最后证明异常序列的完整见证。对每个 $n$ 选 $q_n\in P\cap D_{p_n}$；紧性给子列 $q_{n_k}\to q\in P$。由于 $\operatorname{diam}D_{p_{n_k}}\to0$，有 $D_{p_{n_k}}\to\{q\}$；由闭图(IX115.9)，$q\in D_p$。删去子列下标即得

$$
\forall p\in\Sigma\ \exists p_n\to p,\ \exists q\in P\cap D_p:
D_{p_n}\to\{q\},\quad a(p_n)\to0,\quad\beta(p_n)\to+\infty.
\tag{IX115.15}
$$

局部预算的正向由 $a$ 在 $\mathcal R$ 连续且 $a(p)>0$ 给出。反向若 $\beta\le M$ 在邻域 $U$ 上成立，则定理115.3证明中的普遍不等式 $2a(p')\le Ld(p')$ 给出
$ d(p')\ge1/(LM)$；于是 $p\in\operatorname{int}_P S_j$，其中取 $j>LM$。这证明(IX115.13)。在 $\mathcal R$ 上 $\beta$ 连续，故其在每个紧子集上达到有限最大值。证毕。

**定理 115.7（正则区的完整球丛与纯零球丛）。** 第一投影
$\mathscr B_{\mathcal R}\to\mathcal R$ 是局部平凡的 $B^3$ 丛，第一投影
$\mathscr Z_{\mathcal R}\to\mathcal R$ 是局部平凡的 $S^2$ 丛。第二个丛的总空间仍为完整的 $\{(p,q):q\in P\cap D_p\}$，不把 $q$ 限制在 $\mathcal R$ 内。

证明。令 $H_0=\ker u$，用辅助欧氏范数识别 $H_0$ 与其对偶。每个三球唯一有中心 $c(p)$，并有唯一的半正定形状算子 $Q(p)$，秩为三，使其支撑函数写成

$$
h_{D_p}(\xi)=\langle c(p),\xi\rangle+\sqrt{\langle Q(p)\xi,\xi\rangle}
\qquad(\xi\in H_0).
\tag{IX115.16}
$$

中心由支撑函数的奇部确定，$Q$ 由偶部平方确定。定理115.6已给 $p\mapsto D_p$ 在 $\mathcal R$ 上 Hausdorff 连续；有限维紧凸集的支撑函数随 Hausdorff 距离一致连续，所以 $c(p)$、$Q(p)$ 在 $\mathcal R$ 上连续。$Q(p)$ 恒秩三。固定 $p_0\in\mathcal R$，在 $Q(p_0)$ 的像空间中选三个线性无关的列；连续性保证同一个三阶子式在某邻域内不为零，Gram–Schmidt 给出该邻域上连续的等距标架
$U(p):\mathbb R^3\to\operatorname{ran}Q(p)$。

正平方根 $Q(p)^{1/2}$ 连续，且极分解说明
$D_p=c(p)+Q(p)^{1/2}U(p)B^3$。因此

$$
\Phi(p,z)=\bigl(p,\ c(p)+Q(p)^{1/2}U(p)z\bigr)
\tag{IX115.17}
$$

是从该邻域的 $\times B^3$ 到 $\mathscr B_{\mathcal R}$ 的连续双射；其逆映射由 $Q(p)^{-1/2}$ 在 $\operatorname{ran}Q(p)$ 上的逆和 $U(p)^*$ 连续给出，故是局部平凡化。由114.2，$P\cap D_p=\partial D_p$，所以将 $z$ 限制为 $S^2$ 即得到 $\mathscr Z_{\mathcal R}$ 的局部平凡化。证毕。

**定理 115.8（全域有限预算、整球连续与单位饱和的分界）。** 令
$\mathrm{UF}$ 表示存在一个有限常数 $M$ 使 $\beta(p)\le M$ 对全部 $p\in P$ 成立。则

$$
\mathrm{UF}
\quad\Longleftrightarrow\quad
\Sigma=\varnothing
\quad\Longleftrightarrow\quad
p\mapsto D_p\text{ 在整个 }P\text{ 上 Hausdorff 连续}
\quad\Longleftrightarrow\quad
\sup_{p\in P}\beta(p)<\infty.
\tag{IX115.18}
$$

证明。$\mathrm{UF}$ 与最后一个条件只是同一命题的两种写法。由定理115.6，整球映射的连续点集正是 $\mathcal R$，所以它在整个 $P$ 上连续当且仅当 $\mathcal R=P$，亦即 $\Sigma=\varnothing$。若 $\mathcal R=P$，定理115.6给 $\beta$ 在紧集 $P$ 上连续，故其上确界有限；反之若上确界为有限数，则 $\beta$ 在每个相对开邻域上都一致有界，(IX115.13)给每个 $p\in P$ 属于 $\mathcal R$，于是 $\mathcal R=P$。证毕。

**约定 115.9（本章结论的未决边界）。** 114.6已经给出每个单独排除三球的有限预算 $1\le\beta(p)<\infty$；本章新增的是正则区、极限二择和全域一致有限预算的等价条件。式(IX115.18)不把有限统一预算降为单位预算：由114.8，

$$
\forall p\in P:\ \beta(p)=1
\quad\Longleftrightarrow\quad
\mathrm{Pair}_{\perp},
\tag{IX115.19}
$$

而 $\mathrm{EB3}+\mathrm{PR}\Rightarrow\mathrm{Pair}_{\perp}$ 仍是未决界面。因而本章没有证明 $\Sigma$ 必为空，也没有构造具有异常点的实际塌缩模型；异常点的存在与不存在均未由这些推导决定。整球连续性只在 $\mathcal R$ 上得到，不能外推为全域连续；任何逐个面取得的正延拓也没有被提升为保持原单位的联合延拓。所有比较仍是原纯端点之间的PR比较，辅助欧氏范数只承担拓扑用途。在本章结论下，全域一致有限预算与单位饱和仍是两个不同的未证目标。

## 追加锚（本行以下为增补区）

## 116. 完整厚排除球的四纯态失败证书与端点剖面

**命题 116.1（EB下的有限原支撑与零维或整球端点）。** 取定义114.1的同一个非零有限维实空间 $V$、
闭尖生成凸锥 $C$、严格正单位 $u$、整个归一基 $K$、全部原纯点 $P=\operatorname{ext}K$
及整个原效应区间 $\mathcal E=[0,u]_{C^{\ast}}$。只要求完整厚球条件

$$
\forall s\in P\ \exists d_s\in\mathbb N,\ d_s\ge2:\qquad
D_s\simeq_{\mathrm{aff}}B^{d_s}.
\tag{IX116.1}
$$

各球的维数可以不同；$D_s$ 始终是对整个原 $K$、用整个原确认族定义的排除集。
本命题不附加PR、$\mathrm{Pair}_{\perp}$ 或任意不同纯对的最小面均为球的条件 $\mathrm B$。
固定 $p\in P$ 及 $F=D_p$，写

$$
\begin{gathered}
F=c+B_F,\qquad L(F)=\operatorname{lin}(F-F),\qquad
B_F=\{v\in L(F):|v|_F\le1\},\\
d=\dim F,\qquad m=\dim\ker u=\dim V-1.
\end{gathered}
\tag{IX116.2}
$$

这里 $|\cdot|_F$ 是这张完整仿射球的内在欧氏范数。
令 $\mathrm A(F)$ 表示每个 $|n|_F=1$ 的对径 $c+n,c-n$
都能由某张原 $h\in\mathcal E$ 分别取一和零。
若 $\mathrm A(F)$ 失败，则可在同一个 $F$ 中重新选取原纯对径 $q_*,r_*$，
以及 $\lambda>1$、$a,b\in K$ 和同一张 $e\in\mathcal E$，满足

$$
\lambda(q_*-r_*)=a-b,\qquad e(a)=1,\qquad e(b)=0.
\tag{IX116.3}
$$

记 $G(a),G(b)$ 为 $a,b$ 在原 $K$ 中的最小面，并记
$L(a)=\operatorname{lin}(G(a)-G(a))$、$L(b)=\operatorname{lin}(G(b)-G(b))$。
可以同时保证

$$
\begin{gathered}
a\in\operatorname{ri}G(a),\quad b\in\operatorname{ri}G(b),\quad
e|_{G(a)}=1,\quad e|_{G(b)}=0,\\
L(F)\oplus L(a)\oplus L(b)\subseteq\ker u.
\end{gathered}
\tag{IX116.4}
$$

每个端点的最小面只有下列准确选择：若端点纯，则为该原纯单点、维数零；
若端点混，则为某张完整原排除球 $D_s$，端点在其相对内部，维数为该球的整个 $d_s\ge2$。
因此存在 $x_1,x_2,y_1,y_2\in P$ 及 $\alpha,\beta\in[0,1]$，使

$$
\begin{aligned}
a&=\alpha x_1+(1-\alpha)x_2,\qquad
b=\beta y_1+(1-\beta)y_2,\\
\lambda(q_*-r_*)&=
\alpha x_1+(1-\alpha)x_2-\beta y_1-(1-\beta)y_2.
\end{aligned}
\tag{IX116.5}
$$

同一个原全单位效应 $e$ 在每个正权 $x_i$ 上取一，在每个正权 $y_j$ 上取零。
允许重复纯点与零权项；零权项不承担读数要求。
“至多四个”仅计 $a,b$ 的纯分解支撑，不把标签 $p,q_*,r_*$ 算入这个数。

若 $h_+=\dim G(a)$、$h_-=\dim G(b)$，则

$$
m\ge d+h_++h_-.
\tag{IX116.6}
$$

特别地，若所有完整排除球均为三球，则

$$
(h_+,h_-)\in\{(0,0),(0,3),(3,0),(3,3)\},\qquad
m\ge3+h_++h_-,
\tag{IX116.7}
$$

因而在所选实现中两端均混蕴含 $m\ge9$，即 $\dim V\ge10$。
纯端点分支仍保留，这个条件维数界没有把两端均混作为EB的后果。

反之，对同一原球 $F$ 的任意对径 $q,r$，只要存在 $\lambda>1$ 及(IX116.5)形状的
原纯态凸分解恒等式，就不存在原 $h\in\mathcal E$ 在 $q,r$ 分别取一和零。
这个反向障碍不另需假定分解支撑已具有共同饱和效应。

证明。先明确所复用的前件范围。
[VII103.2，式(VII103.4)—(VII103.5)][Q114FaceExhaustion]仅用完整 $\mathrm{EB}_{\ge1}$，
便给所有非空原真面恰为纯单点或整张 $D_s$，且每张 $D_s$ 为非点紧暴露极大真面。
本处(IX116.1)满足这一前件，毋须各 $d_s$ 相同。
于是 $\operatorname{ext}F=P\cap F$，球内对径均为原纯点。
[VII104.2的证明][Q114LocalBall]还说明，任意两个不同的球面点在原 $K$ 中的最小面恰为 $F$；
这只使用 $F$ 的面性质与球的严格凸性，不需要任意纯对的 $\mathrm B$。
VII104.4的局部极性与校准比较另有 $\mathrm{Pair}_{\perp}$ 前件，此处不使用它们。

以下最大方向和极端纤维的选择，以及两层扰动，复用
[VII98.3，式(VII98.10)—(VII98.15)][Q114ExtremeFibre]的证明核心。
其中原范数、达到性与共同支撑使用[VI90.9，式(90.16)—(90.17)][Q114BaseNorm]，
原截面判据与斜率预算分别见
[VII98.4的证明及VII98.5，式(VII98.17)—(VII98.20)][Q114SectionBudget]。
这些步骤只需要原紧基、全效应与当前这张完整球。
不能移用VII98.3中由VII98.2取得的“两个端点均混”及其正维数下界：
VII98.2正是在排除纯 $a$ 时，调用 $\mathrm B$ 使任意纯对生成的 $H(r,a)$ 为球。
(IX116.1)只描述各个完整 $D_s$，没有给这个额外前件。

具体地，令 $\gamma$ 为原差体 $K-K$ 在 $\ker u$ 上的Minkowski泛函。
[VII98.1，式(VII98.4)—(VII98.5)][Q114NormInterface]的同单位接口为

$$
\gamma(z)=\tfrac12\|z\|_C
=\max_{f\in\mathcal E}f(z)
=\min\{t\ge0:z=t(x-y),\ x,y\in K\},\qquad z\in\ker u,
\tag{IX116.8}
$$

最大值、最小值均达到。其成熟基范数／序单位对偶来源为
[Lami–Palazuelos–Winter，§II.1 Definitions 1—2、Lemma 3][Q114LPW]，
正是有限维原锥与完整 $[0,u]$ 的接口；不使用该文的双系统或受限测量条件。
这里系数 $1/2$ 来自 $u(z)=0$ 时正负质量相等。

由VI90.9，失败的某个对径 $q,r$ 满足 $\gamma(q-r)<1$。
达到的最小实现给 $q-r=t(x-y)$，其中 $0<t<1$，故

$$
Q=(K-K)\cap L(F),\qquad R=\max_{w\in Q}|w|_F>2.
\tag{IX116.9}
$$

$Q$ 紧凸且包含 $F-F=2B_F$。选达到 $R$ 的 $w$；平方内在范数的严格凸性使
$w\in\operatorname{ext}Q$，否则严格凸组合的平方范数小于 $R^2$。
在非空紧凸纤维

$$
M_w=\{(x,y)\in K\times K:x-y=w\}
\tag{IX116.10}
$$

中选一个极点 $(a,b)$。有 $\gamma(w)\le1$；若严格小于一，
(IX116.8)给 $w=s(x-y)$、$0<s<1$，使 $w/s\in Q$ 的长度大于 $R$，矛盾。
所以 $\gamma(w)=1$。取同一对偶极大效应 $e\in\mathcal E$，则
$1=e(w)=e(a)-e(b)$，原零一界迫 $e(a)=1$、$e(b)=0$。
置

$$
q_*=c+\frac wR,\qquad r_*=c-\frac wR,\qquad \lambda=\frac R2>1,
\tag{IX116.11}
$$

便得同一 $F$ 中的原纯对径和(IX116.3)。

最小面相对内部性质给 $a\in\operatorname{ri}G(a)$、$b\in\operatorname{ri}G(b)$。
包含 $a,b$ 的原暴露面 $K\cap\{e=1\}$、$K\cap\{e=0\}$
分别包含其最小面，因此 $e$ 在两面恒一、恒零；两面都是真面。
前述VII103.2分类现在给出恰好纯单点或整张原排除球的选择。
端点非纯时，其最小面不是单点，故为整球且端点在球的相对内部。
这一步保留了零维分支，没有以混合性填入额外假设。

为得到(IX116.4)，取 $v_+\in L(a)$、$v_-\in L(b)$，并假设
$v_+-v_-\in L(F)$。相对内部使充分小的同一个 $\varepsilon>0$ 满足
$a\pm\varepsilon v_+\in G(a)$、$b\pm\varepsilon v_-\in G(b)$。
两对同步扰动的差为 $w\pm\varepsilon(v_+-v_-)$，均在 $Q$ 中且中点为 $w$。
第一层极端性 $w\in\operatorname{ext}Q$ 迫 $v_+-v_-=0$。
两对扰动于是仍属于同一个 $M_w$，其中点为 $(a,b)$；
第二层极端性 $(a,b)\in\operatorname{ext}M_w$ 再迫 $v_+=v_-=0$。
故映射

$$
L(a)\times L(b)\longrightarrow\ker u/L(F),\qquad
(v_+,v_-)\longmapsto[v_+-v_-]
\tag{IX116.12}
$$

单射。将第二个方向换号即得所述直和，维数给(IX116.6)。
第一层消去差分移动，第二层才消去共同平移；二者针对同一个原实现。
在全三球情形，混端点最小面的维数恰为三，纯端点为零，遂得(IX116.7)及两端均混时的界。
它们只约束重新选出的最大方向与极端纤维端点，不是对每个失败方向或每种端点实现的断言。

最后在各端点的原最小面内作纯分解。
若 $a$ 纯，取 $x_1=x_2=a$、$\alpha=1$。
若 $G(a)=D_s=c_++A_+(B^{d_s})$，写 $a=c_++A_+(t n)$，
其中 $0\le t<1$、$\|n\|=1$；$t=0$ 时任选一个单位方向。
取

$$
x_1=c_++A_+n,\qquad x_2=c_+-A_+n,\qquad
\alpha=\frac{1+t}{2}.
\tag{IX116.13}
$$

球面极点是原 $P$ 中的点，且这两个原纯点的凸组合正是 $a$。
对 $b$ 用同样构造，得到 $y_1,y_2,\beta$，从而得到(IX116.5)。
这些支撑都取自各自的原最小面，故由(IX116.4)已具有同一个 $e$ 的饱和读数。
等价地，$e(a)=1$ 的凸平均与 $e(x_i)\le1$ 迫每个正权项取一，
$e(b)=0$ 与 $e(y_j)\ge0$ 迫每个正权项取零；零权项不参与这个推论。

反向若有(IX116.5)形状的恒等式，并有原 $h(q)=1$、$h(r)=0$，则原仿射性给

$$
\lambda
=\alpha h(x_1)+(1-\alpha)h(x_2)
 -\beta h(y_1)-(1-\beta)h(y_2)
\le1,
\tag{IX116.14}
$$

与 $\lambda>1$ 矛盾，反向障碍成立。

排除这类失败仍须在同一个原模型中证明 $Q\subseteq2B_F$。
共同效应在 $F$ 上的零一预算仅给VII98.5的 $1\le R/2$，没有给所缺的 $R\le2$。
有限证书自身也不构造满足全部完整排除球条件的反模型。证毕。

[Q114NormInterface]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md#981-原全效应载体与整个二纯面的最小维数 "VII98.1，式(VII98.4)—(VII98.5)：原基范数、同单位对偶及共同支撑。"
[Q114ExtremeFibre]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md#983-最大伸长与同差纤维的两层极点 "VII98.3，式(VII98.10)—(VII98.15)：最大方向、极端同差纤维及两层扰动；不移用VII98.2的B依赖混合端点结论。"
[Q114SectionBudget]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md#984-严格维数域的原接触与全部局部效应延拓 "VII98.4的截面等价证明及VII98.5的斜率边界(VII98.20)；临界维数结论保留其额外前件。"
[Q114FaceExhaustion]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md#1032-从整个排除球到全部原真面 "VII103.2，式(VII103.4)—(VII103.5)：仅EB所需的共同暴露、原真面穷尽与完整球。"
[Q114LocalBall]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md#1042-局部pair恰好恢复每张已有球的全部对径 "VII104.2证明中已有整球的最小面与局部几何；VII104.4的极性和校准比较另需Pair_perp。"
[Q114BaseNorm]: QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md#90-稀疏实psd的零拼合传递性与一般效应延拓缺口 "VI90.9，式(90.16)—(90.17)：全效应排除、带质量捷径及达到的对偶。"
[Q114LPW]: https://arxiv.org/html/1703.03392v2#S2.SS1 "L. Lami, C. Palazuelos, A. Winter, Ultimate data hiding in quantum mechanics and beyond，§II.1 Definitions 1—2、Lemma 3：有限维基范数／序单位对偶；此处只用其原锥全效应接口。"

## 追加锚（本行以下为增补区）

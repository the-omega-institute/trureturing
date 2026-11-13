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

## 116. 原球标签、一条满刻度直径的三元完成与原全锥三次几何

**约定 116.0（卷间编号）。** 103—106章指[第七卷][Q116VII]，107—113章指[第八卷][Q116VIII]；
114—115章是本卷既有章，116章是本章，新增式号使用IX116前缀。全文的态、纯点、效应和单位均指同一原域。
记全Pair为任意两不同纯点生成真最小面，$\mathrm{Pair}_{\perp}$ 只量化原正交纯对，两者不混用。

### 116.1 原全域与既有完整面接口

**定义 116.1（完整原域）。** 取非零有限维实空间 $V$、闭尖生成凸锥
$C\subset V$ 及在 $C\setminus\{0\}$ 上严格正的 $u$。保留整个原紧基
$K=C\cap\{u=1\}$、全部 $P=\operatorname{ext}K$ 和全部原效应 $\mathcal E=[0,u]_{C^*}$，置

$$
F_p=\{f\in\mathcal E:f(p)=1\},\quad T_p(x)=\min_{f\in F_p}f(x),\quad
D_p=\{x\in K:T_p(x)=0\},\quad \mathcal A_p=\{e\in F_p:e|_{D_p}=0\}.
\tag{IX116.1}
$$

116.1—116.6的基本域仅为 $\mathrm{EB}_{\ge1}$：每个完整 $D_p\simeq_{\rm aff}B^{d_p}$，
$d_p\ge1$；不预付 $P$ 闭、Pair、共同中心、least、谱性、同维或第三点。
$p\perp q$ 表示某张原效应在 $p,q$ 取一、零；补效应给零对称。$H(p,q)$ 为原最小面，
$\mathrm{Pair}_{\perp}$ 表示对所有不同且 $p\perp q$ 的原纯对有 $H(p,q)\ne K$。
记非点真面族、球边及标签纤维为

$$
\mathscr B=\{D_p:p\in P\},\qquad S(F)=P\cap F=\partial_{\rm rel}F,\qquad
I(F)=\{p\in P:D_p=F\}.
\tag{IX116.2}
$$

以下证明使用VII103.2的既有接口：$D_p$ 为紧暴露极大真面，$\mathcal A_p\ne\varnothing$；
全部非空真面只有纯单点或完整球。球的极点恰为原纯点与球的交，故(IX116.2)成立，
$F=\operatorname{conv}S(F)$，而不同完整球若相交，交恰为一个纯点。对不同纯点另有

$$
H(p,q)\ne K\quad\Longleftrightarrow\quad D_p\cap D_q\ne\varnothing.
\tag{IX116.3}
$$

确实，左侧给 $H(p,q)=D_r$，零对称给 $r\in D_p\cap D_q$；反之在非空紧面
$D_p\cap D_q$ 取原纯点 $r$，则 $p,q\in D_r$，所以 $H(p,q)\subseteq D_r\ne K$。
这些接口不消费VII103.3的全Pair前件；IX114.2在固定球维数下复用了同一原面分类。
额外PR分支的严格暴露、纯点紧性、共同刻度、正提升预算、niceness与饱和判据，
分别使用IX114.3—114.9；固定厚球维数时的无facet障碍仍使用IX114.10。
以下同球结构保留可变 $d_p\ge1$ 的原域，给精确双纤维和孤立性；
一方向紧性则使用饱和读数而不输入PR。

### 116.2 同球标签的整球成对刚性

**定理 116.2（精确二分与孤立块）。** 每个 $F\in\mathscr B$ 恰有两种情形：
$I(F)$ 是单点；或存在唯一 $G\in\mathscr B$，使

$$
I(F)=S(G),\qquad I(G)=S(F),\qquad F\cap G=\varnothing.
\tag{IX116.4}
$$

后一情形两球均不与第三张不同完整球相交；前一情形 $F$ 的每个球边点均属于另一张不同完整球。
故单标签恰等价于与另一完整球有交。重复块的纯正交图是 $S(F)\sqcup S(G)$ 上的孤立完全二部图；
每条跨侧边没有共同正交第三点，且其原最小面为 $K$。不据此断言原凸体有join分解。

证明。设 $p\ne s$ 且 $D_p=D_s=F$。取 $q\in S(F)$，置 $G=D_q$。
零对称给 $p,s\in G$；因 $p\notin F$，有 $G\ne F$。任取 $r\in S(F)$，也有
$p,s\in D_r$；不同完整球不能共享两个点，故 $D_r=G$。
若 $t\in S(G)$，则对所有 $r\in S(F)$ 有 $t\in D_r$，零对称给 $r\in D_t$。
取凸包并用极大性得 $D_t=F$。反之，$D_t=F$ 给 $q\in D_t$，故 $t\in D_q=G$，
纯性使 $t\in S(G)$。所以 $I(F)=S(G)$，交换角色同得 $I(G)=S(F)$。
若 $F,G$ 相交，唯一交点 $v$ 纯且 $v\in S(F)$，故 $D_v=G$，产生 $v\in D_v$ 的矛盾。
$G=D_q$ 也给唯一性。若第三球 $L=D_t\ne F$ 与 $F$ 交于 $r$，则
$r\in D_t$ 给 $t\in D_r=G$，进而 $t\in S(G)$、$L=D_t=F$，矛盾；另一侧相同。

若 $I(F)=\{p\}$，固定 $q\in S(F)$。因 $p\in S(D_q)$ 且 $D_q$ 正维，可取
$s\in S(D_q)\setminus\{p\}$。零对称给 $q\in D_s$，而 $D_s=F$ 将使 $s=p$。
故 $F\cap D_s=\{q\}$，证明逐球边交叠及二分的交叠刻画。
最后，对 $x\in S(F)$，全部纯正交邻点恰为 $P\cap D_x=S(G)$，另一侧反之。
$D_x\cap D_y=G\cap F=\varnothing$ 排除第三点，并由(IX116.3)给 $H(x,y)=K$。
两个重复块若共享纯点，该点的 $D$ 及(IX116.4)迫使球对相同。全厚时每个重复纤维含连续统多个标签。证毕。

### 116.3 原宽度与每球一个满刻度方向

**命题 116.3（整球分隔及统一残值）。** 对重复球对 $F,G$，存在同一原 $e\in\mathcal E$，
其零面恰为 $F$、一值面恰为 $G$；并存在 $\varepsilon_F,\varepsilon_G>0$，使

$$
f(x)\ge\varepsilon_F\ (q\in S(F),x\in F,f\in F_q),\qquad
f(y)\ge\varepsilon_G\ (t\in S(G),y\in G,f\in F_t).
\tag{IX116.5}
$$

证明。取非零 $b\in C^*$ 且 $b|_F=0$，令 $M=\max_Kb>0$。最大面中每个纯点 $t$
都由 $b/M$ 确认，故 $F\subseteq D_t$，极大性给 $D_t=F$、$t\in S(G)$。
最大面由其极点凸生成，故包含于 $G$，特别地 $\max_Kb=\max_Gb$。
取球图 $\chi:G\to B^d$、对径 $g_\pm=\chi^{-1}(\pm n)$ 及 $e_\pm\in\mathcal A_{g_\pm}$。
二者零于 $F$；球支持等号给

$$
e_\pm(\chi^{-1}z)=1-\lambda_\pm\pm\lambda_\pm n\cdot z,\qquad0\le\lambda_\pm\le\tfrac12.
\tag{IX116.6}
$$

若某个 $\lambda_\pm=0$，对应效应在整个 $G$ 为一，即可取为 $e$。
否则 $h=\lambda_-e_++\lambda_+e_-$ 正、零于 $F$，在 $G$ 恒为
$k=\lambda_-+\lambda_+-2\lambda_-\lambda_+>0$。前段给 $\max_Kh=k$，故 $e=h/k\in\mathcal E$。
零面包含极大真面 $F$ 而不等于 $K$，故恰为 $F$；一值面同理恰为 $G$，零斜率情形亦然。
$\mathcal E$ 紧：在由 $K$ 中点组成的线性基上所有读数均在 $[0,1]$。
所以 $\{(q,x,f):q\in S(F),x\in F,f\in\mathcal E,f(q)=1\}$ 紧非空。
若评价 $f(x)$ 的最小值为零，其达到点给 $x\in D_q=G$，与 $x\in F$ 矛盾。
故该最小值 $\varepsilon_F>0$；另一侧相同。证毕。

**命题 116.4（宽度的准确含义）。** 定义原整球宽度

$$
W(F)=\max_{f\in\mathcal E}\bigl(\max_F f-\min_F f\bigr),\qquad0\le W(F)\le1.
\tag{IX116.7}
$$

最大值达到，$W(F)=1$ 恰等价于至少一条球内对径被同一原效应读成一、零；重复球必有 $W(F)<1$。
证明。最大、最小读数连续依赖于效应。非恒定仿射函数在球上的两个极值点为唯一对径，
振幅一恰表示两端为一、零。若重复球宽度一，达到宽度的效应确认最大点 $q\in S(F)$，
却在另一端取零，违反(IX116.5)。证毕。

**定理 116.5（存在方向足以消重复并给纯点闭性）。** 若另加 $\forall F\in\mathscr B,W(F)=1$，
则 $p\mapsto D_p$ 是全部纯点到全部非点真面的双射，且 $P$ 在 $K$ 中闭。
证明。116.4排除重复，既有面穷尽给满射。若 $p_j\in P$、$p_j\to x\in K$，
在 $D_{p_j}$ 选饱和对径 $y_j,z_j$、效应 $b_j$，并选 $e_j\in\mathcal A_{p_j}$。
$K,\mathcal E$ 紧使同一子列有 $y_j\to y,z_j\to z,b_j\to b,e_j\to e$，且

$$
e(x)=1,\qquad e(y)=e(z)=0,\qquad b(y)=1,\quad b(z)=0.
\tag{IX116.8}
$$

因此 $y\ne z$，无需预证极限纯。作有限正权纯分解 $x=\sum_i\lambda_i s_i$；
$e(x)=1$ 迫所有 $e(s_i)=1$，于是 $y,z\in D_{s_i}$。这些面含两个不同点，必相同，
已证单射迫所有 $s_i$ 相同，所以 $x$ 纯。有限维中序列闭即闭。证毕。

### 116.4 真实凸边界切片迫使至少一张球单标签

**定理 116.6（仅EB的全局单标签球）。** 仅在116.1原域，存在 $F\in\mathscr B$ 使
$I(F)$ 为单点。任意这样的 $F$ 上每个 $q\in S(F)$ 都满足 $I(D_q)=\{q\}$，
故整个 $S(F)$ 给出在全部 $P$ 中均无重复标签的单射子族。若全部 $d_p\ge2$，这种标签和球有连续统多个。

证明。反设每张完整球均重复，116.2使所有不同完整球两两不交。
正维真面使 $\dim\operatorname{aff}K\ge2$。这些块覆盖 $S=\partial_{\rm rel}K\cong S^m$，其中 $m=\dim V-2\ge1$：
混边界点的非恒定支撑超平面切出非点真面，故是完整球；纯点 $x$ 则取 $q\in S(D_x)$，
零对称给 $x\in D_q$。因而这些正维紧凸面块确实分割整个真实边界。
定义 $x\sim y$ 为两点属于同一完整块，则准确有

$$
x\sim y\quad\Longleftrightarrow\quad (x+y)/2\in S.
\tag{IX116.9}
$$

左推右由面凸且位于边界。右推左时，中点的支撑超平面同时含 $x,y$；若 $x\ne y$，
其非点支撑面是完整块，若 $x=y$ 则自反性足够。因此等价关系在紧 $S\times S$ 中闭。
闭等价关系的紧Hausdorff商定理给闭连续满射 $\pi:S\to Y=S/{\sim}$，且 $Y$ 紧Hausdorff。
这里不假设 $Y$ 是ENR、流形、局部可缩、可度量或有限维。

在 $\operatorname{aff}K$ 选坐标，枚举所有切过 $\operatorname{ri}K$ 的有理高度坐标超平面 $L$。
任一块正维，故有某坐标不同的两点；取其间的有理高度。该高度严格介于 $K$ 的该坐标极值间，
而该坐标在 $\operatorname{ri}K$ 上取遍此开区间，故所取 $L$ 确实切过 $\operatorname{ri}K$。
所以 $Y=\bigcup_L\pi(S\cap L)$，各项紧闭；紧Hausdorff空间的Baire性给一张 $L$ 及
非空开 $O\subseteq Y$，满足 $O\subseteq\pi(S\cap L)$。于是下面两映射是同一 $\pi$ 的限制：

$$
g_1:X_1=\pi^{-1}O\longrightarrow O,\qquad
g_2:X_2=\pi^{-1}O\cap L\longrightarrow O.
\tag{IX116.10}
$$

两者连续满射且proper：$A\subseteq O$ 紧时，$\pi^{-1}A$ 在 $S$ 中紧，和闭集 $L$ 的交也紧。
其纤维分别是整个紧凸块及非空紧凸截面，均可缩。三空间局部紧Hausdorff。
以下统一用系数 $\mathbb F_2$；紧Hausdorff上的Čech群采用与Alexander–Wallace–Spanier自然一致的版本。
对局部紧Hausdorff空间定义 $H_c^j(Z)=\widetilde{\check H}^{\,j}(Z^+;\mathbb F_2)$，
其中 $Z^+$ 为一点紧化；若 $Z$ 紧，仍加一个孤立的 $\infty$，此定义统一成立。

proper性使实际限制延拓成保基点的连续满射 $g_i^+:X_i^+\to O^+$：在 $\infty$ 处，
紧集补的原像仍为紧集补；$\infty$ 纤维为单点，其余纤维仍为非空紧凸集。
固定 $j\ge0$ 并选整数 $n>j$，在整个紧Hausdorff目标 $O^+$ 上用
[Lawson Corollary 3.7][Q116L]，可缩纤维保证点到纤维在 $0,\ldots,n-1$ 次的上同调映射均为同构，
故 $(g_i^+)^*:\check H^j(O^+)\to\check H^j(X_i^+)$ 为同构。
这些同构保持 $\infty$ 的限制；$j=0$ 取到该点的限制核，$j>0$ 用约化群等于普通群，直接得到

$$
g_i^*:H_c^j(O)\ \cong\ H_c^j(X_i)\qquad(i=1,2).
\tag{IX116.11}
$$

$X_1$ 是非空 $m$ 维球面的开子流形；由于 $L$ 切过内点，
$S\cap L=\partial_L(K\cap L)\cong S^{m-1}$，而 $X_2$ 是它的非空开子流形。
此处等式确实使用 $L\cap\operatorname{ri}K\ne\varnothing$：若截面相对内点落在 $S$，其支撑泛函
须在 $L$ 方向恒定，迫整个 $L$ 为支撑平面，与切过内点矛盾；其余包含显然。
从截面内点径向参数化给上述球面同胚。
仅对这两个可度量、局部可缩的流形源，使用VIII113.2、VIII113.12的常系数比较及成熟模二Poincaré对偶，得到
$H_c^m(X_1)\cong H_0(X_1;\mathbb F_2)\ne0$，而 $H_c^m(X_2)=0$。
它们却由(IX116.11)同构于同一 $H_c^m(O)$，矛盾。未对未知商目标使用奇异上同调或流形结论。
Lawson原文§2明确采用Alexander–Wallace–Spanier理论；Corollary 3.7（印刷p71）对紧Hausdorff
连续满射只要求上述逐纤维同构，给每个闭子集的拉回在 $0,\ldots,n-1$ 次同构、$n$ 次单射，
允许任意交换系数群，无ENR、可度量或维数前件；这里闭子集取整个 $O^+$，无需成对长正合列。

最后，任意单标签 $F$ 上若 $D_q$ 重复，116.2给与 $D_q$ 成对的 $G$，且
$q\in I(D_q)=S(G)$。$G$ 与 $F$ 交于 $q$，孤立性迫 $G=F$，使 $F$ 重复，矛盾。
故每个 $I(D_q)=\{q\}$，不同 $q$ 的 $D_q$ 必不同；全厚时 $S(F)$ 的基数为连续统。证毕。

[Q116L]: https://web.archive.org/web/20250613232023id_/http://matwbn.icm.edu.pl/ksiazki/fm/fm65/fm6517.pdf "Jimmie D. Lawson, A generalized version of the Vietoris-Begle Theorem, Fundamenta Mathematicae 65 (1969), 65–72, §2 and Corollary 3.7, printed p71; DOI 10.4064/fm-65-1-65-72."

### 116.5 单标签处的法向体及已支付的七维下界

**定义 116.7（局部归一）。** 固定 $I(D_p)=\{p\}$、球图 $\chi:D_p\to B^{d_p}$、球心 $c_p$，置

$$
\begin{aligned}
\mathcal N_p&=\{b\in C^*:b(p)=0,\ b(c_p)=1\},\\
L_p&=\{v:\exists b\in\mathcal N_p,\ b(\chi^{-1}z)=1+v\cdot z\ (z\in B^{d_p})\},\\
q&=\chi^{-1}(n),\quad r=\chi^{-1}(-n),\quad\delta_p(q)=T_q(r)\quad(\|n\|=1).
\end{aligned}
\tag{IX116.12}
$$

**定理 116.8（有限选尺的内半径与维数）。** $L_p$ 紧凸，存在 $0<\rho_p\le1$ 使

$$
\rho_pB^{d_p}\subseteq L_p\subseteq B^{d_p},\qquad
\delta_p(q)\le\frac{1-\rho_p}{1+\rho_p}<1,\qquad
\delta_p(q)=0\ \Longleftrightarrow\ n\in L_p,\qquad \dim V\ge d_p+d_q+1.
\tag{IX116.13}
$$

因此若全部完整 $D_p\simeq B^3$，仅EB便无条件给 $\dim V\ge7$，这里没有九维结论。
证明。对非零正 $b$ 且 $b(p)=0$，最大面每个纯点 $s$ 都由 $b/\max_Kb$ 确认，
故 $s\perp p$、$s\in D_p$，从而 $\max_Kb=\max_{D_p}b$。
$b\in\mathcal N_p$ 的球上非负性给斜率范数至多一，进而 $0\le b\le2u$；故 $\mathcal N_p,L_p$ 紧凸。
取 $e_p\in\mathcal A_p$，$u-e_p$ 给 $0\in L_p$。116.6末段给每个 $D_q$ 单标签。
任取 $e_q\in\mathcal A_q$，因 $p\in D_q$，有 $e_q(p)=0$；其在 $D_p$ 上为
$1-\lambda+\lambda n\cdot z$，$0\le\lambda\le1/2$。
若 $\lambda=0$，它确认整个 $D_p$，对所有 $s\in S(D_p)$ 给 $D_q\subseteq D_s$，
极大性给 $D_q=D_s$，违反单标签。故 $\lambda>0$，$e_q/e_q(c_p)$ 给 $L_p$ 的正射线点。
仅在有限方向 $\pm e_i$ 各选一次，取所得半径的最小值 $\eta>0$；凸性给
$L_p\supseteq\operatorname{conv}\{\pm\eta e_i\}\supseteq(\eta/\sqrt{d_p})B^{d_p}$。
可取 $\rho_p=\eta/\sqrt{d_p}$，无需连续选择确认尺。斜率 $\rho_p n$ 的正 $b$ 的全域最大值是
$1+\rho_p$，故 $b/(1+\rho_p)$ 为原合法确认效应，在 $r$ 取 $(1-\rho_p)/(1+\rho_p)$。
这给缺口上界；$n\in L_p$ 时半径一给 $\delta_p(q)=0$。反之零缺口给 $r\in D_q$，
任意 $e_q\in\mathcal A_q$ 在 $q,r$ 取一、零且在 $p$ 取零，所以 $2e_q\in\mathcal N_p$、斜率为 $n$。

上述内球使正泛函中满足 $b(p)=0$ 者的线性张成，限制到 $D_p$ 后张成常数和全部 $d_p$ 个方向，
故维数至少 $d_p+1$。另一方面 $p\in S(D_q)$，每个这样的正 $b$ 在球 $D_q$ 的 $p$ 处取最小值，
所以消去其 $d_q-1$ 维切空间，也消去向量 $p$；$u(p)=1$、切向量在 $\ker u$，这共给
$d_q$ 个独立消去方向。故 $d_p+1\le\dim V-d_q$。116.6已提供这样的 $p$，所以全三球时得七维。
$\rho_p>0$ 不推出 $\rho_p=1$ 或 $L_p=B^{d_p}$，更不推出所有方向缺口为零。证毕。

### 116.6 原二元关联上的三轮闭合与重复块四周期

**定理 116.9（实际交换—对径桥）。** 仅在原EB域，令 $c_p$ 为每个 $D_p$ 的唯一对称中心，
定义实际关联及不依赖球图的球内对径

$$
\mathcal I=\{(p,q)\in P^2:q\in S(D_p)\},\qquad a_p(q)=2c_p-q,\qquad
\sigma(p,q)=(q,p),\quad\tau(p,q)=(p,a_p(q)),\quad R=\sigma\circ\tau.
\tag{IX116.14}
$$

$\sigma,\tau$ 是同一 $\mathcal I$ 上的无不动点对合；这里不输入中心连续性。对 $r=a_p(q)$ 有

$$
R^3(p,q)=(p,q)\ \Longleftrightarrow\ q\perp r,\qquad
W(D_p)=1\ \Longleftrightarrow\ \exists q\in S(D_p):R^3(p,q)=(p,q),
\tag{IX116.15}
$$

并且 $\mathrm{Pair}_{\perp}\Longleftrightarrow R^3=\operatorname{id}_{\mathcal I}$。
满足全域恒等式时，两个原对合给Coxeter $A_2\cong S_3$ 在原关联上的真实作用；
各轨道恰为同一原三元组 $\{p,q,r\}$ 的六种有序边，作用在各六点轨道上自由。
若存在重复球对 $F,G$，对 $p\in S(G),q\in S(F)$，令 $\bar p=2c_G-p,\bar q=2c_F-q$，则

$$
(p,q)\xrightarrow{R}(\bar q,p)\xrightarrow{R}(\bar p,\bar q)
\xrightarrow{R}(q,\bar p)\xrightarrow{R}(p,q)
\tag{IX116.16}
$$

是严格四周期。此块上的 $\sigma,\tau$ 整轨道有八条有序跨边，给Coxeter $B_2$ 的二面体八元作用。
这是重复块的必要几何，不是已构造的 $\mathrm{EB}_{\ge2}$ 反例，也未把全部坏边分类为四周期。

证明。零对称及球边纯性使 $\sigma,\tau$ 都保留原关联；交换平方和中心反射平方均为恒等。
$p\notin D_p$ 给 $p\ne q,r$，非退化球的对径给 $q\ne r$，也排除两个对合的不动点。
若同一完整球内两纯点被某原效应读成一、零，该效应的限制是非恒定球上仿射函数，
必在唯一对径达到这两个极值。因此球内原可区分纯对必为对径，此步不需Pair。
写 $R(p,q)=(r,p)$、$s=a_r(p)$，则 $R^2(p,q)=(s,r)$、$R^3(p,q)=(a_s(r),s)$。
若回到原对，必 $s=q$，于是 $q\in D_r$，即 $q\perp r$。
反之，若 $q\perp r$，则 $p,q\in S(D_r)$，且原 $p\perp q$ 的同一效应在二者取一、零，
故 $a_r(p)=q$；同理 $r,p\in S(D_q)$ 被原 $p\perp r$ 的效应区分，故 $a_q(r)=p$。
于是三轮回归。116.4的宽度刻画及此等价，逐个首投影纤维给(IX116.15)第二式。

全域三轮闭合给每条 $p\perp q$ 的 $r\in D_p\cap D_q$，(IX116.3)给 $\mathrm{Pair}_{\perp}$；
反向直接消费VII104.2的全部原对径满刻度，再用第一式。若某条边已有共同第三点 $t$，
取 $e_q\in\mathcal A_q$，其在 $D_p$ 内于 $q,t$ 取一、零，便迫 $t=r$；因此三轮取出的正是原唯一第三点。
此时 $\sigma^2=\tau^2=(\sigma\tau)^3=1$ 是成熟 $S_3$ 呈现，且实际轨道为
$(p,q),(r,p),(q,r)$ 及其反向三边。三纯点两两不同使这六对不同，故稳定子平凡。
重复块则由116.2给 $D_p=F,D_q=G$，所有迭代的对径只取相应球的中心反射，直接得(IX116.16)。
$F,G$ 不交且各对径两端不同，四周期不能缩短；再加交换得到
$\{p,\bar p\}\times\{q,\bar q\}$ 及其反向，共八对，且没有外部边。
在此八点集合上 $\sigma^2=\tau^2=(\sigma\tau)^4=1$，实际八点轨道给标准二面体八元群的自由作用。

在额外EB3加PR的分支，直接复用IX114.5—114.8，而不重新证明共同刻度与正提升预算。
若 $F=D_p$、$q=b_F(v)$、$r=b_F(-v)$，则

$$
T_q(r)=1-2a_F,\qquad \beta_F=(2a_F)^{-1},\qquad
R^3(p,q)=(p,q)\ \Longleftrightarrow\ a_F=\tfrac12\ \Longleftrightarrow\ \beta_F=1.
\tag{IX116.17}
$$

因此 $\operatorname{Fix}(R^3)$ 与首纤维 $\{p\}\times S(D_p)$ 的交，恰为整条纤维或空集；
前者对应 $\beta_F=1$，后者对应 $\beta_F>1$。116.4给
$W(F)=1$ 当且仅当存在一对原可区分对径，所以在此PR分支还恰等价于 $\beta_F=1$。
这直接连接原R循环与IX114的刻度、预算，不把PR当作EB的后果。
以下116.10—116.17将不使用PR，另从全三球加每球一条满刻度直径得到全域三轮闭合。证毕。

### 116.7 全三球的一方向入口与三轴统一非塌陷

**定义 116.10（每球存在一条原饱和直径）。** 在116.1的完整原域，定义

$$
\mathsf Q_1:\qquad
\forall p\in P:\quad D_p\simeq_{\rm aff}B^3,\qquad W(D_p)=1.
\tag{IX116.18}
$$

第二项只要求每球存在 $q,r\in D_p$ 和同一张 $f\in\mathcal E$，使 $f(q)=1,f(r)=0$。
116.4使它等价于每个首纤维至少有一个 $R^3$ 不动点；不要求预先选定连续的端点或效应。
116.11—116.17只使用 $\mathsf Q_1$，不输入PR、Pair、谱性、第三点、共同中心或九维。
116.5已经给标签单射与 $P$ 紧，116.8已经给 $n=\dim V\ge7$。

**引理 116.11（三轴非塌陷、整球连续与真实向量球丛）。** 在 $\mathsf Q_1$ 下，
在 $H=\ker u$ 上任取辅助欧氏内积。每张原球唯一写成

$$
D_p=c_p+Q_p^{1/2}\overline B_H,\qquad Q_p\ge0,\quad\operatorname{rank}Q_p=3.
\tag{IX116.19}
$$

存在 $0<\eta\le R_0<\infty$，使全部球的三根半轴均在 $[\eta,R_0]$ 内。
映射 $p\mapsto D_p$ 在Hausdorff距离下连续，$c_p,Q_p,Q_p^\dagger$ 及其像空间投影连续。
空间 $\xi_p=\operatorname{im}Q_p$ 组成真实秩三向量丛，且连续球尺
$g_p(v,w)=\langle v,Q_p^\dagger w\rangle$ 的闭单位盘恰为 $D_p-c_p$。

证明。令 $L=\max_{f\in\mathcal E}\|f|_H\|$。$L$ 有限；饱和端点的差非零，故 $L>0$。
116.10的端点与效应给

$$
1=|f(q)-f(r)|\le L\|q-r\|,\qquad
\max\{\text{半轴长}}\ge(2L)^{-1}.
\tag{IX116.20}
$$

各半轴长又不超过 $R_0=\operatorname{diam}K/2$。此时只得最大轴的下界。
若最小轴无统一正下界，可取一列球，其最小轴趋零。
将每张球写成 $c_j+A_jB^3$，列向量为按轴长排序的正交主轴；
中心、轴长和正交三标架在有限维紧集中共同取子列，得到 $c_j\to c,A_j\to A$。
由最大轴下界及假设，有 $1\le\operatorname{rank}A\le2$。
任取 $v\in(\ker A)^\perp$、$\|v\|\le1$，沿非零核补 $w\in\ker A$，使 $\|v+w\|=1$。
则

$$
c_j+A_j(v+w)\in\partial D_{p_j}\subset P,\qquad
c_j+A_j(v+w)\longrightarrow c+Av.
\tag{IX116.21}
$$

由 $P$ 闭，整个非退化低维盘 $c+AB^3$ 均在 $P$。
盘含非平凡线段，其中点不能为 $K$ 的极点，矛盾。这给所有三轴的统一下界 $\eta$。

现取 $p_j\to p$。任意子列可再取中心、轴标架及共同零确认效应收敛，记极限球为
$F=c+AB^3$、效应为 $e$。非塌陷保证 $F$ 仍是三维椭球；连续评价给
$e(p)=1,e|_F=0$，故 $F\subseteq D_p$。每个 $\partial F$ 点又是原球面纯点的极限，故在 $P$。
二者同维且包含，仿射包相同。若严格包含，可从 $\operatorname{ri}F$ 内一点走向
$\operatorname{ri}D_p\setminus F$ 的一点；首次离开 $F$ 的点在
$\partial F\cap\operatorname{ri}D_p$，同时被要求纯与非纯，矛盾。
所以每个子列极限均为 $D_p$，即得整球连续。

对辅助坐标中的支持函数 $h_p(v)=\max_{x\in D_p}\langle v,x\rangle$，有

$$
h_p(v)-h_p(-v)=2\langle v,c_p\rangle,\qquad
\left(\frac{h_p(v)+h_p(-v)}2\right)^2=\langle Q_pv,v\rangle.
\tag{IX116.22}
$$

支持函数连续及极化确定连续的 $c_p,Q_p$。正谱与零谱有统一间隙，连续函数演算
给像投影与伪逆连续。在任意 $p_0$ 选三个环境向量，其像投影在 $\xi_{p_0}$ 独立；
在邻域内仍独立，连续Gram–Schmidt给局部标架。按 $g_p$ 归一给实际盘、球的局部平凡化。
辅助欧氏尺只为描述这些原球，不是共同物理内积的输入。证毕。

### 116.8 原边界的双映射柱、整数局部群与定向

**定理 116.12（原球族的拓扑前件）。** 在 $\mathsf Q_1$ 下，记
$n=\dim V,N=n-2,S=\partial_{\rm rel}K\cong S^N,M=S\setminus P$。
原 $M$ 是 $\xi$ 的开三盘丛；原关联 $\mathcal I$ 的两投影
$\pi_1,\pi_2:\mathcal I\to P$ 都是实际 $S^2$ 丛，而且

$$
S\cong\operatorname{DMC}(\pi_1,\pi_2)
\cong D(\xi)\cup_{\mathcal I}D(\xi).
\tag{IX116.23}
$$

$P$ 和 $\mathcal I$ 是紧有限维ENR，均连通、单连通并可定向；
它们分别是维数 $r=N-3=n-5$ 与 $r+2$ 的整数广义同调流形，$r\ge2$。
本结论不将它们认定为拓扑流形。

证明。每个非纯边界点的原最小面是唯一的完整非点真面，且该点位于其相对内部。
标签单射使存在唯一 $\ell(x)\in P$，满足 $x\in\operatorname{ri}D_{\ell(x)}$。
若 $x_j\to x\in M$，标签任一聚点由整球连续性给出一张含 $x$ 的球，唯一性迫它为 $\ell(x)$。
故 $\ell$ 连续，映射

$$
\{(p,v)\in\xi:g_p(v,v)<1\}\longrightarrow M,\qquad(p,v)\longmapsto c_p+v
\tag{IX116.24}
$$

是同胚，逆为 $x\mapsto(\ell(x),x-c_{\ell(x)})$。
两个球心不能相同，否则共同非纯点的标签不唯一；所以 $c:P\to c(P)$ 是同胚。
实际保标签收缩为 $x\mapsto(1-t)x+t c_{\ell(x)}$。

为直接支付ENR，取 $o\in\operatorname{ri}K$，从 $o$ 沿射线投影到 $S$，记为 $\rho$。
$\rho^{-1}(M)$ 是仿射环境去掉 $o$ 后的欧氏开集；
$z\mapsto c_{\ell(\rho(z))}$ 是到 $c(P)$ 的收缩，并逐点固定 $c(P)$。
于是 $c(P)$ 及 $P$ 为紧ENR。Hatcher [A.7、A.8][Q116H]给它们是有限单纯复形的收缩核，
特别地局部可缩、局部道路连通，全部同调群有限生成，道路分量有限且开闭。

在 $p$ 附近用116.11的实际标架，将 $M$ 写成 $U\times\mathbb R^3$。
普通切除及相对乘积Künneth，对点对的局部群给

$$
\begin{aligned}
H_i(P,P\setminus\{p\};\mathbb Z)
&\cong H_{i+3}(M,M\setminus\{c_p\};\mathbb Z)\\
&=\begin{cases}\mathbb Z,&i=N-3,\\0,&i\ne N-3.\end{cases}
\end{aligned}
\tag{IX116.25}
$$

具体的乘积对是
$(U\times\mathbb R^3,(U\setminus\{p\})\times\mathbb R^3\ \cup\ U\times(\mathbb R^3\setminus\{0\}))$；
第二个因子的局部群仅在三次为 $\mathbb Z$，故无Tor项，也没有维数换算的额外假设。
右端使用的是原 $M$ 为开 $N$ 流形。$P$ 已局部紧、ANR且有限覆盖维数，
故Kramer [6.3.2、6.3.5][Q116K]恰好把这些整数奇异局部群识别为
$r=N-3$ 维广义流形，并给覆盖维数也为 $r$、方向层局部常定。
由于 $n\ge7$，这里 $r\ge2$。局部乘积同样使 $\mathcal I$ 为 $r+2$ 维整数广义流形。

事实上 $\mathcal I\cong S(\xi)$，同胚为 $(p,q)\mapsto(p,q-c_p)$，所以 $\pi_1$ 为实际球丛。
116.9的真实交换 $\sigma$ 连续，$\pi_2=\pi_1\sigma$ 使第二投影也是球丛。
$\mathcal I$ 紧且避开对角线，$\sigma$ 无固定点。其局部平凡化使它为局部可缩的欧氏紧子集，
Hatcher A.7—A.8再给紧ENR及同调有限生成。

在 $\mathcal I\times[0,1]$ 定义

$$
((p,q),t)\longmapsto c_p+t(q-c_p)\in S.
\tag{IX116.26}
$$

$t=0$ 按 $\pi_1$ 的纤维压缩，$t=1$ 按 $\pi_2$ 的纤维压缩。
当 $0<t<1$ 时，像为非中心的混边界点；唯一标签先恢复 $p$，
$t=\sqrt{g_p(x-c_p,x-c_p)}$ 再恢复半径，继而恢复 $q$。
中心由第一端恢复，纯点由第二端恢复。每个纯 $q$ 也在第二端像内：取 $p\in S(D_q)$，
零对称给 $q\in S(D_p)$。所以所得紧商到Hausdorff原 $S$ 是连续双射，即同胚。

第一半柱用 $(p,2t(q-c_p))$ 识别为 $D(\xi)$；
第二半柱用 $(q,2(1-t)(p-c_q))$ 识别为另一份 $D(\xi)$。
共同中层是同一 $\mathcal I$，盘边的径向collar给它的开加厚。
因此普通Mayer–Vietoris、相对切除及van Kampen均作用于真实原边界。
这一步不要求球内对径已原正交，第二半柱坐标也不是原仿射球心的断言。

设 $P$ 有 $h$ 个道路分量。每个投影因连通纤维与局部平凡性，在分量集上给双射。
双映射柱的分量图于是为两份 $h$ 点集合间的完美匹配，有 $h$ 个分量。
原 $S^N$ 连通，故 $h=1$，$P,\mathcal I$ 均道路连通。
球丛同伦长正合列及 $\pi_1(S^2)=0$ 给两个基本群同构。
对两半柱的开加厚用van Kampen，得到

$$
0=\pi_1(S^N)\cong\pi_1(P)*_{\pi_1(\mathcal I)}\pi_1(P)\cong\pi_1(P).
\tag{IX116.27}
$$

所以 $P,\mathcal I$ 单连通。$\xi$ 的定向局部系统、两个广义流形的整数方向层遂均平凡。
以后使用的对偶是这个ENR广义同调流形类别中的对偶，不需要拓扑流形升级。证毕。

### 116.9 只先取得分次群与两份拉回独立性

**引理 116.13（整数Betti串和纤维积分）。** 在 $\mathsf Q_1$ 下，存在 $m\ge1$，使

$$
r=2m,\quad N=2m+3,\quad n=2m+5,\qquad
H^j(P;\mathbb Z)=
\begin{cases}\mathbb Z,&j=0,2,\ldots,2m,\\0,&\text{其余 }j.\end{cases}
\tag{IX116.28}
$$

在 $0<j<2m+2$，$\pi_1^*H^j(P)\oplus\pi_2^*H^j(P)=H^j(\mathcal I)$，
两份拉回都单射。取有理系数，定向Gysin序列给

$$
0\longrightarrow H^j(P)\xrightarrow{\pi_1^*}H^j(\mathcal I)
\xrightarrow{\pi_{1!}}H^{j-2}(P)\longrightarrow0.
\tag{IX116.29}
$$

此处尚未断言 $H^*(P)$ 由二次类生成。

证明。记两盘丛半部为 $B_1,B_2$。它们各自收缩到一份 $P$；
collar切除与整数Thom同构给

$$
H^{j+1}(S,B_2;\mathbb Z)
\cong H^{j+1}(B_1,\mathcal I;\mathbb Z)
\cong H^{j-2}(P;\mathbb Z).
\tag{IX116.30}
$$

Hatcher [4D.9—4D.10][Q116H]适用，因为116.12已给真实定向秩三盘丛；
4D.10的证明明确通过CW approximation处理非CW底，本处没有另给底的胞腔结构。
球面对的长正合列在 $1\le j\le N-2=r+1$ 给
$H^j(P;\mathbb Z)\cong H^{j-2}(P;\mathbb Z)$，负次数群取零。
$H^0(P)=\mathbb Z$，故该范围内偶次为 $\mathbb Z$、奇次为零。
ENR的奇异—层比较及覆盖维数 $r$ 给 $H^j(P)=0$ 当 $j>r$。
若 $r$ 奇，则 $j=r+1$ 为偶数，上述递推却给 $H^{r+1}=\mathbb Z$，矛盾。
所以 $r=2m\ge2$，得到整个整数分次群，包括顶次。
通用系数公式和有限生成性还给整数同调无挠。

球面的Mayer–Vietoris在 $0<j<N-1=2m+2$ 给两份拉回的直和同构；
其第二分量的负号吸收到直和映射中，不改变两个像的独立性。
$H^3(P;\mathbb Q)=0$，所以秩三丛的有理Euler类为零。
Hatcher §4.D的Thom—连接同态构造给完整Gysin序列，因而化为(IX116.29)。
投影公式
$\pi_{1!}(\pi_1^*a\,b)=a\,\pi_{1!}b$
来自Thom同构的杯积定义和连接同态的模相容性。
它仅是模公式，绝不是把Thom同构宣布为环同构。
对 $\mathcal I$ 的全部群，(IX116.29)还给

$$
H^{\rm odd}(\mathcal I;\mathbb Q)=0,\qquad
\dim H^{2i}(\mathcal I;\mathbb Q)=
\begin{cases}1,&i=0,m+1,\\2,&1\le i\le m,\\0,&\text{其余 }i.\end{cases}
\tag{IX116.31}
$$

所有端点均在序列内：零次拉回为同构，顶次纤维积分为同构。
整数二次还有更精确的归一：取 $a\in H^2(P;\mathbb Z)$ 生成元，
则 $\pi_1^*a,\pi_2^*a$ 是 $H^2(\mathcal I;\mathbb Z)$ 的整数基。
整数Euler类也在已为零的 $H^3(P;\mathbb Z)$ 中，故整数Gysin映射到 $H^0(P;\mathbb Z)$ 满射，
核为第一份基所张成；第二份基因此送到 $\pm1$。
限制到真实纤维，$a$ 在每张原球边上的积分为 $\pm1$，
所以这些球边甚至是同一个整数 $H_2(P;\mathbb Z)$ 中的本原类。证毕。

### 116.10 真实无对角交换与下降算子的反自伴性

**引理 116.14（最高次反向及偶数 $m$）。** 取有理系数，令
$A_i=H^{2i}(P;\mathbb Q)$、$B_i=H^{2i}(\mathcal I;\mathbb Q)$。
真实交换 $\sigma$ 在 $B_{m+1}$ 上作用为 $-1$。
算子 $\mathcal T=\pi_{1!}\pi_2^*:A_i\to A_{i-1}$ 在 $1\le i\le m$ 均为非零同构，
且对 $a\in A_i,b\in A_j,i+j=m+1$，有

$$
\int_P b\,\mathcal T(a)=-\int_P a\,\mathcal T(b).
\tag{IX116.32}
$$

因此 $m$ 为偶数，特别地 $m\ge2$。

证明。$1\le i\le m$ 时，116.13的直和分解被 $\sigma^*$ 交换，故迹为零。
零次迹为一，顶次迹为 $\varepsilon\in\{1,-1\}$，奇次群为零。
$\mathcal I$ 是紧ENR，Hatcher [A.8、2C.3][Q116H]的Lefschetz定理适用。
$\sigma$ 无固定点，故 $0=L(\sigma)=1+\varepsilon$，即 $\varepsilon=-1$。
此处的作用只是原二元位置交换，尚无第三投影或三元置换群的输入。

在 $1\le i\le m$，$\ker\pi_{1!}=\pi_1^*A_i$；
$\pi_2^*A_i$ 是与之独立的一维补空间，所以 $\mathcal T$ 为非零同构。
给 $P$ 定向，给 $\xi$ 定向，并给 $\mathcal I=S(\xi)$ 取相容的底—纤维定向。
Thom的杯、帽积相容性给
$\int_P b\,\pi_{1!}c=\int_{\mathcal I}\pi_1^*b\,c$；
该构造只用同调方向类，不要求普通切丛。于是

$$
\begin{aligned}
\int_P b\,\mathcal T(a)
&=\int_{\mathcal I}\pi_1^*b\,\pi_2^*a\\
&=-\int_{\mathcal I}\pi_2^*b\,\pi_1^*a
=-\int_P a\,\mathcal T(b).
\end{aligned}
\tag{IX116.33}
$$

中间负号恰来自 $\deg\sigma=-1$，所有类为偶次，换序没有额外符号。
这里 $P$ 的有理Poincaré配对非退化，准确使用AFP [Lemma 3.1][Q116AFP]：
116.12已供应局部紧、第二可数、局部可缩、有限维的可定向同调流形，
紧ENR又保证有限生成；不使用光滑版本。
若 $m$ 奇，取 $0\ne a\in A_{(m+1)/2}$。
$\mathcal T(a)\ne0$，且与 $a$ 的次数互补；两群均一维，非退化性使
$\int_P a\,\mathcal T(a)\ne0$，但(IX116.32)令 $b=a$ 迫它为零，矛盾。
这也单独排除了最低情形 $m=1$，以下才可使用 $a_2$。证毕。

### 116.11 双投影的乘法递推与隐藏高次生成元的排除

**定理 116.15（环乘法迫九维）。** 在 $\mathsf Q_1$ 下，

$$
m=2,\qquad r=4,\qquad N=7,\qquad n=9,\qquad
H^*(P;\mathbb Q)\cong\mathbb Q[x]/(x^3),\quad |x|=2.
\tag{IX116.34}
$$

证明。全段取有理系数，$A=\bigoplus_{i=0}^m A_i,B=\bigoplus_{i=0}^{m+1}B_i$，
指标均为实际上同调次数的一半。逐级唯一选择

$$
a_0=1,\qquad \mathcal T(a_i)=a_{i-1}\quad(1\le i\le m).
\tag{IX116.35}
$$

这是由各一维同构递归归一，未对乘法作任何约定。
以 $\pi_1^*$ 把 $A$ 视为 $B$ 的子环，令 $x=a_1,y=\pi_2^*a_1,\varphi=\pi_2^*$。
因 $\pi_{1!}y=1$，投影公式及(IX116.29)给真实的分次 $A$ 模分解

$$
B=A\oplus yA,\qquad
\varphi(a_i)=t_i a_i+y a_{i-1}\quad(1\le i\le m),\qquad t_1=0.
\tag{IX116.36}
$$

具体地，对任意 $b\in B$，先减去 $y\pi_{1!}b$，余项恰在 $\pi_1^*A$ 中；
若 $a+yc=0$，纤维积分先给 $c=0$，拉回单射再给 $a=0$。
这个自由模分解包括 $B_{m+1}=yA_m$，故以后顶次比较同样有效。

定义乘法系数

$$
xa_i=\lambda_i a_{i+1}\ (0\le i<m),\qquad
\lambda_{-1}=0,\quad\lambda_0=1,
\tag{IX116.37}
$$

并暂定义 $\lambda_m=0$ 表示 $xa_m=0$ 的顶端边界。
$\sigma^*a_i=\varphi(a_i),\sigma^*y=x$。
对 $2\le i\le m$，展开 $\sigma^{*2}a_i=a_i$：

$$
a_i=(t_i^2+t_{i-1}\lambda_{i-1})a_i
       +(t_i+\lambda_{i-2})y a_{i-1}.
\tag{IX116.38}
$$

比较自由第二项得到 $t_i=-\lambda_{i-2}$，故 $t_2=-1$。
令 $\gamma=\lambda_1\in\mathbb Q$。$x^2=\gamma a_2$，由 $\varphi$ 保乘法，

$$
y^2=\gamma\varphi(a_2)=\gamma(xy-a_2).
\tag{IX116.39}
$$

即使 $\gamma=0$，该等式也成立，未作非零除法。

当 $1\le i<m$，比较 $\varphi(xa_i)=y\varphi(a_i)$ 的 $y a_i$ 系数，得到
$\lambda_i=t_i+\gamma\lambda_{i-1}$。
$i=1$ 时这只是 $\lambda_1=\gamma$，与 $t_1=0,\lambda_{-1}=0$ 一致；
$i\ge2$ 时代入 $t_i=-\lambda_{i-2}$。
顶端 $i=m$ 时左边为零，右边仍按(IX116.36)唯一分解，给同一递推的终止条件。
因此精确得到

$$
\lambda_i=\gamma\lambda_{i-1}-\lambda_{i-2}\quad(1\le i\le m),
\qquad \lambda_{-1}=0,\quad\lambda_0=1,\quad\lambda_m=0.
\tag{IX116.40}
$$

计算中 $a_2a_{i-1}$ 只落入 $A$ 项，未假设它是 $x$ 的幂；
顶端此项在 $A_{m+1}=0$ 中消失。
再在非零顶类 $ya_m$ 上计算真实交换：

$$
\sigma^*(ya_m)=x(t_ma_m+ya_{m-1})
=\lambda_{m-1}ya_m=-ya_m,
\qquad\lambda_{m-1}=-1.
\tag{IX116.41}
$$

$xa_m=0$ 已在这里明确使用。

由(IX116.40)，$\lambda_m$ 是 $\gamma$ 的首一整系数多项式。
有理根定理使 $\gamma\in\mathbb Z$。
若 $\gamma\ge2$，递推从 $1,\gamma$ 起严格递增且正，不能有 $\lambda_m=0$；
若 $\gamma\le-2$，用 $\lambda_i(-\gamma)=(-1)^i\lambda_i(\gamma)$ 归约到前者。
故只剩 $\gamma\in\{-1,0,1\}$。
当 $\gamma=0$，$\lambda_{2j}=(-1)^j$，与 $m$ 偶而 $\lambda_m=0$ 矛盾。
当 $\gamma=1$，序列为 $1,1,0,-1,-1,0$ 的六周期；
偶数 $m$ 的零值迫 $m\equiv2\pmod6$，此时 $\lambda_{m-1}=1$，违反(IX116.41)。
所以

$$
\gamma=-1,\qquad
\lambda_i=\begin{cases}1,&i\equiv0\pmod3,\\-1,&i\equiv1\pmod3,\\0,&i\equiv2\pmod3.\end{cases}
\tag{IX116.42}
$$

于是 $m=3d+2$、$d\ge0$，且 $m$ 偶还给 $d$ 偶。
$xa_2=0$ 和 $x^2=-a_2$ 给 $x^3=0$。
这尚未排除 $d>0$：Betti串确实可能容许非二次幂产生的高次类。

专为支付这一点，置

$$
R=\bigoplus_{j=0}^d A_{3j}\subset A.
\tag{IX116.43}
$$

次数相加使它为子环，超出顶次的乘积取零。
由(IX116.42)，$x:A_{3j}\to A_{3j+1}$ 和
$x^2:A_{3j}\to A_{3j+2}$ 均非零，且为一维同构，包括 $j=d$。
乘法诱导的映射因此是环同构

$$
R\otimes_{\mathbb Q}\mathbb Q[x]/(x^3)\ \overset{\sim}{\longrightarrow}\ A.
\tag{IX116.44}
$$

它按各次数模三分解逐项为向量空间同构；保乘法来自 $R$ 是子环及 $x^3=0$，
没有假定 $R$ 的高次生成元不存在。

令 $z=yx^2\in B_3$，则 $z^2=0$。
乘法 $z:R\to B$ 单射：先乘 $x^2$ 在每个 $A_{3j}$ 上为同构，
再乘 $y$ 进入自由第二项。最高一项恰为

$$
z:A_{3d}\longrightarrow yA_{3d+2}=B_{m+1},
\tag{IX116.45}
$$

仍为非零同构；不能在这里丢掉顶次。
对 $b\in A_{3j},j\ge1$，唯一地定义 $\delta b\in A_{3j-3}$，使
$\mathcal T(b)=x^2\delta b$；另令 $\delta1=0$，线性延拓。
$\mathcal T$ 逐级非零，所以 $\delta:A_{3j}\to A_{3j-3}$ 非零。
$t_{3j}=-\lambda_{3j-2}=1$ 给

$$
\sigma^*b=b+z\delta b\qquad(b\in R).
\tag{IX116.46}
$$

此式对常数也成立。由 $\sigma^*$ 保乘法及 $z^2=0$，对 $b,c\in R$ 有

$$
z\bigl(\delta(bc)-b\delta c-c\delta b\bigr)=0.
\tag{IX116.47}
$$

括号内属于 $R$，故由单射性得到Leibniz公式。
这里包括超顶端的乘积：若 $b\in A_{3j},c\in A_{3k}$、$j+k=d+1$，
则 $bc=0$，右侧括号却可能在 $A_{3d}$，(IX116.45)仍能消去 $z$；
若 $j+k>d+1$，括号各项均已因次数为零。因而没有只在非零乘积上证明导子的缺陷。
$\delta$ 降低实际上同调次数六，是偶次数导子。

若 $d\ge1$，取 $0\ne b\in A_3$，则 $\delta b\in\mathbb Q^\times$。
有限维正分次环的正次数元幂零，设 $h\ge2$ 是满足 $b^h=0$ 的最小整数。
完整Leibniz公式给

$$
0=\delta(b^h)=h(\delta b)b^{h-1},
\tag{IX116.48}
$$

与特征零、$\delta b\ne0$ 和最小性矛盾。
所以 $d=0,m=2$，这时才有 $R=\mathbb Q$ 及(IX116.34)。
$n=r+5$ 给九维。维数限制来自真实双投影的乘法和交换；
未使用双映射柱有限分类，也未从Betti数直接指定射影空间或三元作用。证毕。

### 116.12 同一四维纯点空间中的球边支撑与全Pair

**定理 116.16（全部原球相交）。** 在 $\mathsf Q_1$ 下，每张原球边
$A_p=\partial D_p\hookrightarrow P$ 在同一个 $H_2(P;\mathbb Q)$ 中代表非零类。
任意两张原球边相交；不同原球恰交一个原纯点。
所以任意不同 $p,s\in P$ 都满足 $H(p,s)\ne K$，即全Pair。

证明。用116.15的归一 $a_1=x$，对第一投影的任一实际纤维，有

$$
\int_{A_p}x=(\pi_{1!}\pi_2^*x)(p)=1.
\tag{IX116.49}
$$

纤维用 $\xi$ 定向；$\pi_2$ 在此纤维上恰为原包含 $A_p\hookrightarrow P$。
因此每张球边都是同一四维紧可定向ENR整数同调流形中的非零二次同调类。
116.15又给 $H^2(P;\mathbb Q)=\mathbb Q x$ 且 $x^2\ne0$，
所以任意两个非零二次类的交叉配对均非零。

反设 $A_p,A_s$ 不交。它们是 $P$ 的闭ENR二球。
使用AFP [Theorem 3.4、Proposition 3.11(1)][Q116AFP]的非等变支持对偶，
它们的基本类分别给出

$$
\widetilde\alpha\in H^2(P,P\setminus A_p;\mathbb Q),\qquad
\widetilde\beta\in H^2(P,P\setminus A_s;\mathbb Q),
\tag{IX116.50}
$$

其绝对像按帽积自然性恰对应两个原球边的推出类。
具体前件是环境 $P$ 为可定向四维同调流形、闭子空间为可定向二球、
环境方向双覆盖限制为二球的平凡方向双覆盖。
它们及相关闭对均局部紧、第二可数、局部可缩、有限维；紧ENR给所用紧对象的有限同调。
AFP §2.1明确允许环面秩零，此时 $T=\{1\},R=\mathbb Q$，
不存在非平凡稳定子或等变局部化前件。
其Lemma 3.1的证明给开子集上的普通带支撑对偶；
Theorem 3.4的证明以相对杯积、切除和该帽积比较构造(IX116.50)。
在秩零时向量空间对偶保持正合，所用闭二球的同调有限使双对偶比较为同构；
无须额外假定开补集有有限胞腔结构。
此处只是闭支持基本类的对偶，不要求球边局部平坦或有普通法丛。

两个补集是开集，普通相对杯积有定义，且在不交假设下落入

$$
H^4\bigl(P,(P\setminus A_p)\cup(P\setminus A_s);\mathbb Q\bigr)
=H^4(P,P;\mathbb Q)=0.
\tag{IX116.51}
$$

故 $\alpha\beta=0$，与两个非零绝对像的配对非零矛盾。
所以所有原球边两两相交。不同原球的交由116.1恰为原纯单点。
对不同纯 $p,s$，116.5使 $D_p\ne D_s$，取其交点 $t$。
原零对称给 $p,s\in D_t$，于是 $H(p,s)\subseteq D_t\ne K$。
全Pair在原凸体内取得，尚未使用任何矩阵表示。证毕。

### 116.13 一方向入口的等价静态结论与反向全模型计算

**定理 116.17（每球一方向足以取得复三能级）。** 在116.1完整原域，下列条件等价：
$\mathsf Q_1$；EB3且每个首纤维有一个 $R^3$ 不动点；EB3加
$R^3=\operatorname{id}_{\mathcal I}$；EB3加 $\mathrm{Pair}_{\perp}$；
以及存在同原锥、同原单位的实线性双射

$$
\Phi:H_3(\mathbb C)\overset{\sim}{\longrightarrow}V,\qquad
\Phi(\operatorname{Herm}_+(\mathbb C^3))=C,\qquad u\Phi=\operatorname{Tr}.
\tag{IX116.52}
$$

这些条件还给全Pair、全部原对径满刻度、每个原正交纯对的唯一第三点及原三结果共同效应。
PR是后果，不是本定理前件。

证明。116.4、116.9给前两项等价，116.11—116.16使 $\mathsf Q_1$ 推出全Pair，
116.9再给全域三轮闭合。反之全域三轮闭合显然在每个非空首纤维有不动点。
$R^3=1$ 与 $\mathrm{Pair}_{\perp}$ 的等价已经由116.9在更大的EB原域证明。
因而在固定全三球分支，存在量词确实传播到全部方向；本步不需PR。

此时才消费VII104.2—104.3的同域joint接口。
对 $p\perp q$，唯一第三点为 $r=2c_p-q$，且
$D_p\cap D_q=\{r\},H(p,q)=D_r$。
任取原 $a_p\in\mathcal A_p,a_q\in\mathcal A_q$，既有共同完成给

$$
a_r=u-a_p-a_q\in\mathcal A_r,\qquad
a_i(p_j)=\delta_{ij},\qquad a_p+a_q+a_r=u.
\tag{IX116.53}
$$

全域非负性由该既有接口的全域最小值归一论证承担，不由球上的局部相加代替。
116.9的六点轨道现在确实对应原三元组的 $S_3$ 置换。
这些动作作用在原关联上；未由此宣称它们可延拓为整个 $K$ 上的物理可逆变换。

EB3与已得 $\mathrm{Pair}_{\perp}$ 满足VIII113.8—VIII113.9的全厚加一三球入口，
故直接复用该同锥同单位重构，得到(IX116.52)。
原态、全部原纯点、全部效应、Born评价和所有有限数学POVM的字典均由同一 $\Phi$ 保持。
这里的复型选择复用成熟秩三Jordan分类，不另立新分类定理。

反向计算使用整个复三能级原域。取 $V=\operatorname{Herm}_3(\mathbb C),C=\mathrm{PSD},u=\operatorname{Tr}$。
原 $K$ 是全部迹一PSD矩阵，全部纯点为秩一投影，整个效应域为
$f_A(\rho)=\operatorname{Tr}(A\rho),0\preceq A\preceq I$。
若 $p=vv^*,v^*v=1$，则 $\operatorname{Tr}(Ap)=1$ 等价于 $(I-A)v=0$，
所以在 $\mathbb Cv\oplus v^\perp$ 上全部确认效应恰为 $A=p\oplus B,0\preceq B\preceq I$。
对整个归一 $\rho$，正配对给

$$
T_p(\rho)=\operatorname{Tr}(p\rho),\qquad
D_p=\{\rho\succeq0:\operatorname{Tr}\rho=1,\ \rho v=0\}.
\tag{IX116.54}
$$

该完整集合是 $v^\perp\cong\mathbb C^2$ 上全部二阶密度矩阵；
Pauli坐标 $\rho=(I_2+z\cdot\sigma)/2$ 将它仿射识别为整个 $B^3$。
任取 $v^\perp$ 中正交单位向量 $w,z$，对应球对径 $q=ww^*,r=zz^*$；
原全域效应 $f_q$ 在它们上为一、零，故每条直径都饱和，特别地 $W(D_p)=1$。
这支付反向EB3和W1的全部原量词，且由同锥同单位运输保持。

在另有PR的分支，116.9和IX114.8—114.9还同时给

$$
\forall F\ W(F)=1\ \Longleftrightarrow\
\forall F\ \beta_F=1\ \Longleftrightarrow\
\forall F\ a_F=\tfrac12\ \Longleftrightarrow\ R^3=1.
\tag{IX116.55}
$$

因此本定理与IX114的每纤维全有或全无判据兼容，并用无PR的拓扑与代数证明取得更强接口。
这是存在量词更简洁的等价静态入口；不据此宣称逻辑上严格更弱、独立公理最少或全球首创。证毕。

### 116.14 全厚加一三球的原关系候选与静态字典

**定义及应用 116.18（实际三轮呈现）。** 在同一原载体定义候选

$$
\forall p\in P:\ D_p\simeq_{\rm aff}B^{d_p},\ d_p\ge2,\qquad
\exists p_0:D_{p_0}\simeq_{\rm aff}B^3,\qquad R^3=\operatorname{id}_{\mathcal I}.
\tag{IX116.60}
$$

它精确等价于VIII113.8的原候选，因而由VIII113.9得到同一原锥、同一原 $u$ 的 $H_3(\mathbb C)$ 表示。
证明。116.9把最后一项双向换回 $\mathrm{Pair}_{\perp}$；其余两项逐字保留，故VIII113.9全部前件成立。
这里未预放Hilbert、Born或三元框架，第三点由实际 $R$ 循环取出；
但此改写不比 $\mathrm{Pair}_{\perp}$ 逻辑更弱，也不声称独立假设最少或EB自动推出三轮闭合。
同一个 $\Phi:H_3(\mathbb C)\to V$ 保持整个锥和迹，给全部原对象的对应：

| 旧静态对象 | 同一原表示中的完整对应 |
| --- | --- |
| 复三维Hilbert空间、相位射线及纯态 | $p_z=\Phi(zz^*/(z^*z))$，$z\ne0$；全部 $P\cong\mathbb{CP}^2$ |
| 全部混态及混合 | $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$，保持全部凸组合 |
| 全效应、Born、补及零事件 | $f_E(\Phi\rho)=\operatorname{Tr}(E\rho)$，全部 $0\preceq E\preceq I_3$ |
| 纯确认及最低确认读数 | least为秩一投影，$T_{p_z}(p_w)=|z^*w|^2/((z^*z)(w^*w))$ |
| 全部有限数学测量 | 原 $f_j\ge0,\sum_j f_j=u$ 恰对应全部有限POVM $E_j\succeq0,\sum_jE_j=I_3$ |
| 正交完备基及谱分解 | 原joint对应三个正交秩一投影；$\rho=\sum_{i=1}^3\lambda_iP_i$，$\lambda_i\ge0,\sum_i\lambda_i=1$ |
| 单位、派生中心及共同尺 | $U=\Phi I_3$、$c=\Phi(I_3/3)$、$B(\Phi X,\Phi Y)=\operatorname{Tr}(XY)$ |

这些是VIII113.9及其VIII112.8字典的应用，不是重新证明成熟量子字典。
过程、仪器、复合、共同来源、实际共同菜单、物理钟及 $\hbar$ 仍保留VIII113.11的全部独立合同。证毕。

### 116.15 原W分支中乘法、全锥与全效应的可逆三次编码

**定理 116.19（同一原载体的完整恢复）。** 本节明确另用
$\mathsf W=\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp}$；VIII113.7在同一 $V,C,u$ 上供应秩三EJA
$J=(V,\circ,U)$，$\operatorname{tr}=u$、$B(a,b)=\operatorname{tr}(a\circ b)$、$c=U/3$、$H=\ker u$。
$B$ 正定、$B(U,a)=u(a)$、$B(U,U)=3$，$C$ 为平方锥。对 $x\in H$ 记

$$
Q(x)=B(x,x),\quad F(x)=\sqrt6\operatorname{tr}(x^3)=3\sqrt6\det_Jx,\quad
N(t,x)=t^3/27-tQ(x)/6+F(x)/(3\sqrt6).
\tag{IX116.61}
$$

幂是Jordan幂。相对于 $B|_H$ 的梯度、原乘法及原全锥由下式恢复：

$$
\begin{aligned}
\nabla F(x)&=3\sqrt6(x^2-Q(x)U/3),& \|\nabla F(x)\|^2&=9Q(x)^2,\\
\mu(x,y)&=\frac{\nabla F(x+y)-\nabla F(x)-\nabla F(y)}{6\sqrt6},\\
(\alpha U+x)\circ(\beta U+y)&=(\alpha\beta+B(x,y)/3)U+\alpha y+\beta x+\mu(x,y),\\
tc+x\in C&\ \Longleftrightarrow\ t\ge0,\quad Q(x)\le2t^2/3,\quad N(t,x)\ge0,\\
K&=\{c+x:Q(x)\le2/3,\ N(1,x)\ge0\}.
\end{aligned}
\tag{IX116.62}
$$

以 $f_a(v)=B(a,v)$ 写 $a=sc+y$，全部原效应及其全部混态概率恰为

$$
\begin{gathered}
0\le s\le3,\quad Q(y)\le\tfrac23\min\{s^2,(3-s)^2\},\quad
N(s,y)\ge0,\quad N(3-s,-y)\ge0,\\
f_a(c+x)=s/3+B(y,x).
\end{gathered}
\tag{IX116.63}
$$

原纯点即本原幂等元 $p$；记 $J_0(p)=\{z:p\circ z=0\}$，还准确恢复

$$
\begin{aligned}
F_p&=\{f_{p+b}:b\in J_0(p),\ 0\le b\le U-p\},& T_p(\rho)&=B(p,\rho),\\
D_p&=K\cap J_0(p)=b_p+\{y\in J_0(p)\cap H:Q(y)\le1/2\},& b_p&=(U-p)/2.
\end{aligned}
\tag{IX116.64}
$$

证明。以下是成熟秩三谱与Peirce计算在同一原模型中的应用。迹结合性给
$dF_x(h)=3\sqrt6B(x^2,h)$，投影到 $H$ 给梯度；三个实谱值之和为零给
$\sum_i\lambda_i^4=(\sum_i\lambda_i^2)^2/2$，故 $\|\nabla F\|^2=54(\operatorname{tr}x^4-Q^2/3)=9Q^2$。
极化梯度给 $\mu(x,y)=x\circ y-B(x,y)U/3$，展开单位分量即得完整乘法；不把Albert代数当作结合矩阵代数。
$v=tc+x$ 的三个实谱值之和为 $t$，两两乘积和为 $S_2=t^2/3-Q(x)/2$，乘积为 $N(t,x)$。
非负谱给三个不等式；反之 $t,S_2,N\ge0$ 时，对每个 $r>0$，特征多项式满足
$\chi_v(-r)=-(r^3+tr^2+S_2r+N)<0$，故无负根。三根均实，所以恰得到全部平方锥。
不能只保留行列式：谱 $(-1,-1,3)$ 的迹和行列式均正，却不在原锥内。
平方锥关于迹尺自对偶，故全效应恰为 $a\in C,U-a\in C$；分别用于 $sc+y,(3-s)c-y$ 即得(IX116.63)。
$B(c,c)=1/3,B(c,H)=0$ 给概率式，包含全部混态、零效应及补；所有有限数学测量还准确要求 $\sum_j a_j=U$。

为验证原确认而非只给概率表，若 $0\le a\le U,B(a,p)=1$，置 $k=U-a\ge0$，则 $B(k,p)=0$。
对任意 $z\in J_{1/2}(p)$ 及实 $t$，迹自对偶性给
$0\le B(k,(p+tz)^2)=tB(k,z)+t^2B(k,z^2)$，所以 $B(k,z)=0$。
Peirce正交分解给 $k\in J_0(p)$，于是 $a=p+b$；在子代数 $\mathbb Rp\oplus J_0(p)$ 中取谱，
区间条件恰为 $0\le b\le U-p$。正配对非负且可取 $b=0$，故最低确认恰为 $B(p,\rho)$。
同一零配对论证用于 $\rho\ge0$ 给 $D_p=K\cap J_0(p)$。秩二 $J_0(p)$ 的迹零 $y$ 有谱
$\pm\sqrt{Q(y)/2}$，$b_p$ 的两个谱值均为 $1/2$，所以正性恰为 $Q(y)\le1/2$。
这恢复原全部确认与完整排除球，迹尺半径为 $1/\sqrt2$。

全厚简单支路还给 $\Delta_HF=0$：令非对角Peirce维数为 $k\in\{1,2,4,8\}$，迹零对角正交基的平方和为
$2U/3$；每个 $J_{ij}$ 单位向量平方为 $(e_i+e_j)/2$，故 $H$ 的全基平方和为 $(k+2/3)U$。
于是 $\Delta_HF(x)=6\sqrt6B(x,(k+2/3)U)=0$。
旗标支路不能如此断言：在 $\mathbb R\oplus\operatorname{spin}_d$ 写迹零元素 $(-2\beta;\beta,z)$，
则 $Q=6\beta^2+2|z|^2$；令 $s=-\sqrt6\beta,\zeta=\sqrt2z$，得
$F=s^3-3s|\zeta|^2$、$\Delta F=6(1-d)s\ne0$（$d\ge2$）。证毕。

### 116.16 原定位数据的不可删除性

**命题 116.20（保留完整尺或派生中心）。** 完整 $B,u,F$ 恢复 $U=B^{-1}u,c=U/3$，
继而恢复原乘法、整个原锥和全部原效应。若只保留 $H,Q,F$ 及原 $u$，须另留派生 $c$ 才能逐点定位。
证明。给定 $c$ 后 $v=u(v)c+x$ 唯一，$Q$ 的极化给 $B|_H$，并由
$B(tc+x,t'c+y)=tt'/3+B(x,y)$ 恢复完整尺。反例取非零 $h\in H$，令

$$
A_h(v)=v+u(v)h,\qquad C_h=A_hC,\qquad K_h=K+h.
\tag{IX116.65}
$$

$A_h^{-1}=A_{-h}$，它逐点固定 $H$ 且保持 $u$。搬运Jordan结构与迹尺后，
$B_h|_H=B|_H,F_h|_H=F|_H$，但 $U_h=U+3h,c_h=c+h$。
非空紧集不在非零平移下不变，故 $C_h\ne C$。这些同构原W模型的载体定位不同，
所以迹零二、三次数据只能给同构类，不能省去定位仍声称恢复原 $C$。证毕。

### 116.17 成熟分类在完整几何编码中的应用

**应用 116.21（复型几何编码的准确反向）。** 设八维欧氏 $H=\ker u$ 上的齐次三次型满足

$$
\|\nabla F(x)\|^2=9Q(x)^2,\qquad\Delta_HF=0.
\tag{IX116.66}
$$

保留 $u(c)=1$ 的定位点，且原 $C$ 恰等于(IX116.61)—(IX116.62)定义的整个区域，
则原全态、全效应及原评价是复三能级模型；反向其派生数据满足这些条件。
证明。准确采用[Tkachev Theorem 1.1][Q116T]的成熟分类前置：实齐次eikonal三次型正交等价于
可约型 $F_0(s,z)=s^3-3s|z|^2$，或维数 $5,8,14,26$ 的四个Cartan型。
$n$ 维中 $\Delta F_0=6(2-n)s$，故八维谐和排除可约型，余下八维型唯一。
116.19的三实谱与 $k=2$ 基平方和计算表明标准 $\operatorname{Herm}_3(\mathbb C)_0$ 上的
$F_{\mathbb C}(X)=\sqrt6\operatorname{Tr}(X^3)$ 属于此型，故有等距同构 $A$ 使 $F=F_{\mathbb C}\circ A$。
映射 $tc+x\mapsto tI_3/3+Ax$ 保迹；原锥与区域相等的前件及三个实谱判据将原 $C$ 逐点送到全部PSD锥。
同锥同单位随后将全部原效应送到 $0\preceq E\preceq I_3$，保留全部原概率及116.14的完整静态字典。
反向取标准矩阵模型、$c=I_3/3$ 即得。不要求三次型到Jordan代数的一般反向分类。
若只在任意八维 $\ker u$ 另放这样的三次型，而不要求原锥等于上述区域，则没有此原域结论；
116.20也阻止删去定位。这是已重构分支的可逆几何编码，不是独立公理数减少，成熟分类不另计新定理。证毕。

[Q116T]: https://arxiv.org/pdf/1001.2387v2 "V. G. Tkachev, A generalization of Cartan’s theorem on isoparametric cubics, Theorem 1.1; Proc. Amer. Math. Soc. 138 (2010), 2889–2895."

### 116.18 剩余入口与原过程合同

**定义 116.22（尚未支付的入口）。** 在116.1的全部原量词下，保留以下问题：

$$
\begin{gathered}
\mathrm{EB}_{\ge2}\ \stackrel{?}{\Longrightarrow}\ \mathrm{Pair}_{\perp},\qquad
\mathrm{EB3}\ \stackrel{?}{\Longrightarrow}\ \forall p\ W(D_p)=1,\\
\mathrm{EB3}+\mathrm{PR}\ \stackrel{?}{\Longrightarrow}\ \forall p\ \beta_{D_p}=1,\\
\mathrm{EB}_{\ge2}+\bigl(\forall p\ W(D_p)=1\bigr)
\ \stackrel{?}{\Longrightarrow}\ \mathrm{Pair}_{\perp}
\quad\text{（球维数允许变化）}.
\end{gathered}
\tag{IX116.67}
$$

116.17不删除这些问号，也不声称存在违反它们的完整原凸体。
其中在固定EB3前件下，116.17已经证明W1与全部方向饱和、全Pair和复三能级静态表示等价；
未支付的是由球形本身取得W1，或另找无需这一入口的证明。
116.6的全局存在只给至少一张单标签球，116.8的正内半径也只给 $\rho_p>0$；
均不等于所有局部斜率体长满单位球。
全厚加一张三球的116.18继续使用全域三轮闭合，不能用固定全三球的116.17
擅自把可变维数的存在方向条件提升为该完整候选。

**约定 116.23（静态编码和实际过程的边界）。** 116.19的整个锥、效应区间和乘法恢复，
明确在 $\mathsf W=\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp}$ 分支进行；
116.21的反向还明确要求原锥等于所写的整个三次不等式区域及原中心定位。
单独在 $\ker u$ 放一个Cartan三次型不恢复任意原 $C$，116.20的平移反例保留。
这些是可逆的静态几何编码，不是原EB单独已经完成重构或独立公理数已经减少。

全部实际复合与过程仍按VIII113.11：保留同一共同来源域、全部有限份载体及其张量锥和单位、
实际纠缠准备、各分块的界与相容性、全旁观者正性和CP/Kraus提升、逐输入预算、
同族仪器、记录和粗粒化、正质量条件归一、Lüders校准，以及原钟、连续动态来源、单位与 $\hbar$。
数学上给出了一个原三结果效应族，不等于已经给出可调用的实际仪器。
原关联上的集合动作也不自动成为整个原凸体的物理对称。

以下直观解释使用116.17的完整前件。起点始终是全部原态、全部原纯点和全部原测试：
每个纯点背后，所有能被某张确认它的原测试读零的状态合起来，恰是一整颗三维实心球；
每球只再找一条能被一张原全域效应读成一和零的满刻度直径。
满刻度保留了两个分离点，先排除重复球标签，再保证纯点的极限仍是纯点；
如果一颗球沿任何轴压扁，整块塌陷盘都会成为纯点，违反极点定义，所以三轴统一不能塌。
沿这些真实原球的半径，整个原凸边界成为两份同一纯点空间的双映射柱。
真实的二元交换、两个球丛投影与原边界的球面整体约束，不只限制Betti数，还限制环乘法；
高次残留将产生把幂零元送到非零常数的下降导子，矛盾迫使原向量空间九维。
同一四维纯点空间内，每张原球边都代表非零中间类，两颗球不能互相躲开，
交点于是内生地补出第三纯点；全部方向满刻度、三轮闭合和原三结果效应随之成立，
再接上复三能级全部密度态、全效应、Born评价、有限数学测量与谱分解。
重复球块的精确四轮轨道说明了另一种被饱和排除的关联障碍，未被当作已实现的厚球反例。
尚未证明的是球形本身会自动生出每球这条饱和直径；实际过程、复合、仪器、物理钟及 $\hbar$
仍须VIII113.11的各自前件。

[Q116VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "103—106章；完整排除球的原面分类及Pair后的共同完成接口。"
[Q116VIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "107—113章；VIII113.7、VIII113.9的同原锥同原单位重构及VIII113.11过程合同。"
[Q116H]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology；Theorem 2C.3 pp179—180；§4.D Theorem 4D.1 pp432—434、Corollary 4D.9 p441、Theorem 4D.10 pp442—444及其后Gysin构造；Theorem A.7、Corollary A.8 pp525—527。"
[Q116K]: https://arxiv.org/pdf/math/0104064v1 "Linus Kramer, Compact Polygons；§6.3，Proposition 6.3.2及Theorem 6.3.5 pp60—61：有限维局部紧ANR的奇异整数局部群、广义流形与方向层接口。"
[Q116AFP]: https://arxiv.org/pdf/1303.1146v3 "C. Allday, M. Franz, V. Puppe, Equivariant Poincaré–Alexander–Lefschetz duality and the Cohen–Macaulay property；§2.1允许环面秩零，Lemma 3.1 p13、Theorem 3.4 pp15—17、Proposition 3.11(1) p19；取有理系数、可定向ENR同调流形及闭原二球。"

## 追加锚（本行以下为增补区）

## 117. 完整框架的锚片压缩、实三元识别与实际 Jordan 闭包

**约定 117.0（原域与有限接口）。** 原量子起源问题始终取116.1的整个原锥 $C$、单位 $u$、紧基 $K$、全部纯点 $P$ 与全效应 $\mathcal E=[0,u]_{C^*}$。116.17在 EB3 加每个完整排除球至少一条由同一原全域效应读成一、零的直径这一前提下，给出同一原锥、同一原单位的 $H_3(\mathbb C)$ 表示。本章研究已经有共同复矩阵实现的有限框架接口；这个实现及其矩阵乘法是前提，不能用于反推原 EB 到 Jordan 的未证桥。选出的框架也不替代整个原域。

### 117.1 同一实现中的二元与三元数据

**定义 117.1（实际框架、闭包与锚）。** 令 $d\ge2$，在同一个 $A=\operatorname{Herm}_d(\mathbb C)$ 中取三套有标签的完整秩一投影框架

$$
E=(E_i)_{i=1}^d,\qquad F=(F_j)_{j=1}^d,\qquad G=(G_k)_{k=1}^d.
$$

每套的不同成员正交、每个成员迹一，且每套之和都是同一个 $I_d$。内积约定为 $\langle v,w\rangle=v^*w$，第一变量共轭线性。定义

$$
\begin{aligned}
X\circ Y&=\tfrac12(XY+YX),&
q(P,Q)&=\operatorname{Tr}(PQ),\\
b(P,Q,R)&=\operatorname{Tr}(PQR),&
j(P,Q,R)&=\operatorname{Re}b(P,Q,R)
             =\operatorname{Tr}((P\circ Q)R).
\end{aligned}
\tag{IX117.1}
$$

这里的 $P,Q,R$ 是所取实际投影，不是从若干互不相干的实现拼出的表。置

$$
\begin{aligned}
S&=\operatorname{span}_{\mathbb R}\{E_i,F_j,G_k\},\\
J&=\bigcap\{L\subseteq A:L\text{ 是实线性子空间，含全部 }E_i,F_j,G_k,
                    \ L\circ L\subseteq L\}.
\end{aligned}
\tag{IX117.2}
$$

$J$ 是实际最小实 Jordan 闭包；$S$ 只是初始线性张成。以下充分锚条件允许其余跨框架配对为零：

$$
\begin{gathered}
q(E_i,F_1)>0,\quad q(E_i,G_1)>0\quad(1\le i\le d),\\
q(F_j,G_1)>0\quad(1\le j\le d),\qquad
q(F_1,G_k)>0\quad(1\le k\le d).
\end{gathered}
\tag{IX117.3}
$$

定义两张复锚片及其重合列

$$
M_{ij}=b(E_i,F_j,G_1),\qquad N_{ik}=b(E_i,F_1,G_k),\qquad M_{i1}=N_{i1}.
\tag{IX117.4}
$$

对每个三元位置定义实残量

$$
\Delta_{ijk}=q(E_i,F_j)q(F_j,G_k)q(G_k,E_i)-j(E_i,F_j,G_k)^2.
\tag{IX117.5}
$$

### 117.2 完备性压缩与实、复闭包二择

**定理 117.2（压缩锚片识别实际闭包）。** 在定义117.1及全部锚条件(IX117.3)下，令

$$
\begin{aligned}
\Omega={}&\{(i,j,1):1\le i,j<d\}\\
&\mathbin{\cup}\{(i,1,k):1\le i<d,\ 2\le k<d\},\\
\Gamma_\Omega&=\sum_{(i,j,k)\in\Omega}\Delta_{ijk}.
\end{aligned}
\tag{IX117.6}
$$

两部分不相交，且

$$
|\Omega|=(d-1)^2+(d-1)(d-2)=(d-1)(2d-3).
\tag{IX117.7}
$$

有如下精确结论。

（一）全部二元表与 $\Omega$ 上的复数 $b$ 恢复两张完整锚片，进而确定全部有标签框架到共同酉共轭。两张未压缩锚片共有 $2d^2-d$ 个不同三元位置。

（二）只用全部二元表与 $\Omega$ 上的实数 $j$ 即可计算 $\Gamma_\Omega\ge0$，并且

$$
\begin{aligned}
\Gamma_\Omega=0
&\ \Longleftrightarrow\ \sum_{i,j,k=1}^d\Delta_{ijk}=0\\
&\ \Longleftrightarrow\ \text{存在共同酉矩阵使全部 }E_i,F_j,G_k\text{ 都为实矩阵}\\
&\ \Longleftrightarrow\ J=U\operatorname{Sym}_d(\mathbb R)U^*
                      \text{ 对某个酉矩阵 }U,\\
\Gamma_\Omega>0
&\ \Longleftrightarrow\ J=\operatorname{Herm}_d(\mathbb C).
\end{aligned}
\tag{IX117.8}
$$

两种闭包的实维数分别为 $d(d+1)/2$ 和 $d^2$。因此 $\Omega$ 中任意一个严格不等式 $\Delta_{ijk}>0$ 就认证这里的复闭包。位置数(IX117.7)只是一个充分输入上界，不主张最少、独立参数数或实验次数。

证明。先写 $P=pp^*,Q=qq^*,R=rr^*$，其中三个向量均为单位向量。直接相乘给

$$
b(P,Q,R)=\langle p,q\rangle\langle q,r\rangle\langle r,p\rangle,
\qquad |b(P,Q,R)|^2=q(P,Q)q(Q,R)q(R,P).
\tag{IX117.9}
$$

故每个 $\Delta_{ijk}=(\operatorname{Im}b(E_i,F_j,G_k))^2\ge0$。该因子化是通常的三点 Bargmann 恒等式，不作为新的不变量分类。

首先利用完整框架之和等于单位。令

$$
a_i=q(E_i,G_1),\quad c_j=q(F_j,G_1),\quad
t_i=q(E_i,F_1),\quad h_k=\sqrt{q(F_1,G_k)}>0.
$$

迹的线性性和循环性给同一实际实现上的全部和约束

$$
\begin{array}{ll}
\displaystyle\sum_jM_{ij}=a_i,&\displaystyle\sum_iM_{ij}=c_j,\\[2pt]
\displaystyle\sum_kN_{ik}=t_i,&\displaystyle\sum_iN_{ik}=h_k^2.
\end{array}
\tag{IX117.10}
$$

这四类和均为已知实数；各片的行和总数、列和总数均为一。给出 $i,j<d$ 的 $M_{ij}$ 后，依次恢复

$$
\begin{aligned}
M_{id}&=a_i-\sum_{j<d}M_{ij}&&(i<d),\\
M_{dj}&=c_j-\sum_{i<d}M_{ij}&&(j<d),\\
M_{dd}&=c_d-\sum_{i<d}M_{id}.
\end{aligned}
\tag{IX117.11}
$$

最后一行的行和自动为 $a_d$，因为总行和等于总列和。再用 $N_{i1}=M_{i1}$，已知 $i<d,2\le k<d$ 的 $N_{ik}$ 即可恢复

$$
\begin{aligned}
N_{id}&=t_i-\sum_{k<d}N_{ik}&&(i<d),\\
N_{dk}&=h_k^2-\sum_{i<d}N_{ik}&&(k<d),\\
N_{dd}&=h_d^2-\sum_{i<d}N_{id}.
\end{aligned}
\tag{IX117.12}
$$

当 $k=1$ 时，该式与已经得到的 $N_{d1}=M_{d1}$ 一致；最后一行同样由总和一致补齐。$d=2$ 时第二个候选集合为空，恢复公式仍成立。这证明了复数锚片的压缩。特别地，若候选位置上的 $b$ 都实，所有补回条目也都实。

接着给直接坐标恢复，以支付相位与零边的义务。先用共同酉变换使 $E_i=e_ie_i^*$ 为标准坐标框架。第一组锚允许再用对角酉变换及向量相位，使 $F_1=f_1f_1^*$ 且

$$
(f_1)_i=r_i=\sqrt{t_i}>0.
$$

对每个 $G_k=g_kg_k^*$ 选择代表向量相位，使 $\langle f_1,g_k\rangle=h_k>0$；然后对每个 $F_j=f_jf_j^*$ 选择相位，使
$\langle f_j,g_1\rangle=w_j=\sqrt{c_j}>0$。当 $j=1$ 时两条件相容，$w_1=h_1$。由(IX117.9)，

$$
N_{ik}=r_ih_k\overline{(g_k)_i},\qquad
M_{ij}=(f_j)_iw_j\overline{(g_1)_i}.
\tag{IX117.13}
$$

所以

$$
(g_k)_i=\frac{\overline{N_{ik}}}{r_ih_k},\qquad
(f_j)_i=\frac{M_{ij}}{w_j\overline{(g_1)_i}}.
\tag{IX117.14}
$$

所有分母均非零：$r_i,h_k,w_j$ 由锚为正，且 $|(g_1)_i|^2=a_i>0$。公式先恢复全部 $g_k$，再恢复全部 $f_j$。两组实际框架若有相同二元表及相同候选复数，把它们都变到此规范就得到相同投影，故原框架由一个共同酉变换联系。这是有限框架相位重构的直接应用；一般循环不变量重构已有 Chien–Waldron 的 Theorem 3.2，三套以上互补正交基的完整三元版本见其 Theorem 4.7 [Q117CW]。这里不用图的模二循环生成来代替复相位计算。该文内积第一变量线性，因此其同序三元积是(IX117.9)的复共轭。

若 $\Gamma_\Omega=0$，非负项逐项为零，候选 $b$ 全实；(IX117.11)—(IX117.12)使两片全实。(IX117.14)先使全部 $g_k$ 实，再使全部 $f_j$ 实。反向，若全部框架经共同酉变换为实，则每个有序迹积实，全部 $\Delta$ 为零。于是候选残量、完整 $d^3$ 残量与共同实表示具有同一个零集。

最后必须识别闭包而非只识别向量相位。以下复用第五卷命题76.4的秩一角提取与虚边传播方法 [Q117V]。在上述 $f_1=(r_i)$ 的规范中，以 $B_{ij}=e_ie_j^*$ 记矩阵单位，并置

$$
R_{ij}=B_{ij}+B_{ji},\qquad A_{ij}=\mathrm i(B_{ij}-B_{ji})\quad(i\ne j).
$$

对任意 $X\in J$ 和 $i\ne j$，

$$
4E_i\circ(E_j\circ X)=X_{ij}B_{ij}+\overline{X_{ij}}B_{ji}.
\tag{IX117.15}
$$

取 $X=F_1$ 即得 $r_ir_jR_{ij}\in J$；连同全部 $E_i$，这些元张成 $\operatorname{Sym}_d(\mathbb R)$。若全部生成投影实，实对称矩阵在 $\circ$ 下闭合，因此 $J$ 恰等于这个实对称空间。

若某个生成投影 $X$ 有 $\operatorname{Im}X_{ij}=\beta\ne0$，(IX117.15)减去 $(\operatorname{Re}X_{ij})R_{ij}$ 并除以 $\beta$ 就得到 $A_{ij}\in J$。不同指标上的矩阵单位乘法给

$$
2A_{ij}\circ R_{jk}=A_{ik},\qquad
2R_{ij}\circ A_{ik}=A_{jk}\quad(i,j,k\text{ 两两不同}).
\tag{IX117.16}
$$

从一条虚边出发，第一式先得到以其一个端点为中心的全部虚边，第二式再得到其余端点之间的全部虚边。$d=2$ 时原来一条虚边已足够。全部 $E_i$ 以及 $i<j$ 的 $R_{ij},A_{ij}$ 是 $A$ 的实基，故此时 $J=A$。因而在本规范中闭包只有上述两种可能；若 $\Gamma_\Omega>0$，框架不可能全实，必落入第二种。反向，$J=A$ 不可能同时有维数较小的共同实闭包。两个维数按对角元、实边、虚边直接计数，得到(IX117.8)。证毕。

实数 $q,j$ 的结论只识别这里的闭包类型，不供应每个非零虚部的符号。共同复共轭保持 $q,j,\Gamma_\Omega$，却将 $b$ 变为 $\overline b$；定理（一）所用的带符号复数数据比定理（二）的输入更多。甚至在 $d=2$，把 [Q117B] 的已有 Bloch 公式 $j=(1+r\cdot s+s\cdot t+t\cdot r)/4$ 与 $q(P,Q)=(1+r\cdot s)/2$ 直接相配，已给

$$
2j(P,Q,R)=q(P,Q)+q(Q,R)+q(R,P)-1,
$$

所以该维数下的候选实三元可由二元表算出。这也表明(IX117.7)没有最小性含义。

### 117.3 二元盲点与初始线性张成的泄漏

**命题 117.3（同二元表的实际框架由实三元分开）。** 在 $d=4$ 取通常的 Pauli 矩阵 $X,Y,Z$、标准坐标框架 $E$，以 $X\otimes I_2$ 与 $I_2\otimes X$ 的四个联合秩一本征投影组成 $F$，置

$$
D_{\mathrm r}=\operatorname{diag}(1,1,1,-1),\quad
D_{\mathrm c}=\operatorname{diag}(1,\mathrm i,\mathrm i,-1),\quad
G_k^{\mathrm r}=D_{\mathrm r}F_kD_{\mathrm r}^*,\quad
G_k^{\mathrm c}=D_{\mathrm c}F_kD_{\mathrm c}^*.
\tag{IX117.17}
$$

按第五卷命题76.4的符号标签，两个三元组的全部二元表相同，所有跨框架 $q$ 均为 $1/4$；实际闭包分别有实维数十和十六。其初始实线性张成都有维数十，而实三元已经分开这两个实际闭包。

证明。框架完整性、二元表及闭包是第五卷命题76.4的现成见证，直接复用：对角共轭(IX117.17)分别将 $XI,IX$ 送到 $XZ,ZX$ 与 $YI,IY$，其中省略张量符号。因而它们与该命题的原标签相同。选每套第一个向量

$$
e=(1,0,0,0)^T,\quad f=(1,1,1,1)^T/2,\quad
g_{\mathrm r}=(1,1,1,-1)^T/2,\quad
g_{\mathrm c}=(1,\mathrm i,\mathrm i,-1)^T/2.
$$

(IX117.9)给

$$
b(E_1,F_1,G_1^{\mathrm r})=\tfrac18,\qquad
b(E_1,F_1,G_1^{\mathrm c})=\tfrac{\mathrm i}{8}.
\tag{IX117.18}
$$

两者 $j$ 分别为 $1/8$ 和零；对应 $\Delta$ 为零和 $1/64$。此位置属于 $d=4$ 时的十五个候选位置，且全部锚成立，故定理117.2给出同一闭包二择的实三元读法。

初始张成可直接看清。实三元组张成的 Pauli 词为

$$
II,ZI,IZ,ZZ,XI,IX,XX,XZ,ZX,YY;
$$

复三元组张成的词为

$$
II,ZI,IZ,ZZ,XI,IX,XX,YI,IY,YY.
$$

每列十个词在迹内积下正交，带符号框架和恢复其中每个词，故两边初始维数均为十。复例中令 $E_{++}=(II+ZI+IZ+ZZ)/4$、$F_{++}=(II+XI+IX+XX)/4$，则

$$
E_{++}\circ F_{++}
=\frac{II+ZI+IZ+ZZ+XI+IX+XX-YY}{16}
 +\frac{ZX+XZ}{16}.
\tag{IX117.19}
$$

最后一项与复例的整个初始张成正交，且其 Hilbert–Schmidt 范数平方为 $\operatorname{Tr}(((ZX+XZ)/16)^2)=(4+4)/16^2=1/32$。所以初始十维空间并不 Jordan 闭合；闭包十六维不是从十维表面上读出的维数。这两个见证处于同一矩阵环境，不是两个满足原 $C,u,K,P,\mathcal E$ 全部起源前件的模型。证毕。

### 117.4 无第三桥时，完整复三元表仍不足

**命题 117.4（同全部二元、三元表而闭包十、十六维）。** 在 $\mathbb C^4$ 中取标准框架 $E$，令 $G=E$，并以以下酉矩阵的列投影定义完整框架 $F(z)$：

$$
U(z)=\frac12
\begin{pmatrix}
1&1&1&1\\
1&z&-1&-z\\
1&-1&1&-1\\
1&-z&-1&z
\end{pmatrix},\qquad |z|=1.
\tag{IX117.20}
$$

三套有标签框架 $(E,F(1),E)$ 与 $(E,F(\mathrm i),E)$ 的全部二元表，以及任意三个标签的全部有序复数迹积，完全相同；其实际最小实 Jordan 闭包分别为 $\operatorname{Sym}_4(\mathbb R)$ 和 $\operatorname{Herm}_4(\mathbb C)$。

证明。去掉共同因子 $1/2$ 后，每列范数平方为四。六个不同列对的内积分别化为

$$
\begin{gathered}
1+z-1-z,\quad1-1+1-1,\quad1-z-1+z,\\
1-\overline z-1+\overline z,\quad2-2|z|^2,\quad1+z-1-z,
\end{gathered}
$$

故全部为零，$U(z)$ 酉，所有框架实际完整。每列每个坐标模长均为 $1/2$，故 $q(E_i,F_j(z))=1/4$，同框架配对为 Kronecker delta，$q(E_i,G_k)=\delta_{ik}$。二元表与 $z$ 无关。

任意三个标签的投影实际只来自 $E,F(z)$ 两套正交框架。三者中至少两个来自同一套，把它们循环移到相邻位置：若不同，则乘积为零；若相同，则由幂等性把迹积化为一个二元配对。三者全同也是一。因此全部有序复三元都只取零、$1/4$ 或一，取值由标签确定，与 $z$ 无关。

但两边 $F_1$ 都是常实向量 $(1,1,1,1)^T/2$ 的投影，故(IX117.15)已使 $E,F_1$ 生成全部实对称矩阵。$z=1$ 时其余生成元都实，闭包恰为实对称空间。$z=\mathrm i$ 时 $F_2$ 的 $(1,2)$ 元为 $-\mathrm i/4$；提取此角后，(IX117.16)给全部虚边，闭包为全部复 Hermitian 矩阵。维数为十、十六。

所遗漏的关系已经在四阶环上显现：

$$
\operatorname{Tr}(E_1F_1E_2F_2)=z/16.
\tag{IX117.21}
$$

因为 $(F_1)_{12}=1/4$、$(F_2)_{21}=z/4$。这里缺失的正是 $q(E_i,G_1)>0$ 的整列锚，实际值为 $\delta_{i1}$。将同一框架再命名为第三套，不能供应穿过这些零边的桥。一般有限向量族的三元不充分及较长环信息已有 [Q117CW] Example 2.5、Theorem 3.2 的先例；此处把障碍落实为完整正交框架及实际闭包维数的不同。它也只是同一矩阵环境内的有限见证。证毕。

### 117.5 原目标、关系几何与操作接口

**约定 117.5（静态表示和取得三元数的不同前提）。** 定理117.2的前提已经有 $\mathbb C^d$、秩一投影、同一矩阵乘法及三套实际完整框架。其结论是这个有限族的实三元读数足以选择实际生成的实、复闭包，不能把这些前提当成由原二元排除关系已经推出的东西。特别地，$d=3$ 时六个候选位置的结论不是比116.17更弱的全局起源入口。

在116.17的完整前提下，原量子静态接口仍由同一个保锥保单位的 $\Phi:H_3(\mathbb C)\to V$ 给出：

| 原静态对象 | 同一原表示中的对应 |
| --- | --- |
| 全部纯点、混态及凸混合 | $p_z=\Phi(zz^*/(z^*z))$；$K=\Phi\{\rho\succeq0:\operatorname{Tr}\rho=1\}$；保持全部凸组合 |
| 全效应和 Born 评价 | 所有 $0\preceq A\preceq I_3$ 对应 $f_A(\Phi\rho)=\operatorname{Tr}(A\rho)$ |
| 正交共同完成及谱分解 | 原正交纯对有唯一第三纯点；完整框架与 $\rho=\sum_i\lambda_iP_i$ 的谱分解按116.17—116.18取得 |
| 全部有限数学测量 | $f_a\ge0,\sum_af_a=u$ 恰对应 $A_a\succeq0,\sum_aA_a=I_3$ |
| 有限框架乘法读数 | 若已经取得实际 $j$，则 $j(P,Q,R)=\operatorname{Tr}((P\circ Q)R)$；满足锚条件时应用117.2 |

前四行直接使用116.17—116.18，末行使用本章明示的矩阵实现和额外三元数据。框架完备性支付(IX117.10)的和约束，却不供应在原域取得这些三元数据的操作。

例如，若另给秩一 Lüders 更新与相应 Born 规则，从纯态 $P$ 依次通过 $Q,R$ 的两次成功概率是 $q(P,Q)q(Q,R)$，并不是 $j(P,Q,R)$：第一次成功后归一状态是 $Q$，故条件概率为 $q(Q,R)$。若另给三份产品准备 $P\otimes Q\otimes R$、控制系统、相干受控循环置换及校准相位参考，循环干涉可在 Born 读回下取得 $\operatorname{Re}b$；虚部的符号还依赖循环方向和参考相位。这个已知取得合同见 [Q117B] 的关系三元应用。产品来源、相干控制、相位参考和 Born 读回都是额外操作前提，不从知道 $q$ 的表推出。

同样，全部实际复合和过程继续保留VIII113.11的共同来源域、所有有限份载体和张量锥及单位、全部相关联合输入、纠缠准备、分块相容性、全旁观者正性及 CP/Kraus 提升、逐输入预算、同族仪器、记录与粗粒化、正质量条件归一、Lüders 校准，以及原钟、连续动态来源、单位和 $\hbar$。数学上的有限 POVM 不等于可调用的实际仪器，静态闭包也不供应物理时间或复合合同。

原全域尚未支付的问题仍包括

$$
\mathrm{EB3}\ \stackrel{?}{\Longrightarrow}\ \forall p\ W(D_p)=1,
\qquad
\mathrm{EB}_{\ge2}+\bigl(\forall p\ W(D_p)=1\bigr)
\ \stackrel{?}{\Longrightarrow}\ \mathrm{Pair}_{\perp}
\quad\text{（球维数可变）},
\tag{IX117.22}
$$

以及116.22列出的其他原入口。由原关系内生地产生共同 Jordan 实现、可取得的三元关系及其全域相容性，仍不能用本章的有限矩阵前提代付。

本章承重综合是：在(IX117.3)这些非零锚下，把已知的相位恢复与秩一角传播接起来，再用实际完整框架的行列和，得到(IX117.7)—(IX117.8)的有限实三元闭包判据；其数学归属为 `repo-derived` 的有限综合，不主张一般 Bargmann 分类、矩阵单位方法或工具原创。较少候选、锚条件的必要性及一般零边网络的充分判据均未由此确立。

[Q117V]: QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md "第五卷命题76.4：同二元表的Pauli框架、秩一角提取、虚边传播及十、十六维实际Jordan闭包。"
[Q117CW]: https://arxiv.org/pdf/1312.5393v1 "Tuan Chien and Shayne Waldron, A characterisation of projective unitary equivalence of finite frames；arXiv:1312.5393v1，所引PDF正文版本May 31, 2021；Example 2.5、Theorem 3.2及其证明、Theorem 4.7。"
[Q117B]: ../../../Blueprint/D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.md "Qubit Bargmann关系三元应用：Bloch恒等式、循环方向和产品准备／受控循环／相位参考／Born读回的取得合同。"

直观地说，二元表记录两点之间联系多强，三元环还检查这些联系绕一圈能否共同拼合。完整框架像一套恰好覆盖全空间的坐标：每行、每列的总量已经固定，所以末行末列不用重新给，两个锚片的重合部分也只需给一次。满足上述非零锚条件时，保留下来的少量环若全没有虚残量，所有原框架就能一起落在实坐标里，反复做 Jordan 乘法也只得到实对称空间；只要一个候选环留下虚残量，实边便把它传播到全部虚边，闭包扩成整个复 Hermitian 空间。若第三框架只是重复第一套，三角环会看漏只能沿四边环发现的区别；即使所有三元数都知道，也仍可能把十维和十六维闭包混在一起。这明确补上了有限矩阵分支的一个信息缺口，原来从全部排除球本身生出共同量子结构、再给出实际复合与动力学的完整目标仍保留其各自条件。

## 追加锚（本行以下为增补区）

## 118. 原正交关联的开放投影、整球连续与条件量子重构

### 118.1 完整原域与只作用于原二元关系的候选

保留[116.1的完整原域][Q118IX]：非零有限维实空间 $V$、闭尖生成凸锥 $C$、在 $C\setminus\{0\}$ 上严格正的 $u$，以及整个

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad \mathcal E=[0,u]_{C^*},\\
F_p=\{f\in\mathcal E:f(p)=1\},\quad
T_p(x)=\min_{f\in F_p}f(x),\quad
D_p=\{x\in K:T_p(x)=0\},\quad
\mathcal A_p=\{h\in F_p:h|_{D_p}=0\}.
\end{gathered}
\tag{IX118.1}
$$

$\mathrm{EB}_{\ge1}$ 表示每个完整 $D_p$ 是正维仿射欧氏闭球；EB3表示全部都是三球。
所谓仿射球允许在任一辅助环境欧氏尺下呈椭球形，不预付各球共有一把物理内积。
$P$ 始终带从实际 $K$ 继承的拓扑，不先假定闭。
$p\perp q$ 表示存在同一原效应在纯点 $p,q$ 取一、零；补效应使此关系对称。
$H(p,q)$ 表示两点在原 $K$ 中生成的最小面；全Pair指每对不同纯点均有 $H(p,q)\ne K$，$\mathrm{Pair}_{\perp}$ 只量化原正交纯对。

直接复用[VII103.2][Q118VII]、IX116.1的原面接口：$K,\mathcal E$ 紧，每个 $D_p$ 是暴露极大真面，$\mathcal A_p\ne\varnothing$；全部非空真面只有纯单点和这些完整球。
不同完整球至多交于一个原纯点，而每个完整球 $F$ 满足 $S(F):=P\cap F=\partial_{\rm rel}F$、$F=\operatorname{conv}S(F)$。
这些事实只用 $\mathrm{EB}_{\ge1}$，不消费Pair。

**定义 118.1（忠实标签与原边开放性）。** 置

$$
\begin{gathered}
\mathrm{Inj}:\quad D_p=D_s\Longrightarrow p=s\qquad(p,s\in P),\\
\mathcal I=\{(p,q)\in P^2:q\in S(D_p)\},\qquad
\pi_1(p,q)=p,\quad\pi_2(p,q)=q,\quad\sigma(p,q)=(q,p),\\
\mathrm{(O)}:\quad
\forall(p,q)\in\mathcal I\ \forall(p_n)\subset P\ (p_n\to p)\quad
\exists(q_n)\subset P:\ (p_n,q_n)\in\mathcal I\ (\forall n),\quad q_n\to q.
\end{gathered}
\tag{IX118.2}
$$

主候选是EB3、Inj和(O)。它只要求：移动一条实际正交边的第一端时，能用邻近的实际第二端保持正交。
下一节证明(O)恰为 $\pi_1:\mathcal I\to P$ 开放；原零对称使 $\sigma$ 为真实交换，两投影因而同时开放。
这不是要求整个 $\mathcal I$ 在 $P^2$ 中开，也不是先给一个 $S^2$ 丛。
它不输入法向面之间的距离、修复率、连续选择、共同中心、PR、least、谱性、Pair或矩阵表示。
所有纯点、所有实际正交边和每个完整纤维均保留，不能以有限菜单代替其量词。

### 118.2 开放投影恰好控制完整球的连续性

**引理 118.2（固定维数椭球的边界极限）。** 设有限维欧氏环境中 $F_n$ 是有界的三维仿射闭球，且 $F_n\to F$ 为Hausdorff收敛，$F$ 也是三维仿射闭球。则

$$
S(F_n)=\partial_{\rm rel}F_n\longrightarrow\partial_{\rm rel}F=S(F)
\quad\text{（Hausdorff距离）}.
\tag{IX118.3}
$$

此处的 $S$ 只表示相对球面，不需另有共同纯点集合闭性。特别地，若 $x_n\in S(F_n)$、$x_n\to x$，则 $x\in S(F)$。

证明。在任意子列上写 $F_n=c_n+A_n\overline B^3$，$A_n$ 的三列为正交半轴向量。
Hausdorff收敛保证整列一致有界，故 $c_n,A_n$ 有界，可再取子列有 $c_n\to c,A_n\to A$。
线性像的一致收敛给 $F=c+A\overline B^3$；$\dim F=3$ 迫 $\operatorname{rank}A=3$。
因此同一子列上
$\partial_{\rm rel}F_n=c_n+A_nS^2\to c+AS^2=\partial_{\rm rel}F$。
若原序列的球面不收敛到该球面，就有一条Hausdorff距离保持正下界的子列，与刚证的再取子列结论矛盾。
本证明允许仿射包随 $n$ 移动；没有把低维凸集的环境边界当作其相对边界。证毕。

**定理 118.3（原关系开放性的三个等价表述）。** 仅在EB3完整原域，下列三项等价：

1. (O)；
2. $\pi_1:\mathcal I\to P$ 是开映射；
3. $p\mapsto D_p$ 在 $P$ 上Hausdorff连续。

此时 $p\mapsto S(D_p)$ 也Hausdorff连续，两投影均开放。这些结论不需Inj或 $P$ 闭。

证明。先付始终成立的上关联。若 $p_n\to p\in P$、$y_n\in D_{p_n}$、$y_n\to y$，取 $e_n\in\mathcal A_{p_n}$ 并用 $\mathcal E$ 紧性取收敛子列 $e_n\to e$。
连续评价给

$$
e(p)=1,\qquad e(y)=0,\qquad\text{因而 }y\in D_p.
\tag{IX118.4}
$$

这是纯极限标签处的整球上关联，不是预设球连续。

若首投影开放，对 $q$ 的任意相对邻域 $U\subset P$，
$\pi_1(\mathcal I\cap(P\times U))$ 是含 $p$ 的开邻域。
所以 $p_n\to p$ 时，$S(D_{p_n})$ 终将与每个这样的 $U$ 相交；在各个紧球面中选距 $q$ 最近的点 $q_n$，即有 $q_n\to q$，得到(O)。
反之，设 $W\subset\mathcal I$ 相对开且 $(p,q)\in W$，选 $P$ 中开邻域 $U,V$ 使
$(p,q)\in\mathcal I\cap(U\times V)\subset W$。
若 $p$ 不是 $\pi_1(W)$ 内点，可选 $p_n\in U\setminus\pi_1(W)$ 趋于 $p$；(O)给 $q_n\to q$，终将使 $(p_n,q_n)\in W$，矛盾。
故 $\pi_1(W)$ 开。这就是多值关系的通常下半连续性与关联投影开放的基本等价，此处已直接证明，不作新的一般拓扑原理声明。

现设(O)。对任意 $x\in D_p$，取球面上两点 $q,r$ 及 $0\le a\le1$ 使 $x=aq+(1-a)r$；沿过球心的直径即可取得。
(O)给同一标签序列上的 $q_n,r_n\in S(D_{p_n})$ 趋于 $q,r$，故
$x_n=aq_n+(1-a)r_n\in D_{p_n}$ 趋于 $x$。
紧 $D_p$ 的有限网使这一逐点下逼近一致化；(IX118.4)与紧 $K$ 则排除球内点远离 $D_p$ 的子列。
因此 $D_{p_n}\to D_p$。
反之，整球连续及引理118.2使每个 $q\in S(D_p)$ 都可由 $S(D_{p_n})$ 中的点逼近，正是(O)。
球面连续也随之成立。
最后 $\sigma$ 是 $P^2$ 上交换的限制，且由原零对称保留 $\mathcal I$，故为同胚；$\pi_2=\pi_1\sigma$ 使第二投影也开。证毕。

这里(O)与整球连续的等价是EB3域中的几何结论；尚未使用全局拓扑重构。
仅上关联可以容许纤维缩小，所缺的是每条原边向邻近标签的下逼近。

### 118.3 交换原边排除纯、混两类rank0塌缩

**引理 118.4（不预设纯点闭性的极限标签判据）。** 在 $\mathrm{EB}_{\ge1}+\mathrm{Inj}$ 下，设 $p_n\in P,p_n\to x$，$D_{p_n}\to G$ 为非空紧集的Hausdorff收敛。
若 $G$ 含两个不同点，则 $x\in P$；若 $G=\{q\}$ 而 $x\notin P$，则

$$
q\in P,\qquad x\in\operatorname{ri}D_q.
\tag{IX118.5}
$$

若极限标签本来就是纯点 $p$，则不论Inj成立与否，都有 $G\subseteq D_p$。

证明。取 $e_n\in\mathcal A_{p_n}$，允许再取子列使 $e_n\to e\in\mathcal E$，得到 $e(x)=1,e|_G=0$。
作有限正权纯分解 $x=\sum_i\lambda_i s_i$。每个 $e(s_i)=1$，故 $G\subseteq D_{s_i}$。
若 $G$ 非点，不同球不能共同包含它，全部 $D_{s_i}$ 相同；Inj迫使全部 $s_i$ 相同，$x$ 纯。
若 $G=\{q\}$、$x$ 混，则该分解至少含两个不同纯点，其球由Inj不同，共同包含 $q$，交点规则迫使 $q$ 纯。
补效应 $u-e$ 确认 $q$ 且在 $x$ 读零，故 $x\in D_q$；混点不在球的纯边界上，所以 $x\in\operatorname{ri}D_q$。
纯极限标签的末项由 $e(p)=1,e|_G=0$ 直接成立。证毕。

**定理 118.5（开放原边排除整体塌缩）。** EB3、Inj和(O)推出

$$
d_0:=\inf_{p\in P}\operatorname{diam}D_p>0.
\tag{IX118.6}
$$

证明。反设下确界为零。选直径趋零的球列，紧 $K$ 允许对标签与球心取共同子列，得到
$p_n\to x$、$D_{p_n}\to\{q\}$。
若 $x\in P$，定理118.3在 $x$ 给 $D_{p_n}\to D_x$；而 $D_x$ 是三球，不可能是单点。

若 $x$ 混，引理118.4给 $q\in P,x\in\operatorname{ri}D_q$。
任取 $q_n\in S(D_{p_n})$；整球趋单点使 $q_n\to q$。
原零对称给 $p_n\in S(D_{q_n})$，而(O)在纯标签 $q$ 处给 $D_{q_n}\to D_q$。
两边均为三维仿射球，引理118.2于是迫使 $x=\lim p_n\in S(D_q)$，与相对内部结论矛盾。
两种情形均被排除，故(IX118.6)成立。
证明中没有在取得此下界前预付 $P$ 闭、极限纯性或球丛；混标签分支真正使用了原关系的坐标交换。证毕。

### 118.4 正直径下界独立支付纯点紧性与真实球丛

**定理 118.6（非塌缩结构入口）。** 仅在EB3+Inj下，(IX118.6)推出 $P$ 紧，全部原球三根半轴均有统一正下界，$p\mapsto D_p$ Hausdorff连续，且这些实际球组成真实秩三向量球丛。
因此在EB3+Inj域内，(O)、整球连续和正直径下界等价。

证明。先证 $P$ 闭。设 $p_n\to x\in K$；在每球选 $y_n,z_n$ 使 $\|y_n-z_n\|\ge d_0$，并选 $e_n\in\mathcal A_{p_n}$。
取共同子列有 $y_n\to y,z_n\to z,e_n\to e$，于是 $y\ne z,e(x)=1,e(y)=e(z)=0$。
$x$ 的有限正权纯分解中，每个纯分量 $s_i$ 的 $D_{s_i}$ 均含 $y,z$；交点规则使这些球相同，Inj使全部 $s_i$ 相同，故 $x$ 纯。
于是 $P$ 在紧 $K$ 中闭而紧。

在 $H=\ker u$ 任取辅助欧氏尺，将球列写成 $c_n+A_n\overline B^3$，列向量为正交主轴。
最大半轴至少 $d_0/2$，全部半轴至多 $\operatorname{diam}K/2$。
若最小半轴无统一正下界，取中心、半轴和标架共同收敛子列，得 $c_n\to c,A_n\to A$，且 $1\le\operatorname{rank}A\le2$。
任取 $v\in(\ker A)^\perp,|v|\le1$，可沿非零核选 $w\in\ker A$ 使 $|v+w|=1$，故

$$
c_n+A_n(v+w)\in S(D_{p_n})\subset P,\qquad
c_n+A_n(v+w)\longrightarrow c+Av.
\tag{IX118.7}
$$

$P$ 闭使整个非平凡极限盘 $c+A\overline B^3$ 均由纯点组成；其中非平凡线段的中点却不能是 $K$ 的极点，矛盾。
所以三根半轴都有统一正下界 $a_0$，秩1、秩2退化也被排除。

若 $p_n\to p\in P$，任意子列可再取球参数极限 $F=c+A\overline B^3$。
三轴下界使 $F$ 满秩；(IX118.4)给 $F\subseteq D_p$，球面参数极限与 $P$ 闭给 $\partial_{\rm rel}F\subset P$。
二者同维且包含，仿射包相同。
若严格包含，可从 $\operatorname{ri}F$ 中一点走向 $\operatorname{ri}D_p\setminus F$ 中一点；首次离开 $F$ 的点在 $\partial_{\rm rel}F\cap\operatorname{ri}D_p$，同时应纯与非纯，矛盾。
所以每个子列极限都是 $D_p$，即得整球连续。

最后必须构造实际丛。每个原球唯一写为

$$
D_p=c_p+Q_p^{1/2}\overline B_H,\quad Q_p\ge0,\quad\operatorname{rank}Q_p=3,
\qquad \xi_p=\operatorname{im}Q_p,\quad
 g_p(v,w)=\langle v,Q_p^\dagger w\rangle.
\tag{IX118.8}
$$

选固定 $o\in\operatorname{aff}K$，令 $k_p(v)=\max_{x\in D_p}\langle v,x-o\rangle$。支持函数给

$$
k_p(v)-k_p(-v)=2\langle v,c_p-o\rangle,\qquad
\left(\frac{k_p(v)+k_p(-v)}2\right)^2=\langle Q_pv,v\rangle.
\tag{IX118.9}
$$

由整球连续及极化，$c_p,Q_p$ 连续；统一正谱隙给像投影、伪逆连续。
在任意 $p_0$ 选三个环境向量，其像投影在 $\xi_{p_0}$ 独立；邻域内连续Gram–Schmidt再按 $g_p$ 归一，得到真实秩三向量丛的局部标架。
其闭单位盘逐点恰为 $D_p-c_p$，球面逐点恰为原 $S(D_p)$。
辅助尺只描述原对象，不输入共同物理度量。
末项等价由118.3、118.5及本定理首项组成。证毕。

### 118.5 原边界的已付拓扑与同锥同单位静态重构

**引理 118.7（116.12—116.16的准确依赖运输）。** EB3、Inj和定理118.6的结构输出，足以支付116.12—116.16的全部实际前件。
这里不先调用名义上以 $\mathsf Q_1$ 为前提的结论，而是复用其原证明中已被独立取得的结构。

证明。只用EB3的116.6、116.8先给 $n=\dim V\ge7$。
由原面分类，每个混边界点在唯一完整球的相对内部；不同球不能共含混点，Inj又给唯一标签。
紧 $P$、整球连续使标签映射连续，118.6给实际局部平凡化。
因此116.12的原证明适用于同一原边界，给

$$
\begin{gathered}
S=\partial_{\rm rel}K\cong S^{n-2},\quad
S\setminus P\cong\operatorname{int}D(\xi),\quad
\mathcal I\cong S(\xi),\\
S\cong\operatorname{DMC}(\pi_1,\pi_2)
\cong D(\xi)\cup_{\mathcal I}D(\xi).
\end{gathered}
\tag{IX118.10}
$$

第一投影来自实际球面丛，第二投影只用真实交换；没有第三投影输入。
径向参数 $((p,q),t)\mapsto c_p+t(q-c_p)$ 在混边界上靠唯一标签可逆，两端分别按原第一、第二投影压缩。
所以这是整个原凸边界的双映射柱，而非另造一个有相似纤维的空间。
球心像是欧氏开集的收缩核，故 $P$ 为紧ENR；开三盘丛中的局部群给其整数同调流形维数 $r=n-5$。
两真实球丛和原边界球面再给连通、单连通及定向，$\mathcal I$ 也为紧ENR同调流形；不升级为拓扑流形。

后续各段的准确消费者如下。

| 原证明 | 此处已支付的条件 | 可复用输出 |
| --- | --- | --- |
| 116.13 | 同一双映射柱、定向秩三盘丛、真实两个拉回 | 整数偶次Betti串；两份拉回独立；实际Gysin序列及投影公式 |
| 116.14 | 无不动点原交换、紧ENR及定向、前行Gysin | 顶次交换为负；下降算子非零且反自伴；$m=r/2$ 为偶数 |
| 116.15 | 同一关联空间的两个保乘法拉回、自由模分解、顶端边界 | 排除隐藏高次生成元；$m=2,n=9$，$H^*(P;\mathbb Q)=\mathbb Q[x]/(x^3)$ |
| 116.16 | 同一个四维可定向ENR同调流形、每球边非零纤维积分、$x^2\ne0$ | 所有原球边两两相交，从而全Pair |

这里116.13并未从Betti串猜测环：116.15令 $\mathcal T=\pi_{1!}\pi_2^*$，选 $\mathcal T(a_i)=a_{i-1}$，由真实环拉回导出其乘法递推和顶次交换条件。
即使允许二次类之外的高次部分 $R$，原证明仍给 $R$ 上降六次的导子；若 $R$ 有首个正次数元，导子会把一个幂零元送成非零常数，特征零下矛盾。
因此才有 $m=2$，不是把分次群当环。
116.16把每张原球边的基本类放进同一带闭支撑对偶；若两球边不交，相对杯积落在零群，却其绝对像乘积非零，遂矛盾。
它不要求球边局部平坦或有普通法丛。
这些步骤所需的Thom、Gysin、ENR、Lefschetz和同调流形支持对偶，严格沿[116原证明所列的成熟来源及适用范围][Q118IX]使用。

W1在116原路线中先用于消除重复标签、取得纯点紧性，并给最大轴下界；本入口已经分别用Inj、118.5及118.6支付这些用途。
以上从未在Pair之前反向调用116.17，也未先预付球内对径原正交或共同第三点。证毕。

**定理 118.8（原二元开放性候选）。** 在118.1的同一完整原域，下列条件等价：

1. EB3、Inj和(O)，即每个完整纤维是三球、球标签忠实、原正交关联首投影开放；
2. EB3、Inj和 $\inf_{p\in P}\operatorname{diam}D_p>0$；
3. $\mathsf Q_1$，即EB3且每个完整 $D_p$ 至少有一条由同一原全域效应读成一、零的直径；
4. 存在同原锥、同原单位的实线性双射

$$
\Phi:H_3(\mathbb C)\overset{\sim}{\longrightarrow}V,\qquad
\Phi(\operatorname{Herm}_+(\mathbb C^3))=C,\qquad
u(\Phi X)=\operatorname{Tr}X.
\tag{IX118.11}
$$

这些条件还给全Pair、全部原对径满刻度、原正交纯对的唯一第三点及原三结果共同效应。

证明。$1\Rightarrow2$ 是118.5，$2\Rightarrow1$ 是118.6、118.3。
$2\Rightarrow4$ 先由118.6、118.7取得全Pair，尤其 $\mathrm{Pair}_{\perp}$。
此时才用VII104.2—104.3：对原 $p\perp q$，存在唯一原 $r$，且

$$
\begin{gathered}
D_p\cap D_q=\{r\},\qquad H(p,q)=D_r,\qquad r=2c_p-q,\\
\forall a_p\in\mathcal A_p\ \forall a_q\in\mathcal A_q:\quad
 a_r=u-a_p-a_q\in\mathcal A_r,\qquad
 a_p+a_q+a_r=u,\quad a_i(p_j)=\delta_{ij}.
\end{gathered}
\tag{IX118.12}
$$

原共同完成的全域非负性由其全域最小值归一证明承担，不能只凭球上和为一。
EB3及已得 $\mathrm{Pair}_{\perp}$ 满足VIII113.8—113.9，给(IX118.11)；也可在此时使用116.17的Pair分支。
$3\Longleftrightarrow4$ 是116.17的准确结论，W1在本路线是后果。

最后直接核对 $4\Rightarrow1$ 的全部原域。
在矩阵坐标中，$K$ 是全部三阶密度矩阵，$P$ 是全部秩一投影，$\mathcal E$ 是全部 $f_A(\rho)=\operatorname{Tr}(A\rho)$、$0\preceq A\preceq I$。
对秩一 $p$，确认矩阵恰为 $p\oplus B$、$0\preceq B\preceq I$，从而

$$
T_p(\rho)=\operatorname{Tr}(p\rho),\qquad
D_p=\{\rho\succeq0:\operatorname{Tr}\rho=1,\ \rho p=0\}.
\tag{IX118.13}
$$

这是 $p^\perp\cong\mathbb C^2$ 上的整个三球，其支撑确定 $p^\perp$，故EB3和Inj成立。
若 $p\perp q$、$p_n\to p$，令 $Q_n=I-p_n$，尾项定义

$$
q_n=\frac{Q_nqQ_n}{\operatorname{Tr}(Q_nqQ_n)}.
\tag{IX118.14}
$$

分母趋一而正，$q_n$ 是与 $p_n$ 正交的秩一投影且 $q_n\to q$；有限个初项在各完整球面任取。
这证明全部边上的(O)，并由同一个 $\Phi$ 运输回原域。证毕。

获得Pair后，116.9的有限三元提升也原样成立：在同一个 $\mathcal I$ 上令
$\tau(p,q)=(p,2c_p-q)$、$R=\sigma\tau$，则 $R^3=\operatorname{id}$；每条边的轨道及反向恰为同一三纯框架的六条有序边。
这不是先给全态空间的物理群作用。

**前提数量与几何简化。** 主表述只用原关系、其完整纤维和实际拓扑，法向面度量从主候选中消失。
但这三项不比116.17的EB3与W1两项少；在固定EB3域内，Inj加(O)与W1等价，重命名不构成独立公理数减少。
这里也没有证明三项逻辑独立、物理最小或全球原创，更没有证明裸EB3自动供应Inj或(O)。

### 118.6 一张稳定零见证是同一条件的效应解释

因为 $K$ 张成 $V$，$\|h\|_K=\max_{x\in K}|h(x)|$ 是 $V^*$ 上的真正范数。置

$$
Z_t=\{g\in\mathcal E:g(t)=0\}\qquad(t\in P).
\tag{IX118.15}
$$

$Z_t$ 非空紧，距离达到，使用整个原效应区间。

**定义 118.9（每边一张定性稳定零见证）。** 条件(WZ)为

$$
\begin{split}
&\forall s,r\in P\ (r\in D_s)\quad\exists h\in\mathcal A_s:\\
&\quad\forall(t_n)\subset P\ (t_n\to r)\quad
\exists(g_n)\subset\mathcal E:\quad
 g_n(t_n)=0\ (\forall n),\quad\|g_n-h\|_K\to0.
\end{split}
\tag{IX118.16}
$$

$h$ 在全部趋近序列之前选定。固定 $h$ 后，此条件等价于 $\operatorname{dist}_K(h,Z_t)\to0$ 当 $t\in P,t\to r$，也等价于通常的逐 $\varepsilon$ 邻域条件。
不要求所有 $h\in\mathcal A_s$ 或所有 $h\in Z_r$ 稳定，不要求按边连续选 $h$，不要求修复映射连续，也不要求Hölder指数、任何修复率、统一常数或统一邻域。

**引理 118.10（零效应的全域最大值与正距离）。** 在 $\mathrm{EB}_{\ge1}$ 下，$g\in Z_t$ 满足 $\max_Kg=\max_{D_t}g$。
若再有Inj，每个 $h\in\mathcal A_s$ 的零面恰为 $D_s$、一值面恰为 $\{s\}$，且

$$
\operatorname{dist}_K(h,Z_t)\ge\frac{1-\max_{D_t}h}{2}.
\tag{IX118.17}
$$

证明。$g=0$ 时最大值公式显然；否则 $m=\max_Kg>0$，在最大面取纯 $v$。
$g/m$ 是确认 $v$、在 $t$ 读零的原效应，补效应给 $v\in D_t$，所以全域最大值确实在 $D_t$ 达到。
$h$ 的零面按原定义恰为 $D_s$。
若纯 $v$ 取 $h(v)=1$，则 $D_s\subseteq D_v$，极大性与Inj给 $v=s$；任一一值混态的有限纯分解中所有分量也取一，所以整个一值面只有 $s$。
对 $g\in Z_t$ 记 $d=\|g-h\|_K$，有
$1=h(s)\le g(s)+d\le\max_Kg+d=\max_{D_t}g+d\le\max_{D_t}h+2d$。
取下确界即得。证毕。

**命题 118.11（稳定见证推出原边开放）。** 在EB3+Inj下，(WZ)推出(O)。

证明。固定 $(p,s)\in\mathcal I$、$p_n\to p$。原零对称使 $(s,p)$ 是一条原边，取该边(WZ)所给固定 $h\in\mathcal A_s$ 及 $g_n\in Z_{p_n}$，$\|g_n-h\|_K\to0$。
令 $m_n=\max_Kg_n$。因 $g_n(s)\to1$ 且 $g_n\le u$，有 $m_n\to1$，尾项严格正。
在尾项各最大面选原纯点 $s_n$；$g_n/m_n$ 是合法原效应，确认 $s_n$、零于 $p_n$，故 $s_n\in S(D_{p_n})$。
又有 $h(s_n)\to1$。紧 $K$ 中每个聚点均在 $h$ 的一值面，而引理118.10使它仅为 $s$，故 $s_n\to s$。
有限个初项在对应球面任取。这正是(O)，没有假设纯最大点的聚点预先纯，也没有漏掉 $m_n=0$ 的初项。证毕。

**定理 118.12（全EB3+Inj域的固定零测试rank0障碍）。** 在完整EB3+Inj原域，假设

$$
p_n\to x\in K,\qquad D_{p_n}\to\{q\}.
\tag{IX118.18}
$$

允许取子列并重新编号。存在同一条原正交纯边 $(s,r)$ 及同一条 $t_n\in P,t_n\to r$，使对每一张固定 $h\in\mathcal A_s$ 都有

$$
h(t_n)\to0,\qquad
\liminf_n\operatorname{dist}_K(h,Z_{t_n})>0.
\tag{IX118.19}
$$

下界可依赖 $h$，但边、子列与输入序列先于全部 $h$ 选定。这里不假设(O)、$P$ 闭或球连续。

证明。若 $x\in P$，引理118.4给 $q\in D_x$。在 $S(D_x)$ 取 $s\ne q$，令 $r=x,t_n=p_n$。
原零对称给 $r\in D_s$；任意 $h\in\mathcal A_s$ 满足 $h(r)=0$，且其唯一最大点是 $s\ne q$，所以 $\delta_h=1-h(q)>0$。
球极限给 $\max_{D_{t_n}}h\to h(q)$，引理118.10于是给

$$
\liminf_n\operatorname{dist}_K(h,Z_{t_n})\ge\delta_h/2>0.
\tag{IX118.20}
$$

并有 $h(t_n)\to h(r)=0$。此分支无须先证 $q$ 纯。

若 $x$ 混，引理118.4给 $q\in P,x\in\operatorname{ri}D_q$。
任取 $t_n\in S(D_{p_n})$，则 $t_n\to q$，原零对称给 $p_n\in S(D_{t_n})$。
对这些交换后的实际完整球写 $D_{t_n}=c_n+A_n\overline B^3$，取共同参数收敛子列，得 $G=c+A\overline B^3$。
纯标签上关联给 $G\subseteq D_q$，并有 $x\in G$；极限秩允许为0、1、2、3。
若 $G=D_q$，其维数迫 $\operatorname{rank}A=3$；将 $p_n=c_n+A_nv_n$、$|v_n|=1$ 的参数再取收敛子列，得到 $x\in S(D_q)$，矛盾。
故 $G\subsetneq D_q$。若 $G$ 含整个 $S(D_q)$，凸性会给 $G=D_q$，所以可取 $s\in S(D_q)\setminus G$，令 $r=q$。
这是一条原边。任意固定 $h\in\mathcal A_s$ 的唯一最大点 $s$ 不在紧 $G$ 中，故 $\delta_h=1-\max_Gh>0$。
$\max_{D_{t_n}}h\to\max_Gh$，再次给(IX118.20)，且 $h(t_n)\to h(q)=0$。
所取子列、$G,s$ 均与此后的 $h$ 无关，故同一序列确实阻止全部固定完整零确认。证毕。

**推论 118.13（效应与二元几何的等价）。** 在完整EB3+Inj域内，(WZ)、(O)、正直径下界及118.8的同原量子静态表示等价。

证明。118.11给(WZ)$\Rightarrow$(O)，118.8给(O)$\Rightarrow$同原矩阵表示。
反向仍在整个矩阵原域。对原边 $s\perp r$，固定 $h_s=f_s\in\mathcal A_s$；对纯 $t\to r$，记 $Q_t=I-t$，取 $g_t=f_{Q_tsQ_t}$。
$0\preceq Q_tsQ_t\preceq I$，且 $g_t(t)=0$。更一般地，对全部 $0\preceq A\preceq I$，

$$
\begin{gathered}
0\preceq Q_tAQ_t\preceq I,\qquad
\|A-Q_tAQ_t\|_{\rm op}
\le\|tA\|_{\rm op}+\|Q_tAt\|_{\rm op}
\le2\sqrt{\operatorname{Tr}(At)},\\
\max_{\rho\succeq0,\operatorname{Tr}\rho=1}|\operatorname{Tr}(H\rho)|
=\|H\|_{\rm op}\qquad(H=H^*).
\end{gathered}
\tag{IX118.21}
$$

写 $t=vv^*$，最后一个不等式用 $\|Av\|^2\le\langle v,Av\rangle$。
因此 $\|g_t-h_s\|_K\le2\sqrt{\operatorname{Tr}(st)}\to0$，给(WZ)的全部序列量词。
同一个保锥保单位 $\Phi$ 同时运输全效应和全域范数。正直径等价已由118.5—118.6证明。证毕。

定理118.12还独立说明：若完整球真能整体塌缩，失去的并非单个读数趋零，而是固定零测试到邻近精确零纤维之间保持正距离。
只需每条边的一张稳定完整零确认就能阻止这一障碍；所有法向均稳定、连续选择和任何修复率均可从候选前件删除。
相较要求全部零效应Hölder修复的版本，所删除的是量词、速率和选择要求；强版本蕴涵(WZ)，但这里没有给出全EB3域中严格分离它们的模型。
主候选进一步用(O)表达同一缺口，效应范数只留在这一等价解释中。

$$
\boxed{\mathrm{EB3}+\mathrm{Inj}:\qquad
\mathrm{(O)}\ \Longleftrightarrow\ \mathrm{(WZ)}
\Longleftrightarrow\ \inf_p\operatorname{diam}D_p>0
\Longleftrightarrow\ \text{同锥同单位 }H_3(\mathbb C).}
\tag{IX118.22}
$$

### 118.7 宽度饱和集、忠实紧层与全局最大值

本节记完整球的标签纤维为 $I(F)=\{p\in P:D_p=F\}$；它不同于原二元关联 $\mathcal I$。

**定理 118.14（饱和集与近饱和极限）。** 仅在 $\mathrm{EB}_{\ge1}$ 原域，令

$$
W(F)=\max_{f\in\mathcal E}(\max_Ff-\min_Ff),\qquad
\mathscr S=\{p\in P:W(D_p)=1\}.
\tag{IX118.23}
$$

每个非点完整球满足 $0<W(F)\le1$。$\mathscr S$ 是 $K$ 中的紧集。
若 $W(D_{p_j})\to1$，则存在子列 $p_{j_k}\to p\in\mathscr S$。
因此

$$
\mathscr S=\varnothing\quad\Longrightarrow\quad
\sup_{p\in P}W(D_p)<1.
\tag{IX118.24}
$$

证明。全部效应分离 $K$ 中不同点：将任何能分离两点的仿射函数按其全域最小、最大值归一，就得到原效应。
所以非点球的宽度严格正。$\mathcal E$ 紧使最大值达到，范围至多一。

对宽度趋一的序列，选达到宽度的 $b_j\in\mathcal E$、端点 $y_j,z_j\in D_{p_j}$，以及 $e_j\in\mathcal A_{p_j}$。
紧性使同一子列收敛为 $p_j\to x,y_j\to y,z_j\to z,b_j\to b,e_j\to e$，且

$$
e(x)=1,\quad e(y)=e(z)=0,\quad b(y)=1,\quad b(z)=0.
\tag{IX118.25}
$$

因此 $y\ne z$。有限正权纯分解 $x=\sum_i\lambda_i s_i$ 给 $y,z\in D_{s_i}$；全部这些球于是是同一球 $F$。
$b$ 在 $F$ 上已取一、零，故 $W(F)=1$。
116.4给这种饱和球不可能重复标签，即 $I(F)$ 单点；所以全部 $s_i$ 相同，$x=p\in P$，且 $D_p=F$、$W(D_p)=1$。
这同时证明近饱和子列命题和 $\mathscr S$ 的序列闭性。
若饱和集为空而上确界为一，取一条宽度趋一的序列会得到上述矛盾，故(IX118.24)成立。
没有预设全Inj、$P$ 闭或球连续。证毕。

**忠实标签下的正宽度紧层。**

**定理 118.15（紧层、上半连续与正最大值）。** 在 $\mathrm{EB}_{\ge1}+\mathrm{Inj}$ 下，对每个 $\varepsilon>0$，

$$
P_\varepsilon=\{p\in P:W(D_p)\ge\varepsilon\}
\tag{IX118.26}
$$

是 $K$ 中紧集，且

$$
P=\bigcup_{n\ge1}P_{1/n},\qquad
M:=\sup_{p\in P}W(D_p)=\max_{p\in P}W(D_p)>0.
\tag{IX118.27}
$$

$W(D_p)$ 在 $P$ 的相对拓扑上上半连续。
若 $p_j\to x\notin P$，则 $W(D_{p_j})\to0$，并且 $\operatorname{diam}D_{p_j}\to0$。

证明。设 $p_j\in P_\varepsilon,p_j\to x\in K$。
选 $b_j,y_j,z_j,e_j$ 如上，使
$b_j(y_j)-b_j(z_j)=W(D_{p_j})\ge\varepsilon$。
取共同子列后 $b(y)-b(z)\ge\varepsilon$，故 $y\ne z$；同一极限 $e$ 确认 $x$ 并零于 $y,z$。
$x$ 的纯分解中所有 $D_{s_i}$ 共同包含 $y,z$，因此相同；Inj迫使 $x=p$ 纯。
$y,z\in D_p$，于是 $W(D_p)\ge b(y)-b(z)\ge\varepsilon$。
这证明 $P_\varepsilon$ 在 $K$ 中闭而紧。

若一开始 $p_j\to p\in P$，只须取实现宽度上极限的子列，以上紧性与闭零关联就给

$$
\limsup_jW(D_{p_j})\le W(D_p).
\tag{IX118.28}
$$

这一步本身甚至不需Inj。每球宽度正给可数紧层覆盖。
$M>0$；取宽度趋 $M$ 的极大化序列，尾项位于紧层 $P_{M/2}$，其子列极限是纯点。
(IX118.28)使该点的宽度至少 $M$，故达到全局最大值。

若混标签聚点仍有一条子列宽度至少 $\varepsilon>0$，该子列位于紧 $P_\varepsilon$，矛盾。
若其球直径不趋零，取两点距离统一正的子列与共同零效应；同一有限纯分解和Inj论证会迫使聚点纯，仍矛盾。
这证明最后两项；没有把宽度趋零当作一个未经证明的直径估计。证毕。

**未决的最大值入口。** 在未加入(O)或(WZ)的EB3+Inj分支，(IX118.27)仅给 $0<M\le1$，尚未证明 $M=1$。
即使另证 $M=1$，也只先得到至少一张饱和球；从该球传播到每张球仍须证明，不能将全局最大值误写为全部球的最小值。
仅EB3推出Inj、仅EB3推出W1、以及EB3+Inj推出边见证稳定或正直径下界，均未由本章解决。
118.14说明完全无饱和时必有统一上缺口；118.15说明忠实标签分支中混标签聚点只可能伴随球整体塌缩。
这些是宽度路线的实质约束，不是 $M=1$ 或W1的替代证明。

### 118.8 球与球柱相交的实际零测试失稳边界

**例 118.16（完整效应域中的塌球，但不满足全称EB3）。** 固定单位 $a\in\mathbb R^3$，取

$$
\begin{split}
V_0&=\mathbb R\oplus\mathbb R^3\oplus\mathbb R^3,\qquad u_0(t,Z,Y)=t,\\
C_0&=\{(t,Z,Y):\sqrt{|Z|^2+|Y|^2}\le t,\quad |Y-ta|\le t\},\\
K_0&=\{(z,y):|z|^2+|y|^2\le1,\quad |y-a|^2\le1\}.
\end{split}
\tag{IX118.29}
$$

$C_0$ 闭、凸、尖；$t=0$ 仅给零向量，故 $u_0$ 严格正。
$(t,Z,Y)=(1,0,a/2)$ 使两不等式严格，所以锥生成整个 $V_0$。
$K_0$ 是其整个归一基，原全部纯点准确为

$$
P_0=K_0\cap S^5.
\tag{IX118.30}
$$

球面上的点因外部六维欧氏球严格凸而极端；外球内部点可沿 $z$ 的非零方向作小幅正负扰动，保持两约束，故不极端。

全部原效应也可完整写出，而无需限制菜单。定义

$$
\begin{split}
L_0&=\{y:|y|\le1,\ |y-a|\le1\},\\
\sigma_0(v,w)&=\max_{y\in L_0}\bigl(|v|\sqrt{1-|y|^2}+w\cdot y\bigr).
\end{split}
$$

任意原线性读数 $f(t,Z,Y)=\alpha t+v\cdot Z+w\cdot Y$ 属于整个 $\mathcal E_0$ 当且仅当

$$
\sigma_0(-v,-w)\le\alpha\le1-\sigma_0(v,w).
\tag{IX118.31}
$$

这是对每个允许的 $y$ 先在整个 $z$ 球上取极值所得的精确支持函数公式；没有只列一族效应就称它为全部。

全部非点真面准确为

$$
F_n=\{(z,a+n):|z|\le\sqrt{1-|a+n|^2}\},\qquad
|n|=1,\quad a\cdot n<-\tfrac12.
\tag{IX118.32}
$$

它们都是整个三球，其余非空真面为原纯单点。
确实，任一非点暴露面取两不同点的中点。外球严格凸使该中点在外球内部；它仍在 $K_0$ 边界，故只能在球柱边界。
此处支撑法向为 $(0,n)$，切出的整个面就是(IX118.32)；非点性等价于半径正。
任意非暴露真面取相对内点的支撑面，便被包含于这样一个暴露面；三球的非点面只有整个自身，所以同样得到这份穷尽分类。
这项面分类并不等于所有完整 $D_p$ 都是三球。

取 $|n|=1,a\cdot n<-1/2$，记

$$
p_n=(0,-n),\qquad m_n=1+a\cdot n.
$$

$p_n$ 仅激活外球约束，球柱约束严格。因此全部确认效应恰为

$$
f_\tau(z,y)=1-\tau(1+n\cdot y),\qquad
0\le\tau\le\frac1{1+m_n}.
\tag{IX118.33}
$$

理由是确认效应在 $p_n$ 达到全域最大值，唯一外法向射线给该形式；$n\cdot y$ 的全域最大值为 $m_n$、最小值为 $-1$，非负性恰给所列上界。
逐点最小化全部确认，得到整个

$$
T_{p_n}(z,y)=\frac{m_n-n\cdot y}{1+m_n},\qquad
D_{p_n}=F_n.
\tag{IX118.34}
$$

同理，在 $p_n$ 为零的全部原效应恰为

$$
Z_{p_n}=\{g_\tau(z,y)=\tau(1+n\cdot y):0\le\tau\le(1+m_n)^{-1}\}.
\tag{IX118.35}
$$

现在取 $a,b$ 正交单位向量、$0<\varepsilon_j<1/2$、$\varepsilon_j\downarrow0$，令

$$
\begin{split}
n_j&=(-\tfrac12-\varepsilon_j)a+
\sqrt{1-(\tfrac12+\varepsilon_j)^2}\,b,\\
p&=(a-\sqrt3b)/2,\qquad q=(a+\sqrt3b)/2,\\
p^*&=(0,p),\qquad q^*=(0,q).
\end{split}
\tag{IX118.36}
$$

则 $|a+n_j|^2=1-2\varepsilon_j$，故

$$
\operatorname{diam}D_{p_{n_j}}=2\sqrt{2\varepsilon_j}\to0,\quad
p_{n_j}\to p^*,\quad D_{p_{n_j}}\to\{q^*\}.
\tag{IX118.37}
$$

不能漏算极限标签的完整 $D$。在 $p^*$，两条激活法向是 $(0,p)$ 与 $(0,-q)$。
支撑法向为它们的非负组合：两约束有共同严格内点，其严格下降方向稠密于两半空间给出的切锥，取极锥就得到该法向锥。
所以全部确认效应为

$$
f_{\lambda,\mu}(z,y)
=1-\lambda(1-p\cdot y)-\mu(\tfrac12+q\cdot y),\qquad
\lambda,\mu\ge0,\quad\lambda+\mu\le\tfrac23.
\tag{IX118.38}
$$

$p\cdot q=-1/2$。两个括号在整个 $K_0$ 均属于 $[0,3/2]$，并且在 $q^*$ 同时等于 $3/2$；所以非负性充分必要地恰为 $\lambda+\mu\le2/3$。
对这个完整参数单纯形取逐点最小，得到

$$
T_{p^*}(z,y)=\min\left\{\frac{1+2p\cdot y}{3},\frac{2-2q\cdot y}{3}\right\},\qquad
D_{p^*}=\{q^*\}.
\tag{IX118.39}
$$

第一支的零须 $p\cdot y=-1/2$，球柱的支持等号迫 $y=a-p=q$；第二支的零须 $q\cdot y=1$，外球等号同样迫 $y=q$。
两者都使 $z=0$。交换 $p,q$ 亦得 $D_{q^*}=\{p^*\}$。
因此全称EB3在这两个实际原纯标签处失败，尽管(IX118.34)中每颗球都是完整三球。

仍有真实固定零测试的失稳。取

$$
h_0(z,y)=\frac{1+2q\cdot y}{3}\in\mathcal A_{q^*}.
$$

它在 $q^*$ 读一、在整个 $D_{q^*}$ 读零，且 $h_0(p_{n_j})\to0$。
对原态 $w_0=(0,0),w_1=(0,a)\in K_0$，有

$$
2h_0(w_1)-h_0(w_0)=1,
\qquad
2g_\tau(w_1)-g_\tau(w_0)=-2\tau\varepsilon_j\le0
\quad(g_\tau\in Z_{p_{n_j}}).
$$

由于 $|2f(w_1)-f(w_0)|\le3\|f\|_{K_0}$，可得

$$
\operatorname{dist}_{K_0}(h_0,Z_{p_{n_j}})\ge\tfrac13.
\tag{IX118.40}
$$

所以读数趋零本身不保证全效应范数下可修复为精确零。
该模型完整呈现这种边界现象，却不是EB3或EB3+Inj的反例；没有把极限标签的单点 $D$ 隐藏，也没有声称可将它补成满足全称EB3的模型。

### 118.9 原静态字典、反事实与尚缺的关系

定理118.8及推论118.13接回116.17、VIII113.9的同一个 $\Phi$，恢复整个原静态模型：

| 原对象或现有量子公理 | 同原锥、同原单位后的对应 |
| --- | --- |
| 全部纯态与复相位射线 | $P=\{\Phi(vv^*):v^*v=1\}\cong\mathbb{CP}^2$；表示空间为 $\mathbb C^3$ |
| 全部混态及混合 | $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$；保持全部凸组合 |
| 全效应与Born概率 | $f_A(\Phi\rho)=\operatorname{Tr}(A\rho)$，恰含全部 $0\preceq A\preceq I_3$ |
| 原确认与最低确认 | least为 $vv^*$；$T_{\Phi(vv^*)}(\Phi(ww^*))=|v^*w|^2$ |
| 正交与三元共同完成 | 原正交对唯一补成三个正交秩一投影；原三效应全域非负且和为 $u$ |
| 全部有限数学测量 | 原 $f_j\ge0,\sum_jf_j=u$ 恰对应全部有限POVM $A_j\succeq0,\sum_jA_j=I_3$ |
| 谱分解 | 全部密度态 $\rho=\sum_{i=1}^3\lambda_iP_i$，$\lambda_i\ge0,\sum_i\lambda_i=1$ |
| 原单位、派生中心与共同尺 | $u\Phi=\operatorname{Tr}$、$\Phi(I_3/3)$、$B(\Phi X,\Phi Y)=\operatorname{Tr}(XY)$ |

这些是完整条件成立后的静态后果；原域中没有预装Hilbert空间、Born模方、共同物理内积或正交谱分解。
三元共同完成在取得Pair之后才用旧joint接口，全域正性由(IX118.12)的原证明支付。
成熟Jordan分类与静态字典复用VIII113.9；原边界拓扑、环乘法与支持对偶复用116.12—116.16，均不另计为新分类。
来源版本为[5f749ade652957c89e6b8b8d7799e7e5e4947903][Q118Pin]中的对应原证明。
原关系下半连续、投影开放及有限维椭球参数方法属于成熟工具；本章的专用桥由118.2—118.7直接推导。
全部新增数学陈述为纸面推导，没有Lean核验，也没有全球原创或文献检索穷尽声明。

**反事实与准确未决项。** 在完整EB3+Inj域中，若球列整体缩成一点，118.12必给同一原边及同一趋近序列，使该边所有固定完整零确认都保留正修复距离；118.5同时说明原边开放性必失败。
反之，每边仅一张稳定零见证已足够，或者直接要求每条原边对邻近第一端有邻近正交第二端；无须把所有零法向、速率或选择一并加入。
(O)失败的准确含义是存在 $(p,q)\in\mathcal I$、$p_n\to p$ 及一个 $q$ 的相对邻域，使某条子列的全部 $S(D_{p_n})$ 都避开它；上关联本身不排除这种纤维缺失。
例118.16还说明读数趋零不等于效应可修复，但它在极限标签处失败全称EB3，不能反驳主候选，也不能证明完整EB3允许失稳。

尚未解决的是裸EB3是否自动给Inj和(O)，或EB3+Inj是否已经排除118.12的固定零测试障碍。
本章既未证明自动性，也没有满足全部原条件的反模型，故不能作逻辑独立或不可能性判断。
宽度路线中，忠实标签下最大值真实达到，却仍未证明 $M=1$；即使取得一张饱和球，也不能未经传播证明便当作W1。
本章的主候选用原二元关系表达缺口，所减少的是法向表述负担，并非相对116.17的独立前提数量。

完整同原量子起源目标还保留VIII113.11的独立操作、复合与时间合同：共同来源域，全部有限份实际载体与张量锥和单位，每个分块的min/max界、因子置换与重括号，实际纠缠准备，具名低二份桥与同一最大块条件，全部合法未来及切口，全旁观者正性到CP/Kraus的接口，逐输入TP/TNI预算，同事件完整提升，同族仪器、记录与粗粒化，正质量条件归一、Lüders校准，以及原钟、连续动态来源、单位与 $\hbar$。
静态三结果效应族不自动成为可调用的实际仪器，原二元关联上的交换也不自动成为整个态空间的物理可逆变换。
单体秩三条件不施加到高秩复合载体，这些合同也不能打包后算作一个已被推出的前提。

白话说，起点仍是所有原状态、所有原纯点和所有原测试。每个纯点背后的完整排除集合是一整颗三维实心球，不同纯点不能共用同一个球标签。新的主要求直接落在正交关系上：一条已经存在的正交边，轻轻移动一端时，总能在另一端附近找到仍然正交的点。不必预先知道法向怎样变化，也不用指定多快靠近或连续选哪一点。

这个要求先使整颗排除球连续变化。若球缩成一点而标签仍纯，会与该标签本来的完整三球冲突；若标签变混，就把边的两端交换，发现这个混点本来应在交换后球的内部，却又由球面极限被迫落在球面上。整体塌缩因此不可能。只要球直径有正下界，纯点的极限就仍纯；再压扁一轴或两轴，会迫使整块极限盘都成为纯点，而盘内的中点明明能混合，所以这种压扁也不可能。真实连续球丛由此取得，继而接上整个原凸边界的拓扑和环乘法约束：空间被迫九维，球面之间不能互相躲开，交点补出第三纯点和共同三结果，最后得到复三能级的全部状态、效应、Born概率、有限数学测量与谱分解。

固定零测试提供同一缺口的另一幅图景：每条边只要有一张完整零确认，能够对邻近纯输入作任意小的全域修复，就足以保证上述原边稳定；反过来，取得同原量子表示后，直接压缩矩阵就能完成修复。若真有塌球，必有一条原边使所有这样的固定测试都离精确零测试保持一段正距离。这里已经删掉Hölder率、全部法向量词和连续选择，但没有证明裸球形必然禁止这种失稳，也没有比116.17少用独立条件。宽度的正层和饱和集已经紧，最大宽度也确实达到；它必为一以及一张饱和球如何传播到全部球仍未解决。实际操作、复合、仪器和时间继续需要各自的原合同。因此得到的是一套以原二元关系开放性为入口的完整条件静态重构，原完整量子起源问题的剩余桥仍清楚保留。

[Q118IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "116.1—116.8原面、标签与宽度；116.11—116.17三轴非塌缩、真实球丛、拓扑环及同原静态重构。"
[Q118VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2完整原面证明；VII104.2—104.3在Pair之后的原对径与全域三结果共同完成。"
[Q118VIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "VIII113.8—113.9同原锥同原单位复三能级及全静态字典；VIII113.11完整操作、复合与过程合同。"
[Q118Pin]: https://github.com/the-omega-institute/trureturing/tree/5f749ade652957c89e6b8b8d7799e7e5e4947903 "所引116、VII103—104、VIII113原证明的固定来源版本。"

## 追加锚（本行以下为增补区）

## 119. 完整厚排除球的四纯态失败证书与端点剖面

**命题 119.1（EB下的有限原支撑与零维或整球端点）。** 取定义114.1的同一个非零有限维实空间 $V$、
闭尖生成凸锥 $C$、严格正单位 $u$、整个归一基 $K$、全部原纯点 $P=\operatorname{ext}K$
及整个原效应区间 $\mathcal E=[0,u]_{C^{\ast}}$。只要求完整厚球条件

$$
\forall s\in P\ \exists d_s\in\mathbb N,\ d_s\ge2:\qquad
D_s\simeq_{\mathrm{aff}}B^{d_s}.
\tag{IX119.1}
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
\tag{IX119.2}
$$

这里 $|\cdot|_F$ 是这张完整仿射球的内在欧氏范数。
令 $\mathrm A(F)$ 表示每个 $|n|_F=1$ 的对径 $c+n,c-n$
都能由某张原 $h\in\mathcal E$ 分别取一和零。
若 $\mathrm A(F)$ 失败，则可在同一个 $F$ 中重新选取原纯对径 $q_*,r_*$，
以及 $\lambda>1$、$a,b\in K$ 和同一张 $e\in\mathcal E$，满足

$$
\lambda(q_*-r_*)=a-b,\qquad e(a)=1,\qquad e(b)=0.
\tag{IX119.3}
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
\tag{IX119.4}
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
\tag{IX119.5}
$$

同一个原全单位效应 $e$ 在每个正权 $x_i$ 上取一，在每个正权 $y_j$ 上取零。
允许重复纯点与零权项；零权项不承担读数要求。
“至多四个”仅计 $a,b$ 的纯分解支撑，不把标签 $p,q_*,r_*$ 算入这个数。

若 $h_+=\dim G(a)$、$h_-=\dim G(b)$，则

$$
m\ge d+h_++h_-.
\tag{IX119.6}
$$

特别地，若所有完整排除球均为三球，则

$$
(h_+,h_-)\in\{(0,0),(0,3),(3,0),(3,3)\},\qquad
m\ge3+h_++h_-,
\tag{IX119.7}
$$

因而在所选实现中两端均混蕴含 $m\ge9$，即 $\dim V\ge10$。
纯端点分支仍保留，这个条件维数界没有把两端均混作为EB的后果。

反之，对同一原球 $F$ 的任意对径 $q,r$，只要存在 $\lambda>1$ 及(IX119.5)形状的
原纯态凸分解恒等式，就不存在原 $h\in\mathcal E$ 在 $q,r$ 分别取一和零。
这个反向障碍不另需假定分解支撑已具有共同饱和效应。

证明。先明确所复用的前件范围。
[VII103.2，式(VII103.4)—(VII103.5)][Q114FaceExhaustion]仅用完整 $\mathrm{EB}_{\ge1}$，
便给所有非空原真面恰为纯单点或整张 $D_s$，且每张 $D_s$ 为非点紧暴露极大真面。
本处(IX119.1)满足这一前件，毋须各 $d_s$ 相同。
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
(IX119.1)只描述各个完整 $D_s$，没有给这个额外前件。

具体地，令 $\gamma$ 为原差体 $K-K$ 在 $\ker u$ 上的Minkowski泛函。
[VII98.1，式(VII98.4)—(VII98.5)][Q114NormInterface]的同单位接口为

$$
\gamma(z)=\tfrac12\|z\|_C
=\max_{f\in\mathcal E}f(z)
=\min\{t\ge0:z=t(x-y),\ x,y\in K\},\qquad z\in\ker u,
\tag{IX119.8}
$$

最大值、最小值均达到。其成熟基范数／序单位对偶来源为
[Lami–Palazuelos–Winter，§II.1 Definitions 1—2、Lemma 3][Q114LPW]，
正是有限维原锥与完整 $[0,u]$ 的接口；不使用该文的双系统或受限测量条件。
这里系数 $1/2$ 来自 $u(z)=0$ 时正负质量相等。

由VI90.9，失败的某个对径 $q,r$ 满足 $\gamma(q-r)<1$。
达到的最小实现给 $q-r=t(x-y)$，其中 $0<t<1$，故

$$
Q=(K-K)\cap L(F),\qquad R=\max_{w\in Q}|w|_F>2.
\tag{IX119.9}
$$

$Q$ 紧凸且包含 $F-F=2B_F$。选达到 $R$ 的 $w$；平方内在范数的严格凸性使
$w\in\operatorname{ext}Q$，否则严格凸组合的平方范数小于 $R^2$。
在非空紧凸纤维

$$
M_w=\{(x,y)\in K\times K:x-y=w\}
\tag{IX119.10}
$$

中选一个极点 $(a,b)$。有 $\gamma(w)\le1$；若严格小于一，
(IX119.8)给 $w=s(x-y)$、$0<s<1$，使 $w/s\in Q$ 的长度大于 $R$，矛盾。
所以 $\gamma(w)=1$。取同一对偶极大效应 $e\in\mathcal E$，则
$1=e(w)=e(a)-e(b)$，原零一界迫 $e(a)=1$、$e(b)=0$。
置

$$
q_*=c+\frac wR,\qquad r_*=c-\frac wR,\qquad \lambda=\frac R2>1,
\tag{IX119.11}
$$

便得同一 $F$ 中的原纯对径和(IX119.3)。

最小面相对内部性质给 $a\in\operatorname{ri}G(a)$、$b\in\operatorname{ri}G(b)$。
包含 $a,b$ 的原暴露面 $K\cap\{e=1\}$、$K\cap\{e=0\}$
分别包含其最小面，因此 $e$ 在两面恒一、恒零；两面都是真面。
前述VII103.2分类现在给出恰好纯单点或整张原排除球的选择。
端点非纯时，其最小面不是单点，故为整球且端点在球的相对内部。
这一步保留了零维分支，没有以混合性填入额外假设。

为得到(IX119.4)，取 $v_+\in L(a)$、$v_-\in L(b)$，并假设
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
\tag{IX119.12}
$$

单射。将第二个方向换号即得所述直和，维数给(IX119.6)。
第一层消去差分移动，第二层才消去共同平移；二者针对同一个原实现。
在全三球情形，混端点最小面的维数恰为三，纯端点为零，遂得(IX119.7)及两端均混时的界。
它们只约束重新选出的最大方向与极端纤维端点，不是对每个失败方向或每种端点实现的断言。

最后在各端点的原最小面内作纯分解。
若 $a$ 纯，取 $x_1=x_2=a$、$\alpha=1$。
若 $G(a)=D_s=c_++A_+(B^{d_s})$，写 $a=c_++A_+(t n)$，
其中 $0\le t<1$、$\|n\|=1$；$t=0$ 时任选一个单位方向。
取

$$
x_1=c_++A_+n,\qquad x_2=c_+-A_+n,\qquad
\alpha=\frac{1+t}{2}.
\tag{IX119.13}
$$

球面极点是原 $P$ 中的点，且这两个原纯点的凸组合正是 $a$。
对 $b$ 用同样构造，得到 $y_1,y_2,\beta$，从而得到(IX119.5)。
这些支撑都取自各自的原最小面，故由(IX119.4)已具有同一个 $e$ 的饱和读数。
等价地，$e(a)=1$ 的凸平均与 $e(x_i)\le1$ 迫每个正权项取一，
$e(b)=0$ 与 $e(y_j)\ge0$ 迫每个正权项取零；零权项不参与这个推论。

反向若有(IX119.5)形状的恒等式，并有原 $h(q)=1$、$h(r)=0$，则原仿射性给

$$
\lambda
=\alpha h(x_1)+(1-\alpha)h(x_2)
 -\beta h(y_1)-(1-\beta)h(y_2)
\le1,
\tag{IX119.14}
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

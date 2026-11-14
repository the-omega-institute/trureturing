# QUANTUM ORIGIN: EXCLUSION SEGMENT RIGIDITY AND PURE LOCUS TOPOLOGY XII

本卷承接[前卷 XI](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md)的第134—144章；下文不带卷名前缀的既有第134—143章引用均指前卷。第145章给出完整零球的真实标签返回及其固定根严格高段应用，保留各条明列的完整原域与前件。本卷是普通数学散文，未经 Lean kernel 验证。

## 145. 完整零球的真实标签返回与固定根严格高段

### 145.1 全部原对象与显式根合同

**定义 145.1（完整原域、真实零确认与固定根）。** 取非零有限维实空间 $V$、闭尖生成凸锥
$C\subset V$，以及在 $C\setminus\{0\}$ 上严格正的 $u\in V^\ast$。始终使用

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
C^\ast=\{f\in V^\ast:f(C)\subseteq\mathbb R_+\},\qquad
\mathcal E=[0,u]_{C^\ast},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(z)=\min_{f\in\mathcal F_p}f(z),\qquad
D_p=\{z\in K:T_p(z)=0\},\qquad S_p=P\cap D_p.
\end{gathered}
\tag{XII145.1}
$$

标签 $p$ 遍历全部 $P$，第二端点 $z$ 遍历整个 $K$。$K,\mathcal E,\mathcal F_p$ 的紧性与 minimum 达到沿用
[IX114.1—114.2][Q145IX]、[X133.1][Q145X]；确认族不缩成某个预选效应族。
以下 EB3 总指对每个原 $p\in P$，整个 $D_p$ 都仿射等价于完整闭三球。
纯零关系 $p\perp r\Longleftrightarrow T_p(r)=0$ 由补效应对称，且反自反。
纯 PR 则另指全部纯对的 $T_p(r)=T_r(p)$，不交换混态上的正读数。

复用 IX114.2、IX120.1、X133.1 的原面接口：每个 $D_p$ 是非点紧暴露极大真面，
$S_p=\partial_{\rm rel}D_p\cong S^2$，$D_p=\operatorname{conv}S_p$；
不同完整球的交为空或一个原纯单点，全部非空真面只有这些球与原纯单点。
记 $c_p$ 为 $D_p$ 的唯一中心，$I(F)=\{p\in P:D_p=F\}$，并记

$$
\mathcal A_p=\{e\in\mathcal F_p:K\cap\ker e=D_p\}.
\tag{XII145.2}
$$

此族非空。具体地，在 $c_p$ 取一张达到 $T_p(c_p)=0$ 的原效应 $e$；对任意
$z\in D_p$，其球心反射 $z'=2c_p-z$ 仍在 $D_p$，非负性与
$0=e(c_p)=(e(z)+e(z'))/2$ 使 $e$ 零于整个球。反向由 $0\le T_p\le e$ 得到准确零集。
这只是上述真实暴露接口的复用，不把 $e$ 说成全部确认效应的 least。
同样复用球上极值事实：若一张原效应在同一完整球的两点取一、零，这两点必是球的对径纯点。

在所有目标之前固定原 $o\in P$，置

$$
A=D_o,\qquad S=S_o,\qquad B=\bigcup_{s\in S}D_s,\qquad
w=o+2c_o.
\tag{XII145.3}
$$

这里 $w\in V$ 且 $u(w)=3$，不是归一状态；$B$ 收齐每个末球的全部混态。

**定义 145.2（根合同、局部带与关联的合法域）。** 显式根合同 $R_o$ 包含以下条件：
对每个 $s\in S$ 有原纯点 $a_s$，使 $(o,s,a_s)$ 是真实零三角；
$I(A)=\{o\}$ 且 $I(D_s)=\{s\}$ 对每个 $s\in S$ 成立；
$B$ 紧，$o\in B$ 且 $S\subseteq B$。三角的每条边均由同一完整原菜单内的效应见证。
这些是根与根邻点的条件，不包含 $P\subseteq B$、全 Pair 或全局 Inj。

在 $R_o$ 下，真实共同邻点只在已知覆盖的域上定义：

$$
\begin{gathered}
\pi_o:(P\cap B)\setminus\{o\}\longrightarrow S,\\
\{\pi_o(x)\}=A\cap D_x
=\{s\in S:o\perp s,\ x\perp s\}.
\end{gathered}
\tag{XII145.4}
$$

确实，$x\in B$ 给共同邻点存在；$x\ne o$ 与 $I(A)=\{o\}$ 给 $D_x\ne A$，
故点交接口给唯一性及纯性。根三角还迫 $a_s=2c_o-s$。
这个定义没有给尚未知属于 $B$ 的目标预取 $\pi_o(q)$。

局部条件 $L_\varepsilon(o)$ 是 X132.3 在这个固定根、同一个阈值上的原条件：

$$
\begin{gathered}
0<\varepsilon<1,\qquad
\forall z\in P:\quad 0<T_o(z)<\varepsilon\ \Longrightarrow\\
\exists s\in P:\ T_o(s)=T_z(s)=0.
\end{gathered}
\tag{XII145.5}
$$

它经零对称恰给该小正带的纯目标进入 $B$，不预付其余目标。
$L_\varepsilon(o)$ 单列供根合同的来源与高段消费者使用；下面的返回计算只用 $R_o$。

### 145.2 两球效应计算、原对径回送与分离裕量消去

**定理 145.3（保留邻边完成的单对真实标签返回）。** 在完整 EB3 与 $R_o$ 下，取

$$
q\in P\setminus(A\cup\{o\}),\qquad S_q\subseteq B.
\tag{XII145.6}
$$

此时 $h_q=\pi_o|_{S_q}:S_q\to S$ 是同胚；记 $x_s=h_q^{-1}(s)$。
另要求目标的全部真实邻边完成条件

$$
C_q:\quad \forall s\in S\ \exists y_s\in P:
\quad (s,x_s,y_s)\text{ 是真实零三角}.
\tag{XII145.7}
$$

若有一对满足反向纯比较

$$
\exists s_\ast\in S:\quad T_q(s_\ast)\le T_{s_\ast}(q),
\tag{XII145.8}
$$

则对任意真实 $e_o\in\mathcal A_o$、$e_q\in\mathcal A_q$，都有

$$
e_q(w)=1,\qquad q+2c_q=w,\qquad e_q(o)=e_o(q),\qquad
\min_{z\in A}e_q(z)=0,\qquad D_q\cap A\ne\varnothing,\qquad q\in B.
\tag{XII145.9}
$$

仅有根边 $(o,s)$ 的完成不能删除 $C_q$；后者完成的是另一条实际边 $(s,x_s)$。

证明。先说明复用 X133.5 的关联步骤在当前域内合法。
由 $q\notin A$ 及零对称，$o\notin S_q$；(XII145.6) 因而让整个 $S_q$ 落在
(XII145.4) 的定义域内。紧集

$$
\{(x,s,f)\in S_q\times S\times\mathcal E:f(s)=1,\ f(x)=0\}
\tag{XII145.10}
$$

在 $S_q\times S$ 上的投影正是 $h_q$ 的单值图。该图到 $S_q$ 是紧到 Hausdorff 的连续双射，
故 $h_q$ 连续。若两点同映到 $s$，它们都在 $D_q\cap D_s$；
$I(D_s)=\{s\}$ 与 $q\notin A$ 排除 $D_q=D_s$，点交接口遂给单射。
两端都是完整、紧、无边界的二维球面。区域不变性使连续单射的像开，紧性使像闭，
目标连通使其满射，所以为同胚。这是 [Hatcher，印刷页172，Theorem 2B.3、Corollary 2B.4][Q145H]
及 X133.5 的同一应用。它只支付完整极值范围，不直接支付两球相交。

固定上述真实 $e_o,e_q$，记

$$
\alpha=e_q(w),\qquad r=e_q(o),\qquad d=e_o(q),\qquad
t_s=e_q(s),\qquad b_s=e_o(x_s).
\tag{XII145.11}
$$

$q\notin A$ 给 $d>0$；若 $r=0$，则 $o\in D_q$，零对称会给 $q\in A$，故 $r>0$。
根三角中 $s,a_s$ 在 $A$ 内对径，$o,a_s$ 在 $D_s$ 内对径；因此
$s+a_s=2c_o$、$o+a_s=2c_s$。再用 $C_q$ 中的三角，得到

$$
s+2c_s=w,\qquad x_s+y_s=2c_s,\qquad s+y_s=2c_{x_s},\qquad
x_s+2c_{x_s}=w.
\tag{XII145.12}
$$

最后一个等式尚未涉及 $q$ 的球心，不能以 $q+2c_q=w$ 代替它。

在第一张完整球 $D_s$ 上取单位球坐标，令 $o$ 的坐标为 $v_s$、$x_s$ 的坐标为 $z_s$。
它们均为单位向量。真实 $e_o$ 在 $o,a_s$ 取一、零，所以其整个球上限制为
$(1+v_s\cdot z)/2$。真实 $x_s\in D_q$ 使 $e_q(x_s)=0$，而 $e_q(o)=r>0$；
非负仿射函数在球面零点的方向唯一，结合 $e_q(2c_s)=\alpha-t_s$ 得

$$
e_q(c_s+L_s z)=\frac{\alpha-t_s}{2}(1-z_s\cdot z),\qquad
b_s=\frac{1+v_s\cdot z_s}{2},\qquad
r=(\alpha-t_s)(1-b_s).
\tag{XII145.13}
$$

这里 $L_s$ 是该球图的线性部分；$\alpha-t_s>0$ 且 $1-b_s>0$，由 $r>0$ 保证。
这一步用整个 $D_s$ 上的原效应界，未以任意横截球替代 $D_q$。

真实零关系 $x_s\in D_q$ 经零对称使 $q\in D_{x_s}$，从而进入第二张完整球
$G_s=D_{x_s}$。$s$ 也在该球内。其中心满足 (XII145.12)，故 $e_q$ 的中心值为
$\alpha/2$；$q$ 是其取值一的球面点，因而整个球的最小值是 $\alpha-1$。
效应界给 $1\le\alpha\le2$。令 $\widehat q,\widehat s$ 为在这张球内的单位坐标，便有

$$
\begin{aligned}
e_q(c_{x_s}+L_{x_s}z)
 &=\frac\alpha2+\frac{2-\alpha}{2}\widehat q\cdot z,\\
e_o(c_{x_s}+L_{x_s}z)
 &=\frac{1-b_s}{2}(1-\widehat s\cdot z),\\
(2-\alpha)d&=(1-t_s)(1-b_s).
\end{aligned}
\tag{XII145.14}
$$

第二式使用 $e_o(s)=0$、$e_o(w)=1$ 及 $b_s<1$；第三式在同一球内分别于 $s,q$ 评价得到。
若 $\alpha=2$，第一式使每张 $G_s$ 上 $e_q\equiv1$，于是 $t_s=1$ 对全部 $s\in S$ 成立。
$A=\operatorname{conv}S$ 遂给 $e_q(c_o)=1$，但
$r=\alpha-2e_q(c_o)=0$，矛盾。因此

$$
1\le\alpha<2,\qquad
r(1-t_s)=(2-\alpha)d(\alpha-t_s)\quad(s\in S).
\tag{XII145.15}
$$

在使用反向比较之前，可准确看出正分离障碍：若 $t_s$ 取两个不同值，比较最后一个一次等式的系数与
常数项，得到 $r=(2-\alpha)d=\alpha(2-\alpha)d$，故 $\alpha=1$。
若 $\alpha>1$，只能有 $e_q|_A\equiv m$。第一式 (XII145.13) 及 $h_q$ 满射还给
$e_o|_{D_q}\equiv m/(\alpha-m)$，并有

$$
r=\alpha-2m>0,\qquad \alpha-1<m<\frac\alpha2,\qquad D_q\cap A=\varnothing.
\tag{XII145.16}
$$

其中 $m\ge\alpha-1$ 来自 $s\in G_s$ 与 (XII145.14) 的最小值。
若等号成立，$s$ 是 $q$ 在 $G_s$ 内的对径；$C_q$ 又使 $y_s$ 是 $s$ 在同一球的对径，
所以 $q=y_s\perp s$，与 $e_q(s)=m=\alpha-1>0$ 矛盾。
这些是正数分支的必要关系，不是满足整个原域的反模型。

现在由 (XII145.8) 排除该障碍。对任一完整球 $G$ 与其中的原纯点 $z$，
IX114.5 的证明中不使用 PR 的 (IX114.15)—(IX114.16) 给出

$$
T_z(c_G+L_G v)=1-\kappa_G(z)(1-\widehat z\cdot v),\qquad
0\le\kappa_G(z)\le\frac12.
\tag{XII145.17}
$$

原因是每张确认 $z$ 的原效应在整个球上必形如
$1-\lambda+\lambda\widehat z\cdot v$，$0\le\lambda\le1/2$；紧确认族中的最大 $\lambda$ 达到，
并同时实现球内所有 $v$ 的 minimum。这里并未使用 PR 才能得到的“各方向系数相同”。

在 $G_{s_\ast}$ 中，$C_q$ 给 $s_\ast,y_{s_\ast}$ 的真实正交对径，
所以 $\kappa_{G_{s_\ast}}(s_\ast)=1/2$。又 $q\ne s_\ast$，于是

$$
T_q(s_\ast)-T_{s_\ast}(q)
=\left(\frac12-\kappa_{G_{s_\ast}}(q)\right)
(1-\widehat q\cdot\widehat{s_\ast})\ge0.
\tag{XII145.18}
$$

反向不等式使其为零，后一因子严格正，故 $\kappa_{G_{s_\ast}}(q)=1/2$。
$q$ 的这张球内对径因而有原最低值零，属于真实 $D_q$；
在它上面，(XII145.14) 的真实 $e_q$ 取值 $\alpha-1$，准确零集迫 $\alpha=1$。
(XII145.13)—(XII145.14) 随即给 $d=r$，因为 $1-t_s>0$：若 $t_s=1$，第一式将给 $r=0$。

对任意 $s\in S$，此时才取

$$
q_s^-=2c_{x_s}-q=w-x_s-q.
\tag{XII145.19}
$$

它是 $G_s$ 的原纯对径点，且 $e_q(q_s^-)=\alpha-1=0$。
先由准确零集得 $q_s^-\in D_q$，再注意 $x_s\in D_q$ 且 $q_s^-\in D_{x_s}$。
二者原正交，在同一完整球 $D_q$ 内互为对径，因此

$$
2c_q=x_s+q_s^-=w-q.
\tag{XII145.20}
$$

这是真实标签的回送：球心关系是零值与原正交推出的结论，不是输入。

还须消去 $A$ 与 $D_q$ 之间的可能正间隔。写完整根球
$A=c_o+L_A\overline{\mathbb B}^{\,3}$，置

$$
m=e_q(c_o),\qquad v=\|e_q\circ L_A\|_2,\qquad
0\le v\le m<\frac12,\qquad r=1-2m.
\tag{XII145.21}
$$

非负性给 $v\le m$，$r>0$ 给严格上界。由 (XII145.20)、$e_o(w)=1$ 及 $d=r$，
$e_o(c_q)=(1-d)/2=m$。$s$ 遍历完整 $S$ 时，$t_s$ 遍历整个区间
$[m-v,m+v]$；第一球恒等式给

$$
b_s=1-\frac r{1-t_s}.
\tag{XII145.22}
$$

此函数随 $t_s$ 严格递减。$m+v\le2m<1$ 保证全部分母严格正；
$s\mapsto x_s$ 遍历完整 $S_q$，所以 $e_o$ 在整个 $D_q$ 上的两个极值恰为

$$
\min_{D_q}e_o=\frac{m-v}{1-m-v},\qquad
\max_{D_q}e_o=\frac{m+v}{1-m+v}.
\tag{XII145.23}
$$

这里满射只用于保证真实球面的两个极值都被取遍。
仿射函数在完整球上的极值和等于中心值的两倍，故

$$
\frac{m-v}{1-m-v}+\frac{m+v}{1-m+v}=2m,
\qquad 2(1-m)(m^2-v^2)=0.
\tag{XII145.24}
$$

第二式是第一式乘以正数 $(1-m)^2-v^2$ 后的结果。
$m\ge v\ge0$、$m<1/2$ 迫 $m=v$，于是 $\min_Ae_q=m-v=0$。
最小值在紧 $A$ 达到，真实零集给 $D_q\cap A\ne\varnothing$。
$I(A)=\{o\}$ 与 $q\ne o$ 排除 $D_q=A$，故交恰为原纯点 $s\in S$。
零对称将 $s\in D_q$ 送回 $q\in D_s\subseteq B$，完成 (XII145.9)。证毕。

### 145.3 完整纯 PR 的逐项供应与同阈值高段

**推论 145.4（固定根小正条件下的条件返回及严格高段）。** 在定义145.1的整个原域中，假设
完整 EB3、完整纯 PR，以及对事先固定的同一个 $o$ 成立的 $L_\varepsilon(o)$。
则 $R_o$ 成立；对每个满足 (XII145.6) 的目标，$C_q$ 与 (XII145.8) 均成立，
因而具有定理145.3的全部真实标签返回结论。特别地，

$$
\{q\in P:0<T_o(q)<\varepsilon\}\ \cup\ S\ \cup
\{q\in P:T_o(q)>1-\varepsilon\}\ \subseteq B.
\tag{XII145.25}
$$

这里高段使用的正是 $L_\varepsilon(o)$ 的阈值，不另选更有利的阈值。

证明。先支付根合同，不调用 X133.6 的全覆盖结论。
固定 $S\cong S^2$，由 X130.2、X133.3 的同一紧见证投影，

$$
B=\operatorname{pr}_K
\{(s,z,f)\in S\times K\times\mathcal E:f(s)=1,\ f(z)=0\}
\tag{XII145.26}
$$

紧闭。零对称给 $o\in D_s$ 对任意 $s\in S$ 成立，故 $o\in B$。
$L_\varepsilon(o)$ 已经把全部原小正带目标送入这个固定 $B$。

逐点复用 X132.4 在 $p=o$ 的证明：若 $o$ 无真实三角，则 $A\cap B=\varnothing$。
否则从某个非空紧原面 $A\cap D_s$ 的极点取原纯点，就给 $o,s$ 的第三点。
紧效应区间使固定 $T_o$ 为一致 Lipschitz 效应族的 minimum，所以在紧 $B$ 上有
$\mu=\min_BT_o>0$。X132.2 供应原纯 $z$，满足
$0<T_o(z)<\min\{\mu,\varepsilon\}$；但 $L_\varepsilon(o)$ 又给 $z\in B$，矛盾。
因此根有一个真实三角，X133.2 的标签论证给 $I(A)=\{o\}$。
这一固定根反证只消费 $L_\varepsilon(o)$，没有把它提升成每根条件 $\mathsf L$。

该根三角在 $A$ 上给一条原效应读满一、零的直径。
现在使用 IX114.5 的完整纯 PR 共同刻度：$A$ 中某一纯方向的系数为 $1/2$，
故所有纯方向的共同系数都是 $1/2$。对每个 $s\in S$，原球内对径
$a_s=2c_o-s$ 遂满足 $T_s(a_s)=0$，从而 $(o,s,a_s)$ 是实际根三角。
X133.2 给每个 $I(D_s)=\{s\}$；同时 $s\in D_{a_s}\subseteq B$，故 $S\subseteq B$。
连同 (XII145.26) 与 $o\in B$，这逐项支付了 $R_o$。
关联的合法域与目标上完整球面的同胚性，已在 (XII145.4)、(XII145.10) 按这些根条件证明。
整个论证不需要给未覆盖目标定义 $\pi_o(q)$。

接着支付 $C_q$。对每个 $s\in S$，刚取得的根三角在 $D_s$ 上给 $o,a_s$ 的满刻度直径。
再次应用 IX114.5，$D_s$ 的共同系数为 $1/2$。
于是对每个 $x\in S_s$，其同一完整球内对径 $y=2c_s-x$ 满足 $T_x(y)=0$。
三点 $(s,x,y)$ 因而是原纯零三角。对实际的 $x=x_s$ 使用它，就给全部 $C_q$；
这一步并非把根三角本身改称邻边三角。
完整纯 PR 还对任一 $q,s$ 给 $T_q(s)=T_s(q)$，故任取一个 $s$ 即满足 (XII145.8)。
定理145.3现在给所有满足 $S_q\subseteq B$ 的上述目标返回。

最后只对严格高段支付该前件。若 $q=o$，已由 $o\in B$ 处理。
其余取 $q\in P$ 且 $T_o(q)>1-\varepsilon$，因 $\varepsilon<1$，有 $q\notin A$。
对任意 $x\in S_q$，取真实 $f\in\mathcal F_q$ 使 $f(x)=0$；
$u-f\in\mathcal F_x$。在同一个原纯根 $o$ 上评价，并且只对纯对使用 PR，得到

$$
T_o(q)+T_o(x)=T_q(o)+T_x(o)
\le f(o)+(u-f)(o)=1.
\tag{XII145.27}
$$

于是 $0\le T_o(x)<\varepsilon$。若为零，则 $x\in S\subseteq B$；若严格正，则
$L_\varepsilon(o)$ 给 $x\in B$。这对整个真实 $S_q$ 的每一点成立，所以 $S_q\subseteq B$，
定理145.3使 $q\in B$。小正带与 $S$ 的包含已逐项证明，得到 (XII145.25)。证毕。


第139章的拓扑与紧性结论仍未支付 $Q=P$ 或 $\mathsf{MC}$。
第140章在完整 EB3 之外另需 $\mathsf{ZC}$（或 $\mathsf{BC}$）、$\mathsf{Conn}$ 与 $\mathsf{Seed}$，才得到全域球心等式与 $\mathsf{MC}$。
该条件结论不供应本章不假设 $\mathsf{ZC}$ 或 $\mathsf{BC}$ 的真实标签返回定理。

### 145.4 适用边界与数学来源

**约定 145.5（未付区域、原菜单与复用范围）。** (XII145.25) 只包含所写的开比较带。
在 $T_o(q)=1-\varepsilon$ 时，(XII145.27) 只给 $T_o(x)\le\varepsilon$，
不能调用要求严格小于 $\varepsilon$ 的局部条件；等号点只有另行落在已付区域时才被覆盖。
未由 (XII145.25) 支付的中间读数只在 $0<\varepsilon\le1/2$ 时出现，其范围为
$[\varepsilon,1-\varepsilon]$；$\varepsilon>1/2$ 时两条开带重叠，中间范围为空。
在非空中间区，本章没有逐点支付整个 $S_q\subseteq B$，但另有该前件的目标仍可用定理145.3。
这些包含关系始终以同一固定根的 $L_\varepsilon(o)$ 为条件；没有证明 PR 自动供应
$L_\varepsilon(o)$、全 $\mathsf L$、一个全覆盖根、全 Pair 或原静态重构目标。
单对版本的 (XII145.8) 也不单独供应 $C_q$；(XII145.16) 不被宣称为完整原域反例。

XI134 的控制模型具有根与根邻完整球、横截球面满射，却在真实标签处出现球加纯弧的完整零集，
并失败全域 EB3 与 PR。因此它不在本章前件内；不能将其横截球面用作 $S_q$，
也不能用其控制结论取代这里真实标签 $q\in D_{x_s}$ 的步骤。
[THREE_COPY VIII131.3、131.5—131.6][Q145TC] 已有裸 EB3 的第三实心带紧性、
R3 条件下的三／五步奇返回，以及紧部分域 $E_q=S_q\cap B_2$ 上的真实连续单射。
这些结论不供应 $E_q=S_q$；本章的 (XII145.6) 仍明确要求整个原球面已落入 $B$。
[SAME_READBACK132.1][Q145SR] 的无 Inj 凸／径向全态覆盖，也不供应该前件或全 Pair。

第135章的 $\mathsf{MC}$ 要求同一原态的所有有限纯混合表达在球心替换后仍相等，
定理135.5以完整 EB3 加该全域混合相容条件取得同原静态分类。
这里既未假设 $\mathsf{MC}$，也未由局部返回推出它；该条件分类不替代定理145.3的局部推导。
第136章在实际连续仿射球心图与原球标签单射的额外前件下，以一张全效应的完全分离关系刻画全部原纯点，
并取得紧性及完整球的全轴统一间隙。其额外前件在本章未予假设；这里仍显式保留整个 $S_q\subseteq B$
与目标邻边完成 $C_q$，并在所列局部前件下进行保留真实标签的两球返回计算。
第137章的定理137.3在完整 EB3+$\mathsf{Conn}$ 与单个固定根的 $\mathsf G(o)$ 前件下，给出法向椭球、局部二步饱和与纯极限紧性；
其137.9仍把根三角与全覆盖另列为未付条件。本章不假设 $\mathsf{Conn}$ 或 $\mathsf G(o)$，
不从这些支持结论取得 $R_o$、整个 $S_q\subseteq B$ 或 $C_q$；返回链只消费定义145.2与定理145.3明列的前件，
完整纯 PR 分支另按推论145.4逐项支付。

第138章的候选是完整 EB3+$\mathsf{BC}$，其中 $\mathsf{BC}$ 只要求两条原纯混合弦的球心等式相容。
其138.2—138.6给逐球仿射球心图、内部截面、反射纯球、逐球直径下界及重复块障碍，
不供应 $\mathsf{MC}$、全域 Inj、全域非塌缩、$A_F=F$ 或全域球心拼接。
本章不假设 $\mathsf{BC}$，也不以这些逐球结论代付 $R_o$、整个 $S_q\subseteq B$、实际 $C_q$
或 (XII145.8) 的反向纯比较；推论145.4仍按其完整纯 PR 与同根 $L_\varepsilon(o)$ 逐项供应。

第141章的定理141.2在完整 EB3+$\mathsf{Conn}$ 与固定根的 $\mathsf G(o)$ 下，取得原对偶边界开片及整个原实空间的 $\dim_{\mathbb R}V=9$。
其141.3仍未取得 $Q=P$、$\operatorname{conv}Q=K$、$\mathsf{MC}$、全局 $\mathsf R_1$ 或 Jordan 分类。
本章不假设 $\mathsf{Conn}$ 或 $\mathsf G(o)$，也不从该条件结果取得 $R_o$、整个 $S_q\subseteq B$、$C_q$ 或反向纯比较。

第142章的定理142.2在完整 EB3+$\mathsf{Conn}$ 与同一固定根的 $\mathsf G(o)$ 下取得 $Q(o)=P$ 及同原复三能级锥；
第143章的143.4在完整 EB3+$\mathsf{Conn}$ 与全域统一二元可读差额 $\mathsf U$ 下取得同原完整静态分类。
本章不假设 $\mathsf{Conn}$、$\mathsf G(o)$ 或 $\mathsf U$；这两条条件分类不在本章原前件下供应实际根合同 $R_o$、
整个 $S_q\subseteq B$、邻边完成 $C_q$ 或 (XII145.8) 的反向纯比较。

前卷 XI 的定理144.2—144.3在完整 EB3+$\mathsf{Conn}$+$\mathsf{ZC}$ 下取得固定球族连续性与二步纯载体紧性；144.4的全域不塌缩另需在全部原标签之前选定的统一上端预算余量，144.5则输入 $\mathsf{UC}$。本章的 $R_o$、整个 $S_q\subseteq B$、$C_q$ 与单对反向纯比较没有供应这些额外的 Conn、ZC、UC 或全域统一余量，故这些条件结果不替代145.3的返回推导。

裸 EB3、EB3 加纯 PR、以及 X133.9 的完整 $\mathsf E_0$ 自动产生全覆盖根的问题，
仍按 (X133.32) 保留各自的全部原对象、前件与量词；$L_\varepsilon(o)$ 不被当作这些域的已知后果。

本章的承重推导是 (XII145.13)—(XII145.24)：真实原标签进入第二球，单对反向比较迫出原零对径，
先回送球心，再以完整极值范围消去正分离裕量；(XII145.27) 是其严格高段消费者。
采用 `repo-derived` 的纸面归属，不主张全球原创或文献穷尽。
原面分类、真实零确认、IX114.5 的球内刻度与其满刻度传播、X132.2及132.4的固定根证明、
X133.2的标签排重、X133.5的关联拓扑均为明确复用，不另计为新定理。
IX114.4 已在不要求 EB3 的完整 PR 域给 $P$ 紧；这里的固定紧球面论证不重新证明它。
IX120.12—120.13 的 $P_0$ 分支另有 Inj，不被借来替代根合同或 $C_q$。

成熟外部工具限于球上线性函数的极值与 [Hatcher][Q145H] 的区域不变性／同维紧流形嵌入满射。
后者的全部前件只在 (XII145.10) 的两张完整二维球面上使用。
原确认构造与完整效应区间的文献背景沿用 IX114.1 的
[Landsman §1.3，式(1.4)—(1.9)](https://arxiv.org/pdf/quant-ph/9603005v2)；
这里没有从对称跃迁概率另取 least、混态互易、自对偶或额外分类公理。
所得结论仅属于上述有限维原态—效应几何；来源、实际事件仪器、全部有限复合、纠缠、
全旁观正性、记录与全部未来、物理钟、Hamiltonian 及数值 $\hbar$，
继续保留 X133.10 的每个原对象、前件与完整量词，不由这条返回补出。

[Q145IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.1—114.2：原全域、真实零确认与原面；114.4：PR下纯紧性；114.5及(IX114.15)—(IX114.16)：整球刻度；IX120.1、120.4—120.5：原面、三角与既有分类；120.12—120.13：另有Inj的P0分支。"
[Q145X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X132.2—132.4：原小正无隙、局部带与逐点三角反证；X133.1—133.5：完整原面、三角标签、紧投影、已付域上的唯一共同邻点与整球面拓扑；X133.6、133.9：全覆盖根及未付自动性；133.10：完整物理合同。"
[Q145TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "VIII131全文，特别是131.3的裸EB3第三实心带紧性、131.5的R3奇返回及131.6的部分关联域与未付全载体。"
[Q145SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "132.1：完整EB域的无Inj纯点—排除球凸覆盖、径向三纯项及未付最后一对正交。"
[Q145H]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology，印刷页172，Theorem 2B.3、Corollary 2B.4：区域不变性及紧n流形嵌入连通n流形的满射性；这里只用n=2。"

## 追加锚

## 146. 完整记录下的粗测量误差与保相干容量

### 146.1 原来源与实际控制解析

**定义146.1（控制已解析的一激发目录）。** 本章的原生来源为 [RRO Acquisition V][XII146RRO]（固定版本 `90a0a6390171837fa6aa82254c7ad323341f0657`）定义25.1、定义32.1—32.2及定理27.2。保留它们的两个原入口、实际来源和准备身份、未知输入、共同经典 backing、权限、原请求、整个 bank、全部实际记录及全阶段原服务。相干未知 ingress、独立真空 QNew、接线、恒等保持、字面全量子位 $P/B$ 和实际二元占据仪器都是另行供应的权限。所有可访问量子系统，包括输入／交付端口和量子控制器，均计入 bank；除未知码外初始全为独立真空，总可访问激发恰为一。不可访问参考可带激发，但没有对它的操作权限。

量子步骤仅为数守恒 bank 酉、恒等保持、独立真空扩张及单站占据投影。没有未计量环境、未返回量子控制器、混合噪声原语、额外相干测量、复合 detector、重置、丢弃或后选择。经典来源可以相关，不改成独立种子乘积。所有实际采样并使用的随机控制选择、实际端点、门种类、完整角字符串或指定参考门标识、实际 enable、执行顺序及全部占据结果，均由原有 backing 或另行付费安装的不可改写正交经典记录保留。给定真实记录及保留的初始经典 backing，已执行的量子算子链唯一确定，允许整体相位。没有改变算子链的潜在随机位不必记录，未执行分支的反事实随机位不必物化。

称此为**实际控制解析条件**。下界只需其中较弱的版本：每个含点击的真实终端记录解析从未知码到全部保留量子输出的算子链，至多相差标量。完整版本给出这一条件的直接实现。其含义来自实际接口，不是给数学随机 tape 增设输出副本。

RRO V定义27.1保留 requested/executed gate slots、commanded angle strings、observable enable/control labels、锁、保持、结果、输出前缀及实际可观察的资源读数；定义32.1保留初始 controls、external command sources 及其共同 law。定理29.2又明确区分观测结果与被求和的隐藏 Kraus 指标。这些条款没有统一承诺每个私有 enable、后来随机控制及下界放宽的一般酉都被终端记录解析。因此本定义是明确的附加模型条件，不能倒填为旧定义32.2的结论。下界容许将酉放宽到全部数守恒酉，但仍保留这一实际条件。

[FARG续卷][XII146FARG]（同一固定版本）定义60.1、式(60.2)与定理60.2只供应字面门矩阵及其来源；其 PR57 固定包、私有接口、容量与费率不被移植为 RRO 原服务。RRO V定理33.1已供应唯一形式全零路径、首次点击后算子秩至多一及原坐标 $2+2$ 的 $1/4$ 下界。该源 §§34—35 的两个计量量子位和额外已知激发属于另一目录，其26角字不是本章上界。

### 146.2 未知族、分支量词与完整输出

**定义146.2（粗投影目标、总返回协议与距离）。** 取有限维复 Hilbert 未知码的正交分解，$Q_i=Q_i^\dagger$ 为到 $H_i$ 的正交投影，$n\ge1$：

$$
H=\bigoplus_{i=1}^{n}H_i,\qquad Q_iQ_j=\delta_{ij}Q_i,
\qquad \sum_iQ_i=I_H,\qquad k_i=\dim H_i\ge1,\quad d=\sum_i k_i.
\tag{XII146.1}
$$

由实际相干端口把它嵌入 $d$ 个已取得模式的单激发子空间，记为 $E$。未知族包含每个 $\rho_{HR}$ 及任意未触参考 $R$。共同初始经典源、制备标签、归档、样本、权限、版本、命令来源、控制 backing 和随机 law 均输入无关，初态为 $C\otimes(E\otimes I_R)\rho(E^\dagger\otimes I_R)$，并附上全部规定真空。输入相关的实际制备标签违反此条件，不能删掉标签来援引定理。一个已知向量的准备、Tag 或来源增长均不供应这个全族。

目标是保留粗标签的 Lüders 仪器

$$
\mathcal L_Q(X)=\sum_i |i\rangle\langle i|_A\otimes Q_iXQ_i.
\tag{XII146.2}
$$

协议返回 $A$，保留全部实际 bank、已取得系统、来源后继、初始 backing 和实际控制／测量／输出记录。允许每个已返回分支只用有限深度与有限资源，而所有分支的深度、资源及历史长度没有共同有限上界。**总返回**指对每个允许输入，有限已返回历史的概率总和／积分为一。形式零概率分支可以不返回；不为它指定归一条件态。不承诺有限期望代价，也不承诺统一最坏代价。

这里准确区分源的两种有限性措辞。RRO V §29.1写明 “A finite adaptive program is a finite tree”，定理29.2的有限并集证明适用于该有限树范围。定义32.2则写明 “It is total on all positive branches and has finite depth and finite resources on every branch”，并且 “No bound on future lawful source size is imposed”；它随后另写 “put all branches in their finite union of bank coordinates”。若沿用 §29.1 的有限树约定，后一有限并集合法，本章包含全部这样的协议。若允许一个协议有无界长度的有限返回历史族，后一并集不必有限，本章以下述实际记录空间替代该比较空间的有限性要求，证明同一下界。若把“正分支”仅解释成单条路径点概率为正，则“每条无限路径点概率零”不推出总返回；合计非返回概率正的过程没有这里要求的归一返回通道，须另定非返回输出和目标，不能以本章距离代表它。这个限制涉及返回通道的类型，不是额外容量界。

令 $\mathsf H_\Pi$ 为真实有限终端记录的可测空间，含实际初始 backing、所有被保留字段、粗标签及实际来源／版本后继。每个 $h$ 只携带其实际有限 bank $B_h$；共有的原码与原 source-bank 因子按取得身份识别，其他实际已取得因素记为 extras。离散记录使用正交直和；连续共同 backing 或实参数记录使用经典—量子直积分的预对偶：

$$
\Omega(X)=\bigoplus_h\Omega_h(X),\qquad
\|\Omega\|_1=\sum_h\|\Omega_h\|_1;
\qquad
\|\Omega\|_1=\int_{\mathsf H_\Pi}\|\omega(h)\|_1\,d\nu(h)
\quad\hbox{（可测情形）}.
\tag{XII146.2a}
$$

此处直积分是记录可观测代数上的经典—量子态，不把非原子经典 law 写成不可数个 Hilbert 空间迹类正交本征向量。使用通常的标准 Borel 历史空间、可测控制核和可测有限维 bank 纤维；更一般情形需同样存在这些态及条件算子密度。数字有限原生历史满足此条件。每个有限返回历史的算子链给出 CP 分支，按记录直和／积分的正极限仍为 CP；总返回使其迹对每个输入为一，因而得到归一完整输出通道。直和／直积分不预分配任何未发生历史的量子位，不创建无限记录器，不识别不同真实来源后继。有限树时可等价地把未用坐标数学补真空。对无界历史族，仅在每个实际纤维内识别共同因子，无需物理或数学上的有限全局 bank。

全理想 lift 是同一输出接口上的线性归一 CP 通道；其 $A$、原码／原 source-bank 与 $R$ 的**物理张量因子边缘**，对每个输入和参考都精确为嵌入后的 $(\mathcal L_Q\otimes\operatorname{id}_R)(\rho)$，其他原真空按合同保留。不是先投影到码再归一。来源合同规定的其他边缘亦须满足。额外量子因素、端口、真实历史及其他输出全进入比较；本章的上界保持原经典源不变。记允许的 lift 集合为 $\mathfrak L_Q(\Pi)$，定义

$$
\begin{split}
\Delta(\Pi,\widehat{\mathcal L}_Q)
 &=\sup_{R,\rho_{HR}}\frac12
 \|\Omega_\Pi(\rho)-\Omega_{\widehat{\mathcal L}_Q}(\rho)\|_1,\\
\delta(\mathfrak C,Q)
 &=\inf_{\Pi\in\mathfrak C}\ \inf_{\widehat{\mathcal L}_Q\in\mathfrak L_Q(\Pi)}
       \Delta(\Pi,\widehat{\mathcal L}_Q).
\end{split}
\tag{XII146.3}
$$

选择的是服务整个未知族的一个协议与一个线性 lift，然后取全部输入／参考的 supremum；不是逐输入重新选择 lift。内层空集的 infimum 取 $+\infty$。lift 的记录概率可与实际概率不同；只要满足原接口，它可任意重新分配理想记录质量。

记满足定义146.1—146.2的总返回目录为 $\mathfrak C_{\rm res}^{\rm ret}$，其中包括任意已解析数守恒酉的下界放宽；其有限树子目录为 $\mathfrak C_{\rm res}^{\rm fin}$。实角参考目录 $\mathfrak C_{\rm ref}^{\rm fin}$ 另准许所需有限实角门列表及指定有限分布的共同经典选择；每个参考门有固定标识和指定矩阵，解析记录保留实际选择。任意实数的精确矩阵是数学参考权限，不声称已有其有限位物理参数发生器。$\mathfrak C_{\rm dy}^{\rm fin}$ 只执行有限 signed-dyadic $P/B$，并须另供有效目标框架角括号、有限公平经典位及完整保留记录。上标 ret 允许相同权限下的全部总返回历史族。以上目录都承担146.7的同一原来源与实际资源合同。

为准确陈述精度闭包，记 $\mathcal E_{\rm dy}(Q)=\{\Delta(\Pi,\widehat{\mathcal L}_Q):\Pi\in\mathfrak C_{\rm dy}^{\rm fin},\ \widehat{\mathcal L}_Q\in\mathfrak L_Q(\Pi)\}\subseteq[0,1]$，并在实数空间取其闭包 $\overline{\mathcal E_{\rm dy}(Q)}$。这保留每次比较中的所有真实命令和记录；不同精度的命令标签不被识别或删除。误差值可趋于同一极限，不意味着携带不同精度字符串的全输出通道在一个固定接口上范数收敛。

**定理146.3（实际控制已解析目录的尖锐全记录律）。** 对每个有限分拆(XII146.1)，令

$$
I_+=\{i:k_i\ge2\},\qquad \alpha_i=\sqrt{1-1/k_i}\quad(i\in I_+),
$$

空最大值取零，并定义

$$
\delta_*(Q)=
\min_{\substack{w_i\ge0\ (i\in I_+)\\\sum_{i\in I_+}w_i\le1}}
       \max_{i\in I_+}\alpha_i(1-w_i).
\tag{XII146.4}
$$

则下列量词同时成立。

1. 对每个 $\Pi\in\mathfrak C_{\rm res}^{\rm ret}$、每个 $\widehat{\mathcal L}_Q\in\mathfrak L_Q(\Pi)$，有 $\Delta(\Pi,\widehat{\mathcal L}_Q)\ge\delta_*(Q)$。不要求单个协议或不同协议之间具有统一有限树、bank、读数次数、深度或容量界。
2. 在所需实角和精确有限经典 law 已供应的参考目录中，存在有限扫描协议 $\Pi_*$ 及一个固定全理想 lift，满足 $\Delta(\Pi_*,\widehat{\mathcal L}_{Q,*})=\delta_*(Q)$。因此 $\delta(\mathfrak C_{\rm ref}^{\rm fin},Q)=\delta(\mathfrak C_{\rm ref}^{\rm ret},Q)=\delta_*(Q)$，且有限目录达到此值。
3. 在有效角括号、公平位、实际端点控制和原服务均已供应的 dyadic 目录中，对每个 $\varepsilon>0$，存在有限扫描协议及同实际命令标签的固定全理想 lift，满足 $\Delta\le\delta_*(Q)+\varepsilon$。故 $\delta(\mathfrak C_{\rm dy}^{\rm fin},Q)=\delta(\mathfrak C_{\rm dy}^{\rm ret},Q)=\min\overline{\mathcal E_{\rm dy}(Q)}=\delta_*(Q)$；在有限协议目录中一般只是 infimum。任何夹在该有限 dyadic 子目录与 $\mathfrak C_{\rm res}^{\rm ret}$ 之间、且使用相同输出合同的目录也有此值。

若 $|I_+|\le1$，值为零；若 $|I_+|\ge2$，$\delta_*>0$ 是下式的唯一非负根：

$$
\sum_{i\in I_+}\max\{0,1-\delta_*/\alpha_i\}=1.
\tag{XII146.5}
$$

本定理是附加实际控制解析条件下的秩依赖数学结论及匹配构造。它不确定未解析旧定义32.2的尖锐值，不扩大旧定理33.1的控制范围；特别是 $2+2$ 的新值 $1/(2\sqrt2)$ 不取代其原范围的 $1/4$ 下界。

### 146.3 任意理想记录质量下的支持距离

**引理146.4（纯分支对任意正支持态）。** 设 $P$ 为投影，$v$ 为单位向量，$c=\|Pv\|^2\le1/k$，$k\ge2$。任意 $p\ge0$、$\sigma\succeq0$、$P\sigma P=\sigma$、$\operatorname{tr}\sigma=q$ 满足

$$
\|p|v\rangle\langle v|-\sigma\|_1
 \ge F_k(p,q):=\sqrt{(p+q)^2-4pq/k}.
\tag{XII146.6}
$$

**证明。** $p=0$ 或 $q=0$ 由迹给出；$c=0$ 由正交支持给出。其余令 $e=Pv/\sqrt c$、$f=(I-P)v/\sqrt{1-c}$，对 $\operatorname{span}\{e,f\}$ 及其正交补作数学 pinching。它保持实际纯算子不变，理想第一块为 $x|e\rangle\langle e|$，余块正且迹为 $q-x$，$0\le x\le q$。二维差矩阵的行列式是 $-px(1-c)$，故其迹范数为 $f_c(p,x)=\sqrt{(p+x)^2-4pcx}$，退化端点也成立。原范数至少为 $f_c(p,x)+q-x$。又

$$
\frac{\partial f_c}{\partial x}=\frac{x+p(1-2c)}{f_c(p,x)}\le1,
\qquad f_c(p,x)^2-[x+p(1-2c)]^2=4p^2c(1-c)\ge0.
$$

所以 $f_c(p,x)-x$ 不增，最小值在 $x=q$。再用 $c\le1/k$ 得结论。此处对任意理想混态作了支持和质量的优化，没有使用只适用于两个纯态的距离等式。证毕。

以下范数形式同时处理离散和可测记录。令

$$
N_k(x,y)=\sqrt{\alpha^2(x+y)^2+(1-\alpha^2)(x-y)^2},
\qquad \alpha=\sqrt{1-1/k}.
\tag{XII146.7}
$$

它是实二维范数，且 $N_k(p,q)=F_k(p,q)$（$p,q\ge0$）、$N_k(0,y)=|y|$。三角不等式给出

$$
\begin{gathered}
\int F_k(p_h,q_h)\,d\nu(h)\ge
 F_k\left(\int p_h\,d\nu(h),\int q_h\,d\nu(h)\right),\\
s+F_k(p,q)\ge F_k(p+s,q),\qquad
F_k(m,q)+|m-q|\ge2\alpha m.
\end{gathered}
\tag{XII146.8}
$$

离散和可数情形取计数测度；一般情形由向量积分的三角不等式，或非负可积密度的简单函数逼近得到。第二式把向量 $(s,0)$ 加入；第三式是 $N_k(m,m)\le N_k(m,q)+N_k(0,m-q)$。没有要求两边记录质量相等。

### 146.4 总返回历史族上的下界

**定理146.3的下界证明。** 固定任意 $\Pi\in\mathfrak C_{\rm res}^{\rm ret}$。只为经典概率计算，把共同初始 $C$ 与所有输入无关的经典随机控制核实现为同一数学 tape $t\sim\mu$。例如标准 Borel 控制核可用按决策步编号的独立均匀变量及共同 $C$ 实现；核可以依已观测历史改变。这里不预采样占据测量的量子结果，tape 也不是输出。固定 $t$ 及占据结果后，所有请求、守卫、原后继及控制确定。

每个 $t$ 有唯一形式全零占据路径，允许无读数。若它在有限步骤返回标签 $i$，定义 $a(t)=i$；若它永不返回，包括到达不可发生历史后没有返回续接的情形，定义 $a(t)=\bot$。在零概率历史上任取一个可测的确定程序续接，只用于定义形式路径，不改变实际通道。取

$$
w_i=\mu\{t:a(t)=i\},\qquad
\sum_{i\in I_+}w_i\le1.
\tag{XII146.9}
$$

事件 $a(t)=i$ 是所有有限返回时间事件的可数并，因而可测。无须每个形式全零路径有终端，也无须所有终端坐落在一棵有限树内。

若该路径在有限时刻返回，令 $N_t$ 为它从 $H$ 到其实际 bank 的未归一算子链，含 $E$。它由酉、真空等距扩张和零读投影组成，故 $N_t^\dagger N_t\preceq I_H$。对稍后使用的块内输入 $\Phi_b$，真实的“返回 $b$ 且从未点击”总概率准确为

$$
z_b=\int_{\{a(t)=b\}}
\operatorname{tr}\!\left[(N_t\otimes I_R)|\Phi_b\rangle\langle\Phi_b|
(N_t^\dagger\otimes I_R)\right]d\mu(t)
\le\int\mathbf1_{\{a(t)=b\}}d\mu(t)=w_b.
\tag{XII146.9a}
$$

这是未归一分支的线性概率计算，不是对 tape 分块计算平方根范数。$a(t)=\bot$ 时不存在已返回的全零记录，其对 $z_b$ 的贡献为零。即使形式路径无限长，每个有限前缀的存活概率也不超过一。更明确地，令 $T$ 为实际返回步数；总返回给 $\Pr_\rho(T>N)\downarrow0$。在 $\{a=\bot\}$ 上，沿全零路径前 $N$ 步的未返回质量 $r_N(t)$ 单调不增，其积分不超过 $\Pr_\rho(T>N)$；于是 $\int_{\{a=\bot\}}\lim_Nr_N(t)d\mu(t)=0$。因此无限全零形式路径不产生遗漏的正返回质量或归一条件态。这也证明使用全部有限叶的积分时不损失总质量。

在当前整个单激发 bank 上，站点 $q$ 的点击投影为 $|q\rangle\langle q|$。首次点击使从 $H$ 出发的算子秩至多一，之后酉、真空增长与投影都不能增秩。这是 RRO V定理33.1的机制。实际控制解析条件进一步保证：给定真实终端记录 $h$，未区分的经典选择只会给同一个链乘标量，不能在一个 $h$ 中混合不同量子操作。全部初始量子辅助是纯真空，故含点击的真实记录对纯输入给出次归一纯态。该断言只关于真实 $h$，不关于补造的 tape 寄存器。

固定 $b\in I_+$，令

$$
|\Phi_b\rangle=\frac1{\sqrt{k_b}}\sum_{\ell=1}^{k_b}
 |e_{b\ell}\rangle_H|\ell\rangle_R.
\tag{XII146.10}
$$

点击记录上的秩一算子作用后，输出纯态是 laboratory 与 $R$ 的乘积。令 $P_b$ 为原 source-bank／$R$ 上嵌入的 $|\Phi_b\rangle\langle\Phi_b|$ 张量全部新增 extras 的恒等；嵌入包括原 bank 中合同规定的其余真空，按每个真实记录纤维的共同物理因子理解。对任意归一乘积向量 $v=\xi_{\rm lab}\otimes\eta_R$，有

$$
\|P_bv\|^2\le1/k_b.
\tag{XII146.11}
$$

事实上，$\eta_R$ 与 $\Phi_b$ 收缩所得的码向量范数至多 $1/\sqrt{k_b}$；它对 laboratory 的码因子取内积、对 extras 取恒等的算子范数至多此数。laboratory 内部的纠缠、码外或其他模式分量均不能提高它。

任取全理想 lift。其此输入上的正确码／参考边缘是纯 $\Phi_b$，错误粗标签质量零。正算子的某投影补上迹为零时，其平方根在该补上为零，交叉块也为零；因此全部理想输出支持于 $P_b$ 且标签为 $b$，不要求理想 extras 纯。记录按实际经典类型处理；若比较空间还允许跨记录相干，先限制到同一实际记录可观测代数，态范数收缩且支持结论保持。离散时这就是数学 pinching，不是物理删记录。

可测情形的共同密度可以如此固定：取 $\tau=I_H/d$，以实际和理想在 $\tau$ 上的记录概率测度之和为 $\nu$。因 $\rho_H\preceq d\tau$，每个输入的两种记录 law 均被 $\nu$ 支配；有限维输入的 CP 仪器在这些可测有限 bank 纤维中有共同算子密度。张量任意未触参考不产生新的零集。对含点击的实际记录，密度几乎处处是上述单一秩一链的纯输出，而不是在另一个隐藏指标上分解混态。以下积分均关于这个实际记录空间上的共同测度。

将其分为 $G,B,W$：$G$ 为标签 $b$ 且记录中无点击，实际／理想总质量记为 $z,g$；$B$ 为其余标签 $b$ 的记录，质量为 $p,q$；$W$ 为错误标签，实际质量为 $s$，理想质量零。理想独有的无点击记录归 $G$，理想独有的点击记录归 $B$，实际密度都取零。于是 $z+p+s=g+q=1$。$G$ 内不要求实际态保相干或纯，只用迹差得范数至少 $|z-g|$。$B$ 内每个非零实际密度是纯乘积态，以引理146.4和(XII146.8)合并得至少 $F_{k_b}(p,q)$；实际为零的密度同样满足 $F_k(0,q_h)=q_h$。$W$ 的贡献恰为 $s$。设 $m_b=1-z=p+s$，得到

$$
\begin{split}
D_b&:=\frac12\|\Omega_\Pi(\Phi_b)-\Omega_{\widehat{\mathcal L}_Q}(\Phi_b)\|_1\\
&\ge\frac12\{\,|z-g|+F_{k_b}(p,q)+s\,\}\\
&=\frac12\{\,|q-m_b|+F_{k_b}(p,q)+s\,\}\\
&\ge\frac12\{\,|q-m_b|+F_{k_b}(m_b,q)\,\}
 \ge\alpha_b(1-z).
\end{split}
\tag{XII146.12}
$$

此式允许理想方任意移动全部记录质量，不设 $p_h=q_h$，也不假设无点击算子为恒等。对同一协议和同一 lift，结合线性式(XII146.9a)，

$$
\Delta\ge\max_{b\in I_+}D_b
 \ge\max_{b\in I_+}\alpha_b(1-w_b)\ge\delta_*(Q).
\tag{XII146.13}
$$

所有非线性范数估计只按真实记录作直和／直积分。无界有限返回历史族不改变此证明，也不隐含无限物理预分配。下界证毕。

**命题146.5（控制未解析时的限制）。** 仅有点击输出的可分性，不足以推出(XII146.12)的平方根常数。

**证明。** 令 $\Phi=(|00\rangle+|11\rangle)/\sqrt2$，$\tau=(|00\rangle\langle00|+|11\rangle\langle11|)/2$。两个纯分量各与 Bell 射线有平方重叠 $1/2$，但 $\tau-|\Phi\rangle\langle\Phi|$ 在 $\operatorname{span}\{|00\rangle,|11\rangle\}$ 上的两个本征值为 $\pm1/2$，所以半迹距离为 $1/2<1/\sqrt2$。若同一真实记录内混合不同 rank-one 链，不能在未保留指标上分别应用引理146.4后相加。这个代数例子不是旧目录中的实际反例协议；它精确指出扩大本章下界尚缺的实际控制条件，或尚需另一混合分支证明。证毕。

### 146.5 一个总激发的匹配有限扫描与全参考 supremum

**定理146.3的参考上界证明。** 固定各块正交框架 $e_{j\ell}$，令 $P_{j\ell}=|e_{j\ell}\rangle\langle e_{j\ell}|$。选择模式酉 $U$，把这些框架向量送到实际 $d$ 个码模式 $q_{j\ell}$。这是输入无关的已知目标设计，不是从未知态读出振幅。

按共同输入无关 law 选择保护块 $a\in I_+$，概率 $w_a$；余下概率选择符号 $\varnothing$，表示不保护块。保留选择值及所有实际采样位／控制记录。执行 $U$，按固定次序逐站读取不在保护块内的模式，首次点击后停止扫描，各分支均执行同一个 $U^\dagger$ 返回原码。没有点击则完成整个有限列表。无保护时读取全部 $d$ 个模式，全零分支为零算子，不归一也不后选择。给它指定任意形式返回标签即可。

当保护块为 $a$ 时，未含经典概率因子的码分支算子是

$$
K_{a,0}=Q_a,\qquad K_{a,j\ell}=P_{j\ell}\quad(j\ne a).
\tag{XII146.14}
$$

证明是直接相乘：首次点击前各零投影消去已扫描坐标，点击投影选中当前未扫描坐标；全零乘积留下且仅留下保护平面。再以前后 $U,U^\dagger$ 共轭。无保护时只有全部 $P_{j\ell}$。每种选择的伴随乘积和为 $I_H$，故总仪器归一。公布分支所属原块标签 $j$；实际与理想均消去跨块相干。所有零读、首次点击、停止位置、返回字及 source／control 版本均保留。原 source 不变，其他原模式、旧输入端口和辅助量子位为真空，总激发一直为一。

令 $h_{a,0},h_{a,j\ell}$ 表示这些完整真实记录，含 acquisition/source/version/command/enable/hold/read/output 字段。对每个实际随机子记录 $c$，保留其原概率 $\pi_c$ 和选择 $a(c)$；条件初始 backing 也逐项保持。固定如下全理想 lift：在块 $j$ 上，若 $a(c)=j$，赋予记录 $h_{c,0}$ 和量子输出 $Q_jXQ_j$；否则独立均匀赋予 $\ell\in\{1,\ldots,k_j\}$，记录 $h_{c,j\ell}$，仍输出 $Q_jXQ_j$。相应 Kraus 部分分别为 $\sqrt{\pi_c}Q_j$ 与 $\sqrt{\pi_c/k_j}Q_j$。因此不仅选择标签，而且同一选择下所有采样位均保留。连续初始 backing 时对其共同 law 积分。

这是单一线性 CP、归一 lift，其所需边缘恰为(XII146.2)，来源和其他规定因子不变。均匀细索引只是数学理想记录 law，不宣称实际 detector 生成它，也不删除实际细记录。它不依未知块内态或 $R$。

为计算全部输入／参考的 supremum，固定未保护的秩 $k$ 块，取任意归一纯联合输入

$$
|\Psi\rangle=\sum_{\ell=1}^{k}|e_\ell\rangle|r_\ell\rangle,
\qquad p_\ell=\langle r_\ell,r_\ell\rangle,\qquad\sum_\ell p_\ell=1.
$$

$r_\ell$ 不必正交，参考不限于块的同维副本。在记录 $\ell$ 上，实际为 $|u_\ell\rangle\langle u_\ell|$，$u_\ell=|e_\ell\rangle|r_\ell\rangle$；理想为 $|\Psi\rangle\langle\Psi|/k$。由 $\|u_\ell\|^2=\langle u_\ell,\Psi\rangle=p_\ell$，两个次归一纯算子的二维差矩阵给出

$$
D_k(\Psi)=\frac12\sum_{\ell=1}^{k}g_k(p_\ell),\qquad
g_k(p)=\sqrt{(p+1/k)^2-4p^2/k}.
\tag{XII146.15}
$$

$p=0$ 时也保留理想独有质量 $1/k$。$k\ge2$ 时根号在 $[0,1]$ 上严格正；写其平方为 $Ap^2+Bp+C$，有 $A=1-4/k,B=2/k,C=1/k^2$，从而

$$
g_k''(p)=\frac{4AC-B^2}{4g_k(p)^3}
=-\frac4{k^3g_k(p)^3}<0.
\tag{XII146.16}
$$

Jensen 不等式给出

$$
D_k(\Psi)\le\frac{k}{2}g_k(1/k)=\sqrt{1-1/k}=\alpha_k.
\tag{XII146.17}
$$

每个 $p_\ell=1/k$ 达等，特别是 $\Phi_j$ 达等。$k=1$ 时实际与理想完全相同。任意混态可在数学上纯化，将纯化因子并入未触参考，再取边缘；迹距离收缩给出同一界。纯化不增加实验室装置。由于 $H$ 有限维，纯化态在 $H$ 与联合参考之间的 Schmidt 秩至多 $d$；该证明也覆盖任意维正常参考态。

对任意跨块输入，两通道都消去跨块项。令 $\lambda_j=\operatorname{tr}(Q_j\rho_H)$，各粗标签和实际选择记录正交，范数相加，故

$$
\Delta(\Pi_w,\widehat{\mathcal L}_{Q,w})
=\max_j\alpha_j(1-w_j),
\qquad \alpha_j=0\ (k_j=1),\quad w_j=0\ (j\notin I_+).
\tag{XII146.18}
$$

上界来自 $\sum_j\lambda_j\alpha_j(1-w_j)$；下界取最大块的 $\Phi_j$，每个未保护选择都在(XII146.17)达等。因此这是全部参考和全部混输入的精确 supremum。

若无高秩块，直接细读即理想；仅一个高秩块则始终保护它。至少两个时，给定 $\delta\ge0$，约束 $\alpha_i(1-w_i)\le\delta$ 当且仅当 $w_i\ge\max(0,1-\delta/\alpha_i)$；可行当且仅当这些下界之和不超过一。该和由 $|I_+|$ 连续下降至零，在值一处严格下降，唯一根即(XII146.5)。取这些下界为最优权，总和为一。结合下界证明参考目录值及有限达到性。特别地，两个高秩块满足

$$
\delta_*={\alpha_1\alpha_2\over\alpha_1+\alpha_2},\qquad
w_i={\alpha_i\over\alpha_1+\alpha_2}.
\tag{XII146.19}
$$

$m$ 个相同秩 $k\ge2$ 的块有 $\delta_*=(1-1/m)\sqrt{1-1/k}$。证毕。

### 146.6 字面门、有限精度与闭包值

**假设146.6（有效框架与有限控制供给）。** 实际模式、两端接线与端点控制均已取得。所用字面门为 RRO V定义25.1所准许、源于 FARG(60.2) 的

$$
P_q(\theta)=\operatorname{diag}(1,e^{-i\theta}),\qquad
B_{qu}(\theta)|_{10,01}=\begin{pmatrix}\cos\theta&i\sin\theta\\i\sin\theta&\cos\theta\end{pmatrix},
\qquad B|_{00,11}=I.
\tag{XII146.20}
$$

记录实际 enable，包括零 digit 的已执行恒等槽。另供一个目标框架的有限角列表及有效有理括号生成器：给定正精度，返回每角的有证有理区间。它输入无关；任意不可计算实投影的抽象存在性不供应此数据，XI145的静态表示也不供应它。另供所需有限公平经典位、不可改写 backing 及选择权限；$s$ 位须为联合均匀位串，不仅各位边际公平。这是新增经典随机权限，不把原共同源改成独立种子乘积。

**定理146.3的有限精度证明。** 标准两模式消元在本章相位约定下可直接核对。一列的两项 $a,b$ 先用两单站相位变成 $|a|,i|b|$，再用 $B(-\theta)$、$\tan\theta=|b|/|a|$ 消去后一项。$a=0,b\ne0$ 取 $\theta=\pi/2$；两项皆零取恒等槽。逐列至多 $d(d-1)/2$ 次消元，余下上三角酉为对角相位。因此参考 $U$ 及其逆各有至多

$$
G(d)=3d(d-1)/2+d
\tag{XII146.21}
$$

个 $P/B$ 角块，角绝对值可取小于 $2\pi$。逆字用逆序反号。有限模式酉分解是标准供应，[Clements等，Background(1)—(2)及图1][XII146CLE]给出两模式／相位分解背景；这里核对字面 $i\sin\theta$，仅给足够计数，不移植其光学硬件或最优性。至多 $d(d-1)/2$ 条所用两模式计算线及 $d$ 个相位端点控制逐一付费取得；计算线不是材料 parent-child seam。上界不调用额外 Naimark 仪器。

用有效括号选每角误差至多 $2^{-b}$ 的 signed dyadic，实际执行 $\widetilde U$ 及其精确逆字 $\widetilde U^\dagger$。字面全空间生成元范数为一，积分导数得每角酉偏差至多 $2^{-b}$。前后两个 $G(d)$ 块字的 telescoping 与全输出通道收缩给出

$$
\sup_{R,\rho}\frac12\|\Omega_{\rm dyadic}(\rho)-\Omega_{\rm reference}(\rho)\|_1
\le2G(d)2^{-b}.
\tag{XII146.22}
$$

中间包含全部读数、提前停止、反馈及记录的仪器是同一个归一通道；不逐个归一后态。reference 用精确 $U,U^\dagger$ 的量子作用，但携带同一实际写入的 dyadic 命令、digit／enable、版本、时间和输出标签，正如 RRO V §29.1与定理35.1的数学比较接口。它不声称这些标签的实角量子作用已经物理执行，亦不假造额外可见字段。

设 $m=|I_+|\ge2$。最优 $w$ 由有限个实代数数 $\alpha_i$ 和(XII146.5)唯一确定，具有有效有理括号。取 $s$ 个公平位。对前 $m-1$ 个 $w_i$，先取宽度至多 $2^{-s}$ 的有理括号，其下端截到非负，再向下取 $2^{-s}$ 格点；末项补齐总和一。所得 $\widehat w\ge0$，前 $m-1$ 项各少至多 $2\,2^{-s}$，末项多至多 $2(m-1)2^{-s}$。不必判定实数是否恰为某 dyadic 格点。把 $2^s$ 个等概率 bit strings 分成相应整数个子集，就精确实现 $\widehat w$；没有无限拒绝抽样，全部采样位连同选择值保留。式(XII146.18)对这些更细记录仍成立。

由 $\alpha_i\le1$，有 $\max_i\alpha_i(1-\widehat w_i)\le\delta_*+\|\widehat w-w\|_\infty$。以同一完整记录接口上的精确框架 lift 比较，三角不等式给出

$$
\Delta(\Pi_{b,s},\widehat{\mathcal L}_{b,s})
\le\delta_*+2(m-1)2^{-s}+2G(d)2^{-b}.
\tag{XII146.23}
$$

$m\le1$ 时采用确定选择，随机精度项置零。给定正 $\varepsilon$，有限 $b,s$ 可使多出项不超过它。结合普遍下界，误差值全部不小于 $\delta_*$ 且可任意逼近它，故其闭包最小值及定理146.3的 dyadic infimum 均为 $\delta_*$；不保证任意实框架或最优权的有限精确执行。

每角幅度可用指数 $-b,\ldots,2$ 的 $J=b+3$ 个 digit 槽；前后字共至多 $2G(d)(b+3)$ 次 elementary rotations 和同数 digit fetches，含零 digit。两种符号及这 $J$ 个指数的 endpoint-specific entries 至多 $2[d+d(d-1)/2](b+3)$ 个。每分支至多 $d$ 次占据读；若总保护高秩块，则至多 $d-\min_{i\in I_+}k_i$ 次。公平位、完整扫描／停止／返回记录和原服务另计。这些是有限槽位上界，不是实际时长或物理能量界。证毕。

**条件应用（原坐标 $2+2$ 的有限精确值）。** 在 RRO V定义32.1的真实 $r,o,m,y$ 码上，$U=I$。付清一个公平经典位和其不可改写记录，各半保护 $\{r,o\}$ 或 $\{m,y\}$，逐站扫描另一对，首次点击停止。全零保留保护平面，点击已在原码模式，不需旋转、计量量子位或第二激发。上一节 lift 及(XII146.18)给出精确全记录误差 $1/(2\sqrt2)$。原最小 fork 仍有五个 bank 量子位，含真实 dormant $z$；公平位是另供经典资源，不是 native Tag 的随机输出。其余 source、hold、权限及返回义务照定义146.7承担。

### 146.7 原来源、物理误差与每个有限未来

**定义146.7（完整实际供给与返回合同）。** 所有控制从 native Ready、真实 current grants 和已取得 $(v,\mathfrak a)$ 开始。框架模式须由实际源遍历、commission 与描述符取得，数学下标不转成引用。未知码在声明支持的 vacuum carrier 上经实际相干 SWAP ingress 移入；旧端口变真空且保留，不复制、不重置旧未知态。一般 $d$ 的逻辑模式来自实际有限 source／commission；以后逐次供应增长，不预设会拒绝更深合法编辑的容量上界。

锁定当前 source 与 attachment 版本后取得计算线、控制、随机 backing、角与有限目录，保存并恢复借用游标。执行期间不写原生源、准备、历史 tape、旧 sample 或原 guard。所有结果及其后续分支实际保留。新增事务完成自己的 backing／sealing、Print、End、local ACK、root Return 和付费 scratch clearing 后返回 Ready；只清被释放工作槽，不清不可改写控制／测量记录。未完成事务保留 pending 字段和整个 bank 的保持。

原生 Tag、HasPromotion、HasSplit、FetchGrowth、实际 $P/S$、genuine Next、OutOfRange、BadFrame、错误类型拒绝、权限否决、原输出前后缀和所有版本语义均按 RRO V定理27.2保留，不添 guard。计算线不是材料源线，随机选择不是来源实际 Next。全部旧 source／tape／component／preparation 身份、每个 acquisition 版本及共同经典源间相关保持；两个原入口的实际不同根和不同准备不合并，双侧来源只 commission 实际有限 footprint。

收费包括原 source、所有被保留参考／端口／vacuum 系统、全部 classical control、随机来源和采样位、引用编码宽度、描述符／角色／版本、锁和游标、有效框架数据与角括号生成、全部有限算术、位串写读、线／目录安装和校准、结果 latch、记录 sealing、输出／ACK／Return、pending 与清理。未触外部参考不成为可操作资源；其允许输入关联不能缩减。保持覆盖编译、ingress 等待、原服务和输出全程的全部已安装量子系统，按实际 $\sum_t Q_{\rm installed}(t)$ 或另给时长加权账户收费。RRO native Read 的旧费率不代付这些权限。槽位数不推出净节省、最少门数、统一价格、物理时长或能量下界。

**条件推论（全输出误差与有限未来）。** 在定义146.7的供给下，若输入／ingress 全联合误差为 $e_0$，各 elementary gate 的全空间酉偏差上界为 $\zeta_j$，全 bank hold 的完整 half-diamond 误差为 $h_t$，完整 detector／control-record／output instruments 的 half-diamond 误差为 $\kappa_t$，则

$$
\Delta_{\rm physical}
\le\delta_*+2(m-1)_+2^{-s}+2G(d)2^{-b}
 +e_0+\sum_j\zeta_j+\sum_t(h_t+\kappa_t).
\tag{XII146.24}
$$

$m\le1$ 时随机精度项为零；$U=I$ 时角精度项为零。自适应不同分支的校准和取足以控制全部分支的预算上界。证书覆盖全部实际输出、时序／控制侧信道、返回环境与泄漏；仅码边缘校准不足。非理想混合噪声在此是有证物理误差，不是理想目录的免费操作。

**证明。** RRO V命题29.3的全输出 hybrid 逐槽替换，以完整仪器收缩给误差和；无需误差独立。这里没有把逻辑 tick 认作物理时间，也没有采用来源 Hamiltonian 的额外连续演化比较，故不加入未经定义的时钟项。物理时序的差异必须由上述完整证书控制；若另比较连续时间模型，再按它的独立校准预算付费。

全阶段原服务持有整个 bank。QNew／材料增长在每个分支上都是全空间等距映射 $\xi\mapsto\xi\otimes|0\cdots0\rangle$，标记激活只改经典角色，不改旧量子位身份。因此 RRO V定理27.2适用于 dyadic 误差产生的错误粗块分量及任意 bank／reference 联合态；这也是该源定理36.1核对的全空间前提，不借其双计量资源。每个后来合法的有限原 continuation 都保留同一原请求的全阶段扩展；新增材料、描述符、线、控制、记录与保持逐次供应。不存在已供应的无限物理 bank 或无界时间保持。

返回切口后，给两侧全输出施加同一个已供应的归一有限未来通道，迹距离不增；未来的有证误差另加。反馈可依完整记录选择不同原请求，实际后继在各自正交记录块保留，不要求两条随机轨迹逐路径相同。每个中间切口保留原 pending、权限、实际记录与保持合同。无稀有分支除概率的误差保证，也不把返回切口的正下界称为任意未来通道下的不变量。物理协议若偏离一激发或解析条件，须通过完整比较证书另论，不能直接套用理想精确下界。证毕。

### 146.8 XI145的完整静态字典与实际操作

**条件应用146.8（同原对象、标准公理与操作接口）。** 采用 [XI145][XII146XI] 定理XI145.2的完整原域：$V$ 为非零有限维实空间，$C$ 闭尖生成，$u$ 在非零锥元上严格正；$K=C\cap\{u=1\}$，$P=\operatorname{ext}K$，效应为整个 $[0,u]_{C^*}$，$T_p$ 是完整确认族上的 minimum，$D_p$ 是整个零集。EB3 要求每个原 $D_p$ 都是完整非退化闭三球，Inj 要求球标签单射。完整 EB3+Inj+$\dim_{\mathbb R}V=9$，或 XI145.2已证明等价的 EB3+Conn+九维入口，供应同一个

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad\Phi(\operatorname{PSD}_3)=C,\qquad u\Phi=\operatorname{Tr}.
\tag{XII146.25}
$$

准确消费的是 XI145.9 的全部静态字典及 XI145 §145.9 的全部原物理合同，不是本卷 XII145的真实标签返回定理；后者不是本章的数学前提。以下对应始终沿同一个 $\Phi$。

| 标准静态对象／量子公理 | 完整同原对应及其操作界限 |
| --- | --- |
| 载体、正性与质量 | 整个 $V=\Phi(\operatorname{Herm}_3)$、$C=\Phi(\operatorname{PSD}_3)$，含零、次归一和任意非负质量；$u\Phi=\operatorname{Tr}$。对偶质量函数 $u$ 与原 Jordan 单位 $U=\Phi(I_3)$ 不混型。 |
| 态与统计混合 | 整个 $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$，仿射维八；全部有限凸组合与非负组合保持。零质量只有零锥元，不强定其归一态。 |
| 纯态与复叠加 | 全部 $P\cong\mathbb{CP}^2$，实维四；非零 $w\in\mathbb C^3$ 对应 $\Phi(ww^*/(w^*w))$，复非零倍数同标签。任意非零复线性叠加有原射线标签，未因此取得实际相干制备。 |
| 效应与 Born 评价 | 全部效应恰为 $f_M(\Phi X)=\operatorname{Tr}(MX)$、$0\preceq M\preceq I_3$，保零、单位、补及序，覆盖每个混输入和非负质量。任意实线性读数对应 Hermitian $M$。 |
| 完整确认、least 与 minimum | 对单位 $v$，$P_v=vv^*$、$Q_v=I-P_v$，完整菜单为 $f_{P_v+B}$，$B=Q_vBQ_v$、$0\preceq B\preceq Q_v$；菜单非单点，least 为 $f_{P_v}$，每个 $\rho$ 上已达 minimum 是 $\operatorname{Tr}(P_v\rho)$。 |
| 纯比较和端点 | $T_{p_v}(p_w)=\lvert v^*w\rvert^2$；非归一向量除以两范数平方之积。相同射线给一，正交给零，纯 PR 是后果，不是顺序测量交换律。 |
| 完整排除球 | $D_{p_v}$ 是支持于 $v^\perp\cong\mathbb C^2$ 的全部二阶密度矩阵；Pauli 球 $\lVert r\rVert\le1$，纯球缘 $\mathbb{CP}^1\cong S^2$，中心 $\Phi(Q_v/2)=(U-p_v)/2$。不是只识别纯零点。 |
| 原零框架与数学区别 | 原零三角是和为 $I_3$ 的三个正交秩一投影，least 效应和为 $u$；零边有唯一第三点，数学完美区别容量三，全部不同纯对有原真最小面。 |
| 全部有限数学测量 | 任意有限族 $f_j\in C^*$、$\sum_jf_j=u$ 恰为全部 POVM $M_j\succeq0$、$\sum_jM_j=I_3$；零项、重复及任意有限粗粒化均保留。数学概率菜单不供应实际仪器。 |
| 谱与可观测量 | 全态有三项正交纯谱分解，含零权、重谱及任意非负质量；全部 Hermitian 可观测量有实谱和谱投影。重谱不指定唯一逐射线细化。 |
| Jordan、共同尺与齐次性 | $\langle\Phi X,\Phi Y\rangle_\Phi=\operatorname{Tr}(XY)$ 自对偶化原锥，$\Phi X\circ\Phi Y=\Phi((XY+YX)/2)$；正定合同给锥内部齐次性。它们不自动是可调用事件。 |
| 全域球心相容 | $R(x)=(u(x)U-x)/2$ 正、保质量、可逆，$R(p)=c_p$；同一原态的全部有限纯配方替换后仍相同。其逆 $u(y)U-2y$ 不正，不能当作实际恢复。 |

**证明及原合同。** 各静态项直接消费固定版本 `f24456b4a12` 的 XI145.2、XI145.9；其确认菜单的完整性依 $I-M\succeq0$ 及零二次型消去交叉块，minimum 依 $\operatorname{Tr}(B\rho)\ge0$。这是原同锥同单位运输，不以单独的纯射线双射替代全部对象。

一个 qutrit 锐投影菜单由此有数学 Born 概率和形式分支 $\rho\mapsto Q_i\rho Q_i$。只有另供同一全未知族在本章 bank 中的相干 ingress、有效目标框架、实际线／门／hold／detector、控制解析及记录权限，才可代入定理146.3。三维秩分拆只有 $3$、$2+1$、$1+1+1$，至多一个高秩块，故已实际嵌入的这些仪器在参考目录精确实现，在有效 dyadic 目录逼近任意正精度；坐标分拆直接扫描可精确。四维已经有 $2+2$ 的正误差。该能力关系既不选择物理空间维数，也不解释物理宇宙为何三能级。

[全输入恢复§6][XII146REC]的标准实际旗标复 Kraus 判据为操作界限提供解释：全未知块及全部参考的无损恢复，要求每个真实可见 $x$ 内所有复交叉项 $K_{xa}^\dagger K_{xb}=\gamma_{x,ab}I$；不能仅查对角或实部。非标量细读不能靠把细标签改写成同一粗名字纠正。该 Knill–Laflamme／Gregoratti–Werner 型判据是既有供应，本章结论是其特定一激发／全记录条件下的尖锐误差与匹配秩预算。

完整继承 XI145 §145.9 每个原对象、前件、作用域及全部传递引用，包括 XI142.4、XI141.5、XI139.11、THREE_COPY VIII131.8、SAME_READBACK SECTION127.10、125.11、124.9、123.13、EXCLUSION VIII112.9、113.11、IX120.11、THREE_COPY VII121.12、122.14、INTRINSIC_POLAR VI89.7—89.10与全部两尺度式(89.13)、V88.6与87章、原生续卷VII及III的来源／全未来／动态合同、BILATERAL VIII128.H。操作来源 INTRINSIC_POLAR VI 与整球 BILATERAL VI 保持原类型。

同一个装饰元组 $\mathcal O$、共同来源域、全部中点实现、原概率像紧性、全测试表及闭性，零／单位／补／有界倍增、重复标签和每种同中点实现，零、次归一、不等及任意非负质量，过程与参考各自完整相关输入域，均由原消费者供应。原 $L,p,\omega,K,M$、两次使用同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确 PRE 后整个 H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量与空活跃集，均保留原定义；操作映射 $p$、纯标签和根条件不混型。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、旧 support、全部合法未来及每个中间切口、原生与细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption 和资源合同，均保留。原复射线和数学叠加不生成实际相位参考、相干端口、可调用门、接线或权限。

对每个有限 $N\ge1$，仍另供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 与完整效应区间。每个二分割保留 $C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b$，同一产品配对、严格张量单位、全部置换及逆的正性、规范重括号和不连续位置分块。完整二份 $S_2$ 仍量化每个产品或纠缠纯点 $p,q_\ell\in P_2$、每个有限族和 $t_\ell\ge0,\sum_\ell t_\ell=1$，含零权与重复标签，满足 $T_p^{(2)}(\sum_\ell t_\ell q_\ell)=\sum_\ell t_\ell T_{q_\ell}^{(2)}(p)$，其中 $T_p^{(2)}(x)=\inf_{f\in[0,u_2]_{C_2^*},\,f(p)=1}f(x)$，即式(XI145.38)。低二份 $q=1,2$ 的 least／谱性／正面投影与保纯到 Jordan 桥、唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制与秩／实维乘法复型选择、同两因子产品正规形，仍分别供应。

非经典最大复块 $n_r=L\ge2$ 的实际三份资源仍为 $g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r$、$\Delta_r=|g_r\rangle\langle g_r|\in C_3$、$u_3(\Delta_r)=L$，其他扇区零，归一来源 $\Delta_r/L$；不预付三份纯性或实际准备，$L=1$ 按原规则免此资源。本单体支路 $L=3$，二／三份秩九／二十七；高阶整个排除集不再被规定成单体 EB3。形式 $3^N$ 矩阵不支付原复合或其相干 ingress。复合若另获本章有限一激发嵌入，可出现多个高秩块；单体零 infimum 不推出复合仪器普适性。

对全部份数和原实线性 $F:W_m\to W_n$，全旁观正性仍量化每个 $b\ge0$ 和每个含纠缠的同一输入：$(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}$。实际完整层级与共同表示齐备后，才由原 Choi 桥识别 CP 及矩形跨扇区 Kraus。TP／TNI 对每个 $x\in C_m$ 分别要求 $u_n(Fx)=u_m(x)$／$\le u_m(x)$；同族分支预算对同一输入逐点承担。实际事件的 CP 仍需完整提升、实际探针及相容核；全部数学 CP-TNI 分支成为实际事件仍需事件饱和。仪器的共同输入预算、接线、记录、粗粒化、输出校准均另供。仅正质量分支可条件归一；Lüders 更新另需同一分支锐效应、接受态中性和输出校准。

原物理钟、实际动态来源、连续齐次可逆时间群及单位各自独立。另供全实时间连续线性群 $A_t$、$A_0=I$、$A_{s+t}=A_sA_t$、$A_t(C)=C$、$uA_t=u$ 后，才有该额外时间族的有限维生成元；再供复块保迹酉时间族，才用 $U_t=e^{-itH/\hbar}$、$\rho_t=U_t\rho U_t^*$、$\mathcal L(\rho)=-i[H,\rho]/\hbar$，$H=H^*$，量化全部原输入和实际时间。$H$ 标量平移、时间重标、能量识别与标定、数值 $\hbar$、时空和无限支持准备仍保原义务。恒等时间族与非平凡 Hamiltonian 族可有相同静态对象；九维实载体、四维纯域、三维排除球及零图边数不指定物理时空。

因此本章没有删除原重构目标的公理，也没有把条件操作定理当作无输入物理起源。裸 EB3、去掉 Inj 的 EB3+九维、以及 EB3+Conn 的自动九维上界，仍按 XI145保留为各自的原问题。XI145的持续原几何重构范围及完整物理合同保持；本章只在另给的操作目录中证明其锐菜单接口的能力与限制。证毕。

### 146.9 完整中文几何解释

**定理146.3的证明释义（中文几何图景）。** 把一个激发想成在许多真实、已接线房间之间保持未知波幅的一颗粒子。粗菜单把房间分成大厅；目标只宣布哪个大厅，同时保留大厅内部所有未知相位及它与未触外部参考的关系。大厅的秩是独立模式数，不是物理空间维数。这个图景对应已经声明的单激发装置，不替代其全部量子和来源前提。

读到“空”只排除一个模式，其他波幅仍可相干；第一次读到“有”时，整个可访问 bank 唯一激发被定位到一条射线，从输入到该分支的算子只剩秩一。以后接线、增长真空房间、酉和反馈不能把该分支丢掉的未知参考纠缠复原。固定共同经典控制故事只有一条全零路线，它最多给一个大厅一个无点击返回出口，也可能永不返回。后者记为 $\bot$，不能当作成功出口；总返回合同保证它没有遗漏的正概率实际输出。

最优构造真实采样一个保护大厅，只扫描其他大厅的房间。粒子在保护大厅时全空读数保留整个未知大厅态；在别的大厅则于某细房间点击。全部空读、点击、停止位置、采样位和控制字符串保留，最后转回原实际码模式。理想比较者使用同一套完整记录标签，在未保护大厅里独立均匀赋予一个细房间标签，却保留整个未知大厅态；没有人擦掉实际房间名。

秩 $k$ 大厅与一个未触 $k$ 维参考组成的 $\Phi_b$ 是理想的一条纠缠射线；实际点击分支是 laboratory 与参考的乘积，对该射线张量所有其他输出的平方投影至多 $1/k$。真实记录使各块的二维斜向差保留下来。引理146.4允许理想方任意挪动记录质量，仍受平方根支持距离约束；(XII146.8)证明挪到其他标签也不能省掉基本代价 $\sqrt{1-1/k}$。无点击实际出口即使被扰动也不能改善下界，因为证明只用了它的总质量。

若不同控制故事在同一真实标签内混合，斜向分量可能抵消；不能假装它们位于不同物理抽屉后把长度相加。实际控制解析为所用故事供应真实 backing、保留权和输出；数学 tape 只是计算每个出口份额的账本。全部记录直和／直积分只把已经发生的有限故事放入共同数学比较，不要求先造无限房间、预录反事实选择或取得隐藏 Kraus 指标。

每个高秩大厅要求份额 $w_i$，未保护时最坏误差为 $\alpha_i(1-w_i)$。一次控制故事至多一个返回出口，份额总和至多一。最小化最高误差等价于水位方程(XII146.5)：在取得正份额的大厅之间平衡剩余误差。秩一大厅无内部未知相干需要保护，不占份额。两个二维大厅各得一半出口，误差 $1/(2\sqrt2)$；三维码的 $2+1$ 只有一个需保护大厅，可始终留给它。这是 min–max 约束和匹配构造的结论，不是额外物理公设。

XI145识别的是整个原状态体、完整确认菜单、全部效应和排除实心三球。房间—大厅—真实记录的操作解释还需实际未知 ingress、detector、接线、相位控制、保持与记录供应。几何三球不等同实验室空间，有限单激发装置也不等同全部物理宇宙；每个有限联合、全部相关输入、合法未来与中间切口仍按146.8保留。

### 146.10 数学归属与适用范围

**定理146.3的来源约定。** 承重结论是实际控制解析条件下(XII146.4)的全记录秩依赖律、任意理想记录质量下的支持优化、涵盖总返回历史族的下界，以及同接口上不用第二激发的有限匹配扫描和全参考 supremum。有限精度与全原未来沿明确供应的接口消费这些结论，采用 `repo-derived` 数学归属；不作全球优先权或最弱公理断言。

唯一形式零路径、点击秩一、旧 $1/4$、acquisition／activation／全阶段原服务、双计量26角字及其边界分别归 RRO V §§25—36；字面全空间门和 digit 槽归 FARG定义60.1、式(60.2)、定理60.2；实际旗标完整复 Kraus 纠错归全输入恢复§6；完整原静态字典、标准反向及所有物理合同归固定版本 `f24456b4a12` 的 XI145.2、XI145.9与 XI145 §145.9。XI146的有限层推进与本卷 XII145均不是本章操作下界或构造的前提。

外部成熟供应及准确对应为：

* Gerhart Lüders，*Über die Zustandsänderung durch den Meßprozeß*，Ann. Phys. (Leipzig) 8, 322–328 (1951)；K. A. Kirkpatrick译文 [quant-ph/0403007v2][XII146LUD] §2式(1)—(7)，特别式(7)的次归一 $P_kZP_k$。它供应退化投影更新与逐射线细化的标准区别，不供应本装置。
* M. Horodecki、P. W. Shor、M. B. Ruskai，*Entanglement Breaking Channels*，[quant-ph/0302031v2][XII146HSR] Theorem4(B),(D)。rank-one Kraus 的纠缠破坏／可分性是标准机制；本章点击子仪器的次归一结论由实际算子直接给出，平方根常数还需真实记录和引理146.4。
* W. R. Clements等，*Optimal design for universal multiport interferometers*，Optica 3, 1460–1465 (2016)，[1603.08788v2][XII146CLE] Background式(1)—(2)及图1。两模式／相位酉分解是标准数学供应；本章不给其多粒子光学或硬件额外权限。迹范数压缩与收缩、纯化、Jensen、可测概率核和有限 hybrid 同为成熟工具。

未解析旧目录若要获得本章常数，还需实际解析所有会改变同一点击记录内算子链的控制，或另证混合点击分支的尖锐界。在原坐标 $2+2$ 上，旧定理33.1仍给 $1/4$；在本章公平位和记录供给亦被准许时，有限构造给不超过 $1/(2\sqrt2)$ 的上界，二者之间的未解析最优值未由本章确定。已解析目录的值则由定理146.3及其构造确定。有效框架、公平位、全输出校准、实际硬件、有限资源和每个原物理供应条件不能由该值反推。

[XII146RRO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_V.md "90a0a6390171837fa6aa82254c7ad323341f0657；定义25.1、27.1、32.1—32.2，定理27.2、29.2、33.1、35.1、36.1及命题29.3。"
[XII146FARG]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md "90a0a6390171837fa6aa82254c7ad323341f0657；定义60.1、式(60.2)、定理60.2与60.3的私有enable观察边界。"
[XII146REC]: AURIC_FIB_OPTIMAL_MEASUREMENT_QUANTUM_RECOVERY.md#6-全输入与全部参考的复-kraus-判据 "90a0a6390171837fa6aa82254c7ad323341f0657；§6实际旗标复Kraus全码纠错。"
[XII146XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md#145-有限法向转移九维同根纯芽与完整原域复三能级 "f24456b4a12；XI145.2主定理、XI145.9完整静态字典、XI145 §145.9全部物理合同及其传递引用。"
[XII146LUD]: https://arxiv.org/pdf/quant-ph/0403007v2
[XII146HSR]: https://arxiv.org/pdf/quant-ph/0302031v2
[XII146CLE]: https://arxiv.org/pdf/1603.08788v2

## 追加锚（本行以下为增补区）

## 147. 裸 EB3 的九维下界与单标签完整法向

本章在整个原锥、原单位、原状态体和全效应区间上证明：裸完整 EB3 已要求 $\dim_{\mathbb R}V\ge9$；在九维等号处，每个实际单标签纯点都有唯一整球确认和完整四维原法向接口。证明复用既有原面分类、标签二分及有限法向层覆盖，以单标签球与极限一值面的实际接触排除极限重复零球，将有限见证、两步四维紧块和法向尺寸论证接到单标签区域。全局 Inj 仍未证明；同锥同单位的复三能级分类及完整静态字典分别按 EXCLUSION XI 的定理145.2、条件应用145.9，在其完整前件下使用。

### 147.1 原对象、供应与主结论

取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$，及在 $C\setminus\{0\}$ 上严格正的 $u\in V^*$。始终取整个

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x),\qquad D_p=\{x\in K:T_p(x)=0\},\\
S_p=P\cap D_p,\qquad
\mathcal A_p=\{e\in\mathcal E:e(p)=1,\ e|_{D_p}=0\},\\
N_p=\{h\in C^*:h(p)=0\},\qquad L_p=\operatorname{span}_{\mathbb R}N_p,\\
N_F=\{h\in C^*:h|_F=0\},\qquad
a(p)=\dim_{\rm aff}\mathcal A_p,\\
\mathscr B=\{D_p:p\in P\},\qquad
I(F)=\{p\in P:D_p=F\},\qquad
P_{\rm s}=\{p\in P:I(D_p)=\{p\}\}.
\end{gathered}
\tag{XII147.1}
$$

EB3 指对每个 $p\in P$，**整个** $D_p$ 都仿射同构于非退化闭三球。纯关系 $p\perp q\Longleftrightarrow q\in D_p$ 表示某张原效应在两端读一、零；补效应给对称，且 $p\not\perp p$。$K,\mathcal E,F_p$ 紧，全部 minimum 达到；$K$ 张成 $V$，$\operatorname{aff}K=\{u=1\}$。辅助欧氏结构仅用于紧性和参数化。$\operatorname{Aff}(D_p)$ 表示整个原球上的实仿射函数空间。

本章精确使用以下既有供应；跨卷条目以定理、引理或节区分，带 XII 前缀的编号均指本章公式。

* FINITE_PURE VII 的定理103.2：每个 $D_p$ 是紧暴露极大真面，$\mathcal A_p\ne\varnothing$；每个非空真面是纯单点或整个 $D_p$，不预先要求面闭。$S_p$ 是整张球面的全部原纯点；不同球的交为空或一个原纯点。
* EXCLUSION IX 的定理116.2、116.6：每个球或者单标签，或者与唯一不交球 $G$ 配对，$I(F)=S(G), I(G)=S(F)$，其中 $S(F)=P\cap F$；两球均不交第三张不同球。$P_{\rm s}\ne\varnothing$，且 $p\in P_{\rm s},q\perp p\Rightarrow q\in P_{\rm s}$。因此本章所有从单标签点出发的有限零边路都留在 $P_{\rm s}$；这不是 $P_{\rm s}=P$。SAME_READBACK 第126.5节的 $P_{\mathrm s}=P\setminus R$ 与此定义相同，因重复块的球缘及标签恰互为配对球缘。
* SAME_READBACK 引理128.2及其证明：对任意有非空内部的 $m$ 维紧凸体及每个 $1\le k\le m$，法向锥张成维数至少 $k$ 的全部边界点有可数紧覆盖；每层向某个 $m-k$ 维线性空间的正交投影单射，逆满足 $2/\sqrt3$ 的 Lipschitz 界。本章在第147.6节取 $m=8,k=5$，在第147.8节取 $m=8,k=4$，在第147.12节取一般 $m$ 和 $k=4$。它是全点覆盖，不是删去零测例外的可求长性断言。

EXCLUSION IX 的引理119.1、定理119.10及 BILATERAL VIII 的引理121.2—121.4、定理121.5—121.6原来使用全局 Inj。下面展开其在本域所需的局部替换，尤其不直接搬用 VIII 引理121.3的极限纯性。LOCAL_PURE_LIMIT_CONTINUATION 引理132.3、THREE_COPY VIII 引理131.2已供应单标签球混内部极限的反向整球塌缩；第147.3节给出与本有限见证直接相接的端面形式。它不另计为一般凸分析原理。

**主结论总览。** 裸 EB3 给整个原空间的下界 $\dim_{\mathbb R}V\ge9$，证明见推论147.8。等号处有下述定理147.1及命题147.6—147.7的局部完整接口。仍未支付的全局箭头是 $\mathrm{EB3}+\dim_{\mathbb R}V=9\Rightarrow P_{\rm s}=P$，即全局 Inj；它不包含在本章结论内。

**定理 147.1（九维单标签区域的完整原确认）。** 若 EB3 且整个 $\dim_{\mathbb R}V=9$，则对每个 $p\in P_{\rm s}$，

$$
\mathcal A_p=\{e_p\},\qquad \dim L_p=4,\qquad
N_{D_p}=\mathbb R_+e_p.
\tag{XII147.2}
$$

此外，$e_p$ 的整个零面为 $D_p$、整个一值面为 $\{p\}$；置 $g_p=u-e_p$，则

$$
R_p:L_p\overset\sim\longrightarrow\operatorname{Aff}(D_p),\quad h\mapsto h|_{D_p},
\qquad g_p\in\operatorname{ri}N_p,\qquad K\cap\ker g_p=\{p\}.
\tag{XII147.3}
$$

第147.7节还给全部原法向的边界射线、完整归一法向基、固定整张 $S_p$ 上的 Lipschitz 确认效应及原全边效应区间。这里没有把 $\mathcal A_p$ 与整个 $F_p$ 混同，没有断言 $R_p^{-1}$ 为正映射或 $e_p$ 是 $F_p$ 的 least。式(XII147.2)的证明在第147.6节完成，第147.7节证明式(XII147.3)及其全部所列接口。

### 147.2 仅在实际单标签处使用端面唯一性

**引理 147.2（局部端面与冗余公式）。** 在 EB3 下，对每个 $p\in P_{\rm s}$ 有

$$
\begin{gathered}
e\in\mathcal A_p\Rightarrow
K\cap\{e=0\}=D_p,\quad K\cap\{e=1\}=\{p\},\\
\max_K h=\max_{D_p}h\quad(h\in N_p),\\
\dim L_p=a(p)+4,\qquad
N_{D_p}=\operatorname{cone}\mathcal A_p,\qquad
\dim\operatorname{span}N_{D_p}=a(p)+1,\\
q\in S_p\Rightarrow a(q)=a(p).
\end{gathered}
\tag{XII147.4}
$$

证明。零面包含极大真面 $D_p$，又不含 $p$，故恰为 $D_p$。若原纯 $s$ 在 $e$ 取一，则 $D_p\subseteq D_s$，极大性给 $D_s=D_p$，本点的单标签性给 $s=p$。紧一值面由其原极点凸生成，故是 $\{p\}$。

对非零 $h\in N_p$，令 $M=\max_Kh>0$，在最大面取原纯 $s$。原效应 $h/M$ 在 $s,p$ 读一、零，故 $s\in D_p$，得到最大值公式。零函数亦满足。此公式本身不需单标签性。

写 $D_p=c+B\overline{\mathbb B}^3$，$B:\mathbb R^3\to\ker u$ 单射。每个 $q_v=c+Bv\in S_p$，$\|v\|=1$，亦在 $P_{\rm s}$。任取 $b_v\in\mathcal A_{q_v}$，则 $b_v(p)=0$，且球支持等号给

$$
b_v(c+Bw)=1-\beta_v+\beta_v v\cdot w,
\qquad 0<\beta_v\le\tfrac12.
\tag{XII147.5}
$$

斜率为零会使 $b_v$ 在整张 $D_p$ 为一，违反已证一值面仅含 $q_v$。在六个轴端点选一次效应，再加 $u-e\in N_p$、其在 $D_p$ 恒为一，便知 $R_p:L_p\to\operatorname{Aff}(D_p)$ 满射。这只用了 $p$ 及其六个原邻点的单标签性。

对 $h\in\operatorname{ri}N_p$，其零面是 $N_p$ 的公共零集：任意 $k\in N_p$ 有某个 $t>0$ 使 $h-tk\in N_p$，故 $h(x)=0\Rightarrow k(x)=0$。$u-e\in N_p$ 的零面已是 $\{p\}$，所以 $h$ 也恰在 $p$ 为零。

取非零 $h_0\in\operatorname{ri}N_p$，写其球限制为 $\alpha+v\cdot w$。若 $v\ne0$，加上式(XII147.5)中方向 $-v/\|v\|$ 的一个非负倍数，消去斜率。相对内部加锥仍在相对内部；所得非零正泛函的限制为常数，正性及最大值公式保证此常数严格正。归一得

$$
g_c\in\operatorname{ri}N_p,\qquad g_c|_{D_p}=1.
\tag{XII147.6}
$$

这里 $g_c$ 只是本证明所取的常数限制代表。准确切片等式为

$$
\mathcal A_p=u-\{g\in N_p:R_pg=1\}.
\tag{XII147.7}
$$

其中 $g\le u$ 由原最大值公式在整个 $K$、继而整个 $C$ 上支付。切片遇相对内部，仿射维数是 $\dim L_p-4$。这证明第一维数公式。

若 $0\ne h\in N_{D_p}$，令 $M=\max_Kh>0$，则 $h/M$ 的任何纯最大点 $s$ 满足 $D_s=D_p$，故 $s=p$，$M=h(p)>0$，且 $h/M\in\mathcal A_p$。于是 $N_{D_p}=\operatorname{cone}\mathcal A_p$，而 $\mathcal A_p$ 是其 $h(p)=1$ 紧切片，给后一维数公式。

最后固定 $q=c+Bv\in S_p$。$\mathcal A_q\subset N_p$，其限制都属仿射族 $1-\beta+\beta v\cdot w$。允许 $\beta\in\mathbb R$，将该限制族在 $L_p$ 中的逆像记为 $J_q$；其维数为 $\dim\ker R_p+1=a(p)+1$。选 $k\in L_p$ 满足 $R_pk=v\cdot w$，则充分小 $t>0$ 时

$$
h=(g_c+tk)/(1+t)\in\operatorname{ri}N_p\cap J_q.
$$

取 $r\in D_q\setminus\{p\}$。已证 $h(r)>0$，而全部 $\mathcal A_q$ 在 $r$ 为零。因此评价 $r$ 在 $J_q$ 中切出真仿射超平面，$a(q)\le a(p)$。交换 $p,q$，二者均已在 $P_{\rm s}$，得反向不等式。没有使用别的图分支的标签唯一性。证毕。

### 147.3 接触单标签球的非点零效应必确认纯点

**引理 147.3（端面接触的纯性桥）。** 在 EB3 下，设 $q\in P_{\rm s}$、$x\in D_q$、$g\in\mathcal E$，且 $g(x)=1$。若 $Z=K\cap\ker g$ 非空且非点，则存在 $z\in P_{\rm s}$，使

$$
Z=D_z,\qquad K\cap\{g=1\}=\{z\},\qquad x=z,\qquad g\in\mathcal A_z.
\tag{XII147.8}
$$

特别地，假设中的 $x$ 不必先纯。

证明。$g(x)=1$ 及非空零集使 $g$ 非恒定；原面分类给 $Z\in\mathscr B$。记紧一值面为 $M$。其任一原纯点 $t$ 满足 $Z\subseteq D_t$，故由极大性 $D_t=Z$，即 $\operatorname{ext}M\subseteq I(Z)$。

若 $Z$ 重复，IX 定理116.2给配对球 $G$，$I(Z)=S(G)$，从而 $M\subseteq\operatorname{conv}S(G)=G$。但 $x\in M\cap D_q$，所以 $G\cap D_q\ne\varnothing$。重复球 $G$ 不交第三球，且其配对球 $Z$ 与它不交，故只能 $D_q=G$。这使 $D_q$ 重复，与 $q\in P_{\rm s}$ 矛盾。此步明确处理了极限零球可能变成重复球的分支。

因此 $I(Z)=\{z\}$。$M$ 的全部原极点只有 $z$，故 $M=\{z\}$。于是 $x=z\in P$、$D_z=Z$，$z\in P_{\rm s}$，而 $g\in\mathcal A_z$。证毕。

此引理所付的是**原域有限见证极限的纯性**。它不是以“极限本来纯”重写定义，也没有把 $\bigcup_{f\in F_q}\{f=0\}$ 换成各零面的交。另一路同样有效的供应是既有 LOCAL_PURE_LIMIT_CONTINUATION 引理132.3：若上述接触极限落在 $\operatorname{ri}D_q$，对应纯采样标签的下一层整球须缩到 $q$，与保留的非退化四面体矛盾。

### 147.4 固定原球面上的有限闭层

以下第147.4—147.5节不使用九维。固定 $p\in P_{\rm s}$、任意非空相对开集 $U\subset S_p$，在其中取闭二盘 $Q$，其球面内部非空。所有移动 $q$ 均在这同一紧盘中，因而 $q\in P_{\rm s}$。

固定辅助欧氏结构，令 $\xi(x)=x\otimes x\in\operatorname{Sym}^2V$，定义

$$
\Gamma(x_1,\ldots,x_9)=
\det[\langle\xi(x_i),\xi(x_j)\rangle]_{i,j=1}^9,\qquad
\tau(y_0,y_1,y_2,y_3)=
\det[\langle y_a-y_0,y_b-y_0\rangle]_{a,b=1}^3.
\tag{XII147.9}
$$

前者严格正表示九个二次评估泛函独立，后者严格正表示四点仿射无关。

**引理 147.4（局部有限闭层及整球连续）。** 对每个整数 $m\ge1$，令 $Q_m\subset Q$ 由下列存在条件定义：

$$
\begin{gathered}
x_1,\ldots,x_9\in S_q,\qquad \Gamma(x_1,\ldots,x_9)\ge1/m,\\
g_j\in\mathcal A_{x_j},\qquad
y_{j0},\ldots,y_{j3}\in D_{x_j},\qquad
\tau(y_{j0},\ldots,y_{j3})\ge1/m\quad(1\le j\le9).
\end{gathered}
\tag{XII147.10}
$$

则 $Q=\bigcup_{m\ge1}Q_m$，每个 $Q_m$ 紧，且 $q\mapsto D_q$ 在每层按原环境 Hausdorff 距离连续。因此任意 $U$ 中有较小闭二盘 $Q'\subset U$，其球面内部非空，在其上整球连续。

证明。每个实际三球的边界上有九个二次评估独立点：在标准 $S^2$ 取六个轴端点及

$$
(e_1+e_2)/\sqrt2,\quad(e_1+e_3)/\sqrt2,\quad(e_2+e_3)/\sqrt2.
$$

次数至多二的多项式 $c+\ell\cdot t+t^*At$，其中 $A$ 对称，若在这九点为零，六轴点给 $\ell=0,A_{ii}=-c$，后三点给全部非对角 $A_{ij}=0$。故核恰为 $c(1-\|t\|^2)$，十维多项式空间的评估秩为九。齐次化到四维 $\operatorname{span}D_q$，再延伸到 $V$，不改此秩。每个下一层实际三球 $D_{x_j}$ 又含非退化四面体。有限个严格正量可用同一 $1/m$ 下界，得到覆盖。

设 $q_n\in Q_m\to q\in Q$。在紧 $K,\mathcal E$ 的有限乘积中，将全部见证及任取 $e_n\in\mathcal A_{q_n}$ 一起取共同收敛子列，极限记为 $x_j,y_{jk},g_j,e$。有

$$
e(q)=1,\quad e(x_j)=0,\quad g_j(x_j)=1,\quad
g_j(y_{jk})=0,\quad\tau(y_{j0},\ldots,y_{j3})\ge1/m.
\tag{XII147.11}
$$

第一对等式只先给 $x_j\in D_q$，不先给纯性。后一四面体使 $g_j$ 的零面非点。现在 $q\in P_{\rm s}$ 已由固定盘支付，引理147.3逐个给 $x_j\in S_q\cap P_{\rm s}$、$g_j\in\mathcal A_{x_j}$，且所有 $y_{jk}\in D_{x_j}$。连续评价保留 $\Gamma\ge1/m$。所以极限见证仍满足式(XII147.10)，$Q_m$ 闭于紧 $Q$。这正是全局 Inj 未被预付的闭性步骤。

再设 $q_n\to q$ 于同一 $Q_m$。写

$$
D_{q_n}=c_n+B_n\overline{\mathbb B}^3,
\qquad \|B_n\|\le\operatorname{diam}K/2.
$$

该界由全部 $c_n\pm B_nt\in K$，$\|t\|=1$，给出，不假设连续选轴。任意子列可再取 $c_n\to c,B_n\to B,e_n\to e$，故整球趋于 $E=c+B\overline{\mathbb B}^3\subseteq D_q$。同时取全部有限见证极限；已证九个极限点 $x_j\in E\cap S_q$，评估秩仍九。

若 $B$ 秩至多二，九点位于仿射维数至多二的空间，次数至多二的多项式空间维数至多六，矛盾。因此 $E$ 为非退化三椭球，与 $D_q$ 有同一仿射三平面。每个 $x_j$ 是 $D_q$ 的极点，因 $x_j\in E\subseteq D_q$，亦是 $E$ 的极点。两边界二次形式均在该四维齐次空间的九点评估核中；核维数是一，故二次形式成非零比例，边界相同，取其凸包得 $E=D_q$。任意子列再极限均如此，故整列趋于 $D_q$。

紧二盘 $Q$ 是 Baire 空间，可数闭覆盖中某层有非空相对内部；盘边界在盘中无处稠密，故可在这一内部中取球面内部非空的较小闭二盘 $Q'$。证毕。

### 147.5 两条原边给真正四维紧块

**引理 147.5（单标签区域的两步四维块）。** 对每个 $p\in P_{\rm s}$ 及非空相对开 $U\subset S_p$，集合

$$
\{r\in P_{\rm s}\setminus\{p\}:\exists q\in U,\ p\perp q\perp r\}
\tag{XII147.12}
$$

含一个与 $[0,1]^4$ 同胚的原环境紧集。块上每点满足 $a(r)=a(p)$。

证明。在引理147.4的连续盘 $Q'$ 上，整球确定连续中心 $c(q)$ 及连续秩三形状算子 $A(q)$。具体地，在 $\{u=1\}$ 固定参考点 $o$，支撑函数 $h_q(v)=\max_{D_q}\langle v,x-o\rangle$ 给

$$
\langle v,c(q)-o\rangle=\tfrac12(h_q(v)-h_q(-v)),\qquad
\langle v,A(q)v\rangle=(h_q(v)-\langle v,c(q)-o\rangle)^2.
$$

Hausdorff 连续性给支撑函数在单位方向上一致连续，第二式经极化确定连续的 $A(q)$。在一个内点 $q_0$ 附近，取三个固定向量，使其 $A(q_0)$ 像独立；连续性及 Gram—Schmidt 给 $\operatorname{im}A(q)$ 的局部连续正交标架 $W(q):\mathbb R^3\to\ker u$。令 $B(q)=A(q)^{1/2}W(q)$，则

$$
D_q=c(q)+B(q)\overline{\mathbb B}^3,\qquad S_q=c(q)+B(q)S^2
$$

连续，且 $B(q)$ 单射。每个 $S_q$ 含共同原纯点 $p$。在 $q_0$ 的参数球上取紧二帽 $T$，像避开 $p$；联合连续及紧性允许缩小底盘 $Q''\subset Q'$，使全部像仍避开 $p$。底盘和帽各取闭方盘。

映射 $\Psi(q,t)=c(q)+B(q)t$ 在 $Q''\times T$ 上连续。固定 $q$ 时单射。不同 $q,q'$ 都在 $P_{\rm s}$，故 $D_q\ne D_{q'}$；二球都含 $p$，点交规则使交恰为 $\{p\}$，而两帽避开此点。故跨标签亦单射。紧源至 Hausdorff 原环境的连续单射是到像的同胚，给紧四立方体。像点是实际球缘原纯点；单标签邻点闭包给它们均在 $P_{\rm s}$。引理147.2沿两条实际边给 $a(r)=a(q)=a(p)$。证毕。

这不是声称该块内部相对于 $P_{\rm s}$ 开，更不是相对于全部 $P$ 开。

### 147.6 原八维法向层排除单标签处的全部冗余

**定理147.1中式(XII147.2)的证明。** 在 $H=\ker u$ 的八维仿射原状态空间中，正法向与通常外法向有准确锥同构

$$
N_r\longrightarrow\mathcal N_K(r),\qquad h\longmapsto-h|_H.
\tag{XII147.13}
$$

这里 $\mathcal N_K(r)=\{v\in H^*:v(x-r)\le0\ \forall x\in K\}$。核为零：限制为零的 $h$ 是 $u$ 的倍数，而 $h(r)=0$ 消去该倍数。反向，对外法向 $v\in H^*$，定义 $h(x)=-v(x-u(x)r)$；其在整个 $K$、继而整个 $C$ 非负，且零于 $r$。故维数不加减一。这一识别本身与八维无关。

假设某 $p\in P_{\rm s}$ 有 $a(p)\ge1$。引理147.5给原纯紧四块 $F:[0,1]^4\hookrightarrow P_{\rm s}$，块上每个 $r$ 都有 $a(r)\ge1$，引理147.2给 $\dim\operatorname{span}\mathcal N_K(r)\ge5$。因此块的整个像位于原八维凸体的 $\Sigma_5(K)$。

为明确所用覆盖的强度，SAME_READBACK 引理128.2的构造如下。选有理 $b_0,b_1,\ldots,b_5\in H^*$，后五个独立，$E=\operatorname{span}\{b_1,\ldots,b_5\}$；取有理 $\varepsilon>0$，满足 $\sqrt5\varepsilon/\sigma<1/2$，其中 $\sigma$ 是 $E\to\mathbb R^5$、$v\mapsto(\langle b_j,v\rangle)_j$ 的最小奇异值。辅助内积在此识别 $H,H^*$。令 $X$ 是所有法向锥分别遇到十个闭球 $\overline B(b_0\pm b_j,\varepsilon)$ 的边界点。有限见证在固定紧球中及法向图闭给 $X$ 紧。凸法向单调性对 $x,y\in X$ 给

$$
|\langle b_j,x-y\rangle|\le\varepsilon\|x-y\|,
\qquad \|\operatorname{proj}_E(x-y)\|\le\tfrac12\|x-y\|.
$$

故投影到三维 $E^\perp$ 单射，其逆满足 $2/\sqrt3$ 界。任何至少五维法向锥都有相对内点及五对独立短扰动；将其充分精确逼近为上述有理数据便落在某层。可数有理数据给覆盖全部 $\Sigma_5(K)$ 的紧集 $X_j$。此构造不要求层中点纯，不涉及未知球族紧性。

闭集 $F^{-1}(X_j)$ 可数覆盖紧四立方体。Baire 性及立方体内部稠密性给非空欧氏开集 $O\subset(0,1)^4$，使 $F(O)\subseteq X_j$ 于某同一层。于是 $\pi_jF:O\to\mathbb R^3$ 连续单射。将靶线性嵌入 $\mathbb R^4$ 的坐标超平面，区域不变性要求复合像在 $\mathbb R^4$ 中开，与其落在三维超平面矛盾。

因此每个 $p\in P_{\rm s}$ 都有 $a(p)=0$。非空紧凸 $\mathcal A_p$ 遂为单点，引理147.2给 $\dim L_p=4,N_{D_p}=\mathbb R_+e_p$。这个证明无需 $P_{\rm s}$ 闭、紧、Baire 或是流形；两次 Baire 的源分别是实际紧二盘和实际紧四立方体。证毕。

### 147.7 完整原法向、原边效应区间与归一基

**命题 147.6（限制同构、完整边区间与完整法向基）。** 在定理147.1的前件下，固定任意 $p\in P_{\rm s}$，写 $D_p=c+B\overline{\mathbb B}^3$。则式(XII147.3)成立。对 $i=1,2,3$，唯一取 $H_i\in L_p$，使 $H(c+Bw)=w$，其中 $H=(H_1,H_2,H_3)$。定义

$$
\rho_p(v)=\sup_{x\in K\setminus\{p\}}
\frac{-v\cdot H(x)}{g_p(x)}\qquad(v\in\mathbb R^3).
\tag{XII147.14}
$$

它有限、正齐次、次可加、Lipschitz，且 $\rho_p(v)\ge\|v\|$。有准确的原锥及原最大值公式

$$
N_p=\{\alpha g_p+v\cdot H:\alpha\ge\rho_p(v)\},\qquad
\max_K(\alpha g_p+v\cdot H)=\alpha+\|v\|\quad(\alpha\ge\rho_p(v)).
\tag{XII147.15}
$$

对每个 $t\in S^2$、$q_t=c+Bt$，有整个 $V$ 上的等式

$$
e_{q_t}=\frac{\rho_p(t)g_p+t\cdot H}{1+\rho_p(t)},\qquad
\{b\in\mathcal E:b(p)=0,b(q_t)=1\}=[g_p,e_{q_t}].
\tag{XII147.16}
$$

特别地 $t\mapsto e_{q_t}$ 在固定整张原球面上 Lipschitz。

$N_p$ 在四维 $L_p$ 中闭、尖、满维、严格凸，其全部非零边界射线恰为 $\mathbb R_+e_q$，$q\in S_p$，均为暴露极射线。固定任意 $z\in\operatorname{ri}K$，则全部原归一法向基满足

$$
B_p^*=\{h\in N_p:h(z)=1\}
=\operatorname{conv}\{e_q/e_q(z):q\in S_p\}.
\tag{XII147.17}
$$

这里是有限凸组合，无须另取闭包，每项至多四个生成元。

证明。引理147.2的满射与两边维数四给 $R_p$ 同构。式(XII147.6)中的 $g_c$ 由切片等式(XII147.7)及 $\mathcal A_p=\{e_p\}$ 必为 $g_p$，故 $g_p\in\operatorname{ri}N_p$。其零集为 $\{p\}$ 已由端面唯一性证明，故式(XII147.14)分母在全部所写定义域严格正。

取统一 $\delta>0$，使 $g_p\pm\delta H_i\in N_p$。于是整个 $K$ 上 $\|H(x)\|\le\sqrt3g_p(x)/\delta$。这给式(XII147.14)的有限性及 Lipschitz 界；$v\ne0$ 时代入 $c-Bv/\|v\|$ 给 $\rho_p(v)\ge\|v\|$，$v=0$ 时直接成立。正齐次与次可加由上确界定义给出。限制同构使每个 $L_p$ 元素唯一写成 $\alpha g_p+v\cdot H$，其原正性恰为式(XII147.15)的不等式；只有正性已付以后才用引理147.2的全域最大值公式，得到第二式。

若 $b\in\mathcal E,b(p)=0,b(q_t)=1$，球支持等号及限制同构给

$$
b=(1-\beta)g_p+\beta t\cdot H,\qquad
0\le\beta\le(1+\rho_p(t))^{-1}.
$$

反向每个此范围的泛函由式(XII147.15)在原 $C$ 上非负，且全域最大值为一，故属于整个 $\mathcal E$。取 $e_{q_t}\in\mathcal A_{q_t}$，这里 $q_t\in P_{\rm s}$ 已由邻点闭包支付。其参数不为零，否则它在整张 $D_p$ 为一。取 $y\in D_{q_t}\setminus\{p\}$，则 $g_p(y)>0$，而 $e_{q_t}(y)=0$ 给 $(1-\beta)/\beta\le\rho_p(t)$；正性给反向不等式，所以参数恰取上端点，证明式(XII147.16)及其 Lipschitz 性。

式(XII147.15)表明非零边界为 $\alpha=\rho_p(v),v\ne0$，经正齐次化即全部所述射线。对 $q\in S_p$，取 $x_q\in\operatorname{ri}D_q$。正泛函在该相对内点零便零于整个 $D_q$，故

$$
N_p\cap\{h:h(x_q)=0\}=N_{D_q}=\mathbb R_+e_q.
$$

右侧确实在 $N_p$，因 $p\in D_q$。这用的是 $q\in P_{\rm s}$ 已付的完整零面法向射线，故每条边界射线暴露且极端。若两个不成比例的非零锥元之和在边界，其暴露评价在两项上均零，迫它们同属一条射线，矛盾。闭、尖来自原 $C^*$，满维来自 $g_p\in\operatorname{ri}N_p$。

$z$ 是 $C$ 的内点，故每个非零原正泛函有 $h(z)>0$，且有统一 $d>0$ 使 $h(z)\ge d\|h\|$。所以 $B_p^*$ 是三维紧凸基。其极点恰对应上面全部极射线，有限维极点生成及 Carathéodory 给式(XII147.17)和四项界。固定球面效应连续还保证生成集合紧。以上是同一原法向锥的全部基，不是有限预选效应所张的子锥。证毕。

注意，$R_p$ 是线性同构不表示 $R_p(N_p)=\operatorname{Aff}(D_p)_+$。由式(XII147.15)，后者等式恰要求全部方向 $\rho_p(v)=\|v\|$，本章未证明此饱和。唯一整球确认也未给 $T_p(x)=e_p(x)$ 对每个原混输入成立。

### 147.8 有限正法向转移的准确局部适用域

**命题 147.7（局部有限转移与紧层连续）。** 在定理147.1的前件下，设 $p_i,p\in P_{\rm s},p_i\to p$，且存在有限整数 $M\ge1$ 和原正法向 $h_i^\ell\in N_{p_i}$，$1\le\ell\le M$，满足

$$
h_i^\ell\to h^\ell,\qquad
\operatorname{span}\{h^\ell:1\le\ell\le M\}=L_p.
\tag{XII147.18}
$$

则 $D_{p_i}\to D_p,e_{p_i}\to e_p$，并且 $L_{p_i}\to L_p$ 于四维子空间的 Grassmann 空间。

对 SAME_READBACK 引理128.2在原八维凸体取 $k=4$ 的紧层 $X_j$，上述连续性适用于每个 $P_{\rm s}\cap X_j$ 的子空间拓扑。特别地，对每张固定 $S_p$，$p\in P_{\rm s}$，集合 $S_p\cap X_j$ 是实际可数紧覆盖，整球、完整确认效应及法向**张成空间**在各层连续。还可对任意事先指定的紧 $A\subset P_{\rm s}$ 取紧层 $A\cap X_j$。

证明。在任一子列取有界椭球参数及效应极限，得 $E\subseteq D_p$。正锥和评价的闭性给 $h^\ell\in N_p$。对全部固定非负系数 $a_\ell$，原最大值公式给

$$
\max_E\sum_{\ell=1}^M a_\ell h^\ell
=\max_K\sum_{\ell=1}^M a_\ell h^\ell
=\max_{D_p}\sum_{\ell=1}^M a_\ell h^\ell.
$$

这里用同一个参数子列，且泛函在紧 $K$ 上一致收敛，不按系数组更换极限球。有限正锥 $\operatorname{cone}\{h^\ell\}$ 在四维 $L_p$ 中有非空内部；经限制同构再取球上线性部分，其像含三维开集，故非零斜率方向含球面开片。相同最大值迫这些方向在 $D_p$ 上的唯一最大点均在 $E$。因此 $E$ 含 $S_p$ 的球面开片，先迫其秩三。这些点也是 $E$ 的支持点，故两椭球边界二次方程在开片同时消失；二次唯一性给它们成比例，得 $E=D_p$。二次方程在球面开片消失时在整个球面消失，是标准球面参数下多项式的唯一性；也可沿穿过开片的小大圆逐圆使用一元三角多项式唯一性。效应极限于是属于 $\mathcal A_p=\{e_p\}$。任意子列论证给整列收敛。从有限极限组中取四个独立向量，其对应 $h_i^\ell$ 最终仍独立并张成四维 $L_{p_i}$，给张成空间收敛。

在 $k=4$ 的每层 $X_j$，源构造给八个有界外法向见证，分别在固定球 $\overline B(b_0\pm b_\ell,\varepsilon)$ 内，$2\varepsilon/\sigma<1/2$。给定 $p_i\to p$ 于 $P_{\rm s}\cap X_j$，取八个共同极限；四个半差 $d_\ell$ 距 $b_\ell$ 至多 $\varepsilon$，满足

$$
\Big\|\sum_{\ell=1}^4 t_\ell d_\ell\Big\|
\ge(\sigma-2\varepsilon)\|t\|>0\quad(t\ne0).
$$

八个极限因而张满外法向的四维张成空间；用式(XII147.13)补回各个原正法向，它们的极限张满 $L_p$，故式(XII147.18)成立。任意子列再取此共同极限，证明层上连续。紧性结论来自固定 $S_p,A,X_j$ 的原环境紧性。此为 XI 引理145.4—145.5中有限转移步骤的已付局部版本。证毕。

这里未断言全部归一锥基 $B_{p_i}^*\to B_p^*$ 的下连续性。它们在共同紧对偶基中始终有闭图和上包含，但张成空间连续不等于整锥连续。也未断言 $P_{\rm s}\cap X_j$ 自身紧、$P_{\rm s}$ 是 Baire 空间、某个相对开四维图已存在，或层在全部 $P$ 中开。

### 147.9 局部结论与仍未支付的全局箭头

本章结论的准确强度是

$$
\begin{gathered}
\mathrm{EB3}\Longrightarrow\dim_{\mathbb R}V\ge9,\\
\mathrm{EB3}+\dim_{\mathbb R}V=9
\Longrightarrow
\left\{
\begin{array}{l}
P_{\rm s}\ne\varnothing,\quad P_{\rm s}\text{ 沿原零边封闭};\\
\forall p\in P_{\rm s}:\ \text{式(XII147.2)—(XII147.3)、}\\
\qquad\text{式(XII147.15)—(XII147.17)的完整原法向接口};\\
\forall p\in P_{\rm s},\ \forall\,\varnothing\ne U\subseteq S_p
   \text{ 相对开}:\\
\qquad\text{式(XII147.12)含四维紧块，且有命题147.7的紧层连续性}.
\end{array}\right.
\end{gathered}
\tag{XII147.19}
$$

单标签非空性和邻点闭包归 IX 定理116.6；有限层和尺寸工具归上述来源。本章的承重迁移是将第二层极限纯性接回这一单标签域，得到**每一个**单标签处的唯一完整确认和四维完整原法向，并在不使用九维等号的同一四维紧块上给出裸 EB3 的九维下界。相应法向消费者只在 $P_{\rm s}$ 上取得已付前件；全局 Inj 未隐藏在局部记号中。

仍未证明的全局箭头是

$$
\mathrm{EB3}+\dim_{\mathbb R}V=9\
\mathrel{\mathop{\Longrightarrow}^{?}}\ P_{\rm s}=P.
\tag{XII147.20}
$$

在本域 $P_{\rm s}=P$ 准确等价于全局 Inj；若另得到它，才可直接消费 EXCLUSION XI 定理145.2的既有完整等价，其 Inj 分支的充分接口迁移见 XI 命题145.8。下面的 $\Phi$ 遍历实线性双射：

$$
\begin{gathered}
\mathrm{EB3}+\mathrm{Inj}+\dim_{\mathbb R}V=9\\
\Longleftrightarrow\
\exists\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,\qquad
\Phi(\operatorname{PSD}_3(\mathbb C))=C,\quad u\circ\Phi=\operatorname{Tr}.
\end{gathered}
\tag{XII147.21}
$$

本章复用此分类。没有推出 $P_{\rm s}$ 闭或 $P$ 紧。SAME_READBACK 定理126.7已证明：若存在重复球，它必与单标签纯点在原边界中的闭包相交；故不能未经证明把 $P_{\rm s}$ 当作闭域。

相对于 $P_{\rm s}$ 的四维紧块、$P_{\rm s}$-开四维图、$P$-开四维图和原根芽均不同。本章只取得第一项及命题147.7的指定紧层连续。XI 引理145.5的 $P$-开层使用覆盖**全部原纯点**的四维法向接口和原 $P$ 的 Baire 性；本章不能将其直接移给 $P_{\rm s}$，也不能移回整个 $P$。更不能在 XI 第145.5—145.6节的后续推导中借入未付的全纯域邻域、局部纯闭性或原根芽

$$
\mathsf G(o):\quad\exists W\subset V\text{ 开},\quad o\in W,\quad
W\cap P\subseteq\bigcup_{q\in S_o}S_q.
$$

同样，EXCLUSION X 定理127.4、推论127.5的重复球二分仍须保留：若球缘某点存在在本侧整个球上非恒定的原确认，就有实际整球塌缩；否则该点的全部确认在本侧球上恒一，法向平坦且该点非暴露。这里既没有一个满足裸 EB3 加九维的反模型，也没有消灭该二分。仅凭式(XII147.19)不能支付 Conn、全 Pair、PR、least、统一满宽、正限制逆、共同中心、种子三角或自动 PSD。

**二元与三元的界线。** $P_{\rm s}$、式(XII147.10)和式(XII147.12)均由原二元零一关系、原效应和有限见证定义。四维块的见证是两条真实边 $p\perp q\perp r$，不是三角；未取得 $p\perp r$ 或三张效应之和为 $u$。若将来式(XII147.20)闭合，式(XII147.21)及既有 FINITE_PURE VII 定理104.2—104.3、EXCLUSION IX 定理116.9才给每条原零边的唯一第三纯点和实际有限三元框架提升。在这之前，完整三元素提升没有由本章取得。

### 147.10 同一表示的条件 QM 字典与独立物理入口

仅在式(XII147.21)的完整条件另外成立以后，采用其同一个 $\Phi$，直接复用 EXCLUSION XI 的**条件应用145.9**，其所在节是 XI 第145.8节；XI **命题145.8**是证明迁移，不是静态字典。此时 $\Phi$ 送回全部原对象：$K$ 为全部迹一 PSD 像，$P\cong\mathbb{CP}^2$ 为全部复纯射线，全部原效应恰为

$$
f_M(\Phi X)=\operatorname{Tr}(MX),\qquad 0\preceq M\preceq I_3.
$$

若 $v^*v=1$、$P_v=vv^*$、$Q_v=I_3-P_v$，则整个确认菜单是

$$
F_{\Phi P_v}=\{f_{P_v+B}:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\}.
$$

它非单点；$B=0$ 给全锥序 least，并对每个原混输入 $\rho\succeq0$、$\operatorname{Tr}\rho=1$ 达到

$$
T_{\Phi P_v}(\Phi\rho)=\operatorname{Tr}(P_v\rho)=v^*\rho v.
$$

完整 $D_{\Phi P_v}$ 是 $v^\perp\cong\mathbb C^2$ 上的全部密度矩阵，即整颗 Bloch 三球，含全部混态，纯球缘为 $\mathbb{CP}^1\cong S^2$。

这些等式的菜单核对也完全在同一原域中进行：$0\preceq M\preceq I_3$ 且 $v^*Mv=1$ 给 $(I_3-M)v=0$，Hermitian 性消去交叉块，故全部且仅有 $M=P_v+B$ 如上。对每个 $X\succeq0$，$\operatorname{Tr}(BX)\ge0$，所以 $B=0$ 同时给 least 和每个混输入上的已达 minimum。正矩阵满足 $v^*\rho v=0\Longleftrightarrow\rho v=0$，故零集是整个二阶密度球。这些是 XI 条件应用145.9的同一表示计算，不是式(XII147.19)单独导出的全局 Born 规则。

实际未知入口、共同来源及其完整装饰／读回合同不由静态几何供应。全部原质量、共同来源域及全部合法实现、每个有限复合体与全部纠缠联合域、各自全效应和严格张量单位，所有旁观系统上的 CP 测试，实际事件／仪器及逐输入和同族预算、记录／权限／全部合法未来及每个中间切口，仍按 SAME_READBACK **第127.10节（SECTION127.10）**及其完整引用链各自承担；它不是该卷关于共同圆球的同号定理。完整继承亦见 XI 第145.9节的物理合同。物理钟、连续时间来源、Hamiltonian、能量标定和数值 $\hbar$ 仍保留各自独立合同。本章没有将任何这些入口付给局部法向唯一性。

### 147.11 归属边界与原供应文献

EXCLUSION IX 引理119.1、定理119.10的局部线性代数，BILATERAL VIII 引理121.2—121.4、定理121.5—121.6的九点／四面体／两步块及尺寸矛盾，SAME_READBACK 引理128.2的紧投影覆盖，EXCLUSION IX 引理120.7、定理120.8、引理120.11、定理120.12和 THREE_COPY VII 第122.2—122.4节的完整法向消费者，均按原来源复用。THREE_COPY VII 定理121.9供应 EB3 加全局 Inj 的九维下界，其残余切扇证明不在本章重证。

本章的承重迁移由引理147.2—147.5及第147.6、147.12节给出：以单标签端面和原接触排除极限重复球，使有限闭层与四维紧块不再依赖全局 Inj；继而在裸 EB3 下取得整个原空间的九维下界，并在九维等号处取得每个单标签点的完整确认唯一性。命题147.6—147.7将既有法向计算及有限转移接到这一已付局部域。有限维凸极点生成、二次多项式唯一性、Baire、连续正半定平方根、Carathéodory 及区域不变性是成熟中间工具。分类和条件静态字典分别复用 XI 定理145.2、条件应用145.9，不作为本章另证的一般分类。

**原供应文献。** 以下均为仓库 docs/develop/theory 中的原正文；所列条目与节保留其原前件。

* [QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md](QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md)，定理103.2、104.2—104.3：整个原真面、共同零确认及在相应 Pair 前件后的三元框架。
* [QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md)，定义116.1、定理116.2、116.6、116.9、引理119.1、定理119.10、引理120.7、定理120.8、引理120.11、定理120.12：标签孤立二分、单标签邻点闭包、局部有限方向及原法向接口。
* [QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VIII.md](QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VIII.md)，第121.1节、引理121.2—121.4、定理121.5—121.6：原全局 Inj 版本的有限见证、整球连续、四维块及法向层矛盾。
* [QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md](QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)，第126.5节、定理126.7、引理128.2及证明、第127.10节：单标签域、单标签积聚、全点紧投影覆盖及独立物理合同。
* [QUANTUM_ORIGIN_LOCAL_PURE_LIMIT_AND_COMMON_POSITIVE_LIFTS_CONTINUATION.md](QUANTUM_ORIGIN_LOCAL_PURE_LIMIT_AND_COMMON_POSITIVE_LIFTS_CONTINUATION.md)，引理132.3；[QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md](QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md)，引理131.2：既有单标签混极限反向塌缩。
* [QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md](QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md)，定理121.9、第122.2—122.4节，特别是定理122.5：全局 Inj 分支的九维下界及完整四维法锥边界射线消费者。
* [QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md)，定理127.4、推论127.5：仍保留的重复球两分支。
* [QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md)，定理145.2、引理145.4—145.5、第145.5—145.6节、命题145.8、条件应用145.9及第145.9节：全原域根芽、同锥同单位分类、证明迁移、静态字典及独立物理合同；本章未将其全纯域前件局部化为既成结论。

### 147.12 同一纯性桥的原载体维数下界与完整中文图景

**推论 147.8（裸完整 EB3 已要求整个原实空间至少九维）。** 只保留第147.1节的有限维原域和 EB3，不输入九维等号，则

$$
\dim_{\mathbb R}V\ge9.
\tag{XII147.22}
$$

证明。令 $m=\dim\operatorname{aff}K=\dim_{\mathbb R}V-1$。完整三球是原真面，所以 $m\ge4$。IX 定理116.6给 $p\in P_{\rm s}$。引理147.2、147.4和147.5均未使用九维，故有一个原纯紧四立方体，其每点 $r\in P_{\rm s}$ 都满足 $\dim L_r=a(r)+4\ge4$。式(XII147.13)的正法向与外法向同构也与维数无关。因此该块位于原 $m$ 维凸体的 $\Sigma_4(K)$。SAME_READBACK 引理128.2在 $k=4$ 给可数紧覆盖，各层有到 $m-4$ 维空间的单射投影。若 $m\le7$，同第147.6节的紧四立方体拉回及 Baire 论证给非空四维开集连续单射到至多三维的空间；线性嵌入四维后，区域不变性矛盾。故 $m\ge8$，即 $\dim_{\mathbb R}V\ge9$。证毕。

这项下界仍量化整个原空间，且不需要将 $K$ 换成 $\operatorname{conv}P_{\rm s}$。它通过本章纯性桥将已有全局 Inj 分支的九维下界迁移到裸 EB3 原域；不是自动九维上界，更不消去式(XII147.20)。若原维数另有 $\dim_{\mathbb R}V\le9$，本推论先给等号，再由定理147.1取得所有单标签处的完整四维原法向。

**完整中文图景。** 把整个原状态体想成同一块凸实体，每把测试尺都必须在整块实体上读零到一。仅要求每个纯点的完整排除域是一颗三球，就已经迫使整个原实空间至少九维，因而原归一状态体至少八维；这个下界不要求全局球标签唯一，也没有另选较小状态体。其出发点是至少存在一个单标签纯点，且它的完整排除球球缘上的所有纯点也都是单标签。

为了看这些球怎样移动，先在一个实际球面的小圆盘上取标签，再给每颗移动球钉九个足以确定二次边界的点；每个钉子背后的下一颗球还保留一个有体积的四面体。取极限时钉子起初可以落成混态。关键是，同一极限尺一面确认这个钉子，一面在四面体上读零：若它的零球变成重复球，确认面只能落在配对球里，而配对球又碰到了原来的单标签球，立即违反重复球不得碰第三球的规则。于是钉子仍是原纯点，九个钉子才真正固定整颗极限球。小圆盘的两个方向和下一层球帽的两个方向随后拼成原纯点中的四维紧块。

这个紧块上每点至少需要四维原法向。在原状态体维数至多七时，这些点能分成可单射投到至多三维的可数紧层；Baire 先把四维块的一块真正开片放进同一层，区域不变性再禁止它被单射压进三维。因此原状态体至少八维，原实空间至少九维。若整个原空间恰为九维，再假设某个单标签起点有两把不同的整球确认尺，冗余就会沿两条原边传满四维块，使每点至少需要五维法向；此时八维原状态体的相应法向层仍只能单射投到三维，同一个矛盾排除冗余。因此九维等号处，每个实际单标签点只剩一把整球确认尺，且有完整四维原法向、完整原边效应区间和全部归一法向基。

最后一道边界仍然清楚：四维紧块尚不是所有原纯点中的开邻域，法向张成空间的层上连续也不等于整个法锥连续；别的重复球块仍未被排除。裸 EB3 加九维尚未推出全局 Inj，局部唯一整球确认也尚未给整个确认菜单的 least、每个混输入的 Born 最低值或正限制逆。只有另付清全局 Inj，才由既有分类和同一表示的完整字典得到整座复三能级状态体。实际来源、纠缠联合、事件仪器、全部合法未来、物理钟和能量标定仍各有独立入口，不能由这里的静态局部结论代付。

## 追加锚（本行以下为增补区）

## 148. 纯局部极小的全域障碍与同根同阈值闭端点

### 148.1 原域、完整面与端点命题

**定义 148.1（同一原根的读数与二步载体）。** 本章的148.*均属本卷 XII；
[XI145—146][Q148XI]仍指前卷的九维分类与有限层正规性结论。
保留定义145.1的非零有限维实空间 $V$、闭尖生成凸锥 $C$、
在 $C\setminus\{0\}$ 上严格正的原单位 $u$，以及全部原对象

$$
\begin{gathered}
K=C\cap\{u=1\},\quad P=\operatorname{ext}K,\quad
\mathcal E=[0,u]_{C^\ast},\quad
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\\
T_p(x)=\min_{f\in\mathcal F_p}f(x),\quad
D_p=\{x\in K:T_p(x)=0\},\quad S_p=P\cap D_p.
\end{gathered}
\tag{XII148.1}
$$

所有标签遍历整个原 $P$，第二变量遍历整个原 $K$，包括全部混态。
以下假设完整 EB3 与完整纯 PR；前者规定每个完整 $D_p$ 仿射等价于闭三球，
后者规定 $T_p(q)=T_q(p)$ 对全部原纯对成立。
事先固定同一个 $o\in P$，记

$$
h=T_o,\qquad A=D_o,\qquad S=S_o,\qquad
B=\bigcup_{s\in S}D_s,\qquad Q(o)=P\cap B.
\tag{XII148.2}
$$

复用 [IX114.1][Q148IX]的完整菜单紧性与达到性：严格正性使 $K$ 紧，生成性使
$K$ 张成 $V$ 且 $\operatorname{aff}K=\{u=1\}$；在从 $K$ 选出的线性基上评价，
闭效应区间 $\mathcal E$ 有界而紧。$\mathcal F_p$ 闭且含 $u$，所以每个 minimum 达到。
这也把 $K$ 上全部有界仿射效应与同一个原区间 $\mathcal E$ 对应起来，未缩小菜单。

复用 [VII103.2][Q148Faces]、[IX114.2及116.1][Q148IX]的完整原面结果：
每个 $D_p$ 是紧暴露真面，全部非空真面只有原纯单点或完整 $D_p$。
对任何这样的面 $F$，$\operatorname{ext}F=P\cap F$；完整三球的这个集合是其整个相对边界，
同胚于 $S^2$。特别地，每个非空真暴露面的纯缘连通。
这些是原面分类的前两项，不使用另需全 Pair 的最后一项。
三维 $D_p$ 是真面，故 $\dim\operatorname{aff}K\ge4$。

纯集的紧性准确取自 IX114.4。该结论由纯 PR、IX114.3 的原端点暴露和原菜单紧性推出，
不以 $P$ 已闭为前提，不调用 qutrit 表示。
这三项供应——紧 $P$、每个真暴露面的连通纯缘、维数至少二——是下面局部极小论证的全部凸几何输入。

### 148.2 有实际消费者的局部极小桥梁

**引理 148.2（紧极点集上的仿射局部极小）。** 设 $K_0$ 是非空有限维紧凸集，
$P_0=\operatorname{ext}K_0$ 紧，且每个非空真暴露面 $F$ 的
$\operatorname{ext}F=P_0\cap F$ 连通。若 $\dim\operatorname{aff}K_0\ge2$，
则任意仿射函数 $a:\operatorname{aff}K_0\to\mathbb R$ 在 $P_0$ 上的每个局部极小点，
都是它在整个 $K_0$ 上的全局极小点。常量函数以及零维 $K_0$ 也有此结论。
局部极小均取 $P_0$ 的相对拓扑。

证明。在 $\operatorname{aff}K_0$ 中工作，记其方向空间维数为 $d$。
常量情形直接成立。设 $a$ 非恒定，$p\in P_0$ 是局部极小点但不是全局极小点，
置 $\alpha=a(p)$。存在 $P_0$ 中相对开邻域 $U\ni p$，使 $a\ge\alpha$ 于 $U$。
若在 $K_0$ 有比 $\alpha$ 小的值，紧的全局最小面有极点；
面的极点也是 $K_0$ 的极点，故可取 $q\in P_0$ 满足 $a(q)<\alpha$。

令 $Q=P_0\setminus U$。它非空紧，且 $p\notin Q$。
由成熟的有限维 Carathéodory 定理，$\operatorname{conv}Q$ 是
$Q^{d+1}$ 与紧概率单纯形之积的连续像，所以紧。
极端性使 $p\notin\operatorname{conv}Q$：若 $p$ 是 $Q$ 中点的有限凸组合，
每个正权重点都须等于 $p$，与 $p\notin Q$ 矛盾。
有限维严格分离给仿射函数 $b$，满足

$$
b(p)>\max_Q b.
\tag{XII148.3}
$$

在模去常量的仿射函数空间中，保持此严格间隙的 $b$ 构成非空开集。
由于 $d\ge2$ 且 $a$ 的线性部分非零，可使 $b$ 的线性部分不属于 $a$ 的线性部分所张成的直线：
若原分离尺平行，就沿一个独立方向作足够小的扰动；紧 $Q\cup\{p\}$ 使严格间隙保留。
这里没有要求 $p$ 本身暴露。

对 $t\ge0$ 置

$$
g_t=b-ta,\qquad F_t=\operatorname{argmax}_{K_0}g_t,\qquad
M_t=P_0\cap F_t=\operatorname{argmax}_{P_0}g_t.
\tag{XII148.4}
$$

非平行性使每个 $g_t$ 在 $\operatorname{aff}K_0$ 非恒定，故 $F_t$ 总是非空紧真暴露面。
成熟的极点—面传递给 $\operatorname{ext}F_t=P_0\cap F_t$，紧面的极点存在性又给
$M_t\ne\varnothing$ 以及 (XII148.4) 最后的等号。
假设使 $M_t$ 连通；紧 $P_0$ 与闭 $F_t$ 使 $M_t$ 紧。

若 $x\in Q$ 且 $a(x)\ge\alpha$，对每个 $t\ge0$ 都有

$$
g_t(x)\le b(x)-t\alpha<b(p)-t\alpha=g_t(p).
\tag{XII148.5}
$$

因此全部 $M_t$ 均包含于两个互不相交的相对开集
$U$ 与 $W=\{x\in P_0:a(x)<\alpha\}$ 的并。
这给出不能越过 $U$ 边界的具体障碍，而非假定某条极大点轨道连续。
由 (XII148.3)，$M_0\subseteq U$。
再选 $T>0$，使

$$
T(\alpha-a(q))>\max_{P_0}b-b(q).
\tag{XII148.6}
$$

若 $a(x)\ge\alpha$，则
$g_T(x)\le\max_{P_0}b-T\alpha<b(q)-Ta(q)=g_T(q)$，
所以 $M_T\subseteq W$。

考虑整个极大点图

$$
G=\{(t,x)\in[0,T]\times P_0:x\in M_t\}.
\tag{XII148.7}
$$

它由对所有 $y\in P_0$ 的闭不等式 $g_t(x)\ge g_t(y)$ 定义，故在紧积中闭而紧。
到 $[0,T]$ 的投影满射，各纤维为连通非空的 $M_t$。
下面直接使用成熟的紧映射连通纤维论证。
若 $G=C_1\sqcup C_2$ 是非空分离，则两部分在紧 $G$ 中闭，因而紧；
它们在 $[0,T]$ 上的像是两个非空闭集且覆盖区间。
区间连通使两像相交，于是某个纤维同时遇到 $C_1,C_2$。
该纤维被二者分离，违反纤维连通性。所以 $G$ 连通。

但 $G\cap([0,T]\times U)$ 与 $G\cap([0,T]\times W)$ 是两个互不相交的相对开集，
覆盖 $G$；$M_0$ 和 $M_T$ 又使它们均非空，矛盾。
所以 $p$ 在 $P_0$ 上全局极小；前述紧最小面的极点传递再将结论送到整个 $K_0$。
证明未假设 $P_0$ 连通、路径连通、极大点对应下半连续或存在连续选择。证毕。

**命题 148.3（一维非恒定情形不能补入引理）。** 取
$K_0=[0,1]$、$P_0=\{0,1\}$、$a(x)=x$。
所有非空真暴露面的纯缘都连通，且 $P_0$ 紧，但 $p=1$ 是非全局局部极小点。

证明。真暴露面只有两个端点，纯缘为单点。$1$ 在 $P_0$ 中孤立，所以是局部极小点；
$a(0)<a(1)$ 排除全局极小性。
任何在 $1$ 严格大于 $0$ 的仿射分离尺都形如 $b(x)=\beta x+\gamma$，$\beta>0$。
当 $t=\beta$ 时，$b-ta$ 恒定，极大面变成整个 $K_0$，其极点集不连通。
这正是引理中非平行扰动所排除的退化。零维或常量情形没有这个障碍；
原 EB3 应用已有 $\dim\operatorname{aff}K\ge4$，不落入本反例。证毕。

### 148.3 原 minimum 的局部极小转移与真正低端点

**定理 148.4（原比较的内部无纯局部极小与端点逼近）。** 在定义148.1的完整 EB3、纯 PR 域，
对每个事先固定的原 $o$，$h=T_o$ 在 $P$ 上没有读数处于 $(0,1)$ 的局部极小点。
对任意 $0<\varepsilon<1$，每个满足 $h(p)=\varepsilon$ 的原纯点都有实际原纯点列

$$
p_n\longrightarrow p,\qquad 0<h(p_n)<\varepsilon,\qquad
h(p_n)\longrightarrow\varepsilon.
\tag{XII148.8}
$$

因此，在原纯集的相对拓扑中，

$$
\begin{gathered}
\{p\in P:0<h(p)\le\varepsilon\}
\subseteq\overline{\{p\in P:0<h(p)<\varepsilon\}}^{\,P},\\
\overline{\{p\in P:h(p)<\varepsilon\}}^{\,P}
=\{p\in P:h(p)\le\varepsilon\}.
\end{gathered}
\tag{XII148.9}
$$

证明。定义148.1逐项供应引理148.2的紧纯集、全部真暴露面连通纯缘及维数前件。
选辅助范数，紧 $\mathcal E$ 给 $L=\max_{f\in\mathcal E}\|f\|_\ast<\infty$。
每张原效应满足 $|f(x)-f(y)|\le L\|x-y\|$；分别取整个 $\mathcal F_o$ 的 minimum 得

$$
|h(x)-h(y)|\le L\|x-y\|\qquad(x,y\in K).
\tag{XII148.10}
$$

这是固定根、第二变量的连续性，不涉及移动确认族的选择。

反设 $p\in P$ 是 $h|_P$ 的局部极小点，$\mu=h(p)\in(0,1)$。
原 minimum 达到，故取同一完整菜单中的 $f\in\mathcal F_o$，使 $f(p)=\mu$。
在同一纯邻域内，

$$
f(x)\ge h(x)\ge\mu=f(p).
\tag{XII148.11}
$$

因此这张真实原仿射效应 $f$ 在 $P$ 上也于 $p$ 局部极小。
$f(o)=1>\mu$ 使其非恒定；引理148.2给 $f\ge\mu$ 于整个 $K$。
现在才定义真实原线性泛函

$$
f'=\frac{f-\mu u}{1-\mu}.
\tag{XII148.12}
$$

分母正。在整个 $K$ 上，$0\le f'\le1$，且 $f'(o)=1$、$f'(p)=0$。
对任意非零原 $c\in C$，严格正性给 $u(c)>0$，且 $k=c/u(c)\in K$，于是

$$
0\le f'(c)=u(c)f'(k)\le u(c).
\tag{XII148.13}
$$

在 $c=0$ 也成立，所以 $f'\in[0,u]_{C^\ast}=\mathcal E$，进而 $f'\in\mathcal F_o$。
这与 $0<\mu=h(p)\le f'(p)=0$ 矛盾。
归一化在全部原锥上合法，未使用面效应延拓、least 或新的确认菜单。

若 $h(p)=\varepsilon\in(0,1)$，不存在局部极小意味着每个纯邻域都含 $h<\varepsilon$ 的点。
将该邻域同时限制在 $\{h>\varepsilon/2\}$ 及半径 $1/n$ 的环境球内，选原纯 $p_n$，
就得到 (XII148.8)；连续性给读数收敛。
严格带内的点本身已在其闭包中，故有 (XII148.9) 第一项。
第二项的 $h=0$ 点本就在 $\{h<\varepsilon\}$ 中，$h=\varepsilon$ 点由刚构造的列逼近；
反包含由连续性和 $\{h\le\varepsilon\}$ 的相对闭性成立。
这并不由逼近本身供应零层 $S$ 在任意指定载体中的成员资格。证毕。

### 148.4 消费原真实标签返回的闭高端点

**定理 148.5（同根、同阈值的两个闭带）。** 在定义148.1的完整原域中，另假设
对这个事先固定的同一个 $o$ 成立的原条件 $L_\varepsilon(o)$，$0<\varepsilon<1$：

$$
\forall z\in P:\quad 0<h(z)<\varepsilon
\ \Longrightarrow\ \exists s\in P:\ T_o(s)=T_z(s)=0.
\tag{XII148.14}
$$

则对定义148.1的同一个 $B$ 有

$$
\{p\in P:h(p)\le\varepsilon\}
\ \cup\ \{p\in P:h(p)\ge1-\varepsilon\}\ \subseteq B.
\tag{XII148.15}
$$

证明。先消费推论145.4的准确接口：相同的完整 EB3、纯 PR 与 $L_\varepsilon(o)$
给根合同 $R_o$，包括 $S\subseteq B$、$o\in B$、$B$ 紧，以及根和根邻球的单标签性。
它还给出：对任何 $q\in P\setminus(A\cup\{o\})$，若整个真实 $S_q\subseteq B$，
则全部实际邻边完成 $C_q$ 与所需反向纯比较成立，定理145.3使 $q\in B$。
这里未向未覆盖目标预定义 $\pi_o(q)$。

紧性的原对象可明确写为

$$
\Gamma=\{(s,x,f)\in S\times K\times\mathcal E:
f(s)=1,\ f(x)=0\},\qquad B=\operatorname{pr}_K\Gamma.
\tag{XII148.16}
$$

完整原 $S\cong S^2$、$K$、$\mathcal E$ 均紧，评价连续，故 $\Gamma$ 紧。
原 minimum 达到使该投影准确等于 $B$，包括每个 $D_s$ 的全部混态；所以 $B$ 在 $K$ 中闭。
这不需要整族球的连续性或移动标签选择。

由 (XII148.14) 和零对称，$0<h<\varepsilon$ 的全部纯点在 $B$。
定理148.4的真实原纯逼近列与 $B$ 闭性补上 $h=\varepsilon$。
零层准确为 $\{p\in P:h(p)=0\}=S$，其成员资格已由推论145.4另付。
于是整个闭低带 $\{h\le\varepsilon\}\cap P$ 均在 $B$。

再取任意原纯 $q$ 满足 $h(q)\ge1-\varepsilon$。
若 $q=o$，已付 $o\in B$；其余因 $1-\varepsilon>0$，有
$q\in P\setminus(A\cup\{o\})$。
对整个实际 $S_q$ 的任意 $x$，原达到性给 $f\in\mathcal F_q$，满足 $f(x)=0$。
原补效应 $u-f$ 属于 $\mathcal F_x$。在同一个原纯根 $o$ 上评价，仅对纯对用 PR，得到

$$
h(q)+h(x)=T_q(o)+T_x(o)
\le f(o)+(u-f)(o)=1.
\tag{XII148.17}
$$

这正是 (XII145.27) 的原互补不等式。故每个实际 $x\in S_q$ 都满足
$0\le h(x)\le1-h(q)\le\varepsilon$，已由闭低带进入 $B$。
至此才得到整个 $S_q\subseteq B$，进而消费上述推论145.4的 $C_q$、反向比较和真实标签返回，
得到 $q\in B$。这里没有要求存在读数恰为 $1-h(q)$ 的伙伴，也没有用假想的伙伴标签合同。
原严格高带已含 $h=1$；同一不等式也处理这一情形，无需另证 $h=1$ 的纯点刻画。
根与阈值从始至终未变。证毕。

**推论 148.6（临界阈值与尚余的开中带）。** 在定理148.5的相同前件下，
若 $\varepsilon=1/2$，则 $P\subseteq B$，从而同一根满足 X133.1 的 $\mathsf D_2(o)$。
若 $0<\varepsilon<1/2$，(XII148.15) 唯一尚未支付的读数范围是

$$
\varepsilon<h(p)<1-\varepsilon.
\tag{XII148.18}
$$

若 $\varepsilon>1/2$，全覆盖已经由 (XII145.25) 的两条严格带及其另付零层取得，
不作为新的覆盖增量。

证明。临界值时两个闭区间覆盖 $[0,1]$，而 $0\le h\le1$，故 $P\subseteq B$。
每个 $q\in P\cap B$ 都有实际同一个 $s\in S$ 满足 $q\in D_s$；
零对称给 $o\perp s\perp q$，包括 $q=o$，所以原 $\mathsf D_2(o)$ 的共同邻点支成立。
若需要静态表示，此时才可直接消费 [X133.6][Q148X]：其原前件为完整 EB3 加一个固定根的
$\mathsf D_2(o)$，结论为同原锥、同原单位的实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\operatorname{PSD}_3)=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XII148.19}
$$

X133.6的链先由该固定覆盖根取得全部原三角，再调用 IX120.4—120.5及116.17—116.18的既有分类。
这里未把表示预用于引理148.2、定理148.4或148.5；(XII148.19) 是该旧结果的条件应用，
其前件仍包含同根 $L_{1/2}(o)$，不是 EB3 加纯 PR 的自动分类。

小于临界值时，两个闭带的补集正是 (XII148.18)。这只说明所述包含关系的剩余范围，
不声称中带必有点或必不在 $B$。
大于临界值时，$h=0$ 由 $S$ 处理；$h>0$ 且不在严格低带意味着
$h\ge\varepsilon>1-\varepsilon$，已在原严格高带，故覆盖早由145.4成立。证毕。

### 148.5 数学来源与剩余条件

**约定 148.7（归属、复用和未付命题）。** 本章的承重连接是引理148.2到
(XII148.11)—(XII148.13) 的全原菜单归一化，再到真实低端点和整个 $S_q$ 的闭带供应。
引理被定理148.4消费，后者被定理148.5的低端点消费；
低端点再支付145.4实际返回接口所需的整个原 $S_q\subseteq B$。
这是 `repo-derived` 的纸面推导归属，不主张外部精确先例已穷尽或全球原创。

有限维 Carathéodory、严格分离、紧凸面的极点存在与极点—面传递、
紧映射的连通纤维论证均为成熟中间工具。
[Feinberg、Kasyanov、Voorneveld，§1、Definition 1.1前的 Berge 最大值定理][Q148B]
给连续目标、连续非空紧值可行对应的连续最优值和上半连续紧值最优对应；
本章可行集固定为 $P_0$，目标取 $ta-b$，其紧图性质也已由闭不等式直接证明。
该文献结论本身不支付连通极大点纤维、连续选择或本章的仿射局部极小结论。
原始 Berge 书第116页的独立文本与本引理的外部精确先例在此不作已核断言。
[Landsman，§1.3、式(1.4)—(1.9)][Q148L]提供完整仿射效应的原比较背景，
其参数对应为 $p_{\rm Landsman}(x,o)=T_o(x)$；补效应给零对称，纯数值 PR 是另列条件。
该来源不把 minimum 当作全域仿射函数，不供应返回标签或本章端点桥梁。

原菜单达到性、PR 下 $P$ 紧、完整原面穷尽与相对 $S^2$ 纯缘、
根合同及真实返回均按上述准确来源复用，不另计为新增结果。
XI145.2 的表示保持完整 EB3 加整个原空间九维及 Conn 或 Inj 的前件；
XI146.2—146.4 的有限层正规性保持 EB3、Conn、ZC，且量词为
$\forall m\,\exists\varepsilon_m,\delta_m>0$。
这些结论不在本章较弱前件下补付局部极小桥梁，也不把逐层常数统一到全域。

剩余的最小临界候选是：仅由完整 EB3 与完整纯 PR，能否取得一个事先固定的原根
$o$ 满足 $L_{1/2}(o)$。本章仍将它作为未付命题；
闭端点并不给 $L_\varepsilon(o)$ 自动性，也不给阈值任何正宽度扩张。
在 $0<\varepsilon<1/2$ 下补付 (XII148.18) 还需额外论证。
全过程不预用 Conn、Inj、整个空间九维、MC、全 Pair、least 或静态分类；
只在推论148.6已付覆盖之后复用旧分类。
结论属于原有限维态—效应几何，不支付实际来源、仪器、有限复合或物理时间的实现条件。

[Q148IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.1—114.2：同原紧基、完整菜单、达到性及原面；114.3—114.4：纯PR下的端点暴露与纯紧性；116.1及式(IX116.2)：完整相对纯球缘；120.4—120.5、116.17—116.18：既有条件分类。"
[Q148Faces]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2：共同零确认、全部非空真面穷尽及其不依赖Pair的证明；全对结论另列Pair前件。"
[Q148X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X133.1：同一固定根的D2；133.6：完整EB3加一个覆盖根的全部三角与同原静态分类。"
[Q148XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "XI145.2：EB3+Conn或Inj+整个原V九维；XI146.2—146.4：EB3+Conn+ZC的有限层推进；146.6：零边不变与全域统一界的剩余条件。"
[Q148B]: https://arxiv.org/html/1309.7708v1 "E. A. Feinberg, P. O. Kasyanov, M. Voorneveld, Berge's Maximum Theorem for Noncompact Image Sets，§1中Definition 1.1前的经典紧值最大值定理。"
[Q148L]: https://arxiv.org/html/quant-ph/9603005v2 "N. P. Landsman, Poisson spaces with a transition probability，§1.3、式(1.4)—(1.9)：全仿射效应比较、零对称及另列的纯数值互惠。"

## 追加锚

## 151. 原纯域的自动拓扑连通与近一比较的共同零邻点

**定义 151.1（完整原域与局部二元候选）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C$ 和在 $C\setminus\{0\}$ 上严格正的原单位 $u$。整个原归一基、全部原纯点和全部原效应始终是

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^\ast},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\}.
\end{gathered}
\tag{XII151.1}
$$

$K$ 紧并张成 $V$；完整 $\mathcal E$ 及每个非空 $\mathcal F_p$ 紧，故最低值在每个原混输入 $x\in K$ 达到。记 $S_p=P\cap D_p$，以及 $p\perp q\Longleftrightarrow T_p(q)=0$。补效应使零关系对称且反自反。完整 EB3 指每个整个 $D_p$ 都是非退化仿射实心三球；PR 指全部原纯对满足 $T_p(q)=T_q(p)$，不表示先后测量对易。

局部共同零条件定义为

$$
\begin{aligned}
\mathsf N_2:\quad
&\forall p\in P\ \exists\varepsilon_p\in(0,1)\ \forall q\in P:\\
&T_p(q)>1-\varepsilon_p
\quad\Longrightarrow\quad
\exists r\in P:\ T_p(r)=T_q(r)=0.
\end{aligned}
\tag{XII151.2}
$$

阈值逐点选定，同一个实际原纯点 $r$ 同时承担两条原零边；不要求连续选择或统一阈值。完整候选是同一式(XII151.1)原域中的 EB3、PR 与 $\mathsf N_2$，没有输入全域球标签单射、唯一整球零确认、least、谱性、自对偶或矩阵坐标。

**定理 151.2（原纯域与零关联的自动拓扑连通）。** 完整 EB3 加 PR 已使整个 $P$ 和实际纯零关联

$$
\mathcal I=\{(p,q)\in P^2:p\perp q\}
\tag{XII151.3}
$$

均为紧连通空间。这里的连通取原 $V$ 的拓扑，不是有限零路连通。

证明。直接复用 [IX114.3—114.4][Q151IX]：PR 使每个原纯点严格暴露、整个 $P$ 紧，且由原效应的统一范数界，存在有限 $L>0$，使固定 $T_p$ 在全部 $K$ 上为 $L$-Lipschitz。PR 交换两个纯端点，遂给

$$
|T_p(q)-T_{p'}(q')|
\le L\bigl(\|p-p'\|+\|q-q'\|\bigr)
\quad(p,p',q,q'\in P).
\tag{XII151.4}
$$

同一严格暴露确认还给 $T_p(q)=1\Longleftrightarrow p=q$。这些是既有结果的直接消费，没有预设整球确认等于整个菜单的最低确认。

反设 $P=A\sqcup B$ 为非平凡拓扑分离。$A,B$ 均紧，有限维凸包 $H_A=\operatorname{conv}A$、$H_B=\operatorname{conv}B$ 也紧。直接使用 [IX114.2、IX116.1][Q151IX] 的完整原面接口：全部非空真面只有纯单点或整个 $D_s$；每张 $D_s$ 暴露且为极大真面，其全部原纯点恰为连通球面 $S_s\simeq S^2$，且 $D_s=\operatorname{conv}S_s$。因此每个真面的全部纯点都只在 $A$ 或只在 $B$，每个边界点所在的真支撑面也整个包含于 $H_A$ 或 $H_B$。故

$$
\partial_{\rm rel}K\subset H_A\cup H_B.
\tag{XII151.5}
$$

此覆盖在边界上不重叠。若 $x\in\partial_{\rm rel}K\cap H_A\cap H_B$，取过 $x$ 的同一个真支撑面 $F$；分别将 $x$ 写成 $A$、$B$ 中纯点的有限正权混合。支撑泛函的非负余量迫使两种分解的所有纯分量均在 $F$，与 $P\cap F$ 只在一侧矛盾。于是原边界被分成两个不交非空紧集。完整三球是真面，故 $\dim\operatorname{aff}K\ge4$；从原内点径向参数化，边界同胚于连通球面，不容此分离。因此 $P$ 连通。

由(XII151.4)，$\mathcal I$ 闭于紧 $P^2$。投影 $\pi_1:\mathcal I\to P$ 满射，每根纤维 $\{p\}\times S_p$ 连通。若 $\mathcal I$ 分成两个非空紧集，每根纤维只能在一侧；两侧投影便是分离 $P$ 的两个非空不交紧集，矛盾。故 $\mathcal I$ 也连通。证毕。

此证明中，取得 $P$ 紧以后只消费全部原非点真面的连通纯边界。因此同一论证也适用于完整 EB$_{\ge2}$ 加 $P$ 紧，不需要所有球同维。球形所给的是完整原面及其全部纯边界；任意抽取的球面子族不能代替它们。

**定理 151.3（近一共同零点接到有限原零路）。** 在完整 EB3+PR 域，$\mathsf N_2$ 蕴含原零图有限路径连通 $\mathsf{Conn}$，甚至存在一个不预先指定的有限全域路径上界。

证明。对每个原 $p$ 取(XII151.2)的阈值。集合

$$
U_p=\{q\in P:T_p(q)>1-\varepsilon_p\}
\tag{XII151.6}
$$

是包含 $p$ 的原纯域开邻域，且每个 $q\in U_p$ 都经同一个实际共同零邻点在至多两步内到达 $p$。故每个零图分量是开集：其每个点 $p$ 都有仍在该分量内的 $U_p$。补集是其他开分量之并；定理151.2的 $P$ 连通性迫使全图只有一个分量。

若需先于分类取得有限路径上界，紧 $P$ 给有限覆盖 $U_{p_1},\ldots,U_{p_m}$。覆盖的交叠图连通，否则两组互不相交的开集之并分离 $P$。相交的两邻域中心经交点至多四步相连。任意两纯点各先用至多两步到其覆盖中心，再沿至多 $m-1$ 条交叠边到达另一中心，合计不超过 $4m$ 条实际原零边。这里没有把近似零边换成精确零边。证毕。

式(XII151.6)确实只检查同一纯标签附近的比较。对任意包含 $p$ 的原纯域开集 $O$，紧 $P\setminus O$ 上连续 $T_p$ 的最大值严格小于一，故存在 $\delta>0$，使 $\{q:T_p(q)>1-\delta\}\subset O$。这些近一集合是 $p$ 的邻域基，无需声称 $1-T_p(q)$ 是度量。它也不是只由 $q=p$ 满足的空条件：任取 $s\in S_p$，由零对称有 $p\in S_s$；完整球面 $S_s$ 内存在不同纯点 $q_i\to p$，从而 $T_p(q_i)<1$ 且趋于一。

**推论 151.4（完整局部候选的同原复三能级表示）。** 在定义151.1的完整原域内，下列条件等价：

$$
\begin{gathered}
\mathrm{EB3}+\mathrm{PR}+\mathsf N_2,\qquad
\mathrm{EB3}+\mathrm{PR}+\mathsf{Conn},\\
\exists\Phi:\operatorname{Herm}_3(\mathbb C)\overset{\sim}{\longrightarrow}V
\text{ 实线性双射},\qquad
\Phi(\mathrm{PSD}_3)=C,\quad u\Phi=\operatorname{Tr}.
\end{gathered}
\tag{XII151.7}
$$

证明。定理151.3给第一个到第二个的桥。第二个到第三个准确复用 [XI150.5][Q151XI]：有限原零路首先给全域球标签单射和全部唯一整球零确认；已有非单位预算塌缩与唯一标签处的塌缩饱和相接，再沿零路传播，排除非单位预算。此时才支付整个原确认菜单的 least，消费 IX114.9 的同锥同单位分类。本章不另作一次量子分类，也不从 PR 单独跳到整球确认互易。

反向在同一个完整表示中核对。对原纯点 $p=\Phi(vv^\ast)$，$\|v\|=1$，整个原确认菜单、全部混输入最低值和完整排除球分别为

$$
\begin{gathered}
f_{vv^\ast\oplus B}(\Phi\rho)
=\operatorname{Tr}\bigl((vv^\ast\oplus B)\rho\bigr),\qquad
0\preceq B\preceq I_{v^\perp},\\
T_p(\Phi\rho)=v^\ast\rho v,\qquad
\rho\succeq0,\quad\operatorname{Tr}\rho=1,\\
D_p=\Phi\{\rho\succeq0:\operatorname{Tr}\rho=1,\quad
\operatorname{ran}\rho\subset v^\perp\}.
\end{gathered}
\tag{XII151.8}
$$

这里 $vv^\ast\oplus B$ 指 $\mathbb Cv\oplus v^\perp$ 上的块分解。最低值由原菜单中的 $B=0$ 达到，未缩小菜单或混态域。故 EB3 与 PR 成立。对任意原纯 $p=\Phi(vv^\ast)$、$q=\Phi(ww^\ast)$，取单位 $z\in\operatorname{span}_{\mathbb C}\{v,w\}^{\perp}$，则同一个 $r=\Phi(zz^\ast)$ 满足 $T_p(r)=T_q(r)=0$；每个根可取 $\varepsilon_p=1/2$，得到 $\mathsf N_2$。证毕。

完整静态字典直接复用 XI149.5、XI145.9：整个 $K$ 是全部三能级密度矩阵，整个 $P$ 是 $\mathbb{CP}^2$，每张完整排除三球的纯边界是 $\mathbb{CP}^1\simeq S^2$；所有原效应恰为 $0\preceq E\preceq I_3$，读数是 $\operatorname{Tr}(E\rho)$。全部有限数学效应单位分解恰为全部数学 POVM，谱及 Jordan 字典均在同一个 $\Phi$ 下成立。它们是既有静态结论的应用；实际制备、复合与纠缠来源、事件仪器、全旁观 CP、物理时间、Hamiltonian、能量与数值 $\hbar$ 仍各保留所引章节的独立合同。

**定理 151.5（原零图分量的有限层与整个边界）。** 只保留完整 EB3+PR。令 $d_G$ 为实际零图距离，$\Gamma(p)$ 为有限零路分量，并置

$$
A_n(p)=\{q\in P:d_G(p,q)\le n\},\qquad
B_\Gamma=\bigcup_{s\in\Gamma}D_s.
\tag{XII151.9}
$$

则每个 $A_n(p)$ 紧，$\Gamma(p)=\bigcup_{n\ge0}A_n(p)$ 为 $F_\sigma$；若 $q_i\in\Gamma(p)$、$q_i\to q\notin\Gamma(p)$，必有 $d_G(p,q_i)\to\infty$。此外每个分量的凸包包含原 $K$ 的一个相对内点，且

$$
B_\Gamma=\partial_{\rm rel}K\cap\operatorname{conv}\Gamma.
\tag{XII151.10}
$$

各 $B_\Gamma$ 两两不交并覆盖整个原边界。

证明。长度不超过 $n$ 的路径分别是紧 $P^{k+1}$ 中闭零边条件的投影，$0\le k\le n$；有限并仍紧。若一个不可达极限有图距离有界的子列，该子列落在某个紧 $A_N(p)$ 中，极限仍可达，矛盾。

固定 $p\in\Gamma$，以 $c_p$ 为完整 $D_p$ 的球心。$D_p=\operatorname{conv}S_p\subset\operatorname{conv}\Gamma$，故 $x=(p+c_p)/2$ 在该凸包。若 $x$ 在原边界，过 $x$ 的真支撑面同时含 $p,c_p$；因 $c_p\in\operatorname{ri}D_p$，此面含整个 $D_p$。极大真面性迫它等于 $D_p$，却又含 $p\notin D_p$，矛盾。因此 $x\in\operatorname{ri}K$。

式(XII151.10)的从左到右包含由每个 $D_s=\operatorname{conv}S_s$ 直接给出。反向令边界点 $x$ 为 $\Gamma$ 中纯点的有限正权混合，取过 $x$ 的真支撑面 $F$。所有纯分量均在 $F$。若 $F=D_s$，任一纯分量与 $s$ 有零边，故 $s\in\Gamma$、$x\in B_\Gamma$。若 $F=\{x\}$，则 $x\in\Gamma$；取 $s\in S_x$，零对称给 $x\in D_s$ 且 $s\in\Gamma$。同样，任意两分量若贡献同一边界点，过该点的真支撑面中的纯分量就会经其标签至多两步互达，故它们原是同一分量。全部原边界点所在真面为纯单点或完整球，所以这些集合还覆盖整个边界。证毕。

若 $W_\Gamma=\operatorname{span}_{\mathbb R}\Gamma$，上面的内点给 $W_\Gamma\cap\operatorname{int}C\ne\varnothing$，因而 $W_\Gamma^\perp\cap C^\ast=\{0\}$：非零正泛函不能在原锥内点消失。这没有给 $W_\Gamma=V$，原内点可以位于真线性子空间中。也没有给 $\Gamma$ 或 $B_\Gamma$ 闭；无限个紧可达层的并不能代替紧集。

**命题 151.6（重复球块的图孤立与拓扑积聚）。** 在完整 EB3+PR 域，若实际有不同标签共用同一个完整球，则其 [IX116.2][Q151IX] 配对球 $F,G$ 给紧闭零图分量 $\Gamma=S(F)\sqcup S(G)$，但 $\Gamma$ 在整个 $P$ 中不是开集。

证明。既有重复块定理给 $F\cap G=\varnothing$、$I(F)=S(G)$、$I(G)=S(F)$，两张完整球均不与第三张不同完整球相交，故其纯边界构成封闭于零边的完全二部块，且是一个零图分量。每侧球面紧，故 $\Gamma$ 紧闭。

固定 $q\in S(F)$。PR 已给全部原纯点严格暴露，[X124.7、X124.9][Q151X] 遂给实际完整原球列 $D_{p_i}\to\{q\}$，并在紧 $P$ 中取子列 $p_i\to p\in S(G)$。若 $p_i\in\Gamma$，它的完整排除球只能是固定的 $F$ 或 $G$，直径不小于 $\min\{\operatorname{diam}F,\operatorname{diam}G\}>0$。所以最终 $p_i\notin\Gamma$，块外标签却趋到块内标签，$\Gamma$ 不是开集。此处的塌球供应和纯极限定位均为所引结果的组合，不是重复块存在性的反模型。证毕。

**范围 151.7（局部候选的简化尺度与待证桥）。** 定理151.2新增的是在完整原面关系上取得全纯域及关联空间的拓扑连通；定理151.3把只在比较值接近一时要求的二元共同零关系接成全域有限零路，定理151.5刻画同一原分量如何铺在整个凸边界上。这些采用 `repo-derived` 综合推导归属，不主张全球新颖或最小公理。

$\mathsf N_2$ 只检查近一比较带，Conn 检查所有纯对却允许任意有限步；在 EB3+PR 域内，它们经推论151.4选出同一个模型类。因此本候选使输入关系局部化，没有证明独立假设数严格减少。它也不同于 [X132.3—132.5][Q151X] 的小正比较带条件 $0<T_p(q)<\varepsilon_p$，后者不需要 PR，其证明利用原确认水平切片与无三角条件下的正间隔。

[Landsman，Definition 6][Q151L] 的 two-sphere property 量化同 sector 任意两点的双正交闭包并规定球面比较公式，不由单标签 EB3 自动支付；其按跨部分跃迁全零定义的 sector 也不是本章零图分量。[Emir—Kruml—Paseka—Vetterlein，Definition 4、Proposition 32][Q151E] 在全域 L1 和秩至少三的前件下给零图直径至多二；这些前件没有在本章由 PR 推出。[Labardini-Fragoso—Neumann-Coto—Takane，Lemma 2、4][Q151F] 分别在模面格前件下给固定秩面族紧性、在极点集紧且面列已收敛到面的前件下比较面与极点列；它们不把原 $P$ 紧性升级为完整球族闭性。这些文献仅供应比较和适用边界，不代付本章未证的局部桥。

原目标 $\mathrm{EB3}+\mathrm{PR}\Rightarrow\mathsf N_2/\mathsf{Conn}$ 仍未证明，也未给出完整 EB3+PR 反模型来证明其独立。定理151.2不是这道桥：空间连成一片并不制造有限条精确零边；命题151.6还说明图上孤立的块可以受到块外标签积聚。若要删除最后的接线条件，仍须从同一原全效应关系推出局部有限可达，或排除原分量间的整球并合与塌缩。全局 Inj、全部唯一整球零确认、分量闭性和全空间张成均未在此免费取得。

**完整中文图景。** 把所有原状态想成同一块凸实体，每个纯态背后完全排除的全部对象收成一颗实心三球。比较同一对纯态，交换两端最低结果不变，这已让全部纯标签组成紧集。若把纯标签分成彼此分离的两堆，每颗完整球皮只能整张落在其中一堆；球皮包着实心球，最终两堆会把同一凸实体的整个边界也切成不相接的两块，产生矛盾。所以纯标签本来就连成一片。新候选只补一条近处关系：两种纯态已经足够相像时，总能找到同一个被它们完全排除的纯态。这个共同零点把近处两标签接成两步排除接力，局部线路便沿整片纯域传通，已有定理随后恢复同一实体的全部复三能级静态结构与 Born 读数。尚未证明的是，这条近处接线能否也由比较对称和完整三球自动产生；实际仪器、纠缠复合和物理时间仍保留各自合同。

[Q151IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.2—114.4：完整真面、PR下严格暴露与全纯域紧性；IX116.1—116.2：原完整面与重复球孤立块。"
[Q151X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X124.7、124.9：全局单点零射线的实际整球塌缩及原纯极限定位；X132.3—132.5：小正带共同零点与既有静态分类。"
[Q151XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "XI150.5：完整EB3+PR+Conn的满刻度、全原确认菜单least及同锥同单位qutrit；XI149.5、XI145.9：完整静态字典与独立物理合同。"
[Q151L]: https://arxiv.org/html/quant-ph/9603005v2 "N. P. Landsman, Poisson spaces with a transition probability，§1.3式(1.4)、Definition 6。"
[Q151E]: https://arxiv.org/html/2103.13764v1 "T. Emir, D. Kruml, J. Paseka, T. Vetterlein，Linear orthogonality spaces as a new approach to quantum logic，Definition 4、Proposition 32。"
[Q151F]: https://arxiv.org/html/0903.0643v1 "D. Labardini-Fragoso, R. Neumann-Coto, M. G. Takane，Cones and convex bodies with modular face lattices，Lemma 2、4。"

## 追加锚（本行以下为增补区）

## 149. 单标签球心互易的紧纯闭包与原域全饱和

本章的149.*均属本卷 XII；XI149 仍指前卷的单根球心互易机制。

### 149.1 完整原域、二元条件与饱和命题

**定义 149.1（原对象及单标签互易）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C$，及在 $C\setminus\{0\}$ 上严格正的 $u\in V^*$。始终保留整个

$$
\begin{gathered}
K=C\cap\{u=1\},\quad P=\operatorname{ext}K,\quad \mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\quad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\quad D_p=\{x\in K:T_p(x)=0\},\\
S_p=P\cap D_p,\quad
\mathcal A_p=\{e\in\mathcal E:e(p)=1,\ e|_{D_p}=0\},\\
P_{\rm s}=\{p\in P:\{r\in P:D_r=D_p\}=\{p\}\},\\
N_p=\{h\in C^*:h(p)=0\},\quad L_p=\operatorname{span}N_p.
\end{gathered}
\tag{149.1}
$$

原确认菜单紧，minimum 对每个原混输入取得；特别地，$D_p$ 是全部确认零集的**并**。完整 EB3 要求每个 $D_p$ 仿射同构于非退化闭三球，其中心记为 $c_p$。原边 $p\perp q$ 指 $q\in S_p$；补效应使它对称。

对实际完整球 $F$，记 $S(F)=P\cap F$、$I(F)=\{p\in P:D_p=F\}$。Inj 指全部原标签满足 $D_p=D_q\Rightarrow p=q$；Conn 指任意两个原纯点间有有限实际零边路。零图分支也按这种有限路径定义，不按环境拓扑定义。VII103.2供应原真面穷尽及完整暴露球；特别地，$S(F)=\partial_{\rm rel}F$，不同完整球至多交于一个原纯点。

以下讨论完整 EB3 且输入整个原空间的 $\dim_{\mathbb R}V\le9$。由 [XII 推论147.8及定理147.1][S149XII]，维数恰为九，且每个实际 $p\in P_{\rm s}$ 有 $\mathcal A_p=\{e_p\}$。因此下式有定义：

$$
\mathsf{CR}_{\rm s}:\qquad
\forall p,q\in P_{\rm s},\quad p\perp q\Longrightarrow e_p(c_q)=e_q(c_p).
\tag{149.2}
$$

这是原域内新增的模型约束，不是定义恒等式。它只约束实际单标签点之间的实际零边。

**定理 149.2（共同原三元恒等式的全域饱和）。** 在完整 EB3 及 $\dim_{\mathbb R}V\le9$ 下，设 $\varnothing\ne Q\subseteq P_{\rm s}$ 满足

$$
p\in Q\Longrightarrow S_p\subseteq Q.
\tag{149.3}
$$

若存在同一个实数 $\kappa<2$，使整个原 $V$ 上有

$$
e_q+e_{q^\sharp}=\kappa(u-e_p)
\quad(p\in Q,\ q\in S_p,\ q^\sharp=2c_p-q),
\tag{149.4}
$$

则 $Q=P_{\rm s}=P$、$\dim_{\mathbb R}V=9$，并存在实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\mathrm{PSD}_3)=C,\qquad u\Phi=\operatorname{Tr}.
\tag{149.5}
$$

此时 $\kappa=1$。本定理不另输入 $\mathcal A_p$ 唯一性：它由原维数上界和 XII147 对这些实际单标签点支付。证明见149.3—149.8。

**定理 149.3（单标签球心互易候选）。** 在(149.1)的完整原量词下，以下两项等价：

$$
\mathrm{EB3}+\dim_{\mathbb R}V\le9+\mathsf{CR}_{\rm s}
\quad\Longleftrightarrow\quad (149.5).
\tag{149.6}
$$

左侧因而推出全局 Inj、原零图 Conn，以及每个固定原根的两步覆盖。证明在149.2支付二元条件到(149.4)，在149.9完成。

### 149.2 单根机制在实际单标签分支上的完整转移

**引理 149.4（球心互易到共同原恒等式）。** 假设定理149.3左侧成立。取 $P_{\rm s}$ 中任意一个实际零图连通分支 $Q$，则它非空、满足(149.3)，且有一个 $1\le\kappa<2$ 满足(149.4)。

证明。[IX 定理116.6][S149IX]给 $P_{\rm s}\ne\varnothing$，并给其沿实际零边封闭；因此每个这样的分支都满足(149.3)。固定 $p\in Q$。XII147 对 $p$ 及其全部有限步邻点供应

$$
\begin{gathered}
\mathcal A_p=\{e_p\},\quad g_p=u-e_p\in\operatorname{ri}N_p,\quad
K\cap\{e_p=0\}=D_p,\quad K\cap\{e_p=1\}=\{p\},\\
\dim L_p=4,\qquad L_p\longrightarrow\operatorname{Aff}(D_p)
\text{ 为限制线性同构}.
\end{gathered}
\tag{149.7}
$$

写 $D_p=c_p+B\overline B^3$，对 $v\in S^2$ 记 $q_v=c_p+Bv$，并唯一取 $H_i\in L_p$ 使 $H(c_p+Bw)=w$。置

$$
\rho(v)=\sup_{x\in K\setminus\{p\}}\frac{-v\cdot H(x)}{g_p(x)},\quad
Z=\{H(x)/g_p(x):x\in K\setminus\{p\}\},\quad
a_v=2c_{q_v}-p,\quad m(v)=g_p(a_v).
\tag{149.8}
$$

其中 $\rho$ 定义在全部 $\mathbb R^3$，$a_v,m(v)$ 及以下带单位方向的式子取 $v,w\in S^2$。

这里 $q_v\in Q$、$a_v\in S_{q_v}\subset Q$ 都是实际原纯点。XII 命题147.6给有限 Lipschitz 支撑函数 $\rho\ge\|\cdot\|$、有界凸影像 $Z$，及整个原 $V$ 上的

$$
e_{q_v}=\frac{\rho(v)g_p+v\cdot H}{1+\rho(v)}.
\tag{149.9}
$$

以下展开 [XI149.2—149.3][S149XI149] 的单根推导在此处的前件。任意 $h\in N_p$ 在实际球 $D_{q_v}$ 上非负且零于球缘点 $p$，故其球限制是同一支持仿射函数的非负倍数；由 $L_p=\operatorname{span}N_p$，有 $H=z_vg_p$ 于整个 $D_{q_v}$，其中 $z_v=H(a_v)/m(v)$。$g_p$ 唯一零于 $p$，所以 $0<m(v)\le1$，且在这个球上唯一最大于 $a_v$。式(149.9)给 $(-v)\cdot z_v=\rho(v)$。若某个实际比值达到该支撑值，其原态必零于 $e_{q_v}$，故属于整个 $D_{q_v}$；实际接触值只有 $z_v$。这正是 [THREE_COPY VII 定理122.4][S149TC] 的证明所用接口：只需要(149.7)、(149.9)及这个邻球的完整零面，不需要分支外的 Inj。

球心互易现在给

$$
1-\frac{m(v)}2=e_p(c_{q_v})=e_{q_v}(c_p)
=\frac{\rho(v)}{1+\rho(v)},\qquad
m(v)=\frac2{1+\rho(v)}\ge\sigma_p:=\frac2{1+\max_{S^2}\rho}>0.
\tag{149.10}
$$

紧集 $A=\{H(x)/g_p(x):x\in K,\ g_p(x)\ge\sigma_p\}$ 也是凸集：混合两个比值时，用权重正比于 $t/g_p(x_1)$、$(1-t)/g_p(x_2)$ 的实际原混态，其新 $g_p$ 值是相应调和平均，仍至少 $\sigma_p$。每个 $z_v$ 由 $a_v$ 在 $A$ 中实现。于是 $A\subseteq Z\subseteq\overline Z$ 的全部支撑值相同，有限维分离给 $A=Z=\overline Z$。完整支撑面现在才由唯一实际接触判为单点。紧性、唯一性及支撑不等式给支撑点连续，并给

$$
\rho\in C^1(\mathbb R^3\setminus\{0\}),\qquad \nabla\rho(v)=-z_v.
\tag{149.11}
$$

具体地，若 $z(n)$ 是紧凸体在非零方向 $n$ 的唯一支撑点，则
$0\le h(n+k)-h(n)-k\cdot z(n)\le k\cdot(z(n+k)-z(n))=o(\|k\|)$，支付所用微分结论。

再令 $d(v)=e_{a_v}(p)\in[0,1)$、$R_v=u-e_p-e_{q_v}$。在 $q_v$ 的完整球图中，对球缘对径 $p,a_v$ 分别用(149.9)的对应公式，消去同一组三个坐标泛函，得到 [SAME_READBACK 定理123.3][S149SR123] 的全原空间消元式

$$
e_{a_v}=d(v)e_p+\left(d(v)+\frac{1-d(v)}{m(v)}\right)R_v,
\qquad R_v=\frac{g_p-v\cdot H}{1+\rho(v)}.
\tag{149.12}
$$

其两个球图所需限制同构、确认唯一性及一值面，分别由 $p,q_v,a_v\in Q\subset P_{\rm s}$ 的(149.7)供应。没有假设 $R_v$ 正。令
$\mathfrak B(v,w)=\rho(v)-\rho(w)-\nabla\rho(w)\cdot(v-w)\ge0$。将(149.12)代入实际原效应上界 $e_{a_v}(a_w)\le1$，如 [SAME_READBACK 定理124.3][S149SR123] 的同一消元，得到

$$
(1-d(v))(m(w)-m(v))
\le\frac{\mathfrak B(v,w)}{1+\rho(v)}.
\tag{149.13}
$$

确切的代入是 $R_v(a_w)=m(w)(1-\mathfrak B(v,w)/(1+\rho(v)))$；移项所得右端还带系数 $(d(v)m(v)+1-d(v))m(w)\le1$。所以这里只用了同一实现中的原上界。

沿任何经过 $v$ 的双向光滑球面弧，(149.11)给 $\mathfrak B(v,w(t))=o(|t|)$，而(149.10)已给 $m$ 为 $C^1$。式(149.13)在 $t>0$、$t<0$ 分别除以 $t$，且 $1-d(v)>0$，迫所有切向导数为零。于是 $S^2$ 的连通性给 $\rho|_{S^2}=R_p\ge1$，并有

$$
e_p(c_q)=\frac{R_p}{1+R_p}\quad(q\in S_p).
\tag{149.14}
$$

实际零边上的(149.2)使 $R_p=R_q$；沿分支内有限零路，全部 $R_p$ 等于同一个有限 $R\ge1$。取 $\kappa=2R/(1+R)<2$，将(149.9)在 $v,-v$ 相加即得(149.4)，且该等式在整个原 $V$ 上成立。上述转移只调用实际单标签处的完整接口；XI149 的全域 Conn 和其全域 UC 分类均未在此作为前件或结论使用。证毕。

### 149.3 共同差额支付全部球轴及每个标签极限的纯性

以下证明定理149.2，固定其中的实际集合 $Q$ 及共同 $\kappa<2$，并置
$M=\overline Q^{\,K}$。$M$ 仅是原标签的闭包，原态体仍是整个 $K$。

**引理 149.5（同一原效应范数下的三轴非塌缩）。** 有 $1\le\kappa<2$。固定辅助欧氏结构于 $\ker u$，令

$$
L=\max_{f\in\mathcal E}\|f|_{\ker u}\|_*<\infty,
\qquad b=\frac{2-\kappa}{2L}>0.
\tag{149.15}
$$

则每个 $p\in Q$、每个球参数 $D_p=c_p+B_p\overline B^3$ 的最小奇异值至少 $b$。

证明。在(149.4)的 $q$ 处评价，得 $e_{q^\sharp}(q)=\kappa-1\ge0$；在 $q^\sharp$ 处评价，得 $e_q(q^\sharp)=\kappa-1$。故 $e_q(q)-e_q(q^\sharp)=2-\kappa>0$，也给 $L>0$。对任意单位 $t$ 取 $q=c_p+B_pt$，原全效应的统一范数界给
$2-\kappa\le2L\|B_pt\|$。这支付每个方向的半轴界，不仅是直径下界。证毕。

**引理 149.6（共同恒等式排除全部混标签极限）。** $M\subseteq P$，所以 $M$ 是原 $K$ 中的非空紧纯集。

证明。反设 $p_i\in Q$ 趋于混态 $z$。任取 $q_i\in S_{p_i}$，令 $p_i'=2c_{q_i}-p_i\in S_{q_i}\subset Q$。用紧 $K,\mathcal E$ 共同取子列，使
$q_i\to q$、$p_i'\to z'$、$e_{p_i}\to e$、$e_{q_i}\to h$。原评价给

$$
e(z)=1,\quad e(q)=0,\quad h(z)=0,\quad h(q)=1,\quad h(z')=0.
\tag{149.16}
$$

$e$ 非恒定，故 $z$ 是混边界点。[VII 定理103.2][S149VII]给其唯一最小真面 $G$ 为一颗完整原球，且 $z\in\operatorname{ri}G$。原非负性使 $e|_G=1$、$h|_G=0$。$h(q)=1$ 使 $h$ 非零；其零面包含极大真面 $G$，故整个零面恰为 $G$。于是 $z'\in G$，从而 $e(z')=1$。

另一方面，在 $q_i$ 的(149.4)中取对径 $p_i,p_i'$，并在 $p_i'$ 评价，得 $e_{p_i}(p_i')=\kappa-1$。取极限却给 $1=e(z')=\kappa-1$，与 $\kappa<2$ 矛盾。此证明允许 $G$ 是重复球，也没有预先认定 $q,z'$ 纯。证毕。

### 149.4 紧纯闭包中的完整球连续与零封闭

**引理 149.7（所有闭包标签的整球连续）。** 对每个 $p\in M$，有 $S_p\subseteq M$，且 $p\mapsto D_p$ 在整个 $M$ 上按原环境 Hausdorff 距离连续；所有这些球的最小半轴仍至少 $b$。

证明。先令 $p_i\in Q\to p\in M\subset P$。任意子列可再取有界球参数和效应的共同极限

$$
D_{p_i}=c_i+B_i\overline B^3\longrightarrow E=c+B\overline B^3,
\qquad e_{p_i}\longrightarrow e\in\mathcal E.
\tag{149.17}
$$

参数上界来自 $K$ 紧，引理149.5给最小奇异值下界，故 $B$ 秩三。原评价给 $e(p)=1,e|_E=0$，所以按完整 minimum 的原定义有 $E\subseteq D_p$。每个 $c_i+B_it$、$\|t\|=1$ 都在 $Q$，故 $c+Bt\in M\subset P$。因此
$\partial_{\rm rel}E\subseteq P\cap D_p=\partial_{\rm rel}D_p$。

两个球有同一仿射三平面。若 $E\ne D_p$，从 $\operatorname{ri}E$ 中一点走向 $\operatorname{ri}D_p\setminus E$ 中一点，第一次离开 $E$ 的点属于 $\partial E\cap\operatorname{ri}D_p$，与上述纯性矛盾。因此 $E=D_p$。任意子列的再极限相同，给整列收敛、$S_p\subset M$，并将半轴下界传给 $D_p$。

现令任意 $p_i\in M\to p\in M$。任选 $e_i\in\mathcal A_{p_i}$，存在性来自 VII103.2，不要求这些闭包标签单标签。重复同一有界参数极限：刚付的半轴界保留秩三，$e_i$ 的原极限给 $E\subseteq D_p$，而全部移动球缘已经在紧纯 $M$ 中。相同论证给 $E=D_p$。这证明整个 $M$ 上的连续性，且 $S_p\subseteq M$ 正是实际零邻封闭。证毕。

连续整球唯一确定连续中心和形状算子 $A_p\ge0$，满足
$D_p=c_p+A_p^{1/2}\overline B_{\ker u}$、$\operatorname{rank}A_p=3$。例如支撑函数的奇偶部分给中心，剩余支撑函数的平方经极化给 $A_p$；常秩下局部正交标架及伪逆连续。这是 XII147.5、XI145.6所用的同一有限维参数工具，此处其入口已由引理149.7支付。

### 149.5 重复纯极限与单标签区的相对开放性

**引理 149.8（$M$ 内的单标签区开放）。** $M\cap P_{\rm s}$ 是非空的 $M$-开集。

证明。非空性来自 $Q\subset M\cap P_{\rm s}$。反设重复标签 $p_i\in M\setminus P_{\rm s}$ 趋于 $p\in M\cap P_{\rm s}$。记其孤立重复球对为 $F_i=D_{p_i},G_i$。[IX 定理116.2][S149IX]准确给
$I(F_i)=S(G_i)$、$I(G_i)=S(F_i)$，两球不交，且不接触第三球。

由引理149.7，$F_i\to D_p$。取任意 $q\in S_p$，可在 $S(F_i)$ 取 $q_i\to q$；球缘逼近来自连续的秩三球参数。各 $q_i\in M$，且 $D_{q_i}=G_i$，所以 $G_i\to D_q$。又 $p_i\in S(G_i)$，故 $p\in S_q$。在非退化 $S_q$ 取 $r\ne p$，再取 $r_i\in S(G_i)\to r$。所有 $r_i,r$ 都在 $M$；重复对的准确标签式给 $D_{r_i}=F_i$，连续性遂给 $D_r=D_p$。但 $p$ 单标签，迫 $r=p$，矛盾。证毕。

这里没有将重复球的纯极限先排除，也没有断言 $M\subset P_{\rm s}$。所付的只是重复标签不能在这个已付整球连续的紧纯域内积聚到单标签点。它不同于 [SAME_READBACK 定理126.7—126.8][S149SR126] 已有的单标签积聚和上包含。

### 149.6 原法向层给闭包中的真实四维开图

**引理 149.9（相对于 $M$ 的四维开图）。** 存在非空 $M$-开集 $A\subset Q$，同胚于 $\mathbb R^4$ 的开集。

证明。令 $O=M\cap P_{\rm s}$。它是紧度量 $M$ 的非空开子空间，因而局部紧、具有 Baire 性。XII147 给 $\dim L_p=4$ 于每个 $p\in O$。在原八维仿射空间 $\{u=1\}$，

$$
N_p\overset\sim\longrightarrow\mathcal N_K(p),\qquad
h\longmapsto-h|_{\ker u}
\tag{149.18}
$$

是正法向与通常外法向的锥同构；反向是对 $v\in(\ker u)^*$ 取 $h(x)=-v(x-u(x)p)$。故不发生维数平移。

对原八维凸体应用 [SAME_READBACK 引理128.2及证明][S149SR128]，取 $k=4$。得到覆盖全部 $\Sigma_4(K)$ 的可数紧层 $X_j$，每层有到四维空间的正交投影 $\pi_j$，满足
$\|x-y\|\le(2/\sqrt3)\|\pi_jx-\pi_jy\|$。这是全点覆盖。相对闭集 $O\cap X_j$ 覆盖 $O$，Baire 给一个非空 $M$-开集 $O_1\subset O\cap X_j$。

$Q$ 在 $M$ 中稠密，故可取 $a\in Q\cap O_1$。在实际球面 $S_a$ 的一点 $q_0$ 附近，连续秩三球族 $D_q$ 可写成 $c(q)+B(q)\overline B^3$，其中 $B(q)$ 连续单射。这由引理149.7及上述局部标架工具支付。所有这些球都含同一实际点 $a$。取 $S_{q_0}\setminus\{a\}$ 中充分靠近 $a$ 的一点，再取其小紧二维球帽；缩小 $q_0$ 周围的二维底盘，使整个乘积像位于 $O_1$ 且避开 $a$。这里 $O_1=M\cap W$，$W$ 环境开，联合连续性和帽的紧性支付同时缩小。两盘各取闭方盘，得到

$$
\Psi:[0,1]^4\longrightarrow O_1\cap Q,
\qquad \Psi(q,t)=c(q)+B(q)t.
\tag{149.19}
$$

其像在 $Q$ 中是因 $a\perp q\perp\Psi(q,t)$ 及(149.3)。固定 $q$ 时单射；不同 $q,q'\in S_a\subset P_{\rm s}$ 的球不同且只交于 $a$，两帽避开此点，故跨标签亦单射。紧源使 $\Psi$ 为到像的同胚。

现在 $\pi_j\Psi:(0,1)^4\to\mathbb R^4$ 连续单射。[Hatcher Theorem 2B.3][S149Ha]给其像 $\Omega$ 开。由同一个 $X_j$ 上投影单射，

$$
A:=\Psi((0,1)^4)=O_1\cap\pi_j^{-1}(\Omega).
\tag{149.20}
$$

故 $A$ 相对于 $M$ 开，且是实际四维图。此处没有把紧四立方体本身认作原纯开图，也没有声称 $A$ 已相对于整个 $P$ 开。证毕。

### 149.7 同一根的紧四维载体

**引理 149.10（紧四维二步流形）。** 可固定 $o\in A$，使

$$
T=\bigcup_{s\in S_o}S_s\subset Q
\tag{149.21}
$$

以原子空间拓扑是非空紧、无边界四维流形。

证明。固定引理149.9图内任一 $o$。$S_o$ 紧且包含于 $M$，引理149.7给整个 $S_o$ 上的球连续。实际关联空间
$\mathscr S_o=\{(s,r):s\in S_o,r\in S_s\}$ 在紧 $S_o\times M$ 中闭：极限标签和极限点都在 $M\subset P$，整球上包含给 $r\in D_s\cap P=S_s$。故它及其评价像 $T$ 紧。

这个关联是实际 $S^2$ 丛。具体地，写 $Z_s=\operatorname{im}A_s$、$w_s=A_s^{\dagger/2}(o-c_s)$，则 $Z_s$ 连续秩三、$w_s$ 是连续单位截面。去掉公共根截面后，按 [XI145.7证明的球极投影公式][S149XI145]，

$$
(s,v)\longmapsto
\left(s,c_s+A_s^{1/2}
\frac{2v+(\|v\|^2-1)w_s}{1+\|v\|^2}\right),
\quad v\in Z_s\cap w_s^\perp
\tag{149.22}
$$

给秩二实向量丛到 $\mathscr S_o^\times=\{(s,r)\in\mathscr S_o:r\ne o\}$ 的同胚。逆是球极投影，分母 $1-\langle A_s^{\dagger/2}(r-c_s),w_s\rangle>0$。因此 $\mathscr S_o^\times$ 是无边界四维流形。

评价 $\mathscr S_o^\times\to T\setminus\{o\}$ 单射：不同 $s\in S_o$ 的实际单标签球只交于 $o$。其逆连续：对 $r_i\to r\ne o$，用紧 $S_o$ 取对应 $s_i$ 的任意聚点，整球闭图使其为 $o,r$ 的同一个共同邻标签，唯一性迫整列收敛。因此 $T\setminus\{o\}$ 也是四维流形。

还须处理根，不能只用删根后的流形结论。在实际 $M$-开四维图 $A\ni o$ 内，评价限制
$\operatorname{ev}^{-1}(A\setminus\{o\})\to A\setminus\{o\}$ 是两个四维无边界流形间的连续单射，源为开子空间。区域不变性给 $T\cap(A\setminus\{o\})$ 开；紧 $T$ 又使它相对闭。在 $A$ 中取以 $o$ 为坐标中心的小四维开球 $U$。$U\setminus\{o\}$ 连通；上述交集非空，因为任取 $s\in S_o$，其完整 $S_s$ 上有别的点趋近 $o$，最终进入 $M$-开集 $U$。故 $U\setminus\{o\}\subset T$，加上根得 $U\subset T$。$U$ 是 $T$ 中含根的四维开图，根也没有边界。

整个 $T$ 的点经两条实际零边从 $o\in A\subset Q$ 到达，故 $T\subset Q$。各空间都是原有限维环境的子空间，Hausdorff、第二可数。证毕。

### 149.8 原七维边界开放性与完整标签返回

**定理149.2的证明。** 先由 XII147 得 $\dim V=9$。引理149.5—149.10均在其原前件下成立。令 $H=\{u=1\}$、$\partial K=\partial_HK\cong S^7$。在引理149.10的同一个紧四维流形 $T\subset Q$ 上，整个实际球族 $x\mapsto D_x$ 连续。其秩三形状算子和局部标架给真正的闭三球丛及其内部丛

$$
\mathscr E=\{(x,z):x\in T,z\in D_x\},\qquad
\mathscr E^\circ=\{(x,z):x\in T,z\in\operatorname{ri}D_x\}.
\tag{149.23}
$$

局部参数为 $(x,v)\mapsto(x,c_x+B_xv)$，逆由连续左逆给出。$\mathscr E$ 在紧 $T\times K$ 中闭而紧；$\mathscr E^\circ$ 是七维无边界流形。评价

$$
\operatorname{ev}:\mathscr E^\circ\longrightarrow\partial K
\tag{149.24}
$$

连续且单射。若两个球的相对内点相同，该点是原混态，VII103.2的点交规则使两球相同；它们的标签都在 $T\subset P_{\rm s}$，故标签也相同。源、靶均为七维无边界流形，区域不变性给

$$
\mathcal O=\bigcup_{x\in T}\operatorname{ri}D_x
\text{ 在整个原 }\partial K\text{ 中开},\qquad
\mathcal B=\bigcup_{x\in T}D_x\text{ 紧而闭}.
\tag{149.25}
$$

这一步支付的是原凸边界中的真实开放性，前面的 $M$-开图没有被提前升级为 $P$-开图。

若 $\mathcal B\ne\partial K$，取紧分离子 $Z=\partial_{\partial K}\mathcal B$。$\mathcal O$ 非空且 $\partial K\setminus\mathcal B$ 非空开，故 $Z$ 非空、真，且其补集分成两个非空不交开集。任取 $z\in Z$，有 $z\in D_x$、$x\in T$。若 $z$ 混，则 $z\in\operatorname{ri}D_x\subset\mathcal O$，违反边界定义。因此

$$
Z\subseteq\bigcup_{x\in T}S_x\subseteq Q\subseteq P_{\rm s}.
\tag{149.26}
$$

这里最后的实际零邻封闭是关键：无需给分支外原纯点预付四维法向。XII147 已对这个 $Z$ 的**每一点**给四维法向。同149.6的原紧层，$Z_j=Z\cap X_j$ 是覆盖 $Z$ 的可数紧闭集，且同胚于 $\mathbb R^4$ 中的紧集。覆盖维数的闭子集单调性及正规空间闭子空间可数和定理，准确用 [Engelking Theorems 3.1.4、3.1.8、1.8.2][S149En]，给

$$
\dim_{\rm cov}Z\le4.
\tag{149.27}
$$

另一方面，对任意非空紧真子集 $Z\subset S^7$ 的 Čech–Alexander 对偶，[Hatcher Corollary 3.45及页256—257的紧集扩张][S149Ha]给

$$
\check H^6(Z;\mathbb Z)\cong
\widetilde H_0(S^7\setminus Z;\mathbb Z)\ne0.
\tag{149.28}
$$

这里没有给 $Z$ 加局部可缩或流形前件。式(149.27)使每个有限开覆盖可细化为神经维数至多四的覆盖；Čech 群的覆盖神经直接极限于是给 $\check H^6(Z;\mathbb Z)=0$，矛盾。因此 $\mathcal B=\partial K$。

最后返回全部实际标签。任取原 $a\in P$，取原混态 $z\in\operatorname{ri}D_a$。边界覆盖给某个 $x\in T$ 满足 $z\in D_x$；混点交使 $D_a=D_x$。这里只需 $x\in P_{\rm s}$ 的单标签性，便得 $a=x\in T$。所以

$$
P=T\subseteq Q\subseteq P_{\rm s}\subseteq P,
\qquad Q=P_{\rm s}=P=M.
\tag{149.29}
$$

全局 Inj 已付清，才直接消费 [XI 定理145.2][S149XI145] 的 EB3+Inj+九维分支，得到同锥同单位的(149.5)。其条件应用145.9给标准原效应和球中心；在(149.4)的 $q$ 处评价得到 $\kappa=e_q(q)+e_{q^\sharp}(q)=1$，因为标准球内对径是正交纯点。定理149.2证毕。

此证明复用 [XI142.2第四、五步][S149XI142]的原边界评价和紧分离子方法，但重新支付其入口：紧四维 $T$ 来自(149.4)的紧纯闭包，球连续来自引理149.7；分离子不是任意未知原纯集，而由(149.26)确实落在已付四维法向的 $Q$ 内。没有调用 XI142.2的 Conn、全域根芽、全域 Inj 或全域法向作为前件。

### 149.9 候选、整个标准反向与条件比较

**定理149.3的证明。** 左侧由引理149.4在一个非空实际零分支取得定理149.2的完整前件，故得到(149.5)。

反向取整个 $\operatorname{Herm}_3(\mathbb C)$、PSD 锥和迹单位。全部原效应是 $f_A(X)=\operatorname{Tr}(AX)$、$0\preceq A\preceq I_3$。对单位向量 $v$，令 $P_v=vv^*$、$Q_v=I_3-P_v$。完整确认菜单的计算见149.10，给

$$
D_{P_v}=\{\rho\succeq0:\operatorname{Tr}\rho=1,\ \rho v=0\},
\qquad e_{P_v}=f_{P_v},\qquad c_{P_v}=Q_v/2.
\tag{149.30}
$$

这是整个 $v^\perp\cong\mathbb C^2$ 的密度三球，故 EB3。相同球给相同支持平面，继而给相同纯射线，所以 $P_{\rm s}=P$。原实维数九；若 $P_v\perp P_w$，则
$e_{P_v}(c_{P_w})=(1-|v^*w|^2)/2=1/2=e_{P_w}(c_{P_v})$。故 $\mathsf{CR}_{\rm s}$ 成立。任意两条原纯射线，包括相同射线，都有单位 $z\perp\operatorname{span}_{\mathbb C}\{v,w\}$；原 $P_z$ 给两条实际零边。这同时核对 Conn 和每根两步覆盖的标准反向。所有对象沿同一个 $\Phi$ 运输，保持全部原量词。证毕。

这里将原全局 Conn 输入替换为实际单标签零边的球心关系和整个载体的维数上界，未证明独立条件之间的严格逻辑弱化或全局最小性。裸 EB3+九维到 Inj 仍开放；(149.6)的证明实际使用了 $\mathsf{CR}_{\rm s}$ 来支付共同差额及紧纯闭包。也未从纯端点最低确认互易、局部标签唯一或紧四立方体单独推出本候选。

### 149.10 同一个表示的完整静态量子字典

**推论 149.11（全原对象、全菜单与每混输入的 minimum）。** 在定理149.3的等价条件下，采用其同一个 $\Phi$，置 $p_v=\Phi(P_v)$、$U=\Phi(I_3)$、$f_A(\Phi X)=\operatorname{Tr}(AX)$。则 [XI 条件应用145.9][S149XI145] 的全部静态字典适用，具体为

| 原对象 | 同一个表示下的全部对应 |
| --- | --- |
| 全空间、全锥和原单位 | $V=\Phi(\operatorname{Herm}_3)$，$C=\Phi(\mathrm{PSD}_3)$，$u(\Phi X)=\operatorname{Tr}X$，包括零、次归一和任意非负质量。 |
| 全部原态与纯点 | $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$，$P=\{p_v:\|v\|=1\}\cong\mathbb{CP}^2$；所有有限凸混合保持。 |
| 全部效应与评价 | $\mathcal E=\{f_A:0\preceq A\preceq I_3\}$，原评价为 $\operatorname{Tr}(A\rho)$，零、单位、补及原锥序保持。 |
| 完整非单点确认菜单 | $\mathcal F_{p_v}=\{f_{P_v+B}:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\}$。 |
| least与每个原混输入的已达最低值 | least为 $f_{P_v}$，$T_{p_v}(\Phi\rho)=v^*\rho v$，由完整菜单的同一 $B=0$ 达到。 |
| 整个原零球和球缘 | $D_{p_v}=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1,\rho v=0\}$，是整个 Bloch 三球；纯球缘为 $\mathbb{CP}^1\cong S^2$。 |
| 二元最低确认和三元完成 | $T_{p_v}(p_w)=|v^*w|^2$；每条原零边有唯一第三纯点，三个正交纯投影及其 least 效应分别和为 $U$、$u$。全部不同纯对的原最小面为完整原球，全 Pair成立。 |
| 全部有限数学 POVM | 对任意有限结果数，$f_j\in C^*$、$\sum_jf_j=u$ 恰对应 $A_j\succeq0$、$\sum_jA_j=I_3$；含零效应、重复项和全部有限粗粒化。 |
| 谱、共同尺与 Jordan 结构 | 每态有三项正交纯谱分解，允许零权和重谱；迹内积使 $C$ 自对偶，$\Phi X\circ\Phi Y=\Phi((XY+YX)/2)$，单位为 $U$；正定合同变换给锥内部齐次性。 |
| 全域球心几何 | $R(x)=(u(x)U-x)/2$，$c_p=R(p)$；在 $K$ 中相对 $U/3$ 反向缩小一半。全部有限纯配方替换球心后仍给同一原态。 |

证明。表示的全锥与全单位性质首先确定全部态、极点及全对偶效应。若 $0\preceq A\preceq I_3$ 且 $v^*Av=1$，则正矩阵 $I_3-A$ 的零二次型给 $(I_3-A)v=0$；Hermitian 性消去交叉块，得到全部且仅有 $A=P_v+B$ 如表。$B=0$ 与 $B=Q_v$ 都合法，菜单非单点。对每个 $X\succeq0$，$\operatorname{Tr}(BX)\ge0$，故 $B=0$ 给全锥序 least 及每个混输入的 minimum。正性又给 $v^*\rho v=0\Longleftrightarrow\rho v=0$，保留含全部混态的整个零球。其余逐项沿 XI 条件应用145.9的同一 $\Phi$ 运输；这里的145.9是静态字典，不是作为证明迁移的命题145.8。证毕。

### 149.11 独立实际物理合同

定理149.3只分类原静态单体。完整继承 [XI第145.9节][S149XI145]及 [SAME_READBACK 第127.10节（SECTION127.10）][S149SR126]的全部原对象、前件和量词。共同来源域 $\Omega$、未知 ingress、全部原装饰和同源实现、共同读回、全实关系、原概率像紧性、零／单位／补／有界倍增、零及不等质量、原两尺度等式和每个资格输入，均仍独立供应。$\mathbb{CP}^2$ 的静态复射线不产生实际相干制备、相位参考、权限或门。

对每个有限 $N$，仍须另供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格单位 $u_N=u^{\otimes N}$、整个 $K_N,P_N,[0,u_N]$，及每个实际分割的 $C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b$、规范重括号和因子置换。全纠缠输入的联合最低确认、低二份 Jordan 桥、实际自复合及复型选择、实际三份资源和其锥成员身份，均各有原合同；高阶排除域不被规定为单体三球。

全旁观 CP仍量化每个有限旁观系统和每个共同纠缠输入。数学 CP-TNI 分支成为实际事件需要事件饱和及原实现；实际仪器仍需同一输入上的逐分支和同族预算、接线、探针、记录、粗粒化、输出与校准。只在严格正质量分支条件归一。数学有限 POVM、least及 Born minimum 不提供这些实际资格，Lüders 更新另保其锐性和接受态中性前件。

设备与来源绑定、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、原字和旧 support、每个中间 cut、全部合法 futures及记录后的条件未来，继续按原合同量化，不能由单体几何补齐。原物理 clock、实际连续动态来源、时间单位、Hamiltonian、能量识别和标定、数值 $\hbar$、时空与物理空间维数仍独立。另给全实时间连续保锥保质量群才有相应有限维生成元；再给酉时间实现才写 $U_t=\exp(-\mathrm itH/\hbar)$。恒等时间族和非平凡 Hamiltonian 族可共享这里全部静态对象。本章没有经验完成或零假设的结论。

### 149.12 归属与完整中文图景

原面和实际标签二分准确复用 VII103.2、IX116.2及116.6；原维数下界及全部单标签局部接口复用 XII147；单根高度、闭影像、支撑微分和原效应上界的机制复用 XI149及其实际消费者 THREE_COPY VII122.4、SAME_READBACK123.3与124.3。共同恒等式以下的承重连接是：同一差额支付所有半轴，反向实际对径排除混标签极限，紧纯闭包支付全族连续，重复对的互返标签式支付单标签区在该闭包中的开放性，再由原法向投影建立相对开四维图和紧四维二步流形。最后把其完整三球族送入整个原边界，并把任何潜在分离子准确留在已付法向的实际单标签域中，完成全域标签返回。

原法向紧层和投影是 SAME_READBACK128.2的既有全点工具；四维层投影和删根球束的参数方式复用 XI145.4—145.7；七维开放评价和 Čech–Alexander 分离子方法复用 XI142.2第四、五步。有限维紧性、Baire、连续半正定平方根、常秩局部标架、区域不变性和覆盖维数闭集可数和均为成熟中间工具。上述综合不主张文献优先权；最后的同锥同单位分类及完整字典分别复用 XI定理145.2、条件应用145.9，不将区域矩阵表示、光滑射影结构、谱性、正限制逆或全局 joins作为输入。

完整中文图景是：所有纯态、混态和允许的尺始终属于同一块原状态体。两个元素之间的零边，只表示有一把原尺在一端读一、另一端读零。每个实际单标签点背后是一整颗实心排除三球。球心互易只交换零边两端的球心读数，不要求任何两次实际测量的次序交换。单根计算先让各方向的高度相同，再沿实际零路传成一个共同差额；它没有预装全局连通。

在一颗球内取一对对径，两个端点各自的原确认尺之和等于根的互补尺乘同一个 $\kappa<2$。端点的读数差始终是 $2-\kappa$，因此不论球怎样移动，所有轴都有同一正下界。若某列纯标签落成混态，它所在的整张真面会使一把极限尺处处读一；沿旁边实际球再取一次对径，同一恒等式却要求这把尺读成 $\kappa-1<1$，矛盾。因此整个标签闭包仍纯，移动球的全部极限才有资格被判为完整原球。

纯极限仍可能先落到重复标签，证明没有跳过它。若重复球对在这个连续紧纯族内靠近单标签点，两侧的全部球缘也必须互返收敛；取对侧另一端点，就会产生两个不同标签共用原来的单标签球。因此单标签部分在这个闭包内真正开放。原四维法向的紧投影层把一块两步四维紧块升级为闭包中的四维开图。围绕图内同一个根，第一层是二维球面，第二层删根后是二维平面；开图和紧性一起补回根，得到一座真正紧的四维纯载体。

让这座载体的每个标签携带它自己的完整实心三球，四加三得到七维球族。混态球内部不能互撞，所以这些内部在原七维凸边界中铺出真实开放区域。若尚有缺口，已铺部分的边缘只能由这座单标签族的纯邻点组成；它至多四维，却必须将七维球面分开，Alexander 对偶要求它至少六维，矛盾。完整球遂铺满原边界。再进入任意原标签的混态球内部，球的唯一性和已铺标签的单标签性把该标签也送回，才得到全部原纯域以及全局连通。

三元素图景随后才兑现：共同系数锁为一，一颗球内的对径两端彼此也成零边，连同根构成三个两两正交的原纯标签；三把 least 尺和为原单位。每条二元零边都有唯一第三元素。全部纯点组成同一个 $\mathbb{CP}^2$，每条完整零线是 $\mathbb{CP}^1$，其凸包就是完整 Bloch 三球；所有球心围绕共同中心反向缩小一半。整个混态域、全效应、非单点确认菜单、least、每个混输入的 Born 最低值和全部有限数学 POVM沿同一个表示一起得到。实际来源、仪器、纠缠联合、钟、能量和记录未来仍各自需要原合同。

[S149VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "定义103.1、定理103.2：完整minimum、原暴露极大球面、全部原真面穷尽；不预设Pair。"
[S149IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "定理116.2：孤立重复对及I(F)=S(G)、I(G)=S(F)；定理116.6：单标签非空及实际邻点单标签。"
[S149XII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md "第147章全文，特别是推论147.8、定理147.1、命题147.6及第147.9节：裸EB3九维下界和实际单标签完整局部法向；不供应全局Inj或P开图。"
[S149XI149]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "第149章全文，定理149.2—149.3：单根互易的正高度、闭影像及方向常值；本章149.2逐项支付其局部接口，不直接调用保留Conn的149.4。"
[S149TC]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "第122.2—122.3节、定理122.4及其证明：完整局部法向图、实际比值影像及接触纤维。"
[S149SR123]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "第123.2节、定理123.3及证明、定理124.3及证明：实际双球原V消元和同一原效应的高度差上界。"
[S149SR126]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "第126.5—126.8节，定理126.7—126.8：重复球积聚与上包含；SECTION127.10：全部独立实际合同。"
[S149SR128]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "引理128.2及证明式(Q128.6)—(Q128.8)：全部法向层的可数紧覆盖和到n-k维的单射投影。"
[S149XI145]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "定理145.2的EB3+Inj+九维分类，条件应用145.9的同一Phi完整静态字典，第145.9节的独立实际合同；145.4—145.7仅复用明确展开的局部参数及投影方法。"
[S149XI142]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "第142.2节第一、四、五步：紧法向投影层的覆盖维数应用、原七维边界开放评价与任意紧集的Čech–Alexander分离子矛盾；本章重付其实际适用域。"
[S149Ha]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology：Theorem 2B.3，印刷页172；Corollary 3.45，页255，以及页256—257对任意紧集的Čech扩张。"
[S149En]: https://www.maths.ed.ac.uk/~v1ranick/papers/engelking.pdf "R. Engelking, Dimension Theory：Theorems 3.1.4、3.1.8，印刷页209、212，正规空间闭子集单调性及闭子空间可数和；Theorem 1.8.2，页73，欧氏空间覆盖维数。"

## 追加锚（本行以下为增补区）

## 152. 完整菜单的严格差距与入射塌球的唯一落点

**定义 152.1（同原菜单、最优面与实际落点）。** 保留定义151.1的全部原 $V,C,u,K,P,\mathcal E,\mathcal F_p,T_p,D_p,S_p$，假设完整 EB3 与纯 PR。第二变量始终遍历整个原混态域 $K$。沿用 [X125.3][Q152X] 的整球零确认面，并定义辅助下包络、完整最优面和实际塌缩落点集：

$$
\begin{gathered}
\mathcal A_p=\{e\in\mathcal F_p:e|_{D_p}=0\},\qquad
B_p(x)=\min_{e\in\mathcal A_p}e(x),\\
M_p(x)=\{f\in\mathcal F_p:f(x)=T_p(x)\},\qquad
\Delta_p(x)=B_p(x)-T_p(x),\\
\mathscr L(p)=
\{r\in K:\exists(p_i)\subset P,\ p_i\to p,\
d_H(D_{p_i},\{r\})\to0\}.
\end{gathered}
\tag{XII152.1}
$$

$d_H$ 使用任一固定辅助欧氏范数。$\mathcal A_p$ 非空紧凸，其每个成员的整个原零面恰为 $D_p$；$M_p(x)$ 非空紧凸。因此 $0\le T_p(x)\le B_p(x)\le1$，两种 minimum 均达到，且固定标签的两种下包络都在整个 $K$ 上连续。$B_p$ 仅比较原菜单的一个子面，没有替换原 $T_p$。按 [IX115.5][Q152IX]，$\mathscr L(p)\subseteq S_p$；它可以为空。以下不输入全域 Inj、$\mathcal A_p$ 单点性、least 或 Conn。

**定理 152.2（严格差距定位全部最优效应的同一原零点）。** 令

$$
U_p=\{x\in K:\Delta_p(x)>0\}.
\tag{XII152.2}
$$

对每个 $x\in U_p$，存在唯一 $r_p(x)\in S_p$，使每张 $f\in M_p(x)$ 都满足

$$
Z(f):=\{z\in K:f(z)=0\}=\{r_p(x)\}.
\tag{XII152.3}
$$

映射 $r_p:U_p\to S_p$ 连续。若固定原纯输入 $s\in P$ 满足 $\Delta_p(s)>0$，则对每个 $\eta>0$，存在 $p$ 在 $P$ 中的邻域 $W$，使

$$
\forall a\in W\ \forall f\in M_a(s):\qquad
\varnothing\ne Z(f)\subset
\{z\in K:\|z-r_p(s)\|<\eta\}.
\tag{XII152.4}
$$

证明。先在承重推导内部复用 [X125.2式(X125.8)][Q152X] 的原菜单归一化：当 $t=T_p(x)<1$ 时，每个最优 $f$ 都在整个 $K$ 上取零。否则 $m=\min_Kf>0$，则

$$
\widetilde f=\frac{f-mu}{1-m}\in\mathcal F_p,\qquad
\widetilde f(x)=\frac{t-m}{1-m}<t,
\tag{XII152.5}
$$

矛盾。该效应在全部 $K$ 上介于零与一，再由原 $u$ 齐次化到整个 $C$，不要求面效应延拓。

取 $f_0\in\operatorname{ri}M_p(x)$。对任意 $f\in M_p(x)$，有限维凸集的相对内部性质给 $g\in M_p(x)$ 与 $0<\lambda<1$，使 $f_0=\lambda f+(1-\lambda)g$。全域非负性遂给

$$
Z(f_0)=\bigcap_{f\in M_p(x)}Z(f)\ne\varnothing.
\tag{XII152.6}
$$

这是同一最优面的共同零集。每个最优效应的零面都包含于 $D_p$。由完整原真面分类，它只能是纯单点或整个 $D_p$。严格差距排除 $M_p(x)\cap\mathcal A_p\ne\varnothing$，故这些零面均为单点；(XII152.6)使其全部相同，得到(XII152.3)。

若 $x_i\to x\in U_p$，选 $f_i\in M_p(x_i)$。$T_p$ 连续、$\mathcal E$ 与 $D_p$ 紧，使任意子列可再取
$f_i\to f$、$r_p(x_i)\to r'$。评价连续给 $f\in M_p(x)$、$f(r')=0$，故 $r'=r_p(x)$。这给所述连续性。

现在固定上述纯 $s$。仅对纯端点使用 PR 和固定 $T_s$ 的连续性：

$$
T_a(s)=T_s(a)\longrightarrow T_s(p)=T_p(s)<1
\qquad(a\to p,\ a\in P).
\tag{XII152.7}
$$

因此邻近标签的全部最优效应也各有非空原零面。若(XII152.4)失败，可取 $a_i\to p$、$f_i\in M_{a_i}(s)$ 及 $z_i\in Z(f_i)$，使 $\|z_i-r_p(s)\|\ge\eta$。紧性取 $f_i\to f$、$z_i\to z$；(XII152.7)使 $f\in M_p(s)$，而 $f(z)=0$。这与(XII152.3)及距离下界矛盾。证毕。

**定理 152.3（单落点限制与整球并合时的差距保留）。** 在相同完整原域中：

1. 若某个原纯 $s$ 满足 $\Delta_p(s)>0$，则

$$
\mathscr L(p)\subseteq\{r_p(s)\}.
\tag{XII152.8}
$$

2. 若 $a_i\to p$ 且 $D_{a_i}\xrightarrow{H}D_p$，则对每个固定原纯 $s$，

$$
\liminf_i\Delta_{a_i}(s)\ge\Delta_p(s).
\tag{XII152.9}
$$

特别地，若 $\Delta_p(s)>0$，这条整球并合序列最终满足
$M_{a_i}(s)\cap\mathcal A_{a_i}=\varnothing$。

证明。对第一项，若 $D_{a_i}\to\{r\}$，从 $M_{a_i}(s)$ 的任一效应中取真实零点 $z_i$。它属于整个 $D_{a_i}$，故 $z_i\to r$；(XII152.4)又给 $z_i\to r_p(s)$，得到(XII152.8)。发送标签可以来自不同零图分量，没有预设它们与 $p$ 有限零路可达。

对第二项，取 $e_i\in\mathcal A_{a_i}$ 达到 $B_{a_i}(s)$。沿实现下极限的子列再用紧 $\mathcal E$ 取 $e_i\to e$。$e_i(a_i)=1$ 给 $e(p)=1$。对任意 $z\in D_p$，Hausdorff 收敛给 $z_i\in D_{a_i}$、$z_i\to z$，于是 $e(z)=\lim e_i(z_i)=0$。故 $e\in\mathcal A_p$，得到 $\liminf_iB_{a_i}(s)\ge B_p(s)$。减去(XII152.7)的极限即得(XII152.9)。证毕。

这是同一完整菜单中两种 minimum 的差距约束，不是整球连续性的新增假设。整球并合不会自动把原最优效应改成整球零确认；正差距反而保留。

**定理 152.4（两落点、纯行达到与单标签 least）。** 若 $\mathscr L(p)$ 至少含两个不同点，则

$$
T_p(s)=B_p(s)\qquad(s\in P).
\tag{XII152.10}
$$

若再有 $\mathcal A_p=\{e_p\}$，则同一个原 $e_p$ 是完整菜单的 least：

$$
T_p(x)=e_p(x)\quad(x\in K),\qquad
f-e_p\in C^\ast\quad(f\in\mathcal F_p).
\tag{XII152.11}
$$

而且 $\beta_{D_p}=1$，满刻度沿 $p$ 的整个有限零路分量传播。这些结论不要求全域 Inj。

证明。若(XII152.10)在某个原纯输入失败，定理152.3就把全部落点限制到一个点，矛盾。单点性再使 $T_p(s)=e_p(s)$ 对全部原纯 $s$ 成立。对每张固定 $f\in\mathcal F_p$，$f-e_p$ 因而在 $P$ 上非负。由有限维 $K=\operatorname{conv}P$、$C=\operatorname{cone}P$，同一线性泛函在整个 $C$ 上非负；$e_p$ 自己仍在完整菜单中，得到(XII152.11)。没有将逐输入的不同效应拼成仿射函数。

还须支付从这个单标签 least 到真实三角的桥。令 $g=u-e_p$。PR 的严格纯端点暴露给 $T_p(s)<1$ 对所有 $s\ne p$ 成立；由原纯分解及 $T_p=e_p$，有 $Z(g)=\{p\}$。任取 $q\in S_p$ 以及 $h\in\mathcal A_q$。零对称给 $p\in D_q$，故 $h(p)=0$、$h(q)=1$，于是 $u-h\in\mathcal F_p$。least 使

$$
k=(u-h)-e_p=g-h\in C^\ast,\qquad
k(p)=k(q)=0.
\tag{XII152.12}
$$

$k$ 非零，否则 $h=g$，但 $Z(h)=D_q$ 为非退化三球，与 $Z(g)=\{p\}$ 矛盾。故 $Z(k)$ 是含不同纯点 $p,q$ 的非空真面，由原面分类等于某个 $D_r$。零对称给 $p,q,r$ 两两正交，构成真实原三角。准确消费 [IX114.8][Q152IX] 的同球刻度和双向零边传播，即得 $\beta_{D_p}=1$ 及所述分量传播。证毕。

最后一段证明本身给更一般的单标签事实：只要某个 $p$ 已有真正的全菜单 least，它就进入真实三角并使该分量满刻度，不需要两落点前件。两落点与 $\mathcal A_p$ 单点性承担的是取得这个 least 的前一步。反之，若 $\mathcal A_p$ 单点且 $\beta_{D_p}>1$，必有某个原纯 $s$ 满足 $\Delta_p(s)>0$，从而 $\mathscr L(p)$ 至多一个点；否则上述纯行到 least 的推导将迫使满刻度。

**范围 152.5（原局部候选与未消去的两种退化）。** 完整候选仍是定义151.1的 EB3、字面纯 PR 与近一共同零条件 $\mathsf N_2$。推论151.4已将该候选接到同原锥、同原单位的复三能级结构：全纯域为 $\mathbb{CP}^2$，每张完整排除球的纯缘为 $\mathbb{CP}^1$；整个原确认菜单、全部混态最低值及全部原效应分别由(XII151.8)与其静态字典给出。本章保留这些原量词，不另作量子分类。

新增的承重约束是完整最优面的共同单点零集、该零点对混输入的连续定位、纯输入严格差距对全部入射塌缩的单落点限制，以及整球并合时差距的下半连续保留。两落点仅支付(XII152.10)的逐纯输入达到；当 $\mathcal A_p$ 多于一张时，未证明存在同一效应达到所有输入，更未证明整个 $T_p$ 仿射。单落点塌缩、具有多张整球零确认的接收标签，以及跨零图分量的整球并合均未排除。没有由此取得 $\mathsf N_2$、Conn、全域 Inj 或全部 $\mathcal A_p$ 单点，也没有完整 EB3+PR 坏模型；本章未减少候选的独立假设数。

归属为 repo-derived 的跨接口推导，不主张全球原创或最小性。相对内部共同零集、紧性与仿射归一化是成熟中间工具；原面分类、最优效应取零及实际球极限二择按上述来源复用。[Niestegge，2312.13213v2，§3][Q152N]的 $e_\omega$ 下确界遍历所有非负仿射 $a$、$a(\omega)=1$，未加 $a\le1$；其性质 $(\ast\ast)$ 另要求该下确界本身仿射并仅在 $\omega$ 取一。[Niestegge，2411.18589v2，Theorem 1][Q152B]仍以 $(\ast\ast)$ 与 bit symmetry 为前件才给自对偶及跃迁互易。它们没有支付本章 proper 全菜单的 least 或未证的局部共同零点。

**完整中文图景。** 仍在同一块原状态体中比较两种测试：一种允许使用全部原确认菜单，另一种要求把背后整颗排除球都清零。如果前一种能读得严格更低，那么所有达到最低值的测试都只能瞄准同一个真实零点；邻近标签的最优测试也把全部零点收向那里。因此所有向这个标签塌来的球只能落到同一处。若确实有两处不同落点，整行纯读数就已能交给整球清零测试；这些测试再唯一时，同一张尺才支配整个原菜单，并把该标签接进真实正交三角。尚未证明的是，剩下的单落点或多尺情形是否不可能，所以近处两态必有共同排除点这一条仍然保留。实际仪器、复合纠缠、全旁观 CP、物理时间、Hamiltonian 和能量继续各按原独立合同承担。

[Q152IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.2—114.5：完整原面、严格纯暴露、原纯紧性及球内刻度；IX114.8：真实三角与满刻度传播；IX115.5：实际整球极限二择。"
[Q152X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X125.2式(X125.8)：完整原菜单最优效应的全域取零；X125.3：非空紧凸整球零确认面及准确原零面；X126.6保留全域Inj及单标签唯一性的较强前件。"
[Q152N]: https://arxiv.org/html/2312.13213v2 "G. Niestegge，Quantum transition probability，§3：非负仿射下确界及另列的性质(**)。"
[Q152B]: https://arxiv.org/html/2411.18589v2 "G. Niestegge，Bit symmetry entails the symmetry of the quantum transition probability，Theorem 1。"

## 追加锚（本行以下为增补区）

## 153. 原纯帽的道路、联合读数与混输入最低值

**定义 153.1（原域、仿射纯帽与局部差距）。** 保留定义151.1、152.1的全部原 $V,C,u,K,P,\mathcal E,\mathcal F_p,T_p,D_p,S_p,\mathcal A_p,B_p,M_p,\Delta_p,\mathscr L(p)$，假设完整 EB3 与字面纯 PR。每个 minimum 仍遍历其原菜单，并在全部原混输入上达到。对原仿射函数 $a$ 与 $c\in\mathbb R$，记

$$
U(a,c)=\{p\in P:a(p)>c\}.
\tag{XII153.1}
$$

固定一个辅助欧氏范数，其开球记作 $B_\eta(x)$。下文不输入 Conn、全域 Inj、$P_0$、least、局部流形或群齐性。$T_p$ 是原仿射效应的凹下包络，不预设仿射。

**定理 153.2（仿射纯帽与局部纯路径）。** 每个非空 $U(a,c)$ 连通且道路连通；这些帽给 $P$ 每点的道路连通开邻域基。特别地，整个原纯域为局部道路连通、道路连通的紧度量空间。

证明。复用 [IX114.2—114.4][Q153IX] 与定理151.2：$P$ 紧连通，每个纯点严格仿射暴露，每个非空真暴露面的全部纯点构成单点或完整 $S^2$，故连通。以下支付这些原凸条件到半空间截面连通的桥。

空帽及整个 $P$ 的帽已处理。设 $U=U(a,c)$ 非空且真，固定 $p\in U$，取在原 $K$ 上唯一最大于 $p$ 的仿射函数 $b_p$，并置

$$
Q_t=\operatorname*{argmax}_{q\in P}(b_p(q)+t a(q)),
\qquad t\ge0.
\tag{XII153.2}
$$

$b_p+t a$ 始终非恒定：若 $t>0$ 时恒定，则 $p$ 是 $a$ 的全局最小点，却又有 $\min_Pa\le c<a(p)$；$t=0$ 由严格暴露排除。因此 $Q_t$ 是某个真暴露面的完整纯缘，非空紧连通，且 $Q_0=\{p\}$。对 $t>0$、$q\in Q_t$，比较 $q,p$ 给

$$
t(a(q)-a(p))\ge b_p(p)-b_p(q)\ge0.
\tag{XII153.3}
$$

故全部 $Q_t$ 都在较紧的闭帽 $\{a\ge a(p)\}\subset U$ 内。

对每个有限 $T$，集合

$$
G_T=\{(t,q)\in[0,T]\times P:q\in Q_t\}
\tag{XII153.4}
$$

紧，其向区间的投影满射且纤维连通。若 $G_T$ 有非平凡紧开闭分离，每根纤维只能在一侧，两侧投影便给区间的非平凡紧分离，矛盾。故 $G_T$ 连通，其第二投影也连通。于是

$$
E_p=\overline{\bigcup_{t\ge0}Q_t}^{\,P}
\subseteq\{a\ge a(p)\}\subset U
\tag{XII153.5}
$$

为含 $p$ 的紧连通集。这里固定的严格余量 $a(p)-c$ 保证闭包仍在开帽内。

记 $Q_a=\operatorname*{argmax}_P a$。因帽非空且真，$Q_a$ 也是非空紧连通的真面纯缘。取 $t_n\to\infty$、$q_n\in Q_{t_n}$，极大值比较给

$$
0\le\max_Pa-a(q_n)
\le\frac{\max_Pb_p-\min_Pb_p}{t_n}.
\tag{XII153.6}
$$

由紧性，$E_p\cap Q_a\ne\varnothing$。所有 $E_p$ 都接到同一个 $Q_a$，且包含各自的 $p$，故 $U=Q_a\cup\bigcup_{p\in U}E_p$ 连通。没有选择连续极大点。

对任意 $p\in P$ 及其纯开邻域 $W$，严格暴露和紧 $P\setminus W$ 给 $\max_{P\setminus W}b_p<b_p(p)$；在二者之间取阈值便得包含于 $W$ 的连通开帽。$W=P$ 时直接取整个 $P$。因此 $P$ 局部连通。$P$ 紧度量，故完备；准确复用 Mazurkiewicz–Moore–Menger 定理的完备度量局部连通推局部道路连通版本，见 [Björn–Björn–Shanmugalingam，§2][Q153T]。连通且局部道路连通的 $P$ 道路连通；其中每个连通开帽也道路连通，证毕。

这里的经典半空间连通性质称 two-piece property。它本身及完备度量拓扑推论不作为新发现；本条消费原暴露面纤维建立足以供定理153.4使用的原纯路径。该性质在光滑 Lie 群轨道中的使用见 [Luan–Tam，§2][Q153L]，其光滑性与轨道前件不由本条支付。整个 $P$ 的连通仍准确复用151.2，未将一般紧凸线段的离散极点集包含进结论。

**定理 153.3（一维整球零确认族的全部混输入达到）。** 固定原纯标签 $p$。若

$$
\dim\operatorname{aff}\mathcal A_p\le1,
\qquad T_p(s)=B_p(s)\quad(s\in P),
\tag{XII153.7}
$$

则

$$
\begin{gathered}
T_p(x)=B_p(x)\quad(x\in K),\\
\forall f\in\mathcal F_p\quad\exists e\in\mathcal A_p:
\quad f-e\in C^\ast.
\end{gathered}
\tag{XII153.8}
$$

特别地，定理152.4的 $|\mathscr L(p)|\ge2$ 配合该仿射维数条件，已足以取得(XII153.8)，无需 $\mathcal A_p$ 单点。

证明。先在推导内部使用成熟的仿射切片极点方法。对任意两个原仿射函数 $a_1,a_2$ 与非空切片

$$
K_y=\{x\in K:a_1(x)=y_1,\ a_2(x)=y_2\},
\tag{XII153.9}
$$

有 $\operatorname{ext}K_y=P\cap K_y$。确实，若切片极点 $z$ 是原内部混点，$\dim\operatorname{aff}K\ge4$ 使两个约束的共同核仍有非零方向，可在切片中以 $z$ 为中点作非退化小线段。若 $z$ 是原混边界点，其最小原面按完整面分类为某个 $D_r$，且 $z\in\operatorname{ri}D_r$；两个约束在三维 $\operatorname{aff}D_r$ 内的共同核至少一维，又得到同样矛盾。反向包含由原极端性直接成立。紧凸切片的极点分解遂给

$$
K_y=\operatorname{conv}(P\cap K_y).
\tag{XII153.10}
$$

因此任意原混态的两个仿射读数，总能由同一个原纯态同时匹配。这不是分别选择两个纯态，也没有假定所有混态本身纯。

非空紧凸且仿射维数至多一的 $\mathcal A_p$ 可写成 $[e_-,e_+]$，允许两端相同。置 $h=e_+-e_-$，则整个 $K$ 上准确有

$$
B_p=e_-+\min(0,h).
\tag{XII153.11}
$$

反设某张原 $f\in\mathcal F_p$、某个原混态 $x$ 满足 $f(x)<B_p(x)$。对两个仿射读数 $h,f-e_-$ 使用(XII153.10)，取得同一原纯态 $s$ 同时匹配二者。于是

$$
\begin{aligned}
B_p(s)-f(s)
&=\min(0,h(s))-(f-e_-)(s)\\
&=\min(0,h(x))-(f-e_-)(x)
=B_p(x)-f(x)>0,
\end{aligned}
\tag{XII153.12}
$$

与 $f(s)\ge T_p(s)=B_p(s)$ 矛盾。故所有原 $f$ 都满足 $f(x)\ge B_p(x)$；再用 $\mathcal A_p\subseteq\mathcal F_p$，得到全部混输入的等号。

还须证明同一 $f$ 有一张在整个原锥上被它支配的整球零确认。$\mathcal A_p+C^\ast$ 是紧集与闭凸锥之和，故闭凸。若 $f$ 不属于它，有限维严格分离给 $v\in V$ 满足

$$
f(v)<\inf_{e\in\mathcal A_p,\ k\in C^\ast}(e+k)(v).
\tag{XII153.13}
$$

右侧有限迫使 $v\in C$，否则沿某张负读数的正泛函之非负倍数即可将右侧降至负无穷。严格不等还迫使 $v\ne0$。以原 $u$ 归一化，令 $x=v/u(v)\in K$，得到 $f(x)<B_p(x)=T_p(x)$，矛盾。证毕。

$\mathcal A_p$ 在原正序中是反链：若 $e,e'\in\mathcal A_p$ 且 $e'-e\in C^\ast$ 非零，则它的真零面同时含整个极大真面 $D_p$ 和外部点 $p$，不可能。因此 $e=e'$。故在非退化线段分支 $e_-\ne e_+$ 中，(XII153.8)不成为全菜单 least；若 least 存在，它被每张 $\mathcal A_p$ 成员支配，因而自身属于 $\mathcal A_p$，再由反链性迫全部成员相同，矛盾。该分支若实际存在，全部混输入最低值的形状只能是 $\min\{e_-,e_+\}$。本条没有证明此分支与全域纯 PR 共存，也没有排除仿射维数至少二的确认族。

**定理 153.4（严格差距处的塌缩边界与纯路径实现）。** 固定原纯 $p,s$，假设

$$
\delta:=\Delta_p(s)>0,\qquad \mathscr L(p)\ne\varnothing.
\tag{XII153.14}
$$

按定理152.2—152.3，记 $r=r_p(s)$，则 $\mathscr L(p)=\{r\}$。在 $p$ 的任意指定纯邻域中，可选道路连通开帽 $U\ni p$ 及 $\varepsilon>0$，使每个 $a\in U$ 恰属下列一支：

$$
d_H(D_a,D_p)<\varepsilon,
\qquad\text{或}\qquad
D_a\subset B_\varepsilon(r).
\tag{XII153.15}
$$

令 $O=\{a\in U:D_a\subset B_\varepsilon(r)\}$、$Z=\partial_UO$。则 $O$ 非空且相对开，$p\in Z$；每个 $b\in Z$ 都满足

$$
\Delta_b(s)>\delta/2,\qquad
\mathscr L(b)=\{r_b(s)\},
\tag{XII153.16}
$$

且 $b\mapsto r_b(s)$ 在 $Z$ 上连续。还存在 $b\in Z$ 与连续原纯路径 $\sigma:[0,1]\to U$，使

$$
\sigma(0)=b,\qquad \sigma(t)\in O\quad(t>0),
\qquad D_{\sigma(t)}\xrightarrow[t\downarrow0]{H}\{r_b(s)\}.
\tag{XII153.17}
$$

沿此路径 $\beta_{D_{\sigma(t)}}\to\infty$，接收标签 $b$ 自身的预算仍有限。

证明。定理152.3的整球并合差距保留，先给出一个标签邻域及 Hausdorff 容差，使邻近 $p$ 且 $D_a$ 足够接近 $D_p$ 时，$\Delta_a(s)>\delta/2$；否则可用同时趋向 $p,D_p$ 的反例序列违反(XII152.9)。取 $\varepsilon<\operatorname{diam}D_p/8$ 并满足该容差。

[IX115.5][Q153IX]的准确整球极限二择与单落点限制给某个标签邻域，使(XII153.15)成立。否则取趋向 $p$ 且违反二择的标签序列，再取 Hausdorff 子列；极限只能是 $D_p$ 或 $\{r\}$，两者都与违反二择矛盾。利用定理153.2在该邻域及指定邻域内选道路连通开帽 $U$。两支互斥，因为第一支的球直径大于 $\operatorname{diam}D_p-2\varepsilon>6\varepsilon$，第二支的球直径小于 $2\varepsilon$。

整球上半连续性使 $O$ 相对开；已有入射塌缩使 $O\ne\varnothing$ 且 $p\in\overline O$，而直径界给 $p\notin O$，故 $p\in Z$。每个 $b\in Z\subseteq U\setminus O$ 属于整球支，因此其差距大于 $\delta/2$、球直径大于 $6\varepsilon$。对任意 $a_i\in O\to b$，球直径至多 $2\varepsilon$，故其任何 Hausdorff 子列极限都不能是整个 $D_b$。准确极限二择只留下单点，再由定理152.3将全部单点极限固定为 $r_b(s)$。于是 $D_{a_i}\to\{r_b(s)\}$，并给出(XII153.16)。

为核对落点连续性，取 $b_i\in Z\to b\in Z$、$f_i\in M_{b_i}(s)$。由各处严格差距，$Z(f_i)=\{r_{b_i}(s)\}$；定理152.2在固定接收标签 $b$ 的邻近标签零点控制，遂给 $r_{b_i}(s)\to r_b(s)$。

最后取 $a\in O$，在 $U$ 中选从 $p$ 到 $a$ 的连续纯路径 $\gamma$。闭集 $\{t:\gamma(t)\notin O\}$ 非空且不含一；令其最大元为 $t_0<1$，则 $b=\gamma(t_0)\in Z$，且其后路径全在 $O$。重参数化，并消费刚证明的边界极限，即得(XII153.17)。[IX115.3][Q153IX]的统一原效应范数界给 $2a_{D_{\sigma(t)}}\le L\operatorname{diam}D_{\sigma(t)}\to0$，故 $\beta=1/(2a)\to\infty$；每张实际完整球自身的 $a$ 仍严格正。证毕。

此处 $b$ 可在 $p$ 的任意近处取得，但没有强行令 $b=p$。$Z$ 也没有被断言为把 $U$ 分成两个非空开侧的分离子；整球支可能没有内部。塌缩路径与连续落点给单落点分支的实际局部形状，未将其排除。

**范围 153.5（比较、局部道路与准确零边的区别）。** 完整量子候选仍是原 EB3、字面纯 PR 与定义151.1的 $\mathsf N_2$。在这个候选下，推论151.4已经给同一 $C,u$ 的复三能级表示：全部原混态为密度矩阵、全部原效应为 $0\preceq E\preceq I_3$，全部原最低值为 $T_{\Phi(vv^\ast)}(\Phi\rho)=v^\ast\rho v$；纯域为 $\mathbb{CP}^2$，完整排除球的纯缘为 $\mathbb{CP}^1$。

本章支付了裸 EB3+PR 下的原仿射纯帽道路，以及它对实际塌缩边界的消费；另将一维整球零确认族的逐纯输入达到送到全部混输入。成熟的切片极点、严格分离与完备度量拓扑结论均仅作中间工具。上述跨接口推导归属 repo-derived，不认领新的经典拓扑定理、全球原创或最小性。

原纯帽可以与本标签的整颗排除球完全分离：取严格暴露 $p$ 的 $b_p$，由紧性有 $\max_{S_p}b_p<b_p(p)$，在两者间取阈值即可。因此帽内路径尚未给帽外的共同零邻点。整球并合仍是(XII153.15)保留的第一支；Hausdorff 接近不保证有限阶段 $D_p\cap D_q\ne\varnothing$。本章没有推出 $\mathsf N_2$、Conn、全域 Inj 或全部 $\mathcal A_p$ 单点，也没有完整 EB3+PR 反模型；候选的独立假设数没有减少。XII149的维数上界、单标签球心互易与共同三元恒等式仍保留其额外前件。

**完整中文图景。** 两两比较仍用同一套全部原测试，交换两纯端点只要求读数相同。现在可以在每个纯点附近切出一顶小帽，帽里的任意两点都能沿纯态连续走通；严格差距处的小排除球则会沿这种纯路径贴向一个具有连续落点的标签边界。另一方面，若整球清零测试的选择只排成一条线段，两张联合读数就足以把纯态上的最低值结论送到全部混态，但一段不同的尺仍不成为同一张 least。剩下的一步依旧具体：连续走近的两个标签，背后的排除球是否必有同一个真实零点。这一步未由路径、靠近或并合代替。实际仪器、复合纠缠、全旁观 CP、物理钟、Hamiltonian 和能量继续各按原独立合同承担。

[Q153IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.2—114.4：全部真面、严格纯暴露与原纯紧性；IX115.3—115.5：原效应界、整球上半连续与准确极限二择。"
[Q153T]: https://arxiv.org/html/1311.5122v1 "A. Björn, J. Björn, N. Shanmugalingam, The Mazurkiewicz distance and sets that are finitely connected at the boundary，§2：完备度量空间中 Mazurkiewicz–Moore–Menger 局部道路连通推论。"
[Q153L]: https://arxiv.org/html/2611.02575v1 "Y. Luan, T.-Y. Tam, Planar Convexity of Isotropy Orbits via Cohomology and Common Zeros，§2：two-piece property 的半平面表述及其另需光滑流形前件的消费者。"

## 追加锚（本行以下为增补区）

## 154. 三步原纯张成、单标签分量与相对四维几何

### 154.1 同一原域、实际路径与准确供应

**定义 154.1（完整原对象与有限零路）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C$，及在 $C\setminus\{0\}$ 上严格正的 $u\in V^*$。保留定义151.1的整个原域，明确写作

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x)\quad(p\in P,\ x\in K),\\
D_p=\{x\in K:T_p(x)=0\},\qquad S_p=P\cap D_p,\\
\mathcal A_p=\{e\in\mathcal F_p:e|_{D_p}=0\},\qquad
N_p=\{h\in C^*:h(p)=0\},\qquad L_p=\operatorname{span}_{\mathbb R}N_p,\\
P_{\rm s}=\{p\in P:\{s\in P:D_s=D_p\}=\{p\}\}.
\end{gathered}
\tag{XII154.1}
$$

本章假设完整 EB3、完整纯 PR，以及对整个原空间的 $\dim_{\mathbb R}V\le9$：每个整个 $D_p$ 是非退化仿射闭三球，且 $T_p(q)=T_q(p)$ 对全部 $p,q\in P$ 成立。最低值仍在全部原确认菜单中取，第二变量仍遍历全部原混态。记 $p\perp q$ 为 $T_p(q)=0$。这由原补效应对称，且反自反。令 $d_G$ 为这张实际零图的距离，不可达时取 $\infty$，并置

$$
\begin{gathered}
A_n(p)=\{q\in P:d_G(p,q)\le n\},\qquad A_0(p)=\{p\},\\
\Gamma(p)=\bigcup_{n\ge0}A_n(p),\qquad
B_\Gamma=\bigcup_{s\in\Gamma}D_s.
\end{gathered}
\tag{XII154.2}
$$

路径是有限条精确原零边，允许回走。零图分量不按环境拓扑定义；称包含于 $P_{\rm s}$ 的分量为单标签分量。辅助欧氏范数只用于直径、Hausdorff 距离、法向投影和行列式见证，不改变 $C,u$ 或原效应菜单。

本章的既有供应如下。

* 第147.1节所引原面分类给：每个 $D_p$ 是紧暴露极大真面，$\mathcal A_p\ne\varnothing$；全部非空真面只有原纯单点或整个排除球；$S_p=\partial_{\rm rel}D_p\cong S^2$、$D_p=\operatorname{conv}S_p$；不同完整球至多交于一个原纯点。
* [IX定理116.2、116.6][Q154IX]给 $P_{\rm s}\ne\varnothing$，且 $p\in P_{\rm s}\Rightarrow S_p\subset P_{\rm s}$。重复球恰成不交配对 $F,G$，有 $I(F)=S(G)$、$I(G)=S(F)$，其中 $I(F)=\{p:D_p=F\}$、$S(F)=P\cap F$；两球不与第三张不同完整球相交。其球缘给一个完全二部零图分量。
* 第151章在完整 EB3+PR 下给整个 $P$ 紧且拓扑连通、每个 $A_n(p)$ 紧，以及各 $B_\Gamma$ 两两不交并覆盖原边界，准确等式为 $B_\Gamma=\partial K\cap\operatorname{conv}\Gamma$。这里和下文的 $\partial K$ 都指 $\{u=1\}$ 中的边界。
* 推论147.8使本章维数恰为九，故 $\operatorname{aff}K=\{u=1\}$ 为八维，$\partial K\cong S^7$。定理147.1及命题147.6给每个实际 $p\in P_{\rm s}$ 的 $\mathcal A_p=\{e_p\}$、$\dim L_p=4$ 及完整原法向接口。引理147.5已给每个单标签根的实际二步紧四立方体；它是本章直接复用的供应，不另作一次四维块存在性证明。

以下不输入 $P_{\rm s}$ 紧、分量闭、全域 Inj、Conn、least、$\mathsf{CR}_{\rm s}$、共同 $\kappa$、非塌缩下界、全局球标架或矩阵表示。

### 154.2 紧纯域上的直径闭层与整球连续

**引理 154.2（原零球的闭图、直径层及全部可能极限）。** 在定义154.1的域中，令

$$
\mathcal D=\{(p,x)\in P\times K:x\in D_p\},\qquad
M_\varepsilon=\{p\in P:\operatorname{diam}D_p\ge\varepsilon\}
\quad(\varepsilon>0).
\tag{XII154.3}
$$

则 $\mathcal D$ 和每个 $M_\varepsilon$ 均紧，且 $p\mapsto D_p$ 在每个 $M_\varepsilon$ 上按原环境 Hausdorff 距离连续。若 $p_i\to p$，任何收敛的整球子列的极限只有两种：整个 $D_p$，或某个原纯单点 $\{r\}$，其中 $r\in S_p$。本引理不使用九维等号。

证明。若 $p_i\to p$、$x_i\in D_{p_i}$ 且 $x_i\to x$，在完整原菜单中取 $f_i\in\mathcal F_{p_i}$ 使 $f_i(x_i)=0$。紧 $\mathcal E$ 中取子列 $f_i\to f$，得到 $f(p)=1$、$f(x)=0$，故 $x\in D_p$。这证明 $\mathcal D$ 闭于紧 $P\times K$。若 $p_i\in M_\varepsilon\to p$，在每颗球上取距离至少 $\varepsilon$ 的两点，共同取极限并用闭图，极限两点仍在 $D_p$ 且距离至少 $\varepsilon$。所以 $M_\varepsilon$ 闭于紧 $P$。

在 $H=\ker u$ 固定辅助欧氏结构。写

$$
D_{p_i}=c_i+B_i\overline{\mathbb B}^3,
\qquad B_i:\mathbb R^3\longrightarrow H\text{ 单射}.
\tag{XII154.4}
$$

此处逐球任取轴，不要求连续选择。中心 $c_i\in K$，且 $c_i\pm B_it\in K$ 对每个单位 $t$ 成立，故 $\|B_i\|\le\operatorname{diam}K/2$。任一子列可再取 $c_i\to c$、$B_i\to B$，从而整球趋于 $E=c+B\overline{\mathbb B}^3$。闭图给 $E\subseteq D_p$。对每个 $t\in S^2$，点 $c_i+B_it$ 是原纯点；整个 $P$ 紧，遂有

$$
c+B S^2\subseteq P\cap D_p=S_p.
\tag{XII154.5}
$$

若 $\operatorname{rank}B$ 为一或二，则 $B(S^2)=B(\overline{\mathbb B}^3)$：对任何球内向量的像，在其原像仿射空间中取垂直于 $\ker B$ 的最短向量，再沿非零核方向补足到单位长度。因此整个非退化凸集 $E$ 都包含于 $P$。取 $E$ 中两不同点及其中点即违反原极点性。这排除了秩一、二。

若秩三，则 $E$ 与 $D_p$ 有相同的仿射三平面，且 $\partial_{\rm rel}E\subseteq S_p=\partial_{\rm rel}D_p$。它们必相等。确实，若 $E\ne D_p$，可取 $y\in\operatorname{ri}E$ 及 $z\in\operatorname{ri}D_p\setminus E$；线段从 $y$ 向 $z$ 穿出 $E$ 的点既在 $\partial_{\rm rel}E$，又在 $\operatorname{ri}D_p$，矛盾。秩零时则 $E=\{c\}$，由(XII154.5)有 $c\in S_p$。

在 $M_\varepsilon$ 内取极限，直径下界又排除秩零，故任何子列的再极限都是 $D_p$，即所称连续性。无直径下界时仍保留原纯单点塌缩，没有得到全局连续性或统一最小半轴。证毕。

本引理还说明 $P=\bigcup_{m\ge1}M_{1/m}$。在任一连续层上，完整球的中心 $c_p$ 及秩三形状算子 $A_p$ 连续；这一参数工具与第147.5节相同：支撑函数的奇偶部分确定中心，中心化支撑函数的平方经极化确定 $A_p$，且

$$
D_p=c_p+A_p^{1/2}\overline{\mathbb B}_H.
\tag{XII154.6}
$$

在任一层内一点附近，对 $\operatorname{im}A_p$ 用三个固定向量的像及 Gram—Schmidt 取局部连续正交标架 $W_p:\mathbb R^3\to H$，再令 $B_p=A_p^{1/2}W_p$。于是 $D_p=c_p+B_p\overline{\mathbb B}^3$，$B_p$ 连续且单射。这里仅有局部标架，不选择全局主轴。

### 154.3 三步凸包中的原七维边界开片与完整张成

**定理 154.3（单标签根的三步张成及重复根的准确反向）。** 对每个 $p\in P_{\rm s}$，存在原 $\partial K$ 中非空开集 $O_p$，使

$$
O_p\subseteq\operatorname{conv}A_3(p),\qquad
\operatorname{span}_{\mathbb R}A_3(p)=V.
\tag{XII154.7}
$$

因此 $A_3(p)$ 含九个线性无关的实际原纯点，其凸包含一个八维单纯形。反之，若 $p\notin P_{\rm s}$，其配对重复块 $F,G$ 满足

$$
A_2(p)=A_3(p)=\Gamma(p)=S(F)\sqcup S(G),\qquad
\dim\operatorname{span}_{\mathbb R}A_3(p)\le8.
\tag{XII154.8}
$$

特别地，在整个原 $P$ 上，三步张成 $V$ 当且仅当根为单标签。

证明。固定 $p\in P_{\rm s}$。紧 $S_p$ 被相对闭集 $S_p\cap M_{1/m}$ 覆盖；Baire 给某层的非空球面相对内部，可在其中取有非空球面内部的闭二盘。引理154.2给盘上的整球连续性，因此可直接使用引理147.5的局部标架及避开公共点 $p$ 的球帽乘积构造，得到该引理所供应的紧嵌入

$$
\Psi:[0,1]^4\hookrightarrow P_{\rm s}\cap A_2(p).
\tag{XII154.9}
$$

其像由实际两条原零边产生。闭集 $\Psi^{-1}(M_{1/m})$ 可数覆盖紧四立方体。Baire 定理给某层的非空相对内部；立方体内部稠密，故可取非空欧氏开四方块 $J$，其闭包包含于 $(0,1)^4$，且 $\Psi(\overline J)\subset M_{1/m}$。引理154.2给这整块上的球连续。进一步缩小 $J$，用(XII154.6)之后的局部标架，将 $D_{\Psi(t)}$ 写成 $c_{\Psi(t)}+B_{\Psi(t)}\overline{\mathbb B}^3$。

现在评价的是每颗完整球的真正相对内部：

$$
\mathscr E:J\times\mathbb B^3\longrightarrow\partial K,
\qquad
\mathscr E(t,z)=c_{\Psi(t)}+B_{\Psi(t)}z.
\tag{XII154.10}
$$

该映射连续且单射。同一标签内由 $B_{\Psi(t)}$ 单射；不同标签都在 $P_{\rm s}$，故球不同，而两张不同完整球的交只能是原纯点。每个 $\|z\|<1$ 的像都是该三球的非极点，因而是原混态，不能成为这种交点。源是七维欧氏开集，靶是原七维边界流形 $\partial K\cong S^7$。[Hatcher Theorem 2B.3][Q154H]逐坐标应用的区域不变性使

$$
O_p:=\mathscr E(J\times\mathbb B^3)
\tag{XII154.11}
$$

在整个原 $\partial K$ 中开放且非空。对每个 $r=\Psi(t)\in A_2(p)$，都有 $S_r\subseteq A_3(p)$，故 $D_r=\operatorname{conv}S_r\subseteq\operatorname{conv}A_3(p)$。于是得到(XII154.7)的第一项。这一步的维数是原四维标签块加完整三球内部的三维，恰为原边界的七维。

令 $W=\operatorname{span}_{\mathbb R}A_3(p)$，并取原球心 $c_p$。点

$$
x_0=(p+c_p)/2\in\operatorname{conv}A_1(p)
\subseteq\operatorname{conv}A_3(p)
\tag{XII154.12}
$$

位于 $\operatorname{ri}K$。否则过 $x_0$ 的真支撑面同时含 $p,c_p$；它含 $D_p$ 的相对内点 $c_p$，故含整个 $D_p$，由极大真面性必等于 $D_p$，却又含 $p\notin D_p$，矛盾。这也是定理151.5内点论证在本同根有限层中的使用。

从 $x_0$ 径向参数化，映射 $x\mapsto(x-x_0)/\|x-x_0\|$ 是 $\partial K$ 到 $H=\ker u$ 中单位 $S^7$ 的同胚；每条射线恰有一个边界交点，连续性由紧凸体和内点的小球邻域给出。若 $W\ne V$，因 $u|_W\ne0$，$W\cap H$ 是 $H$ 的真线性子空间。$O_p\subset W$ 且 $x_0\in W$ 使其径向像包含于 $S^7\cap(W\cap H)$。后者在 $S^7$ 中没有内部，却包含非空开集，矛盾。故 $W=V$。从张成集抽出九个线性无关点；它们均满足 $u=1$，因而仿射无关，给八维单纯形。此处同时使用边界开片和原内点，没有把“凸包包含内点”单独当作全空间张成的理由。

最后固定重复根。IX116.2给完全二部配对块：一步到达另一侧的全部球缘，两步到达本侧的全部球缘，且没有出块零边。因此(XII154.8)的集合等式成立。每个三球的线性张成都是四维，两者之和至多八维，小于原 $\dim V=9$，给准确反向。证毕。

### 154.4 分量可数性、双重 Borel 性与完全可度量性

**定理 154.4（单标签分量的可数分解）。** 单标签零图分量至多可数。$P_{\rm s}$ 及每个单标签分量 $\Gamma$ 都同时是原紧度量空间 $P$ 中的 $F_\sigma$ 和 $G_\delta$，并且都是 $\sigma$-紧 Polish 空间。这里不含这些分量在 $P$ 中闭或开的结论。

证明。先计数分量。对每个单标签分量 $\Gamma$，定理154.3给某个根 $p\in\Gamma$ 的非空边界开片 $O_p$。由定理151.5，

$$
O_p\subseteq\partial K\cap\operatorname{conv}\Gamma=B_\Gamma.
\tag{XII154.13}
$$

不同分量的 $B_\Gamma$ 不交。因此原第二可数边界中，单标签分量分别占有两两不交的非空开片。固定边界的可数基，每个这样的分量至少含一项非空基开集，且同一基开集不能属于两个分量；例如给分量指定可用基项的最小编号，便得向自然数的单射。记这些分量为 $\Gamma_j$，索引集至多可数。这里没有计数重复分量，也没有断言 $B_\Gamma$ 自身开放。

其次用有限实际零边见证处理重复集合 $R=P\setminus P_{\rm s}$。准确等价是

$$
\begin{aligned}
p\in R\quad\Longleftrightarrow\quad
&\exists s,q,r\in P:\quad p\ne s,\ q\ne r,\\
&p\perp q,\quad p\perp r,\quad s\perp q,\quad s\perp r.
\end{aligned}
\tag{XII154.14}
$$

正向取 $s\ne p$ 且 $D_s=D_p$，再在非退化 $S_p$ 上取两个不同原纯点 $q,r$。反向时 $D_p,D_s$ 共享不同的 $q,r$，点交规则迫 $D_p=D_s$，所以 $p$ 重复。反自反性还使这四点跨侧不能相同，故确为非平凡四周期。

对每个整数 $m\ge1$，在 $P^4$ 中令 $Z_m$ 由这四条零边及

$$
\|p-s\|\ge1/m,\qquad \|q-r\|\ge1/m
\tag{XII154.15}
$$

定义。零关系是闭关系：它是引理154.2的闭图在 $P^2$ 上的限制。故 $Z_m$ 紧，其 $p$ 坐标投影 $R_m$ 紧。有限见证中的两个正距离可用同一个 $1/m$ 下界，因而

$$
R=\bigcup_{m\ge1}R_m,\qquad P_{\rm s}=P\setminus R\text{ 是 }G_\delta.
\tag{XII154.16}
$$

每个单标签分量 $\Gamma_j=\bigcup_nA_n(p_j)$ 已由定理151.5给出紧层穷尽，故为 $F_\sigma$ 且 $\sigma$-紧。分量可数性又给

$$
P_{\rm s}=\bigcup_j\Gamma_j\text{ 是 }F_\sigma\text{ 且 }\sigma\text{-紧},
\qquad
\Gamma_j=P_{\rm s}\cap\left(P\setminus\bigcup_{k\ne j}\Gamma_k\right)
\text{ 是 }G_\delta.
\tag{XII154.17}
$$

所有紧层均是原 $P$ 中的实际紧集，不把相对闭集误称为原紧集。

为明确完全可度量性，在本证明内展开所需的标准描述拓扑事实。若 $X=\bigcap_nU_n\subset P$，各 $U_n$ 在 $P$ 中开，令 $\delta_n(x)=\operatorname{dist}(x,P\setminus U_n)>0$ 对 $x\in X$ 成立；空补集时取 $\delta_n=1$。映射

$$
x\longmapsto\bigl(x,(1/\delta_n(x))_{n\ge1}\bigr)
\quad\text{从 }X\text{ 到 }P\times\mathbb R^{\mathbb N}
\tag{XII154.18}
$$

是到像的同胚，且像闭。确实，若像中序列在乘积中收敛，第一坐标趋于某 $x\in P$；任一 $\delta_n(x)=0$ 都会使对应倒数发散，与该坐标的有限极限矛盾。故 $x\in X$，全部极限坐标正是 $1/\delta_n(x)$。紧度量 $P$ 完备，$\mathbb R^{\mathbb N}$ 的通常可数乘积完备度量与 $P$ 的度量合成完备可分乘积度量；例如各实坐标差取 $\min\{1,|a_n-b_n|\}$ 后以 $2^{-n}$ 求和。闭像遂完备可度量，且第二可数性给可分性。于是 $P$ 的每个 $G_\delta$ 子集为 Polish，特别用于 $P_{\rm s}$ 和各 $\Gamma_j$。它们以及各自非空开子空间都是 Baire 空间。证毕。

### 154.5 任意相对开集中的四维图与四步实际接力

**定理 154.5（稠密的相对四维几何）。** 令 $X=P_{\rm s}$，或令 $X$ 为任意一个单标签零图分量。对每个非空 $X$-开集 $U$，存在非空 $X$-开集 $A\subset U$，同胚于 $\mathbb R^4$ 的开方块，并满足：其 $X$ 中闭包紧且包含于 $U$；$r\mapsto D_r$ 在此闭包上连续；有同一个实际 $a\in U$，使每个 $x\in A$ 都有两步精确路径 $a\perp q_x\perp x$，且任意 $x,y\in A$ 有

$$
x\perp q_x\perp a\perp q_y\perp y.
\tag{XII154.19}
$$

特别地，$A\subseteq A_4(x)$ 对每个 $x\in A$ 成立。所有这类图的并 $\mathcal R_X$ 是 $X$ 中稠密开集，为第二可数四维拓扑流形，且整球映射在 $\mathcal R_X$ 上连续。这些图只相对于 $X$ 开。

证明。由定理154.4，$X$ 是 Polish，故任意非空 $X$-开集 $U$ 是 Baire。将通常外法向定义在原八维方向空间 $H=\ker u$ 上。第147.6节给准确的锥同构

$$
N_x\longrightarrow\mathcal N_K(x),\qquad h\longmapsto-h|_H.
\tag{XII154.20}
$$

核为零，因为在 $H$ 上零的 $h$ 是 $u$ 的倍数，而 $h(x)=0$ 消去该倍数。反向对外法向 $v\in H^*$ 定义 $h(z)=-v(z-u(z)x)$，支撑不等式保证它在整个 $C$ 非负且零于 $x$。因此法向张成维数没有加一或减一；定理147.1给每个 $x\in X$ 的通常法向张成维数恰为四。

对原八维凸体精确取 [SAME_READBACK引理128.2及其证明][Q154SR] 的 $n=8,k=4$。它给可数紧层 $L_j\subset\partial K$ 覆盖这些点，且每层有连续单射正交投影

$$
\pi_j:L_j\longrightarrow E_j^\perp\cong\mathbb R^4,
\qquad \dim E_j=4,
\tag{XII154.21}
$$

逆还满足 $2/\sqrt3$ 的 Lipschitz 界。这里所用单射性来自该引理证明的(Q128.7)—(Q128.8)，不从有限 Hausdorff 测度反推。$L_j$ 不必包含于 $X$。准确闭覆盖是 $U=\bigcup_j(U\cap L_j)$，各项只要求在 $U$ 中相对闭。Baire 给某个非空 $X$-开集

$$
O\subseteq U\cap L_j.
\tag{XII154.22}
$$

取 $a\in O$。需要在 $O$ 内的实际二步块，因而使用引理147.5证明中的环境局部化，而非仅使用其抽象存在结论。写 $O=X\cap W$，其中 $W$ 在原仿射环境中开。引理147.4在实际 $S_a$ 上给一个闭二盘 $Q'$，有非空球面内部，且 $q\mapsto D_q$ 在其上连续；第147.5节的形状算子和局部标架给其中某个内点 $q_0$ 附近的连续 $c(q),B(q)$。由零对称，全部这些 $S_q$ 都含同一个原纯点 $a$。

在 $S_{q_0}\setminus\{a\}$ 中先取充分靠近 $a$ 的一点，再取小紧二维球帽，使整帽在 $W$ 内且避开 $a$。联合连续性、帽的紧性及 $W$ 开性允许缩小 $q_0$ 周围的二维底盘，使全部移动球帽仍在 $W$ 内且避开 $a$。底盘与帽各参数化为闭方盘，得到第147.5节的同一乘积构造

$$
\Theta:[0,1]^2\times[0,1]^2\hookrightarrow O,\qquad
\Theta(b,t)\in S_{q(b)},\quad q(b)\in S_a.
\tag{XII154.23}
$$

固定 $b$ 时单射；不同 $q(b)$ 都单标签，其球都含 $a$，故点交规则使它们只能交于 $a$，而全部帽避开该点，遂跨底盘也单射。紧源保证它是到像的同胚。所有像点都在 $X$，因为 $X$ 沿实际零邻点封闭；这对 $P_{\rm s}$ 由 IX116.6给出，对零图分量由定义给出。像又在 $W$ 中，故确实在 $O$ 中。每个像点同时带有实际两步路径 $a\perp q(b)\perp\Theta(b,t)$。这没有把新的纯点填入原 $P$。

再将紧四立方体按闭集 $\Theta^{-1}(M_{1/m})$ 覆盖。Baire 及立方体内部稠密性给欧氏开四方块 $J$，其闭包仍在立方体内部，且 $\Theta(\overline J)\subset M_{1/m}$。引理154.2给这个闭块上的整球连续性。连续单射 $\pi_j\Theta:J\to\mathbb R^4$ 由区域不变性给开像 $\Omega$。由于 $\pi_j$ 在整个 $L_j$ 上单射，而 $O\subset L_j$，有准确等式

$$
A:=\Theta(J)=O\cap\pi_j^{-1}(\Omega).
\tag{XII154.24}
$$

右边的投影也可视为环境连续线性投影的限制，故 $A$ 是 $X$-开集；$\Theta|_J$ 给所需四维图。其 $X$ 中闭包恰为紧 $\Theta(\overline J)\subset O\subset U$，整球在此闭包上连续。将 $x=\Theta(b,t)$ 对应的 $q_x=q(b)$ 代入，即得(XII154.19)；底盘坐标还使 $q_x$ 在这张图内连续，无需全局选择器。

每个非空 $X$-开集含这样的图，因此其总并 $\mathcal R_X$ 稠密且开。它继承 $X\subset P$ 的 Hausdorff 与第二可数性，每点有四维欧氏邻域，故为四维拓扑流形。整球映射在每张开图上连续，因而在总并上连续。图的直径下界可以逐图不同。全部证明只给 $X$ 的相对拓扑，没有给 $P$ 中的开邻域，亦没有给每个 $X$ 中点都处在 $\mathcal R_X$。证毕。

### 154.6 有限三步见证在重复极限处的共同退化

**定理 154.6（行列式上半连续与整层单向逼近）。** 在九维原 $V$ 上固定非零交替九线性体积形式 $\omega$，令

$$
\eta(p)=\max_{x_1,\ldots,x_9\in A_3(p)}
|\omega(x_1,\ldots,x_9)|.
\tag{XII154.25}
$$

最大值达到，$\eta$ 在整个 $P$ 上上半连续，且

$$
\eta(p)>0\quad\Longleftrightarrow\quad p\in P_{\rm s}.
\tag{XII154.26}
$$

若任意原标签列 $p_i\to p\notin P_{\rm s}$，记其重复块 $\Gamma(p)=S(F)\sqcup S(G)$ 及 $W_p=\operatorname{span}(F\cup G)$，则

$$
\begin{gathered}
\eta(p_i)\longrightarrow0,\\
\sup_{x\in A_3(p_i)}\operatorname{dist}(x,\Gamma(p))\longrightarrow0,
\qquad
\sup_{x\in A_3(p_i)}\operatorname{dist}(x,W_p)\longrightarrow0,
\qquad \dim W_p\le8.
\end{gathered}
\tag{XII154.27}
$$

这是整个有限可达层的单向逼近，不声称相反方向的 Hausdorff 逼近。

证明。对任意固定 $n$，联合可达关系

$$
G_n=\{(p,x)\in P^2:x\in A_n(p)\}
\tag{XII154.28}
$$

是闭的：每个长度 $k\le n$ 的路径空间由紧 $P^{k+1}$ 中的闭零边条件定义，取两端点投影再作有限并仍紧；$k=0$ 给对角线。这是定理151.5紧层论证同时保留起点的形式。

紧 $A_3(p)^9$ 和连续 $\omega$ 给最大值达到。(XII154.26)正是定理154.3的张成等价。对 $p_i\to p$，沿实现 $\limsup_i\eta(p_i)$ 的子列取达到最大值的九元组。共同紧性允许九个坐标同时收敛；$G_3$ 闭保证每个极限点在 $A_3(p)$。体积形式连续，给

$$
\limsup_i\eta(p_i)\le\eta(p).
\tag{XII154.29}
$$

重复根的 $\eta(p)=0$，结合非负性得第一个极限。若(XII154.27)第二项失败，可取固定 $\varepsilon>0$ 及 $x_i\in A_3(p_i)$，使它们到紧 $\Gamma(p)$ 的距离至少为 $\varepsilon$。取 $x_i\to x$，闭 $G_3$ 却给 $x\in A_3(p)=\Gamma(p)$，矛盾。最后 $\Gamma(p)\subset W_p$，而 $\operatorname{span}\Gamma(p)=\operatorname{span}(F\cup G)$，故第三项及维数界随之成立。证毕。

此退化允许每个 $p_i$ 本身仍为单标签，因而其三步见证各自张成原 $V$，但所有九点体积共同趋零。上半连续性没有给这些体积正的统一下界。命题151.6中的块外标签积聚若含单标签子列，该子列必须服从(XII154.27)；块外标签本身不能自动认作单标签。

### 154.7 九个实际纯输入的线性检验与共同恒等式消费者

**推论 154.7（固定九基输入的条件应用）。** 固定任意实际 $a\in P_{\rm s}$，可一次选定九个 $x_1,\ldots,x_9\in A_3(a)$ 构成原 $V$ 的基。对任意实向量空间 $Z$ 及任意两个原实线性映射 $F,G:V\to Z$，有

$$
F=G\quad\Longleftrightarrow\quad
F(x_j)=G(x_j)\quad(1\le j\le9).
\tag{XII154.30}
$$

特别地，令 $Q=\Gamma(a)\subset P_{\rm s}$。若另已证明存在同一个实数 $\kappa<2$，使对所有 $p\in Q$、所有 $q\in S_p$ 及全部这九个固定输入都有

$$
e_q(x_j)+e_{q^\sharp}(x_j)
=\kappa\bigl(u(x_j)-e_p(x_j)\bigr),
\qquad q^\sharp=2c_p-q,\quad 1\le j\le9,
\tag{XII154.31}
$$

则准确满足本卷定理149.2的全原空间恒等式前件，故该定理给 $Q=P_{\rm s}=P$、$\kappa=1$ 及同原锥同原单位的复三能级表示。

证明。定理154.3给这九个实际原纯基输入；线性差 $F-G$ 在一组基上为零恰等于在整个原 $V$ 上为零。$Q$ 非空且沿实际零邻点封闭，且由 IX116.6有 $Q\subset P_{\rm s}$，所以第147章在 $Q$ 的每点给唯一 $e_p$。球内对径 $q^\sharp$ 仍在 $S_p\subset Q$。对每一对实际 $p,q$，将(XII154.30)用于两边线性泛函，便把(XII154.31)提升为整个原 $V$ 上的

$$
e_q+e_{q^\sharp}=\kappa(u-e_p)
\quad(p\in Q,\ q\in S_p).
\tag{XII154.32}
$$

这与定理149.2的(149.3)—(149.4)逐量词相同，故可直接消费。证毕。

这里的有限化只缩减每个线性恒等式的输入检验集；$p,q$ 的全体量词及同一个 $\kappa$ 均保留。三步张成本身没有证明(XII154.31)，也没有制造共同 $\kappa$。完整菜单 minimum $T_p$ 未先被证明线性，因而不得把九点准则直接用于 $T_p$ 与另一函数的比较。这个消费者说明原线性关系的实际用途，不是一条新取得的三元确认恒等式。

### 154.8 已付分类入口下的同一个表示与独立实际合同

若另已支付全局 Inj，准确消费 [XI定理145.2][Q154XI] 的完整 EB3+Inj+原九维分支；若另已支付 Conn，可消费同一定理的 Conn 分支，或 [XI定理150.5][Q154XI] 的完整 EB3+PR+Conn 分支。若另已支付本卷定义149.1的 $\mathsf{CR}_{\rm s}$，则消费定理149.3；若另已支付(XII154.31)的全部前件，则用推论154.7及定理149.2。只有在这些合法入口之一成立后，才有同一个实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\operatorname{PSD}_3)=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XII154.33}
$$

原锥、原单位、全部原混态和原菜单均不替换。完整静态字典直接引用 XI条件应用145.9及本卷推论149.11，不另立删减版字典。为明确最容易混淆的全菜单量词，取 $v^\ast v=1$，令 $P_v=vv^\ast$、$Q_v=I_3-P_v$、$p_v=\Phi(P_v)$、$f_A(\Phi X)=\operatorname{Tr}(AX)$，则同一个 $\Phi$ 给

$$
\begin{gathered}
\mathcal E=\{f_A:0\preceq A\preceq I_3\},\\
\mathcal F_{p_v}
=\{f_{P_v+B}:B=Q_vBQ_v,\quad0\preceq B\preceq Q_v\},\\
T_{p_v}(\Phi\rho)=v^*\rho v
\quad\text{对每个 }\rho\succeq0,\ \operatorname{Tr}\rho=1,\\
D_{p_v}=\Phi\{\rho\succeq0:\operatorname{Tr}\rho=1,\ \rho v=0\}.
\end{gathered}
\tag{XII154.34}
$$

这些是所引完整字典的条件消费。其菜单计算保留所有效应：$I_3-A\succeq0$ 且 $v^\ast Av=1$ 给 $(I_3-A)v=0$，Hermitian 性消去交叉块，故全部确认恰为上述 $P_v+B$；对每个正矩阵输入，$\operatorname{Tr}(B\rho)\ge0$，因此同一菜单中的 $B=0$ 给 least 和每个原混输入的已达 minimum。菜单本身仍非单点。正性又给 $v^\ast\rho v=0\Longleftrightarrow\rho v=0$，所以最后一行是整个排除球，包含全部混态。相同双射保持全部零、次归一和任意非负质量；零质量锥元只有零，不给它强行定义归一态。

其余全部静态对应，包括全纯域 $\mathbb{CP}^2$、整球纯缘 $\mathbb{CP}^1$、Bloch 三球、复共轭内积的纯比较 $|v^\ast w|^2$、原三角、全 Pair、全部有限数学 POVM、谱、共同尺、Jordan 结构及球心配方，均沿这同一个 $\Phi$ 使用原完整字典。它们不是从三步张成直接推出的。这里的 $v^\ast$ 是共轭转置，不能去掉共轭而改为实双线性式。

无论是否另已触发分类，实际物理量词完整保留 [XI第145.9节][Q154XI]、本卷第149.11节及其所引 SAME_READBACK SECTION127.10 的独立合同，准确包括下列范围。

共同来源域 $\Omega$、未知 ingress、同一个原装饰元组、全部同源及同中点实现、共同读回、全实关系、原概率像紧性、全测试表、零／单位／补／有界倍增、零及不等质量、两尺度等式和每个原资格输入分别承担原前件。静态复射线及数学叠加不提供实际相干制备、相位参考、可调用门、来源采用或权限。

对每个有限 $N\ge1$，仍须另供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N$、全部 $P_N$ 及全效应。对每个实际分割 $a+b=N$，保留 $C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b$、同一产品配对、全部因子置换及逆、规范重括号与指定运输。全纠缠输入的联合 minimum、低二份 Jordan 桥、实际自复合及复型选择、实际三份资源和其锥成员身份，仍各有原前件；高阶排除集没有被规定为单体三球。

对每个输入输出份数和每个有限旁观系统，仍在同一个共同输入上要求全旁观正性，包括每个纠缠输入。完整实际有限层级及表示齐备后，才用原 Choi 桥识别 CP。TP／TNI、逐分支及同族总预算都对每个原输入承担。数学 CP-TNI 映射成为实际事件还需事件饱和和原实现；同族仪器仍需实际探针、接线、共同预算、记录、粗粒化、输出与校准。只在严格正质量分支条件归一，零质量分支不强定条件态；Lüders 更新另保锐效应、接受态中性及输出校准合同。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字和旧 support、每个中间切口、全部合法未来、terminal futures、细标签粗归组及记录后的条件未来，均保持原量词。有限步零图路径不支付这些实际操作、记录或未来合同。

物理钟、实际连续动态来源、时间单位、Hamiltonian、能量识别及标定、数值 $\hbar$、时空与物理空间维数分别独立供应。另给实际复酉时间实现后，才写

$$
U_t=\exp(-\mathrm i tH/\hbar),\qquad H=H^*,
\qquad\rho_t=U_t\rho U_t^*.
\tag{XII154.35}
$$

九维原实载体、四维相对纯图、三维排除球和三步线性张成都不指定物理空间或物理时间。

### 154.9 几何解释、归属与尚未支付的桥梁

原纯点、全部混态、每张允许测试尺始终属于同一个原状态体。一次零边表示一把原确认尺在一端读一、另一端读零；PR 交换的是两端各自整个菜单的最低纯比较值。它已使全纯域紧。于是移动球皮的每个极限点仍是原纯点：若一颗球只压成非退化线段或二维椭圆盘，实心极限的每一点都会由原球皮逼近，连混态中点也被迫成为纯点。这个矛盾排除了一维、二维扁化，但仍允许整颗球缩成一个原纯点。直径闭层排除的是最后这种缩点，因而在每层上保留整颗正确的原三球。

从单标签根出发，引理147.5供应两步内的一块四维实际纯点载体。把这块载体按球直径分层，Baire 使其中一小块有连续的完整三球族。接着让每个标签背后的三维实心内部展开：不同单标签球只能在原纯点相交，实心混态内部不会相撞，因此四加三给原七维边界中的连续单射。区域不变性把它变成整个原边界的一块开片。三步纯点的凸包包住这片，且已经含原内点；从该内点径向看，真线性子空间无法容纳球面开片，所以三步实际纯点必须张满整个原九维空间。

重复块只有两张三球的球皮，所有有限零路都困在这个完全二部块内，线性维数至多八。这给单标签和重复标签的准确有限见证区别。若单标签根趋近重复块，原三步见证不能保留统一厚度：不仅任何最大九点体积趋零，整个三步层到接收块的最大距离也趋零。各个发送根仍可各自张满九维；它们共同变薄并不自相矛盾。

不同单标签分量各在原边界中占有不交开片，第二可数性使这些分量至多可数。重复性又由四个实际纯点和四条精确零边见证，两个非零距离把见证分成可数紧层；所以单标签域是 $G_\delta$。分量的紧可达层和上述可数分量分解再给 $F_\sigma$、$\sigma$-紧性与完全可度量性。原四维法向的紧投影层随后使每个非空相对开集都含真正的四维相对开图；图内任意两点可经同一构造根用四条实际零边相接。

这些关系仍不等于全域接线。$A_3(p)$ 张成 $V$ 不意味着 $A_3(p)=P$，不意味着 $\Gamma(p)=P$，也不意味着 $\operatorname{conv}A_3(p)=K$。$\sigma$-紧 Polish 分量不必闭或紧，其闭包也未被证明留在 $P_{\rm s}$。定理154.5的开图只相对于 $X=P_{\rm s}$ 或某个单标签分量开放，不能直接用作定理151.3的全原 $P$-邻域，更没有支付 $\mathsf N_2$。跨直径层的单点塌缩、跨分量的整球并合及(XII154.27)的有限见证退化仍未排除。

因此，完整 EB3+PR 到 Conn、全域 Inj 或单标签球心互易 $\mathsf{CR}_{\rm s}$ 的原桥梁仍未证明；加入本章整个原空间九维上界后，这些箭头也没有在本章付清。共同 $\kappa$ 与(XII154.31)的实际成立仍是推论154.7的额外前件，least、同锥同单位表示和全部原三角不从张成单独产生。没有由此证明原候选的独立假设数减少，也没有给满足完整原关系的反模型来证明这些条件独立。

本章承重连接归为 `repo-derived`：直径闭层的整球连续、原边界开片到三步张成、单标签分量可数性及其描述拓扑、任意相对开集内的局部化四维图、重复极限的有限见证共同退化。二步紧四立方体、完整原面分类、重复块、单标签零邻封闭、原纯紧性、四维法向及既有条件分类均按所列准确来源复用。有限维紧性、Baire 定理、连续正半定平方根、局部标架、紧度量空间的 $G_\delta$ 完全可度量性与区域不变性是成熟中间工具；所需描述拓扑事实已在定理154.4证明内展开。[Hatcher Theorem 2B.3][Q154H]的前件始终是同维欧氏开源上的连续单射，七维边界版本逐坐标应用，四维投影版本只在先取得的开四方块上应用。法向层精确使用 SAME_READBACK128.2证明中的可数紧投影层，参数是 $n=8,k=4$，不调用只给几乎处处结论的可求长性替代。此处不主张文献优先权或全球新颖性。

[Q154IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.1—114.4：原全效应、PR下严格暴露与全纯域紧性；IX116.1—116.2：完整原面、点交和配对重复块；IX116.6：单标签存在及其零邻封闭。"
[Q154SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "引理128.2及其证明(Q128.7)—(Q128.8)：有非空内部的n维紧凸体的全点可数紧覆盖，每层向R^(n-k)连续单射投影；本章取n=8,k=4，层不必只含原纯点。"
[Q154XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "XI145.2：EB3+Conn或Inj+整个原V九维的同锥同单位分类；条件应用145.9：同一个Phi下的全部静态字典和完整菜单；第145.9节：独立实际物理合同；XI150.5：完整EB3+PR+Conn的least与同原分类。"
[Q154H]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology, Theorem 2B.3，印刷页172：U在R^n中开且h:U→R^n连续单射，则h(U)在R^n中开。"

## 追加锚（本行以下为增补区）

## 155. 逐张确认的整球下界与真实零三角

**定义 155.1（完整原域与确认的整球下界）。** 保留定义151.1、152.1的全部原 $V,C,u,K,P,\mathcal E,\mathcal F_p,T_p,D_p,S_p,\mathcal A_p,B_p,\Delta_p,\mathscr L(p)$，假设完整 EB3 与字面纯 PR。全部混输入和确认菜单均不缩减，所有 minimum 仍在原域达到。对固定原纯标签 $p$ 定义

$$
\begin{aligned}
\mathsf{MD}(p):\quad
&\forall f\in\mathcal F_p\ \exists e\in\mathcal A_p:
\quad f-e\in C^\ast,\\
\mathsf{MD}:\quad&\forall p\in P:\mathsf{MD}(p).
\end{aligned}
\tag{XII155.1}
$$

下界效应允许随同一张 $f$ 改变；不要求一个 $e$ 对全部 $f$ 通用。记 $I(F)=\{a\in P:D_a=F\}$，$c_p$ 为完整 $D_p$ 的球心。$I(D_p)=\{p\}$ 表示球的原标签唯一，与 $\mathcal A_p$ 单点性是不同条件。

**定理 155.2（逐张下界直接支付单标签、三角与共同预算）。** 对固定原纯 $p$，条件 $\mathsf{MD}(p)$ 等价于

$$
T_p(x)=B_p(x)\qquad(x\in K).
\tag{XII155.2}
$$

任一成立时，有 $I(D_p)=\{p\}$；对每个 $q\in S_p$，存在唯一共同零邻点

$$
r=2c_p-q,\qquad D_p\cap D_q=\{r\}.
\tag{XII155.3}
$$

而且对每张 $b\in\mathcal A_q$，都存在 $e\in\mathcal A_p$、$c\in\mathcal A_r$，使

$$
e+b+c=u.
\tag{XII155.4}
$$

此外 $\beta_{D_p}=1$，满刻度沿 $p$ 的全部有限原零路传播。没有预设 $\mathcal A_p$ 单点、共同 least、全域 Inj 或 Conn。

证明。由 $\mathcal A_p\subseteq\mathcal F_p$，始终有 $T_p\le B_p$。若 $\mathsf{MD}(p)$ 成立，每张 $f$ 都有一个原正序下界 $e\in\mathcal A_p$，故 $f(x)\ge e(x)\ge B_p(x)$，得到(XII155.2)。反向准确复用153.3证明最后的紧集加闭锥严格分离：该步骤仅用全部混输入的等号，不用 $\dim\operatorname{aff}\mathcal A_p\le1$。具体而言，若 $f\notin\mathcal A_p+C^\ast$，严格分离的向量必属 $C\setminus\{0\}$，以原 $u$ 归一化便给 $f(x)<B_p(x)=T_p(x)$，矛盾。

先排除 $p$ 的重复标签。若 $I(D_p)$ 不止一个点，[IX116.2][Q155IX]给实际孤立配对球 $F=D_p,G$，满足

$$
I(F)=S(G),\qquad I(G)=S(F),\qquad F\cap G=\varnothing.
\tag{XII155.5}
$$

$\mathrm{PR}$ 已支付严格纯暴露。[X124.7、124.9][Q155X]遂在指定的原纯点 $p\in S(G)$ 产生实际序列

$$
a_i\to q_0\in S(F),\qquad D_{a_i}\xrightarrow H\{p\}.
\tag{XII155.6}
$$

将 [X126.3][Q155X] 用在这次实际塌缩的接收标签 $q_0$、落点 $p$ 上，其补效应给

$$
h\in\mathcal F_p,\qquad Z_K(h)=\{q_0\}.
\tag{XII155.7}
$$

该来源不要求 Inj 或 $P_0$。由 $\mathsf{MD}(p)$ 取 $e\in\mathcal A_p$，使 $k=h-e\in C^\ast$。则 $k(p)=k(q_0)=0$，且 $k\ne0$；否则 $h=e$，其原零面不可能同时是单点和完整三球。完整真面分类使 $Z_K(k)=D_t$ 对某个原纯 $t$ 成立。因 $p,q_0\in D_t$，零对称给 $t\in D_p\cap D_{q_0}$；但 $D_p=F,D_{q_0}=G$ 不交，矛盾。因此 $I(D_p)=\{p\}$。

现在任取 $q\in S_p$、$b\in\mathcal A_q$。零对称给 $p\in D_q$，故 $u-b\in\mathcal F_p$。再由逐张下界取 $e\in\mathcal A_p$，使

$$
k=u-b-e\in C^\ast,\qquad k(p)=k(q)=0.
\tag{XII155.8}
$$

若 $k=0$，则 $e=u-b$ 在整个 $D_q$ 恒一。对每个 $t\in S_q$，$e(t)=1$ 且 $e|_{D_p}=0$，于是 $D_p\subseteq D_t$。完整球为极大真面，故 $D_t=D_p$。整个 $S_q$ 含多个原纯点，这与 $I(D_p)=\{p\}$ 矛盾。因此 $k\ne0$。

原真面分类再次给 $Z_K(k)=D_r$，并使 $p,q,r$ 两两原零正交。准确消费 [IX114.8][Q155IX]，得到(XII155.3)、$\beta_{D_p}=1$ 及满刻度的零边传播。又 $r\in D_p\cap D_q$，故 $e(r)=b(r)=0$、$k(r)=1$；由 $0\le k=u-e-b\le u$，有 $k\in\mathcal A_r$。取 $c=k$ 得(XII155.4)。证毕。

(XII155.4)是整个原效应区间内的数学单位分解，没有预付实际三结果仪器。证明的两次下界可以使用不同的 $e$；没有把 $\forall f\exists e$ 换成 $\exists e\forall f$。

**定理 155.3（二维确认族的纯输入极大差距与真实三角）。** 设固定原纯 $p$ 满足 $\dim\operatorname{aff}\mathcal A_p\le2$。则对任意原 $x\in K$、$f\in\mathcal F_p$，存在同一个原纯 $s\in P$，使

$$
B_p(s)-f(s)\ge B_p(x)-f(x),\qquad
\max_{s\in P}\Delta_p(s)=\max_{x\in K}\Delta_p(x).
\tag{XII155.9a}
$$

因而若

$$
T_p(s)=B_p(s)\quad(s\in P),
\tag{XII155.9}
$$

则定理155.2的全部结论成立。特别地，$|\mathscr L(p)|\ge2$ 配合该仿射维数条件，已足以使 $p$ 进入真实三角并使其整个有限零路分量满刻度。反向，

$$
\beta_{D_p}>1,\quad \dim\operatorname{aff}\mathcal A_p\le2
\quad\Longrightarrow\quad
\exists s\in P:\Delta_p(s)>0,
\qquad |\mathscr L(p)|\le1.
\tag{XII155.10}
$$

证明。固定 $e_0\in\mathcal A_p$，记 $W_p=\operatorname{span}(\mathcal A_p-e_0)$。其维数至多二；保持全部这些确认差值读数，取原紧凸切片

$$
Q_x=\{z\in K:h(z)=h(x)\ (h\in W_p)\}.
\tag{XII155.9b}
$$

在 $Q_x$ 上最小化原仿射读数 $f-e_0$，取其极小面的一个极点 $s$；该面是切片的面，故 $s\in\operatorname{ext}Q_x$。153.3证明内的切片论证适用：原内部混点有至少四维切空间，原混边界点位于三维完整球的相对内部，至多两张独立读数均留出非零双向扰动。因此每个切片极点都是原纯点。对全部 $e\in\mathcal A_p$，同一个 $s$ 给

$$
\begin{aligned}
e(s)-f(s)
&=(e-e_0)(x)-(f-e_0)(s)\\
&\ge(e-e_0)(x)-(f-e_0)(x)=e(x)-f(x).
\end{aligned}
\tag{XII155.9c}
$$

对整个 $\mathcal A_p$ 取 minimum，即得第一项；对每个 $x$ 选达到 $T_p(x)$ 的原 $f$，便有 $\Delta_p(s)\ge\Delta_p(x)$。$P$ 紧，$T_p,B_p$ 连续，故两侧最大值达到且相等。这是保持两张差值、向下优化另一张读数，没有要求三张读数同时匹配。

纯行相等遂支付全部原混输入的(XII155.2)，再用定理155.2。两落点的纯行等号由152.4供应。对(XII155.10)，若所有纯差距均零，前述推导将给单位预算；存在纯严格差距后，152.3限制全部实际塌缩落点至多一个。证毕。

本条没有断言非退化线段确认族实际存在，也没有证明两端相同。153.3的反链结论仍保留：非退化线段没有共同 least；此处取得三角的路径已不要求先取得它。

**定理 155.4（仅混态差距的完整三球与三维斜率包围）。** 固定原纯 $p$，假设 $T_p(s)=B_p(s)$ 对全部原纯 $s$ 成立。若某个原混态 $x$ 的 $\Delta_p(x)$ 严格正，则存在实际完整球 $F=D_t$、$y\in\operatorname{ri}F$ 及同一张达到 $T_p(x)$ 的原 $f\in\mathcal F_p$，满足

$$
0<\Delta_p(x)\le\delta_y:=B_p(y)-f(y)\le\Delta_p(y),\qquad
p\notin F,\qquad F\cap D_p=\varnothing.
\tag{XII155.11}
$$

令 $U_F=\operatorname{span}(F-F)$。对任意 $e_0\in\mathcal A_p$，还必有

$$
\dim\operatorname{span}
\{(e-e_0)|_{U_F}:e\in\mathcal A_p\}=3.
\tag{XII155.12}
$$

更定量地，任取球图 $b_F:\overline B^3\to F$，写 $y=b_F(z_0)$；定义原确认差的球内斜率 $\ell_e\in\mathbb R^3$ 为

$$
(e-f)(b_F(z))=(e-f)(y)+\ell_e\cdot(z-z_0),\qquad
\Sigma_F=\{\ell_e:e\in\mathcal A_p\}.
\tag{XII155.13}
$$

则这个紧凸斜率像包含一个以零为球心的实心三球：

$$
\frac{\delta_y}{1+\|z_0\|}\,\overline B^3\subseteq\Sigma_F.
\tag{XII155.14}
$$

证明。取原混态 $x$ 及达到 $T_p(x)$ 的原 $f$，固定任意 $e_0\in\mathcal A_p$。仍在保持全部 $W_p=\operatorname{span}(\mathcal A_p-e_0)$ 读数的原切片 $Q_x$ 上，取 $f-e_0$ 的极小面的一个极点 $y$。与(XII155.9c)完全相同的计算给

$$
B_p(y)-f(y)\ge B_p(x)-f(x)=\Delta_p(x)>0.
\tag{XII155.15}
$$

全部纯行相等使 $y$ 非纯。又 $\operatorname{span}D_p$ 四维，$e_0|_{D_p}=0$、$e_0(p)=1$，故 $\operatorname{span}(D_p\cup\{p\})$ 五维。全部 $W_p$ 消失于此空间，于是

$$
\dim W_p\le\dim V-5<\dim\operatorname{aff}K.
\tag{XII155.16}
$$

原内部点存在保持这些读数的非零双向扰动，不可能为切片极点。故 $y$ 为原混边界点，其最小原面为实际完整三球 $F$，且 $y\in\operatorname{ri}F$。

先证(XII155.14)。任取单位向量 $v$，沿 $z_0-tv$ 到达原球缘 $w$，其中 $0<t\le1+\|z_0\|$。纯行相等和 minimum 达到给某张 $e_w\in\mathcal A_p$ 满足 $(e_w-f)(b_F(w))\le0$。另一方面 $(e_w-f)(y)\ge\delta_y$，故 $\ell_{e_w}\cdot v\ge\delta_y/t\ge\delta_y/(1+\|z_0\|)$。紧凸集 $\Sigma_F$ 在每个单位方向的支撑值均不小于该正数，支撑半空间刻画遂给(XII155.14)。其仿射包络三维，而斜率差正是 $e-e_0$ 的限制，得到(XII155.12)，特别有 $\dim\operatorname{aff}\mathcal A_p\ge3$。

若 $p\in F$，在球图中写 $p=b_F(v)$。每张 $e\in\mathcal A_p$ 的 $1-e|_F$ 非负且零于球面点 $p$，遂有 $e(b_F(z))=1-\alpha_e(1-v\cdot z)$，$\alpha_e\ge0$。其斜率差全在同一轴上，违反(XII155.12)。故 $p\notin F$。

若 $F=D_p$，全部 $e|_F=0$，同样违反该秩条件。若两个球不同且相交，完整原面分类使交集为一个原纯点 $q=b_F(v)$。每张 $e|_F$ 非负且零于 $q$，遂为 $\alpha_e(1-v\cdot z)$，斜率差仍至多一维，矛盾。故 $F\cap D_p=\varnothing$。原 $y,f$ 满足(XII155.15)，即得(XII155.11)。证毕。

在这个证明内还可精确定位共同最优的缺失。记 $E_p(s)=\{e\in\mathcal A_p:e(s)=B_p(s)\}$。取经过 $y$ 的任一直径，其纯端点为 $s_+,s_-$，则

$$
E_p(s_+)\cap E_p(s_-)=\varnothing.
\tag{XII155.17}
$$

确实，若同一个 $e$ 在两端都最低，写 $y=\lambda s_++(1-\lambda)s_-$、$0<\lambda<1$，则凹下包络与该效应共同给 $B_p(y)=\lambda B_p(s_+)+(1-\lambda)B_p(s_-)$；而纯行等号使 $f(y)$ 不低于右侧，与(XII155.11)矛盾。这里缺的是同一张原效应共同达到两端最低值，不是两端数值各自存在。

**推论 155.5（完整下界候选的同原复三能级结构）。** 在定义155.1的原域内，下列条件等价：

$$
\begin{gathered}
\mathrm{EB3}+\mathrm{PR}+\mathsf{MD},\\
\exists\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V
\text{ 实线性双射},\qquad
\Phi(\mathrm{PSD}_3)=C,\qquad u\Phi=\operatorname{Tr}.
\end{gathered}
\tag{XII155.18}
$$

证明。全域 $\mathsf{MD}$ 经定理155.2给全部原球单位饱和；此时准确复用 [IX114.9][Q155IX]，得到同原 $C,u$ 的完整静态复三能级表示，不先输入 Conn、维数九或共同 least。

反向直接在同一表示中消费151.4式(XII151.8)：若 $p=\Phi(vv^\ast)$、$\|v\|=1$，完整原确认效应为 $vv^\ast\oplus B$、$0\preceq B\preceq I_{v^\perp}$。每张都有同一个原正序下界 $vv^\ast\oplus0\in\mathcal A_p$，故支付所要求的逐张下界；EB3与纯 PR由该字典同时给出。证毕。

这是较弱量词的入口：先要求每张确认各有整球清零下界，分类后才得到同一 least；不是把 least 或仿射最低值写进前提。同一个 $\Phi$ 给全部原态为密度矩阵、全部原纯态为 $\mathbb{CP}^2$、每张排除球纯缘为 $\mathbb{CP}^1$，全部原效应为 $0\preceq E\preceq I_3$，原评价与全混态最低值分别为 $\operatorname{Tr}(E\rho)$、$v^\ast\rho v$。全部有限数学单位分解给完整 POVM 字典；实际仪器、复合纠缠、全旁观 CP、物理钟、Hamiltonian、能量及数值 $\hbar$ 仍保留各自独立合同。

**范围 155.6（未消去的原关系与完整中文图景）。** 推论155.5给出完整新入口候选 EB3、字面纯 PR、$\mathsf{MD}$。它与151.4的近一共同零候选在原域内经同一既有分类相接；本章的新增承重内容是逐张下界到原标签唯一及真实三角的桥，二维确认族的定量纯差距转移，以及仅混态差距的实际不相交球与三维斜率包围，不把既有分类另算新结果。没有从裸 EB3+PR 推出 $\mathsf{MD}$、$\mathsf N_2$ 或 Conn，也没有减少独立假设数或构造完整反模型。

若某个标签 $\beta_{D_p}>1$，定理155.2迫使某个原输入有严格差距。若差距已见于纯态，152.3限制该标签的实际塌缩落点至多一个；若全部纯差距为零，定理155.4将混态缺口定位于不碰旧球的另一颗实际完整球，并给三维实心斜率包围(XII155.14)及两端无共同最优(XII155.17)。这两支均未被排除，整球并合分支也仍保留。

本章为 repo-derived 的原效应序、实际塌缩与完整面接口综合推导，不声明全球原创或最少公理数。紧集加闭锥分离、切片极点、线性优化、支撑半空间刻画与球上非负仿射函数是成熟中间工具。更强的三读数纯匹配不能由153的两读数匹配直接取得：[Maier–Netzer，Proposition 2.1、Theorem 2.2][Q155M]的余维二截面道路与三算子联合值域凸性，使用复 Hilbert 自伴算子及复维数至少三；这些结构尚未由裸原前件支付，故不作为本章的输入。

白话上，仍在同一块完整状态体里：每次拿一张确认某个纯点的尺，都能向下换成一张把它背后整颗排除球清零的原尺。各次可以换不同的尺，这个较弱要求已足以找出真实的第三个排除点，进而恢复完整复三能级静态几何。若整球确认尺的独立差值至多两维，先锁住这些差值，再向下优化普通尺，就能把任何混点漏洞送到纯点；若纯点上都能换、混点上却不能，漏洞必须藏在另一颗完全不碰旧球的完整球内部，而且确认尺的斜率从全部三维方向围住普通尺，同一直径两端也需要不同的最低尺。尚待证明的是，比较互易与完整三球能否也自动禁止这些漏洞；没有把这一缺失关系宣布为已内生。

[Q155IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.8—114.9：真实三角、单位预算与既有同锥同单位分类；IX116.2：完整孤立重复球对。"
[Q155X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X124.7：重复球对每个指定纯点的实际整球塌缩；124.9：紧纯接收标签及配对球定位；X126.3：实际塌缩的补确认及全原域单点零面，不输入Inj/P0。"
[Q155M]: https://arxiv.org/html/2409.04444v1 "B. Maier, T. Netzer, A Note on the Carathéodory Number of the Joint Numerical Range，Proposition 2.1、Theorem 2.2。"

## 追加锚（本行以下为增补区）

## 156. 最大混态差距的支撑球与临界三维确认交点

**定义 156.1（同一原域中的最大差距）。** 保留定义155.1的全部原 $V,C,u,K,P,\mathcal E,\mathcal F_p,T_p,D_p,S_p,\mathcal A_p,B_p,\Delta_p$，假设完整 EB3 与字面纯 PR。全部原状态、效应、确认菜单和每个混输入上达到的 minimum 均保留。固定原纯 $p$，本章另有明确的单行前件

$$
T_p(s)=B_p(s)\qquad(s\in P).
\tag{XII156.1}
$$

对原 $f\in\mathcal F_p$，记

$$
\delta_f=\max_{x\in K}\bigl(B_p(x)-f(x)\bigr),\qquad
W_p=\operatorname{span}(\mathcal A_p-e_0),\quad e_0\in\mathcal A_p.
\tag{XII156.2}
$$

$W_p$ 不依赖 $e_0$ 的选择。$\delta_f>0$ 是本章有关支撑球各条的前件，不断言它在完整模型中可实现。对线性泛函 $n$，$\operatorname{argmax}_K n$、$\operatorname{argmin}_K n$ 始终取整个原 $K$。

**定理 156.2（同一原效应差的整球支撑与严格反向预算）。** 若 $\delta_f>0$，则存在 $e_f\in\mathcal A_p$，使 $n_f=e_f-f$ 满足

$$
\max_K n_f=\delta_f,
\qquad F_f:=\operatorname{argmax}_K n_f=D_t
\quad\text{对某个原纯 }t.
\tag{XII156.3}
$$

每个达到 $\delta_f$ 的输入 $x$ 都位于 $\operatorname{ri}F_f$，且

$$
p\notin F_f,\qquad F_f\cap D_p=\varnothing.
\tag{XII156.4}
$$

令 $m_f=\min_K n_f$、$a_f=\max_{D_p}f$。则

$$
m_f<-a_f<0.
\tag{XII156.5}
$$

对每个原纯 $q\in\operatorname{argmin}_K n_f$，同一张归一化原效应满足

$$
g_f=\frac{\delta_f u-n_f}{\delta_f-m_f}\in\mathcal A_q,
\quad Z_K(g_f)=F_f=D_q,
\quad q\notin D_p.
\tag{XII156.6}
$$

证明。对紧凸集 $K,\mathcal A_p$ 上的连续双仿射评价 $L(x,e)=(e-f)(x)$，应用 [Sion，Theorem 3.4][Q156S]。它的紧凸、上半连续凹与下半连续凸条件均由这里的有限维紧凸与双仿射性满足，得到

$$
\delta_f=\max_{x\in K}\min_{e\in\mathcal A_p}L(x,e)
=\min_{e\in\mathcal A_p}\max_{x\in K}L(x,e).
\tag{XII156.7}
$$

两侧都达到。取右侧极小元 $e_f$，任取左侧极大元 $x$，便有

$$
(e-f)(x)\ge\delta_f\quad(e\in\mathcal A_p),\qquad
n_f(z)\le\delta_f\quad(z\in K),\qquad n_f(x)=\delta_f.
\tag{XII156.8}
$$

这是成熟极小极大定理在本条推导内的应用，不另计为新定理。$n_f(p)=0<\delta_f$，故 $F_f$ 为非空真暴露面。由(XII156.1)，所有纯 $s$ 都满足 $B_p(s)-f(s)\le0$，所以 $x$ 非纯。原真面分类使 $F_f$ 是实际完整三球；球内非纯点恰为其相对内点。又 $n_f|_{D_p}=-f\le0$，直接得到(XII156.4)。

若 $a_f=0$，则原 $f\in\mathcal A_p$，与 $\delta_f>0$ 矛盾，故 $a_f>0$。由于 $n_f|_{D_p}=-f$，有 $m_f\le-a_f<0$。以这两个实际全域极值归一化便给 $g_f\in\mathcal E$、$Z_K(g_f)=F_f$。任何纯极小点 $q$ 满足 $g_f(q)=1$，故 $F_f\subseteq D_q$；完整球为极大真面，所以 $D_q=F_f$。

若 $m_f=-a_f$，在 $D_p$ 上取达到 $a_f$ 的一个原纯点 $r$。则 $n_f(r)=m_f$，前段给 $D_r=F_f$。但 $r\in D_p$ 经原零对称给 $p\in D_r=F_f$，违反(XII156.4)。因此不等式严格。它也排除任何纯极小点属于 $D_p$。证毕。

**定理 156.3（三维斜率包围与唯一混态交点）。** 在定理156.2的条件下，固定所取 $e_f,F_f$ 与任意最大差距点 $x$。选球图 $b:\overline B^3\to F_f$，写 $x=b(z_x)$，并定义

$$
(e-e_f)(b(z))=(e-e_f)(x)+\gamma_e\cdot(z-z_x),\qquad
\Gamma_f=\{\gamma_e:e\in\mathcal A_p\}.
\tag{XII156.9}
$$

则

$$
\rho_f\overline B^3\subseteq\Gamma_f,
\qquad \rho_f=\frac{\delta_f}{1+\|z_x\|}>0.
\tag{XII156.10}
$$

若另有 $\dim\operatorname{aff}\mathcal A_p=3$，则 $e_f\in\operatorname{ri}\mathcal A_p$，全部整球零确认在同一个 $x$ 取相同值，并且

$$
\begin{aligned}
e(x)&=e_f(x)=B_p(x)\quad(e\in\mathcal A_p),\\
B_p(b(z))-f(b(z))
&=\delta_f+\min_{\gamma\in\Gamma_f}\gamma\cdot(z-z_x)
\le\delta_f-\rho_f\|z-z_x\|.
\end{aligned}
\tag{XII156.11}
$$

因此 $B_p-f$ 在整个原 $K$ 上的最大点唯一；全部限制 $e|_{F_f}$ 的共同相等点在 $F_f$ 内也唯一，恰为 $x$。这两项唯一性均没有宣称 $\Delta_p$ 在整个 $K$ 上只有一个最大点。

证明。$n_f$ 在整个 $F_f$ 上恒为 $\delta_f$，所以 $e-f$ 的球内斜率与 $e-e_f$ 的斜率相同。对每个单位方向 $v$，沿 $z_x-tv$ 到纯球缘 $w$，其中 $0<t\le1+\|z_x\|$。纯行等号与 minimum 达到给某张 $e_w\in\mathcal A_p$，使 $(e_w-f)(b(w))\le0$；而(XII156.8)给 $(e_w-f)(x)\ge\delta_f$。于是 $\gamma_{e_w}\cdot v\ge\delta_f/t\ge\rho_f$。紧凸 $\Gamma_f$ 的支撑半空间刻画给(XII156.10)。此处复用155.4的斜率包围论证，新增定位在同一个全域支撑效应差上。

映射 $R:W_p\to\mathbb R^3$，$h\mapsto\operatorname{grad}(h\circ b)$ 是线性的，且 $R(\mathcal A_p-e_f)=\Gamma_f$。当 $\dim W_p=3$ 时，(XII156.10)使 $R$ 成为线性同构。$0\in\operatorname{int}\Gamma_f$ 因而给 $e_f\in\operatorname{ri}\mathcal A_p$。线性评价 $e\mapsto(e-e_f)(x)$ 由(XII156.8)在这个相对内点取最小值零，故它在整个仿射包络恒为零。这给第一项等号及第二项的准确展开。取(XII156.10)中的 $-\rho_f(z-z_x)/\|z-z_x\|$ 得所写定量下降。

任意全域最大点 $y$ 满足

$$
\delta_f=B_p(y)-f(y)\le n_f(y)\le\delta_f,
\tag{XII156.12}
$$

故 $y\in F_f$；定量下降再迫 $y=x$。若 $F_f$ 上某点 $b(z)$ 使全部 $e$ 相等，取 $e=e_f$ 并用第一项，便有 $\gamma\cdot(z-z_x)=0$ 对整个 $\Gamma_f$ 成立；实心球包围迫 $z=z_x$。证毕。

**定理 156.4（全部原最优效应的共同球与两端约束）。** 仍假设(XII156.1)，令

$$
\delta=\max_K\Delta_p>0,\qquad \Delta_p(x)=\delta.
\tag{XII156.13}
$$

则存在唯一包含 $x$ 为相对内点的实际完整球 $F$，且对每张 $f\in M_p(x)$，均有 $\delta_f=\delta$，可在定理156.2中取 $F_f=F$。全部这些原最优效应的零面是同一个 $\{r\}$，$r\in S_p$。记 $\bar r=2c_p-r$；对每张 $f\in M_p(x)$，每个相应 $e_f$ 与每个原纯极小点 $q\in\operatorname{argmin}_K(e_f-f)$，均有

$$
\begin{gathered}
D_q=F,\qquad
f(q)>-m_f>a_f=f(\bar r)>0,\\
g_f(p)=g_f(r)=\frac{\delta}{\delta-m_f},\qquad
g_f(q)=1,\qquad g_f|_F=0.
\end{gathered}
\tag{XII156.14}
$$

若另有 $\dim\operatorname{aff}\mathcal A_p=3$，则对整个实际最优面 $M_p(x)$，上述 $e_f$ 唯一，并定义连续仿射映射

$$
\Psi_x:M_p(x)\longrightarrow\operatorname{ri}\mathcal A_p,
\qquad f\longmapsto e_f,
\qquad (e_f-f)|_F=\delta.
\tag{XII156.15}
$$

全部 $e\in\mathcal A_p$ 在同一个 $x$ 相等，每个 $B_p-f$ 的全域最大点均是这个 $x$。不要求 $\Psi_x$ 单射，也不要求不同 $f$ 的纯极小点 $q$ 相同。

证明。任意 $f\in M_p(x)$ 都满足 $B_p-f\le\Delta_p\le\delta$，并在 $x$ 取等，故 $\delta_f=\delta$。定理156.2给 $x\in\operatorname{ri}F_f$；一个凸集的每点只有一个最小面，而这里 $x$ 非纯，所以所有 $F_f$ 都是同一实际球 $F$。定理152.2在这个严格差距点给全部 $M_p(x)$ 的共同原单点零 $r\in S_p$。

$f|_{D_p}$ 是非负仿射函数，零于球缘 $r$ 且不恒零；球上该形式使其最大值恰在对径点 $\bar r$，故 $a_f=f(\bar r)>0$。定理156.2给 $m_f<-a_f$、$q\notin D_p$。$e_f$ 的整个零面恰为 $D_p$，所以

$$
f(q)=e_f(q)-m_f>-m_f>a_f.
\tag{XII156.16}
$$

又 $n_f(p)=n_f(r)=0$，直接从同一原 $g_f$ 的定义得到(XII156.14)。这同时控制原确认点、共同零点、整个支撑球和反向极小标签，没有更换原效应区间。

在三维分支，156.3已给每个 $e_f$ 属于相对内部及全部确认在 $x$ 相等。若 $e,e'\in\mathcal A_p$ 都是相应极小极大元，则 $(e-e')|_F=0$；156.3的梯度同构 $R$ 迫 $e=e'$。相同同构还给 $e_f$ 对 $f|_F$ 的仿射连续依赖。更直接地，若 $f_1,f_2\in M_p(x)$，则 $e=\lambda e_{f_1}+(1-\lambda)e_{f_2}$ 对 $f=\lambda f_1+(1-\lambda)f_2$ 满足 $e-f\le\delta u$ 且在 $F$ 上取等，故唯一性给 $\Psi_x(f)=e$。有限维仿射表达给连续性。每个 $B_p-f$ 的唯一最大点由156.3供应。证毕。

**定理 156.5（完整菜单差距的球内唯一最大与线性下降）。** 在定理156.4的临界三维分支内，$\Delta_p$ 在同一颗实际 $F$ 内只有一个达到全域最大值 $\delta$ 的点，恰为 $x$。取该球图 $b$、$x=b(z_x)$，存在 $\eta,\varepsilon>0$，使

$$
0<\|h\|<\varepsilon
\quad\Longrightarrow\quad
\Delta_p(b(z_x+h))\le\delta-\eta\|h\|.
\tag{XII156.17}
$$

这里取 $\varepsilon<1-\|z_x\|$，故所写输入仍在整个原球内。没有断言其他实际球上不存在另一个全域最大点。

证明。记 $t=T_p(x)$，并在同一球图中令

$$
\Sigma_A=\{\operatorname{grad}(e\circ b):e\in\mathcal A_p\},\qquad
\Sigma_M=\{\operatorname{grad}(f\circ b):f\in M_p(x)\}.
\tag{XII156.18}
$$

由156.3的斜率同构，$\mathcal A_p$ 到 $\Sigma_A$ 是仿射同构。156.4的连续映射 $\Psi_x$ 将紧的整个原最优面送入 $\operatorname{ri}\mathcal A_p$，而 $(e_f-f)|_F=\delta$ 使对应斜率相同。因此 $\Sigma_M$ 是 $\operatorname{int}\Sigma_A$ 的紧子集，存在 $\eta_0>0$，使 $\Sigma_M+\eta_0\overline B^3\subseteq\Sigma_A$。

全部整球零确认在 $x$ 等值，故准确有 $B_p(b(z_x+h))=t+\delta+\min_{\alpha\in\Sigma_A}\alpha\cdot h$。对完整原菜单，紧性给一致的一阶下包络展开

$$
T_p(b(z_x+h))=t+\min_{\beta\in\Sigma_M}\beta\cdot h+o(\|h\|).
\tag{XII156.19}
$$

具体地，邻近输入的任意原最优效应 $f_h$ 的聚点都属于 $M_p(x)$：由原菜单紧性、固定 $T_p$ 连续及最优取等，极限满足 $f(x)=t$。因此其斜率到紧集 $\Sigma_M$ 的距离一致趋零，且 $f_h(x)\ge t$，给所写展开的下界；直接使用 $M_p(x)$ 中的效应给上界。这一步遍历整个原菜单，并未把 $T_p$ 假定为仿射。

斜率的统一内余量给 $\min_{\Sigma_A}\alpha\cdot h\le\min_{\Sigma_M}\beta\cdot h-\eta_0\|h\|$。相减并缩小 $\varepsilon$，取 $\eta=\eta_0/2$，便得(XII156.17)。若 $y\in F$ 也达到全域 $\delta$，纯行等号先排除纯 $y$。对达到 $T_p(y)$ 的原效应应用156.3，全部 $\mathcal A_p$ 必在 $y$ 等值；同一 $F$ 内该交点唯一，故 $y=x$。证毕。

**范围 156.6（候选、未决关系与完整中文图景）。** 完整新入口候选仍为155.1的 EB3、字面纯 PR 与 $\mathsf{MD}$：每张原确认效应，都有一张仍确认同一原纯点且将其整个排除球清零的原效应作正序下界。155.5已证明，在全部原状态、效应、完整菜单和混输入达到的原域中，该候选等价于同原 $C,u$ 的复三能级静态结构；本章不重复该分类。单行前件(XII156.1)不是裸 EB3+PR 已自动取得的关系，临界三维条件也没有成为原模型的定理。

新增的 repo-derived 推导是：同一原效应差的整个极大面、严格反向预算、临界三维时的唯一混态交点，以及整个实际最优面的共同支撑球、仿射对应和实际菜单差距的球内线性下降。极小极大、相对内部、球上非负仿射函数和支撑半空间均为成熟中间工具；不声称全球原创、最少公理或独立假设数减少。

尚未证明原比较互易能禁止(XII156.14)—(XII156.15)这一联合构型；也未构造实现它的完整 EB3+PR 模型。特别地，$g_f$ 仍可只给比较值上界，不能未经证明将其替换成 $T_q$ 的全域 least；不同菜单成员的反向极小标签仍可变化。纯差距分支与整球并合分支仍按152、155保留。这里没有引入154的整个 $\dim V\le9$ 前件，也没有从其相对四维图取得全域 Conn。实际仪器、复合、全旁观 CP、物理钟、Hamiltonian、能量与数值 $\hbar$ 仍各需独立合同。

白话上，仍拿同一块完整状态体和全部原尺来比较：如果纯点上整球清零尺已经够用，混点上却还有漏差，那么最大漏差必由同一张“尺的差”托在另一颗完整球上；这张差尺反向最深处的纯点，又确实以这颗球为自己的整个排除球。若整球确认族恰有三个独立差值，所有这些尺必在球内同一个混点相交，任何方向离开它，每张固定测试的差距都严格下降；将全部最低尺一起比较，实际菜单差距在这颗球内也只有这一个最大点，并在附近线性下降。再把全部最低尺一起看，它们共用旧球上的同一个零点，各自的反向极小标签都在旧球外，而且同一张最低尺在那里读得比旧球上任何点都高。我们得到的是必须同时满足的几何关系，尚未证明这幅构型不可能；因此“两两可比较、交换双方数值不变”能否独自支付最后的共同零关系，仍是原问题。

[Q156S]: https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-s.pdf "Maurice Sion, On general minimax theorems, Pacific Journal of Mathematics 8 (1958), 171–176, Theorem 3.4；连续双仿射紧凸情形。"

## 追加锚（本行以下为增补区）

## 157. 单标签接收端的整球正则性与单三角种子判据

### 157.1 完整原域与局部接口

**定义 157.1（原对象、实际塌缩及有限种子）。** 设 $V\ne0$ 为有限维实向量空间，$C\subset V$ 是闭、尖、生成凸锥，$u\in V^*$ 在 $C\setminus\{0\}$ 上严格正。始终保留同一个原载体上的整个

$$
\begin{gathered}
C^*=\{h\in V^*:h|_C\ge0\},\qquad K=C\cap\{u=1\},\qquad
P=\operatorname{ext}K,\qquad \mathcal E=[0,u]_{C^*},\\
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x)\quad(p\in P,\ x\in K),\\
D_p=\{x\in K:T_p(x)=0\},\qquad S_p=P\cap D_p,\qquad
\mathcal A_p=\{e\in F_p:e|_{D_p}=0\},\\
N_p=\{h\in C^*:h(p)=0\},\qquad L_p=\operatorname{span}_{\mathbb R}N_p,\qquad
N_F=\{h\in C^*:h|_F=0\},\\
\mathscr B=\{D_p:p\in P\},\qquad S(F)=P\cap F,\qquad
I(F)=\{p\in P:D_p=F\},\\
P_{\rm s}=\{p\in P:I(D_p)=\{p\}\},\qquad P_{\rm r}=P\setminus P_{\rm s}.
\end{gathered}
\tag{XII157.1}
$$

第二变量遍历每个原混态；效应区间、全部确认菜单及纯点集合都不缩减。$D_p$ 是全部确认零集的并，不能预先换成它们的交。以下共同背景准确为

$$
\begin{aligned}
\mathrm{EB3}:&\quad \forall p\in P,\quad D_p\simeq_{\rm aff}\overline B^3
\quad\text{（整个非退化闭三球）},\\
\mathrm{PR}:&\quad \forall p,q\in P,\quad T_p(q)=T_q(p),\\
&\quad \dim_{\mathbb R}V\le9.
\end{aligned}
\tag{XII157.2}
$$

维数上界是独立输入。PR 只交换两个纯比较端点。记 $p\perp q\Longleftrightarrow T_p(q)=0$；原补效应使其对称，且 $p\not\perp p$。固定辅助欧氏范数 $\|\cdot\|$ 及其 Hausdorff 距离 $d_H$，仅描述原有限维拓扑。每个完整球 $F=c_F+B_F\overline B^3$ 的中心唯一，$B_F:\mathbb R^3\to\ker u$ 单射，实际对径为 $c_F+B_Ft\leftrightarrow c_F-B_Ft$。按有限原零边路径定义

$$
\Gamma(p)=\{a\in P:\exists n\ge0,\ a_0=p,\ a_n=a,
\ a_j\perp a_{j+1}\ (0\le j<n)\}.
\tag{XII157.3}
$$

这不是环境拓扑连通分支。称

$$
p_i\in P,\qquad p_i\to p\in P,\qquad
d_H(D_{p_i},\{q\})\to0\quad(q\in K)
\tag{XII157.4}
$$

为实际整球塌缩。发送标签没有单标签、最终单标签、互异或同分支要求。一个实际零三角是 $p,q,r\in P$ 满足 $p\perp q$、$q\perp r$、$r\perp p$；非自反性保证三点不同。三条边各有完整原域中的效应见证，定义不要求共同仪器或三张见证之和为 $u$。

以下准确复用既有供应，不将它们另列为新定理。[IX114.1—114.6、IX116.1][Q157IX] 给 $K,\mathcal E,F_p$ 紧、全部 minimum 达到、$C=\mathbb R_{\ge0}K$、$K=\operatorname{conv}P$ 且 $K$ 张成 $V$。PR 给全部原纯点严格暴露及整个 $P$ 紧。置 $M=\max_{f\in\mathcal E}\|f\|_*<\infty$，有

$$
|T_p(x)-T_p(y)|\le M\|x-y\|\qquad(p\in P,\ x,y\in K).
\tag{XII157.5}
$$

完整原面分类给每个 $D_p$ 为紧暴露极大真面，$\mathcal A_p\ne\varnothing$；每个非空真面是纯单点或某个完整 $D_p$。不同完整球若相交，交恰是一个原纯点；$S(F)=\partial_{\rm rel}F$，$F=\operatorname{conv}S(F)$。对每个完整球图 $b_F:\overline B^3\to F$，存在唯一 $0<a_F\le1/2$，使

$$
\begin{gathered}
T_{b_F(w)}(b_F(z))=1-a_F+a_Fw\cdot z
\quad(w\in S^2,\ z\in\overline B^3),\\
h_v(b_F(z))=(1+v\cdot z)/2,\\
\beta_F(v)=\inf\{A\ge0:\exists h\in V^*,\ 0\le_Ch\le_CAu,\ h|_F=h_v\}
=\beta_F=\frac1{2a_F}\quad(v\in S^2).
\end{gathered}
\tag{XII157.6}
$$

下确界达到；$\beta_F$ 也是整个面效应族的共同最优正延拓预算。逐效应正延拓不供应保持单位的线性延拓算子或共同仪器。球内公式包括全部混态，却不宣称比较函数在全 $K$ 仿射。

[IX114.8][Q157IX] 在同一完整 EB3+PR 域中，对每条实际 $a\perp b$ 给

$$
\beta_{D_a}=1
\Longleftrightarrow D_a\cap D_b\ne\varnothing
\Longleftrightarrow H(a,b)\ne K
\Longleftrightarrow\beta_{D_b}=1.
\tag{XII157.7}
$$

$H(a,b)$ 为原最小面；末项由同一定理交换两端取得。若 $b=b_{D_a}(t)$ 且这些条件成立，则交恰为 $\{b_{D_a}(-t)\}$，最小面为 $D_{b_{D_a}(-t)}$，没有预设两球刻度相同。[IX116.2、116.6][Q157IX] 给每个 $F\in\mathscr B$ 或为单标签，或有唯一完整配对球 $G$，满足

$$
I(F)=S(G),\qquad I(G)=S(F),\qquad F\cap G=\varnothing;
\tag{XII157.8}
$$

后一情形两球都不与第三张不同完整球相交。另有 $P_{\rm s}\ne\varnothing$，以及 $p\in P_{\rm s}\Rightarrow S_p\subset P_{\rm s}$；因此有限零路从单标签根出发仍在单标签域。[IX115.4—115.5][Q157IX] 对任意原发送列 $a_i\to a\in P$ 给闭图，以及每个 Hausdorff 子列极限的准确二择

$$
D_{a_i}\to E\quad\Longrightarrow\quad
E=D_a\ \text{或}\ E=\{b\},\ b\in S_a.
\tag{XII157.9}
$$

这些量词不要求发送标签最终单标签。

由本卷推论147.8和独立上界，整个 $\dim_{\mathbb R}V=9$。定理147.1、命题147.6遂在每个实际 $p\in P_{\rm s}$ 供应

$$
\begin{gathered}
\mathcal A_p=\{e_p\},\quad \dim L_p=4,\quad N_{D_p}=\mathbb R_+e_p,\\
\{x\in K:e_p(x)=0\}=D_p,\qquad \{x\in K:e_p(x)=1\}=\{p\},\\
g_p=u-e_p\in\operatorname{ri}N_p,\quad g_p>0\text{ 于 }K\setminus\{p\},\qquad
R_p:L_p\overset\sim\longrightarrow\operatorname{Aff}(D_p),\ h\mapsto h|_{D_p}.
\end{gathered}
\tag{XII157.10}
$$

写 $D_p=c_p+B_p\overline B^3$。唯一原线性 $H_p:V\to\mathbb R^3$ 的各分量在 $L_p$，且 $H_p(p)=0$、$H_p(c_p+B_pz)=z$、$g_p(c_p+B_pz)=1$。对全部 $v\in\mathbb R^3$，既有方向函数和正性公式为

$$
\begin{gathered}
\rho_p(v)=\sup_{x\in K\setminus\{p\}}
\frac{-v\cdot H_p(x)}{g_p(x)},\qquad \rho_p(v)\ge\|v\|,\\
N_p=\{\alpha g_p+v\cdot H_p:\alpha\ge\rho_p(v)\},\\
\max_K(\alpha g_p+v\cdot H_p)=\alpha+\|v\|
\quad\text{在 }\alpha\ge\rho_p(v)\text{ 时}.
\end{gathered}
\tag{XII157.11}
$$

$\rho_p$ 有限、正齐次、次可加且 Lipschitz。对每个单位 $t$，$q_t=c_p+B_pt\in S_p\subset P_{\rm s}$，原式(XII147.16)在整个 $V$ 上给

$$
e_{q_t}=\frac{\rho_p(t)g_p+t\cdot H_p}{1+\rho_p(t)},\qquad
\{n\in\mathcal E:n(p)=0,n(q_t)=1\}=[g_p,e_{q_t}].
\tag{XII157.12}
$$

这些是原 $V^*$ 中的泛函和完整区间。$\mathcal A_p$ 单点不等于 $F_p$ 单点，限制同构也未预付正逆或 least。

最后精确使用本卷定理149.2：在整个 EB3 原域及整个 $\dim V\le9$ 下，若非空 $Q\subseteq P_{\rm s}$ 满足 $S_a\subseteq Q$ 对每个 $a\in Q$ 成立，且存在同一个实数 $\kappa<2$，使

$$
e_q+e_{2c_a-q}=\kappa(u-e_a)
\quad\text{于整个 }V,\qquad \forall a\in Q\ \forall q\in S_a,
\tag{XII157.13}
$$

则 $Q=P_{\rm s}=P$，且存在同原锥、同原单位的实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\mathrm{PSD}_3)=C,\qquad u(\Phi X)=\operatorname{Tr}X.
\tag{XII157.14}
$$

此时 $\kappa=1$。本接口不另输入 Conn、全局 Inj 或 $\mathsf{CR}_{\rm s}$；非空、全部实际零邻封闭和同一个全空间恒等式仍须逐项取得。

### 157.2 一颗单位预算球与一个实际零三角的完整种子判据

**定理 157.2（有限零三角种子与同原静态表示）。** 在定义157.1的完整 EB3+PR+$\dim_{\mathbb R}V\le9$ 域中，下列三项等价：

1. 存在 $p,q,r\in P$，使 $p\perp q$、$q\perp r$、$r\perp p$。
2. 存在一张实际完整球 $F\in\mathscr B$，使 $\beta_F=1$。
3. 存在式(XII157.14)的同原 $C/u$ 表示。

这些条件成立时，全部原球预算为一，$P_{\rm s}=P$，原零图有限边路连通，且每个固定根两步覆盖全部原纯标签。第1项只有三个原纯点及三条实际零边；不预先给共同三结果效应。本节的有限种子论证不从共同背景单独取得第1项或第2项；它们的无额外种子存在性由第158章的开放图册与全域关联另行支付。

证明。先证 $1\Rightarrow2$。$q,r\in S_p$，在同一完整 $D_p$ 的球图中写为 $b(w),b(z)$，$w,z\in S^2$。球内准确式(XII157.6)及 $q\perp r$ 给

$$
0=T_q(r)=1-a_{D_p}+a_{D_p}w\cdot z
\ge1-2a_{D_p}\ge0.
\tag{XII157.15}
$$

故 $a_{D_p}=1/2$、$z=-w$、$\beta_{D_p}=1$。这是既有同球刻度在三个实际原点上的应用。

证 $2\Rightarrow3$ 时，先支付种子球的单标签性。取 $p\in I(F)$。若 $F$ 重复，原配对式(XII157.8)给不交的 $G$，且每个 $q\in S(F)$ 都有 $D_q=G$。任选实际对径 $q=b_F(t)$、$r=b_F(-t)$。预算一及球内公式给 $T_q(r)=0$，所以 $r\in D_q=G$，但 $r\in F$，与 $F\cap G=\varnothing$ 矛盾。因此 $I(F)=\{p\}$，实际种子 $p\in P_{\rm s}$。这一步不能以“种子自然单标签”代替。

令 $Q=\Gamma(p)$。零长路径给 $Q\ne\varnothing$，在路径末尾接边给 $S_a\subseteq Q$ 对每个 $a\in Q$ 成立；IX116.6 沿有限路径给 $Q\subseteq P_{\rm s}$。对任意路径 $p=a_0\perp a_1\perp\cdots\perp a_n=a$，逐边用式(XII157.7)及其交换端点实例，得到

$$
\beta_{D_a}=1,\qquad a_{D_a}=1/2\qquad(a\in Q).
\tag{XII157.16}
$$

这只先传播到一个实际零图分支，没有预先把它认作全部 $P$。

固定任意 $a\in Q$ 和任意 $t\in S^2$。写 $D_a=c_a+B_a\overline B^3$、$q_t=c_a+B_at$、$q_{-t}=c_a-B_at$。两端都在 $S_a\subseteq Q\subseteq P_{\rm s}$，预算一给 $q_t\perp q_{-t}$。$e_{q_t}$ 在其整个 $D_{q_t}$ 上为零，故在实际反极点 $q_{-t}\in D_{q_t}$ 评价式(XII157.12)，得到

$$
0=e_{q_t}(q_{-t})
=\frac{\rho_a(t)-1}{1+\rho_a(t)},\qquad \rho_a(t)=1.
\tag{XII157.17}
$$

另取方向 $-t$，由 $q_{-t}\perp q_t$ 及 $e_{q_{-t}}(q_t)=0$，同样得到 $\rho_a(-t)=1$。正齐次只涉及非负倍数，不承担这一步。因而式(XII147.16)中的两张实际原线性效应分别满足

$$
e_{q_t}=\tfrac12(g_a+t\cdot H_a),\qquad
e_{q_{-t}}=\tfrac12(g_a-t\cdot H_a),\qquad
e_{q_t}+e_{q_{-t}}=u-e_a
\quad\text{于整个 }V.
\tag{XII157.18}
$$

$a,t$ 均任意，且每个 $q\in S_a$ 恰为某个 $q_t$，其实际对径为 $q_{-t}$。因此式(XII157.13)对全部 $a\in Q,q\in S_a$ 成立，使用同一个 $\kappa=1<2$。整个原域和独立维数上界均保留，定理149.2的每一前件已经取得，故 $Q=P_{\rm s}=P$ 并有式(XII157.14)。这一步消费的是149.2的共同恒等式分支，而非将149.3的球心互易当成已知。

反向 $3\Rightarrow1$ 准确复用 [XI条件应用145.9][Q157XI] 和本卷149.11的同一个 $\Phi$ 字典。完整原确认菜单给 $T_{p_v}(p_w)=|v^*w|^2$，其中 $p_v=\Phi(vv^*)$、$v,w$ 为单位复向量。三个标准正交射线给三个实际原纯点，三条原比较均为零，故第1项成立。相同字典给每张完整原球 $a_F=1/2,\beta_F=1$，并使相同球的标签相同。对任意两个原纯射线，含相同射线情形，在复三维中可取单位 $z$ 正交于它们的复张成；其原标签 $p_z$ 给两条实际零边。因此每根两步覆盖和 Conn 均是此已取得表示的后果。证毕。

定理155.2由逐张整球下界 $\mathsf{MD}(p)$ 取得单标签、真实三角和单位预算，推论155.5由全域 $\mathsf{MD}$ 取得无维数上界的既有分类。本节不重复这些结论作为新入口，而保留一个实际零三角或一颗单位预算球的有限存在条件，在独立九维上界下接入149.2。判据的实质连接是：一颗满预算原球先避开配对重复块，随后全部方向的实际反极点评价把一个零图分支接入149.2。仅有一个三角的旧种子接口、要求三角顶点稠密的接口、要求单尺相容及 Conn 的接口，各保留其原前件；这里没有把这些前件从原定理中删除，也不把条件等价称为严格弱化或独立公理数减少。

### 157.3 126的证明在实际单标签接收端的转移

**定理 157.3（任意发送端的单标签无塌缩与整球连续）。** 在式(XII157.1)—(XII157.2)的完整原域中，$\dim_{\mathbb R}V=9$ 且 $P_{\rm s}\ne\varnothing$。对每个 $p\in P_{\rm s}$、每个原发送列 $p_i\in P$ 及每个 $q\in K$，式(XII157.4)不可能成立。此外，对每个 $p\in P_{\rm s}$，

$$
\forall(a_i)\subset P,\quad a_i\to p
\Longrightarrow d_H(D_{a_i},D_p)\to0.
\tag{XII157.19}
$$

等价地，$\forall\varepsilon>0\ \exists\delta>0\ \forall a\in P$，若 $\|a-p\|<\delta$，则 $d_H(D_a,D_p)<\varepsilon$。发送端始终遍历全部原 $P$。

证明。维数等号和非空性分别归于本卷147.8与 IX116.6。反设在实际 $p\in P_{\rm s}$ 发生式(XII157.4)。原二择给 $q\in S_p$，单标签零邻闭包给 $q\in P_{\rm s}$。置

$$
J(p,q)=\{e\in\mathcal E:e(p)=1,e(q)=0\}.
\tag{XII157.20}
$$

它非空、紧，且由式(XII157.12)取补，准确有 $J(p,q)=[e_p,u-e_q]$ 于原 $V^*$。

先在本证明内部展开 [X126.2][Q157X] 的固定边达到步骤，保留它对任意原发送列的量词。固定 $s\in P\setminus\{p\}$。PR、固定 $T_s$ 的连续性及严格纯暴露给

$$
t_i=T_{p_i}(s)=T_s(p_i)\longrightarrow T_s(p)=T_p(s)<1.
\tag{XII157.21}
$$

在充分大的尾部，取达到 minimum 的 $f_i\in F_{p_i}$，$f_i(s)=t_i<1$。若 $m_i=\min_Kf_i>0$，则 $0<m_i\le t_i<1$，全域归一化给

$$
\widetilde f_i=\frac{f_i-m_iu}{1-m_i}\in F_{p_i},\qquad
\widetilde f_i(s)=\frac{t_i-m_i}{1-m_i}<t_i,
\tag{XII157.22}
$$

矛盾。因此 $m_i=0$，存在真实 $z_i\in K$ 使 $f_i(z_i)=0$。同一张 $f_i$ 确认 $p_i$，故 $z_i\in D_{p_i}$；实际整球塌缩迫 $z_i\to q$。紧 $\mathcal E$ 中取子列 $f_i\to f_s$，联合评价给 $f_s(p)=1$、$f_s(q)=0$、$f_s(s)=T_p(s)$。所以 $f_s\in J(p,q)$ 达到左侧。$s=p$ 时非空 $J(p,q)$ 上所有读数均为一，直接成立。结合 $J(p,q)\subseteq F_p$，得到既有固定边等式在此的准确实例

$$
T_p(s)=\min_{e\in J(p,q)}e(s)
=\min\{e_p(s),1-e_q(s)\}\qquad(s\in P).
\tag{XII157.23}
$$

这里是 $\forall s\exists f_s$，尚未取得一张共同最优效应或混态仿射性。

现在按 [X126.6的局部扰动路线][Q157X] 推导，但旧全域 Inj 的消费者改由实际接收端和实际零邻点的147接口逐项供应。写

$$
D_p=b(\overline B^3),\quad q=b(v),\quad\|v\|=1,\quad
g=g_p,\quad H=H_p,\quad
\lambda=\frac1{1+\rho_p(v)}\in(0,1/2],\quad
e_q=(1-\lambda)g+\lambda v\cdot H.
\tag{XII157.24}
$$

取补将整个 $F_p$ 双射到 $\mathcal B_p=\{n\in\mathcal E:n(p)=0\}$，式(XII157.23)等价于

$$
\max_{n\in\mathcal B_p}n(s)=\max\{g(s),e_q(s)\}
\qquad(s\in P).
\tag{XII157.25}
$$

固定 $s\in P\setminus\{p\}$，因 $g(s)>0$ 可令 $Y=H(s)/g(s)$。若 $\|Y\|>1$，取 $t=Y/\|Y\|$。$g\in\operatorname{ri}N_p$ 且 $t\cdot H\in L_p$，所以充分小的 $\varepsilon>0$ 使 $g+\varepsilon t\cdot H\in N_p$。先取得这项全原锥正性，再用式(XII157.11)的原最大值，得到

$$
n_\varepsilon=\frac{g+\varepsilon t\cdot H}{1+\varepsilon}\in\mathcal B_p,
\qquad n_\varepsilon(s)=g(s)\frac{1+\varepsilon\|Y\|}{1+\varepsilon}>g(s).
\tag{XII157.26}
$$

式(XII157.25)迫 $e_q(s)>g(s)$，再由 $\lambda>0$ 得

$$
\|Y\|>1\quad\Longrightarrow\quad v\cdot Y>1.
\tag{XII157.27}
$$

这一步只先排除反向越界：若 $v\cdot Y<-1$，则 $\|Y\|>1$，却同时有 $v\cdot Y>1$，矛盾。因此 $g(s)+v\cdot H(s)\ge0$ 于每个 $s\ne p$ 的原纯点；在 $p$ 处两项都为零。固定线性泛函的非负性经 $K=\operatorname{conv}P$ 延到全部原混态，再经 $C=\mathbb R_{\ge0}K$ 延到整个原锥。故

$$
k=\tfrac12(g+v\cdot H)\in N_p,\qquad
\max_Kk=1,\qquad k\in\mathcal E.
\tag{XII157.28}
$$

原最大值公式只在上述正性成立以后使用。在同一个实际旧球取 $r=b(-v)$，则 $k(q)=1,k(r)=0$，故 $q\perp r$。球内式给 $0=T_q(r)=1-2a_{D_p}$，于是 $a_{D_p}=1/2$。又 $p,r$ 是完整 $D_q$ 中两个不同的正交原纯点：$p\in D_q$ 来自 $q\in D_p$ 及零对称，$r\in D_q$ 来自刚取得的 $q\perp r$，$p\perp r$ 来自 $r\in D_p$。在该球图内写 $p=b_{D_q}(w)$、$r=b_{D_q}(z)$，则

$$
0=T_p(r)=1-a_{D_q}+a_{D_q}w\cdot z
\ge1-2a_{D_q}\ge0.
\tag{XII157.29}
$$

所以 $a_{D_q}=1/2$ 且 $z=-w$，从而两端 $\beta_{D_p}=\beta_{D_q}=1$。三点 $p,q,r$ 此时也确实构成实际原零三角。

这同样恢复126局部证明中的全菜单 least 步骤。对每个单位方向 $t$，$D_p$ 的预算一使 $q_t=b(t)$ 与 $q_{-t}=b(-t)$ 原正交。和式(XII157.17)完全一样，在实际 $q_{-t}$ 评价实际 $e_{q_t}$，得到 $\rho_p(t)=1$；另在 $q_t$ 评价 $e_{q_{-t}}$ 得 $\rho_p(-t)=1$。不从正齐次推出偶性。上确界定义逐方向给 $-t\cdot H(x)\le g(x)$ 对所有 $x\ne p$ 及所有单位 $t$ 成立；在 $p$ 处两项为零，所以

$$
\|H(x)\|\le g(x)\quad(x\in K),\qquad e_q\le g\text{ 于 }K.
\tag{XII157.30}
$$

式(XII157.23)化为 $T_p(s)=e_p(s)$ 对每个原纯点成立。任意固定 $f\in F_p$ 因而有 $f-e_p\ge0$ 于 $P$，再延到 $K,C$；又 $e_p\in F_p$，故在这个假设塌缩的分支中取得

$$
e_p\le_{C^*}f\quad(\forall f\in F_p),\qquad
T_p(x)=e_p(x)\quad(\forall x\in K).
\tag{XII157.31}
$$

没有把逐纯点各自的最优选择直接拼成仿射函数。上述126转移实际需要的唯一整球确认、严格正分母、四维限制同构、相对内部、已正泛函的全域最大值和完整边区间，都由147在 $p$ 处供应；$q$ 及所有实际 $q_t$ 的唯一确认由 IX116.6 后再用147供应。移动 $f_i,z_i$ 的步骤只用完整原域的紧性、纯 PR 和实际整球塌缩。因此没有对 $p_i$ 加入最终单标签前件，也没有调用只讨论单标签变化列的命题147.7。

已有一颗实际单位预算球，定理157.2现在给同原表示(XII157.14)。它只在假设塌缩的反证分支内被取得。用同一个固定 $\Phi$ 及 [XI条件应用145.9][Q157XI] 的完整零球字典，在此证明内部作有限维范数等价估计：

$$
m_\Phi=\min_{\|X\|_{\rm HS}=1}\|\Phi X\|>0,
\qquad \|\Phi X\|\ge m_\Phi\|X\|_{\rm HS}
\quad(X\in\operatorname{Herm}_3).
\tag{XII157.32}
$$

每个原标签 $a=\Phi(vv^*)$ 的整个 $D_a$ 是 $v^\perp$ 上全部密度矩阵的像。该二维复空间内各自选两个正交单位向量，其秩一投影 $R,S$ 都在此零球的原像中，且 $\|R-S\|_{\rm HS}=\sqrt2$。所以所有原 $a\in P$ 都有 $\operatorname{diam}D_a\ge m_\Phi\sqrt2>0$。这只是固定线性双射的成熟范数等价应用，不要求连续选择矩阵基，也不指定物理内积。然而假设塌缩给

$$
\operatorname{diam}D_{p_i}
\le2d_H(D_{p_i},\{q\})\to0,
\tag{XII157.33}
$$

矛盾。故单标签接收端没有任何原发送列的实际整球塌缩。反证中取得的 $P_{\rm s}=P$ 和 $\Phi$ 不能作为实际模型已经分类的结论保留。

最后固定任意 $a_i\in P$、$a_i\to p\in P_{\rm s}$。紧度量 $K$ 的非空紧子集空间在 Hausdorff 度量下紧：有限网给全有界性，紧集的 Hausdorff 极限给完备性。于是任意子列 $D_{a_i}$ 都有进一步收敛子列。式(XII157.9)只允许其极限为 $D_p$ 或某个 $\{q\}$、$q\in S_p$；后者刚已排除。若整列不趋 $D_p$，可取距离 $D_p$ 至少某个固定正数的子列，再取收敛子列就矛盾。故式(XII157.19)成立，原域可度量也给所述 $\varepsilon,\delta$ 形式。证毕。

### 157.4 配对球面的统一控制与原单标签域开放性

**定理 157.4（全纯域中的开放性及塌缩端点限制）。** 在同一完整 EB3+PR+$\dim_{\mathbb R}V\le9$ 域中，$P_{\rm s}$ 在整个原 $P$ 中相对开放。若任意原发送列实际满足式(XII157.4)，则接收标签与着陆点准确满足

$$
p,q\in P_{\rm r},\qquad q\in S_p.
\tag{XII157.34}
$$

证明。先证明开放性所需的整个配对球面控制。假设有重复列 $p_i\in P_{\rm r}$ 趋于 $p\in P_{\rm s}$，置 $F_i=D_{p_i}$，并取式(XII157.8)中的准确配对球 $G_i$。定理157.3对任意发送端的连续性给 $F_i\to D_p$。将证明

$$
\sup_{r\in S(G_i)}\|r-p\|\to0.
\tag{XII157.35}
$$

若不成立，存在 $\varepsilon>0$ 及子列上的实际 $r_i\in S(G_i)$，满足 $\|r_i-p\|\ge\varepsilon$。紧的全部原 $P$ 给进一步子列 $r_i\to r\in P$。准确配对式 $I(F_i)=S(G_i)$ 给 $D_{r_i}=F_i\to D_p$。在这个任意原接收标签 $r$ 处用式(XII157.9)：$D_p$ 非退化，不是单点，故只能 $D_r=D_p$。单标签性 $I(D_p)=\{p\}$ 迫 $r=p$，与 $\|r-p\|\ge\varepsilon$ 矛盾。这控制的是整个相反球面，不能以一个选定伙伴的趋点代替。

令 $\eta_i=\sup_{r\in S(G_i)}\|r-p\|\to0$。原球准确有 $G_i=\operatorname{conv}S(G_i)$，范数凸性使每个 $x\in G_i$ 都满足 $\|x-p\|\le\eta_i$，且 $G_i\ne\varnothing$。于是

$$
d_H(G_i,\{p\})\le\eta_i\to0.
\tag{XII157.36}
$$

这里直接使用原球面凸包，不需要凸体相对边界的稳定性假设。

每个非空球面 $S(F_i)$ 任取实际 $q_i\in S(F_i)$，由紧 $P$ 取子列 $q_i\to q\in P$。$F_i\to D_p$ 给 $q\in D_p\cap P=S_p\subseteq P_{\rm s}$。另一条准确配对式 $I(G_i)=S(F_i)$ 给

$$
D_{q_i}=G_i\longrightarrow\{p\}.
\tag{XII157.37}
$$

这是实际单标签接收端 $q$ 的整球塌缩，与定理157.3矛盾。没有要求 $q_i$ 最终单标签，也没有选择它们去逼近一个预定球面点。因此不存在趋向单标签点的重复列。原 $P$ 可度量，故 $P_{\rm s}$ 相对开放。

对任意实际塌缩，式(XII157.9)先给 $q\in S_p$。定理157.3排除 $p\in P_{\rm s}$。若 $q\in P_{\rm s}$，零对称给 $p\in S_q\subseteq P_{\rm s}$，再次矛盾。因此 $p,q\in P_{\rm r}$。这些限制始终不涉及发送标签的最终类型。证毕。

### 157.5 同一个表示的条件字典与独立物理合同

本节以实际取得式(XII157.14)为适用条件，例如由定理157.2的种子条件或第158章的共同背景定理取得；在此前件下使用 [XI条件应用145.9][Q157XI]、本卷149.11的整个静态字典。定理157.3反证分支中的表示只在该假设之下使用。这里的矩阵字典是既有结果的条件应用，不另立新分类。全部对象使用同一个 $\Phi$：置 $P_v=vv^*$、$v^*v=1$、$Q_v=I_3-P_v$、$p_v=\Phi(P_v)$、$U=\Phi(I_3)$，并令 $f_A(\Phi X)=\operatorname{Tr}(AX)$。则

$$
\begin{gathered}
C=\{\Phi X:X\succeq0\},\quad u(\Phi X)=\operatorname{Tr}X,\quad
K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\},\quad
P=\{p_v:\|v\|=1\},\\
\mathcal E=\{f_A:0\preceq A\preceq I_3\},\qquad
F_{p_v}=\{f_{P_v+B}:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\},\\
f_{P_v}\le_{C^*}f\quad(f\in F_{p_v}),\qquad
T_{p_v}(\Phi\rho)=\min_{f\in F_{p_v}}f(\Phi\rho)
=\operatorname{Tr}(P_v\rho)=v^*\rho v\quad(\rho\succeq0,\operatorname{Tr}\rho=1),\\
D_{p_v}=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1,\rho v=0\},\qquad
c_{p_v}=\Phi(Q_v/2)=(U-p_v)/2.
\end{gathered}
\tag{XII157.38}
$$

确认菜单是完整非单点菜单：正矩阵 $I_3-A$ 的零二次型给 $(I_3-A)v=0$，Hermitian 性消去交叉块，恰得到上述全部 $P_v+B$；反向每个所列 $B$ 都合法。对每个 $X\succeq0$，$\operatorname{Tr}(BX)\ge0$，故同一 $B=0$ 给全锥序 least 和每个原混输入的已达 minimum。正性给 $v^*\rho v=0\Longleftrightarrow\rho v=0$，所以最后一行保留完整混态零球。相同 $\Phi$ 保持全部非负质量，包括零、次归一及任意正质量；$X=0$ 时全部读数为零，只有正质量 $u(x)>0$ 才取 $f_A(x)/u(x)$，不给零质量强定归一态。

其余静态对应完整采用上述原字典：全纯域 $\mathbb{CP}^2$、纯球缘 $\mathbb{CP}^1$、整个 Bloch 三球、纯比较 $|v^*w|^2$、全部原零三角与全 Pair、所有有限数学 POVM（含零效应、重复项和全部有限粗粒化）、零权和重谱允许的谱分解、迹配对、自对偶与 Jordan 乘法、内部齐次性，以及全 $V$ 球心图 $R(x)=(u(x)U-x)/2$。一般实线性读数对应全部 Hermitian $A$；$v^*$ 是共轭转置。所有有限纯配方替换球心的相容性也沿同一表示运输。数学叠加的射线存在不供应实际相干制备。

实际物理范围完整继承 [XI第145.9节][Q157XI]、本卷第149.11节及 [SAME_READBACK第127.10节（SECTION127.10）][Q157SR] 的每一原对象、前件和量词。下述合同各自独立于单体静态分类。

共同来源域 $\Omega$、未知 ingress、同一个原装饰元组、全部同源及同中点实现、共同读回、全实关系、原概率像紧性、全测试表及闭性、零／单位／补／有界倍增、零及不等质量，均保持原合同。原两次同一读回、两实张成、完整(83.8)、INTRINSIC_POLAR VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确 PRE 后整个 H13 与每个原资格输入，以及活跃块严格负方向、共享总迹一、非活跃零质量和空活跃集，继续按上述来源及其传递引用供应。实际相位参考、来源采用、制备、可调用门、接线与权限都不从静态射线产生。

对每个有限 $N\ge1$，仍另供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 及全效应。对每个实际分割 $a+b=N$，仍要求 $C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b$、同一产品配对、全部因子置换及逆、规范重括号与指定运输。二份联合最低确认等式准确保留式(XI145.38)、(Q127.36)对每个产品或纠缠纯点、任意有限族及全部非负归一权重的量词，含零权与重复标签。低二份 Jordan 桥、实际自复合及复型选择、实际三份资源及其在 $C_3$ 中的成员身份分别供应；非经典资源仍取式(XI145.39)、(Q127.37)的同一最大复块及含相位正交基，$L=3$ 支路不以写出矩阵代付实际资源。高阶整个排除集不被规定为单体三球。

对所有输入输出份数 $m,n$、原实线性 $F:W_m\to W_n$ 和每个有限旁观系统 $b\ge0$，全旁观正性仍在每个含纠缠的共同输入上要求 $(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}$。实际完整有限层级及共同表示齐备后，才沿原 Choi 桥识别 CP。TP／TNI 分别对每个原 $x\in C_m$ 要求 $u_n(Fx)=u_m(x)$／$u_n(Fx)\le u_m(x)$；同族分支总预算在同一个输入上逐点承担。实际事件仍需完整提升、实际探针、相容核；让全部数学 CP-TNI 分支成为实际事件仍需事件饱和。共同仪器另保接线、共同预算、记录、粗粒化、输出与校准。只在严格正质量分支条件归一，零质量分支不强定条件态；Lüders 更新另保锐效应、接受态中性及输出校准。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字与旧 support、每个中间切口、全部合法未来、terminal futures、细标签粗归组和记录后条件未来，均保留原量词。有限零边路径和数学共同效应不支付这些实际操作与记录合同。

物理钟、实际连续动态来源、时间群和单位、Hamiltonian、能量识别及标定、数值 $\hbar$、时空和物理空间维数仍分别供应。另给同一载体上的全实时间连续保锥保质量线性群，才有描述该供应的有限维生成元；再给复块上的保迹酉时间实现，才写 $U_t=\exp(-\mathrm itH/\hbar)$、$\rho_t=U_t\rho U_t^*$、$H=H^*$。恒等时间族和非平凡 Hamiltonian 族可以共享全部静态对象。九维原实载体、四维纯域及三维排除球均不指定物理空间或时间。

### 157.6 几何解释、归属与局部结论的边界

把所有原状态想成同一块凸实体，每把原效应都是在整块实体上读零到一的尺，每个纯标签背后可排除的全部状态是一整颗实心三球。只要一颗实际球满预算，它的任意直径两端就能互读一和零；重复球却把对侧全部标签困在另一颗不交球上，容不下这样的第三点，所以这颗种子球必须单标签。满预算沿真实零边逐步传播；在每颗到达的球上，把一个端点自己的全空间确认尺放到实际反极点评价，就逐方向锁定径向系数为一，反方向也另算一次。两把对径尺因而在整个原空间中恰好拼成根标签的互补尺，149章才把这一整支接回全部原域。一个实际零三角已经在某颗球上留下这条满刻度直径，所以足以触发这条有条件的全域传播。另一方面，若球从任意原发送标签缩向单标签接收端，移动最优尺所带的真实零点全落到同一处，固定边上的整行最低读数便迫使原法向的一次小扰动成为正尺，在旧球上制造出满刻度直径；种子判据随之给出的固定表示却使每颗球都有统一正直径，故这种塌缩不可能。极限二择于是留下整颗正确球的连续性。若重复标签还能逼近单标签点，其配对球的整个相反球面都必须统一趋点，否则紧性会留下第二个共享同一零球的标签；球面凸包再使整颗配对球塌缩。另一侧球面标签的纯极限仍是单标签，又制造了刚被禁止的塌缩，因此单标签区在全部原纯域中开放。这个图景始终区分实际种子存在的条件分类与假设塌缩分支中的反证分类。

本章的承重连接属于 `repo-derived`：一颗实际单位预算球经重复块排除、有限零边传播和全空间反极点评价接入149.2；126的扰动证明以147的实际单标签接口逐项替代其旧全域 Inj 消费者；任意原发送列的单标签无塌缩及整球连续；整个配对球面的统一控制和原单标签域开放性。X126.2的固定边 minimum、固定线性表示的范数等价、紧超空间及球面凸包估计均作为证明中的既有或成熟中间步骤使用。原面分类、刻度、预算、二择、配对、单标签邻点闭包、147局部法向、149饱和分类和普通矩阵字典保持上述归属，不另计为新分类。本章不主张文献优先权、全球新颖性、条件严格弱化或独立公理数减少。

仅据本章的局部正则性结论，尚不能把 $P_{\rm s}$ 的开放性换成闭性、$P_{\rm r}=\varnothing$、全局 Inj、Conn、全根两步覆盖或分类；反证中出现的种子也不能脱离该反证假设保留。本章157.2把实际种子接入分类，157.3—157.4则供应任意发送端连续性与原域开放性。第158章将后两项另接环境对偶暴露邻域、正法向标架及横截面，支付每点的原域开放四维图，再推出上述全域结论及实际种子存在。这些全域结论由158的完整推导取得，不以157.4的开放性单独为依据。独立维数上界与第157.5节全部实际物理合同仍分别保留。

[Q157IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.1—114.6：完整原域、纯PR下的严格暴露与紧性、同球刻度和原正延拓预算；IX114.8：原边单位饱和与交换端点传播；IX115.4—115.5：任意原发送列的闭图和整球极限二择；IX116.1—116.2、116.6：原面、准确不交配对、单标签存在及零邻闭包。"
[Q157X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X126.1—126.2：完整原域及实际塌缩的固定边整行达到；X126.5—126.6：保留全域Inj的正扰动、实际对径和least证明；X121实际种子接口与X133固定覆盖根接口各保留全部原前件。"
[Q157XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "XI条件应用145.9：同一个Phi的全静态字典、完整确认菜单和每个混输入的minimum；第145.9节：来源、所有有限复合与纠缠、全旁观CP、事件仪器、记录未来、动态与能量的独立合同；XI140.3—140.4的种子传播另有单尺相容及Conn前件。"
[Q157SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "第127.10节SECTION127.10：完整原来源、所有有限实际联合及全纠缠输入、每个有限旁观者、实际事件和同族仪器、全切口与合法未来、物理钟及Hamiltonian能量合同。"

## 追加锚（本行以下为增补区）

## 158. 每个单标签点的原域开放图册与同原静态分类

### 158.1 完整背景与结论

保留定义157.1的非零有限维实空间 $V$、闭尖生成凸锥 $C$、严格正原单位 $u$，以及整个原 $K=C\cap\{u=1\}$、$P=\operatorname{ext}K$、$\mathcal E=[0,u]_{C^*}$、$\mathcal F_p=F_p$。原最低确认始终为

$$
T_p(x)=\min_{f\in\mathcal F_p}f(x)\quad(p\in P,\ x\in K),\qquad
D_p=\{x\in K:T_p(x)=0\},\qquad S_p=P\cap D_p.
\tag{XII158.1}
$$

全部混输入、全部原效应和全部原确认者保留；$D_p$ 起初是这些确认零集的并。$P_{\rm s}$、$N_p$、$L_p$、$e_p$、$g_p$、$H_p$、$\rho_p$ 均取157.1的定义及其准确供应。正向的共同背景只有完整 EB3、字面纯 PR 和整个原空间的独立上界 $\dim_{\mathbb R}V\le9$。

**定理 158.1（完整原背景的同锥同单位静态等价）。** 在上述原有序空间域中，下列两项等价：

$$
\begin{gathered}
\mathrm{EB3}+\mathrm{PR}+\dim_{\mathbb R}V\le9,\\
\exists\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V
\text{ 实线性双射},\qquad
\Phi(\operatorname{PSD}_3)=C,\qquad u\circ\Phi=\operatorname{Tr}.
\end{gathered}
\tag{XII158.2}
$$

正向背景还推出 $P_{\rm s}=P$、$\dim_{\mathbb R}V=9$，且原 $P$ 是无边界四维拓扑流形。每个原根 $p$ 的实际二步集合

$$
B_2(p)=\bigcup_{q\in S_p}S_q
=\{x\in P:\exists q\in P,\ p\perp q\perp x\}
\tag{XII158.3}
$$

等于整个 $P$；两个不同端点的中间原纯点唯一。原零图连通且直径恰为二。每个 $e_p$ 是整个 $\mathcal F_p$ 的原锥序 least，$T_p(x)=e_p(x)$ 对每个原混输入成立；每条原零边的实际第三点为完整球的反极点，三张确认在整个 $V$ 上和为 $u$。这些均为结论，不是额外前件。证明依次为158.2—158.7；最后才消费149.2的既有分类。

这里不另列连续性假设。定理157.3、157.4已经在同一正向背景中准确支付

$$
\begin{gathered}
P_{\rm s}\ne\varnothing,\qquad P_{\rm s}\text{ 在原 }P\text{ 中开},\\
\forall r\in P_{\rm s}\ \forall(r_i)\subset P,\quad
r_i\to r\Longrightarrow d_H(D_{r_i},D_r)\to0.
\end{gathered}
\tag{XII158.4}
$$

第二行的发送标签不受类型限制。IX116.6还给 $r\in P_{\rm s}\Rightarrow S_r\subset P_{\rm s}$。本章将(XII158.4)用于实际邻点及任意发送列，不将只在单标签列上的连续性充作其替代。

### 158.2 紧闭原关联与整球确认的连续性

**引理 158.2（完整关联与确认映射）。** 原混态关联

$$
\mathcal D=\{(r,x)\in P\times K:x\in D_r\}
\tag{XII158.5}
$$

紧，纯零关系在 $P^2$ 中闭；$y\mapsto e_y$ 从 $P_{\rm s}$ 连续到完整 $V^*$。

证明。PR下整个 $P$ 紧由[IX114.3—114.4][Q158IX]供应。由全部 minimum 达到，$\mathcal D$ 恰是紧集

$$
\{(r,x,f)\in P\times K\times\mathcal E:f(r)=1,\ f(x)=0\}
$$

在前两坐标上的投影；限制到闭集 $P^2$ 得纯零关系闭。这是原全菜单的投影，不是另选零尺后的子关联。

若 $y_i\to y$ 于 $P_{\rm s}$，在紧 $\mathcal E$ 中取任意收敛子列 $e_{y_i}\to f$。有 $f(y)=1$。对任意 $z\in D_y$，(XII158.4)给 $z_i\in D_{y_i}$、$z_i\to z$，故 $f(z)=\lim e_{y_i}(z_i)=0$。于是 $f\in\mathcal A_y=\{e_y\}$，此唯一性由147.1在九维单标签处供应。每个收敛子列都如此；紧性迫整列趋于 $e_y$。有限维度量拓扑给所述连续性，无需 $P_{\rm s}$ 预先闭或紧。证毕。

### 158.3 环境对偶中的单点暴露邻域

令 $W=\ker u$，则 $\dim W=8$。固定任意 $p\in P_{\rm s}$，置 $n_0=g_p|_W$。对 $n\in W^*$ 定义原最小支撑面

$$
\mathfrak F(n)=\operatorname*{argmin}_{x\in K}n(x-p).
\tag{XII158.6}
$$

$g_p(p)=0$、$Z_K(g_p)=\{p\}$，所以 $\mathfrak F(n_0)=\{p\}$。若 $n_0=0$，则 $g_p$ 为 $u$ 的倍数；在 $p$ 评价迫该倍数零，与 $g_p|_{D_p}=1$ 矛盾。因此 $n_0\ne0$。

**引理 158.3（真正环境开的单点支撑区）。** 存在 $n_0$ 在整个八维 $W^*$ 中的开邻域 $O$，使每个 $n\in O$ 的 $\mathfrak F(n)$ 都是单点。记其点为 $s(n)$，则 $s:O\to P$ 连续，且可取 $s(O)\subset P_{\rm s}$。

证明。若不存在这样的邻域，取非零 $n_i\to n_0$，使 $\mathfrak F(n_i)$ 非单点。在整个 $V$ 上定义

$$
\ell_i(x)=n_i(x-u(x)p),\qquad
m_i=\min_K\ell_i,\qquad h_i=\ell_i-m_i u.
\tag{XII158.7}
$$

$\ell_i\to g_p$ 在紧 $K$ 上一致，故 $m_i\to0$、$h_i\to g_p$，且 $M_i=\max_Kh_i\to1$。在充分大的尾部，$0\le h_i/M_i\le1$ 于整个 $K$，经 $C=\mathbb R_{\ge0}K$ 齐次化，得 $h_i/M_i\in\mathcal E$。其最大面含一个原纯极点 $r_i$，满足 $h_i(r_i)=M_i$。于是整个最小面 $\mathfrak F(n_i)$ 包含在实际 $D_{r_i}$ 中。[VII103.2][Q158VII]的原面证明准确适用：该最小面也是严格凸三球 $D_{r_i}$ 的面，非单点迫其为整球。因此

$$
\mathfrak F(n_i)=D_{r_i}.
\tag{XII158.8}
$$

在紧的原 $P$ 中再取 $r_i\to r\in P$。极限评价给 $g_p(r)=1$，即 $r\in S_p\subset P_{\rm s}$。对这些没有预先限制类型的发送标签 $r_i$，定理157.3给 $D_{r_i}\to D_r$。任意 $z\in D_r$ 都有 $z_i\in D_{r_i}$ 趋于它；$h_i(z_i)=0$ 迫 $g_p(z)=0$。故 $D_r\subseteq\{p\}$，违反原 EB3 的非退化性，矛盾。

可令 $O$ 避开零。单点最小面是原纯点，故 $s(O)\subset P$。若 $n_i\to n$ 于 $O$，紧 $K$ 中 $s(n_i)$ 的每个聚点均满足 $n$ 的原最小化不等式，只能等于 $s(n)$；所以 $s$ 连续。因 $s(n_0)=p$ 且定理157.4给 $P_{\rm s}$ 原域开放，缩小 $O$ 即有 $s(O)\subset P_{\rm s}$。证毕。

这里需要的确是 $W^*$ 中的环境开集。仅有四维法向张成空间的连续性不能排除邻近支撑方向暴露非单点原面。上述反证在极限邻点 $r\in S_p$ 使用任意发送端整球连续性，正是157.3的完整量词。

### 158.4 完整原法向的移动正标架

先核对限制到方向空间时的正性和单射性。对每个原纯 $y$，限制把完整 $N_y$ 双射到

$$
\mathcal M_K(y)=\{n\in W^*:n(x-y)\ge0\ (x\in K)\}.
\tag{XII158.9}
$$

逆映射是 $n\mapsto [x\mapsto n(x-u(x)y)]$。若 $0\ne x\in C$，写 $x=u(x)k$、$k\in K$，其值为 $u(x)n(k-y)\ge0$，所以确实回到原 $C^*$，并在 $y$ 为零。另一方面，$L_y$ 的每个元素在 $y$ 为零；若其限制到 $W$ 为零，它是 $a u$，在 $y$ 评价给 $a=0$。故限制在整个 $L_y$ 上单射。记

$$
\Lambda_y=\{h|_W:h\in L_y\},\qquad
\dim\Lambda_y=4\quad(y\in P_{\rm s}).
\tag{XII158.10}
$$

这是极小化法向的符号；通常的外法向取其负。不因归一化另加一维。

**引理 158.4（四张原正效应的连续满标架）。** 在 $p$ 的某个 $P$-开邻域 $U_0\subset P_{\rm s}$ 上，有四张连续原效应 $h_j(y)\in N_y$，组成完整 $L_y$ 的基；$g_p$ 是 $h_j(p)$ 的严格正线性组合。

证明。取标准 $S^2$ 上正四面体的四个顶点 $t_j$，满足 $\sum_{j=1}^4t_j=0$，且这四个向量的关系空间仅由此关系张成。写 $D_p=c_p+B_p\overline B^3$，令

$$
q_j=c_p+B_pt_j,\quad \rho_j=\rho_p(t_j)\ge1,\quad
R=\sum_{j=1}^4\rho_j>0.
$$

147.6的全原空间边效应公式(XII157.12)给

$$
e_{q_j}=\frac{\rho_jg_p+t_j\cdot H_p}{1+\rho_j},\qquad
g_p=\sum_{j=1}^4\frac{1+\rho_j}{R}e_{q_j}.
\tag{XII158.11}
$$

四张效应在完整 $V^*$ 中线性无关。确实，若 $\sum a_je_{q_j}=0$，置 $b_j=a_j/(1+\rho_j)$。$g_p,H_{p,1},H_{p,2},H_{p,3}$ 由原限制同构构成 $L_p$ 的基，比较系数给 $\sum b_jt_j=0$、$\sum b_j\rho_j=0$。前式使全部 $b_j$ 相等，后式因 $R>0$ 使其为零。

对 $p$ 附近的 $y\in P_{\rm s}$，令 $q_j(y)$ 为固定原仿射函数 $t_j\cdot H_p$ 在整个实际 $D_y$ 上的最大点。其在 $D_p$ 的振幅为二，157.3给整球连续性，故附近振幅仍严格正。非恒定仿射函数在非退化仿射欧氏球上有唯一最大点，位于全部原球缘 $S_y$。因此 $q_j(y)$ 定义良好，且 $q_j(p)=q_j$。

这些最大点连续：若 $y_i\to y$，整球连续性使最大值收敛，也使最大点的每个聚点在 $D_y$ 上最大；唯一性识别该聚点。由于 $S_y\subset P_{\rm s}$，引理158.2遂使

$$
h_j(y)=e_{q_j(y)}
\tag{XII158.12}
$$

在完整 $V^*$ 中连续。原零对称给 $y\in D_{q_j(y)}$，所以 $h_j(y)(y)=0$，确为 $N_y$ 中的原正效应。四张在 $p$ 独立，邻近仍独立；$\dim L_y=4$ 使它们张满完整 $L_y$。157.4允许取 $U_0$ 在原 $P$ 中开。

对每个这样的 $y$，严格正系数象限在基映射下的像是 $L_y$ 中的开集，且包含在原 $N_y$ 中。因此每个严格正系数组合都属于完整 $N_y$ 的相对内部。这项正性先在 $V^*$ 中成立，再经已证单射限制到 $W$；没有从球上非负限制臆推原锥正性。证毕。

### 158.5 横截面支付每点的原域开放四维图

**命题 158.5（每个单标签点的开放图册）。** 每个 $p\in P_{\rm s}$ 有一个在原 $P$ 中开的邻域，同胚于四维开球。因此 $P_{\rm s}$ 是 Hausdorff、第二可数的无边界四维拓扑流形。

证明。取引理158.3的 $n_0,O,s$ 和引理158.4的移动基。在八维 $W^*$ 中选 $\Lambda_p$ 的四维线性补空间 $M$，令

$$
\Sigma=n_0+M,\qquad \pi:W^*\to W^*/M.
$$

限制后的四张基连续，故在 $p$ 的较小 $P$-开邻域中仍有 $\Lambda_y\oplus M=W^*$。于是 $\Sigma\cap\Lambda_y$ 恰有一点

$$
a(y)=(\pi|_{\Lambda_y})^{-1}\pi(n_0).
\tag{XII158.13}
$$

用移动基写上述有限维可逆矩阵，矩阵求逆连续，故 $a(y)$ 连续，其基系数也连续。在 $p$ 处，$a(p)=n_0$，系数恰为(XII158.11)的 $(1+\rho_j)/R>0$；缩邻域使全部系数保持严格正。因此 $a(y)$ 是原 $N_y$ 中真实正泛函的限制，不只是其线性张成空间中的一个方向。(XII158.9)给 $y$ 在方向 $a(y)$ 上最小化整个原 $K$。

再缩为 $P$-开 $U\ni p$，使 $a(U)\subset O$。引理158.3的单点最小面于是给

$$
s(a(y))=y\qquad(y\in U).
\tag{XII158.14}
$$

反向若 $n\in\Sigma\cap O$ 充分靠近 $n_0$，连续性给 $y=s(n)\in U$。原最小化不等式使 $x\mapsto n(x-u(x)y)$ 属于 $N_y$，所以 $n\in\Lambda_y$。由 $\Sigma\cap\Lambda_y$ 的唯一性，$n=a(y)$。

在 $\Sigma$ 内取以 $n_0$ 为中心的充分小四维开球 $B$，使 $B\subset O$ 且 $s(B)\subset U$。上面两向恒等式证明 $s$ 和 $a$ 在 $B$ 与

$$
U'=U\cap a^{-1}(B)=s(B)
\tag{XII158.15}
$$

之间互为连续逆。因为 $U$ 在原 $P$ 中开且 $a$ 连续，$U'$ 也在原 $P$ 中开。四维来自 $8-4$；此处没有预先赋予 $P$ 流形结构，也没有使用区域不变性。每个 $p\in P_{\rm s}$ 都能作此构造。Hausdorff和第二可数性由 $P\subset V$ 继承，证毕。

### 158.6 实际二步关联的开闭像与全域覆盖

**命题 158.6（全根二步覆盖与全域单标签）。** 有 $P_{\rm s}=P$，且 $B_2(p)=P$ 对每个原 $p$ 成立；不同端点的共同原零邻点唯一。

证明。先固定 $p\in P_{\rm s}$，定义实际关联及其删根部分

$$
J_p=\{(q,x)\in S_p\times P:x\in S_q\},\qquad
E_p=\{(q,x)\in J_p:x\ne p\}.
\tag{XII158.16}
$$

沿两条原零边的单标签封闭给 $q,x\in P_{\rm s}$。引理158.2使 $J_p$ 闭于紧 $S_p\times P$，故 $J_p$ 紧，评价像恰为 $B_2(p)$，因而 $B_2(p)$ 在原 $P$ 中闭。

下面支付 $E_p$ 的实际局部乘积拓扑，准确复用147.5、149.7—149.10的整球参数与关联机制。固定 $\{u=1\}$ 中原点 $o$ 和 $W$ 上辅助内积。每张仿射椭球的支撑函数唯一写成

$$
\sigma_{D_q}(v)=\max_{x\in D_q}\langle v,x-o\rangle
=\langle v,c_q-o\rangle+\sqrt{\langle v,Q_qv\rangle}
\quad(v\in W),
\tag{XII158.17}
$$

其中 $Q_q\succeq0$ 是 $W$ 上秩三算子。支撑函数的奇部给中心，减去中心后的偶部平方再极化给 $Q_q$；整球 Hausdorff 连续性因此给 $c_q,Q_q$ 连续。这里形状算子在整个八维 $W$ 上定义，其像才是三维移动空间。

在任意 $q_0\in S_p$ 附近，选三个固定向量，使其 $Q_{q_0}$-像独立。邻近仍独立，Gram–Schmidt给到 $\operatorname{im}Q_q$ 的连续等距标架 $U_q:\mathbb R^3\to W$。有限维正半定平方根连续，故

$$
B_q=Q_q^{1/2}U_q,\qquad
D_q=c_q+B_q\overline B^3,\qquad
B_q^\dagger=(B_q^*B_q)^{-1}B_q^*
\tag{XII158.18}
$$

是连续的单射球参数及连续左逆。各球含同一个实际 $p\in S_q$，所以 $w(q)=B_q^\dagger(p-c_q)\in S^2$ 连续。局部可取连续正交变换 $R_q$ 把固定极点 $w_0$ 送到 $w(q)$：将固定的两个切向向量投到 $w(q)^\perp$，在较小邻域Gram–Schmidt，再补 $w(q)$ 即得。于是

$$
(q,z)\longmapsto(q,c_q+B_qR_qz)
\tag{XII158.19}
$$

在 $q_0$ 的一个球面开邻域 $A\subset S_p$ 上给 $J_p$ 的真实局部乘积 $A\times S^2$，逆由连续左逆及 $R_q^{-1}$ 给出，公共极点对应 $p$。删去根截面后，局部为 $A\times(S^2\setminus\{w_0\})$。因此 $E_p$ 以原子空间拓扑是 Hausdorff、第二可数的无边界四维流形。无需不同特征值或全局主轴选择。

考虑评价 $\operatorname{ev}:E_p\to P_{\rm s}$、$(q,x)\mapsto x$。若不同 $q,q'\in S_p$ 有同一像 $x\ne p$，单标签性使 $D_q,D_{q'}$ 不同，却同时包含 $p,x$，违反原球点交规则。因此评价连续单射。其源刚由实际球丛支付四维流形结构，靶的每个点刚由命题158.5支付四维图，且 $P_{\rm s}$ 在原 $P$ 中开。现在才逐坐标应用[Hatcher Theorem 2B.3][Q158H]的区域不变性，得到

$$
\operatorname{ev}(E_p)=B_2(p)\setminus\{p\}
\quad\text{在原 }P\text{ 中开}.
\tag{XII158.20}
$$

还须补回根。取命题158.5给 $p$ 的 $P$-开四球图 $U$，以 $p$ 为坐标中心。$B_2(p)\cap(U\setminus\{p\})$ 既开又闭于连通的穿孔四球 $U\setminus\{p\}$。它非空：任选 $q\in S_p$，完整二球面 $S_q$ 含 $p$，有异于 $p$ 的点趋近 $p$，最终进入原域开集 $U$。故 $U\setminus\{p\}\subset B_2(p)$。实际回走 $p\perp q\perp p$ 又给 $p\in B_2(p)$，所以 $U\subset B_2(p)$。结合(XII158.20)，$B_2(p)$ 在原 $P$ 中开。这正是149.10的删根评价及补根机制，此处其入口为每个单标签点的原域开放图。

由本卷定理151.2的整个原 $P$ 拓扑连通，非空开闭 $B_2(p)$ 只能等于 $P$。但两步的每个终点都在 $P_{\rm s}$，所以 $P_{\rm s}=P$。现在每个原根都是单标签，重复上述论证即得全部 $B_2(p)=P$，并给有限零路连通；没有把拓扑连通直接当成原零图连通。

若 $p\ne x$，共同零邻点存在，且属于 $D_p\cap D_x$；全域单标签使两球不同，点交规则给唯一性。最后验证直径恰二：固定 $p$，取 $q\in S_p$，在完整 $S_q$ 中取 $x\ne p$ 充分靠近 $p$。固定 $T_p$ 连续且 $T_p(p)=1$，故可使 $T_p(x)>0$。$p,x$ 没有零边，却已有两步零路。所以每个根的最大图距离及全图直径都恰为二。证毕。

### 158.7 全方向饱和、完整 minimum 与149.2的逐项应用

**命题 158.7（全部实际三角的共同全空间单位恒等式）。** 对每个原 $p$、每个 $v\in\mathbb R^3$，有 $\rho_p(v)=\|v\|$。对每个原 $f\in\mathcal F_p$，有 $f-e_p\in C^*$。若 $q=c_p+B_pt$、$\|t\|=1$，令 $q^\sharp=c_p-B_pt$，则 $p,q,q^\sharp$ 两两原零正交，并且

$$
e_q+e_{q^\sharp}=u-e_p\quad\text{于整个 }V.
\tag{XII158.21}
$$

证明。命题158.6给不同端点 $p,q$ 的一个实际共同零邻点 $r\in S_p\cap S_q$。因为 $e_q$ 零于整个 $D_q$，其在 $r$ 为零。完整边公式给

$$
e_q(c_p+B_pw)=\frac{\rho_p(t)+t\cdot w}{1+\rho_p(t)},\qquad
\min_{D_p}e_q=\frac{\rho_p(t)-1}{1+\rho_p(t)}.
\tag{XII158.22}
$$

非负性及实际零点 $r$ 迫此 minimum 为零，故 $\rho_p(t)=1$。每个单位方向都单独得到此式，含 $-t$；正齐次给全部非零 $v$ 的结论，$\rho_p(0)=0$ 由定义直接给出。这也是[IX114.8][Q158IX]的真实共同零点与单位预算饱和接口；并未另设三角前提。

对任意原确认 $f$，其补 $h=u-f$ 属于完整 $N_p$，且 $h\le u$。用(XII157.11)的全原锥公式和刚得的 Euclidean gauge，唯一写成

$$
h=\alpha g_p+v\cdot H_p,\qquad
\alpha\ge\|v\|,\qquad
\alpha+\|v\|=\max_Kh\le1.
\tag{XII158.23}
$$

所以 $1-\alpha\ge\|v\|=\rho_p(-v)$，再次用同一个完整正性判据得到

$$
f-e_p=(1-\alpha)g_p-v\cdot H_p\in N_p\subseteq C^*.
\tag{XII158.24}
$$

因 $e_p\in\mathcal F_p$，这就支付全部原混输入的 $T_p(x)=e_p(x)$，没有缩小菜单或把菜单当成单点。

对实际对径两端分别用全空间边公式，得到

$$
e_q=\tfrac12(g_p+t\cdot H_p),\qquad
e_{q^\sharp}=\tfrac12(g_p-t\cdot H_p).
\tag{XII158.25}
$$

相加正是(XII158.21)，等式在整个 $V$ 上成立。在实际 $q^\sharp$ 评价第一式为零，而 $e_q(q)=1$，所以 $q\perp q^\sharp$；另两边来自两点属于 $S_p$。三点不同由零关系非自反性给出。三张原正效应遂和为原 $u$，是数学效应区间中的真实归一三元组。证毕。

**定理158.1的证明。** 由157.3—157.4到命题158.7的推导均只使用完整正向背景。现在逐项消费149.2：原 EB3保留，整个原 $\dim_{\mathbb R}V\le9$ 保留；取

$$
Q=P_{\rm s}=P\ne\varnothing,
\qquad \forall p\in Q:\ S_p\subseteq Q,
\qquad \kappa=1<2.
\tag{XII158.26}
$$

非空及零邻封闭由IX116.6和命题158.6取得；命题158.7对每个 $p\in Q$、每个 $q\in S_p$ 给同一个 $\kappa$ 的全 $V$ 恒等式(XII158.21)。因此149.2的(149.3)—(149.4)每一前件都已支付，得到(XII158.2)中的同原 $C,u$ 双射。该分类所用XI145.2及149.2的饱和机制是既有中间工具，不作为本章另创的分类定理。

反向设有该同一个 $\Phi$。完整静态字典直接由[XI条件应用145.9][Q158XI]、推论149.11及157.5取得。具体地，$V$ 是整个 $\operatorname{Herm}_3$ 的像，故原实维数九；每个原纯点为 $p_v=\Phi(vv^*)$、$\|v\|=1$，其完整原确认菜单为所有 $P_v+B$，$B=Q_vBQ_v$、$0\preceq B\preceq Q_v$。于是对每个原混态 $\Phi\rho$，$T_{p_v}(\Phi\rho)=v^*\rho v$。其完整零集恰为 $v^\perp$ 上全部二阶密度矩阵的像，是非退化仿射闭三球，支付EB3；纯输入时 $T_{p_v}(p_w)=|v^*w|^2=|w^*v|^2$，支付字面纯PR。因全原态、全原效应及全菜单皆由同一双射运输，不是只核对一个子模型。其余正向结论已由158.5—158.7支付。证毕。

### 158.8 同一表示的静态字典、独立合同与几何归属

在定理158.1的共同背景下，157.5的适用条件(XII157.14)已无须另给种子。该节的全部静态字典现在直接适用于同一个 $\Phi$。尤其，置 $P_v=vv^*$、$Q_v=I_3-P_v$、$p_v=\Phi(P_v)$、$f_A(\Phi X)=\operatorname{Tr}(AX)$，则整个原 $K,P,\mathcal E,\mathcal F_p$ 分别是全部密度矩阵、全部秩一射线、全部 $0\preceq A\preceq I_3$ 和完整非单点菜单；并有

$$
\begin{gathered}
\mathcal F_{p_v}=\{f_{P_v+B}:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\},\\
T_{p_v}(\Phi\rho)=\min_{f\in\mathcal F_{p_v}}f(\Phi\rho)
=\operatorname{Tr}(P_v\rho)=v^*\rho v
\quad(\rho\succeq0,\ \operatorname{Tr}\rho=1).
\end{gathered}
\tag{XII158.27}
$$

同一 $B=0$ 达到每个原混态的 minimum。完整 $D_{p_v}$、纯球缘、全部非负质量、原评价、全部有限数学POVM、谱、自对偶、Jordan乘法和全空间球心图均沿157.5及其原来源采用这一相同 $\Phi$，不换表示拼接不同对象。

独立的实际物理范围完整继承157.5所列每个合同及其全部原量词，不再次展开。来源与读回、所有有限实际复合及纠缠输入、每个有限旁观者的CP、事件与同族仪器、记录和全部合法未来及中间切口、物理钟、Hamiltonian、能量与数值 $\hbar$ 均仍分别供应。独立的整个原 $\dim_{\mathbb R}V\le9$ 也仍是正向数学前件；本章未从无维数上界的EB3+PR推出它，亦未以九维载体解释物理时空维数。结论是完整静态单体的同原表示，不是这些实际合同的推导。

本章的承重综合连接是：157的任意发送端整球连续性和原单标签区开放性，先排除环境对偶中非单点支撑面，再以四张真实正法向和横截面构成每个单标签点的原域开放图，随后把既有删根关联评价与补根机制接到151.2的全纯域拓扑连通。147的法向维数、限制同构及全空间边效应，149.7—149.10的椭球参数、球丛及根填充，149.2和XI145.2的既有分类，均作为有条件的中间供应精确使用。有限维紧性、矩阵求逆连续性、正半定平方根、局部正交标架和区域不变性是成熟工具，不另立为独立新结果。155.2已由 $\mathsf{MD}(p)$ 支付单标签、真实三角及单位预算，155.5已给全域 $\mathsf{MD}$ 的无维数上界分类；本章在独立九维上界下先支付图册与全域二步关联，(XII158.24)也取得该既有 $\mathsf{MD}$ 性质，不把此重叠另算一个新分类。这里没有全球新颖性、最少公理数、独立性或严格弱化主张。

几何上，每个原纯点背后是一整颗排除三球；157首先保证球从任何原标签靠近单标签接收点时都不会塌掉，而且单标签区在完整纯态域中开放。若靠近某点互补确认尺的支撑方向仍贴住整颗球，其最大值标签便趋向该点的一个单标签邻点；整球连续性要求球保留，最小支撑却迫它只剩原点，因而矛盾。于是这片环境对偶方向只能接触单个纯点。四张在整个原锥上为正的移动尺给完整法向标架，横切这些四维法向空间，就把单标签点的真实邻域变成原纯态域里开放的四维球。两步零路的删根关联同样有四个自由坐标，区域不变性使它的像开放，紧性使整像闭，穿孔四球的连通性补回根，再由完整纯态域的拓扑连通铺满全域。每条零边遂真的具有共同第三点，这个实际零点逐方向迫原法向预算饱和；球上对径的两张尺在整个原空间恰拼成根尺的补，正好满足149.2的共同单位恒等式，恢复同一个锥和同一个单位上的复三能级静态字典。维数上界和全部实际物理合同仍独立，静态射线与Born最低值本身不制造复合、操作或时间。

[Q158VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2及其证明：完整原效应下的共同暴露、全部原真面穷尽；非单点最小支撑面是实际最大纯标签的整个排除球，不消费全Pair。"
[Q158IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.3—114.4：纯PR下的严格暴露及整个P紧性；114.8：真实共同零点与单位预算；115.5：任意发送列整球极限二择；116.2、116.6：准确重复配对、单标签存在及原零邻封闭。"
[Q158XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "XI145.2：完整EB3+Inj+整个原空间九维的既有分类；条件应用145.9：同一个Phi的全原态、全效应、完整确认菜单和每混输入minimum。"
[Q158H]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology, Theorem 2B.3，印刷页172：欧氏开源上的同维连续单射有开像；本章仅在源、靶四维图均支付后逐坐标应用。"

## 追加锚（本行以下为增补区）

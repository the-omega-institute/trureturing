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

## 146. 纯局部极小的全域障碍与同根同阈值闭端点

### 146.1 原域、完整面与端点命题

**定义 146.1（同一原根的读数与二步载体）。** 本章的146.*均属本卷 XII；
[XI145—146][Q146XI]仍指前卷的九维分类与有限层正规性结论。
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
\tag{XII146.1}
$$

所有标签遍历整个原 $P$，第二变量遍历整个原 $K$，包括全部混态。
以下假设完整 EB3 与完整纯 PR；前者规定每个完整 $D_p$ 仿射等价于闭三球，
后者规定 $T_p(q)=T_q(p)$ 对全部原纯对成立。
事先固定同一个 $o\in P$，记

$$
h=T_o,\qquad A=D_o,\qquad S=S_o,\qquad
B=\bigcup_{s\in S}D_s,\qquad Q(o)=P\cap B.
\tag{XII146.2}
$$

复用 [IX114.1][Q146IX]的完整菜单紧性与达到性：严格正性使 $K$ 紧，生成性使
$K$ 张成 $V$ 且 $\operatorname{aff}K=\{u=1\}$；在从 $K$ 选出的线性基上评价，
闭效应区间 $\mathcal E$ 有界而紧。$\mathcal F_p$ 闭且含 $u$，所以每个 minimum 达到。
这也把 $K$ 上全部有界仿射效应与同一个原区间 $\mathcal E$ 对应起来，未缩小菜单。

复用 [VII103.2][Q146Faces]、[IX114.2及116.1][Q146IX]的完整原面结果：
每个 $D_p$ 是紧暴露真面，全部非空真面只有原纯单点或完整 $D_p$。
对任何这样的面 $F$，$\operatorname{ext}F=P\cap F$；完整三球的这个集合是其整个相对边界，
同胚于 $S^2$。特别地，每个非空真暴露面的纯缘连通。
这些是原面分类的前两项，不使用另需全 Pair 的最后一项。
三维 $D_p$ 是真面，故 $\dim\operatorname{aff}K\ge4$。

纯集的紧性准确取自 IX114.4。该结论由纯 PR、IX114.3 的原端点暴露和原菜单紧性推出，
不以 $P$ 已闭为前提，不调用 qutrit 表示。
这三项供应——紧 $P$、每个真暴露面的连通纯缘、维数至少二——是下面局部极小论证的全部凸几何输入。

### 146.2 有实际消费者的局部极小桥梁

**引理 146.2（紧极点集上的仿射局部极小）。** 设 $K_0$ 是非空有限维紧凸集，
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
\tag{XII146.3}
$$

在模去常量的仿射函数空间中，保持此严格间隙的 $b$ 构成非空开集。
由于 $d\ge2$ 且 $a$ 的线性部分非零，可使 $b$ 的线性部分不属于 $a$ 的线性部分所张成的直线：
若原分离尺平行，就沿一个独立方向作足够小的扰动；紧 $Q\cup\{p\}$ 使严格间隙保留。
这里没有要求 $p$ 本身暴露。

对 $t\ge0$ 置

$$
g_t=b-ta,\qquad F_t=\operatorname{argmax}_{K_0}g_t,\qquad
M_t=P_0\cap F_t=\operatorname{argmax}_{P_0}g_t.
\tag{XII146.4}
$$

非平行性使每个 $g_t$ 在 $\operatorname{aff}K_0$ 非恒定，故 $F_t$ 总是非空紧真暴露面。
成熟的极点—面传递给 $\operatorname{ext}F_t=P_0\cap F_t$，紧面的极点存在性又给
$M_t\ne\varnothing$ 以及 (XII146.4) 最后的等号。
假设使 $M_t$ 连通；紧 $P_0$ 与闭 $F_t$ 使 $M_t$ 紧。

若 $x\in Q$ 且 $a(x)\ge\alpha$，对每个 $t\ge0$ 都有

$$
g_t(x)\le b(x)-t\alpha<b(p)-t\alpha=g_t(p).
\tag{XII146.5}
$$

因此全部 $M_t$ 均包含于两个互不相交的相对开集
$U$ 与 $W=\{x\in P_0:a(x)<\alpha\}$ 的并。
这给出不能越过 $U$ 边界的具体障碍，而非假定某条极大点轨道连续。
由 (XII146.3)，$M_0\subseteq U$。
再选 $T>0$，使

$$
T(\alpha-a(q))>\max_{P_0}b-b(q).
\tag{XII146.6}
$$

若 $a(x)\ge\alpha$，则
$g_T(x)\le\max_{P_0}b-T\alpha<b(q)-Ta(q)=g_T(q)$，
所以 $M_T\subseteq W$。

考虑整个极大点图

$$
G=\{(t,x)\in[0,T]\times P_0:x\in M_t\}.
\tag{XII146.7}
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

**命题 146.3（一维非恒定情形不能补入引理）。** 取
$K_0=[0,1]$、$P_0=\{0,1\}$、$a(x)=x$。
所有非空真暴露面的纯缘都连通，且 $P_0$ 紧，但 $p=1$ 是非全局局部极小点。

证明。真暴露面只有两个端点，纯缘为单点。$1$ 在 $P_0$ 中孤立，所以是局部极小点；
$a(0)<a(1)$ 排除全局极小性。
任何在 $1$ 严格大于 $0$ 的仿射分离尺都形如 $b(x)=\beta x+\gamma$，$\beta>0$。
当 $t=\beta$ 时，$b-ta$ 恒定，极大面变成整个 $K_0$，其极点集不连通。
这正是引理中非平行扰动所排除的退化。零维或常量情形没有这个障碍；
原 EB3 应用已有 $\dim\operatorname{aff}K\ge4$，不落入本反例。证毕。

### 146.3 原 minimum 的局部极小转移与真正低端点

**定理 146.4（原比较的内部无纯局部极小与端点逼近）。** 在定义146.1的完整 EB3、纯 PR 域，
对每个事先固定的原 $o$，$h=T_o$ 在 $P$ 上没有读数处于 $(0,1)$ 的局部极小点。
对任意 $0<\varepsilon<1$，每个满足 $h(p)=\varepsilon$ 的原纯点都有实际原纯点列

$$
p_n\longrightarrow p,\qquad 0<h(p_n)<\varepsilon,\qquad
h(p_n)\longrightarrow\varepsilon.
\tag{XII146.8}
$$

因此，在原纯集的相对拓扑中，

$$
\begin{gathered}
\{p\in P:0<h(p)\le\varepsilon\}
\subseteq\overline{\{p\in P:0<h(p)<\varepsilon\}}^{\,P},\\
\overline{\{p\in P:h(p)<\varepsilon\}}^{\,P}
=\{p\in P:h(p)\le\varepsilon\}.
\end{gathered}
\tag{XII146.9}
$$

证明。定义146.1逐项供应引理146.2的紧纯集、全部真暴露面连通纯缘及维数前件。
选辅助范数，紧 $\mathcal E$ 给 $L=\max_{f\in\mathcal E}\|f\|_\ast<\infty$。
每张原效应满足 $|f(x)-f(y)|\le L\|x-y\|$；分别取整个 $\mathcal F_o$ 的 minimum 得

$$
|h(x)-h(y)|\le L\|x-y\|\qquad(x,y\in K).
\tag{XII146.10}
$$

这是固定根、第二变量的连续性，不涉及移动确认族的选择。

反设 $p\in P$ 是 $h|_P$ 的局部极小点，$\mu=h(p)\in(0,1)$。
原 minimum 达到，故取同一完整菜单中的 $f\in\mathcal F_o$，使 $f(p)=\mu$。
在同一纯邻域内，

$$
f(x)\ge h(x)\ge\mu=f(p).
\tag{XII146.11}
$$

因此这张真实原仿射效应 $f$ 在 $P$ 上也于 $p$ 局部极小。
$f(o)=1>\mu$ 使其非恒定；引理146.2给 $f\ge\mu$ 于整个 $K$。
现在才定义真实原线性泛函

$$
f'=\frac{f-\mu u}{1-\mu}.
\tag{XII146.12}
$$

分母正。在整个 $K$ 上，$0\le f'\le1$，且 $f'(o)=1$、$f'(p)=0$。
对任意非零原 $c\in C$，严格正性给 $u(c)>0$，且 $k=c/u(c)\in K$，于是

$$
0\le f'(c)=u(c)f'(k)\le u(c).
\tag{XII146.13}
$$

在 $c=0$ 也成立，所以 $f'\in[0,u]_{C^\ast}=\mathcal E$，进而 $f'\in\mathcal F_o$。
这与 $0<\mu=h(p)\le f'(p)=0$ 矛盾。
归一化在全部原锥上合法，未使用面效应延拓、least 或新的确认菜单。

若 $h(p)=\varepsilon\in(0,1)$，不存在局部极小意味着每个纯邻域都含 $h<\varepsilon$ 的点。
将该邻域同时限制在 $\{h>\varepsilon/2\}$ 及半径 $1/n$ 的环境球内，选原纯 $p_n$，
就得到 (XII146.8)；连续性给读数收敛。
严格带内的点本身已在其闭包中，故有 (XII146.9) 第一项。
第二项的 $h=0$ 点本就在 $\{h<\varepsilon\}$ 中，$h=\varepsilon$ 点由刚构造的列逼近；
反包含由连续性和 $\{h\le\varepsilon\}$ 的相对闭性成立。
这并不由逼近本身供应零层 $S$ 在任意指定载体中的成员资格。证毕。

### 146.4 消费原真实标签返回的闭高端点

**定理 146.5（同根、同阈值的两个闭带）。** 在定义146.1的完整原域中，另假设
对这个事先固定的同一个 $o$ 成立的原条件 $L_\varepsilon(o)$，$0<\varepsilon<1$：

$$
\forall z\in P:\quad 0<h(z)<\varepsilon
\ \Longrightarrow\ \exists s\in P:\ T_o(s)=T_z(s)=0.
\tag{XII146.14}
$$

则对定义146.1的同一个 $B$ 有

$$
\{p\in P:h(p)\le\varepsilon\}
\ \cup\ \{p\in P:h(p)\ge1-\varepsilon\}\ \subseteq B.
\tag{XII146.15}
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
\tag{XII146.16}
$$

完整原 $S\cong S^2$、$K$、$\mathcal E$ 均紧，评价连续，故 $\Gamma$ 紧。
原 minimum 达到使该投影准确等于 $B$，包括每个 $D_s$ 的全部混态；所以 $B$ 在 $K$ 中闭。
这不需要整族球的连续性或移动标签选择。

由 (XII146.14) 和零对称，$0<h<\varepsilon$ 的全部纯点在 $B$。
定理146.4的真实原纯逼近列与 $B$ 闭性补上 $h=\varepsilon$。
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
\tag{XII146.17}
$$

这正是 (XII145.27) 的原互补不等式。故每个实际 $x\in S_q$ 都满足
$0\le h(x)\le1-h(q)\le\varepsilon$，已由闭低带进入 $B$。
至此才得到整个 $S_q\subseteq B$，进而消费上述推论145.4的 $C_q$、反向比较和真实标签返回，
得到 $q\in B$。这里没有要求存在读数恰为 $1-h(q)$ 的伙伴，也没有用假想的伙伴标签合同。
原严格高带已含 $h=1$；同一不等式也处理这一情形，无需另证 $h=1$ 的纯点刻画。
根与阈值从始至终未变。证毕。

**推论 146.6（临界阈值与尚余的开中带）。** 在定理146.5的相同前件下，
若 $\varepsilon=1/2$，则 $P\subseteq B$，从而同一根满足 X133.1 的 $\mathsf D_2(o)$。
若 $0<\varepsilon<1/2$，(XII146.15) 唯一尚未支付的读数范围是

$$
\varepsilon<h(p)<1-\varepsilon.
\tag{XII146.18}
$$

若 $\varepsilon>1/2$，全覆盖已经由 (XII145.25) 的两条严格带及其另付零层取得，
不作为新的覆盖增量。

证明。临界值时两个闭区间覆盖 $[0,1]$，而 $0\le h\le1$，故 $P\subseteq B$。
每个 $q\in P\cap B$ 都有实际同一个 $s\in S$ 满足 $q\in D_s$；
零对称给 $o\perp s\perp q$，包括 $q=o$，所以原 $\mathsf D_2(o)$ 的共同邻点支成立。
若需要静态表示，此时才可直接消费 [X133.6][Q146X]：其原前件为完整 EB3 加一个固定根的
$\mathsf D_2(o)$，结论为同原锥、同原单位的实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\operatorname{PSD}_3)=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XII146.19}
$$

X133.6的链先由该固定覆盖根取得全部原三角，再调用 IX120.4—120.5及116.17—116.18的既有分类。
这里未把表示预用于引理146.2、定理146.4或146.5；(XII146.19) 是该旧结果的条件应用，
其前件仍包含同根 $L_{1/2}(o)$，不是 EB3 加纯 PR 的自动分类。

小于临界值时，两个闭带的补集正是 (XII146.18)。这只说明所述包含关系的剩余范围，
不声称中带必有点或必不在 $B$。
大于临界值时，$h=0$ 由 $S$ 处理；$h>0$ 且不在严格低带意味着
$h\ge\varepsilon>1-\varepsilon$，已在原严格高带，故覆盖早由145.4成立。证毕。

### 146.5 数学来源与剩余条件

**约定 146.7（归属、复用和未付命题）。** 本章的承重连接是引理146.2到
(XII146.11)—(XII146.13) 的全原菜单归一化，再到真实低端点和整个 $S_q$ 的闭带供应。
引理被定理146.4消费，后者被定理146.5的低端点消费；
低端点再支付145.4实际返回接口所需的整个原 $S_q\subseteq B$。
这是 `repo-derived` 的纸面推导归属，不主张外部精确先例已穷尽或全球原创。

有限维 Carathéodory、严格分离、紧凸面的极点存在与极点—面传递、
紧映射的连通纤维论证均为成熟中间工具。
[Feinberg、Kasyanov、Voorneveld，§1、Definition 1.1前的 Berge 最大值定理][Q146B]
给连续目标、连续非空紧值可行对应的连续最优值和上半连续紧值最优对应；
本章可行集固定为 $P_0$，目标取 $ta-b$，其紧图性质也已由闭不等式直接证明。
该文献结论本身不支付连通极大点纤维、连续选择或本章的仿射局部极小结论。
原始 Berge 书第116页的独立文本与本引理的外部精确先例在此不作已核断言。
[Landsman，§1.3、式(1.4)—(1.9)][Q146L]提供完整仿射效应的原比较背景，
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
在 $0<\varepsilon<1/2$ 下补付 (XII146.18) 还需额外论证。
全过程不预用 Conn、Inj、整个空间九维、MC、全 Pair、least 或静态分类；
只在推论146.6已付覆盖之后复用旧分类。
结论属于原有限维态—效应几何，不支付实际来源、仪器、有限复合或物理时间的实现条件。

[Q146IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.1—114.2：同原紧基、完整菜单、达到性及原面；114.3—114.4：纯PR下的端点暴露与纯紧性；116.1及式(IX116.2)：完整相对纯球缘；120.4—120.5、116.17—116.18：既有条件分类。"
[Q146Faces]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2：共同零确认、全部非空真面穷尽及其不依赖Pair的证明；全对结论另列Pair前件。"
[Q146X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X133.1：同一固定根的D2；133.6：完整EB3加一个覆盖根的全部三角与同原静态分类。"
[Q146XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "XI145.2：EB3+Conn或Inj+整个原V九维；XI146.2—146.4：EB3+Conn+ZC的有限层推进；146.6：零边不变与全域统一界的剩余条件。"
[Q146B]: https://arxiv.org/html/1309.7708v1 "E. A. Feinberg, P. O. Kasyanov, M. Voorneveld, Berge's Maximum Theorem for Noncompact Image Sets，§1中Definition 1.1前的经典紧值最大值定理。"
[Q146L]: https://arxiv.org/html/quant-ph/9603005v2 "N. P. Landsman, Poisson spaces with a transition probability，§1.3、式(1.4)—(1.9)：全仿射效应比较、零对称及另列的纯数值互惠。"

## 追加锚

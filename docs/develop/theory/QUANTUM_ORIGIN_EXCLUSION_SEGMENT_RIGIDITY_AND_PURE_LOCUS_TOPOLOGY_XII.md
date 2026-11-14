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

## 147. 纯局部极小的全域障碍与同根同阈值闭端点

### 147.1 原域、完整面与端点命题

**定义 147.1（同一原根的读数与二步载体）。** 本章的147.*均属本卷 XII；
[XI145—146][Q147XI]仍指前卷的九维分类与有限层正规性结论。
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
\tag{XII147.1}
$$

所有标签遍历整个原 $P$，第二变量遍历整个原 $K$，包括全部混态。
以下假设完整 EB3 与完整纯 PR；前者规定每个完整 $D_p$ 仿射等价于闭三球，
后者规定 $T_p(q)=T_q(p)$ 对全部原纯对成立。
事先固定同一个 $o\in P$，记

$$
h=T_o,\qquad A=D_o,\qquad S=S_o,\qquad
B=\bigcup_{s\in S}D_s,\qquad Q(o)=P\cap B.
\tag{XII147.2}
$$

复用 [IX114.1][Q147IX]的完整菜单紧性与达到性：严格正性使 $K$ 紧，生成性使
$K$ 张成 $V$ 且 $\operatorname{aff}K=\{u=1\}$；在从 $K$ 选出的线性基上评价，
闭效应区间 $\mathcal E$ 有界而紧。$\mathcal F_p$ 闭且含 $u$，所以每个 minimum 达到。
这也把 $K$ 上全部有界仿射效应与同一个原区间 $\mathcal E$ 对应起来，未缩小菜单。

复用 [VII103.2][Q147Faces]、[IX114.2及116.1][Q147IX]的完整原面结果：
每个 $D_p$ 是紧暴露真面，全部非空真面只有原纯单点或完整 $D_p$。
对任何这样的面 $F$，$\operatorname{ext}F=P\cap F$；完整三球的这个集合是其整个相对边界，
同胚于 $S^2$。特别地，每个非空真暴露面的纯缘连通。
这些是原面分类的前两项，不使用另需全 Pair 的最后一项。
三维 $D_p$ 是真面，故 $\dim\operatorname{aff}K\ge4$。

纯集的紧性准确取自 IX114.4。该结论由纯 PR、IX114.3 的原端点暴露和原菜单紧性推出，
不以 $P$ 已闭为前提，不调用 qutrit 表示。
这三项供应——紧 $P$、每个真暴露面的连通纯缘、维数至少二——是下面局部极小论证的全部凸几何输入。

### 147.2 有实际消费者的局部极小桥梁

**引理 147.2（紧极点集上的仿射局部极小）。** 设 $K_0$ 是非空有限维紧凸集，
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
\tag{XII147.3}
$$

在模去常量的仿射函数空间中，保持此严格间隙的 $b$ 构成非空开集。
由于 $d\ge2$ 且 $a$ 的线性部分非零，可使 $b$ 的线性部分不属于 $a$ 的线性部分所张成的直线：
若原分离尺平行，就沿一个独立方向作足够小的扰动；紧 $Q\cup\{p\}$ 使严格间隙保留。
这里没有要求 $p$ 本身暴露。

对 $t\ge0$ 置

$$
g_t=b-ta,\qquad F_t=\operatorname{argmax}_{K_0}g_t,\qquad
M_t=P_0\cap F_t=\operatorname{argmax}_{P_0}g_t.
\tag{XII147.4}
$$

非平行性使每个 $g_t$ 在 $\operatorname{aff}K_0$ 非恒定，故 $F_t$ 总是非空紧真暴露面。
成熟的极点—面传递给 $\operatorname{ext}F_t=P_0\cap F_t$，紧面的极点存在性又给
$M_t\ne\varnothing$ 以及 (XII147.4) 最后的等号。
假设使 $M_t$ 连通；紧 $P_0$ 与闭 $F_t$ 使 $M_t$ 紧。

若 $x\in Q$ 且 $a(x)\ge\alpha$，对每个 $t\ge0$ 都有

$$
g_t(x)\le b(x)-t\alpha<b(p)-t\alpha=g_t(p).
\tag{XII147.5}
$$

因此全部 $M_t$ 均包含于两个互不相交的相对开集
$U$ 与 $W=\{x\in P_0:a(x)<\alpha\}$ 的并。
这给出不能越过 $U$ 边界的具体障碍，而非假定某条极大点轨道连续。
由 (XII147.3)，$M_0\subseteq U$。
再选 $T>0$，使

$$
T(\alpha-a(q))>\max_{P_0}b-b(q).
\tag{XII147.6}
$$

若 $a(x)\ge\alpha$，则
$g_T(x)\le\max_{P_0}b-T\alpha<b(q)-Ta(q)=g_T(q)$，
所以 $M_T\subseteq W$。

考虑整个极大点图

$$
G=\{(t,x)\in[0,T]\times P_0:x\in M_t\}.
\tag{XII147.7}
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

**命题 147.3（一维非恒定情形不能补入引理）。** 取
$K_0=[0,1]$、$P_0=\{0,1\}$、$a(x)=x$。
所有非空真暴露面的纯缘都连通，且 $P_0$ 紧，但 $p=1$ 是非全局局部极小点。

证明。真暴露面只有两个端点，纯缘为单点。$1$ 在 $P_0$ 中孤立，所以是局部极小点；
$a(0)<a(1)$ 排除全局极小性。
任何在 $1$ 严格大于 $0$ 的仿射分离尺都形如 $b(x)=\beta x+\gamma$，$\beta>0$。
当 $t=\beta$ 时，$b-ta$ 恒定，极大面变成整个 $K_0$，其极点集不连通。
这正是引理中非平行扰动所排除的退化。零维或常量情形没有这个障碍；
原 EB3 应用已有 $\dim\operatorname{aff}K\ge4$，不落入本反例。证毕。

### 147.3 原 minimum 的局部极小转移与真正低端点

**定理 147.4（原比较的内部无纯局部极小与端点逼近）。** 在定义147.1的完整 EB3、纯 PR 域，
对每个事先固定的原 $o$，$h=T_o$ 在 $P$ 上没有读数处于 $(0,1)$ 的局部极小点。
对任意 $0<\varepsilon<1$，每个满足 $h(p)=\varepsilon$ 的原纯点都有实际原纯点列

$$
p_n\longrightarrow p,\qquad 0<h(p_n)<\varepsilon,\qquad
h(p_n)\longrightarrow\varepsilon.
\tag{XII147.8}
$$

因此，在原纯集的相对拓扑中，

$$
\begin{gathered}
\{p\in P:0<h(p)\le\varepsilon\}
\subseteq\overline{\{p\in P:0<h(p)<\varepsilon\}}^{\,P},\\
\overline{\{p\in P:h(p)<\varepsilon\}}^{\,P}
=\{p\in P:h(p)\le\varepsilon\}.
\end{gathered}
\tag{XII147.9}
$$

证明。定义147.1逐项供应引理147.2的紧纯集、全部真暴露面连通纯缘及维数前件。
选辅助范数，紧 $\mathcal E$ 给 $L=\max_{f\in\mathcal E}\|f\|_\ast<\infty$。
每张原效应满足 $|f(x)-f(y)|\le L\|x-y\|$；分别取整个 $\mathcal F_o$ 的 minimum 得

$$
|h(x)-h(y)|\le L\|x-y\|\qquad(x,y\in K).
\tag{XII147.10}
$$

这是固定根、第二变量的连续性，不涉及移动确认族的选择。

反设 $p\in P$ 是 $h|_P$ 的局部极小点，$\mu=h(p)\in(0,1)$。
原 minimum 达到，故取同一完整菜单中的 $f\in\mathcal F_o$，使 $f(p)=\mu$。
在同一纯邻域内，

$$
f(x)\ge h(x)\ge\mu=f(p).
\tag{XII147.11}
$$

因此这张真实原仿射效应 $f$ 在 $P$ 上也于 $p$ 局部极小。
$f(o)=1>\mu$ 使其非恒定；引理147.2给 $f\ge\mu$ 于整个 $K$。
现在才定义真实原线性泛函

$$
f'=\frac{f-\mu u}{1-\mu}.
\tag{XII147.12}
$$

分母正。在整个 $K$ 上，$0\le f'\le1$，且 $f'(o)=1$、$f'(p)=0$。
对任意非零原 $c\in C$，严格正性给 $u(c)>0$，且 $k=c/u(c)\in K$，于是

$$
0\le f'(c)=u(c)f'(k)\le u(c).
\tag{XII147.13}
$$

在 $c=0$ 也成立，所以 $f'\in[0,u]_{C^\ast}=\mathcal E$，进而 $f'\in\mathcal F_o$。
这与 $0<\mu=h(p)\le f'(p)=0$ 矛盾。
归一化在全部原锥上合法，未使用面效应延拓、least 或新的确认菜单。

若 $h(p)=\varepsilon\in(0,1)$，不存在局部极小意味着每个纯邻域都含 $h<\varepsilon$ 的点。
将该邻域同时限制在 $\{h>\varepsilon/2\}$ 及半径 $1/n$ 的环境球内，选原纯 $p_n$，
就得到 (XII147.8)；连续性给读数收敛。
严格带内的点本身已在其闭包中，故有 (XII147.9) 第一项。
第二项的 $h=0$ 点本就在 $\{h<\varepsilon\}$ 中，$h=\varepsilon$ 点由刚构造的列逼近；
反包含由连续性和 $\{h\le\varepsilon\}$ 的相对闭性成立。
这并不由逼近本身供应零层 $S$ 在任意指定载体中的成员资格。证毕。

### 147.4 消费原真实标签返回的闭高端点

**定理 147.5（同根、同阈值的两个闭带）。** 在定义147.1的完整原域中，另假设
对这个事先固定的同一个 $o$ 成立的原条件 $L_\varepsilon(o)$，$0<\varepsilon<1$：

$$
\forall z\in P:\quad 0<h(z)<\varepsilon
\ \Longrightarrow\ \exists s\in P:\ T_o(s)=T_z(s)=0.
\tag{XII147.14}
$$

则对定义147.1的同一个 $B$ 有

$$
\{p\in P:h(p)\le\varepsilon\}
\ \cup\ \{p\in P:h(p)\ge1-\varepsilon\}\ \subseteq B.
\tag{XII147.15}
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
\tag{XII147.16}
$$

完整原 $S\cong S^2$、$K$、$\mathcal E$ 均紧，评价连续，故 $\Gamma$ 紧。
原 minimum 达到使该投影准确等于 $B$，包括每个 $D_s$ 的全部混态；所以 $B$ 在 $K$ 中闭。
这不需要整族球的连续性或移动标签选择。

由 (XII147.14) 和零对称，$0<h<\varepsilon$ 的全部纯点在 $B$。
定理147.4的真实原纯逼近列与 $B$ 闭性补上 $h=\varepsilon$。
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
\tag{XII147.17}
$$

这正是 (XII145.27) 的原互补不等式。故每个实际 $x\in S_q$ 都满足
$0\le h(x)\le1-h(q)\le\varepsilon$，已由闭低带进入 $B$。
至此才得到整个 $S_q\subseteq B$，进而消费上述推论145.4的 $C_q$、反向比较和真实标签返回，
得到 $q\in B$。这里没有要求存在读数恰为 $1-h(q)$ 的伙伴，也没有用假想的伙伴标签合同。
原严格高带已含 $h=1$；同一不等式也处理这一情形，无需另证 $h=1$ 的纯点刻画。
根与阈值从始至终未变。证毕。

**推论 147.6（临界阈值与尚余的开中带）。** 在定理147.5的相同前件下，
若 $\varepsilon=1/2$，则 $P\subseteq B$，从而同一根满足 X133.1 的 $\mathsf D_2(o)$。
若 $0<\varepsilon<1/2$，(XII147.15) 唯一尚未支付的读数范围是

$$
\varepsilon<h(p)<1-\varepsilon.
\tag{XII147.18}
$$

若 $\varepsilon>1/2$，全覆盖已经由 (XII145.25) 的两条严格带及其另付零层取得，
不作为新的覆盖增量。

证明。临界值时两个闭区间覆盖 $[0,1]$，而 $0\le h\le1$，故 $P\subseteq B$。
每个 $q\in P\cap B$ 都有实际同一个 $s\in S$ 满足 $q\in D_s$；
零对称给 $o\perp s\perp q$，包括 $q=o$，所以原 $\mathsf D_2(o)$ 的共同邻点支成立。
若需要静态表示，此时才可直接消费 [X133.6][Q147X]：其原前件为完整 EB3 加一个固定根的
$\mathsf D_2(o)$，结论为同原锥、同原单位的实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\operatorname{PSD}_3)=C,\qquad u\circ\Phi=\operatorname{Tr}.
\tag{XII147.19}
$$

X133.6的链先由该固定覆盖根取得全部原三角，再调用 IX120.4—120.5及116.17—116.18的既有分类。
这里未把表示预用于引理147.2、定理147.4或147.5；(XII147.19) 是该旧结果的条件应用，
其前件仍包含同根 $L_{1/2}(o)$，不是 EB3 加纯 PR 的自动分类。

小于临界值时，两个闭带的补集正是 (XII147.18)。这只说明所述包含关系的剩余范围，
不声称中带必有点或必不在 $B$。
大于临界值时，$h=0$ 由 $S$ 处理；$h>0$ 且不在严格低带意味着
$h\ge\varepsilon>1-\varepsilon$，已在原严格高带，故覆盖早由145.4成立。证毕。

### 147.5 数学来源与剩余条件

**约定 147.7（归属、复用和未付命题）。** 本章的承重连接是引理147.2到
(XII147.11)—(XII147.13) 的全原菜单归一化，再到真实低端点和整个 $S_q$ 的闭带供应。
引理被定理147.4消费，后者被定理147.5的低端点消费；
低端点再支付145.4实际返回接口所需的整个原 $S_q\subseteq B$。
这是 `repo-derived` 的纸面推导归属，不主张外部精确先例已穷尽或全球原创。

有限维 Carathéodory、严格分离、紧凸面的极点存在与极点—面传递、
紧映射的连通纤维论证均为成熟中间工具。
[Feinberg、Kasyanov、Voorneveld，§1、Definition 1.1前的 Berge 最大值定理][Q147B]
给连续目标、连续非空紧值可行对应的连续最优值和上半连续紧值最优对应；
本章可行集固定为 $P_0$，目标取 $ta-b$，其紧图性质也已由闭不等式直接证明。
该文献结论本身不支付连通极大点纤维、连续选择或本章的仿射局部极小结论。
原始 Berge 书第116页的独立文本与本引理的外部精确先例在此不作已核断言。
[Landsman，§1.3、式(1.4)—(1.9)][Q147L]提供完整仿射效应的原比较背景，
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
在 $0<\varepsilon<1/2$ 下补付 (XII147.18) 还需额外论证。
全过程不预用 Conn、Inj、整个空间九维、MC、全 Pair、least 或静态分类；
只在推论147.6已付覆盖之后复用旧分类。
结论属于原有限维态—效应几何，不支付实际来源、仪器、有限复合或物理时间的实现条件。

[Q147IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX114.1—114.2：同原紧基、完整菜单、达到性及原面；114.3—114.4：纯PR下的端点暴露与纯紧性；116.1及式(IX116.2)：完整相对纯球缘；120.4—120.5、116.17—116.18：既有条件分类。"
[Q147Faces]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2：共同零确认、全部非空真面穷尽及其不依赖Pair的证明；全对结论另列Pair前件。"
[Q147X]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_X.md "X133.1：同一固定根的D2；133.6：完整EB3加一个覆盖根的全部三角与同原静态分类。"
[Q147XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md "XI145.2：EB3+Conn或Inj+整个原V九维；XI146.2—146.4：EB3+Conn+ZC的有限层推进；146.6：零边不变与全域统一界的剩余条件。"
[Q147B]: https://arxiv.org/html/1309.7708v1 "E. A. Feinberg, P. O. Kasyanov, M. Voorneveld, Berge's Maximum Theorem for Noncompact Image Sets，§1中Definition 1.1前的经典紧值最大值定理。"
[Q147L]: https://arxiv.org/html/quant-ph/9603005v2 "N. P. Landsman, Poisson spaces with a transition probability，§1.3、式(1.4)—(1.9)：全仿射效应比较、零对称及另列的纯数值互惠。"

## 追加锚

# QUANTUM ORIGIN: BINARY TANGENT CLOSURE AND GLOBAL NONCOLLAPSE XIII

> **永久读法。** 本卷是 `generic-v1` 可读取的理论参考输入。合入后的正文、编号和追加锚只增不减；修订与勘误另写在末尾追加区，不改既有字节。本文给出普通数学定义、定理与纸面证明，未经 Lean kernel 验证；不以散文代替形式化真源。

本卷承接[前卷 XII 第159章](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md#159-有限量子面实际面非塌缩与任意有限秩的同原重建)。生产上下文为 `formal-thinking-and-answer` 与 `theory-volume-template`；数学正文由 Codex（GPT-6 模型族）单一作者组织。文献定理、前卷纸面结果与本卷几何综合在各自使用处区分，不赋予它们 Lean 认证或模型多样性含义。

## 160. 实际二元球的切方向闭合与同原有限量子重建

本章把第159章的实际 qutrit 三点面条件 L3 换成二元球之间的切方向条件 TC。新的完整结论是：在下述有限实有序锥域上，L2、TC、NC 当且仅当同一个原锥与原单位具有有限复矩阵的迹归一化序表示。TC 恰好供应成熟 Hermitian Veronesean cap 分类的 H3；分类之后的原单位归一化和原邻点排核沿用第159章的证明。平衡商的 $m=3$ 实例满足全部 L2 与 TC，却有实际三点面塌缩，因而在加 NC 之前严格区分 TC 与 L3。

### 160.1 原域、完整概率菜单和内禀二元切方向

**定义 160.1（全部原对象与实际面）。** 设 $V\ne0$ 为有限维实向量空间，$C\subset V$ 为闭、尖、生成凸锥，$u\in V^\ast$ 在 $C\setminus\{0\}$ 上严格正。始终取

$$
\begin{gathered}
C^\ast=\{f\in V^\ast:f(C)\subseteq\mathbb R_{\ge0}\},\qquad
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\\
\mathcal E=[0,u]_{C^\ast},\qquad
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\}.
\end{gathered}
\tag{XIII160.1}
$$

这里 $p$ 遍历全部 $P$，$x$ 遍历全部 $K$。效应是原锥对偶中的整个区间，不是选择出来的实验菜单，也不是某个小面上的全部仿射函数。$K$ 紧且张成 $V$：严格正性排除归一化底的无界序列，生成性给出张成。有限维紧凸生成给出 $K=\operatorname{conv}P$。完整效应区间紧，$\mathcal F_p$ 是含 $u$ 的非空紧集，故所有 minimum 均实际达到。这些是前卷 §159.1 的背景事实；尤其在排核以前不预设 $T_p$ 对混态为仿射函数。

用原菜单定义

$$
p\perp q\quad\Longleftrightarrow\quad T_p(q)=0,
\qquad p^\perp=\{q\in P:p\perp q\}.
\tag{XIII160.2}
$$

一个达到 $f(p)=1,f(q)=0$ 的效应，其补效应达到反向条件，所以该关系对称且反自反。纯 PR 是更强的数值条件 $T_p(q)=T_q(p)$，此处不假设它。

面一律指满足线段性质的实际凸面。对任意 $A\subset K$，$F(A)$ 是包含 $A$ 的最小实际面，规定 $F(\varnothing)=\varnothing$。写 $F(p,q)=F(\{p,q\})$。有限维面及其锥化的标准性质，包括面相对内部点生成该面、面内生成面与原域实际面相容，以及对非空面 $F$ 的

$$
C_F=\mathbb R_{\ge0}F,\qquad C\cap\operatorname{span}_{\mathbb R}C_F=C_F,
$$

在本章只是沿用的凸几何背景，不另作新的面闭合主张。$F$ 不以暴露面包替换；$D_p$ 也不预设凸。

**定义 160.2（L2、规范切方向、TC 与 NC）。** L2 要求每个不同的原纯点 $p,x\in P$ 的整个实际面

$$
B(p,x):=F(p,x)
$$

仿射同构于非退化闭 Euclidean 三球。实际面的纯点恰为其中的原纯点，故

$$
\operatorname{ext}B(p,x)=P\cap B(p,x)
$$

是该三球的整个二维椭球边界。定义 $\tau_p(x)$ 为此边界在 $p$ 处的仿射切平面的方向空间。具体地，若 $A$ 是从单位三球到 $B(p,x)$ 的仿射同构，$A(s)=p$、$\|s\|=1$，则

$$
\tau_p(x)=\mathrm dA\{h\in\mathbb R^3:s\cdot h=0\}
\subseteq\ker u\cap\operatorname{span}_{\mathbb R}B(p,x),
\qquad \dim_{\mathbb R}\tau_p(x)=2.
\tag{XIII160.3}
$$

三球的仿射自同构固定其中心，在线性部分上为正交变换，所以此空间与所选 $A$ 无关。它也可由球边界上经过 $p$ 的光滑曲线的速度定义。这里只对每一个实际二元球微分，不给整个 $P$ 假设流形、环境度量或相容的全局光滑结构。仿射切平面是 $p+\tau_p(x)$，相应齐次向量空间是 $\mathbb Rp\oplus\tau_p(x)$；两者不混同。

TC 要求

$$
\begin{gathered}
\text{对所有 }p,a,b\in P,\quad a\ne b,\quad p\notin B(a,b),\\
\tau_p(y)\subseteq\tau_p(a)+\tau_p(b)
\quad\text{对每个 }y\in P\cap B(a,b).
\end{gathered}
\tag{XIII160.4}
$$

右端是实线性和，不是给定内积下的正交和。外点条件保证 $p\ne y$，因此所有出现的切方向都有定义。NC 则是整个原邻点集的实际面非塌缩：

$$
p\notin F(p^\perp)\qquad(p\in P).
\tag{XIII160.5}
$$

用于比较的旧 L3 仍采用 §159.4 的含义：每个不包含在任何二点生成面中的三元素纯点集，生成的整个实际面仿射同构于复 qutrit 密度空间 $\mathcal D_3$。L3 不是 TC 的定义。L2 球的仿射维数为三、锥张成维数为四；qutrit 的相应维数是八与九。

下文写 $\operatorname{Herm}_n(\mathbb C)$ 为实向量空间，$\operatorname{PSD}_n$ 为其正锥。对复子空间 $S$ 写

$$
\mathcal D(S)=\{\rho\succeq0:\operatorname{Tr}\rho=1,\ \operatorname{ran}\rho\subset S\},
\quad \mathcal D(0)=\varnothing,\quad \mathcal D_n=\mathcal D(\mathbb C^n),
\quad P_v=vv^\ast\quad(\|v\|=1).
$$

矩阵的正交补和投影属于后来得到的复坐标；原纯点的 $\perp$ 始终是 (XIII160.2)。

### 160.2 TC 精确供应 H3，且不借 L3 支付环境维数

**定理 160.3（端点直和、精确 H3 与分类入口）。** 假设 L2。对每个 $p,a,b$ 满足 (XIII160.4) 的外点条件，有

$$
\begin{aligned}
\operatorname{span}_{\mathbb R}B(p,a)\cap\operatorname{span}_{\mathbb R}B(p,b)&=\mathbb Rp,\\
\tau_p(a)\cap\tau_p(b)&=0,\\
W_{p;a,b}:=\mathbb Rp\oplus\tau_p(a)\oplus\tau_p(b),\qquad
\dim_{\mathbb R}W_{p;a,b}&=5.
\end{aligned}
\tag{XIII160.6}
$$

对该外点和实际球 $B(a,b)$，TC 当且仅当所有射影切平面

$$
\mathbb P_{\mathbb R}(\mathbb Rp\oplus\tau_p(y)),
\qquad y\in P\cap B(a,b),
\tag{XIII160.7}
$$

包含在同一个射影四维子空间中；该空间必为 $\mathbb P_{\mathbb R}(W_{p;a,b})$。此外，若 $K$ 既非单点亦非一个完整二元球，则 L2 已给出 $\dim_{\mathbb R}V\ge7$。在此情形下，L2 与 TC 精确供应 [SV160, Theorem 2.4] 的全部假设。

证明。这里复用的前卷输入是**引理159.5**，其前件只有 L2：不同实际二元球的实张成交集为零或共同纯点的一条实直线，并且

$$
\mathbb P_{\mathbb R}(\operatorname{span}_{\mathbb R}B)\cap\{[q]:q\in P\}
=\{[q]:q\in\operatorname{ext}B\}.
\tag{XIII160.8}
$$

若 $B(p,a)=B(p,b)$，这个实际球包含 $a,b$，从而包含 $B(a,b)$。三球没有真非单点面，故两个球相等，这与 $p\notin B(a,b)$ 矛盾。因此这两个球不同，159.5 给出 (XIII160.6) 第一行。两个切方向分别在这两个张成中，且都属于 $\ker u$；由于 $u(p)=1$，其交为零。每个切方向实维数为二，右端切方向和恰为四维，加径向 $\mathbb Rp$ 后恰为五维。

若 TC 成立，(XIII160.7) 的齐次空间全部包含于 $W_{p;a,b}$，得到一个射影四空间。反之，若它们都在某个射影四空间 $\mathbb P_{\mathbb R}W$ 内，则五维实空间 $W$ 包含端点 $a,b$ 所给的整个 $W_{p;a,b}$，两者因维数相同而相等。再交 $\ker u$，得到

$$
\tau_p(y)\subseteq W_{p;a,b}\cap\ker u
=\tau_p(a)\oplus\tau_p(b),
$$

正是 TC。这也说明固定 $p$ 和 $B$ 时，所得四维方向和与在 $P\cap B$ 中选哪两个不同端点无关。

若 $K$ 非单点，$K=\operatorname{conv}P$ 给出两个不同纯点 $a,b$。若又 $K\ne B(a,b)$，必有 $p\in P\setminus B(a,b)$。上面的两个球各有四维实张成，交恰为 $\mathbb Rp$，所以

$$
\dim_{\mathbb R}V\ \ge\ 4+4-1=7,
\qquad N:=\dim_{\mathbb R}V-1\ge6>3.
\tag{XIII160.9}
$$

这一步只有 L2，没有先用 L3 或尚待得到的矩阵秩。

现取 $X=\{[p]:p\in P\}\subset\mathbb P_{\mathbb R}V$，$\Xi=\{\xi_B=\mathbb P_{\mathbb R}(\operatorname{span}B):B\text{ 为实际二元球}\}$。$X$ 张成整个射影空间。每个 $X\cap\xi_B$ 由 (XIII160.8) 恰为整球的纯边界，其齐次化是 $\mathrm{PG}(3,\mathbb R)$ 中的非退化椭圆二次曲面。

它满足 [SV160, §2.3] 的准确 ovoid 定义。一个单位球模型的齐次二次式为 $q(t,r)=t^2-\|r\|^2$。若 $e=(1,s)$、$\|s\|=1$，经过 $[e]$ 的射影直线由 $e,d$ 张成，其二次式为 $2\lambda\mu\,b(e,d)+\mu^2q(d)$。当极化配对 $b(e,d)\ne0$ 时有第二个不同实交点；当 $b(e,d)=0$ 且 $d$ 不与 $e$ 成比例时，切超平面上的负定商给出 $q(d)<0$，故只有 $[e]$ 一个交点。全部这样的直线恰在唯一的切平面中，该平面仅接触 $[e]$；二次式也排除三个共线曲面点。因此这里的射影切平面正是 (XIII160.7)，不是另一个全局纯流形切空间。

分类的逐项供应如下：

| [SV160] 的假设 | 当前原域中的供应 |
| --- | --- |
| $X$ 张成有限 $\mathrm{PG}(N,\mathbb R)$ | $C$ 生成、$K=\operatorname{conv}P$；(XIII160.9) 给出 $N>3$ |
| 每个 $X\cap\xi$ 是整个 ovoid | L2、(XIII160.8) 与上面的球二次式 |
| H1：每两个不同 cap 点唯一确定一个 $\xi$ | 实际 $F(p,q)$ 的唯一性；在球中的两个不同纯点生成该整球 |
| H2：不同 $\xi,\eta$ 的交只含 cap 点 | 引理159.5 的准确张成交集结论 |
| H3：外点处所有相关切平面同处一个射影四空间 | (XIII160.6)–(XIII160.7) 与 TC 的双向等价 |

尤其 $[p]\notin\xi_B$ 与 $p\notin B$ 由 (XIII160.8) 等价。H3 中的二点符号对应 $B(p,y)$。分类所需的外点、纯点和切平面量词因此与 TC 完全相同。证毕。

### 160.3 从成熟射影商分类到同一个原单位归一化商

**命题 160.4（TC 入口下的统一商与实际小面）。** 在定义160.1的原域上，L2 与 TC 给出有限整数 $n\ge1$ 和一个满射实线性映射

$$
\Psi:\operatorname{Herm}_n(\mathbb C)\longrightarrow V,
\qquad \Psi(\operatorname{PSD}_n)=C,\qquad u\Psi=\operatorname{Tr}.
\tag{XIII160.10}
$$

其规范纯点映射 $[v]\mapsto p_v=\Psi(P_v)$ 是 $\mathbb{CP}^{n-1}\to P$ 的同胚。对每个 $S$ 满足 $1\le\dim_{\mathbb C}S\le2$，同一个 $\Psi$ 限制为 $\operatorname{Herm}(S)$ 到对应实际面张成的线性序同构，并且

$$
\Psi\mathcal D(S)
=F(\{p_v:v\in S,\ \|v\|=1\}).
\tag{XIII160.11}
$$

此处尚不宣称全局单射。

证明。单点底 $K=\{p\}$ 张成一维锥，取 $\Psi(t)=tp$ 即得 $n=1$。若某二元球就是 $K$，其仿射球坐标经 Pauli 参数

$$
X=(tI+a\cdot\sigma)/2,
\qquad \operatorname{Tr}X=t,
\qquad \operatorname{spec}(X)=\{(t+\|a\|)/2,(t-\|a\|)/2\}
$$

齐次延拓为 $n=2$ 的迹归一化序同构。归一化底上的仿射映射唯一延拓为其锥张成上的线性映射，因为对归一化点的线性关系应用单位后，其系数和为零。

其余情形由定理160.3满足 [SV160, Theorem 2.4]。该成熟定理的结论是：cap 的点与椭圆空间构成某个 $\mathrm{PG}(r,\mathbb L)$ 的点线结构，$\mathbb L$ 是环境域的二次扩张，原 cap 射影等价于相应 Hermitian Veronesean 的商。这里 $r\ge2$。有限性不是另外假设：该文 §3.3 用指数 $r$ 的射影切空间维数 $2r$ 排除有限环境中的无限指数。定理对 $r=2,3$ 还有无商的较强结论；本证明在一般有限 $r$ 下只使用其商结论。

“商”采用 [CTV160, §1, p. 5] 的线性射影投影含义：投影中心不交任何椭圆三空间，也不交定义中的相关切四空间。它在每个椭圆空间上有定义且单射。两个不同秩一射影点的连线在它们的共同椭圆空间中，所以全体秩一射影点也不会被识别。此处应用的实域分类是 [SV160] 的一般定理；[CTV160] 的有限域分类不被直接应用于实凸锥。

环境域已经是 $\mathbb R$。若 $\alpha$ 是二次扩张的生成元，最小多项式为不可约 $x^2+bx+c$，则 $4c-b^2>0$，而

$$
j=(2\alpha+b)/\sqrt{4c-b^2},\qquad j^2=-1.
$$

故 $\mathbb L=\mathbb R\oplus\mathbb Rj\cong\mathbb C$，非平凡共轭为 $j\mapsto-j$。这支付了完整的复数域识别，不以流形维数猜测域。环境射影等价的半线性也不会留下实域扭曲：$\mathbb R$ 的域自同构保正平方，因而保序，固定有理数，再由有理数稠密性固定全部实数。

[SV160, §2.3] 的 Hermitian Veronesean 坐标是 $vv^\ast$ 的对角项及每个非对角项的两个实坐标的可逆实线性组合。把它与射影投影、环境等价复合，得到一个满射实线性映射

$$
L:\operatorname{Herm}_n(\mathbb C)\longrightarrow V,\qquad n=r+1,
$$

其秩一射影像恰为 $X$，且在秩一射影点集和支持二维的椭圆空间上单射。满射性来自 $X$ 的张成。

下面是前卷命题159.7在**分类供应之后**的原单位归一化论证，说明它并不再用 L3。对每个非零 $v$，$L(vv^\ast)$ 是某原纯点的非零实倍数，故 $uL(vv^\ast)\ne0$。这个连续实二次型在连通的复单位球面上符号恒定；必要时把整个 $L$ 乘以 $-1$。实迹配对给出唯一 $G\in\operatorname{Herm}_n(\mathbb C)$ 满足

$$
(uL)(X)=\operatorname{Tr}(GX),\qquad v^\ast Gv>0\quad(v\ne0),\qquad G\succ0.
\tag{XIII160.12}
$$

所有秩一正矩阵现都送到原纯射线的正向。谱分解和 $K=\operatorname{conv}P$ 于是给出 $L(\operatorname{PSD}_n)=C$。定义

$$
\Psi(X)=L(G^{-1/2}XG^{-1/2}).
\tag{XIII160.13}
$$

正定合同保持整个正锥，并置换复向量线与二维子空间，故得到 (XIII160.10)。迹一秩一像已经按**原单位**归一化，纯点映射仍为双射。它连续，定义域 $\mathbb{CP}^{n-1}$ 紧，值域在有限维 Hausdorff 空间内，所以是到全部原 $P$ 的同胚；原 $P$ 的紧性是此处的结论。选择相反复共轭可由迹保持实线性序自同构 $X\mapsto X^T$ 吸收。

还须供应实际小面，而不只宣称射影线对应。对 $S=\operatorname{span}_{\mathbb C}\{v,w\}$、$\dim_{\mathbb C}S=2$，令 $B=F(p_v,p_w)$。由于 $\Psi\mathcal D_n=K$，仿射逆像

$$
\{\rho\in\mathcal D_n:\Psi\rho\in B\}
$$

是包含 $P_v,P_w$ 的实际矩阵面，故包含 $\mathcal D(S)$，这里用标准矩阵支持面规则。因此 $\Psi\mathcal D(S)\subset B$。在两边的单位三球坐标中，限制映射写成 $a\mapsto b_0+Ma$。每个 $\|a\|=1$ 是全局纯点，其像也是 $B$ 的纯点，故

$$
\|b_0+Ma\|^2=1\qquad(\|a\|=1).
$$

比较 $a,-a$ 得 $M^Tb_0=0$；二次部分在单位球面恒定给出 $M^TM=cI$。纯点单射排除 $c=0$，于是 $M$ 可逆、$b_0=0$、$c=1$。所以这个限制是到**整个实际球**的仿射同构。按 $u\Psi=\operatorname{Tr}$ 齐次延拓，得到所需四维线性序同构和 (XIII160.11)。支持一维的结论由纯射线立即给出；零支持约定为空面。

这准确复用了命题159.7的归一化与小面证明，而没有直接调用其带 L3 的原陈述：原证明中供应 cap 的引理159.6，已由定理160.3替换。证毕。

### 160.4 NC 排除统一商核，并给出完整原始概率字典

**定理 160.5（L2 + TC + NC 的完整双向重建）。** 在定义160.1的全部原域上，以下两项等价：

1. L2、TC、NC 成立。
2. 存在有限整数 $n\ge1$ 和一个实线性双射

$$
\Phi:\operatorname{Herm}_n(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\operatorname{PSD}_n)=C,\qquad u\Phi=\operatorname{Tr}.
\tag{XIII160.14}
$$

在同一个 $\Phi$ 下，$K=\Phi\mathcal D_n$，$p_v=\Phi(P_v)$ 参数化全部 $P$，$P\cong\mathbb{CP}^{n-1}$，且 $\dim_{\mathbb R}V=n^2$。全部原效应、全部确认者与每个混输入的 minimum 分别是

$$
\begin{gathered}
\mathcal E\longleftrightarrow\{A\in\operatorname{Herm}_n(\mathbb C):0\preceq A\preceq I\},
\qquad f_A(\Phi X)=\operatorname{Tr}(AX),\\
\mathcal F_{p_v}\longleftrightarrow
\{P_v+B:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\},\qquad Q_v=I-P_v,\\
T_{p_v}(\Phi\rho)=v^\ast\rho v\quad(\rho\in\mathcal D_n),\qquad
D_{p_v}=F(p_v^\perp)=\Phi\mathcal D(v^\perp).
\end{gathered}
\tag{XIII160.15}
$$

$f_{P_v}$ 是原菜单的最小确认者，同一效应同时达到所有混输入的 minimum。对任意 $X\succeq0$，包括零和任意非负质量，还成立

$$
\min_{f\in\mathcal F_{p_v}}f(\Phi X)=\operatorname{Tr}(P_vX).
$$

纯 PR、L2 球对径纯点的原可区分性 AD，以及完整矩阵支持面规则都是结论。单点与完整三球端点均包括在等价中。

证明。先由命题160.4取得同一个 $\Psi$，令 $\mathcal N=\ker\Psi$。原单位保证 $\operatorname{Tr}Z=0$ 对每个 $Z\in\mathcal N$ 成立。满射的对偶拉回以实迹配对准确识别全部原泛函为 $\mathcal N^\perp$，所以在排核**以前**，完整菜单只能是

$$
\begin{aligned}
\mathcal E&\longleftrightarrow\mathcal N^\perp\cap[0,I],\\
\mathcal F_{p_v}&\longleftrightarrow
\{A\in\mathcal N^\perp:0\preceq A\preceq I,\ Av=v\},\\
T_{p_v}(\Psi\rho)&=
\min_{\substack{A\in\mathcal N^\perp,\ 0\preceq A\preceq I\\Av=v}}
\operatorname{Tr}(A\rho).
\end{aligned}
\tag{XIII160.16}
$$

正性及补正性分别等价于 $A\succeq0$ 与 $I-A\succeq0$；确认条件等价于 $Av=v$。上式与密度提升选择无关。不能在此时把整个 $[0,I]$ 偷换成原菜单，也不能预设 $P_v$ 已下降为原效应。

现在准确使用前卷 §159.5 的**定理159.10**，而不是把带 L3 的定理159.12当成新的入口。159.10 的供应要求及其当前来源是：

| 排核所需供应 | 当前已经取得的结论 |
| --- | --- |
| 有限复矩阵上的一个满射，正锥像为原 $C$ | (XIII160.10)，不是各球分别选取的局部表示 |
| 同一个原单位满足 $u\Psi=\operatorname{Tr}$ | (XIII160.12)–(XIII160.13) 的正定归一化 |
| 规范纯点参数化全域双射、同胚 | 命题160.4的紧性与纯点单射论证 |
| 每个支持维数至多二的像是原实际面，且限制为序同构 | (XIII160.11) 及整球仿射限制证明 |
| 邻点按完整原效应定义 | (XIII160.2)、(XIII160.16) |

159.8 从这些实际小面推得每个非零核矩阵至少有三个正、三个负特征值；159.9 使用压缩零化空间中的正定矩阵及最大特征向量的实参数扰动；159.10据此取得真实原邻点的张成和准确实际面二分：

$$
\operatorname{span}_{\mathbb C}\{w:\|w\|=1,\ p_w\in p_v^\perp\}=v^\perp,
$$

$$
F(p_v^\perp)=
\begin{cases}
\Psi\mathcal D(v^\perp),&v^\ast Zv=0\quad\text{对所有 }Z\in\mathcal N,\\
K,&v^\ast Zv\ne0\quad\text{对某个 }Z\in\mathcal N.
\end{cases}
\tag{XIII160.17}
$$

第一支是已下降的 $P_v$ 所暴露的真零面。第二支来自实际原邻点的一次有限混合：其提升在 $v^\perp$ 上正定，沿一个在 $v$ 上非零的迹零核方向作小移动，Schur 补使提升全秩而原态不变，实际面因而成为全体。原邻点各自的见证可以不同，并不需要 AD、纯 PR 或联合测量标架。159.8–159.10的证明在取得上述供应后不再使用 L3 或 cap 分类；这里不重证它们。

NC 排除 (XIII160.17) 第二支，所以 $v^\ast Zv=0$ 对所有 $v$ 和所有 $Z\in\mathcal N$ 成立。Hermitian 极化给出 $Z=0$。故 $\mathcal N=0$，取 $\Phi=\Psi$ 得 (XIII160.14)。若 $n=1$，迹归一化已经强迫核为零，$p_v^\perp=\varnothing$，159.10 的约定正给出空面；没有低秩遗漏。

接着证明字典，所用的是同一个双射的对偶，而非额外分类。全部原泛函现在是全部 Hermitian 迹形式，正性与补正性给出 (XIII160.15) 第一行。正收缩 $A$ 满足 $v^\ast Av=1$ 当且仅当 $Av=v$，于是相对于 $\mathbb Cv\oplus v^\perp$ 的非对角块为零，全部确认者恰为 $P_v+B$。每个 $B\succeq0$，所以 $A\succeq P_v$，而 $P_v$ 自己属于原菜单。这同时给出最小确认者及对每个正矩阵输入的 minimum；不只对满秩、对角或纯输入成立。$\operatorname{Tr}(P_v\rho)=0$ 当且仅当 $\rho$ 支持于 $v^\perp$，故得到全部 $D_{p_v}$ 与邻点面。纯输入给出 $|v^\ast w|^2=|w^\ast v|^2$，即纯 PR。支持二维球的对径纯投影相加为该支持上的恒等，向量正交；原效应 $P_v$ 就是可区分见证，得到 AD。标准支持面规则经 $\Phi$ 传到全部原实际面。

反向设 (XIII160.14) 已给定。矩阵支持面规则说明两个不同纯射线生成 $\mathcal D(\operatorname{span}_{\mathbb C}\{v,w\})$，经 $\Phi$ 是整个实际三球，故 L2 成立。原菜单正是 (XIII160.15)，邻点向量恰为 $v^\perp$ 中的射线，它们生成排除 $p_v$ 的支持面，故 NC 成立。

还须对所有实际二元球证明 TC。令 $a=p_\alpha,b=p_\beta$、$S=\operatorname{span}_{\mathbb C}\{\alpha,\beta\}$，$p=p_v\notin\Phi\mathcal D(S)$。纯点单射及支持面规则给出 $v\notin S$，而每个 $y\in P\cap B(a,b)$ 都为某个单位 $w\in S$ 的 $p_w$。置 $Q_v=I-P_v$，$z_w=Q_vw$。对 $z\perp v$，在迹一仿射空间中的秩一曲线

$$
\gamma_z(t)=\frac{(v+tz)(v+tz)^\ast}{1+t^2\|z\|^2},
\qquad \gamma_z'(0)=\Theta_v(z):=vz^\ast+zv^\ast
\tag{XIII160.18}
$$

给出正确的**归一化仿射切方向**。在支持二维球上，其整个切方向为

$$
\tau_{p_v}(p_w)=\Phi\{\Theta_v(z):z\in\mathbb Cz_w\}.
\tag{XIII160.19}
$$

这是实二维空间；例如其生成元是 $\Theta_v(z_w)$ 与 $\Theta_v(iz_w)=i(z_wv^\ast-vz_w^\ast)$。由于 $Q_v|_S$ 复线性且 $z_w\in\mathbb Cz_\alpha+\mathbb Cz_\beta$，$\Theta_v$ 的实线性立即给出 TC。这个计算只用同一个 $\Phi$ 与各支持二维实际面，不假设任何独立的全局纯流形几何。

最后逐项处理端点。$n=1$ 时 $K=\{p\}$、$\mathcal E=\{tu:0\le t\le1\}$、$\mathcal F_p=\{u\}$、$T_p(p)=1$、$D_p=p^\perp=\varnothing$；L2 与 TC 的量词为空，NC 成立。$n=2$ 时每个不同纯对的二元球都是整个 $K$，没有 TC 所需的外点，$D_{p_v}$ 为唯一正交纯点；NC 仍成立。L3 的三点条件在这两个端点都为空。反向与字典全部完成。证毕。

### 160.5 全部实际面、任意纯集闭包与静态量子公理的对应

**推论 160.6（同原闭包字典）。** 在 L2 与 TC 的范围内，下列条件等价：NC；对每个 $p$ 的暴露面版本 $p\notin F_{\mathrm{exp}}(p^\perp)$；完整归一化表示 (XIII160.14)；以及

$$
P\cap F(A)=A^{\perp\perp}\qquad\text{对每个 }A\subset P,
\tag{XIII160.20}
$$

其中 $A^\perp=\{q\in P:q\perp a\text{ 对所有 }a\in A\}$，$F_{\mathrm{exp}}$ 是所有包含给定集合的暴露面的交，允许空面和全体。在重建后，对任意 $A\subset K$ 还有准确支持规则

$$
F(A)=\Phi\mathcal D(S_A),\qquad
S_A=\operatorname{span}_{\mathbb C}
\bigcup_{x\in A}\operatorname{ran}(\Phi^{-1}x).
\tag{XIII160.21}
$$

因此全部原实际面由复支持子空间参数化；空支持给空面，全支持给全体。

其中实际面 NC 与暴露面 NC 的比较，在定理160.10中推广到不带 L2、TC 或矩阵前件的完整原域；本推论的 FC、完整表示和支持规则仍保留上述重建前件。

证明。这里沿用推论159.13的闭包推理，但其所需的完整表示由定理160.5供应，而不是再调用 L3。在命题160.4的统一商上，定理159.10已经给出 (XIII160.17)：第一支本身暴露，第二支是全体，所以对每个 $p$ 有 $F(p^\perp)=F_{\mathrm{exp}}(p^\perp)$。这支付两种 NC 的等价；NC 与表示的等价是定理160.5。

在该表示下，标准矩阵支持面规则先给出 (XIII160.21)。即使 $A$ 无限，有限维性也可从这些支持中选有限多个，张成同一个 $S_A$；这些相应密度矩阵的严格正权混合在 $S_A$ 上正定，因而生成整个支持面。对纯点集 $A$，两次正交补恰返回 $S_A$ 的全部射线，给出 (XIII160.20)。$A=\varnothing$ 时两边为空，$A=P$ 时两边为 $P$。反过来，任意集合的正交补运算由关系对称性满足三次补等于一次补；将 (XIII160.20) 用于 $A=p^\perp$，得 $P\cap F(p^\perp)=p^\perp$，反自反性便给出 NC。证毕。

全部概率配对已经由 $f_A(\Phi\rho)=\operatorname{Tr}(A\rho)$ 识别：不仅最低确认值，而且每个原状态与每个原效应的值都在同一映射中。全部实仿射状态泛函对应 Hermitian 数学可观测量；其谱分解给出投影值的数学表示。任意有限正效应分解 $\sum_j f_j=u$ 恰对应 $A_j\succeq0$、$\sum_j A_j=I$ 的有限 POVM。数学上每个密度矩阵也有本征纯态的凸分解。这些都是同一状态、效应和凸组合结构的后果。

这说明与常见静态量子表述的准确对应：混态是迹一正矩阵，纯态是复 Hilbert 空间中的射线，相位选择不改变原纯点；原效应概率是迹配对，纯确认概率是重叠平方；数学可观测量与有限 POVM 有上述完整形式。复 Hilbert 坐标是重建所得，并非原条件中预先指定。静态定理不把所有数学状态解释为实际可制备，不把每个数学 POVM 解释为已实施的测量仪器。

### 160.6 严格前置分离：所有实际二元球都满足 TC 的三对三平衡商

**定理 160.7（L2 + TC 严格不供应 L3，且原 NC 失败）。** 取

$$
\begin{gathered}
W=\operatorname{Herm}_6(\mathbb C),\qquad
H=\operatorname{diag}(I_3,-I_3)=R_+-R_-,\\
V_3=W/\mathbb RH,\qquad \pi:W\longrightarrow V_3,\qquad
C_3=\pi(\operatorname{PSD}_6),\qquad
u_3(\pi X)=\operatorname{Tr}X,\qquad K_3=\pi\mathcal D_6.
\end{gathered}
\tag{XIII160.22}
$$

这是定义160.1的一个完整原域，满足 L2 与 TC。TC 对全部原纯点和全部实际二元球成立，且相关二维单切方向、四维端点切方向和五维齐次切空间均不被 $\pi$ 压缩。然而正块的三个坐标纯点生成全部 $K_3$，所以 L3 失败；原 NC 也失败。

证明。首先明确复用范围。前卷**定理159.1**在 $m=3$ 给出 $C_3$ 闭、尖、生成，$u_3$ 严格正，全体原纯点恰为 $p_v=\pi(P_v)$，且 $[v]\mapsto p_v$ 是 $\mathbb{CP}^5\to P$ 的同胚。它还给出每个 $\dim_{\mathbb C}S<3$ 的整个像 $\pi\mathcal D(S)$ 是暴露的实际面，$\pi|_{\operatorname{Herm}(S)}$ 为迹保持序同构，并给出这些纯点的准确实际生成面。因此对于每个不同纯对 $a=p_\alpha,b=p_\beta$，

$$
S=\operatorname{span}_{\mathbb C}\{\alpha,\beta\},\qquad
B(a,b)=\pi\mathcal D(S),\qquad \dim_{\mathbb C}S=2.
\tag{XIII160.23}
$$

这证明全部 L2；不是只证明某些嵌入球。

在这个原域上，全部原效应仍严格限定为

$$
\mathcal E_3=\{f_A:0\preceq A\preceq I_6,\ \operatorname{Tr}(AH)=0\},
\qquad f_A(\pi X)=\operatorname{Tr}(AX).
\tag{XIII160.24}
$$

完整确认菜单另加 $Av=v$，每个原混态的 minimum 是在这个完整受约束菜单上取的 $\min\operatorname{Tr}(A\rho)$。定理159.3给出它的全部混输入谱公式 (XII159.13)–(XII159.14)，其值与提升无关。定理159.1还证明所有纯对的 minimum 为 $|v^\ast w|^2$。这些引用不意味着任意选取的矩阵效应都能下降。

现在取**任意** TC 输入 $a=p_\alpha,b=p_\beta,p=p_v$，其中 $a\ne b$、$p\notin B(a,b)$。所有单位向量都在同一个 $\mathbb C^6$ 中，所有像都经过同一个全局 $\pi$。先证明准确外点判据：

$$
p_v\notin\pi\mathcal D(S)\quad\Longleftrightarrow\quad\mathbb Cv\not\subset S.
\tag{XIII160.25}
$$

若 $v\in S$，其投影显然在该面中。若 $p_v$ 在该面中，则它是该实际面的极点；(XIII160.23) 的仿射同构把这个极点写成 $\pi(P_w)$，其中 $w\in S$。全局纯点单射给出 $\mathbb Cv=\mathbb Cw$，故 $v\in S$。同理，$P\cap B(a,b)$ 的**全部**纯点恰为这些 $p_w$，没有额外的纯点提升。

置

$$
L=\operatorname{span}_{\mathbb C}\{v,\alpha,\beta\},\qquad
U=v^\perp\cap L=Q_vS,\qquad Q_v=I-P_v.
\tag{XIII160.26}
$$

外点条件使 $\dim_{\mathbb C}L=3$；$Q_v|_S$ 是复线性单射，因此 $U$ 复维数恰为二，$z_\alpha=Q_v\alpha,z_\beta=Q_v\beta$ 是它的一组复基。这里的 carrier 是同一个三维复空间 $L$ 中垂直于 $v$ 的二维复空间 $U$，并不是一个未说明的“秩至多四”的支撑。

对任意 $p_w\in P\cap B(a,b)$，(XIII160.18) 的归一化曲线位于实际支持二维球 $B(p_v,p_w)$ 的提升中。由该球上的仿射同构，整个原切方向准确为

$$
\tau_{p_v}(p_w)=\pi\Theta_v(\mathbb Cz_w),\qquad z_w=Q_vw,
\qquad \Theta_v(z)=vz^\ast+zv^\ast.
\tag{XIII160.27}
$$

任意两端点切方向之和的提升不是任意 Hermitian 矩阵之和，而准确为

$$
\Theta_v(\mathbb Cz_\alpha)+\Theta_v(\mathbb Cz_\beta)
=\Theta_v(U)=\{vz^\ast+zv^\ast:z\in v^\perp\cap L\}.
\tag{XIII160.28}
$$

这是 $\Theta_v$ 的实线性所得；复系数分别由 $\Theta_v(z)$、$\Theta_v(iz)$ 的实线性组合承载。因为 $z_w\in U$，(XIII160.27)–(XIII160.28) 已给出所有 $w\in S$ 的 TC 包含关系。

还要证明相关切空间没有被商压掉。$\operatorname{Tr}\Theta_v(z)=0$。若 $z\ne0$ 且 $z\perp v$，$\Theta_v(z)$ 在正交基 $v,z/\|z\|$ 上为

$$
\begin{pmatrix}0&\|z\|\\\|z\|&0\end{pmatrix},
$$

在其正交补上为零，故恰有一个正、一个负特征值，分别为 $\|z\|$ 与 $-\|z\|$。所以整个 (XIII160.28) 的任意非零元素惯性为 $(1,1)$；$\ker\pi=\mathbb RH$ 的非零元素却有三个正、三个负特征值。两者交为零。$\Theta_v$ 本身也单射，因为 $\Theta_v(z)v=z$。于是 $\pi$ 在整个四维实切方向和上单射，当然也在每个二维单切方向上单射。

齐次空间是

$$
\mathbb RP_v\oplus\Theta_v(U),\qquad \dim_{\mathbb R}=1+4=5.
\tag{XIII160.29}
$$

若其中 $cP_v+\Theta_v(z)$ 落在 $\mathbb RH$，取迹先得 $c=0$，再用上述惯性得 $z=0$。故 $\pi$ 在这个五维齐次空间上也单射，其射影化恰为四空间。单个二元球的四维齐次张成则已由定理159.1的支持二维限制保证单射。这列出了这里所需的全部切向和球张成的单射，而没有把四维仿射方向误作五维方向。

这证明任意合法 $p,a,b,y$ 的 TC，包含球面的全部连续纯点，不是坐标纯点或某个局部开片的检验。

接着令 $p_j=\pi(P_{e_j})$，$j=1,2,3$，取正块的标准正交基。它们不在任何二元球中：否则该实际球的支持二维表述和纯点单射会把三个独立向量线都放入一个复二维空间。可是

$$
\frac{p_1+p_2+p_3}{3}
=\pi(R_+/3)=\pi(I_6/6),\qquad
R_+/3-I_6/6=H/6.
\tag{XIII160.30}
$$

$I_6/6$ 正定，而满射商映射在迹一仿射超平面上开，所以这个像在 $\operatorname{ri}K_3$ 中。包含该混合的实际面必为全体，故

$$
F(p_1,p_2,p_3)=K_3.
\tag{XIII160.31}
$$

$\dim_{\mathbb R}W=36$、$\dim_{\mathbb R}V_3=35$，且 $C_3$ 生成，因而 $\dim_{\mathrm{aff}}K_3=34$。这不是仿射维数八的 qutrit 面，L3 明确失败。锥维数35也不是任何完整复矩阵空间的平方维数。

最后核对原 NC，而不把此商冒充为完整定理的反例。$\pi$ 已满足定理159.10所需的规范商、全域纯参数化与实际支持至多二维性质；取 $v=e_1$、$Z=H$，有 $v^\ast Zv=1$。准确的原邻点定理**159.10，式 (XII159.29)** 的第二支给出

$$
F(p_{e_1}^\perp)=K_3,
\tag{XIII160.32}
$$

故 NC 失败。这也与平衡商专门结论**命题159.4**的 $h\ne0$ 分支一致。其在本例中的具体内容可直接看见：由全部纯 minimum，$p_{e_2},\ldots,p_{e_6}$ 都是原零邻点；它们的等权混合有提升

$$
\rho=\operatorname{diag}(0,1/5,1/5,1/5,1/5,1/5),
$$

而 $0<t<1/5$ 时 $\rho+tH\succ0$，迹仍为一，像仍为 $\pi\rho$。因此这个真实邻点混合已在原底内部。这里不需要同一个效应同时确认所有零邻点。

完整混态读数确实已经改变。例如定理159.3的 (XII159.15) 给出

$$
T_{p_{e_1}}\bigl(\pi(I_6/6)\bigr)=1/3,
$$

而在提升 $I_6/6$ 上直接套 $P_{e_1}$ 的 Born 值为 $1/6$。$P_{e_1}$ 不满足 (XIII160.24)，不能用该值替代原 minimum。故本例同时保持 L2、TC 和全部纯 PR，却失败 L3、NC 及完整混态矩阵字典。证毕。

**推论 160.8（TC 与旧 L3 的准确强弱）。** 在定义160.1且有 L2 的共同范围中，L3 蕴含 TC；反向蕴含在加 NC 之前严格失败。因此 TC 是比旧 L3 更弱的前置条件。加 NC 后，两套完整候选都等价于同一个类型的同原有限复矩阵模型：

$$
\mathrm{L2+L3+NC}\quad\Longleftrightarrow\quad
\text{(XIII160.14)}\quad\Longleftrightarrow\quad
\mathrm{L2+TC+NC}.
\tag{XIII160.33}
$$

证明。非单点非整球时，引理159.6在实际 qutrit 中由 L3支付准确 H3，定理160.3的反向桥便给 TC；单点和整球时 TC 无外点而为空条件。定理160.7给出有 L2、TC 而没有 L3 的完整原域，证实严格性。左侧完整重建是定理159.12，右侧是定理160.5；两者都保留原 $C,u$ 和完整菜单。特别地，定理160.5的模型反向还供应全部实际 qutrit 面，从而可恢复 L3。证毕。

### 160.7 前提节省的含义、独立物理合同与开放入口

几何上的节省是：为了供应分类的局部闭合，现在只要求实际二元球边界的规范切方向落在两个端点给定的方向和中，不再提供整个三点 qutrit 面的凸结构。TC 仍是一个对所有外点、所有球面纯点的精确三元兼容条件；它不只是一项维数口号。成熟的 H3 没有成为新发现，改变的是从原有序锥的较小供应结构到该成熟条件的透明桥接。严格分离发生在 NC 之前；本章没有证明这些条件在任意背景下全局独立，也没有证明它们构成最小公理组。

对实际物理，定理160.5所识别的是完整静态状态、效应与概率结构。若要进一步把它解释为实验理论，仍需明确给出实际制备与事件的饱和性、实际有限复合系统的载体与完整锥及单位、所有相关输入及重关联和交换接口。在这些复合域给定之后，某操作对每个有限旁观者的完全正性才有确定量词；单系统静态表示不供应这一合同。每个实际仪器的结果族、条件态、记录、权限与预算，以及全部合法未来和中间切口，也各有自己的操作接口。物理钟、连续动力学、幺正实现、Hamiltonian 与能量的识别及 $\hbar$ 的标定需要另外的动力学与经验对应。上述区分保留了静态重建的完整强度，同时没有把数学 POVM 的存在当作实际仪器的存在。

仍未支付的入口可以准确列为：

$$
\mathrm{L2+NC}\ \stackrel{?}{\Longrightarrow}\ \mathrm{TC},
\tag{XIII160.34}
$$

以及三点实际面九维上界的路线。具体以 TF9 记对所有纯点三元组的

$$
\dim_{\mathbb R}\operatorname{span}_{\mathbb R}F(a,b,c)\le9;
$$

本章不证明

$$
\mathrm{L2+TF9+NC}\ \stackrel{?}{\Longrightarrow}\ \mathrm{L3}.
\tag{XIII160.35}
$$

也不从 TF9推出 TC。单纯限制三点实际面的张成维数，并不在本证明中自动供应其 qutrit 仿射序结构或全部 H3。

另一个开放入口是无全局维数上界的完整 EB3 加纯 PR 是否供应全局矩阵重建；这里 EB3 指每个**整个原** $D_p$ 是非退化闭三球，纯 PR 指 (XIII160.1) 的全部纯对数值互易。前卷 §159.7 已说明 EB3 自带 NC，而定理158.1在另加整个 $\dim_{\mathbb R}V\le9$ 时给出同原 qutrit 重建。

已发表的 MD 采用定义155.1的完整原菜单含义：令 $\mathcal A_p=\{e\in\mathcal F_p:e|_{D_p}=0\}$、$B_p(x)=\min_{e\in\mathcal A_p}e(x)$，则 $\mathsf{MD}(p)$ 要求每张 $f\in\mathcal F_p$ 都有一张 $e\in\mathcal A_p$ 满足 $f-e\in C^\ast$；$e$ 允许随 $f$ 改变，$\mathsf{MD}$ 要求此性质对全部原纯 $p$ 成立。在完整 EB3、纯 PR 的原背景中，定理155.2证明它等价于 $T_p(x)=B_p(x)$ 对全部原混输入 $x\in K$ 成立；推论155.5再证明 EB3 + 纯 PR + MD 等价于同原 $C,u$ 的复三能级归一化表示。矩阵字典是这项有条件的重建结论，MD 的定义是逐张正序下界或等价的完整混态包络等号。

无维数上界时，裸 EB3 + 纯 PR 是否推出 MD 仍 open，故其到上述 qutrit 表示的桥也未付。第156章把纯行等号 $T_p(s)=B_p(s)$（全部 $s\in P$）列为额外前件；其正混态差距及临界三维构型的条件结论，没有排除此缺口，也没有构造实现缺口的完整模型。本章没有从裸 EB3 + 纯 PR 取得 L2、TC 或 L3，也不以定理160.7反驳该入口。该商不满足完整 EB3。若已由定理160.5取得表示，再另给 EB3，则 $D_{p_v}=\Phi\mathcal D(v^\perp)$ 的仿射维数迫使 $n=3$；这是重建后的秩判定，不能倒用成重建前的供应。

直观地说，每两个不同纯态先确定一颗完整三球，它的球面就是这两态之间全部可能的纯态。在另一纯态 $p$ 处，连接这颗球面上每个纯态所得到的小球，各有一个二维切方向。TC 只要求这些方向都由连接两个固定端点时得到的四维方向和容纳；加上 $p$ 的径向才是五维齐次空间，射影化后才是成熟帽定理所需的四空间。这个规则用的是球与球怎样接合，不必先给整个三态 qutrit，也不必先知道复数或全局纯态流形。分类把这些接合关系组织成同一个有限复矩阵商，原单位再选定正定尺度和共同的迹归一化。此时局部球仍可能全对，而全局混合已经被商掉：三对三平衡商中，正块三个纯态的平均与全秩均匀态是同一个原态，三个点因此生成全体；每个二元球的切方向却一点也没有被压缩。NC 所约束的正是另一件事：某纯态的全部真实零邻点不能经实际面生成把它自己包进去。159.10证明非零商核必在某纯态处造成这种塌缩；NC 因而排核。排核以后，同一个映射才恢复所有原混态、所有原效应、整个确认菜单与全部 Born minimum，而实际制备、复合、操作和时间仍需各自的物理合同。

### 160.8 完整原菜单下的非塌缩、真邻点面与共同正支撑

**定义 160.9（点态非塌缩与正支撑）。** 只保留定义160.1的有限维原锥、原单位及完整原效应区间，不加 L2、L3、TC、EB3、纯 PR、自对偶或矩阵表示。对每个原纯点 $p$，记 $N_p=p^\perp$、$F_p=F(N_p)$，并定义

$$
\begin{aligned}
\mathrm{NC}(p)&:\quad p\notin F_p,\\
\mathrm{EN}(p)&:\quad
\exists g\in C^\ast\setminus\{0\}:\quad
g|_{N_p}=0,\quad g(p)>0.
\end{aligned}
\tag{XIII160.37}
$$

这里一个 $g$ 要同时消去该 $p$ 的全部原零邻点；不同 $p$ 可以使用不同的 $g$。正泛函仍属于原 $V^\ast$，没有将状态与效应预先识别。非零 $g\in C^\ast$ 的原零面记为 $Z_K(g)=K\cap\ker g$；若它为空，仍采用空面约定。

**定理 160.10（一般点态等价及所有正支撑的严格性）。** 在定义160.9的完整原域内，对每个原纯点 $p$，以下条件等价：

$$
\begin{gathered}
\mathrm{NC}(p)\quad\Longleftrightarrow\quad F_p\ne K
\quad\Longleftrightarrow\quad\mathrm{EN}(p)\\
\Longleftrightarrow\quad
\exists g\in C^\ast\setminus\{0\}:g|_{N_p}=0
\quad\Longleftrightarrow\quad
p\notin F_{\mathrm{exp}}(N_p).
\end{gathered}
\tag{XIII160.38}
$$

而且有下列全称结论：

$$
g\in C^\ast\setminus\{0\},\quad g|_{F_p}=0
\quad\Longrightarrow\quad g(p)>0.
\tag{XIII160.39}
$$

消去 $F_p$ 与消去 $N_p$ 对正泛函等价。因此只要 $F_p$ 为真面，每个消去它的非零正泛函都严格正于 $p$；这里既有这样的泛函存在，也有对其全部选择的严格性。

证明。首先，对每个正泛函 $g$，其零集 $Z_K(g)$ 有实际面性质：若线段内点的非负评价为零，则两端评价都为零。故 $g|_{N_p}=0$ 蕴含 $F_p\subseteq Z_K(g)$，反向由 $N_p\subseteq F_p$ 立即成立；空集时两种消去条件都为空条件。

先证明严格性，暂不使用 $F_p$ 真。取非零 $g\in C^\ast$ 消去 $N_p$，令 $M=\max_{x\in K}g(x)$。紧性使最大值达到。$K$ 张成 $V$，故非零正泛函不可能在 $K$ 上恒零，因而 $M>0$。最大值还在某个**原纯点** $r\in P$ 达到：最大面 $\{x\in K:g(x)=M\}$ 是非空紧凸实际面，取其极点即为 $K$ 的极点。这个论证不要求整个 $P$ 闭或紧。

若 $g(p)=0$，在整个原锥上定义

$$
e=g/M,\qquad 0\le e\le u,\qquad e(r)=1,\quad e(p)=0.
\tag{XIII160.40}
$$

确实每个非零 $c\in C$ 都可写成 $c=u(c)k$、$k\in K$，所以 $g(c)\le M u(c)$；因此 $e$ 是完整原区间中的效应。它确认 $r$，其补效应 $u-e$ 确认 $p$ 且消去 $r$，给出 $r\in N_p$。但 $g$ 消去全部 $N_p$ 而 $g(r)=M>0$，矛盾。由正性遂有 $g(p)>0$。这证明 (XIII160.39)，并说明全称严格性并未借用 L2、矩阵内积或预给的量子模型。完整原菜单和补效应封闭性在 (XIII160.40) 处实际承担了证明。

接着证明真面时正支撑的存在。使用有限维凸几何的标准事实：每个非空真实际面都包含于一个真暴露面。所需形式可从支撑超平面定理直接取得，工具归属见 [Rockafellar160, §§11,18]。具体地，若 $\varnothing\ne F_p\ne K$，取 $z\in\operatorname{ri}F_p$。真面不含 $K$ 的相对内点，否则对任意 $y\in K$ 都能将该内点写为以 $y$ 为一端的开线段内点，面性质会迫使 $F_p=K$。因此 $z\in\partial_{\mathrm{rel}}K$。在 $\operatorname{aff}K$ 内的支撑超平面给出非恒定仿射函数 $h$，满足 $h|_K\ge0$、$h(z)=0$。对任意 $y\in F_p$，相对内部性质给出 $w\in F_p$、$0<t<1$ 使 $z=ty+(1-t)w$（$y=z$ 时取 $w=z$），所以非负性强迫 $h(y)=0$。

由于 $K$ 张成 $V$ 且 $\operatorname{aff}K=\{u=1\}$，$h$ 唯一齐次延拓为线性泛函 $g\in V^\ast$；例如若 $h(x)=\ell(x)+b$ 在该超平面上成立，则取 $g=\ell+bu$。其在 $C$ 上非负，且因 $h$ 非恒定而非零。因此

$$
F_p\subseteq Z_K(g)\subsetneq K.
\tag{XIII160.41}
$$

只在 $F_p$ 的相对内点处取支撑，并未将 $p$ 与任意非暴露面强行严格分离；所得零面允许严格大于 $F_p$。若 $F_p=\varnothing$，直接取 $g=u$，有 $Z_K(u)=\varnothing$、$u(p)=1$。这也支付空真面的存在情形。上面的严格性随后保证任何这样的 $g$ 都不消去 $p$。

现在串联各条件。$p\notin F_p$ 立即蕴含 $F_p\ne K$。真面由前段取得非零正支撑，再由严格性取得 EN。EN 的零面包含 $F_p$ 而排除 $p$，故回到 NC。存在不附加 $g(p)>0$ 的非零正支撑也由严格性给 EN，反向直接成立。最后，EN 给出一个包含 $N_p$ 且排除 $p$ 的暴露零面，所以 $p\notin F_{\mathrm{exp}}(N_p)$；反向由 $F_p\subseteq F_{\mathrm{exp}}(N_p)$ 得 NC。

原背景的 $V\ne0$ 与生成性保证 $K,P$ 非空。若 $N_p=\varnothing$，则 $F_p=\varnothing$，NC、真性和 EN 都成立；上述严格性还说明每个非零正泛函均严格正于这个 $p$。若 $F_p$ 是单点，支撑与严格性证明照常适用，无需该纯点自身暴露。若 $K=\{p\}$，张成性给 $\dim V=1$，$\mathcal F_p=\{u\}$、$T_p(p)=1$，故 $N_p=\varnothing$，并且每个非零正泛函都是 $a u$、$a>0$，全部结论直接成立。若 $F_p=K$，$K$ 的张成性排除任何非零正泛函消去它，且 $p\in F_p$；因此 (XIII160.38) 的各项同时不成立，全称式 (XIII160.39) 的前件则为空。证毕。

归一化的边界须单独保留。对任意满足 EN 的 $g$，$e=g/\max_K g$ 确实是原效应且消去全部 $N_p$，但目前只知 $0<e(p)\le1$；只有另证 $g(p)=\max_Kg$，才能称它为 $p$ 的确认者。以 $g(p)$ 作分母也没有自动给 $e\le u$。上述定理不供应共同确认者、菜单 least、$T_p$ 仿射、$D_p$ 凸、投影或操作，也不推出 $F_p$ 自身暴露，或 $F_p=F_{\mathrm{exp}}(N_p)$。它将推论159.13及推论160.6中**实际 NC 与暴露 NC 的比较这一子句**推广到整个原域；FC、全部支持面规则及完整重建与 NC 的等价，仍分别需要原来声明的 L2 + L3 或 L2 + TC 前件。

### 160.9 完整候选的等价简写与几何含义

**推论 160.11（保留 TC 的真面／正支撑版本）。** 在定义160.1的原域内，有完整的条件等价

$$
\begin{aligned}
&\mathrm{L2+TC+NC}\\
\Longleftrightarrow\quad&
\mathrm{L2+TC}+\bigl[\ \forall p\in P:\ F(N_p)\ne K\ \bigr]\\
\Longleftrightarrow\quad&
\mathrm{L2+TC}+\bigl[\ \forall p\in P\ \exists g_p\in C^\ast\setminus\{0\}:\quad
g_p(q)=0\ (q\in N_p)\ \bigr]\\
\Longleftrightarrow\quad&
\text{同原迹归一化表示 (XIII160.14) 及其完整字典 (XIII160.15)}.
\end{aligned}
\tag{XIII160.42}
$$

第三行中的每个 $g_p$ 自动满足 $g_p(p)>0$，故也可将该行写成 L2 + TC + $[\forall p\,\mathrm{EN}(p)]$。这里“共同”只指同一个 $g_p$ 消去一个固定 $p$ 的全部真实零邻点，既不要求不同 $p$ 共用一张支撑，也不把 $g_p$ 预称为确认者。

证明。定理160.10对每个原纯点给出前三行的等价；定理160.5在其原来的 L2 + TC + NC 前件下给出最后一行及反向。完整字典的同一个 $\Phi$、全部原混态、全部原效应、全部确认者和任意非负质量上的最低值，均沿用定理160.5，不从一般正支撑单独推出。$n=1$ 的空邻点和 $n=2$ 的单点邻点端点分别已由定理160.10与定理160.5覆盖。证毕。

白话上，仍在同一块完整状态体和全部原尺中：固定一个纯态，把所有能与它完全区分的原纯态收集起来，再取包含这批邻点的最小实际面。现在只需说这张面没有吞下整块状态体；完整菜单会自动保证它也没有吞下原来的纯态。几何原因是，真面总能放在一张正支撑尺的零面里；如果这张尺连原纯态也读成零，那么把它的全域最大读数归一化，就得到一张确认某个最大值原纯点的尺；取补后，那个最大点就成为原来纯态的零邻点，反而要求原尺在那里同时读零和严格正。因此，这批邻点拥有一张共同的正支撑尺，与 NC 是同一个要求；尺在原纯态处读数严格正，却还没有被证明达到满刻度。把这个较简洁的关系接回已有完整候选时，二元球 L2 和切方向接合 TC 仍负责组织出统一复矩阵商，真邻点面或共同正支撑负责提供等价的 NC，再由159.10排除商核；同一原单位和同一映射随后恢复完整静态概率字典。这一步没有消去 TC，也没有把正支撑提前升级为 least、投影或物理仪器；实际制备、完整复合与旁观者、所有操作和合法未来、物理时间、Hamiltonian、能量与 $\hbar$ 继续遵守 §160.7 的独立合同。

### 160.10 数学归属、精确文献范围与供应总结

| 内容 | 证据归属及使用范围 |
| --- | --- |
| Hermitian Veronesean cap 的 H1–H3、Theorem 2.4、有限指数 | `literature-attested`：[SV160, §2.3, §3.3]；作为一般实域射影商分类直接使用 |
| 射影商中心的禁止相交条件 | `literature-attested`：[CTV160, §1, p. 5] 的商定义；§6解释投影重建；有限域分类本身不用于实锥 |
| 实际 L2 张成交集、H1/H2 供应 | 已发表仓内纸面引理159.5及引理159.6中仅涉及 L2 的 ovoid 段落 |
| 原单位定向、正定形式、迹归一化、纯拓扑、实际支持至多二维限制 | 命题159.7在分类之后的证明；命题160.4明确以新的 cap 供应重接，不直接套其 L3 前件 |
| 全部原菜单、核惯性、原邻点张成与实际面二分 | §159.5、引理159.8–159.9、定理159.10；其供应逐项在定理160.5中验证 |
| 平衡商的闭锥、全纯集、完整原效应及支持 $r<3$ 的实际面 | 定理159.1；每个混态的完整谱 minimum 为定理159.3，特殊原邻点分支为命题159.4 |
| 任意纯集的实际面双正交闭包 | 推论159.13的矩阵支持面与 Galois 推理，经新重建入口复用 |
| TC 的规范原域表述、端点四维直和与 H3 的双向对应、无 L3 的 $N>3$ 供应 | `repo-derived`：定义160.2、定理160.3的几何综合 |
| L2 + TC + NC 的完整同原候选 | `repo-derived`：定理160.5，复用上述分类、归一化与排核，不另宣称新分类 |
| $m=3$ 平衡商对所有实际二元球的 TC、准确切向单射及严格前置分离 | `repo-derived`：定理160.7与推论160.8；其实际面及原菜单基础来自159 |
| MD 的完整菜单定义、全混输入包络等号及有条件 qutrit 重建 | 已发表定义155.1、定理155.2、推论155.5；第156章的纯行前件与条件差距结论保留其未决边界 |
| 真实际面有真暴露超面 | 成熟有限维支撑超平面与面相对内部工具，归属 [Rockafellar160, §§11,18]；定理160.10列出所需论证 |
| 无 L2／L3／TC 的点态 NC、真邻点面、EN 与暴露 NC 等价；所有正支撑严格正于原纯点 | `repo-derived`：定理160.10的完整原菜单最大点／补效应论证；推论160.11仅据此改写定理160.5的 NC 子句 |

本章的直接原始文献核对范围是 [SV160] 的 §2.3（H1–H3 与 Theorem 2.4）和 §3.3（一般指数及有限性），以及 [CTV160] 的 §1（商定义和定理范围）与 §6（投影重建）。仓内复用范围是第159章上述具名结果及其前件；对其他背景文献的归属沿用159，不把这种转引报告为本章重新核对全部原文。数学支持面、极化、有限维凸生成、谱分解及正定合同是标准背景。这里不宣称全球文献搜索完备、历史优先权、严格最小公理数或新的 Hermitian 分类；新增的是有明确原域的几何综合和其严格实际锥分离。

供应链可压缩为

$$
\begin{gathered}
\mathrm{L2}\ \xrightarrow{\ 159.5\ }\ \mathrm{H1,H2},\qquad
\mathrm{L2+TC}\ \xrightarrow{\ 160.3\ }\ \mathrm{H3},\ N>3,\\
\xrightarrow{\ \mathrm{SV}\ 2.4\ }\ \text{有限复 Hermitian 射影商}
\xrightarrow{\ \text{原 }u\text{ 的正定归一化}\ }\ \Psi,\\
\xrightarrow{\ \text{实际支持至多二维与完整原菜单}\ }\ \text{159.10 的全部供应}
\xrightarrow{\ \mathrm{NC}\ }\ \ker\Psi=0
\xrightarrow{\ \text{同一个 }\Phi\ }\ \text{完整原始静态量子字典}.
\end{gathered}
\tag{XIII160.36}
$$

这条链不以 L3、AD、纯 PR、全局纯流形或物理操作饱和性作为隐含前件。

### 160.11 引用

**[SV160]** J. Schillewaert and H. Van Maldeghem, *Hermitian Veronesean Caps*, in *Buildings, Finite Geometries and Groups*, Springer Proceedings in Mathematics 10 (2012), 175–191. [作者原稿](https://cage.ugent.be/~hvm/artikels/204.pdf)，§2.3，原稿 pp. 3–4：ovoid、H1–H3、Theorem 2.4 及 Hermitian Veronesean 坐标；§3.3，pp. 10–11：一般指数的归约及有限环境排除无限指数。本章实际应用的外部分类型定理只有该 Theorem 2.4。

**[CTV160]** B. N. Cooperstein, J. A. Thas, and H. Van Maldeghem, *Hermitian Veroneseans over finite fields*, Forum Mathematicum 16 (2004), 365–381. [作者原稿](https://cage.ugent.be/~hvm/artikels/133.pdf)，§1，原稿 p. 5：不交椭圆空间及相关切四空间的中心所定义的 quotient，Theorems 1.3–1.4 的有限域范围；§6，pp. 18–19：投影重建。用于解释 [SV160] 的商含义，不将有限域分类直接移植到 $\mathbb R$。

**[R160]** *Quantum Origin: Exclusion Segment Rigidity and Pure Locus Topology XII*，第159章，仓内[前卷源码](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md)，[固定版本 d4a6bd75fd78850fed8cf60aebb6ce7fceffa2e1](https://github.com/the-omega-institute/trureturing/blob/d4a6bd75fd78850fed8cf60aebb6ce7fceffa2e1/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md)。定理159.1、159.3和命题159.4供应平衡商；引理159.5供应 L2 张成交集；引理159.6用于 L3 与 TC 的比较；命题159.7的分类后证明供应原单位归一化；引理159.8–159.9、定理159.10供应不使用 L3 的排核；定理159.12用于两套完整候选的比较，推论159.13用于闭包推理。以上均是纸面结果，不是新取得的 Lean 定理。

**[MD160]** 同一前卷 XII 的定义152.1、定义155.1、定理155.2、推论155.5及第156章：$\mathcal A_p$、$B_p$、完整原菜单逐张正序下界、所有原混输入上的下包络等号，以及在完整 EB3 + 纯 PR 背景中的 qutrit 重建。第156章的纯行等号与正差距均有明确前件，其构型结论没有推出裸 EB3 + 纯 PR 的全混态 MD。

**[Rockafellar160]** R. T. Rockafellar, *Convex Analysis*, Princeton University Press (1970), §§11,18。有限维支撑超平面、实际面与相对内部的标准工具归属。定理160.10明确从真面的相对内点取得包含它的真暴露面，随后用完整原菜单证明该暴露面排除 $p$；不引用任意非暴露面与外点可严格分离的错误命题。这是工具归属，不报告全书的独立文献核验。

## 追加锚（本行以下为增补区）

## 161. Three-copy binary geometry and the whole finite state–process theory

On the all-finite original tensor domain below, the complete candidate
requires only that the whole three-copy base have three-ball binary
faces, their intrinsic tangent directions obey TC, and every pure
point's full-menu zero neighbors generate a proper actual face. Relative
to the stated single-cone paper supplier, this is equivalent to one
common complex-matrix coordinate for every original finite cone. The
result gives the finite state/effect/composite dictionary, characterizes
all mathematical branches and instruments, identifies ideal sharp
updates under pointwise neutrality, and classifies any separately
specified continuous reversible real action. Device availability and
physical time and energy calibration remain separate data.

### 161.1 Original objects, the geometric condition, and the supplier

Let $V\ne0$ be a finite-dimensional real vector space and fix $u\in V^*$.
For every integer $N\ge1$, retain the original data

$$
W_N=V^{\otimes_{\mathbb R}N},\qquad
C_N\subset W_N,\qquad u_N=u^{\otimes N},\qquad
K_N=C_N\cap\{u_N=1\},\qquad P_N=\operatorname{ext}K_N.
\tag{161.1}
$$

Each $C_N$ is a closed pointed generating convex cone, and $u_N$ is
strictly positive on $C_N\setminus\{0\}$. The original effect menu is the
whole interval

$$
\mathcal E_N=[0,u_N]_{C_N^*}.
\tag{161.2}
$$

For every split $a+b=N$, $a,b\ge1$, assume

$$
C_a\otimes_{\min}C_b\ \subseteq\ C_{a+b}
\ \subseteq\ C_a\otimes_{\max}C_b.
\tag{161.3}
$$

The minimum cone is generated by positive simple tensors; the maximum
cone consists of the vectors nonnegative on every $f\otimes g$,
$f\in C_a^*,g\in C_b^*$. Products of vectors and functionals, their
pairing, and the tensor units are the original ones. Product functionals
separate the original joint vector space. Every canonical position
permutation and its inverse are positive on the whole original cone.
Reassociation is the actual canonical identity between the two brackets.
These assumptions apply to every finite level, including every correlated
input in its cone. No comparison, spectrality, Jordan structure, metric,
or operation menu is an additional premise.

Here is a fully original formulation of the only geometric assumption.
For $p\in P_N$, define

$$
\begin{split}
\mathcal F_{N,p}&=\{f\in\mathcal E_N:f(p)=1\},\\
T_{N,p}(x)&=\min_{f\in\mathcal F_{N,p}}f(x),\qquad x\in K_N,\\
p^\perp_N&=\{q\in P_N:T_{N,p}(q)=0\}.
\end{split}
\tag{161.4}
$$

The minima exist by finite-dimensional compactness. Write $F_N(A)$ for
the smallest actual face of $K_N$ containing $A$, with
$F_N(\varnothing)=\varnothing$. Define $\mathsf G_N$ by these conditions:

1. **L2:** for every distinct $p,x\in P_N$, the entire actual face
   $B_N(p,x)=F_N(\{p,x\})$ is affinely isomorphic to a nondegenerate
   closed Euclidean three-ball.
2. **TC:** let $\tau_{N,p}(x)$ be the two-dimensional direction of the
   tangent plane at $p$ to the boundary of $B_N(p,x)$. For every
   $p,a,b\in P_N$, $a\ne b$, $p\notin B_N(a,b)$, and every
   $y\in P_N\cap B_N(a,b)$,
   $$
   \tau_{N,p}(y)\subseteq\tau_{N,p}(a)+\tau_{N,p}(b).
   \tag{161.5}
   $$
   These are intrinsic affine tangent directions of the actual balls;
   their sum is a real linear sum.
3. **Proper neighbor face:** for every $p\in P_N$,
   $$
   F_N(p^\perp_N)\ne K_N.
   \tag{161.6}
   $$

Only $\mathsf G_3$ will be assumed. In particular, the menu in (161.4)
at that level is all of $\mathcal E_3$.

We use the following **conditional single-cone supplier** from the pinned
chapter 160 [S160]: Theorems 160.5 and 160.10, equivalently Corollary 160.11,
identify L2 + TC + (161.6), on one nonzero finite real ordered carrier
with its full menu, with the existence of a trace-normalized order
isomorphism onto one complex matrix cone. Theorem 160.10 equates (161.6)
with $p\notin F(p^\perp)$, and also with a nonzero positive functional
annihilating all of $p^\perp$. The supplier includes the single-point
and three-ball endpoints and its full-menu reverse implication.
The reconstruction in this chapter is relative to that paper supplier;
its single-cone proof is not repeated here.

Write $H_d=\operatorname{Herm}_d(\mathbb C)$, with cone
$H_d^+=\operatorname{PSD}_d$ and unit functional $\operatorname{Tr}$.
The target is one integer $n\ge1$ and one real linear isomorphism

$$
\theta:V\longrightarrow H_n,\qquad
u=\operatorname{Tr}\circ\theta,\qquad
\theta^{\otimes N}(C_N)=H_{n^N}^+\quad\text{for every finite }N\ge1.
\tag{161.7}
$$

Kronecker products identify the real tensor product of Hermitian spaces
with the Hermitian space on the complex tensor product. Effects are
transported by the dual inverse of the same map.

### 161.2 Pure spectators supply actual lower faces and their full menus

**Lemma 161.1 (actual pure-spectator face).** Under (161.1)–(161.3), for
every $a,b\ge1$ and $p\in P_b$,

$$
\begin{split}
M_b&=u_a\otimes\operatorname{id}_{W_b}:W_{a+b}\longrightarrow W_b,\\
F_{a|p}&=\{z\in K_{a+b}:M_bz=p\}
       =\{x\otimes p:x\in K_a\}.
\end{split}
\tag{161.8}
$$

This is an actual face of $K_{a+b}$. The map $I_p:x\mapsto x\otimes p$
is a unit-preserving order isomorphism from $C_a\subset W_a$ onto its
face cone in the span of that face. Its inverse there is
$\operatorname{id}_{W_a}\otimes u_b$.

**Proof.** For $z\in C_{a+b}$, testing $M_bz$ against every element of
$C_b^*$ and using the maximum bound proves $M_bz\in C_b$. It preserves
normalized mass. Therefore the inverse image of the extreme point $p$
inside $K_{a+b}$ is a face: a convex decomposition of a member induces
a convex decomposition of $p$.

Apply [P] (“A pure marginal fixes every conditional state”) with its two
factors interchanged. Its inputs here are exactly the minimum bound for
positive state products, the maximum bound for positive functional
products, the tensor unit and pairing, and original local tomography.
Its pure-marginal conclusion gives the second equality in (161.8).
That result uses no S condition. The minimum bound gives every vector
on the right as an original state. The stated inverse and unit identity
follow from $u_b(p)=1$. Taking nonnegative multiples and real spans
proves the order-isomorphism assertion. ∎

The same cited result says that products of pure states are pure. Thus
if $p\in P_1$, both $p$ and $p\otimes p\in P_2$ are legitimate
pure spectators in Lemma 161.1.

**Lemma 161.2 (matrix face, original unit, and effect extension).** Suppose
there is a trace-normalized order isomorphism

$$
\alpha_3:W_3\longrightarrow H_D,\qquad
\alpha_3(C_3)=H_D^+,\qquad \operatorname{Tr}\circ\alpha_3=u_3.
\tag{161.9}
$$

Then there are trace-normalized order isomorphisms

$$
\alpha_1:W_1\longrightarrow H_n,\qquad
\alpha_2:W_2\longrightarrow H_{n^2},\qquad D=n^3
\tag{161.10}
$$

for an integer $n\ge1$. Each identification carries its own entire
original menu onto $0\le A\le I$. Moreover restriction of the entire
original $\mathcal E_3$ onto either pure-spectator face of (161.8) is
surjective onto that face's full intrinsic effect interval.

**Proof.** Fix $p\in P_1$. Lemma 161.1 embeds $K_2$ as the actual face
$F_{2|p}\subset K_3$, and embeds $K_1$ as the actual face
$F_{1|p\otimes p}\subset K_3$. Under $\alpha_3$, each is a face of
the full density-matrix base.

Every nonempty face of that base is exactly

$$
\mathcal D(S)=\{X\ge0:\operatorname{Tr}X=1,\ \operatorname{ran}X\subseteq S\}
\tag{161.11}
$$

for a nonzero complex subspace $S\subseteq\mathbb C^D$. To recall the
support argument, take $\rho$ in the relative interior of the face and
put $S=\operatorname{ran}\rho$. Every other member can occur with a
positive coefficient in a decomposition of $\rho$, so its support lies
in $S$. Conversely $\rho$ is positive definite on $S$; any density
matrix supported in $S$ can occur with a sufficiently small positive
coefficient in such a decomposition. The face property gives (161.11).

Let $S_a$ be the subspace obtained for $a=1,2$, and choose an isometry
$J_a:\mathbb C^{r_a}\to S_a$. Compression of $\alpha_3 I_p$, or of
$\alpha_3 I_{p\otimes p}$, by $J_a$ gives an order isomorphism onto
$H_{r_a}$. Its trace is exactly $u_a$, since the spectator has unit
mass and compression of a supported matrix preserves trace.

Put $d=\dim_{\mathbb R}V>0$. The isomorphisms just obtained imply

$$
d=r_1^2,\qquad d^2=r_2^2,\qquad d^3=D^2.
\tag{161.12}
$$

All ranks are positive integers. Setting $n=r_1$ gives
$d=n^2,r_2=n^2,D=n^3$. This proves the type, dimensions, and units in
(161.10), without a Jordan or self-duality premise on the original
lower carriers.

For completeness, take any effect $f\in\mathcal E_a$. In the compressed
coordinate it has a unique trace matrix $A\in H_{r_a}$. Positivity of
$f$ and $u_a-f$ is exactly $0\le A\le I_{r_a}$, because the map
identifies the entire positive cone. Extend it on the large Hilbert
space by

$$
\widehat A=J_a A J_a^*,\qquad
0\le\widehat A\le J_aJ_a^*\le I_D.
\tag{161.13}
$$

Then $z\mapsto\operatorname{Tr}(\widehat A\alpha_3z)$ is an original
member of $\mathcal E_3$ restricting to $f$. Conversely restriction
of any original effect to a unit-preserving positive embedding is an
intrinsic proper effect. This proves exact equality of the restricted
menu and the full face menu. The same dual argument identifies each
lower carrier's own full menu. The extension is thus proved after the
matrix-face identification; it is not a premise about arbitrary faces
of arbitrary ordered cones. ∎

### 161.3 Aligning the actual two brackets in one local coordinate

**Proposition 161.3 (common low-level coordinate).** If $\mathsf G_3$
holds, there are an integer $n\ge1$ and one trace-normalized
$\theta:V\to H_n$ such that

$$
\theta^{\otimes q}(C_q)=H_{n^q}^+,\qquad q=1,2,3.
\tag{161.14}
$$

The original products of states and effects, pairing, units, both
brackets, and position permutations at these levels are standard in
these coordinates, on their entire vector spaces and cones.

**Proof.** The conditional chapter 160 supplier applied only to
$(W_3,C_3,u_3,K_3,P_3,\mathcal E_3)$ gives (161.9). Lemma 161.2 then
gives (161.10). Start with any of these fixed trace-normalized matrix
coordinates. They need not initially respect tensor products.

The three actual binary products have precisely the following types:

| Original product | Matrix carrier sizes | Source interface used |
| --- | --- | --- |
| $W_1\times W_1\to W_2$ | $n,n,n^2$ | [P] (conditional normal form) |
| $W_2\times W_1\to W_3$ | $n^2,n,n^3$ | The same interface |
| $W_1\times W_2\to W_3$ | $n,n^2,n^3$ | The same interface |

For each row, the minimum bound gives a positive bilinear state product.
The maximum bound gives a positive bilinear product of all positive
functionals. In trace coordinates call them $M,N$. Original pairing
and units say, on the full real spaces,

$$
\operatorname{Tr}(M(x,y)N(f,g))
 =\operatorname{Tr}(xf)\operatorname{Tr}(yg),\qquad N(I,I)=I.
\tag{161.15}
$$

The product maps have the required injectivity and separation from the
original tensor pairing and local tomography. Lemma 161.2 supplies the
whole matrix cones, own full menus, dimensions, and trace units required
by that interface. Its Xu–Zheng–Fošner application therefore gives a
fixed output unitary and fixed input transpose bits for each row. No
positivity on arbitrary entangled inputs in the initial product
coordinates is assumed by this normal-form theorem.

Now apply the post-type argument of [P] (“Three-copy orientation theorem”)
to the following exact objects:

$$
A=W_1,\quad D=W_2,\quad E_L=E_R=W_3,
\tag{161.16}
$$

with the same actual $W_1\times W_1\to W_2$ in both brackets. Their
two trilinear preparation maps are the original canonical tensor map.
Consequently the source's reassociation $\alpha=J_RJ_L^{-1}$ is the
actual identity and is an order isomorphism. Its $P_{12}=J_L\tau_{12}J_L^{-1}$
is the original whole-three-copy swap, positive on all of $C_3$.
The source's simple-sector inputs are exactly $H_n,H_{n^2},H_{n^3}$,
with the three normal forms just obtained. Thus every premise used in
its orientation proof has been supplied here. Its earlier S-to-Jordan
and type-selection suppliers are not invoked.

In the one-sector case its repeated-index identity includes
$\kappa_{11}=0$; the three positions are independent copies even though
their sector labels agree. This removes the relative transpose in the
actual self-composite. The source then gives fixed trace order
coordinates $\theta,\theta_2,\theta_3$ with

$$
\begin{split}
\theta_2(x\otimes y)&=\theta(x)\otimes\theta(y),\\
\theta_3((x\otimes y)\otimes z)
 &=\theta(x)\otimes\theta(y)\otimes\theta(z).
\end{split}
\tag{161.17}
$$

Its identities also hold for the other bracket and for arbitrary
correlated elements of $W_2$, by the source's whole-space spanning
argument. Simple tensors span the original real spaces, so (161.17)
identifies $\theta_2,\theta_3$ with $\theta^{\otimes2},\theta^{\otimes3}$.
Equation (161.14) follows. Pairing determines the effect products on the
whole dual spaces; product action and spanning determine the original
permutations and reassociation.

If $n=1$, all three spaces have dimension one. Trace normalization and
the original product unit directly give (161.17), with ordinary scalar
multiplication. This is also the scalar boundary of the cited normal
form and orientation interfaces. ∎

### 161.4 The complete finite equivalence

**Proposition 161.4 (post-classification finite propagation).** In the
original all-finite domain (161.1)–(161.3), (161.14) for one fixed
$\theta$ implies (161.7) for that same $\theta$.

**Proof.** This is the single-simple-block specialization of the
post-classification proof in [F102]: Lemmas 102.6–102.10 followed by the
two cone inclusions in the proof of Theorem 102.11 after (102.30).
The inputs of that proof are exactly the fixed standard $C_1,C_2,C_3$
in one product coordinate, all finite original minimum/maximum bounds,
and the original positive permutations. All have now been supplied.

More explicitly, its Bell cup and cap use the whole standard $C_2$.
Its original Choi equivalence is proved by slicing arbitrary original
correlated inputs, before any higher cone is identified with PSD.
The two required rank-one three-leg resources are members of the
standard $C_3$. Their product is in the original $C_6$, and the
positive cap gives the entangling gate's Choi element in the original
$C_4$. Lemma 102.10 invokes Harrow [H] (Corollary 2) for exact finite
universality, including unequal grouped dimensions. The state/effect
sandwich after (102.30) then proves both whole-cone inclusions at each
arbitrary finite $N$. This application uses that tail of the proof,
without the S3 or B1–B3 entry of Theorem 102.11. Its resource, universality,
and sandwich proofs need not be repeated.

For $n=1$, every $W_N$ is one-dimensional. The minimum and maximum
cones of positive rays coincide, and (161.3) inductively gives the
positive ray at every level. Thus this endpoint needs no entangling
resource. For $n=2$, the cited resources use two basis vectors in the
same local block; repeated block labels are permitted throughout that
proof. ∎

**Theorem 161.5 (three-copy geometry iff one whole finite complex hierarchy).**
Relative to the conditional single-cone supplier in §161.1, in the
unchanged original domain the following are equivalent:

1. $\mathsf G_3$.
2. There exist $n\ge1$ and one $\theta$ satisfying (161.7).
3. $\mathsf G_N$ holds at every finite level $N\ge1$, using each
   level's own full original menu and actual faces.

Condition 2 preserves all original products, units, effects, pairings,
position permutations, and reassociation, at every finite level.
Necessarily $\dim_{\mathbb R}V=n^2$, so the integer $n$ is determined
by the original local vector space.

**Proof.** Proposition 161.3 and Proposition 161.4 prove $1\Rightarrow2$.
For $2\Rightarrow3$, at each $N$ the trace order isomorphism
$\theta^{\otimes N}$ identifies the whole cone and its full dual
interval with $H_{n^N}^+$ and $0\le A\le I_{n^N}$. The reverse
implication of the chapter 160 supplier, applied to this one carrier,
gives $\mathsf G_N$. Condition 3 includes $N=3$.

Products and the tensor units are preserved by tensor powers of one
local map. Full dual transport preserves the original evaluation on
every vector, hence every original effect. On simple tensors the
original position permutations and reassociation have their standard
action; spanning proves equality on the whole joint spaces. The local
dimension follows already from Lemma 161.2. ∎

This compares geometry at level 3 with geometry at every finite level
for the same whole finite target. It does not compare the strength of
that target with chapter 160's conclusion about a single isolated cone.
No finite prefix replaces the all-finite domain: the propagation proof
uses $C_6$, arbitrary spectator levels, and every requested $C_N$.

At $n=1$, all bases are singletons; L2 and TC are empty conditions,
and the empty neighbor face is proper. At $n=2$, the local $K_1$ is
the full qubit three-ball, whose TC outer-point condition is empty.
The three-copy cone is $H_8^+$; its geometry is the geometry of that
whole cone. These endpoint statements do not substitute the local
menu or local ball for the original three-copy data.

### 161.5 All states, all effects, and the static dictionary

**Corollary 161.6 (full Born and support dictionary).** Under Theorem 161.5,
put $d_N=n^N$. In the same coordinates at every finite level,

$$
\begin{array}{c|c}
\text{Original object}&\text{Matrix object}\\ \hline
C_N&H_{d_N}^+\\
K_N&\{\rho\ge0:\operatorname{Tr}\rho=1\}\\
P_N&\{vv^*:v\in\mathbb C^{d_N},\ v^*v=1\}\\
\mathcal E_N&\{E\in H_{d_N}:0\le E\le I_{d_N}\}\\
f_E(x)&\operatorname{Tr}(E\theta^{\otimes N}x)
\end{array}
\tag{161.18}
$$

For $p$ corresponding to $vv^*=P_v$, its full confirming menu and
all its minimum values are

$$
\begin{split}
\mathcal F_{N,p}&\longleftrightarrow
 \{P_v+B:B=(I-P_v)B(I-P_v),\ 0\le B\le I-P_v\},\\
\min_{f\in\mathcal F_{N,p}}f(x)
 &=\operatorname{Tr}(P_v\theta^{\otimes N}x),\qquad x\in C_N.
\end{split}
\tag{161.19}
$$

Thus the minimum is represented by the same least effect for every
positive input, including zero and every nonnegative mass. All actual
faces are the support faces (161.11), with
$\mathcal D(\{0\})=\varnothing$; all observables, represented by
the real span of effects, are Hermitian matrices with their ordinary
spectral decompositions. A finite mathematical POVM is exactly a family
$E_a\ge0,\sum_aE_a=I$, with probability $\operatorname{Tr}(E_a\rho)$.

**Proof.** These are the full-dual and support consequences of the cone
and trace identities. They are precisely the conclusions of [F102] (Corollary 102.12) after its cone reconstruction, or the full-menu portion
of [S160] (Theorem 160.5) applied to each identified carrier. Neither
application requires a new geometric or S premise. Their least-effect
formula gives (161.19) on the full positive cone. ∎

The scalar endpoint has one normalized state and effects $0\le e\le1$.
For $n\ge2$, all entangled states and all effects on every composite
occur in (161.18). No state or effect is replaced by a product-only menu.

### 161.6 All original spectators, Choi matrices, and rectangular Kraus maps

Use $W_0=\mathbb R,C_0=\mathbb R_{\ge0},u_0=\operatorname{id}$ only as
the scalar tensor convention, with $\theta^{\otimes0}=\operatorname{id}$.
For $m,n'\ge0$, an original real linear
map $F:W_m\to W_{n'}$ is **spectator-positive** when

$$
(\operatorname{id}_{W_r}\otimes F)(C_{r+m})\subseteq C_{r+n'}
\quad\text{for every integer }r\ge0.
\tag{161.20}
$$

The quantifier includes all original correlated inputs and all positions
of the operation, the latter transported by the original permutations.
Write $d=n^m,e=n^{n'}$ and

$$
\Phi=\theta^{\otimes n'}F(\theta^{\otimes m})^{-1}:H_d\to H_e.
\tag{161.21}
$$

Its unique complex linear extension is understood when using matrix
units. In reference–output order set

$$
\Omega_d=\left(\sum_{j=1}^d|j\rangle|j\rangle\right)
          \left(\sum_{j=1}^d\langle j|\langle j|\right),\qquad
J(\Phi)=(\operatorname{id}_d\otimes\Phi)(\Omega_d)
        =\sum_{i,j}E_{ij}\otimes\Phi(E_{ij}).
\tag{161.22}
$$

**Theorem 161.7 (complete original operation dictionary).** The following
conditions on $F$ are equivalent:

1. $F$ satisfies (161.20).
2. $J(\Phi)\ge0$.
3. The complex extension of $\Phi$ is completely positive.
4. For a finite family of rectangular matrices $K_\alpha:\mathbb C^d\to
   \mathbb C^e$,
   $$
   \Phi(X)=\sum_\alpha K_\alpha X K_\alpha^*.
   \tag{161.23}
   $$

The zero map permits an empty family; a family with at most $de$
members always suffices. In these conditions, write
$B=\sum_\alpha K_\alpha^*K_\alpha=\Phi^*(I_e)$. Then

$$
\begin{array}{c|c|c}
\text{Original mass condition}&\text{Kraus condition}&\text{Choi condition}\\ \hline
u_{n'}F=u_m&B=I_d&\operatorname{Tr}_{\rm out}J=I_d\\
u_{n'}Fx\le u_mx\ (x\in C_m)&B\le I_d&\operatorname{Tr}_{\rm out}J\le I_d
\end{array}
\tag{161.24}
$$

Each budget holds also on every correlated spectator input.

**Proof.** Apply [F102] (Lemma 102.7 and Proposition 102.13) to the single
block of Theorem 161.5. Their original self-reference is exactly $m$
copies of the input, with all reference legs retained; its Choi element
is (161.22) under $\theta^{\otimes(m+n')}$. Theorem 161.5 identifies its
entire original target cone with PSD. The source thus applies to every
original spectator and input in (161.20). Its rectangular Choi/Kraus
step is [W] (Theorems 2.22 and 2.26); its zero-map convention is explicit.
This proves all four equivalences and the finite Kraus bound.

When an input or output is scalar, the same rectangular theorem has
$d=1$ or $e=1$. For scalar input the zero-copy reference is the scalar
unit. The Choi test is positivity of the prepared matrix for scalar
input, and positivity of the representing effect for scalar output.
This includes scalar-to-scalar
maps and uses only the scalar convention, without adding a physical
system to the original domain.

The source's budget identity
$\operatorname{Tr}_{\rm out}J=B^{\mathsf T}$ and its full-input trace
budget give (161.24), including every correlated spectator. Transposition
preserves the PSD order. These are full reference-marginal conditions,
as in that source, and cannot be replaced by a total Choi trace. ∎

Consequently all ancillary matrix sizes have ordinary CP positivity,
even though the original spectator quantifier only used the given
tensor powers. This is a consequence of the obtained Kraus formula.
At $n=1$, (161.23) is multiplication by a number $b\ge0$; the
trace-preserving and nonincreasing conditions are $b=1$ and $b\le1$.

### 161.7 Mathematical instruments and every conditional-state law

**Definition 161.8 (mathematically admissible operations).** On the
original objects $W_N$, call all spectator-positive mass-nonincreasing
maps mathematical branches, and all spectator-positive mass-preserving
maps mathematical channels. A finite mathematical instrument
$(F_a)_{a\in A}:W_m\to W_{n'}$ is a finite family of branches whose sum
is a channel. This defines a mathematical operation theory from the
reconstructed ordered hierarchy. Its definition requires no claim
about availability of a device.

**Theorem 161.9 (instruments, probabilities, and conditioning).** In the
coordinates of Theorem 161.5, the complete set of these instruments is

$$
\Phi_a(X)=\sum_\alpha K_{a\alpha}XK_{a\alpha}^*,\qquad
\sum_{a,\alpha}K_{a\alpha}^*K_{a\alpha}=I_d.
\tag{161.25}
$$

Equivalently $J_a\ge0$ and
$\sum_a\operatorname{Tr}_{\rm out}J_a=I_d$. Every branch has a
complementary branch of the same output type. Its effect is

$$
E_a=\Phi_a^*(I_e)=\sum_\alpha K_{a\alpha}^*K_{a\alpha},\qquad
0\le E_a\le I_d,\qquad \sum_aE_a=I_d.
\tag{161.26}
$$

For every original correlated input, the entire update and probability
laws are as follows. Let $z\in C_{r+m}$, set
$Z=\theta^{\otimes(r+m)}z$, and let $M=u_{r+m}(z)\ge0$. Put

$$
Z_a=(\operatorname{id}_{n^r}\otimes\Phi_a)(Z),\qquad
M_a=\operatorname{Tr}Z_a
   =\operatorname{Tr}((I_{n^r}\otimes E_a)Z).
\tag{161.27}
$$

Then $Z_a\ge0$ and

$$
z_a=(\operatorname{id}_{W_r}\otimes F_a)z
 =(\theta^{\otimes(r+n')})^{-1}Z_a\in C_{r+n'}.
$$

Moreover $M_a\ge0$ and $\sum_aM_a=M$. If $M=1$,
$M_a$ is the outcome probability; for $M>0$ it is $M_a/M$ on the
normalized initial state. Whenever $M_a>0$, the conditional joint
state is exactly $z_a/M_a$, represented by $Z_a/M_a$.
If $M_a=0$, then $Z_a=0$ and $z_a=0$, and no
normalized conditional state is prescribed. In particular $M=0$
forces every output to be zero.

The unnormalized conditional spectator state and its sum satisfy

$$
\begin{split}
\sigma_a
 &=\operatorname{Tr}_{\rm out}Z_a\\
 &=\operatorname{Tr}_{\rm in}
   \bigl[(I\otimes\sqrt{E_a})Z(I\otimes\sqrt{E_a})\bigr],\\
\sum_a\sigma_a&=\operatorname{Tr}_{\rm in}Z.
\end{split}
\tag{161.28}
$$

Thus the conditioned spectator marginal depends on the effect, and
the whole output update depends on the branch. All finite sequential,
adaptive, coarse-grained, and tensor-product instruments obey the
corresponding sum, composition, and conditional probability rules.

**Proof.** Theorem 161.7 applied to the branches and their sum gives
(161.25)–(161.26) and the Choi formulation. The complement construction
is [F102] (Proposition 102.15), used as a mathematical construction:
for a branch with budget $B\le I_d$, choose a unit output vector $v$
and an input orthonormal basis $b_j$. The matrices

$$
L_j=|v\rangle\langle b_j|\sqrt{I_d-B}
\tag{161.29}
$$

are exactly its complementary Kraus family. Its statement covers every
nonzero output size, including size 1, and the zero-probability cases.

Spectator positivity and the budget give the positivity and mass claims
in (161.27). Strict positivity of the original unit, equivalently the
trace on PSD matrices, gives the zero-mass assertion. Division by a
strictly positive mass gives exactly the normalized conditional state.
For (161.28), testing either side against an arbitrary spectator matrix
$G$ gives $\operatorname{Tr}((G\otimes E_a)Z)$, by adjointness and
trace cyclicity. This proves equality on the whole spectator space.
Summing and using $\sum_aE_a=I_d$ proves the last identity.

If a later instrument has branches $\Psi_b$ with Kraus matrices
$L_{b\beta}$, the joint branches are $\Psi_b\Phi_a$, with matrices
$L_{b\beta}K_{a\alpha}$. Their total budget is $I_d$.
Their normalized-input probabilities are

$$
p_{ab}=\operatorname{Tr}(\Psi_b\Phi_a(\rho)),\qquad
\sum_bp_{ab}=p_a,\qquad
p(b\mid a)=p_{ab}/p_a\quad(p_a>0).
\tag{161.30}
$$

For a choice of the later instrument depending on $a$, its total
budget is $I_e$ separately at each $a$, so the same computation
applies. Induction gives every finite adaptive tree, including all
correlated spectator inputs. Coarse-graining adds branches and their
unnormalized outputs; the conditioned coarse-grained state is their
sum divided by its positive total mass. Tensoring instruments tensors
their Kraus matrices, and their total budget is $I_d\otimes I_{d'}$.
Identities and the original permutations are channels, and these
calculations prove closure under the stated operations. ∎

Every original effect occurs as a mathematical branch effect: for a
fixed normalized output state $\omega$, the map
$X\mapsto\operatorname{Tr}(EX)\omega$ is CP with budget $E$.
The same construction simultaneously realizes every finite mathematical
POVM as a mathematical instrument. On equal input and output types,
$X\mapsto\sqrt{E_a}X\sqrt{E_a}$ supplies another such instrument.
These are existence statements; a POVM does not specify a unique
post-measurement state. All state preparations of nonnegative mass at
most one and all effects also fit the scalar input or output convention.

Definition 161.8 is the mathematical admissibility choice. An actual
device menu can be specified separately, and identifying it with this
entire theory is the event-saturation choice of [F102] (Definition 102.14).
That choice is not required for any mathematical statement above.

#### 161.7.1 Ideal sharp update: the existing positive-neutral supplier

Fix $k\ge1$, write $d=n^k$ and $\Theta_k=\theta^{\otimes k}$.
A sharp effect here means an original $e\in\mathcal E_k$ whose
representing matrix in (161.18) is an orthogonal projection $P$.
For an original positive real-linear endomorphism $K:W_k\to W_k$,
suppose

$$
u_kK=e,\qquad
Kp=p\quad\text{for every }p\in P_k\text{ with }e(p)=1.
\tag{161.30a}
$$

The second condition is pointwise neutrality on **every** certain-yes
pure state, including all rays in a degenerate yes subspace. By their
convex decompositions it is equivalent to fixing every normalized
certain-yes state. It is an additional condition specifying an ideal
sharp branch, and is not inferred from sharpness of the effect.

Apply the already published [Atlas161], Proposition 13.4, item 1
(the “Proposition 13.4.1” supplier in [WSharp161], “Sharp neutral
branches reuse the existing uniqueness argument”). The exact
substitution is the single matrix sector $H_d$, the projection $P$,
and the positive real-linear map
$\Lambda=\Theta_k K\Theta_k^{-1}$. Its complex-linear extension is
Hermiticity-preserving and positive. The first identity in (161.30a)
is precisely $\Lambda^*(I_d)=P$; the second fixes every normalized
rank-one projection from $\operatorname{Ran}P$, since (161.18)
parametrizes **all** original pure states. Thus that existing
single-system positive sharp-neutral uniqueness proof gives

$$
\Lambda(X)=PXP\quad(X\in H_d),\qquad
K=\Theta_k^{-1}\bigl[X\mapsto PXP\bigr]\Theta_k.
\tag{161.30b}
$$

The supplier proves equality on the full Hermitian space (and its
complex-linear extension), with no a priori CP or reference-positivity
premise. Complete positivity follows from the obtained compression;
Theorem 161.7 then gives all original spectator extensions. This is a
direct application of the existing uniqueness result, not a new
uniqueness proof. At $P=0$ it gives $K=0$, with an empty certain-yes
set; at $P=I_d$ it gives $K=\operatorname{id}$, since every pure state
is certain-yes. These include $d=1$, where those are the only projections.

Consequently a finite orthogonal resolution $\sum_aP_a=I_d$,
$P_aP_b=0$ for $a\ne b$, has the unique ideal neutral branches
$\Lambda_a(X)=P_aXP_a$. They form a mathematical instrument, including
zero projections. On any normalized original correlated input,
represented by $Z\ge0$, the usual selective and nonselective laws are

$$
\begin{split}
p_a&=\operatorname{Tr}((I\otimes P_a)Z),\\
Z_{\mid a}&=\frac{(I\otimes P_a)Z(I\otimes P_a)}{p_a}
                    \quad(p_a>0),\\
Z_{\rm ns}&=\sum_a(I\otimes P_a)Z(I\otimes P_a).
\end{split}
\tag{161.30c}
$$

Inverse transport by the same tensor powers returns the original
conditional states. For $p_a=0$ the unnormalized output is zero and
there is no prescribed normalized state. This is the standard Lüders
update correspondence under the explicit ideal-neutrality condition.

A sharp effect by itself still allows different updates: the qubit
control in [WSharp161] uses $P_bXP_b$ and $SP_bXP_bS^*$, where $S$
swaps the two basis vectors. Their effects agree and both outcome
sums preserve trace, while their conditional states and subsequent
measurement laws differ. Repeatability of the **outcome** is also
weaker than pointwise neutrality. As in [Atlas161], Proposition 7.3,
item 2, for a degenerate $P$ choose a unitary $V$ commuting with $P$
and rotating rays within $\operatorname{Ran}P$. Then

$$
\Lambda_P(X)=VPXPV^*,\qquad
\Lambda_P^*(I)=P,\qquad
\operatorname{Tr}(P\Lambda_P(X))=\operatorname{Tr}\Lambda_P(X)
\quad(X\ge0).
\tag{161.30d}
$$

Together with $(I-P)X(I-P)$ this is a mathematical instrument: the yes
outcome is certain upon repetition, yet a rotated certain-yes pure
state is disturbed. Hence outcome repeatability cannot supply
(161.30a). Declaring an actual device ideal includes that pointwise
neutrality law; the cone equivalence supplies the conditional
correspondence, without asserting existence of such a device.

### 161.8 A supplied continuous reversible law has a Hamiltonian generator

**Theorem 161.10 (classification of a specified real action).** Assume
Theorem 161.5 and fix a finite $k\ge1$. Suppose an original family of
real linear maps $A_t:W_k\to W_k$, $t\in\mathbb R$, is given with

$$
A_0=I,\quad A_{s+t}=A_sA_t,\quad
A_t(C_k)=C_k,\quad u_kA_t=u_k,
\tag{161.31}
$$

and $t\mapsto A_t$ continuous in the finite-dimensional operator
topology. No implementing unitary family is supplied. Put $d=n^k$.
There is a selfadjoint $H\in H_d$, unique modulo a real multiple of
$I_d$, such that in the reconstructed coordinates

$$
\widetilde A_t(X)=e^{-itH}Xe^{itH},\qquad
\mathcal L(X)=\left.\frac{d}{dt}\widetilde A_t(X)\right|_{t=0}
             =-i[H,X].
\tag{161.32}
$$

The conclusion holds also for $d=2$. For $d=1$, the supplied group
is the identity and every selfadjoint scalar represents its generator.

**Proof.** Transport (161.31) to $H_d$; denote the transported group
by $B_t$. First, a trace-preserving order automorphism $B$ of $H_d$,
$d\ge2$, has one of the two forms

$$
B(X)=UXU^*\quad\text{or}\quad B(X)=UX^{\mathsf T}U^*,\qquad U\in U(d).
\tag{161.33}
$$

Indeed an order automorphism maps extreme rays of the PSD cone onto
extreme rays; trace preservation maps their normalized generators onto
rank-one projections. The equal-size one-factor rank-one preserver
classification [X] (Proposition 2.1), in the trace-normalized application
[P] (“Scalar-factor boundary”), applies to this injective real linear
map. Positivity removes the negative sign, and trace preservation makes
the invertible congruence matrix unitary. This is a mature classification
application, without a dimension-three Wigner premise.

The two sets of maps in (161.33) are compact and disjoint when $d\ge2$.
For disjointness, if transpose were inner on Hermitian matrices, its
complex linear extension would be an algebra automorphism of $M_d$.
It is also an algebra antiautomorphism, which would force all matrices
to commute. Compactness follows from compactness of $U(d)$. They are
therefore separated closed subsets of the automorphism set. Continuity,
connectedness of $\mathbb R$, and $B_0=I$ put every $B_t$ in the first
set. This establishes unitary implementability pointwise, before any
unitary path has been chosen.

The remaining step is the ordinary finite-dimensional continuous
one-parameter group and generator calculus, applied here to the supplied
order action. Its hypotheses and local lift can be exhibited explicitly.
For sufficiently small $\varepsilon>0$, the operator

$$
Q_\varepsilon=\int_0^\varepsilon B_s\,ds
\tag{161.34}
$$

is invertible since $Q_\varepsilon/\varepsilon\to I$. The group law gives
$B_tQ_\varepsilon=\int_t^{t+\varepsilon}B_s\,ds$. Hence $B_t$ is
differentiable and

$$
B_t'=B_tL,\qquad
L=(B_\varepsilon-I)Q_\varepsilon^{-1},\qquad B_t=e^{tL}.
\tag{161.35}
$$

In particular its entries are smooth. A smooth local unitary lift can
now be constructed from $B_t$ itself. Fix the standard basis $e_j$,
put $R_t=B_t(E_{11})$, and, near $t=0$, define

$$
v_1(t)=\frac{R_te_1}{\sqrt{\langle e_1,R_te_1\rangle}},\qquad
v_j(t)=\widetilde B_t(E_{j1})v_1(t),\quad 2\le j\le d.
\tag{161.36}
$$

The denominator is positive near zero; $\widetilde B_t$ here means the
unique complex linear extension. Formula (161.33) in its first branch
shows that these vectors are the columns of an implementing unitary,
all multiplied by the same phase. Thus $U(t)e_j=v_j(t)$ is a smooth
unitary, $U(0)=I$, and $B_t=\operatorname{Ad}_{U(t)}$ near zero.
This lift has been derived from the supplied order action.

Let $K=U'(0)$. Differentiating $U(t)^*U(t)=I$ gives $K^*=-K$, and
differentiating the conjugation gives $L(X)=KX-XK$. Set $H=iK$, so
$H=H^*$ and $L=-i[H,\cdot]$. Equations (161.35) then give (161.32)
for all real $t$, since conjugation by $e^{-itH}$ has the same
generator and initial identity. If two selfadjoint matrices give the
same group, their difference commutes with every Hermitian matrix and
hence with $M_d$; it is a real scalar. Conversely such a scalar does
not change the group.

For $d=1$, trace normalization forces each $B_t$ to be the identity;
the same scalar-uniqueness statement holds. ∎

Both directions of time in this theorem are mathematical channels with
all original spectators, by Theorem 161.7. Static geometry does not
select the supplied action: $H=0$ and, for $d\ge2$,
$H=\operatorname{diag}(0,1,0,\ldots,0)$ give different actions on the
same complete hierarchy. The replacement $t\mapsto ct$ replaces the
generator by $cH$ and preserves all static data. Formula (161.32)
classifies a specified continuous real action; a physical clock, an
energy assignment, and a numerical $\hbar$ require their own calibration.

For any initial unit vector $\psi_0$, the representative
$\psi(t)=e^{-itH}\psi_0$ satisfies the Schrödinger equation
$i\dot\psi=H\psi$, and every density matrix satisfies
$i\dot\rho=[H,\rho]$. A scalar shift of $H$ changes only the vector's
overall phase. If a physical time coordinate and an energy calibration
are additionally chosen, writing $H_{\rm phys}=\hbar H$ gives
$i\hbar\dot\psi=H_{\rm phys}\psi$ and
$i\hbar\dot\rho=[H_{\rm phys},\rho]$. These are correspondences for
the specified group, not a selection of the group or of $\hbar$ by
static geometry.

### 161.9 A full-menu all-finite boundary at one-copy geometry

**Proposition 161.11 (the separable hierarchy).** For each $n\ge2$,
take the original local space $V=H_n$, $u=\operatorname{Tr}$, and,
under its ordinary real tensor identification, set

$$
S_N=\operatorname{cone}\{X_1\otimes\cdots\otimes X_N:X_i\in H_n^+\}.
\tag{161.37}
$$

The data $C_N=S_N$, for every finite $N\ge1$, satisfy the full
original domain (161.1)–(161.3), with full own menus, positive original
permutations and actual reassociation. Their $C_1$ is standard and
satisfies $\mathsf G_1$. They fail (161.7), and their whole $K_3$
fails L2.

**Proof.** The normalized base of $S_N$ is the convex hull of the compact
set of product density matrices, hence compact. Its cone is closed,
pointed as a subcone of PSD, and generating because local PSD matrices
span $H_n$ and their products span $W_N$. Trace is strictly positive
on every nonzero member, and $u_N=u^{\otimes N}$.

For every split, flattening the finite conic sums gives exactly

$$
S_{a+b}=S_a\otimes_{\min}S_b.
\tag{161.38}
$$

If $f\in S_a^*,g\in S_b^*$, their product is nonnegative on each
positive simple tensor and hence on this whole cone. This proves the
maximum bound at every split, with the block cones $S_a,S_b$ themselves.
All original position permutations preserve product generators and have
positive inverses. Canonical reassociation is the identity, and the
original vector and dual products have exact pairing and local
tomography.

The entire dual and effect menu are explicitly

$$
\begin{split}
S_N^*&=\{A\in H_{n^N}:\langle v_1\otimes\cdots\otimes v_N,
 A(v_1\otimes\cdots\otimes v_N)\rangle\ge0\ \text{for all }v_i\},\\
\mathcal E_N&=\{A\in H_{n^N}:0\le
 \langle v_1\otimes\cdots\otimes v_N,
 A(v_1\otimes\cdots\otimes v_N)\rangle\le1
 \ \text{for all unit }v_i\}.
\end{split}
\tag{161.39}
$$

Rank-one local generators establish these equalities for all product
PSD generators and hence for the whole cone. These are full original
menus. For example the two-factor flip matrix is a member of
$\mathcal E_2$, since its product expectation is
$|\langle v_1,v_2\rangle|^2\in[0,1]$, although it has eigenvalue $-1$
on an antisymmetric vector.

Now $S_1=H_n^+$, so the reverse single-cone supplier gives
$\mathsf G_1$. But the two-dimensional Bell projection is not in
$S_2$. Indeed in a positive sum representing a rank-one PSD matrix,
every summand's range lies in its one-dimensional range. A nonzero
positive product summand has a product vector in its range, whereas the
Bell line contains no product vector. This is impossible. Any local
order coordinate $\theta$ taking $S_1$ to a full $H_n^+$ takes
$S_2$ to the cone of positive local products again, so it cannot turn
this hierarchy into (161.7). The local dimension fixes the same $n$.

There is also a direct whole-three-copy geometric failure. Select
orthogonal local vectors $0,1$. The quantum support face on
$S=\operatorname{span}\{|000\rangle,|111\rangle\}$, intersected with
the separable base, is an actual face of that base. A fully product
vector in $S$ is proportional to one of these two vectors: a
superposition with both coefficients nonzero has Schmidt rank two
already across the first-versus-rest split. Positivity of every
summand forces its support into $S$. The intersection is therefore
exactly the segment joining the two product projections. Since the
minimal face of this segment containing both endpoints is the segment,
it is their entire actual generated face in $K_3$. It is not a
three-ball, so L2 fails. ∎

This supplies an all-finite countermodel to promotion from one-copy
geometry to the whole quantum hierarchy, while preserving full menus
and every split bound. It makes no assertion that two-copy geometry
is insufficient; no such countermodel is used here. At $n=1$, the
separable and quantum hierarchies coincide.

### 161.10 Correspondence with the familiar finite quantum axioms

The following dictionary uses the same $\theta$ throughout. The Hilbert
spaces $\mathcal H_N=(\mathbb C^n)^{\otimes N}$ are obtained coordinate
carriers for the reconstructed cones; no quantum reference was assumed
in the original domain. Every row retains the assumptions named in its
last column.

| Familiar quantum ingredient | Exact correspondence | Mathematical status and conditions |
| --- | --- | --- |
| Hilbert rays and density operators | $P_N\simeq\mathbb{CP}^{n^N-1}$ and $K_N\simeq\{\rho\ge0:\operatorname{Tr}\rho=1\}$, including every mixed and entangled state | Derived from $\mathsf G_3$ in the original all-finite domain, relative to [S160], [P] and the [F102] tail |
| Observables and projective statistics | Every Hermitian $A=\sum_j a_jP_j$ gives a spectral PVM, with probabilities $\operatorname{Tr}(P_j\rho)$ and mean $\operatorname{Tr}(A\rho)$ | Matrix spectral calculus after cone reconstruction; interpreting a real span of effects as observables fixes the mathematical dictionary |
| Born rule and general finite measurements | $f_E(x)=\operatorname{Tr}(E\theta^{\otimes N}x)$, $0\le E\le I$; a POVM is $E_a\ge0$, $\sum_aE_a=I$ | Full original dual interval and original evaluation; all such mathematical effects are retained |
| Tensor composites and reduced states | $\mathcal H_{a+b}=\mathcal H_a\otimes_{\mathbb C}\mathcal H_b$; all original products, swaps and brackets are standard; discarding is partial trace | Derived with one common local coordinate; original marginal positivity comes from the maximum bound |
| Quantum operations and channels | All rectangular CP maps with Kraus form; branch budget $\sum_\alpha K_\alpha^*K_\alpha\le I$, channel budget equality | Exact characterization of maps positive on every original spectator and correlated input; calling all of them mathematical operations is Definition 161.8 |
| Instruments and conditional states | Finite CP branch families with total budget $I$; $p_a=\operatorname{Tr}\Phi_a(\rho)$ and $\rho_a=\Phi_a(\rho)/p_a$ when $p_a>0$ | Mathematical instruments and normalization, including adaptive histories and all original spectator marginals; zero-probability states remain unspecified |
| Ideal sharp measurement update | $\Phi_a(X)=P_aXP_a$ and the selective/nonselective laws (161.30c) | Existing [Atlas161] Proposition 13.4(1), via [WSharp161]: positivity, projection effect and pointwise neutrality on every certain-yes pure state; CP is a consequence |
| Reversible Schrödinger evolution | $A_t=\operatorname{Ad}_{e^{-itH}}$, $H=H^*$ modulo scalars; $i\dot\psi=H\psi$ and $i\dot\rho=[H,\rho]$ | Conditional on a specified continuous normalized original order-automorphism $\mathbb R$-group at the fixed finite level; no unitary family is assumed |

For the reduced-state row, the original marginal is
$(\operatorname{id}_{W_a}\otimes u_b)z$. Testing against every original
effect and using tensor pairing shows that its coordinate is exactly
$\operatorname{Tr}_{\mathcal H_b}(\theta^{\otimes(a+b)}z)$, including
all correlated $z$. This also explains the original meaning of the
partial traces in (161.28).

Thus the state, probability and composite axioms in this finite target
are consequences of the stated geometric reconstruction. The operation
class is the mathematical definition by spectator positivity and mass
budget, characterized by the reused CP theorem. The ideal-sharp law
adds its disturbance condition; continuous dynamics adds its specified
real action. Identifying these mathematical operations with actual
devices, or $H$ with physical energy in calibrated time, requires the
corresponding realization and calibration data. No infinite-dimensional
or field-theoretic conclusion is included.

### 161.11 Attribution, exact dependence, and Chinese reading

The actual-face descent from one trace-normalized $C_3$ supplies the
lower trace units, integer dimensions, full effect restriction, and the
matching to the existing product and orientation interfaces. The
common-coordinate step applies those interfaces; the all-finite cone
propagation and Choi/Kraus representation are the cited
post-classification results. The sharp-update correspondence directly
reuses the existing positive-neutral uniqueness result. The
reversible-law argument applies the mature one-factor rank-one
preserver classification and finite-dimensional continuous-group
calculus to obtain the unitary lift and generator. These applications
carry no classification, universality, dynamics or sharp-update novelty
claim, no minimum-independent-axiom claim, and no formal verification
claim.

| Source | Exact contribution used here |
| --- | --- |
| [S160] | Conditional Theorem 160.5: full-menu L2 + TC + NC iff one trace-normalized complex matrix cone; Theorem 160.10/Corollary 160.11: proper actual neighbor face and positive-annihilator versions; all endpoint cases |
| [P], pure-marginal section | Pure marginal forces the product with its other marginal, and products of pure states are pure; only the actual product/pairing/minimum/maximum/tomography contract is used |
| [P], conditional normal form and scalar boundary | Actual positive state/effect products on the already supplied $H_r,H_s,H_{rs}$, exact pairing and units, give fixed unitary/transpose normal forms |
| [P], three-copy orientation proof | Same actual self-composite in both brackets, positive actual reassociation and whole-triple spectator swap, including repeated indices, align the fixed coordinates |
| [F102] | Lemmas 102.6–102.10 and the proof after (102.30): low standard cones to all finite cones; Corollary 102.12, Proposition 102.13, Definition 102.14 and Proposition 102.15: full dictionary and mathematical instruments |
| [X] | Unnumbered Main Theorem, p. 409, (1.1)–(1.2), and Proposition 2.1, pp. 410–411: the mature rank-one preserver classifications used by the normal-form interface and Theorem 161.10 |
| [H] | Corollary 2, unequal dimensions allowed: exact finite universality, as used in Lemma 102.10 |
| [W] | Theorems 2.22 and 2.26: finite rectangular Choi/Kraus and trace-preservation characterizations, as used in Proposition 102.13 |
| [Atlas161], [WSharp161] | Proposition 13.4, item 1, and its “Sharp neutral branches” application: positive real-linear sharp branch plus all-certain-yes pointwise neutrality gives full-space compression and automatic CP, including zero and identity projections; Proposition 7.3, item 2, and the same-effect control distinguish outcome repeatability and sharp effects from neutrality |

The equivalence remains conditional on [S160] as stated, and on the
specified paper interfaces [P] and [F102]. Lemmas 161.1–161.2 supply
the actual-face, original-unit, lower-type, dimension and full-menu
bridges; Proposition 161.3 supplies the inputs of the fixed-coordinate
orientation argument. Proposition 161.4 retains every original finite
cone and spectator used by the tail. Theorem 161.10 constructs its
unitary lift from the specified original order action.
Mathematical admissibility is defined in Definition 161.8; the actual
availability of devices, a chosen reversible action, and physical time
and energy calibrations are separate data, outside the state-cone iff.

中文说明：把每个纯态想成一个端点，把原效应想成刻度从零到一的尺子；本章始终
保留每个有限份数的整块原态体和全部原尺，只在整个三份态体上要求：任意两端点
生成整块三维闭球，原切方向按 TC 接合，每个端点的全部零邻点生成一张真面。
关键桥是固定一个真正的纯旁观者：所有具有这个纯边缘的原联合态恰好组成一张
实际面，而且与较低份数的整个原态锥保单位地同构。三份锥经第160章的条件供应
成为一个复矩阵锥后，这些面就是完整矩阵支持面，一份、二份的类型、维数、迹单位
及各自全部效应随之确定；大菜单向面菜单的满射由支持压缩给出。随后复用实际
产品正规形和同一三份的正重括号、正交换，取得一个共同局部坐标，再接回已发表的
全有限尾部：纯态成为复 Hilbert 射线，混态成为密度矩阵，原尺的评价就是 Born
配对，所有原复合和相关输入都得到保留；在全部原旁观者上保持正性并满足质量
预算的映射恰为矩形 Kraus 分支，有限仪器及条件态按分支质量归一化。锐尺还没有
决定测后状态；若另要求理想锐分支逐点保持每一个本来必答“是”的纯态，就可直接
复用已有正性唯一性结果，得到 Lüders 压缩及其所有相关旁观扩张，不必预先假设
CP。只保证结果可重复，仍允许在退化的“是”子空间里旋转，不能替代这种不扰动。
另给连续可逆实时间群时，成熟秩一保持分类与连续群计算从原群本身推出酉演化及
唯一到标量的自伴生成元，继而得到 Schrödinger 与 von Neumann 方程；恒等演化
和非平凡演化却共享同一几何，所以几何不选择时间群、物理钟、能量或 $\hbar$。
实际设备是否实现全部数学分支，也要另给实现数据。全部可分态层级保留每一有限层
的完整原菜单，却只有一份几何而没有完整量子复合，准确说明这一份入口不够；本章
没有声称存在二份入口的反例，也没有把“三份代替全层几何”的等价说成弱化第160章
单系统结论。

[S160]: https://github.com/the-omega-institute/trureturing/blob/4684b73af5cafe08b88b4f4433533e5b1741b1ad/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md "Pinned chapter 160, conditional single-cone supplier."
[P]: https://github.com/the-omega-institute/trureturing/blob/f5a6211e591351e1a2bdeea0165c2ef29ad21b48/Library/QuantumStates/barnumhilgert2019spectral.md "Pure marginal; conditional matrix-product normal form and scalar boundary; three-copy orientation."
[F102]: https://github.com/the-omega-institute/trureturing/blob/f5a6211e591351e1a2bdeea0165c2ef29ad21b48/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "Chapter 102 post-classification finite hierarchy and operation/instrument interfaces."
[X]: https://doi.org/10.1017/S1446788714000603 "Jinli Xu, Baodong Zheng, Ajda Fošner, Linear maps preserving tensor products of rank-one Hermitian matrices, J. Aust. Math. Soc. 98 (2015), 407–428."
[H]: https://arxiv.org/abs/0806.0631v1 "Aram W. Harrow, Exact universality from any entangling gate without inverses, Corollary 2."
[W]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf "John Watrous, The Theory of Quantum Information, Theorems 2.22 (pp. 82–83) and 2.26 (pp. 87–89); Cambridge University Press, 2018, DOI10.1017/9781316848142."
[Atlas161]: https://github.com/the-omega-institute/trureturing/blob/0826c2f31d52656aa8b51ccc676896bc7693fad7/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md "Pinned Atlas: Proposition 13.4, item 1 (Proposition 13.4.1), positive sharp-neutral uniqueness; Proposition 7.3, item 2, repeatable but disturbing sharp branches."
[WSharp161]: https://github.com/the-omega-institute/trureturing/blob/0826c2f31d52656aa8b51ccc676896bc7693fad7/Library/Quantum/watrous2018theory.md "Pinned sharp-neutral application and same-effect/different-update control; this uniqueness supplier is Atlas Proposition 13.4.1, not an instrument dictionary."

## 追加锚（本行以下为增补区）

## 162. 原二元球的对径满宽、精确供应复用与三复制全有限重建

本章在同一个完整有限原域上给出候选 **L2 + NC + AD**，等价地写成 **L2 + NC + DS**，并将它接到全部原态、原效应和任意非负质量的复矩阵 Born 字典。L2 给实际二纯点面的整颗三球，NC 给全部原零邻点的一张共同正支撑，AD 要求每条球直径都能由原全域效应完全区分；DS 是同一要求的差体截面形式。least 确认、互易、完整混合律以及其后的剥离、自对偶和面投影已有精确供应，本章直接复用。新增纸面工作集中在这些供应的原域匹配、DS 等价、完整 Alfsen–Shultz 定义核对、coatom 入口及以下两个应用：在161的原全有限背景中只检查整个三复制锥；在单系统上由 complete EB3 + 实际 L2 得到且仅得到复 qutrit。

这里的“原”指给定锥和单位所决定的全部对象，不是选出的量子子集。“实际面”指满足线段性质的凸面，亦不表示已有设备实现。本章不输入 TC、pure PR、自对偶、谱性、projectivity、齐次性或纯态传递性。

### 162.1 完整原域与候选

**定义162.1（原对象）。** 令 $V\ne0$ 为有限维实空间，$C\subset V$ 为闭、尖、生成凸锥，$u\in V^*$ 严格正于 $C\setminus\{0\}$。固定

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x)\quad(p\in P,\ x\in C),\\
N_p=\{q\in P:T_p(q)=0\},\qquad
D_p=\{x\in K:T_p(x)=0\}.
\end{gathered}
\tag{162.1}
$$

$K$ 非空紧，$K=\operatorname{conv}P$，$C=\operatorname{cone}P$，$P$ 张成 $V$，这里的分解均为有限和。紧性可由反证得到：无界归一点除以其范数的极限会给非零 $c\in C$、$u(c)=0$。有限维凸生成给其余结论，不预设 $P$ 闭。效应区间在 $K$ 的有限张成子集上的值都属于 $[0,1]$，因而闭且有界；$\mathcal F_p$ 是含 $u$ 的紧集。所以 minimum 达到，且 $T_p(x)=0$ 等价于存在一张原确认效应在 $x$ 读零。

记 $p\perp q\iff q\in N_p$。补效应 $u-f$ 证明零关系对称，$p\not\perp p$；这不假设数值 pure PR。$F(A)$ 是包含 $A\subset K$ 的最小实际面，$F(\varnothing)=\varnothing$。归一底面与锥面的对应是 $F\mapsto\mathbb R_+F\cup\{0\}$、$H\mapsto H\cap K$：将正分解按原质量归一即可双向验证面性。因此所有锥面的交所给的 pair base 正是 $F(p,q)$，没有将实际面换成暴露面。面内的面仍为原面；对锥面 $H$ 有 $C\cap\operatorname{span}H=H$，因为 $z=a-b\in C$、$a,b\in H$ 时 $a=z+b$ 迫使 $z\in H$。

**定义162.2（L2、NC、AD、DS）。**

* **L2：** 每个不同 $p,q\in P$ 的整个 $B=F(p,q)$ 仿射同构于闭 Euclidean 三球。整个球面就是 $P\cap B$，由面性及仿射极点对应得到。
* **NC：** 对每个 $p\in P$，$p\notin F(N_p)$。
* **AD：** 对每颗实际二元球 $B$ 及每个 $p\in P\cap B$，内禀对径点 $p_B^*$ 满足 $p\perp p_B^*$。

AD 沿用已发表 XII §159.4 的含义。在球坐标 $z\in\overline{\mathbb B}^3$、$s\in S^2$ 下，对应 $x\in B$、$p\in P\cap B$，记

$$
b_p^B(x)=\frac{1+s\cdot z}{2}.
\tag{162.2}
$$

球心、对径和此读数均不依赖球坐标；此时 $b_p^B$ 只是球上函数，未预称为原效应。另置

$$
\Delta=K-K\subset\ker u,\qquad E_B=\operatorname{span}_{\mathbb R}(B-B),
\qquad
\mathrm{DS}:\ B-B=\Delta\cap E_B\quad\text{对每颗实际二元球 }B.
\tag{162.3}
$$

下面证明 L2 下 AD 与 DS 等价；它们是同一候选的两种写法，不是两项独立要求。

### 162.2 差体截面与全部球效应的精确延拓

**引理162.3（满宽等价）。** $\Delta$ 是 $\ker u$ 中含零内点的紧对称凸体，记其 Minkowski 范数为 $\|\cdot\|_\Delta$。对不同原纯点，

$$
p\perp q\quad\Longleftrightarrow\quad\|p-q\|_\Delta=1.
\tag{162.4}
$$

在 L2 下，AD、DS 和“每颗实际二元球上的每个 proper 仿射效应都可延拓为 $\mathcal E$ 中的原效应”三者等价。

**证明。** $\operatorname{aff}K=\{u=1\}$，故 $K$ 的相对内点给差体的零内点。若 $f\in\mathcal E$ 在 $p,q$ 分别读一、零，则 $\max_\Delta f=1=f(p-q)$，因此差值在单位体边界。反之，范数一给 $p-q$ 处的支撑线性函数 $h$。将 $h$ 任意延拓到 $V$，有

$$
0<\max_\Delta h=\max_Kh-\min_Kh=h(p)-h(q).
$$

故 $p,q$ 分别为全域最大、最小点，且

$$
f=\frac{h-(\min_Kh)u}{\max_Kh-\min_Kh}\in\mathcal E,
\qquad f(p)=1,\quad f(q)=0.
\tag{162.5}
$$

总有 $B-B\subset\Delta\cap E_B$。若 $m_B$ 为球心，则 $B-B=2(B-m_B)$，其每条射线边界都是某个 $p-p_B^*$。AD 见证在这个差值读一，在整个 $\Delta$ 上至多读一，故截面沿该射线不能再延长；所有射线给出 DS。反之，DS 使每个这种差值不在 $\Delta$ 内部，否则它会在截面中仍是相对内点；于是 (162.4) 给 AD。

AD 见证在球上只能是 $b_p^B$，因为球上非恒定仿射函数的一、零极值必在一条直径两端。任一球 proper 效应为 $a+w\cdot z$，其中 $0\le a-|w|\le a+|w|\le1$；$w\ne0$ 时写成 $(a-|w|)1+2|w|b_p^B$，$s=w/|w|$。将同样的非负组合用于 $u$ 和 AD 见证，系数和 $a+|w|\le1$ 保证原 proper 延拓；常数用 $au$。反向只须延拓 $b_p^B$。证毕。

DS 控制每颗实际球的全部方向在同一环境差体中的宽度，不预设环境内积。它也不等于锥面恒等式 $C\cap\operatorname{span}H=H$；后者没有控制差体截面。任意面的效应延拓尚未用作输入。

### 162.3 精确复用 whole_pair_ball_confirmation

**供应162.4（160.10 的原域 NC）。** 在定义162.1上，不加 L2 或互易，已发表定理160.10 [P162] 给

$$
\mathrm{NC}(p)\ \Longleftrightarrow\ F(N_p)\ne K
\ \Longleftrightarrow\ \exists g_p\in C^*\setminus\{0\}:g_p|_{N_p}=0.
\tag{162.6}
$$

每个这样的非零正支撑都满足 $g_p(p)>0$。它还没有保证 $g_p(p)=\max_Kg_p$、$g_p/g_p(p)\le u$ 或 least。

**复用命题162.5（把 NC + AD 送入已有整球供应）。** 在 L2 + NC + AD 下，直接应用 [W162] 的 `whole_pair_ball_confirmation`，得到唯一的 least 原确认者 $e_p$、pure PR、完整有限混合律及混态零值粘合。其参数映射如下。

| 供应对象／前件 | 本章的精确替换 |
| --- | --- |
| 有限维实范数空间、`C : PointedCone`、`u` | 原 $V,C,u$；任选兼容范数，只给有限维拓扑；闭性、严格正性、$\operatorname{span}C=V$ 已在162.1中 |
| `base`、`pure`、`proper`、`confirms` | 整个 $K$、全部 $P$、整个 $[0,u]_{C^*}$、整个 $\mathcal F_p$，不是受限菜单 |
| `pairBase C u p q` | 全部锥面之交的归一底，由162.1的面对应恰为实际 $F(p,q)$ |
| `BallChart`、`wholePairBalls` | L2 的仿射球参数延拓至整个 $\mathbb R^3$；线性部分单射，`dim=3>0`，整闭球像等于整 pair base |
| `commonSupport` | 固定 $p$ 后只取供应162.4的一张 $g_p$，正于整个 $C$、严格正于 $p$；对每个不同纯 $q$、每个 admissible chart 及映到 $p$ 的每个单位向量，均消去其 chart antipode |
| `comparison`、`excludes` | 原 $T_p(x)$、存在一张原确认者消去 $x$；紧菜单使源码的 infimum 等于本章 minimum，$x$ 可在整个 $C$ 中 |

**接口证明。** L2 的三球同构在仿射包上的延拓给所需 chart。还要支付供应对**所有** charts 的量词：任意注入球 chart 的像都等于同一个三维实际面，因此其维数也只能为三；球间仿射同构保持唯一中心和对径，球面由面性给原纯点。故只要 chart 将单位向量映到 $p$，它的负向量必映到同一个 $p_B^*$。AD 使这个原纯点属于 $N_p$，同一 $g_p$ 遂在每一颗经过 $p$ 的球、每一个 chart antipode 上同时为零。球内任意两个不同球面点也生成同一原球：其原最小面是球的面，而三球没有真非点面。因此上述量词包括任意实际球内任意纯点处的限制。这正是 `commonSupport`，不含 proper 上界或 least 前件。单点底没有不同纯对，chart 量词为空，$g_p=u$ 即可。至此供应的所有前件都已支付。证毕。

已有供应现在直接给出，而非本章再证明：

$$
\begin{gathered}
e_p=g_p/g_p(p)\in\mathcal F_p,\qquad e_p\le f\ (f\in\mathcal F_p),\qquad
T_p(x)=e_p(x)\quad(x\in C),\\
e_p(q)=e_q(p),\qquad e_p|_B=b_p^B\quad(p\in P\cap B),\\
T_p\!\left(\sum_i a_iq_i\right)=\sum_i a_iT_{q_i}(p)
\quad(q_i\in P,\ a_i\ge0,\ \sum_i a_i=1).
\end{gathered}
\tag{162.7}
$$

供应的 `supportEffect` 就是以上同一归一化泛函；球限制公式来自其 `affine_zero_antipode`／`support_effects`。任取另一合法支撑也可送入同一供应，least 的唯一性使归一化结果相同。`whole_pair_ball_confirmation` 还给所有混态 $x_i\in K$ 的

$$
T_p\!\left(\sum_i a_ix_i\right)=0
\ \Longleftrightarrow\ T_p(x_i)=0\quad\text{对所有 }a_i>0,
\qquad a_i\ge0,\quad\sum_i a_i=1.
\tag{162.8}
$$

重复标签、零权、混合的内部和全锥上的零向量均保留；线性性同时给任意非负质量的版本。不是把逐输入 minimum 达到偷换成共同达到者：共同达到者由既有整球定理供应，且 least 在整个原锥上比较。本段是该已有结果的应用，不是新增 least、PR 或 full-mixture 定理，也不报告新的编译或 kernel 结果。

### 162.4 复用 postleast 剥离、自对偶和全部面结构

**供应命题162.6（已有有限后果）。** [L162] “Carrier and the retained condition” 的 $A,C,u,P,e_p$ 分别取本章 $V,C,u,P,e_p$。其 Principle S 的 proper least 条件 (1) 与互易条件 (2)，恰为 (162.7)；不需另给 signed spectrality、内积、群或 filter purity。该笔记 “Positive dual generation and one common complete frame” 及 “Reciprocal comparison gives signed spectrality” 遂直接供应

$$
\begin{gathered}
J:V\overset\sim\longrightarrow V^*,\quad Jp=e_p,\quad J(C)=C^*,\quad
\langle v,w\rangle=(Jv)(w)\text{ 对称正定},\\
e=J^{-1}u=\sum_i p_i,\qquad
\langle p_i,p_j\rangle=\delta_{ij},\qquad \sum_i e_{p_i}=u.
\end{gathered}
\tag{162.9}
$$

每个有限正交纯族都可补成上述完整框架；每个正泛函有有限非负正交展开，每个 $v\in V$ 有某个完整框架中的实系数展开。这里 source 的 $L,B,U$ 分别是 $J,\langle\cdot,\cdot\rangle,e$。剥离的终止界为 $\dim V$，原 order unit 保证 $C^*$ 张成 $V^*$。这些是供应已有的正泛函最大点剥离、零值互易和 signed 平移机制，不再作为162的新证明展开。

**供应命题162.7（已有面单位及正投影）。** 对任意原锥面 $H$，置

$$
H^\diamond=C\cap(\operatorname{span}H)^\perp,\qquad
Q_H=\operatorname{proj}_{\operatorname{span}H}.
$$

[L162] “Face geometry and the projective interface”（421–487行）的 $F,P_F,s_F,F^\perp$ 精确取 $H,Q_H,s_H,H^\diamond$；该笔记的 $U$ 仍为本章向量 $e$，不是原泛函 $u$。其 (10)–(11) 和补面段供应

$$
\begin{gathered}
s_H=Q_He\in\operatorname{ri}H\ (H\ne0),\quad 0\le_Cs_H\le_Ce,\quad
H=C\cap(e-s_H)^\perp,\\
H^\diamond=\operatorname{face}_C(e-s_H),\quad
s_{H^\diamond}=e-s_H,\quad H^{\diamond\diamond}=H,\\
H\text{ 在其张成中自对偶},\quad Q_H\text{ 正且幂等},\quad
u(Q_Hx)=\langle s_H,x\rangle\le u(x)\quad(x\in C).
\end{gathered}
\tag{162.10}
$$

约定 $s_0=0,s_C=e$，两端面均包括。该供应还给所有实际面闭且暴露、面内 signed 谱及补面正投影、原／对偶两侧的正核和正像互补；不从这里的“projectivity”字样直接跳到另一文献的定义。纯单点暴露也可直接复用同笔记 (8)，其 $\{e_p=1\}=\{p\}$ 使用完整 proper least 及互易。

由这些供应可读出任意面的全部 proper 效应延拓：若 $F=H\cap K\ne\varnothing$，面内效应由 $y\in\operatorname{span}H$ 表示，面自对偶使 $y,s_H-y\in H$。于是 $Jy\in[0,u]$，因为 $e-y=(e-s_H)+(s_H-y)\in C$。这是 postleast 面结构的后果，不是前面支付 AD 的前件。以下只补所需主分类文献的精确定义匹配。

### 162.5 Alfsen–Shultz 双侧 P-projection 的完整核对

**命题162.8（原单位下的精确接口）。** 令 $R_H=Q_H^*:V^*\to V^*$，$R'=R_{H^\diamond}$，$Q'=Q_{H^\diamond}$。它们给 [AS162, p.158] 所要求的 quasicomplementary P-projections；相应 projective face 恰是原 $H\cap K$。

**证明。** 对正幂等 $Q$ 定义 $\ker^+Q=C\cap\ker Q$，$\operatorname{im}^+Q=C\cap\operatorname{im}Q=Q(C)$。由162.7的正性、范围和补面，$Q_H(C)=H$，且对 $x\in C$，$Q_Hx=0$ 当且仅当 $x\perp\operatorname{span}H$。所以原空间的两条条件是

$$
\ker^+Q_H=\operatorname{im}^+Q'=H^\diamond,
\qquad
\operatorname{im}^+Q_H=\ker^+Q'=H.
\tag{162.11}
$$

$Q_H$ 的内积自伴性给 $R_HJ=JQ_H$，补面同理。由 $J(C)=C^*$，两 $R$ 正且幂等，对偶锥上的另外两条条件是

$$
\ker^+R_H=\operatorname{im}^+R'=J(H^\diamond),
\qquad
\operatorname{im}^+R_H=\ker^+R'=J(H).
\tag{162.12}
$$

这里后式的正核／正像均相对**原** $C^*$。有限维自然双对偶识别下 $R_H^*=Q_H$、$R'^*=Q'$，故 (162.11) 正是原文所要求的双对偶侧条件；(162.11)–(162.12) 总计四条正核／正像等式，不能换成整个线性核与线性像相等。

还须支付收缩和单位。源 (162.10) 给

$$
R_Hu=Js_H,\quad R'u=J(e-s_H),\quad
R_Hu+R'u=u,\quad 0\le R_Hu,R'u\le u.
\tag{162.13}
$$

因此 $-u\le f\le u$ 蕴含 $-u\le R_Hf\le u$，同理适用于 $R'$；二者对原 $u$ 的 order-unit norm 均收缩。原 $V$ 的 base norm 是

$$
\|v\|_K=\inf_{v=a-b,\ a,b\in C}\bigl(u(a)+u(b)\bigr).
$$

由 $u(Q_Ha)\le u(a)$ 及补面版本，两 $Q$ 在此范数下也收缩。非零幂等的范数为一，零幂等为零。有限维使空间完备、所有算子弱星连续。

现在严格取文献的 order-unit 空间 $A=V^*=A^b(K)=A(K)$，其单位 $e_A=u$，base-norm 预对偶为原 $V$。原文 p.158 的 (2.4) 是每一侧的正核／正像互补；P-projection 还要求弱星连续、正、幂等、范数至多一的 $R$ 及同类 $R'$，并要求它们的对偶也 quasicomplementary。以上已逐项支付。其 projective face 为

$$
K\cap\operatorname{im}R_H^*
=K\cap\operatorname{span}H=K\cap H
=\{x\in K:(R_Hu)(x)=1\}.
\tag{162.14}
$$

最后一步使用 $H=C\cap(e-s_H)^\perp$。每个原面因此都是该主文献意义下的 projective face。证毕。

一般 $Q'\ne I-Q_H$，中间仍可有非对角方向；这里的互补只指四条正核／正像条件。未假设 $2Q_H+2Q'-I$ 为正，也未从“暴露”或“正正交投影”直接宣布满足全部 P-projection 定义。旧供应承担投影构造，本段只证明其到主文献接口的准确匹配。

### 162.6 成熟 Jordan 判据与同原归一化双向重建

**接口162.9（主文献的精确前件）。** [AS162, p.160] 的 Hilbert ball property 要求每对极点的最小实际面 norm-exposed 且为 Hilbert 闭球，允许重合极点和零维球。非单点 $K$ 中，不同点由 L2 和162.7支付，重合点由纯单点暴露支付；有限维支持超平面均 norm-closed。单点 $K$ 直接按一维锥处理。

[AS162, Corollary 7.5, p.188] 对有限维紧凸集的准确充分必要条件是 Theorem 7.2 的 (i) Hilbert ball property 和 (iii) 每个 norm-exposed face projective。其证明明确说 (ii) 在有限维自动，(iv) 由 (iii) 及其 [2, Theorem 7.11] 得到；并没有另外要求本章输入 strong spectrality。命题162.8支付 (iii)。于是得到 $A(K)$ 上的有限维 JB-algebra，亦可使用成熟有限维 Euclidean Jordan 分类；这里复用判据和分类，均非新分类。

记 $H_n=\operatorname{Herm}_n(\mathbb C)$、$H_n^+=\operatorname{PSD}_n$。对复子空间 $S\le\mathbb C^n$ 记

$$
\mathcal D(S)=\{X\succeq0:\operatorname{Tr}X=1,\ \operatorname{ran}X\subset S\},
\quad\mathcal D(0)=\varnothing,\quad\mathcal D_n=\mathcal D(\mathbb C^n).
$$

**定理162.10（单系统完整等价）。** 在定义162.1的同一完整原域上，

$$
\boxed{\quad
\mathrm{L2+NC+AD}\quad\Longleftrightarrow\quad
\mathrm{L2+NC+DS}\quad\Longleftrightarrow\quad
\exists n\ge1,\ \Phi:H_n\overset\sim\longrightarrow V:
\ \Phi(H_n^+)=C,\quad u\Phi=\operatorname{Tr}.
\quad}
\tag{162.15}
$$

$n$ 为有限整数，$\dim_{\mathbb R}V=n^2$。全部原对象都由同一个 $\Phi$ 识别。

**证明。** AD 与 DS 由162.3等价。162.5复用整球供应，162.6–162.7复用 postleast 供应，162.8–162.9支付主文献入口，得到有限维 Jordan 状态空间。

成熟简单因子分解中，若有两个非零直和因子，分别取纯点，其实际生成面是线段，违反 L2。故只有一个简单因子。秩一是 $\mathbb R$，给 $n=1$。秩二简单因子是 spin factor，任意不同纯对生成整个实球，L2 使它恰为三球，即 $H_2$。秩至少三时，成熟分类的实际秩二面是下列球：

| 简单因子 | 实际二纯点面球维数 |
| --- | ---: |
| $\operatorname{Herm}_n(\mathbb R)$ | 2 |
| $\operatorname{Herm}_n(\mathbb C)$ | 3 |
| $\operatorname{Herm}_n(\mathbb H)$ | 5 |
| Albert $\operatorname{Herm}_3(\mathbb O)$ | 9 |

其二阶角实维数为 $2+\dim_{\mathbb R}\mathbb F$，归一底维数为 $1+\dim_{\mathbb R}\mathbb F$；故 L2 只留复因子。秩二球及二阶角的文献接口见 [AS162, Lemmas 3.9–3.10、Proposition 7.6 的证明] 和其引用的成熟分类。这里使用实际 pair-face 的维数，没有预设全局纯流形、齐次性或纯传递性。

所得 $K\cong\mathcal D_n$ 的仿射同构唯一齐次延拓为所需 $\Phi$：归一底间的任意实线性关系经单位读数知系数和为零，仿射性便保持该关系；两底张成各自空间，正逆双向线性延拓。故原锥、原单位确实成为 PSD、迹，不只是射影像或矩阵商。

反向，在完整矩阵底中，实际面恰为支持面 $\mathcal D(S)$。其面性由正分解中各项都消去 $S^\perp$ 得到；若 $\rho$ 在 $S$ 上正定，则每个 $\sigma\in\mathcal D(S)$ 都能以足够小正系数出现在 $\rho$ 的凸分解中，故任何含 $\rho$ 的面都含整个 $\mathcal D(S)$。取任意面的相对内点即得穷尽。谱分解给极点恰为秩一投影。不同纯对的复支持维数为二，写 $X=(I+a\cdot\sigma)/2$，正性恰为 $|a|\le1$，故 L2；对径秩一投影正交，其自身效应给 AD。确认 $P_v=vv^*$ 的原效应矩阵 $A$ 满足 $Av=v$；若还消去 $P_w$，正性给 $Aw=0$，故 $w\perp v$。反向用 $A=P_v$。因此 $F(N_{p_v})=\Phi\mathcal D(v^\perp)$，不含 $p_v$，给 NC。

$n=1$ 时 $K$ 单点、$N_p=\varnothing$，L2、AD、DS 空真；$n=2$ 时 $K$ 整三球、邻点面是对径单点。两个端点都在同一定理中。证毕。

**推论162.11（完整菜单与全部质量）。** 对同一个 $\Phi$，若 $P_v=vv^*$、$\|v\|=1$、$Q_v=I-P_v$，则

$$
\begin{gathered}
P=\{p_v=\Phi(P_v)\}\cong\mathbb{CP}^{n-1},\qquad
f_A(\Phi X)=\operatorname{Tr}(AX),\qquad
\mathcal E\longleftrightarrow\{A:0\preceq A\preceq I\},\\
\mathcal F_{p_v}\longleftrightarrow
\{P_v+B:B=Q_vBQ_v,\ 0\preceq B\preceq Q_v\},\\
e_{p_v}=f_{P_v},\qquad
T_{p_v}(\Phi X)=\operatorname{Tr}(P_vX)\quad(X\succeq0),\\
D_{p_v}=F(N_{p_v})=\Phi\mathcal D(v^\perp),\qquad
\langle\Phi X,\Phi Y\rangle=\operatorname{Tr}(XY),\qquad e=\Phi(I).
\end{gathered}
\tag{162.16}
$$

**证明。** 拉回整个对偶空间，正性及补正性分别给 $A\succeq0$、$I-A\succeq0$。$v^*Av=1$ 时 $(I-A)^{1/2}v=0$，故 $Av=v$，Hermitian 性消去交叉项，得到整个确认菜单。$P_v$ 本身合法且为每个确认者的正序下界，遂同时给全部 $X\succeq0$ 的 minimum，包括零及任意非负质量。支持面规则给排除面；纯对配对值再双线性延拓给迹内积。证毕。

全部面是支持面，面投影为 $\Phi X\mapsto\Phi(\Pi_SX\Pi_S)$，全部面效应可用 $A_S\oplus0$ 延拓。任意纯子集 $A$ 满足 $P\cap F(A)=A^{\perp\perp}$，因为其复线性支持已有有限子集张成，含空集与全体。完整框架长 $n$。实空间 $V$ 上的 Hermitian 观测量为 $x=\Phi(A)$（$A\in H_n$），其在原态 $\Phi X$ 上的期望为 $\operatorname{Tr}(AX)$；PVM、POVM 分别由 $I=\sum_jP_j$ 的正交投影分解、$I=\sum_jA_j$ 的正矩阵分解经 $f_{P_j}$、$f_{A_j}$ 给出，通常矩阵不确定性关系按此原态与观测量字典运输。

为承载普通非交换结合乘法，定义辅助复化 $V_{\mathbb C}=V\otimes_{\mathbb R}\mathbb C$，并将 $V$ 识别为 $V\otimes1$。利用标准 Hermitian 复化 $M_n(\mathbb C)=H_n\oplus iH_n$，将既有 $\Phi:H_n\to V$ 复线性延拓为

$$
\Phi_{\mathbb C}:M_n(\mathbb C)\overset\sim\longrightarrow V_{\mathbb C},\qquad
\Phi_{\mathbb C}(A+iB)=\Phi(A)\otimes1+\Phi(B)\otimes i
\quad(A,B\in H_n).
$$

对 $z,w\in V_{\mathbb C}$，结合乘法与伴随分别定义为 $z\star w=\Phi_{\mathbb C}(\Phi_{\mathbb C}^{-1}(z)\Phi_{\mathbb C}^{-1}(w))$、$z^\dagger=\Phi_{\mathbb C}((\Phi_{\mathbb C}^{-1}(z))^*)$。实空间 $V$ 上的 Jordan 积与 Hermitian Lie 积则为

$$
x\circ y=\Phi\!\left(\frac{AB+BA}{2}\right),\qquad
[x,y]_{\mathrm H}=\Phi\!\left(\frac{AB-BA}{2i}\right)
\quad(x,y\in V,\ A=\Phi^{-1}x,\ B=\Phi^{-1}y),
$$

两者均取值于 $V$。辅助复化不替换原 $K,C,\mathcal E,u$。酉数学对称及正定合同的内部齐次性是表示后的后果，未作输入；数学投影或 POVM 本身不指定实际更新。

### 162.7 coatom、低面高度与 pure PR 的准确缺口

**定理162.12（coatom 球自动满宽）。** 只假设 L2 + NC。若实际二元球 $B$ 是极大真面（coatom），则它的每条直径都满足 AD，不需要 pure PR。

**证明。** 先对任意非空 coatom $H$ 取其相对内点的支持超平面，得到包含 $H$ 的真暴露面；极大性使之等于 $H$。正泛函 $h$ 可归一为 $Z_K(h)=H$、$\max_Kh=1$。取纯最大点 $r$，则 $h\in\mathcal F_r$，故 $P\cap H\subset N_r$。$H$ 现在闭且紧，由纯凸生成、供应162.4与 coatom 性，

$$
H\subset F(N_r)\subsetneq K\quad\Longrightarrow\quad
F(N_r)=H,\qquad N_r=P\cap H.
\tag{162.17}
$$

$r\notin H$，称这样的 $r$ 为 $H$ 的一个支撑极标，不要求唯一。

对 coatom 球 $B$ 取极标 $r$，固定纯 $p\in B$。$F(p,r)$ 必真，否则 L2 使 $K$ 是三球，却含真非单点面 $B$，与三球的严格凸面结构矛盾。有限维严格面包含使维数严格增加，故可取包含 $F(p,r)$ 的 coatom $G$，再取其极标 $s$。由 (162.17)，$p,r\in N_s$，零关系对称给

$$
s\in N_p\cap N_r=N_p\cap(P\cap B).
$$

一张原效应在 $p,s$ 分别读一、零；限制到整球 $B$ 后两个极值只能在对径两端，故 $s=p_B^*$。每个 $p$ 都如此，得到 AD。证毕。

**推论162.13（低面高度）。** 面高度定义为从 $\varnothing$ 到 $K$ 的严格实际面链的最大包含次数，单点高度一，三球高度二。高度至多三时，L2 + NC 等价于162.10的 $n\le3$ 模型；若存在真二元球，则 $n=3$。

**证明。** 每颗真二元球必为 coatom，否则 $\varnothing\subset\{p\}\subset B\subset H\subset K$ 已有四次严格包含。162.12给 AD；若二元球等于 $K$，完整原菜单直接含其 $b_p^K$，也给 AD。应用162.10；矩阵支持面严格链的高度恰为支持秩 $n$。端点及反向均由支持面规则成立。证毕。

也可直接用“每颗真二元球都是 coatom”代替高度前件；这是受限入口，不是任意秩结论。

**命题162.14（pure PR 仅统一每球系数）。** 仅有 L2 和 pure PR $T_p(q)=T_q(p)$ 时，每颗实际球 $B$ 有一个 $c_B\in[0,1]$，使

$$
T_p(x)=1-c_B(1-b_p^B(x))
\quad(p\in P\cap B,\ x\in B).
\tag{162.18}
$$

该球有一对原零纯点，当且仅当该球全部 AD；失败时存在 $0<r_B<1$ 使

$$
B-B\subset r_B(K-K).
\tag{162.19}
$$

**证明。** 每个 $f\in\mathcal F_p$ 在 $p$ 达球上最大值一，故其限制为 $1-c_f(1-b_p^B)$，其中 $c_f=1-f(p_B^*)\in[0,1]$。菜单紧性使 $c_p=\max_fc_f$ 达到；此同一最大斜率同时最小化球内全部输入。对不同纯 $p,q\in B$，$1-b_p^B(q)=1-b_q^B(p)>0$，pure PR 因而使 $c_p=c_q=c_B$。一个零值迫使 $c_B=1$ 且两点对径；反向立即成立。若 $c_B<1$，所有直径差均由 (162.4) 得环境范数严格小于一；直径方向球面紧，范数连续，故其最大值小于一，任选介于它和一之间的正 $r_B$ 即给 (162.19)。反向此包含排除所有球内零对。证毕。

因此 L2 + NC + pure PR 再加“**每颗**实际二元球至少有一个原零对”才可接162.10，一颗种子球不够。coatom 和整球已经排除 (162.19)，一般非极大真球仍留下缺口。若另有有限 coatom 表示 $B=\bigcap_iH_i$，各取极标 $t_i$，则一个失败球必满足 $F(p,t_1,\ldots,t_k)=K$ 对所有纯 $p\in B$：否则取包含此真 join 的 coatom 极标 $s$，对称性给 $s\in N_p\cap\bigcap_iN_{t_i}=N_p\cap(P\cap B)$，产生球内零对。有限交表示是明写的附加前件，不声称每个面都有它。

本章不证明 $\mathrm{L2+NC}\Rightarrow\mathrm{AD}$，也不证明 $\mathrm{L2+NC+pure\ PR}\Rightarrow\mathrm{AD}$ 或 TC；亦未构造满足完整前件并实现 (162.19) 的反模型。数值互易把每球系数统一，并未将它自动定为一。

### 162.8 只在整个三复制域检查 R3 的全有限等价

**定义162.15（161的原全有限背景与 R3）。** 完整保留 [F161, (161.1)–(161.3)]：给定非零有限实 $V$ 和 $u$，对**每个**有限 $N\ge1$ 有

$$
W_N=V^{\otimes_{\mathbb R}N},\quad C_N\subset W_N,\quad u_N=u^{\otimes N},\quad
K_N=C_N\cap\{u_N=1\},\quad\mathcal E_N=[0,u_N]_{C_N^*}.
\tag{162.20}
$$

各 $C_N$ 闭、尖、生成，$u_N$ 严格正于非零正元。对每个拆分 $a+b=N$，$a,b\ge1$，有原单位、原向量／泛函乘积和配对，且

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b.
\tag{162.21}
$$

最大锥用全部 $C_a^*,C_b^*$ 测试。产品泛函分离原联合空间；每个原位置置换及逆在**整个**原锥上为正；两个括号之间是实际 canonical identity。此背景保留全部相关输入、旁观者、完整菜单和局部层析，不预给任何 Jordan 结构、比较律、操作菜单或复方向。

在每层定义 $P_N=\operatorname{ext}K_N$，并用其自己的整 $\mathcal E_N$、整个 $K_N$ 的实际面定义 L2、NC、AD、DS。写 $\mathsf R_N=\mathrm{L2}_N+\mathrm{NC}_N+\mathrm{AD}_N$。**新入口只要求 $\mathsf R_3$，量化整个原 $C_3$ 的全部纯点及实际二元球。** 其 DS 版本同样只在 $\Delta_3=K_3-K_3$ 中取截面，不是检查单体或乘积点子集。

**定理162.16（三复制候选 iff 一个共同坐标下的全有限复层级）。** 在这个精确原背景中，下列等价：

$$
\begin{gathered}
\mathsf R_3;\qquad
\mathrm{L2}_3+\mathrm{NC}_3+\mathrm{DS}_3;\\
\exists n\ge1,\ \theta:V\overset\sim\longrightarrow H_n:\quad
u=\operatorname{Tr}\circ\theta,\qquad
\theta^{\otimes N}(C_N)=H_{n^N}^+\quad\text{对每个有限 }N\ge1;\\
\mathsf R_N\quad\text{对每个有限 }N\ge1.
\end{gathered}
\tag{162.22}
$$

同一 $\theta$ 保持所有原单位、产品、效应、配对、位置置换及重括号；$\dim_{\mathbb R}V=n^2$。只检查三层的几何不删除全有限背景。

**证明。** 162.10先只应用于 $(W_3,C_3,u_3)$，得到 $\alpha_3:W_3\to H_D$、$\alpha_3(C_3)=H_D^+$、$\operatorname{Tr}\alpha_3=u_3$。其后的准确复用如下。

1. **实际面、型别、单位和菜单。** [F161, Lemma 161.1] 的 pure-spectator face 在原 min/max、单位及层析背景下已成立，不用 TC 或 S：对 $p\in P_b$，原边缘为 $p$ 的整个面恰为 $\{x\otimes p:x\in K_a\}$，嵌入 $x\mapsto x\otimes p$ 保持单位且逆为原边缘。纯乘积仍纯，故可用 $p\in P_1$ 和 $p\otimes p\in P_2$，在 $K_3$ 中取得 $K_2,K_1$ 的实际面。[Lemma 161.2] 随后只用已取得的 $\alpha_3$，把这两个面识别为完整复支持面，给 $\alpha_1:W_1\to H_n$、$\alpha_2:W_2\to H_{n^2}$、$D=n^3$。其整数计维是 $d=r_1^2,d^2=r_2^2,d^3=D^2$，$d=\dim V$。原单位成为迹，各自整个菜单成为 $[0,I]$；大菜单限制到 spectator face 的满射性由支持角效应 $A\mapsto J_aAJ_a^*$ 延拓证明，不预设一般面效应延拓。
2. **已分类后的共同方向。** 复用 [Proposition 161.3 的证明，从 (161.9) 之后开始]，不套用它以 $\mathsf G_3$ 开头的单锥供应。三种实际产品 $W_1\times W_1\to W_2$、$W_2\times W_1\to W_3$、$W_1\times W_2\to W_3$ 的矩阵大小分别是 $(n,n;n^2)$、$(n^2,n;n^3)$、$(n,n^2;n^3)$。原 min/max 给所有正态及正泛函的正双线性产品 $M,N$，原配对和单位给 $\operatorname{Tr}(M(x,y)N(f,g))=\operatorname{Tr}(xf)\operatorname{Tr}(yg)$、$N(I,I)=I$；层析给单射和分离。因此161所引用的矩阵产品正规形的前件已全部到位。方向定理的对象准确为 $A=W_1,D=W_2,E_L=E_R=W_3$：**两括号使用同一个实际二复制产品**，重括号是原 identity，$P_{12}$ 是整个 $C_3$ 上的实际 swap。复用其 post-type 证明，含单扇区的 repeated-index 关系 $\kappa_{11}=0$，得到同一 $\theta$ 使 $\theta^{\otimes q}(C_q)=H_{n^q}^+$，$q=1,2,3$。相关二复制输入及整个对偶空间由原张成论证保留。未调用该供应前面的 S-to-Jordan 或型别选择入口。
3. **全有限传播。** 此时精确满足 [Proposition 161.4] 的前件：固定同一 $\theta$ 下的标准 $C_1,C_2,C_3$、所有有限 min/max 边界和原正置换。直接复用其 VII102 Lemmas 102.6–102.10 及 Theorem 102.11 在 (102.30) 后的两锥包含尾部。该尾部的 Bell cup/cap 用 $C_2$，三腿资源用 $C_3$，资源产品用原 $C_6$，Choi 切片及 sandwich 保留任意原相关输入与每个有限旁观者，有限精确普适性也保持其来源前件。因此在同一 $\theta$ 下得到每个完整 $C_N$，不需 S3 或 B1–B3 作为额外入口，亦不重证传播尾部。

$n=1$ 时低层及每个 $W_N$ 一维，min/max 正射线相同，直接给所有层；$n=2$ 时 $C_3$ 是 $H_8^+$，几何量词仍在整个三复制域，资源允许同一局部块内的两个基向量。原简单张量张成，故同一 $\theta$ 自动保持所有产品、置换、括号及全部双对偶配对。反向从共同矩阵表示在每层用162.10的矩阵反向，给各自完整菜单的 $\mathsf R_N$，含 $N=3$；AD/DS 等价由162.3。证毕。

这一步压缩的是**几何检查的层级**：用三复制取代每层几何。它不把全有限原对象缩成三份，也不声称少于三份不够的普遍最小性。161.11的完整可分层级保留本背景及局部量子锥，却有整个 $K_3$ 的线段二元面，故确实不能把本定理的 R3 换成 R1；本章不宣称已有 R2 的全层级反例。

### 162.9 熟悉量子公理的全有限字典及其条件

令 $\Theta_N=\theta^{\otimes N}$。定理162.16取得的目标正是 [F161, (161.7)]，所以161.6–161.10中**从该目标之后开始**的字典全部可直接应用，无须重新给 $\mathsf G_3$、TC、S3 或酉实现。以下只列对应和额外条件，不重证161的表与各条运算规则。

| 熟悉的量子结构 | 本章如何取得，以及仍须保留的条件 |
| --- | --- |
| Hilbert 空间、叠加、纯态和混态 | 161.6：$\mathcal H_N=(\mathbb C^n)^{\otimes N}$；全部 $P_N\simeq\mathbb{CP}^{n^N-1}$，全部 $K_N\simeq\mathcal D_{n^N}$，含所有纠缠态；叠加射线及整体相位字典随坐标而来 |
| 全效应、Born、观测量和测量 | 161.6及162.11：整个原菜单成为 $0\le E\le I$，$f_E(x)=\operatorname{Tr}(E\Theta_Nx)$；完整确认菜单及同一 least 给所有 $x\in C_N$ 的 minimum。全部 Hermitian 谱给 PVM，有限单位正分解给数学 POVM |
| 复张量、交换、括号及约化 | 162.16保持原产品和单位；161.10的约化论证把原边缘 $\operatorname{id}\otimes u$ 识别为偏迹，对全部相关输入成立 |
| CP、分支和通道 | 161.7：原 $F:W_m\to W_k$ 对每个原旁观者的整个 $C_{r+m}$ 正 iff 其矩阵扩张 CP iff Choi PSD iff 有矩形 Kraus 表示；全输入质量预算给 $\sum K_\alpha^*K_\alpha\le I$ 或 $=I$ |
| 仪器、条件态及所有有限历史 | 按161.8把所有旁观正且质量不增的映射定义为数学分支，同族和保质量即仪器；161.9给有限 CP 分支族、完整相关条件态、序列／自适应／粗粒化及张量规则，保留零标签和零质量 |
| 理想锐中性更新 | 161.7.1直接复用 Atlas Proposition 13.4(1)：同型原正映射 $K$ 有投影效应 $e$ 且逐点固定每个 $e(p)=1$ 的原纯态，才推出 $\Theta_kK\Theta_k^{-1}(X)=PXP$；CP及全部旁观扩张随之得到 |
| 连续可逆动力学 | 161.10：另给连续、保原锥及原单位的 $\mathbb R$-群 $A_t$，从这个原群推出 $\Theta_kA_t\Theta_k^{-1}(X)=e^{-itH}Xe^{itH}$，$H=H^*$ 唯一到标量；不预给酉族 |

具体地，旁观正性的全量词仍是

$$
(\operatorname{id}_{W_r}\otimes F)(C_{r+m})\subseteq C_{r+k}
\quad\text{对每个有限 }r\ge0,
\tag{162.23}
$$

$W_0=\mathbb R,C_0=\mathbb R_+$ 只作 scalar convention。所有位置由原置换运输。161.7的 Choi 检查是保留完整参考腿的整个输出 PSD，TP/TNI 用完整参考边缘的预算，不用一个总迹代替。矩阵 Kraus 结论还给任意辅助矩阵大小的通常 CP。$n=1$ 包括标量输入／输出及全部标量分支，$n=2$ 也在所有定理内。

对任意质量 $Z=\Theta_{r+m}z\succeq0$，分支输出与质量为

$$
Z_a=(\operatorname{id}_{n^r}\otimes\Phi_a)(Z)\succeq0,\qquad
M_a=\operatorname{Tr}Z_a=\operatorname{Tr}((I\otimes E_a)Z),\qquad
\sum_aM_a=\operatorname{Tr}Z.
\tag{162.24}
$$

只有 $M_a>0$ 才取 $Z_a/M_a$；$M_a=0$ 时输出为零，不指定归一条件态。条件旁观边缘及无信号和正是161.9的 (161.28)。这保留全部原混态和未归一分支，不只检查乘积输入。

锐效应本身不决定更新，结果可重复也不等于在退化 yes 子空间逐点中性；161.7.1明确保留这种区别。连续群的 Hamiltonian 结论来自161.10对 order automorphism 的分类、连通性和从原群构造的局部酉提升，生成元为 $-i[H,\cdot]$；因此可写 $i\dot\psi=H\psi$、$i\dot\rho=[H,\rho]$，而不把酉可实现性再当作前件。几何仍不选择原时间群：恒等群及不同 $H$ 共享同一层级。物理钟、能量标定和数值 $\hbar$ 另给后，才可令 $H_{\rm phys}=\hbar H$。

数学操作类的定义和表征不宣称实际设备供应；要将整个数学菜单认作实际事件，保留 VII102 Definition 102.14 的 event saturation 和相应记录、接线、预算及实现合同。无限系统、时空和实际装置不由这些有限静态／运算对应推出。

### 162.10 完整排除三球的单系统应用：complete EB3 + 实际 L2 iff 复 qutrit

**定义162.17（完整 EB3）。** 仍只在定义162.1的一个原系统中，要求每个**整个混态零集** $D_p$ 仿射同构于非退化闭三球。没有 pure PR、维数上界、标签单射或 least 前件。这正是 [E162] 的 complete EB3 部分；本节不加该文另外假设的 pure PR。

**引理162.18（已有排除球供应与实际 L2 的接口）。** complete EB3 自动给 NC 和所有非空真非点实际面的穷尽；若还给实际 L2，则每颗实际二元球都是 proper coatom。

**证明。** [EB162] `exclusion_ball_faces` 的**前两个结论**只要求原闭锥、严格单位、生成性及 `exclusionBalls`，没有 pure PR，也没有第三结论的 `pairProper`。取其全部原 base、pure、proper、confirms、exclusion 分别为本章 $K,P,\mathcal E,\mathcal F_p,D_p$，complete EB3 给 `ExclusionChart` 的 `dim=3` 和整像等号。于是已有供应直接给：每个 $D_p$ 是真、紧、暴露的实际三球，且 $D_p=Z_K(f_p)$、$f_p\in\mathcal F_p$；每个非空真实际面是纯单点或某个整个 $D_r$。它量化所有实际面，未先要求其闭。

由定义 $N_p=P\cap D_p$；紧面纯凸生成给 $D_p=\operatorname{conv}(P\cap D_p)$，所以

$$
F(N_p)=D_p\subsetneq K,\qquad p\notin D_p.
\tag{162.25}
$$

这正是实际 NC，不是 uniform budget noncollapse。若另给 L2，任意二元球 $B$ 不可能等于 $K$，否则三球 $K$ 会含真非点面 $D_p$，违反三球的严格凸面结构。故 $B$ 是真非点实际面，按穷尽 $B=D_r$。若 $B\subset H\subsetneq K$，则 $H$ 也是非点，故 $H=D_s$ 是三球；$B$ 是此球的非点面，必等于 $H$。因此 $B$ 为 coatom。证毕。

**定理162.19（完整单系统等价，无 pure PR 前件）。** 在定义162.1的全部原域上，

$$
\boxed{\quad
\text{complete EB3}+\text{实际 L2}
\quad\Longleftrightarrow\quad
\exists\Phi:H_3\overset\sim\longrightarrow V:
\ \Phi(H_3^+)=C,\quad u\Phi=\operatorname{Tr}.
\quad}
\tag{162.26}
$$

故 $\dim_{\mathbb R}V=9$；全部混态、效应、确认者和非负质量 Born 读数都是 (162.16) 的 $n=3$ 字典，pure PR 是结论。

**证明。** 162.18给实际 NC 及全部二元球 coatom，162.12遂给全部 AD，无需 pure PR。应用162.10得到某个 $H_n$ 的同原迹归一化表示。现在才用 EB3 决定秩：162.11给 $D_{p_v}=\Phi\mathcal D(v^\perp)$。$n=1$ 的此面为空，$n=2$ 为单点，都不满足非退化 EB3；$n\ge2$ 时其仿射维数为 $(n-1)^2-1$，等于三迫使 $n=3$。这是重建后的支持秩计算，不倒用作前面的面穷尽或 least 供应。

反向，完整复 qutrit 的全菜单由162.11给整个混态排除集恰为 $\mathcal D(v^\perp)$；$v^\perp$ 复维数二，其整个迹一支持底为三球，故 complete EB3。任意不同纯对的实际支持面同样是二阶密度底，给实际 L2。原单位、全部菜单和全部混输入均由同一 $\Phi$ 保持。证毕。

在 EB3 域内，[EB162] 的第三个结论另说明 `pairProper` 一旦给定就供应所有 pair balls；由于其 exclusion charts 在此维数均为三，它也供应 L2。反向 L2 的 properness 已由162.18证明。因此这里缺失的全称 pair-face 条件也可准确写成 `pairProper`，但 EB3 单独并未在本章支付它。

[E162] 的完整排除三球问题仍保留：complete EB3 + pure PR 是否推出实际 L2，或是否使其 dense $G_\delta$ 域 $Z$ 上的 extension budgets 有共同有限上界，均未由该文或本章证明。其定理160.6–160.7给 $\sup_{p\in P}\beta_{D_p}=\sup_{p\in Z}\beta_{D_p}$，以及有限上界 iff 同原 qutrit 的有条件桥；稠密性、逐点有限和局部有界不支付全域一致上界。现在若**另给实际 L2**，162.19闭合该分支，并在其取得的 pure PR 背景中由 qutrit 字典得所有 $\beta_{D_p}=1$。不能把这个条件结论删去 L2 后回填旧缺口，也没有证明无界分支可实现。

本节是单系统应用，**不是把 EB3 加在全有限层级的 $C_3$ 上**。若在 (162.20)–(162.21) 的全有限背景给 $C_3$ complete EB3 + L2，162.19会使其矩阵大小为三，而161.2又要求该大小等于整数 $n^3$，两者不相容。正确全层级候选是整个 $C_3$ 的 R3；其中排除支持秩为 $n^3-1$，一般不为三球。

### 162.11 依赖、比较、文献及中文图景

在同一完整原域中，162.10与已发表160.5给出

$$
\mathrm{L2+NC+AD}\ \Longleftrightarrow\ \mathrm{L2+NC+DS}
\ \Longleftrightarrow\ \text{同原归一复矩阵模型}
\ \Longleftrightarrow\ \mathrm{L2+NC+TC}.
\tag{162.27}
$$

本候选用直径满宽代替切方向接合入口；不证明去掉 NC 后 AD 与 TC 的严格强弱或独立性。NC 也不能由本章其余输入顺手删去：[P162] 的三对三平衡商保留全部原纯点、实际 L2、TC、pure Born minimum，故也有 AD，却失败 NC；原全效应受核正交约束，均匀满秩态提升 $I_6/6$ 对应的原混态 minimum 为 $1/3$；秩一测试 $P_{e_1}$ 在该提升上的读数为 $\operatorname{Tr}(P_{e_1}I_6/6)=1/6$，但 $P_{e_1}$ 不满足原核正交约束、不属于原效应菜单，故 $1/6$ 不是合法替代读数。这是已有反例的应用，不是新构造，亦不满足完整 EB3。实、四元数、Albert 模型则说明成熟投影结构本身不选复型，L2 的实际面维数才承担型别选择。

| 内容 | 本章的归属和精确用途 |
| --- | --- |
| NC／真邻点面／共同正支撑及严格正值 | 直接复用160.10；不提前称其 proper 确认者 |
| 全 chart antipodes 的 commonSupport 映射 | 162.5的原域接口；L2 给 `wholePairBalls`，NC + AD 给 `commonSupport` |
| least、pure PR、fullMixture、全混态零值与粘合 | 已有 `whole_pair_ball_confirmation` 及其 `support_effects`；不是新 delta |
| 正泛函剥离、signed 谱、自对偶、全部面单位和补面正投影 | 直接复用 Library postleast 供应；不是162.6–162.7的新结果 |
| AD／DS／球效应延拓、完整 AS 定义匹配、coatom／低高度、pure PR 缺口 | 162.3、162.8、162.12–162.14的纸面证明与接口工作 |
| R3 到全有限同一方向 | 本章单锥入口接161.1–161.4的已分类后供应；型别、产品方向、VII102传播各保留其原前件，不另称新分类或普适性定理 |
| 全有限量子字典、理想锐中性更新、指定连续群的酉律 | 复用161.6–161.10和其明确来源；时间群及中性条件仍明写 |
| complete EB3 + 实际 L2 iff qutrit | 162.18–162.19的条件应用；面穷尽来自既有 EB 供应，新增连接是实际 L2 迫 proper coatom 后接 AD，非 EB3 裸重建 |

**[W162]** 固定源码快照 `32215b6ea08095b9a0de6bc465e26d1ad6207cc4`：[WholePairBallConfirmation.lean](https://github.com/the-omega-institute/trureturing/blob/32215b6ea08095b9a0de6bc465e26d1ad6207cc4/D5/S3/Quantum/Foundation/WholePairBallConfirmation.lean)，定义 `pairBase`、`BallChart`、`wholePairBalls`、`commonSupport`（约32–59行），`support_effects` 及 `whole_pair_ball_confirmation`（约322行）；[Blueprint 说明](https://github.com/the-omega-institute/trureturing/blob/32215b6ea08095b9a0de6bc465e26d1ad6207cc4/Blueprint/D5/S3/Quantum/Foundation/WholePairBallConfirmation.md)，Theorem 1.13。`base/pure/proper/confirms/comparison/reciprocalLeast/fullMixture` 使用同 pin 的 [CircuitBalancedConfirmation.lean](https://github.com/the-omega-institute/trureturing/blob/32215b6ea08095b9a0de6bc465e26d1ad6207cc4/D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.lean)。这里是固定源码的精确复用，不声称本章新增形式化结果或重新执行验证。

**[L162]** 同一固定 pin 的 [Library/QuantumStates/mullerududec2012selfduality.md](https://github.com/the-omega-institute/trureturing/blob/32215b6ea08095b9a0de6bc465e26d1ad6207cc4/Library/QuantumStates/mullerududec2012selfduality.md)，187–219行的 carrier／Principle S，285–384行的正泛函剥离、共同框架及 signed 自对偶，386–419行的 (8)，421–487行的全部面几何、补面单位、原／对偶正核正像及单位收缩。本章仅消费 proper-effect 域；不将 least 扩大为对所有无上界正泛函的 least。其后的 filter purity 供应不为本章所需。

**[AS162]** E. M. Alfsen and F. W. Shultz, *State spaces of Jordan algebras*, Acta Mathematica **140** (1978), 155–190，DOI [10.1007/BF02392307](https://doi.org/10.1007/BF02392307)，[主文献 PDF](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6236-11511_2006_Article_BF02392307.pdf)。直接使用 p.158 的 (2.4)、双侧 P-projection、projective unit／face，p.160 的 Hilbert ball property（含重合极点），p.188 Corollary 7.5 及 Theorem 7.2 的 (i)、(iii)。秩二 spin factor 及二阶角的成熟接口为 Lemmas 3.9–3.10（pp.164–165）及 Proposition 7.6 的证明（p.189）。该文引用的 [4] 为 Alfsen–Shultz–Størmer, *A Gelfand–Neumark theorem for Jordan algebras*, Advances in Mathematics **28** (1978), 11–56，其 Propositions 7.1、8.3；spin-factor 段另引用 Topping (1966)。本章据这些成熟分类接口应用，不声称新证 Jordan 分类或重新核查全部转引文献。

**[P162]** 固定已发表快照 `0826c2f31d52656aa8b51ccc676896bc7693fad7`：[Binary Tangent XIII](https://github.com/the-omega-institute/trureturing/blob/0826c2f31d52656aa8b51ccc676896bc7693fad7/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md)，定义160.1–160.2、定理160.5、160.7、160.10；同 pin 的 [Exclusion XII](https://github.com/the-omega-institute/trureturing/blob/0826c2f31d52656aa8b51ccc676896bc7693fad7/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md)，§159.4 的 AD 和平衡商／完整字典供应。只使用各自原有前件。

**[F161]** 固定已发表纸面接口 `34f5761ee1ccff84afa44f5a906002b13409b7b7` 的 [第161章](https://github.com/the-omega-institute/trureturing/blob/34f5761ee1ccff84afa44f5a906002b13409b7b7/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md)：(161.1)–(161.3) 的完整原背景；Lemmas 161.1–161.2；Proposition 161.3 从 (161.9) 后的 post-type 证明；Proposition 161.4 的 VII102 tail；161.6–161.10 的字典、正锐中性和指定连续群。该 pin 按其明示前件提供条件纸面供应。161引用的产品／方向供应为其 [P]，VII102为其 [F102]，锐中性为其 [Atlas161] Proposition 13.4(1)，均按161逐项给出的参数消费，不加入早期 S3/B1–B3 前件。

**[EB162]** 固定 pin `32215b6ea08095b9a0de6bc465e26d1ad6207cc4` 的 [ExclusionBallFaces.lean](https://github.com/the-omega-institute/trureturing/blob/32215b6ea08095b9a0de6bc465e26d1ad6207cc4/D5/S3/Quantum/Foundation/ExclusionBallFaces.lean)，`exclusionBalls` 和约245行的 `exclusion_ball_faces`；[Blueprint Theorem 1.7](https://github.com/the-omega-institute/trureturing/blob/32215b6ea08095b9a0de6bc465e26d1ad6207cc4/Blueprint/D5/S3/Quantum/Foundation/ExclusionBallFaces.md)。前两个结论无 pure PR、无 `pairProper`，第三个结论才以前两个为基础另消费 `pairProper`。

**[E162]** 同一固定快照 的 [Exclusion XIII，第160章](https://github.com/the-omega-institute/trureturing/blob/32215b6ea08095b9a0de6bc465e26d1ad6207cc4/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XIII.md)，完整 EB3 + pure PR 原域、定理160.6–160.7的 extended-supremum／uniform-budget 桥及明确开放入口。此 Exclusion XIII160 与 [P162] Binary Tangent XIII160 是不同文件，引用不可混淆。

本章的完整候选在所列供应及前件下纸面闭合；一般 L2 + NC 的自动 AD、加 pure PR 后的同一缺口、裸 EB3 或 EB3 + pure PR 到 L2／uniform budget 的入口仍未闭合。这里不作全球新颖性、最小独立公理数、formal／kernel 认证或实际设备结论。三复制条件压缩全有限几何检查，不能据条件框的数量宣称物理独立公理更少。上述供应仅按其明示条件使用。

中文图景是：先把全部原准备和全部原尺留在同一块状态体上。两纯态张成整颗三球，还不保证每条直径在环境中有满刻度；AD 恰要求两端能被原尺读成一和零，DS 则说沿球的三个方向切开整个差体，切不出多余宽度。NC 已给一张同时消去全部零邻点的正支撑；AD 让它在所有经过源点的球上都消去对径。这个接口一旦支付，已有整球定理就把同一张支撑校准成全域 least，已有剥离与面几何再供应正定配对、框架及补面。把原锥和对偶锥的四条正核／正像、原单位收缩和弱星连续逐项接到主文献，才可用成熟 Jordan 判据；二元球三维最后选出复矩阵。

若球已是 coatom，从球外两次取支撑极标便能找回球内对径见证。complete EB3 原本就穷尽全部真非点面，另给实际 L2 便让所有二元球都是这种 coatom，于是不借 pure PR 得到 qutrit；没有这项 L2，旧文的一致预算问题仍在。全有限情形则只在整个三复制域支付 L2、NC、AD：实际纯旁观者面把较低层连同原单位及全菜单一起带下，共同二复制产品、重括号和整三复制交换校准方向，已有传播尾部再保持所有有限相关输入。由此得到全部有限态、效应、Born、数学 CP 和仪器；理想锐中性与指定连续可逆群各自带着明写条件，前者给 Lüders，后者从原群推出酉律和生成元。设备是否可用、钟与能量如何标定，仍由对应数据承担。

## 追加锚（本行以下为增补区）

## 163. 一个原三体种子与全部有限 qubit 锥

### 163.1 同一坐标中的完整原域

**定义 163.1（已对齐低二层的全有限背景）。** 固定 $n\ge2$，取
$V=\operatorname{Herm}_n(\mathbb C)$ 为实向量空间，
$W_N=V^{\otimes_{\mathbb R}N}$，$N\ge1$。在同一套实际张量坐标中，
$W_N\cong\operatorname{Herm}_{n^N}(\mathbb C)$ 先仅是向量空间识别。
每个原 $C_N\subset W_N$ 是闭、尖、生成凸锥，
$u_N=\operatorname{Tr}=u_1^{\otimes N}$ 在 $C_N\setminus\{0\}$ 上严格为正。始终使用

$$
K_N=\{x\in C_N:u_N(x)=1\},\qquad
P_N=\operatorname{ext}K_N,\qquad
\mathcal E_N=[0,u_N]_{C_N^*}.
\tag{163.1}
$$

这些分别是整个原基、全部原极点和整个原 proper 效应区间；有限效应菜单是其中
所有有限单位分解。对每一对有限 $a,b\ge1$，要求

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
 \subseteq C_a\otimes_{\max}C_b.
\tag{163.2}
$$

最小锥由正简单张量闭凸生成；最大锥以全部
$f\in C_a^*,g\in C_b^*$ 的 $f\otimes g$ 非负定义。
实际规范重括号使用同一个 $W_{a+b}$ 和同一个联合锥；全部位置置换及其逆均正。
非连续位置的任意分块先经这些置换运输。原配对满足
$(f\otimes g)(x\otimes y)=f(x)g(y)$，单位保持上述乘法。
约定 $W_0=\mathbb R,C_0=\mathbb R_+,u_0=\mathrm{id}$。
唯一预付的矩阵锥等式为

$$
C_1=\operatorname{Herm}_n^+(\mathbb C),\qquad
C_2=\operatorname{Herm}_{n^2}^+(\mathbb C),
\tag{163.3}
$$

二者必须在上述同一实际坐标中成立。本文不假定更高原锥 PSD、高阶普通自对偶、
任意全局矩阵操作的原正性或高阶原纯态分类。
这个背景是 [VII，定义102.1][Q163VII] 的单块、已对齐低二层特例。

称 $F:W_m\to W_k$ **原全旁观正**，若对每个有限 $r\ge0$，
$(\mathrm{id}_{W_r}\otimes F)C_{r+m}\subseteq C_{r+k}$，并允许原置换后的任意作用位置。
这是数学映射条件，不指定物理事件。
对非零向量 $\psi\in(\mathbb C^n)^{\otimes3}$，记 $r_i(\psi)$ 为第 $i$ 个
一腿对其余两腿的矩阵展平秩。本文的三体种子条件为

$$
|\psi\rangle\langle\psi|\in C_3,\qquad
r_1(\psi),r_2(\psi),r_3(\psi)\ge2.
\tag{163.4}
$$

对矩阵秩一向量态，这恰表示每个二分割均纠缠。
“秩一”仅指实际矩阵秩；在证明锥等式之前，不把它等同于原 $P_3$ 的极点。
这与 [VII，定义103.2][Q163VII] 对相干资源的原纯性边界相同。

### 163.2 原滤波、切片与有限预算

**引理 163.2（低二层支付的操作）。** 在定义163.1下，每个一体矩阵合同
$\Phi_A(x)=AxA^*$，$A:\mathbb C^n\to\mathbb C^n$，均原全旁观正。
若 $A^*A\preceq I_n$，则每个原旁观扩张不增迹。
这些映射的有限复合、张量积，以及一体酉共轭及其逆，具有相应原正性。
任意原正效应均可在全部原联合输入上切片；重复切片仍落在原剩余锥。

**证明。** 逐项复用 [VII，引理102.6—102.7、102.8及103.6的证明][Q163VII]。
为核清所消费的输入，令

$$
|I_n\rangle=\sum_{a=0}^{n-1}|aa\rangle,\qquad
\Omega=|I_n\rangle\langle I_n|,\qquad
\beta(z)=\operatorname{Tr}(\Omega z).
\tag{163.5}
$$

由(163.3)，$\Omega\in C_2$，$\Omega/n\in K_2$，$\beta/n\in\mathcal E_2$。
VII102.7 的原自身 Choi 判据只用这个低二层和(163.2)：以 $m$ 对原杯及原置换构成
$\Omega_m\in C_{2m}$，按“参考 $m$ 腿、输出 $k$ 腿”定义

$$
J(F)=(\mathrm{id}_{W_m}\otimes F)\Omega_m,
\qquad F\text{ 原全旁观正}\ \Longleftrightarrow\ J(F)\in C_{m+k}.
\tag{163.6}
$$

反向是把任意 $z\in C_{r+m}$ 与 $J(F)$ 原相乘，再逐对用 $\beta$ 切片的精确蛇式。
每一步由 VII102.6 对整个剩余原锥正，包含任意纠缠旁观者；不使用高层 PSD。
归一杯和 proper 帽每对带 $n^{-2}$，只改变一个严格正的有限系数。
对 $\Phi_A$，$J(\Phi_A)=|A\rangle\!\rangle\langle\!\langle A|\in C_2$，
其中 $|A\rangle\!\rangle=\sum_a|a\rangle\otimes A|a\rangle$。
于是取得全部原旁观者上的正性。
当 $A^*A\preceq I_n$，$u_1-u_1\Phi_A$ 在 $C_1$ 上正；
将它与任意旁观单位相乘并用最大界，得全部旁观预算。
张量积可逐腿提升并复合，位置变化由原置换支付。
一般切片则直接是 VII102.6 的闭锥双极结论。∎

特别地，若 $f\in\mathcal E_a$，$z\in C_{a+b}$，则

$$
0\le u_b((f\otimes\mathrm{id})z)\le u_{a+b}(z),
\tag{163.7}
$$

因为 $f\otimes u_b$ 与 $(u_a-f)\otimes u_b$ 都在原对偶锥中。
故逐次 proper 帽的总迹预算成立，即使中间原态有纠缠。
把正系数除掉用于锥成员关系，不把该除法解释成实际事件放大。

### 163.3 三个 W 的原三角收缩

**命题 163.3（四项三角形）。** 设 $n=2$，
$w=|100\rangle+|010\rangle+|001\rangle$，且 $ww^*\in C_3$。
则在同一个原层级中，

$$
\tau=|111\rangle+|001\rangle+|010\rangle+|100\rangle,
\qquad \tau\tau^*\in C_3,
\qquad \Delta=gg^*\in C_3,\quad g=|000\rangle+|111\rangle.
\tag{163.8}
$$

**证明。** 三个顶点 $A,B,C$ 各放一个原 $ww^*$，腿次序依次为
$(a,A_B,A_C)$、$(b,B_A,B_C)$、$(c,C_A,C_B)$。
最小界先把三份资源放进原 $C_9$。
分别在 $(A_B,B_A)$、$(A_C,C_A)$、$(B_C,C_B)$ 上施加 Bell 帽
$\langle00|+\langle11|$ 所对应的正泛函 $\beta$。
记三条内部边的公共位为 $x,y,z$，令 $w_{ijk}=1$ 当且仅当 $i+j+k=1$。
剩余向量的系数恰为

$$
t_{abc}=\sum_{x,y,z\in\{0,1\}}
 w_{axy}w_{bxz}w_{cyz}.
\tag{163.9}
$$

非零项必须满足 $a+x+y=b+x+z=c+y+z=1$。
两条激活内部边必在某顶点相遇，违反该顶点恰有一个 $1$ 的条件，故只有以下四项：

| 内部 $(x,y,z)$ | 外部 $(a,b,c)$ | 条件 |
| --- | --- | --- |
| $(0,0,0)$ | $(1,1,1)$ | 无内部边激活 |
| $(1,0,0)$ | $(0,0,1)$ | $AB$ 激活，对顶点 $C$ 的外腿为 $1$ |
| $(0,1,0)$ | $(0,1,0)$ | $AC$ 激活，对顶点 $B$ 的外腿为 $1$ |
| $(0,0,1)$ | $(1,0,0)$ | $BC$ 激活，对顶点 $A$ 的外腿为 $1$ |

每项系数均为一，所以 $t=\tau$。
在算子层，$\beta$ 对 dyad 的切片等于在 ket 上作用 Bell bra、在 bra 上作用其伴随；
因此这同一个九腿协议的最终输出就是 $\tau\tau^*$。
其原正性是先由 VII102.6 得 $C_9\to C_7$，再得 $C_7\to C_5$，最后得
$C_5\to C_3$；每一步均包含所有原旁观者。
同一三次切片对任意有限 $r\ge0$ 都把整个 $C_{r+9}$ 送入 $C_{r+3}$。
这里未判定 $C_9$ 或中间锥为 PSD。

预算可以全部使用原 proper 对象：输入 $(ww^*/3)^{\otimes3}$ 的迹为一，
三个帽各取 $\beta/2$，输出

$$
\frac{\tau\tau^*}{3^3\,2^3}=\frac{\tau\tau^*}{216},
\qquad u_3\left(\frac{\tau\tau^*}{216}\right)=\frac1{54}.
\tag{163.10}
$$

令 $H=2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$，$Z=\operatorname{diag}(1,-1)$。
直接展开得

$$
\tau=\sqrt2\,H^{\otimes3}(|000\rangle-|111\rangle),\qquad
[(Z\otimes I\otimes I)H^{\otimes3}]\tau=\sqrt2\,g.
\tag{163.11}
$$

引理163.2支付这些局部酉及原旁观扩张。
于是(163.10)成为 $\Delta/108$，迹仍为 $1/54$；锥缩放给 $\Delta\in C_3$，
条件归一态为 $\Delta/2$。所有操作由上述同一个资源协议联合实现为原数学正映射，
并逐项具有迹预算；没有由协议宣称物理装置存在或确定性成功。∎

### 163.4 完整 qubit 种子等价

**定理 163.4（一个矩阵秩一种子当且仅当全部有限量子锥）。**
在定义163.1的 $n=2$ 背景中，以下两条件等价：

1. 存在实际 $|\psi\rangle\langle\psi|\in C_3$，且 $r_1(\psi)=r_2(\psi)=r_3(\psi)=2$。
2. 对每个有限 $N\ge1$，在同一实际坐标中 $C_N=\operatorname{Herm}_{2^N}^+(\mathbb C)$。

**证明。** 对条件1的非零向量使用 Dür–Vidal–Cirac 的成熟分类
[DVC，§III.2及附录A][Q163DVC]：三个局部秩全为二的三 qubit 向量，恰属
GHZ 或 W 两个可逆局部算子类。该结论只应用于矩阵向量 $\psi$，无需原基极点假设。
故存在可逆 $B_i:\mathbb C^2\to\mathbb C^2$，适当吸收一个非零标量后，使
$(B_1\otimes B_2\otimes B_3)\psi=v$，其中 $v=g$ 或 $v=w$。
若原文给出代表元到 $\psi$ 的方向，就取各局部算子的逆。

取 $s_i=\max\{1,\|B_i\|\}$，$A_i=B_i/s_i$。
引理163.2把这些矩阵滤波映到全部原旁观者上的正、不增迹的一体映射。
从 $\rho_\psi=\psi\psi^*/\|\psi\|^2\in K_3$ 得

$$
(\Phi_{A_1}\otimes\Phi_{A_2}\otimes\Phi_{A_3})(\rho_\psi)
 =t\,\frac{vv^*}{\|v\|^2},\qquad
t=\frac{\|v\|^2}{\|\psi\|^2s_1^2s_2^2s_3^2}\in(0,1].
\tag{163.12}
$$

因此 $vv^*\in C_3$。GHZ 支路直接给 $\Delta$；W 支路用命题163.3。
若从原种子计预算，三份独立 $\rho_\psi$ 经九个滤波及三个 proper 帽、局部酉，
给出 $t^3\Delta/108$，总迹 $t^3/54>0$。
GHZ 支路的归一资源输出为 $t\Delta/2$。
这同时支付了原种子到资源的有限非零系数，而非只讨论抽象 SLOCC 可达性。

现在把 $\Delta$ 接入 [VII，命题103.7的构造及定理103.8][Q163VII]。
本背景已经支付了103.7证明所需的一体合同；不再调用103.5之前的对齐归约。
为明确所需资源，单一局部块的有序活跃块对只有 $(i,i)$，其三条腿仍互不相同。
取 $P=|1\rangle\langle1|$、$X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$，
用(163.6)的参考—输出向量化，有

$$
\begin{aligned}
\alpha&=|I-P\rangle\!\rangle|0\rangle
          +|P\rangle\!\rangle|1\rangle=g,\\
\gamma&=|0\rangle|I\rangle\!\rangle
          +|1\rangle|X\rangle\!\rangle
        =|000\rangle+|011\rangle+|101\rangle+|110\rangle
        =\sqrt2 H^{\otimes3}g.
\end{aligned}
\tag{163.13}
$$

于是 VII(102.24) 的两个指定 dyad 均在原 $C_3$，迹分别为 $2,4$。
从 $\Delta/2$ 经局部酉分别得到 $\alpha\alpha^*/2$ 和 $\gamma\gamma^*/4$，
二者质量均为一；这是103.7在 $d=e=b=2$ 的构造与预算。
二资源的原 $C_6$ 乘积经一个 $\beta/2$，按 VII(103.19) 给

$$
\frac{J(\operatorname{Ad}_{U})}{16}\in C_4,
\qquad U=(I-P)\otimes I+P\otimes X,
\qquad u_4\left(\frac{J(\operatorname{Ad}_{U})}{16}\right)=\frac14.
\tag{163.14}
$$

它只是资源收缩的质量。原自身 Choi 判据据此给该二体门及全部原旁观提升的数学正性。
这精确满足 VII103.8 包含重复标签 $(i,i)$ 的两 dyad 输入。
该削弱尾部复用既有精确有限酉字及态—效应双向夹逼，从而对每个有限 $N$ 给条件2。
调用的是103.8，而不是带 $S_3$ 入口的整条102.11；没有补入整个 $C_3$ 标准性。

反向，条件2在 $N=3$ 包含 $\Delta=gg^*$；$g$ 的三个展平秩均为二，故条件1成立。∎

### 163.5 一般局部维数的同时秩二截取

**引理 163.5（同时保住三个展平秩）。** 若
$\psi\in(\mathbb C^n)^{\otimes3}$ 的三个展平秩均至少为二，则存在
$L_i:\mathbb C^n\to\mathbb C^2$，使
$\phi=(L_1\otimes L_2\otimes L_3)\psi$ 的三个展平秩均为二。

**证明。** 在复仿射空间
$\mathcal A=\prod_{i=1}^3\operatorname{Mat}_{2\times n}(\mathbb C)$ 中，
条件 $r_i(\phi)\ge2$ 是某个 $2\times2$ 子式非零的有限并，故为 Zariski 开集 $U_i$。
分别证明 $U_i$ 非空：固定 $\psi$ 第 $i$ 个展平的一个非零 $2\times2$ 子式。
它的两行只用该腿的两个不同基指标；两列是另外两腿的两个基指标对，
在各腿至多用两个指标。对三腿各作坐标截取，保留这些指标并映到 $\mathbb C^2$。
某一腿若只用一个指标，就任取另一个不同指标补到两个，因 $n\ge2$ 可行。
原非零子式仍是截取后第 $i$ 个展平的子式，所以 $U_i\ne\varnothing$。
复仿射空间不可约，三个非空 Zariski 开集的交非空。
取交中的 $L_i$，三秩均至少二；输出每腿维数为二，故恰为二。∎

固定同一个二维子空间 $S\subset\mathbb C^n$、等距嵌入
$J:\mathbb C^2\to\mathbb C^n$，令 $P=JJ^*$。
对(163.4)的原种子，把上引理的输出嵌回该同一个 $S$：

$$
A_i=JL_i:\mathbb C^n\to\mathbb C^n,\qquad
\widetilde\phi=(A_1\otimes A_2\otimes A_3)\psi\in S^{\otimes3}.
\tag{163.15}
$$

引理163.2使 $\widetilde\phi\widetilde\phi^*\in C_3$。
将各 $A_i$ 除以 $\max\{1,\|A_i\|\}$ 即有全部原旁观者上的不增迹实现，
输出仍非零，归一质量严格为正。
这里调用的是原 $n\to n$ 一体映射，未把 $n\to2$ 的形式矩阵当成模型新增物种。

### 163.6 固定二维压缩的完整锥族与全对偶

**命题 163.6（原正幂等压缩继承整个背景）。** 对固定的 $P$ 定义

$$
Q(x)=PxP,\qquad Q_N=Q^{\otimes N},\qquad
W_N^P=\operatorname{ran}Q_N,\qquad
C_N^P=C_N\cap W_N^P.
\tag{163.16}
$$

以 $J^{\otimes N}$ 识别 $W_N^P$ 与
$\operatorname{Herm}_{2^N}(\mathbb C)$，并限制原迹单位。
则整个族 $(C_N^P)_{N\ge1}$ 满足定义163.1的 $n=2$ 全部条件，
包括所有有限分块的最小／最大界、所有位置置换，以及其自身完整对偶与 proper 区间。

**证明。** 引理163.2先给 $Q$ 的原全旁观正性。
故 $Q_N(C_N)\subseteq C_N$；$Q_N^2=Q_N$ 给

$$
Q_N(C_N)=C_N\cap\operatorname{ran}Q_N=C_N^P.
\tag{163.17}
$$

右边是闭锥与闭子空间的交，所以闭；尖性与严格正迹直接继承。
在 $S$ 上的 PSD 秩一一体矩阵实张成 $\operatorname{Herm}(S)$；
由原最小界，它们的任意 $N$ 重乘积均在 $C_N^P$。
这些乘积实张成 $W_N^P$，所以压缩锥生成整个内在空间。
低二层的原 PSD 等式给 $C_1^P=\operatorname{Herm}_2^+$、
$C_2^P=\operatorname{Herm}_4^+$，坐标统一使用 $J$。

先核算原单位预算，不能把未知高层 $x\in C_N$ 当作 PSD。
置 $R_0=P,R_1=I_n-P$，对 $\epsilon\in\{0,1\}^N$ 定义
$M_\epsilon(x)=R_\epsilon xR_\epsilon$，
$R_\epsilon=R_{\epsilon_1}\otimes\cdots\otimes R_{\epsilon_N}$。
每项由局部合同原正，$\sum_\epsilon R_\epsilon^*R_\epsilon=I$，且在整个向量空间上

$$
\sum_\epsilon u_N(M_\epsilon x)=u_N(x).
\tag{163.18}
$$

这是完备的局部 Kraus 投影族的迹恒等式，不声称其和是恒等映射。
对原正 $x$ 各项迹均非负，全零标签项就是 $Q_N$，因此
$0\le u_N(Q_Nx)\le u_N(x)$。

任意内在正泛函 $g\in(C_a^P)^*$ 在整个原空间有正延拓

$$
\widetilde g=g\circ Q_a\in C_a^*,\qquad
\widetilde g|_{W_a^P}=g.
\tag{163.19}
$$

这支付全部内在正对偶，非仅矩阵效应子集。
若 $0\le g\le u_a|_{W_a^P}$，则对全部 $x\in C_a$，
$0\le\widetilde g(x)\le u_a(Q_ax)\le u_a(x)$，故延拓为原 proper 效应。
其补效应的正性同时来自(163.18)与内在的 $u_a-g$。

对任意 $x\in C_{a+b}^P$ 和任意内在正 $g,h$，原最大界作用于
$\widetilde g\otimes\widetilde h$，给
$(g\otimes h)(x)\ge0$；这里 $Q_a\otimes Q_b$ 在 $x$ 上为恒等。
故得到完整内在最大界。
原最小界与闭性给完整内在最小界。
同一个 $P$ 用于所有位置，使 $Q_N$ 与全部因子置换交换，故置换及其逆限制为正；
规范重括号、原乘法配对及单位也限制为同一套数据。
最后取整个压缩基、全部内在极点与整个内在 proper 区间作为压缩模型数据；
不需要它们与原 $P_N$ 有任何极点对应。∎

**定理 163.7（一般 $n$ 的完整 qubit 压缩结论）。**
在定义163.1及(163.4)下，对每个固定二维 $S$ 及每个有限 $N$，

$$
C_N\cap\operatorname{Herm}(S^{\otimes N})
 =\operatorname{Herm}^+(S^{\otimes N}).
\tag{163.20}
$$

**证明。** 用引理163.5和(163.15)把原种子送进这个固定 $S^{\otimes3}$，
所得实际矩阵秩一态在 $C_3^P$ 且三展平秩均为二。
命题163.6支付压缩族的全部有限背景和全效应菜单，故定理163.4适用于整个压缩族，
给(163.20)。其内部使用的滤波亦可用 $JMJ^*$ 写成原 $n\to n$ 合同；
内在 Bell proper 效应可按(163.19)延拓，再由原切片作用于任意原旁观者。
所以没有只在选定点或选定效应上应用 qubit 定理。∎

### 163.7 尚未支付的原编码与一个准确充分接口

**命题 163.8（寄存器汇入一条原 $n$ 维腿）。** 在定理163.7的假设下，
固定上述 $J$，取 $m=\lceil\log_2 n\rceil$，为 $0\le a<n$ 选各不相同的
$m$ 位计算字 $s_a$，固定原 $\mathbb C^n$ 的正交归一基 $|a\rangle$。
定义实际矩阵与原映射

$$
K=\sum_{a=0}^{n-1}|a\rangle\langle s_a|(J^*)^{\otimes m},
\qquad E:W_m\to W_1,\quad E(x)=KxK^*,
\qquad
\eta_n=\sum_{a=0}^{n-1}\overline J^{\otimes m}|s_a\rangle\otimes|a\rangle.
\tag{163.21}
$$

这里 $\overline J$ 是固定实际计算基中的逐项共轭；参考腿的共轭来自固定的 Choi 约定。
若 $S$ 是计算二维角且 $J$ 为标准嵌入，则 $\overline J=J$。
在同一个原全有限层级中，以下三个条件等价：

1. $\eta_n\eta_n^*\in C_{m+1}$。
2. $E$ 对每个原有限旁观者正。
3. 对每个有限 $N$，$C_N=\operatorname{Herm}_{n^N}^+(\mathbb C)$。

当 $n=2$ 时该接口已由 $C_2$ 支付；当 $n>2$ 时，本章尚未从种子条件推出条件1或2。

**证明。** 由原杯在固定基中的向量化，$J(E)=\eta_n\eta_n^*$，
所以条件1与2正是 VII102.7 的原自身判据。
确切地，$|K\rangle\!\rangle=\sum_t|t\rangle\otimes K|t\rangle$
将输入系数共轭成 $\overline J$，恰给(163.21)；没有在不同层换用参考转置方向。

条件2的单位预算也能支付：$K=KP^{\otimes m}$，故 $E=EQ_m$。
定理163.7使 $Q_mx$ 对每个 $x\in C_m$ 都是压缩 PSD，
而 $K^*K$ 是 $S^{\otimes m}$ 中的码投影，故

$$
0\le u_1(E x)\le u_m(Q_mx)\le u_m(x).
\tag{163.22}
$$

于是 $u_m-u_1E\in C_m^*$。在条件2下，把这个正差与任意原旁观单位相乘，
得到每个旁观扩张的迹不增预算。

由定理163.7，压缩 GHZ dyad $\Delta_S\in C_3$。
取 $m$ 份 $\Delta_S/2$ 原相乘，按原置换重排成三组、每组 $m$ 腿，得到

$$
\frac{h_mh_m^*}{2^m}\in C_{3m},\qquad
h_m=\sum_{s\in\{0,1\}^m}
 (J^{\otimes m}|s\rangle)^{\otimes3}.
\tag{163.23}
$$

条件2允许在这三个实际寄存器上依次施加 $E$，每次保留所有原旁观者。
输出是 $\Delta_n/2^m$，其中
$g_n=\sum_{a=0}^{n-1}|aaa\rangle$、$\Delta_n=g_ng_n^*$；其迹为 $n/2^m>0$。
故 $\Delta_n\in C_3$。
现在用 VII103.7 从这个完整单块资源取得两个指定 dyad，
再用 VII103.8，得到条件3。
反向，条件3包含所有 PSD dyad，故包含 $\eta_n\eta_n^*$，得到条件1。∎

这里的编码形式及其充分性是 [VII，定义104.12、命题104.13][Q163VII]
的单块实例；本章将其接到一般三体种子的压缩输出，不把融合原理另认作新结果。
对 $n>2$，(163.20)只控制每条原腿都位于同一二维支撑的整个子层级。
$E$ 的输出却是一条原 $n$ 维腿，故压缩内部的任意矩阵 CP 操作不能直接替代条件2。
即使(163.22)已经证明单独输入上的正性和迹预算，它仍未给含任意原旁观者的正性。
剩余义务正是混合编码 dyad 的原锥成员关系，或足以直接产生 $\Delta_n$ 的其他原资源论证。
本章既不证明这项义务不可导出，也不由它未付而构造反例；
没有把有限前缀或受限抽象网络称为完整全有限反模型。

### 163.8 已有量子公理的对应、归属与几何图景

**推论 163.9（既有静态字典的原位复用）。** 在定理163.4的等价条件下，
全部有限原数据满足

$$
K_N=\{\rho\succeq0:\operatorname{Tr}\rho=1\},\quad
\mathcal E_N=\{E:0\preceq E\preceq I\},\quad
\Pr(E\mid\rho)=\operatorname{Tr}(E\rho),\quad
P_N\cong\mathbb{CP}^{2^N-1}.
\tag{163.24}
$$

有限菜单恰为 POVM；原全旁观正映射恰为对应矩阵 CP 映射，不增迹／保迹分别是
有限 Kraus 算子的 $\sum_\alpha K_\alpha^*K_\alpha\preceq I$／$=I$。
这些是 [VII，102.12—102.15及103.12][Q163VII] 的现成对应，按已证锥等式复用。
一般 $n$ 在定理163.7下仅得到压缩族内的同一完整字典；只有另付命题163.8的接口后，
才得到整个原 $n$ 维层级的字典。

复矩阵载体、迹单位、实际张量规则、完整菜单和已对齐低二层是站立输入；
本结果条件性地把高阶整锥几何输入压缩成一个三体矩阵秩一种子的存在性。
它不从零导出复数域或低二层，也不比较整套独立公理的最少数目。
数学分支成为可用物理事件仍需 VII102.14 的额外事件饱和；
有限仪器、正概率条件更新及零质量边界直接保留 VII102.15 的合同。
静态几何不选择物理钟、Hamiltonian、时间尺度或 $\hbar$，也不指定效应的唯一更新；
更新后的测量次序仍可不交换，沿用 VII103.12 的边界。

Dür–Vidal–Cirac 的三 qubit 分类、原自身 Choi／切片、指定 dyad 构造、精确有限字尾部、
Born／CP 字典和既有融合接口均为复用。
本章实际补接的是 W 三角形在未知高阶原锥中的逐次准入及预算、任意矩阵秩一种子到
该资源的接口，以及一般 $n$ 同时秩二截取后对完整压缩族的正幂等与全对偶核算。
所作等价限于上述明确模型域，不含物理实现或全部一般维数已闭合的断言。

**完整中文图景。** 先把一份和两份系统的量子坐标固定好，同时保留所有有限份原系统及其全部效应。
对 qubit，只需原三份锥里有一个跨每种二分割都纠缠的矩阵秩一态：若它属于 GHZ 类，局部滤波直接给相干叉口；
若属于 W 类，就取三个副本沿三角形接上三只 Bell 帽。内部没有激活边时留下外部 $111$，
恰有一条激活边时留下其对顶点的那个单独 $1$，四项叠加经局部 Hadamard 和相位便成为 GHZ。
这一资源供应既有尾部所需的两张小 dyad，尾部于是锁定每一有限层的整个态锥与效应锥。
较大局部维数也能把任意这种种子同时滤进固定二维支撑，且二维压缩保留全部正对偶和单位预算，
所以其中每一有限层同样都是量子锥；但多条二维腿汇成一条原 $n$ 维腿还缺明确的原编码资源，
压缩结论没有越过这道接口去替整个原层级作结论。

[Q163VII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Q163DVC]: https://arxiv.org/abs/quant-ph/0005115

**原始文献与精确供应。** [DVC][Q163DVC]：W. Dür, G. Vidal, J. I. Cirac,
*Three qubits can be entangled in two inequivalent ways*, Phys. Rev. A **62**, 062314，
DOI [10.1103/PhysRevA.62.062314](https://doi.org/10.1103/PhysRevA.62.062314)，
§III.1—III.2 的局部秩与 GHZ/W 完整分类、式(15)、(26)及各自随后给出的可逆局部矩阵，
以及附录A的可逆局部算子定理和滤波缩放论证。
[VII][Q163VII] 的来源固定为已发表提交 `bb4f68b5d54f7b55cdf683c779a6c28e9bc46ab8`：
102.1原域；102.6—102.7整锥切片、自身 Choi 和重复帽预算；102.8／103.6局部合同；
103.2矩阵秩一资源及其原纯性边界；103.7和(102.24)两指定 dyad；103.8全有限削弱尾部；
104.12—104.13原融合接口；102.12—102.15／103.12既有静态字典、事件及时间边界。
## 追加锚（本行以下为增补区）

## 164. 一条正则相干矩阵线与全部有限复量子锥

本章在同一已对齐低二层的全有限原锥背景中，证明一个存在性等价：原三腿锥中存在
一条相干、非标量、含满秩点的矩阵铅笔，当且仅当每个有限层都是完整复量子锥。
承重接口是原数据腿上的串行乘法与实际 qubit 控制资源的相干收缩；不输入分组编码。
第163章的原滤波、三体种子与完整二维压缩结果作为本卷前置。

### 原域、切片与允许的数学操作

**定义 164.1（精确的站立背景）。** 固定任意整数 $n\ge2$，令
$V=\operatorname{Herm}_n(\mathbb C)$、$W_N=V^{\otimes_{\mathbb R}N}$。
对所有有限 $N\ge1$，给定闭、尖、生成凸锥 $C_N\subset W_N$，并要求
$u_N=\operatorname{Tr}=u_1^{\otimes N}$ 在 $C_N\setminus\{0\}$ 上严格为正。
同一个实际张量坐标给向量空间识别 $W_N\cong\operatorname{Herm}_{n^N}(\mathbb C)$，且

$$
C_1=\operatorname{PSD}_n,\qquad C_2=\operatorname{PSD}_{n^2}.
$$

这里及以下 $\operatorname{PSD}_d=\operatorname{Herm}_d^+(\mathbb C)$。
使用整个原基 $K_N=\{x\in C_N:u_N(x)=1\}$、全部极点 $P_N=\operatorname{ext}K_N$、
完整正对偶 $C_N^*$ 和完整 proper 区间 $\mathcal E_N=[0,u_N]_{C_N^*}$；
有限效应菜单是全部有限单位分解。对每个有限实际分块 $a+b$，要求

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
 \subseteq C_a\otimes_{\max}C_b.
$$

最小锥是正简单张量的闭凸生成锥；最大锥由全部 $f\otimes g$，
$f\in C_a^*$、$g\in C_b^*$ 的非负半空间定义。所有位置置换及其逆均原正；
重括号是同一原实张量空间上的规范恒等识别，非连续分块由原置换运输。
原配对满足 $(f\otimes g)(x\otimes y)=f(x)g(y)$，单位如上相乘。
约定 $W_0=\mathbb R,C_0=\mathbb R_+,u_0=\mathrm{id}$。
这完整保留 [VII，定义102.1][Q164VII] 的单块模型域；未预付任何 $N\ge3$ 的 PSD、
高阶自对偶、全局矩阵映射正性或高阶纯态分类。

称 $F:W_m\to W_k$ **原全旁观正**，若对每个有限 $r\ge0$，
$(\mathrm{id}_{W_r}\otimes F)C_{r+m}\subseteq C_{r+k}$，包括置换后的作用位置。
下文的协议均指原准备、张量乘积、这些已支付映射及 proper 帽的有限数学复合；
事件菜单与装置可用性不由这个用语指定。

**定义 164.2（相干正则铅笔）。** 固定实际计算基 $|0\rangle,\ldots,|n-1\rangle$，始终取

$$
|A\rangle\!\rangle=\sum_i|i\rangle_{\rm ref}\otimes A|i\rangle_{\rm out},
\qquad
(R\otimes L)|A\rangle\!\rangle=|LAR^{\mathsf T}\rangle\!\rangle.
$$

三腿次序为参考、输出、控制。对非零 $\psi$ 写
$\psi=\sum_k|A_k\rangle\!\rangle|k\rangle$，其控制切片像为
$\mathcal L_\psi=\{\sum_k\alpha_kA_k:\alpha\in(\mathbb C^n)^*\}$；
这里 $\alpha=\sum_k\alpha_k\langle k|$ 是线性 bra，系数直接是 $\alpha_k$。
称原矩阵秩一 dyad $\psi\psi^*\in C_3$ **含二元正则铅笔**，若
$\mathcal L_\psi$ 含二维子空间 $\mathcal L=\operatorname{span}_{\mathbb C}\{A,B\}$，
其中 $A\in GL_n(\mathbb C)$、$B$ 与 $A$ 线性无关。
等价地，$\det(xA+yB)$ 非恒零，且矩阵线确有两个独立方向。
也可直接要求见证的整个切片像恰为二维；下文的单次控制滤波说明两种存在性入口等价。
“秩一”只指实际矩阵秩，不预先断言这是未知原基的极点。

**引理 164.3（原自身 Choi、帽与全部预算）。** 在定义164.1下，令

$$
\Omega_n=|I_n\rangle\!\rangle\langle\!\langle I_n|,\qquad
\beta_n(x)=\operatorname{Tr}(\Omega_nx).
$$

则 $\Omega_n/n\in K_2$、$\beta_n/n\in\mathcal E_2$。
把 $m$ 对原杯重排为全部参考在前、全部输入在后，记作 $\Omega_m$，则

$$
J(F)=(\mathrm{id}_{W_m}\otimes F)\Omega_m\in C_{m+k}
\quad\Longleftrightarrow\quad F:W_m\to W_k\text{ 原全旁观正}.
$$

每个一体合同 $\Phi_A(x)=AxA^*$ 原全旁观正；$A^*A\preceq I_n$ 时所有提升不增迹。
每个 $f\in C_a^*$ 可对整个原联合输入切片，重复切片仍在剩余原锥；若 $f$ proper，则

$$
0\le u_b((f\otimes\mathrm{id})z)\le u_{a+b}(z)\quad(z\in C_{a+b}).
$$

**证明。** 逐项使用 [VII，引理102.6—102.8][Q164VII]，也即163.2的已付接口。
最大界和闭锥双极性给切片；$(u_a-f)\otimes u_b$ 对原联合锥正给上界。
$C_2$ 的 PSD 等式给杯及 proper 帽；最小界给任意有限杯乘积。
在任意 $z\in C_{r+m}$ 与原 $J(F)$ 的乘积上，逐对用 $\beta_n$ 接输入与参考，
精确蛇式给 $(\mathrm{id}_{W_r}\otimes F)z$，没有转置余项。
每一步切片面对的是整个剩余原锥，故包括任意原纠缠旁观者，不要求高阶自对偶。
一体合同的 Choi 是原 $C_2$ 中的 $|A\rangle\!\rangle\langle\!\langle A|$。
若 $A$ 为压缩，$u_1-u_1\Phi_A$ 在 $C_1$ 上正，与旁观单位相乘给全部提升预算。∎

具体地，若一个协议供应 $hJ(F)/T$，其中 $T=u_{m+k}(J(F))>0$、$h>0$，
则用 $m$ 只 proper $\beta_n/n$ 将它接到任意原输入，实施的是
$hF/(Tn^m)$ 及其所有旁观提升。这个公式支付有限字的资源实现。
非零有限滤波一律除以 $s_A=\max\{1,\|A\|\}$；每次 dyad 系数乘 $s_A^{-2}>0$。
正因子可为锥成员关系消去；这不把后选择分支放大成确定性事件。

### 从满秩配对到完整实际控制族

**命题 164.4（规范化、GME 与控制资源）。** 一个含二元正则铅笔的原种子给出

$$
r_M=|I_n\rangle\!\rangle|0\rangle+|M\rangle\!\rangle|1\rangle,
\qquad r_Mr_M^*\in C_3,\quad M\notin\mathbb C I_n.
$$

其三个展平秩是 $(n,n,2)$，故跨每种一腿分割均纠缠（GME）。
它还支付固定实际二维角 $S=\operatorname{span}\{|0\rangle,|1\rangle\}$ 上的整个有限 qubit 族、
全正对偶及 proper 效应延拓；特别地，任意有限控制 ket 的 dyad 均在相应原锥中。

**证明。** 取切片 bra $\alpha,\gamma$ 给出 $A,B$，用同一个控制滤波
$T=|0\rangle\alpha+|1\rangle\gamma$，再在输出腿用 $A^{-1}$，即得 $r_M$，
$M=A^{-1}B$ 非标量。两次均是原 $n\to n$ 一体合同，不是分别准备两个分支。
令 $d_M=\|r_M\|^2=n+\operatorname{Tr}(M^*M)$、
$s_T=\max\{1,\|T\|\}$、$s_L=\max\{1,\|A^{-1}\|\}$。
归一原种子 $\psi\psi^*/\|\psi\|^2$ 经这两次 proper 滤波输出

$$
c_M\,\frac{r_Mr_M^*}{d_M},\qquad
c_M=\frac{d_M}{\|\psi\|^2s_T^2s_L^2}\in(0,1].
$$

$I_n$ 切片使前两腿的秩均为 $n$；$I_n,M$ 独立使控制秩为二。
为支付 qubit 入口，可直接选坐标 $i\ne j$ 使 $M$ 的该二阶主压缩非标量：
有非零非对角元就取其两指标；否则 $M$ 是非标量对角矩阵，取两个不同对角元。
同一个实偏等距 $K=|0\rangle\langle i|+|1\rangle\langle j|$ 作用于前两腿，
留下 $|I_2\rangle\!\rangle|0\rangle+|M_2\rangle\!\rangle|1\rangle\in S^{\otimes3}$，
其中 $M_2=KMK^{\mathsf T}|_S$ 非标量。两个 $K$ 的范数为一；从归一 $r_M$ 的成功质量是
$t_0=(2+\operatorname{Tr}(M_2^*M_2))/d_M>0$。输出三个秩均为二。

现在只复用本卷第163章中 163.4、163.6—163.7 的接口：Dür–Vidal–Cirac 三 qubit GHZ/W 分类、
GHZ 支路的局部滤波或 W 支路的三 W 三角收缩，供应实际嵌入的 GHZ$_2$ dyad。
记 $g=|000\rangle+|111\rangle$、$w=|100\rangle+|010\rangle+|001\rangle$、
$\Delta_2=gg^*$，均在这个实际角内。
若分类滤波 $B_i$ 把截取后的 ket 送为代表 $v=g$ 或 $v=w$，令
$s_i=\max\{1,\|B_i\|\}$，则
$t_D=\|v\|^2/([2+\operatorname{Tr}(M_2^*M_2)]\prod_{i=1}^3s_i^2)>0$。
从上述归一原种子计，GHZ 支路的质量为
$c_Mt_0t_D$；W 支路用三份原种子，输出
$(c_Mt_0t_D)^3\Delta_2/108$，质量 $(c_Mt_0t_D)^3/54>0$。
这些是163.3—163.4已完成的预算，不是本章重新声称的分类或三角形结果。

为写清调用的整个族，令 $P$ 投影到 $S$、$Q_N=\operatorname{Ad}_P^{\otimes N}$。
163.6给原正幂等、不增迹和

$$
Q_N(C_N)=C_N\cap\operatorname{Herm}(S^{\otimes N}),\qquad
g\mapsto g\circ Q_N
$$

对完整内在正对偶及 proper 区间的原延拓，并支付全部分块 min/max 界。
163.7于是给上式的锥恰为 $\operatorname{PSD}(S^{\otimes N})$，对每个有限 $N$ 成立。
等价地，可在已付 GHZ$_2$ 后接 [VII，命题104.11][Q164VII] 的完整 retract 证明。
参考嵌入取实际实坐标，故无额外共轭；一般复嵌入的参考腿须用共轭嵌入。
这里供应的是多条实际二维角腿；没有把它们编码为一条原 $n$ 维输出腿。∎

该控制资源也可追溯成有限种子网络，而不必仅用锥等式挑选准备。
163.4接 VII103.7—103.8的精确 qubit 有限字，能把控制乘积纯态精确送到任意目标 ket。
若字中第 $\ell$ 个二体门的原 Choi 资源输出为 $h_\ell J_\ell/4$，$h_\ell>0$，
用两只原 $\beta_n/n$ 接入控制寄存器，系数乘 $h_\ell/(4n^2)$；一体角酉延为原一体酉。
所以目标归一控制态有有限实现质量
$t_Q=\prod_\ell [h_\ell/(4n^2)]>0$，空乘积为一。
更具体地，令 $t_G$ 为刚才给出的归一 GHZ$_2$ 供应质量。
VII103.7的两叉口经局部酉给归一 $\alpha,\gamma$，桥帽取原 $\beta_n/n$，
就输出 $t_G^2J_{\rm CNOT}^0/(8n)=hJ_{\rm CNOT}^0/4$，其中 $h=t_G^2/(2n)>0$。
$J_{\rm CNOT}^0$ 是真正角零扩张的四腿 Choi，迹为四；未把角门当成全 $n^2$ 维酉。
故可固定这个门，在有 $L$ 次二体使用的精确控制字中取
$t_Q=[t_G^2/(8n^3)]^L>0$。所有拷贝预先原相乘，组成同一有限协议。
这个溯源仅用于资源与预算，不重复计入163章和既有有限字尾部的成果。

### 原数据线上的相干多项式

**引理 164.5（任意有限多项式的单一协议）。** 若 $r_Mr_M^*\in C_3$ 且命题164.4的
完整控制族已经支付，则对每个有限复多项式 $f$，有

$$
r_{f(M)}=|I_n\rangle\!\rangle|0\rangle+|f(M)\rangle\!\rangle|1\rangle,
\qquad r_{f(M)}r_{f(M)}^*\in C_3.
$$

此构造在所有原旁观者上正，具有有限严格正的成功预算。

**证明。** 取 $p\ge1$、$\deg f\le p$，写 $f(t)=\sum_{j=0}^pf_jt^j$，允许补零。
准备 $p$ 份 $r_M$，第 $j$ 份腿为 $(r_j,o_j,c_j)$。
用 $\langle I_n|=\sum_i\langle i|\langle i|$ 把 $o_j$ 接到 $r_{j+1}$，$1\le j<p$。
留下的次序规定为 $(r_1,o_p,c_1,\ldots,c_p)$，ket 恰为

$$
\Xi_p=\sum_{s\in\{0,1\}^p}|M^{|s|}\rangle\!\rangle|s\rangle.
$$

确切的串行乘积顺序是 $M^{s_p}\cdots M^{s_1}$；因各因子是同一个 $M$ 的幂，才化为
$M^{|s|}$。参考—输出约定及实 Bell bra 保证这里没有 $M^{\mathsf T}$ 或 $\overline M$。
最小界给初始 $C_{3p}$，$p-1$ 次原帽切片给 $C_{p+2}$。

每个重量 $j$ 只选一个计算字 $s^{(j)}$，其中 $s^{(0)}=0^p$。
命题164.4供应 $p+1$ 条实际控制腿上的同一个 ket

$$
Q_f=|0^p\rangle|0\rangle+
 \sum_{j=0}^pf_j|s^{(j)}\rangle|1\rangle,
\qquad d_f=\|Q_f\|^2=1+\sum_{j=0}^p|f_j|^2.
$$

在 $\Xi_p$ 的第 $j$ 条控制腿与 $Q_f$ 的第 $j$ 条腿之间，各用一只原 $n$-Bell 帽。
它们在嵌入计算字上按相等指标配对；系数是 $f_j$，不是 $\overline{f_j}$。
剩余三腿仍按参考、输出、最后控制排列，恰为 $r_{f(M)}$。
$s^{(0)}$ 同时用于最后控制的 $0$、$1$ 两值没有冲突，两项在这个最后腿上正交。

完整协议的资源同时位于原 $C_{4p+1}$；共 $2p-1$ 只帽，最后留下三腿。
没有从分别优化的 $M^j$ 态相加来推断相干性，所有幂及其系数来自同一个 ket 收缩。
若输入分别是 $c_M r_Mr_M^*/d_M$ 的 $p$ 份和 $t_Q Q_fQ_f^*/d_f$，
每只帽均取 proper $\beta_n/n$，最终输出为

$$
\frac{c_M^pt_Q}{d_M^pd_fn^{2p-1}}\,r_{f(M)}r_{f(M)}^*,\qquad
t_f=\frac{c_M^pt_Q\,[n+\operatorname{Tr}(f(M)^*f(M))]}
 {d_M^pd_fn^{2p-1}}\in(0,1].
$$

全部因子有限且严格正；非零性已有 $I_n$ 切片保证，上界来自逐次 proper 预算。
若按完整原准备菜单直接选归一控制态，可取 $t_Q=1$；若要求种子溯源，就使用前段的
有限正乘积。后者仍是同一批预先相乘的有限资源和同一个结果分支。
对任意有限 $r$，把旁观者附在上述每一原乘积与切片上，引理164.3给整段的原正性及预算。∎

**引理 164.6（两资源耦合及原复合）。** 对实际 $r_Ar_A^*\in C_3$，两份资源给出
每个 $z\in\mathbb C$ 的原四腿 Choi 元素

$$
J(\operatorname{Ad}_{K_z})\in C_4,\qquad K_z=I_{n^2}+zA\otimes A.
$$

**证明。** 控制帽与其效应矩阵明确取

$$
b_z=\langle00|+z\langle11|,\qquad
b_z^*=|00\rangle+\overline z|11\rangle,\qquad
e_z(x)=\frac{b_zxb_z^*}{1+|z|^2}
 =\operatorname{Tr}\!\left(\frac{b_z^*b_z}{1+|z|^2}x\right).
$$

$b_z^*b_z/(1+|z|^2)$ 是原 $C_2$ 中的秩一正交投影，故 $e_z\in\mathcal E_2$。
未归一 ket 收缩为 $|I\rangle\!\rangle\otimes|I\rangle\!\rangle
+z|A\rangle\!\rangle\otimes|A\rangle\!\rangle$；
原置换把数据腿从 $(r_1,o_1,r_2,o_2)$ 排成 $(r_1,r_2,o_1,o_2)$，即为 $|K_z\rangle\!\rangle$。
所以 $C_6\to C_4$ 的一次 proper 切片给所述 Choi 的正倍数。
两份归一 $r_A$ 的确切输出是 $J(\operatorname{Ad}_{K_z})/[d_A^2(1+|z|^2)]$，
其中 $d_A=n+\operatorname{Tr}(A^*A)$；源若有成功因子，再乘其乘积。
bra 中的 $z$ 与对应 ket 中的 $\overline z$ 不可互换。

两张二体 Choi 按各自“参考两腿、输出两腿”排列；用两只原 Bell 帽把第一张的输出
逐条接到第二张的参考，留下 $|K_2K_1\rangle\!\rangle$ 的 dyad。
每次复合的 proper 帽系数为 $n^{-2}$。任意有限复合及所有原旁观者均由同一切片引理支付。
特别地，所得矩阵即使非酉，其合同也由自身 Choi 判据原全旁观正；未预设全局矩阵操作。∎

### 两个穷尽谱情形中的原纠缠酉

**命题 164.7（至少两个特征值）。** 若 $M$ 有至少两个不同特征值，已付原资源给出
一个原全旁观正、其逆亦原全旁观正的纠缠二体酉共轭。

**证明。** 在 $\mathbb C[t]$ 中将最小多项式写为
$\mu_M(t)=\prod_{\lambda\in\sigma(M)}(t-\lambda)^{r_\lambda}$。
选非空真子集 $F\subset\sigma(M)$。令 $u$、$v$ 分别为 $F$ 内、外的主因子乘积；
它们互素，Euclid／Bézout 恒等式给 $hu+kv=1$，取 $f=kv$。
这就是此处所用的成熟多项式中国剩余定理，具体满足

$$
f\equiv1\pmod{(t-\lambda)^{r_\lambda}}\ (\lambda\in F),\qquad
f\equiv0\pmod{(t-\lambda)^{r_\lambda}}\ (\lambda\notin F).
$$

因而 $\mu_M\mid(f^2-f)$，$P=f(M)$ 是幂等；在两类特征向量上的值分别为一、零，
故 $0\ne P\ne I_n$。引理164.5供应的是同一个相干 $r_P$，并非只供应 $P$ 的独立分支。
取由 $\operatorname{im}P$ 与 $\ker P$ 的基组成的 $S\in GL_n$，则
$S^{-1}PS=P_0$ 是标准坐标正交投影，秩在 $1$ 与 $n-1$ 之间。
参考腿用 $S^{\mathsf T}$、输出腿用 $S^{-1}$，保留 $I_n$ 并把 $P$ 送到 $P_0$。
这两个原一体滤波各除以其 $s_A$ 后均 proper；从归一 $r_P$ 的质量为

$$
\frac{n+\operatorname{rank}P_0}
 {[n+\operatorname{Tr}(P^*P)]\,
  \max\{1,\|S^{\mathsf T}\|\}^2\max\{1,\|S^{-1}\|\}^2}>0.
$$

取两份所得资源，在引理164.6中令 $z=-2$，得到

$$
U_P=I_{n^2}-2P_0\otimes P_0,\qquad
J(\operatorname{Ad}_{U_P})\in C_4.
$$

$P_0\otimes P_0$ 在整个 $n^2$ 维空间上是正交投影，故 $U_P^*=U_P=U_P^{-1}$。
在 $\operatorname{im}P_0$、$\ker P_0$ 各取单位向量 $a,b$，则

$$
U_P\left(\frac{b+a}{\sqrt2}\otimes\frac{b+a}{\sqrt2}\right)
 =\frac{|bb\rangle+|ba\rangle+|ab\rangle-|aa\rangle}{2}.
$$

其二阶系数矩阵行列式为 $-1/2$，故 Schmidt 秩为二，$U_P$ 是 imprimitive。
Choi 判据给它及其同一个逆的全部原旁观正性；迹恒等式给每个提升保迹。
若前序供应为 $c_P r_{P_0}r_{P_0}^*/(n+k)$，其中 $k=\operatorname{rank}P_0$，则输出是
$c_P^2J(\operatorname{Ad}_{U_P})/[5(n+k)^2]$，质量 $c_P^2n^2/[5(n+k)^2]>0$。
这里 $1/(1+|-2|^2)=1/5$；$c_P>0$ 是源滤波与多项式预算的有限乘积。∎

**命题 164.8（唯一特征值与全空间剪切乘积）。** 若非标量 $M$ 只有一个特征值，
已付原资源同样给出纠缠二体酉及其正逆。

**证明。** 写 $M=\lambda I_n+N$。最小多项式给 $N\ne0$ 幂零，设其指数 $r\ge2$。
引理164.5取 $f(t)=(t-\lambda)^{r-1}$，给 $A=N^{r-1}\ne0$ 且
$A^2=0$，因为 $2r-2\ge r$。
令 $q=\operatorname{rank}A\ge1$；$\operatorname{im}A\subset\ker A$ 给 $2q\le n$。
取像空间基 $a_\nu$，选原像 $b_\nu$ 使 $Ab_\nu=a_\nu$，再补齐核空间基。
这些向量合成基；与164.7完全相同的两次原滤波把 $A$ 相似到

$$
J=\sum_{\nu=1}^q|a_\nu\rangle\langle b_\nu|,
$$

现在所有 $a_\nu,b_\nu$ 是互不相同的标准正交基标签。该相似变换的滤波预算也是
$[n+q]/([n+\operatorname{Tr}(A^*A)]s_{S^{\mathsf T}}^2s_{S^{-1}}^2)>0$。
交换每对 $a_\nu,b_\nu$ 的实置换酉 $V$ 满足 $VJV^*=J^*$；
在 $r_J$ 的参考、输出腿同时用 $V$，保持 $I_n$，得到实际 $r_{J^*}$，预算为一。
置 $X=J\otimes J$，取

$$
a=i(\sqrt2-1),\qquad b=\frac{i}{\sqrt2},\qquad
U_J=(I+aX)(I+bX^*)(I+aX).
$$

引理164.6分别用两份 $r_J$、两份 $r_{J^*}$、两份 $r_J$ 给三个剪切因子的原 Choi；
两次复合各用两只 proper 原 Bell 帽，给 $J(\operatorname{Ad}_{U_J})\in C_4$。
所有系数，包括虚数 $a,b$，都放在已明确的 bra $b_z$ 中。

下面在整个 $n^2$ 维空间核算酉性。它有 $q^2$ 个互相正交的不变二维块
$H_{\nu\mu}=\operatorname{span}\{|a_\nu a_\mu\rangle,|b_\nu b_\mu\rangle\}$。
在该有序基中 $X=\begin{pmatrix}0&1\\0&0\end{pmatrix}$，故三个因子的乘积是

$$
\begin{pmatrix}1&a\\0&1\end{pmatrix}
\begin{pmatrix}1&0\\b&1\end{pmatrix}
\begin{pmatrix}1&a\\0&1\end{pmatrix}
=\begin{pmatrix}1+ab&2a+a^2b\\b&1+ab\end{pmatrix}
=\frac1{\sqrt2}\begin{pmatrix}1&i\\i&1\end{pmatrix}.
$$

这里 $ab=-1+1/\sqrt2$，且
$2a+a^2b=a(2+ab)=i(\sqrt2-1)(1+1/\sqrt2)=i/\sqrt2$。
该矩阵与其伴随相乘为 $I_2$。
所有 $H_{\nu\mu}$ 的正交补上 $X=X^*=0$，三个因子均为恒等。
所以 $U_J$ 在全部 $n^2$ 维空间酉；没有遗漏混合 $a,b$ 标签或其余 $n-2q$ 个方向。
它将乘积 $|b_\nu b_\mu\rangle$ 送为
$(i|a_\nu a_\mu\rangle+|b_\nu b_\mu\rangle)/\sqrt2$，Schmidt 秩为二。

逆也逐项支付，而不从“矩阵酉”直接推断未知原锥上的逆正性：

$$
U_J^*=(I+\overline aX^*)(I+\overline bX)(I+\overline aX^*).
$$

用 $r_{J^*},r_J,r_{J^*}$ 和帽系数 $\overline a=-a,\overline b=-b$ 重做同一构造，
得到它的原 Choi。于是两个方向均原全旁观正，且矩阵迹恒等式给保迹。
若前序供应为 $c_Jr_Jr_J^*/(n+q)$，则此六副本构造明确输出

$$
\frac{c_J^6J(\operatorname{Ad}_{U_J})}
 {(n+q)^6(1+|a|^2)^2(1+|b|^2)n^4},
\qquad c_J>0.
$$

其质量为该正系数乘 $n^2$；逆的构造有相同预算。
若要把某个中间剪切单独当成不增迹数学分支，可把其矩阵 $I+zX$
除以 $\max\{1,\|I+zX\|\}$，相应合同除以该数的平方：
其输入原 $C_2$ 已是 PSD，故单位正差及任意原旁观预算都由最大界给出。
本构造本身直接复合 subnormalized Choi，未把未缩放剪切宣称为 proper 事件。∎

### 精确全有限尾部与一个显式六副本见证

**引理 164.9（既有有限字及双向夹逼的准确接合）。** 在定义164.1下，若一个 imprimitive
二体酉 $U$ 的共轭及其逆已原全旁观正，则对全部有限 $N$，$C_N=\operatorname{PSD}_{n^N}$。

**证明。** 复用 [VII，引理102.10及定理103.8证明的尾部][Q164VII]。
这里接合的是“原全旁观可逆纠缠门”之后的证明接口；不把本章的门冒充103.8陈述中的两张指定 dyad。
为明确所代入的量词，假定旧 $N-1$ 腿能用有限字精确给全部 $U(D)$，$D=n^{N-1}$。
这些字的每个生成元都有任意原旁观提升，所以整字可把新原腿保持恒等。
新腿提供 $U(e)$，$e=n$。把 $U$ 放在一个旧实际位置与新腿；固定其余旧腿为乘积向量，
原二体的纠缠见证即为“旧整个块／新腿”切分的 Schmidt 秩大于一的见证。
因此这个跨块门 imprimitive，旧有限字与新局域酉支付全部 $U(D)\otimes U(e)$。

Harrow，[arXiv:0806.0631v1，推论2][Q164H]，允许 $D\ne e$，并给精确有限乘积覆盖
$U(De)$。将每个旧块因子展开回已得有限字，仍是同一原 $N$ 腿上的有限字。
归纳从一体原酉开始；所有生成元及其逆均已有原正性与保迹预算。
这里没有新增一个任意分组矩阵映射，也没有以稠密性、极限或近似门替代精确生成。
精确性属于 Harrow 的成熟定理；该尾部的原旁观归纳属于已存在的 VII102.10。

最后照用 VII103.8 的两个包含，写出单块情形。
原一体纯态的乘积 $p_0$ 由最小界在 $C_N$；有限字把它送到任意归一秩一 dyad。
有限谱分解给 $\operatorname{PSD}_{n^N}\subseteq C_N$。
反向，局部秩一效应的乘积 $e_0(x)=\operatorname{Tr}(p_0x)$ 是原 proper 效应。
其正性由最大界给出，上界逐次使用

$$
u_{a+b}-f\otimes g=(u_a-f)\otimes u_b+f\otimes(u_b-g)\in C_{a+b}^*.
$$

对任意单位 $\psi$，选有限字 $W$ 使 $Wp_0W^*=|\psi\rangle\langle\psi|$。
已支付的逆字给原 proper 效应 $e_0\circ\operatorname{Ad}_{W^*}$，故对每个 $x\in C_N$，
$\langle\psi|x|\psi\rangle\ge0$。于是 $C_N\subseteq\operatorname{PSD}_{n^N}$。
这确立全部原态与全部原效应的等式，不只是一个可生成的态子锥。
任一有限字若按资源协议实现，其每次 Choi 接入均有引理164.3的有限正因子；
字长有限即总预算严格正。其数学保迹自同构性质不要求该资源分支确定性成功。∎

**命题 164.10（显式种子的六副本、十八腿预算）。** 取

$$
\tau_n=\sum_{i=0}^{n-1}|ii0\rangle+|011\rangle
 =|I_n\rangle\!\rangle|0\rangle+|E_{10}\rangle\!\rangle|1\rangle.
$$

若 $\tau_n\tau_n^*\in C_3$，六份归一原种子即可给一个纠缠二体酉的原四腿 Choi，
且成功质量明确非零；不需要先调用控制多项式网络。

**证明。** 本约定下 $E_{10}=|1\rangle\langle0|$，故它的向量化确为 $|01\rangle$。
三个局部秩是 $(n,n,2)$，$\|\tau_n\|^2=n+1$。
令 $J=E_{10}$、$X=J\otimes J$，$a,b$ 取164.8的值。
将六份 $\tau_n\tau_n^*/(n+1)$ 依次配为三对，初始原锥为 $C_{18}$。
中间一对的每份资源在两条数据腿同时施加交换 $|0\rangle,|1\rangle$ 的实置换酉；
这把 $J$ 送为 $J^*$，保留 $I_n$，范数与质量都不变。

三对控制腿依次用 $e_a,e_b,e_a$，每只帽均是164.6的实际 proper 二腿效应。
三次切片 $C_{18}\to C_{16}\to C_{14}\to C_{12}$ 后，
剩下三张四腿 Choi，矩阵分别为 $K_a=I+aX$、$K_b=I+bX^*$、$K_a$。
每张的腿均按“参考两腿、输出两腿”排列。
第一张输出两腿分别接第二张参考两腿，第二张输出两腿再接第三张参考两腿。
每个接头是 $\beta_n/n$；第一次双接头 $C_{12}\to C_8$，第二次 $C_8\to C_4$。
因此数据帽恰有四只，连同三只控制帽共七只，消去十四腿，留下四腿。
串行顺序给 $K_aK_bK_a=U_J$；164.8已在整个 $n^2$ 空间证明其酉性及纠缠性。

最终原输出及其成功质量恰为

$$
\frac{J(\operatorname{Ad}_{U_J})}{D_n},\qquad
D_n=(n+1)^6(1+|a|^2)^2(1+|b|^2)n^4,
\qquad p_n=\frac{n^2}{D_n}>0.
$$

六份归一种子给 $(n+1)^{-6}$；三只 proper 控制帽给
$(1+|a|^2)^{-2}(1+|b|^2)^{-1}$；四只 proper 数据帽给 $n^{-4}$。
因 $U_J$ 酉，Choi 的迹是输入维数 $n^2$，所以这就是成功质量。
$1+|a|^2=4-2\sqrt2>1$、$1+|b|^2=3/2$，故 $0<p_n<1$；
上界也直接来自逐次 proper 预算。
把三对类型改为 $J^*,J,J^*$，帽系数改为 $-a,-b,-a$，同一分母供应 $U_J^*$。
一切局部置换、帽与旁观扩张均已由原 $C_2$ 及切片支付。
若再用两只 proper 原 Bell 帽把这个四腿资源接到任意归一两腿输入，
所得是 $\operatorname{Ad}_{U_J}/(D_nn^2)$，成功质量 $1/(D_nn^2)>0$。
恢复未缩放 Choi 只用于锥成员关系；并未恢复该分支的事件成功率。

当 $n=2$，只在输出腿交换 $0,1$，$\tau_2$ 就变为
$|010\rangle+|100\rangle+|001\rangle$，即 W 代表。
当 $n>2$，它的控制秩二与 GHZ$_n$ 的秩 $n$ 不同，因此不在 GHZ$_n$ 的可逆局部类中。∎

**定理 164.11（正则铅笔与完整有限量子层级）。** 对每个固定 $n\ge2$，在定义164.1的
同一个实际全有限背景内，以下条件等价：

1. 某个原三腿矩阵秩一种子含定义164.2的二元正则铅笔。
2. 存在 $M\notin\mathbb C I_n$，使 $r_Mr_M^*\in C_3$。
3. 命题164.10的明确 dyad $\tau_n\tau_n^*$ 属于原 $C_3$。
4. 对每个有限 $N\ge1$，$C_N=\operatorname{PSD}_{n^N}$，全部等式均在原实际坐标中。

**证明。** 1到2由单次相干控制滤波和输出左乘给出，全部预算见164.4；2显然给1。
由2先用164.4支付整个实际 qubit 控制族，再用164.5支付所需有限多项式。
非标量复矩阵要么有至少两个特征值，要么只有一个特征值；164.7、164.8分别供应
原可逆纠缠门及其所有旁观提升。164.9的既有精确尾部给4。
4在 $N=3$ 包含明确 PSD dyad $\tau_n\tau_n^*$，给3；3又以 $M=E_{10}$ 给2。
此外3直接由164.10的六副本门接164.9给4，独立展示该见证的完整有限预算。
所证是一个合格种子的存在性；并不要求每个给定 GME 向量本身具有正则切片。∎

### 原量子字典、几何与保留的缺口

**推论 164.12（完整静态字典及其操作边界）。** 在定理164.11的等价条件下，
对每个有限 $N$，同一原数据满足下列对应；这是 [VII，102.12—102.15及103.12][Q164VII]
在本章已得整锥等式后的复用。

| 原对象／量词 | 对应的有限复量子数据 | 来源与限度 |
| --- | --- | --- |
| $K_N$ 与凸混合 | $\rho\succeq0$、$\operatorname{Tr}\rho=1$，通常混态分解 | 凸准备为输入；全部 PSD 而非可生成子锥由164.9给出 |
| 全部原纯态 $P_N$ | 单位秩一投影，$\mathbb{CP}^{n^N-1}$ | 只在整锥等式之后识别原极点 |
| 全 proper 效应与有限菜单 | $0\preceq E\preceq I$；全部有限 POVM，含投影测量 | 原完整对偶及单位区间，不是选定探针 |
| 原配对与概率 | $\Pr(a\mid\rho)=\operatorname{Tr}(E_a\rho)$ | Born 式是既定实际配对的坐标表达 |
| 原复合、置换、丢弃 | 通常张量积、因子交换、偏迹及其所有有限复合 | 实际实张量结构为站立输入；整联合正锥现已确定 |
| least 确认与全部高阶比较 | $T_p^{(N)}(x)=\operatorname{Tr}(px)$；纯态间 $|\langle\psi,\phi\rangle|^2$，所有 $S_N$ | 复用 VII102.12 的 least 投影证明，未以 $S_3$ 作入口 |
| 原全旁观正 $F:W_m\to W_k$ | 通常矩形 CP 映射 $F(x)=\sum_\alpha K_\alpha xK_\alpha^*$ | 原自身 Choi 后接成熟 Choi／Kraus 表示；任意矩阵参考 CP 是结论 |
| 原不增迹／保迹预算 | $\sum_\alpha K_\alpha^*K_\alpha\preceq I$／$=I$ | 测试整个输入锥；不是只看 Choi 总迹 |
| 原数学可逆保迹控制 | 本文构造的所有全局酉共轭及其逆 | 每个目标有精确有限字；不指定资源协议确定性成功 |

**证明。** 态锥等式使非退化迹配对下的完整原对偶等于 PSD；单位上下界就是效应行。
PSD 的有限谱分解给纯态与混态对应；VII102.12的确认投影论证给 least 公式。
任意 $m,k$ 的原自身 Choi 现在是完整 $\operatorname{PSD}_{n^{m+k}}$；
VII102.13引用的 Watrous 定理2.22、2.26给有限矩形 Kraus 表达与逐输入预算。
这些结论从锥等式读取，不再调用带不同前提的三份重构定理。∎

若额外选择 VII102.14的事件饱和，全部 CP-TNI 分支和有限 CP 仪器才成为该菜单的可用事件。
仪器条件为 $\sum_{a,\alpha}K_{a,\alpha}^*K_{a,\alpha}=I$；归一输入的分支概率为
$p_a=\operatorname{Tr}(F_a\rho)$，且仅当 $p_a>0$ 时条件态 $F_a\rho/p_a$ 有定义。
一个给定效应仍不指定唯一更新，Lüders 更新是额外选择；有更新的测量次序仍可不交换。
所有酉共轭都已是数学保迹自同构，但静态数据不选物理钟、连续时间族、Hamiltonian、
时间尺度或 $\hbar$。选定可微酉时间族后的 Hamiltonian 描述不能反过来充当本章结论的输入。
复数矩阵载体、单块维数 $n$、已对齐低二层、凸准备、完整菜单和全有限实际复合都是输入；
本章确定剩余全部高阶锥，未从零导出这些站立输入。

**说明 164.13（简洁几何与任意 GME 缺口）。** 新种子的几何只需一条射影矩阵线
$\mathbb P(\mathcal L)\subset\mathbb P(M_n(\mathbb C))$，它不被行列式零超曲面包含。
选线上一个满秩点作 $I_n$，另一个独立方向作 $M$，便得到一个实际二元相干选择。
同时可逆左、右滤波和铅笔基变换保持“二维且含满秩点”；选定 $I_n$ 后，
保留它的两侧滤波实现相似变换。若重新选
$A'=aA+bB$ 为满秩点、$B'=cA+dB$，$ad-bc\ne0$，则

$$
M'=(aI+bM)^{-1}(cI+dM).
$$

只有 $aI+bM$ 可逆时这张局部图才适用；不声称任意基变换都保持指定首切片可逆，
也不声称有唯一、规范或与坐标无关的 $M$ 代表。
多项式网络把这一条线的相干控制转为其有限函数演算：谱分开就选幂等，谱不分开就取
最高非零幂零幂。两条路均保持原数据腿，不需要把 qubit 字串融合成一条原 $n$ 维腿。

正则入口比“指定种子必须 SLOCC 等价于 GHZ$_n$”更宽：GHZ$_n$ 的对角切片像含
$I_n$ 及一个独立投影，故满足入口；$n>2$ 的 $\tau_n$ 也满足入口，却因局部秩
$(n,n,2)$ 不在该类中。这里没有把这种放宽误写成 GHZ$_n$ 到 $\tau_n$ 的单副本滤波转换。

对 $n>2$ 的**任意** GME 矩阵秩一种子，163章只已支付完整二维压缩层级。
例如嵌入的 $|000\rangle+|111\rangle$ 是 GME，但所有切片的秩至多二，
所以该给定种子没有原 $n\times n$ 满秩切片。由任意这样的种子是否仍能推出存在另一正则种子，
或直接推出全部原层级，本章保持开放。正则切片是本定理的充分入口；没有证明它对每个
能完成重构的给定种子都必要。VII104.12—104.13及163.8的混合原编码接口仍可作为另一条
具名充分路线，不能由 qubit 内的 CP 操作直接替代；本章在正则子类中支付的是不同接口。
有限 ket 网络类、有限前缀或某类未能找到满秩切片的尝试，都不构成完整全有限反模型。

### 供应归属与原始来源

本章的项目增量是正则二元资源的上述存在性等价、串行数据线与完整实际 qubit 控制族之间的
相干多项式接口，以及将两个谱情形逐一接回原 Choi、全部旁观者和 proper 预算。
谱多项式、中国剩余定理、幂零与幂等的相似标准形是成熟线性代数；这里已给所需代数推导。
GHZ/W 分类、三 W 三角供应、完整 qubit retract、Choi／Kraus 表示、精确有限普适性与
既有原态—效应夹逼均各归原来源，不把其重复接合另算成新的文献定理。

| 精确供应 | 本章消费的内容 |
| --- | --- |
| VII 定义102.1、引理102.6—102.8 | 原全有限模型；整锥切片；自身 Choi、重复帽预算；局域操作全部原旁观提升 |
| VII 命题103.7、定理103.8 | 已付叉口到两 dyad 的 qubit 供应及其尾部；164.9仅复用纠缠门后的证明接口 |
| VII 引理102.10 | 异维旧块／新腿上的精确有限字归纳；非稠密近似 |
| VII 命题104.11、定义104.12及命题104.13 | 完整 qubit 正 retract 与全对偶；混合编码的准确边界 |
| 本卷第163章 163.2—163.4、163.6—163.8 | 滤波与 GHZ/W 三角预算；整个压缩族；尚未支付的一般维数编码边界 |
| VII 102.12—102.15、103.12 | 已得整锥后的量子字典、事件饱和、条件更新与时间限制 |

VII 只读供应源是 `docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md`，
来源固定为已发表提交 `657a8ba435bf2cae463e935d957d8038b69be8a3`。
163供应来自本卷已发表的第163章，具体消费 163.2—163.4、163.6—163.8 的原滤波、三体种子、二维压缩和预算接口；这些接口构成本章的数学前置。

原始文献：W. Dür、G. Vidal、J. I. Cirac，
[*Three qubits can be entangled in two inequivalent ways*][Q164DVC]，
Phys. Rev. A **62**, 062314 (2000)，DOI [10.1103/PhysRevA.62.062314](https://doi.org/10.1103/PhysRevA.62.062314)；
§III.1—III.2给三 qubit 局部秩边界与 GHZ/W 分类，附录A给可逆局部算子与 SLOCC 的关系。
本章经163的资源预算调用该分类，不将其推广成一般 $n$ 的完整 SLOCC 分类。
Aram W. Harrow，[*Exact universality from any entangling gate without inverses*][Q164H]，
arXiv:0806.0631v1 (2008)，推论2明确给 $U(d_A)\otimes U(d_B)$ 加一个 imprimitive 门的
精确有限生成，且不要求 $d_A=d_B$；本章不重新证明或重新归属这一结果。
John Watrous，*The Theory of Quantum Information* (2018)，定理2.22、2.26，
按 VII102.13的矩形 Choi／Kraus 供应复用。

[Q164VII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Q164DVC]: https://arxiv.org/abs/quant-ph/0005115v2
[Q164H]: https://arxiv.org/abs/0806.0631v1

Matthias Christandl、Fulvio Gesmundo、Jeroen Zuiddam，[*A Gap in the Subrank of Tensors*][Q164CGZ]，arXiv:2212.01668v2，§3 命题 3.1(i)(ii) 给出：在复数域的三因子情形，分割秩至少二（等价地，所有非平凡展平秩至少二）可作一个保持该性质的二维限制，并且一般限制也保持它。因此，163.5 所用的同时二维限制是成熟的精确特例；该结果本身不供应本章的原锥、完整对偶、旁观者继承或预算接口。

Eric Chitambar、Carl A. Miller、Yaoyun Shi，[*Matrix Pencils and Entanglement Classification*][Q164CMS]，arXiv:0911.1803v1，§3 式(3)—(6)及引理 2 给出成熟的矩阵铅笔字典：$2\otimes m\otimes n$ 纯态对应 $\mu R+\lambda S$，局部数据滤波按 $BRC^{\mathsf T}$、$BSC^{\mathsf T}$ 作用，控制腿的 $GL_2$ 变量改变铅笔参数；控制因子分离当且仅当铅笔两项标量成比例。该字典说明本章的正则铅笔几何，但不供应本章的全有限原锥、旁观者或预算桥。

[Q164CGZ]: https://arxiv.org/abs/2212.01668v2
[Q164CMS]: https://arxiv.org/abs/0911.1803v1

**完整中文图景。** 固定一份和两份的量子坐标后，只要原三腿里有一个真正相干的二选一：
一支是满秩的一一配对，另一支是与它不同的配对，就能把前者当作恒等矩阵，后者记作非标量 $M$。
先从这个种子截出二维纠缠，复用已有结果取得任意有限控制态；数据始终沿原来的 $n$ 维腿串行走，
控制只决定这条线上用了多少次 $M$，再以一次共同收缩把它们组合成所需多项式。
若 $M$ 的谱能分开，多项式就挑出一个非平凡投影，给出受控变号；若谱只有一点，最高非零幂留下
平方零偏移，三个剪切便在整个空间上合成纠缠酉。每一步都由原资源、原帽、有限正成功质量和
全部原旁观者上的正性支撑；既有精确有限字随后把任意有限份的全部态锥与效应锥锁成量子形式。
更一般的高维 GME 种子是否也总能越过满秩接口，仍然开放；这幅几何图景没有替它预付编码，
也没有从静态锥几何选出物理事件、更新规则或时间。
## 追加锚（本行以下为增补区）

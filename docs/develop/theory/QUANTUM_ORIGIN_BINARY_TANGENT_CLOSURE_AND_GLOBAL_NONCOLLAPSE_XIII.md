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

另一个开放入口是无全局维数上界的完整 EB3 加纯 PR 是否供应全局矩阵重建；这里 EB3 指每个**整个原** $D_p$ 是非退化闭三球，纯 PR 指 (XIII160.1) 的全部纯对数值互易。前卷 §159.7 已说明 EB3 自带 NC，而定理158.1在另加整个 $\dim_{\mathbb R}V\le9$ 时给出同原 qutrit 重建。无此上界的 EB3 + 纯 PR 到全局 MD（即同原归一化矩阵字典）的桥仍 open；本章没有从它们取得 L2、TC 或 L3，也不以定理160.7反驳该入口。该商不满足完整 EB3。若已由定理160.5取得表示，再另给 EB3，则 $D_{p_v}=\Phi\mathcal D(v^\perp)$ 的仿射维数迫使 $n=3$；这是重建后的秩判定，不能倒用成重建前的供应。

直观地说，每两个不同纯态先确定一颗完整三球，它的球面就是这两态之间全部可能的纯态。在另一纯态 $p$ 处，连接这颗球面上每个纯态所得到的小球，各有一个二维切方向。TC 只要求这些方向都由连接两个固定端点时得到的四维方向和容纳；加上 $p$ 的径向才是五维齐次空间，射影化后才是成熟帽定理所需的四空间。这个规则用的是球与球怎样接合，不必先给整个三态 qutrit，也不必先知道复数或全局纯态流形。分类把这些接合关系组织成同一个有限复矩阵商，原单位再选定正定尺度和共同的迹归一化。此时局部球仍可能全对，而全局混合已经被商掉：三对三平衡商中，正块三个纯态的平均与全秩均匀态是同一个原态，三个点因此生成全体；每个二元球的切方向却一点也没有被压缩。NC 所约束的正是另一件事：某纯态的全部真实零邻点不能经实际面生成把它自己包进去。159.10证明非零商核必在某纯态处造成这种塌缩；NC 因而排核。排核以后，同一个映射才恢复所有原混态、所有原效应、整个确认菜单与全部 Born minimum，而实际制备、复合、操作和时间仍需各自的物理合同。

### 160.8 数学归属、精确文献范围与供应总结

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

### 160.9 引用

**[SV160]** J. Schillewaert and H. Van Maldeghem, *Hermitian Veronesean Caps*, in *Buildings, Finite Geometries and Groups*, Springer Proceedings in Mathematics 10 (2012), 175–191. [作者原稿](https://cage.ugent.be/~hvm/artikels/204.pdf)，§2.3，原稿 pp. 3–4：ovoid、H1–H3、Theorem 2.4 及 Hermitian Veronesean 坐标；§3.3，pp. 10–11：一般指数的归约及有限环境排除无限指数。本章实际应用的外部分类型定理只有该 Theorem 2.4。

**[CTV160]** B. N. Cooperstein, J. A. Thas, and H. Van Maldeghem, *Hermitian Veroneseans over finite fields*, Forum Mathematicum 16 (2004), 365–381. [作者原稿](https://cage.ugent.be/~hvm/artikels/133.pdf)，§1，原稿 p. 5：不交椭圆空间及相关切四空间的中心所定义的 quotient，Theorems 1.3–1.4 的有限域范围；§6，pp. 18–19：投影重建。用于解释 [SV160] 的商含义，不将有限域分类直接移植到 $\mathbb R$。

**[R160]** *Quantum Origin: Exclusion Segment Rigidity and Pure Locus Topology XII*，第159章，仓内[前卷源码](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md)，[固定版本 d4a6bd75fd78850fed8cf60aebb6ce7fceffa2e1](https://github.com/the-omega-institute/trureturing/blob/d4a6bd75fd78850fed8cf60aebb6ce7fceffa2e1/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md)。定理159.1、159.3和命题159.4供应平衡商；引理159.5供应 L2 张成交集；引理159.6用于 L3 与 TC 的比较；命题159.7的分类后证明供应原单位归一化；引理159.8–159.9、定理159.10供应不使用 L3 的排核；定理159.12用于两套完整候选的比较，推论159.13用于闭包推理。以上均是纸面结果，不是新取得的 Lean 定理。

## 追加锚（本行以下为增补区）

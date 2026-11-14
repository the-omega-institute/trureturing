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

## 162. A fixed-local-space tensor quotient with all finite binary geometries and collapsing neighbor faces

**Definition 162.1 (one quotient and its entire tensor hierarchy).**
Fix an integer $m\ge3$, put $d=2m$, and equip the real space
$A=\operatorname{Herm}_d(\mathbb C)$ with the positive-definite real
pairing $\langle X,Y\rangle=\operatorname{Tr}(XY)$. Set

$$
H=\operatorname{diag}(I_m,-I_m),\qquad R=H^\perp\subset A,\qquad
V=A/\mathbb RH,\qquad \pi:A\longrightarrow V,\qquad
u(\pi X)=\operatorname{Tr}X.
\tag{162.1}
$$

Trace is well defined since $\operatorname{Tr}H=0$. For every finite
$N\ge1$, use the real tensor products and the definitions

$$
\begin{gathered}
D_N=d^N,\qquad A_N=\operatorname{Herm}_{D_N}(\mathbb C)
             =A^{\otimes_{\mathbb R}N},\qquad
W_N=V^{\otimes_{\mathbb R}N},\qquad \pi_N=\pi^{\otimes N},\\
C_N=\pi_N(\operatorname{PSD}_{D_N}),\qquad
u_N=u^{\otimes N},\qquad
K_N=\pi_N(\mathcal D_{D_N}),\qquad
\mathcal N_N=\ker\pi_N,\qquad R_N=R^{\otimes N}.
\end{gathered}
\tag{162.2}
$$

The tensor identification in (162.2) is the actual
Kronecker map on Hermitian matrices. Indeed tensor products of real
Hermitian bases are independent, and both spaces have real dimension
$d^{2N}=D_N^2$. Its pairing is exactly

$$
\operatorname{Tr}\bigl((X_1\otimes\cdots\otimes X_N)
 (Y_1\otimes\cdots\otimes Y_N)\bigr)
=\prod_{i=1}^N\operatorname{Tr}(X_iY_i).
\tag{162.3}
$$

Thus this is one fixed $V$ at every level, with its original tensor
products, dual products, units, evaluation, brackets and position
permutations. The cones are the whole displayed images, including the
images of every correlated density matrix. Each own effect menu is
$\mathcal E_N=[0,u_N]_{C_N^\ast}$; $P_N$, $\mathcal F_{N,p}$,
$T_{N,p}$, $p_N^\perp$ and $F_N$ have exactly the original meanings
in (161.4)–(161.6). No subset of effects is substituted for this menu.

**Theorem 162.2 (complete original background at every finite split).**
The data of Definition 162.1 satisfy all of (161.1)–(161.3), with the
actual original permutations and reassociation. Under dual pullback by
$\pi_N$ and the trace pairing, the full dual, effects, confirmers and
minimum on every original mixed input are exactly

$$
\begin{gathered}
W_N^\ast\simeq R_N,\qquad C_N^\ast\simeq R_N\cap\operatorname{PSD}_{D_N},
\qquad
\mathcal E_N\simeq R_N\cap[0,I_{D_N}],\\
f_E(\pi_NX)=\operatorname{Tr}(EX),\\
\mathcal F_{N,\pi_NP_v}\simeq
 \{E\in R_N:0\preceq E\preceq I_{D_N},\ Ev=v\},\\
T_{N,\pi_NP_v}(\pi_N\rho)
 =\min_{\substack{E\in R_N,\ 0\preceq E\preceq I_{D_N}\\Ev=v}}
      \operatorname{Tr}(E\rho),\qquad \rho\in\mathcal D_{D_N}.
\end{gathered}
\tag{162.4}
$$

The confirmer and minimum lines apply to any unit $v$ whose image is
pure; Theorem 162.4 below shows that this includes every unit $v$ and
exhausts $P_N$.

Proof. The orthogonal splitting $A=R\oplus\mathbb RH$ and the
isomorphism $\pi|_R:R\to V$ give

$$
\mathcal N_N
 =\sum_{i=1}^N A^{\otimes(i-1)}\otimes\mathbb RH
                      \otimes A^{\otimes(N-i)},\qquad
\mathcal N_N^\perp=R_N.
\tag{162.5}
$$

These identities use the tensor trace pairing (162.3); in particular
they are identities of the actual real spaces, not just of product
positive elements. The tensor map $\pi_N$ is surjective, and equality
of the trace and $u_N\pi_N$ on simple tensors proves
$u_N\pi_N=\operatorname{Tr}$ on all of $A_N$.

The image $K_N$ of the compact density set is compact, convex and
contained in $u_N=1$. Moreover $C_N=\mathbb R_{\ge0}K_N$, and a
positive lift of a nonzero element has strictly positive trace. Thus
$u_N$ is strictly positive on $C_N\setminus\{0\}$, and
$C_N\cap\{u_N=1\}=K_N$. For a convergent sequence $t_jk_j$ in this
cone, $t_j=u_N(t_jk_j)$ converges. Compactness of $K_N$ proves that
the limit is in the cone, including when $t_j\to0$. Hence $C_N$ is
closed. Strict positivity excludes a nonzero element of both $C_N$
and $-C_N$. Finally PSD spans $A_N$, so surjectivity makes $C_N$
generating. This verifies the complete single-level background at each
$N$.

A real functional descends exactly when its trace matrix annihilates
$\mathcal N_N$, giving $W_N^\ast\simeq R_N$. It is positive on the
whole image cone exactly when $\operatorname{Tr}(EX)\ge0$ for every
$X\succeq0$, equivalently $E\succeq0$ by testing rank-one $X$.
The matrix of $u_N$ is $I_{D_N}\in R_N$, since $I_d\in R$.
Applying positivity also to $u_N-f_E$ gives the effect interval in
(162.4). For a positive contraction, $v^\astEv=1$ is equivalent to
$Ev=v$, because $v^\ast(I-E)v=0$ forces $(I-E)^{1/2}v=0$.
This proves the confirmer and minimum formulas. All evaluations are
independent of the positive lift by (162.5). The matrix interval is
compact and the confirmer set contains $I_{D_N}$, so every minimum
exists. No affine formula for this lower envelope is assumed.

Now fix any split $a+b=N$. Arbitrary $x\in C_a,y\in C_b$ have
positive lifts $X\in A_a,Y\in A_b$. Their tensor $X\otimes Y$ is
positive and maps to the actual $x\otimes y$, proving
$C_a\otimes_{\min}C_b\subseteq C_N$. Conversely any positive
functionals on the two whole block cones have matrices
$E\in R_a\cap\operatorname{PSD}_{D_a}$ and
$G\in R_b\cap\operatorname{PSD}_{D_b}$. For every positive lift
$Z\in A_N$, including every correlated one,

$$
(f_E\otimes f_G)(\pi_N Z)=\operatorname{Tr}((E\otimes G)Z)\ge0.
\tag{162.6}
$$

The last inequality follows by taking the trace of
$Z^{1/2}(E\otimes G)Z^{1/2}\succeq0$. This proves the maximum
bound with $C_a,C_b$ themselves at every split. It also proves the
positivity of every product of original positive effects; product
normalized effects and their complements have the usual unit bound.

For a position permutation $s$, let $U_s$ be the quantum unitary
which actually permutes those tensor factors, and let $S_s$ permute
the factors of $W_N$. Equality on simple tensors, followed by spanning,
gives

$$
S_s\pi_N(X)=\pi_N(U_sXU_s^\ast).
\tag{162.7}
$$

Conjugation preserves PSD, so $S_s$ and $S_s^{-1}$ are positive on
the entire original cone. The same tensor identities show that
reassociation is the actual canonical identity, in every grouping.
Equation (162.3) gives exact evaluation on products; product linear
functionals separate $W_N$ by finite-dimensional tensor duality.
One can also use product effects for separation: every Hermitian
$E\in R_a$ lies between $-cI$ and $cI$ for some $c>0$, so the
own effect interval spans $R_a$, and similarly at every block.
Discarding agrees with the quotient of the matrix partial trace,

$$
(\operatorname{id}_{W_a}\otimes u_b)\pi_{a+b}Z
 =\pi_a(\operatorname{Tr}_{\mathbb C^{D_b}}Z),
\tag{162.8}
$$

as follows first on simple tensors and then on all $Z$. It is therefore
positive on every correlated input. All asserted products, pairings,
units, permutations and brackets are the original ones. ∎

**Theorem 162.3 (sharp tensor-kernel inertia at every finite level).**
For every finite $N\ge1$ and every nonzero $X\in\mathcal N_N$,

$$
n_+(X)\ge m,\qquad n_-(X)\ge m,
\tag{162.9}
$$

where $n_\pm$ count strictly positive and strictly negative eigenvalues
with multiplicity. Both bounds are attained at every level.

Proof. First the real span of the projectors $P_v$ with
$\|v\|=1$ and $v^\astHv=0$ is exactly $R$. For a direct proof of the
nontrivial inclusion, let $B\in A$ annihilate all such projectors.
Write it in $m$-by-$m$ blocks for the two eigenspaces of $H$.
For arbitrary unit vectors $a,b\in\mathbb C^m$, the vectors
$(a,e^{it}b)/\sqrt2$ are isotropic. Their expectations give

$$
a^\astB_{++}a+b^\astB_{--}b
       +2\operatorname{Re}(e^{it}a^\astB_{+-}b)=0
             \qquad(t\in\mathbb R).
\tag{162.10}
$$

Varying $t$ forces $B_{+-}=0$. The remaining equality for all $a,b$
forces $B_{++}=cI_m$ and $B_{--}=-cI_m$, by Hermitian polarization.
Thus this span has annihilator exactly $\mathbb RH$, proving the
claim. Denote the set of these unit isotropic vectors by $\mathcal I$.

Suppose $X\in\mathcal N_N$ and $n_+(X)\le m-1$. For an arbitrary
subset of slots $S\subseteq\{1,\ldots,N\}$, insert a prescribed
$v_j\in\mathcal I$ in each slot $j\notin S$. This defines an
isometry

$$
J_{S,\mathbf v}:\bigotimes_{i\in S}\mathbb C^d
   \longrightarrow (\mathbb C^d)^{\otimes N},\qquad
X_{S,\mathbf v}=J_{S,\mathbf v}^\astXJ_{S,\mathbf v},
\tag{162.11}
$$

where retained slots are in their original relative order. For
$S=\varnothing$ this compression is a scalar; for all slots it is
$X$. A positive subspace for a compression maps isometrically to a
positive subspace for $X$. Consequently

$$
n_+(X_{S,\mathbf v})\le n_+(X)\le m-1.
\tag{162.12}
$$

We prove by induction on $k=|S|$, simultaneously for every subset of
that size and every complementary isotropic product, that
$X_{S,\mathbf v}=0$. For $k=0$, (162.5) and (162.3) give

$$
X_{\varnothing,\mathbf v}
 =\operatorname{Tr}\bigl(X(P_{v_1}\otimes\cdots\otimes P_{v_N})\bigr)
 =0,
\tag{162.13}
$$

because the product of these isotropic projectors is in $R_N$.

For the induction step take any $S$ of size $k\ge1$, fix its
complementary vectors, and write $Y=X_{S,\mathbf v}$. Compressing
any one retained slot $i\in S$ by any $v\in\mathcal I$ gives a
compression with retained slots $S\setminus\{i\}$, hence the zero
operator by induction. Pairing that zero operator with every Hermitian
matrix on the other retained slots says

$$
\operatorname{Tr}(Y(P_v\otimes B))=0
       \qquad(v\in\mathcal I,\ B\text{ any Hermitian matrix on the other slots}),
\tag{162.14}
$$

with factors placed in their actual slots. The spanning result above
and the tensor trace pairing imply that $Y$ belongs to
$\mathbb RH$ in slot $i$, tensored with arbitrary Hermitian factors
in all other slots. This holds for every $i\in S$. Intersecting these
subspaces, or expanding in a basis adapted to $A=R\oplus\mathbb RH$,
gives

$$
Y=tH^{\otimes k}\qquad(t\in\mathbb R).
\tag{162.15}
$$

If $t\ne0$, this matrix has exactly $d^k/2$ eigenvalues of each sign.
Indeed each factor has $m$ signs of each kind, and changing one factor's
sign pairs the two parity classes of tensor eigenvectors. Since
$d^k/2\ge m$ for $k\ge1$, this contradicts (162.12). Hence $Y=0$,
completing the induction for arbitrary subsets. Taking all slots gives
$X=0$. Thus a nonzero kernel matrix has $n_+(X)\ge m$; applying the
same argument to $-X$ gives the negative bound.

For sharpness, at every $N$ the nonzero matrix
$H\otimes P_e^{\otimes(N-1)}$ belongs to (162.5), for any unit
$e\in\mathbb C^d$, and has $m$ eigenvalues of each sign; at $N=1$
this means $H$. ∎

**Theorem 162.4 (unique positive lifts, all pure states, and actual small support faces).**
For every $N\ge1$, any $\sigma\succeq0$ of rank at most $m-1$
is the unique positive lift of $\pi_N\sigma$. For every complex
subspace $S\subseteq\mathbb C^{D_N}$ of dimension at most $m-1$,
$\pi_N\mathcal D(S)$ is an actual face of $K_N$, and

$$
\pi_N^{-1}(\pi_N\mathcal D(S))\cap\mathcal D_{D_N}=\mathcal D(S).
\tag{162.16}
$$

The restriction of $\pi_N$ to $\operatorname{Herm}(S)$ is a
trace-preserving linear order isomorphism onto the span of that face
cone. Its state restriction is an affine isomorphism. All the original
pure points are exactly the distinct images $p_v=\pi_NP_v$, and

$$
\mathbb{CP}^{D_N-1}\longrightarrow P_N,\qquad [v]\longmapsto p_v
\tag{162.17}
$$

is a homeomorphism. For any finite family of unit vectors with
$S=\operatorname{span}_{\mathbb C}\{v_1,\ldots,v_k\}$ of dimension
at most $m-1$,

$$
F_N(p_{v_1},\ldots,p_{v_k})=\pi_N\mathcal D(S).
\tag{162.18}
$$

The empty family gives the empty face. The vectors in these statements
are arbitrary, including vectors entangled across the original slots.

Proof. If $\rho\succeq0$ is another lift of $\pi_N\sigma$, put
$X=\rho-\sigma\in\mathcal N_N$. On $\ker\sigma$ its quadratic
form is nonnegative. A negative spectral subspace of dimension larger
than $\operatorname{rank}\sigma$ would intersect $\ker\sigma$
nontrivially, which is impossible. Thus
$n_-(X)\le\operatorname{rank}\sigma\le m-1$, and (162.9) forces
$X=0$. This is the elementary sign-rank comparison underlying the
mature low-rank-versus-all-state criterion [CHST162, §4.1, Lemma 1(c),
Lemma 2(a), Theorem 1(a)]; that general criterion is background, not a
new state-determination theorem here. Its tensor-kernel premise has
been proved in Theorem 162.3.

Let $r=\dim S\le m-1$. Every Hermitian matrix supported on $S$
has at most $r$ positive and at most $r$ negative eigenvalues; (162.9)
therefore makes $\pi_N$ injective on $\operatorname{Herm}(S)$.
For $\sigma\in\mathcal D(S)$ and an original convex decomposition
$\pi_N\sigma=tx+(1-t)y$, $0<t<1$, choose density lifts
$\alpha,\beta$ of $x,y$. Their mixture is a positive lift of
$\pi_N\sigma$, so uniqueness gives
$\sigma=t\alpha+(1-t)\beta$. For $z\in S^\perp$, positivity and
$z^\ast\sigma z=0$ force $\alpha z=\beta z=0$; hence both lifts are
supported on $S$. This proves the actual face property and (162.16).

The image of $\operatorname{PSD}(S)$ is exactly the cone of this
face. To check order also on its entire real span, suppose
$Y\in\operatorname{Herm}(S)$ and $\pi_NY=\pi_N\rho$ for some
$\rho\succeq0$. Choose $\eta\in\mathcal D(S)$ positive definite
on $S$ and $c>0$ large enough that $c\eta+Y\succeq0$. This matrix
has rank at most $r$ and shares its image with $c\eta+\rho\succeq0$.
Uniqueness gives $Y=\rho\succeq0$. Together with injectivity and
trace preservation this proves the full order-isomorphism assertion.
The zero subspace has zero cone span and empty normalized face, so is
covered separately without choosing $\eta$.

In particular every rank-one image is a singleton actual face and
hence pure. Distinct rank-one projectors have distinct images by unique
positive lifting. Conversely, a density lift of an arbitrary original
extreme point has a finite spectral decomposition. Its image is a
convex combination of these rank-one images, so extremality makes
it one of them. This proves exhaustion. The continuous map (162.17)
is therefore a bijection from compact complex projective space to the
pure set in a finite-dimensional Hausdorff space; it is a homeomorphism.

For a nonempty family in (162.18), its equally weighted lifted mixture
is positive definite on $S$. The standard matrix support-face rule,
recalled in §159.1, says that the lifted projectors generate exactly
$\mathcal D(S)$. The image set is an actual face, so the minimal
original face is contained in it. Pulling that minimal face back by the
affine isomorphism gives a face of $\mathcal D(S)$ containing all
these projectors, hence all of $\mathcal D(S)$. This proves equality,
not merely containment in a convex copy. ∎

**Theorem 162.5 (all-level L2 and TC, and every fixed finite geometric face budget).**
For $m\ge3$, L2 and TC of §161.1 hold on the whole $K_N$ for
every finite $N\ge1$. For $m\ge4$, L3 of Definition 160.2 also
holds at every level. More generally, for any fixed integer $r\ge1$,
choosing $m\ge\max\{3,r+1\}$ ensures that at every finite level
every face generated by at most $r$ pure points is the full intrinsic
complex density face on their lifted vector span. These assertions
concern actual state-face geometry with the original unit.

Proof. Fix $N$ and suppress its index on $\pi_N$ temporarily.
Two distinct pure points have distinct lifted lines spanning a complex
two-space $S$, so (162.18) identifies their entire actual face with
$\mathcal D(S)$. The usual Pauli parametrization identifies this
space with the full closed Euclidean three-ball, proving L2.
All its extreme points are precisely the images of the unit vectors
in $S$, by the affine isomorphism and the global pure injectivity.

For TC take arbitrary $a=p_\alpha,b=p_\beta,p=p_v$ with $a\ne b$
and $p\notin B_N(a,b)$. Put $S=\operatorname{span}_{\mathbb C}
\{\alpha,\beta\}$. Equation (162.16) gives the exact external-point
condition $v\notin S$. Consequently

$$
Q_v=I-P_v,\qquad U=Q_vS=v^\perp\cap
\operatorname{span}_{\mathbb C}\{v,\alpha,\beta\}
\tag{162.19}
$$

has complex dimension two, with basis $z_\alpha=Q_v\alpha$,
$z_\beta=Q_v\beta$. For $z\perp v$, the normalized rank-one curve
and its derivative are

$$
\gamma_z(t)=\frac{(v+tz)(v+tz)^\ast}{1+t^2\|z\|^2},\qquad
\gamma_z'(0)=\Theta_v(z)=vz^\ast+zv^\ast.
\tag{162.20}
$$

For every unit $w\in S$, its actual binary ball with $p_v$ is
$\pi\mathcal D(\operatorname{span}\{v,w\})$. Differentiating its
rank-one boundary through the affine isomorphism gives its entire
intrinsic tangent direction,

$$
\tau_{N,p_v}(p_w)=\pi\Theta_v(\mathbb C Q_vw).
\tag{162.21}
$$

The map $\Theta_v$ is real linear; complex coefficients on a line
are carried by the two real directions $\Theta_v(z)$ and
$\Theta_v(iz)$. Since $Q_vw\in U$, (162.21) implies

$$
\tau_{N,p_v}(p_w)\subseteq\pi\Theta_v(U)
 =\tau_{N,p_v}(a)+\tau_{N,p_v}(b),
\tag{162.22}
$$

for every original pure point of $B_N(a,b)$. This is exactly TC with
all its quantifiers, for arbitrary correlated lifted vectors.

For completeness these are the noncollapsed tangent spaces themselves.
If $z\ne0$ and $z\perp v$, then $\Theta_v(z)$ has eigenvalues
$\|z\|,-\|z\|$ and zeros, by restricting to
$\operatorname{span}\{v,z\}$. Thus it has sign ranks $(1,1)$ and
cannot belong to $\mathcal N_N$ by (162.9). Also
$\Theta_v(z)v=z$, so $\Theta_v$ is injective. Therefore each single
tangent direction has real dimension two and the endpoint sum
$\pi\Theta_v(U)$ has dimension four. On
$\mathbb RP_v\oplus\Theta_v(U)$, taking trace first kills the
coefficient of $P_v$ for a kernel element, and the same inertia
argument kills the remaining direction. The homogeneous space has
real dimension five and is injectively mapped, just as required by
the original affine tangency convention. This is a derivative on actual
binary faces, without assuming a global differential structure on $P_N$.

If $m\ge4$, a triple outside every binary face must have three
independent lifted lines: a dependent triple would lie in the actual
support-two face already proved. Its support-three density face is
actual by Theorem 162.4 and is a full qutrit, proving L3. For the general
budget, at most $r$ lifted lines span dimension at most $r\le m-1$,
so (162.18) proves the assertion simultaneously at every $N$. ∎

The small-face assertions identify intrinsic positive cones, normalized
state spaces and their intrinsic affine effect intervals. They do not
assert that restriction of $R_N\cap[0,I_{D_N}]$ is onto such an
intrinsic interval at the same unit budget. Formula (162.4), including
the condition $E\in R_N$, remains the full original menu. In
particular the geometric budget theorem does not cover arbitrary tests
of restricted original effects, and it gives no formula for all-level
pure minima or pure PR. The single-level pure-minimum calculation of
Theorem 159.1 is not used to replace any higher-level menu.

**Theorem 162.6 (a finite original-neighbor mixture collapses the actual face at every level).**
For every $m\ge3$ and every $N\ge1$, let
$v_0=e_1^{\otimes N}$ and $p=\pi_NP_{v_0}$. Then

$$
F_N(p_N^\perp)=K_N.
\tag{162.23}
$$

In particular both NC and the proper-neighbor-face condition fail at
this pure point at every finite level, including $N=3$.

Proof. Use the standard tensor coordinate basis of $\mathbb C^{D_N}$.
For any coordinate vector
$w=e_{j_1}\otimes\cdots\otimes e_{j_N}\ne v_0$, choose a slot $\ell$ with $j_\ell\ne1$. Choose an index
$k$ of the opposite $H$ sign from $j_\ell$, with $k\ne1$.
There is such an index: each sign block has $m\ge3$ entries, so
excluding index 1 still leaves an opposite-sign choice when needed.
On this local slot set

$$
A_w=P_{e_{j_\ell}}+P_{e_k},\qquad
E_w=I_d^{\otimes(\ell-1)}\otimes A_w
                    \otimes I_d^{\otimes(N-\ell)}.
\tag{162.24}
$$

The two local projectors are distinct and orthogonal, so
$0\preceq A_w\preceq I_d$,
$\operatorname{Tr}(HA_w)=0$, $A_we_1=0$, and
$A_we_{j_\ell}=e_{j_\ell}$. Since $I_d\in R$, it follows that

$$
E_w\in R_N\cap[0,I_{D_N}],\qquad
E_wv_0=0,\qquad E_ww=w.
\tag{162.25}
$$

Thus every $q_w=\pi_NP_w$ is an original pure zero neighbor of
$p$: the original effect $I_{D_N}-E_w$ confirms $p$ and vanishes
at $q_w$. Its complement confirms $q_w$ and vanishes at $p$.
All these witnesses belong to the same full original menu (162.4) at
this level. They are allowed to vary with $w$; no common confirmer
or simultaneous measurement has been assumed.

Write $D=D_N$. The equally weighted mixture of these $D-1$ neighbors
has the density lift

$$
x=\frac1{D-1}\sum_{w\ne v_0}q_w=\pi_N\rho,\qquad
\rho=\frac{I_D-P_{v_0}}{D-1}.
\tag{162.26}
$$

Take the actual tensor-kernel direction

$$
Z=H\otimes P_{e_1}^{\otimes(N-1)}\in\mathcal N_N.
\tag{162.27}
$$

It has trace zero. For $0<t<1/(D-1)$ the diagonal matrix $\rho+tZ$
is positive definite: its formerly missing $v_0$ entry is $t>0$;
all other entries in the slice with slots $2,\ldots,N$ equal to
$e_1$ are $1/(D-1)+t$ or $1/(D-1)-t$, both positive; all
untouched entries are $1/(D-1)>0$. At $N=1$ the slice is the
whole coordinate basis and the same calculation applies. Its trace
is one and $\pi_N(\rho+tZ)=x$.

The restriction of $\pi_N$ from the trace-one affine hyperplane
onto $\{u_N=1\}$ is a surjective affine map, hence open. A positive
definite density has a neighborhood in that hyperplane contained in
the density set. Its image therefore belongs to $\operatorname{ri}K_N$.
Thus $x\in\operatorname{ri}K_N$. Any actual face containing the
neighbors contains their finite mixture $x$ and hence all of $K_N$:
for any $y\in K_N$, relative interior lets $x$ be an open-segment
point between $y$ and another point of $K_N$, and the face property
then includes $y$. This proves (162.23) directly using only original
effects and an explicit interior lift. ∎

**Theorem 162.7 (NC cannot be deleted from the three-copy candidate in the full finite background).**
In the unchanged original domain (161.1)–(161.3), the condition
that $K_3$ satisfy L2 and TC does not imply the proper-neighbor-face
condition or NC. Even requiring L2 and TC at every finite level does
not imply either condition at level 3, or at every level. For every
fixed finite geometric face budget $r$, there is one fixed-local-space
hierarchy satisfying that budget at every level while (162.23) holds
at every level.

Proof. Take the hierarchy of Definition 162.1. Theorem 162.2 supplies
the whole all-finite background; Theorems 162.4–162.5 supply the
actual faces and L2/TC, and Theorem 162.6 contradicts the desired
neighbor-face conclusion. For budget $r$, choose
$m\ge\max\{3,r+1\}$ once, before choosing $N$, and use this same
$V$ at all levels.

There is also a direct carrier obstruction to a full complex matrix
cone at level 3:

$$
\dim_{\mathbb R}V=4m^2-1,\qquad
\dim_{\mathbb R}W_3=(4m^2-1)^3.
\tag{162.28}
$$

Since $(2m-1)^2<4m^2-1<(2m)^2$, the local dimension is not a
square. Its cube is not a square either: if an integer cube is a
square, parity of prime exponents makes the integer itself a square.
A full complex Hermitian matrix cone has square real dimension. At
$m=3$, the dimensions are exactly $35$ and $35^3=42875$.
Consequently this whole $C_3$ is not linearly order isomorphic to
any full complex matrix cone. The actual-neighbor-face obstruction
(162.23) gives the explicit geometric failure in addition to this
dimension obstruction. ∎

The mathematical picture is that a quotient can leave every sufficiently
small support face intact while identifying mixtures of many different
pure points. 中文图景：把原态体看成由许多纯端点围成的整块凸体，每两端点之间的
完整三球及其切向接合都能原样保留，甚至任意预先规定数目的端点所生成的小面都
能保留；但固定一个端点后，全部能用原尺与它完全区分的邻点，仍可混成凸体内部的
一点。一张实际面只要含这个内部点，就不得不吞下整块凸体，也吞下原端点。
这里每一有限份数使用同一个局部商的张量幂，所有原尺、相关态、分组、交换和
重括号同时存在；缺失的是全局邻点面不塌缩这一关系，而非局部小球或其切方向。

The complete candidate $\mathsf G_3$ of §161.1 remains
L2 + TC + proper neighbor face; its existing correspondence in Theorem
161.5 and §161.10 retains exactly its stated suppliers and hypotheses.
The countermodel excludes the attempted deletion of its third clause;
it does not furnish a further reconstruction or a minimum independent
axiom set. The finite face-budget assertion is intrinsic state geometry,
not an assertion about unrestricted face-effect extensions. No
all-level pure PR or whole EB3 property is a conclusion here, and the
bare whole-EB3 + pure-PR reconstruction question of §160.7 remains
outside this countermodel. The construction supplies mathematical
ordered cones and their complete dual menus; physical realization,
available instruments and calibrated dynamics are additional questions.

The new mathematical assertion is the joint all-finite construction
with its tensor-kernel bound, actual-face range and direct original
neighbor mixtures. The one-copy balanced quotient and its one-copy
pure minima already occur in Theorem 159.1; its TC specialization is
Theorem 160.7. The tensor sign-rank premise is proved here rather than
assumed from those one-copy statements. The general low-rank/inertia
criterion is mature background, attributed to [CHST162] and the existing
[literature note](../../../Library/HilbertOperators/carmeliheinosaarischultztoigo2014tasks.md).
The construction and its geometric combination are `repo-derived`;
this describes the derivation and asserts no historical priority for
the tensor inertia argument or the construction. No Hermitian-cap classification,
conditional reconstruction supplier or propagation theorem is a premise
of Theorems 162.2–162.7.

[CHST162]: https://arxiv.org/pdf/1308.5502v2 "C. Carmeli, T. Heinosaari, J. Schultz and A. Toigo, Tasks and premises in quantum state determination, J. Phys. A 47 (2014), 075302; §4.1, Lemmas 1–2 and Theorem 1(a), DOI 10.1088/1751-8113/47/7/075302."

## 追加锚（本行以下为增补区）

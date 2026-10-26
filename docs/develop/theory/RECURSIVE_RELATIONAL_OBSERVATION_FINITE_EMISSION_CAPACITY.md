# 已知当前边界上的有限发射容量、精确计数与恢复平台

本篇研究一个实际已达到、坐标已知的当前边界：只观察此后有限次完整调用的 Emit 位，究竟有多少种可达到的观察，哪些未读尾仍不可区分，以及这些分割何时恰好等于原始尾的定长前缀分割。实质结论是全部分裂的显式取整时序、容量的闭式逆计数及一致斜率误差，以及精确恢复时域上的双向分割等式和平台长度。柱纤维与历史乘积是既有结果在这一观察限制下的应用。

以下均为声明模型内未执行的符号数学推导，采用普通条件证明；没有新增 Lean、kernel、数值实验或物理实现认证。

## 1. 已有模型、实际切口与供给

直接使用 [《当前边界的完整续行正规形与有限观察逆》](RECURSIVE_RELATIONAL_OBSERVATION_EXACT_CURRENT_BOUNDARY_PROVENANCE.md)（简称正规形卷）与 [Paid Zeckendorf observation at a current return](RECURSIVE_RELATIONAL_OBSERVATION_PAID_ZECKENDORF_CURRENT_RETURN.md)（简称 paid-return 卷）的明确接口。

所有时间、调用数及位置下标均为非负整数，原始位从低到高排列。设

$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,
\qquad
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\ (j\ge0)\}.
\tag{1}
$$

$Z(n)$ 表示有限 Zeckendorf 展开并向高位补零，$q_m(x)$ 表示前 $m$ 个原始位，$f(x)=x_0$。$T$ 是端点含入的算术 successor：在第一个相邻 $00$ 的首位置写一并清零更低位，保留更高位；若没有 $00$，则送到 $Z(0)$。特别地，两条纯交替字也在定义域内。$T$ 不是位置删除。

完整块字及其值为

$$
\mathcal B=\{0,10\}^{<\omega},\qquad
P_d=\{p\in\mathcal B:|p|=d\},\qquad
N_p=\sum_{j<|p|}G_jp_j,\qquad C_p=pK.
\tag{2}
$$

每个非空完整块字以零结束，所以其后可接任意 $t\in K$。空字的柱为 $K$。既有时钟为

$$
M_p=G_{|p|+1}-N_p,\qquad k_p=M_p-2,
\qquad b_\varnothing=0,\qquad
b_{p0}=b_{p10}=M_p-1.
\tag{3}
$$

paid-return 卷第2–3节的 producer 从源无关的空记录、时间零及真实顺序端点初始化。初始确认不做 Read 或 Advance。每个达到的返回 $(p,n)$ 满足 $b_p\le n\le k_p$，真实已读字为 $p$，原始游标为 $|p|$，当前点为 $T^nx$。每个 $x\in C_p$ 都实际到达这个柱寿命中的每个返回。

一次 Next 在 $n<k_p$ 时不读，在 $n=k_p$ 时读取下一块：零分支真正读一位，一分支真正读一和其后的强制零。随后用新前缀 $p'$ 计算 $\operatorname{Low}(N_{p'}+n)=f(Z(N_{p'}+n))$，依次真正 Emit、Advance、Return。只有 Advance 改变源时间；等待、查询与暂停没有自主推进。每个达到的 Read 按合同有限完成，所有算术、输入输出均付费。返回时 scratch 与待发输出为空。既有定理给出每段有限运行的生产性和同一真实未读尾的精确续行。

对 $d\ge1$，既有完整块值域与寿命恒等式是

$$
P_d\ \longleftrightarrow\ \{0,\ldots,G_{d-1}-1\},\qquad
p\longmapsto N_p,
\qquad b_p+N_p=G_d-1,\qquad k_p+N_p=G_{d+1}-2.
\tag{4}
$$

固定实际达到的 proper 当前边界，参数为

$$
d\ge1,\quad 0\le\delta\le G_{d-1}-1,\quad
A=G_{d+1}-2-\delta,\quad p\in P_d,\quad r=A-N_p.
\tag{5}
$$

这些条件包含真实可达性：

$$
r-b_p=G_{d-1}-1-\delta\ge0,\qquad k_p-r=\delta\ge0.
\tag{6}
$$

故每个真实源 $pt$，$t\in K$，都从固定初始化到达切口 $(p,r)$，此时未读尾恰为 $t$。当前边界为带端点所有权的 $\partial(d,A)$，其完整当前点集合记为 $U$。正规形卷第2、6节已经给出

$$
Q(t)=T^A(0^dt)=T^{A-N_p}(pt),\qquad Q:K\longrightarrow U\text{ 为双射},
\tag{7}
$$

以及原始来源／时间历史的精确参数化

$$
(p',t)\longmapsto(p't,A-N_{p'}),\qquad (p',t)\in P_d\times K.
\tag{8}
$$

每个参数都是真正到达的历史。同尾的不同 $p'$ 在匹配切口后有相同实际发射字及相同相对原始取得过程。这是全位点结论，包含墙上实际拥有的侧点，并非仅有相位相等。

本篇还直接使用正规形卷第7节的精确首差：若不同尾的最长共同完整块前缀为 $w$，$e=|w|$，则其未来发射首次不同的零起下标为

$$
G_{d+e+1}-2-A-V_d(w),\qquad
V_d(w)=\sum_{j<e}G_{d+j}w_j.
\tag{9}
$$

其后两块为 $0$ 与 $10$，后续可接任意合法尾。这个结论适用于同一实际历史，也适用于不同 $p'$ 的匹配历史。它是下面柱纤维论证的既有供给。

初始空前沿 $d=0$ 单独具有 $p=\varnothing,r=0$、当前集合 $K$ 和恒等尾坐标；不将下述 proper 边界公式用于它，不出现负下标的 $G$。

## 2. 观察限制与精确柱纤维

**定义2.1（有限发射观察）。** 已知固定的 $(d,\delta)$，在式(5)的真实切口以后完成恰好 $h$ 次 Next。记其 $h$ 个 Emit 位为

$$
\widehat v_h(y)=\bigl(f(T^iy)\bigr)_{0\le i<h},\quad v_h(t)=\widehat v_h(Q(t)),\qquad
\mathcal O_h=\{v_h(t):t\in K\},\qquad C_h(d,\delta)=|\mathcal O_h|.
\tag{10}
$$

$\widehat v_h$ 用于完整当前点，$v_h$ 用于原切口未读尾。相对调用位置从此切口起算，Emit、Advance、Return 的固定顺序已知。每次都等待三事件完成；不主张在 Emit 与随后的 Advance、Return 之间提前取得本篇的已完成调用答案。$h=0$ 时观察字为空，仍是一个达到的观察字。

客户端初态除共同参数外不含任何与源相关的旧记忆。观察不含原始回复、Read 数、绝对计数、旧事件、历史前缀、当前内部深度、私有 $N,M,k$、身份／描述符／权利标识、计算费用或时间延迟，也不含 Wall、Extent、Peek 等额外读数。producer 仍执行全部真实 Read 和 Advance。这是对数学观察者使用信息的限制，不安装新的过滤服务，不删去内部字段或原有能力，也不凭数字创造调用权。

**定义2.2（分裂调用与前沿）。** 对 $w\in\mathcal B$，$e=|w|$，置

$$
\tau(w)=G_{d+e+1}-1-A-V_d(w),\qquad
\beta(\varnothing)=0,\qquad
\beta(w0)=\beta(w10)=\tau(w),
\tag{11}
$$

以及

$$
\mathcal F_h=\{w\in\mathcal B:\beta(w)\le h<\tau(w)\}.
\tag{12}
$$

$\tau(w)$ 是从一开始的调用序号，其 Emit 首次分开 $w0K$ 与 $w10K$；零起发射下标是 $\tau(w)-1$。子字在该调用的 Return 已出生，父字此时退出前沿。

**定理2.3（达到观察的完整纤维）。** $\mathcal O_h$ 与 $\mathcal F_h$ 一一对应。与 $w\in\mathcal F_h$ 对应的观察纤维恰为 $wK$；这 $h$ 次实际调用恰好物理读过未读尾的完整字 $w$。每个前沿字及其任意合法完成均实际可达。特别地，

$$
\mathcal F_h=\{\varnothing\},\quad C_h=1\quad(0\le h\le\delta),
\qquad \mathcal F_{\delta+1}=\{0,10\},\quad C_{\delta+1}=2.
\tag{13}
$$

**证明。** 一个实际扩展 $pw$ 的死亡时钟是

$$
k_{pw}=G_{d+e+1}-2-N_p-V_d(w).
$$

它读取下一块的调用号为 $k_{pw}+1-r=\tau(w)$。该调用完成后两个可能孩子均处于各自出生返回。直接使用权重递推可得

$$
\tau(w0)-\tau(w)=G_{d+e}>0,\qquad
\tau(w10)-\tau(w)=G_{d+e+1}>0.
\tag{14}
$$

因此沿每条实际路径，祖先分裂严格先于后代分裂；一个调用不会在该路径连续取得两个块。一个返回字的生存条件正是式(12)。实际运行在有限 $h$ 内取得有限个完整块，故给出某个这样的 $w$。

固定一条在返回 $h$ 取得 $w$ 的实际尾 $t$。任取 $u\in wK$，它与 $t$ 在这些调用所读的全部原始位置相同。producer 的 guard、有限算术、块取得、Emit 和返回更新均确定，且未查看 $w$ 后的任何位。对调用归纳，$u$ 实际执行同样读取及事件三元组，并且取得同一个 $w$。于是 $wK$ 包含于该观察的纤维。这也说明物理取得的 $10$ 包含其第二零；不能把它换成一个未读的承诺位。

反过来，若 $u\notin wK$，则它与 $t$ 的首个原始差别发生在 $w$ 结束以前。该位置不可能是一个共同 $10$ 的第二位置，因为前一共同的一强制双方该位均为零。所以首差在一个真完整前缀 $z$ 后的块起点。运行要取得 $w$，必已在第 $\tau(z)\le h$ 次调用完成这个块的分裂。式(9)使两条真实尾在恰好此调用的 Emit 不同，任意后续完成均不能改变这一首差。因此 $u$ 不在同一观察纤维中。若 $w$ 为空，第一包含已经给出整个 $K$，不需要第二包含的非空情形。

还须证明式(12)中的每个候选是真实前沿，而非形式缓存。给定这样的 $w$ 和任意 $u\in K$，实际源 $pwu$ 由式(6)先到达原切口。沿 $w$ 的块解析，每个祖先有有限的死亡时钟和有限的下一次 Read；生产性保证它们真正完成。式(14)将这些祖先调用依次放在 $\beta(w)$ 以前或恰当时。于是实际在 $\beta(w)$ 得到 $w$，并在 $h<\tau(w)$ 以前不读取下一块。空字从原切口开始。故整个 $wK$ 均达到所称状态。

不同前沿字不能有真前缀关系，否则前缀已分裂而不能仍在前沿。它们的首个不同块由式(9)给不同观察。以上证明覆盖全部真实运行及全部候选，得到所称双射。最后 $\tau(\varnothing)=\delta+1$，两孩子的分裂又严格更晚，故得式(13)。这项柱结论是既有精确首差和实际运行定理的应用。$\square$

## 3. 有限值、移位权重与内部反射引理

本节为求值全部分裂时序建立所需的有限算术桥，不假定或打开任何 Beatty、Sturmian、旋转分割或外部间距定理。

设

$$
\alpha=\frac{\sqrt5-1}{2},\qquad \phi=\alpha^{-1}=1+\alpha,
\qquad F_0=0,\quad F_1=1,\quad F_{n+2}=F_{n+1}+F_n.
\tag{15}
$$

$F_n$ 是普通 Fibonacci 数，不是供给卷中同字母的带符号级数函数。有

$$
0<\alpha<1,\quad \alpha^2=1-\alpha,\quad \phi+\alpha=\sqrt5,
\qquad G_i=F_{i+2}.
\tag{16}
$$

$\sqrt5$ 无理：若既约正有理数 $u/v$ 的平方为五，则 $u^2=5v^2$ 迫使五整除 $u$，再迫使五整除 $v$，矛盾。故 $\phi$ 及每个正整数倍 $q\phi$ 都无理。

**引理3.1（有限合法值域）。** 长度 $L$ 的合法 no11 字，其 $G$ 权重值恰好各取一次整数 $0,\ldots,G_L-1$。因此长度 $e\ge1$ 的完整块字的值恰好各取一次 $0,\ldots,G_{e-1}-1$。

**证明。** $L=0$ 只有空字，值为零；$L=1$ 的两个值为零、一。对 $L\ge2$，最高位为零时由归纳取遍 $[0,G_{L-1}-1]$。最高位为一时次高位必须为零，其余低 $L-2$ 位由归纳取遍 $[0,G_{L-2}-1]$，所以总值取遍

$$
[G_{L-1},G_{L-1}+G_{L-2}-1]=[G_{L-1},G_L-1].
$$

两区间相邻且不交，每个内部值也唯一，证明归纳结论。非空完整块字恰是合法且最后一位为零的字：从低位遇零取块 $0$，遇一则由 no11 取其后的零组成 $10$；末位零保证不会留下一个悬空的一。因此去掉最后零后，值域正是长度 $e-1$ 的合法值域。$\square$

令

$$
a=F_d,\qquad b=F_{d-1}.
$$

检查首值并应用递推给出

$$
\begin{aligned}
\phi G_i-G_{i+1}&=-(-\alpha)^{i+2},\\
G_{d+i}&=aG_{i+1}+bG_i,\\
a\phi+b&=\phi^d,\qquad a+b=G_{d-1},\qquad 2a+b=G_d,\\
F_n&=\frac{\phi^n-(-\alpha)^n}{\sqrt5}.
\end{aligned}
\tag{17}
$$

这里第一式的两边随 $i$ 都满足 Fibonacci 递推，首两值相等；第二式在 $d=1,2$ 成立，随 $d$ 同样递推；第三行由前两个普通 Fibonacci 首值及递推得到；最后式的两根 $\phi,-\alpha$ 均满足 $z^2=z+1$，且给出 $F_0=0,F_1=1$，故其首值和递推唯一性证明该式。这些都是符号恒等式。

**引理3.2（有限字的移位值）。** 对有限合法字的值 $n$，令 $S(n)$ 为把每个权重 $G_i$ 换成 $G_{i+1}$ 所得的值。它由引理3.1的唯一展开良定义，并满足

$$
S(n)=\lfloor\phi(n+1)\rfloor-1,\qquad
V_d(w)=aS(N_w)+bN_w.
\tag{18}
$$

**证明。** 将式(17)第一式逐位相加，得

$$
\phi n-S(n)=\sum_i(-1)^{i+1}\alpha^{i+2}w_i.
$$

所有负的偶位置项即使全取，也只到
$-\alpha^2/(1-\alpha^2)=-\alpha$；所有正的奇位置项即使全取，也只到
$\alpha^3/(1-\alpha^2)=\alpha^2$。有限字不达到这两个无限极值，所以

$$
-\alpha<\phi n-S(n)<\alpha^2.
$$

故整数 $S(n)$ 位于开区间

$$
(\phi n-\alpha^2,\phi n+\alpha)
=(\phi(n+1)-2,\phi(n+1)-1).
$$

两端无理、间距为一，其中唯一整数是 $\lfloor\phi(n+1)\rfloor-1$，证明第一式。式(17)第二式逐位相加证明第二式，包括空字 $n=0,S(0)=0$。$\square$

**引理3.3（有限预算的严格分离）。** 对 $e\ge1$、整数 $1\le q\le G_{e-1}$，以及任意整数 $u$，有

$$
|u-q\phi|>\alpha^{e+3}.
\tag{19}
$$

**证明。** 写 $\varepsilon=\alpha^{e+3}<1$。反设 $|u-q\phi|\le\varepsilon$。代数范数

$$
(u-q\phi)(u+q\alpha)=u^2-uq-q^2
$$

是非零整数；为零将使 $u/q$ 等于无理根 $\phi$ 或 $-\alpha$。又

$$
|u+q\alpha|\le |u-q\phi|+q(\phi+\alpha)
\le\varepsilon+\sqrt5q.
$$

因此该范数的绝对值严格小于

$$
\begin{aligned}
\varepsilon(\sqrt5G_{e-1}+1)
&=\alpha^2-(-1)^{e+1}\alpha^{2e+4}+\alpha^{e+3}\\
&\le\alpha^2+\alpha^6+\alpha^4\\
&<\frac{\alpha^2}{1-\alpha^2}=\alpha<1.
\end{aligned}
$$

第一等号由式(17)的 $G_{e-1}=F_{e+1}$ 得到。第二行使用 $e\ge1$；第三行把三项与同一正几何级数的前三项及其严格正余项比较。非零整数的绝对值不可能小于一，矛盾。于是式(19)成立，且对最近整数的左右两侧都是严格分离。$\square$

**引理3.4（有限反射）。** 对非空完整字 $w$，令 $e=|w|$、$n=N_w$、$M=G_{e+1}$、$q=n+1$ 及 $k=M-q$。则

$$
\lfloor q\phi\rfloor+\lfloor k\phi\rfloor=G_{e+2}-1,
\qquad G_{e+2}-S(n)=\lfloor k\phi\rfloor+2,
\qquad G_{e+1}-n=k+1.
\tag{20}
$$

**证明。** 引理3.1给 $1\le q\le G_{e-1}$。记 $H=G_{e+2}$、$\varepsilon=\alpha^{e+3}$、$\ell=\lfloor q\phi\rfloor$、$t=\{q\phi\}$。式(19)对上下两个邻近整数都适用，所以
$\varepsilon<t<1-\varepsilon$。式(17)给

$$
M\phi=H-(-\alpha)^{e+3}.
$$

若 $e$ 偶，则 $M\phi=H+\varepsilon$，从而
$k\phi=H-\ell+(\varepsilon-t)$，括号严格处于 $(-1,0)$。
若 $e$ 奇，则 $M\phi=H-\varepsilon$，从而
$k\phi=H-\ell-(\varepsilon+t)$，其中 $0<\varepsilon+t<1$。
两种情形均有 $\lfloor k\phi\rfloor=H-\ell-1$，证明第一式。引理3.2的 $S(n)=\ell-1$ 给第二式，$k=M-(n+1)$ 给第三式。空字不调用本引理，在下面直接处理。$\square$

## 4. 全部分裂的显式时间表

**定义4.1（全局节点索引）。** 置

$$
I(\varnothing)=1,\qquad
I(w)=G_{e+1}-1-N_w\quad(e=|w|\ge1),
\qquad E=A+1-G_d=G_{d-1}-1-\delta.
\tag{21}
$$

特别地，$a\ge1,b\ge0,E\ge0$。

**定理4.2（求值后的严格时序）。** 每个整数 $k\ge1$ 恰对应一个完整字 $w(k)$，其中 $I(w(k))=k$。这些字的分裂调用按 $k$ 严格递增，且

$$
\boxed{\ \tau_k=\tau(w(k))=a\lfloor k\phi\rfloor+bk-E\ }.
\tag{22}
$$

首调用为 $\tau_1=\delta+1$。相邻分裂的间隔恰取两种正长度

$$
G_{d-1},\qquad G_d,
\tag{23}
$$

没有同时分裂。前 $k-1$ 个间隔中的长间隔数恰为 $\lfloor k\alpha\rfloor$；两种间隔都无限出现。

**证明。** 对固定长度 $e\ge1$，引理3.1表明式(21)中的 $I(w)$ 恰各取一次区间

$$
G_e\le I(w)\le G_{e+1}-1.
$$

这些区间首尾相接，空字补上整数一，故节点与正整数双射。更明确地，$w(1)=\varnothing$；对 $k\ge2$，选唯一满足 $G_e\le k<G_{e+1}$ 的 $e\ge1$，取
$n=G_{e+1}-1-k$，令 $w(k)$ 为补零至 $e$ 位的 $Z(n)$。其最后位为零，因而是完整字。这是符号参数化，不需要枚举某个实例。

对非空 $w=w(k)$，引理3.2、3.4与式(17)给

$$
\begin{aligned}
G_{d+e+1}-V_d(w)
&=a\bigl(G_{e+2}-S(n)\bigr)+b\bigl(G_{e+1}-n\bigr)\\
&=a\lfloor k\phi\rfloor+bk+2a+b\\
&=a\lfloor k\phi\rfloor+bk+G_d.
\end{aligned}
$$

减去 $A+1$ 即式(22)。空字单独有 $\lfloor\phi\rfloor=1$，故右边是
$a+b-E=G_{d-1}-E=\delta+1=\tau(\varnothing)$，同式成立，不使用负长度或负下标。

因 $1<\phi<2$，连续取整增量是一或二，所以

$$
\tau_{k+1}-\tau_k\in\{a+b,2a+b\}=\{G_{d-1},G_d\}.
$$

即使 $d=1,b=0$，两长度仍为正。因此该时序严格递增且无界：索引顺序就是全部节点的真实分裂先后顺序，没有碰撞，每个有限调用阈值以前只有有限次全局分裂。这也与式(14)的祖先顺序一致。

最后 $\lfloor k\phi\rfloor=k+\lfloor k\alpha\rfloor$ 且 $\lfloor\alpha\rfloor=0$，所以

$$
\tau_k-\tau_1=(k-1)(a+b)+a\lfloor k\alpha\rfloor.
\tag{24}
$$

每个长间隔比短间隔多 $a>0$，故长间隔数如所称。若从某处起只剩短间隔，则 $\lfloor k\alpha\rfloor$ 从此不变，其比值趋于零；若只剩长间隔，则该比值趋于一。两者都与
$\lfloor k\alpha\rfloor/k\to\alpha\in(0,1)$ 矛盾，故两种都无限出现。$\square$

## 5. 容量的闭式逆计数与一致斜率

对任意整数 $h\ge0$，定义

$$
Y=h+E,\qquad z=\alpha^dY,\qquad j=\lfloor z\rfloor,\qquad k=j+1,
$$

以及明确的一次比较

$$
\eta_h=
\begin{cases}
1,&a\lfloor k\phi\rfloor+bk\le Y,\\
0,&a\lfloor k\phi\rfloor+bk>Y.
\end{cases}
\tag{25}
$$

**定理5.1（闭式容量）。** 全部完成分裂的数目为 $J_h=j+\eta_h$，并有

$$
\boxed{\ C_h(d,\delta)=\lfloor\alpha^d(h+E)\rfloor+1+\eta_h\ }.
\tag{26}
$$

这只含两次明确的取整和一次整数比较，不含未知纤维数、无限树求和或待解计数递推。整个原始前沿也有有限参数式

$$
\mathcal F_h=
\left(\{\varnothing\}\cup
\{w(k)0,w(k)10:1\le k\le J_h\}\right)
\setminus\{w(k):1\le k\le J_h\}.
\tag{27}
$$

**证明。** 写 $L(k)=a\lfloor k\phi\rfloor+bk$。式(17)给

$$
L(k)=\phi^dk-a\{k\phi\}.
\tag{28}
$$

由 $F_1=1\le\phi^0$、$F_2=1\le\phi$ 及 Fibonacci 递推归纳，有
$F_d\le\phi^{d-1}$。因此

$$
0<\zeta:=a\alpha^d\le\alpha<1.
\tag{29}
$$

每个整数 $1\le k\le j=\lfloor z\rfloor$ 都满足
$L(k)\le\phi^dk\le Y$，所以已经分裂。反过来，若 $L(k)\le Y$，则

$$
k\le z+\zeta\{k\phi\}<z+\zeta<z+1.
\tag{30}
$$

因此 $k\ge j+2$ 不可能已经分裂。只有 $k=j+1$ 尚未决定，而式(25)恰好决定这一项，包括等号上的真实分裂返回。严格递增时序使已分裂节点正是 $1,\ldots,J_h$，于是 $J_h=j+\eta_h$。

由祖先调用严格更早，这有限集合构成一棵向祖先封闭的二叉子树。初始只有一个前沿字；每次分裂删去一个叶子、加入两个孩子，故 $J_h$ 次分裂后有 $J_h+1$ 个叶子。定理2.3将它们与达到观察双射，得到式(26)。这里一次全局分裂就是一个观察类分成两个；定理4.2已经排除同调用碰撞，不能额外加入未发生的类。

式(27)列出初始根与所有已分裂节点的孩子，再删去已经分裂的节点。每个非根节点有唯一父亲，祖先封闭性保证没有缺失的出生，所以该集合恰为前沿。等价地，非空完整字 $w$ 在前沿，当且仅当
$I(\operatorname{parent}(w))\le J_h<I(w)$；$J_h=0$ 时只有空字。$\square$

**定理5.2（一致斜率及绝对误差）。** 对全部允许的 $d,\delta,h$，

$$
0<C_h-\alpha^d(h+E)<1+\zeta\le1+\alpha,
\qquad
0<C_h-\alpha^dh<2+\alpha.
\tag{31}
$$

特别地，容量在这些参数上一致满足

$$
C_h=\alpha^dh+O(1)=\Theta(1+\alpha^dh),
\tag{32}
$$

且对固定 $d,\delta$，$C_h/h\to\alpha^d$。

**证明。** 上一证明给 $J_h\ge\lfloor z\rfloor$，因此
$C_h=J_h+1>z$。若 $J_h\ge1$，将最大已分裂索引代入式(30)，得 $J_h<z+\zeta$；若 $J_h=0$，因 $z\ge0,\zeta>0$，同一严格不等式仍成立。于是

$$
0<C_h-z<1+\zeta,\qquad
\lfloor z\rfloor+1\le C_h\le\lfloor z\rfloor+2.
$$

又

$$
0\le E\le a+b-1<a\phi+b=\phi^d,
$$

所以 $0\le\alpha^dE<1$。相加即式(31)，其中常数与三个参数均无关。令 $x=\alpha^dh$，则 $C_h\ge1$ 且 $C_h>x$，从而

$$
\frac{1+x}{2}\le C_h<(2+\alpha)(1+x),
$$

这给出一致的 $\Theta$。对固定 $d,\delta$，式(31)的有界误差除以正整数 $h$ 趋于零，得到斜率极限。这里的斜率只涉及有限观察类的基数，不涉及概率或熵。$\square$

**端点核对。** $h=0$ 时 $0\le\alpha^dE<1$，故 $j=0,k=1$；而
$L(1)=a+b=G_{d-1}>E$，所以 $\eta_0=0,C_0=1$，对应空观察字。更一般地，$0\le h\le\delta$ 时
$Y\le G_{d-1}-1<L(1)$，无节点分裂；$h=\delta+1$ 时恰有根在等号处完成分裂。$\delta=0$ 因而在第一次完整调用分裂。$d=1$ 时 $a=1,b=0$、允许的 $\delta=0$，所有证明仍用正的 $G_0,G_1$，没有除以 $b$ 或引用负下标。

式(14)表明根分裂以后，最早孩子分裂在
$\delta+1+G_d$，因为两孩子增量为 $G_d,G_{d+1}$。$G_d\ge2$，所以在 $h=\delta+2$ 容量仍为二。分裂既非每次调用发生，也非每条尾每次均取得一位；最初两个纤维本来就分别为 $0K$ 和 $10K$。

## 6. 恢复时域上的双向分割与精确平台

正规形卷已经证明统一恢复前 $m$ 个原始尾位的锐长度

$$
B_m=G_{d+m}-1-A\quad(m\ge1).
\tag{33}
$$

以下加强为分割的双向相等，并求出此后的首个平台。为此必须排除更深柱在 $B_m$ 以前过早分裂，单有可恢复性不足以推出这项结论。

**引理6.1（合法移位值的严格最大值）。** 令 $U_\ell$ 为长度 $\ell$ 的合法 no11 字在移位权重 $G_d,G_{d+1},\ldots$ 下的最大值。则

$$
U_\ell=
\begin{cases}
G_{d+\ell}-G_d,&\ell\text{ 偶},\\
G_{d+\ell}-G_{d-1},&\ell\text{ 奇}.
\end{cases}
\tag{34}
$$

最高位、隔一位、再隔一位取一给出唯一最大字。对完整块字长度 $s\ge1$，置

$$
c_s=\begin{cases}G_{d-1},&s\text{ 偶},\\G_d,&s\text{ 奇},\end{cases}
$$

则

$$
\max_{|w|=s,\ w\in\mathcal B}V_d(w)=G_{d+s-1}-c_s,
\qquad
\min_{|w|=s,\ w\in\mathcal B}\tau(w)=G_{d+s}+c_s-1-A.
\tag{35}
$$

**证明。** $U_0=0,U_1=G_d$，满足式(34)，最大字唯一。对 $\ell\ge2$，归纳公式给
$U_{\ell-1}<G_{d+\ell-1}$，因为被减去的 $G_d$ 或 $G_{d-1}$ 严格为正。于是最高位为零的任意值，都严格小于仅取最高位一的值。最大字必须取这个一，并令相邻下一位为零；其余低位再取唯一最大字。故

$$
U_\ell=G_{d+\ell-1}+U_{\ell-2}.
$$

这样同时证明高位比较、唯一性与交替形状，未预设一个未经证明的贪心顺序。具体求和由
$G_{i+2}-G_i=G_{i+1}$ 望远镜相消：对 $\ell=2q$，

$$
\sum_{i=0}^{q-1}G_{d+2i+1}
=\sum_{i=0}^{q-1}(G_{d+2i+2}-G_{d+2i})
=G_{d+2q}-G_d;
$$

$q=0$ 时为空和。对 $\ell=2q+1$，

$$
\sum_{i=0}^{q}G_{d+2i}
=\sum_{i=0}^{q}(G_{d+2i+1}-G_{d+2i-1})
=G_{d+2q+1}-G_{d-1}.
$$

这里最小下标为 $d-1\ge0$。这给式(34)，其值也严格小于 $G_{d+\ell}$，封闭上述归纳。

完整字的最后一位为零，所以其最大移位值是 $U_{s-1}$，最大字在位置 $s-2,s-4,\ldots$ 取一；$s=1$ 时就是零字。代入式(34)即式(35)第一式。再代入式(11)，使用
$G_{d+s+1}-G_{d+s-1}=G_{d+s}$，得到第二式。两个奇偶常数均严格为正。$\square$

**定理6.2（精确恢复分割）。** 对每个 $m\ge1$ 以及任意 $t,u\in K$，

$$
\boxed{\quad v_{B_m}(t)=v_{B_m}(u)
\quad\Longleftrightarrow\quad q_m(t)=q_m(u),\qquad C_{B_m}=G_m.\quad}
\tag{36}
$$

更强地，式(36)中的等价分割在全部整数

$$
B_m\le h<B_m+c_m
\tag{37}
$$

保持不变，因此该区间 $C_h=G_m$；在下一端点

$$
C_{B_m+c_m}=G_m+1.
\tag{38}
$$

**证明。** 由 $A\le G_{d+1}-2$ 及 $m\ge1$，式(33)给 $B_m\ge1$。令 $W_m$ 为最后一个块首次覆盖位置 $m-1$ 的完整字集合。一个合法长度 $m$ 前缀若以零结束，本身属于 $W_m$；若以一结束，追加其强制零后属于 $W_m$。反过来这给出 $W_m$ 的全部字，分别长 $m$ 或 $m+1$。所以 $W_m$ 的柱已经把 $K$ 分割为精确的 $q_m$ 纤维；长 $m+1$ 的情形没有额外的选择位。

对 $w\in W_m$，其父字长度 $e<m$。非负移位值及 $G$ 的递增性给

$$
\beta(w)=\tau(\operatorname{parent}(w))
\le G_{d+e+1}-1-A\le B_m.
\tag{39}
$$

另一方面，$s=|w|\ge m$，引理6.1给

$$
\tau(w)\ge G_{d+s}+c_s-1-A>B_m,
\tag{40}
$$

最后严格性来自 $G_{d+s}\ge G_{d+m}$ 和 $c_s>0$。因此 $W_m\subseteq\mathcal F_{B_m}$。这些柱已覆盖整个 $K$，而前沿柱彼此不交并且非空，所以不可能有其他前沿字。于是
$\mathcal F_{B_m}=W_m$：所有目标块均已读完，但没有任何目标块之后的块提前取得。此论证显式排除了深柱过早分裂。

若两个尾 $q_m$ 相同，它们属于同一个 $W_m$ 柱，由定理2.3其观察相同。若观察相同，定理2.3又将它们放在同一个 $W_m$ 柱，所以 $q_m$ 相同。这证明双向等价。引理3.1也证明合法长度 $m$ 字的个数为 $G_m$，故得到容量等式。

还须求精确的下一次分裂。在长度 $m$ 的前沿字中，式(35)的唯一交替最大字给最早调用

$$
G_{d+m}+c_m-1-A=B_m+c_m.
$$

每个长度 $m$ 的完整字都在 $W_m$，所以这个极值确实由当前前沿达到，而非由别处的字达到。在长度 $m+1$ 的前沿字中，即使对全部该长度完整字放宽，式(35)仍给下界

$$
G_{d+m+1}+c_{m+1}-1-A
=B_m+G_{d+m-1}+c_{m+1}.
\tag{41}
$$

它严格大于 $B_m+c_m$：若 $m$ 偶，则 $c_{m+1}=G_d>G_{d-1}=c_m$；若 $m$ 奇，则
$G_{d+m-1}\ge G_d=c_m$，再加正的 $c_{m+1}=G_{d-1}$ 即严格大于。故此前没有一个前沿字分裂。没有父分裂也不会产生新的后代分裂，整个分割遂在式(37)不变。恰在 $B_m+c_m$，该长度 $m$ 的最大字实际分裂；定理4.2排除同时碰撞，故只增加一个观察类，得到式(38)。$\square$

为核对既有锐长度，取同一实际历史的两条合法尾

$$
t=0^\infty,\qquad u=0^{m-1}10\,0^\infty.
\tag{42}
$$

它们 $q_m$ 不同，共同完整前缀为 $0^{m-1}$，移位值为零。式(9)给其首差调用恰为
$G_{d+m}-1-A=B_m$，所以前 $B_m-1$ 次完成调用不能统一恢复 $q_m$。式(6)保证两者都是真实可达源。$m=1$ 时共同字为空，$B_1=\delta+1$，所有等号仍成立。这一锐性和逐尾最早停止已由正规形卷给出；本节新增的是双向分割及精确平台，不另将旧停止最优性计为新结果。

## 7. 原切口当前点与历史乘积的条件化

**定理7.1（观察后的原始历史纤维）。** 固定一个达到观察 $o\in\mathcal O_h$，令其前沿字为 $w$。与 $o$ 相容的原切口当前点集合恰为

$$
\{y\in U:\widehat v_h(y)=o\}=Q[wK].
\tag{43}
$$

其全部原初始化来源／时间历史恰为

$$
\mathcal H_o=
\{(p'wu,A-N_{p'}):p'\in P_d,\ u\in K\}
\simeq P_d\times Q[wK].
\tag{44}
$$

每个固定完整点仍有恰好 $G_{d-1}$ 个原历史；有限观察没有选择实际来源。

**证明。** 定理2.3使观察在尾坐标中的精确纤维为 $wK$。式(7)既满又单，所以它把该纤维恰好送到式(43)：每个 $wu$ 给出真实当前点，反过来每个相容点的唯一尾也必须在 $wK$，两包含均成立。

对式(44)的正包含，任取 $p'\in P_d,u\in K$，源 $p'wu$ 合法；式(6)保证其真正到达 $A-N_{p'}$。既有同尾实际续行使它和参考历史有同一个 $h$ 位观察 $o$，故属于 $\mathcal H_o$。这不是把不同实现各自的极值拼接：每个 $p'$ 都在同一尾 $wu$ 上实际执行。

对反包含，任取原边界的真实历史且观察为 $o$。既有完整分类式(8)迫使它为 $(p't,A-N_{p'})$，其中 $p'\in P_d$、$t\in K$ 是它自己的真实尾。同尾匹配给该尾的观察就是 $v_h(t)$，定理2.3遂迫使 $t\in wK$。故没有其他原历史。乘积的显式双射为

$$
(p',y)\longmapsto(p'Q^{-1}(y),A-N_{p'}),\qquad
p'\in P_d,\ y\in Q[wK].
$$

其逆从真实来源取前 $d$ 位，再取其原切口完整当前点；式(7)和固定长度分解保证两者互逆。这正是既有历史乘积在观察纤维上的限制。

对固定 $y\in Q[wK]$，$Q$ 的单射性给唯一 $t_y$。每个 $p'$ 给一条且仅一条历史，故有 $|P_d|=G_{d-1}$ 条，原返回数仍恰为
$A-G_{d-1}+1,\ldots,A$。不同 $p'$ 给不同原始前缀及返回数。与此同时，$wK$ 含 $w0^\infty$、$w10\,0^\infty$ 和任意远处孤立一的不同完成，$Q$ 将它们送到不同完整点。因此有限 $o$ 不给完整点，更不认证真实 $p'$。$\square$

**命题7.2（推进后仍须保留原实验的条件）。** 令

$$
e=|w|,\qquad D=d+e,\qquad A_h=A+h+V_d(w),\qquad
\delta_h=G_{D+1}-2-A_h.
\tag{45}
$$

则 $0\le\delta_h\le G_{D-1}-1$，并且

$$
T^hQ[wK]=U(\partial(D,A_h)),\qquad
T^hQ(wu)=Q_{D,\delta_h}(u)\quad(u\in K).
\tag{46}
$$

条件化于原边界和 $o$ 后，每个固定推进点的原历史因子仍是 $G_{d-1}$，不能替换为后边界单独分类的 $G_{D-1}$。

**证明。** 对任意原 $p'$，实际返回 $h$ 的前缀是 $p'w$、时间是 $A-N_{p'}+h$，所以其内禀和为

$$
N_{p'w}+A-N_{p'}+h=A+h+V_d(w)=A_h.
$$

这是一个真实达到的深度 $D$ 返回。由式(4)，
$G_D-1\le A_h\le G_{D+1}-2$，故式(45)的余量范围成立。既有同尾逐点正规形用于这个真实后切口，逐个 $u$ 给出式(46)第二式；其后切口 $Q_{D,\delta_h}$ 对整个 $K$ 双射，给第一式，包括全部端点所有权。

特别地，固定推进点唯一决定其真实剩余尾 $u$。在原实验中，它的全部相容推进历史恰为

$$
\{(p'wu,A-N_{p'}+h):p'\in P_d\}.
$$

每项由原历史的正包含真正推进而来，反过来任意条件化推进历史也必须由式(44)中的历史推进。因此仍恰有 $G_{d-1}$ 项。这里使用后切口的限制单射及尾双射，未消去全局非单射的 $T$。

若丢弃原边界及观察条件，只问后边界自己的全部可能历史，则既有分类允许全部 $P_D$，因子为 $G_{D-1}$。$w$ 空时两者相同，$w$ 非空时 $D>d$，后一因子更大。这些额外历史不属于原实验，不能加入条件化纤维。实际采样后的源是 $T^hQ(t)$；输出原切口信息不使源退回 $Q(t)$。$\square$

## 8. 成本、既有能力与结论范围

在前沿纤维 $wK$ 上，按
$(\operatorname{Read},\text{原始交付位数},\operatorname{Next},\operatorname{Emit},\operatorname{Advance},\text{初始化后 Return})$
排列，切口后的精确逻辑操作向量为

$$
(|w|,|w|,h,h,h,h).
\tag{47}
$$

证明是定理2.3的实际取得与每个 Next 的固定三事件相加：每个新原始位恰读一次，零分支一读，$10$ 分支二读；其余调用不读。初始确认有独立费用，不混入后续 Return 数。式(47)是同一真实运行的计数，Read 数不是观察者新增的回复字段。由 Emit 推断强制零不免去 producer 对该零的物理读取。

$C_h$ 只数允许观察中的达到类，不数响应表位数，不是 Shannon 熵、分布风险、算术工作、源生成费用、位存储、延迟或 ML／NN 质量。全局分裂时序不是每条源的读取表；某一调用可只在其他尾的观察类上分裂。闭式可求值不等于已执行求值，亦不提供新的求值复杂度最优性。有限 Fibonacci、幂、取整、比较、Low、解码与缓存运算在实际实现中都付费。

程序及参考约定安装、原始端点与通道绑定、持续调用权及描述符检查、先前边界取得、源的实际供给 $\iota_x$、生成交付 $\gamma_x$、后端存储 $\sigma_x$、驱动者计算、服务配置与误差机制、scratch 分配／扫描／清空、请求扫描与完整 framing、所有字面输入输出、拒绝、DATA 实体化、导出、归档与保留，都保持供给卷的各自费用。producer、receiver、同时存在的数字服务和后端存储必须同时相加，不能用各自峰值替代联合实际存储。不同数值和描述符可导致不同位工作、输出长度与延迟；逻辑操作向量相等不把这些费用判等。每个达到调用有限结束也不意味着统一物理时限、无限输入的有限生成成本或无界继续调用的常数存储。

paid-return 卷第13–15节已给校准、有序、同源暂停 Wall 的付费取得和守卫内使用；第16–21节已给无相位读数、未知固定正有理单位下的 Extent／实际 Step 主动取得。其两次更新之间的完整寿命恢复接入及实际达到边界，至多四个新原始位的结论是已有正面供给。第18–19节已有跨零余量的 LiveStep、有限新任务 Seek、当前 guard 内的读数以及同次资源费用。这些能力存在于各自明示扩展合同中，本篇既不安装它们，也不将它们描述为缺失或新的发射容量成果。

本篇以已持有的 $(d,\delta)$ 为条件，既有取得方法的所有动作、读取、回复、安装和权限费用均保留。若先用主动取得达到一个新切口，则可在那个切口重新以 $h=0$ 开始本篇的观察问题；回溯恢复更早边界不回滚来源。若客户端还使用取得过程中保留的源相关旧信息、额外 Extent／Wall 回复或私有字段，就已经改变观察条件，不能套用只含此后 $h$ 位 Emit 的纤维断言。

边界统一 DATA 的原有守卫仍是

$$
D(L,H)\le\delta,\qquad
D(L,H)=\begin{cases}H,&L=0,\\H+G_L-1,&L\ge1.\end{cases}
$$

有限后续观察会真实推进来源，不扩大原暂停点的立即无读回答域。有限观察类、有限尾前缀、完整当前点、原始历史与持有调用权是不同对象。$Q^{-1}$、式(44)的乘积及任意可能历史选择都不供应尾 getter、源导出、认证历史选择器、rewind、物理前缀改写或权利复制／转移。既有 NativeAcquiredPrefix 使用不同控制器，本文没有把它转成这个 successor，也没有提供一般四表示互逆或无限有效逆。

所有首差、柱与端点结论均在整个 $K$ 上使用：纯交替、最终交替、有限核尾及墙上具体侧点都保留。证明只解析用到的有限块，不搜索一条无限交替字不存在的首个 $00$。原切口包含 $r=b_p$ 与 $r=k_p$；前沿在 $h=\beta(w)$ 包含孩子，在 $h=\tau(w)$ 排除已分裂父字，故没有丢失出生或死亡等号。

额外原始接口、计时通道、独立物理传感器、噪声／标定桥、非 Advance 源变动、并发或撤权、变化单位以及虚假来源承诺均需独立条件。这里没有所有接口上的下界、概率模型、平均性能、物理本体、文献穷尽或世界优先主张。本文相对于所给数学供给的新增内容集中于式(22)的求值时序、式(26)的闭式计数、式(31)的一致斜率误差及式(36)–(38)的双向分割和精确平台；精确首差、柱限制、尾双射、历史乘积与旧锐恢复长度按其原范围复用。

## 追加锚（本行以下为增补区）

## 9. A uniform pathwise reading band and logarithmic distinguishability

**Definition 9.1 (three counts on the same continuation).** Fix an attained proper boundary with the parameters $d,\delta$ of (5), and use exactly the Emit-only observation (10). For $h\ge0$ and each original unread tail $t\in K$, let $R_h(t)$ count the actual new raw Read operations in those $h$ complete Next calls, including forced zeros. If $w\in\mathcal F_h$ is its frontier word, Theorem 2.3 gives $R_h(t)=|w|$. Put

$$
J=C_h(d,\delta)-1,\qquad I_0(h)=\log_2 C_h(d,\delta),\qquad \phi=\alpha^{-1}.
$$

Here $I_0$ measures the logarithm of the number of attained observation classes. It presupposes neither a source distribution nor a Shannon entropy interpretation.

**Theorem 9.2 (two-digit band and the fixed-boundary logarithmic limit).** If $J=0$, then $R_h(t)=0$ for every $t$. If $J\ge1$, define

$$
\ell=\max\{e\ge0:G_e\le J\}.
$$

Every tail then satisfies the simultaneous bounds

$$
\max(1,\ell)\le R_h(t)\le\ell+2.
$$

In particular the raw Read counts of any two tails differ by at most two. Uniformly in all allowed $d,\delta,h,t$,

$$
R_h(t)=\log_\phi(1+\alpha^dh)+O(1),\qquad
I_0(h)=\log_2(1+\alpha^dh)+O(1).
$$

For each fixed $d,\delta$, as integer $h\to\infty$,

$$
I_0(h)=\log_2 h-d\log_2\phi+o(1),\qquad
\frac{I_0(h)}h\longrightarrow0.
$$

Proof. Use the exact cylinder/read correspondence of Theorem 2.3, the node index and length ranges of Theorem 4.2, and the completed-split description of Theorem 5.1. When $J=0$, the only frontier word is empty. When $J\ge1$, the root has split and each frontier word $w$ is nonempty, with

$$
I(\operatorname{parent}(w))\le J<I(w).
$$

For every complete nonempty word of length $e$, its index lies in $[G_e,G_{e+1}-1]$. If $e<\ell$, then $I(w)\le G_\ell-1<J$, a contradiction. If the parent has length greater than $\ell$, that parent is nonempty and its index is at least $G_{\ell+1}>J$, also a contradiction. Thus the parent has length at most $\ell$; adding one block increases length by either one or two. These facts give the asserted band, including the special case $\ell=0$ when $J=1$. There is no use of a nonempty-word index bound at the empty root.

For completeness, elementary induction in the Fibonacci recurrence gives

$$
\phi^e\le G_e\le\phi^{e+1}\quad(e\ge0).
$$

Consequently, for $J\ge1$,

$$
\ell\le\log_\phi J<\ell+2,
\qquad |R_h(t)-\log_\phi J|\le2.
$$

Write $x=\alpha^dh$. Theorem 5.2 gives

$$
\frac{1+x}{2}\le C_h<(2+\alpha)(1+x).
$$

Since $J\ge1$ implies $C_h=J+1\le2J$, we have

$$
\frac{1+x}{4}\le J<(2+\alpha)(1+x)<4(1+x).
$$

Thus one uniform bound for the first $O(1)$ error is $2+\log_\phi4$. In the remaining case $J=0$, Theorem 5.2 implies $0\le x<C_h=1$, so $R_h=0$ differs from $\log_\phi(1+x)$ by less than $\log_\phi2$. Taking base-two logarithms of the same capacity bounds proves the second uniform estimate.

Finally, keep $d,\delta$ fixed. The sharper supplier estimate $0<C_h-\alpha^dh<2+\alpha$ yields

$$
C_h=\alpha^dh\bigl(1+O(h^{-1})\bigr).
$$

Continuity of the logarithm at one gives the stated expansion; division by $h$ gives the limit. Its $o(1)$ assertion does not let $d$ vary with $h$. $\square$

The application is repo-derived from the cited supplier theorems; inversion of Fibonacci growth and elementary logarithmic estimates are classical intermediates. The same $h$ counts actual Next/Emit/Advance/Return transactions, whereas $R_h$ counts acquired bits and $I_0$ counts distinguishable classes on the restricted observation. In particular the pathwise statement does not replace Read counts by an average over tails or reveal those counts through the interface.

If a probability law on tails is separately supplied and $O_h=v_h(t)$, the classical Shannon bound gives $H(O_h)\le\log_2C_h$: for its nonzero class probabilities $p_j$, concavity of $\log_2$ gives $\sum_jp_j\log_2(1/p_j)\le\log_2\sum_jp_j(1/p_j)\le\log_2C_h$. Equality requires uniform attained-class probabilities. No such law is selected here, so $I_0$ is not asserted to equal an actual entropy or to give a probabilistic error rate. The exact recovery horizons and partitions of Section 6 are reused without a new horizon assertion.

## 追加锚（本行以下为增补区）

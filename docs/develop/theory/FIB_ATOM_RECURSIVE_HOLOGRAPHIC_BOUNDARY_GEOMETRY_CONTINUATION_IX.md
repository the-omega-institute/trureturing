# FIB atomic boundary geometry IX: source-faithful resolution and boundary obligations

**Convention 241.0 (canonical continuation and scope).** This volume continues
canonical Continuation VII §239 and canonical Continuation VIII §§240–241. Those two
files remain the published source texts at their existing paths. The distinct
branch results formerly drafted as §§239–252 are retained here under the local
IX numbering §§241–254: former §239 is IX §241, former §240 is IX §242, and
former §§241–252 are IX §§243–254. The duplicate draft §253 is represented by
canonical VII §239; its replacement obstruction and restricted bridge are IX
§§255–256. The source family, first-disagreement mass, and native contraction
used below are the existing `Source` and `NativeMismatchContraction` contracts;
no new Lean statement or physical source-to-space identification is introduced
here.

## 241. Measure-free packing and the resolution budget

### 241.1 A metric-doubling replacement for the volume hypothesis

Uniform lower masses for disjoint small balls, together with an upper mass
bound for their enclosing ball, are one sufficient way to turn a resolved
occurrence set into a packing bound. The measure is not essential to that
counting step. The following version uses only a uniform metric covering
property and therefore has a different scope.

**Definition 241.1 (uniform metric-doubling occurrence bridge).** Retain the
occurrence sets $V_n=V_{T_n}$, their counts $N_n=2F_{n+1}-1$ and heights
$n-1$ for $n\ge1$ from
[Continuation VI, Proposition 114.2(5), equation (114.7)](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md#114-a-finite-depth-source-to-carrier-certificate-and-its-first-failures). Let
$\iota_n:V_n\hookrightarrow X$ map every task-distinct occurrence into one
metric space $(X,\rho)$. Assume that, for fixed $\delta>0$ and fixed
$A,B>0$,

$$
\rho(\iota_n(x),\iota_n(y))\ge\delta\quad(x\ne y),
\qquad
\rho(o,\iota_n(x))\le A(n-1)+B.
\tag{241.1}
$$

Assume also that every closed ball at every center and radius used below is
covered by at most $K\ge2$ closed balls of half its radius, with the same
finite $K$ at every level. Put

$$
R_n=A(n-1)+B,
\qquad q=\log_2K.
\tag{241.2}
$$

No measure, Green kernel, generator, or spatial dimension is part of this
definition.

**Theorem 241.2 (metric-doubling packing obstruction).** Under Definition
241.1,

$$
\boxed{
N_n\le
K^{\left\lceil\log_2\left(1+\frac{2R_n}{\delta}\right)\right\rceil}.
}
\tag{241.3}
$$

Proof. Let

$$
k_n=\left\lceil\log_2\left(1+\frac{2R_n}{\delta}\right)\right\rceil.
$$

Iterating the half-radius covering property $k_n$ times covers the closed
ball $\overline B(o,R_n)$ by at most $K^{k_n}$ closed balls of radius
$R_n/2^{k_n}$. Since

$$
\frac{2R_n}{2^{k_n}}<\delta,
$$

each final ball has diameter strictly smaller than $\delta$ and contains at
most one point of the $\delta$-separated set $\iota_n(V_n)$. All occurrences
lie in the original ball by (241.1), so (241.3) follows. $\square$

If $\delta$ is fixed, (241.3) is polynomial in $n$:

$$
K^{\lceil\log_2(1+2R_n/\delta)\rceil}
=O(n^q).
\tag{241.4}
$$

But $N_n=2F_{n+1}-1$ has

$$
\log N_n=n\log\varphi+O(1).
\tag{241.5}
$$

Consequently no one metric-doubling carrier with fixed $K,A,B,\delta$ can
resolve every prefix. This is a measure-free obstruction; it does not say
that the source has metric dimension $q$, and it does not select $q=3$.

### 241.2 Necessary resolution budget

The same estimate gives a quantitative condition when the resolution is
allowed to vary. Since

$$
\left\lceil\log_2(1+2R_n/\delta_n)\right\rceil
<\log_2(1+2R_n/\delta_n)+1,
$$

every prefix with $N_n>K$ must satisfy

$$
\boxed{
\delta_n
<
\frac{2R_n}{(N_n/K)^{1/q}-1}
=
\frac{4R_n}{N_n^{1/q}-2}.
}
\tag{241.6}
$$

The second form uses $K^{1/q}=2$. Thus, for fixed $K,A,B$, the required
resolution is at most

$$
\delta_n=O\!\left(n\,\varphi^{-n/q}\right).
\tag{241.7}
$$

This is a necessary budget, not an embedding construction and not a
sufficient stability condition. Passing from a finite prefix to an infinite
carrier therefore requires a declared scale law; a fixed positive spatial
resolution is incompatible with the stated uniform bridge.

**Proposition 241.3 (finite exact certificate).** For

$$
K=8,\qquad A=B=\delta=1,\qquad n=26,
$$

one has $R_{26}=26$, $N_{26}=2F_{27}-1=392835$, and

$$
\left\lceil\log_2(1+2R_{26}/\delta)\right\rceil
=\lceil\log_2 53\rceil=6.
$$

The cover capacity is therefore $8^6=262144$, so (241.3) fails:

$$
\boxed{392835>262144.}
\tag{241.8}
$$

This rejects these constants at this prefix. It is not by itself an
all-prefix theorem, and it does not identify $K=8$ with a three-dimensional
covering number.

### 241.3 Why an upper measure bound alone is insufficient

Replacing the doubling condition by an upper estimate on ball masses loses
the packing conclusion unless a uniform lower mass or a direct covering
bound is also supplied. A concrete countermodel is the infinite rooted
binary occurrence tree with unit graph metric. Give a vertex at depth $h$
the mass

$$
\mu(v)=Z^{-1}4^{-h},
\qquad
Z=\sum_v4^{-\operatorname{depth}(v)}.
\tag{241.9}
$$

Since there are at most $2^h$ vertices at depth $h$, $1\le Z\le2$.
Every occurrence remains separated by one unit and the prefix of height
$n-1$ lies in a ball of radius $n$. Nevertheless, for any fixed $d>0$ and
any $t\ge1/3$,

$$
\mu(B(z,t))\le1\le 3^d t^d.
\tag{241.10}
$$

Thus the required upper $t^d$ estimate at the macroscopic radii can hold
while exponentially many occurrences still fit in radius $n$. At radius
$1/3$, the ball about a vertex contains only that vertex and its mass tends
to zero along any infinite spine. There is no uniform lower mass and no
metric-doubling packing control.

This countermodel does not assert an upper estimate at arbitrarily small
radii; it isolates exactly the missing hypothesis. Therefore a
measure-based packing proof may be replaced by Theorem 241.2 only after a
metric-doubling or direct packing property has been established. Neither
route supplies the still-missing occurrence-to-physical-carrier metric,
transport, clock, observation, or dimension-sensitive invariant.

## 241.99 追加锚（本行以下为增补区）

## 242. Exponential resolution threshold

The necessary budget in (241.6) can be stated as a phase boundary. This
separates a change of resolution law from a claim about the dimension of the
carrier.

**Theorem 242.1 (subcritical resolution is impossible).** Suppose the
metric-doubling cover constant $K$, the root-radius constants $A,B$, and the
source separation constants are as in Definition 241.1, except that the
separation may vary with $n$ and is denoted by $\delta_n$. Let

$$
q=\log_2K,qquad
\delta_n\ge c\,n^{-s}e^{-\kappa n}
\quad(n\ge n_0),
\tag{242.1}
$$

for fixed $c>0$, $s\ge0$, and $\kappa\ge0$. If every prefix is
resolved in one common metric-doubling carrier, then necessarily

$$
\boxed{
\kappa\ge\frac{\log\varphi}{q}.
}
\tag{242.2}
$$

In particular, a fixed or polynomially shrinking resolution cannot support
all Fibonacci prefixes for any finite $K$.

Proof. From (241.3) and $\lceil x\rceil<x+1$,

$$
N_n
<K\left(1+\frac{2R_n}{\delta_n}\right)^q.
\tag{242.3}
$$

Since $R_n=A(n-1)+B=O(n)$, (242.1) gives a constant $C>0$ such that

$$
1+\frac{2R_n}{\delta_n}
\le C n^{s+1}e^{\kappa n}
\tag{242.4}
$$

for all sufficiently large $n$. Hence

$$
N_n\le C' n^{q(s+1)}e^{q\kappa n}.
\tag{242.5}
$$

On the other hand, Binet's formula for $N_n=2F_{n+1}-1$ gives

$$
N_n\ge c'\varphi^n
\tag{242.6}
$$

for some $c'>0$ and all large $n$. If $q\kappa<\log\varphi$, the ratio of
(242.6) to (242.5) tends to infinity, a contradiction. Therefore (242.2)
is necessary. The case $\kappa=0$ includes every lower bound of polynomial
order. $\square$

**Corollary 242.2 (the critical polynomial window).** At the threshold

$$
\kappa_*:=\frac{\log\varphi}{q},
$$

the packing estimate requires

$$
\delta_n=O\!\left(n e^{-\kappa_* n}\right).
\tag{242.7}
$$

Thus a law bounded below by $c n^{1+\epsilon}e^{-\kappa_*n}$ for any
$\epsilon>0$ is impossible, while the law $n e^{-\kappa_*n}$ is only a
necessary scale and is not an existence construction.

For the stipulated $K=8$, one has $q=3$ and therefore

$$
\kappa_*=\frac{\log\varphi}{3}.
\tag{242.8}
$$

This number is a resolution exponent of the declared occurrence bridge. It
is not a spatial dimension, a heat-kernel exponent, or a Fock/observation
rank. A physical three-dimensional conclusion still needs an independent
realization law and an observable correspondence.

## 242.99 追加锚（本行以下为增补区）

## 243. 仿射运输与全局标架

前面的局部三维条件只给出每个接口的方向空间。要判断这些接口是否能拼成一个全局载体，还必须指定沿合法边传播状态的规则。

### 243.1 仿射边运输

设 $G=(V,E)$ 是连通的有向关系图。每条有向边 $e:x\to y$ 携带一个仿射运输

$$
T_e(z)=A_ez+b_e,
\qquad A_e\in\mathrm{GL}(d,\mathbb R),
\quad b_e\in\mathbb R^d.
\tag{243.1}
$$

反向边的运输声明为逆映射：

$$
T_{\bar e}=T_e^{-1}.
\tag{243.2}
$$

若 $p=e_k\cdots e_1$ 是一条路径，规定

$$
T_p=T_{e_k}\circ\cdots\circ T_{e_1}.
\tag{243.3}
$$

对闭路 $\gamma$，$T_\gamma$ 是该闭路的仿射 holonomy。这里有两个容易混淆的条件。

**位置无歧义**只要求某个选定的 $z_0$ 满足

$$
T_\gamma(z_0)=z_0
\qquad\text{for every closed }\gamma.
\tag{243.4}
$$

**完整标架无歧义**要求

$$
\boxed{T_\gamma=\mathrm{id}\quad\text{for every closed }\gamma.}
\tag{243.5}
$$

前者可以让一个特殊点路径无关，后者才让所有局部向量和仿射原点都能无歧义地运输。

### 定理 243.1　平凡仿射 holonomy 的等价刻画

以下两项等价：

1. 每条闭路都满足 $T_\gamma=\mathrm{id}$；
2. 存在一族仿射坐标 $g_x:\mathbb R^d\to\mathbb R^d$，满足对每条边 $e:x\to y$：

$$
g_y=T_e\circ g_x.
\tag{243.6}
$$

**证明。** 假设第一项成立。选定根 $o$ 和任意仿射双射 $g_o$。对每个 $x$，取一条从 $o$ 到 $x$ 的路径 $p_x$，定义

$$
g_x=T_{p_x}\circ g_o.
\tag{243.7}
$$

若更换路径，两个路径的拼接给出一条闭路；平凡 holonomy 使结果不变。因此对边 $e:x\to y$，路径 $p_xe$ 可以作为 $y$ 的路径，得到 (243.6)。

反过来，沿任意闭路反复使用 (243.6)，得到

$$
T_\gamma\circ g_o=g_o.
$$

由于 $g_o$ 是满射，故 $T_\gamma=\mathrm{id}$。\quad$\square$

因此，“每个接口都有同一套三维坐标”不能只由局部 Gram 矩阵正性推出。还需要边运输满足 (243.5)，或者明确把 holonomy 作为边界状态保留下来。

## 244. 非平凡 holonomy 的任务相对逃逸条件

设历史 $h$ 记录一个端点、一个初始局部状态和一条合法运输路径。若观察只保留端点与当前粗粒度读出，而不保留路径的标架类，则两个历史可能满足

$$
q(h)=q(h')
$$

却有不同的目标响应。最直接的目标是运输后的状态：

$$
F(h)=T_p(z_0).
\tag{244.1}
$$

若 $h'$ 在同一端点使用 $p\gamma$，则

$$
F(h')=T_p\bigl(T_\gamma(z_0)\bigr).
\tag{244.2}
$$

对这一对历史，须另行要求实际选定的观察满足 $q(h)=q(h')$。若观察包含当前粗粒度读出，该等式不能仅由省略路径或标架类推出。在这个观察纤维前提下，有

$$
\boxed{q(h)=q(h')\ \land\ T_\gamma(z_0)\ne z_0
\quad\Longrightarrow\quad F(h)\ne F(h').}
\tag{244.3}
$$

这是因为第 243.1 节的边运输均为仿射双射，其复合 $T_p$ 为单射；由 (244.1)–(244.2)，$T_\gamma(z_0)\ne z_0$ 给出目标值不等，而观察相等来自单独列出的前提。这两个历史因而构成目标相对的逃逸对；非平凡 holonomy 本身不保证存在这样的逃逸对。若目标只看 holonomy 的某个不变量，非平凡运输仍可能对该目标无害。正确条件是，声明的目标和合法操作必须在所选观察纤维上保持不变。

### 定义 244.1　提升边界

在端点 $x$ 处，令 $\mathcal P_x$ 为从根到 $x$ 的合法路径集合，并按右乘闭路 holonomy 的作用取等价类。任务需要的提升边界可以写成

$$
\widetilde B_x
=
\bigl(\text{局部状态}\bigr)\times
\bigl(\mathcal P_x/\ker \mathsf H_x\bigr),
\tag{244.4}
$$

其中 $\mathsf H_x$ 是路径类在声明任务上的响应表示，$\ker\mathsf H_x$ 包含所有对该任务没有影响的回路差异。

这一定义有两个边界情形：

$$
\begin{array}{ll}
\mathsf H_x\text{ 对所有回路平凡}:&\widetilde B_x\text{ 可退化为普通局部边界};\\[1mm]
\mathsf H_x\text{ 非平凡}:&\text{必须保留路径/标架的任务相关部分，或接受目标逃逸}.
\end{array}
\tag{244.5}
$$

因此，高维内部通过边界返回的方式不只有记忆核。非平凡 holonomy 还会以路径类、共同标架或回路响应的形式进入边界；把它们静默压成一个局部向量，会破坏需要路径相容性的拼接任务。

## 245. 欧氏载体的 packing 证书与解析阈值

前面的 metric-doubling 估计使用抽象覆盖常数。若候选载体确实是欧氏 $d$ 维空间，还可以直接使用体积比得到更强的检查。

### 定理 245.1　欧氏分离集的 packing 上界

若 $S_n\subseteq\mathbb R^d$ 满足

$$
S_n\subseteq\overline B(0,R_n),
\qquad
\|x-y\|\ge\delta_n\quad(x\ne y),
$$

则

$$
\boxed{
|S_n|
\le
\left(1+\frac{2R_n}{\delta_n}\right)^d.
}
\tag{245.1}
$$

**证明。** 以每个 $x\in S_n$ 为中心取半径 $\delta_n/2$ 的闭球。它们的内部两两不交，并且都包含在半径 $R_n+\delta_n/2$ 的球中。比较 $d$ 维 Lebesgue 体积，消去单位球体积后得到 (245.1)。\quad$\square$

### 定理 245.2　Fibonacci 解析分辨率阈值

假设第 $n$ 个前缀有 $N_n=2F_{n+1}-1$ 个需区分的 occurrence，并且

$$
R_n\le An+B,
\qquad
\delta_n\ge c\,n^{-s}e^{-\kappa n}
$$

其中 $A,B,c>0$、$s\ge0$。若所有前缀都能以一个共同的欧氏 $d$ 维载体实现为上述分离集，则必有

$$
\boxed{d\kappa\ge\log\varphi.}
\tag{245.2}
$$

**证明。** 由 (245.1)，$N_n$ 至多为一个常数乘以

$$
n^{d(s+1)}e^{d\kappa n}.
$$

另一方面 Binet 公式给出 $N_n\ge c'\varphi^n$，其中 $c'>0$。若 $d\kappa<\log\varphi$，两者比值随 $n$ 趋于无穷，矛盾。\quad$\square$

在三维时，这个必要条件为

$$
\boxed{
\kappa\ge\frac{\log\varphi}{3}
\approx0.1604039416865345.
}
\tag{245.3}
$$

这个数是 occurrence-to-carrier 分辨率指数。它不是空间维数、热核指数、Fock 模式数或观察秩；只有在另行证明这些量之间的对应后，才可以讨论物理解释。

### 命题 245.3　有限反例证书

取三维、$n=26$、$R_{26}=26$、$\delta_{26}=1$。则

$$
|S_{26}|\le(1+2\cdot26)^3=53^3=148877,
$$

而

$$
N_{26}=2F_{27}-1=392835.
$$

故

$$
\boxed{53^3=148877<392835=N_{26}.}
\tag{245.4}
$$

这排除在这些具体半径、分离度和 occurrence 计数下的三维欧氏实现。它不排除改变分离率、允许更大半径、使用非欧氏载体或不要求所有 occurrence 同时可区分的模型，也不单独证明三维物理空间不存在。

## 246. 从局部三框架到真正三维载体的桥接条件

现在可以把“局部三维”与“整体三维”之间的缺口写成一组同时成立的条件。

### 定义 246.1　任务相对的三维载体证书

对每个有限前缀，要求存在：

1. 一个三维局部状态空间及其实际运输分布；
2. 运输分布无横向泄漏，即括号闭合或有相应的离散小回路闭合证书；
3. 仿射运输在声明任务上具有平凡 holonomy，或提升边界明确保留全部任务相关 holonomy；
4. occurrence 到载体的映射在声明分辨率下是注入的，并满足 $R_n,\delta_n$ 的统一尺度界；
5. 时钟、读出和合法拼接规则都由同一观察边界恢复。

### 命题 246.2　条件性桥接结论

若 Definition 246.1 的五项均成立，则每个有限前缀都具有一个任务相对的三维运输实现；若再有统一的全层级嵌入、统一的运输和观察极限，以及近似态的紧致性，则可把有限层结论传到极限载体。

若第五项或第三项失败，则已有三维局部状态只能称为三维接口：它不再保证整体路径、操作合法性和未来响应可由该接口无损恢复。若第四项失败，packing 阈值也不能用于该模型，因为尚未建立 occurrence 与欧氏点之间的注入对应。

这不是一个从 FIB 语法单独推出的宇宙三维定理。它是一个可逐项反驳的桥接判据：局部三框架、无横向泄漏、任务相对平凡 holonomy、注入与分辨率证书、以及极限紧致性，缺一项都不能把“每个接口三维”升级为“实际载体三维”。

本卷新增结果仍属于理论推导，尚未作为 Lean kernel 证明交付。它们的下一步验证对象已经具体化为：对项目原生合法运输构造 $T_e$；计算生成回路的 holonomy；检查任务观察是否切开 (244.3) 的逃逸对；最后用 (245.1) 和 (245.4) 检验候选 occurrence-to-carrier 桥。

## 247. 辛预测完成对“三个观测坐标”的限制

DEV 的《统一预测几何》把观察边界与动力学放在同一个线性模型中。取

$$
z\in\mathbb R^{2n},\qquad
S=S^{\mathsf T}\succ0,\qquad
A=JS,
$$

其中 $J$ 是标准辛矩阵，读出为 $b=Cz$。定义未来读出的最小行空间

$$
W_0=\operatorname{im}C^{\mathsf T},
\qquad
W_{k+1}=W_k+A^{\mathsf T}W_k,
\qquad
W=\bigcup_kW_k.
\tag{247.1}
$$

取满行秩矩阵 $O$ 使其行空间为 $W$，则 $Oz$ 是全部连续未来读出的最小线性预测边界。

### 定理 247.1　精确非退化辛预测边界具有偶数秩

在上述正定 Hamiltonian 模型中，$W$ 上的限制配对

$$
(u,v)\longmapsto u^{\mathsf T}Jv
$$

非退化。因此：

$$
\boxed{\operatorname{rank}O=\dim W\text{ 为偶数}.}
\tag{247.2}
$$

若还存在矩阵 $K$ 使

$$
OA=KO,
\tag{247.3}
$$

则约化边界满足

$$
K=J_rP^{-1},
\qquad
P=OS^{-1}O^{\mathsf T}\succ0,
\qquad
J_r=OJO^{\mathsf T}
$$

且 $J_r$ 可逆。

**证明。** 若非零 $u\in W$ 与 $W$ 中所有向量都辛正交，则 $A^{\mathsf T}W\subseteq W$ 和 $A=JS$ 给出

$$
u^{\mathsf T}JA^{\mathsf T}u
=
(Ju)^{\mathsf T}S(Ju)>0,
$$

与辛正交矛盾。因此限制配对非退化。非退化反对称矩阵的阶数为偶数，故 (247.2) 成立；其余等式由 $OA=KO$、$AS^{-1}=J$ 直接整理得到。\quad$\square$

### 推论 247.2　秩三的精确边界必须离开至少一个条件

若 $C$ 有三个独立读出，而这些读出本身已经形成全部精确自治预测边界，即

$$
\operatorname{rank}O=3,
$$

则不可能同时满足正定 Hamiltonian 假设、精确闭合 (247.3) 和非退化辛约化。

所以一个“三分量边界”必须被解释为以下至少一种情况：

1. 它只是配置或方向的投影，预测边界还包含隐藏变量；
2. 它是退化的非辛商；
3. 它只在有限误差内自治；
4. 实际动力学不属于此正定 Hamiltonian 模型。

这条排除只针对精确线性辛预测边界，不能推广为“任何三维流形都不可能存在”。相位圆就是一维自治非线性读出，但它没有非退化二形式。

## 248. 三维配置接口与六维正则完成

“三维接口”与“完整预测状态”的最小容量，取决于三个读出是否被解释为配置坐标。

### 定义 248.1　配置型三框架

称三个独立读出为配置型三框架，是指存在坐标

$$
q=(q_1,q_2,q_3)\in\mathbb R^3
$$

使它们张成完整状态中的 Lagrange 子空间 $L$，并且允许的变分满足

$$
\omega|_L=0,
\qquad \dim L=3.
\tag{248.1}
$$

### 定理 248.2　配置型三框架的正则完成至少六维

若 $L$ 是一个三维 Lagrange 子空间，则任何包含其三个独立共轭变量的非退化辛空间都至少是

$$
\boxed{L\oplus L^*\cong\mathbb R^3_q\oplus\mathbb R^3_p,\qquad \dim=6.}
\tag{248.2}
$$

在标准正则坐标中，辛形式为

$$
\omega=\sum_{i=1}^3dq_i\wedge dp_i.
$$

**证明。** 对一个 $2n$ 维辛空间，Lagrange 子空间的维数为 $n$。由 $\dim L=3$ 得 $n=3$，所以总维数为 $2n=6$。选择 $L$ 的一组基并取其辛对偶基，得到 $q,p$ 的 Darboux 坐标。\quad$\square$

这里的“至少”是针对正则共轭完成的，不是说任意携带三个实数的编码都需要六个数。若只要求三个任意观测量的精确 Hamiltonian 预测闭合，定理 247.1 只给出偶数秩下界：秩三被排除，最低可能是四。只有当三个量确实是三维配置坐标并要求其共轭方向也可运输时，六维结论才适用。

### 一个可直接计算的 FIB 兼容样例

取三个独立配置分量和非奇异频率矩阵 $\Omega$，令

$$
A=
\begin{pmatrix}
0&I_3\\
-\Omega^2&0
\end{pmatrix},
\qquad
C=\begin{pmatrix}I_3&0\end{pmatrix}.
\tag{248.3}
$$

则

$$
CA=\begin{pmatrix}0&I_3\end{pmatrix},
\qquad
CA^2=\begin{pmatrix}-\Omega^2&0\end{pmatrix}.
$$

当 $\Omega$ 可逆时，$C$ 与 $CA$ 的行就已经张成全部六维状态。因此当前三维配置读出不能独立预测下一时刻；消去 $p$ 后，它满足二阶方程

$$
\ddot q+\Omega^2q=0.
\tag{248.4}
$$

六维一阶状态与三维二阶历史是同一信息的两种表示。这里增加的是共轭记忆，不是第四根空间轴。

## 249. 相空间 holonomy 会从隐藏共轭变量返回

前面的仿射运输只记录位置型 $T_e$。若接口承载 Hamiltonian 预测，还必须考虑其辛提升

$$
\boxed{
\widetilde T_e(q,p)=\bigl(A_eq+b_e,\,A_e^{-\mathsf T}p\bigr).
}
\tag{249.0}
$$

这是仿射位置运输的余切提升；直接代入 $dq'\wedge dp'=dq\wedge dp$ 可验证它保持标准辛形式。若模型另有磁势或生成函数项，必须把该项作为额外声明的边运输，不能由 (249.0) 自动推定。闭路给出相空间 holonomy $\widetilde H_\gamma$。

### 命题 249.1　位置平凡不等于预测平凡

设 $C$ 只读出位置，且某闭路满足

$$
C\widetilde H_\gamma=C,
\tag{249.1}
$$

但对某个有限未来词 $w$ 有

$$
C A_w\widetilde H_\gamma\ne C A_w.
\tag{249.2}
$$

则存在两个当前读出相同的历史，它们在未来响应上不同；因此位置边界产生任务相对的信息逃逸。

**证明。** 取两个相差该闭路 holonomy 的状态 $z$ 与 $\widetilde H_\gamma z$。由 (249.1)，当前读出相同；由 (249.2)，对某个未来词的响应不同。这正是同一观察纤维中的逃逸对。\quad$\square$

因此，真正需要检验的不是仅有

$$
T_\gamma=\mathrm{id}\quad\text{on positions},
$$

而是任务预测空间上的条件

$$
\boxed{O\widetilde H_\gamma=O.}
\tag{249.3}
$$

若 (249.3) 不成立，隐藏动量、相位或共轭记忆就必须进入提升边界。它们可以以显式状态、历史核或路径类存储；直接把它们重置为零会改变拼接后的未来。

## 250. 更新后的“三维载体”判据

将 §§243–249 合并，可以得到一个比“局部有三个方向”更严格的条件表。

### 定义 250.1　配置—预测双尺度证书

候选 FIB 实现要声称“实际载体是三维”，至少需要同时给出：

1. 三维配置型局部框架及其 occurrence-to-carrier 注入；
2. 无横向运输泄漏，使局部框架形成三维可积切面；
3. 位置运输的任务相对 holonomy 平凡；
4. 辛或其他动力学提升的预测 holonomy 满足 (249.3)，或边界显式保留其任务相关轨道；
5. 分辨率满足本卷定理 241.2、242.1 与 245.1–245.2 在各自假设下给出的 packing 预算；
6. 三维配置的共轭变量、历史记忆或合法性档案满足动态预测充分性；
7. 有统一细化嵌入和近极小态紧致性，使有限层结论能传到极限。

### 命题 250.2　局部三维与完整预测维数的分离

若上述证书成立，则“三维”可以有一个严格的任务相对含义：它是配置载体的局部切维数。完整一阶预测边界则不必是三维；在正则 Hamiltonian 情形，包含三个配置坐标的最小自然完成是六维，而一般任意观测的精确辛预测秩必须是偶数。

若只证明局部 Gram 正性、三个关系分量或一个三维投影，而没有 (249.3)、注入和尺度证书，则最多得到三维接口，不能得到无损的实际三维载体。

这把“为什么三维”拆成两个互不混淆的问题：

$$
\boxed{
\text{三维是配置接口的稳定几何窗口},
\qquad
\text{高维是预测、共轭与跨界关系的承载空间}.
}
$$

本节仍是条件性理论推导，未作为 Lean kernel 证明交付。下一项可计算工作是：从项目原生运输提取位置与辛提升 $T_e,\widetilde T_e$；计算生成闭路的两个 holonomy；构造 $O$ 并检查其秩与 (249.3)；再将结果与 occurrence packing 和边界记忆核逐项合并。

## 250.99 追加锚（本行以下为增补区）

## 251. 目标索引、独立见证对与共同来源边界
本节把 [strict-real 支持卷 V](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md) 定理 1.1–1.2 接到 §§244、246、250 的目标相对边界；通用逃逸与纤维下降沿用[关系观察卷定义 2.1](RECURSIVE_RELATIONAL_OBSERVATION.md)，不另立通用定理。以下是这些来源合同的 `repo-derived` 应用，不主张文献原创性。

### 定义 251.1　完整 child 与目标相对逃逸
对声明区域 $U\subseteq\{(p,v):p\ne24\}$，令 $C_\beta=C(p,v)$ 为支持卷 V §1 的全部合法完整世界 $W=(P(r,b),g,d)$，保留原始 parent、整条非零且次数至多三的 gain、drift、全部 companion、低次和零样本分支及严格守卫 $0<r<1,b>0$；令 $X_U=\bigsqcup_{\beta\in U}C_\beta$，$\pi(W)=\beta$。既有目标逃逸在此完整 child 上的应用为 $E_U(O;T)=\{(\beta,W,W'): \beta\in U,\ W,W'\in C_\beta,\ O(W)=O(W'),\ T(W)\ne T(W')\}$，完整来源目标为 $T_{\rm src}(W)=W$。对同一观察与确定性目标元组，$E_U(O;(T_1,T_2))=E_U(O;T_1)\cup E_U(O;T_2)$，因为元组不同恰是至少一分量不同；因此各分量均无逃逸时元组也无逃逸。这只是集合论恢复，不给出高效解码、有限精度稳定性或物理可取得性。

### 定义 251.2　独立见证对与同对联合签名
以支持卷 V §1 的实际终端响应 $a(W),m(W)$ 定义 $R_J(\beta)=\{(W,W')\in C_\beta^2:W\ne W',\ a(W)=a(W')\}$、$R_M(\beta)=\{(W,W')\in C_\beta^2:W\ne W',\ m(W)=m(W')\}$，并令 $D_J(U)=\{\beta\in U:R_J(\beta)\ne\varnothing\}$、$D_M(U)=\{\beta\in U:R_M(\beta)\ne\varnothing\}$。同对集合 $D_{JM}^{\rm same}(U)=\{\beta\in U:R_J(\beta)\cap R_M(\beta)\ne\varnothing\}$ 只满足 $D_{JM}^{\rm same}(U)\subseteq D_J(U)\cap D_M(U)$；后者允许同一完整 child 中的两组独立见证对，允许交叉重合且不要求两对的公共终端值相同。反向包含一般不成立：三个抽象世界的 $(a,m)$ 分别为 $(0,0),(0,1),(1,0)$ 时，两种响应各有碰撞而联合签名单射；这是量词反例，不是 strict-real 世界构造。令 $O_q=\pi$、$O_J=(\pi,a)$、$O_M=(\pi,m)$、$O_{JM}=(\pi,a,m)$，则 $D_{JM}^{\rm same}(U)$ 正是 $E_U(O_{JM};T_{\rm src})$ 的基点投影。数学联合签名来自同一世界；其物理取得还须另给允许同时读取、复制或重置的协议。

### 命题 251.3　严格 equal-M 见证与 whole-child J 注入性的翻译
令 $K=[56,58]\times[304,305]$。支持卷 V 定理 1.1 对每个 $\beta\in K$ 的整个 $C_\beta$ 给出 $R_J(\beta)=\varnothing$，故 $E_K(O_J;T_{\rm src})=\varnothing$，且任意完整世界上的确定性目标 $T$ 都满足 $E_K(O_J;T)=\varnothing$；这不只是所选 witness 子集的注入性。定理 1.2 又给出 $\beta_*\in K$ 及 $W_A\ne W_B\in C_{\beta_*}$，满足 $m(W_A)=m(W_B)$；前述整个 child 的 J 注入性强制 $a(W_A)\ne a(W_B)$。于是 $(\beta_*,W_A,W_B)\in E_K(O_M;a)\cap E_K(O_M;T_{\rm src})\cap E_K(O_M;(a,m))$，且 $E_K(O_q;a)\ne\varnothing$，但同一对不属于 $E_K(O_M;m)$。证明只将两条来源结论代入定义；得到的是 $\beta_*\in D_M(K)\setminus D_J(K)$ 和指定观察、目标、区域下的逃逸，不结算全局 $D_J\cap D_M$。

### 命题 251.4　区域边界充分性与原生来源拉回条件
对 $\Gamma:X_U\to B$ 及包含预测响应和合法性目标的声明目标族 $\mathscr T$，要求 $E_U(\Gamma;T)=\varnothing$ 对所有 $T\in\mathscr T$ 成立，只保证逐 child 的充分性；若要覆盖整个区域，还须保留基点，例如存在 $b:B\to U$ 使 $\pi=b\circ\Gamma$，或改用边界 $(\pi,\Gamma)$。在此前提下，同边界的两世界必在同一 child，再由逃逸为空得到各目标相同，故目标在边界实际像上下降。向 FIB 原生来源传递时，另须声明原生来源集合 $S_{\rm native,U}$、其基点投影 $\beta_{\rm native}:S_{\rm native,U}\to U$、原生边界 $\gamma:S_{\rm native,U}\to B$ 及目标 $T_{\rm native}$，并给出保基点映射 $L:S_{\rm native,U}\to X_U$，满足
$$
\pi\circ L=\beta_{\rm native},\qquad
\gamma=\Gamma\circ L,\qquad
T_{\rm native}=T\circ L.
$$
还须使合法更新及其定义域的交换图成立；完整来源目标要求 $L$ 在声明来源等价类上单射。正向充分性由复合拉回，但逃逸见证向原生来源传递还要求两个见证世界均在 $L$ 的像中且可同时合法提升；单有映射不够。上述对应、更新与提升条件仍为 open；同名、同维或相同终端数值不能代替它们。

### 有限检验与范围
对 $D_J\cap D_M$ 保留四个世界变量和两组独立见证对，对 $D_{JM}^{\rm same}$ 使用同一对的联合等式；所有世界都须满足完整 child 的原始严格守卫。一个精确见证足以证明相应非空；空性需覆盖全部 child 的区间、Bernstein 或实代数证书，有限抽样不足。候选 $\Gamma$ 的反例是同边界而目标不同的合法世界对；运输与 holonomy 还须在同一来源和合法历史上保持上述交换图，未保留的预测轨道不能重置为零。局部关系维度、预测边界维度、完整来源恢复和物理载体维度继续分立；本卷定义 241.1 与 246.1(4) 的注入和尺度假设、定理 241.2 与 245.1–245.2 的 packing 预算、§§243–244 及 §249 的运输与 holonomy 条件，以及命题 246.2 和定义 250.1(7) 的极限假设仍须分别满足。全局 $D_J\cap D_M$、物理三维载体实现及本节的 Lean 形式化均保持 open；此应用不提供无条件维数结论，也不把不同 source contract 的解析前沿接口视为物理实现。

## 251.99 追加锚（本行以下为增补区）

## 252. 高到低守卫对可逆线性 null 表示的条件性障碍

**定义 252.1（固定的原生前缀与合法性目标）。** 令

$$
\Sigma=\{\mathrm{null},[2],[3],[25],[5]\}.
$$

窗口按高到低读入，每个印刷三位仍按低到高书写；单位位固定为零，允许高端补零，空词合法，没有 End 动作或最高窗非空检查。状态含接缝 $s\in\{0,1\}$ 与整数组成 $n\in\mathbb Z^2$，初态为 $(0,0)$。在合法边上

$$
n'=Sn+d_\sigma,\qquad
S=\begin{pmatrix}1&2\\2&3\end{pmatrix}.
\tag{252.1}
$$

全部接缝与位移为

| 字母 | 印刷三位 | $d_\sigma$ | 允许旧接缝 | 新接缝 |
| --- | --- | --- | --- | --- |
| $\mathrm{null}$ | $000$ | $(0,0)$ | $0,1$ | $0$ |
| $[2]$ | $100$ | $(1,0)$ | $0,1$ | $1$ |
| $[3]$ | $010$ | $(0,1)$ | $0,1$ | $0$ |
| $[25]$ | $101$ | $(2,1)$ | $0$ | $1$ |
| $[5]$ | $001$ | $(1,1)$ | $0$ | $0$ |

令 $\mathcal P\subseteq\Sigma^*$ 为从初态出发的合法有限前缀，$s(w)$ 为其末接缝。固定目标

$$
G_5(w)=\mathbf 1_{\{w[5]\in\mathcal P\}}
       =1-s(w)\qquad(w\in\mathcal P).
\tag{252.2}
$$

它询问下一次 $[5]$ 是否允许，不要求真的执行失败动作，也不把错误结果删出比较。当前组成、方向读数和完整树是另外的任务。

**定义 252.2（待检验的表示合同）。** 所考察的表示由一个有限维实向量空间 $V$、映射 $v:\mathcal P\to V$、一个固定线性自同构 $A:V\to V$ 和一个固定线性泛函 $e:V\to\mathbb R$ 组成，要求

$$
v(w\mathrm{null})=Av(w),\qquad
e(v(w))=G_5(w)\qquad\text{对每个 }w\in\mathcal P.
\tag{252.3}
$$

这里不假设 $v$ 线性、连续或单射，不要求每个向量是可达状态，也不要求其余四个字母有线性实现。可逆性针对整个 $V$；固定的 $A,e$ 不能依前缀或未来测试长度更换。$\mathrm{null}$ 在原生合同中确实更新组成且重置接缝，未被解释为恒等。

**定理 252.3（原生接缝重置排除该表示合同）。** 定义 252.2 的表示不存在。更精确地，令 $H\ge0$ 为整数，只要求下列两条合法轨道的更新等式在 $0\le k<H$ 成立、目标等式在 $0\le k\le H$ 成立，则任何这样的可逆线性表示都须满足

$$
\dim V\ge H+1:
\qquad \mathrm{null}^k,\quad [2]\mathrm{null}^k.
\tag{252.4}
$$

证明。定义 252.1 的表逐项给出

$$
\begin{aligned}
G_5(\varepsilon)&=1,&G_5([2])&=0,\\
G_5(\mathrm{null}^k)&=1,&
G_5([2]\mathrm{null}^k)&=1\quad(k\ge1).
\end{aligned}
\tag{252.5}
$$

所有这些前缀均合法：$[2]$ 从初态合法，$\mathrm{null}$ 对两种接缝都允许，第一次 $\mathrm{null}$ 即将接缝置零。置 $x=v(\varepsilon)-v([2])$，由线性和更新等式得

$$
ex=1,\qquad eA^kx=0\quad(k\ge1).
\tag{252.6}
$$

设 $d=\dim V$。$d=0$ 已与 $ex=1$ 矛盾。对 $d\ge1$，写 $A$ 的特征多项式为

$$
\chi_A(t)=c_0+c_1t+\cdots+c_{d-1}t^{d-1}+t^d,
\qquad c_0=(-1)^d\det A\ne0.
$$

经典 Cayley–Hamilton 恒等式给

$$
0=e\chi_A(A)x
  =c_0ex+\sum_{j=1}^{d-1}c_jeA^jx+eA^dx=c_0,
\tag{252.7}
$$

矛盾。这个论证只使用 $k=0,\ldots,d$。故有限时域 $H$ 若允许 $d\le H$ 也矛盾，得到 (252.4)。所用中间机制是有限维线性表示的标量响应满足固定线性递推；其加权自动机背景见关系延拓几何 §6 所引 Berstel–Reutenauer，*Noncommutative Rational Series with Applications*，Chapter 2，以及 Balle–Panangaden–Precup，[*Singular Value Automata and Approximate Minimization*, arXiv:1711.05994v2](https://arxiv.org/abs/1711.05994v2)，§2、Theorem 2.1 的有限表示与 Hankel 秩对应。后者供应经典表示背景，不是本原生守卫障碍的逐字陈述。这里新增的是由原生两条轨道强制的 (252.6)，而非该经典递推工具。∎

**命题 252.4（有限时域与奇异表示的精确边界）。** 对任意 $H\ge0$，(252.4) 在它声明的两轨道测试族内可达到；若允许奇异的固定线性 $\mathrm{null}$ 更新，则全部原生前缀的守卫任务有二维表示。此外，固定可逆仿射 $\mathrm{null}$ 更新与固定仿射合法性读出也不能在有限维仿射空间上满足全部前缀合同。

证明。对有限时域取 $V=\mathbb R^{H+1}$，基为 $b_0,\ldots,b_H$，令 $A$ 作循环置换 $Ab_i=b_{i+1\bmod(H+1)}$，$e(b_i)=\mathbf1_{\{i=0\}}$。置

$$
u=\sum_{i=0}^H b_i,\qquad
v(\mathrm{null}^k)=A^ku=u,\qquad
v([2]\mathrm{null}^k)=A^k(u-b_0).
\tag{252.8}
$$

在 $0\le k\le H$ 恰得 (252.5)。到 $k=H+1$，第二轨道的目标读出返回零而原生目标为一；此构造只实现所声明的两轨道有限测试，不提供其余词的实现。

对全部守卫任务，将接缝零、一编码为 $b_0,b_1\in\mathbb R^2$。每个字母把允许的源基向量送到表中指定的新接缝基向量，把不允许的源基向量送到零；零保持零。初态为 $b_0$。合法前缀始终是对应的一个基向量，因而 $e=(1,0)$ 精确读出 (252.2)，而

$$
A_{\mathrm{null}}=
\begin{pmatrix}1&1\\0&0\end{pmatrix}
\tag{252.9}
$$

是奇异矩阵。归纳同时验证非法前缀吸收于零；如需区别已失败与合法接缝一，另用 $(1,1)$ 读出当前有效性。这个二维表示不承诺恢复组成。组成与合法性联合任务的既有六维表示见关系延拓几何定理 8.2；其 $\mathrm{null}$ 同样将两个接缝块汇入一个块。

最后，将有限维仿射空间选原点写成 $\mathbb R^d$。仿射更新 $z\mapsto Bz+c$ 与仿射读出 $\ell z+a$ 齐次化为

$$
\widehat A=\begin{pmatrix}B&c\\0&1\end{pmatrix},\qquad
\widehat e=(\ell,a),\qquad \widehat v(w)=(v(w),1).
$$

$B$ 可逆使 $\widehat A$ 可逆；全部前缀等式于是违反定理 252.3。这个结论不覆盖非线性合法性读出、依时更新或无限维表示，也不排除把环境、历史或额外记录作为表示的一部分；扩展后若仍声称有限维且满足 (252.3)，仍须接受同一检验。∎

## 253. augmented-J 的局部逆与未实例化的原生拉回

**定义 253.1（完整世界、基点和局部图）。** 取[支持卷 VII §§1–2](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VII.md#1-complete-worlds-and-the-original-joint-question) 的全部严格完整世界

$$
W=(P(r,b),g,d)\in\mathcal H,\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
$$

其中 $0<r<1$、$b>0$、$0\ne g\in\mathbb R[t]$、$\deg g\le3$、$d\in\mathbb R$，并保留该来源最初五个固定读数和原时钟。记

$$
\pi(W)=(p(W),v(W)),\qquad
\Gamma(W)=\Psi_J(W)=(p(W),v(W),a(W)).
\tag{253.1}
$$

$a$ 是同一完整世界的第七时钟 $J$ 响应；$g,d$ 不随目标更换。为避免与世界的 drift $d$ 混淆，本节不用 $d$ 表示维数。[支持卷 VII 定理 24.1 及推论 24.2](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VII.md#24-complete-augmented-j-critical-classification-and-the-nonnegative-p-consequence) 供应

$$
p(W)\ge0\quad\Longrightarrow\quad
\operatorname{rank}d\Gamma_W=2
\tag{253.2}
$$

在完整二维解析 parent 上成立，包括奇异来源；它不是固定 drift 切片的秩断言。[支持卷 VIII §§28–29](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VIII.md#29-a-vanishing-drift-coefficient-and-a-multiple-carrier-root) 的实际 $J$ 弧点满足 $\alpha=\zeta=0$、$F_0\ne0$、$\Lambda_H\ne0$ 且投影载体根为重根；这否定该点的非零线性漂移消元图，不改变 (253.2)，其中负 $b$ 的代数提升 $G$ 也不是严格完整世界。

**命题 253.2（局部来源恢复与原生守卫缺口同时存在）。** 固定任意 $W_0\in\mathcal H$ 且 $p(W_0)\ge0$。存在包含 $W_0$ 的 parent 邻域 $U$，使 $\Gamma|_U$ 单射，且每个确定性完整世界目标 $T:U\to Y$ 在 $\Gamma(U)$ 上唯一下降。然而，对同一个 $U$，存在保留原生合法前缀的来源扩张及其中两个合法状态，具有相同的基点和 augmented-J 边界，下一次 $[5]$ 的合法性却不同。这是静态局部逆不能自动供应原生拉回的失败见证。

证明。由 (253.2)，$p,v,a$ 中某两个分量 $(f,h)$ 在 $W_0$ 的二维 parent 坐标中有非零 Jacobian。经典逆函数定理给缩小后的 $U$，使

$$
\psi=(f,h):U\longrightarrow\Omega\subseteq\mathbb R^2
$$

为微分同胚。于是 $\Gamma|_U$ 单射，且在其实际像上

$$
L_U(q)=\psi^{-1}(\operatorname{pr}_{f,h}q),\qquad
\overline T(q)=T(L_U(q))
\tag{253.3}
$$

恢复来源和目标。这里 $\operatorname{pr}_{f,h}$ 选取秩判据给出的两个分量；对每个 $q\in\Gamma(U)$，有 $\Gamma(L_U(q))=q$，故由 $\Gamma=(p,v,a)$ 得 $\pi(L_U(q))=\operatorname{pr}_{p,v}(q)$。后一个等式恢复基点，不断言 $(p,v)$ 本身给出局部逆，也不断言 $\operatorname{rank}d(p,v)=2$。这个 $L_U$ 的类型是 $\Gamma(U)\to U$，不是原生历史到完整世界的映射；它只在该分支实际像上定义。上述局部逆推导亦是[支持卷 VII §24](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VII.md#24-complete-augmented-j-critical-classification-and-the-nonnegative-p-consequence) 明示的用途，不把它重新列为独立的新定理。

构造扩张

$$
\widehat U=U\times\mathcal P,\qquad
\widehat\pi(W,w)=\pi(W),\qquad
\widehat\Gamma(W,w)=\Gamma(W),\qquad
\widehat G_5(W,w)=G_5(w).
\tag{253.4}
$$

原生追加 $\widehat U_\sigma(W,w)=(W,w\sigma)$ 的定义域严格为

$$
\widehat D_\sigma
=\{(W,w):W\in U,\ w\in\mathcal P,\ w\sigma\in\mathcal P\}.
\tag{253.5}
$$

其中 $W$ 仍是一整个严格世界，未更换其 source、gain 或 drift，$w$ 则独立满足原生全部接缝守卫。取

$$
\widehat x_0=(W_0,\varepsilon),\qquad
\widehat x_1=(W_0,[2]).
$$

两点均在 $\widehat U$，且

$$
\widehat\Gamma(\widehat x_0)=\widehat\Gamma(\widehat x_1),\qquad
\widehat\pi(\widehat x_0)=\widehat\pi(\widehat x_1),\qquad
\widehat G_5(\widehat x_0)=1\ne0=\widehat G_5(\widehat x_1).
\tag{253.6}
$$

因此不存在 $\overline G_5:\widehat\Gamma(\widehat U)\to\{0,1\}$ 恢复该目标，也不存在边界子集 $D_5^B$ 使 $\widehat D_{[5]}=\widehat\Gamma^{-1}(D_5^B)$。若还要求具体的非空原世界来源，可取[支持卷 V](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md) 定理 1.2 的 $W_A$；它满足 $56\le p(W_A)\le58$，故 (253.2) 适用。

扩张 (253.4) 是两份已声明合同的数学直积反模型，不声称它已由原生 FIB 构造或物理协议实现，也不声称 $\Gamma$ 在 $\mathcal H$ 自身有此碰撞。它反驳的仅是“完整世界上的局部静态坐标逆必然恢复新增的原生守卫”。即便将追加后遗忘前缀的投影与 $U$ 上恒等映射作成交换图，(253.6) 的合法域差别仍在；该恒等映射本身也不是原 $J/M$ 时钟操作的识别。∎

**定义 253.3（原生拉回必须满足的方程）。** 要将本卷命题 251.4 实例化，须另外指定一个原生来源域 $S_{\rm nat}$、基点 $\beta_{\rm nat}:S_{\rm nat}\to\pi(U)$、边界 $\gamma:S_{\rm nat}\to\Gamma(U)$、目标 $T_{\rm nat}$，以及映射 $L:S_{\rm nat}\to U$。对每个声明的原生部分操作 $u_\sigma:D_\sigma^{\rm nat}\to S_{\rm nat}$，还须指定同类型来源操作 $U_\sigma:D_\sigma^{\rm src}\to U$。所需等式是

$$
\begin{gathered}
\pi\circ L=\beta_{\rm nat},\qquad
\Gamma\circ L=\gamma,\qquad
T\circ L=T_{\rm nat},\\
D_\sigma^{\rm nat}=L^{-1}(D_\sigma^{\rm src}),\qquad
L(u_\sigma x)=U_\sigma(Lx)\quad(x\in D_\sigma^{\rm nat}).
\end{gathered}
\tag{253.7}
$$

若结论声称边界本身决定合法性，还要求 $D_\sigma^{\rm src}$ 在 $\Gamma$ 纤维上饱和；在单射分支 $U$ 内自动满足这一项。若操作离开 $U$，则必须给出目标分支及那里的边界和图，不能继续套用 $L_U$ 的定义域。完整来源恢复还须 $L$ 对声明的原生来源等价类单射。向原生来源传递某一逃逸对，须两个端点均在 $L$ 的像中，且对应历史可以同时合法提升；正向目标因子化本身不提供这些提升。

**命题 253.4（该来源桥的实际未定项）。** (253.2) 与 (253.3) 只供应 strict-real 分支内部的来源逆。原生高到低窗口与原 $J/M$ 时钟是不同操作合同；没有给出 (253.7) 中的 $S_{\rm nat},L,U_\sigma$ 及其等式时，不能从前者推出原生目标或合法域的拉回。特别地，若原生历史映射 $i:\mathcal P\to S_{\rm nat}$ 满足 $T_{\rm nat}\circ i=G_5$，且候选向量边界 $v=\gamma\circ i$ 服从固定可逆线性 $\mathrm{null}$ 更新，则不能再以固定线性效应 $e$ 恢复该目标。

证明。静态逆的定义域和陪域在 (253.3) 已固定，不能仅靠改名变成 $S_{\rm nat}\to U$。来源扩张 (253.4) 中的投影 $L(W,w)=W$ 保基点，且 $\Gamma L=\widehat\Gamma$，但 (253.6) 排除 $T L=\widehat G_5$ 及精确合法域反像等式。因此前两式不蕴含其余式。对最后一项，若另有 $e(v(w))=T_{\rm nat}(i(w))$，则它等于 $G_5(w)$，与固定可逆 $\mathrm{null}$ 更新共同给出 (252.3)，违反定理 252.3。这里失败的是这些联合假设，不是所有可能的原生拉回。∎

## 254. 对三维载体判据保留的联合义务

**命题 254.1（表示障碍不选择空间维数）。** 定理 252.3 对所有有限线性维数同样成立，因此它本身不能在三维与其他有限维物理配置载体之间作选择。命题 253.2 的 parent 维数二与三个实响应也不能取代本卷定义 250.1 的三维配置—预测证书。

证明。定理 252.3 的量词是全部有限维 $V$；命题 252.4 又给出离开可逆性后确实存在的原生守卫表示。因而被排除的是“有限维、固定可逆更新、固定线性合法性读出、精确全前缀”这一联合合同。物理配置维数没有被这些假设识别为 $\dim V$，不能由此取得空间维数结论。

对于[支持卷 VII 推论 24.2](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VII.md#24-complete-augmented-j-critical-classification-and-the-nonnegative-p-consequence) 中 $p\ge0$ 的严格完整世界，三分量 $\Gamma$ 在二维 parent 上的局部秩为二，只给该来源的局部静态坐标。命题 253.2 已在保留它的局部逆时产生守卫逃逸，故还须先解决 (253.7) 的来源及操作对应。其后，occurrence 到配置载体的注入仍是本卷定义 241.1 与 246.1(4) 的独立假设，统一分辨率须满足定理 241.2、242.1 与 245.1–245.2 的相应 packing 预算；实际运输与 holonomy 仍须满足 §§243–244 及 §249 的条件，细化嵌入与极限紧致性仍是命题 246.2 和定义 250.1(7) 的额外输入。这里没有构造这些桥接数据。

同样，[支持卷 VII §24](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VII.md#24-complete-augmented-j-critical-classification-and-the-nonnegative-p-consequence) 的局部秩结论没有断言跨分支单射；本卷定义 251.2 的 $D_J\cap D_M$ 仍保留同一完整 child 内的两组独立见证对。局部逆、直积反模型与本卷的守卫障碍均未给出该全局集合的存在或排除。任何把这些任务合并的结论都须在同一实际来源、允许历史和共同基点上同时满足它们，不能由各自分立的可达性拼成联合实现。∎

## 255. Native first-disagreement mass forbids a fixed finite-dimensional full-source bridge

**Definition 255.1 (the native source family and mass).** Let $\mathcal S$
be the entire finite native source family generated by the two leaves
$\operatorname{of}(b)$, $b\in\{0,1\}$, and the binary constructor
$\operatorname{mul}(s,t)$. For two sources $s,t$, let
$\operatorname{frontier}(s,t)$ be the existing finite first-disagreement
frontier, and put

$$
\delta_q(s,t)=\sum_{p\in\operatorname{frontier}(s,t)}q^{|p|}.
\tag{255.1}
$$

This is the same `mass` used by
`D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction`; it is
zero on equal sources and positive on every unequal finite pair. The frontier
is prefix-free. The usual Kraft counting argument therefore gives

$$
0\le\delta_q(s,t)\le1\qquad(0<q\le\tfrac12).
\tag{255.2}
$$

No triangle inequality, completeness, or physical interpretation is included
in this definition.

**Theorem 255.2 (uniform finite-dimensional obstruction).** Fix a rational
$0<q\le\tfrac12$. There do not exist a finite-dimensional real normed space
$E$, a map $\Gamma:\mathcal S\to E$, and constants
$0<c\le C<\infty$ such that, for every $s,t\in\mathcal S$,

$$
\boxed{c\,\delta_q(s,t)\le\|\Gamma(s)-\Gamma(t)\|\le C\,\delta_q(s,t).}
\tag{255.3}
$$

**Proof.** If $\dim E=0$, two unequal sources already contradict the lower
bound in (255.3). Assume $d=\dim E\ge1$. For $n\ge0$, let $\mathcal P_n$
be the perfect native trees of depth $n$: $\mathcal P_0$ consists of the two
leaves, and

$$
\mathcal P_{n+1}=\{\operatorname{mul}(s,t):s,t\in\mathcal P_n\}.
\tag{255.4}
$$

The $2^n$ leaves can be labelled independently, so
$|\mathcal P_n|=2^{2^n}$. If $s\ne t$ lie in $\mathcal P_n$, their first
disagreement frontier contains an address of length at most $n$; hence

$$
\delta_q(s,t)\ge q^n.
\tag{255.5}
$$

Choose $s_0\in\mathcal P_n$. By (255.2) and the upper bound in (255.3),
all points $\Gamma(s)$ with $s\in\mathcal P_n$ lie in the norm ball of
radius $C$ about $\Gamma(s_0)$. By (255.5) their pairwise distances are at
least $c q^n$. Disjoint-ball volume comparison in a $d$-dimensional normed
space gives

$$
2^{2^n}
\le\left(1+\frac{2C}{c\,q^n}\right)^d.
\tag{255.6}
$$

The logarithm of the right side is $O(n)$ for fixed $q,c,C,d$, whereas the
logarithm of the left side is $2^n\log2$. This is impossible for all large
$n$. Thus no map satisfying (255.3) exists. \quad$\square$

The finite-scale content is explicit: for every proposed $d,c,C$, choose
$n$ with

$$
2^{2^n}>\left(1+\frac{2C}{c\,q^n}\right)^d;
\tag{255.7}
$$

then the restriction of any candidate to the finite set $\mathcal P_n$
already violates one of the two inequalities. This is a source-faithful
application of the ordinary packing estimate in §245.1. Continuation III
§§90.2–90.7 and §93.2 supply related source-scale and normalized-area packing
arguments; they use different source families or metrics. The present result
uses the entire native `Source` family and its actual first-disagreement mass,
so it is not a new generic packing theorem, a Hilbert-dimension theorem, or a
selection of physical dimension.

The existing native contraction remains a separate statement:

$$
\delta_q(\rho^{2k}s,\rho^{2k}t)\le(2q)^k\delta_q(s,t),
\qquad k\in\mathbb N,
\tag{255.8}
$$

where $\rho$ is the repository's native substitution. At $q=1/2$ this is
only nonexpansive; for $q<1/2$ it is strictly contractive. It does not repair
the full-source obstruction because the obstruction concerns a single
uniform encoding of all finite sources. No map from this source family to the
quantum parameters or to a physical spatial carrier is asserted.

## 256. Restricted contraction transfer and the remaining bridge obligations

The preceding theorem rules out the two-sided bridge on the whole finite
native family. A restricted source domain can still be studied, but it must be
declared before any transfer claim.

### Definition 256.1 (discounted native mass)

For the existing source family and rational $0<q\le\tfrac12$, use the
$\delta_q$ of (255.1). Equal sources have mass zero; distinct finite sources
have positive mass. The two-step estimate and its iterates are precisely the
existing `NativeMismatchContraction` results, not a new Lean wrapper:

$$
\delta_q(\rho^2s,\rho^2t)\le2q\,\delta_q(s,t),\qquad
\delta_q(\rho^{2k}s,\rho^{2k}t)\le(2q)^k\delta_q(s,t).
\tag{256.1}
$$

### Definition 256.2 (a restricted resolution-preserving boundary)

Let $S_0\subseteq\mathcal S$ be a declared source domain, $E$ a normed space,
and $\Gamma:S_0\to E$ a boundary encoding. It is a $q$-resolution bridge on
$S_0$ only when there are fixed constants $0<c\le C<\infty$ such that

$$
c\,\delta_q(s,t)\le\|\Gamma(s)-\Gamma(t)\|\le C\,\delta_q(s,t)
\qquad(s,t\in S_0),
\tag{256.2}
$$

and a declared update $T$ on $\Gamma(S_0)$ satisfies

$$
\Gamma(\rho^2s)=T(\Gamma(s))
\qquad(s,\rho^2s\in S_0).
\tag{256.3}
$$

The lower bound, upper bound, and update equation are separate obligations.
Theorem 255.2 says that (256.2) cannot hold when $S_0=\mathcal S$ and $E$
has finite dimension.

### Proposition 256.3 (transfer on the realized boundary image)

Assume $S_0$ is closed under $\rho^2$ and (256.2)–(256.3) hold. Then for
all $s,t\in S_0$ and $k\in\mathbb N$,

$$
\|T^k\Gamma(s)-T^k\Gamma(t)\|
\le C(2q)^k\delta_q(s,t)
\le \frac Cc(2q)^k\|\Gamma(s)-\Gamma(t)\|.
\tag{256.4}
$$

**Proof.** The update equation gives
$T^k\Gamma(s)=\Gamma(\rho^{2k}s)$ by induction. Apply the upper bridge
bound, then the existing contraction (256.1), then the lower bridge bound.
\quad$\square$

This conclusion is only on the realized image. Extending $T$ to all of $E$,
or requiring linearity, continuity, a norm bound, or a closed domain, requires
separate evidence. An upper-bound-only encoding may control a resolution cost,
but it supplies neither injectivity/source recovery nor task/update
factorization.

### Proposition 256.4 (the bridge does not choose physical dimension)

Proposition 256.3 is valid for every normed target dimension in which a
restricted bridge is actually supplied. It does not identify any target
coordinate with a physical spatial direction, prove integrability of local
frames, or establish holonomy, operation, clock, or source recovery. The
canonical quantum obstructions in VII §239 and VIII §240 use their own
preparation and operation contracts; no map from the native tree `Source` or
$\delta_q$ to their parameters is declared here. They therefore exclude
neither abstract encodings nor every record-keeping protocol.

The remaining bridge obligations are the declared source domain, the two
uniform constants, update commutation, lawful operation correspondence, and
any requested holonomy or limit certificate. A finite-dimensional restricted
encoding can be proposed only after those data are supplied; the full-source
claim is already refuted by Theorem 255.2.

## 256.99 追加锚（本行以下为增补区）

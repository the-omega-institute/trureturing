# Fibonacci 规范窗口与编译几何

**定位与证明范围。** 本卷研究 Fibonacci 正接枝的实际词编译、同源观察的商与恢复，以及规范低位窗在普通加法下的连续和固定稀疏记录。正文是参考输入与普通数学证明，未经 Lean kernel 验证；不主张 Robin 不等式或黎曼猜想的证明。

**对象与来源合同。** 正接枝以实际非负整数组成为来源，使用替换矩阵、原子接枝、同源重置和唯一终端完整 gcd 答复；收费问数、执行字母、实际前缀与控制空间各按正文合同计量。有序树、组成与数量是不同恢复目标，非空树的组成域去掉原点。规范低位窗则观察同一个实际自然数在普通加法时刻的规范 Fibonacci 数位；固定稀疏时刻不依赖读数。来源上界、终止标记、共同来源、端点归属、紧性与资源限制只在明确给出的假设内使用。

**引用命名空间。** 未带外部来源链接的章节号与条目号均为本卷局部编号。母卷《[Fibonacci 原子关系生成](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)》的引用保留其原编号；[过程几何卷](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)、[动态边界卷](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md)和[恢复几何卷](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)的具名条目同样属于各自卷。上述四卷固定于修订 `5f1ab91c544d8be1f123accd453787f0819fd47d`，正文链接定位该修订的原条目，均不指向本卷的同号条目。

**引用前提与适用边界。** 无限柱集引用保留修订 `cd4bbbef4e52b52ce922b848cd52601c839d2918`，并在对应假设中给出完整的端点流与有限来源映射；Dirichlet 素数定理保留正文所列 Mathlib 修订及参数对应。引用形式化声明不等于本卷的普通证明已被形式化；逐层可分离、存在相容线程、存在实际来源和有限可认证性分别按各自命题的条件判断。

**追加约定。** 卷首与既有正文合入后保留原字节；增补和勘误写在文末追加锚之后，以递增的新章节和条目编号指向所补充或修正的旧条目，并以同一追加锚结尾。


## 1. 增补一·正 Fibonacci 接枝的对数长度编译器

**本批导航。** 本批在 §[133.5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13358) 的同源重置、终端完整 gcd、实际非负来源契约上继续。§1.1 给出线性长度的正接枝基线，§1.2 给出从辅助 Fibonacci 项开始的非邻接表示，§1.3 消去不可执行的单位权，§1.4 把表示编译为两根共同正方向的实际词，§1.5 解码原始组成，§1.6 保留准确问数，§1.7 计数执行字母，§1.8 计数实际前缀与控制空间。旧的阶乘周期编译器仍按其原范围成立；本批只增补一个较短的执行实现，不改判 §[133.5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13358) 的问数结论。

### 1.1. S1：精确的时间顺序动作与有限线性编译器

**定理 1.1（正向线性偏移编译）。** 对任意 $k\ge1$、$A,B\ge0$，下述时间顺序词给出精确偏移 $3A+2B$；每个模 $H>1$ 的偏移都有一个非负代表，所需接枝数至多 $\lfloor(H+1)/2\rfloor$。

**证明。** 记

$$
F_0=0,\qquad F_1=1,\qquad F_{j+2}=F_{j+1}+F_j,
$$

并沿用

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
\alpha=(1,0),\qquad q=(2,3),
$$

以及实际操作 $R(x)=Mx$、$G(x)=x+\alpha$。对任意 $k\ge1$ 和 $A,B\ge0$，按时间顺序执行

$$
R^{k-1},\quad G^A,\quad R,\quad G^B .
$$

这里的幂只是实际重复字母的简写。四个区块之后的状态依次为

$$
M^{k-1}v,\quad M^{k-1}v+A\alpha,\quad
M^kv+A M\alpha,\quad M^kv+A M\alpha+B\alpha .
$$

因为 $M\alpha=(0,1)$、$qM\alpha=3$、$q\alpha=2$，末端标量的整数等式是

$$
q\bigl(W(v)\bigr)=qM^kv+3A+2B .
$$

这不是只在模 $H$ 中成立的记号恒等式，而是对每个实际非负中间状态成立的完整动作计算。

当 $H>1$ 时，对 $c\in\{0,1,\ldots,H-1\}$ 取

$$
 t(c)=
 \begin{cases}
 0,&c=0,\\
 H+1,&c=1,\\
 c,&2\le c<H.
 \end{cases}
$$

于是 $t(c)\equiv c\pmod H$，且 $t(c)$ 要么为零，要么至少为二。$t=0$ 时取 $A=B=0$；$t\ge2$ 为偶数时取 $A=0,B=t/2$；$t\ge3$ 为奇数时取 $A=1,B=(t-3)/2$。所有系数都非负，并且

$$
3A+2B=t(c),\qquad A+B=\left\lfloor\frac{t(c)}2\right\rfloor
 \le\left\lfloor\frac{H+1}2\right\rfloor .
$$

因此一次词的终端响应正好是

$$
\gcd\bigl(qM^kv+c,H\bigr),
$$

它有 $k$ 个实际 $R$ 字母和至多 $k+\lfloor(H+1)/2\rfloor$ 个实际 $G$ 字母。$c=1$ 使用 $H+1$，从而没有执行不可用的单位偏移。取 $k=1,2$ 并使用 §[133.5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13358) 的标量策略，便得到一个有限的 $O(H)$ 字母编译器。这是本批对旧有限存在结论的保留；后面的 Fibonacci 编译器只改善执行上界，既不追溯改变旧词的成本，也不宣称旧词或新词的最短性。

### 1.2. S2：从辅助一开始的非邻接 Fibonacci 表示

**引理 1.2（辅助一的非邻接表示）。** 若 $N\ge2$ 且 $0\le u<F_{N+1}$，则 $u$ 是指标 $2$ 到 $N$ 的互异、非邻接 Fibonacci 项之和。

**证明。** 对所有 $j\ge0$，有

$$
qM^j=(F_{j+3},F_{j+4}),\qquad qM^j\alpha=F_{j+3}.
$$

事实上，$q=(2,3)=(F_3,F_4)$，而行向量 $(x,y)$ 右乘 $M$ 变成 $(y,x+y)$，所以归纳得到第一式；第二式只取第一坐标。因此，接枝在之后经历 $j$ 个 $R$ 时所贡献的可用权重依次为 $F_3,F_4,F_5,\ldots=2,3,5,\ldots$。

下面给出需要的表示事实。若 $N\ge2$ 且 $0\le u<F_{N+1}$，则存在一组系数 $\varepsilon_i\in\{0,1\}$，使得

$$
 u=\sum_{i=2}^{N}\varepsilon_iF_i,
$$

并且任意两个非零系数的指标不相邻。这里只需存在性，不使用唯一性。

从剩余量的贪心下降开始。$u=0$ 时取空和。若剩余量为正，取最大的 $j\ge2$ 使 $F_j$ 不超过它。Fibonacci 数列从 $F_2$ 起严格递增并无界；例如 $F_{j+2}\ge2F_j$（$j\ge2$），所以这个指标存在且有限。当初始量小于 $F_{N+1}$ 时，最大指标不超过 $N$。若 $j=2$，剩余量只能是 $1$，减去 $F_2$ 后为零。若 $j\ge3$，最大性给出

$$
0\le u-F_j<F_{j-1}.
$$

所以后续若仍有非零项，其指标至多为 $j-2$；指标 $j-1$ 不会被选。每次选择都严格减少非负剩余量，归纳必然终止于零，且每次都保留精确和与非邻接性。这一段的 $F_2=1$ 只是数值表示中的辅助项，尚未被当作实际操作。

### 1.3. S3：去除不可用的单位权并控制接枝数

**定理 1.3（正 Fibonacci 接枝表示）。** 对 $H>1$，令 $K$ 与 $\gamma$ 如下；每个模 $H$ 偏移都由权重 $2,3,5,\ldots,F_{K+3}$ 的非负实际接枝表示，接枝总数至多 $\gamma$。

**证明。** 对 $H>1$ 置

$$
K=\min\{k\ge1:F_{k+4}\ge H\},\qquad
\gamma=1+\left\lceil\frac{K+1}{2}\right\rceil .
$$

Fibonacci 数列无界，故 $K$ 有限；$K\ge1$ 同时提供权重 $F_3=2$ 与 $F_4=3$。对 $c\ne0$，有 $2\le t(c)\le H+1$，令 $u=t(c)-2$，则

$$
0\le u\le H-1<F_{K+4}.
$$

由 1.2 取 $N=K+3$，得到

$$
 u=\sum_{i=2}^{K+3}\varepsilon_iF_i,\qquad
\varepsilon_i\in\{0,1\},\qquad
\varepsilon_i\varepsilon_{i+1}=0.
$$

把辅助项 $F_2=1$ 与预留的权重 $2$ 合并。定义

$$
 d_0=\varepsilon_3+1-\varepsilon_2,\qquad
 d_1=\varepsilon_4+\varepsilon_2,\qquad
 d_j=\varepsilon_{j+3}\quad(2\le j\le K).
$$

这是恒等式

$$
2+\varepsilon_2=2(1-\varepsilon_2)+3\varepsilon_2
$$

在整数和中的改写，而不是执行一次权重一的接枝。于是

$$
 t(c)=\sum_{j=0}^{K}d_jF_{j+3}.
$$

非邻接性保证当 $\varepsilon_2=1$ 时 $\varepsilon_3=0$，所以 $d_0$ 从不为负；其余系数也显然非负。并且

$$
 d_0,d_1\in\{0,1,2\},\qquad d_j\in\{0,1\}\ (j\ge2).
$$

接枝总数满足

$$
\sum_{j=0}^{K}d_j
 =1+\sum_{i=3}^{K+3}\varepsilon_i.
$$

指标区间 $3,4,\ldots,K+3$ 有 $K+1$ 个位置，非邻接的选点至多为 $\lceil(K+1)/2\rceil$：将相邻位置成对，每对至多选一个，若有余数再留一个单点。因此 $\sum_jd_j\le\gamma$。

当 $c=0$ 时直接取全部 $d_j=0$。当 $K=1$ 时表示区间正是 $2,3,4$；$u=0$ 给出一个权重 $2$，$u=1$ 给出一个权重 $3$，上述公式仍逐项成立。特别地，$c=1$ 使用 $t(1)=H+1$，从未要求把 $1$ 作为实际权重。这样所有模 $H$ 偏移都由正实际接枝表示，且没有执行单位接枝。

### 1.4. S4：两根共同正方向上的实际短词

**定理 1.4（共同正方向的实际词）。** 对 $k=K,K+1$ 与任意模 $H$ 偏移，存在只含正向 $R,G$ 的实际词，恰有 $k$ 个 $R$，至多 $\gamma$ 个 $G$，并返回 $\gcd(qM^kv+c,H)$。

**证明。** 取 1.3 的系数。对 $k=K$ 或 $k=K+1$，在后一种情形补定义 $d_{K+1}=0$，按时间顺序执行

$$
W(k,c)=G^{d_k},R,G^{d_{k-1}},R,\ldots,R,G^{d_1},R,G^{d_0}.
$$

每个 $G^{d_j}$ 都代表 $d_j$ 个实际的原始 $\alpha$ 接枝；$G^2$ 是两个字母，不是宏指令。词中恰有 $k$ 个 $R$。标号为 $j$ 的接枝块之后还剩恰好 $j$ 个 $R$，所以其最终贡献为 $M^j\alpha$。逐块归纳得到实际整数状态

$$
W(k,c)(v)=M^kv+\sum_{j=0}^{k}d_jM^j\alpha,
$$

其中 $k=K+1$ 时最前面的空块 $G^{d_{K+1}}$ 只产生一个额外的首个 $R$，不改变任何后续接枝所经历的 $R$ 数目。应用 $q$、1.2 与 1.3，得到

$$
q(W(k,c)(v))=qM^kv+\sum_{j=0}^{K}d_jF_{j+3}
=qM^kv+t(c).
$$

故一次完整词末只读一次 gcd 就返回

$$
\gcd(qM^kv+c,H).
$$

$R$ 与 $G$ 都把 $\mathbb N^2$ 映入自身：$R(a,b)=(b,a+b)$，$G(a,b)=(a+1,b)$。因此包括精确零来源和零偏移在内，每个实际前缀都是合法非负状态。词内没有任何块间观察，也没有把实际中间量替换成模代表。对 $c=0$，词就是收费的 $R^k$；它仍提供正确的零偏移终端响应。

### 1.5. S5：连续两行的原始组成解码

**定理 1.5（连续两行的可逆解码）。** $D_K$ 的两行在每个模 $H$ 上构成可逆矩阵，并从两个同源标量剩余恢复原始组成剩余。

**证明。** 令

$$
C=\begin{pmatrix}2&3\\3&5\end{pmatrix},\qquad
D_K=C M^K.
$$

因为 $\det C=1$、$\det M=-1$，有

$$
D_K=
\begin{pmatrix}
F_{K+3}&F_{K+4}\\
F_{K+4}&F_{K+5}
\end{pmatrix},\qquad
\det D_K=(-1)^K.
$$

因此 $D_K$ 在每个模 $H$（包括合数及其全部素数幂分量）上都可逆。若两个标量阶段分别恢复

$$
 y_0=qM^Kv,\qquad y_1=qM^{K+1}v\pmod H,
$$

则原始来源的组成剩余由伴随矩阵给出：

$$
 a=(-1)^K\bigl(F_{K+5}y_0-F_{K+4}y_1\bigr)\pmod H,
$$

$$
 b=(-1)^K\bigl(-F_{K+4}y_0+F_{K+3}y_1\bigr)\pmod H.
$$

这里的逆、减法与乘法只发生在控制器对已取得剩余的算术中；没有对实际来源执行逆操作、负接枝或额外查询。每个词都从同一个原始实际 $v$ 重置，故两行确实是同一来源的 $D_Kv$，而不是把两个不相容来源的局部答案拼接起来。

### 1.6. S6：不改变准确问数的逐位与 CRT 策略

**定理 1.6（短词实现准确问数）。** 在 §[133.5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13358) 的完整契约下，短词策略的最坏收费查询数为 $Q(1)=0$、$Q(H)=2B(H)$（$H>1$）。

**证明。** 设 $H>1$，写成互素素数幂 $P=p^e$ 的乘积，并记

$$
B(H)=\max_{p^e\parallel H}e(p-1).
$$

先恢复 $y=qM^Kv$，再恢复 $y=qM^{K+1}v$。每个阶段内所有素数幂分量使用同一个固定的 $k$；局部轴只能选择偏移，不能选择另一根方向。

在一条 $p^e$ 轴上，维护不变量

$$
 y\equiv r\pmod{p^s},\qquad 0\le r<p^s.
$$

初始 $(r,s)=(0,0)$ 只是模一的空前缀，不是免费观察。若 $s<e$，按 $d=0,1,\ldots,p-2$ 依次测试

$$
 c_p=-r-dp^s\pmod{p^e}.
$$

写 $y=r+p^su$。测试的数值在该轴上为 $p^s(u-d)$，所以完整截断赋值不低于 $s$；当下一位不等于 $d$ 时恰为 $s$，当下一位等于 $d$ 时至少为 $s+1$，并包括一直到饱和深度 $e$ 的所有匹配响应。匹配后作同时更新

$$
(r,s)\longleftarrow(r+d p^s,s+1),
$$

右侧两个位置都使用更新前的 $s$。若前 $p-1$ 个候选都失败，剩余位必是 $p-1$，直接作同一更新而不再收费一次。于是每层至多 $p-1$ 个完整响应，全部 $e$ 层至多 $e(p-1)$ 个查询；零响应、饱和响应和中途超过下一位的深度都已包含在这个分支中。

各轴在每轮给出自己的局部偏移。尚未完成的轴使用上式，已经完成的轴使用已恢复的 $y_p$ 取 $c_p=-y_p\pmod{p^e}$，从而该轴的响应是已知的饱和值。CRT 只把这些偏移合成为一个 $c\pmod H$，再由 1.4 用一个实际短词实现；一次 gcd 的每个素数指数正是相应轴要求的局部响应。没有把独立选择的局部行向量或独立来源假定成可执行对象。每个阶段至多 $B(H)$ 轮，两阶段至多 $2B(H)$ 个收费查询，随后用 1.5 解码。

这个上界的策略自身也有达到 $2B(H)$ 的实际来源。取模 $H$ 的唯一剩余对 $v_*$ 满足

$$
D_Kv_*\equiv(-1,-1)\pmod H,
$$

再取其坐标的非负代表。这是一个共同的实际来源。对任意素数幂轴，两阶段的标量都是 $-1$；在层 $s$，已知前缀为 $p^s-1$，下一位为 $p-1$，所以 $d=0,\ldots,p-2$ 的每次测试都恰给深度 $s$。达到最大值 $B(H)$ 的轴迫使每个阶段各用 $B(H)$ 轮，策略在该来源上用满 $2B(H)$ 个查询。

全体允许策略的下界直接复用已接受的 §[133.5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13358) 下界：来源域仍是包含零的 $\mathbb N^2$，目标仍是精确的完整组成剩余，词仍是任意有限正向词，回答仍是同源重置后唯一的终端完整 gcd，且没有初始读数或中间侧信息。改变上界所选的两根正方向只改变策略中的合法词，不改变下界所覆盖的策略类。因此

$$
Q(1)=0,\qquad Q(H)=2B(H)\quad(H>1).
$$

这里没有另立一份下界证明，也没有把两个不相容的困难分支拼成一个来源。

### 1.7. S7：执行字母的精确上界与对数化

**定理 1.7（执行字母上界）。** 对 $H>1$，总执行字母数至多 $(2K+1+2\gamma)B(H)$；当 $H\ge3$ 时每词至多 $3m-2$、总数至多 $(6m-5)B(H)$，其中 $m=\lceil\log_2H\rceil$。

**证明。** 设两阶段实际轮数分别为 $T_0,T_1$，则 $T_0,T_1\le B(H)$。第一阶段方向为 $K$，第二阶段方向为 $K+1$，故实际 $R$ 字母总数恰为

$$
K T_0+(K+1)T_1\le(2K+1)B(H).
$$

每个查询至多有 $\gamma$ 个 $G$ 字母，因此总 $G$ 字母不超过

$$
\gamma(T_0+T_1)\le2\gamma B(H),
$$

总执行字母不超过

$$
(2K+1+2\gamma)B(H).
$$

单个第一阶段查询至多 $K+\gamma$ 个字母，单个第二阶段查询至多 $K+1+\gamma$ 个字母。所有重复幂都按实际字母计数，查询本身和重置另行计费。

对数界来自简单的 Fibonacci 增长。归纳得

$$
F_{2m+1}\ge2^m\qquad(m\ge1)：
$$

$m=1$ 时为 $F_3=2$；若结论在 $m$ 成立，则
$F_{2m+3}=F_{2m+2}+F_{2m+1}\ge2F_{2m+1}\ge2^{m+1}$。当 $H\ge3$、$m=\lceil\log_2H\rceil$ 时，$m\ge2$，并且

$$
F_{(2m-3)+4}=F_{2m+1}\ge2^m\ge H.
$$

所以 $K\le2m-3$，进而 $\gamma\le1+\lceil(2m-2)/2\rceil=m$。代入可得每个查询至多

$$
K+1+\gamma\le3m-2
$$

个字母，总执行字母至多

$$
(2K+1+2\gamma)B(H)\le(6m-5)B(H).
$$

$H=2$ 时 $K=1$ 且 $B(2)=1$。二进制轴在初始层只测试 $d=0$，所以两个阶段都选零偏移；实际词分别是 $R$ 与 $RR$，共两次收费查询和三个执行字母。$H=1$ 时目标只有一个剩余对，直接返回，不执行任何操作。上述全是执行上界；本批没有证明最短词、最少累计字母、查询最优策略中的运行时间 Pareto 最优，或任何更强的复杂度最优性。

### 1.8. S8：实际前缀增长与控制空间的边界

**定理 1.8（实际前缀与控制空间）。** 新编译器的每个实际前缀满足 $q$ 与坐标的显式源依赖上界；因子分解完成后存在 $O((\log H)^2)$ 位的控制器上界，并不提供 $H$-only 来源存储界。

**证明。** 令实际原始来源为 $v=(a,b)\in\mathbb N^2$，并记 $S=a+b$。对 1.4 的任意查询词，$k\le K+1$、$t(c)\le H+1$，所以完整终端标量为

$$
F_{k+3}a+F_{k+4}b+t(c)
\le F_{K+5}(a+b)+H+1.
$$

对任意非负状态 $x=(a',b')$，有

$$
q(Rx)-q(x)=a'+2b'\ge0,\qquad q(Gx)-q(x)=2.
$$

因而 $q$ 沿每个实际前缀单调不减；初始状态、每个重复接枝中间点、每个 $R$ 之后的状态都不超过该词终端量。于是所有实际前缀的每个坐标均满足

$$
0\le a',b'\le F_{K+5}(a+b)+H+1.
$$

还可把系数写成只含 $H$ 的倍数。当 $K=1$ 时 $F_{K+5}=F_6=8\le4H$（$H\ge2$）。当 $K>1$ 时，$K$ 的最小性给出 $F_{K+3}<H$，且

$$
F_{K+5}=2F_{K+3}+F_{K+2}<3H<4H.
$$

故统一有

$$
F_{K+5}(a+b)+H+1\le4H(a+b)+H+1.
$$

这个估计明确依赖未观测的实际 $a+b$；它不是只依赖 $H$ 的来源存储界，也没有把实际中间状态替换成剩余类。它只适用于新的对数长度编译器的单个完整查询词；每次重置都从原始实际来源重新开始，不产生跨重置的单调性结论。$H=1$ 分支没有查询词。

在素数幂分解已经得到之后，可以给出一个控制器空间的存在性上界。$H$ 至多有 $O(\log H)$ 个不同素因子，相关 Fibonacci 表和每个素数幂、前缀、偏移、位号、层号及局部计数器都可用 $O(\log H)$ 位表示；特别地

$$
 e(p-1)\le p^e-1\le H-1.
$$

把 $O(\log H)$ 个这样的字存入表，再保留当前偏移、当前词的系数和第一阶段标量，得到一个直接的 $O((\log H)^2)$ 位控制空间上界。CRT 中间量和逆矩阵乘积可随时模 $H$ 约减。该说法的前提是因子分解已经可用；因子分解本身的工作区、重置存储、无界实际来源及其存储不计入此上界，且没有宣称任何空间最优或总比特时间最优。

## 2. 本批的来源、边界与核验范围

**来源与复用。** 本批沿用 §[133](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13281) 的实际组成载体、$M,\alpha,q,C$、同源重置和终端完整 gcd 契约；沿用 §[133.5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13358) 的精确问数及其对任意合法有限词的通用下界；沿用其中的逐位赋值和共同方向 CRT 调度。新的内容是正接枝的 Fibonacci 表示、去除辅助单位权、两根连续正方向的实际词，以及字母数、实际前缀和因子分解后控制空间的上界。旧阶乘编译器仍保留原先的有限存在与原有成本范围。

**契约边界。** $H$ 已知且 $H\ge1$；实际来源固定在包含零的 $\mathbb N^2$；每次查询重置到同一个实际来源；词只含原始正向 $R$ 与原始 $\alpha$-接枝 $G$；只在完整词末返回当前 gcd；空词若使用也收费；没有免费 $n$、$g_0$、前缀、执行中间读数、精确组成、树拓扑、时间侧信道、随机期望成本、噪声或近似目标。控制器的因子分解、整数算术、重置保存和实际来源存储均是另行资源。

**结论边界。** 本批保留

$$
Q(1)=0,\qquad Q(H)=2\max_{p^e\parallel H}e(p-1)\quad(H>1),
$$

并给出正实际词的显式执行上界；它没有声称最短执行、累计字母最优、控制器算术最优、来源存储最优、随机或近似变体、无界精确组成恢复、RH 或任何经验结论。本文只讨论上述来源、操作和资源合同内的数学命题。

**本批与既有结论的关系。** 追加内容不改判 §§[132](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13138)–[133](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13281) 的任何已接受命题。§[133.5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13358) 的下界仍覆盖全部允许策略；1.6 的上界只是把同一局部测试改用一个共同的实际短词执行。所有组成与前缀等式都在实际整数状态上成立，模运算只用于控制器的偏移选择和最终解码。

## 追加锚（本行以下为增补区）

## 3. Actual sources and the one-seed equation quotient

**约定 3.1（Objects, targets and reused structure）。** Throughout §§3–16, $\mathbb N$ includes zero. The ordered tree algebra $\mathcal T$ and its substitution are those of definitions [2.1](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L13) and [3.1](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L39). Write $A=\alpha$ and $B=\beta$ for its two leaves. A tree is finite and nonempty; its ordered binary constructor has neither associativity nor commutativity equations. Its composition is the map $c$ of definition [3.3](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L67). The actual composition domain, action and quantity are

$$
X=\mathbb N^2\setminus\{(0,0)\},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
\rho(a,b)=M(a,b)^{\mathsf T}=(b,a+b),\qquad q(a,b)=2a+3b.
$$

We distinguish the tree action $\rho_{\mathcal T}$ from its composition action $\rho=M$. Every actual quantity is at least 2. Put $P=\{x\in X:q(x)\text{ is prime}\}$; its complement consists exactly of composite quantities. For every positive integer $L$, including $L=1$, define

$$
O_L(x)=q(x)\bmod L,\qquad
\widehat B_L(x)=(O_L(x),O_L(\rho x)),\qquad
F_L(x)=\{y\in X:y\equiv x\pmod L\text{ coordinatewise}\}.
$$

A tower will mean positive integers $L_r$ indexed by $r\in\mathbb N$, with $L_r\mid L_{r+1}$ and $L_r\to\infty$. Its fibers at one fixed actual source are $C_r(x)=F_{L_r}(x)$. The unsubscripted $C$ in §5 denotes a matrix. A universal prime certificate at layer $r$ means $C_r(x)\subseteq P$; a universal composite certificate means $C_r(x)\subseteq X\setminus P$. These are semantic statements about all admissible sources; an executable certificate additionally requires specified observations and proof rules.

The tree recurrence and composition dynamics remain owned by theorems [3.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L51) and [3.4](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L81); the escape pair and inverse observation matrix by theorems [5.1](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L141) and [5.4](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L159) and corollary [5.5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L176). The actual nonnegative fixed-quantity domain is the one described in theorem [117.3](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L10037), here with the origin removed. The arguments below use these results with their stated targets, rather than treating a change of notation as a new recovery theorem. In every comparison of future readings the same actual source is used at all times. A witness may depend on $L$; $\forall L\,\exists y\,\forall k$ does not mean $\exists y\,\forall L\,\forall k$.

**定理 3.2（One seed presents the two-leaf algebra only after the equations）。** Let $U$ be the raw syntax generated by a constant $\alpha_0$, an ordered binary constructor and a unary symbol $R$. Let $\simeq$ be the least congruence for both operations generated by

$$
R^2(\alpha_0)\simeq\langle R(\alpha_0),\alpha_0\rangle,\qquad
R(\langle u,v\rangle)\simeq\langle R(u),R(v)\rangle\quad(u,v\in U).
$$

Then $Q=U/{\simeq}$ is isomorphic to $\mathcal T$ as an algebra with a distinguished constant, binary constructor and unary action. The second leaf corresponds to $[R(\alpha_0)]$.

证明。Define $E:U\to\mathcal T$ recursively by

$$
E(\alpha_0)=A,\qquad E(\langle u,v\rangle)=\langle E(u),E(v)\rangle,\qquad
E(R(u))=\rho_{\mathcal T}(E(u)).
$$

The first equation is preserved because $\rho_{\mathcal T}^2(A)=\langle B,A\rangle$; the second is preserved by the substitution rule. Equality of images is preserved in every unary and binary context, so $E$ descends to $\bar E:Q\to\mathcal T$. Conversely define

$$
I(A)=[\alpha_0],\qquad I(B)=[R(\alpha_0)],\qquad
I(\langle s,t\rangle)=\langle I(s),I(t)\rangle.
$$

Tree induction proves $I(\rho_{\mathcal T}(t))=R(I(t))$. At $A$ both sides are $[R(\alpha_0)]$. At $B$ the assertion is exactly the seed equation. At a binary node it follows from the two induction hypotheses and distribution. Tree induction then gives $\bar E(I(t))=t$. Structural induction on $u\in U$ gives $I(E(u))=[u]$: the constant and binary cases follow from the definitions, and the unary case is

$$
I(E(R(u)))=I(\rho_{\mathcal T}(E(u)))=R(I(E(u)))=[R(u)].
$$

Thus the maps are inverse and preserve all stated operations. Raw terms $R^2(\alpha_0)$ and $\langle R(\alpha_0),\alpha_0\rangle$ remain different syntax trees before quotienting. The inverse maps also show that $A,B$ remain distinct and that no associativity, commutativity or further equality of ordered trees is introduced. $\square$

## 4. Tree action, seed recurrence and composition dynamics

**定义 4.1（Action graph and seed-pair update）。** For any set $Y$ and map $\rho:Y\to Y$, its action graph is $\Gamma_\rho=\{(u,v)\in Y^2:v=\rho(u)\}$. On trees put $T_j=\rho_{\mathcal T}^j(A)$. The seed recurrence of theorem [3.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L51) gives

$$
T_0=A,\quad T_1=B,\quad T_{j+2}=\langle T_{j+1},T_j\rangle,
\qquad
(T_j,T_{j+1})\longmapsto(T_{j+1},\langle T_{j+1},T_j\rangle).
$$

The displayed pair operation is a map $\mathcal T^2\to\mathcal T^2$, whereas $\Gamma_\rho$ records an action on single states of a specified carrier.

**命题 4.2（The exact scope of the recurrence）。** The seed recurrence holds for every $j\ge0$. For every tree, $c(\rho_{\mathcal T}(t))=Mc(t)$; every element of $X$ is realized by a tree. For every $x\in X$, the scalar sequence $s_j=q(M^jx)$ satisfies $s_{j+2}=s_{j+1}+s_j$. The corresponding ordered-tree equation need not hold away from the seed orbit.

证明。For the first claim, apply $\rho_{\mathcal T}^j$ to the seed equation. Induction on $j$ shows that its iterates distribute across the constructor, giving the stated recurrence. This is the application of theorem [3.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L51) to definition 4.1. For composition, the two leaves give $(1,0)\mapsto(0,1)$ and $(0,1)\mapsto(1,1)$; at a node, add the two induction hypotheses and use linearity of $M$. This is precisely theorem [3.4](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L81). Given $(a,b)\in X$, choose $a+b>0$ leaves, of which $a$ are $A$ and $b$ are $B$, and join them with any fixed ordered binary bracketing. The resulting tree has that composition.

The identity $M^2=M+I$ gives $M^{j+2}x=M^{j+1}x+M^jx$; applying the linear map $q$ gives the scalar recurrence. For the tree $t=\langle A,B\rangle$, however,

$$
\begin{aligned}
\rho_{\mathcal T}^2(t)&=\langle\langle B,A\rangle,\langle\langle B,A\rangle,B\rangle\rangle,\\
\langle\rho_{\mathcal T}(t),t\rangle
&=\langle\langle B,\langle B,A\rangle\rangle,\langle A,B\rangle\rangle.
\end{aligned}
$$

Their left children differ in free syntax. Equal compositions therefore do not establish the universal ordered-tree equation. $\square$

**命题 4.3（Injectivity and the actual image）。** The tree action is injective and is not surjective. The composition action on $X$ is injective with image

$$
\rho(X)=\{(u,w)\in X:w\ge u\},
$$

and inverse $(u,w)\mapsto(w-u,u)$ on that image.

证明。No image under $\rho_{\mathcal T}$ is the leaf $A$. The image of $A$ is the leaf $B$. The image of $B$ is $\langle B,A\rangle$, which cannot be an image of a binary node because its right child would have to be an image equal to $A$. Thus equal images either identify the same leaf or are images of two binary nodes. In the latter case their corresponding child images are equal, and induction on the trees identifies both original children. This proves injectivity, while the absence of a predecessor of $A$ proves nonsurjectivity. On compositions, $\rho(a,b)=(b,a+b)$ gives the stated image and inverse directly; for an image point the inverse is nonnegative and is not the origin. Integer or residue-ring invertibility of $M$ consequently does not supply a predecessor for every point of $X$. $\square$

## 5. Escape pairs and the target of double readings

**定义 5.1（Escape from a current observation）。** For an observation $O$ and action $\rho$, an escape pair is a pair $u,v$ with $O(u)=O(v)$ but $O(\rho u)\ne O(\rho v)$.

**命题 5.2（Actual escape and exact reconstruction, reusing §§[5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L139) and [13](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L403)）。** The pair $(3,0),(0,2)$ escapes exact quantity and every $O_L$ with $L>1$. Two exact quantities determine the full composition; their residues modulo $L$ determine exactly its composition residue. These statements do not recover an ordered tree.

证明。Theorem [5.1](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L141) supplies the actual pair: both quantities are 6, while their next quantities are 9 and 10. Actual tree realizations are $\langle A,\langle A,A\rangle\rangle$ and $\langle B,B\rangle$. The difference of next readings is 1, which no $L>1$ divides. For $L=1$ all readings agree, so there is no escape pair.

For $s=q(a,b)$ and $t=q(M(a,b))$, the existing inverse of theorem [5.4](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L159) and corollary [13.3](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L459) is

$$
\binom{s}{t}=C\binom{a}{b},\qquad
C=\begin{pmatrix}2&3\\3&5\end{pmatrix},\qquad
\det C=1,\qquad C^{-1}=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}.
$$

Hence $a=5s-3t$ and $b=-3s+2t$. Both products of the displayed integer matrices equal $I$, so the same inverse identity holds modulo every positive $L$. All subtraction here is in $\mathbb Z$ or $\mathbb Z/L\mathbb Z$, not truncated subtraction in $\mathbb N$. Actual exact readings have nonnegative inverse coordinates that are not both zero; arbitrary integer pairs need not. A single finite modulus gives residues rather than unbounded coordinates.

Finally $\langle A,B\rangle\ne\langle B,A\rangle$ but both have composition $(1,1)$. Proposition 4.2 gives composition $M^k(1,1)$ for both at every time $k$. Their exact scalar trajectories, and therefore every modular scalar trajectory, agree. Composition recovery cannot reverse the information loss of $c$. In particular a current quantity alone cannot define a deterministic first-order scalar update on all of $X$; consecutive quantities provide the second-order scalar state of theorem [5.4](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L159). $\square$

## 6. Temporal observation kernels and stable refinement

**定义 6.1（Temporal prefixes）。** Let $Y$ be a set, $\rho:Y\to Y$ and $O:Y\to A$. For $h\in\mathbb N$, put

$$
B_h(y)=(O(y),O(\rho y),\ldots,O(\rho^h y)),\qquad
R_h=\ker B_h,\qquad
\mathcal P(R)=\{(x,y):(\rho x,\rho y)\in R\}.
$$

Thus $h$ indexes a prefix containing $h+1$ observations. An equivalence $E$ is forward-stable if $xEy$ implies $\rho x\,E\,\rho y$.

**命题 6.2（The reused stable-kernel framework in the single-action setting）。** The temporal relations satisfy

$$
R_h=\bigcap_{k=0}^h\mathcal P^k(R_0),\qquad
R_{h+1}=R_0\cap\mathcal P(R_h),\qquad
R_\infty=\bigcap_{h\ge0}R_h.
$$

The relation $R_\infty$ is the coarsest forward-stable equivalence refining $R_0$. If $Y$ has $m>0$ elements and $R_0$ has $c$ classes, some $h\le m-c$ satisfies $R_h=R_{h+1}=R_\infty$.

证明与归属。This is the single total action, single type, constant edge-label instance of [过程几何卷](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md?plain=1#L235), theorem [6.3](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md?plain=1#L235)(a)–(c); its coarseness is the single-rule case of that volume's theorem [19.8](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md?plain=1#L1062) and of [动态边界卷](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md?plain=1#L105), corollary [2.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md?plain=1#L105). Here is the full specialization. Equality of observation tuples means equality at each coordinate, giving the first formula. Separate time zero from the later times to obtain the recurrence. The relations are equivalences and decrease with $h$.

Their intersection is an equivalence contained in $R_0$. If $xR_\infty y$, equality at time $k+1$ gives equality at time $k$ for $\rho x,\rho y$, proving forward stability and $R_\infty=R_0\cap\mathcal P(R_\infty)$. If $E\subseteq R_0$ is any forward-stable equivalence, induction gives $\rho^kx\,E\,\rho^ky$ from $xEy$. Containment in $R_0$ then gives every observation equality, so $E\subseteq R_\infty$. Thus coarsest means largest as a relation, or least distinguishing among stable refinements.

On a finite $Y$, every strict refinement splits some old class and increases the number of classes by at least one. At most $m-c$ such increases are possible. Hence some $h\le m-c$ has $R_{h+1}=R_h$. Substituting this equality in the recurrence gives $R_{h+2}=R_{h+1}$, and induction gives permanent equality and $R_h=R_\infty$. If $Y$ is empty all the relations agree already. Nothing here requires invertibility of $\rho$, asserts backward stability, or supplies a finite bound on an arbitrary infinite carrier. $\square$

## 7. The discrete behavioral ultrametric and its bounded Bellman extension

**定义 7.1（Discounted observations）。** With $Y,\rho,O$ as in definition 6.1, fix $0<\eta<1$. The original discrepancy is

$$
\delta_{01}(u,v)=\mathbf1_{\{u\ne v\}}.
$$

For this discrepancy define

$$
d_h(x,y)=\max_{0\le k\le h}\eta^k\delta_{01}(O(\rho^kx),O(\rho^ky)),\qquad
d_\infty(x,y)=\sup_{k\ge0}\eta^k\delta_{01}(O(\rho^kx),O(\rho^ky)).
$$

If a distinguishing index exists, $\tau(x,y)$ is its least value; otherwise write $\tau=\infty$ and set $\eta^\infty=0$. This is the same first-distinction construction as definition [5.1](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md?plain=1#L197) and theorem [5.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md?plain=1#L199)(a) of [过程几何卷](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md?plain=1#L197), with a single future path and discount $\eta$ in place of $1/2$. The following proofs spell out the quotient and the separate bounded-discrepancy extension needed for the present observations.

**定理 7.2（Original discrete case and both quotient representatives）。** The discrepancy $\delta_{01}$ is already an ultrametric. Its pullback distance is an ultrapseudometric on $Y$, and

$$
d_\infty(x,y)=\begin{cases}\eta^{\tau(x,y)},&\tau(x,y)<\infty,\\0,&\tau(x,y)=\infty,\end{cases}
\qquad
d_h(x,y)=\begin{cases}\eta^{\tau(x,y)},&\tau(x,y)\le h,\\0,&\tau(x,y)>h\text{ or }\tau(x,y)=\infty.\end{cases}
$$

Its zero relation is $R_\infty$. Consequently $\bar d([x],[y])=d_\infty(x,y)$ is a well-defined genuine ultrametric on $Y/R_\infty$, whether or not observations separate actual states.

证明。The discrete discrepancy is symmetric, nonnegative and zero exactly on equality. If $u\ne w$, at least one of $u\ne v$ and $v\ne w$ holds, so

$$
\delta_{01}(u,w)\le\max\{\delta_{01}(u,v),\delta_{01}(v,w)\}.
$$

The equal-endpoint case follows from nonnegativity. Each discounted pullback has this strong triangle inequality. At each time $k$, its $x,z$ term is at most $\max\{d_\infty(x,y),d_\infty(y,z)\}$; taking the supremum proves the same inequality for $d_\infty$. Nonnegativity, symmetry and zero diagonal follow termwise. The finite maximum gives the same laws for $d_h$.

If $\tau$ is finite, all earlier terms vanish, its own term is $\eta^\tau$, and every later term is at most $\eta^k\le\eta^\tau$. This proves the supremum formula. If there is no distinction every term is zero. Restricting to $0\le k\le h$ proves the finite-prefix formula. Since every finite $\eta^\tau$ is positive, zero distance is exactly equality of every future observation, namely $R_\infty$.

Write $d=d_\infty$. If $xR_\infty x'$, then $d(x,x')=0$, and the ultratriangle gives

$$
d(x,y)\le\max\{d(x,x'),d(x',y)\}=d(x',y).
$$

Interchanging $x,x'$ gives the reverse inequality. If also $yR_\infty y'$, the second argument can be changed independently:

$$
d(x',y)\le\max\{d(x',y'),d(y',y)\}=d(x',y'),
$$

and interchanging $y,y'$ gives the reverse inequality. Thus both choices of representatives preserve distance. Nonnegativity, symmetry and diagonal zero descend. For any representatives $x,y,z$, their ultratriangle descends to the classes. Finally $\bar d([x],[y])=0$ holds exactly when $xR_\infty y$, exactly when $[x]=[y]$. The empty quotient satisfies the laws vacuously. $\square$

**定理 7.3（Additional bounded-discrepancy Bellman theorem）。** Independently of the discrete choice, let $\delta:A\times A\to[0,D]$, where $D\ge0$ is finite. Define $d_h,d_\infty$ by the same formulas with $\delta$ in place of $\delta_{01}$. On bounded real functions on $Y^2$, set

$$
(\Phi f)(x,y)=\max\{\delta(Ox,Oy),\eta f(\rho x,\rho y)\}.
$$

Then $d_\infty$ is its unique bounded fixed point, and

$$
0\le d_\infty-d_h\le D\eta^{h+1},\qquad
\Phi^{h+1}(0)=d_h,\qquad
d_\infty(\rho x,\rho y)\le\eta^{-1}d_\infty(x,y).
$$

If $\delta$ is a pseudometric, the distances are pseudometrics; if it is an ultrapseudometric, they are ultrapseudometrics. If $\delta$ separates observation values, zero infinite distance is exactly $R_\infty$; a genuine metric on $Y$ additionally requires these observations to separate $Y$.

证明。Every term lies in $[0,D]$, so its supremum exists and is bounded. Separate $k=0$ and write $k=j+1$ in the tail. This gives

$$
d_\infty(x,y)=\max\{\delta(Ox,Oy),\eta d_\infty(\rho x,\rho y)\},
$$

so existence is explicit. The map $\Phi$ sends bounded functions to bounded functions. For real $u,v,c$, the inequality $|\max(c,u)-\max(c,v)|\le|u-v|$ follows by considering both arguments below $c$, both above it, or on opposite sides. Therefore

$$
\|\Phi f-\Phi g\|_\infty\le\eta\|f-g\|_\infty.
$$

If $f,g$ are bounded fixed points, their finite supremum distance $A$ satisfies $A\le\eta A$, and $1-\eta>0$ forces $A=0$. On an empty domain uniqueness is immediate. No additional fixed-point existence theorem is needed.

For $k\ge h+1$, the corresponding term is at most $D\eta^{h+1}$. The full supremum is the maximum of $d_h$ and this tail supremum; $d_h\ge0$ gives the difference bound. Induction using $\delta\ge0$ gives $\Phi^{h+1}(0)=d_h$. Reindexing also gives

$$
\eta d_\infty(\rho x,\rho y)
=\sup_{j\ge1}\eta^j\delta(O(\rho^jx),O(\rho^jy))\le d_\infty(x,y).
$$

The factor $\eta^{-1}>1$ is a Lipschitz bound for the action, not a contraction bound for it.

If $\delta$ is a pseudometric, each weighted pullback has diagonal zero and symmetry. At each $k$, its $x,z$ term is at most the sum of its $x,y$ and $y,z$ terms, hence at most $d_\infty(x,y)+d_\infty(y,z)$. Taking the supremum proves the triangle inequality; the finite maximum works in the same way. Under the ultrapseudometric hypothesis, replace this sum by a maximum to get the strong inequality. Since all weights are strictly positive, $d_\infty(x,y)=0$ if and only if every observed discrepancy is zero. With separation in $A$, this is precisely $R_\infty$. It separates actual states only when $R_\infty$ is equality. $\square$

**推论 7.4（Unit error bound in the original model）。** For $\delta_{01}$ the bounded Bellman fixed point is the distance of theorem 7.2, with

$$
0\le d_\infty-d_h\le\eta^{h+1},\qquad
d_\infty(\rho x,\rho y)\le\eta^{-1}d_\infty(x,y).
$$

证明。Apply theorem 7.3 with $D=1$; theorem 7.2 already verifies the discrete ultrametric assumptions. The exponent $h+1$ counts the first unobserved time after times $0,\ldots,h$. $\square$

**命题 7.5（Boundaries of the additional hypotheses）。** Boundedness alone does not imply metric laws; an ordinary metric need not produce an ultrametric; and the altered discount $\eta=1$ need not give uniqueness.

证明。On three values $u,v,w$, assign symmetric distances $\delta(u,v)=\delta(v,w)=1/2$, $\delta(u,w)=1$ and zero diagonal. This is a bounded ordinary metric but violates the strong triangle inequality. With $O$ and $\rho$ both identity, $d_\infty=\delta$, proving the second assertion. An arbitrary bounded discrepancy may instead be nonsymmetric or have nonzero diagonal, and these defects likewise persist for identity maps. For the last assertion take $\delta=0$ and identity $\rho$ at $\eta=1$: every nonnegative constant bounded function is fixed by $\Phi$. The uniform tail coefficient requires a uniform $D$, and coefficient 1 follows from $D\le1$. These examples concern the additional generalization or the changed discount; they do not alter the original assumptions $\delta_{01}$ and $0<\eta<1$. $\square$

## 8. Actual modular classes and two-observation closure

**定理 8.1（Every residue is realized on the nonempty source domain）。** For every positive $L$, $O_L$ has exactly $L$ classes on $X$ and $\widehat B_L$ has exactly $L^2$. Its kernel is coordinatewise congruence modulo $L$. For the temporal relation obtained from $O_L$,

$$
R_{h,L}=R_{1,L}\quad(h\ge1),\qquad R_{\infty,L}=R_{1,L}.
$$

Each actual-source fiber is infinite. This applies corollary [5.5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L176) to the actual domain and includes the additional edge case $L=1$.

证明。Let $\pi_L:X\to(\mathbb Z/L\mathbb Z)^2$ take coordinate residues. Given any pair of residues, choose $0\le a,b<L$. If $(a,b)\ne(0,0)$ it is an actual representative. For the zero pair use $(L,0)\in X$. Thus excluding the origin removes no residue class, including at $L=1$.

For a scalar residue $r$, the residue pair $(-r,r)$ has $2(-r)+3r=r$. Surjectivity of $\pi_L$ therefore proves surjectivity of $O_L$, giving exactly $L$ current classes. By the inverse matrix of theorem [5.4](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L159), written in proposition 5.2,

$$
\widehat B_L=C\pi_L,\qquad
\widehat B_L(x)=\widehat B_L(y)\ \Longleftrightarrow\ \pi_L(x)=\pi_L(y).
$$

Since $C$ is invertible modulo every positive $L$, the double reading is onto the residue-pair space and has exactly $L^2$ classes. No prime-modulus or field assumption is involved.

If $x\equiv y\pmod L$, multiplication by the integer matrix $M$ preserves the congruence; induction gives $M^kx\equiv M^ky$ for all $k$. Applying $q$ gives all future observation equalities for this same $y$. Conversely, equality of all future observations includes times 0 and 1, so the inverse matrix forces $x\equiv y$. The relation is therefore already forward-stable after two observations. In particular

$$
R_{1,L}=R_{0,L}\cap\mathcal P(R_{0,L}),\qquad R_{2,L}=R_{1,L}.
$$

For $L>1$ the first refinement is strict, either from proposition 5.2 or from $L^2>L$. For $L=1$ there is one class from the start. Every class contains infinitely many actual points: from any representative add $(jL,0)$ for $j\in\mathbb N$. Finally the induced action on the finite composition quotient is multiplication by $M$, whose determinant $-1$ is a unit modulo every $L$, so this quotient action is a permutation even though the action on $X$ is not surjective. $\square$

**推论 8.2（Behavioral distance at a fixed modulus）。** Apply theorem 7.2 with $Y=X$, $O=O_L$ and $\rho=M$. The zero-distance classes are precisely $F_L(x)$ and the behavioral quotient is a genuine ultrametric space with $L^2$ points. For $L=1$ it is a singleton. On $X$ itself the distance is only a pseudometric, since its zero classes are infinite.

证明。Theorem 8.1 identifies $R_{\infty,L}$ with coordinatewise congruence. The representative independence and separation on the quotient are exactly those proved in theorem 7.2. $\square$

## 9. Divisibility projections, actual recovery and unrealized threads

**定理 9.1（Finite quotient lifts and commuting maps）。** Suppose $L\mid L'$ and set $m=L'/L$. Coordinate reduction

$$
d_{L',L}:(\mathbb Z/L'\mathbb Z)^2\longrightarrow(\mathbb Z/L\mathbb Z)^2
$$

is onto and each of its fibers has exactly $m^2$ elements. It commutes with the actual residue maps and with $C,M$; under $\widehat B_L=C\pi_L$ it is also the projection of double-reading quotients. A scalar current-reading quotient has $m$ lifts per residue. These counts concern quotient classes, not actual sources.

证明。A representative $0\le a<L$ has precisely the lifts $a+iL$ for $0\le i<m$ modulo $L'$. Any representative reducing to $a$ has this form by division by $L$; two such lifts agree modulo $L'=mL$ only when $m\mid i-j$, which in the stated range forces $i=j$. The two coordinates vary independently, giving $m^2$ lifts. A single coordinate gives $m$.

Reduction commutes with every integer linear map, so

$$
d_{L',L}(\pi_{L'}(x))=\pi_L(x),\qquad
d_{L',L}(Cz)=Cd_{L',L}(z),\qquad
d_{L',L}(Mz)=Md_{L',L}(z).
$$

This proves all the asserted commuting relations, including reduction of both observed quantities. Theorem 8.1 shows that each quotient class itself has infinitely many actual sources. $\square$

**定理 9.2（Injection into the tower and its failure of surjectivity）。** For a positive unbounded divisibility tower, the map

$$
x\longmapsto(\pi_{L_r}(x))_{r\ge0}
$$

is injective from $X$ into the coherent residue threads. The coherent thread $z_r=(-1\bmod L_r,0)$ is not in its image, though every finite prefix of it is realized by an actual source. No finite prefix of this tower uniquely identifies an unrestricted actual composition.

证明。Suppose $x=(a,b)$ and $y=(a',b')$ have equal residues at every layer. Each $L_r$ divides the integer differences $a-a'$ and $b-b'$. If a difference is nonzero, choose $r$ with $L_r$ greater than its absolute value. A positive integer that large cannot divide a smaller nonzero integer. Both differences are zero, proving injection.

The residues of $-1$ and 0 reduce compatibly, so $z$ is coherent. If an actual $(a,b)$ realized it, every $L_r$ would divide $a+1$ and $b$. Choosing $L_r>a+1$ contradicts divisibility of the positive integer $a+1$. Hence there is no actual source for the entire thread. Any finite prefix, however, is realized by an actual representative of its final residue pair, using theorem 8.1; divisibility then gives all earlier coordinates. If the final modulus is 1, the representative pair $(0,0)$ can be replaced by $(1,0)$, so this case is also actual.

At any layer $r$, both $x$ and the distinct point $x+(L_r,0)$ belong to $F_{L_r}(x)$. Every finite set of tower indices is dominated by its largest index. Thus no finite collection of layers gives unique unrestricted composition recovery. This realizes, in the present source domain, the distinction between separation and realization in [动态边界卷](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md?plain=1#L256), proposition [6.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md?plain=1#L256), and [过程几何卷](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md?plain=1#L167), theorem [4.4](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md?plain=1#L167): coherent compatibility is not an actual-source existence theorem. $\square$

## 10. A same-source composite escape at every finite modulus

**定理 10.1（No universal prime certificate on the unrestricted domain）。** Let $x=(a,b)\in X$ have prime quantity $n=q(x)$. For every positive $L$, the one actual source

$$
y_L=(a+Ln,b)
$$

has composite quantity, belongs to $F_L(x)$, and reproduces every future modular reading of $x$:

$$
q(y_L)=n(1+2L),\qquad
\forall k\ge0,\quad O_L(M^ky_L)=O_L(M^kx).
$$

Consequently no finite layer, nor any finite prefix of the divisibility tower, universally certifies primality of $x$ on $X$.

证明。The coordinates are nonnegative and not both zero, so $y_L$ is actual. Its difference from $x$ is $(Ln,0)$, whose coordinates are divisible by $L$. The quantity calculation is

$$
2(a+Ln)+3b=n+2Ln=n(1+2L).
$$

Both factors exceed 1 because $n\ge2$ and $L\ge1$. For every $k$, the coordinates of $M^k(y_L-x)$ remain divisible by $L$ because $M$ has integer entries. Applying $q$ proves the congruence for all times with this same witness. The full all-future fiber therefore contains both $x\in P$ and $y_L\notin P$, not merely two sources sharing a current reading. A finite tower prefix is covered by its last modulus, so the same obstruction applies.

The exact quantifiers are $\forall L\,\exists y_L\,\forall k$. Theorem 9.2 rules out a distinct fixed actual $y$ that would work at all unbounded tower layers. The algebraic construction also gives a composite point for any integer quantity $n\ge2$, but its role here is to obstruct a certificate for a prime source. A known uniform source bound changes the admissible fibers, as specified in §12. $\square$

## 11. Singleton identification and finite worst-case status

**定理 11.1（Failure of worst-case interchange on the actual source tower）。** For each fixed $x\in X$, the fibers $C_r(x)$ are nested and

$$
\bigcap_{r\ge0}C_r(x)=\{x\}.
$$

If $x\in P$, let $f=\mathbf1_P$ and $g=\mathbf1_{X\setminus P}=1-f$. Then

$$
\begin{aligned}
\inf_{y\in C_r(x)}f(y)&=0\quad\text{for every }r,&
\inf_{y\in\bigcap_r C_r(x)}f(y)&=1,\\
\sup_{y\in C_r(x)}g(y)&=1\quad\text{for every }r,&
\sup_{y\in\bigcap_r C_r(x)}g(y)&=0.
\end{aligned}
$$

In particular the corresponding monotone limits of finite-layer extrema differ from the extrema on the intersection.

证明。Divisibility gives $C_{r+1}(x)\subseteq C_r(x)$, and $x$ is in each fiber. A point in their intersection has every residue of $x$, and theorem 9.2 therefore identifies it with $x$. At each finite $r$, theorem 10.1 supplies a composite $y_r\in C_r(x)$. Thus $f$ attains 0 and $g$ attains 1 in that fiber; these are their extreme possible values. On the singleton intersection, $f(x)=1$ and $g(x)=0$.

There is no common wrong-status actual point in all the fibers. The witnesses depend on $r$, and in the displayed construction their quantities are $n(1+2L_r)\to\infty$. Identification by intersection supplies neither a finite stage of identification nor an interchange law for infima or suprema. The sufficient hypotheses for such interchange are stated and proved in §16. $\square$

## 12. Uniform size promises and finite certifying decision trees

**定义 12.1（A uniformly bounded source domain）。** Let $B_0\ge2$ be a known integer and restrict every admissible source to

$$
K_{B_0}=\{(a,b)\in X:2a+3b\le B_0\}.
$$

The bound is part of the common domain promise, not merely a fact true of an unobserved distinguished source.

**命题 12.2（Quantity and composition under a size promise）。** The domain $K_{B_0}$ is finite. If $L>B_0$, then $O_L$ recovers the exact current quantity on $K_{B_0}$, and $\widehat B_L$ recovers the exact composition there. Ordered tree syntax need not be recovered in general: for $B_0\ge5$, the two trees $\langle A,B\rangle$ and $\langle B,A\rangle$ have the same composition and quantity and remain indistinguishable.

证明。The inequalities $a\le B_0/2$ and $b\le B_0/3$ put $K_{B_0}$ in a finite rectangle. Every admissible quantity $n$ satisfies $2\le n\le B_0<L$, so its least nonnegative residue is $n$ itself. A quantity need not determine composition: for $B_0\ge6$, $(3,0)$ and $(0,2)$ both have quantity 6. Double readings instead determine both coordinate residues by theorem 8.1. The promised coordinates are each strictly less than $L$, so their least nonnegative representatives are their actual values. For $B_0\ge5$, proposition 5.2 supplies the distinct ordered trees $\langle A,B\rangle$ and $\langle B,A\rangle$ of the same composition; for smaller bounds the proposition makes no universal nonrecovery claim. $\square$

**命题 12.3（Proper prime divisors and finite arithmetic certificates）。** For $2\le n\le B_0$, compositeness is equivalent to the existence of a prime $p$ such that

$$
p^2\le B_0,\qquad p\mid n,\qquad p<n.
$$

One may replace the first bound by $p^2\le n$. Thus testing all primes up to $\sqrt{B_0}$ for proper divisibility is a finite primality criterion on this domain. The case $n=p$ must be excluded.

证明。A proper prime divisor gives $n=pk$ with $p,k\ge2$, hence compositeness. Conversely write a composite $n$ as $uv$ with $1<u\le v$. Then $u^2\le n\le B_0$. The least divisor of $u$ greater than 1 is prime: otherwise a nontrivial factor would be a smaller divisor of $u$. Call it $p$. It satisfies $p\le u$, $p^2\le n$, $p\mid n$ and $p<n$. These implications give both versions. If a divisibility test returns success at $n=p$, it has not supplied a proper divisor and cannot certify compositeness. The finite list is an arithmetic criterion; an observed or executable certificate also needs the divisibility and properness checks to be permitted actions, or computations on an exactly recovered $n$, with their costs included. $\square$

**定义 12.4（Strict-progress finite-candidate model）。** Let $K$ be a known finite set of actual sources and $\theta:K\to T$ a target. An information state is a nonempty subset $S\subseteq K$ containing the one actual source. An allowed action $a\in\mathcal A(S)$ has a finite positive cost $c(S,a)$ and a deterministic outcome map $o_a:S\to\Omega_a$. Its children are the nonempty outcome classes

$$
S_{a,o}=\{x\in S:o_a(x)=o\}.
$$

The menu $\mathcal A(S)$ is finite; an empty menu is allowed. Because $S$ is finite, only finitely many outcome classes are nonempty. Outcomes restrict the same actual source. If actions or costs depend on additional history, that history must first be incorporated into the information state.

A terminal state has an available valid certificate that $\theta$ is constant on it. In the ideal semantic model all target-homogeneous sets are certified terminals, with the certificate test available and its cost already included or separately represented. For composition recovery these sets are singletons. For prime/composite targets proposition 12.3 can justify arithmetic certificates when its checks are available. Homogeneity without such a check does not assert executability.

At every nonterminal $S$, impose strict progress: each action under consideration has every nonempty child strictly smaller than $S$. A proper certifying decision tree uses these actions and ends at certified terminals on every possible branch.

**定理 12.5（Minimax Bellman recurrence and its exact infinity condition）。** In definition 12.4, the value

$$
V(S)=
\begin{cases}
0,&S\text{ is a certified terminal},\\
\displaystyle\min_{a\in\mathcal A(S)}
\left(c(S,a)+\max_{o:S_{a,o}\ne\varnothing}V(S_{a,o})\right),&\text{otherwise},
\end{cases}
$$

with the empty minimum equal to $+\infty$, is well-defined by induction on $|S|$. It is the minimum worst-case total action cost of a proper finite certifying tree, and is $+\infty$ exactly when no such tree exists in this model. Any policy that makes strict progress and can continue until a terminal uses at most $|S|-1$ actions on a branch.

证明与归属。The same-source candidate fibers and first-step decomposition are the mechanism of [恢复几何卷](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md?plain=1#L1000), definitions [8.1](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md?plain=1#L1000)–[8.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md?plain=1#L1027) and theorem [8.5](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md?plain=1#L1073). That theorem minimizes loss under a fixed hard budget and depth; here the target is the cost of exact certification, and decreasing cardinality supplies the induction. Its budget assumptions are not silently transferred to this model.

Strict progress means every child value is already defined at the inductive step. Use the usual extended-real convention $c+\infty=\infty$. A certified terminal has its zero-action tree and value zero. At a nonterminal root, any proper finite tree first uses some action $a$. In each nonempty outcome class its continuation costs at least the inductively optimal child value. Its worst-case cost is consequently at least

$$
c(S,a)+\max_o V(S_{a,o}),
$$

and hence at least the stated minimum. Conversely, if this minimum is finite, the finite menu attains it at an action whose child values are all finite. Induction supplies an optimal finite tree at each child. There are finitely many children, so joining these trees under $a$ gives a proper finite tree attaining the stated cost.

If no action has finite expression, then each available action has at least one child without a finite certifying tree by induction; an empty menu supplies no tree either. Conversely any finite certifying tree would have given a finite expression at its root. This proves both directions of the $+\infty$ equivalence. A worst-case branch is consistent with one actual source: successive candidate sets are nested and the final one is nonempty, so choose a source in that final set. Its deterministic outcomes realize the entire branch.

Each action strictly decreases a positive integer cardinality. A branch starting at $S$ therefore has at most $|S|-1$ actions if it ends at a terminal. If every nonterminal subset has a progressive action and every singleton is certified, induction supplies such a policy everywhere. There are finitely many subsets and finitely many actions per subset, so their finite costs have a finite maximum $c_{\max}$, with $c_{\max}=0$ if there are no actions. The resulting cost is at most $(|S|-1)c_{\max}$.

At a nonterminal state with nonempty finite menu, an infinite value thus means that every action has an uncertifiable child; one unsuccessful action cannot make the minimum infinite when another certifies. The proof concerns precisely the decreasing-cardinality model, not an unrestricted cyclic Bellman equation. $\square$

**命题 12.6（Finite candidates and positive costs have separate limits）。** Finite candidates need not be distinguishable, and positive costs alone do not force termination. Merely offering a self-loop does not force the optimal cost to be infinite.

证明。Fix a prime source $x$ and its composite escape $y_L$ from theorem 10.1. On the finite candidate set $\{x,y_L\}$, allow only future modular readings at that same $L$. Every such action has identical outcomes at the two differently labeled sources, so none can certify their status. For nontermination, a constant-outcome action of cost 1 on a nonterminal state can be repeated indefinitely without changing the candidate set. For the last assertion, take a two-source state with different targets and offer both that cost-1 self-loop and a cost-1 action that reveals which source is present. The revealing action gives a finite certifying tree despite the offered loop. This last action system is outside the strict-progress hypothesis of theorem 12.5. General systems require a restriction to proper policies, another well-founded rank or a separate termination result. $\square$

## 13. Canonical position, temporal iteration and modulus precision

**约定 13.1（Canonical encoding as a premise）。** Use the canonical Zeckendorf encoding of convention [116.1](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L9779): each $n\in\mathbb N$ has a unique finite-support sequence $b_j(n)\in\{0,1\}$ such that

$$
n=\sum_{j\ge0}b_j(n)F_{j+2},\qquad b_j(n)b_{j+1}(n)=0,
\qquad F_0=0,\quad F_1=1,\quad F_{j+2}=F_{j+1}+F_j.
$$

Existence and uniqueness of this encoding are the named standard premise used here, not a new conclusion. The all-zero sequence encodes 0. The unit, window order, seams and positive End convention are exactly those of definition [104.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L6937) and definition [116.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L9805). We rename the positional observation of definition [116.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L9805) to $Z_\ell$, reserving $O_L$ for modular quantity.

**定义 13.2（Unit and low-to-high windows）。** The unit is $\varepsilon=b_0$, of weight $F_2=1$. Window $j\ge0$ is

$$
w_j=(b_{3j+1},b_{3j+2},b_{3j+3}),
$$

with respective weights $(F_{3j+3},F_{3j+4},F_{3j+5})$. Its possible modes are

$$
\mathsf E=000,\quad\mathsf A=100,\quad\mathsf B=010,\quad
\mathsf C=101,\quad\mathsf D=001.
$$

These window-mode symbols are distinct in type from the tree leaves $A,B$. Internal neighboring bits cannot both be 1. When a first window is read its seam condition is $\varepsilon(w_0)_0=0$; between windows the condition is $(w_j)_2(w_{j+1})_0=0$. Equivalently initialize $s=\varepsilon$, require $s(w_j)_0=0$, and then set $s=(w_j)_2$. At zero window precision there is no seam condition on an unread window.

Put

$$
Z_\ell(n)=(\varepsilon,w_0,\ldots,w_{\ell-1}),\qquad Z_0(n)=(\varepsilon),\qquad
P_\ell(x)=\{y\in X:Z_\ell(q(y))=Z_\ell(q(x))\}.
$$

Thus $Z_\ell$ fixes exactly bits 0 through $3\ell$. Above the canonical end the bits are padded with zero and windows with $\mathsf E$. This supplies digits, not an observed End certificate. On trees the observation is $Z_\ell\circ q\circ c$; it is a code of quantity.

**命题 13.3（Seams, truncation and the exact positional intersection）。** The mode and seam conditions are exactly global nonadjacency. For $0\le\ell\le k$, let $\pi_\ell^k$ retain the unit and first $\ell$ windows. Then

$$
Z_\ell=\pi_\ell^k\circ Z_k,\qquad \pi_\ell^\ell=\mathrm{id},\qquad
\pi_\ell^j\circ\pi_j^k=\pi_\ell^k\quad(\ell\le j\le k),
$$

and for every actual $x$,

$$
P_k(x)\subseteq P_\ell(x),\qquad
\bigcap_{\ell\ge0}P_\ell(x)=\{y\in X:q(y)=q(x)\}.
$$

证明。Every adjacent pair of bit positions lies inside a window, crosses from the unit to the first window, or crosses between two windows. Internal mode legality covers the first kind and the two seam rules cover the other kinds; conversely global nonadjacency supplies all these rules. The truncation equalities follow entry by entry, also when $\ell=0$. Composing them with $q$ shows that equality at precision $k$ implies equality at precision $\ell$. Every fiber contains the same actual $x$.

If $q(y)=q(x)$, uniqueness of the canonical code gives equality of all bits, hence membership in every $P_\ell(x)$. Conversely membership in every fiber first gives the same unit at $\ell=0$. Each other bit belongs to a finite window, so choosing a precision including that window gives equality of that bit as well. The full finite-support sequences agree; their defining sums therefore give $q(y)=q(x)$. This proves both inclusions.

This is the truncation framework of definition [116.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L9805) applied on the domain $X$, using the actual-image target criterion of convention [116.3](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L9840). Its limiting target is quantity: $(3,0)$ and $(0,2)$ both have quantity 6 and agree at all positional precisions. By contrast theorem 11.1 gives a singleton intersection for the double-modulus composition tower. Even that singleton composition does not distinguish the two ordered trees in proposition 5.2. $\square$

**命题 13.4（Zero padding and a separate End certificate）。** The mode $\mathsf E$ consumes three positions and is not a terminator. For positive canonical End, the eligibility flag is initialized by $\chi=\varepsilon$ and updated by

$$
\chi_{\mathrm{new}}=\mathbf1_{\{w_j\ne\mathsf E\}},
$$

without taking a logical OR with the old flag. An empty window word may End positively exactly when $\varepsilon=1$; zero has its separate structural representation. A nonempty positive word can End exactly when its last entire window is nonzero, even if its highest bit is zero. Bare $Z_\ell$ never certifies that every unread higher bit is zero.

证明。The End clauses are the precise convention of definition [104.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L6937), restated in definition [116.2](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L9805). A last zero window must clear eligibility even after a nonzero earlier window, which explains the replacement update. Modes $100$ and $010$ can be last windows although their highest bit is zero. End is a separate terminal query, not a sixth window transition.

For the last assertion, fix a finite $Z_\ell(n)$ and choose a bit position $t>3\ell$ above the entire support of $b(n)$, with at least one zero bit between that support and $t$. Add one bit 1 at $t$ and keep every old bit. The result is finite-support and nonadjacent, and therefore, by the canonical encoding premise, is the canonical code of

$$
n'=n+F_{t+2}>n.
$$

Its unit and first $\ell$ windows have not changed. If $n=q(x)$ for $x\in X$, then $n,n'\ge2$. Every integer at least 2 has a nonzero nonnegative $2,3$ composition: for an even $t'$ use $(t'/2,0)$, and for an odd $t'\ge3$ use $((t'-3)/2,1)$. This is the elementary realization underlying theorem [117.3](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L10037). It supplies an actual $y$ with $q(y)=n'$. The same finite bare positional prefix thus admits a different actual quantity and a nonzero unread bit.

If instead a separate certificate establishes that the observed complete prefix is at its actual canonical End, the unread tail is known to be zero and the sum of its observed bits fixes the quantity. On $X$ this still fixes only the quantity fiber. Merely knowing a farther End position while leaving intervening digits unread is not that complete-prefix certificate. $\square$

**命题 13.5（Three distinct axes and their commuting comparison）。** Temporal precision $h$, positional precision $\ell$ and tower index $r$ refer to different maps. The temporal trajectory is

$$
W(y)=(O(\rho^ky))_{k\ge0},\qquad B_h=p_h\circ W,
$$

where $p_h$ deletes times after $h$; this $W$ is not a canonical positional window. A joint temporal/modular observation can be written

$$
B_{r,h}(x)=(q(M^kx)\bmod L_r)_{0\le k\le h}.
$$

Deleting final temporal entries and reducing residues along divisibility commute. At fixed $r$, increasing $h$ past 1 adds no distinction; increasing $r$ through the unbounded double-reading tower identifies composition. Increasing $\ell$ reads more positions of the same quantity and applies neither $\rho$ nor any operation $n\mapsto n+t$.

证明。Temporal truncation gives the fibers of definition 6.1. Modular reduction gives the maps of theorem 9.1. Entrywise reduction and deletion can be performed in either order, proving the commuting comparison without identifying the indices. The temporal stabilization is theorem 8.1; tower injection is theorem 9.2. Definition 13.2 changes only the number of inspected digits, and proposition 13.3 identifies its full target. For exact $q$, two temporal readings already recover composition by proposition 5.2. None of these observations recovers ordered syntax after the map $c$ has discarded it. $\square$

**约定 13.6（Interpretive scope）。** The established maps concern sets, actions, observations and information. A physical interpretation would additionally need a physical state space and encoding, an operation implementing $\rho$, a measurement implementing $O$, an error and noise model, and a relation between discrete indices, resource costs and physical duration. No such bridge is among these hypotheses. The conclusions therefore supply no physical device, time dilation, speedup or runtime/complexity bound; this is a limit of the supplied premises, not a claim that physical realization is impossible.

## 14. Dirichlet prime witnesses in the same actual composition fiber

**约定 14.1（Named arithmetic premise and parameter map）。** The standard Dirichlet theorem used here says: for a positive modulus $L$, a natural residue $n$ coprime to $L$, and every threshold $N\in\mathbb N$, there is a prime $p>N$ with $p\equiv n\pmod L$. The named source is [`Nat.forall_exists_prime_gt_and_modEq`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/LSeries/PrimesInAP.lean#L463-L465). In its parameter names, the explicit `n` is our threshold $N$, the modulus `q` is our $L$, and the residue `a` is our quantity $n=q(x)$. Positivity gives the premise $L\ne0$, and coprimality supplies `a.Coprime q`. Neither primality of $L$ nor a reduced representative for $n$ is required. The following derivation uses this standard theorem, without an analytic reproof.

**定理 14.2（Unbounded prime quantities lift to the same composition fiber）。** For $x=(a,b)\in X$, put $n=q(x)$. If $\gcd(n,L)=1$, then for every $H\in\mathbb N$ there exists an actual $y\in F_L(x)$ with prime quantity $q(y)>H$. The same $y$ reproduces all future $O_L$ readings of $x$. In particular the fiber contains infinitely many prime actual sources; $x$ itself need not be prime.

证明。The elementary $2,3$ representation used in theorem [117.3](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md?plain=1#L10037) is sufficient in the following explicit form: every integer $t\ge2$ equals $2u+3v$ with $u,v\in\mathbb N$. If $t$ is even take $u=t/2,v=0$; if it is odd take $u=(t-3)/2,v=1$, which is nonnegative because $t\ge3$. The exception $t=1$ explains the threshold needed below.

Set $N=\max\{H,n+L\}$. Apply the named Dirichlet theorem with this threshold, modulus $L$ and residue $n$. It gives a prime $p>N$ congruent to $n$ modulo $L$. Since $p>n+L$, the integer congruence yields

$$
p-n=Lt,\qquad t>1,
$$

so $t$ is a natural integer at least 2. Write $t=2u+3v$ as above and define

$$
y=(a+Lu,b+Lv).
$$

It has nonnegative coordinates and is nonzero because $x$ is. It is coordinatewise congruent to $x$, while

$$
q(y)=n+L(2u+3v)=n+Lt=p>H.
$$

Thus scalar congruence has been lifted to the same actual composition fiber. Theorem 8.1 now gives $O_L(M^ky)=O_L(M^kx)$ for every $k$, with this one witness. If there were only finitely many prime sources in the fiber, their quantities would form a finite set with a maximum. Taking $H$ at least that maximum contradicts the construction. $\square$

**命题 14.3（Exact infinity criterion and its limit）。** For one fixed actual fiber $F_L(x)$, it contains infinitely many prime sources if and only if $\gcd(q(x),L)=1$.

证明。The sufficient direction is theorem 14.2. For necessity let $g=\gcd(n,L)>1$. Every $y\in F_L(x)$ has $q(y)\equiv n\pmod L$, hence $g\mid q(y)$. If $q(y)$ is prime $p$, its only positive divisors are 1 and $p$, so $g=p$. If $g$ is not prime there are no prime sources; if it is prime, all prime sources have the single quantity $g$. Nonnegative solutions of $2u+3v=g$ are finite, since $u\le g/2$ and $v\le g/3$. Thus there cannot be infinitely many prime sources. The proof establishes existence and infinity only; it supplies no bound for the least witnessing prime and no prime-search cost. $\square$

## 15. Which towers eventually certify compositeness

**定理 15.1（Exact sourcewise criterion and the later layer）。** Fix $x\in X$ with composite $n=q(x)$ and a positive unbounded divisibility tower $(L_r)$. The following are equivalent:

1. There exists $r_0$ with $\gcd(n,L_{r_0})>1$.
2. There exists $R$ with $C_R(x)\subseteq X\setminus P$.
3. There exists $R$ such that $C_r(x)\subseteq X\setminus P$ for every $r\ge R$.

If every $L_r$ is coprime to $n$, each finite fiber contains infinitely many prime actual sources.

证明。Assume the first condition. Choose a prime divisor $p$ of $\gcd(n,L_{r_0})$; taking the least divisor greater than 1 proves its existence. Then $p\mid n$ and $p\mid L_{r_0}$. Since $n$ is composite, $p<n$. Divisibility makes $p\mid L_r$ for every $r\ge r_0$. Unboundedness supplies $R\ge r_0$ with $L_R>n$.

For any $y\in C_R(x)$, the quantity has the form $q(y)=n+tL_R$ with $t\in\mathbb Z$. Since $0<n<L_R$ and $q(y)\ge2$, one cannot have $t\le-1$, which would give $q(y)\le n-L_R<0$. Thus $q(y)\ge n>p$. Also $p\mid q(y)$, so it is a proper divisor and $q(y)$ is composite. This proves the second condition. Nestedness gives the third; the third gives the second by taking $r=R$.

For necessity, a layer with $\gcd(n,L_R)=1$ has an actual prime witness by theorem 14.2 and hence cannot certify compositeness. Therefore the second condition implies the first. If every layer is coprime, apply theorem 14.2 independently at each layer to obtain the stated infinite witnesses. All these certificates concern the actual composition fibers; the existence proof does not provide an additional measurement mechanism. $\square$

**推论 15.2（All composite sources versus all prime directions）。** For one fixed tower as above, the following conditions are equivalent:

$$
\begin{aligned}
&\forall x\in X\text{ with composite }q(x),\ \exists R=R(x),\quad
C_R(x)\subseteq X\setminus P;\\
&\forall\text{ primes }p,\ \exists r=r(p),\quad p\mid L_r.
\end{aligned}
$$

This requires a prime to appear as a divisor somewhere. It requires neither all its powers, nor divisibility by every integer modulus, nor a common stage for all composite sources.

证明。If every prime appears, choose a prime divisor $p$ of the composite quantity $n=q(x)$. Some $L_r$ is divisible by $p$, and theorem 15.1 supplies a possibly later $R\ge r$ with $L_R>n$ and universal compositeness. The certificate persists at subsequent layers.

Conversely suppose a prime $p$ divides no $L_r$. Its square is an actual composite quantity. For $p=2$ use $x=(2,0)$, whose quantity is 4. For odd $p$, use

$$
x=((p^2-3)/2,1),\qquad q(x)=p^2.
$$

The first coordinate is a nonnegative integer and the source is nonzero. The only prime divisor of $p^2$ is $p$, so $\gcd(p^2,L_r)=1$ for every $r$. Theorem 14.2 gives prime actual witnesses at every layer, precluding a universal composite certificate. This proves the equivalence with the displayed source-dependent quantifiers. $\square$

**命题 15.3（First contact, missing primes and the composite hypothesis）。** Meeting a prime divisor at one layer does not require that same layer to certify compositeness; unbounded divisibility need not meet every prime; and the composite-source hypothesis cannot be removed from theorem 15.1.

证明。For the first assertion take $x=(3,0)$, $n=6$ and $L=2$. Although $\gcd(n,L)=2$, the actual point $y=(1,0)$ has prime quantity 2 and the same coordinate residues. The persistent divisor and a later modulus greater than $n$ are what the sufficient proof uses.

For the second assertion take distinct primes $p,\ell$ and $L_r=\ell^{r+1}$. The tower is positive, divisibility-ordered and unbounded, but no modulus is divisible by $p$: any prime divisor of a product of copies of $\ell$ is $\ell$. Choose the actual composition of $p^2$ in corollary 15.2. Every layer is coprime to its quantity, so it has no finite universal composite certificate despite singleton identification in the limit.

Finally if $n=p$ is prime and $p\mid L_r$, then $\gcd(n,L_r)>1$ while the fiber still contains the prime source $x$. It cannot be universally composite. More generally a fiber containing its distinguished source cannot certify the opposite status. $\square$

## 16. Compact and finite-domain conditions for finite certificates

**定理 16.1（Closed wrong-target sets and a finite successful layer）。** Let $K$ be a compact topological space, and let $D_r$ be nonempty closed subsets with $D_{r+1}\subseteq D_r$. Let $T\subseteq K$ be the desired target and suppose the wrong-target set $W=K\setminus T$ is closed. If $D_\infty=\bigcap_rD_r\subseteq T$, then $D_R\subseteq T$ for some finite $R$, and for every later index as well. It suffices instead that some $D_{r_0}$ be compact, all later fibers be closed relative to it, and $W\cap D_{r_0}$ be relatively closed.

证明。Use the standard finite-intersection characterization of compactness, the same mechanism used for common actual realizations in [过程几何卷](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md?plain=1#L167), theorem [4.4](https://github.com/the-omega-institute/trureturing/blob/5f1ab91c544d8be1f123accd453787f0819fd47d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md?plain=1#L167)(d). Any finite intersection of the nested $D_r$ is its largest-index member, hence nonempty. Compactness gives nonempty $D_\infty$.

If no finite layer were contained in $T$, then $E_r=D_r\cap W$ would be nonempty closed nested subsets of $K$. They too have the finite-intersection property. Compactness would give a point in

$$
\bigcap_rE_r=D_\infty\cap W,
$$

contradicting $D_\infty\subseteq T$. Thus $E_R$ is empty for some $R$, exactly the required certificate; nestedness preserves it later. The relative version is the identical argument inside $D_{r_0}$. The required orientation is closed wrong target, equivalently open desired target. Closedness of $T$ alone cannot replace it. $\square$

**定理 16.2（Semicontinuity, exact extrema limits and attainment）。** In the compact closed nested-fiber setting of theorem 16.1, let $f:K\to\mathbb R$ be bounded. If $f$ is lower semicontinuous, then

$$
\lim_{r\to\infty}\inf_{D_r}f=\inf_{D_\infty}f,
$$

and all the infima are attained. If $f$ is upper semicontinuous, then

$$
\lim_{r\to\infty}\sup_{D_r}f=\sup_{D_\infty}f,
$$

and all the suprema are attained.

证明。First let $D$ be any nonempty compact closed subset of $K$ and $a=\inf_Df$. For a bounded lower semicontinuous $f$, each

$$
D\cap\{f\le a+1/j\}\qquad(j\ge1)
$$

is nonempty by the definition of infimum, and closed by lower semicontinuity. They are nested. The finite-intersection property yields a point with value at most $a+1/j$ for every $j$, hence at most $a$ and therefore equal to $a$. This proves attainment using compactness, without assuming sequential compactness.

Put $m_r=\min_{D_r}f$. It is nondecreasing and bounded, so $m=\sup_rm_r$ is finite and is its limit. Each $E_r=D_r\cap\{f\le m\}$ is nonempty because a minimizer in $D_r$ has value $m_r\le m$. They are nested and closed. Their intersection contains a point $z\in D_\infty$ with $f(z)\le m$. Conversely $D_\infty\subseteq D_r$ gives $m_r\le\inf_{D_\infty}f$ for every $r$, hence $m\le\inf_{D_\infty}f$. Combining the inequalities yields

$$
m=\inf_{D_\infty}f=f(z).
$$

This proves the infimum identity and attainment on the limit fiber. For upper semicontinuous $f$, apply the result to the lower semicontinuous function $-f$ and negate. The finite-layer suprema are nonincreasing and converge to the attained supremum on the intersection.

For a binary success function $f=\mathbf1_T$, lower semicontinuity is equivalent to openness of $T$: its nontrivial strict superlevel sets are exactly $T$. Equivalently $W$ is closed. If the limit fiber is successful, its infimum is 1; a convergent sequence of infima in $\{0,1\}$ with limit 1 must eventually equal 1, recovering theorem 16.1. Likewise $\mathbf1_W$ is upper semicontinuous exactly when $W$ is closed. Thus lower semicontinuity belongs to minimizing success and upper semicontinuity to maximizing loss. $\square$

**命题 16.3（The closedness and compactness assumptions cannot simply be dropped）。** Compact ambient space alone, a closed target alone, or closed fibers without compactness do not imply theorem 16.1. The same examples delimit the exchange of extrema.

证明。For failure of wrong-target closedness, take $K=[0,1]$, $D_r=[0,1/(r+1)]$, $T=\{0\}$ and $W=(0,1]$. The fibers are nonempty closed nested sets with intersection $\{0\}\subseteq T$, but each finite fiber contains a positive point, so none is contained in $T$. Here $W$ is not closed, although $T$ is. For $f(0)=1$ and $f(t)=0$ at $t>0$, the finite infima are all 0 and the limit-fiber infimum is 1; $f$ is not lower semicontinuous at 0. For $g=1-f$, the finite suprema are 1 and the limit-fiber supremum is 0; $g$ is not upper semicontinuous there.

For failure of closed fibers, again take $K=[0,1]$, but set

$$
D_r=\{1\}\cup(0,1/(r+2)),\qquad T=(1/2,1],\qquad W=[0,1/2].
$$

These nonempty fibers are nested and not closed. Their intersection is $\{1\}\subseteq T$, and $W$ is closed, yet every finite fiber meets $W$. Even the continuous function $f(t)=t$ has finite infima 0 and limit-fiber infimum 1. A compact ambient space has not made these fibers compact closed constraints.

For failure of compactness, take

$$
K=\mathbb R,\qquad D_r=\{0\}\cup[r+1,\infty),\qquad
T=(-1/2,1/2),\qquad W=\mathbb R\setminus T.
$$

Both $D_r$ and $W$ are closed, the full nested intersection satisfies $\bigcap_r D_r=\{0\}\subseteq T$, and every finite fiber meets $W$. This proves that compactness has a separate role. $\square$

**命题 16.4（A known finite candidate set gives eventual equality）。** If all nonempty nested fibers $D_r$ lie in one known finite set $K$, then some finite $D_R$ equals $\bigcap_rD_r$. In particular a singleton intersection is attained at a finite layer; an intersection contained in $T$ gives a finite universal certificate. Every bounded real objective then has eventual exact equality of worst-case values without semicontinuity assumptions.

证明。For every $y\in K$ outside the intersection, choose an index $r_y$ with $y\notin D_{r_y}$. There are only finitely many such points, so choose $R$ at least all their indices, or $R=0$ if there are none. Nestedness excludes all of them from $D_R$, while the intersection is always contained in $D_R$. Thus equality holds. For certification alone one can take the maximum only over the wrong-target points in $K\setminus T$. Eventual equality of sets gives the claimed equality of every objective's extrema.

For the present sources, a known uniform $q\le B_0$ supplies the finite set $K_{B_0}$. A layer $L_R>B_0$ gives $C_R(x)\cap K_{B_0}=\{x\}$ by proposition 12.2. The promise must restrict every admissible source: the fact that each individual natural pair has some finite size does not supply a common known finite candidate set. $\square$

**命题 16.5（The failed hypotheses in the actual residue example）。** Theorem 11.1 does not contradict the compact certificate theorem. With the discrete topology each actual modular composition fiber is noncompact. With the topology generated by tower residue fibers, the set of actual composite sources is not closed at any prime source.

证明。An actual fiber is infinite by theorem 8.1. Its cover by singleton open sets in the discrete topology has no finite subcover, proving noncompactness. In the residue topology fix a prime $x$ and the composite witnesses $y_r$ of theorem 10.1 at $L_r$. For any fixed $s$, whenever $r\ge s$ the difference $y_r-x$ is coordinatewise divisible by $L_s$, so $y_r\in C_s(x)$. These fibers form a neighborhood base, hence $y_r\to x$. The limit is prime and every $y_r$ is composite, so the wrong-target set is not closed. Passing to a compact space of coherent residue threads cannot by itself supply this missing closedness; it also requires a definition of prime status on threads that have no actual source. These are the specific missing hypotheses behind the finite-versus-limit distinction. $\square$

## 追加锚（本行以下为增补区）

## 17. 同源规范低位窗的对象、信息与有限算术

**定义 17.1（规范有限来源）。** 本节起的自然数均包含零。令

$$
F_0=0,\qquad F_1=1,\qquad F_{j+2}=F_{j+1}+F_j,\qquad G_j=F_{j+2}.
$$

于是 $G_0=1,G_1=2$，且 $G_{j+2}=G_{j+1}+G_j$。记 $\mathcal P_m$ 为从低位到高位排列的长 $m$ 二进制词中没有相邻两个 1 的集合，$\mathcal P_0=\{()\}$，并令

$$
V(p)=\sum_{0\le j<m}p_jG_j\qquad(p\in\mathcal P_m).
$$

一个自然数 $N$ 的规范有限展开是满足 $N=\sum_j b_j(N)G_j$ 的有限支撑合法二进制列；高位补零，零的所有数字都为零。其存在唯一性由定理 17.4 给出。定义

$$
q_m(N)=(b_0(N),\ldots,b_{m-1}(N)),\qquad q_0(N)=().
$$

记 $0^m$ 为长 $m$ 的全零词，$m\ge1$ 时记 $e_{m-1}$ 为只有位置 $m-1$ 为 1 的长 $m$ 词。

**定义 17.2（连续记录与固定稀疏记录）。** 对 $m,h\in\mathbb N_0$ 定义

$$
W_{m,h}(N)=(q_m(N+t))_{0\le t\le h}.
$$

这里 $h$ 是向前的普通加法步数，记录含 $h+1$ 次观察。对固定有限集合 $S\subseteq\mathbb N_0$ 定义保留时间坐标的记录

$$
\sigma_{m,S}(N)=(q_m(N+t))_{t\in S}.
$$

每个记录内的全部坐标都作用于同一个实际自然数 $N$；不同坐标不能分别选来源。时刻集合预先固定，不依赖读到的数字。空集合的记录是唯一的空元组。另对 $L\ge1$ 定义最低位连续块

$$
B_L(N)=(b_0(N+s))_{0\le s<L}.
$$

此处 $B_L$ 有 $L$ 个数字，与 $W_{m,h}$ 的 $h+1$ 个窗的计数不同。

**定义 17.3（确定关系与资源）。** 数据 $X$ 一致确定数据 $Y$，是指在 $X$ 的实际取值集合上有一个函数 $f$，使每个 $N\in\mathbb N_0$ 都满足 $f(X(N))=Y(N)$。等价地，

$$
\forall N,N'\in\mathbb N_0,\qquad X(N)=X(N')\Longrightarrow Y(N)=Y(N').
$$

函数存在必给出这一蕴含；反向则将每个实际 $X$ 值送到其全部代表元共同的 $Y$ 值，所得函数良定义。因此，双向确定恰是两种数据在实际自然数集合上的纤维完全相同，并不要求不同类型的数据字面相等。稀疏解码 $D(m,M,S)$ 指 $\sigma_{m,S}$ 确定 $q_M$；稀疏预测 $P(m,M,S)$ 指 $q_M$ 确定 $\sigma_{m,S}$。

正宽度主要范围固定为 $1\le m\le M$，在此范围记

$$
g=G_m,\qquad H=G_M,\qquad T=H-g\ge0.
$$

连续记录的时域变量始终写 $h$，$H$ 表示目标窗的 Fibonacci 数。固定稀疏记录的查询数是 $|S|$，其中时刻零也计一次；仅在 $S\ne\varnothing$ 时定义最晚时刻 $\max S$。一次宽 $m$ 查询返回 $m$ 个原始位，原始位数为 $m|S|$。重复时刻只重复同一坐标，不增加信息。这里的计数不附带运行时间、熵、物理取得成本或自适应决策树的优化定义。解码与预测的目标都是所指定的有限窗或有限记录；不附加来源上界、终止标记或其它来源读数。

**定理 17.4（有限窗值的精确双射）。** 对每个 $k\ge0$，$V$ 将 $\mathcal P_k$ 双射到整数集合 $\{0,\ldots,G_k-1\}$。每个自然数因而有唯一的规范有限展开，允许高位补零；每个 $p\in\mathcal P_k$ 都由实际自然数 $V(p)$ 实现，即 $q_k(V(p))=p$。

证明。$k=0$ 时只有空词，其值为 $0=G_0-1$。$k=1$ 时两词 0、1 的值为 0、1，恰是小于 $G_1=2$ 的自然数。设 $k\ge2$，按最高位分两类。最高位为零时，低 $k-1$ 位任取 $\mathcal P_{k-1}$，归纳给出互不重复的值

$$
0,\ldots,G_{k-1}-1.
$$

最高位为一时，相邻的下一位必须为零，低 $k-2$ 位任取 $\mathcal P_{k-2}$，所得值互不重复且恰为

$$
G_{k-1},\ldots,G_{k-1}+G_{k-2}-1=G_k-1.
$$

两段不交并且连续，故归纳得到双射。正递推使 $G_{k+1}\ge G_k+1$，所以 $G_k$ 无界。给定 $N$，取 $N<G_k$ 即有有限合法展开；两种有限展开补到同一长度后由单射性相同。特别地，$R<G_k$ 的规范展开全部非零位均在位置 $k$ 以下。词 $p$ 的补零已经合法，唯一性便给出 $q_k(V(p))=p$。$\square$

**定义 17.5（有符号坐标与圆周相位）。** 令

$$
\alpha=\frac{\sqrt5-1}{2},\qquad \varphi=1+\alpha=\alpha^{-1},\qquad
\beta=\alpha^2=1-\alpha,\qquad r=-\alpha,
$$

$$
a=-\alpha,\qquad b=\alpha^2,\qquad J=[a,b],\qquad
c_j=(-1)^{j+1}\alpha^{j+2}=-\alpha^2r^j.
$$

以 $\mathbb T=\mathbb R/\mathbb Z$ 为周长一的圆周，$[x]$ 表示相位，$\{x\}$ 表示其在 $[0,1)$ 内的代表。定义

$$
s(N)=\sum_j b_j(N)c_j,\qquad z_N=[N\alpha],\qquad E_k=[-k\alpha]\quad(k\in\mathbb Z).
$$

以后 $E_k$ 的整数下标不是该切点在圆上的排序号。

**定理 17.6（有限严格界与实际加法的相位桥）。** 对所有 $j\ge0$，

$$
c_j=G_j\alpha-F_{j+1}=\varphi G_j-G_{j+1}.
$$

任何有限二进制列 $x$ 的有符号和满足 $-\alpha<\sum_jx_jc_j<\alpha^2$。特别地，对每个实际自然数及其全部普通加法观察，

$$
s(N)\in(a,b),\qquad [s(N)]=z_N,\qquad
[s(N+t)]=z_N+[t\alpha]\quad(t\ge0).
$$

不同整数下标的 $E_k$ 两两不同，而且 $z_N\ne E_k$ 对全部 $N\ge0,k\ge1$ 成立。

证明。$\alpha^2+\alpha=1$，$1/2<\alpha<1$，$b-a=1$。若 $\alpha$ 有理，则 $\sqrt5$ 有理；把其写成最简分数，平方等式迫使分子与分母都被 5 整除，矛盾。故 $\alpha$ 无理。

系数恒等式在 $j=0$ 时是 $\alpha-1=-\alpha^2$，在 $j=1$ 时是 $2\alpha-1=\alpha^3$。$G_j\alpha-F_{j+1}$ 满足 Fibonacci 递推；$c_j$ 也满足，因为 $r^2=r+1$。于是对 $j$ 归纳得到第一等式；利用 $G_{j+1}=G_j+F_{j+1}$ 得到第二等式。

偶位置系数为负，奇位置系数为正，其全部绝对值的和分别为

$$
\sum_{i\ge0}\alpha^{2i+2}=\frac{\alpha^2}{1-\alpha^2}=\alpha,
\qquad
\sum_{i\ge0}\alpha^{2i+3}=\frac{\alpha^3}{1-\alpha^2}=\alpha^2.
$$

有限列在两个奇偶类都遗漏严格正的总量。舍去正项得到的下界严格大于 $-\alpha$，舍去负项得到的上界严格小于 $\alpha^2$。这个论证甚至不需要非相邻条件，也适用于重新从零编号的每个有限尾部。对规范展开求和给出

$$
s(N)=N\alpha-\sum_j b_j(N)F_{j+1}
      =N\varphi-\sum_jb_j(N)G_{j+1}.
$$

两式右侧被减掉的都是整数，因而相位为 $[N\alpha]$。把 $N$ 换成每个实际 $N+t$ 得到同源平移公式，无须把分别实现的图边拼成路径。若 $E_i=E_j$ 且 $i\ne j$，则非零整数倍 $(i-j)\alpha$ 为整数，与无理性矛盾。若 $z_N=E_k$ 且 $k\ge1$，则正整数倍 $(N+k)\alpha$ 为整数，同样矛盾。这也排除了每个 $N+t$ 的端点命中。$\square$

## 18. 前缀柱集、精确切点与无限来源的引用前提

**定义 18.1（完成长度与柱区间）。** 对 $p\in\mathcal P_m$、$m\ge1$，令

$$
s_p=\sum_{j<m}p_jc_j,\qquad
d(p)=\begin{cases}m,&p_{m-1}=0,\\m+1,&p_{m-1}=1,\end{cases}
\qquad I_p=s_p+r^{d(p)}J.
$$

区间记号表示仿射像，即使 $r^{d(p)}$ 为负也不改变其含义。记其有序端点为 $\ell_p,u_p$，并记

$$
\mathcal A_m(p)=\{[x]:\ell_p<x<u_p\},\qquad
\mathcal C_m=\{E_k:1\le k\le G_m\}.
$$

为递归起点，空词取 $s_{()}=0,d(())=0,I_{()}=J$。

**定理 18.2（完整前缀区间构造）。** 固定 $m\ge1$，$I_p$ 随 $p\in\mathcal P_m$ 覆盖 $J$，内部两两不交，每个长度为 $\alpha^{d(p)}>0$。对全部实际 $N$，

$$
q_m(N)=p\quad\Longleftrightarrow\quad s(N)\in\operatorname{int}(I_p).
$$

证明。基本二分为

$$
rJ=[-\alpha^3,\alpha^2],\qquad
-\alpha^2+r^2J=[-\alpha,-\alpha^3].
$$

这里用了 $\alpha^2+\alpha^3=\alpha$ 与 $-\alpha^2+\alpha^4=-\alpha^3$。两闭区间覆盖 $J$，仅在 $-\alpha^3$ 相接，内部不交。

从低位词的高端添加一个数字。若长 $m$ 词 $p$ 末位为零，或 $p$ 为空，则有两个合法子词 $p0,p1$；它们的区间分别是

$$
I_{p0}=s_p+r^m(rJ),\qquad
I_{p1}=s_p+r^m(-\alpha^2+r^2J),
$$

而 $I_p=s_p+r^mJ$，因为 $c_m=-\alpha^2r^m$。对基本二分施加这个仿射映射，即得到父区间的二分；方向反转不影响覆盖及内部不交。若 $p$ 末位为一，则只有强制添零的子词 $p0$，父子同有 $s_p$ 和完成长度 $m+1$，其区间相同。逐层归纳得到全部区间的覆盖与内部不交。长度为 $|r|^{d(p)}(b-a)=\alpha^{d(p)}$。

若 $q_m(N)=p$ 且末位为一，合法性迫使 $b_m(N)=0$，这正是完成长度中多加的一位。两种末位情形都可把余下的有限合法尾列从位置 $d(p)$ 起重新编号为 $x$。由 $c_{d+j}=r^dc_j$ 得到精确分解

$$
s(N)=s_p+r^{d(p)}\sum_jx_jc_j.
$$

定理 17.6 把尾和严格放在 $J$ 内部，故 $s(N)$ 在 $I_p$ 内部。反向，实际 $N$ 已有某一前缀 $p'$，刚才的论证将其放在 $I_{p'}$ 内部；内部不交迫使 $p'=p$。每个标签也确实由 $V(p)$ 实现：其尾部为零，$0\in(a,b)$，所以 $s(V(p))=s_p$ 严格位于 $I_p$ 内部。这里没有把区间内全部实数都当成有限自然来源。$\square$

**定理 18.3（精确切点与圆周接缝）。** 对 $m\ge1$，全部 $I_p$ 端点的圆周像恰为 $\mathcal C_m$。其补集的开放连通弧与 $\mathcal P_m$ 一一对应，弧 $\mathcal A_m(p)$ 的唯一标签是 $p$。实际来源满足

$$
q_m(N)=p\quad\Longleftrightarrow\quad z_N\in\mathcal A_m(p).
$$

因此两实际来源的 $m$ 窗相同，当且仅当相位处在同一条补弧。相位零不是额外切点。

证明。固定 $p$，写 $V=V(p),d=d(p)$。两个尚未排序的实端点是 $s_p+r^da$ 与 $s_p+r^db$。因 $d\ge1$，

$$
r^da=-c_{d-1},\qquad r^db=-c_d.
$$

定理 17.6 将这两个端点的相位分别化为

$$
E_{G_{d-1}-V},\qquad E_{G_d-V}.
$$

若末位为零，则 $d=m$，定理 17.4 给 $0\le V\le G_{m-1}-1$，两个下标均在 $[1,G_m]$。若末位为一，则 $d=m+1$，有 $G_{m-1}\le V\le G_m-1$；两个下标是 $G_m-V,G_{m+1}-V$，均为正，并且后者至多 $G_{m+1}-G_{m-1}=G_m$。当 $m=1$ 时两词的值为 0、1，上述界仍成立。因此所有端点相位都在 $\mathcal C_m$ 中。

定理 17.4 给出恰好 $G_m$ 个正长度区间。把一条非退化闭实区间的有限区间分割按左端点排序，内部不交排除相邻内部重叠，覆盖排除空隙，所以前一区间的右端点恰是后一区间的左端点；$G_m$ 个区间恰有 $G_m+1$ 个不同实端点。它们都在长度一的 $J$ 内，模整数唯一可能的不同端点识别是 $a,b$，而这两个外端点确实出现。因此圆周端点恰有 $G_m$ 个。定理 17.6 又使所列 $G_m$ 个 $E_k$ 两两不同，故已证的包含必须是相等。

每个 $I_p$ 的长度 $\alpha^{d(p)}<1$，其内部投影是单射的开放圆弧。上面的分割及外端点识别使这些弧恰为 $\mathbb T\setminus\mathcal C_m$ 的连通分支，且标签互不重复。两个外端点都投到 $E_1$，因为 $a=-\alpha,b=1-\alpha$；穿过相位零的弧则仍是一条完整弧。定理 17.6 排除实际相位命中任何正下标端点，也使 $s(N)$ 是 $z_N$ 在 $(a,b)$ 中的唯一提升。结合定理 18.2 即得所述等价。$\square$

**假设 18.4（引用的无限柱集定理及其精确有限桥）。** 以下引用固定为修订 `cd4bbbef4e52b52ce922b848cd52601c839d2918` 的 [`WindowCylinderPartition.window_cylinder_partition`](https://github.com/the-omega-institute/trureturing/blob/cd4bbbef4e52b52ce922b848cd52601c839d2918/D5/S1/Digit/Infinite/WindowCylinderPartition.lean#L81)。写

$$
\mathcal X=\{x:\mathbb N_0\to\{0,1\}:x_jx_{j+1}=0\},\qquad
P_Lx=(x_0,\ldots,x_{L-1}),
$$

$$
s_\infty(x)=\sum_{j\ge0}x_jc_j,\qquad
\operatorname{ph}(x)=[s_\infty(x)],\qquad C_L(p)=\{x:P_Lx=p\}.
$$

绝对收敛由 $\sum_j|c_j|<\infty$ 保证。该定理的正宽度柱集部分给出：对每个 $L\ge1$，合法长 $L$ 词集合有限；对每个 $p$，将末位一补成 `10` 后的完成长度为 $d(p)$，完成词所对应的返回块词 $c(p)$ 的展开长度为 $d(p)$、有符号部分和为 $s_p$，并有

$$
C_L(p)=\operatorname{range}(\operatorname{prependWord}(c(p))),\qquad
s_\infty(C_L(p))=I_p=[\ell_p,u_p],
$$

$$
u_p-\ell_p=\alpha^{d(p)},\qquad 0<\alpha^{d(p)}<1,\qquad
\bigcup_{p\in\mathcal P_L}I_p=[a,b].
$$

这里返回块为 `0` 与 `10`，从低位向高位串接，$\operatorname{prependWord}$ 表示把这些完整块放到任意合法尾列之前。不同 $p$ 的 $(\ell_p,u_p)$ 两两不交，全部圆周端点恰为 $\{E_1,\ldots,E_{G_L}\}$。对各正整数 $k$，定理中的有向端点流 $e^-_k,e^+_k$ 不同，并满足

$$
\operatorname{ph}(x)=E_k\quad\Longleftrightarrow\quad
x=e^-_k\ \text{或}\ x=e^+_k.
$$

对于每个 $p$，存在 $1\le i,j\le G_L$，使 $[\ell_p]=E_i,[u_p]=E_j$，且精确柱公式是

$$
C_L(p)=\operatorname{ph}^{-1}\!\bigl(\mathcal A_L(p)\bigr)
       \ \cup\ \{e^+_i,e^-_j\},\qquad
\mathcal A_L(p)=\{[x]:\ell_p<x<u_p\}.
$$

此外，对每个 $k\ge1$，

$$
P_L(e^-_k)\ne P_L(e^+_k)\quad\Longleftrightarrow\quad k\le G_L.
$$

这个引用使用的是开内部加指定端点流的柱公式，不能把 $\mathcal A_L(p)$ 换成闭区间像后省略端点归属。源定理以 $[-k\varphi]$ 定义 $E_k$；由于 $\varphi=1+\alpha$，它与此处的 $[-k\alpha]$ 是同一圆周点。

相关定义的对应为：`SignedSeriesRange` 的 $\alpha,a,b,\operatorname{signedValue}$ 分别就是本节的 $\alpha,a,b,s_\infty$；其两交替端点流在偶位、奇位分别取一，值为 $a,b$。`WindowSuccessorGraph` 的 $X(L),P,V,G$ 分别对应 $\mathcal P_L,P_L,V,G_L$。`SuccessorContinuity.LegalDigits` 对应整个 $\mathcal X$。`MultiplierObstruction.zRow(N)` 对应规范有限展开补零后的 $x_N$，其 `phase` 对应 $\operatorname{ph}$；`GoldenZeckendorfLanguage.canonical_indices_not_adjacent` 给出同一非相邻索引约定。由定理 17.4 的唯一性，这个规范自然数行与 $b_j(N)$ 一致。定理 17.6 于是给出

$$
P_Lx_N=q_L(N),\qquad \operatorname{ph}(x_N)=z_N,
\qquad x_N\notin\{e^-_k,e^+_k\}\quad(k\ge1).
$$

把 $x_N$ 代入引用的精确柱公式，恰得到定理 18.3 的实际有限来源分类。定理 18.2—18.3 还给出了这个有限分类自身的直接证明。后文平移柱集时使用的是这一完整对应；单步后继图的逐边自然实现没有提供同一来源的任意联合路径，因而不承担联合观察的前提。

## 19. 最低位编码、累积整数部与连续窗重叠

**定理 19.1（最低位的整数部公式）。** 对每个 $N\ge0$，

$$
b_0(N)=1+\lfloor(N+1)\alpha\rfloor-\lfloor(N+2)\alpha\rfloor.
$$

证明。宽度一的两柱区间由定理 18.2 为

$$
I_0=[-\alpha^3,\alpha^2],\qquad I_1=[-\alpha,-\alpha^3].
$$

实际来源在内部。$\operatorname{int}(I_1)$ 的圆周像在 $[0,1)$ 中恰为

$$
(1-\alpha,1-\alpha^3)=(1-\alpha,2-2\alpha),
$$

其中 $\alpha^3=2\alpha-1$；闭 $I_1$ 的像则包含两个端点，不能与此开区间混同。令 $z=\{N\alpha\}$、$y=\{(N+1)\alpha\}=\{z+\alpha\}$。若 $z<1-\alpha$，则 $y=z+\alpha\ge\alpha>1-\alpha$；若 $z>1-\alpha$，则 $y=z+\alpha-1$，而 $y<1-\alpha$ 等价于 $z<2-2\alpha$。定理 17.6 排除了 $z=1-\alpha$ 与 $z=2-2\alpha$；无理性还排除 $y=0$。因此

$$
b_0(N)=1\quad\Longleftrightarrow\quad 0<y<1-\alpha.
$$

任意实数 $u$ 的整数部增量 $\lfloor u+\alpha\rfloor-\lfloor u\rfloor$ 在 $\{u\}<1-\alpha$ 时为零，在 $\{u\}\ge1-\alpha$ 时为一。代入 $u=(N+1)\alpha$ 即得公式；边界 $y=1-\alpha$ 会使 $(N+2)\alpha$ 为整数，已被排除。论证包括 $N=0$。$\square$

**定理 19.2（连续最低位块的单射标签）。** 对 $L\ge1$ 和任意实际 $N,N'$，$B_L(N)=B_L(N')$ 当且仅当 $z_N,z_{N'}$ 处在圆周去掉 $E_1,\ldots,E_{L+1}$ 后的同一条开放连通弧。不同补弧不能具有同一最低位块标签。

证明。取 $y=\{(N+1)\alpha\}$，写 $w_s=b_0(N+s)$。定理 19.1 消去整数 $\lfloor(N+1)\alpha\rfloor$ 后给出

$$
w_s=1+\lfloor y+s\alpha\rfloor-\lfloor y+(s+1)\alpha\rfloor.
$$

令 $R_0=0$，并对 $1\le k\le L$ 定义累积和

$$
R_k=\sum_{0\le s<k}(1-w_s)=\lfloor y+k\alpha\rfloor,
$$

其中最后一步使用 $\lfloor y\rfloor=0$。反向由 $w_s=1+R_s-R_{s+1}$ 恢复所有位。因此块标签与整数部向量 $(\lfloor y+k\alpha\rfloor)_{1\le k\le L}$ 精确互定。

写 $k\alpha=n_k+\theta_k$，其中 $0<\theta_k<1$。第 $k$ 个整数部在 $[0,1)$ 上只有一个跳点

$$
v_k=1-\theta_k=\{-k\alpha\},
$$

其值在跳点下方为 $n_k$、在跳点及上方为 $n_k+1$。这些 $L$ 个跳点互不相同且都在 $(0,1)$。每个由它们切出的开实区间上整个向量恒定；若 $y<y'$ 属于不同区间，两者之间至少有一个 $v_k$，该坐标的整数部不同。这证明了标签单射性，而不只是标签在区间内恒定。

圆周的 $y$ 坐标还需加入接缝 $y=0$。靠近零与靠近一的两个区间的向量也不同，因为 $L\ge1$，两者之间的任一 $v_k$ 都使相应整数部不同。实际 $y$ 既不为零，也不等于任何 $v_k$，否则 $(N+1)\alpha$ 或 $(N+1+k)\alpha$ 为整数。把圆周坐标平移回 $z_N=y-\alpha$，切点零变成 $E_1$，$v_k$ 变成 $E_{k+1}$。由此得到全圆周的等价，包括穿过原坐标零的弧。$\square$

**定理 19.3（一个低位窗与一个最低位块）。** 对 $m\ge1$，$q_m$ 与 $B_{G_m-1}$ 在实际自然数上精确互定。具体地，

$$
f_m:\mathcal P_m\longrightarrow\{B_{G_m-1}(N):N\ge0\},\qquad
f_m(p)=B_{G_m-1}(V(p))
$$

是双射，且 $B_{G_m-1}(N)=f_m(q_m(N))$。

证明。$G_m\ge2$，故块长 $G_m-1$ 为正。定理 18.3 将 $q_m$ 的相等性化为同处切点 $E_1,\ldots,E_{G_m}$ 的一条补弧；定理 19.2 在 $L=G_m-1$ 时给出完全相同的判据，所以两种数据纤维相同。定理 17.4 给 $q_m(V(p))=p$，因此 $f_m(q_m(N))$ 等于所述实际块。若 $f_m(p)=f_m(p')$，把纤维等价用于 $V(p),V(p')$ 得 $p=p'$；每个实际块也由某个 $q_m(N)$ 得到，故为双射。$\square$

**定理 19.4（连续同源观察的完整重叠等价）。** 对 $m\ge1,h\ge0$，

$$
W_{m,h}(N)=W_{m,h}(N')
\quad\Longleftrightarrow\quad
B_{G_m+h-1}(N)=B_{G_m+h-1}(N').
$$

证明。置 $K=G_m-1\ge1$。在每个时间 $t=0,\ldots,h$，对实际自然数对 $N+t,N'+t$ 应用定理 19.3。两个窗相同，当且仅当两个从时间 $t$ 开始的长 $K$ 最低位块相同。它们在原记录中的整数位置集合为

$$
\{t,t+1,\ldots,t+K-1\}.
$$

这些集合的并恰为 $\{0,\ldots,h+K-1\}$：最初从零开始，最后到 $h+K-1$，相邻起点相差一而 $K\ge1$，没有遗漏的整数位置。所以长 $h+K$ 块相等可以限制到每个短块；全部短块相等则在并集的每个位置给出相等。这两个方向得到结论，因为 $h+K=G_m+h-1$。特别地，$m=1$ 时 $K=1$，短块只是依次相接的单个位，论证并不预设正长度重叠。全部短块都来自原来同一个 $N$，没有逐坐标更换来源。$\square$

## 20. 连续重构的充分时域、完整纤维与互逆映射

**定理 20.1（Fibonacci 差时域的双向充分性）。** 设 $1\le m\le M$，$T=G_M-G_m$。则对全部实际 $N,N'$，

$$
q_M(N)=q_M(N')\quad\Longleftrightarrow\quad
W_{m,T}(N)=W_{m,T}(N').
$$

每个 $h\ge T$ 的记录 $W_{m,h}$ 都确定 $q_M$；每个 $h\le T$ 的 $W_{m,h}$ 都由 $q_M$ 确定。在 $h=T$ 时，两者的每个完整自然数纤维相等，实际记录标签与 $\mathcal P_M$ 双射，两者均有 $G_M$ 个元素。

证明。定理 19.4 给出 $W_{m,T}$ 与 $B_{G_m+T-1}$ 互定，而

$$
G_m+T-1=G_M-1.
$$

定理 19.3 再把这个块与 $q_M$ 等同为同一个纤维划分，得到两向蕴含。较长记录可以截取到时间 $T$ 后解码；较短记录则从 $q_M$ 决定的完整 $W_{m,T}$ 中截取。因此包括 $T=0$ 在内的两个充分方向都成立。

定理 17.4 使每个 $p\in\mathcal P_M$ 由 $V(p)$ 实现。映射 $p\mapsto W_{m,T}(V(p))$ 对实际记录标签满射，反向蕴含使它单射。纤维相同并不只限于这些有限代表元，而是对所有自然数成立。$|\mathcal P_M|=G_M$ 给出标签数。$\square$

**定理 20.2（不附加相位的显式互逆数据映射）。** 在定理 20.1 的范围内，以下预测映射与解码映射互为逆映射。预测映射为

$$
\Pi(p)=(q_m(V(p)+t))_{0\le t\le T}\qquad(p\in\mathcal P_M).
$$

解码映射 $\Delta$ 的输入是一个实际实现的元组 $(p_t)_{0\le t\le T}$：对每个 $p_t$ 应用定理 19.3 的 $f_m$，把所得 $G_m-1$ 个位放在位置 $t,\ldots,t+G_m-2$，合并这些块，再应用 $f_M^{-1}$。

证明。若 $p=q_M(N)$，则 $q_M(V(p))=p$。定理 20.1 保证 $V(p)$ 和原来源 $N$ 的完整时间元组相同，故 $\Pi(p)=W_{m,T}(N)$；这一步没有假设未知 $N$ 等于 $V(p)$。

若输入元组由一个实际 $N$ 实现，则 $f_m(p_t)$ 恰是 $N+t$ 的最低位块。它们在重叠位置相同，因为每个位置都是同一个 $b_0(N+s)$。位置并集是

$$
\{0,\ldots,T+G_m-2\}=\{0,\ldots,G_M-2\},
$$

所以合并结果恰为实际块 $B_{G_M-1}(N)$，属于 $f_M$ 的像，$f_M^{-1}$ 确实有定义并输出 $q_M(N)$。由此 $\Delta(\Pi(p))=p$；对每个实际元组 $w$，也有 $\Pi(\Delta(w))=w$。两个映射只使用所给数据及固定参数，不需要测量相位、选择端点归属、取得来源上界或读终止标记。对 $h\ge T$，先截取前 $T+1$ 个窗再解码；对 $h\le T$，预测后只保留时间 $0,\ldots,h$。$\square$

## 21. 连续时域的规范减法与两侧精确见证

**定理 21.1（规范减法的奇偶低位）。** 若 $K\ge m\ge1$，则

$$
q_m(G_K-G_m)=
\begin{cases}
0^m,&K-m\text{ 为偶数},\\
e_{m-1},&K-m\text{ 为奇数}.
\end{cases}
$$

证明。$K=m$ 时差为零；$K=m+1$ 时差为 $G_{m-1}$，其唯一一位在位置 $m-1$。设 $K\ge m+2$，则

$$
G_K-G_m=G_{K-1}+(G_{K-2}-G_m).
$$

余数非负且严格小于 $G_{K-2}$，由定理 17.4，其规范非零位都在 $K-2$ 以下，即至多在位置 $K-3$。因此在位置 $K-1$ 添加一个一，中间位置 $K-2$ 为零，所得展开合法；唯一性使它就是该差的规范展开。新位置 $K-1\ge m+1$ 不影响前 $m$ 位。每次把 $K$ 减二保留所求低位，最终落到上述两个初值，得到奇偶公式。这是合法展开的证明，未把减法当作逐位减法。$\square$

**定理 21.2（实际自然数的两组锐性见证）。** 对每个 $M\ge1$ 定义

$$
A=G_{M+1},\qquad B=2G_{M+1},\qquad C=A-1,\qquad D=B-1.
$$

则 $q_M(A)=0^M$、$q_M(B)=e_{M-1}$，而 $q_M(C)=q_M(D)$。对 $1\le m<M$，置 $T=G_M-G_m\ge1$，$A,B$ 的 $m$ 窗在时间 $0,\ldots,T-1$ 全部相同，并在时间 $T$ 首次不同。对 $1\le m\le M$，$C,D$ 的 $m$ 窗在时间 $0,\ldots,T$ 全部相同，并在时间 $T+1$ 首次不同。

证明。$A$ 的规范展开只有位置 $M+1$ 的一。递推给出

$$
2G_{M+1}=G_{M+2}+G_{M-1},
$$

右侧占据相隔三的位置，故是 $B$ 的合法规范展开。于是两个 $M$ 窗分别为 $0^M,e_{M-1}$。

令 $R=G_{M-1}-1$。再次由递推，

$$
C=G_M+R,\qquad D=G_{M+2}+R.
$$

$0\le R<G_{M-1}$，所以其展开只用位置 $M-1$ 以下的位。在位置 $M$ 或 $M+2$ 添加一都与这些位隔开，两个展开都合法。因此 $q_M(C)=q_M(D)$，为 $R$ 的展开补到长度 $M$。$M=1$ 时 $R=G_0-1=0$，同样成立。

定理 20.1 已经在未使用锐性结论的情况下证明充分性，所以它应用于 $C,D$ 得到 $W_{m,T}(C)=W_{m,T}(D)$。若 $m<M$，则对 $0\le t\le T-1$，有 $A+t=C+(t+1)$ 与 $B+t=D+(t+1)$；刚才同一个来源对在时间 $1,\ldots,T$ 的等式给出 $W_{m,T-1}(A)=W_{m,T-1}(B)$。

还可以直接核对 $A,B$ 所在的两侧柱区间。由定义 18.1，$0^M$ 与 $e_{M-1}$ 的区间分别为

$$
r^M[-\alpha,\alpha^2],\qquad r^M[\alpha^2,1].
$$

第二式使用 $c_{M-1}=\alpha r^M$、完成长度 $M+1$ 以及 $\alpha+rJ=[\alpha^2,1]$。它们相邻，共同端点为

$$
s_*=r^M\alpha^2=-c_M,\qquad [s_*]=E_{G_M}.
$$

实际有符号值为

$$
s(A)=c_{M+1}=r^M\alpha^3,\qquad
s(B)=c_{M+2}+c_{M-1}=2c_{M+1}=2r^M\alpha^3.
$$

严格不等式

$$
-\alpha<\alpha^3<\alpha^2<2\alpha^3<1
$$

把它们放在端点 $s_*$ 两侧的两个内部；其中 $\alpha^2<2\alpha^3$ 来自 $2\alpha>1$，而 $2\alpha^3<1$ 来自 $\alpha^3<\alpha^2=1-\alpha<1/2$。$M$ 为奇数时乘 $r^M$ 反向，只交换左右方向，不改变内部位置。若 $m<M$，则 $M\ge2$，两个区间之并的长度为

$$
\alpha^M(1+\alpha)=\alpha^{M-1}<1.
$$

并集的内部投影为一条圆弧，其内部唯一的 $\mathcal C_M$ 切点是共同端点 $E_{G_M}$。删去这一切点后，$A,B$ 的相位同在由 $E_1,\ldots,E_{G_M-1}$ 切出的一个分支。定理 19.2 给出它们的 $B_{G_M-2}$ 相同；因 $G_m+(T-1)-1=G_M-2$，定理 19.4 再给出 $W_{m,T-1}$ 相同。这同时核实了时间平移证明中见证的精确相位位置。这里只在 $M\ge2$ 使用长度严格小于一的并集。

最后计算首次分离的实际时刻：

$$
\begin{aligned}
A+T=C+(T+1)&=G_{M+2}-G_m,\\
B+T=D+(T+1)&=G_{M+3}-G_m.
\end{aligned}
$$

定理 21.1 应用于相邻的 $M+2,M+3$，二者减 $m$ 的奇偶性相反，故相应 $m$ 窗恰为不同的 $0^m,e_{m-1}$。结合已经证明的此前全部相等，得出两组精确首次分离。对 $m=M$，$T=0$，$C,D$ 在时间零相同而在时间一不同，此结论依然成立。$\square$

**定理 21.3（连续解码与预测的精确界）。** 对 $1\le m\le M$、$h\ge0$、$T=G_M-G_m$，

$$
W_{m,h}\text{ 确定 }q_M\quad\Longleftrightarrow\quad h\ge T,
$$

$$
q_M\text{ 确定 }W_{m,h}\quad\Longleftrightarrow\quad h\le T.
$$

证明。两个充分方向已由定理 20.1 给出。若 $h<T$，则 $m<M$ 且 $h\le T-1$。定理 21.2 中的实际 $A,B$ 在整个 $W_{m,h}$ 上相同，$q_M$ 却不同，故任何解码函数至少对其中一个失败。若 $m=M$，$T=0$，不存在非负的 $h<T$，没有遗漏的必要性情形。

若 $h>T$，则 $h\ge T+1$。同一定理中的实际 $C,D$ 有相同的 $q_M$，在时间 $T+1$ 的窗却不同，故完整 $W_{m,h}$ 不同；任何从 $q_M$ 出发的预测函数都不能同时正确。两个反例分别阻断相反方向的纤维包含，给出两个精确当且仅当。$\square$

## 22. 连续记录的边界与每个纤维的无限性

**定理 22.1（连续记录的全部宽度边界）。** 对每个 $h\ge0$，有以下分类。

当 $M=m\ge1$ 时，$T=0$，$W_{m,0}(N)=(q_m(N))$ 是单元素元组。投影与单元素元组形成互逆，给出它与 $q_m$ 的信息等价。所有 $h\ge0$ 都可由时间零解码 $q_m$，但仅 $h=0$ 可从 $q_m$ 预测。

当 $m=M=0$ 时，每个 $h$ 都有双向确定。最小非负解码时域为零，预测没有有限的最大时域。

当 $m=0<M$ 时，每个 $h$ 的记录都可预测，却没有解码；即使给出全部非负时间的零宽度窗，也不能解码 $q_M$。特别地，把 $G_M-G_0=G_M-1$ 代入时域，并不能恢复正宽度互定结论中的观察到目标方向。

当 $m>M\ge0$ 时，每个 $h$ 都能解码 $q_M$，却都不能由 $q_M$ 预测 $W_{m,h}$。此时整数 $G_M-G_m<0$ 不是向前时域。

证明。正宽度等宽时，时间零投影给解码，定理 21.2 的 $C,D$ 给时间一的预测反例。两个宽度均为零时，每个固定 $h$ 下双方的实际数据集合都只有一个元素，唯一函数给出双向确定。

若 $m=0<M$，所有观察都是空词；自然数 0 与 1 的 $q_M$ 在位置零不同，而它们全部时间的空窗相同，所以有限和无限的空窗序列都不能解码。预测空窗元组则恒可行。

若 $m>M$，把时间零的 $m$ 窗截到前 $M$ 位即解码。实际来源 0 与 $G_M$ 在前 $M$ 位都为零，但后者在位置 $M<m$ 有一，因此它们的 $m$ 窗在时间零已经不同，反驳预测。$M=0$ 时该对为 $0,G_0=1$，也包含在论证中。$\square$

**定理 22.2（每个实际有限连续记录都有无限来源）。** 对所有有限 $m,h$，$W_{m,h}$ 的每个实际纤维都无限。因此任何这样的记录都不能恢复无上界的完整自然数来源。

证明。$m=0$ 时唯一纤维就是全部自然数。设 $m\ge1$，固定一个实际记录 $W_{m,h}(N)$。取 $L\ge m$ 使 $G_L\ge G_m+h$，由无界性可得；令 $p=q_L(N),v=V(p)$。对于每个 $j\ge L+1$，$v+G_j$ 的展开是 $p$ 的低位加上位置 $j$ 的一个一，二者之间至少留有位置 $L$ 的零，故合法。唯一性给出

$$
q_L(v+G_j)=p=q_L(N).
$$

因为 $h\le G_L-G_m$，定理 20.1 对上窗宽度 $L$ 的预测方向给出

$$
W_{m,h}(v+G_j)=W_{m,h}(N).
$$

$G_j$ 严格递增，所以这些是同一固定纤维中的无限多个不同实际自然数。论证对每个选定记录分别成立，包括包含 $N=0$ 的纤维。$\square$

## 23. 稀疏观察的圆弧交、正向稠密性与二进制例外

**定义 23.1（带时间的切点集合与圆周编码）。** 对正宽度 $m$、固定有限 $S\subseteq\mathbb N_0$，令

$$
K_m(S)=\bigcup_{t\in S}\{t+1,t+2,\ldots,t+G_m\},\qquad
\mathcal E_m(S)=\{E_k:k\in K_m(S)\}.
$$

每个整数区间都含两端点。时刻 $t$ 的标签 $p$ 在来源相位坐标中的开弧是

$$
\mathcal A_{m,t}(p)=\mathcal A_m(p)-[t\alpha].
$$

在 $\mathbb T\setminus\mathcal E_m(S)$ 上，圆周编码为这些逐时标签组成的元组；其给定标签的圆周纤维是所选弧的交。下文说这个纤维连通，是指圆周上的开弧集合，不能与其内实际自然数来源构成的可数集合混同。公共细分单元指 $\mathbb T\setminus\mathcal E_m(S)$ 的连通分支。$S=\varnothing$ 时编码为常值，定义域为整个圆周。

定理 17.6 与定理 18.3，以及假设 18.4 的精确有限桥，给出对每个实际来源的等式

$$
q_m(N+t)=p\quad\Longleftrightarrow\quad
z_N\in\mathcal A_{m,t}(p).
$$

因此时刻 $t$ 的全部切点恰为 $E_{t+1},\ldots,E_{t+G_m}$；全部时刻的切点并恰为 $\mathcal E_m(S)$。实际 $z_N$ 避免这些切点，逐时标签在每个公共细分单元上恒定。但这些事实本身还没有排除不同单元具有同一元组标签。

**定理 23.2（每条正向尾轨道都稠密）。** 给定非空开放圆弧 $U$ 和任意自然数界 $B_0$，存在实际自然数 $N>B_0$ 使 $z_N\in U$。同一结论也适用于这些相位的任意固定圆周平移。

证明。令弧长为 $\lambda>0$，取正整数 $Q$ 使 $1/Q<\lambda$。$0,\alpha,\ldots,Q\alpha$ 的 $Q+1$ 个分数部分布在 $[0,1)$ 的 $Q$ 个等长半开区间中，至少两个同处一区间。令较大索引减较小索引为 $q>0$，其分数部之差为 $\varepsilon\delta$，其中 $\varepsilon\in\{-1,1\}$，$0<\delta<1/Q$；差非零由无理性保证。所以

$$
[q\alpha]=[\varepsilon\delta].
$$

圆周点 $[k\varepsilon\delta]$、$0\le k\le\lfloor1/\delta\rfloor$ 的相邻圆周空隙都至多为 $\delta$。在正方向，这是步长 $\delta$ 的连续网格，最后余隙小于 $\delta$；负方向只反转次序。将整个有限网格平移 $[(B_0+1)\alpha]$ 后，最大空隙不变。长度严格大于 $\delta$ 的开放弧必含其中一点，否则它将落在一个至多长 $\delta$ 的空隙中。该点为

$$
[(B_0+1)\alpha+kq\alpha]=z_{B_0+1+kq},
$$

对应自然数严格大于 $B_0$。任意固定平移的结论只需把 $U$ 反向平移后应用同一论证。因此得到的是每条正向自然数尾轨道的实际访问，而非只对双向整数轨道或极限流的存在断言。$\square$

**定理 23.3（短锚弧交引理）。** 设 $A,B$ 是长度分别为 $a_0,b_0$ 的真开放圆弧，且 $a_0+b_0\le1$。把 $A$ 提升到一条长 $a_0$ 的开实区间后，$A\cap B$ 为空或该提升内的一个开区间。更一般地，有限弧族若有一条锚弧 $A$，其长度加上每条其它弧的长度都至多为一，则全体之交为空或一条开放圆弧。

证明。$B$ 的相邻实提升之间有长度 $1-b_0\ge a_0$ 的间隙。固定提升的 $A$ 中任意两点距离严格小于 $a_0$，不能分别落在 $B$ 的两个不同提升中；若它们这样落入，其距离至少为该间隙长度。因此与 $B$ 的交只可能来自一个提升，交集为空或开实区间。所有其它弧与 $A$ 的交都在同一固定提升中为开区间；有限个开实区间的交仍为空或开区间。

特别地，圆周元组纤维是公共细分单元的并，并排除全部相关切点。若它非空且连通，就只能占据一个连通分支；因为标签在每个单元上恒定，它又包含整个该单元。所以这个纤维恰是一整个公共细分单元。长度和等于一的情形也成立，因为锚弧开放，任意两点距离仍严格小于弧长。$\square$

**定理 23.4（宽度至少二的稀疏标签单射性）。** 若 $m\ge2$ 且 $S\ne\varnothing$，每个非空圆周编码纤维恰是一条公共细分单元。不同单元有不同时间元组标签，并且实际实现的 $\sigma_{m,S}$ 标签数恰为 $|K_m(S)|$。

证明。每个宽 $m$ 柱弧长度为 $\alpha^m$ 或 $\alpha^{m+1}$，至多为 $\beta=\alpha^2<1/2$。对给定标签任选一个时间坐标的弧为锚，它的长度与任何其它坐标弧之和至多 $2\beta<1$。定理 23.3 使元组纤维为空或连通，非空时恰为一个细分单元。

无理性使切点数为 $|K_m(S)|$；非空 $S$ 给非空切点集，圆周去掉这些不同点后恰有这么多非空开放单元。定理 23.2 使每个单元都有实际自然来源，单射标签便给出恰好这么多实际记录。$\square$

**定理 23.5（宽度一的唯一重复标签及解析反例）。** 对 $m=1$ 的固定稀疏记录，每个包含数字一的非空圆周纤维都连通。仅全零元组可能出现在多个分离的单元。将相位坐标旋转为 $x=z-\beta$ 后，时刻 $t$ 的一标签弧为

$$
J_t=(t\beta,(t+1)\beta)\pmod1,
$$

零标签弧为 $\mathbb T\setminus\overline{J_t}$，全零元组的纤维恰为

$$
\mathbb T\setminus\bigcup_{t\in S}\overline{J_t}.
$$

所以全部细分单元的标签互异，恰当且仅当这个全零纤维为空或连通。对于 $S=\{0,4\}$，确实存在两个不同非空单元具有同一标签 $(0,0)$，且两者均有任意大的实际自然来源。

证明。宽度一的一标签弧由定理 19.1 是 $(\beta,2\beta)$，长 $\beta$；零标签弧长 $\alpha=1-\beta$。由于 $-[t\alpha]=[t\beta]$，旋转 $-\beta$ 后得到所述 $J_t$。含有一的元组具有长度 $\beta$ 的锚弧，任何其它坐标弧长度为 $\beta$ 或 $1-\beta$，长度和至多一。定理 23.3 给出连通性。全零纤维是零弧之交，按补集公式恰如所写；它若有多个分支，各分支必有同一全零标签。没有其它可能的重复标签。

由函数 $x^2+x$ 在正数上严格递增，且

$$
(3/5)^2+3/5=24/25<1,\qquad (2/3)^2+2/3=10/9>1,
$$

得到 $3/5<\alpha<2/3$，即

$$
\frac13<\beta<\frac25.
$$

因此当 $S=\{0,4\}$ 时，旋转坐标中的两一弧为

$$
J_0=(0,\beta),\qquad J_4=(4\beta-1,5\beta-1),
$$

且

$$
0<\beta<4\beta-1<5\beta-1<1.
$$

它们的闭包不交。全零标签有两个开放间隙

$$
(\beta,4\beta-1),\qquad(5\beta-1,1),
$$

长度分别为 $3\beta-1>0$ 与 $2-5\beta>0$。它们是切点公共细分中的两个不同单元，时间元组均为 $(0,0)$。对两弧分别应用定理 23.2 的平移版本，可在每一弧找到超过任意指定界的实际自然来源。故这个反例直接排除了仅凭切点并集便断言任意二进制稀疏标签单射的推理。$\square$

**定理 23.6（二进制覆盖强制的两个锚对）。** 若 $m=1,M\ge2$ 且

$$
\{1,\ldots,G_M\}\subseteq K_1(S),
$$

则 $S$ 包含 0，并且至少包含 1、2 中的一个。只观察 $\{0,1\}$ 或只观察 $\{0,2\}$ 时，每个非空圆周纤维都是长度至多 $\beta$ 的单弧，标签互异；包含任意一个这样的时刻对后，再添加任意有限个二进制观察，所有非空圆周纤维仍连通。

证明。先在定理 23.5 的旋转坐标内计算两个时刻对。对 $\{0,1\}$，两一弧为 $(0,\beta)$ 与 $(\beta,2\beta)$，内部不交，只共有端点。排除全部端点后，三个非空元组纤维依次为

$$
\begin{aligned}
(1,0)&:\ (0,\beta),\\
(0,1)&:\ (\beta,2\beta),\\
(0,0)&:\ (2\beta,1).
\end{aligned}
$$

长度为 $\beta,\beta,1-2\beta$，而 $1-2\beta<\beta$ 由 $3\beta>1$ 得到。

对 $\{0,2\}$，$J_2=(2\beta,3\beta)\pmod1$ 穿过圆周零，故四个非空元组纤维恰为

$$
\begin{aligned}
(1,1)&:\ (0,3\beta-1),\\
(1,0)&:\ (3\beta-1,\beta),\\
(0,0)&:\ (\beta,2\beta),\\
(0,1)&:\ (2\beta,1).
\end{aligned}
$$

长度分别是 $3\beta-1,1-2\beta,\beta,1-2\beta$。由 $1/3<\beta<1/2$，它们都严格为正且至多为 $\beta$。在这两个时刻对中，每个给定元组均确定一个短锚弧，包括全零元组。

任何包含该时刻对的完整元组先固定其中一条长至多 $\beta$ 的弧。其它二进制坐标弧的长度至多 $1-\beta$，故定理 23.3 适用，继续相交不能产生断开的非空纤维。

最后，$M\ge2$ 使 $G_M\ge3$。因为全部时刻非负，覆盖下标 1 只能由 $t=0$ 提供。宽度一每次提供的下标块为 $\{t+1,t+2\}$，覆盖下标 3 必须取 $t=1$ 或 $t=2$。覆盖条件因而确实迫使一个锚对出现。这是从覆盖推到标签单射所需要的额外几何步骤。$\square$

## 24. 稀疏解码、预测与互定的精确分类

**定理 24.1（缺失切点与多余切点的实际两侧见证）。** 在 $1\le m\le M$、$g=G_m,H=G_M$ 的范围内：若某个 $k\in\{1,\ldots,H\}$ 不在 $K_m(S)$ 中，则解码 $D(m,M,S)$ 失败；若某个 $k\in K_m(S)$ 不在 $\{1,\ldots,H\}$ 中，则预测 $P(m,M,S)$ 失败。每一种失败都可以由两个超过任意指定自然数界 $B_0$ 的实际来源 $N,N'$ 见证。

证明。先设缺失目标下标 $k$。有限合并切点集中各点不同，故可在 $E_k$ 周围选一条足够小的开邻域，不含任何来源切点，也不含其它目标切点。每个观测坐标在该邻域上恒定，所以整个来源元组恒定；目标 $q_M$ 在 $E_k$ 两侧的标签却不同，这是定理 18.3 的相邻不同柱标签，包括外接缝对应的切点。两个开侧各有正长度。定理 23.2 在每一侧给出 $N,N'>B_0$，于是

$$
\sigma_{m,S}(N)=\sigma_{m,S}(N'),\qquad q_M(N)\ne q_M(N').
$$

这也覆盖 $S=\varnothing$ 的缺失切点情形。

再设多余来源下标 $k$。在 $E_k$ 周围选开邻域，不含目标切点，也不含其它不同的来源切点。目标在整个邻域上恒定；至少一个时间坐标将 $E_k$ 作为自己的真实柱切点，所以该坐标在两侧改变标签。即使多个坐标共享该切点，保留时间的元组也已因这一坐标而改变。对两个开侧应用相同的正向尾轨道论证，得到 $N,N'>B_0$，满足

$$
q_M(N)=q_M(N'),\qquad \sigma_{m,S}(N)\ne\sigma_{m,S}(N').
$$

两种构造都只选实际自然数，排除端点本身。每个被选自然数的全部坐标自动由其自身的 $N+t$ 给出，不是分别选取坐标后拼接。$\square$

**定理 24.2（固定稀疏解码的当且仅当）。** 若 $1\le m\le M$，则

$$
D(m,M,S)\quad\Longleftrightarrow\quad
\{1,\ldots,H\}\subseteq K_m(S).
$$

特别地，每个解码时刻集合都包含 0。

证明。必要性由定理 24.1；其中下标 1 的覆盖强制 $0\in S$。为证充分性，假设目标切点全部被覆盖，则 $S\ne\varnothing$。

若 $m\ge2$，定理 23.4 说明相同元组标签使两实际相位处于同一来源细分单元。若 $m=1,M\ge2$，定理 23.6 给出同一个结论。在这两种情形中，该单元是一条连通弧，其内部不含任何来源切点，故也不含目标切点，必完全包含在一个目标柱弧内。因此相同元组给相同 $q_M$。

剩下 $m=M=1$。此时覆盖 $\{1,2\}$ 等价于 $0\in S$，而目标 $q_1(N)$ 已经就是时间零的被观察坐标。相同元组直接给出相同目标，不需要完整元组的全局标签单射性；例如 $S=\{0,4\}$ 的全零纤维可以断开，仍不影响解码这个已观察的坐标。$\square$

**定理 24.3（固定稀疏预测的当且仅当）。** 若 $1\le m\le M$，则

$$
P(m,M,S)\quad\Longleftrightarrow\quad
K_m(S)\subseteq\{1,\ldots,H\}
\quad\Longleftrightarrow\quad
S\subseteq\{0,\ldots,H-g\}.
$$

对非空 $S$，最后一个条件等价于 $\max S\le H-g$。

证明。必要性由定理 24.1。反向，若 $S$ 为空则记录恒定。若非空，每个目标标签由定理 18.3 确定一条连通开弧。来源切点都是目标切点，故目标弧内部没有任何来源切点，每个被观察坐标都在整条目标弧内恒定。因此目标相同给出整个元组相同；此证明只用目标弧连通，不要求来源元组的全局标签单射。

所有来源下标至少为一；当 $S\ne\varnothing$ 时，最大的来源下标恰为 $\max S+g$。所以来源切点包含于目标下标区间，当且仅当 $\max S+g\le H$。空集合也满足所述集合包含式，因而得到对全部有限 $S$ 的最后等价。$\square$

**定理 24.4（稀疏互定、纤维与确定映射）。** 在相同正宽度范围内，$q_M$ 与 $\sigma_{m,S}$ 双向确定，当且仅当

$$
K_m(S)=\{1,\ldots,H\}.
$$

此时两者的自然数纤维完全相同，实际标签数均为 $H$。预测映射可以取

$$
p\longmapsto(q_m(V(p)+t))_{t\in S},
$$

其在实际元组集合上的逆映射给出解码。

证明。两个相反的包含条件由定理 24.2—24.3 恰好合成集合相等。双向纤维包含给出纤维相等。每个 $p\in\mathcal P_M$ 由 $V(p)$ 实现，并且预测保证这个代表元产生的完整稀疏元组与所有同目标来源的元组相同；解码又保证不同目标不能产生同一实际元组。因此显示的映射为双射，像集恰为全部实际元组，逆映射有定义。定理 17.4 给出 $|\mathcal P_M|=H$。$\square$

## 25. 固定稀疏查询的精确数量、最晚时刻与截止条件

**定理 25.1（两个下界同时可达）。** 设 $1\le m\le M$，$g=G_m,H=G_M$，$k=\lceil H/g\rceil$。所有固定解码时刻集合中的最小查询数恰为 $k$，最小最晚时刻恰为 $H-g$。这两个最小值可以由同一集合同时达到，而且该集合还给出双向确定：当 $k=1$ 时取 $S_* =\{0\}$；当 $k\ge2$ 时取

$$
S_*=\{jg:0\le j\le k-2\}\ \cup\ \{H-g\}.
$$

证明。每个时刻只给 $g$ 个切点下标，解码由定理 24.2 要求覆盖全部 $H$ 个目标下标，故

$$
H\le |K_m(S)|\le g|S|,
$$

从而 $|S|\ge\lceil H/g\rceil$。覆盖下标一强制时间零，所以解码集合非空，其最大值有定义。覆盖下标 $H$ 还要求某个 $t\in S$ 满足 $t+g\ge H$，于是 $\max S\ge H-g$。这些必要界不使用来源标签单射性。

若 $k=1$，由 $g\le H$ 得 $H=g$，$S_* =\{0\}$ 提供全部 $1,\ldots,H$。若 $k\ge2$，则

$$
(k-1)g<H\le kg,
\qquad (k-2)g<H-g\le(k-1)g.
$$

因此最后时刻 $H-g$ 严格大于所有先前时刻 $0,g,\ldots,(k-2)g$，显示的集合恰有 $k$ 个不同元素，最大值为 $H-g$。前 $k-1$ 个规则块首尾相接，覆盖 $1,\ldots,(k-1)g$。最后一块为

$$
\{H-g+1,\ldots,H\},
$$

其起点至多为 $(k-1)g+1$，终点为 $H$，因此扩展前面并集而没有整数空隙；全部块又都包含于 $\{1,\ldots,H\}$。于是 $K_m(S_*)=\{1,\ldots,H\}$。特别地，当 $H=kg$ 恰好整除时，最后时刻是 $(k-1)g$，仍与前面的 $(k-2)g$ 不同，最后一块恰好接上，不产生重复时刻。非整除时可以重叠，却仍无空隙。定理 24.4 给双向确定，同时达到两个下界。$\square$

**定理 25.2（截止时刻内的可行性）。** 对整数截止时刻 $d\ge0$，存在解码集合 $S\subseteq\{0,\ldots,d\}$，当且仅当 $d\ge H-g$；可行时最小查询数仍为 $\lceil H/g\rceil$。

证明。若 $d<H-g$，每个允许时刻的块终点至多 $d+g<H$，无法覆盖目标下标 $H$。若 $d\ge H-g$，定理 25.1 的 $S_*$ 完全落在截止时刻内，并以 $k$ 次查询实现互定。该定理的查询数下界对截止限制下的所有集合仍然成立，故为精确最小值。这是存在某个可行时间表的判据，不是说最晚时刻足够大的每个时间表都会解码。$\square$

**定理 25.3（连续记录的代价与预测时刻全集）。** 在 $1\le m\le M$ 下，连续时间集 $S_h=\{0,\ldots,h\}$ 的切点下标并集为

$$
K_m(S_h)=\{1,\ldots,g+h\}.
$$

因此连续解码恰在 $h\ge H-g$ 时成立，连续预测恰在 $h\le H-g$ 时成立；最短连续解码记录含 $H-g+1$ 次查询，并在该时域给出互定。固定稀疏最优记录的原始返回位数为 $m\lceil H/g\rceil$。仅要求预测时，允许的不同时间恰为 $0,\ldots,H-g$，所以最多可以预测 $H-g+1$ 个不同正宽度窗；空预测记录始终允许。

证明。相邻整数时刻的两个下标块起点相差一，而块长 $g\ge2$；从第一块的起点一到最后一块的终点 $g+h$ 无缺口，得到并集公式。代入定理 24.2—24.3 即得两个时域及连续查询数；这与定理 21.3 中保留了显式算术见证的精确时域一致。特别地，$m=1$ 时 $g=G_1=2$，临界连续记录为时间 $0,\ldots,G_M-2$ 的 $G_M-1$ 次最低位观察。

按定义 17.3，每次查询返回 $m$ 个原始位，定理 25.1 的最优数量为 $\lceil H/g\rceil$，相乘即得表示成本。预测时刻全集由定理 24.3 精确给出，任意子集可预测，任何外部时间都因多余切点而不能预测。重复一个时间只重复完全相同的坐标，不能降低所需不同查询数，也不改变任何确定关系。所有结论按普通加法步数、不同时间数量与原始位数量各自计量，不把其中一个量改称另一个量。$\square$

## 26. 稀疏空值边界与有限信息的来源余量

**定理 26.1（空集合、零宽度与正等宽度）。** 对固定有限 $S\subseteq\mathbb N_0$，有以下全部逻辑边界。

若 $S=\varnothing$，任意 $m,M$ 都可预测，解码恰当且仅当 $M=0$。若 $m=0$，任意 $S,M$ 都可预测，解码仍恰当且仅当 $M=0$。若 $M=0$，解码总成立；当 $m\ge1$ 时，预测恰当且仅当 $S=\varnothing$，当 $m=0$ 时预测对全部 $S$ 成立。特别地，$m=M=0$ 对全部 $S$ 双向确定。

若 $1\le m=M$，则解码恰当且仅当 $0\in S$，预测恰当且仅当 $S\subseteq\{0\}$。这些正宽度结论包括空 $S$。

证明。空记录与零宽度记录都是常值。正宽度目标不是常值，因为 $q_M(0)$ 全零，而 $q_M(1)$ 在第一位为一；零宽度目标则为常值。这立即给出所有常值记录的解码分类及相应预测结论。

若 $M=0,m\ge1,S\ne\varnothing$，任选 $t\in S$。宽 $m$ 至少有两个不同标签的正长度柱弧；定理 23.2 的平移版本使 $z_N+[t\alpha]$ 在 $N\ge0$ 上分别命中这两个弧。因此 $q_m(N+t)$ 非常值，包含它的完整记录也非常值，常值 $q_0$ 不能预测。

最后在正等宽度时 $H=g$。$0\in S$ 的一个块已经覆盖 $\{1,\ldots,H\}$；反向，覆盖下标一只能由零时刻提供，故定理 24.2 化为所述解码条件。定理 24.3 则化为 $S\subseteq\{0\}$。$\square$

**定理 26.2（每个实际有限稀疏记录的纤维无限）。** 对任何有限 $m$ 与有限 $S$，$\sigma_{m,S}$ 的每个实际纤维都是无限集。

证明。若 $S=\varnothing$ 或 $m=0$，唯一纤维是全部自然数。否则令 $h=\max S$。固定某个实际记录 $\sigma_{m,S}(N)$，定理 22.2 给出 $W_{m,h}(N)$ 的无限多个实际来源；每个来源在全部 $0,\ldots,h$ 时刻与 $N$ 的窗相同，限制到 $S$ 后仍相同。因此这一个稀疏纤维包含无限集。$\square$

**定义 26.3（结论的量词范围）。** 稀疏正宽度分类与数量公式的范围是固定有限时间集及 $1\le m\le M$；定理 26.1 另外给出零目标的 $M=0<m$ 扩展。这里没有定义对任意正 $m>M$ 的新稀疏分类。该范围以外的连续记录由定理 22.1 单独处理。常值目标允许空的解码时间集，空集没有在本文中被赋予“最大时刻”，所以正宽度资源公式不代入这些退化情形。

有限记录取得的是指定窗的等价类，定理 22.2 与定理 26.2 保留了每个记录中的无限来源余量。所有普通加法观测都以实际规范有限来源为对象，记录不含 $\rho$、免费 End 标记或完整来源认证。无限合法流仅出现于假设 18.4 的柱集引用与端点说明，并未被当作失败方向的自然数见证。这里的固定时间表最优性只涉及定义 17.3 所给的资源，不扩大到自适应、随机、带噪或其它来源观察契约。

## 追加锚（本行以下为增补区）

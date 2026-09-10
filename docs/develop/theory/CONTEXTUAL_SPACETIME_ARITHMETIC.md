# ZFC兼容算术

## 情境时空算术：保留档案的表示与精确算术投影

本文构造一种两层算术。丰富层中的对象是带时间、位置、因果偏序和来源的有限事件档案，以及这次参与计数的区域和选择；数值层只读取所选正事件数减去负事件数。丰富层可以区别“同样等于一、却发生在不同地点或来自不同来源”的对象。把数值相同的对象取商以后，指定的加、乘、负运算恰好给出整数算术；分数与全部有理 Cauchy 序列再给出有理数与实数。

“道”在这里是一个有类型的情境整体：先说明在哪个档案和区域内谈可能选择，才谈某个选择的相对补集。这是数学建模的名称，不是关于道、物理宇宙或哲学传统的同一性定理。补集投影为算术负号需要背景总电荷为零；这个条件既不能省略，也不是自然界的先验守恒律。

产地与证明状态：本稿由 `consensus-rnd:sshx` 流程的一个隔离 codex-cli 实施席按调用方批准的综合方案编写。实际 GPT PRO 思考输入及本稿采取的修正见第 12 节。本文给出 ZFC 内的普通数学证明及附录中的有限精确核验；**本稿没有新增 Lean 证明，不能称为 kernel-verified**。最终独立评审、仓库准入与 PR 生命周期由调用方接续，本文不预报其结果。

> **PR1 增补导航与阅读时序（2026-09-09）。** §1–13、命题 1–15 和附录的原运行记录保留为基线叙述；其中“本次”及 §12 的 PRO task 均指原稿那次工作。当前增补由 Codex 实施：[§14 观察同余](#pr1-observation)扩充 §9 的下降判据，[§15 精确空间读数](#pr1-spatial)将 §8 定义 12／命题 9 特化到共同位置，[§16 明确语言下的充分性](#pr1-languages)接通 §8/9，[§17 反例、来源与本轮核验](#pr1-boundaries)说明适用边界。附录仍只有一个 Python 核验块，已在其中追加 PR1 检查。本轮调用与评审状态单列于 §17，不沿用原稿 PRO 成功记录。

> **PR2 增补导航与显式勘界（2026-09-09）。** 本批在固定 PR1 候选上增补：[§18 分层律](#pr2-laws)、[§19 卷积整性与单位](#pr2-units)、[§20 时间摘要及最粗充分性](#pr2-theta)、[§21 整数时标规则](#pr2-time)、[§22 带参考点的空间运输](#pr2-reference)、[§23 来源与核验边界](#pr2-evidence)。§17 的“下一批”“本轮”保留为 PR1 当时的范围记录；§12 仍仅是原稿的旧 PRO 收据。本批不改变定义 6 的默认零参考点及 `max+1`，也不把空间商的环律提升为档案律。新增核验继续放在附录原有唯一 Python 块中。

## 1. 有限情境、整体与类型

固定空间维数 $d=3$。一般结论对任一预先固定的有限 $d\geq1$ 同样成立。令 $HF=V_\omega$ 为遗传有限集合的集合，自然数取有限 von Neumann 序数，有序对取 Kuratowski 编码，有限元组由有序对编码。为保证整数坐标也是有限编码，取 $\mathbb Z_{\rm code}=(\{0\}\times\mathbb N)\cup(\{1\}\times\mathbb N_{>0})$，其中 $(0,m)$ 表示 $m$，$(1,m)$ 表示 $-m$。它与通常整数显式双射，序和算术沿此双射运输；全文把这份实现简记为 $\mathbb Z$。不把通常整数的无限等价类表示直接塞入 $HF$。来源树集合 $T\subset HF$ 由下列有限构造生成：

$$
\operatorname{leaf}(n)\quad(n\in\mathbb N),\qquad
\operatorname{pair}(r,s)\quad(r,s\in T).
$$

叶与有序二叉节点使用不同标签。来源树中的重复叶表示重复引用同一来源；它既不创建新的随机变量，也不证明概率独立。事件出现标识 $e\in HF$ 与来源标识 $\rho(e)\in T$ 是不同数据，多个事件可以具有同一来源树。

**定义 1（情境与丰富整数表示）。** 情境是元组

$$
C=(E,\prec,t,x,\sigma,\rho,\Omega),
$$

其中 $E\subset HF$ 有限，称为档案；$\prec\subset E\times E$ 是严格偏序；$t:E\to\mathbb Z$、$x:E\to\mathbb Z^3$、$\sigma:E\to\{1,-1\}$、$\rho:E\to T$ 为全函数，且

$$
e\prec f\Longrightarrow t(e)<t(f),\qquad \Omega\subseteq E.
$$

$\Omega$ 是本次的**当前整体**，即候选贡献区域。丰富表示是 $X=(C,A)$，其中 $A\subseteq\Omega$ 是本次选中的贡献。档案中的 $E\setminus\Omega$ 不参与本次读数。空档案、空区域和空选择均允许。时间只是本模型的离散时标，偏序不是由距离推导出的光锥关系。

**定义 2（有类型的情境整体）。** 记

$$
\mathcal D_C=(C,\Omega,\mathcal P(\Omega)),\qquad
N_C(A)=\Omega\setminus A.
$$

这就是本文的类道整体。它同时指明语境、论域和该论域上的选择空间。$A$ 是 $\mathcal P(\Omega)$ 的一个元素；若 $K\subseteq\mathcal P(\Omega)$ 是一个可能选择族，则 $\mathcal P(\Omega)\setminus K$ 才是“排除这些可能选择”的另一层补集。后者不是 $N_C(A)$。第 10 节的世界域 $\Gamma$ 又是另一个有类型的集合。

不能把“当前选择”默认为已执行的因果过去。例如令 $E=\Omega=\{e,f\}$、$e\prec f$、$t(e)=0,t(f)=1$、符号分别为 $+1,-1$。$\{e\}$ 向下闭，而其补集 $\{f\}$ 不向下闭。因此在一般偏序中，“所有允许选择向下闭”与“任意选择允许取补”不能同时作为本算术载体的要求。需要执行语义的应用可另取允许历史族 $\operatorname{Adm}_C\subseteq\mathcal P(\Omega)$，但必须重新检查其运算闭包；本文算术核心使用全部子集。

档案的“历史”仅指所写入的事件、偏序、坐标、符号和来源树。它不记录未观测的物理事实，也不自动保存每个中间步骤的选择。下文的乘法保证旧事件结构嵌入结果档案，**不保证从结果恢复所有旧选择或旧当前区域**。

```text
丰富表示 (档案 E；当前区域 Omega；选择 A)
              | 保留事件结构，按指定规则运算
              v
        新档案 / 新区域 / 新选择
              | q = 所选正数 - 所选负数
              v
          整数读数及其算术商
```

## 2. 有符号读数与补集负号

**定义 3。** 对 $A\subseteq\Omega_C$ 定义

$$
q_C(A)=\sum_{e\in A}\sigma(e)
=|\{e\in A:\sigma(e)=1\}|-|\{e\in A:\sigma(e)=-1\}|,
\quad u(C)=q_C(\Omega_C),\quad q(X)=q_C(A).
$$

一般情境允许 $u(C)\ne0$。算术载体 $\mathcal B$ 是所有满足 $u(C)=0$ 的丰富表示的集合，称为平衡表示。对它定义 $N(X)=(C,N_C(A))$。平衡是当前整体相对于这个读数的条件，不要求整个档案平衡，也不要求每个地点或来源分别平衡。

**命题 1（补集恒等式及必要条件）。** 在每个有限情境中，对所有 $A\subseteq\Omega_C$，

$$
q_C(N_C(A))=u(C)-q_C(A),\qquad N_C(N_C(A))=A.
$$

并且 $u(C)=0$ 当且仅当对全部 $A\subseteq\Omega_C$ 都有 $q_C(N_C(A))=-q_C(A)$。

**证明。** $A$ 与 $\Omega_C\setminus A$ 不交且并为 $\Omega_C$，有限和的可加性给出第一式。第二式由 $A\subseteq\Omega_C$ 的逐点成员关系给出；这里完整情境保持不动。若 $u=0$，第一式即负号公式；反向取 $A=\varnothing$，得到 $u=0$。证毕。

下列各物不能互换：

| 操作或对象 | 类型与含义 |
| --- | --- |
| $N_C(A)=\Omega_C\setminus A$ | 另一个贡献子集，是点值运算 $\mathcal P(\Omega_C)\to\mathcal P(\Omega_C)$ |
| $N_C[K]=\{N_C(A):A\in K\}$ | 可能选择族的直接像，不是 $\mathcal P(\Omega_C)\setminus K$ |
| $q_C[K]=\{q_C(A):A\in K\}$ | 可能数值的集合；不能把互斥选择的读数相加当作一次实际读数 |
| $\operatorname{Opp}_C(A)=\{B\subseteq\Omega_C:q_C(B)=-q_C(A)\}$ | 反数值纤维，是子集组成的集合；平衡时包含 $N_C(A)$，通常不止一个元素 |
| $\Gamma\setminus W$，其中 $W\subseteq\Gamma$ | 世界层面的逻辑排除，不对每个世界的贡献逐项取补 |
| 全档案符号翻转 $\sigma\mapsto-\sigma$ | 改变情境、保持选择的另一种表示操作，在一般情境也投影为负号 |
| $-q(X)$ 与 $1/q(X)$ | 前者为加法逆，后者只在非零域上为乘法逆；例如 $-2\ne1/2$ |

例如平衡的非空 $\Omega$ 中，$\operatorname{Opp}_C(\varnothing)$ 至少包含 $\varnothing,\Omega$，故不能把它等同于唯一的补集。用满足 $q(s(n))=n$ 的选定代表函数 $s:\mathbb Z\to\mathcal B$ 定义 $L(X)=s(-q(X))$，虽然也投影为负号，但 $L^2(X)=s(-q(s(-q(X))))=s(q(X))$，一般不等于 $X$。相反，保留完整 $C$ 的 $N^2(X)=X$ 是精确等式；丢掉 $C,A$ 后再选代表不能恢复它们。

## 3. 并行加法、时间复合与档案乘法

所有标签采用固定的集合编码。对两个输入分别使用 $\iota_0(e)=(0,e)$、$\iota_1(f)=(1,f)$；生成事件使用第三个标签 $(2,(a,b))$，因此即使输入档案重合，结果中的出现也不碰撞。标签不会改写来源树中的叶编号。

**定义 4（并行加法）。** $X\boxplus Y$ 的档案、当前区域、选择分别为

$$
\iota_0[E_X]\sqcup\iota_1[E_Y],\quad
\iota_0[\Omega_X]\sqcup\iota_1[\Omega_Y],\quad
\iota_0[A_X]\sqcup\iota_1[A_Y].
$$

时间、位置、符号、来源照抄各自输入，只复制内部偏序，不增加跨输入的因果边。

**定义 5（有守卫的时间复合）。** $X\triangleright Y$ 使用同一带标签并集，但增加全部关系 $\iota_0(e)\prec\iota_1(f)$，其中 $e\in E_X,f\in E_Y$。它的定义域恰为

$$
\forall e\in E_X\ \forall f\in E_Y,\quad t_X(e)<t_Y(f).
\tag{T}
$$

这个条件检查整个档案，空输入时按空真解释。不暗中平移绝对时间。若使用显式时间平移 $T_k(C)$（把所有 $t(e)$ 换成 $t(e)+k$，$k\in\mathbb Z$），则表达式必须写为 $X\triangleright T_k(Y)$。非空有限档案总可选 $k>\max t_X-\min t_Y$ 使之合法，但这已是不同的坐标数据。

**命题 2（两种复合的闭包与读数）。** 并行加法总产生合法情境；时间复合在 $T$ 上产生合法情境；二者的读数均为 $q(X)+q(Y)$，背景电荷均为 $u(C_X)+u(C_Y)$，故均在各自定义域内保持平衡。

**证明。** 并行并集内部的传递性与严格性由输入继承，跨分量无边。时间复合中的跨边全部从左向右，内部边接跨边仍是已经加入的跨边，所以关系传递、无环；每条内部边时间递增，每条跨边由 $T$ 时间递增。有限和分别在两个不交分量上求和，得读数公式；用当前整体替换选择得到背景公式。证毕。

**定义 6（档案乘法）。** $P=X\boxtimes Y$ 的档案为

$$
E_P=\iota_0[E_X]\sqcup\iota_1[E_Y]\sqcup
\{p_{ab}=(2,(a,b)):a\in\Omega_X,b\in\Omega_Y\}.
$$

旧事件的四个属性照抄。每个新事件满足

$$
\begin{aligned}
t_P(p_{ab})&=\max(t_X(a),t_Y(b))+1,\\
x_P(p_{ab})&=x_X(a)+x_Y(b),\\
\sigma_P(p_{ab})&=\sigma_X(a)\sigma_Y(b),\\
\rho_P(p_{ab})&=\operatorname{pair}(\rho_X(a),\rho_Y(b)).
\end{aligned}
$$

保留两份旧偏序，加入 $\iota_0(a)\prec p_{ab}$ 与 $\iota_1(b)\prec p_{ab}$，然后取传递闭包。当前整体与选择是

$$
\Omega_P=\{p_{ab}:a\in\Omega_X,b\in\Omega_Y\},\qquad
A_P=\{p_{ab}:a\in A_X,b\in A_Y\}.
$$

旧事件只入档案、不重复计数。新当前整体使用所有候选对，不能用所选对替代它，否则补集的背景也被改了。

**命题 3（乘法合法、精确投影与档案保留）。** 档案乘法总产生合法有限情境，且

$$
q(X\boxtimes Y)=q(X)q(Y),\quad
u(C_P)=u(C_X)u(C_Y),\quad
|E_P|=|E_X|+|E_Y|+|\Omega_X||\Omega_Y|.
\tag{P}
$$

因此 $\mathcal B$ 对乘法封闭。每个输入档案通过带标签映射嵌入 $E_P$，其内部偏序被保持和反映，四个属性被原样保持；即使一因子的读数为零或当前区域为空，也保留两份输入档案。

**证明。** 生成关系的每条边都严格增加整数时间：旧边由假设保证，新增父边由 $\max+1$ 保证。沿任何非空路径，时间仍严格增加，因此传递闭包无自环且满足时标条件。它是有限集合 $E_P^2$ 的子集，可由长度至多 $|E_P|-1$ 的路径刻画，故存在且有限。新节点无出边，不能经它绕回任何旧档案；旧两分量之间也无路径，所以限制在任一旧分量上的关系正是原关系。三个标签互斥，立即给出基数公式。最后分配有限双重和：

$$
\sum_{a\in A_X}\sum_{b\in A_Y}\sigma_X(a)\sigma_Y(b)
=\left(\sum_{a\in A_X}\sigma_X(a)\right)
 \left(\sum_{b\in A_Y}\sigma_Y(b)\right).
$$

把 $A_X,A_Y$ 分别替换为 $\Omega_X,\Omega_Y$ 即得背景公式。空区域时新事件为空，但两个旧档案仍在并集中。证毕。

这里的嵌入是**档案嵌入**，不是第 8 节保持当前区域的情境嵌入：旧当前区域在乘法之后退入档案。尤其 $X\boxtimes 0_\varnothing$ 不编码 $A_X$，因为新选择总为空；不同旧选择可以产生同一个结果。保留已写入事件与恢复全部操作历史是不同保证。

## 4. 三种相等与整数商

**定义 7。** 区别以下三种关系。

1. **编码相等** $X=Y$：整个集合编码逐项相等，含事件标签。
2. **历史同构** $X\cong_hY$：存在双射 $h:E_X\to E_Y$，保持和反映偏序，逐事件保持 $t,x,\sigma,\rho$，并满足 $h[\Omega_X]=\Omega_Y$、$h[A_X]=A_Y$。本定义不把来源重命名或坐标变换自动当作相等。
3. **数值等价** $X\sim Y$：$q(X)=q(Y)$。

编码相等蕴含历史同构，历史同构由有限和重索引蕴含数值等价。反向均失败：重命名事件可改变编码却保留历史同构；第 5 节的并行与时间复合读数相同而因果边数不同。读数连同纤维中的具体点可以表述原对象，但读数本身不能选择原点。

**定义 8（固定整数代表）。** 对 $n\in\mathbb Z$，令 $m=|n|$，取

$$
E_n=\Omega_n=\{(i,s):0\le i<m,\ s\in\{+1,-1\}\}.
$$

偏序为空，所有时间和位置为零，符号为 $s$，来源为 $\operatorname{leaf}(i)$。若 $n>0$ 选全部正事件；若 $n<0$ 选全部负事件；若 $n=0$ 全部数据为空。所得表示记 $\mathbf i(n)$。它满足 $u=0,q=n$。记 $0_\varnothing=\mathbf i(0)$、$U=\mathbf i(1)$。固定代表是取商的截面，不是被忘历史的重建算法。

**命题 4（整数算术同构）。** $\sim$ 是 $\mathcal B$ 上的等价关系，并且是 $\boxplus,\boxtimes,N$ 的同余关系。商集 $\mathbb Z_{\rm st}=\mathcal B/{\sim}$ 在这些诱导运算下是与 $\mathbb Z$ 同构的环，唯一指定的同构为

$$
\bar q_{\mathbb Z}([X])=q(X).
$$

在 $q\ge0$ 的表示子集上，仅用加、乘、零、一取商，得到 $\mathbb N$ 的半环；负号不封闭于该子集。

**证明。** 等价关系来自整数相等。若输入读数相同，命题 1、2、3 表明操作后的读数也相同，故商上运算良定义。商映射由定义良定义且单射，由 $\mathbf i(n)$ 满射，且保加、乘、负、零、一。任一环恒等式两侧经它映到整数中的同一值；单射性把等式带回商上，包括结合、交换、分配、加法逆及乘法单位律。因此是环同构，而不是先假定丰富层已经是环。非负部分以同样方法对应自然数，得最后结论。证毕。

原始历史层的较强结论有具体反例。若 $X$ 的档案非空，则 $X\boxplus N(X)$ 有 $2|E_X|>0$ 个事件，不能与空档案同构，虽读数为零。任意与 $X$ 并行相加的表示都不能使档案变空，所以非空表示没有相对于空档案的原始加法逆。这**不推出消去律失败**：在固定标签的编码相等下，从 $X\boxplus Y=X\boxplus Z$ 取右标签分量并去标签，反而立即得到 $Y=Z$。

任一平衡的数值一表示 $V$ 至少有两个当前事件及两个档案事件；由 $P$，对所有 $X$，

$$
|E_{X\boxtimes V}|=|E_X|+|E_V|+|\Omega_X||\Omega_V|>|E_X|.
$$

所以它不是原始历史层的乘法单位。原始乘法甚至不必结合到历史同构：取 $X=Y=\mathbf i(1)$、$Z=\mathbf i(2)$，其 $(|E|,|\Omega|)$ 分别为 $(2,2),(2,2),(4,4)$，则

$$
|E_{(X\boxtimes Y)\boxtimes Z}|=8+4+4\cdot4=28,
\quad |E_{X\boxtimes(Y\boxtimes Z)}|=2+14+2\cdot8=32.
$$

两者读数都为 $2$。这些计数针对本稿保留档案的乘法，不是单纯 Cartesian 事件乘法的计数。

## 5. 一个完整的时空算例

以下位置只列第一坐标，另外两维为零。令 $E_X=\Omega_X=\{a,b,c,d\}$，选择 $A_X=\{a,b,c\}$；$E_Y=\Omega_Y=\{r,s\}$，选择 $A_Y=\{r\}$。

| 事件 | 时间 | 位置第一坐标 | 符号 | 来源 |
| --- | --- | --- | --- | --- |
| $a$ | 0 | 0 | $+1$ | leaf(7) |
| $b$ | 1 | 2 | $+1$ | leaf(7) |
| $c$ | 1 | 1 | $-1$ | leaf(8) |
| $d$ | 2 | 3 | $-1$ | leaf(8) |
| $r$ | 3 | 10 | $+1$ | leaf(7) |
| $s$ | 4 | 10 | $-1$ | leaf(9) |

$X$ 的偏序为 $a\prec b,c\prec d$，$Y$ 的偏序为 $r\prec s$。两个整体均平衡，$q(X)=q(Y)=1$，$N(X)$ 只选 $d$，读数为 $-1$。并行和与时间复合都合法、读数都是 $2$，都有六个档案事件；前者有三对严格可比事件，后者增加八个跨输入关系而有十一对，故不同历史。

乘积有六个旧档案事件和八个新候选事件，总计十四个；当前只计新事件。三个所选新事件为

| 事件 | 时间 | 位置第一坐标 | 符号 | 来源 |
| --- | --- | --- | --- | --- |
| $p_{ar}$ | 4 | 10 | $+1$ | pair(leaf(7), leaf(7)) |
| $p_{br}$ | 4 | 12 | $+1$ | pair(leaf(7), leaf(7)) |
| $p_{cr}$ | 4 | 11 | $-1$ | pair(leaf(8), leaf(7)) |

因此乘积读数 $1+1-1=1$，新背景有四正四负，仍平衡。传递闭包共有二十七对严格可比事件。重复的来源 7 仍是同一个叶标识；两次出现及两次引用由不同事件标签保留。

$X\boxtimes0_\varnothing$ 有四个旧档案事件、空当前整体和空选择，读数为零。若把 $Y$ 改为选择 $\{r,s\}$ 的数值零，乘积仍有十四个档案事件、八个当前事件、六个所选事件，读数也是零。普通数值零不意味着没有事件、没有来源或没有可供后续结构观察的记录。

## 6. 有理数表示与精确除法

**定义 9。** 令 $\mathcal Q^{\rm rich}=\{(X,Y)\in\mathcal B^2:q(Y)\ne0\}$，记 $v(X,Y)=q(X)/q(Y)\in\mathbb Q$，这里右端的 $\mathbb Q$ 是 ZFC 中标准整数分数构造。定义

$$
(X,Y)\sim_{\mathbb Q}(X',Y')
\quad\Longleftrightarrow\quad q(X)q(Y')=q(X')q(Y).
$$

对 $R=(X,Y),S=(Z,W)$，取以下丰富运算；每次出现的 $\boxplus,\boxtimes,N$ 均为前述档案运算：

$$
\begin{aligned}
R\boxplus_{\mathbb Q}S&=((X\boxtimes W)\boxplus(Z\boxtimes Y),\ Y\boxtimes W),\\
R\boxtimes_{\mathbb Q}S&=(X\boxtimes Z,\ Y\boxtimes W),\\
N_{\mathbb Q}(R)&=(N(X),Y),\\
R^{-1}_{\mathbb Q}&=(Y,X)\quad\text{仅当 }q(X)\ne0,\\
R\div_{\mathbb Q}S&=(X\boxtimes W,\ Y\boxtimes Z)
\quad\text{仅当 }q(Z)\ne0.
\end{aligned}
$$

**命题 5（有理数商与除法守卫）。** 这些运算在所写域上封闭，$\sim_{\mathbb Q}$ 是同余关系，$\mathcal Q^{\rm rich}/{\sim_{\mathbb Q}}$ 经 $[R]\mapsto v(R)$ 与标准有理数域同构；求逆与除法的定义域只由相应数值等价类决定。

**证明。** 非零整数分母 $b,d$ 的乘积 $bd\ne0$，故加、乘后的分母合法。求逆后的分母是原分子，除法后的分母是 $bc$，所以额外守卫恰是 $c\ne0$。在非零分母上，交叉相乘等价于标准分数相等，因而 $\sim_{\mathbb Q}$ 自反、对称、传递。也可直接验证传递性：由 $ad=cb$ 与 $cf=ed$ 得 $adf=bed$，消去非零的 $d$ 得 $af=be$。命题 1 至 3 把上述读数依次化为 $(ad+cb)/(bd)$、$ac/(bd)$、$-a/b$、$b/a$、$ad/(bc)$，正是有理运算。因此输入等价时输出等价，守卫也不随代表而变。商映射由等价的定义单射；任一 $a/b$ 由 $(\mathbf i(a),\mathbf i(b))$ 表示，故满射。域定律由双射和运算保持性传递。证毕。

以后固定截面 $s_{\mathbb Q}(a/b)=(\mathbf i(a),\mathbf i(b))$，其中取唯一既约形式 $b>0$，零写为 $0/1$；整数嵌入为 $X\mapsto(X,U)$。例如丰富公式给出的 $(1/2)+(-3/2)=-1$、$(1/2)(-3/2)=-3/4$、$(1/2)/(-3/2)=-1/3$ 都是精确等式的投影，不是浮点近似。

**整数域内的除法另有条件。** 若要求结果仍在 $\mathbb Z$，必须同时满足 $q(Y)\ne0$ 与 $q(Y)\mid q(X)$；商数 $k$ 是满足 $q(X)=kq(Y)$ 的唯一整数，可用 $\mathbf i(k)$ 选代表。这个额外选择不保存输入档案。若保留分数表示 $(X,Y)$，则它仍携带两份输入，且在可整除时代表同一个整数值。$1/2$ 不在整数精确除法的域内，但在有理除法的域内；截断除法、带余除法是另外的操作，不在此冒充域除法。

## 7. 全部实数、有限前缀与表达式兼容性

**定义 10（丰富实数表示）。** 令

$$
\mathcal R^{\rm rich}=
\{R:\mathbb N\to\mathcal Q^{\rm rich}:a_n=v(R_n)\text{ 在 }\mathbb Q\text{ 中为 Cauchy 序列}\}.
$$

“Cauchy”指对每个有理 $\varepsilon>0$，存在 $N$，使所有 $m,n\ge N$ 满足 $|a_m-a_n|<\varepsilon$。这里取的是**全部**满足条件的序列，不限于可计算序列或有限程序可命名的序列。定义 $R\sim_{\mathbb R}S$ 当且仅当 $v(R_n)-v(S_n)\to0$。序列指标 $n$ 表示近似精度，不是事件的物理时间；不把这些有限图说成具有已证明的连续时空极限。

加、乘、负逐项使用第 6 节的丰富公式。常数嵌入是有理表示的常值序列。按 ZFC 中的标准有理 Cauchy 完备化记 $\widehat{\mathbb Q}$；其元素是 Cauchy 序列模零序列差的等价类。暂记 $\ell(R)=[(v(R_n))]\in\widehat{\mathbb Q}$，不先假定每个实数已经有某个有限事件编码。

**命题 6（实数完备化与合法求逆）。** 上述逐项运算对 $\mathcal R^{\rm rich}$ 封闭，等价关系是同余关系；映射 $[R]\mapsto\ell(R)$ 是到标准实数域 $\widehat{\mathbb Q}\cong\mathbb R$ 的同构。对于一条 Cauchy 读数序列 $a_n$，以下条件等价：

$$
[(a_n)]\ne0
\quad\Longleftrightarrow\quad
\exists\delta\in\mathbb Q_{>0}\ \exists N\ \forall n\ge N,
\ |a_n|\ge\delta.
\tag{R}
$$

在这个定义域上，求逆可逐项**完整**定义为

$$
(\operatorname{Inv}R)_n=
\begin{cases}
(R_n)^{-1}_{\mathbb Q},&a_n\ne0,\\
R_n\boxplus_{\mathbb Q}N_{\mathbb Q}(R_n),&a_n=0.
\end{cases}
\tag{I}
$$

第二分支是合法的丰富有理零，不包含除以零；在 (R) 上，它只会在有限前缀被使用。实数除法定义为逐项乘以 (I)，只要求**除数实数类非零**。

**证明。** 先记录 Cauchy 序列的有界性：取误差 $1$ 的尾部阈值，尾部绝对值至多某个固定项绝对值加 $1$；有限前缀也有最大绝对值，合并即得统一有理界。和与负的 Cauchy 性来自三角不等式。对有界 Cauchy 序列 $a,b$，若 $|a_n|,|b_n|\le M$，可取 $M\ge1$，则

$$
|a_mb_m-a_nb_n|
\le M|b_m-b_n|+M|a_m-a_n|.
$$

各差取小于 $\varepsilon/(2M)$ 即证明乘法封闭。零差关系的传递性也由三角不等式给出；若 $a-a'\to0,b-b'\to0$，利用统一界和
$a_nb_n-a'_nb'_n=a_n(b_n-b'_n)+b'_n(a_n-a'_n)$，证明乘法与换代表相容。加法与负号同理。因此 $\ell$ 良定义，且由等价关系的定义在商上单射。任意有理 Cauchy 序列 $a$ 可逐项提升为 $s_{\mathbb Q}(a_n)$，故满射，且保运算。

这里用到的标准完备化结论有明确构造内容：常值有理序列嵌入，两个类之差非零时，下面证明的尾部下界与 Cauchy 性使其符号最终固定，据此定义严格序；正性对换代表不变并给出全序域。常值有理类在其中稠密，因为任一 Cauchy 序列的充分后项作为常数，与原类任意接近。若 $c_k$ 是这个商中的 Cauchy 类序列，逐个选有理数 $r_k$ 使 $|c_k-r_k|<2^{-k}$。三角不等式给出 $r_k$ 是有理 Cauchy 序列；其类 $c=[(r_k)]$ 满足 $|c-c_k|\le |c-r_k|+2^{-k}\to0$，其中首项趋零直接来自 $r$ 的 Cauchy 性。这证明序列完备。每个类由有界有理序列表示，故有整数界，域是阿基米德的。对任意非空有上界子集 $S$，选有理上界 $u_0$ 及小于某个成员的有理数 $l_0$；后者不是上界，不要求它是整个 $S$ 的下界。二分区间，每一步保持 $u_n$ 为上界、$l_n$ 不是上界，长度趋零。两端点是 Cauchy 序列并趋于同一个类 $c$。若某成员大于 $c$，充分后的 $u_n$ 就小于该成员，与上界矛盾；若 $b<c$，充分后的 $l_n>b$，而存在成员大于 $l_n$，故 $b$ 不是上界。于是 $c$ 是最小上界，得到标准 Dedekind 完备的阿基米德有序域，即 ZFC 中通常的实数构造。本文对其采用的是标准完备化，不增加连续性或完备性公理。

再证 (R)。若 $a$ 不是零序列，存在有理 $\varepsilon>0$，使每个尾部都有一项 $|a_j|\ge\varepsilon$。在 Cauchy 误差 $\varepsilon/2$ 的尾部中，给任一项 $a_n$ 选同尾部这样一个 $a_j$，得到 $|a_n|>\varepsilon/2$，可取 $\delta=\varepsilon/2$。反向，尾部下界显然排除趋零。尾部若还取两项差小于 $\delta$，它们不能异号，否则差至少 $2\delta$；这也证明前述符号最终固定。条件只由零差类决定：若 $a-b\to0$，$a$ 的下界 $\delta$ 在 $b$ 的充分后段给出 $\delta/2$ 下界。

在 (R) 上，(I) 的读数后段就是 $1/a_n$，并有

$$
\left|\frac1{a_m}-\frac1{a_n}\right|
\le\frac{|a_m-a_n|}{\delta^2}.
$$

故倒数读数为 Cauchy。若 $a\sim b$，分别取正下界 $\delta_a,\delta_b$，则后段

$$
\left|\frac1{a_n}-\frac1{b_n}\right|
\le\frac{|a_n-b_n|}{\delta_a\delta_b}\longrightarrow0.
$$

所以求逆不依赖代表；乘回原序列的后段恒为 $1$，有限前缀之差是零序列，故商上是乘法逆。有限前缀任意合法替换不改变类，是因为任一给定误差只需把阈值移到该前缀之后。由双射，全部有序域运算与完备性传递到丰富表示的商。证毕。

两个守卫测试不能混为一谈：$(0,1,1,\ldots)$ 表示非零实数 $1$，(I) 得到合法读数 $(0,1,1,\ldots)$，所以要求每项非零过强；$(1,1/2,1/3,\ldots)$ 每项非零，却表示零类，它的逐项倒数 $(1,2,3,\ldots)$ 非 Cauchy，因为任一尾部相邻项距离都是 $1$，所以要求每项非零又不足以保证实数求逆。这是对全序列的证明；附录只检查其有限前缀，不据有限数据判定任意实数是否非零。

没有声称存在可判定的非零实数谓词。(I) 在声明的域上是 ZFC 定义的函数；一般实数的域判定不因此成为可执行判定算法。若从标准实数 $r$ 出发，固定有理近似 $a_n=2^{-n}\lfloor2^nr\rfloor$ 满足 $0\le r-a_n<2^{-n}$，逐项取 $s_{\mathbb Q}(a_n)$ 给出一个丰富表示；所有实数都能这样表示，但并非都由有限字符串或可计算序列表示。

**命题 7（全部有限算术表达式的兼容性）。** 在整数、有理数、实数任一上述层级，取有限的带括号表达式，常数使用固定代表，变量赋以相应丰富表示，运算仅为该层指定的加、乘、负及合法的除法。若每个除法节点满足该层守卫，则丰富求值存在，并且

$$
\operatorname{readout}(\operatorname{Eval}_{\rm rich}(F))
=\operatorname{Eval}_{\rm usual}(F;\operatorname{readout}\text{ 各变量}).
$$

两个合法表达式的普通值相等，当且仅当其结果在该层的数值商中相等；这里不把历史相等解释成普通数相等。

**证明。** 对表达式树作结构归纳。变量和常数由定义成立。加、乘、负节点由子树归纳假设及命题 1 至 6 的相应保持公式成立。除法节点的定义域由读数决定，子树的读数一致故守卫一致；在该域上相应商数公式给出归纳步骤。整数精确除法还使用非零除数下商数的唯一性。相等结论由各层数值等价的定义或商映射单射性成立。证毕。

这一定理不把空间筛选、时间复合的可执行性或任意历史查询都说成旧标量的函数。它们的精确下降条件如下。

## 8. 情境扩张、粗观察与坐标运输

**定义 11（本稿采用的情境嵌入）。** $j:C\hookrightarrow D$ 是单射 $j:E_C\to E_D$，保持四个属性，满足
$e\prec_C f\iff j(e)\prec_D j(f)$，以及 $j[\Omega_C]=\Omega_D\cap j[E_C]$。最后一项既将旧当前整体嵌入新当前整体，也不把旧非当前事件暗中激活。选中部分运输为 $j[A]$。这是明确采用的一类结构保持扩张；更一般的激活或属性改写不自动属于此定义。

**命题 8（扩张的补集缺项）。** 记新增当前区域 $R=\Omega_D\setminus j[\Omega_C]$。则

$$
\begin{aligned}
q_D(j[A])&=q_C(A),\\
\Omega_D\setminus j[A]&=j[\Omega_C\setminus A]\sqcup R,\\
q_D(\Omega_D\setminus j[A])-q_C(\Omega_C\setminus A)&=\sum_{e\in R}\sigma_D(e).
\end{aligned}
$$

所以补集精确交换运输当且仅当 $R=\varnothing$；补集读数交换运输当且仅当新增区域电荷为零。如果 $C,D$ 都平衡，后一条件自动成立，但前一条件仍可能失败。

**证明。** 单射且保持符号，有限和重索引给出第一式。一个新整体中的未选点，要么在旧整体的像中而对应未选旧点，要么在 $R$ 中，且两类不交，给出第二式。对第二式求电荷得第三式。由于两类不交，新增类非空便破坏集合相等；标量相等则恰好要求其有限和为零。对全体旧当前点应用第一式，得 $u(D)=u(C)+q_D(R)$，从而得到平衡推论。证毕。

**递增地平线的具体例子。** 令 $E_n=\Omega_n=\{(i,s):i<n,s\in\{1,-1\}\}$，时间 $i$，位置 $(i,0,0)$，来源 leaf($i$)，符号 $s$，同符号链 $(i,s)\prec(j,s)\iff i<j$，异符号间无序。包含映射形成递增情境族，每次添一正一负而保持平衡。任一固定有限选择在足够大的地平线上可继续运输，补集集合随地平线扩大但其读数按命题 8 保持。其可数并当然是 ZFC 集合，却已不在有限载体中：正负项各无穷，本文没有给其整体定义 $\infty-\infty$。按每对先正后负枚举，部分和交替为 $1,0$，不收敛；按对分组得零是另一种额外求和约定，不能偷渡为无条件无穷总和。

**定义 12（带背景的粗观察）。** 取有限 bin 集合 $B$ 和映射 $f:\Omega_C\to B$，不要求满射。定义

$$
O_f(X)=(B,w,z),\quad
w(b)=\sum_{e\in\Omega_C,\ f(e)=b}\sigma(e),\quad
z(b)=\sum_{e\in A,\ f(e)=b}\sigma(e).
$$

这里 $w,z:B\to\mathbb Z$ 是电荷而不是布尔占据；bin 可承载 $2,-3,0$ 等整数，不必是一个符号为 $\pm1$ 的新事件。粗观察本身也没有自动携带新的合法因果偏序。

**命题 9（粗观察公式）。** 有 $q(X)=\sum_bz(b)$、$u(C)=\sum_bw(b)$，且补集的粗观察为 $(B,w,w-z)$。对有限集合 $D$ 和映射 $g:B\to D$ 定义 $(g_*z)(d)=\sum_{b:g(b)=d}z(b)$，则 $O_{g\circ f}=(D,g_*w,g_*z)$，连续粗化满足 $(h\circ g)_*=h_*g_*$。并行和可取带标签 bin 并集，分别复制两个 $w,z$；若两侧本来映到同一 bin 集合，再去掉 bin 标签，结果为 $(w_X+w_Y,z_X+z_Y)$。乘积的 bin 映射在**新当前事件**上定义为 $p_{ab}\mapsto(f_X(a),f_Y(b))$，满足

$$
w_P(b,c)=w_X(b)w_Y(c),\qquad z_P(b,c)=z_X(b)z_Y(c).
$$

再按 $h:B_X\times B_Y\to D$ 合 bin 时，分别对这些乘积作 $h_*$，而不是把旧档案再次计入。

**证明。** 各纤维是有限论域的不交分割，总和可分组；每个纤维内的“未选电荷”为背景减所选电荷。复合推送是把同一个有限和先分两次组或一次分组，两者逐项相同。并行公式是两份不交和的相加；乘积一个 bin 对上的选择恰为对应两个所选纤维的 Cartesian 积，有限双和分配即得公式。证毕。

例如一正一负分别落在两个 bin 时，整体 $u=0$，但 $w=(1,-1)\ne(0,0)$；选择正项有 $z=(1,0)$，补集为 $w-z=(0,-1)$，不是 $-z=(-1,0)$。因此标量平衡不足以推出每个空间 bin 或来源各自平衡。

**命题 10（直接像补集的精确边界）。** 若 $f:\Omega\twoheadrightarrow B$ 满射、$A\subseteq\Omega$，则

$$
f[\Omega\setminus A]=B\setminus f[A]
\quad\Longleftrightarrow\quad A=f^{-1}[f[A]].
$$

右端称为纤维饱和，即每个纤维全选或全不选。

**证明。** 饱和时，一个 bin 在 $f[A]$ 中即其全部原像都在 $A$，否则满射保证它有一个不在 $A$ 的原像，所以两侧互为补集。反向，若某个纤维既有选点又有未选点，其 bin 同时属于 $f[A]$ 和 $f[\Omega\setminus A]$，与等式右侧的不交性矛盾。证毕。

反例：$\Omega=\{a,b,c\}$，$f(a)=f(b)=0,f(c)=1,A=\{a\}$，则 $f[\Omega\setminus A]=\{0,1\}$，而 $\{0,1\}\setminus f[A]=\{1\}$。不满射时需把论域改为 $f[\Omega]$，否则未命中的 bin 也会破坏补集式。任意映射的**逆像**则总满足 $f^{-1}[V\setminus U]=f^{-1}[V]\setminus f^{-1}[U]$，由成员逻辑立即成立。

如果还要把粗观察实现成一个每点符号为 $\pm1$ 的新情境，对全部饱和选择保电荷的条件是每个纤维总电荷恰等于目标符号；充分性由分组求和得出，必要性取单一完整纤维。它不覆盖任意非饱和选择，且许多纤维电荷根本不是 $\pm1$。若强行把两个所选正事件合成一个正事件，读数就从 $2$ 变成 $1$。

因果运输另有障碍：原档案只有 $a\prec b,c\prec d$，时间分别 $0,1,0,1$。将 $a,d$ 合并为 $L$，$b,c$ 合并为 $R$，会得到 $L\prec R\prec L$。因此任意事件合并不能被称作合法情境商；时间与偏序的运输须另外证明。

**坐标运输的确切范围。** 给定整数矩阵 $M$，把所有位置换成 $Mx$ 仍是合法情境，且 $M(x+y)=Mx+My$ 保证它与档案乘法交换。非单射 $M$ 可以丢失空间信息；$M\in GL_3(\mathbb Z)$ 才给出可逆的这种坐标变换，而固定坐标定义下的历史同构仍要求坐标值相等。共同空间平移 $x\mapsto x+v$ 与乘法一般不交换：先平移两个输入，新事件位置为 $x+y+2v$；先乘再平移为 $x+y+v$。共同整数时间平移则满足 $\max(t+k,s+k)+1=\max(t,s)+1+k$，保持乘法及 (T)。任意严格递增时间重标虽保持输入偏序，却不一定保持 $\max+1$；例如乘以 $2$ 把生成时间的增量变为 $2$ 而非 $1$。来源运输也须保持叶的共享关系与 pair 构造。空间筛选要随坐标变换运输其区域，固定区域的读数一般会变。本文据此只声明所写结构的运输条件，不声明一般时空协变或物理对称性。

## 9. 结构运算与不能下降的精确原因

**定义 13（结构筛选）。** 对空间区域 $S\subseteq\mathbb Z^3$、来源树集合 $L\subseteq T$、档案子集 $D\subseteq E_C$，定义

$$
\begin{aligned}
F_S(C,A)&=(C,\{e\in A:x(e)\in S\}),\\
F_L(C,A)&=(C,\{e\in A:\rho(e)\in L\}),\\
F_{\downarrow D}(C,A)&=(C,\{e\in A:\exists d\in D\ (e=d\ \lor\ e\prec d)\}).
\end{aligned}
$$

这些操作只改选择，完整背景不变，故均保留平衡情境。也可按“来源树含某个叶”取 $L$，以观察复合来源。它们是 ZFC 定义的合法丰富运算，但通常不是旧读数的函数。

第 5 节在同一个 $C_X$ 中取 $A=\{a,b,c\}$、$A'=\{a\}$，二者读数都为 $1$。空间区域 $x_1\ge2$ 筛选后分别为 $1,0$；来源集合 $\{\operatorname{leaf}(7)\}$ 筛选后分别为 $2,1$；$D=\{b\}$ 的因果过去筛选后也是 $2,1$。因此同数值仍可在空间、来源和因果观测上有可计算的差别，时空不是附在数字上的无作用装饰。

**命题 11（总操作与部分操作的下降判据）。** 设 $q:\mathcal X\twoheadrightarrow Q$ 为满射，$U:\mathcal X\to\mathcal X$ 是确定性总操作。存在唯一 $\bar U:Q\to Q$ 使 $q\circ U=\bar U\circ q$，当且仅当

$$
q(X)=q(Y)\Longrightarrow q(U(X))=q(U(Y)).
\tag{D}
$$

对部分操作 $U:D\to\mathcal X$，若下降还须保留**恰好相同的定义域**，则另外且恰好要求 $D=q^{-1}[q[D]]$，并要求 (D) 对 $X,Y\in D$ 成立。多元版本把 $q$ 换成乘积读数，结论相同。

**证明。** 有下降时，等输入读数经同一函数必有等输出读数；部分版本的定义域必须是某个 $Q$ 子集的全逆像，故饱和。反之，总操作令 $\bar U(r)$ 为纤维 $q^{-1}(r)$ 中任一元素经 $U$ 后的读数，(D) 保证它是唯一值，满射保证存在，故其图定义一个唯一函数，无须把某个选点说成原历史。部分版本在 $q[D]$ 上用同一构造；饱和性使其拉回域恰等于 $D$。证毕。

时间复合说明部分域条件不可省。$X=Y=U$ 的时间全为零，所以 $(X,Y)$ 不满足 (T)；把第二个 $U$ 的时间显式平移到 $1$，两个输入的数值仍为 $(1,1)$，但此时可以时间复合。它的输出读数在合法域上总是和，却不能把“何时可复合”仅凭两个旧整数完整表达。

**定义 14（关系限制的乘积选择）。** 给定 $R\subseteq\Omega_X\times\Omega_Y$，使用定义 6 的**完整乘积情境**，只把选择改为 $\{p_{ab}:(a,b)\in(A_X\times A_Y)\cap R\}$，记 $X\boxtimes_RY$。例如 $R$ 可由空间距离、来源匹配或明定的跨情境关系给出。

**命题 12（遗漏对电荷与普适性障碍）。** 对固定输入情境与固定 $R$，

$$
q(X\boxtimes_RY)=q(X)q(Y)-
\sum_{(a,b)\in(A_X\times A_Y)\setminus R}\sigma_X(a)\sigma_Y(b).
$$

对所有选择都与普通乘法兼容，当且仅当 $R=\Omega_X\times\Omega_Y$。

**证明。** 将全部所选对分成保留对和遗漏对，有限和相减即第一式。全保留时修正项为空。若缺少任何一对 $(a,b)$，取单点选择 $A_X=\{a\},A_Y=\{b\}$，受限输出为零而原乘积为 $\sigma_X(a)\sigma_Y(b)\in\{1,-1\}$，所以全称断言失败。证毕。

在第 5 节取关系 $|x_1(a)-x_1(b)|\le9$，其中左、右自变量分别来自两个输入；它从所选三对中恰去掉 $(a,r)$。于是受限读数 $1-1=0$，遗漏电荷为 $1$，与完整乘积读数 $1$ 的差精确对应。不能只改配对规则，再继续无条件引用普通乘法公式。

## 10. 不确定历史与共同来源

**定义 15（同一世界上的语义）。** 取一个集合 $S$ 的来源变量名，每个变量 $s$ 有非空值域 $V_s$，选择一个**非空**联合赋值域

$$
\Gamma\subseteq\prod_{s\in S}V_s.
$$

不确定丰富状态是函数 $H:\Gamma\to\mathcal B$，或有理、实数层的相应函数。若固定情境，可写成 $H(\gamma)=(C,A(\gamma))$；允许情境随世界而变时，仍须逐世界满足全部类型与平衡条件。变量名可与来源树中的自然数叶对应；一个共同来源的多次引用必须使用同一个 $\gamma(s)$。

若声称 $H$ 只依赖 $S_0\subseteq S$，其精确定义是：任意 $\gamma,\eta\in\Gamma$ 在 $S_0$ 上相同，就有 $H(\gamma)=H(\eta)$。来源标签本身不证明这个性质，也不证明 $S_0$ 最小。多个满足此条件的函数经指定点态运算，至多依赖它们依赖域的并；是否还能缩小由函数本身决定。在数值层，$t-t$ 就是依赖可以完全消失的例子。

**联合约束不能从边缘读数推定。** 对 $\Gamma_i\subseteq\prod_{s\in S_i}V_s$，自然连接

$$
J=\{\gamma\in\prod_{s\in S_1\cup S_2}V_s:
\gamma|_{S_1}\in\Gamma_1,\ \gamma|_{S_2}\in\Gamma_2\}
$$

是兼容这两组局部条件的**最大**域。实际联合模型可为 $\Gamma=J\cap K$，其中 $K$ 保存所有额外联合约束。即使 $S_1\cap S_2=\varnothing$，仍不能从变量名不同推出 $K=J$。例如两个变量各取 $\{1,2\}$，实际域只允许 $(1,1),(2,2)$，它的两个边缘都是全值域，但两个交叉组合都不允许。若另外给了概率测度，概率独立要求联合测度的相应分解；provenance 或域为 Cartesian 积均不单独证明它。$\Gamma=\varnothing$ 表示约束不相容，不能冒充数值零；零值模型在非空域上给出像 $\{0\}$，不相容模型的像是空集。

**命题 13（共同世界上的点态算术）。** 对所有函数在同一非空 $\Gamma$ 上点态求值，命题 7 的兼容性逐世界成立；随后才取可能值像

$$
\operatorname{Poss}_\Gamma(F)
=\{\operatorname{Eval}_{\rm usual}(F; q(H_1(\gamma)),\ldots,q(H_k(\gamma))):\gamma\in\Gamma\}.
$$

其中 $q$ 在有理或实数层换为相应读数。不能用各函数边缘可能值的无条件 Cartesian 组合替代该像。

**证明。** 固定一个 $\gamma$，全部输入为合法确定性表示，命题 7 即给等式；对所有 $\gamma$ 作函数像得集合等式。边缘像遗忘哪些值能在同一 $\gamma$ 上同时出现，下面的例子严格证明这种遗忘可能改变结果。证毕。

令唯一来源 $t\in\{1,2\}$，在四事件平衡整体上取两个正贡献和两个负贡献，时间、位置为零，偏序为空，来源均为 leaf(7)。在世界 $t$ 中选前 $t$ 个正贡献，得到函数 $H$ 的读数恰为 $t$。于是

$$
\operatorname{Poss}(H\boxplus N(H))=\{0\},\qquad
\operatorname{Poss}(H\boxtimes H)=\{1,4\}.
$$

错误地将两次引用独立取值，会分别给出 $\{-1,0,1\}$ 与 $\{1,2,4\}$。乘积来源树 pair(leaf(7), leaf(7)) 表示同一个来源的两次引用；它不是两个独立随机来源。这里出现的集合都只是可能值像，既不等于贡献补集，也不等于一个实际总电荷。

点态除法还须在**每个世界**满足该层守卫。若某世界除数为零，则整个 $\Gamma$ 上的除法函数未定义；可以显式限制到 $\Gamma'=\{\gamma:\text{除法守卫成立}\}$ 后研究，但必须公布域已改变及 $\Gamma'\ne\varnothing$ 的条件。整数还逐世界检查整除性；实数检查每个世界的非零实数类，不要求所有世界共享一个尾部下界。以 $t\in\{0,1\}$ 为例，$t/t$ 不在全域定义，限制到 $\{1\}$ 才有可能值 $\{1\}$，不能把它说成原全域的无条件结果。

## 11. ZFC 构造与兼容性的准确强度

**命题 14（全部载体为 ZFC 集合）。** 本文的有限情境、丰富整数及有理表示、全部丰富 Cauchy 序列、它们的等价商及指定运算，均可在 ZFC 中构造；每个给定的联合来源模型也是集合结构。

**证明。** ZFC 以无穷公理构造 $\omega$，以递归、幂集和并集构造 $V_n$ 与 $HF=\bigcup_{n<\omega}V_n$。用 Kuratowski 有序对及不同自然数标签编码整数、元组、事件出现和来源树。树集合可取 $T_0=\{\operatorname{leaf}(n):n\in\omega\}$，$T_{k+1}=T_k\cup\{\operatorname{pair}(r,s):r,s\in T_k\}$，再作可数并。每棵树以及每份有限函数图都是遗传有限集合。

因此一份有限情境和选择的完整编码属于 $HF$，全部合法编码由 $HF$ 上的分离公理取出；不是对任意大集合的无界收集。有限性、严格偏序、函数图、时标约束、区域包含、符号计数和平衡都是一阶集合论可表达性质，故 $\mathcal B$ 是集合。定义中的有限并、积、传递闭包、函数像与有限和给出相应运算的定义图；命题 1 至 3 已证明所需域上的唯一输出及闭包。

任一集合 $X$ 上的等价关系，其商可写为 $\{[x]:x\in X\}\subseteq\mathcal P(X)$，由分离与替代构造。因此整数商存在，$\mathcal Q^{\rm rich}\subseteq\mathcal B^2$ 及有理商也存在。全序列空间是函数集 $(\mathcal Q^{\rm rich})^{\mathbb N}\subseteq\mathcal P(\mathbb N\times\mathcal Q^{\rm rich})$；以 Cauchy 条件分离出 $\mathcal R^{\rm rich}$，再取零差商。这个函数集不要求元素仍属 $HF$，所以没有把实数限制在可数的有限编码集合中。命题 6 的求逆图只对非零类成立，有限前缀分支以有理零判别给出唯一值；它在 ZFC 中存在，不需要算法判定任意实数类是否非零。

来源模型以给定的集合 $S$ 及值域族为参数；积、子集 $\Gamma$ 和函数 $H$ 都是集合。这里 $\Gamma\ne\varnothing$ 是该模型的显式条件，不是声称任意额外联合约束必相容。有限 bin 数据、情境嵌入、地平线族也分别由相应函数集与分离得到。证毕。

**命题 15（定义性保守扩展）。** 若新词汇仅由本文的 ZFC 公式定义，而本文命题以其证明加入，则对任一原集合论语言句子 $\varphi$，

$$
\mathrm{ZFC}+\mathrm{CSA\ definitions}\vdash\varphi
\quad\Longrightarrow\quad \mathrm{ZFC}\vdash\varphi.
$$

因而在通常元理论中有相对一致性蕴含
$\operatorname{Con}(\mathrm{ZFC})\Rightarrow\operatorname{Con}(\mathrm{ZFC}+\mathrm{CSA\ definitions})$；反向因后者包含前者也成立。这里没有从无条件前提证明任一一致性断言。

**证明。** 新谓词可逐次替换成其集合论定义；有类型的变量量化替换成相应载体上的受限量化。新函数可替换成其唯一输出的定义图；部分运算保留域谓词和图，或在域外统一返回指定的 $\varnothing$，只在合法域声明算术保持。命题 14 及各闭包、守卫证明保证这些定义图在声明域上存在唯一值，故消去定义不会增加一个未证明的存在公理。对扩展语言中的有限推导逐步消去定义，得到原语言的 ZFC 推导，证明保守性。若扩展导致矛盾，同一消去过程给出 ZFC 中矛盾，于是得到相对一致性结论。证毕。

特别地，没有断言外部已经存在一个 ZFC 的集合模型；对任一给定 $M\models\mathrm{ZFC}$ 的“可作定义扩张”只是条件陈述，并不构造这样的 $M$。也不声称 Lean 的依赖类型论基础与 ZFC 完全相同，或已有 Lean 文件内核验证了这整个新模型。

**普遍整体的障碍。** 本稿 $HF$ 中全部有限情境编码构成一个集合，但它不是一切集合的集合；$\mathcal D_C$ 的整体只属于指定情境。若设有含所有集合的集合 $U$，分离出 $R=\{x\in U:x\notin x\}$，由普遍性有 $R\in U$，从而 $R\in R\iff R\notin R$，矛盾。因此扩展到任意集合尺度的“所有情境”时，只可用可定义类的缩写，或先固定集合尺度再取商；不能直接对真类套用本文的集合商论证。整个构造不需要不可达基数，也不把“道包含一切”偷换成 ZFC 的普遍集合公理。

## 12. 来源、已有结果与 PRO 意见的处理

本文组合方案的归类是 `repo-derived`：在既有来源材料与批准方案上给出本稿的显式构造和证明。有限和、商代数、整数分数、有理 Cauchy 完备化、集合编码和定义性保守扩展是成熟数学，不主张为新发现，也不把新组合称为已经完成文献新颖性调查。

标准参考：Terence Tao, *Analysis I*（2022，整数、有理数与实数的标准构造），DOI [10.1007/978-981-19-7261-4](https://doi.org/10.1007/978-981-19-7261-4)；Thomas Jech, *Set Theory*（1997，ZFC、集合层级与通常集合构造），DOI [10.1007/978-3-662-22400-7](https://doi.org/10.1007/978-3-662-22400-7)。本次在线查询核对的是 Crossref 的作者、书名、年份和 DOI 元数据，未据元数据声称逐页核过书中证明。本文承重的具体命题与证明已写在正文。

仓库内直接相关的数学材料如下；链接为源码，声明名给出检索锚。本次读取了这些文件并核对各自冻结成员状态文件存在，未修改或重新证明它们。

| 已有源码 | 本稿采用的边界 |
| --- | --- |
| [RelativeComplement.lean](../../../D5/S3/ConceptDynamics/Negation/RelativeComplement.lean) | `relativeComplement_domain_extension` 的新增区域分解，`preimage_relativeComplement` 与 `image_complement_counterexample` 对逆像、直接像的区分 |
| [ComplementFiberLift.lean](../../../D5/S3/ConceptDynamics/Negation/ComplementFiberLift.lean) | `complementFiber` 与 `sectionLift_square` 区分反值纤维、选点提升及其平方；选代表只得到截面上的回缩 |
| [DaoConceptBoundarySpecialization.lean](../../../D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.lean) | 整体、概念与相对余域的集合表述；“所有表达都留余域”是显式前提，不是由“道”这个名称推出 |
| [InvolutionDescent.lean](../../../D5/S3/ConceptDynamics/ObservationTopology/InvolutionDescent.lean) | `kernelStable_iff_exists_descended` 的纤维稳定下降准则；本稿另写部分域必须饱和的扩充 |
| [ConceptFiberDecomposition.lean](../../../D5/S3/ConceptDynamics/ConceptFiberDecomposition.lean) | `concept_fiber_decomposition` 的读数加依赖纤维表述，不能把纤维中的点从数值自动重建 |

实际 GPT PRO 输入由调用方保留为 `/tmp/dao-spacetime-0909/pro-result.json` 的 `conclusion`；运输证据为 `/tmp/dao-spacetime-0909/pro-attempt-2-transport.json`。本次读取的字段为：`task_id=d42635b1-0943-40dd-8ca7-64654af999b0`，`model=chatgpt-5.5-pro`，`status=completed`，`completed_at=2026-09-08T16:50:07.221+00:00`，`conversation_id=conv_9b0c2d6553535653`，对话 [GPT PRO 建设输入](https://chatgpt.com/c/6aa03bfa-9294-83ec-ad89-bb2c9c0a2cd9)。这些标识证明所消费的输入来自保存的实际调用记录，不使其数学判断成为权威；临时路径的长期保存归调用方负责。调用方记录首次响应已有实质内容但 JSON 转义无效，未将其计作有效面板信封；本稿消费的是重试后的有效结果，未重新归因首次失败。实施载体与 PRO 都是 OpenAI 来源，不以两个载体冒充两个独立模型族。未打开或使用任何 `log_ref` 内容推理。

本稿保留 PRO 提出的有限有符号事件、商算术、局部平衡、共同赋值、相对 ZFC 解释及反例方向，并依批准综合方案作如下具体收紧：

| PRO 输入中的问题或较弱形态 | 本稿落点 |
| --- | --- |
| `Dao(C)=Adm` 与事件补集可能混层 | 定义 2 明确为 $(C,\Omega,\mathcal P(\Omega))$；历史族和世界域另外标型 |
| 单纯 Cartesian 事件乘法遇空因子丢掉输入事件 | 定义 6 保留两份档案再生成当前事件；命题 3 给出嵌入与基数证明 |
| 时间先后可通过平移实现，但易变成暗改绝对时间 | 定义 5 是部分运算，任何平移显式写在输入上 |
| 原始逆元不存在，被笼统写成 noncancellative | 第 4 节撤去该推断，并证明标签编码相等下的加法消去律 |
| 实数求逆早期项可能为零 | 命题 6 定义每个前缀项，证明非零类等价于尾部正下界，并给两个相反方向的守卫测试 |
| 不共享变量名容易被误当成无额外联合约束 | 第 10 节保留 $\Gamma=J\cap K$，不由变量名推出域积或概率独立 |
| 粗化可能丢符号和多重性 | 定义 12 使用双电荷 $w,z$，补集为 $w-z$；命题 10 单独处理直接像的饱和条件 |

这些是对本稿数学范围的实质修正，不把一次思考席响应或实施席自查称为最终独立审查通过。

## 13. 已反驳的更强断言与剩余研究范围

| 更强断言 | 反例或精确替代 |
| --- | --- |
| 任意背景下补集等于算术负号 | $u\ne0$ 时是 $u-q$；取空选择即可检出差异 |
| 因果过去对任意补集封闭 | 两事件链的 $\{e\}$ 与 $\{f\}$ |
| 非空表示加其负表示就是空历史 | 档案基数变为 $2\lvert E_X\rvert>0$ |
| 数值一在原始档案乘法下是单位 | 新档案至少增加两个旧事件；第 4 节基数式 |
| 原始乘法关联顺序不影响历史 | 同读数 $2$ 的两种括号分别有 $28,32$ 个事件 |
| 完整结构都能由一个旧标量更新 | 第 9 节三个同数异筛选反例；须满足命题 11 |
| 限制任一配对仍普遍投影为乘法 | 单点选择命中被删对，$\pm1$ 变成 $0$ |
| 平衡扩张保持补集集合不变 | 新增正负对电荷为零，但新增区域非空 |
| 总体平衡意味着每个 bin 的负号 | $w=(1,-1),z=(1,0)$，补集为 $(0,-1)$ |
| 满射总保直接像补集 | 一个纤维部分被选，像的两部分发生重叠 |
| 任意事件合并保持因果无环 | 两条链合并成 $L\prec R\prec L$ |
| 两输入共同空间平移与乘法交换 | 新点偏移 $2v$ 与 $v$ 不同 |
| 来源边缘集合足以算不确定结果 | 共享 $t-t$ 与 $t^2$ 的像不同于独立配对 |
| 实数逐项非零等价于可求逆 | 零前缀的常一类可逆，$1/n$ 类不可逆 |
| 无限平衡整体有无条件的 $\infty-\infty=0$ | 正负交替的有限部分和不收敛 |
| ZFC 解释证明 ZFC 绝对一致或给出普遍集合 | 定义消去只给相对结论；普遍集合被 Russell 分离反例否定 |

已证明的范围是：有限档案丰富层上的指定整数算术投影、带守卫的分数与全部 Cauchy 序列扩充、结构操作和运输的精确适用条件，以及 ZFC 内的定义解释。上述失败断言已由反例解决，不作为含混的“开放问题”保留。剩余可研究方向是对特定应用另外定义并验证允许历史、因果动力学、连续时空结构或概率模型；这些都不属于本稿已完成的算术兼容性证明。把本稿新模型进一步形式化是另一个工作单元，本次没有完成内核验证或最终独立评审。

## 附录 A. 精确有限核验

以下 Python 3 标准库检查器是本任务的临时核验，不是生产算术引擎。它只用整数、集合与 `fractions.Fraction`，有限遍历的范围是档案即当前区域、空偏序、事件数为 $0,2,4$ 的全部平衡符号配置及全部选择，共 105 个表示、11025 个输入对。另核验正文的非空因果偏序例子、档案保留、原始非结合性、分数、补集粗观察、空间运输、来源与除法反例。普遍命题及全部无限序列的结论由正文证明，不由这些有限运行替代。

在仓根直接执行文档中的唯一 Python 代码块，无需生成工具文件：

```sh
sed -n '/^```python$/,/^```$/p' docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md | sed '1d;$d' | python3 -
```

检查器使用 Python 元组和字典作为有限编码的可读实现；正文的集合编码论证不依赖 Python 对象身份。

```python
from dataclasses import dataclass, replace
from fractions import Fraction
from itertools import product

@dataclass(frozen=True)
class Rich:
    e: dict
    o: frozenset
    w: frozenset
    a: frozenset

def closure(edges):
    out = set(edges)
    while True:
        more = {(a, d) for a, b in out for c, d in out if b == c}
        if more <= out:
            return frozenset(out)
        out |= more

def valid(x):
    assert x.a <= x.w <= x.e.keys()
    assert all(t == int(t) and len(p) == 3 and s in (-1, 1)
               for t, p, s, r in x.e.values())
    assert all(a in x.e and b in x.e and x.e[a][0] < x.e[b][0]
               for a, b in x.o)
    assert closure(x.o) == x.o
    return x

def charge(x, a):
    return sum(x.e[e][2] for e in a)

def q(x):
    return charge(x, x.a)

def neg(x):
    return replace(x, a=x.w - x.a)

def add(x, y):
    e = {(i, a): v for i, z in enumerate((x, y))
         for a, v in z.e.items()}
    o = frozenset(((i, a), (i, b)) for i, z in enumerate((x, y))
                  for a, b in z.o)
    w = frozenset((i, a) for i, z in enumerate((x, y)) for a in z.w)
    a = frozenset((i, a) for i, z in enumerate((x, y)) for a in z.a)
    return valid(Rich(e, o, w, a))

def temporal(x, y):
    if not all(x.e[a][0] < y.e[b][0] for a in x.e for b in y.e):
        raise ValueError("time guard")
    z = add(x, y)
    cross = {((0, a), (1, b)) for a in x.e for b in y.e}
    return valid(replace(z, o=closure(z.o | cross)))

def mul(x, y):
    z = add(x, y)
    e, o, w, chosen = dict(z.e), set(z.o), set(), set()
    for a in x.w:
        for b in y.w:
            key = (2, (a, b))
            ta, pa, sa, ra = x.e[a]
            tb, pb, sb, rb = y.e[b]
            e[key] = (max(ta, tb) + 1, tuple(u + v for u, v in zip(pa, pb)),
                      sa * sb, ("pair", ra, rb))
            o |= {((0, a), key), ((1, b), key)}
            w.add(key)
            if a in x.a and b in y.a:
                chosen.add(key)
    return valid(Rich(e, closure(o), frozenset(w), frozenset(chosen)))

def integer(n):
    e = {(i, s): (0, (0, 0, 0), s, ("leaf", i))
         for i in range(abs(n)) for s in (-1, 1)}
    a = frozenset(k for k in e if k[1] == (1 if n > 0 else -1))
    return valid(Rich(e, frozenset(), frozenset(e), a))

def time_shift(x, k):
    return valid(replace(x, e={a: (t + k, p, s, r)
                               for a, (t, p, s, r) in x.e.items()}))

def spatial(x, scale=1, offset=0):
    return valid(replace(x, e={a: (t, (scale*p[0] + offset,
                                       scale*p[1], scale*p[2]), s, r)
                               for a, (t, p, s, r) in x.e.items()}))

def filt(x, pred):
    return replace(x, a=frozenset(a for a in x.a if pred(a)))

def coarse(x, f):
    bins = {f(a) for a in x.w}
    w = {b: charge(x, {a for a in x.w if f(a) == b}) for b in bins}
    z = {b: charge(x, {a for a in x.a if f(a) == b}) for b in bins}
    return w, z

def rv(r):
    return Fraction(q(r[0]), q(r[1]))

def rat(a, b=1):
    if b == 0:
        raise ValueError("denominator guard")
    return integer(a), integer(b)

def radd(r, s):
    x, y = r
    z, w = s
    return add(mul(x, w), mul(z, y)), mul(y, w)

def rmul(r, s):
    return mul(r[0], s[0]), mul(r[1], s[1])

def rneg(r):
    return neg(r[0]), r[1]

def rdiv(r, s):
    if q(s[0]) == 0:
        raise ValueError("divisor guard")
    return mul(r[0], s[1]), mul(r[1], s[0])

def inverse_term(r):
    return (r[1], r[0]) if rv(r) != 0 else radd(r, rneg(r))

states = []
for n in (0, 2, 4):
    for signs in product((-1, 1), repeat=n):
        if sum(signs) != 0:
            continue
        e = {i: (i, (i, 0, 0), signs[i], ("leaf", i)) for i in range(n)}
        for bits in product((False, True), repeat=n):
            x = valid(Rich(e, frozenset(), frozenset(e),
                           frozenset(i for i in e if bits[i])))
            assert q(neg(x)) == -q(x) and neg(neg(x)) == x
            states.append(x)
pairs = 0
for x in states:
    for y in states:
        a, p = add(x, y), mul(x, y)
        assert q(a) == q(x) + q(y) and q(p) == q(x) * q(y)
        assert charge(a, a.w) == charge(p, p.w) == 0
        assert len(p.e) == len(x.e) + len(y.e) + len(x.w)*len(y.w)
        for i, old in enumerate((x, y)):
            assert all(p.e[(i, k)] == v for k, v in old.e.items())
            assert all((((i, a), (i, b)) in p.o) == ((a, b) in old.o)
                       for a in old.e for b in old.e)
        pairs += 1
assert (len(states), pairs) == (105, 11025)
print("balanced_states=105 pair_checks=11025")

xe = {"a": (0, (0,0,0), 1, ("leaf",7)),
      "b": (1, (2,0,0), 1, ("leaf",7)),
      "c": (1, (1,0,0), -1, ("leaf",8)),
      "d": (2, (3,0,0), -1, ("leaf",8))}
ye = {"r": (3, (10,0,0), 1, ("leaf",7)),
      "s": (4, (10,0,0), -1, ("leaf",9))}
x = valid(Rich(xe, frozenset({("a","b"), ("c","d")}),
               frozenset(xe), frozenset("abc")))
y = valid(Rich(ye, frozenset({("r","s")}), frozenset(ye), frozenset("r")))
p, a, t = mul(x, y), add(x, y), temporal(x, y)
assert (q(x), q(y), q(p), len(p.e), len(p.w), len(p.a), len(p.o)) == (1,1,1,14,8,3,27)
assert [(p.e[(2,(k,"r"))][0], p.e[(2,(k,"r"))][1][0],
         p.e[(2,(k,"r"))][2]) for k in "abc"] == [(4,10,1),(4,12,1),(4,11,-1)]
assert (len(a.o), len(t.o), q(a), q(t)) == (3,11,2,2)
print("worked_product: q=1 archive=14 whole=8 selected=3 causal_pairs=27")
print("parallel_pairs=3 temporal_pairs=11 both_q=2")
z0, z1 = mul(x, integer(0)), mul(x, replace(y, a=y.w))
assert (len(z0.e), len(z0.w), q(z0)) == (4,0,0)
assert (len(z1.e), len(z1.w), len(z1.a), q(z1)) == (14,8,6,0)
assert mul(x, integer(0)) == mul(neg(x), integer(0))
u, two = integer(1), integer(2)
left, right = mul(mul(u,u),two), mul(u,mul(u,two))
assert (len(left.e), len(right.e), q(left), q(right)) == (28,32,2,2)
assert len(add(u,neg(u)).e) == 4 and q(add(u,neg(u))) == 0
assert len(mul(u,u).e) == 8 and q(mul(u,u)) == 1
print("zero_products: (archive,whole,selected,q)=(4,0,0,0),(14,8,6,0)")
print("raw_laws: sum_with_negative_archive=4 unit_product_archive=8 associativity_archives=28,32")

xp = replace(x, a=frozenset("a"))
predicates = (lambda k: x.e[k][1][0] >= 2,
              lambda k: x.e[k][3] == ("leaf",7),
              lambda k: k == "b" or (k,"b") in x.o)
observed = [(q(filt(x,f)), q(filt(xp,f))) for f in predicates]
assert q(x) == q(xp) == 1 and observed == [(1,0),(2,1),(2,1)]
restricted = replace(p, a=frozenset(k for k in p.a
                     if abs(x.e[k[1][0]][1][0] - y.e[k[1][1]][1][0]) <= 9))
omitted = charge(p, p.a - restricted.a)
assert (q(restricted), omitted, q(p)) == (0,1,1)
single = mul(replace(x,a=frozenset("a")), y)
assert q(single) == 1 and q(replace(single,a=frozenset())) == 0
print("filters: spatial=(1,0) source=(2,1) causal=(2,1); restricted_q=0 omitted_charge=1")

expanded = replace(two, a=u.a)
extra = two.w - u.w
assert extra and charge(two,extra) == 0 and q(neg(expanded)) == q(neg(u)) == -1
unbalanced = valid(Rich({k:v for k,v in two.e.items() if k in u.w or k == (1,1)},
                        frozenset(), u.w | {(1,1)}, u.a))
assert q(neg(unbalanced)) == 0 and charge(unbalanced,unbalanced.w) == 1
w,z = coarse(u, lambda k: k[1])
wn,zn = coarse(neg(u), lambda k: k[1])
assert w == wn == {-1:-1,1:1} and z == {-1:0,1:1} and zn == {-1:-1,1:0}
assert all(zn[b] == w[b] - z[b] for b in w)
f = {"a":0,"b":0,"c":1}
assert {f[k] for k in {"b","c"}} == {0,1}
assert {0,1} - {f["a"]} == {1}
assert {("L","L"),("R","R")} <= closure({("L","R"),("R","L")})
print("transport: balanced_added_charge=0 unbalanced_defect=1; bin_complement=(0,-1); image_defect_and_cycle=confirmed")
assert mul(spatial(x,2),spatial(y,2)) == spatial(p,2)
assert mul(time_shift(x,5),time_shift(y,5)) == time_shift(p,5)
assert mul(spatial(x,offset=1),spatial(y,offset=1)) != spatial(p,offset=1)
try:
    temporal(u,u)
    raise AssertionError("unguarded temporal composition")
except ValueError:
    pass
assert q(temporal(u,time_shift(u,1))) == 2
print("coordinates: linear_and_time_translation_commute=True spatial_translation_commutes=False")

r,s = rat(1,2),rat(-3,2)
assert (rv(radd(r,s)),rv(rmul(r,s)),rv(rneg(r)),rv(rdiv(r,s))) == (
    Fraction(-1),Fraction(-3,4),Fraction(-1,2),Fraction(-1,3))
try:
    rdiv(r,rat(0))
    raise AssertionError("unguarded rational division")
except ValueError:
    pass
prefix = [rv(inverse_term(rat(k))) for k in (0,1,1,1)]
null_inverse_prefix = [rv(inverse_term(rat(1,k))) for k in (1,2,3,4)]
assert prefix == [0,1,1,1] and null_inverse_prefix == [1,2,3,4]
print("rationals: sum=-1 product=-3/4 negative=-1/2 division=-1/3 zero_divisor=rejected")
print("inverse_prefixes: (0,1,1,1)->(0,1,1,1); (1,1/2,1/3,1/4)->(1,2,3,4)")

shared = ({t-t for t in (1,2)}, {t*t for t in (1,2)})
independent = ({t-s for t in (1,2) for s in (1,2)},
               {t*s for t in (1,2) for s in (1,2)})
assert shared == ({0},{1,4}) and independent == ({-1,0,1},{1,2,4})
assert {(s,t) for s in (1,2) for t in (1,2) if s == t} == {(1,1),(2,2)}
assert {t for t in (0,1) if t != 0} == {1}
chain = {("e","f")}
assert all(b not in {"e"} or a in {"e"} for a,b in chain)
assert not all(b not in {"f"} or a in {"f"} for a,b in chain)
print("sources: shared_difference={0} shared_square={1,4}; independent_difference={-1,0,1} independent_product={1,2,4}")

# PR1: verification helpers only; Rich/add/mul/neg above remain the archive model.
# Rich.w is Omega (an event set), whereas the first read_pair component is w(p).
def sparse(c):
    return {p: a for p, a in c.items() if a}

def read_pair(x):
    return tuple(sparse(c) for c in coarse(x, lambda k: x.e[k][1]))

def plus_c(c, d):
    return sparse({p: c.get(p, 0) + d.get(p, 0) for p in c.keys() | d.keys()})

def minus_c(c):
    return {p: -a for p, a in c.items()}

def conv(c, d, keep=lambda p, q: True):
    out = {}
    for p, a in c.items():
        for q0, b in d.items():
            if keep(p, q0):
                r = tuple(i + j for i, j in zip(p, q0))
                out[r] = out.get(r, 0) + a*b
    return sparse(out)

def pair_add(x, y):
    return tuple(plus_c(c, d) for c, d in zip(x, y))

def pair_mul(x, y):
    return tuple(conv(c, d) for c, d in zip(x, y))

def flip_signs(x):
    return valid(replace(x, e={k: (t, p, -s, r)
                               for k, (t, p, s, r) in x.e.items()}))

def at(x, points):
    return filt(x, lambda k: x.e[k][1] in points)

def realize(w, z):
    assert sum(w.values()) == 0
    events, chosen = {}, set()
    for p in sorted(w.keys() | z.keys()):
        for selected, value in ((True, z.get(p, 0)),
                                (False, w.get(p, 0) - z.get(p, 0))):
            for i in range(abs(value)):
                k = (p, selected, i)
                events[k] = (0, p, 1 if value > 0 else -1, ("leaf", 0))
                if selected:
                    chosen.add(k)
    return valid(Rich(events, frozenset(), frozenset(events), frozenset(chosen)))

def restricted_mul(x, y, keep):
    full = mul(x, y)
    return replace(full, a=frozenset(k for k in full.a if keep(*k[1])))

origin, v, h = (0,0,0), (1,0,0), (0,1,-1)
delta = {origin: 1}
alpha = {origin: 1, v: -1}
recovery_checks = 0
for state in states:
    bg, selected = read_pair(state)
    for point in ((i,0,0) for i in range(4)):
        z_at = q(at(state, {point}))
        n_at = q(at(neg(state), {point}))
        assert z_at == selected.get(point, 0)
        assert z_at + n_at == bg.get(point, 0)
        assert read_pair(at(state, {point}))[0] == bg
        recovery_checks += 1
assert recovery_checks == 420
background_only = realize(alpha, {})
assert read_pair(background_only) == (alpha, {})
assert q(at(neg(background_only), {origin})) == 1
assert q(at(neg(integer(0)), {origin})) == 0
assert read_pair(at(background_only, set()))[0] == alpha
assert read_pair(neg(background_only)) == (alpha, alpha)
assert read_pair(flip_signs(background_only)) == (minus_c(alpha), {})
shifted_u = spatial(u, offset=1)
assert q(u) == q(shifted_u) == 1
assert (q(at(u, {origin})), q(at(shifted_u, {origin}))) == (1, 0)
print("pr1_recovery: singleton_checks=420 background_after_filter=preserved kernels_strict=True")

image_cases = 0
for a0, a1 in product((-1,0,1), repeat=2):
    bg = sparse(dict(zip((origin,v,h), (a0,a1,-a0-a1))))
    for zs in product((-1,0,1), repeat=3):
        selected = sparse(dict(zip((origin,v,h), zs)))
        state = realize(bg, selected)
        assert read_pair(state) == (bg, selected)
        bound = sum(abs(selected.get(p,0)) + abs(bg.get(p,0)-selected.get(p,0))
                    for p in bg.keys() | selected.keys())
        assert len(state.w) == len(state.e) == bound
        assert charge(state, state.w) == 0 and not state.o
        assert all(event[0] == 0 for event in state.e.values())
        image_cases += 1
assert image_cases == 243

capacity_cases, selection_cases = 0, 0
for pp0, pm0, pp1, pm1 in product(range(3), repeat=4):
    if pp0 + pp1 != pm0 + pm1:
        continue
    counts = {origin: (pp0,pm0), v: (pp1,pm1)}
    events = {(p,s,i): (0,p,s,("leaf",0)) for p, ns in counts.items()
              for s,n in zip((1,-1),ns) for i in range(n)}
    fixed = valid(Rich(events, frozenset(), frozenset(events), frozenset()))
    seen = set()
    for bits in product((False,True), repeat=len(events)):
        chosen = frozenset(k for k,yes in zip(events,bits) if yes)
        bg, selected = read_pair(replace(fixed, a=chosen))
        assert bg == sparse({origin:pp0-pm0, v:pp1-pm1})
        seen.add(tuple(selected.get(p,0) for p in (origin,v)))
        selection_cases += 1
    expected = set(product(range(-pm0,pp0+1), range(-pm1,pp1+1)))
    assert seen == expected
    capacity_cases += 1
assert (capacity_cases, selection_cases) == (19,673)
empty_u, empty_two = replace(u,a=frozenset()), replace(two,a=frozenset())
assert read_pair(empty_u) == read_pair(empty_two) == ({},{})
capacities = []
for fixed in (empty_u, empty_two):
    capacities.append({q(replace(fixed,a=frozenset(k for k,b in zip(fixed.w,bits) if b)))
                       for bits in product((False,True),repeat=len(fixed.w))})
assert capacities == [{-1,0,1},{-2,-1,0,1,2}]
print("pr1_image_capacity: image_cases=243 fixed_contexts=19 choices=673 capacities=[-1,1],[-2,2]")

# Explicit coefficients come from the delta expansions in section 17.3.
sx = realize(alpha, {origin:2, v:-1})
sy = realize({h:1, origin:-1}, {v:1, h:1})
vh, vv = (1,1,-1), (2,0,0)
expected_bg = {h:1, origin:-1, vh:-1, v:1}
expected_z = {v:2, h:2, vv:-1, vh:-1}
full = mul(sx, sy)
assert read_pair(full) == (expected_bg, expected_z)
assert (len(full.e), len(full.w), q(full)) == (24,16,2)
assert read_pair(neg(sx)) == (alpha, {origin:-1})
kept = restricted_mul(sx, sy, lambda a,b: sx.e[a][1] == sy.e[b][1])
assert read_pair(kept) == (expected_bg, {vv:-1})
assert q(kept) == -1 and q(full) == 2
assert conv(read_pair(sx)[1], read_pair(sy)[1], lambda p,q0:p == q0) == {vv:-1}
assert q(restricted_mul(u, shifted_u, lambda a,b:u.e[a][1] == shifted_u.e[b][1])) == 0
assert q(restricted_mul(u, u, lambda a,b:u.e[a][1] == u.e[b][1])) == 1

space_states = [realize(sparse({origin:c, v:-c}), z0)
                for c in (-1,0,1) for z0 in ({h:-1},{},{v:1,h:1})]
space_pairs = 0
for xx in space_states:
    bx,zx = read_pair(xx)
    assert read_pair(neg(xx)) == (bx,plus_c(bx,minus_c(zx)))
    assert read_pair(add(xx,flip_signs(xx))) == ({},{})
    for yy in space_states:
        px,py = read_pair(xx),read_pair(yy)
        assert read_pair(add(xx,yy)) == pair_add(px,py)
        assert read_pair(mul(xx,yy)) == pair_mul(px,py)
        assert sum(conv(px[0],py[0]).values()) == 0
        assert sum(conv(px[1],py[1]).values()) == q(xx)*q(yy)
        assert pair_mul(px,py) == pair_mul(py,px)
        space_pairs += 1
space_triples = 0
pair_samples = [read_pair(xx) for xx in space_states]
for px,py,pz in product(pair_samples, repeat=3):
    assert pair_mul(pair_mul(px,py),pz) == pair_mul(px,pair_mul(py,pz))
    assert pair_mul(px,pair_add(py,pz)) == pair_add(pair_mul(px,py),pair_mul(px,pz))
    space_triples += 1
assert (space_pairs,space_triples) == (81,729)
assert read_pair(left) == read_pair(right) == ({},{origin:2})
assert (len(left.e),len(right.e)) == (28,32)
print("pr1_convolution: sparse_states=9 rich_pairs=81 pair_triples=729 explicit_full_q=2 restricted_q=-1 archives=28,32")

FAIL = object()
def observe(ops, state, read):
    try:
        for operation in ops:
            state = operation(state)
    except (KeyError, ValueError):
        return FAIL
    return ("ok", read(state))

only_a = {"a":"a"}.__getitem__
rd0 = lambda _: 0
common_words = [(),(only_a,),(only_a,only_a)]
for word in common_words:
    oa,ob = observe(word,"a",rd0),observe(word,"b",rd0)
    assert oa is FAIL or ob is FAIL or oa == ob  # The wrong rule misses the defect.
assert observe((only_a,),"a",rd0) == ("ok",0)
assert observe((only_a,),"b",rd0) is FAIL
assert observe((only_a,),"b",rd0) != ("ok",0)
depth_cases = 0
for depth in range(5):
    advance = lambda x, k=depth: (x[0],min(x[1]+1,k+1))
    read = lambda x, k=depth: int(x == ("a",k+1))
    for j in range(depth+1):
        assert observe((advance,)*j,("a",0),read) == observe((advance,)*j,("b",0),read)
    assert (observe((advance,)*(depth+1),("a",0),read),
            observe((advance,)*(depth+1),("b",0),read)) == (("ok",1),("ok",0))
    assert observe((advance,)*depth,advance(("a",0)),read) != observe((advance,)*depth,advance(("b",0)),read)
    depth_cases += 1
f = lambda s,t: 2 if (s,t) == (1,2) else 0
read012 = lambda x: int(x == 2)
second_only = [lambda x,a=a:f(a,x) for a in (0,1,2)]
params01 = [lambda x,a=a:f(a,x) for a in (0,1)] + [lambda x,a=a:f(x,a) for a in (0,1)]
restricted_words = 0
for family in (second_only,params01):
    for depth in range(4):
        for word in product(family,repeat=depth):
            assert observe(word,0,read012) == observe(word,1,read012)
            restricted_words += 1
assert observe((lambda x:f(x,2),),0,read012) == ("ok",0)
assert observe((lambda x:f(x,2),),1,read012) == ("ok",1)
g = lambda x: 0 if x == 0 else 2
assert observe((),0,read012) == observe((),1,read012)
assert observe((g,),0,read012) != observe((g,),1,read012)
assert (depth_cases,restricted_words) == (5,125)
print("pr1_contexts: common_domain_miss=1 depth_counterexamples=5 restricted_word_checks=125 slot_parameter_and_extra_probe=distinguished")

source7 = valid(Rich({"a":(0,origin,1,("leaf",7)), "b":(0,origin,-1,("leaf",7))},
                    frozenset(),frozenset(("a","b")),frozenset(("a",))))
source8 = replace(source7,e={k:(t,p,s,("leaf",8)) for k,(t,p,s,r) in source7.e.items()})
assert read_pair(source7) == read_pair(source8) == ({},delta)
source_reads = tuple(q(filt(xx,lambda k,xx=xx:xx.e[k][3] == ("leaf",7)))
                     for xx in (source7,source8))
assert source_reads == (1,0)
source_products = tuple(q(restricted_mul(xx,source7,
                        lambda a,b,xx=xx:xx.e[a][3] == source7.e[b][3]))
                        for xx in (source7,source8))
assert source_products == (1,0)
ce = {k:(t,origin,s,("leaf",0)) for k,t,s in zip("abcd",(0,1,0,1),(1,1,-1,-1))}
causal = valid(Rich(ce,frozenset({("a","b")}),frozenset(ce),frozenset("ab")))
no_causal = valid(replace(causal,o=frozenset()))
def past(x, targets):
    if not targets <= x.e.keys():
        raise ValueError("dependent causal query domain")
    return filt(x,lambda e:any(e == d or (e,d) in x.o for d in targets))
assert read_pair(causal) == read_pair(no_causal) == ({},{origin:2})
assert (q(past(causal,{"b"})),q(past(no_causal,{"b"}))) == (2,1)
assert tuple(q(restricted_mul(xx,u,lambda a,b,xx=xx:a in past(xx,{"b"}).a))
             for xx in (causal,no_causal)) == (2,1)
old = valid(replace(u,e={**u.e,("old",0):(2,origin,1,("leaf",9))}))
assert read_pair(old) == read_pair(u) == ({},delta)
after = time_shift(u,1)
assert observe((lambda xx:temporal(xx,after),),u,q) == ("ok",2)
assert observe((lambda xx:temporal(xx,after),),old,q) is FAIL
renamed = valid(Rich({"a2":source7.e["a"],"b2":source7.e["b"]},frozenset(),
                    frozenset(("a2","b2")),frozenset(("a2",))))
assert read_pair(renamed) == read_pair(source7)
assert (q(filt(source7,lambda k:k == "a")),q(filt(renamed,lambda k:k == "a"))) == (1,0)
assert tuple(q(restricted_mul(xx,u,lambda a,b:a == "a")) for xx in (source7,renamed)) == (1,0)
assert observe((lambda xx:past(xx,{"a"}),),source7,q) == ("ok",1)
assert observe((lambda xx:past(xx,{"a"}),),renamed,q) is FAIL
print("pr1_boundaries: same_pair_source=1,0 causal=2,1 time_domain=defined,undefined identity=1,0 dependent_D=defined,undefined")

a0 = read_pair(background_only)
e0 = read_pair(u)
zero_pair = ({},{})
assert a0 != zero_pair and e0 != zero_pair
assert read_pair(mul(background_only,u)) == zero_pair
assert read_pair(mul(u,source7)) == read_pair(source7)
assert read_pair(neg(mul(u,u))) == ({},{origin:-1})
assert read_pair(mul(neg(u),neg(u))) == e0
assert read_pair(neg(u)) == read_pair(flip_signs(u))
for xx in space_states:
    bg,_ = read_pair(xx)
    assert (read_pair(neg(xx)) == read_pair(flip_signs(xx))) == (bg == {})
unit_candidates = 0
for coeffs in product(range(-2,3),repeat=3):
    if sum(coeffs) != 0:
        continue
    candidate_a = sparse(dict(zip((origin,v,h),coeffs)))
    # This detects finite examples of c(r-v) != c(r); the unbounded proof is prose.
    c = plus_c(candidate_a,{origin:-1})
    assert conv(c,{v:1,origin:-1}) != {}
    for b_coeffs in product((-1,0,1),repeat=3):
        candidate_b = sparse(dict(zip((origin,v,h),b_coeffs)))
        candidate = (candidate_a,candidate_b)
        if candidate_b != delta:
            assert pair_mul(candidate,e0) != e0
        else:
            assert pair_mul(candidate,a0) != a0
        unit_candidates += 1
assert unit_candidates == 513
print("pr1_rng: zero_divisors=confirmed N_not_J=confirmed N_not_multiplicative=confirmed P0_unit_only=True finite_unit_candidates_rejected=513")

# PR2: all finite data still use Rich and the original archive operations.
def history_map(x, y, mapping):
    assert set(mapping) == set(x.e) and set(mapping.values()) == set(y.e)
    assert len(set(mapping.values())) == len(mapping)
    assert all(x.e[e] == y.e[mapping[e]] for e in x.e)
    assert {(mapping[a],mapping[b]) for a,b in x.o} == set(y.o)
    assert {mapping[e] for e in x.w} == set(y.w)
    assert {mapping[e] for e in x.a} == set(y.a)
    return 1

def rebracket(x, y, z):
    return {**{(0,(0,e)):(0,e) for e in x.e},
            **{(0,(1,e)):(1,(0,e)) for e in y.e},
            **{(1,e):(1,(1,e)) for e in z.e}}

def unit_at(t):
    return time_shift(integer(1), t)

def guard(x, y):
    return all(x.e[e][0] < y.e[f][0] for e in x.e for f in y.e)

def attempt(operation):
    try:
        return operation()
    except ValueError:
        return FAIL

hist_left, hist_right = mul(u,add(u,u)), add(mul(u,u),mul(u,u))
assert (len(hist_left.e),len(hist_right.e),q(hist_left),q(hist_right)) == (14,16,2,2)
comm_left, comm_right = mul(source7,source8), mul(source8,source7)
new_sources = [{z.e[e][3] for e in z.e if z.e[e][0] == 1}
               for z in (comm_left,comm_right)]
assert new_sources == [{("pair",("leaf",7),("leaf",8))},
                       {("pair",("leaf",8),("leaf",7))}]
assert new_sources[0].isdisjoint(new_sources[1])
assert len(comm_left.w) == len(comm_right.w) == 4
empty = integer(0)
additive_isomorphisms = history_map(add(source7,source8),add(source8,source7),
                                  {(i,e):(1-i,e) for i,z in enumerate((source7,source8)) for e in z.e})
additive_isomorphisms += history_map(add(u,empty),u,{(0,e):e for e in u.e})
assert add(u,empty) != u and add(add(u,u),u) != add(u,add(u,u))
additive_isomorphisms += history_map(add(add(u,u),u),add(u,add(u,u)),rebracket(u,u,u))
assert q(add(u,neg(u))) == 0 and len(add(u,neg(u)).e) == 4
print(f"pr2_history: distributivity_archives={len(hist_left.e)},{len(hist_right.e)} ordered_source_new_events={len(comm_left.w)},{len(comm_right.w)} additive_isomorphisms={additive_isomorphisms}")

temporal_states = [empty] + [unit_at(t0) for t0 in (-1,0,1,2)]
current_empty = valid(replace(unit_at(4),w=frozenset(),a=frozenset()))
temporal_states.append(current_empty)
temporal_checks, temporal_defined = 0, 0
for xx,yy,zz in product(temporal_states,repeat=3):
    required = guard(xx,yy) and guard(xx,zz) and guard(yy,zz)
    tl = attempt(lambda: temporal(temporal(xx,yy),zz))
    tr = attempt(lambda: temporal(xx,temporal(yy,zz)))
    assert (tl is not FAIL) == (tr is not FAIL) == required
    if required:
        history_map(tl,tr,rebracket(xx,yy,zz))
        temporal_defined += 1
    temporal_checks += 1
assert guard(unit_at(2),empty) and guard(empty,unit_at(1))
assert not guard(unit_at(2),unit_at(1))
assert attempt(lambda:temporal(temporal(unit_at(2),empty),unit_at(1))) is FAIL
assert attempt(lambda:temporal(unit_at(2),temporal(empty,unit_at(1)))) is FAIL
legal = temporal(temporal(unit_at(0),unit_at(1)),unit_at(2))
assert (len(legal.e),len(legal.o)) == (6,12)
assert attempt(lambda:temporal(temporal(u,empty),unit_at(1))) is not FAIL
assert temporal_checks == 216
print(f"pr2_temporal: triples={temporal_checks} defined={temporal_defined} legal_archive={len(legal.e)} legal_edges={len(legal.o)} empty_middle_adjacent_guards_insufficient=True")

# None denotes +infinity in m and -infinity in M/s; no finite float times.
def theta(x):
    return (read_pair(x), min((v[0] for v in x.e.values()),default=None),
            max((v[0] for v in x.e.values()),default=None),
            max((x.e[e][0] for e in x.w),default=None))

def lo(*values):
    return min((v for v in values if v is not None),default=None)

def hi(*values):
    return max((v for v in values if v is not None),default=None)

def gamma(s, t):
    return None if s is None or t is None else max(s,t)+1

def theta_add(x, y):
    return pair_add(x[0],y[0]),lo(x[1],y[1]),hi(x[2],y[2]),hi(x[3],y[3])

def theta_mul(x, y):
    g0 = gamma(x[3],y[3])
    return pair_mul(x[0],y[0]),lo(x[1],y[1]),hi(x[2],y[2],g0),g0

def theta_guard(x, y):
    return x[2] is None or y[1] is None or x[2] < y[1]

def ceiling_state(s, selected_time=None, floor=0, ceiling=10):
    selected_time = s if selected_time is None else selected_time
    e = {"pos":(selected_time,origin,1,("leaf",0)),
         "neg":(s,origin,-1,("leaf",0)),
         "old_min":(floor,origin,1,("leaf",9)),
         "old_max":(ceiling,origin,1,("leaf",9))}
    return valid(Rich(e,frozenset(),frozenset(("pos","neg")),frozenset(("pos",))))

c0,c9 = ceiling_state(0),ceiling_state(9)
selected_low = ceiling_state(9,selected_time=0)
assert theta(c0) == (({},delta),0,10,0)
assert theta(c9) == (({},delta),0,10,9)
assert max(selected_low.e[e][0] for e in selected_low.a) == 0
assert theta(selected_low)[3] == 9
theta_states = [empty,unit_at(-1),u,unit_at(1),current_empty,c0,c9,selected_low]
theta_pairs,theta_unary,threshold_checks = 0,0,0
for xx in theta_states:
    tx = theta(xx)
    bg,zx = tx[0]
    assert theta(neg(xx)) == ((bg,plus_c(bg,minus_c(zx))),*tx[1:])
    theta_unary += 1
    for points in (set(),{origin},{v}):
        assert theta(at(xx,points)) == ((bg,{p:a for p,a in zx.items() if p in points}),*tx[1:])
        theta_unary += 1
    for k in (-3,0,4):
        assert theta(time_shift(xx,k)) == (tx[0],*(a+k if a is not None else None for a in tx[1:]))
        theta_unary += 1
    for t0 in range(-3,13):
        assert guard(xx,unit_at(t0)) == (tx[2] is None or tx[2] < t0)
        assert guard(unit_at(t0),xx) == (tx[1] is None or t0 < tx[1])
        threshold_checks += 2
    for yy in theta_states:
        ty = theta(yy)
        assert theta(add(xx,yy)) == theta_add(tx,ty)
        assert theta(mul(xx,yy)) == theta_mul(tx,ty)
        out = attempt(lambda: temporal(xx,yy))
        assert (out is not FAIL) == theta_guard(tx,ty)
        if out is not FAIL:
            assert theta(out) == theta_add(tx,ty)
        theta_pairs += 1
assert (theta_pairs,theta_unary,threshold_checks) == (64,56,256)
c0_twice,c9_twice = [mul(mul(xx,u),u) for xx in (c0,c9)]
maxima = theta(c0_twice)[2],theta(c9_twice)[2]
assert maxima == (10,11)
assert q(temporal(c0_twice,unit_at(11))) == 2
assert attempt(lambda:temporal(c9_twice,unit_at(11))) is FAIL
assert theta(mul(selected_low,u))[3] == 10  # Using max selected A would give 1.
same_theta_time = ceiling_state(9,selected_time=5)
assert theta(selected_low) == theta(same_theta_time)
time_filter_reads = tuple(q(filt(xx,lambda e,xx=xx:xx.e[e][0] == 0))
                          for xx in (selected_low,same_theta_time))
assert time_filter_reads == (1,0)
amplification_checks = 0
amp0,amp2 = [ceiling_state(s,floor=-1,ceiling=2) for s in (0,2)]
amp_empty = valid(replace(amp0,w=frozenset(),a=frozenset()))
for xx,yy in ((amp0,amp2),(amp_empty,replace(amp2,a=frozenset()))):
    tx,ty = theta(xx),theta(yy)
    assert tx[:3] == ty[:3] and tx[3] != ty[3]
    early = tx[1]
    n = tx[2] - (tx[3] if tx[3] is not None else ty[3]) + 1
    r0 = ty[3]+n
    for j in range(1,n+1):
        xx,yy = mul(xx,unit_at(early)),mul(yy,unit_at(early))
        for rich,old_t in ((xx,tx),(yy,ty)):
            s0 = old_t[3]
            expected_s = None if s0 is None else s0+j
            assert theta(rich)[2:] == (hi(old_t[2],expected_s),expected_s)
    assert theta(xx)[2] < r0 == theta(yy)[2]
    assert attempt(lambda:temporal(xx,unit_at(r0))) is not FAIL
    assert attempt(lambda:temporal(yy,unit_at(r0))) is FAIL
    amplification_checks += 1
print(f"pr2_theta: pairs={theta_pairs} unary={theta_unary} integer_thresholds={threshold_checks} amplification_cases={amplification_checks} archive_maxima={maxima[0]},{maxima[1]} following_U11=defined,failed time_filter={time_filter_reads[0]},{time_filter_reads[1]}")

theta_law_checks = 0
law_states = [empty,u,current_empty,c9]
for xx,yy,zz in product(law_states,repeat=3):
    assert theta(add(add(xx,yy),zz)) == theta(add(xx,add(yy,zz)))
    assert theta(mul(xx,add(yy,zz))) == theta(add(mul(xx,yy),mul(xx,zz)))
    assert theta(mul(add(xx,yy),zz)) == theta(add(mul(xx,zz),mul(yy,zz)))
    theta_law_checks += 1
for xx,yy in product(theta_states,repeat=2):
    assert theta(mul(xx,yy)) == theta(mul(yy,xx))
    assert theta(add(xx,yy)) == theta(add(yy,xx))
    assert theta(add(xx,empty)) == theta(xx)
    assert theta(mul(xx,u))[3] != 0
theta_left,theta_right = mul(mul(u,u),unit_at(1)),mul(u,mul(u,unit_at(1)))
assert theta(theta_left) == (({},delta),0,2,2)
assert theta(theta_right) == (({},delta),0,3,3)
assert theta(mul(u,empty)) == (({},{}),0,0,None) != theta(empty)
print(f"pr2_theta_laws: rich_triples={theta_law_checks} associativity_maxima={theta(theta_left)[2]},{theta(theta_right)[2]} zero_absorbing=False")

small = [sparse(dict(zip((origin,v,h),cs))) for cs in product((-1,0,1),repeat=3) if any(cs)]
extreme_checks,unit_product_checks = 0,0
for ca,cb in product(small,repeat=2):
    cc = conv(ca,cb)
    assert cc
    for extremum in (min,max):
        pa,pb = extremum(ca),extremum(cb)
        target = tuple(a+b for a,b in zip(pa,pb))
        assert extremum(cc) == target and cc[target] == ca[pa]*cb[pb]
        splits = [(p0,q0) for p0 in ca for q0 in cb
                  if tuple(a+b for a,b in zip(p0,q0)) == target]
        assert splits == [(pa,pb)]
    if cc == delta:
        assert len(ca) == len(cb) == 1
        assert next(iter(ca.values()))*next(iter(cb.values())) == 1
        unit_product_checks += 1
    extreme_checks += 1
unit_checks = 0
for point,sgn in product((origin,v,tuple(-a for a in v),h,tuple(-a for a in h)),(-1,1)):
    assert conv({point:sgn},{tuple(-a for a in point):sgn}) == delta
    unit_checks += 1
nonunit = {origin:2,v:-1}
assert sum(nonunit.values()) == 1 and len(nonunit) == 2
inverse_candidates = 0
for cs in product((-1,0,1),repeat=3):
    candidate = sparse(dict(zip((tuple(-a for a in v),origin,v),cs)))
    assert conv(nonunit,candidate) != delta
    inverse_candidates += 1
assert (len(small),extreme_checks,unit_checks,inverse_candidates) == (26,676,10,27)
print(f"pr2_extrema: nonzero_samples={len(small)} pairs={extreme_checks} products_delta0={unit_product_checks} signed_delta_inverses={unit_checks} nonunit_augmentation={sum(nonunit.values())} inverse_candidates_rejected={inverse_candidates}")

def tree_shapes(start, n):
    if n == 1:
        return [start]
    return [(left,right) for k in range(1,n) for left in tree_shapes(start,k)
            for right in tree_shapes(start+k,n-k)]

def tree_time(tree, times, delay=1):
    if isinstance(tree,int):
        return times[tree]
    return max(tree_time(tree[0],times,delay),tree_time(tree[1],times,delay))+delay

def leaf_depths(tree, depth=0):
    return [(tree,depth)] if isinstance(tree,int) else (
        leaf_depths(tree[0],depth+1)+leaf_depths(tree[1],depth+1))

def tree_rich(tree, times):
    return unit_at(times[tree]) if isinstance(tree,int) else mul(
        tree_rich(tree[0],times),tree_rich(tree[1],times))

tree_checks,rich_tree_checks = 0,0
for n in (3,4):
    for tree in tree_shapes(0,n):
        for times in product((-2,0,3),repeat=n):
            for delay in (1,2,3):
                assert tree_time(tree,times,delay) == max(times[i]+delay*d for i,d in leaf_depths(tree))
                tree_checks += 1
        times = tuple(range(n))
        rich = tree_rich(tree,times)
        expected = max(times[i]+d for i,d in leaf_depths(tree))
        assert theta(rich)[2:] == (expected,expected)
        rich_tree_checks += 1
translation_checks,delay_transport_checks = 0,0
for a,b,c in product(range(-3,4),range(-3,4),(-2,0,3)):
    assert max(a,b)+1+c == max(a+c,b+c)+1
    translation_checks += 1
for scale,b,delay,t0,t1 in product((1,2,3),(-2,0,3),(1,2,3),range(-2,3),range(-2,3)):
    assert scale*(max(t0,t1)+delay)+b == max(scale*t0+b,scale*t1+b)+scale*delay
    delay_transport_checks += 1
assert 2*(max(0,0)+1) != max(2*0,2*0)+1
assert (tree_checks,rich_tree_checks,translation_checks,delay_transport_checks) == (1377,7,147,675)
print(f"pr2_clock: depth_cases={tree_checks} rich_trees={rich_tree_checks} translations={translation_checks} scaled_delay_cases={delay_transport_checks} fixed_delay_scaling_rejected=True")

def mul_at(x, y, reference):
    z = mul(x,y)
    events = dict(z.e)
    for key in z.w:
        t0,p0,s0,r0 = events[key]
        events[key] = (t0,tuple(a-b for a,b in zip(p0,reference)),s0,r0)
    return valid(replace(z,e=events))

def affine_point(p, matrix, offset):
    return tuple(sum(a*b for a,b in zip(row,p))+v0 for row,v0 in zip(matrix,offset))

def affine_rich(x, matrix, offset):
    return valid(replace(x,e={key:(t0,affine_point(p0,matrix,offset),s0,r0)
                              for key,(t0,p0,s0,r0) in x.e.items()}))

def push_c(c, function):
    out = {}
    for p0,value in c.items():
        target = function(p0)
        out[target] = out.get(target,0)+value
    return sparse(out)

def conv_at(c, d, reference):
    return {tuple(a-b for a,b in zip(p0,reference)):value for p0,value in conv(c,d).items()}

matrices = [((1,0,0),(0,1,0),(0,0,1)),((2,0,0),(0,2,0),(0,0,2)),
            ((1,1,0),(0,1,0),(0,0,-1)),((0,0,0),(0,1,0),(0,0,1))]
references,offset = (origin,(1,2,-1)),(2,-1,3)
reference_states = [u,sx,sy,current_empty]
reference_checks,affine_checks,space_unit_checks = 0,0,0
for reference in references:
    for xx,yy in product(reference_states,repeat=2):
        result = mul_at(xx,yy,reference)
        standard = mul(xx,yy)
        assert result.e.keys() == standard.e.keys()
        assert (result.o,result.w,result.a) == (standard.o,standard.w,standard.a)
        assert all((v0[0],v0[2:]) == (standard.e[e][0],standard.e[e][2:]) for e,v0 in result.e.items())
        assert (q(result),charge(result,result.w),len(result.e)) == (
            q(xx)*q(yy),0,len(xx.e)+len(yy.e)+len(xx.w)*len(yy.w))
        assert read_pair(result) == tuple(conv_at(a,b,reference) for a,b in zip(read_pair(xx),read_pair(yy)))
        if reference == origin:
            assert result == standard
        reference_checks += 1
        for matrix in matrices:
            function = lambda p,matrix=matrix:affine_point(p,matrix,offset)
            transported = affine_rich(result,matrix,offset)
            assert transported == mul_at(affine_rich(xx,matrix,offset),affine_rich(yy,matrix,offset),function(reference))
            assert read_pair(transported) == tuple(push_c(c,function) for c in read_pair(result))
            for a,b in zip(read_pair(xx),read_pair(yy)):
                assert push_c(conv_at(a,b,reference),function) == conv_at(push_c(a,function),push_c(b,function),function(reference))
            affine_checks += 1
    for c in small:
        assert conv_at({reference:1},c,reference) == conv_at(c,{reference:1},reference) == c
        space_unit_checks += 1
assert mul_at(spatial(u,offset=1),spatial(u,offset=1),origin) != spatial(mul_at(u,u,origin),offset=1)
collapsed = realize({}, {origin:1,v:1})
matrix = matrices[-1]
function = lambda p:affine_point(p,matrix,origin)
transported = affine_rich(collapsed,matrix,origin)
assert transported.e.keys() == collapsed.e.keys() and len(transported.e) == 4
wrong_before = affine_rich(at(collapsed,{origin}),matrix,origin)
wrong_after = at(transported,{origin})
assert (q(wrong_before),q(wrong_after)) == (1,2)
pull_selected = filt(collapsed,lambda e:function(collapsed.e[e][1]) == origin)
assert affine_rich(pull_selected,matrix,origin) == wrong_after
assert push_c({origin:1},function) == {origin:1} != read_pair(wrong_after)[1]
assert push_c(read_pair(pull_selected)[1],function) == read_pair(wrong_after)[1] == {origin:2}
assert (reference_checks,affine_checks,space_unit_checks) == (32,128,52)
print(f"pr2_reference: rich_pairs={reference_checks} affine_transports={affine_checks} space_units={space_unit_checks} noninjective_events={len(transported.e)} direct_image_filter={q(wrong_before)},{q(wrong_after)} pullback_filter={q(wrong_after)}")

# PR3: finite checks only, using the original Rich archive operations.
import json as pr3_json
from random import Random as pr3_Random
from itertools import combinations as pr3_combinations

pr3_counts = {"source_updates": 0, "source_witnesses": 0,
              "causal_updates": 0, "product_antichains": 0,
              "bare_probes": 0, "legal_probes": 0,
              "mobius_profiles": 0, "mobius_coefficients": 0,
              "bounded_contexts": 0, "redundant_insertions": 0}

def pr3_bytes(value):
    def canonical(z):
        if isinstance(z, dict):
            return sorted([[canonical(k), canonical(v)] for k, v in z.items()],
                          key=lambda item: pr3_json.dumps(item, sort_keys=True))
        if isinstance(z, (set, frozenset)):
            return sorted([canonical(k) for k in z], key=pr3_json.dumps)
        if isinstance(z, (tuple, list)):
            return [canonical(k) for k in z]
        return z
    return pr3_json.dumps(canonical(value), separators=(",", ":")).encode("utf-8")

def pr3_equal(actual, expected, counter):
    assert pr3_bytes(actual) == pr3_bytes(expected), (counter, actual, expected)
    pr3_counts[counter] += 1

def pr3_rho_src(x):
    return tuple(sparse(c) for c in coarse(x, lambda e: (x.e[e][1], x.e[e][3])))

def pr3_pair_product(c, d):
    out = {}
    for (p, r), n in c.items():
        for (q0, s), m in d.items():
            key = (tuple(a+b for a, b in zip(p, q0)), ("pair", r, s))
            out[key] = out.get(key, 0) + n*m
    return sparse(out)

def pr3_alpha(x, e, timed=False):
    t0, p, sign, source = x.e[e]
    return (p, sign, source, t0) if timed else (p, sign, source)

def pr3_U(x, e, timed=False):
    return frozenset(pr3_alpha(x, d, timed) for d in x.w
                     if e == d or (e, d) in x.o)

def pr3_profile(x, timed=False):
    out = {}
    for e in x.w:
        key = (pr3_alpha(x, e, timed), int(e in x.a), pr3_U(x, e, timed))
        out[key] = out.get(key, 0) + x.e[e][2]
    return sparse(out)

def pr3_V(profile):
    return frozenset(a for a, b, upper in profile)

def pr3_causal_filter(x, Q, timed=False):
    # The target domain is Omega = Rich.w, including unselected targets.
    targets = frozenset(d for d in x.w if pr3_alpha(x, d, timed) in Q)
    assert targets <= x.w
    return filt(x, lambda e: any(e == d or (e, d) in x.o for d in targets))

def pr3_diamond(a, b):
    return (tuple(p+q0 for p, q0 in zip(a[0], b[0])), a[1]*b[1],
            ("pair", a[2], b[2]))

def pr3_profile_product(c, d):
    out = {}
    for (a, b, upper), n in c.items():
        for (aa, bb, uu), m in d.items():
            joined = pr3_diamond(a, aa)
            key = (joined, b*bb, frozenset((joined,)))
            out[key] = out.get(key, 0) + n*m
    return sparse(out)

def pr3_subsets(values):
    values = sorted(values, key=repr)
    return [frozenset(c) for n in range(len(values)+1)
            for c in pr3_combinations(values, n)]

pr3_U0 = integer(1)
assert charge(pr3_U0, pr3_U0.w) == 0 and q(pr3_U0) == 1
assert len(pr3_U0.w) == 2 and not pr3_U0.o

class pr3_SignTargets:
    # Membership in the fixed attribute set {a in Attr : sign(a) = eps}.
    def __init__(self, eps):
        assert eps in (-1, 1)
        self.eps = eps
    def __contains__(self, a):
        return a[1] == self.eps

def pr3_P_eps(z, eps):
    return pr3_causal_filter(mul(z, pr3_U0), pr3_SignTargets(eps))

def pr3_probe(x, Q, v0, eta):
    p, eps, tau = v0
    selected = x if eta == 1 else neg(x)
    H = pr3_causal_filter(filt(at(selected, {p}),
                              lambda e: selected.e[e][3] == tau), Q)
    target = (p, eps, ("pair", tau, ("leaf", 0)))
    return q(pr3_causal_filter(mul(H, pr3_U0), {target}))

pr3_rng = pr3_Random(20260910)
pr3_samples = []
for pr3_i in range(48):
    pr3_n = pr3_rng.choice((0, 2, 4))
    pr3_signs = [1]*(pr3_n//2) + [-1]*(pr3_n//2)
    pr3_rng.shuffle(pr3_signs)
    pr3_events = {}
    for pr3_j, pr3_sign in enumerate(pr3_signs):
        pr3_p = origin if pr3_i % 2 else pr3_rng.choice((origin, v, h))
        pr3_r = ("leaf", 0) if pr3_i % 2 else pr3_rng.choice(
            (("leaf", 0), ("leaf", 7), ("pair", ("leaf", 0), ("leaf", 7))))
        pr3_events[pr3_j] = (pr3_rng.randrange(-1, 3), pr3_p, pr3_sign, pr3_r)
    pr3_whole = frozenset(pr3_events)
    for pr3_j in range(pr3_rng.randrange(3)):
        pr3_events[("old", pr3_j)] = (pr3_rng.randrange(-2, 4), v, 1, ("leaf", 9))
    pr3_edges = {(a, b) for a in pr3_events for b in pr3_events
                 if pr3_events[a][0] < pr3_events[b][0] and pr3_rng.randrange(3) == 0}
    pr3_chosen = frozenset(e for e in sorted(pr3_whole) if pr3_rng.randrange(2))
    pr3_samples.append(valid(Rich(pr3_events, closure(pr3_edges), pr3_whole, pr3_chosen)))

for pr3_x in pr3_samples:
    pr3_y = pr3_rng.choice(pr3_samples)
    pr3_w, pr3_z = pr3_rho_src(pr3_x)
    pr3_wy, pr3_zy = pr3_rho_src(pr3_y)
    pr3_S, pr3_L = {origin, h}, {("leaf", 0), ("leaf", 7)}
    pr3_equal(pr3_rho_src(add(pr3_x, pr3_y)),
              (plus_c(pr3_w, pr3_wy), plus_c(pr3_z, pr3_zy)), "source_updates")
    pr3_mul = mul(pr3_x, pr3_y)
    pr3_equal(pr3_rho_src(pr3_mul),
              (pr3_pair_product(pr3_w, pr3_wy), pr3_pair_product(pr3_z, pr3_zy)),
              "source_updates")
    assert all(r[0] == "pair" for c in pr3_rho_src(pr3_mul) for p, r in c)
    pr3_equal(pr3_rho_src(neg(pr3_x)), (pr3_w, plus_c(pr3_w, minus_c(pr3_z))),
              "source_updates")
    pr3_equal(pr3_rho_src(at(pr3_x, pr3_S)),
              (pr3_w, {k: n for k, n in pr3_z.items() if k[0] in pr3_S}), "source_updates")
    pr3_source_filtered = filt(pr3_x, lambda e: pr3_x.e[e][3] in pr3_L)
    pr3_equal(pr3_rho_src(pr3_source_filtered),
              (pr3_w, {k: n for k, n in pr3_z.items() if k[1] in pr3_L}), "source_updates")
    assert not any(a in pr3_mul.w for a, b in pr3_mul.o)
    assert not any(a in pr3_mul.w and b in pr3_mul.w for a, b in pr3_mul.o)
    pr3_counts["product_antichains"] += 1
    pr3_g, pr3_gy = pr3_profile(pr3_x), pr3_profile(pr3_y)
    assert pr3_V(pr3_g) == {pr3_alpha(pr3_x, e) for e in pr3_x.w}
    assert all(pr3_alpha(pr3_x, e) in pr3_U(pr3_x, e) for e in pr3_x.w)
    pr3_equal(pr3_profile(add(pr3_x, pr3_y)), plus_c(pr3_g, pr3_gy), "causal_updates")
    pr3_equal(pr3_profile(neg(pr3_x)),
              push_c(pr3_g, lambda k: (k[0], 1-k[1], k[2])), "causal_updates")
    pr3_equal(pr3_profile(at(pr3_x, pr3_S)),
              push_c(pr3_g, lambda k: (k[0], k[1]*int(k[0][0] in pr3_S), k[2])),
              "causal_updates")
    pr3_equal(pr3_profile(pr3_source_filtered),
              push_c(pr3_g, lambda k: (k[0], k[1]*int(k[0][2] in pr3_L), k[2])),
              "causal_updates")
    for pr3_Q in pr3_subsets(pr3_V(pr3_g)):
        pr3_equal(pr3_profile(pr3_causal_filter(pr3_x, pr3_Q)),
                  push_c(pr3_g, lambda k: (k[0], k[1]*int(bool(k[2] & pr3_Q)), k[2])),
                  "causal_updates")
    pr3_equal(pr3_profile(pr3_mul), pr3_profile_product(pr3_g, pr3_gy), "causal_updates")
    pr3_equal(pr3_profile(time_shift(pr3_x, 3)), pr3_g, "causal_updates")
    # Exercise both success and failure, then force a legal nonempty timing if needed.
    assert guard(pr3_x, pr3_y) == theta_guard(theta(pr3_x), theta(pr3_y))
    pr3_late = time_shift(pr3_y, (theta(pr3_x)[2] or 0) - (theta(pr3_y)[1] or 0) + 1)
    assert guard(pr3_x, pr3_late)
    pr3_equal(pr3_profile(temporal(pr3_x, pr3_late)),
              plus_c(push_c(pr3_g, lambda k: (k[0], k[1], k[2] | pr3_V(pr3_gy))), pr3_gy),
              "causal_updates")

pr3_l0, pr3_l1 = ("leaf", 0), ("leaf", 1)
pr3_bracket_left, pr3_bracket_right = mul(mul(u, u), two), mul(u, mul(u, two))
pr3_expected_left = {(origin, ("pair", ("pair", pr3_l0, pr3_l0), r)): 1
                     for r in (pr3_l0, pr3_l1)}
pr3_expected_right = {(origin, ("pair", pr3_l0, ("pair", pr3_l0, r))): 1
                      for r in (pr3_l0, pr3_l1)}
for pr3_actual, pr3_expected in (
        (pr3_rho_src(pr3_bracket_left), ({}, pr3_expected_left)),
        (pr3_rho_src(pr3_bracket_right), ({}, pr3_expected_right)),
        (pr3_rho_src(source7), ({}, {(origin, ("leaf", 7)): 1})),
        (pr3_rho_src(source8), ({}, {(origin, ("leaf", 8)): 1})),
        (pr3_rho_src(comm_left), ({}, {(origin, ("pair", ("leaf", 7), ("leaf", 8))): 1})),
        (pr3_rho_src(comm_right), ({}, {(origin, ("pair", ("leaf", 8), ("leaf", 7))): 1}))):
    pr3_equal(pr3_actual, pr3_expected, "source_witnesses")
assert set(pr3_expected_left).isdisjoint(pr3_expected_right)
assert pr3_rho_src(comm_left) != pr3_rho_src(comm_right)
assert pr3_rho_src(source7)[1] != pr3_rho_src(source8)[1]

# D6: bare probes cancel, including equality after N, but the legal isolation separates.
pr3_d1e = {e: (t0, origin, sign, pr3_l0)
           for e, t0, sign in zip("abcd", (0, 1, 2, 2), (1, -1, 1, -1))}
pr3_d1x = valid(Rich(pr3_d1e, closure({("a", "b"), ("b", "c"), ("b", "d")}),
                     frozenset(pr3_d1e), frozenset("ab")))
pr3_d1y = replace(pr3_d1x, a=frozenset())
pr3_vp, pr3_vm = (origin, 1, pr3_l0), (origin, -1, pr3_l0)
assert pr3_U(pr3_d1x, "a") == pr3_U(pr3_d1x, "b") == {pr3_vp, pr3_vm}
for pr3_Q, pr3_S, pr3_L in product(pr3_subsets({pr3_vp, pr3_vm}),
                                   (set(), {origin}), (set(), {pr3_l0})):
    pr3_raw, pr3_complements = [], []
    for pr3_x in (pr3_d1x, pr3_d1y):
        for pr3_dest, pr3_z0 in ((pr3_raw, pr3_x), (pr3_complements, neg(pr3_x))):
            pr3_dest.append(q(pr3_causal_filter(filt(at(pr3_z0, pr3_S),
                                    lambda e: pr3_z0.e[e][3] in pr3_L), pr3_Q)))
    assert pr3_raw == [0, 0] and pr3_complements[0] == pr3_complements[1]
    pr3_counts["bare_probes"] += 1
pr3_isolated = tuple(q(pr3_P_eps(z, 1)) for z in (pr3_d1x, pr3_d1y))
assert pr3_isolated == (1, 0)
assert tuple(pr3_probe(z, {pr3_vp, pr3_vm}, pr3_vp, 1) for z in (pr3_d1x, pr3_d1y)) == (1, 0)
# Complemented bare readings are equal, NOT identically zero.
assert tuple(q(pr3_causal_filter(neg(z), {pr3_vp})) for z in (pr3_d1x, pr3_d1y)) == (1, 1)

# Targets outside Omega must have no effect, even when archived and reachable.
pr3_outside = valid(Rich({"a": (0, origin, 1, pr3_l0), "b": (0, origin, -1, pr3_l0),
                         "old": (1, origin, 1, ("leaf", 9))},
                        frozenset({("a", "old")}), frozenset("ab"), frozenset("a")))
assert set(pr3_outside.e) - pr3_outside.w == {"old"}
assert q(pr3_causal_filter(pr3_outside, {pr3_alpha(pr3_outside, "old")})) == 0
assert q(past(pr3_outside, {"old"})) == 1
assert pr3_U(pr3_outside, "a") == {pr3_vp}

# Full finite Boolean inversion through legal carrier-parameter contexts, both selection bits.
for pr3_x in pr3_samples + [pr3_d1x, pr3_d1y, pr3_outside]:
    pr3_D = frozenset(pr3_alpha(pr3_x, e) for e in pr3_x.w)
    pr3_powerset = pr3_subsets(pr3_D)
    pr3_restored = {}
    for pr3_v0, pr3_eta in product(sorted(pr3_D, key=repr), (0, 1)):
        pr3_f = {}
        for pr3_Q in pr3_powerset:
            pr3_f[pr3_Q] = pr3_probe(pr3_x, pr3_Q, pr3_v0, pr3_eta)
            pr3_expected = sum(pr3_x.e[e][2] for e in pr3_x.w
                               if pr3_alpha(pr3_x, e) == pr3_v0
                               and int(e in pr3_x.a) == pr3_eta and pr3_U(pr3_x, e) & pr3_Q)
            assert pr3_f[pr3_Q] == pr3_expected
            pr3_counts["legal_probes"] += 1
        pr3_h = {W: pr3_f[pr3_D] - pr3_f[pr3_D-W] for W in pr3_powerset}
        for pr3_upper in pr3_powerset:
            pr3_coeff = sum((-1)**(len(pr3_upper)-len(W))*pr3_h[W]
                            for W in pr3_subsets(pr3_upper))
            if pr3_coeff:
                pr3_restored[(pr3_v0, pr3_eta, pr3_upper)] = pr3_coeff
            pr3_counts["mobius_coefficients"] += 1
    pr3_equal(pr3_restored, pr3_profile(pr3_x), "mobius_profiles")

# B2: a bounded family of the actual signature; no new primitive is used.
assert pr3_profile(causal) == pr3_profile(no_causal) == {
    (pr3_vp, 1, frozenset((pr3_vp,))): 2,
    (pr3_vm, 0, frozenset((pr3_vm,))): -2}
pr3_ops = [neg, lambda z: at(z, {origin}), lambda z: at(z, {v}),
           lambda z: filt(z, lambda e: z.e[e][3] == pr3_l0),
           lambda z: add(z, u), lambda z: add(u, z),
           lambda z: mul(z, u), lambda z: mul(u, z),
           lambda z: temporal(z, unit_at(2)), lambda z: temporal(unit_at(-1), z),
           lambda z: time_shift(z, 1), lambda z: time_shift(z, -1)]
pr3_ops += [lambda z, Q=Q: pr3_causal_filter(z, Q)
            for Q in pr3_subsets({pr3_vp, pr3_vm})]
for pr3_depth in range(3):
    for pr3_word in product(pr3_ops, repeat=pr3_depth):
        assert observe(pr3_word, causal, q) == observe(pr3_word, no_causal, q)
        pr3_counts["bounded_contexts"] += 1
pr3_time_reads = tuple(q(pr3_causal_filter(z, {(origin, 1, pr3_l0, 1)}, timed=True))
                       for z in (causal, no_causal))
assert pr3_time_reads == (2, 1)
pr3_J_reads = tuple(q(filt(z, lambda e: any((e, d) in z.o for d in z.w)))
                    for z in (causal, no_causal))
assert pr3_J_reads == (1, 0)

# D7: inserting a same-attribute generating edge creates a cross-attribute closure edge.
pr3_d2e = {e: (t0, origin, sign, pr3_l0)
           for e, t0, sign in zip("abcd", (0, 1, 2, 0), (1, 1, -1, -1))}
pr3_d2x = valid(Rich(pr3_d2e, frozenset({("b", "c")}), frozenset(pr3_d2e), frozenset("a")))
pr3_d2y = valid(replace(pr3_d2x, o=closure(pr3_d2x.o | {("a", "b")})))
assert pr3_rho_src(pr3_d2x) == pr3_rho_src(pr3_d2y)
assert theta(pr3_d2x)[1:] == theta(pr3_d2y)[1:]
pr3_edge_reads = tuple(q(pr3_causal_filter(z, {pr3_vm})) for z in (pr3_d2x, pr3_d2y))
assert pr3_edge_reads == (0, 1)

# D8: all singleton hitting marginals agree, but a two-attribute query differs.
pr3_d3e = {"e1": (0, origin, 1, pr3_l0), "e2": (0, origin, 1, pr3_l0),
           "b": (1, origin, -1, ("leaf", 1)), "c": (1, origin, -1, ("leaf", 2))}
pr3_d3x = valid(Rich(pr3_d3e, frozenset({("e2", "b"), ("e2", "c")}),
                     frozenset(pr3_d3e), frozenset(("e1", "e2"))))
pr3_d3y = valid(replace(pr3_d3x, o=frozenset({("e1", "b"), ("e2", "c")})))
for pr3_attr in {pr3_alpha(pr3_d3x, e) for e in pr3_d3x.w}:
    assert q(pr3_causal_filter(pr3_d3x, {pr3_attr})) == q(pr3_causal_filter(pr3_d3y, {pr3_attr}))
pr3_bc = {pr3_alpha(pr3_d3x, e) for e in ("b", "c")}
pr3_marginal_reads = tuple(q(pr3_causal_filter(z, pr3_bc)) for z in (pr3_d3x, pr3_d3y))
assert pr3_marginal_reads == (1, 2)

# A lawful edge insertion with U(f) <= U(e) preserves every current upper set.
for pr3_x in pr3_samples:
    for pr3_e, pr3_f0 in product(sorted(pr3_x.w), repeat=2):
        if (pr3_x.e[pr3_e][0] < pr3_x.e[pr3_f0][0]
                and (pr3_e, pr3_f0) not in pr3_x.o
                and pr3_U(pr3_x, pr3_f0) <= pr3_U(pr3_x, pr3_e)):
            pr3_y = valid(replace(pr3_x, o=closure(pr3_x.o | {(pr3_e, pr3_f0)})))
            assert all(pr3_U(pr3_x, e) == pr3_U(pr3_y, e) for e in pr3_x.w)
            assert pr3_profile(pr3_x) == pr3_profile(pr3_y)
            pr3_counts["redundant_insertions"] += 1
assert pr3_counts["redundant_insertions"] > 0

# D10: even the time-attribute profile need not recover incidence or history isomorphism.
pr3_d5e = {e: (t0, origin, 1, pr3_l0)
           for e, t0 in zip(("a1", "a2", "b1", "b2"), (0, 0, 1, 1))}
pr3_d5e.update({("n", i): (0, origin, -1, pr3_l0) for i in range(4)})
pr3_d5x = valid(Rich(pr3_d5e, frozenset({("a1", "b1"), ("a2", "b2")}),
                     frozenset(pr3_d5e), frozenset(("a1", "a2", "b1", "b2"))))
pr3_d5y = valid(replace(pr3_d5x, o=frozenset({("a1", "b1"), ("a2", "b1")})))
assert pr3_profile(pr3_d5x, timed=True) == pr3_profile(pr3_d5y, timed=True)
pr3_indegrees = tuple(sorted(sum((a, b) in z.o for a in z.e) for b in ("b1", "b2"))
                      for z in (pr3_d5x, pr3_d5y))
assert pr3_indegrees == ([1, 1], [0, 2])
print(f"pr3_source: samples={len(pr3_samples)} updates={pr3_counts['source_updates']} witnesses={pr3_counts['source_witnesses']} brackets={len(pr3_bracket_left.e)},{len(pr3_bracket_right.e)} B1=distinct ordered_pair=distinct")
print(f"pr3_causal: updates={pr3_counts['causal_updates']} product_antichains={pr3_counts['product_antichains']} targets=Omega bare_probes={pr3_counts['bare_probes']} P_plus={pr3_isolated[0]},{pr3_isolated[1]} legal_probes={pr3_counts['legal_probes']} mobius_profiles={pr3_counts['mobius_profiles']} mobius_coefficients={pr3_counts['mobius_coefficients']} bounded_contexts={pr3_counts['bounded_contexts']} B2_time={pr3_time_reads[0]},{pr3_time_reads[1]} strict_successor={pr3_J_reads[0]},{pr3_J_reads[1]} edge={pr3_edge_reads[0]},{pr3_edge_reads[1]} marginals={pr3_marginal_reads[0]},{pr3_marginal_reads[1]} redundant_insertions={pr3_counts['redundant_insertions']} timed_nonisomorphism=True")

# PR4: temporal causal checks; PR1--PR3 and the Rich operations remain unchanged.
pr4_counts = {name: 0 for name in (
    "updates", "endpoint_updates", "earliest_rows", "product_antichains",
    "guard_success", "strict_failures", "context_reads", "mobius_coefficients",
    "mobius_profiles", "xi_paths", "forget_paths", "q_expression", "kernel_edges")}

def pr4_equal(actual, expected, counter):
    assert pr3_bytes(actual) == pr3_bytes(expected), (counter, actual, expected)
    pr4_counts[counter] += 1

def pr4_profile(x):
    return pr3_profile(x, timed=True)

def pr4_earliest(upper):
    earliest_time = min(a[3] for a in upper)
    first = [a for a in upper if a[3] == earliest_time]
    assert len(first) == 1, upper
    return first[0]

def pr4_support_time(g):
    return max((a[3] for a, b, upper in g), default=None)

def pr4_shift_attr(a, k):
    return (*a[:3], a[3] + k)

def pr4_shift_profile(g, k):
    return push_c(g, lambda row: (pr4_shift_attr(row[0], k), row[1],
                  frozenset(pr4_shift_attr(a, k) for a in row[2])))

def pr4_diamond(a, aa):
    return (*pr3_diamond(a[:3], aa[:3]), max(a[3], aa[3]) + 1)

def pr4_profile_product(g, gg):
    result = {}
    for (a, b, upper), value in g.items():
        for (aa, bb, uu), other in gg.items():
            joined = pr4_diamond(a, aa)
            row = (joined, b * bb, frozenset((joined,)))
            result[row] = result.get(row, 0) + value * other
    return sparse(result)

def pr4_xi_direct(x):
    # Definition 22: independent traversal of Omega and A, not of a profile.
    background, chosen = {}, {}
    for e in x.w:
        time, position, sign, source = x.e[e]
        cell = (time, position)
        background[cell] = background.get(cell, 0) + sign
    for e in x.a:
        time, position, sign, source = x.e[e]
        cell = (time, position)
        chosen[cell] = chosen.get(cell, 0) + sign
    return (sparse(background), sparse(chosen),
            min((event[0] for event in x.e.values()), default=None),
            max((event[0] for event in x.e.values()), default=None),
            max((x.e[e][0] for e in x.w), default=None))

def pr4_xi_from_profile(g, m, M):
    # The coefficient already includes sign; do not multiply it by a[1].
    background, chosen = {}, {}
    for (a, b, upper), value in g.items():
        cell = (a[3], a[0])
        background[cell] = background.get(cell, 0) + value
        if b == 1:
            chosen[cell] = chosen.get(cell, 0) + value
    return sparse(background), sparse(chosen), m, M, pr4_support_time(g)

def pr4_forget_time(g):
    return push_c(g, lambda row: (row[0][:3], row[1],
                                 frozenset(a[:3] for a in row[2])))

def pr4_read_table(x, D):
    readings = {}
    for eta in (0, 1):
        selected = x if eta == 1 else neg(x)
        for Q in pr3_subsets(D):
            readings[(eta, Q)] = q(pr3_causal_filter(selected, Q, timed=True))
            pr4_counts["context_reads"] += 1
    return readings

def pr4_restore(D, readings):
    # Inputs are the fixed finite query vocabulary and terminal context readings.
    # No Rich state, profile function, own-attribute probe or product is consumed.
    restored = {}
    subsets = pr3_subsets(D)
    for eta in (0, 1):
        h0 = {W: readings[(eta, D)] - readings[(eta, D - W)] for W in subsets}
        for upper in subsets:
            coefficient = sum((-1) ** (len(upper) - len(W)) * h0[W]
                              for W in pr3_subsets(upper))
            if coefficient:
                assert upper
                a = pr4_earliest(upper)
                assert coefficient * a[1] > 0
                restored[(a, eta, upper)] = coefficient
            pr4_counts["mobius_coefficients"] += 1
    return restored

pr4_rng = pr3_Random(2026091004)
pr4_samples = []
for pr4_i in range(64):
    pr4_n = pr4_rng.choice((0, 2, 4, 6))
    pr4_signs = [1] * (pr4_n // 2) + [-1] * (pr4_n // 2)
    pr4_rng.shuffle(pr4_signs)
    pr4_events = {j: (pr4_rng.randrange(-5, 5),
                        pr4_rng.choice((origin, v, h)), sign,
                        pr4_rng.choice((pr3_l0, pr3_l1, ("pair", pr3_l0, pr3_l1))))
                  for j, sign in enumerate(pr4_signs)}
    pr4_whole = frozenset(pr4_events)
    for pr4_j in range(pr4_rng.randrange(3)):
        pr4_events[("old", pr4_j)] = (pr4_rng.randrange(-7, 7), v, 1, ("leaf", 9))
    pr4_edges = {(e, d) for e in pr4_events for d in pr4_events
                 if pr4_events[e][0] < pr4_events[d][0] and pr4_rng.randrange(4) == 0}
    pr4_chosen = frozenset(e for e in sorted(pr4_whole) if pr4_rng.randrange(2))
    pr4_samples.append(valid(Rich(pr4_events, closure(pr4_edges), pr4_whole, pr4_chosen)))

# Directed boundaries: empty archive; nonempty archive with empty Omega;
# highest current time cancels in W and Z but is visible in Gamma_t support.
pr4_archive_only = valid(Rich({"old": (-4, origin, 1, pr3_l0)},
                              frozenset(), frozenset(), frozenset()))
pr4_cancel_events = {"p": (-3, origin, 1, pr3_l0), "n": (-3, origin, -1, pr3_l0),
                     "top+": (4, origin, 1, pr3_l0), "top-": (4, origin, -1, pr3_l0),
                     "old_min": (-9, v, 1, pr3_l0), "old_max": (8, v, 1, pr3_l0)}
pr4_cancel = valid(Rich(pr4_cancel_events, frozenset(),
                        frozenset(("p", "n", "top+", "top-")), frozenset(("p",))))
assert pr4_xi_direct(pr4_cancel) == ({}, {(-3, origin): 1}, -9, 8, 4)
assert pr4_support_time(pr4_profile(pr4_cancel)) == 4

# D11: one fixed context, different selections at negative own times.
pr4_d11e = {e: (t0, origin, sign, pr3_l0)
            for e, t0, sign in zip("abcd", (-2, -1, 0, 0), (1, 1, -1, -1))}
pr4_d11x = valid(Rich(pr4_d11e, frozenset({("a", "b")}),
                      frozenset(pr4_d11e), frozenset("a")))
pr4_d11y = replace(pr4_d11x, a=frozenset("b"))
pr4_d11_c = {(pr3_vp, 1, frozenset((pr3_vp,))): 1,
             (pr3_vp, 0, frozenset((pr3_vp,))): 1,
             (pr3_vm, 0, frozenset((pr3_vm,))): -2}
assert pr3_profile(pr4_d11x) == pr3_profile(pr4_d11y) == pr4_d11_c
assert pr3_rho_src(pr4_d11x) == pr3_rho_src(pr4_d11y) == ({}, {(origin, pr3_l0): 1})
assert theta(pr4_d11x)[1:] == theta(pr4_d11y)[1:] == (-2, 0, 0)
pr4_d11_W = {(-2, origin): 1, (-1, origin): 1, (0, origin): -2}
assert pr4_xi_direct(pr4_d11x) == (pr4_d11_W, {(-2, origin): 1}, -2, 0, 0)
assert pr4_xi_direct(pr4_d11y) == (pr4_d11_W, {(-1, origin): 1}, -2, 0, 0)
assert pr4_profile(pr4_d11x) != pr4_profile(pr4_d11y)
pr4_d11_reads = tuple(q(pr3_causal_filter(z, {(origin, 1, pr3_l0, -2)}, timed=True))
                      for z in (pr4_d11x, pr4_d11y))
assert pr4_d11_reads == (1, 0)
pr4_common_k = min(theta(z)[1] for z in (pr4_d11x, pr4_d11y)) - 1
pr4_shift_probe = tuple(q(pr3_causal_filter(mul(z, time_shift(pr3_U0, pr4_common_k)),
                         {(origin, 1, ("pair", pr3_l0, pr3_l0), -1)}, timed=True))
                        for z in (pr4_d11x, pr4_d11y))
pr4_flat_probe = tuple(q(pr3_causal_filter(mul(z, pr3_U0),
                        {(origin, 1, ("pair", pr3_l0, pr3_l0), 1)}, timed=True))
                       for z in (pr4_d11x, pr4_d11y))
assert pr4_shift_probe == (1, 0) and pr4_flat_probe == (1, 1)
assert pr4_profile(mul(pr4_d11x, pr3_U0)) == pr4_profile(mul(pr4_d11y, pr3_U0))

# D12: four input selections on the same balanced context; q expression below.
pr4_d12 = valid(Rich({e: (t0, origin, sign, pr3_l0)
                      for e, t0, sign in zip("abcd", (0, 1, 0, 0), (1, 1, -1, -1))},
                     frozenset({("a", "b")}), frozenset("abcd"), frozenset("ab")))
pr4_d12_family = [replace(pr4_d12, a=A) for A in pr3_subsets("ab")]

# D1 and D5 retain their section 26 numbering; check both incomparability directions.
pr4_d1e = {j: (t0, p, sign, pr3_l0) for j, (t0, p, sign) in enumerate(
            ((0, origin, 1), (0, origin, -1), (1, v, 1), (1, v, -1)))}
pr4_d1x = valid(Rich(pr4_d1e, frozenset(), frozenset(pr4_d1e), frozenset((0, 2))))
pr4_d1y = valid(replace(pr4_d1x, e={j: (t0, v if p == origin else origin, sign, r)
                                    for j, (t0, p, sign, r) in pr4_d1e.items()}))
pr4_d5x = pr3_U0
pr4_d5y = valid(replace(pr4_d5x, e={e: (t0, p, sign, pr3_l1 if e in pr4_d5x.a else r)
                                    for e, (t0, p, sign, r) in pr4_d5x.e.items()}))
pr4_cases = pr4_samples + [empty, pr4_archive_only, pr4_cancel, pr4_d11x, pr4_d11y,
                           pr3_outside, pr3_d2y, causal, no_causal, pr3_d5x, pr3_d5y,
                           pr4_d1x, pr4_d1y, pr4_d5x, pr4_d5y] + pr4_d12_family
pr4_xi_cases = list(pr4_cases)

def pr4_check_update(x, expected_g, expected_endpoints):
    pr4_equal(pr4_profile(x), expected_g, "updates")
    pr4_equal(theta(x)[1:], expected_endpoints, "endpoint_updates")
    assert pr4_support_time(expected_g) == expected_endpoints[2]
    pr4_xi_cases.append(x)

for pr4_i, pr4_x in enumerate(pr4_cases):
    assert charge(pr4_x, pr4_x.w) == 0
    pr4_g = pr4_profile(pr4_x)
    pr4_tx = theta(pr4_x)
    pr4_D = frozenset(pr3_alpha(pr4_x, e, timed=True) for e in pr4_x.w)
    assert pr3_V(pr4_g) == pr4_D
    assert pr4_support_time(pr4_g) == pr4_tx[3]
    for (pr4_a, pr4_b, pr4_upper), pr4_value in pr4_g.items():
        assert pr4_a == pr4_earliest(pr4_upper) and pr4_value * pr4_a[1] > 0
        pr4_counts["earliest_rows"] += 1
    pr4_equal(pr4_restore(pr4_D, pr4_read_table(pr4_x, pr4_D)), pr4_g, "mobius_profiles")
    pr4_S, pr4_L = {origin, h}, {pr3_l0, pr3_l1}
    pr4_check_update(neg(pr4_x), push_c(pr4_g, lambda k: (k[0], 1-k[1], k[2])), pr4_tx[1:])
    pr4_check_update(at(pr4_x, pr4_S),
                     push_c(pr4_g, lambda k: (k[0], k[1]*int(k[0][0] in pr4_S), k[2])),
                     pr4_tx[1:])
    pr4_check_update(filt(pr4_x, lambda e: pr4_x.e[e][3] in pr4_L),
                     push_c(pr4_g, lambda k: (k[0], k[1]*int(k[0][2] in pr4_L), k[2])),
                     pr4_tx[1:])
    for pr4_Q in pr3_subsets(pr4_D):
        pr4_check_update(pr3_causal_filter(pr4_x, pr4_Q, timed=True),
                         push_c(pr4_g, lambda k: (k[0], k[1]*int(bool(k[2] & pr4_Q)), k[2])),
                         pr4_tx[1:])
    for pr4_k in (-7, 0, 3):
        pr4_check_update(time_shift(pr4_x, pr4_k), pr4_shift_profile(pr4_g, pr4_k),
                         tuple(a+pr4_k if a is not None else None for a in pr4_tx[1:]))
    pr4_y = pr4_cases[(pr4_i + 1) % len(pr4_cases)]
    pr4_gy, pr4_ty = pr4_profile(pr4_y), theta(pr4_y)
    for pr4_left, pr4_right in ((pr4_x, pr4_y), (pr4_y, pr4_x)):
        pr4_gl, pr4_gr = pr4_profile(pr4_left), pr4_profile(pr4_right)
        pr4_tl, pr4_tr = theta(pr4_left), theta(pr4_right)
        pr4_check_update(add(pr4_left, pr4_right), plus_c(pr4_gl, pr4_gr),
                         theta_add(pr4_tl, pr4_tr)[1:])
        pr4_product = mul(pr4_left, pr4_right)
        pr4_check_update(pr4_product, pr4_profile_product(pr4_gl, pr4_gr),
                         theta_mul(pr4_tl, pr4_tr)[1:])
        assert not any(e in pr4_product.w for e, d in pr4_product.o)
        assert all(pr3_U(pr4_product, e, timed=True) ==
                   {pr3_alpha(pr4_product, e, timed=True)} for e in pr4_product.w)
        pr4_counts["product_antichains"] += 1
        pr4_success = theta_guard(pr4_tl, pr4_tr)
        pr4_out = attempt(lambda: temporal(pr4_left, pr4_right))
        assert (pr4_out is not FAIL) == pr4_success
        pr4_strict = observe((lambda z: temporal(z, pr4_right), neg,
                               lambda z: pr3_causal_filter(z, set(), timed=True)), pr4_left, q)
        if pr4_success:
            pr4_check_update(pr4_out,
                             plus_c(push_c(pr4_gl, lambda k: (k[0], k[1], k[2] | pr3_V(pr4_gr))),
                                    pr4_gr), theta_add(pr4_tl, pr4_tr)[1:])
            assert pr4_strict == ("ok", 0)
            pr4_counts["guard_success"] += 1
        else:
            assert pr4_strict is FAIL
            pr4_counts["strict_failures"] += 1
    # A successful temporal step using the shifted target attributes on the right.
    pr4_delay = 0 if pr4_tx[2] is None or pr4_ty[1] is None else pr4_tx[2] - pr4_ty[1] + 1
    pr4_late = time_shift(pr4_y, pr4_delay)
    pr4_glate = pr4_shift_profile(pr4_gy, pr4_delay)
    pr4_check_update(temporal(pr4_x, pr4_late),
                     plus_c(push_c(pr4_g, lambda k: (k[0], k[1], k[2] | pr3_V(pr4_glate))),
                            pr4_glate), theta_add(pr4_tx, theta(pr4_late))[1:])
    pr4_counts["guard_success"] += 1
assert pr4_counts["guard_success"] > 0 and pr4_counts["strict_failures"] > 0

# A common D can include attributes absent on either side, as in the pairwise proof.
for pr4_left, pr4_right in ((pr4_d11x, pr4_d11y), (pr4_d1x, pr4_d1y), (empty, pr4_d5y)):
    pr4_D = frozenset(pr3_alpha(z, e, timed=True) for z in (pr4_left, pr4_right) for e in z.w)
    for pr4_x in (pr4_left, pr4_right):
        pr4_equal(pr4_restore(pr4_D, pr4_read_table(pr4_x, pr4_D)),
                   pr4_profile(pr4_x), "mobius_profiles")

assert q(pr3_causal_filter(pr3_outside, {pr3_alpha(pr3_outside, "old", timed=True)}, timed=True)) == 0
assert "c" not in pr3_d2y.a
assert q(pr3_causal_filter(pr3_d2y, {pr3_alpha(pr3_d2y, "c", timed=True)}, timed=True)) == 1
pr4_B2 = tuple(q(pr3_causal_filter(z, {(origin, 1, pr3_l0, 1)}, timed=True))
                for z in (causal, no_causal))
assert pr4_B2 == (2, 1)
assert (pr4_profile(pr3_d5x), theta(pr3_d5x)[1:3]) == (pr4_profile(pr3_d5y), theta(pr3_d5y)[1:3])
pr4_D10_indegrees = tuple(sorted(sum((e, b) in z.o for e in z.e) for b in ("b1", "b2"))
                           for z in (pr3_d5x, pr3_d5y))
assert pr4_D10_indegrees == ([1, 1], [0, 2])
pr4_c_then_b = tuple(q(pr3_causal_filter(pr3_causal_filter(z, {pr3_alpha(z, "c")}),
                                       {pr3_alpha(z, "b")})) for z in (pr3_d3x, pr3_d3y))
assert pr4_c_then_b == (1, 0)

class pr4_Qstar:
    def __contains__(self, a):
        return a[0] == origin and a[3] == 2

for pr4_x in pr4_cases:
    pr4_direct_q = q(filt(pr4_x, lambda e: (pr4_x.e[e][0], pr4_x.e[e][1]) == (1, origin)))
    pr4_context_q = q(pr3_causal_filter(mul(pr4_x, pr3_U0), pr4_Qstar(), timed=True))
    pr4_equal(pr4_context_q, pr4_direct_q, "q_expression")

for pr4_x in pr4_xi_cases:
    pr4_g = pr4_profile(pr4_x)
    pr4_m, pr4_M = theta(pr4_x)[1:3]
    pr4_equal(pr4_xi_from_profile(pr4_g, pr4_m, pr4_M), pr4_xi_direct(pr4_x), "xi_paths")
    pr4_equal(pr4_forget_time(pr4_g), pr3_profile(pr4_x), "forget_paths")
assert sum(pr4_xi_from_profile(pr4_profile(pr3_U0), 0, 0)[0].values()) == 0
assert sum(a[1] * value for (a, b, upper), value in pr4_profile(pr3_U0).items()) == 2

# Each tuple certifies a strict kernel edge: fine differs, coarse agrees.
pr4_fine = lambda x: (pr4_profile(x), theta(x)[1:3])
pr4_cau = lambda x: (pr3_profile(x), theta(x)[1:])
pr4_src_time = lambda x: (pr3_rho_src(x), theta(x)[1:])
pr4_zero_background = realize({origin: 1, v: -1}, {})
for pr4_x, pr4_y, pr4_f, pr4_c in (
        (causal, no_causal, pr4_fine, pr4_cau),
        (pr3_d2x, pr3_d2y, pr4_cau, pr4_src_time),
        (source7, source8, pr4_src_time, theta),
        (pr3_U0, time_shift(pr3_U0, 1), theta, read_pair),
        (empty, pr4_zero_background, read_pair, lambda x: read_pair(x)[1]),
        (pr3_U0, spatial(pr3_U0, offset=1), lambda x: read_pair(x)[1], q),
        (causal, no_causal, pr4_fine, pr4_xi_direct),
        (pr4_d5x, pr4_d5y, pr4_fine, pr4_xi_direct),
        (pr4_d1x, pr4_d1y, pr4_xi_direct, theta),
        (pr3_U0, time_shift(pr3_U0, 1), pr4_src_time, pr3_rho_src),
        (source7, source8, pr3_rho_src, read_pair),
        (pr4_d1x, pr4_d1y, pr4_xi_direct, pr4_cau),
        (pr4_d1x, pr4_d1y, pr4_xi_direct, pr4_src_time),
        (pr4_d5x, pr4_d5y, pr4_cau, pr4_xi_direct),
        (pr4_d5x, pr4_d5y, pr4_src_time, pr4_xi_direct),
        (pr3_U0, time_shift(pr3_U0, 1), theta, pr3_rho_src),
        (source7, source8, pr3_rho_src, theta)):
    assert pr3_bytes(pr4_f(pr4_x)) != pr3_bytes(pr4_f(pr4_y))
    pr4_equal(pr4_c(pr4_x), pr4_c(pr4_y), "kernel_edges")

print(f"pr4_temporal_causal: random_samples={len(pr4_samples)} cases={len(pr4_cases)} updates={pr4_counts['updates']} endpoint_updates={pr4_counts['endpoint_updates']} earliest_rows={pr4_counts['earliest_rows']} product_antichains={pr4_counts['product_antichains']} guard_success={pr4_counts['guard_success']} strict_failures={pr4_counts['strict_failures']} context_reads={pr4_counts['context_reads']} mobius_profiles={pr4_counts['mobius_profiles']} mobius_coefficients={pr4_counts['mobius_coefficients']} xi_paths={pr4_counts['xi_paths']} forget_paths={pr4_counts['forget_paths']} kernel_edges={pr4_counts['kernel_edges']} D11={pr4_d11_reads[0]},{pr4_d11_reads[1]} D11_Z_times=-2,-1 common_k={pr4_common_k} shifted_probe={pr4_shift_probe[0]},{pr4_shift_probe[1]} fixed_U0={pr4_flat_probe[0]},{pr4_flat_probe[1]} q_expression={pr4_counts['q_expression']} B2={pr4_B2[0]},{pr4_B2[1]} D10_indegrees={pr4_D10_indegrees[0]},{pr4_D10_indegrees[1]} c_then_b={pr4_c_then_b[0]},{pr4_c_then_b[1]}")
# PR5: mixed closure and expression checks; reuse Rich and timed PR3/PR4 helpers.
pr5_counts = {name: 0 for name in (
    "region_updates", "pair_updates", "endpoints", "unselected_parent_pairs",
    "rejected_parent_pairs", "empty_products", "old_endpoint_products",
    "negative_time_inputs", "asymmetric_slots", "context_steps", "context_q",
    "ts_pair_contexts", "mix_contexts", "strict_failures", "rich_equalities",
    "H_cases", "D13_choices", "D14_choices", "bit_maps", "q_expression", "D14_q")}

def pr5_equal(actual, expected, counter):
    assert pr3_bytes(actual) == pr3_bytes(expected), (counter, actual, expected)
    pr5_counts[counter] += 1

class pr5_Set:
    # Fixed mathematical predicates, including infinite regions; no input X here.
    def __init__(self, predicate):
        self.predicate = predicate
    def __contains__(self, item):
        return self.predicate(item)

def pr5_cell(x, e):
    return x.e[e][0], x.e[e][1]

def pr5_region(x, B):
    return filt(x, lambda e: pr5_cell(x, e) in B)

def pr5_pair(x, y, P):
    return restricted_mul(x, y, lambda e, f: (pr5_cell(x, e), pr5_cell(y, f)) in P)

def pr5_region_profile(g, B):
    return push_c(g, lambda row: (row[0], row[1] * int((row[0][3], row[0][0]) in B), row[2]))

def pr5_pair_profile(g, gg, P):
    out = {}
    for (a, b, upper), value in g.items():
        for (aa, bb, uu), other in gg.items():
            joined = pr4_diamond(a, aa)
            selected = b * bb * int(((a[3], a[0]), (aa[3], aa[0])) in P)
            row = (joined, selected, frozenset((joined,)))
            # Coefficients already carry sign. P only changes the selection bit.
            out[row] = out.get(row, 0) + value * other
    return sparse(out)

def pr5_summary(x):
    return pr4_profile(x), *theta(x)[1:3]

def pr5_summary_q(summary):
    return sum(value for (a, b, upper), value in summary[0].items() if b)

def pr5_rich_bytes(x):
    # Complete encoded state, including event IDs, all attributes, order, Omega, A.
    return x.e, x.o, x.w, x.a

def pr5_summary_step(state, step):
    if state is FAIL:
        return FAIL
    g, m, M = state
    op, *args = step
    if op == "N":
        return push_c(g, lambda row: (row[0], 1-row[1], row[2])), m, M
    if op in ("FB", "FS", "FL", "FQ"):
        param, = args
        if op == "FB":
            return pr5_region_profile(g, param), m, M
        def mask(row):
            if op == "FS":
                return row[0][0] in param
            if op == "FL":
                return row[0][2] in param
            return any(a in param for a in row[2])
        return push_c(g, lambda row: (row[0], row[1]*int(mask(row)), row[2])), m, M
    if op == "T":
        k, = args
        return (pr4_shift_profile(g, k), m+k if m is not None else None,
                M+k if M is not None else None)
    slot, parameter, *predicate = args
    left, right = (state, pr5_summary(parameter)) if slot == 0 else (pr5_summary(parameter), state)
    gl, ml, Ml = left
    gr, mr, Mr = right
    if op == "then" and not (Ml is None or mr is None or Ml < mr):
        return FAIL
    if op in ("add", "then"):
        updated_left = gl if op == "add" else push_c(
            gl, lambda row: (row[0], row[1], row[2] | pr3_V(gr)))
        return plus_c(updated_left, gr), lo(ml, mr), hi(Ml, Mr)
    assert op in ("mul", "MP")
    generated_max = gamma(pr4_support_time(gl), pr4_support_time(gr))
    updated = pr4_profile_product(gl, gr) if op == "mul" else pr5_pair_profile(gl, gr, predicate[0])
    return updated, lo(ml, mr), hi(Ml, Mr, generated_max)

def pr5_rich_step(state, step):
    if state is FAIL:
        return FAIL
    op, *args = step
    if op == "N":
        return neg(state)
    if op == "FB":
        return pr5_region(state, args[0])
    if op == "FS":
        return at(state, args[0])
    if op == "FL":
        return filt(state, lambda e: state.e[e][3] in args[0])
    if op == "FQ":
        return pr3_causal_filter(state, args[0], timed=True)
    if op == "T":
        return time_shift(state, args[0])
    slot, parameter, *predicate = args
    left, right = (state, parameter) if slot == 0 else (parameter, state)
    if op == "MP":
        return pr5_pair(left, right, predicate[0])
    return attempt(lambda: {"add": add, "mul": mul, "then": temporal}[op](left, right))

pr5_all = pr5_Set(lambda _: True)
pr5_empty = frozenset()
pr5_column = pr5_Set(lambda cell: cell[1] in {origin, v})
pr5_past = pr5_Set(lambda cell: cell[0] <= -2)
pr5_adjacent = pr5_Set(lambda cell: (cell[1] == origin and cell[0] <= 0)
                                  or (cell[1] == v and cell[0] <= 1))
pr5_gap2 = pr5_Set(lambda cell: (cell[1] == origin and cell[0] <= 0)
                              or (cell[1] == v and cell[0] <= 2))
pr5_single = frozenset({(1, origin)})
pr5_checker = pr5_Set(lambda cell: (cell[0] + cell[1][0]) % 2 == 0)
pr5_regions = (pr5_all, pr5_empty, pr5_column, pr5_past,
               pr5_adjacent, pr5_gap2, pr5_single, pr5_checker)
pr5_asymmetric = pr5_Set(lambda pair: pair[0][0] < pair[1][0])
pr5_position_pair = pr5_Set(lambda pair: pair[0][1] == origin and pair[1][1] == v)
pr5_predicates = (pr5_empty, pr5_all, pr5_asymmetric, pr5_position_pair)
pr5_Qpositive = pr5_Set(lambda a: a[1] == 1)

def pr5_Q(B):
    return pr5_Set(lambda a: (a[3], a[0]) in B)

def pr5_Qstar(B):
    return pr5_Set(lambda a: (a[3]-1, a[0]) in B)

pr5_rng = pr3_Random(2026091005)
pr5_samples = []
for pr5_i in range(64):
    pr5_n = pr5_rng.choice((0, 2, 4, 6))
    pr5_signs = [1]*(pr5_n//2) + [-1]*(pr5_n//2)
    pr5_rng.shuffle(pr5_signs)
    pr5_events = {j: (pr5_rng.randrange(-8, 6), pr5_rng.choice((origin, v, h)), sign,
                      pr5_rng.choice((pr3_l0, pr3_l1, ("pair", pr3_l0, pr3_l1))))
                   for j, sign in enumerate(pr5_signs)}
    pr5_whole = frozenset(pr5_events)
    for pr5_j in range(pr5_rng.randrange(3)):
        pr5_events[("old", pr5_j)] = (pr5_rng.choice((-12, 10)), h, 1, ("leaf", 9))
    pr5_edges = {(a, b) for a in pr5_events for b in pr5_events
                 if pr5_events[a][0] < pr5_events[b][0] and pr5_rng.randrange(4) == 0}
    pr5_chosen = frozenset(e for e in sorted(pr5_whole) if pr5_rng.randrange(2))
    pr5_samples.append(valid(Rich(pr5_events, closure(pr5_edges), pr5_whole, pr5_chosen)))

# D13 is parameterized, with negative-time instances distinct from the old D12.
pr5_D13_reads = []
for pr5_t1, pr5_t2, pr5_p in ((-4, -1, origin), (-2, 3, v), (4, 7, h)):
    pr5_events = {e: (n, pr5_p, sign, pr3_l0)
                  for e, n, sign in zip("abcd", (pr5_t1, pr5_t2, pr5_t1, pr5_t1), (1, 1, -1, -1))}
    pr5_fixed = valid(Rich(pr5_events, frozenset({("a", "b")}), frozenset(pr5_events), frozenset()))
    pr5_D13_family = [replace(pr5_fixed, a=A) for A in pr3_subsets("ab")]
    pr5_B = frozenset({(pr5_t2, pr5_p)})
    pr5_target = frozenset({pr3_alpha(pr5_fixed, "b", timed=True)})
    pr5_reads = tuple(q(pr5_region(x, pr5_B)) for x in pr5_D13_family)
    pr5_causal_reads = tuple(q(pr3_causal_filter(x, pr5_target, timed=True)) for x in pr5_D13_family)
    assert pr5_reads == (0, 0, 1, 1) and pr5_causal_reads == (0, 1, 1, 2)
    pr5_counts["D13_choices"] += len(pr5_D13_family)
    pr5_D13_reads.append((pr5_reads, pr5_causal_reads))

# D14: three individually identifiable positive points, plus three isolated negatives.
pr5_d14_events = {"a": (1, origin, 1, pr3_l0), "b": (2, v, 1, pr3_l0),
                   "c": (0, origin, 1, pr3_l0)}
pr5_d14_events.update({e: (0, origin, -1, pr3_l0) for e in "xyz"})
pr5_d14 = valid(Rich(pr5_d14_events, frozenset({("a", "b")}),
                     frozenset(pr5_d14_events), frozenset()))
pr5_D14_family = [replace(pr5_d14, a=A) for A in pr3_subsets("abc")]
pr5_D14_reads, pr5_D14_causal = [], []
for pr5_x in pr5_D14_family:
    pr5_direct = pr5_region(pr5_x, pr5_gap2)
    pr5_encoded = at(pr3_causal_filter(pr5_x, pr5_Q(pr5_gap2), timed=True), {origin, v})
    assert pr5_direct.a == pr5_x.a & {"b", "c"}
    assert pr5_encoded.a == pr5_x.a
    pr5_D14_reads.append(q(pr5_direct))
    pr5_D14_causal.append(q(pr5_encoded))
    pr5_counts["D14_choices"] += 1
assert pr5_D14_reads == [0, 0, 1, 1, 1, 1, 2, 2]
assert pr5_D14_causal == [0, 1, 1, 1, 2, 2, 2, 3]
assert (pr5_D14_reads[1], pr5_D14_causal[1]) == (0, 1)

pr5_cases = pr5_samples + [empty, pr4_archive_only, pr4_cancel, pr3_outside,
                           pr3_d5x, pr3_d5y, pr3_U0, unit_at(-3)] + pr5_D14_family
for pr5_i, pr5_x in enumerate(pr5_cases):
    assert charge(pr5_x, pr5_x.w) == 0
    pr5_g, pr5_m, pr5_M = pr5_summary(pr5_x)
    if any(event[0] < 0 for event in pr5_x.e.values()):
        pr5_counts["negative_time_inputs"] += 1
    for pr5_B in pr5_regions:
        pr5_out = pr5_region(pr5_x, pr5_B)
        pr5_equal(pr4_profile(pr5_out), pr5_region_profile(pr5_g, pr5_B), "region_updates")
        pr5_equal(theta(pr5_out)[1:], theta(pr5_x)[1:], "endpoints")
        assert (pr5_out.e, pr5_out.o, pr5_out.w) == (pr5_x.e, pr5_x.o, pr5_x.w)
    pr5_y = pr5_cases[(pr5_i + 3) % len(pr5_cases)]
    for pr5_left, pr5_right in ((pr5_x, pr5_y), (pr5_y, pr5_x)):
        for pr5_P in pr5_predicates:
            pr5_out = pr5_pair(pr5_left, pr5_right, pr5_P)
            pr5_expected = pr5_summary_step(pr5_summary(pr5_left), ("MP", 0, pr5_right, pr5_P))
            pr5_equal(pr4_profile(pr5_out), pr5_expected[0], "pair_updates")
            pr5_equal(theta(pr5_out)[1:], (*pr5_expected[1:], pr4_support_time(pr5_expected[0])), "endpoints")
            assert len(pr5_out.w) == len(pr5_left.w)*len(pr5_right.w)
            assert len(pr5_out.e) == len(pr5_left.e)+len(pr5_right.e)+len(pr5_out.w)
            assert not any(e in pr5_out.w for e, d in pr5_out.o)
            assert all(pr3_U(pr5_out, e, timed=True) == {pr3_alpha(pr5_out, e, timed=True)}
                       for e in pr5_out.w)
            for pr5_e, pr5_f in product(pr5_left.w, pr5_right.w):
                pr5_counts["unselected_parent_pairs"] += int(pr5_e not in pr5_left.a or pr5_f not in pr5_right.a)
                pr5_counts["rejected_parent_pairs"] += int((pr5_cell(pr5_left, pr5_e), pr5_cell(pr5_right, pr5_f)) not in pr5_P)
            pr5_counts["empty_products"] += int(not pr5_out.w)
            pr5_counts["old_endpoint_products"] += int(any(
                z.e[e][0] in theta(z)[1:3] for z in (pr5_left, pr5_right) for e in z.e.keys()-z.w))

# A fixed asymmetric P distinguishes both slots; sources remain ordered as well.
pr5_early, pr5_late = unit_at(-3), unit_at(2)
assert (q(pr5_pair(pr5_early, pr5_late, pr5_asymmetric)),
        q(pr5_pair(pr5_late, pr5_early, pr5_asymmetric))) == (1, 0)
for pr5_slot in (0, 1):
    pr5_step = ("MP", pr5_slot, pr5_late, pr5_asymmetric)
    pr5_equal(pr5_summary(pr5_rich_step(pr5_early, pr5_step)),
               pr5_summary_step(pr5_summary(pr5_early), pr5_step), "asymmetric_slots")

# P=empty must retain the full background. Deleting rejected rows predicts 0, not 2.
pr5_empty_pair = pr5_pair(pr3_U0, pr3_U0, pr5_empty)
pr5_empty_g = pr5_pair_profile(pr4_profile(pr3_U0), pr4_profile(pr3_U0), pr5_empty)
pr5_pair_negative_control = q(pr3_causal_filter(neg(pr5_empty_pair), pr5_Qpositive, timed=True))
assert len(pr5_empty_pair.w) == 4 and pr5_empty_g and all(b == 0 for a, b, U in pr5_empty_g)
assert sum(abs(value) for value in pr5_empty_g.values()) == 4
assert pr5_pair_negative_control == 2
pr5_wrong_g = {}  # The deliberately wrong update deletes every rejected pair.
assert pr5_summary_q(pr5_summary_step(pr5_summary_step((pr5_wrong_g, 0, 1), ("N",)),
                                     ("FQ", pr5_Qpositive))) == 0

# All words/parameters are fixed before iterating X. Both binary slots are exercised.
pr5_words = []
for pr5_param in (pr3_U0, unit_at(-20), unit_at(20), pr4_archive_only, empty):
    for pr5_slot in (0, 1):
        pr5_words.append(("ts_pair_contexts", (("FB", pr5_checker), ("MP", pr5_slot, pr5_param, pr5_asymmetric),
                          ("N",), ("T", -2), ("FB", pr5_past), ("add", 1-pr5_slot, pr3_U0),
                          ("mul", pr5_slot, pr3_U0), ("then", 0, unit_at(30)))))
        pr5_words.append(("mix_contexts", (("FQ", pr5_Qpositive), ("FB", pr5_gap2),
                          ("MP", pr5_slot, pr5_param, pr5_position_pair), ("FL", pr5_all),
                          ("T", 1), ("N",), ("FS", {origin, v}), ("FQ", pr5_Qpositive),
                          ("then", pr5_slot, unit_at(30)), ("FB", pr5_empty))))
for pr5_x in pr5_cases:
    for pr5_kind, pr5_word in pr5_words:
        pr5_rich, pr5_state = pr5_x, pr5_summary(pr5_x)
        for pr5_step in pr5_word:
            pr5_rich = pr5_rich_step(pr5_rich, pr5_step)
            pr5_state = pr5_summary_step(pr5_state, pr5_step)
            assert (pr5_rich is FAIL) == (pr5_state is FAIL)
            if pr5_state is not FAIL:
                pr5_equal(pr5_summary(pr5_rich), pr5_state, "context_steps")
                pr5_equal(q(pr5_rich), pr5_summary_q(pr5_state), "context_q")
                assert charge(pr5_rich, pr5_rich.w) == 0
            else:
                pr5_counts["strict_failures"] += 1
        pr5_counts[pr5_kind] += 1
for pr5_slot in (0, 1):
    pr5_failing = ("then", pr5_slot, pr3_U0)
    pr5_suffixes = (("N",), ("FB", pr5_empty), ("FQ", pr5_empty), ("mul", 0, empty),
                    ("mul", 1, empty), ("MP", 0, empty, pr5_empty), ("MP", 1, empty, pr5_empty))
    for pr5_suffix in pr5_suffixes:
        pr5_ops = tuple(lambda z, step=step: pr5_rich_step(z, step) for step in (pr5_failing, pr5_suffix))
        # Also use the original strict evaluator, whose failed temporal raises.
        pr5_temporal_op = (lambda z: temporal(z, pr3_U0)) if pr5_slot == 0 else (lambda z: temporal(pr3_U0, z))
        assert observe((pr5_temporal_op, pr5_ops[1]), pr3_U0, q) is FAIL
        assert pr5_summary_step(pr5_summary_step(pr5_summary(pr3_U0), pr5_failing), pr5_suffix) is FAIL
        pr5_counts["strict_failures"] += 1

# Proposition 53: full Rich equality, never a profile+cardinality substitute for history.
pr5_expressible = ((pr5_all, pr5_all), (pr5_empty, pr5_empty),
                   (pr5_column, {origin, v}), (pr5_past, pr5_all), (pr5_adjacent, {origin, v}))
for pr5_B, pr5_S in pr5_expressible:
    for pr5_x in pr5_cases:
        pr5_out = at(pr3_causal_filter(pr5_x, pr5_Q(pr5_B), timed=True), pr5_S)
        pr5_equal(pr5_rich_bytes(pr5_out), pr5_rich_bytes(pr5_region(pr5_x, pr5_B)), "rich_equalities")

# Exact small family: two positions, arbitrary membership on seven time blocks
# (-infinity,-3], {-2}, {-1}, {0}, {1}, {2}, [3,+infinity).
# Two representatives in each infinite tail expose strict-time witnesses there.
pr5_times = (-4, -3, -2, -1, 0, 1, 2, 3, 4)
pr5_blocks = (0, 0, 1, 2, 3, 4, 5, 6, 6)
def pr5_H(matrix):
    active = [p for p in range(len(matrix[0])) if any(row[p] for row in matrix)]
    return all(not any(matrix[j]) or all(matrix[i][p] for p in active)
               for i in range(len(matrix)) for j in range(i+1, len(matrix)))

pr5_normal_forms = set()
for pr5_S in pr3_subsets(range(2)):
    pr5_normal_forms.add(tuple(tuple(p in pr5_S for p in range(2)) for t in pr5_times))
    for pr5_top in range(-4, 5):
        for pr5_R in pr3_subsets(pr5_S):
            if pr5_R:
                pr5_normal_forms.add(tuple(tuple((t < pr5_top and p in pr5_S) or
                                      (t == pr5_top and p in pr5_R) for p in range(2)) for t in pr5_times))
for pr5_bits in product((False, True), repeat=14):
    pr5_matrix = tuple(tuple(pr5_bits[7*p+block] for p in range(2)) for block in pr5_blocks)
    assert pr5_H(pr5_matrix) == (pr5_matrix in pr5_normal_forms)
    pr5_counts["H_cases"] += 1
for pr5_B, pr5_expected_H in ((pr5_column, True), (pr5_past, True), (pr5_adjacent, True),
                              (pr5_gap2, False), (pr5_single, False), (pr5_empty, True)):
    pr5_matrix = tuple(tuple((t, p) in pr5_B for p in (origin, v, h)) for t in pr5_times)
    assert pr5_H(pr5_matrix) == pr5_expected_H

# Finite bit-map closure is supplementary; the proof excludes arbitrary finite words.
for pr5_size in (2, 3):
    pr5_identity = (0, 1)*pr5_size
    pr5_masks = {mask for mask in product((0, 1), repeat=pr5_size) if mask[0] >= mask[1]}
    if pr5_size == 3:
        pr5_masks |= {mask for mask in product((0, 1), repeat=3) if mask[0] == mask[2]}
    pr5_maps, pr5_pending = {pr5_identity}, [pr5_identity]
    while pr5_pending:
        pr5_map = pr5_pending.pop()
        pr5_next = {tuple(1-z for z in pr5_map)} | {
            tuple(z*mask[i//2] for i, z in enumerate(pr5_map)) for mask in pr5_masks}
        for pr5_map1 in pr5_next-pr5_maps:
            pr5_maps.add(pr5_map1)
            pr5_pending.append(pr5_map1)
    assert (0, 0)+(0, 1)*(pr5_size-1) not in pr5_maps
    assert all(f[:2] == (0, 1) for f in pr5_maps if f[2:] == (0, 1)*(pr5_size-1))
    pr5_counts["bit_maps"] += len(pr5_maps)

# Proposition 54: fixed lower bounds, no upper-bound or finite-region assumption.
pr5_bounded_regions = ((pr5_empty, -5), (pr5_single, 1),
    (frozenset({(-5, origin), (-2, v), (3, h)}), -5),
    (pr5_Set(lambda cell: cell[0] >= -4 and cell[1] in {origin, v}), -4),
    (pr5_Set(lambda cell: cell[0] >= -6 and (cell[0]+cell[1][0]) % 2 == 0), -6))
for pr5_B, pr5_k0 in pr5_bounded_regions:
    for pr5_k in (pr5_k0-1, pr5_k0-2, pr5_k0-7):
        pr5_parameter, pr5_target = time_shift(pr3_U0, pr5_k), pr5_Qstar(pr5_B)
        for pr5_x in pr5_cases:
            pr5_equal(q(pr3_causal_filter(mul(pr5_x, pr5_parameter), pr5_target, timed=True)),
                       q(pr5_region(pr5_x, pr5_B)), "q_expression")
pr5_bad_B = frozenset({(0, origin)})
pr5_bad_x = unit_at(-1)
pr5_bad_bound = (q(pr5_region(pr5_bad_x, pr5_bad_B)),
                 q(pr3_causal_filter(mul(pr5_bad_x, pr3_U0), pr5_Qstar(pr5_bad_B), timed=True)))
assert pr5_bad_bound == (0, 1)

# D14 is unbounded below, so its positive q expression is a separate direct check.
pr5_D14_Q = pr5_Set(lambda a: (a[0] == origin and a[3] == 1)
                              or (a[0] == v and a[3] in {1, 2, 3}))
for pr5_x in pr5_cases:
    pr5_equal(q(pr3_causal_filter(mul(pr5_x, pr3_U0), pr5_D14_Q, timed=True)),
               q(pr5_region(pr5_x, pr5_gap2)), "D14_q")
assert all(pr5_counts[k] > 0 for k in pr5_counts)
print("pr5_mixed_closure: " + " ".join(f"{name}={value}" for name, value in pr5_counts.items())
      + f" seed=2026091005 random_samples={len(pr5_samples)} cases={len(pr5_cases)}"
      + " P_empty_Omega=4 P_empty_Gamma=nonempty P_empty_N_positive=2 wrong_deleted_rows=0"
      + " D13=0,0,1,1/0,1,1,2 D14=0,0,1,1,1,1,2,2/0,1,1,1,2,2,2,3 bad_k=0,1")

# PR6: fixed seed; finite experiments supplement the arbitrary-context proofs.
pr6_rng = pr3_Random(2026091006)
pr6_counts = {}

def pr6_equal(actual, expected, name):
    assert pr3_bytes(actual) == pr3_bytes(expected), (name, actual, expected)
    pr6_counts[name] = pr6_counts.get(name, 0) + 1

def pr6_pair(x, y, P):
    return restricted_mul(x, y, lambda e, f:
        (pr3_alpha(x, e, True), pr3_alpha(y, f, True)) in P)

def pr6_push(g, gg, rule):
    out = {}
    for row, value in g.items():
        for other, coefficient in gg.items():
            a = pr4_diamond(row[0], other[0])
            target = (a, row[1]*other[1]*int(rule(row, other)), frozenset({a}))
            out[target] = out.get(target, 0) + value*coefficient
    return sparse(out)

def pr6_step(state, step, rich=False):
    if state is FAIL or step[0] != "MAP":
        return (pr5_rich_step if rich else pr5_summary_step)(state, step)
    _, slot, parameter, P = step
    if rich:
        x, y = (state, parameter) if slot == 0 else (parameter, state)
        return pr6_pair(x, y, P)
    x, y = (state, pr5_summary(parameter)) if slot == 0 else (pr5_summary(parameter), state)
    g = pr6_push(x[0], y[0], lambda row, other: (row[0], other[0]) in P)
    return g, lo(x[1], y[1]), hi(x[2], y[2], gamma(pr4_support_time(x[0]), pr4_support_time(y[0])))

def pr6_expression(x, B, k):
    Q = pr5_Set(lambda a: a[3] >= k+1 and (a[3]-1, a[0]) in B)
    return pr3_causal_filter(mul(x, time_shift(pr3_U0, k)), Q, True)

# Tail predicates are fixed before traversing the 64 random and 16 directed inputs.
pr6_tails = [(pr5_gap2, 1), (pr5_empty, -3), (pr5_all, 2)]
for pr6_i in range(24):
    pr6_c = pr6_rng.randrange(-6, 5)
    pr6_S = frozenset(p for p in (origin, v, h) if pr6_rng.randrange(2))
    pr6_d = pr6_rng.randrange(2, 6)
    pr6_R = frozenset(r for r in range(pr6_d) if pr6_rng.randrange(2))
    pr6_B = pr5_Set(lambda cell, c=pr6_c, S=pr6_S, d=pr6_d, R=pr6_R:
        cell[1] in S if cell[0] < c else (cell[0]+sum(cell[1])) % d in R)
    pr6_tails.append((pr6_B, pr6_c))
for pr6_B, pr6_c in pr6_tails:
    for pr6_k in (pr6_c-1, pr6_c-4):
        for pr6_x in pr5_cases:
            pr6_equal(q(pr6_expression(pr6_x, pr6_B, pr6_k)),
                      q(pr5_region(pr6_x, pr6_B)), "tail_q")
pr6_controls = []
for pr6_d in (2, 3, 5):
    pr6_controls.append((pr5_Set(lambda cell, d=pr6_d: cell[0] % d == 0),
                         origin, -2*pr6_d, -2*pr6_d+1))
pr6_drift = pr5_Set(lambda cell: cell[1][1:] == (0, 0) and cell[1][0] >= 0
                    and cell[0] <= -cell[1][0])
pr6_controls.append((pr6_drift, (3, 0, 0), -3, -2))
for pr6_B, pr6_p, pr6_t, pr6_tt in pr6_controls:
    pr6_inputs = [replace(unit_at(t), e={e: (n, pr6_p, s, r)
                   for e, (n, p, s, r) in unit_at(t).e.items()}) for t in (pr6_t, pr6_tt)]
    pr6_equal(tuple(q(mul(x, pr3_U0)) for x in pr6_inputs), (1, 1), "collapse_controls")
    pr6_equal(tuple(q(pr5_region(x, pr6_B)) for x in pr6_inputs), (1, 0), "target_controls")
    pr6_equal(*(pr4_profile(mul(x, pr3_U0)) for x in pr6_inputs), "collapsed_profiles")

# Lemma 4: pull prefix witnesses back by cumulative shifts; c never depends on p.
def pr6_saturated(prefix, factor, p):
    witnesses, J = [], 0
    for step in prefix:
        if step[0] == "T":
            J += step[1]
        if step[0] == "FQ" and step[1]:
            witnesses.append(pr4_shift_attr(sorted(step[1], key=repr)[0], -J))
    c = min([0] + [a[3] for a in witnesses]
            + ([min(factor.e[e][0] for e in factor.w)-J] if factor is not None and factor.w else []))
    times = (c-2, c-1)
    common = {("d", i): (a[3], a[0], a[1], a[2]) for i, a in enumerate(witnesses)}
    balance = 1 + sum(a[1] for a in witnesses)
    common.update({("n", i): (0, origin, -1 if balance > 0 else 1, pr3_l0)
                   for i in range(abs(balance))})
    whole = frozenset(common) | {"e"}
    extremes = list(times) + [event[0] for event in common.values()]
    common.update({"low": (min(extremes)-1, origin, 1, pr3_l0),
                   "high": (max(extremes)+1, origin, 1, pr3_l0)})
    edges = frozenset(("e", ("d", i)) for i in range(len(witnesses)))
    return [valid(Rich(dict(common, e=(t, p, 1, pr3_l0)), edges, whole, frozenset({"e"}))) for t in times]

for pr6_i in range(36):
    pr6_Q = frozenset((pr6_rng.choice((origin, v)), pr6_rng.choice((-1, 1)),
                      pr3_l0, pr6_rng.randrange(-3, 5)) for _ in range(pr6_i % 4))
    pr6_prefix = [("T", pr6_rng.randrange(-3, 4)), ("FQ", pr6_Q), ("N",),
                  ("add", pr6_i % 2, unit_at(2)), ("FS", {origin, v}),
                  ("T", -1), ("FL", {pr3_l0}), ("FQ", pr6_Q), ("then", 0, empty)]
    pr6_rng.shuffle(pr6_prefix)
    pr6_factor = None if pr6_i % 3 == 0 else (empty if pr6_i % 3 == 1 else unit_at(-4))
    pr6_word = pr6_prefix + ([] if pr6_factor is None else [("mul", pr6_i % 2, pr6_factor)])
    pr6_word += [("N",), ("add", 1, pr3_U0), ("FQ", pr5_Qpositive), ("T", 2)]
    for pr6_p in (origin, v, (7, -2, 1)):
        pr6_inputs = pr6_saturated(pr6_prefix, pr6_factor, pr6_p)
        pr6_equal(theta(pr6_inputs[0])[1:3], theta(pr6_inputs[1])[1:3], "saturation_endpoints")
        pr6_outputs = []
        for pr6_x in pr6_inputs:
            assert charge(pr6_x, pr6_x.w) == 0
            for pr6_step0 in pr6_word:
                pr6_x = pr5_rich_step(pr6_x, pr6_step0)
                assert pr6_x is not FAIL
            pr6_outputs.append(q(pr6_x))
        pr6_equal(*pr6_outputs, "saturation_q")
        pr6_name = "saturation_no_product" if pr6_factor is None else (
            "saturation_empty_factor" if not pr6_factor.w else "saturation_product")
        pr6_counts[pr6_name] = pr6_counts.get(pr6_name, 0) + 1

# A periodic query can see early times; the successor witness removes that difference.
pr6_even_Q = pr5_Set(lambda a: a[3] % 2 == 0)
pr6_sat = pr6_saturated([("FQ", {(origin, 1, pr3_l0, 0)})], pr3_U0, origin)
pr6_equal(tuple(q(pr3_causal_filter(x, pr6_even_Q, True)) for x in pr6_sat),
          (1, 1), "periodic_saturation")
pr6_equal(tuple(q(pr3_causal_filter(replace(x, o=frozenset()), pr6_even_Q, True)) for x in pr6_sat),
          (1, 0), "unsaturated_control")
pr6_equal(*(pr5_summary(mul(x, pr3_U0)) for x in pr6_sat), "first_product_fiber")

# Attribute pairing: ordered predicates, both slots, full background, and suffixes.
pr6_asym = pr5_Set(lambda pair: pair[0][3] < pair[1][3])
pr6_signed_source = pr5_Set(lambda pair: pair[0][1] != pair[1][1]
                           and pair[0][2] == pr3_l0)
for pr6_i, pr6_x in enumerate(pr5_cases):
    pr6_y = pr5_cases[(pr6_i+3) % len(pr5_cases)]
    pr6_attrs = sorted(pr3_V(pr4_profile(pr6_x)) | pr3_V(pr4_profile(pr6_y)), key=repr)
    pr6_P = frozenset(pair for pair in product(pr6_attrs, repeat=2) if pr6_rng.randrange(2))
    for pr6_P0 in (pr6_P, pr6_asym, pr6_signed_source, pr5_all, pr5_empty):
        for pr6_slot in (0, 1):
            pr6_step0 = ("MAP", pr6_slot, pr6_y, pr6_P0)
            pr6_rich = pr6_step(pr6_x, pr6_step0, True)
            pr6_state = pr6_step(pr5_summary(pr6_x), pr6_step0)
            pr6_equal(pr5_summary(pr6_rich), pr6_state, "pair_push")
            assert len(pr6_rich.w) == len(pr6_x.w)*len(pr6_y.w)
            pr6_counts["empty_products"] = pr6_counts.get("empty_products", 0) + int(not pr6_rich.w)
            pr6_counts["old_archives"] = pr6_counts.get("old_archives", 0) + int(bool(pr6_x.e.keys()-pr6_x.w or pr6_y.e.keys()-pr6_y.w))
            pr6_counts["negative_inputs"] = pr6_counts.get("negative_inputs", 0) + int(any(t < 0 for z in (pr6_x, pr6_y) for t, p, s, r in z.e.values()))
            pr6_counts["unselected_parents"] = pr6_counts.get("unselected_parents", 0) + sum(e not in pr6_x.a or f not in pr6_y.a for e, f in product(pr6_x.w, pr6_y.w))
            for pr6_suffix in (("N",), ("FQ", pr5_Qpositive), ("FB", pr5_past)):
                pr6_rich = pr5_rich_step(pr6_rich, pr6_suffix)
                pr6_state = pr5_summary_step(pr6_state, pr6_suffix)
                pr6_equal(pr5_summary(pr6_rich), pr6_state, "pair_suffix")
    for pr6_P0 in pr5_predicates:
        pr6_lift = pr5_Set(lambda pair, P=pr6_P0:
            ((pair[0][3], pair[0][0]), (pair[1][3], pair[1][0])) in P)
        pr6_equal(pr5_rich_bytes(pr6_pair(pr6_x, pr6_y, pr6_lift)),
                  pr5_rich_bytes(pr5_pair(pr6_x, pr6_y, pr6_P0)), "pullback_encoding")
pr6_words = [[("FQ", pr5_Qpositive), ("MAP", slot, param, pr6_signed_source), ("N",),
              ("FB", pr5_gap2), ("MP", 1-slot, pr3_U0, pr5_asymmetric),
              ("T", -2), ("then", slot, unit_at(15)), ("N",), ("FQ", pr5_empty)]
             for param in (empty, pr4_archive_only, pr3_U0) for slot in (0, 1)]
for pr6_word in pr6_words:
    for pr6_x in pr5_cases:
        pr6_rich, pr6_state = pr6_x, pr5_summary(pr6_x)
        for pr6_step0 in pr6_word:
            pr6_rich, pr6_state = pr6_step(pr6_rich, pr6_step0, True), pr6_step(pr6_state, pr6_step0)
            assert (pr6_rich is FAIL) == (pr6_state is FAIL)
            if pr6_state is FAIL:
                pr6_counts["strict_failures"] = pr6_counts.get("strict_failures", 0) + 1
            else:
                pr6_equal(pr5_summary(pr6_rich), pr6_state, "mixed_summary")
                pr6_equal(q(pr6_rich), pr5_summary_q(pr6_state), "mixed_q")

# D15 and the fiber criterion; D10 has equal edge counts and is only a control.
pr6_events = {e: (t, origin, sign, pr3_l0)
              for e, t, sign in (("e", 0, 1), ("b1", 1, 1), ("b2", 1, 1),
                                 ("n1", 0, -1), ("n2", 0, -1), ("n3", 0, -1))}
pr6_X = valid(Rich(pr6_events, frozenset({("e", "b1")}), frozenset(pr6_events),
                  frozenset({"e", "b1", "b2"})))
pr6_Y = valid(replace(pr6_X, o=pr6_X.o | {("e", "b2")}))
def pr6_D(x):
    return restricted_mul(x, x, lambda e, f: (e, f) in x.o)

def pr6_J(x, y, rule):
    result = {}
    for e, f in product(x.a, y.a):
        if rule(e, f):
            a = pr4_diamond(pr3_alpha(x, e, True), pr3_alpha(y, f, True))
            result[a] = result.get(a, 0) + x.e[e][2]*y.e[f][2]
    return sparse(result)

pr6_equal(pr5_summary(pr6_X), pr5_summary(pr6_Y), "D15_fiber")
pr6_equal((q(pr6_D(pr6_X)), q(pr6_D(pr6_Y))), (1, 2), "D15_q")
pr6_equal((q(pr6_D(pr3_d5x)), q(pr6_D(pr3_d5y))), (2, 2), "D10_control")
assert pr6_J(pr6_X, pr6_X, lambda e, f: (e, f) in pr6_X.o) != pr6_J(
    pr6_Y, pr6_Y, lambda e, f: (e, f) in pr6_Y.o)
for pr6_Q in (frozenset(), {pr3_alpha(pr6_X, "b1", True)}, pr5_Qpositive):
    for pr6_z in (pr6_X, pr6_Y):
        pr6_rule = lambda e, f: any(a in pr6_Q for a in pr3_U(pr6_z, e, True))
        pr6_direct = restricted_mul(pr6_z, pr3_U0, pr6_rule)
        pr6_expected = pr6_push(pr4_profile(pr6_z), pr4_profile(pr3_U0),
                                lambda row, other: any(a in pr6_Q for a in row[2]))
        pr6_equal(pr4_profile(pr6_direct), pr6_expected, "U_rule_push")
        pr6_equal(pr6_J(pr6_z, pr3_U0, pr6_rule), {a: n for (a, b, U), n
                    in pr6_expected.items() if b}, "J_positive")
    pr6_equal(pr6_J(pr6_X, pr3_U0, lambda e, f: any(a in pr6_Q for a in pr3_U(pr6_X, e, True))),
              pr6_J(pr6_Y, pr3_U0, lambda e, f: any(a in pr6_Q for a in pr3_U(pr6_Y, e, True))), "J_fiber")
for pr6_z in (pr6_X, pr6_Y, pr3_U0, add(pr3_U0, pr3_U0)):
    pr6_equal(pr4_profile(restricted_mul(pr6_z, pr3_U0, lambda e, f: len(pr3_U(pr6_z, e, True)) > 1)),
              pr6_push(pr4_profile(pr6_z), pr4_profile(pr3_U0), lambda row, other: len(row[2]) > 1), "U_size_rule")
    pr6_parity = (sum(abs(n) for n in pr4_profile(pr6_z).values())//2) % 2
    pr6_equal(pr4_profile(restricted_mul(pr6_z, pr3_U0, lambda e, f: (len(pr6_z.w)//2) % 2)),
              pr6_push(pr4_profile(pr6_z), pr4_profile(pr3_U0), lambda row, other: pr6_parity), "global_rule")
pr6_equal(set(pr4_profile(pr3_U0)), set(pr4_profile(add(pr3_U0, pr3_U0))), "same_local_rows")
pr6_q_only = []
for pr6_z in (pr6_X, pr6_Y):
    pr6_pairs = [(e, f) for e, f in product(pr6_z.a, pr3_U0.a) if pr6_z.e[e][2]*pr3_U0.e[f][2] == 1]
    pr6_pairs.sort(key=lambda ef: (pr4_diamond(pr3_alpha(pr6_z, ef[0], True), pr3_alpha(pr3_U0, ef[1], True))[3], repr(ef)))
    pr6_pair0 = pr6_pairs[0 if len(pr6_z.o) % 2 else -1]
    pr6_q_only.append(restricted_mul(pr6_z, pr3_U0, lambda e, f: (e, f) == pr6_pair0))
pr6_equal(tuple(q(z) for z in pr6_q_only), (1, 1), "q_only_control")
assert pr4_profile(pr6_q_only[0]) != pr4_profile(pr6_q_only[1])

# Proposition 57: five independent conditions, then an event realization.
def pr6_conditions(g, m, M):
    rows = list(sparse(g))
    return (all(a[1]*g[a, b, U] > 0 for a, b, U in rows),
            sum(g.values()) == 0,
            all(a in U and all(v[3] > a[3] for v in U-{a}) for a, b, U in rows),
            all(any(aa == v and V <= U for aa, bb, V in rows) for a, b, U in rows for v in U-{a}),
            ((m is None and M is None) or (m is not None and M is not None and m <= M))
            if not rows else (m is not None and M is not None and all(m <= a[3] <= M for a, b, U in rows)))

def pr6_realize(g, m, M):
    assert all(pr6_conditions(g, m, M))
    assigned = [row for row, coefficient in g.items() for _ in range(abs(coefficient))]
    events = {i: (a[3], a[0], a[1], a[2]) for i, (a, b, U) in enumerate(assigned)}
    whole = frozenset(events)
    chosen = frozenset(i for i, (a, b, U) in enumerate(assigned) if b)
    edges = frozenset((i, j) for i, (a, b, U) in enumerate(assigned)
                      for j, (aa, bb, V) in enumerate(assigned) if a[3] < aa[3] and V <= U)
    if m is not None:
        events.update({"low": (m, origin, 1, pr3_l0), "high": (M, origin, 1, pr3_l0)})
    return valid(Rich(events, edges, whole, chosen))

for pr6_i in range(64):
    pr6_g = {}
    for pr6_n in reversed(range(pr6_rng.randrange(7))):
        pr6_a = (pr6_rng.choice((origin, v)), pr6_rng.choice((-1, 1)), pr3_l0, pr6_n-4)
        pr6_U = frozenset({pr6_a}).union(*(U for a, b, U in pr6_g if pr6_rng.randrange(2)))
        pr6_g[pr6_a, pr6_rng.randrange(2), pr6_U] = pr6_a[1]*pr6_rng.randrange(1, 4)
    pr6_total = sum(pr6_g.values())
    if pr6_total:
        pr6_a = (h, -1 if pr6_total > 0 else 1, ("leaf", 99), 3)
        pr6_g[pr6_a, 0, frozenset({pr6_a})] = -pr6_total
    pr6_m, pr6_M = (-6, 5) if pr6_g or pr6_i % 2 else (None, None)
    pr6_equal(pr5_summary(pr6_realize(pr6_g, pr6_m, pr6_M)), (pr6_g, pr6_m, pr6_M), "image_roundtrip")

# Exhaust both formal target sets/selection bits and all forward-edge graphs.
for pr6_times in ((0, 1, 2, 3), (0, 0, 1, 1)):
    pr6_e = {i: (t, origin, 1 if i < 2 else -1, pr3_l0) for i, t in enumerate(pr6_times)}
    pr6_base = Rich(pr6_e, frozenset(), frozenset(pr6_e), frozenset())
    pr6_D0 = [pr3_alpha(pr6_base, i, True) for i in range(4)]
    pr6_actual, pr6_accepted = set(), set()
    for pr6_edges in pr3_subsets((i, j) for i, j in product(range(4), repeat=2) if pr6_times[i] < pr6_times[j]):
        for pr6_A in pr3_subsets(range(4)):
            pr6_z = valid(replace(pr6_base, o=closure(pr6_edges), a=pr6_A))
            pr6_actual.add(pr3_bytes(pr4_profile(pr6_z)).decode())
            pr6_counts["enumerated_states"] = pr6_counts.get("enumerated_states", 0) + 1
    pr6_options = [[frozenset({a}) | U for U in pr3_subsets({v0 for v0 in pr6_D0 if v0[3] > a[3]})] for a in pr6_D0]
    for pr6_Us in product(*pr6_options):
        for pr6_bits in product((0, 1), repeat=4):
            pr6_g = {}
            for pr6_a, pr6_b, pr6_U in zip(pr6_D0, pr6_bits, pr6_Us):
                pr6_row = (pr6_a, pr6_b, pr6_U)
                pr6_g[pr6_row] = pr6_g.get(pr6_row, 0) + pr6_a[1]
            pr6_ok = all(pr6_conditions(pr6_g, min(pr6_times), max(pr6_times)))
            pr6_equal(pr6_ok, pr3_bytes(pr6_g).decode() in pr6_actual, "formal_membership")
            if pr6_ok:
                pr6_accepted.add(pr3_bytes(pr6_g).decode())
                pr6_equal(pr4_profile(pr6_realize(pr6_g, min(pr6_times), max(pr6_times))), pr6_g, "enumerated_roundtrip")
    pr6_equal(pr6_actual, pr6_accepted, "image_sets")
    pr6_counts["distinct_actual_profiles"] = pr6_counts.get("distinct_actual_profiles", 0) + len(pr6_actual)
pr6_a, pr6_b, pr6_c = [(origin, s, pr3_l0, t) for t, s in ((0, 1), (1, 1), (2, -1))]
pr6_D16 = {(pr6_a, 1, frozenset({pr6_a, pr6_b})): 1,
           (pr6_b, 1, frozenset({pr6_b, pr6_c})): 1, (pr6_c, 0, frozenset({pr6_c})): -2}
pr6_equal(pr6_conditions(pr6_D16, 0, 2), (True, True, True, False, True), "D16_conditions")
for pr6_m, pr6_M, pr6_ok in ((None, None, True), (-2, -2, True), (-3, 4, True),
                             (None, 0, False), (0, None, False), (1, 0, False)):
    pr6_equal(all(pr6_conditions({}, pr6_m, pr6_M)), pr6_ok, "empty_endpoint_branches")
    if pr6_ok:
        pr6_equal(pr5_summary(pr6_realize({}, pr6_m, pr6_M)), ({}, pr6_m, pr6_M), "empty_realizations")
assert all(value > 0 for value in pr6_counts.values())
print("pr6_expressibility_pairing: " + " ".join(f"{k}={v0}" for k, v0 in pr6_counts.items())
      + " seed=2026091006 Tail_families=27 random_inputs=64 cases=80"
      + " periodic_and_drift=1,1/1,0 D15=1,2 D10=2,2 D16=1,1,1,0,1")

print("ALL_FINITE_CHECKS_PASSED")
```

**原基线收据说明（PR1 追加）。** 紧接的“本次运行”及其输出是原版本的历史记录；扩充后的实际重跑与新增计数见 §17 的 PR1 核验收据，不以这份旧输出代替本轮运行。

本次运行退出码为 `0`，实际标准输出如下：

```text
balanced_states=105 pair_checks=11025
worked_product: q=1 archive=14 whole=8 selected=3 causal_pairs=27
parallel_pairs=3 temporal_pairs=11 both_q=2
zero_products: (archive,whole,selected,q)=(4,0,0,0),(14,8,6,0)
raw_laws: sum_with_negative_archive=4 unit_product_archive=8 associativity_archives=28,32
filters: spatial=(1,0) source=(2,1) causal=(2,1); restricted_q=0 omitted_charge=1
transport: balanced_added_charge=0 unbalanced_defect=1; bin_complement=(0,-1); image_defect_and_cycle=confirmed
coordinates: linear_and_time_translation_commute=True spatial_translation_commutes=False
rationals: sum=-1 product=-3/4 negative=-1/2 division=-1/3 zero_divisor=rejected
inverse_prefixes: (0,1,1,1)->(0,1,1,1); (1,1/2,1/3,1/4)->(1,2,3,4)
sources: shared_difference={0} shared_square={1,4}; independent_difference={-1,0,1} independent_product={1,2,4}
ALL_FINITE_CHECKS_PASSED
```

核验解释：这些读数仅覆盖上述有限域及具名例子。它们不证明任意图、任意 Cauchy 序列或 ZFC 的一致性，也不是 Lean 内核检查。新文档之外未改动任何仓库文件；完整仓库准入检查、独立数学评审和 PR 交付是调用方的后续步骤。

<a id="pr1-observation"></a>

## 14. PR1 增补 A：严格观察与最大保域同余

本节为 §9 命题 11 增加“允许哪些后续操作”的参数。原命题 1–15 不改；一般结论不把档案历史压成数值，也不预设历史同构与任意新观察之间的包含关系。

**定义 16（部分签名与全部一孔上下文）。** 固定一个集合 $X$、一个集合签名 $\Sigma$。每个符号 $f\in\Sigma$ 指定一个有限元数 $n_f\in\mathbb N$ 和一个确定部分函数 $f:D_f\subseteq X^{n_f}\to X$。固定总读数 $q:X\to Q$，其中 $Q$ 是集合，**不要求 $q$ 满射**。上下文族 $\operatorname{Ctx}_\Sigma$ 恰由以下生成元及有限复合生成：恒等孔 $\square$；对每个 $n_f\ge1$、每个槽位 $1\le i\le n_f$ 和任意固定参数 $a_j\in X\ (j\ne i)$，基本一孔部分函数

$$
x\longmapsto f(a_1,\ldots,a_{i-1},x,a_{i+1},\ldots,a_{n_f}).
$$

复合 $C\circ B$ 仅在 $B(x)$ 有定义且 $C(B(x))$ 有定义时求值；失败严格传播，不把失败当作 $X$ 的元素供后续操作处理。零元符号没有可放孔的槽位，也不增加一孔生成元。这里的固定参数是**全部 $X$ 中的参数**，不限于常数符号可命名的值；上下文不含额外探针、不截断复合深度，不自动增加复制孔或检查语法编码的机制。每个上下文本身仍是有限的。因为签名、参数空间及有限字符串空间都是集合，这个上下文族也是集合。

观察值域取不交并 $Q_\bot=(\{1\}\times Q)\sqcup\{\bot\}$；即使 $Q$ 自己包含一个名为“失败”的值，它也不等于新标签 $\bot$。定义

$$
\operatorname{obs}_C(x)=
\begin{cases}(1,q(C(x))),&C(x)\text{ 有定义},\\ \bot,&C(x)\text{ 无定义},\end{cases}
\qquad
x\approx_\Sigma y\ \Longleftrightarrow\quad
\forall C\in\operatorname{Ctx}_\Sigma,\quad
\operatorname{obs}_C(x)=\operatorname{obs}_C(y).
$$

**定义 17（强保域同余）。** $\theta$ 是 $X$ 上的等价关系；对任意 $f\in\Sigma$ 及逐坐标 $x_j\mathrel\theta y_j$ 的两元组 $\boldsymbol x,\boldsymbol y\in X^{n_f}$，要求

$$
\boldsymbol x\in D_f\iff\boldsymbol y\in D_f,
\qquad
\boldsymbol x,\boldsymbol y\in D_f\Longrightarrow
f(\boldsymbol x)\mathrel\theta f(\boldsymbol y).
\tag{SC}
$$

第一项保留整个定义域，不能删成“共同有定义时比较”。零元情形只有同一个空元组，条件自动成立。记 $\ker q=\{(x,y):q(x)=q(y)\}$；关系按集合包含排序，“最大”指包含所有符合条件的关系。

**命题 16（观察等价的最大性，repo-derived）。** $\approx_\Sigma$ 是 $\ker q$ 内最大的强保域同余。

**证明。** 它是各总函数 $\operatorname{obs}_C:X\to Q_\bot$ 的核的交，故是等价关系；恒等孔使它包含于 $\ker q$。先只替换一个槽位，写基本上下文为 $B$。若 $x\approx_\Sigma y$，则 $\operatorname{obs}_B(x)=\operatorname{obs}_B(y)$。严格失败与所有正常值分离，故 $B(x),B(y)$ 同时有定义或同时无定义。若二者有定义，对任意 $C\in\operatorname{Ctx}_\Sigma$，$C\circ B$ 仍属该族，于是
$\operatorname{obs}_C(B(x))=\operatorname{obs}_C(B(y))$，即 $B(x)\approx_\Sigma B(y)$。

对逐坐标等价的 $n_f$ 元输入，从 $\boldsymbol x$ 到 $\boldsymbol y$ 每次只替换一个坐标，其余坐标取这一步实际的固定参数。上段使定义性沿有限链相同；有定义时输出也沿链等价，传递性给出 (SC)。这一步正是需要所有槽位与全部固定参数的地方。

反之，设 $\theta\subseteq\ker q$ 满足 (SC)。对上下文的生成作归纳：恒等孔保持 $\theta$；基本上下文由 (SC) 保域，并在域内保持 $\theta$。复合时，若内层失败，两侧均严格失败；否则内层输出相关，外层由归纳假设同域且在域内输出相关。最后用 $\theta\subseteq\ker q$，两侧正常读数也相同。因此 $x\mathrel\theta y$ 蕴含每个上下文的观察相同，即 $\theta\subseteq\approx_\Sigma$。全过程没有使用满射或挑选 $Q$ 中未被命中的值。证毕。

**命题 17（扩签名只能细化）。** 在同一 $X,q$ 上，若 $\Sigma\subseteq\Sigma'$ 且旧符号的函数和定义域保持原样，则 $\approx_{\Sigma'}\subseteq\approx_\Sigma$。

**证明。** 原基本上下文及其有限复合全在扩充族内。对较大族全部观察相等，当然对原族相等。只需此集合包含，不涉及计算能力的比较。证毕。

**反例 A1（只比较共同有定义的上下文）。** 取 $X=\{a,b\}$，$Q=\{0,1\}$，$q$ 恒为 $0$，$f$ 仅在 $a$ 有定义且 $f(a)=a$。如果忽略单侧失败，$a,b$ 在每个共同有效上下文中的读数都为 $0$，错误关系把它们识别；但 $f$ 的定义域 $\{a\}$ 不饱和。正确观察在 $f(\square)$ 上是 $(1,0)$ 与 $\bot$。这也同时示范非满射读数完全合法。若再将失败与正常的 $0$ 混同，这个区别又会消失。

**反例 A2（任何固定有限深度都可能不足）。** 给任意 $k\ge0$，取两条互异状态链 $a_0,\ldots,a_{k+1}$ 和 $b_0,\ldots,b_{k+1}$，一个总一元操作 $f$ 各自向下一项移动、在终点停留。令 $q(a_{k+1})=1$，其余读数为 $0$。深度至多 $k$ 的上下文恰为 $\square,f,\ldots,f^k$，均不能区别 $a_0,b_0$；$f^{k+1}$ 却给 $1,0$。而 $f(a_0),f(b_0)$ 已可被深度 $k$ 区别，所以截断关系还可能不保运算。无限量化的是任意有限深度，并非允许一个无限复合上下文。

**反例 A3（遗漏槽位、参数或偷加探针）。** 取 $X=\{0,1,2\}$，$q(0)=q(1)=0,q(2)=1$，总二元操作 $f(s,t)$ 仅在 $(s,t)=(1,2)$ 时取 $2$，其余取 $0$。若只允许孔在第二槽，$0,1$ 的任何非空复合第一步都输出 $0$，永远不可区分；合法的第一槽上下文 $f(\square,2)$ 却给 $0,2$，观察为 $0,1$。即使开放两个槽位，若只许固定参数 $0,1$，仍有同样漏判：首次作用于 $0,1$ 的结果均为 $0$，不能形成区分。另取同一 $X,q$ 但空签名，此时 $0\approx_\varnothing1$。额外操作 $g(0)=0,g(1)=g(2)=2$ 可用 $q\circ g$ 区别它们，却不是原签名上下文；把 $g$ **正式加入**才得到命题 17 的严格细化。这不是原语言充分性被反驳。

**历史同构与依赖参数的勘界。** §4 的“编码相等 $\Rightarrow$ 历史同构 $\Rightarrow\ker q$”仍成立；它不自动插入任意 $\approx_\Sigma$。例如把总操作 $H_e(C,A)=(C,A\cap\{e\})$ 加入签名，$e\in HF$ 是一个固定出现标识。将一份两事件平衡表示中的所选正事件 $e$ 重命名为新标识 $e'$，保持全部属性，则两份表示历史同构，$q\circ H_e$ 却分别为 $1,0$。对一个具体签名若要证明历史同构蕴含观察等价，须证明该关系满足 (SC)、读数保持，并核对固定参数的作用；将参数一起运输所得的自然性，不等于固定同一参数的观察不变性。§16 的空间语言会满足所需条件。

定义 13 的因果查询还有类型依赖：$D$ 原本满足 $D\subseteq E_C$。在全载体上谈同一个查询时，可固定有限 $D\subset HF$ 并把 $F_{\downarrow D}$ 视为域 $\{(C,A):D\subseteq E_C\}$ 上的部分操作；或明确只比较两档案都包含 $D$ 的输入。重命名时需运输 $D$ 为 $h[D]$，不能悄悄把不同查询当作同一个。§17 的因果反例使用两侧共同有效的原事件集 $D$。

<a id="pr1-spatial"></a>

## 15. PR1 增补 B：可实现的精确空间读数及其代数

### 15.1 共同位置、全局像与固定情境容量

沿用 $d=3$，以下证明对任一固定有限 $d\ge1$ 成立。令

$$
R=\mathbb Z^{(\mathbb Z^d)}
=\{c:\mathbb Z^d\to\mathbb Z:\operatorname{supp}(c)\text{ 有限}\},
\quad \varepsilon(c)=\sum_p c(p),\quad I=\ker\varepsilon.
$$

括号上标表示有限支撑，绝非全部函数的无穷求和。记 $\delta_p(r)=1$ 当 $r=p$，其余为零。位置始终使用原稿同一坐标系。

**定义 18（双空间读数）。** 对 $X=(C,A)\in\mathcal B$ 定义

$$
\pi(X)=(w_X,z_X),\qquad
w_X(p)=\sum_{e\in\Omega_C,\ x(e)=p}\sigma(e),\qquad
z_X(p)=\sum_{e\in A,\ x(e)=p}\sigma(e).
\tag{SP}
$$

这是定义 12／命题 9 的共同位置特化：先取含全部当前位置的有限 bin 集合，令 $f=x|_{\Omega_C}$，再将 $w,z$ 向全格点补零。增添空 bin 不改变这个有限支撑函数，比较两对象时可取两个有限 bin 集的并。因此不是另造一种符号计数。总有 $w_X\in I,z_X\in R$，且 $q(X)=\varepsilon(z_X)$；旧档案 $E_C\setminus\Omega_C$ 不计入任一分量。

**命题 18（全局像及最小当前事件数，repo-derived）。**

$$
\pi[\mathcal B]=P:=I\times R.
\qquad
\min_{X:\pi(X)=(w,z)}|\Omega_X|
=\sum_p\bigl(|z(p)|+|w(p)-z(p)|\bigr).
\tag{IMAGE}
$$

**证明。** 包含于 $P$ 已由平衡及有限性说明。反向给定 $(w,z)\in P$，只需处理 $\operatorname{supp}(w)\cup\operatorname{supp}(z)$ 中有限个点。在每点 $p$ 放 $|z(p)|$ 个**选中**事件，符号为 $z(p)$ 的符号；再放 $|w(p)-z(p)|$ 个**未选**事件，符号为 $w(p)-z(p)$ 的符号。某项为零便放零个，无须定义零的事件符号。出现标识用 $(p,\mathrm{selected},i)$ 与 $(p,\mathrm{unselected},i)$ 的不同有限编码，故彼此不同；来源可全部取 leaf(0)，时间全部为零，偏序为空，取 $E=\Omega$。于是这是合法有限情境，逐点所选电荷恰为 $z$、全部当前电荷恰为 $z+(w-z)=w$，总背景为 $\varepsilon w=0$。这证明满像并达到所写事件数。

对任何实现，点 $p$ 的选中事件数至少为 $|z(p)|$，因为每个符号绝对值是 $1$；未选事件电荷为 $w(p)-z(p)$，其数量至少为该数绝对值。这两类互不相交，逐点求和即得下界。构造达到下界，故最小值存在且等于该式。若同时最小化整个档案数，下界仍由 $|E|\ge|\Omega|$ 给出，并由上述 $E=\Omega$ 的构造达到。证毕。

**命题 19（固定 $C$ 的选择像）。** 固定合法平衡情境 $C$，记当前位置 $p$ 的正、负事件数为 $n_+(p),n_-(p)$，则 $w(p)=n_+(p)-n_-(p)$ 固定，而可选分布恰为

$$
\{z\in R:\ \forall p,\quad -n_-(p)\le z(p)\le n_+(p)\}.
\tag{CAP}
$$

区间指逐点**整数**区间，非实区间。**证明。** 任何选择给出 $z(p)=a_+(p)-a_-(p)$，其中 $0\le a_\pm(p)\le n_\pm(p)$，故有界。反向每个非负 $z(p)$ 选恰好 $z(p)$ 个正事件、不选负事件；每个负 $z(p)$ 选恰好 $-z(p)$ 个负事件、不选正事件。区间保证数量够，各位置的选择互不干扰；当前位置以外两容量均为零，必有 $z(p)=0$，故得到一个有限合法选择。证毕。

(IMAGE) 允许随 $(w,z)$ **更换情境**，(CAP) 则固定完整 $C$。例如原代表 $\mathbf i(1)$ 与 $\mathbf i(2)$ 都有 $w=0$，在零点的选择容量分别是 $[-1,1]$ 与 $[-2,2]$。两者若取空选择甚至同为 $\pi=(0,0)$；从第一个固定情境却选不出 $2\delta_0$。不能把全局像 $I\times R$ 当作每一个 $C$ 的选择像。

### 15.2 闭包、空间筛选与位置限制的配对

在 $R$ 上定义逐点加法及有限卷积

$$
(c*d)(r)=\sum_{p+q=r}c(p)d(q).
\tag{CONV}
$$

求和只含两个有限支撑的 Cartesian 积；支撑包含于 $\operatorname{supp}(c)+\operatorname{supp}(d)$，故仍有限。

**命题 20（精确更新式）。** 原稿的并行加法、档案乘法、补集和任意固定空间筛选均在 $\mathcal B$ 上总定义，且

$$
\begin{aligned}
\pi(X\boxplus Y)&=(w_X+w_Y,z_X+z_Y),\\
\pi(X\boxtimes Y)&=(w_X*w_Y,z_X*z_Y),\\
\pi(NX)&=(w_X,w_X-z_X),\\
\pi(F_SX)&=(w_X,\mathbf1_S z_X).
\end{aligned}
\tag{UP}
$$

此外 $\varepsilon(c+d)=\varepsilon c+\varepsilon d$，$\varepsilon(c*d)=(\varepsilon c)(\varepsilon d)$，所以 $I$ 对加法、负号封闭，且 $I*R\subseteq I$。

**证明。** 并行时同一位置的两份带标签电荷相加。乘法只数新当前事件 $p_{ab}$：其位置为 $x(a)+x(b)$，符号为 $\sigma(a)\sigma(b)$；对父位置 $p,q$ 分组，每组有限双和为 $w_X(p)w_Y(q)$，所选组同理为 $z_X(p)z_Y(q)$，再按 $p+q=r$ 合组即得卷积。旧档案仍保留，但不在当前区域，故没有额外线性项。补集逐点是未选电荷，即 $w-z$；筛选只从 $A$ 中删点，背景 $\Omega$ 不动，故必须保留完整 $w$，**不能同时筛掉 $w$**。对有限和换序得到

$$
\sum_r\sum_{p+q=r}c(p)d(q)
=\sum_p\sum_q c(p)d(q)
=\Bigl(\sum_pc(p)\Bigr)\Bigl(\sum_qd(q)\Bigr).
$$

加法和负号下的增广公式逐项成立。由此各式背景都仍属 $I$，也给出 §2/3 的标量读数公式。证毕。

**位置限制扩展的精确范围。** 固定一个谓词 $K\subseteq\mathbb Z^d\times\mathbb Z^d$；定义 14 中对每对输入取 $R_{X,Y}=\{(a,b):K(x_X(a),x_Y(b))\}$，记所得总操作为 $M_K$。仍使用完整乘积情境，因此

$$
w_{M_K(X,Y)}=w_X*w_Y,\qquad
z_{M_K(X,Y)}(r)=\sum_{p+q=r}\mathbf1_K(p,q)z_X(p)z_Y(q).
\tag{K}
$$

**证明。** 每个位置对 $(p,q)$ 中的事件对或者全部保留或者全部排除，故该组电荷为 $\mathbf1_K(p,q)z_X(p)z_Y(q)$；背景没有被限制，仍按 (UP)。有限分组即得式。证毕。这只依赖位置的前提不能换成任意来源、因果或出现身份关系；同位置组中的那些关系不必恒定。

(K) 不恢复已被命题 12 否定的标量乘法：取非零 $v$，输入 $\mathbf i(1)$ 及其空间平移 $v$，二者读数均为 $1$；若 $K(p,q)$ 为 $p=q$，所选对被排除，结果读数为 $0$，而完整乘积为 $1$。第二个输入若不平移，受限读数又为 $1$。任意 $K$ 也不自动继承卷积的交换、结合律；本批只证明所写更新式及 §16 的语言充分性。

### 15.3 带补集运算的交换无单位环

**定义 19。** 在 $P=I\times R$ 上以 (UP) 定义逐分量加法和卷积乘法，零元为 $(0,0)$；另记

$$
J(w,z)=(-w,-z),\qquad N(w,z)=(w,w-z).
$$

$J$ 由 §2 已列的**全档案符号翻转**实现：对每个 $e\in E$ 将 $\sigma(e)$ 换成 $-\sigma(e)$，其余数据及选择不动。时间约束、偏序和有限性仍合法，平衡仍为零；两个空间分量各自取负。这与保持情境、仅改选择的 $N$ 是不同操作。

**命题 21（$P$ 的完整本批类型）。** $P$ 是交换无单位环（rng），$J$ 是其加法逆；$N$ 是额外的加法群自同构及对合，通常不是加法逆、也不是乘法同态。对任一点 $(w,z)\in P$，

$$
N(w,z)=J(w,z)\iff w=0.
\tag{NJ}
$$

**证明（群与卷积定律）。** 逐点整数加法给出 $R$ 的阿贝尔群；$\varepsilon$ 保加，故 $I$ 是子群，$P$ 的逐分量加法也是阿贝尔群，逆为 $J$。卷积有限支撑保证其类型闭合，命题 20 保证 $I$ 分量闭合。对任意 $c,d,e\in R$ 和位置 $r$，

$$
((c*d)*e)(r)=\sum_{p+q+s=r}c(p)d(q)e(s)
=(c*(d*e))(r).
$$

这是同一个有限三重和按不同顺序分组；整数乘法结合且格点加法结合。交换变量 $p,q$ 并用整数乘法交换得 $c*d=d*c$。逐项用整数分配律得 $c*(d+e)=c*d+c*e$，另一边同理。因此这些定律逐分量传到 $P$，零乘积也逐点为零；这是 rng 所需的全部环定律，尚未假设单位存在。

**证明（没有乘法单位，独立于单位分类）。** 反设 $(a,b)\in P$ 对全部 $P$ 元素为单位。乘 $(0,\delta_0)$ 得 $(0,b)=(0,\delta_0)$，故 $b=\delta_0$。因 $d\ge1$，可取非零格点 $v$；$\delta_v-\delta_0\in I$。对 $(\delta_v-\delta_0,0)$ 的单位条件给出

$$
(a-\delta_0)*(\delta_v-\delta_0)=0.
$$

令 $c=a-\delta_0$，逐点评价为 $c(r-v)=c(r)$。若某点 $c(r_0)\ne0$，沿 $r_0+nv\ (n\in\mathbb Z)$ 值恒相同；非零整数向量无加法挠元，这些点两两不同，与有限支撑矛盾。因此 $c=0$，迫使 $a=\delta_0$；但 $\varepsilon(a)=0$ 而 $\varepsilon(\delta_0)=1$，矛盾。这个证明没有借用 $R$ 的整性或完整单位分类。$d\ge1$ 在此必要：$d=0$ 时格点群只有零点，$I=0$，$P\cong\mathbb Z$ 反而有单位。

**证明（$N$ 的角色）。** 直接展开得到 $N(x+y)=N(x)+N(y)$ 及 $N^2=\mathrm{id}$，故是加法群自同构。若 $N(w,z)=J(w,z)$，第一分量要求 $w=-w$，逐点整数无二挠元，故 $w=0$；反向 $w=0$ 时两式均为 $(0,-z)$。例如 $\alpha=\delta_0-\delta_v\ne0$，$N(\alpha,0)=(\alpha,\alpha)$ 而 $J(\alpha,0)=(-\alpha,0)$，所以不是一般负号。令 $e_0=(0,\delta_0)$，则

$$
N(e_0e_0)=(0,-\delta_0),\qquad
N(e_0)N(e_0)=(0,\delta_0),
$$

两者不同，故 $N$ 不是乘法同态。证毕。

**零因子与局部单位。** $a_0=(\alpha,0)$ 和 $e_0=(0,\delta_0)$ 都非零，$a_0e_0=(0,0)$，给出 $P$ 的零因子。子 rng $P_0=\{0\}\times R$ 有自己的单位 $e_0$，因为 $\delta_0*c=c$；它不是 $P$ 的单位，刚才的 $a_0e_0=0\ne a_0$ 已反驳。$P_0$ 上 $N=J$；一般 $z$ 空间层 $R$ 的抽象负号为 $z\mapsto-z$，可由全档案符号翻转诱导，不能与一般背景下的 $N$ 混同。以上类型论断只属于空间商；§4 的 $28/32$ 档案反例继续有效。

<a id="pr1-languages"></a>

## 16. PR1 增补 C：三种明确语言与最粗充分性

本节统一取 $X=\mathcal B$、终端观察 $q:\mathcal B\to\mathbb Z$，上下文严格按定义 16 取全槽位、全部固定丰富参数及任意有限复合。固定空间区域作为操作的名字，不因当前输入改规则。定义

$$
\begin{aligned}
\Sigma_{\rm arith}&=\{\boxplus,\boxtimes,N\},\\
\Sigma_z&=\{\boxplus,\boxtimes\}\cup\{F_S:S\subseteq\mathbb Z^d\},\\
\Sigma_{\rm sp}&=\Sigma_z\cup\{N\}.
\end{aligned}
$$

在 $\Sigma_z,\Sigma_{\rm sp}$ 中也可以只保留全部单点筛选 $F_p:=F_{\{p\}}$，以下同一结论仍成立。$\Sigma_{\rm arith}$ 与 $\Sigma_z$ 作为符号集合**互不包含**，不能从命题 17 直接比较这两个签名；各自都是 $\Sigma_{\rm sp}$ 的子签名。

**命题 22（语言决定观察核，repo-derived）。**

$$
\approx_{\Sigma_{\rm arith}}=\ker q,\qquad
\approx_{\Sigma_z}=\ker z,\qquad
\approx_{\Sigma_{\rm sp}}=\ker\pi.
\tag{LANG}
$$

**证明（充分性须对上下文归纳）。** 算术语言在 $q$ 上的更新分别为整数加、乘、负；空间语言在 $z$ 上的更新分别为加、卷积、$\mathbf1_Sz$；加入 $N$ 后在 $\pi$ 上的全部更新为 (UP)。三种情况下终端 $q$ 都由相应读数决定（空间两种为 $\varepsilon z$）。所有这些丰富操作均为总函数，故不会藏有未保存的部分域。

取一对相应读数相等的输入。恒等孔仍等；基本上下文的固定参数在两侧是同一对象，故上述更新式给出相等的输出读数；有限复合时对子上下文应用归纳假设，再用外层更新式。由此每个合法上下文的终端 $q$ 相同，得到相应核包含于观察等价。该归纳也可直接视为命题 16 的同余充分方向，不能用测试了有限几个上下文替代。

**证明（必要性）。** 算术语言有恒等孔，故观察等价必须在 $\ker q$ 内。空间语言含每个单点筛选，而

$$
q(F_pX)=z_X(p),\qquad
q(F_pNX)=w_X(p)-z_X(p).
\tag{REC}
$$

第一式使 $\Sigma_z$ 观察等价必有全部 $z$ 坐标相同。空间加补集语言中第二式也可观察；结合第一式，逐点相加恢复 $w_X(p)$。所以 $\Sigma_{\rm sp}$ 观察等价必有全部 $w,z$ 相同，即属于 $\ker\pi$。这与充分性合并证明 (LANG)，且只用了单点筛选。证毕。

这些核的严格关系可用具体对象验证。令 $v\ne0$，$U=\mathbf i(1)$，$U_v$ 为其空间平移 $v$；二者读数均为 $1$，但 $z_U=\delta_0,z_{U_v}=\delta_v$，单点筛选在零点给 $1,0$。另令 $B_\alpha$ 为命题 18 对 $(\alpha,0)$ 的实现，$\alpha=\delta_0-\delta_v$，即两个未选事件 $+@0,-@v$；空档案与它都有 $z=0$，而 $q(F_0N0_\varnothing)=0$、$q(F_0NB_\alpha)=1$。故
$\ker\pi\subsetneq\ker z\subsetneq\ker q$；这个关系由证明与见证给出，不来自前两个签名的包含。具体这些语言还满足历史同构 $\Rightarrow\ker\pi$（逐位置重索引即可），因此可以在此特定情形插入观察关系；不能把该结论外推到出现身份探针语言。

**命题 23（任意充分读数恢复 $\pi$）。** 设 $h:\mathcal B\to H$ 是任意总读数，且对 $\Sigma_{\rm sp}$ **充分**，即 $h(X)=h(Y)$ 蕴含所有该签名上下文的严格终端观察相同。则存在唯一函数

$$
\kappa:h[\mathcal B]\longrightarrow P,
\qquad \kappa(h(X))=\pi(X).
\tag{FACTOR}
$$

**证明。** 命题 22 的必要性给出 $\ker h\subseteq\ker\pi$。因此对每个实际出现的 $u\in h[\mathcal B]$，关系“存在 $X$ 使 $h(X)=u$ 且 $\pi(X)=p$”定义唯一的 $p$；存在性来自像的定义，唯一性来自核包含。该关系的图就是 $\kappa$，不必为每条纤维选代表。任意满足等式的函数在每个像点都被强制定值，故唯一。无需假设 $h$ 对整个 $H$ 满射，也不要求在未命中点定义恢复函数。命题 22 的充分方向则表明 $\pi$ 本身可用，故它在核包含意义下是最粗充分读数。证毕。

若先给 $h$ 上的每个操作更新式与保域条件，并给终端 $q$ 的恢复式，上下文归纳会推出命题 23 所用的充分性。这是信息可辨识性的精确结论，**不是字节数最优**、不是对任意观察的可计算性承诺，也不恢复档案历史。任意集合 $S,K$ 的数学定义不意味着其成员测试有算法。

可将任意预先固定的纯位置操作 $M_K$ 加入 $\Sigma_z$ 或 $\Sigma_{\rm sp}$：由 (K) 相应读数仍可更新，且原来的单点探针仍在，故 (LANG) 的这两项及 (FACTOR) 不变。**不能同样宣称 $\Sigma_{\rm arith}$ 加入任意 $M_K$ 后仍为 $\ker q$**；§15.2 的 $p=q$ 例子已给同输入数值、不同受限输出数值。完整卷积与位置受限配对须分清。

<a id="pr1-boundaries"></a>

## 17. PR1 的分离反例、来源边界与核验收据

### 17.1 同空间读数仍不能回答的查询

**反例 B1（同 $\pi$、异来源）。** 两份档案都取 $E=\Omega=\{a,b\}$，符号分别为 $+,-$，时间和位置为零，偏序为空，选择 $\{a\}$。第一份全部来源为 leaf(7)，第二份全部为 leaf(8)。两者 $\pi=(0,\delta_0)$，但来源筛选 $L=\{\operatorname{leaf}(7)\}$ 后 $q$ 分别为 $1,0$。因而来源查询不被 $\Sigma_{\rm sp}$ 覆盖。若定义 14 的关系改为“两父来源相等”，固定另一个所选正事件来源为 leaf(7) 的因子，两份输入的受限输出也分别为 $1,0$，虽空间输入对相同；这说明 (K) 的位置假设有实质内容。

**反例 B2（同 $\pi$、异因果，且 $D$ 共同有效）。** 取两份相同的 $E=\Omega=\{a,b,c,d\}$、零位置、来源 leaf(0)，符号按序为 $+,+,-,-$，时间为 $0,1,0,1$，选择 $\{a,b\}$。第一份唯一严格边为 $a\prec b$，第二份偏序为空，二者都合法，且 $\pi=(0,2\delta_0)$。固定原事件集 $D=\{b\}$，两档案确实都包含它。因果过去筛选在第一份选到 $a,b$、第二份仅选到 $b$，读数为 $2,1$。不以重命名后的无效 $D$ 伪造这个反例。若用“左父在左档案的 $\downarrow D$ 中”限制配对，与一个所选正贡献相乘，同样给 $2,1$；任意因果关系不由位置公式覆盖。

**反例 B3（同 $\pi$、异时间复合域）。** 取 $U=\mathbf i(1)$，再构造 $U^{\rm old}$：保留 $U$ 的当前区域、选择及全部当前属性，只向 $E\setminus\Omega$ 加一个新出现标识、时间为 $2$、位置为零、符号为正、来源 leaf(9) 的旧事件，仍取空偏序。二者皆平衡，$\pi=(0,\delta_0)$。固定 $Y=T_1(U)$，则 $U\triangleright Y$ 合法且读数为 $2$，$U^{\rm old}\triangleright Y$ 因 $2<1$ 为假而无定义。即使保留当前事件的全部时间也漏掉这个域差。PR1 的时间操作继续回到完整档案检查 (T)，不声称 $\pi$ 保存时间守卫；时间摘要属于下一独立批次。

**反例 B4（同 $w$、异固定情境容量）。** §15.1 的 $\mathbf i(1),\mathbf i(2)$ 是已给的见证：在零点分别只有一对与两对正负候选，$w=0$ 相同，空选择还给相同 $\pi$，但允许重选的区间为 $[-1,1]$ 与 $[-2,2]$。这个性质涉及固定 $C$ 中的可能选择族，不是当前选择的单次读数，命题 23 不承诺恢复它。

出现身份关系也越过 (K)：对历史同构但把所选事件 $a$ 换成 $a'$ 的 B1 型表示，固定关系“左父出现标识为 $a$”只在前者保留所选对，输出为 $1,0$。最后，§4 两种括号的档案数 $28,32$ 仍不同；它们的双空间读数却均为 $(0,2\delta_0)$，卷积结合律只识别这个商，不能向上推回历史同构。

### 17.2 成熟来源与本轮产地

本轮采用以下已实际核读的来源收据（调用方在派工中提供），无需把元数据检索冒称逐页证明核读。其适用边界分别为：

| 来源与可定位落点 | 已有内容与本稿使用边界 |
| --- | --- |
| Stanley Burris、H. P. Sankappanavar, *A Course in Universal Algebra*, 作者公开 2012 版，[II §5 定义 5.1 与 II §10](https://www.math.uwaterloo.ca/~snburris/htdocs/UALG/univ-algebra2012.pdf) | `literature-attested`：总代数同余及项运算保持同余。本文 (SC) 额外保留部分域，其最大性是命题 16 的自给证明，未声称原书给出同一部分操作定理。 |
| Andrew M. Pitts, “Operational Semantics and Program Equivalence”, *Applied Semantics*, LNCS 2395 (2002)，[§3 定义 3.1／备注 3.2](https://www.cl.cam.ac.uk/~amp12/papers/opespe/opespe-lncs.pdf) | `literature-attested`：用上下文及终止观察刻画程序等价的成熟方法。这里采用确定部分函数与带标签失败观察，未把程序语言语义或其定理无条件搬到本载体。 |
| Mathlib 在线文档 [Algebra.MonoidAlgebra.Defs 的 mul_def](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MonoidAlgebra/Defs.html) | `literature-attested`：有限支撑系数的卷积乘法。这里只作成熟结构来源；在线文档不是本仓 pin 的核对，也不是本稿的 Lean 验证。 |

强保域最大性、双读数可实现像及最小事件数、固定情境容量、特定语言充分性和本稿 rng 的结论归为 `repo-derived`，证明已在 §14–16 给全。不主张首创；有限和、同余和群代数结构均有成熟背景。辅助 `/tmp/csa-upgrade-20260909/literature-intake.json` 仅消费其 `conclusion`：Milne 的群代数例子是域系数，Gallier 是实仿射空间，二者不作为本批整数系数结论或单位分类的证明。任何 `log_ref` 内容均未消费。

本轮实施是在 `consensus-rnd:sshx` 下由唯一 Codex 实施席完成，输入暴露为 `repo-prior-exposed`（完整派工 GoalArtifact、批准计划、CLAUDE.md、agents/CONTEXT.md、基线文稿及上述来源收据），不称先验独立。按本轮调用方派工记录，两次 NyxID 思考调用均失败，teleology 由 Codex 回退完成；company 默认池的连通性 probe 只返回模型标识 GPT-6 Astra，没有数学内容，**不计 S1 的实质 PRO 意见**。§12 的旧 task 属原稿历史，不算本轮成功调用。当前数学工件的真实网页数学评审、architecture/quality/tests 三席、仓库 required checks 及 PR 生命周期均由 caller 接续，尚不宣称通过或合入。PR2 的时间摘要、完整单位分类、律表和参考点族不属于本批完成主张。

### 17.3 PR1 定向精确核验的范围与预期

附录唯一 Python 块复用原有 `Rich/add/mul/neg`，新增函数仅服务本页的核验。预期值来自正文命题、展开式及反例，未用被检查输出反过来生成预期。一般命题的证明是 §14–16 的证明；脚本对如下明确有限窗口检查实现与这些结论是否一致。

背景恢复在原 105 个表示上逐个探测第一坐标 $0,1,2,3$，共预期 $420$ 次；另用 $(\alpha,0)$ 与空档案检出漏存背景的错误，并检查筛选之后背景仍在。像构造取 $p\in\{0,v,h\}$，$v=(1,0,0),h=(0,1,-1)$，$w$ 的系数为 $(a,b,-a-b)$、$a,b\in\{-1,0,1\}$，$z$ 三个系数各取 $\{-1,0,1\}$，预期 $9\cdot27=243$ 个实现都达到 (IMAGE) 的事件数。固定容量枚举两个位置各自的 $n_+,n_-\in\{0,1,2\}$ 且全局平衡，预期 $19$ 个固定情境、$673$ 个选择；其读数像与 (CAP) 的逐点整数区间逐一比较。

小量稀疏卷积另用显式例子

$$
\pi(X)=(\delta_0-\delta_v,2\delta_0-\delta_v),\qquad
\pi(Y)=(\delta_h-\delta_0,\delta_v+\delta_h).
$$

普通展开给出背景 $\delta_h-\delta_0-\delta_{v+h}+\delta_v$、选择 $2\delta_v+2\delta_h-\delta_{2v}-\delta_{v+h}$，读数为 $2$；$K(p,q)\equiv(p=q)$ 只留下选择 $-\delta_{2v}$，读数为 $-1$，背景不变。这两个最小实现各有四事件，完整乘积档案数 $4+4+4\cdot4=24$。另取 $w=c\alpha\ (c\in\{-1,0,1\})$ 与 $z\in\{-\delta_h,0,\delta_v+\delta_h\}$ 的 $9$ 个状态，检查 $81$ 个丰富输入对的更新式和 $729$ 个空间读数三元组的卷积结合、分配式；仍单独保留 $28/32$ 的丰富层非结合见证。

错误上下文族定向执行反例 A1、A2 的 $k=0,\ldots,4$、A3 的缺槽位与缺参数族（深度 $0$ 至 $3$ 分别 $40,85$ 个词），并区别额外非签名探针。来源、因果、时间域和出现身份使用 B1–B3 及共同有效 $D$ 的具名样本，预期读数分别为 $1/0$、$2/1$、有定义/无定义、$1/0$；另检查重命名后原 $D$ 的依赖域确实可能失效。

零因子、$N\ne J$、$N$ 非乘法同态和 $P_0$ 的自身单位各执行正文见证。有限无单位探针仅枚举 $a$ 支撑在 $\{0,v,h\}$、系数在 $[-2,2]$ 且总和零的 $19$ 种背景，与同支撑、系数在 $\{-1,0,1\}$ 的 $27$ 种 $b$，共 $513$ 个候选；对 $b\ne\delta_0$ 用 $e_0$，对 $b=\delta_0$ 用 $(\alpha,0)$ 检出不满足单位律。这个有限排除**不证明所有格点、所有系数上不存在单位**，后者只由命题 21 的有限支撑周期性证明承担；同样，有限上下文测试不证明全部上下文的最大性或充分性。

**本轮实际运行收据（2026-09-09）。** 在指定工作树、基线 `4ee990c9cb7eb3c8692f0c3f6e5be53cf28f9c85` 上，按附录原 `sed ... | sed ... | python3 -` 命令执行扩充后的唯一代码块，进程实际退出码为 `0`。原 $105/11025$ 检查也在这次执行中运行；本次增加的实际标准输出为：

```text
pr1_recovery: singleton_checks=420 background_after_filter=preserved kernels_strict=True
pr1_image_capacity: image_cases=243 fixed_contexts=19 choices=673 capacities=[-1,1],[-2,2]
pr1_convolution: sparse_states=9 rich_pairs=81 pair_triples=729 explicit_full_q=2 restricted_q=-1 archives=28,32
pr1_contexts: common_domain_miss=1 depth_counterexamples=5 restricted_word_checks=125 slot_parameter_and_extra_probe=distinguished
pr1_boundaries: same_pair_source=1,0 causal=2,1 time_domain=defined,undefined identity=1,0 dependent_D=defined,undefined
pr1_rng: zero_divisors=confirmed N_not_J=confirmed N_not_multiplicative=confirmed P0_unit_only=True finite_unit_candidates_rejected=513
ALL_FINITE_CHECKS_PASSED
```

输出中的 `confirmed/True` 仅报告上述有限例子的断言；一般结论由正文证明。原附录末句“新文档之外未改动任何仓库文件”只描述基线工作；本轮交付范围为本源正文及本源 canonical ingest 新产物，不新增 Lean 或生产算术模块。

<a id="pr2-laws"></a>

## 18. PR2 增补 D：分层律与强部分结合

本批沿用 $d=3$、定义 1–19，新增结论均为普通数学证明。等式必须说明所在层，不能省略取商步骤：

| 层 | 所识别的数据 | 可引用的律及边界 |
| --- | --- | --- |
| 严格标签相等 $=$ | 全部编码，包括每次并集的嵌套标签 | $N^2X=X$；带标签并集不作无条件结合、交换或单位等式 |
| 历史同构 $\cong_h$ | 可重命名出现标识，仍保存全部属性、偏序、当前区域和当前选择 | 并行加法为交换幺半群；档案乘法不结合、不交换、不分配、无单位 |
| $\pi$ 空间商 $P=I\times R$ | 双空间电荷，遗忘时间及历史 | §15 的交换 rng；加法逆是 $J$，$N$ 一般不是负号；$P_0$ 才有自己的单位 |
| $\Theta$ 时间摘要 | $\pi$ 及 §20 的三个端点 | §20 的闭合部分代数；并行加法为交换幺半群，乘法交换、分配但不结合、无单位 |
| 标量商 $\mathcal B/\ker q$ | 所选总电荷 | §4 的整数环；仅凭标量不能保留时间复合域 |

对本批指定语言，关系有 $=\ \subseteq\ \cong_h\ \subseteq\ker\Theta\subseteq\ker\pi\subseteq\ker q$：历史同构按位置及时间重索引，保持双电荷和三个端点；后两包含由忘掉端点及 $q=\varepsilon z$ 给出。反向均失败，分别见出现重命名、B1 的同时间异来源、B3 的旧档案时刻、§16 的同数异位置见证。此链不外推到带固定出现身份探针的任意签名。

**命题 24（历史层的律与反例）。** 历史同构是 $\boxplus,\boxtimes,N$ 的同余，也是 $\triangleright$ 的强保域同余。模历史同构的并行加法以空档案为单位，满足交换、结合；$N$ 是对合，但非空档案没有相对于空档案的加法逆。表中历史乘法的四项失败均成立。

**证明。** 给输入的历史同构 $h_X,h_Y$，在两份旧档案上使用 $(i,e)\mapsto(i,h_i(e))$，在乘法新点上使用 $p_{ab}\mapsto p_{h_X(a)h_Y(b)}$。这是双射，保持全部属性（来源仍为同序的 pair）、生成边及其传递闭包，也运输当前区域和选择。补集由双射运输。时间 guard 逐事件只检查被保持的时刻，故在两侧同真同假；有定义时同一双射还运输全部跨边。这证明同余及保域性。

并行加法的交换同构交换左右标签；结合同构按实际嵌套位置展平为三个分量，再按另一括号加标签。更明确地，左括号的 $(0,(0,e)),(0,(1,f)),(1,g)$ 分别对应右括号的 $(0,e),(1,(0,f)),(1,(1,g))$。两侧都只含原有内部边，所有属性与区域、选择对应，故为历史同构。空档案相加时去掉唯一非空分量的标签即得单位同构。对任一非空 $E_X$，$|E_{X\boxplus Y}|=|E_X|+|E_Y|>0$，所以任何 $Y$ 都不能把和变成空档案；特别 $N(X)$ 不是这种逆。$N^2X=X$ 已由命题 1 在严格层证明。标签展平是同构而非标签等式，例如非空 $X$ 与 $X\boxplus0_\varnothing$ 的有限事件标识整体被加了一层标签，不应写成严格单位等式。

非结合仍用 §4 的原见证 $X=Y=\mathbf i(1),Z=\mathbf i(2)$，两括号档案数为 $28,32$，旧反例完整保留。非分配取 $U=\mathbf i(1)$：

$$
|E_{U\boxtimes(U\boxplus U)}|=2+4+2\cdot4=14,
\qquad
|E_{(U\boxtimes U)\boxplus(U\boxtimes U)}|=8+8=16.
\tag{HD}
$$

二者 $q=2$，但基数阻止任何历史同构；另一侧分配也由 $(U\boxplus U)\boxtimes U$ 的同一计数失败。非交换取两个两事件的 $U$ 型表示，时间全为 $0$、位置全为零、各选正事件，第一份来源全为 leaf(7)，第二份全为 leaf(8)。$X\boxtimes Y$ 的四个新点全在时刻 $1$，来源全为 pair(leaf(7),leaf(8))；$Y\boxtimes X$ 的四个新点同在时刻 $1$，来源全为 pair(leaf(8),leaf(7))。有序 pair 的这些值不同，时刻 $1$ 的点也不能对应任何时刻 $0$ 的旧点，故不存在保属性的双射。

最后假定某 $V$ 是历史乘法单位。由 $0_\varnothing\boxtimes V\cong_h0_\varnothing$，档案基数公式迫使 $E_V=\varnothing$。但此时 $U\boxtimes V$ 的当前区域为空，不能同构于当前区域有两点的 $U$，矛盾。此证明排除任意 $V$，不只排除所选数值一代表。证毕。

**命题 25（时间复合的强部分结合）。** 写 $G(X,Y)$ 为定义 5 的全档案 guard。两表达式 $(X\triangleright Y)\triangleright Z$ 与 $X\triangleright(Y\triangleright Z)$ 都恰在

$$
G(X,Y)\ \land\ G(X,Z)\ \land\ G(Y,Z)
\tag{TA}
$$

上有定义；在该域上有命题 24 所述的重括号历史同构。

**证明。** 左括号先要求 $G(X,Y)$，再要求 $E_X\sqcup E_Y$ 中每点早于 $E_Z$ 每点；后一要求恰分成 $G(X,Z)\land G(Y,Z)$。右括号先要求 $G(Y,Z)$，再将其档案并集拆开得到 $G(X,Y)\land G(X,Z)$。这种全称量词对并集的分解在任一集合为空时仍成立，故两定义域完全相同。两侧最终都保留三个内部偏序并加入全部 $X\to Y,X\to Z,Y\to Z$ 跨边，标签展平逐边对应，也逐项对应全部属性、区域和选择，所以是历史同构，不是无条件严格标签结合式。证毕。

若 $E_Y\ne\varnothing$，相邻 guard 可经任一 $y\in E_Y$ 和整数序传递性推出 $G(X,Z)$；这个非空前提不能省。取 $X=T_2(U),Y=0_\varnothing,Z=T_1(U)$，$G(X,Y)$ 与 $G(Y,Z)$ 都空真，$G(X,Z)$ 却为假，两括号都失败。合法对照 $U,T_1(U),T_2(U)$ 满足全部三 guard，两括号都有六事件与十二条跨可比关系。空中间的合法对照 $U,0_\varnothing,T_1(U)$ 也满足 (TA)。

<a id="pr2-units"></a>

## 19. PR2 增补 E：有限空间卷积的整性、单位与方程

以下 $R=\mathbb Z^{(\mathbb Z^3)}$ 及 $*$ 完全沿用 §15；所有支撑有限。给 $\mathbb Z^3$ 选定字典全序 $\le_{\rm lex}$：按第一个不同坐标的整数序比较。共同加向量后首个不同坐标及该处差值不变，故它与加法相容，即 $p<q\Rightarrow p+r<q+r$。该序不须良序；这里只用非空有限支撑存在最大、最小元。

**命题 26（卷积极值与无零因子）。** 对非零 $a,b\in R$，记支撑极值为 $a_-,a_+,b_-,b_+$，则

$$
\min\operatorname{supp}(a*b)=a_-+b_-,\qquad
\max\operatorname{supp}(a*b)=a_++b_+.
\tag{EXT}
$$

两极值点分别只有这一种来自两支撑的拆分，系数分别为 $a(a_-)b(b_-)$ 与 $a(a_+)b(b_+)$，均非零。因此 $R$ 无零因子。

**证明。** 对支撑点 $p,q$ 有 $p\le a_+,q\le b_+$，所以 $p+q\le a_++b_+$。若 $p<a_+$，则 $p+q<a_++q\le a_++b_+$；若 $q<b_+$ 同理。因此等号迫使 $p=a_+,q=b_+$，反向这一对确实出现。该卷积系数只有一个非零乘积项，两个非零整数的乘积非零，不能被其他项抵消；它是支撑最大元。将不等号反向得到最小元及唯一拆分。乘积至少含极值点，故不为零。证毕。

**命题 27（全部自身单位）。** $R$ 的单位恰为 $\pm\delta_p\ (p\in\mathbb Z^3)$，相应逆为同号的 $\pm\delta_{-p}$。$P_0=\{0\}\times R$ 相对于其自身单位 $(0,\delta_0)$ 的单位恰为 $(0,\pm\delta_p)$。

**证明。** $\delta_0*a=a$ 由逐点有限和直接成立。若 $a*b=\delta_0$，两因子都非零，由 (EXT) 有 $a_++b_+=a_-+b_-=0$。定义在这个有序群中的宽度 $W(a)=a_+-a_-\ge0$，同理 $W(b)\ge0$；两式相减得 $W(a)+W(b)=0$。两个非负元之和为零迫使各自为零：若其一严格正，加另一非负元仍严格正。于是两个支撑分别只有一个点，写为 $a=A\delta_p,b=B\delta_q$。乘积等于 $\delta_0$ 迫使 $p+q=0,AB=1$；整数中只能 $A=B=1$ 或 $A=B=-1$。反向这些点质量确实乘为 $\delta_0$。$R\to P_0,c\mapsto(0,c)$ 保持全部运算和自身单位，故直接运输分类。证毕。

这里的宽度是字典有序群中的向量差，未引入欧氏长度。命题 26 不会使 $P$ 无零因子：§15.3 的 $(\alpha,0)(0,\delta_0)=0$ 仍是正确反例。$P$ 自身无单位，本节不在 $P$ 中偷用“乘法逆”。

**反例 C1（数值可逆不推出有限空间可逆）。** 任取 $v\ne0$，令 $f=2\delta_0-\delta_v$，则 $\varepsilon(f)=1$，但它有两个支撑点，不属命题 27 的单位族，所以没有有限支撑卷积逆。由命题 18 可实现 $\pi(X)=(0,f)$，其 $q(X)=1$ 在整数标量商已经可逆，在 $P_0$ 的空间商却不可逆。此处未改变 §6 的整数非零与整除守卫、有理非零分母守卫或 §7 的实数非零类守卫。

**命题 28（空间方程的准确条件）。** 在有单位环 $R$ 中，给定 $f,h$，方程 $f*g=h$ 有解当且仅当 $h\in fR$；这是主理想成员条件。若 $f\ne0$，有解时唯一。

**证明。** $fR=\{f*r:r\in R\}$ 含零、对差封闭，且 $(f*r)*s=f*(r*s)$，故为理想。其成员定义正是存在一个有限支撑解，未声称存在通用除法操作或给出算法。若 $f*g_1=f*g_2$，分配律给 $f*(g_1-g_2)=0$，命题 26 迫使 $g_1=g_2$。$f=0$ 时恰在 $h=0$ 有解，且每个 $g$ 都是解。证毕。

<a id="pr2-theta"></a>

## 20. PR2 增补 F：保域时间摘要与最粗充分性

### 20.1 端点类型、实际像及闭合更新

**定义 20（时间摘要及允许签名）。** 对 $X\in\mathcal B$ 记

$$
\Theta(X)=(\pi(X),m_X,M_X,s_X),\quad
m_X=\min t_X[E_X],\quad M_X=\max t_X[E_X],\quad
s_X=\max t_X[\Omega_X].
\tag{TH}
$$

端点类型为 $m_X\in\mathbb Z\cup\{+\infty\}$，$M_X,s_X\in\mathbb Z\cup\{-\infty\}$，统一在扩展整数全序中比较。约定空 $E$ 的 $m=+\infty,M=-\infty$，空 $\Omega$ 的 $s=-\infty$。实际载体是

$$
\mathcal T:=\Theta[\mathcal B]\subseteq
P\times(\mathbb Z\cup\{+\infty\})
\times(\mathbb Z\cup\{-\infty\})^2.
$$

不声称右边任意元组可实现。例如 $E\ne\varnothing$ 时 $m,M$ 都有限且 $m\le M$；$\Omega\ne\varnothing$ 时还须 $m\le s\le M$。$\pi=(0,0)$ 不判定 $\Omega$ 为空，因未选的同位置正负对也有此读数。$s$ 检查整个当前整体，绝非 $\max t[A]$；例如所选正点在 $0$、未选负点在 $9$ 时，$s=9$ 而所选最大时刻为 $0$。

指定

$$
\Sigma_{\rm st}=\{\boxplus,\boxtimes,N,\triangleright\}
\cup\{F_S:S\subseteq\mathbb Z^3\}
\cup\{T_k:k\in\mathbb Z\}.
\tag{ST}
$$

乘法仍为定义 6 的 `max+1` 档案乘法，平移每次带显式整数 $k$。终端观察仍是 $q$，上下文严格按定义 16 使用全槽位、任意固定丰富参数及有限复合，失败为独立的 $\bot$。本签名不含来源、因果、出现身份或时间筛选。

**命题 29（$\Theta$ 上的精确域与更新，repo-derived）。** 在 $\mathcal T$ 的实际像上，(ST) 的操作全部下降并恰好保域。并行加法与有定义的时间复合都更新为

$$
(\pi_X+\pi_Y,\ \min(m_X,m_Y),\ \max(M_X,M_Y),\ \max(s_X,s_Y)).
\tag{TH+}
$$

时间复合的域恰为 $M_X<m_Y$，包括空输入。令

$$
\gamma(s,t)=
\begin{cases}
-\infty,&s=-\infty\text{ 或 }t=-\infty,\\
\max(s,t)+1,&s,t\in\mathbb Z.
\end{cases}
$$

档案乘法写 $g=\gamma(s_X,s_Y)$，更新为

$$
(\pi_X\pi_Y,\ \min(m_X,m_Y),\ \max(M_X,M_Y,g),\ g),
\tag{TH*}
$$

其中 $\pi_X\pi_Y=(w_X*w_Y,z_X*z_Y)$。补集仅把 $\pi$ 换为 $(w,w-z)$，空间筛选仅换为 $(w,\mathbf1_Sz)$；两者三个端点均不变。$T_k$ 不改 $\pi$，对三个有限端点加 $k$，对无穷哨兵保持原值。

**证明。** 并集只复制两档案的时刻、两当前区域的时刻，故极值分别取 min/max，且命题 20 给出 $\pi$ 加法；时间复合只添边、不改这几组数据。若两档案非空，有限极值使全称 guard 等价于最大左时刻严格小于最小右时刻。若左为空，$-\infty<m_Y$ 对所有可能的 $m_Y$ 成立；若右为空，$M_X<+\infty$ 对所有可能的 $M_X$ 成立；两者空时也成立，正好对应空真。

乘法任一当前区域空时无新事件，旧档案并集给出 (TH*) 的 $g=-\infty$ 分支。否则两区域的最高时刻都达到；所有新时刻至多 $\max(s_X,s_Y)+1$，取最高时刻父点即可达到，故新整体最大值为 $g$。新事件比其两个父点都晚，而父点已在旧档案中，所以任何新点都不能降低旧档案并集的最小时刻。档案最大值则须同时计两份旧档案及新整体，恰为 $\max(M_X,M_Y,g)$。$\pi$ 乘法由命题 20 给出。补集与空间筛选不改变 $E,\Omega,t$，平移保极值和空性，得其余更新。每个实际像输入都可取丰富原像；上述公式等于该合法丰富运算的像，故输出仍在 $\mathcal T$，且同摘要的不同原像得到同输出、同域。这证明恰好下降，不依赖任意形式端点元组的可实现性。证毕。

可选地加入 §15.2 的纯位置 $M_K$：它使用完整乘积情境，三个端点仍按 (TH*)，只有 $z$ 改用 (K)，故以下充分性与必要性也不变。这个边界不许可任意来源、因果或时间关系配对。

### 20.2 必要性探针与恢复定理

**命题 30（$\Theta$ 恰为最粗充分读数，repo-derived）。** 对 (ST) 的严格 $q$ 观察，

$$
\approx_{\Sigma_{\rm st}}=\ker\Theta.
\tag{THEQ}
$$

因此任意对此语言充分的总读数 $h:\mathcal B\to H$ 都在其实际像上唯一恢复 $\Theta$：存在唯一 $\kappa:h[\mathcal B]\to\mathcal T$ 满足 $\kappa(h(X))=\Theta(X)$。

**证明（充分性）。** 命题 29 使 $\ker\Theta$ 对所有基本操作强保域，并在域内保持摘要；终端 $q=\varepsilon z$ 可由摘要恢复。对定义 16 的上下文归纳：基本步骤同步成功或失败，成功时摘要相同；复合传播失败或继续应用同一更新。因此同摘要时任意上下文的严格终端观察相同。

**证明（恢复 $\pi,m,M$）。** 反向，单点探针 $q(F_pX)$ 与 $q(F_pNX)$ 按 (REC) 恢复全部 $z,w$。现在记 $U_t=T_t(\mathbf i(1))$，即两个当前正负事件、均在零位置且时刻 $t$、只选正事件，$q(U_t)=1$。这里下标 $t$ 始终指时间；与 §16 的空间平移见证区分。任意 $U_t$ 都可作为固定参数，不需要它是签名里的常数符号。由命题 29，

$$
X\triangleright U_t\text{ 有定义}\iff M_X<t,
\qquad U_t\triangleright X\text{ 有定义}\iff t<m_X.
\tag{TP}
$$

两整数阈值族分别恢复 $M$ 和 $m$。具体地，若 $M_X<M_Y$，较大者 $M_Y$ 有限，取 $t=M_Y$ 区分；这也覆盖 $M_X=-\infty$。若 $m_X<m_Y$，较小者 $m_X$ 有限，取 $t=m_X$ 区分；这也覆盖 $m_Y=+\infty$。空档案的阈值族在所有整数上均成功，而任一有限端点都有一个失败阈值，所以哨兵也被区分。

**证明（恢复 $s$，显式迭代界）。** 只余 $\pi,m,M$ 相同而 $s$ 不同的情形。不失一般性 $s_X<s_Y$，故 $s_Y$ 有限，$E_Y$ 非空；共同的 $m,M$ 因而有限，两档案都非空。选任意整数 $t\le m$，它同时满足 $t\le M$ 及 $t\le s_i$（对所有有限的 $s_i$）。对两输入用同一个一孔上下文反复右乘：$X^{(0)}=X$，$X^{(n+1)}=X^{(n)}\boxtimes U_t$，$Y$ 同理。由 (TH*) 归纳，非空当前区域每步最高时刻加一，而空当前区域始终为空；对 $n\ge1$，

$$
\begin{array}{ll}
s_i\in\mathbb Z:&s_{i^{(n)}}=s_i+n,\quad M_{i^{(n)}}=\max(M,s_i+n),\\
s_i=-\infty:&s_{i^{(n)}}=-\infty,\quad M_{i^{(n)}}=M.
\end{array}
\tag{AMP}
$$

理由是新加入的每份 $U_t$ 不超过旧天花板 $M$，而 $s_i+n$ 严格递增；有限 $s_i$ 仍不低于 $t$，所以下一次 $\gamma$ 恰再加一。两侧的 $\pi$ 始终相同，因为每步都与同一 $\pi(U_t)$ 相乘。

若两 $s$ 有限，取 $n=M-s_X+1\ge1$、$r=s_Y+n$，则 $M<s_X+n<s_Y+n=r$，所以 $M_{X^{(n)}}<r=M_{Y^{(n)}}$。若 $s_X=-\infty$，取 $n=M-s_Y+1\ge1$、$r=s_Y+n=M+1$，则 $M_{X^{(n)}}=M<r=M_{Y^{(n)}}$。两种情况下再接 $\square\triangleright U_r$，左侧有定义而右侧失败。迭代数有限，整个探针属于定义 16 的有限上下文。因此 $s$ 不同必可区分，得到必要性。空 $E$ 与非空 $E$ 已由上一段区分，不会在此被错误当成共同有限天花板的输入。

合并两方向得 (THEQ)。充分读数 $h$ 有 $\ker h\subseteq\approx_{\Sigma_{\rm st}}=\ker\Theta$；对每个 $h$ 的像点，所有原像的 $\Theta$ 值相同，故其图定义唯一 $\kappa$，与命题 23 的像上恢复证明相同。没有在未命中的 $H$ 点上选值，也不声称恢复函数可计算或字节数最优。证毕。

**反例 C2（仅存 $\pi,\min E,\max E$ 不充分）。** 构造 $X_0,X_9$，每份当前整体是一正一负，位置全为零、来源 leaf(0)、只选正事件；两点时刻分别全为 $0$ 或全为 $9$。另各加两个不入 $\Omega$ 的档案事件，时刻 $0,10$、零位置、正符号、来源 leaf(9)，使用不同出现标识，偏序为空。两者 $\pi=(0,\delta_0),m=0,M=10$，但 $s=0,9$。两次右乘 $U_0$ 后分别 $s=2,11$，归档最大时刻为 $10,11$。随后接 $\triangleright U_{11}$，前者有定义且 $q=2$，后者因 $11<11$ 为假而失败。这是明确的三步上下文，不靠一般迭代界代替具体核算。

**摘要的消费边界。** $\Theta$ 仍丢来源与因果：B1 两对象都有 $(m,M,s)=(0,0,0)$，B2 两对象都有 $(0,1,1)$，其原查询反例仍成立。它也不回答任意时间筛选。例：一份当前正事件在 $0$、另一份在 $5$，两份当前负事件都在 $9$，只选正点；另都加不入当前区域的时刻 $0,10$ 旧事件，其他属性同 C2。二者 $\Theta=((0,\delta_0),0,10,9)$，按“时刻等于 $0$”筛选却得 $1,0$。该操作未在 (ST) 中；正式扩签名才会进一步细化观察核。

### 20.3 摘要层的运算律及非环边界

**命题 31（摘要层的精确律）。** $\mathcal T$ 的并行加法是交换幺半群，单位为 $\Theta(0_\varnothing)=((0,0),+\infty,-\infty,-\infty)$；乘法交换且双侧分配，但不结合、没有单位；并行零一般不吸收乘法。

**证明。** (TH+) 的 $\pi$ 加法交换结合，端点的 min/max 也交换结合，空哨兵分别是相应 min/max 的单位。这给出全部幺半群律。乘法的 $\pi$ 卷积交换，(TH*) 各端点式也对称，故摘要乘法交换；这不反驳历史层的来源反例。

证明分配时先核对包括空区域的恒等式

$$
\gamma(s,\max(t,u))=\max(\gamma(s,t),\gamma(s,u)).
\tag{GD}
$$

若 $s=-\infty$ 或 $t=u=-\infty$，两边都为 $-\infty$。其余情形 $s$ 有限且 $t,u$ 至少一个有限；忽略其中的空项，两边都是这些有限值与 $s$ 的最大值加一，故相等。现比较 $X(Y+Z)$ 与 $XY+XZ$：$\pi$ 分量由卷积分配律相同；最小端点两边都是 $\min(m_X,m_Y,m_Z)$（重复的 $m_X$ 由 min 的幂等性消去）；$s$ 分量由 (GD) 相同；$M$ 分量两边都是 $\max(M_X,M_Y,M_Z,\gamma(s_X,s_Y),\gamma(s_X,s_Z))$。因此分配成立，另一侧由交换性给出。此核对包含 $E$ 空及 $\Omega$ 空而 $E$ 非空的边界。

非结合取 $U_0,U_0,U_1$，其三个 $s$ 为 $0,0,1$。左括号的新根时刻为 $\max(1,1)+1=2$，旧事件最高仅 $1$，故 $M=s=2$；右括号先生成 $2$，再生成 $3$，归档 $M=s=3$。两侧 $m=0,\pi=(0,\delta_0)$，摘要仍不同。任何单位候选 $V$ 与 $U_t$ 相乘，若 $s_V=-\infty$，输出 $s=-\infty\ne t$；否则输出 $s=\max(s_V,t)+1>t$，同样不可能是 $U_t$。故没有乘法单位。最后 $U_0\boxtimes0_\varnothing$ 的摘要是 $((0,0),0,0,-\infty)$，不等于空档案的并行零。非空档案的加法逆也不可能存在，因为其有限 $M$ 与任意 $M'$ 取 max 后不能成为 $-\infty$。所以这里不是环，空间环律不能全部搬上来。证毕。

<a id="pr2-time"></a>

## 21. PR2 增补 G：整数时间规则的必然部分与约定部分

**命题 32（最早整数与全部交换重标）。** 对 $a,b\in\mathbb Z$，$\max(a,b)+1$ 是同时严格晚于二者的最早整数。一个任意函数 $h:\mathbb Z\to\mathbb Z$ 满足

$$
h(\max(a,b)+1)=\max(h(a),h(b))+1\quad(\forall a,b\in\mathbb Z)
\tag{CLOCK}
$$

当且仅当存在 $c\in\mathbb Z$ 使 $h(n)=n+c$ 对全部整数成立，不需先假设 $h$ 双射或单调。

**证明。** $\max(a,b)+1$ 严格大于二者；任一整数 $j>a,b$ 满足 $j>\max(a,b)$，整数离散性给 $j\ge\max(a,b)+1$。对 (CLOCK) 代入 $a=b=n$，得到 $h(n+1)=h(n)+1$。以 $c=h(0)$，向上归纳给全部非负整数的公式；以 $h(n)=h(n+1)-1$ 向下归纳给全部负整数的公式。反向，整数平移保 max，代入即得 (CLOCK)。证毕。

**命题 33（完整二叉构造树的根时刻）。** 给一棵有限完整二叉树（每个内部节点恰有两子节点），叶 $i$ 的输入时刻为 $t_i\in\mathbb Z$，每个内部节点按默认规则计算。以叶到根的边数为 $\operatorname{depth}_i$，则

$$
t_{\rm root}=\max_i(t_i+\operatorname{depth}_i).
\tag{TREE}
$$

**证明。** 单叶树深度为零，公式成立。内部根的两子树由归纳假设分别有根时刻 $\max_{i\in L}(t_i+d_i)$、$\max_{i\in R}(t_i+d_i)$；新根取二者 max 再加一，等于对所有叶取 $\max(t_i+d_i+1)$。每片叶在整树中的深度恰比其子树深度多一，得公式。证毕。该式描述所选生成事件的构造树；档案中不参与该树的旧事件还可有更大时刻，不能用 (TREE) 代替全档案 $M$。它准确暴露括号树形依赖，不是物理时间定律。

**明示边界族（不替换默认）。** 若预先选择正整数延迟 $\kappa$，把每个新时刻规定为 $\max(a,b)+\kappa$，它仍严格晚于两父点，所以命题 3 的合法性证明逐边照用；但仅 $\kappa=1$ 有命题 32 的“最早整数”性质。同一结构归纳给根时刻 $\max_i(t_i+\kappa\operatorname{depth}_i)$。对正整数 $a$ 及整数 $b$，$h(t)=at+b$ 满足

$$
h(\max(t,u)+\kappa)
=\max(h(t),h(u))+a\kappa.
$$

这是因为正缩放保 max 且 $h(v+\kappa)=h(v)+a\kappa$。因此缩放同时运输延迟为 $a\kappa$ 才交换；若固定 $\kappa>0$，取 $t=u$ 就迫使 $a\kappa=\kappa$，即 $a=1$。默认模型与 §20 主定理始终取 $\kappa=1$。

<a id="pr2-reference"></a>

## 22. PR2 增补 H：共同空间参考点与整数仿射运输

**定义 21（带参考点的情境纤维）。** 对每个 $o\in\mathbb Z^3$ 取一个带标记的载体 $\mathcal B_o=\{(o,X):X\in\mathcal B\}$。只在共同 $o$ 的纤维内定义乘法 $\boxtimes_o$：定义 6 唯一改变的是新事件位置

$$
x(p_{ab})=x_X(a)+x_Y(b)-o.
\tag{ORIGIN}
$$

档案、符号、来源、`max+1` 时间、偏序、当前区域与选择都沿旧规则。$o=0$ 时逐项回到原模型，绝不暗换默认。不同参考点的输入不在此二元操作的域内；需先显式运输到共同纤维。在本节省略对象上重复的 $o$ 标记，并以 $u(X)$ 简记 $u(C_X)$。

**命题 34（参考点卷积与空间单位）。** 此运算合法，$q(X\boxtimes_oY)=q(X)q(Y)$、$u(X\boxtimes_oY)=u(X)u(Y)$ 及命题 3 的档案基数均不变。空间乘法成为

$$
(c*_o d)(r)=\sum_{p+q-o=r}c(p)d(q),
\qquad \pi(X\boxtimes_oY)=(w_X*_ow_Y,z_X*_oz_Y).
\tag{OC}
$$

有单位空间环 $(R,+,*_o)$ 的自身单位为 $\delta_o$；$\{0\}\times R$ 的自身单位为 $(0,\delta_o)$。它们不是档案乘法单位，也不是 $P$ 的单位。

**证明。** 位置不参与时标偏序约束，故合法性证明不变；电荷与基数只用符号、标签及候选对数，故命题 3 的逐项证明不变。按两父位置分组有限和即得 (OC)。直接计算 $\delta_o*_oc=c=c*_o\delta_o$。令 $L_o(c)(r)=c(r+o)$，它是 $R$ 的加法双射；置 $p=p'+o,q=q'+o$，有 $p+q-o=r+o\iff p'+q'=r$，所以 $L_o(c*_od)=L_o(c)*L_o(d)$。于是该环经 $L_o$ 与原 $R$ 同构，$P$ 的背景条件也由总和不变保持，故它仍无单位，$P_0$ 的自身单位则如上。档案基数及当前区域的无单位反证完全与位置无关，命题 24 仍适用。证毕。

**命题 35（整数仿射正向与双向运输）。** 给任意整数矩阵 $M\in\operatorname{Mat}_{3\times3}(\mathbb Z)$、整数向量 $v$，令 $F(x)=Mx+v$。将全部事件位置经 $F$ 运输而保持事件身份及其他数据，参考点同时变为 $F(o)$，定义 $\mathcal F:\mathcal B_o\to\mathcal B_{F(o)}$。它对全部这种 $M$ 都是合法的正向运输，且

$$
F(x+y-o)=F(x)+F(y)-F(o),
\qquad
\mathcal F(X\boxtimes_oY)=\mathcal F(X)\boxtimes_{F(o)}\mathcal F(Y).
\tag{AFF}
$$

整数坐标上的双向运输恰在 $M\in GL_3(\mathbb Z)$ 时保证。

**证明。** 左式展开为 $Mx+My-Mo+v$，右式也为同一向量。档案标签不变，旧点的属性在两侧一样，新点的位置由此恒等式一样，其他生成属性及边按同一旧规则，故得到完整丰富表示的等式，而非仅电荷等式。任意整数矩阵都保持位置的整数类型，且位置无额外合法性约束，故正向结论不要求单射。若 $M$ 在整数格点上双射，标准基向量的逆像组成整数矩阵 $N$，有 $MN=I$；行列式给 $\det M\det N=1$，所以 $\det M=\pm1$。反向若 $\det M=\pm1$，伴随矩阵公式给整数逆 $M^{-1}$，仿射逆为 $x\mapsto M^{-1}(x-v)$，也将参考点运回 $o$。这证明等价。证毕。

固定 $o$ 的共同平移失配仍在：先把两个输入加 $v\ne0$ 却不动 $o$，新位置为 $x+y+2v-o$；先乘再平移为 $x+y+v-o$。 (AFF) 运输的是带参考点的整个族，要求同时 $o\mapsto o+v$，没有推翻 §8 的旧反例。

**命题 36（有限推送与筛选的逆像公式）。** 即使 $F$ 非单射，$\mathcal F$ 也不合并任何事件身份。空间电荷则用有限推送

$$
(F_*c)(r)=\sum_{p\in\operatorname{supp}(c),\ F(p)=r}c(p),
\qquad \pi(\mathcal F X)=(F_*w_X,F_*z_X)
$$

合并系数；对任意 $S\subseteq\mathbb Z^3$ 有

$$
F_*(\mathbf1_{F^{-1}(S)}z)=\mathbf1_SF_*z,
\qquad
\mathcal F(F_{F^{-1}(S)}X)=F_S(\mathcal F X).
\tag{PULL}
$$

还满足 $F_*(c*_od)=(F_*c)*_{F(o)}(F_*d)$ 及 $\varepsilon(F_*c)=\varepsilon(c)$。

**证明。** 事件集合未取商，只改其位置属性；按新位置归组自然得到 $F_*$，即使某纤维无限，参与的支撑仍有限。左边 (PULL) 在 $r$ 的系数为 $\sum_{F(p)=r}\mathbf1_S(F(p))z(p)=\mathbf1_S(r)\sum_{F(p)=r}z(p)$，得电荷式；事件式来自逐事件条件 $x(e)\in F^{-1}(S)\iff F(x(e))\in S$。推送卷积的两边都是有限双和，分别按 $F(p+q-o)=r$ 或 $F(p)+F(q)-F(o)=r$ 分组，(AFF) 使条件相同。对全部目标点求和则每个原支撑项恰计一次，得增广式。证毕。

**反例 C3（直接像区域不能替代逆像）。** 取非单射 $F(x_1,x_2,x_3)=(0,x_2,x_3)$，$e_1=(1,0,0)$，$z=\delta_0+\delta_{e_1}$，$D=\{0\}$。有 $F_*(\mathbf1_Dz)=\delta_0$，但 $\mathbf1_{F[D]}F_*z=2\delta_0$。可用两个位置各一正一负、只选正点的四事件平衡表示实现 $w=0,z$；运输后四个出现仍各自存在，两个所选正贡献只是同处零点。错误来自把非饱和 $D$ 直接换成 $F[D]$：其逆像还含 $e_1$。正确的 (PULL) 在 $S=\{0\}$ 使用整个逆像，两边均为 $2\delta_0$。

<a id="pr2-evidence"></a>

## 23. PR2 的来源、调用边界与定向核验

### 23.1 成熟框架与本仓推导的边界

分层代数、上下文等价、群代数与仿射空间采用成熟框架，不称新颖。§17.2 已核读收据中的 Burris/Sankappanavar、Pitts、Mathlib 在线有限支撑卷积仍分别支持这些背景概念；它们不直接承担本批的 CSA 特定摘要证明。另使用 caller 在批准计划中提供的核读结论：

| 来源 | 精确范围与使用边界 |
| --- | --- |
| J. S. Milne, *Algebraic Groups* (2017)，[§12b，pp. 230–231](https://www.jmilne.org/math/Books/iAG2017.pdf) | `literature-attested`：域系数的有限生成阿贝尔群代数背景；不是本文整数系数单位分类的证明。 |
| Jean Gallier，[geomcs-v2.pdf](https://www.cis.upenn.edu/~jean/gbooks/geomcs-v2.pdf)，作者 2025-10-09 版 §2.1，pp. 18–19 | `literature-attested`：实系数仿射空间与点/向量区分；不冒称该页直接证明整数 torsor 定理。 |

CSA 的实际像、分层反例、$\Theta$ 闭合更新及必要性、此处整数仿射运输归类为 `repo-derived`；卷积极值、整数单位与整数仿射结论的证明均在正文自给，不以外部引文或有限核验填补证明。没有新增 Lean、axiom、判官、schema 或生产引擎，也不宣称本稿已被 Lean 验证。

**本批产地与意见状态。** 本批由 `consensus-rnd:sshx` 的一个 Codex implementation_worker 在固定 PR1 已提交候选 `feec239217c30601cca92c53620492516bec915a` 上实施；输入包括用户批准数学计划、必读规范及本树文稿，属于 `repo-prior-exposed`。未读取另一工作树、同轮 architecture 工件或其他 review 输出，未调用其他 worker。按 caller 本批明确告知的事实，PR1 两次 architecture oracle 请求均因超过预定 `configuring_composer` 等待窗口而被 caller 取消，未返回数学内容；这两次不是已完成数学意见。§17.2 的思考失败和纯连通性探测也不计本轮 S1，§12 旧 PRO 任务只属原稿历史。用户所称 GPT PRO 即 nyxid oracle 通道，不另按型号名是否带 Pro 判定。当前没有可消费的本轮成功实质 Nyx 数学意见；S1 由后续实际 oracle 评审继续结算，实际意见的处置和独立三席评审由 caller 记录。本批不预报 PR2 最终评审通过、required checks 通过或合入。

### 23.2 定向有限核验的预期与界限

附录原有唯一 Python 块复用 `Rich/add/mul/neg/temporal`；新增辅助函数仅用于本页的精确样本核验。预期值由 §18–22 的公式和手算反例规定：历史分配档案为 $14/16$，来源交换在时刻 $1$ 处有四个不匹配的新点；时间复合包括六事件十二条跨边的合法三元组、空中间合法例及相邻 guard 空真而两括号失败的例子。另用含空档案、空当前区域、非空旧档案、未选高时刻点的样本逐对检查 (TH+)、(TH*) 及精确 guard，C2 两次右乘后 $\max E=10/11$，接 $U_{11}$ 恰一侧失败。

卷积测试在三个给定格点、系数 $\{-1,0,1\}$ 的非零小支撑样本中核对极值系数及唯一拆分，另检验 $2\delta_0-\delta_v$ 的增广为 $1$、不属单位族，并在明示有限候选中排除它的逆；无零因子和全部单位分类只由命题 26–27 证明。树公式比较不同括号、不同叶时刻及正整数延迟；参考点测试使用一般整数矩阵、非单射矩阵和仿射位移，同时检查全部事件数据与参考点的运输，并执行 C3 的 $1/2$ 筛选差异。stdout 中的新增计数均由实际执行累加或读取样本结果，有限运行不证明无限全称命题、全部上下文或所有整数仿射映射。


**有限窗口的具体取值。** 时间三元组取空档案、$U_{-1},U_0,U_1,U_2$ 及档案为时刻 $4$ 的正负对但当前区域为空的六个状态。$\Theta$ 的八个状态取空档案、$U_{-1},U_0,U_1$、上述空当前区域状态、C2 的两状态和正点时刻 $0$/负点时刻 $9$ 的状态；每个状态核验补集、三种空间筛选、三种平移，并在整数阈值 $[-3,12]$ 上探测左右 guard。卷积极值的三个格点为 $0,v,h$（沿用 §17.3）；逆候选仅取 $-v,0,v$ 上三系数在 $\{-1,0,1\}$ 的 $27$ 个函数。树枚举三叶和四叶的全部二叉括号，叶时刻各取 $\{-2,0,3\}$、延迟取 $1,2,3$；丰富树另每个括号取叶时刻 $(0,1,\ldots,n-1)$。参考点用 $0,(1,2,-1)$，矩阵用恒等、$2I$、$(x_1,x_2,x_3)\mapsto(x_1+x_2,x_2,-x_3)$ 和 C3 的投影，位移为 $(2,-1,3)$；输入取 $U_0$、§17.3 的 $X,Y$ 及空当前区域状态。

**本批实际运行收据（2026-09-09）。** 在固定候选 `feec239217c30601cca92c53620492516bec915a` 的指定工作树中，亲跑附录原 `sed ... | sed ... | python3 -` 提取命令；首次及将新增同构计数改为实际调用累加后的重跑均退出 `0`。最终执行包含原检查、PR1 检查及 PR2 新增检查，末行实得 `ALL_FINITE_CHECKS_PASSED`。下面仅列最终执行的 PR2 stdout，不把原历史输出当作本批收据：

```text
pr2_history: distributivity_archives=14,16 ordered_source_new_events=4,4 additive_isomorphisms=3
pr2_temporal: triples=216 defined=56 legal_archive=6 legal_edges=12 empty_middle_adjacent_guards_insufficient=True
pr2_theta: pairs=64 unary=56 integer_thresholds=256 amplification_cases=2 archive_maxima=10,11 following_U11=defined,failed time_filter=1,0
pr2_theta_laws: rich_triples=64 associativity_maxima=2,3 zero_absorbing=False
pr2_extrema: nonzero_samples=26 pairs=676 products_delta0=2 signed_delta_inverses=10 nonunit_augmentation=1 inverse_candidates_rejected=27
pr2_clock: depth_cases=1377 rich_trees=7 translations=147 scaled_delay_cases=675 fixed_delay_scaling_rejected=True
pr2_reference: rich_pairs=32 affine_transports=128 space_units=52 noninjective_events=4 direct_image_filter=1,2 pullback_filter=2
ALL_FINITE_CHECKS_PASSED
```

这些结果只判所列样本；完整一般证明位于命题 24–36。canonical ingest 与差分检查的实际命令、退出码、新增 atom/backfill 及 residual-open 计数由本 worker 的 runner 结果工件记录，独立评审与 git/GitHub 生命周期交由 caller 接续。

<a id="p1-joint-image"></a>

## 24. P1/R1：联合时间—空间摘要的全部实际像

§20.2 已给出同一 $\Theta$ 下时间筛选仍可区分的状态。本节和下一节为这个具体缺口增加联合时间—空间电荷，并刻画它在全部合法平衡丰富表示上的实际像及严格观察能力。沿用定义 1–21 的载体 $\mathcal B$、默认空间维数 $d=3$、共同零参考点及定义 6 的 $\max+1$ 档案乘法。这里的“新”指相对于现稿的扩展；有限符号构造与严格上下文方法分别复用 §15 和 §14，端点必要性复用命题 30。若预先固定任意有限 $d\ge1$，将下文 $\mathbb Z^3$ 一致换成 $\mathbb Z^d$，同一构造及证明仍适用。

### 24.1 联合电荷及其与旧摘要的关系

**定义 22（联合时间—空间摘要）。** 令

$$
K=\mathbb Z\times\mathbb Z^3,\qquad
\mathcal L=\mathbb Z^{(K)}
=\{c:K\to\mathbb Z:\operatorname{supp}(c)\text{ 有限}\},
\qquad \varepsilon c=\sum_{(n,p)\in K}c(n,p).
$$

括号上标只取有限支撑函数；上述求和实际只在有限支撑上进行。记 $\delta_{(n,p)}\in\mathcal L$ 为该联合单元上的单点质量，$\delta_p\in R$ 仍指 §15 的空间单点质量。对 $X=(C,A)\in\mathcal B$ 定义

$$
\begin{aligned}
W_X(n,p)&=\sum_{\substack{e\in\Omega_X\\t_X(e)=n,\ x_X(e)=p}}\sigma_X(e),\\
Z_X(n,p)&=\sum_{\substack{e\in A_X\\t_X(e)=n,\ x_X(e)=p}}\sigma_X(e),\\
\Xi(X)&=(W_X,Z_X,m_X,M_X,s_X).
\end{aligned}
\tag{TS}
$$

三个端点直接沿用定义 20：$m_X=\min t_X[E_X]$、$M_X=\max t_X[E_X]$、$s_X=\max t_X[\Omega_X]$，其类型分别为 $\mathbb Z\cup\{+\infty\}$、$\mathbb Z\cup\{-\infty\}$、$\mathbb Z\cup\{-\infty\}$。空档案时 $m=+\infty,M=-\infty$，空当前区域时 $s=-\infty$；全部比较在扩展整数全序中进行。因此 $\Xi$ 的值域先置于

$$
\mathcal L^2\times(\mathbb Z\cup\{+\infty\})
\times(\mathbb Z\cup\{-\infty\})^2,
$$

而它的实际像将在命题 37 中完全刻画。$W$ 是当前背景 $\Omega$ 的电荷，$Z$ 是当前选择 $A$ 的电荷，均不计 $E\setminus\Omega$。

旧 $\pi$ 按位置分组时已把时间求和。确切地，定义有限推送 $\operatorname{sp}:\mathcal L\to R$ 为

$$
\operatorname{sp}(c)(p)=\sum_{n\in\mathbb Z}c(n,p).
$$

按同一有限事件和重新分组便有

$$
\pi(X)=(\operatorname{sp}(W_X),\operatorname{sp}(Z_X)),\qquad
\Theta(X)=((\operatorname{sp}(W_X),\operatorname{sp}(Z_X)),m_X,M_X,s_X).
\tag{TS-SP}
$$

所以 $\Xi$ 决定 $\Theta$，反向不成立。直接用 §20.2 末段的已给见证：两份当前区域各有一个所选正点、一个未选负点，位置均为零；正点分别在时刻 $0,5$，负点均在 $9$，另各有不属于当前区域的时刻 $0,10$ 档案点，偏序为空。两者分别有

$$
\begin{aligned}
(W_X,Z_X)&=(\delta_{(0,0)}-\delta_{(9,0)},\delta_{(0,0)}),\\
(W_Y,Z_Y)&=(\delta_{(5,0)}-\delta_{(9,0)},\delta_{(5,0)}),
\end{aligned}
$$

而 $\Theta(X)=\Theta(Y)=((0,\delta_0),0,10,9)$。时刻 $0$ 的筛选给 $1,0$。因此 $\ker\Xi\subsetneq\ker\Theta$；$\Xi$ 不是旧 $\Theta$ 的别名。

### 24.2 三个实现分支及显式有限构造

**命题 37（全部实际像，repo-derived）。** 令 $\mathcal D_{\rm ts}$ 为满足下列三个互斥分支之一的元组 $(W,Z,m,M,s)$ 的集合，则

$$
\Xi[\mathcal B]=\mathcal D_{\rm ts}.
\tag{TS-IMAGE}
$$

1. **空档案分支：** $W=Z=0$，$m=+\infty$，$M=s=-\infty$。
2. **非空档案、空当前区域分支：** $W=Z=0$，$m,M\in\mathbb Z$，$m\le M$，$s=-\infty$。
3. **非空当前区域分支：** $W,Z\in\mathcal L$，$m,s,M\in\mathbb Z$，并且

$$
m\le s\le M,\qquad \varepsilon W=0,\qquad
\operatorname{supp}(W)\cup\operatorname{supp}(Z)
\subseteq([m,s]\cap\mathbb Z)\times\mathbb Z^3.
\tag{TS-SUPPORT}
$$

第三分支没有要求 $s$ 出现在任一有符号支撑中；正负抵消可以使真实最高当前时刻不可见。

**证明（必要性）。** 有限事件只占有限个联合单元，所以 $W,Z\in\mathcal L$；当前平衡给 $\varepsilon W=0$。空档案迫使 $\Omega=A=\varnothing$，得到第一分支。档案非空而当前区域为空时，档案极值是有限整数且有序，两个电荷为零，得到第二分支。当前区域非空时，它包含于档案，故三个极值均有限且 $m\le s\le M$；每个贡献事件的时间都位于 $[m,s]$，于是得到 (TS-SUPPORT)。这三种空性情形穷尽全部输入。

**证明（第三分支的构造）。** 给定满足 (TS-SUPPORT) 的元组，置有限集 $S=\operatorname{supp}(W)\cup\operatorname{supp}(Z)$。使用 §1 的整数有限编码、Kuratowski 有序对和不同自然数标签，对每个 $a=(n,p)\in S$ 放置

$$
e^A_{a,i}=(0,(a,i))\quad(0\le i<|Z(a)|),\qquad
e^U_{a,j}=(1,(a,j))\quad(0\le j<|W(a)-Z(a)|).
$$

这里 $i,j\in\mathbb N$。这些出现标识全部属于 $HF$ 且两两不同。前一组全部选中，符号为 $Z(a)$ 的符号；后一组全部未选，符号为 $W(a)-Z(a)$ 的符号。两组时间都取 $n$，位置都取 $p$。系数为零时该组为空，不需要给零指定事件符号。把所有这些事件组成初始当前区域 $\Omega_0$，把前一组组成 $A$，便有选中电荷 $Z$、未选电荷 $W-Z$，从而当前总电荷逐单元恰为 $W$。

若 $\Omega_0$ 没有时刻 $s$ 的事件，再加标识为 $(2,0),(2,1)$ 的两个**未选**当前事件，均位于 $(s,0)$，符号分别为 $+1,-1$；若已有时刻 $s$ 的事件则不加。这对事件同时不改变 $W$ 和 $Z$。所得 $\Omega$ 非空，所有时间位于 $[m,s]$，且最大时刻恰为 $s$。

接着对 $\{m,M\}$ 中尚未出现在 $t[\Omega]$ 的每个不同整数 $r$，添加档案事件 $e^{\rm arc}_r=(3,r)$，置 $t(e^{\rm arc}_r)=r$、$x(e^{\rm arc}_r)=0$、$\sigma(e^{\rm arc}_r)=+1$，并使它不属于 $\Omega$。$m=M$ 时这个集合至多要求一个填充事件；这些档案点也不会与前三类出现标识碰撞。令 $E$ 为 $\Omega$ 与这些填充点的并。对全部事件统一取来源 $\operatorname{leaf}(0)$，严格偏序取空关系，至此 $t,x,\sigma,\rho$ 在整个 $E$ 上均已定义。

空关系是合法严格偏序，时标条件空真；$A\subseteq\Omega\subseteq E$。填充点只改变档案端点，不参与当前平衡，故 $u(C)=\varepsilon W=0$。档案内全部时刻位于 $[m,M]$，且两个端点都达到；当前最高时刻为 $s$，所以构造确实实现给定 $\Xi$。这也说明实现不需要增加因果或来源的额外假设。

**证明（其余分支）。** 第二分支取 $E=\{(3,m),(3,M)\}$、$\Omega=A=\varnothing$；标识 $(3,r)$ 的时间为 $r$，位置为零、符号为正、来源为 leaf(0)，偏序为空。若 $m=M$，档案恰有一个事件。第一分支取全部事件数据为空的情境。两者都平衡并实现相应端点。由必要性与三个构造得到 (TS-IMAGE)。证毕。

**命题 38（隐形最高时刻的精确当前事件成本，repo-derived）。** 在第三分支内，定义有限整数和

$$
D(W,Z)=\sum_{(n,p)\in K}\bigl(|Z(n,p)|+|W(n,p)-Z(n,p)|\bigr),
$$

以及

$$
\eta_s=
\begin{cases}
1,&\forall p\in\mathbb Z^3,\quad W(s,p)=Z(s,p)=0,\\
0,&\text{否则}.
\end{cases}
$$

则所有实现中的最小当前事件数恰为

$$
\min_{\substack{X\in\mathcal B\\\Xi(X)=(W,Z,m,M,s)}}|\Omega_X|
=D(W,Z)+2\eta_s.
\tag{TS-COST}
$$

**证明。** 固定任一实现。在联合单元 $a$，选中事件每个符号绝对值为 $1$，其数量至少为 $|Z(a)|$；未选事件的电荷为 $W(a)-Z(a)$，其数量至少为 $|W(a)-Z(a)|$。各单元及两类事件互不相交，求和得到 $D(W,Z)$ 的下界。

若 $\eta_s=1$，则时间 $s$ 的每个位置单元中，选中组和未选组的净电荷都为零。但 $s$ 是实际达到的当前最大时刻，至少一组非空；非空的零电荷组必须同时含正、负事件，至少有两个。$D$ 在全部时间 $s$ 的单元上贡献为零，故这两个事件是上述下界之外的额外成本。若 $\eta_s=0$，原下界已经适用，无须额外加项。

命题 37 的初始构造恰用 $D(W,Z)$ 个当前事件。它在时间 $s$ 有事件，当且仅当某个 $Z(s,p)$ 或 $W(s,p)-Z(s,p)$ 非零；这又等价于 $\eta_s=0$。因此构造只在 $\eta_s=1$ 时补上那两个未选抵消事件，而端点填充均不入当前区域，恰好达到 (TS-COST)。证毕。

这里最小化的是 $|\Omega|$，没有同时给出整个档案 $|E|$ 的最小值。零电荷 $W=Z=0$ 可以出现在三个分支中，不能据此判断当前区域是否为空。例如 $m=0,s=5,M=4$ 不可实现，而 $m=0,s=M=5$、$W=Z=0$ 可实现，且最少需要两个当前事件。

满像也不等于任意固定情境的容量。固定 $C$ 后，令 $n_+(n,p),n_-(n,p)$ 为当前区域中各联合单元的正、负事件数，则每个选择仍必须且恰可满足

$$
-n_-(n,p)\le Z(n,p)\le n_+(n,p)\qquad((n,p)\in K).
$$

这是命题 19 将空间单元换成联合单元的直接应用：非负目标选所需正事件，负目标选所需负事件，各单元互不干扰。命题 37 允许构造新的完整情境，未把这个固定容量限制消去。

<a id="p1-joint-language"></a>

## 25. P1/R2：联合区域语言的精确更新与观察核

### 25.1 固定操作、精确定义域及闭合更新

**定义 23（联合区域语言）。** 对任意预先固定的集合 $B\subseteq K$，令

$$
F_B(C,A)=(C,\{e\in A:(t(e),x(e))\in B\}).
$$

它只筛选 $A$，保持整个 $C$，包括 $E,\Omega$、时间、位置、符号、来源和偏序。对每个固定 $k\in\mathbb Z$，$T_k$ 仍是 §3 的全档案时间平移；在 $\mathcal L$ 上记

$$
(\tau_k c)(n,p)=c(n-k,p).
$$

有限端点加 $k$，两个无穷哨兵保持原值。定义有限支撑乘积 $\odot:\mathcal L^2\to\mathcal L$ 为

$$
(c\odot d)(n,r)=
\sum_{\substack{(a,p)\in\operatorname{supp}(c),\ (b,q)\in\operatorname{supp}(d)\\
\max(a,b)+1=n,\ p+q=r}}
c(a,p)d(b,q).
\tag{TS-PRODUCT}
$$

求和域是两个有限支撑的 Cartesian 积的子集，结果支撑包含于映射 $((a,p),(b,q))\mapsto(\max(a,b)+1,p+q)$ 的有限像，故类型闭合。这里不假设 $\odot$ 结合，也不把 $\mathcal L$ 在这个乘法下称为旧空间卷积环。

指定签名为

$$
\Sigma_{\rm ts}=\{\boxplus,\boxtimes,N,\triangleright\}
\cup\{F_B:B\subseteq K\}\cup\{T_k:k\in\mathbb Z\}.
\tag{TS-LANG}
$$

三个二元符号 $\boxplus,\boxtimes,\triangleright$ 的输入类型都是 $\mathcal B^2$，成功输出属于 $\mathcal B$，其中只有 $\triangleright$ 为部分操作；$N,F_B,T_k$ 为 $\mathcal B\to\mathcal B$ 的总操作。上下文沿用定义 16：恒等孔、每个操作的全部参数槽位、其余槽位中任意固定的丰富参数，以及任意有限复合。每个 $B,k$ 及每个丰富参数在一个上下文中固定；参数不限于可由常数符号命名的对象，孔不自动复制，也不限制为某个预定的有限深度。

终端值域取 $\mathbb Z_\bot=(\{1\}\times\mathbb Z)\sqcup\{\bot\}$。上下文 $C$ 的正常结果观察为 $(1,q(C(X)))$，任何一步无定义就观察为 $\bot$，失败严格传播。用 $X\approx_{\rm ts}Y$ 表示全部这些上下文的严格观察相同。签名不含来源、出现身份或因果查询。

**命题 39（全部精确更新，repo-derived）。** 对 $X,Y\in\mathcal B$，并行加法满足

$$
\Xi(X\boxplus Y)=
(W_X+W_Y,Z_X+Z_Y,\min(m_X,m_Y),\max(M_X,M_Y),\max(s_X,s_Y)).
\tag{TS-ADD}
$$

严格时间复合的准确域为

$$
(X,Y)\in\operatorname{dom}(\triangleright)
\iff M_X<m_Y;
\qquad
\Xi(X\triangleright Y)=\Xi(X\boxplus Y)\quad\text{在此域上}.
\tag{TS-GUARD}
$$

沿用命题 29 的函数 $\gamma$，令

$$
g=\gamma(s_X,s_Y)=
\begin{cases}
-\infty,&s_X=-\infty\text{ 或 }s_Y=-\infty,\\
\max(s_X,s_Y)+1,&s_X,s_Y\in\mathbb Z.
\end{cases}
$$

则默认档案乘法满足

$$
\Xi(X\boxtimes Y)=
(W_X\odot W_Y,Z_X\odot Z_Y,\min(m_X,m_Y),\max(M_X,M_Y,g),g).
\tag{TS-MUL}
$$

其余全部更新为

$$
\begin{aligned}
\Xi(NX)&=(W_X,W_X-Z_X,m_X,M_X,s_X),\\
\Xi(F_BX)&=(W_X,\mathbf1_BZ_X,m_X,M_X,s_X),\\
\Xi(T_kX)&=(\tau_kW_X,\tau_kZ_X,m_X+k,M_X+k,s_X+k).
\end{aligned}
\tag{TS-UNARY}
$$

端点平移按上述哨兵约定解释。对任意 $c,d\in\mathcal L$ 以及 $X\in\mathcal B$，还有

$$
q(X)=\varepsilon Z_X,\qquad
\varepsilon(c\odot d)=(\varepsilon c)(\varepsilon d).
\tag{TS-READ}
$$

这些式子在命题 37 的实际载体 $\mathcal D_{\rm ts}$ 上给出总操作及一个恰好保域的部分操作，成功输出全部仍在该实际像中。

**证明。** 并行加法在每个联合单元把两份带标签事件的电荷相加；档案及当前区域的时刻集合分别取并，所以极值为 (TS-ADD) 的 min/max。时间复合只增加跨边，不改这些事件属性或区域，故有定义时更新相同。两档案非空时，定义 5 的全称条件恰等价于最大左时刻小于最小右时刻。左档案为空时 $M_X=-\infty<m_Y$ 总成立，右档案为空时 $M_X<m_Y=+\infty$ 总成立，两者都空时亦成立。这正好保留空真，而不是只检查当前区域或所选事件。

乘法的新当前事件来自全部 $\Omega_X\times\Omega_Y$。在两个固定父单元 $(a,p),(b,q)$ 内，时间、位置及符号规则分别为 $\max(a,b)+1,p+q$ 及符号相乘。该组的全部当前电荷为 $W_X(a,p)W_Y(b,q)$，所选电荷为 $Z_X(a,p)Z_Y(b,q)$。再按输出单元归组，恰得两个 $\odot$。旧档案被完整保留，但不在新当前区域，所以剖面中没有旧档案的额外线性项。

新当前区域为空当且仅当至少一个父当前区域为空；这由实际事件对的 Cartesian 积判断，不能由某个电荷是否为零判断。两区域都非空时，其最高时刻各自达到；所有新时刻至多为 $\max(s_X,s_Y)+1$，取达到最高时刻的父点便达到这个界，所以新最高时刻为 $g$。每个新点都晚于其两个父点，而父点已经在旧档案中，因此新点不会降低旧档案并集的最小时刻；最大时刻必须同时计两份旧档案及新点，得到 $\max(M_X,M_Y,g)$。无新点时同一公式以 $g=-\infty$ 给出旧档案并集的端点。这正是命题 29 的端点更新，包含空档案及空当前区域的情形。

补集的选中电荷逐单元为 $W-Z$。筛选只从 $A$ 中删事件，故只对 $Z$ 乘掩码，$W$ 与三个端点不变。平移逐事件将时间 $n$ 运输到 $n+k$，得到 $\tau_k$ 及有限极值的平移；空性不变，故哨兵不变。最后，(TS-PRODUCT) 中每个父支撑对恰有一个输出单元，对全部输出单元求和可重排为

$$
\sum_{(a,p)}\sum_{(b,q)}c(a,p)d(b,q)
=\left(\sum_{(a,p)}c(a,p)\right)
 \left(\sum_{(b,q)}d(b,q)\right),
$$

从而得到 (TS-READ)；$q=\varepsilon Z$ 直接来自选择的有限分组。只对输出时间求和，也得到 $\operatorname{sp}(c\odot d)=\operatorname{sp}(c)*\operatorname{sp}(d)$，所以遗忘联合时间数据后逐式回到旧空间及端点更新。

闭包在实际像上证明：给任意一个或两个 $\mathcal D_{\rm ts}$ 元素，命题 37 提供合法丰富实现；命题 1–3 及筛选、平移的定义保证相应丰富运算在所写域内合法并保持平衡。上述式子恰是其 $\Xi$，故仍在 $\mathcal D_{\rm ts}$，且不随实现的选择而变。唯一部分域也只由摘要中的 $M_X,m_Y$ 判定。这里仅使用原像的存在，不要求在所有纤维上同时选代表，更不把形式乘积值域中的不可实现元组混入载体。证毕。

### 25.2 全部有限严格上下文的精确观察核

**命题 40（联合摘要的观察核及像上恢复，repo-derived）。** 对 (TS-LANG) 的完整上下文族，

$$
\approx_{\rm ts}=\ker\Xi.
\tag{TS-KERNEL}
$$

因此 $\Xi$ 在核包含意义下是该指定语言的最粗充分读数。确切地，对任意集合 $H$ 和任意总读数 $h:\mathcal B\to H$，若 $h(X)=h(Y)$ 蕴含全部该语言上下文的严格观察相同，则存在唯一函数

$$
\kappa:h[\mathcal B]\longrightarrow\mathcal D_{\rm ts},
\qquad \kappa(h(X))=\Xi(X)\quad(X\in\mathcal B).
\tag{TS-RECOVERY}
$$

**证明（充分性）。** 设两输入有相同 $\Xi$。在任一基本上下文中，其余槽位使用同一个固定丰富参数，故参数的摘要相同。命题 39 给出两侧同步成功或失败，成功时输出摘要相同；这对每个二元槽位及所有一元符号均成立。对有限复合作归纳，内层失败时两侧严格失败，内层成功时其摘要相同，可继续用外层的相同域和更新式。恒等孔是归纳起点，终端由 $q=\varepsilon Z$ 给相同正常观察。因此 $\ker\Xi\subseteq\approx_{\rm ts}$。这使用定义 16 的全部上下文，并非只检查某个有界词表。

**证明（必要性）。** 对每个 $a=(n,p)\in K$，语言中都有单点掩码，而且

$$
q(F_{\{a\}}X)=Z_X(a),\qquad
q(F_{\{a\}}NX)=W_X(a)-Z_X(a).
\tag{TS-SINGLETON}
$$

若 $X\approx_{\rm ts}Y$，这两族读数逐单元相同，先给 $Z_X=Z_Y$，再相加给 $W_X=W_Y$。此外每个旧空间筛选 $F_S$ 恰是联合柱集筛选 $F_{\mathbb Z\times S}$；其余旧符号及其定义域完全相同。因此旧 $\Sigma_{\rm st}$ 的每个上下文都是本语言上下文，观察等价蕴含旧观察等价。由命题 30，$m_X=m_Y,M_X=M_Y,s_X=s_Y$。这一端点必要性直接消费旧定理，未将它重新列作本轮的新成果。合并即得 $\Xi(X)=\Xi(Y)$，证明 (TS-KERNEL)。

**证明（恢复及最粗性）。** 对充分的 $h$，由刚证的核等式有 $\ker h\subseteq\ker\Xi$。关系图

$$
\{(h(X),\Xi(X)):X\in\mathcal B\}
\subseteq h[\mathcal B]\times\mathcal D_{\rm ts}
$$

在每个 $h$ 的实际像点上至少有一个值，且所有原像由核包含给出同一个值，故它本身就是函数 $\kappa$ 的图。任何满足 (TS-RECOVERY) 的函数在每个实际像点都被强制定值，所以唯一。这不需要挑选历史代表，也不要求 $h$ 对整个 $H$ 满射；未命中的 $H\setminus h[\mathcal B]$ 不属于所断言的恢复域。$\Xi$ 自身的充分性已证，因而确为最粗充分读数。证毕。

这仍是 §14 的严格部分代数语义：正常零观察 $(1,0)$ 与失败 $\bot$ 不同，遗漏任一参数槽位、只允许部分丰富参数或截断上下文深度都不是本命题的语言。命题 16 的最大强保域同余框架在这里继续适用；恢复没有计算性或编码字节数最优的含义。

### 25.3 固定联合父单元谓词的配对扩展

**定义 24（固定时间—空间配对选择）。** 固定任意 $P\subseteq K\times K$。对 $X,Y\in\mathcal B$，操作 $M_P(X,Y)$ 使用定义 6 的完整乘积情境，包含两份旧档案及来自全部 $\Omega_X\times\Omega_Y$ 的新当前事件；仅把选择改为

$$
\{p_{ef}:e\in A_X,\ f\in A_Y,
\ ((t_X(e),x_X(e)),(t_Y(f),x_Y(f)))\in P\}.
$$

同时定义 $\odot_P:\mathcal L^2\to\mathcal L$：在 (TS-PRODUCT) 的同一有限求和中多乘因子 $\mathbf1_P((a,p),(b,q))$，即

$$
(c\odot_Pd)(n,r)=
\sum_{\substack{(a,p)\in\operatorname{supp}(c),\ (b,q)\in\operatorname{supp}(d)\\
\max(a,b)+1=n,\ p+q=r}}
\mathbf1_P((a,p),(b,q))c(a,p)d(b,q).
\tag{TS-PAIR}
$$

**命题 41（配对扩展仍以 $\Xi$ 为精确摘要，repo-derived）。** $M_P:\mathcal B^2\to\mathcal B$ 总定义。仍令 $g=\gamma(s_X,s_Y)$，则

$$
\Xi(M_P(X,Y))=
(W_X\odot W_Y,Z_X\odot_P Z_Y,
\min(m_X,m_Y),\max(M_X,M_Y,g),g).
\tag{TS-PAIR-UPDATE}
$$

将全部这些固定操作加入语言，令

$$
\Sigma_{\rm ts}^{\rm pair}
=\Sigma_{\rm ts}\cup\{M_P:P\subseteq K\times K\},
$$

则仍有 $\approx_{\Sigma_{\rm ts}^{\rm pair}}=\ker\Xi$，且任何对此扩展语言充分的总读数仍满足命题 40 的实际像上唯一恢复性质。

**证明。** $M_P$ 只限制完整乘积情境中的选择，未改变 $\Omega$，所以原乘积的平衡和合法性保持。每个固定父联合单元对中，$P$ 的真假恒定；该组所选电荷因而恰为 $\mathbf1_P((a,p),(b,q))Z_X(a,p)Z_Y(b,q)$。按输出单元有限分组就得到 (TS-PAIR)。当前背景、旧档案及时间数据完全沿普通乘积，故 $W$ 与三个端点仍由 (TS-MUL) 更新，而不能给 $W$ 也乘配对掩码。

式 (TS-PAIR-UPDATE) 只依赖输入摘要，且输出是合法丰富状态的实际像；于是对新增基本上下文也能应用命题 40 的充分性归纳。原单点探针和旧端点上下文仍在扩展语言中，必要性保持，所以观察核不变；恢复图的证明也不变。证毕。

这里的 $P$ 固定在父时间—空间单元上，未被推广为任意来源、出现身份或因果谓词。它可以不对称，也不必使受限读数等于普通标量乘法；定义 14／命题 12 的遗漏对公式仍适用。这一扩展新增的是所写有限和的精确可观察性，没有改动完整乘积背景的语义。

<a id="p1-joint-boundaries"></a>

## 26. P1 的区分见证、来源与边界

### 26.1 联合数据、完整背景与档案端点的见证

**反例 D1（时间边缘与空间边缘不能替代联合剖面）。** 取 $v\in\mathbb Z^3\setminus\{0\}$，令

$$
Z_X=\delta_{(0,0)}+\delta_{(1,v)},\qquad
Z_Y=\delta_{(0,v)}+\delta_{(1,0)}.
$$

每个所选正事件都在同一联合单元配一个未选负事件，取互异的 $HF$ 出现标识、来源 leaf(0)、空偏序及 $E=\Omega$。两份状态都合法平衡，$W_X=W_Y=0$，$m=0,M=s=1$。时间边缘 $n\mapsto\sum_pZ(n,p)$ 在 $0,1$ 各为 $1$；空间边缘 $p\mapsto\sum_nZ(n,p)$ 都为 $\delta_0+\delta_v$。然而

$$
q(F_{\{(0,0)\}}X)=1,\qquad q(F_{\{(0,0)\}}Y)=0.
$$

所以即使同时保存完整联合背景 $W$ 和三个端点，另加两个所选边缘仍不足以回答联合区域筛选；丢失的是时间与位置的配对信息。

**反例 D2（掩码不能同时删去背景）。** 取两个未选当前事件，分别为 $(0,0)$ 处的正事件及 $(1,0)$ 处的负事件，令 $E=\Omega,A=\varnothing$，来源 leaf(0)，偏序为空。于是

$$
W=\delta_{(0,0)}-\delta_{(1,0)},\qquad Z=0.
$$

先施 $F_\varnothing$，背景完全不动；再施 $N$ 就选中这两个当前事件，最后筛选单元 $(0,0)$，因此

$$
q(F_{\{(0,0)\}}N F_\varnothing X)=1.
$$

若错误地在第一步把 $W$ 也筛成零，后两步将误报 $0$。这是 §15.2 背景保留原则在联合单元上的直接见证。

**反例 D3（抵消隐藏的最高当前时刻仍能被观察）。** 对 $a\in\{0,9\}$，构造 $X_a$：当前区域是 $(a,0)$ 处两个未选的正负事件；另各有不属于当前区域、时刻为 $0,10$ 的两个正档案事件。各出现标识互异，全部位置为零、来源 leaf(0)，偏序为空。两者满足

$$
W=Z=0,\qquad m=0,\quad M=10,\quad s=a.
$$

沿用命题 30 的 $U_t=T_t(\mathbf i(1))$。令 $C(X)=(X\boxtimes U_0)\boxtimes U_0$。两次乘积的新选择一直为空，但当前事件真实存在；$X_0$ 的当前最高时刻依次为 $1,2$，$X_9$ 的为 $10,11$。故

$$
M_{C(X_0)}=10,\qquad M_{C(X_9)}=11.
$$

再接 $\square\triangleright U_{11}$，前者成功且 $q=0+1=1$，后者因 $11<11$ 为假而失败。零有符号支撑不能代替 $s$。这是命题 30 及 §20.2 反例 C2 的既有端点放大模式在空选择上的应用；原 C2 选了正事件，成功读数为 $2$，这里空选择使成功读数为 $1$，两者不混用。

**反例 D4（空当前区域仍保留全档案守卫）。** 令 $V_{ij}$ 的当前区域和选择都为空，档案仅有时刻 $i,j$ 的两个不同事件，位置为零、符号为正、来源 leaf(0)，偏序为空，其中 $i<j$。它们均有 $W=Z=0,s=-\infty$。$V_{02}$ 与 $V_{12}$ 的 $M$ 同为 $2$，但前接 $U_0$ 时，$U_0\triangleright V_{02}$ 因 $0<0$ 为假而失败，$U_0\triangleright V_{12}$ 因 $0<1$ 为真而成功，读数为 $1$。$V_{01}$ 与 $V_{02}$ 的 $m$ 同为 $0$，但后接 $U_2$ 时，$V_{01}\triangleright U_2$ 成功且读数为 $1$，$V_{02}\triangleright U_2$ 失败。空档案 $0_\varnothing$ 则在所有整数阈值的左右 guard 中都成功，与这些有限端点不同。这里复用命题 30 的 (TP) 阈值模式，说明空选择、甚至空当前区域都不能抹去档案端点。

**反例 D5（来源查询及任意配对关系超出摘要）。** 两份 $U_0$ 型状态都取同样的两事件、时间与位置为零、空偏序，只选正事件；仅将所选正事件的来源分别设为 leaf(0)、leaf(1)，未选负事件的来源都为 leaf(0)。二者的摘要相同：

$$
\Xi=(0,\delta_{(0,0)},0,0,0).
$$

按来源是否为 leaf(0) 筛选，读数却为 $1,0$。若与一个固定的、所选正来源为 leaf(0) 的 $U_0$ 型参数相乘，并只选来源相等的父对，受限读数也为 $1,0$。所以固定丰富参数并不能使任意来源配对成为 (TS-PAIR) 的特例；同一个联合单元内部仍可有不同来源。

同理，§17.1 反例 B2 的两状态已有相同事件及时间、位置、符号、选择，只差合法偏序。它们在本节都有 $W=0$、$Z=\delta_{(0,0)}+\delta_{(1,0)}$、$(m,M,s)=(0,1,1)$，但对共同有效的 $D=\{b\}$ 作因果过去筛选，仍给 $2,1$。§14 的所选事件 $e$ 重命名为 $e'$ 的见证也保持 $\Xi$，固定身份筛选 $A\cap\{e\}$ 仍给 $1,0$。这些旧见证继续划定来源、因果与出现身份查询的边界；命题 41 没有把它们纳入联合区域语言。

### 26.2 有限表示、共同参考点及来源记录

有限支撑使本节的电荷和、推送与配对求和都是精确有限数学对象。任意 $B\subseteq K$ 或 $P\subseteq K\times K$ 的成员关系却不必可计算；实际执行一次掩码更新，需要给出相应有限支撑点或父支撑对上的成员判定。命题 40 的恢复是实际像上的唯一函数，不是对任意 ZFC 区域的通用程序，也不恢复被摘要忘掉的档案历史或固定情境容量。

默认参考点仍为 $o=0$。若显式置于定义 21 的共同纤维 $\mathcal B_o$，只需把 (TS-PRODUCT)、(TS-PAIR) 的位置条件 $p+q=r$ 换成 $p+q-o=r$；同一有限分组证明逐式适用，时间及档案端点不变。命题 34–36 的参考点运输继续承担兼容性，不同参考点的输入仍须先明确运输到共同纤维。这里没有修改旧 $\mathbb Z/\mathbb Q/\mathbb R$ 接口或默认时间规则。

**主数学来源与复用。** 本次 P1/R1–R2 的主定义、命题、证明及区分见证来自实际完成的 GPT PRO 主推理任务 `8a1e6a18-47e3-4d7e-b703-a33b93c4ef87`，模型为 **GPT-6 Astra**，经默认 `company-chatgpt-pro`、`mode:chat`，完成于 **2026-09-09T15:46:54.998Z**；对话为 [GPT PRO：CSA 新扩展主推理](https://chatgpt.com/c/6aa175d8-7ae0-83ec-9289-e9fc818fe147)，所依据的数学源稿 pin 为 `74e9341e5e38615754f82e99430a257a21c5a26c`（简称 `74e9341`）。本次由 `consensus-rnd:sshx` 的单一 codex-cli 实施席依批准的 P1 来源组织中文表述并独立核对；未另派子工作者或请求另一数学 oracle。

本增补归类为 `repo-derived`，其新能力是联合摘要的三分支实际像、隐形最高时刻的精确当前事件成本，以及指定联合区域语言的精确观察核。公开证明已在 §24–25 给出；有限符号实现与分组方法明确复用命题 18–20，严格上下文及像上恢复框架复用命题 16–17、23，档案端点更新与必要性明确复用命题 29–30。§17.2、§23.1 所列成熟同余、上下文等价和有限支撑结构只作已有背景，不冒称外部文献已证明本稿的同一特化，也不作全球优先权、物理定律、量子模型或 Lean 内核验证声明。

本交付只包含 P1/R1–R2。后续 P2 的累积表示与完整剖面固定因子方程、P3 的依赖结构与严格联合响应、以及另立的 JT 结果均不在本次追加中；这一单元不构成持续研究目标的终止声明。后续独立评审、canonical ingest 及 git/GitHub 交付由 caller 接续，本节不预报其通过或合入结果。

<a id="pr3-source"></a>

## 27. PR3 增补 I：来源语言与来源–位置双电荷

本节沿用定义 1 的来源树集合 $T$，将定义 12／命题 9 的联合分箱 $f(e)=(x(e),\rho(e))$ 向全域补零。记全局读数为 $\rho_{\rm src}$，与逐事件来源函数 $\rho(e)$ 区分：

$$
\rho_{\rm src}(X)=(w_X^\rho,z_X^\rho),\qquad
w_X^\rho(p,r)=\sum_{\substack{e\in\Omega_X\\x(e)=p,\ \rho(e)=r}}\sigma(e),\quad
z_X^\rho(p,r)=\sum_{\substack{e\in A_X\\x(e)=p,\ \rho(e)=r}}\sigma(e).
\tag{SRC}
$$

两分量都是 $\mathbb Z^3\times T\to\mathbb Z$ 的有限支撑函数；比较时可先取两对象所用联合 bin 的有限并。这是已有粗观察的特化，不另建来源本体。$q(X)=\sum_{p,r}z_X^\rho(p,r)$，$\sum_{p,r}w_X^\rho(p,r)=0$；对来源求和恢复 $\pi$。

在加法群 $R_T=\mathbb Z^{(\mathbb Z^3\times T)}$ 上定义魔群环乘法：

$$
\delta_{(p,r)}\star\delta_{(q,s)}
=\delta_{(p+q,\operatorname{pair}(r,s))},
\tag{SRC*}
$$

再作 $\mathbb Z$ 双线性延拓。于是
$(c\star d)(u,\operatorname{pair}(r,s))=\sum_{p+q=u}c(p,r)d(q,s)$，而每个叶来源处的乘积系数为零。pair 单射使每个 pair 结点的两个来源子树分解唯一；位置仍需对全部有限支撑拆分求和。这个乘法**非结合、非交换**：三叶的 $\operatorname{pair}(\operatorname{pair}(r,s),t)$ 与 $\operatorname{pair}(r,\operatorname{pair}(s,t))$ 不同；$r\ne s$ 时 $\operatorname{pair}(r,s)\ne\operatorname{pair}(s,r)$，相应基向量已见失败。双线性及有限支撑不授予结合律；§15 交换 rng 的结合证明、§19 的整性与单位分类不施于这个来源 pair 代数。

指定 $\Sigma_{\rm src}=\Sigma_{\rm sp}\cup\{F_L:L\subseteq T\}$，载体仍为 $\mathcal B$，观察与全槽位、全参数、任意有限深度上下文仍按定义 16。

**命题 42（来源双电荷的精确更新，repo-derived）。** 写 $w=w_X^\rho,z=z_X^\rho,w'=w_Y^\rho,z'=z_Y^\rho$，则

$$
\begin{aligned}
\rho_{\rm src}(X\boxplus Y)&=(w+w',z+z'),\\
\rho_{\rm src}(X\boxtimes Y)&=(w\star w',z\star z'),\\
\rho_{\rm src}(NX)&=(w,w-z),\\
\rho_{\rm src}(F_SX)&=(w,\mathbf1_{S\times T}z),\\
\rho_{\rm src}(F_LX)&=(w,\mathbf1_{\mathbb Z^3\times L}z).
\end{aligned}
\tag{SRC-UP}
$$

**证明。** 沿命题 20 的分组求和，在联合 bin 中并行两份电荷相加；新乘积事件的联合属性为 $(p+q,\operatorname{pair}(r,s))$，父 bin 对上的有限双和是系数之积，再向该联合属性推送即为 $\star$。旧档案不入当前区域，故不添线性项。补集在每个 bin 内取未选电荷；两种筛选只掩蔽所选电荷，背景不变。各操作在 $\mathcal B$ 上总定义；增广对 $\star$ 保乘由有限双和给出，所以背景总和仍为零。证毕。

**命题 43（来源语言的观察核，repo-derived）。**

$$
\approx_{\Sigma_{\rm src}}=\ker\rho_{\rm src}.
\tag{SRC-EQ}
$$

**证明。** 充分性按定义 16 归纳，与命题 22 同形：恒等孔保读数；任一基本上下文在两侧使用同一个固定丰富参数，(SRC-UP) 给同一输出读数；有限复合反复应用这些更新，最终 $q$ 由 $z^\rho$ 求和恢复。所有操作总定义，不遗漏部分域。必要性对每个 $p\in\mathbb Z^3,r\in T$ 用签名内的探针

$$
q(F_pF_{\{r\}}X)=z_X^\rho(p,r),\qquad
q(F_pF_{\{r\}}NX)=w_X^\rho(p,r)-z_X^\rho(p,r).
\tag{SRC-REC}
$$

这里 $F_p$ 按 §16 为位置单点筛选，$F_{\{r\}}$ 是来源单树筛选。第一式恢复 $z^\rho$，两式相加恢复 $w^\rho$；因此观察等价蕴含全部坐标相同。证毕。

**旧见证的新读数（repo-derived）。** 以下只给既有对象追加 (SRC) 读数，数值由定义 8、B1 和 (SRC-UP) 直接计算，附录 `pr3_source` 检查这些等式。记 $l_i=\operatorname{leaf}(i)$。B1 两对象分别有 $\rho_{\rm src}=(0,\delta_{(0,l_7)})$ 与 $(0,\delta_{(0,l_8)})$，故在 $(0,l_7)/(0,l_8)$ 处被分开。§4 的 $X=Y=\mathbf i(1),Z=\mathbf i(2)$ 两括号分别有

$$
\begin{aligned}
z_{(X\boxtimes Y)\boxtimes Z}^\rho
 &=\sum_{j=0}^1\delta_{(0,\operatorname{pair}(\operatorname{pair}(l_0,l_0),l_j))},\\
z_{X\boxtimes(Y\boxtimes Z)}^\rho
 &=\sum_{j=0}^1\delta_{(0,\operatorname{pair}(l_0,\operatorname{pair}(l_0,l_j)))}.
\end{aligned}
$$

两者 $w^\rho=0$，所列支撑不交，虽 $q=2$ 相同。§18 的来源交换例分别有 $z^\rho=\delta_{(0,\operatorname{pair}(l_7,l_8))}$ 与 $\delta_{(0,\operatorname{pair}(l_8,l_7))}$，同样 $w^\rho=0$。这些事实证明 $\rho_{\rm src}$ 能区分相应对象，**不证明它恢复档案基数**；§4 的 $28/32$ 仍是档案计数，(SRC) 只数当前区域。

**命题 44（来源与时间混合语言，repo-derived）。**

$$
\approx_{\Sigma_{\rm src}\cup\Sigma_{\rm st}}
=\ker(\rho_{\rm src},m,M,s).
\tag{SRC-ST}
$$

**证明。** 对两种并集复合，$\rho_{\rm src}$ 都逐分量相加；时间复合只添边，其精确守卫仍为命题 29 的 $M_X<m_Y$。乘法、补集、两种筛选按 (SRC-UP)，$T_k$ 不改联合电荷。端点对并集、乘法、补集、平移复用命题 29；来源筛选与空间筛选一样不改 $E,\Omega,t$，故不改端点。现在对**混合**上下文归纳：基本步骤用同一参数、同一守卫，两侧同步失败，或成功并得到同一四元摘要；复合严格传播失败，成功则继续归纳，终端由 $z^\rho$ 求和。故此核充分，证明没有把两条核定理取交当作混合闭包证明。反向，来源单点探针 (SRC-REC) 仍在；命题 30 的平衡 $U_t$、左右时间守卫与有限右乘放大探针也仍在，分别恢复 $m,M,s$。因此所有四个坐标必要。证毕。

本节的联合分箱沿用 §8，核证明沿用 §14–16 的上下文方法，CSA 专用公式与见证标 `repo-derived`；成熟框架与外部文献的范围在 §29、§31 逐项列明，不主张新颖性或完整来源代数分类。

<a id="pr3-causal"></a>

## 28. PR3 增补 J：去身份因果可观测性

### 28.1 属性、剖面与允许语言

**定义 25（去身份因果筛选与因果剖面）。** 令

$$
\mathrm{Attr}=\mathbb Z^3\times\{+1,-1\}\times T,\quad
\alpha(e)=(x(e),\sigma(e),\rho(e)),\quad
U_X(e)=\{\alpha(d):d\in\Omega_X,\ e=d\ \lor\ e\prec_Xd\}\quad(e\in\Omega_X).
\tag{CAU-U}
$$

简写 $e\preceq d$ 为 $e=d$ 或 $e\prec d$。总有 $\alpha(e)\in U_X(e)$，故 $U_X(e)$ 非空；这里是可达后继的**属性集**，不假定 $\mathrm{Attr}$ 自身带偏序，也不计相同属性后继的重数。对任意固定 $Q\subseteq\mathrm{Attr}$ 定义总操作

$$
F_{\downarrow Q}(C,A)
=(C,\{e\in A:\exists d\in\Omega_C\ (\alpha(d)\in Q\ \land\ e\preceq d)\}).
\tag{CAU-F}
$$

目标 $d$ 严格量化于 $\Omega_C$，**不是 $E_C$**，且不要求目标被选中。定义 13 的身份查询 $F_{\downarrow D}$ 及其依赖域原封保留；(CAU-F) 是新增的属性谓词语言，不替代那个操作。令 $b_X(e)=\mathbf1_{A_X}(e)$，定义有限支撑剖面

$$
\Gamma_c(X)(a,b,U)
=\sum_{\substack{e\in\Omega_X\\\alpha(e)=a,\ b_X(e)=b,\ U_X(e)=U}}\sigma(e),
\quad (a,b,U)\in\mathrm{Attr}\times\{0,1\}\times\mathcal P_{\rm fin}(\mathrm{Attr}).
\tag{CAU-P}
$$

未选事件进入 $b=0$ 行，不能只记 $b=1$；下标 $c$ 与 §10 的世界域 $\Gamma$ 区分。指定
$\Sigma_{\rm cau}=\Sigma_{\rm src}\cup\Sigma_{\rm st}\cup\{F_{\downarrow Q}:Q\subseteq\mathrm{Attr}\}$，仍按定义 16 观察严格终端 $q$。本文对本签名的全部量词只指这个明确的操作集合。

### 28.2 推送更新与充分性

**命题 45（剖面的推送更新与充分性，repo-derived）。** 以下操作把剖面系数沿所列映射推送；多个格合并时将系数相加：

| 操作 | 对剖面格 $(a,b,U)$ 的更新 |
| --- | --- |
| $X\boxplus Y$ | 两剖面逐格相加 |
| $NX$ | $(a,b,U)\mapsto(a,1-b,U)$ |
| $F_SX$，$a=(p,\epsilon,r)$ | $(a,b,U)\mapsto(a,b\mathbf1_S(p),U)$ |
| $F_LX$ | $(a,b,U)\mapsto(a,b\mathbf1_L(r),U)$ |
| $F_{\downarrow Q}X$ | $(a,b,U)\mapsto(a,b\mathbf1_{U\cap Q\ne\varnothing},U)$ |
| 有定义的 $X\triangleright Y$ | 左侧 $(a,b,U)\mapsto(a,b,U\cup V_Y)$，$V_Y=\alpha[\Omega_Y]$；右侧不变，再相加 |
| $X\boxtimes Y$ | 输入格对 $((a,b,U),(a',b',U'))\mapsto(a\diamond a',bb',\{a\diamond a'\})$，系数相乘后推送 |
| $T_kX$ | $\Gamma_c$ 不变 |

其中
$a\diamond a'=(p+p',\epsilon\epsilon',\operatorname{pair}(r,r'))$。端点 $(m,M,s)$ 的类型、空哨兵、更新与时间守卫 $M_X<m_Y$ 全部引用 §20 命题 29；三个筛选都不改端点。因此 $(\Gamma_c,m,M,s)$ 对 $\Sigma_{\rm cau}$ 充分。

**证明。** 并行不添跨边；补集及三个筛选只改选择位，不改 $U$。时间复合加入全部左档案到右档案的边，恰使每个左当前事件可达全部右当前属性，右侧没有新后继。乘法按定义 6 只用新事件作当前区域：**该次乘法结果的当前区域是由极大事件组成的反链，新事件无出边**，所以每个新当前事件的 $U$ 恰为自身属性的单点集；这不称整个档案为反链，也不声称之后串接仍无后继。新选择位是父选择位之积，新符号是父符号之积；在父剖面格上分组，有限双和即系数相乘。时移不改属性 $\alpha$ 或偏序，故不改剖面。

还须说明 $V$ 可由剖面本身恢复。$\sigma$ 已在 $a$ 中，同一格的所有贡献同号，非空格不会抵消为零。因此

$$
V_X=\{a:\exists b,U\ \Gamma_c(X)(a,b,U)\ne0\},\qquad
\ker(\Gamma_c,V,m,M,s)=\ker(\Gamma_c,m,M,s).
\tag{CAU-V}
$$

$V$ 不是独立坐标。对 $a=(p,\epsilon,r)$ 的格求和恢复 $w^\rho(p,r)=\sum_{\epsilon,b,U}\Gamma_c(a,b,U)$，只取 $b=1$ 恢复 $z^\rho$，再求和恢复 $q$。对定义 16 的混合上下文归纳：同剖面、同端点在每个基本步骤同步过守卫或失败；成功则按上表和命题 29 得同摘要。复合严格传播失败；成功到终端时 $q$ 相同。这是全部上下文的充分性证明，有限抽样只核对实现。证毕。

### 28.3 自身属性隔离引理

**引理 1（自身属性隔离，repo-derived）。** 固定平衡参数 $U_0=\mathbf i(1)$：当前区域恰有位置 $0$、时刻 $0$、来源 $l_0=\operatorname{leaf}(0)$ 的一正一负两事件，偏序空，只选正事件 $u_+$。对 $v=(p,\epsilon,\tau)$、$\eta\in\{0,1\}$，记 $J_1=\mathrm{id},J_0=N$，以及

$$
\begin{aligned}
H_{Q,v,\eta}(X)&=F_{\downarrow Q}(F_{\{p\}}(F_{\{\tau\}}(J_\eta X))),\\
v^*&=(p,\epsilon,\operatorname{pair}(\tau,l_0)),\\
f_{v,\eta}^X(Q)&=q\bigl(F_{\downarrow\{v^*\}}(H_{Q,v,\eta}(X)\boxtimes U_0)\bigr).
\end{aligned}
\tag{CAU-ISO}
$$

上式 $F_{\{p\}}$ 是位置筛选，$F_{\{\tau\}}$ 是来源筛选。则

$$
f_{v,\eta}^X(Q)
=\sum_{\substack{e\in\Omega_X:\alpha(e)=v,\ b_X(e)=\eta\\U_X(e)\cap Q\ne\varnothing}}\sigma(e).
\tag{CAU-HIT}
$$

**证明。** $J_\eta$ 先将原选择位为 $\eta$ 的事件变为所选；接着三个筛选分别检查位置、来源和原来的 $U\cap Q\ne\varnothing$，完整情境不变。$U_0$ 只选 $u_+$，所以新选中事件恰为 $(e,u_+)$，属性为 $(x(e),\sigma(e),\operatorname{pair}(\rho(e),l_0))$，符号仍为 $\sigma(e)$。乘积当前区域为反链，故最后一次因果筛选在这些当前事件上恰等于自身属性筛选。pair 单射与位置、符号坐标一起保证只有 $\alpha(e)=v$ 映到 $v^*$，得 (CAU-HIT)。每个筛选原已在签名内，右乘用的 $U_0\in\mathcal B$ 是定义 16 允许的固定载体参数；所有表达式只有一个孔，不新增原语。证毕。

附录的 $P_\epsilon(Z)$ 简写为 $F_{\downarrow Q_\epsilon}(Z\boxtimes U_0)$，其中固定谓词 $Q_\epsilon=\{(p,\epsilon,r):p\in\mathbb Z^3,r\in T\}$；在该乘积反链上它隔离原选择的符号。它是合法上下文的辅助名称，不是新增操作。不能改用“早时刻单事件参数”：其当前总电荷为 $\pm1$，不在定义 3 的平衡载体中，定义 16 不允许它作参数。

**反例 D6（裸探针抵消，repo-derived）。** 取 $E=\Omega=\{a,b,c,d\}$，位置全 $0$、来源全 $l_0$，符号 $+,-,+,-$，时刻 $0,1,2,2$，严格关系恰为
$a\prec b,a\prec c,a\prec d,b\prec c,b\prec d$。$X$ 选 $\{a,b\}$，$Y$ 选空集。记 $v_+=(0,+1,l_0),v_-=(0,-1,l_0)$，则 $U(a)=U(b)=\{v_+,v_-\}$。任意 $Q,S,L$ 对 $a,b$ 同取同舍，故
$q(F_{\downarrow Q}F_SF_LX)=q(F_{\downarrow Q}F_SF_LY)=0$。先取 $N$ 后两侧也相等：原来相差的 $a,b$ 仍抵消；**此时不恒为零**，例如 $Q=\{v_+\},S=\{0\},L=\{l_0\}$ 时两侧均为 $1$。引理 1 用 $v=v_+,\eta=1,Q=\{v_+,v_-\}$ 却分别给 $1,0$；$q(P_+(X)),q(P_+(Y))$ 也为 $1,0$。这些读数由所列四事件逐项求和，附录复核。缺的是裸探针证书的隔离步，**不是核等式被反驳**。

### 28.4 必要性与完整 iff

**命题 46（去身份因果语言的观察核，repo-derived）。**

$$
\approx_{\Sigma_{\rm cau}}=\ker(\Gamma_c,m,M,s).
\tag{CAU-EQ}
$$

**证明。** 充分性已由命题 45 的混合上下文归纳给出。必要性比较 $X,Y$ 时，固定共同有限集合 $D=V_X\cup V_Y$。所有 $U_X(e),U_Y(e)$ 均为 $D$ 的非空子集；$v\notin D$ 的行全零。在这对对象的证明中，$D$ 及下列 $Q$ 是**固定的谓词参数**，并非增加一个随输入变化的原语。对每个 $v\in D,\eta\in\{0,1\}$，引理 1 的全部合法上下文读数相等，所以两对象的全部 $f_{v,\eta}(Q)$ 相等。对 $W\subseteq D$，令

$$
h_{v,\eta}(W)=f_{v,\eta}(D)-f_{v,\eta}(D\setminus W)
=\sum_{U\subseteq W}\Gamma_c(v,\eta,U).
\tag{CAU-ZETA}
$$

第一项命中每个非空 $U$；第二项恰扣掉不包含于 $W$ 的那些行，故第二个等号逐事件成立。两次观察在证明外作整数相减，未把复制孔或减读数添加到上下文。有限布尔格上的 Möbius 反演给出

$$
\Gamma_c(v,\eta,U)
=\sum_{W\subseteq U}(-1)^{|U|-|W|}h_{v,\eta}(W).
\tag{CAU-MOB}
$$

反演框架为 `literature-attested`：G.-C. Rota, “On the foundations of combinatorial theory I. Theory of Möbius functions” (1964)，DOI [10.1007/BF00531932](https://doi.org/10.1007/BF00531932)。本式也可直接核对：代入 (CAU-ZETA) 后，每个 $U'\subseteq U$ 的系数为 $\sum_{U'\subseteq W\subseteq U}(-1)^{|U|-|W|}$，即 $U'=U$ 时为 $1$、否则为 $(1-1)^{|U\setminus U'|}=0$。于是两对象逐格剖面相同；空 $D$ 时两剖面直接为空。$V$ 已由 (CAU-V) 决定，不另设恢复 $V$ 的时间串接探针。端点的必要性直接复用 §20 命题 30：那里全是平衡 $U_t$ 参数，属于本签名，分别区分 $m,M,s$。两方向合并得 (CAU-EQ)。证毕。

这是普通 ZFC 内的完整 iff；一般必要性由隔离与有限反演的任意对象证明承担。附录的小样本逐字节恢复不替代这个证明，也不声称 Lean 已验证。

### 28.5 不可观察的精确范围与正面因果分离

在端点相同的前提下，保持 $\Gamma_c$ 的修改在 $\Sigma_{\rm cau}$ 下不可观察；该限定不能丢掉，因为本签名保留时间复合域。仅谈因果关系修改而固定其他数据时，端点自动相同。

**命题 47（同属性关系差的局部不可见性，repo-derived）。** 固定 $E,\Omega,t,x,\sigma,\rho,A$。若两个合法的**传递严格关系**之对称差只含 $\alpha(e)=\alpha(f)$ 的事件对 $(e,f)$，则每个当前事件的 $U$ 不变，故两表示在 $\Sigma_{\rm cau}$ 下不可区分。

**证明。** 对每个 $e\in\Omega$，改变的当前目标 $f$ 都与 $e$ 同属性；这个属性原已由 $e\preceq e$ 在 $U(e)$ 中，添删这些关系不改属性集。指向 $E\setminus\Omega$ 的关系不直接贡献任何当前目标。假设说的是两份完整传递关系，因而不存在另一个未入差集的闭包变化。剖面及端点相同，用命题 46。证毕。

一个可核查的充分插边条件是：对 $e,f\in\Omega$，插入 $e\prec f$ 前已有 $U(f)\subseteq U(e)$，且插入后取闭包仍满足严格时标。任何新增当前可达对的路径都经过这条新边；它从一个原来可达 $e$ 的当前点 $g$，到一个原来可由 $f$ 达到的当前点。目标属性已在 $U(f)\subseteq U(e)\subseteq U(g)$ 中，所以所有 $U$ 不变。这也允许闭包新增跨属性关系，只要没有新增属性可达性。相反，只知道一条**生成边**的端点同属性，不能推断取闭包后仍不可见。

**反例 D7（同属性生成边可造成正面因果分离，repo-derived）。** $E=\Omega=\{a,b,c,d\}$，位置全 $0$、来源 $l_0$，符号 $+,+,-,-$，时刻 $0,1,2,0$，选择 $\{a\}$。$X$ 只有 $b\prec c$；$Y$ 为 $a\prec b,b\prec c,a\prec c$。两者 $\rho_{\rm src}=(0,\delta_{(0,l_0)})$、$(m,M,s)=(0,2,2)$，但对 $Q=\{(0,-1,l_0)\}$ 有 $q(F_{\downarrow Q}X)=0,q(F_{\downarrow Q}Y)=1$。这些值逐事件计算并由附录 `edge=0,1` 复核，证明 $\Sigma_{\rm cau}$ 严格细化 $\Sigma_{\rm src}\cup\Sigma_{\rm st}$。新增生成边 $a\prec b$ 两端同属性，却在闭包中新增 $a\prec c$ 的跨属性关系，故也反驳“插入同属性生成边并取闭包必不可见”的全称断言。

**反例 D8（单点命中边缘不足，repo-derived）。** 取两个选中正事件 $e_1,e_2$，同属性 $a=(0,+1,l_0)$、时刻 $0$；两个未选负事件，分别有属性 $b=(0,-1,\operatorname{leaf}(1))$、$c=(0,-1,\operatorname{leaf}(2))$、时刻 $1$。取 $E=\Omega$ 为这四点。$X$ 中仅 $e_2$ 指向两个负事件；$Y$ 中 $e_1$ 指向属性 $b$ 的负事件、$e_2$ 指向属性 $c$ 的负事件。对所有单属性 $Q$，读数全同：$Q=\{a\}$ 为 $2$，$\{b\},\{c\}$ 各为 $1$，其余为 $0$；但 $Q=\{b,c\}$ 时分别为 $1,2$（逐点命中计数；附录 `marginals=1,2`）。上述反演使用共同有限集 $D$ 上的子集命中读数。D8 证明只保存单步单点边缘不充分；这里不主张所用探针族最小，也不排除单点筛选的复合提供联合信息（例如 $q(F_{\downarrow\{b\}}(F_{\downarrow\{c\}}X))=1$ 而 $Y$ 侧为 $0$）。

### 28.6 B2 的签名边界

B2 两对象在本节的 $\Sigma_{\rm cau}$ 下仍同核。确切地，记 $a_+=(0,+1,l_0),a_-=(0,-1,l_0)$，所有正事件的 $U=\{a_+\}$，所有负事件的 $U=\{a_-\}$；二者剖面都只有 $(a_+,1,\{a_+\})\mapsto2$ 与 $(a_-,0,\{a_-\})\mapsto-2$，端点均为 $(0,1,1)$。由命题 46 得全部本签名上下文观察相同。若将时间纳入 $\alpha_t(e)=(x(e),\sigma(e),\rho(e),t(e))$，同样形式的属性查询用 $Q=\{(0,+1,l_0,1)\}$，便分别命中两正点与仅上层正点，读数为 $2,1$。这些 B2 读数来自所列事件与关系，附录另查有界本签名上下文及时间查询；本节不立时间属性因果核定理。

**反例 D9（去身份但不在 $\Sigma_{\rm cau}$ 的筛选，repo-derived）。** 定义
$J(C,A)=(C,\{e\in A:\exists d\in\Omega_C\ (e\prec d)\})$。该筛选不用事件身份、在重命名下不变，却问是否有**严格**后继。对 B2 两对象，$q(JX)=1,q(JY)=0$（前者只选到 $a$，后者没有严格边；附录 `strict_successor=1,0`）。故“任何去身份签名下 B2 同核”为假；$J$ 不在 $\Sigma_{\rm cau}$ 内，这不反驳命题 46。也不能把 $J$ 当作其已有上下文：若能表达，它就不能分开本签名同核的 B2。

### 28.7 时间属性剖面的历史边界

**反例 D10（时间属性仍不恢复历史，repo-derived）。** 四个选中正点 $a_1,a_2$ 在时刻 $0$，$b_1,b_2$ 在时刻 $1$；四点除时间外全同属性 $(0,+1,l_0)$。一图的严格关系为 $\{a_1\prec b_1,a_2\prec b_2\}$，另一图为 $\{a_1\prec b_1,a_2\prec b_1\}$。各加四个时刻 $0$、位置 $0$、来源 $l_0$ 的孤立未选负点，取 $E=\Omega$ 为全部八点，得到合法平衡表示。以 $\alpha_t$ 代替 $\alpha$ 所算 $\Gamma_t$ 相同：每个下层正点看见时刻 $0,1$ 两个正属性，每个上层正点只看见自己的时刻 $1$ 正属性，负点均只看见自身负属性。上层入度多重集却为 $\{1,1\}$ 与 $\{2,0\}$（由所列两条边计算；附录复核），任何保时间的历史同构都须保存该多重集，故历史不同构。此例只划定剖面遗忘重数与入射关联的边界，不新增关于时间属性签名的核定理。

<a id="pr3-comparisons"></a>

## 29. PR3 增补 K：与既有理论的对照

本节不新增数学，不作综述。表中外部文献的对象及结论标 `literature-attested`，与本卷的对应判断标 `repo-derived`；取回与核读强度在 §31 披露。对应只比较操作、观察和成立条件，不把名称相似当作定理。

| 既有对象或定理 | 确切对应 | 确切不对应 | 来源与标签 |
| --- | --- | --- | --- |
| Conway，*On Numbers and Games*（1976） | 生日记录递归构造层级，对应本卷的构造深度；数的最简代表与定义 8 的固定代表，都须区别于一个给定构造；游戏在“对一切 $X$”的加法测试中相等，对应定义 16 用测试上下文定义观察等价的做法 | 生日不是档案时刻 $t$；本卷固定截面不承担 Conway 的最简性定理；游戏采用加法测试，本卷量化全部指定的一孔上下文，包括筛选、乘法和部分域失败，不能直接搬用游戏相等判据 | [第二版 DOI 10.1201/9781439864159](https://doi.org/10.1201/9781439864159)，**不是 1976 原版 DOI**。外部对象 `literature-attested`；局部对照 `repo-derived` |
| Green–Ives–Tannen，*Reconcilable Differences*（2009） | $\mathbb Z$-关系以整数作元组重数，差允许负重数和消去；本卷在总背景平衡下得到 $q(NX)=-q(X)$，可在读数层比较有符号消去 | $N$ 是固定背景中的一元补选择，不等于二元关系差；该整数关系语义不提供本卷保留有序 pair 的非结合来源乘法 | DOI [10.1145/1514894.1514920](https://doi.org/10.1145/1514894.1514920)；整数差语义另见下列 TaPP 文 §4。文献陈述 `literature-attested`；对照 `repo-derived` |
| Geerts–Poggi，*On Database Query Languages for K-relations*（2010） | 以 $K$-关系考察查询语言及差运算扩展，要求说明注释域和查询操作；本卷也须先固定观察签名才能谈下降 | 本卷未建立同一查询语言或公理组，来源 pair 乘法也未满足交换半环契约，不能直接调用其查询等价结论 | DOI [10.1016/j.jal.2009.09.001](https://doi.org/10.1016/j.jal.2009.09.001)。文献陈述 `literature-attested`；对照 `repo-derived` |
| Amsterdamer–Deutch–Tannen，*On the Limitations of Provenance for Queries with Difference*（TaPP 2011） | 该文问能否**对每个注释交换半环**扩充关系差，使 Figure 1/2 的 A1–A13 同时成立；结论是否定这个普适要求。A1–A12 的 monus 扩展仍可在某些半环上违反 A13；§3 命题 3.4／推论 3.5 给出具体失败范围。本卷同样须按已声明的运算、公理及量词结算 | Figure 2 的 A10 是 $0-a=0$；§4 明说 $\mathbb Z$ 的差语义不满足 A10、A11。本卷 $N_C$ 是固定背景中的一元补选择，$u=0$ 只导出 $q(NX)=-q(X)$，没有建立 monus 或该文的二元差公理组。**两者是不同的语义任务**；本卷不构成克服、规避、反驳或满足该结果的实例 | [arXiv:1105.2255](https://arxiv.org/abs/1105.2255)，已核读全文及 Figure 2、§3–4。文献断言 `literature-attested`；不同语义任务的对照判断 `repo-derived` |
| Amsterdamer–Deutch–Tannen，*Provenance for Aggregate Queries*（PODS 2011） | 将来源标注扩展至元组内的聚合值，并通过聚合表达差；与本卷“必须说明读数如何沿操作传播”的要求有局部对应 | 这是聚合查询语义，不是上一行的差运算不可能性论文；本卷没有建立其聚合值注释域、嵌套聚合与查询语言契约 | [arXiv:1101.1110](https://arxiv.org/abs/1101.1110)，与 TaPP 文分列。文献陈述 `literature-attested`；对照 `repo-derived` |
| Köhler–Ludäscher–Zinn，*First-Order Provenance Games*（2013） | 用查询求值游戏解释来源，赢／输结构参与判定；与本卷用有结构的来源和明确观察解释读数的方向相接 | 本卷来源树不提供求值游戏、合法策略、赢输判据或 why-not 契约；一个 pair 结点不能替代一场求值游戏 | DOI [10.1007/978-3-642-41660-6_20](https://doi.org/10.1007/978-3-642-41660-6_20)；[arXiv:1309.2655](https://arxiv.org/abs/1309.2655)。文献陈述 `literature-attested`；对照 `repo-derived` |
| Winskel，*Event Structures*（1987） | 用事件出现及因果依赖描述过程，对应本卷 $(E,\prec)$ 的因果层 | 本卷没有冲突关系，允许任意选择 $A\subseteq\Omega$；这些选择不冒充事件结构的合法配置，§1 已给补集不保持向下闭的例子 | DOI [10.1007/3-540-17906-2_31](https://doi.org/10.1007/3-540-17906-2_31)。文献陈述 `literature-attested`；对照 `repo-derived` |
| Bombelli–Lee–Meyer–Sorkin，*Space-time as a Causal Set*（1987） | 因果偏序承载离散事件的先后结构，对应本卷 $(E,\prec,t)$ 中的有序事件层；本卷另给兼容该序的整数时标 | 仅有有限偏序和时标不提供连续几何重建、Lorentz 体积解释或动力学，不能把任意本卷情境认作已验证的物理时空 | DOI [10.1103/PhysRevLett.59.521](https://doi.org/10.1103/PhysRevLett.59.521)。文献陈述 `literature-attested`；对照 `repo-derived` |
| Bennett，*Logical Reversibility of Computation*（1973） | 可逆计算要求能够反演计算状态转移；本卷档案保留使部分输入事件仍可追索，是可比较的保存信息问题 | 留有旧事件不足以证明反演：§3 的 $X\boxtimes0_\varnothing$ 遗忘 $A_X$，不同旧选择产生相同输出。因此“留历史所以可逆”越界 | DOI [10.1147/rd.176.0525](https://doi.org/10.1147/rd.176.0525)。文献陈述 `literature-attested`；本卷失败见证与对照 `repo-derived` |
| Baez–Dolan，*Categorification*；Baez，*The Mysteries of Counting* | 结构到数值的压缩，以及在具备相应结构时推广计数，可与本卷从丰富表示取数值商、有符号读数的形式相比较 | 范畴化还需态射、函子和相干条件；Euler 示性数需相应拓扑或分次／链复形契约。本卷没有建立这些契约，不宣称已范畴化，也不把任意 $q$ 称为 Euler 示性数 | [arXiv:math/9802029](https://arxiv.org/abs/math/9802029)；Baez [讲座稳定入口](https://math.ucr.edu/home/baez/counting/)。文献陈述 `literature-attested`；对照 `repo-derived` |

本节全部对应为局部对应，不构成“这些理论共同导出本卷”的叙事。

<a id="pr3-quantum-boundaries"></a>

## 30. PR3 增补 L：与量子力学的差距

本节不新增数学；沿 §13 的反驳表，只结算“**这些结论未由本卷当前定义推出**”，不写成任何扩展都不可能。外部构造标 `literature-attested`，本卷欠缺何种结构的判断标 `repo-derived`。本卷的整数读数、来源树和共同世界域均未被定义为物理态或实验概率。

| 断言 | 精确替代 | 来源 |
| --- | --- | --- |
| “本算术可解释双缝” | 本卷没有振幅到概率的规则。普通复数算术中 $\lvert1+1\rvert^2=4\ne\lvert1\rvert^2+\lvert1\rvert^2=2$，表明相干相加与分开平方不同；把该交叉项解释为实验概率还需额外规则及归一化。本卷历史枚举也不等于满足一致历史或退相干条件的概率模型 | Feynman（1948），DOI [10.1103/RevModPhys.20.367](https://doi.org/10.1103/RevModPhys.20.367)，路径振幅；Griffiths（1984），DOI [10.1007/BF01015734](https://doi.org/10.1007/BF01015734)，一致历史条件；Gell-Mann–Hartle（1990），[2018 重发入口 arXiv:1803.04605](https://arxiv.org/abs/1803.04605)，退相干历史；Sorkin（1994），[arXiv:gr-qc/9401003](https://arxiv.org/abs/gr-qc/9401003)，量子测度加性层级。外部内容 `literature-attested`；缺项判断与所列算术核算 `repo-derived` |
| “反着即对偶” | 须逐一辨型：$N_C:\mathcal P(\Omega_C)\to\mathcal P(\Omega_C)$ 是固定背景补集；形式时间反向同时反转时标与序，物理时间反演还需指定态与动力学上的作用；有界 Hilbert 算子 $A:H\to K$ 的伴随 $A^*:K\to H$ 由内积定义；范畴对偶 $\mathcal C^{\rm op}$ 反转态射；Fourier 对应把群上的函数送到字符群上的函数。本卷没有将这些构造互相识别的映射与保律条件 | §2、§8 的操作类型与本行缺项判断 `repo-derived`；Baez–Dolan [arXiv:math/9802029](https://arxiv.org/abs/math/9802029) 提供范畴结构背景；[Encyclopedia of Mathematics：Pontryagin duality](https://encyclopediaofmath.org/wiki/Pontryagin_duality) 提供局部紧阿贝尔群与字符群的适用条件，`literature-attested` |
| “加复权重即得量子” | 换成复系数不提供态、正概率、测量及复合规则。本卷的一孔上下文等价不等于 Abramsky–Brandenburger 的 contextuality：后者有测量覆盖、覆盖上相容的概率／经验模型，及其全局截面扩张障碍；不能从本卷存在共同世界或有符号读数推出 Bell 型裁决。Litvinov–Maslov 的去量子化有具体代数和极限条件：非负实数经 $u\mapsto h\log u$ 运输运算（零用 $-\infty$），$h>0$，再取 $h\to0^+$ 得 max-plus；它不支持“改系数便得量子”的推断 | Abramsky–Brandenburger（2011），[arXiv:1102.0264](https://arxiv.org/abs/1102.0264)，摘要及 §2 的测量覆盖／分布；Litvinov–Maslov，*Correspondence Principle for Idempotent Calculus and Some Computer Applications*，[arXiv:math/0101021](https://arxiv.org/abs/math/0101021)，§2。文献陈述 `literature-attested`；本卷类型边界 `repo-derived` |
| “离散是差距” | 离散性本身不排除量子构造。Johnston 在离散因果集上对轨迹求和构造粒子传播子，并在所述 Minkowski 撒点条件下与 Klein–Gordon 延迟传播子比较；这不证明本卷已有同一传播子或其极限 | Johnston（2008），*Particle Propagators on Discrete Spacetime*，[arXiv:0806.3083](https://arxiv.org/abs/0806.3083)，`literature-attested`；本卷缺项判断 `repo-derived` |

只保留下列三项局部类比；它们不是量子理论的推导。

| 结构相似项 | 缺失的量子公理或结构 |
| --- | --- |
| 历史归并的组合结构：多个构造参与一个读数或来源表达 | 缺少振幅及概率解释，也没有一致历史／退相干条件；来源同上表 Feynman、Griffiths、Gell-Mann–Hartle、Sorkin，外部框架 `literature-attested`，本卷类比 `repo-derived` |
| $q$ 沿 $\boxplus$ 及有定义的 $\triangleright$ 相加，形式上类似可加作用量 | 缺少物理作用量的定义、单位与 $\hbar$，也没有由作用量到振幅的规则；§3 命题 2 与上述 Feynman 文给出比较两端，本卷类比 `repo-derived` |
| **仅对 §19 的 $\mathbb Z[\mathbb Z^3]$**，有限系数可经群字符作 Fourier 对应，$\widehat{\mathbb Z^3}\cong\mathbb T^3$（此处 $\mathbb T=\mathbb R/\mathbb Z$，不同于来源树集合 $T$） | 这是阿贝尔群卷积的标准字符对应，缺少 Born 规则与测量理论；不移植到 §27 非结合的来源 pair 代数。上述 Pontryagin duality 稳定入口支持群对偶框架（`literature-attested`）；与本卷空间代数的绑定及边界为 `repo-derived` |

表中的缺项来自对本卷现有定义域与运算的核对，未作物理实验；双缝、Born 规则、Bell 实验与量子动力学在本批均为“未测”，本批也没有提供这些实验或物理公理的实现。

<a id="pr3-receipts"></a>

## 31. PR3 的来源、产地与核验收据

### 31.1 成熟来源与本仓推导的边界

| 范围 | 成熟来源及适用对象 | 本仓推导与结算边界 |
| --- | --- | --- |
| §27 来源语言 | §14–16 已使用的有限支撑与上下文归纳方法；§29 的关系来源文献仅提供查询／系数背景（`literature-attested`） | 联合分箱、非结合有序 pair 更新、来源核及混合时间核的 CSA 特定证明为 `repo-derived`；不把交换环公理移植到来源代数，不主张完整来源代数分类 |
| §28 因果语言 | Rota 的 Möbius 反演框架，DOI [10.1007/BF00531932](https://doi.org/10.1007/BF00531932)，`literature-attested`；此处只用有限布尔格 | 目标域为当前区域的筛选、剖面推送、平衡参数隔离、完整 iff 与 D6–D10 为 `repo-derived`；正文另直接证明所用反演式，有限运行不承担一般必要性 |
| §29 理论对照 | 下表逐项列出的游戏、关系查询、来源游戏、事件结构、因果集、可逆计算及范畴化对象，`literature-attested` | 每项操作／观察／条件的对应及不对应判断为 `repo-derived`；没有建立同一查询语言、monus、公理组或范畴结构 |
| §30 量子边界 | 下表物理文献、测量覆盖／概率模型／全局截面框架、去量子化极限和阿贝尔群字符对偶，`literature-attested` | 本卷缺项与三条局部类比为 `repo-derived`；Fourier 仅绑定 §19 的空间群环，不推出 Born 规则、双缝或 Bell 型裁决 |

`repo-derived` 说明本卷给出了推导，不声明优先权。本批按 DOI、arXiv、出版页、Crossref 元数据及作者／学术站点检索；没有作穷尽的新颖性排查，新颖性优先权为“未测”。原文访问失败不等于没有相关文献，不能据此标 `suspected-novel`。`literature-attested` 的归属标签与本席实际核读强度分开记录：下表“未取回”各项的原文核读为 `ASSUMED-UNVERIFIED`，其中元数据或二手核读的范围逐行写明。已下载文件也不等于已通读。

| 文献（DOI 或稳定 URL） | 本席核读状态 | 实际范围与未核部分 |
| --- | --- | --- |
| [Rota (1964), Theory of Möbius Functions](https://doi.org/10.1007/BF00531932) | 未取回 | 取回出版页并核读元数据；原文未取回。正文另给布尔格反演的直接证明。 |
| [Conway, On Numbers and Games](https://doi.org/10.1201/9781439864159) | 未取回 | 出版页及 Crossref 题名、作者、登记日期已核；书本文字未取回。第二版 DOI 的版次说明据 brief，非 1976 原版 DOI。 |
| [Green–Ives–Tannen (2009), Reconcilable Differences](https://doi.org/10.1145/1514894.1514920) | 未取回 | 出版入口返回 HTTP 403；Crossref 元数据已核。整数差语义另由已通读的 TaPP 文 §4 交叉核读。 |
| [Geerts–Poggi (2010), On Database Query Languages for K-relations](https://doi.org/10.1016/j.jal.2009.09.001) | 未取回 | 取回 linkinghub 入口及 Crossref 元数据，原文未取回；差扩展另见已通读 TaPP 文的讨论。 |
| [Amsterdamer–Deutch–Tannen, TaPP 差运算限制 (2011)](https://arxiv.org/abs/1105.2255) | 已读全文 | 通读取回的 5 页；核对 Figure 2 的 A10/A11、§3 命题 3.4／推论 3.5 与 §4 整数差语义。 |
| [Amsterdamer–Deutch–Tannen, PODS 聚合来源 (2011)](https://arxiv.org/abs/1101.1110) | 只读摘要 | 全文文件已取回，核读摘要中的值层来源、聚合与差；全文未通读。 |
| [Köhler–Ludäscher–Zinn (2013), First-Order Provenance Games](https://arxiv.org/abs/1309.2655) | 只读摘要 | 全文文件已取回，核读完整摘要及开篇；全文未通读。另有 DOI 10.1007/978-3-642-41660-6_20。 |
| [Winskel (1987), Event Structures](https://doi.org/10.1007/3-540-17906-2_31) | 只读摘要 | 核读出版页摘要；章节全文未取回。 |
| [Bombelli–Lee–Meyer–Sorkin (1987), Space-time as a Causal Set](https://doi.org/10.1103/PhysRevLett.59.521) | 已读全文 | DOI 入口返回 HTTP 403 后，从 APS harvest 取回并通读 4 页。 |
| [Bennett (1973), Logical Reversibility of Computation](https://doi.org/10.1147/rd.176.0525) | 未取回 | DOI 转至 IEEE，HTTP 202 且正文为空；另查 UVA PDF 与 IBM 题名入口均为 HTTP 404。未取得摘要或原文，外部断言据 brief。 |
| [Baez–Dolan, Categorification](https://arxiv.org/abs/math/9802029) | 只读摘要 | 全文文件已取回，核读摘要及开篇的范畴、函子与相干要求；全文未通读。 |
| [Baez, The Mysteries of Counting](https://math.ucr.edu/home/baez/counting/) | 只读摘要 | 核读讲座入口摘要；未通读讲义或幻灯片。 |
| [Feynman (1948), Space-Time Approach to Non-Relativistic Quantum Mechanics](https://doi.org/10.1103/RevModPhys.20.367) | 只读摘要 | 从 APS harvest 取回全文；核读摘要、引言及 §2 片段的振幅相加／模平方；全文未通读。 |
| [Griffiths (1984), Consistent Histories and the Interpretation of Quantum Mechanics](https://doi.org/10.1007/BF01015734) | 只读摘要 | 核读出版页摘要；原文未取回。 |
| [Gell-Mann–Hartle (1990), Quantum Mechanics in the Light of Quantum Cosmology](https://arxiv.org/abs/1803.04605) | 只读摘要 | 取回 2018 重发全文；核读完整摘要及重发说明，确认概率指派的退相干条件；全文未通读。 |
| [Sorkin (1994), Quantum Mechanics as Quantum Measure Theory](https://arxiv.org/abs/gr-qc/9401003) | 只读摘要 | 全文文件已取回，核读摘要中的测度加性层级；全文未通读。 |
| [Abramsky–Brandenburger (2011), The Sheaf-Theoretic Structure of Non-Locality and Contextuality](https://arxiv.org/abs/1102.0264) | 只读摘要 | 全文文件已取回；除摘要外核读 §2.1–2.3 的测量覆盖、结果指派与分布定义，全文未通读。 |
| [Litvinov–Maslov, Correspondence Principle for Idempotent Calculus and Some Computer Applications](https://arxiv.org/abs/math/0101021) | 已读全文 | 通读取回的 27 页；§2 的 h log u 运输及 h→0+ 极限为本节直接引用范围。 |
| [Johnston (2008), Particle Propagators on Discrete Spacetime](https://arxiv.org/abs/0806.3083) | 只读摘要 | 全文文件已取回，核读摘要的离散传播子及 Minkowski 撒点比较条件；全文未通读。 |
| [Encyclopedia of Mathematics, Pontryagin Duality](https://encyclopediaofmath.org/wiki/Pontryagin_duality) | 已读全文 | 通读该网页及所附参考、评论；仅引用局部紧阿贝尔群／字符群部分。 |

上述核读状态取自本次实际取回文件与阅读窗口；逐次 URL、HTTP 结果及保留文本位于 runner 工件目录的 `literature/fetch.json`、`literature/extra-fetch.json`、`literature/bennett-fetch.json` 与同目录原文文件。未通读项的完整证明核读仍为“未测”，由后续文献核读或评审接续；本卷自给的证明不依赖把这些状态提升为已读全文。

### 31.2 本批产地与调用边界

本批由 `consensus-rnd:sshx` 的一个 `codex-cli implementation worker` 在工作树 `/Users/auricstudio/trureturing-csa-upgrade-pr3-0909`、分支 `lane/theory/csa-upgrade-pr3-0909` 实施，基线钉住 `4ac806a62d274a48550978b827a4bf546a8c898e`。输入为 caller 交付的收敛 brief（含 R1）、本仓标架与既有卷文，属于 `repo-prior-exposed`；本 implementation worker 未另派子席。

本次 fix pass 3 以 merge 合入包含 dev `a1bcdde34d` 的实际 tip `692c7efed4`（合并提交 `5e12e9c731`；两版本卷字节相同），因 #6684 同尾追加而将 PR3 五节整体顺延为 §27–§31、定义 25、命题 42–47、反例 D6–D10，数学内容不变。

按 **caller／brief 提供的席位记录**，思考席六席全部为 `nyxid-oracle`，其中五席为 codex 负载门超时后的协议回退。该席位说明不是本 worker 对宿主超时原因的独立测量，也不构成模型多样性声明。本 worker 亲跑附录、canonical ingest 与下列 git／字节核对；orchestrator 亲验结果未向本席提供，记“未测”。评审与 PR 生命周期由 caller 接续；本节不预报评审、CI 或合入结果。

本批形态为 **ingest**：`contextual-spacetime-arithmetic` 源卷新增内容经 canonical writer 进入 atom CAS 与该 source 的 `residual-open` backfill。未新增 Lean、axiom、判官、schema 或生产引擎；本批没有 deposit／cover，不报告新增冻结或已吸收状态。Lean、CI、独立评审与物理实验均为“未测”，分别由形式化／CI／评审／物理模型工作承担。

### 31.3 附录实际命令与有限收据

本席在上述工作树实际运行下列原文命令（2026-09-10，本批执行文件对应本卷唯一 Python 块）；退出码 **0**，stderr 为空。复用 `Rich/add/mul/neg/temporal/filt`，R1 允许的 `pr3_` 代码只插在既有最终打印之前。

```sh
sed -n '/^```python$/,/^```$/p' docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md | sed '1d;$d' | python3 -
```

本次合并与重编号后的复跑同样退出 **0**、stderr 为空，以下两条 `pr3_` 收据与原收据逐字相同，末行仍为 `ALL_FINITE_CHECKS_PASSED`。

stdout 中 `pr3_` 两行及最终行原文如下；原有检查也在同一次执行中通过：

```text
pr3_source: samples=48 updates=240 witnesses=6 brackets=28,32 B1=distinct ordered_pair=distinct
pr3_causal: updates=551 product_antichains=48 targets=Omega bare_probes=16 P_plus=1,0 legal_probes=1200 mobius_profiles=51 mobius_coefficients=1200 bounded_contexts=273 B2_time=2,1 strict_successor=1,0 edge=0,1 marginals=1,2 redundant_insertions=12 timed_nonisomorphism=True
ALL_FINITE_CHECKS_PASSED
```

这些计数由实际执行累加。随机种子为 `20260910`；随机当前区域大小取 0、2、4，额外档案点数取 0、1、2，兼容时标的边取传递闭包，选择任意子集。48 个随机样本逐字节检查来源更新，并核对因果剖面更新、乘积当前反链与无出边；额外档案目标见证断言因果筛选只遍历 `Omega`。51 个反演对象为 48 个随机样本加 D6 两对象与当前区域外目标见证，合法探针恢复两种选择位，采用规范序列化字节逐格比较。B2 的 273 个有界上下文为 16 个固定基本操作在深度 0–2 的全部单孔复合；一般上下文结论由命题 46 证明。D6 的补集裸探针只要求两侧相等，§28.3 已列其非零情形。有限收据不声明枚举全部载体、上下文、时间属性签名或历史同构类型；一般必要性已由正文证明，未启用 `pr3_mobius_finite` 降级形态。

### 31.4 ingest 与固定检查点的 git 读数

本次 fix pass 3 在合并 dev、完成重编号并删除旧摄入清单后，实际运行下列命令（2026-09-10）。摄入基线固定为 `a1bcdde34d41cde0c9d77af53de7f2a5088e98a7`；执行前的已提交输入为 `3b08ee811c46e22b65518b43441e328dce5434c8`：

```sh
BASE=a1bcdde34d41cde0c9d77af53de7f2a5088e98a7 make ingest SOURCE="contextual-spacetime-arithmetic docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md"
```

退出码 **0**，stderr 为空；调用前后新增 **93 个 atom、93 个 residual-open backfill**（186 个文件，路径集合实测、两侧 atom_id 成对）。stdout 原文：

```text
INGEST residual_open_added=93 skipped_existing=144 coarse_fallbacks=0 open_genres=0 cas_objects_written=93 ledger_changed=true
```

新增 atom 已逐项检出 §27–§31、定义 25、命题 42–47、反例 D6–D10，以及附录的 D6／D7／D8／D10 注释。本次产物提交为 `52ad2ab16eeca9462f2b32c291b6f119bb386ea9`；下列 git 读数以该提交为固定检查点，范围截至本节改写之前：

| 读数口径 | 实测值 |
| --- | --- |
| 摄入基线本卷行数 | 2552 |
| 上述执行输入及摄入检查点本卷行数 | 3378 |
| 本节更新后的本卷行数（下一次摄入的输入） | 3251 |
| 相对实际合入 dev `692c7efed4e50c2262984cd4e0aa0e6776cdedc3` 的本卷增删行 | +826／−0 |
| 同一 git 比较范围的新增 atom／backfill | 93／93 |
| 检查点 `git status --porcelain=v1` | 退出 0，stdout 为空 |

`git diff --shortstat 692c7efed4e50c2262984cd4e0aa0e6776cdedc3..52ad2ab16eeca9462f2b32c291b6f119bb386ea9` 实跑退出 0，stdout 原文：

```text
 187 files changed, 4126 insertions(+)
```

摄入比较基线与 git 范围分别固定：fetch 时 dev 已从 `a1bcdde34d` 前进到 `692c7efed4`，两版本卷相同，后者包含的其他 dev 改动不计作 PR3 产物。旧摄入删除严格使用 brief 指定的 `4ac806a62d274a48550978b827a4bf546a8c898e..d2c713228e74cd2fbe20a31e2c400c8face7389d` 新增路径清单：95 对、190 个文件；#6684 的 35 对及更早产物不在删除集合。重摄入可按内容地址重新生成其中字节未变的 atom。

合并的字节核对保留了附录 PR3 插入：该段为 314 行代码及一行前导空行。含此插入的原始前缀与 dev 全文直接 `cmp` 退出 **1**，差异从附录 PR3 插入处开始；只剔除此已知插入后的前缀与 dev 全文 `cmp` 退出 **0**、stdout 为空。dev 的 §24–§26 共 416 行、27967 字节原样在前，PR3 的 §27–§31 紧随其后；原始前缀完全相同与保留附录插入不能同时成立，不将前者报告为通过。

本节改写后再以同一摄入基线运行 canonical writer，使本次产地与收据文字也进入消化账。该补充摄入及最终累计 atom／backfill 数、附录原始 stdout、git 差分目录集、提交、推送与干净状态，由本次 runner 的 `result.json` 和所引日志记录；本节上述 93／93 明确只指固定检查点，不冒充最终累计数。

<a id="pr4-temporal-causal"></a>

## 32. PR4 增补 M：含时间属性的去身份因果语言

本节闭合 §28.6–28.7 留下的含时间属性签名的观察核问题。载体仍为定义 3 的平衡表示 $\mathcal B$，档案乘法仍为定义 6，严格观察与全部有限单孔上下文仍为定义 16。以下 CSA 特定定义、推送、证明及见证均标 `repo-derived`，不作新颖性优先权声明；反演只复用 §28.4 已引 Rota (1964) 的有限布尔格公式及该处直接证明，不另立一般 Möbius 定理。

### 32.1 定义 26：含时间属性、当前目标与剖面

**定义 26（含时间属性的去身份因果剖面，repo-derived）。** 令

$$
\begin{aligned}
\mathrm{Attr}_t&=\mathbb Z^3\times\{+1,-1\}\times T\times\mathbb Z,\\
\alpha_t(e)&=(x(e),\sigma(e),\rho(e),t(e)),\\
U_t^X(e)&=\{\alpha_t(d):d\in\Omega_X,\ e\preceq_X d\}\quad(e\in\Omega_X).
\end{aligned}
\tag{TCAU-U}
$$

$e\preceq d$ 仍指 $e=d$ 或 $e\prec d$。$U_t^X(e)$ 是有限非空属性集，同属性目标去重；目标严格限于 $\Omega_X$，不要求属于 $A_X$。对每个固定 $Q\subseteq\mathrm{Attr}_t$ 定义总操作

$$
F_{\downarrow Q}(C,A)
=\bigl(C,\{e\in A:\exists d\in\Omega_C\quad
 (\alpha_t(d)\in Q\ \land\ e\preceq d)\}\bigr).
\tag{TCAU-F}
$$

它保持完整 $C$，只筛选当前选择。沿用 $b_X(e)=\mathbf1_{A_X}(e)$，定义有限支撑整数剖面

$$
\Gamma_t(X)(a,b,U)
=\sum_{\substack{e\in\Omega_X\\
 \alpha_t(e)=a,\ b_X(e)=b,\ U_t^X(e)=U}}\sigma(e),
\quad
(a,b,U)\in\mathrm{Attr}_t\times\{0,1\}\times\mathcal P_{\rm fin}(\mathrm{Attr}_t).
\tag{TCAU-P}
$$

这里对 $\Omega_X$ 全体计数，未选事件进入 $b=0$ 行，$E_X\setminus\Omega_X$ 不进入任何行。指定

$$
\Sigma_{{\rm cau},t}
=\Sigma_{\rm src}\cup\Sigma_{\rm st}
 \cup\{F_{\downarrow Q}:Q\subseteq\mathrm{Attr}_t\}.
\tag{TCAU-LANG}
$$

本节 $F_{\downarrow Q}$ 的参数类型是 $\mathrm{Attr}_t$；§28 的无时间因果筛选可由
$Q\mapsto\varphi^{-1}[Q]=\{a_t:\varphi(a_t)\in Q\}$ 表示，其中
$\varphi(p,\epsilon,r,n)=(p,\epsilon,r)$。因此旧因果上下文逐操作翻译后仍可使用；不把身份目标集合 $D\subset HF$ 加入语言。定义 23 的一般 $F_B$ 和定义 24 的 $M_P$ 也未作为原语并入（ARCH-R4-A1）。

同格事件的符号已由 $a$ 的 $\epsilon$ 坐标固定，故非空格系数为 $\epsilon$ 乘其事件数，不会抵消。因此

$$
\begin{aligned}
V_t(X)=\alpha_t[\Omega_X]
 &=\{a:\exists b,U\ \Gamma_t(X)(a,b,U)\ne0\},\\
s_X&=\max\{n:\exists p,\epsilon,r,b,U\quad
 \Gamma_t(X)((p,\epsilon,r,n),b,U)\ne0\}.
\end{aligned}
\tag{TCAU-SUPPORT}
$$

第二行空支撑取 $-\infty$。与定义 22 的 $W,Z$ 不同，最高时刻的一正一负在这里分属不同属性格，不能共同消失；§26.1 D3 的隐形最高时刻也由此显现。$V_t,s$ 均非独立坐标，所需摘要写成 $(\Gamma_t,m,M)$。$m,M$ 仍为**全档案**端点，含非当前事件；只由当前剖面恢复这两个端点的断言已被 B3／D4 反驳。

### 32.2 命题 48：推送更新与全部混合上下文的充分性

**命题 48（含时间剖面的更新与充分性，repo-derived）。** 对非零格作下表的系数推送；若多个格映到同格，系数相加。写 $a=(p,\epsilon,r,n)$，并令

$$
\begin{aligned}
a\diamond_t a'&=(p+p',\epsilon\epsilon',
 \operatorname{pair}(r,r'),\max(n,n')+1),\\
\tau_k(a)&=(p,\epsilon,r,n+k),\qquad
\tau_k[U]=\{\tau_k(v):v\in U\}.
\end{aligned}
$$

| 操作 | 剖面推送 |
| --- | --- |
| $X\boxplus Y$ | 两剖面逐格相加 |
| $NX$ | $(a,b,U)\mapsto(a,1-b,U)$ |
| $F_SX$ | $(a,b,U)\mapsto(a,b\mathbf1_S(p),U)$ |
| $F_LX$ | $(a,b,U)\mapsto(a,b\mathbf1_L(r),U)$ |
| $F_{\downarrow Q}X$ | $(a,b,U)\mapsto(a,b\mathbf1_{U\cap Q\ne\varnothing},U)$ |
| $X\triangleright Y$，域为 $M_X<m_Y$ | 左格 $(a,b,U)\mapsto(a,b,U\cup V_t(Y))$，右格不变，再相加 |
| $X\boxtimes Y$ | 格对 $((a,b,U),(a',b',U'))\mapsto(a\diamond_t a',bb',\{a\diamond_t a'\})$，系数相乘后推送 |
| $T_kX$ | $(a,b,U)\mapsto(\tau_k(a),b,\tau_k[U])$ |

端点更新直接引用命题 29，以 (TCAU-SUPPORT) 提供 $s_X,s_Y$：并集取 $\min(m_X,m_Y),\max(M_X,M_Y)$；乘积取 $\min(m_X,m_Y),\max(M_X,M_Y,\gamma(s_X,s_Y))$；补集与三个筛选不改端点；平移对有限端点加 $k$，保持哨兵。结论是

$$
\ker(\Gamma_t,m,M)\subseteq\approx_{\Sigma_{{\rm cau},t}}.
\tag{TCAU-SUFF}
$$

**证明。** 并行没有跨边，故逐格相加。补集与筛选只改选择位；即使目标未选，仍在原 $U_t$ 中。时间复合把全部左档案连到全部右档案，每个左当前点因而新增全部右当前属性；右点没有新增后继。若右档案非空而 $\Omega_Y=\varnothing$，$V_t(Y)$ 为空，但守卫仍检查右档案。空档案时 $m=+\infty,M=-\infty$ 的规则恰使相应守卫空真，与命题 29 完全一致。

乘法的新当前点只来自 $\Omega_X\times\Omega_Y$。**该次乘法结果的当前区域是反链，新当前点无出边**，故其 $U_t$ 是自身属性单点集；旧档案虽保留却不进 $\Gamma_t$。逐父格分组，符号乘法及选中位乘法给系数之积与 $bb'$，时间按 $\max(n,n')+1$ 推送。任一当前区域空时，新剖面为空而旧档案端点仍保留。此反链结论只针对该次结果，不延伸到之后再作时间串接的状态。$T_k$ 保持偏序但同时改变自身及每个当前目标的时刻，故必须同时平移 $a$ 与 $U$，不能沿用 §28.2 的“剖面不变”。以上整数公式也适用于负时刻。

同摘要输入可由支撑取到相同的 $V_t,s$，所以全部更新与守卫只依赖摘要，成功结果仍是合法丰富表示的实际像。终端读数为
$q(X)=\sum_{a,U}\Gamma_t(X)(a,1,U)$。现对定义 16 的**全部混合上下文**归纳：恒等孔保持摘要；任一基本操作的其余槽位在两侧使用同一个固定平衡参数，由上表与命题 29 同时成功或失败，成功时摘要相等。复合中内层失败则两侧严格失败，不能用后续补集、空筛选或零因子把失败改成正常零；内层成功则向外归纳，到终端给相同 $q$。这涵盖每个二元槽位和任意有限深度，没有用两种语言的核取交代替闭包证明。证毕。

### 32.3 引理 2：最早元素与忘时见证 D11

**引理 2（最早元素，repo-derived）。** 对每个 $e\in\Omega_X$，$U_t^X(e)$ 中时间坐标最小的元素唯一，且恰为 $\alpha_t(e)$。于是每个非零格 $(a,b,U)$ 满足 $a=\min_t(U)$，实际非零行可由 $(b,U)$ 唯一索引，且同格同号不抵消。

**证明。** $e\preceq e$ 给 $\alpha_t(e)\in U_t^X(e)$；任何其它元素来自严格后继 $d$，由定义 1 有 $t(d)>t(e)$，故最早元素唯一。固定 $U$ 即固定自身属性及符号，再固定 $b$ 就固定整格，格系数为同号事件数之和。证毕。

**不承重的隔离备注。** §28.3 的乘积隔离在本语言的必要性证明中不再需要。若仍使用它，比较双方应共用参数 $T_k(U_0)$，取 $k\le m-1$（两非空档案共有下端点 $m$ 时），从而新选中点时间为 $t(e)+1$，对原时间单射；端点未对齐时可取 $k\le\min(m_X,m_Y)-1$。固定 $U_0$ 会把所有负父时刻送到 $1$，不能用于区分那些自身时刻；附录只将共同 $k$ 与固定 $U_0$ 作为核验对照，不让它承担引理 2 或命题 49。

**反例 D11（忘时后不可分的差测度见证，repo-derived）。** 令 $E=\Omega=\{a,b,c,d\}$，位置全 $0$、来源全 $l_0$，符号按序为 $+,+,-,-$，时间为 $-2,-1,0,0$，唯一严格边 $a\prec b$。$X$ 选 $\{a\}$，$Y$ 选 $\{b\}$，两者平衡。记 $v_+=(0,+1,l_0),v_-=(0,-1,l_0)$；按定义 25 逐事件算得

| 事件 | 无时间自身属性 | 无时间后继属性集 | $b_X,b_Y$ | 符号 |
| --- | --- | --- | --- | --- |
| $a$ | $v_+$ | $\{v_+\}$（$a,b$ 同属性，去重） | $1,0$ | $+1$ |
| $b$ | $v_+$ | $\{v_+\}$ | $0,1$ | $+1$ |
| $c$ | $v_-$ | $\{v_-\}$ | $0,0$ | $-1$ |
| $d$ | $v_-$ | $\{v_-\}$ | $0,0$ | $-1$ |

故两对象的 $\Gamma_c$ 都只有

$$
(v_+,1,\{v_+\})\mapsto1,\quad
(v_+,0,\{v_+\})\mapsto1,\quad
(v_-,0,\{v_-\})\mapsto-2.
$$

两者还都有 $\rho_{\rm src}=(0,\delta_{(0,l_0)})$、$(m,M,s)=(-2,0,0)$，由命题 46 在 $\Sigma_{\rm cau}$ 下同核。写 $v_+[n]=(0,+1,l_0,n)$、$v_-[n]=(0,-1,l_0,n)$，含时间时 $U_t(a)=\{v_+[-2],v_+[-1]\}$、$U_t(b)=\{v_+[-1]\}$、$U_t(c)=U_t(d)=\{v_-[0]\}$。两正格的选中位交换，因而 $\Gamma_t(X)\ne\Gamma_t(Y)$；$Q=\{v_+[-2]\}$ 的合法读数为 $1,0$。定义 22 直接给

$$
W_X=W_Y=\delta_{(-2,0)}+\delta_{(-1,0)}-2\delta_{(0,0)},\qquad
Z_X=\delta_{(-2,0)},\quad Z_Y=\delta_{(-1,0)}.
$$

所以 $\Xi$ 也不同。$a,b$ **同号**，不在单份剖面内抵消；被遗忘的是两对象剖面之差中的时间坐标。该例不复刻 B2 的添删因果边：这里固定同一个完整情境，只交换不同自身时刻的选择。附录复核全部读数。

### 32.4 命题 49：命中读数直接反演与完整 iff

**命题 49（含时间因果语言的精确观察核，repo-derived）。**

$$
\approx_{\Sigma_{{\rm cau},t}}=\ker(\Gamma_t,m,M).
\tag{TCAU-EQ}
$$

**证明。** 充分性为命题 48。反向设 $X\approx_{\Sigma_{{\rm cau},t}}Y$，固定共同有限集 $D=V_t(X)\cup V_t(Y)$。每个实际 $U$ 是 $D$ 的非空子集。对 $\eta\in\{0,1\}$，取 $J_1=\mathrm{id},J_0=N$ 及合法上下文读数

$$
f_\eta^X(Q)=q(F_{\downarrow Q}(J_\eta X))
=\sum_{\substack{e\in\Omega_X\\b_X(e)=\eta,\ U_t^X(e)\cap Q\ne\varnothing}}\sigma(e).
\tag{TCAU-HIT}
$$

这里不需要位置筛选、来源筛选或乘积。对 $W\subseteq D$，令

$$
h_\eta^X(W)=f_\eta^X(D)-f_\eta^X(D\setminus W)
=\sum_{\varnothing\ne U\subseteq W}
 \Gamma_t(X)(\min_t(U),\eta,U).
\tag{TCAU-ZETA}
$$

和式只对实际非零行解释 $\min_t$；其余 $U$ 的贡献约定为零，故不对任意形式子集假设最早元素唯一。第一项命中每个实际 $U$，第二项恰扣除不包含于 $W$ 的行；引理 2 说明同一个 $U$ 只能有一个自身属性。两次读数在**证明中**作整数相减，不增加复制孔或减读数原语。

逐 $U\subseteq D$ 复用 §28.4 的 (CAU-MOB) 直接反演式：

$$
c_\eta^X(U)=\sum_{W\subseteq U}(-1)^{|U|-|W|}h_\eta^X(W).
\tag{TCAU-MOB}
$$

该式恢复按 $(\eta,U)$ 索引的系数：代入 (TCAU-ZETA) 后每个实际 $U'\subseteq U$ 的系数仍为 §28.4 已核对的 $\mathbf1_{U'=U}$。非零的 $c_\eta^X(U)$ 由引理 2 确定唯一 $a=\min_t(U)$，于是恢复全部 $\Gamma_t$ 格；空子集系数为零。两对象的上下文读数全相同，所以反演逐格相同。若 $D=\varnothing$，两当前区域都为空、两剖面直接为空，不运行最早元素步骤。$D,Q,W$ 在这对对象的证明中固定，不是随输入改变的操作。

最后，命题 30 的左右时间阈值探针属于 $\Sigma_{\rm st}\subseteq\Sigma_{{\rm cau},t}$，故恢复全档案端点 $m,M$，包含空档案哨兵；$s$ 已由 (TCAU-SUPPORT) 恢复。合并两方向即得 iff。证毕。

与命题 23 同一像上函数图论证表明：任一对此语言充分的总读数 $h$ 都在 $h[\mathcal B]$ 上唯一恢复 $(\Gamma_t,m,M)$。这是核包含意义的最粗充分性，不是编码大小最优或任意集合谓词可计算的断言。一般量词由上述证明承担，附录只验证所列有限样本。

### 32.5 命题 50：跨批因子映射、核偏序与分层表

**命题 50（遗忘映射与严格核偏序，repo-derived）。** $\Xi$ 由 $\Gamma_t$ 沿自身的时间—位置单元边缘化：

$$
\begin{aligned}
W_X(n,p)&=\sum_{\epsilon,r,b,U}
 \Gamma_t(X)((p,\epsilon,r,n),b,U),\\
Z_X(n,p)&=\sum_{\epsilon,r,U}
 \Gamma_t(X)((p,\epsilon,r,n),1,U).
\end{aligned}
\tag{TCAU-TS}
$$

这里的单元恰为 #6684／定义 22 的 $K=\mathbb Z\times\mathbb Z^3$，背景取 $\Omega$、选择取 $A$，三个端点按原定义照搬（$s$ 由支撑取出）。**系数已经含符号，不再乘 $\epsilon$**。对 $U_0$，正确 $W$ 总和为 $0$；若重复乘符号则变成 $2$，与定义 22 不符。

无时间剖面则是沿

$$
(a,b,U)\longmapsto(\varphi(a),b,\varphi[U])
\tag{TCAU-FORGET}
$$

的系数推送，其中 $\varphi[U]$ 为**去重后的集合**。由此及已有边缘化，有严格主链

$$
\ker(\Gamma_t,m,M)
\subsetneq\ker(\Gamma_c,m,M,s)
\subsetneq\ker(\rho_{\rm src},m,M,s)
\subsetneq\ker\Theta
\subsetneq\ker\pi
\subsetneq\ker z
\subsetneq\ker q.
\tag{TCAU-CHAIN}
$$

另外有

$$
\begin{gathered}
\ker(\Gamma_t,m,M)\subsetneq\ker\Xi\subsetneq\ker\Theta,\\
\ker(\rho_{\rm src},m,M,s)\subsetneq\ker\rho_{\rm src}\subsetneq\ker\pi,\\
{=}\ \subsetneq\ {\cong_h}\ \subsetneq\ker(\Gamma_t,m,M).
\end{gathered}
\tag{TCAU-BRANCHES}
$$

$\ker\Xi$ 与 $\ker(\Gamma_c,m,M,s)$、$\ker(\rho_{\rm src},m,M,s)$ 分别不可比；$\ker\rho_{\rm src}$ 与 $\ker\Theta$ 也不可比。

**证明（映射及包含）。** 将 (TCAU-P) 的有限事件和按 $(t(e),x(e))$ 重分组，背景及选择分别就是定义 22 的 $W,Z$；无需再加权。每个 $e$ 的 $\varphi[U_t^X(e)]=U_X(e)$，自身属性也沿 $\varphi$ 忘时，故有限推送为定义 25 的 $\Gamma_c$。对自身符号及后继集求和得 §27 的 $\rho_{\rm src}$，再沿来源求和得 $\pi$；携带端点即得 $\Theta$。$\Xi\to\Theta$ 为 (TS-SP)，$\pi\to z\to q$ 为既有投影；丢端点得到另一支链。历史同构逐事件保持属性、偏序、区域与选择，因而保持 $U_t$、剖面及端点，编码相等当然给历史同构。

**证明（每条严格边与不可比的见证）。** 下表“相同”总在较粗核侧，“不同”总在较细核侧；只引用已有反例，不重新编号。

| 严格边或两核比较 | 见证及方向 |
| --- | --- |
| $\Gamma_t,m,M\to\Gamma_c,m,M,s$ | B2：旧剖面及端点相同；含时间 $Q=\{(0,+1,l_0,1)\}$ 读 $2,1$，故 $\Gamma_t$ 不同。D11 另给固定情境的忘时见证 |
| $\Gamma_c,m,M,s\to\rho_{\rm src},m,M,s$ | D7：来源双电荷及端点相同；负属性因果筛选读 $0,1$。D6 也可用；B1 不承担此边 |
| $\rho_{\rm src},m,M,s\to\Theta$ | B1：同 $\Theta=((0,\delta_0),0,0,0)$，来源 $l_7/l_8$ 分开 |
| $\Theta\to\pi$ | $U_0,T_1(U_0)$：同 $\pi=(0,\delta_0)$，端点分别全 $0$、全 $1$ |
| $\pi\to z$ | §16 的 $0_\varnothing,B_\alpha$，$\alpha=\delta_0-\delta_v$：同 $z=0$，背景分别为 $0,\alpha$ |
| $z\to q$ | $U_0$ 与其非零空间平移：同 $q=1$，$z=\delta_0,\delta_v$ |
| $\Gamma_t,m,M\to\Xi$ | B2：同 $\Xi$，含时间因果读数 $2,1$；D5 还给同 $\Xi$ 而来源不同的见证 |
| $\Xi\to\Theta$ | #6684／§26.1 D1：同 $\Theta$、同端点，联合单元 $(0,0)$ 的 $Z$ 为 $1,0$ |
| $\Xi$ 对两条来源／无时间因果核：第一方向 | D1 的空偏序使每个无时间 $U$ 都是自身单点集；两位置各有一选中正点、一未选负点，故同 $\Gamma_c$、同 $\rho_{\rm src}$、同端点而异 $\Xi$ |
| 同上：反方向 | D5：同 $\Xi$，来源 $l_0$ 读 $1,0$，故 $\rho_{\rm src}$ 不同，进而 $\Gamma_c$ 不同 |
| $\rho_{\rm src},m,M,s\to\rho_{\rm src}$ | $U_0,T_1(U_0)$：同来源双电荷，端点不同 |
| $\rho_{\rm src}\to\pi$ | B1：同空间双电荷，来源双电荷不同 |
| $\rho_{\rm src}$ 与 $\Theta$ 不可比 | $U_0,T_1(U_0)$ 同前者异后者；B1 同后者异前者 |
| 编码相等 $\to$ 历史同构 | §4 的非平凡事件重命名：历史同构而编码不同 |
| 历史同构 $\to\Gamma_t,m,M$ | D10：同剖面、同端点，时刻 $1$ 上层入度多重集为 $\{1,1\}$ 与 $\{2,0\}$，历史不同构 |

每行给出严格性或不包含所需的一对实际平衡表示，配合已证因子映射即完成偏序结算。证毕。

下表追加 §18 的分层视图；“适用签名”只记已证观察核的语言，不借表新增任何代数律。

| 层 | 所存信息 | 适用签名 | 遗忘内容 | 见证 |
| --- | --- | --- | --- | --- |
| 编码相等 | 全档案、属性、偏序、区域、选择及出现标签 | 本批运算的严格编码解释 | 无编码遗忘 | §4 重命名后仅同构 |
| 历史同构 | 全部历史结构，容许保属性的出现重命名 | 本批去身份操作保同构；不称其观察核 | 出现标签 | D10 同剖面而不同构 |
| $\ker(\Gamma_t,m,M)$ | 含时间自身属性、后继属性集、两选择位及全档案端点 | $\Sigma_{{\rm cau},t}$，命题 49 | 目标重数、入射关联及未记录的旧档案细节 | D10；B2 分开下一层 |
| $\ker(\Gamma_c,m,M,s)$ | 无时间因果剖面及三个端点 | $\Sigma_{\rm cau}$，命题 46 | 属性行内的自身／目标时间 | B2、D11；D7 分开来源层 |
| $\ker(\rho_{\rm src},m,M,s)$ | 来源—位置双电荷及端点 | $\Sigma_{\rm src}\cup\Sigma_{\rm st}$，命题 44 | 因果后继属性集、联合时间信息 | D7、D1 |
| $\ker\Xi$（支链） | 时间—位置双电荷及三个端点 | $\Sigma_{\rm ts}$ 及 §25.3 指定扩展，命题 40–41 | 来源、因果关联 | D5、B2；与上两行不可比 |
| $\ker\rho_{\rm src}$（支链） | 来源—位置双电荷 | $\Sigma_{\rm src}$，命题 43 | 因果、时间与档案端点 | $U_0,T_1(U_0)$；与 $\Theta$ 不可比 |
| $\ker\Theta$ | 空间双电荷及三个端点 | $\Sigma_{\rm st}$，命题 30 | 来源、因果、联合单元信息 | B1、D1 |
| $\ker\pi$ | 背景与选择的空间电荷 | $\Sigma_{\rm sp}$，命题 22 | 时间、来源与历史 | $U_0,T_1(U_0)$ |
| $\ker z$ | 选择的空间电荷 | $\Sigma_z$，命题 22 | 背景电荷及上述历史 | §16 的 $B_\alpha$ |
| $\ker q$ | 所选总电荷 | $\Sigma_{\rm arith}$，命题 22 | 空间分布及上述背景、历史 | $U_0$ 的非零空间平移 |

**表达边界（ARCH-R4-A1）。** 从 $\Gamma_t$ 恢复 $\Xi$ 不等于存在保持完整 $C$ 的 $\Sigma_{{\rm cau},t}$ 上下文实现定义 23 的 $F_B$。柱集 $B=\mathbb Z\times S$ 时已有 $F_B=F_S$，故“所有 $F_B$ 都不可表达”为假。一般 $B$ 的可表达性分类**未测**：本批仅证明下一节的具名单元边界，没有给剩余 $B$ 的统一判据，亦未逐类反驳其可表达性。$M_P$ 同样不并入；含它的混合闭包在本批**未测**，不能从命题 41 或两核取交推出。

### 32.6 历史上界与具名区域的表达边界

由命题 49，D10 升级为“**全部 $\Sigma_{{\rm cau},t}$ 上下文不可区分，而历史不同构**”：两对象端点同为 $(m,M,s)=(0,1,1)$，§28.7 已给同 $\Gamma_t$ 及不同上层入度多重集，直接应用 iff。没有增加入度原语。$\Gamma_t$ 的全部实际像分类**未测**，因为本批只在实际像上证明更新和观察核，没有构造任意形式剖面的历史实现；物理解释、量子模型及 Lean 形式化也**未测**，本批仅含普通 ZFC 证明与有限核验。

**命题 51（具名单元的丰富输出不可表达而 $q$ 读数可表达，repo-derived）。** 取
$B=\{(1,0)\}\subseteq\mathbb Z\times\mathbb Z^3$。不存在固定的有限 $\Sigma_{{\rm cau},t}$ 单孔上下文 $C$，使对每个平衡表示 $X$ 都有定义且

$$
C(X)\cong_h F_B(X).
\tag{TCAU-NONEXP}
$$

但对全部 $X\in\mathcal B$ 有合法的单孔 $q$ 表达式

$$
q(F_BX)=q\bigl(F_{\downarrow Q^*}(X\boxtimes U_0)\bigr),
\qquad
Q^*=\{(0,\epsilon,r,2):\epsilon\in\{+1,-1\},\ r\in T\}.
\tag{TCAU-QEXP}
$$

**证明（丰富输出的结构限制）。** 假设 $C$ 满足 (TCAU-NONEXP)。所有允许操作都不减少档案基数；每个带非空档案固定参数的二元步骤都严格增加基数（定义 4–6），而 $F_B$ 保持原档案基数，后续步骤不能撤销增加。因此这种二元步骤不能出现。空档案参数的并行或时间复合只加可去除的标签，模历史同构可删；它们的时间守卫空真。空档案参数的乘法使当前区域变空，余下允许的一元操作及空档案二元步骤不能恢复非空区域，而 $F_B$ 从不改变 $\Omega$，故也不能出现。

于是 $C$ 模历史同构只剩 $N,F_S,F_L,F_{\downarrow Q},T_k$ 的有限复合。其总时间平移必须为零：对任一非空有限档案，保时间的同构要求其最小时刻不变，而总平移 $k$ 使最小时刻增加 $k$。这些删步在去身份语言下合法：属性筛选与可达性均在历史同构下运输，不依赖被去掉的标签。

**反例 D12（证明中的四事件选择族，repo-derived）。** 固定 $E=\Omega=\{a,b,c,d\}$，位置全 $0$、来源全 $l_0$，符号 $+,+,-,-$，时间 $0,1,0,0$，唯一严格边 $a\prec b$。令 $X_A$ 的选择为任意 $A\subseteq\{a,b\}$，两个负点孤立且未选。各步的累计平移在这四个输入上相同；每个位置／来源筛选对 $a,b$ 的掩码相等，每个因果筛选由 $U_t(a)\supseteq U_t(b)$ 给掩码 $d_a\ge d_b$，且这些掩码不依赖选择。

总平移为零后，$a,b$ 分别是唯一的时刻 $0,1$ 正点，任何历史同构都必须固定它们。因此目标 $F_B(X_A)$ 要求 $b$ 的输出位等于任意输入位 $b_A$，$a$ 的输出位恒为零。若复合中某一步 $d_b=0$，该步就将 $b$ 的位清为常数，之后仅有取补和乘固定掩码，不能恢复对输入 $b_A$ 的依赖，矛盾。故每个筛选都有 $d_b=1$，继而 $d_a=1$。$b$ 的输出等于输入还迫使 $N$ 次数为偶数，于是 $a$ 的选择位也原样保留；取 $a\in A$ 即与恒删 $a$ 矛盾。这排除了任意长度的固定有限复合，而非仅检查某个深度。偶数次 $N$ 的结论是在排除清零掩码之后使用的。

**证明（$q$ 层的正面表达式）。** $U_0$ 只选零位置、时刻 $0$、符号为正的点，新选中事件恰为 $(e,u_+)$，$e\in A_X$，其位置为 $x(e)$、符号仍为 $\sigma(e)$、时间为 $\max(t(e),0)+1$。乘积当前区域为反链，故 $F_{\downarrow Q^*}$ 恰按新事件自身属性筛选。对整数 $t(e)$，$\max(t(e),0)+1=2$ 当且仅当 $t(e)=1$；位置为零的条件也恰为 $x(e)=0$。有限求和即得 (TCAU-QEXP)，空区域时两边均为零。证毕。

(TCAU-QEXP) 的乘积改变档案与当前区域，故不满足 (TCAU-NONEXP) 的丰富输出要求；两结论的观察层不同。柱集仍由 $F_S$ 完整表达；除本节具名 $B$ 和柱集外的一般区域分类仍为“未测”，不从此例推出所有非柱集不可表达。

<a id="pr4-evidence"></a>

## 33. PR4 本批产地与核验收据

### 33.1 实施、先验暴露与思考输入

本批属于 caller 的 `consensus-rnd:sshx` 流程，由一个 Codex 实施席以 `codex-cli` 载体在工作树 `/Users/auricstudio/trureturing-csa-upgrade-pr4-0910`、分支 `lane/theory/csa-upgrade-pr4-0910` 落地。该 worker 没有单独调用本地 skill，没有另派子席；输入是 caller 收敛 brief（含 R1-PR4）、完整 `CLAUDE.md`、既有卷文及前批有限核验，故为 `repo-prior-exposed`，不冒充盲推导或独立评审。

原始基线是 `34d73f32f87c9a50af4890ffb5b141ce0af5110b`。开工实际执行 `git fetch origin dev && git merge-tree --write-tree origin/dev HEAD`，退出 0，试合树为 `a31ec0c72dcfff2c53206eaa0e3f1eca8903392c`；随后 `git merge origin/dev` 退出 0，以 fast-forward 合入 `49c7aecf0c64e27d43dc8bea8fd18ca438080c05`。两版卷字节相同，仍为 3251 行，最大编号为定义 25、命题 47、引理 1、反例 D10，故本批续为 §32–33、定义 26、命题 48–51、引理 2、D11–D12、增补 M，没有 rebase。

**思考构成与判词摘要均据 caller／R1 记录转述**：六席中五席一致；`parsimony` 与 `natural-ownership` 给出最早元素及命中读数直接反演，`worth`、`teleology`、`proportional-containment` 要求将 D11 归为剖面之差的忘时见证并删去可选文献升级表。第六席的具体判词、各思考席模型与载体、原始投票工件未向本 worker 提供，未作独立核验，不据此宣称异模型共识。可选命题 51 的证明形态据 `natural-ownership` 方案；本席补明“保留 b 的任意输入位 ⇒ 不得出现清零掩码 ⇒ a 也不被筛除”的依赖步骤，再使用 N 的偶数性。

本 worker 亲跑下列附录、ingest 与 git／字节核对；这些是实施自查，不是评审判词。caller 后续亲验、独立评审、CI 与合入结果均未向本席提供，记“未测”，本收据不预报它们。

本批形态为 **ingest**：`contextual-spacetime-arithmetic` 源卷追加经 canonical writer 进入 atom CAS 及该源的 `residual-open` backfill。本批没有 deposit／cover；没有新增 Lean、axiom、判官、schema 或 tools，不报告新增冻结或已吸收状态。数学状态为 `repo-derived` 的普通 ZFC 推导加有限核验。

文献仅内部复用 §28.4 已列的 Rota (1964) 反演来源（框架标签 `literature-attested`），不重复增加引文。写作时本席查询该已有 DOI 的 Crossref 元数据，HTTP 200，确认 DOI 与出版年 1964；原始响应及口径在 runner 的 `rota-crossref.json`、`literature-check.json`。该查询不等于通读原文，未升级 §31.1 的任何核读状态。全球新颖性检索与原文全文核读均为“未测”；本批只复用已给直接公式，不以文献全文为新增证明前提，不作优先权主张。

### 33.2 附录实际命令与有限检查范围

本席在上述工作树实际运行下列原文命令，退出码 **0**，stderr 为空；唯一 Python 块沿用 `Rich/add/mul/neg/temporal/filt` 及 `pr3_` 的 `timed=True` 辅助函数，新增段共 **313 行**，只插在原末行打印之前。

```sh
sed -n '/^```python$/,/^```$/p' docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md | sed '1d;$d' | python3 -
```

stdout 的 `pr4_` 行与最后一行原文为：

```text
pr4_temporal_causal: random_samples=64 cases=83 updates=2189 endpoint_updates=2189 earliest_rows=208 product_antichains=166 guard_success=121 strict_failures=128 context_reads=3548 mobius_profiles=89 mobius_coefficients=3548 xi_paths=2272 forget_paths=2272 kernel_edges=17 D11=1,0 D11_Z_times=-2,-1 common_k=-3 shifted_probe=1,0 fixed_U0=1,1 q_expression=83 B2=2,1 D10_indegrees=[1, 1],[0, 2] c_then_b=1,0
ALL_FINITE_CHECKS_PASSED
```

计数均由执行累加。随机种子 `2026091004`，64 个随机平衡表示的当前区域大小取 0、2、4、6，当前时间取整数 −5 至 4，额外档案点数取 0、1、2，边按严格时标生成后取传递闭包，选择任意子集。加定向见证共 83 个输入；覆盖空档案、非空档案而空当前区域、负时刻、最高当前时刻在 W/Z 中抵消、未选目标、当前区域外目标及严格失败传播。更新同时比较剖面及三个端点；乘积只断言该次新当前区域反链与单点后继属性集。

89 份反演核验为 83 个输入加三对对象各用共同 D 的六次恢复；恢复器只接收固定查询词汇 D 和终端上下文读数表，不接收 Rich 对象、不调用剖面函数。规范序列化后逐字节恢复两选择位的全部系数，并断言每个非零格的自身属性恰为 U 的唯一最早元素。Ξ 的 2272 次双路径比较，一条直接分别遍历 Ω/A，另一条只消费 Γ_t 系数及端点，两路不共用边缘化函数；另检查忘时推送的集合去重。83 次 q 表达式检查包含 D12 的四个选择输入，不代替命题 51 对全部有限上下文的否定证明。17 次核比较只核对具名见证的方向，不代替命题 50 的因子映射证明。

原始 stdout/stderr 与命令退出码存于 runner 的 `appendix.stdout.log`、`appendix.stderr.log`、`appendix-receipt.json`。更强结论的边界仍按 §32.5–32.6：一般 F_B 分类、含 M_P 的混合闭包、Γ_t 全部实际像、物理模型和 Lean 均为“未测”，各项未测原因已在相应证明边界说明。

### 33.3 ingest 与固定检查点的 git 读数

首次摄入的已提交输入为 `7a21063aa1ae808ecd2ffc867063058fe5b80840`（§32 提交 `a6d73cfaa8`，附录提交 `7a21063aa1`），摄入基线固定为上述合入 dev SHA。实际命令：

```sh
BASE=49c7aecf0c64e27d43dc8bea8fd18ca438080c05 make ingest SOURCE="contextual-spacetime-arithmetic docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md"
```

退出码 **0**，stderr 为空；新增 **57 个 atom 与 57 个 residual-open backfill**，新增路径的 atom_id 两侧成对。stdout 原文：

```text
INGEST residual_open_added=57 skipped_existing=217 coarse_fallbacks=0 open_genres=0 cas_objects_written=57 ledger_changed=true
```

本次 114 个生成文件已提交为 `0fbf39866eb530d2756c2ddb5e3859503801806e`，内容检出 §32、定义 26、引理 2、命题 48–51、D11/D12 及 PR4 附录段。以下读数仅指该固定检查点，**截至本节追加之前**：

| 读数口径 | 实测值 |
| --- | --- |
| 本卷相对摄入基线的增删 | +616／−0 行（§32 为 303 行，附录为 313 行） |
| 本卷行数 | 3867 |
| 新增 atom／backfill | 57／57 |
| `git status --porcelain=v1` | 退出 0，stdout 为空 |
| `git diff --shortstat 49c7aecf0c64e27d43dc8bea8fd18ca438080c05..0fbf39866eb530d2756c2ddb5e3859503801806e` | 115 files changed, 3864 insertions(+) |
| `git diff --name-only` 的路径集合 | 本卷 + `Meta/Digestion/atoms/sha256` + `Meta/Digestion/backfill/contextual-spacetime-arithmetic/residual-open` |

只追加的字节核对以基线本卷 **248728 字节** 为对象：去掉唯一新增 pr4_ 插入后的前缀逐字节等于基线全文，且只有一个 Python 块。它同时核对顶部导航与 §1–31；不将“未去掉附录插入的整段原始前缀相等”报告为通过。

本节是上述固定检查点之后的正文追加，仍须以同一命令再运行 ingest，使本节产地与收据进入消化账；最终累计计数不以这里的 57／57 代替。正文最后改动之后的摄入、最终 HEAD、逐节提交、推送、试合及干净状态，由 runner 目录 `/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/csa-pr4-impl-0910/attempt-1` 的 `result.json` 与 `implementation.log` 绑定记录。本批按 brief 只交付推送分支，不开 PR；这不是持续研究目标、评审或仓库准入已完成的声明。

<a id="pr5-mixed"></a>

## 34. PR5 增补 N：混合语言闭包与区域筛选的表达性分类

本节接续 §32 的 ARCH-R4-A1：先将定义 23 的区域筛选及定义 24 的配对选择加入含时间因果语言，证明混合闭包；再分类区域筛选在原语言中的丰富输出表达性。载体、单孔上下文、历史同构分别沿用定义 3、16、7。以下新增定义、引理、命题、反例及直接推论均为 `repo-derived`，没有新外部引用，不作 `suspected-novel` 或优先权声明；有限实验只核对所列实例，不替代全称证明。

### 34.1 定义 27：混合语言与表达性量词

**定义 27（混合语言与丰富输出表达性，repo-derived）。** 沿用 $K=\mathbb Z\times\mathbb Z^3$，令

$$
\Sigma_{\rm mix}=\Sigma_{{\rm cau},t}
 \cup\{F_B:B\subseteq K\}
 \cup\{M_P:P\subseteq K\times K\}.
\tag{MIX-LANG}
$$

$F_B,M_P$ 分别严格使用定义 23、24 的函数：前者检查事件自身的时间—位置单元，后者只限制完整档案乘积的选择。依 #6684 的命名，$\Sigma_{\rm ts}$ **不含** $M_P$；含全部 $M_P$ 的是 §25.3 的 $\Sigma_{\rm ts}^{\rm pair}$。本节不改动这两个旧签名的名字或定义。

载体仍为全部平衡表示 $\mathcal B$。上下文仍是定义 16 的恒等孔、全部固定丰富参数、每个二元操作的两个槽位及任意有限复合；任何基本步失败都严格向外传播。对一个预先指定的 $B$，称 $F_B$ 在 $\Sigma_{{\rm cau},t}$ 中可作**丰富输出表达**，当且仅当

$$
\exists\,\text{固定有限单孔上下文 }C_B\in\operatorname{Ctx}_{\Sigma_{{\rm cau},t}}
\quad\forall X\in\mathcal B:\quad
 C_B(X)\text{ 有定义且 }C_B(X)\cong_h F_B(X).
\tag{MIX-HEXPR}
$$

$B$ 可以决定上下文、平移和全部参数，$X$ 不得决定它们；量词次序是 $\exists C_B\,\forall X$。三个问题分别是：**在 $\Gamma_t$ 上下降**，即存在由输入剖面确定输出剖面的语义算子；**固定上下文至 $\cong_h$ 表达**，即 (MIX-HEXPR)；**仅 $q$ 相等的表达**，即将同一量词中的历史同构换为 $q(C_B(X))=q(F_B(X))$。后两项要求原语言中的一个固定上下文，第一项没有该要求。命题 52、53、54 分别处理这些层次；命题 51／D12 已表明仅 $q$ 相等不能推出历史同构表达。

### 34.2 命题 52：混合语言闭包

**命题 52（混合语言的精确观察核，repo-derived）。** 对 $a=(p,\epsilon,r,n)$、$a'=(p',\epsilon',r',n')$，将下表两行接到命题 48 的八行更新表，仍采用该命题的 $a\diamond_t a'$、同格系数相加和端点约定：

| 新操作 | 剖面格推送 | 推送系数 |
| --- | --- | --- |
| $F_BX$ | $(a,b,U)\mapsto(a,b\mathbf1_B(n,p),U)$ | 原系数不变 |
| $M_P(X,Y)$ | $((a,b,U),(a',b',U'))\mapsto(a\diamond_t a',bb'\mathbf1_P((n,p),(n',p')),\{a\diamond_t a'\})$ | 两输入格的系数之积 |

#### 当前背景、端点与扩签名归纳

$F_B$ 保持完整情境 $C$，包括 $\Omega,U_t,m,M$；它的判据是**自身单元**是否在 $B$ 中，不是 $U\cap Q_B$ 是否非空。拒绝一个已选事件时，该事件进入 $b=0$ 行，不从 $\Gamma_t$ 删除。$M_P$ 对全部 $\Omega_X\times\Omega_Y$ 生成新当前事件，包括未选父事件构成的对和不满足 $P$ 的对；这些对仅有选中位 $0$。$P$ 可不对称，上表中的父单元顺序不能交换。谓词不乘到系数或 $\Omega$ 上，**系数已经含符号，不再乘 $\epsilon\epsilon'$**。

$M_P$ 的完整情境沿定义 6 的乘积：旧档案保留但不进当前剖面；新当前事件无出边，故其 $U_t$ 为自身属性单点集。以支撑按 (TCAU-SUPPORT) 恢复 $s_X,s_Y$，置 $g=\gamma(s_X,s_Y)$，端点为

$$
(m,M,s)_{M_P(X,Y)}
=(\min(m_X,m_Y),\max(M_X,M_Y,g),g).
\tag{MIX-ENDPOINTS}
$$

这是命题 29 的完整乘积端点，含空区域和旧档案端点，不用被选父事件的最高时刻替代 $s$。结论为

$$
\approx_{\Sigma_{\rm mix}}=\ker(\Gamma_t,m,M).
\tag{MIX-KERNEL}
$$

**证明（两种新增操作）。** $F_B$ 只筛选 $A$，所以总定义且保持 $\Omega$ 的平衡；同一剖面格的自身单元相同，选中位按表更新。多个格碰撞时将原有符号系数相加，恰等于逐事件分组。$M_P$ 使用合法平衡的完整乘积情境，限制选择不改变平衡，故亦总定义。固定两父格后，父属性、父选择位及 $P$ 的真假均固定；全部父对的新符号之和就是两个已带符号格系数的乘积。新点的属性为 $a\diamond_t a'$、选中位为表中乘积，且新点之间无严格边，得到第二行。未选父对及谓词不满足的对也在这个有限双和中。新点晚于父点，旧档案全部保留，所以端点仍为 (MIX-ENDPOINTS)，与定义 24 完全一致。

**证明（扩签名后的逐步归纳）。** 令摘要 $H(X)=(\Gamma_t(X),m_X,M_X)$。$s$ 和 $V_t$ 可由剖面支撑恢复，终端读数为 $q(X)=\sum_{a,U}\Gamma_t(X)(a,1,U)$。命题 48 已给旧原语逐项的更新与 $\triangleright$ 守卫；本表为扩充后的同一张表补上两个基本步。若 $H(X)=H(Y)$，新增的一元步 $F_B$ 由同一 $B$ 推送同一剖面，保持端点；新增二元步 $M_P(\square,Z)$ 和 $M_P(Z,\square)$ 各自在两个输入位置上使用同一个固定参数 $Z\in\mathcal B$，按有序父格对推送，也给相同摘要。不能因 $P$ 不对称而漏掉一个槽位。

现按定义 16 对**全部 $\Sigma_{\rm mix}$ 上下文**归纳。恒等孔保持摘要；任一基本步由上述扩充表决定成功输出摘要，唯一部分原语 $\triangleright$ 的守卫 $M_{\rm left}<m_{\rm right}$ 也由摘要决定，故两侧同步成功或失败。有限复合中，内层失败则两侧都严格失败，后接 $N$、空筛选或零因子不能把它变成正常零；内层成功则输出摘要相同，继续归纳外层。成功到终端时 $q$ 相等，故 $\ker H\subseteq\approx_{\Sigma_{\rm mix}}$。反向由 $\Sigma_{{\rm cau},t}\subseteq\Sigma_{\rm mix}$ 和命题 49 得 $\approx_{\Sigma_{\rm mix}}\subseteq\ker H$。这里消费的是命题 48 的**旧基本更新**并补证新基本步，没有把旧签名充分性直接改称新签名充分性，也没有用两旧核取交代替归纳。证毕。

**推论（较小语言的核仍成立）。** 按定义 23、24、27 有

$$
\Sigma_{\rm ts}\subseteq\Sigma_{\rm ts}^{\rm pair}\subseteq\Sigma_{\rm mix},
\qquad
\approx_{\Sigma_{\rm mix}}=\ker(\Gamma_t,m,M)
\subsetneq\ker\Xi
=\approx_{\Sigma_{\rm ts}^{\rm pair}}
=\approx_{\Sigma_{\rm ts}}.
\tag{MIX-COMPARISON}
$$

最后两个核等式分别消费命题 41、40。严格性直接引用 §32.5 的 B2：同 $\Xi$、含时间因果读数 $2,1$；该处 D5 的来源见证也可用，不重新编号。#6684 的命题 40 没有被推翻，它刻画较小语言的较粗核，不能改称 $\Sigma_{\rm mix}$ 的核。ARCH-R4-A1 的“未证混合闭包”由命题 52 闭合。语义下降仍不推出 (MIX-HEXPR)，其失败区域由命题 53 和 D13–D14 给出；$\Gamma_t$ 恢复历史的更强断言仍由 D10 反驳。

### 34.3 引理 3：保历史上下文的归约与位保持原则

**引理 3（保历史归约与位保持，repo-derived）。** 设某固定有限 $\Sigma_{{\rm cau},t}$ 单孔上下文对全部输入满足 (MIX-HEXPR)，则有以下归约；前三步只用 $C_B(X)\cong_hF_B(X)$，对任意 $B$ 都成立。

① 所有原语都不减档案基数。带非空档案固定参数的任一二元步骤，由定义 4–6 严格增加 $|E|$，后续不可减；而 $F_B$ 保持 $|E|$，故这种步骤不出现。空档案参数的 $\boxtimes$ 清空 $\Omega$；排除前类参数后，后续步骤不能恢复非空 $\Omega$，与任一非空当前区域输入的目标不符，故也不出现。空参数的 $\boxplus/\triangleright$ 只加可去标签，后者守卫空真；去身份原语在历史同构下运输，所以模 $\cong_h$ 可删去这些步骤。这里不要求 $B$ 非空：即使 $B=\varnothing$，目标仍保留原 $\Omega$。

② 模历史同构只剩 $N,F_S,F_L,F_{\downarrow Q},T_k$ 的有限复合。总时移必须为 $0$：取非空有限档案，其最小时刻在目标中保持，而总时移 $k$ 会使它增加 $k$；保时间的历史同构迫使 $k=0$。

③ 将每个因果谓词按该步之前的累计平移拉回原坐标：若累计时移为 $j$，把 $Q$ 换成 $\tau_j^{-1}[Q]$。空间和来源掩码不受时移影响。每个筛选掩码只依赖完整情境，不依赖 $A$；同一情境的全部选择输入上，累计平移也相同。因此在固定情境上，每个事件的选择位只经历一个有限词，基本变换恰为

$$
z\longmapsto1-z,\qquad z\longmapsto h_i z,
\quad h_i\in\{0,1\},\quad h_i\text{ 与输入选择无关}.
\tag{MIX-BIT}
$$

④ **位保持原则：** 若某个由属性唯一标认的事件，其输出位须等于任意输入位，则每个 $h_i=1$。因为任一次 $h_i=0$ 都使两个输入位的后续值相同，其后的取补与固定掩码不能恢复已经失去的依赖。**在排除全部清零掩码之后**，该事件才只经历取补，输出恒等因而迫使 $N$ 次数为偶数。先断言偶数次 $N$ 再排除清零不是本证明的次序。以上逐步论证同时证明全部结论。证毕。

### 34.4 命题 53：区域筛选至历史同构的完整表达判据

对任意 $B\subseteq K$ 记

$$
S_B=\{p:\exists t\ (t,p)\in B\},\qquad
Q_B=\{(p,\epsilon,r,t):(t,p)\in B,\ \epsilon\in\{\pm1\},\ r\in T\}.
$$

定义条件

$$
H_B:\quad
\forall p\in S_B\ \forall q\in\mathbb Z^3\ \forall t<s:\quad
(s,q)\in B\ \Longrightarrow\ (t,p)\in B.
\tag{MIX-H}
$$

**命题 53（丰富输出表达性的完整分类，repo-derived）。** 以下三项等价：

1. 存在固定有限 $\Sigma_{{\rm cau},t}$ 单孔上下文，对全部 $X\in\mathcal B$ 有定义且输出与 $F_B(X)$ 历史同构。
2. $H_B$ 成立。
3. $B=\mathbb Z\times S$（含 $S=\varnothing$），或存在 $T_B\in\mathbb Z$、$\varnothing\ne R_B\subseteq S_B$ 使

$$
B=(\{t<T_B\}\times S_B)\cup(\{T_B\}\times R_B).
\tag{MIX-NORMAL}
$$

条件成立时有**编码等式**，强于历史同构：

$$
F_B=F_{S_B}\circ F_{\downarrow Q_B}.
\tag{MIX-ENCODE}
$$

**证明（2 ⇒ 1）。** 两个筛选都总定义且保持完整情境，参数只依赖 $B$。若已选事件 $e$ 的自身单元属于 $B$，则 $x(e)\in S_B$，且 $e$ 本身就是 $Q_B$ 中的当前见证，所以保留。反之，若 $e$ 被复合保留，则 $x(e)\in S_B$，并有 $d\in\Omega$ 满足 $e\preceq d$、$(t(d),x(d))\in B$。$d=e$ 时结论直接成立；$e\prec d$ 时由定义 1 有 $t(e)<t(d)$，由 $H_B$ 得 $(t(e),x(e))\in B$。因此两边选择逐事件相同，完整情境又不变，即得 (MIX-ENCODE)。目标 $d$ 可以未选，时刻可以为任意负整数，证明均未排除它们。

**证明（1 ⇒ 2）。** $B=\varnothing$ 时由空间筛选 $F_\varnothing$ 实现，$H_B$ 空真，单列结束。以下设 $B\ne\varnothing$，应用引理 3。对每个 $(t,p)\in B$、每个来源 $r\in T$，取同单元、同来源、相反符号的一正一负平衡反链，$E=\Omega$。正负符号分别唯一标认两个事件；逐个变动目标事件的输入位，目标 $F_B$ 必须保留该位。由位保持原则，该事件在每一步的掩码都为 $1$。

对这些反链逐属性量化，得到同一固定词的约束：每个空间掩码包含 $S_B$；每个来源掩码等于全部 $T$（用 $B$ 中任一单元并遍历全部来源）；每个拉回的因果谓词包含 $Q_B$（反链的 $U_t$ 恰为自身单点，遍历两种符号与全部来源）。全部清零已排除后，任一上述被保留事件还给出 $N$ 总次数为偶数。

若 $H_B$ 失败，取 $p\in S_B$、$t<s$、$(s,q)\in B$ 而 $(t,p)\notin B$。造同来源的正事件 $a@(t,p)\prec b@(s,q)$，另加两个孤立未选负事件使当前区域平衡，取 $E=\Omega$，唯一严格边为 $a\prec b$。跨位置边合法：定义 1 只要求时间严格增加；等时严格边被该定义禁止，所以此处确实使用 $t<s$。$a$ 的每个空间掩码为 $1$，因为 $p\in S_B$；来源掩码全部为 $1$；每个拉回因果谓词都含 $\alpha_t(b)\in Q_B$，而 $U_t(a)$ 含该属性，故其因果掩码也为 $1$。偶数次 $N$ 于是原样保留 $a$ 的输入位。取只选 $a$ 的输入，输出仍选 $a$，但 $F_B$ 恒删它；$a$ 是其时刻唯一正点，总时移为零，历史同构不能换一个事件代它。矛盾。§34.5 的 D14 还给出包含必须保留的第三正点的六事件自足反证，不依赖把单一筛选的失败推广为全语言失败。

**证明（2 ⇔ 3）。** 空集已属于柱集。设 $B\ne\varnothing$ 且 $H_B$ 成立。若时间投影无上界，则对每个 $p\in S_B$ 及每个整数 $t$，可取 $(s,q)\in B$ 且 $s>t$；条件迫使 $(t,p)\in B$，所以 $B=\mathbb Z\times S_B$。若时间投影有上界，它作为非空整数集有最大元 $T_B$。令 $R_B=\{p:(T_B,p)\in B\}\ne\varnothing$；$H_B$ 迫使全部活动位置含全部 $t<T_B$，最大性排除全部 $t>T_B$，恰得 (MIX-NORMAL)。反向，柱集在活动位置含全部时刻；正常形中若 $(s,q)\in B$ 且 $t<s$，则 $t<T_B$，故每个 $p\in S_B$ 都有 $(t,p)\in B$。两种形式均满足 $H_B$。证毕。

**位置相关阈值推论。** 对各非空截面给定 $h(p)\in\mathbb Z\cup\{+\infty\}$，令 $B=\bigcup_p(\{t\le h(p)\}\times\{p\})$，其中 $h(p)=+\infty$ 表示全 $\mathbb Z$。该区域可表达，当且仅当所有非空截面都是全 $\mathbb Z$，或所有非空截面都是有限阈值且只取两个相邻值 $\tau-1,\tau$（可只取其中一个值，最大差 $\le1$）。空区域仍可表达。理由是 (MIX-NORMAL) 中顶层位置阈值为 $T_B$，其余活动位置为 $T_B-1$；反向这些形式直接满足条件。阈值差 $\ge2$ 的不可表达性见 D14；一列全 $\mathbb Z$、另一活动列阈值有限 $h(p)$ 时，取 $t=h(p)+1$，再在全列取 $s>t$，即构成 $H_B$ 的失败见证。不能把“每位置分别时间下闭”当成充分条件。

**旧结论的结算与推论。** 命题 51／D12 的 $B=\{(1,0)\}$ 违反 $H_B$，是同位置特例。柱集的 $F_B=F_S$、全空间过去半轴 $B=\{t\le\tau\}\times\mathbb Z^3$ 的 $F_B=F_{\downarrow Q_\tau}$ 仍为编码等式，其中 $Q_\tau=\{a\in\mathrm{Attr}_t:a\text{ 的时间}\le\tau\}$；任意有限交满足 $F_{B_1\cap B_2}=F_{B_1}\circ F_{B_2}$，因为各筛选保持同一情境并逐位相乘。故这些原充分族保留为本判据的推论。§32.5 与 §32.6 的“一般 $F_B$ 可表达性未测”文字保持原样，其所指固定有限上下文至 $\cong_h$ 的分类**由命题 53 结算**，不重写旧批次的当时记录。

**量化边界。** 本 iff 专指定义 16 的固定有限单孔上下文、定义 26 的 $\Sigma_{{\rm cau},t}$、定义 7 的 $\cong_h$。它不分类一般 $q$ 表达性，不扩张到复制孔、改变 $\Omega$ 的筛选、身份查询、输入自适应参数或未来扩签名；这些扩张不在证明域内，未测。$B$ 可任意无限，ZFC 中的参数存在也不承诺成员判定可计算。

### 34.5 反例 D13、D14：时间逆序与跨位置阈值

**反例 D13（同位置时间逆序的一般见证族，repo-derived）。** 设 $t_1<t_2$，同位置 $p$ 满足 $(t_2,p)\in B$、$(t_1,p)\notin B$。取 $E=\Omega=\{a,b,c,d\}$，来源均为 $r_0$，位置均为 $p$；$a,b$ 为时刻 $t_1,t_2$ 的正事件，$c,d$ 为时刻 $t_1$ 的孤立负事件，唯一严格边 $a\prec b$。只让 $A$ 遍历 $\varnothing,\{a\},\{b\},\{a,b\}$，负事件一直未选。解析读数为

| $A$ | $\varnothing$ | $\{a\}$ | $\{b\}$ | $\{a,b\}$ |
| --- | --- | --- | --- | --- |
| $q(F_BX_A)$ | 0 | 0 | 1 | 1 |
| $q(F_{\downarrow\{\alpha_t(b)\}}X_A)$ | 0 | 1 | 1 | 2 |

#### 四个读数的证明边界

这四个读数本身不证明全语言不可表达；承重的是引理 3 对任意有限词的位保持论证及命题 53。此处给的是任意 $t_1<t_2$ 与任意同位置逆序区域的见证模式，D12 保留旧编号作为其已知特例；附录取 $(-4,-1),(-2,3),(4,7)$ 三组时间，不将旧四事件实例另算一次新发现。

#### 跨位置六事件反证

**反例 D14（跨位置阈值差 2 的六事件自足族，repo-derived）。** 取 $p=(0,0,0)$、$q=(1,0,0)$，

$$
B=(\{t\le0\}\times\{p\})\cup(\{t\le2\}\times\{q\}).
\tag{MIX-D14}
$$

虽然两个非空截面分别向下闭，$H_B$ 仍失败：$(2,q)\in B$、$1<2$，而 $(1,p)\notin B$。取三个同来源正事件 $a@(1,p)\prec b@(2,q)$、$c@(0,p)$，唯一严格边为 $a\prec b$；另加三个时刻 $0$、位置 $p$、同来源的孤立未选负事件，令 $E=\Omega$ 为全部六点。$A$ 遍历 $\{a,b,c\}$ 的全部八个子集。目标删 $a$、保 $b,c$；三个正点的时间—位置属性两两可区分，任何保属性历史同构都固定它们。

假定一个上下文对这个族实现目标且满足全输入保历史要求，用引理 3 归约。保 $c$ 的任意位迫使每个空间掩码在 $p$ 处为 $1$，遂也在 $a$ 处为 $1$。保 $b$ 的任意位迫使每个来源掩码在共同来源处为 $1$，每个拉回因果掩码在 $b$ 处为 $1$；因为 $U_t(b)\subseteq U_t(a)$，后者也在 $a$ 处为 $1$。对被保留位排除清零之后，$N$ 次数为偶数。因此 $a$ 位仍原样保留，取 $A=\{a\}$ 即矛盾。**第三个必须保留的正点 $c$ 正是全上下文反证中强迫空间掩码保留 $p$ 的环节。**

单一 $F_{\downarrow Q_B}$，即使随后接 $F_{S_B}$，会让 $a$ 通过未选的目标 $b$ 而保留。八个读数如下；仅一个筛选失败不能推出所有上下文失败，上段的有限词反证不可省略。

| $A$ | $\varnothing$ | $a$ | $b$ | $c$ | $ab$ | $ac$ | $bc$ | $abc$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $q(F_BX_A)$ | 0 | 0 | 1 | 1 | 1 | 1 | 2 | 2 |
| $q(F_{S_B}F_{\downarrow Q_B}X_A)$ | 0 | 1 | 1 | 1 | 2 | 2 | 2 | 3 |

#### 相邻阈值的正对照

**正对照：**

$$
B'=(\{t\le0\}\times\{p\})\cup(\{t\le1\}\times\{q\})
$$

满足 $H_{B'}$，所以 $F_{B'}=F_{\{p,q\}}\circ F_{\downarrow Q_{B'}}$ 对全部输入精确实现，保持完整情境。整数严格时间下，不存在既在低阈值之外、又严格早于高阈值之内的中间时刻；这说明差 $1$ 与差 $2$ 的分界来自定义 1 的严格整数时标。

### 34.6 命题 54：q 层一致表达的伴随结果

**命题 54（有下界区域的固定 q 表达，repo-derived）。** 精确量词为

$$
\begin{aligned}
\forall B\subseteq K\ \forall k_0\in\mathbb Z:\quad
&\bigl[(\forall(\tau,p)\in B,\ \tau\ge k_0)\ \Longrightarrow\\
&\quad\forall k\le k_0-1\ \forall X\in\mathcal B:\quad
q(F_BX)=q\bigl(F_{\downarrow Q^*}(X\boxtimes T_k(U_0))\bigr)\bigr],\\
Q^*&=\{(p,\epsilon,r,\tau+1):(\tau,p)\in B,
                 \ \epsilon\in\{\pm1\},\ r\in T\}.
\end{aligned}
\tag{MIX-QEXPR}
$$

$B,k_0,k,Q^*$ 都在 $X$ 之前固定；不要求 $B$ 有限或有上界，也不声称该表达保持历史同构。

**证明。** $T_k(U_0)$ 只选位置 $0$、符号正、时刻 $k$ 的点 $u_+$。乘积的新选中事件恰来自 $(e,u_+)$、$e\in A_X$，位置与符号沿 $e$，时间为 $\max(t(e),k)+1$。该次乘积当前区域为反链，故因果筛选只检查新点自身属性。若 $t(e)\ge k$，新时间为 $t(e)+1$，在这个范围内单射，$Q^*$ 恰检查 $(t(e),x(e))\in B$。若 $t(e)<k$，新时间为 $k+1\le k_0$，不等于任何目标时间 $\tau+1\ge k_0+1$，故被拒；原事件因 $t(e)<k<k_0$ 也不属于 $B$。逐选中事件的有符号有限和相等，空选择及负时刻均包含在内。$k$ 只依赖指定区域的下界，不依赖 $X$ 的最早时刻。证毕。

**坏界反例（不另编号）。** 将条件放宽为 $k\le k_0$ 不成立：取 $B=\{(0,0)\}$、$k=k_0=0$，输入为只选时刻 $-1$ 正点的平衡 $U_{-1}$。目标 $q=0$；乘 $U_0$ 后该点时间成为 $1$，命中 $Q^*$，右式为 $1$。因此原命题的统一界 $k\le k_0-1$ 不能按此方式放宽。

命题 53 判定不可作丰富输出表达的**有下界**区域仍可由本命题作固定 $q$ 表达，例如 D12 的单元区域。**D14 的 $B$ 没有时间下界，不能把它列作命题 54 的适用例。** 它也有固定 $q$ 表达，但由以下单独的直接计算给出：

$$
\begin{aligned}
Q_{14}^*={}&\{(p,\epsilon,r,1):\epsilon\in\{\pm1\},r\in T\}\\
 &\cup\{(q,\epsilon,r,j):\epsilon\in\{\pm1\},r\in T,j\in\{1,2,3\}\},\\
q(F_BX)={}&q\bigl(F_{\downarrow Q_{14}^*}(X\boxtimes U_0)\bigr)
\quad\text{对全部 }X\in\mathcal B.
\end{aligned}
\tag{MIX-D14-Q}
$$

这里 $p,q$ 固定为 D14 的两个位置。乘后时间 $\max(t,0)+1=1$ 当且仅当 $t\le0$；它属于 $\{1,2,3\}$ 当且仅当 $t\le2$。在当前反链上逐选中点检查位置与该时间条件，恰给 D14 两个截面，符号保持，故等式成立。这个具名无下界例的 $q$ 表达已结算，丰富输出不可表达性仍由 D14 保持。

**open：** 时间无下界且不属于命题 53 丰富输出可表达族的区域，其**一般** $q$ 层分类（$\exists$ 固定有限 $C\ \forall X$）仍未测，本节没有给出覆盖这整个剩余类的判据。不能将所有无下界 $B$ 一概记为 open：命题 53 的可表达族已给 $q$ 表达，D14 也已由 (MIX-D14-Q) 单独结算。

### 34.7 本批边界

定义 24 的 $M_P$ 之外的其他配对操作**未测**：命题 52 的推送只处理固定有序父时间—位置单元谓词，没有处理任意来源、身份或因果配对。$\Gamma_t$ 的**全部实际像分类未测**：本批在实际丰富输入及其像上证明闭包和核，没有构造任意形式剖面的历史实现。历史恢复的更强结论由 §28.7／D10 反驳；超出定义 16 的上下文扩张及一般剩余区域的 $q$ 分类按 §34.4、§34.6 保留边界。

附录 `pr5_` 段只作有限精确核验：新更新与事件计算逐字节比较，满足 $H_B$ 的编码式比较完整 `Rich` 状态，D13／D14、坏界和配对背景给定向对照；有限位掩码闭包是配套实验，不能替代引理 3 的任意有限词证明。本批没有新增 Lean 证明，不能称为 kernel-verified；普通 ZFC 推导、有限执行、后续评审与仓库准入是分别记账的事项。

<a id="pr5-evidence"></a>

## 35. PR5 产地与核验收据

### 35.1 产地、先验暴露与亲验范围

本批 skill 上下文为 **`consensus-rnd:sshx`**，阶段为 `implementation`。本实施席按 caller 的“六席收敛契约”在工作树 `/Users/auricstudio/trureturing-csa-upgrade-pr5-0910`、分支 `lane/theory/csa-upgrade-pr5-0910` 工作，并实际读取本机该 skill 的 `SKILL.md`、完整 `CLAUDE.md`、指定卷文与附录。没有将自身检查充作六席思考或三席评审。

**思考产地（以下为 caller brief 转述，未读取各席原始判词）：** 六席为 `teleology`、`parsimony`、`fidelity`、`natural-ownership`、`proportional-containment`、`worth`。`fidelity` 载体为 `nyxid-oracle`，brief 记录模型为 **GPT-6 Astra Pro**；其余五席为 `codex-cli`，各自具体模型标识未提供。caller 记录 codex 席遇到 `dispatch.sh` 的负载门 `idle<20%`，因此直接经 runner 派发到分离只读检出；这就是该次旁路理由，不是本实施席对当时宿主负载的实测。六席均暴露 caller 候选计划，**非盲**；codex 席有仓库先验暴露，oracle 的外部先验不可由本席核定，不能据席数宣称先验独立或环境无记忆。各席逐票结果及原始完成工件未向本席提供，本收据只消费 caller 已给的收敛方案。

**实施与评审分工：** 本批实施由一个 `codex-cli` worker 承担，未另派子工作者；它同样看到候选计划和仓库先验，属于 `repo-prior-exposed`。后续三席 `architecture`／`quality`／`tests` 的评审载体、模型、判词及分歧裁决由 caller **另记**；实施交付时未收到这些结果，不预报通过。brief 将 D14 列作有时间下界的例子与其区域公式冲突，本席在改动前指出该点，保留命题 54 原量词，并以 (MIX-D14-Q) 单独证明及核验 D14 的固定 $q$ 表达；其余主数学边界按收敛契约实施。

**caller 亲验范围（仅转述已提供记录）：** brief 记载 2026-09-10 06:35 对 `origin/dev=95442f6d3d` 核对本卷零改动、无在飞 PR 触碰本卷。此后 caller 对本批证明、附录、ingest、提交或评审的亲验结果未向本席提供；本席不代其声明。**本 worker 亲验范围：** 开工 fetch／试合与 fast-forward、卷文 SHA256、原语及证明前提的原文核对、下列附录执行、canonical ingest、只追加字节检查、编号与最终 git 读数。前者为 caller 自报范围，后者为实施自查，二者不合算为独立评审。

原始基线为 `3759149d0ea0884cb8a57fb950e3caddab007a38`。开工实际执行 `git fetch origin dev && git merge-tree --write-tree origin/dev HEAD`，退出 **0**，试合树为 `1d617412f68464c354f309cab594df6790c8e77e`；随后 `git merge origin/dev` 退出 **0**，fast-forward 到 `95442f6d3d6c3bb970029440d4e3a463aaec1993`，作为本批摄入基线。两版本卷字节相同，3935 行、SHA256 `54894115cd9c214a6ba131fe32ca8a2d0109a4c406733394a9060c6780968b04`，故续接定义 27、引理 3、命题 52–54、D13–D14、增补 N 与 §35，没有 rebase 或重编号。

本批形态为 **ingest**；链上一环是 `source_id=contextual-spacetime-arithmetic` 的新增源文 → 新 `atoms/sha256` 对象 → 同源 `residual-open` backfill。新推导为 `repo-derived`，只依赖卷内既有定义与具名结果，没有新增外部引文；未作全球新颖性检索，不作优先权主张。本批未作 deposit／cover，不报告新增冻结或 absorbed；Lean、一般剩余 $q$ 分类、其他配对及全实际像的未测边界见 §34。

### 35.2 附录实际命令与有限核验范围

本席实际执行以下原文命令，退出 **0**，stderr 为空：

```sh
sed -n '/^```python$/,/^```$/p' docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md | sed '1d;$d' | python3 -
```

附录仅在原末行打印之前插入 **356 行** `pr5_` 段，复用 `Rich`、既有档案运算、`pr3_` 的 timed 筛选／剖面和 `pr4_` 的含时间辅助。stdout 的新增行和末行原文为：

```text
pr5_mixed_closure: region_updates=640 pair_updates=640 endpoints=1280 unselected_parent_pairs=7160 rejected_parent_pairs=5316 empty_products=208 old_endpoint_products=512 negative_time_inputs=61 asymmetric_slots=2 context_steps=13608 context_q=13608 ts_pair_contexts=800 mix_contexts=800 strict_failures=806 rich_equalities=400 H_cases=16384 D13_choices=12 D14_choices=8 bit_maps=52 q_expression=1200 D14_q=80 seed=2026091005 random_samples=64 cases=80 P_empty_Omega=4 P_empty_Gamma=nonempty P_empty_N_positive=2 wrong_deleted_rows=0 D13=0,0,1,1/0,1,1,2 D14=0,0,1,1,1,1,2,2/0,1,1,1,2,2,2,3 bad_k=0,1
ALL_FINITE_CHECKS_PASSED
```

计数由执行累加。固定种子 `2026091005` 生成 64 份平衡状态，当前区域大小取 0、2、4、6，当前时刻取 −8 至 5，另取 0、1、2 个非当前档案点（时刻 −12 或 10），合法生成边取传递闭包，选择可为任意子集；加空档案、空当前区域、未选／非当前目标、D10、抵消、负时刻和 D14 族等定向输入，共 80 份。`unselected_parent_pairs`、`rejected_parent_pairs` 计的是多次配对实验中的父对出现数，非去重事件数。`old_endpoint_products` 计至少一个父档案有非当前端点的乘积实例；端点检查包含完整档案。非对称谓词在左右两槽位单列对照。$P=\varnothing,X=Y=U_0$ 的反例保留四个当前事件与非空 $\Gamma_t$，后接 $N$ 及正号因果筛选得 2，错误删行模型得 0。

上下文词与全部参数在遍历输入之前固定，800 个 $\Sigma_{\rm ts}^{\rm pair}$、800 个 $\Sigma_{\rm mix}$ 实例将 $F_B,M_P$ 与旧原语交替；成功步独立比较逐事件状态的摘要及其 $q$ 和纯摘要更新路径。806 次严格失败含两个时间槽位及后接 $N$、空区域／因果筛选、左右零因子的定向对照，失败未被正常零吸收。

400 次 (MIX-ENCODE) 检查覆盖全区域、空区域、柱集、过去半轴、D14 正对照的相邻阈值，比较完整 `Rich` 的 $(e,o,w,a)$：事件标识与所有属性、全部严格关系、当前区域、选择均规范序列化后逐字节相等。这里没有把“同剖面 + 同 $|E|$”充作历史同构证据，D10 的入射区别仍在完整字段中。D13 三组参数各查四个选择，D14 查全部八个选择；有限位映射闭包共 52 个映射只是配套检查，任意有限上下文的否定由引理 3 和命题 53 承担。

正常形对照枚举两个位置上七个时间块的全部 $2^{14}=16384$ 个区域：$(-\infty,-3]$、五个单点 $-2,-1,0,1,2$、$[3,+\infty)$；两条无限尾各用两个代表时刻检查尾内严格关系。`pr5_H` 的条件矩阵与独立生成的柱集／单顶层正常形一致。该实验仅针对这个固定分块族，不能当作任意 ZFC 集合的可计算判定器。命题 54 的 1200 次 $q$ 比较含无限且无上界的有下界区域、负时刻和三个固定合法 $k$，坏界 $k=k_0$ 得 $(0,1)$；D14 的无下界区域另作 80 次 (MIX-D14-Q) 比较，不混入命题 54 的适用计数。

### 35.3 摄入与追加边界的固定检查点

以下读数固定在追加本收据之前，不用本节自指自己的最终摘要。两次 canonical ingest 均使用下列完整命令，均退出 **0**，stderr 均为空：

```sh
BASE=95442f6d3d6c3bb970029440d4e3a463aaec1993 make ingest SOURCE="contextual-spacetime-arithmetic docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md"
```

首次输入 HEAD 为 `074ea6b6ca60d0013ade8b3efb0e6c1df66be07b`，生成 **30 atoms／30 residual-open**，提交 `31dd372c12077da31ada29983172d103d4bd5053`；stdout 为：

```text
INGEST residual_open_added=30 skipped_existing=268 coarse_fallbacks=0 open_genres=0 cas_objects_written=30 ledger_changed=true
```

该次命令成功后，原文核对发现表格后的命题 52 证明、D14 完整反证及正对照没有全部进入 atoms；退出码不代替内容核对。本席只在新增 §34.2、§34.5 补上明确小标题，分别提交 `5b0cb519e83ada291f777f8b19ccbfb31deccd5e`、`113e4c1d6db2255463c716278dcdd6173c1b7c68`，没有手改、删除或修复已经生成的 CAS 对象或账目。

第二次输入 HEAD 为 `113e4c1d6db2255463c716278dcdd6173c1b7c68`，生成 **12 atoms／12 residual-open**，提交 `bae7159e871dc22a57bddb1ba0a2d65518022d1e`；stdout 为：

```text
INGEST residual_open_added=12 skipped_existing=281 coarse_fallbacks=0 open_genres=0 cas_objects_written=12 ledger_changed=true
```

此检查点累计新增 **42 atoms／42 residual-open**。逐行核对 §34 至当时 EOF 的 **143 行非空、非标题、非锚点内容**，每行正文、公式或表格单元内容都能在至少一个新增 atom 中找到，遗漏 **0**；表格行仅去除末尾 Markdown `|` 后比较，因为实际 row atom 的字节边界止于该分隔符之前。全部 42 个 atom 的内容 SHA256 与文件名相符，且均有同源 residual-open。核验脚本与逐行 atom 索引位于本次 runner 目录的 `audit_source_ingest.py`、`ingest-2-coverage.json`。原始 CAS 切片保留段落末尾空行，通用 `git diff --check` 对此报 `new blank line at EOF`；没有为消除该诊断改写不可变 blob，正文的空白检查另行通过。

在此期间 `origin/dev` 前进至 `d59adb46d4703e7fdc7ef7569c5c0919247cc87a`；本席再次 fetch／试合，退出均为 **0**，试合树 `8720ddcc8312b9852b5485b7e092963aa58635b6`。相对首次合入的 dev，本卷差异仍为空；`git merge --no-edit origin/dev` 以 merge commit `3ee29f1954874e4797ed72bc10271a22e9c4a9e9` 合入，不 rebase，摄入仍使用上列固定基线。

追加本收据前的 HEAD 为 `bae7159e871dc22a57bddb1ba0a2d65518022d1e`，卷文 **4526 行／336985 字节**，SHA256 `850c525569a165d6fc5a6bc5f795204ea6562f45a6893e2133fd18b79f47023c`。去除附录唯一新增的 356 行后，现文的前 **296025 字节**与 3935 行基线全文逐字节相等；当时 §34 尾部新增 235 行，工作树干净。实际 `git diff -U0 origin/dev..HEAD -- docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md` 的 hunk 行为：

```text
@@ -2076,0 +2077,356 @@ print(f"pr4_temporal_causal: random_samples={len(pr4_samples)} cases={len(pr4_ca
@@ -3935,0 +4292,235 @@ INGEST residual_open_added=57 skipped_existing=217 coarse_fallbacks=0 open_genre
```

本 §35 是固定检查点之后的正文追加，须在它最后一次改动之后再执行同一 ingest 命令并提交，使收据本身也进入上述链路。最终摄入的退出码、计数及提交、完整附录重跑的 `pr5_` 行与末行、逐节 commit SHA、最终两个纯插入 hunk、允许路径范围、同步／推送和干净状态，由 `/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/csa-pr5-impl-0910/attempt-1/result.json` 与 `implementation.log` 绑定记录，不用这里的固定 42／42 代替最终累计数。本批交付推送分支，不开 PR；三席评审、后续准入及未测数学边界不由实施收据预先判定。

<a id="pr6-expressibility-pairing"></a>

## 36. PR6 增补 O：q 层一致表达的完整分类、属性级配对与不下降配对

本节接续 §34.6–34.7 的三个问题。以下定义、引理、命题、构造、反例及推论均为 repo-derived，只用卷内定义与已证结果，不作新颖性或优先权声明。载体仍为全部平衡表示 $\mathcal B$；完整乘积、严格增时和单孔上下文分别沿用定义 6、1、16。有限核验不替代任意有限上下文的证明。

### 36.1 定义 28：判定对象、量词与 Tail

**定义 28（单孔 q 表达与公共过去尾，repo-derived）。** 三个范围分别如下。

在 $\Sigma_{\rm mix}$ 中，$\forall B\subseteq K$ 的 q 表达平凡成立：见证就是原语 $C=F_B$（也可用 $M_{B\times K}(\square,U_0)$）；这句话不算 §34.6 的推进。

命题 55 的判定对象只取定义 16 的 $\Sigma_{{\rm cau},t}$ 单孔上下文：

$$
E_q(B)\ \Longleftrightarrow\
\exists\,\text{固定有限 }C\in\operatorname{Ctx}_{\Sigma_{{\rm cau},t}}
\ \forall X\in\mathcal B:\quad
C(X)\text{ 有定义且 }q(C(X))=q(F_BX).
\tag{O-QEXPR}
$$

所有旁参数、谓词、平移量与槽位在 $X$ 之前固定；实际孔恰有一个。允许在有限项中重复同一输入的 $\operatorname{Ctx}^{\rm dup}$（如 $X\boxtimes X$）**不是定义 16 的上下文**，其 q 表达问题另列于 §36.7。

定义

$$
\operatorname{Tail}(B)\ \Longleftrightarrow\
\exists c\in\mathbb Z\ \forall p\in\mathbb Z^3\
\forall t,t'<c:\quad \mathbf1_B(t,p)=\mathbf1_B(t',p).
\tag{O-TAIL}
$$

等价地，存在 $c\in\mathbb Z$、$S^-\subseteq\mathbb Z^3$ 及任意 $B_+\subseteq\{t\ge c\}\times\mathbb Z^3$，使
$B=(\{t<c\}\times S^-)\cup B_+$。等价性由每个位置在 $t<c$ 上取共同真值直接给出；这里必须是一个对全部位置有效的 $c$。

命题 53 的 $H_B$ 分类的是至 $\cong_h$ 的丰富输出表达；本节 Tail 分类的是 q 表达；在 $\Gamma_t$ 上语义下降仅指摘要决定输出摘要，不提供原语言的表达构造。三者各有量词与结论，不能互相替代。

### 36.2 引理 4：总上下文的后继饱和与首乘塌缩

**引理 4（后继饱和与首乘塌缩，repo-derived）。** 对每个在全部 $\mathcal B$ 上有定义的固定有限 $C\in\operatorname{Ctx}_{\Sigma_{{\rm cau},t}}$，存在 $c_C\in\mathbb Z$，使任意 $p\in\mathbb Z^3$ 及 $t,t'<c_C$ 都有下述两输入 $X_t,X_{t'}$：唯一选中事件是同来源正点 $e@(t,p)$、$e@(t',p)$，其余当前事件共同且未选，全部档案端点共同，并且

$$
q(C(X_t))=q(C(X_{t'})).
\tag{O-SATURATION}
$$

量词次序为 $\forall C\ \exists c_C\ \forall p\ \forall t,t'<c_C\ \exists X_t,X_{t'}$；只有最后的输入见证可以依赖 $p,t,t'$。

**证明。** 定义 16 把 $C$ 写成沿唯一孔的一条有限基本步骤链；总定义和严格失败传播保证每个前缀也对全部输入有定义。全部原语保留原输入的每个档案事件，其时刻只累计一个固定整数平移 $J$。若某步为 $\square\triangleright Z$ 且 $E_Z\ne\varnothing$，取原输入含任意晚的档案事件，即击破该步 $M<m_Z$；若为 $Z\triangleright\square$，取任意早的档案事件，击破 $M_Z<m$。这些输入可取空当前区域，因而合法平衡。故总上下文不含这种步骤。空档案参数的时间复合没有跨边，只增加可去的出现标签，对去身份操作及 q 无影响。

还需区分空当前因子。若任何乘积使用固定参数 $\Omega_Z=\varnothing$，该步的当前区域与选择都为空。固定同一原情境而仅变 $A$ 时，所有步骤的情境本来就相同；该步后连选择也相同，后续确定操作永久失去对原选择的依赖。因此当 $B\ne\varnothing$ 时，这种上下文不能表达 $F_B$：在 $B$ 中取一正一负平衡反链，对比空选择与只选正点，目标 q 为 $0,1$。引理本身仍允许空因子，并在下面处理。

现只看首次乘积之前的前缀；若无乘积，就看整个词。去掉空档案时间复合的标签后，这里只剩并行加固定参数、$N,F_S,F_L,F_{\downarrow Q},T_k$。设第 $i$ 个因果谓词为 $Q_i$，该步前原输入累计平移为 $j_i$，在原坐标取 $Q_i^0=\tau_{-j_i}[Q_i]$。对每个非空 $Q_i^0$ 选一个属性 $v_i$，空集不选；谓词个数有限，故只需有限个见证。选整数 $c_C$ 不大于 $0$ 和全部 $v_i$ 的时间。若首乘固定因子 $Z$ 的当前区域非空，再令

$$
c_C+J\le\min t_Z[\Omega_Z],
\tag{O-COLLAPSE-BOUND}
$$

其中 $J$ 是首乘前原输入的累计平移。有限条件有共同整数解；它只由 $C$ 决定，与 $p,t,t'$ 无关。

任给 $p,t,t'$，造同标识的两份有限情境。放唯一选中正点 $e$，来源固定为 $l_0$，只令其时刻分别为 $t,t'$；每个 $v_i$ 放一个未选当前点 $d_i$，属性恰为 $v_i$。只添 $e\prec d_i$，所以关系是已传递的星形；$t,t'<c_C\le t(v_i)$ 保证边严格增时。添共同的孤立未选当前点，时刻取 $0$、符号取所需的正或负，使当前总电荷为零。再添两个共同孤立的非当前档案点，其时刻严格包住两份当前时间，得到相同的有限 $m,M$。所有非 $e$ 事件的属性、标识、选择在两侧相同。

前缀中每个非空 $Q_i$ 对 $e$ 都被对应 $d_i$ 命中，空 $Q_i$ 在两侧都不命中；平移过的见证仍在 $\Omega$，筛选只改选择，不删目标。空间与来源掩码相同，$N$ 同步。其他原输入事件无通向 $e$ 的路径，并行加入的固定分量也没有跨边，所以它们的 $U_t$、掩码与选择不受 $e$ 时刻影响。因此首乘前两侧的选择位、位置、符号、来源逐事件相同，唯一可能不同的当前属性是 $e$ 的时刻。

这也是引理 3 位保持原则的响应形：在同一情境上改变一个输入位时，沿前缀的位差等于原位差乘 $(-1)^\nu\prod_i h_i$；$\nu$ 是取补次数，因果掩码为 $h_i=\mathbf1[U_t(e)\cap Q_i\ne\varnothing]$，空间／来源掩码同样逐位相乘。本构造让两输入对应事件的每个掩码相同，不需要假定其位响应非零。

若无乘积，上述逐事件的同位与同符号立即给终端 q 相同。若有首乘且 $\Omega_Z\ne\varnothing$，(O-COLLAPSE-BOUND) 使每个含 $e$ 的新父对在两侧具有同一时间 $\max(t(e)+J,t_Z(f))+1=t_Z(f)+1$；无论孔在左还是右槽位，全部新当前属性与选择位逐对相同。定义 6 的新当前区域是反链，其 $U_t$ 为自身单点，旧 $U_t(e)$ 从此不进入当前剖面。若 $\Omega_Z=\varnothing$，两侧新剖面直接都为空。

前缀中的并集与平移保持两侧共同的 $m,M$。首乘的新当前时间相同（或两侧都无新点），结合旧档案保留与命题 29 的端点公式，首乘后两侧 $H=(\Gamma_t,m,M)$ 相同。对剩余后缀应用命题 48 的逐基本步保摘要归纳，得到相同终端 q；总定义排除了终端失败。至此覆盖全部总有限单孔上下文及空因子情形。证毕。

### 36.3 命题 55：单孔 q 表达的完整分类

**命题 55（$\Sigma_{{\rm cau},t}$ 单孔 q 表达分类，repo-derived）。**

$$
\forall B\subseteq K:\qquad E_q(B)\ \Longleftrightarrow\ \operatorname{Tail}(B).
\tag{O-CLASSIFICATION}
$$

**证明（充分性）。** 固定 Tail 的 $c$，任取整数 $k\le c-1$，定义

$$
\begin{aligned}
Q_{B,k}&=\{(p,\epsilon,r,n):n\ge k+1,\ (n-1,p)\in B\},\\
C_B(X)&=F_{\downarrow Q_{B,k}}(X\boxtimes T_k(U_0)).
\end{aligned}
\tag{O-CONSTRUCTION}
$$

其中 $\epsilon\in\{\pm1\},r\in T$ 任取。这也等于在 $n=k+1$ 层放全部 $p\in S^-$ 的属性，再放全部 $(p,\epsilon,r,t+1)$、$t\ge k+1,(t,p)\in B$。参数均在输入前固定，表达式是总单孔上下文。

乘积选中的父对恰为 $(e,u_+)$、$e\in A_X$；子点位置与符号沿 $e$，时间为 $\max(t(e),k)+1$。当前区域为反链，因果筛选只检查子点自身。若 $t(e)>k$，检查恰为原单元 $(t(e),x(e))\in B$；若 $t(e)\le k$，检查为 $(k,x(e))\in B$，而 $t(e),k<c$，Tail 使其与原单元同真值。逐选中点作有符号有限和即得 q 等式，包括负点、负时刻及空选择。

**证明（必要性）。** $B=\varnothing$ 时 Tail 成立，且 $F_\varnothing$ 可由空空间筛选实现，单列结束。其余情形取 (O-QEXPR) 的固定总上下文 $C$，应用引理 4。对任意 $p$ 及 $t,t'<c_C$，两输入都只选正点 $e$，故

$$
\mathbf1_B(t,p)=q(F_BX_t)=q(C(X_t))
=q(C(X_{t'}))=q(F_BX_{t'})=\mathbf1_B(t',p).
$$

于是 $c=c_C$ 同时适用于全部位置，得到 Tail。这里没有用有限深度搜索承担任意有限 $C$ 的否定。证毕。

**继承结算。** 命题 54 的时间有下界族恰是 Tail 正常形中 $S^-=\varnothing$ 的族；命题 53 的全部丰富可表达族也满足 Tail。D14 可取 $c=1,k=0,S^-=\{p,q\}$，仍无时间下界；其 q 表达成为本命题推论，而丰富输出不可表达性原样成立。§34.6 的一般单孔 q 分类 **由命题 55 结算**。Tail 对有限交封闭（取各阈值的最小值），故 $B\cap D$ 可按 (O-CONSTRUCTION) 重造上下文；不能把单纯 q 等式代入任意后续复合来证明这条结论。

**H-A 的反例族（推论例，不占 D 编号）。** “$\Sigma_{{\rm cau},t}$ 中所有 $B$ 都 q 可表达”为假。对 $d\ge2$、$\varnothing\ne R\subsetneq\mathbb Z/d\mathbb Z$，
$B_{d,R}=\{(t,p):t\bmod d\in R\}$ 在每条过去尾仍有两种真值，故不满足 Tail；空间限制的例子 $B_{\rm even}=\{(t,0):t\text{ 偶}\}$ 同样不可表达。给定任意 $c$，可在 $c$ 以下选择属于和不属于 $R$ 的时刻，这提供每个阈值的反证。

另取

$$
B_{\rm drift}=\bigcup_{n\ge0}\bigl(\{t\le-n\}\times\{(n,0,0)\}\bigr).
\tag{O-DRIFT}
$$

每位置分别最终恒定，但无公共 $c$：给定 $c$，取 $n\ge0$ 使 $-n+1<c$，在位置 $(n,0,0)$ 比较 $-n,-n+1$，真值为 $1,0$。其时间无下界、有上界 $0$。这反驳把 $\exists c\,\forall p$ 弱化为 $\forall p\,\exists c_p$；有限核验中的塌缩读数只作对照，否定由上述任意阈值论证和命题 55 承担。

### 36.4 定义 29 与命题 56：属性级配对的保守扩签名

**定义 29（属性级配对，repo-derived）。** 对固定 $P\subseteq\mathrm{Attr}_t\times\mathrm{Attr}_t$，令 $\widehat M_P(X,Y)$ 使用定义 6 的完整乘积情境，只选满足 $e\in A_X,f\in A_Y$ 且 $(\alpha_t(e),\alpha_t(f))\in P$ 的父对。定义
$\Sigma_{\rm mix}^{\rm attr}=\Sigma_{\rm mix}\cup\{\widehat M_P:P\subseteq\mathrm{Attr}_t^2\}$。旧 $M_P$ 的参数类型仍是 $K\times K$，不改定义 24。

**命题 56（属性配对闭包与观察核，repo-derived）。** 新操作总定义，逐父格的推送为

$$
((a,b,U),(a',b',U'))\longmapsto
(a\diamond_t a',\,bb'\mathbf1_P(a,a'),\,\{a\diamond_t a'\}),
\tag{O-ATTR-PAIR}
$$

推送系数为两父格系数之积，碰撞时相加；端点为
$(\min(m_X,m_Y),\max(M_X,M_Y,\gamma(s_X,s_Y)))$，$s$ 由 $\Gamma_t$ 支撑恢复。并且

$$
\approx_{\Sigma_{\rm mix}^{\rm attr}}=\ker(\Gamma_t,m,M).
\tag{O-ATTR-KERNEL}
$$

**证明。** 限制选择不改完整乘积的平衡或合法性，故操作总定义。固定两个父格，属性和位均固定，谓词真值固定；全部该格父对的符号和为两格系数之积，**系数已经含符号，不再乘 $\epsilon\epsilon'$**。父未选或 $P$ 假的对也生成当前事件，只进入 $b=0$ 行；不删 $\Omega$，不给系数或背景乘掩码。新事件无出边，所以 $U$ 是自身属性单点。旧档案保留，完整端点沿命题 29 更新。

把 (O-ATTR-PAIR) 补入命题 48／52 的基本步表。对 $\widehat M_P(\square,Z)$ 与 $\widehat M_P(Z,\square)$ 分别按有序父格推送同一固定参数，均保摘要；$P$ 不对称也不交换槽位。对全部有限混合上下文归纳：恒等孔保摘要，基本步骤成功则输出同摘要，时间守卫由共同端点决定而同真值，内层失败则严格传播。终端 q 由选中行求和恢复，得到 $\ker(\Gamma_t,m,M)\subseteq\approx_{\Sigma_{\rm mix}^{\rm attr}}$。反向由 $\Sigma_{\rm mix}\subseteq\Sigma_{\rm mix}^{\rm attr}$ 与命题 52（亦可用命题 49 的子语言）给出。证毕。

**拉回与连接。** 令 $\kappa(p,\epsilon,r,n)=(n,p)$。对旧类型 $P\subseteq K^2$ 取
$P^\uparrow=\{(a,a'):(\kappa(a),\kappa(a'))\in P\}$，则 $\widehat M_{P^\uparrow}=M_P$ 是完整编码等式。#6684 的 $\Xi$ 核仍属于 $\Sigma_{\rm ts}^{\rm pair}$（及其子语言 $\Sigma_{\rm ts}$），不是本扩签名的核。

在 $\Sigma_{\rm mix}^{\rm attr}$ 乃至 $\Sigma_{\rm mix}$ 中，令配对谓词查左父单元属于 $B$，右乘固定 $U_0$，便对任意 $B$ 得到 q 表达。**观察核不变，不等于固定表达资源相同。** 这正是命题 55 与命题 56 应保留的区别。§34.7 关于属性级配对闭包的未测项 **由命题 56 结算**；任意规则的下降边界如下。

### 36.5 纤维下降判据、定义 30 与反例 D15

对完整乘积上的任意选择规则 $R=R^{X,Y}$，固定输出属性 $c\in\mathrm{Attr}_t$，定义

$$
J_R^{X,Y}(c)=
\sum_{\substack{e\in A_X,\ f\in A_Y\\
\alpha_t(e)\diamond_t\alpha_t(f)=c}}
\sigma(e)\sigma(f)\mathbf1_R(e,f).
\tag{O-FIBER-COUNT}
$$

这里的规则可依赖整个输入，输出仍只限制所选父对。记 $\widehat W_{X\boxtimes Y}(c)$ 为按**完整属性**分组的当前背景符号和；它由两父 $\Gamma_t$ 的全部行卷积决定，不与定义 22 按 $K$ 分组的 $W$ 混型。输出 $\Gamma_t$ 在 $(c,1,\{c\})$ 行为 $J_R(c)$，在 $(c,0,\{c\})$ 行为 $\widehat W(c)-J_R(c)$，其余行零。

所以有精确语义 iff：该规则在 $\Gamma_t$ 上下降，当且仅当逐 $c$ 的 $J_R$ 在两输入 $\Gamma_t$ 的共同纤维上恒定；即任意 $\Gamma_t(X)=\Gamma_t(X')$、$\Gamma_t(Y)=\Gamma_t(Y')$ 都有 $J_R^{X,Y}(c)=J_R^{X',Y'}(c)$。对 $(\Gamma_t,m,M)$ 下降则换成该摘要的纤维，端点已由完整乘积更新。必要性读选中行，充分性用上述两行重建。这是 repo-derived 的纤维判据，不承诺判定任意规则的算法。

只比较 $\sum_cJ_R(c)$ 是严格较弱的 q 层条件。例如，若存在符号积为正的所选父对，就恰选一个：按先时间、后固定属性编码的全序，在左输入严格关系对数为奇数时取最小输出属性，偶数时取最大输出属性，同属性内再按固定出现编码选一个；无正号所选父对则选空。q 恒为“有正号所选父对”的指示值，由两父 $\Gamma_t$ 决定；但将下述 D15 两图分别与 $U_0$ 配对，关系对数为 $1,2$，被选子点时刻为 $1,2$，故同纤维上的 $J_R$ 不同。

**自身属性谓词只是充分条件。** 规则 $R(e,f)\Longleftrightarrow U_t^X(e)\cap Q\ne\varnothing$ 等于 $F_{\downarrow Q}(X)\boxtimes Y$ 的选择；$R(e,f)\Longleftrightarrow |U_t^X(e)|>1$ 也可按父格直接推送。这两者依赖 $U$，仍下降。全局规则 $R(e,f)\Longleftrightarrow |\Omega_X|/2$ 为奇数也下降，因为 $|\Omega_X|=\sum|\Gamma_t(X)|$，但不是固定局部父格谓词：$U_0$ 与 $U_0\boxplus U_0$ 有相同的父格类型，准入真值却相反。候选中只问 $|\Omega_X|$ 奇偶的版本在平衡载体上恒偶，不能充作这个反例。

**定义 30（同档案因果配对，repo-derived）。** 定义总一元新操作

$$
D_\prec(X)=X\boxtimes_{R_X}X,\qquad
R_X=\{(e,f)\in\Omega_X^2:e\prec_X f\}.
\tag{O-CAUSAL-PAIR}
$$

乘积仍完整，只选 $e,f\in A_X$ 且 $e\prec_Xf$ 的父对。这是**新原语的定义式**，不是定义 16 内的单孔上下文。若把二元 $M_\prec$ 解读为两份带标签旧档案之间的关系，则定义 6 根本没有这样的跨档案路径，选择恒空且下降；欲问别的跨档案因果谓词，必须另定其类型与关系来源。

**反例 D15（同纤维上因果父对数不同，repo-derived）。** 取 $E=\Omega=\{e,b_1,b_2,n_1,n_2,n_3\}$，位置全零、来源全 $l_0$。$e@0,b_1@1,b_2@1$ 为选中正点，三个 $n_i@0$ 为孤立未选负点。$X$ 的关系只有 $e\prec b_1$；$Y$ 的关系为 $e\prec b_1,e\prec b_2$。两图均已传递且严格增时。写 $a_0=(0,+1,l_0,0)$、$a_1=(0,+1,l_0,1)$、$n_0=(0,-1,l_0,0)$，共同非零剖面恰为

$$
(a_0,1,\{a_0,a_1\})\mapsto1,\quad
(a_1,1,\{a_1\})\mapsto2,\quad
(n_0,0,\{n_0\})\mapsto-3.
$$

两侧 $m=0,M=1$，但 $q(D_\prec X)=1$、$q(D_\prec Y)=2$；两个贡献的输出属性同为 $a_0\diamond_t a_1$，所以 (O-FIBER-COUNT) 在同一摘要纤维也不恒定。$D_\prec$ 不在 $\Gamma_t$ 或 $(\Gamma_t,m,M)$ 上下降。

新增边没有增添任何可达属性，因为插边前已有 $U_t(b_2)=\{a_1\}\subseteq U_t(e)$，且无其它非平凡路径；这不重犯 §28.5 D7／P3 的闭包泄漏。$\Gamma_t$ 记录每格事件数，但 $U_t$ 去重，忘掉的是同属性目标的入射重数。D10 原两图的 $D_\prec$ 读数均为 $2$，不能把原图原样充作 D15。

### 36.6 命题 57 与 D16：完整实际像

**命题 57（$\Gamma_t$ 及档案端点的完整实际像，repo-derived）。** 给定有限支撑整数剖面 $g$，格类型为 $(a,b,U)\in\mathrm{Attr}_t\times\{0,1\}\times\mathcal P_{\rm fin}(\mathrm{Attr}_t)$，以及定义 22 类型的 $m,M$。三元组 $(g,m,M)$ 是某 $X\in\mathcal B$ 的 $(\Gamma_t(X),m_X,M_X)$，当且仅当：

1. 每个非零格满足 $\epsilon(a)g(a,b,U)>0$，即同格符号一致。
2. $\sum_{a,b,U}g(a,b,U)=0$，即当前区域平衡。
3. 每个非零格有 $a\in U$，且 $U\setminus\{a\}$ 中每个属性的时刻严格晚于 $a$。
4. **后继见证：** 每个非零格 $(a,b,U)$ 及每个 $v\in U\setminus\{a\}$，都有非零格 $(v,b',V')$ 满足 $V'\subseteq U$。
5. $g\ne0$ 时，$m,M$ 为有限整数且包住全部非零格自身属性的时刻；$g=0$ 时，端点可为空档案的 $(+\infty,-\infty)$，或非空档案的任意有限整数 $m\le M$。

**证明（必要性）。** 同格符号由自身属性固定，系数为该符号乘事件数，得①，且 $g=0$ 当且仅当 $\Omega=\varnothing$。平衡给②；引理 2 给③。若 $v\in U_t(e)\setminus\{\alpha_t(e)\}$，存在当前 $d$ 使 $e\prec d$ 且 $\alpha_t(d)=v$。传递性给 $U_t(d)\subseteq U_t(e)$，$d$ 所属格非零，得④。档案有限且包含当前区域，给⑤。

**证明（充分性与显式构造）。** 对每个非零格制造 $|g(a,b,U)|$ 个不同的当前事件副本，自身属性、选择位照抄，给每个副本指定目标集 $U_e=U$。在这些事件上定义

$$
e\prec f\ \Longleftrightarrow\
t(a_e)<t(a_f)\ \land\ U_f\subseteq U_e.
\tag{O-REALIZATION}
$$

严格增时保证反自反，时间不等式及集合包含的传递性保证关系传递。由③，$a_e\in U_e$；若 $e\prec f$，则 $a_f\in U_f\subseteq U_e$，故无额外可达属性。对每个 $v\in U_e\setminus\{a_e\}$，④提供一个有副本的格 $(v,b',V')$，③使 $t(v)>t(a_e)$，于是该副本可达。故实际 $U_t(e)$ 恰为指定 $U_e$。①使逐格有符号计数恰为 $g$，②给平衡。

初取 $E=\Omega$；按⑤需要时补时刻 $m,M$ 的孤立非当前档案事件，即实现两端点而不改剖面。$g=0$ 时直接取空当前区域，按⑤取空档案或一／两个孤立档案点。全部构造是有限集合，适用定义 1 的编码。证毕。

投影到第一坐标即给 $\Gamma_t$ 的全部实际像：满足①–④的 $g$ 总可选⑤的端点。构造的是**一个**实现，不承诺与产生该剖面的原输入历史同构，D10 的非唯一性保持。“当前区域是反链”只对刚生成的乘积输出成立，对应全部 $U=\{a\}$ 的子类；它**不是一般必要条件**，D10 即为反证，不在①–⑤之中。§34.7 的全实际像未测项由命题 57 结算。

**反例 D16（缺少后继见证的形式剖面，repo-derived）。** 同位置零、同来源 $l_0$，取正属性 $a@0,b@1$ 和负属性 $c@2$，仅令

$$
g(a,1,\{a,b\})=1,\qquad
g(b,1,\{b,c\})=1,\qquad
g(c,0,\{c\})=-2,\qquad (m,M)=(0,2).
$$

①②③⑤均通过，但 $a$ 行的目标 $b$ 只有后继集 $\{b,c\}\nsubseteq\{a,b\}$ 的格，④失败。任何实现中 $a$ 到达一个 $b$，该 $b$ 又到达 $c$，传递性迫使 $c\in U_t(a)$，与所写 $U$ 矛盾。故仅有符号、平衡、唯一最早与端点条件不足。

### 36.7 边界与 OPEN-COPY

**OPEN-COPY。** 令 $\operatorname{Ctx}^{\rm dup}_{\Sigma_{{\rm cau},t}}$ 为使用同一原签名、固定参数、有限项及严格失败传播，但允许重复输入的项语言。精确问题为

$$
E_q^{\rm dup}(B)\ \Longleftrightarrow\
\exists\,\text{固定总项 }C\in\operatorname{Ctx}^{\rm dup}_{\Sigma_{{\rm cau},t}}
\ \forall X\in\mathcal B:\quad q(C(X))=q(F_BX).
$$

已证 $\operatorname{Tail}(B)\Rightarrow E_q^{\rm dup}(B)$，因为 (O-CONSTRUCTION) 的单孔项属于该扩张；反向以及 $\forall B\subseteq K:E_q^{\rm dup}(B)$ 均未证，记 open。引理 4 的首乘固定旁参数条件不适用于 $X\boxtimes X$，不得移贴单孔必要性。

候选思路（worth 席，经 caller 转述；不作定理）：把输入并行复制 $n$ 份使 $\Gamma_t\mapsto n\Gamma_t$，尝试从目标 q 关于 $n$ 的一次多项式取一次部分，化为有限个单孔读数之差再用引理 4；此归约须独立核验，本批未证。

命题 55 的域不含输入自适应参数、无限项或身份扩签名；命题 57 只给存在性，不给唯一性。D15 划出了新原语超出摘要的具体边界，没有把所有依赖关系的规则一概判为不下降。本批仅为普通 ZFC 推导和有限核验，不新增 Lean、axiom、判官或 schema。

<a id="pr6-evidence"></a>

## 37. PR6 产地与核验收据

### 37.1 产地、先验暴露与分工

本批 skill 上下文为 consensus-rnd:sshx，阶段为 implementation。实施载体是一个 codex-cli worker（自报 GPT-6／Codex），按 caller 的六席收敛 brief 与 GoalArtifact 修订 R1-PR6 在分支 lane/theory/csa-upgrade-pr6-0910 实施；本席实际读取本机该 skill 的 SKILL.md、完整 CLAUDE.md 及指定卷文、附录，未另派子席，属于 repo-prior-exposed。

**思考产地（caller brief 转述，未读取原始判词）：** 六席为 teleology、parsimony、fidelity、natural-ownership、proportional-containment、worth。teleology 使用 nyxid-oracle、company-chatgpt-pro 池，自报 GPT-6 Astra Pro；其余五席使用 codex-cli，自报 GPT-6／Codex，经仓内 dispatch.sh 负载门派发，其中四席曾在门内排队至他人负载回落。六席均为 revise，由 meta-judge 收敛至 R1-PR6。排队与模型身份是该次席位／caller 自报，不是本实施席对当时宿主的测量。

各席均暴露 caller 候选计划，**非盲**；候选曾把 $\Sigma_{\rm mix}$、$\Sigma_{{\rm cau},t}$ 与复制孔三个范围混写，席位纠正后由 R1 分开。codex 有仓库先验暴露，oracle 的外部先验不受本席控制，不凭席数宣称先验独立。后续 architecture／quality／tests 三评审席的载体、模型、判词与分歧裁决由 caller **另记**；实施时未收到，不预报通过。

**caller 亲验范围（仅转述 brief）：** 2026-09-10 07:58 核对 dev 上本卷零改动，基线本卷 4602 行、§1–§35。此后对本批的亲验与评审记录未提供。**本 worker 亲验范围：** 原文前提、开工及交付前 fetch／merge-tree、附录执行、ingest 与正文覆盖、追加字节及 git 读数；均为实施自查，不充作独立评审。

开工基线为 462d0a4368ba5a890c5eab619c82437baa88966f，fetch 后 origin/dev 仍为该 SHA；merge-tree 退出 0，试合树 c02b4787ce9ff0cf96d03db1357874add67bc2b7。本卷未有并行尾追加，故续接定义 28–30、引理 4、命题 55–57、D15–D16、增补 O，不 rebase。§36 的 242 行提交为 b7fabcc68cde0c366365d239403079529b923a9f；附录初稿提交为 684487f7be64b35e05cc62f8154cd9f541f81fa3，周期饱和对照补充至 6479fb1da62726408424fb68aae2fc6a94ef41ae。

**brief 更正：** 平衡使 $|\Omega_X|$ 恒偶，原“按其奇偶准入”的非局部例退化；改用 $|\Omega_X|/2$ 奇偶，保留所需的全局而可下降例。命题 57 显式先判三元组 $(g,m,M)$，再投影给 $\Gamma_t$ 的像；属性背景用 $\widehat W(c)$ 区分定义 22 的 $W(n,p)$；$B_{\rm even}$ 是周期族的空间限制例。以上均保持 R1 的结论范围，不改旧结算。

本批形态为 **ingest**；链上一环是 source_id=contextual-spacetime-arithmetic 的新源文 → 新 atoms/sha256 对象 → 同源 residual-open。新推导均 repo-derived，无新外部引用；未作全球新颖性检索，不作优先权主张。不作 deposit／cover，不报告冻结或 absorbed。OPEN-COPY 及任意扩张的边界见 §36.7。

### 37.2 附录实际核验

本席实际运行下列原文命令，退出 **0**，stderr 为空，末行如下。新增 pr6_ 段共 **289 行**，只插在唯一 Python 块原末行打印之前；复用 Rich、pr3_／pr4_／pr5_ 的运算、剖面与规范字节函数。
```sh
sed -n '/^```python$/,/^```$/p' docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md | sed '1d;$d' | python3 -
```
```text
pr6_expressibility_pairing: tail_q=4320 collapse_controls=4 target_controls=4 collapsed_profiles=4 saturation_endpoints=108 saturation_q=108 saturation_no_product=36 saturation_empty_factor=36 saturation_product=36 periodic_saturation=1 unsaturated_control=1 first_product_fiber=1 pair_push=800 empty_products=260 old_archives=640 negative_inputs=690 unselected_parents=8950 pair_suffix=2400 pullback_encoding=320 mixed_summary=3600 mixed_q=3600 strict_failures=720 D15_fiber=1 D15_q=1 D10_control=1 U_rule_push=6 J_positive=6 J_fiber=3 U_size_rule=4 global_rule=4 same_local_rows=1 q_only_control=1 image_roundtrip=64 enumerated_states=1280 formal_membership=1088 enumerated_roundtrip=704 image_sets=2 distinct_actual_profiles=670 D16_conditions=1 empty_endpoint_branches=6 empty_realizations=3 seed=2026091006 Tail_families=27 random_inputs=64 cases=80 periodic_and_drift=1,1/1,0 D15=1,2 D10=2,2 D16=1,1,1,0,1
ALL_FINITE_CHECKS_PASSED
```

固定种子 2026091006 生成 24 个 Tail 谓词，连同 D14、空集、全集共 27 个，两个合法 k 遍历既有 64 份随机及 16 份定向输入。36 个随机小上下文分为无乘积、空因子、非空因子三组，各遍历三个位置；另以周期谓词对照有后继的 1/1 与删边后的 1/0，验证饱和见证的作用。属性配对核对两个槽位、非对称及符号／来源谓词、未选父、空区域、旧档案、负时刻、N／筛选续接与严格失败；P↑ 比较完整编码。J_R 的 U 依赖、全局计数与 q-only 对照分别核验。

实际像核验包含 64 份直接生成的合法形式剖面往返；四事件族固定时间 (0,1,2,3) 与 (0,0,1,1)、符号 ++--、同位置同来源，穷举 1280 个图／选择组合和 1088 份形式候选，接受集与实际像逐个一致，去重实际剖面共 670 份。D16 逐项读数为 1,1,1,0,1；空档案与非空档案空当前区域端点分支另查。有限域计数不承担任意上下文或任意形式剖面的全称证明。预算原为计划而非机器门：正文 242 行在计划内，附录 289 行超过约 150 行的估量，用于保留要求的双路径计算、饱和负对照和完整枚举。

### 37.3 ingest 检查点与最终工件

首次摄入以 684487f7be64b35e05cc62f8154cd9f541f81fa3 为已提交输入，实际命令如下，退出 **0**、stderr 为空。
```sh
BASE=462d0a4368ba5a890c5eab619c82437baa88966f make ingest SOURCE="contextual-spacetime-arithmetic docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md"
```
```text
INGEST residual_open_added=33 skipped_existing=289 coarse_fallbacks=0 open_genres=0 cas_objects_written=33 ledger_changed=true
```

该次新增 33 atoms／33 residual-open，提交 c91664f4f9f1476e3d54a9877431171da959f36c；逐行核对 §36 的 149 行非空、非标题、非锚点内容，遗漏 0。这是本收据与周期对照补充之前的固定检查点，不能充作最终摄入。首次覆盖结果存于本次 runner 的 ingest-1-coverage.json。

本 §37 最后一次改动之后再以同一命令 ingest 并提交；最终计数、全部逐节提交、两个纯插入 hunk、旧文零字节改动、允许路径、干净状态与 push 由 /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/csa-pr6-impl-0910/attempt-1/result.json 绑定记录，原始执行证据另存同目录。本批交付推送分支，不开 PR；评审、CI、合入和持续研究目标的完成不由实施收据预先判定。
<a id="p2-cumulative"></a>

## 38. P2/R3：累积表示与延迟校正结合式

§25 已把默认档案乘法的两个电荷分量写成 $\mathcal L$ 上的 $\odot$。本节给出这一剖面运算的累积表示，下一节据此完整求解固定因子的剖面方程。沿用定义 22–23 的 $\mathcal L=\mathbb Z^{(\mathbb Z\times\mathbb Z^3)}$、整数时间、共同空间参考点 $0$ 及默认时间规则 $\max+1$；空间系数始终属于 §15、§19 的原卷积环 $R=\mathbb Z^{(\mathbb Z^3)}$，乘法仍为 $*$。以下字母 $d$ 表示剖面因子；空间维数固定为 $3$。对任意预先固定的有限空间维数 $m\ge1$，同样的有限和证明仍适用。

### 34.1 有限时间序列与两尾条件

**定义 31（剖面的累积表示）。** 对 $c\in\mathcal L$，令 $c_n\in R$ 为 $c_n(p)=c(n,p)$，并记有限时间支撑

$$
T(c)=\{n\in\mathbb Z:c_n\ne0\}.
$$

这样把 $c$ 识别为 $R$ 中的有限支撑时间序列 $(c_n)_{n\in\mathbb Z}$：只有有限多个时间分量非零，每个分量又只有有限空间支撑。反向，任何这样的时间序列也给出 $\mathcal L$ 的元素，因为有限多个有限空间支撑对应的时间—空间单元之并仍有限。

定义累积算子及其目标类型为

$$
(Pc)(n)=C_n=\sum_{t\le n}c_t,
\qquad
\mathcal A(R)=
\left\{C:\mathbb Z\to R:
\begin{array}{l}
\exists\,\ell,u\in\mathbb Z\ \exists\,B\in R,\\
n<\ell\Longrightarrow C_n=0,\quad
n\ge u\Longrightarrow C_n=B
\end{array}
\right\}.
\tag{CUM-TYPE}
$$

两处蕴含均对所有 $n\in\mathbb Z$ 量化。左尾必须为零，右尾必须最终为同一常值；右尾的 $B$ 可以非零。因此 $\mathcal A(R)$ 不是有限支撑累积序列的集合，也不是全部 $R$ 值序列的集合。此处 $P$ 的类型是累积算子，区别于 §15 的空间读数像集合以及定义 24 的配对谓词。

**命题 58（加法双射与差分逆）。** 逐时间相加使 $\mathcal A(R)$ 成为阿贝尔群，且

$$
P:\mathcal L\longrightarrow\mathcal A(R)
\quad\text{是加法双射},\qquad
(P^{-1}C)_n=C_n-C_{n-1}\quad(n\in\mathbb Z).
\tag{CUM-INVERSE}
$$

**证明。** 对有限支撑 $c$，在最早非零时间以前 $C_n=0$，在最后非零时间以后 $C_n=\sum_t c_t\in R$；$c=0$ 时两个尾部都恒为零。因此 $Pc\in\mathcal A(R)$。对两个累积序列，取其左阈值的较小者、右阈值的较大者，便得到和的两个尾部；取负同样保持两尾条件。所以逐时间的加法、零和负号确实给出所述阿贝尔群。有限和还直接给 $P(c+d)=Pc+Pd$。

反向，给定 $C\in\mathcal A(R)$，可把左阈值减小、右阈值增大而取 $\ell\le u$。置 $c_n=C_n-C_{n-1}$。当 $n<\ell$ 时相邻两项都为零；当 $n>u$ 时相邻两项都为 $B$。所以只有有限区间 $[\ell,u]\cap\mathbb Z$ 中的分量可能非零。每个差分都属于 $R$，且

$$
\operatorname{supp}(c)\subseteq
\bigcup_{n\in[\ell,u]\cap\mathbb Z}
\{n\}\times
\bigl(\operatorname{supp}(C_n)\cup\operatorname{supp}(C_{n-1})\bigr).
$$

右边是有限多个有限集合之并，故确有 $c\in\mathcal L$，而不只是逐时间形式上可作差。对 $n\ge\ell$ 作有限望远镜求和，

$$
\sum_{t=\ell}^{n}(C_t-C_{t-1})=C_n-C_{\ell-1}=C_n;
$$

对 $n<\ell$ 两边均为零。因此 $P(P^{-1}C)=C$。另一方面，$Pc(n)-Pc(n-1)=c_n$，故 $P^{-1}(Pc)=c$。这同时证明双射、差分逆及单射性。证毕。

由差分逆，累积序列的跳变位置恰为 $T(c)$，右尾常值为 $\sum_t c_t$。这给出 R3 的有限跳点表示：只需记录有限次跳变及最终常值，左尾按定义为零，无须实际存储整个无限累积序列。它是有限剖面的精确表示，并未放宽两个尾部条件。

### 34.2 默认延迟乘法的累积与差分公式

**命题 59（延迟一格的乘法公式）。** 对任意 $c,d\in\mathcal L$，写 $C=Pc,D=Pd$，则对所有 $n\in\mathbb Z$，

$$
P(c\odot d)(n)=C_{n-1}*D_{n-1}.
\tag{CUM-DELAY}
$$

相应输出时间分量的两种差分表达式为

$$
\begin{aligned}
(c\odot d)_n
&=C_{n-1}*D_{n-1}-C_{n-2}*D_{n-2}\\
&=c_{n-1}*D_{n-1}+C_{n-2}*d_{n-1}.
\end{aligned}
\tag{CUM-DIFFERENCE}
$$

**证明。** 累积输出时间不超过 $n$ 的全部项。由 (TS-PRODUCT)，两个父时间满足的条件恰为

$$
\max(a,b)+1\le n
\quad\Longleftrightarrow\quad
a\le n-1\ \text{且}\ b\le n-1.
$$

因此在 $R$ 中有有限双和等式

$$
\begin{aligned}
P(c\odot d)(n)
&=\sum_{\substack{a,b\in\mathbb Z\\\max(a,b)+1\le n}}c_a*d_b\\
&=\sum_{a\le n-1}\sum_{b\le n-1}c_a*d_b\\
&=\left(\sum_{a\le n-1}c_a\right)*
  \left(\sum_{b\le n-1}d_b\right)
=C_{n-1}*D_{n-1}.
\end{aligned}
$$

这里非零项只来自 $T(c)\times T(d)$；每一空间卷积也只涉及有限支撑，故所有重排都是有限和重排。对 (CUM-DELAY) 在相邻输出时间 $n,n-1$ 作差，得到 (CUM-DIFFERENCE) 第一式。再加减 $C_{n-2}*D_{n-1}$，并用 $C_{n-1}-C_{n-2}=c_{n-1}$ 与 $D_{n-1}-D_{n-2}=d_{n-1}$，得到第二式。两个下标 $n-1,n-2$ 都来自默认输出延迟，不能改为无延迟的下标。证毕。

### 34.3 无延迟辅助乘法及两个扭曲恒等式

**定义 32（辅助乘法与平移）。** 定义 $\diamond:\mathcal L^2\to\mathcal L$ 为

$$
(c\diamond d)(n,r)=
\sum_{\substack{(a,p)\in\operatorname{supp}(c),\ (b,q)\in\operatorname{supp}(d)\\
\max(a,b)=n,\ p+q=r}}
c(a,p)d(b,q),
\qquad
\alpha=\tau_1,\quad
(\alpha c)(n,p)=c(n-1,p).
\tag{CUM-AUX}
$$

辅助乘积的支撑包含于父支撑对的有限像，所以仍属 $\mathcal L$。$\diamond$ 只用于分析剖面代数，不替换默认 $\odot$，也不替换丰富乘法 $\boxtimes$；它的无延迟时间规则不作为定义 6 的新事件规则。

本节的 $\diamond:\mathcal L^2\to\mathcal L$ 是无延迟剖面乘法，区别于 §28.2 的属性乘积 $\mathrm{Attr}^2\to\mathrm{Attr}$；本节 $\alpha=\tau_1$ 是剖面平移自同构，也区别于定义 25 的事件属性映射 $\alpha(e)$。下述交换与结合结论只指本节明确类型的剖面乘法。

**命题 60（辅助结合律、平移自同构及延迟校正式）。** $\diamond$ 交换、结合并对整数双线性，$\alpha$ 是 $(\mathcal L,+,\diamond)$ 的自同构，且

$$
c\odot d=\alpha(c\diamond d).
\tag{CUM-TWIST}
$$

对全部 $c,d,e\in\mathcal L$，默认剖面乘法还满足两个分别成立的恒等式

$$
(c\odot d)\odot\alpha(e)=\alpha(c)\odot(d\odot e),
\tag{CUM-HOM}
$$

$$
\alpha(c\odot d)=\alpha(c)\odot\alpha(d).
\tag{CUM-MULTIPLICATIVE}
$$

**证明（辅助代数）。** 交换两个父支撑点保持 $\max(a,b)$ 和 $p+q$，整数系数相乘也交换，故 $\diamond$ 交换。对任意输出 $(n,r)$，展开两个括号的有限和，均得到

$$
\sum_{\substack{\max(a,b,t)=n\\p+q+s=r}}
c(a,p)d(b,q)e(t,s).
$$

此和限制在三个输入有限支撑的笛卡尔积上。时间等式
$\max(\max(a,b),t)=\max(a,\max(b,t))$、空间加法结合及整数乘法结合，使两种分组逐项对应，故 $\diamond$ 结合。把任一因子的和或整数倍代入有限和，逐项用整数分配律，得到两个变量的整数线性。

$\alpha$ 保加法且有逆 $\tau_{-1}$。共同平移两个父时间时，

$$
\max(a+1,b+1)=\max(a,b)+1,
$$

位置与系数不动，有限和重索引便给
$\alpha(c\diamond d)=\alpha(c)\diamond\alpha(d)$。所以它确为自同构。将辅助乘积的输出时间再加一，正好把条件 $\max(a,b)=n$ 变为 (TS-PRODUCT) 的默认条件，得到 (CUM-TWIST)。

**证明（累积核对与单射）。** 由定义及有限和直接有

$$
P(c\diamond d)(n)=C_nD_n=C_n*D_n,
\qquad
P(\alpha c)(n)=C_{n-1}.
\tag{CUM-AUX-TRANSFORM}
$$

此显示式中的并置乘法 $C_nD_n$ 明确指原空间卷积 $*$，不是对空间位置逐点相乘。第一式使用 $\max(a,b)\le n$ 等价于 $a,b\le n$；第二式把平移后的求和时间减一。

记 $E=Pe$。用命题 59 两次，(CUM-HOM) 两边经 $P$ 后在每个整数 $n$ 分别为

$$
\begin{aligned}
P\bigl((c\odot d)\odot\alpha(e)\bigr)(n)
&=(C_{n-2}*D_{n-2})*E_{n-2},\\
P\bigl(\alpha(c)\odot(d\odot e)\bigr)(n)
&=C_{n-2}*(D_{n-2}*E_{n-2}).
\end{aligned}
$$

原空间卷积的结合律使它们相等；命题 58 的单射性把累积等式带回剖面等式。最后独立核对乘法保持式：

$$
\begin{aligned}
P\bigl(\alpha(c\odot d)\bigr)(n)
&=P(c\odot d)(n-1)=C_{n-2}*D_{n-2},\\
P\bigl(\alpha(c)\odot\alpha(d)\bigr)(n)
&=P(\alpha c)(n-1)*P(\alpha d)(n-1)
=C_{n-2}*D_{n-2}.
\end{aligned}
$$

再次由 $P$ 单射得到 (CUM-MULTIPLICATIVE)。这个第二恒等式有自己的核对，不从“Hom-associative”一词推出。全部论证发生在整数模块和原空间卷积中，没有借用域上的除法或假设全域单位。证毕。

### 34.4 普通结合律与完整档案的边界

**反例 E1（默认乘法的普通括号仍有区别）。** 取
$c=d=\delta_{(0,0)}$、$e=\delta_{(1,0)}$。由默认时间规则，

$$
(c\odot d)\odot e=\delta_{(2,0)},
\qquad
c\odot(d\odot e)=\delta_{(3,0)}.
$$

左边先在时间 $1$ 生成，再与时间 $1$ 合成至 $2$；右边先将 $0,1$ 合成至 $2$，再与 $0$ 合成至 $3$。这是命题 31 的非结合见证及命题 33 的树深度公式在剖面上的同一边界，不作为另一项独立发现。(CUM-HOM) 校正了所写平移，未把 $\odot$ 变为普通结合的环乘法。

**反例 E2（剖面恒等式不能提升到完整 $\Xi$）。** 沿用命题 30 的 $U_t$：两个当前事件均在空间零点、时间 $t$，一正一负，只选正事件，$E=\Omega$ 且偏序为空。令 $X=U_0,Y=U_2,Z=U_4$，比较

$$
X_L=(X\boxtimes Y)\boxtimes T_1Z,
\qquad
X_R=T_1X\boxtimes(Y\boxtimes Z).
$$

左侧中间当前事件在时间 $3$，$T_1Z=U_5$，故最后当前事件都在 $6$；完整档案出现的时刻集合为 $\{0,2,3,5,6\}$。右侧 $T_1X=U_1$，中间 $Y\boxtimes Z$ 的当前事件在 $5$，最后也全在 $6$；完整档案时刻集合为 $\{1,2,4,5,6\}$。每个输入的当前剖面为零、所选剖面为一份单点质量；按命题 39，最终两侧均有 $W=0$、所选剖面 $\delta_{(6,0)}$、$M=s=6$，但

$$
\Xi(X_L)=(0,\delta_{(6,0)},0,6,6),
\qquad
\Xi(X_R)=(0,\delta_{(6,0)},1,6,6).
$$

档案最小时刻分别为 $0,1$。所以剖面上的延迟校正结合式不能提升为完整 $\Xi$ 恒等式，更不能据此断言丰富表示或完整档案相等。所选数据与完整档案数据的区别在这里仍有实际可见的后果。

<a id="p2-fixed-factor"></a>

## 39. P2/R4：固定因子剖面方程的核、像与可恢复域

### 35.1 全部解的类型与两个尾部的构造

**定义 33（固定因子映射及支撑下界）。** 对每个固定的 $d\in\mathcal L$，定义整数线性映射

$$
L_d:\mathcal L\to\mathcal L,\qquad L_d(c)=c\odot d.
$$

线性来自 (TS-PRODUCT) 的有限和对 $c$ 的整数线性，也可由命题 60 的 (CUM-TWIST) 得到。写 $D=Pd$，对输入 $c$、目标 $h\in\mathcal L$ 分别写 $C=Pc,H=Ph$。对所有 $n\in\mathbb Z$，主理想及支撑受限子群定义为

$$
D_nR=\{D_n*r:r\in R\}\subseteq R,\qquad
\mathcal L_{\ge a}=\{c\in\mathcal L:\forall n<a,\ c_n=0\}
\quad(a\in\mathbb Z).
\tag{CUM-FACTOR-TYPE}
$$

主理想使用原空间卷积；$D_n=0$ 时 $D_nR=\{0\}$。$\mathcal L_{\ge a}$ 对剖面加法与负号封闭。这里不在时间乘法 $\odot$ 上假设整环性质。

**命题 61（固定因子的完整核、像与全部解）。** 对任意固定 $d\in\mathcal L$，有

$$
\ker L_d=
\{c\in\mathcal L:\forall n\in\mathbb Z,\quad
D_n\ne0\Longrightarrow C_n=0\}.
\tag{CUM-KERNEL}
$$

对任意目标 $h\in\mathcal L$，其像条件恰为

$$
h\in\operatorname{im}L_d
\quad\Longleftrightarrow\quad
\forall n\in\mathbb Z,\
\begin{cases}
H_{n+1}=0,&D_n=0,\\
H_{n+1}\in D_nR,&D_n\ne0.
\end{cases}
\tag{CUM-IMAGE}
$$

当此条件成立时，全部解由下列累积序列恰好给出：在 $D_n\ne0$ 的每个位置，$C_n$ 是空间方程 $D_n*C_n=H_{n+1}$ 在 $R$ 中的唯一解；在 $D_n=0$ 的位置，可以自由取 $C_n\in R$，但这些自由值与其余值合成的整个序列必须属于 $\mathcal A(R)$。对所有满足这项两尾限制的选择，取

$$
c_n=C_n-C_{n-1}\qquad(n\in\mathbb Z)
\tag{CUM-ALL-SOLUTIONS}
$$

便得到全部且仅有的解。若 (CUM-IMAGE) 不成立则无解。特别地，$d=0$ 时 $\ker L_0=\mathcal L$、$\operatorname{im}L_0=\{0\}$；目标为零时每个 $c\in\mathcal L$ 都是解，目标非零时无解。

**证明（核、必要性及非零处唯一性）。** 命题 59 在输出时间 $n+1$ 给

$$
P(L_d(c))(n+1)=C_n*D_n=D_n*C_n
\qquad(n\in\mathbb Z).
\tag{CUM-EQUATION}
$$

这里等号的交换使用原空间卷积。由命题 58 的单射性，$L_d(c)=h$ 等价于所有这些值等于 $H_{n+1}$；输出下标必须是 $n+1$。

命题 26 已证明原 $R$ 无零因子。因此 $D_n\ne0$ 时，$D_n*C_n=0$ 当且仅当 $C_n=0$；$D_n=0$ 时乘积恒为零，不限制该处 $C_n$。这给出 (CUM-KERNEL)。一般目标下，在 $D_n=0$ 处必须有 $H_{n+1}=0$；在 $D_n\ne0$ 处必须有 $H_{n+1}\in D_nR$，故像条件必要。若 $D_n\ne0$ 且有两个商 $r_1,r_2\in R$，则 $D_n*(r_1-r_2)=0$，命题 26 使 $r_1=r_2$；这正是命题 32 的空间方程唯一性。所用消去律只属于 $R$，没有移植到 $\odot$。

**证明（像条件充分，明确构造左右尾部）。** 假设 (CUM-IMAGE)。因 $D,H\in\mathcal A(R)$，可取整数 $\ell<u$，使

$$
D_n=H_{n+1}=0\quad(n<\ell),\qquad
D_n=D_\infty,\ H_{n+1}=H_\infty\quad(n\ge u)
$$

其中 $D_\infty,H_\infty\in R$ 为固定常值。在整个左尾 $n<\ell$ 令 $C_n=0$，于是逐点方程成立。

对于右尾，若 $D_\infty\ne0$，像条件给出 $H_\infty\in D_\infty R$，故存在唯一 $Q_\infty\in R$ 使 $D_\infty*Q_\infty=H_\infty$。对全部 $n\ge u$ 取同一个 $C_n=Q_\infty$；因为因子与目标在右尾都恒定，唯一性保证所需商不随 $n$ 变化。若 $D_\infty=0$，像条件迫使 $H_\infty=0$，就在整个右尾令 $C_n=0$。两种右尾都已满足方程及最终常值条件。

剩余只有 $\ell\le n<u$ 的有限多个整数。在其中 $D_n\ne0$ 处取像条件给出的唯一 $R$ 中商，在 $D_n=0$ 处取 $C_n=0$。如此构造的 $C$ 左尾为零、右尾为常值，每个中间值都属于 $R$，所以 $C\in\mathcal A(R)$。命题 58 的有限支撑证明保证其差分是 $\mathcal L$ 中的 $c$。逐点方程对全部整数都成立，(CUM-EQUATION) 及 $P$ 单射给出 $L_d(c)=h$。这里实际只处理两个常值尾部和有限中段，没有对无限多个不受约束的商作选择，也没有把 $R$ 嵌入某个域后作未说明的除法。

**证明（全部解与 $d=0$ 情形）。** 任一实际解的累积序列必属于 $\mathcal A(R)$，并满足 (CUM-EQUATION) 的每个空间方程。因此非零 $D_n$ 处的值被唯一强制，零 $D_n$ 处只有 $R$ 类型及整个序列的两尾条件；反向任何满足这些要求的序列由命题 58 和同一逐点方程给出解。除 $\mathcal A(R)$ 的条件外，没有遗漏其他时间一致性约束。

若 $d=0$，则 $D_n=0$ 对所有整数成立，像条件要求 $H_{n+1}=0$ 对所有整数成立，即 $H=0$；由 $P$ 单射这恰为 $h=0$。此时全部 $\mathcal A(R)$ 都可作解的累积序列，差分逆给全部 $\mathcal L$。核与像的特殊结论随之成立。证毕。

### 35.2 全称像条件的有限段化

**命题 62（共同跳点与两个常值尾段）。** 对给定 $d,h\in\mathcal L$，(CUM-IMAGE) 只需在 $D_n$ 与 $H_{n+1}$ 的共同常值段上各检查一次，包括左右两个常值尾段。它们的跳点包含于有限集合

$$
J=T(d)\cup(T(h)-1),\qquad
T(h)-1=\{t-1:t\in T(h)\}.
\tag{CUM-JUMPS}
$$

因此像条件归结为有限多个空间主理想成员条件，零主理想的成员条件就是目标为零。

**证明。** 相邻差分恰为

$$
D_n-D_{n-1}=d_n,\qquad
H_{n+1}-H_n=h_{n+1}.
$$

所以离开 $J$ 时，两项均无跳变。若 $J=\{j_1<\cdots<j_k\}$ 非空，则它们同时常值的分段可取

$$
n<j_1,\qquad
j_i\le n<j_{i+1}\ (1\le i<k),\qquad
n\ge j_k.
$$

每段中因子、目标及主理想都不变，故该段任一整数上的条件等价于整段条件。第一段是共同的零左尾，最后一段是共同的常值右尾，两段都纳入检查。若 $J=\varnothing$，则 $T(d)=T(h)=\varnothing$，两个剖面均为零，全部整数是一段，两个尾部也同为零。用 $D_nR=\{0\}$ 统一零分支，就得到有限多个 $H_{n+1}\in D_nR$ 条件。证毕。

有限段化只消除了在时间轴上重复同一条件的需要。它不声称空间主理想成员问题有某个复杂度界，也不提供或宣称已经实现通用除法算法；所用空间条件仍是命题 32 的有限支撑解存在条件。

### 35.3 支撑下界上的精确单射域与全域失败

**命题 63（受限单射的充要条件及每个固定因子的全域失败）。** 对任意 $a\in\mathbb Z$、$d\in\mathcal L$，

$$
L_d|_{\mathcal L_{\ge a}}\text{ 单射}
\quad\Longleftrightarrow\quad
\forall n\ge a,\ D_n\ne0.
\tag{CUM-INJECTIVE}
$$

特别地，当 $d=\delta_{(a,0)}$ 时，

$$
c\odot\delta_{(a,0)}=\tau_1c
\qquad(c\in\mathcal L_{\ge a}).
\tag{CUM-SHIFT-FACTOR}
$$

然而对每个 $d\in\mathcal L$，$L_d$ 在整个 $\mathcal L$ 上都不单射，即使 $\varepsilon d=1$ 也不能保证全域单射。

**证明（受限单射的两方向）。** $\mathcal L_{\ge a}$ 是加法子群，故其上的整数线性映射单射等价于受限核只有零元。若所有 $n\ge a$ 的 $D_n$ 都非零，对受限核元，命题 61 迫使 $C_n=0$ 在 $n\ge a$ 成立；输入在 $a$ 以前没有分量，又使 $C_n=0$ 在 $n<a$ 成立。所以 $C=0$，由 $P$ 单射得 $c=0$。

反向，若某个 $n\ge a$ 满足 $D_n=0$，取

$$
c=\delta_{(n,0)}-\delta_{(n+1,0)}\ne0.
$$

它属于 $\mathcal L_{\ge a}$，累积序列满足 $C_n=\delta_0$，而对全部 $j\ne n$ 有 $C_j=0$。因此只有这个单一位置的累积值非零，且恰在 $D_n=0$ 处，(CUM-KERNEL) 给出 $L_d(c)=0$。这提供一个非零受限核元，证明必要性，也覆盖 $d=0$ 时受限单射必失败的情形。

对于单点因子 $d=\delta_{(a,0)}$，有 $D_n=0$ 在 $n<a$，$D_n=\delta_0\ne0$ 在 $n\ge a$，故满足所述单射条件。直接在 (TS-PRODUCT) 中看每个输入时间 $t\ge a$，有 $\max(t,a)+1=t+1$，空间位置加零，系数不变；有限求和得到 (CUM-SHIFT-FACTOR)。它在指定域上实现的是 $\tau_1$，不是恒等映射，不能称为单位；对于早于 $a$ 的输入，多个不同时间还会被合并到 $a+1$，故不作全域平移声明。

**证明（每个固定因子都全域不单射）。** 若 $d=0$，$L_d$ 恒为零，而 $\mathcal L$ 含非零单点质量，故不单射。若 $d\ne0$，有限非空 $T(d)$ 有最早时间 $b=\min T(d)$。取

$$
c=\delta_{(b-1,0)}-\delta_{(b,0)}\ne0.
$$

它的累积剖面仅在 $b-1$ 为 $\delta_0$，而 $D_{b-1}=0$；命题 61 再给 $c\odot d=0$。于是 $L_d(c)=L_d(0)$ 且 $c\ne0$，完成全称结论。证毕。

**反例 E3（增广为一仍不能消去时间因子）。** 具体取

$$
c=\delta_{(0,0)}-\delta_{(1,0)},\qquad
d=\delta_{(2,0)}.
$$

两个因子均非零且 $\varepsilon d=1$；两个输入贡献分别经
$\max(0,2)+1=3$ 与 $\max(1,2)+1=3$ 到达同一输出单元，符号相反，所以

$$
c\odot d=\delta_{(3,0)}-\delta_{(3,0)}=0.
$$

这明确排除了把 §19 的空间无零因子定理移植到时间剖面乘法的强断言。命题 63 给出的可恢复性必须连同支撑下界及每个 $D_n\ne0$ 的条件使用。

<a id="p2-sources-boundaries"></a>

## 40. P2 的主数学来源、成熟框架与后续边界

### 36.1 已完成的主推理与既有结果复用

本次 P2/R3–R4 的核心定义、命题、公开证明及所列边界反例来自已完成的 **GPT PRO** 主推理任务 **8a1e6a18-47e3-4d7e-b703-a33b93c4ef87**，模型 **GPT-6 Astra**，模式 **mode:chat**，完成时间 **2026-09-09T15:46:54.998+00:00**，对话为 [GPT PRO：CSA 新扩展主推理](https://chatgpt.com/c/6aa175d8-7ae0-83ec-9289-e9fc818fe147)。该主数学来源依据的稿件 pin 为 **74e9341e5e38615754f82e99430a257a21c5a26c**。它是数学来源的定位，不是本次包含 P1 的后来工程基线；首次追加的工程基线绑定为 **f2b448dacf2d8eb3581520f115f2d2619cd6af48**。

本次重整以 `d59adb46d4703e7fdc7ef7569c5c0919247cc87a` 的 dev 文稿为固定工程基线，保留该基线全文，将首次 P2 的全部数学材料移至本文末尾：§27–29 改为 §38–36，定义 25–27 改为定义 31–29，命题 42–47 改为命题 58–57，并作本节与 §38.3 的类型及批次说明。此次机械重整由 Codex 实施；旧数学来源归属不变，旧候选的评审与核验收据不自动代表重整后候选已经通过评审或交付。

Codex 实施席依这一已完成来源组织中文数学表述、适配连续编号并独立核对，未把核心数学归为 Codex 的新独立推导，也不兼任本次实施的独立评审席。R3 是成熟累积变换与代数扭曲框架在 CSA 有限整数剖面上的特化；R4 是该主推理给出的完整固定因子方程及可恢复域。两者作为本稿扩展归类为 repo-derived，不据此主张全球优先权。

具体复用关系是：有限空间卷积、其结合交换及分配律沿用 §15；整性和非零空间因子的唯一性沿用命题 26、28；默认整数时间和树深度边界沿用命题 32–33；联合剖面类型、平移、默认乘积及丰富档案端点沿用定义 22–23、命题 39。命题 58–57 的公开证明承担双向无限整数时间链、两尾像条件、输出延迟及固定因子方程的特定结论，不以引用或有限样本代替这些证明。

### 36.2 成熟文献的具体前提

累积表示与 join 乘法的成熟背景见 Andreas Björklund、Thore Husfeldt、Petteri Kaski、Mikko Koivisto、Jesper Nederlof、Pekka Parviainen，*Fast Zeta Transforms for Lattices with Few Irreducibles*，Proceedings of the Twenty-Third Annual ACM-SIAM Symposium on Discrete Algorithms（SODA 2012），pp. 1436–1444，DOI [10.1137/1.9781611973099.113](https://doi.org/10.1137/1.9781611973099.113)，[作者公开的会议论文 PDF](https://thorehusfeldt.com/wp-content/uploads/2010/08/7c52e3293a74298f.pdf)。本次采用的已核读引文资料对应这份会议版本的 PDF 第 1–2 页：其前提是**有限格**与**系数域 $K$**，式 (1.1) 定义 $\zeta$ 变换，式 (1.2) 给出 Möbius 逆，式 (1.3) 明确通过变换后的逐点乘法表达 join 乘法，正文称 $\zeta$ 为代数同构。这里“逐点”是在变换后的格索引上。该来源并未直接陈述本稿的无限整数时间链、整数空间卷积系数、零左尾与最终常值右尾，亦未包含默认输出延迟；这些由命题 58–53 及 (CUM-AUX-TRANSFORM) 的有限和证明单独承担。上述页码不指向另行出版的 2015 年期刊版本。

代数自同态扭曲的成熟背景见 Donald Yau，*Hom-algebras and homology*，[arXiv:0712.3515v3](https://arxiv.org/abs/0712.3515v3)，2009 年 8 月 6 日修订，[版本 PDF](https://arxiv.org/pdf/0712.3515v3)；arXiv 所列期刊出处为 *Journal of Lie Theory* 19（2009），409–421。已核读资料对应该版本：§2.1（PDF 第 2 页）固定特征零域；§2.3（第 3 页）的式 (2.3.2) 为 $(xy)\alpha(z)=\alpha(x)(yz)$，并明确一般 Hom-associative 定义本身不要求 $\alpha$ 保乘法。定理 2.4（第 3–4 页）、引理 2.5 及推论 2.6(1)（第 4 页）说明自同态扭曲 $\mu_\alpha=\alpha\circ\mu$ 的机制，并另行建立乘法保持式；定理的前提是自同态，不要求可逆。

本稿的对应是 $\mu=\diamond$、$\alpha=\tau_1$、$\mu_\alpha=\odot$。$\tau_1$ 在当前整数剖面类型上确实可逆并保持 $\diamond$，由命题 60 自给证明；这一识别不是 Yau 文中直接陈述的 CSA 结论。尤其不能把文献的域上线性代数前提静默扩张到整数模块，也不能只援引 Hom-associativity 的名称来省掉 (CUM-MULTIPLICATIVE) 的证明。引文资料只说明来源可访问性、定位及假设，不充当本稿数学证明或正式评审结论。

### 36.3 剖面方程与完整逆问题的区分

命题 61 的目标严格是 $c\odot d=h$ 的**剖面方程**。即使分别解出 $W$ 与 $Z$ 两个分量的方程，也不能据此断言一个预先指定的完整 $\Xi$ 逆问题有解：输入背景仍须平衡，两个分量必须共同满足命题 37 的实际像与支撑范围条件，所指定的档案端点还必须满足命题 39 的更新式。分别存在剖面解，并未证明这些解能够同时满足同一丰富输入的支撑与端点约束。反例 E2 也说明剖面等式本身不保存完整档案摘要。

这种带同时实际像条件及端点约束的逆问题仍是单独的后续主研究任务。本批 P2 不引入后续 P3/R5–R9 的依赖结构与严格联合响应或 JT 的新结果；这里的 P3 是后续研究批次，区别于前文已保留的 PR3/PR4 来源与因果章节。既有 $\mathbb Z/\mathbb Q/\mathbb R$ 接口、丰富默认操作、共同零参考点、背景与端点限制，以及所选数据和完整档案的区别继续有效。本节的普通数学证明与有限例子核对不构成 Lean 内核验证、物理或量子定律、PR 已交付或持续研究总目标完成的声明。

<a id="p2-numbering-source-ingestion-erratum"></a>

## 41. P2 编号、来源与摄入归属勘误

本勘误针对合入提交 `8b56117af1004e219191f56c010e78957060c9c7` 的 P2：[§38 累积表示](#p2-cumulative)、[§39 固定因子方程](#p2-fixed-factor) 与 [§40 来源及边界](#p2-sources-boundaries)。只校正定位、版本归属及摄入声明的范围；原数学陈述、证明和旧 CAS/YAML 作为历史来源保留，不重复全文，也不把其他批次的同号条目视为 P2。

### 41.1 三个定义与六个命题的跨稿编号

P2 初稿 `70463e7669a120e9fb180fadfb78bbe46ea6eaa1` 为 §§27–29，中间重整稿 `2859ad9afbd338c898739081463e7020818c9eb5` 为 §§34–36，合入稿为 §§38–40。以下每条依次列出初稿、中间稿、合入稿编号；公式标签辨认同一内容。

剖面的累积表示：定义 25 → 定义 27 → 定义 31；合入稿 §38，`CUM-TYPE`。

辅助乘法与平移：定义 26 → 定义 28 → 定义 32；合入稿 §38，`CUM-AUX`。

固定因子映射及支撑下界：定义 27 → 定义 29 → 定义 33；合入稿 §39，`CUM-FACTOR-TYPE`。

加法双射与差分逆：命题 42 → 命题 52 → 命题 58；合入稿 §38，`CUM-INVERSE`。

延迟一格的乘法公式：命题 43 → 命题 53 → 命题 59；合入稿 §38，`CUM-DELAY`、`CUM-DIFFERENCE`。

辅助结合律、平移自同构及延迟校正式：命题 44 → 命题 54 → 命题 60；合入稿 §38，`CUM-TWIST`、`CUM-HOM`、`CUM-MULTIPLICATIVE`。

固定因子的完整核、像与全部解：命题 45 → 命题 55 → 命题 61；合入稿 §39，`CUM-KERNEL`、`CUM-IMAGE`、`CUM-ALL-SOLUTIONS`。

共同跳点与两个常值尾段：命题 46 → 命题 56 → 命题 62；合入稿 §39，`CUM-JUMPS`。

受限单射的充要条件及每个固定因子的全域失败：命题 47 → 命题 57 → 命题 63；合入稿 §39，`CUM-INJECTIVE`、`CUM-SHIFT-FACTOR`。

### 41.2 十个子标题的局部定位

合入稿三个主标题已改号，以下 P2 子标题仍印有中间稿章号。仅在各自父章内按下列定位解读；既有 PR5/PR6 的 §§34–36 不受影响。

§38 内“34.1 有限时间序列与两尾条件”读作 §38.1。

§38 内“34.2 默认延迟乘法的累积与差分公式”读作 §38.2。

§38 内“34.3 无延迟辅助乘法及两个扭曲恒等式”读作 §38.3。

§38 内“34.4 普通结合律与完整档案的边界”读作 §38.4。

§39 内“35.1 全部解的类型与两个尾部的构造”读作 §39.1。

§39 内“35.2 全称像条件的有限段化”读作 §39.2。

§39 内“35.3 支撑下界上的精确单射域与全域失败”读作 §39.3。

§40 内“36.1 已完成的主推理与既有结果复用”读作 §40.1。

§40 内“36.2 成熟文献的具体前提”读作 §40.2。

§40 内“36.3 剖面方程与完整逆问题的区分”读作 §40.3。

### 41.3 七处句内错引及其范围

以下逐处限定所在语句，不构成全局替换规则；§40.1、§40.2 采用 §41.2 的准确定位。

§39 命题 61 的“核、必要性及非零处唯一性”证明中，“这正是命题 32 的空间方程唯一性”应读为 §19 命题 28“空间方程的准确条件”中的非零因子解唯一性。

§39 命题 62 后的有限段化说明中，“所用空间条件仍是命题 32 的有限支撑解存在条件”应读为 §19 命题 28 的主理想成员与有限支撑解存在条件。这两处在初稿、中间稿均指命题 28。

§40.1 重整说明中的“§27–29 改为 §38–36”应读为初稿 §§27–29 对应合入稿 §§38–40。

§40.1 同一重整句中的“定义 25–27 改为定义 31–29”应读为初稿定义 25–27 对应合入稿定义 31–33。

§40.1 同一重整句中的“命题 42–47 改为命题 58–57”应读为初稿命题 42–47 对应合入稿命题 58–63。

§40.1 具体复用段落中的“命题 58–57 的公开证明”应读为 P2 命题 58–63 的公开证明。

§40.2 第一段中的“这些由命题 58–53 及 (CUM-AUX-TRANSFORM) 的有限和证明单独承担”应读为命题 58–59 及命题 60 证明中的 `CUM-AUX-TRANSFORM`；初稿对应命题 42–43，中间稿对应命题 52–53。

§40.1 中“默认整数时间和树深度边界”的命题 32–33 引用仍正确，分别指 §21“最早整数与全部交换重标”和“完整二叉构造树的根时刻”；同段命题 26、28 仍指 §19 的空间整性与空间方程。定义 24 的配对谓词（§25.3）和定义 25 的事件属性映射（§28）也不按 P2 偏移量改号。

### 41.4 最终工程来源与摄入归属

§40.1 所记工程基线 `d59adb46d4703e7fdc7ef7569c5c0919247cc87a` 是中间稿 `2859ad9` 的实际父提交。最终 P2 的父提交为 `82938786158c163b50350c14c948e63df61107a8`，候选 head 为 `b900744153382dc6e7f67a7f8f4bc1cd0d15ed1b`，合入提交为 `8b56117af1004e219191f56c010e78957060c9c7`；中间稿基线不能充作最终候选基线。主数学来源仍为 §40.1 的 GPT PRO 任务 `8a1e6a18-47e3-4d7e-b703-a33b93c4ef87`，数学源稿 pin 仍为 `74e9341e5e38615754f82e99430a257a21c5a26c`，本次编辑勘误不重新归属数学推导。

在上述最终父提交至候选 head 的差分中，新增 34 个 CAS 与 34 个 `residual-open` YAML，该 source 的 YAML 数由 547 增至 581（不含 `source.toml`）。这 34 对的路径和字节均同于中间稿 `2859ad9` 的工件：34 个 CAS 全文均可在中间稿 P2 中定位，只有 7 个仍逐字匹配合入稿 P2，另 27 个因改号或改引而不同。这是版本文本差异，不是 27 个独立数学定理。

在合入稿 `8b56117` 的 581 个账目所引用的 CAS 中，以“编号与完整名称”检索，本节所列定义 31–33、命题 58–63 九项均无命中。因此旧 34/34 CAS/账目对只证明中间编号原料已入账，不能证明最终改号正文已全部摄入。当前完整 `contextual-spacetime-arithmetic` 源及本勘误的摄入状态，以 canonical `make ingest` 的新收据和对应新增 CAS/YAML 判定；旧 CAS/YAML 保留其历史原料身份，不改内容地址，也不改释为其他批次的同号结果。摄入仅记录参考文本，不构成新的数学证明、Lean 内核验证或持续研究总目标完成的声明。

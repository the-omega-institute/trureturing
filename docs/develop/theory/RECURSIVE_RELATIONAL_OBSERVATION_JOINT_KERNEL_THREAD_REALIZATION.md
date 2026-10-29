# Recursive relational observation: realization of typed joint-kernel threads

本卷是统一联合律桥（UJLB）的窄补充。目标是说明：有限深度的联合核商何时
下降为一个相容塔，何时给出真正的全局边界，以及为什么逆极限中的形式线程仍
可能不是任何实际来源或观察者可读状态。全文只讨论声明的经典关系模型，不把
完成化解释成物理时空，也不把有限 law 表当作观察者免费拥有的资料。

## 1. 类型化商塔与两个边界

固定一个带类型的来源

$$
Z=\bigsqcup_{\tau\in I}Z_\tau .
$$

沿用 [UJLB §1.2](RECURSIVE_RELATIONAL_OBSERVATION_UNIFIED_JOINT_LAW_BRIDGE.md)
的定义：$K_0=\ker o$ 是同一合同的当前读出核，读出包含接口类型；$K_{n+1}$
保留 $K_n$，并按同类型动作的合法性及事件—记录—终端—$K_n$ 后继的完整联合
law 细化。$K_n$ 是 (UJB.7303) 迭代所得的闭合有限深度联合细化，不是任意指定
的嵌套关系。声明测试族 $\mathscr T$ 对有限前缀及合法自适应串接闭合。于是
每个 $K_n$ 保持类型，并满足

$$
K_{n+1}\subseteq K_n\qquad(n\ge 0).
$$

UJLB 的递归 $K_n$ 在每个类型 $Z_\tau$ 上都是等价关系：基步是读出相等；
归纳步使用标签相等和已为等价关系的后继 $K_n$（随机合同比较该后继商上的
完整联合 law 的相等），并保留 $K_n$，故自反、对称和传递性逐步保留。
因此以下商 $Q_n$ 合法。

令

$$
Q_n=Z/K_n,
\qquad
q_n:Z\longrightarrow Q_n,\quad q_n(z)=[z]_{K_n},
\qquad
p_n:Q_{n+1}\longrightarrow Q_n,
\qquad
p_n([z]_{K_{n+1}})=[z]_{K_n}.
$$

写 $Q_{n,\tau}=Z_\tau/(K_n|_{Z_\tau})$，所有层间投影均保持接口类型。
保持类型使 $p_n$ 的定义域和值域具有相同的接口标签；嵌套性使它良定义。定义
相容线程空间

$$
L=\varprojlim Q_n
=\{(x_n)_{n\ge0}:p_n(x_{n+1})=x_n\ \forall n\},
$$

以及规范映射

$$
\eta:Z\longrightarrow L,
\qquad
\eta(z)=([z]_{K_0},[z]_{K_1},\ldots).
$$

写

$$
K_\infty=\bigcap_{n\ge0}K_n,
\qquad B=\eta[Z]\subseteq L.
$$

则 $\eta(z)=\eta(u)$ 当且仅当 $z\,K_\infty\,u$。因此存在规范双射

$$
Z/K_\infty\ \cong\ B,
\qquad [z]_{K_\infty}\longmapsto\eta(z).
$$

这里的 $B$ 是实际来源像，而 $L$ 是数学完成。有限阶段联合分离条件为

$$
\bigl(\forall n,\ z\,K_n\,u\bigr)\Longrightarrow z=u;
$$

它等价于 $\eta$ 的单射性。相容线程全都可实现的条件为

$$
\forall x\in L\ \exists z\in Z,\quad \eta(z)=x;
$$

它等价于 $B=L$。所以来源与完成之间的双射必须同时要求分离和线程实现性；
只有一个条件时，只能得到单射或满射的一半。这正是
`InverseLimitCompletion.lean` 中 `stateThread_injective_iff_separates` 与
`stateThread_bijective_iff_complete_and_separates` 所抽象的分裂；
`CompletionIsomorphismCriterion.lean` 给出相同的唯一实现表述，
`LocalGlobalAtlasExactness.lean` 则把核对角与满线程像的两个条件分开。

## 2. 有限联合核下降的精确合同

给定带类型动作 $a:\tau\to\upsilon$。动作的合法域 $D_a\subseteq Z_\tau$、
拒绝原因、成功后继、事件、记录和终止都属于同一个合同。以下使用把非法尝试
也写成显式拒绝分支的总合同，保留其终端和记录，不把未定义行当成合法行。
固定带接口类型标签的终端集 $F_a$，与来源状态不交。总合同定义如下；随后定义
扩展后继投影

$$
J_a^{\mathrm{tot}}(z;\cdot)
 \in \operatorname{Prob}\!\bigl(E_a\times(Z_\upsilon\sqcup F_a)\times R_a\bigr),
 \qquad
\sum_{e,\bar z,r}J_a^{\mathrm{tot}}(z;e,\bar z,r)=1
 \quad(z\in Z_\tau).
$$

在 $D_a$ 上，$J_a^{\mathrm{tot}}(z;\cdot)$ 等于 UJLB 的 $J_a(z;\cdot)$；在
$Z_\tau\setminus D_a$ 上，合同预先声明拒绝事件
$e_a^{\mathrm{rej}}(z)\in E_a$、带类型的拒绝终端
$f_a^{\mathrm{rej}}(z)\in F_a$ 及拒绝记录 $r_a^{\mathrm{rej}}(z)$，并令

$$
J_a^{\mathrm{tot}}(z;\cdot)
 =\delta_{\bigl(e_a^{\mathrm{rej}}(z),\,f_a^{\mathrm{rej}}(z),\,r_a^{\mathrm{rej}}(z)\bigr)}.
$$

因此 (JKT.1)--(JKT.4) 中的原始核统一指 $J_a^{\mathrm{tot}}$；所有非法输入、
拒绝质量和终端质量均由这个总行定义。

$$
q^\sharp_{a,n}:Z_\upsilon\sqcup F_a\longrightarrow Q_{n,\upsilon}\sqcup F_a,
\qquad
q^\sharp_{a,n}(z')=[z']_{K_n},\quad q^\sharp_{a,n}(f)=f.
$$

对有限或可数来源，移位下降的合同是：对每个 $n\ge0$、同类型的
$z,u\in Z_\tau$，若 $z\,K_{n+1}\,u$（即属于同一 $Q_{n+1}$ 输入类），则

$$
\mathbf 1_{D_a}(z)=\mathbf 1_{D_a}(u),
$$

并且对每个事件 $e\in E_a$、记录 $r\in R_a$ 及
$y\in Q_{n,\upsilon}\sqcup F_a$，有完整联合等式

$$
\sum_{\bar z:\,q^\sharp_{a,n}(\bar z)=y}
 J_a^{\mathrm{tot}}(z;e,\bar z,r)
=
\sum_{\bar u:\,q^\sharp_{a,n}(\bar u)=y}
 J_a^{\mathrm{tot}}(u;e,\bar u,r).
\tag{JKT.1}
$$

求和只合并成功后继的 $K_n$ 类，每个固定终端单独保留。不能只比较事件、记录、
后继或时钟的边缘；影响 selector、合法性、继续动作或读数的字段必须留在联合
输出中。若另要求 $z\,K_n\,u$ 时也有相同合法性和上述 $K_n$ 输出联合 law，
则得到可选的更强同层 lumpability；它可支持 $Q_n\to Q_n$ 的核，但不是移位
$Q_{n+1}\to Q_n$ 合同的必要前提。

式 (JKT.1) 给出局部移位下降；与第1节继承的 $K_0=\ker o$、闭合递归细化和
前缀／串接闭合的同一测试族一起，才可沿有限策略树归纳，得到 UJLB 的安全方向

$$
\boxed{K_n\subseteq A_n^{\mathrm{law}}.}
$$

这里 $A_n^{\mathrm{law}}$ 仍按该测试族全部深度不超过 $n$ 的完整轨迹 law 定义；
任意嵌套等价关系加 (JKT.1) 并不足以推出此包含。只有再有 UJLB 的续接 law
对 $K_{n-1}$ 类封闭及统一可识别性假设（例如共同支持分割或适当的类 law
仿射独立性）时，才可提升为
$K_n=A_n^{\mathrm{law}}$。随机合同中不得把这个条件等式写成定义，也不得把
$K_n$ 与 $A_n^{\mathrm{law}}$ 无条件识别。相关 law 与一次取得的区别见
[统一联合律桥](RECURSIVE_RELATIONAL_OBSERVATION_UNIFIED_JOINT_LAW_BRIDGE.md)
第1节及[法则残余与一次运行分离](RECURSIVE_RELATIONAL_OBSERVATION_LAW_RUN_RESIDUAL.md)。

## 3. 移位的有限随机塔

为避免把不存在的同层动力学偷偷加入模型，随机扩展采用移位核。假设：

* $Z$ 是可数的带类型来源；
* 每个 $Q_n$ 是有限的残余阶段；
* 每个动作的事件字母表 $E_a$、实际记录字母表 $R_a$ 和终端字母表 $F_a$
  都是有限的；
* 测试只使用有限前缀、显式权限和已取得记录。

对输入 $x_{n+1}\in Q_{n+1,\tau}$，定义从输入阶段 $n+1$ 到输出阶段 $n$ 的核

$$
\overline J_{a,n}
  (e,y,r\mid x_{n+1}),
\qquad
 y\in Q_{n,\upsilon}\sqcup F_a.
\tag{JKT.2}
$$

其完整输出空间为 $E_a\times(Q_{n,\upsilon}\sqcup F_a)\times R_a$。
任取 $z\in x_{n+1}$，按 $q^\sharp_{a,n}$ 的输出纤维对
$J_a^{\mathrm{tot}}(z;\cdot)$ 求和；
不在输入纤维上求和或另选先验。(JKT.1) 保证该行与输入代表无关。

对 $n\ge1$，明确输出限制为带类型不交并上的映射

$$
\rho_{a,n-1}
 =p_{n-1}|_{Q_{n,\upsilon}}\sqcup\operatorname{id}_{F_a}:
 Q_{n,\upsilon}\sqcup F_a\longrightarrow Q_{n-1,\upsilon}\sqcup F_a.
$$

它在成功类上取 $p_{n-1}$，在每个终端 $f$ 上固定 $f$ 及其类型标签。若
$\bar D_{a,n}\subseteq Q_{n+1,\tau}$ 是下降后的合法域，还要求
$\bar D_{a,n}=p_n^{-1}(\bar D_{a,n-1})$。有限 law 一致性要求

$$
 (\operatorname{id}_{E_a}\times\rho_{a,n-1}\times
  \operatorname{id}_{R_a})_*
 \overline J_{a,n}(\,\cdot\mid x_{n+1})
=
 \overline J_{a,n-1}(\,\cdot\mid p_nx_{n+1}).
 \qquad(n\ge1)
\tag{JKT.3}
$$

这里的输入和输出层刻意错开一层。不能以 (JKT.3) 替换同层递推，也不能从
“每层 law 相同”推出跨层核存在。对有限前缀闭合策略，(JKT.3) 逐层给出一致
的有限观察 law；它仍只涉及声明的事件、记录、终端和后继，不提供未执行未来的
完整表格。

## 4. 线程上的条件核延拓

在可数索引 $n\in\mathbb N$、有限离散阶段和标准柱集 sigma-代数下，若所有
$\overline J_{a,n}$ 满足 (JKT.3)，则对每个线程

$$
x=(x_0,x_1,\ldots)\in L
$$

可以按有限柱集定义一个条件 projective-kernel law $\widehat J_a(\cdot\mid x)$。
对 $x\in L_\tau=\varprojlim Q_{n,\tau}$，其输出空间为
$E_a\times(L_\upsilon\sqcup F_a)\times R_a$，其中
$L_\upsilon=\varprojlim Q_{n,\upsilon}$；固定终端不变成来源线程。
其有限坐标边缘由
$\overline J_{a,n}(\cdot\mid x_{n+1})$ 给出，一致性由 (JKT.3) 保证；在这些
有限性和可数性条件之外，不把延拓称为一般的无界测度定理。

这里还要求每个有限坐标核对输入坐标是可测的；在本节的有限离散阶段和离散
sigma-代数中这是自动满足的。于是由柱集定义的 $\widehat J_a$ 对线程参数
$x\in L_\tau$ 是可测的，并且其有限坐标边缘唯一决定该条件 law。若改用一般
标准 Borel 或不可数输出空间，必须另行给出可测核与测度延拓条件，不能把本段
有限离散论证直接外推。

令 $B_\tau=\eta[Z_\tau]$，并把成功后继和固定终端的取像分开定义为

$$
\eta_a^\sharp:Z_\upsilon\sqcup F_a\longrightarrow L_\upsilon\sqcup F_a,
\qquad
\eta_a^\sharp(z')=\eta(z'),\quad \eta_a^\sharp(f)=f.
$$

在第2节总核合同（含合法行、拒绝行和归一化）、第3节全部阶段假设与
(JKT.3) 一致性，以及本节的可数索引、有限离散阶段和标准柱集 sigma-代数
假设全部成立的前提下，对每个带类型动作 $a:\tau\to\upsilon$，若原始总核
$J_a^{\mathrm{tot}}$ 满足 (JKT.1) 且阶段行按上述输出纤维下降，则对每个
$z\in Z_\tau$ 有

$$
\widehat J_a(\cdot\mid\eta(z))
=
 (\operatorname{id}_{E_a}\times\eta_a^\sharp\times\operatorname{id}_{R_a})_*
 J_a^{\mathrm{tot}}(\cdot\mid z),
\tag{JKT.4}
$$

等式保留失败、终止的事件和记录；$\eta$ 本身从不作用于 $F_a$。式 (JKT.4)
只约束实际输入，不把任意完成点当成原来源。

应分开记账三件事：

1. **完成律**：$\widehat J_a$ 是定义在 $L$ 上的数学条件核，可能给虚拟线程
   正式赋予延拓行为；
2. **实际像集中**：对 $x\in B_\tau$，由 (JKT.4) 得
   $\widehat J_a(E_a\times(B_\upsilon\sqcup F_a)\times R_a\mid x)=1$。
   若只给出延拓而未验证 (JKT.4)，则须另验这一集中条件；它保留终端质量，
   不推出 $B=L$；
3. **观察者取得**：还要有有限、合法、可执行的 acquisition protocol，把某个
   $x\in B$ 的所需坐标写入观察者记录。数学上的核、商映射或解码器不等于已
   取得该值，也不授予完整 law 表。

## 5. 四视图运输的极限条件

设 $i\in\{\mathrm{space},\mathrm{time},\mathrm{boundary},\mathrm{memory}\}$。
本节只用共同来源的有限实际像 $Q_n^0=Q_n$。每层给出保留接口类型的满射表示

$$
r_{i,n}:Q_n^0\twoheadrightarrow Y_{i,n}^0=r_{i,n}[Q_n^0],
$$

以及 $n\ge1$ 时的 bonding map
$\delta_{i,n}:Y_{i,n}^0\to Y_{i,n-1}^0$，要求

$$
\delta_{i,n}r_{i,n}=r_{i,n-1}p_{n-1}\qquad(n\ge1).
\tag{JKT.5}
$$

先在来源 $Z$ 上声明保持类型的等价关系 $E_n^Z$。确定性精确 UJLB 情形取
$E_n^Z:=K_n$；随机 law 情形取 $E_n^Z:=A_n^{\mathrm{law}}$。只有显式假设
$E_n^Z$ 经 $K_n$ 下降时，才在 $Q_n^0=Q_n$ 上定义诱导关系

$$
x\,\bar E_n\,y
\quad\Longleftrightarrow\quad
\exists z,u\in Z:\quad q_n(z)=x,\quad q_n(u)=y,\quad z\,E_n^Z\,u.
$$

这里的下降条件明确取为 $K_n\subseteq E_n^Z$；它与 $E_n^Z$ 的等价性保证
代表元选择无关。确定性情形的诱导关系为 $\bar E_n=\Delta_{Q_n}$，即相等。
随机 law 情形须明确假设 $A_n^{\mathrm{law}}$ 是保持类型的等价关系且
$K_n\subseteq A_n^{\mathrm{law}}$，才能定义上述 $\bar E_n$；不具备这些下降
条件时，不声称存在此商关系。若另有可识别性等式 $K_n=A_n^{\mathrm{law}}$，
其诱导关系也为相等；此等式仍不是无条件结论。四个视图的精确视图合同明确要求

$$
\ker(r_{i,n})=\bar E_n
\qquad
\text{for every }i\in\{\mathrm{space},\mathrm{time},\mathrm{boundary},\mathrm{memory}\}.
$$

这里的 $\bar E_n$ 是由任务合同的来源关系诱导的有限关系，不由视图事后另选；下述
$\chi_{ji,n}$ 的双射、自然性和完整联合核条件都以此精确关系为共同域。

先定义各视图的完成与实际来源线程像：

$$
L_i=\varprojlim(Y_{i,n}^0,\delta_{i,n}),\qquad
\eta_i(z)=\bigl(r_{i,n}([z]_{K_n})\bigr)_n,\qquad B_i=\eta_i[Z]\subseteq L_i.
$$

再明确假设：每层四个表示在同一个 $Q_n^0$ 上有相等的行为核，并给定由这一
共同来源诱导的唯一双射

$$
\chi_{ji,n}:Y_{i,n}^0\simeq Y_{j,n}^0,\qquad
\chi_{ji,n}r_{i,n}=r_{j,n}.
$$

要求它们满足跨层交换式

$$
\delta_{j,n}\chi_{ji,n}=\chi_{ji,n-1}\delta_{i,n}\qquad(n\ge1).
$$

动态运输还要求合法性及完整联合核已在各表示纤维上下降，各视图的移位核
$\overline J^i_{a,n}$ 满足 (JKT.3) 的对应式。明确地，
$\bar D^i_{a,n}\subseteq Y^0_{i,n+1,\tau}$，并且对
$y\in Y^0_{i,n+1,\tau}$，
$\overline J^i_{a,n}(\,\cdot\mid y)$ 的输出空间为
$E_a\times\bigl(Y^0_{i,n,\upsilon}\sqcup F_a\bigr)\times R_a$；且

$$
\begin{aligned}
\bar D^j_{a,n}&=\chi_{ji,n+1}[\bar D^i_{a,n}],\\
\overline J^j_{a,n}(\cdot\mid\chi_{ji,n+1}y)
&=(\operatorname{id}_{E_a}\times\chi^\sharp_{ji,n}\times
\operatorname{id}_{R_a})_*\overline J^i_{a,n}(\cdot\mid y).
\end{aligned}
$$

这里 $\chi^\sharp_{ji,n}=\chi_{ji,n}|_{Y_{i,n,\upsilon}^0}\sqcup
\operatorname{id}_{F_a}$，保留事件、完整记录、失败和终止标签及接口类型。
selector（含停止及动作参数）只使用表示和已取得档案 $c$，并满足
$\Pi^j(a\mid\chi_{ji,n+1}y,c)=\Pi^i(a\mid y,c)$；权限和记录更新也须按上述
联合合同运输，不得另读隐藏来源。初始档案匹配，所选动作在当前表示上合法。

对每个有限自适应策略 $\Pi^i$、其按 $\chi_{ji}$ 运输的策略 $\Pi^j$，以及匹配的
档案／权限记录 $c_i,c_j$，令 $\mathsf{Tr}_{ji}^{\Pi,c}$ 为逐坐标运输的 transcript
映射，则

$$
(\mathsf{Tr}_{ji}^{\Pi,c})_*\operatorname{Law}_i
 \bigl(\mathsf{Tr}_i^{\Pi^i,c_i}\bigr)
=\operatorname{Law}_j
 \bigl(\mathsf{Tr}_j^{\Pi^j,c_j}\bigr).
$$

这里的等式对所有上述有限策略和匹配记录成立；它由列出的完整联合核运输、
selector 相容性及权限／记录更新条件按策略长度归纳得到，不是另行添入的自由
law 表。

在这些条件下，才逐坐标定义线程运输

$$
\chi_{ji}:L_i\to L_j,
\qquad
\chi_{ji}((y_{i,n})_n)=(\chi_{ji,n}(y_{i,n}))_n,
$$

其复合律和逆律为 $\chi_{ki}=\chi_{kj}\circ\chi_{ji}$、
$\chi_{ij}=\chi_{ji}^{-1}$；同源等式给出
$\chi_{ji}\eta_i=\eta_j$，从而 $\chi_{ji}(B_i)=B_j$。观察者的 acquisition
合同仍须另行运输。任意逐层双射若不交换 bonding map，不能定义上述极限映射；
只保持边缘不能保持有限策略树。这里所说的“相等行为核”具体是指同一
$\bar E_n$ 纤维上的完整联合输出 law，连同合法域、selector、档案和权限更新；
只比较某个边缘读数，不足以定义 $\chi_{ji,n}$ 的动态运输。若只有
$\ker r_{i,n}\subseteq\ker r_{j,n}$，则只得单向因子，即使它在实际像上满射，
也不蕴含逆运输。本节仅承接
[运输、任务记忆与完成化](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)
§12、§14、§26 的共同来源及自然图册条件。

与该文 TM §26 的条件字典为：$\Omega=Z$，$\sigma_n=q_n$，$p_n$ 是满足
$p_nq_{n+1}=q_n$ 的商塔限制映射，$r_{i,n}$ 是定义在 $Q_n$ 上的四个视图映射。
对目标动作取 $j_a(n)=n+1$；因此 TM 的 lookahead 输入 $\sigma_{j_a(n)}$
正对应 (JKT.2) 的 $Q_{n+1}$ 输入，而输出仍落在 $Q_n$。成功输出字母表是
$Q_{n,\upsilon}$，固定终端和事件、记录字母表分别对应 TM 环境层中的固定
终端、事件和档案分量；若 TM 的环境层含有额外值，本卷只比较实际像纤维上的
限制或先给出保持类型的嵌入，不能默认为同一字母表。$(JKT.5)$ 是相应的
bonding 自然性，上面展示的核运输等式是完整联合 law 条件。这只是条件字典，
不是新定理。

`RealizedImageKernelFactorization.lean` 中
`realized_image_unique_factorization_iff_reverse_kernel` 对应实际像上的唯一因子
条件；`IndependentDescentCriterion.lean` 的
`inverse_limit_descent_and_independent_converse` 对应“交换则下降、独立坐标提升
才可反推交换”的方向分离。它们不把任意 levelwise bijection 变成自然运输。

## 6. 虚拟线程与形式更新

一个具体边界来自[运输、任务记忆与完成化](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)
§5.3 的整数脉冲读数。对 $n\in\mathbb Z$ 和 $N\ge0$，令

$$
q_N(n)=\bigl(\mathbf 1_{\{n+k=0\}}\bigr)_{|k|\le N},
\qquad
B_N=q_N(\mathbb Z),
$$

令 $r_N:B_{N+1}\to B_N$ 为窗口限制，置

$$
Z:=\mathbb Z,\qquad Q_N:=B_N,\qquad p_N:=r_N,\qquad
\eta(n):=(q_N(n))_N,\qquad B:=\eta[Z],\qquad
L:=\varprojlim Q_N.
$$

全零坐标组成相容线程

$$
\omega=(0,0,0,\ldots)\in L.
$$

对每个有限 $N$ 都存在 $n$ 使 $q_N(n)=0$，但不存在一个整数满足所有窗口同时
为零：

$$
\forall N\ \exists n\;q_N(n)=0,
\qquad
\neg\exists n\ \forall N\;q_N(n)=0.
\tag{JKT.6}
$$

因此 $\omega\in L\setminus B$。沿用该节的识别
$L\cong\mathbb Z\sqcup\{\omega\}$，完成上可以定义

$$
\widetilde T(n)=n+1,
\qquad
\widetilde T(\omega)=\omega,
$$

并得到一个形式上相容的全局更新；然而任何实际整数经有限次正反平移仍是整数，
不能到达 $\omega$。这正是“虚拟线程可以承载扩展更新，而没有实际来源实现它”的
最小实例；这些数学结论不赋予 $\omega$ 物理边界、物理静止态或观察者可写入
状态的解释。

## 7. 从 $K_n$ 到 law 残余的有限比较

若另有嵌套 law 残余

$$
A_{n+1}^{\mathrm{law}}\subseteq A_n^{\mathrm{law}},
$$

并且在第1、2节继承的 UJLB 定义及闭合条件下有
$K_n\subseteq A_n^{\mathrm{law}}$，才有商比较映射

$$
\phi_n:Q_n=Z/K_n\longrightarrow Z/A_n^{\mathrm{law}},
\qquad
\phi_n([z]_{K_n})=[z]_{A_n^{\mathrm{law}}}.
$$

它在每个有限阶段是满射，因为目标类仍由同一个 $z\in Z$ 代表；这只是有限商的
比较，不是 law 递归等价，也不改变 $K_n\subseteq A_n^{\mathrm{law}}$ 的方向。
令 $s_n:Z/A_{n+1}^{\mathrm{law}}\to Z/A_n^{\mathrm{law}}$ 为自然投影；
极限映射使用交换式 $s_n\phi_{n+1}=\phi_np_n$，其在这些同源商上成立：

$$
\varprojlim Q_n\longrightarrow\varprojlim(Z/A_n^{\mathrm{law}}).
$$

逐层满射本身只给出单层 lift；极限满射还须有相容提升的依据。例如，对每个
law 线程 $t=(t_n)_n$，令 $H_n(t)=\phi_n^{-1}(t_n)$，可要求逐前缀提升合同

$$
H_0(t)\ne\varnothing,\qquad p_n[H_{n+1}(t)]=H_n(t)\quad\forall n.
$$

这保证每个已提升前缀可继续。也可改用紧乘积中相容前缀约束的非空闭有限交性质，
或足以保证非空逆极限的 Mittag--Leffler 假设。$Q_n$ 有限可用于紧性路线，
但须明确采用该紧性／有限交性质论证，不能只把各层满射或有限性写成已获相容
lift。有限 law 覆盖与全局 law 边界覆盖因此是不同层次的结论。

## 8. 三层结论与保留边界

本桥应始终区分三层：

1. **数学完成 $L$**：所有满足 bonding 方程的相容线程，允许包含虚拟点；
2. **实际来源像 $B=\eta[Z]$**：由真实来源产生的线程，规范同构于 $Z/K_\infty$；
3. **观察者可读／可存储子集**：由有限合法 acquisition、权限、参考、记录和
   资源合同实际取得的 $B$ 的表示，范围和精度依任务而定。取得有限坐标不等于
   存有完整线程；可取得范围可以严格小于 $B$。

在第5节的同源有限双射、bonding 自然性及全联合合同交换下，四视图可在实际像
$B_i$ 之间，或在完成空间 $L_i$ 之间互运；这不要求 $Z\cong L$。只有要把原始
来源本身与整个完成识别时，才同时要求分离
$\bigcap_nK_n=\Delta_Z$ 和完备 $B=L$。“观察者已经取得”仍须另证有限合法
协议、可读存储、权限和记录闭合，不能从数学互运或 $Z\cong L$ 推出。

仍开放的范围包括无界或非标准可测核、不可数输出与统一测度延拓、量子通道、
无限资源和算法成本、物理时空语义，以及把数学完成点实现为物理对象的经验主张。
本卷没有消除这些缺口，也没有把虚拟线程解释为物理实体。

## 追加锚（本行以下为增补区）

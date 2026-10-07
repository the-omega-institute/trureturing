# FIB-ATOM 混色树的实际地址费用部分界

## 1. 原来源、操作与费用

**定义 1.1（字面来源与替换）。** 来源是一棵未知的非空、有限、完整有序二叉树 $U$：每个节点或者是标为 $\alpha$ 或 $\beta$ 的叶，或者有按左、右排列的两个非空子树。括号、左右次序与每个不同出现均保留。替换为

$$
\rho\alpha=\beta,\qquad
\rho\beta=(\beta,\alpha),\qquad
\rho(S,T)=(\rho S,\rho T),\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
\tag{1.1}
$$

组成 $c(U)$ 是两色叶的数目。公开参数满足

$$
d=3k,\quad k\ge1,\quad a,b>0,\quad n=a+b\ge4,
\qquad
(A,B)=M^d(a,b)
=\bigl(F_{d-1}a+F_db,F_da+F_{d+1}b\bigr),
\tag{1.2}
$$

其中 $F_0=0,F_1=1,F_{t+2}=F_{t+1}+F_t$。令 $N=A+B$，$\mathcal T_C$ 是组成恰为 $C=(A,B)$ 的全部完整有序树，$\mathcal P=\mathcal T_C\cap\operatorname{im}\rho^d$。目标是在整个 $\mathcal T_C$ 上判定是否属于 $\operatorname{im}\rho^d$。负源没有正源高度承诺。

此处直接采用[原定义 57.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md#57-uniform-paid-acquisition-of-actual-image-certificates-at-exact-composition)的来源与组成；混色及 $n\ge4$ 是本卷的附加范围条件。

**定义 1.2（实际地址与四值读数）。** 地址是 $\{L,R\}$ 上的任意有限词，空词 $\varepsilon$ 表示根，词长表示深度。$r_U(u)$ 是同一棵固定树 $U$ 的端点读数：端点为相应叶时返回 $\alpha$ 或 $\beta$，为分支时返回 $\mathsf{br}$，穿过任何叶时返回 $\varnothing$。非空词在分支选择对应子树；非空词在叶上直接返回 $\varnothing$。

给定 $h\in\mathbb N\cup\{\infty\}$，任意 $|u|\le h$ 的原地址请求均合法，不要求先查询祖先。该读数采用 [ActualTreeReadoutAcquisition.readout、Address、Reply](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)。这是地址端口，没有额外导航、重置或探针操作。

**定义 1.3（空历史、策略与主费用）。** 实际历史是按时间排列的有限列表

$$
\mathcal H=((u_1,y_1),\ldots,(u_m,y_m)),\qquad y_j=r_U(u_j).
\tag{1.3}
$$

全部四种回复、原字面地址、先后次序与重复请求都保留。策略 $\pi$ 从共同的、与来源无关的初始化及空取得历史出发，只根据公开参数和自己的完整实际历史选择下一原地址或返回布尔值。合法策略必须在每个 $U\in\mathcal T_C$ 上有限终止且返回正确答案。

令 $T_\pi(U)$ 为完整终端历史，$Q(T)$ 为其中不同的实际请求地址集合。主费用及优化目标为

$$
\operatorname{paid}(T)=|Q(T)|,
\qquad
D_h(a,b;d)=\min_{\pi\text{ 合法}}\max_{V\in\mathcal P}|Q(T_\pi(V))|.
\tag{1.4}
$$

无合法策略时取 $+\infty$。每种回复都收费；重复仍是实际动作并进入历史，但不增加不同地址费用。最坏费用只在正源上取，正确性与有限终止则覆盖全部同组成源。$h=\infty$ 允许任意有限深词，仍要求逐源有限终止。

此处复用 [ActualTreeReadoutAcquisition.Policy、paid](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)的历史与不同地址接口，并按原定义 57.1 限定竞争域。其全组成第三像 `Strategy` 的完整叶基线不适用于本优化；这里也不使用把两种叶都赋零的 `chi`。运行时间、内存、词的编码和物理移动在式 (1.4) 中没有指定价格。公开候选的数学描述不会成为实际取得的来源索引、根报告、前沿或谱读数。

**定理 1.4（本卷的部分界）。** 令 $H=d+n-1$。对每个 $h\ge H$，包括 $h=\infty$，有

$$
A+3\ \le\ D_h(a,b;d)\ \le\ A+n-2+c_d(a,b),
\qquad
c_d(a,b)=
\begin{cases}
a,&d=3,\\
\min(a,b),&d\ge6.
\end{cases}
\tag{1.5}
$$

下界的量词是：对每个这样的参数、深度上限和原合法确定策略 $\pi$，存在**一棵固定有限正源** $V$，其从空历史开始的完整真实终端费用至少为 $A+3$。上界由一个在整个 $\mathcal T_C$ 上正确、有限终止的原地址策略实现。这两个界不要求相等。

证明。下界见定理 5.3，上界见定理 7.3。两条证明分别处理真实终端和实际补查，不以静态证书的存在代替取得。□

## 2. 直接复用的字面结构与终端条件

**定义 2.1（块与两色前沿）。** 记 $X_t=\rho^t\alpha$。对正源 $V$，$\mathcal A(V)$、$\mathcal B(V)$ 分别是其实际 $\alpha$、$\beta$ 叶的地址集。$w(u)=\#L(u)+2\#R(u)$。一个宏树是替换前组成为 $(a,b)$ 的完整有序树；宏叶 $\alpha$、$\beta$ 分别替换为 $X_d$、$X_{d+1}$。

定理 1.4 的证明直接使用[原引理 57.2、定理 57.3、57.4、57.7](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md#57-uniform-paid-acquisition-of-actual-image-certificates-at-exact-composition)。其所需的具体结论是：

$$
X_0=\alpha,\quad X_1=\beta,\quad
X_t=(X_{t-1},X_{t-2})\ (t\ge2),\qquad \rho^d\beta=X_{d+1},
\tag{2.1}
$$

$$
r_{X_t}(u)=
\begin{cases}
\mathsf{br},&w(u)\le t-2,\\
\beta,&w(u)=t-1,\\
\alpha,&w(u)=t\text{ 且末字母为 }R,\\
\varnothing,&\text{其余情况},
\end{cases}
\quad t\ge2.
\tag{2.2}
$$

$\rho$ 单射，$\mathcal P$ 正是全部宏树的逐叶替换族，大小为 $\operatorname{Cat}_{n-1}\binom na$。正源高度至多 $H$；$H$ 是本混色域的准确可解深度阈值。

接受正源 $V$ 的任何原合法策略，其实际终端请求集满足

$$
\mathcal A(V)\subseteq Q(T_\pi(V))
\quad\text{或}\quad
\mathcal B(V)\subseteq Q(T_\pi(V)),
\tag{2.3}
$$

而任一完整颜色前沿的真实匹配在 $\mathcal T_C$ 中唯一确定 $V$，包括任意高度的负竞争者。并且

$$
B-A=F_{d-2}a+F_{d-1}b\ge a+b=n\ge4.
\tag{2.4}
$$

以下是这些复用结论在定理 1.4 证明中的普通推导及条件展开。

式 (2.1) 由字面替换得到。在块内，$L$ 把索引减一，$R$ 把索引减二；索引一或零已经是叶。权重至多 $t-2$ 时尚未到叶，权重 $t-1$ 时到 $\beta$。权重 $t$ 只有最后走 $R$ 才能从索引二直接到 $\alpha$；最后走 $L$ 则此前已到索引一，真实回复为缺失。超过此权重也穿过叶。这证明式 (2.2) 的全部端点情形，空词给分支。

一步像的根 $\beta$ 唯一解码为 $\alpha$，特殊对 $(\beta,\alpha)$ 唯一解码为 $\beta$，其他像分支递归解码为源分支。特殊对不能是源分支的像，因为其右边的根 $\alpha$ 不是任何非空树的一步像。故一步替换以及每个迭代都单射。$\det M=-1$ 使组成为 $C$ 的 $d$ 次像前源组成必须是 $(a,b)$。有序完整树的形状计数及叶位置选择给出所述有限族。

宏树的每个叶深度至多 $n-1$；$X_d$、$X_{d+1}$ 的高度分别为 $d-1,d$。于是正源高度至多 $H$。含最深宏 $\beta$ 的梳树达到 $H$，其中一对最深 $(\beta,\alpha)$ 叶深度均为 $H$。当 $h<H$，交换该对标签，所有允许端点回复不变却得到同组成负例，故不可正确区分。当 $h\ge H$，有限正候选的 $\alpha$ 前沿并集扫描已给出正确有限策略；其正确性使用下述唯一性，不对负源施加高度限制。

$d\ge3$ 的正源都是二次像。二次叶块为 $(\beta,\alpha)$ 和 $((\beta,\alpha),\beta)$，所以每个分支都有两色后代，每个 $\alpha$ 是 $(\beta,\alpha)$ 的右叶；左 $\alpha$ 与终端对 $(\beta,\beta)$ 均不可能出现。

若请求集同时遗漏实际叶 $x\in\mathcal A(V)$、$y\in\mathcal B(V)$，只交换这两片标签得 $W$。形状、组成及除 $x,y$ 之外的全部端点回复不变；穿过它们的词仍回复缺失。若 $y$ 是 $x$ 的左兄弟，交换制造左 $\alpha$；否则 $x$ 原所在的终端对变成 $(\beta,\beta)$。故 $W$ 非二次像，尤其非 $d$ 次像。这给出式 (2.3) 的静态必要性。

任取颜色 $c$，把 $V$ 的全部 $c$ 叶地址及其前缀组成有限前缀树。每个分支有 $c$ 后代，故 $V$ 的每个分支均在此前缀树中；未占据的子槽恰是另一色的单叶。匹配全部这些 $c$ 端点的完整竞争树必须保留此前缀树，且其 $c$ 叶库存已全部用尽。每个空槽必须放一个非空的另一色子树。$V$ 每槽放一叶，已达到最少总叶数；同组成的竞争树有相同总叶数 $N$，故每槽也只能放一叶。竞争树因此等于 $V$。该论证对两色均适用，没有高度前提。

为把静态必要性用于原终端，固定任何匹配实际有限历史的树。逐动作归纳：空初始化相同；相同历史前缀使确定选择器请求同一原地址，固定树给出同一回复，包括重复；返回动作也相同。因此一个匹配实际终端请求集的竞争者必重放整条历史并接受。所有负源上的正确性强制该集是正证书，故式 (2.3) 对真实终端成立。式 (2.4) 是式 (1.2) 的差，两个系数均至少一。□

这些结构供应也对应 [ActualImageAddressCertificate.result、rigidity](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.md) 的组成证书与交换论证，以及 [ActualLeafHistoryRigidity.actual_address_geometry](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.md) 的原端点和字面上下文。后者的叶回复相容关系省去分支、缺失约束；下文的相容关系会保留全部四值。

## 3. 四叶联合读数的统一符号覆盖

**定义 3.1（完整四叶族）。** 四叶完整有序形状为

$$
(z,(z,(z,z))),\quad(z,((z,z),z)),\quad
((z,z),(z,z)),\quad((z,(z,z)),z),\quad(((z,z),z),z).
\tag{3.1}
$$

在各形状的四个有序叶位置，分别放一、二、三片宏 $\alpha$，其余为宏 $\beta$，得到库存 $(1,3),(2,2),(3,1)$ 的全部 $20,30,20$ 个宏树。证书的字面 `0` 代表宏 $\alpha$，`1` 代表宏 $\beta$，括号表示有序分支。实际替换分别为 $X_d,X_{d+1}$；字面数字与来源标签不混同。全部宏树见 §4。

**定理 3.2（每个原地址均在有限符号书内）。** 在上述任一四叶族，任何 $d\ge3$、任何有限原地址的联合四值回复向量都属于 §4 的六十四个向量。对 $|u|\ge3$，令 $p$ 为前三字母，$q=w(u)-d$，$e=\mathbf1_{\{u\text{ 末字母为 }R\}}$。第 $i$ 棵宏树中沿 $p$ 首先到达的宏叶地址和标签记为 $v_i,c_i$，其中 $c_i\in\{0,1\}$。令

$$
W_i=w(v_i),\qquad
\delta_i=q-W_i-c_i.
\tag{3.2}
$$

其第 $i$ 坐标由下表给出。

| 条件 | 坐标字符 | 实际回复 |
| --- | --- | --- |
| $\delta_i\le-2$ | `r` | 分支 $\mathsf{br}$ |
| $\delta_i=-1$ | `b` | 叶 $\beta$ |
| $\delta_i=0,e=1$ | `a` | 叶 $\alpha$ |
| $\delta_i=0,e=0$ 或 $\delta_i\ge1$ | `x` | 缺失 $\varnothing$ |

全部符号参数只需

$$
p\in\{LLL,LLR,LRL,LRR,RLL,RLR,RRL,RRR\},
\quad -1\le q\le8,\quad e\in\{0,1\},
\tag{3.3}
$$

共 $160$ 组；每族去重后恰为六十四个向量，按 `a<b<r<x` 排列。符号书允许不可由某个固定 $d,h$ 实现的参数，仅作**下界的超集**；它不许可上界发出符号请求。

证明。四叶宏树的最大叶深度为三，故沿 $p$ 必有唯一宏叶 $v_i$ 为 $u$ 的前缀。写 $u=v_is_i$。同一实际树的对应子树是 $X_{d+c_i}$，且

$$
w(s_i)-(d+c_i)=w(u)-W_i-d-c_i=\delta_i.
\tag{3.4}
$$

若 $s_i$ 非空，其末字母与 $u$ 相同，式 (2.2) 正好给出表中四值。若 $s_i$ 为空，$\delta_i=-d-c_i\le-3$，根回复分支；整词末字母此时不参与叶判断。因此到宏叶恰止步与进入块后的所有词都被覆盖。

每片宏叶非根，故 $W_i\ge1$；四叶深度至多三，故 $W_i+c_i\le7$。$q\le-1$ 时全部坐标为分支，$q\ge8$ 时全部缺失；越界参数分别用书中的常分支、常缺失向量代表。其余参数由式 (3.3) 穷尽，§4 每行的全部参数见证给出完整去重对应。

短词须单独核对。根和长度一的词均回复分支。长度二时，若首边仍在宏分支，第二边或者仍在宏分支，或者恰到替换块根，均回复分支。若首边到深度一宏叶，第二边读 $X_{d+c}$：第二边 $L$ 的权重一恒给分支；第二边 $R$ 的权重二仅在 $d=3,c=0$ 时给 $\beta$，其余给分支。故唯一例外是 $d=3$ 的 $LR,RR$。

$LR$ 的非恒定坐标恰是首边 $L$ 宏 $\alpha$ 的位置，等于参数 $(p,q,e)=(LRL,0,0)$ 的向量：这些位置有 $W_i+c_i=1$，给 $\delta_i=-1$；其余位置至少二，给分支。同理 $RR$ 等于 $(RRL,1,0)$：首边 $R$ 宏 $\alpha$ 的位置有 $W_i+c_i=2$，其余沿 $RRL$ 到的宏叶权重加标签至少三。所有其他短词都是书中的常分支行。

所以从空词到任意有限深词，跨过 $\alpha$、跨过 $\beta$、在空后缀结束的情形均有原四值向量。对策略真正请求且满足其深度上限的词取此向量即可；符号参数的额外成员只使下界证书承担更强的坐标条件。□

**定义 3.3（证书解码）。** 宏树索引与硬集号的字符表是 `0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ`，从零起依次代表整数。每族独立编号。向量号 $j$ 用十进制，$0\le j<64$；向量的第零坐标对应宏树索引 `0`。参数栏的 $P:q:e$ 中 $P=0,\ldots,7$ 依次代表式 (3.3) 的八个前三字母，$q$ 为有符号整数，$e$ 为零或一。该栏列出产生本行向量的**全部**符号参数。

首阶段两字符 `yH` 表示回复 $y\in\{b,r,x\}$，并保留编号为 `H` 的硬集 $S_H$。第二阶段三字符 `yik` 表示 $i,k$ 是 $S_H$ 内两枚不同宏树索引，二者在本向量均回复同一非 $\alpha$ 字符 $y$。`a--` 表示整个 $S_H$ 在本向量都回复 $\alpha$；两条横线不是索引，也不指定任意源对。

第二阶段表每行从所给起始向量号开始，列出依序十六项；起始号 $0,16,32,48$ 的四行覆盖同一硬集的全部六十四个向量。表中 `a,b,r,x` 分别代表 $\alpha,\beta,\mathsf{br},\varnothing$，与组成参数 $a,b$ 的字体用途区分。

**定理 3.4（有限坐标证书的谓词）。** §4 的全部数据同时满足以下有限等式和包含关系。设 $f_j$ 是第 $j$ 行向量，$t_{H,j}$ 是第二阶段项：

$$
\begin{aligned}
&f_j=(\Phi_i(p,q,e))_i\quad\text{对该行每个参数见证},\\
&\{(p,q,e):\text{全部见证栏}}=\{L,R\}^3\times\{-1,\ldots,8\}\times\{0,1\},\\
&\text{首阶段 }yH\Longrightarrow |S_H|\ge2,
\quad S_H\subseteq\{i:f_j(i)=y\},\quad y\ne a,\\
&t_{H,j}=yik\Longrightarrow i\ne k,\quad i,k\in S_H,
\quad f_j(i)=f_j(k)=y\ne a,\\
&t_{H,j}=a--\Longrightarrow \forall i\in S_H,\ f_j(i)=a.
\end{aligned}
\tag{3.5}
$$

其中 $\Phi_i$ 是式 (3.2) 的四值表。三个宏树表无重复，分别穷尽式 (3.1) 的对应标签配置。完整数目如下。

| 宏库存 | 宏树数 | 向量数及首阶段数 | 硬集数 | 第二阶段项数 | 符号参数数 |
| --- | --- | --- | --- | --- | --- |
| $(1,3)$ | 20 | 64 | 12 | 768 | 160 |
| $(2,2)$ | 30 | 64 | 17 | 1088 | 160 |
| $(3,1)$ | 20 | 64 | 10 | 640 | 160 |
| 合计 | 70 | 192 | 39 | 2496 | 480 |

首阶段包含关系共涉及 $976$ 个成员坐标。第二阶段共 $2442$ 个不同索引的非 $\alpha$ 重合对，以及 $54$ 个真正共同 $\alpha$ 项。

证明。每个形状在四个有序叶位置放 $a_0$ 个零，有 $\binom4{a_0}$ 个选择；五个形状不同，给出 $5\binom4{a_0}$ 个表中宏树。其叶词由括号逐边读取，故式 (3.2) 的 $W_i,c_i$ 均直接由这一有限表确定。

对每个见证三元组，把这些 $W_i,c_i$ 代入式 (3.2)：$q-W_i-c_i\le-2,-1,0,\ge1$ 及 $e=0,1$ 的判别分别给出向量字符。见证栏按八个 $P$、十个 $q$、两个 $e$ 划分全部 $160$ 组，每组恰出现一次，且表中六十四个字符串不同；因此既无未列参数，也无额外向量。

首阶段核对是读取所指定硬集的所有索引坐标；每一栏都给出同一个 $y\in\{b,r,x\}$。例如 $(1,3)$ 的向量零为 `aaaaaabbbrxxbabbrarb`，其首项 `b1` 的硬集为 $\{6,7,8,C,E,F\}$，六个坐标均为 `b`。$(2,2)$ 向量零的首项 `b1` 指向 $\{E,I,M,S,T\}$，五个坐标均为 `b`；$(3,1)$ 向量零的 `x1` 指向 $\{3,4,5,6,7\}$，五个坐标均为 `x`。其余行按同一坐标判别给出式 (3.5) 的首阶段关系。

第二阶段逐项读取三字符所给的两个不同索引；硬集表保证成员资格，向量表给出相同的非 `a` 字符。比如 $(1,3)$ 硬集一、向量二的 `r67` 在该向量的索引 $6,7$ 均为 `r`。共同 `a` 项须核对硬集的每个成员，而非任选两枚：该族硬集一在向量 $40,41$ 的 `a--` 正是六个成员全为 `a`；$(2,2)$ 硬集七在向量 $0,1,2$ 的 `a--` 是索引 $1,2,3,4,5$ 全为 `a`；$(3,1)$ 硬集一在向量 $8,9$ 的 `a--` 是索引 $3,4,5,6,7$ 全为 `a`。表中的其余共同 `a` 项也以全部成员坐标判别。

如此，每一格都归结为式 (3.2) 的整数减法和有限坐标读取。按表的四段排列，第二阶段项总数是 $(12+17+10)64=2496$；其中按 `a--` 计数为 $54$，其余 $2442$ 格均是不同索引的非 `a` 对。首阶段硬集大小逐行相加为 $976$。这些完整有限等式是下界证明使用的证书；它们不声称求得某个决策树的准确最优值。□

## 4. 完整有限证书表

### 4.1 四叶库存 $(1,3)$

**定义 4.1（宏树、向量与硬集）。** 本族的宏树按下表编号；每个向量的坐标依该顺序排列。

| 索引 | 宏树 |
| --- | --- |
| 0 | `(1,(1,(1,0)))` |
| 1 | `(1,(1,(0,1)))` |
| 2 | `(1,((1,1),0))` |
| 3 | `(1,(0,(1,1)))` |
| 4 | `(1,((1,0),1))` |
| 5 | `(1,((0,1),1))` |
| 6 | `((1,1),(1,0))` |
| 7 | `((1,1),(0,1))` |
| 8 | `((1,(1,1)),0)` |
| 9 | `(((1,1),1),0)` |
| A | `(0,(1,(1,1)))` |
| B | `(0,((1,1),1))` |
| C | `((1,0),(1,1))` |
| D | `((0,1),(1,1))` |
| E | `((1,(1,0)),1)` |
| F | `((1,(0,1)),1)` |
| G | `(((1,1),0),1)` |
| H | `((0,(1,1)),1)` |
| I | `(((1,0),1),1)` |
| J | `(((0,1),1),1)` |

| 向量号 | 四值坐标 | 首阶段 | 全部符号见证 $P:q:e$ |
| --- | --- | --- | --- |
| 0 | `aaaaaabbbrxxbabbrarb` | `b1` | 0:2:1 |
| 1 | `aaaaaabbbrxxbabbrarr` | `b1` | 1:2:1 |
| 2 | `aaaaaarrrrxxbrrrbrrr` | `r2` | 2:2:1；3:2:1 |
| 3 | `aabxbaaxxxabaaxxxxxx` | `x3` | 4:4:1 |
| 4 | `aarxbraxxxaraaxxxxxx` | `x3` | 5:4:1 |
| 5 | `abxbxxxxxxbxxxxxxxxx` | `x3` | 7:6:1 |
| 6 | `axxaxxxxxxaxxxxxxxxx` | `x3` | 6:6:1 |
| 7 | `baxbaaxaxxbaaaxxxxxx` | `x3` | 6:5:1 |
| 8 | `bbbbbbrrrraarbrrrbrr` | `b4` | 0:1:1；1:1:1 |
| 9 | `bbbbbbrrrraarrrrrrrr` | `b5` | 2:1:1；3:1:1 |
| 10 | `bbbbbbrrrrxxrbrrrbrr` | `b4` | 0:1:0；1:1:0 |
| 11 | `bbbbbbrrrrxxrrrrrrrr` | `b5` | 2:1:0；3:1:0 |
| 12 | `bbrarbbaxxbrbbaaaaaa` | `b6` | 4:3:1 |
| 13 | `bbrarrbaxxbrbbaaaaaa` | `b6` | 5:3:1 |
| 14 | `bbrxrbbxxxbrbbxxxxxx` | `b6` | 4:3:0 |
| 15 | `bbrxrrbxxxbrbbxxxxxx` | `b6` | 5:3:0 |
| 16 | `brxraaxaxxraaaxxxxxx` | `x3` | 7:5:1 |
| 17 | `brxrxxxxxxrxxxxxxxxx` | `x3` | 7:5:0 |
| 18 | `bxxbxxxxxxbxxxxxxxxx` | `x3` | 6:5:0 |
| 19 | `rbarbbabxxrbbbxxxxxx` | `b7` | 6:4:1 |
| 20 | `rbxrbbxbxxrbbbxxxxxx` | `b7` | 6:4:0 |
| 21 | `rrarbbabxxrbbbxxxxxx` | `b7` | 7:4:1 |
| 22 | `rrbrrrbrxxrrrraaaaaa` | `r7` | 6:3:1；7:3:1 |
| 23 | `rrbrrrbrxxrrrrxxxxxx` | `r7` | 6:3:0；7:3:0 |
| 24 | `rrrbrrrbaarrrrbbbbbb` | `b3` | 4:2:1；5:2:1 |
| 25 | `rrrbrrrbxxrrrrbbbbbb` | `b3` | 4:2:0；5:2:0 |
| 26 | `rrrrrrrraarrrrbbbbbb` | `b3` | 6:2:1；7:2:1 |
| 27 | `rrrrrrrrbbrrrrrrrrrr` | `r3` | 4:1:0；4:1:1；5:1:0；5:1:1；6:1:0；6:1:1；7:1:0；7:1:1 |
| 28 | `rrrrrrrrrrbbrrrrrrrr` | `r3` | 0:0:0；0:0:1；1:0:0；1:0:1；2:0:0；2:0:1；3:0:0；3:0:1 |
| 29 | `rrrrrrrrrrrrrrrrrrrr` | `r3` | 0:-1:0；0:-1:1；1:-1:0；1:-1:1；2:-1:0；2:-1:1；3:-1:0；3:-1:1；4:-1:0；4:-1:1；4:0:0；4:0:1；5:-1:0；5:-1:1；5:0:0；5:0:1；6:-1:0；6:-1:1；6:0:0；6:0:1；7:-1:0；7:-1:1；7:0:0；7:0:1 |
| 30 | `rrrrrrrrxxrrrrbbbbbb` | `b3` | 6:2:0；7:2:0 |
| 31 | `rrxrbbxbxxrbbbxxxxxx` | `b7` | 7:4:0 |
| 32 | `xaxaxxxxxxaxxxxxxxxx` | `x3` | 7:7:1 |
| 33 | `xbxbxxxxxxbxxxxxxxxx` | `x3` | 7:6:0 |
| 34 | `xxaxaxxxxxxaxxxxxxxx` | `x3` | 4:5:1 |
| 35 | `xxaxxaxxxxxaxxxxxxxx` | `x3` | 5:6:1 |
| 36 | `xxbxabxxxxxbxxxxxxxx` | `x3` | 5:5:1 |
| 37 | `xxbxbxxxxxxbxxxxxxxx` | `x3` | 4:4:0 |
| 38 | `xxbxxbxxxxxbxxxxxxxx` | `x3` | 5:5:0 |
| 39 | `xxrxbrxxxxxrxxxxxxxx` | `x3` | 5:4:0 |
| 40 | `xxxxxxaaabxxaxaabxba` | `x8` | 0:3:1 |
| 41 | `xxxxxxaaarxxaxaarxbr` | `x8` | 1:3:1 |
| 42 | `xxxxxxaabaxxxabaxbaa` | `x9` | 2:4:1 |
| 43 | `xxxxxxaaraxxxabrxraa` | `x9` | 3:4:1 |
| 44 | `xxxxxxbbbrxxbxbbrxrb` | `b1` | 0:2:0 |
| 45 | `xxxxxxbbbrxxbxbbrxrr` | `b1` | 1:2:0 |
| 46 | `xxxxxxbbrbxxabrbarbb` | `bA` | 2:3:1 |
| 47 | `xxxxxxbbrbxxabrrarbb` | `bA` | 3:3:1 |
| 48 | `xxxxxxbbrbxxxbrbxrbb` | `bA` | 2:3:0 |
| 49 | `xxxxxxbbrbxxxbrrxrbb` | `bA` | 3:3:0 |
| 50 | `xxxxxxrrrrxxbrrrbrrr` | `r2` | 2:2:0；3:2:0 |
| 51 | `xxxxxxxxaxxxxxaxxaxx` | `xB` | 2:5:1 |
| 52 | `xxxxxxxxaxxxxxxaxaxx` | `xB` | 3:6:1 |
| 53 | `xxxxxxxxbxxxxxabxbxx` | `xB` | 3:5:1 |
| 54 | `xxxxxxxxbxxxxxbxxbxx` | `xB` | 2:4:0 |
| 55 | `xxxxxxxxbxxxxxxbxbxx` | `xB` | 3:5:0 |
| 56 | `xxxxxxxxrxxxxxbrxrxx` | `xB` | 3:4:0 |
| 57 | `xxxxxxxxxaxxxxxxaxax` | `xC` | 0:4:1 |
| 58 | `xxxxxxxxxaxxxxxxaxxa` | `xC` | 1:5:1 |
| 59 | `xxxxxxxxxbxxxxxxbxab` | `xC` | 1:4:1 |
| 60 | `xxxxxxxxxbxxxxxxbxbx` | `xC` | 0:3:0 |
| 61 | `xxxxxxxxxbxxxxxxbxxb` | `xC` | 1:4:0 |
| 62 | `xxxxxxxxxrxxxxxxrxbr` | `xC` | 1:3:0 |
| 63 | `xxxxxxxxxxxxxxxxxxxx` | `x3` | 0:4:0；0:5:0；0:5:1；0:6:0；0:6:1；0:7:0；0:7:1；0:8:0；0:8:1；1:5:0；1:6:0；1:6:1；1:7:0；1:7:1；1:8:0；1:8:1；2:5:0；2:6:0；2:6:1；2:7:0；2:7:1；2:8:0；2:8:1；3:6:0；3:7:0；3:7:1；3:8:0；3:8:1；4:5:0；4:6:0；4:6:1；4:7:0；4:7:1；4:8:0；4:8:1；5:6:0；5:7:0；5:7:1；5:8:0；5:8:1；6:6:0；6:7:0；6:7:1；6:8:0；6:8:1；7:7:0；7:8:0；7:8:1 |

| 硬集号 | 宏树索引集 |
| --- | --- |
| 1 | 6,7,8,C,E,F |
| 2 | 8,9,H,I,J |
| 3 | E,F,G,H,I,J |
| 4 | 2,4,5,D,H |
| 5 | 0,1,2,3,4,5 |
| 6 | 0,1,6,A,C,D |
| 7 | 4,5,7,B,C,D |
| 8 | 3,A,B,D,H |
| 9 | 3,A,B,C,G |
| A | 6,7,9,D,I,J |
| B | C,D,G,I,J |
| C | C,D,E,F,H |

| 硬集号 | 起始向量号 | 依序十六个第二阶段项 |
| --- | --- | --- |
| 1 | 0 | `b67 b67 r67 x78 x78 x67 x67 x68 r67 r67 r67 r67 b6C b6C b6C b6C` |
| 1 | 16 | `x68 x67 x67 b7C b7C b7C r7C r7C b7E b7E bEF r67 r67 r67 bEF b7C` |
| 1 | 32 | `x67 x67 x67 x67 x67 x67 x67 x67 a-- a-- b8E r8F b67 b67 b67 b67` |
| 1 | 48 | `b67 b67 r67 x67 x67 b8F b8E b8F r8F x67 x67 x67 x67 x67 x67 x67` |
| 2 | 0 | `b8J r9I r89 x89 x89 x89 x89 x89 r89 r89 r89 r89 x89 x89 x89 x89` |
| 2 | 16 | `x89 x89 x89 x89 x89 x89 x89 x89 bHI bHI bHI b89 r89 r89 bHI x89` |
| 2 | 32 | `x89 x89 x89 x89 x89 x89 x89 x89 b9I r9J b8H r8H b8J r9I b9I b9I` |
| 2 | 48 | `b9I b9I r89 x9I x9I b8H b8H b8H r8H x8H x8H b9J b9I b9J r9J x89` |
| 3 | 0 | `bEF bEF rEF xEF xEF xEF xEF xEF rEF rEF rEF rEF a-- a-- xEF xEF` |
| 3 | 16 | `xEF xEF xEF xEF xEF xEF a-- xEF bEF bEF bEF rEF rEF rEF bEF xEF` |
| 3 | 32 | `xEF xEF xEF xEF xEF xEF xEF xEF bGI rGJ bEH rFH bEF bEF bFI bIJ` |
| 3 | 48 | `bFI bIJ rEF xFG xEG bFH bEH bFH rFH xEF xEF bGJ bGI bGJ rGJ xEF` |
| 4 | 0 | `a-- a-- rDH b24 r25 x24 x24 x2H b24 b24 b24 b24 b5D r24 b5D r24` |
| 4 | 16 | `x2H x24 x24 b45 b45 b45 r45 r45 r24 r24 r24 r24 r24 r24 r24 b45` |
| 4 | 32 | `x24 x24 x5D x4D b25 b24 b25 r25 x24 x24 x24 x24 x24 x24 x24 x24` |
| 4 | 48 | `x24 x24 rDH x24 x24 x24 x24 x24 x24 x24 x24 x24 x24 x24 x24 x24` |
| 5 | 0 | `a-- a-- a-- b24 r25 b13 x12 b03 b01 b01 b01 b01 b01 b01 b01 b01` |
| 5 | 16 | `r13 r13 b03 b14 b14 b45 r01 r01 r01 r01 r01 r01 r01 r01 r01 b45` |
| 5 | 32 | `x02 b13 x01 x01 b25 b24 b25 r25 x01 x01 x01 x01 x01 x01 x01 x01` |
| 5 | 48 | `x01 x01 x01 x01 x01 x01 x01 x01 x01 x01 x01 x01 x01 x01 x01 x01` |
| 6 | 0 | `b6C b6C r6D a-- a-- b1A x16 b0A b01 b01 b01 b01 b01 b01 b01 b01` |
| 6 | 16 | `r1A r1A b0A b1C b1C bCD r01 r01 r01 r01 r01 r01 r01 r01 r01 bCD` |
| 6 | 32 | `x06 b1A x01 x01 x01 x01 x01 x01 x01 x01 x01 x01 b6C b6C b6D b6D` |
| 6 | 48 | `b6D b6D r6D x01 x01 x01 x01 x01 x01 x01 x01 x01 x01 x01 x01 x01` |
| 7 | 0 | `b7C b7C r7D b4B r5B x45 x45 a-- b45 b45 b45 b45 b5C bCD b5C bCD` |
| 7 | 16 | `a-- x45 x45 b45 b45 b45 r45 r45 r45 r45 r45 r45 r45 r45 r45 b45` |
| 7 | 32 | `x45 x45 x57 x47 b5B b4B b5B r5B x45 x45 x45 x45 b7C b7C b7D b7D` |
| 7 | 48 | `b7D b7D r7D x45 x45 x45 x45 x45 x45 x45 x45 x45 x45 x45 x45 x45` |
| 8 | 0 | `xAB xAB rDH x3H x3H b3A xBD b3A b3D rDH b3D rDH bAD bAD bAD bAD` |
| 8 | 16 | `r3A r3A b3A bBD bBD bBD r3A r3A b3H b3H r3A r3A bAB r3A r3A bBD` |
| 8 | 32 | `xBD b3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A` |
| 8 | 48 | `x3A x3A rDH x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A` |
| 9 | 0 | `xAB xAB bCG x3G x3G b3A xBC b3A rCG rCG rCG rCG bAC bAC bAC bAC` |
| 9 | 16 | `r3A r3A b3A bBC bBC bBC r3A r3A b3G b3G r3A r3A bAB r3A r3A bBC` |
| 9 | 32 | `xBC b3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A` |
| 9 | 48 | `x3A x3A bCG x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A x3A` |
| A | 0 | `b67 b67 r67 x79 x79 x67 x67 x69 r67 r67 r67 r67 b6D b6D b6D b6D` |
| A | 16 | `x69 x67 x67 b7D b7D b7D r7D r7D b7I b7I bIJ r67 r67 r67 bIJ b7D` |
| A | 32 | `x67 x67 x67 x67 x67 x67 x67 x67 b9I r9J a-- a-- b67 b67 b67 b67` |
| A | 48 | `b67 b67 r67 x67 x67 x67 x67 x67 x67 x67 x67 b9J b9I b9J r9J x67` |
| B | 0 | `bCJ rGI bCG xGI xGI xCD xCD xGI rCG rCD rCG rCD bCD bCD bCD bCD` |
| B | 16 | `xGI xCD xCD bCD bCD bCD rCD rCD bGI bGI bGI rCD rCD rCD bGI bCD` |
| B | 32 | `xCD xCD xCD xCD xCD xCD xCD xCD bGI rGJ xCG xCG bCJ rGI bDI bDI` |
| B | 48 | `bDI bDI bCG xCD xCD xCD xCD xCD xCD xCD xCD bGJ bGI bGJ rGJ xCD` |
| C | 0 | `bCE bCE rDE xEF xEF xCD xCD xEF bDH rCD bDH rCD bCD bCD bCD bCD` |
| C | 16 | `xEF xCD xCD bCD bCD bCD rCD rCD bEF bEF bEF rCD rCD rCD bEF bCD` |
| C | 32 | `xCD xCD xCD xCD xCD xCD xCD xCD xDH xDH bEH rFH bCE bCE bDF rEF` |
| C | 48 | `bDF rEF rDE xCD xCD bFH bEH bFH rFH xCD xCD xCD xCD xCD xCD xCD` |

### 4.2 四叶库存 $(2,2)$

**定义 4.2（宏树、向量与硬集）。** 本族的宏树按下表编号；每个向量的坐标依该顺序排列。

| 索引 | 宏树 |
| --- | --- |
| 0 | `(1,(1,(0,0)))` |
| 1 | `(1,(0,(1,0)))` |
| 2 | `(1,(0,(0,1)))` |
| 3 | `(1,((1,0),0))` |
| 4 | `(1,((0,1),0))` |
| 5 | `(1,((0,0),1))` |
| 6 | `((1,1),(0,0))` |
| 7 | `(0,(1,(1,0)))` |
| 8 | `(0,(1,(0,1)))` |
| 9 | `(0,((1,1),0))` |
| A | `(0,(0,(1,1)))` |
| B | `(0,((1,0),1))` |
| C | `(0,((0,1),1))` |
| D | `((1,0),(1,0))` |
| E | `((1,0),(0,1))` |
| F | `((0,1),(1,0))` |
| G | `((0,1),(0,1))` |
| H | `((1,(1,0)),0)` |
| I | `((1,(0,1)),0)` |
| J | `(((1,1),0),0)` |
| K | `((0,(1,1)),0)` |
| L | `(((1,0),1),0)` |
| M | `(((0,1),1),0)` |
| N | `((0,0),(1,1))` |
| O | `((1,(0,0)),1)` |
| P | `((0,(1,0)),1)` |
| Q | `((0,(0,1)),1)` |
| R | `(((1,0),0),1)` |
| S | `(((0,1),0),1)` |
| T | `(((0,0),1),1)` |

| 向量号 | 四值坐标 | 首阶段 | 全部符号见证 $P:q:e$ |
| --- | --- | --- | --- |
| 0 | `aaaaaabxxxxxxbbaabbrarbabaarbb` | `b1` | 0:2:1 |
| 1 | `aaaaaabxxxxxxbbaabbrarrabaarrr` | `b2` | 1:2:1 |
| 2 | `aaaaaarxxxxxxbbrrrrbrrrbrrrbbr` | `b3` | 2:2:1；3:2:1 |
| 3 | `aabxxxxabxbxxxxxxxxxxxxxxxxxxx` | `x4` | 7:6:1 |
| 4 | `abaxxaxbaxbaaxaxaxxxxxxaxxxxxx` | `x4` | 6:5:1 |
| 5 | `axxbaaxaabxbaaxaxxxxxxxaxxxxxx` | `x4` | 4:4:1 |
| 6 | `axxbrbxaarxbraxaxxxxxxxaxxxxxx` | `x4` | 5:4:1 |
| 7 | `baarbbabbrarbbabaxxxxxxbaaaaaa` | `b5` | 4:3:1 |
| 8 | `baarrrabbrarrbabaxxxxxxbaaaaaa` | `b5` | 5:3:1 |
| 9 | `bbbbbbraaaaaarrbbrrrbrrbrbbrrr` | `b6` | 0:1:1；1:1:1 |
| 10 | `bbbbbbraaaaaarrrrrrrrrrrrrrrrr` | `b7` | 2:1:1；3:1:1 |
| 11 | `bbbbbbrxxxxxxrrbbrrrbrrbrbbrrr` | `b6` | 0:1:0；1:1:0 |
| 12 | `bbbbbbrxxxxxxrrrrrrrrrrrrrrrrr` | `b7` | 2:1:0；3:1:0 |
| 13 | `bbrxxaxbrxraaxaxaxxxxxxaxxxxxx` | `x4` | 7:5:1 |
| 14 | `bbrxxxxbrxrxxxxxxxxxxxxxxxxxxx` | `x4` | 7:5:0 |
| 15 | `brbaabarbarbbababxxxxxxbxxxxxx` | `b8` | 6:4:1 |
| 16 | `brbxxbxrbxrbbxbxbxxxxxxbxxxxxx` | `b8` | 6:4:0 |
| 17 | `bxxrbbxbbrxrbbxbxxxxxxxbxxxxxx` | `b5` | 4:3:0 |
| 18 | `bxxrrrxbbrxrrbxbxxxxxxxbxxxxxx` | `b5` | 5:3:0 |
| 19 | `rbbrrrbrrrbrrrbrbaaaaaarbbbbbb` | `b4` | 4:2:1；5:2:1 |
| 20 | `rbbrrrbrrrbrrrbrbxxxxxxrbbbbbb` | `b4` | 4:2:0；5:2:0 |
| 21 | `rrraabarrarbbababxxxxxxbxxxxxx` | `b8` | 7:4:1 |
| 22 | `rrrbbrbrrbrrrbrbrxxxxxxraaaaaa` | `b9` | 6:3:1；7:3:1 |
| 23 | `rrrbbrbrrbrrrbrbrxxxxxxrxxxxxx` | `b9` | 6:3:0；7:3:0 |
| 24 | `rrrrrrrbbbbbbrrrrrrrrrrrrrrrrr` | `bA` | 0:0:0；0:0:1；1:0:0；1:0:1；2:0:0；2:0:1；3:0:0；3:0:1 |
| 25 | `rrrrrrrrrrrrrrrrraaaaaarbbbbbb` | `b4` | 6:2:1；7:2:1 |
| 26 | `rrrrrrrrrrrrrrrrrbbbbbbrrrrrrr` | `bB` | 4:1:0；4:1:1；5:1:0；5:1:1；6:1:0；6:1:1；7:1:0；7:1:1 |
| 27 | `rrrrrrrrrrrrrrrrrrrrrrrrrrrrrr` | `r4` | 0:-1:0；0:-1:1；1:-1:0；1:-1:1；2:-1:0；2:-1:1；3:-1:0；3:-1:1；4:-1:0；4:-1:1；4:0:0；4:0:1；5:-1:0；5:-1:1；5:0:0；5:0:1；6:-1:0；6:-1:1；6:0:0；6:0:1；7:-1:0；7:-1:1；7:0:0；7:0:1 |
| 28 | `rrrrrrrrrrrrrrrrrxxxxxxrbbbbbb` | `b4` | 6:2:0；7:2:0 |
| 29 | `rrrxxbxrrxrbbxbxbxxxxxxbxxxxxx` | `b8` | 7:4:0 |
| 30 | `xaxxxxxaxxaxxxxxxxxxxxxxxxxxxx` | `x4` | 6:6:1 |
| 31 | `xbxxxxxbxxbxxxxxxxxxxxxxxxxxxx` | `x4` | 6:5:0 |
| 32 | `xxaxxxxxaxaxxxxxxxxxxxxxxxxxxx` | `x4` | 7:7:1 |
| 33 | `xxbxxxxxbxbxxxxxxxxxxxxxxxxxxx` | `x4` | 7:6:0 |
| 34 | `xxxabaxxxbxabxxxxxxxxxxxxxxxxx` | `x4` | 5:5:1 |
| 35 | `xxxaxxxxxaxaxxxxxxxxxxxxxxxxxx` | `x4` | 4:5:1 |
| 36 | `xxxbrbxxxrxbrxxxxxxxxxxxxxxxxx` | `x4` | 5:4:0 |
| 37 | `xxxbxxxxxbxbxxxxxxxxxxxxxxxxxx` | `x4` | 4:4:0 |
| 38 | `xxxxaxxxxaxxaxxxxxxxxxxxxxxxxx` | `x4` | 5:6:1 |
| 39 | `xxxxbxxxxbxxbxxxxxxxxxxxxxxxxx` | `x4` | 5:5:0 |
| 40 | `xxxxxxaxxxxxxaaxxaabxbaxaxxbaa` | `x6` | 0:3:1 |
| 41 | `xxxxxxaxxxxxxaaxxaarxbrxaxxbrb` | `x6` | 1:3:1 |
| 42 | `xxxxxxaxxxxxxxxaabaxbaaxabaxxa` | `x3` | 2:4:1 |
| 43 | `xxxxxxaxxxxxxxxaabrxraaxbbrxxa` | `x3` | 3:4:1 |
| 44 | `xxxxxxbxxxxxxaabbrbarbbabrbaab` | `bC` | 2:3:1 |
| 45 | `xxxxxxbxxxxxxaabbrrarbbarrraab` | `bD` | 3:3:1 |
| 46 | `xxxxxxbxxxxxxbbxxbbrxrbxbxxrbb` | `b1` | 0:2:0 |
| 47 | `xxxxxxbxxxxxxbbxxbbrxrrxbxxrrr` | `b2` | 1:2:0 |
| 48 | `xxxxxxbxxxxxxxxbbrbxrbbxbrbxxb` | `bC` | 2:3:0 |
| 49 | `xxxxxxbxxxxxxxxbbrrxrbbxrrrxxb` | `bD` | 3:3:0 |
| 50 | `xxxxxxrxxxxxxbbrrrrbrrrbrrrbbr` | `b3` | 2:2:0；3:2:0 |
| 51 | `xxxxxxxxxxxxxxxxxabxbxxxaabxxx` | `xE` | 3:5:1 |
| 52 | `xxxxxxxxxxxxxxxxxaxxaxxxxaxxxx` | `xE` | 2:5:1 |
| 53 | `xxxxxxxxxxxxxxxxxbrxrxxxbbrxxx` | `xE` | 3:4:0 |
| 54 | `xxxxxxxxxxxxxxxxxbxxbxxxxbxxxx` | `xE` | 2:4:0 |
| 55 | `xxxxxxxxxxxxxxxxxxaxaxxxxxaxxx` | `xE` | 3:6:1 |
| 56 | `xxxxxxxxxxxxxxxxxxbxbxxxxxbxxx` | `xE` | 3:5:0 |
| 57 | `xxxxxxxxxxxxxxxxxxxaxaxxxxxaxx` | `xF` | 0:4:1 |
| 58 | `xxxxxxxxxxxxxxxxxxxaxxaxxxxxax` | `xG` | 1:5:1 |
| 59 | `xxxxxxxxxxxxxxxxxxxbxabxxxxaba` | `xH` | 1:4:1 |
| 60 | `xxxxxxxxxxxxxxxxxxxbxbxxxxxbxx` | `xF` | 0:3:0 |
| 61 | `xxxxxxxxxxxxxxxxxxxbxxbxxxxxbx` | `xG` | 1:4:0 |
| 62 | `xxxxxxxxxxxxxxxxxxxrxbrxxxxbrb` | `xH` | 1:3:0 |
| 63 | `xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx` | `x4` | 0:4:0；0:5:0；0:5:1；0:6:0；0:6:1；0:7:0；0:7:1；0:8:0；0:8:1；1:5:0；1:6:0；1:6:1；1:7:0；1:7:1；1:8:0；1:8:1；2:5:0；2:6:0；2:6:1；2:7:0；2:7:1；2:8:0；2:8:1；3:6:0；3:7:0；3:7:1；3:8:0；3:8:1；4:5:0；4:6:0；4:6:1；4:7:0；4:7:1；4:8:0；4:8:1；5:6:0；5:7:0；5:7:1；5:8:0；5:8:1；6:6:0；6:7:0；6:7:1；6:8:0；6:8:1；7:7:0；7:8:0；7:8:1 |

| 硬集号 | 宏树索引集 |
| --- | --- |
| 1 | E,I,M,S,T |
| 2 | D,E,H,I,O |
| 3 | D,E,J,N,R,S |
| 4 | P,Q,R,S,T |
| 5 | 7,8,D,F,N |
| 6 | F,G,K,N,P,Q |
| 7 | 1,2,3,4,5 |
| 8 | B,C,E,G,N |
| 9 | 3,4,6,9,D,F |
| A | 7,8,9,A,B,C |
| B | H,I,J,K,L,M |
| C | G,I,M,Q,T |
| D | F,G,L,M,T |
| E | L,M,R,S |
| F | K,M,P,Q,T |
| G | K,L,P,Q,R |
| H | I,K,O,P |

| 硬集号 | 起始向量号 | 依序十六个第二阶段项 |
| --- | --- | --- |
| 1 | 0 | `bEI bEI bES xEI xIM xEI xEI xIM xIM rEI rEI rEI rEI xIM xEI xIM` |
| 1 | 16 | `xIM xEI xEI bES bES xIM xIM xIM rEI bST bIM rEI bST xIM xEI xEI` |
| 1 | 32 | `xEI xEI xEI xEI xEI xEI xEI xEI a-- rMS xES xES bIM bMT bEI bEI` |
| 1 | 48 | `bIM bMT bES xEM xEI xEM xEI xEM xEM xEI xEI bMS xEI bMS rMS xEI` |
| 2 | 0 | `bDE bDE bDE xDE xDH xEH xEH xHI xHI rDE rDE rDE rDE xDH xDE xHI` |
| 2 | 16 | `xDH xEH xEH bEO bEO xHI xHI xHI rDE rDE bHI rDE rDE xDH xDE xDE` |
| 2 | 32 | `xDE xDE xDE xDE xDE xDE xDE xDE a-- a-- xDE bHO bIO rHI bDE bDE` |
| 2 | 48 | `bIO rHI bDE xDE xDE bHO xDE xDE xDE xDE xDE xDE xDE xDE xDE xDE` |
| 3 | 0 | `bDE bDE bDE xDE xDJ xEJ xEJ bDN bDN rDE rDE rDE rDE xDJ xDE bEN` |
| 3 | 16 | `bEN bDN bDN bER bER bEN rEN rEN rDE bRS rDE rDE bRS bEN xDE xDE` |
| 3 | 32 | `xDE xDE xDE xDE xDE xDE xDE xDE bJR rJS xDE xDE a-- a-- bDE bDE` |
| 3 | 48 | `xDE xDE bDE xDE xDE xDE xDE xDE xDE xDE xDE bJS bJR bJS rJS xDE` |
| 4 | 0 | `bST rRS bRS xPQ xPQ xPQ xPQ a-- a-- bPQ rPQ bPQ rPQ xPQ xPQ xPQ` |
| 4 | 16 | `xPQ xPQ xPQ bPQ bPQ xPQ a-- xPQ rPQ bPQ rPQ rPQ bPQ xPQ xPQ xPQ` |
| 4 | 32 | `xPQ xPQ xPQ xPQ xPQ xPQ xPQ xPQ xPQ bRT xRS xRS bQT rPQ bST rRS` |
| 4 | 48 | `bQT rPQ bRS xRS xQR xRS xQR xPR xPR xPQ xPQ xPQ xPQ xPQ bRT xPQ` |
| 5 | 0 | `x78 x78 bDN xDF xDF a-- a-- b78 b78 bFN rDF bFN rDF xDF xDF b8N` |
| 5 | 16 | `b8N b78 b78 r78 r78 r78 bDF bDF b78 r78 r78 r78 r78 r78 x8D x8D` |
| 5 | 32 | `x7D x7D x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78` |
| 5 | 48 | `x78 x78 bDN x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78` |
| 6 | 0 | `a-- a-- rFG xFG xFK xGK xGK bFN bFN bFG rFG bFG rFG xFK xFG bGN` |
| 6 | 16 | `bGN bFN bFN bGP bGP bGN rGN rGN rFG bPQ rFG rFG bPQ bGN xFG xFG` |
| 6 | 32 | `xFG xFG xFG xFG xFG xFG xFG xFG xFG xFG bKP rKQ bFG bFG xFG xFG` |
| 6 | 48 | `bFG bFG rFG bKQ xFG rKQ bKP xFG bKQ xFG xFG xFG xFG xFG xFG xFG` |
| 7 | 0 | `a-- a-- a-- x34 x34 x12 b35 b45 r34 b12 b12 b12 b12 x34 x34 b25` |
| 7 | 16 | `b25 b45 r34 b12 b12 r12 b34 b34 r12 r12 r12 r12 r12 r12 x23 x23` |
| 7 | 32 | `x13 x13 x12 x12 b35 x12 x12 x12 x12 x12 x12 x12 x12 x12 x12 x12` |
| 7 | 48 | `x12 x12 x12 x12 x12 x12 x12 x12 x12 x12 x12 x12 x12 x12 x12 x12` |
| 8 | 0 | `xBC xBC bEN xBC a-- xEG xEG bCN rBC bGN rEG bGN rEG a-- xBC bBC` |
| 8 | 16 | `bBC bCN rBC bEG bEG bBC rBC rBC bBC rBC rBC rBC rBC bBC xBC xBC` |
| 8 | 32 | `xBC xBC xEG xCE xEG xCE xBE xBE xBC xBC xBC xBC xBC xBC xBC xBC` |
| 8 | 48 | `xBC xBC bEN xBC xBC xBC xBC xBC xBC xBC xBC xBC xBC xBC xBC xBC` |
| 9 | 0 | `b6D b6D r6F x34 x34 b39 r49 b4D bDF b34 b34 b34 b34 x34 x34 a--` |
| 9 | 16 | `x34 b4D bDF r34 r34 a-- b34 b34 r34 r34 r34 r34 r34 x34 x34 x34` |
| 9 | 32 | `x34 x34 b49 x46 r49 b39 x36 b49 x34 x34 x34 x34 b6F b6F b6D b6D` |
| 9 | 48 | `b6F b6F r6F x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34` |
| A | 0 | `x78 x78 x78 b8A b7A b9B r9C b78 b78 a-- a-- x78 x78 r8A r8A b8B` |
| A | 16 | `b8B b78 b78 r78 r78 bBC r78 r78 b78 r78 r78 r78 r78 bBC x89 b7A` |
| A | 32 | `x79 b8A b9C x78 r9C b9B x78 b9C x78 x78 x78 x78 x78 x78 x78 x78` |
| A | 48 | `x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78 x78` |
| B | 0 | `bHI bHI rHI xHI xHI xHI xHI xHI xHI rHI rHI rHI rHI xHI xHI xHI` |
| B | 16 | `xHI xHI xHI a-- xHI xHI xHI xHI rHI a-- bHI rHI xHI xHI xHI xHI` |
| B | 32 | `xHI xHI xHI xHI xHI xHI xHI xHI bJL rJM bHK rIK bIL bLM bHI bHI` |
| B | 48 | `bIL bLM rHI bIK xIJ rIK bHK xHJ bIK xHI xHI bJM bJL bJM rJM xHI` |
| C | 0 | `bIM rMT rGI xGI xIM xGI xGI xIM xIM bGQ rGI bGQ rGI xIM xGI xIM` |
| C | 16 | `xIM xGI xGI bGQ bGQ xIM xIM xIM rGI bQT bIM rGI bQT xIM xGI xGI` |
| C | 32 | `xGI xGI xGI xGI xGI xGI xGI xGI xGQ xGQ a-- rIQ bGI bGM bIM rMT` |
| C | 48 | `bGI bGM rGI bIQ xGI rIQ xGI xGM bIQ xGI xGI xGI xGI xGI xGI xGI` |
| D | 0 | `bMT rLM rFG xFG xFL xGL xGL xLM xLM bFG rFG bFG rFG xFL xFG xLM` |
| D | 16 | `xFL xGL xGL bGT bGT xLM xLM xLM rFG rFG bLM rFG rFG xFL xFG xFG` |
| D | 32 | `xFG xFG xFG xFG xFG xFG xFG xFG xFG bLT a-- a-- bFG bFG bMT rLM` |
| D | 48 | `bFG bFG rFG xFG xFG xFG xFG xFG xFG xFG xFG xFG xFG xFG bLT xFG` |
| E | 0 | `bMS rLM bRS xLM xLM xLM xLM xLM xLM rLM rLM rLM rLM xLM xLM xLM` |
| E | 16 | `xLM xLM xLM bRS bRS xLM xLM xLM rLM bRS bLM rLM bRS xLM xLM xLM` |
| E | 32 | `xLM xLM xLM xLM xLM xLM xLM xLM bLR bLR xRS xRS bLM bLM bMS rLM` |
| E | 48 | `bLM bLM bRS xLM xLM xLM xLM xLM xLM xMS xLR bMS bLR bMS bLR xLM` |
| F | 0 | `bMT rMT rKM xKM xKM xKM xKM xKM xKM bKP rKM bKP rKM xKM xKM xKM` |
| F | 16 | `xKM xKM xKM bPQ bPQ xKM xKM xKM rKM bPQ bKM rKM bPQ xKM xKM xKM` |
| F | 32 | `xKM xKM xKM xKM xKM xKM xKM xKM xKP xKP bKP rKQ bMQ bMT bMT rMT` |
| F | 48 | `bMQ bMT rKM bKQ xMQ rKQ bKP xMP bKQ xKM xKP xKP xKM xKP xKP xKM` |
| G | 0 | `rLR rLR rKL xKL xKL xKL xKL xKL xKL bKP rKL bKP rKL xKL xKL xKL` |
| G | 16 | `xKL xKL xKL bPQ bPQ xKL xKL xKL rKL bPQ bKL rKL bPQ xKL xKL xKL` |
| G | 32 | `xKL xKL xKL xKL xKL xKL xKL xKL bLR bLR bKP rKQ bLQ rKP rLR rLR` |
| G | 48 | `bLQ rKP rKL bKQ xLQ rKQ bKP xLP bKQ xKP xKL xKP bLR xKL bLR xKL` |
| H | 0 | `bIO bIO rIK xIK xIK xIK xIK xIK xIK bKP rIK bKP rIK xIK xIK xIK` |
| H | 16 | `xIK xIK xIK bOP bOP xIK xIK xIK rIK bOP bIK rIK bOP xIK xIK xIK` |
| H | 32 | `xIK xIK xIK xIK xIK xIK xIK xIK xKP xKP bKP bOP bIO rIK bIO bIO` |
| H | 48 | `bIO rIK rIK bIK xIO bOP bKP xOP bIK xIK xIK xIK xIK xIK xIK xIK` |

### 4.3 四叶库存 $(3,1)$

**定义 4.3（宏树、向量与硬集）。** 本族的宏树按下表编号；每个向量的坐标依该顺序排列。

| 索引 | 宏树 |
| --- | --- |
| 0 | `(1,(0,(0,0)))` |
| 1 | `(1,((0,0),0))` |
| 2 | `(0,(1,(0,0)))` |
| 3 | `(0,(0,(1,0)))` |
| 4 | `(0,(0,(0,1)))` |
| 5 | `(0,((1,0),0))` |
| 6 | `(0,((0,1),0))` |
| 7 | `(0,((0,0),1))` |
| 8 | `((1,0),(0,0))` |
| 9 | `((0,1),(0,0))` |
| A | `((0,0),(1,0))` |
| B | `((0,0),(0,1))` |
| C | `((1,(0,0)),0)` |
| D | `((0,(1,0)),0)` |
| E | `((0,(0,1)),0)` |
| F | `(((1,0),0),0)` |
| G | `(((0,1),0),0)` |
| H | `(((0,0),1),0)` |
| I | `((0,(0,0)),1)` |
| J | `(((0,0),0),1)` |

| 向量号 | 四值坐标 | 首阶段 | 全部符号见证 $P:q:e$ |
| --- | --- | --- | --- |
| 0 | `aaxxxxxxbaaabaarbbab` | `x1` | 0:2:1 |
| 1 | `aaxxxxxxbaaabaarrrar` | `x1` | 1:2:1 |
| 2 | `aaxxxxxxbrbbrrrbbrrb` | `b2` | 2:2:1；3:2:1 |
| 3 | `abbaarbbaabaxxxxxxaa` | `x3` | 4:3:1 |
| 4 | `arbaarrraabaxxxxxxaa` | `x3` | 5:3:1 |
| 5 | `axaabxxxxxxxxxxxxxxx` | `x4` | 7:6:1 |
| 6 | `axabaxxaxxxaxxxxxxxx` | `x4` | 6:5:1 |
| 7 | `babrbaabaaabxxxxxxxx` | `x4` | 6:4:1 |
| 8 | `bbaaaaaarbbbrbbrrrbr` | `b5` | 0:1:1；1:1:1 |
| 9 | `bbaaaaaarrrrrrrrrrrr` | `r4` | 2:1:1；3:1:1 |
| 10 | `bbxxxxxxrbbbrbbrrrbr` | `b5` | 0:1:0；1:1:0 |
| 11 | `bbxxxxxxrrrrrrrrrrrr` | `r4` | 2:1:0；3:1:0 |
| 12 | `brrbbrrrbbrbaaaaaabb` | `b6` | 4:2:1；5:2:1 |
| 13 | `brrbbrrrbbrbxxxxxxbb` | `b6` | 4:2:0；5:2:0 |
| 14 | `bxbbrxxaxxxaxxxxxxxx` | `x4` | 7:5:1 |
| 15 | `bxbbrxxxxxxxxxxxxxxx` | `x4` | 7:5:0 |
| 16 | `bxbrbxxbxxxbxxxxxxxx` | `x4` | 6:4:0 |
| 17 | `rarrraabaaabxxxxxxxx` | `x4` | 7:4:1 |
| 18 | `rbrrrbbrbbbrxxxxxxaa` | `b7` | 6:3:1；7:3:1 |
| 19 | `rbrrrbbrbbbrxxxxxxxx` | `b7` | 6:3:0；7:3:0 |
| 20 | `rrbbbbbbrrrrrrrrrrrr` | `b1` | 0:0:0；0:0:1；1:0:0；1:0:1；2:0:0；2:0:1；3:0:0；3:0:1 |
| 21 | `rrrrrrrrrrrraaaaaabb` | `r8` | 6:2:1；7:2:1 |
| 22 | `rrrrrrrrrrrrbbbbbbrr` | `b3` | 4:1:0；4:1:1；5:1:0；5:1:1；6:1:0；6:1:1；7:1:0；7:1:1 |
| 23 | `rrrrrrrrrrrrrrrrrrrr` | `r4` | 0:-1:0；0:-1:1；1:-1:0；1:-1:1；2:-1:0；2:-1:1；3:-1:0；3:-1:1；4:-1:0；4:-1:1；4:0:0；4:0:1；5:-1:0；5:-1:1；5:0:0；5:0:1；6:-1:0；6:-1:1；6:0:0；6:0:1；7:-1:0；7:-1:1；7:0:0；7:0:1 |
| 24 | `rrrrrrrrrrrrxxxxxxbb` | `r8` | 6:2:0；7:2:0 |
| 25 | `rxrrrxxbxxxbxxxxxxxx` | `x4` | 7:4:0 |
| 26 | `xaaxxbaaxxaxxxxxxxxx` | `x4` | 4:4:1 |
| 27 | `xaxxxabaxxxxxxxxxxxx` | `x4` | 5:5:1 |
| 28 | `xbaxxbrbxxaxxxxxxxxx` | `x4` | 5:4:1 |
| 29 | `xbbxxrbbxxbxxxxxxxxx` | `x4` | 4:3:0 |
| 30 | `xbxxxbrbxxxxxxxxxxxx` | `x4` | 5:4:0 |
| 31 | `xrbxxrrrxxbxxxxxxxxx` | `x4` | 5:3:0 |
| 32 | `xxxaxxxxxxxxxxxxxxxx` | `x4` | 6:6:1 |
| 33 | `xxxbxxxxxxxxxxxxxxxx` | `x4` | 6:5:0 |
| 34 | `xxxxaxxxxxxxxxxxxxxx` | `x4` | 7:7:1 |
| 35 | `xxxxbxxxxxxxxxxxxxxx` | `x4` | 7:6:0 |
| 36 | `xxxxxaxxxxxxxxxxxxxx` | `x4` | 4:5:1 |
| 37 | `xxxxxbxxxxxxxxxxxxxx` | `x4` | 4:4:0 |
| 38 | `xxxxxxaxxxxxxxxxxxxx` | `x4` | 5:6:1 |
| 39 | `xxxxxxbxxxxxxxxxxxxx` | `x4` | 5:5:0 |
| 40 | `xxxxxxxxabaabrbaabba` | `x1` | 2:3:1 |
| 41 | `xxxxxxxxabaarrraabra` | `x1` | 3:3:1 |
| 42 | `xxxxxxxxaxxxaxxbaaxa` | `x5` | 0:3:1 |
| 43 | `xxxxxxxxaxxxaxxbrbxb` | `x5` | 1:3:1 |
| 44 | `xxxxxxxxbrbbrrrbbrrb` | `b2` | 2:2:0；3:2:0 |
| 45 | `xxxxxxxxbxxxbxxrbbxb` | `x5` | 0:2:0 |
| 46 | `xxxxxxxxbxxxbxxrrrxr` | `x5` | 1:2:0 |
| 47 | `xxxxxxxxxaxxabaxxaax` | `x2` | 2:4:1 |
| 48 | `xxxxxxxxxaxxbbrxxabx` | `x2` | 3:4:1 |
| 49 | `xxxxxxxxxbxxbrbxxbbx` | `x2` | 2:3:0 |
| 50 | `xxxxxxxxxbxxrrrxxbrx` | `x2` | 3:3:0 |
| 51 | `xxxxxxxxxxxxaabxxxax` | `x2` | 3:5:1 |
| 52 | `xxxxxxxxxxxxbbrxxxbx` | `x2` | 3:4:0 |
| 53 | `xxxxxxxxxxxxxaxxxxxx` | `x4` | 2:5:1 |
| 54 | `xxxxxxxxxxxxxbxxxxxx` | `x4` | 2:4:0 |
| 55 | `xxxxxxxxxxxxxxaxxxxx` | `x9` | 3:6:1 |
| 56 | `xxxxxxxxxxxxxxbxxxxx` | `x9` | 3:5:0 |
| 57 | `xxxxxxxxxxxxxxxabaxa` | `x5` | 1:4:1 |
| 58 | `xxxxxxxxxxxxxxxaxxxx` | `x4` | 0:4:1 |
| 59 | `xxxxxxxxxxxxxxxbrbxb` | `x5` | 1:3:0 |
| 60 | `xxxxxxxxxxxxxxxbxxxx` | `x4` | 0:3:0 |
| 61 | `xxxxxxxxxxxxxxxxaxxx` | `xA` | 1:5:1 |
| 62 | `xxxxxxxxxxxxxxxxbxxx` | `xA` | 1:4:0 |
| 63 | `xxxxxxxxxxxxxxxxxxxx` | `x4` | 0:4:0；0:5:0；0:5:1；0:6:0；0:6:1；0:7:0；0:7:1；0:8:0；0:8:1；1:5:0；1:6:0；1:6:1；1:7:0；1:7:1；1:8:0；1:8:1；2:5:0；2:6:0；2:6:1；2:7:0；2:7:1；2:8:0；2:8:1；3:6:0；3:7:0；3:7:1；3:8:0；3:8:1；4:5:0；4:6:0；4:6:1；4:7:0；4:7:1；4:8:0；4:8:1；5:6:0；5:7:0；5:7:1；5:8:0；5:8:1；6:6:0；6:7:0；6:7:1；6:8:0；6:8:1；7:7:0；7:8:0；7:8:1 |

| 硬集号 | 宏树索引集 |
| --- | --- |
| 1 | 3,4,5,6,7 |
| 2 | A,B,F,G,J |
| 3 | D,E,F,G,H |
| 4 | E,G,I,J |
| 5 | A,B,D,E,I |
| 6 | 3,4,B,I,J |
| 7 | 5,6,8,9,A |
| 8 | 6,7,9,B |
| 9 | D,G,H,I,J |
| A | E,F,H,I,J |

| 硬集号 | 起始向量号 | 依序十六个第二阶段项 |
| --- | --- | --- |
| 1 | 0 | `x34 x34 x34 b67 r56 x56 x56 b47 a-- a-- x34 x34 b34 b34 x56 x56` |
| 1 | 16 | `b47 r34 b56 b56 b34 r34 r34 r34 r34 r34 x34 x34 b57 b67 b57 r56` |
| 1 | 32 | `x45 x45 x35 x35 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34` |
| 1 | 48 | `x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34` |
| 2 | 0 | `bGJ rFG bAB xFG xFG xAB xAF xFG bAB rAB bAB rAB bBJ bBJ xAF xAB` |
| 2 | 16 | `xAF xFG xFG xFG rAB rAB bFG rAB rAB xAF xBF xAB xBF xBF xAB xBF` |
| 2 | 32 | `xAB xAB xAB xAB xAB xAB xAB xAB a-- a-- xAB bFJ bAB bGJ rFG xAB` |
| 2 | 48 | `xAB xAB xAB xAB xAB xAB xAB xAB xAB xAB xAB bFJ xAB xAB xAB xAB` |
| 3 | 0 | `bGH rFG bFG xDE xDE xDE xDE xDE bDE rDE bDE rDE a-- xDE xDE xDE` |
| 3 | 16 | `xDE xDE xDE xDE rDE a-- bDE rDE xDE xDE xDE xDE xDE xDE xDE xDE` |
| 3 | 32 | `xDE xDE xDE xDE xDE xDE xDE xDE bEH rDE xDE bFH bFG bGH rFG xFG` |
| 3 | 48 | `xFG bEH rDE xFG xFG xEF xEF xDF xDF xDE xDE bFH xDE xDE xDE xDE` |
| 4 | 0 | `bGJ rGJ bGJ xEG xEG xEG xEG xEG bEI rEG bEI rEG bIJ bIJ xEG xEG` |
| 4 | 16 | `xEG xEG xEG xEG rEG bIJ bEG rEG bIJ xEG xEG xEG xEG xEG xEG xEG` |
| 4 | 32 | `xEG xEG xEG xEG xEG xEG xEG xEG bEI rEI xEI xEI bGJ bGJ rGJ xGJ` |
| 4 | 48 | `xGJ bEI rEI xGJ xGJ xEG xEG xGI xGI xEI xEG xEI xEG xEI xEI xEG` |
| 5 | 0 | `a-- a-- bAB xDE xDE xAB xAD xDE bAB rAB bAB rAB bBI bBI xAD xAB` |
| 5 | 16 | `xAD xDE xDE xDE rAB rAB bDE rAB rAB xAD xBD xAB xBD xBD xAB xBD` |
| 5 | 32 | `xAB xAB xAB xAB xAB xAB xAB xAB bEI rDE xAB xAB bAB xAB xAB xAB` |
| 5 | 48 | `bDI bEI rDE xAB bDI xAB xAB xAB xAB xAB xAB xAB xAB xAB xAB xAB` |
| 6 | 0 | `x34 x34 bBJ a-- a-- xBI xIJ b4B bBI rBI bBI rBI b34 b34 xIJ xBI` |
| 6 | 16 | `b4B r34 r34 r34 b34 bIJ r34 r34 bIJ r34 x34 x34 x34 x34 x34 x34` |
| 6 | 32 | `x4B x4B x3B x3B x34 x34 x34 x34 x34 x34 x34 x34 bBJ x34 x34 x34` |
| 6 | 48 | `x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34 x34` |
| 7 | 0 | `x56 x56 b8A b6A r56 x56 x56 a-- b9A r89 b9A r89 b89 b89 x56 x56` |
| 7 | 16 | `x56 a-- b56 b56 b56 r56 r56 r56 r56 x56 x89 x89 x89 b6A x89 r56` |
| 7 | 32 | `x56 x56 x56 x56 x68 x68 x58 x58 x56 x56 x56 x56 b8A x56 x56 x56` |
| 7 | 48 | `x56 x56 x56 x56 x56 x56 x56 x56 x56 x56 x56 x56 x56 x56 x56 x56` |
| 8 | 0 | `x67 x67 x67 b67 r67 x67 x69 b7B b9B r9B b9B r9B b9B b9B x69 x67` |
| 8 | 16 | `b7B b7B b69 b69 b67 r67 r67 r67 r67 b7B x9B x9B x9B b67 x9B r67` |
| 8 | 32 | `x67 x67 x67 x67 x67 x67 x79 x79 x67 x67 x67 x67 x67 x67 x67 x67` |
| 8 | 48 | `x67 x67 x67 x67 x67 x67 x67 x67 x67 x67 x67 x67 x67 x67 x67 x67` |
| 9 | 0 | `bGH rGH bGJ xDG xDG xDG xDG xDG bDI rDG bDI rDG bIJ bIJ xDG xDG` |
| 9 | 16 | `xDG xDG xDG xDG rDG bIJ bDG rDG bIJ xDG xDG xDG xDG xDG xDG xDG` |
| 9 | 32 | `xDG xDG xDG xDG xDG xDG xDG xDG bHI rDI xDI bHJ bGJ bGH rGH xGJ` |
| 9 | 48 | `bDI bHI rDI xGH bDI xGH xGH xDG xDG xDI xDG bHJ xDG xDH xDH xDG` |
| A | 0 | `bHJ rFH bFJ xEF xEF xEF xEF xEF bEI rEF bEI rEF bIJ bIJ xEF xEF` |
| A | 16 | `xEF xEF xEF xEF rEF bIJ bEF rEF bIJ xEF xEF xEF xEF xEF xEF xEF` |
| A | 32 | `xEF xEF xEF xEF xEF xEF xEF xEF bEH rEI xEI bFH bFJ bHJ rFH xFJ` |
| A | 48 | `xFJ bEH rEI xFH xFH xEF xEF xFH xFH xEI xEH bFH xEH xEF xEF xEF` |

## 5. 从原空历史到同一固定正源的下界

**定义 5.1（全四值相容与保留阶段）。** 固定一个四叶族或其固定上下文嵌入族 $\mathcal F$。对实际历史 $\mathcal H$，定义

$$
\operatorname{Comp}(\mathcal H)
=\{V\in\mathcal F:\forall (u,y)\text{ 出现在 }\mathcal H, r_V(u)=y\}.
\tag{5.1}
$$

重复项依原时间顺序保留。证明中维护非空子集 $S\subseteq\operatorname{Comp}(\mathcal H)$，各步 $S$ 嵌套；不要求它等于整个相容族。阶段数是已经强制得到的、不同核心地址上的非 $\alpha$ 回复数，最高取三。阶段零保留全族；阶段一保留首阶段硬集；阶段二保留第二阶段指定的不同源对；阶段三以后选一个相容源作完整真实运行。

**定理 5.2（四叶核心的有限因果障碍）。** 对任意 $d\ge3$ 及上述任一四叶族，任何在原同组成竞争域上正确且逐源有限终止的确定策略，从共同空历史出发，都有一棵固定有限正源，其完整真实终端至少包含三个不同地址上的非 $\alpha$ 实际回复。该断言允许重复请求、全部四值及任意有限原深度。

证明。固定策略 $\pi$。以下只构造一条有限历史及相容正源的嵌套集合，最后将整条历史在一棵固定源上重放。

初始历史为空，$S=\mathcal F$。若下一动作请求已出现地址，则它在 $S$ 的全部成员上都有先前的真实回复。返回该回复、把这次请求和回复再记入历史，$S$ 与阶段均不变。它增加一个实际动作，但没有新的不同地址费用；也不再次读取证书项。

第一次新地址 $u$ 的真实联合向量由定理 3.2 落在某行 $f_j$。取该行首阶段项 `yH`，回复真正的 $y\ne\alpha$，将 $S$ 缩为硬集 $S_H$。式 (3.5) 保证其每个成员都给出该回复，故它们匹配新增历史；该新地址是第一枚非 $\alpha$ 收费地址。初始族包含不同正源，在此之前策略不能返回：正确拒绝与任一相容正源矛盾；正确接受则会有一色完整前沿，由 §2 的唯一性排除另一相容正源。

阶段一时，固定这一硬集。在任何下一新地址 $u$ 上读取对应的第二阶段项。若为 `a--`，整个 $S_H$ 在该地址真正回复 $\alpha$；记入实际回复并保持 $S_H$、阶段一。若为 `yik`，回复该真实非 $\alpha$ 值，保留 $\{i,k\}$。两源索引不同、均属 $S_H$，且给出同一回复，故仍是嵌套非空相容集；这是第二枚不同的非 $\alpha$ 收费地址。所有历史中的 $\alpha$ 请求同样实际收费，只是不增加此阶段数。

阶段二时保留一对不同正源。对下一新地址，若两者均回复 $\alpha$，记入该真实 $\alpha$ 并保持源对。否则至少一源给出非 $\alpha$；选择这样的真实回复 $y$，保留源对中回复 $y$ 的非空桶。这是第三枚不同非 $\alpha$ 地址，保留桶可为单源。此处不需要额外有限证书，因为直接在这两棵实际树的四值读数中作选择。

第三枚出现之前，保留集始终至少含两棵不同正源。若策略在某个构造历史返回假，任何相容正源的历史重放都会错误拒绝。若返回真，固定一棵相容正源 $V$，相同历史必是它的真实终端；式 (2.3) 使请求集含 $V$ 的某一完整颜色前沿，第二棵相容正源匹配此前沿，必须等于 $V$，矛盾。因此第三枚出现之前只能继续原策略选择的实际查询动作。

还须证明不能无限查询而一直没有第三枚。对有限族中每个 $V_i$，令 $m_i$ 是 $\pi$ 从空历史在其上的真实终端查询动作数，包括重复；逐源有限终止给出有限的

$$
m_* = \max_i m_i.
\tag{5.2}
$$

若构造历史已有 $m_*$ 次查询却仍未到第三枚，选任一保留源 $V_i$。全四值相容及确定性逐动作重放，使 $\pi$ 在 $V_i$ 上也走完该相同查询前缀。它须在第 $m_i\le m_*$ 次查询后返回；构造历史也必须在该处返回，和前一段的不能返回相矛盾。若返回恰在第 $m_*$ 次查询后，同样在这个相同历史上矛盾。因此第三枚在有限动作内出现。

在其出现时从非空保留桶中选 $V$。它匹配此前全部字面请求和四值回复。由共同空初始化及历史选择器的确定性，在这**同一棵 $V$** 上重放全部前缀，随后继续 $\pi$ 的真实运行。合法性保证余下有限接受；前缀的三个非 $\alpha$ 地址仍在完整终端的请求集内。

嵌套集合的选择是存在性证明，不是实际执行中的来源切换；没有将各阶段归属于不同实际树。所有回复都是选定最终 $V$ 的真实回复，也没有把逻辑推出的叶加入历史。该论证处理任意有限原词，故只限制到策略实际允许的深度时仍成立。□

**定理 5.3（混色全域的固定源下界）。** 对每个 $d=3k$、$k\ge1$、$a,b>0$、$n=a+b\ge4$、$h\ge H=d+n-1$ 及每个原合法策略 $\pi$，存在一棵 $V\in\mathcal P$，使其完整真实终端满足

$$
|Q(T_\pi(V))|\ge A+3.
\tag{5.3}
$$

证明。先按库存选一个不超过原两色库存的四叶核心：若 $a\ge3$，取 $(3,1)$；否则若 $b\ge3$，取 $(1,3)$；其余情形因 $a,b>0,n\ge4$ 只能是 $a=b=2$，取 $(2,2)$。这些分支覆盖全部参数。

若 $n=4$，直接使用对应的全部四叶宏树。若 $n>4$，扣除核心库存后的两色计数非负且总数 $n-4\ge1$。取一棵具有该剩余组成的固定非空完整宏树 $R$，将每个核心 $T_i$ 放入同一上下文 $(T_i,R)$，再对整体施加 $\rho^d$。所得有限族为

$$
V_i=\bigl(\rho^dT_i,\rho^dR\bigr),
\tag{5.4}
$$

全都有准确组成 $C$，且由替换单射互不相同。$R$ 可以是任何一个固定的该组成完整树；它不随回复改变，也不告知实际策略。

对请求 $Lu$，实际端点递归给出

$$
r_{V_i}(Lu)=r_{\rho^dT_i}(u).
\tag{5.5}
$$

故可在证明中用核心的书向量和阶段规则选回复及保留集。策略请求的仍是完整原词 $Lu$，没有另发 $u$，也没有实际剥离地址前缀的额外权限。映射 $u\mapsto Lu$ 单射，核心的三枚不同收费地址因此变成三枚不同原地址。

不以 $L$ 开头的词或者是孔上方的根，或者进入固定兄弟 $\rho^dR$，包括穿过其叶后的词。它们在全部 $V_i$ 上回复相同：如实记录并收费，保持当前保留集和核心阶段。即使这些外部回复为非 $\alpha$，也不拿来提前凑核心的三单位。重复原词保留其先前回复、历史次序及原阶段。

每个被保留的全源匹配整条原历史；阶段三之前仍至少有两个不同全正源，不能接受或拒绝。用这个固定有限全源族的逐源终端长度之最大值，完全按定理 5.2 的有限重放论证，可知三个核心非 $\alpha$ 地址有限出现，随后选一棵相容全源 $V$，从空历史重放此前全部实际动作并继续它的真实有限终端。外部查询、重复和核心查询都属于同一固定 $V$ 的完整运行。

这些全宏树都有 $n$ 片叶，宏叶深度至多 $n-1$；替换后的正源高度至多 $H$。下界书本身已经处理任意有限深词，所以对任意 $h\ge H$ 的策略实际请求取用它，不改变原深度权限；$h=\infty$ 也包含在内。没有缩小高负源的竞争域。

设最终真实终端为 $T$。其前缀已经包含三个不同地址，实际回复均非 $\alpha$。在这个同一源的完整终端上使用式 (2.3)，保留两个分支：

若 $\mathcal A(V)\subseteq Q(T)$，$A$ 枚实际 $\alpha$ 地址与这三枚非 $\alpha$ 地址互不重合，故 $|Q(T)|\ge A+3$。

若 $\mathcal A(V)\nsubseteq Q(T)$，则 $\mathcal B(V)\subseteq Q(T)$，因此

$$
|Q(T)|\ge B\ge A+n\ge A+4\ge A+3.
\tag{5.6}
$$

第二分支只使用 $B$ 个实际收费地址，不把核心三单位再次加到 $B$；其中也包括 $d=3$ 的 $\beta$ 前沿路径。没有拼接不同来源的独立极值，也没有强制所有终端都补全 $\alpha$。对每个 $\pi$ 得到一棵这样的 $V$，再取正源最坏值及策略最小值，即得 $D_h\ge A+3$。□

## 6. 两种真正付费的局部诊断

**定义 6.1（原诊断词与模式）。** 对 $t\ge2$ 令 $z_t=L^{t-2}R$。对内部假设描述中待处理的宏节点地址 $p$，两种诊断均请求一个原字面地址：

$$
q_1(p)=pRz_{d-1},\qquad
q_2(p)=pRz_{d-2}.
\tag{6.1}
$$

$q_1$ 在所有 $d=3k\ge3$ 可用；$q_2$ 只在 $d=3k\ge6$ 可用。$d=3$ 时 $z_1$ 未定义，不能采用 $q_2$。模式由公开参数一次选定：$d=3$ 用 $q_1$；$d\ge6$ 时若 $a\le b$ 用 $q_1$，若 $a>b$ 用 $q_2$。每次诊断都是实际付费请求。

**定理 6.2（诊断表与原四值分类）。** 固定正源 $V=\rho^d(T)$，若 $p$ 是其同一前源 $T$ 的实际宏节点，则下表精确成立。

| 宏节点类型 | $q_1(p)$ 的实际回复 | $q_2(p)$ 的实际回复（仅 $d\ge6$） |
| --- | --- | --- |
| $\alpha$ 叶 | $\varnothing$ | $\alpha$ |
| $\beta$ 叶 | $\alpha$ | $\beta$ |
| 分支 | $\beta$ 或 $\mathsf{br}$ | $\mathsf{br}$ |

原历史中 $\beta$ 和 $\mathsf{br}$ 仍是两个不同回复，即使 $q_1$ 的控制分类将它们都解释为宏分支。$q_2$ 的缺失回复不属于任何正宏节点类型，必须拒绝。

证明。式 (2.2) 给出 $w(z_t)=t$，$z_t$ 末字母为 $R$，故它是 $X_t$ 的实际 $\alpha$ 地址。若宏节点是 $\alpha$，其替换块为 $X_d$，右子块是 $X_{d-2}$；$d\ge6$ 时，$q_1$ 在它内查询权重 $d-1$ 的 $z_{d-1}$，已经超过该块的叶权重，回复缺失。$d=3$ 时右子块是 $X_1=\beta$，$z_2=R$ 穿过该叶，同样真正回复缺失。若宏节点是 $\beta$，右子块为 $X_{d-1}$，$z_{d-1}$ 正是其 $\alpha$ 地址。

若宏节点是分支 $(S,W)$，查询 $pR$ 后的子树为 $\rho^d(W)$。对任意非空宏树 $W$，权重至多 $d-2$ 的词在 $\rho^d(W)$ 中均给分支，权重恰 $d-1$ 的词给 $\beta$ 或分支。对此按 $W$ 归纳：叶的两种替换块用式 (2.2)；宏分支上的空词就是分支，非空词进入对应宏子树并扣除首字母的正权重，余词落在至多 $d-2$ 的分支范围。于是 $z_{d-1}$ 的权重 $d-1$ 给表中的 $\beta$ 或分支。

$q_2$ 在宏 $\alpha$ 的右子块 $X_{d-2}$ 上查询 $z_{d-2}$，回复 $\alpha$；在宏 $\beta$ 的右子块 $X_{d-1}$ 上以权重 $d-2$ 查询，回复 $\beta$；在宏分支的右子树 $\rho^d(W)$ 上权重 $d-2$，回复分支。这一推导要求 $d-2\ge2$，本参数域即 $d\ge6$。两种诊断词都是实际 $L/R$ 词，未使用 §3 的符号超集作为操作。□

## 7. 有守卫的前序取得与上界

**定义 7.1（原历史上的确定取得策略）。** 模式固定为定义 6.1 的一种。策略保留自己真正取得的按时序四值历史，以及仅由该历史和公开参数计算的内部假设宏描述、待处理地址列表及三个剩余库存计数。

初始历史为空。因 $n\ge4$，任何正宏树的根为分支；把这个根作为公开假设模板，待处理列表取 $(L,R)$，剩余 $\alpha$、$\beta$、分支计数取

$$
x=a,\qquad y=b,\qquad j=n-2.
\tag{7.1}
$$

这里不请求根，不向历史伪造根回复。待处理列表按前序处理：取首项 $p$，分类为分支时用 $pL,pR$ 依次替换它，分类为叶时删除它。

每步先检查计数非负、所构造描述和列表的前序一致性以及所有待处理宏地址深度至多 $n-1$。请求诊断前检查所选 $q_m(p)$ 满足原上限 $|q_m(p)|\le h$。对失败的任一检查，有限返回假。

若待处理列表为空，只有三计数全部为零才进入补查，否则拒绝。若列表非空且 $x+y=1,j=0$，由库存和列表不变量只剩一项；以 $(x,y)=(1,0)$ 或 $(0,1)$ 预测其叶色，删除该项并减相应计数，不伪造取得回复。除此情形，对首项 $p$ 实际请求所选诊断词并记录原四值：

| 模式 | 真实回复 | 内部宏分类及更新 |
| --- | --- | --- |
| $q_1$ | $\varnothing$ | $\alpha$ 叶，须 $x>0$，然后 $x\gets x-1$ |
| $q_1$ | $\alpha$ | $\beta$ 叶，须 $y>0$，然后 $y\gets y-1$ |
| $q_1$ | $\beta$ | 分支，须 $j>0$，然后 $j\gets j-1$ |
| $q_1$ | $\mathsf{br}$ | 分支，须 $j>0$，然后 $j\gets j-1$ |
| $q_2$ | $\alpha$ | $\alpha$ 叶，须 $x>0$，然后 $x\gets x-1$ |
| $q_2$ | $\beta$ | $\beta$ 叶，须 $y>0$，然后 $y\gets y-1$ |
| $q_2$ | $\mathsf{br}$ | 分支，须 $j>0$，然后 $j\gets j-1$ |
| $q_2$ | $\varnothing$ | 立即拒绝 |

相应库存为零时分类拒绝，不作负数更新。分类为分支还要求 $|p|\le n-2$，从而新插入的子地址深度至多 $n-1$。每次更新重新检查列表、描述及计数；拒绝动作没有附加查询。控制分类不会修改原四值历史。

若最终列表空且计数全零，得到完整宏候选 $T_0$，先核对它确有 $n$ 叶、组成 $(a,b)$，令 $V_0=\rho^d(T_0)$。按固定左到右顺序处理 $\mathcal A(V_0)$。对其中已经真正请求过的地址，只读取其历史中真实缓存：若回复不是 $\alpha$，拒绝；若为 $\alpha$，该地址已收费且已有真实证据。对尚未请求的地址，先检查原深度上限，再**实际请求**，记录回复并要求为 $\alpha$。所有前沿项通过才返回真。

根模板、末叶预测、待处理列表、候选的数学前沿均是内部控制描述，不是取得报告。真正缓存只能来自策略已经实际请求的原字面地址；逻辑预测不得记入缓存。

**定理 7.2（全来源有限终止、正源重建及高负源正确性）。** 定义 7.1 的策略对任意 $h\ge H$ 合法。它在每个 $U\in\mathcal T_C$ 上有限终止、返回正确，所有请求均在原深度上限内。对每个固定正源 $V=\rho^d(T)$，解析恰好得到它的同一宏树 $T$，随后实际补查完整 $\alpha$ 前沿。

证明。先不假定被查询的 $U$ 是正源。令 $\ell=x+y$，$s$ 是待处理列表项数。每个尚未拒绝的解析状态满足

$$
\ell-j=s,\qquad x,y,j\ge0.
\tag{7.2}
$$

初始两边都是二。叶分类减 $\ell$ 一且删去一个待处理项，分支分类减 $j$ 一且一个项换为两个项，故等式保持；末叶预测同样按叶更新。计数守卫保证非负。列表是已构造假设描述的未决子槽，首项选择和子项插入保持前序。它们不宣称是负源的真实宏分解。

若 $\ell=1,j=0$，式 (7.2) 强制 $s=1$，非负整数库存且 $x+y=1$ 唯一指定末叶颜色，故预测有确定定义。若列表空而库存未全耗尽，拒绝；若全耗尽且列表空，假设根及所有子槽已组成一棵完整有序树，其两色叶数分别为 $a,b$，分支数为 $1+(n-2)=n-1$，没有未填槽。

每次实际诊断分类或末叶预测都把

$$
x+y+j
\tag{7.3}
$$

减一，初值为 $2n-2$。各守卫或不可能回复立即拒绝；因此不论 $U$ 多高，解析都在有限步内拒绝或形成有限候选。缓存、列表和计数的更新没有来源外的回复，控制计算可从完整原历史确定重建。

再固定一棵正源 $V=\rho^d(T)$，从空历史归纳。初始公开根模板正是 $T$ 的根；待处理项恰为其尚未处理的前序子树根，库存等于这些子树的剩余两色叶数和分支数。定理 6.2 给出首项真实诊断的正确宏分类，相应更新将该同一子树的根从库存和列表中处理掉。分支产生它的两个真实宏孩子，叶删除该真实宏叶。由此不变量沿固定 $T$ 保持，不会因库存不足、错误回复或描述不一致拒绝。

当只剩一叶且无分支时，待处理子树必须是那一真实叶，库存指定其真正颜色。故末叶预测正确，最终候选 $T_0=T$。这是在一棵固定正源上的归纳，并未随回复重新选择前源。

深度须同时约束任意负解析。宏地址守卫保证诊断的 $|p|\le n-1$；$q_1$ 固定后缀长度为 $d-1$，$q_2$ 为 $d-2$，故每次实际诊断满足

$$
|q_1(p)|\le d+n-2=H-1,
\qquad |q_2(p)|\le d+n-3<H.
\tag{7.4}
$$

分支守卫使插入的宏孩子仍在深度 $n-1$ 内。对正 $T$，任何 $n$ 叶完整宏树本来即满足这些深度事实，所以守卫不拒绝正例。对负 $U$，守卫依内部描述执行，绝不假定真实 $U$ 具有正源高度。

一个完成的候选 $T_0$ 有 $n$ 叶；其替换 $V_0$ 具有组成 $C$ 和高度至多 $H$，所以它的全部 $\alpha$ 前沿请求均满足原上限。前沿有限，补查有限；实际 $U$ 即使高于 $H$ 也只被询问这些合法端点。

若补查接受，则每个 $u\in\mathcal A(V_0)$ 都在原历史中有真实回复 $\alpha$：旧项来自真实缓存，新项来自本次真正请求，没有预测项。于是 $U$ 匹配 $V_0$ 的完整 $\alpha$ 前沿。因 $U\in\mathcal T_C$，§2 的同组成前缀树唯一性强制 $U=V_0$，故 $U$ 是正源。该唯一性覆盖全部高负竞争者，不能被负树在未查深处藏入额外子树所绕过：每个未占子槽已经受总叶库存约束。

对正源，解析已得到 $V_0=V$，已请求的前沿项缓存均为真实 $\alpha$，新请求也全返回 $\alpha$，故接受。负源或者解析拒绝、或者缓存不符、或者新前沿回复不符；它不能通过完整前沿。因此策略在整个原竞争域上正确、有限终止。

最后，模式、根模板、前序列表、库存、候选、缓存读取、前沿顺序和返回条件都是公开参数与该策略原历史的确定函数。任意相同实际历史前缀导致同一下一原词；对任一固定 $U$，逐动作原读数重放正是这条有限运行。策略的定义不取得免费来源身份，也不需要预查祖先。□

**定理 7.3（逐源不同地址费用上界）。** 定义 7.1 的策略在每棵固定正源 $V$ 上满足

$$
|Q(T_\pi(V))|
=A+\#\{\text{非 }\alpha\text{ 诊断地址}}
\le A+n-2+c_d(a,b).
\tag{7.5}
$$

因此定理 1.4 的上界在每个 $h\ge H$ 成立。

证明。固定正源及其真实重建宏树。完整宏树有 $n-1$ 个分支和 $n$ 片叶；根与最后一叶是内部预测，没有诊断请求。其余宏节点至多 $2n-3$ 个，各诊断一个原地址。

所有诊断用同一模式的固定非空后缀 $s_m$，地址形如 $p s_m$。两个不同宏节点 $p,p'$ 若诊断地址相同，则右消去同一后缀得到 $p=p'$，矛盾。宏节点在前序列表中只处理一次，故诊断地址无重复。这一单射不要求 $p$ 是已取得的真实端点报告；它只用于算实际发出的原字面词。

非根宏分支至多 $n-2$ 个，两种模式在它们上的回复都非 $\alpha$。模式 $q_1$ 中宏 $\alpha$ 叶给缺失，是非 $\alpha$ 诊断，数目至多 $a$；宏 $\beta$ 叶给真实 $\alpha$。模式 $q_2$ 中宏 $\beta$ 叶给 $\beta$，数目至多 $b$；宏 $\alpha$ 叶给真实 $\alpha$。末叶无诊断，故这些是上界而不要求每个颜色库存都被诊断。

因此 $d=3$ 选择合法 $q_1$，非 $\alpha$ 地址至多 $n-2+a$；$d\ge6$ 选择较少库存对应的模式，至多 $n-2+\min(a,b)$。$\beta$、分支、缺失各自按实际原回复计入；控制分类未将任何一项费用抹去。

在同一固定正源上，诊断回复为 $\alpha$ 的地址是真正的 $\alpha$ 叶，因而属于 $\mathcal A(V)$。补查过程只请求其中尚未实际请求过的地址；已请求者逐一查真实缓存并通过。补查后不同的实际 $\alpha$ 请求地址集合恰为 $\mathcal A(V)$，基数 $A$。所有其余地址恰是先前不同的非 $\alpha$ 诊断地址。两集合按原回复互不相交，所以得到式 (7.5) 的等式。

缓存避免再发同一地址，没有让首次 $\alpha$ 诊断免费，也没有把内部预测的末叶或根当取得证据。即使某诊断直接命中了最终前沿，该地址仍首次付费，仅在补查中不再重复支付。全运行的计费对象一直是实际请求词的集合。对正源取最大值，再在全部合法策略中取最小值，得所述上界。□

## 8. 部分界的边界与未解目标

**命题 8.1（示例区间）。** 在 $(a,b,d)=(2,2,3)$，对每个 $h\ge6$ 有

$$
9\le D_h(2,2;3)\le10.
\tag{8.1}
$$

这是式 (1.5) 的部分界示例，不给出准确值或最佳已知界。

证明。$F_2=1,F_3=2,F_4=3$，故 $A=6,B=10,n=4,H=6$。下界为 $A+3=9$，合法 $q_1$ 模式的上界为 $A+n-2+a=10$。两整数端点不同，部分界本身不能指定准确值。□

**定义 8.2（复用与新推导的数学边界）。** 本卷直接使用原定义 57.1、引理 57.2、定理 57.3、57.4、57.7，以及前述实际树读数、历史、同组成前沿与字面上下文供应。一般证书复杂度、确定决策树及前序解析是成熟中间结构；通用有限递推、代数、深度、归一化及其他数论工具不被重新包装为独立新成果。

本卷承重的新组合关系是：完整四叶混色联合四值书的两阶段活候选闭包及其固定上下文、有限同源因果下界；两种原付费诊断与带库存守卫解析、真正缓存前沿补查所给的逐源非 $\alpha$ 地址上界。其证据是上文普通证明和完整有限坐标等式；既有供应的名称不是对本卷新增命题的自动证明。

有关证书与敏感交换的成熟背景见 [ActualImageAddressCertificate 定理 1.9、1.10 的来源说明](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.md)。这些来源保持其原领域与费用前提，不能仅凭一般决策树结论得出式 (1.5)。本卷的树费用关系为仓内推导，不宣称全局原创或已穷尽相关定理。

**定义 8.3（一般混色准确费用问题）。** 在定义 1.1–1.3 的原混色域内，求全部参数的准确 $D_h$ 仍为未解目标。令 $E_h$ 为[原定义 57.6](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md#57-uniform-paid-acquisition-of-actual-image-certificates-at-exact-composition)的正族加权识别费用；[原定理 57.7](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md#57-uniform-paid-acquisition-of-actual-image-certificates-at-exact-composition)只在适当 $B$ 阈值下给出 $D_h=A+E_h$，并不提供无条件等式。本卷下界保留 $\beta$ 终端分支，上界构造选择 $\alpha$ 补查；这两个用途不删除原目标中的 $\beta$ 前沿路线，尤其不删除 $d=3$ 的路线。

**定义 8.4（一般全公因数查询目标）。** 原一般目标的来源为自然数来源，包含零及混合零；要求正时间的完整最大公因数读数，每次查询执行均收费，包括重复，从空历史作确定适应，逐源有限确定所有未来。其 $H1$、素数 $2,5$、指数一、未知内容、非满轨道、饱和、停滞与退出秩以及 WSS 的原适用范围全部保留。树的不同实际地址费用与该目标每次执行收费是不同目标，式 (1.5) 不确定该一般目标的答案。

**定义 8.5（同一实际整数的严格预算目标）。** 原同一整数目标保留

$$
N^*=1+F_r g^*,\qquad r\ge7\text{ 为素数},
\qquad
C^*+H^*<\left(\frac{\log\log N^*}{\log\log A}\right)^s.
\tag{8.2}
$$

$F_r$ 不假定为素数。必须在这个**同一实际 $N^*$**、原连续窗口和分离分母上处理全部素数幂及全部约数，并满足原严格不等式。式 (8.2) 中的 $A,s,C^*,H^*$ 保持该原数论目标的含义，不与本卷组成计数 $A$ 混用。树部分界没有支付其任何预算；一般混色准确值、一般全公因数目标、同一整数严格预算以及原 Robin、黎曼假设和长期研究目标均保留为未解，不由本卷结算。

## 8.99 追加锚（本行以下为增补区）

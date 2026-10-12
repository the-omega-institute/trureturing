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


## 9. 两个四叶混色格的显式证书

**定义 9.1（两格的完整证书入口）。** 在本卷定义1.1–1.3的原合同下，[四叶显式证书卷定理5.1](FIB_ATOM_MIXED_FOUR_LEAF_EXPLICIT_CERTIFICATES.md#5-具体证书有效性的普通证明与精确费用)给出 $(a,b,d)=(2,2,3),(3,1,3)$ 的完整原矩阵、诊断桶、逐边界、全部两色前沿及真实付费运行，并证明其具体上界有效。对每个 $h\ge6$ 含无穷，证书费用分别为9、8；与本卷定理5.3的固定源下界配合得到 $D_h(2,2;3)=9$、$D_h(3,1;3)=8$。本卷命题8.1的区间因而在该格取端点9。

实际取得的接口直接使用[原定理57.7](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md#57-uniform-paid-acquisition-of-actual-image-certificates-at-exact-composition)，具体有效性与有限数据集中在所引证书卷，不在此重复表或证明。本卷定理5.3仍是下界供应；定义8.3–8.5的一般混色、GeneralH与同一实际整数严格预算保持其原量词和未解范围。

## 9.99 追加锚（本行以下为增补区）


## 10. 多核心在同一真实历史中的实际地址下界

**定义 10.1（原合同、核数与全四值历史相容）。** 采用定义 1.1–1.3 的字面树合同。实际来源 $U$ 是一棵未知、有限、非空的完整有序二叉树；叶标签为 $\alpha,\beta$，每个分支有两个非空的有序子树。括号、左右次序和每个出现均属于来源。替换逐分支作用：

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=(\beta,\alpha),\qquad
\rho(S,T)=(\rho S,\rho T),\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

公开参数为整数 $k\ge1$、$d=3k$、$a,b>0$ 和 $n=a+b\ge4$。用 $F_0=0,F_1=1,F_{i+2}=F_{i+1}+F_i$ 记 Fibonacci 数，令

$$
\begin{aligned}
C=(A,B)&=M^d(a,b)
=\bigl(F_{d-1}a+F_db,\ F_da+F_{d+1}b\bigr),\\
H&=d+n-1,\qquad
q=\min\left\{a,b,\left\lfloor\frac n4\right\rfloor\right\}.
\end{aligned}
$$

$\mathcal T_C$ 包含组成恰为 $(A,B)$ 的所有有限非空完整有序字面树，正域为 $\mathcal P=\mathcal T_C\cap\operatorname{im}\rho^d$，负域为 $\mathcal T_C\setminus\mathcal P$。目标是对整个 $\mathcal T_C$ 判定成员身份。正源高度至多 $H$；负域保留全部同组成完整树，不以这个正源高度筛选。

给定任意 $h\in\mathbb N\cup\{\infty\}$、$h\ge H$，一次原动作可以直接请求任意有限 $L/R$ 词 $u$ 的端点，条件只有 $|u|\le h$，没有祖先查询要求。空词 $\varepsilon$ 请求根。对同一棵固定 $U$，读数 $r_U(u)$ 是端点叶的标签 $\alpha$ 或 $\beta$、端点分支的 $\mathsf{br}$，或穿过叶的缺失 $\varnothing$。实际历史

$$
\mathcal H_m=((u_1,y_1),\ldots,(u_m,y_m)),\qquad y_i=r_U(u_i)
$$

保留全部四值、实际原词、时间顺序和重复。确定策略 $\pi$ 从共同、来源无关的初始化及空取得历史出发，只依公开参数与自己的这条历史选择下一合法原词或布尔返回。合法性要求对每个 $U\in\mathcal T_C$ 正确且逐源有限终止。

令 $T_\pi(U)$ 为完整真实终端历史，$Q(T)=\{u:(u,y)\text{ 出现在 }T\}$。原主费用是不同实际请求地址数：

$$
\operatorname{paid}(T)=|Q(T)|,\qquad
D_h(a,b;d)=\min_{\pi\text{ 原合法}}\max_{V\in\mathcal P}|Q(T_\pi(V))|.
$$

无合法策略时值为 $+\infty$。所有回复类型都按实际地址收费；重复仍是一次实际查询并进入历史，只不增加不同地址费用。最坏费用取正源，正确性和有限终止覆盖正、负全域。不同原词即使在候选上给出相同向量，也没有共同的已付地址。局部精确数学计算在这个目标中没有另定价格；计算所得的候选描述不能充当取得的源索引、根报告、前沿、导航、重置或谱读数，也没有几何代数或 Clifford 坐标到访问的免费接口。

对证明使用的任意有限真实源族 $\mathcal F$，沿用定义 5.1 的全四值相容关系：

$$
\operatorname{Comp}_{\mathcal F}(\mathcal H_m)
=\{V\in\mathcal F:\ r_V(u_i)=y_i\text{ 对每个 }1\le i\le m\}.
$$

它约束每个历史项，包括分支、缺失和重复，不是仅保留叶回复的关系。它是证明中的集合，策略没有免费读出这个集合的操作。

**定理 10.2（同一原历史的多核心联合下界）。** 对定义 10.1 的每个 $k,d,a,b,n,C,H,q$、每个 $h\ge H$（含 $h=\infty$）及每个原合法确定策略 $\pi$，存在一棵固定有限正源 $V\in\mathcal P$，使从空历史开始的同一完整真实终端同时满足

$$
\left|\{u\in Q(T_\pi(V)):r_V(u)\ne\alpha\}\right|\ge3q,
\qquad
|Q(T_\pi(V))|\ge A+3q.
$$

因此

$$
D_h(a,b;d)\ge A+3\min\left\{a,b,\left\lfloor\frac{a+b}{4}\right\rfloor\right\}.
$$

$q=1$ 的断言直接复用定理 5.2–5.3；$q\ge2$ 时的联合关系是所有核的三枚非 $\alpha$ 原地址在一个有限前缀中共同出现，并由同一固定全源实现。该断言仍对整个原竞争域合法的策略量化。

证明。固定任意上述参数、$h$ 和策略 $\pi$。先明确所用的原供应。按 §2 的式 (2.3) 及其普通证明，每棵正源 $W$ 的真实接受终端必含 $\mathcal A(W)$ 或 $\mathcal B(W)$，即一种颜色的完整实际叶前沿；任一完整颜色前沿在全部 $\mathcal T_C$ 中唯一确定 $W$。必要性使用全负域正确性：两色各有未查叶时交换其标签，所有已查四值不变，却得到同组成负源，确定性使它重放接受历史。唯一性使用完整前沿的前缀树和总叶库存，没有负源高度假设。以下直接消费这些结论。

准备一棵可同时容纳 $q$ 个四叶核的真实宏树。由 $q\ge1$、$q\le a,b$ 和 $4q\le n$，取

$$
\ell=n-4q,\qquad t=\max\{q,4q-b\}.
$$

有 $q\le t\le\min\{3q,a\}$：其中 $4q-b\le a$ 来自 $4q\le a+b$，$4q-b\le3q$ 来自 $b\ge q$，并且 $q\le a$。将 $t-q$ 分成 $q$ 个整数 $e_j\in\{0,1,2\}$，$\sum_{j=1}^q e_j=t-q$；这可以先给每项零，再依次填至多二，因为 $0\le t-q\le2q$。第 $j$ 核取库存

$$
(a_j,b_j)=(1+e_j,3-e_j),\qquad
\sum_{j=1}^q(a_j,b_j)=(t,4q-t).
$$

剩余库存 $(a-t,b-4q+t)$ 非负，总叶数为 $\ell$。

固定一棵有 $q+\ell=n-3q\ge1$ 个叶槽的完整有序骨架，其中 $q$ 个槽作孔，地址分别为 $p_1,\ldots,p_q$，其余 $\ell$ 个槽按剩余库存放固定标签。孔是骨架的不同叶槽，故 $p_j$ 两两前缀无关。令 $\mathcal G_j$ 是定义 3.1 中库存 $(a_j,b_j)$ 的全部四叶宏树；它分别属于 $(1,3),(2,2),(3,1)$ 三族之一，大小为 $20,30,20$。每个孔独立填 $T_j\in\mathcal G_j$，记填完的宏树为 $K[T_1,\ldots,T_q]$，并令

$$
V(T_1,\ldots,T_q)=\rho^d\bigl(K[T_1,\ldots,T_q]\bigr),\qquad
\mathcal F=\{V(T_1,\ldots,T_q):T_j\in\mathcal G_j\}.
$$

每棵填完的宏树有 $n$ 片叶、组成 $(a,b)$，所以 $\mathcal F\subseteq\mathcal P$。固定字面孔中的不同元组给出不同宏树，§2 的 $\rho^d$ 单射使它们也给出不同全源。$\mathcal F$ 因而是有限非空乘积族的真实单射实现。宏叶深度至多 $n-1$，替换块 $X_d,X_{d+1}$ 的高度至多 $d$，故每棵全源高度至多 $H$。当 $\ell=0$，骨架只含孔槽；当 $q=1,\ell=0$，根本身就是唯一孔，无须引入空剩余树。$\mathcal F$ 只是下界证明的正子族，$\pi$ 的竞争域仍为整个 $\mathcal T_C$。

由于 $\rho$ 逐分支作用，孔前缀保留其字面位置。若一个实际请求词写成 $w=p_j u$，则这个 $j$ 唯一，而且

$$
r_{V(T_1,\ldots,T_q)}(p_j u)=r_{\rho^d T_j}(u).
$$

这包括 $u=\varepsilon$、两色叶、分支和穿叶缺失。若没有孔词是 $w$ 的前缀，则 $w$ 停在固定骨架的分支，或进入固定剩余标签的替换块，回复在 $\mathcal F$ 上相同。孔祖先也是固定分支，不因一个查询同时读取多个核。每个实际词至多约束一个可变因子；$u\mapsto p_j u$ 单射，各孔的地址集合 $p_j\{L,R\}^{<\omega}$ 不交。这里只作端点等式的数学分类，$\pi$ 实际请求、取得和支付的始终是完整原词 $w$。

局部选择直接采用定理 3.2、3.4、§4 的坐标书及定理 5.2 证明中的三阶段规则。定理 3.2 覆盖每个 $d\ge3$ 的每个有限局部词，包括空词、恰止块根、任意深穿叶词和 $d=3$ 的短词 $LR,RR$。对任一 $\mathcal G_j$，阶段零的新词可以选择真实非 $\alpha$ 回复并保留一个至少含两枚成员的首阶段硬集；阶段一的新词或者在整个硬集上共同回复 $\alpha$，或者按第二阶段表选择同一真实非 $\alpha$ 回复并保留指定的不同源对；阶段二的源对若共同回复 $\alpha$ 就保留它，否则选择其中一枚成员的真实非 $\alpha$ 回复并选定该成员。前两次缩集的包含关系由式 (3.5) 保证；第三次只在两棵实际树的四值中选择。这些都是原单核供应，不另立局部结果。

现在沿同一 $\pi$ 的历史同时构造各核的保留因子。对每个 $j$ 维护阶段 $s_j\in\{0,1,2,3\}$ 和非空嵌套集合 $S_j\subseteq\mathcal G_j$。初值是 $s_j=0,S_j=\mathcal G_j$；阶段一为原硬集，阶段二为指定的不同源对，阶段三为选定的单成员。对每个已经构造的查询前缀 $\mathcal H_m$，维护

$$
\begin{aligned}
&\{V(T_1,\ldots,T_q):T_j\in S_j\}
\subseteq\operatorname{Comp}_{\mathcal F}(\mathcal H_m),\\
&s_j<3\ \Longrightarrow\ |S_j|\ge2,\\
&\left|\{w\in Q(\mathcal H_m):p_j\text{ 是 }w\text{ 的前缀，且其实际回复非 }\alpha\}\right|\ge s_j.
\end{aligned}
$$

第一项保留整条原词、四值、时间顺序和重复历史；它不要求乘积像穷尽所有相容源。第三项只数该孔的不同实际原地址。初始乘积非空，三项显然成立。

给定当前历史，下一动作由原 $\pi$ 决定。若它请求一个已经出现的原词，乘积中的每棵全源均给出该词先前的真实回复；原样返回并再次记入历史，所有 $S_j,s_j$ 保持。这次重复是实际动作，不增加不同地址数。若它请求一个新词且词不在任何孔内，就返回整个 $\mathcal F$ 的公共真实值，照常收费、记史，所有因子保持；即使这个回复非 $\alpha$，也不拿来补足某个核的阶段。

若新词 $w=p_j u$ 在唯一孔内，只更新因子 $j$。$s_j=0$ 时按首表回复非 $\alpha$ 并缩为硬集，令 $s_j=1$。$s_j=1$ 时若整个硬集共同回复 $\alpha$，就返回这个真实值并保持；否则按第二表回复共同非 $\alpha$ 并保留不同源对，令 $s_j=2$。$s_j=2$ 时若两源共同回复 $\alpha$，就返回它并保持；否则选择一个非 $\alpha$ 真实回复和给此值的一枚成员，令 $S_j$ 为该单成员、$s_j=3$。$s_j=3$ 时只按这枚选定成员的真实读数回复。

这些更新保持联合不变量。缩集嵌套，故所有旧四值约束保留；局部端点等式使新约束只涉及因子 $j$，其他因子任取成员仍满足它；被选回复对应的更新因子非空，整个乘积继续非空。每次阶段增加来自此前未请求的实际词，真实回复非 $\alpha$，所以第三项增加一枚不同地址。共同 $\alpha$ 分支的使用条件是整个当前因子确实给出这个值；一般 $\alpha$ 请求仍有来源信息、照常收费并进入史，并没有被从相容条件中删除。相同向量的不同字面词也分别按新地址处理。由实际查询动作数归纳，不变量适用于任意跨核适应、交错、外部查询及重复。

还须处理 $\pi$ 的返回动作。若当前某个 $s_j<3$，在该因子选两枚不同宏树，其他因子各固定一枚。乘积的单射实现给出两棵不同的全正源 $U,W$，均匹配整条 $\mathcal H_m$。共同初始化和确定性逐动作重放保证：若 $\pi$ 在此历史返回，这同一历史就是 $U,W$ 各自的真实终端。返回假会错误拒绝正源。返回真则 §2 的终端条件使 $Q(\mathcal H_m)$ 含 $U$ 的一色完整前沿；$W$ 也匹配此前沿，其同组成唯一性强迫 $W=U$，矛盾。因此任何核尚未到三时，$\pi$ 不能返回。这里真正使用的是全负域正确性给出的原接受条件，并未把原成员判定换成只在 $\mathcal F$ 上识别来源。

为证明所有核共同有限完成，对固定有限族 $\mathcal F$ 的每棵全源 $U$，记 $m_U$ 为 $\pi$ 在 $U$ 上从空历史至真实终端的查询动作数，包含全部重复。原逐源有限终止给出有限整数

$$
m_* = \max_{U\in\mathcal F}m_U.
$$

只要有未完成核，前段已证明 $\pi$ 必须请求下一合法原词，而更新保持非空相容乘积。假设经过 $m_*$ 次构造查询仍有未完成核。选择当前乘积的一棵全源 $U$；嵌套性使它匹配整个前缀，也匹配每个较短前缀。共同空初始化及确定性使 $\pi$ 在固定 $U$ 上逐动作重放这些原词和四值，包括外部请求、重复和每一步的返回选择。它必须在 $m_U\le m_*$ 次查询后返回，但所有这些前缀仍有未完成核，已被证明不能返回；返回恰在第 $m_*$ 次查询后也产生同一矛盾。所以所有 $q$ 核在同一个有限前缀中到达阶段三。

这个有限性只对完整的固定有限族 $\mathcal F$ 取最大值，不要求全竞争域统一时限、不假设逐核公平调度，也没有给 $\pi$ 一个额外时钟或族索引。它阻止策略用无限重复、核外查询或一直搁置某个核来逃避联合完成。

在所有核完成的前缀末端，各 $S_j$ 是单成员。这些成员组成一个元组，确定一棵固定有限 $V\in\mathcal F$。嵌套全史相容使 $V$ 匹配此前全部原地址与四值。让原 $\pi$ 从共同空历史在这同一 $V$ 上运行，它逐动作真实重放整条构造前缀，然后继续自己在 $V$ 上的真实运行；合法性保证完整运行有限且接受。对每孔，三次阶段增加各给一枚不同非 $\alpha$ 实际地址；孔间地址不交，故至少 $3q$ 枚共同属于 $Q(T_\pi(V))$。保留集的缩小用于证明这棵固定源的存在，实际运行始终查询同一 $V$，没有阶段间换源、重置或拼接各孔独立的最坏源。

最后在这个同一完整终端令 $Q=Q(T_\pi(V))$。若 $\mathcal A(V)\subseteq Q$，其 $A$ 枚真实 $\alpha$ 地址与上述 $3q$ 枚非 $\alpha$ 地址不交，因此 $|Q|\ge A+3q$。若 $\mathcal A(V)\nsubseteq Q$，原终端条件强制 $\mathcal B(V)\subseteq Q$，于是只用

$$
|Q|\ge B,\qquad
B-A=F_{d-2}a+F_{d-1}b\ge n\ge4q>3q
$$

也得到 $|Q|\ge A+3q$。$\beta$ 核地址可以已在 $\mathcal B(V)$ 内，这个分支不把 $3q$ 再加到 $B$，也不强迫策略补全 $\alpha$ 前沿。

因此每个原合法 $\pi$ 都有上述一棵固定正源见证；先取正源最坏费用，再对全部原合法策略取最小值，即得所述 $D_h$ 下界。有限 $h$ 时只使用 $\pi$ 真正选择的合法原词，其局部后缀仍由原全词供应覆盖；$h=\infty$ 时每个请求仍为有限词，联合实现仍在有限前缀内完成。全部同组成负源、原四值及原费用贯穿证明。□

## 11. 原费用消费者、来源与未解边界

定理 10.2 直接作用于定义 1.3 的原 $D_h$。结合旧定理 7.3，在全部上述参数及每个 $h\ge H$（含无穷）有

$$
A+3q\le D_h(a,b;d)\le A+n-2+c_d(a,b),\qquad
c_d(a,b)=\begin{cases}a,&d=3,\\\min(a,b),&d\ge6.\end{cases}
$$

右端及其全负域正确的取得策略保持旧定理 7.2–7.3 的含义，直接引用，不构成新上界。$q=1$ 时左端就是旧 $A+3$。$q\ge2$ 等价于 $a,b\ge2$ 且 $n\ge8$，此时左端相对旧下界严格增加 $3(q-1)$；增量不依赖 $d$，不表示总费用具有相同的比例改进。

作为原费用的直接应用，取 $(a,b,d)=(4,4,3)$。由 $M^3=\left(\begin{smallmatrix}1&2\\2&3\end{smallmatrix}\right)$，有 $n=8$、$(A,B)=(12,20)$、$q=2$、$H=10$。联合证明可以取两个库存 $(1,3),(3,1)$ 的核，固定骨架为一对孔；任一局部成员对填孔后整体替换，所得全源组成都恰为 $(12,20)$。因此对每个 $h\ge10$，包括 $h=\infty$，

$$
18\le D_h(4,4;3)\le22.
$$

下端为 $12+3\cdot2=18$，上端直接由旧 $12+8-2+4=22$ 得到。它排除正源最坏不同地址费用至多 $17$ 的原合法策略；没有给出达到 $18$ 的策略，也没有指定准确值。这个八宏叶应用不重认领定义 9.1 所引的两个四叶准确值，应用中的矩阵计算和旧上界也不另作成果。

本定理的数学归属为仓内普通综合推导（repo-derived）。原字面来源、四值端点、空史策略及费用由定义 1.1–1.3 供应；两色完整终端、同组成唯一性、替换单射和高度由 §2 供应。每个有限局部词的覆盖由定理 3.2 供应，硬集、共同 $\alpha$ 与不同非 $\alpha$ 源对由定理 3.4 及 §4 的原坐标书供应，三阶段和单孔的有限同源实现由定义 5.1、定理 5.2–5.3 供应。这些供应的固定原文见 [5f24 版本的本卷](https://github.com/the-omega-institute/trureturing/blob/5f24ef669fb929320a2d417d2c2f3f713e046d97/docs/develop/theory/FIB_ATOM_MIXED_ACTUAL_ADDRESS_PARTIAL_BOUNDS.md)。

完整颜色前沿的原普通证明、原准确深度及带阈值的识别取得桥另见 [同一固定版本续篇的定义 57.1、引理 57.2、定理 57.3–57.4、57.7](https://github.com/the-omega-institute/trureturing/blob/5f24ef669fb929320a2d417d2c2f3f713e046d97/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md#57-uniform-paid-acquisition-of-actual-image-certificates-at-exact-composition)。这里使用的是该原合同下的普通供应；叶回复相容接口不能替代定理 10.2 的全四值历史，全组成第三像的策略或把两色叶都赋零的权重也不能替代原 $D_h$。

$q\ge2$ 的承重联合关系在定理 10.2 中具体由同一全史的嵌套乘积归纳、任一未完成核禁止终端、整个有限族的 $m_*$、一个固定全源的真实重放组成，并在最终原费用中被消费。各核分别存在困难源不能直接代替这个同时见证。库存分配、静态乘积、前缀局部性、单核规则、末端计数、$q=1$、旧上界和四叶值均直接复用，不另立包装声明。

确定性决策树、证书及直和是成熟方法背景。相关文献包括 Jain–Klauck–Santha 的 [arXiv:1004.0105v1](https://arxiv.org/abs/1004.0105v1) 和 Montanaro 的 [arXiv:1302.4207v1](https://arxiv.org/abs/1302.4207v1)。前者的布尔独立坐标、单位查询深度，后者的有限字母表及按坐标固定的权重，不能未经原假设对应就替代这里任意字面词、四值、按真实回复计数的非 $\alpha$ 不同地址及全负域成员判定。它们只作方法背景，不承担数值下界。仓内综合推导不意味着全球原创；没有给出文献或第三方生态穷尽结论。定理 10.2 是普通数学证明，未取得 Lean kernel 认证。

一般准确 $D_h$ 和达到最优值的原合法策略仍未解决。定义 8.3 的 $E_h$ 与原定理 57.7 保持其阈值：$D_h<B$ 时有 $D_h=A+E_h$，特别是 $A+E_h<B$ 足以给此等式；本下界没有取消 $B$ 阈值。几何代数表达、KBonacci 的块执行和其他取得模型没有在此建立保持实际来源、动作、四值、费用及终止的运输关系。

定义 8.4 的 GeneralH 仍是另一原目标：来源为同一固定自然数对 $(a,b)$，包括零与混合零；正时间轨道为

$$
y(k)=F_{k+3}a+F_{k+4}b,
$$

读口返回完整 $\gcd(y(k),H)$，每次实际查询执行均收费，包括重复；策略从空历史作确定适应，要求逐源有限确定全部正未来。这里的 $H$ 保持公因数任务的模数含义，不是树的高度阈值。其 $H1$、素数 $2,5$、指数一、未知内容、非满轨道、饱和、停滞及退出秩与 WSS 的原边界均保持。树的不同地址下界没有决定这个按每次执行收费的目标。

定义 8.5 的 sameN 也保持原实际来源、选择器和严格预算。用该数论目标自己的记号，$r\ge7$ 为素数，$V=F_r$ 是 Fibonacci 整数而不假定为素数，$I$ 为非空连续整数区间且

$$
I\subseteq\left[\left\lceil\frac V{10}\right\rceil,\left\lfloor\frac V5\right\rfloor\right],\qquad
C_0>1,\quad A>5040,\quad
A\le N_g=1+Vg\le C_0A\quad(g\in I).
$$

这里的 $A,V$ 使用 sameN 的数论含义，不是树组成计数和定理 10.2 的正树。保留

$$
\begin{aligned}
Z(m)&=\frac{\sigma(m)}m,\qquad s=\log A\,\log\log A,\qquad t=e^\gamma\log\log A,\\
b_s(1)&=1,\qquad b_s(p^j)=Z(p^j)^s-Z(p^{j-1})^s\quad(j\ge1),\\
w_s(d)&=\frac{b_s(d)}d,\qquad
M_s=\prod_p\max_{j\ge0}w_s(p^j),\qquad
J_s(d)=\log\frac{M_s}{w_s(d)},
\end{aligned}
$$

其中 $b_s$ 按互素乘法延拓，$w_s(1)=1$，$\gamma$ 为 Euler 常数。原实际正整数 $n_0$ 与 $J_0,L_0\ge0$ 满足：每个 $J_s(d)\le J_0$ 的 $d$ 有既约分式 $d/n_0=u_d/v_d$，$\log v_d\le L_0$，且

$$
n_0e^{-2L_0}>\operatorname{diam}I.
$$

原集合

$$
E^*=\{g\in I:\exists d\mid N_g,\ J_s(d)\le J_0\}
$$

非空时给出同一个唯一 $g^*$。这些假设和选择器不被本树定理更换。必须保留同一实际整数 $N^*=1+Vg^*$，以及它的每个实际正素数幂和每个实际约数；严格目标仍是

$$
\begin{aligned}
C^*&=t^{-s}\sum_{\substack{d\mid N^*\\J_s(d)\le J_0}}b_s(d),\qquad
H^*=t^{-s}\sum_{\substack{d\mid N^*\\J_s(d)>J_0}}b_s(d),\\
C^*+H^*&<\mathcal B(N^*),\qquad
\mathcal B(N^*)=\left(\frac{\log\log N^*}{\log\log A}\right)^s.
\end{aligned}
$$

既有精确望远镜到 $Z(N^*)$ 是复用；若只知 $H^*\le\epsilon_A$，则 $C^*+\epsilon_A<\mathcal B(N^*)$ 只是充分条件，较强的 $C^*+\epsilon_A<1$ 不是原目标的必要条件。原 $N^*$ 不能换成 $g^*F_r$、另一种极值整数、边缘最优值或密度平均。本下界没有支付这些预算；一般树准确最优、GeneralH、sameN 严格预算及原 Robin、黎曼假设问题仍保持未解。

## 11.99 追加锚（本行以下为增补区）

## 12. 同色首请求下降与混色共同历史强化下界

### 12.1 原合同与强化下界的完整陈述

本章沿用定义 1.1–1.3、10.1 的原取得问题。来源是未知的有限、非空、完整有序二叉字面树；叶标为 $\alpha,\beta$，分支有两个非空子树，全部括号、左右次序与每个出现均保留。替换作用于整棵宏树：

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=(\beta,\alpha),\qquad
\rho(S,T)=(\rho S,\rho T),\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

对每个整数 $k\ge1$，令 $d=3k$；对每个正整数 $a,b$、$n=a+b\ge4$，公开准确组成为

$$
C=(A,B)=M^d(a,b)
=\bigl(F_{d-1}a+F_db,\ F_da+F_{d+1}b\bigr),
\qquad H=d+n-1.
$$

这里 $F_0=0,F_1=1,F_{i+2}=F_{i+1}+F_i$。竞争域 $\mathcal T_C$ 是组成恰为 $C$ 的全部有限非空完整有序字面树；正域 $\mathcal P=\mathcal T_C\cap\operatorname{im}\rho^d$ 包含此组成的全部 $d$ 次像。负域 $\mathcal T_C\setminus\mathcal P$ 不受正源高度 $H$ 的筛选。

对每个 $h\in\mathbb N\cup\{\infty\}$、$h\ge H$，策略可直接请求任意有限 $L/R$ 词 $u$ 的端点，只要求 $|u|\le h$，无需先查祖先；$\varepsilon$ 为根地址。固定源 $U$ 上的真实回复 $r_U(u)$ 保留全部四值：端点叶 $\alpha$、端点叶 $\beta$、分支 $\mathsf{br}$、穿过叶的缺失 $\varnothing$。策略 $\pi$ 从共同的、来源无关的空初始化及空取得历史出发，仅依公开参数及其自己的完整实际历史选择下一原词或布尔返回。历史按时间排列，保留原字面词、全部四值及重复。原合法性要求 $\pi$ 在每个 $U\in\mathcal T_C$ 上正确且逐源有限终止。

记 $T_\pi(U)$ 为从空史开始的完整真实终端，$Q(T)$ 为其中不同的实际请求词集合。原费用与正源最坏优化仍是

$$
\operatorname{paid}(T)=|Q(T)|,
\qquad D_h(a,b;d)=\min_{\pi\text{ 原合法}}\max_{V\in\mathcal P}|Q(T_\pi(V))|.
$$

每种回复都按实际不同地址收费；重复仍执行并入史，只不增加不同地址数。不同字面词即使给出相同向量，也各有自己的首次取得费用。局部精确数学计算没有另定价格；这不会提供免费来源索引、根报告、前沿、导航、重置、谱读数或 GA/Clifford 坐标到访问的捷径。

**定理 12.1（同色余量在同一真实终端上的强化下界）。** 对每个上述原参数、每个 $h\ge H$（含 $\infty$），令

$$
\begin{aligned}
q&=\min\left\{a,b,\left\lfloor\frac n4\right\rfloor\right\},\\
\max\{q,4q-b\}&\le t\le\min\{3q,a\},\qquad t\in\mathbb Z,\\
m_\alpha&=a-t,\qquad m_\beta=b-4q+t,\\
g(m)&=\max\{m-2,0\},\qquad
L=3q+g(m_\alpha)+g(m_\beta).
\end{aligned}
$$

$t$ 的整数区间非空，可取 $t=\max\{q,4q-b\}$。对这个区间中的每个 $t$ 及每个原合法确定策略 $\pi$，存在一棵固定有限正源 $V\in\mathcal P$，使同一完整真实终端同时满足

$$
\left|\{u\in Q(T_\pi(V)):r_V(u)\ne\alpha\}\right|\ge L,
\qquad |Q(T_\pi(V))|\ge A+L.
$$

因此，对每个可行整数 $t$，

$$
D_h(a,b;d)\ge A+3q+g(a-t)+g(b-4q+t).
$$

该断言不要求不同策略共用同一见证 $V$，但一条见证运行始终查询同一实际源。旧定理 7.2–7.3 的上界与全负域正确取得策略直接复用，故

$$
A+3q+g(a-t)+g(b-4q+t)
\le D_h(a,b;d)\le A+n-2+c_d(a,b),
\qquad
c_d(a,b)=\begin{cases}a,&d=3,\\\min(a,b),&d\ge6.\end{cases}
$$

至少一个余量 $m_\alpha,m_\beta\ge3$ 时，左端严格强于定理 10.2 的 $A+3q$；两余量均至多二时只得到原下界。证明见 12.2–12.4；不主张一般准确值或达到左端的策略。

### 12.2 同色全族的任意首请求单射下降

#### 12.2.1 固定块供应与真实全族

直接使用[固定续篇的引理 57.2、定理 57.3、引理 57.9 及定理 57.10](https://github.com/the-omega-institute/trureturing/blob/e250367fe75d20167ec364111f0fc02e1c6d7bbb/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md#57-uniform-paid-acquisition-of-actual-image-certificates-at-exact-composition)，以及本卷 §2、定理 3.2、3.4、5.2、10.2。块的四值表、替换单射与高度，完整两色终端及同组成前沿唯一性，同色三、四叶基底和混色四叶三阶段均作为原供应消费。

为使库存整数 $t$ 与块索引分开，写 $Z=X_s=\rho^s\alpha$，其中 $s=d$ 或 $d+1$，故 $s\ge3$。对 $m\ge1$，$\mathcal F_m(Z)$ 是所有 $m$ 叶完整有序宏形状逐叶放入同一个真实块 $Z$ 的族。它也是全部 $m$ 叶同色 $\alpha$ 宏树的 $\rho^s$ 像。原 $\rho^s$ 单射保证不同宏形状给出不同实际树。$m\ge2$ 时每个成员根为分支；$\mathcal F_2(Z)=\{(Z,Z)\}$，$\mathcal F_3(Z)$ 是两种不同形状，$\mathcal F_4(Z)$ 是原五种形状。这里不定义零叶空树。

本节只需引理 57.2 的下述块表后果。若 $r_Z(v)=\alpha$，则 $v\ne\varepsilon$、$w(v)=s$ 且末字母为 $R$，其中 $w(v)=\#L(v)+2\#R(v)$。写 $v=ev'$，有

$$
\begin{array}{c|c|c}
e&w(v')&r_Z(v')\\\hline
L&s-1&\beta\\
R&s-2&\mathsf{br}
\end{array}
$$

故删除首字母后必为真实非 $\alpha$ 端点；此处的 $\beta$ 与分支仍是不同回复。

#### 12.2.2 首请求的构造及单射恢复

对任意 $m\ge5$ 和任意有限词 $u$，构造单射

$$
J:\mathcal F_{m-1}(Z)\longrightarrow\mathcal F_m(Z)
$$

使全部 $J(S)$ 在 $u$ 共同回复一个真实 $y\ne\alpha$。

若 $u=\varepsilon$，取 $J(S)=(Z,S)$，共同回复为 $\mathsf{br}$。若 $u=cv$，$c\in\{L,R\}$ 且 $r_Z(v)\ne\alpha$，在 $c=L$ 时取 $(Z,S)$，在 $c=R$ 时取 $(S,Z)$；$u$ 进入固定 $Z$，共同回复为 $r_Z(v)$，可以是 $\beta$、分支或缺失。两种映射都能从另一根孩子恢复 $S$，并恰好增加一片宏 $Z$。

剩余情形为 $u=cv$ 且 $r_Z(v)=\alpha$。按前段写 $v=ev'$。每个 $S\in\mathcal F_{m-1}(Z)$ 有唯一根分解 $S=(U,W)$，其中 $U,W$ 各有正数片宏 $Z$，合计 $m-1$ 片。依 $(c,e)$ 取如下四种两槽插入：

| $(c,e)$ | $J(S)$ | $u=cev'$ 进入的固定块 | 从 $J(S)$ 恢复 $(U,W)$ 的子树位置 |
| --- | --- | --- | --- |
| $(L,L)$ | $((Z,U),W)$ | $LL$ 处的 $Z$ | $LR$ 与 $R$ |
| $(L,R)$ | $((U,Z),W)$ | $LR$ 处的 $Z$ | $LL$ 与 $R$ |
| $(R,L)$ | $(U,(Z,W))$ | $RL$ 处的 $Z$ | $L$ 与 $RR$ |
| $(R,R)$ | $(U,(W,Z))$ | $RR$ 处的 $Z$ | $L$ 与 $RL$ |

每个像恰含 $m$ 片宏 $Z$，且

$$
r_{J(S)}(u)=r_Z(v')=y\ne\alpha
\qquad\text{对全部 }S\in\mathcal F_{m-1}(Z).
$$

四行均按 $e$ 判定：$e=L$ 时 $y=\beta$，$e=R$ 时 $y=\mathsf{br}$。表中恢复位置给出字面树的唯一根分解：两个像相等时，指定位置的 $U,W$ 分别相等，于是原 $S$ 相等。因此四种映射均单射。这是对子树等式的数学恢复，没有让原策略免费读取这些位置或取得被恢复的来源。

#### 12.2.3 所有有限词的完整四值运输与复合

下降还需保留之后每个请求的结构。以下所有后缀 $v$ 都可为空，也可任意深；固定块内的 $r_Z(v)$ 是完整真实四值，穿过它的任一叶仍返回 $\varnothing$。

一槽映射的分类如下。

| 映射 | 原词类别 | 在映射像上的真实回复 |
| --- | --- | --- |
| $S\mapsto(Z,S)$ | $\varepsilon$ | 公共 $\mathsf{br}$ |
| $S\mapsto(Z,S)$ | $Lv$ | 公共 $r_Z(v)$ |
| $S\mapsto(Z,S)$ | $Rv$ | $r_S(v)$ |
| $S\mapsto(S,Z)$ | $\varepsilon$ | 公共 $\mathsf{br}$ |
| $S\mapsto(S,Z)$ | $Lv$ | $r_S(v)$ |
| $S\mapsto(S,Z)$ | $Rv$ | 公共 $r_Z(v)$ |

对于 $S=(U,W)$，四种两槽映射分别有以下完整分类；右栏的端点词始终是原 $S$ 上的一个词。

| $S\mapsto((Z,U),W)$ 的原词 | 真实回复 |
| --- | --- |
| $\varepsilon$、$L$ | 公共 $\mathsf{br}$ |
| $LLv$ | 公共 $r_Z(v)$ |
| $LRv$ | $r_U(v)=r_S(Lv)$ |
| $Rv$ | $r_W(v)=r_S(Rv)$ |

| $S\mapsto((U,Z),W)$ 的原词 | 真实回复 |
| --- | --- |
| $\varepsilon$、$L$ | 公共 $\mathsf{br}$ |
| $LRv$ | 公共 $r_Z(v)$ |
| $LLv$ | $r_U(v)=r_S(Lv)$ |
| $Rv$ | $r_W(v)=r_S(Rv)$ |

| $S\mapsto(U,(Z,W))$ 的原词 | 真实回复 |
| --- | --- |
| $\varepsilon$、$R$ | 公共 $\mathsf{br}$ |
| $RLv$ | 公共 $r_Z(v)$ |
| $Lv$ | $r_U(v)=r_S(Lv)$ |
| $RRv$ | $r_W(v)=r_S(Rv)$ |

| $S\mapsto(U,(W,Z))$ 的原词 | 真实回复 |
| --- | --- |
| $\varepsilon$、$R$ | 公共 $\mathsf{br}$ |
| $RRv$ | 公共 $r_Z(v)$ |
| $Lv$ | $r_U(v)=r_S(Lv)$ |
| $RLv$ | $r_W(v)=r_S(Rv)$ |

各表穷尽全部有限词：空词单列；非空词先按首字母分，在插入分支的一侧再分为空后缀或第二字母。这也覆盖恰停在插入分支、恰停在固定块根、进入 $U,W$、跨过两色叶等情形。按真实端点递归，进入固定子树的一类给公共四值；进入 $U$ 或 $W$ 的一类正好等于 $S$ 的相应单端点读数，未丢弃分支或缺失。

设当前单射 $\Phi:\mathcal F_r(Z)\to\mathcal F_m(Z)$ 有如下性质：对每个原词 $u$，$r_{\Phi(S)}(u)$ 要么是与 $S$ 无关的公共真实值，要么对全部 $S$ 等于 $r_S(v)$，其中 $v$ 是为该 $u$ 确定的一个有限端点词。恒等映射有此性质。若复合本节的一个下降 $J:\mathcal F_{r-1}(Z)\to\mathcal F_r(Z)$，公共值在子族上保持；变量端点 $r_{J(S)}(v)$ 再按上述完整表分类，仍是公共四值或 $r_S(v')$。因此 $\Phi\circ J$ 保持此性质，并因两个映射单射而单射，其像是旧 $\Phi(\mathcal F_r(Z))$ 的非空子族。

运输只陈述真实树上的端点等式。实际执行、取得与支付的仍是 $\pi$ 选择的原完整词 $u$；$v,v'$ 不作为额外请求执行，不进入已付地址集合，也不与 $u$ 共用缓存。两个新原词即使运输到同一辅助端点，仍分别按它们自己的字面身份收费。辅助分类和单射恢复既不提供免费导航，也不改变来源无关空初始化。

### 12.3 同一完整历史上的 $m-2$ 同色供给

固定 $Z=X_s$、$s\ge3$。同色因子的目标额度是 $g(m)$ 枚不同实际原词上的非 $\alpha$ 回复；规则只在当前被请求的词上选择一个由非空嵌套真实子族共同实现的四值。先说明原低阶供应及其在完整历史中的使用。

$m=0$ 时不安放该因子，不用零叶树；$m=1,2$ 用相应数目的固定同色标签槽，额度为零。$m=3$ 时用原两种真实形状 $(Z,(Z,Z))$、$((Z,Z),Z)$。在一枚新原词上，若两者共同回复 $\alpha$，记录该真实值并保留源对；否则选择一枚给出真实非 $\alpha$ 回复的成员，计这一枚新原地址并固定该成员，完成 $g(3)=1$。此前的共同回复和重复在源对上全保留，完成前始终有两棵不同树。这是原定理 57.10 的同色三叶供应的源对使用，不另求低阶准确值。

$m=4$ 时直接消费原引理 57.9 的五形性质：对每个有限端点词，五形中存在至少两棵不同树给出同一个非 $\alpha$ 值。首枚新原词选这个真实桶，保留其中一对不同成员，得到第一单位；随后新词若在这对上共同为 $\alpha$ 就保留，否则选一枚非 $\alpha$ 成员并固定，得到第二单位。第一单位之前保留五形，第二单位之前保留源对；共同 $\alpha$ 及重复都保留旧史。故完成前至少两源，额度为 $g(4)=2$。五形桶与四叶最优值是既有供应，这里不重证或重认领它们。

现在令 $m\ge5$。初始因子为完整 $\mathcal F_m(Z)$，额度零，$\Phi$ 为恒等。下降阶段维护

$$
\mathcal S=\Phi(\mathcal F_r(Z)),\qquad 4\le r\le m,
\qquad\text{已经取得的额度}=m-r,
$$

其中 $\Phi$ 单射且具 12.2.3 的公共四值或单端点性质，$\mathcal S$ 的每个成员匹配此前每一项原四值历史。所有更新只缩到 $\mathcal S$ 的非空子族。若此因子置于一个固定孔中，局部原词指实际全词在该孔后的端点；不同地址身份仍按实际全词判定。

对 $r\ge5$，下一动作按如下完整规则处理。

- 已经请求过的原词：重放此前真实回复，再将重复动作入史；$r,\Phi,\mathcal S$ 及额度都保持。
- 新原词在当前因子上是公共 $\alpha$：记录这个真实 $\alpha$ 并保持因子，不增加额度。
- 新原词是公共非 $\alpha$：记录公共值，计当前这一枚不同原地址；用一槽单射 $J_0(S)=(Z,S)$ 从 $\mathcal F_{r-1}(Z)$ 嵌入 $\mathcal F_r(Z)$，更新 $\Phi\gets\Phi\circ J_0$、$r\gets r-1$。旧像上的公共值在新像保持。
- 新原词运输为变量端点 $r_S(v)$：以 12.2.2 对此有限 $v$ 的下降 $J$，选择其全像共同的真实非 $\alpha$ 值；计当前这一枚不同原地址，更新 $\Phi\gets\Phi\circ J$、$r\gets r-1$。

后两种更新的单射性与全词运输由 12.2.3 保证；新像包含于旧像，故不仅保留之前的叶回复，也保留每一项分支、缺失、时间顺序及重复约束。新原词的真实共同回复在新像上成立，故可以加入同一条历史。以前被共同回复的一个词，在全部后续子族仍给该旧值；这一点保证重复不会再取得下降额度。相同辅助端点对应的两个不同新原词各自真实收费，没有把辅助端点当作已付缓存键。

到 $r=4$ 时已经取得 $m-4$ 单位，因子仍为五形的单射像 $\Phi(\mathcal F_4(Z))$。在下一新原词上，公共 $\alpha$ 保持；公共非 $\alpha$ 可任选两种不同五形作为保留源对并获得首个基底单位；变量端点则使用原引理 57.9 的同一非 $\alpha$ 至少两源桶，保留其中源对，获得首个基底单位。运输等式使这些真实回复发生在当前原词，单射使像中的两源仍不同，缩族使全部旧史保持。随后对这一真实源对，新原词若共同 $\alpha$ 则保持，否则选择真实非 $\alpha$ 单成员，得到第二个基底单位并固定。重复一律只重放旧值。

总额度因此为

$$
(m-4)+2=m-2=g(m).
$$

这个计数表示：凡供给规则完成，便已得到此额度；其共同有限完成将在 12.4 对原合法 $\pi$ 证明。下降未完成时 $r\ge4$，完整族至少含两形且 $\Phi$ 单射；四叶末阶段未完成时仍保留两源。因此每个未完成因子至少有两棵不同真实树，全部成员匹配同一条旧史。完成后固定一棵相容成员，其后每个实际请求都按这棵成员真实回复，仍不改变此前的历史。

### 12.4 同一混色全源上的共同实现与原费用证明

#### 12.4.1 每个可行 $t$ 的库存及真实全正族

固定定理 12.1 的任意原参数、可行整数 $t$、深度 $h$ 与原合法 $\pi$。由 $a,b>0,n\ge4$，有 $q\ge1$、$q\le a,b$ 和 $4q\le a+b$。区间左端的两项各不超过 $a$ 和 $3q$：$q\le a,3q$，$4q-b\le a$ 来自总库存，$4q-b\le3q$ 来自 $b\ge q$。所以整数区间非空。任意其中的 $t$ 都满足 $m_\alpha,m_\beta\ge0$。

将 $t-q$ 分为 $q$ 个 $e_j\in\{0,1,2\}$，$\sum_j e_j=t-q$；$0\le t-q\le2q$ 保证可逐项分配。第 $j$ 个混色四叶核取库存

$$
(a_j,b_j)=(1+e_j,3-e_j),\qquad
\sum_{j=1}^q(a_j,b_j)=(t,4q-t).
$$

各核使用定义 3.1 的对应全部宏树族 $\mathcal G_j$。对余量 $m_c\ge3$ 的每种颜色 $c\in\{\alpha,\beta\}$，再置一个全部 $m_c$ 叶同色宏形状核；余量一或二放相应数目的固定标签槽，余量零不放任何槽。于是可变孔数为 $q+\mathbf1_{m_\alpha\ge3}+\mathbf1_{m_\beta\ge3}$，固定标签槽数为

$$
\mathbf1_{m_\alpha\le2}m_\alpha+\mathbf1_{m_\beta\le2}m_\beta.
$$

选择具有这些孔槽和固定标签槽的非空完整有序骨架 $K$。$q\ge1$ 保证至少一个槽；只有一个槽时它可为根孔，始终无需零叶子树。各可变孔的字面地址 $p_j$ 是不同叶槽，故两两前缀无关。

让每个孔独立填入其全部宏树族中的成员 $T_j$，形成 $K[T_1,\ldots,T_
u]$，然后仅对这个整体施加一次 $\rho^d$。每棵填完的宏树有

$$
n=4q+m_\alpha+m_\beta
$$

片叶、组成 $(a,b)$。其同色 $\alpha$ 核展开为 $\mathcal F_{m_\alpha}(X_d)$，同色 $\beta$ 核展开为 $\mathcal F_{m_\beta}(X_{d+1})$，因为 $\rho^d\beta=X_{d+1}$；不对这些已展开块再施一次替换。定义

$$
\mathcal F=\left\{V(T_1,\ldots,T_
u)
=\rho^d\bigl(K[T_1,\ldots,T_
u]\bigr):
T_j\text{ 独立遍历各完整宏核族}\right\}.
$$

固定孔的填入单射与原 $\rho^d$ 单射使乘积元组在真实全源中单射实现。各核族有限非空，故 $\mathcal F$ 有限非空且 $\mathcal F\subseteq\mathcal P$；全部源准确组成为 $(A,B)$。宏叶深度至多 $n-1$、替换块高度至多 $d$，故全源高度至多 $H$。此有限正族只是证明见证，原策略仍在全部 $\mathcal T_C$ 上合法，允许的原请求没有被限制到孔内或宏地址。

#### 12.4.2 任意交错、核外请求、四值与重复的嵌套乘积

原 $\rho$ 逐分支作用，保留孔前缀 $p_j$。若实际全词 $w$ 进入可变孔，唯一写成 $w=p_jv$，其中 $v$ 可为空，且

$$
r_{V(T_1,\ldots,T_
u)}(p_jv)=r_{\rho^d T_j}(v).
$$

若无孔地址为 $w$ 的前缀，$w$ 停在固定骨架分支，或进入固定标签的替换块，包括穿叶缺失；它在整个 $\mathcal F$ 上给公共真实四值。孔的祖先也是固定分支。集合 $p_j\{L,R\}^{<\omega}$ 两两不交，一个完整请求至多约束一个可变核。这是原端点局部性等式，不是额外请求 $v$ 的执行。

记展开核的完整族为 $\mathcal C_j=\{\rho^dT_j\}$；对同色核它正是 12.3 的 $\mathcal F_{m_c}(X_s)$。因展开单射，可在 $\mathcal C_j$ 内选择嵌套因子，再用其唯一宏原像填回同一 $K$，这只定义全源集合，不给策略来源解码服务。每个混色核的额度 $b_j=3$，每个同色核的额度 $b_j=g(m_c)$，合计 $\sum_j b_j=L$。

沿同一 $\pi$ 的下一实际动作，维护非空嵌套因子 $S_j\subseteq\mathcal C_j$、已取得额度 $\ell_j\in\{0,\ldots,b_j\}$ 及实际原历史 $\mathcal H$，满足

$$
\begin{aligned}
&\{V(T_1,\ldots,T_
u):\rho^dT_j\in S_j\text{ 对全部 }j\}
\subseteq\operatorname{Comp}_{\mathcal F}(\mathcal H),\\
&\ell_j<b_j\ \Longrightarrow\ |S_j|\ge2,\\
&\left|\{w\in Q(\mathcal H):p_j\text{ 为 }w\text{ 的前缀，且实际回复非 }\alpha\}\right|\ge\ell_j.
\end{aligned}
$$

$\operatorname{Comp}_{\mathcal F}$ 保留每一项原词与真实四值，重复按时间顺序入史；它不只约束叶回复。初始 $S_j=\mathcal C_j$、$\ell_j=0$、$\mathcal H$ 为空，上述条件成立。

重复全词 $w$ 时，当前乘积的每棵全源都给出此前回复，原样返回并再次入史；各因子与额度保持。新核外词时，返回整个 $\mathcal F$ 的公共真实值，实际付费并入史，但不补任何核的额度。新孔内词 $w=p_jv$ 时，仅更新 $j$ 因子，其他因子保持。

对混色核直接采用定理 3.2、3.4、§4、5.2 的原三阶段：额度零时，新词按首阶段表给真实非 $\alpha$ 并保留至少两源硬集；额度一时，整个硬集共同为 $\alpha$ 则保持，否则按第二表给共同非 $\alpha$ 并保留不同源对；额度二时，源对共同 $\alpha$ 则保持，否则给其中一枚的真实非 $\alpha$ 并固定该枚，完成第三单位。完整符号覆盖包括任意有限 $v$、空词、块根、穿叶四值与 $d=3$ 的短词例外，故这里无需限制请求类别。共同 $\alpha$ 条件必须对当前整个因子成立。

对同色核，采用 12.3 的低阶源对或五形规则，以及 $\Phi(\mathcal F_r(X_s))$ 的下降规则。新公共 $\alpha$ 保持；新公共非 $\alpha$ 或变量端点下降各增加当前全词的一单位；至四叶后按两阶段完成。完成因子固定一棵真实成员，以后按该成员回复。所有内部运输词都只作数学端点等式，原历史记录的仍是 $w$。

每次更新都是当前因子的非空子族，并使其全部成员在 $w$ 给被选真实回复。嵌套性保留全部旧项；孔局部性使其他因子任取成员也满足新增项，故乘积继续非空并全史相容。额度只在此前未请求的完整 $w$ 且真实回复非 $\alpha$ 时增加，因而确有一枚新的实际不同地址。共同 $\alpha$ 同样支付并保留为历史约束。按查询动作数归纳，整个不变量覆盖跨核适应、任意交错、核外词、两色叶、分支、缺失及重复。即使两词给相同向量或同一辅助端点，仍按各自原词处理；孔内额度也不会重复归给另一孔。

#### 12.4.3 所有核在一个有限前缀共同完成及固定 $V$ 重放

若有未完成核 $j$，$S_j$ 至少两枚不同成员；其他因子各取一枚，由乘积单射实现得到不同全正源 $U,W\in\mathcal F$。它们都匹配完整 $\mathcal H$。共同空初始化及确定性逐动作保证两源都重放此前的全部原词与四值，包括重复和核外动作。若 $\pi$ 此时返回假，就错误拒绝这些正源；若返回真，$\mathcal H$ 就是 $U$ 的真实接受终端。

由原定理 57.3 及本卷 §2，全负域正确性强制该接受终端含 $U$ 的一种完整颜色前沿。$W$ 匹配此前沿，且与 $U$ 同组成，原前沿唯一性便强迫 $W=U$，矛盾。因此任一核未完成时不能终端，策略必须选择下一合法原词。这里确实消费了全部同组成负源的正确性，没有将成员判定换成仅在 $\mathcal F$ 内的来源识别。

为证明共同有限完成，先固定上面整个有限真实族 $\mathcal F$。对每个 $U\in\mathcal F$，令 $m_U$ 是 $\pi$ 在固定 $U$ 上从空史到真实终端的查询动作数，包含重复。原逐源有限终止给

$$
m_* = \max_{U\in\mathcal F}m_U<\infty.
$$

假设构造到 $m_*$ 次查询仍有未完成核。从当前非空乘积选择 $U$；嵌套全史相容使它匹配这整个前缀及每个较短前缀，共同初始化与确定性使其真实运行逐动作重放它们。它须在 $m_U\le m_*$ 次查询后返回。但额度不减，当前未完成的核在所有这些较短前缀也未完成，那些历史已被证明不能返回。返回恰在第 $m_*$ 次查询后也矛盾。故所有核在同一个有限前缀共同取得各自全部额度。

$m_*$ 只取整个固定有限正族的真实终端动作数最大值，既不要求负域统一时限，也不假设逐核公平调度；它不是交给策略的时钟、来源索引或新读数。无限重复、核外查询或一直搁置某核均不能规避此有限性。

在共同完成的前缀末端，从当前乘积选择一棵固定 $V\in\mathcal F$。$V$ 匹配全部旧原词和全部四值。让原 $\pi$ 在这个同一 $V$ 上从空历史运行，它逐动作真实重放整条构造前缀，然后继续自己在 $V$ 上的真实运行；原合法性保证完整运行有限且接受。孔内各额度对应的地址在孔间不交，故全部 $L$ 枚不同非 $\alpha$ 原地址共同保留在这个完整真实终端。

嵌套缩族是固定见证的存在证明，不是执行过程中换源；原真实运行始终查询这个 $V$。没有将各核分别存在的最坏源相加，没有把阶段计数替代实际原地址费用，也没有把推导得到的辅助端点加入实际历史。

#### 12.4.4 两色终端的原费用与有限上限、无穷上限

在这同一 $V$ 的完整真实终端令 $Q=Q(T_\pi(V))$。若 $\mathcal A(V)\subseteq Q$，$A$ 枚真实 $\alpha$ 地址与已经强制的 $L$ 枚真实非 $\alpha$ 地址不交，故

$$
|Q|\ge A+L.
$$

若 $\mathcal A(V)\nsubseteq Q$，原两色终端条件强制 $\mathcal B(V)\subseteq Q$，仅使用 $|Q|\ge B$。由 $g(m)\le m$，

$$
L=3q+g(m_\alpha)+g(m_\beta)
\le3q+m_\alpha+m_\beta=n-q<n,
\qquad
B\ge A+n>A+L.
$$

因此此分支也给 $|Q|\ge A+L$。核中某些非 $\alpha$ 地址可能已属于 $\beta$ 前沿，这一分支不把 $L$ 再加到 $B$；尤其保留 $d=3$ 的原 $\beta$ 路线。

对每个原合法 $\pi$ 都存在上述单一正源 $V$，先在全部原正源上取最坏费用，再对全部原合法策略取最小值得定理 12.1。对于有限 $h$，只回答 $\pi$ 真正选择且满足 $|w|\le h$ 的原词；孔后缀和运输词服务于端点等式，不执行另外的查询、不增加原深度权限。对于 $h=\infty$，每次请求仍是有限词，$m_*$ 及共同完成只涉及有限前缀。全负域正确性、空史、四值、重复与逐源有限终止均在证明中实际使用。控制计算没有引入另一费用指标，GA 或 Clifford 坐标可逆也不能抵免任何实际原词的取得费用。□

### 12.5 实际消费者、新增与复用、未解边界

本章新增内容的活链是：任意有限首请求的全族单射下降，经全四值端点运输和复合，供给同一完整历史中的无界同色 $m-2$ 额度，再由真实全源的嵌套乘积、共同有限完成与固定源重放，得到原 $D_h\ge A+L$。新增同色余量因子是下降的实际消费者，定理 12.1 是同史供给的实际消费者；四表与单射恢复是这条构造的组成部分，不作为独立包装成果。

原块表、替换单射和高度来自固定续篇 57.2；原全负域终端、两色前沿唯一性与 $B-A\ge n$ 来自 57.3 及本卷 §2；三叶源对和四叶非 $\alpha$ 至少两源桶来自 57.9–57.10。混色核的任意有限词覆盖、三阶段和同史乘积方法直接复用本卷 3.2、3.4、§4、5.2、10.2；原上界及真正补查策略直接复用 7.2–7.3。所用本卷原供应的固定文本见 [e250 版本](https://github.com/the-omega-institute/trureturing/blob/e250367fe75d20167ec364111f0fc02e1c6d7bbb/docs/develop/theory/FIB_ATOM_MIXED_ACTUAL_ADDRESS_PARTIAL_BOUNDS.md)。库存、$t$ 区间、末端代数、低阶值、零额度、前缀局部性和实例计算不另认领新成果。上述普通综合推导不宣称全球原创或 Lean kernel 认证；§11 的成熟决策树与直和文献仍只作方法背景，不承担新增数值界。

作为原问题的直接应用，取 $(a,b,d)=(1,8,3)$。原矩阵给 $n=9$、$(A,B)=(17,26)$，且 $q=1$，可行区间只含 $t=1$。余量为 $(m_\alpha,m_\beta)=(0,5)$，所以

$$
L=3+g(0)+g(5)=6,\qquad H=3+9-1=11.
$$

对每个 $h\ge11$，包括 $\infty$，新下界与旧上界给

$$
23\le D_h(1,8;3)\le25.
$$

右端为旧 $17+9-2+c_3(1,8)=25$。这排除正源最坏不同地址费用至多 $22$ 的原合法策略，没有提供达到 $23$ 的策略，也没有指定准确值。该应用、原 $A+3q$ 及既有四叶准确值均是复用或直接代入。

一般混色准确 $D_h$、达到最优的原合法策略与原 $\beta$ 前沿阈值仍未解决。定义 8.3 及原定理 57.7 关于 $D_h=A+E_h$ 的阈值保持；本章不给出无条件等式。几何代数表达的可逆性没有建立新的付费操作桥。

GeneralH 完整合同仍为 §11 的同一固定自然数来源 $(a,b)$，包括零和混合零、正时间 $y(k)=F_{k+3}a+F_{k+4}b$、完整 $\gcd(y(k),H)$ 回复、每次执行含重复收费、空史确定适应和逐源有限确定全部正未来；$H1$、素数 $2,5$、指数一、未知内容、非满轨道、饱和、停滞及退出秩、WSS 均保持原边界。这里的树不同地址费用没有结算该目标。

sameN 保持 §11 的完整实际来源、连续窗口、分离分母和同一选择器；$r\ge7$ 为素数而 $V=F_r$ 只是 Fibonacci 整数，同一实际整数仍为 $N^*=1+Vg^*$。全部实际正素数幂与全部实际约数均保留，严格目标仍为 $C^*+H^*<\mathcal B(N^*)$。已知 $H^*\le\epsilon_A$ 时，$C^*+\epsilon_A<\mathcal B(N^*)$ 只作充分条件，较强的 $<1$ 不是必要条件；既有精确望远镜到 $Z(N^*)$ 只是复用。本章不改这些假设、不支付该预算，也不结算 GeneralH、sameN、Robin、黎曼假设或持续至 2027 的母目标。

## 12.99 追加锚（本行以下为增补区）

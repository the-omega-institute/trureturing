# FIB-ATOM 两个四叶混色格的显式普通证书

## 1. 原合同、两格参数、来源与归属

**定义 1.1（原字面树与完整竞争域）。** 沿用[原定义57.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md#57-uniform-paid-acquisition-of-actual-image-certificates-at-exact-composition)：来源是一棵未知、非空、有限、完整有序二叉树 $U$，叶标签为 $\alpha,\beta$；保留括号、左右和每个不同出现。替换逐个分支作用，且

$$
\rho\alpha=\beta,\qquad \rho\beta=(\beta,\alpha),\qquad
\rho(S,T)=(\rho S,\rho T),\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

本卷的两格为 $(a,b,d)=(2,2,3),(3,1,3)$，$n=a+b=4$。公开组成 $C=(A,B)=M^3(a,b)$，$N=A+B$；$\mathcal T_C$ 包含该组成的全部完整有序树，$\mathcal P=\mathcal T_C\cap\operatorname{im}\rho^3$。目标是在全部 $\mathcal T_C$ 上判定字面三次像成员身份。因为

$$
M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\qquad
(A,B,N)=\begin{cases}(6,10,16),&(a,b)=(2,2),\\(5,9,14),&(a,b)=(3,1),\end{cases}
$$

两格的正源最大高度均为 $H=d+n-1=6$。原竞争域中的负源仍可具有高于6的高度；完整 $N$ 叶树的高度至多 $N-1$，在两格分别为15、13。$H$ 只用于所给上界请求的合法性，不用于筛去负源。

**定义 1.2（原端点、真实历史与两种计数）。** 地址为任意有限 $L/R$ 词，空词 $\varepsilon$ 是根。端点回复 $r_U(u)$ 保留全部四值：相应标签叶为 $\alpha,\beta$，分支为 $\mathsf{br}$，穿过叶为 $\varnothing$。每个 $|u|\le h$ 的请求均合法，无祖先查询要求；$h=\infty$ 允许任意有限深词。共同初始化与来源无关，取得历史为空。确定策略只由公开参数及自身按时序取得的原地址／四值回复历史选择下一请求或布尔返回，必须对每个 $U\in\mathcal T_C$ 正确且有限终止。

若真实终端历史为 $T=((u_1,y_1),\ldots,(u_m,y_m))$，则

$$
Q(T)=\{u_1,\ldots,u_m\},\qquad
\operatorname{paid}(T)=|Q(T)|,\qquad
D_h(a,b;3)=\min_{\pi\text{ 原合法}}\max_{V\in\mathcal P}|Q(T_\pi(V))|.
$$

无合法策略时 $D_h$ 取 $+\infty$。每个不同实际请求地址均收费，不论回复是哪一种；重复仍保留为真实动作及历史项，只不再增加不同地址费用。动作数是 $m$。最坏费用在正源上取，正确性及逐源有限终止在整个竞争域上要求。公开模板、候选索引和矩阵不是已取得的源索引、根报告、前沿、导航、重置、谱读数或几何代数坐标到地址的免费接口。原费用没有给控制计算、存储、词编码或物理移动指定价格。

**定义 1.3（证书的归属）。** 本卷的承重对象是两张具体诊断表及其真实补查的完整有限证书。直接使用原引理57.2、定理57.3、57.4、57.7的字面块、两色刚性、深度独立性及实际取得桥，并使用[混色部分界卷定理5.3](FIB_ATOM_MIXED_ACTUAL_ADDRESS_PARTIAL_BOUNDS.md#5-从原空历史到同一固定正源的下界)的 $A+3$ 固定源下界。原定义57.11已经报告混色四叶 $E=3$ 的有限数值；该数值与一般操作桥、下界均不作为本卷新增数学。第5节证明的是下列全部具体数据确实定义原合法策略并达到所列费用。

## 2. 完整正族与四值原地址矩阵

**定义 2.1（宏库存与列次序）。** 记 $X_t=\rho^t\alpha$，宏标签0、1分别表示替换前的 $\alpha,\beta$，替换后分别为

$$
X_3=((\beta,\alpha),\beta),\qquad
X_4=(X_3,(\beta,\alpha)).
$$

两格的宏树及索引直接取[混色卷定义4.2、4.3](FIB_ATOM_MIXED_ACTUAL_ADDRESS_PARTIAL_BOUNDS.md#4-完整有限证书表)。索引字符为 `0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ` 的初段：$(2,2)$ 使用0至T，$(3,1)$ 使用0至J。矩阵每行从左到右严格依此列次序，分别30、20列；$V_i$ 表示该宏树逐叶替换后的正模板。

原引理57.2的单射性和组成反解在这里逐项适用：一步像根 $\beta$ 解为 $\alpha$，特殊对 $(\beta,\alpha)$ 解为 $\beta$，其他像分支递归解码；特殊对不能另解为源分支，因为一步像没有根 $\alpha$。三次替换也单射，且 $\det M^3=-1$，前源组成唯一为 $(a,b)$。四叶有序完整形状恰为

$$
(z,(z,(z,z))),\quad(z,((z,z),z)),\quad((z,z),(z,z)),\quad
((z,(z,z)),z),\quad(((z,z),z).
$$

根分割为 $1+3,2+2,3+1$，三叶有两形，故这五形穷尽。各形全部四位标签中选2个或3个0，分别有 $\binom{4}{2}=6$、$\binom{4}{3}=4$ 种；定义4.2、4.3的库存分别列全 $5\cdot6=30$、$5\cdot4=20$ 棵。单射保证替换后仍无重复，组成反解保证没有遗漏的三次像。索引仅为公共列名，由真实诊断历史选择模板。

**定义 2.2（原矩阵条目的字面规则）。** 用 `a,b,r,x` 分别编码 $\alpha,\beta,\mathsf{br},\varnothing$；`a` 与宏标签0不可混用。沿用原引理57.2，令 $w(u)=\#L(u)+2\#R(u)$，对于 $t\ge2$ 有

$$
r_{X_t}(u)=
\begin{cases}
\mathsf{br},&w(u)\le t-2,\\
\beta,&w(u)=t-1,\\
\alpha,&w(u)=t\text{ 且末字母为 }R,\\
\varnothing,&\text{其余情况}.
\end{cases}
$$

在宏树中尚未到宏叶的端点给 `r`；第一次到颜色 $c\in\{0,1\}$ 的宏叶前缀 $v$ 后，以 $u=vq$ 对剩余后缀 $q$ 使用 $X_{3+c}$ 的上述规则。空后缀仍在块根，给 `r`。这完整保留两种穿叶情形：权重 $t$ 但末步为 $L$ 时已越过索引1的叶；更大的权重也越叶。因此没有省去 `x`。

**定义 2.3（完整原矩阵与行址）。** 共同节点并集的79个地址按先词长、同长按 $L<R$ 排列，行号为0至78。下表同时给出两格全部 $79\cdot30+79\cdot20=3950$ 个四值条目，记为 $R^{22}_{j,i},R^{31}_{j,i}$。行号 $j$ 永远指表中那个字面地址 $u_j$；只在数学表中简写为行号，实际请求必须发送 $u_j$。

| 行号 $j$ | 原地址 $u_j$ | $(2,2)$：0至T | $(3,1)$：0至J |
| --- | --- | --- | --- |
| 0 | $\varepsilon$ | `rrrrrrrrrrrrrrrrrrrrrrrrrrrrrr` | `rrrrrrrrrrrrrrrrrrrr` |
| 1 | `L` | `rrrrrrrrrrrrrrrrrrrrrrrrrrrrrr` | `rrrrrrrrrrrrrrrrrrrr` |
| 2 | `R` | `rrrrrrrrrrrrrrrrrrrrrrrrrrrrrr` | `rrrrrrrrrrrrrrrrrrrr` |
| 3 | `LL` | `rrrrrrrrrrrrrrrrrrrrrrrrrrrrrr` | `rrrrrrrrrrrrrrrrrrrr` |
| 4 | `LR` | `rrrrrrrbbbbbbrrrrrrrrrrrrrrrrr` | `rrbbbbbbrrrrrrrrrrrr` |
| 5 | `RL` | `rrrrrrrrrrrrrrrrrrrrrrrrrrrrrr` | `rrrrrrrrrrrrrrrrrrrr` |
| 6 | `RR` | `rrrrrrrrrrrrrrrrrbbbbbbrrrrrrr` | `rrrrrrrrrrrrbbbbbbrr` |
| 7 | `LLL` | `rrrrrrrbbbbbbrrrrrrrrrrrrrrrrr` | `rrbbbbbbrrrrrrrrrrrr` |
| 8 | `LLR` | `bbbbbbraaaaaarrbbrrrbrrbrbbrrr` | `bbaaaaaarbbbrbbrrrbr` |
| 9 | `LRL` | `bbbbbbrxxxxxxrrrrrrrrrrrrrrrrr` | `bbxxxxxxrrrrrrrrrrrr` |
| 10 | `LRR` | `aaaaaarxxxxxxbbrrrrbrrrbrrrbbr` | `aaxxxxxxbrbbrrrbbrrb` |
| 11 | `RLL` | `rrrrrrrrrrrrrrrrrbbbbbbrrrrrrr` | `rrrrrrrrrrrrbbbbbbrr` |
| 12 | `RLR` | `rbbrrrbrrrbrrrbrbaaaaaarbbbbbb` | `brrbbrrrbbrbaaaaaabb` |
| 13 | `RRL` | `rrrrrrrrrrrrrrrrrxxxxxxrbbbbbb` | `rrrrrrrrrrrrxxxxxxbb` |
| 14 | `RRR` | `rrrbbrbrrbrrrbrbrxxxxxxraaaaaa` | `rbrrrbbrbbbrxxxxxxaa` |
| 15 | `LLLL` | `bbbbbbrxxxxxxrrbbrrrbrrbrbbrrr` | `bbxxxxxxrbbbrbbrrrbr` |
| 16 | `LLLR` | `aaaaaabxxxxxxbbaabbrarbabaarbb` | `aaxxxxxxbaaabaarbbab` |
| 17 | `LLRL` | `xxxxxxbxxxxxxbbxxbbrxrrxbxxrrr` | `xxxxxxxxbxxxbxxrrrxr` |
| 18 | `LLRR` | `xxxxxxaxxxxxxaaxxaarxbrxaxxbrb` | `xxxxxxxxaxxxaxxbrbxb` |
| 19 | `LRLL` | `xxxxxxrxxxxxxbbrrrrbrrrbrrrbbr` | `xxxxxxxxbrbbrrrbbrrb` |
| 20 | `LRLR` | `xxxxxxbxxxxxxaabbrbarbbabrbaab` | `xxxxxxxxabaabrbaabba` |
| 21 | `LRRL` | `xxxxxxbxxxxxxxxbbrrxrbbxrrrxxb` | `xxxxxxxxxbxxrrrxxbrx` |
| 22 | `LRRR` | `xxxxxxaxxxxxxxxaabrxraaxbbrxxa` | `xxxxxxxxxaxxbbrxxabx` |
| 23 | `RLLL` | `rbbrrrbrrrbrrrbrbxxxxxxrbbbbbb` | `brrbbrrrbbrbxxxxxxbb` |
| 24 | `RLLR` | `baarbbabbrarbbabaxxxxxxbaaaaaa` | `abbaarbbaabaxxxxxxaa` |
| 25 | `RLRL` | `bxxrrrxbbrxrrbxbxxxxxxxbxxxxxx` | `xrbxxrrrxxbxxxxxxxxx` |
| 26 | `RLRR` | `axxbrbxaarxbraxaxxxxxxxaxxxxxx` | `xbaxxbrbxxaxxxxxxxxx` |
| 27 | `RRLL` | `rrrbbrbrrbrrrbrbrxxxxxxrxxxxxx` | `rbrrrbbrbbbrxxxxxxxx` |
| 28 | `RRLR` | `brbaabarbarbbababxxxxxxbxxxxxx` | `babrbaabaaabxxxxxxxx` |
| 29 | `RRRL` | `rrrxxbxrrxrbbxbxbxxxxxxbxxxxxx` | `rxrrrxxbxxxbxxxxxxxx` |
| 30 | `RRRR` | `bbrxxaxbrxraaxaxaxxxxxxaxxxxxx` | `bxbbrxxaxxxaxxxxxxxx` |
| 31 | `LLLLL` | `xxxxxxbxxxxxxbbxxbbrxrbxbxxrbb` | `xxxxxxxxbxxxbxxrbbxb` |
| 32 | `LLLLR` | `xxxxxxaxxxxxxaaxxaabxbaxaxxbaa` | `xxxxxxxxaxxxaxxbaaxa` |
| 33 | `LLLRL` | `xxxxxxxxxxxxxxxxxxxbxbxxxxxbxx` | `xxxxxxxxxxxxxxxbxxxx` |
| 34 | `LLLRR` | `xxxxxxxxxxxxxxxxxxxaxaxxxxxaxx` | `xxxxxxxxxxxxxxxaxxxx` |
| 35 | `LLRLL` | `xxxxxxxxxxxxxxxxxxxrxbrxxxxbrb` | `xxxxxxxxxxxxxxxbrbxb` |
| 36 | `LLRLR` | `xxxxxxxxxxxxxxxxxxxbxabxxxxaba` | `xxxxxxxxxxxxxxxabaxa` |
| 37 | `LLRRL` | `xxxxxxxxxxxxxxxxxxxbxxbxxxxxbx` | `xxxxxxxxxxxxxxxxbxxx` |
| 38 | `LLRRR` | `xxxxxxxxxxxxxxxxxxxaxxaxxxxxax` | `xxxxxxxxxxxxxxxxaxxx` |
| 39 | `LRLLL` | `xxxxxxbxxxxxxxxbbrbxrbbxbrbxxb` | `xxxxxxxxxbxxbrbxxbbx` |
| 40 | `LRLLR` | `xxxxxxaxxxxxxxxaabaxbaaxabaxxa` | `xxxxxxxxxaxxabaxxaax` |
| 41 | `LRLRL` | `xxxxxxxxxxxxxxxxxbxxbxxxxbxxxx` | `xxxxxxxxxxxxxbxxxxxx` |
| 42 | `LRLRR` | `xxxxxxxxxxxxxxxxxaxxaxxxxaxxxx` | `xxxxxxxxxxxxxaxxxxxx` |
| 43 | `LRRLL` | `xxxxxxxxxxxxxxxxxbrxrxxxbbrxxx` | `xxxxxxxxxxxxbbrxxxbx` |
| 44 | `LRRLR` | `xxxxxxxxxxxxxxxxxabxbxxxaabxxx` | `xxxxxxxxxxxxaabxxxax` |
| 45 | `LRRRL` | `xxxxxxxxxxxxxxxxxxbxbxxxxxbxxx` | `xxxxxxxxxxxxxxbxxxxx` |
| 46 | `LRRRR` | `xxxxxxxxxxxxxxxxxxaxaxxxxxaxxx` | `xxxxxxxxxxxxxxaxxxxx` |
| 47 | `RLLLL` | `bxxrbbxbbrxrbbxbxxxxxxxbxxxxxx` | `xbbxxrbbxxbxxxxxxxxx` |
| 48 | `RLLLR` | `axxbaaxaabxbaaxaxxxxxxxaxxxxxx` | `xaaxxbaaxxaxxxxxxxxx` |
| 49 | `RLLRL` | `xxxbxxxxxbxbxxxxxxxxxxxxxxxxxx` | `xxxxxbxxxxxxxxxxxxxx` |
| 50 | `RLLRR` | `xxxaxxxxxaxaxxxxxxxxxxxxxxxxxx` | `xxxxxaxxxxxxxxxxxxxx` |
| 51 | `RLRLL` | `xxxbrbxxxrxbrxxxxxxxxxxxxxxxxx` | `xbxxxbrbxxxxxxxxxxxx` |
| 52 | `RLRLR` | `xxxabaxxxbxabxxxxxxxxxxxxxxxxx` | `xaxxxabaxxxxxxxxxxxx` |
| 53 | `RLRRL` | `xxxxbxxxxbxxbxxxxxxxxxxxxxxxxx` | `xxxxxxbxxxxxxxxxxxxx` |
| 54 | `RLRRR` | `xxxxaxxxxaxxaxxxxxxxxxxxxxxxxx` | `xxxxxxaxxxxxxxxxxxxx` |
| 55 | `RRLLL` | `brbxxbxrbxrbbxbxbxxxxxxbxxxxxx` | `bxbrbxxbxxxbxxxxxxxx` |
| 56 | `RRLLR` | `abaxxaxbaxbaaxaxaxxxxxxaxxxxxx` | `axabaxxaxxxaxxxxxxxx` |
| 57 | `RRLRL` | `xbxxxxxbxxbxxxxxxxxxxxxxxxxxxx` | `xxxbxxxxxxxxxxxxxxxx` |
| 58 | `RRLRR` | `xaxxxxxaxxaxxxxxxxxxxxxxxxxxxx` | `xxxaxxxxxxxxxxxxxxxx` |
| 59 | `RRRLL` | `bbrxxxxbrxrxxxxxxxxxxxxxxxxxxx` | `bxbbrxxxxxxxxxxxxxxx` |
| 60 | `RRRLR` | `aabxxxxabxbxxxxxxxxxxxxxxxxxxx` | `axaabxxxxxxxxxxxxxxx` |
| 61 | `RRRRL` | `xxbxxxxxbxbxxxxxxxxxxxxxxxxxxx` | `xxxxbxxxxxxxxxxxxxxx` |
| 62 | `RRRRR` | `xxaxxxxxaxaxxxxxxxxxxxxxxxxxxx` | `xxxxaxxxxxxxxxxxxxxx` |
| 63 | `LLLLLL` | `xxxxxxxxxxxxxxxxxxxbxbxxxxxbxx` | `xxxxxxxxxxxxxxxbxxxx` |
| 64 | `LLLLLR` | `xxxxxxxxxxxxxxxxxxxaxaxxxxxaxx` | `xxxxxxxxxxxxxxxaxxxx` |
| 65 | `LLRLLL` | `xxxxxxxxxxxxxxxxxxxbxxbxxxxxbx` | `xxxxxxxxxxxxxxxxbxxx` |
| 66 | `LLRLLR` | `xxxxxxxxxxxxxxxxxxxaxxaxxxxxax` | `xxxxxxxxxxxxxxxxaxxx` |
| 67 | `LRLLLL` | `xxxxxxxxxxxxxxxxxbxxbxxxxbxxxx` | `xxxxxxxxxxxxxbxxxxxx` |
| 68 | `LRLLLR` | `xxxxxxxxxxxxxxxxxaxxaxxxxaxxxx` | `xxxxxxxxxxxxxaxxxxxx` |
| 69 | `LRRLLL` | `xxxxxxxxxxxxxxxxxxbxbxxxxxbxxx` | `xxxxxxxxxxxxxxbxxxxx` |
| 70 | `LRRLLR` | `xxxxxxxxxxxxxxxxxxaxaxxxxxaxxx` | `xxxxxxxxxxxxxxaxxxxx` |
| 71 | `RLLLLL` | `xxxbxxxxxbxbxxxxxxxxxxxxxxxxxx` | `xxxxxbxxxxxxxxxxxxxx` |
| 72 | `RLLLLR` | `xxxaxxxxxaxaxxxxxxxxxxxxxxxxxx` | `xxxxxaxxxxxxxxxxxxxx` |
| 73 | `RLRLLL` | `xxxxbxxxxbxxbxxxxxxxxxxxxxxxxx` | `xxxxxxbxxxxxxxxxxxxx` |
| 74 | `RLRLLR` | `xxxxaxxxxaxxaxxxxxxxxxxxxxxxxx` | `xxxxxxaxxxxxxxxxxxxx` |
| 75 | `RRLLLL` | `xbxxxxxbxxbxxxxxxxxxxxxxxxxxxx` | `xxxbxxxxxxxxxxxxxxxx` |
| 76 | `RRLLLR` | `xaxxxxxaxxaxxxxxxxxxxxxxxxxxxx` | `xxxaxxxxxxxxxxxxxxxx` |
| 77 | `RRRLLL` | `xxbxxxxxbxbxxxxxxxxxxxxxxxxxxx` | `xxxxbxxxxxxxxxxxxxxx` |
| 78 | `RRRLLR` | `xxaxxxxxaxaxxxxxxxxxxxxxxxxxxx` | `xxxxaxxxxxxxxxxxxxxx` |

**定义 2.4（无损行分类与原权限）。** 两格均有5个共同 `r` 行：0、1、2、3、5。56个非恒定代表的行号为4、6、8、9、10及12至62；亦即按定义2.3行号依次选取的 `LR,RR,LLR,LRL,LRR` 及行12至62的原词。其余18行与较早行的完整向量相同，两格对应关系如下；代表子矩阵即定义2.3的这些行，不另复制。

| 重复行 | 原地址 | 代表行 | 代表原地址 |
| --- | --- | --- | --- |
| 7 | `LLL` | 4 | `LR` |
| 11 | `RLL` | 6 | `RR` |
| 63 | `LLLLLL` | 33 | `LLLRL` |
| 64 | `LLLLLR` | 34 | `LLLRR` |
| 65 | `LLRLLL` | 37 | `LLRRL` |
| 66 | `LLRLLR` | 38 | `LLRRR` |
| 67 | `LRLLLL` | 41 | `LRLRL` |
| 68 | `LRLLLR` | 42 | `LRLRR` |
| 69 | `LRRLLL` | 45 | `LRRRL` |
| 70 | `LRRLLR` | 46 | `LRRRR` |
| 71 | `RLLLLL` | 49 | `RLLRL` |
| 72 | `RLLLLR` | 50 | `RLLRR` |
| 73 | `RLRLLL` | 53 | `RLRRL` |
| 74 | `RLRLLR` | 54 | `RLRRR` |
| 75 | `RRLLLL` | 57 | `RRLRL` |
| 76 | `RRLLLR` | 58 | `RRLRR` |
| 77 | `RRRLLL` | 61 | `RRRRL` |
| 78 | `RRRLLR` | 62 | `RRRRR` |

深度不超过5的全部63个词均已列入原矩阵；深度6有16个已列词，其余48个原词如下，全部正源上的回复为 `x`。每行按所列前缀分组，表内列全该组的字面词。

| 前三字母 | 未在节点并集内的全部深度6词 |
| --- | --- |
| `LLL` | `LLLLRL,LLLLRR,LLLRLL,LLLRLR,LLLRRL,LLLRRR` |
| `LLR` | `LLRLRL,LLRLRR,LLRRLL,LLRRLR,LLRRRL,LLRRRR` |
| `LRL` | `LRLLRL,LRLLRR,LRLRLL,LRLRLR,LRLRRL,LRLRRR` |
| `LRR` | `LRRLRL,LRRLRR,LRRRLL,LRRRLR,LRRRRL,LRRRRR` |
| `RLL` | `RLLLRL,RLLLRR,RLLRLL,RLLRLR,RLLRRL,RLLRRR` |
| `RLR` | `RLRLRL,RLRLRR,RLRRLL,RLRRLR,RLRRRL,RLRRRR` |
| `RRL` | `RRLLRL,RRLLRR,RRLRLL,RRLRLR,RRLRRL,RRLRRR` |
| `RRR` | `RRRLRL,RRRLRR,RRRRLL,RRRRLR,RRRRRL,RRRRRR` |

所有深度大于6的有限词在正族上也共同给 `x`，因为正源高度至多6。上述分类只描述公共正族的回复纤维；原 $\mathcal T_C$、所有合法有限词和四值回复均保留。两个不同原地址即使行向量相同，也不是同一已付地址，缓存不可沿重复行免费迁移。$(2,2)$ 的诊断使用行8、10、14、16、18、22、24、26、28、30、32；$(3,1)$ 使用行9、10、13、14、16、18、20、24、26、28。使用子矩阵按这些原行引用。

## 3. 两张完整诊断表与逐边界

**定义 3.1（有限诊断节点和边的读法）。** 每格节点编号 $t_0,t_1,\ldots$ 只在该格内使用。节点表给到达索引集 $S$、实际字面请求 $u$、剩余非 $\alpha$ 界 $b(S)$。每条已列边给完整回复桶 $S_y$、孩子及其界；单元素孩子 $[i]$ 只选择模板 $V_i$，界为0，尚未接受。边表的 $\delta=\mathbf1_{y\ne a}$ 是非 $\alpha$ 指示贡献，不是请求收费的替代规则；每个实际请求仍收费。逐边总量为 $\delta+b(S_y)$，不超过父界。

从 $t_0$ 的全索引集开始，每次实际查询后把原词和四值回复追加到历史，再按边表继续。节点表“拒绝回复”列出的所有未列回复立即返回假；`—` 表示该节点四值边全列。只认本次真实历史中的回复。

**定义 3.2（(2,2) 的完整诊断）。** 下列15个节点与44条边组成该格的诊断。

| 节点 | 到达索引 $S$ | 实际请求 $u$ | 父界 $b(S)$ | 拒绝回复 |
| --- | --- | --- | --- | --- |
| $t_0$ | `0,1,2,3,4,5,6,7,8,9,A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T` | `LLR` | 3 | `x` |
| $t_1$ | `7,8,9,A,B,C` | `RLLR` | 2 | `x` |
| $t_2$ | `7,8,C` | `RRRR` | 1 | `x` |
| $t_3$ | `9,B` | `RRR` | 1 | `a,x` |
| $t_4$ | `0,1,2,3,4,5,F,G,K,N,P,Q` | `RLLR` | 2 | — |
| $t_5$ | `1,2,G,P,Q` | `LRRR` | 2 | — |
| $t_6$ | `1,2` | `RRLR` | 1 | `a,x` |
| $t_7$ | `0,4,5,F,N` | `LRR` | 1 | `x` |
| $t_8$ | `0,4,5` | `RLRR` | 1 | `x` |
| $t_9$ | `6,D,E,H,I,J,L,M,O,R,S,T` | `RRR` | 2 | — |
| $t_10$ | `O,R,S,T` | `LLLLR` | 1 | `r,x` |
| $t_11$ | `O,S,T` | `LLRR` | 1 | `x` |
| $t_12$ | `6,D` | `LRR` | 1 | `a,x` |
| $t_13$ | `H,I,J,L,M` | `LRRR` | 1 | — |
| $t_14$ | `L,M` | `LLLR` | 1 | `a,x` |

| 父节点 | 实际请求 | 回复 $y$ | 完整桶 $S_y$ | 孩子 | 父界 | 孩子界 | $\delta$ | $\delta+$孩子界 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $t_0$ | `LLR` | `a` | `7,8,9,A,B,C` | $t_1$ | 3 | 2 | 0 | 2 |
| $t_0$ | `LLR` | `b` | `0,1,2,3,4,5,F,G,K,N,P,Q` | $t_4$ | 3 | 2 | 1 | 3 |
| $t_0$ | `LLR` | `r` | `6,D,E,H,I,J,L,M,O,R,S,T` | $t_9$ | 3 | 2 | 1 | 3 |
| $t_1$ | `RLLR` | `a` | `A` | `[A]` | 2 | 0 | 0 | 0 |
| $t_1$ | `RLLR` | `b` | `7,8,C` | $t_2$ | 2 | 1 | 1 | 2 |
| $t_1$ | `RLLR` | `r` | `9,B` | $t_3$ | 2 | 1 | 1 | 2 |
| $t_2$ | `RRRR` | `a` | `C` | `[C]` | 1 | 0 | 0 | 0 |
| $t_2$ | `RRRR` | `b` | `7` | `[7]` | 1 | 0 | 1 | 1 |
| $t_2$ | `RRRR` | `r` | `8` | `[8]` | 1 | 0 | 1 | 1 |
| $t_3$ | `RRR` | `b` | `9` | `[9]` | 1 | 0 | 1 | 1 |
| $t_3$ | `RRR` | `r` | `B` | `[B]` | 1 | 0 | 1 | 1 |
| $t_4$ | `RLLR` | `a` | `1,2,G,P,Q` | $t_5$ | 2 | 2 | 0 | 2 |
| $t_4$ | `RLLR` | `b` | `0,4,5,F,N` | $t_7$ | 2 | 1 | 1 | 2 |
| $t_4$ | `RLLR` | `r` | `3` | `[3]` | 2 | 0 | 1 | 1 |
| $t_4$ | `RLLR` | `x` | `K` | `[K]` | 2 | 0 | 1 | 1 |
| $t_5$ | `LRRR` | `a` | `G` | `[G]` | 2 | 0 | 0 | 0 |
| $t_5$ | `LRRR` | `b` | `P` | `[P]` | 2 | 0 | 1 | 1 |
| $t_5$ | `LRRR` | `r` | `Q` | `[Q]` | 2 | 0 | 1 | 1 |
| $t_5$ | `LRRR` | `x` | `1,2` | $t_6$ | 2 | 1 | 1 | 2 |
| $t_6$ | `RRLR` | `b` | `2` | `[2]` | 1 | 0 | 1 | 1 |
| $t_6$ | `RRLR` | `r` | `1` | `[1]` | 1 | 0 | 1 | 1 |
| $t_7$ | `LRR` | `a` | `0,4,5` | $t_8$ | 1 | 1 | 0 | 1 |
| $t_7$ | `LRR` | `b` | `N` | `[N]` | 1 | 0 | 1 | 1 |
| $t_7$ | `LRR` | `r` | `F` | `[F]` | 1 | 0 | 1 | 1 |
| $t_8$ | `RLRR` | `a` | `0` | `[0]` | 1 | 0 | 0 | 0 |
| $t_8$ | `RLRR` | `b` | `5` | `[5]` | 1 | 0 | 1 | 1 |
| $t_8$ | `RLRR` | `r` | `4` | `[4]` | 1 | 0 | 1 | 1 |
| $t_9$ | `RRR` | `a` | `O,R,S,T` | $t_10$ | 2 | 1 | 0 | 1 |
| $t_9$ | `RRR` | `b` | `6,D` | $t_12$ | 2 | 1 | 1 | 2 |
| $t_9$ | `RRR` | `r` | `E` | `[E]` | 2 | 0 | 1 | 1 |
| $t_9$ | `RRR` | `x` | `H,I,J,L,M` | $t_13$ | 2 | 1 | 1 | 2 |
| $t_10$ | `LLLLR` | `a` | `O,S,T` | $t_11$ | 1 | 1 | 0 | 1 |
| $t_10$ | `LLLLR` | `b` | `R` | `[R]` | 1 | 0 | 1 | 1 |
| $t_11$ | `LLRR` | `a` | `O` | `[O]` | 1 | 0 | 0 | 0 |
| $t_11$ | `LLRR` | `b` | `T` | `[T]` | 1 | 0 | 1 | 1 |
| $t_11$ | `LLRR` | `r` | `S` | `[S]` | 1 | 0 | 1 | 1 |
| $t_12$ | `LRR` | `b` | `D` | `[D]` | 1 | 0 | 1 | 1 |
| $t_12$ | `LRR` | `r` | `6` | `[6]` | 1 | 0 | 1 | 1 |
| $t_13$ | `LRRR` | `a` | `L,M` | $t_14$ | 1 | 1 | 0 | 1 |
| $t_13$ | `LRRR` | `b` | `H` | `[H]` | 1 | 0 | 1 | 1 |
| $t_13$ | `LRRR` | `r` | `I` | `[I]` | 1 | 0 | 1 | 1 |
| $t_13$ | `LRRR` | `x` | `J` | `[J]` | 1 | 0 | 1 | 1 |
| $t_14$ | `LLLR` | `b` | `M` | `[M]` | 1 | 0 | 1 | 1 |
| $t_14$ | `LLLR` | `r` | `L` | `[L]` | 1 | 0 | 1 | 1 |

**定义 3.3（(3,1) 的完整诊断）。** 下列10个节点与29条边组成该格的诊断。

| 节点 | 到达索引 $S$ | 实际请求 $u$ | 父界 $b(S)$ | 拒绝回复 |
| --- | --- | --- | --- | --- |
| $t_0$ | `0,1,2,3,4,5,6,7,8,9,A,B,C,D,E,F,G,H,I,J` | `LLLR` | 3 | — |
| $t_1$ | `0,1,9,A,B,D,E,I` | `RRR` | 2 | — |
| $t_2$ | `1,9,A` | `LRR` | 1 | `x` |
| $t_3$ | `0,B` | `LRL` | 1 | `a,x` |
| $t_4$ | `D,E` | `LRLR` | 1 | `a,x` |
| $t_5$ | `8,C,G,H,J` | `RRL` | 2 | `a` |
| $t_6$ | `C,G,H` | `LLRR` | 1 | `x` |
| $t_7$ | `2,3,4,5,6,7` | `RLLR` | 2 | `x` |
| $t_8$ | `3,4` | `RRLR` | 1 | `a,x` |
| $t_9$ | `2,6,7` | `RLRR` | 1 | `x` |

| 父节点 | 实际请求 | 回复 $y$ | 完整桶 $S_y$ | 孩子 | 父界 | 孩子界 | $\delta$ | $\delta+$孩子界 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $t_0$ | `LLLR` | `a` | `0,1,9,A,B,D,E,I` | $t_1$ | 3 | 2 | 0 | 2 |
| $t_0$ | `LLLR` | `b` | `8,C,G,H,J` | $t_5$ | 3 | 2 | 1 | 3 |
| $t_0$ | `LLLR` | `r` | `F` | `[F]` | 3 | 0 | 1 | 1 |
| $t_0$ | `LLLR` | `x` | `2,3,4,5,6,7` | $t_7$ | 3 | 2 | 1 | 3 |
| $t_1$ | `RRR` | `a` | `I` | `[I]` | 2 | 0 | 0 | 0 |
| $t_1$ | `RRR` | `b` | `1,9,A` | $t_2$ | 2 | 1 | 1 | 2 |
| $t_1$ | `RRR` | `r` | `0,B` | $t_3$ | 2 | 1 | 1 | 2 |
| $t_1$ | `RRR` | `x` | `D,E` | $t_4$ | 2 | 1 | 1 | 2 |
| $t_2$ | `LRR` | `a` | `1` | `[1]` | 1 | 0 | 0 | 0 |
| $t_2$ | `LRR` | `b` | `A` | `[A]` | 1 | 0 | 1 | 1 |
| $t_2$ | `LRR` | `r` | `9` | `[9]` | 1 | 0 | 1 | 1 |
| $t_3$ | `LRL` | `b` | `0` | `[0]` | 1 | 0 | 1 | 1 |
| $t_3$ | `LRL` | `r` | `B` | `[B]` | 1 | 0 | 1 | 1 |
| $t_4$ | `LRLR` | `b` | `E` | `[E]` | 1 | 0 | 1 | 1 |
| $t_4$ | `LRLR` | `r` | `D` | `[D]` | 1 | 0 | 1 | 1 |
| $t_5$ | `RRL` | `b` | `J` | `[J]` | 2 | 0 | 1 | 1 |
| $t_5$ | `RRL` | `r` | `8` | `[8]` | 2 | 0 | 1 | 1 |
| $t_5$ | `RRL` | `x` | `C,G,H` | $t_6$ | 2 | 1 | 1 | 2 |
| $t_6$ | `LLRR` | `a` | `C` | `[C]` | 1 | 0 | 0 | 0 |
| $t_6$ | `LLRR` | `b` | `H` | `[H]` | 1 | 0 | 1 | 1 |
| $t_6$ | `LLRR` | `r` | `G` | `[G]` | 1 | 0 | 1 | 1 |
| $t_7$ | `RLLR` | `a` | `3,4` | $t_8$ | 2 | 1 | 0 | 1 |
| $t_7$ | `RLLR` | `b` | `2,6,7` | $t_9$ | 2 | 1 | 1 | 2 |
| $t_7$ | `RLLR` | `r` | `5` | `[5]` | 2 | 0 | 1 | 1 |
| $t_8$ | `RRLR` | `b` | `4` | `[4]` | 1 | 0 | 1 | 1 |
| $t_8$ | `RRLR` | `r` | `3` | `[3]` | 1 | 0 | 1 | 1 |
| $t_9$ | `RLRR` | `a` | `2` | `[2]` | 1 | 0 | 0 | 0 |
| $t_9$ | `RLRR` | `b` | `7` | `[7]` | 1 | 0 | 1 | 1 |
| $t_9$ | `RLRR` | `r` | `6` | `[6]` | 1 | 0 | 1 | 1 |

## 4. 全部两色前沿及实际付费清单

**定义 4.1（全部前沿的原矩阵坐标）。** 对每格每个索引 $i$，定义

$$
\mathcal A(V_i)=\{u_j:R_{j,i}=a\},\qquad
\mathcal B(V_i)=\{u_j:R_{j,i}=b\}.
$$

下表列全这50个源的两色前沿行号，按原地址的普通字典序 $L<R$ 排列；因此行号在一格内不必递增。把行号代回定义2.3即可逐字恢复完整字面集合。每行 $\alpha$ 数为6或5，$\beta$ 数为10或9。表列的是公共模板；前沿回复必须由真实请求获得。

| 格 | 源索引 | $\alpha$ 前沿行号 | $\beta$ 前沿行号 |
| --- | --- | --- | --- |
| $(2,2)$ | 0 | `16,10,48,26,56,60` | `15,8,9,47,24,25,55,28,59,30` |
| $(2,2)$ | 1 | `16,10,24,76,58,60` | `15,8,9,23,12,75,56,57,59,30` |
| $(2,2)$ | 2 | `16,10,24,56,78,62` | `15,8,9,23,12,55,28,77,60,61` |
| $(2,2)$ | 3 | `16,10,72,50,52,28` | `15,8,9,71,48,49,51,26,27,14` |
| $(2,2)$ | 4 | `16,10,48,74,54,28` | `15,8,9,47,24,73,52,53,27,14` |
| $(2,2)$ | 5 | `16,10,48,52,56,30` | `15,8,9,47,24,51,26,55,28,29` |
| $(2,2)$ | 6 | `32,18,40,22,24,28` | `31,16,17,39,20,21,23,12,27,14` |
| $(2,2)$ | 7 | `8,48,26,76,58,60` | `7,4,47,24,25,75,56,57,59,30` |
| $(2,2)$ | 8 | `8,48,26,56,78,62` | `7,4,47,24,25,55,28,77,60,61` |
| $(2,2)$ | 9 | `8,72,50,74,54,28` | `7,4,71,48,49,73,52,53,27,14` |
| $(2,2)$ | A | `8,24,76,58,78,62` | `7,4,23,12,75,56,57,77,60,61` |
| $(2,2)$ | B | `8,72,50,52,56,30` | `7,4,71,48,49,51,26,55,28,29` |
| $(2,2)$ | C | `8,48,74,54,56,30` | `7,4,47,24,73,52,53,55,28,29` |
| $(2,2)$ | D | `32,18,20,48,26,28` | `31,16,17,19,10,47,24,25,27,14` |
| $(2,2)$ | E | `32,18,20,24,56,30` | `31,16,17,19,10,23,12,55,28,29` |
| $(2,2)$ | F | `16,40,22,48,26,28` | `15,8,39,20,21,47,24,25,27,14` |
| $(2,2)$ | G | `16,40,22,24,56,30` | `15,8,39,20,21,23,12,55,28,29` |
| $(2,2)$ | H | `32,18,68,42,44,12` | `31,16,17,67,40,41,43,22,11,6` |
| $(2,2)$ | I | `32,18,40,70,46,12` | `31,16,17,39,20,69,44,45,11,6` |
| $(2,2)$ | J | `64,34,66,38,20,12` | `63,32,33,65,36,37,19,10,11,6` |
| $(2,2)$ | K | `16,68,42,70,46,12` | `15,8,67,40,41,69,44,45,11,6` |
| $(2,2)$ | L | `64,34,36,40,22,12` | `63,32,33,35,18,39,20,21,11,6` |
| $(2,2)$ | M | `32,66,38,40,22,12` | `31,16,65,36,37,39,20,21,11,6` |
| $(2,2)$ | N | `16,20,48,26,56,30` | `15,8,19,10,47,24,25,55,28,29` |
| $(2,2)$ | O | `32,18,40,44,24,14` | `31,16,17,39,20,43,22,23,12,13` |
| $(2,2)$ | P | `16,68,42,44,24,14` | `15,8,67,40,41,43,22,23,12,13` |
| $(2,2)$ | Q | `16,40,70,46,24,14` | `15,8,39,20,69,44,45,23,12,13` |
| $(2,2)$ | R | `64,34,36,20,24,14` | `63,32,33,35,18,19,10,23,12,13` |
| $(2,2)$ | S | `32,66,38,20,24,14` | `31,16,65,36,37,19,10,23,12,13` |
| $(2,2)$ | T | `32,36,40,22,24,14` | `31,16,35,18,39,20,21,23,12,13` |
| $(3,1)$ | 0 | `16,10,24,56,60` | `15,8,9,23,12,55,28,59,30` |
| $(3,1)$ | 1 | `16,10,48,52,28` | `15,8,9,47,24,51,26,27,14` |
| $(3,1)$ | 2 | `8,48,26,56,60` | `7,4,47,24,25,55,28,59,30` |
| $(3,1)$ | 3 | `8,24,76,58,60` | `7,4,23,12,75,56,57,59,30` |
| $(3,1)$ | 4 | `8,24,56,78,62` | `7,4,23,12,55,28,77,60,61` |
| $(3,1)$ | 5 | `8,72,50,52,28` | `7,4,71,48,49,51,26,27,14` |
| $(3,1)$ | 6 | `8,48,74,54,28` | `7,4,47,24,73,52,53,27,14` |
| $(3,1)$ | 7 | `8,48,52,56,30` | `7,4,47,24,51,26,55,28,29` |
| $(3,1)$ | 8 | `32,18,20,24,28` | `31,16,17,19,10,23,12,27,14` |
| $(3,1)$ | 9 | `16,40,22,24,28` | `15,8,39,20,21,23,12,27,14` |
| $(3,1)$ | A | `16,20,48,26,28` | `15,8,19,10,47,24,25,27,14` |
| $(3,1)$ | B | `16,20,24,56,30` | `15,8,19,10,23,12,55,28,29` |
| $(3,1)$ | C | `32,18,40,44,12` | `31,16,17,39,20,43,22,11,6` |
| $(3,1)$ | D | `16,68,42,44,12` | `15,8,67,40,41,43,22,11,6` |
| $(3,1)$ | E | `16,40,70,46,12` | `15,8,39,20,69,44,45,11,6` |
| $(3,1)$ | F | `64,34,36,20,12` | `63,32,33,35,18,19,10,11,6` |
| $(3,1)$ | G | `32,66,38,20,12` | `31,16,65,36,37,19,10,11,6` |
| $(3,1)$ | H | `32,36,40,22,12` | `31,16,35,18,39,20,21,11,6` |
| $(3,1)$ | I | `16,40,44,24,14` | `15,8,39,20,43,22,23,12,13` |
| $(3,1)$ | J | `32,36,20,24,14` | `31,16,35,18,19,10,23,12,13` |

**定义 4.2（真实缓存、补查与全部50条运行）。** 诊断到达 $[i]$ 后按定义4.1的字典序遍历 $\mathcal A(V_i)$。若同一原字已在本次实际历史中，只检查缓存中的真实回复是否为 `a`；若未请求，必须实际请求该字，追加真实回复并要求 `a`。任一不符立即拒绝，全部通过才接受。公共 singleton 不代替这个完整检查。

下表每格每源给一条完整按时序实际地址／回复清单：`D[...]` 是诊断段，紧接的 `C[...]` 是实际补查段，两段的串接就是完整 paid 请求列表，没有省略项。每个 `u:y` 发送字面 $u$ 并获得真实 $y$；分段标记本身不是动作。缓存列仅列诊断已查的 `a` 行号，这些真实记录参与最终检查，不再请求。$q_{\ne\alpha}$ 是诊断中不同非 $\alpha$ 地址数，paid 列是整个列表的不同原地址数；本构造没有重复，因此也等于完整动作数。所有 $\alpha$ 前沿都分别出现在诊断或补查段。

| 格 | 源索引 | 完整 paid 时序（诊断；补查） | 已查 $\alpha$ 缓存行号 | $q_{\ne\alpha}$ | paid |
| --- | --- | --- | --- | --- | --- |
| $(2,2)$ | 0 | `D[LLR:b RLLR:b LRR:a RLRR:a]; C[LLLR:a RLLLR:a RRLLR:a RRRLR:a]` | `10,26` | 2 | 8 |
| $(2,2)$ | 1 | `D[LLR:b RLLR:a LRRR:x RRLR:r]; C[LLLR:a LRR:a RRLLLR:a RRLRR:a RRRLR:a]` | `24` | 3 | 9 |
| $(2,2)$ | 2 | `D[LLR:b RLLR:a LRRR:x RRLR:b]; C[LLLR:a LRR:a RRLLR:a RRRLLR:a RRRRR:a]` | `24` | 3 | 9 |
| $(2,2)$ | 3 | `D[LLR:b RLLR:r]; C[LLLR:a LRR:a RLLLLR:a RLLRR:a RLRLR:a RRLR:a]` | 无 | 2 | 8 |
| $(2,2)$ | 4 | `D[LLR:b RLLR:b LRR:a RLRR:r]; C[LLLR:a RLLLR:a RLRLLR:a RLRRR:a RRLR:a]` | `10` | 3 | 9 |
| $(2,2)$ | 5 | `D[LLR:b RLLR:b LRR:a RLRR:b]; C[LLLR:a RLLLR:a RLRLR:a RRLLR:a RRRR:a]` | `10` | 3 | 9 |
| $(2,2)$ | 6 | `D[LLR:r RRR:b LRR:r]; C[LLLLR:a LLRR:a LRLLR:a LRRR:a RLLR:a RRLR:a]` | 无 | 3 | 9 |
| $(2,2)$ | 7 | `D[LLR:a RLLR:b RRRR:b]; C[RLLLR:a RLRR:a RRLLLR:a RRLRR:a RRRLR:a]` | `8` | 2 | 8 |
| $(2,2)$ | 8 | `D[LLR:a RLLR:b RRRR:r]; C[RLLLR:a RLRR:a RRLLR:a RRRLLR:a RRRRR:a]` | `8` | 2 | 8 |
| $(2,2)$ | 9 | `D[LLR:a RLLR:r RRR:b]; C[RLLLLR:a RLLRR:a RLRLLR:a RLRRR:a RRLR:a]` | `8` | 2 | 8 |
| $(2,2)$ | A | `D[LLR:a RLLR:a]; C[RRLLLR:a RRLRR:a RRRLLR:a RRRRR:a]` | `8,24` | 0 | 6 |
| $(2,2)$ | B | `D[LLR:a RLLR:r RRR:r]; C[RLLLLR:a RLLRR:a RLRLR:a RRLLR:a RRRR:a]` | `8` | 2 | 8 |
| $(2,2)$ | C | `D[LLR:a RLLR:b RRRR:a]; C[RLLLR:a RLRLLR:a RLRRR:a RRLLR:a]` | `8,30` | 1 | 7 |
| $(2,2)$ | D | `D[LLR:r RRR:b LRR:b]; C[LLLLR:a LLRR:a LRLR:a RLLLR:a RLRR:a RRLR:a]` | 无 | 3 | 9 |
| $(2,2)$ | E | `D[LLR:r RRR:r]; C[LLLLR:a LLRR:a LRLR:a RLLR:a RRLLR:a RRRR:a]` | 无 | 2 | 8 |
| $(2,2)$ | F | `D[LLR:b RLLR:b LRR:r]; C[LLLR:a LRLLR:a LRRR:a RLLLR:a RLRR:a RRLR:a]` | 无 | 3 | 9 |
| $(2,2)$ | G | `D[LLR:b RLLR:a LRRR:a]; C[LLLR:a LRLLR:a RRLLR:a RRRR:a]` | `24,22` | 1 | 7 |
| $(2,2)$ | H | `D[LLR:r RRR:x LRRR:b]; C[LLLLR:a LLRR:a LRLLLR:a LRLRR:a LRRLR:a RLR:a]` | 无 | 3 | 9 |
| $(2,2)$ | I | `D[LLR:r RRR:x LRRR:r]; C[LLLLR:a LLRR:a LRLLR:a LRRLLR:a LRRRR:a RLR:a]` | 无 | 3 | 9 |
| $(2,2)$ | J | `D[LLR:r RRR:x LRRR:x]; C[LLLLLR:a LLLRR:a LLRLLR:a LLRRR:a LRLR:a RLR:a]` | 无 | 3 | 9 |
| $(2,2)$ | K | `D[LLR:b RLLR:x]; C[LLLR:a LRLLLR:a LRLRR:a LRRLLR:a LRRRR:a RLR:a]` | 无 | 2 | 8 |
| $(2,2)$ | L | `D[LLR:r RRR:x LRRR:a LLLR:r]; C[LLLLLR:a LLLRR:a LLRLR:a LRLLR:a RLR:a]` | `22` | 3 | 9 |
| $(2,2)$ | M | `D[LLR:r RRR:x LRRR:a LLLR:b]; C[LLLLR:a LLRLLR:a LLRRR:a LRLLR:a RLR:a]` | `22` | 3 | 9 |
| $(2,2)$ | N | `D[LLR:b RLLR:b LRR:b]; C[LLLR:a LRLR:a RLLLR:a RLRR:a RRLLR:a RRRR:a]` | 无 | 3 | 9 |
| $(2,2)$ | O | `D[LLR:r RRR:a LLLLR:a LLRR:a]; C[LRLLR:a LRRLR:a RLLR:a]` | `14,32,18` | 1 | 7 |
| $(2,2)$ | P | `D[LLR:b RLLR:a LRRR:b]; C[LLLR:a LRLLLR:a LRLRR:a LRRLR:a RRR:a]` | `24` | 2 | 8 |
| $(2,2)$ | Q | `D[LLR:b RLLR:a LRRR:r]; C[LLLR:a LRLLR:a LRRLLR:a LRRRR:a RRR:a]` | `24` | 2 | 8 |
| $(2,2)$ | R | `D[LLR:r RRR:a LLLLR:b]; C[LLLLLR:a LLLRR:a LLRLR:a LRLR:a RLLR:a]` | `14` | 2 | 8 |
| $(2,2)$ | S | `D[LLR:r RRR:a LLLLR:a LLRR:r]; C[LLRLLR:a LLRRR:a LRLR:a RLLR:a]` | `14,32` | 2 | 8 |
| $(2,2)$ | T | `D[LLR:r RRR:a LLLLR:a LLRR:b]; C[LLRLR:a LRLLR:a LRRR:a RLLR:a]` | `14,32` | 2 | 8 |
| $(3,1)$ | 0 | `D[LLLR:a RRR:r LRL:b]; C[LRR:a RLLR:a RRLLR:a RRRLR:a]` | `16` | 2 | 7 |
| $(3,1)$ | 1 | `D[LLLR:a RRR:b LRR:a]; C[RLLLR:a RLRLR:a RRLR:a]` | `16,10` | 1 | 6 |
| $(3,1)$ | 2 | `D[LLLR:x RLLR:b RLRR:a]; C[LLR:a RLLLR:a RRLLR:a RRRLR:a]` | `26` | 2 | 7 |
| $(3,1)$ | 3 | `D[LLLR:x RLLR:a RRLR:r]; C[LLR:a RRLLLR:a RRLRR:a RRRLR:a]` | `24` | 2 | 7 |
| $(3,1)$ | 4 | `D[LLLR:x RLLR:a RRLR:b]; C[LLR:a RRLLR:a RRRLLR:a RRRRR:a]` | `24` | 2 | 7 |
| $(3,1)$ | 5 | `D[LLLR:x RLLR:r]; C[LLR:a RLLLLR:a RLLRR:a RLRLR:a RRLR:a]` | 无 | 2 | 7 |
| $(3,1)$ | 6 | `D[LLLR:x RLLR:b RLRR:r]; C[LLR:a RLLLR:a RLRLLR:a RLRRR:a RRLR:a]` | 无 | 3 | 8 |
| $(3,1)$ | 7 | `D[LLLR:x RLLR:b RLRR:b]; C[LLR:a RLLLR:a RLRLR:a RRLLR:a RRRR:a]` | 无 | 3 | 8 |
| $(3,1)$ | 8 | `D[LLLR:b RRL:r]; C[LLLLR:a LLRR:a LRLR:a RLLR:a RRLR:a]` | 无 | 2 | 7 |
| $(3,1)$ | 9 | `D[LLLR:a RRR:b LRR:r]; C[LRLLR:a LRRR:a RLLR:a RRLR:a]` | `16` | 2 | 7 |
| $(3,1)$ | A | `D[LLLR:a RRR:b LRR:b]; C[LRLR:a RLLLR:a RLRR:a RRLR:a]` | `16` | 2 | 7 |
| $(3,1)$ | B | `D[LLLR:a RRR:r LRL:r]; C[LRLR:a RLLR:a RRLLR:a RRRR:a]` | `16` | 2 | 7 |
| $(3,1)$ | C | `D[LLLR:b RRL:x LLRR:a]; C[LLLLR:a LRLLR:a LRRLR:a RLR:a]` | `18` | 2 | 7 |
| $(3,1)$ | D | `D[LLLR:a RRR:x LRLR:r]; C[LRLLLR:a LRLRR:a LRRLR:a RLR:a]` | `16` | 2 | 7 |
| $(3,1)$ | E | `D[LLLR:a RRR:x LRLR:b]; C[LRLLR:a LRRLLR:a LRRRR:a RLR:a]` | `16` | 2 | 7 |
| $(3,1)$ | F | `D[LLLR:r]; C[LLLLLR:a LLLRR:a LLRLR:a LRLR:a RLR:a]` | 无 | 1 | 6 |
| $(3,1)$ | G | `D[LLLR:b RRL:x LLRR:r]; C[LLLLR:a LLRLLR:a LLRRR:a LRLR:a RLR:a]` | 无 | 3 | 8 |
| $(3,1)$ | H | `D[LLLR:b RRL:x LLRR:b]; C[LLLLR:a LLRLR:a LRLLR:a LRRR:a RLR:a]` | 无 | 3 | 8 |
| $(3,1)$ | I | `D[LLLR:a RRR:a]; C[LRLLR:a LRRLR:a RLLR:a]` | `16,14` | 0 | 5 |
| $(3,1)$ | J | `D[LLLR:b RRL:b]; C[LLLLR:a LLRLR:a LRLR:a RLLR:a RRR:a]` | 无 | 2 | 7 |

## 5. 具体证书有效性的普通证明与精确费用

**定理 5.1（两张具体证书的原合同有效性）。** 定义2.1–4.2的完整数据分别定义一条共同空历史出发的原确定策略。对每个 $h\in\mathbb N\cup\{\infty\}$、$h\ge6$，它们在相应的全部 $\mathcal T_C$ 上正确且逐源有限终止；两格的正源最坏不同地址费用分别恰为9、8。所有请求深度至多6，全来源动作数分别至多10、8。结合直接复用的固定源下界，两格原优化量为

$$
D_h(2,2;3)=9,\qquad D_h(3,1;3)=8
\qquad(h\ge6\text{，含 }h=\infty).
$$

证明。首先核对有限数据的数学来源。定义2.1的五形状、全部标签位置选择、组成反解及 $\rho$ 单射给出完整正族。定义2.2是在这些宏树的第一个宏叶后直接实例化原57.2；对定义2.3的每个有限原词，它给唯一四值。逐行应用此规则得到所列矩阵，包括常数行、重复行和缺失回复；没有用索引猜测实际源。在两格中，79个已列词正好是正源节点的并集，深度6表中余下48词均穿过每个正源的叶；高度界还给全部更深有限词共同缺失。这些事实仅描述正族，不能用于判断任意负源的同字回复。

对每个诊断节点，定义3.2、3.3的桶逐项满足

$$
S_y=\{i\in S:R_{j,i}=y\},\qquad u=u_j.
$$

故每个已列桶非空，四值桶不交且并为父集，未列桶空。全部73条边表中的集合均真包含于父集；非单元素桶恰链接到其集合对应的下一行，单元素桶只选其一个模板。两格各自根为完整索引集，其余每个节点恰有一条到达边。每个节点有正源索引，所以从根按该索引的矩阵回复可实际到达；全部行都可达。严格缩小排除循环。单元素的剩余界为0，表中每条边均满足

$$
\mathbf1_{y\ne a}+b(S_y)\le b(S).
$$

沿有限树从叶向根归纳，任一正路径的非 $\alpha$ 数不超过根界3。例如 $(2,2)$ 根的 `a,b,r` 桶孩子界均为2，逐边总量为2、3、3；$(3,1)$ 根的 `a,b,r,x` 桶孩子界为2、2、0、2，逐边总量为2、3、1、3。其余每条边的整数贡献完整列于表中。定义4.2还逐源列全每条正路径：第一格最长4个诊断请求，第二格最长3个，且没有路径重用一个原字。因此该权重恰是不同非 $\alpha$ 诊断地址数。节点表与实际路径给诊断请求最大深度5、4。这是所给有限构造的归纳，不需要关于搜索最优性的前提。

现在固定任意原源 $U\in\mathcal T_C$。每个诊断请求必须实际执行，四值回复和先后顺序全部入本次历史。若真实回复未列边就立即拒绝；否则有限缩小的节点树最终选择一个公共模板。缓存只包含这些真实请求，既不包含预报回复，也不以重复行的另一原字替代请求。后续实际补查至多6或5个地址。每个模板的宏叶深度至多3，$X_3,X_4$ 高度为2、3，故全部前沿地址深度至多6。加上诊断长度界，对全部来源动作数分别得到 $4+6=10$、$3+5=8$ 的保守上界。检查真实缓存或在失配后立即返回只会减小动作数。有限终止不假设 $U$ 有宏分解，不假设负源高度至多6。

对正源 $V_i$，从空历史逐请求归纳，它总进入包含 $i$ 的真实桶，最终选中 $[i]$。定义4.1由原矩阵列全其前沿；诊断已查的所有 `a` 地址属于这个同一 $V_i$ 的真实 $\alpha$ 前沿，其他前沿地址按字典序全部实际补查，所以最终检查通过。

对任意到达模板 $V_i$ 且最终通过的 $U$，全部 $\mathcal A(V_i)$ 的回复已真实取得并为 $\alpha$。在这里直接实例化原57.3的完整前沿刚性：$V_i$ 是三次像，因而也是二次像；其每个分支都有两色后代。全部 $\alpha$ 地址的前缀树因此包含 $V_i$ 的每个分支，缺槽恰是 $V_i$ 的 $\beta$ 单叶。匹配这些端点的完整 $U$ 必须保留此前缀树，其 $A$ 片 $\alpha$ 库存已经耗尽。每个缺槽至少放一片 $\beta$；$V_i$ 每槽一叶已经达到组成 $(A,B)$ 的总叶数 $N$，同组成的 $U$ 也只有 $N$ 叶，故每个缺槽只能一片 $\beta$，从而 $U=V_i$。这一步对 $U$ 没有高度限制。同一论证按原57.3也适用于完整 $\beta$ 前沿。故负源无论在浅字上如何兼容诊断，都不可能通过完整真实前沿检查；所有负源被正确拒绝。原57.7已经提供这一实际诊断／未列边拒绝／真实缓存补查的桥，以上是它在本两张具体表上的条件核对。

在一个固定正源的真实终端上，定义4.2补查恰是完整 $\alpha$ 前沿减去同字真实缓存；不再请求已查者。因此已付 $\alpha$ 地址最终恰有 $A$ 个，非 $\alpha$ 诊断地址与它们互不重合，且各请求一次。于是逐源有

$$
Q(T)=\mathcal A(V_i)\mathbin{\dot\cup}
\{u:(u,y)\text{ 在该源诊断段中， }y\ne\alpha\},\qquad
|Q(T)|=A+q_{\ne\alpha}(V_i).
$$

`b,r,x` 均计入第二项；`a` 也照常收费，只与最终前沿合并计数。不能把全部诊断动作数另加在 $A$ 上。50条完整时序逐项给出上述分解，最大 $q_{\ne\alpha}$ 均为3。第一格源1的实际诊断是 `LLR:b RLLR:a LRRR:x RRLR:r`，后接表列5次真实补查，费用9；第二格源6的诊断是 `LLLR:x RLLR:b RLRR:r`，后接5次真实补查，费用8。故两张具体策略的正源最坏费用恰为9、8。

最后对原优化量直接应用混色卷5.3：两格满足 $d=3k,k=1$、$a,b>0$、$n=4$、$H=d+n-1=6$。该定理对每个原合法策略给某一棵固定正源从空历史开始的完整真实终端至少 $A+3$，已覆盖所有合法有限词、全部四值、重复以及 $h=\infty$，不是只覆盖矩阵里的79词。因此两格下界分别为9、8，与本上界相等。原57.3保留的另一终端分支是完整 $\beta$，这里只需其下限 $B=10,9$，不把三单位再次加在 $B$ 上，也不删除该路线。原57.4的深度独立性同样适用；本具体上界自身已满足深度6，而下界已覆盖任意有限深词，所以结论直接对每个 $h\ge6$ 含无穷成立。□

## 6. 引用和未解数学边界

**定义 6.1（数学来源与贡献范围）。** 引文均按原对象和假设使用：

| 来源 | 本卷实际使用的数学内容 |
| --- | --- |
| [原57.1、57.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md#57-uniform-paid-acquisition-of-actual-image-certificates-at-exact-composition) | 全部同组成源、任意原端点与四值历史、费用；字面块、单射、完整正族。 |
| 原57.3、57.4、57.7（同章） | 两色完整终端及全竞争域刚性、有限深度与无穷深度关系、已有实际识别到取得桥及 $B$ 阈值。 |
| 原57.11（同章） | 已有混色四叶 $E=3$ 有限数值报告；不是一般混色公式。 |
| [混色卷4.2、4.3、5.3、7.3、8.1](FIB_ATOM_MIXED_ACTUAL_ADDRESS_PARTIAL_BOUNDS.md) | 原宏树库存及列次序、已发表固定源 $A+3$ 下界和部分上界；两格只代入现有下界。 |
| [ActualImageAddressCertificate 的来源说明](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.md) | 原证书及敏感交换的成熟背景；一般证书复杂度或决策树结果不单独给本卷具体表。 |

本卷新增证据是定义2.3的完整原矩阵、定义3.2、3.3的具体诊断及逐边整数界、定义4.1、4.2的全部前沿和真实时序，以及定理5.1对这些具体证书的普通有效性证明。原 $E=3$ 数值、一般操作桥、两色刚性、深度独立性和 $A+3$ 下界直接复用，不重新取得新增内容名义。这些是仓内普通数学证据；不据此声称全局原创、文献穷尽或内核形式化认证。

**定义 6.2（一般混色目标）。** 原目标仍为所有 $d=3k,k\ge1$、$a,b>0$、$n=a+b\ge4$、每个 $h\ge d+n-1$ 含无穷的准确 $D_h(a,b;d)$，来源、查询、回复、空历史、不同实际地址费用与全负源终止条件均如原57.1。所给证书仅处理本卷两格，不给其他参数的准确值；原57.7的 $D=A+E$ 仍受 $B$ 阈值约束。

**定义 6.3（完整 GeneralH 目标）。** 来源仍为一个固定自然数向量 $(a,b)$，包含零及混合零；正时间 $k$ 的量为

$$
y(k)=F_{k+3}a+F_{k+4}b,
$$

原查询保留完整 $\gcd(y(k),H)$ 回复，每次实际执行都收费，包括重复；从共同空历史确定适应，对每个原源有限确定全部正时间未来。$H=1$、素数2与5、指数1、未知内容、非满轨道、饱和、停滞及退出秩和 WSS 的原适用边界均保留，见[混色卷定义8.4](FIB_ATOM_MIXED_ACTUAL_ADDRESS_PARTIAL_BOUNDS.md#8-部分界的边界与未解目标)及其原目标。本卷的树不同地址费用不确定该目标的答案。

**定义 6.4（同一实际整数的严格全除数预算）。** 原目标仍要求同一个实际整数

$$
N^*=1+F_r g^*,\qquad r\ge7\text{ 为素数},\qquad
C^*+H^*<\left(\frac{\log\log(N^*)}{\log\log(A)}\right)^s.
$$

不假定 $F_r$ 为素数；原连续非空窗口、分离分母、全部实际素数幂与全部约数均保留。原 $A,C_0,N_g,s,t,Z,b_s$ 和非空 $E^*$ 条件保持其数论含义，见[混色卷定义8.5](FIB_ATOM_MIXED_ACTUAL_ADDRESS_PARTIAL_BOUNDS.md#8-部分界的边界与未解目标)及原目标；数论 $A$ 不与树组成计数混用。两格树证书没有支付这项严格预算。一般混色、GeneralH、同一整数预算及原 Robin、黎曼假设和长期 FIB-ATOM 几何代数目标均不由这两格结算。

## 6.99 追加锚（本行以下为增补区）

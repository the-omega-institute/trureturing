# 正交时间场论 OTF-006：内生计算、有效消去与证明搜索

> 理论参考输入：本稿为用户提供的研究正文，包含普通数学证明，未作本候选的 Lean/kernel 认证。原图以文内文字和公式呈现。

OTF RESEARCH SERIES / 006 / VERSION 1.0

正交时间场论

内生计算、有效消去与证明搜索

初始结构、查表记忆与量子门成本的统一计费

Endogenous Computation, Effective Cancellation\
and Proof Search

**资源核心** 初始结构可以降低在线难度；其构造、保存、访问与校验证据都须计入同一模型。 对无结构唯一目标搜索，$b$ 位目标相关经典标签与 $Q$ 次量子查询满足

$$
\boxed{\quad 2^b(Q+1)^2\ge N/9.\quad}
$$

**逻辑核心** 有限维不保证有效可判定；几何转向只有附带保真编码与推理证书， 才可能成为合法证明步骤。

$$
\text{有效构造}+\text{语义保真}+\text{全程资源界}
 \ \Longrightarrow\ \text{可验证的条件归约}.
$$

**范围** 本稿给出完整候选约束与普通数学证明。 它不以免费答案基、未计费无限表或任意实数精度替代标准复杂性问题， 也不声称解决 $P$ 与 $NP$ 或建立判定全部算术真理的算法。

2026 年 11 月 8 日 / Asia–Singapore

项目默认分支 dev，本轮不可变快照：

`5378f9df3131785fa265b07710610a77ee86c66a`

接续 OTF-005 的内部参考、方向路径与完整状态区分。

## 摘要

本文把用户提出的初始结构、查表顺序、量子门计数、无穷消去与通用证明 整理为一套资源可追溯的研究框架。首先区分标准统一计算、非一致建议、 oracle 和已含目标信息的准备，证明多项式可构造的辅助结构可以编译回基础模型， 并以指数填充说明表面加速如何来自输入尺寸改变。 随后建立未知目标搜索中初始经典信息位数与后续查询次数的联合下界， 给出量子二阶与经典一阶权衡，以及将准备阶段重新计入后的恢复定理。 在几何层，证明端点夹角不能单独确定局域门复杂性； 即使坐标一致可计算，三维向量的严格共线判定也能包含停机不可判定性。 在分析层，以单射性、任务纤维饱和、稳定逆界和有效收敛模 取代形式上的无穷约分。最后建立证书保持归约、 辅助定义的保守扩展、有界证明搜索及其资源综合定理， 并明确多项式证明长度与 $NP=\mathrm{coNP}$ 的关系。 观察者的程序、存储、精度、记录与查询全部保留在整体内； 内生性要求信息来源可计费，不使其自动免费或可计算。

**关键词：** 初始结构；非一致计算；量子查询；可逆计算； 有效消去；可计算实数；证明复杂性；内部观察者。

## 目录

- [1　研究目标与 AX-006 完整候选约束](#section-1)
- [2　初始结构究竟改变了什么？](#section-2)
- [3　查表、准备、记忆与顺序的成本](#section-3)
- [4　初始信息与后续搜索的联合资源定理](#section-4)
- [5　几何转向、门复杂性与 SAT 对齐](#section-5)
- [6　无穷的有效消去：保真性、稳定性与收敛模](#section-6)
- [7　从几何可达性到合法逻辑推理](#section-7)
- [8　通用证明：有界搜索、短证存在与不可判定性](#section-8)
- [9　有效、保真且保成本的闭合理论](#section-9)
- [10　与当前项目的衔接及本轮所得](#section-10)
- [A　来源范围、版本及验证说明](#section-A)

<a id="section-1"></a>

## 1　研究目标与 AX-006 完整候选约束

用户提出四项相连的研究方向：复杂性取决于初始结构； 无穷问题可通过已知关系消去；查表、顺序与记忆应按基本门计费； 证明过程应成为可机械检验的通用构造。 本文保留这些方向中可以形式化的部分，并检验其量词、语义与成本。 截至本轮核对，Clay 官方仍把标准 $P$ 与 $NP$ 问题列为未解决 [\[1\]](#ref-clay), [\[3\]](#ref-cook_millennium)。 下文不会把相对化模型、有限规模查表或量子加速误写为该问题的解答。

OTF-005 已区分状态方向、最短旋转元、内部相位、控制及记录。 本轮进一步区分两种关系： 物理门改变编码状态；逻辑规则保持已声明的推理语义。 它们可以在同一个内部装置中实现，但不能仅凭都称为“门”就相互替换。

#### 结构约束 1.1：D1：任务、编码及模型标签

任务由有限输入 $`x\in\{0,1\}^*`$、输出或证书 $y$、 以及已声明的判定或验证关系 $R(x,y)$ 给出。 输入规模 $n=|x|$、承诺域和错误界固定。 统一经典、统一量子、建议及 oracle 模型分别标记； 跨模型结论必须给模拟定理。

#### 结构约束 1.2：D2：初始结构的来源

每个初始表、基变换、参考、程序和辅助结构均说明依赖于 输入长度、已知输入还是未知目标。 内部可生成结构具有统一有限生成程序及准备成本； 免费建议或 oracle 则显式列为外加资源。 没有来源合同的实数振幅不能充当免费无限信息存储。

#### 结构约束 1.3：D3：固定局域门与量子接口

量子寄存器由有限个复二态接口复合，态为正归一密度矩阵； 门从固定有限、常数局域的通用门集中选取， 其矩阵元可在精度位数的多项式时间内近似； 该门集包含或可有效编译本文使用的 $X$、CNOT 与 Toffoli。 允许以记录寄存器实现的测量和经典控制。 近似目标另给精度 $\varepsilon$。 经典逻辑可用含辅助位的可逆电路实现， 辅助位的准备、占用与清理均保留。

#### 结构约束 1.4：D4：全程资源计费

分别记录程序构造时间、准备与路由门数、执行门数、 验证与清理门数、查询次数、最大存储及深度。 若统一换算为基本量子门， 经典编译和控制也须先给可逆实现并计费。 任何多步多项式结论还要求中间表示长度具有统一多项式界。

#### 结构约束 1.5：D5：语义保真的归约

每次降维、投影、约分或编码转换都附带任务语义。 若要求恢复原对象，映射须有指定域上的单射性； 若只保存某项任务，任务值须在被合并的纤维上恒定。 输出证书的恢复、类型与长度一并说明。

#### 结构约束 1.6：D6：有效的无穷与精度合同

无穷对象由有限名称、算法或公理化定义表示。 除法声明非零条件；稳定恢复声明分母或奇异值下界。 由极限输出有限精度结果时，给出可一致有效求值的截断对象， 以及有效尾界或收敛模。 收敛存在、极限有限和可有效求出分别检查。

#### 结构约束 1.7：D7：固定证明核与合法步骤

固定一个有效的形式系统与有限证明编码， 核检查器判定所给证明是否遵守其规则。 每个所谓推理门都给出可检查的前提、结论和健全性依据。 辅助定义与已证引理可以使用， 其构造或证明证书不能由几何可达性替代。

#### 结构约束 1.8：D8：内生历史与有限协议

输入、控制、建议来源、地址、记忆、钟、误差估计与验证器均属于整体历史。 固定有限协议可以嵌入包含这些寄存器的可逆演化。 离线成本可在多次任务间摊销，但须给出复用次数和数据共享范围。 选择更优顺序的搜索成本也属于算法。

这些条件是可供反向检查的模型约束。 若取消某项，后文给出能违反目标结论的具体模型； 不声称形式约束本身可以从“全部内生”这一个词无条件推出。

<a id="section-2"></a>

## 2　初始结构究竟改变了什么？

#### 定义 2.1：三个不同的多项式类

$P$ 是统一确定性经典算法在输入长度的多项式时间内判定的语言类。 $NP$ 是存在多项式长度证书、可由统一经典多项式验证器检查的语言类：

$$
x\in L\iff\exists y,\quad |y|\le p(|x|),\quad V(x,y)=1.
$$

$BQP$ 使用统一多项式规模量子计算和有界错误， 通常取每个输入的正确率至少 $2/3$。

因此 $NP$ 不是“已经证明需要指数时间”的定义； $P\subseteq NP$。某个算法的运行顺序很差，也不使本来在 $P$ 中的语言 离开 $P$，因为类的定义量化的是 *是否存在* 满足界的统一算法。 标准定义与合理模型间的多项式模拟见 Cook 的问题说明 [\[3\]](#ref-cook_millennium)。

#### 定义 2.2：三种辅助结构

- \(i\) **可构造辅助结构：** $a(x)$ 由统一算法从已知输入 $x$ 构造，成本计入。

- \(ii\) **非一致建议：** $a_n$ 只依赖长度 $n$，可免费提供； 若 $|a_n|\le\operatorname{poly}(n)$，经典在线计算给出 $P/\mathrm{poly}$ 模型。 它不要求建议可被统一有效生成。

- \(iii\) **Oracle：** 某固定集合 $O$ 的成员查询作为原语，分别得到 $P^O,NP^O$ 等类。 一次 oracle 查询的实际实现不由该计数模型供应。

依赖未知目标 $w$ 的标签 $a(w)$ 是另一种相关输入， 不等同于只依赖输入长度的建议 $a_n$。

#### 定理 2.3：多项式可构造结构的编译定理

设 $a(x)$ 可在经典时间 $p(n)$ 内构造， $|a(x)|\le p(n)$； 在线经典算法在时间 $q(n+|a(x)|)$ 内给出正确结果。 若 $p,q$ 是固定多项式，则复合算法属于 $P$。 若在线部分是统一有界错误量子算法， 辅助准备也可统一多项式实现，则复合算法属于 $BQP$。

**证明。**

先运行构造，再运行在线程序。 总成本不超过 $p(n)+q(n+p(n))$，仍是固定多项式。 量子情形串联统一的准备与执行电路； 若均为近似实现，把各自误差预算取到总界内即可。 经典构造本身可以由后文可逆模拟计入量子资源。

$\square$

#### 推论 2.4：多项式双向编码不改变多项式可解性

设 $e:X\to X'$ 是两个合法编码域之间的双射， 编码及逆解码均可多项式计算，长度互为多项式有界，且保持任务答案。 若两个合法编码域均可多项式识别，约定拒绝无效字符串， 则相应经典判定问题在两种编码下同时属于 $P$。 证书可多项式转换时，$NP$ 证书性质也相应保持。

**证明。**

在新算法前后复合编码与解码，应用定理 2.3。

$\square$

#### 例 2.5：指数填充会改变表面规模，却不证明 $P=NP$

令

$$
L_{\rm pad}
 =\{x\#1^{\,2^{|x|}}:x\in\mathrm{SAT}\}.
$$

对于总输入长度 $N$，先检查填充格式， 再枚举 $x$ 的全部赋值，可在 $N$ 的多项式时间内完成。 因此 $L_{\rm pad}\in P$。 但 $x\mapsto x\#1^{2^{|x|}}$ 仅输出长度就达指数， 不是标准多项式归约。

这使“换初始表示能够变容易”成为一个真实命题， 同时明确改变发生在何处：编码大小、提供的信息或允许操作变了。 不能把这些改变都压成球面上同一个夹角参数。

#### 命题 2.6：一个明确的相对化相等模型

取 $O$ 为 PSPACE 完全集合（例如真量词布尔公式）。 则

$$
P^O=NP^O=\mathrm{PSPACE}.
$$

**证明。**

任意 PSPACE 语言可多项式归约到 $O$， 故 $\mathrm{PSPACE}\subseteq P^O\subseteq NP^O$。 反向，确定性多项式空间机器可以深度优先枚举 非确定性多项式长度计算分支， 并用多项式空间逐次求解其多项式长度的 $O$ 查询。 空间可复用，故 $NP^O\subseteq\mathrm{PSPACE}$。

$\square$

Baker–Gill–Solovay 还构造了另一递归 oracle $B$， 使 $P^B\ne NP^B$ [\[4\]](#ref-bgs)。 这些结论说明相对化方法的边界及 oracle 资源的作用； 标准无 oracle 的 $P=NP$ 仍然是一个固定的数学命题。

<a id="section-3"></a>

## 3　查表、准备、记忆与顺序的成本

#### 定义 3.1：完整计算资源

对一次协议，使用资源向量

$$
\mathfrak R=
 (T_{\rm gen},G_{\rm prep},G_{\rm route},G_{\rm run},
 G_{\rm check},G_{\rm clean},Q,S,D,\ell).
$$

其中依次为程序生成时间、准备门数、路由门数、执行门数、 验证门数、清理门数、oracle 查询、最大工作存储、 电路深度及精度描述长度。 若所有经典部分均已编译到同一可逆门模型， 可报告其总基本门数 $G_{\rm all}$，但仍保留 $S,D,Q$。

#### 定理 3.2：经典电路的可逆实现与清理

含 $L$ 个有界扇入 Boolean 门、$r$ 位输出的电路， 可以通过 $O(L+r)$ 个固定局域可逆门、$O(L+r)$ 个附加位， 在保留输入的同时计算输出。 复制输出到新寄存器后逆序运行， 可以清空中间辅助位，总门数仍为 $O(L+r)$。

**证明。**

给每个经典门一个初始为零的目标辅助位。 对输入位 $a$ 计算 NOT 时，先对新目标施加 $X$，再以 $a$ 控制 CNOT， 便得到 $1\mathbin{\oplus}a$ 并保留原输入。 复制与 AND 则分别使用 CNOT 与 Toffoli； 其他固定有界扇入门可由常数个这样的门实现。 依拓扑顺序计算每个中间值，用 $r$ 个 CNOT 复制最终经典输出， 再逆序应用同一可逆计算，便恢复所有工作辅助位。

$\square$

这是经典逻辑的资源有界可逆模拟，相关基本构造见 Bennett [\[5\]](#ref-bennett)。它不允许复制未知量子态； 这里复制的是已声明计算基上的经典结果。 所以经典步数并非天然虚假；合理模型间需要明确的模拟成本。

#### 命题 3.3：表的存在、构造和在线访问是不同量

对长度 $n$ 的全部二进制输入，任意 Boolean 函数都可存为 $2^n$ 位真值表。只要表及随机访问被免费给定， 在线读取可以很便宜。 但存在这样一族有限表，不推出统一多项式生成或多项式存储。

**证明。**

每个长度恰为 $n$ 的输入对应一个独立表位， 所以逐项表需 $2^n$ 位。 这些表的取值共有 $2^{2^n}$ 种； 其中没有“全部由短程序统一生成”的计数结论。 更强地，连不可判定语言的每个有限长度切片都具有有限表， 所以仅有逐规模表的存在甚至不推出可判定性。

$\square$

#### 命题 3.4：离线成本的正确摊销

若固定结构准备成本为 $P(n)$， 同一结构支持 $m$ 次在线任务，每次成本至多 $Q(n)$， 则总成本至多

$$
P(n)+mQ(n),
$$

平均每次至多 $P(n)/m+Q(n)$。

**证明。**

准备只执行一次，在线阶段执行 $m$ 次，直接相加。

$\square$

指数准备可以被极多次复用摊薄， 但必须说明这些任务共享的是同一表及同一参数。 若每个新输入都需新的目标相关结构，不能把准备当成全体输入的共同常数。

#### 例 3.5：门数、深度与局部寻址不能合成一个无条件数字

对 $n$ 个互不相关的目标位各施加 $X$， 总门数为 $n$，允许并行时深度为一。 若信息只能沿最近邻链传递，距离为 $d$ 的影响至少需 $d$ 层局域传播；证明是每一层只把依赖的空间范围扩大一个相邻位置。 允许非局域随机访问则改变该约束。

顺序可以改变缓存命中、共享子计算与可并行性， 因而是算法设计的一部分。 但“存在某个好顺序”只有连同其统一寻找方法与成本， 才成为复杂性上界。单独规定最小门数是优化目标， 不是获得最优程序的算法。

<a id="section-4"></a>

## 4　初始信息与后续搜索的联合资源定理

#### 定义 4.1：带相关初始标签的唯一目标搜索

未知目标 $w\in[N]=\{1,\ldots,N\}$， 唯一依赖 $w$ 的可调用原语为位查询

$$
O_w|j,z\rangle=|j,z\oplus[j=w]\rangle.
$$

允许免费给定 $b$ 位经典标签 $a(w)\in\{0,1\}^b$； 其余初态与控制程序仅能依赖此标签及已知参数。 算法须对每个 $w$ 以至少 $2/3$ 概率输出 $w$。 $Q$ 为在线阶段的最坏情形查询上界。 标签可依赖目标，因而本节不是 $P/\mathrm{poly}$ 的长度建议定义。

#### 定理 4.2：初始经典信息与搜索次数的权衡

在上述模型中，经典随机查询和量子查询分别满足

$$
\boxed{
 2^b(Q_{\rm C}+1)\ge\frac23N,\qquad
 2^b(Q_{\rm Q}+1)^2\ge\frac19N.
 }
$$

量子不等式仅针对 $b$ 位 *经典* 标签； 不能不经证明替换为任意 $b$ 量子位的目标相关建议。

**证明。**

至多有 $2^b$ 个标签，故至少有一个纤维

$$
C_a=\{w:a(w)=a\}
$$

大小 $M\ge N/2^b$。在该纤维上，算法的初态与程序相同。

先考虑经典情形。固定全部内部随机位， 沿一个永远回答零的查询历史运行算法。 这条历史至多查询 $Q_{\rm C}$ 个候选。 未被查询的所有 $w$ 产生同一零历史， 算法最后的单一输出至多还能正确命中其中一个。 因此对 $C_a$ 的均匀目标，固定随机位时平均成功率至多 $(Q_{\rm C}+1)/M$。再对随机位平均，仍有相同上界。 逐目标成功率至少 $2/3$，所以 $Q_{\rm C}+1\ge2M/3$，得到第一式。

量子情形可把随机性、中途测量及记录纯化， 并填充为恰好 $Q=Q_{\rm Q}$ 次查询的协议。 令 $\psi_w,\psi_0$ 为目标 oracle 与全零 oracle 下的最终纯态； $\phi_t^0$ 为全零执行中第 $t$ 次查询前的态。 令 $\Pi_w$ 投影到地址为 $w$ 的子空间， $p_t(w)=\left\|\Pi_w\phi_t^0\right\|^2$。 替换查询的 hybrid 展开及酉等距性给

$$
\left\|\psi_w-\psi_0\right\|
 \le\sum_{t=1}^Q\left\|(O_w-1)\phi_t^0\right\|
 \le2\sum_{t=1}^Q\sqrt{p_t(w)}.
$$

由于 $\sum_{w\in C_a}p_t(w)\le1$，Cauchy–Schwarz 不等式给

$$
\sum_{w\in C_a}\left\|\psi_w-\psi_0\right\|\le2Q\sqrt M.
$$

设全零执行输出 $w$ 的概率为 $q_w$，则 $\sum_{w\in C_a}q_w\le1$。 两个纯态的任意事件概率差至多其迹距离， 而纯态迹距离不超过对应向量差范数：

$$
\frac12\left\||u\rangle\langle u|-|v\rangle\langle v|\right\|_1
 =\sqrt{1-|\langle u|v\rangle|^2}\le\left\|u-v\right\|.
$$

因此

$$
\frac23M-1
 \le\sum_{w\in C_a}\left\|\psi_w-\psi_0\right\|
 \le2Q\sqrt M.
$$

即 $Q\ge\sqrt M/3-1/(2\sqrt M)$。 由于 $M\ge1$，有 $Q+1\ge\sqrt M/3$， 进而 $2^b(Q+1)^2\ge N/9$。

$\square$

该证明是在 BBBV hybrid 方法上的明确条件应用 [\[7\]](#ref-bbbv)。它是无结构 oracle 查询模型的界， 没有由此证明一般 SAT 的时间下界或 $P\ne NP$。

#### 命题 4.3：前缀标签达到同阶量子权衡

若 $N=2^n$，标签给出目标的前 $b$ 位，$0\le b\le n$， 则剩余纤维大小为 $M=2^{n-b}$。 经典顺序查询用 $O(M)$ 次；量子搜索用 $O(\sqrt M)$ 次， 其中 $M=1$ 时无需查询。

**证明。**

已知前缀将候选限制到一个可直接准备的子立方体。 令

$$
|s\rangle=\frac1{\sqrt M}\sum_{j\in C_a}|j\rangle,\qquad
 \sin\theta=M^{-1/2}.
$$

位查询可通过相位回踢实现目标反射； 与 $2|s\rangle\langle s|-1$ 复合， 在目标与其余候选均匀叠加张成的平面内每轮旋转 $2\theta$。 $O(1/\theta)=O(\sqrt M)$ 轮可得到常数成功率； 对 $M\ge4$，取最接近最优角的整数轮，成功率至少 $1-1/M$。 $M=2$ 可直接一次位查询判定，$M=1$ 直接输出。 经典枚举给另一上界。

$\square$

这是 Grover 搜索的适用情形 [\[6\]](#ref-grover)。 该平面虽然只有二维，进入目标的允许反射仍有查询成本。 由 $N=2^n$ 得无标签时的量子搜索量级为 $2^{n/2}$， 它仍随地址位数指数增长。

#### 推论 4.4：将初始信息的取得放回内部

若标签本身由 $q_{\rm prep}$ 次同一 oracle 查询生成， 初始整体态原先与 $w$ 无关，在线再用 $q_{\rm run}$ 次， 则成功率至少 $2/3$ 的完整协议满足

$$
\boxed{\quad
 q_{\rm prep}+q_{\rm run}+1\ge\frac{\sqrt N}{3}.
 \quad}
$$

**证明。**

把准备及在线阶段接成一个协议， 包括准备中的测量记录与后续条件控制。 它从与目标无关的初态出发，总查询数至多两阶段之和。 应用定理 4.2 的 $b=0$ 情形。

$\square$

初始结构因而可以实质降低 *后续* 难度， 而其信息来源进入同一整体后，完整资源仍受约束。 这正是内生观察者模型应保留的成本，而不是额外添加一个场外观察者。

#### 推论 4.5：初始信息与搜索指数的线性关系

令 $N=2^n$，免费给出目标的 $b_n=\lfloor\beta n\rfloor$ 位前缀， 其中 $0\le\beta\le1$。在上述查询模型中， 令 $`Q_{\rm C}^*,Q_{\rm Q}^*`$ 分别为满足最坏输入成功率至少 $2/3$ 的最优经典、量子查询数。则

$$
\lim_{n\to\infty}\frac{\log_2(Q_{\rm C}^*+1)}n=1-\beta,\qquad
 \lim_{n\to\infty}\frac{\log_2(Q_{\rm Q}^*+1)}n=\frac{1-\beta}{2}.
$$

**证明。**

定理 4.2 给出与 $2^{n-b_n}$ 和 $2^{(n-b_n)/2}$ 成常数比例的下界； 前缀标签构造给同阶上界。 取二进制对数、除以 $n$，常数与取整误差均趋于零。 $\beta=1$ 时目标已由前缀完全给出，零次查询符合两个极限。

$\square$

**图示（文字版）。** 横轴为初始目标信息占比 $\beta=b/n$，取值从 $0$ 到 $1$；纵轴为渐近查询指数 $\eta$。经典查询直线 $\eta_{\rm C}=1-\beta$ 从 $(0,1)$ 降至 $(1,0)$；量子查询直线 $\eta_{\rm Q}=(1-\beta)/2$ 从 $(0,1/2)$ 降至 $(1,0)$。在 $\beta=1/2$ 处，两条直线的指数分别为 $1/2$ 与 $1/4$。

**图 1。** 唯一目标黑箱搜索的渐近查询指数。 纵轴 $\eta=\lim n^{-1}\log_2(Q+1)$。 图中标签是免费给定的目标前缀；其内部取得成本另由推论 4.4 约束。该图不表示一般 SAT 的时间下界。

<a id="section-5"></a>

## 5　几何转向、门复杂性与 SAT 对齐

#### 命题 5.1：端点夹角不足以决定局域门数

在 $n$ 量子位上，考虑

$$
|a\rangle=|0^n\rangle,\qquad
 |b\rangle=|10^{n-1}\rangle,\qquad
 |c\rangle=|1^n\rangle.
$$

$|a\rangle$ 到 $|b\rangle,|c\rangle$ 的 Fubini–Study 距离均为 $\pi/2$。 若每门至多作用于 $k$ 个量子位， 准备 $|c\rangle$ 至少需 $\lceil n/k\rceil$ 个门， 而准备 $|b\rangle$ 可由一个 $X$ 门完成。

**证明。**

两个目标都与初态正交，故射影距离相同。 未被任何门触及的量子位始终保持初始 $|0\rangle$。 要将所有 $n$ 位变为 $|1\rangle$，所有位置都必须被某个门触及， 故 $kG\ge n$。单个位翻转给另一上界。

$\square$

这不否认计算几何化，而是确定应使用何种几何。 局域门、控制限制与代价函数必须进入度量。 Nielsen 等人在 $SU(2^n)$ 上为多体生成元设置惩罚， 把最短控制路径与电路复杂性相连； 原文同时明确指出，确定最短测地线的初始速度一般并不容易 [\[11\]](#ref-nielsen)。这不是把所有计算压成一个普通 $S^2$ 端点夹角。

#### 注 5.2：正交外积与门不对易的区别

$a\wedge b=-b\wedge a$ 是反对称性。 门的顺序效应由实现元的乘积及交换子决定。 不同量子位上的两个 $X$ 门对易，同一生成元的不同参数指数也对易。 因而不能仅由外积反对称推出所有门都不对易， 更不能由此推出某个顺序具有多项式成本。

#### 定理 5.3：统一经典目标对齐等价于 SAT 求解

以下两项等价：

- \(i\) 存在统一经典多项式算法判定任意 SAT 实例；

- \(ii\) 存在统一经典多项式构造， 对任意公式 $F$ 输出一个候选赋值 $y$， 且当 $F$ 可满足时保证 $F(y)=1$。

因此，若所谓“初始基对齐”在上述完整成本内实现 (ii)， 便确实推出 $P=NP$；该对齐能力本身正是需要证明的实质。

**证明。**

\(ii\) 给出 (i)：构造候选后验证 $F(y)$。 不可满足公式不会通过，可满足公式按条件通过。 (i) 给出 (ii)：先判定 $F$；若可满足， 依次尝试把各变量设为零，并对剩余公式调用 SAT 判定器。 若仍可满足则保留零，否则设为一。 每一步保持可满足性，至多变量数加一次调用即输出见证。 SAT 的 NP 完全性把 (i) 与 $P=NP$ 联系起来 [\[2\]](#ref-cook71), [\[3\]](#ref-cook_millennium)。

$\square$

#### 推论 5.4：量子对齐得到的类不同

若上述构造改为统一多项式量子程序， 并在每个可满足实例上以至少 $2/3$ 概率输出满足赋值， 则结合经典验证得到 $\mathrm{SAT}\in BQP$，进而 $NP\subseteq BQP$。 这一步本身没有给出经典多项式算法。

**证明。**

每次运行后验证候选。无解实例永不误接受， 有解实例按条件以足够概率接受；再复合经典多项式归约。

$\square$

“选目标为测量基”只有在目标或该基的可执行构造已知时直接可用。 在搜索问题中，目标往往正是未知见证； 把它写进初态、门标签或测量装置，会移动信息来源， 不能替代其取得过程。

#### 定理 5.5：三维严格共线可以包含不可判定问题

存在关于程序指标 $e$ 一致可计算的单位向量 $a,b_e\in S^2$，使得

$$
a\wedge b_e=0
 \quad\Longleftrightarrow\quad
 \text{程序 }e\text{ 永不停机}.
$$

而且 $a\cdot b_e>0$，所以该障碍不依赖反向端点。 因此不存在对所有这种有限程序描述的三维方向 判定严格共线的通用算法。

**证明。**

约定停机步数 $t_e\ge1$，定义

$$
r_e=
 \begin{cases}
 2^{-t_e},&e\text{ 在第 }t_e\text{ 步停机},\\
 0,&e\text{ 永不停机}.
 \end{cases}
$$

要求绝对误差至多 $2^{-m}$ 时， 模拟程序 $m$ 步；若已停机则输出准确值， 否则输出零，之后才停机所对应的值小于 $2^{-m}$。 因此 $r_e$ 一致可计算。 令

$$
a=(1,0,0),\qquad
 b_e=\frac{(1,r_e,0)}{\sqrt{1+r_e^2}}.
$$

分母始终至少一，归一化坐标也一致可计算。 外积为零恰当 $r_e=0$， 而内积恒正。 通用共线判定将判定不停机及其补集停机，与停机不可判定性矛盾 [\[9\]](#ref-turing)。

$\square$

该反例已经把全部几何压在三维，甚至一个二维平面内。 难度仍可藏在 *严格零与任意小非零的区分* 中。

#### 推论 5.6：带已知间隙的几何判定可有效完成

若额外承诺

$$
\left\|a\wedge b\right\|=0
 \quad\text{或}\quad
 \left\|a\wedge b\right\|\ge\delta>0,
$$

其中 $\delta$ 为已知有理数， 则以误差小于 $\delta/3$ 计算该范数并以 $\delta/2$ 为阈值， 即可判定两种情况。 成本取决于达到该精度的算法。

**证明。**

零情形的近似值小于 $\delta/3$， 非零情形的近似值大于 $2\delta/3$，两者可分。

$\square$

有限维、有限程序描述、任意精度逼近、严格可判定和多项式可判定， 由此成为五个需要分别证明的性质。

<a id="section-6"></a>

## 6　无穷的有效消去：保真性、稳定性与收敛模

#### 定理 6.1：恢复型约分的准确判据

设 $E:X\to Y$。对全部 $a,b\in X$，推理

$$
E(a)=E(b)\Longrightarrow a=b
$$

成立，当且仅当 $E$ 单射。 若 $E$ 为 Hilbert 空间之间的线性算子， 存在稳定逆估计

$$
\left\|a-b\right\|\le c^{-1}\left\|E(a)-E(b)\right\|
$$

当且仅当 $\left\|Ev\right\|\ge c\left\|v\right\|$ 对全部 $v$ 成立。

**证明。**

第一项就是单射的定义。 第二项取 $v=a-b$，两种表达逐字等价。

$\square$

#### 推论 6.2：非零共同 Hilbert 张量因子可稳定消去

设 $0\ne u\in\mathcal H$，$a,b\in\mathcal K$。则

$$
\left\|u\otimes a-u\otimes b\right\|
 =\left\|u\right\|\,\left\|a-b\right\|.
$$

特别地，$u\otimes a=u\otimes b$ 当且仅当 $a=b$。

**证明。**

Hilbert 张量积的内积定义给 $\left\|u\otimes(a-b)\right\|^2=\left\|u\right\|^2\left\|a-b\right\|^2$。

$\square$

若因子为零，所有对象都被合并。 若因子的范数随截断趋零，逐截断虽可消去，逆误差常数却可能发散。 若所谓共同因子具有无穷 Hilbert 范数，它根本不属于该 Hilbert 空间； 不能直接把通常张量与归一化公式套在它上面。

#### 定理 6.3：任务型压缩允许丢信息，但须保持读出

设 $q:X\twoheadrightarrow Q$，任务 $f:X\to Z$。 存在唯一 $\bar f:Q\to Z$ 使 $f=\bar f\circ q$， 当且仅当

$$
q(x)=q(y)\Longrightarrow f(x)=f(y).
$$

若还希望保存每个后续操作 $F_\alpha$，则须另满足

$$
q(x)=q(y)\Longrightarrow
 q(F_\alpha x)=q(F_\alpha y),
$$

这时 $F_\alpha$ 可以降到 $Q$ 上。

**证明。**

若分解存在，纤维恒定性立即成立。 反之定义 $\bar f(q(x))=f(x)$，纤维条件保证良定义， 满射性保证唯一性。操作的降阶证明相同。

$\square$

#### 反例 6.4：当前读出相同，不保证将来相同

令 $X=\{0,1\}^2$，$q(x_1,x_2)=x_1$， 后续操作为交换 $F(x_1,x_2)=(x_2,x_1)$。 $(0,0)$ 与 $(0,1)$ 当前读出相同， 交换后的读出分别为零和一。 因此删除第二坐标会丢失未来任务需要的信息。

这与项目中的未来读出右同余、目标恢复判据相接 [\[16\]](#ref-repo_scripts), [\[18\]](#ref-repo_v22), [\[20\]](#ref-repo_target_recovery)。 合法约化不必对整个宇宙态单射， 但要对所宣称保留的任务和后续操作足够忠实； 定义出一个商也不自动给出其有效构造算法。

#### 定理 6.5：共同发散因子的有限截断消去与误差界

对有限截断参数 $\Lambda$，设 $h_\Lambda\ne0$，且

$$
A_\Lambda=h_\Lambda(a+r_\Lambda),\qquad
 B_\Lambda=h_\Lambda(b+s_\Lambda).
$$

已知 $|b|\ge\beta>0$、$|a|\le M$、 $|r_\Lambda|\le\epsilon_A(\Lambda)$、 $|s_\Lambda|\le\epsilon_B(\Lambda)\le\beta/2$。 则分母非零，并有

$$
\boxed{
 \left|\frac{A_\Lambda}{B_\Lambda}-\frac ab\right|
 \le
 \frac{2\epsilon_A(\Lambda)}{\beta}
 +\frac{2M\epsilon_B(\Lambda)}{\beta^2}.
 }
$$

若消去后的有限截断比值可一致有效求值， 提供算法可使用的有理数界 $\beta>0$ 与 $M\ge0$， 且两个误差界具有有效收敛模，便得到极限比值的有效精度算法。

**证明。**

先在每个有限 $\Lambda$ 上合法消去 $h_\Lambda$，得到 $(a+r_\Lambda)/(b+s_\Lambda)$。 由于 $|b+s_\Lambda|\ge\beta/2$，

$$
\frac{a+r}{b+s}-\frac ab
 =\frac{br-as}{b(b+s)}.
$$

分别估计两项即得所示界。 通过有效模选取足够大的 $\Lambda$，可把右端压到指定误差的一半， 再将该截断比值求值到另一半误差内，即得有效精度算法。

$\square$

这里没有对一个称为“无穷”的数直接约分； 共同因子在有限截断上消去，再由统一误差界控制极限。 若只知道 $A_\Lambda,B_\Lambda$ 都发散， 比例可以趋于任意常数、发散或振荡， 因此仅有两个无穷符号不能确定答案。 同理 $(\Lambda+c)-\Lambda=c$ 表明相同发散主项 并不指定有限余量；用于物理正则化时还需相应的模型与标定条件。

#### 例 6.6：一个完整的可去奇点证书

对 $x\ne0$，

$$
\frac{\sin x}{x}=\int_0^1\cos(tx)\,\mathrm dt.
$$

右端在 $x=0$ 连续延拓为一。 因 $|\cos(tx)-1|\le t^2x^2/2$，

$$
\left|\frac{\sin x}{x}-1\right|\le x^2/6.
$$

这同时给出了合法定义域、有限核和显式误差界。

#### 反例 6.7：单位归一化不保证极限单位方向存在

在 $\ell^2$ 中令

$$
v_N=\frac1{\sqrt N}\sum_{j=1}^N e_j.
$$

每个 $v_N$ 都归一化，但

$$
\left\|v_{2N}-v_N\right\|^2=2-\sqrt2>0.
$$

故该序列没有范数极限。 它弱收敛到零：对有限支撑测试向量直接成立， 再以其在 $\ell^2$ 中的稠密性及 $\left\|v_N\right\|=1$ 推广。 弱极限零也不是单位态。

#### 定理 6.8：有限极限不供应有效收敛模

存在一致可计算、递增、有界的有理数列 $q_s$， 其极限为不可计算实数。因此该列没有可计算的通用精度收敛模。

**证明。**

令 $K$ 为停机程序指标集合，定义

$$
\alpha_K=\sum_{e\in K}4^{-(e+1)},\qquad
 q_s=\sum_{\substack{e\le s\\e\text{ 在 }s\text{ 步内停机}}}
 4^{-(e+1)}.
$$

有限模拟使 $q_s$ 可计算；各项只会加入，故递增， 且 $0\le q_s\le1/3$。 每个停机指标最终被加入，故 $q_s\to\alpha_K$。

若 $\alpha_K$ 可计算，可依次恢复各个四进制位。 已知指标小于 $e$ 的停机状态后，计算

$$
R_e=4^{e+1}\left(
 \alpha_K-\sum_{\substack{j<e\\j\in K}}4^{-(j+1)}
 \right).
$$

若 $e\notin K$，则 $R_e\in[0,1/3]$； 若 $e\in K$，则 $R_e\in[1,4/3]$。 以误差小于 $1/6$ 近似并用阈值 $2/3$ 可区分， 从而判定停机集，矛盾。 若另有可计算收敛模 $\mu(m)$ 保证 $|\alpha_K-q_{\mu(m)}|\le2^{-m}$， 则它会使 $\alpha_K$ 可计算，仍矛盾。

$\square$

这是有效分析中 Specker 型现象的一个自足构造 [\[10\]](#ref-specker)。 “已经存在有限核”与“可以算出这个核”之间仍有严格差别。

#### 命题 6.9：无限断言的有限归纳证书

若已证明初始不变量 $I(s_0)$ 及保持性 $\forall s\,[I(s)\Rightarrow I(F(s))]$， 则对递推 $s_{k+1}=F(s_k)$ 有 $\forall k\in\mathbb N\,I(s_k)$。

**证明。**

对 $k$ 归纳，初始式给基例，保持性给归纳步。

$\square$

这说明无穷问题还可以通过归纳不变量、紧致性或结构定理处理， 不必都解释成相同因子的约分。 有限证书能够覆盖无限多个实例； 找到并证明保持性仍是实际的数学工作。

<a id="section-7"></a>

## 7　从几何可达性到合法逻辑推理

#### 反例 7.1：外积为零不自动证明同一，更不自动证明蕴涵

单位向量 $a,-a$ 满足 $a\wedge(-a)=0$， 但 $a\cdot(-a)=-1$。 即使追加同向条件，若没有语义保真的命题编码， 向量相同也不自动表示两个公式逻辑等价。

#### 命题 7.2：任意旋转可达不能代表逻辑蕴涵

设所有球面方向可由允许旋转彼此送达。 若把“存在允许旋转从公式编码 $a_\varphi$ 到 $a_\psi$” 直接定义为 $\varphi\models\psi$， 则该关系对所有公式对都成立，因而不健全。

**证明。**

旋转群在单位球面上传递作用。 尤其真公式的编码能被旋转到假公式编码， 但真不蕴涵假，得到反例。

$\square$

物理酉门的可逆性同样不能独自供应单向逻辑推理。 可以用可逆装置计算与检查推理证书， 同时保留输入、规则标签及历史； 证书的逻辑合法性由 D7 的核检查。

#### 定理 7.3：一个忠实但会暴露规模的几何逻辑模型

对 $m$ 个命题变元，令 $W=\{0,1\}^m$， $\mathcal H=\mathbb C^W$，基为 $\{|v\rangle:v\in W\}$。 定义

$$
P_\varphi=\sum_{v\models\varphi}|v\rangle\langle v|.
$$

令 $P_\Gamma$ 对应同时满足全部前提的赋值。 则

$$
\boxed{
 \Gamma\models\varphi
 \iff P_\Gamma P_\varphi=P_\Gamma
 \iff\operatorname{ran}P_\Gamma\subseteq\operatorname{ran}P_\varphi.
 }
$$

**证明。**

所有投影在赋值基中对角。 逐个基向量比较，乘积等式恰要求 每个满足 $\Gamma$ 的赋值也满足 $\varphi$。 对角投影的支撑包含等价于像空间包含。

$\square$

这是一个真正保存逻辑语义的几何表示。 显式列出全部对角元需要 $2^m$ 个位置。 公式可以隐式压缩这些数据， 但这时构造或判定投影包含的困难仍保留在该隐式表示中。

#### 命题 7.4：忠实 Boolean 正交表示的维数下界

若一个投影表示保留上述 Boolean 代数的零、一及所有非零原子， 并对互不相交集合满足正交可加性 $P(A\sqcup B)=P(A)+P(B)$， 则其 Hilbert 空间维数至少为 $2^m$。

**证明。**

每个赋值对应一个非零 Boolean 原子， 共有 $2^m$ 个，且两两不交。 保真的投影像因而是 $2^m$ 个非零两两正交子空间； 每个至少一维，故总维数至少 $2^m$。

$\square$

这个结论针对共同正交、可加的忠实表示。 它不声称 $m$ 个量子位需要 $2^m$ 个物理量子位； 其 Hilbert 空间本来就有 $2^m$ 维。 它说明不能同时保留全部这些逻辑关系， 又把全部对象无损压成同一个普通三维线–面模型。

#### 定义 7.5：证书保持归约

对实例 $x$，归约器输出新实例 $x'$、恢复器 $D$ 以及核可检查的正确性证书 $\pi$。 证书保证：若 $y'$ 是 $x'$ 的有效答案证书， 则 $D(y')$ 是 $x$ 的有效答案证书。 若还声称判定等价，另证明反方向或满足性等价。 构造器、恢复器及其最大表示长度都计入成本。

#### 定理 7.6：合法归约链的健全复合

若每一步归约都具有上述核可检查的正确性证书， 则终点有效证书经恢复器逆序复合得到起点有效证书。

**证明。**

从最后一项有效证书开始， 逐步应用相应的恢复正确性蕴涵，有限归纳得到起点结论。

$\square$

这给“证明门序列”一个可用定义： 每一门都保留类型、前提、结论及合法性证据。 仅有一个总转向面积，尚未指定这些内容。

#### 定理 7.7：辅助定义是保守扩展

设 $\Gamma,\varphi,B$ 不含新变量 $z$， 则

$$
\Gamma\models\varphi
 \iff
 \Gamma\cup\{z\leftrightarrow B\}\models\varphi.
$$

有限个按无环顺序引入的鲜变量定义也满足同样性质。

**证明。**

每个旧变量赋值唯一延拓到 $z=B$ 的真假值，旧语言公式的真假不变。 因此前提反例可以逐一延拓或限制，两个蕴涵等价。 多个定义按无环顺序重复此过程。

$\square$

所以辅助线、代换和引理并非一律非法的外部信息。 由已有对象构造并有证书保证的辅助量，可以缩短表达与证明； 真正需要排除的是未经证明便免费加入答案或额外假设。

#### 例 7.8：共享 DAG 与展开树的差别

在含自由二元函数符号 $f$ 的项语言中，定义 $t_0=x$、$t_{k+1}=f(t_k,t_k)$。 共享 DAG 只有 $k+1$ 个节点； 朴素树展开的节点数满足 $N_{k+1}=1+2N_k$， 故 $N_k=2^{k+1}-1$。 这说明消去所有中间名称可能造成指数展开， 不证明所有等价表达或所有证明都必须指数长。

#### 命题 7.9：已给定可计算依赖 DAG 的动态规划

若一个任务的依赖 DAG、初始叶值及每个节点的确定性计算程序 都可从输入统一多项式构造， 节点数、边数、所有中间值长度和每节点计算时间均为输入长度的多项式， 则按拓扑序缓存节点结果得到统一多项式算法。

**证明。**

拓扑排序和依赖访问可在图的编码长度的多项式时间内完成。 每个节点只计算一次；多项式项数乘以统一多项式单项成本仍为多项式。 所有保存结果长度的总和也有多项式界。

$\square$

这里初始结构确实带来了算法。 其适用条件已经包含图的取得、叶值来源、 局部计算及中间长度；图上一个标记为“求解 SAT”的节点 不能在没有实现时被当作单位成本。

<a id="section-8"></a>

## 8　通用证明：有界搜索、短证存在与不可判定性

#### 定义 8.1：有限证明核

固定多项式时间关系 $K(\varphi,\pi)\in\{0,1\}$， 表示字符串 $\pi$ 是公式 $\varphi$ 的合法证明。 健全性相对于所声明形式系统或语义解释； 完整性是另外的条件。 检查运行时间以 $|\varphi|+|\pi|$ 计。

#### 定理 8.2：有界证明搜索的复杂性

定义

$$
\mathrm{BProof}_K =
 \{(\varphi,1^b):\exists\pi,\ |\pi|\le b,\ K(\varphi,\pi)=1\}.
$$

则 $\mathrm{BProof}_K\in NP$。 若 $P=NP$，存在时间 $\operatorname{poly}(|\varphi|+b)$ 的算法决定该问题， 并在存在时构造相应证明。

**证明。**

证书为 $\pi$，其长度不超过输入中一元编码的 $b$， 检查 $K$ 为多项式，所以在 $NP$。 若 $P=NP$，存在多项式判定器。 为恢复证明，可先找一个可行的准确长度 $\ell\le b$， 再逐位询问“是否存在长度 $\ell$、以前缀 $p0$ 开头的合法证明”。 这些仍是 $NP$ 问题，故在该假设下可多项式判定。 若有则取零，否则取一；至多 $O(b)$ 次查询。

$\square$

长度界必须纳入输入规模。 若 $b$ 用二进制编码，其数值可相对编码长度指数增长， 上述证书长度不再自动受输入长度的多项式控制。 在没有 $P=NP$ 假设时，枚举所有 $|\pi|\le b$ 的字符串 总能有限完成，代价至多 $O(2^b\,\operatorname{poly}(|\varphi|+b))$。

#### 定义 8.3：多项式有界的命题证明系统

证明系统对命题重言式健全且完整：

$$
\varphi\in\mathrm{TAUT}
 \iff
 \exists\pi\ K(\varphi,\pi)=1.
$$

若另有固定多项式 $p$，使每个重言式 都有 $|\pi|\le p(|\varphi|)$ 的证明， 称该系统多项式有界。 这里仅约束短证明存在，不附带寻找算法。

#### 定理 8.4：Cook–Reckhow 刻画

$$
\boxed{
 \text{存在多项式有界的命题证明系统}
 \iff NP=\mathrm{coNP}.
 }
$$

**证明。**

若存在该系统，短证明就是 $\mathrm{TAUT}$ 的 $NP$ 证书， 所以 $\mathrm{TAUT}\in NP$。 由于 $\mathrm{TAUT}$ 为 $\mathrm{coNP}$ 完全， 有 $\mathrm{coNP}\subseteq NP$； 对语言取补又得反向包含，故相等。 反之，若 $NP=\mathrm{coNP}$， 则 $\mathrm{TAUT}\in NP$，其多项式见证验证器本身 就是所需健全、完整且多项式有界的证明系统。

$\square$

这是 Cook–Reckhow 的标准结论 [\[8\]](#ref-cook_reckhow)。 若把关系形式改成从证明串到重言式的总函数形式， 可令无效证书输出一个固定重言式，得到等价描述。

#### 推论 8.5：统一快速找证比短证存在更强

若某统一经典算法对每个重言式 $\varphi$ 在已知多项式时间内输出可通过健全检查器的证明， 则 $\mathrm{TAUT}\in P$，因而 $P=NP$。 算法在非重言式上可以失败或超时。

**证明。**

对任意公式，运行算法到所给时间界， 并验证输出；重言式必接受，其他公式因健全性不接受。 $\mathrm{TAUT}$ 的补语言与 SAT 可通过否定公式多项式互换， 所以 SAT 也在 $P$。

$\square$

#### 定理 8.6：无界证明枚举只给半判定

对任何具有有效有限证明检查的理论 $T$， 可证集合 $\operatorname{Thm}(T)$ 可枚举。 若 $T$ 能证明每个真实有限停机历史， 并且对形如“存在一个停机历史”的算术句健全， 则 $\operatorname{Thm}(T)$ 不可判定。

**证明。**

按长度枚举证明字符串并检查，可逐步输出全部定理； 某个公式可证时终将找到证明，不可证时可能一直搜索。

给程序 $e$ 有效构造算术句 $H_e$， 其含义为“$e$ 存在有限停机历史”。 有限历史可验证性和所列健全性给

$$
e\text{ 停机}\iff T\vdash H_e.
$$

若可判定 $\operatorname{Thm}(T)$，就可判定停机。 停机判定本身不可能：假设 $D(e,x)$ 判定程序 $e$ 在输入 $x$ 是否停机， 构造程序 $M(e)$，当 $D(e,e)$ 说会停机时无限循环， 否则立即停机。将 $M$ 的代码输入自身，两种回答均矛盾 [\[9\]](#ref-turing)。

$\square$

#### 推论 8.7：没有覆盖所有可证句子的可计算长度上界

在上一理论假设下，不存在全可计算函数 $B(n)$， 使每个长度至多 $n$ 的可证公式都有长度至多 $B(n)$ 的证明。

**证明。**

若有，给定公式 $\varphi$ 后枚举所有长度至多 $B(|\varphi|)$ 的候选并检查，即得到全输入终止的可证性判定， 与上一结果矛盾。

$\square$

#### 命题 8.8：长度上界与可证性判定的准确等价

对固定有效证明系统， 存在上述全可计算证明长度上界，当且仅当其可证性可判定。

**证明。**

一个方向已证。 反向，若可证性可判定， 对每个 $n$ 列出长度至多 $n$ 的有限个公式， 判定哪些可证；对可证者逐一搜索最短证明。 有限次搜索全部终止，取所得长度最大值即给可计算 $B(n)$； 没有可证公式时取零。

$\square$

这准确定位了“通用证明机器”能够完成的任务： 统一检查器与有界搜索可以存在， 对可证句子的无界枚举也可以存在； 对全部算术真假的统一终止判定则受到不同层次的限制。 即使假设 $P=NP$，它也只加速已给长度界内的搜索， 不会供应上述不存在的全可计算长度界。

#### 命题 8.9：固定可计算量子门不改变此可判定性边界

一个由统一程序生成、正确率间隙具有已知可计算正下界的有限量子电路判定族， 可以被经典算法在有限时间模拟。 因此它不能判定上述停机集合。

**证明。**

对每个输入先生成有限电路， 用有限维状态向量或密度矩阵逐门模拟。 门矩阵可计算，且电路有限， 所以可把累积数值误差控制到正确率间隙以下。 最终按中间阈值比较接受概率即得相同判定。 该模拟可以非常慢，但仍为终止的有效程序。

$\square$

<a id="section-9"></a>

## 9　有效、保真且保成本的闭合理论

#### 定义 9.1：有效闭合协议

一个协议从有限输入出发，允许： 经过证明的编码与辅助定义， 满足 D5–D6 的消去与极限控制， 以及带证书恢复器的归约。 终点进入一个已声明的可判定核心， 然后恢复原任务答案并由固定核检查。 “闭合”意味着所有依赖都有来源、所有步骤有语义依据、 所有输出有核可读证书；它不保证每个目标都能被该协议闭合。

#### 定理 9.2：资源可追溯的归约综合定理

设输入长度为 $n$ 的任务具有至多 $k(n)$ 步的统一证书保持归约。 假设：

- \(i\) 初始结构及整个归约计划可在 $P(n)$ 时间内构造；

- \(ii\) $S(n)\ge n$，所有中间实例、辅助定义、侧条件、恢复器及输出证书长度至多 $S(n)$；

- \(iii\) 每步构造、检查与恢复，以及最终完整核检查的时间均至多 $t(S(n))$；

- \(iv\) 终点核心可在 $q(S(n))$ 时间内求解，并输出适用的有效证书。

则原任务有健全求解协议，总时间可取

$$
\boxed{
 P(n)+O\!\bigl((k(n)+1)t(S(n))\bigr)+q(S(n)).
 }
$$

若 $P,k,S,t,q$ 均为固定多项式，则整个经典协议为多项式。 若核心为有界错误统一量子算法， 其余步骤可相应编译且总错误预算受控， 则得到相应统一量子上界。

**证明。**

先构造准备与计划，再顺序生成和检查各步证书， 求解核心并逆序应用恢复器。 定理 7.6 给语义健全性。 构造、检查与恢复，再加最终核检查，合计至多常数倍 $k(n)+1$ 次， 每次成本由统一中间长度 $S(n)$ 控制，故得到总界。 量子情形组合统一电路，并把每个近似步骤的误差 分配到总预算内；经典部分用定理 3.2 编译。

$\square$

#### 反例 9.3：多项式步数与局部多项式不足

若第 $j$ 步把当前表示完整平方展开， 长度满足 $s_{j+1}=s_j^2$，则 $s_k=n^{2^k}$。 每一步相对自己的输入长度是多项式， 但随 $k$ 增长的整体输出不再具有 $n$ 的固定多项式界。 所以定理中的统一中间长度条件不可删去。

### 9.1　将原四步提案改为可验证算法

1.  **固定任务与资源。** 给出逻辑理论、输入编码、允许门、初始结构来源及希望输出的证书。 选择前提作参考可以简化坐标； 任何目标相关基变换仍须给出准备程序。

2.  **提交可检查的降维或消去证书。** 对每个拟消去的因子，说明是对象恢复还是任务商； 对极限给有效余项，对除法给非零及稳定性条件。 无界量词可以通过归纳不变量处理， 不能在没有证明时直接当作共同标量因子。

3.  **在合法规则空间中搜索。** 几何距离可以作为启发式、控制目标或已证明的下界； 合法边由推理核和实际门库决定。 每次扩展保留证书与中间表示长度。 没有找到满足条件的归约时，返回未完成或在明确预算内继续搜索。

4.  **恢复并核验。** 将核心解经恢复器返回原命题， 检查完整证明 DAG、侧条件与资源账本。 只对通过固定核的产物报告证明完成。

这是一种可以机械实现的研究工作流： 它支持缓存、引理库、规划与量子子程序， 也允许启发式选择顺序； 它的通用性体现为统一接口和检查方式， 不等价于保证解决全部命题。

### 9.2　逐项反向检验候选约束

| 被省略的条件 | 省略后的模型 | 被破坏的结论 |
|:---|:---|:---|
| 统一初始构造 | 每实例免费给一个正确答案位 | 任何语言都在线常数步，包含不可判定语言 |
| 长度与存储计费 | 给每个 $n$ 免费存 $2^n$ 位表 | 有限表存在被误读为统一多项式算法 |
| 固定局域门库 | 把未知目标的完整解码器算作一门 | 门数不再衡量实现困难 |
| 中间长度界 | 长度逐步平方展开 | 局部多项式不再推出整体多项式 |
| 任务纤维保真 | 删除当前未读但下一步会读的坐标 | 原任务答案无法从压缩态恢复 |
| 精度与间隙 | 三维可计算实数中的严格零测试 | 有限维并不保证可判定 |
| 核的推理语义 | 任意旋转都被认可为蕴涵 | 真公式可以“旋转证明”假公式 |
| 记录与准备成本 | 内生构造的目标标签被当成免费先验 | 完整查询下界被错误绕过 |

<a id="section-10"></a>

## 10　与当前项目的衔接及本轮所得

本轮固定版本为 `5378f9df3131785fa265b07710610a77ee86c66a`。 指定理论目录的名称索引完整返回 1336 项、未截断； 正文只核对与任务相关的选定段落。 以下是 *项目当前文稿已有的结论及其作用* ， 不把有限核读称为对全部证明依赖的重新认证。

| 已有文稿 | 本轮接续的明确内容 |
|:---|:---|
| 有限表复杂性分类 | 区分不同输入角色下的 $P$、$NP$ 完全、$\mathrm{coNP}$ 完全、 $DP$ 完全问题；字面固定表、入口且仅预算变化时属于 $P$， 原文明确不给统一多项式预处理 [\[13\]](#ref-repo_finite_tables) |
| AURIC $\Omega$ | 已有有效有界综合合同；每实例存在有限菜单不推出统一可生成， 有限 Hilbert 维数也不自动给出可用有限门菜单 [\[15\]](#ref-repo_omega) |
| 存在量词与记录 V14 | $\#\mathrm{SAT}/2^m>0$ 可表达存在性， 但指数小概率差仍要求相应精度和抽样或放大资源 [\[14\]](#ref-repo_v14) |
| 历史脚本 V67 与观察商 V22 | 精确内容地址、共享 DAG、未来读出右同余及 共同等距消去与条件滤波的区别 [\[16\]](#ref-repo_scripts), [\[18\]](#ref-repo_v22) |
| 静态历史 V21 与 OTF-005 | 门顺序取决于操作对易性；数据态返回不删除记录事件； 路径几何不独自固定时间与控制成本 [\[17\]](#ref-repo_v21), [\[12\]](#ref-repo_otf5) |
| 证明拓扑与恢复模块 | 路径、可达偏序、拓扑和证明核不同； 目标纤维常值给存在性恢复条件，未自动给有效解码器 [\[19\]](#ref-repo_proof_topology), [\[20\]](#ref-repo_target_recovery), [\[21\]](#ref-repo_dependency_topology) |
| 自主预测记忆 | 有限描述不自动提供无界工作存储； 有界完整配置和重复相同请求具有最终周期约束 [\[22\]](#ref-repo_autonomous) |

本轮主要增加的是把这些接口统一接到三项可检验结论： 初始经典信息与量子查询的联合不等式； 三维可计算坐标中的精确零不可判定见证； 以及明确保留构造、中间长度、精度和证书恢复的归约成本定理。 这些命题在正文给出完整证明； 未作全球新颖性判断，也未把标准结果改名为本项目首创。

### 10.1　四句话的正式版本

1.  **初始结构影响复杂性。** 对的对象是“任务加初始资源加允许操作”的组合。 内部可多项式取得的结构可以带来真实算法； 免费 oracle、建议、目标标签或指数填充改变的是所声明模型。 只有在标准统一经典成本内解决全部 SAT，才得到 $P=NP$。

2.  **无穷可以借已知关系闭合。** 闭合需要可验证的消去、误差、归纳或其他结构证书。 公共发散因子可以在有限截断中消去， 但无穷范数、没有有效模的极限及精确零判断 不能靠形式约分消失。

3.  **顺序、记忆和门数应共同计费。** 已知依赖图上的共享可以避免重复计算； 准备图、取得地址、编译门、选择顺序、 访问存储与保留记录同属完整过程。 量子门数可以作为明确模型下的统一指标， 仍须同时说明宽度、深度、精度与 oracle 资源。

4.  **通用证明方法可以是统一证书协议。** 检查、归约、恢复和有界搜索可以机械化。 短证存在、快速找证、有限维几何可达和算术真理判定， 分别属于不同命题；每一个跨越都需要独立定理。

### 10.2　自指闭环何时具有算法意义

前轮的线、面与内生注意力可以分别作为记录、控制变换与程序选择的解释。 本轮要求把这些解释落实到有限寄存器及可执行操作。 同一个末态可以来自不同长度的门历史； 同一个状态夹角也可以对应不同局域门成本。 因此不能把几何面积、门数与时钟秒数无条件视为同一量。

#### 命题 10.1：余弦反馈的有效收敛与任务边界

设 $F_\sigma(x)=\sigma\cos x$，其中 $\sigma\in\{+1,-1\}$， $x\in[-1,1]$。该映射具有唯一不动点 $x_\sigma=\sigma d$， 其中 $d=\cos d\in(0,1)$。 令 $q=\sin1<1$，则精确迭代满足

$$
|x_k-x_\sigma|\le q^k|x_0-x_\sigma|.
$$

若每次近似求值误差至多 $\eta$，并将结果投影回 $[-1,1]$， 则

$$
|\widetilde x_k-x_\sigma|
 \le q^k|\widetilde x_0-x_\sigma|+\frac{\eta}{1-q}.
$$

**证明。**

$F_\sigma$ 把闭区间映入自身， 且导数绝对值至多 $\sin1=q<1$，故为压缩映射。 不动点存在唯一，偶性给出正负对称。 逐步使用 Lipschitz 界得精确误差式。 带误差时递推 $e_{k+1}\le qe_k+\eta$； 投影到含有不动点的闭区间不增大距离。 求几何级数即得第二式。

$\square$

这给出了一个真正可用的反馈模块：迭代次数与数值精度有明确合同。 但它解决的是该固定不动点问题。 若要用同一模块解决任意输入命题， 还须给出从命题到反馈参数的有效保真编码、 答案读出间隙和完整成本界。 一个收敛方程本身不供应这些接口， 也不使不动点数值成为 $P=NP$ 或通用可证性判定的证书。

### 10.3　白话整体图景

把整个系统看成一个保存结构、寻找路径并核验结果的内部观察者。 它手里的地图越完整，后续寻址越省事； 但绘制地图、记住地图和读取地图都属于它已经做过或仍需做的工作。 若地图把答案提前标出，查询会变快， 这说明先验信息有效，不说明标出答案无需计算。

处理无穷时，观察者可以找到一个共同结构， 把不影响当前任务的部分压缩掉。 它必须同时证明：压缩没有删掉将来需要的区别， 误差不会失控，所需精度能够实际达到。 把无限对象画进一个小球，并不会自动完成这些证明。

数学证明则把寻找与核验明确接在一起： 可以大胆猜测路径、引入辅助对象、复用引理或调用量子子程序， 最终留下的每一步都须被固定规则检查。 本轮得到的统一原则是： *关系可以改变表示，但其取得成本、保真的理由与可恢复的证书， 都必须随着表示一起进入整体。*

<a id="section-A"></a>

## A　来源范围、版本及验证说明

### A.1　不可变项目来源

本稿接续 [trureturing](https://github.com/the-omega-institute/trureturing) 在本轮读取时的默认分支 dev，并固定到提交

$$
\texttt{5378f9df3131785fa265b07710610a77ee86c66a}.
$$

该提交的记录时间为 2026 年 11 月 8 日 17:01:47（Asia/Singapore），本轮元数据获取时间为 17:05:17。 之后的项目正文引用均指向该不可变提交，不依赖分支随后移动。

本轮用 Git Trees 分层读取根目录、docs、develop 与 theory： 返回项数分别为 30、6、3、1336，均报告未截断。 这证明的是指定 theory 目录 *名称索引* 的覆盖范围， 不是对全部 1336 篇文稿的逐篇阅读或认证。 共取得 13 个项目文件，正文论证使用参考文献中列出的相关章节； 下载行为与实际阅读范围分别记录。 OTF-004 与 README 等只作导航的文件，不被计为本轮新增定理依据。

两个 Lean 文件的源码已读取： TargetRecoveryCriterion 与 AlexandrovDependencyTopology [\[20\]](#ref-repo_target_recovery), [\[21\]](#ref-repo_dependency_topology)。 本轮没有运行 Lean 构建或依赖公理审计， 因此这里只报告源码中的命题和用途， 不把源文件存在写成整套新理论已由机器验证。 特别是使用选择原理得到的恢复函数存在性， 不自动给出可计算或多项式时间恢复程序。

### A.2　标准结果与本文证明的关系

复杂性类定义、Cook 的完备性结果、相对化、 Grover 搜索、BBBV hybrid 方法、可逆计算、 Cook–Reckhow 刻画、不可判定性与有效收敛边界， 均有明确一手文献来源。 本文把其中适用的定义与论证接到内部准备、记忆、精度和证书的统一合同上。

联合资源定理在正文给出最大标签纤维与 hybrid 的完整推导， 常数不等式不依赖读者重建外部证明。 三维零判定和单调有界非有效极限也给出显式程序构造。 归约综合定理只在列出的语义、统一性与长度条件下成立。 这些属于本轮可独立检查的普通数学证明， 不构成对历史优先权的声明， 也不以有限范围检索宣称全球新颖性。

对原始文献的阅读以本文使用的定义、定理及证明段落为限。 Cook 1971 作者扫描已获取； 其定理构造另与明确署名的转录版本对照。 Cook–Reckhow 作者勘误指出原文推论 4.7 的假设应写 $\mathrm{coNP}\ne NP$； 本文只使用第 1 节的多项式有界证明系统刻画。

### A.3　复现与可检验范围

本 TeX 文件包含正文、图形与参考文献， 使用 XeLaTeX 和所列开源字体即可排版， 不依赖外部图片。 图 1 直接绘制已证明的两条渐近直线， 没有模拟数据或经验拟合。 版面编译、交叉引用及公式显示检查属于出版质量核验， 不能替代形式系统内的机器证明。

## 参考来源

<a id="ref-clay"></a>

\[1\] Clay Mathematics Institute.  *P vs NP* . Official Millennium Problem status page; checked 8 November 2026, marked “Unsolved”. <https://www.claymath.org/millennium/p-vs-np/>.

<a id="ref-cook71"></a>

\[2\] Stephen A. Cook. The complexity of theorem-proving procedures.  *Proceedings of the Third Annual ACM Symposium on Theory of Computing* , 151–158, 1971. DOI: [10.1145/800157.805047](https://doi.org/10.1145/800157.805047). Author-hosted original scan: <https://www.cs.toronto.edu/~sacook/homepage/1971.pdf>. Theorem 1 and its construction were also checked in the explicitly identified Tim Rohlfs revision-3 transcription: <https://www.cs.cmu.edu/~15455/resources/Cook1971-complx-thm-proof.pdf>.

<a id="ref-cook_millennium"></a>

\[3\] Stephen Cook.  *The P Versus NP Problem* . Official Clay Mathematics Institute problem description, especially §1 (machine models, input-length complexity, checking relations). <https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf>.

<a id="ref-bgs"></a>

\[4\] Theodore Baker, John Gill, and Robert Solovay. Relativizations of the $\mathcal P=?\mathcal{NP}$ question.   *SIAM Journal on Computing*   4(4), 431–442, 1975. DOI: [10.1137/0204037](https://doi.org/10.1137/0204037). Original-paper copy, §§1–3, Theorems 1–3: <https://cse.ucdenver.edu/~cscialtman/complexity/Relativizations%20of%20the%20P%3DNP%20Question%20%28Original%29.pdf>.

<a id="ref-bennett"></a>

\[5\] Charles H. Bennett. Logical reversibility of computation.  *IBM Journal of Research and Development*  17(6), 525–532, 1973. DOI: [10.1147/rd.176.0525](https://doi.org/10.1147/rd.176.0525). Original-paper scan, pp. 525–529, especially the three-tape simulation theorem: <https://worrydream.com/refs/Bennett_1973_-_Logical_Reversibility_of_Computation.pdf>.

<a id="ref-grover"></a>

\[6\] Lov K. Grover. A fast quantum mechanical algorithm for database search.  *Proceedings of the Twenty-Eighth Annual ACM Symposium on Theory of Computing* , 212–219, 1996. DOI: [10.1145/237814.237866](https://doi.org/10.1145/237814.237866). Author preprint, §§1–4: <https://arxiv.org/pdf/quant-ph/9605043>.

<a id="ref-bbbv"></a>

\[7\] Charles H. Bennett, Ethan Bernstein, Gilles Brassard, and Umesh Vazirani. Strengths and weaknesses of quantum computing.   *SIAM Journal on Computing*   26(5), 1510–1523, 1997. DOI: [10.1137/S0097539796300933](https://doi.org/10.1137/S0097539796300933). Author preprint, §3.1, Theorem 3.3 and Corollary 3.4: <https://arxiv.org/pdf/quant-ph/9701001>.

<a id="ref-cook_reckhow"></a>

\[8\] Stephen A. Cook and Robert A. Reckhow. The relative efficiency of propositional proof systems.   *The Journal of Symbolic Logic*   44(1), 36–50, 1979. DOI: [10.2307/2273702](https://doi.org/10.2307/2273702). Author-hosted original, §1, Propositions 1.1 and 1.4 and Definition 1.3: <https://www.cs.toronto.edu/~sacook/homepage/cook_reckhow.pdf>. Cook’s author page corrects the hypothesis in Corollary 4.7 from $\mathsf P\ne\mathsf{NP}$ to $\mathsf{coNP}\ne\mathsf{NP}$; the present use relies on §1 rather than that corollary. <https://www.cs.toronto.edu/~sacook/>.

<a id="ref-turing"></a>

\[9\] Alan M. Turing. On computable numbers, with an application to the Entscheidungsproblem.  *Proceedings of the London Mathematical Society* , second series, 42(1), 230–265, 1936–1937. DOI: [10.1112/plms/s2-42.1.230](https://doi.org/10.1112/plms/s2-42.1.230). Original paper, selected passages in §8 (pp. 246–247), §10 (pp. 255–256), and §11 (pp. 259–260): <https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf>.

<a id="ref-specker"></a>

\[10\] Ernst Specker. Nicht konstruktiv beweisbare Sätze der Analysis.   *The Journal of Symbolic Logic*   14(3), 145–158, 1949. DOI: [10.2307/2267043](https://doi.org/10.2307/2267043). Original paper, pp. 145–148, definitions I–VIII and the statements of Sätze I and IV: <https://doc.rero.ch/record/304204/files/S0022481200105663.pdf>.

<a id="ref-nielsen"></a>

\[11\] Michael A. Nielsen, Mark R. Dowling, Mile Gu, and Andrew C. Doherty. Quantum computation as geometry.  *Science*  311(5764), 1133–1135, 2006. DOI: [10.1126/science.1121541](https://doi.org/10.1126/science.1121541). Author version with proofs, equations (1)–(13) and the synthesis theorem: <https://arxiv.org/pdf/quant-ph/0603161>.

<a id="ref-repo_otf5"></a>

\[12\]  *正交时间场论 OTF-005：轴面几何、相位纤维与内生闭合* . trureturing 项目文稿，§§1,6,9；固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/docs/develop/theory/OTF_005_AXIS_PLANE_GEOMETRY_PHASE_FIBRES_AND_ENDOGENOUS_CLOSURE.md).

<a id="ref-repo_finite_tables"></a>

\[13\]  *Native finite-table complexity classification* . trureturing 项目文稿，Theorems 4.5, 7.3, 8.3, 10.1, 11.1 及 §12； 固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/docs/develop/theory/FIB_NATIVE_FINITE_TABLE_COMPLEXITY_CLASSIFICATION.md).

<a id="ref-repo_v14"></a>

\[14\]  *AURIC 存在量词、电路半环与量子记录，V14* . trureturing 项目文稿，§12，命题12.1；固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14.md).

<a id="ref-repo_omega"></a>

\[15\]  *AURIC $\Omega$ 静态相融纤维理论* . trureturing 项目文稿，§§17,22,28–29；固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md).

<a id="ref-repo_scripts"></a>

\[16\]  *同一本体中的历史脚本、内容寻址与量子纠缠，V67* . trureturing 项目文稿，§2，定理2.3–2.4；固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/docs/develop/theory/AURIC_HISTORY_SCRIPTS_CONTENT_ADDRESSING_AND_QUANTUM_ENTANGLEMENT_IN_ONE_ONTIC_STATE_V67.md).

<a id="ref-repo_v21"></a>

\[17\]  *静态量子历史与内生观察者，V21* . trureturing 项目文稿，§3 定理3.2、§7 命题7.3–7.4；固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/docs/develop/theory/AURIC_STATIC_QUANTUM_HISTORIES_ENDOGENOUS_OBSERVERS_AND_RELATIONAL_CLOCKS_V21.md).

<a id="ref-repo_v22"></a>

\[18\]  *相对门历史与观察商，V22* . trureturing 项目文稿，§4 定理4.1–4.2、§8 定理8.2–8.4；固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md).

<a id="ref-repo_proof_topology"></a>

\[19\]  *证明拓扑、对合逻辑与观察逃逸统一理论* . trureturing 项目文稿，第一、三、十六、十七、十九、二十部；固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/docs/develop/theory/PROOF_TOPOLOGY_DIAGONAL_ESCAPE_THEORY.md).

<a id="ref-repo_target_recovery"></a>

\[20\]  *TargetRecoveryCriterion.lean* , `D5/S3/ConceptDynamics/Restoration`. trureturing 源码，`target_recovery_criterion`；固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. 本轮读取源码，未运行 Lean 构建或公理检查。 [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean).

<a id="ref-repo_dependency_topology"></a>

\[21\]  *AlexandrovDependencyTopology.lean* , `D5/S3/ConceptDynamics/DependencyTopology`. trureturing 源码，主开集、单点闭包及其单调性定理；固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. 本轮读取源码，未运行 Lean 构建或公理检查。 [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology.lean).

<a id="ref-repo_autonomous"></a>

\[22\]  *Recursive relational observation: autonomous predictive memory* . trureturing 项目文稿，§11–12，定理11.1及命题11.2–11.3；固定提交 `5378f9df3131785fa265b07710610a77ee86c66a`. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/5378f9df3131785fa265b07710610a77ee86c66a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_AUTONOMOUS_PREDICTIVE_MEMORY.md).

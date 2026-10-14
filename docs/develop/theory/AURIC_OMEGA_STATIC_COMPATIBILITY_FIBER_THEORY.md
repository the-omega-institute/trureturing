# AURIC Ω 静态相融纤维理论

*AURIC Omega Static Compatibility–Fiber Theory*

## 1. 共同对象、历史与量子接口

**定义 1.1（静态相融对象）。** 设事件集 $E$ 有限或可数，偏序为 $\leq$，每个主下集 $\downarrow e$ 有限。设 $\mathcal C$ 是有限事件集组成的族，含空集及全部单点，满足子集封闭及 $A\in\mathcal C\Rightarrow\downarrow A\in\mathcal C$。配置是向下闭的 $C\subseteq E$，且其每个有限子集属于 $\mathcal C$。记全部配置为 $\operatorname{Conf}$，有限配置为 $\operatorname{Conf}_{\mathrm{fin}}$。配置 $C,D$ 相融，意为 $C\cup D$ 仍是配置。符号 $\Omega$ 表示这些配置、因果关系、允许的局部运输与读出的共同数学对象；它不要求所有配置两两相融，也不要求相融关系传递。事件的身份包含其关系位置，同一门标签在两个位置出现是两个事件。此处采用 Winskel 的事件结构与配置域思想；后文只使用上述明确给出的版本。

**定义 1.2（正历史与内生时钟）。** 有限配置间的基本边为

$$
C\xrightarrow{e}C\cup\{e\},\qquad e\notin C,\quad C\cup\{e\}\in\operatorname{Conf}_{\mathrm{fin}}.
$$

历史是基本边组成的有限路径，长度为边数。观察者 $o$ 的事件支撑为 $E_o\subseteq E$，其局部记录为 $O_o(C)=C\cap\downarrow E_o$。局部读数 $q_o$ 满足 $O_o(C)=O_o(D)\Rightarrow q_o(C)=q_o(D)$，选择规则 $\kappa_o:Y_o\to\mathcal P(\Sigma)$ 只依赖该记录。给每个计数事件严格正权重 $\omega(e)>0$，定义

$$
\tau_o(C)=\sum_{e\in C\cap E_o}\omega(e).
$$

对无限配置，这个和按有限部分和的上确界取值于 $[0,+\infty]$；若只使用实值时钟，就限于有限配置，或另加可求和条件。历史长度、这个加权时钟及等待参数是不同的量。

**假设 1.3（附加的量子表示）。** 每个量子端口是有限维复 Hilbert 空间；并置端口用张量积，允许纠缠；状态是正半定、迹一算子。效果为 $0\leq E\leq I$，概率按 $\operatorname{tr}(\rho E)$ 给出，局部操作由完全正映射表示，非选择操作保迹。第 6 节说明这些表示假设与效果概率的关系。这些假设不能由配置静态性或历史长度正性推出。事件字 $w$、实际仪器输出记录 $h$、振幅展开中的求和路径 $p$ 分别记号；只有实际进入记录端口的数据才是经典记录。

**定义 1.4（五模式及两个设置）。** 取 $\mathcal H=\mathbb C^5$，按

$$
(e_N,e_2,e_3,e_5,e_{25})
$$

排序的单位正交基及 $\Pi_s=e_se_s^\dagger$。$N$ 是一个范数为一的模式，既不是零向量，也不是 Stop。输入遍历全部复密度算子。固定

$$
K=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix},\qquad U(t)=e^{-itK},\quad t\geq0.
$$

一次读是完整秩一 Lüders 仪器 $\mathcal J_s(X)=\Pi_sX\Pi_s$。实际菜单只含同一生成元的非负等待、这项完整读及 Stop，允许有限深度的记录反馈和输入无关的经典随机控制。初始控制资料独立于未知输入，不提供输入副本、参考纠缠或额外量子载体。不把相同效果的其他仪器、独立相位或任意酉加入菜单。一次完整读的结果可以经典合并，但这不是额外的粗块 Lüders 仪器。

作被动变基

$$
\begin{aligned}
D&=\operatorname{diag}(1,i,i,i,1),\\
A&=-iD^\dagger KD=
\begin{pmatrix}
0&1&1&1&0\\
-1&0&0&0&-1\\
-1&0&0&0&0\\
-1&0&0&0&-1\\
0&1&0&1&0
\end{pmatrix},\\
O(t)&=D^\dagger U(t)D=e^{tA},\qquad Q_s(t)=O(t)^T\Pi_sO(t).
\end{aligned}
$$

$A^T=-A$，故 $O(t)$ 实正交。以下密度矩阵和通道均在此实帧中表示；$D$ 不增加任何控制权限。设置 $t$ 的分布为 $p_t(\rho)_s=\operatorname{tr}(Q_s(t)\rho)$，两个指定设置为 $t=0$ 及 $t_*=2/3$。$2/3$ 是数学等待参数，不指定秒或事件数。这个五模式行走及完整实际菜单来自 [《AURIC FIB 二阶关系完成》§§65、79](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md) 与 [《实际等待读出下的近似单份量子边界》§1](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md)。

**定义 1.5（同一个经典—量子端口）。** 对正整数 $q\leq5$，允许一个任意有限经典标记集 $F$ 及固定 CPTP 映射

$$
\operatorname{Enc}:M_5(\mathbb C)\longrightarrow\bigoplus_{f\in F}M_q(\mathbb C),\qquad
\operatorname{Dec}:\bigoplus_{f\in F}M_q(\mathbb C)\longrightarrow M_5(\mathbb C).
$$

记 $T=\operatorname{Dec}\circ\operatorname{Enc}$，所有此类通道的集合为 $\mathfrak C_q$。每个标记块上的解码器在整个 $M_q$ 上 CPTP。标记分布可以依赖输入，标记数不预先统一限定；编解码器在未来设置选择之前固定。全部输入相关量子信息必须经过该端口；无原输入副本、预共享纠缠或量子旁路。解码后的未来策略只接收输出态与输入无关的初始控制资料，标记不另外成为策略的输入。定义

$$
\begin{aligned}
e_{\mathrm{two}}(T)&=\sup_{\rho\in\mathcal D(\mathcal H)}
\max_{t\in\{0,2/3\}}\operatorname{TV}(p_t(\rho),p_t(T(\rho))),\\
\varepsilon_{\mathrm{two}}(q)&=\inf_{T\in\mathfrak C_q}e_{\mathrm{two}}(T),\qquad
\operatorname{TV}(p,p')=\frac12\sum_s|p_s-p'_s|.
\end{aligned}
$$

这采用 Bluhm–Rauber–Wolf 的 measurement-relative compression 合同（Definition 4.1），以共同量子态解码供后来设置使用。CPTP 的合法性要求包括任意辅助系统，性能量度本身只测试上述系统分布。

## 2. 双设置应用与全篇证明的目标

**定理 2.1（静态相融表示中的双设置端口界）。** 在定义 1.1–1.5 的表示中，有限维、有限结果及有限控制分支的实际协议，在固定输入无关随机资料后可以表示为固定的因果端口关系图，精确保留实际记录联合分布；正历史计数、观察响应纤维和合法量子端口维数分别由各自的关系决定。对指定五模式行走，只要同一 CPTP 通道对全部复密度输入精确保留 $t=0,2/3$ 的完整五结果分布，就有 $T=\operatorname{id}_5$。因此定义 1.5 中精确端口的最小块维数为五；并且对 $q=1,2,3,4,5$，

$$
\boxed{\displaystyle\varepsilon_{\mathrm{two}}(q)\geq\frac{5-q}{102}},\qquad
\varepsilon_{\mathrm{two}}(5)=0.
$$

与此同时，全非负等待菜单的归一化响应只有十四个实线性坐标，在全秩态附近有十维盲纤维，且存在菜单不能区分的正交纯态。后两项复用既有五模式效果空间与首读归约；它们与双设置端口界相容，不提供一个可以对全体输入统一删除盲方向的 CPTP 商。

证明分为以下相互衔接的部分。第 3–5 节构造经典正历史、局部相融与目标商，明确哪些区别已被读出遗忘；第 6–8 节在额外量子概率假设下构造实际记录、历史表示和恢复边界；第 9 节把已有原生树及五模式响应空间接到同一个目标商上；第 10 节使用已知的无扰动结构证明一般探针端口公式；第 11 节给出本行走的两个设置以及定量估计；第 12 节证明有限协议与静态图的双向表示，并给出无限延拓的确切范围。这些部分共同证明定理；其中的标准中间事实均按来源使用，不另称 AURIC 的新发现。

## 3. 主定理的经典输入：配置、时钟与运输

**定义 3.1（有限配置上的读出运输）。** 对每个有限配置给一个集合 $S_C$，每条基本边给 $T_{C,e}:S_C\to S_{C\cup\{e\}}$。一条路径的运输是按路径次序的复合。若 $e,f$ 在 $C$ 后可按两种次序合法添加，称这两条长度二路径为一个合法交换菱形。

证明中的配置步骤采用事件结构的配置域结论，以下给出所需假设如何进入证明。非空有向族 $\mathcal D\subseteq\operatorname{Conf}$ 的并向下闭；其有限子集由有向性包含在同一个 $C\in\mathcal D$ 内，故相容。因此 $\bigcup\mathcal D$ 是配置。对任意配置 $C$，每个有限 $A\subseteq C$ 的闭包 $\downarrow A$ 有限且仍在 $C$ 中；这些有限子配置按并有向，其并是 $C$。

令理想指 $\operatorname{Conf}_{\mathrm{fin}}$ 中非空、向下闭、有向的子集。映射

$$
C\longmapsto\{D\in\operatorname{Conf}_{\mathrm{fin}}:D\subseteq C\},\qquad
\mathcal I\longmapsto\bigcup\mathcal I
$$

互逆且保持包含。关键反向是：若有限配置 $D\subseteq\bigcup\mathcal I$，可为 $D$ 的每个事件选一个含它的理想元素，再用有限次有向性找到同一个上界，向下闭性遂给 $D\in\mathcal I$。这里不能省掉有限前驱闭包。以上是 Winskel 配置域方法在定义 1.1 下的直接应用。

若有限配置 $C\subseteq D$，取 $D\setminus C$ 的任一偏序线性扩张逐项添加。每个中间集合向下闭，并包含在合法配置 $D$ 内，所以合法。反向，每条基本边只加一个事件，路径当然要求 $C\subseteq D$。每条这样的路径长度恒为

$$
\ell(C,D)=|D\setminus C|,
\qquad\ell(C,F)=\ell(C,D)+\ell(D,F)\quad(C\subseteq D\subseteq F).
$$

非空追加路径不能有一条追加逆路径，因为包含不能沿非空边反转。这个断言不排除边上读出算子可逆。加权时钟包含单调；在有限配置上有新计数事件时，由严格正权重而严格增长。无限和已为 $+\infty$ 时不声称严格增长。把一个事件细分为依次发生的 $e_1,\ldots,e_m$，保时长当且仅当 $\omega(e)=\sum_j\omega(e_j)$；这是加性要求，不是自动的单位选择。

运输的路径无关性恰等价于每个合法菱形交换：必要性取这两条路径；充分性使用有限偏序任意两个线性扩张可由相邻不可比项的交换连接。可用归纳证明后一个事实：把目标线性扩张的首元素向左移动，跨过的元素均与它不可比，然后对余序归纳。每次交换对应一个合法菱形，故不改复合。于是给定 $s_\varnothing\in S_\varnothing$，从空配置运输得到唯一满足全部边关系的静态赋值 $s_C$。若菱形不交换，同一个终配置可以得到不同值，便必须保留路径信息，或扩大读出空间；不能无条件忘掉顺序。

这也限定了“固定整体”的含义。可取有共同前驱 $a$、互斥后继 $b,c$ 的事件结构，则 $\{a,b\}$ 与 $\{a,c\}$ 都是配置，二者之并不是配置。它们同在 $\Omega$ 中不表示它们同属一条实际历史。

## 4. 主定理的经典输入：保留什么，商掉什么

**定义 4.1（任意目标族的响应商）。** 设 $X$ 为共同源，$Q$ 为任意指标集，每个 $q\in Q$ 给一个映射 $R_q:X\to Y_q$。定义

$$
x\sim_Qx'\quad\Longleftrightarrow\quad\forall q\in Q,\ R_q(x)=R_q(x').
$$

响应商是 $X/{\sim_Q}$，也可用联合映射 $x\mapsto(R_q(x))_{q\in Q}$ 的像表示。这个定义不要求有限目标族。若 $Q=\varnothing$，非空源只有一个类；空源的商为空。

证明所用的最小性是一般因子化原理。编码 $E:X\to Z$ 能恢复每个 $R_q$，即存在 $d_q$ 使 $R_q=d_q\circ E$，当且仅当每个 $R_q$ 在 $E$ 的纤维上常值；解码器自然定义在达到像 $E(X)$ 上。因此 $E(x)=E(x')\Rightarrow x\sim_Qx'$。反之，响应商上的 $[x]\mapsto R_q(x)$ 良定义。这是既有目标族最小商原理的直接使用，不要求凭空扩大一个有限指标集。

取单个读出 $R:X\to Y$ 与时钟 $\tau:X\to\mathbb N$，便有

$$
\tau=\bar\tau\circ R\text{ 于 }R(X)
\quad\Longleftrightarrow\quad
R(x)=R(x')\Rightarrow\tau(x)=\tau(x').
$$

串行字 $g\bar g$ 的算子读出可为 $I$，空字 $\varepsilon$ 的读出也是 $I$，但长度分别为二和零。故可逆算子读出不能恢复正历史计数。$(R,\tau)$ 是同时保留这两个目标的最小补全：任何能恢复二者的 $Q$ 均能恢复该有序对；这个有序对仍未必恢复整个历史。

这一遗漏可以指数增长。取 $r\geq2$ 个字面不同、长度均为二的中性块 $c_i=g_i\bar g_i$，各块算子读出均为 $I$。由 $k$ 个块串接得到的字长都是 $2k$，读出都是 $I$。把字依次切成固定长度二的块能唯一读回块指标，故不同指标序列给不同字，共 $r^k$ 个。若附加记忆 $M$ 与 $(R,\tau)$ 能精确恢复这些字，$M$ 在这族上必须单射，于是

$$
|\operatorname{range}M|\geq r^k,
\qquad b\geq\lceil k\log_2r\rceil
$$

对固定宽度二进制编码成立。这个下界来自同一读出—时钟纤维内的不同字，不能用重复块中没有区别的标签凑数。

**定义 4.2（全部未来与非法延拓）。** 设 $L\subseteq\Sigma^*$ 前缀闭，$q:L\to Y$，取 $\bot\notin Y$，把 $q$ 扩为 $\widetilde q:\Sigma^*\to Y\sqcup\{\bot\}$，非法字一律取 $\bot$。令

$$
w\equiv w'\quad\Longleftrightarrow\quad
\forall v\in\Sigma^*,\ \widetilde q(wv)=\widetilde q(w'v).
$$

在 Myhill–Nerode 的未来不可区分原理中取多值输出，便得到这里的确定观察者。关系右稳定，因为对任意 $g$，测试 $(wg)v$ 就是测试 $w(gv)$。因此商载体是全部 $\Sigma^*/{\equiv}$，更新 $[w]\mapsto[wg]$ 与输出 $[w]\mapsto\widetilde q(w)$ 良定义。载体不能只取 $L$ 而仍宣称每个 $g$ 给总更新。非法字的任意延拓仍非法，由前缀闭性可知它们属于同一个吸收类。

若某确定内部状态 $m(w)$ 经当前状态解码能精确保留每个未来输出，则 $m(w)=m(w')$ 使任意共同后缀后的状态仍相同，因而 $w\equiv w'$。这给最小性，而不承诺商必有限。精确输出无界合法字长时，选取长度两两不同的合法词，其当前输出已经两两不同，所以有限状态观察者不可能完成该任务；若任务域含长度 $0,\ldots,N$ 且须区分它们，至少需要 $N+1$ 个状态及 $\lceil\log_2(N+1)\rceil$ 位。给观察者一个外部时钟、可读日志或未计入的接口会改变状态模型；这些信息必须与 $m$ 一起计算。这里使用 Kozen 的 Myhill–Nerode 论证，不把该最小性改称新的自动机定理。

## 5. 主定理的经典输入：局部拼接与边界唯一性

**定义 5.1（约束赋值）。** 给位置集 $V$、纤维 $S_v$，对指定有限支撑 $K\subseteq V$ 给允许关系 $R_K\subseteq\prod_{v\in K}S_v$。$F(B)$ 是 $B$ 上满足所有支撑完全落在 $B$ 内的约束的赋值。边界读出 $R_B$ 对指定合法内部集合 $S$ 的精确全息性，意为 $R_B|_S$ 单射；若只要恢复目标 $f$，则要求 $f$ 在这些边界纤维上常值。

在主定理的关系图中，局部图块必须保留完整的跨接口约束。具体地，若 $B=\bigcup_i B_i$ 且每个 $K\subseteq B$ 的指定约束支撑完整落在某个 $B_i$，则重叠一致的 $s_i\in F(B_i)$ 给唯一赋值 $s(v)=s_i(v)$。每个约束可在拥有整个支撑的区域验证，故 $s\in F(B)$。这是集合赋值的粘合原理及约束局部性的直接应用。支撑条件不可删：布尔约束 $x\oplus y\oplus z=0$ 的三个二元区域，可以分别取来自 $(0,0,1)$ 的限制；它们重叠一致且局部无完整三元约束，却不能拼成满足该关系的全局赋值。

可数相容极限还需要紧致性。若

$$
X_0\xleftarrow{r_0}X_1\xleftarrow{r_1}X_2\xleftarrow{}\cdots
$$

各层有限非空，限制映射总定义，即使不满射也有非空逆极限。把相容有限串 $(x_0,\ldots,x_n)$ 组成树；从任意 $x_n$ 向前限制得到长度 $n+1$ 的串，故每层非空；每层有限使树有限分支。König 引理给无穷支，正是一致序列。有限性不能只换成非空：$X_n=\{m\in\mathbb N:m\geq n\}$、限制为包含，则一致序列须始终取同一个属于全部尾集的自然数，不存在。这里使用标准紧致性结论，不由“静态”一词保证无穷整体。

线性边界给一个可计算的特例。对 $S=\ker M\subseteq\mathbb K^n$ 与坐标投影 $P_B$，线性性给

$$
P_B|_S\text{ 单射}
\ \Longleftrightarrow\ \ker M\cap\ker P_B=\{0\}
\ \Longleftrightarrow\
\operatorname{rank}\begin{pmatrix}M\\P_B\end{pmatrix}=n.
$$

因为两个内部解边界相同，当且仅当其差在该交核内。此条件不说每个边界值都能实现；可实现边界只是 $P_B(S)$。它也不说逆映射满足量子完全正性，第 8 节将区分这两件事。

**定义 5.2（双射运输与回路）。** 在连通图每个顶点 $v$ 放一个集合 $S_v$，每条定向边放一个双射，反边运输取逆。固定根 $r$。平行赋值是每条边都满足运输关系的顶点赋值。

选一条根到 $v$ 的路径，运输记为 $V_v:S_r\to S_v$。全局平行赋值的根值必须被所有根闭走运输固定；反之若 $x\in S_r$ 被所有根闭走固定，令 $s_v=V_vx$。两条根到 $v$ 的路径之差是闭走，故定义与选路无关，并满足每条边。这样全局平行赋值与共同不动点一一对应。一个根值被回路固定，不要求整个回路算子为恒等。若图是树，以 $V_v^{-1}$ 为顶点坐标变换，边运输全部变为恒等；历史边数仍可非零。反边的形式运输逆是集合或向量空间中的逆，不在正历史中增加一条删除过去事件的边。

上述经典部分提供定理 2.1 所需的三层区分：配置的并只在相融时合法，运输读出可以忘掉正长度，目标商只忘掉声明目标看不到的区别。把这些构造组合称作静态相融结构不增加一个新的普遍定理；主定理还须对其量子实现施加以下条件。

## 6. 主定理的概率前提：效果、通道与实际记录

**假设 6.1（效果概率）。** 在有限维复空间上，为全部效果 $0\leq E\leq I$ 给 $p(E)\geq0$，满足 $p(I)=1$；当 $E+F\leq I$ 时 $p(E+F)=p(E)+p(F)$；同一个效果在不同测量语境中的概率相同。最后这项是效果非语境性，不是为互不相容的设置预设共同的确定答案。

主定理使用的 Born 表示可按 Busch 的效果版本 Gleason 论证取得，包括二维。先由可加性得 $p(0)=0$、$p(E)\leq1$，以及 $E\leq F\Rightarrow p(E)\leq p(F)$。把效果分成 $n$ 个相同部分给 $p(E/n)=p(E)/n$，再得允许范围内的有理齐次性。用上下逼近的有理数及单调性得到实齐次性。对正算子 $B$ 取整数 $n\geq\|B\|$，定义 $\ell(B)=n p(B/n)$；利用共同整数倍及前述齐次性可见它不依赖 $n$。对 $B,C\geq0$，用足够大的同一 $n$ 得 $\ell(B+C)=\ell(B)+\ell(C)$。于是

$$
\ell(B-C)=\ell(B)-\ell(C)
$$

给自伴空间上良定义的实线性泛函：若 $B-C=B'-C'$，就用 $B+C'=B'+C$ 的正锥可加性。有限维迹对偶给唯一自伴 $\rho$ 使 $\ell(H)=\operatorname{tr}(\rho H)$；在秩一投影上非负给 $\rho\geq0$，归一化给 $\operatorname{tr}\rho=1$。复线性延拓也唯一。纯态 $\rho=|\psi\rangle\langle\psi|$ 对秩一投影的概率便是 $|\langle\phi,\psi\rangle|^2$。这里真正使用的是全部效果及其可加结构；仅给静态配置集合不能推出这个概率律。

**定义 6.2（完全正性与仪器）。** 复线性 $\Phi:M_d\to M_e$ 完全正，意为 $\Phi\otimes\operatorname{id}_{M_n}$ 对每个 $n$ 都保持正性。仪器是一族完全正分支 $\mathcal J_a$，其和保迹；只有 $a$ 是输出记录，分支内部的 Kraus 指标一般不是输出。

这里使用 Choi–Kraus–Stinespring 表示（Watrous，Theorems 2.22、2.26 及 Corollary 2.27）。为固定约定，令 $\Gamma_d=\sum_i e_i\otimes e_i$，$\Phi$ 作用于第一因子，则

$$
C_\Phi=(\Phi\otimes\operatorname{id})(|\Gamma_d\rangle\langle\Gamma_d|)
=\sum_{i,j}\Phi(|i\rangle\langle j|)\otimes|i\rangle\langle j|.
$$

完全正性给 $C_\Phi\geq0$。谱分解写成 $C_\Phi=\sum_\mu|K_\mu\rangle\!\rangle\langle\!\langle K_\mu|$，其中 $|K\rangle\!\rangle=\sum_i Ke_i\otimes e_i$，逐矩阵单位比较得

$$
\Phi(X)=\sum_\mu K_\mu X K_\mu^\dagger.
$$

反过来每项在任意辅助因子上都是共轭，故完全正。迹保留等价于 $\sum_\mu K_\mu^\dagger K_\mu=I$，因为对每个 $X$ 的迹差等于 $\operatorname{tr}(X(\sum K_\mu^\dagger K_\mu-I))$。一般正性不够：转置保持正矩阵，但归一 Bell 投影在部分转置下变为交换算子的一半，谱为 $1/2,1/2,1/2,-1/2$，故转置不是完全正。

允许噪声与记录反馈时，对每个已得记录 $h$ 给

$$
\mathcal J_{a|h}(X)=\sum_\mu K_{a\mu|h}XK_{a\mu|h}^\dagger,
\qquad\sum_{a,\mu}K_{a\mu|h}^\dagger K_{a\mu|h}=I.
$$

置 $\sigma_\varnothing=\rho_0$、$\sigma_{ha}=\mathcal J_{a|h}(\sigma_h)$。逐层有

$$
p(h)=\operatorname{tr}\sigma_h\geq0,
\qquad\sum_a p(ha)=p(h).
$$

有限深度且每条分支完结的协议，反复应用此等式得全部叶概率之和为一。只有 $p(h)>0$ 时才定义条件态 $\rho_h=\sigma_h/p(h)$；零概率分支仍有未归一化态零，不需要除法。若环境以后重新参与相互作用，就把它留在接口内；把它先迹掉再假定系统闭合，会改变模型。

对终端效果 $E$，复合仪器 $\mathcal J_h$ 满足

$$
\Pr(h,E)=\operatorname{tr}(E\mathcal J_h(\rho_0))
=\operatorname{tr}(\rho_0\mathcal J_h^\dagger(E)).
$$

这把未来目标拉回指定参考边界；该边界不必是宇宙最早时刻。它是第 4 节目标族在量子表示中的实现：目标是每个合法协议及其实际记录事件的概率，而不是没有指定仪器的形式路径标签。

## 7. 主定理的表示前提：正历史、相干与内生记录

**定义 7.1（历史 Hilbert 空间与长度算子）。** 对有限非空字母表 $\Sigma$，令 $\mathcal H_{\mathrm{hist}}=\ell^2(\Sigma^*)$，正交基为 $|w\rangle$。右追加 $S_g|w\rangle=|wg\rangle$，长度乘法算子为 $N|w\rangle=|w||w\rangle$，其自然定义域是

$$
\mathcal D(N)=\left\{\sum_w a_w|w\rangle:\sum_w|w|^2|a_w|^2<\infty\right\}.
$$

这是自由半群的标准右移表示；它用于把第 3 节的历史箭头与系统算子逆分开。$S_g$ 是等距，$S_g^\dagger$ 删除末尾 $g$，在其他基向量上取零。因此

$$
S_g^\dagger S_g=I,\qquad
S_gS_g^\dagger=P_{\text{末尾为 }g}\ne I.
$$

有限支撑向量构成 $N,S_g,S_g^\dagger$ 的共同不变稠密定义域，在这个域上直接算基向量得 $NS_g-S_gN=S_g$。这是无界算子恒等式的定义域陈述，不能写成全空间有界算子等式。即使系统门 $U_{\bar g}=U_g^{-1}$，历史追加也有

$$
S_{\bar g}S_g|w\rangle=|wg\bar g\rangle\ne|w\rangle,
\qquad S_{\bar g}\ne S_g^\dagger.
$$

**定义 7.2（有限传播约束）。** 设有限维 $H$ 上有酉序列 $U_1,\ldots,U_T$，在 $H^{\oplus(T+1)}$ 上定义

$$
\mathcal D_T(x_0,\ldots,x_T)
=(x_1-U_1x_0,\ldots,x_T-U_Tx_{T-1}),\qquad
\mathcal K_T=\mathcal D_T^\dagger\mathcal D_T.
$$

主定理的静态历史使用标准传播 Hamiltonian 的零空间构造。因为 $\langle x,\mathcal K_Tx\rangle=\|\mathcal D_Tx\|^2$，$\mathcal K_T\geq0$ 且其核恰是满足每一步传播关系的整条轨迹。映射

$$
J\psi=\frac1{\sqrt{T+1}}(\psi,U_1\psi,U_2U_1\psi,\ldots,U_T\cdots U_1\psi)
$$

保内积，且任意核向量由首项唯一决定，故是 $H$ 到 $\ker\mathcal K_T$ 的等距同构。这里算子正性来自平方范数，历史长度正性来自追加计数，两者没有互相推出。

相干读出则使用有限张量收缩的标准展开。对输出 $y$ 的内部路径纤维 $F_y$，每条路径振幅 $A_p$ 是局部矩阵元乘积；若没有可区分路径记录，则

$$
a_y=\sum_{p\in F_y}A_p,\qquad P(y)=\left|\sum_{p\in F_y}A_p\right|^2.
$$

若路径关联到归一记录向量 $m_p$，联合分量是 $\sum_p A_p|y\rangle\otimes|m_p\rangle$，不访问记录器时有

$$
P(y)=\sum_{p,q\in F_y}A_p\overline{A_q}\langle m_q,m_p\rangle.
$$

相同记录保留全部干涉；两两正交记录使交叉项消失。路径索引本身不是一个已存在且正交的物理记录。两个 Hadamard 门之间给中间 $0,1$ 支路附记录 $m_0,m_1$，直接展开第二个门得到

$$
P(0)=\frac{1+\operatorname{Re}\langle m_0,m_1\rangle}{2},\qquad
P(1)=\frac{1-\operatorname{Re}\langle m_0,m_1\rangle}{2}.
$$

没有记录时 $m_0=m_1$，$P(0)=1$；正交且弃置记录时 $P(0)=1/2$。这是量子电路及 which-way 干涉公式在本表示中的应用，而非由经典相容集直接得出的概率。

内生记录由有限仪器的 Stinespring 等距给出：

$$
V\psi=\sum_{a,\mu}K_{a\mu}\psi\otimes|a,\mu\rangle,
\qquad V^\dagger V=I.
$$

记录投影 $P_a=\sum_\mu|a,\mu\rangle\langle a,\mu|$ 后迹掉记录器，得到 $\mathcal J_a(\rho)$；其迹和正概率条件态正是第 6 节的定义。等距可在添入初始化辅助空间、必要时补齐维数之后扩充成酉；有限反馈可由受正交记录控制的后继酉实现。无记录的 Kraus 标签不因这项数学扩充自动成为观察者可读数据。

这项构造不提供任意态克隆。若一个统一等距把每个单位向量 $\psi$ 变成 $\psi\otimes\psi$，则两输入的内积 $z$ 满足 $z=z^2$，与 $0<|z|<1$ 矛盾。即使允许依赖输入的弃置辅助态，内积绝对值也要求 $|z|\leq|z|^2$，仍矛盾。该步骤使用标准不可克隆论证；内生仪器模型也不裁决单次结果体验的本体论。

现在把观察者、记忆及以后还会返回的环境一并放进有限整体，令 $\psi_k=W_k\cdots W_1\psi_0$。归一的静态历史向量为

$$
|\Omega_T\rangle=\frac1{\sqrt{T+1}}\sum_{k=0}^T|k\rangle\otimes|\psi_k\rangle.
$$

它是定义 7.2 的传播核表示；钟投影的未归一分量为 $\psi_k/\sqrt{T+1}$。多时刻实验仍按实际仪器计算，不能把任意钟测量解释成无扰动读取。若 $W_2=W_1^\dagger$，则系统 $\psi_2=\psi_0$，而 $|2\rangle\perp|0\rangle$；通道 $\rho\mapsto\rho\otimes|2\rangle\langle2|$ 合法，系统恢复误差为零。因此“历史没有被删”并不推出系统恢复必有正误差。

若另给可微的有限维单参数酉群 $U(\tau)$、群律及非零实数 $\hbar$，令 $G=U'(0)$。微分 $U(\tau)^\dagger U(\tau)=I$ 得 $G^\dagger=-G$；群律给 $U'(\tau)=GU(\tau)$。所以 $H=i\hbar G$ 自伴，

$$
U(\tau)=e^{-iH\tau/\hbar},\qquad
 i\hbar\frac{d\psi}{d\tau}=H\psi.
$$

这是有限维酉群微分方程的应用；连续校准和群律是附加条件，事件计数没有自动变成这个连续参数。

## 8. 主定理的合法性边界：共同实现与量子恢复

共同量子对象不等于共同经典答案表。主定理不把第 5 节的经典赋值拼接强加给不相容量子设置。CHSH 的标准计算说明原因：若在同一个设置无关概率空间上有 $\pm1$ 变量 $A_0,A_1,B_0,B_1$，则每一点的

$$
A_0(B_0+B_1)+A_1(B_0-B_1)
$$

恰为 $\pm2$，故期望绝对值不超过二。而 Bell 态 $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$ 与

$$
A_0=Z,\quad A_1=X,\quad
B_0=(Z+X)/\sqrt2,\quad B_1=(Z-X)/\sqrt2
$$

有 $\langle Z\otimes Z\rangle=\langle X\otimes X\rangle=1$、两个交叉期望为零，CHSH 值为 $2\sqrt2$。同一密度态统一这些设置的概率，却不满足上述共同经典变量假设。另一方面，局部 POVM 的归一化给

$$
\sum_b p(a,b|x,y)
=\operatorname{tr}\bigl(\rho(E_{a|x}\otimes\sum_bF_{b|y})\bigr)
=\operatorname{tr}(\rho(E_{a|x}\otimes I)),
$$

所以边缘与远端设置 $y$ 无关。这是 no-disturbance 的量子实现，不是对每个未选设置赋共同实际值。

重叠边缘一致也不保证量子拼接。若 $\rho_{AB}$ 与 $\rho_{BC}$ 各为 Bell 纯态，它们在 $B$ 上都为 $I/2$。假定存在共同 $\rho_{ABC}$，令 $P=\rho_{AB}$。正性及 $\operatorname{tr}((I-P)\otimes I\,\rho_{ABC})=0$ 使全态支撑落在 $\operatorname{ran}P\otimes H_C$，故 $\rho_{ABC}=P\otimes\sigma_C$。于是 $BC$ 边缘为 $I_B/2\otimes\sigma_C$，不可能是 Bell 态。量子相融所需的是共同正、迹一实现，不只是重叠一致。

**定义 8.1（量子边界与互补接口）。** 设 $L,B,E$ 为有限维复 Hilbert 空间，且 $\dim L>0$。给等距编码 $V:L\to B\otimes E$，令

$$
\mathcal N_B(X)=\operatorname{tr}_E(VXV^\dagger),\qquad
\mathcal N_E(X)=\operatorname{tr}_B(VXV^\dagger).
$$

在定义 8.1 的非零逻辑空间范围内，主定理所用的量子恢复边界是标准 information–disturbance／量子纠错条件：存在定义在整个 $M(B)$ 上的同一个 CPTP 映射 $\mathcal R:M(B)\to M(L)$，使 $\mathcal R\mathcal N_B(\rho)=\rho$ 对全部 $\rho\in\mathcal D(L)$ 成立，当且仅当有固定密度态 $\sigma_E$ 使

$$
\mathcal N_E(X)=\operatorname{tr}(X)\sigma_E\qquad\text{对全部 }X\in M(L).
$$

密度输入上的常值性与这个全线性扩展等价，因为秩一投影张成自伴空间，自伴空间复线性张成整个矩阵空间；同理，恢复等式等价于 $\mathcal R\mathcal N_B(X)=X$ 对全部 $X\in M(L)$ 成立。以下给出该标准条件的有限维证明，以明确“全部输入”如何进入。

充分性：取逻辑基 $|i\rangle$，零谱方向的编码分量由正性为零；在 $\sigma_E$ 正支撑上写 $\sigma_E=\sum_j\lambda_j|j\rangle\langle j|$，$\lambda_j>0$。令

$$
V|i\rangle=\sum_j\sqrt{\lambda_j}\,|b_{ij}\rangle\otimes|j\rangle.
$$

互补条件用于矩阵单位 $|i\rangle\langle k|$ 给

$$
\sqrt{\lambda_j\lambda_l}\langle b_{kl},b_{ij}\rangle
=\delta_{ik}\lambda_j\delta_{jl},
$$

所以全部 $b_{ij}$ 正交归一。$B$ 中其张成空间可等距识别为 $L\otimes\operatorname{supp}\sigma_E$；$\mathcal N_B(\rho)$ 在该识别下是 $\rho\otimes\sum_j\lambda_j|j\rangle\langle j|$。解码为先取此子空间、逆等距并迹掉第二因子，在正交补上以其迹乘固定逻辑密度态 $\tau_L$ 补全；$\dim L>0$ 保证 $\tau_L$ 存在。两项均完全正且总迹保持，因而这是全 $M(B)$ 上的合法恢复。

必要性：取恢复的 Stinespring 等距 $W:B\to L\otimes F$，令 $U=(W\otimes I_E)V$。对每个纯逻辑输入，输出的 $L$ 边缘是同一个纯态，故 $U|\psi\rangle=|\psi\rangle\otimes|\eta_\psi\rangle$。在逻辑基及其两两叠加上应用线性性，得到同一个辅助单位向量 $\eta$，使 $U|\psi\rangle=|\psi\rangle\otimes|\eta\rangle$ 对所有 $\psi$ 成立。迹掉 $L,F$ 得到固定环境态 $\sigma_E=\operatorname{tr}_F|\eta\rangle\langle\eta|$；$W$ 是等距，故未改变原来的 $E$ 边缘。必要性成立。纠错与环境信息条件见 Knill–Laflamme 及 Schumacher–Nielsen 的标准理论。

零维边界命题：上述恢复等价不能无条件推广到零维逻辑空间。证明：取 $L=\{0\}$、$B=E=\mathbb C$，零映射 $V$ 满足 $V^\dagger V=I_L=0$，因而等距。此时 $\mathcal D(L)=\varnothing$，密度输入上的常值性空泛成立；取 $\sigma_E=1$，全线性条件也成立，因为 $M(L)=\{0\}$。但从 $M(B)=\mathbb C$ 到 $M(L)=\{0\}$ 的唯一线性映射把 $1$ 送到 $0$，迹从一变为零，不能保迹。

第 5 节的线性单射比该条件弱。例如 qubit 的可逆去极化线性映射 $\mathcal N(\rho)=a\rho+(1-a)I/2$，$0<a<1$，在迹一仿射空间上单射，其线性逆却把某些纯态送到非正算子；若存在全态 CPTP 左逆，它在该有限维满像张成空间上只能是这个不正的逆，矛盾。因此统计反演、恢复一个目标函数、与恢复全部量子输入是三种不同要求。

## 9. 主定理的具体共同源：FIB 模式与未来响应

**定义 9.1（无相邻激活的五模式窗口）。** 合法布尔字不含子字 $11$。长度三的五个合法字按

$$
000,\quad100,\quad010,\quad001,\quad101
$$

排列；给三个位置权重 $2,3,5$，分别对应 $\varnothing,\{2\},\{3\},\{5\},\{2,5\}$，即定义 1.4 的五模式。模式 $N$ 对应 $000$；它是长度三、零激活的窗口，不是空历史 $\varepsilon$。其 Hilbert 基向量仍有范数一。

这一窗口构造使用 Fibonacci 计数的标准递推。约定 $\operatorname{Fib}(0)=0,\operatorname{Fib}(1)=1$。长度 $n$ 合法数 $a_n$ 满足 $a_0=1,a_1=2$；按末尾为 $0$、或末尾 $01$ 分解得 $a_n=a_{n-1}+a_{n-2}$，故 $a_n=\operatorname{Fib}(n+2)$。连续三窗口若相邻重叠两位一致，就唯一确定覆盖区间的全字；至少有一个窗口且覆盖每对相邻位置时，每对都被某个合法窗口约束，故全字合法。反之合法全字自然给这样的窗口族。末尾窗口 $000$ 不能恢复全长，例如 $000$ 与 $0000$ 均合法且末尾窗口相同。这是第 4 节纤维遗漏的一个具体实现。

量子制备不是把这些模式当成五种互不相干的未知经典标签。全部 $\mathbb C^5$ 密度态的实仿射维数为 $25-1=24$。在临时记号 $(\varnothing,1,2,3,13)$ 下，以 $1,2,3$ 表示三个激活位置，令

$$
X=p_1+p_{13},\qquad Z=p_2,\qquad Y=p_3+p_{13}.
$$

固定这三个均值后，对角部分由 $\kappa=p_{13}$ 参数化：

$$
p_\varnothing=1-X-Z-Y+\kappa,\quad
p_1=X-\kappa,\quad p_2=Z,\quad
p_3=Y-\kappa,\quad p_{13}=\kappa.
$$

这里 $p_i=\rho_{ii}$，$p_{13}$ 是双激活模式的对角概率，不是单激活模式之间的相干矩阵元 $\rho_{1,3}$。在任意满秩态附近，正定性是开条件，固定三个独立均值的局部纤维有一维对角变化及十个复非对角变化，共二十一实维。低秩边界可能使实际纤维维数下降，不能一律使用该局部维数。态

$$
|\phi_\pm\rangle=(|1\rangle\pm|3\rangle)/\sqrt2
$$

有相同的 $X=Y=1/2,Z=\kappa=0$，但自伴可观测量 $C_{13}=|1\rangle\langle3|+|3\rangle\langle1|$ 的期望分别为 $\pm1$。$C_{13}$ 不是效果；效果可取 $(I+C_{13})/2$。可观测的相干由实际菜单决定，不能仅从对角联合概率中读出。

**定义 9.2（原生树的共同未来目标）。** 有序有限二叉树由叶 $\alpha,\beta$ 与分支 $\langle u,v\rangle$ 生成，替换为

$$
S\alpha=\beta,\qquad S\beta=\langle\beta,\alpha\rangle,
\qquad S\langle u,v\rangle=\langle Su,Sv\rangle.
$$

初始源为 $t=\langle\alpha,v\rangle$。地址由 $L,R$ 组成，读出为 $\alpha,\beta,\mathrm{branch},\mathrm{absent}$ 四值。目标取全部已提供计数 $k\in\mathbb N$ 下地址 $RL,RR$ 的回复。计数是实际给定输入，不由预测码免费取得。

这个特例直接使用 [《自适应取得参考前沿》§12，特别是 Theorems 12.3、12.6、12.7](RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md) 的原生响应分类，接入定义 4.1 的任意目标族。其共同源解释如下：$v$ 是叶时有 $\alpha,\beta$ 两类；$v$ 是分支时，每个孩子的根回复轨迹只有三类，分别从 $\alpha$、$\beta$、branch 开始，其后由替换固定。两个孩子可在同一个实际分支中任取这三类代表，得到九个共同实现。两种叶源的地址回复含初始缺席阶段，与九种分支源区别。于是联合类数为 $2+3\cdot3=11$，而各单地址类数是五；不能把两个分别达到的五相乘成二十五。孩子代表可取 $\alpha,\beta,\langle\alpha,\alpha\rangle$，因而当 $v$ 高度上界至少二时全部十一类已达到。

有限高度的源数也能与这项全未来证明区分。令 $b_h$ 为高度至多 $h$ 的 $v$ 数，则 $b_0=2$、$b_{h+1}=2+b_h^2$，所以 $b_1=6,b_2=38,b_3=1446$。这是全体初始树的计数，不是响应类数。上述分类来自替换轨迹与共同代表，对所有未来计数成立，不以枚举这两个有限集合代替证明，也不以原生十一类给量子端口定维。

**定义 9.3（量子未来的响应空间）。** 对任意指定有限协议菜单 $\mathcal Q$，取每个实际记录事件的效果 $E_{\pi,h}$，令

$$
\mathcal O_{\mathcal Q}=\operatorname{span}_{\mathbb R}\{I,E_{\pi,h}\}.
$$

密度态 $\rho,\sigma$ 对全部实际未来响应相同，当且仅当 $\operatorname{tr}((\rho-\sigma)E)=0$ 对每个 $E\in\mathcal O_{\mathcal Q}$ 成立。这是定义 4.1 的迹配对版本，不把效果的实线性组合当成额外可执行的效果。

对定义 1.4 的实际菜单，复用 [《实际等待读出下的近似单份量子边界》Theorem 2.1](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md) 的首读归约，便有

$$
\sup_{\pi\in\mathcal Q}\operatorname{TV}(P_\rho^\pi,P_\sigma^\pi)
=\sup_{t\geq0}\frac12\sum_s
|\operatorname{tr}(Q_s(t)(\rho-\sigma))|.
\tag{9.1}
$$

这里给出其在主定理中的实际记录含义。固定首读前的输入无关控制资料，同一生成元的等待合并为一个 $O(t)$。若之前就 Stop，两输入的记录律相同。否则首结果 $s$ 的支态为

$$
\Pi_sO(t)\rho O(t)^T\Pi_s=p_s\Pi_s.
$$

给定 $s$ 后，所有有限反馈、再次秩一读及 Stop 构成同一个概率核 $L_s(h)$，与原输入无关，且总质量为一。即使 $p_s=0$，也可从预定态 $\Pi_s$ 定义这个核，乘零即可，不使用零概率条件化。完整记录保留 $s$ 时，两个历史分布是 $p_sL_s(h)$ 与 $p'_sL_s(h)$，其 TV 恰为首分布 TV；遗忘记录是共同后处理，只能减小 TV。输入无关随机控制可先固定再积分，仍受右侧上确界控制。反向以等待 $t$、完整读并立即 Stop 实现任意右侧分布。这覆盖随机控制、Stop 与零概率分支。增添历史门数不必增加对同一个初态的可区分信息。

效果空间与导数证书亦直接引用 [《AURIC FIB 二阶关系完成》65.2–65.3](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)。其结论在当前实帧为

$$
\mathcal O_{\mathcal Q}=\operatorname{Sym}_5(\mathbb R),\qquad
\dim_{\mathbb R}\mathcal O_{\mathcal Q}=15.
\tag{9.2}
$$

引用的参数对应是 $\mathcal L(X)=XA-AX$、$Q_s^{(k)}(0)=\mathcal L^k(\Pi_s)$。非负等待效果的有限维实张成闭合，右差商及其极限仍在其中；这只是张成证明，不增加导数仪器。用上三角十五坐标，次数零至四的累计秩为 $5,9,12,14,15$。以零起编号 $5k+s$ 选列

$$
0,1,2,3,4,5,6,7,8,10,11,12,15,16,20
$$

的行列式为 $-72$。原来源用 $AX-XA$，本处每个 $k$ 次列多 $(-1)^k$；选列次数之和为二十，故行列式符号不变。这里只用既有精确证书，不另立一个有限秩结果。

写任意 Hermitian 密度态为 $\rho=S+iB$，其中 $S$ 实对称，$B$ 实反对称，则 (9.2) 给

$$
\rho\sim_{\mathcal Q}\sigma\quad\Longleftrightarrow\quad
\operatorname{Re}\rho=\operatorname{Re}\sigma.
$$

归一化使十五维线性空间中的恒等坐标固定，故响应有十四个可变实坐标；二十四维全态空间在满秩处留下十维局部盲纤维。单位向量 $\psi_\pm=(e_N\pm i e_2)/\sqrt2$ 正交，其密度矩阵实部却相同，故由 (9.1) 在全部实际有限协议下不可区分。

候选“删除虚部”说明这种商不等于物理压缩。复线性映射

$$
\mathscr R(X)=\frac{X+X^T}{2}
$$

正且保迹，在 Hermitian 上取实部，保留全部实对称效果概率。但在第 6 节的未归一 Choi 约定下

$$
C_{\mathscr R}=\frac{|\Gamma_d\rangle\langle\Gamma_d|+F_{\mathrm{swap}}}{2}.
$$

任意单位反对称向量 $\xi$ 与 $\Gamma_d$ 正交，且 $F_{\mathrm{swap}}\xi=-\xi$，故对应特征值为 $-1/2$。若输入 Bell 向量归一化，Choi 态相应特征值是 $-1/(2d)$，在五维为 $-1/10$。因此 $d\geq2$ 时它不是 CP，不能用作合法编码器。观察纤维上目标相同，只证明统计因子化，不证明有全态统一合法的量子删除操作。

## 10. 主定理的无扰动步骤：探针分量与端口

**定义 10.1（任意探针族与非正交分量）。** 设 $H$ 是正维有限维复 Hilbert 空间，$\{\psi_j\}_{j\in J}$ 是单位向量族，线性张成 $H$；$J$ 可以任意大。令 $P_j=|\psi_j\rangle\langle\psi_j|$，在 $J$ 上以 $\langle\psi_i,\psi_j\rangle\ne0$ 连边。对连通分量 $c$，令 $H_c$ 为该分量探针的线性张成，$P_c$ 为其正交投影。

用于双设置证明的无扰动机制已见 Mayer–Knill，arXiv:1805.04491v1，Theorem 1：张成且非正交图连通的纯态探针决定恒等通道。Koashi–Imoto 的不扰动分解提供更广的背景。以下把这一既有机制用于分量及端口合同，不把连通刚性归为新发现。

不同分量的任意探针正交，故 $H=\bigoplus_cH_c$。每个 $H_c$ 非零，所以分量数至多 $d=\dim H$，即使 $J$ 无限也是如此。每个分量可先选有限个探针张成 $H_c$，再为这些顶点选择有限条连接路径；路径顶点的有限并即给连通且张成的有限子族。因此无需缩小原探针族的量词。

设 CPTP $T:M(H)\to M(H)$ 对所有密度输入保持全部 $P_j$ 概率。在输入 $P_j$ 上，$\operatorname{tr}(P_jT(P_j))=1$；正性与迹一使 $T(P_j)=P_j$。取同一个 Stinespring 等距 $V:H\to H\otimes E$，纯输出给

$$
V\psi_j=\psi_j\otimes\eta_j,\qquad\|\eta_j\|=1.
$$

等距保内积，所以

$$
\langle\psi_i,\psi_j\rangle
=\langle\psi_i,\psi_j\rangle\langle\eta_i,\eta_j\rangle.
$$

非正交边使 $\eta_i=\eta_j$，沿有限路径传播得到每个分量一个单位向量 $\eta_c$。线性延拓给 $Vx=x\otimes\eta_c$ 于 $H_c$。于是全矩阵作用为

$$
T(X)=\sum_{c,d}\langle\eta_d,\eta_c\rangle P_cXP_d.
\tag{10.1}
$$

反过来，任意这样的单位向量族定义等距，因为不同 $H_c$ 正交；得到的通道保留每个探针概率。在任意 Kraus 表示 $T(X)=\sum_\mu C_\mu XC_\mu^\dagger$ 中，也可用其标准环境实现重复上面的论证，得到

$$
C_\mu|_{H_c}=\lambda_{\mu c}I_{H_c}.
\tag{10.2}
$$

这不是只对某个便利 Kraus 表示成立。特别地，只有一个分量时 (10.1) 就是恒等通道。零维空间没有密度输入，不属于这里的非空探针合同；其零矩阵代数应单独处理，不能用空探针的最大值定义端口维数。

现在在 $d$ 维版本的定义 1.5 下，保持全部探针概率的最小量子块维数为

$$
q_{\min}=\max_c\dim H_c.
\tag{10.3}
$$

下界：写编码分支 Kraus 为 $B_{fa}:H\to\mathbb C^q$，标记块解码 Kraus 为 $R_{fb}:\mathbb C^q\to H$。复合 Kraus $C_{fba}=R_{fb}B_{fa}$ 的秩不超过 $q$。由 (10.2)，它在 $H_c$ 上是标量恒等。保迹给 $\sum_{f,b,a}|\lambda_{fba,c}|^2=1$，所以每个 $c$ 至少有一个系数非零，该 Kraus 秩至少 $\dim H_c$。故 $q\geq\max_c\dim H_c$，有限标记数再大也不改变这个下界。

上界使用正交分量测量及共同固定解码。取 $q=\max_c\dim H_c$，给每个分量一个等距 $J_c:H_c\to\mathbb C^q$。把它延拓成部分等距 $U_c:H\to\mathbb C^q$，满足 $U_c^\dagger U_c=P_c$；令 $Q_c=U_cU_c^\dagger$。取 $\tau_c$ 为 $H_c$ 上任意固定密度态，并定义

$$
\begin{aligned}
\operatorname{Enc}(X)_c&=U_cXU_c^\dagger,\\
\operatorname{Dec}_c(Y)&=U_c^\dagger YU_c+
\operatorname{tr}((I_q-Q_c)Y)\tau_c.
\end{aligned}
\tag{10.4}
$$

编码完全正，且 $\sum_cP_c=I$ 使其保迹。解码的第二项是正效果测量再制备固定态，完全正；第一项的迹为 $\operatorname{tr}(Q_cY)$，第二项补上剩余迹，所以每个 $\operatorname{Dec}_c$ 在整个填充块 $M_q$ 上 CPTP。不能只给 $Q_c$ 支撑上的逆等距便宣称完成了解码器。编码输出落在 $Q_c$ 内，故复合为 $\sum_cP_cXP_c$，保持每个探针。分量数已证有限，因而这是允许的有限标记端口。该构造与 Bluhm–Rauber–Wolf Theorem 7.1 的分块压缩及填充思想相接。

(10.3) 的对象是一个共同源上的全输入概率保持通道。它不声称每个单独目标需要这么大的端口，也不声称响应空间的线性维数等于量子块维数。下面只使用五个探针，就把该机制接到定义 1.4 的两个实际设置。

## 11. 主定理的双设置证明与定量余量

证明定理 2.1 的核心从实际矩阵指数开始，而不把一个数值近似当作非零证明。记

$$
M=\frac23A,\qquad S_{12}=\sum_{k=0}^{12}\frac{M^k}{k!}.
$$

诱导最大行和范数为 $\|X\|_\infty=\max_i\sum_j|X_{ij}|$；它次乘，且对所给矩阵 $\|M\|_\infty=2$。矩阵指数级数绝对收敛，于是

$$
\begin{aligned}
\|e^M-S_{12}\|_\infty
&\leq\sum_{k=13}^{\infty}\frac{2^k}{k!}\\
&=\frac{2^{13}}{13!}\sum_{m=0}^{\infty}
\frac{2^m13!}{(13+m)!}\\
&\leq\frac{2^{13}}{13!}\sum_{m=0}^{\infty}(1/7)^m
=\frac76\frac{2^{13}}{13!}
<\frac{64}{6081075}.
\end{aligned}
\tag{11.1}
$$

不等式使用 $(14\cdots(13+m))\geq14^m$；$m=0$ 时空积为一。最后一个有理界也等于 $8\cdot2^{13}/13!$，所以严格性由 $7/6<8$ 直接得到，无需以未经控制的指数数值替代余项。每个矩阵元的误差不超过该行和范数。

有限多项式的 $N$ 行按定义 1.4 的次序恰为

$$
(S_{12})_{N,*}=\left(
\frac{107738440637}{248594813775},\quad
\frac{490347766}{1104865839},\quad
\frac{4899328858}{9207215325},\quad
\frac{490347766}{1104865839},\quad
-\frac{91371050044}{248594813775}
\right).
\tag{11.2}
$$

这些等式由 $M$ 的有理矩阵乘法与有限求和得到；例如可逐项用 $R_0=I$、$R_{k+1}=R_kM/(k+1)$ 写 $S_{12}=\sum_{k=0}^{12}R_k$，完全在有理数域中。上述每项绝对值大于 $367/1000$，且交叉相乘给

$$
\frac{367}{1000}-\frac{64}{6081075}>\frac9{25}.
$$

故对单位实向量

$$
v=O(2/3)^Te_N
$$

的全部五个坐标，都有

$$
|v_j|>\frac9{25},\qquad
\mu:=\min_j|v_j|^2>\frac{81}{625}>\frac18.
\tag{11.3}
$$

这把一个确切有限多项式与已证明的无穷级数尾界连接起来，证明的是实际 $O(2/3)$ 的坐标下界。

若 $T$ 对所有输入保留两个设置的全部概率，就保留 $\Pi_2,\Pi_3,\Pi_5,\Pi_{25}$ 及 $Q_N(2/3)=vv^\dagger$ 的概率。五个向量

$$
e_2,e_3,e_5,e_{25},v
$$

张成 $\mathbb C^5$，因为 $v_N\ne0$；其非正交图是含四条辐条的连通星形，因为另外四个 $v_j$ 也非零。第 10 节的 Mayer–Knill 无扰动步骤给 $T=\operatorname{id}_5$。再用 (10.3) 或复合 Kraus 秩界，得任何精确端口必须 $q\geq5$。$q=5$ 取恒等编码和解码，给精确可行性。

这里精确刚性只用了五个探针投影；加上 $I$，它们张成的实空间至多六维。即使使用两个完整 PVM 的全部十个投影，因为各自之和都为 $I$，总张成维数也至多九，小于 $\operatorname{Herm}_5$ 的二十五维。因此这不是状态层析。结论来自概率保持对全部输入同时成立与 CP 合法性，而非从有限探针数宣称取得全态读数。

为得到显式近似界，下面的推导对任意维数 $d\geq1$、任意复 Kraus 算子都成立。取单位 $v\in\mathbb C^d$，$\mu=\min_i|v_i|^2>0$。对任意复矩阵 $C$ 定义

$$
L_v(C)=\sum_{i=1}^d\bigl(\|Ce_i\|^2-|\langle e_i,Ce_i\rangle|^2\bigr)
+\|Cv\|^2-|\langle v,Cv\rangle|^2.
$$

写 $C=\operatorname{diag}(\lambda_i)+B$，$B$ 对角为零；置

$$
b=\|B\|_{\mathrm{HS}},\qquad
z=\|(I-vv^\dagger)Cv\|,\qquad
\alpha=\operatorname{tr}C/d.
$$

各基向量的正交泄漏平方和恰为 $b^2$，故 $L_v(C)=b^2+z^2$。对任意复数中心 $c$，到 $\mathbb Cv$ 的距离公式给

$$
\begin{aligned}
\|(I-vv^\dagger)\operatorname{diag}(\lambda_i)v\|^2
&=\min_{c\in\mathbb C}\sum_i|v_i|^2|\lambda_i-c|^2\\
&\geq\mu\min_{c\in\mathbb C}\sum_i|\lambda_i-c|^2
=\mu\sum_i|\lambda_i-\alpha|^2.
\end{aligned}
$$

另一方面，由三角不等式和 $\|Bv\|\leq\|B\|_{\mathrm{HS}}$，左侧开方不超过 $z+b$。所以

$$
\begin{aligned}
\|C-\alpha I\|_{\mathrm{HS}}^2
&=b^2+\sum_i|\lambda_i-\alpha|^2\\
&\leq b^2+\frac{(z+b)^2}{\mu}
\leq\left(1+\frac2\mu\right)(b^2+z^2).
\end{aligned}
$$

展开 Hilbert–Schmidt 平方得

$$
L_v(C)\geq\frac{\mu}{2+\mu}
\left(\|C\|_{\mathrm{HS}}^2-\frac{|\operatorname{tr}C|^2}{d}\right).
\tag{11.4}
$$

这里允许复对角、复非对角以及任意非正规矩阵，未假定实 Kraus、unital 性或协变性。

设 $T(X)=\sum_aC_aXC_a^\dagger$ 是通过 $q$ 维块和任意有限标记端口的复合通道。按第 10 节分解可取每个 $\operatorname{rank}C_a\leq q$，保迹给

$$
\sum_a\|C_a\|_{\mathrm{HS}}^2
=\operatorname{tr}\sum_aC_a^\dagger C_a=d.
$$

对秩 $r$ 的任意复矩阵，奇异值分解与 Cauchy–Schwarz 给

$$
|\operatorname{tr}C|
\leq\sum_{i=1}^r s_i(C)
\leq\sqrt r\,\|C\|_{\mathrm{HS}},
$$

故 $|\operatorname{tr}C_a|^2\leq q\|C_a\|_{\mathrm{HS}}^2$。这是标准秩—迹界；经向量化也是 Terhal–Horodecki Lemma 1 的 Schmidt 秩重叠界。将其用于 (11.4)，先求 Kraus 和、再使用 TP，可得

$$
\sum_aL_v(C_a)\geq\frac{\mu}{2+\mu}(d-q).
\tag{11.5}
$$

把此代数损失接回实际测量，需要 $d+1$ 个生存率测试：$d$ 个输入 $P_i=|e_i\rangle\langle e_i|$ 在基测量中检验结果 $i$，另一个输入 $P_v=vv^\dagger$ 在含该投影的实际设置中检验该结果。每项原始分布的指定事件概率都是一。保迹使

$$
\sum_aL_v(C_a)
=\sum_{i=1}^d\bigl(1-\operatorname{tr}(P_iT(P_i))\bigr)
+1-\operatorname{tr}(P_vT(P_v)).
$$

任一指定事件的概率损失不超过完整分布的 TV。若这两个设置上的全输入误差为 $e_{\mathrm{two}}(T)$，则上式不超过 $(d+1)e_{\mathrm{two}}(T)$，从而

$$
e_{\mathrm{two}}(T)\geq
\frac{\mu(d-q)}{(2+\mu)(d+1)}.
\tag{11.6}
$$

应用到五模式时，这一步用了六个输入—结果测试，与精确刚性所用五个张成探针是不同的计数。由 (11.3) 得 $\mu/(2+\mu)>1/17$。因此对 $q<5$，每个允许通道满足 $e_{\mathrm{two}}(T)>(5-q)/102$；对所有允许通道取下确界，只能保留

$$
\varepsilon_{\mathrm{two}}(q)\geq(5-q)/102.
$$

$q=5$ 的恒等通道给零，单独完成端点。这证明定理 2.1 的定量及精确端口结论。

**定义 11.1（全菜单比较与未定精确值）。** 令 $e_{\mathrm{all}}$ 把定义 1.5 的两设置最大值换成全部实际有限协议上确界，$\varepsilon_{\mathrm{all}}(q)=\inf_{T\in\mathfrak C_q}e_{\mathrm{all}}(T)$。既有 [《实际等待读出下的近似单份量子边界》Theorem 5.1](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md) 在同一个全复输入、同一个有限标记合同下给

$$
\frac{7(5-q)}{68}\leq\varepsilon_{\mathrm{all}}(q)
\leq\frac{5-q}{7}.
$$

因为 $e_{\mathrm{two}}(T)\leq e_{\mathrm{all}}(T)$，全菜单下界不能推出两设置下界；(11.4)–(11.6) 正是补上这一步。全菜单上界可给两设置的上界，但不证明最优性。$q<5$ 时两设置精确 minimax 值及最优通道在本文中未定；$1/102$ 不声称最优常数，也不表示一次实验能直接读出一个通道的最坏情形误差。这里的贡献是指定实际两个设置的解析余项、连通探针应用及显式统一下界，不作全球原创性断言。

## 12. 主定理的表示闭合：有限因果图与无限相容态

**定义 12.1（有限量子关系图）。** 图有有限个局部节点及有限维、方向明确的量子和经典端口，依赖关系为无环图。输入边界给共同密度态，允许不同输入端口纠缠；每个节点是局部 CP 仪器，全部记录结果求和后保迹。经典端口的值是实际记录，后继节点的选择可以依赖其因果前驱记录；量子端口不得复制成两个未声明输出。初始辅助态及随机资源按指定共同来源给出，终端效果或输出端口明确。全部结果集有限，全部分支有共同有限深度界。独立节点指作用于不同现有端口、且无记录依赖的节点。

这个图概念使用量子电路与因果量子网络的组合语义；Abramsky–Coecke 提供组合结构的先例，Chiribella–D'Ariano–Perinotti 的量子网络框架明确处理因果连接。这里采用的是有限确定因果图，不包含任意因果序叠加或无限输出协议。

证明定理 2.1 的有限表示结论如下。先固定输入无关的随机控制资料。从第 6 节协议出发，把有限反馈树展开；每个局部操作、实际记录和受控后继都有一个位置节点。不同记录的互斥分支是不同合法配置，节点位置与前驱关系给事件结构，有限性保证有限前驱。未选择分支可在图中作为条件关系存在，不能把其结果并入同一实际配置。输入态、局部 CP 映射和输出记录端口组成固定图；每个实际分支的收缩正是该分支仪器复合，故条件于该随机资料的记录联合概率与原协议相同。对输入无关资料按原分布积分，恢复随机策略的记录律；若随机资料的值域无限，这一步是图族的概率混合，不声称把该无限资料存入一个有限维经典端口。第 9 节的首读归约对这种混合仍成立。噪声可直接用 CP 节点，或用等距及弃置端口；反馈用实际经典记录控制。观察者及记忆作为图内端口保存，后来再作用的环境沿边留到后来节点。

相反，从定义 12.1 的图取任一拓扑排序。按序在相应端口执行局部仪器；已执行记录决定后继分支，每个节点的 CP 性保证含任意旁观辅助时的正性，结果求和的 TP 性保证概率逐层归一。终端即给一个合法有限协议。两个拓扑排序可由相邻独立节点交换连接；在不同端口上，即使其输入纠缠，也有

$$
(\Phi\otimes\operatorname{id})\circ(\operatorname{id}\otimes\Psi)
=\Phi\otimes\Psi
=(\operatorname{id}\otimes\Psi)\circ(\Phi\otimes\operatorname{id}).
$$

所以交换不改分支映射与联合概率。有共同记录依赖的节点不属于这种可交换对。它是第 3 节菱形条件在合法量子端口上的实现。参考边界上的全部记录效果由对偶映射按逆方向拉回，正是第 6 节公式。

每个位置的操作事件仍有正计数；若某系统局部门有逆，其复合可为系统恒等，图中的两次事件仍是两次。该双向表示保留实际记录、观察者支撑、因果连接、局部逆和参考边界概率，不把形式内部路径变成记录，也不把所有不相容设置拼成一个共同经典赋值。它依赖定义 1.3 的概率表示，不能从图固定性反推出 Born 律。至此定理 2.1 的有限表示及全部陈述均已证明。

**假设 12.2（无限系统的相容局部态）。** 设一列共享单位的有限维 $C^*$ 子代数

$$
\mathcal A_1\subseteq\mathcal A_2\subseteq\cdots
$$

位于同一个 $C^*$ 代数中，$\omega_n$ 为正归一线性泛函，且 $\omega_{n+1}|_{\mathcal A_n}=\omega_n$。令 $\mathcal A=\overline{\bigcup_n\mathcal A_n}^{\|\cdot\|}$。这些相容条件是无限表示的额外前提，不由任意边缘相同自动得到。

有限表示之外，可用标准连续延拓与 GNS 构造得到一个合法无限态，而不写不存在的无限等权历史向量。定义 $\omega$ 于代数并集为 $\omega(a)=\omega_n(a)$，其中 $a\in\mathcal A_n$；相容性使其良定义。正泛函的 Cauchy–Schwarz 及 $a^\dagger a\leq\|a\|^2I$ 给

$$
|\omega(a)|^2\leq\omega(a^\dagger a)\leq\|a\|^2.
$$

所以 $\omega$ 唯一连续延拓到 $\mathcal A$，仍归一。对正元 $b$，在并集中逼近 $b^{1/2}$，其平方范数极限及连续性保证 $\omega(b)\geq0$，故延拓是态。

令

$$
\mathcal N_\omega=\{a\in\mathcal A:\omega(a^\dagger a)=0\},\qquad
\langle[a],[b]\rangle=\omega(a^\dagger b).
$$

Cauchy–Schwarz 使该内积在商空间上良定义且正定。又因为

$$
\omega(a^\dagger b^\dagger b a)\leq\|b\|^2\omega(a^\dagger a),
$$

$\mathcal N_\omega$ 是左理想，左乘 $[a]\mapsto[ba]$ 良定义，且算子范数不超过 $\|b\|$。完成商内积空间得 $H_\omega$，左乘延拓给 $*$ 表示 $\pi_\omega$；$\Omega_\omega=[I]$ 为单位循环向量，满足

$$
\omega(a)=\langle\Omega_\omega,\pi_\omega(a)\Omega_\omega\rangle.
$$

这是 Gelfand–Naimark–Segal 表示，见 Fewster–Rejzner 的 GNS 叙述。有限历史向量不能直接令 $T=\infty$：非零常数系数的 $\sum_{k\geq0}|k\rangle\otimes\psi_k$ 范数平方是无穷；把系数全部置零又不是单位向量。GNS 由相容局部态构造表示，不假定这样的等权向量。若改用可平方求和权重，就得到另一项指定权重的构造，不能把它当作无条件的均匀极限。

## 13. 数学引文与结果的归属

**数学引文 13.1（经典及组合前提）。** Winskel，*Event Structures*，载 *Petri Nets: Applications and Relationships to Other Models of Concurrency*，LNCS 255，1987，pp. 325–392，提供事件结构、配置与域的先例；本卷第 3 节明确验证其所用有限前驱版本。[原文](https://www.cl.cam.ac.uk/~gw104/Winskel1987_Chapter_EventStructures.pdf)。Myhill–Nerode 的继续测试及最小状态原理见 Kozen，*Myhill–Nerode Relations*；第 4 节只把二值接受改成明确的多值输出及非法标记。[原文](https://www.cs.cornell.edu/~kozen/Papers/mn.pdf)。第 5 节集合赋值粘合、有限逆系统紧致性及线性核判据分别使用标准粘合、König 引理与秩—零化度论证；可与 Stacks Project 的 [sheaf 条件](https://stacks.math.columbia.edu/tag/006S) 及 [有限集合逆极限](https://stacks.math.columbia.edu/tag/086J) 比较，不将标准工具另立为新结果。原生树的同源十一类归 [《自适应取得参考前沿》§12](RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md)，不是本卷新增的分类。

**数学引文 13.2（概率、仪器及相干）。** Busch，*Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem*，Phys. Rev. Lett. 91, 120403，2003，DOI [10.1103/PhysRevLett.91.120403](https://doi.org/10.1103/PhysRevLett.91.120403)，[arXiv:quant-ph/9909073v3](https://arxiv.org/abs/quant-ph/9909073v3)，支持第 6 节的全部效果概率表示，不支持从静态性推导该假设。Watrous，*The Theory of Quantum Information*，2018，Theorems 2.22、2.26 及 Corollary 2.27，支持完全正、Choi、Kraus 与等距表示的等价及保迹条件；[作者版](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。Abramsky–Coecke，*A Categorical Semantics of Quantum Protocols*，[arXiv:quant-ph/0402130](https://arxiv.org/abs/quant-ph/0402130)，以及 Chiribella–D'Ariano–Perinotti，*Theoretical Framework for Quantum Networks*，[arXiv:0904.4483](https://arxiv.org/abs/0904.4483)，提供第 7、12 节组合语义与因果端口的背景，本文的概率等式逐节点证明。有限传播核采用标准 history-state 方法，参见 Aharonov 等，*Adiabatic Quantum Computation Is Equivalent to Standard Quantum Computation*，[arXiv:quant-ph/0405098](https://arxiv.org/abs/quant-ph/0405098)；第 7 节给出了实际使用的差分算子和归一化。Wootters–Zurek 的不可克隆论证，DOI [10.1038/299802a0](https://doi.org/10.1038/299802a0)，以及 Englert 的 which-way 干涉分析，DOI [10.1103/PhysRevLett.77.2154](https://doi.org/10.1103/PhysRevLett.77.2154)，分别提供对应中间步骤的先例。

**数学引文 13.3（共同实现与恢复）。** CHSH 的经典共同分布界见 Clauser–Horne–Shimony–Holt，DOI [10.1103/PhysRevLett.23.880](https://doi.org/10.1103/PhysRevLett.23.880)；量子设置与共同经典赋值的区别也见 Abramsky–Brandenburger，*The Sheaf-Theoretic Structure of Non-Locality and Contextuality*，[arXiv:1102.0264](https://arxiv.org/abs/1102.0264)。第 8 节并未将效果非语境性等同于一个预定答案的隐变量模型。Knill–Laflamme，*Theory of Quantum Error-Correcting Codes*，[arXiv:quant-ph/9604034](https://arxiv.org/abs/quant-ph/9604034)，与 Schumacher–Nielsen，*Quantum Data Processing and Error Correction*，[arXiv:quant-ph/9604022](https://arxiv.org/abs/quant-ph/9604022)，是全逻辑空间恢复及环境信息条件的标准来源；本卷给出其有限维互补接口证明。Fewster–Rejzner，*Algebraic Quantum Field Theory — an Introduction*，[arXiv:1904.04051v2](https://arxiv.org/abs/1904.04051v2)，提供第 12 节的 $C^*$ 态与 GNS 表示背景，不把无限向量归一化问题转嫁给有限历史公式。

**数学引文 13.4（端口维数与双设置应用）。** Mayer–Knill，*Quantum Process Fidelity Bounds from Sets of Input States*，[arXiv:1805.04491v1](https://arxiv.org/abs/1805.04491v1)，Theorem 1 已证明张成且非正交图连通的纯态族识别酉过程；以目标恒等即给第 10 节使用的刚性。Koashi–Imoto，*What Is Possible Without Disturbing Partially Known Quantum States?*，[arXiv:quant-ph/0101144v2](https://arxiv.org/abs/quant-ph/0101144v2)，特别是有限维支撑及任意指标态族的设定、§V 的不扰动分解，给其一般结构背景。Bluhm–Rauber–Wolf，*Quantum Compression Relative to a Set of Measurements*，[arXiv:1708.04898v4](https://arxiv.org/abs/1708.04898v4)，Definition 4.1 给共同编解码合同，Theorem 5.1 给紧效果族压缩维数的小误差稳定性，Theorem 7.1 给分块上界；这些结论不直接提供本五模式两个设置的常数 $1/102$。Terhal–Horodecki，*A Schmidt Number for Density Matrices*，[arXiv:quant-ph/9911117v4](https://arxiv.org/abs/quant-ph/9911117v4)，Lemma 1 的秩约束最大纠缠重叠界与第 11 节的秩—迹步骤相对应。

十五维行走效果、导数秩列及行列式、以及三类菜单的既有精确量子成本，归 [《AURIC FIB 二阶关系完成》§§65、79](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)。首读归约与全菜单误差区间归 [《实际等待读出下的近似单份量子边界》Theorems 2.1、5.1](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md)。本卷在这些前提上给出第 11 节两个指定设置的解析应用及定量推导；它没有重复认领这些已有结果，也没有断言两设置的最优常数。事件计数、原生响应十一类、量子块维五分别属于不同的目标与操作关系；十维观察盲方向及不可区分正交态对，与全输入概率保持通道只能为恒等同时成立。

## 追加锚（本行以下为增补区）

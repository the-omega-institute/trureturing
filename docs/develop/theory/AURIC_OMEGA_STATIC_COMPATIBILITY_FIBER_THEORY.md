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

## 14. 续篇Ⅲ：原生实现图的拓扑代价

**定义 34.1（实际响应支撑多重图）。** 固定一个确定性有限控制器及一族必须正确处理、每次均有限终止的实际来源。每个运行状态安装一个固定查询和一个回复转移表，每个终止状态安装一个固定完整输出。将这些运行中实际访问的状态及实际使用的有向后继关系合并为 $G=(V,E)$。同一有序状态对只计一次，不因两个回复通向同一后继而重复计边；两个反向有序对则分别保留。忘掉方向后取无向多重图，保留反向弧造成的平行边及任何自环。记

$$
m=\#\{\text{支撑中的运行状态}\},\quad
n=\#\{\text{支撑中的终止状态}\},\quad
c=\#\{\text{无向连通分量}\},\quad
\beta=|E|-|V|+c.
$$

$\beta$ 是这个多重图的环空间维数。假设每个运行状态在所选来源上至多有两个不同实际后继，终止状态没有查询后继。令 $\Delta=2m-|E|\geq0$，并令 $u$ 为已安装而不在支撑中的状态数，总安装数为 $K=m+n+u$。这里的二分性只约束实际来源上的后继，不把具有 $\alpha,\beta,\mathsf{branch},\mathsf{absent}$ 四种回复的整个原生接口改成二值接口。

**命题 34（重复伙伴控制器的支撑成本）。** 上述计数满足

$$
K=2n-c+\beta+\Delta+u.
\tag{34.1}
$$

若至少有 $N$ 种必需完整输出，实际入口状态至多 $r$ 种，每次至多 $k$ 次查询，则

$$
K\geq\max\{N,2N-r\},\qquad N\leq r2^k.
\tag{34.2}
$$

在原生重复伙伴模型的两张具体达到上界的表上，三次查询表的额外一个状态，对应支撑的一个额外无向环维数。

**证明。** 由 $|V|=m+n$、$|E|=2m-\Delta$ 得 $\beta=m-n+c-\Delta$，即 (34.1)。不同完整输出需要不同终止状态，故 $n\geq N$。每个支撑分量包含至少一个实际入口，故 $c\leq r$；其余各缺额非负，得到状态下界。从每个入口展开深度至多 $k$ 的二分回复树，至多有 $2^k$ 个叶；合流及不同来源路径之并中的环不增加这棵展开树的叶数，得到输出容量界。这些是图的 Euler 计数及二分树容量的中间工具。

具体应用取 [《原生出生溯源》Proposition 11.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md) 的六个同时固定的实际来源

$$
Z=\{0_a,0_c,1,2,3,4\},\qquad
G_a=\{0_a,1,2\},\quad G_c=\{0_c,3,4\}.
$$

前两个要求同一个完整输出 $R_0$，其余要求两两不同的 $R_1,\ldots,R_4$。这些 $R_j$ 包含全部修复行、受限分区、规范名字、等异关系及缺席守卫，不是等待一个免费解码器的标签。取实际地址

$$
p_a=LLL,\quad p_1=LLR,\quad p_2=LRR,\quad p_3=RLR,\quad p_4=RRR.
$$

在六来源上，$p_a$ 的回复在 $G_a$ 为 $\beta$、在 $G_c$ 为 $\mathsf{branch}$；$p_j$ 只在来源 $j$ 回复 $\alpha$，否则为 $\mathsf{branch}$。任意其他有限原生地址在这六个来源上只能给常量、这个组分离或一个正指标的单点分离；该事实由上述 Proposition 11.3 对全部地址及其后缀的原生构造供应。

三次查询表从 $q_0$ 开始，安装如下完整转移；$H_j$ 输出 $R_j$。

| 状态 | 地址 | 回复条件 | 后继 |
| --- | --- | --- | --- |
| $q_0$ | $p_a$ | $\beta$ | $q_1$ |
| $q_0$ | $p_a$ | $\mathsf{branch}$ | $q_3$ |
| $q_0$ | $p_a$ | $\alpha$ 或 $\mathsf{absent}$ | $H_0$ |
| $q_1$ | $p_1$ | $\alpha$ / 非 $\alpha$ | $H_1$ / $q_2$ |
| $q_2$ | $p_2$ | $\alpha$ / 非 $\alpha$ | $H_2$ / $H_0$ |
| $q_3$ | $p_3$ | $\alpha$ / 非 $\alpha$ | $H_3$ / $q_4$ |
| $q_4$ | $p_4$ | $\alpha$ / 非 $\alpha$ | $H_4$ / $H_0$ |

六来源上 $q_0\to H_0$ 不发生。因此实际边恰为

$$
\begin{gathered}
q_0\to q_1,\ q_0\to q_3,\ q_1\to H_1,\ q_1\to q_2,\quad
q_2\to H_2,\ q_2\to H_0,\\
q_3\to H_3,\ q_3\to q_4,\ q_4\to H_4,\ q_4\to H_0.
\end{gathered}
$$

四次查询表从 $s_1$ 开始，$s_j$ 查询 $p_j$，$\alpha$ 后继为 $H_j$，非 $\alpha$ 后继为 $s_{j+1}$（$j<4$）或 $H_0$（$j=4$）。它的八条实际边就是这四对后继。直接逐来源跟随表可得

| 表 | $m$ | $n$ | $\#E$ | $c$ | $\beta$ | $\Delta$ | $u$ | $K$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 三次查询 | 5 | 5 | 10 | 1 | 1 | 0 | 0 | 10 |
| 四次查询 | 4 | 5 | 8 | 1 | 0 | 0 | 0 | 9 |

故 $10=2\cdot5-1+1$、$9=2\cdot5-1$。三次表的两条零输出路径在 $H_0$ 合流，形成无向环；这不表示任何一次实际运行绕时间成环。

两张表在整个原生来源纤维上均正确，由原生条目的 Proposition 11.5 供应；其 Theorem 11.4 的异常下界另用原生查询几何：三次深度的首查询必须分离 $G_a,G_c$，否则常量或单点分离会留下至少三个输出而只余一次查询；随后两组分别必须访问 $b_1,b_2$ 与 $b_3,b_4$ 的不同地址锥。故至少有五个运行状态和五个终止状态。一般二分下界 (34.2) 本身只给九，不能替代这个十状态障碍。

在入口编码与控制器**联合选择**、$r\geq1,k\geq0$ 的完整入口合同下，原生条目的 Theorem 11.6 已给

$$
K_{\min}(r,k)=
\begin{cases}
+\infty,&r2^k<5,\\
10,&(r,k)=(1,3),\\
\max\{5,10-r\},&r2^k\geq5,\ (r,k)\ne(1,3).
\end{cases}
\tag{34.3}
$$

本命题提供两张实现图的拓扑分解，不将 (34.3) 另认作新的分类。$\square$

## 15. 续篇Ⅲ：两个固定读出的五模式有理谱证书

**定义 35.1（两基底重叠图）。** 在 $\mathbb C^d$、$d\geq2$ 上取两个正交归一基底 $\mathcal E=(e_i)$、$\mathcal V=(v_j)$，令

$$
P_i=e_ie_i^\dagger,\quad Q_j=v_jv_j^\dagger,\quad
B_{ij}=|\langle e_i,v_j\rangle|^2,\quad
J=\frac1d\mathbf1\mathbf1^{\mathsf T},\quad
\kappa=\|B-J\|_{2\to2},\quad\gamma=1-\kappa.
$$

$B$ 双随机，未假定对称。定义 Hilbert–Schmidt 正交投影及联合偏离算子

$$
\mathcal P(X)=\sum_i\operatorname{tr}(P_iX)P_i,\quad
\mathcal Q(X)=\sum_j\operatorname{tr}(Q_jX)Q_j,\quad
\mathcal L=2\operatorname{Id}-\mathcal P-\mathcal Q.
$$

重叠图只描述两个测试基底之间的关系，不把量子演化替换成经典概率转移。

**定义 36.1（全输入共同端口）。** 令 $1\leq q\leq d$ 为整数，$F$ 为任意非空有限经典标签集。一个端口由在后来选择测量设置前就固定的 CPTP 映射组成：

$$
\operatorname{Enc}:M_d\longrightarrow\bigoplus_{f\in F}M_q,
\qquad
\operatorname{Dec}:\bigoplus_{f\in F}M_q\longrightarrow M_d,
\qquad T=\operatorname{Dec}\circ\operatorname{Enc}.
$$

全部输入为复密度矩阵；不保留输入副本、参考纠缠或任何未计入的量子旁路。经典标签的分布可以依赖输入。令

$$
\begin{aligned}
p_{\mathcal E}(\rho)&=(\operatorname{tr}(P_i\rho))_i,
&p_{\mathcal V}(\rho)&=(\operatorname{tr}(Q_j\rho))_j,\\
\operatorname{TV}(p,p')&=\tfrac12\sum_i|p_i-p'_i|,
&e_{\mathcal E,\mathcal V}(T)&=\sup_\rho\max_{\mathcal B\in\{\mathcal E,\mathcal V\}}
\operatorname{TV}(p_{\mathcal B}(\rho),p_{\mathcal B}(T(\rho))).
\end{aligned}
$$

$\varepsilon_{\mathcal E,\mathcal V}(q)$ 是对全部这种共同端口及任意有限 $F$ 的误差下确界。这是第 1、10 节所用的 Bluhm–Rauber–Wolf Definition 4.1 合同。五模式记号 $\varepsilon_{0,t}$ 指设置 $0,t$，对应 $v_j(t)=O(t)^{\mathsf T}e_j$，故 $B_{ij}(t)=O_{ji}(t)^2$。

**命题 37（五模式的两个固定设置）。** 对定义 1.4 的同一个 $A,K,D$ 及实际等待—模式读出，成立

$$
\kappa(2/3)<\frac23,\qquad \kappa(1)<\frac{23}{50}.
\tag{37.1}
$$

因此对 $1\leq q\leq5$，

$$
\varepsilon_{0,2/3}(q)\geq\frac{5-q}{30},\qquad
\varepsilon_{0,1}(q)\geq\frac{27(5-q)}{500}\geq\frac{5-q}{20}.
\tag{37.2}
$$

**证明。** 先将已有的谱过程验证方法接到共同端口，再给出这两个实际设置的有限证书。一般过程验证的归属是 Zhu–Zhang，*Efficient Verification of Quantum Gates with Local Operations*，[arXiv:1910.14032v2](https://arxiv.org/html/1910.14032v2)，式 (7)、(9)、(28)–(31) 及 Proposition 3；这里只使用单通道的谱不等式，不使用重复试验的样本量结论。

**两投影的中间谱计算（35）。** 令

$$
V(a,b)=\sum_i a_iP_i+\sum_jb_jQ_j.
$$

其 Gram 矩阵及另一乘积为

$$
V^\dagger V=\begin{pmatrix}I&B\\B^{\mathsf T}&I\end{pmatrix},
\qquad VV^\dagger=\mathcal P+\mathcal Q.
$$

设 $B$ 的奇异值为 $1=s_1\geq s_2\geq\cdots\geq s_d$。双随机性将常数方向与其正交补分开，给 $s_2=\|B-J\|=\kappa$。上述 Gram 矩阵的特征值为 $1\pm s_j$。去掉矩阵空间的标量恒等方向后，$\mathcal P+\mathcal Q$ 的最大特征值至多 $1+\kappa$。因此对任意复矩阵 $C$，

$$
\langle C,\mathcal L(C)\rangle_{\mathrm{HS}}
\geq\gamma\left(\|C\|_{\mathrm{HS}}^2-
\frac{|\operatorname{tr}C|^2}{d}\right).
\tag{35.1}
$$

这里将 $C=(\operatorname{tr}C/d)I+C_0$、$\operatorname{tr}C_0=0$ 代入即可。$\gamma>0$ 时，$\mathcal L(C)=0$ 当且仅当 $C\in\mathbb CI$。同时二分图归一化拉普拉斯

$$
L_G=I_{2d}-\begin{pmatrix}0&B\\B^{\mathsf T}&0\end{pmatrix}
$$

的谱为 $1\pm s_j$，第二小值恰为 $\gamma$；它不是绝对混合谱隙，二分性仍给邻接特征值 $-1$。

**共同端口的中间容量估计（36）。** 必须选取与编码—解码分解相适配的 Kraus 表示：编码的第 $f$ 块算子为 $E_{f\alpha}:\mathbb C^d\to\mathbb C^q$，解码在该块上的算子为 $D_{f\beta}:\mathbb C^q\to\mathbb C^d$，于是可取

$$
C_{f\beta\alpha}=D_{f\beta}E_{f\alpha},\qquad
T(X)=\sum_aC_aXC_a^\dagger,\qquad\operatorname{rank}C_a\leq q.
$$

这是存在这种表示，不是断言任意 Kraus 表示都逐项满足该秩界。TP 与奇异值的 Cauchy–Schwarz 界给

$$
\sum_a\|C_a\|_{\mathrm{HS}}^2=d,\qquad
|\operatorname{tr}C_a|^2\leq q\|C_a\|_{\mathrm{HS}}^2.
$$

将 (35.1) 求和，得 $\sum_a\langle C_a,\mathcal L(C_a)\rangle\geq\gamma(d-q)$。另一方面，输入 $P_i$ 在基底 $\mathcal E$ 中的原分布集中于 $i$，其 TV 损失为 $1-\operatorname{tr}(P_iT(P_i))$；$Q_j$ 也一样。这 $2d$ 项之和恰为上述 Kraus 和，每项不超过 $e_{\mathcal E,\mathcal V}(T)$。所以

$$
e_{\mathcal E,\mathcal V}(T)\geq\frac\gamma2\left(1-\frac qd\right),
\qquad
\varepsilon_{\mathcal E,\mathcal V}(q)\geq\frac{\gamma(d-q)}{2d}.
\tag{36.1}
$$

无须秩约束时，同一求和给出纠缠保真度的中间结论：

$$
F_{\mathrm e}(T)=\frac1{d^2}\sum_a|\operatorname{tr}C_a|^2
\geq1-\frac{2e_{\mathcal E,\mathcal V}(T)}\gamma,
\qquad\gamma>0.
\tag{36.2}
$$

为明确与文献的参数对应，置 $|\Phi_d\rangle=d^{-1/2}\sum_i e_i\otimes e_i$、$\chi_T=(T\otimes\operatorname{id})(|\Phi_d\rangle\langle\Phi_d|)$。平衡探针族取两个完整基底、每个探针权重 $1/(2d)$，验证算子为

$$
\Theta=\tfrac12\sum_i P_i\otimes\overline{P_i}
+\tfrac12\sum_j Q_j\otimes\overline{Q_j}.
$$

向量化后它对应 $(\mathcal P+\mathcal Q)/2$，故过程验证谱隙为 $\nu=\gamma/2$。平均通过率为 $p_{\mathrm{pass}}=\operatorname{tr}(\Theta\chi_T)$，满足

$$
1-p_{\mathrm{pass}}\leq e_{\mathcal E,\mathcal V}(T),\qquad
1-p_{\mathrm{pass}}\geq\frac\gamma2(1-F_{\mathrm e}(T)).
$$

适配 Kraus 的秩—迹界给 $F_{\mathrm e}(T)\leq q/d$，与 (36.1) 一致；该秩—重叠步骤也是第 13.4 条所引 Terhal–Horodecki 的标准供应。若 $\gamma>0$ 且误差为零，(35.1) 迫使每个 $C_a$ 为标量恒等，TP 随即给 $T=\operatorname{id}$，而适配秩界要求 $q\geq d$。$q=d$ 的恒等端口可行。若另考虑 $q>d$，等距嵌入及全块 CPTP 补全也给误差零；(37.2) 的系数比较只在 $q\leq5$ 使用。

**五模式的有限有理数据。** 取 $M=10^6$，

$$
T_0=I,\qquad T_k=T_{k-1}\frac{tA}{k},\qquad
S_{16}(t)=\sum_{k=0}^{16}T_k,\qquad
(N_t)_{ij}=\left\lfloor M(S_{16}(t)_{ji})^2+\frac12\right\rfloor,
\qquad\widehat B_t=N_t/M.
$$

精确矩阵为

$$
N_{2/3}=\begin{pmatrix}
187827&196965&283150&196965&135093\\
196965&390384&33773&140770&238108\\
283150&33773&641505&33773&7799\\
196965&140770&33773&390384&238108\\
135093&238108&7799&238108&380892
\end{pmatrix},
\tag{37.3}
$$

$$
N_1=\begin{pmatrix}
1151&114763&356813&114763&412509\\
114763&103985&103127&459052&219073\\
356813&103127&370073&103127&66859\\
114763&459052&103127&103985&219073\\
412509&219073&66859&219073&82485
\end{pmatrix}.
\tag{37.4}
$$

这些数可由给定有限递推及整数取整直接取得；相应逐项平方的最大舍入误差分别为

$$
\frac{11325031748188407259082663713}{24175165004592575654470874584500000}
<\frac1{2M},\qquad
\frac{4267827042099853319}{8933941565252960256000000}<\frac1{2M}.
$$

对称性有代数依据：$R=\operatorname{diag}(1,-1,-1,-1,1)$ 满足 $RAR=-A$，故

$$
O(t)^{\mathsf T}=RO(t)R,\qquad S_{16}(t)^{\mathsf T}=RS_{16}(t)R.
$$

逐项平方后对称，转置约定不改变 (37.3)–(37.4)。舍入矩阵不必恰好双随机，不对其行和作额外调整。

因为 $\|tA\|_\infty=3t$，指数级数余项满足

$$
\|e^{tA}-S_{16}(t)\|_\infty
\leq e^{3t}\frac{(3t)^{17}}{17!}.
$$

这里使用的两个严格指数界也有有限证明：对 $x=2,n=8$ 或 $x=3,n=10$，相邻尾项比至多 $x/(n+2)$，所以

$$
e^x\leq\sum_{k=0}^n\frac{x^k}{k!}
+\frac{x^{n+1}}{(n+1)!}\frac1{1-x/(n+2)}
<\begin{cases}8,&x=2,\\21,&x=3.\end{cases}
$$

分别取 $r_{2/3}=8\cdot2^{17}/17!$、$r_1=21\cdot3^{17}/17!$。真实正交矩阵的每项绝对值至多一，平方误差至多 $r_t(2+r_t)$；再用五阶矩阵的算子范数至多五倍最大项，得

$$
\|B(t)-\widehat B_t\|_{2\to2}
\leq5\left[r_t(2+r_t)+\frac1{2M}\right]
=\begin{cases}
\displaystyle\frac{7629716855893073}{3016317999495200400000}<\frac1{300000},&t=2/3,\\[2mm]
\displaystyle\frac{76514051204692193}{971663500692684800000}<\frac1{10000},&t=1.
\end{cases}
\tag{37.5}
$$

最后给正定性的整数见证。取 $a_{2/3}=133/200$、$a_1=459/1000$，定义

$$
H_t^\pm=Ma_tI\pm(N_t-200000\,\mathbf1\mathbf1^{\mathsf T}).
$$

下表列出它们前 $k$ 行前 $k$ 列的行列式；$a_tI\pm(\widehat B_t-J)$ 的对应顺序主子式等于表项除以 $M^k$。

| $k$ | $\det H_{2/3,k}^{-}$ | $\det H_{2/3,k}^{+}$ |
| ---: | ---: | ---: |
| 1 | 677173 | 652827 |
| 2 | 321387929343 | 558408559343 |
| 3 | 49751990304680768 | 594013168341089232 |
| 4 | 16411661841695975006436 | 488104509828941036526436 |
| 5 | 208640257571412315299700000 | 394535509521969771531499700000 |

| $k$ | $\det H_{1,k}^{-}$ | $\det H_{1,k}^{+}$ |
| ---: | ---: | ---: |
| 1 | 657849 | 260151 |
| 2 | 357850716566 | 87165564566 |
| 3 | 80981574159315600 | 46055892924212400 |
| 4 | 22184403590390660474994 | 8071279133964492722994 |
| 5 | 10424751290747821345552650004 | 196968557936749209747821996 |

全部为正；归一化后的十个主子式在 $t=2/3$ 均大于 $1/5000$，在 $t=1$ 均大于 $1/6000$。Sylvester 判据给两符号矩阵正定，故 $\|\widehat B_t-J\|<a_t$。结合 (37.5)，

$$
\kappa(2/3)<\frac{133}{200}+\frac1{300000}<\frac23,
\qquad
\kappa(1)<\frac{459}{1000}+\frac1{10000}<\frac{23}{50}.
$$

将 $\gamma(2/3)>1/3$、$\gamma(1)>27/50$ 代入 (36.1) 即得 (37.2)。对单个压缩端口的严格界，取下确界后只保留非严格下界；$q=5$ 由恒等端口单独给零。$\square$

**命题 37.1（设置、全菜单与统计估计的比较）。** 同一组 $0,2/3$ 设置的下界由第 11 节的 $(5-q)/102$ 提升为 $(5-q)/30$，常数比为 $102/30=17/5$。没有增加读口。设置 $0,1$ 也是定义 1.4 中已经允许的固定等待与模式读出。对 $1\leq q\leq5$，仍有

$$
\varepsilon_{0,t}(q)\leq\varepsilon_{\mathrm{all}}(q),\qquad
\varepsilon_{\mathrm{all}}(q)\geq\frac{7(5-q)}{68}.
$$

**证明。** 两设置是实际全菜单的子族，逐通道的误差上确界有此顺序，再取同一个端口类的下确界即可。全菜单下界由第 11.1 条所引原结果供应，不能沿相反方向推出两设置下界。$q=4$ 时，三个两设置下界分别为 $1/102$、$1/30$、$1/20$（最后取保守常数），均是全输入最坏情形的分布误差；它们不等于有限样本中的经验频率误差，也不提供单次测量的概率读数。$q<5$ 的精确 minimax 值及常数最优性未由这些不等式确定。$\square$

## 16. 续篇Ⅲ：固定容差、盲纤维与统一操作

**命题 38（共同固定参数的校准区间）。** 第二设置取同一个固定实际参数 $t$，若 $|t-1|\leq1/200$，则

$$
\kappa(t)<\frac12,\qquad
\varepsilon_{0,t}(q)\geq\frac{5-q}{20}\quad(1\leq q\leq5).
$$

**证明。** 对 $O(t),O(s)$ 的任一行，Cauchy–Schwarz 给

$$
\sum_j|O_{ij}(t)^2-O_{ij}(s)^2|
\leq\Bigl(\sum_j|O_{ij}(t)-O_{ij}(s)|^2\Bigr)^{1/2}
\Bigl(\sum_j|O_{ij}(t)+O_{ij}(s)|^2\Bigr)^{1/2}
\leq2\|O(t)-O(s)\|_{2\to2}.
$$

列有同样的界，由 $\|M\|_2\leq\sqrt{\|M\|_1\|M\|_\infty}$ 得

$$
\|B(t)-B(s)\|_{2\to2}\leq2\|O(t)-O(s)\|_{2\to2}
\leq2\|A\|_{2\to2}|t-s|.
$$

最后一步使用 $O(t)-O(s)=\int_s^t AO(u)\,du$ 及正交性。$A=-iD^\dagger KD$ 的谱范数为

$$
\|A\|_{2\to2}=\sqrt{\frac{5+\sqrt{17}}2}<\frac94.
$$

于是 $\kappa(t)\leq\kappa(1)+2\|A\||t-1|<23/50+9/400=193/400<1/2$，再用 (36.1)。条件是全族输入使用共同固定的 $t$；未记录的逐次随机时间抖动形成混合 POVM，须另行定义误差模型，不能由本命题代入一个平均时间处理。$\square$

**命题 39（五模式盲纤维与不可压缩性并存）。** 对 $\gamma>0$ 的两基底，效果的实线性张成维数为 $2d-1$，迹一仿射空间中的读出秩为 $2d-2$，线性盲核维数为 $(d-1)^2$。通过任一满秩密度矩阵的局部读出纤维具有这个维数。尽管如此，全输入精确保留两个设置的同一个 CPTP 通道只能为恒等。对命题 37、38 的五模式设置，这些数分别为

$$
9,\qquad8,\qquad16,\qquad q_{\min}=5.
$$

**证明。** 两个 Hermitian 对角子空间各有实维数 $d$。交中的 $X$ 满足 $\mathcal L(X)=0$，由 (35.1) 只有实标量恒等，故和的维数为 $2d-1$。$I$ 在效果空间中，正交盲核自动无迹，其维数为 $d^2-(2d-1)=(d-1)^2$。限制到迹一超平面后读出秩减一。

若 $\rho$ 满秩，对任意盲方向 $\Delta=\Delta^\dagger$，在 $\|\Delta\|_{\mathrm{op}}<\lambda_{\min}(\rho)$ 的小邻域内 $\rho+\Delta$ 仍正定，因而局部纤维是整个盲核的开邻域。特别地，对非零盲方向取 $0<\eta<1/(d\|\Delta\|_{\mathrm{op}})$，$I/d\pm\eta\Delta$ 是两个读出完全相同的不同密度矩阵。正半定边界处的纤维可以缩小，不宣称每条密度纤维都有这个维数。

统一通道的刚性则由 (36.1) 的零误差论证给出。两个量词分别是 $\exists\rho\ne\sigma:R(\rho)=R(\sigma)$ 与 $\forall\rho:R(T(\rho))=R(\rho)$，后者还要求一个全域 CP 操作，故前者不供应合法的纤维收缩。无扰动刚性的一般先例已在第 13.4 条归给 Mayer–Knill 及 Koashi–Imoto；这里的应用把指定两设置的九维效果空间、十六维盲核与维五端口放在同一合同中。$\square$

**命题 39.1（三种不同的关系量）。** 历史长度、目标响应商的类别数与实现容量不能相互替代。

**证明。** 只有在 $g^{-1}$ 确为当前接口可用且可续接的动作时，历史 $hgg^{-1}$ 才给出实际例子：复合系统作用等于 $h$，而 $\tau(hgg^{-1})=\tau(h)+2$。在形式群胚中也可写该式，但它不为非负等待菜单增加一个逆门。原生五类完整修复输出与前篇十一类联合未来回复属于各自目标的响应商；(34.1) 另需实际图的连接及分支数据。量子两设置只有八个独立概率坐标，却要求维五精确端口，由命题 39 已证。因此这些量对应不同对象、目标与操作合同，没有从一个数推出另一个数的统一等式。$\square$

## 17. 续篇Ⅳ：历史相对的门与可取得的选择信息

**定义 40.1（信息纤维与动作）。** 固定母结构 $\Omega$ 中的完整配置集为 $X$，配置包含相关量子端口、控制器、实际记录和资源条件，不是给不相容测量预填答案的经典表。令 $r:X\to M$，并取 $M=r(X)$，只在实际可达到的记录上定义选择器。置

$$
\mathcal F_m=r^{-1}(m),\qquad
\operatorname{Adm}(x)\subseteq\mathcal A,\qquad
\mathcal A_{\mathrm{safe}}(m)=\bigcap_{x\in\mathcal F_m}\operatorname{Adm}(x).
$$

动作合法性同时包含类型、已安装接口、资源及所声明约束。一次原生查询的 $\mathsf{absent}$ 可以是合法且被计数的回复，不等于调用非法或未发生。以下取有限 $M,\mathcal A$；若要把选择器延拓到未达到的记录，还须 $\mathcal A\ne\varnothing$ 并在那些记录指定任意默认动作。

**中间选择判据（40）。** 在命题 43 的约束控制应用中，确定性记录选择器 $\pi:M\to\mathcal A$ 全域零失误合法，当且仅当每个 $\mathcal A_{\mathrm{safe}}(m)$ 非空。随机分布 $\pi(a\mid m)$ 的同一性质等价于

$$
\operatorname{supp}\pi(\cdot\mid m)\subseteq\mathcal A_{\mathrm{safe}}(m).
\tag{40.1}
$$

**证明及选择障碍。** 同一记录只允许相同的选择律，故其每个正概率动作必须对纤维中每个配置合法。反向在非空交集中按固定动作顺序取首项即可。随机化不能消除某一配置上正概率的非法动作。即使 $\forall x\,\exists a\in\operatorname{Adm}(x)$，也未必有 $\exists a\,\forall x\ a\in\operatorname{Adm}(x)$。例如同一记录下三个配置的动作集为 $\{a,b\},\{b,c\},\{a,c\}$，两两有交而三重交为空；两两控制相容不足以表示这个高阶障碍。

原生接口还给一个已有的具体记忆区别：[《指定编码九状态根查询逃逸》Definition 8.2、Theorems 8.4、8.7](FIB_PRESCRIBED_CODE_NINE_STATE_ROOT_ESCAPE.md) 固定同一个逐来源的取得位 $\sigma^\dagger$，在九状态预算下任意字面地址有至多两次调用的实现，根查询的最小最坏调用数为四。其完整表中

| 当前状态 | 当前地址 | $\alpha$ 后继 | 后继的地址 |
| --- | --- | --- | --- |
| $A$ | $LRRR$ | $B_1$ | $LLR$ |
| $C$ | $LRRR$ | $B_3$ | $RLR$ |

两状态承载不同入口位；不能因当前地址及回复相同就合并它们。比较中 $\sigma^\dagger$ 在每个原生来源上固定，既不能换成只由目标决定的位，也不能重选代表来源的编码。因此该结果与 (34.3) 中的联合优化是不同合同，二者不冲突。上述有限集合论及原生条款是后续五模式控制应用的中间输入。$\square$

## 18. 续篇Ⅳ：仪器支持、无泄漏与持续安全

**定义 41.1（候选支持与已安装仪器）。** 对可达历史 $h$ 给非空候选密度族 $\mathcal D_h$，令

$$
S_h=\operatorname{span}\bigcup_{\rho\in\mathcal D_h}\operatorname{ran}\rho,
\qquad P_h=\text{到 }S_h\text{ 的正交投影}.
$$

动作 $a$ 由与未知输入无关的固定仪器给出：

$$
\mathcal J_{a,b}(X)=\sum_\mu K_{a,b,\mu}XK_{a,b,\mu}^\dagger,
\qquad\sum_{b,\mu}K_{a,b,\mu}^\dagger K_{a,b,\mu}=I.
$$

$b$ 为实际结果，$\mu$ 不自动可读；不同记录可以安装不同仪器，此处省略其 $h$ 下标。令 $Q_{h,a,b}$ 为该结果允许的后继子空间投影。

**中间支持计算（41）。** 后续约束门合法性使用下列精确判据：对 $\mathcal D_h$ 全部候选、每个实际结果均零泄漏，当且仅当

$$
(I-Q_{h,a,b})K_{a,b,\mu}P_h=0\quad\text{对全部 }b,\mu.
\tag{41.1}
$$

**证明。** 第 6 节的 CP 仪器表示给

$$
\operatorname{tr}[(I-Q_{h,a,b})\mathcal J_{a,b}(\rho)]
=\sum_\mu\|(I-Q_{h,a,b})K_{a,b,\mu}\sqrt\rho\|_{\mathrm{HS}}^2.
$$

非负项之间不能抵消。对所有候选为零等价于各算子在全部 $\operatorname{ran}\sqrt\rho=\operatorname{ran}\rho$ 上为零，进而在它们张成的 $S_h$ 上为零，得到 (41.1)。不必假定候选族包括 $S_h$ 上全部密度矩阵。

近似情形若将输入域明确扩大为**全部**支持在 $S_h$ 上的密度矩阵，定义

$$
L_{h,a}=P_h\Bigl[\sum_{b,\mu}K_{a,b,\mu}^\dagger
(I-Q_{h,a,b})K_{a,b,\mu}\Bigr]P_h\geq0.
$$

正算子的最大期望等于最大特征值，故总泄漏的最坏值恰为

$$
\ell(h,a)=\|L_{h,a}\|_{\mathrm{op}},\qquad
\ell(h,a)\leq\epsilon\ \Longleftrightarrow\ L_{h,a}\leq\epsilon P_h.
\tag{41.2}
$$

对原来任意较小的候选族，右侧通常只给上界，不能冒称相同的最坏值。

当 $\pi(a\mid m_h)>0$ 时，结果 $b$ 的后验候选族定义为

$$
\mathcal D_{hab}=
\left\{\frac{\mathcal J_{a,b}(\rho)}{\operatorname{tr}\mathcal J_{a,b}(\rho)}:
\rho\in\mathcal D_h,\ \operatorname{tr}\mathcal J_{a,b}(\rho)>0\right\}.
$$

若此族非空，其支持满足

$$
S_{hab}=\operatorname{span}_\mu K_{a,b,\mu}S_h.
\tag{41.3}
$$

因为对每个 $\rho$，正算子和 $\sum_\mu K_\mu\rho K_\mu^\dagger$ 的像空间是各 $K_\mu\operatorname{ran}\rho$ 的张成，零概率项全为零；再对候选取张成即得。若结果对所有候选概率均为零，则右边为零、后验族为空，不生成实际下一历史。下一门的 (41.1) 必须使用新的 $P_{hab}$；剩余资源及记录也同时更新。$\square$

**定义 42.1（精确有限后继博弈）。** 取有限可观察控制状态集 $Z$、安全子集 $S\subseteq Z$、每个状态的有限合法动作集 $\mathcal A_{\mathrm{safe}}(z)$，以及每个合法动作的**非空**后继集 $\operatorname{Succ}(z,a)$。策略只依赖实际已见的状态历史，对手可选择任一后继。若此博弈代表一个物理或原生历史系统，还要求状态由实际记录递归取得，动作、资源和候选更新在 $Z$ 中精确封闭，合法策略可相互实现，并且允许的有限后继路径与实际可达历史相符。不能把未知量子态作为免费可读状态。对量子候选支持，(41.3) 给更新，但其落在某个有限摘要族中须另有封闭性依据。

**中间安全判据（42）。** 在这个精确有限博弈中令

$$
W_0=S,\qquad
W_{n+1}=\{z\in W_n:\exists a\in\mathcal A_{\mathrm{safe}}(z),\
\operatorname{Succ}(z,a)\subseteq W_n\}.
\tag{42.1}
$$

下降序列有限步稳定于 $W_*$。存在对全部可能结果持续安全且不陷入无动作死点的策略，当且仅当 $z\in W_*$。这是安全博弈的可控前驱不动点工具；观察不足时的知识状态构造见 Chatterjee–Doyen–Henzinger–Raskin，*Algorithms for Omega-Regular Games with Imperfect Information*，[arXiv:0706.2619v3](https://arxiv.org/html/0706.2619v3)，§§3.1–3.2 的非空知识后继及 $\mathsf{CPre}$。

**证明及摘要边界。** 在 $W_*$ 每个状态固定一个见证动作，其非空后继仍在 $W_*$，得到无记忆安全策略。若状态不在 $S$ 则已失败；若它在某轮被删除，则没有可用动作，或每个动作都有一个此前被删除的后继。按删除轮数归纳，对手可在有限步内迫使失败或死点，任何历史策略都不能避免。

若只知道实际后继包含于摘要给出的后继，且摘要动作在整个代表族中均合法，$W_*$ 仍给实际安全策略的充分条件，反向不成立。例如真实安全状态 $x,y,y'$、坏状态 $b$ 和唯一动作满足 $x\to y$、$y\to y$、$y'\to b$、$b\to b$。将 $y,y'$ 合成 $z_1$、$x$ 记为 $z_0$，用并集后继，则 $z_1$ 及 $z_0$ 均被删除；但真实地从 $x$ 始终安全。遗忘摘要不能凭有限性取得完备性。

完整 TP 仪器在非零支持上至少有一个正概率结果，供应后继非空；抽象博弈必须显式要求它。若 Stop 表示成功，须将成功态置为安全吸收态并给一个自环动作；空后继不能凭集合包含关系真空地算作持续控制。安全及非阻塞不等于最终完成，后者须另加终止目标或递减秩。一般量子支持族可以无限，(42.1) 不宣称任意量子控制问题都有有限判定。$\square$

## 19. 续篇Ⅳ：五模式的受约束翻转与记录障碍

**定义 43.1（三位置合法子空间）。** 在 $(\mathbb C^2)^{\otimes3}$ 中禁止相邻位置同时为一，取

$$
\Sigma_F=\{000,100,010,001,101\},\qquad
\mathcal H_F=\operatorname{span}\{|x\rangle:x\in\Sigma_F\},
$$

其投影为 $P_F$，按 $000,100,010,001,101$ 对应 $N,2,3,5,25$。令 $X_j$ 翻转第 $j$ 位，$P_j^0=|0\rangle\langle0|_j$。

**命题 43（原生五模式耦合的 PXP 对应及选择障碍）。** 三个八维 Hermitian 算子

$$
G_1=X_1P_2^0,\qquad
G_2=P_1^0X_2P_3^0,\qquad
G_3=P_2^0X_3
$$

均与 $P_F$ 交换。先限制为五维 $H_j=G_j|_{\mathcal H_F}$，则

$$
H_1+H_2+H_3=K.
\tag{43.1}
$$

若动作只提供裸翻转 $X_1,X_2,X_3$，记录“当前非空”不足以保证合法选择；受约束指数 $V_j(\theta)=e^{-i\theta H_j}$ 则对全部 $\mathcal H_F$ 合法。

**证明。** 裸翻转给 $X_1|010\rangle=|110\rangle\notin\mathcal H_F$，故 $(I-P_F)X_1P_F\ne0$。基态候选上的完整合法性表为

| 候选模式 | 合法裸翻转 |
| --- | --- |
| $000$ | $X_1,X_2,X_3$ |
| $100$ | $X_1,X_3$ |
| $010$ | $X_2$ |
| $001$ | $X_1,X_3$ |
| $101$ | $X_1,X_3$ |

“非空”的纤维为 $\{100,010,001,101\}$，其动作交集为空，尽管每个配置各有合法动作，由 (40.1) 得所述选择障碍。该表只用于基态候选；相干叠加不得免费读出“是哪一模式”，须用 (41.1)。

$G_1$ 的合法连接为 $000\leftrightarrow100$、$001\leftrightarrow101$；$G_2$ 为 $000\leftrightarrow010$；$G_3$ 为 $000\leftrightarrow001$、$100\leftrightarrow101$。没有合法到非法的非零矩阵元；由 Hermitian 性也没有反向跨界项，故 $[G_j,P_F]=0$。逐项相加得到定义 1.4 的同一个 $K$。这正是 PXP 邻位投影约束翻转的三位置开放边界实例；一般结构见 Turner 等，*Quantum Scarred Eigenstates in a Rydberg Atom Chain*，[arXiv:1806.10933](https://arxiv.org/html/1806.10933)，§II、式 (4)–(5)。本应用是有限代数对应，不声称该五模式有一个给定的物理实现。

$G_j$ 本身一般不是酉门，指数才是门；在受阻部分生成元为零，指数为恒等，故不需要先测量邻位再决定是否翻转。$K$ 的模式图边是耦合项，而历史图的一条边可代表一次完整指数或一次仪器。耦合项的存在不自动授权原菜单独立调用每个 $H_j$。$\square$

## 20. 续篇Ⅳ：固定非负等待菜单中的精确逆障碍

**假设 44.1（固定菜单合同）。** 保留定义 1.4 的全五维复输入、$U(s)=e^{-isK}$（$s\geq0$）、完整秩一模式读及 Stop。协议有共同有限深度并确定性终止，允许实际记录反馈及输入无关经典随机种子，不提供量子旁路或额外量子存储。随机资料若连续取值，假设协议与所得通道可测。目标按通道等价，即忽略酉矩阵整体相位。

**命题 44（非零等待无精确确定性有限逆）。** 对任意 $t>0$，该菜单没有全输入实现 $\rho\mapsto U(t)^\dagger\rho U(t)$ 的精确确定性有限协议。

**证明。** 直接由五阶行列式得

$$
\det(\lambda I-K)=\lambda(\lambda^4-5\lambda^2+2),\qquad
\operatorname{spec}(K)=\{0,\pm\omega_+,\pm\omega_-\},\quad
\omega_\pm^2=\frac{5\pm\sqrt{17}}2.
\tag{44.1}
$$

频率比的平方为 $(21+5\sqrt{17})/4$，无理，故 $\omega_+/\omega_-$ 无理。仅等待的有限序列合成为 $U(s)$、$s\geq0$。若它与 $U(t)^\dagger$ 给同一通道，则 $U(s+t)$ 为标量恒等；零特征值方向使标量为一。由于 $s+t>0$，两个频率都必须在这个时间取得 $2\pi$ 整数相位，迫使频率比有理，矛盾。

固定随机种子后展开反馈树。一条包含秩一模式读的叶分支，其系统 Kraus 乘积秩至多一。若一次首读发生，其读前等待可逆且每个秩一投影非零；TP 及有限终止保证有非零叶后继。另一方面，酉通道的 Choi 矩阵秩一，所以任意 Kraus 表示中每个非零算子都必须与该酉成比例，因而秩五。故精确酉协议不能包含非零读分支，只能退回已排除的等待序列。对隐藏 Kraus 项或经典合并结果求和不能恢复被失去的秩。

最后处理连续随机种子。若 $T=\int T_\xi\,d\mu(\xi)$ 是目标酉通道，令 $P$ 为目标归一化 Choi 态的秩一支撑，则

$$
0=\operatorname{tr}[(I-P)\chi_T]
=\int\operatorname{tr}[(I-P)\chi_{T_\xi}]\,d\mu(\xi).
$$

被积项非负，故几乎处处为零。正性及 Choi 态迹一迫使 $\chi_{T_\xi}=\chi_T$ 几乎处处；因此几乎每个固定种子的有限确定性协议都须实现同一个酉通道，与前两段矛盾。这不依赖随机种子具有正质量原子。

结论只排除完整输入上的精确、确定性、有限逆实现；未排除近似恢复、后选择或限制输入子空间。代数逆的存在没有改变给定菜单的权限。$\square$

## 21. 续篇Ⅳ：独立控制与附加相位的代数差别

**假设 45.1（扩大的控制合同）。** 在本节另行提供三个独立门 $e^{-i\theta H_j}$，每个 $\theta\in\mathbb R$ 可独立指定；第二种扩大再提供 $e^{i\phi|N\rangle\langle N|}$、$\phi\in\mathbb R$。这些是新增权限。五维被动坐标矩阵 $D$ 仍不作为门。若只提供任意非负参数，这些单项的谱为 $0,\pm1$ 或 $0,1$、具有 $2\pi$ 周期，也足以提供各自的逆；该周期性不适用于固定总和 $K$。

**命题 45（十维与二十五维控制代数）。** 先限制到五维再令 $A_j=-iD^\dagger H_jD$，则

$$
\operatorname{Lie}_{\mathbb R}(A_1,A_2,A_3)=\mathfrak{so}(5),\qquad
\operatorname{Lie}_{\mathbb R}(A_1,A_2,A_3,iE_{00})=\mathfrak u(5).
\tag{45.1}
$$

维数分别为 $10,25$。在原坐标中的生成门集合闭包分别为 $D\,SO(5)\,D^\dagger$ 与 $U(5)$。

**证明。** 五个模式编号为 $0,1,2,3,4$，令 $J_{ij}=E_{ij}-E_{ji}$。由 (43.1) 的分项得

$$
A_1=J_{01}-J_{34},\qquad A_2=J_{02},\qquad A_3=J_{03}-J_{14}.
$$

精确交换子为

$$
[A_2,[A_2,A_1]]=-J_{01},\qquad
[A_2,[A_2,A_3]]=-J_{03}.
$$

故 $J_{01},J_{02},J_{03},J_{14},J_{34}$ 均在生成代数中。它们的指标图连通，使用 $[J_{ij},J_{jk}]=J_{ik}$ 及反对称换号可得到全部十个 $J_{ij}$（$i<j$）。原生成元均为实反对称，故代数恰为 $\mathfrak{so}(5)$。

加入 $iE_{00}$ 后，已取得每个 $J_{0j}$，并有

$$
[iE_{00},J_{0j}]=i(E_{0j}+E_{j0}),\qquad
[J_{0j},i(E_{0j}+E_{j0})]=2i(E_{00}-E_{jj}).
$$

于是取得每个纯虚对角 $iE_{jj}$；再与 $J_{ij}$ 交换取得所有 $i(E_{ij}+E_{ji})$。十个实反对称、十个纯虚对称非对角及五个纯虚对角独立张成全部反 Hermitian 矩阵，得 $\mathfrak u(5)$。

闭包结论使用矩阵乘积公式及交换子极限：$e^{sX}e^{sY}e^{-sX}e^{-sY}=I+s^2[X,Y]+O(s^3)$，反复相乘并缩小 $s$ 可逼近交换子指数，Trotter 乘积可逼近和的指数。实参数给所需逆。因此闭包包含整个生成 Lie 代数的指数。平面旋转生成 $SO(5)$，每个酉矩阵又是某个反 Hermitian 矩阵的指数，得到两项闭包等式。反向包含由各生成元所属群立即得到。它表示每个目标及每个正容差有有限乘积逼近，没有给出统一的脉冲数、总时间或精度成本；也不反向扩大假设 44.1 的原菜单。维数 $25$ 包含整体相位，若按酉通道计数则还须商掉这一个不可观察相位方向。$\square$

**命题 45.2（合法门的顺序仍可区分）。** 令 $V_j=e^{-i\pi H_j/2}$，则

$$
V_2V_1|000\rangle=-i|100\rangle,\qquad
V_1V_2|000\rangle=-i|010\rangle.
$$

**证明。** $H_1$ 将 $000$ 与 $100$ 配对，$H_2$ 在 $100$ 上为零；交换顺序时 $H_2$ 将 $000$ 与 $010$ 配对，$H_1$ 在 $010$ 上为零。每个二态块在参数 $\pi/2$ 交换并乘 $-i$，受阻态保持恒等，得到两个不同结果。所有步骤都满足 (41.1)，但 $[H_1,H_2]\ne0$，故逐步合法不意味着不同顺序等价。$\square$

## 22. 续篇Ⅳ：程序资源与固定母结构中的策略组合

**定义 46.1（固定量子程序处理器）。** 程序与数据独立输入一个固定等距映射 $W$，所有程序 $|p_a\rangle$ 及剩余态 $|r_a\rangle$ 归一化，并要求对整个数据空间精确确定性地实现

$$
W(|p_a\rangle\otimes|\psi\rangle)
=|r_a\rangle\otimes U_a|\psi\rangle.
$$

一般 CPTP 处理器可先取等距扩张并把全部剩余环境计入 $r_a$。纯酉输出的纯态分解先迫使数据与环境乘积分离，再对数据基向量及其叠加使用线性性，迫使同一程序的剩余态不依赖未知数据；不能将数据藏进一个未计入的输出端口。

**程序正交性的中间工具（46）。** Nielsen–Chuang 的 *Programmable Quantum Gate Arrays*，[arXiv:quant-ph/9703032v1](https://arxiv.org/html/quant-ph/9703032v1)，Result 及式 (6)–(10)，给不同整体相位等价类的精确酉程序必须正交。此处直接使用其内积论证：等距性使任意 $\psi,\phi$ 满足

$$
\langle p_a,p_b\rangle\langle\psi,\phi\rangle
=\langle r_a,r_b\rangle\langle\psi,U_a^\dagger U_b\phi\rangle,
\qquad
\langle p_a,p_b\rangle I=\langle r_a,r_b\rangle U_a^\dagger U_b.
$$

若 $U_a^\dagger U_b$ 不是标量恒等，两个标量系数只能均为零。因此精确编程 $L$ 个两两不只差整体相位的酉需要至少 $L$ 维程序空间。应用于假设 45.1，只取 $e^{-i\theta H_2}$、$0<\theta<\pi/2$ 就已有任意多的不同相位类：$H_2$ 的零特征方向固定整体相位，$\pm1$ 特征方向区分区间内参数。故一个固定有限维纯程序端口不能精确确定性编程这整个连续子菜单。这是已知不可编程结果对本控制合同的应用，不另认作新的不可编程定理。

**命题 46.2（相干程序与经典选择的区别）。** 对正交控制标签，$W_c=\sum_a|a\rangle\langle a|\otimes U_a$ 是合法受控酉；输入 $\sum_ac_a|a\rangle\otimes|\psi\rangle$ 输出 $\sum_ac_a|a\rangle\otimes U_a|\psi\rangle$。

**证明。** 正交标签使 $W_c^\dagger W_c=W_cW_c^\dagger=I$，输出式由线性性得到。相干输出不等于一个已经记录的经典动作；读取控制寄存器须另指定仪器。该结构不提供任意指定测量结果的权限。$\square$

**定义 47.1（内生策略—仪器合同）。** 在同一个固定 $\Omega$ 中保留记录空间 $M$、纤维 $\mathcal F_m$、安全动作集、每个已安装动作的 CP 仪器 $\mathcal J_{a,b\mid m}$、记录更新 $m'=f(m,a,b)$，以及记录上的归一化分布 $\pi(a\mid m)$。动作与结果集有限，

$$
\sum_a\pi(a\mid m)=1,\qquad
\operatorname{supp}\pi(\cdot\mid m)\subseteq\mathcal A_{\mathrm{safe}}(m),\qquad
\sum_b\mathcal J_{a,b\mid m}\text{ 保迹}.
$$

记录与候选、资源的后继更新须相符；持续安全若使用有限模型，则另满足定义 42.1。取 $\sigma_\varnothing=\rho_0$、$\operatorname{tr}\rho_0=1$，同时定义全部相容历史关系

$$
\sigma_{hab}=\pi(a\mid m_h)\mathcal J_{a,b\mid m_h}(\sigma_h),
\qquad m_{hab}=f(m_h,a,b).
\tag{47.1}
$$

**中间概率组合（47）。** 第 6 节的仪器迹守恒与策略归一化给

$$
\sum_{a,b}\operatorname{tr}\sigma_{hab}
=\sum_a\pi(a\mid m_h)\operatorname{tr}\sigma_h
=\operatorname{tr}\sigma_h.
\tag{47.2}
$$

**证明及合同边界。** 对每个 $a$ 先使用仪器和的 TP 性，再对归一化动作分布求和即可。所有态正半定，故零质量历史的态为零、全部后继也为零。在 $\operatorname{tr}\sigma_h>0$ 时有 $\Pr(a\mid h)=\pi(a\mid m_h)$；若还满足 $\pi(a\mid m_h)>0$，则

$$
\Pr(b\mid h,a)=\frac{\operatorname{tr}\mathcal J_{a,b\mid m_h}(\sigma_h)}
{\operatorname{tr}\sigma_h}.
$$

零质量历史不定义条件概率；零概率动作只使 $\Pr(b\mid h,a)$ 不定义，$\Pr(a\mid h)=0$ 仍有定义。共同有限深度且每条分支均终止时，反复用 (47.2) 得叶概率和为一。若动作连续，则须改用可测概率核及积分，不能直接用有限求和符号；命题 44 已在独立随机种子层处理其所需情形。

因此策略描述“如何选动作”，仪器的 Born 概率描述“选定动作后出现什么结果”；一个不替另一个决定取值。若某实际记录有两个均可持续安全的动作，分别选择它们便给不同合法策略，故合法性和 Born 权重都不保证策略唯一。具体策略所依赖的记忆、目标或反馈规则须在 $\Omega$ 内承载，而 (47.1)–(47.2) 允许把这些关系共同放入固定结构，不需要额外图外选择者。这是给定量子表示下的组合结论，不从图的静态性推出 Born 律或经验本体主张。$\square$

**命题 47.2（门语法与内部选择器的组合）。** 在上述合同中，合法续接由已取得历史、尚未排除的候选纤维、纤维上的共同安全动作、实际选择律、结果及资源更新依次确定。状态空间相同不保证控制能力相同。

**证明。** (40.1) 限定可选动作，(41.1) 检查量子支持，(41.3) 更新下一历史，精确有限模型中 (42.1) 判持续安全，(47.1)–(47.2) 给联合记录概率。命题 43 的非空记录反例证明逐配置可选不足以统一选择；命题 44 与 45 则在同一五维空间上分别给固定非负等待、三个独立受约束控制及再加相位的不同权限。它们共同确定路径的语法与选择的承载，不能仅用抽象门集合或 Hilbert 空间维数代替。$\square$

## 追加锚（本行以下为增补区）

## 23. 续篇Ⅵ：有限未来纤维与有记忆的相融截面

**定义 48.1（含提前终止的策略纤维）。** 设 $X$ 是定义 40.1 的实际完整配置域，$m$ 是观察者已经取得的充分控制记录，$X_m\ne\varnothing$ 是其候选纤维。记录充分指：当前接口、合法性、终止合同和剩余资源由 $m$ 确定；记录按已实施动作与实际结果递归更新；候选更新恰好保留能够实现该观察历史的配置及后继。量子情形使用定义 41.1 的候选族及实际仪器更新，不把未知态作为记录。若某摘要不能满足这些条件，以下递归只适用于完整观察历史，不能把它无条件压到该摘要上。

记 $\mathcal T(m)$ 为全部合法终止输出：$d\in\mathcal T(m)$ 当且仅当在 $X_m$ 上立刻输出 $d$ 对每个候选都满足终止合同。记 $\mathcal A_{\mathrm{safe}}(m)$ 为对整个候选纤维统一合法的非终止动作。对其中每个 $a$，令

$$
B(m,a)=\{b:\text{某个候选在动作 }a\text{ 后实际允许结果 }b\},
\qquad m_{a,b}=f(m,a,b).
\tag{VI.1}
$$

假定动作集、终止输出集和各 $B(m,a)$ 有限；$B(m,a)$ 非空，且只为其中的 $b$ 生成非空后继候选纤维。资源消耗包含在合法性与更新中。令 $n$ 仅计尚可实施的非终止动作数，定义带语法标记的有限树

$$
\begin{aligned}
\Pi_0(m)&=\{\operatorname{Stop}(d):d\in\mathcal T(m)\},\\
\Pi_{n+1}(m)&=\{\operatorname{Stop}(d):d\in\mathcal T(m)\}\\
&\quad\sqcup\bigsqcup_{a\in\mathcal A_{\mathrm{safe}}(m)}
\left\{\operatorname{Run}\bigl(a,(\pi_b)_{b\in B(m,a)}\bigr):
\pi_b\in\Pi_n(m_{a,b})\right\}.
\end{aligned}
\tag{VI.2}
$$

它称为**至多 $n$ 步策略纤维**。Stop 在每一个正时限仍可用，故已完成任务不必额外实施一个门。没有合法动作、没有合法 Stop 的记录才是死端；对非法动作或虚构的空后继作全称量化不能产生成功策略。

**所用中间事实及证明。** 在以上精确历史语义中，$\Pi_n(m)$ 的元素恰为从 $m$ 出发、对全部实际结果保证合同成立的深度至多 $n$ 的确定性策略树。深度零只有合法 Stop；正深度或先 Stop，或先作一个统一合法动作，并在每个实际结果下接上一棵较浅成功树。对深度归纳即得双向对应。因而对 $n\ge1$，可作为第一项非终止动作的集合是

$$
\mathcal A_{\mathrm{viable},n}(m)=
\left\{a\in\mathcal A_{\mathrm{safe}}(m):
\forall b\in B(m,a),\ \Pi_{n-1}(m_{a,b})\ne\varnothing\right\},
\qquad \mathcal A_{\mathrm{viable},0}(m)=\varnothing.
\tag{VI.3}
$$

其基数 $\chi_n^{\mathrm{run}}(m)$ 只计第一动作，不计 Stop，也不计后续树的多重性。即使 $\chi_n^{\mathrm{run}}(m)=1$，同一个第一动作仍可接多个成功后续；$\chi_n^{\mathrm{run}}(m)=0$ 且 $\mathcal T(m)\ne\varnothing$ 则是可直接完成，而不是死端。对上述带标记树，有限积给出

$$
|\Pi_{n+1}(m)|=|\mathcal T(m)|+
\sum_{a\in\mathcal A_{\mathrm{safe}}(m)}
\prod_{b\in B(m,a)}|\Pi_n(m_{a,b})|.
\tag{VI.4}
$$

这套递归是有限时限后向归纳的中间工具，不构成一个新的博弈定理。知识状态及非空知识后继的标准来源是 Chatterjee–Doyen–Henzinger–Raskin，*Algorithms for Omega-Regular Games with Imperfect Information*，[arXiv:0706.2619v3](https://arxiv.org/html/0706.2619v3)，§§3.1–3.2；其 sure-winning 的全分支要求与 almost-sure winning 应分别使用。这里另行把 Stop、资源及精确候选更新纳入有限时限合同。

**定义 48.2（带共享记忆约束的策略截面）。** 把一棵候选策略的实际可达观察历史记为 $H$。在每个非终止历史上放一个动作变量，在每个终止历史上放一个输出变量；动作合法性、实际结果后继和终止合同组成定义 5.1 的关系约束。若观察者保留全部观察历史，分叉后的位置没有被强制合并，式 (VI.2) 的分支积就给相容截面。

若观察者只有一个计数状态 $k\in K$，还须存在同一张安装表：状态动作 $a(k)$、确定更新 $\delta(k,b)$ 及终止状态的固定输出。对每个可达历史指定 $\eta(h)\in K$，要求

$$
\eta(h)=\eta(h')\ \Longrightarrow\ a(h)=a(h'),\qquad
\eta(hab)=\delta(\eta(h),b),
\tag{VI.5}
$$

并要求相同终止状态有相同输出，终止与非终止不能在同一状态混用。若动作由状态输出，更新表不需另读动作；若采用其他控制模型，就把它允许的更新输入明确列出。候选环境、目标及预算约束仍须沿同一实际历史检验。满足全部这些约束的赋值称为该记忆布局上的相融策略截面。只在所选策略可达的历史上承担行为约束，未到达记录不能给唯一性结论增添虚构的差别。

**中间拼接边界及证明。** 式 (VI.2) 允许两个结果分支各自选树；式 (VI.5) 可能禁止把这两个选择放进同一个计数状态。取两个实际来源 $x_0,x_1$，第一步合法探测分别回复 $0,1$；此后只有动作 $a_i$ 在 $x_i$ 上合法并到达目标。记住探测回复的树可分别选 $a_0,a_1$。若指定布局将两条探测后历史合并到同一状态，并且没有其他回复寄存器，则共同动作必须属于 $\{a_0\}\cap\{a_1\}=\varnothing$，不存在截面。故两个分支各有延拓不蕴含该共享布局有延拓。反之，满足 (VI.5) 的赋值直接定义一张统一控制表，沿实际结果归纳就实现该截面。

同样，$n$ 是证明中的时限参数，不自动是运行时可读计数器。把控制状态替换成 $(k,j)$、$0\le j\le n$，可能需要多达 $(n+1)|K|$ 个状态；访问记录、动作日志和外部时钟均须按实际模型计费。后文直接保留安装图上的共享状态，不以免费展开策略树来证明同预算实现。

## 24. 续篇Ⅵ：联合任务关系的接口与等价强度

**定义 49.1（共同接口下的三种等价）。** 固定同一个实际源域 $X$，以及具有固定坐标类型的任务读出 $j_P:X\to Y$。$Y$ 可以包含准备回复、服务回复、完整目标及声明保留的其他量。定义

$$
\begin{aligned}
P\sim_{\mathrm{supp}}Q&\quad\Longleftrightarrow\quad j_P(X)=j_Q(X),\\
P\sim_{\mathrm{src}}Q&\quad\Longleftrightarrow\quad
\forall x\in X,\ j_P(x)=j_Q(x).
\end{aligned}
\tag{VI.6}
$$

若另给共同概率空间 $(X,\mu)$ 且读出可测，定义

$$
P\sim_\mu Q\quad\Longleftrightarrow\quad (j_P)_*\mu=(j_Q)_*\mu.
\tag{VI.7}
$$

此处 $j_P(X)$ 是全部实际可达像，而非自动舍弃零质量点的测度支撑。给内部状态换名称时，必须先给保留接口的显式坐标识别；把 $0,1$ 对调而仍直接使用固定标号入口，不是一个默认允许的识别。对由共同随机源驱动的实现，可把该源并入 $X$；量子仪器则以其实际概率律处理，不能因记号相同而预填所有不相容实验的共同回复。

**所用中间边界及证明。** 支持相等恰好保证集合 $j_P(X)$ 上的谓词和函数相同；它保持哪些坐标组合能够由某一个来源共同实现，却不指定双方的那个来源相同。以下有限区分将在原生应用中固定解释范围。

取 $X=\{x_0,x_1\}$、目标恒定，令 $j_P(x_i)=i$、$j_Q(x_i)=1-i$。两个像都为 $\{0,1\}$，逐来源却不同。若 $\mu(x_0)=1/3$、$\mu(x_1)=2/3$，则两读出的 $0$ 概率分别为 $1/3,2/3$。故像相等不保持这些概率、条件概率或期望；即使两读出的分布相同，也不必逐来源相同。把来源身份 $x$ 本身加入共同接口后，$\{(x,j_P(x)):x\in X\}=\{(x,j_Q(x)):x\in X\}$ 才等价于逐来源相等。

回复向量也不独自决定预算。设某个 Read 的实际回复恒为 $b$，两张表在该回复上分别转到正确 Halt 和转回自身；同一查询向量与目标可以给完全相同的联合像，但前者一次调用结束，后者永不结束。要从回复关系转移预算，须保留统一的执行解释器，或者把带成本的执行读出本身加入关系。后文保留整张相同连线表，正是前一种条件。

两两联合关系仍不总够。令

$$
J_\epsilon=\{(u,v,w)\in\{0,1\}^3:u\oplus v\oplus w=\epsilon\},
\qquad \epsilon\in\{0,1\}.
\tag{VI.8}
$$

固定任意两个坐标，第三个由异或式唯一给出，所以两个关系的每个二元投影都是 $\{0,1\}^2$；但偶校验合同在 $J_0$ 上全成立，在 $J_1$ 上全失败。这是第 5 节高阶约束遗漏的联合像版本。后文的准备、服务、观察与目标必须用一个完整联合行，而不能分别给它们挑来源。

**定义 49.2（接口相对的上下文）。** 一个关系上下文只允许对声明的联合坐标作固定函数、关系检验或条件筛选。支持相等对这些上下文封闭：若 $J=J'$，则对任意 $C\subseteq Y$ 及任意 $d:Y\to Z$，有 $J\cap C=J'\cap C$ 及 $d(J)=d(J')$。证明是同一个集合上的交与像运算。这个事实不授权读取 $Y$ 之外的新来源信息、历史、地址字面或概率权重；若要允许这些读取，必须扩展接口并重新检验联合关系。命题 52 将在固定原生模型中给出不能省略该限制的具体例子。

## 25. 续篇Ⅵ：同一地址正规形保留整族共享状态策略

**定义 50.1（固定原生实例与连线族）。** 本节使用 [《有界原生准备器综合与线性字面正规化》](FIB_BOUNDED_NATIVE_PREPARER_SYNTHESIS.md)（下称 BPS）Definitions 1.1–1.3、3.2–3.3 及 Assumption 3.1 的整个原生合同：

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\quad\rho\alpha=\beta,\quad\rho\beta=\langle\beta,\alpha\rangle,
\quad\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle,
\quad\mathcal U_*=\{u:R_{\{L,R\}^3}(\rho u)=R_*\}.
\tag{VI.9}
$$

$R_*$ 是 BPS Definition 1.3 的六类重复伙伴完整当前行，$F(u)=R_{\{L,R\}^3}(u)$ 是含全部外部形状、孔、重命名后的限制分区、全值不等式与守卫的完整目标。记 $t_u=\rho u$，原生回复字母表为 $\mathcal R=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$。寄存器在两阶段静止，准备器只有当前计数状态，不取得已采集树、回复元组、来源身份、日志、计数器或附加工作寄存器。调用、取得、认证、隔离、仅代码交接及忠实新入口保持 BPS 的权限与分别支付条件。准备 Halt 以完整位锁存替换原控制，交接忠实进入 $e_0$ 或 $e_1$，位可从入口身份恢复，但没有另一个持续可读位寄存器。$N$ 只计全部安装记录，$P,L$ 只计实际原生调用；地址表示与传输、表安装、行及输出存储、取得和交接等另有各自的权限与价格，不由这些三坐标预算取得总物理资源守恒结论。

固定服务表 $T=(K_T=Q_T\sqcup H_T,a_T,n_T,o_T,e_0,e_1)$，其中两原始有标号入口不同，所有服务记录及全部输出字面不变。固定非空准备器安装骨架 $K=Q\sqcup H$，$|K|\le N$，以及每个 Read 的有限字面地址赋值 $a:Q\to\{L,R\}^*$。只让以下连线参数变化：

$$
\Theta_K=K\times K^{Q\times\mathcal R}\times\{0,1\}^{H},
\qquad \theta=(s,\nu,\lambda).
\tag{VI.10}
$$

它们分别指定一个共同起点、所有四回复后继和每个 Halt 的原始导出位。无 Halt 时也保留这个有限族，实际成功条件会排除它。全部已安装状态计费，包括重复、未用和同位的多个 Halt。$\Theta_K$ 是多张可选安装表的数学族，不是运行时读取了来源以后再选表的权限。

与连线无关的实际联合行是

$$
J_a=\left\{\left(v_a(u),w_T(u),F(u)\right):u\in\mathcal U_*\right\},
\quad
v_a(u)=(r_{t_u}(a(q)))_{q\in Q},\quad
w_T(u)=(r_{t_u}(a_T(q)))_{q\in Q_T}.
\tag{VI.11}
$$

两个向量按全部安装 Read 的身份编号，保留未访问状态、重复地址和两个服务入口的全部潜在回复；它们只是数学坐标，不是向控制器交付的数据。

**定义 50.2（回复行的统一执行解释）。** 给行 $(v,w,f)$ 和 $\theta$，从 $s$ 出发，在 Read $q$ 读取坐标 $v_q$ 并沿 $\nu(q,v_q)$ 走；每次 Read 恰计一次调用，Halt 立刻输出 $\lambda(h)$ 并不再调用。随后经原始位进入 $e_{\lambda(h)}$，依服务表及 $w$ 运行，并输出固定完整行。记录两阶段的状态—回复轨迹、调用数、导出位、服务输出与目标 $f$。若准备阶段或选中服务阶段首次重复 Read，就记该阶段为发散，保留到首次重复的有限轨迹和发散标记。未进入的阶段记为未进入。这样得到一个总定义的有限描述 $d_\theta(v,w,f)$。

**中间事实及证明。** 在静止源上，每个 Read 的回复固定；重复 Read 会重复其全部确定未来，因此不能后来才 Halt。故这个解释与实际运行一致，有限扫描至多经过 $|Q|+1$ 个准备 Read 访问以及 $|Q_T|+1$ 个已进入服务 Read 访问就能判明终止或重复。一个终止路径不重复 Read，准备及服务调用数分别不超过 $|Q|,|Q_T|$。这是 BPS Lemma 3.4 的固定来源路径论证；不同来源的路径并集可以有环。地址变更后，这个解释保留的是状态身份、回复与计数，未声称保留查询字符串组成的字面轨迹。

**定理 50（连线族的共同正规形）。** 置

$$
q_T=|Q_T|,\qquad
b=\max\bigl(\{0\}\cup\{\max(0,|a_T(q)|-3):q\in Q_T\}\bigr),
\qquad D_0=3+b+6(q_T+N).
\tag{VI.12}
$$

对每个地址赋值 $a$，存在可有效构造的**同一个**赋值 $a^\flat$，使每个 $|a^\flat(q)|\le D_0$ 且 $|a^\flat(q)|\le|a(q)|$，并同时满足下列结论。

1. $J_{a^\flat}=J_a$；准备骨架和服务表不变。
2. 对全部 $\theta\in\Theta_K$，以及全部调用上预算 $P,L\in\mathbb N_0$，$\theta$ 在 $a$ 下是成功 SOME-preparer，当且仅当在 $a^\flat$ 下是成功 SOME-preparer。
3. 更强地，联合族关系

$$
\mathscr D_a=\left\{\left(v,w,f,
(d_\theta(v,w,f))_{\theta\in\Theta_K}\right):(v,w,f)\in J_a\right\}
\tag{VI.13}
$$

不变。即对每个旧实际来源，有一个新实际来源共同匹配所有安装回复、完整目标和**全部连线表**的带成本执行描述；反向亦然。匹配来源不要求相同。

**证明。** BPS Theorem 8.3 的正规化只读取准备地址和全部固定服务地址。其共同后缀 trie 的指标是安装 Read 身份、前三字母所给出现位置和类角色；BPS Theorem 7.1 的缩短不读取准备起点、后继或 Halt 位。BPS Lemma 8.2 的六容量提升只读取这些指标、回复和完整目标，也不使用连线。因而可先任取一张 $\theta$ 调用该构造，所得 $a^\flat$ 与所取 $\theta$ 无关，且满足第一项和深度界。

对相同 $(v,w,f)$，定义 50.2 的每张表都有相同 $d_\theta$。对第一步、下一状态及所有后续 Read 归纳，直至 Halt 或首次重复，得到第三项。特别地，$J_a$ 中的每个行由一个实际来源实现；$J_{a^\flat}=J_a$ 为该整行给一个来源，而不是给不同坐标或不同 $\theta$ 各挑来源。于是这个来源同时匹配 (VI.13) 的所有分量。

对 $\theta$，定义行上的成功谓词 $G_{\theta,P,L}$：准备在 $P$ 次内 Halt，所选原始位入口在 $L$ 次内 Halt 并输出整个 $f$。再定义实际达到位集

$$
B_\theta(J)=\{\text{准备实际输出位}: (v,w,f)\in J,
\text{准备在该行 Halt}\}.
\tag{VI.14}
$$

成功恰为每个行满足 $G_{\theta,P,L}$ 且 $B_\theta(J)=\{0,1\}$。关系相等和解释相同保持这两条，得到第二项。BOTH 是跨来源的存在性条件，不能把它替成每个来源都可任选两位；一个只到达一位的表即使逐行正确也不满足此合同。未选入口不必成功，惟其全部安装回复仍在 (VI.11) 内。$\square$

**推论 50.3（整族资源前沿与共享状态约束）。** 令 $\operatorname{Feas}_a(P,L)\subseteq\Theta_K$ 为成功连线表集，则定理 50 的单个 $a^\flat$ 满足

$$
\forall P,L,\quad
\operatorname{Feas}_a(P,L)=\operatorname{Feas}_{a^\flat}(P,L).
\tag{VI.15}
$$

对任何在全部来源上终止、输出正确并达到 BOTH 的 $\theta$，记 $p_a(\theta),\ell_a(\theta)$ 为两阶段实际调用数的最大值。它们分别至多为 $|Q|,q_T$，且与正规形下的值相同。因此该骨架上所有连线的精确二坐标成本集及 Pareto 极小元不变。对任意由安装表身份规定的子族 $\Theta_0\subseteq\Theta_K$，结论仍成立。

**证明。** 式 (VI.15) 是逐表的第二项同时成立。有限非空 $J_a$ 上，终止调用数有最大值；定义 50.2 的无重访事实给上界，第三项给最大值和成本集相同。限制到 $\Theta_0$ 不改变任一行解释。每张表已经以单个状态动作与同一四后继表满足共享约束，不需要为不同分支复制状态或附加时限计数器。这就把定义 48.2 的有记忆截面族连同资源前沿一起运输。这里的量词是 $\forall a\,\exists a^\flat\,\forall\theta\,\forall P,L$，不是一个赋值同时代表所有原地址赋值。$\square$

定理 50 与推论 50.3 的数学引文是 BPS §§5–9，尤其安装态索引关系 (BPS.21)、Theorem 8.3 和 Theorem 9.1；本处 `repo-derived` 的应用是同一个构造对全部连线、全部上预算以及跨连线共同来源关系的统一运输。后向归纳、确定路径解释和 Pareto 次序均作为标准中间工具使用，不另认领其一般理论。

## 26. 续篇Ⅵ：固定有限观察接口下的条件策略运输

**定义 51.1（保护观察与条件纤维）。** 在定义 50.1 的同一寄存器上，额外固定一个有限字面观察表

$$
\mathcal H=(h_1,\ldots,h_s),\quad h_i\in\{L,R\}^*,\qquad
z_{\mathcal H}(u)=(r_{t_u}(h_i))_{i=1}^s.
\tag{VI.16}
$$

重复字面仍各有指标，$s=0$ 允许空向量。该表是待保留的观察接口，不自动向准备器或服务表增添运行时端口。对 $C\subseteq\mathcal R^s$，条件来源域为 $X_C=\{u\in\mathcal U_*:z_{\mathcal H}(u)\in C\}$。受限成功合同中的 BOTH 在 $X_C$ 上取实际位集；若另外要求全域 BOTH，则须同时检验全域位集。定义扩展的同源联合关系

$$
J_{a,\mathcal H}=\left\{(v_a(u),w_T(u),z_{\mathcal H}(u),F(u)):
 u\in\mathcal U_*\right\}.
\tag{VI.17}
$$

**定理 51（有限观察相对的共同正规化）。** 置

$$
\begin{aligned}
b_{\mathcal H}&=\max\left(\{0\}\cup
\{\max(0,|a_T(q)|-3):q\in Q_T\}\cup
\{\max(0,|h_i|-3):1\le i\le s\}\right),\\
D_{\mathcal H}&=3+b_{\mathcal H}+6(q_T+N+s).
\end{aligned}
\tag{VI.18}
$$

对每个 $a$，存在一个有效的 $a^{\flat\mathcal H}$，逐字弱缩短准备地址、全部长度至多 $D_{\mathcal H}$，固定 $T$ 和每个 $h_i$，使

$$
J_{a^{\flat\mathcal H},\mathcal H}=J_{a,\mathcal H}.
\tag{VI.19}
$$

同一个赋值同时保留所有 $\theta\in\Theta_K$、所有上预算和所有条件事件 $C\subseteq\mathcal R^s$ 的受限回复关系、状态—回复执行关系及成功连线表集。若受限域为空，明确称它为空条件纤维；不把其全称合同的真空成立当作实际成功来源或 BOTH 见证。

**证明。** 将服务、准备和观察三种指标一起放入 BPS Definition 5.1 的共同后缀 trie。每个长度至少三的字面仍拆成原出现前缀 $p_i$ 与后缀 $w_i$，保留指标的类角色。长度不足三的字面在整个实际域回复共同外部 branch。令三种长字面指标的总数为 $m_{\mathcal H}$，则

$$
m_{\mathcal H}\le q_T+|Q|+s\le q_T+N+s.
\tag{VI.20}
$$

BPS §§5–6 的完整四类型六容量摘要和底二一元链稳定式不区分指标的用途。把深度至多 $b_{\mathcal H}$ 的全部 trie 节点冻结，服务及观察的所有后缀端点均已冻结。在其下对每段超过两节点的无标记一元链保留底二节点，BPS Theorem 7.1 的计数证明逐字适用：至多 $2m_{\mathcal H}-1$ 个带标记或二叉的本质节点，每个本质节点前至多两一元节点，故端点深度至多 $b_{\mathcal H}+6m_{\mathcal H}$。服务与观察字面保持原位；准备后缀只缩短，并保留其前三字母。短准备字面可替成 $\varepsilon$，实际调用仍计费。若 $m_{\mathcal H}=0$，全部回复恒为 branch，直接作这些短字面替换即可。

还须证明扩展关系是一个来源的关系。对旧来源的六个不同类值，记录每个类值在**全部三种后缀指标**上的完整回复和类型。缩短前后摘要相等，故每个占有 $j\le6$ 个类值的响应格在新 trie 中也有至少 $j$ 个不同有限树。逐格选不同值，不同格天然不交，保留全部六类整体不等式；两个重复伙伴分别复用同一个选值。类型保留给相同的十一类实际 profile，BPS Lemma 8.2 的逆像构造给一个实际 $u'$，同时实现准备、服务、观察及同一个完整目标。反向同理。观察指标没有引入新的独立类值，故容量截断仍为六，而非 $6+s$。这证明 (VI.19)。

对任意 $C$，以第三坐标属于 $C$ 筛选关系相等式，得到两侧受限行集合相等；每张 $d_\theta$ 仍只从相同安装回复解释，故定理 50 的证明在受限行上成立，包括实际位集。一个原始 $u\in X_C$ 的匹配 $u'$ 也属于 $X_C$。正规形依赖 $a,T,\mathcal H$，不依赖 $C,\theta,P,L$。$\square$

**推论 51.2（有限菜单上下文及条件截面）。** 固定一个合法有限观察上下文，其每次原生查询字面属于 $\mathcal H$，其分支只读取通过已支付接口实际取得的观察回复、已授权的原始导出位及自身已计数状态；规定一个有限调用上界。则定理 51 保留该上下文的全部实际结果与调用数，连同原执行描述及完整目标的联合支持。完整目标与库存回复元组只是分析坐标，不作为上下文运行输入。特别地，对每个实际观察向量 $z$，两侧条件纤维具有同一组可行原安装连线表，故其非空性、唯一表性及表族成本前沿相同。

**证明。** 静止源使同一个字面的多次回复相同，上下文的适应性决策树因而是被保护联合行的一个固定函数。按上下文状态归纳，回复、分支、终止和调用计数相同；对相同联合行取像即可。取 $C=\{z\}$ 再用定理 51 得条件结论。若上下文在字面地址上分支，则已超出本推论的坐标；若它读取新的地址，则应先把这些字面并入 $\mathcal H$。一个实际观察查询仍是另付的原生调用，观察状态也仍计入它自己的预算；$s$ 在 (VI.18) 中是数学保护指标数，不是向准备器免费增加 $s$ 状态或 $s$ 次调用。对条件记录先取得 $z$ 再选择一张表，也需要另外给定并支付这个选择器，不能从条件非空性推出原共同起点模型已经取得了 $z$。$\square$

定理 51 的数学引文为 BPS Theorem 7.1、Lemma 8.2 及 Theorem 8.3。本处 `repo-derived` 的扩展是把固定有限观察字面作为额外冻结指标，以同一六容量提升同时保护条件来源纤维和整个连线族；这不是对无限观察语言的统一正规化。

## 27. 续篇Ⅵ：完整原生模型中的未保护上下文分离

**命题 52（相同原生联合支持不蕴含新增观察下等价）。** 存在同一个固定服务表 $T$ 及两个三状态准备器 $P_3,P_4$，都在原预算 $(N,P,L)=(3,1,4)$ 上成功，且具有相同 (VI.11) 联合关系、相同安装连线与 Halt 位；但加入一个固定原生观察字面以后，其“观察回复—导出位—完整目标”联合关系不同。两个准备器在某个相同实际来源上导出的原始位也不同。

**构造。** 使用 BPS Proposition 1.4 的五个完整目标 $R_0,R_1,R_2,R_3,R_4$，四个右类代表字面为

$$
p_1=LLR,\quad p_2=LRR,\quad p_3=RLR,\quad p_4=RRR.
\tag{VI.21}
$$

安装五个 Read $E_0,E_1,S_2,S_3,S_4$ 和五个 Halt $H_0,\ldots,H_4$。原始入口 $e_0=E_0,e_1=E_1$ 不同，$E_0,E_1$ 都查询 $p_1$：回复 alpha 转 $H_1$，其他三种回复转 $S_2$。$S_i$ 查询 $p_i$，回复 alpha 转 $H_i$；对 $i=2,3$ 的其他回复转 $S_{i+1}$，$S_4$ 的其他回复转 $H_0$。$H_i$ 输出固定整个 $R_i$。这给所有四回复后继，不删未用记录，也不合并两个入口副本。

两个准备器共用安装集 $\{Q,H^P_0,H^P_1\}$、起点 $Q$；在回复 beta 时转 $H^P_1$，其他回复转 $H^P_0$，两个 Halt 分别输出原始位 $0,1$。$P_d$ 的唯一 Read 字面为

$$
a_d(Q)=LLL\,L^d=L^{3+d},\qquad d\in\{3,4\}.
\tag{VI.22}
$$

**证明。** 整个原生域只有 $\Pi_i$ 含右类 alpha，且唯一的 alpha 在 $b_i$；其目标正好为 $R_i$。所有 $Z$ profile 没有右类 alpha，目标为 $R_0$。因此服务表从两个原始入口都正确，最多四次 Read，全部十个安装服务状态都保留。服务正确性不依赖准备位，故这两个位不用改变入口标签就都合法。

比较 $P_3,P_4$ 的共同后缀 trie。五个服务 Read 的后缀全为 $\varepsilon$，在根上有各自标记；唯一准备后缀是 $L^3$ 或 $L^4$。后者在根标记与末端准备标记之间有三个连续的无标记左一元节点，前者只有两个。BPS Lemma 6.3 把三节点链缩成其底二，保持根的全部类型—回复格六容量，并保留各个服务指标、准备指标及出现角色。BPS Lemma 8.2 遂给

$$
J_{a_3}=J_{a_4}.
\tag{VI.23}
$$

也可直接检验这个相等式：每个 profile 固定全部服务根回复和完整目标；$x_a=\beta$ 时两种准备回复都为 absent，而 $x_a$ 为 branch image 时，沿纯左后缀不可能到达 alpha，恰可出现 beta、branch、absent 三种回复。对长度 $d$，分别取 $x_a=B_d,B_{d+1},B_{d-1}$ 就实现三种回复，其他未定类可以选不同的 branch image 避开它们；这里的 $B_j$ 如下定义。这给整个域、全部安装回复与完整目标的双向支持相等。

令 $B_0=\beta$、$B_{j+1}=\langle B_j,B_j\rangle$。每个 $B_j$（$j\ge1$）为不同的有限 branch image，且任一深度 $j$ 字面回复 beta，再深一级回复 absent。对 $P_d$ 取 $x_a=B_d$，其准备位为 $1$；取 $x_a=B_{d+1}$，其准备位为 $0$。把另外五类填成与之不同的正高度 $B_j$，全是 branch image，于是得到实际 $Z_*$ 来源。故两个准备器各自都实际达到 BOTH，并在一次调用内 Halt，证得预算成功。

现在固定新增观察 $h=L^6$。取明确的六类赋值

$$
x_a=B_3,\quad x_c=B_8,\quad
x_{b_1}=B_4,\quad x_{b_2}=B_5,\quad x_{b_3}=B_6,\quad x_{b_4}=B_7.
\tag{VI.24}
$$

它们两两不同且均为 branch image；以 BPS 的重复伙伴填充 $\mathscr S(x)$，则

$$
u_*=\delta(\mathscr S(x))\in\mathcal U_*,\qquad F(u_*)=R_0.
\tag{VI.25}
$$

其中 $\delta$ 是 BPS Lemma 1.2 的有限 image 逆。在同一 $t_{u_*}$ 上，$r(h)=\beta$，$P_3$ 导出 $1$，$P_4$ 查询 $L^7$ 得 absent 而导出 $0$。于是三元组 $(\beta,0,R_0)$ 出现在 $P_4$ 的扩展关系中，在 $P_3$ 的扩展关系中不可能出现，因为后者在 $h$ 回复 beta 时必导出 $1$。新增上下文另行具有读取原始导出位的合法权限，并另付一次 $h$ 查询，比较二者便可区分支持相等的两实现。此比较没有向原准备器提供免费回复。

这一反例同时证明，(VI.23) 的匹配不能要求在每个相同来源保留原始位，也不能升级成对全部新字面上下文的等价。它不反驳定理 51：将 $h$ 作为冻结指标后，任何合法正规化必须保持新增三元组，因而不能用这一 $P_4\mapsto P_3$ 替换来代表它。$\square$

命题 52 的原生域、image 逆和五个目标归 BPS §§1–2；支持相等使用 BPS Lemmas 6.3、8.2。本处 `repo-derived` 的构造把两个恒正确的原始服务入口、三状态 SOME-preparer、长一元地址和一个有代价的新增观察组合为同预算分离，不声称这类观察等价区分具有文献原创性。

## 28. 续篇Ⅵ：整族综合的有效接口与量词边界

**定义 53.1（有效有界综合接口）。** 对一个有效编码的控制实例及预算 $B$，有效有限综合所需的接口包括：可计算给出的有限动作菜单；可有效枚举的全部候选安装表，含有限终止输出选择、共同起点、全部后继及计数状态；每个候选的精确有限联合实现关系的终止计算；该关系上的可判定成功合同；以及一个证明，保证每个预算内成功原策略都具有菜单内的同预算成功代表。若要求保留某个读出关系，则代表完备性还须保留该关系，且使用相同执行解释或明确运输成本与输出。

**所用中间事实及证明。** 这些条件给终止的穷举：有限枚举每张表，精确算其联合关系并检验合同；找到者输出，全部失败则否定存在。完备性来自同预算代表，不来自“检索过很多候选”。有限表法与有界综合属于已知工具；这里需要的是原生地址无界时菜单及精确检查的实际供应者。

仅有“每个实例存在某个有限正规化菜单”不足以给统一判定。令实例为机器 $e$，动作集为自然数 $k$；一次动作成功当且仅当 $e$ 在前 $k$ 步内停机。候选检查模拟有限 $k$ 步，故处处终止；只需固定的执行—终止骨架及单次动作预算，终止输出为成功或失败。若 $e$ 首次停机于 $h$，取菜单 $\{h\}$，全部成功动作都有同预算、相同成功读出的代表；若不停止，取 $\{0\}$，成功代表条件真空成立。因此每个实例都存在这样的有限菜单，但成功策略存在性正是停机问题。缺失的是由 $e$ 统一计算该菜单的有效性，不能从存在量词取得它。相同道理，有限终止输出类型不能用未计价的任意目标程序替换。

**定理 53（原生条件连线族及资源前沿的有限综合）。** 固定定义 50.1 的全部实际原生服务条件及显式有限 $T$，给 $N,P,L$；若还固定显式有限观察表 $\mathcal H$，则下列问题均有终止的精确数学判定与综合过程：在整个 $\mathcal U_*$，或在定义 51.1 任一给定可判定条件 $C\subseteq\mathcal R^s$ 内，是否存在至多 $N$ 安装准备状态、准备至多 $P$ 调用、所选服务至多 $L$ 调用的 SOME-preparer；以及对每个有限菜单地址骨架，其全部可行连线表和精确调用成本前沿。条件域为空与 BOTH 未达到分别报告为不同的数学失败条件。

**证明。** 没有观察指标时使用 BPS Theorem 10.2 的 $D_0$；有观察指标时计算 (VI.18) 的 $D_{\mathcal H}$。前者是后者的 $s=0$ 情形。长度至多 $D$ 的字面菜单可显式构造且大小为

$$
|W_D|=\sum_{j=0}^{D}2^j=2^{D+1}-1.
\tag{VI.26}
$$

枚举有标号安装集 $\{1,\ldots,n\}$、$1\le n\le N$ 的全部 Read/Halt 分割及每个 Read 的菜单地址。对每个骨架保留整个有限 $\Theta_K$。它的表数为

$$
|\Theta_K|=n\,n^{4|Q|}\,2^{|H|};
\tag{VI.27}
$$

当 $N=0$ 候选集为空。未使用状态和重复记录仍参与这些有限选择，不改变固定服务表的任何记录。

精确关系计算使用 BPS Lemma 10.1 的共同后缀 trie 库存法，并把观察指标一并加入。具体地，枚举每个六类值的四类型及全部指标回复向量；相同类型—向量格中若要放 $j$ 个不同类值，检查其六截断容量至少为 $j$。筛选 BPS Proposition 1.4 的十一类实际 profile，重复伙伴共用同值，所有不同类保持整体不等。容量递推只作有限的和、积及截断，提供每个保留格的有限树见证；逆像 $\delta\mathscr S(x)$ 给每个保留行的同一实际来源与整个目标。必要性由实际六类值入格得出，充分性由逐格不同值选择得出，所以库存既不漏行，也不加入边缘拼凑的假行。额外观察只是增加有限回复指标，不增加实际类值数，故同一算法适用。

筛选观察条件后，先检查受限行集非空，再对每个 $\theta$ 用定义 50.2 的解释检查所有行及跨行的 BOTH 位集。Halt 在调用前即检查，最后一次允许调用的后继也立即检查；限额用尽后仍为 Read 才失败，不添加一个“终止探测”调用。只验实际选中入口的正确性和预算，不能把未选入口的失败当成否定。成功表的最大两阶段计数给其精确成本，有限表集合再取 Pareto 极小元。

可靠性由每个实际源都在库存中、每个库存行有实际源及路径解释的一致性得到。完备性由定理 50 或 51：任何原有限字面策略都有相同安装骨架、同一个起点、所有四后继、原始 Halt 位及同预算的菜单内代表；所需整个条件关系和 BOTH 亦保持。因此菜单内全失败排除原模型的所有预算内策略。$\square$

定理 53 中无观察的存在性供应者为 BPS Theorem 10.2，本处不把它重复认领为新判定定理；`repo-derived` 的推论是定理 51 的有限观察条件库存、统一连线族及成本前沿消费者。其合同是 SOME：生成某个真实达到两原始位并使固定入口正确的函数，不要求保留一个另行给出的逐来源代码。针对指定代码，有限菜单充分性、代码程序与证书有效性不能由上述过程代替；其边界见 [《原生指定代码取得》](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md) Theorem 3.2、Theorem 15.2 及 §§20–21。一个闭式有限菜单与候选逐行检查的存在，也不给出有效率的搜索或最小深度常数。

## 29. 续篇Ⅵ：量子仪器、历史分级与静态解释的边界

**定义 54.1（仪器策略的关系实现）。** 对定义 48.1 的每个实际观察历史 $h$，采用定义 41.1 的候选族 $\mathcal D_h$、支持投影 $P_h$ 及一个实际已安装的 CP 仪器 $\mathcal J_{a,b}$。一个策略树或计数状态截面必须同时满足统一动作合法性、

$$
(I-Q_{h,a,b})K_{a,b,\mu}P_h=0,
\qquad
S_{hab}=\operatorname{span}_\mu K_{a,b,\mu}S_h,
\tag{VI.28}
$$

以及实际记录、剩余预算和终止合同的更新；后式只为非空后验结果生成历史。对正迹候选，结果可达的含义是 $\operatorname{tr}\mathcal J_{a,b}(\rho)>0$。Born 权重按定义 47.1 的仪器组合计算，不能从一个可达支持集合恢复。

**中间概率边界及证明。** 即使只有一维量子端口，两个二结果仪器

$$
\mathcal J^{(p)}_0(x)=px,\quad\mathcal J^{(p)}_1(x)=(1-p)x,
\qquad 0<p<1,
\tag{VI.29}
$$

都 CP，和为恒等 TP；所有参数有相同结果可达支持 $\{0,1\}$。取 $p\ne q$，第一结果概率就不同。故一个只保留全部实际分支的策略纤维，可用于“每个实际分支都成功”的合同，但不足以运输成功概率阈值、期望成本或干涉。对连续随机控制，零质量历史与点态实际可达集合还须分开，不能将有限分支论证无条件推广为几乎处处结论。

原生定理 50–53 的有限菜单来自原生树、六类全值不等式和一元摘要稳定；一般量子门接口没有这些假设。有限 Hilbert 维数不保证候选支持或仪器参数只有有限多个，也不供应有效有限正常形。对某个量子系统使用定理 53 的综合思路，需要另外给出定义 53.1 的有效菜单、精确接口封闭和可判定联合合同；既有五模式菜单与扩大控制权限仍受命题 44、45 的分别约束。

**命题 54（计数状态运输与正历史分级相容，但不消除历史）。** 定理 50–51 保留的状态—回复轨迹允许在相同实际回复行上使用同一序号给门事件分级；它不要求一个严格增长函数定义在可能复用的有限控制节点上，也不把支持等价升级为完整事件历史同一。

**证明。** 把一次实际执行展开为历史节点 $h_0,h_1,\ldots$，每实施一次计数事件便追加一个有身份的事件，置 $\tau(h_j)=j$，或按定义 1.2 取严格正权重之和。于是每个计数追加都严格增大有限历史读数。控制投影 $h_j\mapsto k_j$ 可以合并不同历史；若控制图有一圈且每条边都要求 $\tau(k')>\tau(k)$，沿圈传递会得到 $\tau(k)>\tau(k)$，矛盾。即使成功原生运行在固定来源上不重访 Read，不同来源或未选入口的边并集仍可有圈，故严格分级须留在历史层，而不能被移到所有安装节点。

定理 50–51 以相同安装状态和回复数列匹配历史读出中的声明坐标，但准备字面可能已改变。加入字面地址、不可见环境、来源身份或更细事件身份会扩展目标，必须重新保护这些坐标。第 4 节的 $U^{-1}U=I$ 与两次历史追加也继续不同：末端算子读出相同不会删除正历史。静态关系图可以同时表示多张成功策略截面，关系存在性与截面多重性只说明声明合同的实现空间；它既不说明不相容分支同属一个配置，也不推出某种经验本体或自由意志主张。$\square$

## 追加锚（本行以下为增补区）

## 30. 零分隔编码与原生分隔位的回零门

**定义 30.1（同一排斥链中的多块编码）。** 对每个整数 $m\geq1$，取长度 $n=4m-1$ 的开放布尔链，令

$$
\mathcal K_n=\operatorname{span}\{|z_1\cdots z_n\rangle:z_jz_{j+1}=0\},
\qquad \mathcal L_m=\mathcal H_F^{\otimes m}.
\tag{30.1}
$$

第 $a$ 个数据块占位置 $4a-3,4a-2,4a-1$，第 $a$ 个分隔位为 $s_a=4a$（$1\leq a<m$）。沿用定义 43.1 的五模式，定义等距映射

$$
V_m|x_1\rangle\otimes\cdots\otimes|x_m\rangle
 =|x_1\,0\,x_2\,0\cdots0\,x_m\rangle,
\qquad x_a\in\Sigma_F,
\qquad \mathcal C_m=V_m\mathcal L_m.
\tag{30.2}
$$

编码域为 $\mathcal L_m$ 的全部复密度算子，包括块间纠缠态；链上输入为 $V_m\rho V_m^\dagger$。分隔位初始化为零是前提。编码使用 $3m$ 个数据位置、$m-1$ 个分隔位置，$\dim\mathcal C_m=5^m$。编码是端口间的数学映射，不包含未知来源的取得、编码装置的安装、路由或运输供应。

**假设 30.2（逐位置独立控制与一个固定块相位）。** 在 $\mathcal K_n$ 上，令 $P_j^0=|0\rangle\langle0|_j$、$n_j=I-P_j^0$，边界 $P_0^0=P_{n+1}^0=I$，并提供

$$
T_j=P_{j-1}^0X_jP_{j+1}^0,\qquad e^{-i\theta T_j}\quad(1\leq j\leq n,\ \theta\geq0).
\tag{30.3}
$$

位置可以独立寻址，每次仅打开所选的一项，未选项和漂移均为零。对每个数据块另外提供同一个固定相位门

$$
F_a=\exp(i\phi P_{13}^{(a)}),\qquad
P_{13}^{(a)}=n_{4a-3}n_{4a-1},\qquad \phi\in\mathbb R,\quad \sin\phi\ne0.
\tag{30.4}
$$

只要求可重复调用 $F_a$，不提供任意可调相位或其精确逆。$P_{13}$ 指块内第一、第三位置共同激活的投影；在五模式上它是 $|101\rangle\langle101|=|25\rangle\langle25|$，不同于假设 45.1 的 $|N\rangle\langle N|$。门参数是无量纲数学参数；这些独立控制、零漂移、固定相位及初始化均不由原固定总和 $K$ 菜单推出。PXP 生成元及无 $11$ 合法域沿用命题 43；其一般背景为 Turner 等，[arXiv:1806.10933v2](https://arxiv.org/html/1806.10933v2)，§§II.1–II.2。

**命题 30.3（合法编码与精确分隔回零）。** 在假设 30.2 下，每个数据位置脉冲和每个 $F_a$ 都保持 $\mathcal C_m$。在数据块 $a,a+1$ 之间，单独施加一个分隔位脉冲 $e^{-i\pi T_{s_a}}$，则

$$
e^{-i\pi T_{s_a}}V_m=V_m E_a,\qquad
E_a=I-2A_aB_{a+1},\qquad
A=P_3^0|_{\mathcal H_F},\quad B=P_1^0|_{\mathcal H_F}.
\tag{30.5}
$$

这里 $A_aB_{a+1}$ 表示两个不同逻辑块上的张量积投影，$\operatorname{rank}A=\operatorname{rank}B=3$。该脉冲终点所有分隔位精确回到零，$E_a^2=I$；途中可离开编码域，但始终留在无 $11$ 合法域。$E_a$ 是纠缠门，无须另提供跨块酉或跨块相位服务。

**证明。** 零分隔切断相邻数据块之间的 $11$ 冲突，故 (30.2) 把每个五模式张量基向量送到不同的合法链基向量，确为等距。无分隔的两个直接相邻三位窗口则没有此性质：左窗口末位和右窗口首位同时为一的四对组合被排除，合法六位字只有 $25-4=21$ 个。这是 [《原生延拓与金字塔关联》§12](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md) 已有的 $21/25$ 障碍，本编码通过显式增加并初始化一个位置规避它，不将相邻原生窗口直接视作独立端口。一般合法链维数为 $F_{n+2}=F_{4m+1}$（$F_0=0,F_1=1$），由末位零或一的递推得到；$\mathcal C_m$ 只是其中指定的 $5^m$ 维子空间。

每个 $T_j$ 仅在两邻位为零时翻转第 $j$ 位，所以它没有合法与非法基态之间的矩阵元。数据脉冲不改变分隔位；分隔位为零时，块首尾的外邻投影均为恒等，三个块内限制恰为命题 43 的 $H_1,H_2,H_3$。因此其指数保持整个编码域。$F_a$ 是对角门，也保持该域。$T_j$ 的谱含于 $\{0,1,-1\}$，故非负参数通过 $2\pi$ 周期已经给出数据脉冲的逆。

固定其余所有基位，记相邻块的接缝位为 $r,\ell$。若 $r=\ell=0$，分隔位上的生成元是 $X$，且

$$
e^{-itX}|0\rangle=\cos t\,|0\rangle-i\sin t\,|1\rangle;
\tag{30.6}
$$

若其中一位为一，生成元为零，分隔位保持零。在 $t=\pi$，前一情形得到 $-|0\rangle$，后一情形得到 $|0\rangle$，逐基向量即得 (30.5)。途中分隔位为一的分量仅在 $r=\ell=0$ 时出现，故仍无相邻激活。线性性把结论推广至任意叠加、混态及外部参考纠缠输入。

在每块选 $|\mathbf0\rangle=|000\rangle$、$|\mathbf1\rangle=|101\rangle$。$A,B$ 在这两个向量上的特征值分别为 $1,0$；$E_a$ 在其四维乘积子空间中为 $\operatorname{diag}(-1,1,1,1)$。它把 $(|\mathbf0\rangle+|\mathbf1\rangle)^{\otimes2}/2$ 送到系数矩阵

$$
\frac12\begin{pmatrix}-1&1\\1&1\end{pmatrix},
\tag{30.7}
$$

其行列式为 $-1/2$，所以输出 Schmidt 秩为二，确有纠缠。这也满足 Brylinski–Brylinski 对角门矩形相位的非可分判据，见 [*Universal quantum gates*，Proposition 2.1](https://arxiv.org/html/quant-ph/0108062v1)。这里的推导为 `repo-derived` 的指定编码、原生分隔脉冲及回零接口对应；不将受阻条件相位的一般机制认作新的通用原理。$\square$

## 31. 固定非实相位下的有限多块射影通用性

**定理 31.1（编码域上的输入无关有限字）。** 固定任意 $\phi$ 满足 $\sin\phi\ne0$，采用假设 30.2。对每个整数 $m\geq1$、每个 $U\in U(\mathcal L_m)$ 和每个 $\varepsilon>0$，存在一个有限物理脉冲字 $w=w(m,\phi,U,\varepsilon)$、一个 $|z|=1$ 及一个逻辑酉 $W$，使

$$
wV_m=V_mW,\qquad \|W-zU\|_{\rm op}<\varepsilon.
\tag{31.1}
$$

该字只由数据位置脉冲、固定块相位 $F_a$ 及命题 30.3 的完整分隔位 $\pi$ 脉冲组成。每个这种完整操作的终点全部分隔位均为零，微观过程中全链合法。字和参数不依赖未知输入态，无中途测量、后选择或其他块的经典结果。对任意有限维参考 $R$ 及任意密度算子 $\rho\in\mathsf D(\mathcal L_m\otimes R)$，同时有

$$
\left\|(W\otimes I_R)\rho(W^\dagger\otimes I_R)
 -(U\otimes I_R)\rho(U^\dagger\otimes I_R)\right\|_1<2\varepsilon.
\tag{31.2}
$$

这是任意有限块数上的近似射影通用性，不主张任意目标的精确有限综合、完整物理链 $\mathcal K_{4m-1}$ 上的通用性，或统一脉冲数、时间、能量及校准成本界。

**证明。** 先补足固定相位与命题 45 的可调相位之间的差别。只作被动坐标变换 $D$，命题 43、45 已给数据脉冲闭包 $SO(5)$；$D$ 与 $P_{13}$ 对易，所以固定相位在该帧仍为 $F=\operatorname{diag}(1,1,1,1,e^{i\phi})$。非负幂 $F^k$ 的闭包包含 $F^{-1}$：若相位为单位根，逆是一个非负幂；否则圆周紧性给正整数 $k_j\to\infty$ 满足 $F^{k_j}\to I$，从而 $F^{k_j-1}\to F^{-1}$。因此单块有限字的闭包是紧群 $G_\phi$，其 Lie 代数包含 $\mathfrak{so}(5)$ 及其 $F$ 共轭。

沿用命题 45 的矩阵单位 $E_{uv}$ 与 $J_{uv}=E_{uv}-E_{vu}$。对 $0\leq u<4$，

$$
FJ_{u4}F^{-1}
 =\cos\phi\,J_{u4}-i\sin\phi\,(E_{u4}+E_{4u}).
\tag{31.3}
$$

因 $\sin\phi\ne0$，实线性相减给 $i(E_{u4}+E_{4u})$，再用

$$
[J_{u4},i(E_{u4}+E_{4u})]=2i(E_{uu}-E_{44})
\tag{31.4}
$$

取得全部迹零虚对角方向。它们与全部 $J_{uv}$ 交换，取得所有虚对称非对角方向。故该 Lie 代数包含 $\mathfrak{su}(5)$，而 $G_\phi$ 包含 $SU(5)$，在 $PU(5)$ 中满射。这是命题 45 在本固定 $P_{13}$ 相位合同中实际使用的适配，不假定固定角能连续调节。

此处也能精确说明行列式边界。记 $C_\phi=\overline{\{e^{ik\phi}:k\in\mathbb Z\}}\subseteq U(1)$，则

$$
G_\phi=\{Q\in U(5):\det Q\in C_\phi\}.
\tag{31.5}
$$

一侧来自所有数据门行列式为一、$\det F=e^{i\phi}$。另一侧由 $SU(5)\subseteq G_\phi$ 得到：行列式映射的紧像恰为 $C_\phi$，选同一行列式的群中元素后，二者之商属于 $SU(5)$。当 $\phi/(2\pi)$ 为有理数且 $\sin\phi\ne0$，$C_\phi$ 有限，$G_\phi\ne U(5)$；例如 $\phi=\pi/2$。当该比值无理时 $C_\phi=U(1)$。两种情形的射影像都为整个 $PU(5)$，所以不能把固定非实角一概表述为全 $U(5)$ 控制。

现在在 $PU(5^m)$ 中取全部逻辑有限字的闭包 $G_m$。数据脉冲和 $E_a$ 有精确可用的逆，$F_a$ 的逆在其幂闭包中，故 $G_m$ 是群。它含每个块上的全部局部射影酉。命题 30.3 证明了相邻块门 $E_a$ 把一个乘积向量送到非乘积向量，因此它是 Brylinski–Brylinski Theorem 1.3 的 imprimitive 门；该定理的参数在这里为 $d=5$、两个独立逻辑因子 $\mathcal H_F$ 以及 $V=E_a$。由 [该文 Theorem 1.3](https://arxiv.org/html/quant-ph/0108062v1)，完整局部酉加此门通用。完整局部酉在这里属于闭包，而不是被额外提供的精确门：任选该定理给出的有限电路，把其中有限多个局部门分别作射影逼近，乘积的算子范数误差不超过各门误差之和。所以每条相邻边上的全部 $PU(25)$ 都在 $G_m$ 中。

尤其相邻逻辑 SWAP 的射影类在 $G_m$ 中。相邻交换生成任意块置换，故共轭运输给任意两个块上的 $PU(25)$，不需要另外提供物理远程门。Brylinski–Brylinski [Theorem 5.1](https://arxiv.org/html/quant-ph/0108062v1) 的中间事实是全部二 qudit 门可组成任意有限 $m$ qudit 酉；其因子在此为已编码的 $m$ 个五维端口，二块门和路由都只在上述闭包中使用。于是 $G_m=PU(5^m)$。$m=1$ 由前面的单块证明覆盖。闭包的定义给 (31.1) 的一个有限原生字；每个完整操作精确保码和回零由命题 30.3 逐次复合得到。这个论证没有把闭包中的中间门当作精确可调用门。

最后以 $zU$ 代替 $U$，对任意参考输入把两个共轭之差展开为

$$
((W-zU)\otimes I)\rho(W^\dagger\otimes I)
 +(zU\otimes I)\rho((W-zU)^\dagger\otimes I).
\tag{31.6}
$$

用 $\|AXB\|_1\leq\|A\|_{\rm op}\|X\|_1\|B\|_{\rm op}$ 及 $\|\rho\|_1=1$ 得 (31.2)。引用的通用门定理为 `literature-attested` 的中间输入；本结论的 `repo-derived` 内容是固定相位适配、单链合法编码、原生分隔回零及射影有限字量词的共同对应。该存在量词不提供有效率综合，也不供应未知源、控制器安装或可实现硬件。$\square$

## 32. 同一个第一块读口下的两种未来商

**定义 32.1（来源、已得记录与末次模式律）。** 固定 $m\geq1$、同一个源域 $X$、记录映射 $r:X\to M$ 及已达到的记录 $h$，候选纤维为 $X_h=r^{-1}(h)\ne\varnothing$。对每个 $x\in X_h$，令 $\rho_x\in\mathsf D(\mathcal L_m)$ 是该来源在同一个初始化编码、控制及末端接口上的联合态。$h$ 不被解释为免费取得 $\rho_x$。本节允许的未来字在整个纤维上共同合法，并在末端只读第一块的五模式：

$$
R_w(x)(s)=\operatorname{tr}\!\left[\rho_xW_w^\dagger(\Pi_s\otimes I)W_w\right],
\quad s\in\{N,2,3,5,25\}.
\tag{32.1}
$$

不读其他块、不取中途结果，也不向观察者提供其他块的经典输出。$\mathcal Q_{\rm loc}$ 包含任意有限的块内数据及固定相位字，只能给张量积门；$\mathcal Q_{\rm cpl}$ 再包含完整分隔 $\pi$ 脉冲。未来等价定义为同一菜单中每个有限字的完整概率律相等，正是定义 4.1、9.3 的响应商拉回到 $X_h$。这里比较全部有限字；若实际资源只允许一个真子菜单，应以那个子菜单重新取商，不能沿用下面的完整性结论。

**命题 32.2（局部边缘商与耦合联合态商）。** 在定义 32.1 的同一读口和假设 30.2 下，对任意 $x,y\in X_h$，

$$
\begin{aligned}
x\sim_{\rm loc}y
 &\Longleftrightarrow\operatorname{tr}_{2\cdots m}\rho_x
                  =\operatorname{tr}_{2\cdots m}\rho_y,\\
x\sim_{\rm cpl}y
 &\Longleftrightarrow\rho_x=\rho_y.
\end{aligned}
\tag{32.2}
$$

因此局部未来商恰保留第一块的约化态，耦合未来商恰保留此编码端口的联合密度态；它们不因此识别在 $(h,\rho_x)$ 相同的来源间仍可不同的来源身份、不可访问环境或额外关系。若 $\rho_x\ne\rho_y$，存在一个有限、输入无关的合法耦合字及一个末次第一块模式，给出严格不同的概率。

**证明。** 局部字为 $W_1\otimes\cdots\otimes W_m$，将 (32.1) 化为第一块边缘对 $W_1^\dagger\Pi_sW_1$ 的配对，其他块上的门消失。边缘相等因此充分。反向，定理 31.1 的单块部分使这些实际有限字的效果在极限中包含所有秩一投影；概率连续，所以相等的全部实际有限字概率给全部秩一投影的相等配对，进而给相等边缘。

耦合字的效果在定理 31.1 的闭包中为 $U^\dagger P U$，其中 $d=5^m$、$P=\Pi_s\otimes I$，$P$ 的秩为 $k=5^{m-1}$，且 $1\leq k<d$。其酉轨道是全部秩 $k$ 投影。令 $\Delta=\rho_x-\rho_y$。若全部实际字概率相等，连续性给 $\operatorname{tr}(\Delta Q)=0$ 对每个秩 $k$ 投影 $Q$ 成立。取 $\Delta$ 的正交特征基，任意 $k$ 个特征值之和均为零。对任意两个指标，选其余 $k-1$ 个共同指标作差，得这两个特征值相等；$k=1$ 时共同集合为空。由 $\operatorname{tr}\Delta=0$ 得 $\Delta=0$。反向由 (32.1) 立即成立。

若 $\Delta\ne0$，上述论证反向给一个秩 $k$ 投影 $Q$，使 $c=|\operatorname{tr}(\Delta Q)|>0$。选 $U$ 将 $P$ 共轭到 $Q$，再选定理 31.1 的字满足 $\|W-zU\|_{\rm op}<c/8$。由 (31.2) 和测量的迹范数收缩，对两个输入各自的该事件概率误差小于 $c/4$，故实际差仍大于 $c/2$。这把极限分离变成一个真正有限的可读延拓，没有执行极限门。

此识别是整族可选未来的概率函数识别，不是一次末读取得未知密度态。一般非正交纯态不能被一份输入上的仪器确定标成不同状态名：若某效果在 $|\psi\rangle$ 上概率一、在 $|\chi\rangle$ 上概率零，则 $E|\psi\rangle=|\psi\rangle$、$E|\chi\rangle=0$，从而 $\langle\chi|\psi\rangle=0$。例如 $|N\rangle$ 与 $(|N\rangle+|2\rangle)/\sqrt2$ 不满足该必要条件。估计一族概率还需另供重复来源与统计资源。

若另一个原接口已经允许各块独立旋转后的完整联合乘积读出，则既有产品效果张成结论已经识别联合密度态，见 [《二阶关系完成》§§64–65](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md) 及 [混态续篇 C-108](AURIC_FIB_ATOM_HIDDEN_RELATIONS_MIXED_STATE_CAPACITY_AND_CERTIFICATION.md)。此时不能说纠缠门才使联合态可识别；(32.2) 的差别专属于只输出第一块模式的同一个受限接口。本命题为该接口经定理 31.1 的 `repo-derived` 推论，不重新认领一般产品效果完备性。$\square$

## 33. 可读联合关系与内生发布响应

**命题 33.1（相同局部边缘的两块关系见证）。** 在 $m=2$ 的同一个七位编码链上，取命题 30.3 的 $|\mathbf0\rangle=|N\rangle$、$|\mathbf1\rangle=|25\rangle$，并令

$$
\begin{aligned}
\rho_{\mathrm{eq}} &= \tfrac12\bigl(|\mathbf0\mathbf0\rangle\langle\mathbf0\mathbf0|
                     +|\mathbf1\mathbf1\rangle\langle\mathbf1\mathbf1|\bigr),\\
\rho_{\mathrm{neq}} &= \tfrac12\bigl(|\mathbf0\mathbf1\rangle\langle\mathbf0\mathbf1|
                     +|\mathbf1\mathbf0\rangle\langle\mathbf1\mathbf0|\bigr).
\end{aligned}
\tag{33.1}
$$

两态在每个块的边缘都相同，但存在只用块内字、一次原生分隔 $\pi$ 脉冲及第一块末次模式读的有限延拓，使两态的 $25$ 模式概率差严格大于 $1/2$。无其他块的测量或经典结果。

**证明。** 两边缘均为 $(|\mathbf0\rangle\langle\mathbf0|+|\mathbf1\rangle\langle\mathbf1|)/2$，而两态的联合经典关系分别为相等与不等。令 $H$ 在第一块的这两个向量上是 Hadamard，其他三个模式上为恒等。对 (30.5) 的 $E=E_1$，理想酉

$$
U_*=(H\otimes I)E(H\otimes I)
\tag{33.2}
$$

在第二块为 $\mathbf0$ 时对第一块施加 $-X$，第二块为 $\mathbf1$ 时施加恒等。因此它把相等关系的第一块确定送到 $\mathbf1$，不等关系的第一块确定送到 $\mathbf0$；理想 $25$ 概率分别为一和零。

取任意 $0<\delta<1/8$，由定理 31.1 的单块部分选有限局部字 $L$ 及 $|z|=1$ 使 $\|L-zH\|_{\rm op}<\delta$。实际字为 $(L\otimes I)E(L\otimes I)$，与 $z^2U_*$ 的算子范数距离小于 $2\delta$。由 (31.2) 的同一展开及测量收缩，两输入的各自事件概率误差小于 $2\delta$，所以实际概率差大于 $1-4\delta>1/2$。$E$ 由一个完整分隔脉冲精确实现，两个 $L$ 均保持分隔零，故全过程合法、末端回零。此见证把已有边缘不足的关系落实为本链上无旁支读数的有限可读延拓，而不是新增自由联合观察假设。$\square$

**定义 33.2（同一记录纤维上的发布响应）。** 保留定义 32.1 的 $X,r,h$。另明确一个公布值空间 $Y$、每个来源允许公布的集合 $\Lambda_x\subseteq Y$，以及实际公布 $p$ 后的确定目标响应 $F_x(p)$；如果预测对象是概率律，则 $Y$ 和 $F_x(p)$ 都取该概率律类型。$F_x$ 由来源、所公布的值及公布后的合法续接共同决定，不把公布前的概率响应当作公布后仍不变。记录选择器只能公布 $p=f(h)$。在此纤维上合法且处处正确的公布值必须且只须属于

$$
\mathcal P_h=\bigcap_{x\in X_h}\{p\in\Lambda_x:F_x(p)=p\}.
\tag{33.3}
$$

该式复用定义 40.1 的共同合法动作条件和定义 4.1 的来源纤维因子化：同一已得记录对应同一公布值，响应则保持其实际来源与公布值的双重指标。

**命题 33.3（合法耦合通用性不保证自预测不动点）。** 定理 31.1 和命题 32.2 不推出 (33.3) 非空。即使只有一个已知编码来源、公布后只使用本控制合同中的精确合法动作和同一个第一块模式读口，也可以没有共同正确公布值。

**证明。** 对任意 $m\geq1$，取候选纤维只有一个来源 $x$，其第一块为 $|N\rangle=|000\rangle$，其他块为任意固定编码态，分隔为零。公布字母为 $Y=\{0,1\}$，两值都合法。公布后，固定控制器在 $p=0$ 时施加第一数据位置的 $e^{-i\pi T_1/2}$，在 $p=1$ 时不施加数据门，随后都读第一块模式。把实际结果 $2$ 记为一、其余模式记为零；在本来源上只有 $N,2$ 会出现。命题 43 给第一分支确定输出 $2$、第二分支确定输出 $N$，所以

$$
F_x(0)=1,\qquad F_x(1)=0,\qquad \mathcal P_h=\varnothing.
\tag{33.4}
$$

这只是一个已声明初态与公布反馈规则的数学实例，没有推断实际源可被免费准备。它已满足控制前提，并与有限块通用性相容，故反驳由该通用性推出共同不动点的蕴含。反之，若另一个实际发布规则使 (33.3) 非空，其中的值才给该纤维的正确公布；门程序存在、未来概率分离及一次末读取得预测值是不同量词。命题 33.1 的两态若仍在同一个记录纤维中，局部未来相同也不能抹掉它们在耦合延拓下的响应差，须保留实际来源、已得记录与所选择延拓的对应。$\square$

## 34. 六结果联合读出的编码消费者

**假设 34.4（此消费者的末端产品读口）。** 本节在 $m=2$ 编码和假设 30.2 之外，另允许末端分别读两个逻辑块的模式，把两个实际结果共同写入经典记录，再作固定结果合并。没有中途测量；本权限独立于定义 32.1 的仅第一块读口，不能用于该节的观察者比较。采用 [《复合通信与校准》C-116.1、(C121.4)、C-125.3 及§126](AURIC_FIB_ATOM_HIDDEN_RELATIONS_COMPOUND_COMMUNICATION_AND_CALIBRATION.md) 的原端口标识 $|B_j\rangle_A,|f(B_j)\rangle_B$，$0\leq j\leq4$。令 $e_j$ 依次为本卷五模式，声明端口识别

$$
C_A|B_j\rangle_A=e_j,\qquad C_B|f(B_j)\rangle_B=e_j,
\qquad C=C_A\otimes C_B.
\tag{34.5}
$$

原联合输入 $\sigma$ 的数学编码为 $V_2C\sigma C^\dagger V_2^\dagger$。这里分别假设输入和该编码已供应，不从原匹配子空间的等距 $J$ 推出它们，也不供应 C-121 的批量源、通道控制、校准或完整处理器。

**命题 34.2（保留秩二十补空间的近似经典输出测量）。** 在假设 34.4 下，对每个 $\varepsilon>0$，存在一个与未知输入无关的有限合法脉冲字及固定末端合并，实现一个六结果经典输出通道 $\mathcal M_\varepsilon$，逼近原 (C121.4) 的六结果 PVM 经典输出通道 $\mathcal M$。对任意有限参考 $R$ 和任意原端口联合输入 $\sigma\in\mathsf D(A\otimes B\otimes R)$，

$$
\left\|[(\mathcal M_\varepsilon-\mathcal M)\otimes\operatorname{id}_R](\sigma)\right\|_1<2\varepsilon,
\qquad \|\mathcal M_\varepsilon-\mathcal M\|_\diamond\leq2\varepsilon,
\tag{34.6}
$$

从而全部六结果分布的总变差小于 $\varepsilon$，包括与参考上任意后续测量所得结果的联合分布。补结果 $*$ 保留；对原 $\rho_{t,\eta}(X)$，其概率与 $20\eta/25$ 的差小于 $\varepsilon$。结论只逼近经典输出测量，不断言实现保留补空间相干的粗粒 Lüders 仪器。

**证明。** 由原定义 $Je_j=|B_j,f(B_j)\rangle$，有 $CJe_j=|jj\rangle$。原五个秩一 PVM 向量在编码逻辑坐标中为

$$
\widehat a_\pm=(|00\rangle\mp i|44\rangle)/\sqrt2,\quad
\widehat b_\pm=(|11\rangle\mp i|33\rangle)/\sqrt2,\quad
\widehat o=|22\rangle.
\tag{34.7}
$$

它们是五个正交归一向量，按 $a_+,a_-,b_+,b_-,o$ 排列为 $v_0,\ldots,v_4$；补投影 $\widehat Q=I-\sum_{j=0}^4|v_j\rangle\langle v_j|$ 的秩为二十。把这五向量补成整个二十五维空间的一组正交归一基 $v_0,\ldots,v_{24}$，选酉 $U_0$ 将 $v_j$ 送到 $|j,0\rangle$，其余二十个基向量送到第二指标不为零的二十个产品基向量。于是先施加 $U_0$ 再产品读出，把 $(j,0)$ 记为第 $j$ 个结果，所有 $(j,k)$、$k\ne0$ 记为 $*$，恰给全部六个原投影的概率。

用定理 31.1 选有限字 $W$ 射影逼近 $U_0$，误差小于 $\varepsilon$。它作用于整个 $25$ 维编码逻辑域，故没有限制输入只在匹配子空间。对任意参考先用 (31.2)，再用产品测量、结果合并及丢弃量子输出组成的 CPTP 映射的迹范数收缩，得 (34.6) 第一式及统一 $2\varepsilon$ 通道界。这里完全有界迹范数的估计也直接来自 (31.6) 对任意迹类算子的同一个 $2\varepsilon$ 上界，故给所写 diamond 界，而非仅无参考态的估计。经典输出的迹范数为分布 $\ell^1$ 距离，除以二得总变差界；参考后续测量再用收缩即可。原 (C121.5) 的 $*$ 概率为 $20\eta/25$，单事件误差受总变差控制，所以得到补结果界，未丢弃 $\eta>0$ 的质量。

最后，产品细读后合并二十个结果会在所选补空间基上去相干。即使随后再施加 $U_0^\dagger$，对逻辑输入 $\tau=C\sigma C^\dagger$ 的该分支也是 $\sum_{\ell=5}^{24}|v_\ell\rangle\langle v_\ell|\tau|v_\ell\rangle\langle v_\ell|$，一般不等于 $\widehat Q\tau\widehat Q$；例如 $(v_5+v_6)/\sqrt2$ 的纯态相干项被前者删去。因而经典输出近似不供应粗粒 Lüders 后态。此消费者是 C-125.3 / §126 所缺联合控制接口在本零分隔合同下的 `repo-derived` 补足，额外只声明末端产品读口和输入编码，不把控制对应升级为原来源制备或完整物理供应。$\square$

## 追加锚（本行以下为增补区）

## 35. 交替位置编码与单处固定相位

**定义 55.1（合法开链与固定复线性编码）。** 对每个整数 $n\geq0$，令 $\Sigma_n$ 为长度 $n$、不含相邻 $11$ 的布尔字集，并沿用定义 30.1 的合法空间记号

$$
\mathcal K_n=\operatorname{span}_{\mathbb C}\{|x\rangle:x\in\Sigma_n\},
\qquad \mathcal K_0=\mathbb C,\qquad
d_n=\dim\mathcal K_n=F_{n+2},
\qquad F_0=0,\quad F_1=1.
\tag{VII.1}
$$

维数公式由 $d_0=1,d_1=2$ 及末位分解 $d_n=d_{n-1}+d_{n-2}$ 得到。对每个 $k\geq2$，置 $N=2k-1$、$\mathcal L_k^{\mathrm{alt}}=(\mathbb C^2)^{\otimes k}$，固定复线性等距

$$
\iota_k|b_1\cdots b_k\rangle
 =|b_1\,0\,b_2\,0\,\cdots\,0\,b_k\rangle,\qquad
\mathcal C_k^{\mathrm{alt}}=\operatorname{ran}\iota_k,\qquad
P_k^{\mathrm{alt}}=\iota_k\iota_k^\dagger.
\tag{VII.2}
$$

每个基像合法且各不相同，故此映射确为等距。本编码与定义 30.1 的五维块编码是不同的指定子空间；其偶位置为已供应的零，不是从未知输入中取得的观察结果。允许的编码输入为整个 $\mathsf D(\mathcal L_k^{\mathrm{alt}}\otimes R)$，其中 $R$ 是任意有限维被动参考；不要求逻辑位之间或它们与 $R$ 之间乘积分离。

**假设 55.2（无漂移的逐位菜单与同址复用）。** 令 $P_j^0=|0\rangle\langle0|_j$、$n_j=I-P_j^0$，开边界为 $P_0^0=P_{n+1}^0=I$。在整个 $\mathcal K_n$ 上提供独立控制

$$
H_j^{(n)}=\left.P_{j-1}^0X_jP_{j+1}^0\right|_{\mathcal K_n},
\qquad e^{-itH_j^{(n)}},\quad 1\leq j\leq n,\quad t\in\mathbb R.
\tag{VII.3}
$$

一次仅开启所选控制，其余驱动及漂移均为零；允许任意有限串行字及空字。每个 $H_j^{(n)}$ 是互不相交的二态翻转块和零块之直和，谱含于 $\{-1,0,1\}$，所以只允许非负参数也给同一菜单，逆可由 $2\pi$ 周期取得。这是命题 43 的 PXP 限制在一般开链上的独立控制合同；原固定总和 $K$ 的等待菜单不供应该权限。

当 $n\geq3$ 时，再只安装一个固定门

$$
S_{\star,n}=\exp\!\left(\frac{i\pi}{2}n_1n_3\right),
\qquad S_{\star,n}^4=I,\qquad
S_{\star,n}^{-1}=S_{\star,n}^3.
\tag{VII.4}
$$

同一个物理位置对 $(1,3)$ 可以反复调用；不提供其他位置的相位安装，也不提供连续可调相位。对每个 $n\geq1$，记 $\mathcal V_n$ 为纯翻转有限字集；对 $n\geq3$，记 $\mathcal W_n$ 为再允许 $S_{\star,n}$ 的有限字集。两者均含空字和每个字的逆。字及参数可以依赖尺寸、目标和精度，不能依赖未知输入或参考态。综合过程中不使用测量、后选择、额外量子旁路或可访问参考。每个翻转只连接两个合法字，对角相位也保持合法域，故包括脉冲中途在内始终没有到非法域的泄漏。

本合同是无量纲参数下的理想数学菜单。输入及编码初始化的供应是前提；不包含其免费取得、硬件供应、容错或任何综合成本界。

**命题 55.3（窗口隔离、相邻交换与第一窗口接口）。** 采用定义 55.1 和假设 55.2。对 $1\leq a<k$，允许窗口 $(2a-1,2a,2a+1)$ 取任意五模式，所有其他偶位置仍为零、所有其他奇位置任意，所得子空间记为 $\mathcal M_a$。则

$$
\mathcal M_a\simeq\mathcal K_3\otimes
                    (\mathbb C^2)^{\otimes(k-2)}.
\tag{VII.5}
$$

窗口内三个控制保持 $\mathcal M_a$，在此识别下分别为命题 43 的 $H_1,H_2,H_3$ 张量恒等。因此对每个 $\delta>0$，相邻逻辑交换 $\operatorname{SWAP}_{a,a+1}$ 有一个仅用该窗口翻转的有限字 $A$ 满足

$$
\|A\iota_k-\iota_k\operatorname{SWAP}_{a,a+1}\|_{\mathrm{op}}<\delta.
\tag{VII.6}
$$

第一窗口还满足：对每个 $Q\in U(4)$ 和每个 $\delta>0$，存在仅用该窗口翻转及 $S_{\star,N}$ 的有限字 $B$，使

$$
\|B\iota_k-\iota_k(Q\otimes I_{2^{k-2}})\|_{\mathrm{op}}<\delta.
\tag{VII.7}
$$

这里的 $Q$ 按第一、第二逻辑位的固定输入顺序作用，包含其指定的整体标量。

**证明。** 窗口外邻位 $2a-2,2a+2$ 为零，或在开边界缺席；故窗口首尾控制的外邻投影恒为一。窗口外奇位与窗口之间仍隔着零，任意五模式与这些奇位的组合都合法；三个控制也不改变窗口外任何位。逐基向量得到 (VII.5) 及张量限制，线性性使其同时覆盖任意相干输入和参考纠缠，而非仅覆盖已知外位取值。

在基序 $000,100,010,001,101$ 上，令 $T$ 交换 $100,001$，固定 $000,101$，并把 $010$ 取负。交换的行列式为负，辅助方向的负号再给一个负号，故 $\det T=1$。它为实正交矩阵，且与命题 45 的 $D_3=\operatorname{diag}(1,i,i,i,1)$ 对易。因此

$$
T\in D_3SO(5)D_3^\dagger,\qquad
T\iota_2=\iota_2\operatorname{SWAP}.
\tag{VII.8}
$$

复用命题 45 的翻转闭包结论，在完整五维窗口上以算子范数逼近 $T$，再张量恒等及限制到 $\iota_k$，得 (VII.6)。这不把闭包中的 $T$ 当作精确有限原生门。

在第一窗口，(VII.4) 恰为 $|101\rangle$ 上的固定 $i$ 相位。定理 31.1 证明的单块部分在 $\phi=\pi/2$ 时已给出此窗口字闭包包含 $SU(5)$，这里直接复用该结论。令 $\mathcal B=\operatorname{ran}\iota_2=\operatorname{span}\{000,100,001,101\}$；对指定 $Q$ 取整个五维上的扩张

$$
\widehat Q
 =\iota_2Q\iota_2^\dagger+
       (\det Q)^{-1}|010\rangle\langle010|.
\tag{VII.9}
$$

两项作用于正交补空间，故 $\widehat Q$ 为酉且行列式为一。逼近 $\widehat Q$ 再用第一窗口的 (VII.5)，得到 (VII.7)。补方向承担行列式，逻辑端的标量无需舍弃。$\square$

## 36. 一处安装上的任意有限逻辑位控制

**定理 56.1（交替码的普通算子范数通用性）。** 对每个 $k\geq2$、每个 $U\in U(\mathcal L_k^{\mathrm{alt}})$ 及每个 $\varepsilon>0$，在假设 55.2 的同一个物理安装下存在有限字 $W\in\mathcal W_{2k-1}$，使

$$
\|W\iota_k-\iota_kU\|_{\mathrm{op}}<\varepsilon.
\tag{VII.10}
$$

这个字对全部编码输入共同有效，无须在 (VII.10) 外另加整体相位。设 $R$ 是任意有限参考，$\rho\in\mathsf D(\mathcal L_k^{\mathrm{alt}}\otimes R)$，记实际及理想输出为

$$
\begin{aligned}
\omega_W&=(W\iota_k\otimes I_R)\rho
                       (W\iota_k\otimes I_R)^\dagger,\\
\omega_U&=(\iota_kU\otimes I_R)\rho
                       (\iota_kU\otimes I_R)^\dagger .
\end{aligned}
\tag{VII.11}
$$

同一个 $W$ 同时满足

$$
\|\omega_W-\omega_U\|_1<2\varepsilon,\qquad
\operatorname{tr}\!\left[
 ((I_{\mathcal K_N}-P_k^{\mathrm{alt}})\otimes I_R)\omega_W
 \right]<\varepsilon^2.
\tag{VII.12}
$$

第二项是实际物理输出离开交替码的概率；离开整个合法域的概率始终为零。结论不要求近似字的中间终点精确回到交替码，也不声称任意目标可精确有限综合或具有统一高效的脉冲数、时间及精度成本。

**证明。** 标准有限门分解作为中间输入：Barenco 等，*Elementary gates for quantum computation*，[arXiv:quant-ph/9503016v1](https://arxiv.org/html/quant-ph/9503016v1)，§8 的一般门构造，给任意 $U(2^k)$ 一个不使用额外工作位的精确有限二比特门分解。这里只使用该有限存在结论，不重复其分解，也不把它的二比特门计数当作本原生菜单的脉冲复杂度。若采用其单比特门加 XOR 表述，$k\geq2$ 允许把每个单比特门与另一个逻辑位上的恒等合为一个二比特门。

相邻逻辑交换生成任意逻辑位排列，故对分解中的每个有序逻辑位对，先用一个有限相邻交换序列将其依序送到第一、第二逻辑位置，在第一窗口作用指定二比特门，再作逆排列。所有相位调用始终位于物理位置 $(1,3)$；被路由的是逻辑数据。把全部这些理想操作展开为有限逻辑序列 $g_1,\ldots,g_L$，有 $g_L\cdots g_1=U$。各项或为相邻交换，或为第一逻辑位对上的指定 $U(4)$。取正数 $\delta_j$ 满足 $\sum_j\delta_j<\varepsilon$，用命题 55.3 分别选实际全链酉字 $A_j$，使

$$
\|A_j\iota_k-\iota_kg_j\|_{\mathrm{op}}<\delta_j.
\tag{VII.13}
$$

置 $W=A_L\cdots A_1$。无需假定实际近似前缀保码，精确的混合望远镜恒等式为

$$
\begin{aligned}
W\iota_k-\iota_kg_L\cdots g_1
 =\sum_{j=1}^L A_L\cdots A_{j+1}
 (A_j\iota_k-\iota_kg_j)g_{j-1}\cdots g_1 .
\end{aligned}
\tag{VII.14}
$$

空前缀或后缀取恒等。右侧理想前缀始终作用于逻辑域，实际后缀只用全合法域上的酉性，故算子范数小于 $\sum_j\delta_j$。特别地，前一窗口近似残留在辅助方向的振幅不需要被下一窗口精确清除。若 $U=I$，亦可直接取空字。这证明 (VII.10) 及输入无关性。

令 $A=W\iota_k$、$B=\iota_kU$，二者均为等距。张量 $I_R$ 不改变 $\|A-B\|_{\mathrm{op}}$；使用

$$
\begin{aligned}
\omega_W-\omega_U
 &=((A-B)\otimes I_R)\rho(A^\dagger\otimes I_R)\\
 &\quad +(B\otimes I_R)\rho((A-B)^\dagger\otimes I_R)
\end{aligned}
\tag{VII.15}
$$

及迹范数乘积界，得到第一项 (VII.12)。又因 $(I-P_k^{\mathrm{alt}})B=0$，

$$
\|(I-P_k^{\mathrm{alt}})A\|_{\mathrm{op}}
 \leq\|A-B\|_{\mathrm{op}}<\varepsilon.
\tag{VII.16}
$$

把左侧算子张量参考恒等，其平方为泄漏概率的统一上界，得第二项。窗口的精确合法性由假设 55.2 与命题 55.3 保证。本推导增加的是指定交替码上的同址相位复用、行列式补偿及泄漏容许下的有限字组合，不重新认领标准门分解或定理 31.1 的局部相位论证。$\square$

## 37. 同一复线性编码的零相位精确距离

**定理 57.1（翻转菜单的尖锐射影障碍）。** 固定 $k\geq2$ 及定义 55.1 的同一个复线性编码。按逻辑计算基的固定顺序，令 $U_\diamond=\operatorname{diag}(1,i,1,\ldots,1)$。只允许假设 55.2 的翻转字，不使用任何相位安装，则

$$
\inf_{\substack{V\in\mathcal V_{2k-1}\\ \alpha\in\mathbb R}}
 \|e^{i\alpha}V\iota_k-\iota_kU_\diamond\|_{\mathrm{op}}
 =\sqrt{\,2-\sqrt2\,}.
\tag{VII.17}
$$

把 $\mathcal V_{2k-1}$ 换成其算子范数闭包也得到同一个等式。允许 $V$ 在交替码外产生合法振幅，不能降低该界。

**证明。** 对整个 $\mathcal K_n$ 定义被动对角标架

$$
D_n|x\rangle=
 \begin{cases}
 |x\rangle,&|x|\text{ 为偶数},\\
 i|x\rangle,&|x|\text{ 为奇数},
 \end{cases}
\qquad
A_j^{(n)}=D_n^\dagger(-iH_j^{(n)})D_n,
\tag{VII.18}
$$

其中 $|x|$ 是 Hamming 重量。每条翻转边连接相反奇偶性，故 $A_j^{(n)}$ 是实反对称矩阵。每个翻转字及其极限均为 $V=D_nRD_n^\dagger$，其中 $R\in SO(d_n)$；特别地 $V_{xx}=R_{xx}\in[-1,1]$。$D_n$ 只改变坐标，不是可调用的门。

取 $U_\diamond$ 的相位分别为 $1,i$ 的两个编码基像 $|x\rangle,|y\rangle$。全输出列范数满足

$$
\begin{aligned}
\|e^{i\alpha}V|x\rangle-|x\rangle\|^2
 &=2-2R_{xx}\cos\alpha\geq2-2|\cos\alpha|,\\
\|e^{i\alpha}V|y\rangle-i|y\rangle\|^2
 &=2-2R_{yy}\sin\alpha\geq2-2|\sin\alpha|.
\end{aligned}
\tag{VII.19}
$$

这些是整个 $\mathcal K_N$ 中的列距离，未投影掉码外分量。算子范数平方不小于两列下界的最大值；$\min(|\cos\alpha|,|\sin\alpha|)\leq1/\sqrt2$，所以该最大值至少为 $2-\sqrt2$。另一方面，取空字 $V=I$ 和 $\alpha=\pi/4$，所有目标对角元为 $1$ 或 $i$，故

$$
\|e^{i\pi/4}\iota_k-\iota_kU_\diamond\|_{\mathrm{op}}
 =\max\{|e^{i\pi/4}-1|,\ |e^{i\pi/4}-i|\}
 =\sqrt{2-\sqrt2}.
\tag{VII.20}
$$

上下界相合，且上界已由有限字取得，闭包不改变结论。$\square$

**推论 57.2（固定编码菜单内的零处与一处）。** 对每个 $k\geq2$，在假设 55.2 的独立翻转、固定复线性编码和相干酉综合资源次序内，实现任意逻辑酉的任意精度逼近所需的可重复非实相位安装数最小为一。

**证明。** 零处时，即使忽略整体相位，(VII.17) 也排除通用性；一处时定理 56.1 已足够。计数对象是物理相位安装，不是调用次数；一处安装作用于位置对 $(1,3)$，并非一个单位置相位算子。此最小性不量化改变编码、实化编码、测量辅助、后选择或新增复 Hamiltonian 的其他模型，也不涵盖没有该位置对的 $k=1$。$\square$

## 38. 整个合法开链空间的控制闭包

**定理 58.1（全尺寸翻转代数与同一相位的精确行列式类）。** 对假设 55.2 中每个 $n\geq1$，使用 (VII.18) 的标架，有

$$
\operatorname{Lie}_{\mathbb R}\{A_1^{(n)},\ldots,A_n^{(n)}\}
 =\mathfrak{so}(d_n),\qquad
\overline{\mathcal V_n}=D_nSO(d_n)D_n^\dagger.
\tag{VII.21}
$$

对每个 $n\geq3$，只加入原来同一处固定相位 (VII.4)，令

$$
r_n=\operatorname{rank}(n_1n_3|_{\mathcal K_n})=F_{n-2},
\qquad C_n=\langle i^{r_n}\rangle\subseteq U(1).
\tag{VII.22}
$$

则整个合法空间上的算子范数闭包恰为

$$
\overline{\mathcal W_n}
 =\{Q\in U(d_n):\det Q\in C_n\},\qquad
SU(d_n)\subseteq\overline{\mathcal W_n},\qquad
[\overline{\mathcal W_n}]=PU(d_n).
\tag{VII.23}
$$

方括号表示除去整体相位的像。特别地，对每个 $U\in U(\mathcal K_n)$ 和每个 $\varepsilon>0$，存在 $|z|=1$ 及一个输入无关有限字 $W\in\mathcal W_n$，使

$$
\|W-zU\|_{\mathrm{op}}<\varepsilon;
\quad U\in SU(d_n)\text{ 时可以取 }z=1.
\tag{VII.24}
$$

本结论作用于全部 $F_{n+2}$ 维合法空间，既不限制为交替码，也不要求分隔位初始化。对任意合法输入及任意有限被动参考，实际输出与目标酉通道的输出迹范数距离小于 $2\varepsilon$，全过程到非法域的泄漏精确为零。$C_n$ 是有限群，故字面上的 $U(d_n)$ 稠密性不成立。

**证明。** 先证明 (VII.21) 的 Lie 代数等式。由 (VII.18)，生成代数 $\mathfrak g_n$ 包含于 $\mathfrak{so}(d_n)$。$n=1$ 的唯一控制给 $\mathfrak{so}(2)$；$n=2$ 在基序 $00,10,01$ 上给两个坐标旋转 $J_{00,10},J_{00,01}$，其括号给第三个方向，故为 $\mathfrak{so}(3)$。这里及下文 $J_{pq}=E_{pq}-E_{qp}$。$n=3$ 正是命题 45 已有的 $\mathfrak{so}(5)$，不另行重证。

现设 $n\geq4$，归纳已知长度 $n-1$ 的结论。按同一实际链的末位分解

$$
\begin{aligned}
\mathcal K_n&=\mathcal A\oplus\mathcal B,\\
\mathcal A&=\operatorname{span}\{|x0\rangle:x\in\Sigma_{n-1}\},
 &a&=d_{n-1},\\
\mathcal B&=\operatorname{span}\{|u01\rangle:u\in\Sigma_{n-2}\},
 &b&=d_{n-2}.
\end{aligned}
\tag{VII.25}
$$

前 $n-1$ 个控制保持两个分支，在 $\mathcal A$ 上的限制恰为长度 $n-1$ 的控制及其标架。它们在 $\mathcal B$ 上的限制仍实反对称，但不预设两个分支可以独立控制。令 $\mathfrak l$ 为这些分块对角生成元的 Lie 代数，则归纳假设给 $\pi_{\mathcal A}(\mathfrak l)=\mathfrak{so}(a)$。置

$$
\mathfrak k=\{X\in\mathfrak{so}(a):
                    \operatorname{diag}(X,0)\in\mathfrak l\}.
\tag{VII.26}
$$

这是 $\mathfrak{so}(a)$ 的理想：给 $Y\in\mathfrak{so}(a)$，取其提升 $\operatorname{diag}(Y,Z)\in\mathfrak l$，与 $\operatorname{diag}(X,0)$ 交换即得 $\operatorname{diag}([Y,X],0)$。第 $n-1$ 个控制在 $\mathcal B$ 上被末位的一阻断，而其 $\mathcal A$ 分量是 $B=A_m^{(m)}$、$m=n-1$，所以 $B\in\mathfrak k$。

以下直接从这个种子取得整个理想，不用简单 Lie 代数分类。在长度 $m$ 的合法基中取

$$
p=0^m,\qquad q=0^{m-1}1,\qquad
r=0^{m-2}10.
\tag{VII.27}
$$

末位控制 $B$ 在 $p,q$ 上是 $J_{pq}$，在 $r$ 的行列上均为零，其余翻转块与这些指标不交。因此

$$
[J_{rp},B]=J_{rq}\in\mathfrak k.
\tag{VII.28}
$$

对任意其他指标 $x$，理想性质给 $[J_{xr},J_{rq}]=J_{xq}\in\mathfrak k$；再用 $[J_{xq},J_{qy}]=J_{xy}$ 得到所有坐标旋转。于是 $\mathfrak k=\mathfrak{so}(a)$，从而

$$
\mathfrak{so}(a)\oplus0\subseteq\mathfrak l\subseteq\mathfrak g_n.
\tag{VII.29}
$$

这一步证明了所需的分支独立性，而没有从第一投影满射直接假定它。

最后一个控制在 (VII.25) 的分块形式为

$$
A_n^{(n)}=\mathcal J(M),\qquad
\mathcal J(C)=
 \begin{pmatrix}0&C\\-C^{\mathsf T}&0\end{pmatrix}.
\tag{VII.30}
$$

每个 $\mathcal B$ 基态 $|u01\rangle$ 恰与 $\mathcal A$ 基态 $|u00\rangle$ 配对。因此 $M$ 的列 $u$ 仅在互异行 $p(u)=u00$ 上有系数 $\sigma_u=(-1)^{|u|}$。特别地，$\mathcal A$ 中合法态 $r_0=0^{n-2}10$ 对应一个零行。对任意 $X\in\mathfrak{so}(a)$，

$$
[\operatorname{diag}(X,0),\mathcal J(M)]=\mathcal J(XM).
\tag{VII.31}
$$

分别取 $X=J_{r_0,p(u)}$，零行及匹配结构使

$$
J_{r_0,p(u)}M=\sigma_u e_{r_0}e_u^{\mathsf T}.
\tag{VII.32}
$$

由 (VII.29)–(VII.32) 得 $\mathcal J(e_{r_0}e_u^{\mathsf T})\in\mathfrak g_n$。再与 $\operatorname{diag}(J_{x,r_0},0)$ 交换，得到每个 $\mathcal J(e_xe_u^{\mathsf T})$，故全部跨分支矩形方向都已取得。对 $u\ne v$，

$$
[\mathcal J(e_xe_u^{\mathsf T}),\mathcal J(e_xe_v^{\mathsf T})]
 =\operatorname{diag}(0,-J_{uv}).
\tag{VII.33}
$$

这给整个 $0\oplus\mathfrak{so}(b)$。它与 (VII.29) 及全部跨分支方向共同张成 $\mathfrak{so}(a+b)$，归纳闭合。

乘积极限与交换子极限沿用命题 45 的论证；每个所需逆都在有限菜单中。它们把上述 Lie 括号和实线性组合的指数放入翻转字闭包，全部平面旋转又生成 $SO(d_n)$。反向包含由每个 $A_j^{(n)}$ 实反对称立即成立，得 (VII.21)。此全尺寸归纳不以有限尺寸的矩阵秩或数值外推为前提。

现在加入 (VII.4)。投影 $P=n_1n_3|_{\mathcal K_n}$ 非零且非恒等：$101$ 延拓给前者，$0^n$ 给后者。$n=3$ 时秩为一；$n\geq4$ 时强制前缀 $1010$，余下任意合法长度 $n-4$ 尾链，所以秩为 $d_{n-4}=F_{n-2}$，得到 (VII.22)。$S_{\star,n}$ 与 $D_n$ 对易，在 $P$ 的像上为 $i$、在核上为一。

在此被动标架中取闭群的 Lie 代数 $\mathfrak h$。由 (VII.21)，$\mathfrak h$ 包含全部 $J_{pq}$；它也在 $S_{\star,n}$ 共轭下不变。对满足 $|p\rangle\in\operatorname{ran}P$、$|q\rangle\in\ker P$ 的计算基指标，

$$
\begin{aligned}
S_{\star,n}J_{pq}S_{\star,n}^{-1}
 &=i(E_{pq}+E_{qp}),\\
[J_{pq},i(E_{pq}+E_{qp})]
 &=2i(E_{pp}-E_{qq}).
\end{aligned}
\tag{VII.34}
$$

两非空指标集之间的完全二分图连通，故这些对角差张成全部迹零虚对角矩阵。再与全部 $J_{uv}$ 交换，得到所有 $i(E_{uv}+E_{vu})$。它们与实反对称部分共同张成 $\mathfrak{su}(d_n)$，所以闭群包含 $SU(d_n)$。

每个翻转生成元迹零，翻转脉冲行列式为一，而 $\det S_{\star,n}=i^{r_n}$，故全部字及其极限的行列式均在有限群 $C_n$ 中。反之，任意 $Q$ 若行列式在 $C_n$，可取整数 $s$ 使 $\det Q=\det S_{\star,n}^s$，于是 $QS_{\star,n}^{-s}\in SU(d_n)$；两因子均在闭群中。这证明 (VII.23)，不把一个固定角替换成连续相位权限。$D_nSU(d_n)D_n^\dagger=SU(d_n)$，所以该等式也在原坐标成立。

对给定 $U$ 选 $z$ 满足 $z^{d_n}\det U=1$，则 $zU\in SU(d_n)$，闭包定义给 (VII.24) 的一个有限字。若 $\det U=1$，取 $z=1$。对任意参考输入，用 (VII.15) 的同一两项展开，其中 $A=W$、$B=zU$，得迹范数界；$z$ 在通道中消去。原生脉冲及相位都保持整个 $\mathcal K_n$，故合法域泄漏为零。另一方面，$\operatorname{diag}(e^{i\pi/4},1,\ldots,1)$ 的行列式不在 $C_n\subseteq\{1,i,-1,-i\}$，由行列式连续性，它不在该闭包中，字面 $U(d_n)$ 稠密性因此被排除。

取 $n=2k-1$，本定理处理的是整个 $F_{2k+1}$ 维合法链，回答了区别于 $2^k$ 维交替码的全空间控制问题。编码定理 56.1 的无附加相位结论与这里的行列式限制相容：其目标只固定码上的作用，辅助方向可补偿行列式。本定理是同一独立菜单上的全链推导；不从 PXP 背景文献、编码空间通用性或小尺寸结论直接推断全链控制，也不据此主张文献原创性、有效率综合或物理资源供应。$\square$

## 39. 全合法链的第一位置二值未来商

**命题 59.1（同一二值读口的全链概率识别）。** 固定 $n\geq3$ 及假设 55.2 的菜单。沿用定义 32.1 的实际来源域、已得记录 $h$ 及非空候选纤维 $X_h$，但现在每个来源给整个合法链上的态 $\rho_x\in\mathsf D(\mathcal K_n)$。另明确允许末次只读第一物理位置的二值 PVM $\{n_1,I-n_1\}$，无其他位置的经典输出。令

$$
R_w(x)=\operatorname{tr}(\rho_xw^\dagger n_1w),
\qquad w\in\mathcal W_n.
\tag{VII.35}
$$

比较的是全部有限字的完整二值概率律，则

$$
\bigl[\forall w\in\mathcal W_n,\ R_w(x)=R_w(y)\bigr]
 \quad\Longleftrightarrow\quad \rho_x=\rho_y.
\tag{VII.36}
$$

若两态不同，有一个共同合法、输入无关的真正有限字使该二值律不同。此商只保留端口态，不区分在 $(h,\rho_x)$ 相同的来源间仍不同的身份或不可访问环境。

**证明。** 第一位为一强制第二位为零，故 $n_1|_{\mathcal K_n}$ 的秩为 $q=d_{n-2}=F_n$，且 $0<q<d_n$。由定理 58.1，其在字闭包中的共轭轨道是全部秩 $q$ 投影。复用命题 32.2 证明中的固定秩投影分离论证，把其 $(d,k)$ 换成这里的 $(d_n,q)$：全部这种投影与迹零 Hermitian 差 $\Delta=\rho_x-\rho_y$ 的配对均为零，当且仅当 $\Delta=0$。概率的连续性把全部实际字的相等提升到闭包，因此给 (VII.36)；反向由 (VII.35) 立即得到。

若 $\Delta\ne0$，该同一分离论证给秩 $q$ 投影 $Q$，使 $c=|\operatorname{tr}(\Delta Q)|>0$。选 $U$ 使 $U^\dagger n_1U=Q$，再由 (VII.24) 取 $\|w-zU\|_{\mathrm{op}}<c/8$。两个输入各自的事件概率误差小于 $c/4$，故实际字的概率差仍大于 $c/2$，并未执行一个无限极限门。

这里消费的是定理 58.1 对整个合法空间的控制，输入不再受五维块或交替码限制；末端二值读口是另外声明的观察权限。概率函数的识别不等于一份未知输入上的确定态名取得：命题 32.2 的非正交态障碍仍适用，估计概率族还需要重复来源及统计资源。端口态不能自动替代定义 41.1 的实际记录或对可回流环境的联合描述；公布反馈的共同正确值仍须满足定义 33.2 的交集条件，命题 33.3 已表明控制通用性不保证该交集非空。$\square$

## 追加锚（本行以下为增补区）

## 40. 第一位置读口的尖锐全链对比率

**定义 60.1（原生概率对比与来源范围）。** 固定 $n\geq3$，沿用假设 55.2 的整个合法链、有限字集 $\mathcal W_n$ 和命题 59.1 的末端二值读口。以下简记

$$
\begin{aligned}
d&=F_{n+2},&q&=F_n,&P&=n_1|_{\mathcal K_n},\\
P_w&=w^\dagger Pw,&p_\rho(w)&=\operatorname{tr}(\rho P_w),\\
D(\rho,\sigma)&=\tfrac12\|\rho-\sigma\|_1,&
B_n(\rho,\sigma)&=\sup_{w\in\mathcal W_n}
                  |p_\rho(w)-p_\sigma(w)|.
\end{aligned}
\tag{VIII.1}
$$

$F_0=0,F_1=1$，故 $2\leq q<d/2$。$B_n$ 比较理想二值概率函数；一次实际读口只返回一个比特，并不返回 $p_\rho(w)$。对既有历史 $h$ 的来源纤维 $X_h$，可将 $\rho,\sigma$ 限于其中的端口态。下述统一常数的尖锐性和设置数下界则在整个 $\mathsf D(\mathcal K_n)$ 上取量词；这一数学定义域不授予任意态的制备权限。受限测量范数与最佳支配常数的研究框架见 Matthews–Wehner–Winter，[*Distinguishability of quantum states under restricted families of measurements*](https://arxiv.org/html/0810.2327v2)，引言及 §1。

**定理 60.2（Fibonacci 秩读口的最佳对比常数）。** 令 $A=\rho-\sigma$ 的特征值为 $\lambda_1\geq\cdots\geq\lambda_d$。则

$$
\begin{aligned}
B_n(\rho,\sigma)
 &=\max\left\{\sum_{i=1}^q\lambda_i,
                    -\sum_{i=d-q+1}^d\lambda_i\right\},\\
c_nD(\rho,\sigma)&\leq B_n(\rho,\sigma)\leq D(\rho,\sigma),\\
c_n&=\frac{d-q}{d-1}=\frac{F_{n+1}}{F_{n+2}-1}.
\end{aligned}
\tag{VIII.2}
$$

两个常数在全部态对上均最佳。$c_n>1/\varphi$ 且 $c_n\to1/\varphi$，其中 $\varphi=(1+\sqrt5)/2$。若 $B_n(\rho,\sigma)>b$，存在真正有限字 $w$ 使概率差大于 $b$；不要求上确界在有限字中取得。

**证明。** 定理 58.1 给 $SU(d)\subseteq\overline{\mathcal W_n}$。任意两个秩 $q$ 投影酉共轭；将实现共轭的酉乘以适当标量即可令行列式为一而不改共轭。因此实际 $P_w$ 的闭包恰为全部秩 $q$ 投影。这只消费共轭轨道，不把 (VII.23) 的有限行列式类改成 $U(d)$ 稠密性。

所需谱极值是 Fan 的成熟变分工具，见 [Fan 原文 Theorem 1，刊页 653](https://doi.org/10.1073/pnas.35.11.652) 及 [仓内来源说明](../../../Library/Eigenstructure/fan1949weyl.md)。这里的有限维步骤可直接核对：在 $A$ 的特征基中，任意秩 $q$ 投影 $R$ 满足

$$
\operatorname{tr}(AR)=\sum_i\lambda_i r_i,
\qquad 0\leq r_i\leq1,\qquad \sum_i r_i=q.
\tag{VIII.3}
$$

把权重移向较大特征值，最大值为前 $q$ 项之和；最小值为后 $q$ 项之和。相应谱投影达到两端。连续性及上述轨道闭包给 (VIII.2) 第一式。由于 $\operatorname{tr}A=0$，正负谱质量均为 $D$；任何效果与 $A$ 的配对都在 $[-D,D]$ 内，故上界成立。

设 $A\ne0$，正、负特征值个数分别为 $r,s\geq1$。若 $r<q$，前 $q$ 项保留全部正质量，只扣去其余 $d-r$ 个非正特征值中绝对值最小的 $q-r$ 项。它们的绝对值之和至多 $(q-r)D/(d-r)$，包括零特征值时仍成立。因此

$$
\sum_{i=1}^q\lambda_i
 \geq\frac{d-q}{d-r}D\geq\frac{d-q}{d-1}D.
\tag{VIII.4}
$$

若 $s<q$，对 $-A$ 作同一论证。其余情形 $r,s\geq q$ 时，前 $q$ 个正特征值至少占正质量的 $q/r$，最负 $q$ 项至少占负质量的 $q/s$，故

$$
B_n(\rho,\sigma)\geq\frac{q}{\min(r,s)}D
 \geq\frac{q}{\lfloor d/2\rfloor}D\geq c_nD.
\tag{VIII.5}
$$

最后一步使用实际 Fibonacci 秩：$d=3q-F_{n-2}\leq3q-1$。于是 $q\geq(d+1)/3$，且
$q(3d-2)-d^2\geq(d-2)/3>0$，等价地 $2q/d>(d-q)/(d-1)$；再用 $q/\lfloor d/2\rfloor\geq2q/d$。$A=0$ 的情形直接成立。

取任意单位向量 $\psi\in\operatorname{ran}P$，定义同一族见证

$$
\rho_0=|\psi\rangle\langle\psi|,
\qquad \rho_1=\frac{I-\rho_0}{d-1}.
\tag{VIII.6}
$$

两态支撑正交，$D(\rho_0,\rho_1)=1$；差的谱为 $1,-1/(d-1),\ldots,-1/(d-1)$。谱公式给 $B_n=c_n$，并且空字的原 $P$ 已达到此值。因此任何更大的统一下界常数都失败。另取 $u\in\operatorname{ran}P$、$v\in\ker P$ 为单位向量，两纯态的 $D$ 与空字概率差都为一，证明上界常数最佳。

递推式给 $\varphi F_{n+1}-F_{n+2}=(-1)^n\varphi^{-(n+1)}$，从而 $\varphi F_{n+1}-(F_{n+2}-1)>0$。结合 Fibonacci 比值极限即得 $c_n>1/\varphi$ 及所述极限。最后，若全部实际字概率差均不大于 $b$，其上确界也不大于 $b$，证明严格阈值的有限字结论。$\square$

## 41. 同一极值态对的有限份自适应读出

**假设 61.1（逐份一次末端比特合同）。** 两个已知候选为 (VIII.6)，先验各为 $1/2$。另行供应至多 $M$ 份样本，在假设 $i$ 下联合态为 $\rho_i^{\otimes M}$；测量装置各次独立初始化，无跨份量子记忆。每份样本只可施加一个 $\mathcal W_n$ 有限字，再作一次原二值终端测量。字可依赖既往完整经典记录，可提前停止，也容许输入无关的经典随机化；禁止同份追加测量、跨份联合量子操作或额外量子读口。此为统计资源假设，不由定理 58.1 或命题 59.1 产生。

**定理 61.2（原生一次比特合同的精确错误率）。** 在假设 61.1 下，对每个整数 $M\geq0$，最优等先验平均错误率为

$$
e_n(M)=\tfrac12\beta_n^M,
\qquad \beta_n=\frac{q-1}{d-1}\in(0,1).
\tag{VIII.7}
$$

因而对 $0<\epsilon<1/2$，达到 $e_n(M)\leq\epsilon$ 的最小整数预算为
$\left\lceil\log(1/(2\epsilon))/\log(1/\beta_n)\right\rceil$。这是供应样本份数，不是物理历时。

**证明。** 任一允许效果 $R=P_w$ 的秩为 $q$。令 $a=\langle\psi|R|\psi\rangle\in[0,1]$；结果一的两假设概率为

$$
\Pr_0(Y=1)=a,
\qquad \Pr_1(Y=1)=\frac{q-a}{d-1}.
\tag{VIII.8}
$$

空字的基准比特 $X$ 满足 $\Pr_0(X=1)=1$、$\Pr_1(X=1)=\beta_n$。对它施加假设无关的随机核

$$
\Pr(Y=1\mid X=1)=a,
\qquad \Pr(Y=1\mid X=0)=\frac{q(1-a)}{d-q}.
\tag{VIII.9}
$$

因 $q<d-q$，这是合法的 $[0,1]$ 概率。在假设一之下，输出一的概率为
$a(q-1)/(d-1)+q(1-a)/(d-1)=(q-a)/(d-1)$；假设零之下为 $a$。故每个允许单份实验都是同一基准实验的经典退化。

对自适应策略，依次取独立基准比特，按已模拟的历史选择 (VIII.9)，便可在两个假设下同时模拟整个记录和最终决策。源的乘积合同保证每一步条件概率恰为 (VIII.8)。提前停止可填充至 $M$ 步并忽略多余比特。输入无关随机种子可一并模拟。因此完整原记录是 $M$ 个独立基准比特的假设无关后处理。这里直接消费 [《递归关系观察：波粒事件》定理 296.2](RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md#296-信息退化可见结果被怎样压缩同样属于边界) 的有限实验 Bayes 风险单调性，不另立一般 Blackwell 定理。

基准记录在假设零下恒为全一；在假设一下，全一的概率为 $\beta_n^M$。对有限记录分布 $p_0,p_1$，等先验最优错误率为 $\frac12\sum_z\min\{p_0(z),p_1(z)\}$，因为每个记录上分别选择较大似然即可。这里仅全一贡献重叠，得 (VIII.7)。重复原空字 $M$ 次，全一判零、否则判一，恰好达到该界；$M=0$ 时取无观测猜测。$\square$

两态虽然正交，所有有限 $M$ 的上述受限错误率仍严格正。若另授效果 $\rho_0$ 的二值测量，一份即可无误区分两支撑；它不是秩 $q\geq2$ 的原生一次末端效果。故 (VIII.7) 不约束更强的联合测量、同份序贯测量或未知端口上的任务，也不是任意态对的多份公式。

## 42. 保留统一对比的预设有限菜单及其设置数

**定义 62.1（最大单设置对比）。** 一个输入无关的预设菜单为非空有限字列表 $\mathcal F=(w_1,\ldots,w_m)$，其效果为 $P_j=P_{w_j}$。定义

$$
B_{\mathcal F}(\rho,\sigma)
 =\max_{1\leq j\leq m}|\operatorname{tr}((\rho-\sigma)P_j)|.
\tag{VIII.10}
$$

列表在看到未知输入及其测量记录之前固定。这里比较各二值实验中的最大概率差，不是把多个结果概率求和的单一 POVM 范数。

**定理 62.2（严格次尖锐菜单存在与指数设置代价）。** 对任意 $0<\chi<c_n$，存在这样的实际有限字菜单，使对全部密度态对同时有

$$
\chi D(\rho,\sigma)\leq B_{\mathcal F}(\rho,\sigma)
 \leq D(\rho,\sigma).
\tag{VIII.11}
$$

反之，任何在全部密度态对上满足 (VIII.11) 下界的 $m$ 设置菜单都满足

$$
m\geq\tfrac12\exp\!\left(
                  \frac{2\chi^2(d-1)^3}{d^2}\right).
\tag{VIII.12}
$$

**证明。** 先在紧集
$\mathcal S=\{A=A^\dagger:\operatorname{tr}A=0,\ \|A\|_1=2\}$ 上取有限覆盖。每个 $A\in\mathcal S$ 都是两个密度态之差：其正负部分各有迹一。定理 60.2 给某个真正有限字满足 $|\operatorname{tr}(AP_w)|>\chi$。对固定字，这是 $\mathcal S$ 上的开条件。所有这些开集覆盖 $\mathcal S$，紧致性给有限子覆盖。对非零态差除以其 $D$，便得 (VIII.11)；零差直接成立。所选字和参数只依赖 $n,\chi$，不依赖输入。这一存在证明没有把闭包中的门当作已执行的无限字。

为证下界，对每个单位向量 $v$ 使用同一见证族
$\rho_v=|v\rangle\langle v|$、$\sigma_v=(I-\rho_v)/(d-1)$，其 $D=1$。对固定秩 $q$ 投影 $Q$，置 $S=\langle v|Q|v\rangle$，有

$$
\operatorname{tr}((\rho_v-\sigma_v)Q)=\frac{dS-q}{d-1}.
\tag{VIII.13}
$$

仅在此证明中，以复单位球面上的酉不变概率选择 $v$。其分布可由独立标准复 Gaussian 坐标归一化得到，因为 Gaussian 密度只依赖向量范数。各坐标模平方为独立均值一指数变量；前 $q$ 项与其余项之和分别具有密度 $x^{q-1}e^{-x}/(q-1)!$ 和 $y^{d-q-1}e^{-y}/(d-q-1)!$，由指数密度的卷积归纳即可得到。作 $s=x/(x+y),t=x+y$ 的变量替换并积分 $t$，得

$$
f_S(s)=\frac{(d-1)!}{(q-1)!(d-q-1)!}
             s^{q-1}(1-s)^{d-q-1},\qquad 0<s<1.
\tag{VIII.14}
$$

因此，对 $0<u<1$ 及 $Z_u\sim\operatorname{Bin}(d-1,u)$，

$$
\Pr(S\geq u)=\Pr(Z_u\leq q-1),
\qquad \Pr(S\leq u)=\Pr(Z_u\geq q).
\tag{VIII.15}
$$

例如第一式右侧是 $\sum_{k=0}^{q-1}\binom{d-1}{k}u^k(1-u)^{d-1-k}$，其导数为 $-f_S(u)$，在 $u=0$ 为一；第二式取补集。这直接给出所需 Beta—二项关系。

使用 Hoeffding 的成熟二项尾界，见 [*Probability Inequalities for Sums of Bounded Random Variables*](https://doi.org/10.1080/01621459.1963.10500830)，Theorem 2：若 $Z\sim\operatorname{Bin}(N,u)$、$b\geq0$，则任一方向离开均值至少 $Nb$ 的概率不超过 $e^{-2Nb^2}$。其所需一步也可直接推出：Bernoulli 变量 $X$ 的中心化对数矩母函数 $g(t)=\log\mathbb E e^{t(X-u)}$ 满足 $g(0)=g'(0)=0$，而 $g''(t)$ 是一个 Bernoulli 方差，至多 $1/4$。故 $g(t)\leq t^2/8$；独立相乘、指数 Markov 及 $t=4b$ 给上尾，$t=-4b$ 给下尾。

令 $p=q/d$、$a=\chi(d-1)/d$。在上阈值 $u=p+a\in(0,1)$，

$$
(d-1)u-(q-1)=1-p+(d-1)a\geq(d-1)a;
\tag{VIII.16}
$$

在下阈值 $u=p-a\in(0,1)$，$q-(d-1)u=p+(d-1)a\geq(d-1)a$。结合 (VIII.15) 及尾界得

$$
\Pr\{|S-q/d|\geq a\}
 \leq2e^{-2(d-1)a^2}.
\tag{VIII.17}
$$

阈值在 $[0,1]$ 外时相应尾事件为空；在端点也因 (VIII.14) 无原子而为零。由 (VIII.13)，固定设置满足对比至少 $\chi$ 的球面概率不超过 (VIII.17)。若 $m$ 个设置对所有见证态对均满足 (VIII.11)，这些事件的并集必须覆盖整个球面。因此 $1\leq2m e^{-2(d-1)a^2}$，即 (VIII.12)。这里的酉不变测度只是排除小菜单的数学见证，不是供应随机控制或随机制备的资源。$\square$

对固定 $\chi>0$ 且 $\chi<c_n$，(VIII.12) 的指数随 $d=F_{n+2}$ 线性增长。这不与有限维线性坐标的精确可识别性冲突：本定理要求相对于迹距离的统一正对比裕量，且用最大单设置误差衡量。它不提供任意层析、加权结果范数、自适应设置或联合测量的样本下界；也不提供最小菜单、有效字综合或字长上界。若来源域不含全部见证族，不能沿用这里的设置数下界。框架层析参见 Scott，[*Tight informationally complete quantum measurements*](https://arxiv.org/html/quant-ph/0604049v6)，§§III、VI。

## 43. 有限实际记录下的共同来源置信纤维

**假设 63.1（固定历史后的重复来源与独立初始化）。** 固定已得历史 $h$、实际来源 $x\in X_h$ 和端口态 $\rho_x$。先固定满足 (VIII.11) 的实际菜单及整数 $N\geq1$。条件于这一个来源和历史，另行供应 $mN$ 份态 $\rho_x^{\otimes mN}$；第 $j$ 组 $N$ 份分别执行 $w_j$ 和原末端二值测量。装置每份独立初始化，实际效果恰为已知 $P_j$，无跨次返回环境。记录包含设置、样本数和全部比特；记各组一的计数为 $K_j$、频率为 $\widehat p_j=K_j/N$。样本数预先固定，不作未计入的可选停止。

**命题 63.2（原生未来与独立端口协议的同一置信纤维）。** 给定 $0<\delta<1$，置

$$
\begin{aligned}
t&=\sqrt{\frac{\log(2m/\delta)}{2N}},\\
\mathcal C_{\widehat p}
 &=\{\tau\in\mathsf D(\mathcal K_n):
          \max_j|\operatorname{tr}(\tau P_j)-\widehat p_j|\leq t\},\\
X_{h,\widehat p}
 &=\{y\in X_h:\rho_y\in\mathcal C_{\widehat p}\},
\qquad r=\min\{1,2t/\chi\}.
\end{aligned}
\tag{VIII.18}
$$

则对每个固定 $x\in X_h$ 有 $\Pr_x\{x\in X_{h,\widehat p}\mid h\}\geq1-\delta$。任何非空 $\mathcal C_{\widehat p}$ 的迹距离直径至多 $r$。对该集合内任意 $\sigma,\tau$，同时有

$$
\sup_{w\in\mathcal W_n}|p_\sigma(w)-p_\tau(w)|\leq r.
\tag{VIII.19}
$$

进一步，固定任意已声明的有限端口协议 $\Pi$：仅接收端口输入 $A$，有限辅助系统以同一已知态 $\eta$ 独立初始化，采用固定有限分支的量子仪器和经典反馈，终止时保留完整记录，不含被省略的输入相关返回环境。其完整无条件记录律满足

$$
\operatorname{TV}(\mathsf P_\sigma^\Pi,
                   \mathsf P_\tau^\Pi)\leq D(\sigma,\tau)\leq r.
\tag{VIII.20}
$$

**证明。** 假设 63.1 下，第 $j$ 组为 $N$ 个独立 Bernoulli 试验，均值为 $\operatorname{tr}(\rho_xP_j)$。Hoeffding 双侧界及 $m$ 项并合给

$$
\Pr_x\left\{\max_j|\widehat p_j-
               \operatorname{tr}(\rho_xP_j)|>t\mid h\right\}
 \leq2m e^{-2Nt^2}=\delta.
\tag{VIII.21}
$$

这复用 [《递归关系观察：波粒事件》定理 22.3](RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md#22-从精确恢复到有误差的关系重建) 的独立重复取样与共同置信事件方法；这里的消费者是 (VIII.11) 的指定原生菜单。(VIII.21) 中失败事件的补事件 $\{\max_j|\widehat p_j-\operatorname{tr}(\rho_xP_j)|\leq t\}$ 在 $\Pr_x(\cdot\mid h)$ 下的概率至少为 $1-\delta$；在该联合成功事件上，$\rho_x\in\mathcal C_{\widehat p}$，从而 $x\in X_{h,\widehat p}$。若 $\sigma,\tau$ 同属该集合，逐坐标三角不等式给 $B_{\mathcal F}(\sigma,\tau)\leq2t$；(VIII.11) 给 $D(\sigma,\tau)\leq2t/\chi$，再用 $D\leq1$。定理 60.2 的上界于是给 (VIII.19)，无需对无限字族另取并合界。

为核对 (VIII.20) 的协议量词，把每条完整记录 $z$ 的复合分支记为辅助扩张上的 CP 映射 $\mathcal I_z$，把预先的独立初始化记为 $J_\eta(\tau)=\tau\otimes\eta$。其输入效果为 $E_z=(\mathcal I_z\circ J_\eta)^*(I)\geq0$。完整性给 $\sum_zE_z=I$；反馈只决定各分支内已声明的复合映射。因此 $\mathsf P_\tau^\Pi(z)=\operatorname{tr}(\tau E_z)$。对任何记录事件 $S$，$E_S=\sum_{z\in S}E_z$ 是效果，故 $|\operatorname{tr}((\sigma-\tau)E_S)|\leq D(\sigma,\tau)$。对 $S$ 取最大便得完整记录总变差界。只要每个协议满足同一初始化合同，这一确定性结论在同一个置信事件上对全部这样的协议成立；它不授予其中未声明的操作。$\square$

在非空纤维中选一个估计态，只能得到上述置信保证，不是有限比特给出无误精确态名。若集合为空，应报告该置信集合为空，不用任意态替换它。对 $0<\epsilon<1$，充分的预设每组样本数为

$$
N\geq\frac{2\log(2m/\delta)}{\chi^2\epsilon^2},
\tag{VIII.22}
$$

此时 $r\leq\epsilon$，总消耗为 $mN$ 份所供应样本。该充分预算与 (VIII.12) 的设置数障碍是不同方向的结论，不把两者合称最优层析复杂度。可靠置信区域参见 Christandl–Renner，[*Reliable Quantum State Tomography*](https://arxiv.org/abs/1108.5329v2)。

若按训练记录选择未来字或协议，(VIII.19)–(VIII.20) 的确定性统一界仍可用，但物理预测必须作用于一份另行供应的、条件于固定 $x,h$ 与训练记录独立的留出输入，及该协议独立初始化的辅助系统。它不是已消耗样本的测后条件态预测。对于输入相关的隐环境，局部边缘 $\rho_x$ 不决定回流记录；这里直接保留 [《观察者内生三轴几何与预测接口》定义 9.3 的共同环境例](AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md) 的边界。对稀有后选择事件的条件律也须另给事件概率下界，不能从完整无条件记录界直接保留同一常数。

相同单份边缘不供应假设 63.1。复用 [《四角相干与单份认证》命题 C-121.5](AURIC_FIB_ATOM_FOUR_CORNER_COHERENCE_AND_SINGLE_COPY_CERTIFICATION.md) 的共同标签机制：取单位向量 $u\in\operatorname{ran}P_j$、$v\in\ker P_j$，仅抽一次公平比特 $L$，随后全部样本按 $L$ 同时取 $u$ 或同时取 $v$。每份边缘均为 $(|u\rangle\langle u|+|v\rangle\langle v|)/2$，但 $\widehat p_j=L$，对其边缘均值的误差恒为 $1/2$，不随 $N$ 缩小。共同标签造成的联合关联不能被边缘相等消去。

若还要求保留一个实际参考 $R$，可另假定供应 $\tau_{AR}\otimes\rho_x^{\otimes mN}$ 且 $\operatorname{tr}_R\tau_{AR}=\rho_x$；测量后面的独立份不会物理作用于 $AR$。然而本置信纤维只约束 $A$ 的边缘，不识别未知 $AR$ 相关，也不提供带参考的联合迹距离证书。这样的联合供应不是从一个未知 $AR$ 输入免费复制出来的资源。

## 追加锚（本行以下为增补区）


## 44. 固定相位菜单的实际有限字达到

**定理 64.1（Native58 的有限字加强）。** 保留定义 55.1、假设 55.2、(VII.18) 的被动标架及定理 58.1 已证明的全尺寸翻转 Lie 代数。对每个 $n\geq1$，实际翻转字集本身满足

$$
\mathcal V_n=D_nSO(d_n)D_n^\dagger.
\tag{IX.1}
$$

对每个 $n\geq3$，仍只使用同址固定门 $S_{\star,n}$，实际有限字集本身满足

$$
\boxed{\mathcal W_n=\{Q\in U(d_n):\det Q\in\langle i^{F_{n-2}}\rangle\}}.
\tag{IX.2}
$$

因此 $SU(d_n)\subseteq\mathcal W_n$；每个酉通道都有一个精确有限原生字实现。这里“原生”仅指假设 55.2 的理想菜单，参数仍可取任意实数。结论没有给出已评价的脉冲数、持续时间、参数精度或硬件实现。

**证明。** 在被动标架中记 $\widetilde{\mathcal W}_n=D_n^\dagger\mathcal W_nD_n$，$A_j=A_j^{(n)}$，并定义

$$
\mathfrak L=\operatorname{span}_{\mathbb R}
 \{\operatorname{Ad}_g A_j:g\in\widetilde{\mathcal W}_n,\ 1\leq j\leq n\}.
\tag{IX.3}
$$

这里 $g$ 总是一个实际有限字，不是字集闭包中的元素。$\mathfrak L$ 是有限维实向量空间，因而闭；每个实际字的共轭保持它。对每个生成其线性张成的方向 $X=\operatorname{Ad}_gA_j$，都有精确恒等式

$$
e^{tX}=g e^{tA_j}g^{-1}\in\widetilde{\mathcal W}_n
\qquad(t\in\mathbb R).
\tag{IX.4}
$$

字的逆可用，特别是固定相位的逆就是其三次幂。对 $Y\in\mathfrak L$，曲线 $e^{tX}Ye^{-tX}$ 全在 $\mathfrak L$ 内；在零点求导给 $[X,Y]\in\mathfrak L$。对 $X$ 的有限实线性组合使用双线性，故 $\mathfrak L$ 是 Lie 代数。这一步只对有限维向量空间取导数，没有执行一个交换子极限字。

由定理 58.1 的翻转代数等式，$\mathfrak{so}(d_n)\subseteq\mathfrak L$。该定理的 (VII.25)–(VII.33) 是全 $n$ 归纳：被末位阻断的控制产生第一块中的非零理想，孤立匹配边的括号给全部第一块旋转，再由最后控制的匹配与一个零行得到全部矩形跨块方向和第二块旋转。因此这里复用的是该全尺寸证明，不是有限尺寸的秩外推。

设 $P=n_1n_3|_{\mathcal K_n}$。对每个 $n\geq3$，$P$ 的像和核均非零，$S_{\star,n}$ 在两者上分别为 $i$ 和 $1$。$\mathfrak L$ 在这个实际门的共轭下不变。于是对计算基指标 $p\in\operatorname{ran}P$、$q\in\ker P$，它同时包含

$$
J_{pq},\qquad i(E_{pq}+E_{qp}),\qquad
[J_{pq},i(E_{pq}+E_{qp})]=2i(E_{pp}-E_{qq}).
\tag{IX.5}
$$

两个非空指标集之间的完全二分图连通；沿路径相加，以上对角差张成全部迹零纯虚对角矩阵。再与全部 $J_{uv}$ 交换，得到每个 $i(E_{uv}+E_{vu})$。这些与实反对称方向张成 $\mathfrak{su}(d_n)$。反向，(IX.3) 的每个方向都是迹零反 Hermitian，故
$\mathfrak L=\mathfrak{su}(d_n)$。

从 (IX.3) 的实际共轭方向中选一组基 $X_1,\ldots,X_{d_n^2-1}$，考虑

$$
\mathcal F(t_1,\ldots,t_{d_n^2-1})
 =e^{t_1X_1}\cdots e^{t_{d_n^2-1}X_{d_n^2-1}}.
\tag{IX.6}
$$

它在零点的微分是 $(t_j)\mapsto\sum_jt_jX_j$，为到 $T_I SU(d_n)$ 的同构。逆函数定理给 $SU(d_n)$ 中一个恒等邻域，邻域的每个点都是 (IX.4) 的有限字乘积。故 $\widetilde{\mathcal W}_n\cap SU(d_n)$ 是开子群。开子群的全部陪集均开，因而它也闭；$SU(d_n)$ 连通，迫使此子群为整个 $SU(d_n)$。没有把稠密子群当成整个群。

同一论证把 (IX.3) 中的字限于翻转字，所得代数恰为 $\mathfrak{so}(d_n)$：一侧来自定理 58.1，另一侧来自正交共轭保持实反对称性。选实际共轭基，在连通 $SO(d_n)$ 上使用 (IX.6) 的相应维数版本，即得 (IX.1)，包括 $n=1,2$。$n=0$ 的空菜单仅给一维空间上的恒等。

所有翻转脉冲行列式为一，而定理 58.1 已给
$\operatorname{rank}P=F_{n-2}$，所以每个实际字的行列式在 $C_n=\langle i^{F_{n-2}}\rangle$ 内。反之，若 $\det Q\in C_n$，选整数 $k$ 使 $\det Q=\det S_{\star,n}^k$，则
$QS_{\star,n}^{-k}\in SU(d_n)\subseteq\mathcal W_n$，故 $Q\in\mathcal W_n$。被动共轭不改变 $SU$ 或行列式，得到原坐标中的 (IX.2)。对任意 $U$ 取 $|z|=1$ 使 $z^{d_n}\det U=1$，则 $zU$ 有精确有限字，且其酉通道等于 $U$ 的通道。

例如 $n=3,5,8$ 时，$C_n$ 的阶分别为 $4,2,1$。$n=8$ 虽有 $\det S_{\star,8}=1$，该门的相位支撑仍是非零真子空间，故 (IX.5) 仍成立；不能因行列式为一而删去其控制作用。$\square$

本定理应用的是成熟的共轭基与逆函数方法，见 D. D'Alessandro，[*Uniform finite generation of compact Lie groups and universal quantum gates*，Lemma 1、Theorem 2](https://arxiv.org/html/quant-ph/0111133v1)。其接口是连通有限维 Lie 群、所给单参数子群及实参数；本证明把每个共轭和逆都落实为当前固定相位菜单中的字。[《合法门、状态机与 Shor 读出》Theorem 11.2](FIB_LEGAL_GATES_STATE_MACHINES_AND_SHOR_READOUT.md#11-a-phase-restriction-has-an-exact-blind-sector-one-extra-quadrature-removes-it) 已在另一项“某一位置增加第二正交驱动”的菜单下使用精确控制原理。这里增加的是 Native58 的固定相位、全合法链应用，不认领该一般控制方法，也不把两种菜单的权限互换。

## 45. 原支持三维输入的精确末次秩二边缘

**定义 65.1（固定复线性支持与读效果）。** 在 $\mathcal K_3$ 的基序 $000,100,010,001,101$ 中，固定

$$
E_N=\left(\frac{|000\rangle+|101\rangle}{\sqrt2},
          \frac{|100\rangle+|001\rangle}{\sqrt2},|010\rangle\right),
\qquad n_1=\operatorname{diag}(0,1,0,0,1).
\tag{IX.7}
$$

$E_N^\dagger E_N=I_3$，读扇区秩二，其正交补秩三。此 $E_N$ 与 [GC §21 的五基字典](FIB_NATIVE_COMPLETE_CONTINUATION_GLOBAL_ACTUAL_COUNTS.md#21-the-fixed-complex-linear-five-mode-dictionary) 对应。GC 的同一源根满足 (GC.6)，从而其
$M=\operatorname{diag}(0,m_1,m_2)$ 满足 $0\preceq M\prec I_3$、$\operatorname{rank}M=2$。严格上界来自 $D^\dagger D\succ0$ 和根 TP，源根条件本身仍是 GC Assumption 1.2 的未验证供应。

**定理 65.2（精确支持效果，不是完整仪器）。** 在假设 55.2 的 $n=3$ 菜单和命题 59.1 另行声明的末次二值 PVM 下，存在一个实际有限字 $U\in\mathcal W_3$，使

$$
E_N^\dagger U^\dagger n_1UE_N=M.
\tag{IX.8}
$$

因此同一个字对全部复 qutrit 输入 $\rho$ 精确给出一结果概率
$\operatorname{tr}(M\rho)$。对任意有限被动参考及联合态 $X$，丢弃被测系统后，该结果的未归一参考算子恰为
$\operatorname{Tr}_3[(M\otimes I_R)X]$。

**证明。** 选等距 $A:\operatorname{ran}M\to\operatorname{ran}n_1$ 和
$B:\mathbb C^3\to\ker n_1$，定义

$$
J=A\sqrt M+B\sqrt{I_3-M}.
\tag{IX.9}
$$

两项的像正交，故 $J^\dagger J=M+(I_3-M)=I_3$，且
$J^\dagger n_1J=M$。在两个五维空间中分别补齐 $E_N$ 与 $J$ 的三个正交列，得到酉 $U_0$ 满足 $U_0E_N=J$。在输入的二维未指定正交补中选一个单位基向量，将它对应的输出列乘以 $(\det U_0)^{-1}$；其余列不变。所得 $U$ 仍酉，仍有 $UE_N=J$，而 $\det U=1$。定理 64.1 使这个 $U$ 本身成为实际有限字，得到 (IX.8)。将效果恒等式张量 $I_R$ 并对被测系统取偏迹，给参考算子恒等式；无需对参考态作实性或乘积分离假设。$\square$

原读口在未作这个字时的初等压缩是

$$
E_N^\dagger n_1E_N=\operatorname{diag}(1/2,1/2,0),
\tag{IX.10}
$$

由 (IX.7) 的三列逐项配对即可得到；它通常不等于原 $M$。定理 65.2 解决的是支持效果的精确匹配，而非仅按比特个数判断的障碍。效果只决定结果概率及其丢弃系统后的参考边缘：它不指定条件量子后态、GC 的低/高取得分支、完整 live 通道、整个未来可访问纤维成本或真实 FIRST 时刻。甚至“允许末次 PVM 的概率”也不自动给出可复用的 Lüders 后态服务。GC §§23–25 分别保留这些仪器障碍及另加装置前提的条件构造；那些前提没有由本定理授权。原生仪器与时钟缺口，以及原全部预算、全部对比、源与 minimax 的目标，均不因此完成。

## 追加锚（本行以下为增补区）

## 46. 固定四分之一相位的调用秩与精确谱前沿

**定义 66.1（原维数、实帧与至多调用合同）。** 固定 $\mathcal H=\mathbb C^d$ 的一组实正交基及其中的逐坐标共轭，$d\geq2$。设 $P=P^T=P^2$ 是非零、非恒等的实投影，$\operatorname{rank}P=p$，唯一收费门为正向固定相位 $S=\exp(i\pi P/2)$。实控制允许任意有限个 $SO(d)$ 元素；终端只读一个固定实投影 $R=R^T=R^2$ 的二值 PVM $\{R,I-R\}$，$\operatorname{rank}R=r\in\{0,\ldots,d\}$。令

$$
\begin{aligned}
q&=\min(p,d-p),& h&=\min(r,d-r),&m&=\lfloor d/2\rfloor,\\
\mathcal U_{\leq k}
 &=\bigcup_{j=0}^{k}
   \{O_j S O_{j-1}S\cdots S O_0:O_0,\ldots,O_j\in SO(d)\},\\
B_k(\rho,\sigma)
 &=\max_{U\in\mathcal U_{\leq k}}
       |\operatorname{tr}((\rho-\sigma)U^\dagger R U)|,
\qquad k\in\mathbb Z_{\geq0}.
\end{aligned}
\tag{IX.11}
$$

$j=0$ 项为 $SO(d)$。每次 $S$ 计一次，$S^{-1}=S^3$ 若实际采用则计三次；不另供负向相位或连续可调相位。每个固定 $j$ 的参数空间是紧空间 $SO(d)^{j+1}$，有限并仍紧，故 (IX.11) 的最大值确实存在于有限字中。控制字可依赖已知候选对 $(\rho,\sigma)$ 和预先固定的共同经典记录，但对两个未知输入标签必须相同；不提供标签相关旁信息。不使用辅助量子系统、可访问参考、中途测量、后选择或任何非酉 CPTP 预处理。

输入域为全部满足 $\operatorname{Re}\rho=\operatorname{Re}\sigma$ 的密度态对，实部按上述同一实帧逐项取得。因此 $\Delta=\rho-\sigma=iA$，其中 $A$ 为实反对称矩阵。以降序非负数 $a_1\geq\cdots\geq a_m\geq0$ 表示其反对称块权重，包含零块；于是

$$
\operatorname{spec}(\Delta)
 =\{a_1,-a_1,\ldots,a_m,-a_m\}
   \cup\{0\ \text{若 }d\text{ 为奇数}\},
\qquad
D(\rho,\sigma)=\tfrac12\|\Delta\|_1=\sum_{j=1}^{m}a_j.
\tag{IX.12}
$$

这种实部与反对称块分解是既有工具，见 Wu 等，[*Resource theory of imaginarity: quantification and state conversion*，arXiv:2103.01805v1，式 (36)–(37)](https://arxiv.org/html/2103.01805v1#S3.E36)。此输入域称为旧盲态对：每个实对称效果与 $iA$ 的迹配对均为零，因而任何零相位字的读数相同。该定义只约束态对，不授予任意态的原生制备权限。

$B_k$ 是二值概率分布的总变差，即同一事件的概率差绝对值；它采用定义 60.1 的受限测量对比口径。一般框架及其与迹距离的归一化见 Matthews–Wehner–Winter，[*Distinguishability of quantum states under restricted families of measurements*，arXiv:0810.2327v2，引言式 (1)–(3) 及 §1](https://arxiv.org/html/0810.2327v2)。相对于固定实基的实 Kraus 操作比这里的实酉控制更宽；Wu 等，[*Operational Resource Theory of Imaginarity*，arXiv:2007.14847v2，Theorem 2、式 (5) 及随后关于二维像的论述](https://arxiv.org/html/2007.14847v2#Thmtheorem2)，采用的是该更宽菜单。参考文稿《AURIC 受限量子读出与相位资源理论》P.6 的单相位合同与此处相接；P.8/C4 中的实 CPTP 反对称平面合并不在 (IX.11) 的操作类内。

**定理 66.2（每次调用的普适谱上界）。** 对定义 66.1 的全部维数、投影和旧盲态对，令 $t_k=\min(kq,h)$，空和为零，则

$$
B_k(\rho,\sigma)\leq\sum_{j=1}^{t_k}a_j\leq D(\rho,\sigma).
\tag{IX.13}
$$

特别地，$B_0=0$；$r=0,d$ 时所有预算的对比均为零。

**证明。** 对含 $j\leq k$ 次调用的字 $U$，先只作代数上的整体标量归一化。置

$$
\widehat S=
\begin{cases}
S=I+(i-1)P,&p\leq d/2,\\
-iS=I+(-i-1)(I-P),&p>d/2.
\end{cases}
\qquad
\operatorname{rank}(\widehat S-\overline{\widehat S})=q.
\tag{IX.14}
$$

将 $U$ 中每个 $S$ 换为 $\widehat S$ 得 $\widehat U$，只改变整体相位，所以 $Q=U^\dagger RU=\widehat U^\dagger R\widehat U$。乘积差的望远镜展开以及实控制 $O=\bar O$ 给

$$
\begin{aligned}
\operatorname{rank}(\widehat U-\overline{\widehat U})&\leq jq,\\
Q-\bar Q
 &=(\widehat U^\dagger-\widehat U^T)R\widehat U
     +\widehat U^T R(\widehat U-\overline{\widehat U}),\\
\operatorname{rank}(Q-\bar Q)&\leq2jq.
\end{aligned}
\tag{IX.15}
$$

这里的标量归一化没有增添一个可调用的门。又因 $Q,\bar Q$ 都是秩 $r$ 投影，分别对它们及其补投影使用秩的次可加性，得到 $\operatorname{rank}(Q-\bar Q)\leq2h$。

令 $H=(Q-\bar Q)/2$。这是 Hermitian 矩阵，$\bar H=-H$，故每个正特征值 $b$ 的共轭特征向量具有特征值 $-b$。两个投影之差介于 $-I$ 和 $I$ 之间，因此

$$
\operatorname{rank}H=2s,\qquad
s\leq\min(jq,h)\leq t_k,\qquad
H=H_+-H_-,\qquad
0\preceq H_\pm\preceq\tfrac12 I,\quad
\operatorname{rank}H_\pm=s.
\tag{IX.16}
$$

实对称矩阵 $(Q+\bar Q)/2$ 与 $iA$ 的迹配对为零，所以 $\operatorname{tr}(\Delta Q)=\operatorname{tr}(\Delta H)$。复用定理 60.2 所用的 Fan 谱极值：对秩不超过 $s$、满足 $0\preceq C\preceq I/2$ 的矩阵，将其写成超水平谱投影的积分 $C=\int_0^{1/2}\mathbf1_{(u,\infty)}(C)\,du$。每个积分中的投影秩不超过 $s\leq m$，而 $\Delta$ 和 $-\Delta$ 的前 $s$ 个特征值都是 $a_1,\ldots,a_s$，故

$$
\operatorname{tr}(\pm\Delta C)\leq\tfrac12\sum_{v=1}^{s}a_v,
\qquad
|\operatorname{tr}(\Delta H)|\leq\sum_{v=1}^{s}a_v
 \leq\sum_{v=1}^{t_k}a_v.
\tag{IX.17}
$$

将第一项分别用于 $H_+,H_-$ 及 $\pm\Delta$，即得第二项的双向界。对全部有限字取最大值得 (IX.13)。$j=0$ 或 $h=0$ 时 $s=0$，也包含在此论证内。$\square$

**定理 66.3（有足够旁观方向时的精确有限字）。** 在定义 66.1 的合同下，若

$$
d-2h\geq q,
\qquad\text{则对每个 }k\geq0\text{ 有}\qquad
\boxed{B_k(\rho,\sigma)=\sum_{j=1}^{\min(kq,h)}a_j}.
\tag{IX.18}
$$

等号由一个含至多 $k$ 次正向 $S$ 的实际有限字取得。单调用特例与参考文稿 P.6 在 $\theta=\pi/2$ 的公式相同；多调用等式由下述原维数分批构造给出。条件 $d-2h\geq q$ 是充分条件；不以它作为必要条件。无此条件的普适等式以及任意其他固定角度的精确预算前沿，均不由本定理判定；预算仍为至多调用，不涉及恰好调用的分类。

**证明。** 若 $h=0$ 或 $k=0$，定理 66.2 已给结论。以下 $h,k\geq1$。取 (IX.12) 的实正交反对称块基，记前 $h$ 个平面为 $\operatorname{span}_{\mathbb R}\{e_v,f_v\}$，使

$$
A|_{\operatorname{span}\{e_v,f_v\}}
 =a_v\begin{pmatrix}0&1\\-1&0\end{pmatrix},
\qquad
u_v=\frac{e_v+f_v}{\sqrt2},
\qquad
R_0=\sum_{v=1}^{h}|\nu_v\rangle\langle\nu_v|.
\tag{IX.19}
$$

$h\leq m$ 保证这些平面存在，零权重也允许。令 $W$ 为它们的实正交补，$\dim W=d-2h\geq q$。这里 $W$ 是原来同一 $d$ 维系统中的方向；无额外张量因子，也不要求其初态已被置零。

置 $t=\min(kq,h)$，将 $\{1,\ldots,t\}$ 分成 $L=\lceil t/q\rceil\leq k$ 个非空批次 $J_1,\ldots,J_L$，每批大小 $b_\alpha\leq q$。在 $W$ 的一组固定实正交基中，为每批选 $q-b_\alpha$ 个方向，令 $Z_\alpha$ 是其投影，置

$$
E_\alpha=\sum_{v\in J_\alpha}|e_v\rangle\langle e_v|+Z_\alpha,
\qquad
\operatorname{rank}E_\alpha=q,
\qquad
Z_\alpha R_0=R_0Z_\alpha=0.
\tag{IX.20}
$$

不同批次的填充方向可以复用，且全部 $E_\alpha$ 在同一实基中对角，因而对易。写 $\varepsilon=1$ 当 $p\leq d/2$，否则 $\varepsilon=-1$，并令 $T_\alpha=\exp(i\varepsilon\pi E_\alpha/2)$。

任意两个同秩非平凡实投影均可由 $SO(d)$ 共轭：先取正交共轭；若行列式为负，再乘一个与目标投影对易的单方向反射即可校正行列式。这只是选取允许的实控制，不增加相位。于是存在 $O_\alpha\in SO(d)$，在 $p\leq d/2$ 时使 $O_\alpha P O_\alpha^T=E_\alpha$，在 $p>d/2$ 时使 $O_\alpha P O_\alpha^T=I-E_\alpha$。因此一次实际正向调用给

$$
V_\alpha=O_\alpha S O_\alpha^T
 =\begin{cases}
T_\alpha,&p\leq d/2,\\
iT_\alpha,&p>d/2.
\end{cases}
\tag{IX.21}
$$

第二行是同一个正向物理门的恒等式，并未免费使用 $S^{-1}$。

令 $R_h=R$ 若 $r=h$，否则 $R_h=I-R$；这是证明中对终端事件的换名，绝对概率差不变。上述实投影共轭性质给 $O_*\in SO(d)$，使 $O_*^T R_hO_*=R_0$。取实际字 $U=O_*V_L\cdots V_1$。展开 (IX.21) 并合并相邻实控制，这恰含 $L$ 次正向 $S$。整体标量在 $U^\dagger R_hU$ 中消去；每个已选平面上 $T_L\cdots T_1$ 将 $e_v$ 乘以 $e^{i\varepsilon\pi/2}$、保持 $f_v$ 不变，未选平面保持恒等。在 $W$ 上它虽可施加相位，但 $R_0$ 在那里为零。故

$$
\begin{aligned}
U^\dagger R_hU
 &=\sum_{v=1}^{t}
   \left|\frac{e^{-i\varepsilon\pi/2}e_v+f_v}{\sqrt2}\right\rangle
   \left\langle\frac{e^{-i\varepsilon\pi/2}e_v+f_v}{\sqrt2}\right|
     +\sum_{v=t+1}^{h}|\nu_v\rangle\langle\nu_v|,\\
\operatorname{tr}(\Delta U^\dagger R_hU)
 &=-\varepsilon\sum_{v=1}^{t}a_v.
\end{aligned}
\tag{IX.22}
$$

第一式的每个已选向量都是对应 $iA$ 块的特征向量，特征值 $-\varepsilon a_v$；每个未选实向量的期望为零。这也直接核对了第二式的符号与归一化。若 $R_h=I-R$，$\operatorname{tr}\Delta=0$ 只将总迹换号。因此原固定 $R$ 的绝对对比为 $\sum_{v\leq t}a_v$，与定理 66.2 上界相合。全程在原维数内给出有限乘积，不使用闭包或无限逼近。$\square$

**推论 66.4（固定读口的饱和调用数与完整迹距离）。** 保留定理 66.3 的维数条件，令 $\ell=\#\{v:a_v>0\}$、$B_\infty=\sup_{k\geq0}B_k$，并令 $K_{\mathrm{sat}}$ 是取得 $B_\infty$ 的最小非负调用预算。则

$$
B_\infty=\sum_{v=1}^{h}a_v,
\qquad
K_{\mathrm{sat}}=
 \left\lceil\frac{\min(\ell,h)}{q}\right\rceil,
\qquad
\bigl(\exists k:\ B_k=D\bigr)\ \Longleftrightarrow\ \ell\leq h.
\tag{IX.23}
$$

$\ell=0$ 时 $K_{\mathrm{sat}}=0$。这些是同一个固定读口的概率对比结论；当 $B_\infty<1$ 时并不提供一次完美区分。

**证明。** 预算 $\lceil h/q\rceil$ 已由 (IX.18) 取得前 $h$ 项之和。若 $s=\min(\ell,h)>0$，前 $s$ 项严格为正，故当 $kq<s$ 时至少遗漏第 $kq+1$ 个严格正项，而当 $kq\geq s$ 时所遗漏的前 $h$ 项全为零。这给最小预算；$s=0$ 时空字已足够。由 (IX.12)，$D-B_\infty=\sum_{v>h}a_v$，它为零当且仅当 $\ell\leq h$，包括 $h=0$ 和零差。$\square$

## 47. 同址 FIB 相位的全部预算与尖锐混态见证

**定义 67.1（全合法链上的旧盲对比）。** 固定 $n\geq3$，采用定义 55.1、假设 55.2 的整个 $\mathcal K_n$，保留 (VII.18) 的同一被动实帧 $D_n$、(VII.4) 位于物理位置对 $(1,3)$ 的同一正向相位，以及命题 59.1 的同一末端第一位置二值 PVM。以下下标 $n$ 的 $p$ 专指相位支撑秩，$r$ 专指读口秩：

$$
\begin{aligned}
d&=F_{n+2},&
p&=\operatorname{rank}(n_1n_3|_{\mathcal K_n})=F_{n-2},&
r&=\operatorname{rank}(n_1|_{\mathcal K_n})=F_n,\\
\widetilde\rho&=D_n^\dagger\rho D_n,&
\widetilde\sigma&=D_n^\dagger\sigma D_n,&
\widetilde\rho-\widetilde\sigma&=iA,\quad A\in M_d(\mathbb R),\quad A^T=-A.
\end{aligned}
\tag{IX.24}
$$

仅对满足最后一项的旧盲密度态对定义 $B_{n,k}$，即在至多 $k$ 次实际 $S_{\star,n}$、其余为任意有限纯翻转字的菜单中，最大化该同一终端事件的概率差绝对值。$D_n$ 只改变坐标，不能作为门；$n_1n_3$ 和 $n_1$ 均与它对易。定理 64.1 的 (IX.1) 已给纯翻转字恰为 $D_nSO(d)D_n^\dagger$，故这里的任意实控制均有有限原生翻转字实现，不消耗任何相位调用。相位计数使用 (IX.1) 的零相位精确实现；(IX.2) 的无预算通用性不提供给定调用预算的结论。

整个输入域是这些全链密度态对，不限定到交替编码或五维窗口，不另加辅助、参考或 CPTP 合并权限。若固定历史 $h_0$ 已给非空来源纤维 $X_{h_0}$，可将态对限于其中相容来源的端口态；优化字依赖这两个候选及共同已得记录，不能依赖未知来源标签。原生制备、取得记录的成本及一次读口不能直接返回精确概率的边界，与定义 60.1 相同。

**定理 67.2（FIB 旧盲态对的精确调用前沿）。** 对定义 67.1 的每个 $n\geq3$、每个旧盲态对和每个整数 $k\geq0$，以 (IX.12) 的 $a_v$ 表示其被动实帧差的权重，则

$$
\boxed{B_{n,k}(\rho,\sigma)
 =\sum_{v=1}^{\min(kF_{n-2},F_n)}a_v}.
\tag{IX.25}
$$

每个最大值均由同一物理相位安装上的有限字达到。若 $\ell=\#\{v:a_v>0\}$，取得无限预算固定读口值的最小调用数为

$$
B_{n,\infty}=\sum_{v=1}^{F_n}a_v,
\qquad
K_{n,\mathrm{sat}}
 =\left\lceil\frac{\min(\ell,F_n)}{F_{n-2}}\right\rceil;
\qquad
\exists k:\ B_{n,k}=D
\ \Longleftrightarrow\ \ell\leq F_n.
\tag{IX.26}
$$

零差的最小调用数为零。对整个旧盲输入域取最坏情形，固定读口饱和所需的调用数恰为

$$
\max_{\rho,\sigma\text{ 旧盲}}K_{n,\mathrm{sat}}
 =\left\lceil\frac{F_n}{F_{n-2}}\right\rceil
 =\begin{cases}2,&n=3,\\3,&n\geq4.\end{cases}
\tag{IX.27}
$$

**证明。** 相位秩与读口秩分别复用定理 58.1 的 (VII.22) 及命题 59.1；有限实控制复用定理 64.1。Fibonacci 递推给
$d-2r=F_{n-1}\geq F_{n-2}=p>0$，故 $r<d/2$，又 $p\leq r$，于是 $q=p$、$h=r$，恰满足定理 66.3 的维数条件。将该定理及推论 66.4 代入，得到 (IX.25)–(IX.26)。构造中的每个实控制用 (IX.1) 的有限纯翻转字替代；每个 $V_\alpha$ 仍只含一次位于 $(1,3)$ 的 $S_{\star,n}$，故实际调用数保持不变。

最小调用公式至多为 $\lceil r/p\rceil$。下述命题 67.3 给出全部 $m=\lfloor d/2\rfloor$ 个权重严格为正的有效旧盲密度态对；$m\geq r$，故该对达到此调用数下界。最后 $n=3$ 时 $(r,p)=(2,1)$；$n\geq4$ 时
$F_n=2F_{n-2}+F_{n-3}$ 且 $0<F_{n-3}\leq F_{n-2}$，所以 $2<r/p\leq3$，给 (IX.27)。这些比值只计相位调用，不给翻转脉冲数、持续时间或参数精度的界。$\square$

**命题 67.3（尖锐统一系数、正交混态与八维例）。** 在定义 67.1 的输入域上，令 $m=\lfloor F_{n+2}/2\rfloor$、$t=\min(kF_{n-2},F_n)$，则最佳统一下界系数为 $t/m$：

$$
\frac{t}{m}D(\rho,\sigma)
 \leq B_{n,k}(\rho,\sigma)\leq D(\rho,\sigma).
\tag{IX.28}
$$

左侧系数对每个 $n,k$ 均尖锐，包括 $k=0$。特别地，对每个 $n\geq4$，都有支撑正交、$D=1$ 的旧盲混态对，在读口无限预算饱和后仍不能达到完整迹距离。

**证明。** 当 $0<t<m$ 时，降序非负权重满足
$(m-t)\sum_{v\leq t}a_v\geq t\sum_{v>t}a_v$：将每个 $a_u\geq a_v$（$u\leq t<v$）求和即可。整理得前 $t$ 项之和至少为 $t/m$ 倍总和；$t=0,m$ 直接成立。结合 (IX.25) 得 (IX.28)。

为给出有效密度态见证，在被动实帧内任取 $m$ 个两两正交实平面，实正交单位基为 $e_v,f_v$，定义

$$
\begin{aligned}
|\psi_v^\pm\rangle&=\frac{e_v\mp i f_v}{\sqrt2},\\
\widetilde\rho_\pm
 &=\frac1m\sum_{v=1}^{m}|\psi_v^\pm\rangle\langle\psi_v^\pm|,
\qquad \rho_\pm=D_n\widetilde\rho_\pm D_n^\dagger,\\
\widetilde\rho_+-\widetilde\rho_-
 &=\frac{i}{m}\bigoplus_{v=1}^{m}
           \begin{pmatrix}0&1\\-1&0\end{pmatrix}
       \ \oplus\ 0_{d-2m}.
\end{aligned}
\tag{IX.29}
$$

每个符号下有 $m$ 个正交单位向量，故两算子均正、迹为一；两个符号的全部向量也互相正交。它们的实部同为
$\frac1{2m}\sum_v(|e_v\rangle\langle e_v|+|f_v\rangle\langle f_v|)$，所以是旧盲态对。全部 $a_v=1/m$，$\ell=m$、$D=1$，由 (IX.25) 得 $B_{n,k}=t/m$；任何更大的统一系数在此失效。奇数维时未用的一维带零本征值，仍是同一 $d$ 维系统中的合法密度态。$n\geq3$ 时 $m\geq2$，因此这些态确为混态。$n\geq4$ 时 $d-2r=F_{n-1}\geq2$，所以 $m>r$，该见证的无限预算值 $r/m$ 严格小于一；$n=3$ 则 $m=r=2$，无限预算值为一。

$n=4$ 时 $(d,p,r,m)=(8,1,3,4)$。在原合法基序中取
$(e_1,f_1)=(|0000\rangle,|0001\rangle)$、
$(e_2,f_2)=(|0010\rangle,|0100\rangle)$、
$(e_3,f_3)=(|0101\rangle,|1000\rangle)$、
$(e_4,f_4)=(|1001\rangle,|1010\rangle)$，并按 (IX.29) 先在被动实帧中定义态再共轭回物理坐标。八个字恰为全部合法长度四链，故这个选择确有四个完整实平面。此符号态对满足

$$
D(\rho_+,\rho_-)=1,
\qquad
B_{4,k}(\rho_+,\rho_-)
 =\begin{cases}
0,&k=0,\\
1/4,&k=1,\\
1/2,&k=2,\\
3/4,&k\geq3.
\end{cases}
\tag{IX.30}
$$

因此它也同时给出一次相位不能合并全部四个反对称平面、三次达到固定读口上限但仍非一次完美区分的见证。完整迹距离为一与当前固定秩读口的最大对比为 $3/4$ 相容。定理 60.2 的常数针对全部密度态对；(IX.28) 的常数针对本节旧盲子域，两者的量词域不同。$\square$

## 追加锚（本行以下为增补区）

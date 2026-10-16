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

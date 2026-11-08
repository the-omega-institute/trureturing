# Recursive relational observation: unified typed joint laws and representation transport

本卷把既有的过程残余、取得档案 law、一次运行分离和四重表示运输接到同一个带类型的联合一步合同上。它只在声明的有限或可数经典实际共同来源、闭合测试族与可测转录空间内讨论；普通数学推导不计作 Lean 核验，也不构成物理时空定律。

本卷复用 [运输、任务记忆与完成化](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) 第12、14节，[法则残余与一次运行分离](RECURSIVE_RELATIONAL_OBSERVATION_LAW_RUN_RESIDUAL.md) 及 [取得型自适应残余](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ADAPTIVE_RESIDUAL.md) 的定义。它不复制那些卷的完整证明，而只给出它们之间的桥接条件与反例边界。

## 1. 统一联合核桥：行为残余、取得法则与四重表示

前面的第12节和第14节已经分别给出四重表示的动态图册、实际共同来源上的
联合核下降，以及自然运输；取得自适应残余卷则定义了档案 law 残余和一次运行
的零误差分离。本节只补上它们之间的接口。它不另建一套四视图，也不把理论
数学推导写成 Lean 核验或物理时空定律。

### 1.1 一个合同同时承载类型、核与转录

固定有限或可数的带类型实际来源

$$
Z=\bigsqcup_{\tau\in I}Z_\tau .
$$

一个具名动作 $a:\tau\to\upsilon$ 包含其参数、权限要求和合法域
$D_a\subseteq Z_\tau$。成功后继落在 $Z_\upsilon$；失败或终止后继落在声明过的
带类型终端 $F_a$。把非法尝试、拒绝原因和权限结果也写入合同，而不是把它们
从动作菜单中静默删除。对 $z\in D_a$ 给出一步联合核

$$
J_a(z;\eta,\bar z,r),
\qquad
\sum_{\eta,\bar z,r}J_a(z;\eta,\bar z,r)=1,
\tag{UJB.7301}
$$

其中 $\eta$ 是事件或失败标签，$\bar z$ 是成功后继或固定类型终端，$r$ 是
本次真正写入的记录。$r$ 可以包含时钟增量、writer 输出、参考和权限变化；
只要某字段会影响后续选择、合法性或读数，它就必须进入 $Z$、$r$，或两者的
联合后继。所有相同接口类型的动作都放进同一个 typed action set，避免把不同
类型的后继或失败终端直接比较。

给定有限自适应策略 $\Pi$，每次观察到的 $(\eta,r)$ 都决定下一动作，直到
达到深度上限或到达终端。由 (UJB.7301) 按步推送得到完整有序转录 law，记为

$$
\operatorname{Tr}^{\Pi}_z .
\tag{UJB.7302}
$$

该对象保留事件、记录、失败、终止和类型的顺序；它不是一个可以被观察者免费
读取的完整 law 表。若把动作族限制为声明过的测试族 $\mathscr T$，则后续所有
等价、分离和运输都只对同一个 $\mathscr T$ 说话。

### 1.2 联合核细化、语义残余与档案 law 残余

先用同一合同的当前读出 $o$ 定义零步关系

$$
z\,K_0\,u\iff o(z)=o(u).
$$

对 $n\ge0$，把一步联合核推到上一层商的后继纤维，定义联合核细化候选

$$
\begin{aligned}
z\,K_{n+1}\,u\iff{}&z\,K_n\,u,\\
&\text{且对每个同类型动作 }a,\\
&\operatorname{Law}_z\bigl(\eta,[\bar z]_{K_n},r\bigr)
 =\operatorname{Law}_u\bigl(\eta,[\bar z]_{K_n},r\bigr),
\end{aligned}
\tag{UJB.7303}
$$

并且同时比较动作合法性及非法分支的失败标签。这里的等式是同一接口类型上
的联合 law 等式，不能拆成事件、后继和时钟的若干边缘等式。$K_n$ 是对
(UJB.7301) 的局部递归细化；只有在测试族对前后合法接续封闭时，才可把它用于
全部深度不超过 $n$ 的转录。

档案 law 残余则直接按所有自适应实验定义：

$$
z\,A_n^{\mathrm{law}}\,u
\iff
\forall E\in\mathscr T_{\le n},
\quad \mu_z^E=\mu_u^E .
\tag{UJB.7304}
$$

其中 $\mu_z^E$ 是实验 $E$ 的完整档案轨迹分布。式 (UJB.7304) 是 law 残余的
定义，不能被一般地替换成 (UJB.7303) 的局部核条件。联合核闭合和测试族闭合
给出一个安全方向：

$$
\boxed{K_n\subseteq A_n^{\mathrm{law}}.}
\tag{UJB.7305}
$$

在完全确定的 Dirac 核情形，且 $o$、事件、失败、记录与后继都采用同一语义
合同，$K_n$ 退化为过程几何卷的语义残余 $R_n$。若再有每个 $K_{n-1}$ 类的
continuation law 能被同一实验族统一识别（例如存在共同的可测支持分割，或
满足相应的类 law 仿射独立性），才能由 (UJB.7303) 反推出 (UJB.7304) 的
等价；没有这些可识别性条件，(UJB.7303) 只能作为充分条件。令

$$
K_\infty=\bigcap_{n\ge0}K_n,\qquad
A_\infty^{\mathrm{law}}=\bigcap_{n\ge0}A_n^{\mathrm{law}}.
\tag{UJB.7305a}
$$

因此，有限确定性、闭合测试族和共同后继解码成立时，可以得到

$$
K_n=R_n=A_n^{\mathrm{law}},
\tag{UJB.7306}
$$

但 (UJB.7306) 是带条件的特化，不是随机合同中的无条件恒等式。它也不表示
观察者已经取得了整个转录 law。

### 1.3 一次运行的分离不是等价商

固定一个实验 $E$。一次运行对有序对 $(z,u)$ 提供零误差分离，当且仅当存在
同一个转录空间中的可测集合 $H$，使

$$
\mu_z^E(H)=1,\qquad \mu_u^E(H)=0.
\tag{UJB.7307}
$$

记此性质为 $\operatorname{Sep}_E(z,u)$，并令

$$
\operatorname{Sep}_{\le n}(z,u)
\iff
\exists E\in\mathscr T_{\le n}:\operatorname{Sep}_E(z,u).
\tag{UJB.7308}
$$

它是“实验加解码器”的性质，不是配置上的等价关系。若
$z\,A_n^{\mathrm{law}}\,u$，所有深度不超过 $n$ 的实验 law 都相同，故

$$
\operatorname{Sep}_{\le n}(z,u)\Longrightarrow
z\not\!A_n^{\mathrm{law}}u.
\tag{UJB.7309}
$$

反向蕴含不成立；law 不同只说明存在统计差异。有限目标类要有一次统一解码，
必须在同一个实验上给出互不相交的支持分割，而不是对每一对目标分别挑不同
实验。若不同 law 的支持重叠，观察者可以作出有错误概率的估计，却不能从一次
记录零误差认证来源。

这也解释了几个必须保留的反例。法则残余卷的 $0.9/0.1$ noisy-bit 模型中，
两个 law 已被 $A_1^{\mathrm{law}}$ 分开，但二者的有限支持相同，所以没有
一次运行的 $\operatorname{Sep}_{\le1}$。同一卷的三个集中 law
$\{a\},\{b\},\{a\}$ 说明 $\operatorname{Sep}$ 不具传递性，不能把它再商化。
只有在 Dirac 转录、共同实验解码器以及后继合同都闭合时，law 可识别和一次
运行分离才会在该有限任务中重合。

### 1.4 四重表示必须运输同一个联合合同

令

$$
r_i:Z\to Y_i,
\qquad
i\in\{\mathrm{space},\mathrm{time},\mathrm{boundary},\mathrm{memory}\},
$$

仍使用第12节的实际表示像。联合读出满足

$$
\ker(r_{\mathrm{space}},r_{\mathrm{time}},r_{\mathrm{boundary}},r_{\mathrm{memory}})
=\bigcap_i\ker r_i.
\tag{UJB.7310}
$$

若每个页面都满足

$$
\ker r_i=K_\infty
\tag{UJB.7311}
$$

且它的合法性、selector、记录更新和 $J_a$ 都在该纤维上下降，则第12节的唯一
运输给出

$$
\chi_{ji}(r_i(z))=r_j(z),
\qquad
\chi_{ki}=\chi_{kj}\circ\chi_{ji},
\qquad
\chi_{ij}=\chi_{ji}^{-1},
\tag{UJB.7312}
$$

并满足联合核交换式

$$
K_a^j(\chi_{ji}y;\eta,\chi_{ji}y',r)
=K_a^i(y;\eta,y',r).
\tag{UJB.7313}
$$

若采用概率档案边界，则 (UJB.7311) 应改为相应的 $A_\infty^{\mathrm{law}}$
商，并且每页都须满足 law 核和选择器的因子化。只把四个当前数值拼成一个
tuple，不能替代 (UJB.7313)。四页联合可以完整而单页不递归；TM §12.4 的
三态反例正是这种情形。

时间页还必须说明保留的对象。标量累计量 $\tau$ 是有序转录的一个加法投影，
一般不能恢复分支图中的执行顺序；已有 typed residual cocycle 卷中的 $ab$ 与
$ba$ 反例说明，必须保留有序 transcript、非交换运输或足够强的历史摘要。
只有在有限强连通残余图是单一具名有向环、且单圈增量非零时，终点与加法
累计量才具有该卷所述的精确逆性质。

数学上的 $\chi_{ji}$ 也不是免费的内部恢复器。要让它成为观察者的合法操作，
还须声明输入可读、计算与参考成本已进入记忆合同、恢复后的页面仍在合法域内，
以及权限和档案更新都满足 (UJB.7313)。完整 law 表、未执行的未来 transcript
或系统外选择器都不能作为隐藏输入。

### 1.5 统一桥的可检验边界与反例目录

这套桥接只在下列范围内声称精确：有限或可数经典来源、声明的 typed action
menu、实际共同来源、对前后接续封闭的测试族，以及联合核和转录空间具有所需
的可测结构。以下对象仍需另行处理：近似核及误差传播、无限目标族的统一
可测分割、非闭合动作族、量子通道、以及把数学运输实现为有限资源程序的成本。

用于检查边界的最小反例包括：

* LAW_RUN §3 的 noisy-bit：law 不同但有限支持重叠，故统计可辨识不等于一次
  零误差取得；
* TM §14.2 的对角合法域：常值摘要的纤维同时含合法和非法输入，合法性不能
  下降；
* RA.1405 的事件—时钟联合核：各边缘相同而联合关系不同，边缘运输不充分；
* LAW_RUN §1.6 的三集中 law：一次分离关系不传递；
* TM §12.4 的三态四页模型：联合读出可单射而每个单页都可能不递归；
* typed residual cocycle 卷的分支路径：终点和标量时间相同而顺序不同。

所以统一对象不是一个更大的坐标，而是同一实际来源上的一个 typed joint law、
一个任务行为商、一个有序转录，以及四个满足下降和自然运输条件的表示。空间、
时间、边界和记忆只有在这些交换条件成立时，才是同一关系过程的可互相恢复表达。

## 追加锚（本行以下为增补区）

## 2. 有限实际探针的联合行逆

### 2.1 来源、商类与可执行探针

固定有限的事件—记录字母表 $B$、终止字母表 $T$、探针字母表 $\mathcal A$，以及
一个有限的已实现后继商

$$
C=\{1,\ldots,m\},\qquad m\ge 2.
$$

一次首动作的完整行由一个概率分布 $\rho$ 给出。它的质量分别写成
$\rho(b,c)$ 和 $\rho(b,t)$，其中 $(b,c)\in B\times C$ 是带有首事件和整条首记录的
成功后继，$(b,t)\in B\times T$ 是带有同一首记录的终止后继。$b$ 必须包含合法性、
拒绝原因和权限结果等会影响后续选择或解释的字段；若这些字段不能被写入 $b$，
下文只在所有候选来源共有的合法域上成立。终端 $t$ 不与任何 $c$ 合并。

固定首动作前已经取得的档案；以下各行 $\rho$ 都在这个共同初始条件下比较。
令 $S_{\mathrm{actual}}$ 为所有成功后可达的实际状态（包括带完整档案的实际配置），
并令 $q:S_{\mathrm{actual}}\to C$ 为把实际状态或配置映射到其已实现后继商类的商映射。
首动作成功后的实际状态记为 $S_0$，令 $C_0=q(S_0)$。$H_0$ 是此时的完整
已取得上下文，包含旧档案和首记录 $b$。连续调用同一个长度为 $L$ 的宏探针
$\mathsf P$；$W_j\in\mathcal A^L$ 是第 $j$ 次调用实际写入的完整有序事件—记录词，
$S_j$ 和 $H_j$ 分别是调用后的实际状态与完整已取得上下文。特别地，$H_j$
保留 $H_0,W_1,\ldots,W_j$，不覆盖、删除或重排已有记录。

令 $\mathcal F_j$ 为到第 $j$ 次调用结束为止的实际过去所生成的滤过，包含
$S_0,\ldots,S_j$、$H_0,\ldots,H_j$ 以及这些调用的全部记录、控制状态和权限。
$\mathcal F_0$ 是第一次探针之前的实际过去，$\mathcal F_{j-1}$ 是第 $j$ 次
探针的调用前信息。这里包含实际状态只是为了陈述来源核的条件，不赋予观察者
读取隐藏类或完整 law 的操作。每个允许的实际代表元和每个允许的调用前历史
上的来源转移核都须满足同一个点态校准律，其条件期望写法是

$$
\Pr(W_j=w\mid\mathcal F_{j-1})=P_{C_0}(w),
\qquad w\in\mathcal A^L,\quad 1\le j\le r.
\tag{UJB.7401}
$$

其中 $P_c$ 与代表元和实际过去无关；零概率历史处采用所声明的点态转移核，
不对零概率事件作条件除法。每次宏探针在所有支持分支上合法，每一个支持结果
都满足 $q(S_j)=C_0$，且权限允许下一次所需调用；完整的实际状态和完整记录
仍被保留。这一来源条件约束的是给定实际过去的下一输出，而不只是各次调用
未经历史条件化的边缘律。

由此，对每个有正概率的初始条件 $(C_0,H_0)=(c,h_0)$，

$$
\Pr(W_1=w_1,\ldots,W_r=w_r\mid C_0=c,H_0=h_0)
 =\prod_{j=1}^rP_c(w_j).
\tag{UJB.7402}
$$

确实，令 $D_{k-1}=\{W_1=w_1,\ldots,W_{k-1}=w_{k-1}\}$，其中 $D_0$ 是全空间。
它属于 $\mathcal F_{k-1}$，而 $C_0,H_0$ 属于 $\mathcal F_0$。条件期望的塔式律给出

$$
\begin{aligned}
&\Pr(D_{k-1},W_k=w_k\mid C_0,H_0)\\
&\quad=\mathbb E\!\left[
 \mathbf1_{D_{k-1}}\Pr(W_k=w_k\mid\mathcal F_{k-1})
 \mid C_0,H_0\right]\\
&\quad=P_{C_0}(w_k)\Pr(D_{k-1}\mid C_0,H_0).
\end{aligned}
$$

对 $k$ 归纳即得 (UJB.7402)。即使 $H_{k-1}$ 已经保留早先输出，该推导仍然
成立；整向量的乘积律只在初始条件下陈述，不以生成了这些输出的后续历史
再次条件化。它不允许克隆来源、重置到一个隐藏类端口、免费取得校准样本，
或把被探针消耗的权限重新当作仍然存在。

写

$$
\Delta=\min_{c\ne d}d_{\mathrm{TV}}(P_c,P_d)>0,
\qquad
d_{\mathrm{TV}}(\mu,\nu)=\frac12\sum_x|\mu(x)-\nu(x)|.
\tag{UJB.7403}
$$

这里的总变差是有限字母表上的通常归一化距离。给定 $r=m-1$ 次宏探针，
(UJB.7402) 对 $H_0$ 的一致性允许在每个首记录和成功类上求和；终止分支不再
调用探针。因此首动作与后续档案的联合 law 为

$$
\begin{aligned}
\mathcal M_\rho(b,\mathsf{term},t)&=\rho(b,t),\\
\mathcal M_\rho(b,\mathsf{succ},w_1,\ldots,w_r)
 &=\sum_{c\in C}\rho(b,c)\prod_{j=1}^rP_c(w_j).
\end{aligned}
\tag{UJB.7404}
$$

它保留 $b$ 与 $c$ 的联合关系、每个终端的身份和每一个实际写入的探针词。

### 2.2 有界逆与精确行恢复

**引理 2.1（有限类的有界探针逆）。** 在 (UJB.7401)--(UJB.7404) 的条件下，
$\mathcal M_\rho$ 唯一决定 $\rho$，并且对任意两个允许的首行动作行
$\rho,\rho'$ 有

$$
d_{\mathrm{TV}}(\rho,\rho')
 \le \min\left\{1,
m\Delta^{-(m-1)}d_{\mathrm{TV}}(\mathcal M_\rho,\mathcal M_{\rho'})\right\}.
\tag{UJB.7405}
$$

**证明。** 对每一对 $c\ne d$，从有限字母表的总变差定义选取
$f_{cd}:\mathcal A^L\to[0,1]$，使

$$
\mathbb E_{P_c}f_{cd}-\mathbb E_{P_d}f_{cd}
 =d_{\mathrm{TV}}(P_c,P_d)\ge\Delta.
$$

令 $g_{cd}=f_{cd}-\mathbb E_{P_d}f_{cd}$。于是 $|g_{cd}|\le1$，
$\mathbb E_{P_d}g_{cd}=0$，且 $\mathbb E_{P_c}g_{cd}\ge\Delta$。把
$C\setminus\{c\}$ 任意双射到 $\{1,\ldots,r\}$，定义

$$
h_c(w_1,\ldots,w_r)=\prod_{d\ne c}g_{cd}(w_{\iota_c(d)}).
$$

由 (UJB.7402)，对 $k\ne c$，$P_k^{\otimes r}$ 下至少一个因子（$d=k$）均值为零，故

$$
\mathbb E_{P_k^{\otimes r}}h_c=0\quad(k\ne c),
\qquad
\alpha_c:=\mathbb E_{P_c^{\otimes r}}h_c\ge\Delta^r.
\tag{UJB.7406}
$$

这给出一个显式的有界对偶读出，而不需要写出未界的矩阵逆。任意
$F:B\times(C\sqcup T)\to[-1,1]$ 定义一个复合记录上的函数 $G_F$：在终端
$(b,\mathsf{term},t)$ 上取 $F(b,t)$，在成功记录上取

$$
G_F(b,\mathsf{succ},w_1,\ldots,w_r)
 =\sum_{c\in C}F(b,c)\frac{h_c(w_1,\ldots,w_r)}{\alpha_c}.
$$

因此 $|G_F|\le m\Delta^{-r}$，并由 (UJB.7406) 得

$$
\mathbb E_{\mathcal M_\rho}G_F=\mathbb E_\rho F.
$$

取 $F$ 遍历 $[-1,1]$ 中的函数，有限集上的对偶表述给出未归一化变差范数
的界
$\|\rho-\rho'\|_1\le m\Delta^{-r}\|\mathcal M_\rho-\mathcal M_{\rho'}\|_1$；
两边除以 $2$ 即得 (UJB.7405)，再用概率距离不超过 $1$ 截断。若两份复合 law
相等，所有 $F$ 的期望都相等，故首行（包括每个终端）相等。证毕。

这个证明也说明为什么必须保留首事件和首记录：若只保留后继的边缘 law，
$F(b,c)$ 的联合测试就不再能被 $G_F$ 实现。宏的实际动作数至多为

$$
1+rL=1+(m-1)L,
\tag{UJB.7407}
$$

首动作一次，随后每个类保持宏各执行一次。$m=1$ 时没有分离问题，首行动作 law
本身就是行，取 $r=0$ 可得到直接读出；(UJB.7403)--(UJB.7406) 专用于 $m\ge2$。

### 2.3 交替二项族：阶数和指数都是尖锐的

**定理 2.2（持久 Bernoulli 反例）。** 令 $r=m-1$，取

$$
0<p<1,
\qquad 0<\delta<\frac{\min\{p,1-p\}}{r},
\qquad p_i=p+i\delta\quad(0\le i\le r).
$$

有 $m$ 个持久发射类 $E_i$。完整配置为 $(E_i,h)$ 或 $(R_\pm,h)$，其中 $h$
是完整有序的已取得档案。长度一的探针在每个 $(E_i,h)$ 上都合法，权限保持
可继续调用，其完整增量记录由探针名和输出位 $w$ 组成，转移为

$$
(E_i,h)\xrightarrow[\ p_i^w(1-p_i)^{1-w}\ ]{\mathsf P,w}
(E_i,h\mathbin{\|}(\mathsf P,w)),\qquad w\in\{0,1\}.
$$

这里 $\|$ 是向有序档案尾部追加，$q(E_i,h)=i+1$；固定的动作名可从 $W_j$
的字母中省写。两个根 $R_+$、$R_-$ 的首动作都写入同一个标记 $b_\ast$，将
$(a,b_\ast)$ 追加到原档案尾部，随后分别按

$$
\alpha_i=\begin{cases}2^{1-r}\binom ri&i\text{ 偶},\\0&i\text{ 奇},\end{cases}
\qquad
\beta_i=\begin{cases}0&i\text{ 偶},\\2^{1-r}\binom ri&i\text{ 奇}
\end{cases}
\tag{UJB.7408}
$$

选择后继 $(E_i,h\mathbin{\|}(a,b_\ast))$；选择出的隐藏下标 $i$ 不写入首记录。
则 $d_{\mathrm{TV}}(\alpha,\beta)=1$，而根的首标记加上 $k$ 个
探针输出的 law 在 $k<r$ 时完全相同，在 $k=r$ 时满足

$$
d_{\mathrm{TV}}(\mathsf{Law}_{R_+}(b_\ast,W_1,\ldots,W_r),
                 \mathsf{Law}_{R_-}(b_\ast,W_1,\ldots,W_r))
 =r!\,\delta^r.
\tag{UJB.7409}
$$

**证明。** 在每个实际调用前配置 $(E_i,h)$ 上，下一位的来源核恰为
$p_i^w(1-p_i)^{1-w}$，与已经保留的 $h$ 无关；后继保留同一个 $i$ 和完整档案。
因此即使 $h$ 含有全部早先输出，仍有
$\Pr(W_j=w\mid\mathcal F_{j-1})=p_i^w(1-p_i)^{1-w}$，这逐历史实现了
(UJB.7401)。由塔式推导的 (UJB.7402)，给定首动作后的 $E_i,H_0$，词 law
是 Bernoulli 乘积。因为 $0<p_i<1$，每个有限位前缀都有正概率，故这也直接
覆盖每个可达的保留历史。所有有限次探针都可在同一来源上接续，没有重置或
删档；首动作 law 的终端质量为零，$L=1$ 且 $\Delta=\delta$。

偶数项和奇数项的二项式系数都为 $2^{r-1}$，所以 (UJB.7408) 是两
个互不相交的概率分布。对一个长度为 $k$、含有 $s$ 个 $1$ 的词 $x$，其在
$E_i$ 下的概率是

$$
Q_x(i)=(p+i\delta)^s(1-p-i\delta)^{k-s},
$$

这是 $i$ 的次数不超过 $k$ 的多项式。有限差分恒等式

$$
\sum_{i=0}^r(-1)^i\binom ri i^j=0\quad(0\le j<r),
\qquad
\sum_{i=0}^r(-1)^i\binom ri i^r=(-1)^r r!
\tag{UJB.7410}
$$

说明当 $k<r$ 时两个混合 law 的每个词概率相同。令 $k=r$。$Q_x$ 的最高次
系数是 $\delta^r(-1)^{r-s}$，故由 (UJB.7408) 和 (UJB.7410)，每一个词的
两根概率差的绝对值都是

$$
2^{1-r}r!\delta^r.
$$

共有 $2^r$ 个词，半个 $\ell^1$ 和正好给出 (UJB.7409)。因此最先可能的
探针数是 $r=m-1$，而差异的首项确实是 $\delta^r$。令 $\delta\downarrow0$，
任何只依赖较低次 $\delta$ 的统一逆界都会被这个族否定；(UJB.7405) 的指数
不能普遍降低。证毕。

任意在固定上限 $k$ 内依据已见词自适应停止、并把停止标记写入档案的策略，
都是完整长度 $k$ 词 law 的一个共同 Markov 推送（可用填充符把短词补到长度
$k$）。数据处理不等式说明这种停止 law 的总变差不超过完整词 law 的总变差。
故在 $k<r$ 时它仍完全相同，在 $k=r$ 时也不超过 (UJB.7409)；停止规则不能
绕过交替二项式的消去。

### 2.4 结构细化与取得 law 的错位

令 $S_{\mathrm{core}}=\{R_+,R_-,E_0,\ldots,E_r\}$ 是同一族的有限根—发射核，
$\pi$ 是从完整配置 $(x,h)$ 到 $x$ 的投影。在这个有限核上取 UJB.7303 的
结构核链 $K_n^{\mathrm{core}}$，并把一个发射类的一步 Bernoulli law 作为
探针动作的联合记录。当前读出只区分“根”和“发射类”角色，所以所有 $E_i$ 先在
同一类中，且 $R_+$、$R_-$ 也同类。由于 $p_i$ 两两不同，$E_i$ 的一步联合 law
在 $K_1^{\mathrm{core}}$ 已互相分开；根的首动作在 $K_0^{\mathrm{core}}$ 商上仍
只看到同一个发射类，故两个根在 $K_1^{\mathrm{core}}$ 仍相等。到了
$K_2^{\mathrm{core}}$，首动作的后继分布落在 $K_1^{\mathrm{core}}$ 的单点发射类上，
偶数支撑和奇数支撑互不相交，两个根分开。因此

$$
K_2^{\mathrm{core}}=\operatorname{diag}(S_{\mathrm{core}}).
$$

完整配置上的对应链 $\widetilde K_n$ 采用同一角色读出和每步实际新增的记录；
完整旧档案继续保留，并供后续策略使用。合法性、下一增量记录及后继核投影都
只依赖 $\pi$，而追加档案不改变核心后继。由 (UJB.7303) 归纳，

$$
\widetilde K_n=(\pi\times\pi)^{-1}(K_n^{\mathrm{core}}),
\qquad
\widetilde K_2=\ker\pi=\widetilde K_3=\cdots.
$$

所以第二层的对角断言只在有限核上成立；$(E_i,h)$ 与 $(E_i,h')$ 在 $h\ne h'$
时仍是不同的完整配置。若把整份旧档案额外纳入当前读出，则零步关系已经改变，
不属于这里的角色读出链。

从两根上相同的初始档案出发，取得 law 链看到的完整新增记录是 $b_\ast$ 和
持久发射输出；在前面加上共同的旧档案不改变 law 相等性或总变差。总动作数为
$n=1+k$ 时，
(UJB.7410) 给出

$$
R_+\,A_n^{\mathrm{law}}\,R_-
\quad(1\le n\le m-1),
\qquad
R_+\not\!A_m^{\mathrm{law}}R_-.
\tag{UJB.7411}
$$

所以有限核及其上述提升链的结构稳定指数为 $2$ 并不限制取得 law 的平台长度；在这组实际来源中，
平台可一直持续到总根加探针 horizon $m$。这不是对既有 $K_n\subseteq A_n^{\mathrm{law}}$
的改写，而是一个达到该包含方向极限的有限见证。

### 2.5 接回四视图及不可恢复边界

引理 2.1 只恢复一个实际首行及其终端部分。把恢复的行重新放回
(UJB.7301) 的 typed joint law 后，只有当合法性、selector、记录更新和后继都
沿同一商纤维下降，才可继续使用 (UJB.7310)--(UJB.7313) 的四视图运输。于是
空间、时间、边界、记忆仍必须是同一实际共同来源上的四个因子；恢复首行并不
推出 $K_n=A_n^{\mathrm{law}}$ 的全层恒等，也不推出物理时空的本体恢复。

有三类边界必须保留。第一，若探针会破坏 $c$、使所需后续调用不再合法，或只有
单次边缘校准而不满足给定实际过去的 (UJB.7401)，则没有本章的来源保证，不能
据此推出 (UJB.7402) 或把相同边缘律乘成张量 law。第二，若
合法性或拒绝原因藏在不可见字段，(UJB.7405) 只能在声明的共同合法范围内使用，
不能把非法分支静默合并。第三，即使行 law 已由引理唯一确定，重叠支持的一个
有限实际记录仍不能零误差识别隐藏的 $c$；那是 law 级统计逆，不是一次运行的
历史恢复。只有额外的互不相交支持或等价的可测分割，才会回到 UJB.7307--7309
所讨论的零误差边界。

这也说明本桥没有新增 checkpoint 原语：当前增量只用了已经允许的首动作、实际
返回的 class-preserving 宏和完整档案。改变探针成为破坏性的操作、隐藏合法性，
或把未取得的完整 law 当作输入，都会越过本章的假设。

### 2.6 相关文献与使用范围

Vandermeulen--Scott 的 [Lemma 5.3](https://arxiv.org/html/1607.00071v2) 证明
两两不共线的 $m$ 个非零 Hilbert 向量的 $(m-1)$ 次张量幂线性无关；它给出本章
“有限类需要有限张量阶”的已知背景。本章的有界读出直接用 (UJB.7406) 的乘积
测试函数，因此没有把该文的未知混合分解定理冒充为本行逆。

Berrut--Trefethen 的 [barycentric interpolation, §2](https://people.maths.ox.ac.uk/trefethen/barycentric.pdf)
给出已知互异节点的 Lagrange 插值读出；(UJB.7410) 的交替二项式计算是其在
等距 Bernoulli 节点上的显式有限差分版本，而不是新的一般插值定理。

Bian--Abate 的 [Theorem 6 and Figure 1](https://arxiv.org/html/1701.04547v3)
展示概率 Markov 链中 branching/bisimulation 与有限 trace law 之间的结构—取得
差距及总变差界。本章的持久混合族把这个差距落实为同一 typed row 上的精确阶数
和精确常数；它不声称解决该文的一般近似模型问题。

## 2.99 追加锚

## 3. Joint square/cube acquisition for the published finite groups

### 3.1 The conditional source interface and its actual relation

**Definition 3.1 (one source and total paid samples).** Fix one hidden
$i\in\{0,1\}$ throughout a run and use exactly the groups $S_i$ of
[FINITE_GROUP_POWER_MAP_SEPARATION, Definition 1.2 and Theorem 1.3](FINITE_GROUP_POWER_MAP_SEPARATION.md).
Write $O_6(S_i)$ for their order-six elements. Each paid draw satisfies

$$
\Pr(x_j=x\mid i,\text{actual past})=\frac1{1944}
\quad(x\in O_6(S_i)).
\tag{UJB.7501}
$$

A supplied legal, nondestructive same-source fork/read returns opaque
references $a_j=x_j^2$ and $t_j=x_j^3$ from that very draw. The observer
may retain these references and compare stable equality within each
endpoint type, including against old references. Coordinates, names,
cross-type comparisons, multiplication, inverse, conditioning the sampler
and reset are unavailable. Initialization, control, private randomness,
permissions and any refusal or timing information are source-blind;
permission to draw and compare persists. The only source-dependent
observations are the stated typed equalities. Any old source-dependent
records must come from this same contract and their draws count in the
total $n$; changing the current batch does not erase their cost.

The complete equality record is $H_n=(\pi_A,\pi_T)$, two partitions of
the same ordered index set $[n]$, with $j\sim_A k$ iff $a_j=a_k$ and
$j\sim_T k$ iff $t_j=t_k$. Thus $n$ counts all acquired samples, not
live storage, comparisons, elementary native actions or elapsed time.

**Proposition 3.2 (the actual witnessed-relation adapter).** Put
$F=\mathbb F_3$, $V=F^2$, $W=F^3$, $Z=F^2$, and retain the source maps

$$
\begin{aligned}
B_0(v,w)&=(v_1w_1+v_2w_2,\ v_1w_2+v_2w_3),\\
B_1(v,w)&=(v_1w_1-v_2w_2,\ v_2w_1+v_1w_2).
\end{aligned}
$$

Let $A=(V\setminus\{0\})\times Z$ and $T=W\times Z$, interpreted in
$S_i$ as $a=(v,0,s;0)$ and $t=(0,w,z;1)$. The endpoint map is a bijection

$$
\begin{aligned}
O_6(S_i)&\longrightarrow E_i\subseteq A\times T,\\
x&\longmapsto(x^2,x^3),\\
E_i&=\{((v,s),(w,z)):v\ne0,\ B_i(v,w)=s\}.
\end{aligned}
\tag{UJB.7502}
$$

The simple typed incidence graph $G_i=(A,T,E_i)$ has

$$
|A|=72,\quad |T|=243,\quad d_A=27,\quad d_T=8,\quad M:=|E_i|=1944.
\tag{UJB.7503}
$$

Consequently (UJB.7501) becomes conditionally iid uniform edge sampling
from $G_i$, with every witness and edge having mass $1/M$.

Proof. The group construction and order classification are those of the
cited source, §§2–3; no new group construction is needed. Substitution
in its multiplication gives, for $x=(u,w,c;1)$ with $u\ne0$,

$$
x^2=(2u,0,-B_i(u,w);0),\qquad
x^3=(0,w,c+B_i(u,w);1).
$$

Set $v=2u$, $s=-B_i(u,w)$, $z=c+B_i(u,w)$. Bilinearity gives
$B_i(v,w)=s$. Conversely every pair in (UJB.7502) has the unique preimage
$x=(2v,w,z+s;1)$: here $B_i(2v,w)=2s=-s$, so substitution returns both
specified endpoints. Mathematically the same inverse is $x=a^2t$; it
is used only to prove the bijection and grants no observer operation.
For each nonzero $v$, the source proves $B_i(v,-):W\to Z$ has rank two,
hence exactly three solutions for every $s$. There are nine free $z$
values, giving degree $27$ on $A$; every $(w,z)$ has exactly one neighbor
for each of the eight nonzero $v$, giving degree $8$. This proves
(UJB.7503) and the uniform pushforward. In particular all three $w$
coordinates remain: $w_3$ is free for $B_1$, not deleted.

In the [base witnessed relation, Definition 1.2](RECURSIVE_RELATIONAL_OBSERVATION.md),
the witness set is $O_6(S_i)$ and its two endpoint maps are these powers.
Here each endpoint pair has exactly one witness; passing to the support
therefore loses no witness multiplicity. Repeated draws still give
indexed edge occurrences, each of mass $1/M$, and must not be collapsed
when computing sample probabilities. $\square$

### 3.2 Complete law equality through three and the first difference

**Theorem 3.3 (exact first total sample horizon).** Under Definition 3.1,
the complete laws of $H_n$ for $S_0,S_1$ agree for every $0\le n\le3$
and differ for every $n\ge4$. The same equality through three holds for
any common adaptive comparison, retention and stopping protocol with
that total sample cap. At four define

$$
\begin{aligned}
R&=\{a_1=a_2,\ a_3=a_4,\ t_1=t_4,\ t_2=t_3\},\\
R_{\mathrm{str}}&=R\cap\{a_1\ne a_3,\ t_1\ne t_2\}.
\end{aligned}
$$

Their exact probabilities are

$$
\begin{aligned}
\Pr_0(R)&=\frac1{68024448},&
\Pr_1(R)&=\frac1{34012224},\\
\Pr_0(R_{\mathrm{str}})&=\frac{37}{3673320192},&
\Pr_1(R_{\mathrm{str}})&=\frac{91}{3673320192}.
\end{aligned}
\tag{UJB.7504}
$$

Proof. For prescribed within-type equalities on $[n]$, make a typed
bipartite multigraph $F$ whose vertices are the required equality blocks
and whose edge $j$ joins its two blocks. Satisfying edge sequences are
exactly type-preserving homomorphisms $F\to G_i$, so the probability is
$\operatorname{hom}_{\mathrm{type}}(F,G_i)/M^n$. Parallel edges impose
the same incidence constraint and can be collapsed in the numerator;
the denominator retains the original exponent $n$. For $n\le3$ the
resulting simple bipartite graph is a forest without isolated vertices.
A connected tree with $\ell$ left and $r$ right vertices has exactly

$$
M\,8^{\ell-1}27^{r-1}
\tag{UJB.7505}
$$

typed homomorphisms: choose one root edge in $M$ ways, then extend
outward, with eight choices for each new left vertex and $27$ for each
new right vertex. Collisions are permitted in a homomorphism, so no
additional exclusions arise. Multiply over components. These counts
are the same for both sources. An exact atom $H_n=(\pi_A,\pi_T)$ also
excludes every equality between different blocks within each type.
Expand the product of these inequality indicators by finite
inclusion-exclusion. Each term merely coarsens the equality blocks and
still has at most $n$ edges, so every term has equal probability for the
two sources. This proves equality of every atom and hence the whole law;
$n=0$ is immediate. This is the finite typed specialization of the
homomorphism/injectivity counting method of Lovász–Szegedy, §§2.1, 2.4
[LS](https://arxiv.org/abs/math/0408173v2); absent cross-edges are not
required, so these are not induced-subgraph counts.

For the four-edge cycle, let $c_i(t,t')$ count common left neighbors.
For $t=(w,z)$, $t'=(w',z')$, and $d=w-w'$, (UJB.7502) gives

$$
c_i(t,t')=|\{v\ne0:B_i(v,d)=0\}|=3^{2-\operatorname{rank}L_i(d)}-1,
$$

where the matrices of $L_i(d):v\mapsto B_i(v,d)$ are

$$
L_0(d)=\begin{pmatrix}d_1&d_2\\d_2&d_3\end{pmatrix},\qquad
L_1(d)=\begin{pmatrix}d_1&-d_2\\d_2&d_1\end{pmatrix}.
$$

For $L_0$, rank zero occurs only at $d=0$. Among nonzero $d$, rank one
occurs in six cases with $d_1\ne0$, where $d_3=d_2^2/d_1$, and in two
cases with $d_1=d_2=0$, $d_3\ne0$. Thus the rank multiplicities are
$(1,8,18)$. For $L_1$, $d_1^2+d_2^2$ vanishes in $F$ exactly when
$d_1=d_2=0$. Retaining all three values of $d_3$ gives rank
multiplicities $(3,0,24)$. For each $d$, ordered $(t,t')$ have
$27\cdot9^2=2187$ realizations, including any diagonal pairs. Therefore

$$
\begin{array}{c|rrr}
 &c=0&c=2&c=8\\ \hline
G_0&39366&17496&2187\\
G_1&52488&0&6561
\end{array}
\tag{UJB.7506}
$$

counts all $243^2$ ordered pairs. The two left neighbors in $R$ may be
chosen independently, giving
$H_i:=\sum_{t,t'}c_i(t,t')^2$, with $(H_0,H_1)=(209952,419904)$.
For the strict event use
$Q_i:=\sum_{t\ne t'}c_i(t,t')(c_i(t,t')-1)$.
Now $\sum_{t,t'}c_i(t,t')=72\cdot27^2=52488$, while each of the
$243$ diagonal pairs has $c_i(t,t)=8$. Hence

$$
Q_i=H_i-52488-243\cdot8\cdot7,\qquad
(Q_0,Q_1)=(143856,353808).
\tag{UJB.7507}
$$

Divide these ordered counts by $M^4$, without an automorphism divisor,
to obtain (UJB.7504). Projection to the first four draws proves
inequality for every $n\ge4$.

Finally every allowed protocol capped at $n$ is a common randomized
function of $H_n$: retain only its requested comparisons and records,
and follow its source-blind control and coins. For this mathematical
coupling one can pre-generate $n$ edges and expose the requested prefix;
unexposed draws supply no free observations or reset. Equal full laws
therefore imply equal bounded adaptive transcript laws. $\square$

### 3.3 Which acquired information can be recovered

**Proposition 3.4 (single charts and an actual pairing-erasure boundary).**
Either single chart has the same equality law under both sources for
all $n$. Nevertheless, erasing the matching of the two charts need not
erase every distinction: at $n=4$, retain only the two occupancy counts
$k_A=|\{a_1,\ldots,a_4\}|$, $k_T=|\{t_1,\ldots,t_4\}|$. Then

$$
\Pr_0(k_A=k_T=2)=\frac{10183}{3673320192},\qquad
\Pr_1(k_A=k_T=2)=\frac{10507}{3673320192}.
\tag{UJB.7508}
$$

Proof. Biregularity makes the $a_j$ iid uniform on $72$ points and the
$t_j$ iid uniform on $243$ points. For either chart on $m$ points, any
specified exact partition with $k$ blocks has probability $(m)_k/m^n$,
where $(m)_k=m(m-1)\cdots(m-k+1)$, or zero if $k>m$.
This proves the single-chart assertion at every horizon.

For the joint occupancy event, the actual used edge support must be
two disjoint edges, a three-edge path, or a four-edge $K_{2,2}$. The
numbers of the first two support types are common:

$$
D=\frac{M(M-34)}2=1856520,\qquad
P=M\cdot26\cdot7=353808.
$$

Indeed from one edge remove itself, its $26$ other left-incident edges
and its seven other right-incident edges to count disjoint pairs, then
divide by two. A three-edge path has a unique middle edge; choose its
two extensions in $26$ and seven ways. This counts the chosen support
even if a fourth, unused edge exists in $G_i$. Each two-edge support
has $2^4-2=14$ length-four sequences using both edges; each three-edge
support has $3^4-3\cdot2^4+3=36$ using all three; each four-edge support
has $4!=24$. By (UJB.7507) there are $Q_i/4$ such $K_{2,2}$ supports
(the factor four chooses the ordered two left and two right vertices).
Thus the occupancy numerator is

$$
14D+36P+6Q_i=
\begin{cases}39591504&i=0,\\40851216&i=1.\end{cases}
$$

Division by $1944^4$ proves (UJB.7508). The separate occupancy laws
agree, but their joint law differs even without index matching. $\square$

**Proposition 3.5 (historical sufficiency does not give kernel descent).**
$H_n$ retains all past equality answers up to independent renaming of
attained endpoint values. It need not make the next-observation kernel
constant on actual-history fibers, even within $S_0$.

Proof. Two endpoint lists have the same partition pair exactly when
bijections between their attained left values and between their attained
right values match every indexed occurrence. These bijections extend to
the respective finite endpoint sets of the same sizes. Thus every
function of acquired equalities factors through $H_n$, with no claim
that these arbitrary renamings preserve $E_i$ or future behavior.

For the actual failure of predictive descent in $G_0$, take

$$
\begin{aligned}
a&=((1,0),(0,0)),& b&=((0,1),(0,1)),\\
t_0&=((0,0,0),(0,0)),& t_+&=((0,0,1),(0,0)),&
t_-&=((1,0,1),(0,0)).
\end{aligned}
$$

The histories $[(a,t_0),(b,t_+)]$ and $[(a,t_0),(b,t_-)]$ consist of
legal edges: $B_0((1,0),0)=0$ and
$B_0((0,1),(0,0,1))=B_0((0,1),(1,0,1))=(0,1)$.
Both histories have two singleton blocks in each chart. But
$B_0((1,0),(0,0,1))=(0,0)$ whereas
$B_0((1,0),(1,0,1))=(1,0)$. Conditioned on these actual histories,
$\Pr(a_3=a_1,t_3=t_2)$ is respectively $1/1944$ and $0$.
Both conditioning events have positive mass. Therefore a pointwise
predictive quotient cannot be inferred from historical sufficiency.
Averaging over compatible embeddings when conditioning only on the
observed $H_2$ is a different operation; it does not contradict
Theorem 3.3 or prove the joint-kernel descent of (UJB.7313). $\square$

**Proposition 3.6 (blocks and finite certainty).** For fixed $i$, internal
partition patterns of disjoint consecutive four-draw blocks are iid
with law $H_4$, conditionally on every actual past before those blocks.
Each block costs four further samples. Equality-history increments
need not be iid. No deterministic finite total sample cap permits
zero-error identification of $i$; known support size $M$, persistent
permissions and unbounded paid sampling with retention do permit
almost-surely finite zero-error identification.

Proof. Repeated conditioning in (UJB.7501) gives the product uniform
law for any finite future edge sequence given its actual past. Applying
the internal-partition map separately to disjoint blocks gives the
claimed conditional product law. This is conditional on the fixed
source; mixing over an unknown $i$ need not preserve independence.
For a simple failure of iid equality increments, the event that a new
square has appeared is certain at draw one and has probability $71/72$
at draw two. Comparisons against old blocks also depend on retained
history. Proposition 3.5 gives a further predictive obstruction.

For any deterministic cap $N\ge1$, the full transcript in which all
$N$ edges repeat one edge is common to both sources and has probability
$M^{1-N}>0$ under each. On it a common bounded protocol has the same
coin and output law under both sources, so cannot identify both
correctly with probability one. The empty transcript handles $N=0$.

Conversely let $\tau$ be the first paid draw at which $M$ distinct
endpoint pairs have been recorded. Equality of two pairs is recognized by two typed
equality comparisons; no names or multiplication are required. A union
bound over the $M$ edges gives

$$
\Pr_i(\tau>n)\le M(1-1/M)^n\longrightarrow0.
$$

Thus $\tau$ is finite almost surely, with no deterministic finite upper
bound. Since the support size is known, at $\tau$ the retained typed
graph is exactly $G_i$; every endpoint occurs because its degree is
positive. Counting its $\sum c(t,t')^2$ identifies $i$ by (UJB.7506).
This procedure has zero error on every terminating run. $\square$

### 3.4 Mathematical scope and source correspondences

**Assumptions and interpretation 3.7.** Theorem 3.3 is a source-specific
operational application of the existing group construction. The old
Theorem 1.3 separates simultaneous square/cube structure despite every
individual power graph being isomorphic; the new horizon concerns the
particular anonymous uniform order-six experiment (UJB.7501). It does
not reprove the old theorem or assert a new general graph framework.
The [native correlation-order results, Theorems 1.3 and 4.1](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATION_ORDER_ACQUISITION.md)
already distinguish bounded joint laws from optimized acquisition; their
native source family, legal Reads and cost objective are different.
Here Theorem 3.3 supplies the complete four-sample specialization,
while (UJB.7301)–(UJB.7305) keep law equivalence separate from pointwise
joint-kernel descent.

The finite graph, its two boundary maps, its retained indexed edges
and its sample index order are compatible relational encodings of
acquired data. These recover equality history as in Proposition 3.5;
they do not recover physical elapsed time, erased chronology, named
group elements, multiplication or arbitrary permissions. In particular
the single bit $\mathbf1_R$ already separates the four-sample laws, so
the full history is not asserted to be minimal for that narrower task.
Neither an optimal storage bound, a fixed-confidence optimum nor a
native action count follows from the first differing horizon.

The witnessed-relation adapter (UJB.7502) is conditional mathematical
progress. An operation-, joint-law- and resource-preserving realization
of its iid uniform sampler, same-source fork, stable typed equality,
legal permissions and retained references using the original $\alpha/\beta$
operations remains **unproved**. Encoding group elements in trees or
using the mathematical inverse $a^2t$ supplies none of those operational
bridges. The full recovery problem for the original atomic generation
model remains unresolved by this conditional application.

The counting method used inside Theorem 3.3 is classical [LS](https://arxiv.org/abs/math/0408173v2).
For the interaction formulation, Crane–Dempsey,
[Edge exchangeable models for network data, §2.3 and §4.1](https://arxiv.org/abs/1603.04571v4),
uses iid interactions modulo vertex renaming. The present specialization
has disjoint left/right types, mass $1/1944$ on each allowed ordered
pair, type-preserving renaming and retained sample indices and repeated
occurrences. Levin–Chandrasekaran,
[Limits of Weighted Graphs via Random Quotients, Proposition 2.6 and §4.1](https://arxiv.org/abs/2512.23149v3),
likewise provides the mature edge-sampling and homomorphism/injectivity
setting; no general limit or representation theorem is needed for the
finite counts above. First-occurrence naming of equality classes also
appears in Ivanov–Burnaev,
[Anonymous Walk Embeddings, §2](https://proceedings.mlr.press/v80/ivanov18a.html),
but their samples follow dependent walks, so their walk results are not
transferred to this iid edge law. These correspondences attribute the
methods, not the specific rank counts and probabilities for $S_0,S_1$;
the contribution is the stated source-specific operational application.

## 追加锚（本行以下为增补区）

## 4. Exact four-sample relation strength and the uses lost by a decision bit

### 4.1 Source contract and the complete signed law

**Definition 4.1 (the four-sample experiment).** Retain Definition 3.1
without changing its operations: one hidden $i$ is fixed, each paid draw
is iid uniform with replacement on the actual $1944$ edges of
(UJB.7502), and an explicitly supplied nondestructive same-source fork
returns the two typed handles from that draw. Stable equality is only
within type; the two charts share sample indices, and comparisons to
retained old handles remain legal. Control, permissions, initialization
and auxiliary randomness are source-blind. Old source-dependent handles
and records must come from this same experiment and their draws remain
charged. Coordinates, multiplication, an inverse operation, reset and
any additional sampler are unavailable to the observer. Proposition 3.2
supplies the mathematical correspondence with the published groups;
in particular the third $w$ coordinate remains present also for $S_1$.

Let $p_i(\pi,\sigma)=\Pr_i(H_4=(\pi,\sigma))$. Partitions here are
exact equality patterns on the same ordered set $[4]$; e.g. $12|3|4$
means precisely $a_1=a_2$, with $a_3,a_4$ distinct from that value and
each other. Write $\pi\preceq\rho$ for refinement, $|\pi|$ for the
number of blocks, and

$$
\mathcal P=\{12|34,13|24,14|23\},\qquad
\mathcal M(\pi)=\{\rho\in\mathcal P:\pi\preceq\rho\}.
$$

The scalar $H_i=\sum_{t,t'}c_i(t,t')^2$ is the four-cycle homomorphism
count from (UJB.7506), including diagonal and other noninjective maps;
it is distinct from the indexed history $H_n$.

**Theorem 4.2 (complete signed law and optimal terminal decision).** For
the actual sources of Definition 4.1, put $\Delta H=H_1-H_0=209952$.
For every pair of partitions of $[4]$,

$$
\begin{aligned}
p_1(\pi,\sigma)-p_0(\pi,\sigma)
 &=\frac{\Delta H}{1944^4}K(\pi,\sigma),\\
K(\pi,\sigma)
 &=(-1)^{|\pi|+|\sigma|}
 \bigl(|\mathcal M(\pi)|\,|\mathcal M(\sigma)|
       -|\mathcal M(\pi)\cap\mathcal M(\sigma)|\bigr).
\end{aligned}
\tag{UJB.7601}
$$

Thus $K=0$ if either partition has a block of size at least three.
With $\operatorname{TV}(p_0,p_1)=\frac12\sum_{\pi,\sigma}|p_1-p_0|$,

$$
\operatorname{TV}(p_0,p_1)=\frac1{1417176},\qquad
\operatorname{Succ}_{1/2}^{\mathrm{opt}}
 =\frac12+\frac1{2834352}.
\tag{UJB.7602}
$$

A permitted optimal terminal rule chooses $S_1$ when
$|\pi|+|\sigma|$ is even and $S_0$ when it is odd. Every zero-difference
atom can instead be assigned either decision, or randomized.

Proof. The counting argument also applies to two finite simple typed
bipartite graphs with common positive parameters
$\ell,r,d_A,d_T$, where $M=\ell d_A=rd_T$. For prescribed equalities
$(\rho,\tau)$, let $Q(\rho,\tau)$ be the quotient graph with one vertex
per block on each side and edge $j$ between the blocks containing $j$.
Let $F_i(\rho,\tau)$ count its type-preserving homomorphisms into $G_i$.
There is exactly one such map for each ordered edge tuple satisfying
the prescribed equalities. Parallel edges collapse for this count,
since the host is simple, but the probability denominator stays $M^4$.
No automorphism division and no exclusion of unused cross-edges occur.

By (UJB.7505), a connected tree with $u$ left and $v$ right vertices
has $M d_T^{u-1}d_A^{v-1}$ homomorphisms. Products give the forest
counts. A simple bipartite graph with at most four edges and no isolated
vertices is a forest unless it is exactly a four-cycle. Here that
cycle occurs exactly when $\rho,\tau$ are distinct members of
$\mathcal P$: both sides have two blocks of size two, and the distinct
matchings make all four endpoint pairs different. There are six ordered
cases. Therefore $F_1-F_0=\Delta H$ on these six cases and is zero
elsewhere. This uses the common degrees, not graph isomorphism.

Let $N_i(\pi,\sigma)=M^4p_i(\pi,\sigma)$. Each prescribed equality
count is the sum of $N_i$ over its coarsenings. Finite partition-lattice
inversion gives the full exact law, as well as its signed difference:

$$
\begin{aligned}
N_i(\pi,\sigma)
 &=\sum_{\rho\succeq\pi,\ \tau\succeq\sigma}
   \mu(\pi,\rho)\mu(\sigma,\tau)F_i(\rho,\tau),\\
N_1(\pi,\sigma)-N_0(\pi,\sigma)
 &=\Delta H
   \sum_{\substack{\rho\in\mathcal M(\pi),\,
                    \tau\in\mathcal M(\sigma)\\\rho\ne\tau}}
       \mu(\pi,\rho)\mu(\sigma,\tau).
\end{aligned}
\tag{UJB.7603}
$$

Here $\mu$ is the inverse of the refinement incidence matrix. On an
interval from $\pi$ to a matching $\rho$, each pair is either already
a block or is obtained by merging two singletons. The interval is a
product of two-element chains, whose inverse coefficients are $-1$
for a merge and $1$ for no merge. Consequently
$\mu(\pi,\rho)=(-1)^{|\pi|-2}$. All surviving summands in the second
line have the same sign. Their number is the number of ordered distinct
compatible matchings, exactly the parenthesis in (UJB.7601). A block
of size at least three has no compatible matching. This proves every
signed atom, without an enumeration of the $225$ pairs.

For a fixed matching $\rho$, its refinements are itself, its two
one-pair splittings, and the discrete partition. Their coefficients
are $1,-1,-1,1$, with absolute sum $4$. Since the contributions to each
$K$ have a common sign, absolute values introduce no cancellations:

$$
\sum_{\pi,\sigma}|K(\pi,\sigma)|=6\cdot4\cdot4=96,
\qquad \sum_{\pi,\sigma}K(\pi,\sigma)=6(1-1-1+1)^2=0.
\tag{UJB.7604}
$$

For an explicit compact description, the partition types with nonempty
$\mathcal M$ are the discrete partition $D$, six one-pair partitions
$E$, and three matchings $P$. Each $E$ has one matching completion,
with two $E$ per matching. The cells $DD$, $DE/ED$, $DP/PD$ contribute
respectively $6,-2,2$, with multiplicities $1,12,6$. Cells $EE$, $EP/PE$
and $PP$ with different completions contribute $1,-1,1$, with
multiplicities $24,24,6$. All other cells are zero. Equivalently the
coefficients $(-2,-1,0,1,2,6)$ have multiplicities
$(12,24,152,30,6,1)$.

Thus generally $\operatorname{TV}=48|\Delta H|/M^4$. In the actual
sources, (UJB.7506) gives

$$
H_0=17496\cdot2^2+2187\cdot8^2=209952,\qquad
H_1=6561\cdot8^2=419904,
$$

and hence $48\cdot209952/1944^4=1/1417176$. For any randomized terminal
decision with probability $d(h)$ of choosing $S_1$ at atom $h$, its
equal-prior success is

$$
\frac12\sum_h\bigl[p_0(h)(1-d(h))+p_1(h)d(h)\bigr]
 =\frac12+\frac12\sum_h(p_1(h)-p_0(h))d(h).
$$

It is maximized by $d=1$ on positive differences and $d=0$ on negative
ones. The sum of positive differences is TV, proving (UJB.7602).
Since $\Delta H>0$, (UJB.7601) identifies exactly those strict signs
by the parity of the occupied endpoint counts. Stable typed equality
computes these counts legally. This establishes terminal performance,
not a one-bit bound on storage during acquisition.

The prescribed rectangle $R$ of Theorem 3.3 has gap
$\Delta H/M^4=\operatorname{TV}/48$. Each of the six exact strict-cycle
atoms has the same gap, so their disjoint union has gap
$\operatorname{TV}/8$. They retain the earlier separation, but neither
is the complete optimal event. The pair of occupancies and its parity
retain the full TV for this equal-prior task. $\square$

### 4.2 Strict actual atoms and later source decisions

**Proposition 4.3 (every optimal binary decision discards later uses).**
For the actual four-sample laws define the exact atoms

$$
C=(12|34,13|24),\qquad
U=(1|2|3|4,12|34),\qquad
V=(12|3|4,13|24).
$$

Writing $L(h)=p_1(h)/p_0(h)$ on these positive atoms, their counts and
likelihood ratios are

| Atom $h$ | $N_0(h)/M$ | $N_1(h)/M$ | $L(h)$ |
| --- | ---: | ---: | ---: |
| $C$ | $74$ | $182$ | $91/37$ |
| $U$ | $89916$ | $90132$ | $7511/7493$ |
| $V$ | $1200$ | $1092$ | $91/100$ |

Any binary summary that retains the equal-prior optimal binary testing
value merges $C$ and $U$, after labeling its two outputs by their optimal
decisions. It cannot retain the optimal value for prior
$\Pr(i=1)=1/3$. Applied separately to two four-sample blocks, its two
retained bits also fail to retain the equal-prior optimum of the two
full block records. Both failures hold for every assignment on ties.

Proof. Let $I_i=N_i(C)$. Reusing (UJB.7507), or excluding equal left
vertices and equal right vertices from the four-cycle homomorphisms,
gives

$$
I_i=H_i-\ell d_A^2-rd_T^2+M=H_i-66096.
\tag{UJB.7605}
$$

The subtraction removes $\ell d_A^2$ maps with coincident left vertices
and $rd_T^2$ with coincident right vertices; their intersection has
$M$ maps and is restored once. Thus $(I_0,I_1)=(143856,353808)$.

For $V$, choose the repeated left vertex, then its ordered two distinct
right neighbors, and then one further left neighbor at each right
endpoint, excluding the middle vertex. This gives
$\ell d_A(d_A-1)(d_T-1)^2$ assignments. The only remaining forbidden
equality identifies those two outer left vertices. The resulting exact
four-cycle assignments are counted by $I_i$. Therefore

$$
N_i(V)=72\cdot27\cdot26\cdot7^2-I_i.
\tag{UJB.7606}
$$

For $U$, fix ordered distinct right endpoints $t,t'$ with codegree
$c=c_i(t,t')$. Each right endpoint must choose two ordered distinct
left neighbors. Before cross-exclusions there are $56^2$ choices.
Each of the four cross equalities has $c\cdot7^2$ assignments. The
only compatible intersections are the two bijections identifying both
left pairs, each with $c(c-1)$ assignments; three cross equalities
would violate a within-pair inequality. Inclusion-exclusion therefore
gives $56^2-196c+2c(c-1)$ assignments. Moreover

$$
\sum_{t\ne t'}c_i(t,t')=M(d_A-1),\qquad
\sum_{t\ne t'}c_i(t,t')(c_i(t,t')-1)=I_i.
$$

The first identity chooses a left vertex and two distinct neighbors;
the second counts the strict cycles. Consequently

$$
N_i(U)=243\cdot242\cdot56^2-196M\cdot26+2I_i.
\tag{UJB.7607}
$$

Dividing (UJB.7605)–(UJB.7607) by $M=1944$ proves the table. All three
atoms have positive mass under both sources. In particular $C,U$ have
strictly positive signed differences and $V$ has a strictly negative
one. The pointwise optimization in Theorem 4.2 forces the decisions
$1,1,0$ at these atoms, respectively. More generally a two-output
summary followed by an optimal decoder must send all strict positive
atoms to the output decoded as $1$ and all strict negative atoms to
the other output: mixing strict signs would strictly decrease success.
This also forces deterministic outputs there for a randomized summary.
Hence $C$ and $U$ occupy the same summary fiber irrespective of ties.

For prior $q=\Pr(i=1)$ and zero-one loss, the optimal decision chooses
$1$ precisely when $q p_1(h)>(1-q)p_0(h)$. At $q=1/3$ this is $L>2$.
Now $91/37>2$ while $7511/7493<2$. The strict decisions at $C,U$ are
opposite, so any common decision on their summary fiber incurs strictly
larger Bayes risk. Even with prior $1/2$, their posteriors
$91/128$ and $7511/15004$ differ, although their optimal actions agree.

For two consecutive blocks of four paid draws, Proposition 3.6 gives
conditional independence under the same fixed $i$. Retain only the two
full internal partition records for the moment. Their law is
$p_i\otimes p_i$, so the joint likelihood ratios multiply:

$$
L(C)L(V)=\frac{8281}{3700}>1,\qquad
L(U)L(V)=\frac{683501}{749300}<1.
\tag{UJB.7608}
$$

Both block records have the same retained decision bits $(1,0)$, but
the equal-prior optimal decisions are opposite and strict. Each record
has positive probability under both sources. The compressed fiber thus
mixes strictly positive and strictly negative product-law differences,
strictly decreasing TV and increasing optimal error. Extra permitted
cross-block comparisons can only improve the full eight-sample
experiment; no value for its optimum is asserted here. $\square$

### 4.3 Old handles, next-read prediction and kernel descent

**Proposition 4.4 (a legal next-read use lost under either tie choice).**
Let $Z=(1234,1234)$, the all-same-edge atom. Retain the four old paired
handles and buy a fifth draw from the same source. Let $J$ report whether
its paired handle equals any of the old paired handles, using the two
within-type comparisons at the same old index. Then, for each $i$,

$$
\Pr_i(J=1\mid Z)=\frac1M,\qquad
\Pr_i(J=1\mid h)=\frac4M\quad(h=C,U,V).
\tag{UJB.7609}
$$

No equal-prior-optimal binary summary alone preserves these conditional
prediction probabilities. In particular neither historical equality
sufficiency nor optimal terminal testing implies pointwise descent of
the actual next-state kernel.

Proof. For a concrete retained edge history $e=(e_1,\ldots,e_4)$ let
$m(e)$ be the number of distinct edge pairs in that list. The event
$J=1$ is the disjoint union of those $m(e)$ edge outcomes. The next
edge is independent and uniform on the same support, so its conditional
probability given this actual history is exactly $m(e)/M$. This count
is determined by the intersection of the two equality partitions.
It equals one on $Z$ and four on each of $C,U,V$, proving (UJB.7609)
both pointwise for this readout and after conditioning on the observed
atom. These atoms have positive probability; $p_i(Z)=M/M^4=M^{-3}$.

The atom $Z$ is an equal-prior tie. Every optimal binary summary sends
$C,U$ to one bit and $V$ to the other by Proposition 4.3. Whichever
bit receives $Z$, it therefore merges a history with repeat probability
$1/M$ with one having probability $4/M$. A randomized assignment of
$Z$ has at least one output of positive probability and has the same
obstruction there. If old handles are separately retained to execute
$J$, those handles belong to the full continuation state and cannot be
counted as part of a state consisting only of the decision bit.

For clarity, an averaged conditional history law always exists here.
For a general $n$-sample exact record $h$ let $N_i(h)$ count compatible
ordered edge tuples. For an $(n+1)$-sample record $h'$ restricting to
$h$, uniform sampling gives, when $N_i(h)>0$,

$$
Q_i(h,h')=\Pr_i(H_{n+1}=h'\mid H_n=h)
 =\frac{N_i(h')}{M N_i(h)}.
\tag{UJB.7610}
$$

For public prior $q=\Pr(i=1)$ the corresponding mixture kernel is

$$
Q_q(h,h')=
\frac{(1-q)N_0(h')+qN_1(h')}
 {M\bigl((1-q)N_0(h)+qN_1(h)\bigr)}
\tag{UJB.7611}
$$

on positive conditioning events. These formulas average over compatible
actual histories, and in the second case over the posterior source.
They do not assert that each concrete history inducing $h$ has that
same next-state row. Proposition 3.5 already gives two positive-mass
actual histories in $G_0$ with the same $H_2$, but respective next-read
probabilities $1/M$ and $0$ for $a_3=a_1,t_3=t_2$. That is a pointwise
failure of descent even for the full equality record. It coexists with
(UJB.7610), and with the particular readout $J$ whose probability does
depend only on its full equality record. Any further state quotient
must preserve the relevant legal actions, available references, joint
response laws and updates on its fibers, as required in §1. $\square$

**Interpretation 4.5 (reused principles and the remaining bridge).**
The homomorphism/injective-count distinction and finite inversion in
Theorem 4.2 use the mature methods of Lovász–Szegedy,
[§§2.1, 2.4](https://arxiv.org/abs/math/0408173v2), and
Levin–Chandrasekaran,
[Proposition 2.6 and §4.1](https://arxiv.org/html/2512.23149v3).
The latter's iid edge-sampling construction is used only with the
explicit typed, index-preserving adapter of §3; its general limit
results are not premises of these finite computations. Exact equality
patterns require distinct block vertices within each type, not induced
nonedges. The signed-law calculation and C/U/V counts are consequences
for the actual published pair, rather than a new general sampling
framework or a novelty claim for inversion or likelihood testing.

The distinction between an action optimal for one decision problem and
statistical sufficiency is classical; see Blackwell,
[Equivalent Comparisons of Experiments](https://doi.org/10.1214/aoms/1177729032).
On a common positive support, constancy of $L$ on a deterministic
summary fiber makes the conditional distribution on that fiber the
same for both sources: dividing $p_1(h)=L p_0(h)$ by the two fiber
masses proves it. Conversely a common conditional distribution forces
that ratio to be constant. The likelihood ratio consequently preserves
all source posteriors and source decision uses there, including product
likelihoods for conditionally independent blocks. It need not preserve
old handles or response laws for a different continuation task.

The existing repository declarations
[`total_variation_channel_eq_iff_no_sign_mixing`](../../../D5/S3/TotalVariation/Equality/DataProcessingEquality.lean),
[`bayesRisk_le_of_blackwellDominates`](../../../D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk.lean),
and [`causal_state_factorization`](../../../D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization.lean)
state the corresponding channel-sign criterion, decision-risk
monotonicity and unequal-future-law obstruction under their explicit
finite-kernel, Markov-kernel or factorization hypotheses. The finite
experiment and positive-mass atoms above supply the concrete sign and
fiber obstructions; the general declarations alone do not supply the
source-specific counts (UJB.7605)–(UJB.7608).

The witnessed relation still has the explicit map
$O_6(S_i)\xrightarrow{(x^2,x^3)}A\times T$ of Proposition 3.2, with
unit witness multiplicity on each actual edge. The two endpoint charts,
the paired history and its sample-index order encode different
relations of the acquired data; parity preserves just the stated
terminal testing value. A joint-law-, permission- and cost-preserving
implementation of the supplied uniform sampler, same-source fork,
stable equality and retained-handle contract using the original native
$\alpha/\beta$ preparation and acquisition operations remains unproved.
The conditional four-sample result therefore leaves that bridge and
the broader recursive recovery of space, time, boundary and memory
unresolved.

## 追加锚（本行以下为增补区）

## 5. Conditional observation of a legally prepared native comb

### 5.1 Actual sources, shared labels and the observer boundary

**Definition 5.1 (finite preparation and public promise).** Fix public
$N\ge4$ and put $k=15N$. Use the actual $S_i,A,T,E_i$ of Proposition
3.2, with $|A|=72$, $|T|=243$ and $M=1944$, retaining $W=\mathbb F_3^3$
also for $i=1$. Conditional on one fixed hidden $i$, an external
preparer draws $N$ independent uniform elements $x_j\in O_6(S_i)$.
Their paired endpoints $(a_j,t_j)=(x_j^2,x_j^3)$ are exactly independent
uniform edges of $E_i$, by (UJB.7502), with no witness multiplicity.
Independently of these draws and of $i$, choose uniform full injections

$$
\lambda:A\hookrightarrow\{0,1\}^7,\qquad
\varrho:T\hookrightarrow\{0,1\}^8,
\tag{UJB.7701}
$$

independently of one another. Each map is sampled once on its entire
domain and shared across all $N$ samples, all bits and all later Reads.
Concatenate the fields in sample order:

$$
z_{15(j-1)+h}=\lambda(a_j)_h\ (1\le h\le7),\qquad
z_{15(j-1)+7+h}=\varrho(t_j)_h\ (1\le h\le8).
\tag{UJB.7702}
$$

Use [IV37.1](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_IV.md#37-the-exact-native-alphabeta-connection)'s
ordered gadgets

$$
C=\langle\beta,\alpha\rangle,\quad
D_0=\langle\beta,C\rangle,\quad D_1=\langle C,\beta\rangle,\quad
M_* =\langle\langle C,\alpha\rangle,\alpha\rangle.
$$

Define $F_{k+1}(z)=M_*$ and
$F_b(z)=\langle D_{z_b},F_{b+1}(z)\rangle$ for $1\le b\le k$.
The public promised family and the two laws are

$$
\mathcal C_N=\{F_1(z):z\in\{0,1\}^{15N}\},\qquad
\mu_i^N=\mathcal L(F_1(z)\mid i).
\tag{UJB.7703}
$$

The promise is all assignments, not just the support of either law.
An assignment outside those supports still denotes the same kind of
legal native endpoint. It need not encode any group edge sequence.

**Assumption 5.2 (stationary, source-blind handoff).** The preparer starts
from AA17.1's known allocated $\alpha$ and uses only the guarded local
events $P_p:\alpha\mapsto\beta$ and
$S_p:\beta\mapsto\langle\beta,\alpha\rangle$ to reach $F_1(z)$.
It then supplies one stationary endpoint to a distinct observer. The
observer's only source-dependent port is the original-root Read on an
arbitrary finite word in $\{L,R\}^*$, including the empty word. The
four replies are $\alpha,\beta,\mathsf b,\bot$ (branch and absent);
every strict extension of a logical leaf returns $\bot$. These are
exactly the conventions of
[`ActualTreeReadoutAcquisition.readout`](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean),
with $L=\mathsf{false}$, $R=\mathsf{true}$, $\alpha=\mathtt{of\ true}$
and $\beta=\mathtt{of\ false}$.

The observer receives public $N$, the promise and the two law
descriptions, but no $i$, sampled element, named endpoint, injection,
preparation word, old source-dependent record, preparation cursor,
allocation identity or hidden reference. There is no fork, copy,
rerooting, reset, new draw or observer source edit. Availability,
permissions, timing and refusal information carry no additional source
dependence. A Read supplies its declared reply only. Logical Reads do
not expose the extra unary material marker used to realize $\beta$ in
AA17.3's material view.

A common controller is installed from public data only, or selected
from a common source-independent distribution. Let $H$ include all
hidden source and preparation variables, and let $J$ denote that
installed controller before private randomization. A supplied seed
$U$ has a common probability law and is independent of the **joint**
pair $(H,J)$; $J$ is independent of $H$. Thus, for either source,

$$
\mathcal L_i(H,J,U)=\mathcal L_i(H)\otimes\nu_J\otimes\nu_U.
\tag{UJB.7704}
$$

Marginal independence from $i$ alone would not suffice. All query,
stop, update, output and retained-state maps, including randomized
installation and any reported control data, are measurable. Words and
replies carry their discrete sigma algebras; other state and output
spaces carry their declared sigma algebras. Each local transition
completes in finite time. Bounded stopping means at most the stated
number of Read invocations on every attained run. Constant, repeated,
absent and off-path invocations all count. The complete transcript
includes the ordered operands and replies, stopping/truncation flag,
output and any retained state or next operand produced from them.
No independent observation of preparation or local physical timing is
silently included in this transcript.

This is a conditional access and preparation contract. The distributions
in Definition 5.1 are external inputs to the preparer, not randomness
generated by $P/S$. Attaching a distinct observer with public-only
initial state does not assert a LAB erasure or reset operation.

### 5.2 Legal preparation, every address and the full-domain inverse

**Proposition 5.3 (source, operation and resource correspondence).** Every
member of $\mathcal C_N$ is legally reachable, with exact generation
grade $5k+4=75N+4$. Every finite original-root Read is either a fixed
reply or a function of one designated bit. Exactly $k=15N$ Reads suffice
to invert the encoding on the entire promised family and hence recover
the current ordered term, AA17.3's oriented material support and
terminal boundary, and AA17.2's labelled generation causal order.
Sufficient total and maximum literal operand lengths are respectively
$k(k+3)/2$ and $k+1$. These are invocation and operand statements,
with all other resources kept separate.

Proof. For $b=1,\ldots,k$, at $r=R^{b-1}$ perform
$P_r,S_r,S_{rL}$. The current continuation is $\alpha$, and these
events produce $\langle C,\alpha\rangle$ there. At $r=R^k$, perform
$P_r,S_r,S_{rL},S_{rLL}$ to produce the four-leaf $M_*$. Every
promotion sees $\alpha$ and every split sees $\beta$. This is IV37.1's
fixed $3k+4$-event preparation. Each still inactive slot is $C$ at
$q_b=R^{b-1}L$. For bit zero perform
$P_{q_bR},S_{q_bR}$, obtaining $D_0$; for bit one perform
$S_{q_bL},P_{q_bR}$, obtaining $D_1$. All guards hold. Slots are
disjoint, so insertion in any order is legal. Full insertion costs
exactly $2k$ events, giving $5k+4$ altogether: $45N+4$ fixed
preparation events and $30N$ insertion events.

Each $D_e$ has one $\alpha$ and two $\beta$ leaves; $M_*$ has three
$\alpha$ and one $\beta$. Thus the final leaf counts are
$(n_\alpha,n_\beta)=(k+3,2k+1)$. In any successful LAB history from
$\alpha$, if $p,s$ are the promotion and split counts, then
$n_\beta=p$ and $n_\alpha=1-p+s$. Consequently every history to this
endpoint has $p=2k+1$, $s=3k+3$ and grade $p+s=5k+4$; the grade is
not an artifact of the chosen insertion order.

For a suffix $u$ at a slot, the complete local reply table is

$$
\begin{array}{c|ccccccc}
u&\varepsilon&L&R&LL&LR&RL&RR\\\hline
\operatorname{Read}_{D_0}(u)&\mathsf b&\beta&\mathsf b&\bot&\bot&\beta&\alpha\\
\operatorname{Read}_{D_1}(u)&\mathsf b&\mathsf b&\beta&\beta&\alpha&\bot&\bot
\end{array}
\tag{UJB.7705}
$$

All suffixes of length at least three are absent for both bits. Every
finite root word is uniquely in one of the following classes: a spine
word $R^j$ with $0\le j<k$ (reply $\mathsf b$); a word $q_bu$ for
one $1\le b\le k$ (table (UJB.7705)); or a word $R^ku$ (the fixed
reply $\operatorname{Read}_{M_*}(u)$). This follows by locating the
first $L$ before the first $k$ right steps, if any; words ending before
that first $L$ are spine words, and all remaining words enter $M_*$.
The classes exhaust even excessively long, nested and absent operands.
In particular no Read traverses two slots or discloses two bits.

The decoder queries, for every $b=1,\ldots,k$,

$$
w_b=q_bL=R^{b-1}LL.
\tag{UJB.7706}
$$

Its reply is $\beta$ for $z_b=0$ and $\mathsf b$ for $z_b=1$.
This is the **local $L$** reply in (UJB.7705); local $LL$ would instead
be the different root operand $R^{b-1}LLL$. Thus the $k$ replies
recover $z$ without any support test, completing the inverse on all
$2^k$ promised assignments. Rebuilding $F_1(z)$ then answers every
future Read of this endpoint without further source access.

To specify the recovered views, recursively realize $\alpha$ as a
terminal, $\beta$ as a unary vertex with a terminal left child, and a
logical branch as a binary vertex with its ordered realized children.
Its finite support and maximal-address boundary are AA17.3's $S_0,B_0$.
The converse arity parser, or prefix closure of the boundary, recovers
the same term. Its split events are exactly its logical branch
addresses; promotions are exactly the non-$\alpha$ positions born
$\alpha$ (root or right child). Add the local $P_p\prec S_p$ and
parent-creating-split precedence edges of AA17.2 and take their
transitive closure. These operations compute the labelled causal
order from the decoded term. Conversely its split/promote labels
reconstruct the same branches and leaf labels by AA17.2. No source
identity or chosen serial extension is required for these inverses.

The literal $w_b$ has length $b+1$, so
$\sum_{b=1}^k|w_b|=k(k+3)/2$ and $\max_b|w_b|=k+1$.
The $k$ decoded bits are a sufficient payload; operands, counters,
output representations and scratch are additional. Computation,
navigation, memory, sampling, map selection, preparation event operands
and source-blind installation/handoff have not been charged to the Read
count or bounded by these formulas. In particular the distinct-address
functional `ActualTreeReadoutAcquisition.paid` is a different tariff;
here every invocation counts, as in NCO1.1. $\square$

### 5.3 Complete equality through seven adaptive Reads

**Theorem 5.4 (first native observation horizon).** Under Definitions
5.1 and Assumption 5.2, for every $N\ge4$ and every common measurable
adaptive observer using at most seven original-root Read invocations,
the complete transcript laws under $\mu_0^N,\mu_1^N$ are equal.
This includes arbitrary finite operands, repeats, constant/absent
answers, partial fields, retained state and bounded stopping. At eight
invocations a fixed event has the strictly positive gap (UJB.7710)
below. Thus eight is the first possible invocation budget for a law
difference in this conditional experiment.

Proof. First fix any tuple of at most seven words, without imposing a
length bound or requiring the words to differ. By (UJB.7705) and its
exhaustive root classification, each nonconstant answer uses one bit
of one field in (UJB.7702). Let $I_A,I_T\subseteq[N]$ be the sample
positions whose respective left and right fields are touched. Then

$$
|I_A|+|I_T|\le7,\qquad r:=|I_A\cap I_T|\le3.
\tag{UJB.7707}
$$

Several bits of a field, or repeated queries for a bit, add no new
field to these sets. For the $r$ doubly touched samples, Theorem 3.3
gives equality of the complete typed equality-partition law: its
prescribed-equality quotients have at most three edges, hence after
parallel-edge collapse are forests, with counts (UJB.7505). Finite
inclusion-exclusion gives exact partitions as well as required
equalities. Its hypotheses hold here because these samples are iid
uniform actual edges of the same simple biregular $G_i$.

Every other touched field comes from a different edge sample, with
only one endpoint selected. By biregularity its endpoint is uniform on
its own type, independently of the doubly touched core and of all
other such one-sided samples. Given any concrete selected values so
far, a new left endpoint equals each existing left equality block
with probability $1/72$ and forms a new block with probability
$(72-s)/72$ if there are $s$ existing blocks. For a right endpoint the
corresponding probabilities are $1/243$ and $(243-s)/243$. These
probabilities depend only on the partitions, even when the core's
conditional named-vertex distribution is not uniform. Adjoining these
fields one by one proves equality of the entire selected typed
partition law under the two sources.

Conditional on any such partitions with $s_A,s_T$ distinct selected
vertices, the complete codewords assigned to their ordered blocks
are independent uniform ordered injections into alphabets of sizes
$128,256$. Explicitly, any proposed word assignment has probability

$$
\frac{\mathbf1\{\text{exactly the prescribed within-type equalities}\}}
 {(128)_{s_A}(256)_{s_T}},
\qquad (K)_s=K(K-1)\cdots(K-s+1).
\tag{UJB.7708}
$$

Indeed each restriction of a uniform full injection has the same
number of full extensions. The maps are independent of the actual
endpoints and of one another. Hence the law in (UJB.7708) depends on
the equality record only. Combining the two common laws proves
equality even of all selected **complete** codewords, so also of the
particular bit projections and deterministic native replies. Hidden
labels are shared throughout this argument; no unobserved label or
endpoint is redrawn in response to a query.

For adaptive control fix $J=j,U=u$. These determine one common
deterministic program. For any control-consistent stopped or truncated
path $h=((w_1,y_1),\ldots,(w_m,y_m))$, $m\le7$, its source event is
exactly $\bigcap_{a=1}^m\{t:\operatorname{Read}_t(w_a)=y_a\}$.
On this path the operands are fixed, so its probability agrees by
the preceding argument; inconsistent paths have probability zero
under both laws. There are at most four children per Read and depth
at most seven, hence finitely many paths for this fixed program,
despite the countably infinite operand vocabulary. Stop/output,
next-operand and retained-state values are common functions of the
path, including the zero-Read case. They therefore have equal joint
laws. This is the fixed-source cylinder argument of
[NCO4.1](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATION_ORDER_ACQUISITION.md#4-bounded-experiments-stopping-and-fixed-family-saturation),
applied to the present all-word equality rather than its different
future-read task. Finally (UJB.7704) permits integration over $(j,u)$
against the same product law; measurability of all the stated maps
ensures these are measurable transcript pushforwards. It is not
necessary to assume that adaptive operands are unconditionally
independent of the source. The eight-Read event below proves the
remaining assertion. $\square$

### 5.4 The actual all-zero event and the fixed-source certainty boundary

**Proposition 5.5 (eight-Read gap, decoding and overlap).** For
$j=1,2,3,4$ Read (UJB.7706) at slot indices

$$
b_{A,j}=15(j-1)+1,\qquad b_{T,j}=15(j-1)+8.
\tag{UJB.7709}
$$

Let $E$ be the event that all eight replies are $\beta$, equivalently
that the first bits of the first four left fields and the first four
right fields are all zero. Then

$$
\Pr_1(E)-\Pr_0(E)=\frac{56}{158731093125}>0.
\tag{UJB.7710}
$$

Choosing source $1$ on $E$ and source $0$ otherwise has equal-prior
success $1/2+28/158731093125$. This is an attained value, without an
optimality claim. For every fixed $N$, even complete decoding of the
endpoint leaves equal-prior Bayes error at least
$\tfrac12\,1944^{1-N}>0$.

Proof. A uniform injection into $K$ binary words of a fixed length
assigns distinct words to $s$ distinct selected vertices. Exactly
$K/2$ words have first bit zero, so the probability that those $s$
labels all have first bit zero is $f_K(s)=(K/2)_s/(K)_s$. Conditional
on $H_4=(\pi,\sigma)$, the event probability is consequently
$f_{128}(|\pi|)f_{256}(|\sigma|)$, using independence of the two full
injections. Apply Theorem 4.2's complete signed law, not just a
selected equality event. Its only prescribed-equality discrepancies
are the six ordered distinct pairs of matchings. For each matching its
refinements consist of itself, two one-pair splittings and the discrete
partition, with inversion weights $1,-1,-1,1$. Thus its weighted
contribution is

$$
\begin{aligned}
g(K)&=f_K(2)-2f_K(3)+f_K(4)
     =\frac{((K/2)_2)^2}{(K)_4},\\
g(128)&=\frac{1008}{15875},\qquad
g(256)=\frac{4064}{64515}.
\end{aligned}
\tag{UJB.7711}
$$

For the identity, write $a=K/2$ and put the three terms over $(K)_4$;
after factoring $(a)_2$, the remaining factor is
$(K-2)(K-3)-2(a-2)(K-3)+(a-2)(a-3)=a(a-1)$.
Using the actual $H_1-H_0=209952$ from (UJB.7506), the gap is exactly

$$
\frac{6\cdot209952}{1944^4}\,
\frac{1008}{15875}\,\frac{4064}{64515}
=\frac{56}{158731093125}.
\tag{UJB.7712}
$$

This sign corresponds to zeros because the actual operand is $q_bL$:
$D_0$ returns $\beta$ there. A test of local $LL$ has a different
reply table and is not the event in (UJB.7709). The eight operand
lengths in sample order are $2,9,17,24,32,39,47,54$, with sum $224$
and maximum $54$. These are sufficient literal lengths in addition
to the eight invocation charges.

For overlap, let all $N$ actual edge draws equal one edge. This has
probability $M^{1-N}$ under either source. Its two codewords are an
independent uniform pair $(u,v)\in\{0,1\}^7\times\{0,1\}^8$.
Moreover the converse holds: if all left fields agree and all right
fields agree, injectivity forces all paired edges to be that same
edge. Thus, for each fixed $(u,v)$, the endpoint whose $N$ fields all
equal $(u,v)$ has exact mass

$$
\mu_i^N(\{t(u,v)\})=\frac{1944^{1-N}}{128\cdot256},
\qquad i=0,1.
\tag{UJB.7713}
$$

Summing these distinct endpoints gives a common full-tree sublaw of
mass $1944^{1-N}$. On this sublaw a common decision has the same
distribution for both sources, even with arbitrary independent coins
and the entire decoded tree. It makes equal-prior error at least half
that mass. More generally, prior masses $p_0,p_1>0$ give error at
least $\min(p_0,p_1)1944^{1-N}$. Every transcript is a channel from
this fixed tree and the source-independent installation and seed, so
further Reads or source-free processing cannot remove this common
sublaw. There is no finite zero-error source identification at fixed
$N$, even after the full inverse of Proposition 5.3. $\square$

**Proposition 5.6 (what the inverse preserves and what it cannot recover).**
On the two law supports, the decoded fields recover the complete
indexed typed equality record $H_N$ and its pairing. On all of
$\mathcal C_N$ they recover the ordered term and the AA17 views of
Proposition 5.3, but neither arbitrary serial generation history nor
fresh edge samples follow from that inverse. A full serial word is
recoverable under the additional public recipe consisting of the
fixed preparation in Proposition 5.3 followed by complete slot
insertions in increasing $b$, with the displayed two-event word for
each bit.

Proof. On the supports, injectivity makes equality of complete fields
equivalent to equality of the corresponding actual endpoints, and
their public positions retain the common sample index. For an
unsupported assignment the same field partitions still exist, but a
named group realization is not implied. The inverse does not disclose
unused map values, named group elements, their multiplication or $i$.
With the additional public recipe, the decoded $z$ specifies every
promotion/split and every literal event address in that recipe, so
reconstructs that exact word. Without it, perform two disjoint slot
insertions in opposite orders after the same fixed preparation and
complete all other insertions identically. Both executions are legal,
have the same endpoint, views and grade, but have different serial
words. This is the AA17.2 distinction between a labelled causal order
and a chosen linear extension, not a failure of the current-term
inverse. Finally every further Read is deterministic on the same
prepared endpoint. Repeating a Read repeats its reply; reading another
slot exposes another part of the same finite preparation. Neither
operation supplies a fresh independent draw. $\square$

**Scope 5.7 (suppliers and remaining conditions).** This is a
`repo-derived` source-specific application: Proposition 3.2 and
Theorems 3.3/4.2 supply the actual group/edge adapter and signed sample
law; IV37.1 supplies the legal bit-slot construction; AA17.1–17.3
supply guards and the syntax/material/boundary/causal-order inverses;
NCO2.3 and NCO4.1 supply the all-word locality and fixed-source
adaptive-cylinder methods in their own domains. The graph
homomorphism/inversion method is classical, as cited in §§3–4
([Lovász–Szegedy, §§2.1, 2.4](https://arxiv.org/abs/math/0408173v2));
the random-function interaction framework is also prior
([Maurer, Random Systems](https://crypto.ethz.ch/publications/Maurer02.html)).
The additional content is their explicit actual-source/native-operand
correspondence, the partial-field argument with shared full injections,
and this exact seven/eight-invocation result. It asserts no new general
graph, coding or adaptive-interaction theorem, and no broader literature
originality claim. The proofs here are ordinary mathematics, not Lean
verification.

The distinction between globally shared injections and freshly sampled
labels is essential: independent injections redrawn for every sample
would make all $N$ codeword pairs iid uniform under both sources,
erasing even the full-tree difference. Observer blindness is also
essential: a preparer retaining $z$ can compute $E$ before any observer
Read. These are different contracts from Assumption 5.2. Full uniform
injections are a sufficient specification, not a proved weakest one.

This finite preparation realizes a stationary native observation law
under added access assumptions. It supplies no autonomous native
sampler for the hidden group law or injections, no native isolation or
handoff service, and no changing-source joint kernel or ongoing
same-source fork/sample mechanism. The costs of those mechanisms,
installation, computation, navigation and all memory beyond the
sufficient payload remain separate. No minimum-memory bound or
optimum eight-Read accuracy follows here. The general autonomous
recovery problem for space, time, boundary, memory and recursive
observation remains unresolved by this conditional result.

## 追加锚（本行以下为增补区）

## 6. The sharp eight-invocation decision boundary of the prepared source

### 6.1 The same experiment and its measurable protocol class

Retain Definition 5.1 and Assumption 5.2 in full. In particular, the
actual graph is (UJB.7502), with all three $w$ coordinates, $72$ left
vertices, $243$ right vertices and $1944$ edges. Proposition 3.2 supplies
the bijection from the actual order-six elements, Proposition 5.3 the
legal native preparation and the exhaustive original-root address
classification. The full-label experiment of §4 supplies a latent
probability calculation; its handle/equality operations are not ports
of the native observer of §5.

For clarity, the two laws average over the **single** draw of each full
injection (UJB.7701), independently across endpoint types and independently
of the iid edge samples. They do not condition on particular realized
injections. Conditional on $s$ distinct vertices of one type, their
ordered labels have probability $1/(Q)_s$ for each ordered distinct
$s$-tuple of words, with $Q=128$ or $256$, exactly as in (UJB.7708).
Equal vertices retain the same word across every sample and query.
This without-replacement law concerns images of distinct vertices;
the original edges are sampled with replacement. No history-dependent
redraw or independent-bit surrogate is used below.

Write $\omega=(J,U)$ for the independently installed controller and
supplied independent seed of (UJB.7704), on their product probability
space $(\Omega,\mathcal F,\nu)$. Its sigma algebra is arbitrary. The
initial observer state is a measurable function of public $N$, the
public promise/law descriptions and $\omega$ **only**. Every subsequent
query, stop, update, output and retained-state map is common to the two
sources, measurable on its declared carriers, and receives only these
public data, this seed and previously acquired replies. An initial
state with equal marginal laws could still contain the hidden maps or
correlated preparation data; equality of marginals is not a substitute
for this derivation and joint independence requirement.

Let $\mathcal A_8(N)$ contain all these protocols whose stopping is
pathwise bounded by eight actual original-root Read invocations.
There is no restriction on the finite operands, and repeats, constants,
absences and off-path calls remain legal and paid. Local transitions
retain Assumption 5.2's finite completion requirement; no additional
computability, address-length or memory restriction is imposed. For
$\mathcal A\in\mathcal A_8(N)$ let $\mathsf{Tr}_{\mathcal A}$ be its
complete stopped record, including operands, replies, stop/truncation
flag, output and retained state. For arbitrary measurable laws use
$\operatorname{TV}(P,Q)=\sup_E|P(E)-Q(E)|$, which is half the absolute
mass sum for finite laws. Define

$$
V_8(N)=\sup_{\mathcal A\in\mathcal A_8(N)}
 \operatorname{TV}\bigl(\mathcal L_0(\mathsf{Tr}_{\mathcal A}),
                         \mathcal L_1(\mathsf{Tr}_{\mathcal A})\bigr).
\tag{UJB.7801}
$$

The upper bound will also hold with $\omega$ itself retained in the
record. Edge sampling, full-injection selection, legal preparation and
isolated handoff remain external premises. The statement does not
supply them as new bare-LAB operations.

### 6.2 A uniform cell bound from the actual full injections

**Lemma 6.1 (sharp coefficient for every four-pair bit design).** Choose
any four distinct sample indices. For each chosen sample $j=1,\ldots,4$,
select a left coordinate $a_j\in[7]$ and a right coordinate $b_j\in[8]$.
Let $Y_{\mathbf a,\mathbf b}\in\{0,1\}^8$ list these four left bits
and four right bits, in those two blocks. Uniformly in all these
indices, coordinates and values $y$,

$$
\begin{aligned}
\Pr_1(Y_{\mathbf a,\mathbf b}=y)-\Pr_0(Y_{\mathbf a,\mathbf b}=y)
 &=c_{\mathbf a,\mathbf b}(-1)^{\sum_{j=1}^8y_j},\\
|c_{\mathbf a,\mathbf b}|&\le\Delta:=\frac{56}{158731093125}.
\end{aligned}
\tag{UJB.7802}
$$

When $a_1=\cdots=a_4$ and $b_1=\cdots=b_4$, the coefficient is
$+\Delta$; the common left and right coordinates need not be equal.

Proof. Use the partition refinement order of §4.1 and its three
perfect matchings $\mathcal P=\{12|34,13|24,14|23\}$. For one side put
$Q=2^d$ and $\chi_h(x)=(-1)^{x_h}$. Given a partition $p$ of $[4]$,
define $m_Q(\mathbf a;p)$ to be the expected product
$\prod_{j=1}^4\chi_{a_j}(X_{B_p(j)})$, where the distinct blocks of
$p$ receive uniform ordered distinct labels in $\{0,1\}^d$.
Here $B_p(j)$ denotes the block containing $j$. This is the actual
conditional injection channel, by (UJB.7708), even when the named
vertices conditional on their equality record are not uniform.

We calculate these moments with their without-replacement denominator
explicit. Write $k_p=|p|$, and for each block $B$ set
$u_B=\bigoplus_{j\in B}e_{a_j}\in\mathbb F_2^d$. For a partition
$\rho$ of the set of $p$-blocks put

$$
\mu(0,\rho)=\prod_{C\in\rho}(-1)^{|C|-1}(|C|-1)!.
$$

Distinct-label inclusion-exclusion gives

$$
m_Q(\mathbf a;p)=\frac1{(Q)_{k_p}}
 \sum_{\rho}
 \mu(0,\rho)Q^{|\rho|}
 \prod_{C\in\rho}\mathbf1\left\{\bigoplus_{B\in C}u_B=0\right\}.
\tag{UJB.7803}
$$

Indeed the indicator that $k_p$ label variables are all distinct is
the sum over $\rho$ of $\mu(0,\rho)$ times the indicator of equality
within each $C\in\rho$. The coefficient counts cyclic orderings on
each block with sign $(-1)^{|C|-1}$. On a tuple with a nontrivial
equality class, the sum is zero because the signed sum of permutations
within that class is zero; on an all-distinct tuple it is one.
After multiplying by the characters, each merged label sum is $Q$
when its total character is zero and zero otherwise. Dividing by the
number $(Q)_{k_p}$ of ordered distinct tuples proves (UJB.7803).

For $t\in\mathcal P$ define its consumed matching coefficient

$$
K_Q(\mathbf a;t)=\sum_{p\preceq t}\mu(p,t)m_Q(\mathbf a;p).
\tag{UJB.7804}
$$

If $t^-,t^+$ are its two one-pair splittings and $D=1|2|3|4$ is the
discrete partition, then §4.1's interval calculation makes this exactly
$m_Q(\mathbf a;t)-m_Q(\mathbf a;t^-)-m_Q(\mathbf a;t^+)
 +m_Q(\mathbf a;D)$.

Every proper marginal of $Y_{\mathbf a,\mathbf b}$ uses at most seven
bits, hence is common by Theorem 5.4 and (UJB.7706). Apply the finite
Boolean Fourier expansion to its signed mass function
$d(y)=\Pr_1(Y=y)-\Pr_0(Y=y)$. A character supported on a proper subset
has zero coefficient because the corresponding marginal difference
is zero. Only the full character survives, so

$$
d(y)=c_{\mathbf a,\mathbf b}(-1)^{\sum y_j},\qquad
c_{\mathbf a,\mathbf b}
 =\frac1{256}\left(\mathbb E_1\prod_{j=1}^8(-1)^{Y_j}
                  -\mathbb E_0\prod_{j=1}^8(-1)^{Y_j}\right).
\tag{UJB.7805}
$$

This expands a real function on the finite cube; it does not assume
independent or uniformly distributed observed bits.

Set $h=(H_1-H_0)/1944^4=1/68024448$. Theorem 4.2, specifically
(UJB.7603), supplies the entire signed exact partition law. Its only
prescribed-equality differences are the six **ordered** pairs of
distinct perfect matchings, each of size $h$. Averaging the independent
left/right injection characters against that law and interchanging
finite sums yields

$$
\begin{aligned}
c_{\mathbf a,\mathbf b}
 &=\frac1{256}\sum_{p,q}
       (p_1(p,q)-p_0(p,q))m_{128}(\mathbf a;p)m_{256}(\mathbf b;q)\\
 &=\frac h{256}
   \sum_{\substack{t,s\in\mathcal P\\t\ne s}}
        K_{128}(\mathbf a;t)K_{256}(\mathbf b;s).
\end{aligned}
\tag{UJB.7806}
$$

This reuses the full-label signed law without giving its equality
record to the native observer.

It remains to bound every possible coordinate tuple, rather than just
the fixed coordinate used by the attaining protocol. Flipping one
coordinate in **all** labels is a permutation of the full cube and
preserves the uniform distinct-label law. If that coordinate occurs
oddly among $a_1,\ldots,a_4$, it reverses the sign of the character
product. Thus every $m_Q(\mathbf a;p)$ and $K_Q(\mathbf a;t)$ is zero
in this case. If all multiplicities are even, the only possibilities
are one coordinate four times, or two distinct coordinates twice each.
These alternatives exhaust arbitrary coordinate choices, including all
four distinct coordinates.

For the nonzero cases put

$$
A_Q=\frac{Q(Q-2)}{(Q-1)(Q-3)}.
$$

The following small moment calculation follows directly from
(UJB.7803). If all four coordinates agree, the matching, either split,
and discrete moments are respectively

$$
m_t=1,\qquad m_{t^-}=m_{t^+}=-\frac1{Q-1},\qquad
m_D=\frac3{(Q-1)(Q-3)}.
\tag{UJB.7807}
$$

For example, the discrete numerator is $3Q^2-6Q$: the three pairings
and the one four-block merger are precisely its zero-character
partitions. The split has block characters $0,u,u$, with $u\ne0$;
the two nontrivial labels have character correlation $-1/(Q-1)$.
The same result also follows by including the third distinct label
in (UJB.7803).

If the two coordinates occur twice each, let $r\in\mathcal P$ be
their coordinate-equality matching. Its discrete moment is

$$
m_D=\frac{Q-6}{(Q-1)(Q-2)(Q-3)}.
\tag{UJB.7808}
$$

Here the block characters are $u,u,v,v$ with distinct nonzero basis
characters $u,v$. Only the matching grouping like characters and the
full merger contribute, with numerator $Q^2-6Q$. At $t=r$ the matching
moment is $1$ and both split moments are $-1/(Q-1)$, as above.
At $t\ne r$ the matching has block characters $u+v,u+v$, giving
$-1/(Q-1)$, whereas either split has characters $u+v,u,v$ and moment
$2/((Q-1)(Q-2))$. For this last value only their full merger contributes
$2Q$ in (UJB.7803).

Substitution into (UJB.7804) therefore gives the complete classification

$$
\begin{array}{c|c}
\text{coordinate multiplicities}&K_Q(\mathbf a;t)\\\hline
\text{some odd multiplicity}&0\\
\text{all four coordinates equal}&A_Q\\
\text{two pairs, with }t=r&A_Q\left(1-\dfrac2{(Q-2)^2}\right)\\
\text{two pairs, with }t\ne r&-\dfrac{A_Q}{Q-2}
\end{array}
\tag{UJB.7809}
$$

For $Q=128,256$, these formulas give $|K_Q(\mathbf a;t)|\le A_Q$;
the two-pair magnitudes are strictly smaller. Apply this bound to
each of the six terms of (UJB.7806):

$$
\begin{aligned}
|c_{\mathbf a,\mathbf b}|
 &\le\frac{6h}{256}A_{128}A_{256}\\
 &=\frac6{256\cdot68024448}
     \frac{16128}{15875}\frac{65024}{64515}
  =\frac{56}{158731093125}=\Delta.
\end{aligned}
\tag{UJB.7810}
$$

If each side uses one fixed coordinate, all three of its $K$ values
are the positive $A_Q$, so every term has the same positive sign and
$c_{\mathbf a,\mathbf b}=\Delta$. No calculation depends on which four
sample indices were selected: their edges are iid and all unused
samples integrate out under the same full injections. Together with
(UJB.7805) this proves the uniform sharp cell statement. $\square$

### 6.3 Every stopped adaptive leaf and every independent measurable seed

**Theorem 6.2 (attained maximum over all lawful eight-call protocols).**
For each fixed public $N\ge4$, under exactly the source and access
hypotheses of §6.1,

$$
V_8(N)=\frac{7168}{158731093125}.
\tag{UJB.7811}
$$

The upper bound includes the joint record of the independent installation,
seed and complete stopped transcript. It is attained by the eight
original-root operands in (UJB.7814) below.

Proof. Fix $\omega$ first, making all common controller maps
deterministic. For any control-consistent stopped leaf $\ell$, its
operands and replies are fixed; its source event is the single
unconditional cylinder

$$
C_\ell=\bigcap_{a=1}^{m_\ell}
 \{t:\operatorname{Read}_t(w_a)=y_a\},\qquad m_\ell\le8.
\tag{UJB.7812}
$$

Source-dependent adaptation chooses these operands along the path;
fixing the path fixes them. There is no extra condition on the source
from a stop or state value, since each is determined by the seed and
that reply path. Inconsistent paths have zero probability under both
laws. We evaluate (UJB.7812) under the original averaged preparation
law, without assuming uniform labels conditional on the acquired path.

By Proposition 5.3, each operand is constant or an invertible two-reply
function of one bit in one endpoint field. Let $I_A,I_T$ be the sample
indices whose respective endpoint fields are informatively touched on
this leaf, and $r=|I_A\cap I_T|$. The equality-record extension argument
in §5.3 applies to every fixed tuple with $r\le3$: its proof uses that
condition for the paired core, then adjoins independent one-sided
uniform endpoints and the channel (UJB.7708). The seven-call assumption
there was used only to force $r\le3$, not in that extension. Hence
$\mu_1^N(C_\ell)-\mu_0^N(C_\ell)=0$ whenever $r\le3$, also for
an eight-call tuple with many one-sided samples, multiple coordinates
of a field, repeated bits or constant replies.

Otherwise $2r\le|I_A|+|I_T|\le m_\ell\le8$ forces $r=4$ and equality
throughout. Consequently this leaf has exactly four paired sample
indices, exactly one informative invocation for each of their eight
endpoint roles, and no other invocation. A constant, repeated role or
second coordinate in one role would violate that count. Decoding each
of its invertible replies, the leaf is exactly one cell of one design
in Lemma 6.1. It follows that for **every** leaf

$$
|\mu_1^N(C_\ell)-\mu_0^N(C_\ell)|\le\Delta.
\tag{UJB.7813}
$$

The selected sample indices and coordinates may be completely different
on different leaves; (UJB.7810) is uniform over all of them.

At a fixed query node, its chosen word has at most two possible replies
on the whole promised comb family, by (UJB.7705) and Proposition 5.3.
Thus the attained reply tree is binary, possibly unary, with depth at
most eight. Induction on the remaining depth bounds its number of
stopped leaves by $2^8=256$: a stop contributes one leaf, a unary node
uses the bound of its child, and a binary node sums the two child
bounds. This retains all paid repeats and absences; it does not
normalize them away. Therefore its discrete leaf record has TV at most
$\tfrac12\cdot256\Delta=128\Delta$. The complete stopped record,
including operands, output and every retained local state, is a common
function of the seed and leaf. For this fixed seed it has TV at most
that bound too. Zero-call, early-stop and truncated-at-eight leaves
are included.

To cover all the admitted seeds, let $\Theta=\mathcal C_N$ be the finite
discrete space of prepared terms, with masses $p_i(\theta)=\mu_i^N
(\{\theta\})$. Using the source-blind boundary, the complete record is
a common function $\Psi(\omega,\theta)$. Measurability of the initial
state and every query/stop/update/output/retained-state map makes
$\Psi$ measurable by finite induction over the eight steps, padding
stopped runs with a fixed stop marker. Read itself is measurable:
words are countable discrete, $\Theta$ is finite discrete, and each
reply fiber is a countable union of word/term rectangles. Thus arbitrary
declared measurable state/output carriers introduce no missing
transcript-measurability premise.

For any measurable event $E$ in the joint seed/record space, its signed
probability is exactly

$$
\Pr_1((\omega,\Psi)\in E)-\Pr_0((\omega,\Psi)\in E)
 =\int_\Omega\sum_{\theta\in\Theta}
       (p_1(\theta)-p_0(\theta))
       \mathbf1_E(\omega,\Psi(\omega,\theta))\,d\nu(\omega).
$$

The integrand is a finite sum of measurable functions. For every fixed
$\omega$, the event section selects a set of leaves in that seed's
finite tree, so its absolute signed mass is at most $128\Delta$ by
the deterministic result. Taking absolute values and integrating proves
the same bound on every $E$, hence on joint TV. This is a direct
finite-source product-measure argument, needing no regular conditional
distribution and no standard-Borel or completeness assumption on
$\Omega$. Dropping the seed or applying any common measurable decoder
cannot increase this event bound. Independence of the *joint* hidden
preparation from $\omega$ is essential to the product formula.

For attainment choose the first coordinate of each endpoint type in
samples $1,2,3,4$, and use the actual root operands

$$
w_{A,j}=R^{15j}LL,\qquad w_{T,j}=R^{15j+7}LL,
\qquad j=0,1,2,3.
\tag{UJB.7814}
$$

They are (UJB.7706) at $b=15j+1$ and $b=15j+8$, respectively. The
reply $\beta$ decodes as zero and $\mathsf b$ as one; these are local
$L$ Reads of the slots, with the same original root on every call.
This deterministic protocol makes exactly eight lawful invocations.
Lemma 6.1 gives discrepancy $+\Delta$ on each of the $128$ even-parity
bit strings and $-\Delta$ on each of the $128$ odd ones. Thus the
event of even parity has gap $128\Delta=7168/158731093125$, attaining
the universal ceiling. Both the full transcript and its terminal parity
have exactly that TV. The supremum is a maximum for every fixed
$N\ge4$; additional prepared samples cannot improve it within eight
calls. $\square$

### 6.4 Exact decision, retained parity and resource boundaries

**Corollary 6.3 (equal-prior performance).** Under Theorem 6.2's
hypotheses the maximum equal-prior success of a lawful eight-call
binary source decision is

$$
\frac12+\frac{3584}{158731093125}
 =\frac{158731100293}{317462186250},
\qquad
\operatorname{Err}^{\mathrm{opt}}_{1/2}
 =\frac12-\frac{3584}{158731093125}
 =\frac{158731085957}{317462186250}.
\tag{UJB.7815}
$$

The attaining protocol (UJB.7814) outputs $i=1$ on even decoded parity
and $i=0$ on odd parity.

Proof. A binary decision has equal-prior success
$\tfrac12+\tfrac12(P_1(E)-P_0(E))$, where $E$ is its source-$1$ event;
independent final randomization can be included in the supplied seed.
Theorem 6.2 bounds the event gap by $128\Delta$, and its even-parity
event attains it with the positive orientation. Substituting gives
(UJB.7815). The two parity fibers contain only one sign each of the
signed discrepancy, explaining TV preservation without a reversible
transcript encoding. $\square$

The eight literal operand lengths are $2,9,17,24,32,39,47,54$, with
sum $224$ and maximum $54$, as in Proposition 5.5. Their construction,
storage and navigation are separate from eight invocation charges.
Proposition 5.3's exact $75N+4$ native preparation events also remain
separate, together with their operands, external edge sampling, selection
and storage of both full injection tables, controller installation,
isolated handoff, local computation, decoding and memory. A running
parity accumulator suffices for the acquired-bit component of the
terminal rule; it supplies no minimum-memory result for the whole
observer, operands, counters or source preparation.

The one-event gap of Proposition 5.5 remains $\Delta$. Collecting all
positive parity cells increases that gap by a factor of $128$ using
the same eight calls. This is optimal pairwise TV and equal-prior
binary decision performance under this particular averaged source law.
It is not a general sufficient-statistic claim, an optimum for other
priors or losses, source recovery, zero-error identification, a physical
or native sampler, a total-time optimum, a memory minimum, or an
optimum for any budget above eight. In particular $V_8(N)<1$, and
Proposition 5.5's common full-tree sublaw still excludes zero-error
source identification at fixed $N$ even after complete decoding.

### 6.5 Suppliers, mathematical content and scope of verification

The source-specific increment is (UJB.7803)–(UJB.7810)'s uniform
mixed-coordinate coefficient bound and its use on every stopped
adaptive leaf and every independent measurable seed. The actual graph,
all $w_3$ values, order-six/edge bijection, complete four-sample signed
law, native comb, all-address bridge and first distinction are reused
from §§3–5 with their original hypotheses. Their different observer
contracts are not identified. Section 1.3's distinction between a law
difference and what one run can identify remains applicable; this
finite decision theorem does not settle §1.4's four-view transport and
mutual-recovery conditions.

The finite real-function Fourier expansion and coefficient identity
are [O'Donnell, *Analysis of Boolean Functions*, Theorem 1.1 and
Proposition 1.8](https://arxiv.org/abs/2105.10386v1), applied here to
the signed mass function on eight bits. They require neither an
independent observed-bit law nor an independent source assignment.
His Definition 3.13 excludes repeated-coordinate paths; that convention
is not imported into native invocation accounting. The binary leaf
bound above is proved directly with repetitions and unary nodes.

The once-sampled function
$w\mapsto\operatorname{Read}_{\theta}(w)$ and common adaptive controller
have the random-function/interaction interpretation of
[Maurer, *Indistinguishability of Random Systems*, Definitions 2–3,
9–10 and Lemma 4](https://crypto.ethz.ch/publications/files/Maurer02.pdf).
This supplies framework and credit, not the source-specific numerical
ceiling or an assumption eliminating adaptive advantage. That ceiling
comes from (UJB.7813) for this actual source. The equal-prior convention
also agrees with the paragraph following Maurer's Lemma 5.

For the finite parity channel $W(y,e)=\mathbf1\{e=\sum_jy_j\bmod2\}$,
$W\ge0$ and each row sums to one. Its fibers do not mix positive and
negative discrepancy signs. This is precisely the finite hypothesis
of the existing
[`total_variation_channel_eq_iff_no_sign_mixing`](../../../D5/S3/TotalVariation/Equality/DataProcessingEquality.lean)
supplier, used here as ordinary mathematical credit for the TV equality.
Reading that result supplies no fresh compiled application. Likewise
[`ActualTreeReadoutAcquisition.RandomContract`](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)
explicitly assumes neither measurable transcripts nor a common good-seed
set, and its `paid` functional counts distinct addresses. The stronger
measurable-map and pathwise invocation contract used here is stated in
§6.1 and Assumption 5.2, not inferred from that Lean interface.

This is a `repo-derived` application of the cited finite methods with
an additional source-specific bound, not a new general Fourier, TV or
random-system theorem. The named suppliers and bounded searches in the
existing TV/budget modules do not supply this native eight-call ceiling;
no worldwide novelty or exhaustive literature-absence claim is made.
These are ordinary conditional proofs and exact arithmetic, not Lean
verification. The external preparation and isolation premises are not
verified physical capabilities. The autonomous recovery of space,
time, boundary, memory and recursive observation remains unresolved
by this finite result.

## 追加锚（本行以下为增补区）

## 7. Nine invocations preserve the decision optimum but not the next-read law

### 7.1 The nine-call experiment and its signed cylinders

**Definition 7.1 (one more invocation of the same prepared endpoint).**
Retain Definition 5.1, Assumption 5.2 and §6.1 in full, including the
actual graphs (UJB.7502), all three $w$ coordinates, iid edge sampling
with replacement, and the once-sampled full injections into $128$ and
$256$ words. The installation and arbitrary measurable seed remain
independent of the joint hidden preparation. Replace only the pathwise
cap of eight actual original-root Read invocations by nine. Define
$\mathcal A_9(N)$ and $V_9(N)$ by this replacement in (UJB.7801).
Constants, repeats, absences, stopping and arbitrary finite original-root
operands retain their original meanings and charges. No operation on
an endpoint handle or on an injection table is added.

A bit position is a triple of sample index, endpoint type and coordinate
in its word. Distinct positions can have equal values because their
actual endpoints or labels agree; their bits are not assumed independent.
For a fixed list of $d$ distinct positions let $Z$ be its bit vector
and set $D_Z(z)=\Pr_1(Z=z)-\Pr_0(Z=z)$.

**Lemma 7.2 (at most one surviving character on nine positions).**
For every public $N\ge4$ and every such fixed list,

$$
\begin{array}{ll}
d\le7:&D_Z=0,\\
d=8:&|D_Z(z)|\le\Delta,\\
d=9:&|D_Z(z)|\le\Delta/2,
\end{array}
\qquad\Delta=\frac{56}{158731093125}.
\tag{UJB.7901}
$$

For $d=9$, either $D_Z=0$ or there exist an eight-element subset $S$
of the nine positions and $|c|\le\Delta$ such that

$$
D_Z(z)=\frac c2(-1)^{\sum_{a\in S}z_a}.
\tag{UJB.7902}
$$

This does not assert that the remaining bit is conditionally fair under
either source.

Proof. The first line is Theorem 5.4. More generally the selected-field
argument of §5.3 applies whenever at most three sample indices are
touched on both types, even if more than seven coordinates are read:
the paired equality core has at most three edges, all other selected
endpoints are independent one-sided uniform vertices, and (UJB.7708)
is the common full-injection channel. Thus its whole selected-bit law
is common. A nonzero eight-position law must consequently touch four
paired indices, exactly once in each of their eight endpoint roles.
Lemma 6.1 gives its full-parity form with coefficient bounded by
$\Delta$. Its coordinate-flip argument also supplies the necessary
condition that each coordinate occurs evenly on each type separately.

Apply finite Boolean Fourier expansion to the signed mass on nine bits.
For $S\subseteq[9]$ its coefficient is

$$
\widehat D_Z(S)=2^{-9}\left(
 \mathbb E_1(-1)^{\sum_{a\in S}Z_a}
 -\mathbb E_0(-1)^{\sum_{a\in S}Z_a}\right).
\tag{UJB.7903}
$$

All coefficients with $|S|\le7$ vanish by the common marginals. The
full nine-position coefficient vanishes too: some coordinate on one
endpoint type has odd multiplicity among nine total occurrences.
Complementing that coordinate in every word of that type preserves
each uniform full-injection law and negates the character. Each of
its source expectations is therefore zero. The Fourier expansion and
its uniform cube normalization are [O'Donnell, *Analysis of Boolean
Functions*, Theorem 1.1 and Proposition 1.8](https://arxiv.org/abs/2105.10386v1).
They apply to this real signed mass function, without requiring a
uniform or independent observation law.

It remains to count nonzero eight-position marginals. If there are at
most three paired indices, none is nonzero. Otherwise there are exactly
four, since five pairs require ten positions. Their eight endpoint
roles leave one extra position. If this is a new one-sided sample,
only its deletion can leave four complete pairs. If it is a second
coordinate in an existing role, only deletion of one of that role's
two positions can do so. Those two coordinates are distinct. On that
type let $u$ be the sum in $\mathbb F_2^d$ of the coordinate basis
vectors of the other three roles. Retaining coordinate $h$ satisfies
the necessary even-multiplicity condition only when $u+e_h=0$.
At most one of the two distinct coordinates can satisfy it. Thus at
most one eight-position marginal survives in either case.

For that marginal, if present, Lemma 6.1 gives signed mass
$c(-1)^{\sum_{a\in S}z_a}$ with $|c|\le\Delta$. Its full character
moment difference is $2^8c$, so (UJB.7903) gives nine-cube coefficient
$c/2$. Fourier reconstruction now proves (UJB.7902). $\square$

### 7.2 The adaptive plateau with actual invocation accounting

**Theorem 7.3 (sharp nine-invocation plateau).** For every public
$N\ge4$, under Definition 7.1,

$$
V_9(N)=V_8(N)=128\Delta=\frac{7168}{158731093125}.
\tag{UJB.7904}
$$

The bound also holds with the independent installation and seed retained
jointly with the complete stopped record. The original eight operands
(UJB.7814) attain this at-most-nine maximum. The optimal equal-prior
success and error are consequently still (UJB.7815).

Proof. Fix $\omega=(J,U)$. Each control-consistent leaf has the single
unconditional cylinder of its fixed operands and replies, as in
(UJB.7812). Proposition 5.3 makes every operand constant on the whole
promise or an invertible two-reply function of one bit position.
Different operands can reveal the same bit; every invocation remains
paid. Once a bit has been acquired, every later read of it is
determined on the current promise cylinder.

For counting cylinders only, suppress constant nodes and subsequent
reads of previously acquired positions. Keep their original operands,
replies and invocation charges as deterministic data on the path.
This describes the same record; it does not grant a free operation.
A leaf now has depth $d$ equal to its number of distinct acquired
positions, at most its actual invocation count and hence at most nine.
The tree is binary, with zero-mass branches optionally omitted, and
the leaf cylinders are unchanged. Truncating at nine invocations also
defines it on unsupported promise paths without changing any attained
record. Stopping, retained state and operand choice add no source
condition beyond the acquired path.

For any binary tree with leaf depths $d_\ell$,
$\sum_\ell2^{-d_\ell}\le1$: assign the root weight one and each
child half its parent's weight, then sum terminal weights. Lemma 7.2
gives on each leaf

$$
|\mu_1^N(C_\ell)-\mu_0^N(C_\ell)|
 \le256\Delta\,2^{-d_\ell}.
\tag{UJB.7905}
$$

At depths at most seven the left side is zero, at depth eight the
right side is $\Delta$, and at depth nine it is $\Delta/2$. Hence

$$
\operatorname{TV}(\text{leaf law}_0,\text{leaf law}_1)
 \le128\Delta\sum_\ell2^{-d_\ell}\le128\Delta.
\tag{UJB.7906}
$$

The original complete record, including all suppressed paid calls,
states and output, is a common function of the leaf and fixed seed.
It has the same event bound. This covers unary nodes, zero calls,
early stops, repeated coordinates, constants, absences and designs
that differ between adaptive leaves.

To include every admitted seed, put $\Theta=\mathcal C_N$,
$p_i(t)=\mu_i^N(\{t\})$ and let $\Psi(\omega,t)$ be the complete
record. This is measurable by finite induction through nine steps,
padding stopped runs with a stop marker. Read is measurable on the
countable discrete word space and finite discrete term space; all
controller maps are measurable by hypothesis. For each measurable
joint seed/record event $E$, joint independence gives

$$
\Pr_1((\omega,\Psi)\in E)-\Pr_0((\omega,\Psi)\in E)
 =\int_\Omega\sum_{t\in\Theta}(p_1(t)-p_0(t))
    \mathbf1_E(\omega,\Psi(\omega,t))\,d\nu(\omega).
\tag{UJB.7907}
$$

The inner signed mass has absolute value at most $128\Delta$ for
every $\omega$ by (UJB.7906). Integrating gives the joint TV bound.
This finite-source argument needs no regular conditional distribution,
standard-Borel assumption or completeness assumption on the seed
space. Independence from the entire hidden preparation is essential;
independence from $i$ alone would not give this product formula.
Common measurable decoders preserve the event bound by inverse images.

Finally $\mathcal A_8(N)\subseteq\mathcal A_9(N)$ and Theorem 6.2's
eight-call protocol attains $128\Delta$. This proves equality, also
for $N=4$, where a fifth sample is not available. The equal-prior
formula follows exactly as in Corollary 6.3. The correspondence with
[Maurer, *Indistinguishability of Random Systems*, Definitions 9–10
and Lemma 4](https://crypto.ethz.ch/publications/files/Maurer02.pdf)
is a stationary random Read function inside a common adaptive
controller; it does not supply this source-specific ceiling. $\square$

### 7.3 Positive equal-posterior histories with different ninth-read laws

**Proposition 7.4 (the actual continuation obstruction).** Under the
same contract, now with $N\ge5$, acquire the first coordinates in
samples $1,\ldots,4$ by (UJB.7814). In endpoint-type block order write
$Y=(L_1,L_2,L_3,L_4,R_1,R_2,R_3,R_4)$, and put

$$
B_+=\{Y=(0000,0000)\},\qquad
B_-=\{Y=(1111,0000)\}.
\tag{UJB.7908}
$$

Both histories are positive under both actual laws, have even parity
and signed source discrepancy $+\Delta$, and satisfy
$\Pr_i(B_+)=\Pr_i(B_-)$ for each $i=0,1$. Thus their source
posteriors agree for every common prior $\theta=\Pr(i=1)\in[0,1]$,
including $0$ and $1$. Nevertheless the actual ninth operand
$R^{60}LL$, of length $62$, reads $L_5$ from the already prepared
fifth sample and satisfies

$$
\Pr_i(L_5=0\mid B_+)=q_i>\frac12,\qquad
\Pr_i(L_5=0\mid B_-)=1-q_i<\frac12,\qquad
2q_i-1\ge\frac7{1143},
\tag{UJB.7909}
$$

with exact values

$$
q_0=\frac{4405844809873481}{8604951131412990},\qquad
q_1=\frac{4405845183168137}{8604951878002302}.
\tag{UJB.7910}
$$

The mixed-prior continuation probabilities also differ by at least
$7/1143$ for every $\theta\in[0,1]$. Neither terminal parity nor the
complete posterior on $i$ therefore supplies this next-read kernel.

Proof. Repeating one fixed actual edge on the first four draws has
positive probability; assigning its left label first bit zero or one
and its right label first bit zero has probability $1/4$. Thus both
histories have positive actual probability, not just promise membership.
Complementing the first coordinate in every left label is a
probability-preserving bijection of full injections under each source.
It sends $B_+$ to $B_-$ and complements $L_5$, giving equal event
probabilities and complementary continuation probabilities. Lemma 6.1
gives discrepancy $+\Delta$ because both parities are even.

Let $K$ be the number of distinct actual left endpoints among the
first four draws. On $B_+$, the $K=k$ labels all have first bit zero,
leaving $64-k$ zero-bit labels among the $128-k$ unused labels. The
fifth left endpoint is uniform on $72$ vertices and independent of the
first four draws and injections. Given the first endpoints and labels,
it hits their $k$ distinct vertices with probability $k/72$; otherwise
the uniform full-injection extension supplies a zero bit with probability
$(64-k)/(128-k)$. Past right-bit conditioning can change the law of
$K$ but not this extension law, since the full injections are independent.
Consequently

$$
\begin{aligned}
g(k)&=\frac{k}{72}+\frac{(72-k)(64-k)}{72(128-k)}
 =\frac12+\frac{56k}{144(128-k)},\\
q_i&=\mathbb E_i[g(K)\mid B_+].
\end{aligned}
\tag{UJB.7911}
$$

Since $1\le K\le4$ and $k/(128-k)\ge1/127$, this gives
$2q_i-1\ge56/(72\cdot127)=7/1143>0$.

For a finite specification of the exact arithmetic, reuse
$N_i(p,s)$ in (UJB.7603) and $f_Q(k)=(Q/2)_k/(Q)_k$. Put
$W_i(p,s)=N_i(p,s)f_{128}(|p|)f_{256}(|s|)$. Then

$$
\Pr_i(B_+)=1944^{-4}\sum_{p,s}W_i(p,s),\qquad
q_i=\frac{\sum_{p,s}W_i(p,s)g(|p|)}{\sum_{p,s}W_i(p,s)}.
\tag{UJB.7912}
$$

The prescribed-equality counts in (UJB.7603) are products, over tree
components with $u$ left and $v$ right vertices, of
$1944\,8^{u-1}27^{v-1}$, except for the four-cycle with count
$H_i$; here $H_0=209952$ and $H_1=419904$. Partition inversion uses
$\mu(p,r)=\prod_{B\in r}(-1)^{k_B-1}(k_B-1)!$, where $k_B$ counts
$p$-blocks in $B$. The resulting sums over the $15$ partitions per
side give (UJB.7910) and

$$
\Pr_0(B_+)=\frac{5624151066283}{1383134192451000},\qquad
\Pr_1(B_+)=\frac{478052882111239}{117566406358335000}.
\tag{UJB.7913}
$$

Their difference is $\Delta$. All third $w$ coordinates and free
$z$ multiplicities remain in these actual graph counts.

Writing these positive event probabilities as $b_0,b_1$, the common
source posterior is
$r_\theta=\theta b_1/((1-\theta)b_0+\theta b_1)$. The two mixed
continuation probabilities are $(1-r_\theta)q_0+r_\theta q_1$ and
its complement. Their difference is a convex combination of the two
positive gaps, proving the assertion also for known-source priors.

This does not conflict with Theorem 7.3: source discrimination and
next-read prediction are different tasks, and (UJB.7902) asserts no
fair-bit condition under either individual source. Nor does it
contradict
[`posterior_future_policy_universal_sufficiency`](../../../D5/S3/Estimation/DecisionRisk/PosteriorFuturePolicySufficiency.lean)
or [`PosteriorHistoryCompression`](../../../D5/S3/Estimation/DecisionRisk/PosteriorHistoryCompression.lean).
Those suppliers require a future kernel indexed by the chosen latent
state and policy/experiment, independent of history once that state
is fixed. Taking the state to be $i$ alone omits the shared injections
and fails that premise here, even when $i$ is known. A full hidden
state can supply the premise but is not an observer port. $\square$

## 8. The exact thirty-five-class boundary for four future coordinate pairs

### 8.1 The predictive task uses the actual prepared source

**Definition 8.1 (fixed-coordinate histories and future laws).**
Retain Definition 5.1, Assumption 5.2 and §6.1, now with public
$N\ge8$, and fix the first coordinate on both endpoint types.
For sample $j$ let $X_j=(\lambda(a_j)_1,\varrho(t_j)_1)$, in cell
order $00,01,10,11$. Its two actual original-root operands are

$$
w_{A,j}=R^{15(j-1)}LL,\qquad
w_{T,j}=R^{15(j-1)+7}LL.
\tag{UJB.8001}
$$

Future indices are distinct already prepared but unread indices;
there is no new draw, reset, rerooting, map access or fresh injection.
Fix a public prior $\theta=\Pr(i=1)\in[0,1]$. For a particular
ordered acquired history $h=(X_1,\ldots,X_4)$ let $n_c(h)$ count
cell $c$, so $\sum_cn_c=4$. The target law is
$K_\theta(h)=\mathcal L_\theta(X_5,\ldots,X_8\mid h)$.
A deterministic predictive summary $S$ supplies this exact law if
$K_\theta$ is a function of $S(h)$ at every positive acquired history.

For realized full injections define
$A_0=\{a:\lambda(a)_1=0\}$, $T_0=\{t:\varrho(t)_1=0\}$,
$L=|A_0|$, $D=|T_0|$, $C=|E_i\cap(A_0\times T_0)|$, and

$$
q=\frac1{1944}(C,\ 27L-C,\ 8D-C,\ 1944-27L-8D+C).
\tag{UJB.8002}
$$

These are the four edge proportions by the actual degrees in
(UJB.7503). Conditional on $i$ and the full injections, the $X_j$
are iid categorical with parameter $q$ because the original edge
draws are independent uniform draws with replacement. This is a
conditional representation, not a new categorical sampling port.
Let $\nu_i$ be the finite pushforward law of $q$ under the original
full injections and put $\nu_\theta=(1-\theta)\nu_0+\theta\nu_1$.
For each nonnegative integer vector $n$ define

$$
Z_\theta(n)=\int q^n\,d\nu_\theta(q),\qquad
q^n=\prod_cq_c^{n_c},\qquad 0^0=1.
\tag{UJB.8003}
$$

These finite sums treat arbitrary real $\theta$ as a fixed mathematical
parameter; they do not supply an effective exact-real oracle.

### 8.2 A common positive support in both actual graph laws

**Lemma 8.2 (a nonsingular grid of actual cuts).** For each actual
source separately, $\operatorname{supp}\nu_i$ contains these $125$
distinct, strictly positive-cell vectors of (UJB.8002):

$$
L=36+x+y,\qquad D=120+z,\qquad C=480+12x+15y+4z,
\qquad x,y,z\in\{0,1,2,3,4\}.
\tag{UJB.8004}
$$

The affine map to $(L,D,C)$ has determinant $-3$, and its subsequent
map to $\sum_cq_c=1$ is invertible. The support is consequently
present under every $\theta\in[0,1]$, including $0$ and $1$.

Proof. Use the actual sets
$A=(\mathbb F_3^2\setminus\{0\})\times\mathbb F_3^2$ and
$T=\mathbb F_3^3\times\mathbb F_3^2$. Set $v_+=(1,0)$ and
$v_-=(2,0)=-v_+$. Both actual bilinear maps satisfy

$$
B_i(v_+,w)=(w_1,w_2),\qquad
B_i(v_-,w)=-(w_1,w_2),\qquad i=0,1.
\tag{UJB.8005}
$$

The base left cut comprises all nine $s$ values for each
$v\in\{(0,1),(0,2),(1,1),(1,2)\}$. It has size $36$ and exactly
four neighbors at each right vertex, one $s=B_i(v,w)$ for each of
those four $v$. This holds in both graphs, without identifying their
other incidences.

Partition $\mathbb F_3^2$ into

$$
\begin{aligned}
P&=\{(0,1),(0,2),(1,0),(1,1)\},\\
Q&=\{(1,2),(2,0),(2,1),(2,2)\},\qquad\{(0,0)\}.
\end{aligned}
$$

For each $s$, the right fiber
$T_s=\{(w,z):(w_1,w_2)=s\}$ has $27$ vertices: three choices of
$w_3$ and nine of $z$. Order each fiber and let the base right cut
contain its first $12$ vertices for $s\in P$, first $15$ for $s\in Q$,
and first $12$ for $s=(0,0)$. Its size is $120$. Fix four reserved
vertices among the $15$ unused vertices in $T_{(0,0)}$.

Add the first $x$ vertices of $\{(v_+,s):s\in P\}$ and first $y$
vertices of $\{(v_-,-s):s\in Q\}$ to the base left cut. Add the
first $z$ reserved vertices to the base right cut. Each new left
vertex has respectively $12$ or $15$ neighbors in the base right cut,
by (UJB.8005). None is adjacent to a reserved vertex, since neither
$P$ nor $Q$ contains zero. Every reserved right vertex has four
neighbors in the base left cut. Thus the three sizes and the cut
count are exactly (UJB.8004), with no $xz$ or $yz$ terms.

These cuts are actual possible zero-bit preimages of full injections.
Here $36\le L\le44$, so both $L$ and $72-L$ are at most $64$;
$120\le D\le124$, so $D$ and $243-D$ are at most $128$. For a
specified left cut its probability of being exactly the zero-bit
preimage is

$$
\frac{(64)_L(64)_{72-L}}{(128)_{72}}>0;
$$

for a specified right cut the probability is
$(128)_D(128)_{243-D}/(256)_{243}>0$. The full maps are independent,
so each cut pair and its $q$ have positive actual probability under
each source. No unused label coordinate has been deleted or redrawn.

The four cell numerators are

$$
\begin{aligned}
1944q_{00}&=480+12x+15y+4z,\\
1944q_{01}&=492+15x+12y-4z,\\
1944q_{10}&=480-12x-15y+4z,\\
1944q_{11}&=492-15x-12y-4z.
\end{aligned}
\tag{UJB.8006}
$$

Their grid minima are respectively $480,476,372,368$, hence positive.
Also

$$
\det\begin{pmatrix}1&1&0\\0&0&1\\12&15&4\end{pmatrix}=-3.
\tag{UJB.8007}
$$

The inverse from $q$ is $C=1944q_{00}$,
$L=72(q_{00}+q_{01})$ and $D=243(q_{00}+q_{10})$.
It proves nonsingularity and distinctness. Every mixture of the two
laws retains these positive support masses, including either unmixed
endpoint. $\square$

### 8.3 Exact conditional-law separation and minimality

**Theorem 8.3 (exactly thirty-five predictive classes).** Under
Definition 8.1, for every fixed public $N\ge8$ and fixed public prior
$\theta\in[0,1]$, all $256$ ordered acquired histories are positive,
and

$$
K_\theta(h)=K_\theta(h')\quad\Longleftrightarrow\quad n(h)=n(h').
\tag{UJB.8008}
$$

The next-four-pair conditional law therefore has exactly $35$ values.
The count is sufficient for every remaining fixed-coordinate sample
sequence through $N$. At the completed-four-pair boundary, $35$ is
the minimum number of values of a deterministic summary supplying
those exact laws. Count and future-law value determine one another
on their realized images.

Proof. For a particular ordered acquired word with counts $n$, the
conditional iid representation gives probability $Z_\theta(n)$.
Its joint probability with a particular ordered future word on distinct
unread indices, with counts $m$, is $Z_\theta(n+m)$. Hence

$$
\Pr_\theta(\text{that ordered future word}\mid h)
 =\frac{Z_\theta(n+m)}{Z_\theta(n)}.
\tag{UJB.8009}
$$

There is no multinomial factor for a particular ordered word. If only
future counts are requested, multiply by $|m|!/\prod_cm_c!$.
Lemma 8.2 gives positive mass at positive-cell $q$, so
$Z_\theta(n)>0$ for every $n$. Thus every ordered history is positive.
Formula (UJB.8009) proves sufficiency for every remaining length at
most $N-4$, and equality of counts implies equality of future laws.
All indices in this formula are originally prepared draws.

Conversely suppose two next-four-pair laws agree. Write $Z=Z_\theta$
and $n=n(h)$, $n'=n(h')$. The polynomial

$$
f(q)=\frac{q^n}{Z(n)}-\frac{q^{n'}}{Z(n')}
\tag{UJB.8010}
$$

is homogeneous of degree four. For every $|m|=4$, choose one ordered
future word with counts $m$. Equality in (UJB.8009) gives
$\int q^mf(q)\,d\nu_\theta(q)=0$. In particular this holds for
$m=n$ and $m=n'$, so

$$
\int f(q)^2\,d\nu_\theta(q)
 =\frac1{Z(n)}\int q^nf(q)\,d\nu_\theta(q)
 -\frac1{Z(n')}\int q^{n'}f(q)\,d\nu_\theta(q)=0.
\tag{UJB.8011}
$$

This finite nonnegative sum forces $f$ to vanish at every positive
support point, in particular all $125$ points of Lemma 8.2. The
positive Gram/moment argument and finite interpolation are mature
algebraic tools; compare [Laurent, *Sums of Squares, Moment Matrices
and Polynomial Optimization*, Lemma 2.3](https://homepages.cwi.nl/~monique/files/moment-ima-update-new.pdf).
The degree bound for this actual support can be verified directly.

Compose $f$ with the affine map (UJB.8004)–(UJB.8006), obtaining a
polynomial $g(x,y,z)$ of total degree at most four, vanishing on
$\{0,1,2,3,4\}^3$. Fixing grid values of $(y,z)$ gives a polynomial
of degree at most four in $x$ with five roots, hence identically zero.
Its coefficients in $x$ vanish on all grid pairs $(y,z)$. Repeating
the five-root argument first in $y$ and then in $z$ forces every
coefficient to vanish. Thus $g$ vanishes on $\mathbb R^3$.
Nonsingularity from Lemma 8.2 implies $f=0$ on the whole hyperplane
$\sum_cq_c=1$. For any $r\in(0,\infty)^4$ and $s=\sum_cr_c$,
homogeneity gives $f(r)=s^4f(r/s)=0$. A polynomial vanishing on the
positive open orthant is identically zero, by successively applying
the univariate root identity to each coordinate. Distinct monomials
$q^n$ and $q^{n'}$ are linearly independent, and both denominators
are positive, so (UJB.8010) is identically zero only if $n=n'$.
This proves (UJB.8008) in both directions.

There are $\binom{4+4-1}{4-1}=35$ nonnegative four-cell counts of total
four. Each is realized by a positive ordered word, and (UJB.8008)
makes their laws distinct. Any deterministic summary supplying those
laws must separate every pair of different counts, requiring $35$
values. The count attains that bound. Its induced map to the
future-law image is a bijection, proving the mutual-recovery assertion.

The separation principle is the existing
[`causal_state_factorization`](../../../D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization.lean):
unequal future laws force unequal sufficient-summary values. The
conditional-future equivalence corresponds to [Shalizi and Crutchfield,
*Computational Mechanics: Pattern and Prediction, Structure and
Simplicity*, Definition 5, equation (16), Lemma 7 and Theorem 2](https://arxiv.org/abs/cond-mat/9907176v2).
Their stationary entire-past, almost-sure entropy minimality is not
transferred as this finite cardinality theorem. The actual-source
support and degree-four separation establish the exact $35$ here;
general factorization alone supplies no such count. $\square$

### 8.4 Dynamic updates, paid acquisition and the recovery boundary

**Proposition 8.4 (task-specific memory and native costs).** At each
completed-pair boundary in Definition 8.1 the count updates by

$$
n\longmapsto n+e_c\quad\text{on acquiring the next pair }c.
\tag{UJB.8012}
$$

At the completed-four-pair boundary its exact deterministic predictive
name needs and admits six fixed-width bits. This is a naming payload,
not total observer memory. Acquiring the past four pairs costs eight
invocations, total literal operand length $224$, maximum $54$.
The ninth-read witness adds one length-$62$ invocation, for nine
invocations and length sum $286$. The next four pairs cost eight
further invocations, length sum $704$, maximum $114$; all eight pairs
therefore cost sixteen invocations and length sum $928$. Native
preparation still requires exactly $75N+4$ events, with its original
separate external costs.

Proof. The next completed cell multiplies the hidden likelihood
$q^n$ by $q_c$, yielding $q^{n+e_c}$ and (UJB.8012). After $j$
completed pairs there are at most $\binom{j+3}{3}$ count values,
giving a naming upper bound $\lceil\log_2\binom{j+3}{3}\rceil$
bits when $j$ is separately known. No minimality assertion at other
boundaries is needed. At $j=4$, Theorem 8.3 requires all $35$ names,
and $2^5<35\le2^6$ proves the exact fixed-width bound. Enumerating
those $35$ vectors gives an encoding; their finite conditional laws
give a mathematical decoder for fixed $\theta$, not an efficient
exact-real computation theorem for arbitrary priors.

Pair halves are acquired in separate paid invocations. An unmatched
reply, its type and the public query cursor are separate state. The
completed-pair count does not specify them or predict a partly matched
continuation. Packed-name updates, operand construction and evaluation
of finite sums can need further workspace. The bound includes none
of that workspace, the installed controller, law descriptions, seed,
output representation or preparer memory.

The past operand lengths are $2,9,17,24,32,39,47,54$. Sample five's
first left bit is at slot $61$, giving $R^{60}LL$ of length $62$.
For samples five through eight the lengths are
$62,69,77,84,92,99,107,114$, summing to $704$. Every word is read from
the same original root. Invocation charges are not replaced by distinct
field counts or word lengths; they also do not pay for constructing,
storing or navigating operands. Proposition 5.3's preparation events,
external iid edge sampling, both full injection tables, installation,
isolated handoff, computation, decoding and all other memory keep their
separate costs. Theorem 7.3 covers the full native menu, including paid
repeats, constants and absences; this fixed schedule concerns only the
named predictive task. $\square$

**Proposition 8.5 (the exact recovered relation and its exclusions).**
For each fixed prior in Theorem 8.3, the four-cell count, the next-four
fixed-coordinate pair law, and the laws of all remaining fixed-coordinate
sequences are mutually recoverable on their realized images. Proposition
7.4's two actual histories lie in different classes despite their equal
source posteriors and terminal parity. These equivalences do not give
historical reconstruction or full native-menu sufficiency.

Proof. The count determines every remaining law by (UJB.8009). Their
collection includes the next-four law because $N\ge8$, and that law
determines the count by (UJB.8008). For $B_+$ and $B_-$ the counts are
respectively $(4,0,0,0)$ and $(0,0,4,0)$. Proposition 7.4 gives their
equal source posteriors and parity but unequal actual future marginal.
The ordered words $(00,00,01,01)$ and $(00,01,00,01)$ have the same
count and are both positive, but distinct ordered histories. This
explicitly prevents historical reconstruction from that count.

Those last two histories also have different acquired right bits at
sample two. Rereading that original-root slot with one paid invocation
returns different deterministic bits. Their full native continuation
laws therefore differ, despite equal laws for unread fixed-coordinate
pairs. Thus the count is not sufficient for the full native menu.
No factorization for other coordinates, matched old slots or unmatched
pair halves is inferred. The $35$-value bound concerns deterministic
summaries returning the history-specific exact law; it is not a lower
bound for randomized generation of an averaged future law. Forgetting
the realized history changes the prediction task.

All recovery maps here are finite mathematical maps for a fixed prior,
not operations obtaining the hidden injections, free endpoint handles
or an exact real prior. The common full-tree overlap of Definition 5.1
and §§5–6's resource boundaries still apply. The source-specific
additions are the odd-character nine-call ceiling, the positive
same-posterior continuation obstruction, and the actual cut-support
separation yielding $35$ classes. The Fourier, random-system,
Bayesian-mixture, interpolation and causal-state principles are reused;
no new general theorem in those subjects or worldwide novelty is
asserted. These are ordinary conditional mathematical proofs, not
Lean-verified declarations. They identify a particular predictive
boundary and its memory expression; mutual recovery of space, time,
boundary, memory and recursive observation under the full original
operations remains unresolved. $\square$

## 追加锚（本行以下为增补区）


## 9. Indexed acquisition on the entire stationary native Read menu

### 9.1 The actual generator and its indexed restrictions

Throughout §§9–14, assume Definition 5.1 and Assumption 5.2: public
finite $N\ge4$, $k=15N$, the actual graphs
$E_i$ of Proposition 3.2, both complete once-shared injections, the
stationary original root, and no additional source port. Fix public
$\theta\in[0,1]$. Every conditional statement below is restricted to
positive-probability evidence under this very prior. Specific results
requiring unread indices impose their additional bounds on $N$.

**Definition 9.1 (complete shared generator and labelled edges).** Put
$\mathcal L=\{0,1\}^7$, $\mathcal R=\{0,1\}^8$, and
$\mathcal Y=\mathcal L\times\mathcal R$. The complete once-shared
generator is $g=(i,\lambda,\varrho)$, including every value of both
full injections, not just their observed coordinates or their cut sizes.
Its finite prior $\pi_\theta$ assigns to each such $g$ the mass

$$
\pi_\theta(g)=\frac{w_i}{(128)_{72}(256)_{243}},\qquad
w_0=1-\theta,\quad w_1=\theta.
\tag{UJB.9001}
$$

Here $(Q)_r$ is the falling factorial. Let $\mathcal G_\theta$ be
its positive-mass support. Transport the actual edge relation by the
injections, writing

$$
\begin{aligned}
\mathcal E_g&=\{(\lambda(a),\varrho(t)):(a,t)\in E_i\},\\
p_g(y)&=\frac1M\mathbf1_{\{y\in\mathcal E_g\}},\qquad M=1944.
\end{aligned}
\tag{UJB.9002}
$$

Thus $|\mathcal E_g|=M$, with no multiplicities lost: Proposition 3.2's
edge adapter is bijective and both label maps are injective. Given $g$,
the originally prepared label pairs $Y_1,\ldots,Y_N$ are iid with law
$p_g$. They are not new draws available to the observer. Their fifteen
bits, concatenated in the original order, are exactly $z$ in (UJB.7702).

An indexed cache $D$ consists of masks $m_j\subseteq[15]$ and acquired
bit assignments $d_j\in\{0,1\}^{m_j}$, for $1\le j\le N$.
Repeated information is entered once in this cache, while its invocation
cost is counted every time. Define the label rectangle

$$
B_j(D)=\{y\in\mathcal Y:y|_{m_j}=d_j\},\qquad
r_j(g;D)=\frac{|\mathcal E_g\cap B_j(D)|}{M}.
\tag{UJB.9003}
$$

The rectangle can constrain arbitrary, overlapping or disjoint subsets
of coordinates within a sample. Different samples keep their original
indices even when their masks coincide. Empty masks have $r_j=1$.
Let

$$
\begin{aligned}
Z(D)&=\sum_g\pi_\theta(g)\prod_{j=1}^Nr_j(g;D),\\
\pi_D(g)&=Z(D)^{-1}\pi_\theta(g)\prod_{j=1}^Nr_j(g;D),\\
Q_{g,j,D}(y)&=
 \frac{\mathbf1_{\{y\in\mathcal E_g\cap B_j(D)\}}}
 {|\mathcal E_g\cap B_j(D)|}.
\end{aligned}
\tag{UJB.9004}
$$

Only $Z(D)>0$ caches are admitted. The last expression is needed only
where $\pi_D(g)>0$, so every denominator used there is positive.
The indexed acquired-law interface is

$$
\mathsf I_D(y_1,\ldots,y_N)
 =\sum_g\pi_D(g)\prod_{j=1}^NQ_{g,j,D}(y_j).
\tag{UJB.9005}
$$

It is a conditional law of the actual entire prepared array, not a table
of accessible hidden values. The distinction between $\pi_D$ and the
indexed factors $Q_{g,j,D}$ is essential for old-sample continuations.

**Proposition 9.2 (native acquisition and continued conditioning).**
For every attained finite native transcript, its source-dependent content
is exactly a consistent indexed cache as above. Conditional on that
transcript, the prepared-array law is (UJB.9005). For every further legal
finite sequence of original-root Reads, including adaptive bounded
stopping and repeats, (UJB.9005), the declared controller and its available
control resources determine the complete continuation law. No whole
label, endpoint or generator is supplied by a bit acquisition.

Proof. Proposition 5.3 classifies every finite operand, not merely the
canonical decoder operands. A constant reply makes no new restriction.
For a nonconstant entry of (UJB.7705), its two possible replies are
distinct, so the reply gives exactly the designated $z_b$, at sample
$j=1+\lfloor(b-1)/15\rfloor$ and local coordinate
$h=1+((b-1)\bmod15)$. Repeated consistent replies impose the same
restriction; inconsistent replies describe a null event. These facts
also apply to absences that are informative entries of the local table;
fixed absences contribute no restriction. Conditional iid edge sampling
then gives the likelihood $\prod_jr_j(g;D)$. Conditioning each sample
on its own rectangle gives the product in (UJB.9005), proving the formula.

For a fixed controller and fixed random seed, every complete attained
transcript fixes its successive operands, stops, outputs and state
updates. All arrays satisfying its cache follow that same transcript;
all others fail a recorded reply. Thus its source likelihood is the
cache indicator. With randomized installation or a measurable independent
seed, the probability of the compatible controller choices is the same
for every array satisfying this indicator. The joint conditional measure
factors into (UJB.9005) and that transcript's conditional controller/seed
measure. Because the array is finite, this argument uses finite sums
and Radon–Nikodym identities; it does not condition on a zero-mass seed
value. The identities hold almost surely for nondiscrete controller data.
Assumption 5.2's independence from the whole hidden source is used here.

For any next operand $w$, let $f_w(y_1,\ldots,y_N)$ be its actual reply
from Proposition 5.3. A positive reply $v$ updates the array law by

$$
\mathsf I_{D'}(y)=
 \frac{\mathbf1_{\{f_w(y)=v\}}\mathsf I_D(y)}
 {\sum_x\mathbf1_{\{f_w(x)=v\}}\mathsf I_D(x)}.
\tag{UJB.9006}
$$

The new cache is the old one with that earned bit added, or the unchanged
cache for a constant/repeated reply. Summing along the actual controller
transitions proves every finite continuation cylinder. Measurable
independent controller mixtures preserve the identity, as does bounded
stopping. Controller state, retained query cursor, available seed,
operands, permission contract and output maps remain explicit inputs to
this pushforward. Two different controllers do not acquire equal output
laws merely because their source interfaces agree. $\square$

### 9.2 Recovering laws, rather than hidden realizations

**Theorem 9.3 (actual-source four-view law correspondence).** Fix $N$,
$\theta$ and the same source access and continuation-controller convention.
On positive histories the following objects determine one another:

1. The conditional prepared-array law $\mathsf I_D$.
2. The conditional law of the current ordered endpoint $F_1(z)$.
3. The conditional law of its oriented material support $S_0$.
4. The conditional law of its terminal-address boundary $B_0$.
5. The conditional law of its labelled generation partial order.
6. The family of conditional transcript laws for all finite original-root
   Read continuations with declared common controllers.

The last object is a family indexed by protocols, including the decoder,
not one experiment's marginal reply law. At a fixed public mask
$m=(m_1,\ldots,m_N)$, the acquired assignments $d$ and $\mathsf I_D$
also recover one another on their realized images. This additional
cache recovery has exactly that fixed-mask scope.

Proof. Proposition 5.3 supplies an injection $z\mapsto F_1(z)$ and its
full-promise inverse, together with the source-to-support, boundary and
labelled-order inverses. We reuse those maps, AA17.2–17.3's local LAB
correspondences, and FARG §9's ordered parsing and path-read separation;
we do not replace local LAB by FARG's global simultaneous substitution.
Pushing a finite probability law through each bijection and its inverse
proves mutual recovery of objects 1–5, including probabilities outside
one source's support if they occur in the promised family.

Proposition 9.2 maps object 1 to object 6. Conversely object 6 includes
Proposition 5.3's fixed $k$-Read decoder, whose complete replies biject
with $z$. Its law therefore recovers object 1. This also proves the
precise minimality statement: a deterministic summary sufficient for
all those continuation laws must distinguish unequal $\mathsf I_D$;
$\mathsf I_D$ attains that behavior/law quotient. No cardinality or
whole-memory optimum is implied.

At a fixed mask, each acquired bit has a Dirac marginal under
$\mathsf I_D$, located at its acquired value. Reading those marginals
recovers every $d_j$, and (UJB.9003)–(UJB.9005) give the inverse map.
If $s_m$ positive assignments occur on this fixed mask, their exact
interface values need and admit $\lceil\log_2s_m\rceil$ fixed-width
naming bits. This names an interface value with the public mask supplied;
it does not pay for retaining the mask or implementing its decoder.
When the mask varies, an already forced bit can be acquired again without
changing the law. The law then does not recover which invocations
occurred, their order, their cost, or which forced bits were explicitly
read. No variable-mask cache inverse follows. $\square$

The generation order in object 5 is the labelled precedence relation,
not the actual chosen serial extension. These law inverses neither
identify the realized endpoint from an unacquired law nor recover the
realized $i$, either injection, the sampled group elements or an actual
preparation chronology. The source may have multiple latent realizations
of the same array. Equality of posterior laws is likewise distinct from
having observed the hidden variable itself.

**Proposition 9.4 (lawful reindexing and actual address costs).**
A public permutation of sample indices, separate public permutations of
the seven left and eight right coordinates, and fixed public bit flips
induce a bijection $T$ of arrays and indexed caches. The actual prior
array law is invariant under $T$, for every $\theta\in[0,1]$, and

$$
\mathsf I_{TD}=T_\#\mathsf I_D.
\tag{UJB.9007}
$$

These are exact law transports with translated operands and evidence;
they are not physical source edits or free navigation. Every bit requested
at local coordinate $h$ of sample $j$ has the actual decoder operand

$$
b(j,h)=15(j-1)+h,\qquad
w_{j,h}=R^{b(j,h)-1}LL,\qquad |w_{j,h}|=b(j,h)+1.
\tag{UJB.9008}
$$

Proof. Sample permutations preserve the conditional iid law. Coordinate
permutations and flips are bijections of each full label alphabet, so
postcomposition preserves the uniform law of the entire injection.
Transform the whole maps and all samples together; independently
redrawing a coordinate would not be this bijection. Transforming the
conditioning rectangles proves (UJB.9007).

For an arbitrary informative operand $q_bu$, transform its slot to the
new $b'$. If the bit is flipped, exchange the first letter of its
nonempty local suffix $u$: $L\leftrightarrow R$, $LL\leftrightarrow RL$,
and $LR\leftrightarrow RR$. The table (UJB.7705) verifies that this
exactly compensates the flip in the reply. Constant spine, slot-root,
long-absent and marker replies remain their known constants. Thus the
translation covers the full native menu. The translated informative
operand has length $b'+|u|$, not its old slot's length. For the standard
bit decoder this is (UJB.9008). Its evaluation on $Ty$ agrees with the
old evaluation on $y$; executing the translated query on the original
array instead requests the correspondingly changed task.

For any actual invocation list $w_1,\ldots,w_t$, charge $t$ invocations,
$\sum_s|w_s|$ literal operand symbols and $\max_s|w_s|$ maximum operand
length. The set of distinct earned bits describes the cache, not that
invocation list's cost. Scanning all $k$ standard operands has the costs
in Proposition 5.3; scanning only a new mask uses the corresponding
subsum of $b+1$, and every repeated invocation still counts.

A source-independent observer can retain $15N$ mask flags and at most
$15N$ acquired values, in addition to its controller description,
counters, addresses and workspace, and update this cache with each
reply. The public graph and
prior descriptions then define finite sums for its predictions. For a
rational prior these sums can in principle be evaluated by exhaustive
finite enumeration and rational arithmetic; the injection enumeration
alone has $2(128)_{72}(256)_{243}$ terms before any array calculation.
For arbitrary real $\theta$ the displayed laws are mathematical maps,
not an effective exact-real oracle. No efficiency follows. The external
preparation remains exactly $75N+4$ native $P/S$ events, besides edge
sampling, selecting/storing both full maps, source storage and handoff.
Observer computation, input, output, controller, seed, navigation,
retention and any physical service costs are separate resource axes.
$\square$

## 10. Equal complete generator posteriors can lose old-sample association

### 10.1 A positive witness on both actual graphs

**Theorem 10.1 (strict indexed association witness).** For any fixed
$N\ge4$ and $\theta\in[0,1]$, read $A$ coordinate 1 and $T$
coordinate 1 in samples $1,\ldots,4$, obtaining $00$ in every sample.
Also read left coordinate 2 in those four samples. Consider its two
ordered patterns

$$
h=(0,0,1,1),\qquad h'=(0,1,0,1).
\tag{UJB.10001}
$$

Both full acquired histories are positive under each actual source.
They have the same old fixed-cut count $(4,0,0,0)$ and the identical
posterior distribution of the complete generator $g=(i,\lambda,\varrho)$.
Nevertheless their joint continuation laws differ when only previously
unread coordinates of the old samples 1 and 2 are queried.

Proof. For each $g$, let $a_g$ and $b_g$ be the probabilities of the
two masks

$$
(A_1,A_2,T_1)=(0,0,0),\qquad (0,1,0),
$$

respectively. Each history's likelihood at this very same $g$ is
$a_g^2b_g^2$. Hence their generator posteriors agree pointwise, not just
after projection to $i$ or to a cut statistic. Denote their common law
by $\eta$. Where it has mass, $a_g,b_g>0$.

Let $V_j=(A_{j,3},\ldots,A_{j,7},T_{j,2},\ldots,T_{j,8})$ be the
remaining twelve bits at sample $j$. Let $u_g$ and $v_g$ be its laws
under those two masks. Given $g$, distinct samples remain independent.
Thus the same continuation event $\{V_1=V_2\}$ has probabilities

$$
P_h=\mathbb E_\eta\|u_g\|_2^2,\qquad
P_{h'}=\mathbb E_\eta\langle u_g,v_g\rangle.
\tag{UJB.10002}
$$

Flipping coordinate 2 in every left label preserves the prior of the
full injections, exchanges $a_g,b_g$ and $u_g,v_g$, and preserves
$a_g^2b_g^2$. Consequently

$$
P_h-P_{h'}=\frac12\mathbb E_\eta\|u_g-v_g\|_2^2.
\tag{UJB.10003}
$$

Here the event compares the same unread reply words in both histories;
it is not a comparison of differently conditioned marginal pages.
To prove strictness and positivity in the actual source, take

$$
a_0=((1,0),(0,0)),\quad a_1=((0,1),(0,0)),\quad
 t_0=((0,0,0),(0,0)).
\tag{UJB.10004}
$$

The two pairs $(a_0,t_0),(a_1,t_0)$ are edges of both $E_i$ by their
actual bilinear formulas. Assign the seven-bit labels of $a_0,a_1$ the
binary integers $0$ and $33$ (most significant coordinate first), and
leave label $32$ unused. Extend to a full injection by assigning the
remaining left vertices, in lexicographic order, the first $70$ unused
integers other than $32$. Assign $t_0$ right label $0$ and the remaining
right vertices the integers $1,\ldots,242$ in lexicographic order.
These are legal complete injections with positive actual probability.

Their first edge belongs to the first mask and their second to the
second mask, so $a_g,b_g>0$. At the all-zero twelve-bit suffix the
first conditional law is positive, while the second is zero: the latter
would require the unused left label $32$. Hence $u_g\ne v_g$ on a
positive-mass generator in each actual source. Repeating these actual
edges in the pattern required by either history proves that history's
positive probability. Equation (UJB.10003) is strictly positive for
each unmixed prior and every mixture, proving all assertions. $\square$

The supplier `posterior_future_policy_universal_sufficiency` assumes
a future-response law indexed by policy and latent state, with no
additional history argument. With $\mathit{Theta}=g$, the $h$-dependent
old-slot factors
$Q_{g,j,D}$ cannot be discarded. Taking $\mathit{Theta}$ to include
the entire prepared array does give a history-independent deterministic
Read function, which is exactly the bridge proved in §9. A posterior
on the shared generator suffices for wholly unread samples, but not
for samples already constrained in different indexed ways.

### 10.2 What the response law recovers

**Proposition 10.2 (recoverable collision law and paid continuation).**
For either history in Theorem 10.1, the joint law of $(V_1,V_2)$
determines the law of the typed endpoint-equality relation on samples
1 and 2 after their labels are completed. It also determines the suffix
collision probabilities in (UJB.10002). Neither law identifies their
realized named endpoints, generator, or realized collision outcome.

Proof. Combine the known three prefix bits per sample with $V_j$.
This recovers their complete observed label pairs. Injectivity gives

$$
a_1=a_2\iff\lambda(a_1)=\lambda(a_2),\qquad
t_1=t_2\iff\varrho(t_1)=\varrho(t_2).
\tag{UJB.10005}
$$

Thus equality of the appropriate complete words is a deterministic
pushforward of the joint response. Under $h$, full edge equality is
exactly $V_1=V_2$; under $h'$ it is impossible because the acquired
left second bits differ. These are statements of collision laws, not
an inversion from equality to named vertices. At an actual execution,
completing the words yields the realized equality test. Before such
execution the probability law supplies no actual outcome. Even after
it, Proposition 3.2's named edge inverse is unavailable: the full maps
are not known, and no group-operation port has been granted.

The acquired past uses coordinates $1,8,2$ in each of four samples:
$12$ invocations, total literal length $326$, maximum $54$.
Completing the twelve remaining coordinates in each of samples 1 and 2
uses $24$ more invocations, length sum $422$, maximum $31$.
All numbers follow by summing (UJB.9008). No observed bit is queried
in this separating continuation. $\square$

For the lexicographic injections in (UJB.10004), the first/second
mask edge counts are
$(447,449)$ in $E_0$ and $(458,438)$ in $E_1$. Their squared suffix-law
differences are respectively $716/200703$ and $367/100302$.
These are positive contributions to (UJB.10003), not evaluations of its
full posterior average. Every such generator has positive prior mass
when its source has positive prior mass; the theorem's strictness
therefore includes $\theta=0$ and $1$ without numerical approximation.

## 11. Separate coordinate pages do not supply their joint continuation

### 11.1 Conditioning each page on its declared evidence

**Definition 11.1 (two separate prediction pages).** Use $N\ge8$.
Page $r\in\{1,2\}$ acquires only left coordinate $r$ in samples
$1,\ldots,4$. Its evidence is the ordered four-bit word $H_r$ and its
summary $S_r$ is the number of zeros in that word. Its declared consumer
is the law of left coordinate $r$ on any selection of wholly unread
sample indices, conditional on $H_r$ alone. Neither page observes the
other coordinate, a right bit, or a paired old-slot continuation.

For each fixed source, a fresh endpoint $a_j$ is uniform on $A$, since
every vertex has degree $27$. Conditional on the complete left
injection, this page has iid Bernoulli parameter
$L_r/72$, where $L_r=|\{a:\lambda(a)_r=0\}|$. A four-bit word with
$n$ zeros has likelihood $(L_r/72)^n(1-L_r/72)^{4-n}$. Thus $S_r$
is sufficient for exactly its declared consumer. This proof integrates
over the unobserved coordinates and right injection; it never
conditions the page's law on evidence the page did not acquire.

**Theorem 11.2 (strict actual cross-coordinate obstruction).** Both
combined histories

$$
\begin{array}{c|cc}
 &H_1&H_2\\\hline
c&(0,0,1,1)&(0,0,1,1)\\
c'&(0,0,1,1)&(1,1,0,0)
\end{array}
\tag{UJB.11001}
$$

have strictly positive actual probability under both sources. Each
has $(S_1,S_2)=(2,2)$, so the two page summaries and their page-specific
predictive laws agree. Nevertheless, conditional on the full combined
evidence in each row, the joint continuation reading left coordinates
1 and 2 in samples $5,\ldots,8$ has different laws. This remains true
for every $\theta\in[0,1]$.

Proof. For a full injection put $n_{uv}=|\{a:\lambda(a)_{1,2}=uv\}|$
and $q_{uv}=n_{uv}/72$. Its actual support is all integer vectors

$$
0\le n_{uv}\le32,\qquad \sum_{uv}n_{uv}=72,
\tag{UJB.11002}
$$

with probability

$$
\omega(n)=\frac{\prod_{uv}\binom{32}{n_{uv}}}{\binom{128}{72}}.
\tag{UJB.11003}
$$

Indeed the image of the uniform full injection is a uniform $72$-subset
of the $128$ labels, partitioned into four buckets of size $32$.
Each possible image has the same $72!$ assignments to the actual
vertices. Consequently (UJB.11003) is the actual injection pushforward,
not an arbitrary categorical prior. Right labels and the index $i$
integrate out because the observed samples have uniform left endpoints.
Given this injection, the paired left-coordinate observations are iid
with parameter $q$.

Write $p(q)=q_{00}^2q_{11}^2$ and $r(q)=q_{01}^2q_{10}^2$.
Their expectations under $\omega$ agree, by flipping the second label
coordinate; call the common positive value $Z$. For the fixed ordered
future word $e=(00,00,11,11)$ the two conditional probabilities differ
by

$$
\Pr(e\mid c)-\Pr(e\mid c')
 =\frac{\mathbb E[p^2]-\mathbb E[pr]}Z
 =\frac{\mathbb E[(p-r)^2]}{2Z}>0.
\tag{UJB.11004}
$$

Strictness holds at the actual bucket vector $(16,16,16,24)$:
all its cells are positive, it satisfies (UJB.11002), and
$16^2\,24^2\ne16^4$. Assign that many distinct labels from the four
buckets to any corresponding partition of the $72$ actual left
vertices and extend to the full right injection. Regular degrees
supply actual edges at each vertex, so each row of (UJB.11001) has
positive probability in either graph. The same full-injection law
works under any source prior, including its endpoints. $\square$

For explicit rational values, let $\mathcal N$ be the $22109$ vectors
in (UJB.11002). Summing the displayed finite hypergeometric weights gives

$$
\begin{aligned}
Z&=\frac{1318541}{333298800},\\
\Pr(e\mid c)&=\frac{59793742630939}{13730035262017536},\\
\Pr(e\mid c')&=\frac{32023312367}{8938825040376},\\
\Pr(e\mid c)-\Pr(e\mid c')
 &=\frac{10605934835227}{13730035262017536}>0.
\end{aligned}
\tag{UJB.11005}
$$

These numbers refer to one ordered future word, with no multinomial
factor. They are independent of $i$ and $\theta$ for the stated reason,
not because the full graphs have been replaced. The same support
contains the positive $125$-point grid
$(16+x,16+y,16+z,24-x-y-z)$, $x,y,z\in\{0,\ldots,4\}$.

### 11.2 Joint evidence and recoverable continuation laws

**Proposition 11.3 (joint-count recovery for the actual paired-coordinate task).**
Let $H=(H_1,H_2)$ range over positive combined evidence of a fixed
public acquisition schedule, and let $K(H)$ be its requested joint
continuation law. A decoder from the two page summaries exists exactly
when

$$
(S_1(H_1),S_2(H_2))=(S_1(H'_1),S_2(H'_2))
 \ \Longrightarrow\ K(H)=K(H')
\tag{UJB.11006}
$$

for all such histories. For the actual paired-coordinate task above,
retaining the four joint counts $n^{\rm past}_{uv}$ repairs the loss:
the full-evidence likelihood is $\prod q_{uv}^{n^{\rm past}_{uv}}$,
and its finite conditional ratios supply every wholly unread
paired-coordinate sequence. For arbitrary partial reads and old slots,
the indexed rectangles of Definition 9.1 supply the sufficient repair.

Proof. A decoder implies constancy on every summary fiber. Conversely
choose the common law on each realized fiber; this is well-defined
exactly under (UJB.11006). This is the existing abstract factorization
principle, not a new factorization theorem. Its actual premise fails
by Theorem 11.2 and is restored for the stated unread consumer by the
joint likelihood just displayed. In the general native task the repair
is (UJB.9003)–(UJB.9006): each new coordinate must be conjoined with the
other restrictions at its actual sample index before counting compatible
edges. Multiplying page marginals does not count those intersections.

The paired past in (UJB.11001) costs eight invocations, length sum $200$,
maximum $48$; the displayed future costs eight, length sum $680$,
maximum $108$. Each coordinate is one actual original-root operand.
Joint counting can be performed after the second half of each actual
pair, retaining its unmatched first reply and sample cursor until then.
The unmatched reply and cursor are additional retained data; their
retention and the joint-count computation are separate resource costs. $\square$

The page summaries are not asserted sufficient for the full combined
conditioning event. Their failure is precisely that upgrade. Joint
counts here do not repair old-slot replay, supply unread coordinates
of partly constrained samples, or inherit §8's $35$-value bound.

## 12. Predictive support closure of complete labels and its partial-read composition

### 12.1 Complete histories have a constant edge likelihood

**Definition 12.1 (version set and support closure).** Fix a public set
$C\subseteq[N]$ of completed samples, whose entire fifteen-bit labels
$y_j$ were actually acquired. Write $D_C=\{y_j:j\in C\}$ as a set
of distinct label pairs. The version set and its closure are

$$
\begin{aligned}
\mathcal V(D_C)&=\{g\in\mathcal G_\theta:D_C\subseteq\mathcal E_g\},\\
\operatorname{cl}_\theta(D_C)
 &=\bigcap_{g\in\mathcal V(D_C)}\mathcal E_g.
\end{aligned}
\tag{UJB.12001}
$$

Only nonempty version sets are admitted. Closure means forced presence
in every still possible labelled edge relation, not a topological
completion or reachability closure on the material tree. It depends
on the positive support of the actual prior; at $\theta=0,1$ only
that source's full injections are in $\mathcal G_\theta$.

**Theorem 12.2 (sharp complete-label predictive closure).** Suppose all
samples outside $C$ are wholly unread, and $U=[N]\setminus C$ is
nonempty. For fixed $C,N,\theta$, the following determine one another
on the positive-history image:

- $\operatorname{cl}_\theta(D_C)$;
- the law $P_C$ of the next full label pair at any designated $u\in U$;
- the indexed joint law of all the still unread samples $Y_U$.

More precisely,

$$
\begin{aligned}
\pi(g\mid y_C)&=
 \frac{\pi_\theta(g)\mathbf1_{\{g\in\mathcal V(D_C)\}}}
 {\pi_\theta(\mathcal V(D_C))},\\
P_C(y)&=\frac1M\Pr(g\in\mathcal G_\theta:
                           y\in\mathcal E_g\mid y_C),\\
\operatorname{cl}_\theta(D_C)&=\{y:P_C(y)=1/M\}.
\end{aligned}
\tag{UJB.12002}
$$

Thus equality of closures is exactly equality of these unread-sample
laws, not merely a sufficient condition. No observed label multiplicity,
chronological order or original-slot assignment is recovered by this
equivalence.

Proof. At each $g$ the likelihood of the particular ordered completed
history is $M^{-|C|}\mathbf1_{\{D_C\subseteq\mathcal E_g\}}$.
The constant cancels in conditioning, proving the first line. Repeats
have the same factor $1/M$ per occurrence, which is why their
multiplicity disappears only after conditioning; they are not removed
from the original sample law.

Every compatible $g$ contains the intersection in (UJB.12001), and
$D_C$ is a subset of that intersection. Hence

$$
\mathcal V(D_C)
 =\mathcal V(\operatorname{cl}_\theta(D_C)).
\tag{UJB.12003}
$$

Closure is consequently extensive, monotone and idempotent on this
positive domain. It reconstructs the version set and hence the complete
conditional generator law using the fixed public prior. That law gives
$\sum_g\pi(g\mid y_C)\prod_{u\in U}p_g(y_u)$, proving recovery of
the full unread law, whose marginal gives $P_C$.

Conversely each $p_g(y)$ is either $0$ or exactly $1/M$, and every
$g$ in the version set retains strictly positive conditional mass.
Its average reaches $1/M$ exactly when every such $g$ contains $y$.
This proves the last line of (UJB.12002), and completes both inverse
directions. The equal nonzero edge mass is crucial: a general weighted
latent mixture does not recover its version set from a saturated
one-step law in this way. $\square$

If $C$ is empty, this proof still applies, with the public prior and
its initial closure. If $U$ is empty there is no next unread sample and
the unread-array law is the singleton empty-product law. It determines
closure on a chosen history domain exactly when closure is constant
on that domain. This is the precise exception to the inverse, not an
implicit permission to create a fresh sample. On the full completed
history domain it is not constant: repeat a label edge $y$ in every
sample, or repeat $y'$ with a different left label. Both are positive;
there is a full injection realizing $y'$ while omitting $y$'s left
label, so $y$ belongs to the first closure and not the second.

### 12.2 Partially acquired samples keep their own likelihoods

**Theorem 12.3 (weighted partial composition and effective closure).**
Partition $[N]=C\sqcup P\sqcup U$. Samples in $C$ are complete;
each sample in $P$ has a specified nonempty proper mask and acquired
assignment; every sample in $U$ has an empty mask. Fix these index
sets, the entire indexed partial cache $D_P$, and $N,\theta$.
For a positive combined history set

$$
\begin{aligned}
W_P(g)&=\prod_{j\in P}r_j(g;D_P),\\
\mathcal V_P(D_C)&=\{g\in\mathcal V(D_C):W_P(g)>0\},\\
C_P(D_C)&=\bigcap_{g\in\mathcal V_P(D_C)}\mathcal E_g.
\end{aligned}
\tag{UJB.12004}
$$

If $U\ne\varnothing$, the effective closure $C_P(D_C)$, the next
full-label law on a designated $u\in U$, and the joint law of all
$Y_U$ determine one another, **with the indexed partial cache held
fixed**. The closure and that cache also determine all continuations
on partly acquired samples and their joint law with $Y_U$.
The unweighted complete-history closure together with $D_P$ is
another sufficient representation, but is not asserted recoverable
from the next-label law.

Proof. Direct conditioning of the same actual source gives

$$
\pi(g\mid y_C,D_P)
 \ \propto\ \pi_\theta(g)
       \mathbf1_{\{D_C\subseteq\mathcal E_g\}}W_P(g).
\tag{UJB.12005}
$$

It has positive support exactly $\mathcal V_P(D_C)$, which is nonempty
by positivity of the history. As in (UJB.12003),

$$
\mathcal V_P(D_C)
 =\{g\in\mathcal G_\theta:C_P(D_C)\subseteq\mathcal E_g,
                                      \ W_P(g)>0\}.
\tag{UJB.12006}
$$

Indeed $D_C\subseteq C_P(D_C)$ proves right-to-left inclusion;
left-to-right follows from the definition of the intersection.
Thus $C_P$ and the fixed actual $W_P$ reconstruct both the support
and the weights in (UJB.12005). The still unread sample law is again
an average of products of $p_g$. Its next-label marginal is bounded
by $1/M$, with saturation set exactly $C_P$. The proof of Theorem
12.2 therefore gives both inverse directions verbatim for this
weighted, fixed-partial-cache domain.

For $j\in P$ use $Q_{g,j,D_P}$ in (UJB.9004), not $p_g$.
Their product with the unread $p_g$ factors, mixed under (UJB.12005),
gives the joint law of all unfinished and unread samples. Already
read bits at those partial indices have their fixed values, so rereads
and completions are also supplied. The complete-history closure first
recovers $\mathcal V(D_C)$ by (UJB.12003); attaching $W_P$ supplies
(UJB.12005), proving the other sufficient representation. $\square$

This composition has three necessary scope qualifications. First,
allowing $D_P$ to vary without retaining it loses its index association
and weights; Theorem 10.1 demonstrates that even the whole generator
posterior then fails for old-slot completion. Second, these closure
inverses consume at least one wholly unread sample, with its entire
label law available as a mathematical object. When $U$ is empty the
unread consumer is constant, even if partly acquired samples remain;
no inverse from that constant is claimed. Third, $C_P$ or the
unread law does not recover the assigned completed labels at each old
index in $C$. To extend to the full native menu, keep those indexed
completed labels as well; replay reads return them deterministically.
Equations (UJB.12005)–(UJB.12006) and those indexed values then recover
$\mathsf I_D$. Conversely $\mathsf I_D$ at the fixed total mask
recovers the whole cache by Theorem 9.3. All masks and values arise
by the paid native process, rather than by a free latent-state input.

For dynamic use, partial acquisition adds its actual rectangle
restriction and reweights by (UJB.9006). On completing a sample,
move its index from $P$ to $C$, delete its former partial likelihood
factor and replace it by the exact complete-label constraint with
factor $1/M$. The deleted factor must not also be retained as an
independent observation. Equivalently retain the entire indexed cache
and recompute (UJB.9004); it gives the same law. Moving a wholly
unread index into $P$ is likewise an actual new Read, not an external
resampling step. This specifies legal updates through every sample
completion boundary while preserving the old-slot restrictions.

## 13. Transporting future readouts does not transport past evidence for free

### 13.1 Actual full-label evidence and its coarsening

**Theorem 13.2 (full-label evidence versus its missing first bit).**
For any $N\ge4$ and $\theta\in[0,1]$, completely read sample 1.
Write its left label as $(B,u)$ with $u\in\{0,1\}^6$, and its right
label as $v\in\{0,1\}^8$. The full past is $H=(B,u,v)$ and its
coarsening is $C=(u,v)$. The future response is $X=\lambda(a_2)_1$,
a previously unread bit of the second prepared sample. Every full
past has positive probability, and for each fixed $u,v$,

$$
\begin{aligned}
\Pr(X=0\mid B=0,u,v)&=\frac{575}{1143},\\
\Pr(X=0\mid B=1,u,v)&=\frac{568}{1143},\\
\Pr(X=0\mid u,v)&=\frac12.
\end{aligned}
\tag{UJB.13003}
$$

This fails the fiber condition for the legal first-bit future readout
at every one of these coarsened-past fibers, even with $i$ known.

Proof. We use the following finite conditional-law identities and the
image-factorization principle cited in §14.1 within this actual-source
calculation.

Let $H$ be a finite acquired history, $X$ a named finite future response
under a declared protocol, and $K(h)=\mathcal L(X\mid H=h)$ on its
positive domain in the actual source. Let $W$ be a public future-readout
map, and let $C=c(H)$ coarsen the past. At each fixed full past $h$,

$$
\mathcal L(W(X)\mid H=h)=W_\#K(h).
\tag{UJB.13001}
$$

The history-specific transported law is recoverable from $c(h)$ exactly
when $W_\#K$ is constant on every positive $c$-fiber. Conditioning on
the coarsened past instead always gives the mixture

$$
\mathcal L(W(X)\mid C=c)
 =\sum_{h:c(h)=c}\Pr(H=h\mid C=c)\,W_\#K(h).
\tag{UJB.13002}
$$

Both formulas hold for a fixed public stochastic readout channel as
well, by summing its rows. They do not license a new physical readout
port: the named response must be an actual native protocol or declared
postprocessing of one.

Sum the finite joint law over each readout fiber for (UJB.13001),
and then over the histories in the evidence fiber for (UJB.13002).
Constancy is sufficient by assigning its common law to each fiber,
and necessary because a decoder has one output per coarsened value.
This reuses abstract image factorization; the substantive test is which
fibers the actual source permits and which target laws vary there.
A conditional mean of different laws in (UJB.13002) does not provide
the realized $h$-specific law.
For the stated first-bit task, $W$ is the identity and $c$ forgets $B$.
It remains to compute the actual conditional laws on each coarse fiber.

Fix any actual first edge. Its two assigned labels are independent
uniform elements of their full alphabets, so
$\Pr_i(H=(B,u,v))=1/(128\cdot256)>0$ for both sources. Conditional
on this edge and its complete labels, the rest of the full left
injection is a uniform injection avoiding its one used label. The
next left endpoint is uniform on $72$ vertices. It equals the first
one with probability $1/72$, and otherwise its label is uniform among
the $127$ remaining labels. Therefore, if $B=0$,

$$
\Pr(X=0\mid H)
 =\frac1{72}+\frac{71}{72}\frac{63}{127}
 =\frac12+\frac7{2286}=\frac{575}{1143}.
\tag{UJB.13004}
$$

If $B=1$ the value is $(71/72)(64/127)=568/1143$.
The argument is unchanged by the right label: after the chosen first
edge, it imposes no restriction on the unassigned left labels. More
formally, for any fixed first edge the conditional left-injection
extension has exactly this same distribution, so mixing over possible
first edges or source indices preserves the result.

Flipping the first coordinate of the whole left injection is a
probability-preserving bijection fixing $u,v$ and exchanging the two
values of $B$. Thus $B$ is conditionally fair given $C$, and averaging
the first two probabilities gives $1/2$. This is the actual mixture
(UJB.13002), not the full-past pushforward (UJB.13001). The two
history-specific probabilities differ by $7/1143>0$. $\square$

### 13.2 Recoverable refinement and acquisition costs

**Corollary 13.3 (the additional relation for the named combined task).**
At a fixed public coarsened value $(u,v)$, retaining the coarsened record
and its realized full-past-specific first-bit prediction law requires
and admits two distinct supplemental names. The missing relation can
be carried by the earned bit $B$, or by that two-valued law name. It
is one fixed-width naming bit for this task with $(u,v)$ supplied,
not one bit of total observer memory or a bound for the full native menu.

Proof. Theorem 13.2 supplies two distinct law values in the same positive
fiber, proving the two-name lower bound. Retaining $B$ attains it by
(UJB.13003). More generally, to pass from coarse evidence $C$ to a
specified refinement $B$, one needs its joint relation with the target:

$$
\Pr(X=x\mid C=c,B=b)
 =\frac{\Pr(X=x,B=b\mid C=c)}{\Pr(B=b\mid C=c)}
\tag{UJB.13005}
$$

where the denominator is positive. Separate laws of $B\mid C$ and
$X\mid C$ omit that relation. Here (UJB.13003) makes $B$ conditionally
fair and $X$ conditionally fair but not conditionally independent.
An indexed acquired interface supplies this joint relation for each
actually retained refinement; forgetting the refinement changes the
prediction task. $\square$

The full past costs fifteen actual invocations, operand lengths
$2,\ldots,16$, sum $135$, maximum $16$. Acquiring only its coarsening
costs fourteen, lengths $3,\ldots,16$, sum $133$; acquiring the full
past and later forgetting $B$ still costs fifteen. The next bit is
$w_{2,1}=R^{15}LL$, length $17$, costing one more invocation.
These are three different acquisition histories even where their
retained coarse records coincide. Restricting a future label readout
to this bit at the fixed full past is ordinary lawful postprocessing;
replacing the full past by its fourteen-bit coarsening is a different
conditioning event. Neither operation identifies the hidden endpoint.

## 14. Supplier correspondences and recovery domains

### 14.1 Scoped mathematical suppliers

The group/edge adapter, all three $w$ coordinates in both sources,
full-injection law, native preparation and complete operand
classification are those of §§3–5. FARG §9 supplies ordered term
serialization and all-path separation; AA17.2–17.3 supply the material
support, boundary and local-generation partial-order inverses used by
Proposition 5.3. FARG's global simultaneous substitution and AA17's
local $P/S$ generation are distinct operations. Theorem 9.3 uses the
bijections instantiated in Proposition 5.3 to transport probability laws.

For image factorization and separation of unequal target laws, the
repository suppliers are
`CausalStateFactorization.causal_state_factorization` and
`PredictiveStateUniversalMinimality.predictive_state_universal_minimality`.
For latent-state sufficiency, the supplier
`PosteriorFuturePolicySufficiency.posterior_future_policy_universal_sufficiency`
assumes a future PMF indexed by policy and latent state without an
extra history argument. With latent state $g$, the old-slot factors
$Q_{g,j,D}$ retain that extra dependence; with latent state the entire
prepared array, the Read response is history-independent, as in §9.

[Shalizi and Crutchfield, *Computational Mechanics: Pattern and Prediction,
Structure and Simplicity*, arXiv:cond-mat/9907176v2](https://arxiv.org/html/cond-mat/9907176v2),
Definition 5, equation (16), Lemma 7 and Theorem 2, supply conditional
future-law equivalence and its refinement/minimality principle under
their stationary-process and almost-sure entropy hypotheses. The
finite-law factorization in §§9, 11 and 13 uses equality of the declared
conditional continuation laws; it does not identify entropy with a
finite fixed-width cache size or substitute an entire-past domain for
the indexed old-slot access domain.

[Aldous, *Exchangeability and Related Topics*, §2, printed pp. 9–10
(PDF pp. 11–12), equations (2.1)–(2.2)](https://www.stat.berkeley.edu/~aldous/Papers/me22.pdf),
Lecture Notes in Mathematics 1117, pp. 1–198, gives the two-stage
construction that first selects a distribution and then samples iid
from it, with finite-dimensional laws equal to mixtures of products.
Here the distribution is $p_g$ from (UJB.9002), with $g$ sampled by the
full-injection prior (UJB.9001) and the original independent edge
samples. This construction is a premise of the actual source, rather
than a converse inferred from finite exchangeability. The observation
domain contains only the $N$ prepared samples. The saturation inverse
in §12 uses the additional equal nonzero edge mass $1/M$ and positive
support conditions proved there.

### 14.2 Domains of the recovery correspondences

For fixed $N,\theta$, the conditional law of the indexed constraints
on one prepared array, together with the declared controller resources,
determines all stationary original-root Read continuation laws. Its
correspondence with endpoint, material-space, boundary and labelled
generation-order laws is Theorem 9.3. The additional inverse to the
acquired assignments holds on each fixed public mask. Invocation order,
repeats and cost are not determined by that law when masks vary.

For wholly unread labels, §12's smaller support-closure representation
is equivalent to the unread-sample law when at least one unread sample
remains, with the partial cache held fixed in Theorem 12.3. The indexed
partial cache and the assigned completed labels are retained for
continuations on old slots. If there is no unread sample, the unread
law is the constant empty-product law, and its closure inverse holds
exactly on domains with constant closure. Combining coordinate pages
or refining past evidence uses the joint relations in §§11 and 13.

These correspondences are between conditional laws on the stated
finite source and native operation domains. A law is distinct from a
realized endpoint, an inaccessible latent realization, or a chosen
serial generation history. Fixed-width names for law values are
distinct from total observer storage and computation. Source
acquisition, conditional-law computation and actual realization have
the separate resource costs stated in §§9–13. No equivalence with
additional source ports, evolving source operations or physical
spacetime is assumed.

## 追加锚（本行以下为增补区）

## 15. The two literal sources as geometric types with finite capacities

**Definition 15.1 (typed capacities of the actual sources).** Retain
(UJB.7502), including every $w_3,z$, and the full-injection prior
(UJB.9001). A type is an equal-neighborhood class within one endpoint
sort. Its capacity is its number of literal endpoints. The type relation
has an incidence exactly when its two classes are adjacent; each pair of
literal endpoints above an incidence still has edge multiplicity one.
Write its left and right type sets as $L_i,R_i$, its incidence indicator
as $I_i$, and its capacities as $c_i,d_i$.

**Theorem 15.2 (geometric reduction of both literal sources).** For $G_0$,
$R_0$ is the affine point set $F^3$, and $L_0$ is the set of its affine
lines in the four directions

$$
K_{[v]}=F(v_2^2,-v_1v_2,v_1^2),\qquad [v]\in\mathbb P^1(F),\quad F=\mathbb F_3.
\tag{UJB.15001}
$$

Incidence is point-on-line. Every line type has capacity $2$ and every
point type capacity $9$. There are $36$ line types, $27$ point types,
$108$ incidences, and one connected component. For $G_1$, identify
$F^2$ with the field $F[\iota]$, $\iota^2=-1$. Both type sets are
$F[\iota]$; incidence is equality of the type values. A left type has
capacity $8$, a right type capacity $27$. Thus $G_1$ is exactly nine
disjoint $K_{8,27}$ components, retaining all $72$ and $243$ endpoints.

Proof. The two rows of $B_0(v,-)$ have rank two for $v\ne0$ and kernel
(UJB.15001). Its solution set for $s$ is one affine line with that
kernel. The four projective choices of $v$ give four different kernels:
representatives $(1,0),(0,1),(1,1),(1,2)$ give vectors
$(0,0,1),(1,0,0),(1,2,1),(1,1,1)$. Equal affine solution lines must
have the same kernel, so their $v$ values are scalar multiples; the
corresponding $s$ values have that same multiplier. Consequently the
left twins are exactly $(v,s)$ and $(-v,-s)$. For a right endpoint
$(w,z)$, adjacency ignores $z$. Conversely the choices $v=(1,0),(0,1)$
recover $(w_1,w_2)$ and $(w_2,w_3)$ from their adjacent left endpoints,
so different $w$ values have different neighborhoods. Right twins are
therefore exactly the nine $z$ values at fixed $w$. A line has three
points, and every point has one incident line of each direction. This
proves the class and incidence counts. The displayed directions span
$F^3$; moving along their affine lines connects any two points, proving
connectedness of the quotient and hence of its blow-up.

For $G_1$, the polynomial $X^2+1$ has no root in $F$. Multiplication
of $v_1+\iota v_2$ and $w_1+\iota w_2$ gives exactly the two entries of
$B_1$. Its edge equation is therefore

$$
w_1+\iota w_2=(s_1+\iota s_2)/(v_1+\iota v_2).
\tag{UJB.15002}
$$

Each value on the right has eight left representatives, one for each
nonzero $v$. Each value on the left has three $w_3$ and nine $z$
representatives. Their neighborhoods coincide precisely at equal values,
and distinct values have disjoint neighborhoods. This proves the entire
literal decomposition, including the free coordinates rather than
removing them. $\square$

**Theorem 15.3 (actual-source injective capacity expansion).** Let $H$ be
any finite typed bipartite graph with distinguished left vertices $X$
and right vertices $Y$. Required parallel incidences may be merged for
this count; no absent cross-edge is forbidden. Its number $J_i(H)$ of
type-preserving injective embeddings into the literal $G_i$ is

$$
J_i(H)=\sum_{\alpha:X\to L_i,\ \beta:Y\to R_i}
 \left(\prod_{xy\in E(H)} I_i(\alpha x,\beta y)\right)
 \prod_{\ell\in L_i}(c_i)_{|\alpha^{-1}\ell|}
 \prod_{r\in R_i}(d_i)_{|\beta^{-1}r|}.
\tag{UJB.15003}
$$

Here $(a)_0=1$ and $(a)_b=0$ for $b>a$; the capacities are the constants
in Theorem 15.2, not independently fitted weights. The formula includes
isolated vertices and is zero if $|X|>72$ or $|Y|>243$.

Proof. Project an injective embedding to its geometric types. Within
each type its distinguished vertices must choose different literal
endpoints, in exactly the indicated falling-factorial number of ways.
Choices in different types are disjoint and independent. Every required
incidence then holds for every lift precisely when its type incidence
holds, by Theorem 15.2. This partitions all embeddings without omission
or automorphism division. It also proves the asserted zero cases.
The established twin-reduction method of Grohe–Thurley,
[*Counting Homomorphisms and Partition Functions*, §6.1, Lemma 6.1,
(6.1)–(6.3)](https://arxiv.org/abs/1104.0185v3), sums positive vertex
weights over identical rows of a nonnegative symmetric matrix. Here
one may place the typed incidence matrix in the off-diagonal blocks
of a symmetric matrix. Its ordinary homomorphism reduction would use
$c_i^b,d_i^b$. Injectivity instead requires the displayed capacities;
the counting distinction is the classical one in Lovász–Szegedy,
[*Limits of dense graph sequences*, §§2.1, 2.4](https://arxiv.org/abs/math/0408173v2).
The source-specific geometric types and their simultaneous capacity
constraints are what will be consumed below. $\square$

## 16. Exact indexed evidence without complete hidden injections

**Definition 16.1 (sample partitions and allowed labels).** For the same
public $N\ge4$, let $p,q$ range over partitions of the original $[N]$.
They assert the exact equality classes of its left and right endpoints,
respectively. Construct $H_{p,q}$ with one distinguished vertex per
block and an incidence from $p(j)$ to $q(j)$ for every original index
$j$. Repeated incidences impose a single adjacency constraint, but the
sample denominator below retains all $N$ occurrences. Put $r=|p|$,
$s=|q|$. Discard pairs with $r>72$ or $s>243$.

For a left block $B\in p$, let $A_B(D)\subseteq\mathcal L$ consist of
all full left words satisfying every acquired left-coordinate restriction
at indices in $B$. Define right-block sets in $\mathcal R$ in the same
way. Conflicting restrictions give an empty set. With no restrictions
the set is the whole appropriate alphabet. These are intersections of
restrictions at the same proposed endpoint, not products of separate
coordinate-page probabilities.

For an alphabet enumerated as $\ell_1,\ldots,\ell_Q$, and $t$
distinguished blocks with allowed sets $A_b$, define integer arrays
$f_v(S)$, $S\subseteq[t]$, by

$$
\begin{aligned}
f_0(S)&=\mathbf1_{\{S=\varnothing\}},\\
f_v(S)&=f_{v-1}(S)+
 \sum_{b\in S:\ell_v\in A_b}f_{v-1}(S\setminus\{b\}),\quad 1\le v\le Q.
\end{aligned}
\tag{UJB.16001}
$$

Write $L_p(D)=f_{128}([r])$ for the left restrictions, and
$R_q(D)=f_{256}([s])$ for the right restrictions.

**Theorem 16.2 (source-capacity evaluator for every indexed cache).**
For every assignment of masks and values in (UJB.9003), including null
ones, define

$$
\begin{aligned}
Z_i^*(D)&=\frac1{1944^N}
 \sum_{p,q}\frac{J_i(H_{p,q})L_p(D)R_q(D)}{(128)_{|p|}(256)_{|q|}},\\
Z^*(D)&=(1-\theta)Z_0^*(D)+\theta Z_1^*(D).
\end{aligned}
\tag{UJB.16002}
$$

Then $Z^*(D)=Z(D)$, the existing evidence normalizer in (UJB.9004),
for both literal source branches and every $\theta\in[0,1]$. Equations
(UJB.15003), (UJB.16001), (UJB.16002), with finite loops over partitions,
type assignments and subsets, are a terminating exact evaluator. No
individual complete hidden injection is enumerated. This supplies a
constructive source reduction for the existing normalizer, rather than
asserting finite evaluability or abstract sufficiency for the first time.

Proof. Fix a source and a particular tuple of sampled literal edges.
Its exact endpoint equality partitions are unique. Conversely an
injective embedding of $H_{p,q}$ supplies exactly one such ordered tuple.
There are $J_i(H_{p,q})$ tuples, each of mass $1944^{-N}$; unused
cross-edges do not have to be absent.

For fixed literal endpoints belonging to the $r$ attained left blocks,
a compatible injective assignment of their labels is counted by
$L_p(D)$. Indeed $f_v(S)$ counts injective assignments of the blocks
in $S$ into the first $v$ alphabet elements. The last label is either
unused, or assigned to exactly one block $b$ that permits it. These
are the disjoint alternatives in (UJB.16001). Thus the recurrence
accounts also for unused labels, including their possible later use.
Every such partial assignment has exactly

$$
(128-r)_{72-r}\,(256-s)_{243-s}
\tag{UJB.16003}
$$

extensions to the two entire once-shared maps, after the analogous
right-label choice. Dividing by their original prior denominator gives

$$
\frac{(128-r)_{72-r}(256-s)_{243-s}}
 {(128)_{72}(256)_{243}}=
 \frac1{(128)_r(256)_s}.
\tag{UJB.16004}
$$

All unobserved literal vertices remain in these extension factors.
Within each source their different geometric capacities are already
included in $J_i$, so no source-dependent multiplicative factor can
be dropped or replaced by a new prior. For example, when all attained
vertices occupy one left and one right type, the lift factors are
$(2)_r(9)_s$ in $G_0$ and $(8)_r(27)_s$ in $G_1$. If an entire
label allocation to geometric types is specified, its internal full-map
multiplicities would instead be $(2!)^{36}(9!)^{27}$ and
$(8!)^9(27!)^9$; (UJB.15003) and (UJB.16003) partition those same
literal assignments, rather than treating these constants as equal.
Summing the tuple probabilities and averaging the two original source
weights proves (UJB.16002). $\square$

**Theorem 16.3 (finite arithmetic account and exact input).** Let
$\mathcal P_N(a)$ be the partitions of $[N]$ into at most $a$ blocks.
For $p\in\mathcal P_N(72)$, $q\in\mathcal P_N(243)$, put
$r=|p|$, $s=|q|$. One direct implementation of Theorem 16.2 requires
at most

$$
\begin{aligned}
\mathcal W(N)=1000+N+
\sum_{p,q}\big[&128r2^{r-1}+256s2^{s-1}+30(N+1)\\
 &+10(N+r+s+1)(36^r27^s+9^{r+s})\big]
\end{aligned}
\tag{UJB.16005}
$$

exact rational additions, subtractions, multiplications and divisions
on the counting and probability values. This is a finite upper bound for all masks, not a polynomial bound or a
bit-operation bound. For rational $\theta$ all outputs are exact
rationals. For arbitrary real $\theta$, (UJB.16002) can be returned as
the symbolic affine expression with rational coefficients; every
positive conditional probability below is a ratio of such expressions.
Exact numerical evaluation and null-event decisions require an input
representation supporting the relevant arithmetic and zero/order tests,
for example a rational or a specified real algebraic number. An
unrepresented arbitrary real is not an effective exact-real input.

Proof. Enumerate partitions by restricted-growth words and type maps
in lexicographic order. There are $36^r27^s$ type-map pairs for $G_0$
and $9^{r+s}$ for $G_1$. For each pair initialize the type occupancies,
scan the $r+s$ distinguished vertices, and multiply their remaining
capacities before incrementing the occupancy. If it is exhausted the
contribution is zero. Check the at most $N$ required incidences and add
the surviving product. Initialization, counters, this product and its
addition fit the factor $10(N+r+s+1)$, including occupancy-count
updates. No literal-vertex permutation is needed; combinatorial cursors and bit-set operations are separate from
this arithmetic count.

For (UJB.16001), at each of $Q$ labels copy the preceding subset array
and add one term for each allowed pair $(S,b)$ with $b\in S$.
There are at most $Qt2^{t-1}$ such additions. Membership in $A_b$
can be prepared by scanning its original cache restrictions and testing
the alphabet words. This uses finite Boolean work, at most
$128\cdot7N+256\cdot8N$ bit comparisons per partition pair; it
requires no rational arithmetic. The rational products and denominators
in (UJB.16002) fit the remaining $30(N+1)$ per pair. Falling-factorial
tables, source constants, mixture and $1944^N$ fit $1000+N$. These choices give the stated conservative
bound even when zero terms are not pruned. Subset storage, partition
and type-map enumeration, growing integer bit lengths, input/output
and controller storage are separate resources. $\square$

## 17. Continued native use and the fixed-partial-cache inverse

**Theorem 17.1 (exact indexed continuation and update).** Keep the full
indexed cache $D$, public $N,\theta$, and the controller and permissions
of Assumption 5.2. On $Z^*(D)>0$, Theorem 16.2 evaluates every next
original-root Read response and every finite conditional array cylinder.
It covers arbitrary coordinate masks, restrictions added to old samples,
partial-to-complete transitions, completed-slot replay, constants,
repeats and null proposed responses. With the declared controller it
therefore supplies the entire stationary Read continuation interface,
including bounded adaptive continuation, without a new source port.

More explicitly, let $D\wedge E$ mean conjoining new indexed coordinate
restrictions, retaining each coordinate once. A contradiction has
normalizer zero. Then

$$
\Pr(E\mid D)=\frac{Z^*(D\wedge E)}{Z^*(D)}.
\tag{UJB.17001}
$$

For a complete candidate array $y\in\mathcal Y^N$, let $D_y$ fix all
its coordinates. Its conditional mass is

$$
\mathsf I_D(y)=
 \mathbf1_{\{y\text{ satisfies }D\}}\frac{Z^*(D_y)}{Z^*(D)}.
\tag{UJB.17002}
$$

This is the same $\mathsf I_D$ as (UJB.9005), not a posterior on types
or on the source alone.

Proof. Theorem 16.2 is the probability of the actual cache event.
Intersections of those events are exactly indexed conjunction, giving
(UJB.17001); fixing the whole array gives (UJB.17002). Thus both ways
of evaluating cylinders agree by finite additivity.

For every finite operand, use Proposition 5.3's exhaustive classification:
a spine/marker/constant slot suffix has its fixed reply, while an
informative entry of (UJB.7705) returns a one-to-one function of one
specified array bit. A new bit uses the two ratios in (UJB.17001), whose
sum is one, and appends its actual value at that index. A known bit,
including any bit of a completed sample, returns its recorded value
with probability one; it is never resampled from an updated generator.
A fixed reply leaves the cache unchanged. A contrary repeat, wrong
constant, or zero-normalizer new reply is a null event and has no
conditional posterior. Informative absences use their bit restriction;
constant absences do not. Null initial evidence likewise receives only
its zero normalizer, not an arbitrary conditional law.

When a partly acquired index becomes complete, its block restrictions
in Definition 16.1 are simply their full conjunction. In the generator
notation, this replaces its old $r_j(g;D)$ by
$M^{-1}\mathbf1_{\{y_j\in\mathcal E_g\}}$; it does not multiply
that factor by the old partial likelihood a second time. A former
unread index acquires its own restriction in exactly the same manner.
The original indices in $p,q$ and their allowed-label intersections
are retained throughout, including when two different samples have
identical masks or the same observed labels. Every term still refers
to the same two full maps via (UJB.16003), with no independent map
redraw at a bit, endpoint or completion boundary.

For a fixed bounded deterministic adaptive controller, each attained
reply fixes the next operand and update. Induction down its reply tree
multiplies (UJB.17001); the ratios telescope to the final cache
normalizer divided by the starting one. Constants and repeats remain
invocations even though their ratios are one. A bound of $b$ invocations
gives at most $2^{b+1}-1$ nodes, so this construction uses at most that
many evaluations bounded by $\mathcal W(N)$, plus finite controller and
address work. Arbitrarily long individual operands are classified by
their actual finite words, not by restricting the menu to the standard
decoder addresses.

For the general measurable independent controller of Assumption 5.2,
let $K_y$ be its continuation transcript measure when replies are the
deterministic replies of the fixed array $y$, with its available
controller/seed measure as in Proposition 9.2. The exact continuation
measure is the finite combination

$$
\sum_{y\in\mathcal Y^N}\mathsf I_D(y)K_y.
\tag{UJB.17003}
$$

Thus at most $2^{15N}$ evaluations provide all source coefficients for
every such controller, even with bounded adaptive stopping and general
output spaces. This statement retains the supplied controller measure;
it does not assume that integration over an arbitrary measurable seed
has an effective numerical presentation. A finite explicit controller
tree with rational transition weights, and rational $\theta$, gives a
terminating rational evaluation of its whole finite transcript law.
More general effective numerical claims require a corresponding exact
representation of the controller measure. Formula (UJB.17003) itself
holds for all the controllers in §9. $\square$

**Theorem 17.2 (capacity-evaluated closure with its exact inverse domain).**
Partition $[N]=C\sqcup P\sqcup U$ as in Theorem 12.3. Fix $N,\theta$,
the sets of indices and the entire indexed partial cache $D_P$. Retain
the completed values at their original indices. If $U\ne\varnothing$,
choose an actual $u\in U$. For $y\in\mathcal Y$, let $D[u=y]$ add
its full label at that index. Then

$$
C_P(D_C)=
 \{y:1944\,Z^*(D[u=y])=Z^*(D)\}.
\tag{UJB.17004}
$$

Consequently the effective closure, the next full-label law and the
joint unread law have exactly the mutual recovery domain of Theorem
12.3. The closure together with $D_P$ and the indexed completed labels
supplies the full native interface. No such inverse from the unread
law is asserted when $U$ is empty, nor when the partial cache varies
without being retained.

Proof. By (UJB.17001), the left probability in (UJB.17004), divided
by $Z^*(D)$, is the actual next full-label law on the designated unread
sample. The saturation identity and the fixed-prior, fixed-partial-cache
inverse are exactly (UJB.12004)–(UJB.12006). We reuse that theorem:
its positive support reconstructs the version set, its fixed $W_P$
reconstructs the weights, and its indexed $Q_{g,j,D_P}$ reconstruct
old partial samples. Indexed completed values give deterministic replay.
Theorem 17.1 now evaluates this same interface constructively. At most
$128\cdot256$ additional normalizers compute (UJB.17004); this is
computation on descriptions and acquired data, not acquisition of those
unread values. If $U=\varnothing$, the unread law is the one-point empty
product even when partial samples remain. Theorem 12.2's nonconstant
closures on completed histories show why it has no general inverse;
Theorem 17.1 still evaluates the actual remaining old-slot Reads.

For each of these full indexed laws, Theorem 9.3 already transports
the conditional law to the ordered endpoint, oriented material support,
terminal boundary and endpoint-labelled generation order, and back via
the entire family of Read protocols. The endpoint-labelled causal order
and all successful histories are the correspondences supplied by
`NativeEndpointCausalOrder.result`, `NativeEndpointEventIdeals.all_histories`
and `NativePromiseCausalBoundary.result`; an actual serial extension is
not recovered. No new causal/serial correspondence is needed here.
The generic factorization and policy-sufficiency suppliers of §14.1
likewise do not remove the old-slot factors. In particular Theorems
10.1, 11.2 and 13.2 remain obstructions to discarding index association,
joint coordinate restrictions or retained past evidence. $\square$

## 18. Actual capacity thresholds, forced relations and mixed predictions

**Theorem 18.1 (sharp common-neighbor capacities and feasible witnesses).**
For unordered distinct literal left endpoints, the common-right-neighbor
histograms are

$$
\begin{array}{c|rrr}
 &0&9&27\\\hline
G_0&1872&648&36\\
G_1&2304&0&252
\end{array}
\tag{UJB.18001}
$$

Three distinct left endpoints have at most $9$ common right neighbors
in $G_0$ and at most $27$ in $G_1$, both bounds attained. For the
complete typed bipartite graph on three distinguished left and $m$
distinguished right vertices, the exact counts at the relevant thresholds
are

$$
\begin{aligned}
J_0(K_{3,9})&=27(8)_3(9)_9>0,&J_0(K_{3,10})&=0,\\
J_1(K_{3,m})&=9(8)_3(27)_m\quad(1\le m\le27),&
J_1(K_{3,28})&=0,\\
J_1(K_{3,10})&=92575499208192000.
\end{aligned}
\tag{UJB.18002}
$$

Thus ordinary type coarsening with unrestricted multiplicative weights
loses feasibility on the actual $G_0$: it allows a map of $K_{3,10}$
to a single incident line and point, whereas no injective literal
realization exists. The attainable $K_{3,9}$ makes the threshold sharp.

Proof. In $G_0$, two different line types either are disjoint or meet
at one point, while two literal vertices in the same line type have
all $27$ right neighbors in common. There are $36\binom22=36$
same-type pairs. At each of the $27$ points the four incident line
types give $\binom42$ pairs with four literal lifts each, giving $648$.
The remaining $\binom{72}2-36-648=1872$ pairs are disjoint. In $G_1$
there are $9\binom82=252$ pairs with $27$ common neighbors and
$\binom{72}2-252=2304$ disjoint pairs.

Three distinct left vertices cannot all occupy a $G_0$ line type of
capacity two. If they have common neighbors, at least two distinct lines
meet at their unique common affine point. All common right endpoints
are the nine $z$ values there. At each point the eight incident literal
left vertices allow $(8)_3$ ordered triples, and no triple can be
counted at another point. This proves the first line of (UJB.18002).
For $G_1$ a triple with common neighbors must lie in one of its nine
components; its right choices are exactly the component's $27$ literal
endpoints. This proves the remaining counts.

At $w=0$, all eight endpoints $(v,0)$ are adjacent to every $(0,z)$
in both sources. Any three distinct such left endpoints and all nine
$z$ values give the first positive witness. In $G_1$, allowing all
$w_3$ as well gives its $27$-neighbor witness. A single type incidence
with positive ordinary weights gives a positive homomorphism term
$2^3 9^{10}$ in $G_0$, but the correct lift term $(2)_3(9)_{10}$ is
zero. All other capacity assignments are zero by the proved geometric
bound. This is a failure of the uncapacitated replacement, not of
Theorem 15.3. $\square$

**Theorem 18.2 (an acquired relation forces a new relation in both sources).**
Fix $N\ge7$, four different left label words $a,b,c,d$ and two different
right label words $u,v$. Completely acquire seven distinct sample indices
with the ordered edge labels

$$
au,\ av,\ bu,\ bv,\ cu,\ cv,\ du.
\tag{UJB.18003}
$$

For every $\theta\in[0,1]$ this history is positive. Its support closure
contains the previously unacquired pair $dv$. With $N\ge8$ and all
other samples unread, its full-label probability at any designated
unread sample is exactly $1/1944$. The same forced-support conclusion
holds after any additional positive indexed partial evidence on other
indices. The use of three distinct common left labels is sharp for
this family: the five-edge evidence $au,av,bu,bv,du$ need not force
$dv$ when $1-\theta>0$.

Proof. Two different affine points of $G_0$ lie on at most one line
of the allowed directions: an affine line through two points is unique.
Their right neighborhoods therefore have at most two common literal
left endpoints. Three distinct common left endpoints force the two
right endpoints to have the same $w$, hence to be twins. In $G_1$,
even one common left endpoint forces two right endpoints into the same
component and hence the same right type. Thus (UJB.18003) forces $u,v$
to be right twins in every compatible generator of either source.
The observed $du$ then forces $dv$. For positivity take $w=0$, two
different $z$ values, and four different $v\ne0$ with $s=0$.
All eight required pairs exist in both sources. Assign their prescribed
distinct labels and extend both injections using (UJB.16003). The
seven specified independent samples then have positive probability.
Theorems 12.2 and 17.2 give the saturated unread prediction. Restricting
to any smaller nonempty version set by further partial evidence cannot
remove a forced edge.

For sharpness in $G_0$, take $u=((0,0,0),0)$,
$v=((0,0,1),0)$ and left endpoints
$a=((1,0),0)$, $b=((2,0),0)$, $d=((0,1),0)$.
Both $a,b$ meet $u,v$, and $d$ meets $u$, but
$B_0((0,1),(0,0,1))=(0,1)\ne0$, so $dv$ is absent. These literal
vertices admit the prescribed distinct labels and full extensions.
This generator retains positive posterior mass whenever $1-\theta>0$,
so $dv$ is not then forced by the five edges. For that comparison's
unread prediction one needs $N\ge6$; it grants no extra sample when
all indices have already been used. $\square$

**Theorem 18.3 (exact mixed predictions consumed by the evaluator).**
Let $a\ne b$ and $u\ne v$ be prescribed full labels of the appropriate
sorts. At $N\ge4$, complete three designated samples as
$au,av,bu$, leave a designated fourth wholly unread, and leave every
other sample unread. This history is positive for both sources, and
for every $\theta\in[0,1]$ the fourth sample has

$$
\Pr(Y_4=bv\mid au,av,bu)
 =\frac{37+54\theta}{91\cdot1944}.
\tag{UJB.18004}
$$

With three distinct left words $a,b,c$, two distinct right words $u,v$,
$N\ge6$ and five complete designated samples $au,av,bu,bv,cu$,
the analogous designated unread sample has

$$
\Pr(Y_6=cv\mid au,av,bu,bv,cu)
 =\frac{28+63\theta}{1944(37+54\theta)}.
\tag{UJB.18005}
$$

Both are exact joint-mask predictions of Theorems 16.2 and 17.1;
the newly completed sample is conditioned at its own index.

Proof. For a typed three-edge path $P_4$, choose its middle edge,
then a different right neighbor in $26$ ways and a different left
neighbor in seven ways. Thus

$$
J_0(P_4)=J_1(P_4)=1944\cdot26\cdot7=353808.
\tag{UJB.18006}
$$

For $K_{2,2}$, sum $(h)_2$ over ordered distinct left pairs having
$h$ common right neighbors. Equation (UJB.18001) gives
$J_0(K_{2,2})=143856$ and $J_1(K_{2,2})=353808$.
At three completed samples their likelihoods are
$353808/[1944^3(128)_2(256)_2]$ under either source, independent of
which prescribed distinct labels were used. At four prescribed labels
forming the square, the numerator becomes the respective $K_{2,2}$
count and the sample denominator becomes $1944^4$. The unchanged
label denominator cancels in (UJB.17001), proving (UJB.18004).

For the five-edge graph in the second assertion, choose the ordered
right pair and ordered common left pair $a,b$, then choose $c$ from
the six remaining left neighbors of $u$. Its count is
$6J_i(K_{2,2})$. Completing $cv$ instead counts $K_{3,2}$.
In $G_0$ a right pair can have three common left endpoints only if
it lies in the same point type, giving $27(9)_2(8)_3=653184$;
in $G_1$ its count is $9(27)_2(8)_3=2122848$. Hence the two
five-edge counts are $(863136,2122848)$ and the six-edge counts are
$(653184,2122848)$. Their positive mixed likelihood ratio, with its
additional factor $1944^{-1}$, is (UJB.18005). Here the common label
denominator is $(128)_3(256)_2$. The explicit $w=0$ configurations
used above give positive realizations of every required pattern in
both sources. No unspecified maximum-likelihood embedding or separate
source optimum has been substituted for the shared mixture. $\square$

**Theorem 18.4 (contingent source exclusion and the remaining resource axes).**
Fix three different left label words and ten different right label
words. At $N\ge31$, completely acquire the thirty prescribed incidences
of their $K_{3,10}$ at distinct sample indices, with the other indices
unread. This history is positive exactly when $\theta>0$, with
probability

$$
\frac{\theta\,92575499208192000}
 {1944^{30}(128)_3(256)_{10}}.
\tag{UJB.18007}
$$

It forces source $1$ on its positive domain. Nevertheless neither this
capacity witness nor the evaluator gives a bounded always-correct
source classifier. The arithmetic account (UJB.16005) changes neither
the native invocation tariff nor the address tariff of (UJB.9008).

Proof. The counts and positive realizations are (UJB.18002), and the
full-map extension division is (UJB.16004). Each distinct original
sample contributes $1944^{-1}$, proving (UJB.18007) and its exact
null domain at $\theta=0$. A wholly unread continuation requires the
additional original index stated in the theorem. At $N=30$ the same
completed evidence and source exclusion remain meaningful, but its
unread-array law is the empty product and carries no closure inverse.
The common positive all-zero events of §5 still obstruct every bounded
always-correct classifier, so positive exclusion events do not supply
a sure acquisition protocol.

Each actual coordinate acquisition still uses its original native
operand, and every repeat, constant and absence still counts as an
invocation. In particular a newly acquired local bit $h$ at sample $j$
has standard operand length $15(j-1)+h+1$, while general operands
retain their literal lengths. Computing normalizers supplies
probabilities, not the realized unread bits. The retained indexed
cache, controllers, cursors, operands, output laws and subset/type
workspace are separate resources from the finite arithmetic count.
The external source preparation and its once-shared random maps remain
the premises of §§5 and 9. None of the displayed law calculations
constructs native randomness, a hidden-realization inverse, a selected
serial history, or a physical-spacetime correspondence. $\square$

## 追加锚（本行以下为增补区）

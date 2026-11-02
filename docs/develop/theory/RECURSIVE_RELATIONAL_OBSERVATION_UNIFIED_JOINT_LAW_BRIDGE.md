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

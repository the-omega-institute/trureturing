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

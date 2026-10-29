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

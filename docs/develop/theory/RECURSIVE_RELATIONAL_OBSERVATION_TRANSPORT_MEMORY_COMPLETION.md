# 递归关系观察：运输、任务记忆与完成化

本卷以共同来源上的实际观察、合法续接及表示运输连接空间、边界、时间和记忆。观察者包括完整已获档案 $C$、来源索引、内外记录、校准、参考、时钟与权限；任务摘要只承担明确指定的后续实验。数学逆映射不自动是可执行操作，几何修复也不自动是可反复使用的合法通道。

全文给出普通数学论证；引用既有 Lean 声明时只使用所列陈述及不可变提交范围，不把下述综合推导称作新增 Lean 核验或原创性结论。相位与单值实角、原始档案与工作记忆、全时间精确行为与固定视界近似、实际实现与相容完成分别保留各自的前提。

阅读顺序为：第1章运输及锚点，第2章任务记忆与共同端口，第3章合法胶合与经典共同来源修复，第4章切面和历史流，第5章紧观察、近似策略与完成化。[联合关系与时钟卷](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md)和[有效分辨率卷](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md)使用本卷的表示与续接接口。式号 TM、AP 保留为跨卷唯一的公式地址。

## 1. 运输、锚定相位与任意纤维

### 1.1 有限图上的相位运输与任务范围

固定非空有限连通无向多重图，允许平行边与自环。每条无向边选一条正向代表 $e:o(e)\to t(e)$，另有形式逆 $\bar e$。正向代表集合记 $E$。每边有相位 $u_e\in U(1)$，并约定 $u_{\bar e}=u_e^{-1}$。路径运输为按遍历顺序的复数乘积。逆边在此承担几何比较，不自动是允许的物理逆操作。

节点换相位 $s_v\in U(1)$ 将边变为

$$
u'_e=s_{t(e)}u_es_{o(e)}^{-1}.
$$

所有相位均在同一个共同模型、同一边身份和同一校准约定中比较。图、端口、可用路径及两路振幅的相干合成能力是额外固定的数据；仅由边相位不生成这些权限或全部观察者档案。

固定根 $o$ 和生成树 $T$。令 $r_v$ 为树中从 $o$ 到 $v$ 的唯一路径，$P_v=u(r_v)$。规范化后每条边的相位是

$$
h_e=P_{t(e)}^{-1}u_eP_{o(e)}.
\tag{TM.1}
$$

每条树边 $h_e=1$。非树边 $e$ 对应基于 $o$ 的闭路 $r_{o(e)}e r_{t(e)}^{-1}$，其运输就是 $h_e$。所有这些式子保留实际平行边，未把它们先聚合成一个矩阵元。

### 1.2 有限图上的相位运输与换基

完整观察者保留全部已获档案、同源关系、端口权限、参考、实际时钟及校准；工作表示不替代这些数据。生成树边相位能够全部消去，要求同时运输端口参考；已固定的多个端口校准会留下开放路径不变量。

设 $G=(V,E)$ 是有限有向多重图，保留具名平行边与自环。每条边 $e:s\to t$ 带相位

$$
u_e\in U(1)=\{z\in\mathbb C:|z|=1\}.
$$

为了检验相容性，可以加入形式逆边 $\bar e:t\to s$，定义 $u_{\bar e}=u_e^{-1}$。形式逆不授予逆向执行权限，也不意味着实际时间或费用取负。实际已存在的反向边若是另一条具名边，其标签并不自动等于这个形式逆。

路径 $P=e_1\cdots e_n$ 的相位为

$$
u(P)=\prod_{k=1}^n u_{e_k},
$$

空路径相位为一，形式逆路径按反序遍历逆边。

**命题 1.1（端点运输、闭路与同端点比较）。** 采用列状态运输约定。局部换基 $\psi'_v=g_v\psi_v$，其中 $g_v\in U(1)$，要求边运输同时变为

$$
u'_e=g_tu_eg_s^{-1}.
\tag{AP.1}
$$

则对任何形式路径 $P:s\to t$，

$$
u'(P)=g_tu(P)g_s^{-1}.
\tag{AP.2}
$$

因而所有形式闭走法的相位保持；对同端点路径 $P,Q:s\to t$，

$$
u'(P)\overline{u'(Q)}
=u(P)\overline{u(Q)}
=u(P\bar Q).
\tag{AP.3}
$$

**证明。** 对一步运输，将 $\psi_t=u_e\psi_s$ 两端分别换基，得到
$\psi'_t=g_tu_eg_s^{-1}\psi'_s$，所以式（AP.1）正是同一运输的坐标表达。形式逆也满足相同公式，因为
$(g_tu_eg_s^{-1})^{-1}=g_su_e^{-1}g_t^{-1}$。沿路径相乘，中间各顶点的 $g_v^{-1}g_v$ 逐个抵消，给式（AP.2）。闭走法首尾相同，而 $U(1)$ 交换，所以端点共轭抵消。对于 $P,Q$，两个端点因子相同且模为一，因此相乘后抵消；$u(\bar Q)=u(Q)^{-1}=\overline{u(Q)}$ 给最后一式。证毕。

实际实验若只允许正向执行 $P,Q$，式（AP.3）仍可用于比较二者；它不要求实验能够执行 $\bar Q$。若端点不同，则须先声明把它们接到同一读取接口的实际运输或参考，不能直接将两份振幅相加。

### 1.3 生成森林消去与无固定参考时的完整分类

在底层无向多重图中选生成森林 $T$，每个连通分量选根 $r$。令 $P_v$ 是树中从根到 $v$ 的唯一形式路径，置

$$
h_v=u(P_v),\qquad g_v=h_v^{-1}.
\tag{AP.4}
$$

**命题 1.2（树归一与基本闭路）。** 式（AP.4）的换基使全部树边相位为一。对非树边 $e:s\to t$，换基后的相位恰为

$$
u'_e=u(P_s\,e\,\overline{P_t}).
\tag{AP.5}
$$

固定每个根处 $g_r=1$ 后，使树边全部为一的换基唯一。

**证明。** 对任意树边 $e:s\to t$，两条根路径在树内消去往返后相差该有向边，因此 $h_t=u_eh_s$，不论边方向是否背离根。于是
$u'_e=h_t^{-1}u_eh_s=1$。对非树边，同一计算给
$u'_e=h_t^{-1}u_eh_s$；交换性使它等于根到 $s$、经过 $e$、再沿树返回根的闭走法相位。若另一换基也使树边为一，则每条树边要求 $g_t=u_e^{-1}g_s$；从根值逐边递推，唯一决定所有顶点值。证毕。

**命题 1.3（平凡闭路、顶点势与相位场分类）。** 下列条件等价：

1. 存在换基使全部边相位为一；
2. 全部形式闭走法相位为一；
3. 相对于任一固定生成森林，全部基本闭走法相位为一。

更一般地，两份相位场 $u,\widetilde u$ 换基等价，当且仅当它们在全部形式闭走法上的相位相同。

**证明。** 第一项推出第二项，来自A卷命题1.1；第二项直接包含第三项。由A卷命题1.2，第三项使树边和全部非树边在同一换基后均为一，故推出第一项。对于两份相位场，取比值场 $v_e=\widetilde u_e/u_e$。两份闭路相位相同等价于比值场闭路相位全部为一，于是存在顶点函数 $g$ 使 $v_e=g_tg_s^{-1}$，即 $\widetilde u_e=g_tu_eg_s^{-1}$。这里可将使 $v$ 归一的换基取逆，获得所需方向。证毕。

若 $n=|V|$、$m=|E|$、连通分量数为 $c$，非树边数为

$$
b_1=m-n+c.
$$

树归一后，每个非树边可以独立赋予任意单位相位，没有额外约束。因此

$$
U(1)^E/U(1)^V\cong U(1)^{b_1}.
\tag{AP.6}
$$

此处商掉的是顶点换基作用；每分量的共同常相位作用平凡。自环和平行边均计入非树边数。空图与孤立点按空乘积处理。式（AP.6）分类声明的相位场，不声称从任意强度数据已经取得这些坐标。

这复用的是既有生成树机制：RRO 定理67.1使用 $\mathbb F_2$，定理77.1使用正实增益。路径构造与基本环检验可以迁移，它们专属的计数、概率及正性结论不能迁移。ZeroLoopPotentialEquivalence 的交换加法群可取 $U(1)$ 的加法包装，不需要假装存在全局单值的实对数。

**例 1.4（单位相位平凡不等于所选实角和为零）。** 有向三角形每条边相位均为 $e^{2\pi i/3}$，则闭环相位为一，可以由A卷命题1.3消去全部边相位。但三个指定实角之和为 $2\pi$，不存在实顶点势使每条边的实差分都精确等于所指定的 $2\pi/3$：沿圈实差分望远镜为零，与 $2\pi$ 矛盾。单位相位的等价关系包含模 $2\pi$，不能把它静默改成实角的精确等式。证毕。

### 1.4 完整基本闭环读数确定相位运输到节点换基

**命题 1.5。** 设 $r=|E|-|V|+1$。相位运输在节点 $U(1)$ 换基下的等价类，与 $r$ 个非树边相位 $(h_e)_{e\notin T}\in U(1)^r$ 一一对应。

**证明。** 将 A卷第1.3节 的生成森林分类取为这里的非空连通图，连通分量数为一，根为 $o$，树路径为 $r_v$，相位场为 $u_e$。于是 $b_1=|E|-|V|+1=r$；式（AP.4）中的 $h_v$ 对应这里的 $P_v$，式（AP.5）的非树边坐标对应式（TM.1）的 $h_e$。该分类的双向构造和独立实现给出所述双射；这里仍保留平行边、自环及同一具名边身份。证毕。

该命题分类的是已给图上的相位运输。它不恢复未知图的嵌入或纽结型，也不恢复边的未知幅度、观察者旧档案或未声明的实验权限。图为树时 $r=0$，所有此类相位运输在上述换基下等价，仍不表示实际端口校准可以被任意抛弃。

### 1.5 固定外部参考后的开放路径不变量

设 $R\subseteq V$ 是已固定相位坐标的参考顶点，只允许

$$
g_r=1\qquad(r\in R).
\tag{AP.7}
$$

参考是否固定、其坐标与关联是否已获，均属于完整档案和操作合同。以下先讨论已声明的精确固定参考。

**命题 1.6（锚定换基的完整判据）。** 两相位场 $u,\widetilde u$ 在满足式（AP.7）的换基下等价，当且仅当比值场 $v=\widetilde u/u$ 满足：

1. 每条形式闭走法 $C$ 有 $v(C)=1$；
2. 同一连通分量内任意两个参考顶点之间的形式路径 $P:r\to r'$ 有 $v(P)=1$。

**证明。** 若 $\widetilde u_e=g_tu_eg_s^{-1}$，则 $v(P)=g_{r'}g_r^{-1}$；闭路及参考间路径分别给一，证明必要性。反之，在含参考的分量选参考根 $r_0$，沿路径定义 $h_v=v(P_v)$。闭路条件使该值与路径选择无关。参考间条件给每个参考顶点 $h_r=1$。接一条边得 $v_e=h_th_s^{-1}$，令 $g_v=h_v$ 即得所需换基并固定全部参考。不含参考的分量任选根，作相同构造，无须锚定条件。证毕。

**例 1.7（无环仍有已校准开放相位）。** 取两个顶点、一条边

$$
s\xrightarrow{e^{i\phi}}t.
$$

图没有环，但若 $s,t$ 的相位校准都固定，则允许的换基在两点均为一，边相位不能改变。输入为一，输出再与同端口的固定参考一相加，读数为

$$
|1+e^{i\phi}|^2.
$$

$\phi=0,\pi$ 分别给四与零。这是平方模读数，不在未声明归一化时称为概率。“树上没有环不变量”不等于“树上的完整校准实验没有相位信息”。若把实际外部参考关系也纳入整体，该比较本身可形成一条闭合关系链；不能为获得局部规范自由度而删除旧参考。证毕。

### 1.6 连通图中固定参考的完整独立不变量

本节回答更精确的后续问题：在基本环相位之外，参考根到其余参考点的树路径相位，是否正好构成全部独立附加不变量？

**定义 1.8（锚定相位场及坐标）。** 设 $G=(V,E)$ 为有限连通有向多重图，允许自环和平行边，连通性指底层无向图。设非空参考集 $R\subseteq V$，记

$$
n=|V|\ge1,\qquad m=|E|,\qquad k=|R|\ge1,\qquad
b=m-n+1.
$$

选参考根 $r_0\in R$ 和底层生成树 $T$。对每个顶点 $v$，令 $P_v$ 为从 $r_0$ 到 $v$ 的唯一树中形式路径。对相位场 $u$，定义

$$
h_v(u)=u(P_v),\qquad h_{r_0}(u)=1.
$$

对每条非树边 $e:s\to t$，定义基本环相位

$$
\ell_e(u)=h_s(u)\,u_e\,h_t(u)^{-1}.
$$

对每个 $r\in R\setminus\{r_0\}$，定义参考间树路径相位

$$
a_r(u)=h_r(u).
$$

记锚定换基群为

$$
\mathcal G_R=\{g:V\to U(1):g_r=1\text{ 对所有 }r\in R\}.
$$

**定理 1.9（完整性与独立实现）。** 映射

$$
u\longmapsto
\bigl((\ell_e(u))_{e\notin T},(a_r(u))_{r\in R\setminus\{r_0\}}\bigr)
\tag{AP.21}
$$

在 $\mathcal G_R$ 作用下不变，并诱导一个紧交换群同构

$$
\boxed{
U(1)^E/\mathcal G_R
\cong U(1)^{\,b+k-1}
=U(1)^{\,m-n+k}.
}
\tag{AP.22}
$$

具体地，两份相位场具有相同的 $b$ 个基本环相位及 $k-1$ 个参考间树路径相位，当且仅当它们相差一个固定全部参考的顶点换基；这些 $b+k-1$ 个单位相位可任意独立指定，不存在额外关系。

**证明。**

第一步，不变性。由A卷命题1.1及 $g_{r_0}=1$，

$$
h_v(g\cdot u)=g_vh_v(u).
$$

代入基本环定义，所有 $g$ 因子抵消。参考顶点上 $g_r=1$，所以 $a_r$ 也保持。

第二步，完整性。假设 $u,\widetilde u$ 的式（AP.21）相同。取

$$
g_v=\widetilde h_vh_v^{-1}.
$$

根处及其余参考处均有 $g_r=1$。把树边的 $\ell_e$ 约定为一，则每条边都有

$$
u_e=h_t\ell_eh_s^{-1},\qquad
\widetilde u_e=\widetilde h_t\ell_e\widetilde h_s^{-1}.
$$

因此 $\widetilde u_e=g_tu_eg_s^{-1}$，得到锚定等价。反向由第一步已经证明。

第三步，任意独立实现。任给

$$
(\lambda_e)_{e\notin T}\in U(1)^b,\qquad
(\alpha_r)_{r\in R\setminus\{r_0\}}\in U(1)^{k-1},
$$

设 $h_{r_0}=1$、$h_r=\alpha_r$ 对其余参考成立；在非参考顶点上可任选 $h_v$，例如全部取一。令 $\lambda_e=1$ 对树边成立，并定义全部实际边

$$
u_e=h_t\lambda_eh_s^{-1}.
\tag{AP.23}
$$

沿树根路径相乘，$\lambda_e=1$，故望远镜给 $u(P_v)=h_v$，包括反向遍历树边的情形。由基本环定义，非树边的 $\ell_e$ 正好等于 $\lambda_e$，参考树路径相位正好等于 $\alpha_r$。因此每一组指定不变量都被某个相位场实现，且各坐标可以独立变化。

第四步，群与拓扑。所有坐标都由有限乘积、取逆构成，故式（AP.21）是连续群同态。第三步选择所有非参考 $h_v=1$ 给连续乘法截面，第二步说明它的纤维恰为锚定规范轨道。因此诱导的商映射与该截面诱导的逆互为连续群同构，得到式（AP.22）。也可用紧到 Hausdorff 的连续双射结论。证毕。

**推论 1.10（完整参数分解与计数）。** 在同一树和参考选择下，

$$
U(1)^E
\cong
U(1)^{V\setminus R}
\times U(1)^{E\setminus T}
\times U(1)^{R\setminus\{r_0\}}.
\tag{AP.24}
$$

三个因子分别记录非参考顶点的树运输 $h_v$、基本环相位和参考间树路径相位。锚定换基只逐坐标乘第一个因子，其余两因子保持；作用自由。

**证明。** 前向取所有 $h_v,\ell_e$，参考部分与非参考部分分开。反向用式（AP.23）重建；沿树的望远镜说明两方向互逆。若一个锚定换基保持全部边相位，则每条边两端 $g_t=g_s$，连通性使 $g$ 常值，而参考处固定一，故 $g$ 恒为一。证毕。

这里独立不变量的数量为

$$
b+k-1=(m-n+1)+(k-1)=m-n+k.
$$

若进一步把全部相位限制在 $N$ 次单位根群 $\mu_N$，其中 $N\ge2$，同样构造不离开该群。因此共有 $N^m$ 份相位场、$N^{n-k}$ 个锚定换基，且

$$
\#(\mu_N^E/\mathcal G_R)=N^{m-n+k}.
\tag{AP.25}
$$

证明来自式（AP.24），也可由自由作用逐轨道计数。至少需要 $m-n+k$ 个取值于 $\mu_N$ 的无损坐标：若只用 $q<m-n+k$ 个此类坐标，其值域至多 $N^q$，不能单射承载 $N^{m-n+k}$ 个等价类。对于连续 $U(1)$，上述数量是乘积群及拓扑坐标的数量，不声称排除了任意不连续的集合编码。

**例 1.11（退化边界与最小非平凡组合）。**

- 只有一个参考点时，$k=1$，只剩 $b$ 个环相位，与A卷命题1.3一致。
- 图是树时，$b=0$，仍有 $k-1$ 个参考间开放路径相位；两个固定端点的一条边正是A卷例1.7。
- 全部顶点都是参考时，$k=n$，锚定换基只有恒等，独立不变量数为 $m$，没有删除任何边相位信息。
- 只有一个顶点时，$n=k=1$，每条自环都是非树边，$b=m$，结论仍适用。
- 两个参考顶点 $s,t$ 之间有两条平行边，取第一条为树边。给定树路径相位 $\alpha\in U(1)$ 和基本环相位 $\lambda\in U(1)$，式（AP.23）给 $u_1=\alpha,u_2=\alpha\lambda$。两者任意独立；闭环比值 $u_2/u_1=\lambda$ 不能代替锚定开放相位 $\alpha$，反之亦然。

以上均为A卷定理1.9构造的直接实例，不增加物理可执行性或额外概率解释。

**命题 1.12（坐标的相对边界解释）。** 对每条实际有向边使用一个整数生成元，令 $C_1=\mathbb Z^E$，$C_0=\mathbb Z^V$，边界算子为

$$
\partial e=t(e)-s(e).
$$

考虑整数链群

$$
Z_1(G,R)=\{z\in C_1:\partial z\text{ 支撑在 }R\}.
$$

则各基本闭链
$C_e=P_s+e-P_t$（$e\notin T$）
与各参考根路径 $P_r$（$r\in R\setminus\{r_0\}$）构成 $Z_1(G,R)$ 的一组整数基。因此其秩为 $b+k-1$；不变量（AP.21）恰为相位场在这些基链上的乘法取值。

**证明。** 若 $z\in Z_1(G,R)$，把其边界写成

$$
\partial z=\sum_{r\in R\setminus\{r_0\}}c_r(r-r_0).
$$

这可行且唯一，因为任何边链边界的顶点系数总和为零。于是
$z'=z-\sum_{r\ne r_0}c_rP_r$ 具有零边界。对每个非树边 $e$，从 $z'$ 减去其 $e$ 系数乘 $C_e$，可消去全部非树边，并保持边界为零。剩余链支撑在树中；若非零，取其非零支撑森林的叶，边界在该叶非零，与零边界矛盾。因此剩余链为零，证明张成。

若这些链的整数线性组合为零，先取边界，$r-r_0$ 的独立性使所有参考路径系数为零；再比较各非树边系数，各基本闭链只在自己的非树边上有系数一，所以全部基本闭链系数也为零。故它们是一组整数基。相位沿链的乘法取值按边的整数幂定义，恰给式（AP.21）。证毕。

这提供了一个不依赖图的空间嵌入的“相对边界”表述：闭链与连接固定参考的链同属于边界只落在参考集合的关系。它仍不是空间纽结结论。

**适用边界。** 独立性针对本文声明的完整相位赋值空间 $U(1)^E$，其中各具名边相位可任意赋值。若另有源模型、可执行器件、额外路径等式、对称性、归一化或校准规律限制相位场，允许的不变量只能取该模型的像，可能存在附加关系；不能把A卷定理1.9的满射结论原样移过去。例如若额外要求所有形式闭路相位为一，则全部基本环坐标被固定为一，不再独立可变。

A卷定理1.9分类的是相位场相对于固定参考换基的等价类，不是强度读数的自动可识别性。树路径可能包含只在数学检验中使用的形式逆；取得这些相位仍需要实际允许的相干实验、参考、记录访问和精度条件。A卷第2.11节给其中一类恢复接口，A卷例2.13说明单份强度可能不足。

### 1.7 生成树归一化：保留真正的闭环作用

闭环运输作用先确定给定初态的可达分支轨道，再由全部允许未来实验确定最小任务记忆。下面的可逆执行合同下，该记忆为左陪集作用集合 $G/K$；$K$ 不必正规。

令 $\Gamma=(V,E)$ 是有限、非空、连通无向多重图，允许平行边和自环。$E$ 计数无向边；每条边有两个形式方向 $e,\bar e$，即使是自环也保留两个方向。记 $o(e),t(e)$ 为起点、终点。

每个顶点有纤维 $E_v$，每条有向边有双射

$$
T_e:E_{o(e)}\to E_{t(e)},
\qquad T_{\bar e}=T_e^{-1}.
$$

纤维不要求有限。选根 $o$ 和生成树 $T$，记唯一树路径 $p_v:o\to v$，并设

$$
F=E_o,
\qquad A_v=T_{p_v}:F\to E_v,
\qquad A_o=\mathrm{id}.
$$

对 $x\in E_v$，用 $s=A_v^{-1}x$ 作统一纤维坐标。每条边的归一化运输为

$$
h_e=A_{t(e)}^{-1}T_eA_{o(e)}\in\operatorname{Sym}(F).
$$

树边满足 $h_e=\mathrm{id}$，反向满足 $h_{\bar e}=h_e^{-1}$。对按从左到右执行的路径 $\gamma=e_1\cdots e_n:v\to w$，运输次序为 $T_\gamma=T_{e_n}\cdots T_{e_1}$，于是

$$
\boxed{
T_\gamma=A_w(h_{e_n}\cdots h_{e_1})A_v^{-1}.
}
$$

证明是将 $T_e=A_{t(e)}h_eA_{o(e)}^{-1}$ 逐项代入，相邻的 $A^{-1}A$ 消去。树边归一化为恒等，是因为树路径接上树边后与对应根路径只相差立即往返，而逆向运输相互抵消。

每条非树边 $e:v\to w$ 对应根闭环 $p_v\,e\,\bar p_w$，其运输恰为 $h_e$。定义

$$
G=\langle h_e:e\text{ 为选定方向的非树边}\rangle
\le\operatorname{Sym}(F).
$$

所有根闭环运输组成的群正是 $G$：一个方向由路径分解式成立；另一个方向把每个生成元及其逆实现为相应根闭环，再串接实现任意乘积。

非树边数为

$$
\beta_1=|E|-|V|+1.
$$

因此，所有闭环运输平凡，当且仅当这 $\beta_1$ 个生成运输全为恒等。更换生成树改变生成元和局部坐标；若连根纤维坐标也更换，则闭环作用相应共轭。它不改变实际路径的响应关系。

非交换情形必须保留有序复合，不能只保存各生成元的出现次数。形式逆边目前只保证数学比较中的可逆性；是否可以实际执行逆边，另由A卷第2.1节的权限条件承担。

## 2. 任务记忆、共同端口与加权续接

### 2.1 指定未来实验的商，才是最小任务记忆

本节增加以下实际条件。

1. 每个有向边及其逆边均真正允许执行；合法性只依赖当前顶点。
2. 当前顶点已知并可作为外部给定的类型信息；图、运输及读数已标定。
3. 初始根分支 $s_0\in F$ 已知。把它写成符号不等于免费取得它。
4. 指定每个顶点的任务读数 $o_v:E_v\to Y_v$，要求在任意有限合法延续后精确恢复读数。
5. 该下界针对封闭的确定性预测实现：外部输入仅为已知当前顶点及下一条边或指定查询，不能免费重读完整档案、外部时钟或传感器来补回摘要未保存的区别。凡影响更新、合法性或解码的观察器内部状态，都必须包含在摘要状态中；不能只比较显示值却暗中使用未计入的控制状态、历史指针、时钟、缓存或随机种子。若允许额外外部输入，须重新定义配置、操作接口及记忆与输入的计数范围，不能直接沿用本节下界。
6. 逐边合法性、标签或费用若依赖分支或历史，须把相关依赖纳入配置与指定输出。仅沿将来已知路径求和的边费用，不等于要求恢复过去累计费用；后一任务必须另外计入。

令

$$
f_v=o_v\circ A_v,
\qquad O=G\cdot s_0.
$$

每个顶点上的可达归一化分支恰好都是 $O$。任意 $g s_0$ 可以先在根执行对应闭环，再沿树到目标顶点得到；反向包含关系由A卷第1.7节的路径分解式给出。

在 $O$ 上定义

$$
\boxed{
s\sim t
\iff
\forall g\in G\ \forall w\in V,
\quad f_w(gs)=f_w(gt).
}
$$

这个关系恰是从任意已知当前顶点出发的未来不可区分关系。一条实际延续的归一化运输属于 $G$，给出一个方向。另一个方向从当前顶点沿树回根、执行实现 $g$ 的根闭环，再沿树到 $w$，即可实际读取 $f_w(gs)$。这一步真正使用了逆向执行权限。

设

$$
M=O/{\sim}.
$$

若 $s\sim t$，则对任意 $h\in G$，由在定义中将 $g$ 换成 $gh$ 得 $hs\sim ht$。因此边更新

$$
\overline U_e([s])=[h_es]
$$

及当前读数

$$
\overline f_v([s])=f_v(s)
$$

都良定义。实现状态可以写成 $(v,[s])$，边执行为

$$
(v,[s])\longmapsto(t(e),[h_es]).
$$

下面明确说明对任意历史摘要的最小性，不预先假设候选摘要是当前分支的函数。

令 $\mathcal H_v$ 是从给定初态出发、终止于顶点 $v$ 的全部有限合法历史。对 $\gamma\in\mathcal H_v$，定义其真实归一化分支

$$
s_\gamma=A_v^{-1}T_\gamma s_0\in O.
$$

一个候选观察器在顶点 $v$ 的完整内部摘要为

$$
\sigma_v:\mathcal H_v\to W_v,
\qquad W_v^{\mathrm{reach}}=\sigma_v(\mathcal H_v).
$$

只对每个已知当前顶点分别取可达摘要集 $W_v^{\mathrm{reach}}$。要求存在确定性更新与确定性解码

$$
U_e:W_v^{\mathrm{reach}}\to W_w^{\mathrm{reach}},
\qquad d_v:W_v^{\mathrm{reach}}\to Y_v,
$$

使每条 $e:v\to w$ 及每个 $\gamma\in\mathcal H_v$ 满足

$$
\sigma_w(\gamma e)=U_e(\sigma_v(\gamma)),
\qquad
d_v(\sigma_v(\gamma))=o_v(T_\gamma s_0).
$$

这里“两个历史摘要相同”必须意味着承担更新和读数的完整内部状态相同。若后续响应仍依赖被遗漏的观察器内部状态，则上述确定性 $U_e,d_v$ 不存在，本定理的前提没有满足。

若 $\sigma_v(\gamma)=\sigma_v(\gamma')$，确定性更新按延续长度归纳，给出两历史在每个相同合法延续后的摘要相同；再用确定性精确解码，得到全部未来读数相同。因此

$$
s_\gamma\sim s_{\gamma'}.
$$

故映射

$$
\pi_v:W_v^{\mathrm{reach}}\to M,
\qquad
\pi_v(\sigma_v(\gamma))=[s_\gamma]
$$

良定义。每个顶点都能到达每个 $O$ 中分支，故 $\pi_v$ 满射；因为 $\sigma_v$ 满射到自己的可达像，满足这条历史因子分解等式的 $\pi_v$ 唯一。并且

$$
\pi_w U_e=\overline U_e\pi_v,
\qquad
d_v=\overline f_v\pi_v.
$$

这就是最小性：任何精确承担指定任务的完整历史摘要，在每个已知当前顶点都有唯一的规范满射到 $M$。候选可以记住更多旧历史，但不能合并不同的 $\sim$ 类。

因此

$$
\boxed{
\text{有限精确工作记忆存在}
\iff |M|<\infty.
}
$$

这既不要求 $G$ 有限，也不由底图有限自动保证。若还要求在记忆内部保存并区分当前顶点，则可用 $V\times M$；本节的“最小分支记忆”始终是在顶点已知的条件下逐顶点比较，不能把不同顶点的外部知识暗中算作免费恢复的内部记忆。

完整分支轨道 $O$ 本身最小，当且仅当

$$
s\ne t
\Longrightarrow
\exists g\in G\ \exists w\in V,
\quad f_w(gs)\ne f_w(gt).
$$

即时读数单射是充分条件但非必要条件；未来操作可以显露当前尚未显露的区别。

### 2.2 陪集公式：操作、分支与任务记忆是三种大小

设

$$
H=\operatorname{Stab}_G(s_0),
\qquad
K=\{g\in G:gs_0\sim s_0\}.
$$

$K$ 是商作用中 $[s_0]$ 的稳定子，所以为子群，且 $H\subseteq K$。也可直接证明：若 $g,k\in K$，关系的 $G$-不变性给出 $gks_0\sim gs_0\sim s_0$；对 $gs_0\sim s_0$ 施加 $g^{-1}$，得到 $g^{-1}s_0\sim s_0$。

轨道—稳定子对应给出

$$
\boxed{O\cong G/H,\qquad M\cong G/K.}
$$

具体地，$gK\mapsto[gs_0]$ 良定义且为双射，因为

$$
[gs_0]=[hs_0]
\iff h^{-1}g\in K
\iff gK=hK.
$$

因此三种区别分别是

$$
\begin{aligned}
G &: \text{运输操作本身的区别},\\
G/H &: \text{给定初态可达分支的区别},\\
G/K &: \text{任务必须保留的未来行为区别}.
\end{aligned}
$$

若有限，最小记忆状态数为 $[G:K]$。$K$ 不必正规，$G/K$ 是陪集作用集合而非自动成为商群；记忆状态数也不是一般意义的最小实向量空间维数。

### 2.3 有限轨道时的计算与实际分辨路径

若 $O$ 有限、显式可枚举，生成元作用表已知，读数相等可判定，取恰由选定方向的基本非树边生成元及其逆组成的有限集 $S$（无非树边时可加入恒等），定义

$$
R_0=\bigcap_{v\in V}\ker f_v,
$$

$$
R_{n+1}
=R_0\cap\bigcap_{h\in S}(h\times h)^{-1}R_n.
$$

归纳可知，$R_n$ 恰检验长度不超过 $n$ 的生成元词及全部终端读数。因而它递减，交为 $\sim$；若某步 $R_n=R_{n+1}$，对同一细化算子再次作用即得 $R_{n+1}=R_{n+2}$，故平台永久稳定。

令

$$
c_0=|O/R_0|,
\qquad m=|M|.
$$

每次严格细化至少多一个类，最终类数为 $m$，所以严格分裂次数及首次稳定深度至多

$$
m-c_0\le |O|-c_0.
$$

这适配既有 `controlled_finite_stability`，不是另行宣称一个新的基础最小化原理。联合读数的余域可取其实际像，从而满足既有定理的满射前提。无非树边时可单独处理，或加入恒等动作满足非空动作类型条件。

这个深度计算的是生成元词长，不是物理时间。若生成树上根到顶点的最大边距离为 $D$，每个根生成闭环的实际边长至多 $2D+1$。两个不同记忆类有某个长度不超过 $m-c_0$ 的生成元词及某个终端顶点能区分它们。从任意已知当前顶点实际执行“回根—这些闭环—前往读数顶点”，总边长不超过

$$
\boxed{2D+(2D+1)(m-c_0).}
$$

这是一条分辨路径长度上界；实际耗时还需要每条边的执行代价，不能由图边数自动推出。

### 2.4 圆环二覆盖：非平凡运输可以对应两态或一态记忆

取底图为圆环 $C_m$，$m\ge3$，纤维为 $\{+1,-1\}$。生成树上的边运输为恒等，唯一非树边交换正负，其逆也交换正负。初始根分支为 $+1$。

对闭合路径，若净绕数为 $n$，最终归一化分支为

$$
s=(-1)^n.
$$

也可以用非树边经过次数的奇偶描述该分支；正反经过都翻转符号，故模二后与有向绕数一致。

若任务能读取根分支，其他顶点即使只有常值读数，也能通过沿树返回根区分正负。因此

$$
|M|=2.
$$

若任务只读取底图位置，且合法性不依赖分支，则全部分支未来等价，故

$$
|M|=1.
$$

所以同一个非平凡几何闭环，不决定同一个任务记忆需求。任务是否能够使用分支区别，必须单独说明。

其连续几何实现是圆周二覆盖 $z\mapsto z^2$。仓内 `CircleDoubleCoverHistoryLift` 已提供：给定初始提升点后路径提升唯一；不存在连续全局截面；底圆周完整一圈的提升从 $1$ 到 $-1$。

两态摘要只保存绕行奇偶，不恢复整数绕数，也不恢复包含回退在内的完整原始路径档案。这是覆盖与路径问题，不是环境结型定理。

### 2.5 最小非交换置换例子：六个操作、三个记忆状态

取一个顶点及两条环边，纤维与运输为

$$
F=\{1,2,3\},
\qquad a=(12),
\qquad b=(23).
$$

初态为 $1$，任务读数为

$$
f(s)=\mathbf1_{\{1\}}(s).
$$

此时 $G=S_3$，有六个群元素；可达轨道有三个分支。当前读数合并 $2,3$，但追加 $a$ 后

$$
f(a2)=1,
\qquad f(a3)=0.
$$

分支 $1$ 已由当前读数区别于另外两个，故全部三个分支未来可分。于是

$$
\boxed{|G|=6,\qquad |O|=|M|=3.}
$$

按从左到右执行词，得到

| 已执行词 | 最终分支 | 当前读数 | 再追加 $a$ 的读数 |
|---|---:|---:|---:|
| $ab$ | $3$ | $0$ | $0$ |
| $ba$ | $2$ | $0$ | $1$ |

两词有相同生成元计数、相同顶点、相同当前读数，却有不同的未来行为。阿贝尔化绕行计数不足以承担这个任务。

更直接地，形式交换子路径 $a\,b\,\bar a\,\bar b$ 对每种有向生成元的净计数均为零；由于此例的两个运输都是对合，它的运输等于按顺序执行 $abab$，却把 $1$ 送到 $2$，并非恒等。

本例

$$
H=K=\operatorname{Stab}(1)=\{\mathrm{id},(23)\}
$$

在 $S_3$ 中不正规。这同时展示为什么最小任务记忆应是陪集作用集合，不能默认是商群。

三分支是非交换置换作用的最小可能分支数：两个及以下元素上的置换群均交换。两个生成元也是生成非交换群所必需的最少生成元数。这里不宣称任意其他线性或代数模型的普遍最小性。

### 2.6 操作权限及无限记忆反例

取单顶点、一个环，令

$$
F=\mathbb Z,
\qquad T(n)=n+1,
\qquad s_0=0,
\qquad f(n)=\mathbf1_{\{0\}}(n).
$$

若 $T,T^{-1}$ 均允许，则任意 $n\ne m$ 都可由未来平移 $-n$ 区分：

$$
f(n-n)=1,
\qquad f(m-n)=0.
$$

因此 $O=\mathbb Z$，未来等价关系就是相等，最小任务记忆无限。有限底图和二值读数不能保证有限工作记忆。

同一个无限轨道，若改读数为奇偶，只需两态；若改为常值，只需一态。这进一步分开轨道大小和任务记忆大小。

若保留原读数，但只允许向前执行 $T$，实际可达集变成 $\mathbb N_0$。所有正整数对全部合法未来词的输出都为零，初态零则在空词读数上不同，故最小任务记忆恰为两态。

这说明用于比较坐标的逆映射，不等于观察者真正获准执行的逆操作。将形式逆元加入实际操作语言，会改变未来可区分关系与最小记忆。

受限权限时，应直接使用合法路径版本。设

$$
R_v=\{A_v^{-1}T_\gamma s_0:
\gamma:o\to v\text{ 是实际合法历史}\}.
$$

在 $R_v$ 上令 $s\sim_v t$ 当且仅当相同未来词在两者上的合法性一致，且对合法词，全部指定输出一致。若合法性只依赖顶点，只需比较从 $v$ 出发的允许路径读数；若依赖分支，则定义域一致也是必要条件。

对每条实际边 $e:v\to w$，定义其实际合法域

$$
D_e=\{s\in R_v:e\text{ 在分支 }s\text{ 上合法}\}.
$$

$D_e$ 对 $\sim_v$ 饱和：若 $s\sim_v t$，则仅执行 $e$ 这个未来词的合法性一致，故 $s\in D_e$ 当且仅当 $t\in D_e$。因此商上的合法域正是由 $D_e$ 构成的那些类，边更新的准确类型为

$$
D_e/{\sim_v}\longrightarrow R_w/{\sim_w},
\qquad [s]\longmapsto[h_es],
$$

其中分母表示 $\sim_v$ 在 $D_e$ 上的限制。若 $s\in D_e$，从一条到达 $s$ 的合法历史再执行 $e$，可知 $h_es\in R_w$。若 $s\sim_v t$ 且两者属于 $D_e$，把任意后续词接到 $e$ 后面，使用 $\sim_v$ 的定义便得 $h_es\sim_w h_et$，所以该部分商更新良定义。最小性仍由A卷第2.1节对完整确定性历史摘要的延续归纳给出，但一般不再有跨顶点统一的群轨道或 $G/K$ 公式。

若权限还依赖尚未编码的历史，就必须先把该历史依赖加入配置；不能在不满足 Markov 式更新前提的表示上直接套用上述商。

### 2.7 从基本相位到最小工作记忆：有限周期与圆周完成

在前述连通图中，进一步令每个顶点纤维为 $U(1)$，边运输为相位乘法；固定根处已知初态 $z_0\in U(1)$。所有边及逆边现在均须真正允许执行，当前顶点外部已知，树路径运输与参考已校准。根端口允许两种读数

$$
Q(z)=\bigl(|1+z|^2,\ |1+iz|^2\bigr).
\tag{TM.8}
$$

式(TM.3)证明 $Q$ 单射。非根顶点的状态可以沿已知树路径返回根后读取；形式逆本身不供应这个权限。

下文计算的是一个闭合确定性预测接口的状态数：外部输入只含已知当前顶点与下一条具名边或查询标记，更新和答案由这些输入及所计状态决定。若接口还会读取旧档案、累计次数、外部控制器状态或新实验结果，则所有能改变预测的该类数据都必须纳入所计状态；不把它们作为免费且可不同的旁路。完整档案仍可在观察者其他结构中保留，结论只计承担所声明预测任务的充分商，不声称压缩整份档案，也不讨论允许免费重读整份档案的算法工作空间。

记 $h_1,\ldots,h_r$ 为基本环相位，并设

$$
G=\langle h_1,\ldots,h_r\rangle\le U(1).
\tag{TM.9}
$$

**命题 2.1。** 每个已知当前顶点上的未来行为商与 $z_0G$ 双射，后者构成无行为冗余的最小确定性工作记忆。此处任务是精确恢复所有允许未来根端口读数，不包含对完整历史档案的压缩。无限集合中仅有相同状态基数不保证实现无冗余或具有该规范同构。

**证明。** 使用 A卷第2.1节 的历史摘要最小性：纤维取 $U(1)$，运输取相位乘法，初态取 $z_0$，根读数取式（TM.8），其余顶点通过实际允许的树逆路径返回根。于是可达轨道为 $z_0G$，根处单射读数 $Q$ 分离轨道的任意两点，故该处的未来等价关系就是相等。A卷第2.1节 对任意完整确定性历史摘要构造的唯一规范满射，遂给出到 $z_0G$ 的满射；保存当前相位则达到该下界。这一代入依赖本节已经声明的逆向权限、已知顶点和无未计旁路的闭合预测合同。证毕。

**推论 2.2。** 存在有限状态的精确工作记忆，当且仅当每个 $h_j$ 都是单位根。若其阶分别为 $d_j$，则最小状态数为

$$
m=\operatorname{lcm}(d_1,\ldots,d_r),
\tag{TM.10}
$$

无非树边时约定 $m=1$。

**证明。** 有限 $G$ 中每个元素必有有限阶。反之，若全部 $h_j$ 的阶有限，则它们均属恰有 $m$ 个元素的 $m$ 次单位根群 $\mu_m$，故 $G\le\mu_m$ 有限。Lagrange 定理给 $|G|\mid m$；对每个生成元的循环子群又给 $d_j\mid |G|$，所以 $m\mid |G|$，两者相等。无生成元或全部生成元为一时直接得到 $G=\{1\}$ 和 $m=1$。再用 $z_0G$ 与 $G$ 的双射及上一命题。证毕。

例如，一个相位 $e^{2\pi i/3}$ 需要三态；两个基本相位的阶分别为二、三时需要六态；若某个 $h_j$ 有无限阶，则需要无限多个精确工作状态。后一个结论不意味着必须使用无限多个坐标：单个单位复数即可表示当前工作状态，但它有无限多个可区分值。有限状态数、有限坐标数、有限精度和物理存储成本是不同要求。

**通常拓扑下的完成。** 若某个 $h_j$ 有无限阶，Context49.11的单位圆幂稠密论证给 $\overline{\langle h_j\rangle}=U(1)$，因此 $\overline{z_0G}=U(1)$。$G$ 由有限个生成元生成，故至多可数；通常圆周完成有不可数多个点。因此实际有限路径可达轨道严格小于其通常拓扑完成。单位根情形则轨道有限且已闭。

这里直接复用 Context49.11 已有的圆周稠密性，不把它当作新的数论结果。所用拓扑必须写明：通常弦长拓扑允许逼近新相位；若将精确根读数 $Q(z)$ 的每一个不同值都视作离散符号，则根处任意两个不同轨道点已在深度零分开。非根顶点须先沿树返回根，再执行查询；分离深度由树路径长及查询是否另计一步决定。图有限使这些深度有统一有限上界，因此对应的精确前缀度量一致离散，不存在上述新的 Cauchy 极限。两种完成不能只因都称作“极限”而认成一个对象。

### 2.8 状态误差与运输误差具有不同的长期几何

已知运输与未知运输必须分开。固定同一个已知 $h\in U(1)$，两个单位相位初态 $z,z'\in U(1)$ 满足

$$
|h^nz-h^nz'|=|z-z'|\qquad(n\ge0).
\tag{TM.11}
$$

故无限精确状态数本身不排除关于初态误差的全时间一致稳定性。由式(TM.5)，同一运输下两组端口读数的 Euclidean 距离也恒为 $2|z-z'|$。

若同时比较两个运输 $h,h'$，则

$$
|h^nz-h'^nz'|
\le |z-z'|+n|h-h'|.
\tag{TM.12}
$$

证明先插入 $h^nz'$，对第二项应用单位相位幂的望远镜界。A卷第2.13节的 $h=1$、$h_m=e^{i\pi/m}$ 正是在相同初态下改变运输，给任意长重复的统一含噪恢复反例；它不是对固定已知运输的式(TM.11)的反例。

于是，同一关系结构中至少有三个独立问题：未知当前状态能否被读出，实际运输能否被标定，以及取得的误差保证对多长的后续任务有效。只有明确了这三者，才能将周期、记忆与全息恢复连接为可检验的结论。

**有限状态近似实现的边界。** 式(TM.11)比较同一精确运输作用于两个初态，并不保证有限状态、逐步舍入的实现能够无限期保持任意小误差。对此有一个直接反例定理：固定无限阶 $h$，每步输入同一个绕环标记。任何闭合有限确定性预测器给出的复数相位估计 $a_n$，均满足

$$
\sup_{n\ge0}|h^nz_0-a_n|\ge1.
\tag{TM.13}
$$

若每个估计均限制在 $U(1)$，该上确界等于二。

**证明。** 有限状态且每步输入相同，使状态及其输出最终周期化。取一个周期长度 $p\ge1$ 和进入周期后的固定位置 $n_0$，有 $a_{n_0+kp}=a$ 对全部 $k\ge0$ 成立。由于 $h$ 无限阶，$h^p$ 仍无限阶，Context49.11的正幂稠密性使 $h^{n_0+kp}z_0$ 在圆周稠密。连续距离函数于是给

$$
\sup_{k\ge0}|h^{n_0+kp}z_0-a|
=\sup_{|z|=1}|z-a|=1+|a|\ge1.
$$

最后一个等式在 $a\ne0$ 时取与 $a$ 相反的单位方向，在 $a=0$ 时直接成立。若 $|a_n|=1$，这一子序列的误差上确界为二，而所有时刻误差均至多二。证毕。

这一界不排除有界视界上的高精度有限实现，不排除无限状态的单坐标表示，也不排除具有另行计费的外部时钟或档案访问的算法。它把周期性状态机、稠密相位过程和资源受限预测明确分开。

### 2.9 共同端口的干涉读取路径间关系

给每条实际边另配正实幅度增益 $r_e>0$，定义

$$
w_e=r_eu_e,\qquad r(P)=\prod_{e\in P}r_e.
$$

零增益边应从有效支持图中剔除，否则其相位没有可见作用。分束或合束若另有复系数，其相位必须明确计入边运输或端口合同。本节只取有限声明路径族；若改取无穷路径和，必须另有合法的收敛及重排合同。

**命题 2.3（双路径强度与环相位）。** 同一实际相干来源 $\xi$ 经两条允许的路径 $P,Q:s\to t$，在同一输出模式相加，振幅为

$$
a=\xi r(P)u(P),\qquad b=\xi r(Q)u(Q).
$$

则

$$
|a+b|^2
= |\xi|^2
\left[
r(P)^2+r(Q)^2
+2r(P)r(Q)\operatorname{Re}u(P\bar Q)
\right].
\tag{AP.8}
$$

共同端点换基保持该强度及交叉项。

**证明。** 展开 $(a+b)(\bar a+\bar b)$，对角项分别为 $|\xi|^2r(P)^2$、$|\xi|^2r(Q)^2$；交叉项之和为
$2|\xi|^2r(P)r(Q)\operatorname{Re}(u(P)\overline{u(Q)})$，再用A卷命题1.1。两条振幅在端点换基下乘同一个单位因子，故平方模及交叉项保持。若来源坐标也按 $g_s$ 运输，则输出坐标整体乘 $g_t$，结论相同。证毕。

两条路径必须属于同一个实际实验及共同相干来源；终端模式、时序和端口合同必须允许振幅相加。不同模式只有在声明实际合束操作后才能套用式（AP.8）。复数或负振幅不是概率；一般路径矩阵也不自动满足概率归一化。

**命题 2.4（完整端口共同运输）。** 取列状态邻接矩阵

$$
A_{ts}=\sum_{e:s\to t}w_e,\qquad G=\operatorname{diag}(g_v).
$$

逐边换基给

$$
A'=GAG^{-1}.
$$

对输入、读出及初态共同运输

$$
B'=GB,\qquad H'=HG^{-1},\qquad x'_0=Gx_0,
\tag{AP.9}
$$

则所有 $n\ge0$ 满足

$$
H'(A')^nB'=HA^nB,\qquad
H'(A')^nx'_0=HA^nx_0.
\tag{AP.10}
$$

同一输入序列下的全部有限时刻实际输出保持。

**证明。** 对每个矩阵元，所有同首尾边具有共同因子 $g_t/g_s$，所以求和给相似式。归纳得 $(A')^n=GA^nG^{-1}$，代入式（AP.9）并抵消给式（AP.10）。对于更新 $x_{n+1}=Ax_n+Bu_n$，若 $x'_n=Gx_n$，则
$A'x'_n+B'u_n=G(Ax_n+Bu_n)$；从共同初态归纳，所有状态满足该关系，读出亦相同。证毕。

只变 $A$ 而固定跨顶点混合的 $H$，一般改变了实验。具名平行边在矩阵中被求和，又是另一层信息压缩；这些矩阵等式不自动恢复各边身份或各边相位。

### 2.10 路径记录与可读取的相干

到达同一输出端口时，两条路径还分别关联有限维记录向量 $\eta_P,\eta_Q$，且二者范数为一。只读取输出强度、不区分这些记录时，令

$$
I=\|a\eta_P+b\eta_Q\|^2,\qquad
\mu=\sum_k\eta_P(k)\overline{\eta_Q(k)}.
$$

**命题 2.5（记录重叠的干涉因子）。**

$$
I=|a|^2+|b|^2+2\operatorname{Re}(a\bar b\,\mu),
\qquad |\mu|\le1.
\tag{AP.11}
$$

**证明。** 按记录坐标展开平方模并求和。对角项由两记录归一化给 $|a|^2,|b|^2$；交叉项为 $a\bar b\,\mu$ 及其共轭。Cauchy–Schwarz 给 $|\mu|\le\|\eta_P\|\|\eta_Q\|=1$。证毕。

相同记录给 $\mu=1$，恢复完整干涉；正交记录给 $\mu=0$，该强度不再含路径相位；单位模重叠只移动相位，严格小于一的重叠降低可见交叉项。同一来源本身不足以担保指定端口仍保持相干。

式（AP.11）与仓内 EnvironmentRecords.recordOverlap 的定义完全同型。PhaseRecordRecoveryCriterion 的准确结论是：单位模重叠可由声明的匹配操作联合反转；严格收缩后再施加对应共轭通道，会留下 $|\mu|^2$ 因子。它没有证明获得完整环境访问后仍无法恢复，也不把任意数学反转授予观察者。

**命题 2.6（保留档案的随机振幅版本）。** 若 $A,B$ 在给定完整已获档案 $C$ 后具有有限二阶矩，则

$$
\mathbb E[|A+B|^2\mid C]
= \mathbb E[|A|^2\mid C]
+\mathbb E[|B|^2\mid C]
+2\operatorname{Re}\mathbb E[A\bar B\mid C].
\tag{AP.12}
$$

**证明。** 逐实现展开平方模，再取同一条件期望。二阶矩及 Cauchy–Schwarz 保证交叉项可积；条件期望线性及其与实部交换给公式。证毕。

条件独立性只有配合相应条件均值等条件才保证交叉项为零。例如条件独立且两条件均值为零是充分条件；仅凭“不同路径”不能宣布独立。若两臂来自同一随机振幅 $\xi$ 的已知线性分束，公共随机相位会在 $\xi\bar\xi$ 中抵消，不能因来源随机而自动删除干涉。

### 2.11 四相位读数、恢复范围与精确误差界

假设允许在第二条路径施加已校准相位 $e^{i\alpha}$，并在同一稳定来源、同一记录及端口合同下获得四份读数。记

$$
\Gamma=a\bar b\,\mu,\qquad B_0=|a|^2+|b|^2.
$$

**命题 2.7（复交叉项恢复）。** 相位扫描给

$$
I_\alpha=B_0+2\operatorname{Re}(e^{-i\alpha}\Gamma),
$$

因而

$$
\Gamma=
\frac{I_0-I_\pi}{4}
+i\,\frac{I_{\pi/2}-I_{3\pi/2}}4.
\tag{AP.13}
$$

**证明。** 将A卷命题2.5中的第二振幅替换为 $e^{i\alpha}b$。若 $\Gamma=x+iy$，四个读数依次为 $B_0+2x,B_0+2y,B_0-2x,B_0-2y$，按相同相位配对作差即得公式。共同背景 $B_0$ 在差分中消去。证毕。

如果 $|\xi|^2r(P)r(Q)$ 已校准且非零，记录重叠 $\mu$ 也已知非零，则

$$
u(P\bar Q)
= \frac{\Gamma}{|\xi|^2r(P)r(Q)\mu}.
\tag{AP.14}
$$

这是将A卷命题2.3中的交叉项代入定义后的精确除法。若 $\mu=0$，所有扫描读数都不含该环相位；若 $\mu$ 未知，扫描首先只识别乘积 $\Gamma$，不能直接分离记录关联与路径相位。四次使用的来源、相位控制、记录和校准若发生未计入的变化，式（AP.13）不是同一未知量的恢复式。

**命题 2.8（强度误差的运输）。** 若四份强度读数各自实误差绝对值至多 $\varepsilon$，则用式（AP.13）计算的 $\widehat\Gamma$ 满足

$$
|\widehat\Gamma-\Gamma|\le\frac{\varepsilon}{\sqrt2}.
\tag{AP.15}
$$

在式（AP.14）的分母精确已知时，对应环相位估计误差至多

$$
\frac{\varepsilon}
{\sqrt2\,|\xi|^2r(P)r(Q)|\mu|}.
\tag{AP.16}
$$

**证明。** 每个差分的误差至多 $2\varepsilon$，除以四后实部、虚部误差分别至多 $\varepsilon/2$。复模误差至多 $\sqrt{2(\varepsilon/2)^2}=\varepsilon/\sqrt2$。再除以精确已知非零分母的模，得到式（AP.16）。证毕。

相干重叠接近零时，这个恢复保证失去稳定性。取得四份同合同读数、相位扫描及校准所需资源另行计量；公式不提供免费的独立重备或未获参考。分母有误差时还需另给其下界与误差传播，不能使用式（AP.16）冒充已经包含校准噪声。

### 2.12 两个相位读出恢复一个基本闭环

假设对每个所需基本闭环，可以将参考路径与该闭环路径在同一输出端口相干合成，且已独立校准振幅因子，使两路未知相对振幅恰为 $h_e$，合成表达为 $1$ 与 $h_e$。可控制的参考相移为 $\theta$，读数定义为

$$
I_{e,\theta}=|1+e^{i\theta}h_e|^2
=2+2\operatorname{Re}(e^{i\theta}h_e).
\tag{TM.2}
$$

这里的 $I$ 是指定模型的强度读数，未归一化为概率，也未假定其物理实现免费。必须同一未知 $h_e$ 在两次实验中保持，或有已证运输将两次数据归到同一未知量；取得旧读数后的模型漂移不能忽略。

**命题 2.9。** 两个读数 $I_{e,0},I_{e,\pi/2}$ 唯一给出

$$
h_e=\frac{I_{e,0}-2}{2}
-i\frac{I_{e,\pi/2}-2}{2}.
\tag{TM.3}
$$

因此，在上述取得合同满足时，$2r$ 个精确强度读数足以恢复整份相位运输的节点换基等价类。

**证明。** 写 $h_e=x+iy$，式(TM.2)给出 $I_{e,0}=2+2x$ 与 $I_{e,\pi/2}=2-2y$。式(TM.3)直接恢复两个实坐标，再应用A卷第1.4节一一对应。证毕。

这个结论是一个显式充分测量设计，不声称它在任意连续或非连续测量语言中是最少次数。若只允许 $\theta=0$，则 $h=i$ 与 $h=-i$ 都给 $I=2$，而第二读数分别为零与四；单一余弦读数不能一般恢复带方向的相位。

更一般，已知且非零的共同振幅 $a,b\in\mathbb C$ 给 $I_\theta=|a+e^{i\theta}bh|^2$。令 $B=|a|^2+|b|^2$，则

$$
h=\frac{(I_0-B)-i(I_{\pi/2}-B)}{2\overline a b}.
\tag{TM.4}
$$

若 $a=0$ 或 $b=0$，所有强度均与 $h$ 无关。这给相干参考缺失时的精确不可识别反例。


**约定 2.10（两种相位扫描的符号对齐）。** 本节令受控第二振幅为 $e^{i\theta}h$，所以 $I_{\pi/2}=2-2\operatorname{Im}h$。A卷第2.11节 的扫描写成 $a+e^{i\alpha}b$ 并恢复 $\Gamma=a\overline b\,\mu$，其虚部公式为正号。令该节 $a=1,b=h,\mu=1,\alpha=\theta$，则 $\Gamma=\overline h$，故两式相互共轭而一致。对本节一般式（TM.4），取 AP 的第二振幅为 $bh$，得到 $\Gamma=a\overline b\,\overline h$；由 $h=\overline\Gamma/(\overline a b)$ 得同一负号公式。两读数恢复需要已知背景与非零校准；四读数差分可消去共同未知背景，但仍需同一稳定来源、记录和相位控制。各自的同时误差界及分母条件保持独立，不能互换。

### 2.13 恢复误差沿路径的传播

**命题 2.11。** 对任意两个合法单位相位 $h,h'$，两读数差满足

$$
|h-h'|=\frac12\sqrt{(I_0-I'_0)^2+(I_{\pi/2}-I'_{\pi/2})^2}.
\tag{TM.5}
$$

**证明。** 两读数之差分别是 $2\operatorname{Re}(h-h')$ 和 $-2\operatorname{Im}(h-h')$；平方相加即可。证毕。

若给出的两次强度各有同时误差界 $\varepsilon_0,\varepsilon_1$，由式(TM.3)形成的复数估计与真值的距离至多 $\sqrt{\varepsilon_0^2+\varepsilon_1^2}/2$，但估计未必落在单位圆上。比较两个与同一数据及误差合同相容的单位相位，则其距离至多 $\sqrt{\varepsilon_0^2+\varepsilon_1^2}$；此处每个坐标的两个合法值至多相差 $2\varepsilon_j$。联合误差合同必须在同一个事件上成立，不能用各自不同的成功事件当作同时保证。

在生成树规范中，闭路 $\gamma$ 的运输为

$$
H_\gamma=\prod_{e\notin T}h_e^{n_e(\gamma)},
\tag{TM.6}
$$

其中 $n_e$ 是对该具名非树边的有向净遍历数。这个净计数式使用相位的交换性；非交换纤维运输必须保留完整词序。

对两份单位相位族，若 $|h_e-h'_e|\le\eta_e$，则

$$
|H_\gamma-H'_\gamma|
\le\sum_{e\notin T}|n_e(\gamma)|\eta_e.
\tag{TM.7}
$$

**证明。** 正整数幂的差按有限望远镜和展开；单位模使每项模至多 $|h-h'|$。负幂取共轭，获得同一界。有限个单位模因子乘积再作望远镜差即得结论。证毕。

因此，在所有被允许未来闭路都满足 $\sum_e|n_e|\le L$ 且所有 $\eta_e\le\eta$ 的任务内，有共同误差界 $L\eta$。若允许任意 $U(1)$ 相位及同一闭环的任意多次合法重复，则任意小的正基础读数误差，都不能保证一个随该误差趋零而趋零的全重复任务统一误差界。精确读数仍可确定全部路径运输；下面否定的是含噪恢复的这种统一稳定性。

**反例 2.12。** 单个基本环取 $h=1$ 与 $h_m=e^{i\pi/m}$。则 $h_m\to1$，两次基本强度读数也趋同，但绕该环 $m$ 次后 $h_m^m=-1$，而 $h^m=1$，距离恒为二。这不否定每条固定路径的连续性。更强地，对任意 $\varepsilon>0$，取足够大的 $m$，使两组基本强度的对应坐标相差至多 $2\varepsilon$。两组读数的中点就是同时符合两模型逐坐标误差界 $\varepsilon$ 的同一份数据。第 $m$ 次合法重复的目标分别为 $1$ 与 $-1$；任何仅使用此数据的恢复器给出相同估计 $z$，由 $2\le|z-1|+|z+1|$，至少在一个模型上误差不小于一。重复次数尚不是物理时长。

### 2.14 最小实例及三类盲区

**例 2.13（无有向闭圈仍有路径相位障碍）。** 取两个具名平行有向边 $s\to t$，两条路径振幅分别为

$$
a=\frac12,\qquad b=\frac{e^{i\phi}}2.
$$

该有向图没有任何正长度有向闭路径，故只检查有向闭路径的条件空真。但形式闭走法及双路径比较的相位可以非平凡。因此，在一般有向图上，“所有有向闭路径相位为一”不足以保证相位场可消去。以一个两臂有向菱形替代平行边得到同样障碍。强连通等额外条件才可能补足这种检验。

其固定一次强度读数为

$$
I_0=\frac{1+\cos\phi}{2}.
\tag{AP.17}
$$

当 $\phi=\pi/2$ 与 $-\pi/2$ 时，两者都给 $I_0=1/2$，但基本环相位不同，不能由顶点换基互换。在第二臂施加 $\alpha=\pi/2$，前一振幅变为 $-1/2$，与第一臂相消，读数零；后一振幅变为 $1/2$，读数一。故规范不变读数未必分离全部规范等价类。所有数值均由两个复数相加直接算得。证毕。

**例 2.14（遗漏相位参考）。** 对单条路径，$a$ 与 $e^{i\theta}a$ 的强度相同，故仅有这些强度不能恢复相对于遗漏参考的相位。加入同端口参考 $r\ne0$ 后，读取

$$
|a+e^{i\alpha}r|^2
$$

并按四相位差分即可恢复 $a\bar r$。这恢复的是相对参考的关系，不是无参考的绝对相位。若参考本来已经属于完整档案，不能删除它来制造不可识别性。证毕。

**例 2.15（相位变化不推出熵增或时间箭头）。** 明确选择两维酉模型

$$
\psi(t)=\frac1{\sqrt2}(1,e^{-i\omega t}),\qquad
\rho(t)=\psi(t)\psi(t)^*.
$$

演化为 $\operatorname{diag}(1,e^{-i\omega t})$，逆由 $-t$ 给出。向量归一化使 $\rho(t)$ 始终为秩一投影，谱为 $(1,0)$，故 von Neumann 熵恒为零。在声明的通常量子投影读数模型中，采用加减基得到

$$
p_\pm(t)=\frac{1\pm\cos(\omega t)}2.
\tag{AP.18}
$$

直接将 $\psi(t)$ 与两个归一化加减向量配对并取平方模即可验证。两概率之和为一，测量 Shannon 熵周期变化。这排除了“相位变化必然产生全态熵增”，也排除了“某个读数熵增加便建立不可逆时间方向”。这里明确增加了有限维酉态与投影读数模型，不从一般复权图推出量子概率规则。证毕。

### 2.15 频率、记忆次序与局部标架的准确连接

**命题 2.16（路径相对频率）。** 若同一校准参数 $t$ 下，

$$
u_e(t)=e^{-i\omega_et},
$$

则

$$
u(P,t)=e^{-i\Omega_Pt},\qquad
\Omega_P=\sum_{e\in P}\omega_e,
$$

形式逆遍历对该和取负号，并且

$$
u(P\bar Q,t)=e^{-i(\Omega_P-\Omega_Q)t}.
\tag{AP.19}
$$

**证明。** 指数对加法的字符律把有限相位乘积变成频率和的相位；形式逆给相反频率。对两条路径应用同一等式并相除即可。证毕。

在非零交叉项、固定记录与幅度条件下，干涉读数含由 $\Omega_P-\Omega_Q$ 控制的余弦项；差为零时该交叉项不随 $t$ 变化，差非零且交叉系数非零时，该余弦项周期为 $2\pi/|\Omega_P-\Omega_Q|$。单个校准时刻的相位只给模 $2\pi$ 条件，不自动恢复实频率；多个通道也不自动有公共精确周期。

式（AP.19）直接复用 PrimeFrequencyPhaseFlow 的字符律与 PhaseTwistedStableSwapCurvature.relative_phase_reconstruction。取 $\omega=\log p$ 是另一个明确的参数指定，不是证明一切频率都来自素数。标量相位乘积只见频率之和，因此遗失同一批标量因子的排列次序。

PrimeSwapCurvature 中保留次序的是另一种对象：

$$
U_p=
\begin{pmatrix}a&b_p\\0&\lambda_p\end{pmatrix},
$$

$$
U_qU_p-U_pU_q
= \begin{pmatrix}
0&(a-\lambda_q)b_p-(a-\lambda_p)b_q\\
0&0
\end{pmatrix}.
\tag{AP.20}
$$

直接乘两个上三角矩阵得到式（AP.20）。共同记忆原点变换

$$
b_p\longmapsto b_p+(a-\lambda_p)c
$$

使右上角新增两项
$(a-\lambda_q)(a-\lambda_p)c-(a-\lambda_p)(a-\lambda_q)c=0$，所以保持交换差。非共振时，既有源码进一步把它分解为两共振间隙之积乘局部原点估计之差；其非零分母条件仍须保留。这是带记忆提升的交换缺陷，不能认作两个 $U(1)$ 标量的交换子，因为后者恒为零。图上的不同路径相位可以不同，是因为路径经过的具名边和上下文不同，并非标量乘法不交换。没有可逆性条件时，矩阵交换差也不能擅自改写为可执行群交换环。

LocalEulerFrameHistoryNonreconstruction 证明：局部 Euler 行列式不能恢复原始 $GL_2$ 标架族及跨地址运输。但该模块中的运输来自

$$
T_{j\leftarrow i}=F_j^{-1}F_i.
$$

沿闭路按执行次序相乘，邻接的 $F_iF_i^{-1}$ 逐个抵消，闭路运输自动为单位矩阵。因此，该模块不能作为非平凡闭环相位的见证；它支持的是局部谱读数没有保留原始跨位置标架关系。标架族、标架的规范等价类、实际固定端口下可辨认的关系是不同任务。

图的闭环也不等于空间纽结。上述模型只存入关联、方向、标签和参考，没有存入三维嵌入及允许的环境形变，因此没有推出纽结分类。

### 2.16 记忆计量与有限视界的使用边界

行为最小性计算的是全部决定后续准入、更新与输出的状态。如果实现另读可见配置 $v(h)$ 和内部状态 $m(h)$，则一般只有
$$
\operatorname{im}(v,m)\twoheadrightarrow H/{\sim},
$$
不能直接改成 $\operatorname{im}m\twoheadrightarrow H/{\sim}$。可见位自身是输出、更新恒等而内部状态单点即反例。固定同一完整可见配置后，$k$ 个两两未来可分历史仍要求 $k$ 个不同内部状态。任何会区分这些历史的额外档案、传感器数据、历史计数器或时钟，必须固定相同、不可访问，或计入所讨论总状态；收费访问也不能从状态容量账中排除。

有限视界商 $Q_n=H/{\sim_n}$ 给未来深度 $n$ 的静态区分下界。一般更新首先给 $Q_{n+1}\to Q_n$，不能无条件给同一 $Q_n$ 上的闭合更新。若相邻全域关系 $\sim_n=\sim_{n+1}$，在包含全部声明动作的标准行为细化递推下，该关系已对动作稳定，遂等于完整行为核。此处 $H$ 须包含同一实现的全部可达历史并对合法续接闭合，全部声明动作有限，且全部纳入任务的当前读数与步骤标签均取有限值。于是每个 $N_n=|Q_n|$ 有限；嵌套分割与上述平台性质给 $\sup_nN_n<\infty$ 当且仅当完整行为商有限。这里的相等须针对全部实际历史与合法操作，采样数据上连续两次没有增加类别不承担这一证明。

上述机制使用既有 GradedPredictionShift 的单更新分级映射与稳定合同；多动作部分域适配仍需逐首边归纳。MinimumRollbackAlphabet 仅供应固定可见纤维的有限标签计数机制；未来行为充分性及固定可见条件需先履行，不能把整个新增记忆论证宣称为该源码已逐字核验。


**无统一有限记忆的增长例。** 从零开始，状态为 $r\in\mathbb N_0$，允许 $\mathrm{inc}(r)=r+1$ 和 $\mathrm{dec}(r)=\max(r-1,0)$，读数为 $\mathbf1_{r=0}$。所有状态可达。深度 $n$ 的等价类恰为 $\{0\},\ldots,\{n\},\{r\ge n+1\}$：较小的两状态 $r<s$ 在至多 $r\le n$ 次 dec 后分离；两者都大于 $n$ 时，任一长度不超过 $n$ 的操作词及其前缀都不能使状态到零，因此读数相同。于是 $N_n=n+2$，每层可有限编码但不存在统一有限精确实现。最后一个类含 $n+1,n+2$，一步 dec 后分别属于单点类 $\{n\}$ 与尾类，所以这个有限视界商不能同层自主更新。本任务不读取原始日志；增加日志查询会改变这些等价类。

### 2.17 Weighted continuation tasks

**定义 2.17。** A weighted continuation system consists of a state set $Q$, a common set $\mathcal T$ of continuation tests, a partial action $\delta(q,u)$, an observation map $o:Q\to O$, an additive cost $c(q,u)$ in a cancellative commutative monoid $M$, and a duration $\tau(q,u)\in\mathbb N$. Tests have an identity $\varepsilon$ and an associative concatenation wherever defined. A legal two-stage action is exactly a legal concatenated action, and for every such action,
$$
\begin{aligned}
\delta(q,uv)&=\delta(\delta(q,u),v),\\
c(q,uv)&=c(q,u)+c(\delta(q,u),v),\\
\tau(q,uv)&=\tau(q,u)+\tau(\delta(q,u),v).
\end{aligned}
\tag{TM.552}
$$
The identity test leaves the state fixed and has zero cost and duration. Ordinary word concatenation with its legal partial transition action is an instance. Vectors of nonnegative real resource costs give an instance of $M$.

The residual task of $q$ is the function on the common test set
$$
\mathcal R_q(u)=
\begin{cases}
\bot,&\delta(q,u)\text{ is undefined},\\
\bigl(o(\delta(q,u)),c(q,u),\tau(q,u)\bigr),
&\delta(q,u)\text{ is defined}.
\end{cases}
\tag{TM.553}
$$
Define $q\sim q'$ exactly when $\mathcal R_q=\mathcal R_{q'}$. The weighted continuation quotient is $Q/{\sim}$.

**命题 2.18。** Equality of residual tasks is a right congruence for the partial action and preserves the cost and duration of each legal continuation. In particular, the action, observation, continuation cost, and continuation duration descend to the quotient.

**Proof.** Equality of residual functions gives the same legal tests and the same observed triples. If $u$ is legal from $q\sim q'$, then $v$ is legal from $\delta(q,u)$ exactly when $uv$ is legal from $q$, and likewise for $q'$. Thus these successor states admit the same tests. Their terminal observations agree by applying residual equality to $uv$. Additivity gives
$$
\begin{aligned}
c(q,uv)&=c(q,u)+c(\delta(q,u),v),\\
c(q',uv)&=c(q',u)+c(\delta(q',u),v).
\end{aligned}
\tag{TM.554}
$$
The left sides and the first summands agree, so cancellation in $M$ gives equality of the successor continuation costs. Cancellation in $\mathbb N$ gives the corresponding equality of durations. Hence $\delta(q,u)\sim\delta(q',u)$. The identity test supplies $o(q)=o(q')$. $\square$

**定理 2.19（preservation under continuation intertwining）。** Consider two weighted continuation systems with the same observation and cost sets. Suppose there are a surjective state map $h:Q\to Q'$ and a single bijection $\Phi:\mathcal T\to\mathcal T'$ of continuation tests, shared by all states, with the following properties:

1. $\Phi$ preserves the identity and defined concatenations in both directions.
2. For every $q,u$, the action $\delta(q,u)$ is defined if and only if $\delta'(h(q),\Phi(u))$ is defined, and then
   $$
   h(\delta(q,u))=\delta'(h(q),\Phi(u)).
   \tag{TM.555}
   $$
3. Observations, additional costs, and raw durations are preserved:
   $$
   \begin{aligned}
   o'(h(q))&=o(q),\\
   c'(h(q),\Phi(u))&=c(q,u),\\
   \tau'(h(q),\Phi(u))&=\tau(q,u)
   \end{aligned}
   \tag{TM.556}
   $$
   whenever the continuation is legal.

Then
$$
q\sim r\quad\Longleftrightarrow\quad h(q)\sim' h(r),
\tag{TM.557}
$$
and $h$ induces an isomorphism of the weighted continuation quotients, with tests identified by $\Phi$.

**Proof.** The hypotheses give the exact identity
$$
\mathcal R'_{h(q)}(\Phi(u))=\mathcal R_q(u)
\tag{TM.558}
$$
for every state and test, including undefined actions. Since $\Phi$ is a single surjective test correspondence, equality of either pair of residual functions is equivalent to equality of the other pair. Thus the map on quotient classes is well-defined and injective. Surjectivity of $h$ makes it surjective. The transition intertwining and preservation of cost, duration, and observation descend to the quotient by the preceding proposition. $\square$

**推论 2.20（terminal optimization）。** Any optimization of a fixed function of terminal observation, additional cost, and additional duration over legal continuation tests factors through the weighted continuation quotient. This includes a fixed duration constraint and a terminal reward minus a fixed function of accumulated resource cost.

**Proof.** Equivalent states have identical residual functions, hence identical feasible observed triples under every such constraint. Applying the same objective gives the same attainable objective values and therefore the same supremum or infimum whenever the chosen ordered codomain admits it. $\square$

**注 2.21。** Separate bijections between the continuation sets at individual states are insufficient unless they implement the same identification of tests across the states being compared. Equality of right languages compares the response to the same continuation. A state-dependent relabeling can exchange those tests. A bijection between represented integer values supplies none of the transition, test, cost, or duration equalities in this theorem.

### 2.18 相位恢复与既有结果的连接

主卷67.1和77.1分别承担二元与正实乘法的循环—势判据；ZeroLoopPotentialEquivalence承担一般连通路径群胚的加法版本。这里使用同一生成树构造，把相位等价类具体连接到两个可校准的端口强度及路径误差。它与《过程几何》的端口运输、逐路径相干相加、闭轨与开放响应区分相容；闭路相位恢复仍不等于仅由 trace/determinant恢复完整图或全部状态。

给定物理模型中哪些路径能相干合成、怎样对齐历时、参考相位如何取得、记录与环境如何共同保留，必须由实际实验合同给出。本文没有把图的形式逆当作反向执行，没有把相位消去当作档案删除，没有把非平凡闭环当作熵产生，也未推导物理三维空间或时间来自选基。

### 2.19 固定来源与准确复用边界

以下所有源码与理论地址均固定到 bfd5737539c696eedd4638da17d7f449339526cd。这些声明只在各自给定的假设范围内使用。

| 来源 | 可复用内容及不能外推的边界 |
| --- | --- |
| [RRO 定理67.1](https://github.com/the-omega-institute/trureturing/blob/bfd5737539c696eedd4638da17d7f449339526cd/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L32003) | 生成森林、基本循环、锚点及二元共同见证；简单无向图和 $\mathbb F_2$ 的计数概率不移入任意 $U(1)$ 实验。 |
| [RRO 定理77.1](https://github.com/the-omega-institute/trureturing/blob/bfd5737539c696eedd4638da17d7f449339526cd/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L34786) | 保留平行边的乘法闭路—势构造；正参考概率的固定律与正性合同不变为相位概率。 |
| [ZeroLoopPotentialEquivalence](https://github.com/the-omega-institute/trureturing/blob/bfd5737539c696eedd4638da17d7f449339526cd/D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence.lean#L37) | 连通群胚、任意交换加法群中的零闭路—势等价；群胚逆不授予实际逆向执行权限。 |
| [PrimeFrequencyPhaseFlow](https://github.com/the-omega-institute/trureturing/blob/bfd5737539c696eedd4638da17d7f449339526cd/D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow.lean#L116) | 单位模字符、时间／频率加法及标量乘积失序；不提供 Fourier 反演、熵律或时间箭头。 |
| [PrimeSwapCurvature](https://github.com/the-omega-institute/trureturing/blob/bfd5737539c696eedd4638da17d7f449339526cd/D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature.lean#L60) | 记忆交换差、共同原点规范不变及非共振分解；不是两个标量 $U(1)$ 因子的非交换曲率。 |
| [PhaseTwistedStableSwapCurvature](https://github.com/the-omega-institute/trureturing/blob/bfd5737539c696eedd4638da17d7f449339526cd/D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.lean#L84) | 相对频率与相位重建，单位模扭转保持相应残差范数界；不证明同步、时间单调或残差必然衰减。 |
| [LocalEulerFrameHistoryNonreconstruction](https://github.com/the-omega-institute/trureturing/blob/bfd5737539c696eedd4638da17d7f449339526cd/D5/S3/Observer/AgencyHolonomy/LocalEulerFrameHistoryNonreconstruction.lean#L34) | 相同行列式不能恢复原始标架历史及跨地址过渡；其由全局标架生成的运输具有平凡闭路乘积，不是非平凡环相位反例。 |
| [EnvironmentRecords](https://github.com/the-omega-institute/trureturing/blob/bfd5737539c696eedd4638da17d7f449339526cd/D5/S3/Quantum/EnvironmentRecords.lean#L24) | 记录 Gram 重叠及迹掉环境后的相干因子；不能仅由相同约化通道推断观察者已获哪些环境信息。 |
| [PhaseRecordRecoveryCriterion](https://github.com/the-omega-institute/trureturing/blob/bfd5737539c696eedd4638da17d7f449339526cd/D5/S3/ObserverMemory/CoherentReversal/PhaseRecordRecoveryCriterion.lean#L32) | 指定记录反转操作的单位模恢复与严格收缩条件；不是对所有扩大访问合同的恢复不可能性。 |

生成树与闭路机制属于已有数学。本文将其接到固定参考、共同端口、记录重叠及误差条件，并给出锚定相位场的明确完整坐标；这些普通推导没有被声明为新原创定理或已完成新增形式化。数学表示的存在、实际取得、强度可识别及有限误差恢复分别保留自己的前提。

## 3. 合法胶合与共同来源的经典修复

### 3.1 行为压缩何时保留局部到整体

以下为普通集合值数学推导，不把既有的行为商、层条件或有限容量定理重新标为原创结论，也不声称新增 Lean 核验。所有结论只针对指定观察、限制、覆盖及操作语言。基础所有者包括 RRO120.2、120.4、120.5 的行为商与残余记忆、RRO124.3–124.4 的匹配族与唯一胶合，以及既有严格响应下降的合法域纤维条件。

先区分表示运输与抽象基数相等。对满射行为商 $q:X\to Q$ 和边界 $e:X\to E$，$\ker e=\ker q$ 等价于存在满足 $D(e(x))=q(x)$ 的双射 $D:\operatorname{im}e\to Q$。这必须是与两份实际表示相容的双射；仅写两个集合抽象同构并不足够。例如 $X=\{0,1,2\}$，$q$ 合并 $0,1$，$e$ 合并 $0,2$，两者像都只有两个点，却具有不同的核，不存在上述交换的解码器。若只要求边界充分，条件仍是 $\ker e\subseteq\ker q$，由此定义的 $D$ 唯一且满射，但不要求单射。

固定拓扑空间上的集合值层 $P$、集合值预层 $Q$，以及逐开集满射的自然映射 $q:P\to Q$。自然性意为
$$
q_V(p|_V)=q_U(p)|_V\qquad(V\subseteq U).
\tag{TM.14}
$$
这里 $P(U)$ 是已经声明的实际整体；$Q(U)$ 可取局部任务的实际行为商，但只作逐处压缩并不能预设 $Q$ 仍是层。覆盖始终是所论开集的完整覆盖；一般 site 版本需要相应的覆盖与拉回数据，不从这份拓扑版本自动取得。

**商胶合判据。** 对固定覆盖 $U=\bigcup_iU_i$，$Q(U)\to\operatorname{Match}_Q(U_i)$ 是双射，当且仅当下面两项同时成立。

1. 对任意 $p,p'\in P(U)$，若所有 $i$ 都有 $q_{U_i}(p|_{U_i})=q_{U_i}(p'|_{U_i})$，则 $q_U(p)=q_U(p')$。
2. 对任意 $Q$ 的匹配族 $(b_i)_i$，存在 $p_i\in P(U_i)$，使 $q_{U_i}(p_i)=b_i$，且这些 $p_i$ 在完整交叠上真正相等。

第一项恰是压缩后的分离性。由 $q_U$ 满射，任意两份 $Q(U)$ 候选可取整体代表；自然性将局部相等翻译为第一项，继而给整体相等。反向则直接对整体代表的像使用 $Q$ 的分离性。

第二项恰是压缩后的胶合存在。匹配的 $P$ 代表由 $P$ 的层条件胶合成 $p$；自然性使 $q_U(p)$ 限制为全部 $b_i$。反向，若 $b\in Q(U)$ 胶合该匹配族，逐处满射给 $p\in P(U)$ 满足 $q_U(p)=b$，其限制就是所需匹配代表。这里代表提升的存在不提供实际取得算法或代价界。两项对全部所论覆盖成立，恰好使 $Q$ 成为层。

**压缩后失去唯一性的有限反例。** 在两点离散空间 $U=\{1,2\}$ 上令 $P(W)=\{0,1\}^W$。这是状态赋值层。整个 $U$ 的任务只读奇偶 $q_U(x_1,x_2)=x_1\oplus x_2$，每个单点和空集的任务均为常值；每处操作只有恒等。于是各 $Q(W)$ 都是该处任务的精确行为商，$q$ 自然且逐处满射。对单点覆盖，$Q(U)$ 有两个点，匹配族却只有一个：压缩后的限制不是单射。每处最小并不能取代全局任务被局部任务检测的条件。

**压缩后失去存在性的有限反例。** 在三点离散空间 $U=\{1,2,3\}$ 上仍取赋值层 $P(W)=\{0,1\}^W$，令 $q_W$ 记录 $W$ 内全部无序两点的异或；$|W|\le1$ 时值域为单点。令 $Q(W)$ 为该映射的实际像，限制按忘掉对应点对。于是 $q$ 自然且逐处满射。对三个二点集的覆盖，交叠是单点，所以八个二进制三元组全部匹配；整体实际像仅包含
$$
r_{12}\oplus r_{23}\oplus r_{31}=0
\tag{TM.15}
$$
的四个三元组。必要性由每个底层位出现两次；充分性取 $x_1=0,x_2=r_{12},x_3=r_{31}$，第三项由式(TM.15)给出。故这次 $Q$ 的限制单射但不满射，$(1,1,1)$ 无任何整体提升。这是确定性赋值的反例，不需要概率或量子假设。

### 3.2 合法域下降与压缩、拼接、演化的共同交换

先给拼接—演化交换的一组充分条件。设 $P$ 仅在所论覆盖上分离，$D\subseteq P$ 是子预层，$T:D\to P$ 是自然映射。若当前这份匹配的局部合法输入 $p_i\in D(U_i)$ 存在 $D(U)$ 中的胶合 $p$，则 $T_U(p)$ 限制为每个 $T_{U_i}(p_i)$。因此更新后匹配族已有整体，且由 $P$ 分离性唯一；这份结论不需要额外假定 $P$ 对所有匹配族均能胶合。$D$ 的分离性也已经由 $P$ 的分离性继承。

回到A卷第3.1节的 $P,Q$ 均为层及逐处满射自然 $q$。对每个操作 $a$，设 $D_a\subseteq P$ 为子层，$T_a:D_a\to P$ 自然。再要求合法域对 $q$ 饱和，并且后继的压缩读数在 $q$ 纤维上恒定：
$$
D_a(U)=q_U^{-1}(q_U(D_a(U))),\qquad
q_U(p)=q_U(p')\Longrightarrow
q_U(T_{a,U}p)=q_U(T_{a,U}p')
\quad(p,p'\in D_a(U)).
\tag{TM.16}
$$
这里所有原像都在当前实际 $P(U)$ 内取。标签、费用、停止与失败若属于指定任务，也须一并满足纤维不变；不能只降下后继而删去这些输出。定义实际合法像
$$
\bar D_a(U)=q_U(D_a(U)),\qquad
\bar T_{a,U}(q_U(p))=q_U(T_{a,U}(p)).
$$
饱和给商合法性双向保真，第二条件给更新良定，逐处满射给唯一性。

**商合法域仍为子层。** 自然性首先使 $\bar D_a$ 是 $Q$ 的子预层。给一份 $\bar D_a$ 匹配族 $(b_i)$，先在 $Q$ 中胶合为 $b$，再由逐处满射取整体代表 $p\in P(U)$，$q_U(p)=b$。每个 $b_i\in\bar D_a(U_i)$ 有合法代表；$p|_{U_i}$ 与其同 $q$ 像，饱和迫使 $p|_{U_i}\in D_a(U_i)$。由 $D_a$ 的层条件，这些实际匹配代表胶合为某 $p'\in D_a(U)$；$P$ 的分离性给 $p'=p$。于是 $b=q_U(p)\in\bar D_a(U)$。唯一性从 $Q$ 继承，证毕。

自然性还使 $\bar T_a$ 与限制交换：对合法代表 $p$，两边均为 $q_V(T_{a,V}(p|_V))$。因此原系统和商系统均满足合法胶合与演化交换。特别地，对匹配合法的实际代表 $(p_i)$，
$$
q_U\!\left(T_{a,U}(\operatorname{Glue}_P(p_i))\right)
= \operatorname{Glue}_Q\!\left(
\bar T_{a,U_i}(q_{U_i}(p_i))
\right).
\tag{TM.17}
$$
左边先取得实际整体、演化并压缩；右边在局部压缩后演化再胶合。各侧合法性与等式均已由同一组条件得到。对只有商局部族、尚无已获实际代表的情况，定理提供表示中的存在和唯一性，不提供执行一份全局准备的物理权限。

**有限过程的合法域仍可胶合。** 令空词 $D_\epsilon=P,T_\epsilon=\mathrm{id}$。按从左到右执行约定，若 $w$ 后接 $a$，则
$$
D_{wa}(U)=\{p\in D_w(U):T_{w,U}(p)\in D_a(U)\},\qquad
T_{wa,U}=T_{a,U}\circ T_{w,U}.
\tag{TM.18}
$$
若 $D_w,D_a$ 是子层且 $T_w$ 自然，则 $D_{wa}$ 是子层：局部匹配输入先在 $D_w$ 胶合，$T_w$ 的局部像在 $D_a$ 中且匹配，由 $D_a$ 的局部性得整体像合法。组合自然性逐式继承。若各一步满足式(TM.16)，归纳得 $D_w$ 对 $q$ 饱和、所有 $T_w$ 降下且交织；使用上一段即得每个有限词版本的式(TM.17)。不从所有有限词的结论直接断言无限执行可实现。

**共享资源反例。** 两点赋值层中，规定整体至多一个坐标为一，而单点零或一都合法。这个合法域是子预层，但单点合法族 $(1,1)$ 无合法整体，故不是子层。即使更新为恒等且与限制交换，两个局部各自能耗用一个资源也不能推出整体可同时耗用两个。这准确说明为何合法域的局部到整体不能删去。

### 3.3 局部相容的非实现性具有严格误差下界

在同一共同概率空间的三比特模型中，对每对 $ij$ 指定完美反相关目标律 $r_{ij}=\frac12\delta_{01}+\frac12\delta_{10}$。三份目标的单点重叠全都相同，却不能来自同一个实际联合律。这个非实现性还有精确的近似形式：
$$
\inf_{p\in\operatorname{Prob}(\{0,1\}^3)}
\max_{ij\in\{12,23,13\}}
 d_{\rm TV}(p_{ij},r_{ij})=\frac13.
\tag{TM.19}
$$

证明对每个具体三比特串，三个不等关系至多有两个成立。取任意共同联合律的期望，得
$$
\sum_{ij}p(X_i\ne X_j)\le2.
$$
故至少一对满足 $p(X_i\ne X_j)\le2/3$。目标律在该事件上概率一，而全变差至少等于任一事件的概率差，因此最大边缘全变差至少 $1/3$。

反向在六个非恒定比特串上取均匀联合律。每对边缘对 $00,11$ 各赋 $1/6$，对 $01,10$ 各赋 $1/3$。与目标律相比四个绝对差都是 $1/6$，全变差为其和的一半，即 $1/3$；三对同时达到这个值。上下界具有同一实际联合见证，故式(TM.19)成立。

这给出零重叠缺陷而严格正全局恢复缺陷的例子。不能仅以局部重叠误差为零，推出全局实现误差为零；定量恢复界还必须测量联合实现障碍，或加入足以排除此障碍的结构条件。它不是量子可实现性定理，不是因果时间或物理能量定律，也不据此宣称新的文献优先权。

### 3.4 同一个闭环残余控制拼接障碍与最坏恢复误差

定性所有者是主卷定理67.1的循环零奇偶与共同顶点见证、定理67.8的概率提升及定理67.12的时间边／空间边共同见证；`SimpleGraphCycleSpace.finite_graph_cycle_space` 已有有限简单图上的对应声明。以下循环判据直接使用该结果，保留其生成森林构造来说明与恢复见证的参数对应；新增连接在于全变差恢复目标、整体翻位对称化及有限 minimax 证书，不将定性判据重新声明为新的形式化成果。

设 $G=(V,E)$ 是有限简单无向图，$E\ne\varnothing$。为每条边任选一个端点顺序，并给定 $b_e\in\mathbb F_2$。边的目标联合律 $r_e^{b_e}$ 在满足 $x_u\oplus x_v=b_e$ 的两个位对上各赋概率 $1/2$。每个端点边缘都是均匀位，故不同边在公共顶点上的目标读数完全相容。所有候选恢复必须来自同一整体位配置空间 $\mathbb F_2^V$ 上的概率律 $p$。令
$$
v_e(x)=\mathbf1_{x_u\oplus x_v\ne b_e},\qquad
\alpha(G,b)=\min_{p\in\operatorname{Prob}(\mathbb F_2^V)}
\max_{e\in E}d_{\rm TV}(p_e,r_e^{b_e}).
$$
有限概率单纯形紧而损失连续，故这里的最小值确实取到。对任意边，目标律在违反事件上的概率为零，因而 $d_{\rm TV}(p_e,r_e^{b_e})\ge\mathbb E_pv_e$。把整体律与其全部位同时翻转后的像平均，得 $p^{\rm sym}=(p+\iota_*p)/2$，其中 $\iota(x)=x\oplus\mathbf1$。这不改变任何违反概率。对每个边缘，同一异或扇区内两位对的概率相等；若违反概率为 $\eta_e$，则满足扇区内每对概率为 $(1-\eta_e)/2$，违反扇区内每对概率为 $\eta_e/2$。直接计算得 $d_{\rm TV}(p_e^{\rm sym},r_e^{b_e})=\eta_e$。因此
$$
\boxed{
\alpha(G,b)
=\min_p\max_e\mathbb E_pv_e
=\max_{\lambda\in\Delta(E)}\min_{x\in\mathbb F_2^V}
\sum_{e\in E}\lambda_ev_e(x).
}
\tag{TM.20}
$$
第二等号是有限零和博弈的 minimax 定理，也可由有限线性规划对偶得到：$\max_e$ 等于对边权单纯形 $\Delta(E)$ 最大化，双线性期望满足有限 minimax；固定 $\lambda$ 后，对概率律的最小值在某个确定配置取得。这是成熟有限对偶的应用，不宣称新的对偶定理。左侧要求同一 $p$ 同时给出所有边缘；右侧寻找一份权重证书，使每个整体配置都必须付出相应的违反量。两侧最优值都取到，不把逐边单独可达的目标拼成虚构共同来源。

更具体地，一份共同概率律 $p\in\operatorname{Prob}(\mathbb F_2^V)$ 和归一化非负边权 $\lambda\in\Delta(E)$ 若满足
$$
\mathbb E_pv_e\le t\quad(\forall e),\qquad
\sum_e\lambda_ev_e(x)\ge a\quad(\forall x),
$$
就认证 $a\le\alpha(G,b)\le t$，且同一份 $p^{\rm sym}$ 的最大边缘误差不超过 $t$；当 $a=t$ 时，该联合律与边权共同认证并达到最优值。若把每个二元边差分 $\delta x$ 嵌入实向量空间并取凸包
$$
\mathcal C_G=\operatorname{conv}\{\delta x:x\in\mathbb F_2^V\}\subset[0,1]^E,
$$
则还得到
$$
\boxed{\alpha(G,b)=\min_{z\in\mathcal C_G}\|z-b\|_\infty.}
\tag{TM.21}
$$
因为 $z_e=\mathbb E_p(\delta X)_e$，而 $b_e$ 取零或一，使 $|z_e-b_e|=\mathbb E_pv_e$。这里凸组合用实数概率，边标签组合用二元域运算；两种运算没有混同。于是同一整体实现集合既给出关系相容条件，也给出明确的凸几何恢复距离。

以下三件事等价：$\alpha(G,b)=0$；存在 $x\in\mathbb F_2^V$ 满足全部边约束；每条简单回路 $C$ 满足
$$
\bigoplus_{e\in C}b_e=0.
\tag{TM.22}
$$
若误差为零，则每条边约束以概率一成立；边数有限，全部约束同时成立的事件仍概率一，所以有确定性满足配置。反向将任意满足配置与其整体翻位各取一半，即同时实现每条目标律。满足配置沿回路求异或给式(TM.22)。若所有回路异或为零，在各连通分支选根及生成树，固定根位为零，沿树边累加 $b_e$ 给各顶点位；每条非树边对应的基本回路保证其边约束也成立。孤立顶点可任意赋位。

顶点换位 $x'_v=x_v\oplus g_v$ 同时运输边标签为 $b'_{uv}=b_{uv}\oplus g_u\oplus g_v$。该双射保持每份对应联合律的边缘全变差，故 $\alpha(G,b')=\alpha(G,b)$；所有闭环异或也保持。零误差因此仅依赖边标签模顶点换位的类别；非零误差的数值还依赖图和所选边观察合同，不能只由“存在一条非平凡回路”决定。

对单一 $m$ 边循环图 $C_m$，$m\ge3$，若全部边标签异或为零，误差为零；若异或为一，则
$$
\boxed{\alpha(C_m,b)=1/m.}
\tag{TM.23}
$$
下界：每个配置至少违反一条边，对所有边赋权 $\lambda_e=1/m$ 即由式(TM.20)得到 $1/m$；也可直接对违反数取期望。上界：对每条指定边 $e$，只将该边目标标签翻转，得到闭环异或为零的标签族，故存在恰好违反原来第 $e$ 条边的配置。均匀选择这 $m$ 个配置，并对每个配置与其整体翻位各取一半，构成同一整体联合律。每条边违反概率恰为 $1/m$，而整体翻位对称性使边缘全变差也恰为 $1/m$。三边全反相关正是式(TM.19)；偶数边全反相关则可精确交替赋值，误差为零。

**多个回路的联合障碍不能逐圈最优化后拼接。** 每个非零循环 $C$ 都给下界 $1/|C|$，但这些下界的最大值未必等于整体最优值。在完全图 $K_5$ 上取所有边标签为一；任意二分至多切开 $2\cdot3=6$ 条边，十条边至少违反四条，均匀边权给 $\alpha\ge2/5$。均匀选择十个两元素顶点集作为值为一的集合，再整体翻位对称化；每条边恰被其中六个集合切开，故全部边的违反概率与全变差同时为 $2/5$。因此
$$
\alpha(K_5,\mathbf1)=2/5>1/3.
\tag{TM.24}
$$
最短非零循环只有三边，却不能独自认证这份精确整体距离。障碍来自所有局部要求对同一个赋值的共同约束。

这份闭环异或也可以直接实现为离散运输：在每个顶点置一个位纤维，沿边 $e$ 执行 $s\mapsto s\oplus b_e$；逆向执行同一翻位，确为可逆运输。回路作用是 $s\mapsto s\oplus\bigoplus_{e\in C}b_e$。存在与全部边运输一致的全局位截面，当且仅当每条闭环的运输都是恒等；对一条指定闭环，它改变纤维位，当且仅当该闭环的标签异或非零。若根纤维位初始已知，且允许后续读取纤维位，则零次与一次非零闭环执行回到同一可见顶点，却具有不同未来响应。在当前可见配置、全部可访问侧信息及后续实验规则均相同，且未来响应仅由这些量与工作记忆决定的实现合同下，两段历史必须对应不同工作记忆状态；一位足以实现本模型的纤维运输。若访问次数、时钟或完整已获档案已经区分两段历史，则只能据此要求整体有效状态保留该区别，不能另行推出额外内部记忆位的下界。

这里没有假定物理时间、曲率、三维嵌入或量子规律。相同的明确边运输可以被组织为局部拼接问题，也可以被组织为闭环接续问题；二者共享的是式(TM.22)中的实际组合残余。若没有读取纤维位的权限，或已把纤维位放入可见配置，上述内部记忆下界的任务或固定可见条件就改变。一般概率恢复、一般相位干涉和一般时空几何不由这个二元模型自动获得同一误差公式。

尤其，非零闭环残余不妨碍过程合法执行。取公平位 $Z$，令三次连续操作的状态位为 $X_0=Z,X_1=Z,X_2=Z,X_3=Z\oplus1$，其相邻边标签分别为 $0,0,1$，每个相邻目标联合律都精确实现。只有再要求末次访问与初次访问共享同一个隐藏变量 $X_3=X_0$，才产生三角拼接障碍。因此上述 $1/3$ 或 $1/m$ 约束的是“一顶点一个共同变量”的恢复合同，不能未经论证用于允许同一可见顶点拥有不同访问状态的时间过程。记录访问次数或纤维状态，正是在保留这个区别。

**档案纤维不能被对称化偷偷扩大。** 式(TM.20)针对允许全部整体位配置及其概率混合的来源类。限制到固定实际档案纤维时，事件概率仍给全变差下界，但上界构造需要证明整体翻位和混合仍在该纤维内合法。单边、$b_e=0$ 而档案只允许配置 $00$ 时，违反概率为零，但唯一边缘 $\delta_{00}$ 到公平相等目标 $(\delta_{00}+\delta_{11})/2$ 的全变差为 $1/2$。因此“能满足关系”与“能准备所指定的公平联合律”不同；实际档案、已有锚点及制备权限必须随模型一起运输，不能只保留循环标签。

### 3.5 同一循环的合法近似与有符号精确恢复

这里直接使用恢复几何卷定理1.2的有限字典 $\ell^1$ 对偶、命题1.3的对称原子凸包解释，以及主卷第119节逐原子对偶约束所给的支撑／符号判据。原子由一份完整位配置的全部边缘指示数组组成，目标由全部公平边目标组成；也可附总质量一的坐标。若原子和目标位于有限维空间 $Y$，对偶定理的状态空间取 $Y^*$，字典取原子评价泛函，目标取目标数组的评价泛函，价格均为一。下面履行的是这一成熟机制在循环共同边缘问题中的具体构造与最优值计算，不把一般对偶重新算作新增理论。

固定上一节的循环图 $C_m$，$m\ge3$，并假定边目标标签的总异或为一。合法概率联合律不能精确给出全部公平边目标，其最优最坏边误差为 $1/m$。现在改变数学恢复合同：允许实有符号权重 $\nu:\mathbb F_2^V\to\mathbb R$，要求总质量一，每条边的推前严格等于 $r_e^{b_e}$，并最小化系数总量
$$
\Gamma(\nu)=\sum_x|\nu(x)|.
$$
这是一份有限线性恢复表示；负系数不代表可以准备负概率来源。它回答同一局部目标需要多少有符号系数代价，与上一节合法概率逼近的距离是两个不同优化问题。

令 $q$ 为不超过 $m$ 的最大奇数，即 $q=m$ 当 $m$ 为奇数、$q=m-1$ 当 $m$ 为偶数。则
$$
\boxed{
\min_{\nu:\,\nu_e=r_e^{b_e}\ \forall e}\Gamma(\nu)
=\frac{q+1}{q-1},\qquad
\min_\nu\sum_x\max\{-\nu(x),0\}
=\frac1{q-1}.
}
\tag{TM.25}
$$
式中的可行权重同时满足总质量一；由于存在边且目标边质量一，该总质量也由任意一份边推前约束蕴含。第二个最小值使用同一可行类。

**对偶下界。** 对每个完整位配置，令 $N(x)=\sum_ev_e(x)$。沿整个循环求异或，每个顶点位出现两次，因此 $N(x)$ 为奇数，且 $1\le N(x)\le q$。于是
$$
F(x)=\frac{q+1-2N(x)}{q-1}
\tag{TM.26}
$$
在全部实际配置上满足 $|F(x)|\le1$。若有符号权重精确恢复每条边目标，每条违反事件的有符号质量为零，故 $\sum_x\nu(x)N(x)=0$。结合总质量一，得到
$$
\frac{q+1}{q-1}
=\sum_x\nu(x)F(x)
\le\sum_x|\nu(x)|.
$$
这是在同一个整体配置集合上认证的对偶证书，不把边上分别成立的证书当成共同见证。

证书也能写成对给定边缘数据的线性读数：在每条边定义 $f_e(a,c)=(q+1)/(m(q-1))-2\mathbf1_{a\oplus c\ne b_e}/(q-1)$，则 $F(x)=\sum_ef_e(x_u,x_v)$。全部目标边缘上的总读数是 $(q+1)/(q-1)$，而每个实际整体原子上的绝对读数至多一。这正是有符号原子恢复中的同一份对偶证书，证书的各分量不需要被解释为概率。

**同一有符号见证的达到性。** 对任意满足 $1\le k\le m$ 的奇数 $k$，均匀选择一个大小为 $k$ 的边集 $S$。希望只违反这些边，等价于要求顶点差分为 $b\oplus\mathbf1_S$。其循环异或为零，已有循环判据给一个顶点配置；将它与整体翻位各取一半。再对全部 $S$ 平均，得到共同概率律 $p_k$。它只支持 $N(x)=k$，整体翻位对称，每条边的违反概率都是 $k/m$，因此
$$
(p_k)_e=(1-k/m)r_e^{b_e}+(k/m)r_e^{1-b_e}.
$$
取
$$
\nu_* =\frac{q}{q-1}p_1-\frac1{q-1}p_q.
\tag{TM.27}
$$
总质量为一；每条边的违反扇区系数恰为零，满足扇区系数恰为一，故全部边目标同时精确恢复。$q\ge3$，两份概率律的支持分别位于 $N=1$ 与 $N=q$，彼此不交，遂有 $\Gamma(\nu_*)=(q+1)/(q-1)$。任意总质量一的实有符号权重都满足负质量 $N_-=(\Gamma-1)/2$，从而式(TM.25)的两项最小值同时得到。

三边全反相关时，六个非恒定位串各赋 $1/4$，两个恒定位串各赋 $-1/4$，总质量一、每对边缘恰为公平反相关，系数总量为二、负质量为 $1/2$。这个确切表示并没有产生合法的三比特概率律。四边总异或一的循环也有最小系数总量二，而合法概率误差变成 $1/4$；三边对应误差为 $1/3$。所以同一份有符号系数代价值不足以确定合法概率误差；二者分别计量该共同关系中的精确线性表示成本与合法概率恢复距离。

**接触层不等于唯一系数。** 对任意最优 $\nu$，各项 $|\nu(x)|-\nu(x)F(x)$ 非负且总和为零，所以正权重只能位于 $N(x)=1$ 层，负权重只能位于 $N(x)=q$ 层，中间层权重必须为零。这与主卷第119节的接触证书机制相同，但没有给出接触原子的线性独立性，不能由此断言最优系数唯一。实际上，对三边全反相关的上述见证 $\nu_0$，全部
$$
\nu_t(x)=\nu_0(x)+t(-1)^{x_1+x_2+x_3},\qquad |t|\le1/4,
\tag{TM.28}
$$
都是不同的最优见证。三阶奇偶项对任何两位边缘求和为零，对全空间求和也为零；所给 $t$ 范围保留六个非恒定串的非负号和两个恒定串的非正号，所以所有边缘、总质量及总绝对系数二均保持。由同一边界可恢复目标，不等于能够识别唯一的内部有符号实现。

整个结论使用自由的全部位配置来源及其线性表示。若实际档案、锚点或准备权限删去部分配置，下界证书仍对保留配置成立，但达到性必须重新提供合法支撑；甚至精确有符号表示的可行性也需重验。这里运用成熟有限 $\ell^1$ 恢复对偶，没有把负系数解释为物理负概率、负时间或量子态，也不由此宣称文献原创或新增 Lean 核验。

### 3.6 固定档案的 Hoffman 纤维修复与尺度常数

边界读数接近一份可实现目标时，能否只小幅调整完整共同来源，就使全部边界读数同时等于该目标？对固定有限档案，这由成熟的 Hoffman 多面体误差界回答。结论是到目标纤维的距离界，适用于同一个档案上的全部可行目标；其常数依赖档案约束、观察映射和误差范数。把档案或上下文数量不断扩张以后，还需检验这些常数能否统一控制。

#### 3.6.1 成熟供应：参考多面体上的统一等式误差界

令 $R\subseteq\mathbb R^N$ 为固定非空多面体，$C:\mathbb R^N\to\mathbb R^D$ 为固定线性映射，源空间与目标空间分别指定范数。参考多面体版本的 Hoffman 界给出有限常数 $\widetilde H(C\mid R)\ge0$，使
$$
\operatorname{dist}\bigl(x,C^{-1}(d)\cap R\bigr)
\le \widetilde H(C\mid R)\,\|d-Cx\|
\qquad\forall d\in C(R),\quad\forall x\in R.
\tag{TM.67}
$$

这里距离使用源范数，右侧剩余量使用目标范数。Javier Peña、Juan C. Vera、Luis F. Zuluaga 的 *New characterizations of Hoffman constants for systems of linear constraints*，[arXiv:1905.02894v2](https://arxiv.org/pdf/1905.02894v2)，在第2.2节命题5（PDF第9页）给出同时包含不等式、等式和参考多面体的统一界，并给出相应常数的紧性；取不等式矩阵为空，即为第10页式(17)的上述形式。第11页定义原文记号 $\widetilde H(C\mid R)=H([],C\mid R)$，并再次说明式(17)的紧性。本节沿用纯等式版本的 $\widetilde H$，式(TM.70)仅将所指定映射与参考多面体下的值简记为 $H_A$，没有把原文常数改成另一份泛用 $H$。第4页明确说明，未另作限制的结果适用于任意范数。因而本节直接使用该成熟结果，并非另立新的普遍误差界。

两个量词尤其关键：同一常数对全部 $x\in R$ 和全部可行右端 $d\in C(R)$ 同时成立；可行性确保目标纤维非空。$R$ 可以是低维多面体，并不要求其在环境空间有内点。

#### 3.6.2 代入固定共同档案与上下文边缘

固定有限非空的合法完整档案集合 $A$、有限非空的上下文集合 $E$。每个上下文 $e\in E$ 有有限非空读数集合 $B_e$ 和固定读数映射 $\pi_e:A\to B_e$。这里全部上下文读取同一份档案；动作、历史、来源或共享变量的合法性已经包含在 $A$ 及其读数定义中。暂定所有支撑于 $A$ 的概率混合都是允许的来源律，令
$$
\begin{aligned}
\Delta_A&=\{p\in\mathbb R^A:p(a)\ge0,\ \sum_{a\in A}p(a)=1\},\\
(M_ep)(b)&=\sum_{a:\,\pi_e(a)=b}p(a),\qquad
Mp=(M_ep)_{e\in E}.
\end{aligned}
\tag{TM.68}
$$

边缘映射按同一公式线性延拓到整个 $\mathbb R^A$。在源空间和目标乘积空间上分别指定
$$
\|v\|_{\rm src}=\tfrac12\sum_{a\in A}|v(a)|,\qquad
\|z\|_{\rm obs}=\max_{e\in E}\tfrac12\sum_{b\in B_e}|z_e(b)|.
\tag{TM.69}
$$

二者都是其整个有限维空间上的范数。对概率律之差，源范数就是总变差距离；目标范数就是全部上下文总变差中的最大值。

取任意当前来源律 $q\in\Delta_A$ 与真实可行目标 $y\in M(\Delta_A)$，记目标纤维 $F_y=\{p\in\Delta_A:Mp=y\}$，剩余量 $\delta(q,y)=\max_{e\in E}\operatorname{TV}(M_eq,y_e)$。式(TM.67)取 $R=\Delta_A$、$C=M$、$x=q$、$d=y$，直接给出
$$
\boxed{
\min_{p\in\Delta_A,\,Mp=y}\operatorname{TV}(p,q)
\le H_A\max_{e\in E}\operatorname{TV}(M_eq,y_e),
\qquad q\in\Delta_A,\ y\in M(\Delta_A),
}
\qquad H_A=\widetilde H(M\mid\Delta_A)<\infty.
\tag{TM.70}
$$

下标 $A$ 省略了已经固定的 $M$ 和两份范数，不表示常数只由档案数量决定。$\Delta_A$ 紧，$F_y$ 是其中非空闭集，总变差是连续函数，故最小值确实由某个 $p_*=p_*(q,y)$ 达到。又因任意两份概率律的总变差至多为一，该最小值还不超过 $\min\{1,H_A\delta(q,y)\}$。至此已给出完整的应用证明：成熟定理供应统一常数，指定范数将其转为式(TM.70)，紧性供应达到最小值的同一个修复来源律。

这份修复保留合法档案支持，并让所有上下文同时达到 $y$。它不逐边选择互不相干的来源。若实际概率协议另有限制，允许律只是 $\Delta_A$ 的某个固定非空多面体 $R$，应以该 $R$ 替换参考多面体并重新计算常数；不能先在全部混合中取得修复，再省略原协议的约束。

#### 3.6.3 同一个修复来源律控制全部有界读数和随机后处理

选定上述某个最近修复律 $p_*$ 后，对任意 $f:A\to[0,1]$，都有
$$
\left|\mathbb E_{p_*}f-\mathbb E_qf\right|
\le\operatorname{TV}(p_*,q)
\le\min\{1,H_A\delta(q,y)\}.
\tag{TM.71}
$$

证明如下。令 $v=p_*-q$，则 $\sum_av(a)=0$。正部与负部的总质量相等，均为 $\tfrac12\sum_a|v(a)|=\operatorname{TV}(p_*,q)$。由 $0\le f\le1$，$\sum_af(a)v(a)$ 的上下界分别由正部与负部质量控制，得到式(TM.71)。这对全部 $f$ 同时成立，使用的是已经选定的同一个 $p_*$，无需为不同任务分别换来源。

若后续观察由一个固定随机核 $K(b\mid a)$ 描述，其中输出集合 $B$ 有限，$K(b\mid a)\ge0$ 且 $\sum_bK(b\mid a)=1$，则同一修复还满足
$$
\begin{aligned}
\operatorname{TV}(Kp_*,Kq)
&=\tfrac12\sum_b\left|\sum_aK(b\mid a)(p_*(a)-q(a))\right|\\
&\le\tfrac12\sum_{b,a}K(b\mid a)|p_*(a)-q(a)|\\
&=\operatorname{TV}(p_*,q)
\le\min\{1,H_A\delta(q,y)\}.
\end{aligned}
\tag{TM.72}
$$

因此，一旦某项后续协议确实由同一档案上的随机核实现，其输出律也受同一界控制。此处比较的是原来源律与所选修复来源律；若未来过程还依赖未进入 $A$ 的变量，就没有取得这样的共同核，不能直接套用本式。

式(TM.70)的取得对象是一份纤维内的邻近来源律。它没有断言该来源唯一，也没有构造只依赖 $y$ 的固定解码器、线性右逆或执行算法。即使 $\delta(q,y)=0$，结论也只保证 $q\in F_y$。例如 $A=\{a_0,a_1\}$ 且所有读数恒定时，$\delta(q,y)$ 对所有 $q$ 都为零，而 $\delta_{a_0}$ 与 $\delta_{a_1}$ 对任务 $f=\mathbf1_{\{a_1\}}$ 的答案仍不同。因此，邻近纤维修复不是根据边界识别某个未知真实来源的保证。

#### 3.6.4 与仓内固定仿射剩余量界的供应范围

固定快照 `237012b49d0d4729a86f7e9dd252d94df1de8dd0` 的 `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md:6418`，定理37.7已经给出固定概率多面体 $\mathcal D$ 上的顶点间隙界：若 $r$ 为固定非负仿射函数，非空零集为 $F$，且存在正剩余量顶点，令 $\gamma$ 为最小正顶点剩余量，则
$$
\operatorname{dist}_{\rm TV}(q,F)
\le\min\{1,r(q)/\gamma\}.
\tag{TM.73}
$$

其证明写 $q$ 为顶点凸组合，把具有正剩余量的顶点质量移到某个 $F$ 中的合法点；非负仿射性保证这部分总质量至多为 $r(q)/\gamma$。若全部顶点的剩余量为零，则 $F=\mathcal D$，无需定义正间隙。该卷在第6429行明确保留了固定多面体、仿射性、非负性以及存在性结论的边界。

式(TM.70)使用的 $\|Mq-y\|_{\rm obs}$ 一般是凸分段线性函数，未必仿射；而且目标 $y$ 遍历整个可行像。最简单地，在 $\Delta_{\{0,1\}}$ 上写 $q=(1-t,t)$，观察 $t$，指定目标 $a\in(0,1)$，剩余量为 $|t-a|$，目标纤维位于线段内部。一个非负仿射函数若在这个内部点为零，就在整条线段上为零，不能把该单点纤维写成其零集。因此，不能直接将定理37.7的固定仿射顶点证明当成对所有 $y$ 的式(TM.70)。这里的统一于右端的供应来自所引命题5及式(17)，已有顶点界仍在自身条件下成立。

#### 3.6.5 星图档案：最优稳定常数恰为叶数

固定整数 $n\ge1$，取中心为 $0$、叶为 $1,\ldots,n$ 的星图。每个顶点有二值状态，合法完整档案限定为全零及恰有一片叶取值一：
$$
A_n=\{\mathbf0,e_1,\ldots,e_n\}\subseteq\{0,1\}^{\{0,1,\ldots,n\}},\qquad
(e_i)_0=0,\quad(e_i)_j=\mathbf1_{\{i=j\}},\qquad
\pi_i(a)=(a_0,a_i).
\tag{TM.74}
$$

中心在全部档案中恒为零，观察第 $i$ 条边的二元边缘。对任意 $p\in\Delta_{A_n}$，记 $p_i=p(e_i)$、$p_0=p(\mathbf0)=1-\sum_{i=1}^np_i$。按二元读数 $00,01,10,11$ 的次序，$M_ip=(1-p_i,p_i,0,0)$。于是整个边界恰好确定 $p_1,\ldots,p_n$，再由归一化确定 $p_0$；$M$ 在这个档案单纯形上是单射。其可行边缘必须满足 $p_i\ge0$ 与 $\sum_ip_i\le1$，不能把各边任意 Bernoulli 参数都当作共同可行数据。

先给锐下界。取 $q_n=n^{-1}\sum_{i=1}^n\delta_{e_i}$，目标 $y^{(0)}=M\delta_{\mathbf0}$。这份目标明确由合法共同来源实现。目标的每条边都以概率一读到 $00$，故任意 $p\in F_{y^{(0)}}$ 必须满足所有 $p_i=0$，即目标纤维只有 $\delta_{\mathbf0}$。于是
$$
\min_{p\in F_{y^{(0)}}}\operatorname{TV}(p,q_n)=1,\qquad
\operatorname{TV}(M_iq_n,y_i^{(0)})=\frac1n\quad(1\le i\le n),\qquad
\delta(q_n,y^{(0)})=\frac1n.
\tag{TM.75}
$$

因此，任何对全部可行 $y$ 与全部 $q$ 有效的常数都必须至少为 $n$。

再给匹配的全局上界。取任意 $p,q\in\Delta_{A_n}$，令 $\Delta_i=p_i-q_i$。归一化给 $p_0-q_0=-\sum_{i=1}^n\Delta_i$，而每条边的总变差等于 $|\Delta_i|$，所以
$$
\begin{aligned}
\operatorname{TV}(p,q)
&=\tfrac12\left(\left|\sum_{i=1}^n\Delta_i\right|+\sum_{i=1}^n|\Delta_i|\right)\\
&\le\sum_{i=1}^n|\Delta_i|
\le n\max_{1\le i\le n}|\Delta_i|
=n\max_{1\le i\le n}\operatorname{TV}(M_ip,M_iq).
\end{aligned}
\tag{TM.76}
$$

对任意可行目标 $y$，取其唯一来源 $p\in\Delta_{A_n}$，式(TM.76)即给式(TM.70)中常数 $n$ 的有效性。连同式(TM.75)的达到实例，得到
$$
\boxed{
H_n^{\rm opt}
:=\inf\{H\ge0:\operatorname{dist}_{\rm TV}(q,F_y)
\le H\max_i\operatorname{TV}(M_iq,y_i)\ \text{对全部可行 }y\text{ 与全部 }q\text{ 成立}\}
=n.
}
\tag{TM.77}
$$

这是这族明确档案与指定范数下的锐常数计算。每个固定 $n$ 的修复稳定界都有限，但当档案和边界同时扩张时，最优常数无界。星图没有环，边界映射在合法来源上还具有唯一逆，仍不能由这些事实推出独立于 $n$ 的最大边误差控制。

这个增长结论也依赖误差怎样汇总。若将目标误差改成所有边总变差之和，式(TM.76)直接给常数一，式(TM.75)仍达到该界。改变范数改变了所衡量的预算；不能将总误差与最大单边误差的常数混作同一个尺度稳定性结论。

#### 3.6.6 纤维修复的适用边界

统一目标必须属于同一固定像 $M(\Delta_A)$。每个上下文分别给出概率律，甚至交叠处边缘一致，都不自动提供共同实现。例如三个二值变量的三条边都要求两端总是相反，可以让每条边及所有单点边缘分别一致，却不存在三个比特两两不同的完整档案。这样的受挫理想目标不在全局边缘像中，目标纤维为空，式(TM.70)没有可修复对象。先改目标、放宽合法档案或另行最小化不可行残差，都会形成另一个问题，不能冒充原纤维已经修复。

全部修复系数是合法概率 $p(a)\ge0$。若某份有符号向量只能在线性张成中实现目标，它尚未提供 $\Delta_A$ 中的可行性见证；原子表示或有符号系数恢复的代价界不能替代这里的概率约束。本文也没有把到纤维的邻近性转成一项免费可执行的制备：取得可行目标的共同来源、求取修复律、验证约束及执行新协议，各需相应输入与资源。

由此，固定档案上的“体／边”可以通过一份明确的修复关系连接：边界剩余量控制移到真实目标纤维所需的整体改变；选定同一修复以后，全部指定有界任务和合法随机后处理共享这一控制。跨层级、跨尺度继续使用时，仍须同时运输共同来源、可行像与常数。成熟的有限维修复定理和式(TM.77)的尺度计算共同说明了这些条件各自承担的工作。

#### 3.6.7 不可行理想目标：到最优共同来源的统一误差界

即使理想局部律没有共同实现，仍可另行研究“距离它最近的合法共同来源”。继续固定上述 $A,E,B_e,\pi_e,M$ 和两份范数，允许目标 $r=(r_e)_{e\in E}\in\prod_e\Delta_{B_e}$ 不属于 $M(\Delta_A)$。定义
$$
\delta_r(q)=\max_{e\in E}\operatorname{TV}(M_eq,r_e),\qquad
\alpha_r=\min_{q\in\Delta_A}\delta_r(q),\qquad
\operatorname{Opt}_r=\{p\in\Delta_A:\delta_r(p)=\alpha_r\}.
\tag{TM.78}
$$

有限维总变差与有限最大值都是连续函数，$\Delta_A$ 非空紧，故 $\alpha_r$ 达到，$\operatorname{Opt}_r$ 为非空紧集。所有 $r_e$ 都是概率律，因而 $0\le\alpha_r\le1$。又因 $M(\Delta_A)$ 紧，$\alpha_r=0$ 当且仅当 $r\in M(\Delta_A)$；不可行目标具有严格正的最小剩余量。

令有限行指标集为 $\mathcal I=\{(e,s):e\in E,\ s\in\{-1,1\}^{B_e}\}$。对任意实向量 $z$，每个坐标选择其符号即得 $\sum_b|z_b|=\max_s\sum_bs_bz_b$。因此可定义与 $r$ 无关的固定矩阵 $\widetilde A$，以及依赖 $r$ 的右端 $b_r$：
$$
\begin{aligned}
\delta_r(q)
&=\max_{(e,s)\in\mathcal I}\tfrac12s^{\mathsf T}(M_eq-r_e),\\
\widetilde A_{(e,s)}&=\tfrac12s^{\mathsf T}M_e,\qquad
(b_r)_{(e,s)}=\alpha_r+\tfrac12s^{\mathsf T}r_e.
\end{aligned}
\tag{TM.79}
$$

矩阵有 $\sum_e2^{|B_e|}$ 行；这里用有限符号展开证明多面体性，不附带有效率的计算保证。由式(TM.79)，全部行不等式等价于 $\delta_r(p)\le\alpha_r$；对 $p\in\Delta_A$，最优值的定义又给反向不等式，故
$$
\operatorname{Opt}_r
=\{p\in\Delta_A:\widetilde A p\le b_r\}.
\tag{TM.80}
$$

这一多面体非空已有紧性保证，所以 $b_r$ 是固定系统 $\widetilde A p\le b$、$p\in\Delta_A$ 的可行右端。

现在用源范数 $\tfrac12\|\cdot\|_1$，并在行剩余量空间 $\mathbb R^{\mathcal I}$ 使用 $\ell^\infty$ 范数。向量 $w$ 到非负正交锥的 $\ell^\infty$ 距离为 $\|(-w)_+\|_\infty$：逐坐标将负值截断为零即可达到，任意非负候选在相应坐标上的误差又至少为该负值的绝对值。因此，所引命题5取等式矩阵为空时的剩余距离，正好是 $\|(\widetilde A q-b_r)_+\|_\infty$。对任意 $q\in\Delta_A$，它进一步满足
$$
\begin{aligned}
\|(\widetilde A q-b_r)_+\|_\infty
&=\max_{(e,s)\in\mathcal I}
\left(\tfrac12s^{\mathsf T}(M_eq-r_e)-\alpha_r\right)_+\\
&=\bigl(\delta_r(q)-\alpha_r\bigr)_+
=\delta_r(q)-\alpha_r.
\end{aligned}
\tag{TM.81}
$$

最后一步使用 $q$ 属于同一可行来源集，故其目标值不小于最优值。这也是为什么不能把任意有符号输入代入该式最后一行。

参考多面体版本的纯不等式 Hoffman 界因此给出
$$
\boxed{
\min_{p\in\operatorname{Opt}_r}\operatorname{TV}(p,q)
\le C_{A,M}\bigl(\delta_r(q)-\alpha_r\bigr)
\quad\forall r\in\prod_e\Delta_{B_e},\quad\forall q\in\Delta_A,
}
\qquad C_{A,M}=H(\widetilde A\mid\Delta_A)<\infty.
\tag{TM.82}
$$

式(TM.82)的 $H(\widetilde A\mid\Delta_A)$ 是这里对所引混合约束常数 $H(\widetilde A,[]\mid\Delta_A)$ 的纯不等式简记；它与式(TM.67)取不等式矩阵为空的纯等式记号 $\widetilde H(C\mid R)$ 分别使用自己的约束类型。

左侧最小值由 $\operatorname{Opt}_r$ 的紧性达到。常数的统一性来自成熟定理对全部可行不等式右端的量词：$r$ 和 $\alpha_r$ 只改变 $b_r$，参考多面体、矩阵及两份范数均未改变。因此该常数与 $r$ 无关。式(TM.78)—(TM.82)给出的是该成熟定理的有限多面体应用，不是新的普遍误差界。

一个具体不可行例子仍来自式(TM.74)的 $n=2$ 档案。让两条理想边都以概率一读到 $01$。合法来源必须满足 $p_1+p_2\le1$，而剩余量为 $\delta_r(p)=\max\{1-p_1,1-p_2\}=1-\min\{p_1,p_2\}$。所以 $\alpha_r=1/2$，唯一最优来源是 $p_*=(\delta_{e_1}+\delta_{e_2})/2$。理想目标仍没有精确共同实现；最优来源留下不可消去的目标剩余量 $1/2$。若 $q=\delta_{\mathbf0}$，其剩余量为一，超出最优值的部分为 $1/2$，到最优来源的总变差为一。这里的“最优”始终相对于固定合法档案和所声明的最大边误差。

选定式(TM.82)的某个最近最优来源后，式(TM.71)、(TM.72)的同一证明继续控制全部 $[0,1]$ 有界任务和共同随机核，只需将右侧换为 $\min\{1,C_{A,M}(\delta_r(q)-\alpha_r)\}$。这将目标剩余量分成相对于该档案无法减少的 $\alpha_r$，以及可以通过移向最优来源减少的超额部分；即使超额为零，也不抹去正的 $\alpha_r$。

这个结论逼近某个最优共同来源，不识别一份预先指定的隐藏整体，也不保证唯一解码器或高效取得最优值、常数与修复律。它的跨规模常数仍可增长：允许的目标包含式(TM.75)的可行全零目标，此时 $\alpha_r=0$，该实例已迫使任何对应星图档案的统一常数 $C_{A_n,M}$ 至少为 $n$。非线性准入、无限档案或无限上下文不自动具有上述有限多面体结构，须另行供应相应误差界。

## 4. 切面、动态规划与完整历史流

### 4.1 动态规划的合法切面、继续接口与资源几何

以下是有限计算模型中的普通数学推导；不将程序的调度参数解释为物理时钟。固定有限 DAG $G=(V,E)$，边 $u\to v$ 表示 $v$ 的计算必须读取 $u$。每个节点有值域、确定性计算规则、结果存储大小 $s_v>0$ 和执行时长 $t_v>0$。源输入、静态参数、允许的共同输入族及指定输出集合 $O$ 均属于模型；已经取得的完整档案不因丢弃工作缓存而被宣称消失。

先限定每个节点只执行一次、所有声明节点都须执行、前驱值作为不可重新取得的黑箱记录保存，不允许代数压缩、重算或未计费的外部读取。下述空间只计这些结果记录；输入库、控制信息、地址、数值位长和算子内部工作区另计。允许这些额外能力时须重新结算，不能把本模型的存储下界外推。

合法已完成集 $I\subseteq V$ 是依赖偏序的下闭集。定义仍活跃的旧结果与可执行的新节点：
$$
L(I)=\{u\in I:\exists v\notin I,\ (u,v)\in E\}\cup(I\cap O),\qquad
R(I)=\{v\notin I:\operatorname{Pred}(v)\subseteq I\}.
\tag{TM.29}
$$
$R(I)$ 是反链，$L(I)$ 一般不是：若 $u\to v\to w$ 且另有 $u\to w$，在 $I=\{u,v\}$ 处，$u,v$ 都活跃且可比较。项目 `ExecutableFrontier` 的 `ReadyOver`、`executableFrontier` 对应 $R(I)$；它没有声明 $L(I)$ 的存储定理。

**继续充分性。** 固定 $I$、同一剩余源输入接口、静态规则和控制规则后，$L(I)$ 的实际值决定全部后续结果。证明：就绪节点的任意前驱在 $I$ 内且有未完成消费者，所以在 $L(I)$ 内。执行该节点并按式(TM.29)释放不再活跃的记录，便得到下一切面的值。沿剩余拓扑序归纳，所有后续值相同。因此缓存前沿是指定未来任务的充分表示；它通常不恢复已经丢弃的内部值，如只保留 $x+y$ 不能恢复 $x,y$。

令调度 $\pi$ 逐步产生 $I_0\subset\cdots\subset I_{|V|}$。在上述逐节点黑箱模型中，完成一步并释放死值之后的最小常驻峰值为
$$
M_{\rm live}(\pi)=\max_k\sum_{v\in L(I_k)}s_v.
\tag{TM.30}
$$
充分性由只保存活跃值的执行达到。必要性来自每个活跃值仍有未来消费者或属于指定保留输出，且禁止重新获得或以别的编码替代。若先分配新结果再释放最后一次使用的旧结果，瞬时峰值还须计 $\sum_{u\in L(I_k)}s_u+s_{v_{k+1}}$；允许原位覆盖时采用不同的分配合同。式(TM.30)没有把任意程序的信息下界等同于图切面的节点数。

总工作 $W=\sum_vt_v$ 与关键路径长度 $D=\max_{p}\sum_{v\in p}t_v$ 由这个固定计算图给出。若有 $p$ 个同速处理器、忽略通信与其他资源冲突，则完成时间满足 $T\ge\max(W/p,D)$；该下界不保证可同时达到。无限处理器下按依赖最早启动可达到 $D$。在单位时长模型中，最大反链大小等于所有合法前缀中就绪集合的最大大小：就绪集合总为反链；对任意反链 $A$，先完成其所有严格前驱，可使 $A$ 同时就绪。一次具体的分层未必包含达到该最大宽度的一层。

**同一递推的不同切法。** 在 $n\times m$ 格点上取
$$
d_{ij}=c_{ij}+\min(d_{i-1,j},d_{i,j-1}),\qquad d_{00}=c_{00},
\tag{TM.31}
$$
边界只取存在的前驱。整数坐标变换 $\tau=i+j,\ \xi=i$ 的行列式为 $-1$，具有整数逆 $i=\xi,j=\tau-\xi$；两个依赖方向均使 $\tau$ 增一，所以每个对角层可以并行计算。串行行序、列序和波前是同一递推的合法调度。工作量仍为 $nm$ 次节点计算；在单位算子且无限处理器合同中，关键路径为 $n+m-1$。任意旋转不自动保持整数域、依赖或资源合同。

取
$$
c=\begin{pmatrix}1&4&2&7\\3&1&5&2\\6&2&1&3\end{pmatrix},\qquad
d=\begin{pmatrix}1&5&7&14\\4&5&10&12\\10&7&8&11\end{pmatrix}.
\tag{TM.32}
$$
只保留 $d_{2,3}$，每节点结果大小和时长均为一。逐行常驻峰值四、逐列三；先分配新值再释放旧值时分别为五、四。按 $i+j$ 同步计算的层宽为 $1,2,3,3,2,1$，共六层；若保留全部旧层直到新层完成，峰值为六。三种执行均产生同一个结果十一。枚举这个有限依赖偏序的全部三十五个下闭集，得到串行常驻峰值最小值三；该有限核对不替代一般证明，也未新增 Lean 核验。

当允许重算时，已完成集合不再决定当前保存的值，应另取存储配置并逐次计费；这进入图上的 pebbling 型工作—存储问题。当允许状态摘要或代数重写时，则须证明目标因子化与更新闭合，不能继续沿用逐节点存储下界。项目 `FiniteHorizonValueFactorization.finite_horizon_value_factorization` 已在有限非空动作、全定义确定性转移、实奖励及终值的合同下证明：转移交织、奖励与终值因子化，推出所有有限视界 Bellman 值因子化。它支持这种摘要的语义检验，不替代本节 DAG 存储或部分域最小化适配。恢复卷8.5–8.6进一步给出必要边界：恒值动作可以解锁新操作，目标候选相同也可以有不同的继续价值。

**拓扑布局与 one-shot pebbling 的计数约定。** Per Austrin、Toniann Pitassi、Yu Wu，*Inapproximability of Treewidth, One-Shot Pebbling, and Related Layout Problems*，[arXiv:1109.4910v1](https://arxiv.org/pdf/1109.4910v1)，PDF第7页（印刷第6页）定义有向布局仅允许拓扑序，切面集合为 $V_i=\{u:\pi(u)\le i<\pi(v),(u,v)\in E\}$。第10页（印刷第9页）Definitions 2.9—2.11 规定首尾配置为空、每个 sink 至少被放置一次、每步只放一个或取一个 pebble、放置时全部前驱当前均有 pebble，成本计整个配置的最大基数，one-shot 又禁止重复放置。对这些字面规则下的非空有限 DAG，精确计数是 $\mathrm{BP}^{1s}(G)=\operatorname{Layout}(G;V,\max)+1$。

这个差一可直接证明。每个节点都通向某个 sink，所以全部节点必须被放置；首次放置次序是拓扑序。在放置第 $i+1$ 个节点前，$V_i$ 中每个节点都还必须保留，否则未来消费者将无法在禁止重算的条件下取得前驱。放置后瞬时至少有 $|V_i|+1$ 个 pebble；每次最后使用后立即逐个移除的清理顺序达到该界。取最优拓扑序，并注意非空图的最终切面 $V_{|V|}=\varnothing$，即得上述式子。单边 $u\to v$ 的稳定布局宽度是一，分开放／取的峰值是二；孤立单节点的宽度是零，峰值是一。

该 v1 第11页（印刷第10页）Lemma 2.12 的印刷等式省略了这个 $+1$，而所列 separate-move 规则计入放置后的配置；本文按明列的配置计数，不将该印刷等式直接套用。这个校正只针对所引 v1 的字面约定，没有据此判断其他版本。更不能把它移到本节的保留输出模型：式(TM.29)含 $I\cap O$，末端输出仍驻留。单位大小、先分配再释放时，固定顺序的精确瞬时峰值是 $\max_{0\le i<|V|}(|L(I_i)|+1)$；不能无条件改成 $\max_i|L(I_i)|+1$，因为最大稳定集合可能恰好是最终保留输出。式(TM.30)及式(TM.32)后的既有常驻与瞬时计数继续采用原合同。另有 $n$ 个源共同指向一个 sink 的例子：拓扑稳定宽度为 $n$、分步峰值为 $n+1$，但底层无向星图 pathwidth 为一，故有向拓扑约束不能由无向布局宽度替代。

**张量收缩是另一份空间合同。** Igor L. Markov、Yaoyun Shi，*Simulating quantum computation by contracting tensor networks*，[arXiv:quant-ph/0511069v7](https://arxiv.org/pdf/quant-ph/0511069v7)，PDF第8页 Definition 3.3 与式(1)描述通常一次同时求和两张量全部共享指标的收缩，也允许开放连线；第9页 Proposition 3.5 在电路概率任务中通过输入与测量张量关闭网络。第10页为图论分析另取逐条边收缩、保留随后仍待收缩的自环这一约定，Definition 4.1 的 $\operatorname{cc}(G)$ 只统计新合并顶点的最大度，不包含初始顶点；第10—11页 Proposition 4.2 才在该约定下证明 $\operatorname{cc}(G)=\operatorname{tw}(L(G))$。

这里 $L(G)$ 是线图。第10页 Proposition 3.6 的运行时参数却是所有出现张量的最大 rank，初始张量不能漏算；路径例子的 $\operatorname{cc}=1$ 而初始最大度数为二，已经显示两种计量不同。将平行边改成同时收缩会改变中间计数，不能原封不动保留上述精确等式。第11页 Lemma 4.4、Theorem 4.5 还给原图 treewidth 与 $\operatorname{cc}$ 的比较，包含最大度依赖；星图 $K_{1,m}$ 的原图 treewidth 为一，而线图是 $K_m$、$\operatorname{cc}=m-1$，说明该依赖不可省略。以上是成熟的网络收缩连接，不把它等同于本节的拓扑执行次序、驻留输出或任意开放端口模型的空间成本。

**格点递推的成熟调度骨架。** Richard M. Karp、Raymond E. Miller、Shmuel Winograd，*The Organization of Computations for Uniform Recurrence Equations*，Journal of the ACM 14(3)（1967），563–590，[doi:10.1145/321406.321418](https://doi.org/10.1145/321406.321418)，[原始扫描](https://www.cs.colostate.edu/~cs560dl/Notes/KMW-JACM1967.pdf)，印刷第564—566页的定义要求整数格点域、给定的必需域外边界值、与格点无关的固定偏移、单个与格点无关的函数，并严格依赖列出的参数；合法正整数调度尊重依赖，一次函数求值计一个时间单位。它为式(TM.31)的固定前驱方向及调度问题提供成熟骨架，但任意变化的 $c_{ij}$ 不是那个原始单一同质函数方程的逐字实例。

本节把 $c_{ij}$ 作为逐格给定的外部费用场，其取得若须计费，应把读取或计算依赖加入图；这项扩充本身不保证原文所有定理条件。式(TM.31)的有限反对角合法性已经由本节整数变换直接证明：两个前驱在 $(\tau,\xi)$ 中分别为 $(\tau-1,\xi-1)$ 和 $(\tau-1,\xi)$。该证明运输实际有限域、边界与资源约定，不借未列明的无限域定理代替，也不改变式(TM.32)的有限实例。

### 4.2 区域边界的 min-plus 组合与相容运输

固定有限带实边费用的 DAG 区域 $R$，入口 $A$、出口 $B$，以及明确指定的内部合法路径族。定义边界传递
$$
K_R(b,a)=\min_{\gamma:a\leadsto b\text{ in }R}\sum_{e\in\gamma}c_e,
\tag{TM.33}
$$
无合法路径时值为 $+\infty$。DAG 保证所有非空路径族有限，从而最小值取得；负边费用不造成负环问题。费用按边计，以免相邻区域的共享顶点费用重复收费。

设 $R_1:A\to B$ 与 $R_2:B\to C$ 串联，内部不交；要求每条所论整体路径都恰在某个 $b\in B$ 分为一条 $R_1$ 路径和一条 $R_2$ 路径，并且每一对这样的端点匹配路径都合法拼接。共同来源或共享资源若会额外限制拼接，也必须保存在接口中；只有端点同名不承担此条件。此时
$$
K_{R_2\circ R_1}(c,a)
=\min_{b\in B}\{K_{R_2}(c,b)+K_{R_1}(b,a)\}.
\tag{TM.34}
$$
证明：任一整体路径按接缝分解，其费用不小于右边；反向对达到有限右边的 $b$ 取两段最优路径并合法拼接。若右边无有限项，则两侧均不可达。结合律来自有限双重最小值的交换及加法结合律。因此合法串联块可由同一份边界矩阵参与后续计算。若任务还要求返回实际路径、计数、日志、内部中间值或其他联合读数，须扩充摘要；代价矩阵没有自动恢复这些内容。

若允许路径反复跨接缝、绕过接口，或两段最低费用不能在同一实现中同时达到，式(TM.34)不成立。存在环时，还须处理可达负环、极小值取得及反馈闭包；一般非 min-plus 动态规划需要边界响应函数，不能一概编码成这种矩阵。

**费用势的坐标运输。** 对顶点势 $\phi$ 定义 $c'_{uv}=c_{uv}+\phi(v)-\phi(u)$。沿每条路径望远镜相消，得到
$$
K'_R(b,a)=K_R(b,a)+\phi(b)-\phi(a).
\tag{TM.35}
$$
若入边界值同步改为 $x'_a=x_a+\phi(a)$，输出 $y_b=\min_a(K_R(b,a)+x_a)$ 满足 $y'_b=y_b+\phi(b)$。固定端点的路径最优集合不变；端口数值若没有配套运输，不能声称整个读数不变。此推导与既有路径 cocycle/状态势及端口运输机制相接，没有提供任意普通实矩阵相似变换保持 min-plus 运算或算法成本的结论。

### 4.3 费用空间的分片线性几何与边界恢复范围

固定非空有限 DAG 路径族 $\mathcal P$，边费用向量 $c\in\mathbb R^E$，路径使用向量 $n_p\in\{0,1\}^E$。最优值为
$$
F(c)=\min_{p\in\mathcal P}\langle n_p,c\rangle.
\tag{TM.36}
$$
于是 $F$ 是凹的分片线性函数：凹性由每个路径的仿射等式及取最小值直接推出；有限条线性函数的比较将费用空间分成有限多面体区域。在路径 $p$ 的最优区域中，对每条 $q$ 都有 $\langle n_p-n_q,c\rangle\le0$；不同真正最优区域的公共面反映费用并列。两条路径费用相等但被第三条严格支配时，其相等超平面并不是最优方案的切换面。

令 $L=\max_p\|n_p\|_1$。对任意 $c,c'$，每条路径的费用差至多 $L\|c-c'\|_\infty$；分别代入两边的最优路径，得到
$$
|F(c)-F(c')|\le L\|c-c'\|_\infty.
\tag{TM.37}
$$
若在 $c$ 处唯一最优路径为 $p_*$，且存在其他路径，令 $\Delta=\min_{q\ne p_*}\langle n_q-n_{p_*},c\rangle>0$。当 $\|c-c'\|_\infty\le\varepsilon$ 且 $2L\varepsilon<\Delta$ 时，$p_*$ 在 $c'$ 处仍唯一最优，因为每个竞争差至多下降 $\|n_q-n_{p_*}\|_1\varepsilon\le2L\varepsilon$。唯一一条路径的情形无需该间隔条件。这里最优值稳定与最优结构稳定是两个命题；切换面上的最优值仍满足式(TM.37)，而最优路径可以变化。

这给动态规划与关系接口主线一个具体对应：全体满足节点关系及共同输入约束的赋值构成计算整体；合法切面给未来任务的充分边界；调度指定依赖偏序的一种实现次序；驻留值记录完成部分对后续计算仍有用的区别；区域摘要在式(TM.34)条件下支持继续组合。它是统一关系问题的有限、确定性、可计费实例，不是已经从算法推导三维物理空间、量子规则或普遍非线性时间。

**三种空间不可混同。** 原计算图的节点布局、运行时存储地址、费用参数空间分别支持不同问题。图可研究路径、偏序与分隔；费用空间支持式(TM.36)的多面体与分片线性分析；定义了范数才有式(TM.37)的误差大小。微分、黎曼、辛、复几何等方法各需其光滑结构、度量、二形式或复结构；单凭“整体”与“几何”二字不能取得这些假设。对循环 Bellman 系统，有限展开可产生 DAG；无限视界则另需存在、唯一及收敛条件。项目 `DiscountedBellmanContraction.discounted_bellman_contraction_and_unique_fixed_point` 的有限状态/动作、非负归一转移和 $0<\gamma<1$ 只承担其折扣合同。

**充分边界与完整体恢复。** 设计算整体或历史为 $X$，指定全部后续任务的行为商为 $q:X\to Q$，切面摘要为 $e:X\to E$。继续充分只要求 $\ker e\subseteq\ker q$；恢复完整内部还要求 $e$ 对所需完整对象单射，或提供另一份限制后的逆。求和节点把 $(0,1)$ 与 $(1,0)$ 变成相同结果即可反驳自动完整重构。合法继续还须保持动作定义域、费用及后继；区域拼接则再履行A卷第3.1节与A卷第3.2节的相容代表与合法域条件。计算空间换时间、任务商压缩和全体双向恢复是相接而不等价的三种操作。

### 4.4 连续状态与连续时间的同一边界组合

动态规划的原理不要求状态或时间离散。有限表格只是计算表示之一；连续状态上的价值函数可以作为边界，而组合仍遵循对中间状态取下确界的 Bellman 原理。以下直接给出一个可完全计算的连续模型，不由离散算法推出物理时空。

固定 $d\ge1,t>0$ 及 $x,y\in\mathbb R^d$。合法内部为绝对连续路径 $\gamma:[0,t]\to\mathbb R^d$，满足两端点条件且导数平方可积，费用为 $\mathcal A(\gamma)=\frac12\int_0^t\|\dot\gamma(r)\|^2\,dr$。由 $y-x=\int_0^t\dot\gamma(r)\,dr$ 和 Cauchy–Schwarz，不小于 $\|y-x\|^2/(2t)$。匀速直线取得下界；等号要求导数几乎处处为 $(y-x)/t$，绝对连续性遂使路径唯一。故
$$
K_t(x,y)=\inf_{\gamma:x\leadsto y}\mathcal A(\gamma)
=\frac{\|y-x\|^2}{2t},\qquad
\gamma_*(r)=x+\frac r t(y-x).
\tag{TM.38}
$$
对 $s,t>0$，设 $z_*=(tx+sy)/(s+t)$。展开平方得
$$
K_s(x,z)+K_t(z,y)
=K_{s+t}(x,y)+\frac{s+t}{2st}\|z-z_*\|^2.
\tag{TM.39}
$$
因此
$$
K_{s+t}(x,y)=\min_{z\in\mathbb R^d}\{K_s(x,z)+K_t(z,y)\}.
\tag{TM.40}
$$
这同时是连续路径的切割、合法拼接和最优性证书。整条最优直线在时刻 $s$ 的实际位置恰为 $z_*$；若指定另一个切面值 $z$，式(TM.39)量化其额外最低费用。这里的三个费用都在同一端点、同一欧氏范数、同一时长单位下定义。

对有界 Lipschitz 终端函数 $g:\mathbb R^d\to\mathbb R$，定义
$$
(S_tg)(x)=\inf_y\{K_t(x,y)+g(y)\},\qquad S_0g=g.
\tag{TM.41}
$$
$t>0$ 时，连续有下界的 $g$ 与二次强制增长项保证极小值取得。有限值的双重下确界可交换，再用式(TM.40)，得到 $S_s(S_tg)=S_{s+t}g$。这里整份函数是边界数据，不是有限个表项；其精确存储或有限维闭合另需结构。

若 $g$ 的 Lipschitz 常数为 $L_g$，取 $y=x$ 得 $S_tg\le g$；由 $g(y)\ge g(x)-L_g\|y-x\|$ 并最小化一元二次式得
$$
g(x)-\frac12L_g^2t\le (S_tg)(x)\le g(x),\qquad
\|S_tg-S_th\|_\infty\le\|g-h\|_\infty.
\tag{TM.42}
$$
后一式由 $g\le h+\|g-h\|_\infty$ 及其反向取下确界证明。将每个候选 $y$ 同步平移，还得 $S_tg$ 的空间 Lipschitz 常数不超过 $L_g$。所以 $t\downarrow0$ 时有统一回接，而不只是形式上的无穷重复假设。

这个算子是经典 Hopf–Lax 构造的二次费用实例。相应 Hamilton–Jacobi 方程写作 $\partial_tV+\frac12\|\nabla V\|^2=0$；全局经典可微性不能默认，一般需要粘性解框架。该 PDE 联系只作成熟理论接口，此处证明承担式(TM.38)–(TM.42)及其直接推论，不冒领一般 HJB 存在唯一性或新 Lean。更一般控制系统的动态规划需要合法轨道能够限制并拼接、成本可加以及状态包含继续所需信息；有限表格缺失不是数学障碍。

最小费用核不保留全部路径。具有相同端点和时长的非最优弯曲路径会被式(TM.38)的优化消去；若指定 $x=y=0$，零路径与非零闭合弯曲路径就是明确例子。只有将体限制为该模型的唯一最优路径族，端点和时长才恢复完整轨道。一般不严格凸的问题还可能有多个极小路径。非线性价值算子与非线性时间也是不同命题：本例 $S_t$ 对通常函数加法并非线性，但参数仍满足加法半群规律。

### 4.5 共同能量约束使重复细化恢复连续整体

上一节的完整合法路径还可以通过全部相容的有限切面精确恢复。固定 $T>0,a,b\in\mathbb R^d$ 和有限实数 $E\ge\|b-a\|^2/(2T)$。令 $h_n=T/2^n$，定义
$$
Q_n^E=\left\{(x_0,\ldots,x_{2^n}):\ x_0=a,\ x_{2^n}=b,\quad
\sum_{k=1}^{2^n}\frac{\|x_k-x_{k-1}\|^2}{2h_n}\le E\right\}.
\tag{TM.43}
$$
每个 $Q_n^E$ 取通常欧氏子空间拓扑，逆极限取相应积拓扑的子空间拓扑。连接映射取偶数编号节点。对相邻两个细步用 $\|u+v\|^2\le2(\|u\|^2+\|v\|^2)$，得到粗层能量不超过细层能量，所以连接映射良定义。每个粗层节点间插入算术中点，细层能量恰等于粗层能量，故连接映射满射。每层 $Q_n^E$ 是非空紧集：约束闭且由离散 Cauchy–Schwarz 得 $\|x_k-a\|\le\sqrt{2ET}$，直线节点给非空性。

设 $\mathcal H_E$ 是所有端点为 $a,b$ 的绝对连续路径，满足 $\frac12\int_0^T\|\dot\gamma\|^2\le E$，赋一致拓扑。则采样给出相容的双射，且实际上是同胚：
$$
\mathcal H_E\ \cong\ \varprojlim_n Q_n^E.
\tag{TM.44}
$$
**证明。** 合法路径在每个小区间应用积分 Cauchy–Schwarz，其样本的离散能量不超过完整能量，因此得到塔。连续路径在稠密二分网格上的值决定整条路径，故采样单射。

反向给相容塔，令 $\gamma_n$ 为第 $n$ 层节点的分段仿射插值。它的实际积分能量恰为式(TM.43)的和，故所有插值满足
$$
\|\gamma_n(r)-\gamma_n(r')\|\le\sqrt{2E}\,|r-r'|^{1/2}.
\tag{TM.45}
$$
若 $m\ge n$，两条插值在全部第 $n$ 层网格点相同。取任意 $r$ 所在粗网格区间的一个端点，分别用式(TM.45)，得到 $\|\gamma_m-\gamma_n\|_\infty\le2\sqrt{2Eh_n}\to0$。所以有唯一连续一致极限 $\gamma$，并保留全部样本与端点。

导数 $v_n=\dot\gamma_n$ 在 $L^2([0,T];\mathbb R^d)$ 中有界。取弱收敛子列至 $v$；对每个 $r$，以区间指示函数作 $L^2$ 测试函数，$\gamma_n(r)=a+\int_0^rv_n$ 收敛到 $a+\int_0^rv$。与一致极限比较可得 $\gamma(r)=a+\int_0^rv$，故 $\gamma$ 绝对连续。弱下半连续性给其能量不超过 $E$。这证明采样满射。这里使用的是成熟的有限维向量值 $L^2$ 弱紧性与范数弱下半连续性，不是单靠每层存在推出整体存在。

式(TM.45)及固定起点使 $\mathcal H_E$ 一致有界且等度连续；同一弱导数论证证明它在一致拓扑中闭。Arzelà–Ascoli 使其紧，而逆极限是有限维紧空间乘积中的 Hausdorff 子空间。采样连续且为双射，因而是同胚。证毕。

记相容塔第 $n$ 层的离散能量为 $E_n$。粗化不增能量给 $E_n\uparrow E_\infty\le E$；对已恢复路径在每个小区间应用 Cauchy–Schwarz，有 $E_n\le\mathcal A(\gamma)$；弱下半连续又给 $\mathcal A(\gamma)\le\liminf_nE_n$。所以完整塔还精确恢复能量：
$$
\mathcal A(\gamma)=\sup_n E_n.
\tag{TM.46}
$$
这不意味着能量在一致拓扑下连续，也不将式(TM.44)提升为强 $H^1$ 同胚。端点为零的 $\gamma_n(r)=n^{-1}\sin(2\pi nr/T)$ 一致趋于零，但每条作用量均为 $\pi^2/T$。固定粗采样不能稳定恢复所有能量；极限的精确可识别、近似的取得模量与强拓扑收敛是不同要求。

该定理的边界不是一个时间点，而是全部相容有限采样及同一个能量预算。固定一个有限采样层一般无法恢复全部合法路径；预算恰为端点最小能量时，合法族退化为唯一匀速直线，属于例外。缺少统一能量或连续模量时，相容的逐层样本也不保证连续体。例如在 $[0,1]$ 上给全部二分有理点赋值 $f(0)=0$、$f(q)=1$ 对每个 $q>0$；每个有限层都可由连续折线实现，但全部样本没有连续实现，且首小段能量随细化无界。

因此，反复细化与连续整体的关系具有明确的中间条件：共同来源的相容性加统一的紧性控制。式(TM.44)描述完整路径对象，式(TM.40)描述其中最优费用的组合摘要；后者由对前者作优化取得，通常不可逆。有限采样仍含精确实坐标，不等于有限比特算法；求取、存储这些数据的资源另计。二分细化是一个可重复的生成／观察程序，既没有设定最低物理层，也没有将细化层数等同于物理流逝时间。

### 4.6 静态切分与因果容量：完整历史流、末端法与可压缩记忆

改变一个证明的切分顺序，不等于改变一个随机过程的合法执行顺序。本节在有限坐标、确定条件容量的模型中，把这一区别写成两个不同的可行域：静态柱集容量只限制末端法的一组边缘质量；逐步归一化、完整档案条件化和合法调度则组成一个有限历史流多面体。后者投影恰好给出可实现的末端联合律，前者一般严格更大。

以下为普通数学定义与纸面推导，不是新增 Lean 声明或形式核验结论。全局柱集界及静态证书与采样顺序的区分，复用不可变版本 `e25dea7a9919fcae53bb797f7740b0f5c99668ac` 的 [Erdős 7 第59篇 B.1—B.3](https://github.com/the-omega-institute/trureturing/blob/e25dea7a9919fcae53bb797f7740b0f5c99668ac/docs/reports/erdos7-odd-covering/problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md)。有限状态动态规划、占用流和保行为商均为成熟结构；这里明确给出它们接入当前条件容量模型所需的映射、两方向证明及档案边界，不主张这些一般原理的新颖性。

#### 4.6.1 有限坐标、完整可访问档案与可拼接行

固定有限非空坐标集 $I=\{1,\ldots,n\}$，每个坐标的字母表 $X_i$ 有限非空，记 $m_i=|X_i|$。完整具名赋值空间、确定原子容量及允许行分别为

$$
\Omega=\prod_{i\in I}X_i,\qquad
\frac1{m_i}\le r_i\le1,\qquad
K_i=\left\{q\in\mathbb R_{\ge0}^{X_i}:
\sum_{x\in X_i}q_x=1,\ q_x\le r_i\ \forall x\right\}.
\tag{TM.212}
$$

每个 $K_i$ 是非空紧多面体；均匀行属于其中。坐标身份与字母表始终固定，不允许在不同历史中重命名同一个实际坐标。

**定义 4.1（合法逐步法）。** 每个坐标恰读取一次。第 $t$ 步之前的 $\mathcal F_t$ 包含当前全部实际可访问档案，包括已经取得的结果、此前选择及保留的辅助记录。调度先使用该档案与本步合法的调度随机化选择未读坐标 $I_t$；令 $\mathcal G_t$ 进一步包含本步已公开的调度随机化及坐标选择。结果 $Y_t$ 在其后取得。在 $I_t=i$ 的事件上，要求

$$
\Pr(Y_t=x\mid\mathcal G_t)\le r_i
\quad\text{几乎处处，对每个 }x\in X_i.
\tag{TM.213}
$$

取得结果后，实际发生的坐标、结果与新增记录进入下一份档案。本节保留此前可访问记录，使 $\mathcal F_t\subseteq\mathcal G_t\subseteq\mathcal F_{t+1}$；尚未公开的源创新不因此被提前加入。条件式针对完整可访问档案，不能先丢掉已知信息再验证容量。

调度的新随机性在使用时不带尚未取得的源创新信息。它可以在抽样前公开；结果抽样所用的源随机性却不能在结果抽样前一并公开。如果一份种子已经让未来结果成为当前可知量，该信息属于 $\mathcal G_t$，必须按它重新检查式(TM.213)。这里的独立性针对新调度随机性与尚未取得的源创新，不要求调度变量与最终输出独立：最终输出可以因策略选择而依赖调度变量。

**假设26.2（cap-only 行拼接）。** 给定任一可达历史和所选未读坐标 $i$，允许使用 $K_i$ 中任意一行；不同后继历史上的合法行可以独立选择和拼接。除每个坐标恰读一次外，没有未记录的共同模型索引、源相容约束、跨分支预算或限制行选择的额外资源条件。任意未读坐标均可被选取，调度可以随机化。

这是下文精确可实现性的实质前提。如果对象是一个预先固定联合律的外部源，而控制者只能查询它，满足数值容量的任意条件行未必实际可选。此时必须额外保持该源的条件律相容关系；仅有 $q\in K_i$ 的流约束只是一份松弛。历史相关的权限、费用与预算也不能靠这一假设被免费删除。

#### 4.6.2 全局柱集界不需要固定采样顺序

对 $A\subseteq I$ 及具名部分赋值 $a\in\prod_{i\in A}X_i$，定义实际柱集与价格

$$
C_a=\{v\in\Omega:v_i=a_i\ \forall i\in A\},
\qquad c_a=\prod_{i\in A}r_i.
\tag{TM.214}
$$

空赋值给 $C_\varnothing=\Omega$、$c_\varnothing=1$。

**命题 4.2（任意合法调度的全局柱容量）。** 任意满足式(TM.213)的合法逐步法，其末端联合律 $\mu$ 满足

$$
\mu(C_a)\le c_a
\qquad\text{对每个实际部分赋值 }a.
\tag{TM.215}
$$

这个必要条件不要求假设26.2中的全部行都可实现，只使用完整档案下的条件容量与非预见调度。

**证明。** 令 $H_t$ 为已经发生的有序坐标—结果历史，$U(H_t)$ 为未读坐标。对剩余步数倒向归纳，证明

$$
\Pr(C_a\mid\mathcal F_t)
\le
\mathbf1_{\{H_t\text{与 }a\text{相容}\}}
\prod_{i\in A\cap U(H_t)}r_i.
\tag{TM.216}
$$

全部坐标读完时，两侧均为已经确定的事件指示。假设后一时刻结论成立，并先条件化于 $\mathcal G_t$。若过去已经与 $a$ 冲突，成功概率为零。否则，若所选坐标 $i\notin A$，对结果平均不改变剩余目标乘积；若 $i\in A$，仅 $Y_t=a_i$ 的分支可能成功，其条件概率至多 $r_i$，其他目标坐标由归纳给出剩余因子。再对调度随机化取条件平均，得到式(TM.216)。在根处取期望即得式(TM.215)。整个证明没有假定坐标独立。$\square$

**推论 4.3（分数柱覆盖）。** 对目标事件 $S\subseteq\Omega$，若非负权重满足

$$
\sum_a w_a\mathbf1_{C_a}\ge\mathbf1_S,
\qquad w_a\ge0,
\tag{TM.217}
$$

则所有合法逐步法均满足

$$
\mu(S)\le\sum_a w_ac_a.
\tag{TM.218}
$$

证明只需对式(TM.217)积分，再逐项使用式(TM.215)。各柱集可以彼此交叠，覆盖不要求分割。

#### 4.6.3 证书树的切分顺序与实际采样顺序

固定一个证书节点 $a$，其整个柱集的价格是 $c_a$。可以直接用该柱覆盖目标在其内的部分，或选取证书尚未固定的坐标 $i$，用各子柱的覆盖拼成覆盖。若子覆盖价格已经除以各自的 $c_ar_i$，则归一化价格递推为

$$
U(a)=\min\left\{1,\ r_i\sum_{x\in X_i}U(a\cup\{i=x\})\right\}.
\tag{TM.219}
$$

无目标完成的节点取值零；完整赋值上的值为 $\mathbf1_S$。若证书也优化下一切分坐标，可在分裂项再取 $\min_i$。按证书树归纳，每个节点都构造一份真实柱覆盖，根价格因而适用于所有合法采样顺序。该递推只搜索一类树状覆盖，不声称穷尽所有分数柱覆盖。

这份推导使用 $\mu(C_a)\le c_a$，没有使用通常并不成立的
$\mu(C_{a\cup\{i=x\}}\mid C_a)\le r_i$。对证书而言已经固定的坐标，在实际采样中可能后来才被读取；不能据此重排条件律。

**反例 4.4（合法法的反序条件概率越过容量）。** 取两比特，$r_1=r_2=3/4$。先抽 $X_1$，令 $\Pr(X_1=0)=3/4$；再抽 $X_2$，使它以 $3/4$ 的条件概率等于 $X_1$。这是合法法，其联合律为

$$
(\mu_{00},\mu_{01},\mu_{10},\mu_{11})
=\frac1{16}(9,3,1,3).
\tag{TM.220}
$$

然而

$$
\Pr(X_1=0\mid X_2=0)=\frac9{10}>\frac34.
\tag{TM.221}
$$

所以同一份末端法不能按其反序条件律合法地先抽 $X_2$。静态证书仍可以先切 $X_2$，因为它依赖的是全局柱容量。

第59篇 A 节的 terminal phase elimination 要求先读完 core，再读取 terminal 坐标；其最优条件行与乘积续接是在这份实际顺序约束下使用。B 节的 terminal 产品覆盖则组合实际安全集合的柱覆盖，乘的是证书价格，无需实际法具有独立坐标或合法的 core-first 条件化。两者分别承担不同的量词范围。

#### 4.6.4 全局容量松弛与逐步可实现性的严格分离

记 $\mathcal A$ 为假设26.2下可由合法逐步法实现的末端联合律集合，并定义静态全局柱容量多面体

$$
\mathcal G=
\left\{\mu\in\mathbb R_{\ge0}^{\Omega}:
\sum_{v\in\Omega}\mu_v=1,\
\sum_{v\in C_a}\mu_v\le c_a\ \forall a\right\}.
\tag{TM.222}
$$

A卷命题4.2给 $\mathcal A\subseteq\mathcal G$。

**命题 4.5（两比特严格间隙）。** 对 $r_1=r_2=3/4$，令 $S=\{00,11\}$。则

$$
\max_{\mu\in\mathcal A}\mu(S)=\frac34,
\qquad
\max_{\mu\in\mathcal G}\mu(S)=1.
\tag{TM.223}
$$

**证明。** 分布

$$
\widehat\mu_{00}=\widehat\mu_{11}=\frac12,
\qquad
\widehat\mu_{01}=\widehat\mu_{10}=0
\tag{TM.224}
$$

满足全部静态容量：单坐标原子质量为 $1/2\le3/4$，双坐标原子质量至多 $1/2<9/16$，空柱质量为1。因此 $\widehat\mu\in\mathcal G$ 且 $\widehat\mu(S)=1$。

对任意合法逐步法，在第二次抽样前，第一比特已经属于完整档案。无论第二次选择哪个坐标，匹配这个已知比特的条件概率均至多 $3/4$。对完整档案与所有调度随机化平均，得到 $\mu(S)\le3/4$。反向，先公平抽第一比特，再以 $3/4$ 概率匹配它，所得合法联合律为

$$
(\mu_{00},\mu_{01},\mu_{10},\mu_{11})
=\frac18(3,1,1,3),
\tag{TM.225}
$$

并达到 $3/4$。$\square$

这不是固定顺序的局限；上界同时覆盖自适应顺序、随机顺序和合法策略的混合。缺失的约束是已取得结果进入实际档案之后，对下一行仍须满足的条件容量。将未来匹配结果预存在一个公开种子中，不能规避这条条件。

#### 4.6.5 分数覆盖的直接对偶是支持次概率 packing

全部部分赋值只有有限多个。记最小分数柱覆盖价格为

$$
\mathsf C(S)=
\min_{w_a\ge0}
\left\{\sum_a c_aw_a:
\sum_{a:v\in C_a}w_a\ge1\ \forall v\in S\right\}.
\tag{TM.226}
$$

非负权重自动使 $S$ 外的覆盖不等式成立，因此它等价于式(TM.217)。空柱给有限可行价格1；$S=\varnothing$ 时零权重给价格零。

有限线性规划对偶给出

$$
\mathsf C(S)=
\max_{\nu_v\ge0\ (v\in S)}
\left\{\sum_{v\in S}\nu_v:
\sum_{v\in S\cap C_a}\nu_v\le c_a\ \forall a\right\}.
\tag{TM.227}
$$

这是支持在 $S$ 上的非负质量 packing。空柱约束只要求总质量至多1，而非恰为1。两边有限、可行且有界，有限 LP 强对偶适用。

对 $\mu\in\mathcal G$，其限制 $\nu_v=\mu_v\mathbf1_S(v)$ 是式(TM.227)的可行点，所以

$$
\max_{\mu\in\mathcal A}\mu(S)
\le\max_{\mu\in\mathcal G}\mu(S)
\le\mathsf C(S).
\tag{TM.228}
$$

若直接对式(TM.222)中的归一化概率 LP 写对偶，则归一化等式具有一个自由乘子 $\lambda$。删去冗余空柱约束后，该对偶为

$$
\begin{aligned}
\max_{\mu\in\mathcal G}\mu(S)
=\min_{\lambda\in\mathbb R,\ w_a\ge0\ (a\ne\varnothing)}
&\left[\lambda+\sum_{a\ne\varnothing}c_aw_a\right],\\
\text{约束}\quad
&\lambda+\sum_{\substack{a\ne\varnothing\\v\in C_a}}w_a
\ge\mathbf1_S(v)\quad\forall v\in\Omega.
\end{aligned}
\tag{TM.229}
$$

式(TM.226)允许的是非负空柱权重，式(TM.229)的 $\lambda$ 却可取负值。不能仅凭二者都使用柱集，就略过这个对偶区别；这里不假设任意支持次概率 packing 都可在保容量下扩充成概率律。

对A卷命题4.5的相等事件，式(TM.224)本身具有总质量1并支持在 $S$ 上，因而是式(TM.227)的价格1见证。空柱又给上界1，所以

$$
\mathsf C(\{00,11\})=1>\frac34.
\tag{TM.230}
$$

因此穷尽该静态松弛的所有分数柱覆盖，仍不能证明真实的 $3/4$ 上界。

#### 4.6.6 有序历史的有限流多面体

定义全部有序坐标—结果历史

$$
\mathcal H_k=
\left\{((i_1,x_1),\ldots,(i_k,x_k)):
i_1,\ldots,i_k\text{互异},\ x_j\in X_{i_j}\right\},
\qquad \mathcal H=\bigcup_{k=0}^{n}\mathcal H_k.
\tag{TM.231}
$$

根为 $\varnothing$。$U(h)$ 是未读坐标，$hix$ 表示向历史追加 $(i,x)$。当 $|h|=n$，$v(h)\in\Omega$ 是其完整具名赋值。这里“完整历史”指完整的有序坐标—结果历史；若实际观察者还有额外档案，本节先投影这些额外记录，并在下节说明保留范围。

设节点质量为 $m(h)$，选取流为 $f(h,i)$，结果子流为 $f(h,i,x)$。定义 $\mathcal P_H$ 为下列有限线性约束的非负解集：

$$
\begin{aligned}
m(\varnothing)&=1,\\
\sum_{i\in U(h)}f(h,i)&=m(h) &&(|h|<n),\\
\sum_{x\in X_i}f(h,i,x)&=f(h,i) &&(i\in U(h)),\\
0\le f(h,i,x)&\le r_if(h,i) &&(x\in X_i),\\
m(hix)&=f(h,i,x).
\end{aligned}
\tag{TM.232}
$$

终端 joint-law 投影定义为

$$
\mu_v=\sum_{\substack{h\in\mathcal H_n\\v(h)=v}}m(h).
\tag{TM.233}
$$

**引理 4.6（质量守恒与紧性）。** 对每个可行流，

$$
\sum_{h\in\mathcal H_k}m(h)=1
\qquad(0\le k\le n).
\tag{TM.234}
$$

**证明。** 根层成立。若第 $k$ 层成立，对该层所有选择和结果求和，再用唯一父节点关系，得到第 $k+1$ 层总质量仍为1。因此每个节点质量、选取流和子流都在 $[0,1]$ 内，式(TM.233)是概率律。任一固定坐标顺序配均匀行给出可行流；约束有限且闭，故 $\mathcal P_H$ 是非空紧多面体。$\square$

#### 4.6.7 流与合法策略的双向实现

**定理 4.7（有序历史流的精确实现）。** 在假设26.2下，$\mathcal P_H$ 的式(TM.233)投影恰等于 $\mathcal A$。更精确地，任意实际合法策略都诱导式(TM.232)中的坐标历史流；任意这样的流都能由一份满足完整档案条件容量的合法策略实现。

**证明：策略到流。** 对 $h\in\mathcal H_t$ 置

$$
\begin{aligned}
m(h)&=\Pr(H_t=h),\\
f(h,i)&=\Pr(H_t=h,I_t=i),\\
f(h,i,x)&=\Pr(H_t=h,I_t=i,Y_t=x).
\end{aligned}
\tag{TM.235}
$$

分支互斥且完备给出全部守恒等式。即使实际档案还包含额外随机记录，$\{H_t=h,I_t=i\}$ 仍对 $\mathcal G_t$ 可测，故

$$
\begin{aligned}
f(h,i,x)
&=\mathbb E\left[
\mathbf1_{\{H_t=h,I_t=i\}}
\Pr(Y_t=x\mid\mathcal G_t)\right]\\
&\le r_i f(h,i).
\end{aligned}
\tag{TM.236}
$$

这一步是对合法的细档案条件行取平均；确定容量与行集合的凸性保留合法性。式(TM.233)正是原策略的末端联合律。

**证明：流到策略。** 在 $m(h)>0$ 时定义选择分布，在 $f(h,i)>0$ 时定义结果行：

$$
\sigma(i\mid h)=\frac{f(h,i)}{m(h)},
\qquad
q(x\mid h,i)=\frac{f(h,i,x)}{f(h,i)}.
\tag{TM.237}
$$

式(TM.232)保证两者归一化，且 $q(\cdot\mid h,i)\in K_i$。零质量历史任选未读坐标的合法选择分布；零选择流的结果行可取均匀行。

先用独立于尚未取得结果创新的新调度随机性按 $\sigma$ 选择坐标，并将本步调度随机性和选择纳入档案；随后用尚未公开的新结果创新按 $q$ 抽样。该结果行仅依赖 $h,i$，即使条件于完整已公开的调度随机性也仍满足 $q_x\le r_i$。结果创新可以在抽样完成后被保留，但不能在此前公开；以后使用的新创新与此前档案独立。

对历史长度归纳。根概率为1。若到达 $h$ 的概率为 $m(h)$，正流分支的实际概率为

$$
m(h)\sigma(i\mid h)q(x\mid h,i)
=f(h,i,x)=m(hix).
\tag{TM.238}
$$

零流分支的概率也为零。因此所构造策略逐层实现全部指定历史流，终端投影就是式(TM.233)。$\square$

构造使用独立的新随机创新来实现给定条件核，不意味着结果坐标独立。条件行依赖过去结果，因而仍能产生模型允许的联合关联。

**推论 4.8（凸性、可达性及实现边界）。** $\mathcal A$ 是非空紧凸多面体，任何线性末端目标都达到最优值。合法策略的凸混合可先抽一份独立于新结果源的策略选择变量，公开其值，再执行相应合法策略；式(TM.213)在每个已知混合分支上仍成立。

这不意味着“先公开一个决定全部未来结果的种子，再依次读出”合法。例如容量小于1时，公开种子已决定的下一结果具有条件概率1，即使忘记种子后的边缘分布很均匀也不合规。末端法可实现是存在一份合法实现的结论，并不认证该末端法的任意给定实现。

A卷定理4.7保留原策略的有序坐标—结果历史律及末端 joint law，却不保留原始随机种子和其他辅助档案的完整联合律。条件平均与重新实现可以改变这些额外记录及其关联。若它们属于任务输出，必须在模型中显式保留。

#### 4.6.8 部分赋值 DAG 的占用流与两方向压缩

令 $\mathcal Q$ 为所有具名部分赋值组成的有限集。每个坐标要么未读，要么已有一个实际值，因此

$$
|\mathcal Q|=\prod_{i\in I}(1+m_i).
\tag{TM.239}
$$

状态 $a\in\mathcal Q$ 的层数为 $|\operatorname{dom}(a)|$，未读坐标为 $U(a)$，选择与结果使它转到 $a\cup\{i=x\}$。每条边增加一个已读坐标，所以这是分层 DAG；每次执行至多访问每个状态一次。

定义节点占用质量 $M(a)$、选取流 $F(a,i)$ 与结果子流 $F(a,i,x)$。根质量和每个非终端节点的出流约束是

$$
\begin{aligned}
M(\varnothing)&=1,\\
\sum_{i\in U(a)}F(a,i)&=M(a),\\
\sum_{x\in X_i}F(a,i,x)&=F(a,i),\\
0\le F(a,i,x)&\le r_iF(a,i).
\end{aligned}
\tag{TM.240}
$$

一个非根部分赋值可以经不同最后坐标到达，因此入流守恒是

$$
M(a)=\sum_{i\in\operatorname{dom}(a)}
F(a\setminus\{i\},i,a_i)
\qquad(a\ne\varnothing).
\tag{TM.241}
$$

这里 $a\setminus\{i\}$ 删除坐标 $i$ 的赋值。全部变量非负。完整赋值 $v\in\Omega$ 的末端概率直接取

$$
\mu_v=M(v).
\tag{TM.242}
$$

**定理 4.9（部分赋值压缩精确保留末端法）。** 在假设26.2下，式(TM.240)—(TM.242)给出的末端法集合仍恰为 $\mathcal A$。

**证明：有序流到占用流。** 对历史 $h$ 记其部分赋值为 $a(h)$，并聚合

$$
\begin{aligned}
M(a)&=\sum_{h:a(h)=a}m(h),\\
F(a,i)&=\sum_{h:a(h)=a}f(h,i),\\
F(a,i,x)&=\sum_{h:a(h)=a}f(h,i,x).
\end{aligned}
\tag{TM.243}
$$

具有相同部分赋值的历史处于同一层，未读坐标和允许行集合也相同。对式(TM.232)求和立即给出式(TM.240)。每个到达非空 $a$ 的有序历史有唯一的最后坐标 $i$；按最后坐标分组，恰得式(TM.241)。在终端层，式(TM.243)就是式(TM.233)，所以末端法不变。

**证明：占用流到实际策略。** 在正质量状态与正选择流上，按

$$
\sigma(i\mid a)=\frac{F(a,i)}{M(a)},
\qquad
q(x\mid a,i)=\frac{F(a,i,x)}{F(a,i)}
\tag{TM.244}
$$

执行；零流处任选合法行。调度随机化与结果创新的可用时间按A卷定理4.7处理，因此策略满足完整档案条件容量。

对层数归纳。第零层到达空赋值的概率是1。假设第 $k$ 层每个状态 $a$ 的实际概率是 $M(a)$，则经其 $(i,x)$ 边的概率是 $F(a,i,x)$。到达第 $k+1$ 层某个状态 $b$ 的事件，按最后读取的坐标 $i\in\operatorname{dom}(b)$ 分为互斥分支，其总概率为

$$
\sum_{i\in\operatorname{dom}(b)}
F(b\setminus\{i\},i,b_i)=M(b).
\tag{TM.245}
$$

因此终端联合律恰为式(TM.242)。把这份实际策略展开成有序历史树，再使用式(TM.235)，也得到一份相应的有序可行流。两方向证明完成。$\square$

此压缩删去的是过去读取顺序，保留的是全部已读坐标及其实际值。它精确保留可实现的末端 joint-law 集合，不承诺保留原策略的读取顺序分布，亦不承诺保留原调度随机化档案。原策略可能用过去顺序携带内部记忆；在当前模型中，同一部分赋值的未来合法行集合不受这份记忆限制，条件平均和新的状态策略能保住末端法。若源相容性、费用或权限实际依赖顺序，这个论证就不再允许删除顺序。

状态数式(TM.239)仍可能随坐标数指数增长。精确有限表示的存在不意味着提取、存储、求解或核验成本很低。

#### 4.6.9 更小 DP 状态何时足够

**命题 4.10（保任务输出的状态压缩充分条件）。** 对一份有限视界历史树，设 $s=\psi(h)$ 为有限摘要。以下条件足够使历史流按摘要聚合，并能由摘要策略重新实现相同的末端任务输出律：

1. 相同摘要具有相同阶段（固定视界下等价于相同剩余步数）、相同合法具名动作及对应结果字母表。
2. 对每个合法动作，相同摘要具有相同非空凸条件行集合 $K(s,i)$；若要求线性流表示，再要求它是由有限线性约束给出的多面体。
3. 后继摘要可以从当前摘要、动作和本次结果公开更新。
4. 所需末端输出通过终端摘要因子化。
5. 各历史的合法行可以按节点独立拼接；所需保留的费用、权限和其他资源条件也已经纳入状态或保价的转移标签。

其中公开更新和末端因子化写为

$$
\psi(hix)=T(\psi(h),i,x),
\qquad
o(h)=\bar o(\psi(h))\quad\text{于终端历史}.
\tag{TM.246}
$$

**证明。** 同阶段同摘要的历史可以聚合节点、选择与结果流。对某个摘要及动作，其聚合后的条件行是原条件行的凸组合，组合权重与各选择流成比例；条件2保证它仍合法。条件3保证各条聚合边有确定的后继摘要，故入流和出流守恒相容。对聚合流归一化，并像式(TM.245)一样按阶段归纳，可构造一份摘要策略实现全部摘要占用质量。条件4随后给出原末端任务输出律。条件5保证这些局部选择确实能拼成同一份合法过程。$\square$

这是一组可直接检查的充分条件，不声称每个条件都是所有可能压缩方法的必要条件。若只需要一个损失期望，末端输出可取该损失；若需要全部具名坐标的 joint law，终端摘要就必须能恢复完整赋值。只保存 live-label mask，须另外证明该任务的合法域、后继和末端输出均在 mask 纤维上不变；不能把它自动称作保存了完整联合档案。

若需要保存每步历史相关费用，可将其作为摘要上确定的转移标签。这样保留各标签的期望累计值；若要保存整个费用路径的联合律，则应把累计记录并入状态及末端输出。行选择本身若另有费用，也必须作为动作信息保持，并检验聚合是否保价，不能从行的凸性自动推出。

完整观察者可以包含额外有限档案、剩余预算、权限、来源状态和已发生的调度记录。将这些必要信息与阶段一起加入状态，仍可使用相同的有限流方法；摘要必须由实际可访问档案取得，不能把隐藏的剩余预算或未读源值当作已知状态。若只能访问其后验，则应保留所需的共同后验，并重新检查有限性与公开更新。若这些信息决定合法行集合或未来查询而未被摘要保持，则上述条件失败，不主张它们可删。增加路径预算状态也不自动解除“所有分支必须共用同一外部模型索引”的非矩形约束。

#### 4.6.10 真实 Bellman 值、归一化行与贪心填充

对目标 $S\subseteq\Omega$，在完整部分赋值 $v$ 上置 $V(v)=\mathbf1_S(v)$。在非终端部分赋值上，真实最优成功概率满足

$$
V(a)=
\max_{i\in U(a)}\ \max_{q\in K_i}
\sum_{x\in X_i}q_xV(a\cup\{i=x\}).
\tag{TM.247}
$$

固定实际采样顺序时，只保留规定的下一坐标；其他调度限制必须进入合法动作集。

**证明。** 按剩余坐标数归纳。对任意策略，分解首次坐标选择与其结果行；每个后继的续接成功概率不超过归纳值，故根值不超过右侧。反向，每个 $K_i$ 紧且目标线性，内层最大值达到；坐标集有限，外层最大值也达到。选择一个达到最大值的坐标和行，再在每个后继使用归纳取得的最优策略。假设26.2允许独立拼接这些续接，故达到右侧。随机混合下一坐标不会超过最佳坐标值。$\square$

内层保留了 $\sum_xq_x=1$，不能替换为仅对各项分别使用上界 $r_i$ 后求和。

**引理 4.11（有上界归一化行的贪心值）。** 对实数 $v_1\ge\cdots\ge v_m$ 及 $1/m\le r\le1$，令
$k=\lfloor1/r\rfloor$、$\alpha=1-kr$。则

$$
\max_{\substack{q_j\ge0,\ \sum_jq_j=1\\q_j\le r}}
\sum_{j=1}^{m}q_jv_j
=r\sum_{j=1}^{k}v_j+\alpha v_{k+1}.
\tag{TM.248}
$$

当 $\alpha=0$ 时省略最后一项，尤其 $k=m$ 时不会使用不存在的 $v_{m+1}$。一个最优行依次给前 $k$ 项质量 $r$，给下一项质量 $\alpha$，其余为零。

**证明。** 如果 $j<\ell$、$q_j<r$ 且 $q_\ell>0$，将
$\min(r-q_j,q_\ell)$ 的质量从 $\ell$ 移到 $j$ 不降低目标。按有限次填充与清空得到上述行，其总质量恰为1，所有原子不超过 $r$。因此任意可行行的值均不超过这个行，后者又可行。值相同时可以有多个最优行，不主张唯一性。$\square$

A卷命题4.5的相等事件给出了两种递推的精确区别。读完第一个比特后，两个实际子问题的最优值均为 $3/4$，所以任意归一化第一行的加权值仍是 $3/4$。静态柱覆盖递推却给

$$
\min\left(1,\frac34\left(\frac34+\frac34\right)\right)=1.
\tag{TM.249}
$$

式(TM.219)比较可用覆盖的价格；式(TM.247)优化可执行的归一化条件行。两者使用不同的可行对象，不能仅因都写成树递推就等同。

真实动态规划还给出一类保因果约束的上界证书。若终端 $W(v)\ge\mathbf1_S(v)$，且每个非终端状态满足

$$
W(a)\ge
\sum_{x\in X_i}q_xW(a\cup\{i=x\})
\quad\forall i\in U(a),\ \forall q\in K_i,
\tag{TM.250}
$$

则按剩余步数归纳，每份合法策略均有 $\Pr(S)\le W(\varnothing)$。取 $W=V$ 达到真实最优值；因 $K_i$ 是多面体，验证式(TM.250)只需其有限顶点。该证书保留了各步的归一化行和实际后继结构，故能够表达柱覆盖中缺失的 $3/4$ 分离。

#### 4.6.11 固定顺序、预先混合顺序与自适应顺序

对一个固定排列 $\sigma$，令 $C_{\sigma,t}(x_1,\ldots,x_t)$ 为前 $t$ 个实际坐标 $\sigma(1),\ldots,\sigma(t)$ 取这些值的柱集，零长度柱为 $\Omega$。一份末端法能够按此固定顺序合法实现，当且仅当它是概率律并满足

$$
\mu(C_{\sigma,t}(x_1,\ldots,x_t))
\le r_{\sigma(t)}
\mu(C_{\sigma,t-1}(x_1,\ldots,x_{t-1}))
\quad\forall t,\ \forall(x_1,\ldots,x_t).
\tag{TM.251}
$$

必要性来自相应条件原子容量。充分性则用子柱质量除以正的父柱质量恢复条件行；父柱质量为零时，其所有子柱质量也为零，可在不可达节点任选合法行。这给出固定顺序法集合 $\mathcal A_\sigma$ 的直接线性表示。

若先用合法根随机化选定整份排列，再保持这个排列执行，末端法集合为各固定顺序多面体的凸包；若允许观察中途结果后再选下一坐标，则使用完整的 $\mathcal A$。因而

$$
\mathcal A_\sigma
\subseteq
\operatorname{conv}\!\left(\bigcup_\tau\mathcal A_\tau\right)
\subseteq\mathcal A.
\tag{TM.252}
$$

凸包的一个方向由根随机化实现；另一个方向按已选排列分组，条件平均同一排列下的合法行，再使用式(TM.251)。这里的根随机化在任何结果取得之前可用，不含未来结果源信息。

两坐标时，第一个坐标选定后，第二个坐标已经唯一，所以自适应顺序不超出这份根混合类。三坐标及以上可以在后续历史上选择不同未读坐标，但这一控制形式的增加本身不证明第二个包含严格。本节不借用其他输入—输出因果模型的严格分离，来替代当前 cap-only 采样模型所需的实例。

#### 4.6.12 最后一次读取给出的因果切面上界

对事件 $S\subseteq\Omega$，定义第 $i$ 个坐标在其余坐标赋值 $u$ 下的截面及其归一化容量：

$$
S_i(u)=\{x\in X_i:(x,u)\in S\},
\qquad
b_i(u)=\min\{1,r_i|S_i(u)|\}.
\tag{TM.253}
$$

其中 $(x,u)$ 按固定坐标身份拼成完整元组。令 $L$ 为实际最后读取的坐标身份。

**命题 4.12（实际最后读取的截面界）。** 任意合法逐步法满足

$$
\Pr(S)\le
\mathbb E\bigl[b_L(X_{-L})\bigr]
=\mathbb E\!\left[\min\{1,r_L|S_L(X_{-L})|\}\right].
\tag{TM.254}
$$

**证明。** 在最后坐标已选择而结果尚未取得的完整档案 $\mathcal G_{n-1}$ 中，$L$ 与其余坐标 $X_{-L}$ 都已知。只有 $S_L(X_{-L})$ 中的结果可以进入 $S$；每个结果条件质量至多 $r_L$，整行质量又恰为1。因此条件成功概率至多 $b_L(X_{-L})$。对档案取期望即得式(TM.254)。这不要求读取顺序固定，也不要求任何坐标独立。$\square$

式(TM.254)保留了末次坐标与既有赋值的共同档案关系。若只保留末端联合律 $\mu$，对每条实际执行路径都有
$b_L(X_{-L})\le\max_i b_i(X_{-i})$，故仍得到线性的末端法必要条件

$$
\mu(S)
\le
\sum_{v\in\Omega}\mu_v
\max_{i\in I}b_i(v_{-i}).
\tag{TM.255}
$$

再取最坏截面即有不依赖未知末端法的界

$$
\Pr(S)\le
\max_{i\in I}\ \max_{u\in\prod_{j\ne i}X_j}
\min\{1,r_i|S_i(u)|\}.
\tag{TM.256}
$$

式(TM.255)的 $\max_i$ 是对已发生过程作的上界松弛，不授权策略看完全部结果后再决定谁最后读取。式(TM.254)保留实际 $L$，式(TM.255)删去 $L$ 而保留末端赋值，式(TM.256)再删去赋值依赖；三者的保证依次变弱。

对两比特相等事件，每个截面都恰含一个结果，故式(TM.256)给 $3/4$，直接排除式(TM.224)的静态容量见证。这条切面证书使用了实际最后一次读取的归一化与可见过去；全局柱容量未保留这一条件关系。对其他事件，最坏截面可能给出1，届时需要使用保留更多历史的流或 Bellman 证书，不能将这条必要条件当作完整可实现性判据。

#### 4.6.13 与既有行为商、联合核和资源接口的连接

[第64篇“Adaptive core policy and continuous stoploss optima”](https://github.com/the-omega-institute/trureturing/blob/19a8543ea50538700a993a51989d9cbc7b5bf4fd/docs/reports/erdos7-odd-covering/problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md)第12—60行、第176—181行已经给出本节接口的具体任务使用：在先读完 core、再处理 terminal 的策略域中，剩余 core 名集合与仍匹配的原始标签 ID 组成缓存摘要 $q(h)=(U,A)$。该节在其给定 profile 满足叶容量蕴含祖先容量的条件下，优化真实归一化叶行；同后继 mask 的实际叶按准确重数分组，选定行再展开回实际叶，各后继策略自由拼接，有限归纳得到达到最优值的实际策略。完整采样值与实际历史始终保留给后续 tail 查询，缓存共用不替代它们。因此它已经承担 core-first 的任务摘要与真实 Bellman 最优策略，不是只有静态覆盖价格；但其 $(U,A)$ 只对所声明的 head 目标充分，不能被引用为任意未来任务或完整联合档案的通用充分摘要。

[第55篇“Adaptive read-once head orders with unrestricted tail comparison”](https://github.com/the-omega-institute/trureturing/blob/19a8543ea50538700a993a51989d9cbc7b5bf4fd/docs/reports/erdos7-odd-covering/problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md)第20—87行、第178—199行已经在原始标签、事件和确定条件容量固定的前提下，构造剩余坐标集合上的势 $Z(h)=B_{U(h)}(b(h))$，并证明每个合法所选行后的条件期望不增。其输入允许每个标签的坐标事件容量，较本节单个原子容量更一般；非负权重与递增凸终端函数共同进入比较。辅助 $U_p$ 对不同坐标独立，但同一坐标的辅助量在全部标签间共享，不能逐标签另抽，也不把辅助独立性赋给实际联合律。调度随机化须进入完整档案并在其后检查行容量，实际值与原始标签不能随分支重写。这是式(TM.250)所体现的逐步因果上界证书的一项既有具体使用。两篇正文均提供本库已交付的普通纸面数学；本节另补完整历史流与部分赋值 DAG 的精确投影及两方向实现，不将既有上界势、任务摘要或它们的计算实例计作新增 Lean 结果。

[ML 卷定理2.2与3.2](https://github.com/the-omega-institute/trureturing/blob/e25dea7a9919fcae53bb797f7740b0f5c99668ac/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)已经要求任务摘要保持读数、动作定义域、更新及费用，并以全部未来严格响应确定最粗自治表示。[Context Geometry 第3节](https://github.com/the-omega-institute/trureturing/blob/e25dea7a9919fcae53bb797f7740b0f5c99668ac/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md)已经组织了行为像、操作下降和保真运输。本节不重新把这些一般商原理计为新内容；A卷命题4.10是在有限随机行与占用流中加入凸聚合、末端输出量词和可拼接条件的具体使用。

ML 卷定义34.1、定理34.3已经给出联合后继核、公开更新与矩形性条件下的有限视界 Bellman 拼接，并明确将相关正文作为纸面推导。本题的每个 $q\in K_i$ 通过

$$
\mathcal K_q(x,s')=
q_x\mathbf1_{\{s'=T(s,i,x)\}}
\tag{TM.257}
$$

给出观测与后继状态的同一份联合核。cap-only 假设使这些核可逐历史拼接。原卷的鲁棒控制具有其自己的 $\inf/\sup$ 角色；本节由采样者选择行来最大化成功概率，因而使用式(TM.247)，不能不经映射照抄其他问题的优化量词。

已有 `DynamicClosureMinimality` 与 `ControlledBehaviorUniversality` 承担确定性动态闭包和行为表示接口；已有 `BellmanMaxEquation`、`BellmanContraction` 承担特定的折扣预测距离结论。这些声明不等于本节随机历史流、占用流聚合或给定完整档案下的条件容量已经得到新增形式化。其语义接口限定了上述复用范围。

**成熟文献的具体对应。** Yüksel—Saldi 的 [*Convex Analysis in Decentralized Stochastic Control, Strategic Measures and Optimal Solutions*, arXiv:1609.07685v2](https://arxiv.org/pdf/1609.07685v2)，PDF 第11页定理2.2以顺序条件核刻画战略测度；第11—12页定理2.3给独立随机化政策的积分表示；第12页定理2.4在经典信息结构且保留过去观测与动作的条件下证明战略测度凸性。这些结果承担完整信息结构、条件核和随机化的成熟框架；本节另外加入具名坐标只读一次与式(TM.232)的容量不等式。在这种对应中，可由控制者确定选择的是坐标和条件行，不是将受容量限制的结果输出确定化；定理2.3不能被解释为允许预先公开全部结果种子。

von Stengel 的 [*Efficient Computation of Behavior Strategies*, Games and Economic Behavior 14(2), 220—246 (1996)](https://doi.org/10.1006/game.1996.0050)是序列形式的成熟来源。这里的守恒与比值恢复具体对应其作者讲义 [*Extensive Games and the Sequence Form*](https://conferences.mpi-inf.mpg.de/adfocs-24/material/Bernhard/2ext-adfocs.pdf)：PDF 第25、27页给实现概率及 $Ex=e$，第29—30页给子实现概率除以前实现概率的行为策略恢复，并明确完美回忆条件；这些分别是讲义的第18、20、22—23张幻灯片。本节采用完整历史作为安全起点，再单独证明可用的压缩。讲义承担这份具体对应，不将它写成已逐字核对1996年原论文的定理；博弈序列形式本身也未直接给出当前结果容量和末端坐标律投影。

Mannor—Mebel—Xu 的 [*Lightning Does Not Strike Twice: Robust MDPs with Coupled Uncertainty*, arXiv:1206.4643](https://arxiv.org/pdf/1206.4643)，§4.1 定理5及证明位于 PDF 第4—6页，将剩余偏离次数 $d$ 加入状态，并通过状态 $(s,d)$ 与 $(s,d,a)$ 的完全信息顺序博弈进行倒向归纳。该节明确要求参数偏离在发生后被决策者观察，预算计算的是发生偏离的决策阶段数。它支撑“可观察剩余资源必须进入状态”的具体方法，不将任意隐藏预算或跨历史共享源约束自动化为同一种可见预算；其决策者—自然的优化量词也不同于本节自由选择 capped row 的模型。

本节的具体连接是：静态切分可运输一个对所有合法顺序成立的证书，但运输实际采样法还须保存完整条件关系；有限历史流将这些关系变成守恒、归一化和子流容量；在末端任务允许且后继结构相容时，可以消去读取顺序这部分记忆。对更完整的观察者，输出、来源、费用与权限须一起进入保留条件。相同末端数值、相同柱容量或相同递推外形，都不能代替这份关系运输证明。

## 5. 紧观察、近似策略与相容完成

### 5.1 分辨率、动态规划与拓扑：完整观察塔和任务充分商

“改变坐标不应改变拓扑”与“减少读数仍能正确决策”是两种不同保证。前者要求表示之间具有适当的可逆运输；后者只要求当前任务的奖励、合法动作和后继关系能够下降。动态规划认证这些关系的递推一致性，不会自行把一个多对一观察商变成同胚。

本节把二者接成一条精确的关系：在同一个紧 Hausdorff 载体上，一族具有闭纤维、相容且联合分离的观察可以恢复整个拓扑；但其中任一单层即使保留全部指定 Bellman 值，也仍可能丢失圆周方向。素数幂读数、圆周幂观察和通用 solenoid 分别给出离散精度、相位混叠和连续相容塔的具体对照。以下紧性桥、实例和连接论证为普通数学；已有源码的归属与适用范围列在本节末尾，没有把这些综合结论宣称为新增 Lean 定理。

#### 5.1.1 同一紧载体上的相容观察：实现性可以由有限交性质推出

设 $X$ 是紧 Hausdorff 空间，$I$ 是非空向上有向指标集。对每个 $i\in I$，给定 Hausdorff 空间 $X_i$ 和连续满射 $q_i:X\to X_i$，故 $X_i=q_i(X)$。当 $i\le j$ 时给定连续连接映射 $p_{ij}:X_j\to X_i$，满足

$$
p_{ii}=\operatorname{id},\qquad p_{ij}p_{jk}=p_{ik},\qquad q_i=p_{ij}q_j.
\tag{TM.311}
$$

细化不要求每一层都严格新增区别；恒等连接、重复观察及稳定平台都允许。重复层仍可承担核验、访问或费用，但不能据重复次数声称观察核严格变小。若新增约束改变合法载体，也须将载体的变化单独说明。

这里的共同来源是同一个 $X$，不是分别选取互不相关的局部状态空间。每个 $q_i$ 从紧空间连续满射到 Hausdorff 空间，因而已经是商映射；连接映射也自动满射，因为任意 $y_i=q_i(x)$ 都由 $q_j(x)$ 提升。

令

$$
L=\varprojlim_iX_i
=\{(y_i)\in\prod_iX_i:p_{ij}(y_j)=y_i\text{ 对所有 }i\le j\},
\qquad Q(x)=(q_i(x))_i.
\tag{TM.312}
$$

**命题 5.1。** 在这些条件下，$Q$ 满射。若观察族联合分离点，即

$$
\bigl(\forall i,\ q_i(x)=q_i(x')\bigr)\Longrightarrow x=x',
\tag{TM.313}
$$

则 $Q:X\to L$ 是同胚。

**证明。** 固定任意相容线程 $y=(y_i)\in L$，定义 $F_i=q_i^{-1}(\{y_i\})$。每个 $F_i$ 非空；由于单点在 $X_i$ 中闭且 $q_i$ 连续，$F_i$ 闭。对任意有限指标 $i_1,\ldots,i_n$，有向性给出共同上界 $j$。由 $q_j$ 满射，取 $x$ 使 $q_j(x)=y_j$。于是

$$
q_{i_k}(x)=p_{i_kj}(q_j(x))=p_{i_kj}(y_j)=y_{i_k},
\qquad x\in\bigcap_{k=1}^nF_{i_k}.
\tag{TM.314}
$$

因此这些闭集具有有限交性质。$X$ 的紧性推出 $\bigcap_iF_i\ne\varnothing$，即全部局部读数来自同一个实际状态，$Q$ 满射。联合分离给单射。$Q$ 按坐标连续，而 $L$ 是 Hausdorff 乘积的子空间；紧空间到 Hausdorff 空间的连续双射是同胚。证毕。

这里无需把“每个线程都有实现”另外当作前提；它已经由紧性、闭纤维及有向相容性推出。若没有联合分离，仍得到满射，但恢复的是共同观察核的商：

$$
x\sim x'\iff\forall i,\ q_i(x)=q_i(x'),
\qquad X/{\sim}\ \cong L.
\tag{TM.315}
$$

确实，$Q$ 的核正是该关系；它是到 Hausdorff 空间的连续满射，故诱导的商到 $L$ 为同胚。这一结论也区分了两种“完整”：实现性要求没有原载体之外的相容线程，分离性要求没有两个原状态共享同一个完整线程。

#### 5.1.2 不能只写“连续商”：非 Hausdorff 观察仍可能产生幽灵线程

原载体紧 Hausdorff，并不足以替任意商拓扑补出上一命题。下面的实际反例同时满足相容、满射、商映射和联合分离。

取 $X=[0,1]$，指标为所有有限子集 $F\subset X$，按包含关系排序。令

$$
X_F=F\sqcup\{*\},\qquad
q_F(x)=\begin{cases}x,&x\in F,\\ *,&x\notin F,\end{cases}
\tag{TM.316}
$$

并给 $X_F$ 真正的商拓扑。其非空开集恰是包含 $*$ 的子集：这种集合的原像是从区间中删掉有限个点；不含 $*$ 的非空集合的原像是有限集，不是区间中的开集。因此 $X_F$ 虽有限，却不是离散 Hausdorff 空间。

若 $F\subset G$，连接映射保留 $F$ 中的名字，把其余名字送到 $*$。它与 $q_F,q_G$ 交换，且连续、满射并为商映射。任意不同的 $x,y$ 由层 $F=\{x\}$ 分开，故整个观察族联合分离点。

然而全 $*$ 线程相容，每一层都有实际实现，其共同实现却要求

$$
x\in\bigcap_{F\subset X,\ F\text{ 有限}}(X\setminus F)=\varnothing.
\tag{TM.317}
$$

不存在这样的 $x$。失败点准确地落在 $q_F^{-1}(\{*\})=X\setminus F$ 非闭；紧性的闭集有限交性质无从应用。A卷命题5.1 中的 Hausdorff 观察商是一个清楚的充分条件，不能在使用该通用命题时静默删除。

同样，有向相容性也不是“各坐标分别能取到”几个字可以代替的。例如圆周的实部和虚部分别覆盖 $[-1,1]$，但两个区间任意选出的点不一定位于同一个圆周上。共同细化层及其相容关系承担了联合实现约束。

#### 5.1.3 紧度量空间上的定量桥：最坏纤维直径趋于零

若进一步给 $X$ 一个相容的度量 $d$，并明确要求 $X$ 非空，则同一观察塔具有定量形式。令

$$
E_i=\{(x,y)\in X\times X:q_i(x)=q_i(y)\},\qquad
\delta_i=\max_{(x,y)\in E_i}d(x,y).
\tag{TM.318}
$$

各 $E_i$ 包含非空对角线；Hausdorff 目标使等值关系闭，故 $E_i$ 是紧 $X\times X$ 的非空闭子集。距离连续，所以最大值存在且有限。若 $i\le j$，则 $E_j\subseteq E_i$，因此 $\delta_j\le\delta_i$。

联合分离进一步推出有向极限 $\delta_i\to0$：对A卷第5.2.1节的一般核缩小定理取开对角邻域 $U_\varepsilon=\{(x,y):d(x,y)<\varepsilon\}$。本节的连续满射、有向相容及共同分离正好是该定理的假设，故最终 $E_i\subseteq U_\varepsilon$。等价地，

$$
F_i^\varepsilon=E_i\cap\{(x,y):d(x,y)\ge\varepsilon\}
\tag{TM.319}
$$

最终为空。该一般定理的有限交性质证明只在A卷第5.2.1节给出。若允许空 $X$，可另约定所有 $\delta_i=0$；最大值证明本身不以空集为非空。

对任意连续实目标 $f$，定义一致模量

$$
\omega_f(s)=\max\{|f(x)-f(y)|:x,y\in X,\ d(x,y)\le s\},\qquad s\ge0.
\tag{TM.320}
$$

约束集合非空紧致，故最大值存在。紧度量空间上的连续函数一致连续，因而 $s\downarrow0$ 时 $\omega_f(s)\to0$。每层纤维内目标振幅不超过 $\omega_f(\delta_i)$。为每个 $y\in X_i$ 任取一个原像 $s_i(y)$，得到集合层解码器 $\bar f_i(y)=f(s_i(y))$，满足

$$
\sup_{x\in X}|f(x)-\bar f_i(q_i(x))|
\le\omega_f(\delta_i)\longrightarrow0.
\tag{TM.321}
$$

这里得到的是最坏纤维误差随细化消失。没有要求或证明选择 $s_i$ 连续、可计算，也没有给出带噪逆映射的稳定常数或达到某个精度的有效速率。若另有度量、算法与资源估计，它们须另行接入。这是“分辨率趋细能控制恢复误差”的正面结论，并不使单层商成为拓扑不变量。

#### 5.1.4 Bellman 关系怎样沿观察塔运输

先取有限非空的共同动作集 $A$，确定性转移 $T_a:X\to X$、阶段奖励 $r_a:X\to\mathbb R$ 和终端奖励 $g:X\to\mathbb R$。假设每层存在对应数据，使

$$
q_iT_a=T_{i,a}q_i,\qquad
r_a=r_{i,a}q_i,\qquad g=g_iq_i.
\tag{TM.322}
$$

定义有限时域值，其中 $n$ 计阶段奖励的次数，零时域仍有终端奖励：

$$
V_0=g,\qquad
V_{n+1}(x)=\max_{a\in A}\{r_a(x)+V_n(T_ax)\}.
\tag{TM.323}
$$

层上值 $V_{i,n}$ 使用同一递推。

**命题 5.2。** 对每层和每个有限时域，

$$
V_n=V_{i,n}q_i.
\tag{TM.324}
$$

**证明。** 直接应用 `finite_horizon_value_factorization`，取微状态 $X$、宏状态 $X_i$、抽象 $q_i$、共同有限非空动作集 $A$，并将转移、阶段奖励、终值分别取为 $T_a,r_a,g$ 与 $T_{i,a},r_{i,a},g_i$。式（TM.322）逐项给出其三个假设，因此得到式（TM.324）。相同代入满足 `finite_horizon_optimal_actions_descend`，因为每个动作的评分精确对应：

$$
r_a(x)+V_n(T_ax)
=r_{i,a}(q_i x)+V_{i,n}(T_{i,a}(q_i x)).
\tag{TM.325}
$$

于是最大化动作集合也完全相同。证毕。

上述已有结论不依赖拓扑。若 $T_a,r_a,g$ 连续，各 $q_i$ 为商映射，则它们下降后的函数连续；有限个连续动作值的最大值也连续。

由 $q_j$ 满射和式（TM.311）、（TM.322），还得到层间关系

$$
p_{ij}T_{j,a}=T_{i,a}p_{ij},\qquad
r_{j,a}=r_{i,a}p_{ij},\qquad
V_{j,n}=V_{i,n}p_{ij}.
\tag{TM.326}
$$

这是把粗层值函数拉回细层，而非随意把细层函数压到粗层。若 $q_i^*v=v\circ q_i$，Bellman 算子满足

$$
\mathcal B_Xq_i^*=q_i^*\mathcal B_i.
\tag{TM.327}
$$

在A卷命题5.1 的完整逆极限上，$T_a^L((y_i))=(T_{i,a}(y_i))$ 保持相容线程，且 $QT_a=T_a^LQ$。层上值在同一线程处相等；对不可直接比较的两个指标，取共同上界即可证明。因而整体动力学、线程动力学与指定任务的值通过同一组交换关系连接起来。

若动作合法性随状态变化，必须额外要求合法动作菜单沿观察纤维不变。随机转移的对应前提是整个转移概率律满足 $(q_i)_*P_a(x,\cdot)=P_{i,a}(q_ix,\cdot)$；只匹配某个奖励的期望不能代替它。有界奖励和折扣 $0\le\gamma<1$ 时，有限最大值的差不超过各动作评分差的最大值，故 $\|\mathcal Bv-\mathcal Bw\|_\infty\le\gamma\|v-w\|_\infty$。在连续奖励、连续确定转移的紧状态空间上，$\mathcal B$ 保持 $C(X)$，该空间的 sup 范数完备，收缩定理给唯一固定值。商的拉回因满射而保持 sup 范数，且与算子交换，故固定值满足相同下降关系。无折扣无限时域及平均奖励需要另外的存在和收敛条件。

#### 5.1.5 一个固定非恒定任务完整保值，却丢掉圆周方向

取

$$
X=S^1\times[0,1],\qquad Y=[0,1],\qquad q(z,y)=y.
\tag{TM.328}
$$

动作 $a\in\{0,1\}$，固定 $\alpha\notin2\pi\mathbb Q$，定义

$$
T_a(z,y)=\left(e^{i\alpha a}z,\frac{y+a}{2}\right),\qquad
r((z,y),a)=y,\qquad g(z,y)=y.
\tag{TM.329}
$$

奖励不是常数；动作会改变可见状态，并能使隐藏圆周坐标旋转。所有转移和奖励连续，且通过 $q$ 精确下降为 $\bar T_a(y)=(y+a)/2$、$\bar r(y,a)=y$、$\bar g(y)=y$。

不仅一般下降定理适用，这里还能算出全部时域值：

$$
V_n(z,y)=\bar V_n(y)
=(2-2^{-n})y+n-1+2^{-n},\qquad n\ge0.
\tag{TM.330}
$$

证明从 $V_0=y$ 出发。若 $V_n=c_ny+d_n$ 且 $c_n>0$，动作 $1$ 的继续值比动作 $0$ 大 $c_n/2$，所以

$$
c_{n+1}=1+c_n/2,\qquad d_{n+1}=d_n+c_n/2,
\quad c_0=1,\ d_0=0.
\tag{TM.331}
$$

解得式（TM.330），并得到每个正时域的最优首动作唯一为 $1$。

但 $S^1\times[0,1]$ 经 $(z,y)\mapsto(z,(1-s)y)$ 形变收缩到 $S^1\times\{0\}$，而区间可缩。因此

$$
\pi_1(S^1\times[0,1])\cong\mathbb Z,\qquad
\pi_1([0,1])=0;
\quad H_1(S^1\times[0,1];\mathbb Z)\cong\mathbb Z,
\quad H_1([0,1];\mathbb Z)=0.
\tag{TM.332}
$$

奖励、所有有限时域值及最优动作被精确保留，圆周仍被商掉。这说明任务逻辑的完整下降与拓扑信息的完整保留不能互相替代。若未来新增读取相位的奖励，旧表示就不再充分；改变的是任务族的量词范围。

#### 5.1.6 “所有任务”比“一个任务的所有时域”强在哪里

设 $q:X\to Y$ 是紧 Hausdorff $X$ 到 Hausdorff $Y$ 的连续满射。若要求每个连续实值终端任务都能够下降，即

$$
\forall g\in C(X,\mathbb R),\quad
\exists\bar g:Y\to\mathbb R,\qquad g=\bar gq,
\tag{TM.333}
$$

则 $q$ 必为同胚。证明：紧 Hausdorff 空间中的不同点可以由连续实函数分离；若 $q(x)=q(x')$，式（TM.333）会迫使全部连续实函数在两点相同，故 $x=x'$。于是 $q$ 为连续双射，紧到 Hausdorff 给同胚。反过来，同胚当然使每个连续终端任务下降，并保持连续性。

因此，在这个明确模型内，保留全部连续终端任务已经强到保留拓扑；保留一个固定任务的全部时域则远远不够。把“所有”放在任务族还是时域上，会改变结论。

真正的坐标旋转若由同胚给出，拓扑不变量随之保留。降分辨率一般是多对一商，不是可逆换坐标。若还要比较策略、成本或动力学，相关数据也必须一起运输。连续满射保留紧性及连通、道路连通的正向性质，但并不保证基本群、同调或维数不变；完整观察塔恢复 $X$，也不意味着任一单层已经恢复全部拓扑不变量。

还应区分“旋转完整对象”与“旋转能在固定观察商上更新”。对满射 $q:X\to Y$ 和操作 $R:X\to X$，存在 $\bar R:Y\to Y$ 使 $qR=\bar Rq$ 的充要条件是

$$
q(x)=q(y)\Longrightarrow q(Rx)=q(Ry).
\tag{TM.334}
$$

必要性代入交换关系即得；充分性令 $\bar R(q(x))=q(Rx)$，纤维条件保证定义无歧义。若 $q$ 是商映射且 $R$ 连续，这个下降映射连续。若 $R$ 是同胚，要保证 $\bar R$ 也可逆，还应要求 $R^{-1}$ 同样保持观察核；此时两个下降映射由满射性验证互为连续逆。

例如在平面上令

$$
R(x,y)=(-y,x),\qquad q(x,y)=x.
\tag{TM.335}
$$

$(0,1)$ 与 $(0,-1)$ 原读数相同，旋转后读数分别为 $-1$ 与 $1$，故固定横坐标观察下不存在 $\bar R$。把定义域限制为闭单位圆盘，反例仍成立且载体紧 Hausdorff。完整旋转保持原空间拓扑，并不替这个有损观察补回被遗忘的纵坐标。若同时运输观察，改用 $q'=qR^{-1}$，则严格有 $q'R=q$；这是更换表示后保留同一读数的交换关系。项目既有动态闭包中的 `InterventionClosed` 正是纤维保持条件，并以全部有限干预响应构造最小闭合细化。

#### 5.1.7 有限离散名字的连通性障碍，以及边界粘合

若 $X$ 连通而 $D_i$ 离散，则每个连续 $q_i:X\to D_i$ 都恒定：连续像连通，离散空间的非空连通子集只能是单点。无限多个这样的名字仍不能联合分离非平凡连通空间。有限离散空间的乘积及其逆极限全不连通，因为任意两个不同线程都能被某个坐标的开闭柱集分开。

所以“非平凡连通载体、连续有限离散读数、联合分离”不能同时成立。非恒定的数字量化可以在边界处不连续；或者必须给表示增加邻接、接缝或非离散的几何实现，不能把这些额外关系省略。

一个完整的粘合模型是二进制序列空间

$$
D=\{0,1\}^{\mathbb N_{\ge1}},\qquad
b(d)=\sum_{n\ge1}d_n2^{-n}.
\tag{TM.336}
$$

$D$ 是有限离散前缀的逆极限，紧致且全不连通。共享前 $N$ 位时，两读数之差至多 $2^{-N}$，所以 $b$ 连续；二进制展开给满射 $b:D\to[0,1]$。令 $d\sim e$ 当且仅当 $b(d)=b(e)$。不相同序列的等值恰发生在边界双表示：若首个差异处一侧为 $1$、另一侧为 $0$，该位差值只能由后面全部为 $0$ 与全部为 $1$ 的最大尾差抵消。因此

$$
u\,1\,000\cdots\sim u\,0\,111\cdots,
\qquad D/{\sim}\ \cong[0,1].
\tag{TM.337}
$$

最后一个同胚由紧空间到 Hausdorff 空间的连续满射为商映射得到。再识别区间两端得到 $S^1$；等价地，直接按 $d\mapsto e^{2\pi i b(d)}$ 的核作商。

这里没有违反离散名字的障碍：构造方向是全不连通代码空间经过明确的接缝商，成为连续几何。有限前缀函数在双表示接缝两侧可能不同，因此不能沿该商下降成区间上的连续离散读数。反向任意选取一个二进制表示，也不能据此取得全局连续截面。

这条机制在既有《QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION》39.16 节已有正文归属：离散细化、逆完成、边界识别与几何实现共同承担连续统的构造。有限图也须区分离散顶点集与加入连续边、胞腔后的几何实现。单凭“有无限多层”没有给出这些粘合关系。

#### 5.1.8 素数分辨率：纵向精度与横向互补是两种关系

取素数 $p$，深度 $k\ge0$，实际整数读数为

$$
q_{p,k}:\mathbb Z\to\mathbb Z/p^k\mathbb Z,
\qquad q_{p,k}(n)=n\bmod p^k.
\tag{TM.338}
$$

固定 $p$ 增大深度时，旧读数由新读数约化得到：$q_{p,k}=\pi_{k,k+1}q_{p,k+1}$。相应核是差值属于 $p^k\mathbb Z$；它随 $k$ 递减。已经拥有深层读数时，附加旧浅层读数不再切开新的纤维。$k=0$ 的模数为一，读数恒定。

不同素数的读数则是互补关系。若 $p\ne q$ 且 $k,\ell\ge1$，共同核为

$$
p^k\mathbb Z\cap q^\ell\mathbb Z=p^kq^\ell\mathbb Z,
\qquad
\mathbb Z/(p^kq^\ell)\mathbb Z
\cong\mathbb Z/p^k\mathbb Z\times\mathbb Z/q^\ell\mathbb Z.
\tag{TM.339}
$$

两个方向都严格增加相对单个读数的区分能力，例如 $0$ 与 $p^k$ 被第一个读数合并，却可由第二个分开。这个互补不是概率独立断言；尚未指定整数的概率律。

对任意正模数，$n\bmod L$ 能由 $n\bmod L'$ 因子化的充要条件是 $L\mid L'$：核包含要求 $L'\mathbb Z\subseteq L\mathbb Z$，反向则用自然约化。数字大小 $L'>L$ 不足以构成细化；例如模 $5$ 与模 $6$ 的观察互不细化。$\log L$ 是 $L$ 个可能标签的最大编码容量；只有指定共同概率律后才有实际 Shannon 熵，且 $H(N\bmod L)\le\log L$，等号要求该余数均匀。它不是每次取得一份读数就自动增加的信息量。

更一般地，正模数 $a,b$ 的实际联合像不是任意指定的乘积，而是

$$
\operatorname{im}(n\mapsto(n\bmod a,n\bmod b))
=\{(u,v):u\equiv v\pmod{\gcd(a,b)}\}
\cong\mathbb Z/\operatorname{lcm}(a,b)\mathbb Z.
\tag{TM.340}
$$

必要性由同一个整数在公共模数下的约化得到。充分性可写得直接：令 $d=\gcd(a,b)$、$a=da'$、$b=db'$，选整数代表 $u,v$。若 $v-u=dc$，求 $n=u+at$ 只需解 $a't\equiv c\pmod{b'}$；因为 $\gcd(a',b')=1$，Bézout 恒等式给出解。两个解之差同时被 $a,b$ 整除，恰等价于被最小公倍数整除。只有 $d=1$ 时相容约束才为空，联合像为整个乘积。

这与项目既有 `PrimeBudgetReadoutDichotomy`、`SamePrimeScaleRedundancy` 和 `CompatibleResidueJointImage` 的区分一致：增加同一素数的深度是纵向细化，加入不同素数是横向联合观察，公共因子承担必须保留的重叠约束。

#### 5.1.9 整数的每个有限读数可实现，不代表完成线程仍是整数

固定 $p$，所有深度读数联合分离整数：若 $p^k\mid(n-m)$ 对每个 $k$ 成立，只能有 $n=m$。但

$$
\mathbb Z\longrightarrow
\mathbb Z_p:=\varprojlim_k\mathbb Z/p^k\mathbb Z
\tag{TM.341}
$$

不是满射。原整数载体不是A卷命题5.1 中的紧载体；无论先给它离散拓扑，还是研究其 $p$-进观察拓扑，都不能把不存在的紧性放入证明。

一个具体非整数线程由 $p$-进展开

$$
\xi=\sum_{j\ge0}p^{2^j}
\tag{TM.342}
$$

给出。每个模 $p^k$ 的坐标由有限部分和实现，且坐标相容。它的数字在 $2^j$ 位为 $1$，其余位为 $0$，既有无限多个 $1$，也有任意高位置的 $0$。普通非负整数的 $p$-进数字最终全为 $0$；负整数 $-m$ 的数字最终全为 $p-1$，因为大深度代表 $p^N-m$ 的高位由一长串 $p-1$ 构成。故 $\xi$ 不来自任何普通整数。

整数像在 $\mathbb Z_p$ 中稠密：任意有限个相容坐标约束可归并到某个最高深度，再选该余数的整数代表即可。稠密不等于满射；选定 $p$-进距离后的完成化补入的是这些新线程，不能将其称为原整数已经具有的新有限位。

同时保留所有正模数时得到相容同余数据的完成。有限个不同素数方向由 CRT 拼接，全部深度再组成线程；原整数仍是这份完成中的指定像。有限阶段的可实现性、完整线程的存在以及线程是否属于原像，在这里有各自明确的量词。

还须区分 valuation 表与余数表。单个 $v_p(n)$ 只记录被 $p$ 整除的深度，不记录单位部分；例如 $v_p(1)=v_p(1+p)=0$，两者模 $p^2$ 却不同。全部素数的 valuation 若限定在普通正整数上，可凭有限支撑与唯一分解恢复整数；带符号整数还须保留符号，任意无限支撑 valuation 表也未必对应普通整数。$p$-进余数线程则在每个深度保留实际余数及其约化关系。这些结构之间可以另建恢复映射，但不能把 valuation、整数剩余类和 $p$-进状态当成同一份未经说明的数据。

#### 5.1.10 圆周幂观察：高频本身不等于更细分辨率

把圆周写成乘法群 $S^1$。对正整数 $k$ 定义 $h_k(z)=z^k$。其核是 $k$ 阶单位根群 $\mu_k$。对非空有限频率集合 $K\subset\mathbb N_{>0}$，联合读数满足

$$
\ker(h_K)=\bigcap_{k\in K}\mu_k=\mu_g,
\qquad g=\gcd(K),\qquad h_K(z)=(z^k)_{k\in K}.
\tag{TM.343}
$$

证明：$g$ 整除每个 $k$，故 $z^g=1$ 推出所有 $z^k=1$。反向由有限 Bézout 恒等式 $g=\sum_{k\in K}a_kk$ 得 $z^g=\prod_k(z^k)^{a_k}=1$。因此联合读数分离圆周点恰在 $g=1$ 时成立，并有显式恢复

$$
\sum_{k\in K}a_kk=1
\quad\Longrightarrow\quad
z=\prod_{k\in K}(z^k)^{a_k}.
\tag{TM.344}
$$

负指数在圆周上合法且连续。这给联合像上的连续逆，故 $h_K:S^1\to h_K(S^1)$ 为同胚；没有宣称全部自由输出元组都有共同原像。

例如 $4$ 和 $9$ 都不是素数，但 $9-2\cdot4=1$，所以

$$
u=z^4,\quad v=z^9
\quad\Longrightarrow\quad z=vu^{-2},
\qquad
h_{\{4,9\}}(S^1)=\{(u,v)\in S^1\times S^1:u^9=v^4\}.
\tag{TM.345}
$$

相容方程的必要性直接成立；反向若 $u^9=v^4$，令 $z=vu^{-2}$，则 $z^4=v^4u^{-8}=u$，且 $z^9=v^9u^{-18}=v$。这里 gcd 为一保证的是恢复与联合分离；它不像互素有限模数的 CRT 那样让整个自由乘积成为联合像。共同来源的类型不能混用。

单个频率越来越高并不自动细化旧观察。准确地说，

$$
h_\ell\text{ 可经 }h_k\text{ 因子化}
\quad\Longleftrightarrow\quad k\mid\ell.
\tag{TM.346}
$$

若 $k\mid\ell$，取幂 $\ell/k$ 即得因子化；反向要求 $\mu_k\subseteq\mu_\ell$，对原始 $k$ 阶单位根检查即得整除。因此倍频 $h_\ell$ 可以是 $h_k$ 的更粗后处理：$z$ 与多出的相位被合并。数字上的“更高”不是观察偏序中的“更细”；增加一份具有互补核的读数才可能解除混叠。

#### 5.1.11 通用 solenoid：相容圆周层、实流与隐藏同余在同一对象中

本项目已有一个成熟的连接例，不必另造容器。按既有 `UniversalSolenoid` 定义，令 $\mathbb T=\mathbb R/\mathbb Z$，

$$
\Sigma=
\{(\theta_m)_{m\ge1}\in\mathbb T^{\mathbb N_{>0}}:
n\theta_{mn}=\theta_m\text{ 对所有 }m,n\ge1\}.
\tag{TM.347}
$$

这里每一层本身是连续圆周，不是有限离散名字。相容条件是圆周乘法覆盖的连接关系；它们给乘积中的闭条件，所以 $\Sigma$ 紧致 Hausdorff。可见投影是 $\operatorname{pr}_1(\theta)=\theta_1$。已有实流为

$$
\iota(t)_m=t/m\pmod1,
\qquad \operatorname{pr}_1\iota(t)=t\pmod1.
\tag{TM.348}
$$

每个坐标连续，所以实流连续。其稠密性还可直接由有限坐标证明：给定 $\theta\in\Sigma$ 和有限指标集，取这些指标的共同倍数 $M$，为 $\theta_M$ 选实代表 $x$，令 $t=Mx$；相容关系使 $\iota(t)$ 在全部这些坐标上与 $\theta$ 完全相等。因此每个基本柱邻域都命中实流。实线连通，连续像连通，连通子集的闭包连通，故 $\Sigma$ 连通。这与既有 `continuous_realFlow`、`denseRange_realFlow` 及连通实例一致。

同一个可见投影的核则由相容同余数据给出。设

$$
\widehat{\mathbb Z}_{\rm comp}
=\{(a_m):a_m\in\mathbb Z/m\mathbb Z,
a_{mn}\bmod m=a_m\}.
\tag{TM.349}
$$

映射 $a\mapsto(a_m/m\pmod1)_m$ 单射，像恰为 $\ker\operatorname{pr}_1$：如果 $\theta_1=0$，则 $m\theta_m=0$，每个 $\theta_m$ 是唯一模 $m$ 余数对应的 $m$ 阶扭点；相容性正好成为余数约化关系。投影满射由式（TM.348）给出。因而在这里明确的群层上有

$$
0\longrightarrow\widehat{\mathbb Z}_{\rm comp}
\longrightarrow\Sigma\xrightarrow{\operatorname{pr}_1}\mathbb T
\longrightarrow0.
\tag{TM.350}
$$

这正是既有 `CongruenceData` 与 `congruence_solenoid_short_exact` 的元素级短正合接口。本节不把这份声明升级成未经核对的额外拓扑同构，也不从连通性擅自推出道路连通性。

既有 `SolenoidCharacter` 还分类了 $\Sigma$ 到 $\mathbb T$ 的连续加法特征：它们由有理数索引。若 $r=a/b$，则

$$
\chi_{a/b}(\theta)=a\theta_b,
\qquad \chi_{a/b}(\iota(t))=(a/b)t\pmod1.
\tag{TM.351}
$$

表达不依赖分数表示，因为 $a/b=c/d$ 时 $ad=bc$，在共同坐标 $bd$ 上有 $a\theta_b=ad\theta_{bd}=bc\theta_{bd}=c\theta_d$。每个连续特征都具有且只具有这种形式，是所引既有分类结果，而非本节凭公式声称的新结论。

于是，可见连续相位、隐藏的相容同余、连续实流及有理特征频率确实存在于同一个已声明对象中。有限离散核不能单独承担整个连通空间；圆周层的连接关系与全部相容条件共同组织整体。这里的“频率”是特征沿选定实流的斜率，没有将其认作未经建模的物理波、能量或时钟速率。

#### 5.1.12 结果归属与本节的适用范围

源码归属固定于提交 `19a8543ea50538700a993a51989d9cbc7b5bf4fd`。`D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean` 的 `ThreadComplete`、`SeparatesStates` 与 `stateThread_bijective_iff_complete_and_separates`（58–109 行），以及 `D5/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion.lean` 的 `completion_map_equiv_iff`（29–82 行），承担类型层的相容线程与等价条件；它们没有假设紧 Hausdorff 拓扑，也没有自动给出本节的有限交性质与同胚升级。

紧度量纤维直径的有向极限在A卷第5.1.3节由A卷第5.2.1节的一般核缩小定理代入开度量对角邻域得到。`D5/S3/Observer/MetricGeometry/FiniteWordFiberDiameter.lean`（21–56 行）给有限观察前缀的折扣预测距离界，距离和假设与本节不同；`D5/S3/ConceptDynamics/EscapeSpectrum/CompactResidualFiniteCompletion.lean`（43–71 行）在紧残差域与开放分离条件下抽取有限预算，其对象是既定目标的缺陷关系。本节没有把二者冒认为一般紧度量观察塔直径定理的同形所有权。

`D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization.lean` 的 `finite_horizon_value_factorization`（27–70 行）和 `D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent.lean` 的 `finite_horizon_optimal_actions_descend`（94–163 行）直接承担有限非空动作下的值及最优动作下降。`D5/S3/Observer/DynamicProgramming/DiscountedBellmanContraction.lean` 的声明限于有限状态、有限动作的随机转移收缩；本节提及一般紧空间上连续确定转移的折扣扩展采用普通 sup 范数证明，没有将其归成该有限状态声明的逐字结论。

`D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean` 的 `InterventionClosed`（36–41 行）、`DynClosure`（43–47 行）和 `dynamic_closure_is_least`（79–99 行）承担干预保持观察纤维及最小闭合细化；旋转的固定商反例与同时运输观察的式子在本节直接验证。

`D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.lean`（21–54 行）已有自然数截断每层满射而最大线程不在原像中的反例；其非紧载体不与A卷命题5.1 冲突。`D5/S1/Solenoid/Connectivity/FiniteNameInverseLimitNoGo.lean`（28–47 行）及 `D5/S3/ConceptDynamics/Topology/ConnectedDiscreteNamingDiscontinuity.lean`（29–45 行）承担有限离散名字的连通性障碍。二进制完成后识别边界双表示的机制已有 `docs/develop/theory/QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md` 39.16 节（35395–35448 行）的正文归属。

素数与联合像接口分别来自 `D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.lean`（44–100 行）、`SamePrimeScaleRedundancy.lean`（43–64、92–123 行）及 `CompatibleResidueJointImage.lean` 的 `joint_residue_image_eq_compatible_pairs`（49–130 行）。本节所用正模数 CRT 是后者允许任意自然模数的陈述之受限情形；圆周幂读数的 gcd 核、$4/9$ 恢复及其联合像由本节直接证明，不借用整数 CRT 的自由乘积结论。

`D5/S1/Dynamics/UniversalSolenoid.lean`（14–18、64–123、132–188 行）给原载体、同一可见投影、实流、稠密性和连通性；`D5/S1/Solenoid/ExactSequence.lean` 的 `CongruenceData`（21–26 行）与 `congruence_solenoid_short_exact`（177–186 行）给同一投影的元素级核与满射接口。`D5/S1/Dynamics/SolenoidCharacter.lean` 的 `continuous_solenoid_characters_are_rational`、`characterEquivRational` 给连续特征分类；`D5/S1/Solenoid/Connectivity/CharacterCompletionDuality.lean` 明确直接复用该分类，不将其作为第二份独立证明。

本节据此保留三个不能互相代替的保证：相容观察塔的完整拓扑恢复、指定任务的 Bellman 下降，以及数字完成后经明确接缝得到的连续实现。它们可以在同一研究中组合，但每一步都要指明恢复的是原状态、任务行为、相容线程，还是带新边界识别的商空间。

### 5.2 紧观察塔的一致分辨与有限时域值稳定性

一族观察能够最终分开任意两个状态，并不单凭定义给出统一的有限分辨率。紧致性补上这一步：若观察连续、阶段有向细化、全部阶段共同分离点，则任一给定的统一精度都能在一个有限阶段达到。有限连续标签因而能够精确下降；连续实值任务能够一致近似。把这个结果用于 Bellman 递推，还须保留共同动作、合法性和实际续值上的误差。

以下均为普通数学推导。有限阶段不必是有限集合；“一个阶段”也不等于已有取得该阶段的计算预算。

#### 5.2.1 有向观察核的一致缩小

设 $X$ 是非空紧 Hausdorff 空间，$I$ 是非空有向预序集。对每个 $i\in I$，给定到 Hausdorff 空间 $X_i$ 的连续满射

$$
q_i:X\longrightarrow X_i.
$$

若 $i\le j$，存在连接映射 $r_{ji}$，满足 $q_i=r_{ji}q_j$。设全部 $q_i$ 共同分离点，即

$$
(\forall i\in I,\ q_i(x)=q_i(x'))\Longrightarrow x=x'.
$$

记观察核和对角线为

$$
E_i=\{(x,x'):q_i(x)=q_i(x')\},\qquad
\Delta_X=\{(x,x):x\in X\}.
$$

则对于任一包含整个 $\Delta_X$ 的开集 $U\subseteq X^2$，存在 $i_0$，使

$$
E_i\subseteq U\qquad(i\ge i_0).
\tag{TM.449}
$$

证明：$X_i$ 为 Hausdorff，故 $E_i$ 闭；相容性给出 $j\ge i\Rightarrow E_j\subseteq E_i$。反设没有任何 $E_i$ 包含于 $U$。紧集 $K=X^2\setminus U$ 上的闭集 $E_i\cap K$ 全非空，而且任意有限个阶段有共同上界，故这些闭集具有有限交性质。紧致性给出一点属于全部 $E_i\cap K$。共同分离性使该点属于 $\Delta_X$，与 $K\cap\Delta_X=\varnothing$ 矛盾。找到一个阶段后，其全部细化阶段仍满足同一包含关系。

若 $X$ 进一步为紧度量空间，令

$$
\eta_i=\max\{d(x,x'):(x,x')\in E_i\}.
$$

这里最大值存在，因为 $E_i$ 是非空紧集。对任意 $\varepsilon>0$，取 $U=\{d(x,x')<\varepsilon\}$，由式（TM.449）得到

$$
\eta_i\longrightarrow0
\quad\text{沿有向集 }I\text{ 收敛}.
\tag{TM.450}
$$

这是观察纤维直径的统一收敛；没有另行给出达到精度 $\varepsilon$ 所需阶段的有效算法或成本界。

#### 5.2.2 有限连续标签与合法性在一个阶段下降

设 $D$ 是有限离散空间，$f:X\to D$ 连续。则存在 $i_0$，使每个 $i\ge i_0$ 都有唯一连续映射 $f_i:X_i\to D$，满足

$$
f=f_iq_i.
\tag{TM.451}
$$

证明：集合 $U_f=\{(x,x'):f(x)=f(x')\}$ 是包含对角线的开集。由式（TM.449），某个阶段以后 $E_i\subseteq U_f$，即 $f$ 在每条 $q_i$ 纤维上常值。满射性给出唯一集合映射 $f_i$。连续满射 $q_i$ 从紧空间到 Hausdorff 空间，是闭映射，因而是商映射；由 $f_iq_i=f$ 连续，得 $f_i$ 连续。

对有限非空动作集 $A$，若合法动作集合

$$
L:X\longrightarrow\mathcal P_{\ne\varnothing}(A)
$$

作为有限离散值映射连续，便同样在一个阶段精确下降。有限时域中的有限多个 $L_t$ 可取各自阶段的共同上界。因此同一纤维中的全部状态具有相同合法动作集合。若 $X$ 连通，则这样的连续 $L$ 必须常值；闭条件定义的合法区域不自动使 $L$ 连续。

编码边界也由这两个假设直接区分。固定 $k\ge2$，无限 $0/1$ 串中禁止连续 $k$ 个 $1$ 的子空间 $Y_k\subseteq\{0,1\}^{\mathbb N}$ 闭而紧，其有限支撑码稠密，但不等于整个载体。对 $k=2$，设整数编码权 $w_0=1,w_1=2,w_{n+2}=w_{n+1}+w_n$；其模 $2$ 周期为 $1,0,1$。仅在位置 $3t$ 为 $1$ 的有限码在低位优先、其余位补零的乘积拓扑中趋于零码，而所编码整数的奇偶标签恒为 $1$，零码标签为 $0$。因此奇偶标签在这个稠密有限码域上已经不连续，不能连续延拓到 $Y_2$，也不能借式（TM.451）获得有限位恢复。若改用带 END 标记的有限串前缀拓扑，每个完成的有限码都是孤立点，域为无限离散空间而非紧空间；所有标签虽逐点连续，仍无统一有限读取深度的保证。具体地，任给读取深度 $N$，在 $N$ 之后选择一处奇权位置与一处偶权位置，两个单 $1$ 合法码的前 $N$ 位同为零，而奇偶标签不同。两种表示改变了连续性与紧致性，不能互换假设。

#### 5.2.3 实值任务的一致近似与选择的边界

对连续 $V:X\to\mathbb R$，定义纤维振幅

$$
\operatorname{osc}_{E_i}(V)
=\max_{(x,x')\in E_i}|V(x)-V(x')|.
$$

对任意 $\varepsilon>0$，集合 $\{|V(x)-V(x')|<\varepsilon\}$ 是对角线开邻域，故式（TM.449）给出

$$
\operatorname{osc}_{E_i}(V)\longrightarrow0.
\tag{TM.452}
$$

每条非空纤维紧，故可定义

$$
m_i(y)=\min_{q_i(x)=y}V(x),\qquad
M_i(y)=\max_{q_i(x)=y}V(x),\qquad
v_i(y)=\frac{m_i(y)+M_i(y)}2.
$$

逐纤维比较即得

$$
\|V-v_iq_i\|_\infty
\le\frac12\operatorname{osc}_{E_i}(V).
\tag{TM.453}
$$

这是集合映射上的一致估计，不声称上述 $v_i$ 连续，也不提供连续代表点。若 $X$ 为紧度量空间，记

$$
\omega_V(u)=\sup_{d(x,x')\le u}|V(x)-V(x')|.
$$

则 $\omega_V(u)\to0$，且 $\operatorname{osc}_{E_i}(V)\le\omega_V(\eta_i)$。任取右逆 $s_i:X_i\to X$，有

$$
\|V-(V\circ s_i)q_i\|_\infty\le\omega_V(\eta_i).
\tag{TM.454}
$$

任意右逆只是集合选择；其连续性、可测性和可计算性须另证。

#### 5.2.4 代表点粗模型的有限时域值收敛

现在令 $X$ 为紧度量空间，固定有限时域 $H$ 和共同的有限非空动作集 $A$。对 $0\le t<H$、$a\in A$，给定连续转移 $F_t(\cdot,a):X\to X$、连续奖励 $r_t(\cdot,a):X\to\mathbb R$，以及连续终值 $h:X\to\mathbb R$。定义

$$
V_H=h,\qquad
V_t(x)=\max_{a\in A}\{r_t(x,a)+V_{t+1}(F_t(x,a))\}.
\tag{TM.455}
$$

有限个连续函数的最大值连续，故倒推得到全部 $V_t$ 连续且有界。

任取右逆 $s_i$，定义同一个代表点粗模型

$$
\bar r_{i,t}(y,a)=r_t(s_i y,a),\qquad
\bar F_{i,t}(y,a)=q_iF_t(s_i y,a),\qquad
\bar h_i(y)=h(s_i y),
$$

并用这些函数作同样的 Bellman 递推，得到 $\bar V_{i,t}$。此递推在全部有界函数上进行；不预设粗函数连续。

令 $e_{i,t}=\|V_t-\bar V_{i,t}q_i\|_\infty$，则

$$
e_{i,H}\le\omega_h(\eta_i),\qquad
e_{i,t}\le e_{i,t+1}+\omega_{V_t}(\eta_i).
\tag{TM.456}
$$

证明：对 $y=q_i(x)$，细 Bellman 值 $V_t(s_i y)$ 与粗值 $\bar V_{i,t}(y)$ 的奖励相同，各动作的续值差至多 $e_{i,t+1}$。由

$$
|\max_a u_a-\max_a v_a|\le\max_a|u_a-v_a|
$$

可得 $|V_t(s_i y)-\bar V_{i,t}(y)|\le e_{i,t+1}$。又 $q_i(s_iq_i x)=q_i x$，故 $d(x,s_iq_i x)\le\eta_i$，从而 $|V_t(x)-V_t(s_iq_i x)|\le\omega_{V_t}(\eta_i)$。三角不等式即给出递推；终值按式（TM.454）处理。

因此

$$
e_{i,t}\le\sum_{s=t}^{H}\omega_{V_s}(\eta_i)
\longrightarrow0.
\tag{TM.457}
$$

收敛对同一固定模型、同一固定有限时域成立，而且估计与右逆的具体选择无关。它没有把粗模型的一个转移当成细模型的精确路径提升。

若希望只用原始数据控制误差，定义对动作取最大后的统一模量

$$
\omega_{r,t}(u)=\max_a\sup_{d(x,x')\le u}|r_t(x,a)-r_t(x',a)|,
$$

$$
\omega_{F,t}(u)=\max_a\sup_{d(x,x')\le u}d(F_t(x,a),F_t(x',a)).
$$

逐动作比较给出

$$
\omega_{V_t}(u)
\le\omega_{r,t}(u)+\omega_{V_{t+1}}(\omega_{F,t}(u)),
$$

故也有

$$
e_{i,t}\le e_{i,t+1}
+\omega_{r,t}(\eta_i)
+\omega_{V_{t+1}}(\omega_{F,t}(\eta_i)).
\tag{TM.458}
$$

若奖励、转移和终值具有相应 Lipschitz 常数，取

$$
L_H=L_h,\qquad
L_t=L_{r,t}+L_{F,t}L_{t+1},
$$

则 $V_t$ 为 $L_t$-Lipschitz，且

$$
e_{i,0}\le\eta_i\sum_{t=0}^{H}L_t.
\tag{TM.459}
$$

若动作集合依赖状态，但每个 $L_t$ 是A卷第5.2.2节所述连续有限值映射，则在全部合法性标签已经下降的阶段取粗合法集 $\bar L_{i,t}(y)=L_t(s_i y)$。每条纤维中的合法集相同，且细 $V_t$ 仍连续：在每一点附近合法集局部常值，再取有限最大值。式（TM.456）—（TM.457）的证明保持有效。式（TM.458）中对任意度量近点的模量估计原先使用共同动作，不能在跨越不同合法集时原样套用。

#### 5.2.5 非线性 Bellman 缺陷的累加

令 $P_i v=vq_i$。考虑细算子 $T_t$、粗算子 $\bar T_{i,t}$ 及其实际递推

$$
V_t=T_tV_{t+1},\qquad
\bar V_{i,t}=\bar T_{i,t}\bar V_{i,t+1}.
$$

假设细算子对一致范数不扩张，并且在递推实际使用的每个续值上满足

$$
\|T_tP_i\bar V_{i,t+1}
-P_i\bar T_{i,t}\bar V_{i,t+1}\|_\infty
\le\varepsilon_{i,t},
$$

$$
\|V_H-P_i\bar V_{i,H}\|_\infty\le\varepsilon_{i,H}.
$$

则插入 $T_tP_i\bar V_{i,t+1}$ 并用三角不等式，得到

$$
\|V_t-P_i\bar V_{i,t}\|_\infty
\le\|V_{t+1}-P_i\bar V_{i,t+1}\|_\infty+\varepsilon_{i,t}.
$$

归纳给出

$$
\|V_0-P_i\bar V_{i,0}\|_\infty
\le\sum_{t=0}^{H}\varepsilon_{i,t}.
\tag{TM.460}
$$

共同动作的确定性 Bellman 算子确实不扩张：每一动作的续值差不超过输入函数的一致距离，取同一动作集的最大值保留该上界。无需在所有有界粗函数上统一控制缺陷，但必须控制实际使用的续值；仅在一个无关测试函数上检查交换关系不足以进行这项归纳。

折扣情形中，若 $T$ 为 $\beta$-收缩，$0\le\beta<1$，且 $V^*=TV^*$、$\bar V^*=\bar T\bar V^*$ 为有界不动点，那么由

$$
\|TP_i\bar V^*-P_i\bar T\bar V^*\|_\infty\le\varepsilon
$$

推出

$$
\|V^*-P_i\bar V^*\|_\infty\le\frac{\varepsilon}{1-\beta}.
\tag{TM.461}
$$

证明是在同一个三角不等式中得到 $e\le\beta e+\varepsilon$。如还要断言不动点存在，可在全部有界函数的完备一致范数空间上，以有界奖励和合法的折扣 Bellman 算子应用收缩定理；不得在未经证明完备或未经证明算子保持的函数类上直接引用它。

#### 5.2.6 值逼近可以接出近最优策略，但不自动给精确或连续提升

在A卷第5.2.4节的共同动作条件下，定义细动作值

$$
Q_t(x,a)=r_t(x,a)+V_{t+1}(F_t(x,a)).
$$

相应粗动作值为

$$
\bar Q_{i,t}(y,a)=\bar r_{i,t}(y,a)
+\bar V_{i,t+1}(\bar F_{i,t}(y,a)).
$$

令 $\bar\pi_{i,t}(y)$ 是粗 Bellman 递推中任一最大化动作，令细策略 $\pi_{i,t}(x)=\bar\pi_{i,t}(q_i x)$。有限非空动作集保证最大化动作存在。由三次相减可得

$$
|Q_t(x,a)-\bar Q_{i,t}(q_i x,a)|\le\delta_{i,t},
$$

$$
\delta_{i,t}=\omega_{r,t}(\eta_i)
+\omega_{V_{t+1}}(\omega_{F,t}(\eta_i))+e_{i,t+1}.
$$

粗动作最大化并在两端使用该误差界，得到

$$
0\le V_t(x)-Q_t(x,\pi_{i,t}(x))\le2\delta_{i,t}.
$$

若 $W_{i,t}$ 为此策略在真实细动力学上的性能，终值仍为 $h$，则

$$
V_t(x)-W_{i,t}(x)
\le2\delta_{i,t}
+(V_{t+1}-W_{i,t+1})(F_t(x,\pi_{i,t}(x))).
$$

故

$$
0\le\|V_0-W_{i,0}\|_\infty
\le2\sum_{t=0}^{H-1}\delta_{i,t}\longrightarrow0.
\tag{TM.462}
$$

这是增加了逐动作比较与真实策略递推后的性能保证；仅有值函数一致近似的陈述并不包含这些条件。这里的策略首先是集合映射，不据此宣称连续、可测、可计算，也不宣称达到精确最优。

#### 5.2.7 同一紧观察塔中的四个边界例子

取 $X=[-1,1]$，$n\ge2$，定义

$$
q_n(x)=\operatorname{sgn}(x)\max\{|x|-1/n,0\},
\qquad X_n=[-1+1/n,1-1/n].
\tag{TM.463}
$$

这是连续满射，将 $[-1/n,1/n]$ 合并为一点，其余纤维均为单点，故 $\eta_n=2/n$。若 $m\ge n$，取

$$
r_{mn}(y)=\operatorname{sgn}(y)
\max\{|y|-(1/n-1/m),0\},
$$

便有 $q_n=r_{mn}q_m$。又 $q_n(x)\to x$，故全部阶段共同分离点。以下未另指定的转移取恒等映射，终值取零。

**一致缩小不产生连续代表点。** 对任一右逆 $s_n$，$y>0$ 时强制 $s_n(y)=y+1/n$，$y<0$ 时强制 $s_n(y)=y-1/n$。在零点的左右极限分别为 $-1/n$ 与 $1/n$，故没有连续右逆。取所有奖励和终值为零，细粗值仍完全相同。因此值的精确恢复也不蕴含连续状态选择。

**连续值与一致近似不产生连续最优动作或精确动作下降。** 取单步问题、全局动作 $A=\{+,-\}$、奖励 $r(x,+)=x$、$r(x,-)=-x$、终值零。其连续值为 $V(x)=|x|$。任何精确最优策略在 $x>0$ 必选 $+$，在 $x<0$ 必选 $-$，所以不可能连续到离散动作空间。若中央纤维代表点取零，则 $\bar V_n(q_n x)=0$ 于中央纤维，其他点与 $V(x)$ 相同，一致误差恰为 $1/n$；但该纤维上的任一个固定动作都在某一侧严格次优。误差趋零可以支持近最优性能，不能把一个粗动作提升为整条纤维上的精确最优动作。

**不连续合法性破坏值收敛。** 仍取单步，动作名为 $a,b$，奖励 $r(x,a)=0$、$r(x,b)=1$ 均连续，终值零；规定 $x\le0$ 只允许 $a$，$x>0$ 允许 $a,b$。真实值为 $\mathbf1_{(0,1]}(x)$。中央代表点取零，则粗合法集只有 $a$，粗值在整个中央纤维为零，而 $0<x\le1/n$ 的真实值为一。因此所有 $n$ 的一致误差均为一。取正代表点又会把 $b$ 当成在该纤维普遍合法；这会在负半边产生不合法的策略。问题是合法性没有下降，而不是奖励缺少连续性。

**固定时域收敛不推出全部时域的一致收敛。** 取唯一动作、恒等转移、每步奖励 $r(x)=x$、终值零，中央代表点取零。时域 $H$ 的真实值为 $Hx$，中央纤维上的粗值为零，其他点完全相同，故一致误差为 $H/n$。每个固定 $H$ 都收敛，但取 $H=n$ 后误差恒为一。

#### 5.2.8 已有数学接口与结论范围

以下源码对应不可变快照 `9d27c77aa30f936d272e367f5e24f9c04fe1fbcb`：

| 已有接口 | 可直接承担的内容 | 本段不据此冒领的内容 |
|---|---|---|
| `D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization.lean` 中 `finite_horizon_value_factorization` | 共同有限动作、奖励与终值精确下降、转移精确交换时，任意有限时域的值精确下降 | 紧观察塔、近似模型、非连续合法性或一致误差率 |
| `D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent.lean` 中 `finite_horizon_optimal_actions_descend` | 上述精确条件下，全体最优动作集合精确下降，比单纯值下降更强 | 连续最优选择、近似策略性能或未经保持的状态依赖合法性 |
| `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.lean` 中 `intertwining_defect_telescope`、`norm_intertwining_defect_le` | 连续线性映射的交换缺陷展开及带算子范数的传播界 | 非线性 Bellman 最大值算子的直接定理；式（TM.460）另外用不扩张性证明 |
| `D5/S3/Observer/DynamicProgramming/DiscountedBellmanContraction.lean` 中 `discounted_bellman_contraction_and_unique_fixed_point` | 有限离散状态、有限动作、非负归一化转移与 $0<\gamma<1$ 下的折扣收缩及唯一不动点 | 一般紧商空间的函数类、任意选择器的正则性或现成的跨表示缺陷界 |
| `D5/S1/Dynamics/ProfiniteCharacter.lean` 中 `continuous_character_factors_through_residue` | 相容剩余类整数的连续群特征经一个有限剩余坐标分解 | 任意观察塔的有限标签定理；其目标为圆群，不能借式（TM.451）的有限标签结论省略所用群结构 |

本段没有把这些已拥有的精确结果再次命名为新定理。本节围绕式（TM.449）—（TM.463）给出用于衔接的普通证明与反例，不宣称完成新增 Lean 核验，也不据此宣称文献原创。这里成立的统一关系是：紧致且共同分离的观察使连续任务的隐藏纤维振幅一致消失；共同合法动作与稳定递推再把这份几何精度转成固定时域的值和性能精度。连续选择、精确路径提升、统一无限时域及实际取得成本仍须各自的附加条件。

### 5.3 同一模型的读数逆极限：新增不动点与一点紧化

继续使用A卷第2.6节允许正反平移的整数模型。对 $N\ge0$，取有限未来窗口读数

$$
q_N(n)=\bigl(\mathbf1_{\{n+k=0\}}\bigr)_{|k|\le N},
\qquad B_N=q_N(\mathbb Z).
$$

$B_N$ 包含窗口内 $2N+1$ 个位置上的全部单脉冲，以及全零向量，故 $|B_N|=2N+2$。窗口限制给出满射

$$
r_N:B_{N+1}\to B_N.
$$

它保留内侧脉冲，将两个端点脉冲送为零，并把零送为零。令

$$
L=\varprojlim(B_N,r_N).
$$

定义 $X=\mathbb Z\sqcup\{\infty\}$ 到 $L$ 的映射：整数 $n$ 对应 $(q_N(n))_N$；$\infty$ 对应所有窗口均为零的相容族。

这个映射是双射。一份相容族若某窗口在位置 $k$ 出现 $1$，则所有更大窗口都必须保留该脉冲；每层至多一个脉冲，故全族唯一对应整数 $n=-k$。若任意窗口都没有脉冲，则全族为零。因此

$$
\boxed{L\cong\mathbb Z\sqcup\{\infty\}.}
$$

每个有限窗口的全零读数都有实际整数实现，却没有任何单个整数同时实现所有窗口全零：

$$
\forall N\ \exists n:\ q_N(n)=0,
\qquad
\neg\exists n\ \forall N:\ q_N(n)=0.
$$

这是量词差别，不是数值误差。相容极限新增了不能由有限执行历史到达的理想分支。

#### 5.3.1 开邻域的完整描述

现在给每个有限 $B_N$ 离散拓扑，给 $L$ 乘积空间中的逆极限子空间拓扑，并用上述双射运输到 $X$。

对整数 $n$，选任意 $N\ge|n|$。第 $N$ 坐标等于 $q_N(n)$ 的柱集只包含 $n$：该坐标的非零脉冲已唯一决定全族。因此 $\{n\}$ 是开集，整数部分的子空间拓扑就是离散拓扑。

对 $\infty$，第 $N$ 坐标等于零的柱集为

$$
U_N=\{\infty\}\cup\{n\in\mathbb Z:|n|>N\}.
$$

$U_N$ 构成 $\infty$ 的邻域基。证明如下：乘积子空间的基本邻域只限制有限多个坐标；包含 $\infty$ 时，每个坐标条件都包含零。取这些坐标的最大指标 $N$，进一步要求第 $N$ 坐标恰为零，由相容性就满足所有较小指标的零坐标条件。因此任何包含 $\infty$ 的开集都包含某个 $U_N$。

由此得到全部开集的精确分类：

1. 不含 $\infty$ 的任意整数子集都是开集。
2. 含 $\infty$ 的集合 $U$ 是开集，当且仅当 $\mathbb Z\setminus U$ 有限。

必要性：若 $U$ 含某个 $U_N$，则其整数补集包含于有限集合 $[-N,N]\cap\mathbb Z$。充分性：若整数补集有限，取 $N$ 足够大包含该补集，则 $U$ 是 $U_N$ 与若干整数单点开集的并。

#### 5.3.2 Hausdorff 性、紧性与一点紧化

不同整数可用各自单点开集分离；整数 $n$ 与 $\infty$ 可用 $\{n\}$ 和 $U_{|n|}$ 分离。因此 $X$ 是 Hausdorff 空间。

对任意开覆盖，先取一项 $U$ 覆盖 $\infty$。上一小节表明 $X\setminus U$ 是有限整数集；对这些有限个点各取一项覆盖，就得到有限子覆盖。因此 $X$ 紧。这个紧性证明直接来自开邻域结构，不需要另引更大的边界或额外紧化对象。

$\mathbb Z$ 在 $X$ 中开且稠密：整数单点开，而每个 $U_N$ 都包含整数。离散 $\mathbb Z$ 的紧子集恰为有限集——有限集显然紧，无限子集的单点开覆盖没有有限子覆盖。因此 $\infty$ 的邻域恰是“$\infty$ 加上某个紧集的补集”。

所以这个实际读数塔的逆极限，正是离散 $\mathbb Z$ 的 Alexandroff 一点紧化。它不是把正无穷和负无穷分开的两点紧化；两个方向只要最终离开每个有限集合，就趋向同一个 $\infty$。

#### 5.3.3 正反平移延拓为同胚

定义

$$
\widetilde T(n)=n+1\quad(n\in\mathbb Z),
\qquad \widetilde T(\infty)=\infty.
$$

其逆映射为整数上的 $n\mapsto n-1$，并固定 $\infty$。整数子集的原像仍是整数子集，因而开；含 $\infty$ 的余有限开集的原像仍余有限，因而开。正反两映射均连续，所以 $\widetilde T$ 是同胚。

还可直接在读数坐标上看到连续性。对 $b\in B_{N+1}$，以 $k\in[-N,N]$ 为输出坐标，定义

$$
s_N^+(b)_k=b_{k+1},
\qquad s_N^-(b)_k=b_{k-1}.
$$

这些映射的值属于 $B_N$，并满足

$$
q_N(n+1)=s_N^+(q_{N+1}(n)),
\qquad
q_N(n-1)=s_N^-(q_{N+1}(n)).
$$

全零族也满足同样关系，故它们给出逆极限上互逆的连续平移。这里有一个必要的尺度细节：第 $N$ 层的平移后读数由第 $N+1$ 层决定；一般不能由同一层 $B_N$ 决定。例如 $n=N+1$ 与 $n=N+2$ 在第 $N$ 层均为零，但反向一步后，前者进入可见窗口，后者仍为零。因此不强加不存在的逐层 $B_N\to B_N$ 动态闭合。

由于整数上 $n+1\ne n$，$\infty$ 是延拓平移的唯一不动点。任何整数经有限次正反平移仍为整数，因此该不动点不可从实际初态经有限执行到达。

#### 5.3.4 体／边解释的准确范围

有限执行产生的整数状态保真嵌入相容读数边界；所有原有有限实验读数及平移关系都得到保持。完成化同时补入一个每个有限窗口均可实现、整体却没有原始实现的相容理想分支。

因此这提供了具体的体／边关系，却没有证明“保真嵌入就是两个承载器完全相同”。若要把离散实现与完成化说成同一对象的两份完整表示，仍需证明原始实际像已经对相应极限闭合。本例恰好显示这一额外条件不能省略。

该不动点来自明确的相容读数完成化；不能仅由其存在把它认作物理空间、物理静止态、免费可用原语或已经到达的实际状态。

### 5.4 档案、拓扑及仓内来源的边界

有限任务记忆不等于压缩完整观察者档案。只要允许无界重复绕行，不同有限事件词就有无限多个。要求精确复述档案、查询无界累计次数或某种未纳入状态的过去累计费用时，任务本身已经增加区别，不能继续使用较弱任务的有限记忆结论。

图路径模立即逆向抵消给出自由路径群胚，连通图的根基本群秩为 $\beta_1$。有限离散纤维及边双射构成组合覆盖：每个纤维顶点对每个相应有向边端口有唯一提升边；其连通提升分量对应可达轨道 $O$。非交换生成元是一种作用的呈示，不是独立物理坐标或普遍特征基。

同一个抽象圆周可以在三维空间中嵌入为平凡结或三叶结。环境结型需要嵌入、环境同痕或补空间等额外数据，不能由抽象闭环作用直接恢复。若图上再附加二维胞腔，其边界关系必须作用平凡，运输才下降到相应基本群胚；不能把图的自由群秩当成未声明周围空间的全部拓扑。

既有来源的准确归属如下，均指开头固定快照。

| 来源 | 可承担内容 | 不自动承担的扩展 |
|---|---|---|
| `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md`，定理 67.1，第 32003 行起 | 有限简单图上的 $\mathbb F_2$ 环奇偶、生成森林、共同顶点见证、锚、$\beta_1$ 与计数；允许空图和非连通图 | 不直接覆盖一般多重图上的非交换纤维运输 |
| 同文定理 77.1，第 34786 行起 | 正参考二分多重图的环增益与势函数；保留平行边；有限生成树检验与共同概率律条件 | 本文一般运输模型不自动继承其概率分类；该定理不自动给出任务最小记忆 |
| `D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence.lean`，`closed_path_zero_iff_exists_potential` | 连通群胚、交换加法群中的零闭环代价与顶点势差等价 | 不直接形式化非交换纤维运输及最小任务记忆 |
| `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean`，`DynClosure`、`dynamic_closure_is_least` | 任意类型及全定义操作族的最小动态稳定细化；所需新行为商的主要一般支点 | 有类型的图边及部分动作须显式适配，不能省略合法性 |
| `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean`，`controlled_behavior_universal_property` | 有限受控行为的商、唯一满射因子与基数界 | 该定理的有限状态及候选实现前提不能省略；无限纤维、有限任务商与有类型部分动作须另外连接 |
| `D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization.lean`，`canonical_minimal_realization` | 任意类型的单一更新系统之规范行为实现；精确更新及读数下从可达实现像的唯一满射 | 单一自主更新不是任意分支操作族的同一陈述 |
| `D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.lean`，`controlled_finite_stability`，第 499 行起 | 有限非空状态、动作及读数类型下，满射读数的细化平台永久稳定、最大稳定等价及类数界 | 生成元词长不能直接称作物理时间；空生成元族须处理非空前提 |
| `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.lean` | 单更新的有限视界观察核递推、反单调及与完整行为的联系 | 不替代一般受控分支版本的条件核对 |
| `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverHistoryLift.lean`，`circle_double_cover_history_lift`，第 36 行起 | 圆周平方覆盖的唯一路径提升、无连续全局截面、完整一圈由 $1$ 提升到 $-1$ | 不处理环境结型；不自动给出一般图任务的记忆最小性 |
| `D5/S3/Observer/AgencyHolonomy/ActionLoopRequiresMemory.lean`，`policy_change_implies_memory_change`、`injective_policy_detects_memory_change` | 策略变化推出记忆变化，以及单射策略读数下的对应逆向蕴含 | 没有最小记忆基数或维数定理 |

A卷第1.7节、A卷第2.1节、A卷第2.2节、A卷第2.3节、A卷第2.4节、A卷第2.5节、A卷第2.6节 与 A卷第5.3节给出普通数学推导、明确实例和必要条件反例，不把已有生成树原理、动态商原理或一点紧化的标准事实冒充新发现。

保留的实质连接是：在指定合法未来语言下，从闭环运输到可达轨道，再到未来行为商；并用同一个整数平移模型精确展示有限记忆、操作权限、相容极限与新增不动点之间的区别。

## 追加锚（本行以下为增补区）

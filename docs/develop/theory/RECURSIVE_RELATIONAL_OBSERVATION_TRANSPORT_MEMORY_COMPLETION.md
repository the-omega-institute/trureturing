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

该 v1 第10页（印刷第9页）Lemma 2.12 的印刷等式省略了这个 $+1$，其证明接续于第11页（印刷第10页）；而所列 separate-move 规则计入放置后的配置。本文按明列的配置计数，不将该印刷等式直接套用。这个校正只针对所引 v1 的字面约定，没有据此判断其他版本。更不能把它移到本节的保留输出模型：式(TM.29)含 $I\cap O$，末端输出仍驻留。单位大小、先分配再释放时，固定顺序的精确瞬时峰值是 $\max_{0\le i<|V|}(|L(I_i)|+1)$；不能无条件改成 $\max_i|L(I_i)|+1$，因为最大稳定集合可能恰好是最终保留输出。式(TM.30)及式(TM.32)后的既有常驻与瞬时计数继续采用原合同。另有 $n$ 个源共同指向一个 sink 的例子：拓扑稳定宽度为 $n$、分步峰值为 $n+1$，但底层无向星图 pathwidth 为一，故有向拓扑约束不能由无向布局宽度替代。

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

既有来源的准确归属如下，均指开头固定快照 `bfd5737539c696eedd4638da17d7f449339526cd`（见本卷 §2.19）。

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


## 6. 进位扩张、合法取得与查询—等待边界

在有限阿贝尔滤过中，相同的分次层可以具有不同的整体运算。进位余循环提供层间拼接，截面变换运输整套运算和读数；目标的行为纤维决定哪些区别必须保留，而指定传感器与合法动作决定这些区别如何取得。以下先给出带标记扩张的重建及任务下降，再在同一原初态的高位传感器上分别计算查询数与向前等待。

记号按节取作用域：第6.1–6.7节的 $q$ 是商同态、$s$ 是集合截面、$\beta:Q\to K$ 是截面修正；第6.8节起，$q\in\mathbb N$ 表示剩余查询预算、$s$ 表示相位、$\beta$ 表示原始符号的数值解码基准。两位扩张实例的 $k$ 是隐藏高位，第6.8节的 $k$ 则是位深。第6.11节固定 $p=2,k=j$，初始高位 $b$ 与余数的二进位 $b_i$ 分开记。

### 6.1 带标记扩张与进位运算

固定有限阿贝尔群及其加法同态组成的正合列

$$
0\longrightarrow K\xrightarrow{\iota}G\xrightarrow{q}Q\longrightarrow0.
\tag{CE.1}
$$

正合表示 $\iota$ 单射、$q$ 满射且 $\iota(K)=\ker q$。核 $K$ 与商 $Q$ 都带标记；比较时须说明是否保留这些标记。取一个归一化的**集合截面**

$$
s:Q\to G,\qquad q\circ s=\operatorname{id}_Q,\quad s(0)=0.
\tag{CE.2}
$$

有限性保证可以选代表，但不保证能在给定实验预算内准备这些代表。截面也不必是群同态。

因为 $q(s(a)+s(b)-s(a+b))=0$，存在唯一的 $c_s(a,b)\in K$ 使

$$
\iota(c_s(a,b))=s(a)+s(b)-s(a+b).
\tag{CE.3}
$$

记 $c=c_s$。既有[截面进位构造 `kernelCarry`](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/D5/S1/Deficit/Cocycles/AdditiveCarryCocycle.lean)以 $\ker q$ 为值域；这里用正合性给出的同构 $\iota:K\cong\ker q$ 将其运输到指定的 $K$。该来源的加法群取 $X=G$、$B=Q$，商同态取 $q$、代表函数取 $s$，右逆条件正是式（CE.2）。该构造不需要有限性；有限性是本章的模型条件。

定义

$$
\Phi_s:K\times Q\to G,\qquad\Phi_s(k,a)=\iota(k)+s(a).
\tag{CE.4}
$$

它是集合双射，因为

$$
\Phi_s^{-1}(g)=
\left(\iota^{-1}(g-s(qg)),qg\right),
\tag{CE.5}
$$

其中 $\iota^{-1}$ 只在 $\ker q$ 上使用。确实，$q(g-s(qg))=0$；代回 $\Phi_s$ 得到 $g$，而对 $g=\iota(k)+s(a)$，有 $qg=a$ 和 $g-s(qg)=\iota(k)$，所以另一复合也为恒等。再由式（CE.3），

$$
\begin{aligned}
\Phi_s(k,a)+\Phi_s(\ell,b)
&=\iota(k+\ell)+s(a)+s(b)\\
&=\iota(k+\ell+c(a,b))+s(a+b).
\end{aligned}
$$

于是完整加法被精确运输成

$$
(k,a)\star_c(\ell,b)
=\bigl(k+\ell+c(a,b),a+b\bigr).
\tag{CE.6}
$$

仅有集合双射 $G\cong K\times Q$ 不表示群是直积；群直积要求进位能在合适截面下消去。

由归一化、交换律及结合律分别得到

$$
c(0,a)=c(a,0)=0,\qquad c(a,b)=c(b,a),
\tag{CE.7}
$$

$$
c(a,b)+c(a+b,d)=c(b,d)+c(a,b+d).
\tag{CE.8}
$$

归一化由 $s(0)=0$ 和 $\iota$ 单射得到，对称性由 $G$ 交换得到。式（CE.8）直接使用上述来源的 `section_carry_cocycle`，参数仍为 $G,Q,q,s$，并经 $\iota$ 运输；它只要求加法交换群与右逆，归一化和对称性由此处另列的条件保证。在当前坐标中，两边经 $\iota$ 都等于 $s(a)+s(b)+s(d)-s(a+b+d)$。

反过来，若阿贝尔群 $K,Q$ 和一张表 $c:Q^2\to K$ 满足 CE.7–CE.8，则 CE.6 给出阿贝尔群。两种结合次序的 $Q$ 坐标相同，$K$ 坐标相等恰是 CE.8；零元是 $(0,0)$，逆元为

$$
(k,a)^{-1}=(-k-c(a,-a),-a).
\tag{CE.9}
$$

反向构造的细节如下。对 $(k,a),(\ell,b),(m,d)$，左结合的核坐标为 $k+\ell+m+c(a,b)+c(a+b,d)$，右结合的为 $k+\ell+m+c(b,d)+c(a,b+d)$；式（CE.8）使其相等。式（CE.7）的两个归一化等式分别给出左右单位元。式（CE.9）与 $(k,a)$ 右乘时，核坐标是 $k-k-c(a,-a)+c(a,-a)=0$；左乘时由 $c(-a,a)=c(a,-a)$ 同样为零。交换性由 $K,Q$ 交换和 $c(a,b)=c(b,a)$ 得到。因此它确为阿贝尔群，记作 $G_c$。

嵌入 $k\mapsto(k,0)$ 保加法且单射，投影 $(k,a)\mapsto a$ 保加法且满射；投影核恰为 $\{(k,0):k\in K\}$，所以恢复式（CE.1）的正合性。截面 $a\mapsto(0,a)$ 的进位恰为 $c(a,b)$。原扩张的 $\Phi_s$ 则是保持指定核与商的群同构。因而在这些条件下，两层的群运算加上一张归一化对称余循环表，足以重建带标记扩张。

这比“层数、大小或维数相同”严格更强。每层的数据说明有哪些坐标，进位表说明这些坐标怎样共同运算。

### 6.2 截面变换与整个实验的运输

另取归一化函数 $\beta:Q\to K$，并令

$$
s'(a)=s(a)+\iota(\beta(a)),\qquad \beta(0)=0.
$$

直接代入 CE.3：

$$
c_{s'}(a,b)=c_s(a,b)+\delta\beta(a,b),
\quad
\delta\beta(a,b)=\beta(a)+\beta(b)-\beta(a+b).
\tag{CE.10}
$$

同一个 $g$ 的新坐标却要减去该修正：

$$
T_\beta(k,a)=(k-\beta(a),a),
\quad \Phi_{s'}\circ T_\beta=\Phi_s.
\tag{CE.11}
$$

因而

$$
T_\beta(x\star_c y)
=T_\beta(x)\star_{c+\delta\beta}T_\beta(y).
\tag{CE.12}
$$

式（CE.12）两侧的核坐标同为 $k+\ell+c(a,b)-\beta(a+b)$，商坐标同为 $a+b$。同一个平移动作的旧参数 $(\ell,b)$ 因而也须运输为 $(\ell-\beta(b),b)$。

对任意旧坐标动作 $A$ 和读数 $o$，新坐标表示必须取

$$
A'=T_\beta\circ A\circ T_\beta^{-1},\qquad
 o'=o\circ T_\beta^{-1}.
$$

如果 $A$ 只在 $D$ 上定义，新定义域为 $T_\beta(D)$；状态相关费用 $e$ 的新表示为 $e\circ T_\beta^{-1}$，输出及失败标签也作同样运输。对相应状态 $z'=T_\beta z$，有 $A'z'=T_\beta Az$ 及 $o'(z')=o(z)$。对有限动作词逐步取消相邻的 $T_\beta^{-1}T_\beta$，每个前缀状态都相应，每次读数、费用和合法性都对应；空词由读数等式处理。按已见记录选择动作、停止或报告的策略也逐步对应，保留共同随机种子时则对每个种子如此。只运输终点而未运输中间接口，不具有这份保证。

这两个符号必须成对保留：**进位加余边界，高位坐标减截面修正**。仅改进位表而保持旧坐标读数，会换掉实际运算。

更一般地，在固定 $K,Q$ 及其标记时，任何保持核和商的扩张同构都具有

$$
F(k,a)=(k+t(a),a),\qquad t(0)=0
$$

的形式。理由是 $(k,a)=(k,0)\star_c(0,a)$，且 $F$ 在核上是恒等、在商上也是恒等。要求 $F:G_c\to G_d$ 保持加法，比较 $K$ 坐标就得到必要且充分条件

$$
d=c-\delta t.
\tag{CE.13}
$$

必要性的计算是 $k+\ell+c(a,b)+t(a+b)=k+t(a)+\ell+t(b)+d(a,b)$。反向，式（CE.13）使此等式成立，$F$ 的逆为 $(k,a)\mapsto(k-t(a),a)$，故确为保持标记的同构。因此固定标记的等价关系恰由余边界给出，不要求两张表逐项相等。

若还更换层标记，取同构 $\alpha:K\to K'$、$\gamma:Q\to Q'$，候选

$$
F(k,a)=(\alpha k+t(a),\gamma a)
$$

保持运算的精确条件变成

$$
\alpha(c(a,b))+t(a+b)
=t(a)+t(b)+d(\gamma a,\gamma b).
\tag{CE.14}
$$

这里 $t:Q\to K'$、$t(0)=0$。比较两种乘法的核坐标恰得式（CE.14），商坐标由 $\gamma$ 保加法而相等。反向，该式保证乘法相容，而

$$
F^{-1}(k',a')=
\left(\alpha^{-1}\bigl(k'-t(\gamma^{-1}a')\bigr),\gamma^{-1}a'\right)
$$

给出双射性。因此式（CE.14）是改变层标记时的准确相容条件。

分裂判据直接使用 [`extension_section_iff_coboundary`](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/D5/S1/Deficit/Cocycles/ExtensionSectionCoboundary.lean)：以 $G,Q,q,s$ 代入，归一化前提为 $s(0)=0$，将核值修正函数写成 $\iota\circ\beta$，得到存在加法同态右逆当且仅当存在 $\beta:Q\to K$ 使 $c+\delta\beta=0$。方程在 $(0,0)$ 处给出 $\beta(0)=0$，无需增添该来源未列的前提。此时 $s+\iota\beta$ 的进位为零，由式（CE.6）、（CE.12）得到同指定标记相容的直积表示；反向，同态截面自身的进位为零。

术语上，任意群扩张的 $H^2$ 分类还可能涉及非平凡作用；即使作用平凡、$K,Q$ 阿贝尔，任意中心扩张也未必阿贝尔。本章只使用**归一化对称余循环**对应的阿贝尔扩张，不把全部中心扩张无条件认成此处的阿贝尔对象。

### 6.3 相同分次层、不同扩张与小素数分类

设 $p$ 为素数。取 $K=Q=\mathbb F_p$，用 $\bar a\in\{0,\ldots,p-1\}$ 表示标准整数代表。

第一种整体是

$$
G_{\mathrm{cyc}}=\mathbb Z/p^2\mathbb Z,
\quad\iota(k)=p\bar k,\quad q(g)=g\bmod p,
\quad s(a)=\bar a\bmod p^2.
$$

此时 $g=\bar a+p\bar k$，进位为

$$
c_{\mathrm{cyc}}(a,b)
=\left\lfloor\frac{\bar a+\bar b}{p}\right\rfloor\bmod p.
\tag{CE.15}
$$

第二种整体是

$$
G_{\mathrm{split}}=\mathbb F_p\times\mathbb F_p,
\quad\iota(k)=(k,0),\quad q(k,a)=a,\quad s(a)=(0,a),
$$

其进位恒为零。两者的指定滤过都是

$$
G\supset\iota(K)\supset0,
\quad\operatorname{gr}(G)=(G/\iota K)\oplus\iota K\cong\mathbb F_p\oplus\mathbb F_p.
\tag{CE.16}
$$

这里说的是**选定滤过的分次加法群相同**。不能把第二个滤过写成 $G\supset pG\supset0$，因为 $p\mathbb F_p^2=0$。若分次对象还附带跨层的乘 $p$ 映射等额外关系，两者已经可以被区分。两者也都是 $p^2$ 个点的有限离散空间，差异在运算与滤过拼接，不能从此例宣称它们的裸拓扑不同。

两个群不可能同构：$G_{\mathrm{cyc}}$ 有阶 $p^2$ 的元素，$G_{\mathrm{split}}$ 每个元素都被 $p$ 消去。更直接地，循环群中任何 $1\in Q$ 的提升都是 $1+pt$；它的 $p$ 倍等于 $p\ne0$，因此没有同态截面。

进位中还有一个简洁的不变量：

$$
\kappa(c):=\sum_{j=0}^{p-1}c(j,1)\in\mathbb F_p.
\tag{CE.17}
$$

在 $c\mapsto c+\delta\beta$ 下，额外项为

$$
\sum_{j=0}^{p-1}[\beta(j)+\beta(1)-\beta(j+1)]
=p\beta(1)=0,
$$

其中 $j+1$ 按模 $p$ 计算。所以 $\kappa$ 不随截面改变。循环群只有 $j=p-1$ 时发生一次进位，故 $\kappa(c_{\mathrm{cyc}})=1$；分裂群的 $\kappa(0)=0$。这也直接证明两张表不相差余边界。

其操作含义可直接由式（CE.6）推导。从零出发，将所选提升 $s(1)$ 重复相加 $m$ 次，$0\le m\le p$，其坐标为

$$
\left(\sum_{j=0}^{m-1}c(j,1),\ m\bmod p\right).
$$

$m=0$ 为空和与零元；若式子对 $m<p$ 成立，再加 $(0,1)$ 时由式（CE.6）恰添一项 $c(m,1)$，故归纳成立。取 $m=p$，终点的商读数为零，核坐标为 $\kappa(c)$，在循环与分裂两例中分别是 $1$ 和 $0$。当 $p=2$，分裂运算就是逐位异或（XOR）；最小对照为

$$
(0,1)\star_{c_{\mathrm{cyc}}}(0,1)=(1,0),
\quad
(0,1)\star_0(0,1)=(0,0).
\tag{CE.18}
$$

因此，“层相同”不保证“反复操作后的共同实现相同”。这个反例也不依赖非交换性：两个整体都完全交换。

**命题 6.1（固定标记的小素数分类）。** 令 $K=Q=\mathbb F_p$，保持两个群的标记，以 $c\sim c+\delta\beta$、$\beta(0)=0$ 比较归一化对称余循环。$p=2$ 时恰有两张表、两个等价类；$p=3$ 时恰有九张表、三个等价类，每类三张。在这两个情形，$\kappa(c)$ 完全判定等价类。

**证明。** 对 $p=2$，表由 $A=c(1,1)\in\mathbb F_2$ 决定，且恰为 $A c_{\mathrm{cyc}}$，故满足余循环式。归一化余边界的唯一可能非零位置为 $\delta\beta(1,1)=2\beta(1)=0$，所以两个值 $A$ 分属两类，$\kappa=A$。

对 $p=3$，设

$$
A=c(1,1),\quad B=c(1,2)=c(2,1),\quad C=c(2,2).
$$

其余位置由归一化确定。式（CE.8）在 $(1,1,2)$ 上给 $A+C=B$，故 $C=B-A$。反向任取 $A,B\in\mathbb F_3$ 并置 $C=B-A$，取 $\beta(0)=\beta(1)=0$、$\beta(2)=A$，则

$$
(c+\delta\beta)(1,1)=0,\qquad
(c+\delta\beta)(1,2)=(c+\delta\beta)(2,2)=A+B.
$$

因此 $c+\delta\beta=(A+B)c_{\mathrm{cyc}}$。对任意归一化 $\beta$，余边界归一化且对称；余循环式两边的余边界部分都等于

$$
\beta(a)+\beta(b)+\beta(d)-\beta(a+b+d).
$$

故余边界满足余循环式，循环表的标量倍也满足它；相减说明任取的表 $c$ 确为余循环。共有 $3^2=9$ 张表，且 $\kappa(c)=A+B$。不同 $\kappa$ 由式（CE.17）的不变性不能等价；同一 $\kappa$ 的表都等价于 $\kappa c_{\mathrm{cyc}}$。固定 $A+B$ 时 $A$ 有三个选择，所以每类恰三张。$\square$

允许改变层标记时应使用式（CE.14），不能把固定标记的 $\kappa$ 数值直接当作未标记分类。

### 6.4 商观察的全部未来与行为纤维

回到任意 CE.1。允许动作标签 $u$ 对应已知的平移量 $g_u\in G$：

$$
T_u(g)=g+g_u.
$$

只通过商传感器 $q$ 读取。因为

$$
q(T_u(g))=q(g)+q(g_u),
\tag{CE.19}
$$

故对任意有限控制词 $w=(u_1,\ldots,u_n)$，

$$
q(T_{u_n}\cdots T_{u_1}g)
=q(g)+\sum_{i=1}^nq(g_{u_i}).
\tag{CE.20}
$$

**精确结论。** 将当前读数、所有未来控制词的终读数、乃至每个词的完整前缀读数都保留，所得行为观察 $B_q$ 仍满足

$$
\ker B_q=\ker q.
\tag{CE.21}
$$

这里的 $\ker$ 是观察的纤维等价关系，精确地说：

$$
B_q(g)=B_q(h)\iff q(g)=q(h).
$$

它不是群同态的零核；$B_q$ 中含有已知平移的分量一般是仿射函数。证明一向由 CE.20 给出；另一向使用空词读数 $q(g)$。特别地，$g$ 与 $g+\iota(k)$ 在任何这类实验中都无法区分。无限长档案也不能改变逐项相同这一事实。

这直接适配 [最小动态闭合 `dynamic_closure_is_least`](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean)：观察取 $q$，全定义干预取 $(u,g)\mapsto g+g_u$，候选仍取 $q$，细化因子为恒等。式（CE.19）给候选纤维的干预稳定性，空词给反向细化，所以行为纤维恰为原观察纤维。该来源允许任意类型与全定义操作族；部分域需要第6.5节的额外条件。[Context Geometry 命题24.4](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) 给出固定模读数的对应情形。

自适应协议还须保留完整初始化。令 $X$ 为实际初始实现的集合，$g:X\to G$ 给出原始对象状态，$I(x)=(m_0(x),c_0(x),\theta_0(x),\pi(x))$ 给出声明的完整可访问初始化：$m_0$ 包含全部已取得的内外部记录及其联合关系，$c_0$ 是内部／控制器状态，$\theta_0$ 包含全部已知设置和可变参数，$\pi$ 包含策略及其代码。对确定性协议，保留第 $n$ 步配置 $C_n=(a_n,m_n,c_n,\theta_n,\pi)$，其中 $a_n=q(g_n)$，$m_n$ 保留初始记录和截至该步的完整可见前缀。假设两次运行使用同一协议规则和同一组已知平移；动作菜单、停止决定及策略选择均为 $C_n$ 的函数，动作 $u$ 的合法性由 $(C_n,u)$ 决定，策略每次继续时从该配置的合法菜单选择动作；执行动作 $u$ 后的费用和额外报告仅由 $C_n,u,a_{n+1}$ 决定，记录、控制器及设置的更新仅由这些量和本步报告决定；停止时的费用与报告仅由 $C_n$ 决定。在这些下降条件下，若 $q(g(x))=q(g(y))$ 且 $I(x)=I(y)$，则使用同一策略的两次运行具有相同的全部可见前缀、动作、费用、报告和停止行为；这里不要求 $g(x)=g(y)$。若要初始化相等对每一对同商实现均成立，充要条件是在 $(q\circ g)(X)$ 上存在 $\bar I$ 使 $I=\bar I\circ(q\circ g)$：正向取每条纤维上的共同初始化为 $\bar I$ 的值，反向由代入即得。若另有已取得的记录，须将其留在 $I$ 中，比较实际联合观察 $x\mapsto(q(g(x)),I(x))$ 的纤维，不能仅凭商读数相等删去这些记录。

证明按已产生的有限前缀归纳。零步时，商读数相等与完整初始化相等共同给出 $C_0(x)=C_0(y)$，包括全部旧记录、控制器、设置和策略。假设截至第 $n$ 步的可见前缀及 $C_n$ 相同，则下降条件给出相同菜单、合法性与停止决定；若停止，终止报告及费用相同，两次运行同时结束。若继续，同一策略在相同配置上选择同一合法动作 $u$，由 CE.19 得 $a_{n+1}(x)=a_n(x)+q(g_u)=a_n(y)+q(g_u)=a_{n+1}(y)$。本步费用与额外报告因其输入相同而相同，再由同一记录／控制器／设置更新得到 $C_{n+1}(x)=C_{n+1}(y)$；将这一步追加到已有前缀，得到相同的新前缀和累计费用，完成归纳。故两次运行或者在同一步停止并留下相同完整档案，或者均不停止且无限档案逐项相同。对可测的随机协议，若种子 $R$ 与完整初始实现独立、两次运行使用同一分布 $\mu$，且每个固定种子下均满足上述下降条件，则以同一个 $R\sim\mu$ 耦合两次运行；条件于该种子，刚才的归纳逐步成立，故档案作为种子的函数相同，观察分布也相同。携带源信息的种子须计入初始联合观察；若合法性、执行耗时或其他报告不满足下降条件，也须作为额外观察接口保留，不能仍用仅有 $q$ 的纤维作结论。$\square$

仅有商读数相等不足以保证上述自适应结论。取分裂群 $G=\mathbb F_2\times\mathbb F_2$、$q(k,a)=a$，旧记录为 $m_0=k$，其余初始化相同；两个动作 $T_0=\operatorname{id}$、$T_1(k,a)=(k,a+1)$ 始终合法且费用为零，同一策略选择 $T_{m_0}$ 后读取 $q$。每个固定动作都满足 $q(T_u(k,a))=a+u$，因而保持 $q$ 的纤维；但初态 $(0,0)$ 与 $(1,0)$ 的商读数均为 $0$，旧记录分别为 $0$ 与 $1$，策略分别选择 $T_0$ 与 $T_1$，下一读数分别为 $0$ 与 $1$。这证明缺少初始化相等时自适应结论不成立，而实际联合观察 $(q,m_0)$ 已区分这两个初态。$\square$

跨两个例子，可以用共同标签 $(\ell,b)$ 指定对应坐标的平移。两系统的低位更新始终是 $a\mapsto a+b$，故同低位初态具有相同的全部低位控制行为。即便内部进位不同，当前指定的实验语言仍看不到差别。

更一般地，从加法、取负、已知常数与已知整数倍构造的群项都保持 $q$ 的纤维；只把这些运算结果继续交给 $q$，仍不能恢复隐藏 $K$。这里的“所有加法续接”保留这个合法运算含义，不包含未授权的位交换或隐藏态传感器。

在有限实现的表述中，直接使用 [`controlled_behavior_universal_property`](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean)：源状态取 $Y=G$、候选实现取 $W=Q$、输出取 $O=Q$，实现映射为满射 $q$，实现上的动作是 $a\mapsto a+q(g_u)$、读数是恒等映射。两个交换条件分别是式（CE.19）与 $\operatorname{id}_Q\circ q=q$，且 $G,Q$ 有限。该来源给出从 $Q$ 到受控行为商的唯一满射因子及相应基数界；式（CE.21）进一步说明此因子单射。名义实现若含未被来源实现的状态，唯一性只在实际像上使用。这一有限状态结论不直接适用于带无界事件计数或完整档案的状态空间。

### 6.5 有限视界的值与全部最优动作下降

取共同有限非空动作集 $U$，商状态 $a=q(g)$。假设全定义确定性更新满足 $qT_u=\overline T_uq$，实值阶段奖励和终值满足

$$
r(g,u)=\bar r(qg,u),\qquad h(g)=\bar h(qg).
\tag{CE.22}
$$

对加法控制，$\overline T_u(a)=a+q(g_u)$。Bellman 递推为

$$
V_0(g)=h(g),\quad
V_{n+1}(g)=\max_{u\in U}\{r(g,u)+V_n(T_u g)\}.
\tag{CE.23}
$$

这里直接使用本卷第5.1.4节命题5.2及 [`finite_horizon_value_factorization`](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization.lean)：微状态取 $G$，宏状态取 $Q$，抽象取 $q$，共同动作取有限非空的 $U$，微／宏转移取 $T_u,\overline T_u$，奖励与终值取 $r,h,\bar r,\bar h$。转移交换关系及式（CE.22）正好给出三个前提，故

$$
V_n(g)=\bar V_n(qg)\quad\text{对所有有限 }n.
\tag{CE.24}
$$

相同参数满足 [`finite_horizon_optimal_actions_descend`](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent.lean) 的前提。对每个动作，实际评分相等：

$$
r(g,u)+V_n(T_u g)=\bar r(qg,u)+\bar V_n(\overline T_u(qg)).
$$

这里 $n$ 是续值的剩余阶段数，该评分决定 $n+1$ 阶段问题的首动作。在同一有限非空动作集上取最大值，最大值和全部达到最大值的动作标签，包括并列最优动作，都相同。两扩张共享商更新、奖励和终值时，分别经这个商系统得到同样的值与全部最优动作。该值函数来源不要求状态集有限；其共同有限非空动作和实值条件不能挪给第6.9节的扩展非负最小—最大费用。

部分动作采用 [ML 卷定理2.2、3.2的严格下降条件](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)：每个动作定义域是 $q$ 纤维的并；同纤维的合法具名菜单相同、有限且非空；合法时的输出、费用和后继观察均经 $q$ 因子化，不合法时的失败报告及其费用也一致。以终值下降为零视界基例，对剩余视界归纳，同一合法动作的评分相等，再在同一非空菜单上取最大值，给值和全体最优标签相等。逐前缀归纳还保持输出、累计费用和失败语义。这里另行核对了部分域，没有将全定义转移的来源定理当作任意部分动作版本。

具体取第6.3节的两个 $K=Q=\mathbb F_p$ 扩张，$p$ 为素数。一个非恒定任务是 $U=\{0,1\}$、按各自的 $s(u)$ 平移，

$$
\bar r(a,u)=\mathbf1_{a=0}-u/4,
\qquad\bar h(a)=\mathbf1_{a=1}.
\tag{CE.25}
$$

两扩张对所有有限视界的上述任务等价。相反，若任务终值改为 $h_s(g)=\mathbf1_{k_s(g)=0}$，则 $(0,a)$ 与 $(1,a)$ 低位相同而终值不同，连零步任务都不能经 $q$ 下降。

所以是否需要保留进位，取决于目标及操作：有的任务只需要商，有的任务必须恢复核坐标或整个运算。相同最优值不是无条件的内部同构证书。

### 6.6 揭示核坐标的合法接口

#### 6.6.1 联合读数与进位表项的取得

在给定截面下，定义

$$
k_s(g)=\iota^{-1}(g-s(qg)).
\tag{CE.26}
$$

联合读数 $(k_s(g),q(g))$ 就是 CE.5，可精确恢复完整 $g$。这个传感器必须实际可用；其数学定义不自动提供设备。换截面后

$$
k_{s'}(g)=k_s(g)-\beta(qg),
\tag{CE.27}
$$

因为 $g-s'(qg)=g-s(qg)-\iota(\beta(qg))$，式（CE.27）在核上由 $\iota^{-1}$ 的加法性立即得到。同一实际读数的坐标说明须随之运输。

若目标是识别未知进位表，且确实能准备同一系统中的 $s(a),s(b),s(a+b)$，执行加法和取负，再读出所得核元素的 $K$ 标签，则

$$
s(a)+s(b)-s(a+b)=\iota(c_s(a,b))
\tag{CE.28}
$$

直接返回该表项：该残差属于 $\ker q$，校准读数在这个核上等于 $\iota^{-1}$，所以输出恰为 $c_s(a,b)$。逐个有序对 $(a,b)\in Q^2$ 作此实验，共至多 $|Q|^2$ 次即可取得全表。每项都需要同一系统中相应截面点的准备、合法加减和核读取；次数界不赋予这些步骤零费用。

只把 CE.28 的残差交给旧传感器 $q$，永远得到零。执行了一个产生核元素的操作，不等于已经读到了该核元素。若 $a,b$ 及已知 $c$ 本就可见，报告这次发生何种进位也不恢复未知的初始 $k$；它只决定后续核坐标相对于 $k$ 的增量。例如固定 $a,b,\ell$ 时，两个不同的 $k,k'$ 在相同商动作下分别变成 $k+\ell+c(a,b)$、$k'+\ell+c(a,b)$；已知的进位增量完全相同，初始差 $k-k'$ 仍未确定。

#### 6.6.2 位交换与滤过权限

在第6.3节的 $K=Q=\mathbb F_p$ 两位坐标中，若另行允许操作

$$
U_s(k,a)=(a,k),
\tag{CE.29}
$$

则之后读取 $q$ 就得到原隐藏 $k$。它是有限集合上的双射，却不是循环群 $\mathbb Z/p^2$ 的群自同构：$(0,1)$ 表示阶 $p^2$ 的元素 $1$，其像 $(1,0)$ 表示阶 $p$ 的元素 $p$，而群自同构保持元素阶。对任一循环群自同构 $A$，有 $A(pg)=pA(g)$，所以 $A(pG)=pG=\ker q$；同商的两元素之差属于该子群，变换后的差仍在其中。因此仅增加这些自同构仍不能切开旧核纤维。

在分裂群中位交换逐坐标保加法，且自身为逆，故是群自同构；但它把指定的隐藏轴 $\{(k,0)\}$ 送到另一轴 $\{(0,k)\}$，不保持指定滤过。因此，它在“所有群自同构”任务中可以合法，在“保持既定滤过”任务中不合法。必须先声明操作合同，不能以换坐标名义免费增加这种能力。

#### 6.6.3 连续高位恢复的两位特例

在循环群中令 $T(g)=g+1$，初态为 $g=a+pk$，其中 $a,k$ 取标准数字。只观察高位。对 $0\le n\le p-1$，

$$
k_s(T^n g)=k+\left\lfloor\frac{a+n}{p}\right\rfloor\pmod p.
\tag{CE.30}
$$

式（CE.30）来自整数除法：$a+n<2p$，所以在该窗口至多进位一次；先模 $p^2$ 再读高位，恰相当于将整数商对 $p$ 取模。第一个高位读数给 $k$。即使 $k=p-1$，进位后的零与 $k$ 也不同。若首次变化发生在 $1\le\tau\le p-1$，则 $a=p-\tau$；若始终不变，则 $a=0$。因此 $p$ 个连续读数恢复完整两位，最大滞后为 $p-1$。在这个固定连续协议中，更短最坏视界不能区分初态 $0$ 与 $1$；该锐性不声称适用于所有自适应或跳时协议。

这是 [Context Geometry 定义24.7、定理24.8–24.9及推论24.10](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) 的位深 $k=1$ 特例：此处符号 $k$ 表示初始高位数值，引用中的位深另固定为一。原源为模 $p^2$ 状态、动作仅为 $+1$、传感器为高位、协议在每个连续时刻读取。其最小动态闭合是完整模 $p^2$ 状态。相反，在分裂群中按 $(0,1)$ 更新，高位恒为 $k$，任意长高位历史都不能恢复 $a$。

这对照说明：**时间能否把遗漏坐标送到界面，由传感器和拼接运算共同决定。**低位传感器配循环加法已经闭合；高位传感器配同一加法未闭合，因此能够通过进位时间取得低位。

若只需区分两个整体的加法规律，可从已知零态开始，将指定的低位单位提升重复相加 $p$ 次，再读核坐标，循环群给 $1$、分裂群给 $0$。这一识别方案额外使用已知准备和核读数；仅保留低位时仍无法区分。

### 6.7 用整个已重建子群递归拼接

有限长滤过 $G=F_0\supset F_1\supset\cdots\supset F_r=0$ 可以逐级组织成

$$
0\to F_{i+1}\to F_i\to F_i/F_{i+1}\to0.
\tag{CE.31}
$$

设每个商群 $Q_i=F_i/F_{i+1}$ 的运算已给定。从 $F_r=0$ 出发，若整个群 $F_{i+1}$ 已重建，并给出归一化对称余循环 $c_i:Q_i^2\to F_{i+1}$，就以

$$
(u,a)\star_i(v,b)=(u+_{F_{i+1}}v+c_i(a,b),a+_{Q_i}b)
$$

重建 $F_i$。第6.1节的结合律、单位元、逆元及正合性证明适用于这一步；若 $c_i$ 来自原滤过的截面，$\Phi_{s_i}$ 还给保持整个核与商的同构。对 $i=r-1,r-2,\ldots,0$ 作有限倒向归纳，得到整体 $G$。在此阿贝尔模型中，商对核的共轭作用平凡，无需另添非平凡作用。只给所有分次群 $F_i/F_{i+1}$，仍可能遗漏逐级扩张类。此处也不声称任意多层对象都只需要相邻两张标量进位表：第 $i$ 级的核是整个 $F_{i+1}$，先前已重建的运算必须被下一层真实使用。

改变截面提供相同对象的新坐标；增加可用传感器或操作改变观察者的可达能力；增加记录长度只是在既定操作语言里扩展历史。这三种改变可以分别计算，不能互相冒充。

在全文的阿贝尔合同内，归一化与对称性仍是拼接条件，不能仅凭结合律省去 CE.7。任务在完整未来响应的纤维上常值，只证明目标由该响应表示决定；不自动给出一次实验的准备许可、重置许可、有效算法或费用保证。

因此，本例给主线提供的紧凑结构是

$$
\boxed{\text{层的数据} + \text{满足结合律的拼接} + \text{保拼接的转换}}
$$

以及与之配套的取得判据

$$
\boxed{\text{目标在全部合法未来响应的共同纤维上常值}}.
$$

前者重建内部运算，后者判定当前实验是否足够。两者之间的桥由实际传感器、动作、来源与费用承担。一个进位余循环不是额外堆砌的统一名词，它是把多次操作的两条路径接到同一实现上的有限关系证书。

因子化的准确含义可由 [`universal_sufficiency_factorization`](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization.lean) 直接给出。取非空实际来源集 $X$、完整合法响应映射 $B:X\to\mathcal R$ 及目标 $T:X\to Y$；当前群模型的非空性由零元保证。其前提是

$$
B(x)=B(x')\Longrightarrow T(x)=T(x').
$$

将该来源中的概念取 $B$、目标取 $T$，所得结论是目标经响应因子化到实际目标像 $T(X)$。在实际响应像 $B(X)$ 上，这个因子唯一且由 $\bar T(Bx)=T(x)$ 定义；前提恰好保证无歧义。把 $T(X)$ 包含进 $Y$ 即恢复原目标。若响应空间有不可达名义元素，不对那些元素声称唯一解码；空来源域则两个实际像皆空，唯一空映射单独处理。因子存在不提供读取整份 $B(x)$ 的有限协议、有效算法、重置许可或费用界。

本卷第5.1.1节命题5.1只有在同一紧 Hausdorff 来源、非空有向相容观察塔、连续满射到 Hausdorff 层等条件下，才以闭纤维有限交性质保证每个相容线程都有共同实现；联合分离再给同胚。有限扩张的逐级重建不自动提供这些完成化条件。

### 6.8 同一原初态的合法取得与两种费用

固定整数 $p\ge2$、$k\ge0$，令 $P=p^k$。只讨论模 $pP$ 的初态
$$
x=bP+r,\qquad 0\le b<p,\quad 0\le r<P.
\tag{AS.1}
$$
以标准代表 $0\le x<pP$ 定义传感器 $d_k(x)=\lfloor x/P\rfloor$，群内加法按模 $pP$ 进行。每次读数不扰动状态；初始读数 $b$ 已取得并保留。目标为原初态 $x$，故余下需要识别 $r$。全部动作增量、事件数和结果均进入记录。若使用 $p$ 进整数解释，再要求 $p$ 为素数；下列有限循环模型本身不需要素性。

基本执行只允许 $+1$，但可在所选时刻不读取，或在根据已有结果选择的时刻读取。等待 $n$ 个事件要计 $n$ 次实际单位演化；一次读取另计一查询。没有重置、复制、时间倒流或未知的外部状态旁路。初始读取不计在“额外查询”中，但所有总读取数应加一。

[任意二元问题识别定理 `arbitrary_binary_questions_identify_target`](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/D5/S3/ConceptDynamics/Coding/FiberBinaryIdentification.lean)在有限来源、有限当前读数和有限目标的条件下，允许逐纤维选择任意二元问题而给出对数深度。这里仅将其作为信息量比较；实际传感器可实现哪些问题，要由下面的阈值证明给出。[二元协议深度下界 `adaptive_binary_protocol_depth_lower_bound`](https://github.com/the-omega-institute/trureturing/blob/7f2bd771ec9e4bffc9558419ac45147775310773/D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound.lean)要求有限来源与有限当前读数，以及与当前读数和协议 transcript 相容的精确目标解码；该下界本身不要求目标类型有限。对于按已知 $b$ 选择的策略，固定 $b$ 后取 $X_b=\{0,\ldots,P-1\}$、当前读数为单点、目标为 $r\mapsto bP+r$，其唯一当前纤维有 $P$ 个不同目标。下面将真实原始读数规范化为二元响应，才应用该下界。

同一整数模型还可以在任意 $P\ge1$ 上定义，不要求 $P$ 为 $p$ 的幂。固定整数 $p\ge2$，令

$$
R_{p,P}(b,r;n)=
\left\lfloor\frac{(bP+r+n)\bmod(pP)}P\right\rfloor,
\quad 0\le b<p,\quad 0\le r<P,\quad n\in\mathbb N.
$$

模运算取非负标准代表。这里 $P$ 是块长度及阈值相位周期，整个状态的周期为 $pP$。当 $P=p^k$ 时，$R_{p,P}(b,r;n)=d_k(x+n)$；任意整数 $P$ 只表示有限块传感器，不据此赋予它 $p$ 进位深。以下只依赖该整数读数公式的阈值、查询、等待和递推结论，对这个有限块模型同样成立。

本节的费用是实际向前单位事件数与实际读取次数。仅保留固定信息后作计算、允许任意干预的模型、仅有 $+1$ 的模型，是不同的可用信息与操作条件。全程 $+1$ 时累计位移等于等待事件数；若另许带符号或任意大小的动作，只比较终点位移不会保持沿路每次读取的费用。以下优化识别原初态的剩余最坏等待，另约束每条路径的查询预算；若任务要求复述全部读取档案、逐次读取费用或既付总费用，这些量必须另行保留。实际等待单位是所声明的事件，不据此换算为物理秒或能量。

#### 6.8.1 原始读数、阈值与向前等待

对任意已知非负累计事件数 $n=cP+s$，其中 $0\le s<P$，直接有
$$
d_k(x+n)=\bigl(b+c+\mathbf1_{\{r\ge P-s\}}\bigr)\bmod p.
\tag{AS.2}
$$
该式包括整个状态的环绕。确实，对任意非负整数 $z$，写 $z=apP+v$、$0\le v<pP$，则 $\lfloor z/P\rfloor=ap+\lfloor v/P\rfloor$，所以先模 $pP$ 后取商等于先取商再模 $p$。再将 $n=cP+s$ 代入，其整数恒等式为
$$
\left\lfloor\frac{bP+r+n}{P}\right\rfloor=b+c+\left\lfloor\frac{r+s}{P}\right\rfloor.
$$
由于 $0\le r+s<2P$，商 $\lfloor(r+s)/P\rfloor$ 恰为 $\mathbf1_{\{r\ge P-s\}}$。因此任意有限块模型的原始式同样为

$$
R_{p,P}(b,r;n)=
\left(b+c+\mathbf1_{\{r\ge P-s\}}\right)\bmod p.
$$

当 $s=0$，指示量恒为零。否则从实际读数减去已知的 $b+c$、再对 $p$ 取模，恰得到 $0$ 或 $1$，由于 $p\ge2$ 两值不同。高位本身有 $p$ 种可能符号，但在已知 $b$ 和本次动作之后，至多增加一个二元分支。发生环绕也不损害此解码。

任给阈值 $1\le\theta<P$，取 $s=P-\theta$，即可读取 $\mathbf1_{\{r\ge\theta\}}$。若当前事件数为 $n_0$，选择严格晚于 $n_0$ 且模 $P$ 等于 $s$ 的最早事件数，就只需再等
$$
\delta(n_0,\theta)=((P-\theta-n_0)\bmod P),
\quad\text{若此值为零则取 }P.
\tag{AS.3}
$$
这里只前进；归一化公式中的 $c$ 由累计事件数给出，不能忘记该档案。为获取下一个模 $P$ 相位，无需等待整个状态周期 $pP$。

#### 6.8.2 自适应查询的上下界

允许等待任意有限事件数时，最坏额外查询数的最小值为
$$
J(P)=\lceil\log_2P\rceil,
\qquad J(1)=0.
\tag{AS.4}
$$
一个固定历史节点的两种原始符号为已知 $\beta$ 与 $\beta+1\bmod p$；不同节点使用不同符号对，不增加单个节点的分支数。

上界通过有序候选区间实现。初始区间为 $[0,P-1]$；若当前区间为 $[l,h]$ 且 $l<h$，令 $\theta=\lfloor(l+h+1)/2\rfloor$，执行 AS.3 的等待，再解码 AS.2。响应为零则置 $h=\theta-1$，为一则置 $l=\theta$。每步两支的大小均不超过原大小的一半向上取整，所以至多 $J(P)$ 次后只剩一个候选。具体地，若当前候选数不超过 $2^q$ 且大于一，两支各不超过 $2^{q-1}$；按 $q$ 归纳，至多 $q$ 次即可取得单候选。阈值与等待只由已见响应和已知事件数决定，不需要读取未知 $r$。

下界：给定同一个 $b$，在确定性策略的每个记录节点，本次所选事件数已经由过去决定；AS.2 使该节点最多有两个新响应。深度至多 $q$ 的二元决策树最多有 $2^q$ 个叶。精确识别 $P$ 个实际目标需要至少 $P$ 个叶，即 $q\ge J(P)$。既有下界接口使用固定宽度二元 transcript；对早停分支可补确定的虚拟位作为数学编码，虚拟位不算实际追加查询。该接口的原式为
$$
\operatorname{Nat.clog}_2(\operatorname{worstFiberDiversity})\le\operatorname{depth}.
$$
此处最大纤维目标数为 $P$。允许早停不增加此容量；不同停止时间也由已有记录决定，不是额外传感器。这个论证正好满足既有二元协议下界的条件，不能从原始读数有 $p$ 个符号误用 $p$ 叉下界。

沿二分路径，每次阈值严格落在新的真子区间内，故不会重复前一个阈值。首查询相位非零，后续相位也不同于上次。于是 AS.3 的每次等待均至多 $P-1$，给实际等待上界
$$
N_{\mathrm{binary}}\le J(P)(P-1).
\tag{AS.5}
$$
这是该构造的等待上界，最坏总读取数为 $1+J(P)$，部分来源可以更早停止。其等待未必最优：取 $p=3,k=1,P=3$，上述中点构造先询问 $\theta=1$，最早在 $n=2$ 读取；若响应一，候选为 $\{1,2\}$，下一阈值 $2$ 最早在 $n=4$ 读取，所以最坏等待为四。改为在 $n=1,2$ 连续读取，依次取得阈值 $2,1$。其归一化响应向量在 $r=0,1,2$ 上分别为 $(0,0),(0,1),(1,1)$，故两次查询、最坏等待二即可识别。第6.8.4节的 $r=0,1$ 下界说明二已最优。因此最优查询数与某个达到它的构造之等待，不能不经比较就称为共同最优。

#### 6.8.3 固定查询与实际等待

若所有查询时刻可依赖已知 $b$，但不能依赖新增读数，则最小额外查询数为 $P-1$。已知任意非负整数事件数的读数仍由 AS.2 化为一个阈值，重复阈值或 $s=0$ 不增加区别。$q$ 个互异阈值将有序集合 $\{0,\ldots,P-1\}$ 划成恰 $q+1$ 个非空区间，每个区间内的全部响应向量相同。因此精确识别要求 $q+1\ge P$。

取时刻 $1,\ldots,P-1$，恰取得全部阈值，达到下界。故
$$
q_{\mathrm{fixed}}=P-1,\qquad q_{\mathrm{adaptive}}=J(P).
\tag{AS.6}
$$
该差距不是同一有限窗口内的任意重新编码：自适应协议允许取得后续结果后再决定何时取得下一份信息。先看完固定完整记录，再对其后处理，仍须支付固定记录的取得费用。这里不比较有噪声或有先验分布时的平均查询数。

#### 6.8.4 首窗口必须逐事件读取

任何只向前执行 $+1$、精确识别全部初态的策略，其最坏等待至少为 $P-1$。当 $P>1$，同一 $b$ 下的 $r=0$ 和 $r=1$ 在所有事件数 $0\le n<P-1$ 的高位完全相同；相同旧记录迫使同一策略采取相同动作。二者的首次可能区别在 $n=P-1$。连续完整采样达到该等待下界。

更强地，若要求所有分支在首窗口 $0\le n\le P-1$ 内停止，那么最坏额外查询数也至少为 $P-1$。证明沿 $r=0$ 的实际分支考察严格递增的非冗余采样时刻 $0=n_0<n_1<\cdots$。若某个相邻时间间隔 $n_i-n_{i-1}\ge2$，选择两个不同余数，使各自的首次进位时刻都在整数区间 $(n_{i-1},n_i]$ 内。两者在此前采样中都未进位，在 $n_i$ 都已进位；之后直至 $P-1$ 都只显示同一个高位 $b+1\bmod p$。它们遵循相同的后续适应性策略，却永久给出相同剩余窗口记录，无法识别。若 $r=0$ 的分支停止时尚未达到 $P-1$，则 $r=1$ 与它仍不可区分。因此这条分支必须在每个 $1,\ldots,P-1$ 读取。

当 $P=1$，初读已识别目标，两项费用均为零。总而言之，最小等待 $P-1$ 与最小查询 $J(P)$ 分别可达，却在 $P-1>J(P)$ 时不能由同一个协议同时达到。不能把不同策略各自取得的最小值拼成共同可达费用对。

### 6.9 读后相容域上的精确最小—最大费用

固定有限块参数 $p,P$ 及上述确定性精确协议类。以下最小—最大费用只定义在**当前读数已经取得的决策节点**。设当前候选余数恰为整数区间 $[l,h]$，当前事件相位为 $s=n\bmod P$，剩余额外查询预算为 $q\in\mathbb N$。读后相容域是
$$
\mathcal D_P=
\{(l,h,s):0\le l\le h<P,\ 0\le s<P,
\ s=0\ \text{或}\ \neg(l<P-s\le h)\}.
$$
这个条件表示当前时刻的阈值响应在全部剩余候选上恒定；它已经包含在现有知识中。还须保留“当前读数已取得”这一语义前提。等待中的中间时刻没有新读数，下一读取时间只能由旧记录和已知事件数决定，故从读后节点到下一读取的全部等待可合成一个未来时刻；这说明采用读后节点并未删去原合同中能改进初态费用的策略。初始读后节点 $([0,P-1],0)$ 属于此域。空候选集代表不相容记录，不是这里的决策节点。对域中节点，考察当前候选恰为 $[l,h]$ 的知识条件以及已经取得的当前读数；不声称每个数值三元组都必须在某个指定根协议中出现。所有实际后继则确实来自当前来源集合的非空部分。

定义 $C_q(l,h,s)$ 为在至多 $q$ 次后续查询内识别所有当前候选的协议之最坏额外单位演化数的下确界，无协议时为 $+\infty$。费用取 $\mathbb N\cup\{+\infty\}$；下面证明每个有限值都由一份协议达到。它不依赖数值基准 $b+\lfloor n/P\rfloor\bmod p$：候选区间和相位相同的两份读后档案，每次等待相同事件数后相位仍相同；用各自保留的基准减去原始符号，所获阈值比特逐来源相同。因此可将一个协议的读数标签逐节点运输为另一协议，等待和查询数逐来源保持。这只消去费用所不敏感的符号标记，没有允许原始解码忘掉基准。基例为
$$
C_q(l,l,s)=0,\qquad C_0(l,h,s)=+\infty\quad(l<h).
\tag{AS.7}
$$
对于 $(l,h,s)\in\mathcal D_P$、$l<h$、$q\ge1$，有精确递推
$$
C_q(l,h,s)=\min_{l<\theta\le h}
\left[\delta(s,\theta)+
\max\{C_{q-1}(l,\theta-1,P-\theta),
C_{q-1}(\theta,h,P-\theta)\}\right].
\tag{AS.8}
$$
这里 $\delta$ 按 AS.3 取严格正等待。在读后相容域中，任何内部阈值 $l<\theta\le h$ 均不同于当前相位对应的阈值 $P-s$，故实际上 $1\le\delta(s,\theta)\le P-1$。立即重读当前传感器只返回已知常量，不能再划分候选，因而不需要将它作为有用的零等待动作。

读取内部阈值后，两个孩子的相位同为 $s'=P-\theta$。左孩子为 $[l,\theta-1]$，其所有候选都小于 $P-s'=\theta$；右孩子为 $[\theta,h]$，其所有候选都不小于 $\theta$。于是当前阈值在各自孩子上恒定，两者均属于 $\mathcal D_P$。每个孩子由非空的实际候选集合实现，所以递推在该域内闭合，最坏费用必须取两支最大值。

证明首先删除无用读取。区间外阈值或零相位的响应在全部当前候选上确定。删除这次实际读取后，可由现有知识计算该常量以选择原策略的后续动作，并在下一次有用查询之前执行同样多的实际 $+1$。后续有用读数及其绝对事件数不变，等待费用不增，查询数减少。这会改变字面上的实际采样记录，却不改变候选知识和后续有用记录；推导出的常量不冒充一次实际测量。

其次，对选定内部阈值，若原策略在首次未来可达相位之后还等待 $aP$ 个事件才读取，可将该读取及整个后继策略一同提前 $aP$ 个事件。这里是构造另一条全程只向前的策略，不是逆转已经执行的状态。实际符号满足
$$
d_k(x+n+aP)=d_k(x+n)+a\pmod p.
$$
通过已知符号重标记运输后续策略，全部归一化二元响应不变；其后每个分支的相位相同，总等待减少 $aP$。这一步使用保留的原始解码基准，不能把原始符号跨周期直接视为相等。

现在对剩余预算 $q$ 证明递推的两个方向，同时证明有限值可达。$q=0$ 或单候选时式（AS.7）成立。设较小预算已证明。任一成功协议从非单候选节点必有首个有用读数；删去此前已知常量读取后，这次读数对应某个内部阈值 $\theta$。若其时间比最早相位多 $aP$，把此次读数及全部后续分支平移到更早 $aP$，并在策略内将新原始符号加上已知的 $a\bmod p$ 来模拟旧符号。这保持每个相同原初 $r$ 的旧分支选择，后继相位及相对等待不变。新首段等待为 $\delta(s,\theta)$，后续仍各使用至多 $q-1$ 次查询。由归纳假设，两支最坏剩余等待分别至少是式（AS.8）的两个孩子值，故原策略最坏等待至少为该阈值的右端表达式，进而至少为所有阈值的最小值。

反向，对一个使右端有限的阈值，先等待 $\delta(s,\theta)$ 并读同一传感器。归纳假设为两个非空真实孩子分别给达到相应 $C_{q-1}$ 的协议，按实际响应接续其中一个，即构成同一原初来源上的合法协议。一个来源只进入其实际孩子；两孩子的并恰为原候选集，所以整份协议的最坏等待恰是首段等待加两孩子最坏值的最大值。内部阈值集合有限且非空，故若有有限值，其最小值由某个阈值达到；若全部为无穷，则前一方向排除任何成功协议。这样同时证明式（AS.8）、有限值可达及最优后继策略的存在，没有将两个边缘最优值误作同一次实现同时取得的值。

这个证明在扩展非负费用、状态相关有限阈值菜单及真实分支上进行；它不是第6.5节实值有限动作最大化定理的逐字代入。

若 $h-l+1>2^q$，则任一截止内的二元树容量均不足，故 $C_q(l,h,s)=+\infty$。原初态的接口为 $C_q(0,P-1,0)$，第6.8节给出查询可行性、一般等待上界与最短等待端点。

相容域的大小有精确的有限表达。长度为 $m$ 的区间有 $P-m+1$ 个；它有 $m-1$ 个内部阈值，各排除唯一相位 $P-\theta$，故其相容相位恰有 $P-(m-1)=P-m+1$ 个。因此

$$
|\mathcal D_P|=\sum_{m=1}^{P}(P-m+1)^2
=\sum_{t=1}^{P}t^2
=\frac{P(P+1)(2P+1)}6.
$$

末式可由 $P=1$ 起归纳：将 $P(P+1)(2P+1)/6$ 加 $(P+1)^2$ 得 $(P+1)(P+2)(2P+3)/6$。预算 $0,\ldots,q$ 与此域的完整乘积有 $(q+1)|\mathcal D_P|$ 个元素，每个非终端节点至多 $P-1$ 个内部阈值。递推每步严格降低预算，有限个最小值选择与已证明的后继拼接给出有限最优策略。这个计数描述全部数学状态，不等于实际访问数，也不提供位复杂度或实际运行成本。$P=1$ 时唯一三元组为 $(0,0,0)$，各预算费用均为零；$q=0$ 时只使用式（AS.7）。

#### 6.9.1 未读节点与有限截止判据

固定 $p,P,b$，非空候选集 $A\subseteq\{0,\ldots,P-1\}$，已知事件数 $n\in\mathbb N$、整数截止 $D\ge n$、查询预算 $q\in\mathbb N$。令 $\mathsf F_q(A,n,D)$ 表示存在一份确定性向前协议，至多再读取 $q$ 次，在不迟于 $D$ 时精确识别同一原初 $r\in A$。此处允许当前读数尚未取得，因而在 $n$ 立即读取是合法的。置

$$
A_y(t)=\{r\in A:R_{p,P}(b,r;t)=y\},\qquad
R_{p,P}(b,A;t)=\{R_{p,P}(b,r;t):r\in A\}.
$$

**命题 6.2（有限截止的精确分解）。** $\mathsf F_0(A,n,D)$ 当且仅当 $|A|=1$。若 $q\ge1$，则

$$
\begin{aligned}
\mathsf F_q(A,n,D)\iff{}& |A|=1\\
&\text{或 }\exists t\in\{n,\ldots,D\}\ \forall y\in R_{p,P}(b,A;t),\quad
\mathsf F_{q-1}(A_y(t),t,D).
\end{aligned}
$$

**证明。** 单候选可以立即输出。没有后续读取时，单凭已知时间和旧档案不能分开不同候选，所以零预算基例必要。对非单候选成功协议，其下一次实际读数以前没有新的未知信息，故读取时刻 $t$ 只由现有知识决定。取得符号 $y$ 后，候选恰为非空纤维 $A_y(t)$，其后至多使用 $q-1$ 次查询，并受同一截止限制，给出必要性。反向，先向前执行 $t-n$ 个事件并读取，再按实际符号执行存在的对应子协议；像集合有限，只需为每个实际符号选一个子协议。各分支分割同一个原初候选集，这就给出一份在 $D$ 前成功的共同协议。对预算归纳完成证明；重复读取同一时刻仍使预算下降，不破坏归纳。$\square$

对实际读后相容节点 $A=[l,h]$、$s=n\bmod P$，在保留原始解码基准的条件下，有

$$
C_q(l,h,s)=\inf\{D-n:D\in\mathbb N,\ D\ge n,\ \mathsf F_q(A,n,D)\},
\qquad \inf\varnothing=+\infty.
$$

这由式（AS.8）的两向证明得到：即时重读为常量，无用读数可删，整周期可随整个后继协议和原始符号标记一同提前；反向最早内部阈值协议本身属于此截止协议类。有限值处该下确界也是最小值。一个给定截止失败仅说明费用大于 $D-n$，不能推出无穷；$|A|>2^q$ 才以对所有截止成立的容量论证给出不依赖等待长度的不可行性。

**命题 6.3（未读节点的即时信息）。** 取 $p=2$、$P=2$、$b=0$，已执行 $n=1$ 次加一，但尚未读取当前传感器；候选仍是 $[0,1]$，剩余一次查询。当前两个实际读数为
$$
d_1(0+1)=0,\qquad d_1(1+1)=1.
$$
立即读取即可识别，额外演化费用为零。若忽略读后域限制，将 AS.8 套入 $(l,h,s,q)=(0,1,1,1)$，唯一阈值 $\theta=1$ 的严格正等待是 $\delta(1,1)=2$，错误地给出费用二。该三元状态不在 $\mathcal D_2$，所以式（AS.8）不对它作出这个错误结论。

若另建包含“已经等待、当前读数尚未取得”的状态模型，当前阈值切开候选时必须允许零额外演化、消耗一次查询的立即读取，然后进入两个读后相容孩子。上述 DP 选择读后域，足以处理所有从初始已知 $b$ 开始的协议优化，但不把中间等待状态直接当成读后节点。

### 6.10 费用摘要与原始符号解码

$C_q$ 只保留相位 $s$，是因为已知解码基准的变化仅重标记实际符号，后续归一化响应和费用不变。原始实现仍须保存
$$
\beta=\left(b+\left\lfloor n/P\right\rfloor\right)\bmod p,
$$
或等价地保留初始 $b$ 和准确累计事件数 $n$。若 $n=cP+s$，则
$$
\left\lfloor\frac{n+\delta}{P}\right\rfloor=c+\left\lfloor\frac{s+\delta}{P}\right\rfloor.
$$
所以对包括零等待和跨多周期等待的 $\delta\ge0$，用
$$
\beta'=\left(\beta+\left\lfloor\frac{s+\delta}{P}\right\rfloor\right)\bmod p,
\qquad s'=(s+\delta)\bmod P
$$
更新，再将实际新读数 $y$ 解码为 $(y-\beta')\bmod p$。该值恰为零或一，候选更新具有以下精确的原始响应纤维解释。设 $I=[l,h]$；若 $s'>0$，两个不同原始符号 $\beta'$、$\beta'+1\pmod p$ 的实际来源分别为

$$
\{r\in I:R_{p,P}(b,r;n+\delta)=\beta'\}
=I\cap[0,P-s'-1],
$$

$$
\{r\in I:R_{p,P}(b,r;n+\delta)=\beta'+1\pmod p\}
=I\cap[P-s',P-1].
$$

这由第6.8.1节指示量等于零或一直接得到。$s'=0$ 时只有原始符号 $\beta'$，候选仍为 $I$。每个非空响应纤维为区间，且新阈值在其中恒定，所以都是读后相容孩子；空纤维不是实际分支。初始 $\beta=b$、$s=0$；初始 $b$ 还须作为输出参数保留，以便最后从识别出的 $r$ 恢复原初态 $x=bP+r$。

因此，$(l,h,s,q)$ 是归一化控制与未来费用的充分状态；固定模型参数后，$(b,l,h,s,\beta,q)$ 支持原始符号解码、动作选择、候选更新及目标输出。若还要求报告完整累计费用，则另外保留已累计的事件数和查询数；这不改变剩余费用递推。原合同中的完整事件档案也可以继续承担这些记忆，不必重新测量。

**命题 6.4（同一费用摘要不能解码同一原始符号）。** 取 $p=2,P=4,b=0$。一份历史在初读后等到 $n=2$，读取零。由于 $0\le r<4$，

$$
R_{2,4}(0,r;2)=\left\lfloor\frac{r+2}{4}\right\rfloor,
$$

故候选恰为 $r=0,1$，相位为二、$\beta=0$。另一份历史在初读后等到 $n=6$，读取一。对 $r=0,1$，$r+6$ 为 $6,7$，模八后的高位为一；对 $r=2,3$，$r+6$ 模八为 $0,1$，高位为零。因此它也恰留下 $[0,1]$、相位二，但 $\beta=1$。两份历史各花一次额外查询，可有同一剩余查询预算。

再等待一个事件，第一份历史的读数在 $r=0,1$ 上为

$$
R_{2,4}(0,0;3)=0,\qquad R_{2,4}(0,1;3)=1;
$$

第二份则为

$$
R_{2,4}(0,0;7)=1,\qquad R_{2,4}(0,1;7)=0.
$$

因此同一新原始零符号，在第一份历史要求留下 $r=0$，在第二份历史要求留下 $r=1$。

两种历史均是读后节点，候选、相位和剩余查询预算完全相同，但上述所需更新不同。因此不存在仅以 $(l,h,s,q)$ 和原始新符号为输入、在两种历史上都正确的统一更新函数。两者的归一化阈值行为与最优费用仍然相同；相位费用压缩不等于可以忘掉符号解码基准。

#### 6.10.1 任务充分性及完整档案

当 $P=p^k$ 时，全部高位未来响应的双点纤维核恰为模 $p^{k+1}$ 相等，这是第6.6.3节所引 Context Geometry 24.8–24.10的结论。这里改变的是从该行为取得目标的协议，不是凭等待生成一个原来不存在的状态区别。给定高位纤维的 $P$ 种可能性，阈值读数通过实际进位耦合取得低位；如果运算改成无进位的逐位群加法，固定高位传感器不会提供这些阈值。

因此对象、传感器、允许动作、实际档案、任务和费用必须一同声明。商状态的数学充分性没有自动给出固定窗口的可译性，也没有给出指定查询预算下的可执行性。AS.8 展示了 DP 的一个具体作用：在读后相容节点，归一化控制与剩余费用可以压成当前候选区间、已知相位和剩余预算。保留初始高位与累计事件档案，或本节给出的等价解码基准后，该表示才同时支持原始传感器的后继更新、目标恢复与费用合成。


#### 6.10.2 有限商与协议范围

AS.1–AS.8 采用上述读后闭合域，并区分归一化控制状态与原始读数解码状态。位传感器的有限循环模型要求 $p\ge2$、$P=p^k$；任意 $P\ge1$ 的扩展始终按第6.8节的有限块模型解释。素性仅在使用 $p$ 进整数解释时要求。取得目标仅为模 $p^{k+1}$ 的初态，不是整个 $p$ 进整数；协议为确定性、精确识别、无噪声且只向前演化，不覆盖平均费用、随机误差或任意外部观测。



### 6.11 Dyadic 最少查询预算下的锐等待

固定主动进位传感器合同：$p=2$，$P=2^j$，初态 $x=bP+r\pmod{2P}$，初始高位 $b$ 已取得且保留，未知 $0\le r<P$。允许的演化只有向前 $+1$；查询无噪声、不扰动状态，查询时刻可由已有记录决定。协议必须对每个初态精确识别原初态，查询数和实际单位演化次数分别计费。解码保留 $\beta=(b+\lfloor n/P\rfloor)\bmod2$ 或等价累计事件档案。讨论确定性协议，且额外查询最坏不超过 $j$ 次。

**定理 6.5（最少查询预算下的锐等待）。** 若 $j\ge1$，此协议类的最小最坏等待为
$$
W_j=(j-1)2^j+1.
\tag{DW.1}
$$
$j=0$ 时 $P=1$，初读已识别目标，故 $W_0=0$，额外查询和等待均为零。这里的最坏取同一已知 $b$ 纤维内全部 $r$；对两个 $b$ 结果相同。

首先，每次新读数在已知动作档案下至多提供一个阈值比特。确切地，写 $n=cP+s$、$0\le s<P$，有
$$
d_j(x+n)=(b+c+\mathbf1_{\{r\ge P-s\}})\bmod2.
\tag{DW.2}
$$
$s=0$ 给常量，其余相位给一个内部有序阈值。这个实际执行公式及其解码条件由主动传感器的 AS.2 提供。通用二元决策树容量由既有 `BinaryProtocolDepthLowerBound.adaptive_binary_protocol_depth_lower_bound` 所对应的叶数论证承担；任意二元问题的可用性不是本命题前提，实际阈值必须按向前等待实现。

**饱和容量迫使每次二等分。** 同一个 $b$ 下有 $2^j$ 个可能余数，深度至多 $j$ 的二元决策树最多有 $2^j$ 个叶。精确识别必须使每个余数对应不同叶，故树在这两个界上同时达到等号。根的任一孩子最多容纳 $2^{j-1}$ 个目标，两孩子的实际目标数合计为 $2^j$，所以各有恰 $2^{j-1}$ 个。递归应用同一论证，每个第 $i$ 层节点都含 $2^{j-i}$ 个目标，所有路径恰进行 $j$ 次有用查询。

阈值与区间求交仍是区间，因此每个内部节点的阈值被唯一确定为该区间的中点。不能通过早停、无用读数或让某一支拥有额外查询预算绕过此结论；这些做法都会使总叶容量严格不足。等待时刻由已有记录选择，不另带一个观察未知余数的接口。

**实际等待的下界。** 沿余数 $r=P-1$ 的路径，每次归一化响应为一。被迫的第 $i$ 个阈值及相位为
$$
\theta_i=P-2^{j-i},\qquad s_i=P-\theta_i=2^{j-i},
\quad 1\le i\le j.
\tag{DW.3}
$$
首读至少等待 $P/2$ 个单位事件。随后相位严格下降；只允许向前演化时，从 $s_{i-1}$ 到 $s_i$ 至少等待 $P-s_{i-1}+s_i$。跨越额外完整周期只会增加等待。相加得到
$$
n_j\ge \frac P2+\sum_{i=2}^j(P-s_{i-1}+s_i)
=(j-1)P+1.
\tag{DW.4}
$$
求和中 $\sum_{i=2}^j(-s_{i-1}+s_i)=-s_1+s_j$，而 $s_1=P/2,s_j=1$，所以右端恰为 $(j-1)P+1$。空和约定覆盖 $j=1$。整个下界沿同一个实际来源 $r=P-1$ 得到，已知 $b$ 只能重标记读数，不改变这些必须出现的相位。

**同一协议达到下界。** 在每个候选区间取中点阈值，并在它最早的未来相位查询。第一个等待为 $P/2$。之后第 $i$ 个阈值相对前一阈值改变恰 $2^{j-i}$：前一响应为零时阈值下降，相位上升，等待为 $2^{j-i}$；前一响应为一时阈值上升，相位下降，等待为 $P-2^{j-i}$。每一项均不超过后一值。因此对每条真实来源路径，
$$
n_j\le\frac P2+\sum_{i=2}^j(P-2^{j-i})
=(j-1)P+1.
\tag{DW.5}
$$
因为 $\sum_{i=2}^j2^{j-i}=P/2-1$，上式的和确为 $(j-1)P+1$。所有等待均在 $1,\ldots,P-1$，每次读取后的候选为真子区间，故协议始终处于第6.9节的读后相容域。用保留的 $\beta$ 解码实际原始符号，即能按中点分支；归纳至第 $j$ 次时每个来源都变成单候选，最后输出原初 $bP+r$。全一响应路径逐段取得较大等待，达到等号。下界和上界属于同一模型及同一最坏费用，遂得式（DW.1）。$\square$

对于 $j\ge1$，还可逐路径准确记录费用。把 $r$ 的二进展开记为 $b_1\cdots b_j$，此处的 $b_i$ 是未知余数的位，与已知初始高位 $b$ 区分。最早相位的中点协议在第 $i$ 次查询取得归一化位 $b_i$：前 $i-1$ 位已经把候选限制为共享该前缀的长度 $2^{j-i+1}$ 区间，中点将下一位为零和为一的两个半区间分开。故这一识别由实际传感器逐步完成，并未先读取未知二进展开。后一次的阈值方向由刚取得的该位决定。具体地，第 $i+1$ 段等待为
$$
2^{j-i-1}+b_i\bigl(P-2^{j-i}\bigr),\qquad1\le i<j,
$$
其常数项连同首段满足
$$
\frac P2+\sum_{i=1}^{j-1}2^{j-i-1}=P-1.
$$
上述逐步费用相加为
$$
n_j(r)=P-1+\sum_{i=1}^{j-1}b_i\bigl(P-2^{j-i}\bigr).
\tag{DW.6}
$$
各系数正，因此最高 $j-1$ 位全一的两个余数 $P-2,P-1$ 恰给最大费用，最高 $j-1$ 位全零的两个余数 $0,1$ 恰给最小费用 $P-1$；$j=1$ 时两对均为整个二点集合。末次响应决定最后一个候选区别，但不会改变已经付出的末次查询时刻。

容量饱和强制阈值树，但不强制所有成功协议都在最早相位读取。有的最优协议可以在非最坏分支额外等待而仍保持同一最坏值；DW.6 只属于所述最早相位中点协议。

**命题 6.6（最优绝对时序不唯一）。** 对 $j=3,P=8$，存在两个均使用至多三次额外查询、最坏等待均为 $17$ 的精确协议，其逐来源完成时刻不同。

**证明。** 式（DW.6）的两个权重为 $8-4=4$、$8-2=6$，常数项为七，故最早中点协议在四对来源 $\{0,1\},\{2,3\},\{4,5\},\{6,7\}$ 上的完成时刻依次为

$$
7,\qquad 13,\qquad 11,\qquad 17.
$$

实际首查询在 $n=4$；第一响应为零时第二查询在 $n=6$，为一时在 $n=10$。仅当两个已见归一化响应均为零、候选已为 $\{0,1\}$ 时，将末次查询从 $n=7$ 延后一个 $P$ 周期到 $n=15$，其他分支不变。这个选择只用已取得记录，且 $15>6$，所以全程仍只向前演化并仅再读一次。式（AS.2）给延后一周期的原始高位加一模二；同步更新 $\beta$ 后，归一化阈值仍为一，仍区分 $r=0,1$。新协议四对来源的完成时刻为

$$
15,\qquad 13,\qquad 11,\qquad 17.
$$

两个已知初始高位 $b$ 下都作相同的归一化运输，故所有原初态仍精确恢复。两个协议的最坏等待都是 $17=W_3$，由定理6.5均最优；但新协议在 $r=0,1$ 上的时间已不同于式（DW.6）。因此饱和容量所强制的中点阈值树，不强制最优协议的绝对时序唯一。$\square$

由此，对于 $j\ge3$，最少查询协议的最坏等待 $(j-1)P+1$ 严格大于不限制查询预算时的最短最坏等待 $P-1$。两种最优值不能拼成共同可达费用对。$j=2$ 也已有 $W_2=5>3$；$j=1$ 两者均为一。这是同一进位关系内部的实际取得成本差异，不是重新编码造成的信息损失。

差值可以直接写为
$$
W_j-(P-1)=(j-2)P+2,\qquad
j(P-1)-W_j=P-j-1\ge0\quad(j\ge1).
$$
第一差值在 $j\ge2$ 严格为正，在 $j=1$ 为零；$j=0$ 单独为零。第二差值的非负性来自 $2^j\ge j+1$：$j=1$ 取等号，若 $2^j\ge j+1$，则 $2^{j+1}\ge2j+2\ge j+2$，归纳即可。

既有 AS.5 的上界 $j(P-1)$ 仍然成立，本命题在 $P=2^j$ 且预算恰取最少查询数时将它锐化；AS.8 的一般区间／相位／预算递推不被改动。本命题没有给非二幂 $P$ 的闭式，也没有处理更多查询预算下的全部边界、平均费用、随机误差或有噪声协议。

## 追加锚（本行以下为增补区）

## 7. 最少查询的完成相位与隐藏调度的记忆代价

Claim status: open。这里研究第6.11节主动进位传感器的一项新恢复任务：协议完成后，仅把一个时钟摘要和最后一次原始传感器读数交给接收端，先前逐次读数不再可访问。已知调度和隐藏调度是两份不同合同。本节给出它们相差一位时钟记忆的精确下界及达到构造；不是关于任意时钟的普遍信息增益律。

### 7.1 同一来源、饱和查询与最终两点纤维

固定 $j\ge1$、$P=2^j$，初态 $x=bP+r\pmod{2P}$，初始高位 $b\in\{0,1\}$ 已知，$r\in\{0,\ldots,P-1\}$ 未知。沿用第6.11节的确定性、无噪声、不扰动、仅向前加一、至多 $j$ 次额外查询的精确识别合同。允许依赖旧记录等待任意有限事件数；不假设最早查询或最短等待。完成时刻 $N$ 专指第 $j$ 次实际查询的事件数，最终读取之后的任意人为报告延迟不计入 $N$。

二元叶容量在 $P=2^j$ 上饱和，故每层必须二等分当前候选区间；这是第6.11节已给出的论证，而非本节的新一般定理。写

$$
r=2t+u,\qquad 0\le t<P/2,\quad u\in\{0,1\}.
\tag{TM.701}
$$

最终查询前，当前候选恰为 $\{2t,2t+1\}$。这两个来源的前 $j-1$ 个归一化响应及相应原始响应完全相同，所以任何固定确定性调度 $\pi$ 的最终查询时刻对它们相同，记为 $N_\pi(t)$。最终阈值必须是 $2t+1$，因此

$$
S:=N_\pi(t)\bmod P=P-1-2t,\qquad
N_\pi(t)=c_\pi(t)P+S,
\quad c_\pi(t)\in\mathbb N_0.
\tag{TM.702}
$$

$S$ 取遍 $P/2$ 个奇相位。将同一实际来源代入原始高位传感器，得到

$$
Y=\left\lfloor
\frac{(bP+2t+u+N_\pi(t))\bmod2P}{P}
\right\rfloor
=(b+c_\pi(t)+u)\bmod2.
\tag{TM.703}
$$

这里用的是 $2t+S=P-1$；$u=0$ 时尚未进位，$u=1$ 时恰发生一次进位。这一恒等式对所有允许的整周期等待成立。

### 7.2 已知协议中的相位恢复与最小时钟字母表

**命题 7.1（固定调度的终端压缩）。** 固定一份为接收端所知的成功调度 $\pi$ 及初始高位 $b$。仅由 $(S,Y)$ 可以恢复原初余数，具体为

$$
t=\frac{P-1-S}{2},\qquad
u=(Y-b-c_\pi(t))\bmod2,\qquad r=2t+u.
\tag{TM.704}
$$

在终端实际记录上，$r\mapsto(S,Y)$ 是从 $P$ 个来源到
$\{1,3,\ldots,P-1\}\times\{0,1\}$ 的双射。若时钟摘要限定为仅依赖完成时刻的映射 $\phi(N)$，接收端除此之外只持有 $Y,b,\pi$，则精确恢复需要至少 $P/2$ 个实际时钟标签；$S=N\bmod P$ 达到该下界。

证明。由（TM.702）恢复唯一的 $t$，已知调度确定 $c_\pi(t)$，再由（TM.703）恢复 $u$。每个 $t$ 的两个 $u$ 给出两个相反的 $Y$，从而实际像恰为所述直积。若 $\phi$ 只取 $k$ 个实际值，二值 $Y$ 与它的联合读数至多有 $2k$ 个值。恢复全部 $P$ 个余数要求 $2k\ge P$；相位摘要恰有 $P/2$ 个值。$\square$

这个最小性只计接收端终端时钟标签，不计整份 $\pi$ 的描述、重建 $c_\pi(t)$ 的计算或采集阶段控制器的空间。一个巨大调度表不能因此被称为免费记忆。最早中点协议没有这个未指定的解码表：式（DW.6）给

$$
N_{\rm early}(t)=P-1+P\,\operatorname{wt}(t)-2t,
\qquad c_{\rm early}(t)=\operatorname{wt}(t),
\tag{TM.705}
$$

其中 $\operatorname{wt}(t)$ 是 $t$ 的 $j-1$ 位二进制中一的个数。于是只需由已恢复的 $t$ 计算位奇偶即可解码。计数器必须实际可读，并在最后查询时锁存；仅仅在外部模型里存在一个 $N$ 不足以提供该端口。

### 7.3 隐藏调度使最小时钟字母表加倍

**命题 7.2（跨调度统一恢复的严格代价）。** 仍固定 $j,b$，现在要求同一个解码器对第7.1节的全部成功调度同时正确，且不接收调度标识或之前的查询档案。其输入仅为 $(\phi(N),Y,b)$，$\phi:\mathbb N_0\to Z$ 仅依赖完成时刻。则在全部实际完成时刻上

$$
|\operatorname{im}_{\rm actual}\phi|\ge P.
\tag{TM.706}
$$

取 $V=N\bmod2P$ 达到下界：实际 $V$ 为 $2P$ 周期中的 $P$ 个奇数。统一解码器为

$$
S=V\bmod P,\quad
c_2=\left\lfloor V/P\right\rfloor,\quad
t=\frac{P-1-S}{2},\quad
u=(Y-b-c_2)\bmod2.
\tag{TM.707}
$$

证明。充分性来自（TM.702）—（TM.703）及
$\lfloor N/P\rfloor\bmod2=\lfloor (N\bmod2P)/P\rfloor$。

为证明必要性，从最早中点协议出发。对每个最终两点纤维 $\{2t,2t+1\}$，可在最后查询之前额外等待零个或一个 $P$ 周期。决策只依赖前 $j-1$ 次已取得的读数，因此两种调度均合法；多等待一周期保持阈值不变而翻转原始符号。于是对每个 $t$，最终商 $c$ 的两种奇偶都可实现。固定最后的原始符号为 $Y=0$：给定 $t$ 和所选奇偶，令 $u=(-b-c)\bmod2$，该来源的实际末读正好为零。当 $t$ 与奇偶分别取遍时，得到 $P$ 个不同的原初余数。对应的完成时刻两两不同：不同 $t$ 有不同模 $P$ 相位，同一 $t$ 的两个时刻相差 $P$。若这些时刻中的两个被 $\phi$ 合并，解码器会在相同的 $(\phi(N),0,b)$ 上被要求输出两个不同余数，矛盾。因此至少需要 $P$ 个时钟标签。上述模 $2P$ 编码正好使用 $P$ 个实际值，达到下界。$\square$

固定已知协议的合同需要 $\log_2(P/2)=j-1$ 位终端时钟编码，跨全部隐藏协议的合同需要 $\log_2P=j$ 位。差出的位是已经累计多少个整周期的奇偶，不是增加了关于 $r$ 的独立来源信息。接收端知道完整策略时，该奇偶可由已恢复的 $t$ 重新计算；策略被隐藏时必须从别处保留。

**命题 7.3（最优等待也不能消除调度歧义）。** $j=3$、$P=8$、$b=0$ 时，即使两份调度的最坏等待均为最优值 $17$，相位和原始末读仍可相同而来源不同。

证明。第6.11节命题6.6给出最早中点协议，以及仅在最后候选为 $\{0,1\}$ 时将末读从七推迟到十五的另一份协议；两者最坏等待均为十七。最早协议的 $r=0$ 给 $N=7,S=7,Y=0$；延后协议的 $r=1$ 给 $N=15,S=7,Y=0$，因为 $(1+15)\bmod16=0$。二者在不标记协议的 $(S,Y)$ 上相同，原初余数却不同。模十六的完成记录为七和十五，能区分它们。$\square$

这只是最优协议类内相位摘要不充分的见证；命题7.2的全参数下界量化全部饱和查询成功协议，并未证明每个 $j$ 的最优等待子类都需要同一大小的统一时钟编码。

### 7.4 时钟是已取得前缀的可读保存位置

固定已知 $\pi,b$，取 $R$ 在 $\{0,\ldots,P-1\}$ 上均匀。写 $R=2T+U$，则 $T$ 均匀而 $U$ 是与它独立的公平位。式（TM.702）使 $S$ 与 $T$ 双射对应；式（TM.703）把 $U$ 按 $T$ 决定的奇偶翻转，故 $Y$ 仍为与 $T$ 独立的公平位。因此由实际联合律直接得到（单位 bit）

$$
I(R;S)=j-1,\qquad
I(R;Y)=1,\qquad
I(S;Y)=0,\qquad
I(R;S,Y)=j.
\tag{TM.708}
$$

最终时刻 $N_\pi(T)$ 也是 $T$ 的单射函数：相等的时刻先给相等的模 $P$ 相位，再给相等的 $T$。所以

$$
H(N_\pi(T))=I(R;N_\pi(T))=j-1.
\tag{TM.709}
$$

增添整周期等待可以改变平均或最坏费用，却不改变固定确定性协议下这个熵。协议随机化或对接收端未知时，必须把随机种子、策略变量及其共同来源写入联合律，不能直接沿用（TM.708）—（TM.709）。

最终查询以前已经取得的前缀恰确定 $T$，调度把它写入将要到达的相位 $P-1-2T$。因此完成相位的 $j-1$ 位来自此前实际读数；它不是一次未经计费的额外查询。这个例子把指定空间余数、采集路径的时钟相位、最后读数和接收端记忆连接起来：互相恢复依赖相位精度、已知调度或周期奇偶，以及实际可访问的联合记录。若时钟被固定为只有一个标签，则除 $j=1$ 外，单个末读至多区分两个余数，不再完成原任务。

### 7.5 来源与未覆盖范围

本节是第6.11节主动传感器费用公式和饱和决策树的仓内综合推导；承重新增为固定调度与隐藏调度两种终端访问合同的严格字母表差距及统一解码。已读取 BinaryProtocolDepthLowerBound.lean 的 adaptive_binary_protocol_depth_lower_bound，它承担有限二元协议的通用容量下界；已读取 PassiveAdaptiveTranscriptUpperBound.lean 的 passive_adaptive_transcript_upper_bound，其适用面是固定来源上指定被动实验族的完整联合读数。源文件分别位于 D5/S3/ConceptDynamics/Coding/ 和 D5/S3/ConceptDynamics/Experiment/，它们都不是本节具体完成时刻公式或隐藏调度下界的新增形式核验。

这里不把“时钟步数等于预测深度”作为前提，因而不与 ClockTimeVersusRefinementDepth.clock_time_does_not_determine_refinement_depth 的有限反例冲突。时钟在本模型中成为记忆，是由指定协议建立的关联，不是时间的一般定义。当前结论限于无噪声二幂模型、最终查询瞬间、已知初始高位和实际可读事件计数；未处理有噪声计时、未知 $b$、连续时钟误差或采集阶段最小工作空间。未新增 Lean、冻结或消化结算，也未据此宣称文献原创。

## 追加锚（本行以下为增补区）

## 8. 完成相位带误差时的因果记忆修复

Claim status: open。本节在第7节同一终端访问合同中放松时钟精度，保持原来的精确识别目标。它不改变采集阶段的查询数，而计算在最后查询前已取得的前缀中，最少要另存多少种标签，才能在有误差的时钟读数下恢复初态。接收端知道固定确定性调度 $\pi$ 及初始高位 $b$；隐藏调度的第7.3节合同不适用下面的解码器。

### 8.1 圆周误差与先于噪声取得的标签

仍取 $P=2^j$、$r=2t+u$，令 $n=P/2$。真实完成相位为

$$
S_t=P-1-2t\pmod P,\qquad 0\le t<n.
\tag{TM.801}
$$

接收端不再取得精确 $S_t$，而取得圆周 $\mathbb R/P\mathbb Z$ 上的 $\widehat S$，其误差合同是

$$
d_P(\widehat S,S_t)\le\varepsilon,\qquad
d_P(a,b)=\min_{k\in\mathbb Z}|a-b+kP|.
\tag{TM.802}
$$

这是逐来源成立的最坏误差界；允许误差由对手选择，不赋予它概率律。最后的原始传感器位 $Y$ 仍精确。允许发送的补充标签为 $z(t)$，它只依赖在末读之前已经取得的前缀 $t$；不得依赖尚未发生的 $u$ 读数或尚未取得的时钟误差。接收端仅持有 $(\widehat S,Y,z(t),b,\pi)$。

记圆周中以 $S_t$ 为中心、半径 $\varepsilon$ 的闭球为 $B_t$。两个不同前缀能够被同一时钟读数混淆，当且仅当

$$
B_t\cap B_{t'}\ne\varnothing
\quad\Longleftrightarrow\quad
d_P(S_t,S_{t'})\le2\varepsilon
\quad\Longleftrightarrow\quad
d_n(t,t')\le\varepsilon,
\tag{TM.803}
$$

其中 $d_n(t,t')=\min\{|t-t'|,n-|t-t'|\}$。中间等价的反向取圆周最短弧中点；因此误差恰等于阈值时，两球相接也必须判为混淆。末个等价来自 $d_P(S_t,S_{t'})=2d_n(t,t')$。

在前缀集 $\mathbb Z/n\mathbb Z$ 上将不同且满足 (TM.803) 的顶点连边，得到有限混淆图 $G_\varepsilon$。这个图一般不是等价类的并：不同闭误差球可以链式相交而两端不相交，不能直接当作确定读出的一条纤维。

### 8.2 标签恰须切开可能混淆的前缀

补充标签能对全部允许误差完成精确恢复，当且仅当它在 $G_\varepsilon$ 的每条边上取不同值。

证明。若两个相邻前缀得到相同标签，取两球交点作同一个 $\widehat S$。对每个前缀分别选择
$u=(-b-c_\pi(t))\bmod2$，则 (TM.703) 给出相同的最终读数 $Y=0$。这两份实际来源的 $r=2t+u$ 不同，接收端全部输入却相同，所以不能统一解码。这里为两来源选取各自允许的误差，是最坏误差合同要求比较的两个实际实现，没有把它们拼成一个来源。

反向，若标签分开所有相邻前缀，则对给定的 $(\widehat S,z)$，至多有一个同标签的 $t$ 满足 $\widehat S\in B_t$：若有两个，它们的球在 $\widehat S$ 相交，会违反标签条件。真实来源保证至少有一个，故 $t$ 唯一；再以已知 $c_\pi(t)$ 和精确 $Y$ 用 (TM.704) 恢复 $u,r$。这给实际像上的解码器，不要求对不满足误差合同的输入输出任意“正确答案”。$\square$

因而最小标签数是该具体混淆图的色数。图着色与零错误修复的关系是成熟机制，相关经典文献为 H. Witsenhausen, [The zero-error side information problem and chromatic numbers (Corresp.)](https://doi.org/10.1109/TIT.1976.1055607), IEEE Transactions on Information Theory 22(5), 592–593, 1976。本节已经直接证明所需的单次有限图桥梁；承重的是由主动进位协议导出的因果前缀图及下面的精确阈值，不能把一般着色原理重新申领为新增理论。

### 8.3 二幂圆周上的零位、一位、两位阈值

**定理 8.1（有限误差区间的精确修复容量）。** 当 $P\ge8$ 为二幂时，记本节合同下最小补充标签数为 $L_P(\varepsilon)$，则

$$
L_P(\varepsilon)=
\begin{cases}
1,&0\le\varepsilon<1,\\
2,&1\le\varepsilon<2,\\
4,&2\le\varepsilon<4.
\end{cases}
\tag{TM.804}
$$

三个区间分别可取常值标签、$z(t)=t\bmod2$、$z(t)=t\bmod4$。当 $P=8$ 时，最后的四标签结论对全部 $\varepsilon\ge2$ 成立。小规模例外为：$P=2$ 时全部误差下只需常值标签；$P=4$ 时 $\varepsilon<1$ 只需一个标签，$\varepsilon\ge1$ 恰需两个。

证明。若 $\varepsilon<1$，不同整数前缀的循环距离至少一，图无边，常值标签足够。

若 $1\le\varepsilon<2$，只连接相邻前缀。对 $n\ge4$，这是一个偶数循环；$t\bmod2$ 分开包括首尾回绕在内的每条边。有边排除常值标签，故两种标签必要且充分。$n=2$ 时图就是二点边，结论相同。

现在 $n=P/2\ge4$ 且 $2\le\varepsilon<4$。因 $n$ 被四整除，同余模四的不同前缀，其循环距离至少四，所以模四标签始终足够；$n=4$ 时每个标签只对应一个前缀，更无歧义。

为证四标签必要，只需用 $\varepsilon=2$ 的子图。每个连续三点 $t,t+1,t+2$ 两两相邻，三个或更少标签若可行，就必须在每个三点窗口中用尽三种颜色。比较两个相邻三点窗口，迫使 $z(t+3)=z(t)$，下标模 $n$ 计算。由于 $n$ 为二幂而 $\gcd(n,3)=1$，循环上的加三遍历全部顶点，这又迫使标签恒定，与相邻顶点须不同矛盾。因此三标签不可能，结合模四达到构造得四。该论证也覆盖 $n=4$，其混淆图直接为四点完全图。

当 $n=4$ 时循环距离最大为二，$\varepsilon\ge2$ 已使混淆图完整，继续扩大误差也只需保留四种前缀。$n=2$ 的距离最大为一，给所述小规模结论；$n=1$ 时前缀本来只有一个，由 $Y,b,\pi$ 即可恢复末位，任何时钟误差都无额外影响。$\square$

标签数对应的定长附加存储分别是零、一、两 bit。阈值一和二处的跳变采用闭误差界，不能将等号划入前一个低成本区间。若 $P\ge16$ 且 $\varepsilon\ge4$，本定理未给出全范围最优式；例如五个连续前缀已经两两混淆，至少需五标签，不能继续使用四标签结论。

### 8.4 与观察纤维、已发生记录和取得成本的对应

一个接收端事后看到的误差球，与采集端可以预先计算的标签，属于不同接口。给每个接收读数的候选来源临时编号，可能得到更小的局部标签数，但该编号依赖尚未取得的 $\widehat S$，不符合 $z=z(t)$ 的因果约束。本节之所以要同时满足整个混淆图的着色条件，正是因为同一个前缀在不同允许误差下只能发送同一个已保存标签。

这个差距在 $\varepsilon=2,P\ge8$ 时已经严格出现。对任意固定 $\widehat S$，允许的真实相位落在一段长度四的闭圆弧内；奇相位间距为二，所以至多有三个候选，且以任一奇相位为中心时恰有三个。固定原始末读 $Y$ 后，每个候选 $t$ 又只对应一个 $u$，故接收端单次候选来源数的最大值正好为三。然而定理8.1证明预先写入的标签至少有四种。分别为各个三点候选集选择最省标签，不能保证这些选择来自同一函数 $z(t)$；这是一项跨上下文的相容义务，不能由最大单纤维大小代替。

仓内 D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring.lean 的 minimum_repair_labels_eq_chromatic_eq_fiber_diversity，针对确定读出与目标的缺陷图，允许在其来源上选择标签，并得到最大纤维目标数。本节的误差球交叠和先于误差取得的标签有额外约束，不能直接把该声明的最大纤维式套在每个 $\widehat S$ 的候选集上。上面的两方向证明给出了本合同到混淆图的具体桥梁；没有新增 Lean 声明或将这座桥报成已形式核验。

这个有限结果将两种补偿明确连接：提高实际时钟精度可以降低补充记忆，保留从旧读数得到的前缀标签可以允许较粗时钟。但没有增大原来关于同一余数的独立证据，也没有免除取得 $t$ 的前 $j-1$ 次查询。边界必须同时保存可读时钟、精确末读、适用的已知调度，以及该误差合同下必要的标签；单独报告时钟误差上界或当前后验都不足以代替这一联合恢复条件。

## 追加锚（本行以下为增补区）

## 9. 隐藏调度的截止预算与精确时钟字母表

Claim status: open。第7节区分已知固定调度与全部隐藏调度，第7.3节只给出两份最优等待调度也能发生歧义的见证。本节补齐中间问题：若接收端知道调度符合一个共同截止上界，但不知道具体调度，究竟要保留多少种时钟标签？答案取决于截止所允许的调度族，而不是单条路径的等待时间。

### 9.1 调度族的实际终端类型

保持第7.1节全部假设：$j\ge1$，$P=2^j$，已知初始高位 $b$，未知余数 $r=2t+u$，$0\le t<n=P/2$，$u\in\{0,1\}$；精确识别全部来源，至多 $j$ 次额外无噪声高位查询，时钟在末次查询瞬间锁存。两位变量 $b,u$ 与时间单位仍按同一原始传感器解释，禁止在终端接口中暗中把原始末读 $Y$ 替换为已校正的 $u$。

对任意非空成功调度族 $\mathcal F$，定义前缀 $t$ 的可达周期奇偶集

$$
B_{\mathcal F}(t)=
\left\{
\left\lfloor N_\pi(t)/P\right\rfloor\bmod2:
\pi\in\mathcal F
\right\}\subseteq\{0,1\}.
\tag{TM.901}
$$

一份调度在最终两点纤维上的时间 $N_\pi(t)$ 不依赖末位 $u$，且
$N_\pi(t)\bmod P=S_t=P-1-2t$。因此同一个实际完成时刻唯一确定 $(t,c\bmod2)$，其中 $c=\lfloor N/P\rfloor$。调度族只描述哪些这样的类型实际可能出现；不要求某一份调度同时实现全部类型。

**命题 9.1（隐藏调度族的精确终端容量）。** 接收端知道 $\mathcal F,j,b$，但不接收 $\pi$ 或旧查询档案；它只能取得 $(\phi(N),Y,b)$，其中 $\phi$ 是预先固定、仅依赖实际完成时刻的函数。对全部 $\pi\in\mathcal F$ 与全部来源统一精确解码所需的最小时钟标签数为

$$
M(\mathcal F)=\sum_{t=0}^{n-1}|B_{\mathcal F}(t)|.
\tag{TM.902}
$$

这里标签数取 $\mathcal F$ 的全部实际完成时刻的像；不计不可发生输入的任意延拓。

证明。对每种可达类型 $(t,p)$，选取实现它的调度和完成时刻，并令 $u=(-b-p)\bmod2$。由于时间不依赖 $u$，这仍是该调度中的实际来源，式（TM.703）给相同原始末读 $Y=0$。不同类型给不同 $r=2t+u$：不同 $t$ 位于不同二点纤维，同一 $t$ 的不同 $p$ 给相反的 $u$。因而这些见证时刻必须获得两两不同的 $\phi$ 标签，否则同一个终端输入被要求解码为两个来源。这给（TM.902）的下界。

取 $\phi(N)=N\bmod2P$，其实际值与可达类型一一对应：由 $S=\phi(N)\bmod P$ 恢复 $t=(P-1-S)/2$，由 $\lfloor\phi(N)/P\rfloor$ 取得 $p$，再以 $u=(Y-b-p)\bmod2$ 恢复末位。该实际像恰有（TM.902）个值，也可重新编号为同样大小的标签集。故下界达到。$\square$

单一已知调度的每个 $B_{\mathcal F}(t)$ 都是单点集，恢复第7.2节的 $P/2$；全部隐藏调度使每个集都为 $\{0,1\}$，恢复第7.3节的 $P$。上述求和还处理两者之间的实际可达调度族，不需要把调度标识免费加入接收端。

### 9.2 逐前缀完成时刻的可实现范围

最早中点协议在前缀 $t$ 上的完成时刻为

$$
E_t=P-1+P\,\operatorname{wt}(t)-2t,
\qquad
W=\max_t E_t=(j-1)P+1.
\tag{TM.903}
$$

这里 $\operatorname{wt}(t)$ 取其 $j-1$ 位展开；$j=1$ 时 $t=0$、重量为零。式（TM.903）是第6.11节已给出的具体等待公式。

每份饱和查询成功调度都满足

$$
N_\pi(t)=E_t+P K_\pi(t),\qquad K_\pi(t)\in\mathbb N_0.
\tag{TM.904}
$$

证明这一限制时，先用饱和二元容量固定每个来源的中点阈值路径，再沿这条路径比较实际查询时刻：每次所需阈值只规定一个模 $P$ 相位；最早协议逐次取不早于上一查询的最小允许时刻。任意其他调度逐步都不能早于该选择，最终相位又相同，故完成时间与 $E_t$ 相差非负整数个 $P$。原始读数的周期奇偶虽可翻转，控制器由实际计数可恢复归一化响应，因此不改变这条阈值路径。

反向，每一张非负整数表 $K(t)$ 都有一个因果实现：前 $j-1$ 次查询按最早协议执行，它们已经确定 $t$；只在最后查询之前，依该已获前缀多等 $P K(t)$ 次前进，再作原来的末次查询。等待选择不读取未知的 $u$，额外整周期保持区分这两个来源的阈值。因而（TM.904）不仅是逐前缀必要条件，也同时刻画全部可实现终端时间表。这个存在构造不主张存储整张表的控制器空间最小。

令 $\mathcal F_D$ 为最坏末次查询时刻不超过整数截止 $D$ 的全部上述成功调度。$D<W$ 时该族为空，不能把空族上的真空解码称作识别了来源。对 $D\ge W$，前缀 $t$ 的实际可达时刻恰为

$$
\{E_t+Pk:0\le k\le\lfloor(D-E_t)/P\rfloor\}.
\tag{TM.905}
$$

其中每个时刻都能由只延迟该前缀的构造实现，其他前缀保留最早时间且仍不超过 $D$。允许的 $k$ 是从零开始的连续整数集，所以

$$
|B_{\mathcal F_D}(t)|
=1+\mathbf1_{\{E_t+P\le D\}},
\qquad
M(\mathcal F_D)
=n+\#\{t:E_t+P\le D\}.
\tag{TM.906}
$$

这是截止限制进入终端恢复问题的具体接口：只有当同一前缀的两种周期奇偶都在允许族中实际出现时，该前缀才多占一个不可合并的时钟标签。

### 9.3 最优调度与截止松弛的二幂阶梯

**定理 9.2（共同截止下的锐时钟容量）。** 对整数 $h\ge0$，取 $D=W+h$，要求同一解码器对全部最坏完成时刻不超过 $D$ 的隐藏调度正确，则

$$
\boxed{
M(\mathcal F_{W+h})
=P-j+\#\{i\in\{1,\ldots,j\}:2^i\le h\}.
}
\tag{TM.907}
$$

特别地，全部最优等待调度的最小时钟字母表有 $P-j$ 个标签；松弛达到 $2,4,\ldots,2^j$ 时依次增加一个标签，$h\ge P$ 后达到全部隐藏调度的 $P$ 个标签上界。

证明。先取 $j\ge2$。由（TM.903），前缀 $t$ 获得第二种周期奇偶的最小松弛阈值为

$$
E_t+P-W
=(\operatorname{wt}(t)-j+3)P-2t-2.
\tag{TM.908}
$$

若 $\operatorname{wt}(t)\le j-3$，右边严格为负，$h=0$ 时已经容许两种奇偶。其余前缀恰有 $j$ 个：在 $j-1$ 位中恰缺一个一的 $j-1$ 个前缀，以及全一前缀。前一类可写为

$$
t=n-1-2^k,\quad 0\le k\le j-2,
\qquad E_t+P-W=2^{k+1};
\tag{TM.909}
$$

后一类 $t=n-1$ 满足 $E_t=W$，故第二奇偶阈值为 $P=2^j$。因此 $h=0$ 有 $n-j$ 个双奇偶前缀、$j$ 个单奇偶前缀，合计 $2(n-j)+j=P-j$ 个类型；此后恰在（TM.909）和 $P$ 的每个阈值新增一种类型。将计数代入命题9.1即得（TM.907），并同时得到下界和达到编码。

$j=1$ 时只有 $t=0$、$E_t=W=1$，允许完成时刻为 $1+2k\le1+h$。$h<2$ 只有偶 $k$ 的初始类型；$h\ge2$ 两种 $k$ 奇偶都可达，标签数由一变二，也符合（TM.907）。$\square$

例如 $j=3$、$P=8$、$W=17$ 时，四个前缀的最早完成时刻分别是 $7,13,11,17$；最优协议族另容许 $t=0$ 在十五完成，所以实际模十六类型为 $\{7,15,13,11,1\}$，恰有五种。对同一模型，松弛 $h=0,1$ 需五标签，$2\le h\le3$ 需六，$4\le h\le7$ 需七，$h\ge8$ 需八。第7.3节的碰撞只是这五类中不能被同一相位标签合并的一对。

小参数也有明确界限：$j=2$ 时，$h=0,1$ 的标签数为二，$h=2,3$ 为三，$h\ge4$ 为四。对 $j\ge3$，$2^{j-1}<P-j<2^j$，故全部最优调度虽然比任意隐藏调度少了 $j$ 个实际标签，定长二进制存储仍需 $j$ 位；不能把字母表缩减报成一位定长存储节省。

### 9.4 截止、接口与内部记忆的边界

（TM.907）的单调增加来自需要同时服务的隐藏调度族扩大。同一已知策略获得额外等待额度，并不会因此失去第7.2节的 $P/2$ 标签解码；允许选择一个策略与要求对全部未知策略统一正确是不同量词。上式只计接收端的时间标签，未给采集阶段最小工作空间、平均编码长度或最省解码计算量。

若采集端在末次读取后把 $Y$ 校正为 $u=(Y-b-\lfloor N/P\rfloor)\bmod2$ 再交给接收端，则 $(S,u)$ 总能以 $P/2$ 个相位标签恢复 $r$。这是允许处理末读并改变输出接口的新合同；不能借它否定保持原始 $Y$ 的下界。反过来，若实际时钟端口不能分辨同一前缀的两种周期奇偶，又不提供这项校正，则命题9.1给出了具体不能合并的来源见证。

本节将第6.11节的主动取得费用、第7节的终端时钟恢复与隐藏策略的不确定性接成一个精确有限模型；新综合推导是共同截止对可达终端类型的筛选，以及由此得到的 $P-j$ 与二幂松弛阶梯。它不新增一般商集原理，不把有限枚举当作全参数证明，也不主张上述闭式已获文献原创核查或 Lean 核验。结论仍限于二幂来源、无噪声高位读取、已知初始高位、饱和查询预算和末次查询时刻；报告延迟、未知参考与有误差时钟须另立实际接口。

## 追加锚（本行以下为增补区）

## 10. 随机隐藏调度中的目标信息与时钟随机性

Claim status: open。第9节计数的是零错误统一解码所需的实际标签。本节为同一个末次查询接口指定联合概率律，计算隐藏调度究竟使相位记录漏掉多少目标信息。随机等待可以增大时钟记录自身的熵，却不增加它关于来源的互信息；共同截止又给这种损失一个可达到的精确界。

### 10.1 来源独立的私有种子与因果时间表

固定 $j\ge1$、$P=2^j$、$n=P/2$ 及共享的初始高位 $b$，所有信息量以 bit 计。令来源 $R$ 在 $\{0,\ldots,P-1\}$ 上均匀，并写

$$
R=2T+U,\qquad
T\sim\operatorname{Unif}\{0,\ldots,n-1\},\quad
U\sim\operatorname{Bernoulli}(1/2),\quad T\perp U.
\tag{TM.1001}
$$

控制器另有取值有限的私有随机种子 $Z$，要求 $Z\perp R$。每个正概率种子值确定一份第9节的因果成功调度；接收端知道这份随机机制及其分布，但不知道实际 $Z$。固定种子后，末次查询之前仍不能区分同一前缀中的两个 $U$，所以完成时间具有

$$
N=E_T+PK,\qquad K=k(T,Z)\in\mathbb N_0,
\qquad E_t=P-1+P\,\operatorname{wt}(t)-2t.
\tag{TM.1002}
$$

种子可以预先取得，也可由来源独立的内部随机机制供给；没有以额外来源证据预选策略。$N$ 仍是实际末次查询时刻，不能在看到 $U$ 后利用报告延迟重写这个变量。

记

$$
S=N\bmod P=P-1-2T,\qquad
Q=\lfloor N/P\rfloor\bmod2,\qquad
Y=(b+Q+U)\bmod2.
\tag{TM.1003}
$$

接收端取得全时刻 $(N,Y)$ 或只有相位的 $(S,Y)$ 是两种不同的访问合同。$Y$ 始终是未校正的原始末读。

### 10.2 随机等待熵与来源互信息的精确分离

**命题 10.1（隐藏周期奇偶造成的条件信息损失）。** 在 (TM.1001)—(TM.1003) 的同一联合律下，

$$
\begin{aligned}
H(N)&=j-1+H(K\mid T),&
I(R;N)&=j-1,\\
I(R;N,Y)&=j,&
I(R;S,Y)&=j-H(Q\mid T),\\
I(R;Y)&=1-H(Q\mid T),&
I(S;Y)&=0.
\end{aligned}
\tag{TM.1004}
$$

证明。$N$ 的模 $P$ 相位恢复 $T$，进而由 $(N-E_T)/P$ 恢复 $K$；反向 $(T,K)$ 决定 $N$。故 $N$ 与 $(T,K)$ 在实际像上双射，得
$H(N)=H(T)+H(K\mid T)=j-1+H(K\mid T)$。
由于 $Z$ 独立于 $(T,U)$，而 $K$ 由 $(T,Z)$ 决定，给定 $T$ 后 $K$ 与 $U$ 独立。因此
$I(R;N)=I(T,U;T,K)=H(T)=j-1$。

给定 $(T,Q)$，$U$ 仍是公平位，故 $Y$ 是公平位且与 $(T,Q)$ 独立。于是 $H(Y)=1$，$Y$ 与 $S$ 独立，给出最后一项。给定 $R=(T,U)$ 后，$Y$ 与 $Q$ 只是已知位的翻转，所以
$H(Y\mid R)=H(Q\mid T)$，从而 $I(R;Y)=1-H(Q\mid T)$。
同样，$Y$ 不改变给定 $T$ 后的 $Q$ 分布；固定 $(T,Y)$ 时又由 $U=Y-b-Q\bmod2$ 双射恢复 $U$ 与 $Q$。因而

$$
H(R\mid S,Y)=H(U\mid T,Y)=H(Q\mid T),
\tag{TM.1005}
$$

给出相位记录的等式。最后，精确 $N$ 自身给出 $T,Q$，与 $Y$ 联合便恢复 $U$，所以 $H(R\mid N,Y)=0$，全时刻记录的目标信息为 $H(R)=j$。$\square$

第7.4节的固定确定性调度对应 $H(K\mid T)=H(Q\mid T)=0$，因此与本式相容。随机种子造成的额外时钟熵 $H(K\mid T)$ 不属于新增来源信息。它也不全是解码损失：若最早协议在末次查询前以公平种子选择多等零个或两个 $P$ 周期，则 $K\in\{0,2\}$，有 $H(K\mid T)=1$ 而 $H(Q\mid T)=0$。此时 $H(N)$ 增加一位，相位与原始末读仍完整恢复 $R$。若允许的截止不足以容纳该延迟，这个例子当然不属于该截止族。

### 10.3 共同截止下可丢失多少平均目标信息

继续取 $W=(j-1)P+1$、整数 $h\ge0$、$D=W+h$。现在要求每个正概率种子确定的整份协议都对全部来源成功，且最坏末次查询时刻不超过 $D$。因此每个前缀仍服从第9.2节的实际可达时间限制。令

$$
q(h)=\#\{i\in\{1,\ldots,j\}:2^i\le h\}.
\tag{TM.1006}
$$

本节的极值允许选择任意来源独立的有限私有种子及其分布；若随机源的分布被另行固定，则下面的界仍成立，但公平混合的达到构造不一定可用。

**定理 10.2（截止族的锐平均信息下界）。** 在以上所有合规随机调度中，

$$
\boxed{
\min I(R;S,Y)
=j-1+\frac{j-q(h)}{n}.
}
\tag{TM.1007}
$$

等价地，最多漏掉的目标信息为

$$
\max H(R\mid S,Y)
=\max H(Q\mid T)
=\frac{n-j+q(h)}n
=\frac{M(\mathcal F_D)-n}{n}.
\tag{TM.1008}
$$

证明。定理9.2表明，截止族有 $j-q(h)$ 个前缀只能产生一个周期奇偶，有 $n-j+q(h)$ 个前缀能产生两种奇偶。前一类的条件熵 $H(Q\mid T=t)$ 必为零，后一类至多为一。$T$ 均匀，所以取平均给出 (TM.1008) 的上界；再用命题10.1即得 (TM.1007) 的下界。

达到界只需一个独立公平位 $Z$。$Z=0$ 选择全部最早查询；$Z=1$ 选择另一份固定策略：恰在满足 $E_t+P\le D$ 的前缀上，于最后读取之前多等一个 $P$ 周期，其他前缀不延迟。前 $j-1$ 次读取已经确定 $t$，所以第二策略因果可实现；两份策略各自对全部来源成功且均符合截止。每个双奇偶前缀的 $Q$ 此时公平，每个单奇偶前缀的 $Q$ 仍确定，因此同时达到所有条件熵界。无需假设不同未发生分支上的独立种子共同被实际读取。$\square$

在最优截止 $h=0$ 下，接收端只有相位和原始末读时，最小目标信息为 $j-1+j/n$；若 $h\ge P$，全部前缀都能翻转周期奇偶，最小值降为 $j-1$。$j=1,2$ 在最优截止下都无周期奇偶歧义，仍分别保留完整一位、两位目标信息。这些结论量化随机机制的共同实际联合律；不同协议分别达到的统计量没有被拼成一个不可能的来源。

### 10.4 三位来源中的四分之一位损失

取 $j=3$、$P=8$、$n=4$、$b=0$、最优截止 $D=17$。最早时刻为 $(7,13,11,17)$，只有前缀 $t=0$ 允许再等一个 $P$ 周期。用定理10.2的公平混合时，$t=0$ 的时刻在七与十五之间等概率选择，其他三前缀不变。因此

$$
H(K\mid T)=H(Q\mid T)=\frac14,
\qquad
H(N)=\frac94,\qquad I(R;N)=2,
\tag{TM.1009}
$$

而

$$
I(R;Y)=\frac34,\qquad
I(R;S,Y)=\frac{11}4,\qquad
I(R;N,Y)=3.
\tag{TM.1010}
$$

相位与末读仍独立，且 $(S,Y)$ 均匀占据八种记录，所以 $H(S,Y)=3$；然而其中关于来源的互信息只有 $11/4$。区别正出现在 $t=0$：相同相位与原始末读可以由两个来源经不同私有种子产生；其余三前缀能完整解码。这是记录自身的熵、目标互信息和零错误可恢复性在同一个有限来源上的明确分离。

还可以直接计算恢复错误，而不以互信息代替成功率。对一份固定合规随机机制，令 $p_t=\Pr(Q=1\mid T=t)$，并令 $e^*$ 为只用 $(S,Y,b)$ 的解码器中最小平均错误概率。观察到 $S$ 后 $T$ 已知，公平 $U$ 又使 $Y$ 不改变该前缀上的 $Q$ 分布；所以最优解码只需选择两种周期奇偶中条件概率较大者，得到

$$
e^*=\frac1n\sum_{t=0}^{n-1}\min\{p_t,1-p_t\},
\qquad
\max_{\text{截止 }D\text{ 合规随机机制}}e^*
=\frac{n-j+q(h)}{2n}.
\tag{TM.1011}
$$

第二式在单奇偶前缀贡献零、双奇偶前缀贡献至多二分之一，并由同一公平双策略混合达到。其量词是先为每份已知机制选择最优解码器，再比较各机制的最小错误率；没有交换为未知概率律下的另一种对抗问题。当前三位例子的最大 $e^*$ 为 $1/8$，保留 $(N,Y)$ 时则为零。

来源独立条件也有最小反例。取 $j=1,P=2,b=0,D=3$（即 $h=2$），令相关种子 $Z=R=U$，并以 $K=Z$ 选择末读时刻 $N=1+2Z$。固定每个种子的调度仍然因果且对全部来源成功，但实际联合律已在开始时把来源位放进种子。此时 $I(R;N)=1$，不再等于 $j-1=0$；$S=1$ 且 $Y=0$ 恒定。它说明外部计算不能把与来源相关的参考位当作免费独立随机性。

第9节在全部最优隐藏调度上得到五个时钟标签的零错误下界，本节同一截止上的最坏平均损失则只有四分之一位。前者要求每个允许来源和策略都正确，后者按明确均匀来源与随机种子求平均，不能用其中一个数替代另一个。这个桥梁也解释了为什么单独增加观察者记录的随机性不足以增加任务能力：需要保留的是与末读共同恢复来源的周期参考。

本节使用 Shannon 熵和互信息的标准链式法则，新增的模型推导是这些法则与主动进位时序、截止可达奇偶及其达到策略的结合。有限概率计算可核对实例，通用结论由上述条件独立与构造给出；没有新增 Lean、消化结算或文献原创性主张。非均匀来源、与来源相关的种子、噪声末读以及随机失败协议不属于当前假设。

## 追加锚（本行以下为增补区）

## 11. 共同截止与圆周误差下的因果补充记忆

### 11.1 全截止调度族与末读之前的可用类型

**定义 11.1（来源、终端接口与统一字母表）。** 沿用第7—10节的同一主动进位实验。固定 $j\ge2$，令 $P=2^j$、$n=P/2$，已知初始高位 $b\in\{0,1\}$，待恢复余数为 $R=2t+u$，其中 $0\le t<n$、$u\in\{0,1\}$。协议对全部 $P$ 个来源成功，使用恰好 $j$ 次额外的因果、无噪声、不扰动的二元高位查询，状态仅向前加一，查询之间可依旧记录等待有限步；$N$ 是末次实际查询的时刻，不包含读后报告延迟。取整数 $h\ge0$ 及共同截止

$$
E_t=P-1+P\operatorname{wt}(t)-2t,\qquad
W=(j-1)P+1,\qquad D=W+h.
\tag{TM.1101}
$$

$\mathcal F_D$ 是满足 $\max_tN_\pi(t)\le D$ 的**全部**确定性成功调度，而不是预先选定的一份协议。第9.2节给出 $N_\pi(t)=E_t+PK_\pi(t)$，$K_\pi(t)\in\mathbb N_0$；任何这样的非负表都能在先取得 $t$ 后、只推迟末次查询而实现。末次查询以前的 $j-1$ 个读数已经确定 $t$，同一前缀的两个来源尚不可分辨；采集端还须实际掌握计划时刻 $N_\pi(t)$ 的周期奇偶

$$
\nu=\left\lfloor N_\pi(t)/P\right\rfloor\bmod2,
\qquad S_t=P-1-2t\pmod P,
\qquad Y=(b+\nu+u)\bmod2.
\tag{TM.1102}
$$

接收端得到圆周 $\mathbb R/P\mathbb Z$ 上的 $\widehat S$、精确且未经校正的原始末读 $Y$，以及一个补充标签 $\lambda$；共享参数为 $j,b,D,\varepsilon$，其中 $\varepsilon\ge0$，误差满足闭界 $d_P(\widehat S,S_t)\le\varepsilon$。它不接收实际调度、旧读数或精确 $N$。标签必须在末次 $u$ 读出及未来相位误差发生之前选定，允许依赖实际调度、旧因果状态和已经取得的 $(t,\nu)$，不允许依赖 $u$ 或 $\widehat S$。一个共同解码器须对全部 $\pi\in\mathcal F_D$、全部来源、全部允许误差正确。

记这份合同的最小补充字母表大小为 $\Lambda_{j,h}(\varepsilon)$，计数取跨所有调度的同一个标签集。它不计时钟端口、采集控制器、取得 $t$ 的查询费用或解码计算，亦不以各调度分别选择的小字母表代替全局字母表。定长二进制表示的费用为 $\lceil\log_2\Lambda_{j,h}(\varepsilon)\rceil$。

**命题 11.2（可达类型的具体需求）。** 令

$$
B_D(t)=\{\lfloor N_\pi(t)/P\rfloor\bmod2:\pi\in\mathcal F_D\},
\quad k_t=|B_D(t)|,
\quad q(h)=\#\{1\le i\le j:2^i\le h\}.
\tag{TM.1103}
$$

则

$$
k_t=1+\mathbf1_{\{E_t+P\le D\}},\qquad
L:=\#\{t:k_t=1\}=j-q(h),\qquad
M:=\sum_tk_t=2n-L.
\tag{TM.1104}
$$

实际单需求前缀集恰为

$$
\mathcal S_h=
\{n-1:h<P\}\ \cup
\{n-1-2^r:0\le r\le j-2,\ h<2^{r+1}\}.
\tag{TM.1105}
$$

这里带条件的花括号在条件不成立时为空。若 $t\in\mathcal S_h$，唯一可达奇偶是 $\operatorname{wt}(t)\bmod2$；否则 $B_D(t)=\{0,1\}$。

证明。允许的 $K$ 恰为从零到 $\lfloor(D-E_t)/P\rfloor$ 的整数。当上端为零时只有最早奇偶；上端至少一时两种奇偶均出现。由

$$
E_t+P-W=(\operatorname{wt}(t)-j+3)P-2t-2
\tag{TM.1106}
$$

可知重量至多 $j-3$ 的前缀已经为双需求。其余是 $j-1$ 位中恰缺一个一的 $n-1-2^r$，以及全一前缀 $n-1$；它们取得第二种奇偶的松弛阈值分别为 $2^{r+1}$ 与 $P$。因此恰有（TM.1105）的单需求，阈值计数给出（TM.1104）。这些都是同一完整截止族的可实现类型：令指定前缀的最后等待增加一个周期、其余前缀保持最早时间，就实现了每个获准的第二奇偶。$\square$

### 11.2 从因果标签支持集到混淆图

**定理 11.3（隐藏调度与相位误差的精确类型图）。** 在顶点集

$$
V_D=\{(t,\nu):0\le t<n,\ \nu\in B_D(t)\}
\tag{TM.1107}
$$

上定义图 $H_{D,\varepsilon}$：同一 $t$ 的不同奇偶相邻；不同 $t,t'$ 的全部类型之间连边，当且仅当 $d_n(t,t')\le\varepsilon$。则

$$
\boxed{\Lambda_{j,h}(\varepsilon)=\chi(H_{D,\varepsilon}).}
\tag{TM.1108}
$$

即使标签允许区分同一类型背后的调度和旧因果状态，也不能低于此色数。

证明。记 $\mathcal B_t=\{s:d_P(s,S_t)\le\varepsilon\}$。第8.1节的圆周几何给出
$\mathcal B_t\cap\mathcal B_{t'}\ne\varnothing$ 当且仅当 $d_n(t,t')\le\varepsilon$。对任一可行编码，令 $A_{t,\nu}$ 是所有实现类型 $(t,\nu)$ 的调度与旧状态所可能发出的标签集合。这是非空集合；由于标签先于末读，改变同一前缀中的 $u$ 不改变相应标签。

若相邻的两个类型的支持集共享某个标签，则分别选取实现该标签的实际调度。不同前缀时取两相位球的一个交点，同一前缀时取共同中心作为 $\widehat S$；对每个类型都取 $u=(-b-\nu)\bmod2$。两份实际实现的末读均为 $Y=0$，收到的相位和标签也相同，而来源不同：不同 $t$ 对应不同二点纤维，同一 $t$ 的两个奇偶对应相反的 $u$。共同解码器因此矛盾。故相邻类型的标签支持集必须不交。从每个非空支持集各取一个标签，所得函数就是正常染色；全局标签数至少是色数。这里比较的是合同分别要求正确的两个实现，并未假设一条实际历史同时发生两种奇偶。

反过来，给定图的正常染色 $c$，采集端从已取得的 $(t,\nu)$ 发出 $c(t,\nu)$。对一个合规输入 $(\widehat S,Y,\lambda)$，至少存在一个真实类型满足 $\widehat S\in\mathcal B_t$ 且 $c(t,\nu)=\lambda$。若存在两个，它们或者是同一前缀的不同奇偶，或者相位球在 $\widehat S$ 处相交；两种情形都相邻，不应同色。因此类型唯一，再取

$$
u=(Y-b-\nu)\bmod2,\qquad R=2t+u
\tag{TM.1109}
$$

即完成统一恢复。$\square$

该证明中的有限图着色机制属于零错误旁信息问题的经典关系；文献对应为 H. S. Witsenhausen, *The zero-error side information problem and chromatic numbers (Corresp.)*, IEEE Transactions on Information Theory **22**(5), 592–593 (1976), [doi:10.1109/TIT.1976.1055607](https://doi.org/10.1109/TIT.1976.1055607)。此处使用的是上面已经逐方向证明的单次有限模型，不从该文献引出截止公式或下节的混合需求闭式。

仓内 `D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring.lean` 的 `minimum_repair_labels_eq_chromatic_eq_fiber_diversity` 所用边关系是“确定读出相等且目标不同”。本定理的边来自相位球交叠，标签又必须先于误差取得；交叠不具有传递性，因而不满足直接用一个确定观察纤维代替此图的条件。

**推论 11.4（有限独立种子的支持边界）。** 若再允许取值有限且独立于来源的私有种子，每个正概率种子固定一份对全部来源成功的截止调度，且要求对每个允许误差零错误，则最小字母表仍由这些调度支持所形成的同一类型图给出。随机化本身不能减少该支持图的色数；要求覆盖完整 $\mathcal F_D$ 时仍为（TM.1108）。

证明。来源独立使每个正概率种子下的两种 $u$ 都属于须正确的输入。将 $A_{t,\nu}$ 的定义再并入正概率种子值，上述相邻支持集不交的证明逐字成立。反向的类型染色根本不需要种子。若固定机制只支持 $\mathcal F_D$ 的真子族，应先按其实际支持重算 $B_D(t)$；不能把缩小调度族造成的降低归于随机编码。该结论只涉及有限种子和逐允许误差的零错误合同，不使用平均错误或无穷种子的几乎处处替代。$\square$

### 11.3 混合单双需求的锐循环染色

**定理 11.5（一般误差壳上的精确补充容量）。** 取整数 $m\ge2$，满足

$$
m-1\le\varepsilon<m,\qquad
j\ge3+\lfloor\log_2m\rfloor,\qquad
n=ma+\rho,\quad 0\le\rho<m,\quad a\ge2\rho.
\tag{TM.1110}
$$

其中 $m$ 仅表示误差壳参数。则完整截止族的最小补充字母表为

$$
\boxed{
\Lambda_{j,h}(\varepsilon)
=\max\left\{2m,\left\lceil\frac{2n-L}{a}\right\rceil\right\}
=2m+\mathbf1_{\{L<2\rho\}},\qquad L=j-q(h).
}
\tag{TM.1111}
$$

证明。整数距离使不同前缀的邻接条件恰为 $1\le d_n(t,t')\le m-1$。设 $f=\lfloor\log_2m\rfloor$，则 $n\ge4\cdot2^f>2m$。此外 $t<m<2^{f+1}$，这段整数中的二进制重量至多 $f$：若有 $f+1$ 个一，其最小值为 $2^{f+1}-1\ge m$。故 $t=0,\ldots,m-1$ 均满足 $\operatorname{wt}(t)\le j-3$，都是双需求。它们在图中给出一个 $K_{2m}$，于是 $\Lambda\ge2m$。

同一颜色在每个前缀至多出现一次，且它所占据的不同前缀循环距离至少 $m$。将这些前缀循环排序，全部相邻间隙之和为 $n$、每个至少 $m$，所以同一颜色至多占据 $a=\lfloor n/m\rfloor$ 个类型；只有一个前缀的情形也满足此界。共有 $M=2n-L$ 个类型，故 $\Lambda\ge\lceil M/a\rceil$。两项下界均在同一图上成立。

为给达到构造，先证明所需的循环槽块事实。按 $t=0,\ldots,n-1$ 排列整数长度为 $\ell_t\ge k_t$ 的连续槽块，把全部槽依次按模 $c$ 着色。若总槽数 $T=\sum_t\ell_t$ 被 $c$ 整除，且任意循环连续 $m$ 个槽块的长度之和至多 $c$，则从每块任选 $k_t$ 个不同槽作为该前缀的颜色，得到正常染色。事实上，同一块的已选槽和任意相邻前缀的已选槽均落在某个连续 $m$ 块窗口内；窗口至多含 $c$ 个连续槽，其中模 $c$ 的颜色两两不同。跨过 $n-1$ 与零的窗口也如此：因 $T\equiv0\pmod c$，把槽序列周期延长后，跨缝颜色正好延续原模 $c$ 顺序。这同时处理块内两奇偶和圆周首尾边，不能只检查不回绕的窗口。

若 $L\ge2\rho$，从实际单需求集 $\mathcal S_h$ 中选择任意 $2\rho$ 个前缀组成 $J$，令这些块的长度为一，其余块长度为二。所需类型均放得下；没有选入 $J$ 的单需求块可有一个未使用槽。总长度为 $2n-2\rho=2ma$，被 $2m$ 整除；任意 $m$ 块长度至多 $2m$。上述槽块事实给出 $2m$ 色构造，与团下界相等。

若 $L<2\rho$，取

$$
c=2m+1,\qquad
z=(-2n)\bmod c=(a-2\rho)\bmod c,
\quad 0\le z<c.
\tag{TM.1112}
$$

因为 $a\ge2\rho$，有 $z\le a-2\rho\le a$。每个前缀先放两个槽，再在位置 $0,m,\ldots,(z-1)m$ 的块末各放一个未使用的附加槽；$z=0$ 时不放。所选位置的循环间隔至少 $m$：内部间隔恰为 $m$，跨缝间隔为 $n-(z-1)m\ge m+\rho$。所以任何 $m$ 块窗口至多含一个附加槽，长度至多 $2m+1=c$。总槽数为 $2n+z$，按定义被 $c$ 整除，槽块构造给 $2m+1$ 色。另一方面

$$
2n-L=2ma+(2\rho-L),\qquad 1\le2\rho-L\le a,
\tag{TM.1113}
$$

故容量下界恰为 $2m+1$。当 $L\ge2\rho$ 时容量下界至多 $2m$；两种情形合起来即（TM.1111）。$\square$

均匀需求的对应先例是 Campêlo、Corrêa、Moura、Santos, *On optimal k-fold colorings of webs and antiwebs*, Discrete Applied Mathematics **161**(1–2), 60–70 (2013), [doi:10.1016/j.dam.2012.07.013](https://doi.org/10.1016/j.dam.2012.07.013)，预印本 [arXiv:1108.5757v1](https://arxiv.org/abs/1108.5757v1)。按其第2页约定，$W_m^n$ 的边满足 $m\le|t-t'|\le n-m$；在 $n\ge2m$ 时，其补图 antiweb 正是这里的前缀图 $C_n^{m-1}$。该文第8页定理2给均匀 $k$ 重需求的色数 $\lceil kn/\lfloor n/m\rfloor\rceil$。取 $k=2$ 即为全部双需求时的 $\lceil2n/a\rceil$。本定理对截止产生的单、双混合需求另给下界和达到证明，未将混合需求公式归给该均匀定理。

### 11.4 不依赖未来读数的编码与局部枚举解码

**命题 11.6（槽起点形式的共同编码）。** 在定理11.5的条件下，定义类型在自身块中的序号

$$
\sigma(t,\nu)=
\begin{cases}
\nu,&k_t=2,\\
0,&k_t=1.
\end{cases}
\tag{TM.1114}
$$

单需求的唯一奇偶即使为一，也必须占第零槽；这里用的是实际类型序号，不是无条件把奇偶当作槽号。低容量情形 $L\ge2\rho$ 中，令 $J$ 为（TM.1105）按数值递增排序后的前 $2\rho$ 项，取

$$
I(t)=2t-\#\{s\in J:s<t\},\qquad
\lambda(t,\nu)=(I(t)+\sigma(t,\nu))\bmod 2m.
\tag{TM.1115}
$$

高容量情形 $L<2\rho$ 中，按（TM.1112）选 $c,z$，取

$$
I(t)=2t+\min\{z,\lceil t/m\rceil\},\qquad
\lambda(t,\nu)=(I(t)+\sigma(t,\nu))\bmod c.
\tag{TM.1116}
$$

这些编码分别达到（TM.1111）的最优字母表；双方只需共享公式和参数，无需让接收端取得实际调度。

证明。低容量时 $t$ 以前的每个块贡献两个槽，$J$ 中每个较早前缀恰减少一个，故（TM.1115）的 $I(t)$ 正是块起点。高容量时，较早的附加槽位置满足 $rm<t$、$0\le r<z$，其个数恰为 $\min\{z,\lceil t/m\rceil\}$，故（TM.1116）也是块起点。这包括 $t=0$ 时计数为零以及 $t=n$ 时全部 $z$ 个附加槽已经计入的两端。每块前 $k_t$ 个槽按（TM.1114）分配，正好得到定理11.5证明中的染色。$J$ 可从至多 $j$ 项的实际单需求列表生成，未要求先枚举 $n$ 个前缀；这只是编码表达式的描述，不是控制器空间或运行时间的最优性结论。$\square$

**命题 11.7（有限候选的显式解码）。** 取 $\widehat S$ 的代表元 $s\in[0,P)$，令

$$
\theta=\frac{P-1-s}{2},\qquad
\mathcal V(s)=\left\{v\in\mathbb Z:
\left\lceil\theta-\frac\varepsilon2\right\rceil
\le v\le
\left\lfloor\theta+\frac\varepsilon2\right\rfloor
\right\}.
\tag{TM.1117}
$$

把每个 $v$ 化为 $t=v\bmod n$，枚举 $\nu\in B_D(t)$，按（TM.1115）或（TM.1116）计算标签。对合规输入恰有一个类型与收到的 $\lambda$ 相符，用（TM.1109）恢复来源。至多枚举 $m$ 个前缀及 $2m$ 个类型。

证明。条件 $d_P(s,P-1-2t)\le\varepsilon$ 等价于存在与 $t$ 模 $n$ 同余的整数 $v$ 满足 $|v-\theta|\le\varepsilon/2$，因此（TM.1117）列出全部且仅列出相位兼容前缀。闭区间的长度为 $\varepsilon<m$，其中整数至多有 $m$ 个；因 $n>2m$，这些整数不会给出重复模 $n$ 前缀。类型染色保证至多一个匹配标签，真实实现保证至少一个，再由原始末读还原 $u$。$\square$

这个枚举式的数学定义使用精确比较。若把它读成有限计算程序，输入须支持所需的精确取整和闭端点比较，例如给定有理 $s,\varepsilon$ 的精确表示；任意可计算实数的近似描述并不自动允许判断端点等号。枚举至多 $2m$ 个类型不等于总位复杂度或时间复杂度已被界定。采集端先取得 $t$、实际计划并掌握 $\nu$，以及接收端取得有指定精度的相位端口，仍是恢复的实际条件。

### 11.5 截止阈值、局部候选数与定长位数

**推论 11.8（共同截止的唯一容量跳点）。** 在定理11.5的参数范围中，若 $\rho=0$，全部 $h\ge0$ 均有 $\Lambda=2m$。若 $\rho>0$ 且 $j<2\rho$，全部 $h\ge0$ 均有 $\Lambda=2m+1$。若 $\rho>0$ 且 $j\ge2\rho$，则

$$
\Lambda_{j,h}(\varepsilon)=
\begin{cases}
2m,&0\le h<2^{j-2\rho+1},\\
2m+1,&h\ge2^{j-2\rho+1}.
\end{cases}
\tag{TM.1118}
$$

一个保证（TM.1110）中规模条件成立的充分界为

$$
j\ge J(m):=\max\left\{
3+\lfloor\log_2m\rfloor,
1+\left\lceil\log_2(2m(m-1))\right\rceil
\right\}.
\tag{TM.1119}
$$

对固定非二幂 $m$，若进一步 $j\ge2(m-1)$，随截止松弛变化的两个容量水平都出现。

证明。由 $L=j-q(h)$ 单调下降，条件 $L<2\rho$ 等价于 $q(h)\ge j-2\rho+1$。正阈值计数 $q$ 依次在 $2^1,\ldots,2^j$ 增加；若 $1\le j-2\rho+1\le j$，首个满足值就是（TM.1118）的跳点。其余两种情形直接来自 $0\le L\le j$。式（TM.1119）使 $n=2^{j-1}\ge2m(m-1)$，故 $a\ge2(m-1)\ge2\rho$。非二幂 $m$ 不整除二幂 $n$，所以 $\rho>0$；而 $j\ge2(m-1)\ge2\rho$ 保证起始为低容量、到达所示松弛后为高容量。$\square$

**命题 11.9（单次未标记上下文恰有 $2m$ 个最大候选来源）。** 在定理11.5的合同中，对不含补充标签的一个固定上下文 $(\widehat S,Y,b)$，把能够经某份合规隐藏调度产生该上下文的来源组成集合。其大小的最大值恰为 $2m$。因此 $L<2\rho$ 时，局部候选最大值严格小于全局必需字母表 $2m+1$。

证明。由（TM.1117），相位兼容的前缀至多 $m$ 个；每个前缀至多有两个奇偶，而固定 $Y,b,\nu$ 后只有一个 $u$，所以来源数至多 $2m$。另一方面前 $m$ 个前缀全为双需求。它们的相位取代表元 $P-1,P-3,\ldots,P-1-2(m-1)$，共享中点 $\widehat S=P-m$，到该中点的距离均至多 $m-1\le\varepsilon$。固定任意 $Y$，每个前缀的两种可达奇偶给出两个不同来源，合计 $2m$。这些来源分别具有合法实现，故最大值达到。

不同上下文各自给候选编号，并不保证这些编号来自同一个先于误差选择的标签函数。定理11.3的支持集条件恰要求跨所有上下文相容；当（TM.1111）给出多一个标签时，障碍是此相容性。$\square$

**命题 11.10（字母表跳变与最优定长位数）。** 定理11.5的最优补充定长位数恒为

$$
\left\lceil\log_2\Lambda_{j,h}(\varepsilon)\right\rceil
=1+\lceil\log_2m\rceil.
\tag{TM.1120}
$$

还有一个直接达到此位数的编码：令 $Q=2^{\lceil\log_2m\rceil}$，发送 $(t\bmod Q,\nu)$，使用至多 $2Q$ 个标签。

证明。$K_{2m}$ 给出至少 $\lceil\log_2(2m)\rceil=1+\lceil\log_2m\rceil$ 位的下界。若最优字母表为 $2m$，它已经达到。若为 $2m+1$，则 $\rho>0$；二幂 $m$ 本应整除 $n$，所以此时 $m$ 非二幂。$2m$ 与其上方最近二幂都是偶数，且不相等，故二者相差至少二，$2m+1$ 尚未超过该二幂。因此两种容量有相同的上取整对数。

对给出的替代编码，规模条件保证 $Q\mid n$ 且 $Q\ge m$。同余模 $Q$ 的不同前缀，其循环距离至少 $Q$，不能相邻；同一前缀的不同奇偶被第二分量分开。因此这也是正常染色，用 $\log_2(2Q)=1+\lceil\log_2m\rceil$ 位达到下界。它优化定长二进制费用，未必优化非二幂标签字母表的基数。$\square$

### 11.6 五前缀误差壳中的十与十一

**命题 11.11（同一模型中的局部十候选与全局十一标签）。** 取 $m=5$、$4\le\varepsilon<5$、$j=7$、$h=0$，则 $n=64=5\cdot12+4$，实际单需求集为

$$
\mathcal S_0=\{31,47,55,59,61,62,63\},\qquad
L=7,\qquad M=121.
\tag{TM.1121}
$$

最小全局字母表为十一，而每个未标记接收上下文至多有十个候选来源，且此局部上界可达到。十一标签的显式编码可取

$$
z=4,\qquad I(t)=2t+\min\{4,\lceil t/5\rceil\},\qquad
\lambda=(I(t)+\sigma(t,\nu))\bmod11.
\tag{TM.1122}
$$

证明。式（TM.1105）给出所列七个单需求；一色至多覆盖十二个类型，十色只能覆盖一百二十个，容纳不了 $121$。高容量构造在块 $0,5,10,15$ 各放一个附加槽，总计 $128+4=132$ 槽，以十一色循环分配，达到下界。局部十候选由命题11.9给出；例如 $\widehat S=123$ 同时兼容前五个双需求前缀。

再给一个具体恢复。令 $b=0$、$\varepsilon=9/2$、真实来源 $R=63$，即 $t=31,u=1$。其最早末读时间为 $E_{31}=705\le W=769$，且 $E_{31}+128>769$，所以唯一奇偶是 $\nu=1$。于是 $S_{31}=65$、$Y=0$，块序号须用 $\sigma=0$，由（TM.1122）得 $\lambda=66\bmod11=0$。若收到 $\widehat S=67$，误差为二，满足合同。解码式给 $\theta=30$、前缀候选 $28,29,30,31,32$，其可用标签依次为

$$
\{5,6\},\quad\{7,8\},\quad\{9,10\},\quad\{0\},\quad\{2,3\}.
\tag{TM.1123}
$$

因此唯一匹配为 $(31,1)$，继而 $u=(0-0-1)\bmod2=1$，恢复 $R=63$。单需求若误把原始奇偶一用作槽号，这个编码就不再是所证明的构造。$\square$

**命题 11.12（改变来源规模时的容量序列）。** 保持 $m=5$、$h=0$，在下列四个模型中有：

| 参数 $j$ | 前缀数 $n$ | 商余 $(a,\rho)$ | 单需求数 $L$ | 最小补充标签数 |
| --- | --- | --- | --- | --- |
| $5$ | $16$ | $(3,1)$ | $5$ | $10$ |
| $6$ | $32$ | $(6,2)$ | $6$ | $10$ |
| $7$ | $64$ | $(12,4)$ | $7$ | $11$ |
| $8$ | $128$ | $(25,3)$ | $8$ | $10$ |

证明。四行均满足 $j\ge5$ 和 $a\ge2\rho$，逐行比较 $L$ 与 $2\rho$，由（TM.1111）即得 $10,10,11,10$。各行的来源集合大小 $P=2n$ 不同，因而这不是固定来源上放宽截止或误差使容量下降的反例。同一 $j,m$ 下随 $h$ 增加，需求只增加，色数不会减少。十与十一都需要四位定长二进制补充存储，也不构成定长位数的跳变。$\square$

### 11.7 小误差的完整区间与两个必要条件反例

**定理 11.13（$j\ge4$、$0\le\varepsilon<4$ 的精确值）。** 对完整截止族，

$$
\Lambda_{j,h}(\varepsilon)=
\begin{cases}
2,&0\le\varepsilon<1,\\
4,&1\le\varepsilon<2,\\
\displaystyle\max\left\{6,\left\lceil\frac{2n-L}{\lfloor n/3\rfloor}\right\rceil\right\},
&2\le\varepsilon<3,\\
7+\mathbf1_{\{h\ge8\}},&3\le\varepsilon<4,\ j=4,\\
8,&3\le\varepsilon<4,\ j\ge5.
\end{cases}
\tag{TM.1124}
$$

其中 $L=j-q(h)$。在第三行，$j=4$ 的具体截止分段为

$$
\Lambda_{4,h}(\varepsilon)=
\begin{cases}
6,&0\le h<2,\\
7,&2\le h<8,\\
8,&h\ge8,
\end{cases}
\qquad 2\le\varepsilon<3.
\tag{TM.1125}
$$

对于奇数 $j\ge5$，同一误差区间在 $h=P/2$ 从六跳到七；对于偶数 $j\ge6$，在 $h=P/8$ 从六跳到七。特别地，最紧截止 $h=0$ 时，$2\le\varepsilon<3$ 总是恰需六标签。

证明。若 $\varepsilon<1$，不同前缀不相邻，只剩各自的奇偶团；$j\ge4$ 时前缀零为双需求，所以两色必要且充分。若 $1\le\varepsilon<2$，取定理11.5中的 $m=2$；$n$ 被二整除，得到四。

若 $2\le\varepsilon<3$ 且 $j\ge5$，取 $m=3$。此时 $n\ge16$、$a\ge5$、$2\rho\le4$，主定理适用。由于 $2^{j-1}$ 模三在 $j$ 为奇数时等于一、偶数时等于二，阈值（TM.1118）分别成为 $2^{j-1}=P/2$ 和 $2^{j-3}=P/8$。

剩下 $j=4,n=8,m=3$ 须单独构造。图中每色至多占据两个类型，前三个双需求前缀又给出六点团，故下界是 $\max\{6,\lceil(16-L)/2\rceil\}$。当 $h<2$ 时，需求依次为

$$
(k_0,\ldots,k_7)=(2,2,2,1,2,1,1,1).
\tag{TM.1126}
$$

依需求分配十二个连续槽，模六着色；任意三个循环连续块至多六槽，且总长十二被六整除，故第11.3节的槽块论证适用。具体八个调色集依次为

$$
\{0,1\},\ \{2,3\},\ \{4,5\},\ \{0\},
\{1,2\},\ \{3\},\ \{4\},\ \{5\}.
\tag{TM.1127}
$$

当 $2\le h<4$ 时单需求集为 $\{3,5,7\}$，当 $4\le h<8$ 时为 $\{3,7\}$。两种情形都令块三、七长一，其他块长二，总长十四，模七着色；任意三个循环连续块至多六槽，不超过七。这容纳全部实际需求，结合 $L=3$ 或二的容量下界，恰为七。当 $h\ge8$ 时 $L\le1$，容量下界为八；令所有块长二，总长十六，模八着色即可，所有三块窗口仍至多六槽。因此三种构造分别使用十二、十四、十六槽，且都包含回绕窗口验证，证明（TM.1125）。

最后，$3\le\varepsilon<4$ 且 $j\ge5$ 时取 $m=4$，主定理直接给八。若 $j=4$，前缀图 $C_8^3$ 的不同顶点只有反足对 $(t,t+4)$ 不相邻。一个颜色只能在同一反足对内共享，所以

$$
\chi(H_{D,\varepsilon})=\sum_{t=0}^3\max\{k_t,k_{t+4}\}.
\tag{TM.1128}
$$

下界来自不同反足对之间全相邻；上界是给每个反足对分配互不相交的调色集，将其中大小为 $k_t$、$k_{t+4}$ 的两个子集分配给两端。前三对总贡献六；第四对 $(3,7)$ 在 $h<8$ 时贡献一，在 $h\ge8$ 时贡献二。得到（TM.1124）的最后两行。$\square$

**命题 11.14（主闭式的两个条件不能删去）。** 在 $m=4,j=4,h=0$ 时，$a=2,\rho=0$ 满足余数条件，但最小字母表为七，小于形式代入（TM.1111）所得的八；这里违反的是 $j\ge3+\lfloor\log_2m\rfloor$。在 $m=3,j=4,h\ge8$ 时，规模条件成立，但最小字母表为八，大于形式代入最后一个两水平表达式所得的七；这里 $a=2<2\rho=4$。

证明。第一个值由（TM.1128）在需求（TM.1126）下计算为 $2+2+2+1=7$，前四个前缀并非全部双需求，所以八点团下界不成立。第二个值由（TM.1125）给出；共有至少十五个类型、每色至多承载两个，直接迫使八色。此时 $2\rho-L$ 可大于 $a$，故（TM.1113）中将容量上取整限制为只多一色的步骤失效。两例均不否定适用于这些参数的精确类型图等式（TM.1108）。$\square$

**命题 11.15（误差四的端点）。** $j=4,h=0,\varepsilon=4$ 时恰需十二标签；$j\ge5,\varepsilon=4$ 时对任意 $h\ge0$ 至少需十标签。因此（TM.1124）不能延伸到闭端点四。

证明。第一种情形中八个前缀全部相邻，图成为十二类型的完全图。第二种情形中前五个前缀的重量至多二，不超过 $j-3$，故都是双需求；它们两两循环距离至多四，十个类型构成完全子图。由定理11.3得到所述界。$\square$

## 追加锚（本行以下为增补区）

## 12. 四重表示的动态关系图册

前面的章节分别讨论了端口运输、任务记忆、切面动态规划和完成化。
本节把它们收束成一个有限经典的判据：空间、时间、边界和记忆只有在
它们保留同一个未来行为商时，才是同一关系过程的不同表示。

### 12.1 实际联合来源与未来行为商

固定一个有限的实际联合来源 $Z$。它的一个元素已经包含本次任务会影响
未来的对象状态、参考、权限、工作记忆和已保留档案；没有列入 $Z$ 的变量
不能在后续核或选择器中偷偷使用。固定有限动作集 $\mathcal A$。对每个
$a\in\mathcal A$，给出合法性指标 $L_a:Z\to\{0,1\}$、有限事件集 $E_a$、
有限记录集 $R_a$，以及仅在 $D_a=\{z:L_a(z)=1\}$ 上归一化的联合核

$$
J_a(z;\eta,z',r)\ge0,\qquad
\sum_{\eta\in E_a,\;z'\in Z,\;r\in R_a}J_a(z;\eta,z',r)=1
\quad(z\in D_a).
\tag{TM.1201}
$$

记录 $r$ 可以包含可见事件、实际时钟增量和 writer 输出；若某一项会影响
后续选择或合法性，它必须进入 $Z$ 或 $r$。不合法动作使用与合法事件分离的
拒绝符号和固定拒绝记录，不能把未定义的非法核行当作零概率合法事件。

令 $\mathscr T$ 是声明过的有限自适应测试族：测试可以读取零步类型，选择
合同内动作，观察事件、后继摘要和记录，并根据已见前缀继续。测试族对合法的
前后接续封闭。记 $\mathsf B_z(T)$ 为从 $z$ 开始执行 $T$ 所得的完整有限
转录分布，定义

$$
z\sim_{\mathscr T}u
\iff
\forall T\in\mathscr T,\quad
\mathsf B_z(T)=\mathsf B_u(T).
\tag{TM.1202}
$$

令 $Q=Z/{\sim_{\mathscr T}}$，并把商映射记为 $q:Z\twoheadrightarrow Q$。
这里使用实际像 $Q=q[Z]$；不会给未被实际来源取得的摘要值任意扩展行为。
按定义，$q$ 是当前测试任务下的最小动态边界：两个来源能被合并，当且仅当
全部声明的未来接续都无法区分它们。

### 12.2 四种表示的精确性

令

$$
I=\{\mathrm{space},\mathrm{time},\mathrm{boundary},\mathrm{memory}\},
\qquad r_i:Z\to Y_i\quad(i\in I),
$$

并把 $Y_i^0=r_i[Z]$ 限制为实际表示像。称 $r_i$ 对任务 $\mathscr T$
**动态充分**，如果存在边界上的合法性、联合核和选择器，使所有有限测试
转录都能只从 $r_i(z)$ 生成；称它**动态分离**，如果

$$
r_i(z)=r_i(u)\Longrightarrow z\sim_{\mathscr T}u.
\tag{TM.1203}
$$

若还要求表示不把行为等价的来源拆开，则完整精确性就是

$$
\ker r_i=\sim_{\mathscr T}.
\tag{TM.1204}
$$

式（TM.1204）比“当前数值相同”强：它包括零步类型、合法性、事件、后继、
writer 记录、时钟以及选择器在全部允许续接中的联合关系。

### 定理 12.1（四重动态图册的唯一运输）

假设四个表示 $r_i$ 都满足（TM.1204），并且各自的边界核由（TM.1201）
按后继纤维求和得到；外显 selector 使用无历史读取的版本，历史依赖 selector
则对每个可见前缀分别满足同样的因子化。则对任意 $i,j\in I$，存在唯一双射

$$
\chi_{ji}:Y_i^0\longrightarrow Y_j^0,\qquad
\chi_{ji}(r_i(z))=r_j(z).
\tag{TM.1205}
$$

这些运输满足

$$
\chi_{ki}\,=\,\chi_{kj}\circ\chi_{ji},
\qquad
\chi_{ii}=\operatorname{id},
\qquad
\chi_{ij}=\chi_{ji}^{-1}.
\tag{TM.1206}
$$

若 $K_a^i$ 是 $r_i$ 上的联合核，则在实际表示像上有交换关系

$$
K_a^j\bigl(\chi_{ji}(y);\eta,\chi_{ji}(y'),r\bigr)
=K_a^i(y;\eta,y',r),
\tag{TM.1207}
$$

并且合法性、时钟增量、writer 记录和外显动作分布都沿 $\chi_{ji}$ 保持。
因此四种表示给出相同的全部有限自适应转录律。

**证明。** 由（TM.1204），若 $r_i(z)=r_i(u)$，则 $q(z)=q(u)$；反向包含
也成立，所以 $r_i$ 在 $q$ 的每个纤维上恒定，并在实际像上诱导唯一映射
$\chi_i:Q\to Y_i^0$。同样，$q$ 在每个 $r_i$ 纤维上恒定，故 $\chi_i$ 为双射。
置 $\chi_{ji}=\chi_j\circ\chi_i^{-1}$，立即得到（TM.1205）—（TM.1206）。

边界核的定义是对同一个 $z$ 的 $r_i$ 后继纤维求和。把 $y=r_i(z)$、
$y'=r_i(z')$ 代入，并用 $r_j=\chi_{ji}\circ r_i$，两边的求和指标是同一个
$r_j$ 纤维，故得到（TM.1207）。合法性与记录是同一联合核的投影；selector
的因子化同理。最后按测试长度归纳：零步输出由（TM.1204）保留；假设已见前缀
相同，则动作分布相同，下一事件、后继表示和记录由（TM.1207）相同，故下一步
转录律相同。历史 selector 对每个共同前缀逐项使用同一论证。证毕。

反过来，若一个表示 $r$ 对全部 $\mathscr T$ 的转录律充分，则同一表示值生成
相同的全部声明转录律，因而 $\ker r\subseteq\sim_{\mathscr T}$。要得到
（TM.1204），还须要求行为等价的来源具有相同表示，即
$\sim_{\mathscr T}\subseteq\ker r$；两项合起来才给核相等。所以“互相可恢复”
要求各表示保留同一行为商，而不是四个当前读数之间存在某个事后函数。

### 12.3 有限确定更新的联合细化

上面的核条件在确定性有限模型中有一个直接的稳定算法。令 $F_a:Z\to Z$
为每个动作的总更新，令 $\ell_a:Z\to L_a$ 把合法性、事件、记录、时钟和失败原因
合并为一个可见标签。四种当前表示的联合读出为

$$
J(z)=\bigl(r_{\mathrm{space}}(z),r_{\mathrm{time}}(z),
r_{\mathrm{boundary}}(z),r_{\mathrm{memory}}(z)\bigr).
$$

定义递减关系链

$$
R_0=\ker J,
\qquad
R_{n+1}=\{(z,u)\in R_n:\forall a\in\mathcal A,
\ell_a(z)=\ell_a(u)\ \land\ (F_a z,F_a u)\in R_n\}.
\tag{TM.1209}
$$

令 $\Phi(z)$ 收集初始 $J$ 值及每个有限动作词的全部标签和到达点的 $J$ 值。
则

$$
R_\infty:=\bigcap_{n\ge0}R_n=\ker\Phi.
\tag{TM.1210}
$$

**定理 12.2（四切面的有限完成与稳定深度）。** 每个 $R_n$ 都是等价关系，
$R_{n+1}\subseteq R_n$；链在某个

$$
d\le |Z|-|\operatorname{im}J|
\tag{TM.1211}
$$

处稳定，并且稳定关系是包含于 $\ker J$、同时保持所有 $\ell_a$ 与后继的最大前向同余。
联合读出 $J$ 本身是完整动态边界，当且仅当 $R_0=R_\infty$，等价于对每个
$a$，$\ell_a$ 在 $J$ 纤维上恒定且存在 $\overline F_a$ 使

$$
J\circ F_a=\overline F_a\circ J.
\tag{TM.1212}
$$

**证明。** 关系链的等价性由归纳得到：若 $R_n$ 是等价关系，则标签相等和
$R_n$ 中的后继条件在反身、对称、传递下都保持。严格细化时等价类数至少增加一，
而 $R_0$ 有 $|\operatorname{im}J|$ 个类、$Z$ 至多有 $|Z|$ 个类，故（TM.1211）。
对动作词长度作归纳，$(z,u)\in R_n$ 当且仅当长度不超过 $n$ 的所有标签—联合读出
转录相同；取交得到（TM.1210）。稳定关系正好是对所有动作保持标签和后继的最大
同余。若 $R_0=R_\infty$，零步联合读出已经保留这些条件，故可定义
$\overline F_a(Jz)=JF_a z$；反向则由（TM.1212）和标签因子化使链不再细化。
证毕。

### 12.4 联合图册不等于每一页都可递归

联合映射的核满足

$$
\ker(r_{\mathrm{space}},r_{\mathrm{time}},r_{\mathrm{boundary}},r_{\mathrm{memory}})
=\bigcap_{i\in I}\ker r_i.
\tag{TM.1213}
$$

所以四份表示的联合可以完整，即使每份单独都不完整。更一般地，实际像之间的
单向运输 $h_{ji}:Y_i^0\to Y_j^0$ 满足 $h_{ji}r_i=r_j$ 当且仅当

$$
\ker r_i\subseteq\ker r_j;
\tag{TM.1214}
$$

它在实际像上为双射当且仅当两个核相等。即使（TM.1213）等于 $R_\infty$，
每个分量仍须单独满足自己的动态下降方程，才能作为可递归运输的页面。

一个三状态见证为 $Z=\{0,1,2\}$，唯一动作是循环
$F(0)=1,F(1)=2,F(2)=0$，动作标签恒定，完整零步类型区分三状态。取

$$
r_{\mathrm{space}}(z)=\mathbf1_{z=0},\quad
r_{\mathrm{time}}(z)=\mathbf1_{z=1},\quad
r_{\mathrm{boundary}}(z)=*,\quad
r_{\mathrm{memory}}(z)=\mathbf1_{z=2}.
$$

四者的联合读出是单射，因而联合边界完整；但 $r_{\mathrm{space}}$ 把 $1,2$ 合并，
而它们的后继读出分别为 $0,1$，不存在 $\overline F$ 使
$r_{\mathrm{space}}F=\overline F r_{\mathrm{space}}$。$r_{\mathrm{time}}$ 与
$r_{\mathrm{memory}}$ 同理，常值 $r_{\mathrm{boundary}}$ 虽能下降却丢失区分。
因此“联合可恢复”不等于四个单独坐标都能递归运输。

### 12.5 四种名字各自承担什么

在同一 $Z$ 上，四个名字可以按任务解释为：

* **空间表示**记录端口、邻接、切面或允许路径；它必须保留未来路径实验会用到的
  共享接口。
* **时间表示**记录已声明的路径词、时钟读数或累计费用；若时钟本身不可见且
  不影响未来，不能凭空把它当作来源状态，若它影响选择则必须进 $Z$。
* **边界表示**通常就是 $q$ 或其一个双射编码；它保存全部指定续接所需的残余行为。
* **记忆表示**记录控制器、参考、权限和档案中会影响下一步的部分；不能把这些
  内容当作免费背景再声称只有边界一个状态。

因此空间和时间并非先验的两个坐标轴，边界也不是一张完整内部照片；四者是
同一联合来源经不同精确表示得到的四份坐标。若某一表示只保存当前读数而丢掉
后续会用到的关系，它就不满足（TM.1203），更不能参与图册运输。

### 12.6 三个有限实例

**FIB 二叶项。** FIB 卷的

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle
$$

给出源语法层；这里的自由树集合本身不假定有限。以下只在声明的“组成读取与
$\rho$ 后继”观察族（或其有限模/有限商）下使用 $\sim_{\mathscr T}$，因此有限性
属于所选边界商，不属于原始树集合。在该任务下，
$\ker c=\sim_{\mathscr T}$。若加入拼接，实际共同来源的合法域须满足
过程几何卷定理 3.5 的条件；事件、记录、时钟与后继须满足该卷 §29.1 的联合核条件。
这些下降条件保证动态充分性，核相等还须保留上面的任务范围。若读取左叶，
$\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$ 被区分，计数商
就不再是同一行为边界。

**有限仿射模网络。** 有效分辨率卷 §11 的 $D_v$ 是未来端口任务的最小边界。
一条边或一条已知路径的记忆纤维大小为

$$
k_\gamma=\frac{D_v}{D_w/\gcd(D_w,A_\gamma)}.
\tag{TM.1208}
$$

当 $k_\gamma=1$ 时，终端边界可以恢复起始边界；当 $k_\gamma>1$ 时，记忆必须
保存该纤维的索引。这个纤维索引正是时间运输不可逆时边界与记忆之间的缺口。

**联合读数与时钟。** 过程几何卷 §29.5 的三点模型中，输出边缘和时钟边缘
可以分别相同而联合核不同。故把空间、时间分别压缩再拼接，一般不能恢复（TM.1207）；
必须保留事件—时钟—后继的联合核。

### 12.7 数学运输与实际可执行恢复的分界

式（TM.1205）给出的是实际像上的数学双射，不自动给出观察者能够执行的操作。
要把 $\chi_{ji}$ 作为合法恢复器，还需声明：

1. 观察者实际可以读取 $Y_i^0$ 的输入，而不是只有理论上的完整函数表；
2. $\chi_{ji}$ 的计算、参考、权限和时间成本已计入同一记忆/记录合同；
3. 恢复后得到的表示仍在下一步合法动作的定义域内，并满足（TM.1207）；
4. 若只要求近似恢复，必须给出距离、误差传播和允许的测试族，不能把近似双射写成精确运输。

缺少这些条件时，最多得到表示层等价，不能宣称内部观察者已经取得了另一份表示。

### 12.8 失败边界与来源

最小反例是 $Z=\{a,b,c\}$，令 $q(a)=q(b)=0,q(c)=1$，并让唯一动作满足
$$F(a)=a,\quad F(b)=c,\quad F(c)=c.$$
当前摘要把 $a,b$ 合并，但下一步的可见终止类型不同，所以不存在边界函数
$\bar F$ 使 $qF=\bar Fq$。这说明当前读数相同不是动态充分性。

若两个表示只共享事件、时钟和后继的边缘，而不共享联合核，也会失败；
过程几何卷 §29.5 的有限反例给出见证。若 $Z$ 无限、核近似、量子通道或动作族不闭合，则（TM.1205）
仍可作为候选定义，但有限商、归一化和实际来源存在性必须另证。

本节的有限经典综合接用过程几何卷定理 3.5 的实际来源部分拼接、§29.1 的联合
事件—时钟—后继核及 §29.5 的边缘反例，并接用有效分辨率卷 §11 和本卷
第1—5节的运输、记忆和完成接口。
它给出的最小统一对象不是一个最大坐标，而是实际来源上的动态行为商及其四份自然表示。

## 13. FIBONACCI_ATOMIC_RELATION_GENERATION 作为生成基础

上一节把 FIB 二叶项放在四重图册的一个实例位置。若要回答“它是不是更基础”，
必须先区分三种不同的“原子性”：语法上不可再展开、在指定观察族下不可区分，
以及作为动力学的不可约操作。这三者不是同一个概念。

### 13.1 两个叶生成元与独立的组合原语

FIB 卷所用的源签名可以写成

$$
\Sigma_{\mathrm{Fib}}
 =\bigl\{\alpha,\beta,\langle-,-\rangle,\rho\bigr\},
$$

其中

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle .
\tag{RA.1301}
$$

在这个签名中，$\alpha,\beta$ 是两类叶生成元：它们没有由语法给出的子项。
二元构造 $\langle s,t\rangle$ 却不是第三个叶原子，而是把已有项组成新项的独立
原语；它有序、非交换、非结合，除非另加关系，不能把
$\langle\alpha,\beta\rangle$ 化成任何一个叶，也不能把左右次序抹掉。

因此，“底层只有两个不可约关系”只有在把“关系”限定为**叶标签**时才准确。
若“关系”指产生后继或组合的操作，则至少还要保留二元组合和替换：

$$
\rho(\alpha)=\beta,
\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,
\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle .
\tag{RA.1302}
$$

这里 $\rho$ 是动力学，$\langle-,-\rangle$ 是构造，$\alpha,\beta$ 是源标签；
不能把三者压成同一种对象。

更严格地说，忽略 $\rho$ 后的源层是函子

$$
X\longmapsto \{\alpha,\beta\}+X\times X
$$

的初始代数。给定任意载体 $X$、两个解释 $a_X,b_X\in X$ 和二元运算
$\mu:X\times X\to X$，存在唯一解释

$$
\operatorname{Eval}(\alpha)=a_X,
\qquad
\operatorname{Eval}(\beta)=b_X,
\qquad
\operatorname{Eval}(\langle s,t\rangle)
 =\mu(\operatorname{Eval}(s),\operatorname{Eval}(t)).
\tag{RA.1302a}
$$

因此它是一个可递归解释的生成语法，而不是已经选定的一种数值模型。数值、矩阵、
关系档案和程序都只是对同一自由项的不同解释；解释值相同不能反推源项相同。

### 13.2 “不可约”必须带观察任务下标

令 $\mathcal T_{\mathrm{Fib}}$ 为自由二叉树集合，$\mathscr E$ 为声明的测试族。
语法不可约只说 $\alpha,\beta$ 是叶；行为不可约则应写成

$$
\alpha\not\sim_{\mathscr E}\beta
\quad\Longleftrightarrow\quad
\exists E\in\mathscr E,
\ \operatorname{Obs}_E(\alpha)
\ne
\operatorname{Obs}_E(\beta).
\tag{RA.1303}
$$

若测试族只读取原子计数，$\langle\alpha,\beta\rangle$ 与
$\langle\beta,\alpha\rangle$ 会被合并；若测试族能够读取左、右路径，它们会被区分。
所以 $\alpha,\beta$ 作为叶生成元是固定的，哪些项仍然不可约却由观察合同决定。
这正是动态行为商的作用：

$$
q_{\mathscr E}:\mathcal T_{\mathrm{Fib}}
\twoheadrightarrow
\mathcal T_{\mathrm{Fib}}/{\sim_{\mathscr E}}
$$

可以把语法生成层和任务边界层分开。不能从“有两个叶”直接推出任何观察者都必须
保存整棵树。

### 13.3 为什么两叶是一个最小的非平凡源层

在固定目标为“有两类可区分的叶，并允许有限二元组合”的口径下，
$(\alpha,\beta,\langle-,-\rangle)$ 是最小的自由源层：

* 零个叶不能生成非空项；
* 一个叶和二元构造只能生成未标记的树，无法表达两类叶之间的区别；
* 两个叶加一个二元构造已经能生成任意有限有序二叉项。

这是**签名的最小性**，不是说所有关系系统都能被这一个签名无损表示。要使它成为
Fibonacci 源，还必须加入 $\rho$ 及其在叶和构造上的递归作用；没有 $\rho$ 时只有静态
自由项，没有 $T_{j+2}=\langle T_{j+1},T_j\rangle$ 的后继规律。

在计数任务中，组成映射

$$
c(\alpha)=(1,0),\qquad c(\beta)=(0,1),\qquad
c(\langle s,t\rangle)=c(s)+c(t)
$$

把自由树投影到 $\mathbb N^2$，而 $\rho$ 在组成层诱导

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},
\qquad c(\rho t)=M c(t).
\tag{RA.1304}
$$

于是 FIB 的基础性可以精确表述为：它给出一个两通道源层和一个保持该源层的线性
后继，而不是预先给出一个最大宇宙状态。

### 13.4 从生成层到动态边界

若任务只要求组成及其 Fibonacci 后继，取 $q_{2,3}(a,b)=2a+3b$，并定义两层边界

$$
\partial_{2,3}(t)
 =\bigl(q_{2,3}(c(t)),q_{2,3}(M c(t))\bigr).
$$

由于

$$
\begin{pmatrix}2&3\\3&5\end{pmatrix}
$$

行列式为 $1$，有

$$
\ker\partial_{2,3}=\ker c
\quad\text{在 }\mathcal T_{\mathrm{Fib}}\text{ 上成立}.
\tag{RA.1305}
$$

并且存在边界更新

$$
U(n,n')=(n',n+n'),
\qquad
\partial_{2,3}(\rho t)=U\partial_{2,3}(t).
\tag{RA.1306}
$$

所以在“组成—Fibonacci 后继”这个明确任务下，FIB 的两个叶生成层确实产生了一个
精确动态边界：边界只忘记树的次序和括号，而不忘记该任务要求的全部未来数量响应。

但若任务扩大为完整路径读数，则

$$
\ker c\supsetneq\sim_{\mathrm{path}};
$$

例如 $\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$ 有相同组成，
却有不同的左叶读数。此时 $\partial_{2,3}$ 仍是组成任务的边界，却不是完整树任务的
动态充分边界；必须把路径接口或等价的结构记录加入联合状态。

### 13.5 与四重关系图册的接合

在上一节的记号中，可以把 FIB 的不同层写成同一来源上的不同读出：

$$
r_{\mathrm{source}}(t)=t,
\qquad
r_{\mathrm{boundary}}(t)=\partial_{2,3}(t),
\qquad
r_{\mathrm{memory}}(t)=\text{保存路径与替换所需的记录}.
$$

对组成任务，$r_{\mathrm{boundary}}$ 已经等于最小行为商的一个双射编码；对完整树
任务，$r_{\mathrm{memory}}$ 必须补回被 $c$ 合并的结构关系。于是“空间、时间、边界、
记忆”不是四个先验实体，而是同一 FIB 共同来源在不同测试合同下的表示。

这也给“FIB 更基础”一个严格范围：

$$
\boxed{
\text{FIB 提供最小的二叶生成与后继层；}
\quad
\text{观察者、边界和拼接仍由任务商与联合核定义。}
}
$$

若要把 FIB 推广为一般关系过程，需要把叶集合、构造器、动作、合法性和记录核参数化。
仅把所有对象命名成 $\alpha$ 或 $\beta$ 不会自动得到一般过程，也不会自动得到物理时空。

本节的“更基础”是相对于当前关系图册的**生成层基础性**，不是已证明的宇宙本体
还原；FIB 卷仍是理论输入，本文新增连接也未宣称已经完成 Lean 核验。

## 12.99 追加锚

## 14. 实际共同来源的联合核下降与 FIB 图册自然性

### 14.1 有类型的共同来源与完整一步合同

固定有限有类型来源 $S_i,S_j,S_k$ 和摘要 $q_\ell:S_\ell\to B_\ell$，
其中 $B_\ell=q_\ell[S_\ell]$ 只取实际像。实际共同来源是给定的
$C\subseteq S_i\times S_j$；它声明哪些输入对共同实现，不由两个局部像的乘积推定。
令 $g:(i,j)\to k$ 为具名拼接动作，全部参数包含在 $g$ 中，并置

$$
A=(q_i\times q_j)|_C,\qquad B=A[C],\qquad D=D_g\subseteq C.
\tag{RA.1401}
$$

$D$ 是当前实际输入的合法域。有限集合 $E_g$ 包含全部声明事件，$R_g$ 包含
全部声明记录、writer 输出和时钟增量；后续所需的权限、控制器及记忆也须进入
后继 $u\in S_k$ 或保留记录。给出只在合法行上定义的联合核

$$
J_g(v;\eta,u,r)\ge0,\qquad
\sum_{\eta\in E_g,\,u\in S_k,\,r\in R_g}J_g(v;\eta,u,r)=1
\quad(v\in D).
\tag{RA.1402}
$$

这里的目标是保留合法性及事件—记录—时钟—后继摘要的共同律，不要求恢复
被 $q_k$ 合并的内部后继。过程几何卷定理 3.5 给出实际来源的部分拼接接口，
§29.1 给出带标签的后继纤维求和；以下将二者用于同一个有限合同。

### 14.2 精确下降、合法域与联合关系的两个障碍

**定理 14.1（实际来源上的精确有限判据）。** 存在商合法域 $\bar D\subseteq B$
和其上的归一化联合核 $\bar J_g(b;\eta,b',r)$，满足

$$
D=A^{-1}(\bar D),\qquad
\bar J_g(A(v);\eta,b',r)
=\sum_{q_k(u)=b'}J_g(v;\eta,u,r)\quad(v\in D),
\tag{RA.1403}
$$

当且仅当 $D=A^{-1}(A[D])$，且对所有 $v,w\in D$，若 $A(v)=A(w)$，则
对每个 $\eta\in E_g,r\in R_g,b'\in B_k$ 有

$$
\sum_{q_k(u)=b'}J_g(v;\eta,u,r)
=\sum_{q_k(u)=b'}J_g(w;\eta,u,r).
\tag{RA.1404}
$$

全部原像在 $C$ 内取。商唯一，其合法域为 $\bar D=A[D]$，合法行由
（RA.1403）的纤维和定义；$B\setminus\bar D$ 只承载不合法判定，不承载核行。

证明。若商存在，$D=A^{-1}(\bar D)$ 使合法性在每个实际 $A$ 纤维上恒定；
由 $A:C\twoheadrightarrow B$ 得 $\bar D=A[D]$。同一商行的单值性给（RA.1404）。
反向，饱和性下降合法域，（RA.1404）保证按任一合法代表定义的纤维和无关代表。
非负性继承自 $J_g$；$q_k$ 的各实际纤维分割 $S_k$，所以求和归一化仍为一。
实际像上的满射性给唯一性，包括 $D=\varnothing$ 时无合法行的情形。
不向 $B$、$B_k$ 的像外补入状态，也不向非法输入补入概率行为。$\square$

**定理 14.2（对角合法域的尖锐障碍与边缘不足）。** 取
$S_i=S_j=\{0,1\}$，两个局部摘要恒为 $*$，明确给定实际载体
$C=\{0,1\}^2$，但只允许 $D=\{(0,0),(1,1)\}$。
两条合法行都以概率一输出同一事件、同一记录和唯一后继，则（RA.1404）成立，
而合法性仍不能下降。若实际载体改为该对角线，且 $D=C$，相同核便能下降。

证明。前一种载体有 $A^{-1}(A[D])=C\ne D$，常值摘要同时有合法与非法代表。
后一种载体只有合法代表，故两项判据都成立。在前一种载体中，额外保留
$\mathbf1_{x=y}$ 就足以切开合法与非法纤维；无需凭空恢复两个局部隐藏位。$\square$

联合条件也不能用逐边缘比较代替。过程几何卷 §29.5 的有限反例取来源
$v,w,t$，把 $v,w$ 摘为同值，后继恒为 $t$，令事件 $\eta$ 与时钟记录 $r$ 为位：

$$
J(v;0,t,0)=J(v;1,t,1)=\tfrac12,\qquad
J(w;0,t,1)=J(w;1,t,0)=\tfrac12.
\tag{RA.1405}
$$

在 $t$ 上取 $J(t;0,t,0)=1$，此外各项为零。事件边缘、时钟边缘、后继边缘，甚至事件—后继和时钟—后继
两份边缘都相同，但 $\Pr(\eta=r\mid v)=1$、$\Pr(\eta=r\mid w)=0$。
因此（RA.1404）失败；合法域饱和与联合核恒定是各自不可省略的条件。

### 14.3 实际像上的图册自然性与递归选择

**定理 14.3（共同来源下的自然运输）。** 令
$\chi_\ell:B_\ell\to\widetilde B_\ell$ 为双射，
$\widetilde q_\ell=\chi_\ell q_\ell$，并保留同一个 $C,D,J_g,E_g,R_g$。
则 $\Xi=(\chi_i\times\chi_j)|_B$ 将 $B$ 双射到
$\widetilde B=\widetilde A[C]$，且定理 14.1 的两项条件在运输前后等价。
若下降条件成立，商合法域和联合核的运输在合法行上满足

$$
\widetilde{\bar D}=\Xi[\bar D],\qquad
\widetilde{\bar J}_g(\Xi b;\eta,\chi_k b',r)
=\bar J_g(b;\eta,b',r).
\tag{RA.1406}
$$

证明。$\widetilde A=\Xi A$，故运输不改变输入纤维；
$\widetilde q_k(u)=\chi_k b'$ 与 $q_k(u)=b'$ 等价，故后继求和指标也相同。
合法域随像运输，核的交换式直接由（RA.1403）得到。$\square$

若各页面运输由同一来源上的 $\chi_\ell^{ba}q_\ell^a=q_\ell^b$ 确定，
实际像上的唯一性还给出 cocycle
$\chi_\ell^{ca}=\chi_\ell^{cb}\chi_\ell^{ba}$、恒等运输与逆运输。
因为两条路径复合后在每个实际来源值上的输出都为 $q_\ell^c$，运输与路径无关；
这要求同源对应，不是任意选择一组双射就自动成立。

有限自适应选择器须通过可取得的商值 $b$ 与全部保留记录 $c$ 因子化，
包括停止、动作参数及记录更新。运输合同为
$\widetilde\Pi_n(g\mid\Xi b,c)=\Pi_n(g\mid b,c)$，所选动作须在当前商值合法。
若每个后续拼接仍使用它的实际载体并满足定理 14.1，初始记录匹配且共同更新，
按步数归纳，（RA.1406）保持全部有限联合转录律。递归接合不新增独立准备权限。

对同一来源的两个读出 $f,h$，$\ker f\subseteq\ker h$ 只给实际像上的唯一
单向因子 $h=\bar h f$：在 $f$ 纤维上定义 $\bar h(f(z))=h(z)$ 即可。
核相等才给双向恢复及上述唯一双射；行为充分只保证包含于行为等价关系。
数学恢复若要成为内部观察者的操作，仍须满足 §12.7 的可读取与执行条件。

### 14.4 FIB 的有限组成图册及其恢复边界

取 $m\ge2$，令 $V_m=(\mathbb Z/m\mathbb Z)^2$，$x=c(t)\bmod m$。
每个余数组成都可由非负计数提升并取总叶数非零的树实现，故实际像是整个 $V_m$。
$\alpha,\beta$ 仍是叶生成元，配对仍是独立构造原语，$\rho$ 是动力学；
组成商把配对送到加法，把替换送到 $x\mapsto Mx$。置

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
H=\begin{pmatrix}2&3\\3&5\end{pmatrix}=M^4,\qquad
r_{\rm space}(x)=x,\quad r_{\rm time}(x)=Mx,\quad
r_{\rm boundary}(x)=Hx,\quad r_{\rm memory}(x)=M^{-1}x.
\tag{RA.1407}
$$

$\det M=-1$、$\det H=1$ 在模 $m$ 下都是单位，所以四份表示都是双射。
对相应矩阵 $T_a\in\{I,M,H,M^{-1}\}$，更新为
$U_a=T_aMT_a^{-1}$，运输为 $\chi_{ba}=T_bT_a^{-1}$。
这些矩阵都与 $M$ 交换，故 $U_a=M$ 且 $\chi_{ba}U_a=U_b\chi_{ba}$；
运输的 cocycle 由中间矩阵及其逆抵消得到。

作为实际联合核实例，可取 $C=\{(x,x):x\in V_m\}$、$D=C$，拼接后继为 $Mx$，
事件固定、时钟增量固定为一、其余记录固定。任取两个页面作输入摘要、一个页面
作后继摘要，$A$ 都是单射，定理 14.1 成立；定理 14.3 就给四份坐标的共同运输。
此例的共同来源是对角线，不声称所有页面值可以独立拼接。

若声明任务读取 $\ell(x)=2x_1+3x_2$ 及其全部 $\rho$ 后继读数，则
$(\ell(x),\ell(Mx))=Hx$，前两次读数已经区分全部 $m^2$ 个组成状态。
任意单个标量映射 $V_m\to\mathbb Z/m\mathbb Z$ 至多有 $m$ 个值，不能精确恢复；
两个这样的标量读数达到界。时间页是一步移位坐标，记忆页是前态坐标；
它们的精确性限于这个组成与数量续接合同。

这是有限模组成商的图册，不能恢复树的次序或括号。
$\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$ 有相同模组成，
四页及全部后继数量读数相同，但左叶不同；加入左路径读取就破坏组成商的充分性。
本例使用 FIB 卷 §3.4、§5.4—5.5 的组成更新和两层数量读取，
四份名称只指同一任务商的条件表示。

## 追加锚（本行以下为增补区）

## 15. FIB 生成层的同余商与内部观察闭合

上一节把实际共同来源上的联合核下降条件写成了边界判据。本节补上 FIB 源层与
该判据之间的一个接口：只有当观察任务对允许的组合上下文闭合时，FIB 的行为商
才自身继承组合与后继；否则它只是一次读数的压缩，不能作为内部观察者继续运行的
状态。

### 15.1 组合上下文决定何时行为商继承源运算

令

$$
\mathcal T=\mu X.\bigl(\{\alpha,\beta\}+X\times X\bigr)
$$

为 FIB 的自由有序二叉项。固定一个带类型的部分组合合同，其合法域记为
$D_\mu\subseteq\mathcal T\times\mathcal T$；$\rho$ 若不是全定义的，记其合法域为
$D_\rho\subseteq\mathcal T$。一个带一个孔的上下文由

$$
[-],\qquad \langle C[-],t\rangle,\qquad
\langle t,C[-]\rangle,\qquad \rho\circ C[-]
$$

反复生成；实际任务只取其中声明为合法的上下文族 $\mathcal C$。要求恒等上下文
$[-]$ 在 $\mathcal C$ 中；对每个 $(s,u)\in D_\mu$，外层上下文
$\langle[-],u\rangle$ 在相应位置合法，对每个 $(u,s)\in D_\mu$，
$\langle u,[-]\rangle$ 在相应位置合法；当 $s\in D_\rho$ 时 $\rho[-]$ 也合法。
此外，要求 $\mathcal C$ 对把一个合法上下文代入另一个合法上下文封闭。设
$\operatorname{Obs}(C[t])$ 包含该上下文的合法性、事件、记录、时钟和指定后继读数，
并定义

$$
s\equiv_{\mathcal C}t
\iff
\forall C\in\mathcal C,\quad
\operatorname{Obs}(C[s])=\operatorname{Obs}(C[t]).
\tag{RA.1501}
$$

以下假设 $D_\mu,D_\rho$ 对（RA.1501）的等价关系饱和。

若 $s\equiv_{\mathcal C}t$，则对每个使相应组合合法的 $u$ 有

$$
\begin{gathered}
\langle s,u\rangle\equiv_{\mathcal C}\langle t,u\rangle,
\qquad \langle u,s\rangle\equiv_{\mathcal C}\langle u,t\rangle,\\
s,t\in D_\rho\Longrightarrow \rho(s)\equiv_{\mathcal C}\rho(t).
\end{gathered}
\tag{RA.1502}
$$

证明只需把外层上下文分别取为 $\langle[-],u\rangle$、$\langle u,[-]\rangle$
和 $\rho[-]$；这些上下文只在相应合法域内使用，闭合条件保证它们仍属于测试族。
于是 $\equiv_{\mathcal C}$ 是允许操作意义下的部分同余。令

$$
\bar D_\mu=\{([s],[t]):(s,t)\in D_\mu\}.
$$

饱和条件使它与代表元无关；商上的组合与后继应写成

$$
\bar\mu:\bar D_\mu\to\mathcal T/{\equiv_{\mathcal C}},
\qquad
\bar\mu([s],[t])=[\langle s,t\rangle],
\qquad
\bar\rho([s])=[\rho(s)]\quad([s]\in D_\rho/{\equiv_{\mathcal C}}).
\tag{RA.1503}
$$

非法组合或非法后继若属于任务读数，则由 $\operatorname{Obs}$ 中的失败标签保留；
否则它们不在（RA.1503）的定义域内。若上下文族不封闭，则（RA.1502）不能从一次
读数相同推出，商最多是当前任务的摘要，不自动是一个能继续拼接的源过程。

### 15.2 组成商是 FIB 源的一个同态边界

在只观察组成及其 $\rho$ 后继的任务中，令

$$
c(\alpha)=(1,0),\qquad c(\beta)=(0,1),\qquad
c(\langle s,t\rangle)=c(s)+c(t),
$$

并记 $B_c=c[\mathcal T]\subseteq\mathbb N^2$。则 $B_c$ 对加法和

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}
$$

作用封闭，并满足

$$
c(\langle s,t\rangle)=c(s)+c(t),
\qquad
c(\rho s)=Mc(s).
\tag{RA.1504}
$$

因此 $c$ 在该任务下诱导

$$
\bar\mu_c(x,y)=x+y,
\qquad
\bar\rho_c(x)=Mx.
\tag{RA.1505}
$$

FIB 卷的两层数量读数定理给出：对只读取组成和全部 $\rho$ 后继的观察族，
$c(s)=c(t)$ 当且仅当两项具有相同的任务行为。因此 $B_c$ 是该任务行为商的
一个实际同构编码；它忘记次序和括号，但不忘记该任务要求的组合与后继。

相反，单个数量读数通常不是动态边界。取

$$
t=\langle\alpha,\langle\alpha,\alpha\rangle\rangle,
\qquad
u=\langle\beta,\beta\rangle,
$$

则 $c(t)=(3,0)$、$c(u)=(0,2)$。对 $\ell(a,b)=2a+3b$ 有

$$
\ell(c(t))=\ell(c(u))=6,
$$
但

$$
\ell(c(\rho t))=9,
\qquad
\ell(c(\rho u))=10.
\tag{RA.1506}
$$

所以不存在 $\bar\rho:\ell[B_c]\to\ell[B_c]$ 使
$\ell c\rho=\bar\rho\ell c$。一个当前标量可以是合法读数，却不是可递归运输的
边界；两层读数或等价的联合关系才闭合。

### 15.3 内部观察者何时只需访问边界

本小节限于确定性操作和一个固定的共同初始记忆；随机或分支过程应改用第 14 节的
联合事件—记录—后继核。令 $q:\mathcal T\to B$ 是一个候选边界，$M_O$ 是观察者的
工作记忆。对任务中允许的每个操作 $a$，令 $L_a$ 为完整状态上的合法性指标，
并假设存在边界合法性 $\bar L_a$、边界更新 $\bar T_a$、记录函数
$\overline{\operatorname{Rec}}_a$ 和记忆更新 $\bar U_a$，满足

$$
\begin{aligned}
L_a(s)&=\bar L_a(q(s)),\\
q(T_a(s))&=\bar T_a(q(s))\qquad(L_a(s)=1),\\
\operatorname{Rec}_a(s,m)&=\overline{\operatorname{Rec}}_a(q(s),m),\\
U_a(s,m)&=\bar U_a(q(s),m)\qquad(L_a(s)=1).
\end{aligned}
\tag{RA.1507}
$$

当 $L_a(s)=0$ 时，记录函数取已声明的失败事件和失败记录；后继更新不被调用，
或等价地把它扩展到一个失败吸收态。这样合法性和失败也都从边界恢复。

并且选择器满足

$$
\pi(s,m)=\bar\pi(q(s),m).
\tag{RA.1508}
$$

则对相同的初始记忆 $m$，任意有限内部转录只由 $(q(s),m)$ 决定。证明按转录长度归纳：零步时由
（RA.1508）决定动作；执行后由（RA.1507）决定边界、记录与记忆的下一值；归纳
假设再应用于下一步。因而观察者不需要访问完整树，只需访问动态充分边界及其实际
保留的记忆。

反向地，若一个表示对所有声明的组合、$\rho$ 接续及内部选择都能生成相同的
有限转录，则它的核必须包含在相应行为等价关系中；若还要求该表示支持源层的
组合更新，则其核必须对这些操作成同余。于是“FIB 只有两个不可约关系”不能直接
成为观察者状态的结论；真正可执行的状态是

$$
\boxed{
\text{两叶生成元的源签名}
\;+
\text{任务闭合的行为商}
\;+
\text{选择器实际保留的记忆}.
}
\tag{RA.1509}
$$

这把 FIB 的基础性限定在生成层，同时说明它怎样进入局部过程—观察者—边界—拼接
模型：叶标签给出源，二元构造给出拼接，$\rho$ 给出后继，行为同余给出边界，
而观察者记忆保存尚未被当前商吸收但仍影响后续选择的关系。所有结论仍限定在声明的
有限或可定义任务族；它们不把组成商升级为完整树、物理时空或任意未声明实验的全知状态。

### 15.4 数量矩阵相容不等于语法替换相容

还需区分边界层的矩阵运输与源语法上的实际替换。对任意有限项
$u,v\in\mathcal T$，定义叶替换同态

$$
\widehat A_{u,v}(\alpha)=u,\qquad
\widehat A_{u,v}(\beta)=v,\qquad
\widehat A_{u,v}(\langle s,t\rangle)
 =\langle\widehat A_{u,v}(s),\widehat A_{u,v}(t)\rangle,
$$

并令

$$
A_{u,v}=\begin{bmatrix}c(u)&c(v)\end{bmatrix}\in M_2(\mathbb N).
$$

结构归纳给出

$$
c\bigl(\widehat A_{u,v}(t)\bigr)=A_{u,v}c(t)
\qquad(t\in\mathcal T).
\tag{RA.1510}
$$

若 $A_{u,v}M=MA_{u,v}$，则只有组成商上的交换式成立：

$$
c\bigl(\widehat A_{u,v}(\rho t)\bigr)
=A_{u,v}Mc(t)
=MA_{u,v}c(t)
=c\bigl(\rho\widehat A_{u,v}(t)\bigr).
\tag{RA.1511}
$$

但自由树上的交换有更强的充要条件：

$$
\boxed{
\widehat A_{u,v}\circ\rho=\rho\circ\widehat A_{u,v}
\iff
v=\rho(u)\ \text{且}\ \rho(v)=\langle v,u\rangle .
}
\tag{RA.1512}
$$

证明。若两侧相等，在 $\alpha$ 上得到 $v=\rho(u)$，在 $\beta$ 上得到
$\rho(v)=\langle v,u\rangle$。反向地，这两个等式使两侧在两个叶生成元上相同；
两者又都是保持有序二元构造的同态，故对全部有限树作结构归纳即相同。证毕。

矩阵中心化器条件不能替代（RA.1512）。取

$$
u=\langle\alpha,\alpha\rangle,
\qquad
v=\langle\beta,\beta\rangle.
$$

此时 $A_{u,v}=2I$，所以 $A_{u,v}M=MA_{u,v}$；然而

$$
\widehat A_{u,v}\rho(\beta)
=\langle\langle\beta,\beta\rangle,\langle\alpha,\alpha\rangle\rangle,
$$

而

$$
\rho\widehat A_{u,v}(\beta)
=\langle\langle\beta,\alpha\rangle,\langle\beta,\alpha\rangle\rangle.
\tag{RA.1513}
$$

两棵有序树不同，但它们的组成均为 $(2,2)$，因而全部组成—$\rho$ 未来读数相同。
这给出一个严格的层级分界：黄金整数或矩阵动力学的相容性是行为商上的运输条件，
不是原子关系生成语法上的相容性。若观察者只访问组成边界，（RA.1511）已经足够；
若它需要执行叶替换并保留完整树语法，则必须额外验证（RA.1512）或保存能区分
（RA.1513）两棵树的结构记忆。

因此，FIB 的“两个不可约关系”最稳妥的含义是两个叶生成元；其后的矩阵、黄金整数
和边界运输都属于不同层。只有把相应的同态、行为商和观察任务逐层对齐，才能把
生成层接到内部观察者的可执行拼接上。

### 15.5 扩展观察签名只会细化行为商

设 $S$ 是当前的部分操作签名，$T$ 是对它的扩展：旧符号的元数和部分操作在
$T$ 中保持不变，只增加新的合法操作或新的上下文。对同一读出 $q$，记
$\equiv_S$、$\equiv_T$ 为各自的全部严格上下文观察等价。则有

$$
\boxed{
\equiv_T\ \subseteq\ \equiv_S.
}
\tag{RA.1514}
$$

因为 $T$ 的上下文族包含旧签名的上下文族，$T$ 下相等的全部观察转录必然包括
$S$ 下的全部转录。因而增加可执行的观察或接续只能拆分原有边界类，不能把原先
已经可区分的来源重新合并。

在 FIB 中，组成任务的边界核是 $\ker c$。加入左叶读取后，
$\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$ 仍有相同组成，
却有不同的新转录，所以

$$
\equiv_{\mathrm{path}}\subsetneq\ker c.
\tag{RA.1515}
$$

这不是四页坐标之间的一次运输失败，而是任务签名本身变强后，最小边界发生了真实
细化。反过来，若每个新增读数、合法性和后继都能写成旧边界上的函数，并且新增操作
在旧边界上满足同一部分同余条件，则新上下文对旧纤维不再产生区分，商保持不变。
所以“换一张图”与“允许一种新实验”必须分开：前者要求同一行为商上的双射，后者
通常改变行为商本身。

（RA.1514）的抽象支点是仓内
`StrictOneHoleContexts.contextual_equivalence_is_greatest` 与
`signature_extension_refines`；本节只把它们特化到 FIB 的源签名和组成边界，未新增
Lean 声明。部分操作的合法性、失败标签和实际共同来源仍须按第 14 节的联合核条件
保留，不能因签名扩展而省略。

### 15.6 精确有限观察器必须覆盖完整行为商

再固定一个有限的 FIB 任务：源状态集为有限实际像 $Y$，动作更新为
$T_a:Y\to Y$，当前读出为 $o:Y\to O$。令

$$
\mathsf B(y)(w)=o(T_w(y)),
\qquad
Q=Y/{\ker\mathsf B},
\qquad
q:Y\twoheadrightarrow Q,
\tag{RA.1516}
$$

其中 $w$ 遍历包括空词的全部有限动作词，$T_w$ 按动作词逐项复合。
完整行为相等在每个动作下保持，且包含当前读数相等，因此商上有良定义的
$T_a^Q([y])=[T_a(y)]$ 与 $o_Q([y])=o(y)$。若一个有限观察器载体 $W$ 具有满射实现
$r:Y\twoheadrightarrow W$、更新 $\widetilde T_a$ 和读出 $\widetilde o$，并满足

$$
rT_a=\widetilde T_a r,
\qquad
o=\widetilde o r,
\tag{RA.1517}
$$

则存在唯一满射

$$
f:W\twoheadrightarrow Q,
\qquad q=fr,
\tag{RA.1518}
$$

且 $f$ 交织每个动作更新和当前读出：

$$
f\widetilde T_a=T_a^Qf,
\qquad o_Qf=\widetilde o.
\tag{RA.1518a}
$$

证明是：由（RA.1517）沿动作词归纳，
$r$ 的同一纤维产生同一完整行为，因此 $\mathsf B$ 在 $r$ 的纤维上恒定；实际像
给出 $f(r(y))=q(y)$ 的良定义。$r$ 满射保证它定义在整个 $W$ 上且唯一；
$q=fr$ 及 $q$ 满射保证 $f$ 满射。把每个 $w\in W$ 写成 $r(y)$，
再应用（RA.1517），即得（RA.1518a）。于是

$$
|Q|\le |W|.
\tag{RA.1519}
$$

对 FIB 的组成—$\rho$ 后继任务，固定 $m\ge2$ 并取

$$
Y=V_m=(\mathbb Z/m\mathbb Z)^2,
\qquad T(x)=Mx,\qquad o(x)=2x_1+3x_2.
$$

则前两层数量读数的可逆矩阵使 $Q\cong V_m$，故任何精确有限观察器至少需要
$m^2$ 个实际实现状态。若整个观察器状态只保存一个模 $m$ 标量，则至多有 $m$ 个
值，不能满足这一界；两层读数作为联合状态达到它。这里计数的是全部允许初态的
完整未来行为，不是某一次输出的字母表大小。§14.4 已说明每个模组成状态都有
实际树来源；这里不把从单个 $\alpha$ 出发的 $M$ 轨道等同于整个 $V_m$。

（RA.1516）—（RA.1519）是仓内
`D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.controlled_behavior_universal_property`
的 FIB 特化说明；本节没有新增 Lean 声明。它把“两个叶生成元”与“观察者必须
保存多少可继续使用的边界状态”明确分开：前者是源签名的大小，后者由任务行为商
决定，二者不能相互替代。

### 15.7 叶原子数与允许操作下的最少种子数

§13.3 的两叶最小性固定了“保留两类叶、仅用配对构造”的口径。
若讨论允许动力学后的生成能力，就必须重新声明允许的操作。记
$\mu(s,t)=\langle s,t\rangle$，令

$$
\Omega_0=\{\mu\},\qquad \Omega_1=\{\mu,\rho\}.
$$

对初始种子集 $A\subseteq\mathcal T$，记 $\langle A\rangle_\Omega$ 为包含 $A$
且对 $\Omega$ 中操作封闭的最小子集。这里闭包只使用列明的正元数操作；
$\alpha,\beta$ 是载体中的元素，不作为可免费注入闭包的零元运算。
否则若把两叶都列作可调用常元，空种子已经能生成全部项，种子计数就换了口径。

**命题 15.1（固定操作集下的种子最小性）。** 对上述两种闭包，有

$$
\min\{|A|:\langle A\rangle_{\Omega_0}=\mathcal T\}=2,
\qquad
\min\{|A|:\langle A\rangle_{\Omega_1}=\mathcal T\}=1.
\tag{RA.1520}
$$

第一式由 $\{\alpha,\beta\}$ 达到，第二式由 $\{\alpha\}$ 达到。

证明。配对的结果总是非叶项，故若纯配对闭包含有 $\alpha,\beta$，
这两个叶必须都已在种子集中；两叶又按自由树的定义生成全部有限项，证明第一式。
加入 $\rho$ 后，$\rho(\alpha)=\beta$，所以从 $\{\alpha\}$ 先取得两叶，
再由配对生成全部项。空集在一元和二元操作下仍封闭，不能生成非空的 $\mathcal T$，
证明第二式。事实上 $\mu$ 和 $\rho$ 都不会输出根为 $\alpha$ 的项，
所以任何生成全部项的种子集仍必须含 $\alpha$；这里没有声称任意单种子都足够。
证毕。

仅有 $\rho$ 的单种子轨道也不同于允许配对的闭包：

$$
\{\rho^n(\alpha):n\ge0\}\subsetneq\mathcal T.
\tag{RA.1521}
$$

例如 $\langle\alpha,\alpha\rangle$ 不在该轨道中：零步只有 $\alpha$，
而从第一步起每个后继都含有 $\beta$ 叶。这直接来自两条叶替换规则。
所以把初始种子数降为一，没有消除配对操作，也没有把全部树压成一条后继路径。

这些结论只使用 FIB 卷定义 2.1、定理 2.2 与定义 3.1，是对生成口径的纸面推导，
不宣称新增 Lean 核验。$\beta$ 在配对语法中不可分解，与它能通过
$\rho(\alpha)$ 取得并不冲突。FIB 的生成基础应由叶类型、组合构造和替换规则共同
给出；生成元或种子的数量不能替代 §15.6 中由未来行为决定的观察器容量。

## 追加锚（本行以下为增补区）


## 16. 读取接口决定的补充记忆与实际图册初始化

§15.6 比较完整观察器与任务行为商。本节固定一个已经声明的有限状态任务，再把完整表示拆成当前可读界面与补充记忆，区分两种更新权限。FIB 卷 §36、§42–43 已区分逐层最少记录、自治记录塔和联合运输；这里研究同一精度层上的可逆后继，不能直接搬用精度塔的数值下界。

### 16.1 当前可读界面与两种更新合同

令 $X$ 为有限非空任务状态集，$T:X\to X$ 为置换，$q:X\to Y=q[X]$ 为当前可读界面。目标是在每个规定接口恢复 $x\in X$；若原始来源还含任务之外的细节，应先明确任务商，而不是把本节的恢复目标扩成整个来源。补充记忆为 $r:X\to R=r[X]$，要求

$$
E_r(x)=(q(x),r(x))\quad\text{单射}.
\tag{RA.1601}
$$

允许读取界面的更新合同是存在 $U:E_r[X]\to R$，使

$$
r(Tx)=U(q(x),r(x)).
\tag{RA.1602}
$$

只依赖记忆的自主更新合同则要求存在 $u:R\to R$，使

$$
r(Tx)=u(r(x)).
\tag{RA.1603}
$$

式（RA.1603）的输入只有当前记忆；时刻、界面值、策略状态、外部档案或其他寄存器若参与计算，必须计入 $R$，不能成为隐藏输入。这里比较的是由当前任务态确定的函数型记录，以及确定性、固定更新规则下的补充记忆值数，不是读出字母表、算法运行时间或物理空间。若同一任务态可以携带多种历史记忆，须先另定联合状态，不能直接把它当作本节的 $r:X\to R$。有限初态允许集固定为整个 $X$；两种合同均须另行解释怎样实际取得初始记录。

置 $d_q=\max_{y\in Y}|q^{-1}(y)|$。允许式（RA.1602）时，最小补充记忆值数恰为 $d_q$：每条纤维须取不同标签，逐纤维使用同一组 $d_q$ 个标签达到界；单射的 $E_r$ 使 $U=rTE_r^{-1}$ 在实际像上良定义。完整后继同时为 $E_rTE_r^{-1}$，故这里不把补充记忆单独误当完整状态。

这个静态容量结论复用仓内 `DefectGraphMinimumColoring.minimum_repair_labels_eq_chromatic_eq_fiber_diversity`，目标取 $\operatorname{id}_X$。上述共用界面的更新则说明它如何进入当前动态合同；不将最大纤维原理另算为新形式化结果。

### 16.2 自主记忆需要稳定分划，普通着色不足

定义有限图 $G_{T,q}$，顶点为 $X$，且

$$
x\mathrel{\mathcal E_{T,q}}x'
\iff
x\ne x'\ \land\ \exists n\ge0,\quad q(T^nx)=q(T^nx').
\tag{RA.1604}
$$

$T$ 是置换，所以不同来源在这些后继仍然不同。若 $L$ 为 $T$ 的置换阶，$n$ 只需遍历 $0,\ldots,L-1$；这里取的是所有后继中**至少一次碰撞**的并，而不是全部未来读数一致的行为核。

**命题 16.1（自主补充记忆的精确分划条件）。** 一个标签函数 $r$ 满足（RA.1601）、（RA.1603），当且仅当它是 $G_{T,q}$ 的合法着色，而且其核在 $T$ 下稳定：

$$
r(x)=r(x')\Longrightarrow r(Tx)=r(Tx').
\tag{RA.1605}
$$

因此自主记忆最小值是所有满足（RA.1605）的合法着色中最少的颜色数；图的普通色数只给下界。

证明。若自主更新成立，相同记忆沿全部后继仍相同。若它们又在某一步发生界面碰撞，（RA.1601）在该步迫使 $T^nx=T^nx'$，由置换性反推 $x=x'$，矛盾。故同一颜色不含图边，且一步更新直接给（RA.1605）。反之，取 $n=0$ 得联合单射性；核稳定使 $u(r(x))=r(Tx)$ 良定义。其唯一性使用 $R=r[X]$。证毕。

核稳定与商上更新的对应复用 `DynamicsDescent.dynamics_descends_iff`；有限完整行为的最粗稳定细化已有 `DynamicClosureMinimality.dynamic_closure_is_least`。本节额外固定补充记忆的读取权限，故所求是满足联合恢复条件的稳定分划，不是另一个无条件最小行为商。

### 16.3 一个任意大容量差距及着色反例

取素数 $p\ge5$，令 $X=\mathbb Z/p\mathbb Z$、$T(x)=x+1$。令 $q$ 只合并 $0,1$ 为一个值 $*$，其他 $p-2$ 个元素各自保留不同标签。

**命题 16.2（循环源上的两种容量）。** 对这个同一来源、同一读数和同一恢复目标，有

$$
\min|R|_{\rm joint}=2,
\qquad
\chi(G_{T,q})=3,
\qquad
\min|R|_{\rm autonomous}=p.
\tag{RA.1606}
$$

证明。最大读数纤维为 $\{0,1\}$，两值记录 $r(x)=\mathbf1_{x=1}$ 已使联合表示单射，故第一式成立。未来界面碰撞恰发生于来源相差 $\pm1$，所以图是奇循环 $C_p$。奇循环不能二染色，交替两色并给末点第三色即可，证明第二式。

若一个自主记录合并不同的 $i,j$，则由沿循环平移的核稳定性，对每个 $k$ 都有 $r(k)=r(k+j-i)$。非零的 $j-i$ 在素数阶循环群中生成全群，故 $r$ 必为常函数。它不能区分读数同为 $*$ 的 $0,1$，违反联合恢复条件。因此自主记录必须单射；取 $r(x)=x$、$u(x)=x+1$ 达到 $p$。证毕。

这里 $\chi=3$ 与自主最小值 $p$ 的差距说明：不能把任意合格着色直接称为能运行的记忆更新。比如 $p=5$ 时依次给顶点颜色 $(0,1,0,1,2)$ 是合法三染色，但颜色同为一的顶点 $1,3$ 的后继颜色分别为零和二，无法定义只读取颜色的一步更新。补充记忆从两值增到 $p$ 值，来自更新接口的限制；完整实际状态仍只有 $p$ 种，没有增加独立来源信息。

### 16.4 FIB 在同一精度层的严格容量分离

回到 $V_m=(\mathbb Z/m\mathbb Z)^2$、$T(x)=Mx$、$q(x)=\ell x$，其中

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad \ell=(2,3),\qquad m\ge2.
$$

$\det M=-1$ 是模任意 $m$ 的单位，故 $T$ 在整个 $V_m$ 上是置换。观察矩阵
$B=\begin{pmatrix}2&3\\3&5\end{pmatrix}$ 的整数行列式为一，
所以 $(q(x),q(Mx))$ 是 $V_m$ 上的双射；固定第一分量后恰有 $m$ 个第二分量，
故每条 $q$ 纤维有 $m$ 个元素。取

$$
h(x)=\ell M^{-1}x=(1,2)x,
\qquad z(x)=\ell Mx=(3,5)x.
\tag{RA.1607}
$$

两种联合表示 $(h,q)$ 与 $(q,z)$ 都可恢复 $x$，且

$$
h(Tx)=q(x),\qquad z(Tx)=q(x)+z(x),\qquad z=h+q.
\tag{RA.1608}
$$

故允许读取当前 $q$ 的最小补充记忆恰有 $m$ 个值。它是对完整 $m^2$ 态的分量分解，与 §15.6 的整个观察器下界一致。

**命题 16.3（后继碰撞覆盖迫使自主记录完整）。** 若

$$
\forall d\in V_m\setminus\{0\},\quad
\exists n\ge0,\quad \ell M^nd=0,
\tag{RA.1609}
$$

则任何满足（RA.1601）、（RA.1603）的记录均单射，最小自主记忆值数为 $m^2$。

证明。对任意不同的 $x,x'$，将（RA.1609）应用于 $d=x-x'$，得到二者在某一步的相同 $q$。命题16.1迫使它们使用不同记忆值。记录完整 $x$ 并按 $M$ 更新达到界。证毕。

模二时，三行 $\ell M^n$ 依次为 $(0,1),(1,1),(1,0)$；其核覆盖全部非零差向量。模三时，前四行是

$$
(2,0),\quad(0,2),\quad(2,2),\quad(2,1).
\tag{RA.1610}
$$

它们的核是二维三元域中的全部四条直线。因此两种读取合同的最小补充记忆值数分别为

| 模数 | 可以读取当前界面 | 只依赖记忆自主更新 |
| --- | ---: | ---: |
| $m=2$ | $2$ | $4$ |
| $m=3$ | $3$ | $9$ |

这一下界针对任意标签函数，不假定记录是线性的。全部有限分划核对提供独立的小实例检查：四态有15种分划，九态有21147种分划；分别同时检验联合单射和核稳定后，两例都只剩离散分划。有限核对不替代上面的全称证明。

条件（RA.1609）不能省略。模五取

$$
r(a,b)=2a+b\pmod5.
\tag{RA.1611}
$$

则 $r(Mx)=3r(x)$，而 $(q,r)$ 的矩阵行列式是 $-4\equiv1\pmod5$。因此自主补充记忆也只需五个值，等于纤维下界。具体地，非零差向量
$d=(1,3)$ 满足 $Md=3d$、$q(d)=1$，所以 $q(M^nd)=3^n\ne0\pmod5$，
直接违反（RA.1609）。不能由模二、模三推出任意模数都需要 $m^2$ 个自主记忆值。

### 16.5 由实际读数初始化，并在同一来源上运输

式（RA.1607）定义了来源上的函数，还没有把它们交给内部观察者。固定如下取得合同：当前 $q$ 可被精确、无扰动地读取；一次推进确实执行同一个 $M$；这些操作合法，且没有未记录的额外变化。令 $x_t=M^tx_0$、$y_t=q(x_t)$。观察者先保存 $y_0$，推进一次，再读取 $y_1$。此后取

$$
(h_t,y_t)=(y_{t-1},y_t),\qquad t\ge1.
\tag{RA.1612}
$$

**命题 16.4（一次预热后的实际恢复）。** 在上述取得合同下，对每个初态和每个 $t\ge1$，

$$
x_t=
\begin{pmatrix}-3&2\\2&-1\end{pmatrix}
\binom{h_t}{y_t},
\qquad
z_t=h_t+y_t=q(x_{t+1}),
\qquad
(h_{t+1},y_{t+1})=(y_t,h_t+y_t).
\tag{RA.1613}
$$

证明。由 $x_{t-1}=M^{-1}x_t$，有 $(h_t,y_t)^{\mathsf T}=\begin{pmatrix}1&2\\2&3\end{pmatrix}x_t$；所示矩阵是其整数逆，所以对全部 $m\ge2$ 都成立。$M^2=M+I$ 给 $y_{t+1}=y_t+y_{t-1}$。保留推进前已读取的 $y_t$，执行一次 $M$ 后读取 $y_{t+1}$，即实现所示更新；归纳保持等式。证毕。

只取得首个读数时还剩 $m$ 个相容初态，不能把预测值 $z_0$ 当作免费输入。预热后，保存上一读数的补充寄存器有 $m$ 个可能值，当前读数有 $m$ 个可能值，全部 $m^2$ 个联合值都实际实现。这个容量以当前读数可访问为条件；脱离传感器后还要保留该读数或等价的完整解码值，不能把补充寄存器的 $m$ 值当成独立运行的全部容量。持久原始档案、额外策略记忆与检查费用均不在这个稳态补充寄存器下界中。

把操作拆开时，一个明确的充分实现具有状态标签

$$
\mathsf U,\quad\mathsf S_y,\quad\mathsf A_y,\quad
\mathsf R_{h,y},\quad\mathsf P_{h,y},\qquad h,y\in\mathbb Z/m\mathbb Z.
\tag{RA.1613a}
$$

初始化按 $\mathsf U\xrightarrow{\mathrm{read}\ y}\mathsf S_y
\xrightarrow{M}\mathsf A_y\xrightarrow{\mathrm{read}\ v}\mathsf R_{y,v}$ 执行；
随后按 $\mathsf R_{h,y}\xrightarrow{M}\mathsf P_{h,y}
\xrightarrow{\mathrm{read}\ v}\mathsf R_{y,v}$ 维护。
仅凭已取得的读数，$\mathsf S$ 与 $\mathsf A$ 尚不保证恢复整个来源；协议的准确恢复保证从 $\mathsf R$ 接口开始。
$\mathsf P$ 保存已经取得的旧读数对，此时当前来源由 $MD(h,y)$ 恢复，其中
$D(h,y)=(2y-3h,2h-y)$；预测 $h+y$ 仍与下一次实际取得的 $v$ 分开。
这共有 $1+2m+2m^2$ 个标签，是把已锁存读数和操作阶段一起计入的充分实现，
不是总硬件或微步骤存储的最小性结论。

预热接口 $t=1$ 也可恢复原初任务态：

$$
x_0=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}\binom{y_0}{y_1}.
\tag{RA.1613b}
$$

这里的矩阵是 $B$ 的整数逆，因而同样适用于每个模数 $m\ge2$。
但（RA.1613）在以后各接口恢复的是当前 $x_t$。
若另知 $t$，可由 $x_0=M^{-t}D(h_t,y_t)$ 恢复原初态；
若要求永久恢复同一个 $x_0$，所需的推进计数（可取模 $M$ 的置换阶）或原初档案
必须计入重新声明的联合状态，不能作为隐藏输入。
例如模二时，初态 $(1,0)$ 在 $t=1$ 与初态 $(1,1)$ 在 $t=2$
具有相同当前态 $(0,1)$ 和相同读数对 $(h_t,y_t)=(0,1)$，但原初态不同。

“上一读数”指本次来源推进之前的读数，不指任意上一次传感器调用。
在同一个来源态上重复读取时不替换 $h$。例如模二的 $x=(1,0)$ 当前读数为零，
推进后读数为一；未推进而读到两次零，不能据此用 $D(0,0)$ 恢复 $x$。
若推进只有部分合法域 $D_M$，则从单读数 $y$ 保证能启动，需要
$q^{-1}(y)\subseteq D_M$，或对声明的初态集作相应交集；不能免费假定未知来源已获许可。

$(h,q)$ 和 $(q,z)$ 的运输为

$$
(h,q)\longmapsto(q,h+q),\qquad
(q,z)\longmapsto(z-q,q).
\tag{RA.1614}
$$

它们共享同一来源及当前界面 $q$；单独的 $h$ 与 $z$ 不能互相恢复。例如 $x=0$ 与 $x'=(2,-1)$ 满足 $h(x)=h(x')=0$，却分别有 $z(x)=0,z(x')=1$；反向取 $x''=(-5,3)$，有 $z(x'')=z(0)=0$，而 $h(x'')=1\ne0=h(0)$。这些见证模任意 $m\ge2$ 都成立。删除运输所需的共同界面，会丢失这一区别。

因此，在上述取得合同和预热后的规定接口上，二维任务态 $(a,b)$、相邻读数对 $(h,q)$ 与含当前界面的表示 $(q,z)$ 可以在同一有限源上两两精确恢复。单独的界面或补充记录一般不足以恢复整个任务态。换成扰动测量、未知后继、噪声、部分许可或额外控制器后，须重新核对第14节的联合核下降及§15.3的选择器因子化；不能仅凭同形矩阵沿用本节合同。

### 16.6 来源与仍未解决的接口

静态最大纤维容量、商上的稳定更新及完整行为商复用上述仓内声明；FIB 的替换、相邻读数恢复和自治精度塔分别来自 FIB 卷 §3–5、§42–43。本节把它们接到同一精度层的两种读取权限，给出稳定着色条件、循环反例、模二/模三容量分离和实际初始化协议。它们是理论正文中的推导，不宣称新增 Lean 核验，也不以有限分划枚举支持未处理的模数。

实际取得也可写成同源候选集更新。在已取得 $y_0$ 并确认一次推进后，新读数 $y_1$ 给出

$$
M(q^{-1}(y_0))\cap q^{-1}(y_1)=\{D(y_0,y_1)\}.
\tag{RA.1615}
$$

这与 S. E. Tuna 的 [*Deadbeat observer: construction via sets*, arXiv:1006.2713v3](https://arxiv.org/abs/1006.2713v3)
所用的有限步相容集收缩相接。该文 §4 的 Assumptions 1–2
给出有限深度相容集为单点或空集，以及前推相容集的成员一致性条件；
§5 的 Theorem 3 在其原有设定中使用这些条件。
在本节的有限环模型中，置 $N=\ker q$，相应集合为 $x+N$、$x+MN$。
$N$ 由 $(-3,2)$ 生成，$MN$ 由 $(2,-1)$ 生成，而 $q(2,-1)=1$，
故 $q$ 限制在 $MN$ 上为双射，$N\cap MN=\{0\}$。
于是 $(x+N)\cap(x+MN)=\{x\}$，且对任意读数 $y$，
$(x+MN)\cap q^{-1}(y)$ 都为单点。
若 $w\in x+MN$，则 $w+MN=x+MN$，直接给出前推陪集的成员一致性。
这里复用其相容集构造来表达取得过程；该文的实数空间定理是方法来源，
本节有限环的时间对齐、模数结论和记录容量均由上述直接代数证明支持。

一般 $m$ 下自主补充记忆的精确最小值，尤其不满足（RA.1609）且没有已给自主充分坐标时的最优稳定分划，仍需另求。永久原初恢复所需的扩展状态与阶段实现的最小总存储也未由本节确定。随机记录、近似恢复、噪声累积和取得/更新的计算成本同样不由这些状态数解决。这里的坐标名称只说明给定任务的表达与运输，不宣称已经推出物理时空或完成空间、时间、边界与记忆普遍互相恢复的目标。

## 追加锚（本行以下为增补区）


## 17. 模十三的最小自主补充记忆与取得边界

本节补足 §16 在模十三上的精确最小值。固定 $V=\mathbb F_{13}^2$、
$M=\begin{pmatrix}0&1\\1&1\end{pmatrix}$、$q(a,b)=2a+3b$，
所有运算均在 $\mathbb F_{13}$ 中。允许接口态是整个 $V$，恢复目标是当前模组成态，
不是完整树语法或永久原初态。补充记录是确定性的当前状态函数
$r:V\to R=r[V]$，要求

$$
x\longmapsto(q(x),r(x))\ \text{单射},\qquad
r(Mx)=u(r(x)).
\tag{RA.1701}
$$

自主更新 $u$ 只能读取 $r$；当前 $q$、时刻、轨道相位和控制器若参与更新，
就必须计入记录，不能作为暗中输入。允许读取界面的另一合同则是
$r(Mx)=U(q(x),r(x))$。以下比较这两种合同中的补充记录值数，
不把补充记录单独当作完整观察者，也不赠送初始记录。

### 17.1 完整来源上的三种精确容量

**命题 17.1（联合读取、自主记录与自主线性记录）。** 在上述整个 $V$ 和当前态恢复合同下，

$$
\min |R|_{\rm joint}=13,\qquad
\min |R|_{\rm autonomous}=20,\qquad
\min |R|_{\rm autonomous,\ linear}=169.
\tag{RA.1702}
$$

第三项要求 $r$ 是取值于某个 $\mathbb F_{13}$ 向量空间的线性映射，
但不预先要求 $u$ 线性。第二项允许任意标签函数。

先证明第一项与第三项。每条 $q$ 纤维有13个来源，联合单射性迫使至少13个记录值。
取 $h(a,b)=a+2b$，则 $(q,h)$ 的矩阵行列式为 $2\cdot2-3\cdot1=1$，
且 $h(Mx)=q(x)$，所以13值达到联合读取的界。

若 $r$ 线性且自主，则 $u(0)=0$，从 $r(x)=0$ 得 $r(Mx)=0$，
故 $\ker r$ 为 $M$ 不变子空间。特征多项式为 $t^2-t-1$，判别式是5；
模十三的平方值为

$$
\{0,1,3,4,9,10,12\},\qquad 5\ \text{不在其中}.
\tag{RA.1703}
$$

因此特征多项式没有域内根，$M$ 没有一维不变子空间：若某条一维子空间不变，
其非零生成元就给出域内特征值。零秩记录又不能区分同一 $q$ 纤维中的13态。
所以线性自主记录只能秩二，实际像有 $13^2=169$ 个值；取 $r(x)=x$ 达到。
任意自主记录的20值构造及下界如下。

### 17.2 六条非零轨道与零读数的位置

直接矩阵乘法给出

$$
M^4=\begin{pmatrix}2&3\\3&5\end{pmatrix},\qquad
M^7=8I,\qquad M^{14}=-I,\qquad M^{28}=I,\qquad
\det(M^4-I)=-5\ne0.
\tag{RA.1704}
$$

每个非零来源的轨道长恰为28。其最小周期整除28；周期1、2、4都使来源被
$M^4$ 固定，与 $M^4-I$ 可逆冲突；周期7、14分别使 $8x=x$、$-x=x$，
也只允许 $x=0$。

取六个代表元，并记其28态轨道为 $\mathcal O(c_i)$、$\mathcal O(d_i)$：

$$
\begin{aligned}
c_0&=(0,1),&c_1&=(0,2),&c_2&=(0,4),\\
d_0&=(1,3),&d_1&=(1,4),&d_2&=(1,5).
\end{aligned}
\tag{RA.1705}
$$

二次式 $Q(a,b)=a^2+ab-b^2$ 满足 $Q(Mx)=-Q(x)$。
这六个代表的 $\{Q,-Q\}$ 依次为
$\{\pm1\},\{\pm4\},\{\pm3\},\{\pm5\},\{\pm2\},\{\pm6\}$，互不相同。
所以六条轨道不交，共含 $6\cdot28=168$ 个非零来源，另有零固定点。
置

$$
C=\bigcup_{i=0}^2\mathcal O(c_i),\qquad
U=\bigcup_{i=0}^2\mathcal O(d_i),\qquad |C|=|U|=84.
\tag{RA.1706}
$$

它们是不交的 $M$ 稳定集合。又 $\ker q=\mathbb F_{13}(2,3)$，
而 $M^3c_0=(2,3)$。标量8的乘法阶为四，由 $M^7=8I$，
每条 $c_i$ 轨道在索引

$$
n=3,10,17,24\pmod{28}
\tag{RA.1707}
$$

各有一个零读数。三条不交轨道给出12个不同的非零核向量，
已穷尽 $\ker q\setminus\{0\}$；所以这些就是各 $c_i$ 轨道的全部零读数位置，
而 $U$ 上的读数从不为零。

### 17.3 二十类的几何构造与自主更新

按以下次序列出 $B$ 的七个元素 $b_0,\ldots,b_6$，并固定剩余斜率集 $S$：

$$
\begin{aligned}
B&=\{(0,1),(3,5),(8,8),(1,12),(12,11),(5,0),(10,2)\},\\
S&=\{3,4,5,7,9,10,11\}.
\end{aligned}
\tag{RA.1708}
$$

取如下来源类，以类名作为记录标签：

$$
Z=\{0\},\qquad A_c=cB\quad(c\in\mathbb F_{13}^{\times}),\qquad
L_m^*=\{(a,ma):a\in\mathbb F_{13}^{\times}\}\quad(m\in S).
\tag{RA.1709}
$$

这里有 $1+12+7=20$ 类。说明它们确为分划：二维域上非零向量的方向
由斜率 $m\in\mathbb F_{13}$ 或竖直方向 $\infty$ 唯一指定，共14个方向。
$B$ 的斜率按所列次序为

$$
(\infty,6,1,12,2,0,8).
\tag{RA.1710}
$$

因此 $B$ 恰在七个不同方向上各取一个非零向量。
这些方向上的任意非零向量唯一写成 $cb_j$；若 $cb_j=c'b_k$，
先由方向得 $j=k$，再得 $c=c'$。故12个 $A_c$ 不交，覆盖这七条线的全部非零点。
其余七个方向恰是 $S$，由七个 $L_m^*$ 不交覆盖；加上 $Z$ 即为全部169态。

每类中的来源可由当前 $q$ 区分。对 $B$，读数按次序为

$$
(q(b_0),\ldots,q(b_6))=(3,8,1,12,5,10,0),
\tag{RA.1711}
$$

七值互异，所以每个 $cB$ 的七个读数也互异。
在 $L_m^*$ 上，$q(a,ma)=(2+3m)a$；其系数只在 $m=8$ 时为零，
而 $8\notin S$。所以每个 $L_m^*$ 的十二个读数恰为全部非零域元素。
$Z$ 只有一个来源。因此 $x\mapsto(q(x),r(x))$ 单射。

更新同样可由短式直接验证：

$$
Mb_j=5b_{j+2\bmod7},\qquad M^4b_j=b_{j+1\bmod7},\qquad
MB=5B,\quad M^4B=B.
\tag{RA.1712}
$$

这些等式由七个已列向量逐项相乘得到；第二式也由第一式和 $5^4=1$ 得到。
故 $M(A_c)=A_{5c}$。对 $m\in S$，因 $m\ne0$，有
$M(a,ma)=(ma,(1+m)a)$，其新斜率为 $1+m^{-1}$。完整记录更新为

$$
u(Z)=Z,\qquad u(A_c)=A_{5c},\qquad
u(L_m^*)=L_{1+m^{-1}}^*.
\tag{RA.1713}
$$

斜率更新的次序是

$$
3\longmapsto10\longmapsto5\longmapsto9\longmapsto4
\longmapsto11\longmapsto7\longmapsto3.
\tag{RA.1714}
$$

所以更新留在已定义标签中。$A_c$ 的乘五更新分成三个4循环，
$L_m^*$ 构成一个7循环，$Z$ 固定。由这些逐类等式，记录核在 $M$ 下稳定，
且 $rM=ur$；实现更新只需已有类名，不读取 $q$、来源坐标或相位。
这给出20值自主补充记录。

### 17.4 任意自主记录的二十值下界

取任意满足（RA.1701）的 $r$，不假定其线性、类形状或轨道相位对齐。
因为 $M$ 是来源置换且 $R=r[V]$，每个标签 $r(x)$ 都有前驱
$r(M^{-1}x)$；有限集上的 $u$ 因而是置换。
一条28态来源轨道映到一条 $u$ 循环，设其长度为 $e$。
由 $u^{28}(r(x))=r(x)$，$e\mid28$；
在这条来源轨道中，每个该循环标签恰出现 $28/e$ 次。
同一标签里的来源必须有不同 $q$，故最多13态，排除 $e=1,2$。
特别地，$r(0)$ 是固定标签，而任何非零来源都不能使用固定标签，
所以 $r^{-1}(r(0))=\{0\}$。

若记录使用任何28循环，连同这个零固定标签就至少需要29值，已超过20。
以下只须处理没有28循环的情形，此时非零来源可用的周期仅为4、7、14。
每条 $c_i$ 轨道都不能用7或14周期：索引3、17相差14，
是两个不同且读数同为零的来源，但这两种记录周期都会合并它们。
所以三条 $c_i$ 轨道各映到4循环。

它们不能共享同一个4循环。若两条来源轨道的标签循环相交，
置换循环便完全相同，与起始标签的相位如何对齐无关；
此时每个标签含两条来源轨道各七态，共14态，超过13种读数。
因此 $C$ 至少占据三个不交4循环，共12个标签。
任何 $U$ 轨道也不能接入这些循环：一旦共用标签，其记录周期就是四，
每个标签又会增加七态，与已在该标签中的七个 $C$ 来源冲突。

所以 $U$ 的84态全部使用这12标签及零标签之外的标签。
又 $q$ 在 $U$ 上不取零，同一标签至多容纳12个 $U$ 来源，
不论不同 $U$ 轨道是否共用循环，都至少再需
$\lceil84/12\rceil=7$ 个标签。加上零标签，

$$
|R|\ge12+7+1=20.
\tag{RA.1715}
$$

这一下界是对全部合法 $r,u$ 的周期与容量证明，不靠穷举全部分划。
结合 §17.3 的构造，命题17.1证毕。

### 17.5 单条 $\alpha$ 后继来源的四值边界

若只取 $\rho^n(\alpha)$ 的模组成态，则来源是
$O_\alpha=\{M^n(1,0):n\ge0\}$，只有28态。
因 $M(1,0)=c_0$，它与 $\mathcal O(c_0)$ 是同一条轨道。
此处仍把整条轨道视为允许接口态，未额外提供已知时刻或相位。

（RA.1707）在该轨道上给出四个零读数，所以最大读数纤维至少为四。
又 $(1,0)=8b_5$，乘五更新使这条轨道使用 $A_8,A_1,A_5,A_{12}$ 四类。
它们共含28态，因而恰是整条轨道；每类上的 $q$ 单射，
所以任意读数在轨道上最多出现四次。
最大纤维因而恰为四，联合读取补充记录至少四值。
自主四值记录可明确写为

$$
r_\alpha(M^n(1,0))=n\bmod4,\qquad
u_\alpha(k)=k+1\bmod4,\qquad
\min|R|_{\rm joint,O_\alpha}
=\min|R|_{\rm autonomous,O_\alpha}=4.
\tag{RA.1716}
$$

轨道相位 $n\bmod28$ 由当前态唯一确定，且 $4\mid28$，所以该式是良定义的
当前态函数；同一标签的来源属于同一个 $A_c$，故 $(q,r_\alpha)$ 单射。
相位只用于描述此函数，不作为更新器的额外读权限；装载后只按四标签循环更新。
单独这四值仍不能恢复28态。

允许任意 $\alpha,\beta$ 配对的源域则不同。按 §14.4 的组成合同，
每对模十三余数都有非负叶计数的非空树提升，实际像才是整个 $V$；
这还包括模组成零的非空树。即使从单种子 $\alpha$ 借 $\rho(\alpha)=\beta$
取得第二叶，再允许配对，也已改变为这种更大的源域。
所以四值结论量化单条后继轨道，十三、二十、一百六十九量化全部模组成态，
二者不能互换，更不能由种子数推出完整观察者容量。

### 17.6 共同实现、实际装载与未决范围

构造中的 $C$ 恰是12个 $A_c$ 类的并。事实上
$B=\{M^{4j}c_0:0\le j<7\}$，
而标量8生成四阶子群 $H=\{1,5,8,12\}$，三个陪集
$H,2H,4H$ 分割 $\mathbb F_{13}^{\times}$。
用 $M^7=8I$ 和 $M^4B=B$，
$\mathcal O(sc_0)=\bigcup_{h\in H}shB$（$s=1,2,4$）：
每项都来自同一来源轨道，四个不交七态类已给出全部28态。
因此 $U$ 恰是七个 $L_m^*$ 类的并。
联合表示的实际像共有
$12\cdot7+7\cdot12+1=169$ 种，
并非13种读数与20种标签的全部自由组合。
单独一个 $A_c$ 标签仍对应七态，一个 $L_m^*$ 标签仍对应十二态；
恢复当前来源需要共同的当前界面 $q$。

上述 $r$ 是来源坐标，不能据其存在免费初始化观察者。
在 §16.5 的取得合同下——精确无扰动读取、确认同一个 $M$ 的一次合法推进、
无未记录的额外变化——先实际读取 $y_0=q(x_0)$，保存它并推进，
再实际读取 $y_1=q(x_1)$，其中 $x_1=Mx_0$。于是

$$
x_1=(2y_1-3y_0,\ 2y_0-y_1),\qquad r_1=r(x_1).
\tag{RA.1717}
$$

把取得的当前态按（RA.1709）归类后，才装载相应标签。
其后每次确认来源执行一次 $M$，记录执行一次固定更新（RA.1713），
归纳保持 $r_t=r(x_t)$；解码时仍须实际访问当前 $q(x_t)$。
标签更新本身无需读取该界面，不等于观察者脱离传感器也能恢复当前态。

只取得首个 $q$ 时仍有13个相容来源，它们需要不同记录，
故仅凭该首读数不能保证装载正确标签。
没有上述实际取得权限时，不能用预计算的来源坐标、预测的第二读数或隐藏相位
代替所缺输入。装载所需的临时读数、解码工作空间、操作阶段、控制器和执行成本，
须在相应实现合同中另计；20只是已经装载并在规定接口维护的补充记录值数，
不是这些总成本的最小值，也不直接等于物理位数。
若目标改为永久恢复同一个 $x_0$，则计数或原初档案仍须按 §16.5 另行计入。

精确有限算术核对覆盖全部169态：零固定点与六条28轨道不交穷尽；
$C,U$ 各84态，非零零读数在 $C$ 中恰12态、在 $U$ 中零态；
20类的大小为一类1态、十二类7态、七类12态，逐类读数单射并满足完整更新；
单 $\alpha$ 轨道的最大读数纤维为四，四标签联合表示区分全部28态；
（RA.1703）、（RA.1704）及两次实际读数的解码常数均一致。
这些有限核对支撑所列算术，任意记录的下界仍由 §17.4 的纸面全称证明给出。
本节不宣称 Lean 核验或原创性。一般模数的最优稳定分划、实际取得与更新的
最小总成本，以及最小关系结构下空间、时间、边界与记忆普遍可恢复的条件，仍未解决。

## 追加锚（本行以下为增补区）


## 18. 允许原子嫁接后的自主记忆：稳定分划收紧为不变子空间商

本节沿用 §16 的当前态恢复合同，扩大 §17 的允许操作。生成种子数、补充记录值数与完整观察器状态数是三个不同量；§15.7 的单种子生成结论不决定后两者。

### 18.1 全域任务商与更新权限

**定义 18.1（原子嫁接合同）。** 固定素数 $p$，取有限非空有序二叉树 $t::=\alpha\mid\beta\mid\langle t,t\rangle$；
叶替换为 $\rho(\alpha)=\beta$、$\rho(\beta)=\langle\beta,\alpha\rangle$，并在配对上分配。
组成满足 $c(\alpha)=(1,0)$、$c(\beta)=(0,1)$、$c(\langle s,t\rangle)=c(s)+c(t)$。
任务态仅为 $x=c(t)\bmod p\in V=\mathbb F_p^2$，不要求恢复树形或整数叶数。于是

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
q(a,b)=2a+3b,\qquad G(x)=x+\alpha,
\quad \alpha=(1,0),\ \beta=(0,1).
$$

这里 $G$ 由实际操作 $g_\alpha(t)=\langle t,\alpha\rangle$ 实现。每个 $V$ 中的态都有实际非空树代表：取非负剩余代表的叶数并任意配对；零对可用 $p$ 个 $\alpha$ 叶实现。
初态域是整个 $V$，不是仅有 $\{M^n\alpha:n\ge0\}$ 的轨道。

记录为确定函数 $r:V\to R=r[V]$，要求存在固定函数 $u,v:R\to R$，使

$$
(q,r)\text{ 单射},\qquad r(Mx)=u(r(x)),\qquad r(Gx)=v(r(x)).
\tag{RA.1801}
$$

解码器可以读取当前 $q$，两个自主更新器只能读取 $r$；操作名称已声明，时刻、旧读数、额外控制状态均不是免费输入。
记录值数的最小化不预先赠送初始 $r(x)$；实际取得在 §18.7 另述。

### 18.2 正向实际词与核的强制形状

**定理 18.2（一个原子嫁接已强制平移同余）。** 不假定 $r,u,v$ 线性。只要两个自主更新成立，便存在唯一 $\mathbb F_p$ 子空间 $W\le V$，使

$$
r(x)=r(y)\iff x-y\in W,\qquad MW=W.
\tag{RA.1802}
$$

证明。记 $E$ 为 $r$ 的相等核。$M$ 可逆且 $V$ 有限，故有整数 $L\ge2$ 使 $M^L=I$；例如取 $L=(p^2)!$。
又有 $G^p=I$。核对 $M,G$ 的正向稳定性因而也给逆向稳定性：
$M^{-1}$ 在任务商上的作用由 $\rho^{L-1}$ 实现，$G^{-1}$ 由 $g_\alpha^{p-1}$ 实现。
等价地，$u^L=\operatorname{id}_R$、$v^p=\operatorname{id}_R$，所以这些非线性商更新也是置换。

按从左到右的执行顺序，实际词 $\rho^{L-1},g_\alpha,\rho$ 在 $V$ 上给出
$x\mapsto M(M^{L-1}x+\alpha)=x+\beta$。
更一般地，对 $0\le A,B<p$，词

$$
g_\alpha^A,\ \rho^{L-1},\ g_\alpha^B,\ \rho
\quad\text{在 }V\text{ 上实现 }x\mapsto x+A\alpha+B\beta.
$$

零次操作可省去；即使 $A=B=0$，留下的 $\rho^L$ 仍是非空正向词。
负系数取模 $p$ 的非负代表，所以每个平移及其逆都由有限非空正向实际词实现。
全过程仅替换或配对非空树；$\rho^L$ 只在任务商上为恒等，不要求原树替换满射、可逆或周期。
这些词还使任一初始剩余可达整个 $V$，没有声称能取得任意指定树形。

故对每个 $z\in V$，有 $xEy\iff(x+z)E(y+z)$。
置 $W=\{w:w\mathrel E0\}$，便有 $xEy\iff(x-y)\mathrel E0$。
若 $w,w'\in W$，平移与传递性给 $w+w'\mathrel E w'\mathrel E0$；平移 $w\mathrel E0$ 并用对称性得 $-w\mathrel E0$。
于是 $W$ 是加法子群，在素域上又因反复加法而是 $\mathbb F_p$ 子空间。
$M$ 及其逆保持 $E$ 且固定零，故 $MW=W$。$W$ 是零类，因而唯一。
这是有限阿贝尔群同余的经典陪集论证；此处直接证明，不另加文献假设。证毕。

### 18.3 所有素数上的准确自主容量

**定理 18.3（全域准确最小值）。** 在定义 18.1 的合同下，最小记录值数为

$$
C_p=\min_{\substack{W\le V,\ MW=W\\W\cap\ker q=\{0\}}}|V/W|
=\begin{cases}
p^2,&t^2-t-1\text{ 在 }\mathbb F_p\text{ 上不可约},\\
p,&t^2-t-1\text{ 在 }\mathbb F_p\text{ 上有根}.
\end{cases}
\tag{RA.1803}
$$

证明。由定理 18.2，每个记录的类恰为 $W$ 的陪集，故 $|R|=|V/W|$。
联合恢复等价于 $W\cap\ker q=\{0\}$：非零交向量 $w$ 使 $0,w$ 的两项读数都相同；反之，两项相同使差属于该交。
对任意合格 $W$，取 $r(x)=x+W$，更新为
$u(x+W)=Mx+W$、$v(x+W)=x+\alpha+W$，即达到对应类数。

行向量 $q$ 非零，且观察矩阵

$$
Q=\begin{pmatrix}q\\qM\end{pmatrix}
=\begin{pmatrix}2&3\\3&5\end{pmatrix},\qquad \det Q=1.
\tag{RA.1804}
$$

所以每条 $q$ 纤维有 $p$ 个态，任何联合恢复记录至少有 $p$ 值。
全空间 $W=V$ 不合格；零空间合格。一条 $M$ 不变直线若落在 $\ker q$，则 $qM$ 也在其上为零，与 $Q$ 可逆矛盾。
故每条不变直线都合格，其交 $\ker q$ 恰为零。
二维空间的不变直线存在，当且仅当特征多项式 $t^2-t-1$ 有域内根。
具体地，垂直线不稳定；其余线写成 $\mathbb F_p(1,\lambda)$，稳定条件恰为 $\lambda^2=\lambda+1$。
无根时仅有零空间与全空间可不变，给 $p^2$；有根时一条直线给 $p$，达到纤维下界。

有根时还可取标量记录

$$
r_\lambda(a,b)=b-\lambda a,\qquad
u(s)=(1-\lambda)s,\qquad v(s)=s-\lambda.
\tag{RA.1805}
$$

代入 $\lambda^2-\lambda=1$ 即验证更新，其核正是上述直线。
模二时多项式在 $0,1$ 均非零，所以 $C_2=4$。
模五时为 $(t-3)^2$，唯一不变线为 $\mathbb F_5(1,3)$；取 $r=2a+b$，有 $u(s)=3s$、$v(s)=s+2$，故 $C_5=5$。
对奇素数 $p\ne5$，判别式为 $5$，所以 $5$ 为平方时取 $p$，为非平方时取 $p^2$；重根情形已由模五单独处理。证毕。

### 18.4 可组合配对没有再抬高此下界

**命题 18.4（二元配对与一原子嫁接的容量等价）。** 保留 $M$ 的自主更新，若另要求
$r(x+y)=\bar\mu(r(x),r(y))$ 对全部 $x,y\in V$ 成立，则可恢复记录的准确最小值仍为 $C_p$。

证明。固定第二项为实际树 $\alpha$，令 $v(s)=\bar\mu(s,r(\alpha))$，便得到定义 18.1 的固定嫁接更新，故定理 18.3 给下界。
反向，每个该定理的陪集记录都有良定义的 $\bar\mu(x+W,y+W)=x+y+W$，给相同上界。
每个任务态由非空树实现，任意两代表的配对仍是合法非空树，包括表示零剩余的树。
下界只用已许可的一原子嫁接，不依赖受限轨道中两份任意输入能够独立取得；另列全部固定平移也不提高容量，因为 §18.2 已用正向词实现它们。证毕。

### 18.5 模十三的严格变化与具体嫁接反例

**命题 18.5（模十三的二十类不能沿用）。** 模十三非零平方为 $\{1,3,4,9,10,12\}$，不含 $5$。
故 $C_{13}=169$，自主记录必须单射。§17 的 $M$ 单独二十类记录 $r_{17}$ 不满足原子嫁接更新。

证明。前半由定理 18.3。对后半，沿用 §17 的 $A_c=cB$ 与 $L_m^*$，取

$$
x=(0,1),\quad y=(3,5)\in A_1,\qquad
Gx=(1,1)=5(8,8)\in A_5,\quad
Gy=(4,5)\in L_{11}^*.
\tag{RA.1806}
$$

因为 $(8,8)\in B$ 且 $11\cdot4\equiv5\pmod {13}$，嫁接后两态在不同类。
同一旧记录 $A_1$ 无法经一个确定 $v$ 同时更新到 $A_5$ 与 $L_{11}^*$。
两初态分别由 $\beta$ 和含三个 $\alpha$、五个 $\beta$ 的树实现，两个后态由各自接入一叶 $\alpha$ 实现。
以 §17 的 $M$ 单独二十类最优构造为基准，固定原子嫁接将准确最小值提高到 $169$；上述反例直接说明旧构造的更新障碍。证毕。

### 18.6 共用当前读数与完整状态的区别

**命题 18.6（允许更新器读取 $q$ 时仍只需 $p$ 值）。** 若将两个自主更新改为可读取当前 $(q,r)$ 的更新，即使同时允许配对，最小补充记录值数仍为 $p$；完整恢复表示的实际联合像则有 $p^2$ 态。

证明。取 $z(x)=qMx=3a+5b$。由（RA.1804），$(q,z)$ 恰为 $V$ 到 $\mathbb F_p^2$ 的双射，并有

$$
z(Mx)=q(x)+z(x),\qquad z(Gx)=z(x)+3,\qquad
z(x+y)=z(x)+z(y).
\tag{RA.1807}
$$

相应当前界面更新为 $q(Mx)=z(x)$、$q(Gx)=q(x)+2$ 与 $q(x+y)=q(x)+q(y)$。
这给 $p$ 值充分记录；每条 $q$ 纤维的 $p$ 态给下界。任意完整恢复表示必须单射，故实际像大小始终为 $|V|=p^2$。
对任何满足联合恢复的 $r$，$(q,r)[V]$ 都恰有 $p^2$ 态，不能把边缘值数的乘积 $p|R|$ 当成联合像大小。
脱离当前界面独立运行时，完整机器须自己保留足够信息；本命题的 $p$ 值仅是共用界面条件下的补充容量。证毕。

FIB 卷 §§130–131 对固定嫁接研究的是输出 $\gcd(qx,H)$ 的完整自主行为机器；原子嫁接给全组成商 $H^2$，并已用实际正向词证明分离。
本节另固定素数、精确恢复目标与可供解码的外部 $q$，最小化补充 $r$；有不变线时 $r$ 只需 $p$ 值，完整联合像仍为 $p^2$，与上述完整机器计数相容。这里不重报仿射闭包或经典同余论证为原创结果。

### 18.7 实际取得与结论的适用边界

**命题 18.7（两次同源读数取得当前记录）。** 若允许精确无扰动读取当前 $q$，两次读取之间实际执行一次已许可的 $\rho$，且没有其他未知操作，令 $y_0=q(x_0)$、$y_1=q(Mx_0)$。则

$$
x_0=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}\binom{y_0}{y_1},\qquad
x_1=Mx_0=\begin{pmatrix}-3&2\\2&-1\end{pmatrix}\binom{y_0}{y_1}.
\tag{RA.1808}
$$

证明。第一式是（RA.1804）的逆，第二式左乘 $M$，均是模 $p$ 恒等式。
故在第二读数接口可计算并置入任一上述 $r(x_1)$，再按其已证明的更新规则维护；$M$ 是任务商置换，预热后的当前态域仍是整个 $V$。证毕。

仅取得 $y_0$ 时仍有 $p$ 个相容态，不能从该读数独自生成满足联合恢复的 $r$。
此取得协议需锁存首读数并区分读取、推进等阶段；这些若作为内部状态存在就须计入，稳态记录下界不是微步骤总存储的最小值。
永久恢复同一原初态还须保存初态或已执行变换的信息，不能把时刻或操作历史隐入更新器。
本节只分类全域有限素数任务商的记录合同；复合模数、受限取得、噪声及空间、时间、边界与记忆的一般恢复条件仍不由此决定。

## 追加锚（本行以下为增补区）


## 19. 复合模数的自主记录与分歧素数五

本节把 §18 的固定素数合同放到任意复合模数。状态仍是实际非空有序二叉树的叶计数在模 $m$ 下的像；记录只保存可达的标签，不把标签数改写成位数、完整状态数或取得控制器的内部记忆。以下固定 $m\ge2$，并令

$$
V_m=(\mathbb Z/m\mathbb Z)^2,\qquad
M(a,b)=(b,a+b),\qquad
G(a,b)=(a+1,b),\qquad
q(a,b)=2a+3b .
\tag{RA.1901}
$$

这里 $M$ 是实际替换操作 $\rho$ 的状态作用，$G$ 是把一片 $\alpha$ 接到实际树上的操作。树语法为 $t::=\alpha\mid\beta\mid\langle t,t\rangle$，组成映射为 $c(\alpha)=(1,0)$、$c(\beta)=(0,1)$、$c(\langle s,t\rangle)=c(s)+c(t)$，均在 $V_m$ 中计算。 任意 $(a,b)$ 取 $0\le a,b<m$ 的剩余代表，由相应数量的两种叶子任意二叉配对即可得到非空树；$(0,0)$ 用 $m$ 片 $\alpha$ 表示。

**定义 19.1（复合模数记录合同）。** 记录是任意确定函数
$r:V_m\to R=r[V_m]$，其中存在固定的 $u,v:R\to R$ 使

$$
(q,r)\text{ 为单射},\qquad
r(Mx)=u(r(x)),\qquad r(Gx)=v(r(x)).
\tag{RA.1902}
$$

$u,v$ 只读已有记录和已知操作名；$q$ 只给解码器。记录标签不是完整态、树形、叶数整数或额外时钟。容量定义为正确初始化后实际可达标签的数量 $|R|$。

### 19.1 正向词强制出平移同余

**定理 19.2（任意非线性记录的陪集形状）。** 任何满足（RA.1902）的记录都有唯一加法子群 $W\le V_m$，满足

$$
r(x)=r(y)\Longleftrightarrow x-y\in W,\qquad
MW=W,\qquad W\cap\ker q=\{0\},
\tag{RA.1903}
$$

且 $|R|=m^2/|W|$。反过来每个满足这些条件的 $W$ 都给出一个合同记录。

**证明。**
$M$ 是有限集合上的置换，故存在 $L\ge1$ 使 $M^L=I$；$G^m=I$。
由交织等式，$u^L$ 与 $v^m$ 在 $R$ 上为恒等，因而 $u,v$ 都是置换。其逆作用由正向词 $M^{L-1}$、$G^{m-1}$ 实现；这只是在状态商上取逆，并不声称实际树替换可逆。 按执行顺序先做 $M^{L-1}$，再做 $G$，再做 $M$，所得状态为

$$
M\bigl(M^{L-1}x+(1,0)\bigr)=x+(0,1).
\tag{RA.1904}
$$

与 $G$ 一起，重复这些有限正向词就得到任意 $A(1,0)+B(0,1)$ 的平移，其中 $A,B$ 取模 $m$ 的非负代表。即使系数为零，也可保留正向词 $M^L$；每个词都作用在同一棵当时的非空树上。于是等价关系 $x\sim y\iff r(x)=r(y)$ 对每个平移都双向不变。 令 $W=\{w:w\sim0\}$。平移不变性给出 $x\sim y\iff x-y\in W$。若 $w,w'\in W$，则 $w+w'\sim w'\sim0$；由对称性和平移，$-w\sim0$。故 $W$ 是加法子群。 $M$ 固定零且其正向作用和逆作用都保持等价关系，所以 $MW=W$。 联合单射恰等于 $W\cap\ker q=\{0\}$：交中非零元给出两个相同的 $(q,r)$，反之相同的两项读数的差在该交中。等价类是 $W$ 的陪集，所以 $|R|=|V_m/W|=m^2/|W|$。 反向地，给定这样的 $W$，令 $r(x)=x+W$，并令 $u(x+W)=Mx+W$、$v(x+W)=Gx+W$；稳定性保证良定义，交为零保证联合解码。证毕。 这里的可达性来自实际来源：每个模态都有非空树代表，且上述平移词从任一状态在状态层面到达所有模态。词中的 $M^{L-1}$ 是正向迭代，不是树的逆操作；不复制来源、不引入幽灵独立坐标，也不把负计数当作物理输入。

### 19.2 素数幂中的全部稳定子群

令 $m=p^h$。写 $f(T)=T^2-T-1$。

**命题 19.3（局部分类，包含非自由子群）。** 若 $W\le(\mathbb Z/p^h\mathbb Z)^2$ 满足 $MW=W$ 且 $W\cap\ker q=\{0\}$，则 $W=0$，或存在 $1\le e\le h$ 及 $\lambda\pmod {p^e}$ 使

$$
W=\left\langle p^{h-e}(1,\lambda)\right\rangle,
\qquad f(\lambda)\equiv0\pmod {p^e}.
\tag{RA.1905}
$$

此时 $|W|=p^e$，且 $q$ 在 $W$ 上自动单射。

**证明。**
因 $q|_W$ 单射，$W$ 嵌入循环群 $\mathbb Z/p^h\mathbb Z$，所以 $W$ 本身循环，阶为 $p^e$；循环性不要求自由，$e<h$ 的非自由循环子群仍由以下分类覆盖。取生成元写为
$p^{h-e}w$，其中 $w=(a,b)$ 在 $(\mathbb Z/p^e\mathbb Z)^2$ 中为原始向量。 $MW=W$ 给出某个 $\lambda$ 满足 $Mw=\lambda w\pmod {p^e}$，即 $b=\lambda a$、$a+b=\lambda b$。 若 $a$ 非单位，则 $b$ 也非单位，与 $w$ 原始矛盾；故 $a$ 为单位，可把生成元乘以 $a^{-1}$ 规范为 $(1,\lambda)$。第二个坐标方程正是 $f(\lambda)=0$。 反向地，根给出的向量满足 $M(1,\lambda)=\lambda(1,\lambda)$，所以其生成子群稳定。 还需核对 $q$。若 $q(1,\lambda)$ 被 $p$ 整除，则由特征关系 $qM(1,\lambda)=\lambda q(1,\lambda)$ 也被 $p$ 整除。可是

$$
\begin{pmatrix}q\\qM\end{pmatrix}
=
\begin{pmatrix}2&3\\3&5\end{pmatrix},
\qquad
\det\begin{pmatrix}2&3\\3&5\end{pmatrix}=1,
\tag{RA.1906}
$$

会迫使 $(1,\lambda)$ 在模 $p$ 下为零，矛盾。因此 $q(1,\lambda)$ 是单位，$q$ 在该循环子群上单射。证毕。

**命题 19.4（根提升深度）。** 定义

$$
e_p(h)=\max\bigl(\{0\}\cup
\{e:1\le e\le h,\ f\text{ 在 }\mathbb Z/p^e\mathbb Z\text{ 有根}\}\bigr).
\tag{RA.1907}
$$

则 $p\ne5$ 时有模 $p$ 根便有 $e_p(h)=h$；无模 $p$ 根则 $e_p(h)=0$。对 $p=5$，任意 $h\ge1$ 都有 $e_5(h)=1$。

**证明。**
模 $2$ 代入 $0,1$ 均不为零，故无根；高次有根必降为低次根。
设 $p$ 为奇素数且 $p\ne5$。恒等式

$$
(2\lambda-1)^2=4f(\lambda)+5
\tag{RA.1908}
$$

表明模 $p$ 根处 $2\lambda-1$ 为单位。若 $f(\lambda)=p^jc$，取 $\lambda'=\lambda+p^jt$，则

$$
f(\lambda')\equiv p^j(c+t(2\lambda-1))\pmod {p^{j+1}}.
\tag{RA.1909}
$$

唯一选择 $t\pmod p$ 可消去括号，逐层提升至 $p^h$。 模 $5$ 时唯一根为 $3$。任意提升写成 $3+5t$，而

$$
f(3+5t)=5+25t+25t^2\equiv5\pmod {25}.
\tag{RA.1910}
$$

所以不存在模 $25$ 根，也不存在更高根。证毕。

### 19.3 CRT 组合与一般下界

**定理 19.5（复合模数容量）。** 若
$m=\prod_{p^h\parallel m}p^h$，则最大可用核阶为

$$
D=\prod_{p^h\parallel m}p^{e_p(h)},
\qquad
C_m=\min|R|=\frac{m^2}{D}
=\prod_{p^h\parallel m}p^{\,2h-e_p(h)}.
\tag{RA.1911}
$$

**证明。**
CRT 给出 $V_m=\prod V_{p^h}$。取整数 CRT 幂等元
$\varepsilon_p$，它在 $p^h$ 分量为一、其余分量为零。任意加法子群对整数倍封闭，故

$$
W=\bigoplus_{p^h\parallel m}\varepsilon_pW
\tag{RA.1912}
$$

是其一次实际来源中的主分量分解。$M,q$ 与这些投影交换，因而稳定性和 $q|_W$ 单射逐分量成立。命题 19.3 给出每个分量的阶上界 $p^{e_p(h)}$，阶相乘得到 $|W|\le D$，从（RA.1903）得到下界 $|R|\ge m^2/D$。 对每个分量同时取达到 $e_p(h)$ 的根，CRT 合成一个整数 $\lambda$ 满足 $f(\lambda)\equiv0\pmod D$；当 $D=1$ 取 $\lambda=0$。

令 $H=m/D$、$W=\langle H(1,\lambda)\rangle\le V_m$；由第一坐标知其阶为 $D$。因 $D\mid f(\lambda)$，$M(H(1,\lambda))=\lambda H(1,\lambda)$ 在 $V_m$ 中成立，故 $MW\subseteq W$；$M$ 可逆且 $W$ 有限，所以 $MW=W$。在 $p^h$ 分量，若 $e_p(h)=0$ 则子群为零，否则 $H$ 是 $p^{h-e_p(h)}$ 的单位倍，该分量由 $p^{h-e_p(h)}(1,\lambda)$ 生成。命题 19.3 的反向论证保证 $q$ 在每个非零局部分量上单射，因此在 $W$ 上单射。由定理 19.2，陪集记录 $r(x)=x+W$ 满足本节合同，容量为 $m^2/D$，达到同一模数下的下界。这组选取在同一个 $W$ 和同一个模态中实现，故不是把分别可达的最佳值误当成共同来源。CRT 幂等元只用于坐标证明，不是新增物理操作。证毕。

### 19.4 可执行的两坐标记录

令

$$
H=m/D,\qquad W=\langle H(1,\lambda)\rangle,
\qquad
r(a,b)=(A,B)=(a\bmod H,\,b-\lambda a\bmod m).
\tag{RA.1913}
$$

当 $H=1$ 时第一坐标是唯一的模一元素。该记录的实际标签集合为 $\mathbb Z/H\mathbb Z\times\mathbb Z/m\mathbb Z$，也可用标准代表的整数 $A+HB$ 存放。

**命题 19.6（满射、核和容量）。** 映射（RA.1913）满射，核恰为 $W$，所以

$$
|R|=Hm=m^2/D=C_m.
\tag{RA.1914}
$$

**证明。**
给定 $A,B$，取 $a=A$、$b=B+\lambda A$ 即得该标签。若 $A=0$ 且
$B=0$，则 $a=Hk$、$b=\lambda a$，正好是 $kH(1,\lambda)$。反向包含显然成立。证毕。

**命题 19.7（只用记录的更新）。** 对任意记录坐标，固定代表后定义

$$
u(A,B)=\bigl(\lambda A+B\bmod H,\,
-f(\lambda)A+(1-\lambda)B\bmod m\bigr),
\tag{RA.1915}
$$

$$
v(A,B)=\bigl(A+1\bmod H,\,B-\lambda\bmod m\bigr).
\tag{RA.1916}
$$

它们分别等于 $r(Mx)$ 与 $r(Gx)$，且不读取 $q$。

**证明。**
写 $b=B+\lambda a$。则 $a'=b$ 给出第一坐标
$\lambda A+B$，而

$$
b'-\lambda a'
=a+(1-\lambda)b
=-f(\lambda)a+(1-\lambda)B.
\tag{RA.1917}
$$

由于 $D\mid f(\lambda)$ 且 $m=HD$，第二式在模 $m$ 下不随 $a$ 换成 $a+Hk$ 而改变，故它确实只由已有 $A,B$ 决定。$G$ 的两式直接给出 （RA.1916）。配对也可自主相加：

$$
r(x+y)=r(x)+r(y)
\quad\text{在 }\mathbb Z/H\mathbb Z\times\mathbb Z/m\mathbb Z\text{ 中}.
\tag{RA.1918}
$$

因此叶记录为

$$
r(\alpha)=(1\bmod H,-\lambda),\qquad r(\beta)=(0,1),
\tag{RA.1919}
$$

每个实际二叉节点把两个已有坐标相加。证毕。

### 19.5 联合解码与不相容观测

**命题 19.8（可执行解码器）。** 令
$\kappa=2+3\lambda$。命题 19.3 说明 $\kappa$ 在模 $D$ 下为单位。 给定记录 $(A,B)$ 和当前观测 $s=q(a,b)$，先取 $A,B,s$ 的标准整数代表，令

$$
E=\operatorname{rem}_m\bigl(s-\kappa A-3B\bigr).
\tag{RA.1920}
$$

若 $D=1$，记录本身已是 $(a,b)$。若 $D>1$，相容观测满足 $H\mid E$，并令

$$
k=\kappa^{-1}(E/H)\pmod D,\qquad
a=A+Hk\pmod m,\qquad
b=B+\lambda a\pmod m.
\tag{RA.1921}
$$

**证明。**
由 $b=B+\lambda a$，

$$
s=\kappa a+3B\pmod m.
\tag{RA.1922}
$$

又 $a=A+Hk$，故 $E$ 是 $\kappa Hk$ 的模 $m$ 标准代表，必被 $H$ 整除，且 $E/H=\kappa k\pmod D$。这给出（RA.1921）。若 $E$ 不被 $H$ 整除，应报告 $(s,A,B)$ 不相容；不能把整个笛卡尔积都宣称为实际联合像。这里 $E/H$ 是普通整数除法， 绝不是把 $H$ 当作模 $m$ 的逆。因联合单射，实际全联合像有 $m^2$ 个态；通常它是 $\mathbb Z/m\mathbb Z\times R$ 的真子集。证毕。

### 19.6 分歧素数五与模二十五边界

对 $m=5^h$，$D=5$、$H=5^{h-1}$、可取 $\lambda=3$。于是

$$
r(a,b)=(a\bmod5^{h-1},\,b-3a\bmod5^h),
\tag{RA.1923}
$$

$$
u(A,B)=(3A+B\bmod H,\,-5A-2B\bmod5^h),
\qquad
v(A,B)=(A+1\bmod H,\,B-3\bmod5^h),
\tag{RA.1924}
$$

并且 $|R|=5^{2h-1}$。端点 $h=1$ 的容量为 $5$；$h=2$ 即 $m=25$ 的容量为 $125$。当 $h\ge2$ 时，第一坐标只含 $5^{h-1}$ 个值，记录是非自由的两坐标商。 模 $25$ 的自然尝试 $r_0(a,b)=b-3a$ 虽与 $q$ 联合单射，却不自主。确实，

$$
r_0(0,0)=r_0(1,3)=0,\qquad
r_0(M(0,0))=0,\qquad r_0(M(1,3))=r_0(3,4)=20.
\tag{RA.1925}
$$

两初态分别有 $25$ 片 $\alpha$ 和一片 $\alpha$ 加三片 $\beta$ 的非空树代表； 所以这是实际来源反例，说明 $25$ 标签的朴素延拓不可能有单值 $u$。它反驳的是该朴素记录， 不是本节的 $125$ 标签定理。联合单射可直接由矩阵 $\bigl((2,3),(-3,1)\bigr)$ 的行列式 $11$ 与 $25$ 互素核对。

### 19.7 允许更新器读 $q$ 时的补充下界

**命题 19.9（$q$ 可供更新的最小补充）。** 若更新器也能读取当前 $q$，则补充记录的最小容量为 $m$，但完整联合像仍有 $m^2$ 个态。
令

$$
z(a,b)=q(M(a,b))=3a+5b\pmod m.
\tag{RA.1926}
$$

有

$$
z(Mx)=q(x)+z(x),\qquad z(Gx)=z(x)+3,
\tag{RA.1927}
$$

且

$$
a=5q-3z,\qquad b=-3q+2z\pmod m.
\tag{RA.1928}
$$

故 $z$ 给出 $m$ 值的充分补充。$q$ 满射，因为 $-2+3=1$，故每条 $q$ 纤维有 $m$ 个态；联合单射迫使每条纤维拥有至少 $m$ 个补充标签。这里的容量与自主 $R$ 的容量不同；$(q,z)$ 的联合像是全部 $m^2$ 个态。

### 19.8 初始化是独立接口

容量定理只量正确初始化后的维护。允许存在未匹配的模型 $(x,s_0)\in V_m\times R$； 自主更新本身不能替它取得正确标签。对任一固定正向操作词 $w$，其记录作用 $U_w$ 是双射并满足

$$
U_w(r(x))=r(wx),\qquad
U_w(s_0)=r(wx)\Longleftrightarrow s_0=r(x).
\tag{RA.1929}
$$

逐步选词的自适应程序也对每一条实际分支满足同一等式，因此错误种子不能靠既定自主置换修复。 这不等于声称真实初始化不可达，也不把错误标签算作来源联合像。 有两种独立授权的初始化接口。其一，若源树可读且允许自底向上归约，就给 $\alpha,\beta$ 写入（RA.1919），每个配对节点相加，得到当前树的 $r(c(t))$。 其二，若允许同一来源的无扰动两次读取和写入：先读 $s=q(x)$ 并保留，再实际执行一次 $M$，读 $t=q(Mx)$，由行列式一的逆矩阵先解旧态

$$
x=(5s-3t,\,-3s+2t)\pmod m,
\tag{RA.1930}
$$

再把 $r(Mx)$ 写入当前记录。一次 $M$ 确实改变来源状态；两次读数来自同一演化来源， 不能写成同态的重复读数。临时保存首读数、取得控制器和记录写权限均不免费，本节不声称其费用最优。

### 19.9 有限整数核验

已有有限整数核验覆盖下表九个模数，全源态总数为 $23912$；每一行均遍历该模数的全部 $m^2$ 个 $(a,b)$， 并将每个源态分别与 $\alpha,\beta$ 配对核验记录相加。

| $m$ | $D$ | $H$ | 所取 $\lambda$ | $|R|=C_m$ | $M$ 全局周期 |
|---:|---:|---:|---:|---:|---:|
| 4 | 1 | 4 | 0 | 16 | 6 |
| 5 | 5 | 1 | 3 | 5 | 20 |
| 9 | 1 | 9 | 0 | 81 | 24 |
| 11 | 11 | 1 | 4 | 11 | 10 |
| 13 | 1 | 13 | 0 | 169 | 28 |
| 25 | 5 | 5 | 3 | 125 | 100 |
| 55 | 55 | 1 | 8 | 55 | 20 |
| 65 | 5 | 13 | 3 | 845 | 140 |
| 125 | 5 | 25 | 3 | 3125 | 500 |

已有核验逐态检查了标签满像计数、$(q,r)$ 联合单射、（RA.1921）解码、$u/v$ 一致性、 全态对两个基叶的二叉记录相加、$M$ 周期、正向词 $M^{L-1}$ 后 $G$ 后 $M$ 的 $\beta$ 平移，以及 $q$ 辅助的 $z$ 更新和解码。根枚举得到模 $5$ 为 $\{3\}$、模 $25$ 与模 $125$ 无根、模 $11$ 为 $\{4,8\}$；模 $25$ 的（RA.1925）也逐项确认。该有限核验没有枚举任意分划， 一般下界和分类来自上述证明，不由样本穷举代替。

### 19.10 适用边界

本节只继承同一固定模数层内的 $M$ 加单叶嫁接合同，并给出该层正确初始化后的自主记录容量。 它不声称跨精度塔的最优性、无限来源、整棵树恢复、取得资源最优或长期目标已经完成。 CRT 组合证明的是同一实际来源上的共同记录；它不把各分量的坐标当作额外物理操作。

## 追加锚（本行以下为增补区）


## 20. 自主补充记忆的精度塔与实际有限来源

本节在 §19 的一般模数单层分类上，加入只读取记录的降精度要求，并区分完成域中的相容线程与同一棵非空有限树的实际像。全部结论沿用当前态恢复合同；容量只计算正确初始化后的补充标签。

### 20.1 当前态合同与核约化判据

固定素数 $p$，对每个 $h\ge1$ 取

$$
\begin{gathered}
V_h=(\mathbb Z/p^h\mathbb Z)^2,\qquad
M(a,b)=(b,a+b),\qquad G(a,b)=(a+1,b),\\
q_h(a,b)=2a+3b\pmod{p^h},\qquad
r_h:V_h\to R_h=r_h(V_h),\\
(q_h,r_h)\text{ 单射},\qquad
r_hM=u_hr_h,\qquad r_hG=v_hr_h.
\end{gathered}
\tag{RA.2001}
$$

$r_h$ 是确定的当前态记录，$u_h,v_h$ 是时齐次更新，输入只有记录与已声明的操作名；当前 $q_h$、历史、相位和额外时钟不进入更新器。源域是整个 $V_h$。解码器可以读取当前 $q_h$，$|R_h|$ 只计实际像中的补充标签，不是取得阶段或总硬件容量。

记 $\pi_h:V_{h+1}\to V_h$ 为坐标约化。§19 已给出唯一陪集核 $W_h\le V_h$，满足 $MW_h=W_h$、$W_h\cap\ker q_h=\{0\}$，且

$$
r_h(x)=r_h(y)\iff x-y\in W_h.
$$

以下复用该分类及其单层最小值，不重新证明单层同余分类。

**定理 20.1（只读取记录的降精度）。** 存在 $\ell_h:R_{h+1}\to R_h$ 满足源交换式，当且仅当核约化满足包含；存在时，该映射唯一、满射，并与两个更新交换：

$$
\boxed{
\begin{gathered}
\bigl(\exists\ell_h:R_{h+1}\to R_h,\ \ell_hr_{h+1}=r_h\pi_h\bigr)
\quad\Longleftrightarrow\quad
\pi_h(W_{h+1})\subseteq W_h,\\
\ell_hu_{h+1}=u_h\ell_h,\qquad
\ell_hv_{h+1}=v_h\ell_h.
\end{gathered}}
\tag{RA.2002}
$$

证明。必要性由 $r_{h+1}(w)=r_{h+1}(0)$ 得到 $r_h(\pi_hw)=r_h(0)$，故 $\pi_hw\in W_h$。反向定义
$\ell_h(r_{h+1}(x))=r_h(\pi_hx)$；核包含保证同一高层记录的不同代表给出相同低层值。$r_{h+1}$ 满射给唯一性，$\pi_h$ 与 $r_h$ 满射给满射性。又因 $\pi_hM=M\pi_h$，

$$
\ell_hu_{h+1}r_{h+1}(x)
=r_h(\pi_hMx)
=u_hr_h(\pi_hx)
=u_h\ell_hr_{h+1}(x).
$$

再用 $r_{h+1}$ 满射即得 $M$ 更新交换；$G$ 同理。证毕。

若相邻包含对所有 $h$ 成立，记 $\pi_{h,k}$ 为坐标约化，复合 $\ell_{h,k}=\ell_h\cdots\ell_{k-1}$ 自动满足
$\ell_{h,k}r_k=r_h\pi_{h,k}$ 与 $\ell_{h,k}\ell_{k,j}=\ell_{h,j}$。所以相邻条件足以构成整座塔，不要求核约化满射。逐层固定双射 $b_h:R_h\to R'_h$，即使非线性，也只把降层改为
$\ell'_h=b_h\ell_hb_{h+1}^{-1}$，并共轭更新器；它不改变核或判据。合并标签则改变了记录，不属于双射重标记。

### 20.2 同时逐层最优的全部相容类型

令 $f(t)=t^2-t-1$。称 $p\ne5$ 且 $f$ 模 $p$ 有根为 split 情形，无根为 nonsplit 情形；$p=5$ 单列。“逐层最优相容塔”要求每层都达到 §19 单层下界，并满足定理 20.1。

**定理 20.2（三类最优塔）。** 固定来源坐标，允许逐层任意双射重标记，则 split 恰有两条最优相容根分支；nonsplit（包括 $p=2$）只有全态类型；$p=5$ 只有下述两坐标类型。三类均可同时达到全部单层下界。

证明。在 split 情形，§19 给出的最优核为
$W_h=(\mathbb Z/p^h\mathbb Z)(1,\lambda_h)$，其中 $f(\lambda_h)=0$。约化后仍是满长直线，且核中第一坐标为 $1$ 的向量唯一，故

$$
\pi_h(W_{h+1})\subseteq W_h
\iff\lambda_{h+1}\equiv\lambda_h\pmod{p^h}.
$$

模 $p$ 的两个根各有唯一的逐层提升（§19 的简单根提升结论），所以恰有两条相容分支，不能逐层独立换根。每条分支可取

$$
\begin{gathered}
R_h=\mathbb Z/p^h\mathbb Z,\qquad
r_h(a,b)=b-\lambda_ha,\qquad |R_h|=p^h,\\
u_h(s)=(1-\lambda_h)s,\qquad
v_h(s)=s-\lambda_h,\qquad
\ell_h(s)=s\bmod p^h.
\end{gathered}
\tag{RA.2003}
$$

记录满射，核正是 $W_h$。联合解码所需单位可由整数恒等式直接看出：

$$
(2+3t)(5-3t)=1-9f(t).
\tag{RA.2004}
$$

在同一环中的真根上，$2+3\lambda_h$ 的逆就是 $5-3\lambda_h$。

在 nonsplit 情形，§19 给 $W_h=0$，故任意合格记录都是全态记录的双射重标记。取 $r_h(a,b)=(a,b)$、$\ell_h=\pi_h$，更新就是 $M,G$，每层有 $p^{2h}$ 个标签。模二无根，属于此类。

在五进情形，§19 给模五唯一根 $3$、模二十五及以上无根，因此每层唯一最优核和标准记录为

$$
\boxed{
\begin{gathered}
H_h=5^{h-1},\qquad W_h=\langle H_h(1,3)\rangle,\qquad |W_h|=5,\\
\pi_h(W_{h+1})=\{0\}\subsetneq W_h,\\
R_h=\mathbb Z/5^{h-1}\mathbb Z\times\mathbb Z/5^h\mathbb Z,\\
r_h(a,b)=(A,B)=(a\bmod H_h,\ b-3a\bmod5^h),\qquad
|R_h|=5^{2h-1}.
\end{gathered}}
\tag{RA.2005}
$$

该记录满射、核为 $W_h$。其自主更新与降层为

$$
\begin{aligned}
u_h(A,B)&=(3A+B\bmod H_h,\ -5A-2B\bmod5^h),\\
v_h(A,B)&=(A+1\bmod H_h,\ B-3\bmod5^h),\\
\ell_h(A,B)&=(A\bmod5^{h-1},\ B\bmod5^h).
\end{aligned}
\tag{RA.2006}
$$

最后一行的输入属于 $R_{h+1}$。第二更新坐标中的 $-5A$ 良定义，因为 $5H_h=5^h$。坐标约化满足源交换式，故与 $M/G$ 更新交换。$h=1$ 的第一坐标是 $\mathbb Z/1\mathbb Z$ 的单点，这个端点仍属于塔。所有最优记录具有同一个核，因而任意标签表示都由定理 20.1 组成相容塔。证毕。

**例 20.3（模十一的错根分支）。** 取 $\lambda_1=4\pmod{11}$、$\lambda_2=85\pmod{121}$。有
$f(4)=11$、$f(85)=7139=59\cdot121$，而 $85\equiv8\pmod{11}$。两层记录 $r_1=b-4a$、$r_2=b-85a$ 各自最优，但

$$
\begin{gathered}
x=(0,0),\qquad y=(1,85)\in V_2,\\
r_2(x)=r_2(y)=0,\qquad
r_1(\pi_1x)=0,\qquad r_1(\pi_1y)=4.
\end{gathered}
$$

因此不存在只读取记录的 $\ell_1$，双射重标记也不能修复。同一低层根 $4$ 的相容高层根应为 $37\pmod{121}$。零剩余对有非空树代表，例如 $121$ 个 $\alpha$ 叶；$y$ 由一个 $\alpha$ 和 $85$ 个 $\beta$ 叶实现。反例没有使用空树。相容性不增加最优塔同时达到单层下界的容量，但独立挑选的逐层最优记录不一定相容。

### 20.3 有限隐藏核与极限记录

令 $V_\infty=\varprojlim_hV_h=\mathbb Z_p^2$、$R_\infty=\varprojlim_h(R_h,\ell_h)$。相容记录诱导 $r_\infty:V_\infty\to R_\infty$；以下使用定理 20.2 的标准坐标，双射重标记按层运输结论。

**定理 20.4（最优塔的极限）。** split 分支给出真根 $\lambda\in\mathbb Z_p$，且

$$
\begin{gathered}
R_\infty\cong\mathbb Z_p,\qquad
r_\infty(a,b)=b-\lambda a,\qquad
\ker r_\infty=\mathbb Z_p(1,\lambda),\\
a=(2+3\lambda)^{-1}(q-3r),\qquad b=r+\lambda a.
\end{gathered}
\tag{RA.2007}
$$

因此记录单独在全 $\mathbb Z_p^2$ 上隐藏一条直线，与当前 $q=2a+3b$ 联合则恢复全态。nonsplit 的极限记录为 $\mathbb Z_p^2$，且 $r_\infty=\operatorname{id}$。五进极限则为

$$
\boxed{
R_\infty\cong\mathbb Z_5^2,\qquad
r_\infty(a,b)=(a,b-3a),\qquad
r_\infty^{-1}(A,B)=(A,B+3A).
}
\tag{RA.2008}
$$

证明。split 中相容根与标量记录分别组成 $\lambda$ 和一个 $p$-进数，记录满射、核如式（RA.2007）；式（RA.2004）保证解码分母为单位。nonsplit 按坐标约化直接得到全态。五进的第一坐标按 $5^{h-1}$ 截断，虽起于模一，仍唯一确定 $A\in\mathbb Z_5$；第二坐标确定 $B\in\mathbb Z_5$。反向截断给所有记录线程，显式逆即得双射。等价地，相容核线程满足 $w_h=\pi_h(w_{h+1})=0$，故 $\varprojlim W_h=0$。证毕。

五进必须区分下列映射，不能把有限源纤维的大小直接传给极限：

| 映射 | 纤维或核的性质 |
|---|---|
| $r_h:V_h\to R_h$ | 每个纤维恰有 $5$ 个态 |
| $W_{h+1}\to W_h$ | 零映射 |
| $\ell_h:R_{h+1}\to R_h$ | 每个纤维恰有 $25$ 个标签 |
| $r_\infty:V_\infty\to R_\infty$ | 每个纤维恰有 $1$ 个态 |

固定一个相容记录线程，高层源纤维中的五个差异约化后全部消失，其低层像只有一个态，不满射到低层的五态纤维。这些有限选择不是跨层独立选择。

所有情形的完整联合实际像始终为

$$
J_h=(q_h,r_h)(V_h),\qquad |J_h|=p^{2h}.
\tag{RA.2009}
$$

这由联合编码单射给出，不能一般用边缘基数乘积 $p^h|R_h|$ 代替。联合降层在实际像上为 $(s,z)\mapsto(s\bmod p^h,\ell_hz)$，其逆极限与 $V_\infty$ 一一对应。五进有限层的有效联合值须满足
$s\equiv11A+3B\pmod{H_h}$；解码可取 $a=11^{-1}(s-3B)$、$b=B+3a$（模 $5^h$），所得 $a\bmod H_h=A$。极限中则已有 $q=11A+3B$，当前读数由记录确定；有限层仍需 $q_h$ 补足源纤维。

### 20.4 同环图册与只读取记录的运输

**命题 20.5（换根图册）。** 在同一个环 $K=\mathbb Z/p^h\mathbb Z$ 或 $K=\mathbb Z_p$ 中，令 $r_\lambda=b-\lambda a$、$r_\mu=b-\mu a$。只要 $2+3\lambda$ 为单位，就有

$$
\boxed{
r_\mu=\frac{2+3\mu}{2+3\lambda}r_\lambda
+\frac{\lambda-\mu}{2+3\lambda}q.
}
\tag{RA.2010}
$$

证明。不作除法时恒有
$(2+3\lambda)r_\mu=(2+3\mu)r_\lambda+(\lambda-\mu)q$，乘以单位逆即可。若两斜率是真根，式（RA.2004）保证两方向的单位性，故两个联合图册互相转换。但全域 $K^2$ 上存在只读 $r_\lambda$ 的函数产生 $r_\mu$，当且仅当 $\lambda=\mu$：$0$ 与 $(1,\lambda)$ 的旧记录同为零，新记录分别为 $0$ 与 $\lambda-\mu$。此论证也排除非线性转换。证毕。

例 20.3 须先将高层根约化为模十一的 $8$，再在同一环使用
$r_4=9r_8+q$。这是读取 $q$ 的联合转换，不能提供只读取记录的降层。高层五进没有满长根；非根斜率即使使分母为单位，代数图册也不保证自主维护。模二十五取 $r_0=b-3a$，则 $0$ 与 $(1,3)$ 的 $r_0$ 都为零，执行 $M$ 后却为 $0$ 与 $20$。所以不能借单标量图册删去五进记录的第一坐标。

### 20.5 一棵共同有限树的准确来源像

沿用非空有限有序二叉树 $\mathcal T$ 及叶计数 $c$。计数的实际像为

$$
C=\{(a,b)\in\mathbb N_0^2:a+b>0\},\qquad
\mathcal T\xrightarrow{c}C\xrightarrow{\iota}\mathbb Z_p^2.
\tag{RA.2011}
$$

$c$ 满射：给定该非负计数对，任意配对指定数量的两类叶即可。$\iota$ 是普通整数的自然嵌入；计数不保留左右次序或括号结构。

**命题 20.6（共同有限来源）。** 来源线程 $x\in V_\infty$ 及对应的完整联合线程有一棵共同有限树来源，当且仅当 $x\in\iota(C)$。记录线程 $\varrho\in R_\infty$ 有某棵共同有限树来源，当且仅当

$$
\varrho\in r_\infty(\iota(C))=
\begin{cases}
\{b-\lambda a:a,b\in\mathbb N_0,\ a+b>0\},&\text{split},\\
\iota(C),&\text{nonsplit},\\
\{(a,b-3a):a,b\in\mathbb N_0,\ a+b>0\},&p=5.
\end{cases}
\tag{RA.2012}
$$

证明。一棵有限树的计数对固定，全部截断必须来自同一对，给必要性；属于所列实际像时，由该计数对构造树，给充分性。完整联合线程逐层唯一解码且解码与约化相容，故与来源线程使用同一判据。证毕。

每个有限层源态都能由非空树实现：取非负剩余代表，零对改用 $(p^h,0)$。然而线程 $(-1,0)$ 的第 $h$ 层可分别用 $(p^h-1,0)$ 实现，却没有共同有限树；否则某个 $a\ge0$ 满足 $p^h\mid a+1$ 对所有 $h$ 成立，与 $a+1>0$ 矛盾。这里 $-1$ 是普通整数，障碍是非负来源限制。

其记录线程也没有共同有限树来源。nonsplit 与五进由极限记录单射立即得到；split 的该记录为 $\lambda$，若 $b-\lambda a=\lambda$ 来自非负整数计数，则 $\lambda=b/(a+1)\in\mathbb Q$，但 $f$ 没有有理根。进一步，split 的 $r_\infty$ 在整个 $\mathbb Z^2$ 上单射：两整数对记录相同，第一坐标不同会迫使 $\lambda$ 为有理数；第一坐标相同则第二坐标也相同。因此完整精度记录在整数计数域上确定计数，仍不恢复树形，也不消除全 $\mathbb Z_p^2$ 上的隐藏直线。

来源线程属于 $\iota(C)$，与记录线程属于 $r_\infty(\iota(C))$ 是不同判据。尤其在 split 情形，不能把一个任意选取的记录原像要求为非负整数对，来判断该记录是否具有某个有限树来源。

### 20.6 初始化、读取能力与结果归属

固定 $h$，$M,G$ 是有限源域置换；取 $M^L=I$，由记录满射得 $u_h^L=\operatorname{id}$、$v_h^{p^h}=\operatorname{id}$，故记录更新也是置换。对任意初始标签 $s_0\in R_h$、操作词 $w$ 及其记录置换 $U_w$，

$$
r_h(wx)=U_w(r_h(x)),\qquad
U_w(s_0)=r_h(wx)\iff s_0=r_h(x).
\tag{RA.2013}
$$

因此维护更新不能修复错误初值；即使自适应选出操作词，这个逐词等价式仍成立。正确高层记录可以降为正确低层记录，不等于取得正确高层记录的权限。源语法访问、暂存读数、记录写入与阶段控制须按 §18.7、§19 的取得合同另行授权并计费；本节不重复取得证明，也不优化取得控制器或总硬件。已知有限树按需计算任一给定有限精度，不等于一次免费取得无限精度记录。

单层核分类、根深度、容量下界及有限记录构造均复用 §19；定理 20.1 是本卷 §5.1.6 一般纤维下降原则在该核分类下的具体应用。[FIB 卷定理 29.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 已有隐藏核跨两级约化为零而逆极限为零的机制；本节只计算当前 $q+M/G$ 合同下的一级归零与极限坐标。[FIB 卷 §§42–43](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 属于方阵 $B$、Smith 坐标及其自治记录合同，其容量结论不能直接移植。

本卷 §5.1.1 的共同实现依赖同一紧 Hausdorff 来源、连续满射到 Hausdorff 层及有向相容性，可用于这里的完成载体，不能据此把线程反推为有限树；§5.1.9 已区分整数来源与其完成。本节的新增内容是这些机制在当前维护合同下的具体核判据、最优相容分支及非空树记录像，属于普通数学应用，不另作一般定理或原创声明。空间、时间、边界与记忆的一般恢复目标仍超出本节范围。

## 追加锚（本行以下为增补区）


## 21. 有界实际来源的有限精度计数恢复

在下述有限单射判据成立时，有界树上的标量观察与计数映射具有相同的核：$\ker(o_h|\mathcal T_N)=\ker(c|\mathcal T_N)$。因此一个确实取得的有限记录足以恢复该实际树的计数及所有已声明的计数任务。本节把 §20.5 的整数完整精度单射接到这个有限逆接口；纤维下降、黄金范数、查询容量及终端 gcd 取得均复用既有结果，只证明当前来源限制下的应用与边界。

### 21.1 同一实际来源、可见输入与恢复关系

沿用 §19–20 的非空有序二叉树 $\mathcal T$、叶计数 $c$ 和操作 $M(a,b)=(b,a+b)$、$G(a,b)=(a+1,b)$。给定整数 $N\ge1$，定义

$$
C_N=\{(a,b)\in\mathbb N_0^2:1\le a+b\le N\},\qquad
\mathcal T_N=c^{-1}(C_N),\qquad
K_N=|C_N|=\sum_{\ell=1}^N(\ell+1)=\frac{N(N+3)}2.
\tag{RA.2101}
$$

固定一棵未知但实际的 $t\in\mathcal T_N$，记 $x=c(t)$。$N$ 的有效性是供应的来源承诺，不从记录推断。参数还包括已认证的 split 素数 $p\ne5$、$f(z)=z^2-z-1$ 的指定简单根，以及 §19 的唯一相容提升 $\lambda_{j+1}\equiv\lambda_j\pmod{p^j}$。有限解码输入为 $N,p,h\ge1$、该分支的有限根 $0\le\lambda_h<m=p^h$ 和精确同源标准剩余 $0\le s<m$，其中

$$
e_h(a,b)=b-\lambda_ha\pmod m,\qquad o_h=e_h\circ c,\qquad s=o_h(t).
\tag{RA.2102}
$$

根可由已认证的 $\lambda_1$ 另行准备；若供应 $\lambda_h$，其根身份及分支相容性也须供应或另行验证。统一精度证书是下文有限判据通过，或严格充分界成立。当前数量 $q$、树语法、历史、时钟及重置权限均不是这个标量解码器的隐含输入。

每个 $C_N$ 中的对都有非空树代表（§20.5）。故 $e_h|C_N$ 单射当且仅当上述树观察核等于计数核；成立时，实际像上有唯一 $d_{N,h}:e_h(C_N)\to C_N$ 满足 $d_{N,h}(o_h(t))=c(t)$。这是 [RRO 卷定理 2.2](RECURSIVE_RELATIONAL_OBSERVATION.md) 的实际像纤维因子化直接代入。对任何另外声明的集合 $Y$ 与计数任务 $F:C_N\to Y$，

$$
F(c(t))=(F\circ d_{N,h})(o_h(t)),\qquad t\in\mathcal T_N.
\tag{RA.2103}
$$

这里恢复的是计数商，包括 $F(a,b)=2a+3b$；不要求从标量生成某个原始树代表，更不把任意代表当作原树。

### 21.2 非空差集与指定分支的精确判据

**命题 21.7（实际非空差集）。** 令 $D_N=C_N-C_N$。对 $d=(u,v)\ne0$，置 $P=\max(u,0)+\max(v,0)$、$Q=\max(-u,0)+\max(-v,0)$，则

$$
D_N=\{0\}\ \cup\
\{d\ne0:P,Q>0,\ \max(P,Q)\le N\}\ \cup\
\{d\ne0:\min(P,Q)=0,\ \max(P,Q)\le N-1\}.
\tag{RA.2104}
$$

证明。写 $d=d_+-d_-$，其中两个向量逐坐标非负且支撑不交。所有非负代表 $x-y=d$ 恰为 $x=d_++z$、$y=d_-+z$，$z\ge0$。若 $P,Q>0$，两者已非空，$z=0$ 给充分性，而叶数界给必要性。若一部分为零，共同部分必须有至少一片叶，故非零部分至多 $N-1$；反向添加 $z=(1,0)$ 即得两个允许来源。零差由任一允许来源自身实现。证毕。尤其 $N=1$ 时非零差只有 $\pm(1,-1)$；不能用含空树三角形的较大差集替代。

**命题 21.8（统一精度与单个观测纤维）。** 对每个指定的有限根，置

$$
\Lambda_h=\{(u,v)\in\mathbb Z^2:v-\lambda_hu\equiv0\pmod m\}
=\mathbb Z(1,\lambda_h)+\mathbb Z(0,m).
\tag{RA.2105}
$$

这个格的指数为 $m$，且

$$
e_h|C_N\text{ 单射}\iff\Lambda_h\cap D_N=\{0\},\qquad
h_{\mathrm{unif}}=\min\{h\ge1:\Lambda_h\cap D_N=\{0\}\}.
\tag{RA.2106}
$$

证明。整数映射 $(u,v)\mapsto v-\lambda_hu\pmod m$ 满射，核就是所列格；任一核向量写成 $u(1,\lambda_h)+(0,v-\lambda_hu)$。两个允许来源记录相等恰好是它们的差进入此核，给出等价式。相容性使高精度记录相等蕴含低精度相等，故单射性随精度单调；下节的充分界保证这个有限最小值存在。证毕。

这是对所有 $C_N$ 来源使用同一个逆的最小统一前缀长度。对于已收到的实际记录，另定义

$$
A_{N,h}(s)=\{y\in C_N:e_h(y)=s\},\qquad
h_x=\min\{h\ge1:A_{N,h}(e_h(x))=\{x\}\}.
\tag{RA.2107}
$$

在精确同源及有效界承诺下，当前计数由 $s$ 唯一确定恰好是 $|A_{N,h}(s)|=1$，等价于 $\Lambda_h\cap(x-C_N)=\{0\}$。非单点时，不同允许来源给出完全相同的解码输入；单点时其成员就是实际计数。于是 $h_x\le h_{\mathrm{unif}}$，但两者不必相等。指定分支必须保留在碰撞及纤维判据中；这里不作共轭分支统一最小值的数值比较。§20.5 的完整 $p$-进记录在整数计数上单射是另一条无限精度事实，不是解码器读取无限记录的授权。

### 21.3 必要容量、严格充分界与有限精度选择

**命题 21.9（当前来源域的精度界及有限检验）。** 统一恢复的必要条件是 $m\ge K_N$；令 $B_N=\lfloor5N^2/4\rfloor$，则 $m>B_N$ 是充分条件。后者只是充分包络，不是精确阈值。

证明。必要性直接代入既有容量结果：$C_N$ 的 $K_N$ 个计数必须注入 $m$ 个标量值。若以 $p$ 值回答、最坏深度 $h$ 的确定查询协议表述，同样是 [WorstCaseDepthInformationLowerBound 的精确识别界](../../../Blueprint/D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.md) 在来源 $C_N$、分支数 $p$ 上的应用；它不赋予读数接口，也不限制每个实际来源都必须读同样多位。

复用 [黄金范数](../../../Blueprint/D5/S0/Carrier/Norm.md) 在坐标 $(A,B)=(v,-u)$ 上的恒等式，得整数

$$
F(u,v)=v^2-uv-u^2
\equiv(v-\lambda_hu)(v-(1-\lambda_h)u)\pmod m.
\tag{RA.2108}
$$

非零整数差的 $F$ 非零：$u=0$ 时为 $v^2$；$u\ne0$ 时 $F=0$ 会使 $v/u$ 成为 $f$ 的有理根，而 $f$ 无有理根。指定分支碰撞推出 $m\mid F$，反向不成立。

在 $D_N$ 中，同向（包括一个坐标为零）的非零差满足 $|u|+|v|\le N-1$，故 $|F|\le(|u|+|v|)^2\le(N-1)^2$。异向差经整体取负写成 $(u,-z)$，其中 $1\le u,z\le N$，于是

$$
-N^2\le z^2+uz-u^2
\le N^2+Nu-u^2
=\frac{5N^2}{4}-(u-N/2)^2.
\tag{RA.2109}
$$

因此所有差都满足 $|F|\le B_N$。取 $z=N$ 和最靠近 $N/2$ 的正整数 $u$，该混合差属于 $D_N$ 并取到 $B_N$；$N=1$ 取 $u=z=1$ 即取到 $1$。所以这是差域的准确范数包络。若 $m>B_N$，非零 $F$ 不可能被 $m$ 整除，故不存在非零碰撞。证毕。

令 $h_0$ 为满足 $p^{h_0}\ge K_N$ 的最小正整数。split 素数必有 $p\ge11$：小于十一的素数中，$2,3,7$ 的 $f$ 无根，$5$ 已排除。又 $pK_N>B_N$（例如 $2pN(N+3)>5N^2$），故

$$
h_{\mathrm{unif}}\in\{h_0,h_0+1\}.
\tag{RA.2110}
$$

容量排除所有较小层，下一层由严格范数界保证足够。求 $h_0$ 和严格充分层都用整数幂比较，不依赖浮点对数或无限根。

精确检验也可避免枚举来源对。**此检验先要求 $m>N$**。$u=0$ 的非零允许差不可能碰撞；利用 $d$ 与 $-d$ 的对称性，只需 $u=1,\ldots,N$。式（RA.2104）此时给出的允许整数 $v$ 恰为 $[-N,N-1-u]$：负值来自混合差，非负值满足 $u+v\le N-1$。置 $t_u=\lambda_hu\bmod m$ 为标准代表，则

$$
\Lambda_h\cap D_N\ne\{0\}
\iff\exists u\in\{1,\ldots,N\}:\quad
t_u\le N-1-u\ \text{或}\ t_u\ge m-N.
\tag{RA.2111}
$$

证明。允许区间包含于 $(-m,m)$，与 $t_u$ 同余的整数只能是 $t_u$ 或 $t_u-m$。前者属于允许区间恰好满足第一个不等式；后者为负，属于区间恰好满足第二个不等式。$u=N$ 时第一端点是 $-1$，第一条件自动为假，仍完整保留负端。$N=1$ 时只测试 $v=-1$；真根不可能为 $-1\pmod p$，故 $h_{\mathrm{unif}}=1$。证毕。

取 $L=\lceil\log_2m\rceil$。逐次模加更新 $t_u$，检验耗 $O(NL)$ 二进制位工作、$O(L+\log(N+1))$ 工作位，参数准备另计。$p^{h_0}\ge K_N>N$，所以在 $h_0$ 可用这个检验：通过就取 $h_0$，失败就取 $h_0+1$。这是可选且单独计费的精确精度选择；直接取范数充分层也可。省下一位并不自动比取得这一位便宜。

**例 21.10（三种精度区别）。** 取 $p=11,\lambda_1=4,N=3$。此时 $K_3=9\le11=B_3$，但 $(0,3)$ 和 $(2,0)$ 的记录都为 $3$；容量不是充分性，充分界中的严格号不能一般改为 $m\ge B_N$。同层记录 $1$ 的纤维却只有 $(0,1)$：$a=0,1,2,3$ 对应的标准 $b$ 依次为 $1,5,9,2$，后三者叶数均超过三。因此这个实际来源 $h_x=1$，而相容根 $\lambda_2=37$ 在 $121>B_3$ 处单射，给 $h_{\mathrm{unif}}=2$。

上述碰撞差 $(2,-3)\in D_3$ 的范数为 $11$；在根 $4$ 下 $v-\lambda_1u=-11$，在另一根 $8$ 下却为 $-19$。这只反驳“范数整除即该差在指定分支碰撞”，不宣告另一分支在整个 $C_3$ 上单射。

反向，范数充分条件并非必要。取 $p=239,\lambda_1=16,N=14$；$239$ 不被所有不超过其平方根的素数 $2,3,5,7,11,13$ 整除，故为素数。$f(16)=239$，而 $B_{14}=245>239$。整数值 $b-16a$ 全落在 $[-224,14]$，区间宽 $238<239$。若两个值模 $239$ 相等，便先在整数上相等；再由 $16(a-a')=b-b'$ 和 $|b-b'|\le14<16$ 得 $a=a',b=b'$。故该模数已统一足够，虽未达到范数充分界。

### 21.4 有限逆与参数准备分别计费

**命题 21.11（有保护条件的扫描逆）。** 给定上述标准输入，**先检查 $m>N$；否则返回“精度不足”并停止扫描**。通过时，对 $a=0,\ldots,N$ 取

$$
b_a=(s+\lambda_ha)\bmod m,\qquad
\text{保留 }(a,b_a)\iff1\le a+b_a\le N.
\tag{RA.2112}
$$

所得恰为整个 $A_{N,h}(s)$。有有效同源来源及统一证书时，唯一成员是实际计数；未认证单射时仍可列候选，但同样必须先通过 $m>N$。

证明。任一允许来源的 $b$ 满足 $0\le b\le N<m$，因此同余式唯一给出 $b=b_a$，必被保留；每个保留对反过来满足来源界和记录式。证毕。零候选只说明所声明输入不相容，不能判定哪项承诺错误；多候选表示尚不能唯一恢复。若单点却无统一证书，只对本次观测纤维声明恢复。

保护条件有实际作用：$N=m=11,\lambda_1=4$，实际来源 $(0,11)$ 的 $s=0$。若去掉保护条件，$a=0$ 只扫描到 $(0,0)$ 并因空对而丢弃，漏掉真实来源。本节在 $m\le N$ 时只返回精度不足，不另设低精度恢复路线。

令 $n=\lceil\log_2(N+1)\rceil$。从 $b_0=s$ 开始用一次模加生成下一项；因为两个加数都小于 $m$，至多减去一次 $m$。每行加法、比较和计数花 $O(L)$ 位工作，故总计 $O((N+1)L)$，工作空间 $O(L+n)$，不含输入、保留的多候选输出及外部证书。完整候选表可流式输出；若全部存储，另付输出空间。这里 $m>N$ 保证 $n=O(L)$。这个界按 $N$ 计，不能称作按二进制输入长度 $\log N$ 的多项式算法。

根准备另按 §19 的简单根递推进行：若 $f(\lambda_j)$ 被 $p^j$ 整除，令

$$
\lambda_{j+1}=\lambda_j+p^jt_j,\qquad
t_j\equiv-\frac{f(\lambda_j)}{p^j}(2\lambda_1-1)^{-1}\pmod p,
\quad0\le t_j<p.
\tag{RA.2113}
$$

固定的导数逆只计算一次。已有认证 $p,\lambda_1$ 时，学校整数算法给保守 $O(hL^2+(\log p)^3)$ 位工作、$O(L)$ 工作空间，保留当前根和幂即可；这是提升和幂准备费用，不是取得 $s$ 的费用。计算 $K_N,B_N$ 花 $O(n^2)$ 位工作，逐次整数幂比较可用保守 $O(hL^2)$ 界；可选式（RA.2111）检验按其 $O(NL)$ 界另计。素性认证、根发现、证书及其验证、参数取得若不是已供应输入，须声明相应表示、算法及价格；这个提升界不覆盖它们。

### 21.5 三种独立授权的取得合同

**约定 21.12（有价取得与计数后导出）。** 以下三个接口是替代合同；存在数学逆不授予其中任何读、写、重置或控制权限。

第一，若明确允许一个精确、无扰动、正确初始化的同源数字提供者，对同一固定 $x$ 和同一相容分支返回 $r_\infty(x)$ 的数字 $d_j\in\{0,\ldots,p-1\}$，则 $h$ 次调用给出

$$
s=\sum_{j=0}^{h-1}d_jp^j\in[0,m),\qquad
\text{取得收费 }\sum_{j=0}^{h-1}c_j.
\tag{RA.2114}
$$

$c_j$ 是合同给出的调用价格；只有同一单位下才相加为该取得费，局部位工作另列。可变二进制 $p$ 的装配可缓存数字后逆序采用学校 Horner 算法，保守花 $O(L^2)$ 位工作、$O(L)$ 工作空间：第 $j$ 个乘法的操作数长度为 $O(j\log p)$ 与 $O(\log p)$，求和为 $O(h^2(\log p)^2)=O(L^2)$。仅当 $p$ 固定时，可将乘常数按线性位工作计，得到 $O(hL)$。若提供者交付预装好的二进制 $s$，转换费用转入提供者合同，不因此消失。加上根准备、可选精度选择、解码及获准写入的费用，才是这条路线的账；完整精度单射没有实现或初始化这个提供者。

第二，若实际树的有效完整语法已获准可读，则直接遍历计数。$\ell\le N$ 片叶的满二叉树有 $2\ell-1$ 个节点（按树归纳），付所声明的节点访问价格及 $O(\ell\log(N+1))$ 计数位工作；流、栈或遍历游标的存储按实际访问方式另计。计数本身已经恢复；沿用 $n=\lceil\log_2(N+1)\rceil$，所得普通二进制 $a,b$ 各至多 $n$ 位。对任意有限 $m=p^h$，先以流式或学校除法将两者约化模 $m$，花 $O(nL)$ 位工作，再对至多 $L$ 位的约化操作数作学校乘法、减法及取模，花 $O(L^2)$，故形成 $s$ 的导出费用为 $O(nL+L^2)$，根准备另计。若 $m>N$，则 $n=O(L)$，恢复 $O(L^2)$ 界；若已供应约化计数且先前约化费用已计入，导出也为 $O(L^2)$。语法计数后的导出不要求 $m>N$，较小模数同样可用。因此标量是导出及维护记录，不是语法访问的替代授权。

第三，若明确允许每次实验重置到同一个实际 $x$、执行正向 $M/G$ 词，并只在终端取得完整 $\gcd(q(wx),H)$，可直接代入既有 [TerminalGcdAcquisitionCost 的取得构造](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost.md)。应选满足 $p^e>N$ 的最小正整数 $e$，而不必取标量模数：

$$
H=p^e>N,\qquad Q\le2e(p-1),\qquad
W_H=(H^2)!+1+2(H-1),\qquad
\text{原语动作数}\le2e(p-1)W_H.
\tag{RA.2115}
$$

应用说明。旧合同来源为任意自然计数对，操作为这里的 $M,G$，每个词从同一原初对开始，唯一回答为终端完整 gcd；故限制到 $C_N$ 不损坏其取得上界。其两个阶段取得 $n_0=q(x)\bmod H$、$n_1=q(Mx)\bmod H$，再用行列式一的逆给 $(a,b)=(5n_0-3n_1,-3n_0+2n_1)\bmod H$。标准代表因 $a,b\le N<H$ 就是实际整数计数，随后形成所需任意有限 $r_h$。旧正词构造在两个阶段 $k=0,1$ 的长度至多 $(H^2)!+k+2(H-1)$，给出上式。这里仅作假设完整的代入，不重证取得定理，也不把它对无限制模组成任务的最优查询数转移为有界标量任务的最优值。

式（RA.2115）的 $Q$ 数查询而非位工作；需另付重置、终端读取、gcd、词准备、回答后处理、控制器、计数解码、标量导出及写入。若按自然整数计数执行，每一步叶数 $S$ 至多变成 $2S+1$，单词中的数长至多 $O(W_H+\log(N+1))$，故可另给 $O(QW_H(W_H+\log(N+1)))$ 的保守加法位工作界；这不包含真实树改写或重置费用。阶乘长度使这条路线不能据查询数称作高效取得，实验中间来源也不要求留在 $C_N$。

若仪器只允许终端读取模 $m$ 的完整 gcd，使用上述较小 $H$ 还须 $H\mid m$，并允许执行按 $H$ 构造的相同正词及收费后处理：

$$
\gcd(\gcd(q(wx),m),H)=\gcd(q(wx),H).
\tag{RA.2116}
$$

这是因为 $H\mid m$ 时，共同约数逐素数取最小指数即相同。统一足够的 $m=p^h>N$ 保证 $e\le h$；若不整除便没有这项转移。后处理不新增免费的 $q$ 读数或同源重置权限。

例如 $p=11,N=10$，相容 $\lambda_2=37$ 在模 $121$ 下仍把 $(0,10)$ 与 $(3,0)$ 合并为 $10$，而模十一容量也不足；模 $1331>B_{10}=125$ 足够，所以标量统一需要三位。获准 gcd 路线的两个组成坐标模 $H=11$ 已够恢复计数，把所引用构造的查询上界由 $60$ 减为 $20$。这只比较这两个代入的查询上界，不比较实际时耗，不断言 $20$ 最优，也不把一个标量自动视作更少的总记忆。

### 21.6 正确初始化、有限时域与长期恢复边界

来源界认证、精确同源取得及正确写入、操作下的适用界是三项独立义务。任何允许 $x=(a,b)$ 与超界 $(a+m,b)$ 都有相同 $e_h$；因此即使扫描得到单点，也不能认证真实来源满足 $N$。§20 的式（RA.2013）又说明错误种子不被自主维护修复。

正确取得并写入后，复用式（RA.2003）的维护：

$$
U_M(s)=(1-\lambda_h)s\pmod m,\qquad
U_G(s)=s-\lambda_h\pmod m,\qquad
e_h(Ox)=U_O(e_h(x)).
\tag{RA.2117}
$$

当 $x,Ox\in C_B$ 且精度对所声明的 $B$ 足够时，$d_{B,h}(U_O(e_h(x)))=Ox$。这才把已取得的观察边界接成计数任务的记忆：更新器只读已有记录和已声明操作名，有限逆恢复当前计数与数量。模更新本身全域有效，但 $C_N$ 并不闭合，例如 $G(N,0)=(N+1,0)$、$M(0,N)=(N,N)$。

**命题 21.13（声明时域下的有界逆）。** 若从 $C_N$ 开始，执行至多 $k$ 次已声明的 $M/G$，则全部中间实际计数属于 $C_{N_k}$，其中

$$
N_j=2^j(N+1)-1,\qquad0\le j\le k.
\tag{RA.2118}
$$

证明。非空性由两个操作保持。$M$ 后总数为 $a+2b\le2(a+b)$，$G$ 后为 $a+b+1\le2(a+b)+1$；统一用 $S_{j+1}\le2S_j+1$，从 $S_0\le N$ 归纳得 $S_j\le N_j$。证毕。先为 $N_k$ 选择足够精度，按授权正确取得并写入原初同源记录，式（RA.2117）逐步保持正确性，扫描逆遂在整个声明时域可用。若事后扩大界或精度，则须另有正确高层初始化或获准从当前来源重新取得；低层维护不能制造新数字。模更新、来源闭包及有限逆的保证不能混作同一件事。

这里的 $L$ 位标量与解码工作位不包含来源树、提供者内部状态、参数证书及全部控制硬件。操作词或有限时域若用于某个计数任务，是另外供应的数据，不由当前计数倒推出历史。$\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$ 已有同一计数；括号、路径、见证及历史也未被恢复。

本节的有限逆是既有范数、容量和纤维下降机制在当前受限来源上的普通数学应用。FIB 卷的完整模行为及目标锁定约数探针（§§272–273）各有自己的观察与取得假设，不授予这里的标量数字接口；方阵 Smith 精度及全域自主容量（§§36、42–43）也不是这条三角来源单标量判据。空间邻接、端口与粘合、拓扑或度量、因果时间，以及这些结构与边界和记忆互相恢复的条件，仍须另给来源关系、观察映射及恢复证明。计数商的有限操作桥不替代这些长期义务。

## 追加锚（本行以下为增补区）


## 22. 一次全局替换的实际节点、单孔边界与来源恢复

本节沿用 [FIB 关系延拓几何定义 1.1、1.3](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) 的自由有序来源、替换和计数；跨卷及 D5 引用固定在提交 `678d9ac377e1215354f6c9f4a99094d947e9d15f`，本卷 §20.5–20.6 的引用固定在提交 `e96860cb1d3b238554ad8a7d13ea3a8bf4995a38`。以下讨论实际树形上的一次替换。

### 22.1 同一来源的节点与单孔对应

**约定 22.1（有序树、出现地址与已记录的一步）。** $\mathcal T$ 是全部非空有限有序二叉树，两个叶标签不同，配对全定义，左右顺序与括号不取商：

$$
\begin{gathered}
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\qquad
E=\langle\beta,\alpha\rangle,\\
\rho(\alpha)=\beta,\qquad \rho(\beta)=E,\qquad
\rho(\langle x,y\rangle)=\langle\rho(x),\rho(y)\rangle.
\end{gathered}
\tag{RA.2201}
$$

固定同一实际来源 $u$ 及当前树 $t=\rho(u)$。历史解释另以正确保留的记录 $\mathsf{rec}_\rho$ 为前提：最后实际动作确是对该 $u$ 施加一次全局 $\rho$。该记录在下述候选观察中只表示动作及此承诺，不含完整源树、外部上下文或更早历史。

节点是有限 $L/R$ 字的实际出现，根为 $\varepsilon$。不同地址即使标签相同也不合并。写 $t|_p$ 为地址 $p$ 的完整子树，$|p|$ 为字长；非根地址 $p=qL$ 或 $qR$ 的父地址为 $p^-=q$。递归定义

$$
\begin{aligned}
\operatorname{Pos}(\alpha)=\operatorname{Pos}(\beta)&=\{\varepsilon\},\\
\operatorname{Pos}(\langle x,y\rangle)
&=\{\varepsilon\}\sqcup L\operatorname{Pos}(x)\sqcup R\operatorname{Pos}(y),\\
\mathcal B(u)&=\{r\in\operatorname{Pos}(u):u|_r=\beta\},\qquad
K(u,p)=\mathbf1_{\{p\in\operatorname{Pos}(u)\}}\quad(p\in\operatorname{Pos}(t)).
\end{aligned}
\tag{RA.2202}
$$

这里 $L\operatorname{Pos}(x)=\{Lq:q\in\operatorname{Pos}(x)\}$，右侧同理。称 $K=1$ 的切口为旧切口，含义是同一地址已在该源树中出现。

纯配对单孔上下文由 $H::=\square\mid\langle H,w\rangle\mid\langle w,H\rangle$、$w\in\mathcal T$ 形成，保留每条实际旁支。对 $p\in\operatorname{Pos}(t)$，删去且只删去 $t|_p$ 得 $C_{t,p}$，其填充满足

$$
\begin{aligned}
C_{t,\varepsilon}[v]&=v,\\
C_{\langle x,y\rangle,Lq}[v]&=\langle C_{x,q}[v],y\rangle,\\
C_{\langle x,y\rangle,Rq}[v]&=\langle x,C_{y,q}[v]\rangle.
\end{aligned}
\tag{RA.2203}
$$

令 $\widehat\rho(H)$ 固定唯一孔并将每条旁支 $w$ 换成 $\rho(w)$。这些上下文的组合语义复用 [StrictOneHoleContexts](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean) 的 `Generator`、`contextDenote` 和 `forall_contexts_iff_words`：取二元操作为 $\operatorname{some}(\langle x,y\rangle)$，固定参数就是实际旁支。其一般强同余结论 `contextual_equivalence_is_greatest` 不另证明；像成员测试是成功后的布尔读数，假读数不等于配对失败。

**命题 22.2（实际替换的节点与孔实现）。** 对每个 $u\in\mathcal T$，令 $t=\rho(u)$。对每个 $p\in\operatorname{Pos}(t)$，非根切口的新旧归属只由其直接父节点是否为扩张块 $E$ 决定：

$$
\boxed{K(u,p)=1\iff
p=\varepsilon\ \text{或}\ \bigl(p\ne\varepsilon\ \text{且}\ t|_{p^-}\ne E\bigr).}
\tag{RA.2204}
$$

具体地，存在以下不交节点分解；旧节点的嵌入就是同地址映射 $p\mapsto p$：

$$
\operatorname{Pos}(\rho(u))
=\operatorname{Pos}(u)
\sqcup\{rL:r\in\mathcal B(u)\}
\sqcup\{rR:r\in\mathcal B(u)\}.
\tag{RA.2205}
$$

对同一 $u$ 的每个旧切口 $p\in\operatorname{Pos}(u)$，子树及单孔上下文都按该地址对应，且对每个 $v\in\mathcal T$ 有

$$
\begin{gathered}
(\rho(u))|_p=\rho(u|_p),\qquad
C_{\rho(u),p}=\widehat\rho(C_{u,p}),\\
\boxed{\rho(C_{u,p}[v])=C_{\rho(u),p}[\rho(v)].}
\end{gathered}
\tag{RA.2206}
$$

证明。先确定本次替换的像语法。令 $\mathcal R=\rho(\mathcal T)$。它恰是由下面三个产生式生成的最小集合；相应解析在像上唯一：

$$
\begin{gathered}
\mathcal R::=\beta\mid E\mid\langle\mathcal R,\mathcal R\rangle,\qquad
\alpha\notin\mathcal R,\\
\delta(\beta)=\alpha,\quad \delta(E)=\beta,\quad
\delta(\langle x,y\rangle)=\langle\delta(x),\delta(y)\rangle
\quad(x,y\in\mathcal R),\\
\delta(\rho(u))=u,\qquad \rho(\delta(t))=t\quad(t\in\mathcal R).
\end{gathered}
\tag{RA.2207}
$$

源树结构归纳将每个像放入该语法。语法不产生叶 $\alpha$，故特殊块 $E$ 的右孩子不在语法中，$E$ 不能同时按一般配对产生式解析；叶、特殊块和一般配对三种情形不交。$\delta$ 在一般配对处递归到严格更小的有限子树。语法归纳给出每个生成树的原像及 $\rho\delta=\operatorname{id}$，源树归纳给出 $\delta\rho=\operatorname{id}$。这证明像的准确性、唯一解析和 $\rho$ 的单射性；这里的解析只为具体节点论证提供支持。

再对 $u$ 归纳。源 $\alpha$ 只有旧根，像为叶 $\beta$；源 $\beta$ 的根仍在原地址，像为 $E$，恰多出左右两个孩子。源为 $\langle x,y\rangle$ 时，保留根并分别给两子树的归纳分解加前缀 $L,R$，即得（RA.2205）。源叶没有后代，不同源叶地址互不为前缀，所以新增地址既不与旧地址相交，也不彼此混同。旧父子边及左右次序都保留；源 $\beta$ 的旧根由叶变为分支，故嵌入不声称保留标签或叶性。

同一归纳在旧地址上给出子树等式。因此输出中每个 $E$ 出现的根恰对应一个源 $\beta$ 叶：源 $\alpha$ 的像是 $\beta$；源配对的像有两个 $\mathcal R$ 子树，右子树不可能为 $\alpha$；新增节点本身都是叶。于是 $E$ 的两个孩子恰为新增节点，旧非根节点的父节点必来自源配对且其像不等于 $E$。根总是旧节点，得到（RA.2204）。

最后沿旧地址证明上下文等式。根孔两侧均为 $\square$；若 $u=\langle x,y\rangle$、$p=Lq$，则
$\widehat\rho(C_{u,p})=\langle\widehat\rho(C_{x,q}),\rho(y)\rangle=C_{\rho(u),Lq}$，右孔同理。再按上下文构造归纳：孔处恒等，左右包裹处使用（RA.2201），得 $\rho(H[v])=\widehat\rho(H)[\rho(v)]$ 对每个 $v$ 成立；代入已对应的实际上下文即得（RA.2206）。它覆盖根、源 $\alpha$ 叶、源 $\beta$ 的旧根和任意深度的源内部节点。新增地址 $rL,rR$ 不在 $\operatorname{Pos}(u)$ 中，$C_{u,rL},C_{u,rR}$ 未定义；输出孔仍可合法填充。证毕。

### 22.2 像测试推论与外部兄弟关系

**推论 22.3（两项像测试及其边界）。** 在命题 22.2 的同源承诺下，定义

$$
I(t,p)=\mathbf1_{\mathcal R}(t|_p),\qquad
J(t,p)=\mathbf1_{\mathcal R}(C_{t,p}[E]),\qquad
\eta(t,p)=(I(t,p),J(t,p)).
\tag{RA.2208}
$$

所有输出切口恰有下列三类，且 $K(u,p)=1$ 当且仅当 $\eta(t,p)=(1,1)$：

| §22 切口来源 | 完整焦点 $t|_p$ | $I$ | $J$ |
| --- | --- | --- | --- |
| 旧节点 $p\in\operatorname{Pos}(u)$ | $\rho(u|_p)$ | 1 | 1 |
| 新左孩子 $p=rL$，$r\in\mathcal B(u)$ | $\beta$ | 1 | 0 |
| 新右孩子 $p=rR$，$r\in\mathcal B(u)$ | $\alpha$ | 0 | 1 |

证明。旧切口的焦点由（RA.2206）属于 $\mathcal R$；取 $v=\beta$，又得 $C_{t,p}[E]=\rho(C_{u,p}[\beta])\in\mathcal R$。

新左切口 $rL$ 的焦点为 $\beta$，填入 $E$ 后在旧地址 $r$ 形成 $X=\langle E,\alpha\rangle$。$X$ 不等于 $E$，且右孩子不在 $\mathcal R$，所以 $X\notin\mathcal R$。还须排除祖先重新解析的吸收：若 $X$ 是不属于 $\mathcal R$ 的复合树，则其任何直接祖先 $\langle X,s\rangle$ 或 $\langle s,X\rangle$ 都不能等于两个叶组成的 $E$，也不能按 $\langle\mathcal R,\mathcal R\rangle$ 解析；祖先仍是像外复合树。沿有限祖先链归纳，这个缺陷一直传到根，包括 $r=\varepsilon$ 时的零层祖先情形。因此整个新左填充在像外。

新右切口 $rR$ 的焦点是像外叶 $\alpha$，填入 $E$ 却使旧地址 $r$ 的块成为 $\langle\beta,E\rangle=\rho(\langle\alpha,\beta\rangle)$。在旧切口 $r$ 应用（RA.2206），得
$C_{t,rR}[E]=\rho(C_{u,r}[\langle\alpha,\beta\rangle])\in\mathcal R$。此像的原像改变了源 $r$ 处的叶，并没有在实际旧源 $u$ 中提供 $rR$ 孔。节点分解穷尽三类，故 $(0,0)$ 不出现。

根恒为旧切口，整树替成 $E$ 仍在像中。源 $\alpha$ 的唯一输出切口为旧根 $\beta$；源 $\beta$ 的输出 $E$ 在根、$L$、$R$ 分别给 $(1,1),(1,0),(0,1)$。旧内部节点及旧两类叶已经由任意旧地址的运输式覆盖。新左例说明单独 $I$ 不能分类，新右例说明单独 $J$ 不能分类；这是这项合取判据的分量敏感性，$K$ 本身就是一位目标，（RA.2204）也直接给一项布尔判据，因而不能推出所有表示的两位下界。

非吸收论证只用像外复合块，不能换成无条件反射 $H[x]\in\mathcal R\Rightarrow x\in\mathcal R$。实际取 $u=\langle\alpha,\alpha\rangle$、$t=\langle\beta,\beta\rangle$、旧孔 $p=R$，有 $C_{t,R}[\alpha]=E\in\mathcal R$ 而 $\alpha\notin\mathcal R$；解码后的源为 $\beta$，已没有原来的 $R$ 孔。新右孩子的像外焦点同样可以由父节点吸收到 $E$。这不影响（RA.2206）对 $\rho(v)$ 填充的限定。证毕。

进一步，令 $d(t,p)=1$ 恰当 $p=qL$ 且右兄弟 $t|_{qR}$ 为叶 $\alpha$，其余情形（包括根）为零。则

$$
I(t,p)=\mathbf1_{\{t|_p\ne\alpha\}},\qquad
J(t,p)=1-d(t,p),\qquad
K(u,p)=I(t,p)(1-d(t,p)).
\tag{RA.2209}
$$

证明。对像语法归纳：$E$ 的孩子都是叶，一般配对的复合真子树由归纳假设处理，故每个输出复合子树都在 $\mathcal R$；唯一可能的像外子树是特殊块右孩子 $\alpha$。而输出中右兄弟为 $\alpha$ 的左切口恰为 $E$ 的新左孩子。故前式及后两式分别由像语法和三类表得到。候选观察若已保留完整焦点，就已决定 $I$；所需补充可以只取外部兄弟谓词 $d$。这只是集合层面的充分支持观察，未断言已取得兄弟地址或其读数。

### 22.3 相同候选观察下的实际分离对

**命题 22.4（计数、叶序与完整焦点仍可遗漏源节点归属）。** 写 $c(t)=(a,b)$ 为两类叶计数，$q(c(t))=2a+3b$；有序叶序满足 $\operatorname{fr}(\alpha)=\alpha$、$\operatorname{fr}(\beta)=\beta$，配对时依左右顺序拼接。取实际联合域及候选投影

$$
\begin{gathered}
\mathcal X=\{(u,p):u\in\mathcal T,\ p\in\operatorname{Pos}(\rho(u))\},\\
O(u,p)=\bigl(c(t),\operatorname{fr}(t),p,t|_p,|p|,\mathsf{rec}_\rho\bigr),
\qquad t=\rho(u).
\end{gathered}
\tag{RA.2210}
$$

即使再给源计数和源叶序，也不能从这个投影恢复 $K$。它只是一项声明的候选观察，不限制完整观察者已获档案中的其他证据。

证明。令 $B=\beta$，取

$$
\begin{aligned}
U&=\langle\langle\alpha,\beta\rangle,\langle\alpha,\beta\rangle\rangle,&
V&=\langle\langle\langle\alpha,\beta\rangle,\alpha\rangle,\beta\rangle,\\
S=\rho(U)&=\langle\langle B,E\rangle,\langle B,E\rangle\rangle,&
T=\rho(V)&=\langle\langle\langle B,E\rangle,B\rangle,E\rangle,\qquad p=RL.
\end{aligned}
\tag{RA.2211}
$$

每条联合记录都由它自己的同一实际源树经同一个全局 $\rho$ 取得，没有拼接独立边缘。直接按树计算得

$$
\begin{gathered}
c(U)=c(V)=(2,2),\qquad
\operatorname{fr}(U)=\operatorname{fr}(V)=\alpha\beta\alpha\beta,\\
c(S)=c(T)=(2,4),\qquad q(c(S))=q(c(T))=16,\\
\operatorname{fr}(S)=\operatorname{fr}(T)=\beta\beta\alpha\beta\beta\alpha,\qquad
S|_{RL}=T|_{RL}=B,\quad |RL|=2,\\
O(U,RL)=O(V,RL),\qquad K(U,RL)=1,\quad K(V,RL)=0.
\end{gathered}
\tag{RA.2212}
$$

在 $U$ 中 $RL$ 是右配对的左叶 $\alpha$；在 $V$ 中右孩子只是叶 $\beta$，没有 $RL$ 地址，$T$ 的 $RL$ 是其扩张所新增的左孩子。对应的父子树分别为 $\langle B,E\rangle$ 与 $E$，与主判据相符。残余上下文为

$$
\begin{aligned}
C_{S,RL}[z]&=\langle\langle B,E\rangle,\langle z,E\rangle\rangle,\\
C_{T,RL}[z]&=\langle\langle\langle B,E\rangle,B\rangle,\langle z,\alpha\rangle\rangle.
\end{aligned}
\tag{RA.2213}
$$

共同填入 $E$，第一式等于
$\rho(\langle\langle\alpha,\beta\rangle,\langle\beta,\beta\rangle\rangle)$，第二式含像外复合块 $\langle E,\alpha\rangle$，不能被祖先吸收。所以两处 $\eta$ 分别为 $(1,1),(1,0)$，外部兄弟谓词分别为零、一。两份填充都仍是合法非空有限树；不同的是额外的像及旧源孔对应性质，不是原始配对合法性。叶序保留了叶标签顺序，却没有保留括号或焦点与父节点的关系。

现直接应用既有 [TargetRecoveryCriterion](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean) 的 `target_recovery_criterion`，取状态域 $\mathcal X$、过程 $O$、目标 $K$；$\mathcal X$ 由 $(\alpha,\varepsilon)$ 居住。上述同纤维异目标对排除了 $K=f\circ O$。若只在实际观察像上表述，则使用 [HistoryPayloadFactorization](../../../D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.lean) 的 `ker_beta_subset_ker_payload_iff_unique_factorization`。这里引用已有恢复判据，不另立一般恢复结果。证毕。

### 22.4 已获完整码、动作记录与恢复范围

像语法给每个 $t\in\mathcal R$ 唯一的数学原像 $\delta(t)$；只有在约定 22.1 的真实最后动作与同源承诺下，它才等于实际立即前态 $u$。单凭 $E\in\mathcal R$ 不能判定它由替换取得还是由直接配对构成。即使最后动作确为 $\rho$，历史 $\beta\xrightarrow{\rho}E$ 与 $\alpha\xrightarrow{\rho}\beta\xrightarrow{\rho}E$ 仍有相同末态、最后动作与立即前态，却有不同的更早历史。初态、步数或历史档案是额外条件。

已经取得当前实际树的有效完整码时，复用 [FIB 原子关系生成定义 9.1、定理 9.2–9.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的结构解码或全部路径重建，即可恢复 $t$，再用（RA.2207）取得 $u$ 并判断 $p\in\operatorname{Pos}(u)$。另一既有完整码是 [SourceTreeEncoding](../../../D5/S0/History/Spacetime/SourceTreeEncoding.lean)：将 $\alpha,\beta$ 分别嵌入 `FreeMagma Nat` 的 `.of 0`、`.of 1`，配对嵌入 `.mul`，使用 `sourceCode_injective`、`source_code_equiv`、`decodeSource_encode`。完整有序树保留括号及可重建的出现地址，相同叶标识不合并出现。已有完整源码也直接足够。本节不重复编码或完整码恢复理论；这条充分路线以码已经取得及最后动作记录正确为前提。

数学填充、像测试、父兄弟判据及原像解码均不授予实际读、计算、复制、写、复位、回滚或逆向执行权限。$\eta$ 的两项输出与 $K$ 的一项输出，不计算取得支持树或上下文、验证记录、定位地址、暂存及持久保存的成本；维护已有正确记录也不替代取得与初始化。沿用本卷 §20.5–20.6：完整计数精度仍不恢复树形，取得与维护须分开计费；持续操作下的更新代价及保持充分性的条件还须单独给出。

当前 $K$ 的充分支持观察还不构成持续任务的自主更新记录。[递归关系观察定理 120.4–120.5](RECURSIVE_RELATIONAL_OBSERVATION.md) 已给出指定操作、全部未来响应及可达确定实现的相应条件；这里没有为 $O$、$\eta$ 或 $d$ 证明那些更新交织条件，也没有有限观察机或最小状态结论。全部有限树组成无限载体，单棵树有限不能代替整个残余响应族有限。

在这个限定模型中，同地址出现关系给组合空间的位置，单孔上下文给可填充边界，正确动作记录把两者连接到一次变化，外部兄弟信息则补足当前归属任务遗漏的关系。空间、时间、边界与记忆的完整关系恢复目标仍然保留；多孔共同来源、持续动态充分性、更早实际历史以及物理空间和时间的互相恢复，各需自己的来源、访问、更新与结构条件，不能由本节的一步单孔结论推出。

## 追加锚（本行以下为增补区）
## 23. 固定来源的出生边界、联合像与有限来源证书

本节把同一出现的当前有序边界接到相对于固定初态的首次存在时刻，并刻画全部出生坐标的共同来源。沿用本卷 §22 的实际地址、单孔运输及唯一一步解析，特别是（RA.2205）–（RA.2207）和（RA.2211）的两个来源；§22 所属快照是 `5c337f8687016b79bed0a15fe5819d8edb274a80`。其余跨卷与 D5 接口的引用固定在 `587d5ac330548db24a7df576c758f26523c9a699`。以下给出普通数学证明；声明源码的引用不表示本节已经过 Lean 核验。

### 23.1 固定初态、绝对出生与父边界

**定义 23.1（来源、操作及查询域）。** 取自由有限非空有序满二叉树，不对左右次序、括号或同标签出现取商：

$$
\begin{gathered}
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad E=\langle\beta,\alpha\rangle,\\
\rho(\alpha)=\beta,\quad \rho(\beta)=E,\quad
\rho(\langle x,y\rangle)=\langle\rho(x),\rho(y)\rangle,\\
\mathcal P=\{L,R\}^{*},\qquad t_j=\rho^j(u)\quad(j\in\mathbb N).
\end{gathered}
\tag{RA.2301}
$$

配对是构造来源的运算；演化另行指定为全局 $\rho$。固定一个 $u$ 为纪元零来源和根 $\varepsilon$，不允许中途编辑、重选来源、移根、空间平移、共享出现识别或纪元重置。读取、控制和档案追加不改变来源。$\operatorname{Pos}$ 与 $t|_p$ 使用（RA.2202）的实际出现地址。空间祖先是地址前缀，时间保持边是 $(j,p)\mapsto(j+1,p)$；不为初态已有分支赋予纪元零以前的装配时间。

**引理 23.2（每个有限地址的出生及分支延迟）。** 每个 $p\in\mathcal P$ 最终出现。定义

$$
\begin{gathered}
b_u(p)=\min\{j\ge0:p\in\operatorname{Pos}(t_j)\},\qquad
b_u(\varepsilon)=0,\qquad 0\le b_u(p)\le2|p|,\\
p\in\operatorname{Pos}(t_k)\iff b_u(p)\le k\qquad(k\in\mathbb N).
\end{gathered}
\tag{RA.2302}
$$

两个孩子有相同出生时刻，记 $e_u(p)=b_u(pL)=b_u(pR)$。若 $b_u(p)=0$，则按初态在 $p$ 的标签为配对、$\beta$、$\alpha$，$e_u(p)$ 分别为 $0,1,2$。若 $b_u(p)>0$，则 $p$ 末字母为 $L$ 时 $e_u(p)=b_u(p)+1$，末字母为 $R$ 时 $e_u(p)=b_u(p)+2$。

证明。由（RA.2205），所有已有地址保持，只在旧 $\beta$ 叶下同时新添两个孩子，新左孩子为 $\beta$，新右孩子为 $\alpha$。从任一已出现节点出发，若当前为配对，其孩子已在；若为 $\beta$，下一步成为 $E$；若为 $\alpha$，先成为 $\beta$，再成为 $E$。故孩子至迟两步内出现。以地址长度归纳，根在零时刻出现，孩子至迟在 $2|p|+2$ 出现，证明最终存在与界，从而最小值有定义。已有地址的保持给出存在集合是从最小值起的全部整数，得历史存在等价式。初态三种标签的孩子时刻直接由上述变化得到；一个正出生节点由新添规则只能是其末字母决定的 $\beta$ 或 $\alpha$，后续第一次分支延迟恰为一或二。这也覆盖初态内部节点、初态两类叶以及任意深度的新孩子。证毕。

一般单调过滤中的首次阶段及后续存在复用 [BirthStageFiltration](../../../D5/S3/ConceptDynamics/DagSemantics/BirthStageFiltration.lean) 的 `birthStage_unique`、`mem_of_birthStage_le`；这里承重的额外内容是具体孩子延迟及 $2|p|$ 界。

令实际查询域、出生目标与历史准入为

$$
\begin{gathered}
\mathcal X=\{(u,n,p):u\in\mathcal T,\ n\in\mathbb N,
\ p\in\operatorname{Pos}(t_n)\},\qquad F(u,n,p)=b_u(p),\\
Q_k(u,p)=\mathbf1_{\{b_u(p)\le k\}}.
\end{gathered}
\tag{RA.2303}
$$

一个历史目标 $n_*\le n$ 可以单独固定；所问的 $k\le n_*$ 不随以后观察纪元改变。最新前态准入在 $j\ge1$、$p\in\operatorname{Pos}(t_j)$ 的守卫下是 $Q_{j-1}$。首次存在时刻是 $b$；首次为真的最新前态位，对正出生节点是在 $b+1$，不能把两者混为一谈。

**定义 23.3（闭前缀及有限右边界时钟）。** $P_r(v)$ 给出每个相对地址 $a$、$|a|\le r$ 的标签，值域为 $\{\alpha,\beta,\mathsf{pair},\mathsf{absent}\}$；深度 $r$ 的标签本身可见，叶下面全部为不存在。对有限树定义

$$
\kappa(\alpha)=0,\qquad\kappa(\beta)=1,\qquad
\kappa(\langle x,y\rangle)=2+\kappa(y).
\tag{RA.2304}
$$

它等于右端叶深度的两倍，再在该叶为 $\beta$ 时加一。对合法非根查询，$q=p^-$ 是实际配对节点，声明较小观察

$$
O_{n,r}(u,p)=(n,p,P_r(t_n|_q)),\qquad
s(u,n,p)=\min(n+2,\kappa(t_n|_q)).
\tag{RA.2305}
$$

完整已获档案是另一个仍保留的参数，含全部已取得的出生、祖先和来源证据；这里的 $O_{n,r}$ 是用于比较的投影，不是完整状态的定义。

**定理 23.4（父边界恢复绝对出生）。** 对每个 $(u,n,p)\in\mathcal X$ 的非根 $p$，

$$
\boxed{\ b_u(p)=\max(0,n+2-\kappa(t_n|_{p^-}))=n+2-s(u,n,p).\ }
\tag{RA.2306}
$$

根的出生恒为零。给定这个出生，所有历史准入 $Q_k$ 由（RA.2302）恢复。

证明。先对有限树作结构归纳。叶 $\alpha$ 的时钟由零变一；叶 $\beta$ 的像是 $E$，时钟由一变二。配对情形使用右子树归纳假设：

$$
\kappa(\rho(\langle x,y\rangle))
=2+\kappa(\rho(y))=2+\kappa(y)+1.
\tag{RA.2307}
$$

所以对所有有限 $v$、$m\ge0$，$\kappa(\rho^m(v))=\kappa(v)+m$，后式由 $m$ 归纳。

若 $b_u(p)=0$，父地址 $q$ 初态就是配对。由（RA.2206）沿同地址迭代，$t_n|_q=\rho^n(u|_q)$，故其时钟至少为 $n+2$，右侧为零。若 $j=b_u(p)>0$，在 $j-1$ 时 $p$ 不在，在 $j$ 时出现；（RA.2205）使它恰为某旧 $\beta$ 叶的左或右新孩子，因此其直接父 $q$ 在 $j$ 时恰为 $E$。此后父地址保持，同地址运输给

$$
t_n|_q=\rho^{n-j}(E),\qquad
\kappa(t_n|_q)=2+n-j.
\tag{RA.2308}
$$

代入得到 $j$。两种情况穷尽合法查询，包括在当前时刻刚出生的节点。$n=0$ 时所有合法地址都是初始地址，无需读取父边界即可答零；根没有父地址，单独答零。父节点对合法非根查询确为配对，因而时钟至少二且结果在 $0..n$。若 $p$ 当前不存在，查询应返回不存在；本式不延伸到它，尤其不补造一个缺失的父子树。证毕。

在固定 $n,p$ 的实际像上，$s=n+2-b$ 与 $b=n+2-s$ 互相决定。这是这项任务的信息等价，不是通用表示最小性。对带正确来源、根、绝对纪元、地址及完整支持记录的实际查询载体，公式给出观察到出生的纤维恒定性；直接复用 [HistoryPayloadFactorization](../../../D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.lean) 的 `ker_beta_subset_ker_payload_iff_unique_factorization`。它允许空载体并只在实际观察像给唯一因子；不把因子方向反转为出生恢复档案。完整查询域由 $(\alpha,0,\varepsilon)$ 居住，固定 $n\ge1$ 的非根域由 $(\beta,n,L)$ 居住，故需要全观察值域上的存在版本时也满足 [TargetRecoveryCriterion](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean) 的 `target_recovery_criterion` 的居住前提。

### 23.2 同一对来源的全部纪元与尖锐半径

**定理 23.5（声明的父前缀族中的准确半径）。** 对每个 $n\ge1$，

$$
r_n=\lceil n/2\rceil
\tag{RA.2309}
$$

足以由 $O_{n,r_n}$ 恢复合法非根查询的出生；每个 $0\le r<r_n$ 都不能在全部此类查询上恢复哪怕谓词 $b=0$。$n=0$ 的合法查询及所有根查询的答案恒定，不需要边界读数。

证明充分性。沿父树的右路径读到深度 $r_n$。若先遇到深度 $d\le r_n$ 的叶，其标签给出准确时钟 $2d+\mathbf1_{\{\beta\}}$，从而给出上限截断 $s$；不必再访问不存在的后代。若深度 $r_n$ 仍为配对，右端叶至少在下一层，故

$$
\kappa\ge2(r_n+1)\ge n+2,
\tag{RA.2310}
$$

截断已经等于 $n+2$。特别地，$n=2r_n$ 时下界是 $n+2$，$n=2r_n-1$ 时是 $n+3$。可见深度上的叶也必须读其标签；它同样确定截断。此读法只使用 $P_{r_n}$ 中一条路径。

证明必要性。固定（RA.2211）的两个有限来源和同一地址，不随 $n$ 重选：

$$
\begin{aligned}
U&=\langle\langle\alpha,\beta\rangle,\langle\alpha,\beta\rangle\rangle,\\
V&=\langle\langle\langle\alpha,\beta\rangle,\alpha\rangle,\beta\rangle,
\qquad p=RL,\qquad T_m=\rho^m(\alpha).
\end{aligned}
\tag{RA.2311}
$$

$RL$ 在 $U$ 初态存在，在 $V$ 第一步才存在，故对每个 $n\ge1$ 查询均合法，出生分别为零和一。复用 [FIB 原子关系生成定义 3.1、定理 3.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的 $T_0=\alpha,T_1=\beta$ 及 $T_m=\langle T_{m-1},T_{m-2}\rangle$（$m\ge2$），同地址运输得到

$$
\begin{gathered}
(\rho^nU)|_p=(\rho^nV)|_p=T_n,\\
(\rho^nU)|_R=\langle T_n,T_{n+1}\rangle,\qquad
(\rho^nV)|_R=T_{n+1}=\langle T_n,T_{n-1}\rangle.
\end{gathered}
\tag{RA.2312}
$$

令 $d_m$ 为 $T_m$ 的最小叶深度。$d_0=d_1=0$，递推给
$d_m=1+\min(d_{m-1},d_{m-2})=\lfloor m/2\rfloor$，最后一个等式对偶数、奇数分别代入归纳假设成立。所以所有严格低于 $\lfloor m/2\rfloor$ 的深度标签都是配对。

当 $r_n=1$（$n=1,2$），两父树的深度零标签都是配对。若 $r_n\ge2$，两父树左支完全相同；右支在父深度至多 $r_n-1$ 的观察，只涉及子树深度至多 $r_n-2$。较浅的 $T_{n-1}$ 的最小叶深度已经是 $r_n-1$：$n=2r_n$ 或 $2r_n-1$ 两种情形都如此。因此右支这些坐标全部为配对，较深的 $T_{n+1}$ 也全部为配对。两父前缀通过深度 $r_n-1$ 完全相等，包括每个被观察坐标，没有通过删除标签得到相等。

深度 $r_n$ 上的右端坐标则确实区分它们。反复使用右支指标减二，若 $n=2r_n$，两父树在 $R^{r_n}$ 的子树分别为 $T_3$ 与 $T_1$，标签为配对与 $\beta$；若 $n=2r_n-1$，分别为 $T_2$ 与 $T_0$，标签为配对与 $\alpha$。这包含 $n=1,2$ 的起点。故 $r_n$ 是所声明族的准确最坏半径；更小半径的同观察异目标对排除恢复器。

两来源的叶序都是 $\alpha\beta\alpha\beta$。按来源结构，$\operatorname{fr}\rho=\sigma\operatorname{fr}$，其中 $\sigma(\alpha)=\beta$、$\sigma(\beta)=\beta\alpha$；配对处只串接左右叶序。迭代得每个纪元叶序相同，计数亦相同，后者也直接复用母卷定理 3.4。因此即使增加初始及全部纪元的准确叶序、计数和当前完整焦点，分离对仍在较小投影的同纤维中。只记录同一个动作名、时刻及成功承诺的盲 $\rho$ 收据可以匹配；包含来源码、构造读取或其他区分数据的收据与档案不据此相等。证毕。

任意固定半径在无界后续纪元上失败，因为同一 $U,V$ 对在所有 $n>2r$ 仍给反例。对于完整保留档案 $c$，$(O_{n,r_n},c)$ 的充分性仍成立；若 $c$ 已含正确绑定的出生或其他区分证据，不再有上述必要性结论。不得删除它来制造相等完整状态。此下界仅为所声明父前缀族的深度界，不是任意探针、信息位、先验记忆或总费用下界，也不是对移动不透明点的祖先任务的下界。

### 23.3 独立出生语法与一个共同来源

**定义 23.6（联合出生场的局部规则）。** 在有限坐标乘积中独立定义

$$
\mathcal D=\prod_{p\in\mathcal P}\{0,\ldots,2|p|\},\qquad
B(u)=(b_u(p))_{p\in\mathcal P}.
\tag{RA.2313}
$$

$\mathcal A\subseteq\mathcal D$ 恰由以下规则组成，所有规则对每个 $p$ 施加；$e_b(p)$ 是两个孩子的共同值：

$$
\begin{gathered}
b(\varepsilon)=0,\qquad b(pL)=b(pR)=e_b(p),\\
b(p)=0\ \Longrightarrow\ e_b(p)\in\{0,1,2\},\\
b(p)>0\ \Longrightarrow\
 e_b(p)=\begin{cases}b(p)+1,&p\text{ 末字母为 }L,\\b(p)+2,&p\text{ 末字母为 }R.\end{cases}
\end{gathered}
\tag{RA.2314}
$$

令 $Z_b=\{p:b(p)=0\}$，$\mathcal A_{\rm fin}=\{b\in\mathcal A:Z_b\text{ 有限}\}$。局部规则及有限性条件都没有引用“存在一个实现来源”。从根开始，每条边使值不减且至多加二，故规则本身也蕴含 $b(p)\le2|p|$；乘积中的界只是规范化。

**定理 23.7（有限来源的准确联合像与构造逆）。** 映射

$$
B:\mathcal T\longrightarrow\mathcal A_{\rm fin}
\tag{RA.2315}
$$

是双射。逆 $D(b)$ 的位置恰为 $Z_b$；在 $p\in Z_b$，$e_b(p)=0,1,2$ 分别给标签配对、$\beta$、$\alpha$。

证明。引理 23.2 给真实出生的全部局部规则，且 $Z_{B(u)}=\operatorname{Pos}(u)$ 有限，证明必要性。

反向取 $b\in\mathcal A_{\rm fin}$。根为零，每条边值不减；正值节点的孩子严格更大。因此零集合前缀闭，不能在一个正值节点之下重新出现零。兄弟等值使每个零节点或者有两个零孩子，或者都没有；$e=0$ 正是前一种情形。$e=1,2$ 的节点没有零孩子，分别赋 $\beta,\alpha$。所得是一个非空有限有序满二叉树 $D(b)$，构造中没有先假定它实现整个场。

按地址长度证明 $b_{D(b)}(p)=b(p)$。根处同为零。假定 $p$ 处相等；若 $b(p)=0$，逆构造标签使其孩子的首次时刻恰为 $e_b(p)$。若 $b(p)>0$，真实出现时的新左或新右标签由 $p$ 末字母决定，其孩子时刻恰为 $b(p)+1$ 或 $b(p)+2$，也是 $e_b(p)$。这同时确定两个孩子，覆盖每个有限地址，故 $B(D(b))=b$。对于原来源 $u$，零集合就是它的实际位置；初始标签也由其真实孩子出生时刻 $0,1,2$ 唯一恢复，故 $D(B(u))=u$。这证明双射及唯一性：全部坐标由同一个构造来源实现，不是各坐标独立挑选代表。证毕。

**推论 23.8（在出生观察中取得的有限耗尽证书）。** 对 $b\in\mathcal A$，

$$
Z_b\text{ 有限}\iff
\exists h\ge1\ \forall p\ (|p|=h\Rightarrow b(p)>0).
\tag{RA.2316}
$$

一旦观察到这样的整层，出生坐标通过深度 $h$ 已唯一决定整个有限初态。

证明。有限 $Z_b$ 有最大深度，取严格更深的 $h\ge1$。反向，若深度 $h$ 全为正，由值不减可知所有更深节点也为正，故 $Z_b$ 被包含在有限集合 $\mathcal P_{<h}$。每个零节点深度至多 $h-1$，它的两个孩子出生值都在已观察范围内，决定其初始标签。深度 $h$ 以下的正值增量全部由末字母决定，故已给证书的任何全场延拓一致。这里是有限联合出生观察上的证书，不是树的额外 End 构造子，也没有使用未观察的种子高度。证毕。

**定理 23.9（全部语义纪元及初始祖先）。** 对 $b\in\mathcal A_{\rm fin}$ 和 $j\ge0$，按如下坐标定义 $H_j(b)$：

$$
\operatorname{tag}_{H_j(b)}(p)=
\begin{cases}
\mathsf{absent},&b(p)>j,\\
\mathsf{pair},&b(p)\le j\text{ 且 }e_b(p)\le j,\\
\beta,&b(p)\le j\text{ 且 }e_b(p)=j+1,\\
\alpha,&b(p)\le j\text{ 且 }e_b(p)=j+2.
\end{cases}
\qquad H_j(b)=\rho^j(D(b)).
\tag{RA.2317}
$$

这些情况穷尽且不交。$p$ 的纪元零祖先是它的最长零出生前缀 $a_b(p)$；若 $p$ 本来存在，$a_b(p)=p$，若后来产生，$a_b(p)$ 是初态的一个叶。正出生非根节点的左右出生见证就是其末字母。

证明。局部规则使 $b(p)\le e_b(p)\le b(p)+2$。对已存在节点，如果孩子已出生，它是配对并永远保持；如果孩子还未出生，差值只能为一或二。初始或新生 $\beta$ 在孩子出生前一时刻为 $\beta$，初始或新生 $\alpha$ 在孩子出生前两时刻为 $\alpha$，下一时刻为 $\beta$。引理的精确分支延迟和定理 23.7 已确定全部首次时刻，故得到三种标签及所述轨道等式。也可直接验其良构性：存在集合前缀闭，孩子同时存在，正是父为配对的条件。根存在，若一个节点不存在其所有后代也不存在。最长零前缀存在于有限的前缀链，唯一；若它后面还有字母，它不能是初态配对，否则下一前缀仍为零。因此它恰为初态叶，而后代由此叶的替换生成。此祖先是初始出现关系，不增加初态以前的事件。证毕。

对固定合法 $n,p$，来源／出生／语义轨道的联合像恰为

$$
\{(D(b),n,p,(H_j(b))_{0\le j\le n},b):
 b\in\mathcal A_{\rm fin},\ b(p)\le n\}.
\tag{RA.2318}
$$

这是一个共同来源的像；实际动作真值、独立收据、完整档案和控制器状态不是这个像从 $b$ 恢复的字段。

### 23.4 独立有限阶段与完成

**定义 23.10（局部阶段与无限树载体）。** 对 $h\ge0$，$S_h$ 是 $\mathcal P_{\le h}$ 上的场，具有坐标界、根零条件，并满足（RA.2314）中孩子都可见的全部规则，即每个 $|p|<h$ 的兄弟等式及该父的局部规则。先定义这个语法集合，再定义实际联合像

$$
A_h=\{B(u)|_{\mathcal P_{\le h}}:u\in\mathcal T\}.
\tag{RA.2319}
$$

连接映射为限制。另定义 $\overline{\mathcal T}$：全部有限或无限的良构有根有序满二叉构造树，用所有有限地址的构造／不存在标签表示；根存在，配对恰有两个存在孩子，叶无孩子，不存在节点无存在后代。它取构造前缀拓扑，无指定点的移动、移根或平移商。$\mathcal A$ 取有限离散坐标的乘积拓扑。

**定理 23.11（有限联合实现、完成与稠密真子集）。** 对全部 $h\ge0$，$A_h=S_h$，每个限制 $A_{h+1}\to A_h$ 满射，而且

$$
\varprojlim_h A_h=\mathcal A.
\tag{RA.2320}
$$

出生映射扩展为同胚 $\overline B:\overline{\mathcal T}\to\mathcal A$；有限来源的像恰为稠密真子集 $\mathcal A_{\rm fin}$。

证明有限阶段。实际出生满足可见规则，所以 $A_h\subseteq S_h$。取 $x\in S_h$，把深度至多 $h$ 的零节点保留。值不减保证零节点的前缀仍为零，兄弟等式保证其内部满二叉结构。对深度小于 $h$ 的零节点，孩子值可见，依次用 $e_x=0,1,2$ 赋配对、$\beta,\alpha$；深度 $h$ 的零节点切为任意 $\alpha$ 或 $\beta$ 叶，因为其孩子出生尚未观察。这构造一个有限来源 $u_x$。按地址长度，与定理 23.7 相同的分支延迟归纳，只对 $|p|\le h$ 使用可见规则，得 $B(u_x)(p)=x(p)$。边界叶标签只影响下一层的出生，没有修改已指定值。$h=0$ 时阶段仅为根零，任一单叶来源均实现。于是反包含成立。给任一 $A_h$ 元素选这个来源，其深度 $h+1$ 出生限制是延拓，故连接映射满射。

一个相容线程在每个坐标 $p$ 的值由任意 $h\ge|p|$ 读取，限制相容保证无关。根规则在零层检查；每个局部规则在 $h\ge|p|+1$ 检查，故所得全场属于 $\mathcal A$。反向，一个 $b\in\mathcal A$ 的全部限制属于 $S_h=A_h$。这完成具体线程识别，不把联合像改成单坐标像的自由乘积。一般线程与分离／实现的包装直接使用 [InverseLimitCompletion](../../../D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean) 的 `stateThread_injective_iff_separates`、`stateThread_bijective_iff_complete_and_separates` 和 [过程几何定理 4.1–4.4](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)。本节已供应它们所需的实际阶段与共同实现。

证明无限来源对应。对任意 $b\in\mathcal A$，同样把零集合赋以 $e_b$ 决定的标签；无需它有限，所得仍满足 $\overline{\mathcal T}$ 的每项有限良构条件，记为 $\overline D(b)$。在无限树上，$\rho$ 的有限坐标定义见下节；引理 23.2 的地址长度归纳只经过一条有限祖先链，仍证明每个地址在至多 $2|p|$ 时出现。因此 $\overline B(v)$ 有定义，且同样的局部延迟归纳给出
$\overline B\overline D=\operatorname{id}$、$\overline D\overline B=\operatorname{id}$。零集合和子出生时刻恢复所有初始标签，故不同来源分离；不需要在无限右脊上求 $\kappa$。

给出精确有限依赖以证明两向连续。$h=0$ 的出生限制恒为根零。$h\ge1$ 时，原来源构造标签通过深度 $h-1$ 足以决定全部深度至多 $h$ 的出生：沿每条地址，只要父初始为配对就继续零出生；第一次初始叶的标签给一或二的分支时刻，后面全部延迟由左右字母决定。所用来源标签都是该地址的严格前缀。反向，出生通过深度 $r+1$ 决定初态构造标签通过深度 $r$：$b(p)>0$ 给初态不存在；$b(p)=0$ 时 $e_b(p)$ 给初态三种构造。两方向每个有限读数都只依赖有限读数，所以是同胚，且有限子空间的拓扑也由此对应。

各局部规则只涉及有限离散坐标，违例有有限见证，故 $\mathcal A$ 在 $\mathcal D$ 中闭。紧有限坐标乘积及闭条件的完成机制沿用过程几何定理 4.3–4.4；如用 [CompactLocalRealization](../../../D5/S3/Observer/Completion/CompactLocalRealization.lean) 的 `compact_local_realization`，其紧载体取 $\mathcal A$ 或同胚的 $\overline{\mathcal T}$，不是有限树集合 $\mathcal T$。每个基本柱邻域只限制有限地址，取覆盖这些地址的某个深度，前面的 $u_x$ 同时实现它们，证明 $\mathcal A_{\rm fin}$ 稠密。

最后全零场 $b_\infty(p)=0$ 满足所有局部规则，零集合是全部 $\mathcal P$，故不属于 $\mathcal A_{\rm fin}$。深度 $h$ 内全部为配对、深度 $h$ 边界切为叶的有限来源，实现其全部出生坐标到深度 $h$；完整全零场却只由无限全配对树实现，任何有限初态都不可能有全部地址。故子集是真子集，有限一致性不等于有限来源实现。这个具体实例也符合 [LocalDescentGlobalCompatibility](../../../D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.lean) 的 `escaping_thread_not_in_global_image` 所区分的局部满射与全局像。证毕。

[来源联合完成卷引理 2.2、定理 2.3、命题 2.4、推论 2.5](FIB_SOURCE_COMPLETION_DYNAMICS.md) 的来源是有限支持非相邻数字地址，读数为数字前缀和组成余数；其无有限 End 结论仍属于该读数族。（RA.2316）是另一种更强有序出生观察上的耗尽证书，不从数字／余数读数获得，也不声称任何无限场由有限来源实现。

### 23.5 前缀自然性与不重置的时间更新

**命题 23.12（闭前缀上的准确替换与纪元求值）。** 对 $v\in\overline{\mathcal T}$，$P_r(\rho(v))$ 仅依赖 $P_r(v)$。在实际良构前缀像上定义 $f_r$：旧坐标标签 $\alpha,\beta,\mathsf{pair}$ 分别变成 $\beta,\mathsf{pair},\mathsf{pair}$；旧不存在坐标 $p$ 仅在其直接父旧标签为 $\beta$ 时变成孩子标签，末字母 $L,R$ 分别给 $\beta,\alpha$，否则仍不存在。根不使用父规则。于是

$$
\begin{gathered}
P_r\rho=f_rP_r,\qquad
\pi_{r,s}f_r=f_s\pi_{r,s}\quad(s\le r),\\
H_j(b)=\rho^j(\overline D(b)),\qquad
H_{j+1}(b)=\rho(H_j(b)),\\
P_rH_{j+1}(b)=f_rP_rH_j(b)\qquad(b\in\mathcal A).
\end{gathered}
\tag{RA.2321}
$$

这里 $H_j$ 对无限场也用（RA.2317）的标签式定义；$P_rH_j$ 只需要出生通过深度 $r+1$。

证明。原有节点的标签变化就是替换规则。一个旧不存在地址在一步里能变成节点，只能是旧 $\beta$ 叶的直接孩子；旧不存在父下面更深的坐标不可能同一步出现。孩子的旧父深度小于它，故所有所需标签都已在 $P_r$ 中。规则逐坐标给出良构前缀，且限制时同坐标使用同标签，证明两个前缀等式；所有深度的结果相容，唯一确定无限树上的 $\rho$，从而无需进行无限递归求值。

对 $H_j$，若 $b(p)>j$ 且 $b(p)=j+1$，其父的孩子时刻就是 $j+1$，父在 $j$ 的标签为 $\beta$，新标签由左右决定；若 $b(p)>j+1$，它仍不存在。已存在时，$e_b(p)\le j$ 的配对保持；$e_b(p)=j+1$ 的 $\beta$ 变为配对；$e_b(p)=j+2$ 的 $\alpha$ 变为 $\beta$。所以标签式逐坐标满足 $\rho H_j=H_{j+1}$。$H_0=\overline D$ 由零骨架与初始标签成立，按 $j$ 归纳即得轨道等式和自然性。每个标签式只读 $b(p)$ 及两个孩子值，给所述多一层的出生依赖。

深度 $r$ 已足够，且不能一般减为 $r-1$（$r\ge1$）：取到深度 $r$ 才分出 $\alpha$ 与 $\beta$ 的两棵有限树，例如同一右梳骨架在末端 $R^r$ 分别赋这两个叶。它们通过深度 $r-1$ 的标签一致，替换后深度 $r$ 标签为 $\beta$ 与配对，仍不同。$r=0$ 需要根标签，两个单叶来源的像根也不同。因此闭前缀约定不需要更深来源前缀，并保留准确的观察深度。证毕。

固定来源的状态推进是 $(j,b)\mapsto(j+1,b)$。对任何已获出生，绝对值、纪元零来源和地址都不改；重新读取合法非根 $p$ 时，$j$ 与父时钟都增加一，（RA.2306）的结果仍相同。另写 $B(\rho(u))$ 则是把当前树指定为新的纪元零来源，属于不同问题，不能替代此更新。一个固定历史目标 $(n_*,p)$ 的准入仍由原 $b(p)\le n_*$ 决定；当 $b(p)>n_*$，该历史位置的子树及孔未定义，而非当前位置的某个伪前态。

### 23.6 完整档案的条件像推论

**推论 23.13（既有部分过程的有限重放实例）。** 固定[过程几何定义 1.1–1.2、定理 3.2–3.5](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) 的一个确定局部读过程 $\mathsf P$，其具名动作含已安装的查询参数。显式参数包括来源身份与纪元零根、初始化绝对纪元 $N_0$、已获根／引用绑定、安装控制和输入、合法端口／引用权限及保留支持、初始控制状态 $M_0$ 以及完整旧档案 $c_0$。除源树外，这个局部过程的初始配置全部显式给定；不得另依赖未列出的环境状态或隐藏权限。初始化及其以前的来源承诺正确是条件；$c_0$ 中已有语义读数与动作依其已声明绑定检查，其他已获字段逐字保留，其合法性仍受原过程合同约束。若它包含须重放的更早过程段，该段从其声明的初态检查，不把它作为任意自由档案。

采用固定有限字母表的无歧义自分隔有限记录编码；无界整数、地址或引用编码为有限字，不假定有限条记录的值域有限。停止标记是实际给定有限迹的末事件，之后没有新事件。把一个停止配置的联合表示写为

$$
(b,N,p,c_0,c,M_0,M),\qquad c=c_0\mathbin{\|}d,
\tag{RA.2322}
$$

其中 $d$ 是全部新事件的有限编码，含已写停止标记。该过程的语义联合像恰由以下条件给出：$b\in\mathcal A_{\rm fin}$，$b(p)\le N$，$c$ 保留完整 $c_0$，并且 $\operatorname{Leg}_{\mathsf P}(b,c,M_0,M,N,p)$ 成立。这里 $\operatorname{Leg}$ 只是原过程的有限逐事件重放，定义如下。

从给定初始化引用和 $M_0,N_0$ 开始，新段的每一步必须是安装的确定策略按当前可访问数据、完整保留记录和控制状态所选的具名动作，满足原过程合法域；每个读或移动使用已取得且在该纪元有效的引用。根绑定来自初始化或声明的根重新取得，子引用只由已获配对节点的有序孩子响应派生；不能凭输入地址制造句柄。来源身份和根不得改变。每个读响应以（RA.2317）在它绑定的绝对纪元和地址核对；每个已宣告出生输出以 $b(p)$ 核对。每个 $\mathsf{ApplyRho}$ 收据只把绝对纪元增加一，实际后继及引用有效期按原执行合同更新；跨纪元旧引用的继续使用必须由该合同明确允许。原 controller/writer 后继给下一 $M$，事件按顺序追加；安装策略所选停止、最终 $N,p,M$ 及停止编码必须相符。声明的合法性、权限、费用或其他标签仍逐项核对，不能由源标签替代。重放中没有“存在某个有限来源或历史实现这些记录”的子句。

证明。在一项符合合同的语义运行中，源出生属于 $\mathcal A_{\rm fin}$，查询守卫成立，完整 writer 给 $c_0$ 的原样保留，每一步给上述重放条件，得必要性。反向，先由定理 23.7 构造唯一 $u=D(b)$；定理 23.9 给每个绝对纪元的真实语义标签。初始化正确和原过程的条件执行合同提供初始配置及允许动作。按新迹事件数归纳：确定控制选择和合法域检查给下一步允许；标签式给正确读数，原后继／引用规则给下一配置，完整 writer 给下一档案。检查停止步及末状态完成有限运行，得到充分性。旧段若有既有检查义务，使用其给定初态作同一有限检查。此为既有过程的实例推论，重放得到数学合法运行，不认证所报物理事件确曾发生。完整 $b$ 是语义表示参数，不声称一个停止的有限运行取得了它的无穷多个坐标。证毕。

出生场不能恢复独立选择的档案。例如在同一有限来源、同一纪元，允许的读根一次后停止与读根两次后停止保留不同事件词而有相同 $B(u)$。这可以由不同的安装读次数输入或不同已声明过程实现；对一个完全固定的确定过程、输入和初始化，不声称同一起点有两个不同确定运行。其反例结论仅是 $B$ 本身遗漏那些过程／输入／档案字段，故联合表示必须保留它们。

还可把全零出生线程配上一个固定的盲过程：从纪元零根开始，只施加 $N$ 次 $\rho$、记录同一来源承诺及递增纪元，然后写停止标记，不读取树形、叶数或全场。按合同所需的根支持另列为参数。每个有限出生窗口与此有限迹同时由足够深的有限全配对来源实现；盲记录与窗口从同一个来源获得，没有拼接边缘。完整线程却不由任何有限来源实现，因为其零骨架无限。停止标记只结束这条有限迹，既不是初态树的 End，也不表示已经读到全零场。此为出生联合像的非实现例，未建立一般档案完成框架。

### 23.7 条件取得、保留与费用边界

**约定 23.14（实际访问与初始化合同）。** 以下实现前提记为 `ASSUMED-UNVERIFIED`：实际取得当前根、有限查询地址、绝对纪元和对同一纪元零来源的真实纯 $\rho$ 承诺；合法构造读取返回节点标签，并且仅在配对处返回有序孩子句柄；安装的有限守卫控制可以遍历输入 $L/R$ 字、维护所需计数和上限、读取已获控制／纪元数据，并安排已确认的全局替换；完整档案可追加且每条旧事件均保留。查询期间纪元静止，或者另取得并计费一个该纪元快照。跨替换的根重新取得或句柄持续有效、引用绑定、快照／旧单元保存及收据真实性的支持均须另行供应和计费。数学编码不授予访问、执行、免费复制或历史认证权限。

**命题 23.15（固定历史目标的有限取得与条件上界）。** 在约定 23.14 下，可从已获根沿已获查询字遍历，若遇阻挡叶则返回不存在；合法非根查询在父节点沿右脊读到定理 23.5 的上限，计算并记录出生。正确绑定的 $(\text{来源身份},\text{纪元零根},p,b_u(p))$ 连同其支持引用可永久用于该目标的历史准入，而以后新请求的地址仍需取得。

声明单位字操作模型：每次构造检查、孩子移动、守卫转换及事件／缓存写入各计一单位，字宽 $w$ 足够容纳当次地址、纪元、身份及句柄，位宽与序列化另行计费。于是单个合法查询的观察工作及新增事件空间为

$$
O(|p|+\lceil N/2\rceil+1),
\tag{RA.2323}
$$

再加实际初始化、根／引用／收据取得与所有支持费用。它不把整个大小为 $O(2^r)$ 的完整前缀读取计成路径成本。

对固定历史目标纪元 $n_*$，在已确认观察纪元

$$
N_h=\max(n_*,2h)\qquad(h\ge1)
\tag{RA.2324}
$$

可枚举全部 $|p|\le h$ 地址并逐项取得出生，保留全部遍历、读取、输出和替换记录。这个有限阶段的观察工作为 $O((h+n_*+1)2^h)$；$n_*=0$ 时为 $O(h2^h)$。重复较浅阶段的累计观察工作有同阶上界。每个有限来源最终会给出（RA.2316）的正出生整层证书，从而恢复初态；没有统一的未读种子高度界。在无限来源上这个证书搜索不保证停止，完整 $B$ 只是阶段的语义极限。

证明。遍历父路径至多 $|p|$ 次移动／检查；右路径至多 $\lceil N/2\rceil$ 条边和多一个端点检查，每次状态转换、记录和输出在所声明字模型中只增加常数倍费用，证明单项界。根及 $N=0$ 情形只需常数输出；查询不存在时的有限遍历也在路径界内。若必须保存多字数据或多个原始事件，其写入数及序列化增加量另行计入，不隐藏于一个免费写动作。

由 $b_u(p)\le2|p|$，观察纪元 $N_h\ge2h$ 时全部这些地址存在；所需有限枚举及上限控制由合同供应，未使用任意地址句柄或出生 oracle。地址总数为 $2^{h+1}-1$，每次查询费用至多常数倍 $h+\lceil N_h/2\rceil+1\le2h+n_*+2$，给阶段界。按深度 $1..h$ 求和，$\sum_{d\le h}2^d=O(2^h)$、$\sum_{d\le h}d2^d=O(h2^h)$，给累计界；其中所有旧档案占用照常累加，不作删除。有限来源的初始位置深度有上界，逐步增大的 $h$ 必越过它，届时整层出生为正，推论 23.8 给唯一初态及其标签。历史目标 $n_*$ 始终固定，后来的 $N_h$ 只是观察推进；若开始已在更晚纪元，则使用实际当前纪元，路径工作界相应使用该更大 $N$，不回滚取得旧态。证毕。

来源本身的费用是另一项。在显式无共享出现单元模型中，若每次全局替换遍历／更新当时的节点并按单位工作写新单元，令 $L(u)$ 为初始叶数；由母卷定理 3.4 的 Fibonacci 组成动力学和满二叉树节点数 $2L-1$，纪元 $j$ 的节点数为 $O(L(u)\varphi^j)$，$\varphi=(1+\sqrt5)/2$。求几何和得通过纪元 $N$ 的累计来源工作为 $O(L(u)\varphi^N)$；这个计数包括显式树规模，不是常数时间的整体替换。另加来源构造、全部保留版本／快照与句柄支持、初始化、收据／引用验证、完整旧档案、字位宽及序列化资源。编码为程序或值不保证这些费用保持，所给界是条件模型计数，不是设备测量或任意探针的最优性。

完整树码已获时，仍直接复用母卷定义 9.1、定理 9.2–9.3 与 [SourceTreeEncoding](../../../D5/S0/History/Spacetime/SourceTreeEncoding.lean) 的 `sourceCode_injective`、`source_code_equiv`、`decodeSource_encode`（叶嵌入 `FreeMagma Nat` 的零／一，配对保序），以及 §22 的像解析；此充分路线不重新命名为新编码成果。[尺度读出与逆许可几何定义 1.1、1.3、定理 1.2、1.4](https://github.com/the-omega-institute/trureturing/blob/587d5ac330548db24a7df576c758f26523c9a699/docs/develop/theory/FIB_SCALE_READOUT_PERMISSION_GEOMETRY.md) 的末端标量合同只恢复组成或组成祖先许可，其明确给出的同组成异括号三步像边界与本节一致；它不供应有序出现出生恢复。计数、叶序、不透明移动点、实际历史与逆解析仍是不同任务。

本节的钟与局部像是具体来源推导；纤维判据、完整编码、一般完成与部分 writer 语义保留其既有所有者。已获出生缓存只支持它已取得的正确绑定目标，不能据此获得[主卷定理 120.4–120.5](RECURSIVE_RELATIONAL_OBSERVATION.md) 要求的全部未来严格响应和可达初始化更新合同，也不能把[恢复几何定义 8.1–8.2](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md) 的有限共同实现优化套在全部有限树这个无限类上。任意导航、自读、额外操作、独立控制和档案、未确认来源史、物理度量空间与时间的互相恢复仍需各自的访问、共同实现和动态充分性条件。这里没有物理恢复、普遍观察者最小性、世界原创性或完整持续目标完成的结论；初态与纯 $\rho$ 语义链的恢复不能替代实际事件认证。

## 追加锚（本行以下为增补区）

## 24. 固定 \(\rho\) 的绝对纪元重建游标与父导航下界

第23节给出了固定来源的出生场、绝对纪元和有限重放合同。本节只在那个来源合同上增加一个专用的语义游标。它把一个已取得的有限种子与一个绝对纪元组合起来，避免把每次全局替换误写成重新展开整棵树；同时给出一个较弱的父导航任务下界，说明局部更新便宜不等于闭合预测状态有限。

本节的游标是语义表示。它不自动提供根票、父引用、快照、权限、writer 或收据；这些仍由（RA.2322）—（RA.2324）及过程几何卷的实际过程合同决定。

### 24.1 叶扇区的唯一分解与显式公式

固定一个有限有序源树 \(u\in\mathcal T\)、一个绝对纪元 \(N\ge0\)，以及源树中每个叶的**出现位置** \(r\)。相同标签的两个叶仍按出现位置区分。令

$$
\eta(r)=
\begin{cases}
0,&\operatorname{tag}_u(r)=\alpha,\\
1,&\operatorname{tag}_u(r)=\beta,
\end{cases}
\qquad
w(q)=\#_L(q)+2\#_R(q)
$$

其中 \(q\in\{L,R\}^{*}\)。记

$$
T_0=\alpha,
\qquad T_1=\beta,
\qquad
T_{m+2}=\langle T_{m+1},T_m\rangle.
\tag{RA.2401}
$$

这里复用 [FIB 原子关系生成卷定义 3.1 与定理 3.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md#3-fibonacci-替换与组成动力学)；本节只把该轨道放入第23节的固定来源、绝对纪元和访问合同。

对 \(\rho^N(u)\) 中的一个地址，或者它是源树的原有内部出现，或者唯一地写成

$$
 p=rq
$$

其中 \(r\) 是一个源叶出现、\(q\) 是该叶展开出的后缀。叶根本身取 \(q=\varepsilon\)。在叶扇区中，当前子树的语义索引为

$$
\boxed{
 k(N,r,q)=N+\eta(r)-w(q),
}
\tag{RA.2402}
$$

并且当 \(q=\varepsilon\) 时当前子树是 \(T_{N+\eta(r)}\)。对非空后缀 \(q=q'a\)，它在固定纪元 \(N\) 已存在的准确条件是

$$
\boxed{
 N\ge e_u(rq):=2-\eta(r)+w(q').
}
\tag{RA.2403}
$$

这里的出生时间是孩子根的第一次出现时间；源叶自身的出生时间为零。条件（RA.2403）比单独检查 \(k\ge0\) 强：例如从 \(\alpha\) 出发在 \(T_2\) 时，\(LL\) 的形式索引为零，但该地址尚未出现。

**命题 24.1（叶扇区公式）。** 对每个合法的 \(rq\)，\(\rho^N(u)\) 在该地址的子树等于 \(T_{k(N,r,q)}\)，且（RA.2403）给出其存在的充要条件。

**证明。** \(q=\varepsilon\) 时是 \(\alpha\)、\(\beta\) 叶的定义以及 \(\rho\) 的迭代。若当前扇区为 \(T_k\)，其左子树为 \(T_{k-1}\)，右子树为 \(T_{k-2}\)；沿左边把 \(w\) 增加一，沿右边把 \(w\) 增加二，得到（RA.2402）。源 \(\alpha\) 的第一层孩子在纪元二出现，源 \(\beta\) 的第一层孩子在纪元一出现；以后每条左、右边分别再延迟一、二步，故对子路径 \(q'a\) 的出生时间为（RA.2403）。沿 \(q\) 的长度归纳同时证明存在性与子树公式。证毕。

### 24.2 游标载体与语义操作

游标保存以下语义数据：源身份和纪元零根、源叶出现 \(r\) 或源内部出现、后缀栈 \(q\)、权重 \(w(q)\)、已确认绝对纪元 \(N\)，以及必要时用于读取源骨架的有序上下文。对源内部出现，\(\mathsf{DownL}\)、\(\mathsf{DownR}\) 直接沿源骨架移动；对叶扇区，先检查（RA.2403），再按（RA.2402）更新索引。

在叶扇区中，定义

$$
\operatorname{ReadTag}(N,r,q)=
\begin{cases}
\alpha,&k(N,r,q)=0,\\
\beta,&k(N,r,q)=1,\\
\mathsf{pair},&k(N,r,q)\ge2.
\end{cases}
\tag{RA.2404}
$$

仅当 \(k\ge2\) 时，\(\mathsf{DownL}\) 和 \(\mathsf{DownR}\) 合法，并分别把 \(w(q)\) 增加一、二；它们把后缀栈压入 \(L\) 或 \(R\)。\(\mathsf{Up}\) 弹出一个后缀；后缀为空时回到该源叶的源父上下文，源根处的 \(\mathsf{Up}\) 不定义。因而游标不是只保存一个地址整数，而是保存一个能够恢复局部组合上下文的 zipper 数据。

一次已确认的纯 \(\rho\) 接续只做

$$
(N,r,q,w)\longmapsto(N+1,r,q,w).
\tag{RA.2405}
$$

源身份、纪元零根、出现位置和后缀栈均不重置。由（RA.2402）可知，同一地址的子树索引统一增加一；由（RA.2403）可知，历史出生时间不随观察纪元改写。冻结的历史视图可以保留自己的 \(N\)，但读取它不等于获得物理回滚或旧快照访问。

**命题 24.2（有限交错的语义正确性）。** 在固定源骨架和固定绝对纪元初值下，任意有限交错的 \(\mathsf{ReadTag}\)、合法上下移动和（RA.2405）都与直接对 \(\rho^N(u)\) 作同地址求值一致。

**证明。** 叶扇区的读数由命题24.1给出；每次下移只应用 \(T_k\) 的左、右递归，且由 \(k\ge2\) 守卫排除不存在的孩子；上移撤销同一后缀操作或回到保存的源父上下文。纪元增加把每个 \(T_k\) 送到 \(T_{k+1}\)，源内部节点则由 \(\rho\) 的二元同态规则更新。对交错长度作归纳，得到每一步的地址、标签和后继一致。证毕。

### 24.3 语义常数更新与实际执行边界

在一个字宽足以容纳当前计数器、引用和已分配栈单元的抽象模型中，游标核心的读标签、上下移动和纪元增加各使用常数个语义字操作；每次叶扇区下移至多新增一个不可变栈单元。固定种子 \(u\) 后，执行 \(H\) 个游标命令所需的语义存储为

$$
O(|u|+|q_0|+H),
\tag{RA.2406}
$$

其中完整事件档案、控制器状态、引用序列化和任意大整数的位宽费用另计。保留每个显式起始规则的语法族

$$
A_0\to\alpha,
\quad A_1\to\beta,
\quad A_{j+2}\to\langle A_{j+1},A_j\rangle
$$

在推进到 \(N+1\) 时只需追加 \(A_{N+2}\) 和一个新的起始规则；对固定 \(u\)，该语法描述大小为 \(O(|u|+N+1)\)，但保留全部历史起始规则的总存储会累加。这里使用的是一个专用族解释器，不能把静态语法压缩的预处理结构自动宣称为可在线更新。

要把（RA.2406）提升为实际观察者的有界费用结论，至少还需满足：源根与叶出现已经实际取得并有绑定证据；父子引用在当前纪元仍有效，或合同提供有界成本的同地址刷新；\(\mathsf{Up}\) 有授权的父引用或根重取得路径；控制器、writer、收据和权限状态的更新负载有界。若一次全局替换使所有旧句柄失效，而合同只允许逐一刷新，则（RA.2405）的语义常数更新不能隐藏这项实际费用。完整过程仍应按（RA.2322）逐事件重放；语义游标不认证记录所声称的物理事件。

### 24.4 固定树父导航任务的精确最小状态

下面故意研究一个弱于完整过程的任务，以得到可检验的状态下界。固定一棵已知有限有序树 \(t\)，允许的操作只有构造读取、\(\mathsf{DownL}\)、\(\mathsf{DownR}\) 和部分 \(\mathsf{Up}\)，并观察每一步的合法性与当前构造标签；不计来源句柄、writer 输出、历史档案和独立事件身份。定义位置 \(p\) 的父链响应

$$
\Sigma_t(p)=\bigl(t|_p,t|_{\operatorname{parent}(p)},\ldots,t\bigr).
\tag{RA.2407}
$$

**定理 24.3（单源 \(\rho\) 轨道的父导航下界）。** 令 \(F_0=0,F_1=1\)。在上述弱导航任务中，\(t=T_N\) 时每个位置具有不同的 \(\Sigma_t(p)\)，因而最小精确状态数为

$$
\boxed{2F_{N+1}-1}.
\tag{RA.2408}
$$

若 \(t=T_{N+1}=\rho^N(\beta)\)，则最小状态数为

$$
\boxed{2F_{N+2}-1}.
\tag{RA.2409}
$$

因此在该任务中，任何闭合的精确预测器在 \(\alpha\) 种子、纪元 \(N\) 至少需要

$$
\left\lceil\log_2(2F_{N+1}-1)\right\rceil=\Omega(N)
\tag{RA.2410}
$$

个二进制状态位；这不是带外部游标、树存储或档案的总工作空间下界。

**证明。** 记 \(\kappa(T_j)=j\)。在 \(T_N\) 中，沿左边和右边分别把子树指标减一、减二；从根到任一位置的指标序列因此逐步确定整个地址，而每个位置的父链响应记录了这条序列及每一级的有序构造。因此不同位置给出不同 \(\Sigma_t\)。若两条父链在某一级首次不同，先作共同次数的 \(\mathsf{Up}\)，再在该级读取构造标签即可区分；若一方先到根，则下一次 \(\mathsf{Up}\) 的合法性不同，也给出区分。故这些签名确实是不同的残余行为类，而不只是不同的编码。反向地，给定 \(\Sigma_t(p)\)，\(\mathsf{Up}\) 删除首项，\(\mathsf{DownL}\)、\(\mathsf{DownR}\) 把选定的孩子附加为新的首项，所以相同的 \(\Sigma_t\) 对所有有限续接具有相同响应；这正是过程几何卷残余行为商在这个弱任务上的状态。

节点数满足

$$
S_0=S_1=1,
\qquad S_m=1+S_{m-1}+S_{m-2},
$$

故归纳得 \(S_m=2F_{m+1}-1\)。以 \(m=N+1\) 代入得到（RA.2408），以 \(m=N+2\) 代入得到（RA.2409）。精确状态至少要区分这些残余类，故容量下界为（RA.2410）。证毕。

该下界只针对声明的父导航与构造读取。如果禁止父操作、允许额外对称商、把完整树或游标放在外部存储，或改变合法性合同，状态数都可能不同。它不构成一般观察者的统一有限记忆不可能定理；它只说明不能从“每次局部 \(\rho\) 更新为常数语义操作”推出“所有未来父导航都由固定有限状态闭合”。

### 24.5 两个必要反例

第一，若替换后只更新焦点子树而保留旧父上下文，取 \(u=\langle\alpha,\alpha\rangle\)，焦点在左叶。把焦点从 \(\alpha\) 改成 \(\beta\) 而不更新右兄弟，会读出虚假的父 \(\langle\beta,\alpha\rangle\)；真实父是 \(\langle\beta,\beta\rangle\)。历史版本仍可作为历史数据，但不能冒充当前上下文。

第二，语义地址存活不保证句柄存活。取 \(u=\alpha\)，根在一次 \(\rho\) 后成为 \(\beta\)。若根引用只在纪元零有效，纪元一用该引用读取就不合法；同地址出生公式没有替代真实的刷新或重新取得权限。

第三，端点语义状态不恢复 writer 顺序。若两种操作序列都在同一持久根合同下到达纪元一根位置，

$$
\mathsf{ReadTag};\mathsf{ApplyRho}
\qquad\text{与}\qquad
\mathsf{ApplyRho};\mathsf{ReadTag}
$$

可以有相同的来源、纪元和焦点，却分别留下不同的事件词。完整档案必须保留顺序；端点相等不能推出 writer 相等。

### 24.6 结论范围与来源

本节的出生公式和游标运输是 FIB 自由二叶语法在固定纯 \(\rho\) 任务下的 repo-derived 推导；它们不把地址编码变成访问权限，也不把语义常数操作变成物理设备的常数时间。父导航下界只针对（RA.2407）的弱任务，完整观察者仍需第23节的实际共同来源、控制器、档案、权限和收据合同。

二叉焦点/上下文的局部操作可参照 Gérard Huet, *The Zipper*, Journal of Functional Programming 7(5), 549–554 (1997), §3.2；静态 grammar-compressed tree 的预处理与常数延迟导航可参照 Markus Lohrey、Sebastian Maneth、Carl Philipp Reh, *Traversing Grammar-Compressed Trees with Constant Delay*, arXiv:1511.02141v2 (2015), Theorem 1。部分持久数据结构的摊还更新条件可参照 James R. Driscoll、Neil Sarnak、Daniel D. Sleator、Robert E. Tarjan, *Making Data Structures Persistent*, Journal of Computer and System Sciences 38(1), 86–124 (1989)。这些文献只支持其声明模型中的局部工具；没有一个自动供应本节的在线全局替换、句柄权限或完整 writer 合同。

本节没有新增 Lean 声明、消化账目或物理实现结论。尚未解决的接口包括：实际取得的有限种子或正出生整层证书、跨纪元引用有效性、父引用刷新合同、完整过程的 reachable-domain 联合响应、以及把所有实际成本纳入同一度量。任何一个条件缺失时，相应结论只能保留为语义候选或条件命题。

## 25. 固定出生场上的续接核、条件信念与联合边界

第24节给出了固定来源、固定纯 \(\rho\) 轨道上的语义游标，并把父导航下界限制在一个声明的弱任务中。本节增加概率与自适应续接，但不把它们解释成系统外的控制器。目标是刻画一个观察者在已经取得部分记录后，怎样保留仍然会影响未来读数的联合关系。

本节的新增对象有两个层次。第一层是给定有限状态和有限策略族的**未来续接核**；它判断两个当前配置能否对所有允许的有限后续实验保持不可区分。第二层是在固定 FIB 出生场上，把来源、绝对纪元、游标、权限和档案放进同一个实际联合来源，并对该联合状态做条件更新。只保存当前目标的边缘后验，或只保存当前出生场，都不保证这两个层次能够闭合。

### 25.1 有限自适应策略的续接核

先固定有限经典模型。令 \(S\) 为完整配置集合，\(M\) 为观察者的工作记忆，\(A\) 为动作集合。动作 \(a\) 的一步联合核写成

$$
J_a(y,s'\mid s,m),
$$

其中 \(y\) 包含合法、失败、事件和指定读数；若动作在 \((s,m)\) 不合法，则失败标签也必须由同一个核给出。记忆更新是

$$
m'=U(m,a,y),
$$

或把档案写入拆开为 \(c'=W(c,m,a,y)\)，再令 \(m' = U(m,c',a,y)\)。所有会影响下一步选择或读数的参考、权限和控制状态都必须在 \(s\)、\(m\) 或显式记录中出现。

一个有限策略 \(\pi\) 是前缀闭合的策略树：在每个有限转录 \(\tau\) 上，它选择停止，或者选择一个当前声明为合法候选的动作 \(a\)。在得到 \(y\) 后，策略树转到相应的子策略 \(\pi_{a,y}\)。令 \(K^{\pi}_{s,m}\) 为该策略生成有限转录的概率核。递归地，若 \(\pi\) 在根停止，则

$$
K^{\pi}_{s,m}(\mathsf{stop})=1.
$$

若根选择 \(a\)，则对每个首读数 \(y\) 和后续有限转录 \(\tau\)，定义

$$
K^{\pi}_{s,m}\bigl((a,y)\mathbin{\Vert}\tau\bigr)
=
\sum_{s'}J_a(y,s'\mid s,m)
K^{\pi_{a,y}}_{s',U(m,a,y)}(\tau).
\tag{RA.2501}
$$

如果记录单列，则右侧的记忆参数还包括 \(W(c,m,a,y)\)。不合法动作的失败输出留在转录中；它不能被递归定义静默删除。确定性过程只需把 \(K\) 换成有限迹集合或单值转录。

给定允许的前缀闭合策略族 \(\Pi\)，定义未来续接等价

$$
(s,m)\mathrel{\approx_\Pi}(t,n)
\iff
\forall\pi\in\Pi,\ \forall\tau,
\quad
K^{\pi}_{s,m}(\tau)=K^{\pi}_{t,n}(\tau).
\tag{RA.2502}
$$

这里的比较同时包含停止、合法性、失败标签、读数、记录和后继分布。它比“一次读数相同”强，也比“当前目标后验相同”强；它只比较已声明的有限策略与有限转录，不预设所有无限分支已经实际发生。

**命题 25.1（续接迹等价与可执行商的区别）。** 若 \(\Pi\) 对有限前缀封闭，则（RA.2502）定义一个等价关系，记为 \(\approx^{\mathrm{tr}}_\Pi\)。它给出声明策略族下所有有限转录的最大观察商：同一类的状态对每个已声明策略产生相同的有限迹分布。

迹等价本身不自动保证可以定义一个逐步运行的 Markov 商。要得到这样的可执行边界，还需加强为一步闭合关系 \(\approx^{\mathrm{bis}}_\Pi\)：同类代表对每个声明动作有相同的合法／失败标签与读数质量，并且每个正概率读数的后继，在对应的下一步等价类上的总质量相同。于是

$$
\approx^{\mathrm{bis}}_\Pi
\ \subseteq\
\approx^{\mathrm{tr}}_\Pi,
\tag{RA.2503a}
$$

在确定性过程，两者在该任务上相合；在概率过程中，即使 \(\Pi\) 包含全部已声明的一步探针，
也还需要另加“这些探针完备刻画后继类质量”的条件，不能由策略族的名称自动推出相合。满足
该额外条件时，商集

$$
Q^{\mathrm{bis}}_\Pi=(S\times M)/{\approx^{\mathrm{bis}}_\Pi}
$$

上才可以定义商核和商记忆更新。

**证明。** 迹等价的反身性、对称性和传递性直接来自（RA.2502）。一步闭合要求的合法性、读数和后继类质量正是概率核可下降的代表无关条件；按策略树深度归纳，得到商上的所有有限转录律。反向包含表示任何一步闭合的商都不能区分其代表能够生成的有限策略迹。概率过程中，单凭所有已经声明的迹相等，可能仍不足以选出逐步的后继类核，因此必须把一步条件单列为执行合同。证毕。

令 \(\eta:S\times M\to B\) 是任一摘要。如果同一 \(\eta\)-纤维上的状态对所有 \(\Pi\) 策略具有相同续接迹，则

$$
\ker\eta\subseteq\mathrel{\approx^{\mathrm{tr}}_\Pi}.
\tag{RA.2503}
$$

若它还满足下节的一步因子化条件，则 \(\eta\) 诱导一个可执行商，并有
\(\ker\eta\subseteq\approx^{\mathrm{bis}}_\Pi\)。若每个行为等价类也不被摘要拆开，才能把摘要称为相应商的精确编码。因而“最小”总是相对于策略族、转录和一步执行合同，而不是一个脱离任务的绝对状态数。

### 25.2 动态充分边界的逐步因子化条件

对确定性或概率性模型，摘要 \(\eta\) 真正能够继续运行，必须满足以下条件。若

$$
\eta(s,m)=\eta(t,n)=b,
$$

则对每个声明动作 \(a\)：

1. \(a\) 在两边同时合法或同时失败，且失败类型相同；
2. 对每个读数 \(y\) 和每个新边界 \(b'\)，后继纤维上的联合质量相同：

$$
\sum_{s':\eta(s',U(m,a,y))=b'}
J_a(y,s'\mid s,m)
=
\sum_{t':\eta(t',U(n,a,y))=b'}
J_a(y,t'\mid t,n);
\tag{RA.2504}
$$

3. 记录、停止标签与权限结果能由 \((b,a,y)\) 决定；
4. 选择器在任务中若可用，则对实际可访问的摘要和记录因子化，不能访问摘要合同没有提供的隐藏代表。

条件（RA.2504）在实际共同来源像上求和。不能把边缘上分别可达的状态拼成一个并不存在的联合状态，也不能向边界像外补入“幽灵”概率。若档案 \(c\) 单列，则把 \((s,c,m)\) 视为完整状态，并把 \(c'\) 纳入后继摘要；否则应先把档案并入 \(m\)。

在这些条件下定义

$$
\bar J_a(y,b'\mid b)
=
\sum_{s':\eta(s',U(m,a,y))=b'}J_a(y,s'\mid s,m)
$$

并以任意代表 \((s,m)\) 计算；（RA.2504）保证定义与代表无关。
在确定性特例中，若 \(J_a\) 由单值后继 \(T_a\) 给出，则有交换式

$$
\eta(T_a(s,m))
=\bar T_a(\eta(s,m)).
\tag{RA.2505}
$$

在概率情形，式（RA.2505）由 \(\bar J_a\) 的后继纤维推前替代；也就是先用
完整核更新再投影，与先用 \(\bar J_a\) 在边界上更新相同。对策略树深度归纳，得到

$$
K^{\pi}_{s,m}
=\bar K^{\pi}_{\eta(s,m)}
\qquad(\pi\in\Pi).
\tag{RA.2506}
$$

反向地，如果某一步的合法性、读数或后继纤维质量依赖于同一 \(\eta\)-纤维中的代表，那么一棵一步策略，或在该读数后接上区分代表的子策略，就会违反（RA.2506）。因此（RA.2504）是声明任务下的逐步充分性判据；它不是任意投影自动拥有的性质。

这一判据与第12节的动态商和第15节的 FIB 组合上下文商相容，但关注点不同：第12节先给四份表示的联合下降条件，第15节研究 FIB 项在上下文闭合时的部分同余；本节把**自适应策略树的整套续接核**作为比较对象，并允许其后继是概率条件核。

### 25.3 固定出生场上的联合信念边界

现在回到第23—24节的固定来源合同。取一个有限来源族 \(\mathcal U\)，每个来源是带叶出现位置的有限有序 FIB 树。固定纯替换 \(\rho\)，并令可观察绝对纪元取有限集合 \(\mathcal N\)。把一个仍会影响未来行为的隐状态写成

$$
\theta=(u,N,\chi,\varpi),
$$

其中 \(u\in\mathcal U\) 是源及其纪元零根，\(N\in\mathcal N\) 是绝对纪元，\(\chi\) 是第24节的语义游标（源内部上下文、叶扇区、后缀栈和权重），\(\varpi\) 表示当前引用、权限和句柄合同。若某些字段已被观察者明确取得，它们可以从隐状态移入显式工作记忆；关键是不能同时在两边重复计数。

给定档案与控制状态 \(c,m\)，实际共同来源提供一个联合像

$$
E\subseteq \mathcal U\times\mathcal N\times\mathsf X\times\mathsf P\times\mathsf C\times\mathsf M,
$$

其中 \(\mathsf X\) 是合法游标集合，\(\mathsf P\) 是权限／句柄状态。条件信念必须是同一实际来源上的联合分布

$$
\nu_{c,m}(u,N,\chi,\varpi)
=\Pr(u,N,\chi,\varpi\mid C=c,M=m),
\tag{RA.2507}
$$

而不能把“源后验”“纪元后验”和“游标后验”分别求出后任意相乘。若来源是确定的，\(\nu_{c,m}\) 可以退化为一个点质量；若只是部分取得，它才保留多个联合可能。

例如实际像只有两个联合状态
\(\{(u_0,\chi_0),(u_1,\chi_1)\}\) 时，两个边缘都可以是均匀的，
但边缘乘积还会加入不存在的 \((u_0,\chi_1)\) 与 \((u_1,\chi_0)\)。
若下一步合法性要求 \(u=\chi\)，真实联合分布给出概率一，而错误的独立重组只给出
二分之一。因而“分别知道两个边缘”不能替代同一来源上的联合条件。

对动作 \(a\)，第23节的实际访问、出生、句柄刷新、writer 和事件合同合成一个条件核

$$
K_a(y,\theta',c'\mid\theta,c,m),
\tag{RA.2508}
$$

其中非法调用的失败记录也属于 \(y\) 或 \(c'\)。在取得结果 \(y\) 后，先做未归一化更新

$$
\widetilde\nu_{c,m,a,y}(\theta',c')
=
\sum_\theta
\nu_{c,m}(\theta)
K_a(y,\theta',c'\mid\theta,c,m).
\tag{RA.2509}
$$

令

$$
Z_{c,m,a,y}
=\sum_{\theta',c'}
\widetilde\nu_{c,m,a,y}(\theta',c').
$$

当 \(Z_{c,m,a,y}>0\) 时，条件边界为

$$
\nu_{c,m,a,y}(\theta',c')
=
\frac{\widetilde\nu_{c,m,a,y}(\theta',c')}
{Z_{c,m,a,y}}.
\tag{RA.2510}
$$

零概率分支必须显式 totalize，或者标记为不可达；不能用除零的形式式假装观察者取得了该结果。若档案写入只是观察者已知的确定函数，可把 \(c'\) 从随机核中投影出来，但不能把它从实际共同来源和权限条件中删除。

### 25.4 联合后验的有限重放闭合

令联合边界为

$$
\Gamma=(\nu_{c,m},c,m),
\tag{RA.2511}
$$

并要求动作选择、合法性、记录写入和游标更新都只依赖 \(\Gamma\)：

$$
 a=\pi(\Gamma),
\qquad
\Gamma'=\overline T_{a,y}(\Gamma).
\tag{RA.2512}
$$

定义从条件联合信念出发的混合迹核

$$
K^{\pi}_{\nu_{c,m},c,m}(\tau)
:=
\sum_{\theta}\nu_{c,m}(\theta)\,
K^{\pi}_{\theta,c,m}(\tau).
\tag{RA.2513a}
$$

如果（RA.2508）由同一来源合同生成、（RA.2509）—（RA.2510）保留全部实际联合质量、档案 writer 不重置来源身份与绝对纪元，而且第24节的游标操作在每个正概率分支合法，则对每个有限策略 \(\pi\) 和有限转录，按（RA.2501）的策略树深度归纳有

$$
K^{\pi}_{\nu_{c,m},c,m}(\tau)
=
\overline K^{\pi}_{\Gamma}(\tau).
\tag{RA.2513}
$$

这给出一个条件性的有限重放定理：联合信念、档案和控制状态构成指定有限任务的动态充分边界。它不说观察者能免费取得 \(\nu_{c,m}\)，也不说无限来源可由某个有限数据结构完整表示；它只说一旦合同实际提供并维护这份边界，边界更新与完整配置的有限续接相同。

证明是对转录长度归纳。零长度只读取停止标签。首动作由（RA.2512）选择，未归一化质量由（RA.2509）与实际核相同；正概率结果归一化得到（RA.2510），档案与控制更新由（RA.2512）确定。对子策略使用归纳假设，再对首结果求和得到（RA.2513）。来源身份、纪元和 writer 若被重置，两个不同的历史可能被错误合并，归纳的共同来源前提即失效。

**推论 25.2（联合边界的最小化方向）。** 在动作族能够区分所有声明字段的任务中，任何精确摘要至少要保留 \(\nu_{c,m}\) 与游标／权限的联合行为类；只保留源边缘、当前出生场、目标后验或一个互信息数值，都只有在它们满足（RA.2504）的因子化时才可作为动态边界。

这是一条条件性方向结论，不是说每个字段都必须按本文的字面编码保存。若两个字段在声明策略族下行为等价，可以按（RA.2502）继续商掉；若某个字段影响未来合法性、读数、writer 或权限，就不能因当前读数相同而删除。

### 25.5 最小有限反例：零即时目标信息仍保留未来关联

取四个等概率世界 \((X,K)\in\{0,1\}^2\)，其中 \(X\) 是目标 bit，\(K\) 是稍后可读取的参考 bit。第一步动作读出

$$
Y=X\oplus K.
$$

在先验 \(\Pr(X=x,K=k)=1/4\) 下，\(\nu_y\) 表示取得 \(Y=y\) 后的条件信念，
两种历史信念为

$$
\begin{aligned}
\nu_0&=\tfrac12\delta_{(0,0)}+\tfrac12\delta_{(1,1)},\\
\nu_1&=\tfrac12\delta_{(0,1)}+\tfrac12\delta_{(1,0)}.
\end{aligned}
\tag{RA.2514}
$$

两者在目标坐标上的边缘都为均匀分布；以下互信息均取该四世界先验：

$$
\Pr_{\nu_0}(X=0)=\Pr_{\nu_1}(X=0)=\tfrac12,
\qquad
I(X;Y)=0.
\tag{RA.2515}
$$

令 \(\eta_X(\nu)(x)=\sum_k\nu(x,k)\) 为只保留目标边缘的摘要；
令 \(R_k\) 表示第二步读到 \(K=k\) 后用已保留的 \(Y\) 解码，
\(\eta_{\mathrm{out}}\) 投影到解码输出 \(X\)。所以只保存当前目标后验的摘要会把 \(\nu_0\) 与 \(\nu_1\) 合并。但是允许的后续动作读取 \(K\)，再用已经保存的 \(Y\) 输出 \(X=Y\oplus K\)。特别地在 \(K=0\) 时，\(\nu_0\) 必然输出 \(X=0\)，而 \(\nu_1\) 必然输出 \(X=1\)。因此不存在一个只依赖当前目标后验的边界更新 \(\bar R_0\) 使

$$
\eta_{\mathrm{out}}R_0(\nu_0)=\delta_0
=\bar R_0\eta_X(\nu_0),
\qquad
\eta_{\mathrm{out}}R_0(\nu_1)=\delta_1
=\bar R_0\eta_X(\nu_1).
\tag{RA.2516}
$$

动态行为商至少区分两个阶段一残余类；保存 \(Y\) 或等价的 parity 类已经足够完成这个二步任务。若把初态、两种中间类和终止态都计入完整协议自动机，则状态数为四；这里的关键边界是中间的两类，而不是把自动机阶段计数误作记忆容量。

这个四世界模型是二元目标、二元参考、两种非退化目标后验和确定性二步解码的显式最小规模例子；这里的结论只需要该有限反例，不依赖一般最小性主张。它说明

$$
\boxed{
\text{零即时互信息}\ne\text{零未来作用};
\qquad
\text{当前目标后验}\ne\text{动态充分边界}.
}
$$

它也说明“思考”或“解码”可以改变关系的可用位置而不增加整体联合熵：取得 \(Y\) 和 \(K\) 已经建立联合关联，最后的 XOR 只是把该关联转成直接可读的记录。

### 25.6 FIB 出生场中的两个边界失效对

第24节的游标公式允许把同一源叶出现和后缀放在不同绝对纪元读取。取固定源 \(u=\alpha\) 的两个历史：

$$
\theta_1=(u,N=1,\chi=\text{根},\pi=\text{当前根句柄}),
\qquad
\theta_2=(u,N=2,\chi=\text{根},\pi=\text{当前根句柄}).
$$

两者的源后验都是 \(\delta_u\)，但出生场不同。由（RA.2402）—（RA.2404），纪元一的根为 \(T_1=\beta\)，\(\mathsf{DownL}\) 不合法；纪元二的根为 \(T_2=\langle\beta,\alpha\rangle\)，\(\mathsf{DownL}\) 合法且读出 \(\beta\)。因此 source-only posterior 不能决定下一操作的合法性；绝对纪元或等价的游标行为类必须进入边界。

即使两个历史被安排在相同的当前出生场标签上，权限／句柄也不能自动省略。一个句柄可能只在纪元零有效，而另一个带有已认证的跨纪元刷新合同。对同一个 \(\mathsf{ReadTag}\) 或 \(\mathsf{DownL}\)，一个历史可以合法返回，另一个只能返回失败。故当前树标签和源后验相同，仍不推出（RA.2504）。

档案也有同样的独立作用。令纪元二根为
\(T_2=\langle\beta,\alpha\rangle\)。路径
\(\mathsf{DownL};\mathsf{Up}\) 与
\(\mathsf{DownR};\mathsf{Up}\) 都回到同一个语义根游标和同一个来源、纪元，
但若 writer 记录子方向，两个历史的事件词分别含有 \(L\) 与 \(R\)。只保存当前
游标不能支持之后的审计或日志读取；这时必须保留档案本身，或保留一个满足下式的
档案摘要：

$$
\Gamma(C\mathbin{\Vert}e)=\overline\Gamma(\Gamma(C),e).
$$

这两个失效对和（RA.2514）的相关性反例有不同来源：前者是绝对纪元与出生权限没有进入源边界，后者是目标与参考之间的联合关系被边缘化。共同修复方式是把所有会影响声明未来续接的字段放入同一实际联合来源，再按（RA.2509）运输；不是把更多独立边缘表拼在一起。

### 25.7 与父导航下界及信息增量的关系

令 \(\Pi_{\mathrm{parent}}\) 只含第24节的 \(\mathsf{ReadTag},\mathsf{DownL},\mathsf{DownR},\mathsf{Up},\mathsf{Stop}\)。则定理24.3的

$$
2F_{N+1}-1
$$

（以及 \(\beta\) 种子的 \(2F_{N+2}-1\)）可理解为该弱策略族续接商的一个精确状态数。加入 \(\mathsf{ApplyRho}\)、任意单孔上下文、writer 事件、档案读取或权限刷新，只会扩大策略族；新商可以细化，原下界不能自动升级为完整观察者的容量下界。

另一方面，若固定目标 \(X\)，动作 \(A=\pi(C,M)\) 由当前记录和控制状态确定，
并且新档案完整保留 \(A\) 与旧记录，即 \(C'=(C,A,Y)\)，一次动作的互信息增量满足

$$
I(X;C')-I(X;C)=I(X;Y\mid C,A)\ge0,
\tag{RA.2517}
$$

这里用到了 \(I(X;A\mid C)=0\)。若动作没有由 \(C\) 确定，或新记忆覆盖了
\(A\)、旧记录或其它目标相关关联，则应改用取得项减去未保留项的净增益式；
（RA.2517）不能在缺少这些条件时直接使用。

但（RA.2514）说明第一步可以为零而第二步为正。若新档案覆盖旧证据，则还需扣除未保留的目标相关量；对联合边界来说，关键仍是（RA.2504）的全部续接质量，而非单步信息分数。因而“信息自增”应理解为在合法路径上逐步扩大可使用的行为区别，不能要求每一步即时互信息严格为正。

### 25.8 条件范围与未决接口

本节只在有限经典来源、有限策略和明确的概率核中给出联合边界与续接判据。无限策略只被逐个有限前缀比较；把这些有限核再取极限，需要额外的一致性、紧性或共同来源实现条件。量子过程、近似后验、未知模型和物理设备的时间／空间成本都不由（RA.2501）—（RA.2517）自动供应。

第23—24节的根票、来源身份、句柄刷新、writer 收据、实际档案和访问权限仍是独立合同；本节的 \(\nu_{c,m}\) 是在这些合同已经给定时的数学条件边界，不是观察者免费得到的完整分布。若实际来源只给出边缘像而没有联合像，或零概率分支没有 totalize，有限重放闭合只能标为未完成。

本节没有新增 Lean 声明、消化账目或物理时空结论。它把第24节的确定性游标、第12/15节的动态商与 FIB 生成层，以及观察者的信息取得问题接成一个新的条件模型：最小对象是指定策略族下的续接行为商；在概率版本中，其可计算表示是来源、纪元、游标、权限、档案和控制状态的实际联合边界。

## 追加锚（本行以下为增补区）

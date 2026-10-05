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

这里的 \(\overline T_{a,y}\) 包含显式控制更新
\(m'=U(m,c',a,y)\)；若控制更新含随机性，则把 \(m'\) 一并纳入条件核的后继，
并把联合边界扩展为 \((\nu_{c,m},c,m)\) 的后继分布。否则，来源后验虽已更新，
控制器却没有定义下一步可访问的状态，策略树归纳不能闭合。

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

## 26. 跨分辨率实际来源上的四视图动态充分性

第12节已经在同一分辨率上给出空间、时间、边界和记忆四种表示的动态图册。
第25节则把来源、纪元、游标、权限、档案和控制状态放进一个有限策略的联合边界。
本节补上二者之间的纵向接口：不同分辨率必须来自同一个实际来源，粗化必须与合法
更新及四种表示的运输交换；只有这样，单层的互相恢复才可沿分辨率塔继续使用。

本节把三个经常混淆的结论分开：行为恢复只要求保留声明任务下的未来转录，来源恢复
还要求保留指定的来源目标，实际取得则还要有观察者能够执行的读写合同。所有求和和
恢复器都限制在实际来源像上。Claim status: open；本节是普通数学综合，没有新增 Lean
声明，也不推出物理时空结论。

### 26.1 分辨率塔与共同实际来源

令 \(\Lambda\) 是有限的有向分辨率偏序，\(\lambda\succeq\mu\) 表示 \(\lambda\)
比 \(\mu\) 精细。固定非空实际来源 \(\Omega\)，允许 \(\Omega\) 无限。每层有配置集合
\(S_\lambda\)、实际实现映射

$$
\sigma_\lambda:\Omega\longrightarrow S_\lambda,
\qquad
S_\lambda^0=\sigma_\lambda[\Omega].
$$

只在实际像 \(S_\lambda^0\) 上定义后续操作。对 \(\lambda\succeq\mu\)，给出层间
投影

$$
p_{\lambda\mu}:S_\lambda^0\longrightarrow S_\mu^0,
$$

并要求

$$
\boxed{
p_{\lambda\lambda}=\operatorname{id},\qquad
p_{\mu\nu}\,p_{\lambda\mu}=p_{\lambda\nu},\qquad
p_{\lambda\mu}\,\sigma_\lambda=\sigma_\mu.
}
\tag{RA.2601}
$$

最后一个等式是共同来源条件。它排除了一种不合法的拼接：先在细层选择一个实际
来源，再在粗层任意换成另一个具有相同边缘读数的来源。

每层使用同一个声明动作族 \(A\)。把事件、读数、失败原因、时钟增量和 writer
记录打包为有限输出字母表 \(O_\lambda\)。动作 \(a\) 的总核记为

$$
J^a_\lambda(o,s'\mid s),
\qquad s,s'\in S_\lambda^0, o\in O_\lambda.
$$

不合法调用也使用显式失败输出和固定的失败后继；不把未定义的非法核行当作零概率
合法事件。若 \(\lambda\succeq\mu\)，输出的粗化写成
\(\varepsilon_{\lambda\mu}:O_\lambda\to O_\mu\)，则共同来源上的核自然性为

$$
\boxed{
J^a_\mu(o_\mu,t\mid p_{\lambda\mu}s)
=
\sum_{\substack{\varepsilon_{\lambda\mu}(o)=o_\mu\\
                   p_{\lambda\mu}s'=t}}
J^a_\lambda(o,s'\mid s).
}
\tag{RA.2602}
$$

它同时要求合法性、失败、记录和读数按同一输出映射下降。确定性特例是
\(p_{\lambda\mu}T_{\lambda,a}=T_{\mu,a}p_{\lambda\mu}\)，并且输出标签也按
\(\varepsilon_{\lambda\mu}\) 下降。若策略根据输出前缀选择动作，声明的策略族须在
这些输出投影下闭合。

若动作在分辨率 \(\lambda\) 上需要更细的输入，不能把这个前视依赖省略。给出
\(j_a(\lambda)\succeq\lambda\)，并要求
\(\lambda\succeq\mu\Rightarrow j_a(\lambda)\succeq j_a(\mu)\)。把该动作的前视核明确写成
\[
J^a_\lambda:S^0_{j_a(\lambda)}\longrightarrow O_\lambda\times S^0_\lambda,
\]
或在随机情形写成同一类型上的联合质量核。它从
\(S_{j_a(\lambda)}^0\) 取输入、把后继放回 \(S_\lambda^0\)；对
\(s\in S_{j_a(\lambda)}^0\)，粗输入由
\(p_{j_a(\lambda),j_a(\mu)}s\) 给出，层间相容应写成

$$
J^a_\mu(o_\mu,t\mid p_{j_a(\lambda),j_a(\mu)}s)
=
\sum_{\substack{\varepsilon_{\lambda\mu}(o)=o_\mu\\
                   p_{\lambda\mu}s'=t}}
J^a_\lambda(o,s'\mid s).
\tag{RA.2602a}
$$

单调性保证输入限制的类型成立；否则右侧的粗输入并不是该动作在 \(\mu\) 层的
合法前视输入。下文为简洁起见写成同层形式 (RA.2602)，但结论同样适用于
(RA.2602a)。

### 26.2 四视图的动态充分性

令 \(\Pi_\lambda\) 是层 \(\lambda\) 的有限前缀闭合测试族，\(K^{\pi}_{\lambda,s}\)
是从 \(s\) 执行测试 \(\pi\) 所得的有限转录核。定义层行为关系

$$
s\sim_\lambda t
\iff
\forall\pi\in\Pi_\lambda,\ \forall\tau,
\quad
K^{\pi}_{\lambda,s}(\tau)=K^{\pi}_{\lambda,t}(\tau).
$$

四个表示的索引集为

$$
I=\{\mathrm{space},\mathrm{time},\mathrm{boundary},\mathrm{memory}\}.
$$

各表示是实际像上的读出

$$
r_{i,\lambda}:S_\lambda^0\longrightarrow Y_{i,\lambda}^0,
\qquad
Y_{i,\lambda}^0=r_{i,\lambda}[S_\lambda^0].
$$

称 \(r_{i,\lambda}\) 动态充分，如果同一读出纤维中的状态具有相同的合法性、失败
类型和输出，并且对每个新表示纤维的后继质量相同：若
\(r_{i,\lambda}(s)=r_{i,\lambda}(t)=y\)，则对每个 \(a,o,y'\)，有

$$
\sum_{r_{i,\lambda}(s')=y'}J_{\lambda,a}(o,s'\mid s)
=
\sum_{r_{i,\lambda}(t')=y'}J_{\lambda,a}(o,t'\mid t).
$$

selector、停止、记录和权限更新还必须只使用该表示及明示的档案。于是可以定义表示
上的核 \(K^i_{\lambda,a}\)，并得到
\(\ker r_{i,\lambda}\subseteq\sim_\lambda\)。称其为精确行为表示，当且仅当还满足

$$
\boxed{
\ker r_{i,\lambda}=\sim_\lambda.
}
\tag{RA.2603}
$$

右向包含是最小性：表示不把同一行为商中的两个状态永久拆成两个状态。动态充分
本身只需要左向包含；若只要求一个目标而非全部行为，则应把右侧的行为商换成该目标
的纤维关系。

### 26.3 跨层表示运输与四视图自然图册

对 \(\lambda\succeq\mu\)，希望每个视图有一个实际像上的粗化
\(\delta_{i,\lambda\mu}:Y_{i,\lambda}^0\to Y_{i,\mu}^0\)。它必须满足

$$
\boxed{
\delta_{i,\lambda\mu}\,r_{i,\lambda}
=
r_{i,\mu}\,p_{\lambda\mu}.
}
\tag{RA.2604}
$$

在实际像上，满足 (RA.2604) 的映射存在且唯一，当且仅当

$$
\ker r_{i,\lambda}
\subseteq
\ker(r_{i,\mu}\,p_{\lambda\mu}).
$$

因此，细层合并的状态不能让粗层重新区分；这是跨层表示可下降的精确条件。层间恒等
和复合由 (RA.2601) 继承。这个实际像上的唯一因子判据与
`realized_image_unique_factorization_iff_reverse_kernel` 的形式接口相同。

**定理 26.1（跨分辨率四视图自然图册）。** 假设 (RA.2601)–(RA.2604) 成立，
四个视图在每层都是精确行为表示，且各视图核由同一个实际核 \(J\) 对后继纤维求和
得到。则对任意 \(i,j\in I\) 和 \(\lambda\in\Lambda\)，存在唯一双射

$$
\chi_{ji,\lambda}:Y_{i,\lambda}^0\longrightarrow Y_{j,\lambda}^0,
\qquad
\chi_{ji,\lambda}(r_{i,\lambda}s)=r_{j,\lambda}s.
$$

这些双射满足

$$
\boxed{
\chi_{ki,\lambda}=\chi_{kj,\lambda}\chi_{ji,\lambda},
\quad
\chi_{ii,\lambda}=\operatorname{id},
\quad
\chi_{ij,\lambda}=\chi_{ji,\lambda}^{-1},
}
$$

并且与分辨率运输交换：

$$
\boxed{
\delta_{j,\lambda\mu}\,\chi_{ji,\lambda}
=
\chi_{ji,\mu}\,\delta_{i,\lambda\mu}.
}
\tag{RA.2605}
$$

若 \(K^i_{\lambda,a}(o,y'\mid y)\) 是表示核，则同层换视图保持核：

$$
\boxed{
K^j_{\lambda,a}(o,\chi_{ji,\lambda}y'\mid\chi_{ji,\lambda}y)
=
K^i_{\lambda,a}(o,y'\mid y).
}
\tag{RA.2606}
$$

跨层核是细层核按输出和后继表示的推前：

$$
\boxed{
K^i_{\mu,a}(\varepsilon_{\lambda\mu}o_\lambda,y'_\mu\mid
              \delta_{i,\lambda\mu}y)
=
\sum_{\substack{\varepsilon_{\lambda\mu}(o')=\varepsilon_{\lambda\mu}(o_\lambda)\\
                  \delta_{i,\lambda\mu}y'=y'_\mu}}
K^i_{\lambda,a}(o',y'\mid y).
}
\tag{RA.2607}
$$

式 (RA.2607) 中的 \(o_\lambda\) 只是表示所考察的粗输出纤维；若输出已经打包成
一个标签，求和中的第一条件可省略。因而先换视图再粗化、先粗化再换视图，以及先在
细层重放再把结果推到粗层，给出同一个有限转录分布。

**证明。** 令 \(q_\lambda:S_\lambda^0\to Q_\lambda=S_\lambda^0/\sim_\lambda\)
是行为商。由 (RA.2603)，每个 \(r_{i,\lambda}\) 在 \(q_\lambda\) 上诱导唯一双射
\(\widehat r_{i,\lambda}:Q_\lambda\to Y_{i,\lambda}^0\)。置

$$
\chi_{ji,\lambda}
=
\widehat r_{j,\lambda}\,\widehat r_{i,\lambda}^{-1}.
$$

双射的复合律和唯一性随即成立。对任意 \(s\in S_\lambda^0\)，(RA.2604) 的左右
两边在 \(r_{i,\lambda}s\) 上都等于 \(r_{j,\mu}(p_{\lambda\mu}s)\)，得到
(RA.2605)。

将同一个 \(J_{\lambda,a}\) 在两个表示的后继纤维上有限求和，使用
\(r_{j,\lambda}=\chi_{ji,\lambda}r_{i,\lambda}\)，得到 (RA.2606)。对输出纤维和
层间纤维再求和，(RA.2602) 给出 (RA.2607)。最后对策略树深度归纳：根的停止、合法性
和失败标签由这些核保持；给定相同的已见前缀，selector 因子化而选择同一个动作，
下一输出及后继边界质量由 (RA.2606) 或 (RA.2607) 相同，再对子策略使用归纳假设。
证毕。

### 26.4 行为恢复、来源恢复与实际取得

三种“恢复”使用不同的量词。令 \(q_\lambda:S_\lambda^0\to Q_\lambda\) 为指定
行为商，令 \(\theta:\Omega\to\Theta\) 是真正要恢复的来源目标；\(\theta=\operatorname{id}\)
时表示完整来源身份。对视图定义来源层读出

$$
\widehat r_{i,\lambda}=r_{i,\lambda}\,\sigma_\lambda:
\Omega\to Y_{i,\lambda}^0.
$$

**行为恢复**是存在 \(B_{i,\lambda}:Y_{i,\lambda}^0\to Q_\lambda\) 使

$$
q_\lambda\sigma_\lambda=B_{i,\lambda}\widehat r_{i,\lambda};
$$

等价地，\(\ker\widehat r_{i,\lambda}\subseteq
\ker(q_\lambda\sigma_\lambda)\)。它只保证指定未来实验的转录可以重放。精确行为表示
还要求反向包含，即 (RA.2603) 在实际状态层成立。

**来源恢复**是存在 \(R_{i,\lambda}:Y_{i,\lambda}^0\to\Theta\) 使

$$
\theta=R_{i,\lambda}\widehat r_{i,\lambda};
$$

等价地，\(\ker\widehat r_{i,\lambda}\subseteq\ker\theta\)。完整来源的无损恢复
取 \(\theta=\operatorname{id}\)，此时要求 \(\widehat r_{i,\lambda}\) 单射；若只关心
来源的某个商，则只要求它在该商的纤维上恒定。即使四个视图都精确行为，行为等价
仍可能合并来源目标不同的状态，因此不自动给出来源恢复。

**实际取得**还需要一个观察合同。设 \(c\) 是当前记录、权限和参考，写
\(\mathsf{Acq}_{i,\lambda}(c;\omega\Downarrow y)\) 表示存在一条合法有限协议，
在同一个实际来源 \(\omega\) 上取得输出 \(y\)。视图可实际取得，要求对声明域中的每个
\((\omega,c)\)，协议输出唯一且

$$
y=\widehat r_{i,\lambda}(\omega),
$$

并把协议的计算、校准、权限、参考、时钟和费用写入同一记录与控制状态。数学双射
\(\chi\)、行为解码器 \(B\) 或来源解码器 \(R\) 只作用于已经取得的表示值；它们本身
不证明观察者已经取得该值。

若存在各层来源目标 \(\theta_\lambda:S_\lambda^0\to\Theta\)，满足
\(\theta_\lambda\sigma_\lambda=\theta\) 且 \(\theta_\mu p_{\lambda\mu}=\theta_\lambda\)，并且
两层解码器都存在，则在实际像上自动满足

$$
R_{i,\mu}\delta_{i,\lambda\mu}=R_{i,\lambda}.
$$

这只是来源目标的运输方程；它没有把来源恢复升级成实际读取权限。

### 26.5 无限分辨率与线程恢复

若分辨率为 \(\mathbb N\)，先区分环境层
\(Y_{i,n}\) 与实际像 \(Y_{i,n}^0\subseteq Y_{i,n}\)。环境限制为
\(\delta_{i,n}:Y_{i,n+1}\to Y_{i,n}\)，并满足
\(\delta_{i,n}(Y_{i,n+1}^0)\subseteq Y_{i,n}^0\)；其在实际像上的限制才是实际来源所运输的
映射。令
\[
L_i=\varprojlim(Y_{i,n},\delta_{i,n}),
\]
则实际来源给出落在 \(L_i\) 中的线程

$$
\operatorname{Thread}_i(\omega)
=
\bigl(\widehat r_{i,0}(\omega),
       \widehat r_{i,1}(\omega),\ldots\bigr),
$$

并由 (RA.2604) 满足全部相容方程。由于 (RA.2605) 的每个分量都是双射，四种实际线程
有相同的核：

$$
\operatorname{Thread}_i(\omega)=\operatorname{Thread}_i(\omega')
\iff
\operatorname{Thread}_j(\omega)=\operatorname{Thread}_j(\omega').
$$

这只说明四种表示在全部分辨率上保留同一线程区别。要把线程称作来源，仍需两项
独立条件：

1. **分离**：所有层读数相同的两个实际来源相等（或具有同一指定来源目标）；
2. **完备**：每个环境逆极限中的相容线程都来自某个实际来源，即
   \(\operatorname{Thread}_i(\Omega)=L_i\)（或在指定来源目标的商上满足相应满射）。

前者是来源到线程的单射，后者是满射。二者同时成立时，来源与环境相容线程之间才有
双射。没有分离时只能恢复行为线程；没有完备时，逆极限中还可能有数学上相容但
实际来源没有实现的幽灵线程。这正是 `stateThread_bijective_iff_complete_and_separates`
与 `local_global_atlas_exactness` 所分开的两个条件。

若环境层等于实际像，即 \(Y_{i,n}=Y_{i,n}^0\)，且 \(\Omega\) 有限、每层实际像也有限，
限制映射由共同来源条件满射，基数最终稳定，稳定段上的限制为双射，完备性可由此
另行推出。环境层含有额外候选值时，这个有限稳定性不推出环境逆极限完备性；下面的
反例刻意使用无限来源，避免把有限稳定性误当作一般逆极限完备性。

### 26.6 四个边界反例

**反例 26.A（行为恢复不等于来源恢复）。** 取
\(\Omega=\{0,1\}\)，唯一动作是 `Stop`，两个来源都返回同一个 `ok`，没有后续动作。
于是 \(\sim=\Omega\times\Omega\)。四个视图都取常值 \(*\)，满足精确行为表示，
视图之间的运输是恒等；但 \(\theta(\omega)=\omega\) 不可能经由常值读出因子化，
来源不可恢复。

**反例 26.B（跨层投影不自然）。** 细层为
\(S_f=\{a,b\}\)，粗层为 \(S_c=\{*\}\)，且 \(p(a)=p(b)=*\)。唯一动作在两层
都是自环，但细层在 \(a,b\) 上分别输出标签 \(0,1\)。若声明的粗任务保留这两个标签，
(RA.2602) 要求粗状态 \(*\) 同时给出两个不同输出，因而不存在粗层动态核。当前
粗读数相同不能替代跨层动态充分性。

**反例 26.C（数学互逆不等于实际取得）。** 取
\(\Omega=\{0,1\}\)，四个抽象视图及其 \(\chi\) 都是恒等，来源解码器也存在；但
所有合法读取协议只返回常量 `ok`，或者当前权限为空。抽象的行为和来源恢复成立，
\(\mathsf{Acq}\) 不成立，观察者不能实际取得该坐标。

**反例 26.D（相容线程不一定是真实来源）。** 取
\(\Omega=\{0,1\}^{\mathbb N}\setminus\{g\}\)，其中
\(g=(0,1,0,1,\ldots)\)。令环境层
\(Y_0=\{*\}\)、\(Y_n=\{0,1\}^n\ (n\ge1)\)，限制映射删除最后一位；实际像取
\(Y_n^0=Y_n\)，因为每个有限二进制前缀都有不等于 \(g\) 的延拓。于是环境逆极限
\(L=\{0,1\}^{\mathbb N}\) 含有 \(g\)，但 \(g\) 不来自任何实际来源。它满足全部
环境相容方程，却不在实际线程像中；无限层相容因此不推出实际来源存在，必须另加
完备性。这里的幽灵是环境逆极限元素，不是实际像中的值。

### 26.7 与既有章节及 Lean 支点的去重

第12节 TM.1201–1207 已处理同一分辨率上的四视图唯一运输、核交换以及“联合读出
完整不等于每个单页都可递归”。第25节 RA.2501–2517 已处理有限策略树、实际联合
后验、来源／纪元／游标／档案的联合边界和零即时互信息。本节只增加分辨率指标、
共同实际来源、层间实际像投影、输出推前以及四视图—分辨率交换，不重复这些单层
证明。有效分辨率卷第10—11节已给具体投影与仿射模边界；本节只抽象其自然性，不
重算那些整数公式。

可直接对应的既有形式化支点为：

* `D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.lean` 的 `realized_image_unique_factorization_iff_reverse_kernel`：实际像上的唯一跨层因子与反向核包含等价；
* `D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization.lean` 的 `universal_sufficiency_factorization`：目标因子化与读出纤维恒定等价；
* `D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean` 的 `target_recovery_criterion`：指定来源目标恢复与目标在读出纤维上恒定等价；
* `D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality.lean` 的 `effective_image_naturality`：源运输、读出因子化和目标因子化推出实际像上的自然交换；
* `D5/S3/ConceptDynamics/Sufficiency/DescentCompositionLaw.lean` 的 `descent_composition_law`：连续层间半共轭的复合；
* `D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean` 的 `stateThread_injective_iff_separates`、`stateThread_bijective_iff_complete_and_separates`，以及 `LocalGlobalAtlasExactness.lean`：线程来源恢复所需的分离与完备双条件；
* 若要把单层确定更新压到最小前向商，可复用 `MinimalPredictiveCompletionQuotient.lean` 的 `minimal_predictive_completion_quotient`，不必另造最小商定义。

本节的新增组织是把这些支点放进同一实际来源的分辨率塔，并明确行为恢复、来源恢复和实际取得的不同量词；它没有把普通数学综合冒充 Lean 核验。

## 26.99 追加锚

## 27. 完整未来行为商与四视图的最小预测边界

第26节证明了一个共同实际来源上的空间、时间、边界和记忆视图可以同时对指定任务动态充分，并且能够沿分辨率投影交换。本节补上一个不同的问题：**动态充分的表示是否已经是最小的表示**。四个视图可以彼此精确恢复，却仍共同保留了对未来任务没有作用的历史细节；反过来，只比较当前读数也可能删掉之后才会被读出的关联。最小性必须相对于声明的未来实验族定义。

### 27.1 类型化未来行为与最小预测商

令 \(H\) 是同一个实际来源合同下的历史集合。历史可以包含来源、端口、档案、参考、权限、事件和工作记忆；它不是把分别可达的边缘状态任意拼起来的笛卡尔积。令 \(\mathcal V\) 是前缀闭合的有限类型化动作词族。一个词 \(v\) 只有在其前缀的输出接口与下一动作的输入接口相容时才属于 \(\mathcal V\)。

把一项未来实验的全部指定结果记为

$$
\operatorname{Resp}:\{(h,v):h\in H, v\in\mathcal V\}
\longrightarrow \mathcal O_v .
$$

\(\mathcal O_v\) 的标签必须保留当前任务要求区分的合法性、失败、读数、事件、writer、记录和终止信息；概率模型中把单个结果换成相应的结果分布。定义完整未来行为等价

$$
 h\mathrel{\sim_{\mathcal V}}h'
 \quad\Longleftrightarrow\quad
 \forall v\in\mathcal V,
 \quad
 \operatorname{Resp}(h,v)=\operatorname{Resp}(h',v).
 \tag{TM.2701}
$$

若比较的输出带有后继边界，则等式按相同类型的后继行为理解；若动作失败，则失败标签本身也是响应的一部分，不能静默删去。反身性、对称性和传递性逐词成立，所以可以定义最小预测商

$$
 C_{\mathcal V}=H/{\sim_{\mathcal V}},
 \qquad
 q_{\mathcal V}:H\to C_{\mathcal V},
 \qquad
 q_{\mathcal V}(h)=[h].
 \tag{TM.2702}
$$

“最小”在这里是划分意义下的最小，而不是先验地声称商有限、容易计算或实际可取得。它只合并在全部声明续接中都没有可见差别的历史。

**命题 27.1（最小预测商的因子化性质）。** 设 \(q:H\to Q\) 是一个候选边界，并且存在

$$
 \widehat{\operatorname{Resp}}:\operatorname{im}(q)\times\mathcal V
 \longrightarrow \mathcal O_v
$$

使得

$$
 \operatorname{Resp}(h,v)
 =
 \widehat{\operatorname{Resp}}(q(h),v)
 \qquad(h\in H, v\in\mathcal V).
 \tag{TM.2703}
$$

则存在唯一满射

$$
 d_q:\operatorname{im}(q)\twoheadrightarrow C_{\mathcal V},
 \qquad
 d_q(q(h))=[h],
 \tag{TM.2704}
$$

满足 \(d_q\circ q=q_{\mathcal V}\)。若 \(\ker q=\sim_{\mathcal V}\)，则 \(d_q\) 是双射；若 \(\ker q\) 严格细于 \(\sim_{\mathcal V}\)，则 \(q\) 动态充分但保留了可被任务商掉的额外历史。

**证明。** 若 \(q(h)=q(h')\)，由（TM.2703）对每个 \(v\) 有相同响应，故 \(h\sim_{\mathcal V}h'\)，于是 \(q(h)\mapsto[h]\) 良定义。它的像包含每个 \([h]\)，所以满射。由 \(d_q(q(h))=[h]\) 唯一确定。若两边的核相等，\(d_q\) 同时单射；若候选核更细，则至少有两个候选边界值落在同一个行为类上。证毕。

这个命题把“当前读数相同”与“未来可继续使用的边界相同”分开。一个只保留目标后验、单个端点或某个互信息数值的摘要，只有在它满足（TM.2703）时才是动态充分的；第25.5节的 \(X\oplus K\) 例子已经给出当前目标边缘相同而后续读 \(K\) 不同的反例。

### 27.2 前向执行与行为商的区别

式（TM.2701）比较的是完整有限续接的结果。若希望在商上逐步执行，而不是只在词的末端比较，还需要一个前缀闭合的更新合同。对每个可执行动作 \(a\)，要求同一行为类的代表具有相同的合法／失败标签、同类型的一步读数，并且每个正概率读数的后继行为质量能按行为类求和。确定性情形写成

$$
 q_{\mathcal V}(T_a h)
 =
 \overline T_a(q_{\mathcal V}(h)),
 \tag{TM.2705}
$$

概率情形则把右侧替换为后继类上的推前核。若这个一步条件失败，完整词的某个前缀仍能把两个代表区分开，因而不能把它们当作同一个可执行边界。反过来，在动作族对后继类质量完备时，对词长归纳可由（TM.2705）恢复（TM.2701）的所有有限响应。

因此有两个不同的对象：

* \(C_{\mathcal V}\) 是指定未来任务的最小预测商；
* 满足一步闭合的商才是可以继续驱动选择器和记录器的最小可执行边界。

第25节的策略树续接核给出了概率版的一步合同；本节只把它抽象成商的普适性质，不把迹等价自动冒充成 Markov 更新。

### 27.3 四视图的精确恢复、过度细化与最小性

令

$$
 E_{\mathrm{sp}},E_{\mathrm{tm}},E_{\partial},E_{\mathrm{mem}}:H\to X_i
$$

分别表示空间、时间、边界和记忆视图。若每个 \(E_i\) 都满足（TM.2703），则命题27.1给出唯一的满射

$$
 d_i:\operatorname{im}(E_i)\twoheadrightarrow C_{\mathcal V},
 \qquad d_i(E_i(h))=[h].
 \tag{TM.2706}
$$

若某个视图的核正好是 \(\sim_{\mathcal V}\)，则 \(d_i\) 是双射；两个精确视图之间有唯一运输

$$
 R_{ij}=d_j^{-1}\circ d_i,
 \qquad
 R_{jk}\circ R_{ij}=R_{ik},
 \qquad
 R_{ii}=\mathrm{id}.
 \tag{TM.2707}
$$

若四个视图都精确，四视图运输由同一个 \(C_{\mathcal V}\) 唯一决定。这说明“互相可恢复”与“已经最小”是两个命题：前者只要求视图间存在双射或指定运输，后者还要求它们的核等于完整未来行为等价。

例如在只有 `Stop` 且所有历史都返回同一个 `ok` 的任务中，取 \(H=\{h_0,h_1,h_2\}\)。原始历史身份 \(E(h_i)=h_i\) 与另一个复制身份的视图彼此可以恢复，且都动态充分；但

$$
 C_{\mathcal V}=\{[h_0]\}
$$

只有一个行为类。两个身份视图的运输存在，却都不是最小边界。相反，若一个视图把两个有不同未来响应的历史合并，它连动态充分都不是。因而不能由“四张图能互相翻译”推出“图中没有冗余”，也不能由“当前端点相同”推出“未来行为相同”。

把第39节的二叶 FIB 历史放入同一判据，可以得到更具体的分界。两条三步动作词若端点和长度相同，但事件词、档案或策略状态不同，则只有在声明的 \(\mathcal V\) 不读取这些差别时才属于同一行为类；一旦允许后续动作读取 writer 或由记忆选择下一步，它们就被（TM.2701）分开。第39节的有限顺序反例因此是行为商的一个测试样例，而不是仅凭端点恢复就可以删除的历史。

### 27.4 分辨率投影何时下降到最小商

设 \(H_s,H_r\) 是两个分辨率上的实际历史集合，\(p_{sr}:H_s\to H_r\) 是只在实际像上声明的投影。记对应行为等价为 \(\sim_s,\sim_r\)。在实际像闭合的前提下，下面的条件等价于存在唯一映射

$$
 \overline p_{sr}:C_s\to C_r,
 \qquad
 \overline p_{sr}([h]_s)=[p_{sr}(h)]_r,
 \tag{TM.2708}
$$

使得

$$
 \overline p_{sr}\circ q_s=q_r\circ p_{sr}:
 H_s\to C_r:
$$

$$
 h\sim_s h'
 \Longrightarrow
 p_{sr}(h)\sim_r p_{sr}(h').
 \tag{TM.2709}
$$

**证明。** （TM.2709）保证（TM.2708）的右侧与代表无关，故给出良定义的下降；满射性只需把 \(C_r\) 限制为 \(p_{sr}\) 的实际像行为类。反向地，若下降存在，\(q_s(h)=q_s(h')\) 时两边经 \(\overline p_{sr}\) 相等，立即得到（TM.2709）。唯一性由 \(q_s\) 的满射性确定。证毕。

若分辨率还带动作词运输 \(p_{sr}(T^s_a h)=T^r_{\bar a}p_{sr}(h)\)，并且读数／失败标签有相应推前，则（TM.2708）进一步给出商上的自然交换；只在状态集合上存在投影，不足以保证未来响应的自然性。连续投影的下降满足

$$
 \overline p_{rt}\circ\overline p_{sr}=\overline p_{st}
$$

但必须先检查每一层的实际像闭合及（TM.2709）。无限分辨率时，商线程的分离仍是单射条件，环境逆极限中的每条相容线程都来自实际来源则是完备条件；这两个条件不能由有限层下降自动推出。第26.5—26.6节的幽灵线程反例正说明了这一边界。

### 27.5 观察者记忆与可见端点回路

令 \(M:H\to M_0\) 是观察者当前记忆，\(p:M_0\to A\) 是由该记忆确定下一动作的策略读出，\(E:H\to X\) 是一个端点或时间视图。若存在两个合法动作词 \(u,v\) 使

$$
 E(T_u h)=E(T_v h),
 \qquad
 p(M(T_u h))\ne p(M(T_v h)),
 \tag{TM.2710}
$$

则 \(T_u h\) 与 \(T_v h\) 在包含下一步策略的未来族中不可能属于同一行为类。否则同一行为类会要求相同的下一动作合同，却给出两个不同的实际选择。若 writer 或记录读取本身区分 \(u\) 与 \(v\)，即使策略读出相同，也有同样结论。

这给出一个有限的记忆下界：端点视图可以把两条路径放回同一位置，但只要未来策略或记录仍能读取路径差别，完整预测边界就必须保留该差别，或保留一个在任务上等价的摘要。若策略完全经由端点因子化，即 \(p\circ M=\widehat p\circ E\)，则（TM.2710）的策略差别不再出现；这只消除了这一种区分，不能自动删除 writer、权限或其它未来读数。

第39节的二叶动作顺序提供了（TM.2710）的具体候选：两条顺序相反的三步词可以有相同端点和相同长度，而事件词或最后一步策略不同。第42节已经讨论一般有向回路和固定点；本节的增加点是把回路是否可商掉直接交给观察者的未来行为商，而不是把所有几何回路都当作同一种 holonomy。

### 27.6 有限反例与结论范围

有三个容易混淆的量应分开：

1. **当前信息量**，如 \(I(X;M)\) 或一个边缘后验；
2. **动态充分性**，即是否存在（TM.2703）这样的全部续接因子化；
3. **最小性**，即候选边界的核是否正好等于（TM.2701）。

第25.5节已经证明第一项相同不推出第二项；本节命题27.1证明第二项只推出候选到最小商的满射，不推出候选本身最小。一个候选边界可以因为保留档案、事件词或权限历史而过度细化，同时仍然完全正确。

因此本节的统一结论是

$$
\boxed{
\begin{gathered}
\text{完整未来行为商是指定任务下的最小预测边界；}\\
\text{动态充分候选都唯一下降到它，但可能保留冗余；}\\
\text{四视图互恢复要求共同商上的运输，最小性还要求核相等；}\\
\text{分辨率运输要先满足行为核的下降条件，逆极限仍须另验分离与完备。}
\end{gathered}}
\tag{TM.2711}
$$

这里的“最小”不等于有限、低成本或已被观察者实际取得；这里的“全息”也只表示对声明的 \(\mathcal V\) 足够。若扩大动作词、读数、writer 或权限合同，行为等价可能变细，原来的最小边界不再自动适用。反之，若任务明确不读取某类事件，则这些事件可以被行为商安全地合并。

本节可复用的形式化近邻包括 `ControlledBehaviorUniversality.lean` 的有限词行为与唯一因子化、`PredictiveMemoryMinimalQuotient.lean` 的最小预测记忆商、`MinimalPredictiveCompletionQuotient.lean` 的普适商，以及第26节列出的实际像下降和逆极限声明。本节新增的是把它们接到 FIB 四视图和观察者记忆的同一最小性判据上；上述组织和反例是理论正文推导，不计作新增 Lean 核验，也不构成物理时空定律。

## 27.99 追加锚

## 28. Clifford 历史的可拼接整数边界与叶预算记忆

### 28.1 来源、整数正规形与六步运输

本节把来源固定为 [FIBONACCI_ATOMIC_RELATION_GENERATION.md §§2–3](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的全部自由有序非空二叉树，并使用[该来源卷 §§355–357](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的 Clifford 叶积、替换与历史结论。它与 [RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md §§101–107](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md) 的随机来源、概率选择器和停止记录分开。设 $\mathcal T$ 由非空自由语法

$$
t::=\alpha\mid\beta\mid\langle s,u\rangle,
\qquad s,u\in\mathcal T,
$$

生成，且叶的实际顺序和括号都保留。实际替换与同源三项窗口为

$$
\begin{aligned}
\rho(\alpha)&=\beta,\qquad \rho(\beta)=\langle\beta,\alpha\rangle,\\
\rho(\langle s,u\rangle)&=\langle\rho(s),\rho(u)\rangle,\\
W_3(t)&=\bigl(E(t),E(\rho t),E(\rho^2t)\bigr).
\end{aligned}
$$

令 $A=E(\alpha)$、$B=E(\beta)$，其中 $E(\langle s,u\rangle)=E(s)E(u)$，并令 $G=\langle A,B\rangle$ 为指定 Clifford 单位中的子群。已有关系为

$$
A^2=1,
\qquad B^2=-1,
\qquad AB+BA=1.
$$

置 $S=BA$。于是

$$
S^2=S+1,
\qquad S^{-1}=S-1,
\qquad B=SA,
\qquad ASA=1-S=-S^{-1}.
\tag{28.1}
$$

**引理 28.1（全群的整数正规形）。** 每个 $g\in G$ 唯一写成

$$
N(e,k,p)=(-1)^eS^kA^p,
\qquad e,p\in\{0,1\},\quad k\in\mathbb Z.
\tag{28.2}
$$

正规坐标的乘法为

$$
(e,k,p)(f,\ell,q)=
\bigl(e+f+p\ell\bmod2,\ k+(-1)^p\ell,\ p+q\bmod2\bigr).
\tag{28.3}
$$

证明。$A^{-1}=A$、$B^{-1}=-B=B^3$ 且 $-1=B^2$，所以任意包含逆字母的群字都能先化为正的 $A,B$ 字。由 $ASA=-S^{-1}$，共轭保整数幂，对每个 $\ell\in\mathbb Z$ 都有

$$
AS^\ell A=(-S^{-1})^\ell=(-1)^\ell S^{-\ell},
\qquad AS^\ell=(-1)^\ell S^{-\ell}A.
$$

此式也覆盖负指数，因为共轭保逆。于是用 $B=SA$ 逐字移项得到（28.2），存在性成立；反过来，（28.2）的每个元也都属于 $G$。为证唯一性，$1,S$ 张成的偶部分与 $A,B$ 张成的奇部分直和；这是来源卷 §355 的 $1,A,B,AB$ 线性无关性的直接后果，因为 $S=1-AB$ 且 $SA=B$。所有正规元都是非零单位，所以偶、奇两类不能在直和的唯一交点零处相等。定义偶子代数上的实同态

$$
\Phi(a+bS)=a+b\varphi,
\qquad \varphi=\frac{1+\sqrt5}{2},
$$

其中 $\varphi^2=\varphi+1$。若 $(-1)^eS^k=(-1)^fS^\ell$，应用 $\Phi$ 得 $(-1)^e\varphi^k=(-1)^f\varphi^\ell$。因 $\varphi>1$，符号和整数指数都分别相同；右乘 $A$ 后同样得到奇部分的唯一性。最后，将 $A^p$ 穿过 $S^\ell$ 使用上述全整数换位式，再合并 $A^{p+q}$，得到（28.3）。$\square$

由来源卷 §356 的等级对合共轭 $J$，有

$$
J(A)=A+B=S^2A,
\qquad J(B)=-B,
\qquad J(S)=1-S=-S^{-1}.
$$

因此 $J$ 在正规坐标上是

$$
 j(e,k,p)=(e+k\bmod2,\ 2p-k,\ p),
 \qquad j^2=\operatorname{id}.
\tag{28.4}
$$

这给出不依赖树代表的整数运输；它只是在同一实际单位上重写来源卷 §356 的 $J$。

### 28.2 三元观察边界与实际载体

令 $g_\alpha$、$g_\beta$ 表示两个原子的前三项正规坐标：

$$
\begin{aligned}
g_\alpha&=\bigl((0,0,1),(0,1,1),(0,1,0)\bigr),\\
g_\beta&=\bigl((0,1,1),(0,1,0),(0,2,1)\bigr).
\end{aligned}
\tag{28.5}
$$

对三元组逐坐标使用（28.3）定义乘法 $\odot$，并定义

$$
F(u_0,u_1,u_2)=(u_1,u_2,j(u_0)).
\tag{28.6}
$$

若 $\mathbf u(t)$ 是 $W_3(t)$ 的正规坐标，则

$$
\mathbf u(\langle s,v\rangle)=\mathbf u(s)\odot\mathbf u(v),
\qquad
\mathbf u(\rho t)=F(\mathbf u(t)).
\tag{28.7}
$$

定义实际载体

$$
\mathcal C_3=\{\mathbf u(t):t\in\mathcal T\},
$$

它是三元正规坐标空间中的实际像，而不是整个 $G^3$。由（28.5）及（28.3）归纳可得每个实际三元组都满足

$$
 p_0=p_1+p_2\pmod2.
\tag{28.8}
$$

原子三元组满足此式；逐坐标乘法把三个 $p$ 分量相加，$F$ 只循环三个分量并保持该等式，故对所有非空树成立。式（28.8）只是必要条件，不能把满足它的环境点自动当作实际树来源；特别地，计算中使用的三重单位元不代表空树。

由来源卷 §356 的 $F^6=\operatorname{id}$ 及全历史纤维定理，实际来源的以下对象互相决定：三元边界 $\mathbf u(t)$、$W_3(t)$、完整历史 $\mathscr H(t)$。坐标到观察是逐坐标的 $N$，历史更新是 $F$，所以这三个表示可以在实际载体上逐项恢复。原树的括号、叶路径和前缀分解属于更强的来源表示，并不由此恢复。

**命题 28.2（指定操作族的行为核）。** 考虑由读取 $E$、施加 $\rho$、在左侧或右侧拼接一个已知实际上下文组成的任意有限记录实验。这些操作在全部 $\mathcal T$ 上合法，合法性不依赖来源代表；控制规则只读取公开上下文和已记录的动作、读数。在实际载体 $\mathcal C_3$ 上，两个来源具有相同三元坐标，当且仅当每个这样的实验都给出相同的动作与精确读数记录。

这里的动作合同只记录这些代数动作和精确读数；输出不包括源叶数、费用或耗时、原始来源档案或导航信息、绝对迭代时刻，也不以源叶数上限或容量限制改变动作合法性。

证明。若坐标相同，拼接由（28.7）逐坐标乘法给出，运输由 $F$ 给出；对操作序列归纳，所有读数均相同，因而依赖这些记录的控制也选择相同动作。反之，若三个坐标中第 $i$ 项不同，其中 $i\in\{0,1,2\}$，就恰施加 $i$ 次替换后读取 $E$。由 $W_3$ 的定义，读数直接是原窗口第 $i$ 项 $E(\rho^i t)=N(u_i(t))$；$N$ 的单射性使这次读数分离两个来源。左右拼接已知单位不会抹掉差异，因为群乘法可逆。于是该操作族的行为核正是坐标相等的核。这是对 §27 最小未来行为商在本任务上的具体实例，而非新的通用商定理。$\square$

已知实际上下文 $v$ 时，对已实现的右拼接 $\mathbf w=\mathbf u\odot\mathbf v$，恢复公式是 $\mathbf u=\mathbf w\odot\mathbf v^{-1}$；对已实现的左拼接 $\mathbf w=\mathbf v\odot\mathbf u$，恢复公式是 $\mathbf u=\mathbf v^{-1}\odot\mathbf w$。逆在每个坐标的群中计算，消去恢复的是实际被拼接的行为类，不把任意群逆当作实际树上下文。未知的左右分解一般没有唯一逆。换言之，坐标记忆、三项边界和完整时间历史在实际像上可互相运输，原始树和绝对经过时间仍是额外信息。

### 28.3 叶预算下的三维整数增长

令 $\lambda(t)$ 为叶数。给定公开整数 $L\ge1$，定义

$$
H_L=\{[t]_{\mathscr H}:1\le\lambda(t)\le L\},
$$

其中等价类是完整历史相等类；由（28.2）和命题28.2，也可用三元坐标相等定义。对任意有 $m$ 个叶的有序叶词，正规形中的指数满足

$$
 k=\sum_{\substack{1\le r\le m\\\text{第 }r\text{ 个叶为 }\beta}}
 (-1)^{r-1},
\qquad |k|\le\left\lceil\frac m2\right\rceil.
\tag{28.9}
$$

这是因为每个叶都使奇偶位翻转，而一个 $\beta$ 在第 $r$ 位只贡献 $(-1)^{r-1}$。两次替换把一片原叶至多变成四片叶，所以 $W_3$ 的三项叶词长度都不超过 $4L$，从而每个坐标的指数满足 $|k_j|\le2L$。每个坐标的 $e,p$ 各有两个取值，即三个坐标共六个二进制位，得到

$$
|H_L|\le64(4L+1)^3.
\tag{28.10}
$$

下面给出同阶下界。取固定括号的实际正叶块

$$
U=(\alpha\beta)^2,
\qquad V=\beta^2,
\qquad W=\alpha^2.
$$

由（28.3）直接计算

$$
\begin{aligned}
\mathbf u(U)&=\bigl((0,-2,0),(0,0,0),(1,0,0)\bigr),\\
\mathbf u(V)&=\bigl((1,0,0),(0,2,0),(0,0,0)\bigr),\\
\mathbf u(W)&=\bigl((0,0,0),(1,0,0),(0,2,0)\bigr).
\end{aligned}
\tag{28.11}
$$

对 $i,j,k\ge0$，先省略 $U^iV^jW^k$ 中零次重复的块，再将剩余非空块列表按固定括号拼接为 $T_{i,j,k}$；排除 $(i,j,k)=(0,0,0)$。其叶数为 $4i+2j+2k$，且三个坐标的指数分别为

$$
(-2i,\ 2j,\ 2k),
$$

三个 $e$ 位组成 $(j\bmod2,k\bmod2,i\bmod2)$，所有 $p$ 位为零。于是 $i,j,k$ 的不同必给出不同实际行为类。若 $i+j+k\le n=\lfloor L/4\rfloor$，则 $\lambda(T_{i,j,k})\le L$，故

$$
|H_L|\ge {n+3\choose3}-1.
\tag{28.12}
$$

上下界合起来给出

$$
|H_L|=\Theta(L^3)
\tag{28.13}
$$

这里没有断言实际像恰等于某个整格，也没有断言（28.12）的常数是最优常数。

### 28.4 固定宽度记忆与在线取得

固定公开 $L$，令静态精确编码使用 $b$ 位等长二进制串和一个对该 $L$ 固定、来源无关的解码器，不附加未计费历史旁信息。解码器必须恢复每个输入的三元行为边界。任何这样的编码都必须区分 $H_L$ 的不同类；否则两个行为类拥有同一编码，命题 28.2 给出的分离读数会矛盾。因而 $2^b\ge|H_L|$。反过来，$H_L$ 是有限的实际类集合，给它固定编号 $0,\ldots,|H_L|-1$，将编号写成 $\lceil\log_2|H_L|\rceil$ 位；固定解码器把各编号送回对应三元边界，再由 $F$ 恢复完整行为。这达到下界，所以精确静态最小位数为

$$
b_{\min}^{\mathrm{static}}(L)=\left\lceil\log_2|H_L|\right\rceil
 =3\log_2L+O(1).
\tag{28.14}
$$

上述可达性是固定 $L$ 的抽象静态编号；实际集合的枚举、编号表描述和解码计算成本另计，不包含在下面的坐标在线更新界中。这里没有给出 $|H_L|$ 的精确公式或最优在线秩算法。$H_L$ 限定初始输入家族，不是任意未来增长操作下的闭合活状态集。

一个明确的固定宽度坐标编码是：每个坐标存 $e,p$ 两位，再把 $k+2L\in\{0,\ldots,4L\}$ 存为
$\lceil\log_2(4L+1)\rceil$ 位。总长为

$$
6+3\left\lceil\log_2(4L+1)\right\rceil,
\tag{28.15}
$$

与（28.14）相差常数阶；这里没有声称存在同样简单的精确最优在线秩编码。

若输入是已取得的有序叶流，公开 $L$ 允许一个固定相位的有限转导器同时更新三项。每个原叶对 $(E,E\circ\rho,E\circ\rho^2)$ 的叶贡献为

$$
\begin{array}{c|ccc}
 &E(t)&E(\rho t)&E(\rho^2t)\\ \hline
\alpha&\alpha&\beta&\beta\alpha\\
\beta&\beta&\beta\alpha&\beta\alpha\beta
\end{array}
\tag{28.16}
$$

所以每片输入叶至多触发三个固定长度的正规形乘法。三个有符号 $k$ 计数器和六个相位位可原地维护；每次整数更新的位复杂度为 $O(\log(L+1))$，总算术更新为

$$
O(L\log(L+1)).
\tag{28.17}
$$

这里把源遍历、上下文取得、输入存储、固定描述以及展开后的输出分别计费。稳定坐标本身只需 $O(\log L)$ 工作空间；若要打印 Clifford 系数，另有

$$
S^k=F_{k-1}+F_kS\qquad(k\ge1),
\tag{28.18}
$$

其中 $F_r$ 是 Fibonacci 数，因此展开系数有 $\Theta(k)$ 位，不能把任意精确实数 oracle 的转换费用视为零。沿单独的 $\rho$ 轨道，$F^6=\operatorname{id}$；原三项指数满足 $|k_j|\le2L$ 时，应用（28.4）至多把界增至 $2L+2$。原树叶数仍随替换增长；另有允许的无界拼接强迫计数器无界，例如反复拼接 $V=\beta^2$，其第二坐标指数为 $2j$，其中 $j\ge1$ 是块数。不同 $j$ 给出不同可分离行为类，所以允许任意这类拼接时不存在普遍固定容量；此论证不要求每一次拼接都增加记忆。

### 28.5 可恢复性的边界与来源碰撞

坐标记忆恢复的是指定操作族的行为边界，而非来源本身。已有的实际碰撞说明这一点：$\alpha$ 与 $\rho^6(\alpha)$ 的完整历史相同，但叶数分别为 $1$ 和 $13$。在叶上限 $13$ 的另一任务中，把已知 $\alpha$ 作为新叶拼接到前者仍合法，而拼接到后者会超出上限；历史观察不能恢复这一来源容量条件。反向运行 $F$ 则在实际像上给出唯一、精确的前行为类：

$$
F^{-1}(u_0,u_1,u_2)=(j(u_2),u_0,u_1)=F^5(u_0,u_1,u_2).
$$

它由实际树 $\rho^5(t)$ 表示，并满足 $F(F^{-1}(\mathbf u(t)))=\mathbf u(t)$。这不认证所供应特定原树的原树前驱；例如 $\alpha$ 没有满足 $\rho(s)=\alpha$ 的实际树。六周期也不能恢复绝对迭代时刻，因为相差六次替换的实际来源仍有相同历史。

同样，绝对经过时间、原始遍历路径、括号结构和未公开的上下文拆分都没有被（28.2）编码。若把动作词扩展到这些对象，行为核会变细，必须重新计算边界和容量。三个整数指数刻画的是指定 Clifford 来源、精确叶读数、有限叶预算和已知上下文操作下的行为边界，不决定原始关系的数量或物理空间维数。

Clifford 平方约定、极化关系和标准代数构造沿用 Lundholm–Svensson，*Clifford algebra, geometric algebra, and applications*，arXiv:0907.5356v1，§§2.1–2.3；该文只支持标准 Clifford 背景。正规坐标、实际三元载体、拼接行为核、三维增长和容量结论均由 [FIBONACCI_ATOMIC_RELATION_GENERATION.md §§2–3、355–357](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 与本节的显式计算推出，不把标准文献当作这些项目特定结论的来源。这些是普通数学理论推导，不包含新增的 Lean 核验。

## 28.99 追加锚

## 29. 组成细化的 Clifford 行为边界、实际容量与条件时间恢复

### 29.1 同一来源与叶阈值合同

本节沿用 §28 的全部非空有序原树 $\mathcal T$、Clifford 观察 $E$、三元正规坐标 $\mathbf u$、逐坐标乘法 $\odot$ 和运输 $F$。组成取自 [FIBONACCI_ATOMIC_RELATION_GENERATION.md §3](FIBONACCI_ATOMIC_RELATION_GENERATION.md)：

$$
c(t)=(a(t),b(t)),\qquad \lambda(t)=a(t)+b(t),\qquad
c(\rho t)=Mc(t),\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

**定义 29.2（带公开阈值的来源合同）。** 定义联合边界及其实际像

$$
\eta(t)=(\mathbf u(t),c(t)),\qquad
\mathcal J=\eta(\mathcal T).
$$

操作为读取 $E$、施加 $\rho$、在左侧或右侧拼接一个公开已知的实际非空上下文 $v\in\mathcal T$，以及对每个公开可选整数 $h$ 只读

$$
P_h(t)=\mathbf 1_{\{\lambda(t)\le h\}}.
$$

上下文的身份在记录中保留，已知的 $\eta(v)$ 可用于计算；同一实验比较使用同一个上下文，而非仅使用相同叶数的未知代表。一个指令指定上述动作、可选的后继读数 $E$ 或 $P_h$、以及可选整数叶上限 $H$。只读指令的候选来源就是当前来源。若未附上限，动作执行并记录 `accept` 及所请求的后继读数；若附上限，先在候选来源上判断 $\lambda\le H$，成功时同样记录并更新，失败时只记录 `reject`，不返回后继读数且原来源不变。记录还含动作名、上下文身份、所用 $h,H$ 和读数种类；无读数的动作仍记录其接受或拒绝。

有限实验的控制只使用公开输入和累积记录。合同不把未知 $\eta(t)$ 直接供应给控制器，也不记录原树、遍历路径、费用、物理耗时或额外协议相位。这里的普遍量词允许全部整数 $h$ 和任意有限的公开 $H$；它不同于仅允许一个固定活上限的合同。

**命题 29.3（普遍阈值合同的精确行为核）。** 对任意 $s,t\in\mathcal T$，定义 29.2 中所有有限实验的完整记录相同，当且仅当 $\eta(s)=\eta(t)$。因而 $\eta$ 是该合同的充分语义状态；任何能确定所有这些记录的状态都必须区分不同 $\eta$。这不供应边界的取得算法或读数 oracle。

证明。联合边界的闭合更新为

$$
\begin{aligned}
(\mathbf u,c)&\xmapsto{\rho}(F\mathbf u,Mc),\\
(\mathbf u,c)&\xmapsto{\text{右拼接 }v}
 (\mathbf u\odot\mathbf u(v),c+c(v)),\\
(\mathbf u,c)&\xmapsto{\text{左拼接 }v}
 (\mathbf u(v)\odot\mathbf u,c(v)+c).
\end{aligned}
$$

$E$ 是 $N(u_0)$，$P_h$ 和后继叶上限判断都是后继组成之和的函数。若两边界相同，则候选边界、接受或拒绝及读数均相同；拒绝后两边界仍相同。对记录长度归纳，依赖记录的控制也总选择同一指令。

反之，若 $\mathbf u$ 不同，某个窗口坐标 $i\in\{0,1,2\}$ 不同，施加 $i$ 次 $\rho$ 后读取 $E$，由引理 28.1 的正规形唯一性分离。若组成不同，令

$$
\lambda_0=a+b,\qquad \lambda_1=a+2b,
\qquad a=2\lambda_0-\lambda_1,\quad b=\lambda_1-\lambda_0.
$$

两个组成必在 $\lambda_0,\lambda_1$ 中至少一项不同。对该项取两个叶数中的较小者为 $h$，在初态或一次替换后读 $P_h$ 即分离。每个实验只用一个有限阈值，整个合同则量化全部阈值。若仅用带上限的指令表述动作，也必须允许自由选择有限高上限：取大于两条待比较有限路径上全部候选叶数的 $H$，就能实现前述替换探针；带 $h$ 上限的只读 $E$ 指令，其接受或拒绝也能实现 $P_h$。固定一个活上限不保证这些探针可执行。$\square$

### 29.4 五个整数与一个六叶障碍

**引理 29.5（实际像上的相位恢复与更新）。** 写 $u_i=(e_i,k_i,p_i)$，其中 $i=0,1,2$。在实际联合像 $\mathcal J$ 上，五个整数

$$
\xi(t)=(k_0,k_1,k_2,a,b)
$$

与 $\eta(t)$ 互相决定。具体地，令

$$
(b_0,b_1,b_2)=(b,a+b,a+2b).
$$

则

$$
(p_0,p_1,p_2)=(a+b,a,b)\bmod2,
\qquad
e_i=\left(\frac{b_i-k_i}{2}\right)\bmod2.
$$

每个分子都是偶数。对 $\xi=(k_0,k_1,k_2,a,b)$ 和 $\zeta=(\ell_0,\ell_1,\ell_2,d_0,d_1)$，实际拼接的五整数为

$$
\bigl(k_i+(-1)^{p_i}\ell_i\bigr)_{i=0}^2
\quad\text{与}\quad (a+d_0,b+d_1),
$$

其中相位 $p_i$ 取自左因子 $\xi$。实际替换为

$$
\xi(\rho t)=
\bigl(k_1,k_2,2((a+b)\bmod2)-k_0,b,a+b\bigr).
$$

证明。每片叶的 Clifford 像是奇元素；原树及前两次替换的叶数分别为 $a+b,a+2b,2a+3b$，其奇偶分别为 $a+b,a,b$。由来源卷引理 357.2 的整数子环字符，另记其为 $\vartheta$ 以免与本节 $\eta$ 混淆，有

$$
\vartheta(A)=1,\qquad \vartheta(B)=3,\qquad
\vartheta(S)=3\quad\text{于 }\mathbb F_5.
$$

$S^{-1}=S-1$ 仍在该整数子环内，故字符也适用于负的整数幂。于是

$$
\vartheta(N(e_i,k_i,p_i))=(-1)^{e_i}3^{k_i}
 =3^{2e_i+k_i}=3^{b_i}.
$$

$3$ 的阶为 $4$，所以 $2e_i+k_i\equiv b_i\pmod4$。这同时给出整除性与 $e_i$ 的唯一二进制值。因而五整数保留全部有限相位，并非删去相位信息。拼接的指数公式直接来自（28.3），组成相加；替换的指数公式来自 $F$ 和（28.4），组成由 $M$ 更新。相位再由上述公式恢复。所有陈述均限于同一原树生成的实际像；这些等式不构成任意环境五元组的完整实现判据。$\square$

**命题 29.6（叶数不足以闭合替换；固定活上限粗化行为划分）。** 对以下正叶词取固定括号的原树

$$
P=\alpha\alpha\alpha\beta\alpha\alpha,
\qquad Q=\beta\beta\alpha\beta\beta\beta.
$$

它们满足

$$
\begin{aligned}
\mathbf u(P)=\mathbf u(Q)
 &=\bigl((1,-1,0),(1,0,1),(0,3,1)\bigr),\\
c(P)&=(5,1),\qquad c(Q)=(1,5),\\
\lambda(P)=\lambda(Q)&=6,\qquad
\lambda(\rho P)=7,\quad \lambda(\rho Q)=11.
\end{aligned}
$$

因此 $(\mathbf u,\lambda)$ 不能决定替换后的叶数。若合同只允许读取 $E$、读取固定 $P_6$，以及附固定上限 $6$ 的替换和非空左右拼接，则 $P,Q$ 的所有有限完整记录相同，尽管 $\eta(P)\ne\eta(Q)$。在这一受限合同下，$\eta$ 充分但不是最小行为商。

证明。令 $S=BA$，逐叶使用（28.3），或等价地使用 $A^2=1,B^2=-1,AS^m=(-1)^mS^{-m}A$，得到

$$
\begin{aligned}
E(P)&=A^3BA^2=AB=-S^{-1},
&E(Q)&=B^2AB^3=AB,\\
E(\rho P)&=B^3SB^2=-A,
&E(\rho Q)&=S^2BS^3=-A,\\
E(\rho^2P)&=S^3(S^2A)S^2=S^3A,
&E(\rho^2Q)&=(S^2A)^2S(S^2A)^3=S^3A.
\end{aligned}
$$

这给出所列三个正规坐标。组成由叶词直接计数，后继叶数是 $a+2b$。固定上限 $6$ 时，任何非空拼接都有至少 $7$ 片叶，两棵树的替换也都超限，故所有修改指令都拒绝且保持各自初态。两初态的 $E$ 和 $P_6$ 相同；对记录归纳，每个依赖记录的有限控制都得到相同记录。定义 29.2 的无界阈值合同则可在替换后以 $P_8$ 分离二者，不能把两个合同的最小性结论混用。$\square$

### 29.7 实际联合像的五维增长与静态记忆

**定理 29.8（短块构造与实际容量）。** 对公开整数 $L\ge1$，令

$$
\mathcal J_L=\{\eta(t):1\le\lambda(t)\le L\}.
$$

则

$$
{\lfloor L/4\rfloor+5\choose5}-1
\ \le\ |\mathcal J_L|\ \le\
(2L+1)^3\left({L+2\choose2}-1\right).
$$

特别地 $|\mathcal J_L|=\Theta(L^5)$。这是实际联合像的增长，不是环境整数格点计数的等式。

证明。取以下五个实际正叶块，每块和块之间都使用固定括号：

$$
U=\alpha\beta\alpha\beta,\quad V=\beta\beta,\quad
W=\alpha\alpha,\quad R=\beta\alpha\beta\alpha,\quad
D=\alpha\beta\beta\alpha.
$$

由（28.3）乘四个或两个叶原子的三项坐标，得到五整数列

$$
\begin{array}{c|rrrrr}
 &U&V&W&R&D\\ \hline
k_0&-2&0&0&2&0\\
k_1&0&2&0&0&-2\\
k_2&0&0&2&0&2\\
a&2&0&2&2&2\\
b&2&2&0&2&2
\end{array}
$$

例如 $E(U)=(AB)^2=S^{-2}$、$E(R)=S^2$、$E(D)=AB^2A=-1$；其后两项由叶替换后同一乘法得到。每块的三个位 $p_i$ 均为零，所以按固定顺序拼接非负次重复的块时，三个指数与两个组成直接相加；$e_i$ 由引理 29.5 恢复。

五列组成的矩阵为

$$
K=\begin{pmatrix}
-2&0&0&2&0\\
0&2&0&0&-2\\
0&0&2&0&2\\
2&0&2&2&2\\
2&2&0&2&2
\end{pmatrix},\qquad \det K=-128.
$$

将五列除以 $2$，得到首三行为 $(-1,0,0,1,0)$、$(0,1,0,0,-1)$、$(0,0,1,0,1)$，末两行为 $(1,0,1,1,1)$、$(1,1,0,1,1)$。以首三行消去末两行的前三项，末尾 $2\times2$ 块变为 $\left(\begin{smallmatrix}2&0\\2&2\end{smallmatrix}\right)$。因此除以 $2$ 后的行列式为 $(-1)\cdot1\cdot1\cdot4=-4$，原行列式为 $2^5(-4)=-128$。故 $K$ 在整数五元组上单射。

对 $(i,j,k,r,d)\in\mathbb N^5\setminus\{0\}$，省略零次块，将 $U^iV^jW^kR^rD^d$ 的非空块列表按固定括号拼接成一棵树。它的五整数恰为 $K(i,j,k,r,d)^{\mathsf T}$，不同五元组给出不同实际联合边界，叶数为

$$
4i+2j+2k+4r+4d\le4(i+j+k+r+d).
$$

取五元组之和不超过 $n=\lfloor L/4\rfloor$，非零选择数为 ${n+5\choose5}-1$：加入松弛量后是六个非负整数之和等于 $n$，按隔板计数，再排除全零五元组。这证明下界。构造中不把省略全部块解释为空树。

对上界，组成满足 $a,b\ge0$、$1\le a+b\le L$，共有 ${L+2\choose2}-1$ 个可能值。由（28.9），前两次替换的叶词长度至多 $4L$，所以每个 $|k_i|\le2L$。组成固定时，引理 29.5 强制 $k_i\equiv b_i\pmod2$，区间 $[-2L,2L]$ 中指定奇偶的整数至多 $2L+1$ 个；$e_i,p_i$ 均由组成和指数决定，不能再乘一个相位因子。故每个组成至多对应 $(2L+1)^3$ 个实际联合边界。下界的五次增长与上界的五次增长合并即得结论；未满足实际像约束的环境候选只会使上界宽松。$\square$

**推论 29.9（固定宽度容量、条件纤维与供给叶流）。** 对固定公开 $L$，不附来源旁信息，要求固定且来源无关的解码器恢复所有 $\mathcal J_L$ 中的边界。其精确静态最小等长位数是

$$
b_{\min}^{\mathrm{static}}(L)=\left\lceil\log_2|\mathcal J_L|\right\rceil
 =5\log_2L+O(1).
$$

明确的五整数编码可取

$$
3\left\lceil\log_2(4L+1)\right\rceil
+2\left\lceil\log_2(L+1)\right\rceil
$$

位。若已供应有序叶流，至多 $L$ 片叶的坐标算术更新可用 $O(L\log(L+1))$ 位运算与 $O(\log L)$ 坐标工作空间。作为普通静态条件计数，另有

$$
\begin{aligned}
\max_{\mathbf u}\#\{c:(\mathbf u,c)\in\mathcal J_L\}&=\Theta(L^2),\\
\max_{\mathbf u,m}\#\{c:(\mathbf u,c)\in\mathcal J_L,\ a+b=m\}&=\Theta(L).
\end{aligned}
$$

证明。精确解码要求不同联合边界有不同码，故 $2^b\ge|\mathcal J_L|$。给有限实际像固定编号并解码回边界即达到 $\lceil\log_2|\mathcal J_L|\rceil$，再用定理 29.8。显式编码将三个 $k_i+2L\in\{0,\ldots,4L\}$ 和 $a,b\in\{0,\ldots,L\}$ 分别写为固定宽度；有限相位由引理 29.5 恢复。

供给叶流时，从三重群单位及零组成开始积累，逐片叶使用（28.5）与（28.3）更新三个指数和相位，并递增相应组成。空前缀仅是计算初值，不是来源树。也可每步由五整数重算相位；所需数个整数均为 $O(L)$，每片叶只需常数次 $O(\log(L+1))$ 位操作。最终相位可由五整数恢复，无须另存于输出码。这里的工作空间是坐标空间；源遍历、输入取得与存储、上下文供给、枚举与编号表描述、解码计算及展开 Clifford 系数的输出分别计费。静态编号可达性不提供精确最优在线秩算法，也不把 $\mathcal J_L$ 当作未来任意增长操作下的闭合活空间。五个整数描述边界，不决定物理寄存器的最少数目。

第一类纤维至多含 ${L+2\choose2}-1=O(L^2)$ 个组成。投影到 $\mathbf u$ 的实际像是 §28 的 $H_L$，其大小为 $\Theta(L^3)$；由 $|\mathcal J_L|=\Theta(L^5)$，至少一条纤维含 $\Omega(L^2)$ 个组成。第二类纤维至多含 $m+1\le L+1$ 个组成；投影到 $(\mathbf u,m)$ 至多有 $L|H_L|=O(L^4)$ 个值，因此至少一条纤维含 $\Omega(L)$ 个组成。这是最大静态纤维结论，不要求每条纤维有该规模，也不供应新的记忆取得机制。$\square$

### 29.10 拼接逆、实际前驱与时间恢复

**命题 29.11（条件消去与实际像判据）。** 对已实现的右拼接 $w=\langle s,v\rangle$，已知同一个实际上下文 $v$ 时，联合边界恢复为

$$
\eta(s)=\bigl(\mathbf u(w)\odot\mathbf u(v)^{-1},c(w)-c(v)\bigr).
$$

对已实现的左拼接 $w=\langle v,s\rangle$，群因子的顺序反过来：

$$
\eta(s)=\bigl(\mathbf u(v)^{-1}\odot\mathbf u(w),c(w)-c(v)\bigr).
$$

对于任意供应的 $w,v$，记前两式给出的右拼接消去候选与左拼接消去候选分别为 $q_R$ 与 $q_L$。则

$$
\begin{aligned}
q_R\in\mathcal J
&\iff \exists s\in\mathcal T,\quad \eta(\langle s,v\rangle)=\eta(w),\\
q_L\in\mathcal J
&\iff \exists s\in\mathcal T,\quad \eta(\langle v,s\rangle)=\eta(w).
\end{aligned}
$$

组成非负本身不充分；每个候选属于 $\mathcal J$ 只认证相应拼接方向上的行为分解，不认证供应原树 $w$ 的根分解。

同样，若 $c(t)=(a,b)$，唯一环境前驱候选是

$$
\left(F^{-1}\mathbf u(t),(b-a,a)\right),\qquad
F^{-1}(u_0,u_1,u_2)=(j(u_2),u_0,u_1).
$$

它属于 $\mathcal J$ 当且仅当存在实际 $s$ 使 $\eta(\rho s)=\eta(t)$，并不等价于供应原树 $t$ 在 $\rho(\mathcal T)$ 中。

证明。三项 Clifford 值均为群单位，逐坐标乘法左右分别可消去；组成相加在整数群中也可消去。若候选属于 $\mathcal J$，选择实现它的非空树 $s$，按相应拼接方向代回闭合更新便得到 $\eta(w)$；若实际行为分解存在，消去唯一性迫使候选就是 $\eta(s)$。实际根分解是更强条件，等式 $\eta(\langle s,v\rangle)=\eta(w)$ 没有原树单射性可用。替换部分用 $F$ 的逆及 $M^{-1}(a,b)=(b-a,a)$ 作完全相同的双向代入。实际像成员资格仍是条件，非负组成与相位恢复式没有代替它；此处不提供一般实际像求解器。$\square$

**命题 29.12（非负候选与原树前驱的两个失效）。** 取 $t=\langle\alpha,\beta\rangle$。其替换前驱候选组成为 $(0,1)$，却不存在实际前驱行为类。另取

$$
t_+=\langle\beta,\langle\beta,\alpha\rangle\rangle,
\qquad t_-=\langle\langle\beta,\beta\rangle,\alpha\rangle.
$$

二者 $\eta$ 相同，但仅 $t_+$ 属于原树替换像。即使联合边界和前驱行为类均可恢复，也不能恢复供应原树的前驱合法性。

证明。$c(t)=(1,1)$，所以前驱候选组成是 $(0,1)$。这一组成的非空实际树只能是单叶 $\beta$，而 $\rho\beta=\langle\beta,\alpha\rangle$。其初始叶积为 $BA=S$，$E(t)=AB=-S^{-1}$，二者不同，例如（28.2）的指数分别为 $1,-1$。故 $\eta(\rho\beta)\ne\eta(t)$，候选不属于 $\mathcal J$。类似地，任意 $w=t,v=\alpha$ 的右消去候选也有非负组成 $(0,1)$，但初始群值为 $ABA=A-B\ne B$，不等性由来源卷 §355 的 $A,B$ 线性无关性给出，所以不能仅凭组成非负认证右行为分解。

$t_+,t_-$ 具有相同叶词 $\beta\beta\alpha$，每次替换后仍有相同叶词，因此三元观察和组成都相同。前者是 $\rho(\langle\alpha,\beta\rangle)$。后者不是任何叶的替换像；若是某个二元原树的替换像，则其右子树 $\alpha$ 必须属于 $\rho(\mathcal T)$。但叶 $\alpha$ 没有前驱：两种原子的像分别为 $\beta$ 和二元树，二元树的像也必为二元树。因此后者没有原树前驱。$\square$

**定理 29.13（丰富历史与有起点承诺的离散时间）。** 在同一实际来源上，丰富历史

$$
\mathscr R(t)=\bigl(E(\rho^n t),\lambda(\rho^n t)\bigr)_{n\ge0}
$$

与 $\eta(t)$ 互相决定。若公开给定初始联合边界 $\eta_0=(\mathbf u_0,c_0)\in\mathcal J$，且承诺只执行 $n$ 次 $\rho$、其中 $n\in\mathbb N$ 未知，则当前联合边界中组成 $c$ 至多对应一个 $n$；在联合边界层面，相容条件为

$$
c=M^nc_0,\qquad \mathbf u=F^n\mathbf u_0.
$$

这里恢复的是相对于给定初态和纯替换承诺的动作次数。没有起点，或允许拼接时，当前联合边界不恢复绝对纪元或物理经过时间。

证明。$\eta$ 由 $(F,M)$ 给出每个后继边界，故决定 $\mathscr R$。反向取前三级 Clifford 值恢复 $\mathbf u$，由前两项叶数 $\lambda_0,\lambda_1$ 及命题 29.3 的公式恢复 $a,b$，故决定 $\eta$。

每个实际组成 $c_0\in\mathbb N^2\setminus\{0\}$ 的 $M$ 轨道各项不同。为证此点，若 $c_r=(a_r,b_r)$，则

$$
\lambda_{r+1}-\lambda_r=b_r\ge0,
\qquad \lambda_{r+2}-\lambda_r=a_r+2b_r>0.
$$

故相隔至少两步的组成不同。相邻组成若相同，则 $M(a_r,b_r)=(a_r,b_r)$ 推出 $b_r=a_r$ 且 $a_r+b_r=b_r$，只能是零组成，与实际非空来源矛盾。因此 $c=M^nc_0$ 中的 $n$ 唯一；三元坐标须再满足 $F^n\mathbf u_0$，而不能以组成相符代替联合相容。给定实际实现初态并确有纯替换过程时，这些条件自动满足。反之，若两式成立，对初态的任一实际代表施加 $n$ 次替换即实现当前联合边界；这不认证另行供应原树的执行历史。

没有起点时，同一当前边界既可被称为零步初态，也可在有实际前驱时被称为其一步后继，故无绝对步数。允许拼接后，甚至固定原树起点 $\alpha$，两次替换得到 $\rho^2\alpha=\langle\beta,\alpha\rangle$，一次把已知 $\beta$ 左拼接到 $\alpha$ 也得到同一原树端点，动作次数却为二和一。该端点连原树都相同，联合边界当然不能区分。合同从未给出动作时长，所以纯替换次数也不能转成物理耗时。$\square$

上述联合核、五整数恢复、短块容量和条件逆是由本卷 §28 与来源卷 §§3、355–357 推出的项目特定结论（repo-derived）；标准群消去、有限编号与隔板计数仅作为证明中的通用步骤。适用范围始终是指定 Clifford 来源和指定记录合同，不把五维增长当作物理维数，也不把实际像上的条件恢复当作原树或无承诺时间的恢复。

## 29.99 追加锚


## 30. 固定活上限下的精确行为商、容量与恢复边界

本节把 §29 的公开阈值合同收紧为一个固定活上限。固定整数 $H\ge1$ 在一次运行开始前公开，并在运行中保持不变。令

$$
\mathcal T_H=\{t\in\mathcal T:1\le\lambda(t)\le H\}.
$$

来源仍是同一实际的非空有序 $α/\beta$ 原树；$B=E(\beta)$ 保持来源卷中的 Clifford 含义，$H$ 只是活叶上限。读指令返回 $E(t)$ 且不改变来源。替换 $ρ$ 以及给定实际非空上下文 $v$ 的左、右拼接，先检验候选叶数是否不超过 $H$；通过则更新来源并在记录中写入 `accept`，失败则只写入 `reject`，保持来源不变并不给出候选的 $E$。动作名、上下文身份、公共输入和初始记录都在记录中；比较两个来源时使用同一个程序、相同的公共输入和初始记录。有限自适应控制只读累积记录和合同明确供应的字段，不直接读取未知的 $η$，也没有隐藏的 $η$ 访问。不允许原树导航、时钟、费用、变阈值、重置、复制、新鲜未知来源，以及把来源重新解接或做逆向消去（消去）。上下文供应和守卫是语义接口；取得它们的算法和费用另行计数。这里的状态是来源响应语义，不是控制器或不断增长的档案。

### 30.1 三个窗口与固定上限的分层记录

写 $c(t)=(a,b)$，并置

$$
\lambda _0=a+b,
\qquad \lambda _1=a+2b,
\qquad \lambda _2=2a+3b=\lambda _0+\lambda _1.
\tag{TM.3001}
$$

更一般地，$λ_{i+2}=λ_i+λ_{i+1}$，而 $c(\rho^i t)=M^ic(t)$。令 $E_i(t)=E(\rho^i t)$；当需要上下文时写

$$
 d_i(v)=\lambda(\rho^i v)>0,
 \qquad h_i(v)=E(\rho^i v).
\tag{TM.3002}
$$

这里的 $d_i,h_i$ 是已知实际上下文所供应的语义参数，而不是免费取得的读数。沿用 §29 的 $η(t)$，其 Clifford 三窗正是 $(E_0,E_1,E_2)$，并附组成 $c$。

先定义固定上限的来源边界/档案候选

$$
q_H(t)=
\begin{cases}
(0,E_0(t),\lambda _0(t)),&\lambda _1(t)>H,\\[2mm]
(1,c(t),E_0(t),E_1(t)),&\lambda _1(t)\le H<\lambda _2(t),\\[2mm]
(2,\eta(t)),&\lambda _2(t)\le H.
\end{cases}
\tag{TM.3003}
$$

标签 $0,1,2$ 分别表示当前来源可安全继续的纯替换步数为零、恰为一步、至少为两步；标签 $2$ 的可观察视界在两步处截断。标签 $0$ 不保存第二窗，因为一次替换已经超出上限；标签 $1$ 保存到第二窗但不保存第三窗；标签 $2$ 保存 §29 的完整三窗。纯替换的未来叶数由 $M$ 生成，窗口读数由 $F$ 生成，因此不必预先保存无穷历史。

29.5 的相位公式给出一个等价的整数编码：标签 $0$ 保存 $e_0,k_0,\lambda _0$，其中 $e_0$ 直接存储，而 $p_0=\lambda _0\bmod2$；标签 $0$ 没有可用的组成字段，不能由组成和 $k_i$ 重建。标签 $1$ 保存 $a,b,k_0,k_1$；标签 $2$ 保存 $a,b,k_0,k_1,k_2$，这两种标签下的各 $e_i,p_i$ 均按引理 29.5 由组成和 $k_i$ 恢复。这个编码与（TM.3003）等价，不声称逐字段最小。

**引理 30.1（固定上限下的闭合更新）。** 设当前来源为 $t\in\mathcal T_H$，上下文 $v$ 为已知实际非空原树。

1. 右拼接 $\langle t,v\rangle$ 与左拼接 $\langle v,t\rangle$ 都恰在
   $\lambda _0(t)+d_0(v)\le H$ 时接受；拒绝时来源及已保留 profile 的 $E$/source 值完全相同；事件记录追加 `reject`，且不提供候选读出。
2. 对接受的右拼接，所有仍被记录的窗口满足
   $$
   E_i(\langle t,v\rangle)=E_i(t)h_i(v),
   \qquad c(\langle t,v\rangle)=c(t)+c(v),
   $$
   左拼接则为
   $$
   E_i(\langle v,t\rangle)=h_i(v)E_i(t),
   \qquad c(\langle v,t\rangle)=c(v)+c(t).
   $$
3. 标签 $0$ 的替换永远拒绝；标签 $1$ 的替换接受并落到标签 $0$，其新标签值为 $(0,E_1,\lambda _1)$；标签 $2$ 的替换永远接受，落到标签 $1$ 或 $2$，分别由 $\lambda _3>H$ 或 $\lambda _3\le H$ 决定。标签 $2$ 的完整字段按已有的 $F$、$M$ 更新为 $(F\mathbf u,Mc)$，再按新标签截断。
4. 标签 $0$ 的接受拼接仍为标签 $0$；标签 $1$ 的接受拼接若新的 $\lambda _1\le H$ 则仍为标签 $1$，否则落到标签 $0$，不可能上升到标签 $2$；标签 $2$ 的接受拼接可以落到任一标签。

**证明。** 叶数在左右拼接下相加，在替换下变为 $\lambda _1$，所以第 1 项直接来自固定守卫。$E$ 的结合乘法给出第 2 项；只在相应窗口仍可由合同访问时使用该式。标签 $0$ 的条件是 $\lambda _1>H$，故替换候选被拒绝。标签 $1$ 满足 $\lambda _1\le H<\lambda _2$，替换后的当前叶数为原 $\lambda _1$，而替换后的一次替换叶数为原 $\lambda _2>H$，故恰落标签 $0$。标签 $2$ 的替换候选叶数为原 $\lambda _1$，且原 $\lambda _1\le\lambda _2\le H$；替换后的后继的第一未来窗口大小是原 $\lambda _2$，第二未来窗口大小是原 $\lambda _3$，故分别由 $\lambda _3>H$ 或 $\lambda _3\le H$ 决定落到标签 $1$ 或 $2$，得到第 3 项。

拼接把每个 $\lambda_i$ 加上正数 $d_i(v)$。因此标签 $0$ 的 $\lambda _1$ 仍大于 $H$；标签 $1$ 的 $\lambda _2$ 原已大于 $H$，拼接后更大，故不可能进入标签 $2$；标签 $2$ 的两道不等式都可能改变。拒绝是恒等转移。归纳地，任意成功的混合路径都保持恰有一个 $\rho^j(t)$ 的出现，嵌在已知变换后的正组成上下文中；其组成恒为 $M^j c(t)+d$，其中 $d\in\mathbb N^2$ 已知。再施加 $\rho$ 保留这个单孔出现并把 $d$ 更新为 $Md$；左右拼接只把已知组成加到 $d$；拒绝则保留该出现和 $d$。这个单出现不变量统一覆盖所有混合路径；未知的更深窗口不会被上下文解锁。证毕。

**定理 30.2（固定活上限的精确行为核）。** 对 $s,t\in\mathcal T_H$，在上述固定合同下，所有使用相同程序、公共输入和初始记录的有限自适应实验产生相同完整记录，当且仅当

$$
q_H(s)=q_H(t).
\tag{TM.3004}
$$

因此，前述 $q_H$ 来源边界/档案确实给出 $Q_H=q_H(\mathcal T_H)$，它是该固定合同的最小行为商。

**证明。** 先证充分性。引理 30.1 表明每个动作的接受／拒绝、可见读数和候选后的标签都由当前标签、所保存字段以及公共上下文的 $d_i,h_i$ 确定。于是两个相同 $q_H$ 的来源在一步后仍有相同记录和相同的后继 $q_H$；对记录长度归纳，依赖累积记录的自适应控制也选择同一动作。

再证必要性。若标签不同，一次替换即可分离标签 $0$ 与标签 $1$ 或 $2$：前者记录 `reject`，后者记录 `accept`。标签 $1$ 与标签 $2$ 的第一次替换都接受，但第一次之后标签 $1$ 已落到 $0$，第二次替换拒绝；标签 $2$ 的第一次后继仍有下一次替换叶数等于原 $\lambda _2\le H$，所以第二次替换接受。若保存的 $E_i$ 不同，则在 $i$ 次合法替换后读取 $E$ 即分离，其中 $i=0,1,2$ 分别对应当前、标签 $1$ 可达和标签 $2$ 可达的窗口。

还需分离组成字段。若两个同标签来源的 $\lambda _0$ 不同，设较小者为 $x$、较大者为 $y$，则 $x<y\le H$。取固定括号的全 $\alpha$ 上下文 $v_d$，其叶数 $d=H-x\ge1$；在较小来源上右拼接被接受，在较大来源上被拒绝。若 $\lambda _0$ 相同而组成仍不同，则 $\lambda _1$ 不同。对标签 $1$ 或 $2$，先作一次共同合法替换，再对新来源使用叶数为 $H-\min(\lambda _1(s),\lambda _1(t))$ 的全 $\alpha$ 上下文；该数为正，较小的第二窗口接受而较大的拒绝。因为 $a,b$ 由 $\lambda _0,\lambda _1$ 经 $a=2\lambda _0-\lambda _1$、$b=\lambda _1-\lambda _0$ 唯一恢复，组成不同必落入这两种情形。上述脚本只依赖公开上下文和记录，不需要未知来源的尺寸探针、重置或取消。故核恰为（TM.3003）的相等核。证毕。

### 30.2 遗失窗口的实际见证

**命题 30.3（固定上限下的不可逆窗口丢失）。** 取原子卷定理 356.4 的两棵固定括号树

$$
 p=\langle\alpha,\langle\alpha,\beta\rangle\rangle,
 \qquad
 q=\langle\beta,\langle\alpha,\alpha\rangle\rangle.
$$

它们的组成与三窗为

$$
 c(p)=c(q)=(2,1),
 \qquad
 (\lambda _0,\lambda _1,\lambda _2)=(3,4,7),
$$

$$
 E_0(p)=E_0(q)=B,
 \qquad E_1(p)=E_1(q)=-S,
 \qquad E_2(p)=S^4A=2A+3B,
 \qquad E_2(q)=A.
\tag{TM.3005}
$$

所以 $q_4(p)=q_4(q)$（事实上 $q_5,q_6$ 也相同），而 $q_7(p)\ne q_7(q)$。在上限 $H=7$ 下，二者都可接受同一个右侧 $\alpha$ 拼接；拼接后组成与三窗叶数均为

$$
 c=(3,1),
 \qquad (\lambda _0,\lambda _1,\lambda _2)=(4,5,9),
$$

且两者的 $E_0=BA=S$、$E_1=(-S)B$ 相同，故两者的后继都具有同一个标签 $1$ 的 $q_7$。

**证明。** 三窗值和（TM.3005）正是原子卷定理 356.4 的显式 Clifford 计算；$S^4A=2A+3B\ne A$ 由 $1,A,B,AB$ 的线性无关性得到。右侧 $\alpha$ 的组成增量为 $(1,0)$，故叶数按（TM.3001）变为 $(4,5,9)$；右乘相同的 $E_i(\alpha)$ 保持前两窗相等，且 $5\le7<9$ 给出标签 $1$。于是不存在一个只看 $q_7(\langle s,\alpha\rangle)$ 和已知 $\alpha$ 的取消映射，能恢复原来的 $q_7(s)$：对 $s=p,q$，映射输入相同而输出应不同。这不与实际原树的差别或 Clifford 群中的消去律矛盾；被丢弃的是固定上限合同中的第三窗。

命题 29.6 的 $P,Q$ 是同一现象的另一见证：它们在 $H=6$ 的 $q_6$ 相同，但在 $H=7$ 时一次替换分别接受和拒绝。两组例子只用于应用既有的原子卷和 §29 计算，不引入新的来源词。证毕。

### 30.3 商的容量与静态记忆

由定理 30.2，$Q_H$ 是实际闭合的固定合同商。对 $H\ge3$，有

$$
|\mathcal J_{\lfloor H/3\rfloor}|
\ \le\ |Q_H|\ \le\ |\mathcal J_H|,
\tag{TM.3006}
$$

其中 $\mathcal J_L$ 是 §29.8 的实际联合像。事实上，若 $\lambda _0(t)\le\lfloor H/3\rfloor$，则 $\lambda _2(t)\le3\lambda _0(t)\le H$，所以其完整 $\eta$ 被 $q_H$ 的标签 $2$ 保留；另一方面 $q_H$ 的三种标签和字段都由 $\eta$ 决定，故它从 $\mathcal J_H$ 因子化。复用定理 29.8 的实际正块增长，得到

$$
|Q_H|=\Theta(H^5),
\qquad
b_{\min}^{\mathrm{static}}(H)=\left\lceil\log _2|Q_H|\right\rceil
 =5\log _2H+O(1).
\tag{TM.3007}
$$

这里的位数是固定 $H$、来源无关的静态精确编码下界；给 $Q_H$ 任意固定编号即达到它。它不包括来源取得、上下文供应、守卫、解码表、扩展输出、控制器存储、累计档案存储或运行时间的费用。

小上限可直接算出

$$
|Q_1|=2,
\qquad |Q_2|=6.
\tag{TM.3008}
$$

$H=1$ 只有 $\alpha,\beta$，其 $E_0$ 为 $A,B$。$H=2$ 的六棵树由两片叶的四种有序词和两个单叶组成，$E_0$ 依次为

$$
A,\ B,\ 1,\ AB,\ BA,\ -1,
$$

这些值两两不同，因此固定商也有六个类。

### 30.4 提高上限的投影与恢复

令 $H\le K$，仍只在同一个实际集合 $\mathcal T_H$ 上比较两个合同。定义

$$
\pi_{K,H}:q_K(\mathcal T_H)\longrightarrow Q_H,
\qquad
\pi_{K,H}(q_K(t))=q_H(t).
\tag{TM.3009}
$$

这个映射满射且良定义。为看清其纤维，若 $q_K(t)$ 为标签 $0$，则 $\lambda _1(t)>K\ge H$，所以 $q_H(t)$ 也是标签 $0$，并直接取其 $E_0,\lambda _0$；若为标签 $1$，其 $c,E_0,E_1$ 已给出，$q_H$ 要么保留同一标签和字段，要么在 $H<\lambda _1$ 时降为标签 $0$；若为标签 $2$，完整 $\eta$ 给出 $q_H$ 的任一标签。故同一 $q_K$ 值必有同一 $q_H$ 值，且每个 $Q_H$ 值由原来的 $t$ 命中，证明了（TM.3009）。

对一个声明的实际子族 $\mathcal S\subseteq\mathcal T_H$，§27.4 的（TM.2708）—（TM.2709）给出一般逆判据：从 $q_H(\mathcal S)$ 恢复 $q_K(\mathcal S)$ 的映射存在，当且仅当 $q_K$ 在每个 $q_H$ 纤维上为常值；要使它成为（TM.3009）的逆，等价地要求两者在 $\mathcal S$ 上的核相等。若附加供应侧信息 $r(t)$，同一判据作用于 $(q_H(t),r(t))$ 与 $q_K(t)$ 的两项联合映射。侧信息只有在实际纤维上区分被删除的字段时才改变结论。

对固定标签 $1$ 的 $q_H$ 纤维，组成和 $E_0,E_1$ 已固定，因而 $\lambda _2$ 也固定。若 $K<\lambda _2$，提升后的标签仍为 $1$，没有新字段；若 $K\ge\lambda _2$，提升为标签 $2$，唯一新增的是 $E_2$，等价的整数描述正是 29.5 的 $k_2$（其相位由已知组成恢复）。若该 $k_2$ 在实际纤维上变化，旧的 $q_H$ 不能恢复提升后的商；若不变化，则该纤维上可以恢复。标签 $2$ 的 $q_H$ 已保留完整 $\eta$，所以对同一来源它对每个更大的 $K$ 都足够。统一地，$K\ge3H$ 保证 $\lambda _2\le3\lambda _0\le3H\le K$，因而在 $\mathcal T_H$ 上全部来源都保留 $\eta$；这只是充分阈值，不是最优阈值。

静态投影不是受守卫动作的交织子。若 $\lambda _0(t)\le H<\lambda _1(t)\le K$，则同一个替换在 $H$ 合同中被拒绝，而在 $K$ 合同中被接受，并把来源送出 $\mathcal T_H$；所以（TM.3009）不能单独给出两个动态系统之间的动作交换。提高权限时，若被删除的区别在旧 profile 的实际纤维上变化，就不能仅从该旧 profile 计算它；保留实际来源可以用新合同做新的实验，但统一的取得协议仍需另一证明。标签 $2$ 已保留完整 $\eta$，或附加侧信息在该纤维上区分被删除字段时，前述恢复例外成立。上述恢复始终是行为商和已供应字段的恢复，不是物理时间、原始树或历史路径的恢复。

### 30.5 来源、复用与边界

本节的固定守卫合同、标签闭合和必要性脚本是对本仓库 §29 的具体收紧，属于 repo-derived 普通数学推导。Clifford 碰撞复用原子卷定理 356.4 已有的 [FIBONACCI_ATOMIC_RELATION_GENERATION.md §356.4](FIBONACCI_ATOMIC_RELATION_GENERATION.md) $p,q$ 示例；固定上限的另一对复用本卷命题 29.6；行为商的下降和逆判据复用本卷 §27.4 的（TM.2708）—（TM.2709），五整数相位编码复用本卷引理 29.5，容量增长复用 §§29.8—29.9。标准群消去、实际像上的有限编号和隔板计数只是这些证明中的通用步骤。

本节依赖来源卷已声明的 Clifford 构造和本卷既有结果；正文是普通数学推导，不声称 Lean 内核核验。来源取得、原树导航或恢复、解码表生成、控制器与累计档案存储、物理寄存器、运行时间和物理时间仍不在结论内。

## 30.99 追加锚

## 31. 同一未知原树的初始行为边界取得、八叶阈值与公共尺寸恢复

### 31.1 初始目标与实际取得记录

**定义 31.1（共同初始化的初始边界识别）。** 固定公开整数 $H\ge1$，全部来源、读口、动作、守卫和拒绝语义均取自 §30。未知初始来源为 $t\in\mathcal T_H$；运行中的实际来源记为 $t_{\mathrm{cur}}$。目标是输出初始值 $q_H(t)$，不是停止时的 $q_H(t_{\mathrm{cur}})$，也不是原树 $t$。一个确定性记录控制协议对所有允许的初始来源使用相同程序、公共输入、初始记录和初始控制态；每个下一动作、停止决定和最终输出只依赖这些公共量及已取得记录。称它识别初始边界，若对每个 $t\in\mathcal T_H$ 都经过有限次来源调用后停止，并输出恰为 $q_H(t)$ 的值。协议可以保留任意大的已取得档案；定义不把未知初始边界、组成或叶数供应给它。运行没有复位、复制、新鲜未知来源、变上限、来源逆向解接或隐藏的尺寸／$\eta$ 读口。

这里采用 [RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md §55](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) 的共同初始化与连续自适应识别语义；其加一来源、高位读口、正等待限制和容量公式不移到本来源。该卷引理 56.2 的配置分离原理在这里通过定理 30.2 应用：若两个不同的初始目标在某一步拥有相同完整已见记录以及相同当前 $q_H$，以后所有记录、控制选择和输出都相同。所保留的是完整记录，所以任意扩大档案容量也不能补回从未进入记录的区别。这只是既有确定未来结论的应用，不重新定义通用识别博弈。

**定义 31.2（先存窗口、再填至首次拒绝的协议）。** 对每个固定 $H$ 使用以下同一个确定性动作规则。开始时三项窗口寄存器均为空，计数 $j=s=0$，相位为首读。

1. 读取当前 $E$ 并保存为 $E_0$，然后尝试一次 $\rho$。
2. 若这次拒绝，保持 $j=0$ 并直接进入填充相位。若接受，置 $j=1$，读取并保存 $E_1$，再尝试第二次 $\rho$。第二次拒绝则直接进入填充相位；第二次接受则置 $j=2$，读取并保存 $E_2$ 后进入填充相位。不尝试第三次替换。
3. 填充相位反复在右侧拼接已知单叶 $\alpha$。每次接受仅把 $s$ 加一；遇到第一次拒绝即停止来源调用，令 $n=H-s$，输出取得记录
   $$
   \Gamma_H(t)=(j,E_0,\ldots,E_j,n).
   \tag{TM.3101}
   $$

所有拼接都保持原有固定上限 $H$，填充期间不读取 $E$。每次拒绝只有合同中的 `reject`，不读取被拒绝候选。窗口值是在实际来源尚处于相应替换位置时保存的；式（TM.3101）是上述执行的结果，不是预先供应的来源 profile。终止输出表可以再作用于这份取得记录，恢复下面所指定的初始目标。

**定理 31.3（窗口数与填充计数的实际含义）。** 对每个 $H\ge1$ 和每个实际 $t\in\mathcal T_H$，定义 31.2 的协议合法且有限停止。所得 $j$ 恰为初始 $q_H(t)$ 的标签；其中 $j=2$ 表示初始来源至少有两次可接受替换。保存的窗口为初始 $E_i(t)$，$0\le i\le j$。填充开始时的实际来源恰为 $\rho^j(t)$，并且

$$
s=H-\lambda_j(t),\qquad n=\lambda_j(t),
\qquad \lambda(t_{\mathrm{cur}})=H\text{ 于终止时}.
\tag{TM.3102}
$$

证明。初始来源已在上限内，所以首读合法。第一次替换接受当且仅当 $\lambda_1\le H$；若拒绝，初始标签就是 $0$。第一次接受后的来源为 $\rho(t)$，此时第二次替换接受当且仅当 $\lambda_2\le H$。因此恰一次接受后遇到拒绝给标签 $1$，两次接受给标签 $2$，没有用来源叶数端口。读取发生在每次接受之后而在任何填充之前，故保存值分别是 $E_i(t)$。拒绝不改变来源，故填充前恰为 $\rho^j(t)$，其叶数 $\lambda_j$ 满足 $1\le\lambda_j\le H$。

一次右拼接 $\alpha$ 恰增加一片叶，所以前 $H-\lambda_j$ 次拼接都接受，下一次候选有 $H+1$ 片叶而拒绝。于是有限停止，成功计数与 $n$ 正是（TM.3102）。这也覆盖 $\lambda_j=H$：填充相位的第一个拼接就拒绝，$s=0$，仍有一次最终拒绝调用。来源的当前叶数在停止时为 $H$；初始窗口保存在记录中，不能把填充后的当前来源当作初始来源。

最小上限 $H=1$ 的两个来源也分别完整执行：对 $\alpha$，首读 $A$，第一次替换接受并读 $B$，第二次替换拒绝，第一次填充也拒绝，得到 $(j,E_0,E_1,n)=(1,A,B,1)$；对 $\beta$，首读 $B$，第一次替换拒绝，第一次填充拒绝，得到 $(j,E_0,n)=(0,B,1)$。标签 $2$ 的填充前叶数至少为二，因为 $\lambda_2=2a+3b\ge2$；这一事实也覆盖标签 $2$ 的零次成功填充端点。$\square$

### 31.2 初始边界的精确八叶阈值

**定理 31.4（全初始家族的统一取得阈值）。** 在恰为 §30 的固定合同下，对每个固定整数 $H\ge1$，存在一个对全部 $t\in\mathcal T_H$ 共同初始化、确定性、逐点有限停止的记录控制协议，识别初始 $q_H(t)$，当且仅当

$$
H\le8.
\tag{TM.3103}
$$

允许任意大的已取得档案和控制载体，否定方向仍成立。这里每个 $H$ 同时指定初始家族 $\mathcal T_H$ 和目标 $q_H$；式（TM.3103）不比较一个固定来源家族在不同资源下的取得能力。

证明。先设 $H\le8$，执行定义 31.2。标签 $0$ 时，定理 31.3 给出 $n=\lambda_0$，故直接输出

$$
(0,E_0,n)=q_H(t).
\tag{TM.3104}
$$

对其余两个标签，复用引理 29.5 与原子卷引理 357.2 的整数子环字符 $\vartheta$。在实际初始读数上

$$
\vartheta(E_0)=3^b\in\mathbb F_5^\times,
\qquad (3^0,3^1,3^2,3^3)=(1,3,4,2).
\tag{TM.3105}
$$

这四个值各不相同，故从已保存 $E_0$ 唯一取得 $r\in\{0,1,2,3\}$，满足 $b\equiv r\pmod4$。这是对读数作已知函数，不增加来源端口。

标签 $1$ 时，取得的 $n=\lambda_1=a+2b\le8$，所以 $0\le b\le\lfloor n/2\rfloor\le4$。在 $0,\ldots,\lfloor n/2\rfloor$ 中，给定模四余数只有一个候选，唯一可能的二候选情形是 $n=8,r=0$，此时 $b=0$ 或 $4$，相应组成为 $(a,b)=(8,0)$ 或 $(0,4)$。组成第一种的所有实际树都是八片 $\alpha$ 的叶词，故 $E_1=B^8=1$；第二种都是四片 $\beta$ 的叶词，故 $E_1=(BA)^4=S^4\ne1$。这里 $B^2=-1$ 给出 $B^8=1$，$S^4\ne1$ 来自引理 28.1 的正规形唯一性。括号不影响结合的叶积。已经保存的 $E_1$ 因而分离这一例外，不需要再动作；$H\le8$ 下 $n=8$ 也强制 $H=8$。确定 $b$ 后令 $a=n-2b$，输出

$$
(1,(a,b),E_0,E_1)=q_H(t).
\tag{TM.3106}
$$

标签 $2$ 时，取得的 $n=\lambda_2=2a+3b\le8$，故 $0\le b\le2$。这三个整数有不同模四余数，$r$ 唯一确定 $b$；然后

$$
a=\frac{n-3b}{2},\qquad
q_H(t)=\bigl(2,((u_0,u_1,u_2),(a,b))\bigr),
\qquad N(u_i)=E_i.
\tag{TM.3107}
$$

正规坐标 $u_i$ 由引理 28.1 唯一取得。所得 $a$ 的整除性、非负性和组成正确性由实际输入及定理 31.3 保证；解码器只在已声明的实际记录像上使用这些公式，不要求解决任意环境元组的树实现问题。三种标签的输出合起来识别初始边界。

再设 $H\ge9$。置 $r_H=H-9\ge0$，给下列三个非空正叶词各取一个固定括号的实际原树：

$$
X_H=\beta\beta\alpha\beta\beta\alpha^{r_H},
\qquad Y_H=\alpha^H,
\qquad Z_H=\alpha\beta^4\alpha^{r_H}.
\tag{TM.3108}
$$

这里的非空叶词统一按从左至右的左结合括号生成原树。零次重复只表示省略尾部叶块；$X_9,Z_9$ 本身仍各有五片叶，不引入空来源或运行时未知上下文。直接计数组成及替换叶数得到

$$
\begin{aligned}
c(X_H)=c(Z_H)&=(H-8,4),
& (\lambda_0,\lambda_1,\lambda_2)(X_H)
 =(\lambda_0,\lambda_1,\lambda_2)(Z_H)&=(H-4,H,2H-4),\\
c(Y_H)&=(H,0),
& (\lambda_0,\lambda_1,\lambda_2)(Y_H)&=(H,H,2H).
\end{aligned}
\tag{TM.3109}
$$

三棵树都属于 $\mathcal T_H$，且都为标签 $1$，因为第一替换叶数等于 $H$，第二替换叶数严格大于 $H$。

逐叶使用 $\rho(\alpha)=\beta$、$\rho(\beta)=\beta\alpha$，相应第一替换叶积的原子贡献为 $B,S$。初始叶积为

$$
\begin{aligned}
E_0(X_H)&=B^2AB^2A^{r_H}=A^{r_H+1}=A^H,\\
E_0(Y_H)&=A^H,\\
E_0(Z_H)&=AB^4A^{r_H}=A^{r_H+1}=A^H.
\end{aligned}
\tag{TM.3110}
$$

等式用到 $B^2=-1$、$B^4=1$、$A^2=1$ 和 $H-(r_H+1)=8$。为计算下一窗口，由 $B=SA$ 及 $ASA=-S^{-1}$ 的整数幂形式有

$$
S^2BS^2=S^3AS^2=S^3S^{-2}A=SA=B.
\tag{TM.3111}
$$

因而

$$
\begin{aligned}
E_1(X_H)&=S^2BS^2B^{r_H}=B^{r_H+1}=B^H,\\
E_1(Y_H)&=B^H,\\
E_1(Z_H)&=BS^4B^{r_H}\ne B^H.
\end{aligned}
\tag{TM.3112}
$$

最后一个不等式也完全在实际来源中验证：若相等，左乘 $B^{-1}$ 再右乘 $B^{-r_H}$ 得 $S^4=B^{H-1-r_H}=B^8=1$，与正规形唯一性矛盾。$X_H,Y_H$ 的初始标签值因组成不同而不同；$X_H,Z_H$ 的初始标签值因 $E_1$ 不同而不同。这三个是实现了指定读数的原树，不以环境 tuple 的可实现性为假设。

现在考虑任意声称识别全家族的确定性有限协议。只读 $E$ 在三棵树上都返回 $A^H$；拼接任何叶数 $d_0(v)>4$ 的已知非空上下文，无论在左在右，都在三者上拒绝且不改变来源。它们的候选叶数分别为 $H-4+d_0(v)>H$ 与 $H+d_0(v)>H$。因此只由这些动作组成的任意共同前缀在三者上拥有相同记录，包括上下文身份、动作名及可选的后继读取请求；被拒绝候选没有读数。共同公共输入和控制初始化也相同。

正确协议不能在这样的共同前缀上停止，因为三者的初始 $q_H$ 不同；也不能永远只作这些动作，因为每个输入须有限停止。故必有第一条其余的来源动作。§30 的动作菜单使它只能是 $\rho$，或在某一侧拼接叶数 $1\le d_0(v)\le4$ 的已知实际非空上下文。

若该动作是 $\rho$，三者都接受。对 $X_H,Y_H$，其当前叶数都为 $H$，后继再替换叶数分别为原 $\lambda_2=2H-4$ 与 $2H$，均严格大于 $H$。其当前 $E$ 都为 $B^H$，故两者的当前边界合并为

$$
q_H(\rho X_H)=q_H(\rho Y_H)=(0,B^H,H).
\tag{TM.3113}
$$

接受记录相同，若该指令请求随后读取 $E$，两读数也相同。它们的初始标签仍因组成不同而不同。

若该动作是拼接 $v$，则在 $X_H,Z_H$ 上都接受，在 $Y_H$ 上拒绝。$X_H,Z_H$ 的新叶数同为 $H-4+d_0(v)$；其新第一替换叶数同为 $H+d_1(v)>H$，因为实际非空上下文总有 $d_1(v)>0$。故两者都落入标签 $0$。右拼接时其当前读数同为 $A^Hh_0(v)$，左拼接时同为 $h_0(v)A^H$。所以按实际选定的拼接侧，合并后的当前边界分别同为

$$
\begin{cases}
(0,A^Hh_0(v),H-4+d_0(v)),&\text{右拼接},\\
(0,h_0(v)A^H,H-4+d_0(v)),&\text{左拼接}.
\end{cases}
\tag{TM.3114}
$$

这一对的完整已见记录相同，包括本次 `accept` 与任何可选后继 $E$；其初始边界却由（TM.3112）不同。

两种可能的首动作都产生“同记录、同当前 $q_H$、不同初始目标”的一对。直接应用定理 30.2 的一步闭合与确定控制归纳，这一对未来的所有来源响应和控制选择都相同，故协议停止时输出相同，不能同时正确恢复两个初始目标。档案即使任意大，保存的仍是相同记录；来源原树虽可仍然不同，合同内不再有区分它们的动作。矛盾，排除所有这样的识别协议。

成对可区分性没有被否定：$X_H,Z_H$ 可由一次 $\rho$ 后读取 $E$ 分离；$X_H$ 或 $Z_H$ 与 $Y_H$ 可由右拼接已知四叶 $\alpha^4$ 的接受／拒绝分离。这些分别存在的脚本不能在同一未知来源上共同执行而保留全部初始区别，正是上述首次动作所揭示的障碍。正向与否定方向合起来证明（TM.3103）。$\square$

### 31.3 公共初始尺寸下任意上限的恢复

**定理 31.5（固定公共尺寸的充分恢复条件）。** 给定公开整数 $H\ge1$ 和 $1\le m\le H$，把允许初始家族限制为

$$
\mathcal T_{H,m}=
\{t\in\mathcal T_H:\lambda_0(t)=m\}.
\tag{TM.3115}
$$

同一个 $m$ 对全家族公开，且控制初始化仍与未知来源无关。定义 31.2 的原协议在任意这样的 $H,m$ 下都取得初始 $q_H(t)$；无需供应全 $Q_H$ 转移表。已知初始尺寸是附加的先验／定义域限制，不是在全 $\mathcal T_H$ 上已取得的信息，也不主张它是必要或最小侧信息。

证明。执行的接受／拒绝规则不变，定理 31.3 仍给出标签 $j$、初始窗口以及 $n=\lambda_j(t)$。若 $j=0$，直接输出 $(0,E_0,m)$，此时填充所得 $n$ 也等于 $m$。若 $j=1$ 或 $2$，因为 $a+b=m$，分别有

$$
\lambda_1=a+2b=m+b,
\qquad \lambda_2=2a+3b=2m+b.
$$

因此统一的反解是

$$
b=n-jm,
\qquad a=(j+1)m-n\qquad(j=1,2).
\tag{TM.3116}
$$

实际记录保证这两个整数非负，且和为 $m$。标签 $1$ 输出 $(1,(a,b),E_0,E_1)$；标签 $2$ 将保存三窗转成唯一正规坐标并与 $(a,b)$ 配成 $\eta$，输出 $(2,\eta)$。每个字段都是初始字段。不同于定理 31.4 在全家族中只靠模四信息，式（TM.3116）由同一个已公开的初始 $m$ 给出完整 $b$，所以不受八叶限制。取得动作只有原合同中的两次以内替换、实际读取和单叶拼接，不需要隐藏组成端口、复位、复制或来源逆操作。$\square$

### 31.4 有限控制载体与来源调用界

**定理 31.6（显式有限控制和调用上界）。** 对固定公开 $H$，定义 31.2 的取得记录有一个共同初始化的确定有限控制载体。对 $H\le8$ 接上定理 31.4 的固定输出表，或对公开 $m$ 的 $\mathcal T_{H,m}$ 接上定理 31.5 的固定输出表，就得到相应初始边界识别器。取得阶段的来源调用数不超过

$$
H+4.
\tag{TM.3117}
$$

此数计算每次读取、每次替换尝试和每次拼接尝试，包含最终拒绝的拼接与任何拒绝的替换；固定内部表操作另计。

若读数通过一个固定、来源无关的转换接口变成引理 28.1 的紧凑正规坐标，则所存控制字段可编码为 $O(\log(H+1))$ 位。该位数只计控制载体字段；转换表的描述／构造、转换计算、展开 Clifford 输出、算术硬件或工作区和物理运行时间不包含在界内。不主张调用数或控制容量最优。

证明。可取相位集合为

$$
\{R_0,T_1,R_1,T_2,R_2,\mathrm{Fill},\mathrm{Out},\mathrm{Invalid}\},
\tag{TM.3118}
$$

其中 $R_i$ 读取并写入第 $i$ 个窗口寄存器，$T_i$ 尝试第 $i$ 次替换。共同起态为 $R_0$，三个寄存器为空，$j=s=0$。$R_0$ 后继为 $T_1$；$T_1$ 接受时置 $j=1$ 并去 $R_1$，拒绝时去 $\mathrm{Fill}$。$R_1$ 后继为 $T_2$；$T_2$ 接受时置 $j=2$ 并去 $R_2$，拒绝时去 $\mathrm{Fill}$。$R_2$ 后继为 $\mathrm{Fill}$。$\mathrm{Fill}$ 每次只发出右拼接 $\alpha$，接受则将 $s$ 加一并留在此相位，拒绝则去 $\mathrm{Out}$。终止输出只由 $j,s$ 和已保存窗口计算 $n=H-s$，再使用声明的固定输出表；不再读取来源。一般 $H$ 的取得阶段可以输出 $\Gamma_H$，并不据此声称全家族的初始 $q_H$ 都能解码。

三个窗口寄存器各有一个空标记；$j\in\{0,1,2\}$、$s\in\{0,\ldots,H-1\}$。每个实际保存的 $E_i$ 来自当时至多 $H$ 片叶的来源，故（28.9）给 $|k_i|\le H$，且 $e_i,p_i\in\{0,1\}$。因此每个寄存器的正规坐标字母表大小至多 $1+4(2H+1)$。用上述八相位，整个字段乘积载体大小至多

$$
24H\bigl(1+4(2H+1)\bigr)^3.
\tag{TM.3119}
$$

这是可用的有限载体上界，包含未使用标记、全部相位和终止配置，不是最小值。若要求总表，可将不符合相位的响应、越界字段、读数转换的非法标记或非实际记录的解码失败统一送到 $\mathrm{Invalid}$，其固定输出为非法标记并停止；终止配置形式后继取自身。实际合同中的执行由定理 31.3 及上述解码证明保证不会进入该相位；包括在 $s=H-1$ 时也不会再收到成功填充的响应。这样总化未使用表项不添加来源能力，也不改变允许输入的输出。

正规形唯一性保证每个可能读数只有一个坐标表示。对固定 $H$，所有这样的读数属于有限集合，所以可预先固定一张来源无关的读数到坐标／控制／输出表，或另行提供实现此转换的方法。原 $E$ 端口并未自动供应紧凑坐标；有限表的存在不等于它的构造或读取成本为零。在这项明确的表示接口下，每个 $k_i+H$ 用 $\lceil\log_2(2H+1)\rceil$ 位，三个寄存器的有限相位位与空标记、$j$ 和有限控制相位只用常数位，$s$ 用 $\lceil\log_2H\rceil$ 位（$H=1$ 时零位）即可，故得到所述 $O(\log(H+1))$ 存储界。固定公共参数的表示若也计入，$H$ 及可选 $m$ 各用 $O(\log(H+1))$ 位，结论阶数不变。引理 28.1 的唯一坐标及定理 31.4、31.5 的解码公式足够，不需要枚举全 $Q_H$ 的动作转移表。

最后计来源调用。标签 $j=0$ 使用一读、一次替换尝试和 $H-n+1$ 次填充；标签 $j=1$ 使用两读、两次替换尝试和 $H-n+1$ 次填充；标签 $j=2$ 使用三读、两次替换尝试和 $H-n+1$ 次填充。因此总数分别为

$$
\begin{cases}
H-n+3\le H+2,&j=0,\ n\ge1,\\
H-n+5\le H+4,&j=1,\ n\ge1,\\
H-n+6\le H+4,&j=2,\ n\ge2.
\end{cases}
\tag{TM.3120}
$$

定理 31.3 已包括零次成功填充；最终拒绝仍由这里的 $+1$ 计入。$H=1$ 的 $\alpha$ 执行恰有五次来源调用，$\beta$ 执行恰有三次，也满足（TM.3117）。内部坐标转换、表查询和输出计算不属于上述来源调用，而是不同费用项。$\square$

### 31.5 识别语义、来源与恢复范围

**约定 31.7（文献对应与项目特定结论）。** Pavel Panteleev，[*Preset Distinguishing Sequences and Diameter of Transformation Semigroups*，arXiv:1412.0034v1，第1—2页](https://arxiv.org/pdf/1412.0034v1)，给出已知确定 Mealy 转移／输出下的初态识别与预定区别词语义；这里复用其“未知初态、已知动作语义”的区分，不引用预定词长度界作为本协议的来源调用界。Petra van den Bos、Frits Vaandrager，[*State Identification for Labeled Transition Systems with Inputs and Outputs*，arXiv:1907.11034v2，定义12—20与图3](https://arxiv.org/pdf/1907.11034v2)，给出按输出自适应的无环测试、观察迹分离及首次选择合并状态而不存在全状态自适应区别图的例子。这些语义已在 Context 卷 §55 路由；本节使用完整迹识别，不把它改成终止控制态独自解码的容量合同，也不把学习接口或区别测试的文献当作复位权限。

Clifford 叶积、三窗正规形、字符、组成替换和固定行为核分别复用本卷 §§28—30 与 [FIBONACCI_ATOMIC_RELATION_GENERATION.md §§355—357](FIBONACCI_ATOMIC_RELATION_GENERATION.md)。实际取得记录、八叶阈值、三个正叶来源的首次动作障碍及公共初始尺寸下的反解，是在这些前提上的 repo-derived 普通数学综合推导；所引识别文献不供应这一来源特定阈值，也不据此宣称文献原创性或 Lean 内核核验。

恢复的对象始终是初始固定合同的行为边界。窗口档案把替换位置上的时间读数与填充取得的容量关系组合起来；公共初始尺寸使同一个组成能够从最终可达窗口尺寸反解。它们不恢复原树括号、叶路径、绝对时间或来源逆向执行。定理 31.4 的全家族否定允许任意大的已见档案；定理 31.5 只给出一个明确充分的先验条件，不分类任意先验。本文没有关于随机控制、固定家族的资源反单调、物理维数、最优调用／记忆代价或全局关系统一的结论。

## 31.99 追加锚

## 32. 初始同源侧信息的八倍阈值、补充容量与操作次序

### 32.1 执行前证据与固定记录后的补充

**定义 32.1（两种初始侧信息合同）。** 固定公开整数 $H\ge1$。来源取 §30 的全部实际非空有序 $\alpha/\beta$ 原树 $\mathcal T_H$，读口为当前 $E$，修改动作仅为受固定活上限 $H$ 守卫的 $\rho$ 及已知实际非空上下文的左、右拼接。拒绝保持来源、记下拒绝而不返回候选 $E$。运行始终使用同一个实际未知来源，不供应复位、复制、新鲜未知来源、原树导航、逆向消去、变上限或额外尺寸读口。恢复目标始终是运行前的 $q_H(t)$。

令 $h:\mathcal T_H\to\mathcal L$ 为一个固定函数，其值由同一初始实际来源供应；$\mathcal L$ 是公开的有限非空标签字母表。区分以下两种合同。

1. **合同 A：执行前供应。** 一个共同的确定性记录控制程序在运行前收到 $h(t)$，可用它选择所有后续动作、停止决定和输出。相同标签的来源使用相同公共输入、初始记录和控制初始化。对每个 $t\in\mathcal T_H$，程序须在有限次来源调用后停止并输出初始 $q_H(t)$；允许任意大的已取得档案。
2. **合同 B：固定执行后的解码补充。** 来源动作完全按定义 31.2 执行，执行器忽略 $h$。一个固定解码函数只收到 $(\Gamma_H(t),h(t))$，并须对每个 $t\in\mathcal T_H$ 输出初始 $q_H(t)$。

若公开承诺一个实际子家族 $\mathcal F\subseteq\mathcal T_H$，上述全部正确性与有限停止要求只在该子家族上量化，并明确标出 $\mathcal F$。同一个公共初始尺寸 $m$ 限制来源家族为 $\mathcal T_{H,m}$；随来源变化的 $h(t)$ 在全 $\mathcal T_H$ 上供应额外证据。标签的产生、同源依据、交付和保留不属于 §30 的免费动作。

固定 $H$ 后，$\Gamma_H=(j,E_0,\ldots,E_j,n)$ 决定定义 31.2 的完整执行记录：$j=0$ 给第一次替换拒绝，$j=1$ 给第一次接受而第二次拒绝，$j=2$ 给两次接受；相应读取就是保存的窗口。随后恰有 $H-n$ 次右拼接 $\alpha$ 接受，再一次拒绝。动作顺序及上下文身份均已固定。因此合同 B 没有额外的隐藏完整记录可供解码。

对合同 A 的同标签来源，复用定理 30.2：一旦两个不同初始目标拥有相同完整已见记录及相同当前 $q_H$，共同确定程序以后选择相同动作并收到相同响应，最终输出相同。扩大已见档案不能解除这种合并；其归纳前提包括相同标签与共同初始化。初态识别和首次选择合并的语义沿用约定 31.7 中 Panteleev 以及 van den Bos–Vaandrager 的对应；这里没有新增复位权限或转移词长度结论。

**定义 32.2（容量与尺寸商标签）。** 写初始组成为 $c(t)=(a,b)$，并置

$$
m=a+b,\qquad \lambda_1=m+b,\qquad \lambda_2=2m+b.
\tag{TM.3201}
$$

对整数 $M\ge1$ 定义仅依初始尺寸的标签

$$
\sigma_M(t)=\left\lfloor\frac{m}{4}\right\rfloor\bmod M
\ \in\{0,\ldots,M-1\}.
\tag{TM.3202}
$$

记合同 A、B 在整个 $\mathcal T_H$ 上的最小可用标签字母表大小分别为 $M_A(H)$、$M_B(H)$。这里对任意固定标签函数 $h$ 和符合相应合同的程序或解码函数取最小值，不要求 $h$ 仅依尺寸，也不把标签生产费用计入这个容量。空标签字母表不可供应非空来源；大小一表示没有随来源变化的补充。

合同 B 的一般静态纤维计数和缺陷图着色框架复用仓内 [MinimalAppealLabelCount](../../../D5/S3/ConceptDynamics/Appeal/MinimalAppealLabelCount.lean)、[DefectGraphMinimumColoring](../../../D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring.lean) 及 [BinaryRepairCost](../../../D5/S3/ConceptDynamics/Coding/BinaryRepairCost.lean) 的相应结论。Charpenay–Le Treust–Roumy，[*Zero-Error Coding for Computing with Encoder Side-Information*，arXiv:2211.03649v1，定义 II.1、III.1、IV.1 与定理 III.4](https://arxiv.org/pdf/2211.03649v1)，提供成熟的零误差编码及图着色对应。该文的独立同分布多次来源、期望前缀长度率和成对共享侧信息假设不作为本节单来源、固定宽度补充及不可逆取得的前提，也不供应下面的数值阈值。

### 32.2 尺寸商标签的精确阈值

**定理 32.3（$\sigma_M$ 的八倍阈值）。** 对每个固定 $H,M\ge1$，以 $h=\sigma_M$ 在整个 $\mathcal T_H$ 上识别初始 $q_H$，在合同 A 中可行当且仅当在合同 B 中可行，也当且仅当

$$
H\le8M.
\tag{TM.3203}
$$

这是对指定标签函数 $\sigma_M$ 的分类，不是对任意 $M$ 值标签函数的分类。

证明。先设 $H\le8M$，保持定义 31.2 的执行不变。定理 31.3 给初始标签 $j$、初始窗口 $E_0,\ldots,E_j$ 和 $n=\lambda_j$。$j=0$ 时直接输出 $(0,E_0,n)$。

若 $j\ge1$，用[原子卷引理 357.2、定理 357.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的整数子环字符，记为 $\vartheta$。它作用于继承的子环

$$
\mathcal O=\mathbb Z\cdot1\oplus\mathbb Z\cdot A
           \oplus\mathbb Z\cdot B\oplus\mathbb Z\cdot AB,
\qquad
\vartheta(s+tA+uB+vAB)=[s+t+3u+3v]_5.
\tag{TM.3204}
$$

实际 $E_1=E(\rho t)$ 属于 $\mathcal O$，且 $\rho t$ 的 $\beta$ 叶数为 $m$，所以 $\vartheta(E_1)=3^m$。$3$ 在 $\mathbb F_5^\times$ 中阶为四，由此唯一确定 $r=m\bmod4$ 的标准代表 $0\le r\le3$。写 $m=4\lfloor m/4\rfloor+r$，与已供应标签组合得到

$$
m\equiv4\sigma_M(t)+r\pmod{4M}.
\tag{TM.3205}
$$

字符只在整数子环上使用；它不是任意实 Clifford 元素的降模映射。

$j=1$ 时，$n=m+b$ 且 $0\le b\le m$，于是候选初始尺寸满足

$$
\left\lceil\frac n2\right\rceil\le m\le n,
\qquad m+n>H.
\tag{TM.3206}
$$

这个区间的直径为 $\lfloor n/2\rfloor\le n/2\le H/2\le4M$。两个不同候选若有（TM.3205）的同一余数，差至少为 $4M$；因此只有直径恰为 $4M$ 才能出现二候选。全部等号强制 $n=H=8M$，两候选为 $m=4M$ 与 $m=8M$。前者强制 $c=(0,4M)$，后者强制 $c=(8M,0)$；所有实现前者的树只有 $\beta$ 叶，所有实现后者的树只有 $\alpha$ 叶。因此保存的下一窗分别为

$$
E_1=S^{4M},\qquad E_1=B^{8M}=1,
\qquad S=BA.
\tag{TM.3207}
$$

引理 28.1 的唯一正规形给 $S^{4M}\ne1$。已有的 $E_1$ 区分这两个端点，不需要新动作。其余情形由（TM.3205）—（TM.3206）唯一确定 $m$。

$j=2$ 时，$n=2m+b$，所以

$$
\left\lceil\frac n3\right\rceil\le m\le
\left\lfloor\frac n2\right\rfloor.
\tag{TM.3208}
$$

直径至多 $n/6\le H/6\le8M/6<4M$，故（TM.3205）在该区间至多有一个候选。实际输入供应一个候选，所以恰有一个。

两种非零标签都用

$$
b=n-jm,\qquad a=(j+1)m-n
\tag{TM.3209}
$$

恢复初始组成，再配上已保存的初始窗口。$j=1$ 输出 $(1,(a,b),E_0,E_1)$；$j=2$ 将三窗按引理 28.1 转为唯一正规坐标，与 $(a,b)$ 配成 §29 的 $\eta$，输出 $(2,\eta)$。整除性、非负性和窗口的共同实际实现由输入保证，解码只作用于实际记录像；这里不供应任意环境元组的原树实现判定。定义 31.2 已逐点有限停止，故合同 B 可行；合同 A 也可忽略侧信息选择动作，最后使用同一解码。

反之，设 $H\ge8M+1$，令 $R=H-8M-1\ge0$。给以下非空叶词各取从左至右左结合的固定括号原树：

$$
X=\beta^{2M}\alpha\beta^{2M}\alpha^R,
\qquad Y=\alpha^H,
\qquad Z=\alpha\beta^{4M}\alpha^R.
\tag{TM.3210}
$$

零次叶块仅省略，$X,Z$ 都保留至少一片 $\alpha$，不引入空来源或空上下文。计数组成得到

$$
\begin{aligned}
c(X)=c(Z)&=(H-8M,4M),&m(X)=m(Z)&=H-4M,\\
c(Y)&=(H,0),&m(Y)&=H.
\end{aligned}
\tag{TM.3211}
$$

三者都满足 $\lambda_1=H$ 和 $\lambda_2>H$，所以初始标签均为一；$X,Z$ 的 $\lambda_2=2H-4M$，$Y$ 的 $\lambda_2=2H$。初始尺寸相差 $4M$，故三者的 $\sigma_M$ 相同。

由 $B^2=-1$、$A^2=1$，并用 $H-(R+1)=8M$，有

$$
E_0(X)=E_0(Y)=E_0(Z)=A^H.
\tag{TM.3212}
$$

具体地，$B^{2M}AB^{2M}=A$ 且 $B^{4M}=1$。下一窗的原子贡献是 $\alpha\mapsto B$、$\beta\mapsto S$。引理 28.1 的换位式给

$$
S^{2M}BS^{2M}
=S^{2M+1}AS^{2M}
=S^{2M+1}S^{-2M}A=B,
\tag{TM.3213}
$$

其中 $(-1)^{2M}=1$。因此

$$
E_1(X)=E_1(Y)=B^H,
\qquad E_1(Z)=BS^{4M}B^R\ne B^H.
\tag{TM.3214}
$$

若最后两个值相等，左乘 $B^{-1}$、右乘 $B^{-R}$ 就得到 $S^{4M}=B^{H-1-R}=B^{8M}=1$，违背正规形唯一性。故 $X,Y$ 的初始 $q_H$ 因组成不同而不同，$X,Z$ 的初始 $q_H$ 因下一窗不同而不同。

考虑一个在合同 A 中正确的共同程序。相同标签给三者相同初始化。只读 $E$ 总返回共同 $A^H$；拼接任意已知实际非空上下文 $v$，若 $d_0(v)>4M$，左右两种拼接在三者上都拒绝且不改变来源。所有只由这些动作组成的共同前缀具有相同完整记录，包括上下文身份、拒绝和已取得读数，且不返回被拒绝候选的窗口。程序不能在该前缀停止，因为初始目标不同；逐点有限停止又排除永远只执行这些动作。因此存在第一条其余动作，只能是 $\rho$，或某侧拼接 $1\le d_0(v)\le4M$ 的实际上下文。

若首动作为 $\rho$，三者都接受，$X,Y$ 的当前叶数同为 $H$，再替换都超限，当前 $E$ 同为 $B^H$。于是

$$
q_H(\rho X)=q_H(\rho Y)=(0,B^H,H).
\tag{TM.3215}
$$

这对来源的接受记录及任何随后请求的当前 $E$ 也相同。

若首动作为拼接 $v$，则 $X,Z$ 都接受而 $Y$ 拒绝。$X,Z$ 的新叶数同为 $H-4M+d_0(v)$，新一次替换叶数同为 $H+d_1(v)>H$，因为非空正上下文满足 $d_1(v)>0$。故这对来源都落入标签零，当前边界同为

$$
\begin{cases}
(0,A^Hh_0(v),H-4M+d_0(v)),&\text{右拼接},\\
(0,h_0(v)A^H,H-4M+d_0(v)),&\text{左拼接}.
\end{cases}
\tag{TM.3216}
$$

乘法次序分别保留，未要求上下文与来源交换；完整记录仍相同，包括接受及可选后继读取。这里 $d_i,h_i$ 沿用（TM.3002）的实际上下文参数。

无论哪种首动作，都使一对不同初始目标拥有相同标签、相同完整记录和相同当前 $q_H$。按定义 32.1 所复用的定理 30.2，以后共同确定程序的所有动作、响应及输出相同，不能同时正确。任意大的档案也只保存这份共同记录。合同 A 因而不可行；合同 B 是合同 A 的受限情形，也不可行。$\square$

### 32.3 固定执行记录后的精确补充容量

**定理 32.4（合同 B 的最小标签数）。** 令

$$
K=\left\lceil\frac H8\right\rceil
 =\left\lfloor\frac{H-1}{8}\right\rfloor+1.
\tag{TM.3217}
$$

则在整个实际家族 $\mathcal T_H$ 上

$$
M_B(H)=K.
\tag{TM.3218}
$$

仅依初始尺寸的 $\sigma_K$ 达到该值。等长二进制补充的精确最少位数为 $\lceil\log_2K\rceil$，$K=1$ 时为零；这是补充字母表容量，不是取得器的总记忆最优值。

证明。因 $H\le8K$，定理 32.3 已用不变的执行器和 $\sigma_K$ 给出 $K$ 值上界。

对下界，对每个 $k=0,\ldots,K-1$ 取固定左结合的实际叶词

$$
T_k=\beta^{2k}\alpha\beta^{2k}\alpha^{H-8k-1}.
\tag{TM.3219}
$$

由 $8(K-1)\le H-1$，尾部指数非负；零次块省略后仍有中间 $\alpha$。其组成和替换叶数为

$$
c(T_k)=(H-8k,4k),\quad m(T_k)=H-4k,\quad
\lambda_1(T_k)=H,\quad\lambda_2(T_k)=2H-4k>H.
\tag{TM.3220}
$$

这里 $4k<H$，最后不等式严格成立。与（TM.3212）—（TM.3213）相同的叶积计算，包含 $k=0$，给

$$
E_0(T_k)=A^H,\qquad E_1(T_k)=B^H.
\tag{TM.3221}
$$

定义 31.2 因而在每个 $T_k$ 上返回完全相同的

$$
\Gamma_H(T_k)=(1,A^H,B^H,H),
\tag{TM.3222}
$$

且其完整执行记录相同。$K$ 个初始目标 $(1,(H-8k,4k),A^H,B^H)$ 则两两不同。任何解码补充都须给它们两两不同的标签，所以字母表至少含 $K$ 个值。这个实际共同记录家族使上、下界相等。

$\sigma_K(T_k)=\bigl(\lfloor H/4\rfloor-k\bigr)\bmod K$，故这 $K$ 个实际来源也取得全部 $K$ 个标签。最后按定义 32.2 所复用的固定宽度二进制容量关系，$b$ 位可行恰在 $2^b\ge K$，从而得到所述位数。$\square$

### 32.4 执行前任意标签的矩形下界

**引理 32.5（实际组成与下一窗的矩形家族）。** 令 $K$ 如（TM.3217），取 $1\le C\le K$，并置 $R=K-C+1$。以行 $k=C-1,\ldots,K-1$ 和列 $r=0,\ldots,C-1$ 定义固定左结合的原树

$$
T_{k,r}=\beta^{2(k+r)}\alpha\beta^{2(k-r)}
        \alpha^{H-8k-1}.
\tag{TM.3223}
$$

这 $RC$ 个树都实际属于 $\mathcal T_H$，初始标签均为一，且

$$
\begin{aligned}
c(T_{k,r})&=(H-8k,4k),\qquad m(T_{k,r})=H-4k,\\
\lambda_1(T_{k,r})&=H,\qquad\lambda_2(T_{k,r})=2H-4k>H,\\
E_0(T_{k,r})&=A^H,\qquad
E_1(T_{k,r})=S^{4r}B^H.
\end{aligned}
\tag{TM.3224}
$$

其 $RC$ 个初始 $q_H$ 两两不同。

证明。$k\ge C-1\ge r$ 使全部 $\beta$ 指数非负；$k\le K-1$ 使尾部指数非负。省略零次块后保留一片中间 $\alpha$，所以是非空实际树。组成只依行，计数给（TM.3224）的前三个尺寸公式，$4k<H$ 给标签一。

记尾部指数为 $L_k=H-8k-1$。初始叶积中的两侧 $B$ 块分别是 $(-1)^{k+r}$ 与 $(-1)^{k-r}$，其积为一，因此初始积为 $A^{L_k+1}=A^H$。下一窗为

$$
\begin{aligned}
S^{2(k+r)}BS^{2(k-r)}B^{L_k}
 &=S^{2(k+r)+1}AS^{2(k-r)}B^{L_k}\\
 &=S^{4r+1}AB^{L_k}
 =S^{4r}B^{L_k+1}
 =S^{4r}B^H.
\end{aligned}
\tag{TM.3225}
$$

第二步用全整数换位式及偶指数 $2(k-r)$，末步用 $B^{8k}=1$。不同行组成不同；同一行的不同列有不同 $S^{4r}$，由引理 28.1 的正规形唯一性及右消去 $B^H$ 得下一窗不同。故初始目标两两不同。$\square$

**定理 32.6（合同 A 的线性补充下界）。** 对整个 $\mathcal T_H$，执行前任意有限标签的最小容量满足

$$
\left\lceil\frac{\lfloor(K+1)^2/4\rfloor}{K}\right\rceil
 \ \le\ M_A(H)\ \le\ K.
\tag{TM.3226}
$$

此外，$H\ge9$ 时 $M_A(H)\ge2$。因而

$$
\begin{aligned}
M_A(H)&=1 &&(1\le H\le8),\\
M_A(H)&=2 &&(9\le H\le16),\\
M_A(H)&=\Theta(H) &&(H\longrightarrow\infty).
\end{aligned}
\tag{TM.3227}
$$

对于 $H\ge17$，本定理不确定 $M_A(H)$ 的精确值；（TM.3203）只确定 $\sigma_M$ 的阈值。

证明。上界仍用 $\sigma_K$ 和不变的定义 31.2。为证下界，固定引理 32.5 的 $R\times C$ 实际矩形。在一个标签类中，程序初始化相同。称该类中的一个非空子集可识别，若共同确定协议在其每个输入上有限停止并正确输出初始目标。一个正确协议限制到允许输入的子集仍正确；这只是证明中的量词限制，不是来源删除动作。

先考虑一个可识别子集 $U$，其中初始尺寸最小的行包含至少两列。记该行索引为 $k_*$；它是 $U$ 中最大的 $k$，行内两个来源有相同初始尺寸 $H-4k_*$、相同 $E_0=A^H$ 和不同初始下一窗。

所有只读及在 $U$ 中处处拒绝的拼接都给共同、不变的记录前缀。若在首次 $\rho$ 前第一次出现一个在 $U$ 中某处接受的拼接 $v$，则

$$
H-4k+d_0(v)\le H
\quad\Longrightarrow\quad
H-4k_*+d_0(v)\le H
\tag{TM.3228}
$$

因为 $k_*\ge k$。故该拼接被最小尺寸行的全部来源接受。其新第一替换叶数为 $H+d_1(v)>H$，所以行内这两个来源都落标签零，当前尺寸相同。右拼接给共同当前 $E=A^Hh_0(v)$，左拼接给共同当前 $E=h_0(v)A^H$；无论哪侧，上下文都是同一个已知实际正上下文。其完整此前记录、本次接受及可选后继 $E$ 相同，而初始下一窗不同。定理 30.2 排除后续正确恢复。因此正确协议在首次 $\rho$ 前不能作任何在 $U$ 中被接受的拼接。

$U$ 至少有两个不同初始目标，程序不能在此前的共同前缀上停止；逐点有限停止也排除无限只读或处处拒绝的拼接。故必须出现共同的首次 $\rho$。它在 $U$ 全部来源上接受，之后每个来源的当前尺寸都是 $H$，标签都为零，当前 $E$ 为 $S^{4r}B^H$，仅依列 $r$。若 $U$ 的同一列含不同行的两个来源，它们在这个时刻合并为相同当前 $q_H$，拥有相同完整记录和不同初始组成，仍由定理 30.2 排除正确恢复。因此这种 $U$ 每列至多一格，得到 $|U|\le C$。相同标签、完整记录和共同初始化是两种合并的共同前提；档案大小没有出现在排除理由中。

现在对矩形内任意一个正确标签类 $V$ 估计大小。若其最小尺寸行仅有一格，就在证明中删去该单格行，再将原协议限制到剩余子集；反复进行。每次删去整个当前最小尺寸行，至多删一次每行。若全部行都以单格删完，则 $|V|\le R\le K$。否则剩下某个可识别子集，其最小尺寸行至少两格；此前最多删去 $R-1$ 个单格，而刚证明的结论使剩余子集至多 $C$ 格。因此

$$
|V|\le(R-1)+C=K.
\tag{TM.3229}
$$

空类、单格类同样满足此界；$C=1$ 时全部非空行只有一格，直接属于删完的情况。这个限制论证没有断言任意正确标签类一开始就不能重复行或列。

矩形共有 $RC$ 个不同初始目标，每个标签类最多 $K$ 格，所以任何正确补充需至少 $\lceil RC/K\rceil$ 个标签。对 $1\le C\le K$ 取最大乘积，得

$$
\max_C RC=\max_C C(K-C+1)
 =\left\lfloor\frac{(K+1)^2}{4}\right\rfloor,
\tag{TM.3230}
$$

从而得到（TM.3226）。对 $H\ge9$，只有一个标签意味着所有来源共同初始化且无变化补充，定理 31.4 已排除，故还须 $M_A(H)\ge2$。$H\le8$ 时上界 $K=1$，而 $9\le H\le16$ 时 $K=2$，得两段精确值。

最后，$\lfloor(K+1)^2/4\rfloor\ge K^2/4$，因为奇数 $K$ 时左侧为 $(K+1)^2/4$，偶数 $K$ 时为 $(K^2+2K)/4$。因此

$$
\frac H{32}\le\frac K4\le M_A(H)\le K
 \le\frac H8+1.
\tag{TM.3231}
$$

这证明线性阶数，同时不消除两界之间的精确容量缺口。$\square$

### 32.5 同一公开实际子家族中的操作次序分离

**定理 32.7（先填充与固定窗执行的容量分离）。** 对公开共同承诺的实际家族

$$
\mathcal F_H=\{T_k:0\le k<K\},
\tag{TM.3232}
$$

其中 $T_k$ 取自（TM.3219），合同 B 仍需恰 $K$ 个补充标签；合同 A 则用一个标签、没有随来源变化的补充即可识别全部初始 $q_H$。$H\ge9$ 时分离严格，且两容量之比随 $H$ 无界。

证明。固定执行器在全部 $T_k$ 上给共同（TM.3222）及共同完整记录，而 $K$ 个初始目标不同，故合同 B 至少需 $K$ 个标签；定理 32.4 的 $\sigma_K$ 给上界。

合同 A 对该公开家族使用同一个程序：不先替换或读取窗口，直接在初始来源右侧反复拼接已知单叶 $\alpha$，到首次拒绝为止；令成功次数为 $s$。初始尺寸为 $H-4k$，守卫和拒绝语义给

$$
s=H-(H-4k)=4k,
\qquad k=s/4.
\tag{TM.3233}
$$

因此共同输出函数返回初始边界

$$
(1,(H-8k,4k),A^H,B^H).
\tag{TM.3234}
$$

这里组成及两个窗口来自同一个公开家族承诺和已证明的（TM.3220）—（TM.3221），不是从未调用的 $E$ 端口取得。来源调用恰为 $s+1$ 次，包含最后拒绝；没有 $\rho$、复位或复制。所有输入有限停止，故一个不变化的标签足够，非空家族又至少需要一个标签。

当 $H\ge9$ 时 $K\ge2$，容量分别为 $K$ 与一；$K=\lceil H/8\rceil$ 无界。这个公开家族限制独立于全 $\mathcal T_H$ 合同，不给出 $M_A(H)=1$；全家族仍受定理 32.6 限制。$\square$

### 32.6 补充容量、取得控制与恢复对象

**定理 32.8（不变取得器的费用范围）。** 在整个 $\mathcal T_H$ 上，取 $K=\lceil H/8\rceil$，供应初始 $\sigma_K$ 并保持定义 31.2 的动作规则，得到合同 A 和 B 的识别器。其来源调用仍至多 $H+4$，最优固定执行后补充的等长位数为 $\lceil\log_2K\rceil$。在定理 31.6 的固定、来源无关的紧凑坐标转换接口下，保留该补充字段及原取得控制字段仍只需 $O(\log(H+1))$ 位。对合同 A 任意标签的最优等长补充容量，则由定理 32.6 得

$$
\left\lceil\log_2M_A(H)\right\rceil
 =\log_2H+O(1)\qquad(H\longrightarrow\infty).
\tag{TM.3235}
$$

这些界分别计来源调用、补充输出容量和声明接口下的控制字段；不包含标签生产与同源认证、交付与保留机制、读数转换和表的构造／描述、算术工作区或硬件、展开后的输出与物理时间，也不宣称总费用、调用数或总记忆最优。

证明。来源动作与定义 31.2 完全相同，直接复用定理 31.6 的 $H+4$ 上界；解码由定理 32.3 保证。补充位数来自定理 32.4。原紧凑字段为定理 31.6 的有限相位、至多三个正规窗口坐标及填充计数，大小为 $O(\log(H+1))$；新增字段有 $K\le H$ 个值，可用 $\lceil\log_2K\rceil=O(\log(H+1))$ 位保留，故字段阶数不变。转换接口和表的费用仍独立于这个字段计数。式（TM.3235）则对（TM.3231）的线性上下界取对数，再取整；它不提供一个在全家族上达到未知精确 $M_A(H)$ 的具体最优程序。$\square$

**定义 32.9（初始证据的供给与表示边界）。** 在定义 32.1 中，$h(t)$ 总指运行前同一实际来源的函数值。若先在初始来源上执行填充取得其尺寸，再以所得尺寸计算 $\sigma_M$，此时实际来源已被改变，不能代替“供应标签而保持原初始来源”的前提。公开子家族承诺可使初始目标由这份记录恢复，如定理 32.7，但不使已改变的来源重新等于初始来源。拒绝信息是可见边界，接受动作则改变可达窗口，二者不能当作同一个免费静态尺寸读口。

本节的恢复表示是初始组成与可达的同源 Clifford 窗口，即初始 $q_H$。符号证明依赖本卷 §§28—31 与[原子卷引理 357.2、定理 357.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的实际来源、唯一正规形、字符和守卫更新；八倍阈值、共同记录家族、矩形限制和操作次序分离属于这些前提上的来源特定普通数学推导。静态标签框架只供应一般编码关系。原树括号、叶路径、逆向物理执行、绝对时间与物理空间几何不属于 $q_H$ 的恢复对象；统计编码率也不等同于这个单来源行为合同的容量。

## 32.99 追加锚

## 33. 公共首替换层的同标记取得、实际障碍与三角形容量

本节继续 §32 的原始合同。来源是全部自由有序、非空的 $\alpha/\beta$ 二叉树，初始上限固定为 $H$；允许的来源动作仍只有当前 $E$ 读、$\rho$ 和已知实际非空上下文的左、右拼接。拼接和替换都受原有正的叶数守卫，拒绝保持来源且不返回候选读数；没有复位、复制、逆向导航、变上限或免费的 $n$ 读口。目标是运行前的初始 $q_H$，标签在第一条动作以前由同一初始实际来源供应。标签生产、认证、交付和表的构造不属于本节取得器。

§§28–32 已给出 Clifford 正规形、三窗运输、固定执行记录和同记录合并原理。原子卷 §§359.3–360.2 已给出全部实际三窗联合像的正规形以及固定历史纤维的 Euler 充要判据；以下只在其中取出的实际叶词上作具体切片和取得推导，不把任意满足坐标方程的环境元组当作来源，也不重新声称一般联合像定理。

### 33.1 公共首替换层与行列数据

对 $t\in\mathcal T_H$ 写初始组成 $c(t)=(a,b)$，并置

$$
m(t)=a+b,\qquad n(t)=a+2b,\qquad \lambda _2(t)=2a+3b=2m(t)+b=m(t)+n(t).
$$

记 $E_0(t)=E(t)$、$E_1(t)=E(\rho t)$。本节首先固定一个公开整数 $1\le n\le H$，并限制到一个非空的实际家族 $\mathcal F\subseteq\mathcal T_H$，满足

$$
\lambda _1(t)=n,\qquad \lambda _2(t)=m(t)+n>H \quad(t\in\mathcal F).
\tag{TM.3301}
$$

因此所有成员的初始标签都是 $1$，而第一次替换后的来源都不能再接受第二次替换。由

$$
a=2m-n,\qquad b=n-m
\tag{TM.3302}
$$

可知在固定 $n$ 和固定首读 $E_0=g$ 的纤维中，初始目标由一对 $(m,z)$ 唯一确定，其中 $z=E_1$；若多个树代表给出同一对，下面只保留这一对一次。行按 $m$ 递增，列由 $z$ 标记。这个去重只发生在证明中的候选表，不是运行时从来源删除对象。

### 33.2 同标记充要判据与阈值剥离协议

**定理 33.1（公共 $n$ 的同标记判据）。** 在满足（TM.3301）的实际家族上，一个标签可以被所有成员共享并配合一个忠实的确定性取得程序，当且仅当对每个首读纤维 $E_0=g$，下述行检验通过。反复删除当前最小 $m$ 行中的唯一目标；若最终没有行，检验通过。若第一次遇到含至少两个目标的行，则要求剩余目标的列值 $z=E_1$ 在所有剩余行中均不重复。等价地，失败当且仅当存在 $u,v,s,t\in\mathcal F$，使

$$
\begin{gathered}
E_0(u)=E_0(v)=E_0(s)=E_0(t),\\
m(u)=m(v)\le\min\{m(s),m(t)\},\qquad E_1(u)\ne E_1(v),\\
m(s)\ne m(t),\qquad E_1(s)=E_1(t).
\end{gathered}
\tag{TM.3303}
$$

允许这些名字在证书中重合，所以证书实际含三或四个不同目标。若标签函数为 $h$，则同一结论逐个作用于每个 $(h,E_0)$ 纤维，失败证书还须满足 $h(u)=h(v)=h(s)=h(t)$；程序可以先按 $h$ 和初始 $E_0$ 查公开候选表，再执行同一协议。公开的 $n$ 是整个家族的承诺，不是另加的来源端口。

**证明。** 先证必要性。固定一个 $(h,E_0)$ 纤维，记共同首读为 $g$。若行检验失败，先在证明中剥去首个多目标最小行以前的单目标行，再把任意正确协议限制到从该多目标行起的剩余候选集。该集的最小 $m$ 行含至少两个不同目标，且有两个不同行共享同一列。限制只改变证明中的量词，不改变来源合同，也不要求协议实际执行这些剥离。以下合并论证均在这个剩余候选集上进行。设在第一次 $\rho$ 以前已经发生了一段公共记录前缀，其中所有被接受的拼接都使用同一个已知上下文序列。令它们在当前零阶和一阶替换窗口上累计增加的叶数为 $D_0,D_1$。对每个实际非空正上下文 $v$，写其对应增加量为 $d_0(v),d_1(v)$；由组成运输有

$$
1\le d_0(v)\le d_1(v).
\tag{TM.3304}
$$

在这段公共前缀中，当前两层尺寸分别为 $m+D_0$ 和 $n+D_1$，当前 $E_0=L_0gR_0$、当前 $E_1=L_1zR_1$，其中 $L_0,R_0,L_1,R_1$ 都是由同一已知上下文序列确定的共同可逆因子。因此 $E_1$ 的相等与不等不会因这些因子而改变；被拒绝的拼接既不改来源也不改这些关系。

考虑公共前缀之后的下一次拼接 $v$，允许此前已有安全的处处接受拼接。如果

$$
n+D_1+d_1(v)\le H,
\tag{TM.3305}
$$

则由 $m+D_0\le n+D_1$ 和（TM.3304），它在整个候选集上都接受，记录不含行或列区别，只消耗有限容量。如果（TM.3305）失败，而拼接在某处接受，则它必在最小 $m$ 行的全部成员上接受。接受以后下一次替换窗口已经超过 $H$，所以该行中的不同 $z$ 都落入标签 $0$；它们有相同的当前尺寸、相同的当前 $E_0$（右拼接为 $L_0gR_0h_0(v)$，左拼接为 $h_0(v)L_0gR_0$，其中 $h_0(v)=E(v)$）和相同的完整记录。定理 30.2 的同记录合并原理于是排除正确恢复。故在第一次 $\rho$ 以前，正确协议只能作处处接受且仍满足（TM.3305）的公共拼接、处处拒绝的公共拼接和公共读动作。

处处接受的拼接每次使 $D_1$ 至少增加一，且（TM.3305）给出有限次数上界；公共前缀不能以同一输出正确恢复所有不同初始目标，无限公共只读或处处拒绝的前缀又不能满足逐点有限停止。因此协议必须最终执行一次共同的 $\rho$。这次替换在全部候选上接受，当前尺寸相同，当前标签变为 $0$，当前读数是共同可逆因子包围的 $z$。若剩余行中有两个不同行共享同一列 $z$，它们在相同完整记录和相同当前 $q_H$ 下合并，仍被定理 30.2 排除。于是第一次多目标行之后的剩余部分必须列单射。

若行检验失败且某个重复列在首个多目标行出现，就取该行此列目标和另一不同列目标为 $u,v$，再取此列在该行与后行的两个目标为 $s,t$；其中一个名字重合，得到三目标证书。若该行没有列在后行重现，则任取该行的两个目标为 $u,v$，并取后面两个不同行的同列目标为 $s,t$，得到四目标证书，且这个重复列不同于首行选出的两列。反之，将协议限制到任一（TM.3303）证书的三或四目标子集，其最小行含两个不同列，且余下部分含跨行重复列，刚才的合并论证直接否定正确协议。

再证充分性。初始读 $E_0$ 后按标签和首读选择公开候选表。若当前表只剩一个目标，立即输出它。若最小 $m$ 行是唯一目标且还有别的行，右侧拼接固定左结合的实际词 $\alpha^{H-m}$。该上下文非空；它在该行恰好接受，在所有更大 $m$ 行拒绝。接受时立即输出该行的唯一目标；拒绝时来源未变，只在控制器表中剥离该行，继续下一行。到达首个多目标行时，行检验保证余下列值全局单射。此时执行 $\rho$ 并读取 $E$；此前所有拼接都已拒绝，所以来源仍是初始来源，读到的正是唯一的初始 $E_1=z$，由它查回 $(m,z)$，再用（TM.3302）输出初始组成及初始 $q_H$。每一步或者剥离一行或者停止，因而有限停止。若该纤维有 $R$ 个占用行，初始读一次、至多 $R-1$ 次剥离拼接，末端至多一次 $\rho$ 加一次读，来源调用数不超过

$$
R+2.
\tag{TM.3306}
$$

这包含初始 $E_0$ 读；上下文的公开产生和表描述另计。证毕。

### 33.3 三、四目标障碍与实际四元见证

**推论 33.2（最小障碍的三、四目标形式）。** 在固定 $n,E_0$ 纤维中，定理 33.1 失败恰由下列两种配置之一见证：

$$
\{(m,x),(m,y),(m',x)\},\qquad m<m',\ x\ne y,
\tag{TM.3307}
$$

或

$$
\{(m,x),(m,y),(m',z),(m'',z)\},\qquad m<m'<m'',\ x,y,z\text{ 两两不同}.
\tag{TM.3308}
$$

第一种需要三个目标，第二种需要四个目标；每种配置的任意扩张仍不可同标记取得。

证明。取检验中第一次留下的多目标行。若某个跨行重复列已经在该行出现，取该行的此列目标与另一个不同列目标，再取后面同列目标，组成（TM.3307）；否则选该行的两个不同列，并选后面两个不同行的同列目标，按行指标递增排列得到（TM.3308），该重复列与首行两列均不同。反向蕴含正是定理 33.1 的必要性证明。扩张不可能比其公开子集更易取得。证毕。

**定理 33.3（$H\ge17$ 的实际四源最小见证）。** 对每个 $H\ge17$，令

$$
\begin{aligned}
U&=\alpha^H,&\quad V&=\beta^2\alpha\beta^2\alpha^{H-9},\\
W&=\beta^6\alpha\beta^2\alpha^{H-17},&\quad Z&=\beta^8\alpha\alpha^{H-17},
\end{aligned}
\tag{TM.3309}
$$

均取固定左结合括号，零次块省略。它们都是原合同中的实际来源，且

$$
\begin{array}{c|c|c|c|c}
\text{来源}&c(t)&m& E_0&E_1\\ \hline
U&(H,0)&H&A^H&B^H\\
V&(H-8,4)&H-4&A^H&B^H\\
W&(H-16,8)&H-8&A^H&S^4B^H\\
Z&(H-16,8)&H-8&A^H&S^8B^H
\end{array}
\tag{TM.3310}
$$

并且 $\lambda _1=H$、$\lambda _2>H$。四源家族不能共享一个标签，而每个三源子家族都可共享一个标签；故三目标检验不足，即使在这些实际来源上也需要四目标证书。

**证明。** 这些词分别是 §32.4–§32.5 的实际正词：$U,V$ 是 $k=0,1$ 的两行，$W,Z$ 是 $k=2$ 的 $r=1,2$ 两列。直接用 $B^2=-1$、$B=SA$、$ASA=-S^{-1}$ 得（TM.3310）；例如 $E_1(W)=S^6BS^2B^{H-17}=S^4B^H$，而 $E_1(Z)=S^8B^H$。按 $U,V,W,Z$ 排列的四个 $m$ 值为 $H,H-4,H-8,H-8$，占用行分别是 $W,Z$ 的最小行、$V$ 的中间行和 $U$ 的最大行；$S$ 的无限阶以及正规形唯一性保证四列值中 $B^H,S^4B^H,S^8B^H$ 彼此不同。四源集合满足（TM.3308），所以定理 33.1 否定一个标签。

$\{W,Z,U\}$ 与 $\{W,Z,V\}$ 的余下三列全不同，先执行 $\rho$ 再读即可。$\{U,V,W\}$ 与 $\{U,V,Z\}$ 先右接 $\alpha^8$：只在最小行接受并立即确定 $W$ 或 $Z$；在余下的 $U,V$ 上右接 $\alpha^4$，接受确定 $V$，拒绝确定 $U$。拒绝不读取候选 $E$，所以这些程序仍保持原合同。四源家族的容量因而恰为二：给 $Z$ 一个标签，给 $\{U,V,W\}$ 另一个标签，在后一纤维运行三源程序，在前一纤维直接输出公开的 $Z$ 目标。这个结论把标签函数当作已供应的数学输入，并不实现其生产或认证。证毕。

### 33.4 两个饱和首窗切片的完整实际像

**定理 33.4（$E_0=\pm A^H$ 饱和切片的完整分类）。** 令 $\delta\in\{0,2\}$，考虑所有满足 $\lambda _1=H$ 且

$$
E_0=(-1)^{\delta/2}A^H
\tag{TM.3311}
$$

的实际来源。它们的组成必为

$$
b=4k+\delta,\qquad a=H-8k-2\delta\ge0.
\tag{TM.3312}
$$

当 $a>0$ 时，所有可能的下一窗恰为

$$
E_1=S^xB^H,\qquad x\in\{-b,-b+4,\ldots,b-4,b\}.
\tag{TM.3313}
$$

当 $a=0$ 时，唯一的实际叶词是纯 $\beta^b$，只有端点 $x=b$ 出现。这里的“完整”只针对所声明的两个实际首窗切片；一般三窗联合像仍由原子卷定理 359.3 和定理 360.2 描述。

**证明。** 先取任一实际叶词，并用 §28 的正规形写 $E_0=(-1)^eS^{k_0}A^p$。由（TM.3311）及正规形唯一性，$k_0=0$。§29.5 的相位关系在首坐标给出

$$
2e+k_0\equiv b\pmod4.
\tag{TM.3314}
$$

而（TM.3311）中的符号使 $e\equiv\delta/2\pmod2$，故 $b\equiv\delta\pmod4$。再由 $\lambda _1=a+2b=H$ 得（TM.3312）。

设原叶词为 $x_1\cdots x_m$，并令 $q_i=1$ 当 $x_i=\beta$、否则 $q_i=0$。逐叶应用（28.3）可得首坐标的指数和符号为

$$
 k_0=\sum_{i=1}^m(-1)^{i-1}q_i,
 \qquad
 e\equiv\sum_{\substack{i\text{ 为偶数}\\x_i=\beta}}1\pmod2.
\tag{TM.3315}
$$

因此 $k_0=0$ 恰使奇位置与偶位置的 $\beta$ 数相等，特别是 $b$ 为偶数且 $e\equiv b/2\pmod2$；这与 $e\equiv\delta/2$ 再次给出 $b\equiv\delta\pmod4$。为计算下一窗，对每个原叶位置令

$$
\varepsilon_i=(-1)^{\#\{j<i:x_j=\alpha\}},\qquad
D=\sum_{i=1}^m\varepsilon_i,\qquad
q=\#\{i:\varepsilon_i=-1\}.
$$

在 $\rho$ 后，$\alpha$ 块是 $B=SA$，$\beta$ 块是 $BA=S$。故逐块应用（28.3）给出

$$
E_1=(-1)^qS^D A^{a\bmod2}.
$$

$k_0=0$ 还控制了 $\beta$ 位置上的符号。若按 $\beta$ 从左到右编号为 $j$，则
$k_0=\sum_j(-1)^{j-1}\varepsilon_{\beta_j}=0$；因而奇、偶编号的
$\varepsilon_{\beta_j}$ 和相等。每一组有 $b/2$ 项，所以这个共同和与
$b/2$ 同余，从而 $\sum_{\beta}\varepsilon_i\equiv b\pmod4$，即
$\#\{\beta:\varepsilon_i=-1\}$ 为偶数。$\alpha$ 位置上负号的数目恰为
$\lfloor a/2\rfloor$，故 $q\equiv\lfloor a/2\rfloor\pmod2$。此外，所有
$\alpha$ 位置的 $\varepsilon_i$ 之和为 $a\bmod2$，所以

$$
D-(a\bmod2)=\sum_{\beta}\varepsilon_i\in\{-b,-b+4,\ldots,b-4,b\}.
\tag{TM.3316}
$$

把 $B^H=(-1)^{\lfloor H/2\rfloor}S^{a\bmod2}A^{a\bmod2}$ 代入，并用 $H=a+2b$、$b$ 为偶数及 $q\equiv\lfloor a/2\rfloor$，得到

$$
E_1=S^{D-(a\bmod2)}B^H.
\tag{TM.3317}
$$

这证明了（TM.3313）的必要性；这里的指数是 $D-(a\bmod2)$，而不是未调整的 $D$。

反过来，若 $a>0$，对每个 $0\le j\le 2k+\delta/2$ 取实际固定括号词

$$
W^\delta_{k,j}=\beta^{2j}\alpha\beta^{4k+\delta-2j}\alpha^{a-1}.
\tag{TM.3318}
$$

它保留中间 $\alpha$，是非空实际树，组成正是（TM.3312），并由同一逐叶计算给出

$$
E_1(W^\delta_{k,j})=S^{\,4j-4k-\delta}B^H.
\tag{TM.3319}
$$

当 $j$ 遍历上述区间时，指数正好遍历（TM.3313）。若 $a=0$，没有 $\alpha$ 叶，实际叶词只能是 $\beta^b$，直接得到端点 $x=b$；它确实满足首窗符号，因为 $B^{4k}=1$、$B^{4k+2}=-1$。故分类和实际实现均成立。

令

$$
K=\left\lceil\frac H8\right\rceil,\qquad N=\left\lfloor\frac{H+3}{8}\right\rfloor.
\tag{TM.3320}
$$

$\delta=0$ 的正 $\alpha$ 行为 $k=0,\ldots,K-1$，宽度为 $1,3,\ldots,2K-1$，共有 $K^2$ 个不同目标；$\delta=2$ 的正 $\alpha$ 行为 $k=0,\ldots,N-1$，宽度为 $2,4,\ldots,2N$，共有 $N(N+1)$ 个不同目标。若 $a=0$ 的端点存在，它是另一个单目标最小行，而不是一整行。证毕。

### 33.5 全家族的列高下界与新的精确区间

**定理 33.5（实际切片给出的全 $H$ 下界）。** 设 $\ell$ 是全家族合同 A 的可用标签数。则由定理 33.4 的两个实际切片分别得到

$$
(K-\ell)_+^2\le \ell(2K-1)-K^2,
\tag{TM.3321}
$$

以及（$N=0$ 时视为无约束）

$$
(N-\ell)_+\bigl((N-\ell)_++1\bigr)\le 2N\ell-N(N+1).
\tag{TM.3322}
$$

因此

$$
M_A(H)\ge\max\left\{
\left\lceil\frac{4K-1-\sqrt{8K^2-8K+1}}2\right\rceil,
\left\lceil\frac{4N+1-\sqrt{8N^2+1}}2\right\rceil
\right\},
\tag{TM.3323}
$$

其中第二项在 $N=0$ 时略去；§32 的尺寸标签仍给 $M_A(H)\le K$。特别地

$$
\liminf_{H\to\infty}\frac{M_A(H)}H\ge\frac{2-\sqrt2}{8},
\tag{TM.3324}
$$

但这些切片不决定一般全家族的精确最优值。

**证明。** 先看任一标签类在 $\delta=0$ 或 $\delta=2$ 三角行族中的形状，只考虑 $L\ge1$ 的切片。设行指标为 $k=0,\ldots,L-1$，行宽分别为 $2k+1$ 或 $2k+2$；$k$ 越大，当前初始尺寸 $H-4k-\delta$ 越小。置 $W=2L-1$ 或 $2L$。若该类有多目标行，令 $t$ 为其最大行指标，并置 $d=L-1-t$，称 $k\le t$ 的部分为核心、$k>t$ 的部分为剥离部分。若该类非空但每行至多一个目标，则明确取 $t=0,d=L-1$，核心仅取第 $0$ 行中的目标，剥离部分取 $k>0$ 的目标。若该类为空，则取 $d=0$，核心和剥离部分均为空。

对非空类，剥离部分在至多 $d$ 行中每行至多有一个目标。多目标类的核心由定理 33.1 列单射，而全单目标类的核心至多一个目标，同样列单射；核心的列均属于第 $t$ 行的列集，故大小至多为该行宽 $W-2d$。因此所有类（包括空类及 $L=1$ 的类）的大小均至多

$$
d+(W-2d)=W-d.
\tag{TM.3325}
$$

对每个类按上述约定定义 $d_i$、核心和剥离部分。若有 $\ell$ 个类，总剥离目标数至多为 $\sum d_i$，而把（TM.3325）对所有类求和给出

$$
\sum d_i\le \ell W-\text{(切片总目标数)}.
\tag{TM.3326}
$$

另一方面，一个在切片中出现 $h$ 次的列，至多有 $\ell$ 个未剥离副本，因为每个未剥离类内部列单射；所以至少有 $(h-\ell)_+$ 个副本必须剥离。

在 $\delta=0$ 切片中，列高为 $K$ 一次、$1,2,\ldots,K-1$ 各两次，所需剥离总数为

$$
(K-\ell)_+ +2\sum_{h=\ell+1}^{K-1}(h-\ell)=(K-\ell)_+^2.
\tag{TM.3327}
$$

代入 $W=2K-1$ 和总数 $K^2$ 得（TM.3321）。在 $\delta=2$ 切片中每个高 $1,\ldots,N$ 出现两次，所需总数为

$$
2\sum_{h=\ell+1}^{N}(h-\ell)
=(N-\ell)_+\bigl((N-\ell)_++1\bigr),
\tag{TM.3328}
$$

代入 $W=2N$ 和总数 $N(N+1)$ 得（TM.3322）。对（TM.3321），若 $\ell\ge K$，因（TM.3323）中的第一较小根不超过 $K$，所需下界已成立；仅在 $\ell<K$ 时展开正部，得到 $\ell^2-(4K-1)\ell+2K^2\le0$，从而 $\ell$ 至少为其较小根。对（TM.3322），$N=0$ 时略去；$N\ge1$ 且 $\ell\ge N$ 时，第二较小根不超过 $N$，下界同样已成立；仅在 $\ell<N$ 时展开，得到 $\ell^2-(4N+1)\ell+2N(N+1)\le0$。两个较小根分别为（TM.3323）所列实数，取整数上整即得该式。由于 $K/H\to1/8$，第一项的主系数是 $2-\sqrt2$，得到（TM.3324）。端点单行只增加一个实际目标，不会削弱这些下界。证毕。

**定理 33.6（$21\le H\le24$ 的全家族精确容量）。** 对每个整数 $21\le H\le24$，有

$$
M_A(H)=3.
\tag{TM.3329}
$$

**证明。** 此时 $K=N=3$。$\delta=2$ 切片由三行宽度 $2,4,6$ 构成，共十二个实际目标。列 $S^2B^H$ 在三行各出现一次。若两个标签足够，则每个标签类必须达到定理 33.5 中的最大六个目标；（TM.3325）的等号迫使每个类的全部目标列单射。三次出现的同一列不可能分配到两个列单射类中，故两个标签不够；这也等价于（TM.3322）在 $\ell=2$ 时要求 $2\le0$。

另一方面，§32.3 的公开标签

$$
h(t)=\left\lfloor\frac{m(t)}4\right\rfloor\bmod3
\tag{TM.3330}
$$

在 $H\le24$ 的全 $\mathcal T_H$ 上已有确定性取得和解码程序，并保持原合同的来源调用界。因此三标签足够，和下界合起来得到（TM.3329）。这里的上界复用全家族结果；切片只负责不可行性，不能把子家族程序误报为全家族程序。

### 33.6 正三角实际子家族的精确操作容量

对 $K=\lceil H/8\rceil$，取引理 32.5（TM.3223）的实际词，并让指标遍历正三角区域

$$
T_{k,r}=\beta^{2(k+r)}\alpha\beta^{2(k-r)}
\alpha^{H-8k-1},\qquad 0\le r\le k<K,
\tag{TM.3331}
$$

并令 $\mathcal P_H$ 为这些实际来源的家族。它有 $K(K+1)/2$ 个不同初始目标，且

$$
\begin{aligned}
c(T_{k,r})&=(H-8k,4k),&
E_0(T_{k,r})&=A^H,&
E_1(T_{k,r})&=S^{4r}B^H,\\
\lambda _1(T_{k,r})&=H,&
\lambda _2(T_{k,r})&>H.
\end{aligned}
\tag{TM.3332}
$$

**定理 33.7（正三角家族的精确容量）。** 在公开限制到 $\mathcal P_H$ 的合同下，执行前标签容量和固定执行后补充容量分别为

$$
M_A(\mathcal P_H)=\left\lceil\frac{K+1}{2}\right\rceil,\qquad
M_B(\mathcal P_H)=K.
\tag{TM.3333}
$$

**证明。** 先证每个同标记类至多含 $K$ 个目标。把行按 $k$ 编号；若某类有最大多目标行 $p$，则 $k>p$ 的 $K-1-p$ 行在剥离后每行至多一个目标，而 $k\le p$ 的余下部分因列单射至多含第 $p$ 行的 $p+1$ 个列。因此该类大小至多

$$
(K-1-p)+(p+1)=K.
\tag{TM.3334}
$$

若没有多目标行，界更直接。总目标数为 $K(K+1)/2$，故至少需要 $\lceil(K+1)/2\rceil$ 个标签。

下面构造达到该下界的分割。$K=1$ 时只有一个类。设 $K=2s+1$，并假定 $K-2=2s-1$ 时已有 $s$ 个可行类。对旧类 $j=0,\ldots,s-1$，加入新行中的两个目标

$$
(2s-1,j),\qquad (2s,s+j).
\tag{TM.3335}
$$

它们位于旧类当前多目标行之上，依次是可剥离的单目标行，不破坏列单射。再取一个新类：在行 $2s-1$ 取列 $s,\ldots,2s-1$，在行 $2s$ 取列 $0,\ldots,s-1$ 以及列 $2s$。这个类共有 $2s+1=K$ 个目标，列恰为 $0,\ldots,2s$ 各一次，故通过定理 33.1。新两行被无重叠地覆盖，得到 $s+1$ 类。偶数 $K=2s$ 时，把 $K+1=2s+1$ 的构造限制到行 $k<K$，删去最上行目标；可行性在候选子集下保持，仍有 $s+1=\lceil(K+1)/2\rceil$ 个类。归纳给出上界，和下界相等。

固定执行后的记录在 $r=0$ 的 $K$ 个来源上完全相同：其 $\Gamma$ 都是

$$
(1,A^H,B^H,H),
\tag{TM.3336}
$$

而组成 $(H-8k,4k)$ 随 $k$ 改变。故合同 B 至少需要 $K$ 个补充值；§32.4 的尺寸商标签 $\sigma_K$ 在该家族上达到 $K$，所以 $M_B(\mathcal P_H)=K$。正三角的标签程序就是定理 33.1 的阈值剥离程序：每个标签先取其公开类，当前最小行用 $\alpha^{H-m}$ 测试，最后在列单射余集上 $\rho$ 后读 $E$。例如 $K=3$ 时可取

$$
\{(0,0),(1,0),(2,1)\},\qquad
\{(1,1),(2,0),(2,2)\},
\tag{TM.3337}
$$

两类都满足判据。证毕。

这些结果只关闭了声明的公共首替换层、两个饱和首窗切片和正三角实际子家族。全 $\mathcal T_H$ 的一般最优 $M_A(H)$、混合不同 $n$ 的标签判据、标签生产与认证、表和精确算术的构造成本、总记忆最优以及原树括号、叶路径、绝对时间和物理空间的恢复仍不由本节给出；特别是 $17\le H\le20$ 的全家族精确值没有由这里的四源见证确定，§32 保留的长期全家族问题继续开放。本文各证明是普通数学推导，不构成 Lean 核验或新的形式化真值声明。

## 33.99 追加锚
## 34. 混合首窗的实际上带判据、交叉障碍与 β 的必要性

本节固定 §30 的合同和一个公开的整数 $H\ge1$。来源是同一棵非空、有序、自由括号化的实际 $\alpha/\beta$ 原树；初始目标始终是原来源的 $q_H$，不是执行中来源的当前边界。读 $E$ 不改来源；$\rho$ 与左右正上下文拼接都先作实际叶数守卫，拒绝只写入 `reject`、保持来源并不给出被拒候选的读数。控制器使用同一初始化、同一公共输入和同一初始记录，允许任意大小的已取得档案，但每个实际来源逐点有限停止。标签、上下文、候选表、表的认证和所有算术都是供应或计算接口，均不等于运行时的 $m$、$n$ 端口。

§34.1 的分类器和 §34.2 的两个三源实例只研究公开实际子族

$$
\mathcal U_H\subseteq\{t\in\mathcal T_H:m(t)+n(t)>H\}.
\tag{TM.3401}
$$

上带条件使这两处的初始标签只有 $0$ 和 $1$：标签 $0$ 的 $n>H$ 只表示首个 $\rho$ 必拒；标签 $1$ 满足 $n\le H<m+n$。实际来源的 $m=a+b$、$n=a+2b$ 总有 $n\ge m$。§34.3 转而保留含标签 $2$ 的低对，并研究它与上带高对的交叉；它不受前一句的两标签限制。对标签 $0$，下面把 $n=\infty$ 当作候选表中的哨兵；它不是隐藏的实际整数，也不是可以调用的端口。

### 34.1 实际目标纤维与有序截止证书

**定义 34.1（上带实际表和截止块）。** 运行前给定一个有限的实际标签函数 $h$。初始读 $E_0=g$ 后，在每个 $(h,g)$ 纤维中，把实际来源的 $q_H$ 值去重，得到有限表 $C$。表的每一行来自声明的实际原树；它可以由原子卷定理 359.3 的三窗实际像正规形和定理 360.2 的 Euler 充要条件构造、认证，不能用环境中的任意坐标元组替代。

对 $q\in C$ 记其表内的 $m(q)$。标签 $1$ 行还记 $n(q)\le H$ 和 $z(q)=E_1(q)$；标签 $0$ 行置 $n(q)=\infty$，不填 $z$。一列截止

$$
0=c_0<c_1<\cdots<c_s\le H,\qquad c_s\ge\max_{q\in C}m(q)
\tag{TM.3402}
$$

给出块 $C_i=\{q\in C:c_{i-1}<m(q)\le c_i\}$。空块不施加条件。块 $C_i$ 称为 **F 块**，若存在函数 $f_i$ 使 $q=f_i(m(q))$；对精确去重表，这等价于 $m$ 在 $C_i$ 上单射。它称为 **R 块**，若

$$
\begin{aligned}
q,q'\in C_i, n(q)>c_i, n(q')>c_i, m(q)=m(q')&\Longrightarrow q=q',\\
q,q'\in C_i, n(q)\le c_i, n(q')\le c_i, (n(q),z(q))=(n(q'),z(q'))&\Longrightarrow q=q'.
\end{aligned}
\tag{TM.3403}
$$

第一行包括标签 $0$ 的 $n=\infty$；第二行只涉及标签 $1$。也就是说，R 块的拒绝分支上目标是 $m$ 的函数，接受分支上目标是 $(n,z)$ 的函数。对去重的精确初始目标表，这两项正是相应的单射条件。

**定理 34.2（上带混合 $n$ 的完整截止判据）。** 给定一个有限实际子族、一个固定的有限标签集 $L$，以及一个给定的初始来源标签函数 $h:\mathcal U_H\to L$，存在一个使用这份 $h$ 的单一忠实确定性取得协议，当且仅当每个非空 $(h,E_0)$ 纤维的实际表 $C$ 都有一个（TM.3402）截止序列，使每个非空块为 F 块或 R 块。

**证明。** 先证充分性。固定一个纤维和其证书，按截止递增扫描，跳过空候选块而不作来源调用，并保留每个非空块的原右端点 $c_i$。到 $c_i<H$ 时，尝试右侧固定括号的实际上下文 $\alpha^{H-c_i}$；$c_i=H$ 时省略零次上下文，不发出空动作。此前的每次拒绝都保持初始来源不变；跳过的空隙不含实际候选，所以第一次接受（或在 $c_i=H$ 时的隐式接受）恰好意味着

$$
 c_{i-1}<m\le c_i.
\tag{TM.3404}
$$

在选定块后令 $d=H-c_i$。F 块只作右侧单叶 $\alpha$ 填充直到第一次拒绝。若成功了 $s$ 次，当前来源在填充开始时有 $m+d$ 片叶，故 $m=c_i-s$；F 条件使原始 $q_H$ 唯一。

R 块先尝试一次 $\rho$。在拒绝分支，当前首窗为 $m+d\le H$，填充给出同一个 $m=c_i-s$；守卫拒绝等价于 $n+d>H$，即 $n>c_i$，所以第一行（TM.3403）给出唯一初始目标。在接受分支，因 $n+d\le H$，执行一次当前 $E$ 读，得到

$$
 E'=zB^d
\tag{TM.3405}
$$

（左上下文时是相应的已知可逆因子在另一侧）。已知因子只在控制器的算术中消去，不对来源作逆动作。随后仍以右侧 $\alpha$ 填充；若成功 $s$ 次，则 $n=c_i-s$，且由（TM.3405）恢复 $z$。第二行（TM.3403）把 $(n,z)$ 解码为唯一初始目标。若 $n=c_i$，填充没有成功动作但仍执行一次最终拒绝，故端点也在合同内。每个分支均有限停止；初始目标被原表解码，始终没有读取被拒上下文的候选 $E$，没有供应 $m$ 或 $n$。

再证必要性。把任意成功协议前置一次首读，并固定一个 $(h,E_0=g)$ 纤维。在首次 $\rho$ 以前，已接受的上下文组成总和记为 $(u,v)$，其两个叶数增量为

$$
D_0=u+v,\qquad D_1=u+2v,\qquad D_0\le D_1.
\tag{TM.3406}
$$

当前两个守卫尺寸分别是 $m+D_0$、$n+D_1$；所有当前读数只是固定的已知单位因子包围 $g$，因而在此纤维内不产生新的候选区别。拒绝上下文不改变来源，也不给候选读数。一个固定的首次 $\rho$ 历史因此只能留下一个实际的 $m$ 区间 $(\ell,u]$，其中

$$
 u=H-D_0.
$$

有限实际表和逐点有限停止保证实际出现的叶数区间只有有限个非空部分。置

$$
 c=H-D_1\le u.
\tag{TM.3407}
$$

在该叶执行 $\rho$ 时，$n\le c$ 的候选接受，$n>c$ 的候选拒绝。下面的叶数等式中 $n$ 是原来源的实际第一替换叶数；标签 $0$ 行的表内哨兵 $\infty$ 只用于截止比较，并与实际 $n>H$ 给出同一拒绝分支。记该叶的实际目标表为 $C_{\ell,u}=\{q\in C:\ell<m(q)\le u\}$。拒绝时 $n+D_1>H$，当前来源落标签 $0$，其 $q_H$ 仅为 $(0,L_0gR_0,m+D_0)$，其中 $L_0,R_0$ 是这份共同历史的已知单位因子。因而相同 $m$ 而不同初始目标的两行已有相同完整记录和相同当前 $q_H$，由定理 30.2 永远不能再分开。

接受时，新来源的下一次替换叶数满足

$$
\lambda _1(\rho(\text{当前来源}))
=\lambda _2(\text{当前来源})
=m+n+D_0+D_1>H.
$$

故接受后也落标签 $0$，当前叶数为 $n+D_1$，当前 $E=L_1zR_1$，其中 $L_1,R_1$ 是共同的已知单位因子。相同 $(n,z)$ 而不同初始目标的两行同样具有相同完整记录和相同当前 $q_H$，也由定理 30.2 永久合并。因此成功协议强制

$$
\begin{aligned}
q,q'\in C_{\ell,u},\ n(q)>c,\ n(q')>c,\ m(q)=m(q')&\Longrightarrow q=q',\\
q,q'\in C_{\ell,u},\ n(q)\le c,\ n(q')\le c,\ (n(q),z(q))=(n(q'),z(q'))&\Longrightarrow q=q'.
\end{aligned}
\tag{TM.3408}
$$

若 $c>\ell$，下半区间 $(\ell,c]$ 是 R-safe：其拒绝键为 $m$，接受键为 $(n,z)$，正好给出（TM.3403）的两行；上半区间 $(c,u]$ 中有 $n\ge m>c$，全部拒绝，因而是以端点 $u$ 为右端的 F-safe 区间。若 $c\le\ell$（包括 $c<0$），整个叶 $(\ell,u]$ 都是 F-safe；若协议在首次 $\rho$ 前停止，其非空叶也只能是 F-safe，因为共同记录上只能输出一个值。

把所有非空首次 $\rho$ 叶和停止叶按 $m$ 排序。对每个叶保留其必要右端点：R-safe 下半段保留 $c$，F-safe 上半段或整叶保留 $u$；空的下半段、上半段和没有实际目标的候选间隙均可保留为空块。将这些右端点去重并递增排列，加入 $0$，并在需要时加入 $H$，得到有限序列（TM.3402）；每个有实际目标的块都落在上面的某个 F-safe 或 R-safe 部分。只有在一个空隙确实没有实际候选、且吸收它不会改变相邻非空块所需的右端点和 $m$／$(n,z)$ 键时，才允许把空隙吸收到相邻块；本构造默认保留空块，不把相邻 R 块任意合并，因为移动其端点会改变接受的 $n$。于是每个非空块都是 F 块或 R 块。任意其他首次有效动作都是一个正上下文，其实际增量仍给出同一个标量截止；因此不遗漏动作类型。充分性与必要性合在一起证明判据。$\square$

**推论 34.3（原始目标延续与实际调用界）。** 定理 34.2 也适用于一个已经运行过的节点：若取得档案已经认证所有仍存的当前实际来源属于（TM.3401），并且档案表逐行保存“当前实际 profile—原始 $q_H$ 目标”的配对，则在每个相同当前 $E_0$ 的档案纤维内，把 F 块条件替换为“原始目标在 $m$ 的纤维上恒定”，把 R 块（TM.3403）的两项条件分别替换为“拒绝分支的原始目标在 $m$ 的纤维上恒定”和“接受分支的原始目标在 $(n,z)$ 的纤维上恒定”，同一截止执行器恰好恢复原始目标。认证是对实际来源像的认证，不是把原始目标或隐藏尺寸作为运行时端口。

对于初始表令 $R$ 为纤维中占用的不同 $m$ 行数。扫描跳过空候选块而不调用来源，保留每个非空块的原右端点；每个这样的块至少占用一行不同的 $m$，故至多使用 $R$ 次非空阈值拼接，最终端点 $c_i=H$ 仅隐式接受；每条路径至多一次 $\rho$，接受时至多一次最终 $E$ 读；填充包含所有成功的单叶和最后一次被拒的单叶，至多 $H$ 次来源调用。连同初始读，实际来源调用数满足

$$
 1+R+1+1+H=H+R+3.
\tag{TM.3409}
$$

这里明确计入初始读和填充的最终拒绝；两个额外的一项分别是 $\rho$ 和接受后的最终读。若阈值端点为 $H$，零次上下文被省略而不计为空动作；若填充成功次数为零，仍发出一次非空单叶并记录最终拒绝。式（TM.3409）只是存在性上界，不是调用最优性主张。上下文生成与供给、标签生产和认证、实际表的构造、精确算术、输出表示和全部记忆各自计费。

### 34.2 正的混合 $n$ 实例与交叉切片障碍

**命题 34.4（正混合 $n$ 的三源取得）。** 对每个 $H\ge9$，取固定括号的实际词

$$
 X_H=\beta^2\alpha\beta^2\alpha^{H-9},\qquad
 Y_H=\alpha^{H-4},\qquad
 Z_H=\alpha^H.
\tag{TM.3410}
$$

则三者有共同 $E_0=A^H$，共同 $E_1=B^H$，而

$$
\begin{array}{c|ccc}
 &m&n&\lambda _2=m+n\\ \hline
X_H&H-4&H&2H-4\\
Y_H&H-4&H-4&2H-8\\
Z_H&H&H&2H
\end{array}
\tag{TM.3411}
$$

都在上带。一个标签的实际协议是：首读后尝试右侧 $\alpha^4$；它在 $Z_H$ 上拒绝，在 $X_H,Y_H$ 上接受；随后只在接受分支尝试 $\rho$，它在 $X_H$ 上拒绝、在 $Y_H$ 上接受。必要时接受分支读当前 $E$，再按定理 34.2 的表解码。故公共 $n$ 的“先剥离唯一最小行”规则不能扩展到这里：$\alpha^4$ 先把 $Z_H$ 与 $X_H,Y_H$ 分开，再由 $\rho$ 分开共享 $m$ 的 $X_H,Y_H$。

**证明。** 计数给出（TM.3411）。由 $B^2=-1$、$B^4=1$、$A^2=1$，

$$
 E_0(X_H)=B^2AB^2A^{H-9}=A^{H-8}=A^H,
$$

且 $S^2BS^2=B$ 给出

$$
 E_1(X_H)=S^2BS^2B^{H-9}=B^{H-8}=B^H.
$$

这里最后的终端幂是 $B^{H-9}$；当 $H=9$ 它是零次幂，仍给出 $E_1(X_9)=B^{1}=B^9$，没有省略或改写终端因子。$Y_H,Z_H$ 的两式分别是 $A^{H-4},A^H$ 与 $B^{H-4},B^H$，同样因四次幂为单位而相等。右接 $\alpha^4$ 的首窗守卫正是 $m+4\le H$；$\alpha^4$ 本身只把 $Z_H$ 与 $X_H,Y_H$ 分开，并不区分 $X_H,Y_H$。在接受分支再作 $\rho$ 时，$X_H$ 的守卫为 $n+4=H+4>H$ 而拒绝，$Y_H$ 的守卫为 $n+4=H$ 而接受，故两步才完成三分。若先作 $\rho$，$X_H,Z_H$ 都因 $n=H\le H$ 而接受；二者初始 $m$ 分别为 $H-4$ 和 $H$，初始 $q_H$ 不同，但接受后当前叶数同为 $H$、当前 $E=B^H$，且下一次替换叶数 $m+n>H$，故当前标签同为 $0$、当前 $q_H$ 相同，初始目标由定理 30.2 永久合并；若只填充，$X_H,Y_H$ 的相同 $m,E_0$ 也会合并。这说明正上下文的实际守卫是混合层所需的关系。$\square$

**定理 34.5（交叉 $n$ 的三源精确两标签容量）。** 对每个 $H\ge16$，取

$$
 X_H=\beta^2\alpha\beta^2\alpha^{H-13},\qquad
 Y_H=\alpha^{H-4},\qquad
 Z_H=\beta^8\alpha^{H-16}.
\tag{TM.3412}
$$

这些实际来源共有 $E_0=A^H$，其参数和关键下一窗为

$$
\begin{array}{c|ccc|c}
 &m&n&\lambda _2&E_1\\ \hline
X_H&H-8&H-4&2H-12&B^H\\
Y_H&H-4&H-4&2H-8&B^H\\
Z_H&H-8&H&2H-8&S^8B^{H-16}
\end{array}
\tag{TM.3413}
$$

在显示子族 $\{X_H,Y_H\}$ 上一个标签足够，右接 $\alpha^8$ 按首窗守卫分开二者；三源子族 $\{X_H,Y_H,Z_H\}$ 的精确初始标签容量为 $2$：一个标签给 $Z_H$，另一个给 $\{X_H,Y_H\}$。一个标签不可能在原始 $q_H$ 下取得三者。

**证明。** 先核对实际表。对 $X_H$，

$$
E_0(X_H)=B^2AB^2A^{H-13}=A^{H-12}=A^H,
\qquad
E_1(X_H)=S^2BS^2B^{H-13}=B^{H-12}=B^H;
$$

$Y_H$ 给出 $A^{H-4},B^{H-4}$，而 $Z_H$ 给出 $B^8A^{H-16}=A^{H-16}=A^H$ 和 $S^8B^{H-16}$。计数给出（TM.3413）。当 $H=16$ 时，$Z_{16}=\beta^8$ 是非空纯 $\beta$ 端点，表中 $\alpha^0$ 只是零次尾块，不是空来源。

一个标签不可能的证明必须覆盖所有共同前缀。固定任意协议并考察首次 $\rho$ 以前的历史。初始读、只读和全拒绝的上下文在三源上完全相同。令已经接受的正上下文的总首窗、下一窗增量为 $U,V$；每个实际上下文满足 $d_1\ge d_0>0$，故 $V\ge U$。若 $V>4$，$X_H,Z_H$ 的当前 $n$ 都大于 $H$，而它们的当前 $m$ 都是 $H-8+U$，首读只差同一个已知因子；二者同时落标签 $0$ 并合并。因此正确协议在此以前必须有 $V\le4$。

若此时首次作 $\rho$，$X_H,Y_H$ 都因 $n+V=H-4+V\le H$ 而接受；第一次替换后的来源满足

$$
\lambda _1(\rho(\text{当前来源}))
=\lambda _2(\text{当前来源})
=m+n+U+V>H
$$

（对 $H\ge16$ 已有 $2H-12>H$），且两者的共同初始 $E_1=B^H$ 在这段共同历史后仍只被同一个已知可逆因子包围；它们有相同的当前标签 $0$ 和相同的完整记录，所以初始目标合并。若不作 $\rho$而用正上下文分开 $X_H,Y_H$，其首窗增量 $d$ 必须满足

$$
 U+d>4,\qquad d_1\ge d,\qquad
 V+d_1\ge V+d>V+4-U\ge4,
$$

即接受这个上下文后已经进入 $V>4$ 的合并情形。接受两者的上下文没有区别，拒绝两者的上下文也没有区别；连续作这些动作最终要么进入 $V>4$，要么违反逐点有限停止。首读、只读和全拒绝前缀都不能在三源上停止。故不存在一个标签的共同协议。

两个标签足够：给 $Z_H$ 一个标签并直接输出其公开的原始目标；给 $\{X_H,Y_H\}$ 一个标签，右接 $\alpha^8$，在 $X_H$ 上尺寸从 $H-8$ 到 $H$ 而接受，在 $Y_H$ 上从 $H-4$ 到 $H+4$ 而拒绝，记录立即区分二者。非空家族至少需要一个标签，而前段证明排除了一个标签，所以显示三源子族的精确容量是 $2$。$\square$

### 34.3 β 的必要性：一个参数化四源容量分离

**定理 34.6（β 必要性的四源族与精确公开容量）。** 对任意 $r\ge0$ 置 $H=16+4r$，取

$$
\begin{aligned}
 P_r&=\beta\alpha^{5+2r},&Q_r&=\alpha^2\beta\alpha^{3+2r},\\
 X_r&=\beta^3\alpha\beta^2\alpha^{4+4r},&Y_r&=\beta\alpha^{13+4r}.
\end{aligned}
\tag{TM.3414}
$$

令 $\mathcal F_r=\{P_r,Q_r,X_r,Y_r\}$，所有词按固定左结合括号实现。由 $\rho^2(\alpha)=\beta\alpha$、$\rho^2(\beta)=\beta\alpha\beta$，并置 $S=BA$，有

$$
\begin{aligned}
&E_0(P_r)=E_0(Q_r)=E_0(X_r)=E_0(Y_r)=S,\\
&E_1(P_r)=E_1(Q_r)=(-1)^rS^2A,\qquad
 E_1(X_r)=E_1(Y_r)=S^2A,\\
&E_2(P_r)=-S^{-3-2r}A,\qquad E_2(Q_r)=-S^{1-2r}A,\\
&E_2(X_r)=(SB)^3S(SB)^2S^{4+4r},\qquad
 E_2(Y_r)=(SB)S^{13+4r}.
\end{aligned}
\tag{TM.3415}
$$

低对与高对的组成、尺寸和第二窗叶数为

$$
\begin{array}{c|c|c|c|c}
 & (a,b)&(m,n)&(E_0,E_1)&\lambda _2\\ \hline
P_r,Q_r&(5+2r,1)&(6+2r,7+2r)&(S,(-1)^rS^2A)&H-3\\
X_r&(5+4r,5)&(H-6,H-1)&(S,S^2A)&2H-7\\
Y_r&(13+4r,1)&(H-2,H-1)&(S,S^2A)&2H-3
\end{array}
\tag{TM.3416}
$$

The high pair always has $(E_0,E_1)=(S,S^2A)$; the low pair has $(S,(-1)^rS^2A)$, so it agrees with the high pair exactly when $r$ is even. In every case all four have $E_0=S$. The exact $E_2$ entries in (TM.3415) are the literal products of the displayed words, not coordinates supplied independently of them. In particular $E_2(P_r)\ne E_2(Q_r)$ by uniqueness of the $S^kA$ normal form.

In the original contract allowing arbitrary actual positive contexts, $\mathcal F_r$ has one-label capacity; if only left and right positive pure-$\alpha$ contexts are allowed while retaining the original $\rho$ and read operations, the exact capacity is two. Both capacities concern the displayed four-source actual subfamily; they do not define or claim the full-family $M_A(H)$.

**证明。** 先给一个标签的实际协议。首读后右接一个 $\beta$ 叶；四源都接受，此上下文在三个窗口的增量为 $(1,2,3)$。随后尝试 $\rho$：$X_r,Y_r$ 的当前首个替换尺寸为 $H+1$，故拒绝；填充右侧 $\alpha$ 到首次拒绝，成功次数分别为 $5$ 和 $1$，从 $m=H-s-1$ 恢复两个不同的初始目标。$P_r,Q_r$ 的第一次替换接受；读取当前 $E$ 后消去已知的 $E_1(\beta)=S$，再尝试第二次 $\rho$。第二次守卫在恰为 $H$ 时接受；再读并消去已知的 $E_2(\beta)=S^2A$，由（TM.3415）分开 $P_r,Q_r$。每个分支都返回原始 $q_H$。高对 $X_r$ 分支恰用初读、$\beta$ 拼接、一次被拒的 $\rho$、五次成功的 $\alpha$ 填充和一次最终拒绝，共 $9$ 次；$Y_r$ 分支同理共 $5$ 次。低对分支用初读、$\beta$ 拼接、两次接受的 $\rho$ 及其两次读数，共 $6$ 次；没有发出零次上下文。故 quartet 的最坏实际来源调用数为 $9$。

下面证明纯 $\alpha$ 一个标签不可能，且这个结论包含所有左右方向和所有正长度。$P_r,Q_r$ 共享 $E_0,E_1$、相同 $m=6+2r$，但（TM.3415）给出不同的初始 $E_2$。任一纯 $\alpha$ 上下文的首窗和下一窗增量相同，等于其长度 $d\ge1$。若首个有效上下文有 $2\le d\le H-(6+2r)=10+2r$，它在低对上接受，并使第二窗尺寸从 $H-3$ 增加 $2d$，越过 $H$；两行随后有相同当前标签、相同两个记录窗口和相同首窗尺寸，第三窗已被合同丢弃。若 $d>10+2r$，四个来源都拒绝，记录没有区别。长度 $d=1$ 在四个来源上都接受，但在此后再接受任何正长度纯 $\alpha$ 上下文时，低对的累计长度至少为 $2$，回到前一种低对合并，或直接全拒绝。

另一种首个有效动作是 $\rho$。它在高对上接受，并把 $X_r,Y_r$ 送到当前尺寸 $H-1$、共同当前 $E_1=S^2A$ 的标签 $0$；若此前已接受唯一的一个 $\alpha$ 叶，则高对当前尺寸为 $H$，同样同时变为标签 $0$。左右拼接只在相同记录两侧乘以同一个已知因子，不改变这些合并。因而首个 $\rho$ 也毁掉高对的初始区别。首读、全拒绝上下文和只读动作都产生共同记录；逐点有限停止排除永远停留在这些前缀。所有纯 $\alpha$ 长度和两侧已穷尽，故一个标签不可能。

两个标签足够：给 $\{P_r,Q_r\}$ 一个标签，连续两次 $\rho$ 并在接受后读 $E_1,E_2$，由（TM.3415）解码；给 $\{X_r,Y_r\}$ 一个标签，纯 $\alpha$ 填充至首次拒绝，两个不同的初始 $m$ 解码。非空家族至少需要一个标签，于是显示子族的精确容量为

$$
M_A(\mathcal F_r)=1,\qquad M_A^{\alpha}(\mathcal F_r)=2.
\tag{TM.3417}
$$

逐对可分不推出共同取得：定理 30.2 的行为商和这些实际脚本都允许逐对用读、$\rho$ 与纯 $\alpha$ 阈值分开，但一个共同初始化的协议必须面对同一份记录；这里正是低对的第二窗和高对的首窗在同一首动作上的不可兼容。$\square$

### 34.4 来源范围、复用与未决边界

本节复用 §§28–33 的固定守卫、同记录合并、填充执行器和公共 $n$ 判据；原子卷 §§355–357 提供 Clifford 叶积、替换窗口和矩阵关系，§§359.3、360.2 提供实际三窗像和固定历史纤维的 Euler 认证。这里的新增内容是上带混合 $n$ 的有序截止充要条件、实际终端执行器、正混合实例、交叉 $n$ 三源精确两标签容量和参数化 β/纯 α 容量分离。它们都是指定实际来源和固定合同下的普通数学推导，不构成 Lean 核验、冻结声明或文献优先性主张。

表和标签的生产、实际像的枚举与认证、上下文的生成和传输、已知因子的精确算术、控制器和档案的内存、原树括号与叶路径的恢复、原始时间和物理空间的恢复均未计入（TM.3409）或（TM.3417）。本节没有给出含标签 $2$ 的全家族混合分类，没有给出全家族 $M_A(H)$ 或其最优调用数，也没有把一个实际子族的容量升级为全 $\mathcal T_H$ 的容量。上带判据的表必须来自实际来源像；标签 $0$ 的 $\infty$ 只用于表的分支书写。

## 34.99 追加锚

## 35. 整段自适应截止压缩、双资源运输与原始目标的嵌套取得

### 35.1 实际配对档案与固定合同

固定公开整数 $H\ge1$，来源、替换、读和左右正上下文仍取 §30 的同一合同。初始来源属于声明的有限实际子族 $\mathcal F\subseteq\mathcal T_H$；固定有限标签集 $L$ 和已经供应的同源函数 $h:\mathcal F\to L$。目标始终是

$$
\tau(t)=q_H(t),\qquad t\in\mathcal F,
\tag{TM.3501}
$$

右端取初始来源，后续动作不重新定义它。在一个已取得节点，采用配对行 $(s,\eta(s),\tau)$：$s$ 是该记录下的当前实际来源，$\eta(s)$ 是它的完整三窗和组成，$\tau$ 是同一行携带的初始目标。可以只存完整 $\eta$ 与目标，但每行必须有认证的实际实现，并由声明初始族沿该分支的真实动作得到。显式原树或正词可作为认证；一般实际像认证可复用原子卷 §§359.3、360.2。重复的完整配对行可以去重；当前 $q_H$ 相同而原始 $\tau$ 不同的行必须同时保留。定理 30.2 随即判定这种共同记录下的碰撞不可恢复。

完整 $\eta$ 只是离线表坐标，不是运行时端口。在线控制只访问真实累积记录与当前实际 $E$；所有隐藏尺寸、隐藏窗口、初始目标和未来分支表均不得直接查询未知来源。表中记

$$
m=\lambda _0(s),\qquad n=\lambda _1(s),\qquad
\lambda _2(s)=m+n,\qquad \lambda _3(s)=m+2n.
\tag{TM.3502}
$$

这里即使当前标签为 $0$，离线实际实现仍有有限的真实 $n>H$，不把它变成在线读数。先执行一次当前 $E$ 读，将表按真实读出的值划分；以下每个阶段从一个共同读数 $E(s)=g$ 的实际纤维开始。标签供应、全部实际表和认证、所有已知上下文的 $h_i(v)=E_i(v)$、上下文生成与传输、精确算术、记录和控制器存储各自计费。

### 35.2 双资源正上下文与已知因子的记录运输

对整数 $d\ge1$、$0\le r\le d$，令 $K(d,r)$ 是固定左结合括号的实际非空词

$$
K(d,r)=\alpha^{d-r}\beta^r.
\tag{TM.3503}
$$

零次子块只省略该子块；$d>0$ 保证剩下的是非空来源。它作为一次受守卫的右拼接执行，其组成与前三项资源增量为

$$
c(K)=(d-r,r),\qquad
(D_0,D_1,D_2)=(d,d+r,2d+r).
\tag{TM.3504}
$$

已知窗口因子保持字面乘法次序：

$$
k_0=A^{d-r}B^r,\qquad
k_1=B^{d-r}S^r,\qquad
k_2=S^{d-r}(S^2A)^r,
\qquad S=BA,\qquad SB=S^2A.
\tag{TM.3505}
$$

一般已接受正上下文的总组成为 $(u,v)$ 时，$D_0=u+v$、$D_1=u+2v$、$D_2=D_0+D_1$。可实现的整数对恰为

$$
0<D_0\le D_1\le2D_0,
\qquad d=D_0,\qquad r=D_1-D_0.
\tag{TM.3506}
$$

零对 $(D_0,D_1)=(0,0)$ 只表示省略拼接；下文写 $d=r=0$ 时没有 $K$ 来源调用，也不制造空实际来源。

**引理 35.1（同组成的已知因子延续运输）。** 两个实际模板含同一个未知的 $\rho^j(t)$ 单次出现，其余材料已知，且已知组成相同。任一模板上基于完整记录的确定性延续，可在另一个模板上用真实当前读和已知单位算术模拟，保持全部动作守卫和原始目标输出。模拟保存真实物理记录与计算出的虚拟记录两份；它不要求两份读数字面相等。

**证明。** 单出现的存在及正组成更新复用引理 30.1；此处另证完整延续的可执行模拟。对每个窗口指标 $i$，两模板的读数分别写成

$$
L_iE_i(\rho^jt)R_i,\qquad P_iE_i(\rho^jt)Q_i,
\tag{TM.3507}
$$

四个外因子都是已知实际材料的单位。只要第二模板的当前读 $e$ 已经真实取得，第一模板的虚拟当前读为

$$
L_0P_0^{-1}eQ_0^{-1}R_0.
\tag{TM.3508}
$$

这里仅在算术中对已知 $P_0,Q_0$ 求逆，不对未知来源作求逆、取消、重置或复制。未被守卫许可的未知窗口不进入运行时计算；被拒候选没有 $E$ 可供（TM.3508）。

两模板组成相同，故同一个后续正上下文在两边有同样的拼接守卫，同一次 $\rho$ 也有同样的候选尺寸。若两边均右接已知 $w$，四因子更新为

$$
(L_i,R_i,P_i,Q_i)\longmapsto
(L_i,R_ih_i(w),P_i,Q_ih_i(w));
\tag{TM.3509}
$$

若均左接 $w$，更新为

$$
(L_i,R_i,P_i,Q_i)\longmapsto
(h_i(w)L_i,R_i,h_i(w)P_i,Q_i).
\tag{TM.3510}
$$

这些次序由结合乘法直接给出，不能交换非交换因子。接受 $\rho$ 后，各因子序列移动到下一窗口，未知单出现变成 $\rho^{j+1}(t)$；拒绝时模板及因子均不变。每次物理读按（TM.3508）产生虚拟读，守卫位连同原动作身份写入虚拟记录，再把该完整虚拟记录送给原控制器；因此它的下一动作和停止输出都可逐步重建。真实记录始终保存实际执行的动作、实际守卫位和实际读，不用虚拟读覆盖它。归纳得到延续模拟。

所有已知因子序列由三窗、$F$ 和 $j$ 生成，已有 $F^6=\operatorname{id}$ 允许有限周期表示；有限程序也可以只生成它实际用到的已知因子。此事实不供应未知深窗。$\square$

若一个无 $\rho$ 前缀最终把未知源 $s$ 变成窗口 $L_iE_i(s)R_i$，将该尚未执行的前缀改为一次右接同组成的 $K(d,r)$ 后，物理窗口为 $E_i(s)k_i$。此时虚拟窗口可写为

$$
E_i^{\rm virtual}=L_iE_i^{\rm physical}k_i^{-1}R_i.
\tag{TM.3511}
$$

这是事先构造的替代协议，绝非撤销已经执行的不可逆前缀；同组成保留两个守卫增量和以后所有 Fibonacci 增量。一般已知词的叶序和材料相对未知出现的左右位置可能改变外因子，故不能以相同组成冒充相同读数；固定叶序与未知出现位置时，纯括号重排不改变这些结合乘积。

### 35.3 整个无替换自适应阶段的有序截止压缩

**引理 35.2（整段阶段压缩）。** 固定共同当前读数 $g$ 的有限实际配对表。任一逐点有限成功协议，从阶段入口到首次尝试 $\rho$ 或停止的整个自适应部分，可以由递增截止扫描替代。每个占用块保留原叶的端点

$$
c=H-D_0,
\tag{TM.3512}
$$

以及原叶的准确 $D_1$。选中块只接受一个 $K(D_0,D_1-D_0)$ 宏拼接；零对时省略。替代后原阶段完整记录可计算重建，接受 $\rho$ 后的延续由引理 35.1 运输。

**证明。** 阶段内未尝试 $\rho$，故全部当前读都是已知左右因子包围入口 $g$；相同入口读及相同既有动作记录上的下一读完全确定，不新增来源区别。若已经接受的上下文累计首窗、下一窗增量为 $(U,V)$，下一个叶数为 $e>0$ 的上下文守卫恰为

$$
m+U+e\le H\quad\Longleftrightarrow\quad m\le H-U-e.
\tag{TM.3513}
$$

接受增加两个累计量，拒绝不改变任何累计量且不给候选读。因此一份终端阶段历史的入口尺寸条件是某个整数区间

$$
\ell<m\le H-D_0,
\qquad D_0\le D_1\le2D_0,
\tag{TM.3514}
$$

其中 $\ell$ 是各拒绝阈值给出的最大下界，若无拒绝则取 $0$。全部接受阈值随累计首窗增量下降，最后一次接受给出最紧上界 $H-D_0$；无接受时上界为 $H$。这解释了（TM.3512），它不是该叶实际占用的最大 $m$。

有限实际表上的每条路径都有限停止，故各行直到第一次 $\rho$ 或停止的有限路径并集也是有限树。不同终端历史的整数区间互不相交：假如某个尺寸同时满足两份历史，入口读 $g$ 与各阈值守卫就会使同一个确定性控制器走两条路径，矛盾。删除没有实际行的叶，再按各叶右端点 $c$ 递增排列；不同占用叶不能有同一右端点。上一占用叶的右端点与下一叶下界之间可以有空隙，但其中没有实际候选。

以这些原右端点作截止。对一个较晚占用块，先前各宏的首窗守卫都拒绝，来源保持为入口源；到自身端点 $c$ 的宏才接受。故第一次接受选中恰好同一实际叶。若该叶端点大于它占用的最大尺寸，仍须保留端点，因为改变它会改变 $D_0$ 和 $D_1$。首个占用块之前、相邻占用块之间、最后占用尺寸到其端点之间的空隙不增添候选；可以显式留为空块，不能借空隙移动占用叶端点。$c=H$ 表示隐式选择并省略零对动作。

选中宏的组成等于原叶全部已接受上下文之和。原叶每个已接受中间前缀的首窗累计增量不超过 $D_0$，所以宏接受时这些原中间接受也都合法；原拒绝探针则按该叶历史中的阈值重建，不实际执行其候选。原读按入口 $g$ 与该历史的已知因子重建。因此被选中的整份阶段历史，包括动作身份、所有接受和拒绝位、每次真实已取得的原读和停止选择，都由入口读与被选叶计算决定。叶后的真实宏源与原叶源满足（TM.3511），引理 35.1 运输后续完整记录控制。被压缩的是整个无 $\rho$ 自适应阶段，而不只是重新命名已有单出现不变量。$\square$

### 35.4 实际行上的有限嵌套证书

**定义 35.3（嵌套截止证书）。** 一个入口表先真实读取当前 $E$，各非空纤维分别给出以下证书。在共同 $E=g$ 的纤维 $C$ 中选整数

$$
0=c_0<c_1<\cdots<c_s\le H,
\qquad c_s\ge\max_{C}m,
\qquad C_i=\{(s,\eta(s),\tau)\in C:c_{i-1}<m\le c_i\}.
\tag{TM.3515}
$$

空块不施加义务、也不调用来源，但保留后续非空块的端点。每个非空块取

$$
d_i=H-c_i,\qquad 0\le r_i\le d_i,\qquad
(D_0,D_1)=(d_i,d_i+r_i),
\tag{TM.3516}
$$

并属于以下两类之一。

F 块要求原始 $\tau$ 在该块的每个 $m$ 纤维上恒定。R 块按真实替换守卫分为

$$
C_i^- =\{n+d_i+r_i>H\},\qquad
C_i^+ =\{n+d_i+r_i\le H\}.
\tag{TM.3517}
$$

在 $C_i^-$ 上要求 $\tau$ 在 $m$ 纤维上恒定。在 $C_i^+$ 上逐行右接一次 $K(d_i,r_i)$ 后尝试 $\rho$，零对只省略拼接；接受后真实读取当前 $E$，每个实际读纤维携带原始 $\tau$ 并有下一层证书。后继的离线实际组成、三窗由实际拼接及 $M,F$ 计算，特别是

$$
\begin{aligned}
m'&=n+d_i+r_i,\\
n'&=m+n+2d_i+r_i,\\
E'&=E_1(s)k_1.
\end{aligned}
\tag{TM.3518}
$$

$E'$ 的纤维正是 $z=E_1(s)$ 的纤维，因为 $k_1$ 已知且可逆；只有接受后取得的 $E'$ 才能在算术中消去 $k_1$。递归发生在接受 $\rho$ 后的实际读上；拒绝分支没有候选 $E$、没有这类子节点。证书是有限树，所有子行保留认证的实际实现及相同原始 $\tau$。

**定理 35.4（任意标签混合的原始目标取得充要条件）。** 对固定 $H\ge1$、有限实际 $\mathcal F$、有限 $L$ 与给定 $h$，一个使用同一初始化的忠实确定性协议逐点有限停止并取得初始 $q_H$，当且仅当每个非空初始 $(h,E_0)$ 实际配对纤维具有定义 35.3 的嵌套证书。初始标签可以任意混合 $0,1,2$。

**证明。** 充分性给出实际执行器。进入一个已读纤维，按端点递增扫描其非空块；在 $c_i<H$ 时尝试一次真实右接 $K(d_i,r_i)$，在 $c_i=H$ 时省略。此前拒绝都保留入口源，故首次接受或末端隐式选择恰好选中 $C_i$。不能把宏拆成一串单叶守卫，§35.7 给出实际反例。

F 块选中后，以右接单叶 $\alpha$ 填充到第一次拒绝。若成功 $s$ 次，则填充开始时叶数为 $m+d_i$，所以

$$
s=H-(m+d_i)=c_i-m,\qquad m=c_i-s.
\tag{TM.3519}
$$

表的 F 函数据此返回唯一原始 $\tau$。若成功次数为零，仍发出一次非空 $\alpha$ 并记最终拒绝。R 块选中后尝试 $\rho$，实际守卫给出（TM.3517）；拒绝不改源，同一填充公式及拒绝表的 $m$ 纤维函数返回原始目标。接受时执行实际 $E$ 读，按（TM.3518）进入相应真实子表，再执行其证书。有限证书及有限填充保证逐点停止，归纳确保所有叶输出同一行的初始目标；没有取得隐藏 $m,n$ 的端口。

必要性从任一成功协议开始，在每个阶段入口加入一次当前实际读。该读不改变来源，只增加已计费用；固定其实际纤维后，用引理 35.2 压缩整个首次 $\rho$ 前缀。停止叶共同记录只能输出一个 $\tau$，因而满足 F 条件。首次 $\rho$ 叶保留准确 $(D_0,D_1)$，其拒绝条件为 $n+D_1>H$。此时当前源仍在上限内，下一替换尺寸却已超过 $H$；以后正上下文只增加这个尺寸，拒绝替换永远不会被它重新打开。两行若有同一入口 $m$，则它们在该拒绝分支有相同完整原记录、相同当前 $E$ 和相同当前尺寸 $m+D_0$，当前标签均为 $0$，故当前 $q_H$ 相同。定理 30.2 排除从此共同记录恢复两个不同原始目标。因此拒绝分支的 $\tau$ 必在入口 $m$ 纤维上恒定。

首次 $\rho$ 接受的行，在宏拼接后也有相同替换守卫。引理 35.1 把原成功延续运输到这些实际宏后继，且保留原始 $\tau$。加入一次真实当前读，对其每个实际纤维再次压缩。重复过程不会用相同当前 profile 删除不同目标；这种配对碰撞仍由定理 30.2 直接排除。各子表均由同一真实动作从父表的存活行生成，不能把未取得的数学窗口作为分支。

此递归有限性由下面的统一替换深度界保证；每个阶段只有有限实际行、有限非空尺寸块及有限实际读纤维。按剩余替换深度归纳，即得有限嵌套证书。$\square$

**推论 35.5（接受替换深度与存在性调用界）。** 取 $F_1=F_2=1$、$F_{k+2}=F_{k+1}+F_k$，并令

$$
J_H=\max\{j\ge0:F_{j+1}\le H\}.
\tag{TM.3520}
$$

任一实际合法路径接受 $\rho$ 的次数至多 $J_H$。若定理 35.4 的证书存在，则它有一个实际执行器，未知来源调用数至多

$$
H(J_H+2)+2(J_H+1).
\tag{TM.3521}
$$

**证明。** 接受 $j$ 次 $\rho$ 后，由已有单出现不变量，当前组成为 $M^jc(t)+b$，其中 $b\in\mathbb N^2$ 是已知正材料累计的贡献。若初始组成为 $(a_0,b_0)$，未知出现本身的叶数为

$$
\lambda_j(t)=F_{j+1}a_0+F_{j+2}b_0\ge F_{j+1},
\qquad a_0+b_0\ge1.
\tag{TM.3522}
$$

当前源含这个出现且叶数不超过 $H$，故 $j\le J_H$。特别地 $J_1=1$：单叶 $\alpha$ 的第一次替换得到单叶 $\beta$，第二次候选有两叶而拒绝；把 $J_1$ 取成零会遗漏合法路径。

证书执行器至多有 $J_H+1$ 个阶段。每阶段非空块至多 $H$ 个，因为每块占用不同整数尺寸；因而截止扫描至多 $H$ 次来源调用，入口实际读一次，R 叶至多一次 $\rho$ 尝试。接受后的当前读就是下一阶段入口读，不重复计数。只有一个终端阶段进行填充；至多 $H-1$ 次成功和一次最终拒绝，合计至多 $H$。相加为 $(J_H+1)(H+2)+H$，即（TM.3521）。这是成功协议存在时的一个调用上界；不声明最少调用，也不把标签、证书、实际表、上下文供给、算术及全部记忆成本计为零。$\square$

### 35.5 第三未来窗超限时的两层完整判据

**推论 35.6（$\lambda _3>H$ 的两层判据）。** 若每个初始实际来源满足 $\lambda _3=m+2n>H$，则定理 35.4 的条件等价于：在各初始 $(h,E_0)$ 纤维选择（TM.3515）首层块及（TM.3516）的 $(d,r)$；每块为 F，或其首次 $\rho$ 拒绝部分的原始 $\tau$ 是 $m$ 的函数，而每个首次 $\rho$ 接受后的真实 $E$ 纤维满足推论 34.3 的配对原始目标上带截止判据。

准确地，在一个首层接受纤维中，当前坐标为

$$
x=n+d+r,\qquad y=m+n+2d+r,\qquad E=E_1(s)k_1.
\tag{TM.3523}
$$

每个这样的当前读纤维独立选择 $0=b_0<b_1<\cdots<b_t\le H$、$b_t\ge\max x$，保留非空块端点并跳过空块。在其第二层块 $(b_{j-1},b_j]$ 内，F 条件是原始 $\tau$ 在 $x$ 纤维上恒定；R 条件是在 $y>b_j$ 的行上 $\tau$ 为 $x$ 的函数，在 $y\le b_j$ 的行上 $\tau$ 为 $(y,E_1(\text{当前源}))$ 的函数。第二层采用 §34.3 的实际纯 $\alpha$ 执行器，首层仍保留 $r$，不得把它删成纯 $\alpha$ 增量。

**证明。** 首层宏和替换均接受后，在同一实际行上有

$$
x+y=m+2n+3d+2r=\lambda _3+3d+2r>H.
\tag{TM.3524}
$$

因此后继表认证了 §34.1 的当前上带，即当前第二次替换尺寸超过 $H$；当前可能为标签 $0$ 或 $1$。其当前读是实际已取得的 $E_1(s)k_1$，目标仍为初始 $\tau$，正满足推论 34.3 的所有配对档案条件。该推论的充要判据处理整个后继延续；若第二次替换接受，下一替换尺寸已超过 $H$，只能终端解码。首层必要性与充分性由定理 35.4 给出，故所述两层条件也是充要的。第一层中初始标签 $2$ 并未被排除。

没有 $\lambda _3>H$ 时不能直接应用这个上带推论。例如 $H=3$、实际初始源 $\alpha$ 有 $(m,n,\lambda _2,\lambda _3)=(1,1,2,3)$；第一次替换后的 $\beta$ 仍为标签 $2$，连续第三次纯替换在尺寸 $3=H$ 时接受。这不否定嵌套判据，只说明一般情况须允许更多层。$\square$

若后一阶段选择 $(d',r')$，第二次替换的准确守卫为

$$
m+n+2d+r+d'+r'\le H,
\tag{TM.3525}
$$

并且须同时满足此前实际首层拼接、首次替换和后层拼接守卫。第二窗增量为 $2d+r$；只保留首窗增量 $d$ 会遗漏它。

### 35.6 实际混合标签、端点与原始目标碰撞

**命题 35.7（实际三标签取得与等号端点）。** 取固定左结合实际词

$$
P=\alpha^3\beta,\qquad Q=\alpha\beta\alpha^2,\qquad
U=\alpha^7\beta,\qquad V=\alpha\beta^5.
\tag{TM.3526}
$$

它们的离线实际表为

$$
\begin{array}{c|ccc|ccc}
\text{来源}&m&n&\lambda _2&E_0&E_1&E_2\\ \hline
P&4&5&9&AB&A&S^5A\\
Q&4&5&9&AB&A&SA\\
U&8&9&17&AB&A&S^9A\\
V&6&11&17&AB&BS^5&S(S^2A)^5
\end{array}
\tag{TM.3527}
$$

$H=10$ 时初始标签依次为 $2,2,1,0$，全行满足 $m+2n>10$。首层截止 $c=H$ 省略上下文，首次 $\rho$ 在 $V$ 上拒绝，其余接受；第二层仍省略上下文，第二次 $\rho$ 在 $U$ 上拒绝，在 $P,Q$ 上接受，随后实际读 $S^5A$ 与 $SA$ 分开二者。一个标签因而取得显示四源族的全部原始目标。

**证明。** 组成直接给出前三列。由 $A^2=1$、$B^2=-1$、$E_1(\alpha)=B$、$E_1(\beta)=S$，前三行首读均为 $AB$，下一读分别为 $B^3S=BSB^2=B^7S=-BS=A$；$V$ 的首读为 $AB^5=AB$，下一读为 $BS^5$。字面二次替换给出 $E_2(\alpha)=S$、$E_2(\beta)=S^2A$，所以二次读正为表中乘积；$Q$ 的值化简为 $S(S^2A)S^2=SA$，不能将 $P$ 的 $S^5A$ 换成它。正规形唯一性保证 $S^5A\ne SA$。守卫分别检查 $n$ 和 $m+n$；拒绝支路与接受读支路对应表中原始目标，所有分支只依据真实记录。若需填充，最终拒绝按（TM.3519）计入。

同一 $P,Q$ 右接单叶 $\beta=K(1,1)$ 后，尺寸三项变为 $(5,7,12)$。在 $H=12$ 两次替换都接受，第二次恰等于上限；在 $H=11$ 第二次拒绝。接受后的第二窗读为原 $E_2$ 右乘已知 $SB=S^2A$。这同时检验（TM.3504）、（TM.3505）和（TM.3525）的 $2d+r=3$。$\square$

**命题 35.8（同当前 profile 不消除原始目标）。** 在 $H=9$ 取实际词 $X=\alpha^9$、$Y=\beta^2\alpha\beta^2$。它们初始首读均为 $A$，尺寸对分别为 $(9,9)$ 和 $(5,9)$，标签都为 $1$，初始 $q_9$ 不同。首次 $\rho$ 却都接受并落到同一个当前 $q_9=(0,B^9,9)$。因此这种接受后配对档案不能删去某个原始目标来声称取得。

**证明。** $E_0(Y)=B^2AB^2=A$；$E_1(Y)=S^2BS^2=B=B^9$，而 $E_1(X)=B^9$。接受后下一替换尺寸分别为 $18$、$14$，均超过 $9$，故当前标签 $0$、当前尺寸 $9$ 和当前读完全相同，原始目标仍不同。定理 30.2 排除共同记录下的进一步恢复。$\square$

### 35.7 批量守卫不能串行化为单叶守卫

**命题 35.9（原始第三窗被部分接受销毁的反例）。** 在 $H=10$ 使用命题 35.7 的 $P,Q$。原动作一次尝试右接实际 $\alpha^7$，因 $4+7=11>10$ 在二者上均拒绝，保持原源；随后两次实际 $\rho$ 和当前读仍能取得各自原始 $q_{10}$。若把这一批量动作改成依次右接七个单叶 $\alpha$ 并在首次拒绝时停止，则第一次接受已经永久合并两个不同初始目标。

**证明。** 初始两个目标有共同 $E_0=AB$、$E_1=A$、组成 $(3,1)$，第三窗分别为 $S^5A$、$SA$。原批量拒绝不产生候选读，不改任一窗口；随后两次替换候选尺寸为 $5,9\le10$，实际读第三窗即分离。

串行化的第一单叶在二者上均接受；当前组成为 $(4,1)$，尺寸为

$$
(\lambda _0,\lambda _1,\lambda _2)=(5,6,11),\qquad
E_0=(AB)A,\qquad E_1=AB.
\tag{TM.3528}
$$

所以两个当前源已为同一标签 $1$ 的 $q_{10}$，共同真实记录也相同。原始第三窗虽在完整数学 $\eta$ 中仍有不同值，在固定上限合同内却再不可取得；定理 30.2 禁止以后分开原始目标。故模拟宏的守卫必须作为一次原子拼接，不能用会部分修改来源的单叶探测替代。引理 35.2 只在宏已经接受的选定叶上核对原前缀中间接受合法性，并不赋予串行化一个被拒宏的权限。$\square$

### 35.8 复用关系与证明范围

单出现不变量、Clifford 正规形、三窗运输、固定行为商和填充取得分别复用 §§28–31；实际像条件复用原子卷 §§359.3、360.2。这里的结构结论是整个无替换自适应阶段的有序截止压缩、准确双增量保留、完整确定性记录运输，以及在同一实际原树上取得初始 $q_H$ 的有限嵌套充要条件。$\lambda _3>H$ 时只追加首层双增量条件，再由 §34.3 供应第二层，未重复其上带分类或 β 必要性的四源定理。

初态识别与自适应完整迹的成熟方法范围沿用 §31.7 的主文献：Panteleev 的 [arXiv:1412.0034v1](https://arxiv.org/pdf/1412.0034v1) 及 van den Bos–Vaandrager 的 [arXiv:1907.11034v2](https://arxiv.org/pdf/1907.11034v2)。它们只供应识别语义和合并障碍的方法，未供应本节双资源锥、实际宏实现或嵌套截止定理。

以上结论有普通数学证明，不构成 Lean 内核核验。完整 $\eta$ 离线认证不增加运行时观察接口；原树地址历史的恢复定理和不同来源的 k-bonacci 取得定理不导出这里的 $E$ 单端口能力。深度界 $J_H$ 允许两次以上接受替换；两层结论只在已证 $\lambda _3>H$ 条件内成立。调用界仅为存在性上界；最少调用、表与标签的取得成本、总记忆、原树括号和物理空间时间恢复，以及全家族标签分割优化均在本节证明范围之外。

## 35.99 追加锚
## 36. 实际档案纤维的无缺口几何、下中位关系与首次全家族容量分离

本节保持 §§30–35 的固定公开整数 $H$、实际非空有序自由括号化 $\alpha/\beta$ 原树、当前 $E$ 读口、受活叶上限守卫的 $\rho$ 和左右正上下文拼接。拒绝保持来源且不返回候选读数；目标始终是同一初始来源的 $q_H$。复用原子卷 [§§359–360](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的联合正规形与 Euler 来源判据，以及本卷的相位、$\Gamma_H$、F/R 执行器和原始目标配对规则。下文 $j$ 是 $q_H$ 的层标签，$h$ 是另行供应的补充标签，两者不同。

### 36.1 全尺度实际纤维的整数区间

**约定 36.1（实际目标与档案坐标）。** 记 $Q_H=q_H(\mathcal T_H)$，并写初始组成为 $(a,b)$、$m=a+b$、$n=a+2b$、$\ell=2a+3b=m+n$。定理 31.3 使 $\Gamma_H$ 在 $Q_H$ 上成为良定义的函数：

$$
\Gamma_H(q)=
\begin{cases}
(0,E_0,m),&j=0,\\
(1,E_0,E_1,n),&j=1,\\
(2,E_0,E_1,E_2,\ell),&j=2.
\end{cases}
\tag{TM.3601}
$$

这里的右侧是数学上的初始坐标；运行时只能按定义 31.2 实际取得该档案。$\Gamma_H$ 与 $m$ 共同决定初始目标：层标签1时 $(a,b)=(2m-n,n-m)$，层标签2时 $(a,b)=(3m-\ell,\ell-2m)$。层标签0的档案已经等于其目标。

**引理 36.2（全部实际 $\Gamma_H$ 纤维无缺口）。** 对每个 $H\ge1$ 和每个非空实际档案纤维，存在整数 $m_-\ge1$、$R\ge0$，使其初始目标尺寸恰为

$$
\{m_-+4r:0\le r\le R\},
\tag{TM.3602}
$$

每个尺寸恰对应一个目标。层标签0的纤维为单点。这是实际来源像的结论，不能仅由非负流量或环境格点推出。

证明。唯一目标性由约定 36.1 给出。非零层的共同 $E_1$ 通过引理 29.5 的字符确定 $m\bmod4$，所以不同尺寸之差是四的倍数。以下证明任意两个实际端点间的每个允许格点都有实际来源。

先取层标签1纤维。固定 $E_0,E_1$ 后，原子卷（359.2）–（359.3）确定 $p,q,u,v$ 和 $w\bmod2$：$p$ 是 $E_1$ 的等级，$q$ 是 $E_0$ 与 $E_1$ 等级之和模二。取两个实际端点，按 $\beta$ 数排序为

$$
 b_1=b_0+4r,\qquad a_1=a_0-8r,\qquad r\ge1,
\tag{TM.3603}
$$

因为它们的 $n=a+2b$ 相同。分别选实际三窗延拓，较大 $b$ 的端点参数记为 $(u,v,w_1,p,q)$。使用原子卷（360.1）的

$$
 X_1=\frac{a_1-p-2w_1+2u}{4}.
$$

对 $0<k<r$ 取组成 $(a_0-8k,b_0+4k)$，并选 $X=X_1$、$w=w_1+4(r-k)$。$Y=(b-q-2u+2v)/4$ 比较小 $b$ 端点的 $Y$ 增加 $k$。以原子卷（360.2）的下标顺序写 $\mathbf x=(x_{00},x_{10},x_{01},x_{11})$、$\mathbf y=(y_{00},y_{01},y_{10},y_{11})$，所得八边证书为

$$
\mathbf x(k)=\mathbf x_1+(4(r-k),4(r-k),0,0),\qquad
\mathbf y(k)=\mathbf y_0+(k,k,k,k).
\tag{TM.3604}
$$

所有边数为非负整数；四条 $\beta$ 边和 $x_{00},x_{10}$ 都严格为正。两组 $\beta$ 边分别连接 $00,01$ 与 $10,11$，而 $x_{00},x_{10}$ 把这两组接通，故整个正支撑包含起点 $00$ 且弱连通。组成公式与顶点流量正是原子卷定理 360.2 的公式；$w$ 的变化保持其模二值，所以前两窗不变。该定理给出同一档案的实际正叶词。中间 $m$ 介于两实际端点之间，故仍满足 $m\le H$、$n\le H<m+n$，不会改变层标签。端点本身已有实际来源。

再取层标签2纤维。其完整 $W_3$ 和 $\ell$ 固定；同一 $W_3$ 的组成模四相同，联立 $2\Delta a+3\Delta b=0$ 得到

$$
(\Delta a,\Delta b)=(12r,-8r),\qquad \Delta m=4r.
\tag{TM.3605}
$$

所有正规参数 $(u,v,w,p,q)$ 固定。在整数中间点 $k=0,\ldots,r$，$X=X_0+3k$、$Y=Y_0-2k$，因此

$$
\mathbf x(k)=\mathbf x_0+(3k,3k,3k,3k),\qquad
\mathbf y(k)=\mathbf y_0-(2k,2k,2k,2k).
\tag{TM.3606}
$$

这些数也是两端点边数的仿射插值，故均为非负整数。严格中间点的正支撑恰为两个实际端点正支撑的并；两端点各自弱连通且都包含 $00$，故这个并弱连通。原子卷定理 360.2 再给出实际来源，且 $\ell\le H$ 保证它仍为层标签2。这证明所有四步格点都被实际填满。$\square$

### 36.2 层标签2的尖锐全尺度固定档案残余

**定理 36.3（层标签2的精确最大纤维）。** $H=1$ 没有层标签2来源。对每个整数 $H\ge2$，在全部实际层标签2来源上，最大 $\Gamma_H$ 目标纤维大小为

$$
D_2(H)=1+\left\lfloor\frac{\max(H-5,0)}{24}\right\rfloor.
\tag{TM.3607}
$$

它也是保持固定 $\Gamma_H$ 执行、仅补充解码时的最小标签字母表大小；此结论不评价一般自适应取得容量 $M_A(H)$。

证明。若一个纤维含 $f\ge2$ 个目标，取其最小、最大 $m$ 的实际端点，写成（TM.3605），则 $r\ge f-1$。在较小 $a$ 的端点，四条 $\beta$ 边都比另一端点多 $2r$，故全部为正。这些边占据两个互不相接的 $\beta$ 二边回路，实际弱连通性迫使至少一条 $\alpha$ 边为正，即 $a_0\ge1$。在较大 $a$ 的端点，四条 $\alpha$ 边全部为正，实际连通性同样迫使 $b_1\ge1$。因此 $b_0=b_1+8r\ge1+8r$，从而

$$
H\ge\ell=2a_0+3b_0\ge5+24r\ge5+24(f-1).
\tag{TM.3608}
$$

这给出（TM.3607）的上界，包括 $2\le H\le4$ 时只能有单点的情况。

为证明尖锐性，对任意 $r\ge0$、$0\le i\le r$，指定同一个实际三窗 $\Omega=R_{11}=(-S^{-1},-A,S^3A)$ 和组成

$$
(a_i,b_i)=(1+12i,\ 1+8(r-i)),\qquad
\ell_i=5+24r,\qquad m_i=2+8r+4i.
\tag{TM.3609}
$$

其正规参数为 $u=v=w=0,p=q=1$。原子卷（360.1）给 $X=3i$、$Y=2(r-i)$，八条边的实际证书恰为

$$
\mathbf x=(X+1,X,X,X),\qquad
\mathbf y=(Y,Y,Y+1,Y).
\tag{TM.3610}
$$

边数非负、总组成与（TM.3609）相同，起终点为 $00,11$。若 $0<i<r$，全部边都为正。若 $i=0<r$，四条 $\beta$ 边与唯一的 $\alpha$ 边 $00\to10$ 接通四顶点；若 $i=r>0$，四条 $\alpha$ 边与唯一的 $\beta$ 边 $10\to11$ 接通四顶点。$r=0$ 时支撑就是 $00\xrightarrow{\alpha}10\xrightarrow{\beta}11$。所以每个端点和中间点都满足完整 Euler 判据。取这些有向多重图的任意 Euler 路并给其正叶词任意固定有序括号，得到一族实际原树，而非仅有形式组成的候选。

对 $H\ge5$ 取 $r=\lfloor(H-5)/24\rfloor$，这 $r+1$ 个来源都是层标签2，共同档案为 $(2,-S^{-1},-A,S^3A,5+24r)$，初始组成两两不同。对 $2\le H\le4$，单叶 $\alpha$ 是层标签2，给出所需单点。$H=1$ 则因 $\ell\ge2$ 无此层。固定档案解码必须在一个目标纤维上供应不同标签；反过来，对每个有限实际纤维编号就能使用其最大大小的字母表解码，这是 §32 的既有静态纤维计数关系。故两种数值相等。$\square$

**推论 36.4（正标签模数的精确阈值）。** 对整数 $H\ge2$、$L\ge1$，既有标签 $\sigma_L=\lfloor m/4\rfloor\bmod L$ 在层标签2的固定 $\Gamma_H$ 解码任务上成功，当且仅当

$$
H\le24L+4.
\tag{TM.3611}
$$

特别地，$\Gamma_H$ 在层标签2的实际目标像上单射当且仅当 $2\le H\le28$。$H=1$ 的空层没有需要区别的目标。

证明。引理 36.2 给每个纤维连续的四步尺寸，故 $\lfloor m/4\rfloor$ 是连续整数；若（TM.3611）成立，定理 36.3 给 $D_2(H)\le L$，连续至多 $L$ 个整数的模 $L$ 值互异。若 $H\ge24L+5$，在（TM.3609）取 $r=L$，首末两目标尺寸相差 $4L$，$\sigma_L$ 相同而目标不同，否定解码。取 $L=1$ 即得28的边界。

在边界 $H=29$，两个字面实际词可以取

$$
U=\beta^4\alpha\beta^5,\qquad
V=\alpha^7\beta\alpha^6.
\tag{TM.3612}
$$

它们的组成分别是 $(1,9),(13,1)$；逐叶相乘给同一个 $R_{11}$，且 $\ell=29$。任何 $H\ge29$ 都使它们的层标签为2且 $\Gamma_H$ 相同，但初始 $q_H$ 不同。这个反例限制的是原固定档案；它不排除改变自适应动作或供应别的关系。$\square$

### 36.3 三目标档案列的穷尽分类

**引理 36.5（实际词的两个指数恒等式）。** 对任意实际正叶词，把第 $j$ 个 $\beta$ 前的 $\alpha$ 数记为 $A_j$，置 $s_j=(-1)^{A_j}$、$\varepsilon=a\bmod2$。则

$$
k_0=\sum_{j=1}^{b}(-1)^{j-1}s_j,\qquad
k_1=\varepsilon+\sum_{j=1}^{b}s_j,\qquad
|k_1-\varepsilon|\le b.
\tag{TM.3613}
$$

同时实际相位给 $b\equiv2e_0+k_0\pmod4$、$m\equiv2e_1+k_1\pmod4$。

证明。按（28.3）右乘初始叶原子时，每片 $\alpha$ 的指数贡献为零，第 $j$ 片 $\beta$ 的贡献是 $(-1)^{A_j+j-1}$，得到第一式。在第一替换窗口中，原 $\alpha$ 贡献 $B$，原 $\beta$ 贡献 $S$；只有原 $\alpha$ 改变该窗口的当前等级。因此原 $\alpha$ 的带符号贡献交替相消，和为 $\varepsilon$，每个原 $\beta$ 的贡献为 $s_j$，得到第二式及其界。相位同余直接使用引理 29.5。$\square$

**定理 36.6（$17\le H\le20$ 的全部三目标列）。** 固定 $17\le H\le20$。层标签0、2的实际档案纤维均为单点；层标签1的每个档案纤维至多有三个目标。三个目标的全部列恰由下表给出，其中 $g=E_0$，$z=E_1$ 的完整值由所列 $k_1$ 与任一所列尺寸恢复为

$$
z=N\left(\left(\frac{m-k_1}{2}\right)\bmod2,\ k_1,\ n\bmod2\right).
\tag{TM.3614}
$$

| TM36列型与范围 | $g$ | $k_1$ | 初始尺寸（递增） |
|---|---|---|---|
| TM36中央列：$17\le n\le H$ | $N(0,0,n\bmod2)$ | $n\bmod2$ | $n-8,n-4,n$ |
| TM36正侧列：$n=19\le H$ | $N(0,1,0)$ | $2$ | $10,14,18$ |
| TM36负侧列：$n=19\le H$ | $N(1,-1,0)$ | $0$ | $10,14,18$ |
| TM36正延续列：$n=20=H$ | $N(0,1,1)$ | $1$ | $11,15,19$ |
| TM36负延续列：$n=20=H$ | $N(1,-1,1)$ | $-1$ | $11,15,19$ |

证明。层标签0已由档案决定；层标签2的单点性由定理 36.3 给出。层标签1固定 $n\le H\le20$ 且 $\lceil n/2\rceil\le m\le n$，直径至多10，同一列的 $m$ 同余模四，故至多三个；有三个时必为 $m_*-8,m_*-4,m_*$。

设最大尺寸目标的 $\beta$ 数为 $b_*=n-m_*$，最小尺寸目标的 $\alpha$ 数为 $n-2b_*-16\ge0$。因此 $n\ge16$、$b_*\le2$。

若 $b_*=0$，最大词是纯 $\alpha^n$，列为 $g=A^n,z=B^n$。$n=16$ 时最小词是纯 $\beta^8$，其 $k_1=8$，不能等于最大词的 $k_1=0$。剩下 $17\le n\le H$ 恰是中央列。

若 $b_*=1$，则 $n\in\{18,19,20\}$。$n=18$ 时最小词是纯 $\beta^9$，其 $k_1=9$；最大一 $\beta$ 词由（TM.3613）有 $|k_1|\le1$，排除。$n=19$ 时最小词为 $\beta^j\alpha\beta^{9-j}$，给 $k_1=2j-8$。最大词有十七片 $\alpha$ 和一片 $\beta$，故 $k_1\in\{0,2\}$，迫使 $j=4$ 或5。前者给 $(k_0,k_1)=(-1,0)$，后者给 $(1,2)$；相位给表中的两个 $n=19$ 列。

$n=20$ 时最小词为 $\beta^r\alpha\beta^v\alpha\beta^s$，其中 $r+v+s=9$。两个 $\alpha$ 之间的 $v$ 片 $\beta$ 贡献负号，所以 $k_1=9-2v$。最大词有十八片 $\alpha$ 和一片 $\beta$，不仅要求 $k_1\in\{-1,1\}$，也要求 $|k_0|\le1$。前一条件给 $v=4$ 或5。当 $v=4$ 时交替和给 $k_0=1$；当 $v=5$ 时

$$
k_0=1-2(-1)^r\in\{-1,3\}.
\tag{TM.3615}
$$

必须再用最大一 $\beta$ 来源的 $|k_0|\le1$ 排除3，才得到 $(k_0,k_1)=(-1,-1)$。因此 $v=5$ 本身不蕴含 $k_0=-1$。实际相位把 $(1,1)$ 与 $(-1,-1)$ 分别变成表中的两个 $n=20$ 列。

若 $b_*=2$，则只有 $n=20$，最小词是纯 $\beta^{10}$，其 $k_1=10$；最大词有十六片 $\alpha$ 和两片 $\beta$，满足 $|k_1|\le2$，排除。上述分类穷尽全部可能性。

每个保留列确有三个实际来源。中央列对 $j=0,1,2$ 取

$$
\beta^{2j}\alpha\beta^{2j}\alpha^{n-8j-1}.
\tag{TM.3616}
$$

两个 $n=19$ 列分别取

$$
\beta^{2j+1}\alpha\beta^{2j}\alpha^{16-8j},\qquad
\beta^{2j}\alpha\beta^{2j+1}\alpha^{16-8j}.
\tag{TM.3617}
$$

给这些词右接一片 $\alpha$，得到对应 $n=20$ 列。所有指数非负，省略零块仍保留中间 $\alpha$，故均为非空实际来源。组成计数给表中尺寸；第一窗用 $B^2=-1$ 相乘，第二窗用 $BS^t=(-1)^tS^{-t}B$ 相乘，给所列 $g,k_1$；（TM.3614）给完整 $z$。每个目标满足 $n\le H<m+n$，所以确属该层。不同括号不改变这两窗，但原树括号仍保留。$\square$

### 36.4 下中位补充关系与解析截止

**定义 36.7（下中位关系、Top 与 Low）。** 对固定 $17\le H\le20$，在每个实际层标签1的 $\Gamma_H$ 列中，将初始尺寸排序为 $m_1<\cdots<m_r$，仅给下中位目标 $m_{1+\lfloor(r-1)/2\rfloor}$ 补充标签 $h_H=0$，其余给 $h_H=1$。全部层标签0、2目标也给 $h_H=0$。这是初始 $q_H$ 的函数，由同一未修改的初始来源供应。

由定理 36.6，$h_H=1$ 恰含两种目标：每个重复列的最大尺寸目标称 Top，每个三目标列的最小尺寸目标称 Low。每列至多一个 Top；Low 只出现于表36.6。

对已实际读出的 $g=N(e,k,p)$ 定义公开截止

$$
c_H(g)=
\begin{cases}
H-8-((H-p)\bmod2),&(e,k)=(0,0),\ H\ge18-p,\\
10+p,&(e,k)\in\{(0,1),(1,-1)\},\ H\ge19+p,\\
0,&\text{其余情形}.
\end{cases}
\tag{TM.3618}
$$

这里模二取标准代表；三个情形互斥，正截止均满足 $0<c_H(g)<H$。其定义域仅为 $17\le H\le20$。

**引理 36.8（截止精确分离补充标签1的两个极端）。** 在 $h_H=1$ 的实际来源上，$m\le c_H(g)$ 当且仅当来源属于 Low。在每个固定 $g$ 中，Low 上 $m$ 单射，Top 上 $(n,E_1)$ 单射。若 $c_H(g)=0$，该 $g$ 纤维只有 Top。

证明。表36.6的中央 Low 尺寸为 $n-8$，$n$ 与 $p$ 同奇偶；第一行截止就是其中最大者。其余四列的 Low 尺寸是 $10+p$，恰为第二行截止。每个固定 $g$ 的这些 Low 尺寸互异；同列的 Top 尺寸至少17，均超过最大截止12。没有列于表中的 $g$ 不含 Low。

还须排除两目标列的 Top 落在截止下。反设某 Top 的 $m\le c=c_H(g)>0$；它的同列另有实际尺寸 $m'\le m-4$，故

$$
n\le2m'\le2m-8,\qquad a=2m-n\ge8,\qquad b=n-m\le m-8.
\tag{TM.3619}
$$

若 $g=N(0,0,p)$，实际相位迫使 $b\equiv0\pmod4$。因 $c\le12$，只有 $b=0$ 或4。$b=0$ 时 $n=m$，于是 $m'+n\le2c-4\le H$，与另一目标的层标签1条件矛盾。$b=4$ 时（TM.3619）迫使 $m\ge12$，故只能是 $H=20,c=m=12,n=16$；另一目标必有 $m'=8$，即纯 $\beta^8$，给 $k_1=8$，而 Top 的 $(a,b)=(8,4)$ 由（TM.3613）给 $|k_1|\le4$，又矛盾。

在另外四个正截止纤维，$g=N(0,1,p)$ 或 $N(1,-1,p)$，相位迫使 $b\equiv1\pmod4$。由 $c\le11$ 和（TM.3619）只能有 $b=1$，因而 $n=m+1$、$m'+n\le2c-3\le H$，仍与层标签1矛盾。故任何 Top 都超过截止。最后每个 $(g,E_1,n)$ 列只有一个 Top，给出所需单射性。$\square$

### 36.5 初始目标的字面执行与容量

**定理 36.9（全实际家族 $17\le H\le20$ 的精确容量）。** 在合同 A 中供应定义 36.7 的同初始来源标签 $h_H\in\{0,1\}$，并给定共同公开的认证实际解码表和所用正上下文，存在一个确定性记录控制协议，在全部 $\mathcal T_H$ 上有限停止、返回初始 $q_H$，使用至多 $H+4$ 次来源调用。因此

$$
M_A(H)=2<3=M_B(H),\qquad17\le H\le20.
\tag{TM.3620}
$$

证明。先真实读取当前 $E_0=g$。若 $h_H=0$，从这份已保存首读继续定义 31.2 的 $\Gamma_H$ 执行，不重复首读。每个实际档案恰留一个补充标签0目标，故其实际解码表返回该初始目标。

若 $h_H=1$，来源必为初始层标签1。计算（TM.3618）的 $c$。$c=0$ 时直接使用既有 R 执行器：尝试一次 $\rho$，它因初始 $n\le H$ 接受；随后真实读 $E$，保存为初始 $E_1=z$；右接单叶 $\alpha$ 填至首次拒绝，记成功次数 $s$，得到 $n=H-s$。由引理 36.8，此时只可能是其 $(g,z,n)$ 列的 Top，查原始配对表输出该初始 $q_H$。

$c>0$ 时先尝试一次受守卫的实际右上下文 $\alpha^{H-c}$。这是一条正上下文动作，不能拆成逐叶部分接受的探测。接受当且仅当初始 $m\le c$，由引理 36.8 恰选出 Low；当前叶数为 $m+H-c$。继续单叶填充到首次拒绝，成功次数给 $m=c-s$；Low 上 $(g,m)$ 唯一，故原始表返回它的完整初始目标，包括未在此分支读取的初始第二窗。宏动作拒绝时来源不变且无候选读数；此时恰是 Top，随后运行同一个 R 分支并解码初始目标。

这些动作就是 §§31、34 的合法执行器。所有填充都包含最后一次拒绝，特别是 $s=0$ 的端点；不再读取填充后的来源来冒充初始窗。补充标签0分支由定理 31.6 用至多 $H+4$ 次调用。其余分支的调用数，含共同首读，为

$$
\begin{array}{ll}
H-n+4,&\text{无截止 R},\\
H-n+5,&\text{宏拒绝后 R},\\
c-m+3,&\text{宏接受后 F}.
\end{array}
\tag{TM.3621}
$$

它们均不超过 $H+4$。所有分支有限停止并返回原始表中的初始目标。这个显示协议的单叶初始 $\alpha$ 位于层标签2、补充标签0，$\lambda_2=2$，实际使用 $H-2+6=H+4$ 次调用；这里只说明该协议达到其界，不主张调用最优。

上界覆盖全家族，包括纯 $\alpha$、纯 $\beta$ 和全部有序括号；定理 31.4 对所有允许左右上下文与完整档案排除 $H\ge9$ 的单标签协议，故 $M_A(H)=2$。$M_B(H)=\lceil H/8\rceil=3$ 直接复用定理 32.4。定理 32.6 已给 $H\le8$ 的两容量均为1、$9\le H\le16$ 均为2，故17是整个实际家族首次严格分离的上限。这里比较的是补充字母表，不是总记忆、总时间或标签生产费用。$\square$

### 36.6 同源供应的取得边界与下一尺度障碍

**命题 36.10（保持原树的运行不能生产该补充位）。** 固定 $H$。一个来源无关初始化的确定性有限 TM30 程序，若在每个输入上结束时仍是精确的初始原树，则其输出只能是初始 $E_0$ 的函数。对 $17\le H\le20$，这种程序不能生产 $h_H$；该位甚至不是固定取得档案 $\Gamma_H$ 的函数。

证明。任何接受的正上下文严格增加叶数；接受的 $\rho$ 在存在 $\beta$ 时也严格增加叶数。叶数从不下降。若来源只有 $\alpha$，一次接受的 $\rho$ 虽不增加叶数，却变为全 $\beta$ 原树；此后若再接受修改，叶数严格增加。因此任何接受修改都不可能回到精确初始原树。满足命题条件的运行不能含接受修改，只能读取不变的 $E_0$ 和收到拒绝。对同一 $E_0$ 纤维按确定控制归纳，动作、响应和输出相同，故输出因子化经过 $E_0$。

对每个 $17\le H\le20$ 取实际词

$$
X_H=\beta^2\alpha\beta^2\alpha^{H-9},\qquad Y_H=\alpha^H.
\tag{TM.3622}
$$

它们共同 $E_0=A^H$、共同 $\Gamma_H=(1,A^H,B^H,H)$；定理 36.6 的中央列恰有尺寸 $H-8,H-4,H$，其中 $X_H$ 是中间目标、$Y_H$ 是最大目标。因此 $h_H(X_H)=0$、$h_H(Y_H)=1$，排除经过 $E_0$ 或 $\Gamma_H$ 的因子化。$\square$

**命题 36.11（$H=21$ 的下中位扩展障碍）。** 将定义 36.7 的列内下中位选择继续用于 $H=21$，不能仅凭该两值标签取得全部初始目标，且不能通过改变它的同标签后续控制来修复。实际三源证书为

$$
u=\beta^4\alpha\beta^6,\qquad
v=\beta^6\alpha\beta^4,\qquad
w=\alpha\beta^2\alpha^{16}.
\tag{TM.3623}
$$

证明。三个来源的 $n$ 均为21，首窗均为 $-A$；尺寸分别为 $11,11,19$。下一窗依次为

$$
z_-=S^{-2}B,\qquad z_+=S^2B,\qquad z_-.
\tag{TM.3624}
$$

两个列的实际尺寸都恰为 $11,15,19$：中间来源分别可取 $\beta^2\alpha\beta^4\alpha^8$、$\beta^4\alpha\beta^2\alpha^8$；最大来源分别是 $w$、$\beta^2\alpha^{17}$。组成与相位排除其他尺寸，因为 $\lceil21/2\rceil\le m\le21$ 且 $m\equiv11\pmod4$。故 $u,v,w$ 都取得补充标签1，而三个初始目标不同。

共同只读或处处拒绝的动作不能区分三者，有限正确协议必须出现首次有效修改。若是 $\rho$，三者都接受并变为当前层标签0、尺寸21，$u,w$ 的当前 $E$ 都为 $z_-$，因此同记录同当前 $q_{21}$ 合并。如果是叶数 $d\le10$ 的任意正上下文，无论左右，$u,v$ 都接受；其新首替换叶数为 $21+d_1>21$，当前层标签0、尺寸 $11+d$ 和当前读数相同，故合并。$d>10$ 时三者都拒绝，不是有效修改。两个可能首修改都由定理 30.2 永久丢失不同初始目标，否定所有同标签协议。定理 33.6 已独立给出全家族 $M_A(H)=3$ 于 $21\le H\le24$；这里的三源证书说明本选择不能原样延伸，不代替那个全家族下界。$\square$

### 36.7 恢复关系与开放范围

下中位关系决定哪一部分初始区别能交给固定时间窗口档案，哪一部分必须先由正上下文的容量截止保留。引理 36.2 和定理 36.3 把这种边界接到共同实际 Euler 来源及其组成；无缺口几何只说明单个档案纤维的结构，不保证跨不同列的不可逆动作相容。一般 $H$ 的精确 $M_A(H)$ 仍须对整个实际 $Q_H$ 寻找满足定理 35.4 嵌套原始目标证书的最小标签分割，并给出针对全部允许动作的匹配下界；最大 $\Gamma_H$ 纤维大小、逐对可区分性或普通静态着色不能替代这项优化。

补充位在首次来源动作前从同一未修改的初始来源供应；实际解码表、认证数据及所用正上下文是共同公开的供应或构造接口。补充位的离线定义使用 $m,n$ 或档案列，不把这些坐标变成运行时端口。在线分支只使用该位、公开 $H$、真实 $E$ 读和已取得的守卫／计数记录。标签生产、同源认证、传输与保留，表和上下文的构造，坐标转换、精确算术、输出及全部存储分别计费。命题 36.10 排除了免费保持原树的生产方式；先取得 $\Gamma_H$ 再复位并不属于合同。

本节是基于上述仓内供应定理的普通数学推导。来源调用最优、总记忆和生产费用、一般尺度自适应最优，以及原树括号、叶地址、绝对时间和物理空间的恢复仍未由这些结论确定。层标签2固定档案的24步阈值不提升为全家族自适应最优公式。

## 追加锚（本行以下为增补区）

## 37. 全实际家族的尖锐首项容量与无界次线性节省

### 37.1 初始目标与共同动作强制的行列关系

**约定 37.1（全家族容量与记号）。** 来源、读口和全部允许动作取 §§30–36 的固定合同；共同公开整数 $H\ge1$，目标始终为同一未修改初始来源的 $q_H(t)$。沿用定义 32.2 的 $M_A(H),M_B(H)$，约定 36.1 的 $Q_H,\Gamma_H$，以及初始坐标

$$
m=a+b,\qquad n=a+2b,\qquad E_0=g,\qquad E_1=z,
\qquad K=\left\lceil\frac H8\right\rceil.
\tag{TM.3701}
$$

层标签1的目标由 $(g,m,n,z)$ 决定，其实际档案列由 $(1,g,z,n)$ 决定。一个固定 $g$ 下的行指初始尺寸 $m$ 相同的目标集，列指初始 $(n,z)$ 相同的目标集。层标签始终写作 $j$；$\eta\in\{0,1\}$ 仅表示下文公开的半块位置，不是层标签。下界中的 $L$ 表示任意已供应字母表的大小；上界中的 $J$ 表示档案分支标签数，避免混用。

合同 A 对任意 $h:\mathcal T_H\to\mathcal L$ 取最小值，不要求它通过 $q_H$ 分解。以下必要条件也允许这种来源相关标签；构造的标签则明确是初始 $q_H$ 的函数。所有协议共同初始化、确定性，并在每个实际输入上有限停止，允许任意大的已取得记录。

**定理 37.2（全部正上下文下的首次替换行列限制）。** 固定一个有限的实际层标签1目标集，所有目标具有同一个初始 $E_0=g$，并为每个目标选择一棵实际代表原树。设一个成功的合同 A 协议在这些代表上取得初始目标。对任一共享补充标签类，按各代表的实际运行将其分为：

- $P$：停止前没有尝试 $\rho$，或首次尝试 $\rho$ 被拒绝；
- $C$：首次尝试 $\rho$ 被接受。

则 $P$ 在每个初始尺寸行中至多含一个目标；$C$ 在每个初始档案列中至多含一个目标。更强地，某列中的 $C$ 成员必须是该标签类在此列中的最大尺寸成员。本结论包括任意含 $\beta$ 的实际正上下文、左右拼接、穿插读数和被拒绝探测。

证明。首次 $\rho$ 之前，复用引理 30.1 的单出现不变量，当前来源含未知原树恰一次，其余是已知正上下文。若沿一个共同记录前缀累计接受的上下文在前两窗增加尺寸 $D_0,D_1$，则

$$
0\le D_0\le D_1,
\qquad \lambda_0^{\mathrm{cur}}=m+D_0,
\qquad \lambda_1^{\mathrm{cur}}=n+D_1.
\tag{TM.3702}
$$

当前首读是按实际左右顺序相乘的 $L_0gR_0$，两个外因子已知且可逆。此前每个拼接守卫只依赖 $m$ 和该前缀已知的尺寸增量。因此同标签、同 $m$ 的成员在停止或首次 $\rho$ 之前有相同完整记录和控制选择。若停止而不尝试 $\rho$，它们输出相同。若其中两个首次 $\rho$ 都拒绝，则二者的当前层标签都是0、当前尺寸同为 $m+D_0$、当前 $E$ 同为 $L_0gR_0$。它们拥有相同完整记录及相同当前 $q_H$。定理 30.2 使该合并在每个共同后续控制下永久保持，不能恢复两个不同初始目标。这证明 $P$ 的行限制。

再取同标签、同列的两个目标，初始尺寸 $m_1<m_2$，共同第一替换尺寸为 $n$，共同第一未来窗为 $z$。假设较小者的首次 $\rho$ 接受，沿它的真实前缀累计增量记为 $D_0,D_1$，故 $n+D_1\le H$。证明较大者逐步跟随完全相同的前缀。一个被较小者接受的上下文前缀，其累计增量 $U_0,U_1$ 满足 $U_0\le U_1\le D_1$，而实际组成保证 $m_2\le n$，所以

$$
m_2+U_0\le n+U_0\le n+D_1\le H.
\tag{TM.3703}
$$

它也被较大者接受。一个被较小者拒绝的上下文，在较大者上也拒绝，因为此前增量相同且 $m_2>m_1$。所有穿插读都是相同已知因子包围 $g$。对动作数归纳，确定性控制因而获得相同的完整首次替换前记录。两者随后都接受首次 $\rho$，新尺寸同为 $n+D_1$，新首读同为 $L_1zR_1$。两者初始都在层标签1，故各自 $m_i+n>H$；新来源的下一替换尺寸为 $m_i+n+D_0+D_1>H$。它们于是再次具有相同当前层标签0的 $q_H$ 和相同完整记录，而初始目标不同，违反定理 30.2。因此存在较大同列成员时，较小成员不能属于 $C$。同列、同 $m$ 本来就只有一个目标，故 $C$ 的列单射性也成立。证明始终保留初始目标，没有把当前行为商当作恢复目标。$\square$

### 37.2 混合首替换尺寸的实际三角来源与全协议下界

**定理 37.3（混合列的正词及完整 Euler 证书）。** 对整数

$$
0\le i\le K-1,\qquad 0\le s\le i,\qquad |r|\le i-s,
\qquad k=i-s,
$$

置

$$
a=H-8i+4s,\qquad b=4k,
\qquad
W_{i,s,r}=\beta^{2(k+r)}\alpha\beta^{2(k-r)}\alpha^{a-1}.
\tag{TM.3704}
$$

省略零次子块，给整个非空叶词取固定左结合括号。它是实际层标签1来源，且

$$
\begin{aligned}
m&=H-4i,&n&=H-4s,\\
E_0&=A^H,&E_1&=S^{4r}B^H,&E_2&=S^a.
\end{aligned}
\tag{TM.3705}
$$

这些初始目标两两不同。其行 $i$ 含 $(i+1)^2$ 个目标；列以 $(s,r)$ 编号，令 $d=s+|r|$，则该列的行恰为 $i=d,\ldots,K-1$，高度为 $K-d$。对每个 $d=0,\ldots,K-1$，高度 $K-d$ 的列恰有 $2d+1$ 个。

证明。由 $8(K-1)\le H-1$，有 $a\ge1$，且 $k\pm r\ge0$，所以（TM.3704）不是空来源。数叶即得 $m=a+b=H-4i$、$n=a+2b=H-4s\le H$。又

$$
m+n=2H-4(i+s)>H,
$$

因为 $4(i+s)\le8(K-1)\le H-1$。故层标签恰为1，包括 $k=0$ 的纯 $\alpha$ 边界。

给出同一来源的八边证书。使用[原子卷定义 360.1、定理 360.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的边顺序，置 $\varepsilon=a\bmod2$、$w=\lfloor a/2\rfloor$。终点为 $(p,q)=(\varepsilon,0)$，参数为

$$
u=0,\qquad v=2r,\qquad X=0,\qquad Y=k+r,
$$

八个边重数为

$$
\mathbf x=(w+\varepsilon,w,0,0),\qquad
\mathbf y=(k+r,k+r,k-r,k-r).
\tag{TM.3706}
$$

所有边重数非负，$x_{00}>0$；它连接 $00$ 与 $10$。若某个 $\beta$ 二边回路存在，它分别接在 $00$ 或 $10$ 上，故全部正支撑与起点 $00$ 弱连通。边和是 $(a,b)$，出入差是从 $00$ 到 $(\varepsilon,0)$，且参数满足原子卷（360.1）–（360.2）的全部方程。所写叶词正沿此路径：在 $p=0$ 处经过偶数片 $\beta$，经过一片 $\alpha$，在 $p=1$ 处经过偶数片 $\beta$，最后走余下的 $\alpha$。因此它不仅是形式组成候选，而是认证的实际正 Euler 来源。

原子卷引理 359.2、定理 359.3 对该证书给出

$$
E_0=A^\varepsilon,\qquad
E_1=(-1)^wS^{4r+\varepsilon}A^\varepsilon,
\qquad E_2=S^{2w+\varepsilon}=S^a.
\tag{TM.3707}
$$

这里 $\varepsilon=H\bmod2$，且 $w=\lfloor H/2\rfloor-4i+2s$ 与 $\lfloor H/2\rfloor$ 同奇偶，因此第一未来窗恰为 $S^{4r}B^H$。也可在前两窗直接使用 $B^{2(k+r)}AB^{2(k-r)}=A$ 和 $S^{2(k+r)}BS^{2(k-r)}=S^{4r}B$。第三窗只是同源证书的一部分；本合同在这些初始来源上不能访问它。

不同 $i$ 给不同 $m$，不同 $s$ 给不同 $n$；固定 $i,s$ 后，不同 $r$ 的 $S^{4r}B^H$ 由引理 28.1 的无限阶正规形唯一性区分。约定 36.1 遂保证所数目标全部不同。固定行 $i$，其宽度为 $\sum_{s=0}^i(2(i-s)+1)=(i+1)^2$。固定 $(s,r)$ 后，恰须 $i\ge s+|r|$；固定 $d$ 时，$s=d,r=0$ 给一列，$s=0,\ldots,d-1$ 各给 $r=\pm(d-s)$ 两列，合为 $2d+1$。$\square$

**定理 37.4（全协议的精确亏额不等式与首项极限）。** 设大小为 $L$ 的任意同源补充字母表使一个合同 A 协议在整个 $\mathcal T_H$ 上取得初始目标。若 $1\le L\le K$，置 $e=K-L$，则必有

$$
\frac{e(e+1)(2e+1)}6
\le \sum_{u=1}^K\min(L,u^2).
\tag{TM.3708}
$$

令 $t=\lfloor\sqrt L\rfloor$，右侧的精确整数公式是

$$
\sum_{u=1}^K\min(L,u^2)
=\frac{t(t+1)(2t+1)}6+(K-t)L.
\tag{TM.3709}
$$

特别地，令 $b(K)$ 为 $1,\ldots,K$ 中满足（TM.3708）的最小整数 $L$，则

$$
M_A(H)\ge b(K),\qquad
K-\sqrt[3]{3}\,K^{2/3}\le M_A(H)\le K=M_B(H),
\tag{TM.3710}
$$

并有

$$
\lim_{H\to\infty}\frac{M_A(H)}H=\frac18,
\qquad
\lim_{H\to\infty}\frac{M_A(H)}{M_B(H)}=1.
\tag{TM.3711}
$$

证明。把同一个全家族协议和同一个标签函数限制到定理 37.3 的实际代表来源。每个列在每个标签类至多含一个 $C$ 成员，所以高度为 $h$ 的列至少有 $(h-L)_+$ 个 $P$ 成员。每个行在每个标签类至多含一个 $P$ 成员，且行 $i$ 总共只有 $(i+1)^2$ 个目标。因此

$$
\begin{aligned}
|P|&\ge\sum_{d=0}^{e-1}(2d+1)(e-d)
      =\sum_{v=1}^e v^2
      =\frac{e(e+1)(2e+1)}6,\\
|P|&\le\sum_{i=0}^{K-1}\min\bigl(L,(i+1)^2\bigr).
\end{aligned}
\tag{TM.3712}
$$

中间恒等式由 $v^2=\sum_{d=0}^{v-1}(2d+1)$ 换序得到，故（TM.3708）成立。$e=0$ 时左侧是空和；$K=L=1$ 也包含在内。对 $u\le t$ 使用 $u^2\le L$，对 $u>t$ 使用 $u^2>L$，给出（TM.3709）。因为 $L=K$ 总满足不等式，$b(K)$ 良定义；它只是必要条件的整数下界，不是精确容量。既有定理 32.6、§33 的下界仍可与它取最大值。

定理 32.3–32.4 已给 $M_A(H)\le K=M_B(H)$，无需重证固定档案构造。取 $L=M_A(H)$，右侧不超过 $LK\le K^2$，而左侧至少是 $e^3/3$，故 $e\le\sqrt[3]{3}K^{2/3}$，得到（TM.3710）。最后 $K/H\to1/8$ 且 $K^{2/3}/H\to0$，夹逼即得（TM.3711）。这个必要条件量化全部允许动作和任意来源相关标签，不以标签经由 $q_H$、只用 $\alpha$ 控制或有限协议表为假设。$\square$

### 37.3 深列目标的尖锐跨列行负载

**定义 37.5（半块、深目标及其伴随者）。** 对 $K=\lceil H/8\rceil$ 定义共同公开参数

$$
\eta=
\begin{cases}
0,&8K-7\le H\le8K-4,\\
1,&8K-3\le H\le8K.
\end{cases}
\tag{TM.3713}
$$

对整数 $1\le r<K$ 置 $T=K-r$。令 $D(H,T)$ 为实际层标签1目标 $q$ 中，在相同 $\Gamma_H$ 列里还存在尺寸 $m(q)+4T$ 目标的那些目标。引理 36.2 保证，这等价于该列中有至少 $T$ 个比它大的目标。它是初始目标集合的定义，不供应尺寸端口。

**定理 37.6（深列在一个首读尺寸行上的精确最大重数）。** 对每个 $H$ 和 $1\le r<K$，有

$$
\max_{g,m}
\bigl|\{q\in D(H,T):E_0(q)=g,\ m(q)=m\}\bigr|
=r(r+\eta).
\tag{TM.3714}
$$

等号由具有完整连通 Euler 证书的实际来源和实际同列伴随者达到，包括零 $\beta$ 伴随者端点。

证明。先证上界。对一个深目标取实际同列伴随者，尺寸为 $m'=m+4T$，令伴随者的 $\beta$ 数为

$$
b'=n-m-4T\ge0.
$$

两来源组成分别是

$$
(a,b)=(m-4T-b',\ 4T+b'),
\qquad
(a',b')=(m+4T-b',\ b').
\tag{TM.3715}
$$

非负性给 $m\ge4T+b'$，而共同 $n=m+4T+b'\le H$，所以

$$
8T+2b'\le H\le8K-4+4\eta,
\qquad b'\le4r-2+2\eta.
\tag{TM.3716}
$$

若最后等号成立，前面各式必须取等号；初始 $a=0$，伴随者 $a'=8T$。初始来源于是纯 $\beta$，其 $E_1$ 指数为 $4T+b'$；伴随者的 $\alpha$ 数为偶数，引理 36.5 给其 $E_1$ 指数绝对值至多 $b'$。因为 $T>0$，两者不可能在同一列。因此实际必要界严格改为

$$
0\le b'\le4r-3+2\eta.
\tag{TM.3717}
$$

固定 $g,m$。引理 29.5 的相位字符固定 $b'$ 的模四余数，因为初始 $b=4T+b'$。固定一个允许的 $b'$ 后，$n=m+4T+b'$ 固定，伴随者的 $\alpha$ 奇偶 $\varepsilon=a'\bmod2$ 也固定。把伴随词的奇数序号与偶数序号 $\beta$ 之前的 $\alpha$ 奇偶符号之和分别记为 $U,V$，引理 36.5 给

$$
k_0=U-V,
\qquad k_1=\varepsilon+U+V=\varepsilon+k_0+2V.
\tag{TM.3718}
$$

$k_0$ 由 $g$ 固定，$V$ 是 $\lfloor b'/2\rfloor$ 个 $\pm1$ 的和，最多有 $\lfloor b'/2\rfloor+1$ 个值。完整 $E_1=(-1)^{e_1}S^{k_1}A^{p_1}$ 没有额外的符号倍数：$p_1=n\bmod2$ 已固定，而 $m'\equiv2e_1+k_1\pmod4$ 唯一固定 $e_1\in\{0,1\}$。因此固定 $b'$ 至多给这么多个不同列及目标。

当 $\eta=0$，在（TM.3717）范围内，余数0、1的和各为 $\sum_{j=0}^{r-1}(2j+1)=r^2$，余数2、3的和各为 $\sum_{j=0}^{r-2}(2j+2)=r(r-1)$，后一个和在 $r=1$ 时为空。当 $\eta=1$，四类分别为 $r^2,r^2,r(r+1),r(r+1)$。每个 $g$ 只用其中一类，故统一上界为 $r(r+\eta)$。

以下给出每个半块上达到等号的共同来源证书。对

$$
0\le j\le r-1,\qquad 0\le i\le2j+\eta
$$

置

$$
\begin{aligned}
m_*&=4K-3+2\eta,&a&=4r-4j-3,&b&=4T+4j+2\eta,\\
u&=0,&v&=2i-2j-\eta,&w&=2r-2j-2,\\
p&=1,&q&=0,&X&=0,&Y&=T+i.
\end{aligned}
\tag{TM.3719}
$$

原子卷定理 360.2 的八边证书是

$$
\mathbf x=(w+1,w,0,0),\qquad
\mathbf y=(T+i,T+i,T+2j+\eta-i,T+2j+\eta-i).
\tag{TM.3720}
$$

其实际伴随者取 $w'=w+4T$、$Y'=i$，其余正规参数不变，证书为

$$
\mathbf x'=(w+4T+1,w+4T,0,0),\qquad
\mathbf y'=(i,i,2j+\eta-i,2j+\eta-i).
\tag{TM.3721}
$$

两组边数都非负且总流量从 $00$ 到 $10$。原来源的两个 $\beta$ 二边回路均为正，$x_{00}>0$ 把它们接通；$w=0$ 时仍接通。伴随者的 $\alpha$ 二边回路为正，任何存在的 $\beta$ 回路都接在它上面。特别地 $j=i=\eta=0$ 时，伴随者只有连通的 $\alpha$ 回路，不使用虚假的空来源。它的组成是 $(a+8T,b-4T)$，尺寸为 $m_*+4T$。两组八边数都满足原子卷（360.1）–（360.2），所以完整 Euler 判据确实认证两棵实际来源。相应的字面叶词还可取

$$
\begin{aligned}
U_{j,i}&=\beta^{2(T+i)}\alpha\beta^{2(T+2j+\eta-i)}\alpha^{a-1},\\
V_{j,i}&=\beta^{2i}\alpha\beta^{2(2j+\eta-i)}\alpha^{a+8T-1},
\end{aligned}
\tag{TM.3722}
$$

省略零次块后均非空；任意固定有序二叉括号化都是实际原树。

原子卷引理 359.2、定理 359.3 给两个来源共同的前两窗

$$
E_0=(-1)^\eta A,
\qquad E_1=S^{4i-4j-2\eta}B,
\tag{TM.3723}
$$

因为 $w,w+4T$ 均为偶数。各自第三窗分别为 $S^{2w+1}$ 和 $S^{2w+8T+1}$，仅作同源证书，不作为可取得读口。共同第一替换尺寸为

$$
n_j=8K-4r+4j-3+4\eta
\le8K-7+4\eta\le H.
\tag{TM.3724}
$$

在整个指定半块，$m_*+n_j-H\ge4T-2+2\eta>0$，伴随者的第二替换尺寸更大。因而二者都在层标签1，具有相同实际 $\Gamma_H$，且尺寸相差 $4T$；每个 $U_{j,i}$ 的初始目标都属于 $D(H,T)$。不同 $j$ 的 $n_j$ 不同；固定 $j$ 后不同 $i$ 的 $E_1$ 不同。它们全部处于同一个 $g,m_*$ 行，共计

$$
\sum_{j=0}^{r-1}(2j+\eta+1)=r(r+\eta)
$$

个不同目标，达到上界。$\square$

### 37.4 覆盖全部层标签的分割与字面取得协议

**定理 37.7（深列分流的全家族取得构造）。** 固定 $H$，取 $1\le r<K$，置

$$
T=K-r,\qquad C=r(r+\eta),\qquad J=T-C,
\qquad c=H-4T.
\tag{TM.3725}
$$

将层标签2的空层容量约定为 $D_2(1)=0$，其余 $D_2(H)$ 使用定理 36.3。若

$$
J\ge1,\qquad D_2(H)\le J,\qquad 0<c\le8J,
\tag{TM.3726}
$$

则存在大小为 $T$ 的同初始来源补充字母表及一个共同确定性协议，在整个 $\mathcal T_H$ 上有限停止并返回初始 $q_H$，来源调用至多 $H+4$。这个标签是初始 $q_H$ 的函数，所用正上下文是一次受守卫的原子右拼接 $K(4T,0)=\alpha^{4T}$。

证明。字母表分为互不相交的档案标签 $\mathcal A=\{\mathrm a_1,\ldots,\mathrm a_J\}$ 和截止标签 $\mathcal U=\{\mathrm u_1,\ldots,\mathrm u_C\}$，合计 $J+C=T$。在每个层标签1的实际 $\Gamma_H$ 列中，按尺寸递增排列其 $f\le K$ 个目标；此上界由定理 32.4 的固定档案容量给出。把最低的 $(f-T)_+$ 个目标标为 Low。引理 36.2 使这些目标恰为该列的 $D(H,T)$ 成员。余下 $\min(f,T)$ 个目标中，最低的

$$
\min\bigl(J,\min(f,T)\bigr)
$$

个目标分别取得不同档案标签；再剩下的最高目标标为 High，给它们在该列内互异的截止标签。High 数量为

$$
\max\bigl(0,\min(f,T)-J\bigr)\le T-J=C,
$$

故这些标签够用。跨列的 Low 则在每个固定 $(g,m)$ 行上分配互异截止标签：定理 37.6 保证该行至多有 $C$ 个 Low。可按 $(n,k_1)$ 字典序给其秩；固定 $g,m,n,k_1$ 后相位恢复完整 $z$，所以不会漏掉不同目标。Low 与 High 的分配独立，二者共享截止标签是允许的。层标签0与2只分配档案标签；其列大小分别为1和至多 $D_2(H)\le J$，也能在每列内单射分配。这个分割恰覆盖全部实际目标一次，定义出同源 $h(t)=h(q_H(t))$。

证明共同截止真正分离 Low 和 High。Low 有同列伴随者 $m+4T\le n\le H$，所以 $m\le c$。任何 High 在它的实际列中至少有 $J$ 个较小目标。引理 36.2 因而给出实际同列目标 $m-4J$；初始和伴随者组成非负，分别给

$$
m\le n\le2(m-4J),\qquad m\ge8J.
\tag{TM.3727}
$$

若 $m=8J$，这些不等式迫使 $n=m=8J$。High 为纯 $\alpha$，第一未来窗为 $B^{8J}=1$；较小伴随者为尺寸 $4J$ 的纯 $\beta$，第一未来窗为 $S^{4J}\ne1$。它们不能在同一实际列，故真正有

$$
m\ge8J+1>c
\tag{TM.3728}
$$

在 High 上成立。于是一个共同原子守卫能同时分离所有截止标签的两种来源，不能把这个结论换成各列独立编号。

以下给出完整实际执行器。先读一次初始 $E_0=g$ 并保留。若供应的是档案标签，接着执行定义 31.2 的剩余动作，不重复首读：尝试第一次 $\rho$，接受则读 $E_1$ 并尝试第二次 $\rho$，再次接受则读 $E_2$；在相应位置以单叶 $\alpha$ 右填充到第一次拒绝。定理 31.3 给实际初始 $\Gamma_H$。档案标签在每个这种列内单射，所以共同认证解码表由 $(h,\Gamma_H)$ 返回唯一初始目标。

若供应的是截止标签，尝试一次原子右接 $\alpha^{4T}$，不把它拆成单叶序列。它接受当且仅当 $m+4T\le H$，由前述分离恰在 Low 上接受。接受后用单叶 $\alpha$ 右填充到第一次拒绝；若成功 $s$ 次，则

$$
s=H-(m+4T)=c-m,\qquad m=c-s.
\tag{TM.3729}
$$

Low 的行内标签单射使真实取得的 $(h,g,m)$ 决定完整初始目标。此分支不需要保留已经失去的未来窗。

若原子拼接拒绝，来源保持不变，且它属于 High，初始层标签必为1。尝试一次 $\rho$；它接受，随后真实读出原始 $E_1=z$。再用单叶 $\alpha$ 右填充到第一次拒绝，若成功 $s$ 次，则 $n=H-s$。High 的截止标签在每个 $(1,g,z,n)$ 列中单射，所以 $(h,g,z,n)$ 返回唯一初始 $q_H$。这里没有第二次替换要求，没有读取被拒候选，也没有把填充后的当前目标替代初始目标。

档案分支复用定理 31.6 的至多 $H+4$ 次来源调用。Low 分支包含初始读、原子拼接、$c-m$ 次成功填充及一次最终拒绝，共 $c-m+3$ 次。High 分支包含初始读、宏拒绝、一次 $\rho$、其后的真实读、$H-n$ 次成功填充及一次最终拒绝，共 $H-n+5\le H+4$ 次。Low 的 $c\le H$ 和 $m\ge1$ 也给所需上界。零次成功填充时仍计入最终拒绝。所有分支只访问供应标签、公开 $H$、真实读数和已经取得的计数／守卫记录，故构成符合合同的同源初始目标取得协议。$\square$

**定理 37.8（整数二次参数与平方根保证节省）。** 对所有整数 $H\ge1$，按（TM.3713）取 $\eta$，定义

$$
r_H=
\begin{cases}
\displaystyle\left\lfloor\frac{\sqrt{8K+17}-3}{4}\right\rfloor,&\eta=0,\\[2mm]
\displaystyle\left\lfloor\frac{\sqrt{8K+25}-5}{4}\right\rfloor,&\eta=1.
\end{cases}
\tag{TM.3730}
$$

则

$$
M_A(H)\le K-r_H,
\qquad r_H=\frac{\sqrt H}{4}+O(1).
\tag{TM.3731}
$$

$r_H=0$ 时使用既有固定档案构造。对 $17\le H\le20$ 保留定理 36.9 的更强精确值 $M_A(H)=2$。特别地，对每个 $H\ge49$，有 $M_A(H)<M_B(H)$。

证明。若 $\eta=0$ 且 $r=r_H\ge1$，（TM.3730）精确等价于选取满足

$$
K\ge2r^2+3r-1
\tag{TM.3732}
$$

的最大非负整数 $r$。此时 $K\ge4$，$1\le r<K$，且

$$
J=K-r-r^2\ge K/2,
\qquad
c=H-4(K-r)\le4K+4r-4\le8J.
\tag{TM.3733}
$$

第一式由 $K/2-r-r^2\ge(r-1)/2\ge0$ 得到，第二式最后的不等式恰是（TM.3732）。又 $H\ge8K-7$ 给 $c\ge4K+4r-7>0$，所以截止是一个正的公共整数。

若 $\eta=1$ 且 $r=r_H\ge1$，它是满足

$$
K\ge2r^2+5r
\tag{TM.3734}
$$

的最大非负整数 $r$。此时 $K\ge7$，$1\le r<K$，且

$$
J=K-r-r(r+1)\ge(K+r)/2,
\qquad
0<c\le4K+4r\le8J.
\tag{TM.3735}
$$

第一式和最后一个不等式都由（TM.3734）直接移项得到，正性来自 $H\ge8K-3$。

在两种非零 $r$ 情形，$J\ge1$。由定理 36.3 与 $H\le8K$，有

$$
D_2(H)\le\left\lceil\frac K3\right\rceil\le J.
\tag{TM.3736}
$$

为核对第一个整数界，$2\le H\le4$ 时 $D_2=1$；$H\ge5$ 时以 $K=3d,3d+1,3d+2$ 分别代入 $1+\lfloor(8K-5)/24\rfloor$，所得上界依次为 $d,d+1,d+1$。$H=1$ 的空层为0。第二个界由整数 $J\ge K/2$ 得到。于是（TM.3726）全部满足，定理 37.7 给 $M_A(H)\le K-r_H$。若 $r_H=0$，定理 32.3 的 $\sigma_K$ 本来就给此界，所有小尺度均被覆盖。

两根式都等于 $\sqrt{K/2}+O(1)$，向下取整只改变有界量；而 $K=H/8+O(1)$，故 $r_H=\sqrt H/4+O(1)$。若 $H\ge49$，则 $K\ge7$；在两种半块中 $r=1$ 分别满足（TM.3732）、（TM.3734），所以 $r_H\ge1$，而 $M_B(H)=K$。这给严格全家族分离；平方根是已构造的保证节省，不是未知最优节省的渐近等号。$\square$

### 37.5 指定截止前缀的不可逆合并边界

**定理 37.9（带首个接受截止假设的尖锐行合并障碍）。** 取定理 37.6 的 $C=r(r+\eta)$ 个较小来源 $U_{j,i}$，并额外假设 $K\ge2r$。设协议在每个这样的来源上，在任何接受的 $\rho$ 之前，首个被接受的修改是一个叶数为 $4T$ 的实际正上下文拼接；此动作之前只执行当前读和被拒绝动作。上下文可以含任意 $\alpha,\beta$，拼接可以在左或右，且可由标签及既有记录选择。在这个前缀假设下，任何成功协议至少须在该来源族上使用 $C$ 个补充标签。允许任意后续动作和任意大的完整档案，这个下界仍成立。

证明。所有 $U_{j,i}$ 初始 $E_0=(-1)^\eta A$、初始尺寸 $m_*=4K-3+2\eta$ 相同。一个共享标签类在首次接受修改前的读数和每个拒绝动作的记录相同：正上下文守卫只依赖共同 $m_*$，而初始 $\rho$ 在层标签1必接受，所以此假设下不能在此前尝试一个被拒绝的 $\rho$。因此同标签成员选择相同首个上下文和方向。

该上下文确实在每个见证上接受，因为

$$
m_*+4T=8K-4r-3+2\eta\le8K-7+4\eta\le H.
\tag{TM.3737}
$$

不论其组成如何，它使第一未来尺寸增加至少 $4T$。使用（TM.3724）的最小 $n_j$ 及半块上端点，得到

$$
n_j+4T-H\ge4K-8r+1>0.
\tag{TM.3738}
$$

于是接受拼接后，同标签成员全部进入层标签0，当前尺寸同为 $m_*+4T$，当前 $E$ 是共同 $g$ 乘上相同已知左因子或右因子，完整记录也相同。它们的当前 $q_H$ 相同，但初始目标两两不同。定理 30.2 使合并永久，任何后续读取、替换或正拼接都不能解除。因此每个标签类至多含一个见证，必须有至少 $C$ 个标签。

若一个 $T=K-r$ 标签的结构要求所有这些深目标都经过上述首截止，则必须满足 $r(r+\eta)\le K-r$，所以此结构只能有 $r=O(\sqrt K)$ 的节省。定理 37.8 在其充分条件下确实得到同一平方根阶，但这里没有证明最优常数。前缀假设不可删除：这 $C$ 个较小来源本身的 $\Gamma_H$ 两两不同，由定义 31.2 的不变档案执行器可用单个标签全部恢复。因此本定理不是不受限的 $M_A(H)\ge C$，也不排除别的首个取得策略。$\square$

### 37.6 联合容量结论与关系恢复的范围

**定理 37.10（首项相同而可节省量无界、次线性）。** 令全家族最优字母表节省为 $\Delta(H)=M_B(H)-M_A(H)$。对每个 $H\ge1$ 有

$$
r_H\le\Delta(H)\le\sqrt[3]{3}\,K^{2/3},
\tag{TM.3739}
$$

从而

$$
\frac{\sqrt H}{4}+O(1)\le\Delta(H)
\le\sqrt[3]{3}\,K^{2/3},
\qquad
\Delta(H)\longrightarrow\infty,
\qquad \frac{\Delta(H)}H\longrightarrow0.
\tag{TM.3740}
$$

左侧渐近不等式的精确含义是存在常数 $B$，使全部 $H\ge1$ 都满足 $\Delta(H)\ge\sqrt H/4-B$。等价的构造上界为 $M_A(H)\le H/8-\sqrt H/4+O(1)$；首项极限仍是（TM.3711）的 $1/8$。这些结论不确定一般有限 $M_A(H)$ 的精确值，也不确定 $\Delta(H)$ 的尖锐阶或常数。

证明。定理 37.8 和 $M_B(H)=K$ 给左界；定理 37.4 给右界。$r_H=\sqrt H/4+O(1)$ 蕴含其趋于无穷；$K^{2/3}/H\to0$ 蕴含次线性。余下上界用 $K=H/8+O(1)$ 代入得到。平方根下界与三分之二次幂上界之间仍有未闭合的节省区间；不能从指定截止结构的条件下界推出它已经匹配。$\square$

**约定 37.11（同源恢复、供应与费用边界）。** 本节恢复的是每棵实际原树的初始 $q_H$，包括纯 $\alpha$、纯 $\beta$ 和全部有序括号化。行、列、伴随者、Euler 参数及 $(m,n,k_1)$ 是离线数学坐标，在线取得只使用实际当前 $E$、补充标签、公共 $H$ 和已经发生的守卫／计数记录。所用纯 $\alpha$ 宏的前两窗因子是 $A^{4T}=B^{4T}=1$，但接受拼接仍改变原树，不是复位。上界分割的 $h$ 必须在首次来源动作前从同一未修改的初始来源供应，认证实际解码表及所用正上下文是共同固定的供应或构造接口；本节未定义保持原树的标签生产器，不能先取得 $\Gamma_H$ 再假定可以复位。命题 36.10 的保持原树生产限制仍适用。

$H+4$ 只计算读取、替换尝试和拼接尝试，包含所有最终拒绝。标签的生产、同源认证、认证数据的核验、传输与保留，实际表的生成和描述、正上下文的生成与供应、正规坐标转换、精确算术工作区、控制器和完整记录的存储、输出展开及物理时间分别属于不同资源项；字母表数的节省不自动给这些费用的节省，也不给总控制记忆最优值。

恢复与静态充分性的数学接口沿用仓内 [TargetRecoveryCriterion](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean) 的 `target_recovery_criterion` 及 [IndexedTargetSufficiency](../../../D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency.lean) 的 `indexed_target_sufficiency`：过程必须是同一实际协议在同一初始来源上取得的完整记录，目标取初始 $q_H$；同一完整记录纤维内目标恒定才许可解码。本节的实际执行器和定理 30.2 分别承担可取得性与永久合并，不能把分别可达的窗口拼成未执行的联合读数。有限静态 [MinimumCompleteObserverSetCover](../../../D5/S3/ConceptDynamics/ExperimentDesign/MinimumCompleteObserverSetCover.lean) 的 `minimum_complete_observer_is_set_cover` 须有共同供应的观察函数及相应加性费用；它不代替定理 35.4 的嵌套原始目标保持条件。[SafeActionRefinementMonotonicity](../../../D5/S3/ConceptDynamics/Decision/SafeActionRefinementMonotonicity.lean) 的 `safe_action_refinement_monotonicity` 只处理纤维上动作合法性；定理 37.9 表明一个合法动作仍能销毁初始区别。初态识别与首动作合并的文献语义沿用 §31.7 的既有引文，不移用其长度界来得到本节的来源特定容量公式。

定理 37.2–37.10 是对本卷实际守卫合同及原子卷共同来源证书的普通数学推导，不据静态接口的存在宣告这些具体结论已获形式核验。一般最优分割、尖锐节省、标签生产与认证成本、来源调用和全部存储最优，以及原树括号、叶地址、绝对时间、物理空间与原树本身的恢复均未由上述容量界确定；这些对象与初始行为商的恢复不同。

## 追加锚（本行以下为增补区）

## 38. 共同实际历史中的初始目标配对、上带闭包与无界最小障碍

本章固定 §30 的来源和动作合同。公开整数 $H\ge1$ 在运行中不变；未知来源是一棵实际非空、有序、自由括号化的 $\alpha/\beta$ 原树。当前 $E$ 读不改来源，$\rho$ 及已知正上下文的左、右拼接都受候选叶数不超过 $H$ 的守卫。拒绝保持来源，不返回候选 $E$。控制器初始化相同，依据已取得记录确定动作，并在每个声明输入上有限停止。补充标签由同一初始来源供应。以下目标恒为初始 $\tau=q_H(t)$；当前来源的 $q_H$ 只决定未来响应，不能替代这个目标。

对组成 $(a,b)$ 写 $m=a+b$、$n=a+2b$，故 $m\le n$，后续资源依次为 $m+n,m+2n$。$A=E(\alpha)$、$B=E(\beta)$、$S=BA$ 保持 §§28–30 和[原子卷 §§359–360](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的含义。实际来源认证、输出解码表、上下文供给及其算术成本都是独立前提；下面的可行性整数摘要不承担这些存储或供给义务。

### 38.1 一个实际历史上的配对商

**命题 38.1（原始目标到当前行为的同余与永久碰撞）。** 固定已实际达到的一份共同记录 $\omega$，包括相同公共输入、相同供应标签值、动作身份、上下文身份、守卫响应和真实读。令表中每行的初始来源为 $t_i$，沿该记录取得的当前来源为 $s_i$，并置

$$
\tau_i=q_H(t_i),\qquad b_i=q_H(s_i),\qquad
P_\omega=\{(b_i,\tau_i)\}.
$$

存在定义良好的函数 $f_\omega$，使 $b_i=f_\omega(\tau_i)$。若两个不同 $\tau$ 有相同当前 $b$，则该共同历史之后不能恢复所有初始目标。若没有这种碰撞，当前商与存活初始目标一一对应；保留其逆字典后，恢复当前商与恢复初始目标等价。每个相同配对只须保留一个实际代表；尤其可按初始目标去重，但不能删去当前商相同而初始目标不同的行。

证明。引理 30.1 给每个固定来源动作一个由当前 $q_H$ 决定的响应及商更新，拒绝为恒等更新。相等初始 $q_H$ 在记录第一步给相等响应和后继商；按记录长度归纳，所有前缀如此，得到相等当前商。因此 $f_\omega$ 定义良好，完整三窗或括号的额外差别不破坏此结论。

若 $\tau\ne\tau'$ 而 $f_\omega(\tau)=f_\omega(\tau')$，过去记录已相同，定理 30.2 使每个共同确定性延续的未来记录也相同。若协议逐点停止，它在二者上同时输出同一个值，不能等于两个目标。增加档案或只对既有记录作后处理不修复这个碰撞。若 $f_\omega$ 单射，有限实际像上的逆存在，实际取得任一侧后按字典映射即可取得另一侧；这是解码，不是来源逆动作。相同 $(b,\tau)$ 的全部实现有相同未来响应和相同所需输出，删除重复代表不影响延续存在性。不同历史的行若被合在一起，上述归纳前提失效，不能沿用这个字典。$\square$

例如 $H=9$ 时，实际词 $\beta^4\alpha^5$ 与 $\beta^8\alpha$ 的完整组成不同，但都有 $m=9,E_0=A,n>9$，故初始目标同为 $(0,A,9)$；它们只算一个目标。反之，命题 35.8 的 $\alpha^9$ 与 $\beta^2\alpha\beta^2$ 有不同初始目标，共同首次 $\rho$ 后当前商同为 $(0,B,9)$；二者必须保留，且延续不可能。这里的两种去重方向不能互换。

### 38.2 行释放、列期限与完整块条件

**定义 38.2（上带配对表与两个极值轮廓）。** 在命题 38.1 的一个实际共同历史上，实际读当前 $E=g$，固定其非空纤维，并假设所有当前来源满足严格上带条件 $m+n>H$。按初始目标去重为有限表 $C$；每个目标保留当前来源的实际代表和输出关联。当前标签只有 $0,1$。标签 $0$ 的表内 $n$ 置为 $\infty$，不保留不可用的 $z$；标签 $1$ 保留真实 $n\le H$ 和 $z=E_1(s)$。这个哨兵只表示所有有限截止均拒绝，不是来源的真实尺寸或运行时端口。

在每个当前 $m$ 行上，若至多一个初始目标，置 $R(m)=0$；否则令 $R(m)$ 为该行各目标的 $n$ 的第二大值。重复的资源值按不同目标重复计数。例如两个不同目标都需要 $n=7$，第二大值仍为 $7$。$R$ 可为 $\infty$。对标签 $1$ 的每个多目标列 $k=(n,z)$，令 $s(k)$ 为列内 $m$ 的第二大值，同样按目标计重，置

$$
D(s)=\min\{n(k):s(k)=s\},\qquad
B(l)=\min_{s>l}D(s),
$$

空最小值为 $H+1$。两个轮廓各至多有 $H$ 个位置。$B(l)$ 随 $l$ 不减。一个区间块 $l<m\le c$ 称 F 安全，若目标是 $m$ 的函数；称 R 安全，若 $n>c$ 的拒绝部分目标是 $m$ 的函数，而 $n\le c$ 的接受部分目标是 $(n,z)$ 的函数。若入口读已支付，后续执行不重复支付它。

这里每个目标恰占一行，源于固定历史同余及按目标去重，不是把任意来源实现的条数当成目标重数。当前商碰撞允许保留在表内，由下面的条件直接检出；不为它制造另一种优化模型。

**引理 38.3（释放—期限块判据）。** 对 $0\le l<c\le H$，F 安全等价于该块所有 $R(m)=0$；R 安全等价于

$$
\max_{l<m\le c}R(m)\le c<B(l),
\tag{TM.3801}
$$

空行最大值为零。存在忠实的全动作延续恢复初始目标，当且仅当有递增截止分块使每个非空块 F 安全或 R 安全。

证明。F 条件直接是每行至多一个目标。R 拒绝部分在每行至多留一个目标，恰等价于第二大 $n$ 不大于 $c$；两个无穷哨兵也按此规则判为失败。对接受列 $k$，若 $n(k)\le c$，其所有尾部成员 $m>l$ 已满足 $m\le n(k)\le c$，故无需再筛选块的上界。尾部至少留两个目标恰在 $s(k)>l$。于是存在重复接受列恰在某个 $s>l$ 的期限不大于 $c$，即 $B(l)\le c$。这证明（TM.3801）的两个方向。

为把块条件接回全动作，考察任何成功协议首次 $\rho$ 前的一个共同历史。所有读都是已知左右单位因子包围入口 $g$；已接受正上下文累计资源为 $(D_0,D_1)$，其中 $D_0\le D_1$。全部接受、拒绝守卫留下入口尺寸区间 $(l,u]$，$u=H-D_0$。置 $c=H-D_1\le u$。首次 $\rho$ 拒绝时，下一尺寸超过 $H$，当前商为 $(0,L_0gR_0,m+D_0)$；同 $m$ 的不同目标会永久碰撞，所以拒绝部分须对 $m$ 恒定。接受时，后继下一尺寸为 $m+n+D_0+D_1>H$，当前商为 $(0,L_1zR_1,n+D_1)$；同 $(n,z)$ 的不同目标也会永久碰撞。若 $c>l$，下半块 $(l,c]$ 因而 R 安全；上半块 $(c,u]$ 有 $n\ge m>c$，全拒绝，因而 F 安全。若 $c\le l$，整块 F 安全。首次替换前停止的叶也 F 安全，因为共同记录只能输出一个值。

有限表上各输入有限停止，故各首次替换前路径的并有限；其尺寸区间互不相交，否则同一确定性程序在相同尺寸和读上会有两条记录。按右端点排序并保留空隙，得到有限截止分块。上述论证包括任意正词、任意左右位置及既有档案，正是 §34 的阶段必要性在初始目标上的应用。逆向则由命题 38.5 的字面扫描逐块实现，无须假设新的尺寸读口。因此块条件等价于所有允许动作下的可恢复性。$\square$

### 38.3 最小闭包与稀疏包含式

**定理 38.4（最小闭包的精确性与稀疏障碍）。** 从 $l=0$ 开始，剥去第一歧义行 $s>l$ 之前的单目标行，以 F 块覆盖其占用前缀，令 $l=s-1$；没有歧义行时以 F 块到 $H$ 结束。从 $c=s$ 反复更新

$$
c\longleftarrow\max\left(c,\max_{l<m\le c}R(m)\right).
\tag{TM.3802}
$$

遇到 $\infty$ 或超过 $H$ 的释放值即失败。到达有限不动点 $c_*$ 时，若 $c_*\ge B(l)$ 则失败，否则发出 R 块 $(l,c_*]$，令 $l=c_*$ 并继续。该算法接受当且仅当存在恢复协议。

等价的稀疏形式如下。对每个歧义行取闭实区间 $I_m=[m,R(m)]$；无穷或超过上限的右端判为失败。只合并有交集的区间，公共端点也算交集，得到互不相交的强制分量 $[a_j,b_j]$。整数上相邻而不相交的 $[a,b]$ 与 $[b+1,d]$ 不合并。对每个多目标接受列取跨度 $J_k=[s(k),n(k)]$，去重并删去包含另一跨度的非极小跨度。保留的跨度构成包含反链。可行恰在没有一个保留跨度被包含于任何强制分量。

证明。更新严格增加时增加至少一，有限且不超上限时必终止。F、R 安全性在删除目标后、保留原端点时均遗传。因而剥去单目标前缀，不破坏任一既有可行分块：限制旧块，保留端点即可。首个剩余歧义行 $s$ 不能属 F 块。若可行首 R 块端点为 $d$，则块内每个释放值不超过 $d$。归纳表明（TM.3802）的每个迭代值不超过 $d$，所以无穷、超上限及 $c_*>d$ 均不可能。若 $c_*\ge B(l)$，则 $d\ge B(l)$，违反该块期限，故全协议不可行。

若 $c_*<B(l)$，最小闭包前缀自身 R 安全。把任一可行首块 $(l,d]$ 换成此安全前缀，余下 $(c_*,d]$ 仍使用旧端点 $d$；它只是旧安全块的限制，仍安全。后续块原样保留。因此每次选最小闭包都不损失可行延续。按剩余占用行归纳证明算法完整性；充分性由块引理和实际扫描成立。每个 R 块删除至少一歧义行，故总步骤有限。

对稀疏形式，从第一歧义行 $a$ 开始，闭包扩张恰在某个 $I_m$ 的左端已落入当前区间且右端伸出时发生。迭代不能越出含 $a$ 的区间并集连通分量；稳定也不能遗漏与当前区间相交的 $I_m$。所以最小闭包恰是该分量右端 $b$，而首块下界为 $a-1$。其期限失败恰在存在 $s(k)\ge a,n(k)\le b$；由 $s(k)\le n(k)$，这等价于 $J_k\subseteq[a,b]$。端点 $b$ 处启动的区间参与同一闭包；$b+1$ 处启动的区间留给下一块，说明仅整数相邻不能合并。重复上述论证即得全部分量。

若跨度 $J$ 包含较小跨度 $J'$，每个包含 $J$ 的分量也包含 $J'$，故删除 $J$ 不会漏掉最后一个障碍。有限反复删除后，每个删除的跨度包含某个保留跨度，因而判据不变。对每个左端 $s$ 只留最小右端，再取 $s'\ge s,n'\le n$ 的非支配前沿，得到同一反链，至多 $H$ 条。无障碍时对每个分量使用端点 $b_j$ 的 R 块，间隙占用行使用 F 块；有障碍时闭包已经证明所有动作不可行。$\square$

碰撞不会被这个算法掩盖。当前标签 $0$ 的同 $m$、不同初始目标产生至少两个无穷值，释放立即失败。当前标签 $1$ 的同 $(m,n,z)$、不同目标产生释放至少 $n$，同时其接受列期限为 $n$ 且 $s(k)\ge m$。任何含 $m$ 的 R 块都须结束于 $n$ 之后或其上，又必须早于 $n$，矛盾；F 块也不安全。这与命题 38.1 的永久障碍相合。

从 $N$ 个目标构造轮廓、分量和反链，可排序分组后线性扫描；比较操作为 $O(N\log(N+1))$，可行性摘要存储为 $O(k+p)$ 个整数端点，其中 $k,p\le H$。这是给定类的可行性表示，不是总控制器或最少位数。它不在任意限制下闭合：删除一个行目标可以消除释放并断开分量，旧反链也会改变。新标签分割、子表限制或实际动作之后须从实际配对表重算，不能用旧摘要猜新表。输出字典和来源认证保留在摘要之外。

### 38.4 字面宏扫描及调用预算

**命题 38.5（保留初始目标的扫描执行器）。** 定理 38.4 接受时，其 F/R 分块可由同一实际来源上的纯 $\alpha$ 宏扫描实现。包括入口真实读和终端填充最终拒绝，来源调用至多 $H+4$。

证明。实际读 $g$ 后取该供应标签和读纤维的离线计划。按非空块端点 $c$ 递增，在 $c<H$ 时尝试一次右接实际 $\alpha^{H-c}$；它是一次完整守卫的宏，不能分解为若干可能部分接受的单叶。$c=H$ 时省略空上下文。早先端点拒绝不改入口来源，首个接受或末端隐式选择恰选中 $l<m\le c$。

F 块选中后，连续右接单叶 $\alpha$ 到第一次拒绝，若成功 $f$ 次，则 $f=H-(m+H-c)=c-m$，所以 $m=c-f$，由 F 行字典输出初始 $\tau$。R 块先尝试 $\rho$。拒绝时同一填充给 $m$，拒绝行字典输出目标；接受时真实读取 $E'=zB^{H-c}$，只在算术中右消去已知 $B^{H-c}$，再填充。此时 $f=c-n$，所以 $n=c-f$，接受列字典按 $(n,z)$ 输出初始目标。上带使这次接受后的下一替换尺寸已超过 $H$，不会遗漏更深合法分支。任何终端都执行最后一次非空单叶拒绝，即使 $f=0$。

若入口实际尺寸为 $m$，早先调用宏的端点都是不同的正整数且小于 $m$；包括选中宏在内的宏调用数 $v\le m$。F 总调用数为 $1+v+c-m+1\le H+2$，R 拒绝为 $1+v+1+c-m+1\le H+3$，R 接受为 $1+v+1+1+c-n+1\le H+4$，最后使用 $n\ge m$。入口读已由父层取得时只计一次。调用界不包含计划构造、标签供给与认证、上下文生成、算术位复杂度、输出、解码表或全部记忆；它也不声称最少调用。$\square$

### 38.5 实际的任意长最小障碍链

**定理 38.6（$2L+1$ 个目标的实际最小障碍与精确受限容量）。** 对每个 $L\ge1,H\ge8L+1$，令

$$
m_i=H-4L+4i\quad(0\le i\le L),\qquad a_i=m_i-4\quad(i<L),
$$

取下列非空正叶词的任意固定有序括号化，零长度子块省略：

$$
\begin{aligned}
U&=\beta^{2L}\alpha\beta^{2L}\alpha^{H-8L-1},&
V&=\alpha^H,\\
P_i&=\beta^4\alpha^{a_i}&&(0\le i<L),\\
N_i&=\alpha\beta^4\alpha^{a_i-1}&&(1\le i<L).
\end{aligned}
\tag{TM.3803}
$$

此实际族 $\mathcal C_{L,H}$ 有 $2L+1$ 个不同初始目标，全部位于上带；全族一标签不可恢复，而每个真子族一标签可恢复。对这个公开受限族，执行前任意补充标签的最小字母表与固定 §31 执行器档案后的补充最小字母表分别记为 $M_A(\mathcal C_{L,H};H)$、$M_B(\mathcal C_{L,H};H)$，则两者恰为 $2$。若 $L\ge2$ 且删去任一内部 $P_i$ 或 $N_i$，则受限容量为 $M_A=1,M_B=2$。

证明。由 $H\ge8L+1$，$a_i\ge4L-3\ge1$，所有词合法且非空。资源和窗为

$$
\begin{array}{c|c|c|c|c}
&\text{组成}&m&n&E_1\\ \hline
U&(H-8L,4L)&m_0&H&B^H\\
V&(H,0)&H&H&B^H\\
P_i&(a_i,4)&m_i&m_{i+1}&S^4B^{m_{i+1}}\\
N_i&(a_i,4)&m_i&m_{i+1}&S^{-4}B^{m_{i+1}}
\end{array}
\tag{TM.3804}
$$

共同 $E_0=A^H$。事实上 $B^4=1$，所以 $P_i,N_i$ 的首读是 $A^{a_i}=A^H$；$U$ 两个偶数 $B$ 块的符号乘积为一，首读也为 $A^{H-8L}=A^H$。下一窗的叶因子是 $B,S$，故 $P_i$ 给 $S^4B^{a_i}=S^4B^{m_{i+1}}$，$N_i$ 给 $BS^4B^{a_i-1}=S^{-4}B^{m_{i+1}}$；这里 $BS^4=S^{-4}B$。$U$ 给 $S^{2L}BS^{2L}B^{H-8L-1}=B^{H-8L}=B^H$。正规形唯一性与 $S$ 的无限阶使同行两窗不同；不同 $i$ 的 $n$ 不同，只有 $U,V$ 重复列 $(H,B^H)$。最小 $m+n$ 是 $2H-8L+4>H$，且所有 $n\le H$，故全为标签 $1$，目标由各自行列不同而互异。

补足同一来源的 Euler 认证。在原子卷定理 360.2 的顺序 $\mathbf x=(x_{00},x_{10},x_{01},x_{11})$、$\mathbf y=(y_{00},y_{01},y_{10},y_{11})$ 中，完整次数为

$$
\begin{array}{c|c|c}
U&(\lceil(H-8L)/2\rceil,\lfloor(H-8L)/2\rfloor,0,0)&(L,L,L,L)\\
V&(\lceil H/2\rceil,\lfloor H/2\rfloor,0,0)&(0,0,0,0)\\
P_i&(\lceil a_i/2\rceil,\lfloor a_i/2\rfloor,0,0)&(2,2,0,0)\\
N_i&(\lceil a_i/2\rceil,\lfloor a_i/2\rfloor,0,0)&(0,0,2,2)
\end{array}
\tag{TM.3805}
$$

表中第二、三列分别为 $\mathbf x,\mathbf y$。字面词从 $00$ 出发，终点为 $(H\bmod2,0)$；$a_i\equiv H\pmod2$。$U$ 在 $00$ 作第一个 $\beta$ 回路，到 $10$ 后作第二个回路，余下 $\alpha$ 往返；$P_i$ 的回路附着在 $00$，$N_i$ 的回路附着在第一片 $\alpha$ 到达的 $10$，$V$ 为纯 $\alpha$ 路径。这些路径逐边给出（TM.3805），边和为所列组成，出入差是起终点差。$U$ 的正 $\alpha$ 边把两个 $\beta$ 回路接通，其余正支撑也都与起点弱连通，包含最小 $H=8L+1$ 的零尾部。因此非负次数、完整流量和连通条件同时成立；三窗和资源属于同一实际正词，非独立拼出的坐标。

闭包已经给一个不可行证明：行 $m_0$ 的释放为 $m_1$，每个内部行 $m_i$ 的释放为 $m_{i+1}$，所以闭包到 $m_L=H$；$U,V$ 列的期限为 $H$，其第二大尺寸是 $m_0$，故 $B(0)=H$，违反严格期限。

另给全动作的直接下界。跟随最小行 $U,P_0$ 的共同记录直到首次 $\rho$。此前它们同尺寸、同首读，所有拼接守卫和读相同；不同目标与有限停止迫使发生首次替换。设此前接受上下文的累计增量为 $D_0\le D_1$，共同历史的尺寸区间为 $(l,u]$，$l<m_0,u=H-D_0$，替换截止为 $c=H-D_1\le u$。若 $c<m_1$，$U,P_0$ 都拒绝并永久合并，所以成功须 $c\ge m_1$。该共同历史也包括尺寸 $m_1$ 的两行：其尺寸落在 $(l,u]$，首次替换前控制仅见尺寸阈值及共同首读。避免它们双拒绝要求 $c\ge m_2$。逐行迭代至 $c\ge m_L=H$，因此 $D_1=D_0=0$。不存在任何已接受正上下文；此前被拒探针在所有 $m\ge m_0$ 上均拒绝。于是 $U,V$ 共享这份历史，首次 $\rho$ 都接受，当前尺寸同为 $H$，当前读同为 $B^H$，下一尺寸超限，当前商相等而初始组成不同。命题 38.1 排除一切后续恢复。这覆盖任意 $\beta$ 材料、左右位置、宏长度、适应控制和档案，不仅是纯 $\alpha$ 扫描失败。

逐一给删除协议。删 $U$ 或 $V$ 后所有接受列单射，一块 R($H$) 即可。删 $P_0$ 后最小行只剩 $U$，先以端点 $m_0$ 的 F 块取得它，再对拒绝尾部使用 R($H$)，尾部列单射。删内部 $P_i$ 或 $N_i$ 时，先用端点 $m_i$ 的 R 块：该块的拒绝行是 $U$ 及尺寸 $m_i$ 的单个幸存者，尺寸不同；所有更早的 $P_j,N_j$ 在 $n=m_{j+1}\le m_i$ 接受，接受列互异。所以该块安全。余尾已不含 $U$，以 R($H$) 结束。每种分块由命题 38.5 字面实现。任意真子族包含于某个单目标删除，限制该有限协议仍正确，故全为一标签可行。

全族至少两标签；以一标签隔离 $U$，另一标签给列单射的其余族，得到两标签上界。固定 §31 档案 $\Gamma_H$ 在标签 $1$ 上的键为 $(1,E_0,E_1,n)$，此族恰有一个两目标纤维 $U,V$，其余单点。$U,V$ 在该固定执行器中首读相同，首次替换都接受并读 $B^H$，下一替换都拒绝，尺寸已是 $H$，终端填充也都立即拒绝；动作身份及完整记录因此相同。即使保留完整固定记录，补充仍至少两值，以在该唯一纤维区别二者达到两值上界，得 $M_B=2$。删内部链接时 $U,V$ 仍在，所以 $M_B=2$，而上述协议给 $M_A=1$。这些都是该公开实际子族的容量，不能冒充全家族公式。$\square$

**推论 38.7（不存在固定禁形元数）。** 没有一个与 $H$ 无关的有限整数 $K$，使所有实际上带族的一标签可行性都能由其至多 $K$ 个目标的子族是否可行决定。

证明。选 $L$ 使 $2L+1>K$，再取 $H\ge8L+1$。定理 38.6 的整个族不可行，而每个至多 $K$ 目标的子族都是真子族，均可行。这直接反驳所述判据，包含以对、三元或四元禁形为完整条件的主张。稀疏闭包仍精确，因为其强制分量可以承载任意长链，而不要求障碍有固定大小。$\square$

### 38.6 来源状态与适用边界

本章的书面前置是本卷定理 30.2、§34 的全动作截止条件、§35 的共同历史配对，以及原子卷 §§359–360 的联合三窗正规形与完整 Euler 认证。释放—期限闭包、实际链及其删除协议在此给出了普通数学证明，不能以未收入正文的推导代替这些证明。Panteleev 的 [arXiv:1412.0034v1](https://arxiv.org/abs/1412.0034v1) 和 van den Bos–Vaandrager 的 [arXiv:1907.11034v2](https://arxiv.org/abs/1907.11034v2) 是初态识别和适应区分的成熟背景，没有供应这里的具体轮廓、链或调用公式。本章不作 Lean 核验或文献原创性主张。

严格上带、共同实际历史、真实读纤维和初始目标字典都是承重条件。可行性摘要不是来源重构，也不是任意限制下的自动更新状态；有限供给表及输出的认证成本仍在。全家族最优 $M_A(H)$、尖锐节省阶数、总记忆最优性及更深层压缩均未由本章解决。

## 39. 两层实际取得的行—对角运输、最早准入端点与记录恢复

本章沿用 §38 的固定合同、供应标签和初始目标。假设声明的每个初始实际来源均满足

$$
\lambda _3=m+2n>H.
\tag{TM.3901}
$$

这允许初始标签 $0,1,2$ 任意混合。§35 已给这个范围的完整两层截止条件；下面将每个第二层证书消为直接的行—对角轮廓，再用固定端点的交换证明消去首层分块回溯。所有子表都来自同一个实际宏、同一个初始族和同一条真实分支，不能把各边缘最优方案拼成一个未共同实现的协议。

### 39.1 初始有限关联表与一宏运输

**定义 39.1（初始表、阈值和运输后的行列）。** 实际读初始 $E_0=g$，固定一个非空 $(h,g)$ 纤维，依命题 38.1 按初始目标去重为 $C$。每个目标保留实际认证与输出关联。标签 $0$ 只用 $(m,\infty)$ 的拒绝哨兵，不填不可用的 $E_1,E_2,m+n$；标签 $1,2$ 保留 $(m,n,z)$，$z=E_1$，标签 $2$ 再保留 $w=E_2$。令 $R_0(m)$ 为初始行的第二大 $n$，单目标行取零，资源重复按不同目标计数。固定 $g,m$ 至多一个标签 $0$ 目标 $(0,g,m)$，所以初始 $R_0$ 有限。

对初始区间 $C(l,c)=\{\tau:l<m\le c\}$，选整数

$$
d=H-c,\qquad \max(0,2c-H)\le t\le c,\qquad r=c-t.
\tag{TM.3902}
$$

于是 $0\le r\le d$。$d>0$ 时选一个实际右宏 $K=\alpha^{d-r}\beta^r$，其三个资源增量为

$$
(D_0,D_1,D_2)=(d,d+r,2d+r)=(d,H-t,d+H-t).
\tag{TM.3903}
$$

$d=0$ 时 $c=t=H,r=0$，省略拼接，不调用空来源。为这个省略情形，仅在因子算术中约定 $k_i=1$；非空情形 $k_i=E_i(K)$ 是实际已知宏的窗口。

首次 $\rho$ 拒绝部分为 $n>t$，它的行安全性恰是

$$
\max_{l<m\le c}R_0(m)\le t.
\tag{TM.3904}
$$

首次接受后真实读 $E'=zk_1$，在算术中右消去已知 $k_1$。每个所得 $z$ 纤维保留接受目标子表

$$
A_z(l,c,t)=\{\tau:l<m\le c,\ n\le t,\ E_1=z\}.
$$

置 $a=H-t$、$p=m+n+d$。在这个子表上定义行释放 $R_z(n)$ 为同一 $n$ 行各不同初始目标的 $p$ 的第二大值，单目标行取零；即使 $p>t$ 也保留为超限释放。对 $p\le t$ 的多目标列 $(p,w)$，取其第二大 $n$ 为 $s$，令 $D_z(s)$ 为这些列中最小 $p$，空值为 $t+1$，并令 $B_z(e)=\min_{s>e}D_z(s)$。同资源的不同目标仍按目标重数参与极值。

因为 $p\le t$ 蕴涵 $m+n=p-d\le t\le H$，每个被使用的 $w$ 都属于初始标签 $2$ 的已认证字段。初始标签 $1$ 的 $m+n>H$，不能进入这些列；不需要也不允许给它供应隐藏第三窗。决策表只需 $z$ 的相等类，以及固定 $z$ 内 $(m+n,w)$ 的相等类和尺寸坐标。数值窗口、实际来源认证、在线匹配及目标值由另一份解码关联保存。

**引理 39.2（直接行—对角轮廓与实际子层等价）。** 每个 $A_z(l,c,t)$ 由同一宏及首次替换形成的真实当前坐标是

$$
x=n+a,\qquad y=p+a=m+n+2d+r,\qquad E=zk_1,
\tag{TM.3905}
$$

且 $x+y=\lambda _3+3d+2r>H$。在归一化截止轴 $e=b-a$ 上，以上限坐标 $t$ 对 $R_z,D_z$ 运行定理 38.4 的闭包，恰好决定这个实际子层的所有允许动作延续能否恢复初始目标。它不搜索第二层分块；遇超 $t$ 释放即失败。

证明。实际拼接增量（TM.3903）与一次 $\rho$ 给（TM.3905），相加给所述严格上带。真实上限仍为 $H$。子层端点 $b$ 的纯 $\alpha$ 宏长度是 $H-b=t-e$；它的实际拼接守卫与后续替换守卫分别为

$$
x+(t-e)\le H\ \Longleftrightarrow\ n\le e,
\qquad
y+(t-e)\le H\ \Longleftrightarrow\ p\le e.
\tag{TM.3906}
$$

因此物理截止块在平移后正是原 $n$ 轴的截止块。$b$ 低于最小占用 $x$ 的端点没有候选，省略即可；所有占用端点对应 $1\le e\le t$，末端 $b=H$ 对应 $e=t$。没有把上限改成 $t$，也没有假装平移后的整数对是另一种物理来源。

接受第二次替换的列读为 $wk_2B^{t-e}$。右侧是同一宏的固定已知因子及该子宏因子，故在一个固定块内，真实读相等恰等价于原 $w$ 相等；资源列为 $p$，等价于原 $m+n$，因为 $d$ 固定。拒绝目标在 $n$ 行上的安全性为第二大 $p$ 不超过 $e$。接受列的尾部第二大 $n$ 决定期限，理由与引理 38.3 相同：$n\le p\le e$ 使全部该列尾部成员进入区间。于是实际上带块条件经平移恰为 $R_z,D_z$ 的条件，F 条件也完全对应。

当实际 $y>H$ 时 $p>t$，该来源在任一子层截止均拒绝；以有限 $p>t$ 代替无穷哨兵不改变任何 $e\le t$ 的比较。两个此类目标在同一行产生超限释放而失败。所有列仅在 $p\le t$ 时建立，因此没有访问不存在的运行时第三窗。定理 38.4 的完整闭包及其保留初始目标的实际执行器逐块运输回来，证明两个方向。$\square$

### 39.2 同一宏的准入关系与最早端点

**定义 39.3（首层块准入）。** 令 $G(l,c,t,z)$ 是引理 39.2 的子层闭包结果。定义

$$
\mathcal A(l,c)\ \Longleftrightarrow\
\exists t\in[\max(0,2c-H),c]\cap\mathbb Z:
\left[\max_{l<m\le c}R_0(m)\le t\right]
\ \land\ \bigwedge_{A_z\ne\varnothing}G(l,c,t,z).
\tag{TM.3907}
$$

空接受侧不增加义务。该存在量词的同一个 $t$ 决定整个初始块、同一个实际宏、所有真实接受纤维和它们的表；只有真实读出 $z$ 后才允许采用该纤维自己的子层计划。另定义 $\mathcal F(l,c)$ 为该块每个初始 $m$ 行至多一个目标。式（TM.3907）是联合关系，不是对不同实现分别优化再取交。

**定理 39.4（最早准入端点的全动作精确算法）。** 在（TM.3901）的实际初始表中，从 $l=0$ 开始；若剩余行都单目标，发出 F 块到 $H$ 并结束。否则找首个歧义尺寸 $s>l$，剥去它之前的占用单目标前缀为 F 块，置 $l=s-1$。依次测试 $c=s,s+1,\ldots,H$，选最小满足 $\mathcal A(l,c)$ 的 $c$ 及其中任意一个见证 $t$，发出其 R 块，置 $l=c$ 并重复；没有准入端点则失败。该算法接受，当且仅当存在使用给定补充标签的忠实确定性协议逐点有限取得初始 $q_H$。

证明。§35 的阶段压缩保持准确的两个增量与完整历史：任一首层叶的端点是 $c=H-D_0$，其宏可替为同组成的 $K(d,r)$，$0\le r\le d$。停止叶已满足 F 条件。对首次尝试 $\rho$ 的叶置 $t=c-r$；若 $t<0$，非空实际来源有 $n\ge1>t$，故该叶的首次 $\rho$ 全部拒绝。此时在固定叶记录和共同 $E_0=g$ 下，同一 $m$ 的行有相同当前商 $(0,L_0gR_0,m+d)$，定理 30.2 迫使它们携带的初始 $\tau$ 相同。因此保留原端点 $c$ 将该叶归为 F 块，由既有 F 执行器取得 $m=c-f$，按该叶保留的初始目标字典输出 $\tau$。余下 R 块均有 $t\ge0$，结合 $0\le r\le d=H-c$ 得 $\max(0,2c-H)\le t\le c$，正是（TM.3902）。其拒绝部分安全性等价于（TM.3904）；由（TM.3901）所有首次接受子层均为实际上带，引理 39.2 将每个完整子层延续存在性精确替为 $G$。所以任一全动作成功协议给一份只含 $\mathcal F$ 与 $\mathcal A$ 的首层分块；反向由这些条件的实际宏与闭包执行器逐块执行，恢复原目标。这里复用定理 35.4 的全阶段必要性，而子层替换的等价已经逐项证明。

为消去首层分块回溯，须验证固定端点和固定阈值的遗传性。一个准入块删去任意目标后，仍用旧 $c,t$；其拒绝行保持目标恒定，接受纤维成为旧实际子表的限制。旧真实成功延续限制到这个子族仍正确，所以精确子层闭包仍通过。其宏未变，所有资源与来源实现仍相容。F 安全同样遗传。这里不是声称旧轮廓能直接更新，而是允许从实际限制表重算。

因此剥去单目标前缀可通过限制原分块而保持可行性。第一个剩余行 $s$ 歧义，其可行首块必须为 R，设旧端点为 $d_0$，旧阈值为 $t_0$。它证明 $\mathcal A(l,d_0)$，故算法的最小端点 $c_*\le d_0$。用算法准入的前缀 $(l,c_*]$ 替换旧块前部，对旧块余部 $(c_*,d_0]$ 仍用旧端点 $d_0$ 和旧阈值 $t_0$，遗传性保证其安全。位于余部的来源尺寸 $m>c_*$，对新前缀宏的守卫拒绝，故其实际来源保持原样；它没有先接受新材料再尝试旧计划。后续旧块全部不变，得一个可行的剩余分块。按剩余占用行归纳，选择最小准入端点不会丢失可行延续。

每次 R 块至少删除首个歧义行，算法有限。若找不到准入端点，任何所需首 R 块都不存在，所以原全动作协议不存在。反向若算法结束，所有输出块均有实际执行器，有限填充给逐点停止。两方向合成结论。保留旧端点和阈值是交换证明的必要步骤；它不允许穿过占用行移动端点，也不允许用部分接受的探针代替宏。$\square$

**命题 39.5（有限测试量与占用行计算条件）。** 对一个含 $N\ge1$ 个不同初始目标的给定纤维，最早端点算法至多测试 $H$ 个端点和 $H(H+1)/2$ 个阈值。若对子表仅处理占用行和实际列，以排序及顺序扫描构造、执行轮廓，则可用 $O(H^2N\log(N+1))$ 次键比较和整数操作完成可行性计算。该界不计数值窗口的位运算、来源认证或解码表生成。

证明。一个尾部按递增顺序测试至所选 $c$；下个尾部从大于 $c$ 的尺寸开始，此前端点不再测试。失败也只终止这一递增扫描，所以总端点不超过 $H$。在端点 $c$，阈值区间长度为 $\min(c,H-c)+1\le H-c+1$，总数至多 $\sum_{c=1}^H(H-c+1)=H(H+1)/2$。

固定一次 $(l,c,t)$，从至多 $N$ 条存活行建立 $z$、$n$ 和 $(p,w)$ 分组，排序花 $O(N\log(N+1))$。各非空 $z$ 表的行数总和不超过 $N$。在每表中按占用行排序并保留期限位置的后缀最小值，闭包用只前进的行指针吸收 $n\le e$ 的行；剥前缀及查询期限也按已排序位置前进。或直接使用定理 38.4 的分量和跨度扫描，均只需该表占用数据的线性操作。全部子表相加为 $O(N)$，不是每个纤维扫描 $H$ 个空位置。乘以阈值数量即得所述界。若实现为每个读纤维密集扫描 $H$，此证明的操作界不适用。这里只给条件明确的算法上界，不宣称输出表、控制记忆或认证的最优成本。$\square$

### 39.3 字面执行、原始目标输出与记录等价

**定理 39.6（两层执行器、紧凑记录和调用界）。** 定理 39.4 接受时，可在同一个实际来源上字面执行其计划，保留初始目标输出；来源调用保守地至多 $2H+6$。给定供应标签、入口真实读和该计划及解码器，选中块身份、真实 $\rho$ 响应位、合法归一化读身份及终端填充成功次数构成与这个执行器完整动作响应记录等价的记录。

证明。首层按端点递增扫描选定 $K(d,r)$ 宏，$d=0$ 省略。早先拒绝不改初始来源；选中 F 块后填充至拒绝，$m=c-f$，用初始行字典输出 $\tau$。选中 R 块后尝试 $\rho$。拒绝时同一填充和拒绝行字典输出初始目标；接受时真实读 $E'=zk_1$，按实得 $z$ 进入引理 39.2 的子层计划。归一化仅作算术右消去，不给未知来源施逆。

子层端点 $e$ 执行一个实际 $\alpha^{t-e}$ 宏，物理端点为 $b=e+H-t$，$e=t$ 时省略。子层 F 填充成功 $f$ 次给 $n=e-f$，由该行的目标字典输出。子层 R 拒绝也给 $n=e-f$，用拒绝行字典；若接受，真实读取

$$
E''=wk_2B^{t-e},\qquad
w=E''\bigl(k_2B^{t-e}\bigr)^{-1}
   =E''B^{-(t-e)}k_2^{-1}.
\tag{TM.3908}
$$

乘积次序不可交换。终端填充给 $p=e-f$、原 $m+n=p-d$，用接受列 $(p,w)$ 在已取得的 $z$ 纤维中输出初始目标。子层上带保证此接受后不能再取得更深窗；每个终端都含一次最终非空单叶拒绝，即使填充零次成功。整个执行没有尺寸读口、被拒候选读、来源复制、重置、导航或来源取消。

调用计数也可在归一化轴上直接作。若首层接受后的原 $n$ 已给定，子层此前宏端点都是小于 $n$ 的不同正整数，含选中宏的宏数不超过 $n$。其 F、R 拒绝、R 接受的计数分别至多 $1+n+e-n+1$、再加一次 $\rho$、或再加一次 $\rho$ 和一次真实读，R 接受填充为 $e-p+1$ 且 $p\ge n$。所以包括子层入口读的总数至多 $t+4$，正与命题 38.5 的计数对应。首层宏至多 $H$ 次，初始读一次，首次 $\rho$ 一次；它接受后的真实读已经是子层入口读，不重复支付。因此首次接受路径总数至多 $H+1+1+(t+4)\le2H+6$。首层终端路径至多 $H+3$。这是存在性预算，不是最少调用结论，且所有离线表、上下文、供给、算术、记录及输出成本独立。

从完整记录提取选中块、$\rho$ 位、归一化读和填充计数，得到所述紧凑记录。逆向给定计划、$H,h,g$ 及这些字段，计划决定每个宏身份及顺序；选中块决定全部早先宏拒绝和选中宏接受；$\rho$ 位决定真实分支；归一化读与已知因子按（TM.3908）及 $E'=zk_1$ 重建实际读；填充计数决定所有成功单叶及最后拒绝。故该执行器完整记录被重建。字典由终端坐标给初始 $\tau$。这只是一份给定执行器、给定计划和解码器的记录等价；它不编码任意来源历史，也不自动给计划本身的存储界。$\square$

### 39.4 最早端点为 23 的实际混合例

**命题 39.7（实际四源的最早端点及 $\beta^2$ 宏）。** 取 $H=25$ 和固定括号正词

$$
P=\beta\alpha^8,\qquad Q=\alpha^2\beta\alpha^6,\qquad
X=\beta^3\alpha\beta^2\alpha^{11},\qquad Y=\beta\alpha^{20}.
\tag{TM.3909}
$$

它们共同 $E_0=B,E_1=S$。$P,Q$ 为标签 $2$，$(m,n,m+n)=(9,10,19)$，分别有 $E_2=S^{-6}A,S^{-2}A$；$X,Y$ 为标签 $1$，资源分别为 $(17,22,39),(21,22,43)$。全部 $\lambda _3>25$。首个歧义行是 $9$，最早准入端点为 $c=23$，该端点的见证是 $t=21,r=d=2$，实际宏 $\beta^2$。

证明。$P,Q$ 的首读均为 $B$，下一读分别是 $SB^8=S$、$B^2SB^6=S$。二次叶因子为 $S,S^2A$，故二次读是 $S^2AS^8=S^{-6}A$ 和 $S^2(S^2A)S^6=S^{-2}A$，使用 $AS^j=(-1)^jS^{-j}A$。$X$ 的首读为 $B^3AB^2A^{11}=B$，下一读为 $S^3BS^2B^{11}=S$，$Y$ 给 $BA^{20}=B,SB^{20}=S$。组成计数给表中资源，$P,Q$ 的 $\lambda _3=29$，$X,Y$ 分别为 $61,65$；正规形唯一性保证低对第三窗不同。

完整 Euler 次数采用原子卷顺序：

$$
\begin{array}{c|c|c}
&\mathbf x&\mathbf y\\ \hline
P&(0,0,4,4)&(1,0,0,0)\\
Q&(1,1,3,3)&(1,0,0,0)\\
X&(0,0,6,6)&(2,1,1,1)\\
Y&(0,0,10,10)&(1,0,0,0)
\end{array}
\tag{TM.3910}
$$

逐词从 $00$ 读到 $01$ 给出这些边次数，故出入差为起终点差，次数和给相应组成。$P,Q,Y$ 的 $00\to01$ 边连上在 $01,11$ 的 $\alpha$ 路径，$Q$ 多出的 $00,10$ 往返也连接到起点。$X$ 的两个 $\beta$ 回路经 $01\to11$ 的正 $\alpha$ 边相连。全部正支撑弱连通，故这些资源和窗口有完整的同一实际来源认证。

对任何含首个歧义行的 $c\le21$，$d\ge4$。宏在低对上接受，其潜在第二替换尺寸为 $19+2d+r\ge27>25$；即使首次替换也拒绝，低对仍保持同尺寸同可见窗，初始第三窗的差已不可恢复。因此没有此类端点准入。$c=22,d=3$ 时，$r=0$ 使高对首次替换都接受，当前同尺寸 $25$、同读 $SB^3$，下一替换超限，永久合并不同初始目标；$r\ge1$ 则低对的第二候选为 $19+6+r>25$，仍不可恢复。端点空隙并不绕开这个宏增量。

$c=23,d=2,r=2,t=21$ 时，$\beta^2$ 在全族接受。高对首次候选为 $22+4=26$，均拒绝，填充取得初始 $m=17,21$，两者可解码。低对首次候选为 $10+4=14$，均接受；其子表同一 $n=10$ 行的释放为 $p=19+2=21$，两列的 $w$ 不同，无期限障碍。闭包取 $e=21=t$，省略子宏，第二次替换候选恰为 $25$，真实读分开低对。于是端点 $23$ 准入且是最早者。这里给的是所显示实际例及其计划，不重新发布一般四源资源定律。$\square$

### 39.5 资源、边界、执行次序与记忆的有条件回接

**命题 39.8（既有资源及三窗运输的恢复接口）。** 在任意合法单出现历史上，令 $j$ 为已接受 $\rho$ 次数，$v_0=(m,n)^{\mathsf T}$ 是初始相邻资源，$T=\begin{pmatrix}0&1\\1&1\end{pmatrix}$。存在由已知上下文及真实动作次序确定的向量 $b$，使实际当前资源为 $v=T^jv_0+b$。若当前相邻资源对被合法取得或明确供应，且 $j,b$ 保留，则唯一恢复 $v_0=T^{-j}(v-b)$，进而恢复初始组成。对合法真实读 $L_iE_{j+i}(t)R_i$，保留已知因子次序即可算术恢复该窗；若整个归一化连续三窗被取得或供应，既有 $F^6=\operatorname{id}$ 再恢复初始三窗。

证明。单出现不变量使一次上下文拼接在相邻资源上增加其已知 $(d,d+r)$；一次 $\rho$ 将资源对及此前上下文贡献同乘 $T$；拒绝不变。按实际动作词归纳得 $T^jv_0+b$。两段的参数 $(T^{j_1},b_1),(T^{j_2},b_2)$ 按先后次序合成为 $(T^{j_1+j_2},T^{j_2}b_1+b_2)$，因此无序累计总量不能代替 $b$。$\det T=-1$，整数逆存在，求逆式唯一；再用初始 $a_0=2m-n,b_0=n-m$ 得组成。这个恒等式没有给资源对增加一个观察端口，单个当前叶数或单个 $j$ 也不供应缺失坐标。

窗口的实际已知因子按引理 35.1 在左右拼接及替换下有序更新。对真实读作 $L_i^{-1}(L_iE_{j+i}R_i)R_i^{-1}$ 得该窗，逆元只施于已知因子。被拒候选没有读，不能代入这个等式。连续三窗为既有 $F^jW_3(t)$，$F^6=\operatorname{id}$ 给可逆 $F^{-j}$，得到所述条件恢复。代数三窗与资源恢复均是既有接口的应用，不是对合法取得的替代证明。$\square$

在本章执行器中，最终字典输出的是初始 $q_H$：标签 $0$ 恢复恰为 $E_0,m$；标签 $1$ 恢复组成及前两窗；标签 $2$ 恢复组成及三窗，并由既有 $F$ 律决定完整数学窗口历史。未被初始目标保留的窗口不因紧凑记录而被宣称取得。完整记录和紧凑记录的等价需要供应计划、上下文身份及解码器；丢弃这些条件会同时丢弃已知因子和资源贡献。它不是物理时长恢复。

不同括号的 $\langle\langle\alpha,\alpha\rangle,\alpha\rangle$ 与 $\langle\alpha,\langle\alpha,\alpha\rangle\rangle$ 有相同叶词、组成、全部窗口及行为商，却是不同原树。原子卷推论 360.3 还描述全部同窗 Euler 词及括号纤维。因此本章的恢复不唯一重建括号、原树历程或物理空间；物理空间、时间、边界和记忆的解释还须供应忠实的物理模型。

### 39.6 来源状态与未覆盖范围

本章直接复用 §§30、34、35 的行为同余、实际双增量锥、整阶段压缩及有序因子运输，§38 的上带闭包提供完整子层算法；实际例依原子卷 §§359–360 的来源条件认证。识别文献仍取 §38.6 所列成熟背景，不把它们当作行—对角公式、最早端点交换或 $2H+6$ 预算的供应者。以上均为普通数学证明，不构成 Lean 核验或原创性主张。

严格 $\lambda _3>H$ 保证本章全体子层均属上带。若某个具体宏另外认证所有接受子行上带，可单独使用同一局部轮廓，但这不推出任意深度的必要判据。$H=3$ 的初始 $\alpha$ 有 $(m,n,\lambda _2,\lambda _3)=(1,1,2,3)$，连续第三次纯替换在等号上仍合法，故删除严格假设会遗漏深层分支。一般全家族继续由 §35 的嵌套条件供应完整性；把未简化的后续 oracle 重新命名不构成这里的压缩。全家族精确 $M_A(H)$、尖锐节省、补充关系的生产认证、最少调用、总记忆和物理恢复仍未解决。

## 40. 实际第三窗交叠族、根摘要失效与正确子层区分

本章仍以同一初始实际来源的 $q_H$ 为目标，并允许 §30 的全部确定性适应协议、任意正的左右上下文和任意已取得记录。来源读只有真实当前 $E$；补充标签为运行前供应的同源函数值。$M_A(\mathcal F;H)$ 仅指所声明公开有限实际族的最小供应字母表。下面把第三窗交叠变成一个精确局部关系，展示根层上带摘要在缺失假设时的失败，以及运输到正确实际子层后恢复精确性的方式。

### 40.1 全尺度正词与连接 Euler 证书

**定理 40.1（实际第三窗交叠族的精确一／二标签判据）。** 对任意整数 $k\ge0$，令

$$
H=8k+40,\qquad
J_k=\{w\in\mathbb Z:w\text{ 为奇数},\ -2k-5\le w\le2k+7\}.
$$

选不同 $w_1,w_2\in J_k$，置 $W=\{w_1,w_2\}$，取正叶词的任意固定有序括号化：

$$
\begin{aligned}
U_+&=\beta^5\alpha^{2k}\beta\alpha^{2k+1}\beta^6\alpha,\\
U_-&=\alpha^{2k}\beta^5\alpha^{2k+1}\beta^6\alpha\beta,\\
V_w&=\beta\alpha^{2k+7-w}\beta\alpha^{2k+6+w}\beta^2\alpha
\quad(w\in W).
\end{aligned}
\tag{TM.4001}
$$

零次子块省略，整个词均非空。对实际族 $\mathcal F_{k,W}=\{U_+,U_-,V_{w_1},V_{w_2}\}$，有

$$
M_A(\mathcal F_{k,W};H)=
\begin{cases}
1,&W\cap\{-1,1\}=\varnothing,\\
2,&W\cap\{-1,1\}\ne\varnothing.
\end{cases}
\tag{TM.4002}
$$

证明。先给完整的共同来源认证。全部指数非负，且 $2k+6+w\ge1$。其资源和窗是

$$
\begin{array}{c|c|c|c|c|c}
&\text{组成}&m&n&m+n&E_2\\ \hline
U_+&(4k+2,12)&4k+14&4k+26&H&S^2\\
U_-&(4k+2,12)&4k+14&4k+26&H&S^{-2}\\
V_w&(4k+14,4)&4k+18&4k+22&H&S^{2w}
\end{array}
\tag{TM.4003}
$$

共同 $E_0=1,E_1=-1$，全部初始标签 $2$、$\lambda _3=m+2n>H$。表中完整八边认证，在原子卷顺序 $\mathbf x=(x_{00},x_{10},x_{01},x_{11})$、$\mathbf y=(y_{00},y_{01},y_{10},y_{11})$ 为

$$
\begin{array}{c|c|c}
U_+&(k+1,k+1,k,k)&(3,3,3,3)\\
U_-&(k,k,k+1,k+1)&(3,3,3,3)\\
V_w&(A_w,A_w,B_w,B_w)&(1,1,1,1)
\end{array},\qquad
A_w=k+\frac{7+w}{2}\ge1,\quad B_w=k+\frac{7-w}{2}\ge0.
\tag{TM.4004}
$$

所有数为非负整数，$\alpha$ 和 $\beta$ 边和给表中组成，出入差全为零、终点为 $00$。字面词也直接给这些 Euler 路：$V_w$ 先到 $01$，作 $B_w$ 个 $\alpha$ 二边往返，再由 $\beta$ 到 $00$；接着走 $2A_w-1$ 片 $\alpha$ 到 $10$，作一个 $\beta$ 二边回路，最后由 $\alpha$ 回 $00$。$U_+$ 的前五片 $\beta$ 在 $00,01$ 往返后到 $01$，走 $2k$ 片 $\alpha$，再由 $\beta$ 回 $00$，走 $2k+1$ 片 $\alpha$ 到 $10$，作三次 $\beta$ 回路后由 $\alpha$ 返回。$U_-$ 先作 $k$ 次 $q=0$ 的 $\alpha$ 回路，五片 $\beta$ 到 $01$，$2k+1$ 片 $\alpha$ 到 $11$，六片 $\beta$ 往返到 $11$，再由 $\alpha\beta$ 经 $01$ 回 $00$。逐段计数恰为（TM.4004），包括 $k=0$ 及 $B_w=0$ 的端点。

两个 $\beta$ 二边回路均为正。$U_+$ 的 $q=0$ 正 $\alpha$ 对把两回路接通，$U_-$ 的 $q=1$ 正 $\alpha$ 对把它们接通；$V_w$ 始终有 $A_w\ge1$ 的 $q=0$ 正对。因此全部正支撑与起点弱连通，非负流量并未省略连通条件。用原子卷（360.3）计算整数参数，三者均为 $u=v=0$、状态 $00$，第三整数分别为 $1,-1,w$，因为它等于 $x_{10}-x_{01}$。定理 359.3 给三窗

$$
L(0,0,w)R_{00}=(1,(-1)^w,S^{2w}),
$$

正是（TM.4003）的共同前两窗及第三窗。故资源与三窗属于同一实际正词。$S$ 无限阶使 $U_+,U_-$ 目标不同，两个 $V$ 目标不同；即使 $w=\pm1$ 与某个 $U$ 第三窗相同，组成不同仍使初始目标不同。

若 $W$ 避开 $\{-1,1\}$，直接实际读 $E_0$，作首次 $\rho$ 并真实读共同 $E_1=-1$，作第二次 $\rho$，候选尺寸在所有来源上恰等于 $H$，再真实读 $E_2$。四个 $E_2$ 互异，供给的实际族解码器返回对应初始目标。该协议为五次来源调用，无隐藏尺寸字段。对任意交叠情形，两标签总足够：一标签供应 $U$ 对的成员资格，另一标签供应 $V$ 对资格；每对的第三窗内部互异，同一两次替换协议恢复。这给两值上界，标签生产与认证另计。

现在证交叠时的全动作下界。首次替换前，最小 $m$ 行是 $U_+,U_-$，它们同组成、同首读、同下一窗，但初始第三窗不同；其 $m+n=H$。若一个正上下文在这对上接受，无论左或右，其 $D_2=D_0+D_1>0$ 将当前第二替换尺寸增到 $H+D_2>H$，当前商至多保留共同前两窗和共同组成。因此同记录下两目标永久合并，违背命题 38.1。成功协议不能在最小行接受任何正上下文；在它上拒绝的上下文也在更大 $V$ 行拒绝。此前实际读均共同，所有拒绝不改来源，所以四源共享完整前缀。不同目标与逐点有限停止迫使一次 $\rho$，它在全族接受，真实当前读同为 $-1$。

首次替换之后，最小当前行变成两个 $V$，尺寸 $4k+22$；$U$ 行为 $4k+26$。每个来源的下一替换尺寸都是 $H$。两个 $V$ 有不同下一窗，故任何在该最小行接受的正上下文都把下一尺寸抬到 $H$ 以上，当前标签变 $0$，同尺寸同读，永久合并不同初始目标。成功延续因此不能在 $V$ 行接受上下文；在它上拒绝的上下文在更大 $U$ 行也拒绝。当前读共同，拒绝不改来源，四源仍共享记录，有限停止再次迫使 $\rho$。它在全族以候选尺寸 $H$ 接受。

若 $w_i=1$，$V_{w_i}$ 与 $U_+$ 此时同当前商 $(0,S^2,H)$；若 $w_i=-1$，与 $U_-$ 同当前商 $(0,S^{-2},H)$。下一替换资源已超过 $H$，这确为完整当前商相等，而初始组成不同、所需目标不同。完整过去记录也相同，所以任何后续控制和任意大档案都不能恢复。这覆盖任意正词、任意宏长度、左右位置、被拒探针及适应选择，给两标签下界，与上界合成（TM.4002）。$\square$

### 40.2 同根摘要的不同答案及真正的子层轮廓

**命题 40.2（根摘要不足与首次替换后轮廓精确）。** 在定理 40.1 的同一 $k,H$ 下，各 $W$ 的全部初始 $(\text{标签},m,n,E_0,E_1)$ 多重集相同；把 §38 的 $R,D$ 公式无条件用于这些标签 $2$ 根表，所得轮廓也相同，却不能决定可恢复性。真实首次 $\rho$ 后的正确上带子表，则由 §38 的轮廓精确区分交叠与不交叠。

证明。由（TM.4003），根表占用两个行，每行两个目标，同列键为各自 $(n,-1)$。其无条件轮廓为

$$
\begin{aligned}
R(4k+14)&=4k+26,&D(4k+14)&=4k+26,\\
R(4k+18)&=4k+22,&D(4k+18)&=4k+22,
\end{aligned}
\tag{TM.4005}
$$

其余 $R=0,D=H+1$。根闭包到 $4k+26$，期限已为 $4k+22$，对每个 $W$ 都失败。可是 $W=\{-1,1\}$ 的容量为 $2$，$W=\{3,5\}$ 的容量为 $1$，而这些奇数在全部 $J_k$ 中都合法。故不仅这段错误算法失败：任何仅依 $H,R,D$ 或所列完整前两窗多重集的函数都无法决定答案，因为其输入相同而正确答案不同。这里比较的是可行性，不是完整初始目标相等；第三窗关联恰是根摘要遗漏的信息。

实际首次 $\rho$ 后所有当前读为 $-1$。$V$ 行当前 $m'=4k+22$，$U$ 行当前 $m'=4k+26$，下一资源均为 $H$，下一窗分别为 $S^{2w}$ 和 $S^{\pm2}$。此时所有来源严格满足当前 $m'+n'>H$，可合法使用 §38。两个歧义行的释放都为 $H$，最小闭包到 $H$。若两指数集合不交，所有接受列 $(H,E_1(\text{当前源}))$ 单射，期限为 $H+1$，闭包通过；若交叠，重复列的第二大当前尺寸为 $4k+22$，期限为 $H$，闭包失败。首次节点尚未有不同目标的同当前商碰撞，因为匹配的 $U,V$ 尺寸不同；轮廓检测的是随后被迫合并。这证明运输到真实子层的摘要保留了根层遗漏的关系，并与（TM.4002）一致。$\square$

**推论 40.3（添加真实标签 $1$ 来源仍有同一交叠判据）。** 向 $\mathcal F_{k,W}$ 添加

$$
Y=\beta^2\alpha\beta^2\alpha^{4k+17}.
\tag{TM.4006}
$$

该来源为初始标签 $1$，加入后的真实混合标签族仍满足（TM.4002），根轮廓（TM.4005）也不变。

证明。其组成 $(4k+18,4)$，资源为 $m=4k+22,n=4k+26,m+n=H+8$。完整边数为 $\mathbf x=(2k+9,2k+9,0,0),\mathbf y=(1,1,1,1)$：字面词先在 $00$ 作 $\beta$ 回路，经 $\alpha$ 到 $10$ 作另一回路，再沿奇数 $\alpha$ 尾部回 $00$。次数平衡，边和给所述组成，正 $\alpha$ 对接通两回路，所以支撑连接起点。原子卷参数为 $u=v=0,w=2k+9$、状态 $00$，三窗为 $(1,-1,S^{4k+18})$，但初始目标标签 $1$ 不保留第三窗。$Y$ 初始只增加一个单目标尺寸行；在原 $U$ 的 $(n,E_1)=(4k+26,-1)$ 列中，新的最大尺寸为 $4k+22$，第二大仍为 $4k+14$，因为原 $U$ 有两个不同目标。因此 $D$ 不变，单行 $R=0$ 也不变。

两次替换执行中，$Y$ 首次接受并读 $-1$，第二次唯一拒绝，因为候选为 $H+8$。该真实拒绝直接选出它的初始目标，不读其不可用第三窗。其余来源照定理 40.1 运行，故无交叠时一标签足够，交叠时用两标签将 $Y$ 加入任意一类即可。交叠下的一标签下界也因限制到原四源成立；直接强制记录论证中 $Y$ 在首次之前大于受保护的 $U$ 最小行，首次之后尺寸与 $U$ 相同、大于受保护的 $V$ 行，不能分开它们的共同记录。

首次真实子层里 $Y$ 为当前标签 $0$，同当前读 $-1$、尺寸 $4k+26$，其表内下一资源是无穷哨兵。同一行另外两个 $U$ 的下一资源为 $H$，第二大仍为 $H$；它不进入接受列。故正确子层闭包仍仅由 $U,V$ 的第三窗交叠决定。$\square$

### 40.3 等号上带不能替代严格上带

**命题 40.4（$m+n=H$ 不准入原上带约化）。** 把 §38 的统一条件从 $m+n>H$ 放宽为 $m+n\ge H$，原轮廓闭包不再完整。

证明。对任意 $a\ge2$，取 $H=2a+3$ 和实际词 $P=\beta\alpha^a,Q=\alpha^2\beta\alpha^{a-2}$。二者同组成 $(a,1)$、$m=a+1,n=a+2,m+n=H$，共同前两窗为 $BA^a,SB^a$；第三窗分别为 $(-1)^aS^{2-a}A$ 和 $(-1)^aS^{6-a}A$。这些公式按二次叶因子 $S,S^2A$ 有序相乘即得，正规形保证第三窗不同。

其八边次数分别为 $\mathbf x_P=(0,0,\lceil a/2\rceil,\lfloor a/2\rfloor)$、$\mathbf x_Q=(1,1,\lceil a/2\rceil-1,\lfloor a/2\rfloor-1)$，共同 $\mathbf y=(1,0,0,0)$。非负次数来自所显示正词；从 $00$ 到 $(a\bmod2,1)$ 的字面路径给端点流量，$00\to01$ 的正边连上 $q=1$ 的 $\alpha$ 路径，$Q$ 的 $q=0$ 往返也与起点相接。所以它们是完整认证的实际来源，包括 $a=2$ 的零尾。

根表若误用上带轮廓，得到 $R(a+1)=D(a+1)=a+2$，闭包在该期限上失败。但两次纯 $\rho$ 在资源 $a+2$ 和 $H$ 均接受，真实第三窗读区分初始目标，一标签可恢复。首次之后是真正上带，下一资源为 $H$、下一窗不同，正确子层轮廓无重复列而通过。原上带必要性依赖首次接受后立即落标签 $0$；等号允许再一次合法替换，所以失败处正是该假设被删去。这证明不能作所述统一放宽。$\square$

### 40.4 来源、局部完整性与未解决范围

本章复用原子卷 §§359–360 的实际三窗像及八边、端点流量、正支撑连通条件，本卷 §§30、35 的初始目标和实际历史语义，以及 §38 的上带闭包。§40.1 的交叠族和全动作强制两次替换证明由上述具体正词完整展开；§40.3 的等号低对使用同一既有叶因子关系。成熟初态识别论文只提供方法背景，没有提供这些具体来源、交叠公式或容量结论。以上是普通数学结论，不构成 Lean 核验或文献原创性主张。

精确一／二标签判据只适用于所显示实际族；它不把第三窗交叠谓词提升成任意四源的完整判据。定理 38.6 已在严格上带给出任意长最小障碍，所以固定元数检验仍不完整。正面的约化发生于共同历史上的真实当前上带子表；根层必须保留 §39 的原始目标、第三窗列关联、准确两个资源增量和共同宏。一般更深层仍用 §35 的完整嵌套条件，全家族 $M_A(H)$、尖锐节省及任意深度紧凑结构仍未解决。

源表和标签的生产、来源认证、上下文供给、窗口精确算术、计划和解码表存储各有成本；这些证明不给免费供应、总记忆最优或最少调用。资源、实际执行记录和 Clifford 边界的有条件互恢复遵守命题 39.8 的合法读及已知次序前提，不恢复唯一原树括号或物理历程。

## 追加锚（本行以下为增补区）
## 41. 实际四源的尖锐双资源阈值与共同来源构造

本章固定 §30 的实际合同。公开整数 $H\ge1$ 在运行中保持不变；来源是同一棵非空、有序、自由括号化的实际 $\alpha/\beta$ 原树。读 $E$ 不改变来源，$\rho$ 与任意已知正上下文的左右拼接均先检验候选叶数是否不超过 $H$；拒绝只写入拒绝事件、保持来源并不给出被拒候选的 $E$。控制器共享初始化，允许保存任意已取得记录，按每个实际输入逐点有限停止，目标始终是初始 $q_H$。以下把 Clifford 单位记为 $G=BA$，以免与公开上限 $H$ 混淆。

本章及以下两章把实际原子组成记为 $c=(u,v)$，其中 $u,v$ 分别是 $\alpha,\beta$ 叶数；资源坐标为 $m=\lambda_0=u+v$、$n=\lambda_1=u+2v$、$\ell=\lambda_2=m+n$，故 $m\le n\le2m$，且实际组成由 $(u,v)=(2m-n,n-m)$ 恢复。$(m,n)$ 称为窗口大小对，不称为原子组成。对组成为 $(u,v)$ 的已知上下文定义

$$
D_0=u+v,\qquad D_1=u+2v,\qquad D_2=D_0+D_1.
\tag{TM.4101}
$$

任何在首次 $\rho$ 前被接受的正上下文累计增量满足 $0<D_0\le D_1\le2D_0$；空累计量写为 $(0,0)$，不把空对当作一个实际调用。左右次序只改变已知窗口因子的左右位置，不改变三个增量。

### 41.1 四源定理

**定理 41.1（实际四源的全动作尖锐阈值）。** 设四个实际初始来源 $P,Q,X,Y$ 满足下列条件：

1. $P,Q$ 的实际原子组成相同，窗口大小对为 $(m_L,n_L)$，$\ell_L=m_L+n_L\le H$；它们有相同的 $E_0,E_1$ 和不同的 $E_2$，且初始目标已按 $q_H$ 去重。
2. $X,Y$ 的第一替换大小均为 $N\le H$，当前大小满足 $m_X<m_Y\le N$，且 $m_X+N>H$；二者有相同的 $E_1$。
3. 四源的 $E_0$ 相同，且 $m_L\le m_X$。

令

$$
t=H-N+1\ge1,\qquad s=H-\ell_L\ge0.
\tag{TM.4102}
$$

在允许任意正左右上下文、任意自适应记录、所有守卫和逐点有限停止的合同下，四源使用同一份初始来源标签时的最小标签字母表满足

$$
M_A(\{P,Q,X,Y\};H)=
\begin{cases}
1,&s\ge t+\lceil t/2\rceil,\\
2,&s<t+\lceil t/2\rceil.
\end{cases}
\tag{TM.4103}
$$

若把上下文限制为任一侧的纯 $\alpha$ 正词，则

$$
M_A^\alpha(\{P,Q,X,Y\};H)=
\begin{cases}
1,&s\ge2t,\\
2,&s<2t.
\end{cases}
\tag{TM.4104}
$$

这里的 $M_A$ 只计运行前供应的来源标签；来源表、上下文、守卫、算术和解码器仍由原合同另行供应。

**证明。** 先证一标签的充分性。置

$$
d=\lceil t/2\rceil,\qquad r=t-d,
$$

则 $0\le r\le d$，实际右上下文

$$
K=\alpha^{d-r}\beta^r
\tag{TM.4105}
$$

的增量为

$$
(D_0,D_1,D_2)=(d,t,d+t).
\tag{TM.4106}
$$

条件 $s\ge d+t$ 给出 $\ell_L+d+t\le H$。因为 $m_X\le m_Y-1$ 且 $d\le t$，$P,Q,X$ 在第一次拼接上的候选首叶数不超过 $H$；若 $m_Y+d>H$，则只有 $Y$ 拒绝，该拒绝分支只含 $Y$，其原始目标由表直接输出，且来源未被改变；否则四源都接受，接着尝试 $\rho$。

对高源，第一次替换的候选大小为 $N+t=H+1$，所以 $X,Y$ 均拒绝；若前一步的 $Y$ 已拒绝，则仍由上一分支结束。对低源，第一次替换的候选大小为 $n_L+t$，而

$$
n_L+t\le n_L+s-d\le H-(m_L+d)\le H,
\tag{TM.4107}
$$

故 $P,Q$ 接受。对接受后的高源，右侧连续接单叶 $\alpha$ 直到第一次拒绝；若成功 $f$ 片，则初始 $m$ 由

$$
f=H-(m+d),\qquad m=H-d-f
\tag{TM.4108}
$$

唯一确定。$X,Y$ 的 $m$ 不同，所以填充和原始表给出各自目标。

对 $P,Q$，宏拼接后、第一次替换前的窗口大小对为 $(m_L+d,n_L+t)$；第一次替换后为 $(n_L+t,\ell_L+d+t)$，所以第二次替换候选大小为 $\ell_L+d+t\le H$，第二次 $\rho$ 也接受。两次真实读分别被已知宏窗口因子包围；将这些已知因子只在算术中按实际左右次序移除，第二次读得到原始 $E_2$，再由 $P,Q$ 的不同 $E_2$ 解码初始目标。整个过程没有使用被拒候选读，也没有物理逆、复位或复制。$t=1$ 时 $d=1,r=0$；若 $Y$ 在第一宏上拒绝，它仍是唯一拒绝者，$P,Q,X$ 的上述路径不变，没有调用空上下文。若 $t=1$ 且 $Y$ 接受，则高对在 $\rho$ 后由填充分开。纯 $\alpha$ 情形取 $d=t,r=0$，同一执行器的低资源消耗为 $2t$，从而得到上界。

再证全动作下界。沿 $P,Q$ 的共同记录直到第一次 $\rho$，所有实际读都是同一已知左右因子包围共同的 $E_0$；共同 $E_1$ 也按同一已知因子变换，所有守卫相同。若此前接受上下文累计为 $(D_0,D_1)$，为了保持两者的 $E_2$ 区别，必须有

$$
D_2=D_0+D_1\le s,
\tag{TM.4109}
$$

否则当前 $q_H$ 至多保留共同的前两窗及相应资源字段，定理 30.2 永久合并两个不同初始目标。若 $D_1\ge t$，整数锥给出 $D_0\ge\lceil D_1/2\rceil\ge\lceil t/2\rceil$，于是 $D_2\ge t+\lceil t/2\rceil$。在 $s<t+\lceil t/2\rceil$ 时，任何成功共同前缀都必须满足 $D_1\le t-1$。

在第一次产生不同守卫响应的拼接上，较小的 $P,Q$ 必须接受而至少一个高源必须拒绝；否则四源仍共享该动作记录。设被拒绝的高源大小为 $m\le m_Y\le N$，则低源累计首增量满足

$$
D_0\ge H-m+1\ge H-N+1=t,
\tag{TM.4110}
$$

从而 $D_1\ge D_0\ge t$，和上一段矛盾。被 $P,Q$ 拒绝的探针也在更大的高源上拒绝，不产生新的记录区别。逐点有限停止排除无限共同前缀，故四源必须在共同前缀后执行第一次 $\rho$。

若 $D_1\le t-1$，则 $X,Y$ 的第一次替换都接受，所得当前大小均为 $N+D_1$，当前 $E$ 是相同已知因子包围共同初始 $E_1$；下一次替换的候选大小至少为 $m_X+N>H$。于是二者有相同的当前标签 $0$、相同完整记录和相同当前 $q_H$，但初始目标不同，定理 30.2 排除任何后续恢复。故一标签不可能。若上下文纯 $\alpha$，有 $D_0=D_1$，故（TM.4109）直接给出 $D_1\le\lfloor s/2\rfloor$，而（TM.4110）要求 $D_1\ge t$，得到 $s\ge2t$ 的必要性。

最后，两标签总是足够：运行前供应低对或高对的成员资格。低对不作宏拼接，直接作两次 $\rho$ 并真实读取 $E_2$，因 $\ell_L\le H$ 而合法；高对直接右接单叶 $\alpha$ 到第一次拒绝，以成功次数 $f=H-m$ 恢复不同的初始大小 $m_X,m_Y$。标签分支上的原始目标字典分别来自实际来源表；该两标签协议不依赖一标签宏的资源阈值。故（TM.4103）和（TM.4104）均得证。 $\square$

### 41.2 每个资源对的实际来源与欧拉证书

**定理 41.2（任意 $t\ge1,s\ge0$ 的实际四源）。** 给定任意 $t\ge1,s\ge0$，取满足

$$
a\ge2,\qquad a\equiv s-t\pmod2,\qquad N=2a+s-t+4,
\tag{TM.4111}
$$

且足够大的 $a$，使 $N\ge11$、$a+1\le N-5$、$N>t+4$。令 $H=N+t-1$，取任意固定的有序括号化

$$
\begin{aligned}
P&=\beta\alpha^a,&Q&=\alpha^2\beta\alpha^{a-2},\\
X&=\beta^3\alpha\beta^2\alpha^{N-11},&Y&=\beta\alpha^{N-2}.
\end{aligned}
\tag{TM.4112}
$$

则它们满足定理 41.1 的全部实际来源条件，并且 $H-\ell_L=s$、$H-N+1=t$。

**证明。** 由实际原子组成得到窗口大小对和第二替换大小为

$$
\begin{array}{c|c|c|c}
& (m,n)&m+n&E_0,E_1\\ \hline
P,Q&(a+1,a+2)&2a+3&(BA^a,\,G B^a),\\
X&(N-5,N)&2N-5&(BA^{N-2},\,G B^{N-2}),\\
Y&(N-1,N)&2N-1&(BA^{N-2},\,G B^{N-2}).
\end{array}
\tag{TM.4113}
$$

其中 $B^4=1$、$A^2=1$ 给出 $E_0(X)=E_0(Y)$，而直接使用 $B^2=-1$ 和 $S=BA$ 化简 $E_1(X)=S^3BS^2B^{N-11}=SB^{N-2}=E_1(Y)$。由 $a\equiv N\pmod2$，低、高的 $E_0$ 也相等。条件 $N>t+4$ 给出 $m_X+N>H$，而 $a+1\le N-5$ 给出 $m_L\le m_X$。低源的第二窗口由

$$
E_2(P)=(-1)^aG^{2-a}A,\qquad E_2(Q)=(-1)^aG^{6-a}A
\tag{TM.4114}
$$

给出；$G$ 的无限阶和唯一正规形保证二者不同。

按 Atomic360 的边顺序

$$
\mathbf x=(x_{00},x_{10},x_{01},x_{11}),\qquad
\mathbf y=(y_{00},y_{01},y_{10},y_{11}),
$$

四个实际词的完整边次数为

$$
\begin{array}{c|c|c}
&\mathbf x&\mathbf y\\ \hline
P&(0,0,\lceil a/2\rceil,\lfloor a/2\rfloor)&(1,0,0,0)\\
Q&(1,1,\lceil a/2\rceil-1,\lfloor a/2\rfloor-1)&(1,0,0,0)\\
X&(0,0,1+\lfloor(N-11)/2\rfloor,\lceil(N-11)/2\rceil)&(2,1,1,1)\\
Y&(0,0,\lceil(N-2)/2\rceil,\lfloor(N-2)/2\rfloor)&(1,0,0,0).
\end{array}
\tag{TM.4115}
$$

所有条目均非负；$a=2$ 时 $Q$ 的两个尾项为零，$N=11$ 时 $X$ 的尾项为零，均仍是非空词。逐字从 $00$ 出发得到终点 $(a\bmod2,1)$ 或 $(N\bmod2,1)$，所以端点流量和组成方程成立。$P,Q,Y$ 由 $00\to01$ 的正 $\beta$ 边接到 $01$ 上的 $\alpha$ 链，$Q$ 还经过 $00\to10\to00$ 的正回路；$X$ 由 $01\to11$ 的正 $\alpha$ 边接通两个 $\beta$ 回路。全部正支撑与 $00$ 弱连通。由 Atomic359.3 的唯一正规形，参数为

$$
\begin{aligned}
&p=a\bmod2,\ q=1,\ u=v=p,\qquad
w_P=-\lceil a/2\rceil,\quad w_Q=w_P+2,\\
&w_Y=-\lceil(N-2)/2\rceil,\quad w_X=w_Y+4.
\end{aligned}
\tag{TM.4116}
$$

这些参数与（TM.4113）—（TM.4114）相容，故四个窗口属于同一实际来源像，而非独立选择的坐标。 $\square$

### 41.3 固定族的上限跳变与同摘要见证

**命题 41.3（全尺度固定族的上限跳变）。** 对每个 $k\ge1$，取

$$
a=4k+4,\qquad N=12k+12,\qquad H_0=20k+11.
\tag{TM.4117}
$$

定理 41.2 的四源有 $t=8k,s=12k$，因而在 $H_0$ 处全动作容量为 $M_A=1$，纯 $\alpha$ 容量为 $M_A^\alpha=2$，因为 $12k<16k=2t$；在同一四个初始来源上把公开上限改为 $H_1=H_0+1$ 后，$t=8k+1,s=12k+1$，两种容量均为 $2$。两个上限下各源的实际原子组成及初始 $q_H$ 逐源相同。固定档案 $\Gamma_H=(j,E_0,\ldots,E_j,\lambda_j)$ 也逐源相同：低源保持 $j=2$ 及其三窗和 $\lambda_2$，高源保持 $j=1$ 及其两窗和 $N$；组成不是 $\Gamma$ 的字段。公共 $H$ 和完整执行记录中的填充成功次数随上限改变，不属于此处的档案字段不变断言。

**证明。** 在 $H_0$ 处，实际宏 $\beta^{4k}$ 的增量是 $(4k,8k,12k)$；低源第二次替换候选正好为 $H_0$，高源第一次替换候选为 $H_0+1$，所以定理 41.1 给出一标签。$H_1$ 处四源的初始标签和窗口没有跨越任何边界，而（TM.4103）变为两标签。每个三源子族仍可一标签：含低对和一个高源时先作两次 $\rho$，含一个低源和高对时作宏 $\alpha^{H_1-m_L}$，再对高对填充。因此障碍正是四源的联合资源阈值。上限是固定族的公共合同参数；这不是对全体来源的 $M_A(H)$ 单调性作断言。 $\square$

同一上限还显示首增量不足以描述动作。$H_0$ 处宏 $\beta^{4k}$ 与宏 $\alpha^{4k}$ 都在四源上接受，二者均有 $D_0=4k$，且因为 $A^{4k}=B^{4k}=1$，每个来源的字面当前 $E_0$ 相同；但二者的 $D_1$ 分别为 $8k$ 与 $4k$。前者之后高源的 $\rho$ 被拒绝，后者之后高源的 $\rho$ 仍可接受并被合并，说明同一当前首窗和同一当前尺寸不能替代完整的双增量。

**命题 41.4（$H=31$ 的相同摘要而不同答案）。** 固定 $H=31,N=27$，分别取 $a=7$ 与 $a=11$ 的两组四源。定义这里比较的弱摘要只保留：共同 $E_0$，低、高的 $E_1$，高源的 $(m,n)$，固定 $\Gamma$ 纤维的目标基数，以及纤维内目标按初始 $m$ 的相对排序和间距；单点纤维没有非零间距。还可保留低对在共同 $(E_0,E_1)$ 纤维中第三窗正规形指数的相对排序和差，仍不保留绝对指数。两组的这份摘要相同：共同 $E_0=G$，低 $E_1=-G^2A$，高 $E_1=G^2A$，高源窗口大小对为 $(22,27),(26,27)$，纤维基数为 $(1,1,2)$，唯一双点 $\Gamma$ 纤维的初始大小依次为 $X<Y$、间距为 $4$；低对第三窗均为 $-G^kA$，$k_P<k_Q$ 且 $k_Q-k_P=4$。但低松弛分别为 $s=14$ 和 $s=6$，而 $t=5$，故前者一标签、后者二标签。

证明。两组均满足（TM.4111）且共享 $N,H$。弱摘要省略低源的实际组成 $(7,1)\to(11,1)$、绝对大小 $m_L:8\to12$、$n_L:9\to13$、$\ell_L:17\to25$，因而也省略相应的 $s:14\to6$ 和更深资源 $\lambda_3:26\to38$；它还省略低源的绝对第三窗口对，后者从 $(-G^{-5}A,-G^{-1}A)$ 变为 $(-G^{-9}A,-G^{-5}A)$。低源完整 $\Gamma$ 的 $E_2$ 和 $\lambda_2$ 字段因此改变，不能声称所有列或完整低档案不变。高源和其完整档案保持不变，所列弱摘要的相对排序和四步间距也保持不变。由定理 41.1，两组的阈值同为 $8$，而 $14\ge8>6$，于是答案不同。该反例只否定明确定义的弱摘要；这不是对保留完整 $(\Gamma,m)$ 表的否定。 $\square$

本章的实际结论只涉及显示的四源及其初始行为目标。来源、上下文、标签和解码表的生产、认证、存储与物理实现没有被资源阈值免费承担；全家族的全深度最优、标签生产和物理时空恢复仍需另行条件。

## 42. 一个固定低簇与任意上带的锚定簇判据

固定 $H\ge1$，令有限实际族 $\mathcal F=L\sqcup U$ 共享一份供应标签和实际初始首读 $E_0=g$。低簇 $L$ 至少含两个不同初始目标；所有低源具有相同实际原子组成、相同窗口大小对 $(m_0,n_0)$、相同 $E_0,E_1$ 和按目标去重后互异的 $E_2$，其中 $\ell_0=m_0+n_0\le H$，置 $s=H-\ell_0$。低簇不要求 $\lambda_3>H$；两次接受的替换已经能够读出其完整初始目标。上带 $U$ 的每个源满足 $m+n>H$、$m\ge m_0$、$E_0=g$；它可以任意混合初始标签 $0,1$、任意 $E_1$ 列和任意多个行。所有目标仍是初始 $q_H$，重复的当前轮廓不得代替不同的原始目标。

### 42.1 实际 轮廓 与单一截止

**定义 42.1（锚定簇的上 轮廓）。** 对 $U$ 按不同初始目标去重。标签 $0$ 的表行以 $n=\infty$ 作哨兵；这只是表示第一次 $\rho$ 必拒，不是实际整数或运行时端口。对每个初始尺寸行 $m$，若只有一个目标置 $R(m)=0$；若有多个目标，令 $R(m)$ 为该行目标的 $n$ 的第二大值，$\infty$ 按通常序参与。对每个重复的标签 $1$ 列 $(n,z)$，其中 $z=E_1$，令 $p$ 为列中第二大的 $m$，并置

$$
D(p)=\min\{n:(n,z)\text{ 为重复列且其第二大尺寸为 }p\},
\tag{TM.4201}
$$

没有这样的列时空最小值为 $H+1$。对 $l\in\{0,\ldots,H\}$ 定义

$$
B(l)=\min_{p>l}D(p),\qquad B=B(0),\qquad T=H-B+1.
\tag{TM.4202}
$$

若没有重复接受列，则 $B=H+1,T=0$。令

$$
A(c)=\max_{m\le c}R(m),
\tag{TM.4203}
$$

空最大值为零。对每个 $c$，令 $\operatorname{TailOK}(c)$ 表示把实际上带子族 $U_{m>c}$ 交给 §38 的上 轮廓 闭包测试后通过；空尾部通过。因为成功协议限制到任一子族仍是成功协议，$\operatorname{TailOK}(c)$ 随 $c$ 单调：若在 $c$ 通过，则在更大的截止也通过。故存在最小边界

$$
L_U=\min\{c\in[0,H]:\operatorname{TailOK}(c)\},
\tag{TM.4204}
$$

并且 $\operatorname{TailOK}(c)$ 当且仅当 $c\ge L_U$。这里的 轮廓、上带证书和目标字典都来自声明的实际原树；轮廓 本身不是动态状态，也不替代来源认证。

**定理 42.2（锚定簇 AC 的精确充要条件）。** 族 $\mathcal F$ 存在一标签、任意正左右上下文、逐点有限停止且忠实恢复所有初始目标的确定性协议，当且仅当存在整数

$$
\max(m_0,L_U)\le c\le H
\tag{TM.4205}
$$

使

$$
\begin{aligned}
d&=H-c,\qquad e=\max(d,T),\\
e&\le2d,\qquad d+e\le s,\qquad A(c)+e\le H.
\end{aligned}
\tag{AC}
$$

若 $d=e=0$，则省略宏上下文；不调用空来源。若 $d>0$，一次实际右宏

$$
K=\alpha^{\,2d-e}\beta^{\,e-d}
\tag{TM.4206}
$$

具有 $(D_0,D_1,D_2)=(d,e,d+e)$；某一子块可以为零，但整个宏长度为 $d>0$。

**证明。** 先证必要性。沿低簇中两个不同目标直到第一次 $\rho$，其全部读和守卫相同。若此前累计增量为 $(d,e)$，则正上下文锥给出 $(d,e)=(0,0)$ 或 $0<d\le e\le2d$。低簇第二窗大小变为 $\ell_0+d+e$；若超过 $H$，两个不同 $E_2$ 被截断，当前记录和 $q_H$ 相同，定理 30.2 排除恢复，故

$$
d+e\le s.
\tag{TM.4207}
$$

两个不同低目标不能在共同记录上停止并输出正确答案，逐点有限停止也排除无限共同前缀，故成功协议必须到达有限的第一次 $\rho$。令 $c=H-d$。在此前共同路径中，$m\le c$ 的所有上带行跟随低簇：每个已接受上下文的累计首增量不超过 $d$，而在 $m\le c$ 上均接受；若某探针在低簇上拒绝，它也在所有 $m\ge m_0$ 的上带源上拒绝。全部读是共同 $E_0$ 被相同已知左右因子包围，故记录也相同。于是第一次 $\rho$ 的低路径包含 $U_{m\le c}$，并且 $c\ge m_0$。若 $d>0$，$m>c$ 的上带源不能跟随全部已接受上下文；若 $d=0$，$c=H$，尾部为空。把原成功协议的初始输入限制到同一批原始上带来源 $U_{m>c}$，仍得到合法成功协议，因而 $\operatorname{TailOK}(c)$ 成立、$c\ge L_U$。这项限制从原始来源开始，不是在已经拼接的低路径上运行尾部协议，也不取消任何实际动作。

置 $a=H-e$。若首次 $\rho$ 拒绝，同一行 $m\le c$ 中满足 $n>a$ 的两个目标具有相同记录、当前大小和标签 $0$；因此每个前缀行至多一个拒绝目标，恰为 $A(c)\le a$。若首次 $\rho$ 接受，同列 $(n,z)$ 的两个目标在接受后具有同一当前大小 $n+e$ 和同一已知因子包围的当前读；它们的下一替换大小 $m+n+d+e>H$，故不能有重复接受列。这里 $e\ge d$ 给出 $a=H-e\le H-d=c$；实际来源的 $m\le n$ 又给出：任一满足 $n\le a$ 的列，其全部成员都满足 $m\le n\le a\le c$，因而整列都在共同前缀内。故前缀没有重复接受列当且仅当全表没有 $n\le a$ 的重复列，恰为 $a<B(0)=B$，等价于 $e\ge T$。标签 $0$ 的无穷哨兵始终拒绝，不参与接受列。正上下文整数锥另给 $e\le2d$。

若某成功协议以 $e'$ 满足这些条件，则令 $e=\max(d,T)\le e'$。它仍满足 $d\le e\le e'\le2d$，并减小 $d+e$ 和 $A(c)+e$。降低 $e$ 会使额外的列接受，但 $e\ge T$ 仍给出 $H-e<B$，所以上述全列包含论证保证每个新增接受列也单射；拒绝目标集合则只会缩小。因此（AC）的三个上界和低簇条件仍成立。这个替换是对待执行宏的数学选择，不是对已经执行来源作取消或反演，故得到（AC）。

再证充分性。先真实读取 $E_0=g$，查实际表和 $L_U$。若 $d>0$，尝试一次右宏 $K$；它恰在 $m\le c$ 时接受，拒绝分支恰为 $U_{m>c}$，在该分支运行其已通过 $\operatorname{TailOK}(c)$ 的上 轮廓 执行器。若 $c=H$，省略宏，尾部为空，整族进入前缀。

在接受宏的前缀中先尝试 $\rho$。低簇候选为 $n_0+e\le H$，因为 $d+e\le s$；低源接受后第二次替换候选为 $\ell_0+d+e\le H$。对上带源，若 $n>H-e=a$ 则第一次替换拒绝；条件 $A(c)+e\le H$ 保证每个这种拒绝行至多一个目标。右接单叶 $\alpha$ 直到第一次拒绝，若成功 $u$ 片则 $m=c-u$，从实际行字典返回初始目标，不使用被拒候选读。

若上带源满足 $n\le a$，第一次替换接受并真实读取当前 $E'=zk_1$；$k_1$ 是宏的已知右窗口因子，只在算术中按次序右消去以得到初始 $z=E_1$。随后第二次 $\rho$ 对所有上带源拒绝，因为 $m+n>H$ 且宏增量非负；当前大小为 $n+e$。填充 $\alpha$ 到拒绝给出 $u=H-n-e$，故恢复 $n=H-e-u$。$e\ge T$ 使所有接受列 $(n,z)$ 单射，实际列字典返回初始目标。低簇分支在第二次接受后再真实读取并移除已知的第二窗口因子，按互异 $E_2$ 解码。每个分支都保留同一个原始 $\tau$，且拒绝分支从不读取被拒候选。

$U$ 为空时 $L_U=0$，宏后的上带分支为空；$d=e=0$ 时上述叙述中的宏和其窗口因子均省略，第一次 $\rho$ 直接执行。于是所有分支均是有限的实际调用，证明充分性。 $\square$

### 42.2 单一扫描、记录和调用边界

**命题 42.3（AC 的单一 $c$ 扫描与保守调用界）。** 在 AC 判据中不需要搜索第二资源 $e$ 或其 $\beta$ 分解。对每个 $c$ 只计算 $d=H-c$ 和 $e=\max(d,T)$；若某个 $e'$ 可行，则该 $e$ 也可行。 $\operatorname{TailOK}$ 的最小边界可用单调二分在至多 $\lceil\log_2(H+1)\rceil+1$ 次 轮廓 闭包调用中找到；随后以一次 $c$ 的递增扫描和前缀最大值 $A(c)$ 检查（AC）。实际执行器的未知来源调用至多 $H+6$，且这是保守界。

证明。$e$ 的替换已在定理 42.2 必要性中证明；它同时保持 $d\le e\le2d$、$e\ge T$、$d+e\le s$ 和 $A(c)+e\le H$。单调性给出二分上界。实际执行时，低簇接受分支至多包含入口读、一次宏、两次 $\rho$ 和两次可用读，共六次，不需填充。宏接受而上带首次替换拒绝的分支至多有 $H+4$ 次调用；上带首次接受、第二次拒绝的分支至多有 $H+5$ 次调用，包括填充的终端拒绝。宏拒绝分支保持原始上带来源，既有 §38 上轮廓执行器至多用 $H+4$ 次，入口读和宏至多再加两次，故统一为 $H+6$。该数不计标签供应、实际来源认证、上下文生成、解码表、算术位复杂度、计划存储、全部档案和输出存储。 $\square$

AC 的资料项只是 $R,D$ 两个实际上带 轮廓、低簇的 $m_0,s$、单一截止 $c$ 及实际目标关联。它不把 可行性元数据 自动提升为闭合动态状态，不把独立坐标表当作实际来源，也不提供任意多低组成、交错低行或一般全家族的充分判据。每个被使用的 轮廓 行、窗口和欧拉证书仍须由同一实际原树表认证。

## 43. 五源的尖锐联合阈值、真五词与四源约化失效

### 43.1 五源定理

**定理 43.1（实际五源的尖锐阈值）。** 设实际初始来源 $P,Q,X,Y,Z$ 满足：$P,Q$ 同实际原子组成、同窗口大小对 $(m_L,n_L)$、同 $E_0,E_1$ 而 $E_2$ 不同，$\ell_L=m_L+n_L\le H$；$X,Y$ 的第一替换大小均为 $N\le H$，$m_X<m_Y\le N$，$m_X+N>H$，并且二者 $E_1$ 相同；$Z$ 的 $m_Z=m_Y$、第一替换大小 $N_Z$ 满足 $N<N_Z\le H$；五源 $E_0$ 相同且 $m_L<m_X$。不要求 $E_1(Z)\ne E_1(Y)$。令

$$
s=H-\ell_L,\qquad t=H-N+1,\qquad h=H-m_Y+1.
\tag{TM.4301}
$$

在任意正左右上下文下，

$$
M_A(\{P,Q,X,Y,Z\};H)=M_A^\alpha(\{P,Q,X,Y,Z\};H)
=\begin{cases}1,&s\ge2h,\\2,&s<2h.\end{cases}
\tag{F5}
$$

在既有固定 $\Gamma$ 合同下，执行后的补充容量为 $M_B=2$。

**证明。** 先明确高三源的一标签纯 $\alpha$ 协议：作截止为 $m_X$ 的 F 宏 $\alpha^{H-m_X}$。由于 $m_X<m_Y\le H$，宏为正词且恰接受 $X$，该单点分支直接输出其初始目标；拒绝分支保留原始 $Y,Z$。在拒绝分支作一次 $\rho$，二者都接受，因为 $N<N_Z\le H$；随后右接单叶 $\alpha$ 到第一次拒绝，成功次数 $f=H-n$ 恢复不同的初始第一替换大小 $n=N,N_Z$，由原始目标表解码。这就是该上带的 F/R 协议，不依赖 $E_1(Y),E_1(Z)$ 是否相同。

再用定理 42.2 的 AC 判据。高子族 $U=\{X,Y,Z\}$ 的 $m_X$ 行为单点行，$m_Y$ 行有 $Y,Z$ 两目标，故 $R(m_Y)=N$。重复接受列只有 $(N,E_1(X))$ 中的 $X,Y$，其第二大行是 $m_X$，所以 $B=N,T=t$。当截止 $c\ge m_Y$ 时，$A(c)=N$，而 $e\ge t$、$N+e\le H$ 不可能同时成立，因为 $N+t=H+1$。故任何可行截止都满足 $c<m_Y$；此时 $A(c)=0$，尾部是上述可行高子族的限制，且 $d=H-c\ge H-m_Y+1=h\ge t$，所以 AC 中最小的 $e$ 为 $e=d$。最小联合低资源代价为 $d+e=2d\ge2h$，在 $c=m_Y-1$ 处取等号。该截止的尾部只含 $Y,Z$，二者有不同的 $N,N_Z$，故尾部一标签可行；又因 $m_L<m_X<m_Y$，它满足低行允许范围。于是 $s\ge2h$ 时一标签存在，且宏可取纯 $\alpha^h$。

再证全动作下界。首次 $\rho$ 前，保留 $P,Q$ 的第三窗口区别要求所有已接受前缀满足 $D_0+D_1\le s$。若某正上下文首次分开五源，它必须接受低对而拒绝一个大小不超过 $m_Y$ 的源，故其累计 $D_0\ge H-m_Y+1=h$，并由正性得 $D_1\ge h$，从而 $D_0+D_1\ge2h$。在 $s<2h$ 时不存在这样的首次分开上下文；所有被拒探针也不产生记录差别，共同停止无法输出不同初始目标，逐点有限停止排除无限共同前缀，故必有有限的第一次共同 $\rho$。

记该次前缀的第二增量为 $e$。若 $e<t$，$X,Y$ 均接受；它们的当前大小同为 $N+e$，当前 $E_0$ 是相同的已知因子包围共同初始 $E_1$，而下一替换大小超过 $H$，故二者当前标签 $0$、记录和 $q_H$ 相同，初始目标不同。若 $e\ge t$，$X,Y,Z$ 均拒绝；$Y,Z$ 的当前大小同为 $m_Y+D_0$，当前 $E_0$ 也相同。当前标签 $0$ 的 $q_H$ 只保留该首读和该大小，不保存实际原子组成或 $E_1$，所以二者当前 $q_H$ 和完整记录相同；但初始第一替换大小 $N\ne N_Z$ 给出不同初始组成和不同初始标签 $1$ 目标。无论 $E_1(Y),E_1(Z)$ 是否相同，定理 30.2 都排除恢复。故一标签下界成立。

当 $s\ge2h$，先真实读 $E_0$，再执行纯宏 $\alpha^h$。它接受 $P,Q,X$，拒绝 $Y,Z$。接受分支第一次 $\rho$ 拒绝 $X$，该单点分支直接输出初始目标；低对接受，其窗口大小对变为 $(n_L+h,\ell_L+2h)$。第二次 $\rho$ 对低对仍接受，因为 $\ell_L+2h\le H$；随后一次真实读为 $E_2(P)G^h$ 或 $E_2(Q)G^h$，只在算术中右乘已知 $G^{-h}$，按原始 $E_2$ 分开 $P,Q$。拒绝宏的分支保持原始来源；$Y,Z$ 的第一次 $\rho$ 都接受，随后纯 $\alpha$ 填充的成功次数给出不同的原始 $n=N,N_Z$。若这两个实际 $E_1$ 不同，可用一次替换后的真实读直接区分并省略填充。于是纯 $\alpha$ 给出一标签上界。

两标签在所有松弛值下都足够：运行前供应低对与高三源的成员资格；低对不拼接宏，直接作两次 $\rho$ 和一次实际 $E_2$ 读，高三源用开头已证明的一标签 F/R 协议。因此在 $s<2h$ 时容量恰为 $2$，而在 $s\ge2h$ 时恰为 $1$，得（F5）的两种动作容量。

固定 $\Gamma$ 中，$P,Q$ 的标签 $2$ 档案因不同 $E_2$ 分成单点；$X,Y$ 共享同一 $(1,E_0,E_1,N)$ 档案键。$Z$ 的列是 $(N_Z,E_1(Z))$，因 $N_Z\ne N$ 而不同于 $(N,E_1(X))$，即使三个高源的 $E_1$ 完全相同也成立。因此最大目标纤维恰为二，固定执行后补充容量为 $2$。 $\square$

同 $E_1$ 的情形也有字面实际来源：在 $H=16$ 取 $P=\beta^4\alpha^2$、$Q=\beta^3\alpha^2\beta$、$X=\beta^2\alpha\beta^2\alpha^3$、$Y=\alpha^{12}$、$Z=\beta^2\alpha\beta^2\alpha^7$。窗口大小对依次为 $(6,10),(6,10),(8,12),(12,12),(12,16)$；五源 $E_0=1$，低对 $E_1=-G^4$、$E_2=G^2,G^{-2}$，三个高源的 $E_1$ 都为 $1$。它满足五源定理的全部假设，且 $Y,Z$ 的初始组成分别为 $(12,0),(8,4)$，静态列仍由 $n=12,16$ 分开。

**定理 43.2（所有真子族的四源约化）。** 在

$$
t+\lceil t/2\rceil\le s<2h
\tag{TM.4302}
$$

时，在定理 43.1 的全部实际来源假设下，五源全族需要两个标签，而每个真子族都一标签可行。这里 $N<N_Z\le H$ 已蕴含 $t=H-N+1\ge2$；抽象删除结论不另要求 $t\ge5$。

**证明。** 删除 $Z$ 后得到定理 41.1 的四源；其宏取 $d=\lceil t/2\rceil,r=t-d$。由于 $t\ge2$，$d\le t-1$，从而 $m_Y+d\le N+t-1=H$，所有剩余源都接受宏。低对两次接受替换恢复，$X,Y$ 第一次替换拒绝后由填充恢复不同原始 $m$。删除 $X$ 或 $Y$ 后，剩下的两个高源有不同的第一替换大小 $N,N_Z$；不作宏，先作 $\rho$，再尝试第二次 $\rho$。低对第二次接受而高源拒绝；低分支实际读 $E_2$，高分支按第一次替换后的当前大小填充恢复原始 $n=N,N_Z$，即使其 $E_1$ 相同也能解码。删除 $P$ 或 $Q$ 后，剩下一个低源：正宏 $\alpha^{H-m_L}$ 恰接受该最小行，其单点分支直接输出原始目标；拒绝分支保持原始高三源，并使用定理 43.1 开头的一标签 F/R 协议。再删去任意更多目标只是限制这些协议的实际输入子族，故所有真子族一标签可行。$t\ge5$ 只用于定理 43.3 所选第五词满足 $N+4\le H$，不是本删除证明的条件。 $\square$

### 43.2 每个资源对的实际五词与欧拉证书

**定理 43.3（任意 $t\ge5,s\ge0$ 的实际五源构造）。** 对任意 $t\ge5,s\ge0$，取足够大的 $a\ge2$ 满足 $a\equiv s-t\pmod2$，并令

$$
N=2a+s-t+4,\qquad H=N+t-1=2a+s+3,
\tag{TM.4303}
$$

使 $N\ge11$、$a+1<N-5$、$N>t+4$。使用定理 41.2 的四个词并加入

$$
Z=\beta^5\alpha^{N-6}.
\tag{TM.4304}
$$

则

$$
\begin{array}{c|c|c|c}
& (m,n)&m+n&E_0,E_1\\ \hline
P,Q&(a+1,a+2)&2a+3&(BA^a,\,G B^a)\\
X&(N-5,N)&2N-5&(BA^{N-2},\,G B^{N-2})\\
Y&(N-1,N)&2N-1&(BA^{N-2},\,G B^{N-2})\\
Z&(N-1,N+4)&2N+3&(BA^{N-2},\,G^5 B^{N-6}).
\end{array}
\tag{TM.4305}
$$

低对的第三窗口仍为（TM.4114），且 $E_1(Z)\ne E_1(Y)$。

**证明。** $Z$ 的实际原子组成为 $(N-6,5)$，直接给窗口大小对 $(m_Z,n_Z)=(N-1,N+4)$；$A^4=B^4=1$ 给共同 $E_0$，而 $E_1(Z)=G^5B^{N-6}=G^5B^{N-2}$ 与 $GB^{N-2}$ 不同，否则唯一正规形迫使 $G^4=1$。前四个来源及其实际欧拉证书完全复用定理 41.2，不重复坐标选择。

对新增第五词，Atomic360 边次数为

$$
\mathbf x_Z=(0,0,\lceil(N-6)/2\rceil,\lfloor(N-6)/2\rfloor),\qquad
\mathbf y_Z=(3,2,0,0).
\tag{TM.4306}
$$

字面路径先沿 $00\leftrightarrow01$ 的五条 $\beta$ 边到 $01$，再沿 $01\leftrightarrow11$ 的 $\alpha$ 链；边次数和给出（TM.4305）的组成，终点为 $(N\bmod2,1)$，出入流量正确，正支撑与 $00$ 弱连通。由 Atomic359.2 的逐边增量，参数为

$$
p=N\bmod2,\qquad q=1,\qquad u=p,\quad v=p+2,\quad
w_Z=-\left\lceil\frac{N-6}{2}\right\rceil.
\tag{TM.4307}
$$

它与 $Y$ 的参数相差 $v$ 和 $w$ 的相应整数，给出相同首窗而不同第二窗。于是第五词是同一实际来源体系中的合法来源，而不是抽象边缘坐标。 $\square$

由（TM.4303），该构造的五源阈值为

$$
s\ge2(t+1).
\tag{TM.4308}
$$

所以每个 $t\ge5$ 的区间 $t+\lceil t/2\rceil\le s<2(t+1)$ 都给出一个所有四源子族和上 轮廓 均可行、但五源联合阈值失败的实际族。若另取 $a>s-1$，则 $\lambda_3(P)=\lambda_3(Q)=3a+5>H+1$，低簇也落在两层假设的严格范围内。

### 43.3 全尺度上限转移与精确遗漏字段

**命题 43.4（五源的连续上限转移）。** 对每个 $t\ge5$，取

$$
a=3t+2,\qquad N=7t+10,\qquad H_0=8t+9.
\tag{TM.4309}
$$

则 $s_0=2t+2=2h_0$，其中 $h_0=t+1$；纯宏 $\alpha^{t+1}$ 一标签成功，且这个字面五源族在 $H_0$ 有至多五次实际来源调用的协议，计入接受和拒绝调用。把上限改为 $H_1=H_0+1$ 后，$s_1=2t+3<2(t+2)=2h_1$，同一固定实际五源需要两个标签。所有四源真子族在 $H_1$ 仍一标签可行，且初始目标及固定 $\Gamma$ 字段逐源不变。

**证明。** 先作实际入口 $E_0$ 读。宏 $\alpha^{t+1}$ 在 $P,Q,X$ 上接受，在 $Y,Z$ 上以候选大小 $H_0+1$ 拒绝；接受分支的低第二次替换恰为 $H_0$，$X$ 的第一次替换为 $H_0+2$。低分支不读中间 $E_1$，只作两次接受的 $\rho$ 和最后一次实际 $E_2$ 读，再右移除已知 $G^{t+1}$ 因子；包括入口读和宏，共五次。$X$ 分支在第一次 $\rho$ 拒绝后即返回单点目标，共三次。拒绝宏的 $Y,Z$ 保持原始来源，首次替换都接受；$t=5$ 时 $N_Z=N+4=H_0$ 也合法，随后一次实际 $E_1$ 读因（TM.4305）不同而直接分开，共四次。五源调用次数依次为 $(5,5,3,4,4)$，无需填充；此界仅针对该字面族，不替代一般 AC 或 F/R 执行器的填充调用界。

升到 $H_1$ 后，五个来源仍保持原标签、实际组成和窗口；低源固定 $\Gamma$ 仍为标签 $2$ 的三窗与 $\ell_L$，高源仍为标签 $1$ 的两窗与原始 $n$。此时 $t_1=t+1$，且 $t_1+\lceil t_1/2\rceil\le2t+3=s_1<2h_1$，因此所有四源真子族由定理 43.2 的各删除情形一标签可行；只有删除 $Z$ 的形状直接使用定理 41.1。完整五源按（F5）转为二标签。两上限的比较固定来源族和来源字段，不把该跳变解释为全局 $M_A(H)$ 非单调。 $\square$

**命题 43.5（$H=63$ 的相同上 轮廓 而不同五源答案）。** 固定 $H=63,N=56$ 和相同的高词 $X,Y,Z$。低词取 $a=20$ 与 $a=24$ 两种选择。两组都有

$$
R(55)=56,\quad R(m)=0\ (m\ne55),\qquad
D(51)=56,\quad D(p)=64\ (p\ne51),
\tag{TM.4310}
$$

高源大小为 $51,55,55$，高 $E_1$ 为 $-G,-G,-G^5$；低簇、所有四源子族和上 轮廓 的可行性结论在两组均相同，唯一适用四源阈值为 $t=8$、$t+\lceil t/2\rceil=12$。然而低松弛分别为 $s=20$ 与 $s=12$，而五源阈值 $2h=18$，所以 $a=20$ 的全族一标签可行，$a=24$ 的全族需要两个标签。

证明。两组均由（TM.4303）给出共同 $H,N$；$a=20$ 与 $a=24$ 的低簇分别有 $\ell_L=43,51$，而低 $\lambda_3=65,77>63$。上轮廓只看高行、重复 $(n,E_1)$ 列和其第二大尺寸，因而两组完全相同。四源阈值为 $12$，两组分别满足 $20>12$ 和 $12=12$，所以两个四源族均通过；其余真子族用定理 43.2 的删除协议。五源阈值为 $18$，两组分别满足 $20\ge18$ 和 $12<18$，所以只有第一组全族通过。AC 保留的联合关系是低松弛与截止的同一不等式，恰能区分两组。 $\square$

因此，“上带 $R,D$ 可行、每个低分量可行、所有四目标子族可行”并不构成五源联合可行性的充分条件；它遗漏了同一个首宏同时必须支付低簇双窗口和保护高行的共同资源。这个失败不否定保留完整配对 $(\Gamma,m)$ 表的表示，也不把固定族的 上限敏感性冒充为全体 $M_A(H)$ 的单调性。所有上述五源结论只在显示的实际来源、固定守卫和初始目标解码合同内成立；更深层全局最优、标签生产、总记忆、物理时空及全家族容量仍未由此确定。

## 追加锚（本行以下为增补区）

## 44. 单位历史实际正源的任意精确取得深度与原始目标记忆

本章固定 §§30–31 的单一未知实际来源、共同初始化、固定活上限、当前 $E$ 读、受守卫的 $\rho$ 和任意已知非空正上下文的左、右拼接合同。一次上下文拼接是原子候选：只有整个候选叶数不超过上限才接受；拒绝不改变来源，也不返回候选读数。目标恒为未改动初始来源的 $q_H$。控制器可保留任意已取得记忆，下一动作及输出只由公共量和实际记录确定，并须在每个声明输入上有限停止。

下面给出一个公开限制族上的精确最坏接受替换深度。标签只有一个固定值；来源类别是经过实际正词认证的输入前提。这个前提不供应未知组成、尺寸或未来窗口端口。合法路径的深度上界仍由推论 35.5 供应；本章证明的是一个可恢复族的必要深度及其匹配执行，而非从长合法路径推断必要性。

### 44.1 Fibonacci 投影与稀疏源族

**定义 44.1（公开生成数据与实际来源）。** 取 $F_0=0,F_1=F_2=1$，并用 Fibonacci 递推。对整数 $D\ge2$ 和整数向量 $c=(a,b)$ 定义

$$
\ell_j(c)=F_{j+1}a+F_{j+2}b\quad(j\ge0),\qquad
C_D=\operatorname{lcm}(F_1,\ldots,F_D).
\tag{TM.4401}
$$

对 $0\le i<D$ 置

$$
\begin{aligned}
d_i&=4(-1)^{i+1}\frac{C_D}{F_{D-i}}2^i
       (F_{i+2},-F_{i+1}),\\
L_D&=\sum_{i=0}^{D-1}(|d_{i,\alpha}|+|d_{i,\beta}|),\qquad
R_D=8(L_D+1),\\
c_\varepsilon&=(R_D,R_D)+\sum_{i=0}^{D-1}\varepsilon_i d_i,
\qquad \varepsilon\in\{0,1\}^D.
\end{aligned}
\tag{TM.4402}
$$

这些是离线定义的整数资源，在线算法不能直接查询未知 $c_\varepsilon$。对每个 $0\le j<D$ 定义两个位向量

$$
\varepsilon^{j,-}_i=\mathbf1_{\{\ell_j(d_i)<0\}},\qquad
\varepsilon^{j,+}=\varepsilon^{j,-}+e_j,
\qquad
\mathcal E_D=\bigcup_{j=0}^{D-1}
 \{\varepsilon^{j,-},\varepsilon^{j,+}\},
\tag{TM.4403}
$$

其中 $e_j$ 为第 $j$ 个单位位，集合删除重复项。下面的证明保证第 $j$ 位原为零，所以加 $e_j$ 仍是位向量。再置

$$
Q(\varepsilon)=\sum_{i=0}^{D-1}2^i\varepsilon_i,\qquad
Q_D^{\max}=\max_{\varepsilon\in\mathcal E_D}Q(\varepsilon),\qquad
B_D=R_DF_{D+3},\qquad
H_D=B_D+4C_DQ_D^{\max}.
\tag{TM.4404}
$$

写 $c_\varepsilon=(a_\varepsilon,b_\varepsilon)$，令 $r_\varepsilon=a_\varepsilon/4$、$s_\varepsilon=b_\varepsilon/4$。取以下字面正词的固定左结合有序二叉括号化：

$$
t_\varepsilon=
\alpha^{2r_\varepsilon-1}\beta^{2s_\varepsilon}\alpha
\beta^{2s_\varepsilon-1}\alpha^{2r_\varepsilon}\beta,
\qquad \varepsilon\in\mathcal E_D.
\tag{TM.4405}
$$

定义 $\mathcal F_D=\{t_\varepsilon:\varepsilon\in\mathcal E_D\}$。供应标签函数为 $h_D(t_\varepsilon)=\star$，在整个族上保持同一个常量，不随来源或后续动作改变。标签生产者直接返回 $\star$，不访问来源；认证来源确属声明类别是另一个前提，不能用常量标签替代。

**引理 44.2（终端单射、重复最小值与逐层分离）。** 对定义 44.1 的任意整数 $D\ge2$，$\mathcal E_D$ 恰有 $D+1$ 个元素；全部 $c_\varepsilon$ 的两个坐标均为严格正的四倍整数。对每个 $0\le j<D$，$\ell_j$ 在 $\mathcal E_D$ 上的最小值恰由两个不同位向量取得；而

$$
\ell_D(c_\varepsilon)=B_D+4C_DQ(\varepsilon)
\tag{TM.4406}
$$

在整个二进制立方体上单射。对每个整数 $j\ge0$ 还有

$$
\min_{\varepsilon\in\mathcal E_D}\ell_{j+1}(c_\varepsilon)
 >\max_{\varepsilon\in\mathcal E_D}\ell_j(c_\varepsilon).
\tag{TM.4407}
$$

证明。Cassini 恒等式和递推给出

$$
F_{j+1}F_{i+2}-F_{j+2}F_{i+1}
=\begin{cases}
(-1)^{i+1}F_{j-i},&j>i,\\
0,&j=i,\\
(-1)^jF_{i-j},&j<i.
\end{cases}
\tag{TM.4408}
$$

具体地，$j=i+1$ 的值由 Cassini 得 $(-1)^{i+1}$；对 $j>i$ 的递推决定余项，交换 $i,j$ 并取负号得到 $j<i$ 的式子。因此 $\ell_j(d_i)$ 恰在 $i=j$ 为零；对 $i<D$，$\ell_D(d_i)=4C_D2^i>0$。基点满足 $\ell_D(R_D,R_D)=R_DF_{D+3}$，故得到（TM.4406）及单射性。

在整个二进制立方体上最小化 $\ell_j$，每个非零系数独立决定其位：负系数取一，正系数取零；只有第 $j$ 位任意。恰有（TM.4403）的两点取得最小值，两点都在 $\mathcal E_D$，所以限制到该集合后仍恰有这两个最小点。

为了计算集合大小，对实数 $z$ 考察法向量 $(1,z)$。第 $i$ 个生成向量的系数 $d_{i,\alpha}+z d_{i,\beta}$ 只有一个零点

$$
z_i=F_{i+2}/F_{i+1}.
$$

式（TM.4408）保证这 $D$ 个零点两两不同。将零点按实数大小排列，沿 $z$ 从负无穷到正无穷，每次只改变一个最小化位，且每个位只改变一次。因此 $D+1$ 个互补开区间给出 $D+1$ 个互不相同的最小化位向量；在每个零点，两种最小化位向量恰为左右相邻区间的两点。法向量 $\ell_j$ 是 $(1,z_j)$ 的正倍数，故这些相邻点的并恰为（TM.4403），其大小为 $D+1$。

每个生成向量的坐标为四的倍数，$R_D$ 为八的倍数，且每个坐标的扰动绝对值至多 $L_D$。所以两个坐标均至少为 $R_D-L_D>0$，也都是四的倍数。对整个二进制立方体可取统一估计

$$
|\ell_j(c_\varepsilon)-R_DF_{j+3}|\le L_DF_{j+3}.
$$

于是下一层最小值减去本层最大值至少为

$$
R_DF_{j+2}-L_DF_{j+5}>0,
\tag{TM.4409}
$$

因为 $F_{j+5}=3F_{j+2}+2F_{j+1}\le5F_{j+2}$ 且 $R_D>5L_D$。限制到 $\mathcal E_D$ 保留该严格不等式，证明（TM.4407）。$\square$

### 44.2 同一正源的窗口、组成与初始目标

**命题 44.3（$D+1$ 个实际初始目标）。** 对每个整数 $D\ge2$ 和每个整数 $H\ge H_D$，$\mathcal F_D\subseteq\mathcal T_H$ 是恰含 $D+1$ 个来源的非空族。每个来源同时满足

$$
W_3(t_\varepsilon)=(1,1,1),\qquad
c(t_\varepsilon)=c_\varepsilon,\qquad
\lambda_j(t_\varepsilon)=\ell_j(c_\varepsilon),
\quad j\ge0.
\tag{TM.4410}
$$

全部初始 $q_H$ 都为标签 $2$，且两两不同。其具体目标为

$$
\tau_\varepsilon=q_H(t_\varepsilon)
 =(2,(\mathbf u_{\mathrm{unit}},c_\varepsilon)),
\tag{TM.4411}
$$

其中 $\mathbf u_{\mathrm{unit}}=((0,0,0),(0,0,0),(0,0,0))$ 是 §28 正规坐标中三个单位窗口的唯一坐标，不把观察值 $1$ 与这个坐标混写。供应标签仍仅为 $\star$。

证明。引理 44.2 保证 $r_\varepsilon,s_\varepsilon\ge1$；（TM.4405）的每个显示块都有正长度。它就是[原子卷推论 360.4](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的单位历史词。为明确同源认证，按原子卷定理 360.2 的顺序，它的八边次数是

$$
\mathbf x=(r_\varepsilon,r_\varepsilon,r_\varepsilon,r_\varepsilon),\qquad
\mathbf y=(s_\varepsilon,s_\varepsilon,s_\varepsilon,s_\varepsilon).
\tag{TM.4412}
$$

起点及终点均为 $00$，四个顶点出入平衡，全部八条边严格为正，正支撑与 $00$ 连通。边次数和为 $(4r_\varepsilon,4s_\varepsilon)=c_\varepsilon$；原子卷引理 359.2 的累计参数为 $u=v=w=p=q=0$。因此同一条实际非空叶词同时供应单位三窗与声明组成，每一种有序括号化均保留它们，固定左结合只是选定代表。

组成替换和推论 35.5 给出（TM.4410）的 Fibonacci 叶数。单位三窗在 §28 的 $F$ 运输下固定，故所有纯替换位置的实际 $E$ 都等于 $1$。由引理 44.2，$\lambda_D\le H_D\le H$，且 $D\ge2$ 保证 $\lambda_2\le\lambda_D$；初始来源在上限内并为标签 $2$。式（TM.4406）区分每两个组成，因而区分其初始 $q_H$；不同组成也保证实际词不同。$\square$

### 44.3 首次响应分歧的全动作下界

**引理 44.4（重复最小投影的必要深度）。** 固定整数 $D\ge2,H\ge1$，令 $\mathcal F\subseteq\mathcal T_H$ 为有限实际族。假定全部来源有相同 $W_3$、两两不同的初始目标 $\tau(t)=q_H(t)$，且对每个 $0\le j<D$，$\lambda_j$ 在该族的最小值至少由两个来源取得，同时

$$
\min_{t\in\mathcal F}\lambda_{j+1}(t)
 >\max_{t\in\mathcal F}\lambda_j(t).
\tag{TM.4413}
$$

若标签在整个族上为同一个常量，则任何依照 §§30–31 合同成功恢复初始目标的确定性逐点有限停止协议，都有一个输入路径接受至少 $D$ 次 $\rho$。该结论允许任意已取得记忆、任意当前 $E$ 读、任意正左／右上下文及任意被拒探测。

证明。在一份所有输入共同取得的完整记录上，令 $j$ 为已接受的 $\rho$ 次数。引理 30.1 的单出现不变量使每个当前来源仍实际含有一次 $\rho^j(t)$，其余材料均为已知正上下文。因此相邻的当前叶数可写为

$$
m_t=\lambda_j(t)+U,\qquad
n_t=\lambda_{j+1}(t)+V,\qquad 0\le U\le V.
\tag{TM.4414}
$$

$U,V$ 是已知上下文在真实动作次序中运输后的贡献，不是未经运输的历史插入量。共同接受 $\rho$ 时 $(U,V)$ 变为 $(V,U+V)$；共同接受正上下文时加上 $(u,v)$，其中 $0<u\le v$；拒绝或只读不改变它们。这证明不等式在任意共同历史上保持。所有窗口的已知左右因子按引理 35.1 保持次序；未知出现的完整窗口历史因相同 $W_3$ 而共同。因此相同实际动作前缀后的当前 $E$ 总相同，读不能成为首次响应分歧。这里没有把未被守卫许可的窗口供应给控制器。

只要 $j<D$，（TM.4413）给 $\min n_t>\max m_t$。若下一正上下文是首次非共同响应，它的增量为 $(u,v)$，$v\ge u>0$。某个较大当前尺寸来源拒绝，故 $\max m_t+u>H$；所有最小 $m_t$ 的来源则接受。取两个最小 $\lambda_j$ 的来源，二者初始目标不同，接受后当前尺寸相同、当前 $E$ 相同，且

$$
n_t+v>\max m_t+u>H.
$$

两者均落当前标签 $0$，有同一个当前 $q_H$；完整记录也相同，包括该上下文身份及其接受响应。定理 30.2 与命题 38.1 判定它们的初始目标永久合并，任意增大记忆也无济于事。因此成功协议不能用这样的上下文首次分开族。论证覆盖左右两侧、任意叶序和含 $\beta$ 的上下文，接受后再读当前 $E$ 也不分开该对。

若一次 $\rho$ 对全族拒绝且 $j<D$，则全部 $n_t>H$；两个最小 $\lambda_j$ 来源已具有相同当前标签 $0$、尺寸及 $E$，并仍有相同完整记录和不同初始目标。同一个永久碰撞再次排除成功延续。

若一次 $\rho$ 是首次非共同响应，且 $j<D-1$，至少有来源拒绝，所以 $\max n_t>H$。取两个最小 $\lambda_{j+1}$ 来源；两者都接受。接受后的当前尺寸等于相同的最小 $n_t$，当前 $E$ 相同；下一次替换的候选尺寸为

$$
\lambda_{j+2}(t)+U+V
 >\max_{s\in\mathcal F}\lambda_{j+1}(s)+V
 =\max_{s\in\mathcal F}n_s>H.
\tag{TM.4415}
$$

严格号由（TM.4413）在 $j+1$ 处以及 $U\ge0$ 得到。因此该接受对又落同一个当前标签 $0$，具有同记录、同当前 $q_H$ 和不同初始目标。拒绝侧的响应不同不能修复接受侧这个实际碰撞；任何接受后的当前读在该对上也相同。

所以成功协议在共同深度 $j<D-1$ 时，不能有响应分歧、全拒绝 $\rho$ 或共同停止；共同停止只有一个输出，不能等于不同目标。已共同接受的 $\rho$ 若达到 $D$，结论即成立。否则在共同深度 $D-1$ 时，上下文首次分歧与全拒绝 $\rho$ 仍被排除；若 $\rho$ 首次分歧，它至少在一个输入上接受，产生深度 $D$；若共同接受，同样达到 $D$。剩下的可能只有无限共同读／拒绝前缀或有限共同停止：前者违反逐点有限停止，后者无法输出不同目标。有限实际族也保证无穷共同前缀不能被不同输入的未到达停止点解释。故总有一条输入路径接受至少 $D$ 次 $\rho$。$\square$

### 44.4 匹配的在线取得与精确深度

**定理 44.5（一个常量标签的任意精确最坏接受深度）。** 对每个整数 $D\ge2$，定义 44.1 给出整数 $H_D$ 及 $D+1$ 个实际正词来源 $\mathcal F_D$。对每个整数 $H\ge H_D$，令 $\mathfrak P_{D,H}$ 为全部共同初始化、只用 §§30–31 合同、在 $\mathcal F_D$ 每个输入上有限停止并正确输出其初始 $q_H$ 的确定性协议；每个输入供应同一个 $h_D=\star$，协议可使用任意已取得记忆。若 $\operatorname{dep}_\rho(\Pi,t)$ 只计真正接受的 $\rho$ 调用，则

$$
\min_{\Pi\in\mathfrak P_{D,H}}
 \max_{t\in\mathcal F_D}\operatorname{dep}_\rho(\Pi,t)=D.
\tag{TM.4416}
$$

有一个在全部这些输入上恰接受 $D$ 次 $\rho$ 的有限在线协议，它只再用原子全 $\alpha$ 右上下文探测，不用任何 $E$ 读，来源调用数至多

$$
D+\lceil\log_2 H\rceil+1,
\tag{TM.4417}
$$

其中计入每次接受／拒绝调用及最后一次单叶拒绝。

证明。命题 44.3 与引理 44.2 满足引理 44.4 的全部假设，故得到下界。为同时证明可恢复性和匹配上界，先在同一个未知原源上依次调用 $D$ 次实际 $\rho$。每次候选叶数为 $\lambda_j\le\lambda_D\le H_D\le H$，所以全部接受；等号也是合法接受。此时未知实际尺寸记为

$$
N=\lambda_D(t_\varepsilon)=B_D+4C_DQ(\varepsilon).
\tag{TM.4418}
$$

这个 $N$ 尚未读取。接下来只由真实守卫响应取得它。初始化整数 $l=0,u=H,U=0$，维持

$$
l<N\le u,\qquad U=H-u,\qquad
\lambda(t_{\mathrm{cur}})=N+U.
\tag{TM.4419}
$$

当 $u-l>1$ 时，令 $c=\lfloor(l+u)/2\rfloor$，构造已知非空、固定括号的上下文 $\alpha^{u-c}$，尝试一次实际原子右拼接。其整候选大小为 $N+U+u-c=N+H-c$，故实际响应满足

$$
\text{accept}\quad\Longleftrightarrow\quad N\le c.
\tag{TM.4420}
$$

接受时置 $u=c$，把 $U$ 增加实际接受的长度 $u_{\mathrm{old}}-c$；拒绝时仅置 $l=c$，来源和 $U,u$ 保持不变。两种更新均保持（TM.4419），并使正整数区间宽度至多变为原宽度的一半向上取整；最多 $\lceil\log_2 H\rceil$ 次探测后 $u-l=1$，因 $N$ 为整数得到 $N=u=H-U$，实际当前尺寸恰为 $H$。再尝试一次单叶 $\alpha$，其候选大小为 $H+1$，实际拒绝，作为终端响应。

若 $N=c$，该宏恰在上限处接受，不能把等号改为拒绝。若 $N=H$，全部区间探测均拒绝，没有任何成功上下文；最终单叶也拒绝，而 $U=0$ 仍正确给出 $N=H$。每个宏长度为正，拒绝是整宏的原子拒绝，不用逐叶执行替代被拒宏，不读取被拒候选。

由实际取得的 $U$ 和公共数据计算

$$
Q=\frac{H-U-B_D}{4C_D}.
\tag{TM.4421}
$$

在声明实际族上，这个商是非负整数，等于唯一的 $Q(\varepsilon)$；取其 $D$ 个二进制位恢复 $\varepsilon$，再用（TM.4402）计算原组成 $c_\varepsilon$，输出（TM.4411）的原始 $q_H(t_\varepsilon)$。不是把饱和后的当前 $q_H$ 当作初始目标。公共族限定及同源证书保证位向量确属 $\mathcal E_D$；没有要求在线控制器枚举未知未来树或调用 §35 的嵌套可行性函数。

替换和区间循环均有限，最后拒绝也计费；无当前窗口读、隐藏尺寸端口、来源导航、复制、重置、逆向消去或新未知源。区间控制的每个数只来自公共常量、先前动作身份及真实响应。因此该协议属于 $\mathfrak P_{D,H}$，深度为 $D$，调用数满足（TM.4417），与下界相合。$\square$

### 44.5 已取得记忆与终端当前边界

**命题 44.6（不同记录补偿同一个终端当前边界）。** 在定理 44.5 的匹配协议中，对每个 $D\ge2,H\ge H_D$ 和每个 $t_\varepsilon\in\mathcal F_D$，终端当前边界均为

$$
q_H(t_{\mathrm{cur}})=(0,A^H,H),
\tag{TM.4422}
$$

但实际记录中的累计接受上下文长度 $U$ 两两不同，足以恢复不同初始目标。令 $\omega_\varepsilon$ 为该输入上的完整实际记录，则

$$
\tau_\varepsilon=
\operatorname{decode}_{D,H}(\omega_\varepsilon),\qquad
\operatorname{decode}_{D,H}\text{ 由（TM.4421）、（TM.4402）、（TM.4411）给出}.
\tag{TM.4423}
$$

这里的配对始终是同一初始实际词、其真实终端来源及它自己取得的记录。

证明。纯 $D$ 次替换后 $E=1$，之后仅右接纯 $\alpha$，总实际接受长度为 $U=H-N$；拒绝均不改变来源。所以终端 $E=A^U$。所有 $N$ 为四的倍数，$A^2=1$ 给出 $A^{H-N}=A^H$。终端当前尺寸是 $H$，且当前 $\beta$ 数严格为正：初始两个字母数都正，替换 $(a,b)\mapsto(b,a+b)$ 保持此性质，纯 $\alpha$ 插入不减少 $\beta$。下一替换候选尺寸为 $H+\#\beta>H$，当前标签为 $0$，得到（TM.4422）。

式（TM.4406）的单射性保证不同源有不同 $N$，所以有不同 $U=H-N$；实际记录确实保存了不同的接受宏长度之和，式（TM.4423）已经由匹配协议的证明给出。终端当前商单独遗失原目标，实际取得记忆保留了它。引理 44.4 禁止的是同一完整记录之内的碰撞；这里终端商相同发生在不同记录之间，故不违反定理 30.2 或命题 38.1。只对一个共同记录作事后处理不能产生这些不同 $U$。$\square$

因此任意固定常数 $K$ 都不能给出在不改变标签和动作合同下、适用于全部可恢复实际限制族的接受替换深度上界：取 $D>\max(K,1)$ 即得反例。特别地 $D=4$ 排除统一三次，$D=7$ 排除统一六次。所有这些原源的全部纯代数历史相同，故三窗充分性与 $F^6=\operatorname{id}$ 不供应恒定的实际取得深度。它们仍供应既有代数运输；变化的是守卫所作用的 Fibonacci 资源投影及实际取得记录，不是代数定理的真值。

### 44.6 分离计费、来源与未决范围

标签字母表大小为一，没有来源特定标签位；替换最坏深度精确为 $D$，匹配协议在每个输入上都取 $D$，下界只要求任意成功协议至少有一个输入达到此深度。总来源调用界为（TM.4417），不主张最优总调用数。协议的纯 $\alpha$ 上下文总接受叶数精确为 $U=H-N\le H$；每个尝试宏长度至多 $H$，尝试宏的总叶长度保守地至多 $H\lceil\log_2 H\rceil+1$，含最终单叶。被拒宏也须供应，它的长度不是零成本；一次宏调用不等于一片物理叶或一个物理时间单位。

给定公开数值 $D,H,C_D,R_D,B_D$ 及字面 $d_i$，每个整数或向量坐标有 $O(\log(H+1))$ 位，$D$ 个向量的固定描述需 $O(D\log(H+1))$ 位。在线区间控制用常数个 $O(\log(H+1))$ 位整数，解码再用 $D$ 个代码位和常数个组成累加器，工作空间可取 $O(\log(H+1)+D)$ 位，另计固定描述、全部记录和输出。解码需要一次精确除法、位提取和至多 $D$ 次有符号向量加法；在给定公开数值及学校式整数算术下，区间控制加解码的保守位运算界为 $O((\log(H+1))^2+D\log(H+1))$。这些界不包含公共数值生成、Fibonacci 与最小公倍数计算、实际源生产及类别认证、上下文生成／传输和守卫实现。若只保留公式生成器，可省字面向量表，但须另付生成和算术费用；这里不宣布最小描述或最小记忆。

最小公开上限的一个具体实例为 $D=2$：$C_2=1$，$d_0=(-4,4)$、$d_1=(16,-8)$、$R_2=264$，代码集合为 $\{0,1,2\}$，原组成为 $(264,264),(260,268),(280,256)$。其 $\lambda_2$ 为 $1320,1324,1328$，故 $H_2=1328$；匹配协议累计接受的纯 $\alpha$ 长度分别为 $8,4,0$。同一公式给出 $H_3=13928,H_4=219160,H_7=8177578840$。这些数值只展示该构造，不构成小上限最优或普遍尺度最优结论。

文献与证明范围：初态识别、完整迹与首次选择合并的语义复用 §31.5 的 Panteleev 和 van den Bos–Vaandrager 来源，不移入它们的长度、复杂度或自动机表取得结论。实际正词与 Euler 认证复用原子卷引理 359.2、定理 360.2、推论 360.4；单出现资源、固定行为核、已知因子运输及原始目标配对分别复用引理 30.1、定理 30.2、引理 35.1、命题 38.1。Fibonacci 行列式、稀疏最小投影、首次分歧下界和匹配的宏取得／公式解码是这些供应上的 repo-derived 普通数学综合推导，不主张文献优先权或 Lean 核验。

该族只有初始标签 $2$，是实际 $\mathcal T_H$ 的公开限制族；当前标签 $0$ 的碰撞、上限等号、最后拒绝与零次成功上下文均已处理。结论不计算全族最优标签容量 $M_A(H)$、其节省缺口、任意混合标签表的紧凑完整边界、所有历史的紧凑表示或尖锐深度与上限增长率。也不恢复未知原树的原括号、叶路径、实际过去、绝对时间或物理时空，不把重算一个规范代表当作找回原树。一般紧凑性、独立的符号边界与投影计数／类别证书问题，以及完整持续空间—时间—边界—记忆恢复目标仍为未决。

## 追加锚（本行以下为增补区）

## 45. 实际历史的拒绝边界、四支撑分层与终端原始目标解码

### 45.1 同源目标、正材料运输与已取得窗口

**定义 45.1（固定来源及历史的语义对象）。** 固定公开整数 $H\ge1$，使用 §30 的实际非空有序 $\alpha/\beta$ 原树域 $\mathcal T_H$、固定活叶上限和动作合同。声明有限实际初始族 $\mathcal F\subseteq\mathcal T_H$、同源供应函数 $h:\mathcal F\to\mathcal L$，并固定一个已经实际达到的共同有限记录 $\omega$。该记录包含同一初始化、公共输入、供应值 $\ell\in\mathcal L$、每个动作及其上下文身份、实际 `accept`／`reject` 和真实当前 $E$ 读；自适应动作只依赖这些已取得量。读不改源；$\rho$ 或一个命名的实际非空正上下文 $v$ 的左／右拼接，以整个候选叶数 $\le H$ 为接受条件。拒绝不改变来源，不返回候选 $E$，也不把一个被拒宏拆为部分接受的单叶动作。

目标固定为同一初始来源的

$$
\tau(t)=q_H(t),\qquad t\in\mathcal F.
\tag{TM.4501}
$$

以 $s_\omega(t)$ 表示该来源沿此记录得到的实际当前来源。后续 $q_H(s_\omega(t))$ 描述当前未来行为，不重新定义 $\tau(t)$。共同记录下的配对采用命题 38.1 的 $(q_H(s_\omega(t)),\tau(t))$，不能把当前行为相同而初始目标不同的两行删为一行。

写初始组成 $c(t)=(a,b)$、初始资源 $z(t)=(m,n)=(a+b,a+2b)$，并置

$$
T=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
\lambda_k(t)=(1,0)T^kz(t)
 =F_{k+1}a+F_{k+2}b,
\qquad F_0=0, F_1=1.
\tag{TM.4502}
$$

因此 $m\ge1$、$m\le n\le2m$，且每个 $\lambda_k$ 严格为正。沿用 §§28、35 的三窗、乘法和运输：

$$
W_3(t)=(E_0(t),E_1(t),E_2(t)),\qquad
F(x_0,x_1,x_2)=(x_1,x_2,J(x_0)),
\qquad J^2=\operatorname{id}.
\tag{TM.4503}
$$

$J$ 保乘法。对 $j=3q+r$、$0\le r<3$，已有 $E_j(t)=J^q(E_r(t))$。这是数学窗口恒等式，不是取得未读窗口的端口。上下文的公开精确参数为 $W_3(v)$ 和

$$
D(v)=(d,e)=(\lambda_0(v),\lambda_1(v)),
\qquad 1\le d\le e\le2d.
\tag{TM.4504}
$$

这些参数的来源认证、取得和算术另计。三重群单位 $(1,1,1)$ 只表示没有外材料的代数因子，不表示一个可调用的空来源。

引理 30.1 的单出现与引理 35.1 的已知因子运输给出：若此记录已接受 $j$ 次 $\rho$，则有由已接受动作确定的已知整数对 $(U,V)$ 和已知单位三元组 $P,Q$，使每个存活来源同时满足

$$
\begin{aligned}
(\lambda_0(s_\omega(t)),\lambda_1(s_\omega(t)))
 &=T^jz(t)+(U,V),\\
W_3(s_\omega(t))&=P\odot F^j(W_3(t))\odot Q.
\end{aligned}
\tag{TM.4505}
$$

这里 $\odot$ 逐坐标乘法且保持左右次序；$(U,V)$ 是当前已知材料在真实替换次序下的贡献，不是未经运输的历史插入量。数学式可以对所有初始来源定义一个无守卫的正材料模板；是否实际沿记录到达仍由下面的精确过滤决定。

### 45.2 一个上界、逐深度拒绝下界与实际读的闭合表示

**定义 45.2（历史的源向表示及更新）。** 固定定义 45.1 的静态供应 $H,\mathcal F,h,\ell$。历史的可更新字段为

$$
\mathsf B_\omega=
(j,U,V,P,Q,I,(z_i)_{i\in I},r_0,\ldots,r_{j+1}),
\qquad I\subseteq\{0,1,2\}.
\tag{TM.4506}
$$

$z_i$ 只记录由实际当前读规范化取得的初始 $E_i$。初始化为 $j=U=V=0$、$P=Q=(1,1,1)$、$I=\varnothing$、$r_0=r_1=0$。下界字段统一取非负整数；一个尚无非平凡拒绝条件的方向取零。该字段定义的初始来源集合为

$$
\begin{aligned}
\mathcal A(\mathsf B)=\{t\in\mathcal F:\;&h(t)=\ell,\quad
 E_i(t)=z_i\ (i\in I),\\
 &\lambda_j(t)\le H-U,\quad
 \lambda_k(t)>r_k\ (0\le k\le j+1)\}.
\end{aligned}
\tag{TM.4507}
$$

以下更新始终使用动作前的字段，除非明确写为更新后的值。

1. 实际读返回 $e_\mathrm{obs}$ 时，先作已知单位算术
   $$
   y=P_0^{-1}e_\mathrm{obs}Q_0^{-1},\qquad
   j=3q+r,\quad z_r=J^q(y).
   \tag{TM.4508}
   $$
   将 $r$ 加入 $I$；若已经存有 $z_r$，实际读必须与之相同。其余字段不变。这里的逆只消去已知单位，不对未知实际来源作逆动作。
2. 任一侧的正上下文 $v$ 被拒绝时，不改变 $j,U,V,P,Q,I$，只置
   $$
   r_j\longleftarrow\max(r_j,0,H-U-d).
   \tag{TM.4509}
   $$
   若接受，则置 $(U,V)\leftarrow(U+d,V+e)$。右侧接受置 $Q\leftarrow Q\odot W_3(v)$；左侧接受置 $P\leftarrow W_3(v)\odot P$。保留全部读字段和下界。
3. $\rho$ 被拒绝时，不改变来源运输和读字段，只置
   $$
   r_{j+1}\longleftarrow\max(r_{j+1},0,H-V).
   \tag{TM.4510}
   $$
   若接受，则置
   $$
   (j,U,V,P,Q)\longleftarrow
   (j+1,V,U+V,F(P),F(Q)),
   \tag{TM.4511}
   $$
   保留已有下界，并为新末方向附加一个零下界。$j$ 是完整接受次数，不按三或六取模。

接受后要求一次当前读，就先作接受更新，再用真实读作第 1 项更新。被拒动作没有候选读供第 1 项使用；拒绝之后另发出的读只读取未改变的当前源。停机本身不改变来源集合，正确输出条件另由初始目标恒定性决定。

**定理 45.3（任意实际共同历史的精确过滤与旧接受条件消去）。** 对定义 45.1 的每个实际共同有限记录，按定义 45.2 更新得到的 $\mathcal A(\mathsf B_\omega)$，恰为能产生该完整记录的全部初始来源。每个这样的来源具有（TM.4505）的实际当前资源和三窗。所有先前接受的容量不等式由最终的一个上界 $\lambda_j\le H-U$ 推出；所有拒绝恰为每个 Fibonacci 方向上所保留的最大严格下界；所有实际读恰为至多三个已取得初始窗口等式。该结论不要求有限次拒绝或重复读提供新的区别。

证明。先固定记录中所有动作身份和接受／拒绝位，将已接受动作看作无守卫的正材料模板。对任意实际初始组成，拼接使当前叶数增加 $d>0$；$\rho$ 把当前 $(a',b')$ 变为 $(b',a'+b')$，故当前叶数增加 $b'\ge0$。因此沿这个模板，叶数始终非递减。一次全 $\alpha$ 当前源的 $\rho$ 可以保持叶数不变，不能把这里的非递减误写为严格递增。最终叶数 $\le H$ 就保证模板中每次被记录为接受的候选及初始叶数都 $\le H$，包括上限等号。

在当前字段下，一个上下文候选的守卫恰为

$$
\lambda_j(t)+U+d\le H,
\tag{TM.4512}
$$

而一个 $\rho$ 候选的守卫恰为

$$
\lambda_{j+1}(t)+V\le H.
\tag{TM.4513}
$$

所以拒绝分别给出（TM.4509）、（TM.4510）的严格反向不等式。同一方向的多道严格下界恰等价于最大下界。因每个实际 $\lambda_k\ge1$，负下界可以取零而不改变来源集合。没有引入被拒候选的新材料、窗口或当前尺寸。

实际读满足 $e_\mathrm{obs}=P_0E_j(t)Q_0$。已知因子可逆，且 $J^2=\operatorname{id}$，故（TM.4508）恰等价于 $E_r(t)=z_r$，包括 $q$ 的两种奇偶和全部六个相位。重复同一 $r$ 的规范化读不再细分该初始窗口纤维。

现在对记录长度归纳。初始（TM.4507）恰为给定供应值的初始族，因为 $\mathcal F\subseteq\mathcal T_H$，而两个零下界均自动满足。拒绝步保留旧最终上界，仅交上其实际响应对应的新下界；读步仅交上一个真实等式。上下文接受的新最终上界是（TM.4512），$\rho$ 接受的新最终上界是（TM.4513）；正材料的非递减性使新上界蕴含旧上界，因此无需再保留旧接受约束。其余下界和初始窗口等式均不变。引理 30.1 与引理 35.1 给接受后的资源和有序因子更新；拒绝和读不改来源，故（TM.4505）持续成立。

反向也在同一归纳中成立：满足新谓词的初始来源满足旧记录的全部条件，并对下一命名动作产生恰好该响应或真实读。既定控制器只依赖记录，故它在此来源上选择相同下一动作。它没有被额外提供任何隐藏的 $\eta$ 端口。于是谓词既不遗漏实际行，也不增添未曾按该记录执行的初始行，证明精确性。$\square$

### 45.3 配对延续充分性与表示计费

**命题 45.4（全部命名动作的响应、后继与原始目标闭合）。** 相对于固定 $H,\mathcal F,h,\ell$，字段 $\mathsf B$ 精确决定配对关系

$$
\mathcal P(\mathsf B)=
\{(q_H(s_\omega(t)),\tau(t)):t\in\mathcal A(\mathsf B)\},
\tag{TM.4514}
$$

并决定任意下一真实读、$\rho$ 和任意命名正左／右上下文的响应分支、各分支的字段更新和后继配对关系。两个具有同一字段的已达到历史，具有同一个源向延续问题。字段不要求重建旧完整记录、某个既定控制器的内部状态或费用计数。

证明。对每个 $t\in\mathcal A(\mathsf B)$，（TM.4505）给当前完整三窗与组成资源；由 $a'=2m'-n'$、$b'=n'-m'$ 和（TM.3003）求出当前 $q_H$，而 $\tau(t)$ 始终由初始来源求出。由定理 45.3，每一对都来自该历史下的同一个真实来源行。因此（TM.4514）没有混用两个不同实现。

下一读按 $P_0E_j(t)Q_0$ 分支，下一上下文按（TM.4512）分支，下一 $\rho$ 按（TM.4513）分支。定义 45.2 与定理 45.3 随即给出每个非空响应分支的精确后继。这里“决定分支”指决定候选的响应划分，不指控制器在调用前知道实际未知来源将选中哪一支。上下文的左右次序仍在 $P,Q$ 中，既不能交换，也不能丢弃。

两个同字段历史有相同初始候选、相同当前响应语义及相同初始目标。故从任一节点重新指定同一个延续程序，逐步更新将产生相同配对分支。若要延续某个依赖旧记录的特定程序，必须另保留它的程序状态，或把此节点的旧状态作为固定延续描述；本字段不重建它。这个区别不改变源向延续的存在性，但禁止把字段位数当作任意运行控制器的全部记忆。

停止并只按该共同节点输出一个目标，恰在 $\tau$ 在 $\mathcal A(\mathsf B)$ 上恒定时正确。若共同记录内有相同当前 $q_H$ 而不同 $\tau$，命题 38.1 已给出永久碰撞，任何未来允许动作都不能恢复全部目标。将该检验用于一个下一动作的每个实际响应分支，给出成功协议的必要动作条件；通过它不证明存在某个成功的全局策略，也不证明贪心地选此动作安全。全局存在性仍取定理 35.4 的既有嵌套取得条件，不另建一个改名判据。$\square$

**命题 45.5（与记录长度无关的源向字段上界）。** 在一个非空实际达到节点，采用 §28 的精确单位正规坐标接口时，定义 45.2 的可变源向字段可用

$$
O\bigl((\log_2(H+1))^2\bigr)
\tag{TM.4515}
$$

位表示，与 $\mathcal F$ 的表行数和完整记录长度无关。该界是充分表示界，不是最小记忆结论。

证明。推论 35.5 给 $0\le j\le J_H=O(\log(H+1))$，包括 $H=1$ 时的 $J_1=1$。对每次接受上下文和 $\rho$ 的更新归纳，有

$$
0\le U\le V\le2U.
\tag{TM.4516}
$$

上下文加上（TM.4504）的正锥向量；$T(U,V)=(V,U+V)$ 仍在此锥中。非空存活来源满足 $\lambda_j\ge1$ 和 $\lambda_j+U\le H$，故 $U\le H-1$、$V\le2H-2$。每个截为非负的拒绝阈值在 $[0,H]$ 内，至多 $j+2$ 个阈值各需 $O(\log(H+1))$ 位；法向量由其整数指标和 Fibonacci 递推生成，不额外存一列不断增长的矩阵。

已接受的已知材料在当前源中共含 $U$ 片叶。按未知单出现的左右位置分成两个已知叶词；任一空侧仅取代数单位。这两个词的总当前叶数不超过 $H-1$，它们的三窗分别为 $P,Q$。§28.3 的正规指数界因此把六个单位各压在 $O(H+1)$ 的整数范围内；符号和奇偶只需固定个位数。三个已取得初始窗口来自初始叶数 $\le H$ 的真实来源，其正规指数也为 $O(H+1)$。掩码 $I$ 只需三位，其余 $j,U,V$ 共需 $O(\log(H+1))$ 位。于是阈值列承担（TM.4515）的主项，其余字段只需 $O(\log(H+1))$ 位。$\square$

该计费把 $H$、供应标签值及其产生、静态实际族与 $h$ 的成员判定、来源认证、已知上下文参数、控制器状态、计划／解码器描述、完整档案、费用计数、上下文生成和传输、守卫实现、坐标转换计算及展开 Clifford 输出分别置于界外。拒绝一个很大的命名上下文无需把该候选的群值加入字段，但该上下文的输入长度和生产费用仍要支付。在线字段更新不要求列举所有来源行；判断目标恒定或选定全局动作，仍可能依赖静态供应的枚举、成员算法和原始目标计算，不能由（TM.4515）推出高效可行性算法。§30.3 的静态当前行为商位数、这里的未知源历史字段位数和任意控制器总记忆，是三个不同任务。定理 44.5 已证明可恢复实际族的必要接受替换深度无统一常数界；三窗和六周期不将这里的完整 $j$ 或拒绝法向量截为常数。

### 45.4 一个实际三窗纤维的四支撑分层

**定理 45.6（固定完整窗口的精确实际组成层）。** 固定一个实际完整三窗

$$
\Omega=L(u,v,w)R_{pq},\qquad
u,v,w\in\mathbb Z,\quad p,q\in\{0,1\},
\tag{TM.4517}
$$

其中 $L,R_{pq}$ 取[原子卷定义 359.1 与定理 359.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的唯一共同来源参数。置

$$
\begin{aligned}
X_0&=\max(0,u,-w,u-w-p),\\
Y_0&=\max(0,-u-q(1-p),v-pq,v-u),\\
a_*&=2w-2u+p,\qquad b_*=2u-2v+q.
\end{aligned}
\tag{TM.4518}
$$

对每个坐标划分两个互不相交的整数层

$$
D_X^0=\{X_0\},\quad D_X^1=\{X\in\mathbb Z:X\ge X_0+1\},
\qquad
D_Y^0=\{Y_0\},\quad D_Y^1=\{Y\in\mathbb Z:Y\ge Y_0+1\}.
\tag{TM.4519}
$$

令 $\mathcal S_\Omega\subseteq\{0,1\}^2$ 为通过以下角点检验的层指标：把 $(X,Y)=(X_0+i,Y_0+k)$ 代入原子卷（360.2），所得八边总数非零，且所有正边的端点连同 $00$ 弱连通。则全部实际非空来源的精确组成纤维为

$$
\{c(t):W_3(t)=\Omega\}
=
\bigcup_{(i,k)\in\mathcal S_\Omega}
\{(4X+a_*,4Y+b_*):(X,Y)\in D_X^i\times D_Y^k\}.
\tag{TM.4520}
$$

至多四个角点检验即分类整个固定窗口纤维；$(1,1)$ 总通过。在每个被纳入的组成上，原子卷定理 360.2 供应同一条实际正叶词及其有序括号来源。这里不把分别可实现的三个窗口拼为假想共同源，也不把所有非负八边都视为连通。

证明。原子卷定理 360.2 已供应整数性、端点流量及弱连通的充要条件，本证明只化简固定 $\Omega$ 后的支撑变化。其四条 $\alpha$ 边重数为

$$
(X+w-u+p, X+w, X, X-u),
\tag{TM.4521}
$$

故非负恰在 $X\ge X_0$。四条 $\beta$ 边重数为

$$
(Y+u+q(1-p),\ Y,\ Y-v+pq,\ Y+u-v),
\tag{TM.4522}
$$

故非负恰在 $Y\ge Y_0$。四条同字母边的总数分别为 $4X+a_*$、$4Y+b_*$，得到组成公式；顶点流量在这些参数下恒等地满足从 $00$ 到 $(p,q)$ 的要求，无需重复求解。

当 $X=X_0$ 时，$\alpha$ 支撑等于该最小点的支撑；当 $X\ge X_0+1$ 时，四个数都严格为正，故 $\alpha$ 支撑不再随 $X$ 变化。$Y$ 的两层同理。因此在（TM.4519）的每个 Cartesian 层上，八边正支撑恰等于该角点的支撑。非空性也在层上恒定：任一射线层至少有同字母的四条正边，只有双单点层可能为零边向量。于是非空与弱连通恰由四个角点决定，原子卷的充要判据逐点给出（TM.4520）。内层角点的八边全部严格为正，整个四状态图连通，所以 $(1,1)$ 通过。$\square$

这个层划分不是向上封闭正交锥。例如取 $\Omega=(A,B,S)=L(0,0,0)R_{10}$，有 $X_0=Y_0=0$、$a_*=1,b_*=0$。$(X,Y)=(0,0)$ 给组成 $(1,0)$，八边向量为

$$
(1,0,0,0; 0,0,0,0),
$$

由实际 $\alpha$ 实现；$(X,Y)=(1,0)$ 给组成 $(5,0)$ 和

$$
(2,1,1,1; 0,0,0,0).
$$

虽有非负整数重数和正确端点流量，其正支撑分为 $00$—$10$ 与 $01$—$11$ 两部分，原子卷定理 360.2 排除来源。因此增大 $X$ 会引入未连到起点的分量。四层检验保留了这种区别；此例属于定理的支撑边界证明，而非删去实际性后的放松。

### 45.5 实际取得全三窗后的饱和线与原始目标解码

**定理 45.7（全固定窗口实际类的条件终端判定）。** 固定一个非空实际达到节点，且定义 45.2 的 $I=\{0,1,2\}$：三个初始窗口都已由同一历史的真实当前读规范化取得，记为 $\Omega=(z_0,z_1,z_2)$。假设该节点存活初始来源恰为

$$
\{t\in\mathcal T_H:W_3(t)=\Omega,\quad
\lambda_j(t)\le H-U,\quad
\lambda_k(t)>r_k\ (0\le k\le j+1)\}.
\tag{TM.4523}
$$

这是完整固定窗口实际类与已观察资源条件的交，不含额外的不规则族／标签删选。该假设例如由初始族 $\mathcal T_H$ 且 $h$ 只依赖 $W_3$ 的供应给出。若只使用 §30 的读接口，$I$ 的三个不同指标意味着历史已接受至少两次 $\rho$，所以这里 $j\ge2$；下面线参数分离和饱和障碍的证明只用 $j\ge1$。

从这个节点开始，实际右接单叶 $\alpha$，直到第一次拒绝；即使入口已饱和也发出一次单叶并记其拒绝。对每个实际得到的填充分支：

1. 全部初始候选的 $(X,Y)$ 恰落在一条整数 Diophantine 线上与至多四个整数区间的交式表示中；每个区间对应定理 45.6 的一个支撑层，端点可由精确整数算术计算，无需枚举正词或所有组成。
2. 从这个已经达到的饱和分支，存在只用合同允许动作、逐点有限停止并正确输出全部初始 $q_H$ 的延续，当且仅当这些区间的并含恰好一个整数参数。
3. 单参数时可直接解码初始组成和初始 $q_H$。至少两个参数时，任意正左／右上下文、$\rho$、真实读及任意有限自适应组合，都不能恢复此共同记录内的全部初始目标。

证明。设入口的已知贡献为 $U_\mathrm{in}$，填充实际接受 $f$ 次。每次叶数增加一，且不改变 $j$；拒绝保持来源。若入口实际尺寸为 $M$，则 $f=H-M$，故这段取得有限，恰用 $f+1$ 次来源调用。最后尺寸为 $H$。填充后的已知贡献为 $U'=U_\mathrm{in}+f$，从真实响应及公开贡献取得

$$
C=H-f-U_\mathrm{in}=H-U',\qquad \lambda_j(t)=C.
\tag{TM.4524}
$$

这不是隐藏尺寸查询。最终上界是 $\lambda_j\le C$，最后单叶拒绝给 $\lambda_j>C-1$；若 $C=1$，截零下界仍给相同条件。因为资源为整数，两者恰给等式。非递减性使该等式蕴含此前所有填充接受条件，全部旧拒绝及读等式仍按定理 45.3 保留。于是（TM.4524）刻画该分支的准确来源切面，而非候选外包络。

令

$$
A_j=F_{j+1},\qquad B_j=F_{j+2},\qquad
K=\frac{C-A_ja_*-B_jb_*}{4}.
\tag{TM.4525}
$$

实际分支保证 $K\in\mathbb Z$。由 Euclid 算法和 Fibonacci 递推，$\gcd(A_j,B_j)=1$。取一个 Bézout 对 $x_j,y_j$，使 $A_jx_j+B_jy_j=1$，置 $\widehat X=x_jK$、$\widehat Y=y_jK$。定理 45.6 的组成式把资源等式恰化为

$$
A_jX+B_jY=K,\qquad
(X,Y)=(\widehat X+B_jk,\widehat Y-A_jk),\quad k\in\mathbb Z.
\tag{TM.4526}
$$

后式给全部整数解：任两解之差满足 $A_j\Delta X=-B_j\Delta Y$，互素性使 $\Delta X$ 为 $B_j$ 的倍数、$\Delta Y$ 为相应的 $-A_j$ 倍数；反向代入即成立。

现在分别与至多四个被纳入的支撑层相交。一个单点层给 $X=X_0$ 或 $Y=Y_0$，一个射线层给 $X\ge X_0+1$ 或 $Y\ge Y_0+1$。各旧拒绝条件仍为 $\lambda_i>r_i$。置

$$
a(k)=4\widehat X+a_*+4B_jk,\qquad
b(k)=4\widehat Y+b_*-4A_jk.
\tag{TM.4527}
$$

则每个严格下界等价于一条一元整数条件

$$
4(A_iB_j-B_iA_j)k
\ge r_i+1-A_i(4\widehat X+a_*)-B_i(4\widehat Y+b_*),
\qquad A_i=F_{i+1}, B_i=F_{i+2}.
\tag{TM.4528}
$$

初始 $a(k)+b(k)\le H$ 也可显式加入，虽它已经由最终尺寸及正模板非递减性推出。每条条件形如 $dk\ge e$ 或 $dk=e$。若 $d>0$，不等式给 $k\ge\lceil e/d\rceil$；若 $d<0$，给 $k\le\lfloor e/d\rfloor$；若 $d=0$，按 $0\ge e$ 判为全满足或空。等式在 $d\ne0$ 时要求整除并给一个参数，在 $d=0$ 时按 $e=0$ 判定。故每个层给一个精确整数区间，允许为空或单点。

区间有限：$A_j,B_j>0$，$X\ge X_0\ge0$、$Y\ge Y_0\ge0$，而（TM.4526）固定正系数的和，所以两个坐标有有限上界。支撑层互不相交，故所给参数区间也互不相交。取并恰给（TM.4523）与该填充记录允许的全部实际组成；定理 45.6 在每个组成上供应真实共同窗口来源，定理 45.3 又保证该来源沿相同真实记录达到节点。若单个组成有多个叶序或括号，它们仍在集合内，不被认作同一原树；它们只具有相同所需初始 $q_H$。

若区间的并含唯一参数 $k$，用（TM.4527）求出 $a,b$，再置 $m=a+b,n=a+2b$。记 $\mathbf u_\Omega$ 为 $\Omega$ 三个单位在 §28 的唯一正规坐标。作为（TM.3003）的统一初始解码式，返回

$$
\operatorname{dec}_H(\Omega,a,b)=
\begin{cases}
(0,E_0,m),&n>H,\\
(1,(a,b),E_0,E_1),&n\le H<m+n,\\
(2,\eta),\quad \eta=(\mathbf u_\Omega,(a,b)),&m+n\le H.
\end{cases}
\tag{TM.4529}
$$

这确实是初始目标，不是饱和后的当前边界。在本定理的真实三窗取得假设下，已经有两次接受的 $\rho$；无插入时的初始 $\lambda_2=m+n$ 不大于第二次接受候选的实际尺寸，故 $m+n\le H$，因此这里实际返回第三行。前两行只是统一初始 $q_H$ 的公式，不声称标签 $0,1$ 可以在此合同中经过真实读取得全三窗。所有窗口来自此历史实际取得数据，所有资源只来自公开贡献与真实守卫位。

若有两个不同参数 $k,k'$，初始叶数差为

$$
m(k)-m(k')=4(B_j-A_j)(k-k')=4F_j(k-k')\ne0,
\qquad j\ge1.
\tag{TM.4530}
$$

初始 $q_H$ 的标签 $0$ 直接保存 $m$，标签 $1,2$ 的组成也决定 $m$；因此不同参数必有不同初始目标。至少一次接受的 $\rho$ 把每个非空未知出现变成含 $\beta$ 的实际词：$\rho(\alpha)=\beta$、$\rho(\beta)=\beta\alpha$。后续正上下文不删除 $\beta$，后续 $\rho$ 也保留至少一片 $\beta$。饱和时全部候选当前尺寸为 $H$，下一 $\rho$ 的候选尺寸为 $H+\#\beta>H$，而任意正上下文添加 $d\ge1$ 也必超限，不论左右、叶序和括号。它们的当前读均为

$$
g=P'_0J^{\lfloor j/3\rfloor}(z_{j\bmod3})Q'_0,
\qquad q_H(s_\mathrm{sat}(t))=(0,g,H),
\tag{TM.4531}
$$

其中 $P',Q'$ 含已接受填充的已知因子。于是所有修改均拒绝、所有真实读均相同；每次拒绝后当前源仍不变。对任意依共同记录选择动作的延续归纳，未来记录始终相同，有限停止时只能给相同输出。不同初始目标不可同时满足。这也直接是定理 30.2 与命题 38.1 的共同历史永久碰撞。单参数解码给充分性，多参数碰撞给全动作必要性，证明三个断言。$\square$

同样的区间推导容许额外公开的有限条线性初始资源条件，只须在（TM.4528）旁加入它们；不改变每个层的一元区间形状。其来源合法性仍由实际 Euler 支撑供应，不能用连续多边形或非整数解代替。此定理只判定已经达到的饱和分支，不判定在未饱和节点选择填充是否保护目标，也不证明某个全三窗取得前缀存在。未经真实取得的数学 $\Omega$ 不满足它的读前提。

### 45.6 任意族或来源依赖标签的精确剩余条件

**命题 45.8（不规则供应下的终端修正）。** 保留定理 45.7 的真实三窗取得和饱和历史，但允许任意定义 45.1 的实际初始族与来源依赖 $h$。令 $\mathcal K_\mathrm{full}$ 为忽略静态族／标签删选后，按四支撑层、记录资源条件和（TM.4526）得到的至多四区间之并。实际参数集合恰为

$$
\begin{aligned}
\mathcal K_\mathrm{actual}=\{k\in\mathcal K_\mathrm{full}:\;&\exists t\in\mathcal F,\quad h(t)=\ell,\\
&W_3(t)=\Omega,\quad c(t)=(a(k),b(k))\}.
\end{aligned}
\tag{TM.4532}
$$

在该非空实际饱和分支，原始目标可恢复恰在 $|\mathcal K_\mathrm{actual}|=1$。任意静态族／标签删选可在 $\mathcal K_\mathrm{full}$ 中制造任意孔洞，所以一般不能宣称实际参数仍为至多四个区间；未供应成员判定或有效枚举时，（TM.4532）只是语义条件，不是免费的终端计算接口。

证明。定理 45.3 的候选谓词同时保留实际成员与同源标签。已固定 $\Omega$ 和组成的两个初始来源，其全部窗口读、受守卫资源以及已知因子运输都相同，故在既定记录上具有同样响应；初始 $q_H$ 也相同。因此一个完整类参数进入实际分支，恰在该组成与窗口上存在满足初始成员及标签的真实来源，得到（TM.4532），不要求该组成的全部树都属于 $\mathcal F$。

（TM.4530）的初始目标分离与（TM.4531）的饱和碰撞不依赖族是否规则，所以单参数仍可由（TM.4529）解码，多参数仍被全部允许动作排除。为见孔洞没有一般限制，在任何给定有限 $\mathcal K_\mathrm{full}$ 的每个参数上用定理 45.6 选一个真实代表。声明其中任意非空子集为 $\mathcal F$ 并供应常量标签，或保留这些代表并给任意子集同一个标签值，就得到该子集的实际参数。于是任意稀疏删选都可以发生。若此静态供应仅是语义定义而没有可用成员算法、可枚举表或认证接口，字段更新仍由实际动作闭合，但在（TM.4532）上计算唯一性需要另给取得与计算条件。$\square$

### 45.7 相同数学窗口下的真实目标碰撞与安全取得

**命题 45.9（一个参数化单位双源的先替换失败与零替换取得）。** 对任意整数 $r,s\ge1$，使用原子卷推论 360.4 的实际正词 $\omega_{r,s}$ 并固定一个有序二叉括号化。取

$$
U=\omega_{r,s+1},\qquad V=\omega_{r+2,s},\qquad
H=N=4r+8s+8.
\tag{TM.4533}
$$

这两个初始实际源都满足 $W_3=(1,1,1)$，初始标签均为 $1$，目标不同。共同第一步接受 $\rho$ 后，二者在同一记录内具有相同当前 $q_H$，全部合同允许动作都不能再恢复两个原始目标。另一方面，给两源同一供应标签，从未经修改的初始族 $\{U,V\}$ 用单叶 $\alpha$ 右填充直到第一次拒绝，且不接受任何 $\rho$，可以取得各自初始目标。

证明。推论 360.4 已提供共同单位三窗及实际词，不重证其构造。组成和资源为

$$
\begin{array}{c|ccc}
 &c=(a,b)&m=a+b&n=a+2b\\ \hline
 U&(4r,4s+4)&4r+4s+4&N\\
 V&(4r+8,4s)&4r+4s+8&N.
\end{array}
\tag{TM.4534}
$$

八边证书分别为 $(r,r,r,r;s+1,s+1,s+1,s+1)$ 和 $(r+2,r+2,r+2,r+2;s,s,s,s)$。所有八边严格正，起终点均为 $00$，出入平衡且弱连通；它们认证同一个实际源同时具有声明窗口和组成，而非独立地认证三个读。两源均有 $m\le H$、$n=H<m+n$，故初始 $q_H=(1,c,1,1)$ 且组成不同。

第一步 $\rho$ 恰在上限等号接受，当前叶数同为 $N=H$、当前读均为 $1$，下一候选尺寸为初始 $m+N>H$。故当前 $q_H$ 均为 $(0,1,H)$，实际响应及接受后任何真实读也相同。所有正上下文超限，$\rho$ 超限，读均相同；拒绝不改源，故任意自适应延续仍有同记录。不同初始目标被命题 38.1 永久合并。

从未经修改的初始节点改用实际单叶填充，成功次数分别为

$$
f_U=H-m_U=4s+4,\qquad f_V=H-m_V=4s.
\tag{TM.4535}
$$

它们在第一拒绝前取得不同真实记录，已知两源的目标字典按该计数给出正确初始输出。成功和最后拒绝都是真实调用；无重置、隐藏组成／尺寸读、被拒候选窗口或来源逆操作。也可一次尝试命名的非空纯 $\alpha$ 宏，长度 $H-m_U=4s+4$，其守卫在 $U$ 上接受、在 $V$ 上拒绝，直接分开两源。该宏是整候选原子检验，不把被拒候选串行化。

这两个协议是事先选择的不同取得路线，不是在已经执行共同 $\rho$ 后撤销它。数学上知道二者的单位三窗，不等于三个窗口已由当前读取得；因此零替换协议不是定理 45.7 的全三窗前提实例。该双源还说明源向表示必须保留初始来源与目标关联，而不能仅保留当前商或六周期相位。$\square$

### 45.8 关系恢复的条件与范围

**推论 45.10（取得记录、资源边界与终端目标的条件恢复链）。** 在定义 45.1 的固定合同和静态供应下，每份实际共同历史确定定义 45.2 的精确源向字段；此字段确定全部候选的当前运输和初始目标配对，并在每个命名动作的实际响应后闭合更新。在定理 45.7 的完整固定窗口实际类上，已经取得的三窗把资源候选化为定理 45.6 的四支撑层，真实终端填充又把它切到 Fibonacci 整数线；唯一线参数足以恢复初始目标，多参数则构成共同记录内的全动作不可恢复证书。

证明。前三项依次为定理 45.3、命题 45.4、定理 45.6；真实填充等式、唯一参数解码和多参数碰撞为定理 45.7。它们均对同一初始实际源及其本人取得的记录取值。故这里的时间动作记录、资源边界和已取得窗口记忆可以在这些条件下恢复目标，不需要把边缘窗口的分别实现冒作联合来源。$\square$

字段是对指定未来来源响应与目标的充分表示，不能由它逆恢复被舍弃的完整旧记录。它也不恢复原树括号、叶路径、完整历史调用数、物理时间或物理空间；若把这些量加入目标或观察合同，充分性必须重新证明。只有三个数学窗口不保证一个忠实取得前缀，饱和分支可判定也不保证全局策略存在。接受替换深度的通用 $J_H$ 上界取推论 35.5，可恢复族的任意必要深度与匹配取得取定理 44.5；这里没有将其仍称为未解决，也没有以周期性削弱它。

数学来源及文献范围：Clifford 单位正规坐标、$F,J$ 与正材料单出现分别复用 §§28–30、引理 35.1；全动作行为核与初始目标碰撞复用定理 30.2、命题 38.1；全局取得存在性复用定理 35.4；实际三窗共同来源与 Euler 认证复用[原子卷 §§359–360](FIBONACCI_ATOMIC_RELATION_GENERATION.md)。初态识别与完整迹的方法背景沿用 §31 的 Panteleev，*Preset Distinguishing Sequences and Diameter of Transformation Semigroups*，arXiv:1412.0034v1，及 van den Bos–Vaandrager，*State Identification for Labeled Transition Systems with Inputs and Outputs*，arXiv:1907.11034v2；它们不供应本章的正材料、Fibonacci 上限或实际源类别结论。Cousot–Halbwachs，[*Automatic discovery of linear restraints among variables of a program*](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL78.shtml)，POPL 1978，84–97 页，提供线性关系表示的成熟背景；这里的整数半平面是实际记录的精确条件，不是以凸包替代不规则成员集合。旧接受约束消去、四支撑层、终端一元区间解码及其实际条件是上述供应上的 repo-derived 普通数学综合推导，不主张文献优先权或 Lean 核验。

（TM.4515）没有证明最优／最小记忆、总描述最优或算术最优；四区间结果没有免除来源成员／标签取得，命题 45.8 已列出任意供应的额外义务。全族 $M_A(H)$、其节省缺口、全局最少调用、任意族的高效全局策略计算、原树恢复及完整物理时空解释，均不由本章确定。

## 追加锚（本行以下为增补区）
## 46. 共同窗口有序资源类的单线取得证书与对数上限尺度

本章使用 §30 的同一实际正来源、固定活上限、当前 $E$ 读和受守卫动作合同。目标始终是同一初始来源的 $q_H$，标签与初始化保持原供应。定理 44.5 已给出任意精确必要接受替换深度；定理 45.3 已给出任意实际历史的精确来源过滤。本章处理一个有明确资源序关系的共同完整窗口类：把 §35 的分支嵌套证书压成一条继续取得序列，并由此推出全动作投影计数障碍。在原子卷已有单位正词上，所得密集网格族同时具有必要深度、合法解码与尖锐的族内对数尺度。普通数学证明不构成当前 Lean 内核核验；这些类条件不是免费提供的隐藏资源端口。

### 46.1 实际类、原始目标与两个资源序条件

**定义 46.1（共同窗口有序资源类）。** 固定公开整数 $H\ge1$，声明非空有限实际族 $\mathcal F\subseteq\mathcal T_H$。每行必须由同一实际非空有序 $\alpha/\beta$ 原树认证，使用引理 30.1 的真实资源、窗口与守卫。给定同源标签 $h$，本类只含一个固定供应值 $\ell$ 的纤维；不增加标签，不把类别成员认证计为标签输出。控制器初始化相同，所有动作及命名上下文只依赖公共供应和已取得完整记录，并须逐点有限停止。实际族及其精确表、上下文供应、算术和解码器的费用分别计算。

目标为 $\tau(t)=q_H(t)$，右端取初始来源。按命题 38.1，在每个不同初始目标上保留一个实际代表，记代表表为 $C$；不能按当前商去掉不同初始目标。相等初始 $q_H$ 的其他代表在同一程序上有相同全部响应及接受替换次数，因此在 $C$ 上正确的协议也在整个 $\mathcal F$ 上正确。以下资源条件可先在全族核验，再选代表；若只在选定代表上核验，结论也经此行为同余扩展至原族。

令 $F_0=0,F_1=F_2=1$，$F_{i+2}=F_{i+1}+F_i$，并置

$$
 v_0(t)=\binom{\lambda_0(t)}{\lambda_1(t)},\qquad
 T=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
 \lambda_j(t)=(1,0)T^jv_0(t).
 \tag{TM.4601}
$$

要求有同一个完整数学窗口 $W_3(t)=\Omega$，且

$$
 \min_{t\in C}\lambda_1(t)\ \ge\ \max_{t\in C}\lambda_0(t),
 \qquad
 \min_{t\in C}\lambda_2(t)\ \ge\ \max_{t\in C}\lambda_1(t).
 \tag{TM.4602}
$$

初始标签 $0,1,2$ 可以混合。$\Omega$ 与每行资源是已认证离线表的坐标，不要求它们已经通过在线读全部取得；在线选择不能直接查询未知行的这些字段。条件允许等号。替换深度是完整实际执行中 `accept` 的 $\rho$ 数，拒绝的 $\rho$、上下文、读和算术不混入此数。

### 46.2 保序与混合拼接的终端化

**引理 46.2（共同历史上的唯一继续分支）。** 在定义 46.1 的类上，对任意实际共同动作历史，若已接受 $j$ 次 $\rho$，存活行的当前资源同时具有

$$
 \binom{m(t)}{n(t)}=T^jv_0(t)+b,\qquad
 b=(b_0,b_1)^{\mathsf T},\qquad 0\le b_0\le b_1\le2b_0,
 \qquad \min n\ge\max m.
 \tag{TM.4603}
$$

该历史下的全部当前读相同。一个在该表上同时有接受和拒绝行的正上下文拼接，把其全部接受行送到当前标签 $0$；接受支路只能终端解码，其原始目标必须是动作前 $m$ 的函数。一次 $\rho$ 的拒绝支路也只有终端解码能力，原始目标必须是当前 $m$ 的函数。此结论覆盖任意命名实际正词、任意左／右位置、任意既有记录和重复拒绝。

证明。对任意有序源对 $s,t\in C$，置 $\Delta_j=\lambda_{j+1}(s)-\lambda_j(t)$。（TM.4602）给 $\Delta_0,\Delta_1\ge0$，而递推给 $\Delta_{j+2}=\Delta_{j+1}+\Delta_j$。故对所有 $j\ge0$、所有有序源对都有 $\lambda_{j+1}(s)\ge\lambda_j(t)$。引理 30.1 和命题 39.8 供应实际的单出现仿射运输。一个已接受上下文增加实际整数对 $(d,e)$，$1\le d\le e\le2d$；一次接受替换将贡献 $b$ 变为 $Tb$。此锥从零起在两种更新下封闭，拒绝不改变它，得到（TM.4603）。限制存活表仍保留该序关系。

共同完整窗口按已有 $F$ 律运输；在同一动作历史中，实际读恰为相同已知左因子、相同运输窗口与相同已知右因子的有序乘积。因此读不能分开该表。它没有查询未经许可的深窗，也不把不同左右词的因子交换。

现在考虑一次增量 $(d,e)$ 的混合拼接。选一个拒绝行 $r$，其真实守卫给 $m(r)+d>H$。每个接受行 $s$ 满足

$$
 n(s)+e\ge m(r)+d>H.
 \tag{TM.4604}
$$

故其新当前标签为 $0$。同一接受支路内，若两行有相同动作前 $m$，则新当前尺寸相同、读相同、标签同为 $0$；它们有同一过去记录及同一当前 $q_H$。定理 30.2 与命题 38.1 排除不同原始目标的恢复。反之，目标是 $m$ 的函数时，实际取得尺寸后即可按原目标字典解码。这里的严格不等式来自真实拒绝，因此（TM.4602）的等号无须排除。

$\rho$ 拒绝恰为 $n>H$。此支路当前标签为 $0$，以后正材料只增加下一候选尺寸，不会重新打开替换；同 $m$ 的不同目标仍有共同读与当前商碰撞。它只能按 $m$ 终端解码。混合上下文的拒绝支路源不变；$\rho$ 的接受支路是唯一可能继续接受替换的支路。全部响应和读均属同一实际行与它本人取得的历史。$\square$

引理中的“终端”允许继续正拼接以取得尺寸，不要求立刻停机；它表示此后不能再接受 $\rho$，且同 $m$ 的区别无法取得。全过程已有多少档案位不改变这个共同记录内的碰撞。

### 46.3 没有递归子证书的有限算术证书

**定义 46.3（单线取得证书）。** 取有限整数 $k\ge0$，初始 $C_0=C$、$b_0=(0,0)^{\mathsf T}$。这里 $b_j$ 表示第 $j$ 阶段的向量，$b_{j,0},b_{j,1}$ 表示其坐标。对 $t\in C_j$ 定义

$$
 \binom{m_j(t)}{n_j(t)}=T^jv_0(t)+b_j.
 \tag{TM.4605}
$$

每个 $0\le j<k$ 供应三个整数 $p_j,d_j,e_j$，满足下列全部有限表条件：

1. $0\le p_j<H$。令 $F_j=\{t\in C_j:m_j(t)\le p_j\}$、$S_j=C_j\setminus F_j$。要求 $S_j\ne\varnothing$，且 $F_j$ 在 $m_j$ 上单射。
2. $0\le d_j\le e_j\le2d_j$，且对全部 $t\in S_j$ 有 $m_j(t)+d_j\le H$。零对只表示省略动作，不是空上下文。
3. 令 $R_j=\{t\in S_j:n_j(t)+e_j>H\}$，要求 $R_j$ 在 $m_j$ 上单射。
4. 令 $C_{j+1}=\{t\in S_j:n_j(t)+e_j\le H\}$，要求其非空，并逐行保留同一初始目标 $\tau(t)$。置

$$
 b_{j+1}=T\left(b_j+\binom{d_j}{e_j}\right).
 \tag{TM.4606}
$$

终端要求 $C_k$ 在 $m_k$ 上单射。$k=0$ 时只有该要求。这里“单射”针对按不同目标保留的行；空退出集自动满足它。$F_j,R_j,C_k$ 的字典将实际取得的当前阶段尺寸送到该行原始 $\tau$，不能输出修改后当前商来替代目标。

证书只含一个继续表序列、每阶段三个整数、仿射贡献及终端目标关联，没有分支子证书或继续可行性 oracle。共同窗口只需供应一次；静态实际表和它的源—目标关联仍须保留或可计算取得。该结构没有声明表取得免费、证书搜索高效或最小记忆。

### 46.4 深度保持的全动作充要对应

**定理 46.4（共同窗口有序资源类的精确取得证书）。** 对定义 46.1 的每个类及每个整数 $D\ge0$，以下两项等价：有一个使用 §30 全部允许动作、逐点有限停止、正确取得初始 $q_H$ 且最坏接受替换深度不超过 $D$ 的确定性协议；有一个定义 46.3 的证书，其长度 $k\le D$。

更强地，从任一成功协议可取得证书与合法执行器，保持每个保留初始目标上的接受替换次数；长度 $k$ 恰为该协议的最坏接受替换深度。反向，每个长度 $k$ 的证书有最坏深度恰为 $k$ 的实际执行器。因此成功时最优深度恰为可行证书的最小长度。此对应只保持所述深度与原始输出，不声称完整物理记录、总调用或上下文费用相等。

证明。先证必要性与深度保持。在每个阶段加入一次不改来源的真实当前读，再用引理 35.2 压缩首次尝试 $\rho$ 或停止之前的整个无替换阶段。每个占用块的端点 $c=H-d$ 和准确下一资源增量 $e$ 均保留，满足 $0\le d\le e\le2d$。右侧规范宏与原模板同组成；引理 35.1 以有序已知因子运输其延续。这个模拟对每个行保留每次替换守卫、动作选择与原始输出，所以每次接受 $\rho$ 一一对应；加入读及重建虚拟记录不增加接受替换。

在该阶段全表上令 $M=\max m_j$。如果某个 R 块有非空接受替换部分，则该部分某行满足 $n_j+e\le H$，由引理 46.2 有

$$
 H-e\ge\min_{C_j}n_j\ge M,
 \qquad c=H-d\ge H-e\ge M.
 \tag{TM.4607}
$$

所以这个块必为最后占用块；不能另有一个接受继续的 R 块。即使 $c=M$，仍没有更晚占用尺寸。更早的占用块只能是 F，或是替换全拒绝的 R；定理 35.4 的必要条件使它们在各自 $m_j$ 行上目标恒定。每个尺寸只属于一个占用块，故其联合是单射的尺寸前缀。选 $p_j$ 为该前缀的最后占用尺寸；无前缀时取零。保留最后 R 块原来的准确 $(d_j,e_j)$，不因端点与占用最大尺寸之间的空隙移动宏增量。前缀为 $F_j$，其余为 $S_j$，替换拒绝部分为 $R_j$，接受部分为 $C_{j+1}$，恰满足定义 46.3。

接受后的全体行仍有一个共同完整窗口，因而只有一个真实读纤维；实际资源更新正是（TM.4606）。在这一实际子表上重复。若某阶段没有接受继续的 R 块，全部占用块均是终端尺寸函数，它们的联合也在 $m_j$ 上单射，得到终端条件。共同记录中的不同目标不能被删掉；它们在表内各随真实守卫退出或继续。

原协议每行有限停止，有限行的到达路径并也有限。只有一条接受继续序列，故此构造终止。也可用推论 35.5 的统一 $J_H$ 界。F 块在原协议该阶段中尚未尝试替换即停止；R 拒绝退出以后处于标签 $0$，原协议也不可能再接受替换。二者换成终端尺寸取得不改变接受次数；接受支路的运输逐次保留计数。故各目标原有深度原样保留，而非只证明存在另一个较浅协议。某行走到最后继续阶段，给 $k$ 等于原协议最坏深度。

再证充分性，给出只依赖真实响应的执行器。在阶段 $j<k$，若 $F_j$ 非空，一次原子右接实际 $\alpha^{H-p_j}$。其长度为正，接受恰为 $m_j\le p_j$。接受时右接单叶 $\alpha$ 到第一次拒绝；若成功 $f$ 次，则

$$
 m_j=p_j-f.
 \tag{TM.4608}
$$

按 $F_j$ 字典输出原始目标。若前缀宏拒绝，源不变并进入 $S_j$；$F_j$ 为空时直接省略该宏。

在 $S_j$ 上，若 $d_j>0$，一次原子右接固定有序括号的实际词

$$
 K_j=\alpha^{2d_j-e_j}\beta^{e_j-d_j}.
 \tag{TM.4609}
$$

其资源增量恰为 $(d_j,e_j)$，长度 $d_j>0$；一个子块指数为零只省略该子块。条件 2 保证全体接受。零对省略此动作。随后尝试 $\rho$：拒绝的真实响应选中 $R_j$，源保持为宏后源；用单叶填充到第一次拒绝，成功 $f$ 次时 $m_j=H-d_j-f$，按 $R_j$ 字典解码。接受的真实响应选中 $C_{j+1}$，实际后继资源为

$$
 (m',n')=(n_j+e_j,\ m_j+n_j+d_j+e_j),
 \tag{TM.4610}
$$

故按（TM.4606）进入下一阶段。到第 $k$ 阶段填充，成功 $f$ 次给 $m_k=H-f$，按终端字典输出。每次填充都包含最后一次非空单叶拒绝，包括 $f=0$；未知资源不被预先查询，被拒候选不提供读。

所有行在 $F_j,R_j$ 或 $C_k$ 恰退出一次，输出均是原目标。每个阶段前的宏选择只依赖真实守卫及公开计划；任意宏均整候选原子执行，不能将被拒宏串行化。填充只用于已证明安全的终端支路。非空 $C_k$ 保证至少一行接受恰 $k$ 次替换，其余不超过 $k$，得精确最坏深度。相等初始目标的其他实际代表依定理 30.2 产生同样响应、计数和输出，完成全族证明。$\square$

这里没有在线查询 $n_j$ 来选 $C_{j+1}$：该集合由实际替换响应选择。必要性中的任意左右上下文通过同组成和已知因子运输处理，不把它们的字面读视为相等。证书执行器可不作窗口读，因为其公共实际表已限定共同完整窗口；加入一次真实初读只增加一项来源调用。有限表给定时，$k\le J_H$、$p_j<H$、$d_j\le H-1$、$e_j\le2H-2$ 使证书可有限枚举。这是可判定的充要描述，不是多项式搜索或控制器最小化定理。

### 46.5 所有动作下的资源投影障碍

**推论 46.5（逐深度投影计数必要条件）。** 在定义 46.1 的类上，记不同初始目标数 $N=|C|$，并令

$$
 N_j=\bigl|\{\lambda_j(t):t\in C\}\bigr|.
$$

若有最坏接受替换深度至多 $D$ 的成功协议，则

$$
 N\le\sum_{j=0}^{D}N_j.
 \tag{TM.4611}
$$

这是该类的全动作障碍；它不假设纯 $\alpha$ 上下文、预定策略、有限档案位数或独立尺寸读端口，也不是充分条件。

证明。定理 46.4 给 $k\le D$ 的单线证书。在第 $j<k$ 阶段，退出的 $F_j$ 与 $R_j$ 各在 $m_j$ 上单射，且前者 $m_j\le p_j$、后者 $m_j>p_j$。故其联合对每个 $m_j$ 至多退出一个不同初始目标。由（TM.4605），共同偏移 $b_{j,0}$ 使相等 $m_j$ 恰等于相等初始 $\lambda_j$，所以此阶段至多退出 $N_j$ 个目标。终端 $C_k$ 同理至多 $N_k$ 个。每个初始目标恰计一次，求和得到（TM.4611）。禁止同一退出行携带两个目标的是共同记录内的当前标签 $0$ 碰撞；任意大的档案不增加这一计数。$\square$

### 46.6 实际单位正词网格、必要深度与合法解码

**定理 46.6（密集实际族的两步深度夹界）。** 对每个整数 $K\ge0$，置

$$
 R=F_{K+5},\qquad B=2R,\qquad
 H_K=4(3R-1)F_{K+6},\qquad d_*=K+3.
 \tag{TM.4612}
$$

对每个 $B\le r,s\le B+R-1$，取[原子卷推论 360.4](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 已有字面正词的固定左结合有序括号化

$$
 \omega_{r,s}=\alpha^{2r-1}\beta^{2s}\alpha
                 \beta^{2s-1}\alpha^{2r}\beta,
 \qquad \mathcal G_K=\{\omega_{r,s}:2R\le r,s<3R\}.
 \tag{TM.4613}
$$

在每个公开上限 $H\ge H_K$，给此族同一个常量供应标签，所有 $R^2$ 初始目标都不同、都为标签 $2$，且全族满足定义 46.1。记全部允许协议中的最小最坏接受替换深度为 $d_{\min}(\mathcal G_K;H)$，则

$$
 K+1\le d_{\min}(\mathcal G_K;H)\le K+3.
 \tag{TM.4614}
$$

显示的执行器在每行接受恰 $d_*$ 次 $\rho$，不需要窗口读，来源调用至多

$$
 K+3+\lceil\log_2 H\rceil+1.
 \tag{TM.4615}
$$

上界给达到的深度，不声明区间内的精确最优；下界覆盖任意正左右上下文、拒绝探针、自适应控制及不限长取得记录。

证明。原子卷推论 360.4 同时供应 $c=(4r,4s)$、$W_3=(1,1,1)$ 和同一个实际词。其定理 360.2 的八边认证在本族为四条 $\alpha$ 边各 $r$ 次、四条 $\beta$ 边各 $s$ 次，起终点均为 $00$，全部重数严格正、流量平衡、支撑弱连通。因而窗口、资源和实际原树属于同一实现，不是自由整数元组。全部所写指数为正。已有窗口运输固定单位三元组，故完整数学历史均为 $E_j=1$。

由同一实际组成有

$$
 \lambda_j(\omega_{r,s})=4(F_{j+1}r+F_{j+2}s).
 \tag{TM.4616}
$$

故 $\min\lambda_1=24R>24R-8=\max\lambda_0$，$\min\lambda_2=40R>36R-12=\max\lambda_1$。同时 $\lambda_2\le20(3R-1)<H_K$，因 $F_{K+6}\ge8$。于是每个初始目标为 $(2,\eta)$，其组成区分全部 $R^2$ 行；常量标签未供应这个未知组成。还有 $\lambda_3\le32(3R-1)\le H_K$，所以 §39 的严格 $\lambda_3>H$ 假设在此全族不成立，不能用它的两层完整性替代本证明。

证明必要深度。写 $r=2R+i,s=2R+l$，$0\le i,l<R$。第 $j$ 投影的可变部分除以四为 $F_{j+1}i+F_{j+2}l$，取值在整数区间 $[0,(R-1)F_{j+3}]$，所以

$$
 N_j\le(R-1)F_{j+3}+1.
 \tag{TM.4617}
$$

若有深度至多 $K$ 的成功协议，推论 46.5 与 Fibonacci 求和给

$$
 \begin{aligned}
 R^2&\le\sum_{j=0}^{K}\bigl((R-1)F_{j+3}+1\bigr)\\
    &=(R-1)(F_{K+5}-3)+K+1
      =R^2-4R+K+4.
 \end{aligned}
 \tag{TM.4618}
$$

但 $F_5=5$，之后每个增量至少一，所以 $R=F_{K+5}\ge K+5$，右端严格小于 $R^2$。矛盾。这个必要性对全部 $H\ge H_K$ 成立，不是从长合法路径推得；它不重复定理 44.5 的任意深度存在结论，而是使用新类证书限制每阶段能释放的初始目标数。

给出合法上界及记录解码。先纯执行 $d_*=K+3$ 次 $\rho$，没有正上下文。实际叶数单调增加，最后尺寸

$$
 N_{\mathrm{term}}=4(ar+Rs),\qquad a=F_{K+4},\qquad
 N_{\mathrm{term}}\le4(3R-1)(a+R)=H_K\le H.
 \tag{TM.4619}
$$

所以每一步真实接受。在 $H=H_K,r=s=3R-1$ 时最后一步恰取上限等号，仍接受。证书在这些阶段取 $p_j=d_j=e_j=0$、$C_j=C$；终端尺寸的单射性由下面解码式给出。

终端尺寸取得直接复用定理 44.5 证明中的原子二分宏。为明确其适用域，入口未知尺寸只要求 $1\le N_{\mathrm{term}}\le H$；初始化 $l=0,u=H,U=0$。在 $u-l>1$ 时置 $c=\lfloor(l+u)/2\rfloor$，一次原子右接实际非空 $\alpha^{u-c}$。真实候选为 $N_{\mathrm{term}}+U+u-c=N_{\mathrm{term}}+H-c$，故接受恰为 $N_{\mathrm{term}}\le c$。接受置 $u=c$ 并增加实际 $U$，拒绝只置 $l=c$；其不变量为

$$
 l<N_{\mathrm{term}}\le u,\qquad U=H-u,\qquad
 \lambda(t_{\mathrm{cur}})=N_{\mathrm{term}}+U.
 \tag{TM.4620}
$$

最多 $\lceil\log_2H\rceil$ 次宏调用后整数宽度为一，取得 $N_{\mathrm{term}}=H-U$，实际当前尺寸为 $H$；再发单叶 $\alpha$，候选 $H+1$ 拒绝。即使 $N_{\mathrm{term}}=H$、$U=0$，最后拒绝仍存在。没有读取被拒宏，没有将它拆成部分接受，也没有隐藏尺寸端口。

相邻 Fibonacci 数互素：Euclid 递推降至 $F_2=F_1=1$。公开选 $u_a$ 为 $a$ 模 $R$ 的逆，取最小非负余数。由已取得 $z=(H-U)/4$ 计算

$$
 r=2R+(u_a z\bmod R),\qquad s=\frac{z-ar}{R}.
 \tag{TM.4621}
$$

区间 $[2R,3R-1]$ 每个模 $R$ 余数恰出现一次；$z=ar+Rs$ 保证（TM.4621）恢复原 $r,s$，第二商为整数并落在声明区间。这同时证明终端投影单射。返回初始标签 $2$、单位窗口和组成 $(4r,4s)$，即本人原始 $q_H$，而不是填充后的商。执行只使用公共数据、宏身份和真实响应，逐点有限停止；$d_*$ 次替换及二分宏与最后拒绝给（TM.4615）。$\square$

### 46.7 必要深度与上限的定量尺度

**推论 46.7（族内尖锐对数率与类的最坏阶）。** 令 $\varphi=(1+\sqrt5)/2$，所有此处对数取自然对数。对（TM.4612）的实际族和最小显示上限有

$$
 \frac{H_K}{R^2}\longrightarrow12\varphi,\qquad
 |\mathcal G_K|=R^2=\Theta(H_K),\qquad
 d_{\min}(\mathcal G_K;H_K)
 =\frac{\log H_K}{2\log\varphi}+O(1).
 \tag{TM.4622}
$$

显示执行器的达到深度 $K+3$ 具有同一个主系数，距离最优至多两次接受替换。更一般地，对每个整数 $H\ge H_0=448$，选最大的 $K$ 使 $H_K\le H$，在该同一 $H$ 合同中仍有实际常量标签族 $\mathcal G_K$，其目标数为 $\Theta(H)$，且

$$
 d_{\min}(\mathcal G_K;H)
 =\frac{\log H}{2\log\varphi}+O(1).
 \tag{TM.4623}
$$

这里 $O(1)$ 常数统一于所述 $K,H$。若 $D_{\mathrm{ord}}(H)$ 表示定义 46.1 中可恢复常量标签类的最优深度的上确界，则

$$
 \frac{\log H}{2\log\varphi}-O(1)
 \le D_{\mathrm{ord}}(H)\le J_H
 =\frac{\log H}{\log\varphi}+O(1),
 \qquad D_{\mathrm{ord}}(H)=\Theta(\log H).
 \tag{TM.4624}
$$

（TM.4624）没有确定全类的最优主系数；（TM.4622）—（TM.4623）的主系数只对所显示实际族精确。

证明。令 $\psi=(1-\sqrt5)/2=-\varphi^{-1}$。序列 $(\varphi^n-\psi^n)/\sqrt5$ 满足相同递推和初值，所以 $F_n=(\varphi^n-\psi^n)/\sqrt5$。于是 $R=\varphi^{K+5}(1+o(1))/\sqrt5$，$F_{K+6}/R\to\varphi$。由（TM.4612）得到 $H_K/R^2\to12\varphi$ 及 $\log H_K=2K\log\varphi+O(1)$。定理 46.6 的两端相差二，给（TM.4622）。

$H_K$ 严格递增且趋于无穷，$H_{K+1}/H_K\to\varphi^2$；其全部相邻比率有统一有限上界。所选最大 $K$ 满足 $H_K\le H<H_{K+1}$，故 $H/H_K$ 在统一有界区间内，$\log H-\log H_K=O(1)$ 且 $R^2=\Theta(H)$。定理 46.6 已证明扩大上限后同一族的夹界仍成立，给（TM.4623）。最后推论 35.5 的 $J_H$ 对每条合法路径都成立，其 Fibonacci 定义和上述公式给上端；所选实际族给下端。非空可恢复单行类保证该上确界有意义，有限整数界保证它有限。$\square$

这量化了某个可取得目标所需的接受深度，不把它等同于所有物理时间或总来源调用。窗口仍只有单位历史；增长发生在资源投影与真实取得记录。定理 44.5 的稀疏任意精确深度族仍成立，此处补的是目标数线性于上限的密集族及必要深度的对数率，不作另一次无界性发现。

### 46.8 不能舍弃的资源行关联

**命题 46.8（弱摘要相同而深度答案不同）。** 单凭上限、目标数、常量标签、共同完整窗口、初始标签及（TM.4602）两个条件的真值，不能决定深度至多 $K$ 的可取得性。

证明。固定 $K\ge0$、$R=F_{K+5}$，令 $N=R^2$、共同上限 $\bar H=48N$。定理 46.6 的网格族在此上限仍有 $N$ 个不同标签 $2$ 目标、单位窗口、同一常量标签、两项序条件均真，并仍需超过 $K$ 次接受替换。其协议合法，因为 $F_{K+6}<2R$ 给 $H_K<24R^2<\bar H$。

在同一上限使用已有实际单位词组成的条带族

$$
 \mathcal S_N=\{\omega_{2N+i,\,2N}:0\le i<N\}.
$$

它也有 $N$ 个不同初始目标、单位窗口、同一常量标签、初始标签全为 $2$。其资源为 $m_i=16N+4i$、$n_i=24N+4i$、$\lambda_{2,i}=40N+8i\le48N-8$。两序条件严格成立，因为 $\min n=24N>20N-4=\max m$、$\min\lambda_2=40N>28N-4=\max n$。但所有 $m_i$ 不同：未经替换即用真实尺寸取得恢复 $m$，再用 $i=(m-16N)/4$ 解码本人原始目标，接受替换深度为零。两族所列弱摘要相同而有不同深度答案。定义 46.3 保留源—资源行—原始目标关联，恰没有作这个不充分删减。$\square$

### 46.9 分离计费、供应归属与未决范围

定义 46.3 的计划有 $O(k)$ 个阶段记录，全部退出字典共至多 $N$ 个目标关联，另有公共实际表与共同窗口。阶段整数需 $O(\log(H+1))$ 位；按既有紧凑整数／窗口接口，阶段计划为 $O(k\log(H+1))$ 位。在线只需阶段号、已知贡献和终端取得计数，终端字典、程序描述、静态表、全部记录与输出另计。此界没有删除原始目标关联，没有对任意既定控制器宣称总记忆上界，也不证明最小描述、最小状态或最优证书搜索复杂度。

定理 46.4 的单叶填充执行器每个非终端阶段至多一次前缀宏、一次共同宏、一次替换尝试，最后仅一个支路填充；来源调用保守上界为 $3k+H$，没有初读。终端填充也可直接换为（TM.4620）的已有二分宏：取得终端入口尺寸 $M$ 后，F 支路计算 $m_j=M-(H-p_j)$，R 拒绝支路计算 $m_j=M-d_j$，末阶段计算 $m_k=M$。这些支路的行单射已由证书验证，替换该终端算法不引入新碰撞。于是同一深度的来源调用上界可取 $3k+\lceil\log_2H\rceil+1$；若另作初读，加一。宏中途不读出任何尺寸，最后拒绝始终计费。这只是显示算法的界，不是最少调用定理。

在定理 46.6 中，标签字母表恰为一，生产者返回常量，不访问来源；类别成员认证、实际正词生产和原始目标输出是独立费用。每个初始词恰含 $4(r+s)$ 片叶，介于 $16R$ 与 $24R-8$；这不是零材料来源。显示协议替换恰 $K+3$ 次，二分取得没有额外替换。终端纯 $\alpha$ 上下文的实际接受总叶数恰为 $U=H-N_{\mathrm{term}}\le H-1$，每次尝试宏至多 $H$ 叶，尝试总叶长保守地至多 $H\lceil\log_2H\rceil+1$，包括被拒宏和最后单叶。原子一次调用不等于一次单叶生产或单位物理时间；替换展开、上下文生成／传输和守卫实现仍各自计费。

若终端改用单叶填充，实际成功数 $f=H-N_{\mathrm{term}}$，无初读的来源调用恰为 $K+3+f+1$；在 $H=H_K$ 时 $0\le f\le4(R-1)F_{K+6}$。这是同一深度但不同调用与材料安排，不能混报为二分调用界。二分记录仅须保留实际累计 $U$ 与公共常量即可用（TM.4621）解码；在给定公共 Fibonacci 数及逆 $u_a$、学校式整数算术下，常数个 $O(\log(H+1))$ 位整数寄存器足够，区间控制与解码位运算保守上界为 $O((\log(H+1))^2)$。生成公共 Fibonacci 常数、求逆、认证来源与解码器、字面记录存储及输出分别另计；这是足够工作空间与算术界，不是物理总记忆最优。只存生成公式可节省字面族表，但须承担其计算与认证费用。

数学供应归属：实际正词、共同三窗及八边 Euler 认证归[原子卷 §§359–360](FIBONACCI_ATOMIC_RELATION_GENERATION.md)；来源动作与永久碰撞归引理 30.1、定理 30.2、命题 38.1；整个无替换阶段压缩、准确双增量与非交换因子运输归引理 35.1—35.2、定理 35.4；仿射次序贡献归命题 39.8；无统一常数的必要深度与原子二分终端取得归定理 44.5；任意实际历史的完整过滤与源—目标后继归定理 45.3、命题 45.4。这里的新增综合结论为资源序条件下的分支消去、深度保持的单线充要证书、投影释放计数和实际密集族的定量对数率，不将已有单位词、静态恢复或无界深度列作新供应。

仓内 [TargetRecoveryCriterion](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean) 的 `target_recovery_criterion` 和 [IndexedTargetSufficiency](../../../D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency.lean) 的 `indexed_target_sufficiency` 供应既有的目标在实际读出纤维上恒定与因子分解接口；它们不供应此处的取得前缀。[SafeActionRefinementMonotonicity](../../../D5/S3/ConceptDynamics/Decision/SafeActionRefinementMonotonicity.lean) 的 `safe_action_refinement_monotonicity` 是纤维上动作合法性的包含，不保证合法动作保护初始目标。[ReachableBehaviorMinimality](../../../D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality.lean) 的 `finite_state_minimality` 有给定单子作用、可达性和同外部未来行为前提，不将初态区别自动交给受守卫协议。另有 [BinaryProtocolDepthLowerBound](../../../D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound.lean) 的 `adaptive_binary_protocol_depth_lower_bound` 和 [FiberBinaryIdentification](../../../D5/S3/ConceptDynamics/Coding/FiberBinaryIdentification.lean) 的 `arbitrary_binary_questions_identify_target`：它们计二进制问题深度并容许给定或任意二值问题，不等于这里只计接受 $\rho$、且尺寸探测会改源的动作合同。上述源码接口不构成当前编译证据，不代替本章的普通源特定证明。

初态识别、区分与最终状态定位的成熟背景仍取 §31 已列 Panteleev，*Preset Distinguishing Sequences and Diameter of Transformation Semigroups*，arXiv:1412.0034v1，及 van den Bos–Vaandrager，*State Identification for Labeled Transition Systems with Inputs and Outputs*，arXiv:1907.11034v2。没有移用其长度界、自动机模型或搜索接口来证明本章的正资源结论。全部新增论证是既有供应上的 repo-derived 普通数学综合，不主张全库无重叠、文献优先权或 Lean 核验。

若共同完整窗口或（TM.4602）缺失，读可以分叉，混合上下文接受也未必终端化；定理 46.4 与推论 46.5 不分类那些族。证书的有限枚举不解决一般混合窗口／资源族的紧凑全局策略或高效搜索。显示网格族的最优深度仍在（TM.4614）两步区间内，全有序类的最优主系数只受（TM.4624）夹界；全族 $M_A(H)$、节省缺口、最少调用、标签与表的取得认证最优、总记忆和完整长期关系恢复目标均未由本章完成。输出始终为初始 $q_H$，不恢复原括号、叶路径、原树过去、物理空间或物理时间；重算一个规范来源也不等于找回本人原树。

## 追加锚（本行以下为增补区）
## 47. 任意有限实际族的全动作取得图、精确深度与合法执行

本章固定 §30 的实际非空有序 $\alpha/\beta$ 原树、同一个活叶上限 $H$、真实当前 $E$ 读以及整候选守卫。目标仍为同一初始来源的 $q_H$，原供应标签不变。给定完整、经过来源认证的有限初始目标表和精确可计算的读数坐标接口，可以有限决定任意混合窗口、任意资源排列的取得可行性，计算最少最坏接受 $\rho$ 深度，并输出只依赖真实记录的实际执行器。其输入完整性、坐标转换、静态计划、解码、上下文材料和物理操作均须付费。

这里复用定理 35.4 的取得存在性、定理 45.3 的精确历史过滤、§30 的行为核与一般有限稳健规划。新增的源特定桥梁是：直接枚举覆盖所有正上下文的有限组成动作；证明每个有用响应都有资源或候选数进展；将历史过滤接到可计算的全局搜索和实际策略；给出数值上限相关的状态、搜索、控制和材料上界。共同完整窗口与（TM.4602）的两道资源序条件均不是本章前提。以下是普通数学论证及有限精确检验，不是 Lean 内核核验。

### 47.1 完整初始表、同一来源和可读取接口

**定义 47.1（带原始目标的认证输入）。** 固定公开整数 $H\ge1$、非空有限实际族 $\mathcal F\subseteq\mathcal T_H$、原同源供应函数 $h$ 和一个非空供应纤维 $\mathcal F_\ell=\{t\in\mathcal F:h(t)=\ell\}$。要求供应一张有限表

$$
\mathscr C=\{(t_i,c_i,\Omega_i,\tau_i):1\le i\le N\},
\qquad c_i=(a_i,b_i),\quad
\Omega_i=W_3(t_i),\quad \tau_i=q_H(t_i),
\tag{TM.4701}
$$

其中 $t_i\in\mathcal F_\ell$，$1\le a_i+b_i\le H$，$\tau_i$ 两两不同，并且有完整覆盖条件

$$
\forall t\in\mathcal F_\ell\quad
\exists!i\in\{1,\ldots,N\}\quad q_H(t)=\tau_i.
\tag{TM.4702}
$$

每行的组成、完整数学窗口和目标属于同一个实际实现。实现可以是显式非空正词及有序括号，也可以是原子卷定理 360.2 的整数性、八边非负和有效支撑弱连通证书，附该行属于声明纤维的依据。后者认证实际共同来源；仅有三项分别可实现、流量平衡或者可行资源数值均不足够。认证表的每一行实际可实现，并不证明（TM.4702）；覆盖、纤维成员判定和表的取得是另一个供应义务。若原输入是完整来源枚举，则按初始 $q_H$ 去重并选择原枚举中的实际代表，得到此表。

精确坐标使用 §28 的唯一正规形

$$
N(\epsilon,k,p)=(-1)^\epsilon S^kA^p,
\qquad \epsilon,p\in\{0,1\},\quad k\in\mathbb Z.
\tag{TM.4703}
$$

表内完整窗口、已知上下文及实际当前读都要求有可计算的精确正规坐标表示或转换接口，群乘法、相等判断、求逆和 $J$ 在该表示上可计算。这个接口是对已经返回的真实读数进行计算；它不是额外读取隐藏组成、初始窗口或深窗的端口。若原 $E$ 端口返回展开 Clifford 系数，其解析、转换及结果写出费用另计。一个语义上定义的有限族或没有枚举取得界的成员 oracle，不自动满足本定义的有效输入条件。

在线控制器只收到公共 $H,\mathscr C,\ell$ 和真实已取得记录，不能查询实际未知的行号 $i$。静态表限定未知来源可能是什么，不直接告知哪行实际发生。目标字典的内容是初始 $\tau_i$；修改后的当前 $q_H$ 不替换它。

**引理 47.2（初始去重与历史配对）。** 在（TM.4702）下，一个在全部 $t_i$ 上正确的确定性协议在全部 $\mathcal F_\ell$ 上正确。对应来源与其代表的每个真实响应、停止输出和接受 $\rho$ 次数都相同。一个已达到共同历史内，不同 $\tau_i$ 的行不得按相同当前行为删为一行。

证明。定理 30.2 使相等初始 $q_H$ 的两个实际来源在同一公共初始化和同一程序下产生相同全部记录；其一步闭合性使所有后继继续保持这种对应。对记录长度归纳，控制器选择同一个下一动作，接受 $\rho$ 的位也相同。若代表停止，原来源沿相同记录停止并需要相同初始目标，故其输出正确。完整覆盖将此论证应用于每个允许初始来源。后半句是命题 38.1 的原始目标配对：相同当前行为只保证相同未来记录，不能使两个不同的初始输出同时正确。$\square$

令 $F_0=0,F_1=F_2=1$、$F_{k+2}=F_{k+1}+F_k$，并定义

$$
\lambda_k(i)=F_{k+1}a_i+F_{k+2}b_i,
\qquad J_H=\max\{j\ge0:F_{j+1}\le H\}.
\tag{TM.4704}
$$

下文记 $J=J_H$，所以 $J_1=1$。单叶 $\alpha$ 的第一次 $\rho$ 接受并保持一叶；第二次候选有两叶而拒绝。完整接受次数 $j$ 不能仅按三或六取模。

### 47.2 覆盖任意左右正上下文的有限动作

**定义 47.3（规划键与实际外因子）。** 对一个已达到的共同历史，保留规划键

$$
K=(j,U,V,C),\qquad \varnothing\ne C\subseteq\{1,\ldots,N\},
\tag{TM.4705}
$$

其中 $C$ 恰为产生该历史的初始目标索引集，$j$ 为完整接受 $\rho$ 次数，$(U,V)$ 为已经接受并运输至当前的已知材料贡献。实际执行还保留有序已知单位三元组 $P,Q$，满足每个 $i\in C$ 的同一实际当前来源 $s_i$ 有

$$
\begin{aligned}
m_i&=\lambda_0(s_i)=\lambda_j(i)+U,\\
n_i&=\lambda_1(s_i)=\lambda_{j+1}(i)+V,\\
W_3(s_i)&=P\odot F^j(\Omega_i)\odot Q.
\end{aligned}
\tag{TM.4706}
$$

初始键为 $K_0=(0,0,0,\{1,\ldots,N\})$，且 $P=Q=(1,1,1)$。三重单位仅表示没有外材料，不是可调用的空来源。一般已达到历史的 $C,j,U,V,P,Q$ 由真实记录和定理 45.3 求出；没有重新访问初始原树。

定义有限规范动作集

$$
\mathcal A_H=\{\operatorname{Read},\rho\}
\cup\{A(d,e):1\le d\le H-1,\ d\le e\le2d\}.
\tag{TM.4707}
$$

$A(d,e)$ 是一次原子右拼接，使用固定左结合括号的实际正词

$$
v_{d,e}=\alpha^{2d-e}\beta^{e-d}.
\tag{TM.4708}
$$

两个子块之一可以为零并被省略；总叶数 $d>0$，所以整个词非空。其组成为 $(2d-e,e-d)$，当前和下一窗口资源增量恰为 $(d,e)$。零对只表示省略动作，不列入上下文动作集。动作数为

$$
A_H=|\mathcal A_H|=2+\frac{(H-1)(H+2)}2;
\qquad A_1=2.
\tag{TM.4709}
$$

$E_j(i)$ 表示 $F^j(\Omega_i)$ 的首项。规范读是先发出真实当前 Read，取得 $x$，再计算

$$
y=P_0^{-1}xQ_0^{-1}=E_j(i).
\tag{TM.4710}
$$

它不是预先查询表中实际未知行的窗口。把各响应对应的非空索引子集记为 $C_y,C_+,C_-$，规划转移为

$$
\begin{array}{c|c|c}
\text{动作和响应}&\text{索引子集}&\text{后继键}\\ \hline
\operatorname{Read}:y&C_y=\{i\in C:E_j(i)=y\}&(j,U,V,C_y)\\
A(d,e):\mathrm{accept}&C_+=\{i\in C:m_i+d\le H\}&(j,U+d,V+e,C_+)\\
A(d,e):\mathrm{reject}&C_-=C\setminus C_+&(j,U,V,C_-)\\
\rho:\mathrm{accept}&C_+=\{i\in C:n_i\le H\}&(j+1,V,U+V,C_+)\\
\rho:\mathrm{reject}&C_-=C\setminus C_+&(j,U,V,C_-).
\end{array}
\tag{TM.4711}
$$

空子集不是实际响应分支。只有接受 $\rho$ 的边有深度权重一，其余边权重零。接受右宏更新 $Q\leftarrow Q\odot W_3(v_{d,e})$；接受 $\rho$ 更新 $(P,Q)\leftarrow(F(P),F(Q))$；拒绝及 Read 不改变实际来源或外因子。守卫中的等号全部接受。拒绝没有候选的 $E$，也不加入材料。

**定理 47.4（全上下文对应与物理读的提升）。** 对固定认证输入和任意已达到共同历史，（TM.4711）精确给出所有规范动作的响应划分和实际后继。全部允许的实际正左／右上下文可用（TM.4708）替代，保持取得可行性、每个初始目标以及每行接受 $\rho$ 次数。反向，每个规范动作策略都有合法的原合同实现。此对应保持规范化记录；任意原控制器的字面记录需以已知有序因子构造虚拟记录，不与替代后的物理记录混同。

证明。引理 30.1 的单出现不变量和引理 35.1 给出（TM.4706）；其资源闭合更新直接得到（TM.4711）。相对于一个共同历史，$P_0,Q_0$ 是同一对已知可逆因子，故（TM.4710）对全部行作同一个双射读数重标记。由真实读选中的纤维恰为 $C_y$，而不是从两个不同来源选取的边缘窗口的组合。拒绝保持原源，接受得到其真实正拼接或替换，故每个后继都在原子来源域内。

任意命名实际正上下文 $v$ 有 $d=\lambda_0(v)\ge1$、$e=\lambda_1(v)$ 和 $d\le e\le2d$。词 $v_{d,e}$ 与 $v$ 有完全相同的组成。无论原上下文置于哪一侧，把它事先替换为一次右拼接此词，在每个存活行上都有同样的当前组成；继续替换时，全部未来 Fibonacci 资源贡献也相同。因此该步和以后逐次模拟的所有守卫相同，接受／拒绝与接受 $\rho$ 计数逐行相同。

还须处理非交换读和依赖读的下一动作。令原虚拟模板的已知外因子为 $L,R$，替代模板的物理外因子为 $P,Q$。已经真实取得的物理当前读 $x=P_0E_j(i)Q_0$ 转为

$$
x_{\mathrm{virtual}}=L_0P_0^{-1}xQ_0^{-1}R_0.
\tag{TM.4712}
$$

所有求逆只在已知单位算术中进行，次序如式中所示。原左接受置 $L\leftarrow W_3(v)\odot L$，原右接受置 $R\leftarrow R\odot W_3(v)$；物理接受始终置 $Q\leftarrow Q\odot W_3(v_{d,e})$。接受 $\rho$ 将四因子都施以 $F$；拒绝将它们全部保持。把原动作身份、实际相同的守卫位和（TM.4712）的读写入虚拟记录，送给原程序，原程序便选择其本来选择的下一动作或停止输出。物理记录另存实际动作、守卫和真实读。对原路径长度归纳即得到模拟，任意交替左右位置、非交换因子、重复拒绝和六个窗口相位都包括在内。没有未知来源的逆动作、拆接、重置或复制，也没有被拒候选的读。

若 $d\ge H$，所有非空当前来源都有 $m_i+d>H$，故该上下文必拒绝、源不变且无候选读。原控制器所需的这个已确定事件可在内部加入其虚拟记录而不发出来源调用。因此未列入（TM.4707）的正上下文不提供取得能力或降低接受 $\rho$ 深度。其余每个整数对都有（TM.4708）的实际代表，计数由 $\sum_{d=1}^{H-1}(d+1)$ 得到（TM.4709）。反向只需执行这些允许的真实宏、Read 和 $\rho$，用（TM.4710）计算规范读并按实际响应选支；归纳给出相同后继和初始输出。$\square$

一个原子宏被拒绝时必须整个保持来源。把它改为逐叶拼接，部分叶可能已经被接受，不是上述对应。上下文身份和实际原始读值也不因组成相同而字面相同。规划键 $K$ 单独不能重建原始读值；还需知道有序 $P,Q$。它没有恢复完整旧记录、任意旧控制器的程序状态或物理费用。

**命题 47.5（源—目标兼容的必要条件）。** 在一个共同实际历史内，以（TM.4706）和（TM.3003）求每行当前 $q_H(s_i)$。若存在 $i\ne i'$ 有相同当前 $q_H(s_i)=q_H(s_{i'})$，则不可能恢复全部存活初始目标。

证明。表中 $\tau_i\ne\tau_{i'}$。定理 30.2 使这两个实际当前来源在相同已取得记录和同一延续程序下产生相同全部未来记录；目标必须分别为两个不同的初始 $\tau$。二者不能在相同停止记录上均被正确输出。$\square$

这是一项可提前判负的永久合并检验；没有合并只是必要条件，并不保证存在一个对所有未来响应均成功的下一动作。全局可行性由下面的整个取得图决定。因子消去后的 $(m_i,n_i,E_j(i),\ldots)$ 只是一种计算当前配对行为的比较编码，不能把它冒认为实际取消了已知材料后的树。

### 47.3 每条有用边的有限进展

**引理 47.6（资源锥、深度上限与严格进展）。** 每个非空已达到键满足

$$
0\le j\le J,\qquad 0\le U\le V\le2U,
\qquad U\le H-1.
\tag{TM.4713}
$$

从（TM.4711）删掉“只有一个非空响应、其后继正是原键”的动作。在剩余图上，每条响应边均严格降低非负整数

$$
\mu(K)=(J-j)+(H-1-U)+(|C|-1).
\tag{TM.4714}
$$

证明。初始材料对为零；接受上下文加上 $(d,e)$，该向量位于 $0\le d\le e\le2d$ 的锥中。接受 $\rho$ 将 $(U,V)$ 变为 $(V,U+V)$；若 $U\le V\le2U$，则 $V\le U+V\le2V$，故锥在两种接受更新下封闭。拒绝和读不改此锥。非空存活行有 $1\le\lambda_j(i)$ 和 $\lambda_j(i)+U\le H$，所以 $U\le H-1$。其未知单出现含至少 $F_{j+1}$ 叶；由推论 35.5 得 $j\le J$，包括 $H=1$ 的等尺寸首次替换。

候选索引只会减少。一次接受上下文令 $U$ 增加至少一；一次接受 $\rho$ 令 $j$ 增加一，且新 $U=V\ge U$，因此二者均严格降低（TM.4714），即使接受 $\rho$ 不增加实际当前叶数亦如此。若一个读有至少两个非空值纤维，每个纤维都是 $C$ 的真子集，故也严格降低 $\mu$；单值读则恰为所删动作。修改动作的拒绝边不改 $j,U,V$；若其接受部分非空，拒绝子集为真子集，否则整个动作恰为所删的唯一拒绝自转移。因而所有剩余边严格进展。$\square$

**推论 47.7（策略不必保留已确定的自转移调用）。** 对取得存在性和接受 $\rho$ 深度优化，可以删去上述动作，不丢失成功协议。剩余图无环；从初始键出发的任何路径至多含

$$
L_H(N)=H+J+N-2
\tag{TM.4715}
$$

次来源调用。一般已达到键的对应界为 $\mu(K)$。

证明。全拒绝修改的源确实不变，控制器可计算其共同已确定的 reject 并在内部推进。单值规范读的值可从固定表和键求出；结合已知外因子，可为需延续的原程序计算该步原始读，而不发出真实来源调用。二者都是模拟已确定的事件，不是假装取得一个尚有多个可能值的读。不作这种删减也不新增来源区别或接受 $\rho$。若原程序逐点有限停止，有限表上各代表的有限执行路径之并为有限树，内部跳过的已确定事件不会构成无穷模拟。定理 47.4 先把任意正上下文协议送到有限动作界面，再逐支删去这些调用，得到深度不增加的规范协议。每个实际来源调用严格降低初始值 $\mu(K_0)=L_H(N)$，所以有路径界。$\square$

此处的进展来自完整接受计数、真实材料和候选目标数，不能只用当前叶数：全 $\alpha$ 的一次 $\rho$ 可以保持叶数不变。来源调用分别计每次 Read、每次 $\rho$ 尝试和每次整宏尝试，包括拒绝；调用次数不是物理时间。

### 47.4 精确可行性、最优接受深度与实际策略

**定理 47.8（任意有限认证实际族的完整取得算法）。** 对定义 47.1 的每个输入及任意已达到键 $K$，枚举（TM.4707）、按（TM.4711）生成全部非空响应后继，删去推论 47.7 的动作，并在 $|C|=1$ 时停止展开。这是有限无环的目标配对图。按 $\mu$ 递增次序定义

$$
D(K)=
\begin{cases}
0,&|C|=1,\\[1mm]
\displaystyle\min_{a\in\mathcal A_H^{\mathrm{use}}(K)}
\ \max_{o:\,C_{a,o}\ne\varnothing}
\bigl(w(a,o)+D(K_{a,o})\bigr),&|C|>1,
\end{cases}
\tag{TM.4716}
$$

其中 $w(a,o)=1$ 当且仅当 $a=\rho$ 且 $o=\mathrm{accept}$，否则为零；含无穷子值的最大值为无穷，空动作集的最小值为无穷。那么以下条件等价：

1. 有确定性原合同延续，在每个兼容初始来源上有限停止并正确输出其初始 $q_H$。
2. $D(K)<\infty$。

当有限时，$D(K)$ 恰为所有这些原合同延续中最少的最坏未来接受 $\rho$ 次数；保存每个节点一个取得最小值的动作及其真实响应后继，即得到达到此深度的合法策略。初始完整运行的调用次数至多（TM.4715），接受深度至多 $J$。没有共同窗口、资源排序、隐藏最优动作或可行性 oracle 前提。

证明。动作数有限，且（TM.4713）给有限的 $j,U,V,C$ 取值；引理 47.6 使每个非平凡子节点有更小 $\mu$，因此即使很多边权为零，（TM.4716）也已良基，没有零代价循环问题。若 $|C|=1$，所有兼容来源要求同一个表内初始目标，立即按字典输出即可，未来接受深度零且已经最小。反之，$|C|>1$ 时不同索引要求不同初始目标，尚不能正确统一停止。

对 $\mu$ 归纳证明充分性与达到值。有限非终端值必有一个达到最小值的动作，且其每个非空真实响应子节点都有有限值。实际发出该动作，若是读则仅对真实返回的 $x$ 使用（TM.4710），否则直接以真实 accept/reject 选支。定理 47.4 保证选中（TM.4711）的恰当子节点及实际来源。对子节点使用归纳得到的策略，便全部正确停止。当前动作的接受权重加上最坏子深度，正是（TM.4716）所选值。每个非空分支有实际代表来源实现；有限子树上的最大路径及该路径的目标索引也有共同实际实现，故这不是把不同边缘最坏值拼成一条虚构历史。严格进展给出有限调用界。

再证必要性和最优性。给定任意逐点有限成功延续，有限初始代表表使其实际有限执行路径之并成为有限树。定理 47.4 将所有上下文规范化，保持每行初始目标及接受 $\rho$ 计数；推论 47.7 删除已确定自转移。若其根已经终端，值零不大于该延续的非负深度。否则其首个有用动作必须在每个非空响应子节点都有成功子延续。对子节点按更小 $\mu$ 归纳，$D(K_{a,o})$ 不大于该子延续的最坏未来深度。加上该边真实接受权重、取响应最大值，再取动作最小值，说明 $D(K)$ 不大于原延续的最坏未来深度，且有限。充分性已经给一个达到 $D(K)$ 的原合同策略，故其值正是全动作最优接受深度。引理 47.2 将代表上的正确性及计数扩展到整个声明纤维。$\square$

可以按以下有限程序实现，不把规划器作为另一个未供应的判据：先由固定表预计算（TM.4704）和六个 $E_j$ 相位，从入口键生成可达节点；每个节点扫描实际表计算（TM.4711）；把新键存入有限字典；依 $\mu$ 排序进行（TM.4716）；保存达到有限最小值的动作、可能响应和子地址；终端地址关联初始目标字典。判负可使用命题 47.5 提前结束，亦可不使用它而完成相同的递推。

执行器从已取得入口初始化 $K,P,Q$，查表选择一个动作，发出一次真实调用，按实际响应更新键地址和已知因子，到终端地址输出原始 $\tau$。初始入口和全部规范宏都是右侧时，始终 $P=(1,1,1)$，只需保留 $Q$；任意已经达到的左右混合入口则继续保留两个因子。查表不读取未知行号，表内行的资源只用于计算可能分支，实际分支由来源回答选择。深度零的赢节点仍可能需要读或上下文；$D=0$ 不等于已经可以停止。

这个递推是成熟的有限稳健规划：选择动作的存在量词和全部实际响应的全称量词不能交换。定理 35.4 已供应同一取得存在性；这里没有把它重命名为新存在性发现，而是用源特定有限动作、进展和计数，把其语义目标接成一个可执行、有费用上界的算法。

### 47.5 可达状态数和数值上限搜索界

**命题 47.9（历史过滤给出的候选集计数）。** 对固定输入，令 $R$ 为上述可达图的键数，包括判负键和终端键。则

$$
R\le (J+1)\frac{H(H+1)}2
\min\left\{2^N,
 (H+1)^{J+2}(N+1)^3\right\}.
\tag{TM.4717}
$$

记 $B_H=\lceil\log_2(H+1)\rceil$。由 $N\le|Q_H|=O(H^5)$ 和 $J=O(B_H)$，得到

$$
R=2^{O(B_H^2)}=H^{O(\log(H+1))}.
\tag{TM.4718}
$$

证明。深度 $j$ 有 $J+1$ 种，材料锥中 $U=0,\ldots,H-1$ 时 $V$ 有 $U+1$ 种，所以 $(U,V)$ 总数为 $H(H+1)/2$。固定 $(j,U,V)$，任意候选集首先至多有 $2^N$ 种。

另用定理 45.3：此固定资源键下，完整已达到历史的候选集恰由最终上界 $\lambda_j(i)\le H-U$、至多 $j+2$ 道严格下界 $\lambda_k(i)>r_k$ 和至多三个已经实际取得的初始窗口等式决定。所有 $r_k$ 可在 $\{0,\ldots,H\}$ 中取值；负下界与零等价，因为 $\lambda_k(i)\ge1$。每个初始窗口的等式寄存器是未设置，或等于该表相应列的至多 $N$ 种值之一。对于读 $j=3q+r$，其等式来源是 $J^q(P_0^{-1}xQ_0^{-1})=E_r(i)$，因此两个已知因子不进入该等式列的取值计数。过去全部接受条件已经由最终上界推出，不另乘历史长度因子。故固定 $(j,U,V)$ 至多有 $(H+1)^{j+2}(N+1)^3$ 个可达 $C$；这些过滤字段只是计数见证，不要求规划键同时存一个 $N$ 位掩码和另一份过滤字段。以 $j\le J$ 统一并取较小界，得到（TM.4717）。

初始目标去重给 $N\le|Q_H|$；§30.3 的现有容量结论给 $|Q_H|=O(H^5)$，小上限 $H=1,2$ 也满足常数扩张后的上界。由 $F_{k+2}\ge2F_k$ 得 $J=O(\log(H+1))$。把这两个界代入（TM.4717）取对数，得到 $O(B_H^2)$；无匹配下界或最小状态数断言。$\square$

**命题 47.10（带显式表示和字典费用的有限算法界）。** 采用定义 47.1 的紧凑精确坐标，表坐标及紧凑目标部分有 $O(NB_H)$ 位；另加供应标签、成员与覆盖证据、来源证书和原词等输入长度。排除这些输入的产生与验证以及原读转换费用后，一个保守的显式图构造和递推实现有

$$
O\bigl(RH^2N^2B_H^3\bigr)
\tag{TM.4719}
$$

位操作上界，离线存储可用

$$
O\bigl(RH^2N^2B_H^2\bigr)
\tag{TM.4720}
$$

位。这是数值 $H$ 的拟多项式充分上界，不是二进制输入的多项式算法或紧界。

证明。§§28–29 的叶指数界使初始三窗和紧凑目标中每个整数指数为 $O(H+1)$，固定个位的符号和奇偶加上 $O(B_H)$ 位整数即得行坐标界。预计算 $\lambda_k(i)$ 至 $k=J+1$ 足够处理全部规划守卫。因为 $F_{J+1}\le H<F_{J+2}$、$F_{J+2}\le2H$ 和 $F_{J+3}\le3H$，这些预计算投影均不超过 $3H^2$，所以即使某些离线投影已超上限，其整数仍只有 $O(B_H)$ 位。六相位的 $E_j(i)$ 直接由 $F$ 与 $J$ 生成，指数仍为 $O(H+1)$。预计算需 $O(N(J+2)B_H^2)$ 位操作的保守学校算术界。

每个节点至多枚举 $A_H=O(H^2)$ 个动作参数。一次扫描 $N$ 行，用已算投影、精确整数比较和单位坐标，得到响应纤维。读纤维可按 $O(B_H)$ 位单位坐标排序；$\log(N+1)=O(B_H)$，故这一部分在 $O(NB_H^2)$ 内。若直接用 $N$ 位掩码写各子键，至多 $N$ 个读子集的保守写入界为 $O(N^2)$；修改动作至多两个子键。每个字典键有 $O(N+B_H)$ 位；用确定性平衡搜索树，查询或插入至多比较 $O(\log(R+1))=O(B_H^2)$ 次。一次动作的至多 $N$ 个子键因而可以在 $O(N^2B_H^3)$ 位操作内处理；这里实际计算字典和掩码费用，没有把集合索引当免费 oracle。乘节点和动作数，包含排序及回溯递推，就得（TM.4719）。值只有 $0,\ldots,J$ 或无穷，比较与保存动作不超过这个保守界。存每个节点、全部响应边及其子地址、掩码和动作参数，按同样的宽松计数得到（TM.4720）。采用紧凑过滤字段或只保存选定动作可以减掉不必保留的内容，但本命题不要求这种优化。

将 $N=O(H^5)$ 代入，多项式因子乘（TM.4718）仍为 $2^{O(B_H^2)}$。动作枚举本身已经有 $\Theta(H^2)$ 项，在 $H$ 的二进制位数中为指数规模；显式表、原词或来源证书输入若更紧凑，也不能据此宣称算法在它们的总位长中多项式。$\square$

这里的 $2^N$ 是任意初始索引子集的通用描述上界，不是宣称这些子集都可达。（TM.4717）利用实际历史的 Fibonacci 下界和三项读等式，允许不同历史共享节点；当 $N$ 在 $H^5$ 量级上增长时，其上界小于不受限制的子集计数。对稀疏表并无逐实例更小或更快的保证，所以保留两者的最小值。不据此声称比所有优化过的 TM35 实现快，也不把一般信念图或记忆压缩定理计作新结果。

### 47.6 混合窗口的两个非终端读支路

**命题 47.11（$H=12$ 的实际分叉与精确深度二）。** 取一个恒定原标签、固定左结合括号，以及四个实际正词

$$
P=\alpha\alpha\alpha\beta\beta,\quad
Q=\alpha\beta\alpha\alpha\beta,\quad
X=\alpha\alpha\beta\beta\alpha,\quad
Y=\beta\alpha\alpha\beta\alpha.
\tag{TM.4721}
$$

其共同组成为 $(3,2)$，资源为 $(\lambda_0,\lambda_1,\lambda_2)=(5,7,12)$，初始标签都为 $2$，且同一实际行上的窗口为

| 47.11 实际行 | $E_0$ | $E_1$ | $E_2$ | $x=(x_{00},x_{10},x_{01},x_{11})$ | $y=(y_{00},y_{01},y_{10},y_{11})$ |
| --- | --- | --- | --- | --- | --- |
| 47.11P | $-A$ | $-S^{-1}A$ | $S^3$ | $(2,1,0,0)$ | $(0,0,1,1)$ |
| 47.11Q | $-A$ | $-S^{-1}A$ | $S^{-1}$ | $(1,0,1,1)$ | $(0,0,1,1)$ |
| 47.11X | $-A$ | $-S^3A$ | $S^3$ | $(2,1,0,0)$ | $(1,1,0,0)$ |
| 47.11Y | $-A$ | $-S^3A$ | $S^{-1}$ | $(1,0,1,1)$ | $(1,1,0,0)$ |

该族的最少最坏接受 $\rho$ 深度为二。第一次接受 $\rho$ 后的 Read 产生 $\{P,Q\}$ 和 $\{X,Y\}$ 两个非终端支路，两个支路都必须继续接受 $\rho$。因此只保留 TM46 的资源序条件，不能把其“最多一个非终端继续支路”扩展到任意完整窗口。

证明。每个字面词都是非空实际来源。按原子卷四状态边图读取该词，表中八数正是同一条 $00\to10$ 路的边次数；总数为三条 $\alpha$、两条 $\beta$，流量差为起终点之差，所有有效支撑都连到 $00$。零边不强求无用顶点加入支撑。故实际认证同时成立。对同一词用（28.3）逐字乘 $g_\alpha,g_\beta$，或先作字面替换再乘 Clifford 原子，得到所列窗口。正规形唯一性和 $S$ 无限阶使四个初始 $q_H$ 不同。

没有上下文接受时，第一和第二次 $\rho$ 分别在候选大小 $7$ 和 $12=H$ 接受。读第一次后窗口 $E_1$，把四行分成上述两对；每对的 $E_1$ 相同而 $E_2$ 不同。再接受第二次 $\rho$ 并读 $E_2$，由第一读的配对记忆和第二读共同唯一选中初始行，按其初始目标字典输出。因此四次调用 $\rho,\operatorname{Read},\rho,\operatorname{Read}$ 合法，并给深度二。

还须排除所有左右正上下文和适应性迂回。在第一次 $\rho$ 之前，若某个非空正上下文接受，其增量 $(d,e)$ 有 $d+e>0$，当前第二未来资源变为 $12+d+e>12$。于是相同组成及相同前两窗的 $P,Q$ 在同一接受记录后有相同当前 $q_H$，但初始 $E_2$ 不同；$X,Y$ 也如此。该动作立即永久合并一个必须区分的初始目标对，故不能属于成功协议。第一次 $\rho$ 之后、第二次之前，接受上下文使下一替换资源 $12+e>12$；在每个尚存的 $E_1$ 对内，同样进入相同当前大小和当前读的标签 $0$，再次永久合并。左右因子不同不改变这个论证，因为比较的是同一命名动作在一对实际来源上的相同因子。四行组成始终相同，所以拒绝上下文和其他共同拒绝响应均不给行间信息。到第二次接受 $\rho$ 以前，$P,Q$ 的全部可取得读与守卫都相同，任何成功协议在该对上必须接受至少两次 $\rho$。

若第一次之后未读并保留 $E_1$ 就接受第二次，则 $P,X$ 共同到达大小 $12$、读 $S^3$ 的标签 $0$，而 $Q,Y$ 共同到达大小 $12$、读 $S^{-1}$ 的标签 $0$；各对初始 $E_1$ 不同。饱和后所有正上下文拒绝，下一 $\rho$ 候选大小 $19>12$，此合并无法修复。因此成功协议必须在该时间切面取得 $E_1$；其两个读支路各有两个不同初始目标，并非终端。两道 TM46 序条件却都满足，因为 $7\ge5$、$12\ge7$；失效的恰是共同完整窗口前提。$\square$

本例不证明没有一个公共操作序列：上述四调用序列就是公共安排。它证明执行和解码需保留所读支路，且两个响应支路都继续取得，不能将它们压成只有一个继续表、另一支终端的 TM46 结构。

### 47.7 无序资源下的混合宏接受仍可继续

**命题 47.12（$H=80$ 的共同窗口非终端接受支路）。** 使用原子卷推论 360.4 的实际单位正词

$$
\omega_{r,s}=\alpha^{2r-1}\beta^{2s}\alpha
\beta^{2s-1}\alpha^{2r}\beta,
\qquad r,s\ge1,
\tag{TM.4722}
$$

取 $U_*=\omega_{1,2}$、$V_*=\omega_{2,1}$、$Z_*=\omega_{12,1}$，原标签恒定。它们的完整窗口都是 $(1,1,1)$，但初始资源和标签为

| 47.12 实际行 | 组成 | $(\lambda_0,\lambda_1,\lambda_2)$ | 初始标签 |
| --- | --- | --- | --- |
| 47.12U | $(4,8)$ | $(12,20,32)$ | $2$ |
| 47.12V | $(8,4)$ | $(12,16,28)$ | $2$ |
| 47.12Z | $(48,4)$ | $(52,56,108)$ | $1$ |

一次原子右宏 $\alpha^{29}$ 在 $U_*,V_*$ 上接受，在 $Z_*$ 上拒绝。接受支路仍可成功继续接受 $\rho$，不是 TM46 所说的只能按动作前尺寸终端解码的接受支路。

证明。每个单位词的四条 $\alpha$ 边重数都为 $r$，四条 $\beta$ 边重数都为 $s$；全部为正、平衡、支撑连通，终点为 $00$。原子卷供应其组成 $(4r,4s)$ 和同源单位窗口，不把一个环境单位元当空树。三个初始目标不同，且 $\min\lambda_1=16<52=\max\lambda_0$，第一道 TM46 资源序条件不成立。

宏的真实守卫分别为 $12+29=41\le80$、$12+29=41\le80$ 和 $52+29=81>80$。拒绝支路恰为 $Z_*$，可立即输出其初始目标。接受后 $U_*,V_*$ 的当前读共同为 $A$，当前大小共同为 $41$，下一替换大小却为 $49$ 和 $45$；两行都在标签 $1$，初始目标不同且动作前尺寸都为 $12$，所以目标不是这个接受表上的尺寸函数。

在此支路尝试 $\rho$，两行均接受到大小 $49$ 和 $45$，下一候选为 $90$ 和 $86$ 而超限；当前读共同为 $B$，因为 $E(\rho(\alpha^{29}))=B^{29}=B$。随后右接单叶 $\alpha$ 到第一次拒绝，成功次数分别为 $31$ 和 $35$；最终非空候选大小均为 $81$，确实拒绝。以 $49=80-31$ 或 $45=80-35$ 和原始目标字典输出 $U_*$ 或 $V_*$。大小是通过真实调用取得的结果，不是宏前偷偷查询；最后拒绝亦计入调用。因此这个实际混合宏接受支路有合法继续取得，而不是永久终端化。$\square$

本例隔离了资源序的作用：完整窗口仍共同，失去资源序便不能应用引理 46.2 的终端化。定理 47.8 原样允许这样的接受后继续支路；它没有移动首宏端点、把原子宏串行化，或把不同来源的两个资源最优值视为共同可达。

### 47.8 实际执行存储、表输入与材料计费

**命题 47.13（选定策略的充分控制和材料上界）。** 固定（TM.4716）求出的策略及初始目标字典作为只读静态输入。有一个达到定理 47.8 深度的执行器，其可变源向控制字段为 $O(B_H^2)$ 位，包括节点地址和已知有序外因子；初始全右执行可只保留 $Q$。一个初始完整运行至多尝试

$$
(H-1)L_H(N)
\tag{TM.4723}
$$

片上下文叶，全部被接受的原始上下文叶数之和至多 $H-1$。这些界不包括替换扩张材料、物理时间、静态表、全部算术工作空间或完整档案。

证明。节点地址用 $O(\log(R+1))=O(B_H^2)$ 位，计划表已给它所代表的 $j,U,V,C$、下个动作及响应地址，不需要另存一个 $N$ 位候选掩码。一个动作参数用 $O(B_H)$ 位。已接受并运输的已知材料在当前来源中共有 $U\le H-1$ 叶；按未知单出现的左右位置分为两个已知叶词，空侧仅取代数单位。它们的三窗指数由 §28 的叶指数界限制为 $O(H+1)$，因此六个单位因子各用 $O(B_H)$ 位，并可用 $F$ 或有序乘法闭合更新。这说明特定执行器的字段上界；反查读值、对表访问、输出和算术临时空间仍须由实际接口计费。

每个选定宏至多有 $H-1$ 叶，每个尝试计一次真实调用，调用数至多 $L_H(N)$，得到（TM.4723），包括被拒但仍须生产和供应的宏。接受一个宏令 $U$ 增加其叶数 $d$；接受 $\rho$ 令 $U\leftarrow V\ge U$；其他动作不降 $U$。故已接受宏的原始叶数之和不超过最终 $U\le H-1$。运输后的同一材料可能含更多叶，已经计入当前 $U$ 的约束，不能把上述插入量与实际替换加工量混同。$\square$

静态策略只需在每个可达非终端节点保存一个动作、最多 $N$ 个读响应地址或两个守卫响应地址；配合终端目标地址，一个充分描述界为 $O(R(N+1)B_H^2)$ 位，另加原始表、覆盖与来源证据以及输出字典。计算策略的离线图和临时掩码按（TM.4720）计。一个在线重新运行整个搜索器的程序，不能借用只读计划已经供应时的可变字段界。任意原控制器的状态、旧记录和费用计数也不是这个界覆盖的对象。

输入与费用的实际区分如下。

| 47.13 成本对象 | 需要供应或计算的内容 | 上述界的适用边界 |
| --- | --- | --- |
| 47.13表与标签 | 完整初始目标覆盖、纤维成员依据、原供应 $h$、同源行关联 | $O(NB_H)$ 只计紧凑坐标，不生产标签或证明覆盖 |
| 47.13来源证书 | 正词或原子卷八边及连通证书；实际原树构造 | 证书可紧凑，构造的正词和原树仍须输出其叶和括号 |
| 47.13精确读与算术 | 真实 $E$ 的解析和正规坐标转换、相等、乘法、已知求逆、$J$ | （TM.4719）以紧凑接口为前提；不把原端口转换当免费 |
| 47.13计划与解码 | 图计算、静态分支表、目标关联、查表和输出 | 小可变地址不使整个只读计划或离线工作空间变小 |
| 47.13正上下文 | 整宏命名、括号、生成、传输及被拒候选生产 | 每个宏 $d\le H-1$；拒绝不消除生产费用 |
| 47.13守卫与替换 | 整候选叶检查、实际 $\rho$ 扩张、加工和运输 | 接受深度及调用数不指定这些物理操作的时间单位 |
| 47.13档案与展开输出 | 原始完整记录、旧程序状态、展开 Clifford 系数 | 若要这些对象，必须另存；紧凑指数不等于展开输出长度 |

八边证书含固定个数的 $O(B_H)$ 位整数时，其算术与四顶点支撑核查可用有限紧凑计算；仍要证明证书对应的目标、组成及纤维身份。读显式来源词要支付其实际长度。宏的窗口可由

$$
W_3(v_{d,e})=
\bigl(A^{2d-e}B^{e-d},\ B^{2d-e}S^{e-d},\
S^{2d-e}(S^2A)^{e-d}\bigr)
\tag{TM.4724}
$$

在紧凑群坐标中计算；规划只枚举参数，不必先生产全部词。若真的生产整个规范动作词表，其叶数总和 $\sum_{d=1}^{H-1}d(d+1)=\Theta(H^3)$，不能把这张表作为单位成本的物理字母表。

对 $|k|=\Theta(H)$ 的 $S^k$，展开系数由 Fibonacci 整数组成，可以有 $\Theta(H)$ 位；$O(B_H)$ 位指数是一个精确紧凑描述，不是这些系数的免费写出。相同组成上下文替代和读规范化只保持取得与接受深度；它们可以改变原始读值、上下文材料、记录、算术及耗时。没有最少总记忆、最少调用、最少物理成本或最短物理时间结论。

### 47.9 有限精确区分与原始目标检验

**命题 47.14（两种有限表示的区分结果）。** 在下列明确有限输入上，完整字面动作模型和（TM.4711）的规范模型给出相同的可行性与最优最坏接受 $\rho$ 深度；每个规范可达键都有一个实际字面实现，使所有动作响应、后继目标索引和最优继续深度相同。

字面模型独立采用精确有理矩阵

$$
A_{\mathrm L}=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
B_{\mathrm L}=\begin{pmatrix}1/2&1\\-5/4&-1/2\end{pmatrix},
\qquad S_{\mathrm L}=B_{\mathrm L}A_{\mathrm L}.
\tag{TM.4725}
$$

直接逐字求乘积，以 $\alpha\mapsto\beta$、$\beta\mapsto\beta\alpha$ 展开替换，用实际词长决定守卫。状态保留每个初始目标索引和它本人当前字面词。每个上限的字面动作表枚举长度 $1,\ldots,H-1$ 的全部非空二字母词，分别放在两侧，另加 Read 和 $\rho$；未列出的长度至少 $H$ 上下文全拒绝。规范模型另用（28.3）的整数单位坐标、三窗运输和双资源键。两模型分别求整个非平凡响应图的深度值，并核对规范每个可达键的实际实现和全部子分支，未用浮点近似。

| 47.14 有限输入 | 初始正词数 | 不同初始目标 $N$ | 规范键数 | 字面配对状态数 | 两模型的最优接受深度 |
| --- | --- | --- | --- | --- | --- |
| 47.14全词H1 | $2$ | $2$ | $4$ | $4$ | $0$ |
| 47.14全词H2 | $6$ | $6$ | $23$ | $24$ | $0$ |
| 47.14全词H3 | $14$ | $12$ | $74$ | $98$ | $0$ |
| 47.14全词H4 | $30$ | $21$ | $179$ | $334$ | $1$ |
| 47.14全词H5 | $62$ | $33$ | $382$ | $1005$ | $1$ |
| 47.14混合H5 | $4$ | $2$ | $8$ | $15$ | $0$ |
| 47.14混合H7 | $4$ | $4$ | $42$ | $211$ | $2$ |
| 47.14障碍H9 | $3$ | $3$ | $19$ | $133$ | $\infty$ |
| 47.14配对H9 | $2$ | $2$ | $17$ | $61$ | $0$ |

全词输入枚举不超过该上限的全部非空叶词，按初始目标选择代表。所有有序括号化在本合同的词乘积、逐叶替换词和叶数上具有相同响应，对动作次数归纳得同一行为，因此这个有限检验不遗漏因括号改变的可见动作；它没有恢复本人原括号。混合 $H=5,7$ 的四词为 $\alpha\alpha\beta,\beta\alpha\alpha,\beta\alpha^4,\beta^5$。在 $H=5$ 它们只有两个不同初始目标，去重保留两个代表；不能把四个词身份误当四个初始 $q_H$。$H=7$ 则有四个不同初始目标，真实协议先尝试 $\rho$，拒绝识别 $\beta^5$；接受后 Read 区分 $\beta\alpha^4$，余下两词需再接受到 $7=H$ 并读第三窗。这一对前两窗相同，故全动作下至少需要第二次接受 $\rho$，最优值二。

障碍 $H=9$ 的三词为 $\alpha^9,\beta^2\alpha\beta^2,\alpha\beta^4$；它复用 §31、§35 的实际首动作合并障碍。配对 $H=9$ 为前两词：初态可以用一次单叶上下文守卫分别识别，但一次共同接受 $\rho$ 后，两行共同到达大小 $9$、读 $B$ 的标签 $0$，仍要求不同初始目标。两个模型在该实际子节点都返回 $\infty$；若删去原始目标关联而只存当前行为，就会错误地允许终端输出。

证明及有限核对范围。矩阵直接满足 $A_{\mathrm L}^2=I$、$B_{\mathrm L}^2=-I$ 和 $A_{\mathrm L}B_{\mathrm L}+B_{\mathrm L}A_{\mathrm L}=I$。$I,A_{\mathrm L},B_{\mathrm L},A_{\mathrm L}B_{\mathrm L}$ 线性无关：写系数 $u,v,w,z$，两非对角项分别迫使 $w+z=0$、$w-z=0$，两对角项再迫使 $u=v=0$。故这是该四维 Clifford 表示上的忠实精确矩阵检验，矩阵相等不额外合并原 $E$。

对长度至多六的全部 $126$ 个初始正词、至多五的 $62$ 个上下文，逐一核对两侧，共 $15624$ 个动作案例，其中 $1032$ 个接受案例；检查同组成规范宏守卫、下一和第二未来资源、真实乘积、已知因子消去及虚拟读重建。每个初始词的三窗也由字面替换矩阵与整数正规坐标交叉核对。在上表九项搜索中，对全部规范可达键合计核对 $11701$ 个规范动作响应对应，并对所有字面上下文两侧合计核对 $76696$ 个响应及接受读的有序运输对应。每个非平凡子边还核对严格降低（TM.4714）；有限赢节点的查表策略在所有代表行上实际运行，正确返回本人初始目标，并达到各自计算的最坏接受深度和调用界。判负节点没有虚构的提取策略。

另外对实际 $\alpha$ 在 $H=13$ 下的纯替换路径核对 $j=0,\ldots,6$，叶数依次为 $1,1,2,3,5,8,13$，第六次在等号接受，下一候选 $21$ 拒绝；这同时覆盖 $H=1$ 所需的等尺寸首次替换和全部六相位及周期回接。规范宏 $(d,e)=(1,1),(1,2),(3,3),(3,6)$ 检查纯 $\alpha$、纯 $\beta$ 和零子块省略。左右已知非交换因子用 $L=E(\beta\alpha)$、$R=E(\alpha\beta)$、未知词 $\alpha\alpha\beta$ 实测：$L^{-1}(LE(\alpha\alpha\beta)R)R^{-1}$ 恢复原读，而交换消去次序得到不同值，故此负对照能发现因子次序错误。命题 47.11、47.12 的所有字面词、同源窗口、八边次数及连通、等号接受、宏拒绝和最终填充拒绝也由精确矩阵和正词计数独立核对。

这些有限计算证实上述明确的计数与实例，提供对错误规范化、守卫等号、读／接受／拒绝、丢目标或左右次序的区分。它们不证明对任意 $H$、任意族成立，也不替代定理 47.4、引理 47.6 和定理 47.8 的普通全称证明。表中节点数随枚举和保留终端方式定义，不是最小记忆、复杂度下界或实测运行时间优势。$\square$

### 47.10 关系恢复的回接、来源与未决边界

对同一实际运行，空间侧的当前／下一资源 $(m_i,n_i)$ 由初始组成和已接受材料的运输给出，时间侧的 $j$ 指真实接受替换次序，边界侧的候选集由有限 Fibonacci 拒绝下界、最终上界和实际读等式给出，记忆侧保留使这些等式成立的已取得支路与有序外因子。定理 47.8 把这几个同源表达接到原始目标解码：在正确协议的终端观察纤维上，初始 $q_H$ 恒定；需要可取得性时，还必须执行相应真实策略，静态存在一个解码函数本身不够。

若目标具有初始标签 $2$，成功输出保留其完整 $W_3$ 和组成，故 §28 的六周期公式可从这项结果重新生成该来源的代数 $E(\rho^k t)$ 历史；这是数学序列重建，不是曾实际执行的物理历史恢复，超限窗口也没有被当作实际读取得。初始标签 $1$ 或 $0$ 的目标截断了更深窗或组成信息，本章不把这些遗失字段重新填入。不同原树可能具有相同目标，给它们重造一个规范来源不等于找回本人括号、叶路径和过去。

一般目标在实际记录纤维上恒定与恢复因子的等价，复用仓内 [TargetRecoveryCriterion](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean) 的 `target_recovery_criterion` 和 [IndexedTargetSufficiency](../../../D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency.lean) 的 `indexed_target_sufficiency`。未来行为商的通用边界仍取 [ReachableBehaviorMinimality](../../../D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality.lean) 的 `finite_state_minimality` 所列作用、可达性和外部行为条件；它不自动提供本合同的上下文生产、信息保护或取得政策。这里只引用这些现有数学接口，不声称本章进行了其当前编译。初态识别的成熟文献背景沿用 §31 与 §46.9 已列的区分序列和带输入输出状态识别来源，不借用其长度界证明本章资源估计。

来源特定供应为 §§28–30 的精确整数群、实际三窗运输与行为核；§35 的双资源宏和有序读模拟及取得存在性；§38 的原始目标配对；§45 的历史过滤和字段充分界；原子卷 §§359–360 的同源正规形、Euler 实际认证及单位词。普通稳健递推、目标因子化、子集信念表和这些既有结论均不是本章新发现。本章新增的是有限组成全动作覆盖、资源／候选数进展、可达候选集计数和有费用边界的策略提升的组合，以及隔离 TM46 两个前提的实际 $H=12,80$ 见证。不主张文献优先权、全库无重叠或新的群结构。

完整表和可计算读接口是本章完成结论的条件，不是已经解决的供应算法。全族 $M_A(H)$、更紧的复杂度和表示下界、没有给定完整表时的有效来源成员判定及认证取得、最优总记忆、任意成本目标的最优策略、原始完整历史与物理空间时间的关系互恢复仍未解决。固定有限实际输入的取得可行性和最优接受深度已经由上述有限普通算法完整决定；它不完成长期整体目标，也不把普通数学与有限检验等同于仓库 required CI 或 Lean 核验。

## 追加锚（本行以下为增补区）

## 48. 实际正源的紧凑剩余接口、原始目标投影与付费读转换

本章的目标是同一未修改来源的 $q_H$，而不是执行后的当前商。原子卷 §§359–360 供应实际共同三窗及组成的完整像，§45 供应实际历史过滤，§47 供应全动作取得与最优接受深度。本章把这些供应接到固定维整数可行性和去重投影算法：对明确有效的来源族，局部可行性、终端原始目标、永久碰撞及受限族的目标计数可以不输出整个来源表。以下均为普通数学证明；没有执行 Lean 核验、Lenstra 或 Barvinok–Woods 后端，也没有以有限枚举检验代替这些算法的通用正确性。

### 48.1 来源域、有效族与连接支撑图册

**定义 48.1（原合同及有效输入）。** 固定整数 $H\ge1$，令 $\mathcal T_H$ 为 §§28、30 的全部实际非空有序 $\alpha/\beta$ 二叉树，初始叶数在 $[1,H]$。叶序及括号仍属于来源身份；$E$ 是关联 Clifford 叶积。实际 $\rho$ 满足 $\rho(\alpha)=\beta$、$\rho(\beta)=\langle\beta,\alpha\rangle$ 并保持原二元构造。唯一观察及修改合同仍为 §30：真实当前 Read、$\rho$、命名实际正上下文的左／右拼接，整候选叶数 $\le H$ 接受，拒绝为来源恒等且不给候选读。没有重置、复制、解接、来源逆操作、树地址、隐藏组成或未读窗口端口。

写初始共同参数为

$$
x=(u,v,w,X,Y)\in\mathbb Z^5,\qquad p,q\in\{0,1\},
\qquad \Omega=L(u,v,w)R_{pq}.
\tag{TM.4801}
$$

这里 $L,R$ 取原子卷定义 359.1。依定理 360.2 定义

$$
\begin{aligned}
a&=4X+2w-2u+p,& b&=4Y+2u-2v+q,\\
z&=(X+w-u+p,\ X+w,\ X,\ X-u;\\
 &\hspace{13mm}Y+u+q(1-p),\ Y,\ Y-v+pq,\ Y+u-v).
\end{aligned}
\tag{TM.4802}
$$

$z$ 的顺序为 $(x_{00},x_{10},x_{01},x_{11};y_{00},y_{01},y_{10},y_{11})$。$x$ 边翻转状态第一位，$y$ 边翻转第二位；八边的具体起止点取原子卷定义 360.1。谓词 $V_H(x,p,q)$ 要求 $z\ge0$、$1\le a+b\le H$，并要求所有正重数边的端点连同 $00$ 在忽略方向后连通。全零边及不与起点连接的回路均不合格。

有效族有两个分别使用的范围。可行性范围允许对每个有限端点／模二图册显式给出一列有理仿射等式和非严格不等式的有限并，记为 $\Phi(x,p,q)$；片数计入输入，不以一个未经展开的任意 Boolean 公式代替这列。投影计数范围另固定一个常数 $c$，每个端点／模二图册至多 $c$ 片，$c$ 不随 $H$、历史或输入位长增长。片内的不等式数和系数位数可以增长。不添加新的整数未知量，不以可执行程序、括号语言或任意成员 oracle 定义这些片。两个范围都声明

$$
\mathcal F_\Phi=
\{t\in\mathcal T_H:\Phi(x(t),p(t),q(t))\},
\qquad \tau(t)=q_H(t).
\tag{TM.4803}
$$

即包含满足限制的每棵实际树，而不只包含一个人为挑选的代表。全活上限族取 $\Phi=\mathrm{true}$、$c=1$。若 $\Phi$ 描述已经供应的标签纤维，标签值必须在修改前由另行授权、计费的同源生产者真实供应；一个纤维公式本身不生产实际标签。令 $B_H=\lceil\log_2(H+1)\rceil$，$s$ 为族描述的二进制位长；所有有理系数均以分子／正分母给出。

**引理 48.2（固定维实际来源图册）。** $V_H\wedge\Phi$ 恰是维数五的有限有界有理多面体的整数点并，在每片上三窗正规坐标及初始目标有有限仿射分支。在固定片数范围，这个并的片数有与 $H$ 无关的常数上界。每个整数点都有属于 $\mathcal F_\Phi$ 的一个实际非空来源，且每个允许来源均被包含。

证明。固定 $(p,q)$、$\delta=(u\bmod2,v\bmod2,w\bmod2)$ 及八边非空支撑掩码 $\sigma$。只保留其端点连同 $00$ 连通的掩码；对 $e\in\sigma$ 加 $z_e\ge1$，对其余边加 $z_e=0$。这是用有限离散情况完整表达连接性，并没有把连接性降为流量平衡。置

$$
(u,v,w)=(2h+\delta_u,2k+\delta_v,2l+\delta_w),
\qquad (h,k,l,X,Y)\in\mathbb Z^5.
\tag{TM.4804}
$$

在此图册，所有边、组成与资源都是这五个整数的仿射式。原子卷推论 359.4 给出

$$
\begin{array}{c|ccc}
i&0&1&2\\ \hline
\kappa_i&2u+q-2pq&2v+p+q-2pq&2w+p+2q\\
\epsilon_i&v+pq\pmod2&w+pq\pmod2&u\pmod2\\
\gamma_i&p+q\pmod2&p&q
\end{array}
\qquad E_i=N(\epsilon_i,\kappa_i,\gamma_i).
\tag{TM.4805}
$$

模二选择使所有符号和等级成为常数，指数成为整数仿射式。给定一个窗口等式时，符号／等级不符便删去整片，否则只加一个指数等式。初始标签按 $a+2b\ge H+1$、$a+2b\le H<2a+3b$、$2a+3b\le H$ 分为三片；严格整数条件改写为差一的非严格条件。

这些多面体在实数意义下也有界。八边非负且总和为 $a+b\le H$，每条边均在 $[0,H]$。由原子卷式 (360.3)，$u=x_{01}-x_{11}$、$v=x_{01}-x_{11}+y_{01}-y_{11}$、$w=x_{10}-x_{01}$，且 $X=x_{01},Y=y_{01}$。因此可加 $|u|,|w|\le H$、$|v|\le2H$、$0\le X,Y\le H$ 的冗余实界，(TM.4804) 的变量也有 $O(H)$ 界。无需以额外变量保存模二条件。

实际树的叶词从 $00$ 经过八边图，给出相应端点、模二及连接支撑，故被包含。反之，图册整数点满足定理 360.2 的全部条件，其八边给出从 $00$ 到 $(p,q)$ 的非空 Euler 正词，任意固定有序括号化就是一个实际来源。这同一个来源有指定组成及全部三窗，因而满足 $\Phi$；不是分别实现各个边缘窗后将其拼合。基本情况数至多 $4\cdot8\cdot255\cdot3=24480$，再乘显式族片数；固定 $c$ 时为常数。$\square$

### 48.2 部分真实读下的精确剩余与响应闭合

**定义 48.3（共同历史的实际剩余）。** 固定同一公共初始化、有效族及已经实际达到的共同有限记录 $\omega$，使用 §45 定义 45.2 的字段

$$
\mathsf B_\omega=(j,U,V,P,Q,I,(z_i)_{i\in I},r_0,\ldots,r_{j+1}).
\tag{TM.4806}
$$

$j$ 是完整接受 $\rho$ 次数；$P,Q$ 是已知有序外因子；$I\subseteq\{0,1,2\}$ 只保存由真实当前读规范化取得的初始窗。$r_k$ 是相应 Fibonacci 方向的最大非负拒绝下界。令

$$
\lambda_k=F_{k+1}a+F_{k+2}b,
\qquad
\Psi_\omega=V_H\wedge\Phi\wedge(\lambda_j\le H-U)
 \wedge\bigwedge_{k=0}^{j+1}(\lambda_k\ge r_k+1)
 \wedge\bigwedge_{i\in I}(E_i=z_i).
\tag{TM.4807}
$$

三重代数单位只表示尚无外材料，不属于可调用的空来源。输入的真实历史、上下文身份及系数解析费用另计；压缩字段不声称重建任意旧程序状态。实际非空节点有 $j\le J_H=\max\{j:F_{j+1}\le H\}=O(B_H)$，$0\le U\le V\le2U$、$U\le H-1$、$r_k\in[0,H]$，均复用 §§45、47。取 $L$ 为族、多面体条件、$H$ 和紧凑字段的总位长；完整来源描述、原始系数响应及字面档案不计入这个压缩输入。Fibonacci 系数按指标生成，或全部显式列出，均有 $L=O(s+B_H^2)$ 的充分表示界。

**定理 48.4（同一实际历史的完整来源与下一响应）。** 对定义 48.3 的输入，$\Psi_\omega$ 的整数点恰给产生整个 $\omega$ 的允许初始共同参数。每个可行点都有一个实际初始来源沿这同一记录到达，其所需输出仍为 $\tau=q_H$ 的初始值。下一次 Read、$\rho$、命名正左／右上下文的每个非空响应和后继仍由相同五变量谓词表示，不需要先读全三窗。

证明。引理 48.2 已给实际来源及族的双向完整对应；定理 45.3 说明最后当前上界、全部拒绝方向下界及已经取得的窗口等式恰是整个历史。具体地，沿已接受正模板，叶数非递减，故最后 $\lambda_j+U\le H$ 推出以前全部接受守卫。拒绝给严格反向不等式，同方向只需最大者；读 $x$ 恰给 $z_r=J^{\lfloor j/3\rfloor}(P_0^{-1}xQ_0^{-1})$，$r=j\bmod3$。负下界可取零，因为所有实际 $\lambda_k\ge1$。对历史长度归纳，这些条件既必要又充分；既定自适应程序在相同已取得记录上选择相同动作。于是从可行点构造的那个正词本身遵从全记录，不仅在终点有相同资源。

各候选的实际当前资源及完整数学三窗为

$$
m=\lambda_j+U,\qquad n=\lambda_{j+1}+V,
\qquad W_3(s_\omega)=P\odot F^j(\Omega)\odot Q.
\tag{TM.4808}
$$

给定真实正上下文的已付参数 $(d,e),W_3(v)$，其接受／拒绝片分别加 $\lambda_j+U+d\le H$／$\lambda_j+U+d\ge H+1$；接受置 $(U,V)\leftarrow(U+d,V+e)$，并按侧更新 $P\leftarrow W_3(v)\odot P$ 或 $Q\leftarrow Q\odot W_3(v)$。拒绝只置 $r_j\leftarrow\max(r_j,0,H-U-d)$。$\rho$ 的两片分别用 $\lambda_{j+1}+V\le H$／$\ge H+1$；接受置 $(j,U,V,P,Q)\leftarrow(j+1,V,U+V,F(P),F(Q))$ 并附零下界，拒绝只加强 $r_{j+1}$。这些正是 §45 的更新，等号全部接受。

真实 Read 返回后只增加上述 $z_r$ 等式；若已有该窗，要求完全相等。拒绝没有候选读，拒绝之后的另一次 Read 读取原当前源。初始变量、族及函数 $\tau$ 在全部更新中都保持同一身份；计算当前商时另从 (TM.4808) 求 $(a',b')=(2m-n,n-m)$ 及当前保留窗。对任意有限延续归纳，便得同源响应闭合和初始输出关联。为继续某个依赖旧字面记录的程序仍须另存其程序状态；这里供应的是从节点重新指定延续的源向问题。$\square$

### 48.3 固定维局部判定与永久初始目标碰撞

**定理 48.5（局部可行性与合法终端输出）。** 在定义 48.1 的显式有限并范围，可用 $L^{O(1)}$ 位操作及临时空间决定 $\Psi_\omega$ 是否有整数点，返回一个 $O(B_H)$ 位的初始参数及八边实际证书，并决定一个非空节点能否立即正确输出同一初始目标。片数在 $L$ 中计费，固定维数为五。空谓词只表示没有兼容来源，不是一次实际运行的成功终端。

证明。引理 48.2 将谓词变为显式五维有界整数多面体的并，读等式由 (TM.4805) 处理。等式可写成两道不等式，有理系数清分母的位长仍为输入位长的多项式。Lenstra 的固定整数变量数可行性算法逐片决定非空性；原子卷的 Euler 定理已保证整数可行就是实际正来源可行。也可用 Barvinok–Woods 定理 1.7 的恒等映射情况计数整数点以判非空。两者都是调用已发表算法的数学构造，不是假定一个来源 oracle。

为了提取见证，在一个可行片的五个 $O(H)$ 有界整数坐标上逐坐标二分测试 $x_i\le t$，并在确定后加 $x_i=t_i$。每坐标 $O(B_H)$ 次决定足够，所有新增位长为 $O(B_H)$。由 (TM.4802) 得八边，全部整数仍为 $O(B_H)$ 位。输出文字正词是另一项费用。

取一个见证的初始目标 $\tau_*$，再测试 $\Psi_\omega\wedge(\tau\ne\tau_*)$。按初始标签及模二图册分支，目标是下面 (TM.4809) 的固定十三槽仿射向量。不同于 $\tau_*$ 是至多二十六个整数半空间的并；逐片测试仍在五维，片数增长为常数倍。若全不可行，每个兼容来源都需同一 $\tau_*$，输出正确；若可行，第二个实际来源沿同一记录却需另一输出，立即统一停机错误。一个任意选出的见证并不告知实际未知来源是哪一个。多项式运行时间也给多项式工作空间，不意味着所有算术只能用 $O(B_H)$ 位空间。$\square$

**定理 48.6（当前合并的实际双源查询）。** 在同一显式有限并范围，可用 $L^{O(1)}$ 位操作决定是否有两个产生 $\omega$ 的实际初始来源 $t,t'$ 满足

$$
q_H(t)\ne q_H(t'),\qquad
q_H(s_\omega(t))=q_H(s_\omega(t')).
$$

正答案可返回两个八边证书及其不同初始目标，此时任何允许的确定性有限延续都不能在全部兼容来源上成功。对一个指定下一动作，也可多项式决定某个实际共同响应后是否出现此类碰撞；命名上下文的精确参数位长加到输入，生产、读取及传输该上下文另计。无碰撞只是信息保留的必要条件。

证明。取两份引理 48.2 的图册，维数固定为十。每份同时保留同一个历史谓词与自己的初始目标；两点可不同，不要求源相同。分别按当前标签 $n>H$、$n\le H<m+n$、$m+n\le H$ 分支，当前组成为 $(2m-n,n-m)$。$F^j$ 的六相位以及 §28 的乘法和 $J$ 使 (TM.4808) 的每个当前指数在图册上仿射，符号与等级固定；奇偶指数已由图册固定。当前两个编码相等因而是仿射等式，符号／等级不符则删片。等价地，同一已知 $P,Q$ 可在保留窗的相等比较中消去，不能将这种比较当作实际材料解接。初始目标不同再拆为固定数目的严格方向不等式。两个有界源片的乘积仍有界；逐片固定十维可行性及二分见证提取给所称位复杂度，族片配对的平方也由显式输入长度支付。

两证书由定理 360.2 实现为正树，由定理 48.4 沿同一完整记录到达。当前 $q_H$ 相同使定理 30.2 的全合同未来记录相同；控制器持有的过去记录亦相同，初始所需输出却不同，所以不能都正确。这复用 §38 的配对不变量和命题 47.5 的永久合并结论。增加空白档案容量不增加来源区别。

下一上下文或 $\rho$ 查询，在两份源片各加接受或拒绝守卫，要求两者有同一响应，然后作相应更新；Read 则要求两个实际当前 $E$ 相等且来源不变。以更新后的当前商作上述比较，并始终以原初始目标作不等比较。修改最多两个共同响应，Read 的相等是固定相位仿射条件，片数仍可计费且维数不变。找到一个碰撞分支足以判该动作不能统一成功；所有分支都无碰撞仍须检查更长历史及 §47 的存在动作／全部响应递推，不是贪心成功证书。$\square$

### 48.4 去重的原始目标计数、秩与实际提升

**定义 48.7（固定目标编码）。** 对 §30 的初始 $q_H$ 使用向量

$$
\operatorname{enc}(\tau)=
(t,m,a,b,\kappa_0,\kappa_1,\kappa_2,
 \epsilon_0,\epsilon_1,\epsilon_2,\gamma_0,\gamma_1,\gamma_2)
 \in\mathbb Z^{13}.
\tag{TM.4809}
$$

标签 $t=0$ 只保留 $t,m,\kappa_0,\epsilon_0,\gamma_0$，其他槽置零；$t=1$ 保留 $t,a,b$ 及窗 $0,1$ 的三种字段，其他槽置零；$t=2$ 保留 $t,a,b$ 和全部三窗，$m$ 槽置零。这里 $m=a+b$。编码对实际 $q_H$ 单射，零槽只是遗忘字段的规范占位，不是额外的来源信息。在每个引理 48.2 的初始标签／模二片上它是整系数仿射映射。令

$$
Z_\omega=
\{\operatorname{enc}(q_H(t)):t\in\mathcal F_\Phi
                    \text{ 产生 }\omega\},
\qquad D_\omega=|Z_\omega|.
\tag{TM.4810}
$$

**定理 48.8（固定片数的完整目标投影）。** 在定义 48.1 的固定 $c$ 投影范围，可用 $L^{O(1)}$ 位操作、描述长度和工作空间构造系数恰为一的有限集合生成函数

$$
f_\omega(\mathbf y)=\sum_{z\in Z_\omega}\mathbf y^z
 =\sum_{\nu\in A}\frac{\alpha_\nu\mathbf y^{b_\nu}}
 {\prod_{h=1}^{k_\nu}(1-\mathbf y^{d_{\nu h}})},
\qquad \alpha_\nu\in\mathbb Q,\quad d_{\nu h}\ne0.
\tag{TM.4811}
$$

每个分母的因子数有只依赖固定维数及 $c$ 的常数界。负指数允许 Laurent 单项式。可以精确计算 $D_\omega$ 及目标成员判定；在初始全族节点这就是完整 $Q_H$ 的紧凑表示。计算的对象是不同初始目标，不是整数提升数、叶词数或括号数。

证明。对定理 48.4 的每个五维有界有理源多面体 $P$，用 (TM.4809) 的整仿射映射投影 $P\cap\mathbb Z^5$。Barvinok–Woods 定理 1.7 给这个整数像的短有理生成函数，系数按像集合计为一，并不将有同一像的不同整数点重复计算。仿射常量可以在所得生成函数外乘一个单项式；不必增加可变维数。输入映射无需满秩，十三维输出固定，定理允许降秩整数像。

引理 48.2 的连接支撑、端点、模二、初始标签及至多 $c$ 个族片共有固定数目。它们的投影可以重叠。使用该文推论 3.7 的集合并算法删除交叠重复；直接相加并不合法。推论的集合数与分母因子数必须固定，恰由这里的条件保证。所得并由定理 48.4 的两个方向完全等于 $Z_\omega$：每个实际来源被包含，每个像点也有同一历史的实际提升，因而既无幻源又无遗漏。

有限集合的函数本身是 Laurent 多项式，故 $\mathbf y=\mathbf1$ 是可去奇点。以该文定理 2.6 及其后关于正则点的特化算法计算 $f_\omega(\mathbf1)=D_\omega$；不能在每个分式的零分母处直接代值。成员判断也可在各原源片加 $\operatorname{enc}(\tau)=z$ 并用定理 48.5 判非空，外部查询向量的位长计入输入。算法输出位数均由多项式时间约束，得到所称描述与空间界。

片数可随输入增长的显式并仍适用定理 48.5–48.6；本定理不据此对其去重投影作同一多项式结论。任意 Boolean 公式的展开可能增加片数，反复并／交短函数也可能增加分母界；固定维数本身不消除这些限制。$\square$

**推论 48.9（有效秩、解秩与实际正源提升）。** 在定理 48.8 的范围，按 (TM.4809) 的十三槽词典序可多项式计算一个成员的零基秩，并对 $0\le r<D_\omega$ 解秩，返回唯一目标及一个实际来源八边证书。读出文字源仍须支付其长度。$D_\omega=1$ 时，解码唯一初始目标无需更多未知来源调用。若一个另行授权生产者确实知道该初始目标，那么该节点静态补充码最少需 $D_\omega$ 个符号，固定二进码需 $\lceil\log_2D_\omega\rceil$ 位，秩码达到此界。

证明。非零整数槽在 $[-2H,H]\cup[0,2H]$ 内有足够界，即统一 $[-2H,2H]$；初始三窗的指数界由每叶三窗的指数分别不超过二及 §28 乘法给出。对一个查询 $z$，词典序小于它的目标按第一不同槽分为至多十三类。每类把前槽等式及该槽 $\le z_i-1$ 加回每个原源多面体，再按定理 48.8 投影计数。类之间在目标层不交叠，故其计数和就是秩。这样每次都从固定数目原片重新构造，不对增长的生成函数任意多次 Boolean 组合。

解秩逐槽在整数界内二分，用已固定前缀及当前槽 $\le t$ 的投影计数，找包含第 $r$ 个目标的最小槽值，并减去此前各值的目标数。每槽 $O(B_H)$ 次查询；固定十三槽保证唯一解。加全部目标等式后，用定理 48.5 的五坐标二分提取一个实际提升。得到的初始正树属于族并遵从全记录；它只是一个兼容代表，不能冒称为实际未知原树本人。$D_\omega=1$ 时全部兼容输入需同一输出，合法立即停止由定理 48.5 保证。

静态码的下界及秩码构造复用有限纤维编码：两个不同目标不可共用同一码，且秩恰给 $D_\omega$ 个值。没有生产者时，这个容量计算不构成新信息端口；发生定理 48.6 的永久碰撞后，控制器不能从旧记录自行生产区分它们的秩。$\square$

### 48.5 已返回系数的付费精确转换

**命题 48.10（整数系数序列化适配器）。** 假设原合法 $E$ 端口已经返回四个精确有符号二进整数，按已声明、忠实的固定基 $(1,S,A,SA)$ 序列化，语义为当前实际 Clifford 叶积。取 $D$ 为总输入位长加一，则无需额外来源调用，可用 $O(D^2)$ 位操作及 $O(D)$ 工作位转换为唯一 $N(\epsilon,k,p)$；若编码不属于该正规单位群则拒绝转换。解析、接收、保存及输出均计费。也可从固定基 $(1,A,B,AB)$ 的整数输入做同阶转换。该结论的格式及语义假设不证明未知物理仪器符合性。

证明。偶部与奇部直和，单位非零。若两部都非零或都为零，拒绝；否则确定 $p$，将非零部分写成 $(x+yS)A^p$。利用 $S^2=S+1$ 及 $S^{-1}=S-1$，归纳得

$$
\begin{aligned}
S^n&=F_{n-1}+F_nS &&(n\ge1),\\
S^0&=1,\\
S^{-n}&=(-1)^n(F_{n+1}-F_nS)&&(n\ge1).
\end{aligned}
\tag{TM.4812}
$$

正式通过乘 $S$ 使用 Fibonacci 递推；负式从 $S^{-1}=S-1$ 起，通过再乘 $S-1$ 得下一项。因此 $y=0$ 只能为 $(x,y)=(\pm1,0)$、$k=0$，$x=0$ 只能为 $(0,\pm1)$、$k=1$。其余同号非零系数只能是 $\pm(F_{k-1},F_k)$、$k\ge2$；异号只能是 $\pm(-1)^n(F_{n+1},-F_n)$、$k=-n$。顺次产生 Fibonacci 相邻对，同时检查正负两种完整系数对及全局符号。重复值 $F_1=F_2=1$ 不造成歧义：$k=1$ 的完整对为 $(0,1)$，$k=2$ 为 $(1,1)$，负指数对的两项符号相反。式 (TM.4812) 的唯一性也由 §28 的正规形唯一性保证。

令 $M=\max(|x|,|y|)$，当 $F_n>M$ 后，未来正负候选均不可能匹配。由 $F_{n+2}\ge2F_n$，至多 $O(D)$ 个递推步；每步只加、比较和检查 $O(D)$ 位整数，所以时间 $O(D^2)$、工作位 $O(D)$。没有精确匹配就拒绝，不使用近似对数或浮点识别。若原基系数为 $(c_0,c_A,c_B,c_{AB})$，由 $AB=1-S$、$B=SA$ 转为 $(c_0+c_{AB},-c_{AB},c_A,c_B)$，只有定数次整数运算，已含在界内。

当前叶数 $\le H$ 使当前 $E$ 的 $|k|\le H$：每个 $A$ 增量为零、每个 $B=SA$ 对累计指数贡献 $\pm1$。Fibonacci 展开因而有 $D=O(H)$ 的充分输入界，紧凑输出只需 $O(B_H)$ 位。这个展开界可以达到：正词 $(\beta\alpha)^r$ 有 $2r$ 叶且 $E=S^r$，取 $r=\lfloor H/2\rfloor$；由 $F_{n+2}\ge2F_n$ 及 $F_{n+1}\le2F_n$，其系数位长为 $\Theta(H)$。接收 $D$ 位不能按 $O(B_H)$ 计费。已知 $P,Q$ 的消去及 $J$ 随后在 §28 紧凑坐标中进行；这些是已返回数值的计算，不是逆向修改来源。一个精确实数语义、未指定算法的符号或误差区间均不满足此整数序列化前提。$\square$

### 48.6 与全动作规划的合法组合及搜索规模

**定理 48.11（紧凑接口对 §47 的保持）。** 对定义 48.1 的有效族和实际入口，定理 48.4–48.6 可替代 §47 的逐表扫描，提供其终端判定、全部非空下一响应及永久碰撞检验。§47 的取得可行性和最优最坏接受 $\rho$ 深度递推保持成立。固定片数范围还可用 $D_\omega$ 和秩表达其目标字典。此组合没有新增来源动作，也不把局部多项式位复杂度变成全局多项式规划。

证明。集合 $\mathcal T_H$ 虽含许多括号，仍有限；其初始目标像亦有限。思想上按初始 $q_H$ 去重、从族内取一个代表，由引理 47.2 得完整表的语义。定理 48.4 精确给同一表的当前响应纤维，定理 48.5 给恰相同的终端条件，且不同初始目标从不按当前商合并。因此每条源—目标配对分支与 §47 的语义表分支一致，不必真的输出表。

动作仍取式 (TM.4707)：Read、$\rho$ 以及 $1\le d\le H-1$、$d\le e\le2d$ 的整次右宏 $A(d,e)$，宏源为 $\alpha^{2d-e}\beta^{e-d}$ 的固定括号正词。定理 47.4 已证明它覆盖所有允许正左／右上下文，保留守卫、初始目标及接受深度；模拟字面旧控制器时保持虚拟因子次序。没有将拒绝宏串行化。

在 $j=3q+r$ 处，下一真实读规范化为初始 $E_r$。可以列举 $N(\epsilon,k,p)$、$\epsilon,p\in\{0,1\}$、$|k|\le2H$ 的至多 $16H+4$ 个候选初始窗，逐个加等式并用定理 48.5 保留非空者。真实响应仍必须先由一次合法 Read 返回，再用 $P_0^{-1}xQ_0^{-1}$ 及 $J^q$ 选支；离线候选列表不告知实际响应。修改动作只需两次守卫可行性测试。单值读及全拒绝动作可复用推论 47.7 删去：它们对兼容来源不增加区别，冗余等式／下界不应被计作信息进展。

令 $N_\omega$ 为兼容的不同初始目标数。定理 30.2 使同一初始目标在同一程序下具有同一完整记录，故一个真正响应分裂将初始目标集合严格分裂，不能只是分开同一目标的两个提升。§47 的下降量

$$
(J_H-j)+(H-1-U)+(N_\omega-1)
\tag{TM.4813}
$$

对每条剩余边严格降低；接受 $\rho$ 通过完整 $j$ 进展，包括纯 $\alpha$ 的等尺寸首次替换。对该量归纳，§47 定理 47.8 的“选一动作、全部实际响应都成功”最小最大递推依然良基，得到同样的取得存在性和最优接受深度。计算一个目标数为一的节点是立即终端；规划值零的非终端则仍可能需要读／上下文，两者不混同。

计搜索规模时，可用 $j,U,V,(r_k),I,(z_i)$ 作为离线规范键；当前 $P,Q$ 不进入规范候选的取值计数，因为下一读使用已知因子重标记。实际执行仍保留它们。材料锥有 $H(H+1)/2$ 个 $(U,V)$，每个读槽有未设置或至多 $16H+4$ 个初始值，故一个充分键界是

$$
R_{\rm sym}\le
(J_H+1)\frac{H(H+1)}2
(H+1)^{J_H+2}(16H+5)^3
=2^{O(B_H^2)}.
\tag{TM.4814}
$$

此界是语法描述上界，允许重复键描述同一语义候选集，不断言最小。冗余字段和不同规范路径可按键去重；对子节点的实际目标数下降证明保证有用图无环。$N_\omega$ 在此只承担良基证明，片数可变时也可对已经生成的图拓扑排序，不需要把精确目标计数当作免费 oracle。显式字典比较支付 $O(B_H^2)$ 位键及 $O(\log R_{\rm sym})$ 次比较，每节点有 $O(H^2)$ 修改宏及 $O(H)$ 候选读。乘上局部多项式供应和有限递推，给一个 $2^{O(B_H^2)}\operatorname{poly}(s+B_H)$ 位时间／空间充分界。即使显式并的片数随 $s$ 增长，局部判定仍多项式，这个全球界仍可使用；投影生成函数的固定片数假设没有因此放宽。

选定只读策略已供应时，实际在线控制继续使用 §47 的节点地址及有序因子，$O(B_H^2)$ 可变控制字段界不包含算术工作空间、策略生产／保存、原档案、系数输入及输出。来源调用、尝试／接受材料及接受深度沿用 §47 的原界，没有获得新的物理时间界。全族无额外初始标签时，§31 的成功阈值仍是 $H\le8$；$H\ge9$ 的实际障碍不被模型供给消除。$\square$

### 48.7 显式供应、认证及输出费用

**命题 48.12（旧编译器的足够界与紧凑接口的费用边界）。** 全族初始表可复用原子卷定理 360.2，在 $O(H^5B_H^2)$ 位时间、$O(H^5B_H)$ 位空间内枚举五整数、验证并按初始目标去重，得到 §47 所需完整紧凑行表。这是旧像判据及枚举的应用。固定片数紧凑接口的局部费用为 $L^{O(1)}$，并不支付字面全表或来源输出；所有完整性认证仍须有对应证明或经核对的精确算法。

证明。枚举 $u,w\in[-H,H]$、$v\in[-2H,2H]$、$X,Y\in[0,H]$ 及 $(p,q)$，共 $O(H^5)$ 项。实际词的八边每项不超过 $H$，式 (360.3) 给出这些范围，故枚举完整；保留恰 $V_H$ 的行，每行通过连通 Euler 条件实现实际共同来源。求初始 $q_H$ 后比较排序去重，每目标留一个八边证书。仿射评估及固定支撑检查用 $O(B_H)$ 位操作，排序的 $O(\log(H^5))=O(B_H)$ 比较因子给所列保守学校算术界。有效限制 $\Phi$ 的逐行评估另加其实际描述／计算费用。验证每一行合法并不验证没有遗漏；完整性由枚举范围及双向对应证明给出，或由完整扫描复核，不能从若干有效代表推断全覆盖。

§§29–30 已给共同参数及目标数 $\Theta(H^5)$。一个八边证书只有固定多个 $O(B_H)$ 位整数；检查非负、端点、正支撑以及族／历史条件，用关于 $s+B_H^2$ 的多项式位操作即可。负可行性、投影去重及生成函数的认证还依赖所引精确算法与本章归约；检查若干正证书不会认证这些负答案或函数全体。没有供应新的 kernel 不可行性证书或经过实现核验的投影软件。

全族显式逐目标表至少需 $\Omega(H^5)$ 条输出；规定每条固定宽度字段及八边证书时为 $\Theta(H^5B_H)$ 位。若每条还必须含一棵文字代表，其总长度为 $\Theta(H^6)$：上界每棵 $O(H)$，下界取 $N_H\ge c_0H^5$ 及共同参数数 $|\mathcal J_L|\le C_0L^5$。长度 $\le\delta H$ 的来源最多提供 $C_0(\delta H)^5$ 个 $q_H$，因为初始目标由该来源共同参数决定；选固定 $\delta>0$ 使 $C_0\delta^5<c_0/2$，其余 $\Omega(H^5)$ 个目标的任何代表都长于 $\delta H$。故总文字输出 $\Omega(H^6)$。这是该字面格式的下界，不能移用于全部压缩描述。

从一个八边证书造 Euler 词可用 $O(H)$ 边步骤及 $O(HB_H)$ 保守位操作，括号输出再付 $O(H)$；生产物理来源并未由整数证书完成。编译、局部算术、图／策略描述、可变控制、完整档案、来源文字、Clifford 展开系数、上下文生产与传输、整候选守卫、实际 $\rho$ 展开、调用数及物理历时属于不同资源坐标。在同一次协议内才可按其已声明相加／峰值规则汇总；$L=O(s+B_H^2)$ 不能代替所有这些费用。这里没有实测运行加速、全局多项式取得、免费初始标签或真实仪器符合性结论。$\square$

### 48.8 支撑边界、部分读及初始目标合并的有限实例

**命题 48.13（两个已读窗仍有两个原始目标的完整实例）。** 取 $H=9$，共同真实记录为“Read 得 $A$；$\rho$ 接受；Read 得 $B$；右拼接单叶 $\alpha$ 拒绝”。在全族中，这个记录的不同初始目标恰有两个，初始组成为 $(1,4)$ 和 $(9,0)$；其当前目标只有一个 $(0,B,9)$。因此部分读掩码 $I=\{0,1\}$ 的剩余不可按当前目标去重。

证明。正词 $\beta\beta\alpha\beta\beta$ 与 $\alpha^9$ 的直接 Clifford 乘积都有 $E_0=A,E_1=B$；组成为 $(1,4)$、$(9,0)$，$\lambda_1=9$。第一次 $\rho$ 在上限等号接受，两者当前叶数九，右拼接一叶便拒绝，故确实共用所述完整记录。初始标签都为一：$\lambda_1=9$ 且 $\lambda_2$ 分别为十四、十八，目标因组成不同而不同。

反向，接受 $\rho$ 给 $n\le9$，随后拒绝一叶给 $n+1>9$，所以初始 $n=a+2b=9$。$E_0=A$ 在 (TM.4805) 中迫使 $p=1,q=0,u=0$、$v$ 偶；$E_1=B$ 进一步迫使 $v=0$、$w$ 偶。因此 $a\equiv1\pmod4,b\equiv0\pmod4$。结合 $a,b\ge0$ 与 $a+2b=9$，只可能 $(a,b)=(9,0)$ 或 $(1,4)$。两种都已有实际来源，且标签一只保留这些组成及两个已经固定的窗，故初始目标数恰二，不需要假设第三窗已读。当前第一次后继的未来替换尺寸分别十四、十八，均超限，故同为 $(0,B,9)$；任何正上下文或 $\rho$ 都拒绝，Read 恒为 $B$。这也是定理 48.6 的永久合并实例，新增档案容量不能自行重新取得初始区别。$\square$

纯 $\alpha^m$ 的八边只有 $x_{00}=\lceil m/2\rceil,x_{10}=\lfloor m/2\rfloor$ 非零；纯 $\beta^m$ 只有 $y_{00}=\lceil m/2\rceil,y_{01}=\lfloor m/2\rfloor$ 非零，$m\ge1$：连续同字母分别只在 $00,10$ 或 $00,01$ 往返，从 $00$ 开始就给出这些次数。它们都连接实际起点，无需占满四顶点。对应三窗由单叶三窗逐坐标乘法得到 $(A^m,B^m,S^m)$、$(B^m,S^m,(S^2A)^m)$，其中 $(S^2A)^2=S^2S^{-2}=1$。特别地，$H=1$ 有两个目标：$\alpha$ 标签一，第一次替换仍一叶并接受；$\beta$ 标签零，替换拒绝。空来源不能以单位乘积冒充。单位三窗和组成 $(4,0)$ 给四条 $x$ 边各一、四条 $y$ 边零，两个互不连接的回路；即使流量全平衡也不在实际像内。这些均复用原子卷的支撑边界，不将连续松弛点视为实际词。

一组有限确切数据为下表：对每个 $H$，实际非空叶词的三窗／组成联合像与连接八边证书像相等；目标列是在该 $H$ 的分层商下去重，故不等于提升数。

| $H$ | 不同共同三窗／组成 | 不同初始 $q_H$ |
| --- | --- | --- |
| 1 | 2 | 2 |
| 2 | 6 | 6 |
| 3 | 14 | 12 |
| 4 | 29 | 21 |
| 5 | 55 | 33 |
| 6 | 97 | 48 |
| 7 | 161 | 69 |
| 8 | 255 | 92 |
| 9 | 387 | 123 |
| 10 | 569 | 158 |

这些有限值可由忠实基 $(1,S,A,SA)$ 的整数乘法对非空词直接计算，另由八边计数、端点和连通支撑枚举计算；二者不是同一份像公式的重复求值。部分读响应的有限控制用实际当前词作守卫／替换／左右拼接，与 (TM.4807) 的初始谓词比较；签名转换含负指数、重复 Fibonacci 值、零及混合等级拒绝。有限一致只支持所列实例与有界控制，不证明固定维求解或短生成函数软件的普遍正确性；通用范围依靠前述普通证明及所引算法。

### 48.9 来源、重用关系与未决边界

固定维整数可行性引用 Lenstra，*Integer programming with a fixed number of variables*，*Mathematics of Operations Research* 8(4)，538–548，[DOI:10.1287/moor.8.4.538](https://doi.org/10.1287/moor.8.4.538)：固定的是整数变量数，不是不等式数或二进系数。去重投影、固定数目集合并及正则特化引用 Barvinok–Woods，*Short Rational Generating Functions for Lattice Point Problems*，[arXiv:math/0211146v1](https://arxiv.org/pdf/math/0211146v1)，定理 1.7、推论 3.7、定理 2.6 及其正则点注记。源多面体有界、整数像映射、片数和分母界固定是本章逐项满足的条件；计数不靠向分式逐项代入其极点。

实际来源归原子卷 §§359–360，群算术、窗口及资源归 §§28–30，历史与原始配对归 §§38、45，规划与深度归 §47。§§29–30 的增长、已有枚举／Euler 像、通用纤维编码及目标充分性均作为重用。仓内 [TargetRecoveryCriterion](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)、[IndexedTargetSufficiency](../../../D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency.lean) 与 [FiberBinaryIdentification](../../../D5/S3/ConceptDynamics/Coding/FiberBinaryIdentification.lean) 提供一般恢复／静态编码的既有接口；引用不声称其当前重新编译。新供应是明确实际正源域上的五维共同历史归约、去重初始目标投影、十维永久合并查询和付费系数适配的组合，不是新通用 solver、Euler 定理、行为商或文献原创性结论。

固定状态词的计数像与语言编译是成熟研究背景，可参见 To，*Parikh Images of Regular Languages: Complexity and Applications*，[arXiv:1002.1464v2](https://arxiv.org/abs/1002.1464v2)，以及 Esparza–Ganty–Kiefer–Luttenberger，*Parikh's Theorem: A simple and direct automaton construction*，[arXiv:1006.3825v3](https://arxiv.org/abs/1006.3825v3)。这里不借用未核对的增长界替代原子卷连接证书或当前源合同；表中八边图的紧凑编译也不成为新观察端口。初态识别与破坏性合并的文献背景继续取 §§31、46–47 的区分序列及带输入输出状态识别来源，不移入 reset、已知实际行或外部测试输入。

[OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md §§52–57](OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md) 分别以其标量迹／正树来源研究近似目标、源绑定校准和消费者／时限合同。本章既不把那里的模三、剥离、几何或校准端口移给 TM，也不从模型函数的精确性推出物理 $E$ 仪器已符合合同。树地址读出、随机组成树律、同源概率核与这里的确定性目标集合计数也各守原域；目标系数一不意味着实际来源概率均匀。

共同初始源参数连接空间侧资源 $\lambda_j+U,\lambda_{j+1}+V$、时间侧真实接受次序 $j$、边界侧拒绝／真实读约束和记忆侧初始目标剩余。在原合同与有效族条件下，它们由同一关系恢复所需目标；这不恢复原括号、叶地址、未记录过去或物理空间时间。任意族的有效翻译、一般 Boolean 家族的紧凑投影界、全族更锐利补充容量、合法非恒定标签生产、全局高效策略搜索、实际求解后端的认证与性能、仪器符合性和共同物理费用／校准仍需各自供应。局部理论接口是长期关系恢复目标的条件推进，不是整个目标的完成。

## 追加锚（本行以下为增补区）

## 49. 初始行为边界遗失的原树：饱和纤维、全上限极值与付费恢复

### 49.1 同一实际来源与两个补充目标

本章沿用 §§28–30 的自由有序非空来源、Clifford 叶积与固定活上限。原树的叶序和括号都是身份的一部分；结合的叶积相等不使原树相等。初始目标仍为 §31 的 $q_H(t)$。在此之外，分别研究补回组成和补回整个初始原树所需的来源记录。所有计数都是实际来源的基数，不给来源集合指定概率律。

**定义 49.1（原树纤维与初始饱和族）。** 对公开整数 $H\ge1$，令

$$
\begin{aligned}
\mathcal T&:\quad t::=\alpha\mid\beta\mid\langle s,u\rangle,\qquad s,u\in\mathcal T,\\
\mathcal T_H&=\{t\in\mathcal T:1\le\lambda(t)\le H\},\\
c(t)&=(a,b),\qquad m=a+b,\qquad n=a+2b,\\
E_i(t)&=E(\rho^it),\qquad W_3(t)=(E_0(t),E_1(t),E_2(t)),\\
\mathcal S_H&=\{t\in\mathcal T_H:m=H,\ b\ge1\},\\
\mathcal F_H(\tau)&=\{t\in\mathcal T_H:q_H(t)=\tau\},\qquad
R(H)=\max_{\tau\in q_H(\mathcal T_H)}|\mathcal F_H(\tau)|.
\end{aligned}
\tag{TM.4901}
$$

这里 $s,u$ 均为实际非空树，且

$$
\begin{aligned}
\rho(\alpha)&=\beta,&\rho(\beta)&=\langle\beta,\alpha\rangle,&
\rho\langle s,u\rangle&=\langle\rho s,\rho u\rangle,\\
q_H(t)&=
\begin{cases}
(0,E_0(t),m),&n>H,\\
(1,(a,b),E_0(t),E_1(t)),&n\le H<m+n,\\
(2,(W_3(t),(a,b))),&m+n\le H.
\end{cases}
\end{aligned}
\tag{TM.4902}
$$

标签二只是将 §29 的 $\eta$ 写成三窗与组成；没有更换其相等关系。$R(H)$ 数原始有序树，既不是不同 $q_H$ 的数目，也不是不同叶词、当前来源或任意选定代表的数目。每个固定的 $m$ 叶词有

$$
K_m=\operatorname{Cat}_{m-1}=\frac1m\binom{2m-2}{m-1}
\tag{TM.4903}
$$

种有序满二叉括号化。此经典计数沿用统计卷定理 2.2；原子卷推论 360.3 保证在本来源中这些括号全部保留，没有额外的括号合法性筛选。

### 49.2 饱和正 $\beta$ 纤维的全部叶序与全部括号

**定理 49.2（饱和纤维的精确实际计数）。** 设
$o=\lceil H/2\rceil$、$e=\lfloor H/2\rfloor$。对 $\epsilon\in\{0,1\}$ 和整数 $-e\le k\le o$，定义

$$
\begin{aligned}
Y_H(\epsilon,k)=\{y\in\mathbb Z:
&\max(0,-k)\le y\le\min(e,o-k),\\
&y\equiv\epsilon\pmod2,\quad k+2y\ge1\},\\
C_H(\epsilon,k)&=\sum_{y\in Y_H(\epsilon,k)}
\binom{o}{y+k}\binom{e}{y}.
\end{aligned}
\tag{TM.4904}
$$

在 $\mathcal S_H$ 中，目标
$\tau_{\epsilon,k}=(0,N(\epsilon,k,H\bmod2),H)$ 的纤维恰有 $C_H(\epsilon,k)$ 个有序叶词和 $K_HC_H(\epsilon,k)$ 棵原树。其组成集合恰为

$$
\{(H-k-2y,k+2y):y\in Y_H(\epsilon,k)\}.
\tag{TM.4905}
$$

空 $Y_H$ 表示该目标不存在，不表示存在空来源。

证明。复用引理 28.1 的唯一正规形及其有序乘法：

$$
\begin{aligned}
N(\epsilon,k,p)&=(-1)^\epsilon S^kA^p,\qquad S=BA,\\
(\epsilon,k,p)(f,\ell,q)&=
(\epsilon+f+p\ell\bmod2,\ k+(-1)^p\ell,\ p+q\bmod2),\\
E(\alpha)&=N(0,0,1),\qquad E(\beta)=N(0,1,1).
\end{aligned}
\tag{TM.4906}
$$

从左至右编号一个 $H$ 叶词。设奇数位置的 $\beta$ 数为 $x$，偶数位置的 $\beta$ 数为 $y$。乘入第 $r$ 片叶前的等级为 $r-1\bmod2$，所以奇数位置 $\beta$ 向指数贡献 $+1$，偶数位置 $\beta$ 贡献 $-1$ 并翻转一次符号；$\alpha$ 只翻转等级。归纳得到

$$
E_0=N(y\bmod2,x-y,H\bmod2).
\tag{TM.4907}
$$

正规形唯一性使给定 $\epsilon,k$ 的条件恰为 $x=y+k$、$y\equiv\epsilon\pmod2$。再加 $0\le x\le o$、$0\le y\le e$ 和 $b=x+y\ge1$，得到 (TM.4904) 的完整集合。对每个可行 $y$，独立选择 $o$ 个奇数位置中的 $y+k$ 个和 $e$ 个偶数位置中的 $y$ 个，恰有所写乘积数目的叶词；每一种选择都是实际正词。不同 $y$ 给不同组成 $b=k+2y$，每个可行组成都有这样的词。任取其 $K_H$ 种括号均为实际原树。又因 $m=H,b>0$，有 $n=H+b>H$，全部属于标签零，且该标签恰只保存这里固定的 $E_0,H$。因此计数和组成集合均无遗漏。$\square$

**命题 49.3（组成补充字母表的尖锐值）。** 在声明的整个饱和族 $\mathcal S_H$ 上，假设解码器收到初始 $q_H(t)$ 和由同一实际初始来源产生的附加符号。要对每个来源精确恢复 $c(t)$，一个共同附加字母表的最小大小及固定二进宽度分别为

$$
A_c(H)=\max_{\epsilon,k}|Y_H(\epsilon,k)|=\left\lceil\frac H4\right\rceil,
\qquad
b_c(H)=\left\lceil\log_2\left\lceil\frac H4\right\rceil\right\rceil.
\tag{TM.4908}
$$

这里的可达性是静态来源编码；附加符号并非 TM30 自动产生的读数。

证明。由 (TM.4905)，同一纤维的 $b$ 以四为步长，每个 $y$ 恰对应一个组成。若 $H=4d$、$d\ge1$，则 $o=e=2d$。整个 $y$ 区间的偶数点最多 $d+1$ 个；只有 $k=0$ 才可能容纳完整区间 $[0,2d]$，这时 $y=0$ 被正 $\beta$ 条件删去。$k\ne0$ 时区间至多有 $2d$ 个整数点，每个奇偶类至多 $d$ 个；$k=0$ 的奇数类也只有 $d$ 个。因此上界 $d$，而 $k=0,\epsilon=1$ 达到它。

若 $H=4d+1$，则 $e=2d,o=2d+1$，每个奇偶类至多 $d+1$ 个；取 $k=1,\epsilon=0$，恰有 $y=0,2,\ldots,2d$。若 $H=4d+2$ 或 $4d+3$，则 $e=2d+1$，每个奇偶类至多 $d+1$ 个；取 $k=0,\epsilon=1$，恰有 $y=1,3,\ldots,2d+1$。这些见证也覆盖 $H=1,2,3$。

不同组成共用 $q_H$ 时必须有不同附加符号，这是有限纤维编码的经典下界。反向将实际 $y$ 在递增的 $Y_H(\epsilon,k)$ 中的零基序号作为符号，不同纤维复用同一字母表；解码得到 $y$ 后用 (TM.4905) 恢复组成。于是上界可达，二进宽度为字母表大小的向上取整对数。此一般编码步骤复用 MinimalAppealLabelCount 和 BinaryRepairCost 的接口，本命题所计算的是本实际饱和来源的组成多样性。$\square$

### 49.3 跨全部初始标签的最大原树纤维

**定理 49.4（全上限纤维向初始饱和族的归约与精确极值）。** 对每个整数 $H\ge1$，$R(H)$ 的最大值在 $\mathcal S_H$ 内达到，且

$$
R(H)=K_H\max_{\substack{-e\le k\le o\\\epsilon\in\{0,1\}}}
C_H(\epsilon,k).
\tag{TM.4909}
$$

等价地，约定越界二项式为零，则

$$
R(H)=K_H\max_{\substack{-e\le k\le o\\\epsilon\in\{0,1\}}}
\left(
\sum_{\substack{0\le y\le e\\y\equiv\epsilon\ (2)}}
\binom{o}{y+k}\binom{e}{y}
-\mathbf1_{\{\epsilon=0,k=0\}}
\right).
\tag{TM.4910}
$$

证明。先取任一非空完整纤维 $\mathcal F_H(\tau)$，不能先假设它饱和。标签零显式固定 $m$；标签一、二固定 $(a,b)$，因而也固定 $m$。三个标签均固定 $E_0$。标签零有 $n>H\ge m$，故 $b>0$；标签一、二固定 $b$，所以每个纤维要么全部含 $\beta$，要么全部是 $\alpha^m$ 的括号化。

若 $m<H$ 且纤维含 $\beta$，取长度 $H-m$ 的固定全 $\alpha$ 原树 $v$。映射 $t\mapsto\langle t,v\rangle$ 在自由语法上单射，所得树均有 $H$ 叶、正 $\beta$ 数和共同的 $E_0(t)E_0(v)$，因此落在一个饱和标签零纤维。若 $m<H$ 且纤维只有 $\alpha^m$，改取同长度、含 $\beta$ 的固定 $v$，例如 $\beta\alpha^{H-m-1}$ 的固定括号化；完全相同的论证成立，$H-m=1$ 时 $v=\beta$。

若 $m=H,b=0$，把每片 $\alpha$ 改为 $\beta$ 而保留所有括号，得到到 $\beta^H$ 全部括号化的单射；其像是一个饱和标签零纤维的子集。若 $m=H,b>0$，原纤维已经饱和。四种情形覆盖三个标签和所有允许长度。它们是比较实际集合基数的语法单射，不是声称可用 TM30 执行改叶、逆向恢复或新取得协议。

故任一原树纤维不大于某个饱和纤维。饱和族本来就在 $\mathcal T_H$ 内，两个方向一起证明极值归约，再用定理 49.2 得 (TM.4909)。不带 $b>0$ 条件的二项式和只多计 $x=y=0$，即 $\alpha^H$；它位于 $\epsilon=k=0$，而且 $n=H$ 在守卫等号接受，实际属于标签一。减去这唯一叶词，再乘全部 $K_H$ 种括号，恰得 (TM.4910)。$\square$

### 49.4 带符号的二项式闭式与主项常数

**定理 49.5（原树极值的精确计算式与渐近）。** 设 $t=e+k$，并定义

$$
\begin{aligned}
D_H(k)&=(-1)^e[z^t](1+z)^o(1-z)^e,\\
C_H(\epsilon,k)&=
\frac{\binom Ht+(-1)^\epsilon D_H(k)}2
-\mathbf1_{\{\epsilon=0,k=0\}}.
\end{aligned}
\tag{TM.4911}
$$

系数越界取零。若 $H=2\ell$，则 $D_H(k)$ 在 $t$ 奇数时为零，在 $t$ 偶数时为 $(-1)^{\ell+t/2}\binom\ell{t/2}$；若 $H=2\ell+1$，则为 $(-1)^{\ell+\lfloor t/2\rfloor}\binom\ell{\lfloor t/2\rfloor}$。于是定理 49.4 给出有限二项式计算式，且

$$
R(H)\sim\frac{\sqrt2\,8^H}{8\pi H^2}
\qquad(H\longrightarrow\infty).
\tag{TM.4912}
$$

证明。不限制 $y$ 奇偶时，用 Vandermonde 恒等式得到
$\sum_y\binom o{y+k}\binom ey=\binom H{e+k}$。
带权 $(-1)^y$ 的和是 $(1+z)^o(1-z^{-1})^e$ 的 $z^k$ 系数，乘以 $z^e$ 后等于 (TM.4911) 中的 $D_H(k)$。偶／奇筛选分别取无符号和与有符号和的半和／半差，再删去唯一纯 $\alpha$ 词，得精确式。

偶长度时 $(1+z)^o(1-z)^e=(1-z^2)^\ell$；奇长度时为 $(1+z)(1-z^2)^\ell$。直接取系数得所列公式，因而 $|D_H(k)|\le2^{\lfloor H/2\rfloor}$。令 $M_H=\binom H{\lfloor H/2\rfloor}$。所有 $\binom Ht\le M_H$，而 $k=0$ 给中央值；在该 $k$ 选较大的奇偶类，删去纯 $\alpha$ 至多损失一，故

$$
\frac{M_H}2-1\ \le\ \max_{\epsilon,k}C_H(\epsilon,k)
\ \le\ \frac{M_H}2+\frac{2^{\lfloor H/2\rfloor}}2.
\tag{TM.4913}
$$

经典 Stirling 公式给
$M_H\sim2^H\sqrt{2/(\pi H)}$，故误差项相对 $M_H$ 趋零；又有
$K_H\sim4^H/(4\sqrt\pi H^{3/2})$。将两式及 (TM.4909) 相乘，得到 (TM.4912) 的常数。Catalan、Vandermonde、奇偶筛选和 Stirling 均是成熟计数工具；新增的来源事实是它们在实际初始 $q_H$ 纤维中的精确接合及跨标签的极值归约。$\square$

### 49.5 完整合法记录中的持续不可分与取得边界

**定理 49.6（初始同纤维的完整历史不可分）。** 设初始来源属于一个声明子族 $\mathcal F\subseteq\mathcal T_H$，已供应标签 $h:\mathcal F\to L$ 满足 $h=\bar h\circ q_H$。一个确定性控制器对相同 $h$ 使用共同程序、公开输入、初始控制态和初始记录；下一动作、记录更新、停止决定和输出只依赖这些量及已经取得的记录。其来源接口恰为 TM30：

1. `Read` 返回当前实际 $E$，来源不变。
2. $\rho$ 及用已知实际非空树 $v$ 的左／右拼接先检验整个候选的叶数是否 $\le H$；接受则更新实际来源并记录 `accept`，拒绝则来源不变、只记录 `reject`，没有候选的 $E$。
3. 记录保留动作名、上下文身份、标签、实际响应和所声明的控制字段；停止和最终输出也是控制器的决定。没有隐藏的树、尺寸、深窗、地址、时钟、费用、复位、复制、变上限或逆向解接端口。

若 $q_H(s)=q_H(t)$，则每一有限实际前缀的完整记录和当前 $q_H$ 相同，控制器的停止时刻（以调用步计）及输出相同；若不停止，所有有限前缀仍相同。因此任何由这些记录恢复的额外目标必须在初始 $q_H$ 纤维上常值。若该协议确实恢复初始 $q_H$，其终端记录的原树纤维恰为相应初始 $q_H$ 纤维在 $\mathcal F$ 中的限制，不能只计一个代表。

证明。同初始 $q_H$ 给同标签 $h$，从而共同初始化。复用引理 30.1：同当前 $q_H$ 的两来源在同一 `Read` 上给同读数；同一修改动作有同守卫位，拒绝均为恒等转移，接受后的所保留窗口、组成和新标签也相同。一个操作后的来源未必是同一原树，但当前 $q_H$ 仍相同。控制器从相同完整记录选同一下一动作和同一上下文，故对调用次数归纳，所有有限前缀和控制状态相同。记录更新函数若保留更多已有记录，输入仍相同。停止函数也有相同输入；一侧停止时另一侧同样停止并输出相同值。若它从记录准确恢复目标，任意两棵同初始纤维原树必须有同目标值。$\square$

若某协议在 $\mathcal F$ 上确实逐点有限停止并恢复初始 $q_H$，其终端完整记录的原树纤维恰为 $\mathcal F\cap\mathcal F_H(\tau)$：同初始目标给同终端记录，反向同终端记录给同正确输出。这是有条件的终端等价，不断言全族取得协议存在。若协议未取得初始目标，一个记录可能兼容多个初始纤维，每个存活纤维仍整块保留；不能把当前 $q_H$ 去重后的一个代表算成一棵原树。

在 $\mathcal S_H$ 上，`Read` 一次即取得初始 $(0,E_0,H)$；每个非空拼接候选有 $H+\lambda(v)>H$ 叶，每个替换候选有 $H+b>H$ 叶，全部拒绝。因而同纤维的完整历史只有共同读值及相同拒绝响应，保存任意多这样的记录仍不能恢复非恒定组成或原树。这里 $H$ 和族条件公开，不能将这条单读协议移成全 $\mathcal T_H$ 的自由初始标签。

全上限常量标签取得仍受定理 31.4 的 $H\ge9$ 否定约束。其实际三源
$X_H=\beta\beta\alpha\beta\beta\alpha^{H-9}$、$Y_H=\alpha^H$、$Z_H=\alpha\beta^4\alpha^{H-9}$ 有共同 $E_0=A^H$，但三个初始 $q_H$ 不同。读和长度大于四的拼接均给共同非改变前缀。逐点停止的正确协议必须最终选第一条其余动作：若选 $\rho$，$X_H,Y_H$ 同接受、同当前 $(0,B^H,H)$；若选任一侧长度一至四的拼接，$X_H,Z_H$ 同接受并合并为同标签零当前目标。该对的已见记录也相同，故不可能再分离原初目标。此复用说明：静态解码器收到 $q_H$ 的前提，与在原接口取得 $q_H$ 的任务，不能互换。

### 49.6 初始 $q_H$ 已供应时的尖锐原树记录宽度

**推论 49.7（固定来源界下的原树补充容量）。** 对每个 $H\ge1$，固定一个与实际未知来源无关的解码程序，假设它收到初始 $q_H(t)$，另收到由同一实际初始树产生并保留的固定宽度二进记录 $r(t)$。若要求对全部 $t\in\mathcal T_H$ 精确返回该原树，则最小宽度恰为

$$
b_{\mathrm{tree}}(H)=\lceil\log_2R(H)\rceil
=3H-2\log_2H+O(1).
\tag{TM.4914}
$$

同一值也适用于只要求 $\mathcal S_H$ 的共同宽度。若在某族上初始 $q_H$ 已由定理 49.6 的合法协议取得，保留它的全部终端记录或继续合法操作均不会细分原有 $q_H$ 纤维。全族 $H\ge9$ 的常量标签协议不满足取得前提。

证明。在含 $R(H)$ 棵树的一个纤维内，解码器的 $q_H$ 输入相同，附加记录必须两两不同，故 $2^b\ge R(H)$。反向给每个纤维的原树独立编号 $0,\ldots,|\mathcal F_H(\tau)|-1$，用共同的 $R(H)$ 字母表容纳这些编号即可；下一节给出有效编号，而不是免费实际行选择。定理 49.4 使两个声明族的最坏纤维相同，定理 49.5 取对数给渐近式。一般最大纤维编码与二进转换复用 MinimalAppealLabelCount、BinaryRepairCost；本章只确定它们在此原树目标上的精确多样性。历史的结论直接来自定理 49.6。特别地，$H=1,2$ 的宽度为零，这是以初始 $q_H$ 已供应为条件的端点，并不说无来源调用或无输入费用。$\square$

### 49.7 付费初始原树输入上的全上限秩与逆

**定理 49.8（全原树纤维的有效编号及足够数值费用）。** 假设编码者得到并支付对同一实际初始 $t\in\mathcal T_H$ 的完整有序树输入，包括叶序和全部括号；记录与解码者收到的初始 $q_H(t)$ 在身份上绑定，且记录真实保留。存在统一的精确编码／解码程序，使每个初始目标 $\tau$ 的原树纤维与整数区间 $[0,|\mathcal F_H(\tau)|-1]$ 双射。补充码用 (TM.4914) 的共同宽度。使用精确二进整数和学校算术，令 $B_H=\lceil\log_2(H+1)\rceil$，以下构造的算术位工作 $O(H^7)$、临时工作空间 $O(H^6)$ 足够；这些是数值 $H$ 的充分界，不是输入位长 $B_H$ 的多项式界或最优界。

证明。先说明词计数使用的已有来源结构。原子卷 §§359–360 的四状态源图以 $(p,q)$ 记已读 $\alpha,\beta$ 的奇偶，三窗为 $L(u,v,w)R_{pq}$。其乘入一片叶的整数增量依状态依次为

$$
\begin{array}{c|cc}
(p,q)&\alpha&\beta\\\hline
00&(0,0,0)&(0,0,0)\\
10&(0,0,1)&(0,0,0)\\
01&(1,1,-1)&(0,1,0)\\
11&(-1,-1,0)&(0,-1,0)
\end{array}
\tag{TM.4915}
$$

下一状态分别翻转 $p$ 或 $q$。在状态中同时保留组成，令 $z=(a,b,u,v,w,p,q)$，从零状态按该表累加并将 $a$ 或 $b$ 加一。$W_3=L(u,v,w)R_{pq}$ 和组成决定 (TM.4902) 的投影 $\pi_H(z)$。这只是已有实际源转导器及 §48 供应的使用，不将 Boolean 像编译器重新列为新增结论；此处附加的是同一初始目标的路径重数和原树身份秩。空前缀是计算起点，不能作为实际来源输出。

给定非空目标 $\tau$，其长度 $m$ 由标签零的 $m$ 或标签一、二的 $a+b$ 唯一确定。记 $z\cdot\sigma$ 为乘入叶 $\sigma$ 的状态。对所有长度至多 $m$ 的实际前缀状态，定义后向计数

$$
C_\tau(z)=
\begin{cases}
\mathbf1_{\{\pi_H(z)=\tau\}},&a+b=m,\\
C_\tau(z\cdot\alpha)+C_\tau(z\cdot\beta),&a+b<m.
\end{cases}
\tag{TM.4916}
$$

长度严格增一，所以由末层向前计算。两个同状态前缀有相同完整三窗及组成，接同一后缀仍有相同三窗和组成；末层投影相同。因此 $C_\tau(z)$ 不依赖哪个前缀代表到达 $z$，按剩余长度归纳恰数该前缀可接出的目标叶词。它数不同后缀而非不同终端状态，故不会将多个原叶词压成一个代表。每个图路径本来就是实际词，每个实际词也给唯一这样的路径；完整性由此双向对应供应，没有未知实际行 oracle 或任意族成员 oracle。

按 $\alpha<\beta$ 排目标纤维的叶词。读取实际叶词时从零状态、零秩开始；遇 $\beta$ 就先加上 $C_\tau(z\cdot\alpha)$，再沿 $\beta$ 前进；遇 $\alpha$ 直接前进。每层的 $\alpha$、$\beta$ 后缀是两个互不相交且按序相邻的块。逐层归纳得到叶词秩 $r_w\in[0,C_\tau(0)-1]$。反向比较当前整数与 $\alpha$ 块大小：小于则选 $\alpha$，否则减去该大小并选 $\beta$。最后余秩零且终端指标一，所以解秩恰恢复原叶词。零大小块不会被合法秩选中。

独立地按根的左叶数 $l=1,\ldots,m-1$ 排括号形状，再按左秩优先、右秩次之排序。单叶形状秩为零，分支形状的秩为

$$
r_s=
\sum_{j=1}^{l-1}K_jK_{m-j}
+r_{\mathrm{left}}K_{m-l}+r_{\mathrm{right}}.
\tag{TM.4917}
$$

Catalan 递推 $K_m=\sum_{j=1}^{m-1}K_jK_{m-j}$ 使这些块恰分割 $[0,K_m-1]$。定位块后对 $K_{m-l}$ 作除法求左右秩，递归即可解形状秩；结构归纳证明双向互逆。这是经典括号枚举的显式应用，不是新的通用树码定理。

最终令

$$
r(t)=K_m r_w(t)+r_s(t).
\tag{TM.4918}
$$

纤维含 $C_\tau(0)$ 个词，每词含全部 $K_m$ 个形状；混合进位给出恰 $K_mC_\tau(0)=|\mathcal F_H(\tau)|$ 个无空隙的编号。解码用商和余数解词、解形状，按叶序填入标记。自由有序树唯一由这两个对象决定，故返回的正是原来的树。越界秩必须拒绝；小纤维的共同固定宽度会有未用码。

费用方面，$a,b$ 非负且 $a+b\le H$，每个整数增量有固定界，所以 $|u|,|v|,|w|\le O(H)$。五个有界整数及固定奇偶字段给 $O(H^5)$ 个前缀状态，长度已由 $a+b$ 确定，没有再乘一层 $H$。确定性有序字典存实际可达状态和两条边；键长 $O(B_H)$、字典深度 $O(B_H)$。每个后向词计数至多 $2^H$，原树计数和秩至多 $\sum_{j\le H}2^jK_j<8^{H+1}$，均有 $O(H)$ 位。前向建图、后向加法及键比较可保守地包在 $O(H^5(H+B_H)^2)=O(H^7)$ 位工作内；存图、键和计数需要 $O(H^5(H+B_H))=O(H^6)$ 位。计算 Catalan 数、定理 49.5 的极值、形状块乘除及秩／解秩也在此界内：至多 $O(H^2)$ 次 $O(H)$ 位整数的学校乘除和一个 $O(H)$ 节点递归足够。临时空间可在一次编码或解码结束后释放；它与永久补充码宽度不是同一量。$\square$

输入和身份条件有实质费用。可用前序的三种符号“分支、$\alpha$、$\beta$”忠实序列化一个 $m$ 叶树，共 $2m-1$ 个符号；采用固定两位符号码时，读取、接收及保留完整原树档案需 $O(H)$ 位数据，树解析／索引可用 $O(HB_H)$ 位，全部被上述临时界覆盖。编码程序从此付费输入计算 $q_H$ 和秩，不调用未知当前源；这不说明 TM30 能交付该序列化。若已发生破坏性操作后才尝试读取当前树，该输入不是定理要求的初始树，除非另有真实初始档案。

解码输出同样必须支付 $2m-1$ 个树符号的写出和存储；若只消费秩，则没有免费展开树。初始 $q_H$ 在紧凑整数格式需 $O(B_H)$ 位，但它的实际取得、精确读数格式转换、描述及保留另计。永久秩记录用 $b_{\mathrm{tree}}(H)$ 位，完整树档案若同时保留须再加其空间；共享只读表的检索和合法共享权限也按实际合同计费。来源／版本标识的位长、绑定和核对成本没有由 $H$ 单独控制，须另付 $|\mathrm{id}|$ 及实际绑定费用。本定理假设绑定成立，不能把标识字符串或表中一个模型代表当作真实性证明；造一棵数学代表也不支付实际材料准备、守卫或物理生产。

### 49.8 端点、原树控制与当前目标控制

**命题 49.9（可直接核对的实际端点与反例）。** 本章计数及编码具有以下有限控制。

| 上限 $H$ | 最大初始原树纤维 $R(H)$ | 补充固定宽度 $b_{\mathrm{tree}}(H)$ |
| --- | --- | --- |
| 49.9（$H=1$） | 1 | 0 |
| 49.9（$H=2$） | 1 | 0 |
| 49.9（$H=3$） | 4 | 2 |
| 49.9（$H=4$） | 20 | 5 |
| 49.9（$H=5$） | 84 | 7 |
| 49.9（$H=6$） | 420 | 9 |
| 49.9（$H=7$） | 2508 | 12 |
| 49.9（$H=8$） | 15873 | 14 |

$H=4$ 时，$\beta\beta\alpha\alpha$、$\beta\alpha\alpha\beta$、$\alpha\beta\beta\alpha$、$\alpha\alpha\beta\beta$ 的全部五种括号恰为目标 $(0,-1,4)$ 的二十棵原树。$H=5$ 时，$\beta\alpha^4$ 与 $\beta^5$ 的任意括号同属 $(0,B,5)$，组成却分别是 $(4,1)$、$(0,5)$；该纤维的组成序号分别为零、一。

证明。将 (TM.4911) 对 $t=0,\ldots,H$ 的两个奇偶类求值、删去纯 $\alpha$ 项，$H=1,\ldots,8$ 的最大词数依次为 $1,1,2,4,6,10,19,37$；乘 $K_H=1,1,2,5,14,42,132,429$ 得表中值，再取向上整对数得宽度。$H=1$ 时 $\alpha$ 为标签一且第一次 $\rho$ 在等号接受，$\beta$ 为标签零并拒绝；$H=2$ 的两棵单叶、四棵双叶原树给六个不同初始目标，全部纤维单点。一般 $\alpha^H$ 在等号接受首替换，必须从饱和计数中删去；$\beta^H$ 则始终是非空饱和来源。

在 $H=4$ 的所列四词中，奇、偶 $\beta$ 数均为一，(TM.4907) 给 $N(1,0,0)=-1$；反向 $Y_4(1,0)=\{1\}$，恰有 $\binom21^2=4$ 个词，因此没有第五个叶词。每词五种括号全部保留。$H=5$ 的两词分别有 $(x,y)=(1,0),(3,2)$，故同 $\epsilon=0,k=1$，$Y_5(0,1)=\{0,2\}$；相同合法未来行为由定理 49.6 给出，不以其组成相同为前提。

再取 $t_L=\langle\langle\alpha,\alpha\rangle,\beta\rangle$、$t_R=\langle\alpha,\langle\alpha,\beta\rangle\rangle$。二者原叶词都为 $\alpha\alpha\beta$，三窗和组成都相同，故对每个 $H\ge3$ 有相同初始目标和共同 TM30 完整历史；(TM.4917) 的形状秩却分别为一、零。原树地址 $\mathtt L$ 的数学答案分别是分支、$\alpha$ 叶，正是独立树地址卷定义 16.1 的不同答案。叶词秩、$E$、$\eta$ 或一个目标代表均不能替代原树秩。

当前目标也不能替代初始目标。$H=9$ 时 $X=\beta\beta\alpha\beta\beta$ 与 $Y=\alpha^9$ 初始组成不同，但共同记录“Read 得 $A$；$\rho$ 接受；Read 得 $B$；右拼接 $\alpha$ 拒绝”将当前来源合并为 $(0,B,9)$。初始两标签一目标仍不同，复用命题 48.13 可知不能按这个当前目标合并原始行。把它们当成同一个初始纤维会给错误的码域。

最后，单位三窗和组成 $(4,0)$ 的八边候选虽然非负且平衡，正支撑分裂成两个回路，原子卷命题 360.7 排除实际来源；纯 $\alpha^4$ 的第三窗是 $S^4\ne1$。原子卷命题 360.6 的候选 $(1,1,-S^2)$ 也没有共同来源。这些候选都不能进入 (TM.4916) 的实际路径末层。$\square$

上述数值还可作彼此不同的有限核对：字面替换 $\alpha\mapsto\beta,\beta\mapsto\beta\alpha$ 后直接乘整数矩阵

$$
A=\begin{pmatrix}1&0\\-1&-1\end{pmatrix},\qquad
B=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
S=\begin{pmatrix}1&1\\1&0\end{pmatrix}.
\tag{TM.4919}
$$

直接相乘得到 $A^2=1,B^2=-1,AB+BA=1$。若 $x_0I+x_1S+x_2A+x_3SA=0$，右下、左上、右上、左下四项依次给 $x_0=x_2$、$x_1=-2x_2$、$x_3=x_1$、$-5x_2=0$，故四个系数均零。这证明 $1,S,A,SA$ 线性无关，因而给该四维代数的忠实表示。对 $H\le8$，非空词的三窗／组成联合像，与独立枚举非负八边、端点流量及连接支撑所得像相等；三个 $q_H$ 标签均按原始不等式投影。枚举每词的全部原括号可核对最大纤维，并逐树核对 (TM.4918) 的无碰撞、无空隙和完全逆。此方法区分原树、叶词、像点和当前目标；仅数像点的程序无法核对本命题。有限核对不替代定理 49.2–49.8 的全称证明。

### 49.9 所恢复的关系与仍需供应的执行记录

**命题 49.10（付费记录的恢复范围）。** 在命题 49.3 的身份和输入条件下，组成序号恢复 $c(t)$，从而恢复无上下文纯替换的完整数学资源轨迹；在定理 49.8 的条件下，原树秩再恢复原始叶序、全部括号和每个原树地址的数学结果。若另有完整的实际动作／响应档案及已知上下文，则可按原规则恢复其所指的数学来源状态与资源；单独的 $q_H$、组成序号或原树秩均不恢复未记录的实际执行、物理历时或真实仪器符合性。

证明。组成解码已经给出 $a,b$，所以 $M=\begin{pmatrix}0&1\\1&1\end{pmatrix}$、$F_0=0,F_1=1$ 的旧资源规律确定

$$
c(\rho^jt)=M^j(a,b),\qquad
\lambda_j=F_{j+1}(a+b)+F_jb\quad(j\ge0).
\tag{TM.4920}
$$

这是可计算的数学轨迹；在 $\mathcal S_H$ 内，$\lambda_1=H+b>H$，所以实际接受替换深度仍为零，已解出的 $b$ 不解锁操作。组成不决定叶序，也不决定括号；命题 49.9 的同词不同形状已经说明后一缺口。原树秩的双向逆则给出完整自由语法，故按地址逐边行走决定分支、两种叶和缺失结果，也能计算三个数学窗口和 $\eta$。展开替换树或输出一组地址必须另付其真实输出长度，$O(H^7)$ 界没有包含任意深度的无限输出。

若真实动作档案另已保留，从已恢复初始树逐步按所记 $\rho$、左右实际上下文及守卫位重放，便得到对应数学状态；已记录的拒绝保持状态。也可复用 §§35、45 的单出现运输，将当前两个资源写成 $\lambda_j+U,\lambda_{j+1}+V$，其中 $j$ 和已知材料贡献 $U,V$ 必须来自同一份实际记录。原树秩本身没有这些历史参数。一个饱和树可经历零次调用、一次 Read 或任意多次拒绝的非空拼接，三种过去有相同初始树和相同秩而记录不同。故从源记录不能反推哪段未记录过去真的发生，更不能推墙钟历时、准备或材料费用。

地址答案是解码后树上的数学函数，不是 TM30 新增的地址观察权。内部矩阵／源图的完整证明也不证明一个未知物理 $E$ 仪器在全部相关来源和动作上符合原规则；实际接口、来源身份、保留档案与物理时序仍须各自成立。$\square$

### 49.10 数学供应、复用归属与范围

原子卷 [§§359–360](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 供应实际正词、四状态三窗、连接八边判据及全部有序括号；本卷 §§28–30 供应唯一整数群算术、资源投影和精确行为核；§§31、35、38、45–48 供应初始目标取得边界、单出现运输、完整历史过滤、初始／当前关联与有效像接口。本章不重新供应 TM48 的编译器或规划器。统计卷 [定理 2.2、§§283–285](FIB_ATOM_STATISTICAL_LAWS.md) 已有 Catalan 回接和在其指定概率律下的条件纤维计算；本章的全上限极值是概率无关基数，不从那些统计结论移入均匀、Gaussian 或重置假设。

经典前置见 Stanley，[*Enumerative Combinatorics, Volume 2*](https://doi.org/10.1017/CBO9780511609589)，§6.2 的 Catalan 计数；Flajolet–Sedgewick，[*Analytic Combinatorics*](https://algo.inria.fr/flajolet/Publications/book.pdf)，印刷页 4 的 Stirling 公式及页 6–7 的二叉树计数、闭式和渐近。Vandermonde 与偶／奇系数筛选在定理 49.5 中只作经典中间步骤。通用恢复／最大纤维编码复用仓内 [TargetRecoveryCriterion](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)、[IndexedTargetSufficiency](../../../D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency.lean)、[MinimalAppealLabelCount](../../../D5/S3/ConceptDynamics/Appeal/MinimalAppealLabelCount.lean) 和 [BinaryRepairCost](../../../D5/S3/ConceptDynamics/Coding/BinaryRepairCost.lean)。其中恢复判据有非空域前提，有限编码结果要求有限来源及记录类型；这里的 $\mathcal T_H$ 非空、有限，$q_H(\mathcal T_H)$ 有限，故普通数学应用满足这些条件。引用源文件不声称当前重新编译或 Lean 核验，也不授予实际输入访问。

仓内 [SourceTreeEncoding](../../../D5/S0/History/Spacetime/SourceTreeEncoding.lean) 已有自由树的忠实语法编码；本章不是新通用树序列化定理。ReachableBehaviorMinimality 的有限状态、可达性和给定作用假设只供应抽象行为商，不能推出初始树输入或破坏性识别协议。独立 [树地址卷定义 16.1](FIB_SCALE_READOUT_PERMISSION_GEOMETRY.md) 的四值地址端口比 TM30 强，命题 49.9 展示不能反向移植；[观察者相对卷 §§49–51、54–57](OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md) 的真实身份、合法共享、校准与符合性义务仍各守自己的合同。

本章新增的 repo-derived 普通推导是实际初始饱和纤维的完整组成进程及尖锐 $\lceil H/4\rceil$ 补充字母表、覆盖全部三个标签的原树极值归约、精确有符号二项式／Catalan 极值与其主项常数，以及在同一付费初始原树输入上达到该宽度的有效秩和逆。历史持久不可分及通用编码作为已有结果的连接条件使用，不主张一般识别、计数或树码的文献优先权。范围止于这个固定来源界和明确初始输入；任意族判定、未给实际行、合法标签生产、全族 $H\ge9$ 常量标签取得、未记录执行恢复、物理时间与真实仪器符合性均未因此获得解。它给长期空间、时间、边界和记忆互恢复问题一个明确的来源记录条件，不把长期目标改成已经完成。

## 追加锚（本行以下为增补区）

## 50. 实际拒绝历史的精确取得关联与平方对数容量

### 50.1 固定合同、固定族与完整关联任务

**定义 50.1（普遍精确记录任务）。** 固定公开整数 $H\ge1$、非空实际初始族 $\mathcal F\subseteq\mathcal T_H$ 和与来源无关的公共初始化。来源、替换、Clifford 当前 Read 及受守卫的正左／右拼接严格取 §30：来源是非空有序 $\alpha/\beta$ 二叉树；$\rho(\alpha)=\beta$、$\rho(\beta)=\langle\beta,\alpha\rangle$；整个候选叶数 $\le H$ 才接受。拒绝保持当前树，不返回候选读数。允许的上下文必须是命名的实际非空树，宏不可拆成部分接受的叶动作。没有隐藏组成、未来窗、原树导航、重置、复制、解接、来源逆操作、时钟或费用读出。这里不供应来源依赖的初始标签；若写标签，其值恒为一。

令 $\mathscr R(H,\mathcal F)$ 为这个初始化下全部实际可达到的有限完整记录。记录包含每个命名动作的身份、真实接受／拒绝以及实际 Read 返回值；至少一个 $t\in\mathcal F$ 本身沿该记录执行才称为可达到。允许在这些记录上量化所有有限脚本及只依赖已取得记录的自适应控制，不要求记录属于同一个预选成功策略。对 $\omega\in\mathscr R(H,\mathcal F)$，定义

$$
\begin{aligned}
\mathcal A_\omega&=\{t\in\mathcal F:t\text{ 实际产生整个 }\omega\},\\
\tau(t)&=q_H(t),\\
\mathcal P_\omega&=\{(q_H(s_\omega(t)),\tau(t)):t\in\mathcal A_\omega\},\\
\mathcal Z_\omega&=\{\tau(t):t\in\mathcal A_\omega\}.
\end{aligned}
\tag{TM.5001}
$$

$s_\omega(t)$ 是该初始来源沿同一记录得到的实际当前树。$\tau$ 始终取初始值，$q_H(s_\omega(t))$ 则取当前值；$q_H$ 是定理 30.2 的固定合同精确行为商。$\mathcal P_\omega$ 保留当前行为与本人原始目标的关联，不按当前行为删掉不同原始目标。

一个容量为 $b$ 的表示是编码 $C:\mathscr R(H,\mathcal F)\to\{0,1\}^b$ 和固定解码器 $D_{H,\mathcal F}$，满足

$$
\forall\omega\in\mathscr R(H,\mathcal F),\qquad
D_{H,\mathcal F}(C(\omega))=\mathcal P_\omega.
\tag{TM.5002}
$$

解码器的静态输入是 $H$、已声明初始族的完整实际描述／表、同一公共初始化、固定的 §30 运算规则及精确数值表示约定。它们全部在历史之前固定并另行计费。解码器不另收当前树或当前行为、不查询未知初始行，也不新发 Read。全部可访问的历史依赖内容必须计入 $C$：包括旧动作流、宏长度、读数、辅助记录、控制状态、历史特定程序或其地址、表选择指针及外置存储的索引。一个包含所有可能历史的固定字典可以是静态输入，但选择其当前条目的地址不能免费。随机种子若依赖历史且参与精确解码，也在此计费。允许从完整记录离线编码；§45 已另给可逐事件更新的充分表示。

记 $b(H,\mathcal F)$ 为满足 (TM.5002) 的最小最坏固定宽度位数，$b_{\rm full}(H)=b(H,\mathcal T_H)$，并置

$$
B_{\rm rel}(H)=\max_{\varnothing\ne\mathcal F\subseteq\mathcal T_H}b(H,\mathcal F).
\tag{TM.5003}
$$

固定 $H$ 的非空有序树域有限；当前及原始行为都在有限 $Q_H$ 中，故可能关系有限，最小值和最大值存在。这个任务的普遍性是对全部可达到记录要求完整关系，不是要求一项策略访问全部记录。

**命题 50.2（目标集合的投影及逆恢复条件）。** 总有 $\mathcal Z_\omega=\pi_2\mathcal P_\omega$。若另已供应同一记录诱导的确定性当前映射 $f_\omega$，则

$$
\mathcal P_\omega=\{(f_\omega(\tau),\tau):\tau\in\mathcal Z_\omega\}.
\tag{TM.5004}
$$

因此只恢复存活原始目标集与恢复完整关系等价，须以 $f_\omega$ 可由已计费信息求出为条件。在定义 50.1 的无额外历史旁信息合同中，不能无条件宣称这两项任务等价。

证明。投影来自定义。相等初始 $q_H$ 的两个来源依定理 30.2，在同一命名记录上得到相等当前 $q_H$；因此在相容初始目标上 $f_\omega(\tau)=q_H(s_\omega(t))$ 良定义。该函数可以由已知动作运输求出，但旧动作身份或运输字段若因历史变化，必须计费，不能只由 $\mathcal Z_\omega$ 假定已知。

取原子卷推论 360.4 的实际单位词 $t=\omega_{1,1}$，公开 $H=100$、$\mathcal F=\{t\}$。记录“Read 得 $1$”与记录“Read 得 $1$，$\rho$ 接受，Read 得 $1$”都实际达到；两者原始目标集同为 $\{q_{100}(t)\}$。初始组成 $(4,4)$ 与后继组成 $(4,8)$ 都保留标签二，而各自三窗都是单位，故当前行为不同，完整关系也不同。于是仅凭相同原始目标集不能解码完整关系。另一方面，下文的显示历史有共同已知纯替换深度 $j$、无接受上下文，故其 $f_\omega=f_j$ 相同；在那个受限历史族上可以用投影区别来证明关系区别。$\square$

### 50.2 已有充分表示与相同量词

**定义 50.3（复用的源向字段）。** 对定义 50.1 的每个实际记录，使用定义 45.2 的字段

$$
\mathsf B_\omega=(j,U,V,P,Q,I,(z_i)_{i\in I},r_0,\ldots,r_{j+1}).
\tag{TM.5005}
$$

$j$ 是全部接受 $\rho$ 次数；$U,V$ 是运输至当前的已接受材料资源；$P,Q$ 是保持左右次序的已知三窗因子；$I\subseteq\{0,1,2\}$ 只含真实 Read 已规范化取得的初始窗；$r_k$ 是第 $k$ 个 Fibonacci 方向的最大非负拒绝下界。三重单位表示没有外材料的代数因子，不是空来源。令 $F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$，并写

$$
\lambda_k(t)=F_{k+1}a(t)+F_{k+2}b(t),\qquad
\mathcal U(x_0,x_1,x_2)=(x_1,x_2,J(x_0)),\quad J^2=\operatorname{id}.
\tag{TM.5006}
$$

这里 $\mathcal U$ 是 §§28、35 的窗口运输 $F$ 的改记号，避免与 Fibonacci 数混淆。定理 45.3 与命题 45.4 已证明

$$
\begin{aligned}
\mathcal A_\omega=\{t\in\mathcal F:\;&E_i(t)=z_i\ (i\in I),\quad
\lambda_j(t)\le H-U,\quad
\lambda_k(t)>r_k\ (0\le k\le j+1)\},\\
\binom{m'}{n'}&=T^j\binom{a+b}{a+2b}+\binom UV,\quad
T=\begin{pmatrix}0&1\\1&1\end{pmatrix},\\
W_3(s_\omega(t))&=P\odot\mathcal U^j(W_3(t))\odot Q.
\end{aligned}
\tag{TM.5007}
$$

由 $(a',b')=(2m'-n',n'-m')$ 和 (TM.3003) 计算当前商，由初始行计算本人 $\tau$，即解码 (TM.5001)。等号接受使拒绝条件严格；最后当前叶上界蕴含所有旧接受上界，因为正拼接及替换均不减叶数。实际读先消去已知左右因子，再按 $j=3q+r$ 用 $J^q$ 得到 $z_r$；该算术不取得未读窗口。表的数学三窗仅是静态可能行的描述，不告知未知行，也不提供新端口。

命题 45.5 已给非空节点 $0\le j\le J_H=O(\log(H+1))$、$0\le U\le V\le2U$、$U\le H-1$、$0\le r_k\le H$。至多 $j+2$ 个阈值各有 $O(\log(H+1))$ 位。已接受材料的两个有序叶词共至多 $H-1$ 叶，故 $P,Q$ 的六项正规指数均为 $O(H+1)$；至多三个已取得初始窗也有这个指数界。由 §28 的唯一正规坐标，全部这些非阈值字段共需 $O(\log(H+1))$ 位。于是同一个固定解码器通过 (TM.5007) 对每个实际记录恢复完整 $\mathcal P_\omega$，不再要求旧动作流作为旁输入。这直接复用 TM.4515，给统一常数 $C_0$ 使

$$
\forall H\ge1\ \forall\varnothing\ne\mathcal F\subseteq\mathcal T_H,
\qquad b(H,\mathcal F)\le C_0(\log_2(H+1))^2.
\tag{TM.5008}
$$

上界与定义 50.1 的初始族、完整关系及所有可达到记录量词一致。它是既有充分表示的应用；本章新增承重内容是下述实际来源的匹配下界。它不包括静态表、解码计算、展开输出或任意旧程序继续运行所需状态。

### 50.3 整数分离点及同源正词

**定义 50.4（有效单位来源族）。** 对整数 $j\ge2$，置

$$
Q_j=F_{j+2},\qquad T_j=Q_j^8,\qquad
M_j=\left\lfloor\frac{Q_j^4}{8}\right\rfloor,\qquad
H_j=80T_jF_{j+3}.
\tag{TM.5009}
$$

以下在固定 $j$ 内简写 $Q,T,M$。对 $0\le k\le j$，令

$$
A_k=F_{k+1},\quad B_k=F_{k+2},\quad t_k=B_k/A_k,\quad
n_k(r,s)=A_kr+B_ks,
\tag{TM.5010}
$$

并定义实际整数点

$$
R_k=T+\lfloor Tt_k^2\rfloor,\qquad
S_k=5T-\lfloor2Tt_k\rfloor.
\tag{TM.5011}
$$

对每个 $k$、$0\le v\le M$ 取点 $(R_k+v,S_k)$；另取锚点 $(10T,10T)$。点 $(r,s)$ 的来源为固定左结合有序括号化的正词

$$
\omega_{r,s}=\alpha^{2r-1}\beta^{2s}\alpha
\beta^{2s-1}\alpha^{2r}\beta.
\tag{TM.5012}
$$

令 $\mathcal F_j$ 为这些具体原树的集合。它在选取历史之前固定，与下文阈值向量无关。在每个 $H\ge H_j$ 使用同一族和常量初始化。

**引理 50.5（舍入后各方向独立）。** $t_k\in[1,2]$，这些 $j+1$ 个比值两两不同，且对 $k\ne l$ 有

$$
|t_k-t_l|\ge Q^{-2},\qquad
n_l(R_k,S_k)-n_l(R_l,S_l)
\ge A_l(Q^4-3)>A_lM.
\tag{TM.5013}
$$

因此对任意 $0\le v\le M$ 与任意 $0\le z_l<M$，$k\ne l$ 时

$$
n_l(R_k+v,S_k)>n_l(R_l,S_l)+A_lz_l.
\tag{TM.5014}
$$

证明。由 Fibonacci 递推，$A_k\le B_k\le2A_k$。相邻行列式 $A_kB_{k+1}-B_kA_{k+1}=(-1)^k$；固定 $k$ 后对 $l$ 递推得到

$$
A_kB_l-B_kA_l=(-1)^kF_{l-k}\quad(l>k).
\tag{TM.5015}
$$

非零整数行列式和 $A_k,A_l\le Q$ 给出比值间隔。先不舍入，置 $p(t)=(T+Tt^2,5T-2Tt)$；直接展开得

$$
n_l(p(t_k))-n_l(p(t_l))=A_lT(t_k-t_l)^2\ge A_lQ^4.
\tag{TM.5016}
$$

每个点的第一坐标舍入误差在 $(-1,0]$，第二坐标误差在 $[0,1)$，所以 $n_l$ 的误差在 $(-A_l,B_l)$。比较两个点损失小于 $A_l+B_l\le3A_l$，得到 (TM.5013) 的非严格充分界。$Q\ge3$ 且 $M\le Q^4/8$，故 $Q^4-3>M$。增加第一坐标 $v\ge0$ 只增加 $A_lv$，而 $z_l\le M-1$，于是得到严格 (TM.5014)。没有使用浮点近似或将不同方向的无约束极值拼成来源。$\square$

**引理 50.6（完整实际族及原始目标）。** 定义 50.4 的每个来源都是非空实际正树，组成、三窗和资源同时为

$$
c(\omega_{r,s})=(4r,4s),\qquad
W_3(\omega_{r,s})=(1,1,1),\qquad
\lambda_k(\omega_{r,s})=4n_k(r,s).
\tag{TM.5017}
$$

在每个 $H\ge H_j$，$\mathcal F_j\subseteq\mathcal T_H$，恰有

$$
N_j=(j+1)(M+1)+1
\tag{TM.5018}
$$

个不同初始 $q_H$，全部为标签二。

证明。由 $1\le t_k\le2$ 和 $M\le T$，分离点满足

$$
2T\le R_k\le5T,\qquad T\le S_k\le3T,\qquad
1\le R_k+v\le6T.
\tag{TM.5019}
$$

原子卷推论 360.4 已经证明 (TM.5012) 的同一正词有单位三窗及组成 $(4r,4s)$。其定理 360.2 的四条 $\alpha$ 边重数全为 $r$、四条 $\beta$ 边重数全为 $s$，全部严格正，起终点是 $00$，流量平衡且支撑连通。因而这里复用的是同一个实际来源，不是三个分别可实现的窗口。对实际替换组成应用来源卷 §3，即得第三式。

同一块内不同 $v$ 有不同组成。若 $(R_k+v,S_k)=(R_l+w,S_l)$、$k\ne l$，对该点取 $n_l$；由 (TM.5013) 左侧严格大于 $n_l(R_l,S_l)+A_lM$，右侧恰为 $n_l(R_l,S_l)+A_lw$ 且 $w\le M$，矛盾。锚点第一坐标 $10T>6T$，不在任一块中。

任一分离点、任一 $k\le j+2$ 有

$$
4n_k(r,s)\le24T(A_k+B_k)=24TF_{k+3}.
\tag{TM.5020}
$$

特别地 $\lambda_2\le24TF_5<H_j$，锚点 $\lambda_2=40TF_5<H_j$，故全族初始标签为二。组成两两不同，在标签二的 $\eta$ 中被保留，所以目标两两不同，证明计数与完整覆盖。来源词的括号保持身份；相同初始目标的其他原树若另纳入族，依定理 30.2 具有同一响应，但不是本人原树的恢复。$\square$

### 50.4 全部阈值历史的共同实际实现

**定理 50.7（合法历史与精确存活来源）。** 固定 $j\ge2$、公开 $H\ge H_j$ 及 $\mathcal F_j$。对每个

$$
z=(z_0,\ldots,z_j)\in\{0,\ldots,M-1\}^{j+1}
\tag{TM.5021}
$$

定义

$$
\ell_k(z)=4\bigl(n_k(R_k,S_k)+A_kz_k\bigr),\qquad
d_k(z)=H-\ell_k(z).
\tag{TM.5022}
$$

记录 $\omega_z$ 在深度 $k=0,\ldots,j$ 先作真实当前 Read，返回 $1$；再尝试整个右侧正宏 $\alpha^{d_k(z)}$，响应 reject；若 $k<j$，接着尝试 $\rho$，响应 accept。每个这样的非空完整记录都由同一个实际初始锚 $\omega_{10T,10T}$ 实现，终点恰为同一实际树 $\rho^j(\omega_{10T,10T})$。在 $\mathcal F_j$ 上

$$
\begin{aligned}
\mathcal A_{\omega_z}
=\{\omega_{10T,10T}\}
\ \cup\!\bigcup_{k=0}^j
\{\omega_{R_k+v,S_k}:z_k<v\le M\}.
\end{aligned}
\tag{TM.5023}
$$

全部历史的已接受材料贡献 $U=V=0$、有序外因子 $P=Q=(1,1,1)$；前三次真实读分别取得初始 $E_0,E_1,E_2$，而不是由离线表导入未读窗。

证明。由 (TM.5020)，所有宏阈值满足 $1\le\ell_k<H_j\le H$，所以 $1\le d_k\le H-1$；每个上下文都实际非空，有确定字面长度和固定括号。锚点在深度 $k$ 的叶数为 $40TF_{k+3}$。分离点及阈值的相应上界为 $24TF_{k+3}$，故锚在每个宏都严格超阈值，记录 reject。锚在最后深度 $j$ 恰有

$$
\lambda_j(\omega_{10T,10T})=40TF_{j+3}=H_j/2\le H.
\tag{TM.5024}
$$

纯替换叶数非递减，故所有此前替换候选都满足同一个 $H$ 守卫。拒绝宏保持本人树，不加入上下文材料，不返回候选值。单位三窗被 $\mathcal U$ 固定，且 $J(1)=1$，所以每个实际当前 Read 都为 $1$。这证明一条共同实际执行实现全部事件与同一终点；没有将多个来源的边缘响应拼为一条历史。

对任一分离点，$\lambda_j\le24TF_{j+3}<H_j$ 同样保证所有记录中的替换接受；所有深度的真实读均为一。其第 $l$ 个宏守卫为

$$
4n_l(r,s)+d_l\le H
\quad\Longleftrightarrow\quad
n_l(r,s)\le n_l(R_l,S_l)+A_lz_l.
\tag{TM.5025}
$$

因此拒绝恰为严格反向不等式。位于第 $k$ 块的点由引理 50.5 满足每个其他方向的拒绝条件；自身方向恰为 $v>z_k$，得到 (TM.5023) 的必要及充分两向。每个块的 $v=M$ 均存活，故节点非空且至少有 $j+2$ 个不同原始目标。

在第 $k$ 宏之前，第 $k$ 块的 $v=z_k$ 点已满足全部此前不同方向的拒绝；它的当前候选恰有 $H$ 叶，实际接受。锚则拒绝，所以宏确有两个非空响应，reject 分支严格删掉相容来源，而非删图中的全拒绝自转移。这个等号点不属于全拒绝记录的最终存活集；把 $>$ 写成 $\ge$ 会错误纳入它。前三个深度 $0,1,2$ 均真实达到且有 Read，已取得窗的含义因而严格满足 §45。$\square$

### 50.5 无当前碰撞的实际关联分离

**定理 50.8（不同原始目标在显示前缀中不碰撞）。** 在定理 50.7 的每个 $\omega_z$ 的每个事件前后，任意两个相容初始来源若原始目标不同，其当前 $q_H$ 也不同。此结论对每个 $H\ge H_j$ 同时成立。

证明。分离点在深度 $j$ 的第二未来替换叶数满足

$$
\lambda_{j+2}\le24TF_{j+5}
\le72TF_{j+3}<80TF_{j+3}=H_j\le H,
\tag{TM.5026}
$$

其中 $F_{j+5}=2F_{j+3}+F_{j+2}\le3F_{j+3}$。所以全部分离点在所有深度 $k\le j$ 均保留标签二。锚的下一替换叶数满足

$$
\lambda_{j+1}=40TF_{j+4}<80TF_{j+3}=H_j\le H,
\tag{TM.5027}
$$

因为 $F_{j+4}=F_{j+3}+F_{j+2}<2F_{j+3}$。锚在全部显示深度至少保留标签一。标签一及二均保存当前组成；所有初始组成两两不同，而 $M_{\rm src}=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$ 的行列式为 $-1$，故 $M_{\rm src}^k$ 保持组成不同。若标签不同直接分离；若标签相同，所保留组成分离。实际 Read 及拒绝不改源，没有接受上下文，所以事件间不会新增碰撞。限制存活集仍保留此性质。这里没有假定当前标签永远为二：锚在 $H=H_j$、深度 $j$ 可以为标签一，证明只需其组成仍保留。$\square$

**定理 50.9（不同阈值给不同可达到关联）。** 定理 50.7 中恰有 $M^{j+1}$ 个不同 $\mathcal P_{\omega_z}$；存活原始目标集亦有这么多个。区别发生于真实初始来源，且即使附加共同终点的锚行为作为固定旁信息，这个数目不变。

证明。若 $z\ne z'$，选一个 $k$；交换名称后可令 $z_k<z'_k$。实际来源

$$
t_* =\omega_{R_k+z_k+1,S_k}
\tag{TM.5028}
$$

属于固定族，因为 $z_k+1\le M$。它满足两记录所有其他方向的拒绝，满足 $z$ 的自身方向拒绝，却在 $z'$ 的自身方向接受。因此本人初始标签二目标属于 $\mathcal Z_{\omega_z}$ 而不属于 $\mathcal Z_{\omega_{z'}}$。族内没有另一行有此目标，故投影不同，完整关系不同。另一方面向量总数就是 $M^{j+1}$，给出精确数目。共同实际锚、共同 $j,U,V,P,Q$ 和共同读数均由定理 50.7 给出；这些固定值不能区分向量，宏身份的差别须进入已计费记录。

在全族 $\mathcal T_H$ 上使用同样的 $\omega_z$，这些历史仍由锚实现，也仍给至少 $M^{j+1}$ 个不同完整关系。理由不只是子族包含：若另一个全族来源有 $q_H(t_*)$，定理 30.2 保证其在相同命名脚本上的全部响应与 $t_*$ 相同，因而它也不能产生 $\omega_{z'}$。所以该原始目标在全族的投影中仍只属于前一记录。这并不宣称全族节点无当前碰撞；定理 50.8 的无碰撞范围是明确稀疏实际族。$\square$

### 50.6 每个充分大上限的尖锐容量与图规模

**定理 50.10（普遍精确关联的平方对数尖锐阶）。** 存在与 $H,\mathcal F$ 无关的常数 $c,C>0$ 和整数 $H_0$，使

$$
\forall H\ge H_0,\qquad
c(\log_2(H+1))^2\le b_{\rm full}(H)
\le B_{\rm rel}(H)\le C(\log_2(H+1))^2.
\tag{TM.5029}
$$

而且对每个这样的 $H$，存在历史之前固定的、有效描述的实际族 $\mathcal F_{j(H)}$，其 $b(H,\mathcal F_{j(H)})$ 也满足同阶上下界，且其下界历史全部满足定理 50.8 的无碰撞性质。因而尖锐阶为 $\Theta((\log_2(H+1))^2)$。

证明。不同关系不能由同一码经固定解码器解出，这是已有有限无损编码原理。应用定理 50.9 的实际关系数，任何表示必须有

$$
2^b\ge M^{j+1},\qquad
b\ge\left\lceil(j+1)\log_2M\right\rceil.
\tag{TM.5030}
$$

其新增前提是来源特定、共同可达到的关系数，不是一般抽屉原理。令 $\varphi=(1+\sqrt5)/2$、$L=\log_2\varphi$。由 Fibonacci 递推的 Binet 式（亦可用 §46.7 的既有推导）得

$$
\log_2Q=jL+O(1),\quad
\log_2M=4jL+O(1),\quad
\log_2H_j=9jL+O(1).
\tag{TM.5031}
$$

于是此构造的下界主比率为

$$
\frac{(j+1)\log_2M}{(\log_2H_j)^2}
\longrightarrow\frac{4}{81\log_2\varphi}>0.
\tag{TM.5032}
$$

这不是最优常数断言。$H_j$ 严格递增、无界，且 $F_{n+1}\le2F_n$ 给

$$
H_{j+1}/H_j\le2^8\cdot2=512.
\tag{TM.5033}
$$

对任意 $H\ge H_2=2624400$，选最大 $j\ge2$ 满足 $H_j\le H$。则 $H<H_{j+1}\le512H_j$，所以 $\log_2(H+1)=\log_2H_j+O(1)$，其中常数统一。定理 50.7–50.9 在整个区间使用宏 $d_k=H-\ell_k$，已经证明其守卫及无碰撞不随扩大上限失效；不沿用旧上限的固定宏。由 (TM.5030)–(TM.5033) 得充分大 $H$ 的统一下界，稀疏族及全族都成立。上界完全复用 (TM.5008)。$\square$

**推论 50.11（精确未剪枝取得图的可达到键数）。** 对上述固定实际稀疏表，§47 的键 $K=(j,U,V,C)$ 以不同初始目标索引保留候选，枚举全部允许规范动作；保留全部非空响应键，仅删除已确定自转移、并在单目标节点停止。这个图至少有

$$
M^{j+1}=2^{\Omega((\log(H+1))^2)}
\tag{TM.5034}
$$

个不同可达到键。即使在键进入后施行命题 47.5 的当前目标碰撞检验，显示路径与其末键也不会被该项检验删除。结合 TM.4718 的已有上界，该精确图的最坏规模阶为 $2^{\Theta((\log(H+1))^2)}$。

证明。显示宏正是 §47 的规范 $A(d,d)=\alpha^d$，$1\le d\le H-1$。每个宏的 accept 与 reject 部分都非空，reject 真删候选；每次接受 $\rho$ 改变完整 $j$，因此均非已确定自转移。单位 Read 在稀疏表上可能被图删除，但不改源或候选，去掉它仍到达相同键。每个前缀包含锚和各块的 $v=M$，所以不是单目标终端。最终 $U=V=0$、$j$ 固定而 $C$ 依 (TM.5023) 有 $M^{j+1}$ 个不同值。全部键各有同一锚真实执行的路径；不是允许的环境元组计数。定理 50.8 排除这些路径上的当前目标碰撞，故该特定前检也不删它们。上界来自命题 47.9，不在此重新命名规划算法。$\square$

此推论只涉及保留精确键的未剪枝图；所述碰撞检验是在进入键后检查该键，不包括因一个动作的其他响应判负而删去整个动作的安全剪枝。它没有证明每个末键都有统一成功延续，没有约束赢策略访问多少键，也不限制可按任务延续等价进一步合并的算法、所有规划算法或每项成功政策的记忆。

### 50.7 实际数值与区分对照

**命题 50.12（最小显示参数的完整实例）。** $j=2$ 时，$Q=3,T=6561,M=10,H_2=2624400$，三个基点分别为

$$
(R_0,S_0)=(13122,19683),\quad
(R_1,S_1)=(32805,6561),\quad
(R_2,S_2)=(21323,13122).
\tag{TM.5035}
$$

固定族有 $34$ 个不同初始目标，锚为 $\omega_{65610,65610}$；$10^3$ 个阈值向量分别有不同关联。以 $z=(0,0,0)$ 为例，宏阈值及宏长度为

$$
(\ell_0,\ell_1,\ell_2)=(131220,183708,328048),\quad
(d_0,d_1,d_2)=(2493180,2440692,2296352).
\tag{TM.5036}
$$

此记录恰有八次来源调用。三个等号来源 $\omega_{R_k,S_k}$ 在其相应宏接受；锚三个宏均拒绝，两次替换均接受。

证明。逐项代入 (TM.5009)–(TM.5022) 得所列整数。锚叶数从 $524880$ 经 $787320$ 到 $1312200$，均不超过 $H_2$；第三个未来尺寸为 $2099520\le H_2$，第四个为 $3411720>H_2$，所以末端锚标签一，而每个分离点末端标签二。等号来源在此前其他方向严格拒绝，由 (TM.5025) 在自身方向恰接受。两向量例如只把 $z_0$ 从零改为一时，实际 $\omega_{13123,19683}$ 在前一记录存活，在后一记录自身宏等号接受，故被后一全拒绝记录排除。34 行、1000 关系和调用数均由上述普通证明确定，不依赖把巨大实际词当成单位成本输入。$\square$

**命题 50.13（实际性、关联及宏原子性的反面控制）。** 单位三窗的组成 $(4,0)$、$(0,4)$ 和零组成均不能作为本章的实际来源；同一个当前目标也不能代替原始关联；把整个 reject 宏逐叶执行会改变来源。

证明。原子卷定理 360.2 在组成 $(4,0)$ 上给四条 $\alpha$ 边各一次、$\beta$ 边全零，支撑分成 $00\leftrightarrow10$ 与 $01\leftrightarrow11$，不连通。$(0,4)$ 同理分成两条 $\beta$ 回路。零组成无边，是被排除的空来源。相反 $(4,4)$ 的八边各一且全连通，已有非空单位词。故“各窗为单位”和非负流量不足以补全实际性。

在 $H=9$，实际 $\alpha^9$ 与 $\beta^2\alpha\beta^2$ 的初始组成为 $(9,0)$、$(1,4)$，初始 Read 共同为 $A$，一次 $\rho$ 都在九叶等号接受且后继 Read 共同为 $B$；再右拼接一叶都拒绝。两初始目标不同，当前目标共同为 $(0,B,9)$，这是 §48.13 的既有反例。若按当前目标删掉原始目标关联便漏掉永久损失；本章下界另用定理 50.8 排除了这一碰撞机理。

在命题 50.12 的锚初态，第一宏长度 $2493180$ 使候选叶数超限，整个宏拒绝而锚保持不变；若先拼接其第一片 $\alpha$，候选 $524881\le H_2$，会接受并改变原树。故串行叶接口不是所证明的原子宏合同。拒绝后的另一次 Read 只读未变锚，没有候选读可加入窗口档案。$\square$

### 50.8 分离费用、引用范围与恢复边界

**命题 50.14（显示族的资源分项）。** 令 $B_H=\lceil\log_2(H+1)\rceil$，固定公式生成器及精确整数学校算术。显示族的公式、参数、文字来源、真实调用、保留记录及解码的费用可分别取以下充分界；它们不组成一个未声明价格的物理时间界。

证明。来源族的固定规则加参数 $j,H$ 有 $O(B_H)$ 位描述；$Q,T,M$ 及全部点用精确 Fibonacci、乘法和整数除法生成。若显式输出 $N_j$ 个紧凑行及八边证书，描述为 $O(N_jB_H)$ 位；准备各基点及逐行计算可用 $O((N_j+j)B_H^2)$ 位操作的保守界。单位词和 Euler 证书的正确性来自原子卷已有结果及引理 50.6，不把编译器或认证接口重新列为新数学。

每个文字源有 $4(r+s)=O(T)$ 叶、$2\cdot4(r+s)-1$ 个树节点；锚恰有 $80T$ 叶。输出全部文字来源为 $\Theta(N_jT)$ 叶，单个请求则付它本人的长度。紧凑参数或八边证书不支付实际词、括号和物理来源生产。

每条显示历史恰有 $j+1$ 次真实 Read、$j+1$ 次 reject 宏尝试、$j$ 次 accept 替换，共 $3j+2$ 次来源调用。每个宏 $1\le d_k\le H-1$，实际供应全部尝试宏至多 $(j+1)(H-1)$ 叶；拒绝也付生成和传输，接受上下文材料为零。最后一个 $\rho$ 之后没有偷偷再尝试替换；额外读或动作须另计。若给定逐叶线性实现，$j$ 次接受替换所处理的活叶总数至多 $jH$，但 §30 不规定该实现或每次调用的物理时长。所有数字守卫均是整数精确比较，等号真实接受。

阈值向量或归一化阈值列有 $O(jB_H)=O(B_H^2)$ 保留位，生成全部宏长度的学校算术可用 $O(jB_H^2)$ 位操作，临时若干整数可用 $O(B_H)$ 工作位。这不将阈值向量作为额外公共输入；若把它编进专属程序，其 $M^{j+1}$ 种身份必须由已计费描述／地址选择。

采用完整实际代表表的固定解码器，可以扫描各行、检查 (TM.5007)、算初始和当前目标并输出关系；保守的紧凑算术界为 $O(N_j(j+1)B_H^2)$ 位操作，输出至多 $N_j$ 个各 $O(B_H)$ 位的紧凑配对。输出全部关系本身不是保留码大小；工作空间、静态表访问和输出缓冲单独计费。任意初始族的对应界取其实际代表行数，不假定成员 oracle 免费。全族完整表的供给可复用 §48.12 的原子像枚举；本章没有提出新编译器、固定维 solver 或新规划算法。

真实 Read 已返回精确正规单位坐标时，其处理按该表示计费。若返回展开整数 Clifford 系数，接收长度和转换另计：§48.10 仅在忠实固定基整数序列化前提下给 $O(D^2)$ 位操作、$O(D)$ 工作位的已有适配；一般合法源可有 $D=\Theta(H)$，不能用紧凑指数的 $O(B_H)$ 位代替它。本族的实际读全为一，不据此削去一般来源的读输出费用。以上描述、算术、档案、物质输出、端口调用和物理历时是不同坐标。$\square$

本章复用原子卷 §§359–360 的共同正规形、八边连通实际像与单位词，TM28–30 的正规坐标、组成运输、固定活上限及行为核，TM35 的有序已知因子运输，TM45.3–45.5 的实际历史过滤、完整关联解码与平方对数充分界，以及 TM47.9 的图规模上界。TM46 的资源序类识别不是本章前提，TM48 的来源接口、投影、碰撞查询及枚举均保持既有归属。这里只补实际可达到拒绝历史的独立方向构造、无碰撞桥梁及匹配容量／精确图下界。

一般目标纤维恒定及因子分解可对照仓内 [TargetRecoveryCriterion](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean) 的 `target_recovery_criterion`；[IndexedTargetSufficiency](../../../D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency.lean) 的 `indexed_target_sufficiency` 以完整依赖读出已供应为条件，不使未达到窗口可读；[ReachableBehaviorMinimality](../../../D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality.lean) 的 `finite_state_minimality` 另有有限载体、给定单子作用、可达性和相同外部未来行为前提，不能直接替代本章受守卫历史的实际数目。[ActualStrictHistoryCapacity](../../../D5/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity.lean) 的 `reached_prefix` 使用原树 Address/Reply/Recipe 合同，其不可变地址读不是 §30 的破坏性词积读；本章不转入那项观察权限。

已发表背景仅在对应范围使用：To，*Parikh Images of Regular Languages: Complexity and Applications*，[arXiv:1002.1464v2](https://arxiv.org/abs/1002.1464v2)，定理 3.1、4.1 和引理 4.2 处理有限自动机路径计数及半线性表示，循环须与基接受路径相接；八种边可取固定字母表，而仅计原两类字母不保留状态增量。该文不提供本章的破坏性拒绝关联数。Panteleev，*Preset Distinguishing Sequences and Diameter of Transformation Semigroups*，[arXiv:1412.0034v1](https://arxiv.org/abs/1412.0034v1)，§1 以已知有限 Mealy 转移／输出函数和未知初态说明区分任务，区分序列存在性并非自动；该文的序列长度界不是本章的保留记录容量界。通用有限编码、Fibonacci 增长和静态模型供给均为成熟／既有步骤；本章源特定结论为这些供应上的 repo-derived 普通数学推导，不主张文献优先权。

定义 50.1 的关系容量不是终端只输出一个初始目标的容量，也不是所有成功政策、所有规划算法、任意控制器状态或全部物理记忆的下界。当前物理源仍存在不意味着解码器获准检查它；显示共同锚终点还说明端点本身可以相同而记录关系不同。小码配不计费的旧动作、专属程序或指针不满足任务。未剪枝图下界不判定显示节点的赢性，碰撞检验未删节点也不证明后续取得成功。本章不恢复原树括号、叶地址、实际旧执行、绝对时间或物理空间；重造规范来源不是找回本人原树。没有给确定族发明概率律，没有物理时间定理、仪器符合性证明或新增观察端口。

## 追加锚（本行以下为增补区）
## 51. 完整单位历史纤维的静态容量与全上限合法恢复分类

本章保持 §§28–47 的原树、观察、同源记录和活上限合同，补充整个单位历史纤维的精确初始目标表及恢复阈值。Atomic359–360 的共同来源对应、§30 的行为商、§36 的原树保持边界、§§37–38 的永久碰撞原则、§§44、46 的终端尺寸取得和 §47 的全动作规划均作为既有接口复用，不改判其结论。以下证明只针对这个声明接口；静态目标表不提供在线的来源相关字段。

### 51.1 整个来源族、原始目标与唯一在线接口

**定义 51.1（完整单位族与恢复任务）。** 来源为自由有序非空二叉树

$$
\mathcal T\ni t::=\alpha\mid\beta\mid\langle t,t\rangle,
\qquad
\rho(\alpha)=\beta,\quad
\rho(\beta)=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\tag{TM.5101}
$$

原树的相等保留叶序和全部括号。组成为 $c(t)=(a,b)$，叶数为 $\lambda(t)=a+b$。沿用 Clifford 叶积 $E$，其原子像满足 $A^2=1$、$B^2=-1$、$AB+BA=1$；记 $E_i(t)=E(\rho^it)$、$W_3(t)=(E_0,E_1,E_2)$。对公开固定整数 $H\ge1$，声明

$$
\begin{aligned}
U_H&=\{t\in\mathcal T:1\le\lambda(t)\le H,\ W_3(t)=(1,1,1)\},\\
m(t)&=a+b,\qquad n(t)=a+2b,\qquad \lambda_2(t)=m+n,\\
q_H(t)&=
\begin{cases}
(0,E_0,m),&n>H,\\
(1,c,E_0,E_1),&n\le H<m+n,\\
(2,c,W_3),&m+n\le H.
\end{cases}
\end{aligned}
\tag{TM.5102}
$$

（TM.5102）的标签2使用 TM29 联合边界 $\eta=(\mathbf u,c)$ 的等价 $(c,W_3)$ 坐标。由 TM28.1 的唯一正规形，每个单位窗口的正规坐标都是 $(e,k,p)=(0,0,0)$，所以在 $U_H$ 上输出 $(2,c,(1,1,1))$ 可按固定坐标转换写成原 TM30 的 $(2,\eta)$。下文所有输出均指这个同一初始目标；该转换不增加来源观察字段。

这里 $U_H$ 包含满足条件的每个实际叶词的每种有序括号化。成员承诺是共同公开的族限定；每个输入另外供应同一个常量标签 $\star$。控制器共同初始化，只依据公开数据及实际已取得的记录，确定下一动作或停止并输出初始 $q_H(t)$。

在线动作恰为 §30 的三类：当前 `Read` 返回真实 $E$ 且不修改来源；尝试 $\rho$；尝试将一个已知实际非空正上下文 $v$ 接在当前树左侧或右侧。后两类先对整个候选检验叶数 $\le H$，等号接受；接受则更新来源，拒绝则保持来源且不给候选读数。记录包含公共输入、标签、动作及上下文身份、守卫响应和实际读值。任意已取得记录可无限保留，但它不供应额外的来源相关初始字段。没有在线成员测试、原树导航、独立尺寸读、时钟、费用读、变上限、复制、重置、来源逆操作或新鲜未知来源。已知上下文的供应、整候选守卫及实际读的表示均须另付成本。

在 $U_H\ne\varnothing$ 时，令 $\mathfrak P_H$ 为在每个输入上有限停止、正确输出初始 $q_H$ 的上述确定性协议集合。定义

$$
d_{\min}(U_H;H)=
\begin{cases}
\displaystyle\min_{\Pi\in\mathfrak P_H}\max_{t\in U_H}
\operatorname{dep}_\rho(\Pi,t),&\mathfrak P_H\ne\varnothing,\\
\infty,&\mathfrak P_H=\varnothing,
\end{cases}
\tag{TM.5103}
$$

其中深度只计真正接受的 $\rho$，所有拒绝和拼接仍分别计来源调用。空族不赋予这个恢复深度。最大值存在：固定 $H$ 的实际树族有限；单位族含 $\beta$，每次接受修改严格增叶，故每条合法路径的接受深度也有有限资源界。

### 51.2 既有共同来源对应与完整目标覆盖

**引理 51.2（Atomic360 单位纤维的实际应用）。** 令 $h=\lfloor H/4\rfloor$。整个 $U_H$ 的组成集合恰为

$$
\{(4r,4s):r,s\in\mathbb Z_{\ge1},\ r+s\le h\}.
\tag{TM.5104}
$$

对每个这样的参数，可取固定左结合括号的实际正词

$$
\omega_{r,s}=
\alpha^{2r-1}\beta^{2s}\alpha\beta^{2s-1}\alpha^{2r}\beta.
\tag{TM.5105}
$$

它的三窗口为 $(1,1,1)$，组成是 $(4r,4s)$；Atomic360.2 顺序下的八边次数为 $(r,r,r,r;s,s,s,s)$，全正、平衡且有效支撑连通。资源三项是

$$
m=4(r+s),\qquad n=4(r+2s),\qquad m+n=4(2r+3s).
\tag{TM.5106}
$$

证明。直接应用 [Atomic360.2–4](https://github.com/the-omega-institute/trureturing/blob/042193cace9d54a1f78c6b4cc460b8e0592553c0/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)：单位的唯一共同正规参数为 $(u,v,w,p,q)=(0,0,0,0,0)$，八边消元强制四条 $\alpha$ 边同数、四条 $\beta$ 边同数；连通和非空排除任一计数为零。该既有结论同时给出（TM.5105）的实际实现。原始叶数约束化为 $r+s\le h$，替换的既有组成更新给（TM.5106）。Atomic360.3 已证明该纤维的全部叶词恰是相应八边次数的全部 Euler 路标签，全部原树恰是这些词的全部有序括号化。因此此处复用的是整个纤维的充要对应，未以显示词替代来源域。$\square$

**定理 51.3（完整而无重复的初始目标表）。** 对所有 $H\ge1$，以下两部分组成一张完整目标表，每个初始目标恰有一行实际来源证书。

第一部分取

$$
1\le s\le S_h:=\left\lfloor\frac{h-1}{2}\right\rfloor,
\qquad 1\le r\le h-2s,
\tag{TM.5107}
$$

并输出 $\omega_{r,s}$、组成 $(4r,4s)$、单位三窗及目标

$$
\tau_{r,s}=
\begin{cases}
(2,(4r,4s),(1,1,1)),&2r+3s\le h,\\
(1,(4r,4s),1,1),&2r+3s>h.
\end{cases}
\tag{TM.5108}
$$

当上界小于下界时不输出行。第二部分令

$$
z_{\min}=\max\left(2,\left\lfloor\frac{h+3}{2}\right\rfloor\right),
\qquad z_{\min}\le z\le h,
\tag{TM.5109}
$$

输出 $\omega_{1,z-1}$ 及目标 $\tau_z=(0,1,4z)$。在 $h<2$ 时这两部分都空。

证明。任意实际 $t\in U_H$ 由引理 51.2 取得唯一正整数组成参数 $r,s$。由于三项资源都是四的倍数，$n\le H$ 等价于 $r+2s\le h$，$m+n\le H$ 等价于 $2r+3s\le h$。若 $n\le H$，组成保留于初始目标，参数恰落（TM.5107）；该目标唯一对应第一部分的一行。

若 $n>H$，初始目标只保留 $z=r+s$ 和单位首窗。固定 $z$ 时，$1\le s\le z-1$，而 $r+2s=z+s$ 的最大值是 $2z-1$。因此该大小的标签0目标存在，当且仅当 $2\le z\le h$ 且 $2z-1>h$，其整数解恰为（TM.5109）。该部分代表的 $r=1,s=z-1$ 实际达到最大值，故其 $n>H$，原始 $m=4z\le H$，证书和目标均正确。

每个输出代表属于 $U_H$。第一部分的不同组成给不同目标，第二部分的不同 $z$ 给不同大小目标，两部分由标签区分；所以表无重复。前两段将每个实际来源的初始目标唯一映到一行，证明 §47 所要求的完整覆盖

$$
\forall t\in U_H\quad\exists!i\quad q_H(t)=\tau_i.
\tag{TM.5110}
$$

这既覆盖所有实际叶词，也覆盖全部括号。由 TM30.2 和 TM47.2，任何在表中代表上正确的共同程序，在具有相等初始目标的每个实际来源上产生相同响应、输出和接受深度。因此可用这张表推理整个任务；在线运行仍作用于未知的原来源，未把它换成代表，也未恢复其括号。$\square$

### 51.3 精确计数和真正供应解码器的静态码

**定理 51.4（目标数与尖锐固定宽度码）。** 对所有整数 $H\ge1$，有

$$
N_H:=|q_H(U_H)|=\left\lfloor\frac{h^2}{4}\right\rfloor,
\qquad U_H=\varnothing\ \Longleftrightarrow\ H<8.
\tag{TM.5111}
$$

对非空情形，公开供应 $H$、（TM.5107–9）的表规则和下面的秩解码程序后，固定宽度精确静态目标码的最小位数为

$$
b_H=\lceil\log_2N_H\rceil=2\log_2H+O(1).
\tag{TM.5112}
$$

这里编解码的输入是一个已经确定的目标及其码，未供应未知来源的目标码取得器。

证明。由（TM.5104），最小实际单位组成是 $(4,4)$，故最小叶数为8，得到空族边界。$h\ge2$ 时，第一部分行数为

$$
P(h)=\sum_{s=1}^{\lfloor(h-1)/2\rfloor}(h-2s)
=\left\lfloor\frac{(h-1)^2}{4}\right\rfloor.
\tag{TM.5113}
$$

写 $h=2k$ 或 $h=2k+1$，该和分别为 $k(k-1)$ 或 $k^2$；第二部分行数分别为 $k$ 或 $k$，即 $\lfloor h/2\rfloor$。相加分别得 $k^2$ 或 $k(k+1)$，恰是 $\lfloor h^2/4\rfloor$。$h=0,1$ 直接得到零。

按 $s$ 递增、同一 $s$ 内 $r$ 递增排序第一部分，然后按 $z$ 递增排序第二部分。零基秩为

$$
\begin{aligned}
R_H(\tau_{r,s})&=(s-1)(h-s)+r-1,\\
R_H(\tau_z)&=P(h)+z-z_{\min}.
\end{aligned}
\tag{TM.5114}
$$

第 $s$ 行之前的总长度是 $\sum_{t=1}^{s-1}(h-2t)=(s-1)(h-s)$；因此第一式连续铺满 $0,\ldots,P(h)-1$，第二式连续铺满剩余秩直到 $N_H-1$。给定合法秩 $k<P(h)$，在 $1\le s\le S_h$ 内二分求最大满足 $(s-1)(h-s)\le k$ 的 $s$，然后求 $r=k-(s-1)(h-s)+1$，按（TM.5108）恢复目标。给定 $P(h)\le k<N_H$，直接求 $z=z_{\min}+k-P(h)$。目标中的单位窗口由公开族声明供应，无额外来源相关解码字段。输出 $b_H$ 位的秩二进制表示即可，未使用的位串明确定义为无效输入；$N_H=1$ 时使用唯一空位串。

任何固定宽度精确码必须把 $N_H$ 个不同目标送入不同位串，故 $2^b\ge N_H$。上述双射达到 $\lceil\log_2N_H\rceil$。$h=\lfloor H/4\rfloor$ 给渐近式。$\square$

端点如下；标签指初始 $q_H$，并不表示已执行替换后的来源。

| TM51 上限区间 | $h$ | $N_H$ | 非空静态位数 | 初始目标说明 |
|---|---:|---:|---:|---|
| TM51 $1\le H\le7$ | 0或1 | 0 | 不定义 | 空族 |
| TM51 $8\le H\le11$ | 2 | 1 | 0 | 仅 $(0,1,8)$ |
| TM51 $12\le H\le15$ | 3 | 2 | 1 | $(1,(4,4),1,1)$ 与 $(0,1,12)$ |
| TM51 $16\le H\le19$ | 4 | 4 | 2 | 保留组成 $(4,4),(8,4)$；标签0大小12、16 |
| TM51 $20\le H\le23$ | 5 | 6 | 3 | $(4,4)$ 的第二替换大小20成为标签2；另有下述四源障碍 |

特别地，$H=12$ 时 $n(\omega_{1,1})=H$，第一次替换接受；$H=16$ 时 $n(\omega_{2,1})=H$ 也接受；$H=20$ 时 $\lambda_2(\omega_{1,1})=H$，初始标签为2。所有四个上限剩余类使用同一 $h$ 判据，均保留等号。

### 51.4 小上限的合法原源执行与最小深度

**引理 51.5（复用终端尺寸取得）。** 在公开 $H$ 下，若入口未知实际尺寸为整数 $1\le M\le H$，则只用合法原子全 $\alpha$ 右拼接及守卫响应，可在至多 $\lceil\log_2H\rceil+1$ 次来源调用内取得入口 $M$，不用 `Read` 或 $\rho$。协议结束时当前尺寸是 $H$，包含最后一次单叶拒绝。

证明。这是 TM44.5 的（TM.4419–20）终端算法的应用。初始化 $l=0,u=H,U=0$，维持

$$
l<M\le u,\qquad U=H-u,\qquad
\lambda(t_{\rm cur})=M+U.
\tag{TM.5115}
$$

只要 $u-l>1$，置 $c=\lfloor(l+u)/2\rfloor$，尝试一次已知非空固定括号的 $\alpha^{u-c}$ 右拼接。整候选大小是 $M+U+u-c=M+H-c$，故真实响应为接受当且仅当 $M\le c$。接受时令 $u=c$，并使 $U$ 增加 $u_{\rm old}-c$；拒绝时仅令 $l=c$。两种更新都保持不变量，区间宽度至多减半向上取整。最多 $\lceil\log_2H\rceil$ 次后 $u-l=1$，整数性给 $M=u=H-U$，当前尺寸为 $H$。再尝试单叶 $\alpha$，整候选 $H+1$ 被拒绝。

若 $M=c$，接受是准确的等号响应；若 $M=H$，所有探测都拒绝而 $U=0$，仍准确输出入口 $M$。被拒宏不拆成逐叶动作，未返回候选读，也未查询来源尺寸。所有整数都来自公开 $H$ 和真实动作记录。$\square$

**定理 51.6（小上限的匹配协议与深度下界）。** 对 $8\le H\le15$，$d_{\min}(U_H;H)=0$；对 $16\le H\le19$，$d_{\min}(U_H;H)=1$。匹配协议不作 `Read`，最坏来源调用不超过 $\lceil\log_2H\rceil+2$；各分支输出原始目标。

证明。$8\le H\le11$ 时只存在一个初始目标，直接输出 $(0,1,8)$，无来源调用。$12\le H\le15$ 时，实际组成参数满足 $r+s\le3$。$(r,s)=(1,1)$ 的原始大小是8，目标是 $(1,(4,4),1,1)$；$(1,2),(2,1)$ 的原始大小都是12，且 $n>H$，目标同为 $(0,1,12)$。立即运行引理 51.5，按取得的入口大小8或12解码原目标。接受拼接可改变当前窗口或分层；输出关联依靠已取得的入口大小，不靠终端当前 $q_H$。深度为零，调用至多 $\lceil\log_2H\rceil+1$。

对 $16\le H\le19$，先尝试一次 $\rho$，在任何拼接之前进行。完整组成参数满足 $r+s\le4$；$n\le H$ 恰发生在 $(r,s)=(1,1),(2,1)$，接受后的入口大小分别为12、16，原始目标分别为 $(1,(4,4),1,1)$、$(1,(8,4),1,1)$。接受后运行终端取得，用12或16区分这两个原始目标。首次 $\rho$ 拒绝时，来源未变；剩余目标为标签0的大小12或16，运行终端取得后输出 $(0,1,M)$。这覆盖全部六种组成以及按定理 51.3 覆盖的全部实际来源。每条路径至多一次接受 $\rho$，所有动作均由当前真实响应选择，调用至多 $1+\lceil\log_2H\rceil+1$。

还需排除零接受深度。取实际来源 $X=\omega_{1,2}$、$Y=\omega_{2,1}$，二者共同 $m=12$、$W_3=(1,1,1)$，但 $n_X=20$、$n_Y=16$，故在 $16\le H\le19$ 其初始目标不同。假设存在每条输入路径都不接受 $\rho$ 的成功协议。在每个共同历史之前，二者尚未接受替换，只附了同一批已知上下文；当前大小同为 $12+U$，当前读为同一有序已知左、右因子夹着单位。任何上下文守卫给同一响应，包括任意混合字母、任意大小、任意一侧及所有拒绝。若此时尝试 $\rho$，其下一大小为 $20+V$ 和 $16+V$。协议的零接受假设强制较小者 $Y$ 拒绝；于是较大者 $X$ 也拒绝。拒绝和任意 `Read` 保持共同记录。按动作长度归纳，控制与完整记录始终相同。有限停止迫使二者输出同一值，不能同时正确。故最坏深度至少为1，匹配协议达到该界。$\square$

### 51.5 所有较大上限的真实四源障碍

**定理 51.7（全正上下文、任意记录和控制下的不可恢复）。** 对每个整数 $H\ge20$，一个常量标签的 TM30 协议不能在整个 $U_H$ 上有限正确恢复初始 $q_H$，即 $d_{\min}(U_H;H)=\infty$。此结论允许任意已取得记录存储、任意确定性自适应控制和精确当前读，覆盖所有允许的正上下文及两侧拼接。

证明。置

$$
r=\left\lfloor\frac{H-12}{4}\right\rfloor\ge2,
\qquad H=4r+12+\delta,\qquad 0\le\delta\le3.
\tag{TM.5116}
$$

选择固定括号的四棵实际来源，记名字 $C,A_*,B_*,D_*$；星号避免与 Clifford 原子像 $A,B$ 混同。

| TM51 实际来源 | 正词 | 组成 | $m$ | $n$ | 初始标签 |
|---|---|---|---|---|---|
| TM51 $C$ | $\omega_{r,1}$ | $(4r,4)$ | $4r+4$ | $4r+8$ | 1 |
| TM51 $A_*$ | $\omega_{r-1,2}$ | $(4r-4,8)$ | $4r+4$ | $4r+12$ | 1 |
| TM51 $B_*$ | $\omega_{r+1,1}$ | $(4r+4,4)$ | $4r+8$ | $4r+12$ | 1 |
| TM51 $D_*$ | $\omega_{r,2}$ | $(4r,8)$ | $4r+8$ | $4r+16$ | 0 |

所有参数都正，所有 $m\le H$，由引理 51.2 得四源全部实际属于 $U_H$。八边次数全正，所以没有假定未证可实现的资源元组。$C$ 的 $m+n=8r+12>H$，另外三源的 $m+n$ 更大；其初始目标两两不同，前三者保留不同组成，第四者有不同标签。关键等式为

$$
m_C=m_{A_*},\qquad
m_{B_*}=m_{D_*}=n_C,\qquad
n_{A_*}=n_{B_*}\le H<n_{D_*}.
\tag{TM.5117}
$$

假设有成功协议。先只看 $C,A_*$，二者初始大小和首窗相同。首次尝试 $\rho$ 之前，它们对每次 `Read` 以及每个正上下文的左／右拼接都给相同响应，因此动作身份、上下文身份、既有读历史和控制完全相同。读数的相同性来自同一已知因子的实际有序乘积，未交换非交换因子。若该前缀有限停止，二者得到同一输出而原始目标不同；若永远没有首次 $\rho$，则违反逐点有限停止。因此有一个有限共同前缀以首次 $\rho$ 尝试结束。

记此之前全部接受上下文对当前、下一叶数的累计贡献为 $U,V$。对每个实际正上下文，设 $c(v)=(a_v,b_v)$，则

$$
d_0(v)=a_v+b_v\ge1,\qquad
d_1(v)=a_v+2b_v,\qquad
d_0(v)\le d_1(v)\le2d_0(v).
\tag{TM.5118}
$$

故 $0\le U\le V\le2U$；左、右位置不改变这些增量，拒绝贡献为零。这里包含任意实际混合正上下文，不限制为全 $\alpha$。

若首次 $\rho$ 在 $C$ 上拒绝，则 $n_C+V>H$，而 $n_{A_*}>n_C$，所以 $A_*$ 也拒绝。二者有相同已取得记录、相同当前大小 $m_C+U$ 和相同当前 $E$，且当前都为标签0；其当前 $q_H$ 相同而初始目标不同。由 TM30.2、TM38.1 的永久碰撞，任何共同延续都不能成功。成功协议因此必须让 $C$ 接受，得到

$$
n_C+V\le H.
\tag{TM.5119}
$$

该条件还强制 $B_*,D_*$ 沿同一个完整前缀运行。用前缀长度归纳：假设此前动作和响应相同；每个在 $C$ 上接受的上下文，在接受后的累计当前贡献 $U'$ 满足 $U'\le V$，于是 $B_*,D_*$ 的候选大小 $n_C+U'\le H$，也接受。每个在 $C$ 上拒绝的上下文，在具有同一贡献且原始大小更大的 $B_*,D_*$ 上也拒绝。当前读相同，因为四源的初始首窗都是单位，同一有序已知因子包在它们外侧；因此下一控制也相同。归纳覆盖任意数量的读、拒绝、两侧拼接和依赖完整记录的分支选择，四源到达同一首次 $\rho$ 指令。

若这次 $\rho$ 在 $A_*$ 上接受，由 $n_{A_*}=n_{B_*}$ 可知 $B_*$ 也接受。二者拥有相同整份记录，替换后的当前大小同为 $n_{A_*}+V$；当前 $E$ 也是同一变换后已知左因子乘原始 $E_1=1$ 再乘同一右因子。其下一大小分别为原始 $m+n+U+V$，都严格大于 $H$。故当前均为标签0，当前 $q_H$ 相同，两个不同初始目标永久合并。

若首次 $\rho$ 在 $A_*$ 上拒绝，则 $B_*$ 同样拒绝；$D_*$ 因 $n_{D_*}>H$ 也拒绝。$B_*,D_*$ 有相同整份记录、相同当前大小 $m_{B_*}+U$ 和相同当前 $E$，当前均为标签0，另一次永久合并出现。无论 $A_*$ 接受还是拒绝，协议至少在一对实际输入上无法同时有限正确停止。

以上三种情况穷尽首次 $\rho$ 的所有响应。永久合并之后任意未来动作都受同一个 TM30 行为商支配；存储更多既有记录或对读做精确算术不能把同记录分开。成功的全 $U_H$ 协议限制到这个实际四源族也应成功，矛盾。$\square$

此处障碍复用 TM37.2 的首次替换行列约束及 TM38.1–4 的初始目标配对原则；新结论是它们在完整单位族上的实际全上限阈值，不是一个新的通用不可逆识别原理。

在 $H=20$，取 $r=2$，四个显示词及资源为

$$
\begin{array}{c|c|c}
\text{来源}&\text{实际叶词}&(m,n)\\ \hline
C&\alpha^3\beta^2\alpha\beta\alpha^4\beta&(12,16)\\
A_*&\alpha\beta^4\alpha\beta^3\alpha^2\beta&(12,20)\\
B_*&\alpha^5\beta^2\alpha\beta\alpha^6\beta&(16,20)\\
D_*&\alpha^3\beta^4\alpha\beta^3\alpha^4\beta&(16,24).
\end{array}
\tag{TM.5120}
$$

直接首次替换的响应是接受、接受、接受、拒绝；$A_*,B_*$ 恰在大小20接受，之后共同当前目标 $(0,1,20)$，但初始目标分别保留 $(4,8)$、$(12,4)$。若先在四源上共同右接一个 $\alpha$，再替换，则响应变为接受、拒绝、拒绝、拒绝；$B_*,D_*$ 共同当前目标 $(0,A,17)$，但初始目标分别为 $(1,(12,4),1,1)$、$(0,1,16)$。先左接 $\beta$ 或先左接 $\alpha\beta$ 也给实际混合／侧向控制，由相同有序因子证明处理。$H=20$ 的 $\omega_{1,1}$ 同时有合法第二替换，说明某些来源可达到深度2，并不修复四源的统一不可恢复。

**推论 51.8（完整单位族的精确分类）。** 在定义 51.1 的同一声明接口下，所有非空情形恰满足

$$
d_{\min}(U_H;H)=
\begin{cases}
0,&8\le H\le15,\\
1,&16\le H\le19,\\
\infty,&H\ge20.
\end{cases}
\tag{TM.5121}
$$

证明。定理 51.6 给两个有限区间的匹配上下界，定理 51.7 给整个剩余区间的实际障碍。$\square$

跨 $H$ 的比较同时改变了声明族 $U_H$ 和目标 $q_H$，不是给一个固定未变任务增加资源后却降低能力的陈述。特别是某些较小上限时已经合并的标签0目标，在较大上限时重新成为须区分的组成目标。

### 51.6 补充关系的静态可用性与同源生产边界

**命题 51.9（精确保持原源只能输出常量）。** 固定一个非空 $U_H$。若来源无关初始化的确定性 TM30 程序在每个输入上有限停止，结束时保留精确的初始原树，则它在整个 $U_H$ 上只能输出常量。因此它不能为定理 51.7 的四源生产非恒定补充标签。

证明。复用 TM36.10 的原树保持原则，并在本族中直接检查前提：引理 51.2 给每个来源至少四个 $\beta$。接受正拼接严格增叶；接受 $\rho$ 也严格增叶，因为增量等于当前 $\beta$ 数，而在替换或正拼接后该数保持正。允许动作从不减叶，故精确保留原树排除每次接受修改。程序只可能读不变的 $E_0=1$，或得到拒绝。共同初始化后，按每个记录前缀归纳，动作、身份、拒绝、读值和输出均相同。$\square$

**命题 51.10（显示四源的尖锐条件补充字母表）。** 对每个 $H\ge20$，定理 51.7 所显示的四源族，在补充标签确由同一未修改初始来源供应、且在线阶段仍只用 TM30 动作的条件下，最小标签字母表大小恰为2。整个 $U_H$ 在同样的实际同源供应条件下有 $h-1$ 个初始大小标签的充分上界；不主张这是完整 $U_H$ 的最小字母表。

证明。一个标签不够，已由定理 51.7 对四源证明。供应两值标签：$C,A_*$ 为第一类，$B_*,D_*$ 为第二类，即表示该四源中的两个初始大小行。第一类立即尝试纯 $\rho$，二者都接受；随后由引理 51.5 取得接受后入口 $n$，因 $n_C\ne n_{A_*}$ 而区分原始目标。第二类立即尝试纯 $\rho$，$B_*$ 接受、$D_*$ 拒绝，守卫位已区分原始目标。接受等号 $n_{A_*}=n_{B_*}\le H$ 完整保留；全部操作都在那一棵被供应标签的实际原来源上执行，最坏接受深度为1，来源调用至多 $\lceil\log_2H\rceil+2$。故两值足够且必要。

对整个 $U_H$，供应初始 $z=r+s\in\{2,\ldots,h\}$，共有 $h-1$ 个可能标签。先尝试 $\rho$；拒绝时立即输出 $(0,1,4z)$。接受时入口大小为 $N=n\le H$，终端取得给这个 $N$；已知初始 $M=4z$，于是 $b=N-M$、$a=2M-N$。用 $M+N\le H$ 判断原始标签2或1，单位窗口由族承诺供应，输出原始 $q_H$。这证明条件上界而未证明最小性。$\square$

上述补充标签需要同初始来源的真实供应关系，例如来源构造阶段确实持有该原树的可解析档案，离线计算其组成、确认 $W_3=(1,1,1)$ 并把标签与后来被执行的这棵实际原树配对；档案的取得、材料、解析、配对和认证全部另计。仅有一个同目标的规范代表、同名树句柄、某棵别的树的组成或未证明对应的记录，不满足这个条件。该条件定理没有给未知运行树增加大小或导航端口，也没有让命题 51.9 的保持原树程序生产该标签。常量标签的原任务仍受定理 51.7 约束。精确的全 $U_H$ 最小补充字母表、紧致总调用和最小总记忆仍未在此确定。

### 51.7 有效供应、位工作、输出和物理成本的分离

**命题 51.11（充分算法表示与成本坐标）。** 令 $B_H=\lceil\log_2(H+1)\rceil$。以下是上述构造的充分上界，均不作为最优总成本或物理时间定理。

证明。目标表程序只须公共 $H$、两个整数循环、六段词公式（TM.5105）、八边证书和目标判据，其统一程序描述长度独立于 $H$，另输入 $O(B_H)$ 位的 $H$。逐行以增量计数求 $r,s,m,n,m+n$、标签和八边数，各次加法、比较及由小常数倍的运算耗 $O(B_H)$ 位工作；整个表有 $N_H=\Theta(H^2)$ 行，故紧凑编译及每行算术／证书核对有充分 $O(H^2B_H)$ 位工作、$O(B_H)$ 可变迭代器位。完整覆盖依赖定理 51.3 的证明，不是把逐行认证当成覆盖。紧凑显式输出的词段指数、目标和证书共 $O(H^2B_H)$ 位，输出存储不算入迭代器空间。

单目标秩用普通整数乘法可在 $O(B_H^2)$ 位工作内求出；解码二分至多 $O(B_H)$ 次，每次前缀计算用 $O(B_H^2)$ 位工作，故充分解码界为 $O(B_H^3)$ 位工作、$O(B_H)$ 工作位。它们的公共解码公式已在定理 51.4 明确供应；静态码容量没有支付未知来源的目标取得。

每个显示代表的展开词恰有 $4(r+s)\le H$ 个叶，固定括号化用 $O(H)$ 个字面树符号；展开全部行及树证据至多用 $O(H^3)$ 个符号。真实来源材料、树构造、保存、发送和证书访问各自付费。一个简短八边证书保证存在同一实际来源，不意味着这些树已经物理构建。对确实供应的字面原树档案，大小为 $L$ 的树可保序遍历，按 TM28／Atomic359 的固定整数状态更新求三窗及组成，取得成员判定和初始目标；$O(L\log(L+1))$ 位工作和 $O(L\log(L+1)+B_H)$ 位工作区是一个保守充分界，包含最坏深树的遍历栈。此处计算只作用于实际供应的档案；它没有对未知运行树提供遍历权，亦不认证未验证的未知物理仪器。

小上限正协议不用 `Read`，只用零或一次 $\rho$ 尝试、至多 $\lceil\log_2H\rceil$ 个原子全 $\alpha$ 宏和最后一次单叶拒绝。终端取得入口为 $M$ 时，接受的填充材料恰为 $H-M$；全部尝试的宏材料保守不超过 $H\lceil\log_2H\rceil+1$，包含被拒宏。程序的分支位、$l,u,U$ 及算术有充分 $O(B_H)$ 可变控制位、$O(B_H^2)$ 位工作；字面存储全部紧凑动作长度及响应可用 $O(B_H^2)$ 位。展开的上下文身份、整份物理记录、记录输出和来源本体分别计费。原始大小 $M_0$ 与终端入口 $M$ 不可混同：首次 $\rho$ 接受时 $M=n(t)$；原树已有的替换产物和新附材料也必须分别核算。

对于任意规划，直接复用 TM47 的认证初始表、全动作图和表示费用；本章不重做全上限编译器或声称多项式规划界。对于实际执行，算法位工作、静态计划及字典、紧凑／展开输出、迭代器／档案空间、来源材料、真实调用、守卫实现、替换内部代价、证书获取、调度、读值解析及物理费用均是不同坐标。调用原子性不保证单位持续时间；没有墙钟、物理空间、可共享证书句柄或未知仪器符合性的结论。$\square$

### 51.8 来源对应与适用边界

以下引用固定于提交 `042193cace9d54a1f78c6b4cc460b8e0592553c0`；它们的假设与本章对应如下。

- [Atomic §§355–357、359–360](https://github.com/the-omega-institute/trureturing/blob/042193cace9d54a1f78c6b4cc460b8e0592553c0/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)：叶积及忠实矩阵、窗口后继、联合正规形、八边充要条件、全部 Euler 词／括号对应和单位正词供给。本章直接使用这些结论，不把一般有效像编译、Euler 构造或表示变换计为新增贡献。
- [TM §§28–30、36–38、44、46–47](https://github.com/the-omega-institute/trureturing/blob/042193cace9d54a1f78c6b4cc460b8e0592553c0/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)：整数更新、原动作守卫、行为核、源保持生产边界、首次替换行列限制、原始目标配对、终端二分填充、全正上下文动作对应及完整认证表。这里的完整单位表使既有 TM47 输入的覆盖条件具体成立；不授予实际未知行查询。
- [TargetRecoveryCriterion.target_recovery_criterion](https://github.com/the-omega-institute/trureturing/blob/042193cace9d54a1f78c6b4cc460b8e0592553c0/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)：该结论在非空状态空间上将目标因子化等价于同观察纤维内目标恒定及碰撞集为空。它供应抽象判据，不供应合法破坏性取得器。
- [IndexedTargetSufficiency.indexed_target_sufficiency](https://github.com/the-omega-institute/trureturing/blob/042193cace9d54a1f78c6b4cc460b8e0592553c0/D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency.lean)：该结论要求一个已供应的索引读出家族及其完整依赖读出；不证明这些读能在同一不断修改的原源上联合取得。
- [ReachableBehaviorMinimality.finite_state_minimality](https://github.com/the-omega-institute/trureturing/blob/042193cace9d54a1f78c6b4cc460b8e0592553c0/D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality.lean)：该结论要求有限载体、幺半群动作、候选可达性和相等完整外行为，给未来行为商的最小性；当前行为相同不自动恢复不同初始目标。

文献背景仅在下列明确条件下使用：

- [Lundholm–Svensson，Clifford algebra, geometric algebra, and applications，arXiv:0907.5356v1，§§2.1–2.3](https://arxiv.org/abs/0907.5356v1) 的商代数满足 $v^2=q(v)$、$vw+wv=2\beta_q(v,w)$，乘法结合，标准等级对合保持乘法。它支持本章沿用的代数约定，未给本树族的恢复阈值。
- [Panteleev，Preset Distinguishing Sequences and Diameter of Transformation Semigroups，arXiv:1412.0034v1，页1–2](https://arxiv.org/abs/1412.0034v1) 明确假设已知有限确定性 Mealy 转移／输出表，输入和输出字母表有限，转移、输出为全函数，并区分成对可辨与一个统一预设区分序列。这里不引入其全输入、复位或序列长度界；成对行为商辨识不能代替本章的合法自适应初始目标取得。
- [van den Bos–Vaandrager，State Identification for Labeled Transition Systems with Inputs and Outputs，arXiv:1907.11034v2，定义12–20、图3、页10–12](https://arxiv.org/abs/1907.11034v2) 要求测试与给定 suspension automaton 的可用输入和全部输出相容，按完整可观察终止轨迹定义区分；图3展示每种初始选择都会合并必要状态对而不存在统一自适应区分图。它提供成熟的破坏性识别背景，本章四源仍单独证明实际入族、全部正上下文守卫及原始目标碰撞；不转入 suspension 语义或另加测试端口。

本章结论是上述既有接口上的综合推导：完整单位族的唯一目标覆盖、精确计数／秩、深度0／1／不可恢复阈值，以及显示四源的条件两值补充关系。没有假定不可达来源存在；实际部署另须供应来源的族成员认证、上下文材料／原子守卫、读表示和同源标签／档案的真实符合性；数学目标表无法给未知仪器生产这些条件。

单位三窗连同全部代数后继历史是一个固定观察值，却可对应 $N_H$ 个不同的原始资源行为目标。小上限时，真实守卫记录足以恢复该目标；更大上限时，来源资源、行动与记录必须联合保留原始目标关联，否则合法动作会造成永久合并。这个分类推进持续问题：在固定声明接口下，观察、边界、资源和合法记忆何时能确定彼此；静态可表示、行为可辨、实际可取得和同源可认证各有独立条件。未恢复原始括号、实际旧轨迹、物理空间或标定时间；未供应统计律、来源复制／重置／逆操作、共享证书权限、未知仪器符合性、其它观察接口的取得结论或完整长期目标的终结。

## 追加锚（本行以下为增补区）

## 52. 付费准备的同核取得分离与 TM30 已取得记录桥梁

**本批导航。** 本章以不可变输入 `40be8185113f7ac5abd5cbf534b844b8014fa9e3` 为基线，接续 TM30 的实际来源与 TM31 的初始目标，补充一个来源特定的否定结论：完整初始行为核仍为 $\ker(q_H)$，并不足以保持统一取得初始 $q_H$ 的能力。反例只公开真实准备写入的发生，不把未知商值或实际表行供应给观察者。本章随后将既有因子化、完整标签与策略运输框架用于一个充分的、有效且在线的已取得记录合同，给出双向普通证明，并明确全有限请求语言的资源条件。TM31 的原不可能性、已知尺寸解码与调用界均作供应复用，不重新证明；不使用任何 TM50/51 草稿或结论。本章不改判、替换或改写早先理论。

**约定 52.1（来源、历史与初始目标）。** 固定公开整数 $H\ge1$。$\mathcal T$ 是由两种叶 $\alpha,\beta$ 和有序二元构造 $\langle s,v\rangle$ 生成的非空自由树；$\mathcal T_H=\{t:1\le\lambda(t)\le H\}$。初始实际树为 $t_0$，当前实际树为 $t$，二者通过同一准备发生绑定，不能在证明中更换来源。替换逐构造满足 $\rho\alpha=\beta$、$\rho\beta=\langle\beta,\alpha\rangle$、$\rho\langle s,v\rangle=\langle\rho s,\rho v\rangle$。$c(t)=(a,b)$ 数两种叶，$\lambda_0=a+b$、$\lambda_1=a+2b$、$\lambda_2=2a+3b$，$E_i(t)=E(\rho^it)$。$E$ 是同一指定 Clifford 来源的结合叶积，$A=E(\alpha)$、$B=E(\beta)$、$S=BA$，满足 $A^2=1$、$B^2=-1$、$AB+BA=1$。不是任意环境三元组都属于这个实际来源。

宏请求语言恰为 $\mathrm{Read},\rho,L_v,R_v$，其中 $v$ 是已知、实际、非空的有序上下文，身份及左右顺序保留。Read 返回当前 $E(t)$，来源不变；其余请求先检验整个候选的叶数，候选在 $\mathcal T_H$ 中则提交并返回 accept，否则返回 reject、来源不变且不发表候选 $E$。拒绝是一次实际响应，不能删除。初始记录、公开参数、程序和控制初始化共同。原 TM30 没有树导航、尺寸、时钟、费用、变阈值、复位、未知来源复制、新鲜未知来源或逆向解接端口。

令 $h$ 为这个发生实际取得的原宏记录，逐项包括请求、参数、上下文身份与实际响应。控制器自己的确定性局部状态由共同初始化和 $h$ 导出，允许真实保留更长档案。目标始终为

$$
\tau_H(t_0)=q_H(t_0),\qquad
q_H(t)=
\begin{cases}
(0,E_0(t),\lambda_0(t)),&H<\lambda_1(t),\\
(1,c(t),E_0(t),E_1(t)),&\lambda_1(t)\le H<\lambda_2(t),\\
(2,\eta(t)),&\lambda_2(t)\le H.
\end{cases}
\tag{TM.5201}
$$

这里 $\eta$ 是 TM29 的实际组成与三窗边界；窗口与唯一整数正规坐标等价。协议取得 $\tau_H$ 指一个有效、共同初始化、确定性记录控制器在每个允许的 $t_0$ 上有限停止并输出该初始值。有限停止包括所采用的本地计算、记录、转换与输出，而不只计来源调用。原 TM31 的语义证明在其声明表示接口内提供所需控制；本章使用精确有效 Read 表示时明列其供应条件。

### 52.1 同一实际树的付费准备发生

**定义 52.2（三值节点输入与声明的观察合同）。** 对实际树定义私有三值 preorder 包

$$
C(\alpha)=[\mathtt a],\quad C(\beta)=[\mathtt b],\quad
C(\langle s,v\rangle)=[\mathtt n]C(s)C(v).
\tag{TM.5202}
$$

包保留全部括号与叶序。它由输入所有者供应给来源所有者 P，内容就是所选择的实际 $t_0$ 的构造包；A 不得读包载荷。公开 $R=2H-1$ 个私有节点单元，单元字母表为 $\{\mathtt{blank},\mathtt a,\mathtt b,\mathtt n\}$，可用两位表示。先实际构造、清空这 $R$ 个单元。输入发生随后对 $C(t_0)$ 的每个 token 实际执行一次私有 WRITE，顺序地址为 $1,2,\ldots$，结束时实际 SEAL。未写单元保持 blank；没有附加的未知行号或 $q_H$ 输入。P 的来源就是该包的解码树，后续接受更新也替换此来源包。

扩张合同 $M_H^{\mathrm{prep}}$ 声明 A 可以接收 WRITE 的发生、地址、相同单位 tick/fee 标签及 SEAL；token 值、节点种类、内部匹配位与私有源寄存器不在 A 的视图中。每个 token 的公开相位和派发模板相同。固定的构造、清空、验证与封存标签另外保留。准备中只允许有限本地计数、记存和复制已交付的事件；首次来源请求在 SEAL 后，未封存时统一 unavailable。准备不是控制器可反复调用的来源请求，没有中断后再询问新源或撤销输入的菜单。需要在准备中允许本地停止时，其选择只依赖当时已交付的事件，且不产生来源响应。两种解释均保下面的同核结论。

这明确改变了观察合同。WRITE 是付费输入工作的公开发生，并非原 TM30 增添一个 size 请求；原宏请求菜单和全来源家族保持。字面费用来自这些实际单元操作，不能把 $f(q_H)$ 直接命名为一个收费 oracle。P 持有完整来源包，不意味着 A 获得树导航权。

**命题 52.3（实际付费分离）。** 对每个固定 $H\ge1$，定义 52.2 可以接上一个有效、有限进展、同实际树的理想付费服务，使所有声明可见的后续准备与服务标签只依赖公开请求及原响应。由此得到的完整初始行为核恰为 $\ker(q_H)$；然而 $M_H^{\mathrm{prep}}$ 在整个 $\mathcal T_H$ 上有一个统一取得初始 $q_H$ 的协议。对 $H\ge9$，这一能力严格超出原 TM30。这里只构造一个故意扩张观察的理想反过程，不声称给出保持原取得能力的付费实现，也不声称原生硬件或物理符合性。

**证明。** 先补足反过程的实际服务和费用，以免将正确后缀或中性日程当作未供应的 oracle。以下有限表扫描仅是这个来源特定反例的辅助存在构造，不是新的通用编码、表或电路成果。

从两棵一叶树开始，按叶数依次生成全部有序分裂 $n=i+(n-i)$ 及已生成左右树，得到 $\mathcal T_H$ 的无重复构造枚举。每层和层数有限；构造包由式（TM.5202）生成。相同语法只能来自同一根的左右分裂，故覆盖且可决定相等。对每棵树递归计算 $\rho$ 候选和 Read 叶积，逐构造计数整个候选，不作局部先接受；超上限候选仅用于私有 guard，输出只保留 reject 与旧包。约定 $\mathcal T_0=\varnothing$。对 $v\in\mathcal T_{H-1}$ 的左右拼接逐棵同样计算。Read、$\rho$、两侧拼接的全部行由这些实际构造生成，行中的 successor 是实际包，不是自由选择的 profile。生成和写入每行、公开程序、常量及工作单元均付费，且在未知输入选定前执行。不存在免费保有表或实际输入行的假设。

计算 $E$ 使用所引来源的有限整数代数：$1,S,A,SA$ 为固定基，$S^2=S+1$、$ASA=1-S$，逐叶乘 $A$ 或 $B=SA$ 即得精确四整数。负整数和符号用有限二进字符串。枚举完这些有限行后，顺次扫描它们，实际取得最大载荷位长，给各字段公开共同宽度。宽度、代码、常量表和初始化由这项终止算法生产并计费，不能用“有有限最大值”替代它。Read 的公开包为这些整数的固定忠实编码，语义仍为原 $E$；包与 $E$ 双向有效且一一对应，因而只是值表示。若将本论证用于一个原 Read 实际序列化接口，必须先供应其忠实精确表示；一个未指定算法的精确实数符号或带噪读数不满足本条件。

每个服务私下从 $R$ 个单元读取当前包，逐行比较全部位，对每一行都执行相同宽度的相等与按位选择，累积匹配的原响应与 successor 包。相等可由逐位 XOR、NOT、AND 的固定链计算，选择位为 $(b\wedge x)\vee(\neg b\wedge y)$；两候选都算，不通过私有匹配位决定分支或访问地址。每行字段完整扫描，最终也完整写回 $R$ 个来源单元和固定宽度响应单元，未改变或拒绝时写回旧值。公开 PC、地址、tick、费用和相位顺序因此由公开表长与请求决定，实际未知行没有公开地址。每个布尔求值、位读写、派发、PC 更新、单元构造及交接都算实际工作的一个已声明理想单位；选择的语义没有递归另加一个计费器。构造日程是有限列表，剩余指令数严格下降，所以每次服务必达响应及交付切面。

已知实际上下文的材料先由上下文所有者付费形成并交付，其完整身份及语法是请求的公开参数。通过递归解析其有限构造包取得 $d=\lambda(v)$；这项扫描的标签、成本只依赖已公开材料。当 $d\ge H$，每个非空当前来源都必须拒绝；仍实际解析材料、保留请求和 reject，完整写回旧源，不读取拒绝候选的 $E$。当 $d\le H-1$，在已生成的全部实际上下文包中也以固定扫描取得匹配，再扫描完整联合表。即使 $H=1$ 的上下文表为空，大上下文分支仍覆盖所有非空 $v$。任意大的公开上下文只使该次输入处理与材料费用增大，没有改成一个有界参数语言。验证初始包同样扫描全部有效包，所有允许输入的 valid/SEAL 相同；无来源相关公开错误或提前退出。私有源包承载实际树的表示关系，接受时输出表里由同一原候选生成的包，拒绝和 Read 时解码树不变，归纳得整个运行的同源正确性。

至此，服务的额外公开标签仅由公共数据、请求和原响应导出，任意有限请求串都可继续；记录与精确发生计数采用付费可扩展存储，分配与复制按实际已公开记录确定。固定 $H$ 的表/源核心有限，不声称整个不断保留记录的配置空间有限。这个有限算法服务的构造费可以极大，不会被解释为实现最优。它已经供应本命题需要的理想反过程后缀，尚不是对其他生产者的符合性认证。

现计准备节点写入数。叶有一节点；若左右有 $m_s,m_v$ 片叶，归纳给

$$
|C(\langle s,v\rangle)|
=1+(2m_s-1)+(2m_v-1)=2(m_s+m_v)-1.
\quad |C(t_0)|=2\lambda_0(t_0)-1.
\tag{TM.5203}
$$

parser 读首 token，叶立即结束，$\mathtt n$ 递归取接续的两棵树，唯一确定消费位置；按构造归纳，解析 $C(t)$ 恰回到 $t$ 并耗尽该包。这保证完整实际语法供应，而非来源无关的值列表。A 真实接收这些发生后，自己付费递增记录计数 $L$，在 SEAL 后计算

$$
m=(L+1)/2=\lambda_0(t_0).
\tag{TM.5204}
$$

$L$ 是这次实际事件记录的长度，不是表中预置的来源值。选择两位单元的节点 token 后，唯一新增的公开重复事件就是必需的实际写入，没有新增 Read countdown 或额外来源查询；这是本文选用的节点输入构造。没有宣称每种物理编码中的最小位成本，尤其不把三值节点数 $2m-1$ 与二进 prefix 编码的 $3m-1$，或逐叶 Read 的 $m$ 个块混为一数。

定义 $\ell(0,E,n)=n$、$\ell(1,(a,b),E_0,E_1)=a+b$、$\ell(2,\eta)=a+b$。式（TM.5201）给

$$
\lambda_0(t)=\ell(q_H(t)).
\tag{TM.5205}
$$

故相同初始 $q_H$ 有相同 $L$，完整准备地址、tick、fee、availability 与 SEAL 相同。TM30.1 给相同当前 $q_H$ 的共同请求有相同响应和相同后继 $q_H$；上述服务中性又给完整公开后缀相同。本地计数、记录、复制、预算比较和停止均在相同输入上执行。对每个有限公开发生与来源调用归纳，两初始 $q_H$ 相同的来源在任意共同有效自适应控制器下有同一完整视图和选择。反向，TM30.2 的每个原有限区别脚本仍可在封存后执行，并可忽略准备记录；原请求不会因次数而禁用，所以初始 $q_H$ 不同者仍可分离。因此是精确核相等，而非仅一侧包含：

$$
\ker\operatorname{Beh}(M_H^{\mathrm{prep}})
=\ker(q_H)
=\ker\operatorname{Beh}(M_H).
\tag{TM.5206}
$$

取得方面，A 先从实际准备事件取得 $m$，然后在同一源上执行原 TM31.2 的完整窗口—填充协议，包含所有替换与最终填充拒绝。TM31.3 已证它取得初始标签 $j$、初始 $E_0,\ldots,E_j$ 及 $n=\lambda_j(t_0)$，虽然停止时当前叶数为 $H$。将已取得 $m$ 放进 TM31.5 的已知尺寸解码，统一输出

$$
\begin{cases}
(0,E_0,m),&j=0,\\
(1,(a,b),E_0,E_1),&j=1,\\
(2,\eta),&j=2,
\end{cases}
\qquad b=n-jm,\quad a=(j+1)m-n\quad(j=1,2).
\tag{TM.5207}
$$

这是引用 TM31.5 解码的代入，不将它重复计为新增数学。$m$ 随本次输入变化却由相同计数规则取得；没有限制来源为一个预先公开的 $\mathcal T_{H,m}$。保存窗口、计数、系数转换和写出均有效有限且付费。来源调用至多 $H+4$，直接复用 TM31.6；准备和服务微工作不计入该调用数。

需要实际验收/使用的反过程还可作如下有限本地续接，毋须隐藏初始目标检验。A 封存并付费复制实际准备事件与原宏行至 V。V 用公开构造枚举的实际初始树逐个重放，比较该树的 $2\lambda_0-1$ 准备标签与全部原行，只保留符合这份扩张记录的候选，保持初始索引。真实 $t_0$ 始终保留；符合该记录的每个候选都具有同一个已计 m 和同一实际 Gamma，故由同一 TM31.5 解码输出式（TM.5207）的值。V 扫描所有候选的目标，检查提案恰为这个共同值，再实际写出绑定该准备/源/Stop 的回执，复制至 C，由 C 核对引用和类型、实际写入消费者输出。候选枚举、重放、比较、回执和两段 copy 均有有效有限日程并付费；V 没有 P 的实际输入行或私有初始 q。该续接只是实际已取得扩张记录的确定性计算，故在相同初始 q 下的全部可见 copy/check/use 标签也相同，不改变式（TM.5206）。表中的公开模型树和 guard 工作材料没有独立未知源身份，不增加一个可供 A 调用的来源副本；唯一可变实际源始终满足 live cap H。

最后，原全家族在 $H\ge9$ 无这样的取得协议是 TM31.4 的已有否定方向。结合其结论和式（TM.5207）即得严格能力差异，不重证原阈值。$\square$

### 52.2 实际 H9 前缀见证与全家族量词

**命题 52.4（同原记录的早期准备区别）。** 在 $H=9$ 下，给下列正词取从左至右的左结合实际树：

$$
X=\beta\beta\alpha\beta\beta,\qquad
Y=\alpha^9,\qquad Z=\alpha\beta^4.
\tag{TM.5208}
$$

它们分别有准备写入 $9,17,9$ 次。$X,Y$ 的首个原 Read 记录相同，但这两份准备视图不同；接受一次 $\rho$ 后，$X,Y$ 的当前 $q_9$ 和已见原记录仍相同，初始目标却不同。此对见证说明准备视图不通过已取得原记录因子化；原全家族取得不可能性必须另用 TM31.4，不能由一个成对前缀推断。

**证明。** $X,Z$ 的组成为 $(1,4)$、三叶数为 $(5,9,14)$；$Y$ 的组成为 $(9,0)$、三叶数为 $(9,9,18)$，故都为标签一。按实际叶积，$B^2AB^2=A$、$AB^4=A$、$A^9=A$，所以三者 $E_0=A$。第一次替换叶积为

$$
E_1(X)=S^2BS^2=B,\qquad E_1(Y)=B^9=B,\qquad
E_1(Z)=BS^4\ne B.
\tag{TM.5209}
$$

$S^2BS^2=B$ 与 $S^4\ne1$ 是 TM31 的原见证计算，后者由 TM28.1 唯一正规形，亦可用 $S^2=S+1$ 直接核对。于是 $q_9(X)=(1,(1,4),A,B)$、$q_9(Y)=(1,(9,0),A,B)$。共同原前缀 Read$(A)$、$\rho$(accept)、Read$(B)$ 后，当前边界都为 $(0,B,9)$；实际树可以不同，不得把当前同商当作初始同源值。式（TM.5203）给准备计数 $9$ 与 $17$。空原历史已经无法产生同一个 source-independent 准备视图；相同首 Read 返回也无法解释这个差别。

$X,Y$ 原来仍可用右拼接已知四叶 $\alpha^4$ 的 accept/reject 分离，$X,Z$ 可用 $\rho$ 后 Read 分离，所以此对不是原成对不可区分反例。TM31.4 的三个来源首次有效修改障碍排除一套适用于全家族的原协议；这里仅引用其结论。扩张协议在这三个来源上先计数区分 $Y$，再在五叶支上以原 $\rho$ 和 Read 区分 $X,Z$，而命题 52.3 的统一协议另外覆盖整个 $\mathcal T_H$、任意 $H$ 与全部括号。三源演示和全族结果的量词由此分开。$\square$

### 52.3 已取得记录上的有效在线合同

**定义 52.5（切面、视图与付费装饰）。** 原 idle 切面有实际配对 $(t_0,t,h)$，当前 $t$ 是从 $t_0$ 按 $h$ 中接受动作递推的实际树，拒绝保留它。局部控制、保留权限与输出相位另附；$q_H(t_0)$ 只作数学目标，不能是控制输入。实现切面另有实际私有来源表示、工作区、阶段、真实档案及局部交付引用。关系 $\mathcal R$ 保留同一个准备/源发生与上述初始—当前配对。它不能仅说“存在某个相容来源行”，也不能把所有所有者的私有状态合成一个新读口。

固定公共量 $p$，包括 $H$、有效代码、单位、上下文编码、身份生成规则和共同初始化。将控制器本地有限决策、复制、检查和消费记入有类型的本地记录 $u$；它们只读该接收者已收到的数据。有效在线装饰器 $D$ 与有效投影 $\mathrm{Dec}$ 满足，在每个允许决策切面，

$$
V=D_p(h,u),\qquad \mathrm{Dec}(V)=h.
\tag{TM.5210}
$$

装饰器状态由过去公开数据递推，是同一个算法，对所有允许初始源共同。其输入不是 $q_H$、实际初始树、实际表行或某个将来响应。准备视图由 $p$ 产生。一次原来源请求的实际响应交付为分界，公开 service 字分成有限前段、原响应与有限后段：

$$
D_p(h(a,r),u')
=D_p(h,u)\,P_p(h,u,a)\,[\operatorname{deliver}(a,r)]\,
Q_p(h,u,a,r,u').
\tag{TM.5211}
$$

这里 $a$ 包括原字面参数和上下文身份，$r$ 是该次原动作实际返回的 Read 值或 accept/reject。前段不得用尚未交付的 $r$，后段可用已交付的 $r$，不预测下一次响应。$P,Q$ 包括所有声明可读的准备、owner、PC、地址、tick、fee、阶段、停止、busy、availability、分配、复制、记录、通道及输出标签。标签的总数与每个中间前缀也须由此在线产生，不能只匹配服务终点或最终总费。若一个原行的响应通过分片交付，则它的公开编码与逐片次序必须明确，装饰器只有在该片实际交付时才消费该片；有控制选择的部分交付切面必须同时有原合同对应。

最直接的串行解释保原 TM30 的原子来源服务：idle 处可选原请求或有限本地操作/Stop；来源服务中可实际接收和记存标签，但没有额外来源调用、中途目标输出、timeout 或取消来源更新的选择。服务必有限到达下一 idle，全部接收事件仍保在视图中，不把它们当作不可观察 $\tau$。若实现确有内部选择、局部 Stop、availability 探测或 consumer 决策切面，则必须把那个切面加入 $\mathcal R$、式（TM.5210）和原相位/选择的双向对应；不能借原子记号隐藏它。以下命题在这种逐切面对应下同样归纳，原子串行版本则不增加原动作。

**假设 52.6（同源、全动作、进展与交付）。** 一个候选理想实现 $I_H$ 在声明的实际族 $\mathcal F\subseteq\mathcal T_H$ 上满足以下合同；每项都是需单独实例化的前提。

1. P 的实际私有初始化接收并保留同一 $t_0$ 的忠实语法表示，其输入、表示转换、代码和构造实际发生并付费。公开身份是相同规则产生的发生引用，不编码树内容。公开准备视图与有效控制初始化由 $p$ 唯一决定。初始 $\mathcal R$ 覆盖每个 $t_0\in\mathcal F$。
2. 每个 idle 的原请求及全部已知实际非空上下文都在双向对应中。Read 真正计算并交付当前 $E(t)$，保持树；$\rho,L_v,R_v$ 使用原整候选守卫，接受后的实际表示解码到那个候选，拒绝解码仍为旧树且只交付 reject。请求、上下文身份、左右顺序及公开参数逐字保留。沒有未知源导航、reset、copy、新源、逆向修改、变 $H$ 或隐藏初始目标测试；本地 copy 只复制已经获准取得的记录，不复制未知源。
3. 式（TM.5210）—（TM.5211）由一个已供应的有效在线装饰器成立，投影逐行还原真正交付的原响应。它在实际可达像上成立，并覆盖所有声明的 A/V/C 视图及可合法向它们传递数据的通道。一个未能交付的响应不能作为装饰器输入。源相关费用、分配失败、残额、名称、后台排程、无穷等待、可用性和 Stop 标签若可读，都在此合同中，不允许删去后继续引用结论。
4. 每个准入服务、拒绝、复制与必要本地检查/消费段都实际有有限日程或严格下降的有效自然数秩；所有允许的最大局部运行到达下一匹配切面。没有等待未知外部答复或允许无限不可见停滞。局部规则/调度是确定有效的；如另加调度选择，则须对每个允许选择提供相同的、源无关的在线对应与进展，不能只选一个有利日程。
5. 请求、Read 系数、已保存初始窗口、reject 行和发生引用通过实际有序写入与付费复制到接收者自己的存储。A/V/C 可访问的只有其交付视图，不能由数学联合元组免费共享 P 私有材料。目标输出由已取得记录和公开代码有效产生；若任务要求检查与使用，还必须有下节的本地检查及真实绑定交付/使用。终止、准备身份、初始目标绑定和所需有限 consumer 续接在双向关系中保持。
6. 无接口级固定总请求额、固定终端档案上限或源相关准备额度。每个原合法有限协议的本地数据、上下文、档案与准确计数有足够的真实付费空间，可逐次扩展，也可采用命题 52.10 的公开 per-protocol 供给。费用和截止条件若参与选择，其全部标签与 availability 仍须满足第 3 项；数值预算运输另需定义 52.11 的实际成本关系。

### 52.4 两向初始目标取得及本地消费者

**命题 52.7（TM30 已取得记录桥梁的充分后果）。** 在假设 52.6 的精确表示与有效本地计算条件下，对每个声明实际族 $\mathcal F$ 和每个有效表示的初始目标 $f:\mathcal F\to Y$，原 TM30 有一个有效、共同初始化、逐点有限停止的记录控制取得器，当且仅当 $I_H$ 有一个这样的取得器。翻译保持同一初始树、当前实际树、原请求/响应序列与来源调用数。任务若要求实际本地检查和消费者使用，结论以两边真实匹配的该续接为条件。这个充分 correspondence 不声称是每个单一目标取得能力相等的必要条件。

**证明。** 本命题的因子化与控制归纳是既有 Process Geometry 3.2–3.4、Observer-relative 44.1–44.2 的应用，以下写出用于本来源的两个有效构造，明确其源统一量词与初始索引。

先从原取得器 $\pi_M$ 提升。共同初始化 $I_H$ 于同一个 $t_0$，在每个允许切面将实际收到的 $V$ 通过 Dec 投影给 $\pi_M$，支付投影、局部计算和记存。若它选 $a$，执行对应的实际服务。第 2 项给实际原响应 $r$ 和相同 current successor；第 3、5 项保证下一切面实际可读的投影恰为 $h(a,r)$。第 4 项保证不会因内部停滞遗失下一行。按调用及本地切面归纳，原协议收到原实际源的同一响应，故同样选上下文、停止并输出 $f(t_0)$。原有限停止路径只有有限多有限服务和本地段，故提升有限停止。注意输出不是 $f(t)$；初始索引始终在 $\mathcal R$ 中。

反向，固定任意实现取得器 $\pi_I$，构造一个原取得器。它只保留自己真正取得的 $h$ 及模拟 $\pi_I$ 所需的有效本地状态。首先用 $p$ 算共同准备视图。之后在本地逐事件运行同一个 D 和 $\pi_I$，直至对方选下一原请求或 Stop。前响应阶段的可见数据由 $(p,h,u,a)$ 算出，不能要求尚未知 $r$；到匹配的原响应交付，执行同一个 $a$ 于这个实际原源，真实取得 $r$，再将此 $r$ 交给 D，生成后段及实际本地记录操作的模拟。对应内部切面若存在，使用其相同原本地选择/相位；原子版本中没有中途请求。每个本地模拟段有效有限，额外记录也实际记存并付费，不凭数学存在的因子函数执行不可计算操作。

由第 1 项，初始实现源关系和模拟视图相同。若归纳前提在一个切面成立，则相同视图/本地状态使 $\pi_I$ 选同一 $a$ 或 Stop；第 2 项使同一实际 $t$ 返回同一 $r$ 并变成同一 actual successor；D 的第 3 项使完整后续视图/本地状态相同，第 4、5 项保持下一切面可达并交付相同数据。因此模拟与真实 $I_H$ 对每个 $t_0$ 有同一原行、每个允许停止决定和输出。实现取得器在每个输入上有限停止，模拟这些有限段也有限停止；输出就为 $f(t_0)$。统一性是

$$
\forall\pi_I\ \exists\pi_M\ \forall t_0\in\mathcal F,
\qquad (\text{原行、停止、初始输出})_{\pi_M,t_0}
=(\text{对应原行、停止、初始输出})_{\pi_I,t_0}.
\tag{TM.5212}
$$

D、Dec 和构造 $\pi_M$ 在未知输入之前固定；不存在 $\forall t_0\exists\pi_M$ 的偷换。复制、检查和使用是有效 record-only 段时按同一局部归纳保持，必要的 source/preparation 绑定和实际消费也由第 5 项保持。来源调用各对一段，故计数相同；内部逻辑工作并不因此相等。$\square$

取 $f=\tau_H$ 和 $\mathcal F=\mathcal T_H$，本充分桥梁在其实例化成立时运输 TM31.4 的原阈值，而不会制造 $H\ge9$ 的取得器。命题 52.3 的扩张准备违反假设 52.6 第 1、3 项：相同公共 $p$ 与空原 $h$，$X,Y$ 的实际准备视图是九次和十七次 WRITE，不存在共同 D 的输出。它的标签通过潜在 $q_H$ 因子化却不通过已取得 $h$ 因子化。它满足正确宏源转移并不修复这个缺口；仅抹去 setup/tick/address 的 call/return 模拟也不满足完整观察字母表。

每个给定切面的扩张视图通过已取得记录因子化，必须在该记录纤维上常值，这是既有静态因子判据的必要方向。但纤维常值本身只给实际像上的数学函数；有效性、在线性、双向动作、进展与真实交付仍是额外义务。这是对所声明 replay 合同的条件，不能升级为“任意实现只要取得某个单目标，就必有这一 D”的必要性定理。例如常值初始目标可在共同初始化时输出，即使另有无用的新标签；本章的充分要求比那个单目标的取得等价严格。

**定义 52.8（记录相对的本地 checker 与消费者）。** 假设 V 实际收到带同一准备/源引用的完整有限原记录 $h$，已供应有效、完整的实际候选初始族 $\mathcal F$ 及原语义。保持初始—当前配对，顺次重放 h：每个候选初始树 $s$ 只沿该记录的相同原请求更新其 current tree，若其原响应不符该行则排除。

本地验收的有效性还要求目标值的精确相等可判定；仅有可计算名称不够。对本章必需的 $f=q_H$，按式（TM.5201）的标签、组成／叶数与各窗口的唯一整数正规坐标表示值：用式（28.3）沿每棵实际候选的叶序逐步计算，得到有限整数元组；提案按同一表示提供，逐字段整数比较决定相等。一般 $Y$ 的 checker 须另外供应这样的精确相等算法；这不增加未知来源端口，也不改变命题 52.7 的记录策略运输。在上述条件下记

$$
\mathcal F_h=\{s\in\mathcal F:
\operatorname{replay}(s,\operatorname{requests}(h))=h\}.
\qquad
\operatorname{Safe}(h,g)\iff
\mathcal F_h\ne\varnothing\ \land\ \forall s\in\mathcal F_h,
f(s)=g.
\tag{TM.5213}
$$

另检查引用、行序、类型、实际 Stop 边界和提案。V 接受时形成带这些真实引用及 $g$ 的回执；C 实际收到该回执与输出包，核对同一准备、源、Stop、目标类型与提案，再实际复制/写入它的消费者寄存器。每一环的存在、接收、核对和使用分别付费。仅存在一个数学正确 $g$ 不产生就绪或使用发生。

**命题 52.9（本地安全性与初始索引）。** 在假设 52.6 的真实交付下，真实 $t_0$ 始终留在 $\mathcal F_h$；式（TM.5213）成立的接受值就是 $f(t_0)$。完整有效有限候选与可判定精确相等的值表示下，checker 是有效有限的记录计算，且任何通过它的提案不会增加 $h$ 的来源区别。H9 的例子须相对于声明的 prior 取量词：令 $\mathcal F\subseteq\mathcal T_9$，令 $f=q_9\!\upharpoonright_{\mathcal F}$，并假定 $X,Y\in\mathcal F$；取实际来源 $t_0=X$ 所交付的共同原 Read–$\rho$–Read 记录
$$
h_{XY}=\bigl(\operatorname{Read}(A),\ \rho(\mathrm{accept}),\ \operatorname{Read}(B)\bigr).
$$
则 $X,Y\in\mathcal F_{h_{XY}}$、$f(X)=q_9(X)\ne q_9(Y)=f(Y)$，所以 $\operatorname{Safe}(h_{XY},q_9(X))$（以及提案 $q_9(Y)$）均不成立。特别地，取 $\mathcal F=\mathcal T_9$ 得到全家族的 H9 障碍。这里用 $X,Y$ 推出拒绝的特定见证论证要求 $X,Y\in\mathcal F$；排除 $Y$ 只使该见证不再适用，并不保证接受。例如 $\mathcal F=\{X,Z\}$、实际来源仍为 $X$ 时，$\operatorname{Safe}(h_{XY},q_9(X))$ 成立。

**证明。** 空记录兼容所有候选，包括实际 $t_0$。每行在实际树上发生的请求、响应与 successor 由假设第 2 项正确，且第 5 项实际交付该行，所以真实行逐项与 replay 相等，归纳保持 $t_0$。Safe 中取 $s=t_0$ 即得正确性。有限有效候选可以逐个扫描，每次用有效的原树动作与有限记录做有限重放，再用目标的有效表示计算 $f(s)$，用已供应的精确相等算法比较它与提案；这给有限算法，前提不允许用任意不可判定族描述替代候选枚举。它的真实输入只有交付 $h,g$ 和公共模型，故输出、费用、地址及回执通过它们因子化；扫描有效候选的代码/表和空间须另外构造、供给和付费，不免费取得实际行。C 的绑定核对使实际使用对象仍为这个已验初始目标。

在上述 H9 特化中，$X,Y\in\mathcal F$ 且两者都按同一 $h_{XY}$ 重放成功，故才可推出 $X,Y\in\mathcal F_{h_{XY}}$；这一步不从 $\mathcal T_9$ 的成员资格替代任意 prior 的成员资格。两初始目标不同，故该 proposal 不满足全称项。若 P 私有地比较 proposal 与自身隐藏 $q_H(t_0)$，在 $X$ 接受、$Y$ 拒绝，就增加了一个源敏感真值端口，不是式（TM.5213）的 checker。若只检查共同当前 $(0,B,9)$，则目标被换成 current，不能验证原 initial proposal。

边界由 $Z$ 给出：$E_0(Z)=A$，但 $E_1(Z)=BS^4\ne B$，所以在 $\mathcal F=\{X,Z\}$ 上，$Z$ 不属于 $\mathcal F_{h_{XY}}$，从而 $\mathcal F_{h_{XY}}=\{X\}$，式（TM.5213）对 $g=q_9(X)$ 为真。上面的特定 $X/Y$ 见证论证以 $X,Y\in\mathcal F$ 为前提；排除 $Y$ 只移除此见证，其他兼容初始候选仍可造成拒绝。一般地，对任意声明的 $\mathcal F\subseteq\mathcal T_9$ 和 $f=q_9\!\upharpoonright_{\mathcal F}$，只要实际来源 $X\in\mathcal F$、$h$ 为该来源的真实交付记录，就有 $X\in\mathcal F_h$ 保证非空，故式（TM.5213）给出 $\operatorname{Safe}(h,q_9(X))\iff\forall s\in\mathcal F_h,\ q_9(s)=q_9(X)$。

例如，给 $W=\alpha^5$ 取左结合实际树，在实际来源仍为 $X$ 时，$X,W$ 都有五叶、九次准备写入；$W$ 的三叶数为 $(5,5,10)$，$E_0(W)=A^5=A$、$E_1(W)=B^5=B$，故 $q_9(W)=(1,(5,0),A,B)\ne q_9(X)$。在 $\mathcal F=\{X,W\}$ 上两者均重放 $h_{XY}$，所以 $\mathcal F_{h_{XY}}=\{X,W\}$ 且 $\operatorname{Safe}(h_{XY},q_9(X))$ 为假，尽管 $Y\notin\mathcal F$。此例针对这个已取得记录切面的检查；一次 $\rho$ 后当前 $q_9$ 分别为 $(0,B,9)$ 与 $(0,B,5)$。

静态充分性/缺陷判据复用 TargetRecoveryCriterion；实际候选不空条件由真实 $t_0=X$ 提供，未编译普通应用不计为 Lean 核验。$\square$

### 52.5 全有限语言、有效资源供给与成本

**命题 52.10（固定请求额度的反例与公开 per-protocol 上界）。** 固定 $H$ 的有限源/服务核心可以反复服务任意有限次请求；一个固定全局 requestE、固定容量的完整有限档案或固定宽度非环绕累计计数不能代表原完整语言。相反，在明确的有效全执行及逐点终止承诺下，可以从 $H$ 和一个公开协议有效求出它在全部 $\mathcal T_H$ 上的共同有限资源上界。此算法的运行、存储与预分配均须付费；不提供任意程序终止判定或一个免费的普遍界。

**证明。** 在 $H=1$ 的实际单叶 $\alpha$ 上，对每个有限 $r\ge0$，$\mathrm{Read}^r$ 后 Stop 合法、每次返回 $A$ 且来源不变。取 $r=E+1$，固定总额 E 的模型在原合法继续点必须拒绝/关闭/丢弃最后一行，故双向语言对应失败。原响应不断相同也不使完整记录相同：记录长度分别为 r。一个固定有限状态存储载体若能恢复每个完整档案，就要给无限多不同 r 一个单射存储，有限性矛盾。非环绕准确请求序号、累计 tick 或累计费同理值无界。这个论证只针对保有完整记录/准确计数；有限源转导器完全可以无界流式发出相同 Read，而不保留它的全部过去。亦没有要求每个原协议一定保有整档。

现在陈述上界算法的确切输入前提。公开协议 $\pi$、其表示/控制、必要 checker/consumer、全部材料构造、记录扩展与调度有统一有效执行语义，有限前缀的步骤、输入/输出、分配/释放和成本事件可精确计算；它们不依赖未建模外部应答。若采用一个具体 lower process，其所有微步与计量同样有效并在这次模拟内，而非只给一个语义来源 oracle。执行语义在计算上界前已固定；取出的上界只作充足供给，不能改变协议、日程或代价规则。承诺 $\pi$ 及所需整个续接对每个实际 $t_0\in\mathcal T_H$ 都有限停止。任何预算/调度分支已包含在这一固定语义中。

按命题 52.3 的构造递推有效枚举全部有限 $\mathcal T_H$，在本地模型中给每个可能初始树运行同一 $\pi$。顺次模拟每个输入也会终止；等价地轮流推进各模拟器，直到所有均停止。逐步记录每个模拟的来源调用、已付工作、各存储对象存活及其位长、上下文材料与输入/转换/输出长度、计数最大值。因初始列表有限且每个全执行有限，存在一个阶段全部停止，算法必到达该阶段。此时顺次扫描每个有限结果，实际求出各路径费用最大值、同步存储峰值最大值、最大字段/地址/计数位长，得到例如

$$
R_{\mathrm{calls}}(H,\pi)=\max_{t_0\in\mathcal T_H}N_{\mathrm{calls}}(\pi,t_0),\qquad
B_{\mathrm{peak}}(H,\pi)=\max_{t_0\in\mathcal T_H}B_{\mathrm{peak}}(\pi,t_0).
\tag{TM.5214}
$$

这些表达式的最大值不是算法的替代物；上面实际模拟/汇总就是在承诺类上的取得算法。分配所得充足资源后，相同语义的每条真实路径已被其初始树模拟覆盖，故由逐步归纳不会超过相应峰值或计数界。若固定宽度编译改变微步或日程，应再供应那个编译的 all-path 成本/进展证明；不能把 reference 语义测得的工作数不经关系直接搬入新机器。共同上界是全部输入的公开最大值，不是依未知实际输入选出的容量或 advice。

整个边界计算本身及随后资源/代码构造也实际耗时、存储和费用，须记入准备账。承诺不成立时，这个算法可能一直模拟，既不给上界也不判定不终止；没有对所有程序的总终止决定器。具体初始化或外部调度只有非有效存在时，也不满足算法前提。对一个已选终止协议的供给是限定的实现族，不能作为服务语言的新 requestE；有可扩展付费存储的同一服务则对每个有限请求前缀单独完成其实际分配。$\square$

**定义 52.11（费用、存储与归属的不同坐标）。** 原模型本身只定义语义调用，不附墙钟价格。在选定 lower 合同中，至少分开记录来源调用次数、实际逻辑工作/构造费、同时存储峰值、源/上下文材料、输入/转换/输出和物理时间。对一条已实现有限路径，使用来源调用计数与实际理想工作式

$$
\begin{aligned}
N_{\rm source}&=\#\{\mathrm{Read},\rho,L_v,R_v\text{ 实际调用，包括 reject}\},\\
K&=K_{\rm model/code}+K_{\rm input/prep}+K_{\rm bound/allocation}
 +\sum_i\bigl(K_{\rm control,i}+K_{\rm context,i}
 +K_{\rm guard/service,i}+K_{\rm record/copy,i}\bigr)
 +K_{\rm convert/output}+K_V+K_C,\\
B_{\rm peak}&=\max_k\sum_{o\text{ 在发生 }k\text{ 存活}}|o|.
\end{aligned}
\tag{TM.5215}
$$

求和项是各自真正发生的不同操作，不重复把“服务”既作总额又与其全部子操作相加。拒绝、padding、未选中的表行运算、构造字面常量、材料生成/发送、接收/保留、控制器计数与消费者写入全部在相应项。峰值是同一次日程的同时存活和，不是各阶段分别最小值的拼接；固定源核心之外还计公开上下文、表/代码、scratch、在途副本、local control 和保留档案。源的 live cap H 并非工作内存上限。

命题 52.3 的节点数据操作单独可核对为：构造 $R$ 个源单元，清空 R 次，输入 $L=2m-1$ 次 token WRITE，SEAL 一次，即 $R+L+1=R+2m$ 次这些数据/封存操作，加 $R$ 个单元构造；这是选定单位中的子账，不是整机总费。相同的 per-token control、tick 发布、真实事件交付/保存与 A 的递增也收费。A 只保留计数时计数需 $\lceil\log_2(2H)\rceil$ 位，逐位递增为有限有效工作；要求保留完整事件档案时则另外写入所有地址/引用/标签。输入两位单元的 $2L$ 位源材料也不能与 L 次单元写混为一个位成本。表生成、扫描、上下文及实际 Read 整数包/转换/输出费用再加；$N_{\rm source}\le H+4$ 从来不是 $K\le H+4$。

桥梁只给语义取得和调用计数保持。若比较带预算的取得，需同时供应一个有效源无关成本运输，对全部路径的准备、每段及消费真实费用和 availability 保持，或给已证明的方向上界并对应地转换预算。把实现数值费用映为原“每调用一单位”而不计其他项不满足它。可观察的费、残额和截止必须仍由已取得记录在线解释；它们不能充当 latent target 真值传感器。理想 tick 不等于 SI 秒，未供应硬件速率、噪声和校准时无物理耗时、最优或普遍硬件费结论。

归属与允许视图按下表绑定到本同源过程；其他观察者的数据若能通过合法通道到达 A/V/C，也纳入装饰器，不能在通信后仍称私有。

| 52归属 | 实际职责和准入视图 |
| --- | --- |
| 52P准备 | 接收实际初始树材料，保私有载荷和发生引用；对发表前的准备相位、地址、tick、fee、可用性负责。事后消费者过滤不能撤销已公开长度。 |
| 52P服务与局部调度 | 持有 current 源、私有 guard/candidate/scratch；负责整候选、真实 Read、接受/拒绝、中间标签及有限进展。实际行匹配位不能成为公开地址。 |
| 52A控制与记录 | 从真实收到的 public data/records 决策；保存初始窗口和发生计数，支付记存/转换/控制，不能读取 P 私有源。 |
| 52通道与副本 | 产生有序不可变行及真实引用，实际传送/接收/保留副本；一个数学指针或联合元组不是 copy 发生。 |
| 52V本地checker | 只访问已交付 h、proposal 和公开有效候选/模型，保初始/current 索引；付费重放/常值核对，无隐藏 initial target truth test。 |
| 52C消费者 | 访问真实回执和输出包，核对类型/源/prepare/Stop/proposal 并实际使用；正确数学值不能代替交付和使用。 |

### 52.6 供应核对、有限 corroboration 与剩余范围

**约定 52.12（精确复用与原文条件）。** 以下引文均以本章基线不可变提交为仓库输入。普通证明读过这些原陈述及所需前提；没有当前编译、Lean/kernel 或账目状态声明。通用数学只作为本章来源特定分离和桥梁的中间步骤使用。

| 52供应 | 本章用到的确切内容与边界 |
| --- | --- |
| 52TM30–31 | [运输—记忆—完成卷 TM30.1–30.2、TM31.1–31.6](https://github.com/the-omega-institute/trureturing/blob/40be8185113f7ac5abd5cbf534b844b8014fa9e3/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)：实际非空有序树、整候选及 reject、共同记录控制；TM30 精确核与闭合用于式（TM.5206）；TM31.3 给实际 Gamma，31.5 给已公开 m 下的初始解码，31.6 给 $H+4$；31.4 的原全家族 $H\ge9$ 否定直接引用。准备事件取得 m 是本章新增条件，非原合法 size 口。 |
| 52TM28与48 | 同一 pinned 卷 TM28.1 的整数正规形及 28.3 乘法；TM48.10 的 adapter 只在原 Read 已返回忠实固定基的四个精确二进整数时，付费 $O(D^2)$ 位操作/$O(D)$ 工作位转换。它不给未知 E 仪器符合性，也不给免费 compact coordinates。本章反过程可由实际叶积生成此表示；对其他实现仍须供应。 |
| 52PG完整标签 | [Process Geometry 3.2–3.4、20.3](https://github.com/the-omega-institute/trureturing/blob/40be8185113f7ac5abd5cbf534b844b8014fa9e3/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)：实际像上的根、域、全标签和 successor 纤维不变，以及共同局部输入/记录的策略归纳；不把相同潜在行为树当作已取得树。20.3 已明说核不变不保证动作菜单、事件词或取得费用不变。命题 52.7 在实际已取得历史上应用此机制。 |
| 52OR局部与相位 | [Observer-relative 44.1–44.2、58–65，特别 60.1–60.2、63.1、65.1–65.3](https://github.com/the-omega-institute/trureturing/blob/40be8185113f7ac5abd5cbf534b844b8014fa9e3/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md)：局部视图、真实 copy、控制相位/消费者和全观察中性有各自前提。58–65 是 bounded rational-word 源 $D_Q$，私有 words、SAMPLE、全局 attempt E 和 typed consumer；63.1 以完整门流相等为条件，65 明留原树/动作/费用 intertwiner。它不是假设 52.6 的实例化，E 不可移植为原语言上限。 |
| 52静态Lean供应 | [TargetRecoveryCriterion.target_recovery_criterion](https://github.com/the-omega-institute/trureturing/blob/40be8185113f7ac5abd5cbf534b844b8014fa9e3/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)：`Nonempty X`、给定 process/target，恢复等价于 target 在 process 纤维常值。真实兼容 t 提供非空性；声明只供应静态因子判据，不供应 record 取得。 |
| 52有类型Lean供应 | [TypedFiniteViewKernel.typed_finite_view_kernel](https://github.com/the-omega-institute/trureturing/blob/40be8185113f7ac5abd5cbf534b844b8014fa9e3/D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean)：给定类型、Option-valued 具名带标签 step 与 q；全部有限路径保域、标签序和读数，平台给完整核。没有付费源生产、因果 controller 或服务进展输入，不能由此断言假设 52.6 已实现。 |
| 52TM2与49 | 同一 pinned 卷 TM2.19 的 continuation 运输要求一个所有状态共享的 test 双射、双向域/successor 与观察/成本/时长相等；仅一个树编码不供应它。TM49.6 允许已供应 label 通过初始 q 因子化来保同 q 初始纤维；本章从不细分这样的纤维，因此无矛盾，也不重做其原树容量成果。 |
| 52实际原子来源 | [Atomic §§355–357、359 的原规则](https://github.com/the-omega-institute/trureturing/blob/40be8185113f7ac5abd5cbf534b844b8014fa9e3/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)：非空实际有序树、替换构造、Clifford 叶积及四基独立；本章见证是实际正树，不把三窗的单独可实现性变成共同来源。本章无需另一个 queued joint-capacity/unit-fiber 结果。 |

文献状态为：付费节点准备在这个实际 TM30 全家族上给出“精确同核、不同统一初始取得”的推导是 `repo-derived`；通用因子化、完整标签和策略运输是既有供应复用。只在本章列出的邻接来源和以下原文中核对过对应条件，不主张全库无重叠、穷尽文献或来源特定结论的全球优先权。

| 52原文 | 已核对的桥梁内容与对象/量词对应 |
| --- | --- |
| 52Lynch–Vaandrager | *Forward and Backward Simulations, Part I: Untimed Systems*，[作者 IC95 稿](https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf)，§3.2，PDF 页11–12，定义的两项 forward simulation 与 Theorem 3.10：初始关系覆盖及每一步存在同迹有限片段，给 trace inclusion。state 对应 actual source/control/history，片段对应 service。它不单独给有效统一 policy back-translation、反向控制、有限进展或被隐藏 tick/address 的中性，故这些由假设 52.6 另给；未将 untimed $\tau$ 用来删除已公开事件。旧字体提取有分隔问题，引用限于能核对的陈述。 |
| 52Abate等 | *Journey Beyond Full Abstraction*，[arXiv:1807.04603v6](https://arxiv.org/pdf/1807.04603v6)，§4.1，PDF 页8，$\mathrm{RrHC}:\forall C_T\exists C_S\forall P$ 的 property-free 形式。把 context 对应合法控制器、program 对应用 t 初始化的 server，得到式（TM.5212）的 uniform 量词形状；每源选择不同 simulator 不足。原文的编译/安全模型不是本来源的树/成本供应，不引入恶意 context 或整个编译器安全结论。 |
| 52van den Bos–Vaandrager | *State Identification for Labeled Transition Systems with Inputs and Outputs*，[arXiv:1907.11034v2](https://arxiv.org/pdf/1907.11034v2)，Definitions 17、20 和 Figure 3，PDF 页11–12：成对 test 与一个 adaptive distinguishing graph 不同，首次选择可以合并未取得区别。input/output 对应原请求/响应，叶对应初始目标。原文 suspension automaton 条件、有限字母表算法和长度界不供应 TM30 全上下文语言、reset 或 H9 数值；原不可能性由 TM31 提供。 |

上述三种成熟数学内容均为 `literature-attested` 中间框架。本章双向证明实际补足有效、全字母表、在线、same-source、有限进展、record delivery 和本地消费条件，未把任一文献 trace inclusion 定理扩张为未经条件的 TM30 acquisition 定理。

**命题 52.13（独立有限 corroboration 的确切范围）。** 在精确有理矩阵模型

$$
A=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
B=\begin{pmatrix}1/2&1\\-5/4&-1/2\end{pmatrix}
\tag{TM.5216}
$$

中，基 $1,A,B,AB$ 的坐标矩阵行列式为 $-5\ne0$；该模型在四维 Clifford 张成空间忠实。以下有限断言已经用独立编写、无仓库/前阶段程序导入的精确整数与有理算术核对：$H=1,\ldots,12$ 全部正叶词运行，$H\le6$ 全部括号树运行，$H\le5$ 全部实际上下文至 $H+1$ 叶的两侧拼接，以及 H9 见证和固定 E 原 Read 续接。它们仅 corroborate 所述有限样本，不证明所有 H、所有历史或完整 lower emitter 的符合性。

**证明与有限范围说明。** 矩阵直接满足 $A^2=1,B^2=-1,AB+BA=1$，四基 determinant 非零使有限等式不因表示坍缩而伪真。一个独立枚举用实际树的递归生成、实际 $\rho$ 与整候选拼接；另一路逐词使用整数正规坐标乘法与精确矩阵叶积交叉比较，未调用任何 producer/reviewer。执行前固定失败条件：编码非单射或长度非 $2m-1$；相同 q 有不同准备写入迹；已取得 m 加真实 Gamma 不回到初始 q；guard/Read/successor 不符、reject 改源或给候选 E；H9 计数/窗口/merger 错误；隐藏初始真值 checker 能被误当作 record-only；固定 E 不能被 $\mathrm{Read}^{E+1}$ 反驳。任一断言失败须停止并否定相应有限结论，不能把失败重新归类为无限范围免责。

实际退出码为 0，核对的 $H$–word 运行数为 16,356（允许同一词在不同 H 上分别运行）；三个数学窗口的整数/矩阵比较为 49,068；初始标签零/一/二分别为 14,788、1,399、169 次。全部括号树的 $H$–tree 运行数为 3,920，每次检查解析逆、$2m-1$ 长度、同 q 准备迹及初始解码。$H\le5$、上下文 $\le H+1$ 的实际 tree/context 对为 1,839,388，两侧 graft 为 3,678,776 次，其中 accept 1,344、reject 3,677,432；另有 1,364 次 Read/$\rho$。按相同 current q、请求及实际上下文分组的响应/successor 类为 239,692，均未见不一致。H9 的全部一至四叶实际上下文两侧 merger 共 204 次。共同 Read–$\rho$–Read 记录的有界左结合候选中有四词，含 $X,Y$；在声明 $\mathcal F=\mathcal T_9$、$f=q_9$ 的实例中，record-only checker 拒绝把 $q_9(X)$ 作为唯一初始目标提案。$H=1,E=0,\ldots,8$ 的九个原 $\mathrm{Read}^{E+1}$ 续接均合法，固定 cap 的末端 EXHAUSTED 与原响应不同。准备/address/tick/fee/phase/stop/availability/copy 的八种人为不同标签作为负控确被视图相等检查识别；这些是局部 label 反例 fixture，不是某个真实 emitter 的 all-path 运行认证。矩阵 rank/determinant 另以独立短计算核对，退出码亦为 0。

有限程序的范围是算术、实际有限树动作和所声明的反例记录，不是假设 52.6 的已实例化实现。一般 code-length、同核分离、全族取得与双向 correspondence 依靠前述普通证明及列明供应，不能由这些有限计数推成全称定理。普通证明与有限精确核对均不计为 Lean verification。$\square$

**开放问题 52.14（尚未实例化的忠实 paid TM30 与物理桥梁）。** 命题 52.3 已供应理想扩张反过程的实际源输入、有限 suffix 和费用条件，它故意不保持原 acquisition。假设 52.6 对一个保持原接口的 fully faithful paid TM30 producer 仍需另外实例化：来源私有输入与所有公开准备前缀的中性；每种接受/拒绝的实际树服务及确切 Read 编码；全参数、全可见中间切面/availability/Stop 的在线装饰器；本地调度进展；全部实际上下文材料、准确可增长计数、记录与 copy；初始 checker/consumer 绑定，以及同一次日程的符号成本/空间与供给。一般有限可表示性不认证任何已有 bounded word producer，未执行的树微程序也不是符合性证据。Padding 准备的全部输入相位至公开 R 次、把 dummy payload 保私有，是消除本章长度信号的局部修复；在早已公开 SEAL 后才追加 padding 不能撤回该信号，正确全实现仍须逐项满足合同。

物理器件、校准、噪声、实际墙钟与逻辑 tick/fee 的关系没有供应。其他来源/端口、概率协议、外部不受约束调度、所有目标都需要这一充分 D 的必要性、最优硬件或普遍资源成本也不在本章结论中。本章推进的是同实际树、同初始目标下“空间/时间标签—已取得记忆—行为边界”的精确条件：latent 行为商可以相同，而真实取得记录不同；只有在完整、有效、在线且真正交付的关系及进展/资源前提成立时，策略和初始目标取得才按所证两向恢复。长期持续目标仍有上述具体未解桥梁。

## 追加锚（本行以下为增补区）

## 54. Complete unit-family supplied advice: linear capacity and actual acquisition

This appendix refines the conditional minimum-advice question on the **complete actual unit-history family**. [OR68.5][OR68] already proves linear growth with the public cap and the exact values 1 at $8\le H\le19$ and 2 at $20\le H\le35$. [OR69.4][OR69] gives 2 at $36\le H\le39$ and 3 at $40\le H\le55$. Here the all-policy lower bound improves OR68's $h/8$ leading lower to $\gamma h$, where $h=\lfloor H/4\rfloor$ and $\gamma=(7-3\sqrt3)/11$. Two explicit constructions give separate alphabet/depth/call tradeoffs, and a cap-28–31 policy supplies a particular call bound and a fixed-executor separation for already known numerical exactness.

The general exact function, the sharp leading alphabet coefficient, existence of a normalized limit, and normal forms for minimum-alphabet policies remain unresolved; particular caps can be settled when valid bounds coincide. These are ordinary mathematical proofs under the conditional supplied-advice interface, without a Lean verification claim.

The structural premises below are taken from the immutable revision `e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74`; the published OR68–69 comparisons use `511f1920bceaaf9f6ec6411030fbd4da42abfbfd`.

### 54.1 The task and its actual source correspondence

**Definition 54.1 (conditional supplied alphabet).** Let $H\ge1$ be a public integer, fixed throughout a run. An actual source is a nonempty ordered binary tree

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\tag{TM.5401}
$$

Equality of trees retains leaf order and every bracket. Write $c(t)=(a,b)$ for the leaf composition, $m=a+b$, $n=a+2b$, and $E_i(t)=E(\rho^it)$. The leaf product $E$ is evaluated in the project's associative Clifford algebra, with $E(\alpha)=A$, $E(\beta)=B$, $A^2=1$, $B^2=-1$, and $AB+BA=1$. Set

$$
\begin{aligned}
\mathcal T_H&=\{t:1\le\lambda(t)\le H\},\\
U_H&=\{t\in\mathcal T_H:(E_0(t),E_1(t),E_2(t))=(1,1,1)\},\\
q_H(t)&=\begin{cases}
(0,E_0(t),m),&n>H,\\
(1,c(t),E_0(t),E_1(t)),&n\le H<m+n,\\
(2,c(t),(E_0(t),E_1(t),E_2(t))),&m+n\le H.
\end{cases}
\end{aligned}
\tag{TM.5402}
$$

The last line is TM30's $(2,\eta)$ in its equivalent composition/three-window coordinates. Thus the target here is exactly the published $q_H$.

The online actions are ambient TM30 actions: current `Read`, a whole $\rho$ attempt, and a whole left or right concatenation with a named actual nonempty positive context. The guard accepts precisely when the entire candidate has at most $H$ leaves, including equality. Rejection preserves the source and supplies no candidate read. The record includes public inputs, the supplied label, action and context identities, actual guard responses and actual reads. These semantics continue after the source leaves $U_H$. There is no reset, copy, navigation, source replacement, inverse action, row/size/target port, new cost observation, or candidate-read leakage.

For nonempty $U_H$, define $A_U(H)$ to be the least cardinality of a finite nonempty alphabet $\mathcal L_H$ for which there exist a function $\ell_H:U_H\to\mathcal L_H$, genuinely supplied from the **same unmodified initial source**, and one effective deterministic controller $\Pi_H$, such that

$$
\forall t\in U_H:\quad
\Pi_H\bigl(H,\ell_H(t);t\bigr)
\text{ stops after finitely many source calls and outputs }q_H(t).
\tag{TM.5403}
$$

Equal labels have equal initialization and public data. Every later choice depends only on that initialization and acquired records. The minimization allows arbitrary source-dependent supplied functions, including functions depending on leaf order or brackets; the lower proof does not require their computability or factorization through $q_H$. The upper suppliers and controllers constructed here are effective uniformly in $H$. Their supplier algorithms take already available initial-source information as input; this is not a free way to obtain that information from the unknown running source.

The prior is the public logical promise of membership in the complete $U_H$, not a probability distribution. A varying supplied label is additional evidence. By Atomic360 and TM51, $U_H$ is empty exactly for $1\le H<8$. We use $A_U(H)=0$ there if an empty alphabet is permitted on an empty domain; a convention requiring nominally nonempty alphabets gives 1 instead. No depth or logarithmic advice width is assigned to the empty task. All substantive capacity claims concern $H\ge8$.

**Source correspondence (reused, with coordinates for this appendix).** Put

$$
h=\lfloor H/4\rfloor,\qquad H=4h+\delta,\quad0\le\delta\le3.
$$

Atomic360.2–4 and TM51.2–3 give exactly

$$
c(t)=(4r,4s),\quad r,s\ge1,\quad r+s\le h.
\qquad
z=r+s,\quad w=r+2s.
\tag{TM.5404}
$$

Consequently $m=4z$, $n=4w$, $m+n=4(z+w)$, and

$$
2\le z\le h,\quad z+1\le w\le2z-1,
\qquad r=2z-w,\quad s=w-z.
\tag{TM.5405}
$$

For every such pair there is an actual witness, with any fixed ordered bracketing, whose leaf word is

$$
\omega_{r,s}=
\alpha^{2r-1}\beta^{2s}\alpha\beta^{2s-1}\alpha^{2r}\beta.
\tag{TM.5406}
$$

Its eight state-edge multiplicities in Atomic360 are $(r,r,r,r;s,s,s,s)$: all are positive, balanced, and have connected support. The converse in that theorem is essential: **all** qualifying leaf words are the corresponding Euler-path labels, and **all** their ordered bracketings are actual members. A disconnected support with one of $r,s$ zero is excluded, and $r=s=0$ would be an excluded empty source. No merely marginally attainable resource triple is used here.

Use the shorthand $\tau_h(z,w)$ for the original target of a finite pair $w\le h$:

$$
\tau_h(z,w)=
\begin{cases}
(2,(4(2z-w),4(w-z)),(1,1,1)),&z+w\le h,\\
(1,(4(2z-w),4(w-z)),1,1),&z+w>h.
\end{cases}
\tag{TM.5407}
$$

If $w>h$, the target is $(0,1,4z)$; all its hidden compositions at that size count as one target. Such a target exists precisely when $2z-1>h$. Its actual representative is $\omega_{1,z-1}$. The symbol $(z,\infty)$ below denotes this target, not an observed or physical infinite resource.

Every displayed inequality holds for every $\delta$. For instance, $w\le h$ is exactly $4w\le H$, while $z+w\ge h+1$ gives $4(z+w)>H$. This does not prove that the unrestricted optimum depends only on $h$: arbitrary ambient contexts can have lengths not divisible by four.

TM30.2 states that equal initial $q_H$, equal label and common initialization force identical complete responses under every such controller. TM38.1 states that equal complete acquired records and equal **current** $q_H$, paired with different original targets, cause permanent failure of recovery. TM45.1–4 preserves these initial/current pairs throughout actual histories. Thus a construction with labels factoring through the original target lifts to every word and bracketing in that target fiber, without physically replacing the running source by a witness. For a competing arbitrary supplier in a lower bound, select one actual representative per target and retain that representative's actual label. This restriction makes no factorization assumption.

### 54.2 The unit resource geometry

**Lemma 54.2 (exact columns, rows and second archive load).** For $h\ge2$ define $[x]_+=\max(x,0)$. The original tag-1 column with first replacement coordinate $w\le h$ has the integer interval

$$
I_w=[a_w,w-1]\cap\mathbb Z,
\quad a_w=\max(\lfloor w/2\rfloor+1,h-w+1),
\quad f_w=[w-a_w]_+.
\tag{TM.5408}
$$

The tag-1 row with original size coordinate $z$ has degree

$$
d_z=[\min(2z-1,h)-\max(z,h-z)]_+.
\qquad
\epsilon_z=\mathbf1_{\{2z-1>h\}}
\tag{TM.5409}
$$

where $\epsilon_z$ counts its single additional tag-0 target. For $h\ge3$ put

$$
K=\lfloor(h-1)/2\rfloor,\quad
D=\lfloor(h+1)/6\rfloor,\quad
b=\lceil(h+2)/3\rceil.
\tag{TM.5410}
$$

Then $\max_w f_w=K$, every nonempty tag-1 row has $z\ge b$, and the largest original tag-2 column at second replacement coordinate $p=z+w\le h$ has size $D$. If $D=0$, there are no such targets.

**Proof.** The finite-pair conditions give $z\le w-1$ and $z\ge\lfloor w/2\rfloor+1$; tag 1 additionally requires $z\ge h-w+1$. This gives (TM.5408), including empty intervals. The row has

$$
\max(z+1,h-z+1)\le w\le\min(2z-1,h),
$$

which gives (TM.5409). The composition with largest possible $w$ at row $z$ has $w=2z-1$, proving the tag-0 indicator. The inequality $f_w\le w-1-\lfloor w/2\rfloor\le K$ is attained at $w=h$. For tag 1, $h+1\le z+w\le3z-1$, hence $z\ge b$.

For tag 2 at $p=z+w$, positive $r=3z-p$ and $s=p-2z$ are equivalent to

$$
\lfloor p/3\rfloor+1\le z\le\lfloor(p-1)/2\rfloor.
\tag{TM.5411}
$$

For $p\ge5$ its length is $\lfloor(p-1)/2\rfloor-\lfloor p/3\rfloor$. At $p=6k+a$, $a=0,1,2,3,4,5$, these lengths are respectively $k-1,k,k,k,k,k+1$. At $p<5$ the interval is empty. They are all at most $\lfloor(p+1)/6\rfloor$, and $p=6D-1\le h$ realizes $D$ when $D\ge1$. This proves the exact maximum and the empty case. Each counted point has the simultaneous actual witness (TM.5406). $\square$

### 54.3 A necessary finite inequality against all policies

**Theorem 54.3 (complete-family counting obstruction).** For $h\ge2$ let

$$
B(h)=\min\left\{L\in\mathbb Z_{\ge1}:
\sum_{w=3}^{h}[f_w-L]_+
\le\sum_{z=2}^{h}\min(d_z,L-\epsilon_z)\right\}.
\tag{TM.5412}
$$

Empty sums are zero. This minimum exists, and every successful supplied alphabet on the complete $U_H$ has size at least $B(h)$. For $H\ge20$ it also has size at least 2, by the published TM51.7 obstruction. The finite inequality is necessary; it is not an acquisition certificate.

**Proof.** Choose an actual witness for every original tag-1 target and for every original tag-0 size target, retaining whatever label the putative full-family protocol gives it. Every witness is in the same $U_H$. For each label, partition these representatives by their actual runs: $P$ consists of those stopping without a $\rho$ attempt or whose first $\rho$ attempt rejects; $C$ consists of those whose first attempt accepts. Pointwise finite stopping makes this dichotomy exhaustive. Every tag-0 witness belongs to $P$, since positive contexts cannot decrease its already excessive next size.

Here is the actual-history argument underlying TM37.2, including the tag-0 extension needed by the count. Before the first $\rho$, the accepted contexts contribute common known amounts $U,V$ to current and next size, with $0\le U\le V$; each individual positive context has $1\le d_0\le d_1\le2d_0$. The current read is the same ordered product $L_0\,1\,R_0$ for sources with a common record. Left and right factors retain their actual order.

Two same-label representatives in one original $z$ row have identical full records up to stopping or the first $\rho$: context guards depend only on their common $4z$ and known accepted increments; Reads agree. If a run stops before that attempt, both stop with the same output. If two such representatives are in $P$ and an attempt occurs, both first attempts reject. Their current sources then have the same size $4z+U$, the same read and current tag 0, hence the same current $q_H$. Their original targets are different, so TM30.2/TM38.1 prohibit a successful continuation. Therefore each label supplies at most one $P$ member per row, including the obligatory tag-0 member.

For the column restriction, take two same-label tag-1 representatives with the same $w$ and $z_1<z_2$. Suppose the smaller source's first $\rho$ accepts after contributions $U,V$. Then $4w+V\le H$. Every context accepted along this source's actual prefix also accepts on the larger source: if its cumulative increments after that context are $U',V'$, then

$$
4z_2+U'\le4w+U'\le4w+V\le H.
\tag{TM.5413}
$$

Here $U'\le V'\le V$, since all accepted contributions are nonnegative. Every context rejected on the smaller source also rejects on the larger, with the same preceding increments. Ordered-factor Reads agree. Induction therefore forces the larger source to follow the **same complete actual prefix**, including every context identity, side, Read and rejection. Both first $\rho$ attempts accept. The two current sizes become $4w+V$, and the two current reads become the same $L_1\,1\,R_1$. Their next sizes are $4(z_i+w)+U+V>H$, because each original source is tag 1. They have identical current tag-0 $q_H$ and identical complete records but different original targets: another permanent collision. Thus $C$ contains at most one member of each column per label. In fact an accepting member must be that label class's largest row in its column.

This argument permits every actual mixed positive context, either side, arbitrary intervening reads, unlimited acquired records and all later ambient actions. It uses forced simultaneous histories, not two independently achieved windows. It places no accepted-depth bound on competing protocols.

With $L$ labels, at most $L$ tag-1 representatives in column $w$ belong to $C$, so that column has at least $[f_w-L]_+$ members in $P$. Row $z$ has at most $L$ total $P$ members and already contains $\epsilon_z$ mandatory tag-0 members; hence at most $\min(d_z,L-\epsilon_z)$ tag-1 members in $P$. Counting the same actual tag-1 $P$ set by columns and rows gives (TM.5412). When $L\ge\max_w f_w$, its left side is zero and the right side is nonnegative, so $B(h)$ exists. The inequality is monotone in $L$. Restriction of a successful protocol on the full family must satisfy it. The additional 2 lower bound is TM51.7, not a new quartet theorem. $\square$

**Theorem 54.4 (linear all-policy necessity).** With

$$
\gamma=\frac{7-3\sqrt3}{11}=0.163986143390306\ldots,
\qquad B(h)=\gamma h+O(1),
\qquad A_U(H)\ge\gamma h-O(1).
\tag{TM.5414}
$$

The absolute error is uniform over all four cap residues.

**Proof.** Write $\lambda=L/h$. The row and column degrees in Lemma 54.2 differ by a bounded amount, independent of $h$, from $h$ times the profiles

$$
G(x)=\begin{cases}
2x-1,&1/2\le x\le2/3,\\
x/2,&2/3\le x\le1,\\
0,&\text{otherwise},
\end{cases}
\qquad
W(y)=\begin{cases}
3y-1,&1/3\le y\le1/2,\\
1-y,&1/2\le y\le1,\\
0,&\text{otherwise}.
\end{cases}
\tag{TM.5415}
$$

For example, $w-a_w$ is $\min(\lceil w/2\rceil-1,2w-h-1)$ before clipping, while the row degree is the clipped difference in (TM.5409); their floor and strict-endpoint discrepancies are bounded by constants. For $0\le\lambda\le1/3$, integrate at the clipping points:

$$
\begin{aligned}
\int_0^1[G(x)-\lambda]_+\,dx
&=\int_{(1+\lambda)/2}^{2/3}(2x-1-\lambda)\,dx
 +\int_{2/3}^{1}(x/2-\lambda)\,dx\\
&=\frac16-\frac\lambda2+\frac{\lambda^2}{4},\\
\int_0^1\min(\lambda,W(y))\,dy
&=\int_{1/3}^{(1+\lambda)/3}(3y-1)\,dy
 +\lambda\left(1-\lambda-\frac{1+\lambda}{3}\right)
 +\int_{1-\lambda}^{1}(1-y)\,dy\\
&=\frac{2\lambda}{3}-\frac{2\lambda^2}{3}.
\end{aligned}
\tag{TM.5416}
$$

Clipping by positive part or minimum is 1-Lipschitz. Each profile has finitely many pieces with bounded slopes, and a bounded jump at an endpoint contributes only a bounded Riemann-sum error. Thus floor errors summed over $O(h)$ entries and Riemann-sum errors both contribute $O(h)$ to the unnormalized sums, uniformly in $\lambda$. Replacing $L$ by $L-\epsilon_z$ on the row side changes that side by at most $h$. The difference between the two sides of (TM.5412) is therefore

$$
\sum_w[f_w-L]_+-\sum_z\min(d_z,L-\epsilon_z)
=\frac{h^2}{12}(11\lambda^2-14\lambda+2)+O(h).
\tag{TM.5417}
$$

The smaller root of $11\lambda^2-14\lambda+2$ is $\gamma$; its derivative there is $-6\sqrt3\ne0$. This polynomial decreases on $[0,1/3]$. A fixed sufficiently large constant $C$ makes (TM.5417) positive for $L\le\gamma h-C$ and negative for $L\ge\gamma h+C$ in a neighborhood of the root, for all sufficiently large $h$. Monotonicity of the exact finite inequality then gives $B(h)=\gamma h+O(1)$. Finitely many remaining $h$ are absorbed in the constant. If a competing alphabet has $L/h>1/3$, the claimed lower bound is already immediate. Theorem 54.3 proves necessity in every other case. None of this calculation asserts sufficiency of the count. $\square$

### 54.4 A smaller alphabet with at most two accepted replacements

**Theorem 54.5 (effective two-replacement construction).** For $h\ge3$ use (TM.5410) and define

$$
\begin{aligned}
T_2&=\max\left(
\left\lceil\frac{h+K-b}{3}\right\rceil,
\left\lceil\frac{K+\max(1,D)}{2}\right\rceil
\right),\\
C_2&=K-T_2,\qquad J_2=2T_2-K,\qquad c_2=h-T_2-1.
\end{aligned}
\tag{TM.5418}
$$

There is a genuinely supplied alphabet of size $T_2$ and one controller effective uniformly in $H$ that recovers the original $q_H$ on every source in $U_H$. It uses no Read, accepts at most two $\rho$, and makes at most $\lceil\log_2H\rceil+3$ source calls. Moreover $T_2=7h/18+O(1)$.

**Proof: parameter feasibility.** For $h\ge3$, $K\ge1$, $D\le K$, $b\ge2$, and $h-b\le2K$: for even $h$, $2K=h-2$; for odd $h$, $2K=h-1$. Both ceilings in (TM.5418) are at most $K$. Thus

$$
1\le T_2\le K,\quad C_2\ge0,\quad
J_2\ge\max(1,D),\quad
3T_2\ge h+K-b,
\quad1\le c_2\le h-2.
\tag{TM.5419}
$$

We give the complete supplier and decoder, abbreviating $T=T_2$, $J=J_2$, $C=C_2$, $c=c_2$. Use disjoint symbols $a_1,\ldots,a_J$ and $u_1,\ldots,u_C$, totaling $J+C=T$. If $C=0$, the latter block and all its action branches are absent.

**Supplier and simultaneous load.** In every original tag-1 column, mark its lowest $[f_w-T]_+$ members Low. The remaining consecutive interval begins at

$$
\beta_w=\max(a_w,w-T).
\tag{TM.5420}
$$

Give its first at most $J$ members label $a_{z-\beta_w+1}$. Give each remaining member, called High, label $u_{z-\beta_w-J+1}$. At most $T-J=C$ High members exist in any column. The Low members in row $z$ have exactly the interval of columns

$$
L_z=\max(z+T+1,h-z+1)\le w\le\min(2z-1,h).
\tag{TM.5421}
$$

To see this, $z$ is Low exactly when $z\in I_w$ and $z+T\le w-1$; increasing $z$ preserves the lower endpoint of that gapless column. Formula (TM.5421) is precisely these inequalities. Its length is at most

$$
[\min(z-1,h-z)-T]_+\le K-T=C.
\tag{TM.5422}
$$

The last maximum is exact: if $C>0$, take the single row $z=\lfloor h/2\rfloor+1$ and columns $w=z+T+1,\ldots,h$; they are all actual tag-1 Low members and there are $C$. If $C=0$, all Low intervals are empty. Label Low members by $u_{w-L_z+1}$, injectively in their own row. This independently reuses the same $u$ symbols assigned to High members.

Give every original tag-0 target $a_1$. For every tag-2 target at $p=z+w$, give $a_{z-\lfloor p/3\rfloor}$. Lemma 54.2 places this index in $1,\ldots,D\subseteq1,\ldots,J$. These assignments cover all three original target bands; each target receives one label, hence each actual source receives the label of its own original target.

Every Low source has $z\le h-T-1=c$. Every High source satisfies $z\ge\beta_w+J\ge a_w+J\ge b+J$. By (TM.5419),

$$
c=h-T-1<b+2T-K=b+J.
\tag{TM.5423}
$$

Consequently one public cutoff separates **every** Low from **every** High, across all columns and repeated symbols. This is the joint compatibility that column-by-column numbering alone would not supply.

**Terminal procedure (reused from TM44.5/TM51.5).** Denote by $\operatorname{Size}_H$ the actual destructive terminal acquisition of the size $M$ of its entry source. For completeness, initialize $l=0$, $u=H$, $U=0$ and maintain $l<M\le u$, $U=H-u$, current size $M+U$. While $u-l>1$, put $k=\lfloor(l+u)/2\rfloor$ and attempt one whole right context $\alpha^{u-k}$. Its positive exponent is known; its guard accepts exactly when $M\le k$. Acceptance replaces $u$ by $k$ and adds $u_{\rm old}-k$ to $U$; rejection replaces $l$ by $k$ and changes no source. Interval width decreases to at most its previous half rounded up. After at most $\lceil\log_2H\rceil$ attempts, $u-l=1$ and $M=u=H-U$. Current size is $H$. Make a final single-leaf $\alpha$ attempt, which rejects. The procedure returns the **entry** $M$ in at most $\lceil\log_2H\rceil+1$ calls. Entry $M=H$, midpoint equality, and zero accepted fill calls are all covered. No size port or partial acceptance of a rejected macro is involved.

**Executable decoder.** On label $a_i$, attempt $\rho$. If it rejects, apply $\operatorname{Size}_H$ and return $(0,1,M)$. The rejected source is the original tag-0 source. If it accepts, attempt $\rho$ once more. On second rejection, apply $\operatorname{Size}_H$, obtain $4w$, set $z=\beta_w+i-1$, and output $\tau_h(z,w)$. On second acceptance, apply $\operatorname{Size}_H$, obtain $4p$, set $z=\lfloor p/3\rfloor+i$, $w=p-z$, and output $\tau_h(z,w)$. The two guard responses distinguish original tags 0, 1 and 2, including equality at the second boundary. The relevant label is injective in that measured archive column. This does not assert that an original tag-2 source becomes tag 0 after two replacements.

On label $u_i$, attempt the one whole right context

$$
\alpha^{P},\qquad P=H-4c>0.
\qquad 4z+P\le H\ \Longleftrightarrow\ z\le c.
\tag{TM.5424}
$$

Acceptance therefore selects Low. Apply $\operatorname{Size}_H$ to obtain its entry size $M$, compute $z=(M-P)/4$, set $w=L_z+i-1$, and output $\tau_h(z,w)$. Rejection selects High and preserves the original source. Attempt $\rho$, which accepts because High is original tag 1 with $w\le h$. Apply $\operatorname{Size}_H$ to obtain $4w$, set $z=\beta_w+J+i-1$, and output $\tau_h(z,w)$. When a High member exists the archive part of its column contains exactly $J$ members, so this formula has no implicit empty-prefix convention.

All size subtractions are arithmetic on known inserted material and actual terminal guard records, not inverse source operations. After padding or filling, the current source need not be unit. The terminal procedure operates on any ambient actual source and does not consult its windows. Each branch outputs the initial target, using the public original unit-window promise.

**Coverage, effectivity and stopping.** The formulas use integer arithmetic, the public cap and the initial target at the supplier. If the supplier has an actual initial-tree archive, counting its leaves and computing its three windows gives these inputs by the pinned algorithms; authentic pairing with the running unmodified tree remains a separate supply obligation. The consumer gets only the symbol. Its choices depend on that symbol and actual guards; a fixed bracketing rule effectively names every positive $\alpha$ macro. No noncomputable cap-specific table or source-specific program is selected. The formulas supply a single algorithm for all $H$, with direct constant output at $h=2$.

The archive branch adds at most two $\rho$ attempts to the terminal procedure; the High branch adds a cutoff rejection and one accepted $\rho$; the Low branch adds one accepted cutoff. Therefore all runs stop within the stated call bound and have accepted $\rho$ depth at most two. TM30.2 and the complete source correspondence lift correctness to every qualifying word and bracketing, with its own supplied label and original running source. Finally $K=h/2+O(1)$, $D=h/6+O(1)$, $b=h/3+O(1)$; the two terms of (TM.5418) are respectively $7h/18+O(1)$ and $h/3+O(1)$. Their maximum is $7h/18+O(1)$. $\square$

### 54.5 A one-replacement alternative

**Theorem 54.6 (effective one-replacement construction).** For $h\ge3$ set

$$
v=\left\lfloor\frac{3K-h+2}{5}\right\rfloor,\quad
T_1=K-v,\quad J_1=K-2v,\quad c_1=h-T_1-1.
\tag{TM.5425}
$$

An alphabet of size $T_1$ suffices on the complete $U_H$, with no Read, at most one accepted $\rho$, and at most $\lceil\log_2H\rceil+3$ calls. Its supplier and controller are effective uniformly in $H$, and $T_1=2h/5+O(1)$.

**Proof.** For odd $h=2k+1$, $K=k$ and $3K-h+2=k+1$; for even $h=2k$, $K=k-1$ and $3K-h+2=k-1$. These are nonnegative for $h\ge3$. Also $h\ge2K+1$, so $5v\le K+1$. For $K=1$, $v=0$ and $J_1=1$. For $K\ge2$, $J_1\ge(3K-2)/5>0$, hence its integer value is at least 1. Thus $T_1\ge1$, $v\ge0$, $J_1+v=T_1$, and $1\le c_1\le h-2$.

Use symbols $a_1,\ldots,a_J$, $u_1,\ldots,u_v$, where $J=J_1$ and $T=T_1$. Here the finite column includes **both** original tags 1 and 2. Its full interval is

$$
\lfloor w/2\rfloor+1\le z\le w-1,
\qquad \widehat\beta_w=\max(\lfloor w/2\rfloor+1,w-T).
\tag{TM.5426}
$$

Mark the members $z<\widehat\beta_w$ Low and give them label $u_{w-z-T}$. Give the next at most $J$ members label $a_{z-\widehat\beta_w+1}$. Give remaining High members label $u_{z-\widehat\beta_w-J+1}$. Give all tag-0 targets $a_1$.

Low means $w\ge z+T+1$. Its exact row load is

$$
[\min(z-1,h-z)-T]_+\le K-T=v,
\tag{TM.5427}
$$

with row indices $w-z-T=1,\ldots,$ that load. After deleting Low, a column has at most $T$ members. Its High suffix has at most $T-J=v$ members. All label indices therefore fit. As in Theorem 54.5, the maximum Low row load is realized in the single row $z=\lfloor h/2\rfloor+1$ if $v>0$. If $v=0$, both Low and High are empty, and only the $a$ branch exists.

Every Low source has $z\le c_1$. Every High source has $z-J\ge\lfloor w/2\rfloor+1$, giving $w\le2(z-J)-1$. Since also $w\ge z+1$, High has $z\ge2J+2$. The choice of $v$ gives

$$
5v\le3K-h+2
\quad\Longleftrightarrow\quad c_1\le2J+1.
\tag{TM.5428}
$$

Thus the one common macro $\alpha^{H-4c_1}$ accepts exactly Low and rejects exactly High in every repeated $u$ class, including equality at $z=c_1$.

On label $a_i$, attempt $\rho$. Rejection gives original tag 0: use $\operatorname{Size}_H$ and output $(0,1,M)$. Acceptance gives entry $4w$: use $\operatorname{Size}_H$, compute $z=\widehat\beta_w+i-1$, and return $\tau_h(z,w)$. In particular the original tag is obtained by comparing recovered $z+w$ with $h$, without attempting a second replacement or observing a second window.

On label $u_i$, attempt $\alpha^{P}$ with $P=H-4c_1>0$. Acceptance gives Low: terminal entry $M$ recovers $z=(M-P)/4$ and $w=z+T+i$. Rejection leaves the original High source unchanged: one $\rho$ accepts, terminal entry gives $4w$, and $z=\widehat\beta_w+J+i-1$. In both cases return $\tau_h(z,w)$. These steps include every finite target regardless of original tag. The $u$-High branch can include original tag 2; its next windows are simply unused.

As before, each dictionary is injective in the acquired coordinate, and the simultaneous cutoff selects which meaning of a repeated symbol applies. No invisible row is consulted. Effectivity, actual-source lifting, positive macro naming, ambient semantics and stopping follow by the explicit arithmetic and the same terminal procedure. There are at most two initial calls and at most one accepted replacement. Finally $v=h/10+O(1)$ and $K=h/2+O(1)$, giving $T_1=2h/5+O(1)$. $\square$

The two constructions have different coordinates. Theorem 54.5 gives the smaller asymptotic alphabet $7h/18+O(1)$ with accepted depth at most 2. Theorem 54.6 gives $2h/5+O(1)$ with accepted depth at most 1. Each separately has the same stated total-call upper bound. Combining the smaller alphabet from one with the smaller accepted-depth bound from the other is not justified. Neither theorem prices label production, material, memory or physical duration.

### 54.6 Reused exact values through cap 31 and a fixed-archive counterexample

**Theorem 54.7 (reused small-cap exactness and explicit execution).** On the complete actual family,

$$
A_U(H)=\begin{cases}
1,&8\le H\le19,\\
2,&20\le H\le31.
\end{cases}
\tag{TM.5429}
$$

The numerical values in (TM.5429) are already published in [OR68.5][OR68], whose two-label interval continues through cap 35. The explicit protocol below establishes that at $28\le H\le31$, two labels suffice with at most one accepted $\rho$ and at most $\lceil\log_2H\rceil+3$ calls, whereas the fixed executor that ignores the label, attempts $\rho$ immediately and then applies $\operatorname{Size}_H$ requires three labels for subsequent original-target decoding.

**Proof.** The first interval is the published TM51.6–8 result. At $h=5,6$, both (TM.5418) and (TM.5425) yield alphabet 2. TM51.7 proves one label impossible for every $H\ge20$. This settles $20\le H\le27$.

Now let $h=7$, $28\le H\le31$. The complete target set consists of the following two supplied classes, using the coordinate/target convention of (TM.5407):

$$
\begin{aligned}
\mathcal C_1={}&\{(2,3),(3,4),(4,5),(5,6),(6,7),(4,6),(6,\infty),(7,\infty)\},\\
\mathcal C_2={}&\{(3,5),(5,7),(4,7),(5,\infty)\}.
\end{aligned}
\tag{TM.5430}
$$

This is a complete ordinary coverage check: at $w=3,4,5,6,7$, the finite rows are respectively $\{2\}$, $\{3\}$, $\{3,4\}$, $\{4,5\}$, $\{4,5,6\}$. The tag-0 rows are $5,6,7$. They give all twelve distinct targets, each exactly once in (TM.5430). Each finite point is realized by $\omega_{2z-w,w-z}$, and each infinite marker by $\omega_{1,z-1}$. Thus the classes cover every actual word and bracketing through TM51's source correspondence.

For label 1, first attempt the whole right macro $\alpha^{H-20}$; its positive length is 8, 9, 10 or 11. Acceptance is exactly $z\le5$. On acceptance, attempt $\rho$. If it accepts, the source was one of $(2,3),(3,4),(4,5)$: their $n+(H-20)$ are respectively $H-8,H-4,H$. Apply $\operatorname{Size}_H$ and distinguish those entry sizes. Output their own original targets. In particular **both $(2,3)$ and $(3,4)$ are original tag 2**; the latter satisfies $z+w=7$ on the equality boundary. The third is tag 1.

If that $\rho$ rejects, the source was $(4,6)$ or $(5,6)$; their unchanged-after-attempt entry sizes are respectively $4z+(H-20)=H-4,H$. Terminal acquisition distinguishes them and returns their original tag-1 targets. If the first macro rejects, the original source is unchanged and is one of $(6,7),(6,\infty),(7,\infty)$. Attempt $\rho$: acceptance uniquely identifies $(6,7)$, since $28\le H$; rejection leaves the two tag-0 sources, distinguished by terminal entry sizes 24 and 28. The uniquely identified accepting branch may stop immediately.

For label 2, first attempt the whole right macro $\alpha^{H-16}$, of positive length 12, 13, 14 or 15. Acceptance is exactly $z\le4$, selecting $(3,5)$ or $(4,7)$. Their entry sizes are respectively $H-4,H$; use $\operatorname{Size}_H$ and return the corresponding original tag-1 target, without replacement. Rejection leaves $(5,7)$ or $(5,\infty)$ unmodified. One $\rho$ attempt accepts on the former and rejects on the latter, identifying the original target immediately.

Every displayed acceptance inequality uses the entire actual candidate. An all-$\alpha$ macro contributes its length equally to $m$ and $n$, by (TM.5401); after its acceptance, a $\rho$ guard therefore compares the stated $n+P$ with $H$. Rejected macros do not insert any part of their material. Every equality case accepts. Each branch has at most two prefix calls, at most one accepted $\rho$, and at most one terminal acquisition. All choices use the label and actual responses, with the public decoder just given. This proves sufficiency on the complete family. The published quartet lower proves necessity.

For comparison, fix an executor independent of the supplied label: immediately attempt $\rho$, then apply $\operatorname{Size}_H$ to the actual resulting source. Its execution record retains every public input, action and context identity, guard response and read, but excludes the repair label subsequently supplied to the decoder. If the label was supplied earlier but ignored, this is the projection deleting only that initial label entry; decoding uses the pair of this record and the label. This fixed-execution repair task is distinct from Definition 54.1, where the controller uses the supplied label and the full record includes it. Its rejecting branch has one target per measured original $z$. Its accepting branch has one full record fiber for each $w$, containing all

$$
\lfloor w/2\rfloor+1\le z\le w-1.
\tag{TM.5431}
$$

The response prefix is the same first acceptance, and the terminal procedure is deterministic from entry $4w$. Thus these are equal **complete label-independent execution records**, including every action and response, not only equal terminal summaries. Their original targets are pairwise different. The maximum fiber has $K=\lfloor(h-1)/2\rfloor$ members, achieved at $w=h$; ranks within those fibers and one reused symbol on each singleton rejecting fiber attain $K$ labels when $h\ge3$. This is the fixed-record repair calculation of TM32, scoped to this executor.

At $h=7$, the $w=7$ record fiber contains actual targets $(4,7),(5,7),(6,7)$. Their sources have first resources $(16,28),(20,28),(24,28)$, all in $U_H$. The first replacement accepts, all resulting entry sizes are 28, and every subsequent terminal action and response is identical. Any decoder after this fixed execution needs three distinct labels. The two-label policy above is legal and succeeds on the complete family because its supplied label changes the execution itself. Hence the optimum over all policies is strictly smaller than this fixed-archive optimum. Adding the usual second replacement attempt before filling also gives the same three-target collision: it rejects for each source because each original $m+n>H$. This does not convert a fixed archive fiber count into a lower bound on arbitrary acquisition. $\square$

### 54.7 All-cap bounds, growth and supplied bits

**Corollary 54.8 (envelope of these constructions and reused growth order).** For every $H\ge8$, with the empty convention of Definition 54.1 handled separately, the reused small-cap values in (TM.5429) hold. At every $H\ge32$,

$$
\max\{2,B(\lfloor H/4\rfloor)\}
\le A_U(H)
\le\min\{T_2(\lfloor H/4\rfloor),T_1(\lfloor H/4\rfloor)\}.
\tag{TM.5432}
$$

The same two sufficient constructions and the same necessary inequality apply at $12\le H\le31$, with Theorem 54.7 supplying a separate two-label protocol at $28\le H\le31$. All bounds are finite explicit integer formulas, with positive-part and empty-block conventions stated above. As $H\to\infty$,

$$
\gamma h-O(1)\le A_U(H)\le\frac7{18}h+O(1),
\quad
\frac{7-3\sqrt3}{44}H-O(1)\le A_U(H)\le\frac7{72}H+O(1).
\tag{TM.5433}
$$

Thus $A_U(H)=\Theta(H)$, as already established by [OR68.5][OR68]. Its minimum advice-only fixed binary width, also a consequence of that published growth order, is

$$
b_U(H)=\lceil\log_2 A_U(H)\rceil=\log_2H+O(1)
\quad\text{on nonempty tasks}.
\tag{TM.5434}
$$

**Proof.** Combine Theorems 54.3–7; at $h=2$ the sole target permits direct constant output. Both constructive families are uniformly effective and cover every source, so their smaller alphabet is a valid capacity upper bound, with its own stated depth coordinate. Theorem 54.4 supplies a positive linear lower bound. For $A$ occupied symbols, any fixed-width exact code has $2^b\ge A$, while a public numbering of the symbols attains $\lceil\log_2A\rceil$ bits. The minimum-alphabet theorem therefore gives (TM.5434); $A=1$ uses the single empty bit string. Alphabet size, actual source calls and accepted replacement depth are distinct quantities. $\square$

Equations (TM.5432–3) record the envelope of the two constructions here. For comparison on the same task, [OR68.2, 68.4–5][OR68] give the lower $\max(2,\lfloor(h+10)/8\rfloor)$ and the paired upper $K-p$, where
$p=\min(\lfloor(K-1)/2\rfloor,\lfloor(3K+3-h)/4\rfloor)$ and $K-p=3h/8+O(1)$. That upper uses at most one accepted $\rho$ and at most $\lceil\log_2H\rceil+4$ calls. The $7h/18+O(1)$, depth-$\le2$ construction and the $2h/5+O(1)$, depth-$\le1$ construction here each use at most $\lceil\log_2H\rceil+3$ calls. Each alphabet, depth and call bound belongs to its own simultaneous construction. In particular OR68's smaller leading alphabet does not acquire either construction's $+3$ call guarantee. The stronger leading lower $\gamma>1/8$ comes from Theorems 54.3–4.

[OR69.2–4][OR69] supply complete same-source target dictionaries giving the exact values 2 at $36\le H\le39$ and 3 at $40\le H\le55$, with at most one accepted $\rho$ and at most $\lceil\log_2H\rceil+5$ calls. Their three-label necessity uses a thirteen-source obstruction against all ambient actions and arbitrary tree-dependent binary labels. These published numerical results are credited comparison context; the protocols and lower proofs above retain their own costs and scope.

Some exact integer instantiations illustrate the envelope of these constructions; upper columns retain their separate depth guarantees and the $+3$ call bound. The last column records known values with their sources. These entries do not extrapolate a general exact formula.

| Public caps $H$ | $h$ | Necessary alphabet $\max(2,B(h))$ for $H\ge20$ | $T_2$ (depth $\le2$) | $T_1$ (depth $\le1$) | Known exact value and source |
|---|---:|---:|---:|---:|---|
| 20–23 | 5 | 2 | 2 | 2 | 2, [OR68.5][OR68] |
| 24–27 | 6 | 2 | 2 | 2 | 2, [OR68.5][OR68] |
| 28–31 | 7 | 2 | 3 | 3 | 2, [OR68.5][OR68]; explicit protocol (TM.5430) |
| 32–35 | 8 | 2 | 3 | 3 | 2, [OR68.5][OR68] |
| 48–51 | 12 | 3 | 4 | 4 | 3, [OR69.4][OR69] |
| 80–83 | 20 | 4 | 7 | 8 | not settled by the displayed or cited bounds |
| 400–403 | 100 | 17 | 39 | 40 | not settled by the displayed or cited bounds |

### 54.8 Sources, costs, proof scope and unresolved obligations

Relative to OR68–69, the substantive refinements are the complete unit table's exact row/column load, its finite necessary inequality and profile root against all protocols, and the simultaneous cutoff allocations covering all original bands. The leading lower $\gamma h$ improves the published $h/8$ lower; the two sufficient alphabets offer their own depth guarantees with the $+3$ call bound. The complete-family cap-28–31 policy establishes its explicit two-label execution and separates unrestricted acquisition from one fixed execution. Linear growth, its logarithmic advice-width consequence and the numerical small-cap exactness are credited reuse. Actual source generation, complete Euler/bracketing coverage, $N_H$, the quartet, behavioral congruence, terminal filling and finite planning are suppliers, not new results of this appendix.

The structural proof dependencies are the first two published files below, at `e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74`; published comparison context is supplied by OR68–69 at `511f1920bceaaf9f6ec6411030fbd4da42abfbfd`:

- [FIBONACCI_ATOMIC_RELATION_GENERATION.md](https://github.com/the-omega-institute/trureturing/blob/e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), Atomic359 and Atomic360.2–4: common-source windows, positive unit witnesses, connected eight-edge criterion, all Euler words and every ordered bracketing. These match the actual source, composition and unit-window premise of (TM.5404–6).
- [RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md](https://github.com/the-omega-institute/trureturing/blob/e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), TM30.1–2: exact whole guards and behavior on the ambient $\mathcal T_H$; TM32.1–2: advice selected before execution versus repair after a fixed record; TM37.2 and TM37.7: all-context first-attempt constraints and the Low/archive/High construction architecture; TM38.1: permanent collisions on one common record; TM44.5 and TM51.5: actual terminal entry-size acquisition; TM45.1–4: original/current history pairing; TM47.1–2, 47.4 and 47.8: actual representative coverage, full-context correspondence and finite planning; TM51.1–3 and 51.6–11: the full unit task, small-cap baseline, constant-label obstruction and source-preserving production/cost boundary. These premises retain the same source, original target, actions, universal quantifiers and resource coordinates used above. The lower bound on the larger full $\mathcal T_H$ from TM37 is not transferred to the smaller $U_H$.
- [OR68 §§68.1–5][OR68]: the same conditional full-family $A_U(H)$, paired construction, all-policy $\max(2,\lfloor(h+10)/8\rfloor)$ lower, exact values through cap 35 and linear growth. Its upper has its own one-replacement/$+4$-call cost coordinates.
- [OR69 §§69.1–3][OR69]: the same task's full-family dictionaries, thirteen-source full-action binary obstruction and exact values at caps 36–55. Its upper has its own one-replacement/$+5$-call cost coordinates.

The parameter and interface correspondence is exact on nonempty tasks: OR68's $\nu=z+s$ is this appendix's $w$, and OR69's $(x,y)$ is $(z,w)$, with the same $r,s,h,H=4h+\delta$. OR69's finite $C_{r,s}$ is $\tau_h(r+s,r+2s)$, and $Z_x$ is the tag-0 target denoted here by $(z,\infty)$. Both published definitions quantify the complete actual ordered-tree family, the same initial $q_H$, arbitrary total labels authentic to that unmodified initial tree, common deterministic initialization, arbitrary acquired histories and all ambient TM30 actions with whole-candidate guards and equality acceptance. This appendix's optional empty-task convention is separate. The correspondence supplies no actual-source label producer or archive access.

No external state-identification, learning, homing or side-information coding theorem carries proof weight in this appendix. The source-specific results above are deductions from the stated pinned suppliers; no global originality claim is made. Neither TM52 nor TM53 is a premise.

The uniform programs have fixed descriptions plus public integer input $H$. Their arithmetic fields, symbol index, a bounded number of branch bits and terminal interval counts can be held in $O(\log(H+1))$ bits under compact integer/context naming. This is a sufficient controller representation for these programs, not a minimum-memory theorem. Literal action identities, expanded contexts, full records and outputs have their own representation costs. The call bound counts every attempted whole macro, rejected replacement and terminal single-leaf rejection; it does not charge accepted depth for any of them except an accepted $\rho$. A call's atomic semantics does not make its context material, guard, replacement work or physical duration unit cost.

The upper suppliers are computable from an already supplied initial target or from a genuine initial-tree archive. Archive acquisition, parsing, family membership certification, pairing with this same running tree, label production, delivery and retention remain separate. TM51.9 applies unchanged: a common-initialized TM30 program required to finish with each exact original unit tree can output only a constant. Every accepted context strictly adds leaves, and every accepted replacement adds leaves because unit sources have positive $\beta$ count; no permitted action reverses that increase. Without accepted modifications, all reads are the same unit and all attempted modifications reject, giving a common record. Thus the nonconstant supplied labels here are not produced by such a preserving consumer. An equivalent canonical witness or another tree's archive does not establish identity with the executed source.

Full word/bracketing coverage follows from the pinned ordinary theorem. The all-policy lower bound rests on the simultaneous-history proof in Theorem 54.3. Bounded enumeration does not supply either universal claim; the known exact value at $H=32$ is supplied by OR68's ordinary upper and lower proofs. These ordinary proofs carry no Lean, build or CI verification claim.

The remaining full question is explicit. The general exact function $A_U(H)$, the sharp leading alphabet coefficient or even existence of its normalized limit, and a normal form for minimum-alphabet policies under all depths and mixed positive contexts are not determined. OR68–69 settle the nonempty interval through cap 55; other particular caps can be settled when valid lower and upper bounds coincide, without supplying a general exact formula. The count (TM.5412) discards action compatibility and is not known sufficient; the cutoff constructions are not shown necessary or optimal. The whole complete family, all original bands and every ambient action remain in this unresolved optimization. The appendix does not replace that goal with a tag-1 subfamily, a fixed archive, a depth restriction or a finite solver instance. It also leaves genuinely produced/certified label costs, optimal total calls/memory, physical instrument conformity, original-tree/bracketing recovery and the persistent relation-recovery goal unsettled.

[OR68]: https://github.com/the-omega-institute/trureturing/blob/511f1920bceaaf9f6ec6411030fbd4da42abfbfd/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md#68-完整单位原树的条件补充字母表配对上界与增长必要性
[OR69]: https://github.com/the-omega-institute/trureturing/blob/511f1920bceaaf9f6ec6411030fbd4da42abfbfd/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md#69-完整单位原树在三十六至五十五上限的条件字母表精确值

## 追加锚（本行以下为增补区）

## 55. Actual unit-history compatibility: target-fiber obstructions and residue advice

A supplied symbol is useful for original-target recovery only when all sources carrying it admit one common actual acquisition strategy. Row and column allocations can satisfy their numerical constraints while forcing an irreversible collision along every permitted strategy. This appendix proves that such minimal obstructions have unbounded target arity even inside the single actual unit-history fiber. It then exhibits one jointly compatible acquisition on the complete unit family: a common padding cutoff, one replacement attempt, terminal entry-size acquisition, and retained residue advice. The resulting alphabet bound is a consequence of that actual-history certificate.

The results are ordinary mathematics on the published TM30 interface. Atomic360 actual realization, TM30 behavioral congruence, TM38 general compatibility and its earlier minimal-obstruction mechanism, and TM44/TM51 terminal acquisition retain their existing attribution. The structural premises are the Atomic/TM statements at `e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74`. No TM52 or TM53 statement is a premise. The [TM54 comparison](#TM55-L4) uses immutable revision `20b37ca68329a5d1ee0b67c28ffe2c90e89f4fce`; the [published TM55OR68–TM55OR69 comparisons](#TM55-L5) use `511f1920bceaaf9f6ec6411030fbd4da42abfbfd`. These comparisons are not premises of either new result.

### 55.1 Same actual source, original target, and conditional advice

<a id="TM55-D1"></a>
**Definition TM55.1 (the unchanged conditional task).** An actual source is a nonempty ordered binary tree

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle,
\qquad \rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\tag{TM.5501}
$$

Tree equality retains leaf order and every bracket. Write $c(t)=(a_\alpha,a_\beta)$, $m=a_\alpha+a_\beta$, $n=a_\alpha+2a_\beta$, and $E_j(t)=E(\rho^jt)$. The associative Clifford leaf product satisfies $E(\alpha)=A$, $E(\beta)=B$, $A^2=1$, $B^2=-1$, $AB+BA=1$. For the public fixed integer cap $H\ge1$, put

$$
\begin{aligned}
\mathcal T_H&=\{t:1\le\lambda(t)\le H\},\\
U_H&=\{t\in\mathcal T_H:(E_0(t),E_1(t),E_2(t))=(1,1,1)\},\\
q_H(t)&=\begin{cases}
(0,E_0(t),m),&n>H,\\
(1,c(t),E_0(t),E_1(t)),&n\le H<m+n,\\
(2,c(t),(E_0(t),E_1(t),E_2(t))),&m+n\le H.
\end{cases}
\end{aligned}
\tag{TM.5502}
$$

The tag-2 coordinates are the published $(2,\eta)$ in the equivalent composition/three-window representation of TM51.1. Throughout a run the required output is the initial $q_H(t)$ of this same tree. The current $q_H(t_{\rm cur})$ describes future behavior and does not redefine that output.

The permitted online actions are current `Read`, a whole $\rho$ attempt, and a whole left or right concatenation with a named actual nonempty positive context. `Read` returns actual current $E$ and preserves the source. A modification accepts exactly when the entire candidate has at most $H$ leaves; equality accepts. Rejection preserves the entire source and supplies no candidate read. The complete record retains public inputs, label, action/context identities, actual responses and actual reads. Every decision depends only on public initialization and that acquired record. These ambient semantics continue after the source leaves $U_H$.

For any nonempty $\mathcal F\subseteq U_H$, let $A(\mathcal F;H)$ be the least size of a finite nonempty alphabet $\mathcal L$ for which a genuinely supplied same-unmodified-initial-source function $\ell:\mathcal F\to\mathcal L$ and one effective deterministic original-interface controller satisfy

$$
\forall t\in\mathcal F:\quad
\Pi(H,\ell(t);t)\text{ stops after finitely many source calls and outputs }q_H(t).
\tag{TM.5503}
$$

The declared family is public; sources with the same label have the same public initialization. Set $A_U(H)=A(U_H;H)$ for $H\ge8$. The minimization permits arbitrary source-dependent suppliers, including dependence on leaf order and bracketing, and all finite adaptive protocols, arbitrary acquired memory, both context sides, mixed positive contexts, `Read`, and unrestricted accepted replacement depth. Necessity below imposes no factorization or computability restriction on a competing supplier. The exhibited sufficient suppliers/controllers are uniformly effective from $H$ and authentic initial-source information.

Such information can be an already supplied original target, or a parsed, certified archive authentically paired with this exact unmodified initial tree. Its acquisition, pairing, label production, delivery and retention are separate obligations. The consumer receives only the public data and the supplied symbol. A public formula or dictionary describes possible targets and does not reveal the unknown live row. An equivalent witness or another tree's archive does not authenticate the running source. There is no reset, copy, replacement of the running tree by a witness, source inverse, navigation, changed cap, hidden target/size port, or new cost observation. The empty family at $H<8$ is outside the substantive theorems; its alphabet may be assigned 0 under an empty-alphabet convention.

<a id="TM55-S1"></a>
**Reused source correspondence.** Put $h=\lfloor H/4\rfloor$ and $H=4h+\delta$, $0\le\delta\le3$. Atomic360.2–4 and TM51.2–3 give exactly

$$
\begin{gathered}
c(t)=(4r,4s),\qquad r,s\ge1,\quad r+s\le h,\\
z=r+s,\quad w=r+2s,\qquad
2\le z\le h,\quad z+1\le w\le2z-1,\\
m=4z,\quad n=4w,\quad m+n=4(z+w),\qquad
r=2z-w,\quad s=w-z.
\end{gathered}
\tag{TM.5504}
$$

For every such pair a genuine source is any fixed ordered bracketing of

$$
\omega_{r,s}
=\alpha^{2r-1}\beta^{2s}\alpha\beta^{2s-1}\alpha^{2r}\beta.
\tag{TM.5505}
$$

In Atomic360's order $(x_{00},x_{10},x_{01},x_{11};y_{00},y_{01},y_{10},y_{11})$, its eight edge multiplicities are $(r,r,r,r;s,s,s,s)$. They are positive and balanced with connected support. In the unit specialization of Atomic360.2, the unique parameters are $(u,v,w,p,q)=(0,0,0,0,0)$ and all four $\alpha$ edge counts agree, as do all four $\beta$ counts. Setting just one group to zero gives disconnected support; setting both to zero gives an excluded empty source. Thus these are genuine common-source constraints. Atomic360.3 states that every qualifying leaf word is precisely an Euler-circuit label sequence with those counts and that every ordered bracketing of every such word is an actual source. The displayed witnesses certify existence; they do not replace the family or the running source.

For $w\le h$ use the finite-target abbreviation

$$
\tau_h(z,w)=\begin{cases}
(2,(4(2z-w),4(w-z)),(1,1,1)),&z+w\le h,\\
(1,(4(2z-w),4(w-z)),1,1),&z+w>h.
\end{cases}
\tag{TM.5506}
$$

For $w>h$ the target is $(0,1,4z)$, regardless of the hidden $w$. Such a target exists exactly when $2\le z\le h$ and $2z-1>h$, with witness $\omega_{1,z-1}$. Finite points have distinct targets; hidden compositions in one tag-0 row have one target. The comparisons $w\le h$ and $z+w\le h$ are exactly $4w\le H$ and $4(z+w)\le H$ at every cap residue. This does not prove that the unrestricted optimum depends only on $h$.

<a id="TM55-S2"></a>
**Reused history correspondence and terminal acquisition.** TM30.1 gives whole guards and ordered source transport; TM30.2 gives equality of all future responses for equal current $q_H$ under common initialization. TM38.1 applies when the complete past records are also equal: equal current $q_H$ paired with different original targets is a permanent collision. TM45.1–4 retains those original/current pairs and the ordered known outer factors. Therefore the extra size of a stored record cannot repair a difference that never entered it.

Before the first $\rho$, accepted contexts on a common history contribute $(U,V)$ to current/next size, with

$$
0\le U\le V,\qquad
m_{\rm cur}=m+U,\quad n_{\rm cur}=n+V,
\qquad E_{j,\rm cur}=L_jE_j(t)R_j.
\tag{TM.5507}
$$

Each positive context $v$ has $d_0(v)\ge1$ and $d_0(v)\le d_1(v)\le2d_0(v)$, irrespective of its side. The factors $L_j,R_j$ are the actually ordered known products from those contexts. They are not commuted. A rejection changes neither contributions nor factors. A first accepted replacement changes the resource pair to $(n+V,m+n+U+V)$ and the current read to $L_1E_1(t)R_1$.

Write $\operatorname{Size}_H$ for the already published TM51.5 terminal entry-size procedure, directly reusing TM44.5 proof equations (TM.4419–20). Its sole source hypothesis is an ambient entry tree with integer size $1\le M\le H$. It uses no `Read` or replacement, returns that entry $M$, ends at current size $H$, and makes at most $\lceil\log_2H\rceil+1$ whole source calls including the final single-$\alpha$ rejection. Its controller maintains $l<M\le u$, inserted size $H-u$, and actual current size $M+H-u$; the positive right macro of length $u-\lfloor(l+u)/2\rfloor$ accepts exactly when $M\le\lfloor(l+u)/2\rfloor$. All uses below check the entry hypothesis. This is a cited acquisition lemma, not a new proof wrapper or size port.

TM47.2's lifting hypothesis is also concrete here: the actual witnesses cover every allowed initial target, and sources with the same initial $q_H$ and supplied label have the same complete record, stopping output and accepted depth by TM30.2. Thus a controller correct on the representatives is correct on every qualifying word and ordered bracketing in those target fibers. A lower argument may instead choose any actual representative in each target fiber and retain its actual supplied label; no target factorization is assumed.

### 55.2 Minimal incompatible target fibers wholly inside the unit history

<a id="TM55-T2"></a>
**Theorem TM55.2 (unit target-fiber minimal obstructions).** For every integer $k\ge2$, every $H$ with $h\ge4k$, and every cap residue, set

$$
a=h-2k,\qquad b=h-k,\qquad
S_{k,h}=\{(a+i,a+i+1),(a+i,b+i):0\le i<k\},
\tag{TM.5508}
$$

and let $\mathcal F_{k,H}$ be the full preimage in $U_H$ of the $2k$ targets $\tau_h(z,w)$ indexed by $S_{k,h}$. All are distinct genuine original tag-1 targets in the same unit-window fiber. No common-label controller recovers them under arbitrary original finite protocols. Every nonempty proper target subfamily, including the entire actual fibers of its selected targets, has a literal effective one-label controller. Moreover

$$
A(\mathcal F_{k,H};H)=2.
\tag{TM.5509}
$$

Minimality means deletion of an entire target fiber. Deleting one tree while leaving another realization of its target does not remove this obstruction.

**Proof.** First verify actual membership. We have $a\ge2k\ge4$, $a\ge h/2$, and $a\le z\le b-1$. The listed next coordinates obey

$$
z+1\le w\le h-1,\qquad w\le2z-1,\qquad z+w\ge2a+1>h.
\tag{TM.5510}
$$

For the high point in row $i$, the inequality $w\le2z-1$ follows from $2z-w=h-3k+i\ge k+i\ge2$; for the low point it is immediate. Thus $r=2z-w\ge1$, $s=w-z\ge1$, and the witness (TM.5505) belongs to $U_H$ and has $n\le H<m+n$ for every $\delta$. The two points in each row have different $w$ since $k\ge2$, and different rows have different $z$. All $2k$ original targets are distinct.

Suppose a successful deterministic controller is initialized with one common label. Choose any one actual realization of every listed target. Follow the two row-0 sources $(a,a+1)$ and $(a,b)$. Before the first $\rho$ attempt their current sizes are both $4a$ plus the same accepted contribution, and their initial $E_0$ is 1. A context on either side has the same whole guard on both; reads give the same ordered $L_0\,1\,R_0$. Induction over actions gives equal complete records, including rejected macros, every read and every context identity. They cannot stop during this prefix with two different correct outputs. Pointwise finite stopping rules out a path that never reaches a first $\rho$. Hence a finite common first-$\rho$ prefix exists.

Let $U,V$ be its final accepted contributions and define the mathematical cutoff

$$
c_*=(H-V)/4.
\tag{TM.5511}
$$

It need not be an integer and is not a consumer observation. If $c_*<a+1$, both row-0 first replacements reject. They have equal past records and current sizes $4a+U$, equal current reads, and both are currently tag 0 since their next candidates exceed $H$. TM30.2/TM38.1 then gives a permanent collision of different original targets. Successful recovery consequently requires $c_*\ge a+1$.

We need the same actual prefix on later rows, rather than separately feasible prefixes. Every listed source with $a\le z\le c_*$ follows this complete prefix. Prove this by induction over its actions. Assuming the preceding records agree, deterministic control chooses the same action and context. For any context accepted on row 0, let $U'$ be the cumulative current contribution after that acceptance. Positivity and $d_0\le d_1$ give $U'\le V$, so its candidate on the later source satisfies

$$
4z+U'\le4c_*+V=H.
\tag{TM.5512}
$$

It accepts there too. Any context rejected on row 0 has candidate size $4a$ plus the same previous contribution and the same context length greater than $H$; replacing $a$ by $z\ge a$ preserves rejection. Reads agree as $L_0\,1\,R_0$, with the actual left and right order. Read does not change source or contributions. This completes the induction, covering arbitrary positive mixed contexts on either side and every intervening read or rejected attempt. It uses no restriction on future accepted depth or memory.

Now if $c_*\ge a+i$, both sources in row $i$ reach this same first replacement instruction. Their next coordinates are $a+i+1$ and $b+i$, with the first smaller than the second. If $c_*<a+i+1$ they both reject, giving the same row collision as above. Starting with $c_*\ge a+1$ and applying this implication through rows $1,\ldots,k-1$ forces

$$
c_*\ge a+k=b.
\tag{TM.5513}
$$

The high point $(a,b)$ and the last low point $(b-1,b)$ therefore follow the same complete prefix and both accept the first $\rho$. Their new current sizes are both $4b+V$, and their new reads are both $L_1\,1\,R_1$, because both original $E_1$ values are 1. Their next sizes are $4(z+b)+U+V>H$ by original tag 1. They have equal current tag-0 $q_H$ and equal acquired records, but different original targets. The same permanent-collision lemma excludes every continuation. This contradiction proves the arbitrary-policy impossibility.

For minimality, delete either target in a public row $j$, $0\le j<k$, and set

$$
c_j=a+j,\qquad P_j=H-4c_j>0.
\tag{TM.5514}
$$

There is now one survivor in row $j$. Attempt the whole right macro $\alpha^{P_j}$, with a fixed ordered bracketing. It accepts exactly when $z\le c_j$, that is, $i\le j$. On acceptance attempt one $\rho$: its guard is $4w+P_j\le H$, exactly $w\le c_j$. This selects precisely the low points in rows $i<j$, whose $w=a+i+1$ are all distinct. The rejecting portion contains the high point in each earlier row and the unique survivor in row $j$, one target in each distinct $z$ row. In either portion apply $\operatorname{Size}_H$ to the actual entry source. On replacement acceptance it returns $M=4w+P_j$; on rejection it returns $M=4z+P_j$. Recover the indicated coordinate by subtracting the known $P_j$ and dividing by four, then output the corresponding original target from the public deletion dictionary. These dictionaries are injective in the acquired coordinate within each actual guard branch.

On initial macro rejection the original source is unchanged, with $i>j$. Attempt $\rho$, which accepts since every original point has $w\le h$. The only repeated column in the full set is $b$, shared by $(a,b)$ and $(b-1,b)$; row 0 is absent from this tail. All tail columns are therefore distinct. Terminal acquisition returns $4w$ and the tail dictionary gives the original target. Every terminal entry is an actual accepted current source of size in $[1,H]$. Equalities accept, rejected whole macros insert no material, and the protocol has no `Read`, at most one accepted replacement and at most $\lceil\log_2H\rceil+3$ source calls including terminal rejection. Restricting one such controller proves recovery of every smaller nonempty proper target subfamily.

For two labels on the full family, give label 1 exactly to the fiber of $(a,b)$ and output that public original target directly. Give label 2 to every other target fiber. Their columns are distinct, so immediate $\rho$ followed by $\operatorname{Size}_H$ returns $4w$ and identifies their original target. This supplier is uniformly computable from authentic original-target information; it is a conditional supply assertion. The one-label impossibility proves necessity of two. The witnesses cover each target, and the labels and decoders agree on its entire original-target fiber. TM47.2 with TM30.2 therefore lifts every sufficient controller to every qualifying word and ordered bracketing; the impossible representative selection could also have been any such realization. $\square$

### 55.3 What static allocation fails to retain

<a id="TM55-C3"></a>
**Corollary TM55.3 (unbounded arity and failed allocation certificates).** Within actual unit sources that are all initially tag 1, no cap-independent fixed target arity determines common-label recovery by checking all subfamilies of that arity. In particular pairwise compatibility is insufficient. The following static tests on a declared target class are also insufficient: one rejected/stopping allocation per row, one accepted allocation per column, the accepted member being maximal in its column, aggregate column-excess versus row capacity, and every column-subset capacity test for that allocation relaxation.

**Proof.** For any fixed $K$, choose $k\ge2$ with $2k>K$ and $h\ge4k$. By Theorem TM55.2, every subfamily of at most $K$ target fibers is recoverable with a common label while the whole $2k$-target family is not. This disproves the asserted bounded-arity characterization.

For the static tests, assign the high points to $P$ and the low points to $C$:

$$
P=\{(a+i,b+i):0\le i<k\},\qquad
C=\{(a+i,a+i+1):0\le i<k\}.
\tag{TM.5515}
$$

There is exactly one $P$ member in each row, and $C$ has distinct columns. Its member in column $b$ is the largest row $b-1$, above the $P$ member in row $a$; all other $C$ columns are singleton. Thus even TM37.2's stronger local maximality condition holds. Only column $b$ has degree two; every other column has degree one. With one symbol the aggregate excess $\sum_w[\deg(w)-1]_+$ is 1 and total row capacity is $k$. For every subset $W$ of columns, the demand $\sum_{w\in W}[\deg(w)-1]_+$ is 0 unless $b\in W$, when it is 1; the explicit $P$ assignment supplies that demand without exceeding any row capacity. It is also a certificate for the corresponding bipartite allocation problem, so all its column-subset capacity inequalities hold.

Nevertheless this static $P/C$ assignment cannot be the first-attempt classification of a successful actual history, and no alternative actual strategy succeeds with one label. The common-prefix proof shows the missing numerical linkage: row releases $[a+i,a+i+1]$ join at their endpoints into $[a,b]$, which contains the repeated-column span $[a,b]$. This is the already published TM38.3–4 release/deadline mechanism, now instantiated entirely in one unit-history fiber. The new result is the target-minimal unit embedding and its literal protocols, not the general mechanism or an abstract coloring theorem. $\square$

For an arbitrary successful supplier on the complete $U_H$, let $\mathcal L_\tau$ be the labels it actually supplies on realizations of original target $\tau$. The stronger source-specific necessary condition is

$$
\bigcap_{(z,w)\in S_{k,h}}\mathcal L_{\tau_h(z,w)}=\varnothing.
\tag{TM.5516}
$$

Indeed a symbol in this intersection would permit choosing one genuine realization of every displayed target with that same symbol, contradicting Theorem TM55.2. Competing labels may depend on all source details. The condition does not require a target-dependent supplier, and it is not asserted sufficient.

The conclusion concerns a proposed acquisition certificate for a label class. It does not prove a numerical separation $A_U(H)>B(h)$ for a complete-family necessary count such as [TM54 (TM.5412)](#TM55-L4): some different full-family partition could still meet that count and use compatible histories. Nor is the restricted value 2 a complete-family upper bound.

<a id="TM55-E4"></a>
**Example TM55.4 (a four-target unit obstruction).** At $h=8$, $H=32,33,34,35$, $k=2$, the targets are

$$
(4,5),\ (4,6),\ (5,6),\ (5,7),
\qquad c=(12,4),(8,8),(16,4),(12,8),
\tag{TM.5517}
$$

respectively. All are original tag 1 and have actual witnesses (TM.5505). The releases force $c_*\ge5$ and then $c_*\ge6$; the two column-6 targets then permanently collide. Deleting either row-0 target gives the literal cutoff 4, and deleting either row-1 target gives cutoff 5. This is a pairwise-compatible class with no common-label strategy. It is a falsifier of pairwise or static allocation sufficiency, not evidence from a search exhausting arbitrary protocols.

### 55.4 One actual cutoff and one residue supplier on the complete family

<a id="TM55-P5"></a>
**Proposition TM55.5 (one-cutoff residue certificate).** Suppose $h\ge2$ and integers $L,c$ satisfy

$$
L\ge2,\qquad 1\le c<h,\qquad c\le2L+2,\qquad h-c\le L-1.
\tag{TM.5518}
$$

With $H,L,c$ public, $L$ conditional supplied symbols suffice for original-target recovery on the complete $U_H$. One uniform supplier/controller uses no `Read`, at most one accepted $\rho$, and at most $\lceil\log_2H\rceil+3$ source calls. Its executor is independent of the supplied label; the label is retained for original-target decoding.

**Proof.** Let the Euclidean residue representative and the whole padding length be

$$
\operatorname{rep}_L(x)=1+((x-1)\bmod L)\in\{1,\ldots,L\},
\qquad P=H-4c>0.
\tag{TM.5519}
$$

In particular $\operatorname{rep}_L(0)=L$. Supply

$$
\ell_H(t)=\begin{cases}
\operatorname{rep}_L(w-z),&w\le h,\\
\operatorname{rep}_L(c-z),&w>h\text{ and }z\le c,\\
1,&w>h\text{ and }z>c.
\end{cases}
\tag{TM.5520}
$$

For a finite original target, $(z,w)$ is recoverable from its retained composition. For a tag-0 target, the rule uses only its original $z$; its hidden $w$ is unused. Thus the supplier is a function of the original target on all three original bands, and hence is uniformly computable from authentic original-target information or a certified same-tree archive. This sufficiency factorization is proved for this construction only; it is not an optimization restriction.

On the running original source first attempt the whole right context $\alpha^P$, then attempt $\rho$ exactly once whether padding accepted or rejected. Apply $\operatorname{Size}_H$ to the resulting actual source. Let $M$ be the acquired entry size of this terminal procedure, and let $A,R$ denote the two actual response bits. The actual histories are

| Padding / replacement | Exact original-source condition | Terminal entry $M$ |
|---|---|---|
| $AA$ | $z\le c$, $w\le c$ | $4w+P$ |
| $AR$ | $z\le c$, $w>c$ | $4z+P$ |
| $RA$ | $z>c$, $w\le h$ | $4w$ |
| $RR$ | $z>c$, $w>h$ | $4z$ |

These are guard facts, not pre-supplied source coordinates. The padding candidate has size $4z+P$, so it accepts exactly when $z\le c$. On acceptance the actual composition acquires $(P,0)$: its next size is $4w+P$, and replacement accepts exactly when $w\le c$. On rejection the entire padding is absent and the source is still original; replacement then accepts exactly when $4w\le H$, equivalently $w\le h$. A rejected replacement leaves that actual source unchanged. The replacement acceptance changes it to its own actual $\rho$ image. All four terminal entries are sizes of resulting ambient sources in $[1,H]$ by the true guards, so TM51.5 applies even when the current source is no longer a unit source.

Let $i$ be the retained symbol. The decoder is

$$
\begin{array}{c|l}
AA & w=(M-P)/4,\quad z=w-i;\quad\text{output }\tau_h(z,w),\\
AR & z=(M-P)/4,\quad j=(z+i-c)\bmod L;\\
   & \quad j=0:\ \text{output }(0,1,4z);\quad
      j>0:\ w=c+j,\ \text{output }\tau_h(z,w),\\
RA & w=M/4,\quad z=w-i;\quad\text{output }\tau_h(z,w),\\
RR & \text{output }(0,1,M).
\end{array}
\tag{TM.5521}
$$

Here $j\in\{0,\ldots,L-1\}$ is the Euclidean remainder. These are formulas on the declared actual record image, not assertions that arbitrary tuples have actual source realizations.

To prove the $AA$ and $RA$ formulas, write $d=w-z=s\ge1$. Positivity of $r=z-d$ gives $w=z+d\ge2d+1$. If a finite target has $d>L$, then

$$
w\ge2L+3>c,\qquad
z=w-d\le h-L-1\le c-2.
\tag{TM.5522}
$$

Every such large gap therefore lies in the crossing history $AR$. In $AA$ or $RA$ we have $1\le d\le L$, hence $i=\operatorname{rep}_L(d)=d$ and $z=w-i$ is exact. These branches are finite since their replacement accepts; original tags 1 and 2 are both decoded by (TM.5506), which compares the recovered initial $z+w$ with $h$.

In the finite part of $AR$, the possible columns are $c+1,\ldots,h$, a consecutive interval of length at most $L-1$. Since $i\equiv w-z\pmod L$,

$$
j\equiv z+i-c\equiv w-c\pmod L,\qquad
1\le w-c\le h-c\le L-1.
\tag{TM.5523}
$$

Thus $j=w-c$ and the original finite target is decoded exactly. For a tag-0 source in the same $AR$ branch, its supplied symbol instead obeys $i\equiv c-z\pmod L$, so $j=0$. No finite crossing column uses that residue. The tag-0 target at an acquired row occupies the missing residue, including the cutoff row $z=c$ where its symbol is $L$. In $RR$, rejection of the unpadded original replacement means original tag 0 and $M=4z$, exactly its original retained target. This exhausts every initial source without observing its hidden row or composition.

The recorded guard pair separates the four dictionaries before terminal acquisition; inside each history $M$ and $i$ determine the original target. The terminal procedure may alter both source and current windows, but its acquired entry $M$ is retained together with these response bits and the supplied symbol. Consequently the output remains the initial target rather than the terminal current $q_H$. Equality is retained in both guard tests, particularly $z=c$, $w=c$, and unpadded $w=h$. The divisions by four subtract $P$ on precisely the padded histories, so every cap residue is handled.

There are exactly two prefix source calls and at most $\lceil\log_2H\rceil+1$ terminal calls, including its final rejection. Only the prefix $\rho$ can be an accepted replacement. All named contexts are genuine nonempty all-$\alpha$ trees with a fixed public bracketing convention. The arithmetic, branch selection and terminal control form one uniform algorithm and use no `Read`. Labels and decoders are constant on the original-target fibers; (TM.5504–6) and the checked TM47.2 lifting hypotheses give correctness on all qualifying words and ordered bracketings, each executed on its own source. $\square$

<a id="TM55-T6"></a>
**Theorem TM55.6 (complete-family one-third bound with simultaneous costs).** For every integer $H\ge8$, put

$$
L=\left\lfloor\frac{h+1}{3}\right\rfloor
=\left\lceil\frac{h-1}{3}\right\rceil
=\left\lfloor\frac{H+4}{12}\right\rfloor.
\tag{TM.5524}
$$

One conditional supplier and one controller effective uniformly in $H$ recover every original target in the complete actual $U_H$ and satisfy simultaneously

$$
A_U(H)\le L,\qquad
\operatorname{Read\ calls}=0,\qquad
\operatorname{accepted\ }\rho\le1,\qquad
\operatorname{source\ calls}\le\lceil\log_2H\rceil+3.
\tag{TM.5525}
$$

For $h\ge5$ the construction is exactly Proposition TM55.5 with $c=h-L+1$ and $P=H-4c$. For $h=2,3,4$ it uses one symbol, omits padding, attempts $\rho$ once and then uses the same terminal acquisition. This is one whole construction; no cost coordinate is borrowed from another supplier.

**Proof.** At $h\ge5$, $L\ge2$, $1\le c<h$, $h-c=L-1$, and $h\le3L+1$ implies $c\le2L+2$. The three residues of $h$ make the parameter check explicit:

| $h$ | $L$ | $c$ | $P$, where $H=4h+\delta$ |
|---|---:|---:|---:|
| $3q$ | $q$ | $2q+1$ | $4(q-1)+\delta$ |
| $3q+1$ | $q$ | $2q+2$ | $4(q-1)+\delta$ |
| $3q+2$ | $q+1$ | $2q+2$ | $4q+\delta$ |

In the first two rows $h\ge5$ implies $q\ge2$; in the third it implies $q\ge1$. Hence every padding length is positive even at $\delta=0$. All hypotheses of Proposition TM55.5 hold, giving (TM.5525). The identity with $\lfloor(H+4)/12\rfloor$ follows for every $\delta=0,1,2,3$ by the same three residues.

For $h=2$, the sole target is $(0,1,8)$: replacement rejects and terminal acquisition returns 8. For $h=3$, the sole finite pair is $(2,3)$; for $h=4$, the finite pairs are $(2,3)$ and $(3,4)$. All other actual targets in these bases are tag 0. More uniformly, a finite pair has $w\ge2d+1$, so $d\le\lfloor(h-1)/2\rfloor\le1$ and hence $d=1$. Immediate replacement rejection leaves the original tag-0 source, whose terminal entry $M$ gives $(0,1,M)$. Acceptance gives $M=4w$; set $z=w-1$ and return $\tau_h(z,w)$. The original band follows from the recovered initial coordinates, and all available windows are supplied by the unit-family promise. These bases use one symbol and no padding, at most one accepted replacement and at most $\lceil\log_2H\rceil+2$ calls. They issue no empty context or fictitious padding response. Source coverage and lifting are the same as above. $\square$

The upper alphabet is $h/3+O(1)=H/12+O(1)$ with the displayed replacement/call guarantees jointly. It is an unrestricted-capacity upper bound witnessed by a particular executor; it does not assert that arbitrary minimum-alphabet controllers have its cutoff form or depth.

### 55.5 A decisive residue falsifier and original/current distinction

<a id="TM55-E7"></a>
**Example TM55.7 (constant tag-0 reuse loses an original target).** At $H=40$, $h=10$, $L=3$, $c=8$, $P=8$, take

$$
\begin{aligned}
u&=\omega_{2,4},\quad (z,w)=(6,10),\quad q_{40}(u)=(1,(8,16),1,1),\\
v&=\omega_{1,5},\quad (z,w)=(6,11),\quad q_{40}(v)=(0,1,24).
\end{aligned}
\tag{TM.5526}
$$

The finite source receives $i=\operatorname{rep}_3(4)=1$. Giving the tag-0 source the same constant symbol 1 would make both padding attempts accept with current size 32, and both replacements reject: their candidates have sizes 48 and 52. They have the same action identities and two actual response bits, and current $E=1$ since $A^8=1$. Their current targets are both $(0,1,32)$ but their initial targets differ. TM38.1 excludes every common continuation, including the identical terminal procedure. Correct supply gives the tag-0 source $i=\operatorname{rep}_3(8-6)=2$, reserving $j=0$ in its acquired row. The example falsifies that naive supply rule, not an unrestricted alphabet optimum.

Equality in the complete theorem is substantive. For example $h=7$, $L=2$, $c=6$, and $H=28+\delta$ give $P=4+\delta$. The actual point $(5,6)$ accepts padding and then replacement at candidate size $4\cdot6+P=H$. Its terminal entry is exactly $H$; all interval probes and the final single-leaf attempt reject, yet the retained symbol 1 and recovered $w=6$ decode $z=5$. The actual tag-0 row $z=6$ also accepts padding at size $H$ but rejects replacement; its symbol is $\operatorname{rep}_2(0)=2$. These are different recorded histories, not a same-history collision. At $h=5$, $(2,3)$ has $z+w=h$ and is decoded as original tag 2, preserving the third original band even though the executor attempts replacement only once.

### 55.6 Source locators, finite falsification, and remaining obligations

<a id="TM55-L1"></a>
[Atomic source at the immutable pin](https://github.com/the-omega-institute/trureturing/blob/e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md): Atomic359.1–3 supplies ordered triple multiplication, the four-state transition table and unique common-source parameters; Atomic360.2 supplies the eight nonnegative edge counts, balance and necessary connected support; Atomic360.3 supplies every Euler word and ordered bracketing; Atomic360.4 supplies precisely the positive unit compositions and (TM.5505). Their actual pinned text establishes both existence and completeness used in [the source correspondence](#TM55-S1). Connected support is checked in each displayed witness; no separately attainable windows are spliced.

<a id="TM55-L2"></a>
[TM source at the immutable pin](https://github.com/the-omega-institute/trureturing/blob/e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md): TM30.1–2, equations (TM.3001–4), supplies exact guards, rejection preservation, source transport and behavioral congruence. TM31.1 fixes pointwise finite stopping and the original-target task. TM37.2 supplies the local first-attempt restrictions used as explicitly necessary static tests in [Corollary TM55.3](#TM55-C3). TM38.1 supplies the permanent same-record collision, TM38.3–4 the general upper-band release/deadline criterion, and TM38.6–7 the earlier general unbounded minimal obstructions. [Theorem TM55.2](#TM55-T2) gives a new minimal embedding wholly within the actual unit history; none of those generic mechanisms is reclaimed as new.

<a id="TM55-L3"></a>
At that same TM pin, TM44.5 proof equations (TM.4419–20) and TM51.5 supply the terminal procedure with its final rejection, no `Read`, and sole entry-size hypothesis. Every invocation above has an actual ambient entry in $[1,H]$. TM45.1–4, especially (TM.4505) and (TM.4511–14), supplies ordered outer-factor and $(U,V)$ transport, exact actual-history filtering and preservation of initial/current pairing. TM47.1–2, (TM.4701–2), requires authenticated representatives with complete initial-target coverage, supplied here by Atomic360 and TM51.2–3. TM47.4 supplies full positive-context correspondence; its generic normalization and TM47.8's finite planning are prior results, not new claims or optimization restrictions. TM51.9–11 supplies the exact-source-preserving production obstruction and separated costs.

<a id="TM55-L4"></a>
The [TM54 comparison at immutable revision `20b37ca68329a5d1ee0b67c28ffe2c90e89f4fce`](https://github.com/the-omega-institute/trureturing/blob/20b37ca68329a5d1ee0b67c28ffe2c90e89f4fce/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#54-complete-unit-family-supplied-advice-linear-capacity-and-actual-acquisition) uses the same complete $U_H$, initial $q_H$, and conditional same-unmodified-initial-source label contract. For every integer $H\ge12$, hence $h\ge3$, put $K=\lfloor(h-1)/2\rfloor$, $D=\lfloor(h+1)/6\rfloor$, and $b=\lceil(h+2)/3\rceil$. TM54 Theorem 54.5 supplies alphabet $T_2=\max(\lceil(h+K-b)/3\rceil,\lceil(K+\max(1,D))/2\rceil)=7h/18+O(1)$, no `Read`, at most two accepted $\rho$, and at most $\lceil\log_2H\rceil+3$ whole source calls including terminal rejection. On that same domain, [Theorem TM55.6](#TM55-T6) supplies $\lfloor(h+1)/3\rfloor=h/3+O(1)$ symbols, no `Read`, at most one accepted $\rho$, and the same $+3$ call bound, all in its own single construction.

For every integer $H\ge12$, TM54 Theorem 54.6 separately supplies alphabet $T_1=K-\lfloor(3K-h+2)/5\rfloor=2h/5+O(1)$, no `Read`, at most one accepted $\rho$, and at most $\lceil\log_2H\rceil+3$ whole source calls including terminal rejection. Theorem TM55.6 gives its $h/3+O(1)$ upper with these simultaneous depth and call bounds on the same domain, and also covers $8\le H\le11$ by its explicit base case. At every $H=400,401,402,403$, $h=100$ and the three displayed alphabet bounds are respectively $T_2=39$, $T_1=40$, and $L=33$. Each alphabet, accepted depth and call bound belongs to its own construction; none prices authentic supply, material or physical duration.

TM54's necessary count (TM.5412) and leading lower coefficient $(7-3\sqrt3)/11$ likewise serve only as comparisons. Neither those lower results nor either TM54 upper construction is used in the proofs of Theorems TM55.2 or TM55.6.

<a id="TM55-L5"></a>
Panteleev's *Preset Distinguishing Sequences and Diameter of Transformation Semigroups*, van den Bos–Vaandrager's *State Identification for Labeled Transition Systems with Inputs and Outputs*, and Charpenay–Le Treust–Roumy's *Zero-Error Coding for Computing with Encoder Side-Information* are mature background sources already attributed in the pinned TM31.7 and TM32.2. No external state-identification, zero-error coding, automata correspondence or coloring theorem carries proof weight here. The source-specific arguments rest on the pinned Atomic/TM statements and the ordinary proofs above. No global originality or literature-priority certification follows.

[TM55OR68 Definition 68.1][TM55OR68] and [TM55OR69 Definition 69.1][TM55OR69] use exactly the conditional full-unit task of Definition TM55.1 on nonempty domains. TM55OR68's $\nu=z+s$ is this appendix's $w$, and TM55OR69's $(x,y)$ is $(z,w)$, with the same $r,s,h,H=4h+\delta$. TM55OR69's finite $C_{r,s}$ is $\tau_h(r+s,r+2s)$, and $Z_x$ is $(0,1,4z)$. Their definitions retain every actual word and ordered bracketing, all three original target bands, arbitrary tree-dependent labels authentic to the same unmodified initial source, common deterministic initialization, arbitrary acquired histories and all ambient TM30 actions with whole guards, equality acceptance and unchanged rejection. The optional empty-family convention here is separate; this correspondence supplies no archive access or label producer.

[TM55OR68 Theorems 68.2, 68.4 and Corollary 68.5][TM55OR68] already establish $A_U(H)=\Theta(H)$. For every integer $H\ge20$, their paired upper has alphabet $K-p=3h/8+O(1)$, where $K=\lfloor(h-1)/2\rfloor$ and $p=\min(\lfloor(K-1)/2\rfloor,\lfloor(3K+3-h)/4\rfloor)$, jointly with no `Read`, at most one accepted $\rho$ and at most $\lceil\log_2H\rceil+4$ whole source calls including terminal rejection. Its execution costs remain those of that paired construction. Theorem TM55.6 supplies its own $h/3+O(1)$ alphabet, one-replacement and $+3$-call certificate; it does not reestablish linear growth as a new result.

The published exact values are 1 at $8\le H\le19$ and 2 at $20\le H\le35$ by [TM55OR68.5][TM55OR68], extended to 2 at $36\le H\le39$ and 3 at $40\le H\le55$ by [TM55OR69.4][TM55OR69]. TM55OR68's paired protocol on its nonempty two-label interval has the one-replacement/$+4$-call bound above; TM55OR69's complete target dictionaries for $36\le H\le55$ have no `Read`, at most one accepted $\rho$ and at most $\lceil\log_2H\rceil+5$ calls including terminal rejection. These numerical classifications are credited published results, with their own execution costs and ordinary mathematical evidence status; they carry no Lean verification claim.

The same-task [TM55OR70 comparison][TM55OR70] supplies a separate Ferrers necessary bound $A_U(H)\ge L_F(H)$, with $L_F(H)=(2-\sqrt2)H/16+O(1)$ and $L_F(H)=4$ for $72\le H\le87$. It supplies no matching upper bound or general exact function. This is comparison context only, not a premise or a new result of TM55; its execution costs and other resource coordinates remain separate.

<a id="TM55-V8"></a>
**Validation TM55.8 (bounded falsifiers, separate from universal proof).** The recorded finite checks use integer Clifford coefficients in the basis $1,A,B,AB$, literal composition updates for accepted whole modifications, unchanged rejection, actual terminal entry records, and decoded retained original targets. The falsification conditions are a bad unit witness/edge correspondence, a differing whole guard, nonpositive issued context, failed equality or small base, duplicate same-label complete-record targets, incorrect original-target output, failed deletion dictionary, or excess depth/calls. A one-label successful arbitrary controller on a whole displayed chain would instead falsify the universal obstruction proof, which is not tested by enumerating bounded prefixes.

The recorded bounded checks found no falsifying case in the following domains:

| Falsifier scope | Cases checked | Result |
|---|---:|---|
| Displayed words, $1\le r,s\le12$: composition, three exact unit products, eight state-edge counts | 144 | All correct |
| Every leaf word of compositions $(4,4),(4,8),(8,4)$: unit products iff the specified Euler counts hold | 1,060 | Correspondence holds |
| Every ordered bracketing of each qualifying eight-leaf word, with literal structural $\rho$ and $\rho^2$ | 3,432 | All three products are 1 |
| Terminal entry acquisition, $1\le M\le H\le257$ | 33,153 | Entry, unchanged rejection, equality and call bound correct |
| Complete positive compositions, $2\le h\le96$, all $\delta=0,1,2,3$ | 589,760 | Original target, symbol range/factorization, complete-record decoding, depth and call bounds correct |
| Chains, $8\le h\le64$, $2\le k\le\lfloor h/4\rfloor$ | 435 target tables | Membership, distinctness and static allocation correct |
| Every single-target deletion on these chains, every surviving target, all cap residues | 348,760 literal executions | Original target and stated simultaneous bounds correct |
| The second class of the two-label chain supplier, all displayed chains and cap residues | 20,620 literal executions | Distinct-column decoding correct |
| $h=8,k=2$, all cap residues, every prefix of length at most 2 from Read and both sides of all positive words of length 1–4 | 15,132 prefixes | Common-prefix propagation and forced accepting collision arithmetic correct |

The complete-family branch totals are $AA=133{,}044$, $AR=139{,}360$, $RA=57{,}660$, $RR=259{,}656$; the separate small bases have 12 accepting and 28 rejecting replacement runs. This includes every hidden composition of each collapsed tag-0 target in the range. The finite reserved-residue counterexample in Example TM55.7 was also checked. Finite arithmetic evidence does not prove an all-cap theorem, exhaustive all-word coverage, arbitrary-policy impossibility or optimality; those conclusions depend on the ordinary proofs and checked published correspondence. No Lean, kernel, build or physical instrument verification is asserted.

<a id="TM55-O9"></a>
**Unresolved obligations TM55.9.** The general exact function $A_U(H)$, a sharp leading coefficient, and existence of a normalized limit remain open. The exact intervals cited above are established; other particular caps can be settled when valid lower and upper bounds coincide, without determining a general exact formula. The chain condition (TM.5516) is necessary but not a full compatibility characterization across all original bands, particularly tag-2 continuation. The displayed static allocation tests fail on label classes; no numerical complete-family $A_U(H)>B(h)$ separation follows. Neither the single-cutoff executor nor depth at most one or two is proved a normal form for minimum-alphabet policies. Arbitrary competitors retain all source-dependent labels, mixed left/right positive contexts, reads, arbitrary acquired records and every finite accepted depth.

The source-bound label-production hypothesis remains an application obligation. TM51.9 applies unchanged: a common-initialized TM30 program that ends with every exact initial unit tree preserved can output only a constant. Every accepted positive context strictly adds leaves; every accepted replacement strictly adds leaves because unit sources have positive $\beta$ count and that positivity persists. No permitted action removes leaves. Such a preserving program can therefore have only unchanged reads of 1 and rejected modifications, giving a common record and common output. The sufficient nonconstant labels here are not produced for free by that consumer.

The source-call bound counts whole macro attempts, including rejected padding, replacement and terminal single-leaf attempts. A symbolic macro is not a claim of unit material or physical duration. Authentic archive acquisition, membership/pairing certification, supplier work, expanded contexts, rejected candidate material, replacement work, guard implementation, full-record storage, retained advice, output representation and physical costs remain separate. The explicit arithmetic controller has a sufficient $O(\log(H+1))$ variable-bit representation with compact integer context names; that is not a minimum-memory theorem and does not charge those other coordinates. Original tree/bracketing recovery, physical spacetime recovery, instrument conformity and the broader persistent relation-recovery goal remain unsettled.

The next research question keeps the entire task: can a uniformly effective genuine same-source supplier and compatible original-interface controller attain $(1/3-\varepsilon)h+O(1)$ symbols for some $\varepsilon>0$ on the complete $U_H$, or can an all-policy actual-history lower argument prove $h/3-O(1)$ necessity? A successful answer must retain all original bands and every actual word/bracketing, rather than solve a fixed executor, bounded-depth relaxation or marginal allocation. A proof that minimum capacity admits a bounded-depth normal form would be an additional substantive bridge, not a premise available here.

[TM55OR68]: https://github.com/the-omega-institute/trureturing/blob/511f1920bceaaf9f6ec6411030fbd4da42abfbfd/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md#68-完整单位原树的条件补充字母表配对上界与增长必要性
[TM55OR69]: https://github.com/the-omega-institute/trureturing/blob/511f1920bceaaf9f6ec6411030fbd4da42abfbfd/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md#69-完整单位原树在三十六至五十五上限的条件字母表精确值

[TM55OR70]: https://github.com/the-omega-institute/trureturing/blob/4f981b86a637c4aff1f1825ec0efe41dd5bb36e2/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md#70-完整单位原树的-ferrers-截角与更强条件字母表下界

## 追加锚（本行以下为增补区）

## 56. The common physical-prefix barrier

One fixed actual positive-context attempt followed by the first $\rho$ attempt imposes a supplied-alphabet barrier even when every subsequent original action remains available. On the complete actual unit family the barrier is $h/3-2$, where $H=4h+\delta$ and $0\le\delta\le3$. A separate ten-fiber class at $H=36,37,38,39$ admits one-symbol recovery with a second context chosen after the first rejection, but no one-symbol controller with a fixed one-context/first-$\rho$ prefix can recover that class. Both impossibility arguments retain complete acquired records and the distinction between the initial required target and current behavior.

The source/action premises are [Atomic359–360][TM56Atomic] and [TM30, TM38, TM44–47 and TM51][TM56Base] at immutable pin `28a41b31247b847af1b1b3118f7cb00ffd3b9cda`. The matching residue executor is reused directly from [TM55.5][TM56Residue] and [TM55.6][TM56Residue6] at immutable pin `dc14da97f120bbc04038a3bbc7996c78d001b9f1`; [the source binding](#TM56-L3) gives the same-source correspondence. The new interface check places that executor in the declared prefix class. The resulting sharp leading coefficient concerns this class alone.

### 56.1 Complete actual sources, resource types, and the prefix class

<a id="TM56-S1"></a>
**Reused source and target correspondence.** An actual source is a nonempty ordered binary tree $t::=\alpha\mid\beta\mid\langle t,t\rangle$. Tree equality retains leaf order and every bracket. The original substitution is $\rho\alpha=\beta$, $\rho\beta=\langle\beta,\alpha\rangle$, extended structurally to trees. Write $E_j(t)=E(\rho^jt)$ and distinguish the letter composition $c(t)=(a_\alpha,a_\beta)$ from the resource pair $(m,n)=(a_\alpha+a_\beta,a_\alpha+2a_\beta)$. The complete unit family is

<a id="TM56-E01"></a>
$$
U_H=\{t:1\le m(t)\le H,\ (E_0(t),E_1(t),E_2(t))=(1,1,1)\},
\qquad H=4h+\delta,\quad 0\le\delta\le3.
\tag{TM.5601}
$$

Atomic360.2–4 and TM51.2–3 give exactly the initial compositions and resource coordinates

<a id="TM56-E02"></a>
$$
\begin{gathered}
c(t)=(4r,4s),\qquad r,s\ge1,\qquad r+s\le h,\\
z=r+s,\quad w=r+2s,\qquad
2\le z\le h,\quad z+1\le w\le2z-1,\\
m=4z,\quad n=4w,\qquad r=2z-w,\quad s=w-z.
\end{gathered}
\tag{TM.5602}
$$

For $w\le h$, the initial target is

<a id="TM56-E03"></a>
$$
\tau_h(z,w)=
\begin{cases}
(2,(4(2z-w),4(w-z)),(1,1,1)),&z+w\le h,\\
(1,(4(2z-w),4(w-z)),1,1),&z+w>h.
\end{cases}
\tag{TM.5603}
$$

For $w>h$, it is $(0,1,4z)$, with hidden $w$ irrelevant to that initial target. A tag-0 row exists exactly when $2\le z\le h$ and $2z-1>h$. A genuine witness for every positive pair is any fixed ordered bracketing of

<a id="TM56-E04"></a>
$$
\omega_{r,s}=\alpha^{2r-1}\beta^{2s}\alpha\beta^{2s-1}\alpha^{2r}\beta.
\tag{TM.5604}
$$

Its eight Atomic360 edge multiplicities are $(r,r,r,r;s,s,s,s)$, positive, balanced and with connected support. The tag-0 row $z$ has witness $\omega_{1,z-1}$. Atomic360.3 includes every qualifying leaf word and every ordered binary bracketing, not only these witnesses. Selecting a witness in a lower argument never substitutes it for the running source.

The ambient action contract is TM30.1–2. A whole current `Read` returns actual current $E$ and preserves the source. A whole $\rho$ attempt or whole left/right concatenation with an actual nonempty positive context accepts exactly when the entire candidate has at most $H$ leaves; equality accepts. Rejection preserves the complete source and provides no candidate read. The record retains public inputs, supplied label, action and context identities, all responses and all actual reads. There is no reset, copy, inverse, source replacement, navigation, size port, target port or additional observation. The required output remains the **initial** $q_H(t)$ throughout; current $q_H(t_{\rm cur})$ describes future behavior only.

<a id="TM56-D1"></a>
**Definition TM56.1 (common physical prefix).** Fix public $H$, one public actual nonempty positive context $v$ and one fixed side. A controller belongs to $\mathrm{CPF}(v,H)$ if on every run it attempts this same context and then its first whole $\rho$, independently of the supplied symbol. These are its first two modifying attempts. Finitely many harmless current `Read` calls may precede the context or intervene between it and $\rho$; the attempts are consecutive after deleting those Reads. No additional modifying attempt, even a rejected one, occurs before that first $\rho$. After it, arbitrary ambient TM30 actions are allowed: either side, mixed positive contexts, Reads, arbitrary retained records and any finite accepted replacement depth. Continuation decisions may depend on the supplied label and the actual record.

Advice is a genuinely supplied function $\ell:U_H\to\mathcal L$ of the same unmodified initial source, authentic to that source before online actions. Lower bounds permit any exact-tree function, including dependence on leaf order and brackets, without target factorization or computability restrictions. Controllers are effective deterministic programs with common public initialization for equal labels and must stop correctly after finitely many source calls on each declared input. Exhibited upper suppliers are conditional constructions from authentic initial-target information or a certified same-tree archive; their production and pairing are separate obligations.

For the context put $p=d_0(v)>0$ and $q=d_1(v)$, so $p\le q\le2p$, and define

<a id="TM56-E05"></a>
$$
c=\left\lfloor\frac{H-p}{4}\right\rfloor,
\qquad k=\left\lfloor\frac{H-q}{4}\right\rfloor,
\qquad k\le c\le h.
\tag{TM.5605}
$$

Here scalar $c$ is a cutoff, whereas $c(t)$ denotes letter composition. The context accepts exactly at $z\le c$. On acceptance the subsequent $\rho$ accepts exactly at $w\le k$; on context rejection the source is unchanged and $\rho$ accepts exactly at $w\le h$. These guards include equality. In particular $c<0$ makes the context always reject.

<a id="TM56-E06"></a>
$$
\begin{aligned}
(m,n)&=(4z,4w)\\
&\xrightarrow{\text{accepted context}}(4z+p,4w+q)\\
&\xrightarrow{\text{accepted }\rho}(4w+q,\ 4(z+w)+p+q).
\end{aligned}
\tag{TM.5606}
$$

All three pairs in (TM.5606) are current/next **sizes**, not $\alpha/\beta$ letter counts. An accepted context adds letter composition $(2p-q,q-p)$; an accepted $\rho$ sends letter composition $(a,b)$ to $(b,a+b)$. Thus its post-$\rho$ next resource is exactly $m+n+p+q$. For an all-$\alpha$ context $p=q=P$, this is $m+n+2P$. Rejection changes neither the resource pair nor the actual tree. These are the typed TM30 transport formulas, with no omitted contribution.

<a id="TM56-S2"></a>
**Reused permanent-collision principle.** TM30.2 and TM38.1 apply to two actual sources with equal complete acquired records and equal current $q_H$, even when their initial targets differ. Every common later action then has the same response, actual reads and successor behavior on both. Pointwise finite stopping gives the same output, so recovery of both different initial targets is impossible. This principle covers all ambient continuations, including sources that have left $U_H$. It requires equality of the full record and current target; equality of a terminal size alone would not suffice.

### 56.2 A uniform lower bound after the common prefix

<a id="TM56-T1"></a>
**Theorem TM56.1 (common-prefix barrier).** For every $H\ge8$, every fixed actual positive context $v$ on either fixed side, and every $\mathrm{CPF}(v,H)$ controller recovering the initial target on complete $U_H$ with a finite supplied alphabet $\mathcal L$,

<a id="TM56-E07"></a>
$$
|\mathcal L|\ge\frac h3-2.
\tag{TM.5607}
$$

This quantifies arbitrary exact-source labels, all three initial target bands, all actual words and brackets, and every permitted post-prefix continuation. It imposes no terminal `Size_H` hypothesis.

**Proof.** Let $z_0=\lfloor h/2\rfloor+1$. For $h\ge7$, all pairs selected below are positive finite unit targets. Choose one genuine $\omega_{2z-w,w-z}$ per selected target with a fixed ordered bracketing, and retain the label actually supplied on that exact tree. If there are more selected targets than labels, two witnesses share a label. Their initial Reads are all 1. Reads after a common accepted context are also equal: they give the same ordered product with $E_0(v)$ and the original unit read. Thus equal labels and the displayed common responses give equal complete prefix records, including the number and identities of any intervening Reads.

If $c\le2h/3$, including $c<0$, select

<a id="TM56-E08"></a>
$$
S_{RA}=\{(z,h):\max(z_0,c+1)\le z\le h-1\},
\qquad
|S_{RA}|=h-\max(z_0,c+1)\ge h/3-1.
\tag{TM.5608}
$$

Every context rejects since $z>c$, and every unchanged first $\rho$ accepts at $w=h$, including $4h\le H$. The original targets are tag 1. The post-$\rho$ resource pair is $(4h,4(z+h))$, with $4(z+h)>H$, and the current read is the original $E_1=1$. Thus all current targets equal $(0,1,4h)$. Two equal labels would give a permanent collision of distinct initial targets. Each label can therefore cover at most one selected witness. The size estimate uses $z_0\le h/2+1$ and $c+1\le2h/3+1$.

If $c>2h/3$, then $c\ge z_0$. For $k\le2h/3$ select the accepted-context, rejected-$\rho$ row

<a id="TM56-E09"></a>
$$
S_R=\{(z_0,w):\max(z_0+1,k+1)\le w\le h\},
\qquad |S_R|=h-\max(z_0,k).
\tag{TM.5609}
$$

The inequalities $w\le h\le2z_0-1$ and $z_0+w>h$ make every pair a genuine original tag-1 target. The context accepts and $\rho$ rejects because $w>k$. Each resulting source has next size $4w+q>H$, current size $4z_0+p$ and common current read $E_0(v)$, on either fixed context side. Hence its current target is $(0,E_0(v),4z_0+p)$ and equal labels yield equal complete records and a permanent collision. For $k\le h/2$ the row has at least $h-z_0\ge h/2-1$ members; for $h/2<k\le2h/3$ it has $h-k\ge h/3$ members.

If $2h/3<k<h$, use

<a id="TM56-E10"></a>
$$
S_A=\left\{(z,k):
\max\left(\left\lfloor\frac k2\right\rfloor+1,h-k+1\right)
\le z\le k-1\right\}.
\tag{TM.5610}
$$

We have $z\le k-1\le c$, $k\le2z-1$ and $z+k>h$. Thus all selected pairs are positive original tag-1 targets and both prefix actions accept. The exact boundary-column arithmetic is

<a id="TM56-E11"></a>
$$
4k+q\le H<4(k+1)+q,
\qquad
4(z+k)+p+q\ge4(h+1)+p+q>H.
\tag{TM.5611}
$$

The post-$\rho$ current read is $E_1(v)$: it is the ordered context factor times the original $E_1=1$, on the chosen side. Every current target is consequently $(0,E_1(v),4k+q)$. Equal labels give the same complete record and the same current target before any later continuation. Their initial targets remain distinct. The column size is

<a id="TM56-E12"></a>
$$
\begin{aligned}
|S_A|
&=k-\max\left(\left\lfloor\frac k2\right\rfloor+1,h-k+1\right)\\
&=\min\left(\left\lceil\frac k2\right\rceil-1,2k-h-1\right)
\ge h/3-1.
\end{aligned}
\tag{TM.5612}
$$

Finally, $k\ge h$ forces $k=c=h$ by (TM.5605). Use

<a id="TM56-E13"></a>
$$
S_A'=\{(z,h):z_0\le z\le h-1\},
\qquad |S_A'|=h-z_0\ge h/2-1.
\tag{TM.5613}
$$

Both attempts accept, the current size is $4h+q\le H$, and the next size is $4(z+h)+p+q>H$. The common current target is $(0,E_1(v),4h+q)$, giving the same collision. This endpoint is possible only when $0<p\le q\le\delta$, and is retained wherever the actual context allows it.

Every case therefore requires at least as many labels as its selected witness set. For $h\ge7$ these counts exceed the stated $h/3-2$ bound; for $2\le h\le6$ its right side is nonpositive. This proves (TM.5607) for all $H\ge8$ and all four residues. The actual label of each selected tree, rather than any target-factorized advice, drives the pigeonhole argument. Even an attempted earlier stop on equal labels and equal Reads cannot return two different initial targets. $\square$

If a particular continuation is `Size_H`, the three main sets enter it at $4h$, $4z_0+p$ and $4k+q$, respectively. The theorem instead uses equal complete records and equal current $q_H$ at the prefix boundary, which proves impossibility for every ambient continuation.

### 56.3 Direct residue reuse and the matching class interface

<a id="TM56-P2"></a>
**Proposition TM56.2 (TM55 residue executor belongs to the prefix class).** For $h\ge5$, put

<a id="TM56-E14"></a>
$$
L=\left\lfloor\frac{h+1}{3}\right\rfloor,
\qquad c=h-L+1,
\qquad P=H-4c=4(L-1)+\delta>0.
\tag{TM.5614}
$$

The supplier of [TM55.5][TM56Residue] and its [TM55.6 executor][TM56Residue6], with the actual right context $v=\alpha^P$ under its fixed public bracketing, belong to $\mathrm{CPF}(v,H)$. On complete actual $U_H$ that same construction simultaneously has $L$ supplied symbols, no Reads, at most one accepted $\rho$ and at most $\lceil\log_2H\rceil+3$ whole source calls, including terminal rejection.

**Interface check.** The parameters satisfy $L\ge2$, $1\le c<h$, $h-c=L-1$ and $c\le2L+2$, precisely the hypotheses of TM55.5 (TM.5518). Positivity of $P$ holds in every cap residue because $L\ge2$. The context has letter composition $(P,0)$ and resource increments $p=q=P$, hence both scalar cutoffs in (TM.5605) are exactly $c$. The first two modifying attempts are this fixed actual context followed by one $\rho$ on either context response, with no intervening Reads or other attempts. The later `Size_H` is an allowed ambient continuation. Its entry source has size in $[1,H]$ by the preceding actual guards; it need not belong to $U_H$.

The source correspondence is literal: TM55's $U_H$, $(r,s)$, $(z,w)$, $\omega_{r,s}$ and initial $\tau_h$ are those of (TM.5601–4). Its conditional supplier is exactly TM55 (TM.5520): $\operatorname{rep}_L(w-z)$ on finite targets, $\operatorname{rep}_L(c-z)$ on padded tag-0 rows, and 1 on unpadded tag-0 rows, where $\operatorname{rep}_L(x)=1+((x-1)\bmod L)$. The retained symbol and actual response bits are passed to the original-target decoder TM55 (TM.5521), without changing any label meaning. In its four actual histories $AA,AR,RA,RR$, terminal entries are respectively $4w+P,4z+P,4w,4z$. These entries are current sizes; they are not compositions or initial-target replacements. All words and brackets lift by the same Atomic360/TM47.2 correspondence. The residue correctness proof and supplier/decoder are reused, not new mathematical contributions of Proposition TM56.2. The simultaneous alphabet/depth/call guarantee is TM55.6 (TM.5524–25). $\square$

Let $A_{\mathrm{CPF}}(H)$ minimize the conditional alphabet over all fixed actual nonempty contexts, fixed sides, arbitrary exact-source suppliers and successful controllers in their CPF classes. For $h\ge5$, [Theorem TM56.1](#TM56-T1) and [Proposition TM56.2](#TM56-P2) give

<a id="TM56-E15"></a>
$$
\frac h3-2\le A_{\mathrm{CPF}}(H)
\le\left\lfloor\frac{h+1}{3}\right\rfloor
=\frac h3+O(1).
\tag{TM.5615}
$$

Thus the leading coefficient $1/3$ is sharp **in this class**, with the exhibited costs belonging to its one actual execution. TM55.6's $h=2,3,4$ bases use one symbol, no padding, one $\rho$ and `Size_H`, with at most $\lceil\log_2H\rceil+2$ calls. Those no-padding protocols are outside the nonempty-context CPF class and are not upper certificates for (TM.5615). No unrestricted $h/3-O(1)$ necessity, minimum-depth assertion or unrestricted normalization theorem follows.

### 56.4 Ten complete fibers and an adaptive second context

<a id="TM56-T3"></a>
**Theorem TM56.3 (ten-fiber separation).** For each $H=36+\delta$, $0\le\delta\le3$, let

<a id="TM56-E16"></a>
$$
\begin{aligned}
S_9=\{&(3,4),(3,5),(4,6),(5,6),(5,7),\\
&(5,9),(6,8),(6,9),(7,9),(8,9)\},\\
\mathcal F_{9,H}
&=\{t\in U_H:q_H(t)\in\{\tau_9(z,w):(z,w)\in S_9\}\}.
\end{aligned}
\tag{TM.5616}
$$

One common supplied symbol admits a same-source controller recovering the initial target on every complete fiber in $\mathcal F_{9,H}$, with no Reads, at most two context attempts before the first $\rho$, at most one accepted $\rho$ and at most $\lceil\log_2H\rceil+4$ whole source calls. Conversely, for every fixed actual nonempty positive context on either fixed side, every one-symbol controller with that CPF prefix fails on $\mathcal F_{9,H}$, even with harmless Reads, arbitrary acquired records and arbitrary ambient continuation after the first $\rho$.

**Proof of membership and construction.** The first two points are initial tag 2 and the other eight are initial tag 1. The genuine witnesses from (TM.5604) are:

| Initial $(z,w)$ | $(r,s)$ | Actual witness | Initial band |
|---|---|---|---|
| $(3,4)$ | $(2,1)$ | $\omega_{2,1}$ | 2 |
| $(3,5)$ | $(1,2)$ | $\omega_{1,2}$ | 2 |
| $(4,6)$ | $(2,2)$ | $\omega_{2,2}$ | 1 |
| $(5,6)$ | $(4,1)$ | $\omega_{4,1}$ | 1 |
| $(5,7)$ | $(3,2)$ | $\omega_{3,2}$ | 1 |
| $(5,9)$ | $(1,4)$ | $\omega_{1,4}$ | 1 |
| $(6,8)$ | $(4,2)$ | $\omega_{4,2}$ | 1 |
| $(6,9)$ | $(3,3)$ | $\omega_{3,3}$ | 1 |
| $(7,9)$ | $(5,2)$ | $\omega_{5,2}$ | 1 |
| $(8,9)$ | $(7,1)$ | $\omega_{7,1}$ | 1 |

For example $\omega_{2,1}=\alpha^3\beta^2\alpha\beta\alpha^4\beta$ realizes $(3,4)$. The genuine source $\omega_{1,7}$ instead has $(z,w)=(8,15)$ and initial target $(0,1,32)$; it witnesses the tag-0 row 8 in $U_H$, outside this ten-fiber class. The finite point $(8,9)$ is realized by $\omega_{7,1}$. Every witness permits any ordered bracketing, and (TM.5616) retains the entire actual fibers.

Supply $\star$ to every input. First attempt the actual right context

<a id="TM56-E17"></a>
$$
\alpha^{H-19}=\alpha^{17+\delta}.
\tag{TM.5617}
$$

Its guard is $4z+(H-19)\le H$, exactly $z\le4$. On acceptance attempt $\rho$, whose guard is $4w+(H-19)\le H$, exactly $w\le4$. Only $(3,4)$ accepts that replacement. The two rejecting points $(3,5)$ and $(4,6)$ enter `Size_H` at $M=4z+(H-19)$, with distinct rows 3 and 4. All guard equalities are included.

On first-context rejection the complete original source is unchanged. Attempt the actual right context

<a id="TM56-E18"></a>
$$
K(d,e)=\alpha^{2d-e}\beta^{e-d},
\qquad
(d,e)=
\begin{cases}
(1,1),&\delta=0,\\
(\delta,\delta+1),&\delta=1,2,3.
\end{cases}
\tag{TM.5618}
$$

Zero exponents denote absence of that letter, not an empty context. The four actual nonempty words are $\alpha,\beta,\alpha\beta,\alpha^2\beta$, with increments $(1,1),(1,2),(2,3),(3,4)$. Each accepts on every remaining input: the largest row is $z=8$ and $4z+d\le H$ in all residues. Now attempt $\rho$. Its exact guard is

<a id="TM56-E19"></a>
$$
4w+e\le H\quad\Longleftrightarrow\quad w\le8.
\tag{TM.5619}
$$

The accepting points have distinct columns $w=6,7,8$, and the four rejecting points at $w=9$ have distinct rows $z=5,6,7,8$. Their `Size_H` entry sizes are respectively $4w+e$ and $4z+d$. A public decoder for the actual acquired record is:

| First context | First $\rho$ | Retained terminal entry | Initial output |
|---|---|---|---|
| accepts | accepts | $M=16+(H-19)$ | $\tau_9(3,4)$ |
| accepts | rejects | $z=(M-(H-19))/4\in\{3,4\}$ | $\tau_9(3,5)$ if $z=3$; $\tau_9(4,6)$ if $z=4$ |
| rejects; second context accepts | accepts | $w=(M-e)/4\in\{6,7,8\}$ | $\tau_9(5,6)$, $\tau_9(5,7)$, $\tau_9(6,8)$, respectively |
| rejects; second context accepts | rejects | $z=(M-d)/4\in\{5,6,7,8\}$ | $\tau_9(z,9)$ |

The first branch may also run `Size_H` in its accepting case, as in this uniform dictionary. Each entry is an actual size in $[1,H]$, so TM51.5 supplies finite terminal acquisition with no Read or replacement and at most $\lceil\log_2H\rceil+1$ calls, including final rejection. There are two prior source calls on the first-context-accepted branch and three on the second-context branch. Hence their whole-call bounds are $\lceil\log_2H\rceil+3$ and $\lceil\log_2H\rceil+4$. Only the single first $\rho$ attempt can be an accepted replacement. These alphabet, depth and call bounds hold simultaneously on the same running-source execution. TM30.2 and TM47.2 lift the dictionary to every actual word and bracketing in each complete fiber. No reset, copy, private row or replacement by a witness occurs.

**Proof of impossibility for every fixed first context.** Fix any actual nonempty positive context with increments $(d,e)$, $d>0$, $d\le e\le2d$, and either fixed side. Give all sources the same symbol and public initialization. Put

<a id="TM56-E20"></a>
$$
t=\left\lfloor\frac{H-d}{4}\right\rfloor,
\qquad u=\left\lfloor\frac{H-e}{4}\right\rfloor.
\tag{TM.5620}
$$

If $t\le6$, the actual witnesses for $(7,9)$ and $(8,9)$ both reject the context. Their unchanged first $\rho$ attempts accept at current size $4w=36\le H$. Their next sizes are $4(7+9)$ and $4(8+9)$, both above $H$. Thus their current targets are both $(0,1,36)$ and their complete records agree, including any harmless Reads. Their different initial targets form a permanent collision. Success would therefore require $t\ge7$.

With $t\ge7$, the context accepts the row-5 points $(5,6),(5,7),(5,9)$ and the column-6 points $(4,6),(5,6)$. If $u\le6$, the row points $(5,7)$ and $(5,9)$ both reject $\rho$: their next sizes $4w+e$ exceed $H$, their current sizes are both $20+d$ and their current reads are both $E_0(v)$. They have the same current target $(0,E_0(v),20+d)$ and equal complete records. Avoiding this permanent collision requires $u\ge7$.

If $u\ge6$, both column-6 points accept $\rho$. Their current sizes are both $24+e\le H$, and their next sizes are $4(4+6)+d+e$ and $4(5+6)+d+e$. Both exceed $H$ already at their original $40$ and $44$, since $H\le39$. Their current reads are both $E_1(v)$, so both current targets are $(0,E_1(v),24+e)$ and their complete records agree. Avoiding this collision requires $u<6$, contradicting $u\ge7$.

The witness argument uses equal complete records and current $q_H$, so TM38.1 excludes every ambient continuation, with arbitrary retained memory and finite accepted depth. Harmless Reads cannot break these equalities and add no modifying action before first $\rho$. An earlier stop with the one common symbol and unit Reads likewise cannot distinguish the initial targets. The impossibility is for a common symbol; arbitrary distinct advice symbols can distinguish the targets and are not excluded by this theorem. $\square$

A common physical context can produce different subsequent numeric cutoffs on its accepted and rejected branches: its contributions are present on acceptance and absent on rejection. In Theorem TM56.3 a second actual context is issued on the rejection branch. That extra modifying attempt places its successful one-symbol controller outside CPF.

### 56.5 Bound sources, bounded evidence, and remaining scope

<a id="TM56-L1"></a>
[Atomic359–360 at `28a41b31247b847af1b1b3118f7cb00ffd3b9cda`][TM56Atomic] supplies the ordered triple/common-source correspondence, actual positive witnesses, balanced connected edge support and every Euler word and ordered bracketing. Atomic360 (360.4–5) retains those supplier equation labels. [TM30.1–2 at that same pin][TM56Base], (TM.3001–4), supplies whole guards, equality acceptance, unchanged rejection, ordered source transport and behavioral congruence. TM38.1 supplies the full-record permanent collision used in both lower arguments. These source mechanisms are reused.

<a id="TM56-L2"></a>
[TM44.5 (TM.4419–20), TM51.5 and TM47.1–2 at that pin][TM56Base] supply terminal entry-size acquisition and complete-target lifting. `Size_H` needs only an actual ambient entry size in $[1,H]$, uses no Read or replacement, and costs at most $\lceil\log_2H\rceil+1$ calls including final rejection. TM45 retains ordered outer factors and initial/current pairing. TM51.2–3 supplies the complete unit target coordinates used throughout. None is an additional online observation.

<a id="TM56-L3"></a>
[TM55.5][TM56Residue] and [TM55.6][TM56Residue6] at `dc14da97f120bbc04038a3bbc7996c78d001b9f1` are the bound residue source in `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md`. TM55.5 assumes $h\ge2$ and integers $L,c$ satisfying $L\ge2$, $1\le c<h$, $c\le2L+2$ and $h-c\le L-1$. TM55.6 applies for every integer $H\ge8$, with $h=\lfloor H/4\rfloor$ and $L=\lfloor(h+1)/3\rfloor$; for $h\ge5$ it uses $c=h-L+1$ and $P=H-4c>0$, whereas its $h=2,3,4$ bases omit padding. Both use the same complete $U_H$, initial target, conditional same-unmodified-initial-source advice and actual source/action correspondence as this chapter. The Atomic359–360 and TM30/38/44/45/47/51 source sections are byte-identical at that immutable source and this chapter's `28a41b31247b847af1b1b3118f7cb00ffd3b9cda` pin, so the common-source premises agree. The alphabet, Read, replacement and call guarantees hold simultaneously on the same running-source execution.

<a id="TM56-L4"></a>
[TM54 at merged revision `20b37ca68329a5d1ee0b67c28ffe2c90e89f4fce`][TM56Prior54] uses the same complete $U_H$, initial target and conditional same-source advice contract. Its complete-family necessary count (TM.5412) and upper constructions in Theorems 54.5–6 remain prior comparison results. The current CPF lower bound is not a bound over all the controllers minimized there, and the residue upper remains attributed to TM55.5–6.

<a id="TM56-L5"></a>
[OR68 Definition 68.1][TM56OR68] and [OR69 Definition 69.1][TM56OR69] use the same full-source conditional task: OR68's $\nu$ and OR69's $y$ are this chapter's $w$, and OR69's $x$ is $z$. The finite target $C_{r,s}$ is $\tau_h(r+s,r+2s)$; $Z_x$ is $(0,1,4z)$. Their arbitrary exact-tree labels and full ambient controllers retain a larger policy domain than CPF. OR68's linear growth and small-cap results, [OR69's complete-family exact intervals][TM56OR69], and [OR70's Ferrers necessary bound][TM56OR70] remain comparison/reuse boundaries. In particular the published complete-family value at $36\le H\le39$ is 2, whereas Theorem TM56.3 concerns a proper ten-target-fiber class with one common symbol. It adds no complete-family exact-small-cap claim. OR70 supplies a further unrestricted necessary bound, not unrestricted $h/3$ necessity or a general exact formula. The immutable comparison revisions are `511f1920bceaaf9f6ec6411030fbd4da42abfbfd` for OR68–69 and `4f981b86a637c4aff1f1825ec0efe41dd5bb36e2` for OR70.

<a id="TM56-V1"></a>
**Bounded arithmetic evidence.** The reported finite arithmetic checks have the following scopes, separate from the universal proofs above:

| Arithmetic scope | Reported result |
|---|---|
| $7\le h\le40$, all four $\delta$, $1\le p\le H+2$, $p\le q\le2p$: selected lower witness sets and exact prefix size arithmetic | No counterexample to validity or the $h/3-2$ count; exit 0 |
| $2\le h\le60$, all four $\delta$, every finite and tag-0 target: residue branch/entry/label dictionary | No duplicate decoder key; exit 0 |
| $H=36,37,38,39$, the ten target fibers: actual second-context increments, equality guards and decoder keys | Ten distinct initial-target keys; exit 0 |

These are bounded integer falsifiers, not arbitrary-policy enumeration, all-word testing or proofs of universal impossibility. The residue dictionary check supports the reused TM55 construction, not a new residue theorem. The source witnesses and full-fiber coverage follow from Atomic360 and the typed parameter correspondence; the one-symbol witness for $(8,9)$ is specifically $\omega_{7,1}$.

<a id="TM56-O1"></a>
**Remaining scope.** The unrestricted complete-family minimum $A_U(H)$, its sharp leading coefficient and existence of an unrestricted normalized limit remain undetermined here. Controllers with arbitrary pre-$\rho$ modifications, label-dependent contexts, multiple cutoffs, $\rho$-first schedules or other adaptive prehistories are outside the CPF lower theorem. Their post-$\rho$ actions are not restrictions inside that theorem: every ambient finite continuation remains quantified. The ten-fiber controller and counterexample do not give a general depth normal form or an exact complete-family capacity.

Authentic label production and delivery, source membership and pairing, archive parsing and retention, full-record storage, context material, guard/replacement work, integer arithmetic and memory/time costs remain separately charged. All statements are ordinary mathematics on the declared source/action interface. This chapter supplies neither Lean kernel verification nor physical verification, and does not settle the unrestricted complete-family goal.

[TM56Atomic]: https://github.com/the-omega-institute/trureturing/blob/28a41b31247b847af1b1b3118f7cb00ffd3b9cda/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md
[TM56Base]: https://github.com/the-omega-institute/trureturing/blob/28a41b31247b847af1b1b3118f7cb00ffd3b9cda/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[TM56Residue]: https://github.com/the-omega-institute/trureturing/blob/dc14da97f120bbc04038a3bbc7996c78d001b9f1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#TM55-P5
[TM56Residue6]: https://github.com/the-omega-institute/trureturing/blob/dc14da97f120bbc04038a3bbc7996c78d001b9f1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#TM55-T6
[TM56Prior54]: https://github.com/the-omega-institute/trureturing/blob/20b37ca68329a5d1ee0b67c28ffe2c90e89f4fce/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#54-complete-unit-family-supplied-advice-linear-capacity-and-actual-acquisition
[TM56OR68]: https://github.com/the-omega-institute/trureturing/blob/511f1920bceaaf9f6ec6411030fbd4da42abfbfd/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md#68-完整单位原树的条件补充字母表配对上界与增长必要性
[TM56OR69]: https://github.com/the-omega-institute/trureturing/blob/511f1920bceaaf9f6ec6411030fbd4da42abfbfd/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md#69-完整单位原树在三十六至五十五上限的条件字母表精确值
[TM56OR70]: https://github.com/the-omega-institute/trureturing/blob/4f981b86a637c4aff1f1825ec0efe41dd5bb36e2/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md#70-完整单位原树的-ferrers-截角与更强条件字母表下界

## 追加锚（本行以下为增补区）

## 57. A complete paid ideal realization of the original ordered-tree interface

This construction realizes the actual TM30 source, including its preparation, whole actions, original responses, growing records, record-only verification and consumer output. Its quantifiers are all public integers $H\ge1$, all nonempty ordered $\alpha/\beta$ trees with at most $H$ leaves, all actual nonempty finite contexts, and all effective lawful finite original protocols. The machine is an explicitly declared ideal finite-control process with constructed finite tapes. All proofs here are ordinary mathematics. Physical conformance, a native implementation and optimality are separate questions.

### 57.1 The unchanged source and the exact target

Let $\mathcal T$ be the free nonempty ordered binary-tree algebra on $\alpha,\beta$. Its equality retains both brackets and order. Put $c(t)=(a,b)$, $\lambda(t)=a+b$, and $\mathcal T_H=\{t:1\le\lambda(t)\le H\}$. The actual substitution is

$$
\rho\alpha=\beta,\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\tag{PR57.01}
$$

At an idle original cut the menu is `Read`, $\rho$, `Left(v)` and `Right(v)`, with any named actual $v\in\mathcal T$. Read returns the exact current $E$ and leaves the source unchanged. The three modifications form respectively $\rho t$, $\langle v,t\rangle$ and $\langle t,v\rangle$. The entire candidate is tested against $\lambda\le H$. Acceptance publishes only `accept` and installs that candidate; rejection publishes only `reject` and retains the old source. There is no candidate Read on rejection. Arbitrarily large finite contexts remain typed requests. There is no source navigation, reset, duplication, inverse, size port or request quota. Serial busy cuts admit only the next prescribed microtransition, not another original request.

Use the pinned Clifford algebra with $A^2=1$, $B^2=-1$, $AB+BA=1$, and $S=BA$. Its faithful coordinates are $N(e,k,p)=(-1)^eS^kA^p$. Write $u_i(t)$ for the normal coordinates of $E(\rho^it)$ and $\eta(t)=((u_0,u_1,u_2),c(t))$. Set $\lambda_0=a+b$, $\lambda_1=a+2b$, $\lambda_2=2a+3b$. The target is literally

$$
q_H(t)=\begin{cases}
(0,E(t),\lambda_0),&\lambda_1>H,\\
(1,(a,b),E(t),E(\rho t)),&\lambda_1\le H<\lambda_2,\\
(2,((u_0,u_1,u_2),(a,b))),&\lambda_2\le H.
\end{cases}
\tag{PR57.02}
$$

In particular the tag-2 output contains $\eta$, not an unexplained flattened coefficient tuple. The initial target and the current target have different identities throughout. A preparation identity names an occurrence, not a tree value. The public prior $D$ is any declared nonempty subset of the finite $\mathcal T_H$; the unrestricted case is $D=\mathcal T_H$. An arbitrary such subset can be supplied by its complete membership bit-vector in the enumeration of §57.10. Its creation and transmission are paid. Public effective prior predicates can instead be evaluated on every enumerated tree; termination on this finite enumeration is the meaning of an effective declaration. No private predicate or source-dependent choice of program is allowed.

### 57.2 Finite primitives, actual tapes and literal control

**Definition PR57.D1 (constructed-tape machine).** There are 64 fixed tape ports, a finite public control state, eight finite symbol latches (their bit subfields supply Boolean operands), finite port-ownership tokens and a meter. The port assignments are fixed: control and public arithmetic 0–15, producer private data 16–23, actor 24–31, verifier 32–39, consumer 40–47, mailboxes 48–55, and meter/readout 56–63. Every ordinary tape is a finite word between a left marker $L$ and a right marker $R$ with one head. A second head is permitted on the meter only. Head marks are finite tracks on the constructed cells: a move changes the two adjacent marks, so a head position never occupies a hidden natural-number register. Ordinary symbols are $L,R,\square,0,1,\mathsf{sep},\mathsf{seal},\mathsf F$; each cell occupies eight model bits: three symbol bits, three head/append/read marks, a seal mark and one reserved bit. Ordinary tapes use only their designated head mark. The unused marks are zero. Every move/extension changes a fixed finite set of adjacent symbol/mark bits. No cell beyond $R$ exists. Head positions are physical cursor relations to existing cells, not stored integer registers. The finite control and token storage has its actual finite encoded size $b_{\rm ctl}$.

The following are the primitive core occurrences. Each acts on a fixed finite set of adjacent tape cells or one finite latch/token; no action reads or changes an unbounded interval. A control successor is part of that occurrence.

| core occurrence | exact effect |
| --- | --- |
| `RD(i,j)` | read the symbol at port $i$ into finite latch $j$; no head movement |
| `WR(i,s)` | write one symbol, or one latched bit, at the current writable ordinary cell |
| `ML(i)`, `MR(i)` | move one cell within the constructed interval; crossing $L$ or $R$ is disabled |
| `EX(i)` | at $R$, replace $R$ by $\square$, construct one new $R$ immediately to its right, and leave the head at the new blank cell |
| `BF(f)` | apply one specified Boolean truth table to the bit subfields of operand latches 0–2 and put its bit in result latch 3 |
| `IN(i)` | put the next supplied bit in the input latch for the declared public or private ingress; it does not move or write a tape |
| `OUT(j)` | transmit one bit from a declared public output latch |
| `TOK(a,b)` | transfer one of the finitely many port/availability tokens from $a$ to $b$ |
| `CTL` | take a finite control edge, including seal, phase change, request/response commitment or halt |

`RD` and `WR` do not hide a seek. A move is not an allocation. `EX` is a literal one-cell constructor, including initialization to $\square$ and right-marker replacement. Zero initialization still requires `WR(0)`. A three-input truth table has exactly eight bits and 256 possible codes. The model does not make addition, string copying, integer-address lookup or integer comparison a primitive.

Each core occurrence simultaneously appends one receipt symbol at the meter's append head: the old meter $R$ becomes a receipt and one new $R$ is constructed. A receipt is either ordinary or a fence, as selected by a `CTL` fence edge. This fixed one-cell side effect is part of the finite transition rule, including for `EX`, meter scans and readout. The event has one logical tick and two fee units: one core unit and one receipt-construction unit. This is a finite-symbol primitive convention, not an atomic operation on an unbounded numeral. At a cut after $n$ events the actual meter contains exactly $n$ receipts and a right marker. There is no second fee counter, automatic binary increment or automatic transcript of private values.

All 63 ordinary tape boundary pairs are constructed by fixed boot constructor edges, each constructing one ordinary cell (the boundary-construction case of `EX`); the meter is the remaining port. Every control-description bit and initial finite control/token bit is installed by a bit ingress/write edge, one bit at a time, with the same receipt side effect. Boundary constructor edges and control-bit installation are finitely many boot variants of the core `EX` and `WR` operations, not an unbounded installation primitive. The finite bootstrap has only the states `next`, `input-bit`, `write-bit`, `advance`, `done`; it installs a prescribed finite literal encoding and the ordinary pairs of boundary markers, then enables the main control. The meter initially has its two boundary markers and append head, supplied as the irreducible primitive port. Their sixteen bits and the fixed primitive control bits are the initial constant $S_0$, also included in storage. There is no preconstructed data arena. The primitive port convention is the foundation of this ideal model; it is not a theorem about constructing hardware from nothing.

Here is a fully encodable specification of the control, with a mechanical finite expansion. A native row is

$$
U(q)\;U({\rm op})\;U(i)\;U(j)\;U(s)\;U(q_0)\;U(q_1),
\qquad U(n)=1^n0.
\tag{PR57.03}
$$

Unused fields are zero. State numbers are assigned in the order of the routines below, then textual occurrence order. On a testing `RD` row the predicate is equality of the newly read symbol to the finite immediate $s$; on a testing `CTL` row it is equality of the designated public latch $j$ to $s$. All other rows have $q_0=q_1$. Thus the predicate is encoded in the row, not a missing instruction field. Composite public tests first compute their Boolean bit by the listed routines. A boundary test on a private tape distinguishes only $L$ or $R$ from all ordinary symbols and takes the same successor on private 0 and 1. The opcode order is the table above, with Boolean codes in lexicographic bit order. Public tests may select a successor. Private latches may only feed `BF` and bit writes; they never select a successor, port or move. The public observation of the PC is this native row number and routine phase; private latch contents are excluded.

For avoidance of an implicit compiler, the finite expansion rules are part of the specification. Sequence joins the exit edge of the first finite graph to the entry of the second. `if public P` inserts one `RD`/finite-test edge to the two entries and joins their exits. `while public P` inserts that edge, an edge back from the body exit, and an exit edge. `for each 1 in a finite unary tape` is `RD; if 0 exit; body; MR; back`. The loop head is a real tape head. A fixed subroutine call is inlined. Finite alternatives over the eight symbols, 64 ports and 256 truth tables are expanded into those finitely many cases; they do not create states indexed by integers. Parameters and return data are on tapes. All uses of these rules below have a finite static nesting depth. The generator's depth-first expression traversal uses a constructed stack of frames, not native recursive calls. Push and pop are the append/scan routines below. Thus the control graph is finite independently of $H$, contexts, program length and request count. Its encoding is (PR57.03); the boot installs its bits literally. Its size is $|\operatorname{enc}(\operatorname{expand}(\mathcal R))|$, where $\mathcal R$ is the finite list of routines specified in §§57.3–57.10. This is a computable length of a given encoding, not an assigned service constant. Dynamic instructions use a different explicit encoding in §57.5.

All native control is constructed once. Reading a native rule and changing its finite control state is the primitive finite mechanism just declared; it is not a word-sized instruction service whose fetch is secretly omitted. Dynamic code, policies, address strings, descriptors and data are ordinary tape contents and are fetched by charged scans. No generator generates its interpreter, allocator or own control.

### 57.3 Complete tape service routines and progress

**Definition PR57.D2 (service library).** Each arrow in the following recipes is an occurrence from Definition PR57.D1. No recipe has an integer-valued atomic step.

`Home(i)` repeatedly reads the current cell; on $L$ it stops, otherwise it moves left and repeats. From position $h$ relative to $L$ it costs exactly $2h+1$ core occurrences. Only the boundary test controls this loop; ordinary private bits are ignored. `Tail(i)` analogously seeks $R$. A traverse of $h$ intervening cells costs $2h+1$ from its starting point. Positions and boundaries are public.

`Append(i,b)` requires the head at $R$ and performs `EX; WR(b); MR`. It costs three core occurrences and constructs exactly one cell. `AppendWord(i,w)` reads every symbol of the finite sealed $w$, appends it, and moves its source head once per symbol. Its per-symbol body is `RD; EX; WR; MR(destination); MR(source)`, of length five. Homes and seeks to the two specified starting positions are separately counted. This routine is used for descriptors, instructions, literal public input, stack frames and string copies; no bulk write is primitive.

`Allocate(i,k)` takes a real unary $U(k)$ at its first bit and the arena head at $R$. For each leading 1 it executes `RD(counter); EX(i); WR(i,0); MR(i); MR(counter)`; the terminal 0 is read once. Its body count is $5k+1$, plus actual counter/arena positioning and delimiter/descriptor construction. Before allocation, `Base(i)` obtains the actual arena offset: `Home`, then move past $L$ and scan to the already existing $R$, appending one 1 to a separate public counter for each intervening cell and then 0. Only the $R$ test controls it. For $b$ existing data cells its body is $5b+4$ occurrences (`RD; Append(1); MR` per cell, then `RD(R); Append(0)`), plus home/initial movement/positioning. This constructs $U(b)$ before any new arena cell is created. A descriptor is the concatenation of owner code, arena-port code, $U(b)$, $U(k)$, initialization flag, mutability flag and creation/request ordinal, where $b$ is the arena offset. Its bits are created with `AppendWord`; $U(b)$ is this actually constructed `Base` result, copied to the descriptor. Every appended cache/code/stack block uses the same `Base` routine for its starting reference; no cursor position is converted into a numeral without this scan. `Allocate` appends a delimiter and never changes a preceding block. Allocation, descriptor creation, zeroing and later copying are distinct executed bodies. Fresh intervals cannot alias. An erase is a full seek plus one `WR(0); MR` per designated cell; erased cells remain constructed and counted in storage.

`Seek(i,U(a))` first executes `Home(i)`, then one `MR(i)` to data index zero. Starting at the first bit of a real address string, for every leading 1 it performs `RD(address); MR(i); MR(address)`, then reads the terminal 0. Its cost is

$$
\operatorname{SeekCost}(h,a)=2h+1+1+3a+1=2h+3a+3,
\tag{PR57.04}
$$

plus positioning the address head. The data tape must already contain that cell. Code generation/validation checks this public bound. A read or write at the result adds one occurrence. Offset zero means the first cell after $L$. Marker tests in `Home` never branch on an ordinary bit. All addresses of a private gate execution are supplied by public code, so all these seeks are source independent.

Unbounded public naturals and references use $U(n)$, including zero. Increment constructs a new version: append all old leading 1s, one extra 1, then 0; retire but retain the old version. Addition concatenates leading-1 parts and a terminator. Subtraction of $v\le u$ walks paired 1s, then copies the remaining $u-v$ 1s. Comparison walks two strings together until a terminator. Multiplication repeats a full leading-1 copy once for every 1 of its first argument. A finite bound $B$ can be converted to a binary width by the loop $w=1,P=2$; while $P\le B$, increment $w$ and double $P$ by unary concatenation. It stops because $2^w>B$ for some $w\le B+1$. Every intermediate string, comparison and copy is constructed by the displayed routines. There is no modular wrap. These inefficient algorithms suffice for every finite public integer, including address arithmetic and generation ordinals.

`Promote(x,w,w')`, $w'\ge w$, allocates a fresh $w'$-bit vector, copies all $w$ old bits by seeks/reads/writes, then writes zero extension for unsigned values or the copied sign bit for signed values at each of the remaining $w'-w$ positions. All iterations and addresses are public. Old vectors remain retained or are erased by a complete scan. Unary references have no finite address width to promote; a relocation constructs a fresh descriptor and copies every unary reference to its new version with the same routines. No reference is truncated.

**Lemma PR57.L1 (service termination and constructive storage).** Every invocation above with finite constructed inputs and a valid finite bound terminates and leaves only finitely many constructed cells. It has a unique next primitive occurrence at every unfinished cut.

**Proof.** `Home` decreases the head distance to $L$; `Tail` decreases distance to the already existing $R$. An append has exactly three occurrences. An allocate/copy/seek loop consumes a fixed, already sealed unary string or sealed finite block. Newly created cells lie on a different tape or beyond the source fence and cannot extend that loop's bound. Nested multiplication loops have the two fixed finite operands as bounds. Width search strictly increases $P$ by doubling and stops no later than $B+1$ increments; its inner copies have fixed finite inputs. Promotion consumes $w'$ positions. These arguments give a natural outer-iteration bound and a finite inner bound for every invocation, rather than a rank that increases when more allocator work is created. Only `EX` constructs cells, one at a time; finitely many terminating bodies imply finite construction. The deterministic recipe gives a successor at each unfinished cut. $\square$

### 57.4 Ticks, fee numerals, identities and charged readout

**Definition PR57.D3 (closed-cut readout).** The public microtrace contains one tick pulse and the fee increment 2 at every occurrence. Its cumulative mathematical coordinates after $n$ pulses are $(n,2n)$. These coordinates are not automatically stored accessible binary numerals. What is stored is the meter's unary receipt sequence. A fence occurrence writes a distinguished receipt $\mathsf F$. A public unary counter counts fences, with the increment recipe of §57.3. The read head scans from $L$, counting fence markers with paid unary arithmetic, until the declared already existing fence number is reached. It also constructs a separate bound tape by appending one 1 for each receipt visited, then a terminal 0 at the selected fence. It stops at that marker, even though new receipts are being appended during the scan. The resulting bound is an actual stored $U(n)$, not an execution index used as a free loop bound.

For a fence at event $n$, a second scan driven by that stored bound constructs $U(n)$ and $U(2n)$: for every leading 1, `RD(bound); RD(meter)`, append one 1 to the tick tape, append two 1s to the fee tape, `MR(meter); MR(bound)`; read the terminal bound 0 once, then append a terminal 0 to each output tape. The body is exactly $13n+7$ core occurrences, plus fence selection, bound creation and positioning. The two numeral blocks are sealed, actually copied and, if requested, printed one bit per `OUT`. Their type is `tick/fee at fence f`. They report the old closed cut; the readout's own events increase the current meter. The complete pulse sequence determines that increase exactly. There is no requirement to print a number that already includes the act of printing that number, and no recursive free counter.

An event identity is a receipt-cell occurrence in this append chain. A tape address is the port, its origin and a finite cursor path. The trace exposes all moves, reads, writes, extensions and origin resets, hence exactly which existing cell each occurrence touches. A request/block/row reference is a stored unary ordinal plus its actual creation chain; its numeric wire representation is constructed and copied using §57.3. An address can also be serialized by scanning its finite path and appending $U(a)$. Merely mentioning a mathematical address or event index in a proof does not supply such a serialization. No primitive emits an arbitrarily long numeric label.

Preparation/version identifiers are complete public finite bit strings actually installed and copied. A preparation ordinal advances by paid unary increment independently of source content. A current-generation field records the accepted-update count, advanced after the original `accept` response; an attempt field advances on every call. Original identity never changes. These counters are distinct from the meter and may not substitute for it.

**Lemma PR57.L2 (exact nonrecursive metering).** At every finite cut, meter receipts, tick pulses and charged fees have counts $n,n,2n$. Every requested closed-cut numeral is correct and finite, including when its readout creates more receipts.

**Proof.** Each primitive appends exactly one receipt and emits exactly one tick and fee increment 2. Induction establishes the counts, beginning at the irreducible port. Fence ordinals are maintained by a separate paid routine whose bounds are finite; the selected fence existed before the readout. Its prefix has $n$ cells permanently, so the readout appends exactly $n$ and $2n$ ones. New receipts occur strictly after the fence and are excluded from the loop. The terminal zeros and output are paid. No meter value is an input to a primitive transition and no self-inclusive readout equation is used. $\square$

### 57.5 Literal gate instructions and a terminating generator

**Definition PR57.D4 (dynamic Boolean tape).** A generated gate record is the literal bit string

$$
1\;f_0f_1\cdots f_7\;U(d)\;U(a)\;U(b)\;U(c).
\tag{PR57.05}
$$

The first bit 0 instead means end of program. Each record has length $13+d+a+b+c$. $f$ is the full truth table in input order 000,…,111; $d$ is the destination and $a,b,c$ are operand bit addresses on the specified private or public workspace tape. All four address fields are present, including for constants and unary gates. There is no immediate-width ambiguity, implicit next-PC or hidden arithmetic opcode. Unused operands point to the constructed zero cell. Instructions execute in record order.

The fixed interpreter does the following: read header and eight truth-table bits into finite public control, moving once after each (18 occurrences); copy each complete unary field onto its own public address tape; seek/read the three operands; apply `BF(f)` once; seek/write the destination; resume at the next record. Copying an address-field bit uses `RD(code); EX(address); WR(address,bit); MR(address); MR(code)`, exactly five occurrences. All four field copies and their positioning are executed. The three operand values stay in latches 0–2. All public code, boundary and address scans use latch 4; the result in latch 3 survives destination positioning. No private latch value is tested by control. Let $P_g$ be the actual address-field positioning and scratch-sealing occurrences in this invocation, and $h_{g,r}$ the actual workspace head position before the $r$th seek. With $v=(a,b,c,d)$,

$$
I(g)=18+5\sum_{r=1}^4(v_r+1)
 +\sum_{r=1}^4(2h_{g,r}+3v_r+3)+4+1+P_g.
\tag{PR57.06}
$$

The 4 means three operand reads and one result write; 1 is `BF(f)`. $P_g$ is not an unnamed service charge: it is the sum of the `Home`, `Seek`, `CTL` and `WR` occurrences prescribed above for the actual four address tapes. Each newly cached field has a descriptor for its actual start offset; before each workspace seek its address head is positioned there by the complete `Seek` recipe on that public tape. Each such positioning is $2h+3b+3$, plus positioning its descriptor; each seal/control edge is one occurrence. The descriptor seeks terminate on the literal finite descriptor, whose start was represented by `Base` before its append, or by a full origin scan to its delimiter with its paid unary block ordinal. Such a scan counts delimiters by the unary increment/compare recipes, including those extra occurrences; it does not use a mathematical offset as an uncharged stopping test. Every delimiter scan uses `RD; MR` until that declared public delimiter. No positioning is a random-access primitive. Equivalently expand the recipe and count its finite event word; (PR57.06) groups that word. End-of-program costs one header `RD` plus its prescribed exit `CTL`. Initialization, generator work and later output/copy are outside $I(g)$ and are counted where executed.

The gate generator is a native public routine, not a generated gate list. Its finite stack machine has frames `(kind, children left to visit, result references)` encoded by fixed tags and unary references. It first visits every child in order, pushing its finite expression frame; on completion it allocates one fresh result bit, emits (PR57.05) by `AppendWord`, and pushes the resulting reference. Literals emit constant truth tables; variable leaves emit projection tables. MUX emits all three children and then its truth table. A fold is a public loop over its declared finite index string. Bounds, addresses and offsets are computed by unary routines. Every `Emit(f,d,a,b,c)` writes all record bits by the append recipe; no instruction is assumed to exist before that write.

The finite expression templates used here are exactly Boolean gates and the following bit recurrences. At each position an adder emits

$$
t=x\mathbin\oplus y,\quad s=t\mathbin\oplus c,
\quad u=x\land y,\quad v=c\land t,\quad c'=u\lor v.
\tag{PR57.07}
$$

It uses five gates per bit, including the final carry computation. Subtraction emits $\neg y$ at every bit and uses that same adder with initial carry 1; negation uses complement and addition of 1. Equality folds `(NOT XOR)` with AND, three gates per position. Unsigned less-than scans most significant first with old $e,l$, emitting

$$
z=\neg(x\oplus y),\quad n=\neg x,\quad u=e\land n,
\quad v=u\land y,\quad l'=l\lor v,\quad e'=e\land z;
\tag{PR57.08}
$$

this is seven gates per position because $z$ needs XOR and NOT. Signed comparison flips each sign bit before this comparison. Every bit MUX uses one full three-input truth table. All initial constants and copies are themselves emitted. Evaluating both arms means executing their gates even if their values will not be selected. Vector widths are chosen from public bounds before generation; all arithmetic values and even unused arithmetic arms lie inside the declared signed range. Bits are only a representation of these integers; overflow is never assigned an integer meaning.

**Lemma PR57.L3 (noncircular generation and gate execution).** Every finite template and finite public loop bound yields a finite literal gate tape and a finite interpreter execution. Its instruction/address/extension trace is independent of private operands.

**Proof.** A depth-first stack frame either descends to a proper subexpression or completes one visited child. The finite expanded expression forest, including all public fold iterations, bounds the number of visits; each `Emit` is a terminating finite append. The generator's arithmetic and allocator are native service routines already installed by the finite bootstrap. They do not call gate generation to instantiate themselves. The interpreter consumes one whole record at a time and stops at its fixed terminal 0. Field copying and seeking terminate by Lemma PR57.L1; every address has a publicly checked allocated destination. No private value bit controls an edge or head motion; truth-table evaluation changes only latch/data values. Thus a gate tape determines the entire precommit trace and its finite cost. $\square$

### 57.6 Actual paid input, contexts and policy computation

**Definition PR57.D5 (material supply).** Put $N=2H-1$. Private preparation is exactly $2N$ `IN` occurrences, in pairs, followed by their actual writes to $N$ token slots of the freshly allocated producer block. Each input bit has `IN; WR; MR`; the slots and their masks are allocated and zeroed first. The private choices define the source occurrence. There is no externally traversed variable-length tree or free $t\mapsto\operatorname{code}(t)$ routine. The choices are just the initial source material, whose ingress/write occurrences are charged. The typed valid packets below have a bijection with actual $\mathcal T_H$. Every actual $t$ is represented by its unique choices. This is a representation of the initial input, not a program selected by that input. An effective upstream creator, if part of a protocol, executes on the same tapes before these writes; its work and material are counted as supply work.

The token alphabet is `PAD=00`, `alpha=01`, `beta=10`, `PAIR=11`. The active packet is the literal preorder tree code followed by PAD to length $N$. On all $N$ slots a generated circuit starts with need 1, closed 0, leaves 0, validity 1. PAD while not closed sets validity to 0: **padding is forbidden before closure**. A non-PAD after closure also sets validity to 0. Before closure PAIR adds one needed child slot; a leaf subtracts one and increments leaves. Closure is sticky when the updated need is zero. Invalid inputs never shorten the scan. The final test is validity, closure, need zero and $1\le$ leaves $\le H$. Explicitly, with old $(n,z,l,v)$ for need, closed, leaf count and validity, let $P,A,B$ test PAIR, alpha and beta, $L=A\lor B$, $T=P\lor L$, and $I=(\mathtt{PAD}\land\neg z)\lor(T\land z)$. Compute $n_* = n+[P]-[L]$, $n'=\operatorname{MUX}(T\land\neg z,n_*,n)$, $l'=l+[L\land\neg z]$, $z'=z\lor[n'=0]$, $v'=v\land\neg I$. Every candidate is computed before selection. These are bit-circuit templates made solely of the arithmetic/Boolean recipes already specified. A signed width $N+4$ suffices for all need/count arms, including unused need-minus-one at zero. Validity is committed only at the end. The source domain concerns valid preparations; malformed packets have the same finite validation schedule and a failure, with no target receipt.

For an actual public context, the material packet contains its name and exact finite preorder token sequence, with its stored length. Every symbol is generated by the actor's public program or received by a charged `IN; WR; MR` sequence. The complete packet is parsed, copied and retained on paid tapes. A context given as an effective expression is expanded by the public stack generator: a leaf appends its token; a branch appends PAIR and pushes right then left, with every frame and token actually written. The number of unvisited expression nodes decreases after each completed expansion. Arbitrary effective context-creation computation is included through the policy interpreter below. No semantic $d_i(v),h_i(v)$ or ownership/name test is a free supplier. Contexts with $d>H$ are still completely constructed, validated, retained and processed by the service. Identical algebraic values or equal leaf counts do not replace the named actual tree.

An effective original policy is supplied as a finite deterministic Turing transition table and its finite public initial tape; both are installed bit by bit by the same append/ingress routines. A row contains unary state and symbol codes, a new state/symbol, and one of the three finite directions. The interpreter scans every row of the sealed table for each simulated step, compares complete unary state/symbol codes using the service routines, stores the unique matching row, writes the simulated symbol and new state, and moves the simulated head by one. A virtual two-sided tape is represented by two finite stacks and a current symbol; pushing is `AppendWord`, popping scans the finite stack to its last sealed frame and constructs a new prefix version. Blank extension uses `Allocate`, not an infinite blank tape. State and head numerals are never assumed stored by the mathematical simulation. A finite alphabet may be encoded into fixed blocks, with their block width part of the installed program.

Input to this interpreter is precisely the public initialization and original projected record. Output is a request plus full named context packet, or stop plus a proposed target. Writing all those bits is policy work. A restart-on-history policy or a persistent-state policy is represented by its own table; retained machine tapes supply its actual state. Every effective deterministic original protocol has such a finite machine description; the specific step-by-step interpretation just given establishes the supply connection, rather than appealing to computability to skip it. The construction does not decide whether a program terminates. A lawful finite computation is one whose actual table execution reaches its output state in finitely many simulated steps. Each such step is itself a finite paid tape schedule. Only public data or already committed responses influence that policy's branches.

**Theorem PR57.T1 (literal source representation and parser correspondence).** Valid fixed packets are in bijection with $\mathcal T_H$; private preparation has the same public trace for every valid source. Their active tokens transduce faithfully to `AtomicPrefixParser.code`.

**Proof.** Open slots initially number one. PAIR consumes one slot and creates two; a leaf consumes one. Before closure there is no PAD and after closure there are only PADs. Thus closure separates exactly one complete ordered binary tree from its suffix. There are $m$ leaves and $m-1$ branches, hence $2m-1\le N$ active tokens. Conversely structural preorder traversal has these properties and uniquely determines the packet. The actual primitive ingress and the generated validation tape have fixed public length/addresses. Secret validity/count values are only circuit operands. The transduction is PAIR $\mapsto[\mathrm{false}]$, alpha $\mapsto[\mathrm{true},\mathrm{true}]$, beta $\mapsto[\mathrm{true},\mathrm{false}]$, with PAD omitted only after closure. By structural induction this is exactly the pinned parser code of the same `FreeMagma Bool` tree, with true labeling alpha. An $m$-leaf token code becomes $3m-1$ bits. If the transduction is executed internally, it reserves $2N$ slots, forms lengths 0/1/2 and prefix offsets by fixed circuits, scatters with equality masks, retaining the result and its active-length mask privately. Public context transduction may serialize its canonical bit string by paid public work. No private source transduction is published, and no private length is used as an address or a public precommit loop bound. The parser's parse/remainder equivalence and injectivity therefore apply to this transduced active word, not to the two-bit token alphabet itself. $\square$

### 57.7 The complete whole-action source schedules

All private source work is on generated fixed gate tapes. Each call computes $A_i=[X_i\ne\mathtt{PAD}]$ and $L_i=A_i\land\neg A_{i+1}$, with the public sentinel $A_N=0$, by full scans of the $N$ slots. The unique last-active mask is therefore literal, not a private traversal stopping condition. These masks and private offsets are operands, never addresses. Every candidate array is freshly allocated and fully initialized. Counts/offsets use signed width $W=3N+C+8$, where $C$ is that call's public candidate capacity; this exceeds every intermediate absolute count and offset, including arithmetic arms later discarded.

For $\rho$ an active PAIR emits `(PAIR)`, alpha emits `(beta)`, beta emits `(PAIR,beta,alpha)`, and PAD emits the empty chunk. The chunk length $\ell_i$ lies in 0,…,3 and the private offset is $o_i=\sum_{k<i}\ell_k$. Reserve $C=3N$ token slots, initialized to PAD. For every $j<C$, $i<N$, $r<3$ and each token bit, OR the terms

$$
[r<\ell_i]\land[j=o_i+r]\land\operatorname{chunkbit}(i,r).
\tag{PR57.09}
$$

Every term and every fold gate is executed. The generator's loops have public bounds $C,N,3$, and each equality/comparison is the complete $W$-bit recipe. The resulting candidate is its actual preorder concatenation, followed by padding.

For a context of $d$ leaves and $M=2d-1$ active tokens reserve $C=1+N+M$. Slot zero is PAIR. In `Left(v)`, place context token $k$ at $1+k$ and active source token $i$ at $1+M+i$, using a full $j$-by-input equality scatter. In `Right(v)`, place active source token $i$ at $1+i$, and context token $k$ under all masks

$$
L_i\land[j=2+i+k].
\tag{PR57.10}
$$

The source's last active token is $i$; thus $2+i$ is the first context position. All $i,k,j$ are scanned, whether their masks are true or false. Nonmatches contribute zero and unused suffix positions are PAD. The two directions preserve actual brackets and order.

The candidate parser of §57.6 scans all $C$ slots, retaining full grammar/leaf-count results. It computes $g=[\lambda({\rm candidate})\le H]$ together with candidate validity. At every original source slot and bit it executes `MUX(g,candidate_i,old_i)` and writes the result to the current-source block. All $N$ slots are written. The block is unavailable throughout this phase, and the successor is logically committed only after its final write. On rejection each old source bit is retained, with the same source-block/preparation identity and accepted-generation count. Scratch arrays and offsets are erased by whole scans; their allocated cells remain counted. The only committed response is the one-bit guard result. The candidate's $E$ is neither evaluated for an update response nor exposed.

A Read reserves four $D=H+5$-bit signed vectors in the faithful basis $(1,S,A,SA)$, starts with $(x,y,u,v)=(1,0,0,0)$ and at every token computes both

$$
R_\alpha=(u,v,x,y),\qquad R_\beta=(u-v,-u,y,x+y).
\tag{PR57.11}
$$

It selects $R_\alpha$ on alpha, $R_\beta$ on beta and the old tuple on PAIR/PAD, evaluating every candidate and selection bit. It converts at full width to the original faithful coefficient tuple

$$
(c_0,c_A,c_B,c_{AB})=(x+y,u,v,-y).
\tag{PR57.12}
$$

A fixed-length $4D$-bit response block is written completely before its response-commit token is released. That release makes one complete typed response available; it does not perform an uncharged copy or serial transmission. Subsequent delivery copies/prints the block through the routines below. Canonical signed-binary trimming, if desired, happens only after commitment and is a public computation on the returned original $E$. Equal coefficients denote precisely equal original responses. An accept/reject block is likewise complete before release. At no precommit cut is any response block readable by the actor.

**Theorem PR57.T2 (actual source and original Read conformance).** For all $H,t\in\mathcal T_H$, every original context of arbitrary finite size, and every finite lawful call sequence, these schedules give the exact original responses and evolving actual trees. Rejection preserves the original source; Read does not mutate it.

**Proof.** The representation theorem supplies exactly the current literal preorder code. The chunk substitution is (PR57.01) on each token and preserves branch tokens, so concatenating chunks gives the exact code of $\rho t$. Distinct output offsets have a unique contributing chunk position; the equality OR therefore writes that code and PAD suffix. The left/right equations give PAIR followed by the exact two actual subtree codes in their specified order. The parser counts the complete candidate, so $g$ is exactly the original whole guard, including equality at $H$. If accepted, its $2\lambda-1$ active tokens fit $N$; if rejected, every MUX gives the old bit. Nothing splits a whole context into sequential interface calls.

For Read, $S^2=S+1$ and $SA=B$ give the displayed right-multiplication formulas. Preorder visits leaves in their original left-to-right order. Induction through the $N$ slots therefore gives the product $E(t)$; PAIR and PAD are identities of the scan, not source leaves. The coefficient $\ell_1$ norm grows by at most a factor two per active leaf, so selected coefficients have magnitude at most $2^H$. Even the unselected one-step candidates and final conversion have magnitude at most $2^{H+2}$. Signed width $H+5$ contains them strictly, with no overflow. The Read program writes only workspace/response cells. Induction over calls now gives exact source and response conformance. $\square$

### 57.8 Observation at every cut and one causal simulator

**Definition PR57.D6 (complete visible trace).** At each primitive cut observers see the current public phase/native instruction identity, finite owner/token state, busy/idle availability, port and exact cursor-cell occurrence touched, move direction and extension, channel direction, tick pulse and fee increment, and public material/instruction fields actually released or transmitted. A cursor-cell occurrence is identified by port and its origin/move history; its printed numeral is available only after a paid serialization. Block identities, stored ordinals, seal/handoff occurrences and declared immutable reference chains are public. Public code, context packets, policy parameters, delivered archives, receipts and task output are accessible only through their declared paid reads/copies. Private source bits, source-parser counts, masks, offsets, gate latches and unreleased candidate/response blocks have no observation port. Physical electrical activity is not an additional label.

An original response commits at its complete response-block release. The observation correspondence consumes precisely that original response then, before simulating its delivery or any subsequent response-dependent work. This defines partial-delivery cuts too: after release the simulator may serialize the acquired $y$, but before release it may not inspect $y$. Availability has exactly the same pattern for all valid sources with the same public history. Original calls are admitted only at idle cuts; all intermediate generator, allocation, gate, copy and control cuts are present in the microtrace with their unique next transition.

Let $\omega$ be the actually committed original prefix. The public simulator is the very same native control, public generator, allocator, policy interpreter and copy schedules, with private bit values erased. For each public request it executes the public parameter work and builds the same gate tape; executes gate seeks/writes using arbitrary dummy bits while retaining only their labels; stops at response release; consumes the single original response $y$; then fills the now-public response block with the faithful encoding of $y$ and executes all postcommit work. It maintains its actual unary ordinals, addresses, meter receipts and public tapes. Preparation uses dummy private input bits with the same $2N$ ingress labels and validation schedule, with the domain's valid-preparation result. It does not select an enumerated representative source and it never maintains a speculative original source or initial target.

**Theorem PR57.T3 (uniform prefix-causal full observation correspondence).** This is one effective source-uniform correspondence covering every allowed cut, with exact instructions, addresses, availability, identities, ticks/fees, preparation, material creation, growth/copy, verification and consumer use. Erasing its added microstructure yields precisely the unchanged original trace.

**Proof.** Before a response release, the source affects only private circuit bits. Lemma PR57.L3 gives the same code, control edges, tape movements, allocations and cost counts for equal public initialization, prefix and request. Fixed preparation length likewise gives equal ingress/validation labels. Each receipt side effect is fixed. Source-data writes differ privately, but their cell occurrences and instruction labels agree. Theorem PR57.T2 supplies exactly one original $y$ at release; no earlier label uses it. Every later branch, trimming choice, copy length or accepted-generation increment may depend on that $y$, which is now in the acquired prefix. Policy, context creation, archive, verifier and consumer routines read only that prefix and public inputs, so their complete subsequent computations are simulated literally. Induction on primitive cuts, interrupted only by these original response releases, gives equality of the complete visible trace. Truncating the execution at any cut truncates the same simulator run, so the maps are prefix compatible. Original enabledness is idle/menu, and micro enabledness is the prescribed successor on both sides. Projection keeps each actual original request and exactly its response, with the same source successor and stop decision. No future response, private initial target or representative source is used. $\square$

In particular a fee or address threshold does not supply a new source distinction: it is a function of public input and responses already acquired. The simulator itself can be run on paid tapes if a protocol elects to use it; its computed work is then additional public policy work, not a free selector.

### 57.9 Owned growth, complete copying and authentic records

**Definition PR57.D7 (records and channels).** Producer $P$, actor $A$, verifier $V$ and consumer $C$ have disjoint archive/workspace ports. A mailbox is a separately constructed tape interval, not an alias of an archive or receiver snapshot. Sender writes, seal, token handoff, receiver copy and acknowledgement are serial. A sealed sender block remains immutable throughout the copy. The complete destination length is allocated/initialized first. For a $k$-bit payload, after actual positioning, the sender loop is `RD(sender); WR(mailbox); MR(sender); MR(mailbox)` for each bit, then one seal `CTL` and one token handoff. The receiver loop is the same four occurrences from mailbox to destination, then one seal and one acknowledgement handoff. Its body has exactly

$$
8k+4
\tag{PR57.13}
$$

core occurrences. Allocation/zeroing, all homes/seeks, unary length/identity descriptors and any serial output are additional occurrences, disjoint from these two loops. The head movements are part of this count and cannot be omitted. A destination becomes readable only at its final seal. Source, mailbox and destination coexist. Mailbox data and markers may be retained; all constructed storage is counted.

Every original call, including every reject, appends one producer row. Its literal fields are length-framed finite bit strings: model/version/preparation identity, `INITIAL-SOURCE` identity, request ordinal, previous row reference, exact original request, complete context name and code reference, exact committed original response, accepted-generation count before/after, schedule/template identity, start-fence and response-commit-fence references, and the row's creation/seal occurrence chain. Natural fields use $U(n)$. A Read field contains the exact coefficient representation. A rejected update has only reject and no candidate value. Each context reference points to the complete actually retained packet, never to a representative with the same leaf count or $E$. Length framing is `U(length)` followed by that many actual bits; its prefix and payload are produced by the append routines.

Start and response-commit fence numerals are obtained by the closed-cut scans of §57.4. They refer to those closed cuts, not to the future end of the row's own serialization. Row completion is a distinct seal occurrence. There is consequently no self-referential fee-range field. The fee interval between start and response commitment is obtained by subtraction of the two represented fee numerals; row/copy completion costs are separate exact event intervals. Old row fields are never edited. Each complete row is copied to $A$ through a distinct mailbox; context material is copied as well if not already present there.

At stop, $P$ freezes the actual row/context prefix and copies it completely, with its framing and descriptors, through a fresh mailbox to a fresh $V$ snapshot. $P$'s archive, $A$'s archive, mailbox and $V$'s snapshot all coexist. Verification begins only after complete snapshot seal. There is no arbitrary external transcript-import port. Names are checked, but authenticity comes from these allowed write/copy transitions. A row's original-preparation field is never changed to its current-generation field. Rejected attempts still advance the request ordinal and retain their actual row.

**Lemma PR57.L4 (copy and archive authenticity).** Every readable receiver block equals its designated sealed sender block bit for bit and retains that sender's original identities. Every verifier snapshot is exactly the producer's frozen actual prefix.

**Proof.** Each loop reads and writes the same indexed bit once; positioning and constructed length ensure its exact interval. During the sender loop only the sender owns the mailbox write token; during the receiver loop it is sealed and the destination is inaccessible until completion. Induction on $k$ gives bit equality. The framing/identity payload is part of that same copy, not generated by a receiver's choice. Induction over appended rows gives continuity, immutability and unchanged original preparation identity. Freezing precedes the snapshot copy, so the snapshot is the actual frozen prefix. This is ideal exclusive-ownership provenance, not a cryptographic theorem about hostile writers. $\square$

### 57.10 Whole-fiber verification, literal tag-2 decoding and actual use

**Definition PR57.D8 (exhaustive paid record verifier).** $V$ uses only its snapshot, copied public initialization/prior and proposed target. It has no source port. For an explicit enumeration without a hidden table, form all length-$N$ token words in base four: start at all PAD; increment by scanning every slot with a carry from the last slot, emitting a fresh version; stop after all PAIR. This is exactly $4^N$ words. Parse every word with the fixed circuit of §57.6, retaining the valid ones. By Theorem PR57.T1 they enumerate $\mathcal T_H$ once. Apply the declared prior to every valid word, paying its actual table/program computation. Exhaustive whole scanning never stops at its first survivor or disagreement. Invalid words are fully processed by the parser and then skipped publicly; they are not sources.

For each retained $s\in D$, save its initial target in a distinct initial-target block, then replay **every** authentic original row from the beginning on a separate current-candidate block. A Read row is compared to the exact computed current $E$. An accepted update must have the true whole guard and installs the actual complete candidate. A reject must have the false guard and preserves the old candidate. All context packets are loaded from the snapshot and processed on their actual side. The running survival bit is the AND of all comparisons; a false bit never shortens replay. Original metadata, row continuity, framing, identities and copy references are scanned completely. Verification is a public computation on enumerated candidates and acquired data; even source-dependent branches within a candidate calculation are branches on public enumerated values. Using the same fixed circuits is sufficient and fixes all replay costs explicitly.

Initial $q_H(s)$ is computed from this enumerated $s$, not from the actual hidden source. Count $(a,b)$ by full token scan and choose the tag using (PR57.02). To obtain tag 2, directly fold the original leaf contributions

$$
g_\alpha=((0,0,1),(0,1,1),(0,1,0)),\qquad
 g_\beta=((0,1,1),(0,1,0),(0,2,1))
\tag{PR57.14}
$$

from the temporary triple unit using, in each coordinate,

$$
(e,k,p)(f,\ell,q)=(e+f+p\ell\bmod2, k+(-1)^p\ell, p+q\bmod2).
\tag{PR57.15}
$$

The unit is an arithmetic initialization, not an empty source. These folds give $u_0,u_1,u_2$ for that same actual candidate $s$. Initial and current blocks stay distinct even after irreversible updates.

A precise wire encoding is tag $U(j)$ followed by the fields of (PR57.02), in that order; pairs/tuples have fixed arity and each finite string is length framed. A signed integer uses a sign bit and a length-framed magnitude, zero with sign zero. Tag 2 is `U(2); (u0,u1,u2); (a,b)`, with each $u_i=(e_i,k_i,p_i)$ in that order. It decodes literally to $(2,\eta)$.

If a proposal arrives instead as tag plus three coefficient windows and composition, a paid adapter first converts each window from the original basis by

$$
(c_0,c_A,c_B,c_{AB})\mapsto(c_0+c_{AB},-c_{AB},c_A,c_B)
\tag{PR57.16}
$$

and checks that only one of the even/odd coefficient pairs is nonzero. For the nonzero pair $(x,y)$ it enumerates the full pairs for $S^0$, $S^1$, $S^k=(F_{k-1},F_k)$, $k\ge2$, and $S^{-n}=(-1)^n(F_{n+1},-F_n)$, $n\ge1$, testing both global signs. Fibonacci values are generated by actual additions; stop once the next tested Fibonacci magnitude exceeds $\max(|x|,|y|)$, after also testing the boundary pair. Because $F_{n+2}\ge2F_n$, only finitely many pairs can match. A convenient total schedule tests $k=0,1$, and then all positive/negative pairs with indices through the first $r+2$ such that $F_r>\max(|x|,|y|)$; redundant final tests avoid any boundary ambiguity. The normal-form uniqueness supplies a unique $(e,k,p)$ or a failure. Reverse conversion is paid Fibonacci generation with the same formulas and basis change. Thus coefficients and normal coordinates are faithfully interconverted on their actual image; mixed-grade/zero/nonunit inputs fail. The adapter uses only returned/proposed coefficients, never an additional source Read. Complete pair tests handle negative exponents and $F_1=F_2=1$ without approximate logarithms. Bit arithmetic uses the same literal gates with sufficiently promoted public widths.

Let $b_s(\omega)$ be the final replay survival bit. Compute by the complete enumeration

$$
\mathsf{nonempty}=\bigvee_{s\in D}b_s(\omega),\qquad
\mathsf{constant}=\bigwedge_{s\in D}
 (\neg b_s(\omega)\lor[q_H(s)=\tau]).
\tag{PR57.17}
$$

Accept iff metadata/proposal checks, nonempty and constant are all true. Empty fibers fail; ambiguous fibers fail. Retain a typed `INITIAL-q_H` receipt containing the literal original target, immutable prefix end, original preparation/version identity, prior description, verification occurrence and actual snapshot reference. Failure yields a refusal with no accepted receipt.

Consumer $C$ receives a complete actual copy through a fresh mailbox. It scans framing, type, prior, original identity, snapshot/prefix end and receipt-creation references, compares every target field to its proposed task value, and checks the actual accepted receipt seal. Only after all checks does it allocate, initialize and write its task-output block by bit copies. The output's type is `INITIAL-q_H`. A wrong type, malformed receipt, wrong original identity, ambiguous fiber or refusal produces no task output. These checks are executed before the decision, and failures have paid finite schedules too. A receipt remains bound to that frozen prefix; a later current source cannot reinterpret it.

**Theorem PR57.T4 (record-only soundness, complete-fiber acceptance and use).** For every authentic prefix on an actual $t_0\in D$, that source survives replay. A target proposal is accepted exactly when it is constant on the entire nonempty compatible original-source fiber and the declared structural checks succeed. Every consumer output equals the actual initial $q_H(t_0)$.

**Proof.** The enumeration is complete and duplicate-free by Theorem PR57.T1, and the declared prior retains exactly $D$. Lemma PR57.L4 gives the actual rows and contexts. Theorem PR57.T2 applied row by row to $t_0$ makes every comparison true. Conversely a surviving $s$ has exactly every recorded original response under the same requests and complete contexts; induction gives precisely membership in the original record fiber. Initial target computation uses (PR57.14)–(PR57.15), the pinned group law and the tag tests, so it is the literal $q_H(s)$. The coefficient adapter is an injective change of basis followed by exhaustive testing of the unique normal form; hence it does not change that target. Formula (PR57.17) is exactly nonempty fiber constancy, with no survivor selected as actual. Applying constancy to $s=t_0$ proves $\tau=q_H(t_0)$. Actual receipt copying and complete consumer checks retain that identity and value; its bit writes decode to precisely that target. No initial-target oracle was used. $\square$

### 57.11 Complete occurrence partition, simultaneous storage and protocol transfer

**Definition PR57.D9 (same-execution costs).** Every core occurrence has its native opcode and exactly one routine-purpose tag. The tag is installed in public control at entry and restored at exit. The disjoint purpose classes are: boot/control description; input/context/program/prior supply; standalone allocation/initialization/descriptors/promotion/erase; unary arithmetic, identity and closed-cut readout; expression generation and instruction construction; dynamic source-gate execution including fetch/seek; policy table interpretation and request construction; archive framing/append/freeze; channel transfer; verification/enumeration/replay/adapter; receipt/consumer checking and task output. These are tags on actual occurrences, not sums of overlapping whole-phase bounds. Untagged helpers such as `Home`, `Seek` and `Append` inherit the caller's tag. Explicit calls of `Allocate` or `Promote` enter the allocation tag. The gate interpreter inherits verification during replay and has the dynamic-source-gate tag during a source call. Consequently a verification-gate `RD` is counted once in verification with subtag `gate-fetch`. A code-field `EX` inside the gate fetch is dynamic gate work, and is also one constructed cell in the separate storage coordinate; it is not charged again as standalone allocation. A channel loop's `WR` is channel transfer, while its destination's earlier allocation/zeroing is allocation. A tag change is itself a `CTL` occurrence assigned to its entering routine. Failure and stop edges carry their actual phase's tag. The independent opcode partition below further identifies every constructor, read, write, move, evaluation, input, output and control occurrence.

Let $n_{p,o}(r)$ count the actual core occurrences with purpose $p$ and opcode $o$ in a finite execution $r$. Let $e(r)=\sum_{p,o}n_{p,o}(r)$ and let $a(r)$ count ordinary `EX` constructions plus actual finite boot cell constructors, excluding the meter. Then

$$
T(r)=e(r),\qquad F(r)=2e(r),\qquad
F_{\rm core}=\sum_{p,o}n_{p,o}(r),\quad F_{\rm meter}=e(r).
\tag{PR57.18}
$$

Thus there is no undefined “paid descriptor work” summand. Counts are obtained by the actual recipes: `Append` is 3, `Allocate` is $5k+1$ plus its stated positioning/descriptor events, `Seek` is (PR57.04), `Gate` is (PR57.06), complete channel body is (PR57.13), and a selected closed-prefix readout body is $13n+7$. Sequence adds these expanded event-word lengths; a public loop sums its body over its actual stored finite bound; a public branch uses its actual chosen event word. Gate counts for arithmetic are the bit recurrences of §57.5. Generator instruction writes are three occurrences per written code bit plus actual source/descriptor/ordinal reads and moves. Boot writes its complete native encoding, masks/markers and program bits with the same primitive rules. Policy costs sum complete table-step scans and simulated-tape work. Verification costs sum all $4^N$ parser executions, every prior evaluation and every row replay for every retained candidate. Nothing assigns these unexecuted sums as a free prepaid certificate.

This recurrence is an effective exact evaluation of a finite schedule, not an efficiency estimate. At any unfinished permitted cut the completed prefix is counted in the same way. Private values affect Boolean results but not the precommit event word; postcommit public branches use only actual acquired data. Allocation costs never include a channel loop or instruction fetch a second time. Erasure is work and does not recover a previous construction charge. The mandatory meter occurrence belongs only to $F_{\rm meter}$, even when its associated core event is a readout scan.

All constructed ordinary cells are retained in this model, including erased/replaced scratch versions. If $A(c)$ is their number at cut $c$ and $n(c)$ the meter receipt count, the actual simultaneous storage is

$$
S(c)=S_0+b_{\rm ctl}(c)+8A(c)+8n(c),\qquad
S^{\rm peak}(r)=\max_{c\preceq r}S(c).
\tag{PR57.19}
$$

Here $b_{\rm ctl}(c)$ counts the installed finite control/token/latch bits already constructed; tape-encoded dynamic code/descriptors are in $A(c)$. The fixed finite primitive port is included in $S_0$; head marks on all subsequently constructed cells are included in the factors 8. A head is a marked-cell relation, not an extra free accessible address integer. Storage is monotone, so its finite-run peak occurs at the last cut. The sum includes simultaneously the current private source, all candidates/offsets, code/address tapes, native description, policy state, all complete context material, producer/actor archives, distinct mailboxes, verifier snapshots/enumeration/replay, initial/current target blocks, receipts, meter and consumer output. At a snapshot of $k$ retained archive bits, the four independent archive copies contribute at least $4k$ payload bits (and their actual eight-bit cell encodings, framing and descriptors), while all other constructed cells coexist. No separate maximum is substituted for this sum.

**Theorem PR57.T5 (whole-runtime progress and all finite protocol transfer).** Every finite lawful original request sequence with finite effective supply/control work has a unique finite lifted execution through all its preparation, services and deliveries. Every pointwise terminating uniformly correct effective original protocol on its declared $D$ lifts to the same original calls, responses, stop and initial proposal, followed by accepted verification and actual correct consumer output. There is no fixed bound on request count, context size, reference width or total memory.

**Proof.** Bootstrap is a finite literal installation. Lemmas PR57.L1–L3 give termination of each tape routine, parameter construction, generator and fixed gate execution. Material-expression expansion consumes a finite expression; a lawful policy step has a finite table scan and finite stack work, and a lawful local policy computation has finitely many such steps. A source call has finite public nested bounds $N,C,W,D$ and a finite gate tape; copy/framing loops have the already constructed finite payload as bound. Meter readout stops at an existing fence. The verifier's outer base-four enumeration has exactly $4^N$ words; each prior computation terminates by its declaration; each replay has the frozen finite row count and actual finite context bounds. Its adapter Fibonacci loop terminates by geometric growth, and its consumer loops consume finite sealed blocks. These give explicit finite bounds for the subroutines that can create new work; a lexicographic rank that omits newly created allocator work is unnecessary.

A finite concatenation of these terminating schedules terminates. At each unfinished microcut the native routine has a prescribed successor. Recursive construction of that successor yields a nonempty unique execution; there is no optional wait or scheduler fairness hypothesis. Each finite cut has finitely many `EX` and receipt constructions. More lawful requests start fresh finite schedules, never a quota failure or wrap.

For transfer, run the same installed policy table on the projected authentic original history. Theorem PR57.T3 and source conformance give exactly its old next decision and old response, by induction on original cuts. Its actual finite local work is paid, so pointwise termination gives a finite stop prefix. For any $s\in D$ producing that same terminal record, determinism gives the same stop proposal. Uniform correctness of the original policy makes it $q_H(s)$ for every such $s$. The actual $t_0$ supplies nonemptiness. Theorem PR57.T4 therefore accepts and produces the actual initial target at the consumer. This is a total realization of the interface and all lawful finite behavior; correctness of a chosen acquisition policy remains exactly its original domain-specific property. $\square$

**Corollary PR57.C1 (the unchanged impossibility).** For $D=\mathcal T_H$ and $H\ge9$, the realized interface has no uniformly correct deterministic effective initial-target acquisition protocol using its permitted observations.

**Proof.** Any such finite acquisition protocol can be run on the original responses with the effective causal simulator supplying all additional microobservations. Its effective local work becomes original local computation. It would then violate pinned TM31 Theorem 31.4. In particular after a first irreversible merge the new verifier rejects an ambiguous initial-target fiber; additional journal, addresses or record copies are functions of the same acquired original history and cannot distinguish it. $\square$

### 57.12 Edge cases, falsifiable boundaries and immutable suppliers

PAD before closure is a substantive error: at $H=2$, `PAD,alpha,PAD` must fail while `alpha,PAD,PAD` succeeds. A rule that only checks final need and absence of active tokens after closure accepts both and loses the literal-code bijection. At $H=1$, alpha has tag 1: its first $\rho$ still has one leaf and accepts, and its second has two leaves and rejects. Beta has tag 0 and its first $\rho$ rejects. A rule equating acceptance with strict leaf growth mishandles alpha.

Whole action and source identity matter even for immediate rejection. A context larger than $H$ is allowed; both concatenations are fully processed and rejected without changing the source. Splitting it into leaf appends can accept an initial fragment and is a different operation. At $H=9$, let $X=\beta\beta\alpha\beta\beta$, $Y=\alpha^9$ and $Z=\alpha\beta^4$, each with fixed left-associated brackets. $X,Y$ have the same initial $A$ and post-$\rho$ $B$, yet initial compositions $(1,4)$ and $(9,0)$. Their shared Read/accept/Read/Right(alpha)-reject prefix has at least two initial targets and only one current tag-0 boundary. It must not receive a single initial-target receipt.

For $t=\langle X,\alpha\rangle$ and $u=\langle Z,\alpha\rangle$, both initial boundaries at $H=9$ are $(0,1,6)$; both $\rho$ candidates have ten leaves and reject. Their candidate $E$ values differ: the first is $-1$, the second is $(BS^4)B=-2-3AB$, since $S^4=2+3S$. In the pinned representation $A=\operatorname{diag}(1,-1)$, $B=\left(\begin{smallmatrix}1/2&1\\-5/4&-1/2\end{smallmatrix}\right)$, this second value is $\left(\begin{smallmatrix}-7/2&-3\\-15/4&-7/2\end{smallmatrix}\right)$. Publishing that rejected value breaks Theorem PR57.T3. Similarly the private preparation code lengths for $X,Y$ are 9 and 17 tokens; emitting those lengths publicly would add a distinction absent from their initial Read. Fixed $N=17$ preparation avoids it. A finite-width ordinal or a fixed request cap fails on a sufficiently long finite Read sequence. A readout that scans the live meter end rather than a pre-existing fence need not terminate: its scan events create new receipts to chase.

The construction assumes the declared finite-symbol primitive machine, including its one-cell event receipt side effect and ideal exclusive ownership. It supplies no extra information about the original source. An alternative primitive machine must redo the schedules and observation proof; costs are not representation independent. The existence result does not claim efficient circuits, minimal storage, optimal policy computation or a polynomial verifier. It does not decide arbitrary program termination, prove hostile-message authenticity, handle concurrent/interrupted calls, noise, finite physical exhaustion, speculation or native timing. All-source interface realization is distinct from all-source initial-target acquisition. The realization theorem has no fixed request bound or external runtime-realization premise. Native software and mechanized checking of this finite-control description remain separate validation work, not premises silently used here.

The immutable supplier revision for all links below is `17b26a61db5577d2f67031c777e9d86e91c3e617`. The following exact subsection roles delimit the reused facts; they supply no uncharged runtime service.

| immutable supplier | precise reused fact |
| --- | --- |
| [AtomicPrefixParser.lean, theorem `result`](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.lean#L49) | literal leaf `[true,b]`, branch `false::left++right`; parse with actual remainder, injectivity, prefix freedom and complete decode; the transduction is proved in PR57.T1 |
| [GenealogicalFiberTransport.lean, `Source`, `substitution`, `composition`](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean#L31) | `FreeMagma Bool`, actual ordered substitution and leaf composition |
| [Atomic §355, Definition 355.1 and proof of Theorem 355.3](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#355-clifford-叶积的组成余数与进位恢复边界) | the specified quadratic form, Clifford leaf product, relations and faithful four-coefficient basis |
| [Atomic §356, Lemmas 356.2–356.3](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#356-连续-clifford-叶积窗口的尖锐闭合与历史纤维) | same-source three-window identities and grade-preserving conjugation; no different source model |
| [Atomic §357, Lemma 357.2](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#357-全原树-clifford-历史的有限字符与尖锐算术恢复) | integer subring and original-basis coefficient multiplication |
| [TM §28.1–§28.2, Lemma 28.1, (28.3), (28.5)](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#281-来源整数正规形与六步运输) | unique normal coordinates, actual multiplication and leaf triple contributions |
| [TM §29.1, Definition 29.2](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#291-同一来源与叶阈值合同) | literal $\eta=(\mathbf u,c)$, used in original tag 2 |
| [TM §30.1, (TM.3003), Lemma 30.1 and Theorem 30.2](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#301-三个窗口与固定上限的分层记录) | exact fixed-$H$ whole-action/reject contract and target |
| [TM §31.1–§31.2, Definition 31.1 and Theorem 31.4](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#312-初始边界的精确八叶阈值) | common initialization, initial-target acquisition quantifiers and full-family $H\ge9$ impossibility |
| [TM §48.5, Proposition 48.10](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#485-已返回系数的付费精确转换) | already-returned exact coefficient adapter, including negative powers; 48.10 is a proposition within subsection 48.5 |
| [TargetRecoveryCriterion.lean, `target_recovery_criterion`](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean#L37) | nonempty-source fiber-constancy criterion; PR57.T4 supplies its actual record fiber by replay |
| [Observer-relative §§58–64, especially Definitions 60.3, 61.1, 61.3 and 64.1](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md#64-实际字面调度的完整符号费用与空间) | ownership, actual copies, consumer type/use and logical-unit accounting templates; its fixed widths/request bounds and atomic numeral maintenance are not imported |
| [Process geometry §3, Theorems 3.2 and 3.4](https://github.com/the-omega-institute/trureturing/blob/17b26a61db5577d2f67031c777e9d86e91c3e617/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md#3-可执行任务商与联合拼接) | legality, labels, successor and finite adaptive trace coordinates must all be retained; ordinary PR57.T3 proves them for this runtime |

The supplier facts concern their stated actual images, exact representations and contracts. A mathematical normal form, finite source set or abstract recovery map alone is not a supply channel. Every material, representation conversion and control computation used above is connected to its own finite paid transitions.

## 追加锚（本行以下为增补区）

## 58. 完整单位实际源的四分之一条件供应与原始目标逆解

在固定活上限和原 TM30 接口下，真实供应标签可以选择不同的实际上下文。本章给出完整单位历史族上的一个统一构造：对每个整数 $H\ge8$，以 $\lceil\lfloor H/4\rfloor/4\rceil$ 个真实供应符号恢复未修改初始来源的原 $q_H$，同一次执行不作 `Read`，至多接受一次 $\rho$，并至多作 $\lceil\log_2H\rceil+3$ 次整来源调用。承重的新论证是覆盖完整目标三角形的标签分割及其实际记录逆解；实际正源生成、行为商、材料传输、终端取得和有限规划沿用既有结果。该结论以精确同源的真实供应为条件，并不供应一个免费生产者。

### 58.1 原树、原目标与真实供应的量词

<a id="TM58-D1"></a>
**定义 58.1（完整实际单位族与不变的任务）。** 原树为自由有序非空二叉树 $t::=\alpha\mid\beta\mid\langle t,t\rangle$。相等关系保留叶序与全部括号。替换逐树定义为 $\rho(\alpha)=\beta$、$\rho(\beta)=\langle\beta,\alpha\rangle$ 和 $\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle$。组成为 $c(t)=(a,b)$，叶数为 $a+b$；Clifford 叶积满足 $A^2=1$、$B^2=-1$、$AB+BA=1$，记 $E_j(t)=E(\rho^jt)$。固定公开整数 $H\ge8$，置

<a id="TM58-E01"></a>
$$
\begin{aligned}
U_H&=\{t:1\le a+b\le H,\ (E_0,E_1,E_2)=(1,1,1)\},\\
m&=a+b,\qquad n=a+2b,\qquad \lambda_2=2a+3b=m+n,\\
q_H(t)&=\begin{cases}
(0,E_0,m),&n>H,\\
(1,c(t),E_0,E_1),&n\le H<m+n,\\
(2,\eta(t)),&m+n\le H.
\end{cases}
\end{aligned}
\tag{TM.5801}
$$

最后一行严格使用 TM30 的原始字面编码。按 TM28–29 的唯一正规形，$\eta=(\mathbf u,c)$，其中 $\mathbf u$ 是三个窗口的正规坐标。在单位族中固定

<a id="TM58-E02"></a>
$$
\mathbf u_{\mathrm{unit}}=((0,0,0),(0,0,0),(0,0,0)),\qquad
\eta(t)=(\mathbf u_{\mathrm{unit}},c(t)).
\tag{TM.5802}
$$

三个 $(0,0,0)$ 均按原 $(e,k,p)$ 顺序排列。因此后文给出组成后，标签2输出就是 $(2,(\mathbf u_{\mathrm{unit}},c))$；没有改成附加字段的目标，也没有以运行后当前目标替代初始目标。式（TM.5801）中的标签0、1、2是目标标签，须与供应符号 $i$ 区别。

在线接口始终是原 TM30 的当前 `Read`、整树 $\rho$ 尝试，以及将一个已知实际非空正上下文整体接在当前树左侧或右侧的尝试。整个候选叶数 $\le H$ 时接受，等号接受；拒绝保持完整实际树不变，不返回候选读数。公共参数、供应符号、动作名、实际上下文身份及括号、真实响应和实际读均属于完整记录。每个下一动作与停止输出只依赖共同公开量和已取得记录；相同标签有相同程序与初始化。运行可离开 $U_H$，此后仍按同一 ambient 整候选语义执行。成员条件不是在线成员测试。接口没有尺寸、目标、档案、导航、时钟或费用读口，也没有变上限、复位、复制、来源替换或逆拼接。

真实供应的条件是：首次在线动作之前，供应者已经持有这个精确未修改初始树的真实原目标信息，或持有能认证该原目标且与这棵原树精确配对的档案；供应者据此计算总标签函数 $\ell_H:U_H\to\mathcal L_H$。消费者只收到公开 $H$ 与其真实符号。另一棵同目标代表树、另一个档案或没有精确身份关联的句柄都不能代替这一同源配对条件。原目标证据的取得、解析、成员与身份认证、生产、交付、保留各有自己的费用。下文证明这一条件成立时的消费者构造，未证明这些外部条件已在物理装置中实现。

记 $A_U(H)$ 为上述条件任务的最小非空供应字母表基数。其竞争者保留任意依赖精确叶词和括号的总标签、任意已取得记录、所有 ambient 有限自适应原协议、`Read`、两侧任意混合正上下文和任意接受替换深度。下面的充分标签恰经由原目标分解；这不是最小化问题的附加限制。

<a id="TM58-L2"></a>
**引理 58.2（完整实际像与字面目标三角形）。** 写 $H=4h+\delta$，其中 $h=\lfloor H/4\rfloor\ge2$、$0\le\delta\le3$。完整 $U_H$ 的组成像恰为 $(4r,4s)$，$r,s\ge1$、$r+s\le h$。令 $z=r+s$、$w=r+2s$，则

<a id="TM58-E03"></a>
$$
2\le z\le h,\qquad z+1\le w\le2z-1,\qquad
(m,n,\lambda_2)=(4z,4w,4(z+w)),\qquad
(r,s)=(2z-w,w-z).
\tag{TM.5803}
$$

置 $C(z,w)=(4(2z-w),4(w-z))$。原目标的完整字典为

<a id="TM58-E04"></a>
$$
\begin{aligned}
Z(z)&=(0,1,4z),\\
\tau_h(z,w)&=\begin{cases}
(2,(\mathbf u_{\mathrm{unit}},C(z,w))),&z+w\le h,\\
(1,C(z,w),1,1),&z+w>h,
\end{cases}\quad(w\le h),\\
q_H(t)&=\begin{cases}Z(z),&w>h,\\ \tau_h(z,w),&w\le h.\end{cases}
\end{aligned}
\tag{TM.5804}
$$

这里每个有限点对应一个不同原目标；每个 $w>h$ 的行只对应 $Z(z)$，但该行全部隐藏组成仍属于输入域。

证明。复用 Atomic359.1–3、Atomic360.2–4 及其 TM51.2–3 应用。共同单位正规参数全为零，八边次数化为 $(r,r,r,r;s,s,s,s)$。非空及有效支撑连通排除 $r=0$ 或 $s=0$：只有一组边非零时支撑分裂，两组皆零时没有来源。反之，每个正参数有实际正词

<a id="TM58-E05"></a>
$$
\omega_{r,s}=\alpha^{2r-1}\beta^{2s}\alpha\beta^{2s-1}\alpha^{2r}\beta,
\tag{TM.5805}
$$

其八边次数正、平衡、连通，三窗皆为单位，组成为 $(4r,4s)$。Atomic360.3 的充要对应还给出该次数的全部 Euler 叶词和这些词的全部有序二叉括号化；显示词只证明每个参数有源，未缩小输入域。初始叶数约束恰为 $r+s\le h$，原替换组成公式给出（TM.5803）。由于资源均为四的倍数，$4w\le H$ 等价于 $w\le h$，$4(z+w)\le H$ 等价于 $z+w\le h$，对四种 $\delta$ 一律成立，包括等号。代入（TM.5801）–（TM.5802）得到（TM.5804）。$\square$

### 58.2 标签选择的实际上下文与全部响应

<a id="TM58-D3"></a>
**定义 58.3（四分之一供应与共同执行器）。** 令

<a id="TM58-E06"></a>
$$
L=\left\lceil\frac h4\right\rceil
=\left\lfloor\frac{H+12}{16}\right\rfloor,\qquad
\mathcal L_H=\{1,\ldots,L\},\qquad c_i=2L+2i-2.
\tag{TM.5806}
$$

供应者按原目标字典计算

<a id="TM58-E07"></a>
$$
\ell_H(t)=\begin{cases}
1,&w>h,\\
1+((z-1)\bmod L),&w\le h,\ z\le2L,\\
\lceil x/2\rceil,&w\le h,\ z>2L,\ x\equiv y\pmod2,\\
\lceil y/2\rceil,&w\le h,\ z>2L,\ x\not\equiv y\pmod2,
\end{cases}\qquad (x,y)=(z-2L,w-2L).
\tag{TM.5807}
$$

第一行不读取标签0隐藏的 $w$；在原目标处只需判断已给的目标标签并供应符号1。有限目标已保留组成，可恢复 $z,w$ 后计算其余三行。因此这是原目标的一个函数，符合定义58.1的供应边界。

固定每个正整数 $p$ 的公开实际全 $\alpha$ 树 $v_p$：$v_1=\alpha$，$v_{p+1}=\langle v_p,\alpha\rangle$。收到符号 $i$ 后，共同程序先计算 $c_i$。若 $c_i<h$，尝试一次整右拼接 $\langle t_{\mathrm{cur}},v_P\rangle$，其中 $P=H-4c_i$；若 $c_i\ge h$，真实省略这一次调用，并仅在算术中置 $P=0$。随后无论真实响应为何，均尝试 $\rho$ 恰好一次，再在实际得到的 ambient 树上执行 §58.4 的既有 $\mathrm{Size}_H$，取得它的入口叶数 $M$。最后按 §58.3 的字典输出原目标。

省略模式记作 O；它没有上下文候选、没有上下文响应，也没有空树 $v_0$。即使 $c_i=h$ 且 $\delta>0$，未执行的表达式 $H-4c_i=\delta$ 为正，程序仍省略，不以它代替 $P=0$。在实际发出模式中，A、R 分别表示真实接受、拒绝；AA、AR、RA、RR 按上下文、$\rho$ 的先后排列。OA、OR 只表示省略模式中的真实 $\rho$ 响应。符号、模式、所有实际前缀响应以及入口 $M$ 都保留；实际动作身份由公开 $H,i$ 和该记录确定。

<a id="TM58-L4"></a>
**引理 58.4（范围、占用与整候选分支）。** 式（TM.5807）在整个 $U_H$ 上取值于 $\mathcal L_H$，每个符号实际被使用。在发出模式中 $P>0$，所有实际分支恰如下表，等号均接受。

| 58分支 | 原始组成条件 | $\mathrm{Size}_H$ 的实际入口 $M$ |
| --- | --- | --- |
| 58AA | $z\le c_i,\ w\le c_i$ | $4w+P$ |
| 58AR | $z\le c_i,\ w>c_i$ | $4z+P$ |
| 58RA | $z>c_i,\ w\le h$ | $4w$ |
| 58RR | $z>c_i,\ w>h$ | $4z$ |
| 58OA | 省略且 $w\le h$ | $4w$ |
| 58OR | 省略且 $w>h$ | $4z$ |

每个入口均满足 $1\le M\le H$。拒绝从不插入被拒材料，也从不局部执行被拒宏。

证明。由 $L=\lceil h/4\rceil$ 得 $4L-3\le h\le4L$。有限高区有 $1\le x<y\le h-2L\le2L$，故两种向上取整都在 $1,\ldots,L$；低区余数及标签0规则也在此范围。若 $L\ge2$，每个 $i\ge2$ 被实际有限点 $(i,i+1)$ 使用，符号1被 $(L+1,L+2)$ 使用；这些点的列不超过 $h$，因为 $L+2\le4L-3\le h$。$L=1$ 时非空族只使用符号1。因 $h=4k+e$，$0\le e\le3$，逐 $e$ 代入得（TM.5806）第二个表达式对每个 $\delta$ 都成立。

若 $c_i<h$，则 $P=4(h-c_i)+\delta\ge4$，上下文是实际非空树。整拼接候选大小为 $4z+P$，所以接受当且仅当 $z\le c_i$。若接受，加入组成 $(P,0)$；$\rho$ 候选大小为 $4w+P$，所以接受当且仅当 $w\le c_i$。若上下文拒绝，原树完整保持，$\rho$ 候选为 $4w$，所以接受当且仅当 $w\le h$。省略分支直接使用后者。接受 $\rho$ 将当前／下一资源 $(m',n')$ 更新为 $(n',m'+n')$；特别地，发出并两次接受后的下一资源为 $4(z+w)+2P$，并非 $4(z+w)+P$。这些真实更新给出表内入口。接受的整候选证明大小不超过 $H$，拒绝保留先前合法树，因而所有入口合法。$\square$

### 58.3 完整分割的普通证明与显式逆解

<a id="TM58-L5"></a>
**引理 58.5（有限低区的两行分离）。** 在一个固定符号 $i$ 的有限低区 $z\le2L$，只有行 $z=i$ 和 $z=L+i$；不满足原三角形的行忽略。在发出模式中它们都接受上下文，且其 AA 列区间互不相交；有限 AR 至多为第二行的一个端点。

证明。低区的余数定义恰给这两行，行1本来不存在。因 $c_i\ge2L$，两行都满足 $z\le c_i$。第一行列区间为 $[i+1,2i-1]$，其上界不超过 $c_i$，故全为 AA。第二行上界 $2(L+i)-1=c_i+1$；其 AA 区间为 $[L+i+1,\min(c_i,h)]$，超出 $c_i$ 的有限列只可能是 $c_i+1$，此时为 AR。两个 AA 区间分离，因为 $2i-1<L+i+1$。区间为空、被 $h$ 截断以及 $w=c_i$ 等号都已经包含；没有低区有限 RA 或 RR。$\square$

<a id="TM58-L6"></a>
**引理 58.6（有限高区的奇偶尾与相邻例外）。** 固定符号 $i$，在发出模式的有限高区中没有 AA 或 RR。每个 AR 行至多含一个有限原目标，每个 RA 列也至多含一个有限原目标。唯一需要单独处理的异奇偶相邻点是 $(x,y)=(2i-1,2i)$，它属于 RA。

证明。若 $x,y$ 同奇偶，标签由 $x$ 决定，$x$ 为 $2i-1$ 或 $2i$。两者均大于 $c_i-2L=2i-2$，所以上下文拒绝；有限 $w\le h$ 使 $\rho$ 接受，得到 RA。同奇偶与 $x<y$ 进一步给出：$x=2i-1$ 时 $y\ge2i+1$ 且奇；$x=2i$ 时 $y\ge2i+2$ 且偶。

若 $x,y$ 异奇偶，标签由 $y$ 决定，$y$ 为 $2i-1$ 或 $2i$。当 $y=2i-1$ 时，$x$ 偶且 $x\le2i-2$，上下文接受，$w=c_i+1>c_i$ 使 $\rho$ 拒绝，得到 AR。当 $y=2i$ 时，$x$ 奇且 $x\le2i-1$；若 $x\le2i-3$，得到 AR，若 $x=2i-1$，则上下文拒绝而 $\rho$ 接受，得到 RA。另一个相邻点 $(2i-2,2i-1)$ 仍是 AR，不能把全部相邻点统一划入 RA。

于是 AR 中已知行 $x$ 后，唯一列为 $y=2i-1+(x\bmod2)$。RA 中已知列 $y$ 后，奇列给 $x=2i-1$，偶列 $y=2i$ 给相邻例外 $x=2i-1$，其余实际偶列给 $x=2i$；同奇偶来源不可能占据 $y=2i$。这证明所述唯一性，包含最大尾列 $y=h-2L$ 和所有向上取整端点。$\square$

<a id="TM58-L7"></a>
**引理 58.7（每个标签0隐藏组成的覆盖）。** 若 $L\ge2$，标签0来源只可能在行 $z\ge2L$。可能的行 $z=2L$ 恰在 $h\le4L-2$ 时出现；它使用符号1并全部进入一个有限目标未占用的 AR 行。其余标签0行全部进入 RR。

证明。标签0要求 $h<w\le2z-1$。若 $z\le2L-1$，则 $2z-1\le4L-3\le h$，矛盾。$z=2L$ 时存在隐藏列当且仅当 $h<4L-1$，即 $h=4L-3$ 或 $4L-2$。此时 $c_1=2L<h$，实际上下文非空，$z=c_1$ 在等号处接受；每一个隐藏 $w>h$ 都满足 $w>c_1$，故 $\rho$ 拒绝，入口为 $8L+P=H$。所有这些隐藏组成只要求同一个 $Z(2L)$。

有限低区的行 $2L$ 使用符号 $L\ne1$；符号1的有限低区 AR 行只能是 $L+1<2L$。有限高区行大于 $2L$，也不能占据这个行。故符号1的 AR 行 $2L$ 是原目标字典的空位。其他标签0行满足 $z>c_1$，拒绝上下文，继而每一个 $w>h$ 都使 $\rho$ 拒绝，入口为 $4z$。这里没有选择一个隐藏组成充当整行；不等式逐一覆盖该行的全部隐藏列。$\square$

<a id="TM58-L8"></a>
**引理 58.8（真实省略的完整字典）。** 若 $L\ge2$，省略当且仅当 $i=L$ 且 $h\in\{4L-3,4L-2\}$。这个符号的实际来源只有有限低区行 $L$、$2L$，均接受 $\rho$；两行的入口列区间分离，OR 不可达。

证明。对 $i<L$，$c_i\le4L-4<h$；对 $i=L$，$c_L=4L-2$，故省略条件恰如所述。此时 $y\le h-2L\le2L-2$，且 $x<y$。高区的任一种取整标签都不可能达到 $L$。标签0统一使用符号1，与 $L$ 不同。剩下的低区行 $L$、$2L$ 都有限，省略后 $\rho$ 接受；其列区间分别为 $[L+1,2L-1]$、$[2L+1,h]$，没有 $w=2L$，故入口 $4w$ 分离两行。这也是省略后不能减去未插入的 $\delta$ 的原因：此处来源上没有该材料。$\square$

<a id="TM58-L9"></a>
**引理 58.9（全部一符号基例）。** $L=1$ 恰对应 $h=2,3,4$。对每个 $\delta\in\{0,1,2,3\}$，以下列表穷尽实际组成三角形，表中有限输出均为原标签1。

| 58基例 | 所有原始组成点 $(z,w)$ | 实际分支、入口与原输出 |
| --- | --- | --- |
| 58基例2 | $(2,3)$ | 省略；OR，$M=8$，输出 $Z(2)$ |
| 58基例3有限 | $(2,3)$ | $P=H-8>0$；AR，$M=H$，输出 $\tau_3(2,3)$ |
| 58基例3隐藏 | $(3,4),(3,5)$ | RR，$M=12$，输出 $Z(3)$ |
| 58基例4有限低 | $(2,3)$ | $P=H-8>0$；AR，$M=H$，输出 $\tau_4(2,3)$ |
| 58基例4有限高 | $(3,4)$ | RA，$M=16$，输出 $\tau_4(3,4)$ |
| 58基例4隐藏 | $(3,5),(4,5),(4,6),(4,7)$ | RR，$M=4z$，输出 $Z(z)$ |

证明。三角形在 $h=2,3,4$ 分别有 $1,3,6$ 个点，表内已全部列出。$c_1=2$；$h=2$ 时真实省略，对全部 $\delta$ 都有 $12>H$，故 $\rho$ 拒绝。$h=3,4$ 时上下文长度分别为 $4+\delta$、$8+\delta$。行2在上下文等号处接受而列3超出截止2，故 AR；$h=4$ 的 $(3,4)$ 拒绝上下文，$\rho$ 在 $4w\le H$ 处接受，是引理58.6的高区相邻例外。其余点满足 $z>2,w>h$，故 RR。两个有限点均有 $z+w>h$，按初始测试输出标签1。$\square$

<a id="TM58-D10"></a>
**定义 58.10（实际记录上的显式逆解）。** 对实际发出模式使用已知 $P=H-4c_i$；对省略模式使用算术 $P=0$。以下解码函数只在真实供应、真实响应及真实终端入口的记录像上断言正确。它不声称任意数字元组都有对应来源；离开记录像的输入可标为无效。

| 58逆解分支 | 恢复初始坐标的公式 | 原始字面输出 |
| --- | --- | --- |
| 58逆AA | $w=(M-P)/4$；若 $w\le2i-1$，置 $z=i$，否则置 $z=L+i$ | $\tau_h(z,w)$ |
| 58逆AR零 | $z=(M-P)/4$；若 $i=1,z=2L,h\le4L-2$ | $Z(z)$ |
| 58逆AR有限 | 上一条件不成立；同样取 $z=(M-P)/4$。若 $z\le2L$，置 $w=c_i+1$；否则置 $w=c_i+1+(z\bmod2)$ | $\tau_h(z,w)$ |
| 58逆RA | $w=M/4$；若 $w$ 奇或 $w=c_i+2$，置 $z=c_i+1$，否则置 $z=c_i+2$ | $\tau_h(z,w)$ |
| 58逆RR | 不恢复隐藏 $w$ | $(0,1,M)$ |
| 58逆OA | $w=M/4$；若 $w\le2i-1$，置 $z=i$，否则置 $z=L+i$ | $\tau_h(z,w)$ |
| 58逆OR | 不恢复隐藏 $w$ | $(0,1,M)$ |

AR零行的条件自动排除 $h=3,4$；在 $h=2$ 不存在发出模式。RA 中 $2L$ 为偶数，故 $w$ 与 $y=w-2L$ 同奇偶，$w=c_i+2$ 恰为 $y=2i$，所以该式与引理58.6的列逆解完全相同。OA 实际只在引理58.8中出现，$i=L$，其阈值 $2i-1=2L-1$ 分离两行。OR 实际只在 $h=2,i=1,M=8$ 出现。减去 $P$ 只发生在实际接受上下文的 AA、AR 中；RA、RR、OA、OR 都没有插入该前缀材料。

<a id="TM58-T11"></a>
**定理 58.11（完整分割与原目标唯一逆解）。** 对所有 $H\ge8$ 及每个实际 $t\in U_H$，式（TM.5807）的真实供应与定义58.3的实际前缀产生上述六种分支之一；定义58.10利用真实分支及 $M$ 恰输出初始 $q_H(t)$。在固定 $H,i$ 的每个实际分支／入口格中，原目标唯一。

证明。引理58.5穷尽有限低区，给出 AA 的两行阈值和有限低区 AR 的唯一列 $c_i+1$。引理58.6穷尽有限高区，给出高区 AR 的列公式及 RA 的行公式。低区 AR 恢复行 $z\le2L$，高区 AR 恢复行 $z>2L$，因此两字典不相撞；高区无 AA，所以 AA 的低区阈值完整。引理58.7单独覆盖每个隐藏标签0组成，给出 AR零行与 RR 原目标，且证明它们与有限字典分离。引理58.8穷尽 $L\ge2$ 的省略输入，OA 的同一阈值恢复唯一初始行，OR 不出现。引理58.9穷尽剩下的一符号基例，逐项与逆解表一致。这些域并成整个（TM.5803），没有剩余组成。

在实际 AA、AR 中，入口减去实际前缀后恰为四的倍数；其余入口本来为四的倍数。所得有限 $(z,w)$ 均为原三角形中的点，所以（TM.5804）有限输出的组成正，初始标签测试准确；特别在 $z+w=h$ 输出原标签2，而非运行后被材料改变的标签。标签0输出只保留原本应保留的 $Z(z)$。故解码逐源正确。每个格的公式给出唯一原目标；标签0多个隐藏组成占同格时，原目标本来相同。$\square$

### 58.4 既有终端取得与同一次执行的联合上界

<a id="TM58-P12"></a>
**命题 58.12（ambient 入口尺寸取得的复用证书）。** 原 TM44.5 证明中的（TM.4419）–（TM.4420）及 TM51.5 所给 $\mathrm{Size}_H$，只需当前实际树入口叶数 $1\le M\le H$，不需单位三窗或已知组成。它以至多 $\lceil\log_2H\rceil+1$ 次整非空右上下文尝试取得入口 $M$；不作 `Read` 或 $\rho$，最后树大小为 $H$，并包含一次真实单叶拒绝。

证明。为明确本构造的调用前提，重述该既有机制。初始化 $l=0,u=H,U=0$；$U$ 计这段终端中已接受的全 $\alpha$ 叶数。维持

<a id="TM58-E08"></a>
$$
l<M\le u,\qquad U=H-u,\qquad
\lambda(t_{\mathrm{cur}})=M+U.
\tag{TM.5808}
$$

当 $u-l>1$，置 $k=\lfloor(l+u)/2\rfloor$，尝试整右接公开树 $v_{u-k}$。因为 $l<k<u$，它实际非空。整候选为 $M+H-k$，所以真实接受恰等价于 $M\le k$。接受则置 $u=k$ 并将 $U$ 加上旧 $u-k$；拒绝则只置 $l=k$，实际树不变。两分支保持（TM.5808），等号 $M=k$ 走接受。区间宽度至多变为旧宽度的一半向上取整；至多 $\lceil\log_2H\rceil$ 次后宽度为1，整数 $M$ 唯一等于 $u$。此时

<a id="TM58-E09"></a>
$$
M=u=H-U,\qquad \lambda(t_{\mathrm{cur}})=H.
\tag{TM.5809}
$$

再尝试整右接单叶 $v_1$，候选为 $H+1$，真实拒绝。即使入口 $M=H$、没有接受任何填充，也保留这次拒绝。读到的响应记录及已接受长度使程序计算入口 $H-U$；程序从未调用尺寸读口。整个过程适用于任意 ambient 合法入口，也未恢复入口原树。$\square$

<a id="TM58-T13"></a>
**定理 58.13（完整实际族的四分之一条件恢复）。** 对每个整数 $H\ge8$，在定义58.1的精确未修改原树真实供应条件下，定义58.3给出一个统一有效的供应公式和一个共同初始化的确定程序。对每个实际 $t\in U_H$，该程序在同一棵来源的同一次有限执行中输出原 TM30 字面 $q_H(t)$，且同时满足

<a id="TM58-E10"></a>
$$
\begin{aligned}
|\mathcal L_H|&=\left\lceil\frac{\lfloor H/4\rfloor}{4}\right\rceil,
&N_{\mathrm{Read}}&=0,\\
\operatorname{dep}_{\rho}&\le1,
&N_{\mathrm{whole}}&\le\lceil\log_2H\rceil+3.
\end{aligned}
\tag{TM.5810}
$$

其中 $N_{\mathrm{whole}}$ 计每次实际整候选尝试，包括被拒上下文、被拒 $\rho$ 和终端单叶拒绝；深度只计接受的 $\rho$。真实省略路径还有 $N_{\mathrm{whole}}\le\lceil\log_2H\rceil+2$。特别地，原 unrestricted 条件问题满足 $A_U(H)\le\lceil h/4\rceil$。

证明。引理58.4已证明所有符号在范围内、实际占用，以及每个分支的真实入口 $1\le M\le H$，故命题58.12的 ambient 前提逐一满足。定理58.11的显式字典利用该段真实取得的入口值输出原目标。发出路径有一次前缀上下文、一次 $\rho$ 及至多 $\lceil\log_2H\rceil+1$ 次终端调用；省略路径少一次前缀调用。只有前缀那一次 $\rho$ 可能接受，终端没有 $\rho$，整个程序没有 `Read`。各个资源界因此属于这一个程序、同一条实际路径，未将不同控制器的字母表和调用成本合并。区间有限收缩及有限整数逆解保证逐源有限停止。

上述计算在所有实际叶词与括号上成立，原因有两层。第一，Atomic360 的完整充要对应及引理58.2覆盖每一个实际来源的组成，不只是显示词（TM.5805）；每个整候选大小由真实组成更新，与叶序和括号无关。第二，供应函数在每个原 $q_H$ 纤维上恒定。TM30.2 的行为等价和 TM47.1–2 的代表提升保证：相同初始目标、同标签及同初始化的所有实际实现，使用这个共同程序时有相同动作身份、响应、停止和输出，包括标签0中原目标隐藏组成不同的实现。代表在这里只作证明装置，运行树从未被换成代表。故（TM.5810）同时量化完整 $U_H$ 的每个词及其每一种有序括号化，而不是受限前缀族或有限帽表。$\square$

### 58.5 完整记录、原始／当前配对与必要反例

<a id="TM58-P14"></a>
**命题 58.14（所选终端执行器的精确记录格）。** 对固定 $H,i$，本程序的实际模式、实际前缀响应和入口 $M$ 恰决定完整动作／响应记录；反过来完整记录决定这些量。因此定理58.11是这个终端执行器的精确原目标兼容性证书。该证书未给任意原协议一个记录正规形。

证明。前缀实际树 $v_P$、侧别与括号都是公开 $H,i$ 的函数；省略同样由公开条件决定。随后 $\mathrm{Size}_H$ 的 $l,u$、每次实际树 $v_{u-k}$ 和响应都由 $M$ 确定，包含最后单叶拒绝。故这些量恢复本程序的整记录。完整记录保留供应符号和前缀响应，又由终端累计接受长度给出 $M=H-U$，所以反向也成立。

原始／当前配对的区别可在停止处直接看到。在 AA、AR、RA、RR、OA、OR 六种分支中，终端入口的当前 $E_0$ 依次是 $B^P,A^P,1,1,1,1$，因为原 $E_0=E_1=1$，接受前缀在右侧，且 $\rho(v_P)$ 为全 $\beta$ 树。终端再右接总共 $U=H-M$ 个 $\alpha$，所以在一个固定记录格中停止时的当前 $E_0$ 相同。原树有正 $\beta$ 数；上下文和至多一次接受 $\rho$ 都保持正 $\beta$ 数。因此停止时当前叶数为 $H$，下一替换叶数严格大于 $H$，当前目标为

<a id="TM58-E11"></a>
$$
q_H(t_{\mathrm{stop}})=(0,E_{\mathrm{entry}}A^{H-M},H).
\tag{TM.5811}
$$

若一个这样的记录格含不同原目标，它们会同时有相同完整记录及相同当前 $q_H$，TM38.1 就排除任何后来修复。定理58.11证明本分割没有这种格。一般的继续策略在选择本终端之前可能保留更多信息；此处的必要充分性只针对已固定的执行器。TM45.1–4 的同源原始／当前历史关系与 TM47.4、47.8 的全动作对应、有限稳健规划仍是既有供应，本章未把这一格证书命名为新的通用规划器。$\square$

<a id="TM58-P15"></a>
**命题 58.15（固定较小截止的原目标擦除与移动守卫）。** 一个较小上限子任务的目标不能自动代替原目标；接受材料也不能在任意替换深度只减去一个常量。具体地，取 $2\le c<h$、$P=H-4c$，在原单位树上先右接 $v_P$。对任何接受行 $2\le z\le c$ 和 $w>c$，当前 $q_H$ 都是 $(0,A^P,4z+P)$，该行被合并的不同原目标数为

<a id="TM58-E12"></a>
$$
d_h(c,z)=\max\{0,\min(2z-1,h)-c\}
+\mathbf1_{\{2z-1>h\}},\qquad
\max_{2\le z\le c}d_h(c,z)=\min(c-1,h-c+1).
\tag{TM.5812}
$$

另一方面，取 $F_0=0,F_1=F_2=1$。初始全 $\alpha$ 材料 $P$ 经 $j$ 次接受替换，其当前和下一资源贡献分别为 $PF_{j+1}$、$PF_{j+2}$。在相应未加材料的子源上，后续上下文增量 $d$ 和下一替换必须分别检验

<a id="TM58-E13"></a>
$$
\mathrm{child}_{\mathrm{cur}}+d\le H-PF_{j+1},\qquad
\mathrm{child}_{\mathrm{next}}\le H-PF_{j+2}.
\tag{TM.5813}
$$

证明。接受行的当前大小为 $4z+P$，下一大小 $4w+P>H$，读积为 $A^P$，所以当前标签0相同。每个 $c<w\le\min(2z-1,h)$ 是一个不同有限原目标；若还有 $w>h$，整行的这些隐藏列另贡献一个 $Z(z)$。这给出（TM.5812）的计数，随 $z$ 不减。若 $2c-1\le h$，行 $c$ 的值为 $c-1$；若 $2c-1>h$，值为 $h-c+1$，边界 $2c-1=h$ 也与公式一致。同标签下，所有此前无修改读都为单位，接受后的当前目标相同，TM38.1排除任意后来区分；这是这个固定前缀的必要负载，未限制其他控制器。

例如 $H=40,c=8,P=8$，实际词 $\omega_{3,3}$、$\omega_{2,4}$ 给 $(z,w)=(6,9),(6,10)$。其 $q_{32}$ 均为 $(0,1,24)$，而原 $q_{40}$ 是不同标签1；接受前缀后均变为当前 $(0,1,32)$。本构造在这两点供应符号3，$c_3=h=10$，真实省略前缀，接受 $\rho$ 后入口分别36、40，故没有运行这个擦除前缀。

材料传输则直接复用 TM30.1 与 TM45.3–4 的 Fibonacci 组成更新：初始 $(P,0)$ 的 $j$ 次像，其叶数和下一叶数为所述两个贡献，给出（TM.5813）。其他接受的正材料只再加非负贡献，不能取消差异。例如 $H=80$，初始 $\omega_{3,2}$ 的 $(z,w)=(5,7)$；未加材料、上限60的两次替换候选为28、48，都接受。实际先在上限80加 $P=20$ 后，两候选为48、88，第二次拒绝。本构造只尝试一次 $\rho$，使用引理58.4的真实守卫，随后终端不作替换，故未使用恒定剩余上限的多层子任务。$\square$

<a id="TM58-P16"></a>
**命题 58.16（响应与实际动作身份不能擦除）。** 入口大小的边际相等不能代替完整记录相等；将标签所选择的实际上下文改成统一上下文也可能使原目标永久碰撞。

证明。在 $H=80,L=5,i=1,c_i=10,P=40$，有限点 $(6,11)$ 是 AR，$M=64$，原标签2组成为 $(4,20)$；隐藏点 $(16,21)$ 是 RR，$M=64$，原目标为 $(0,1,64)$。二者真实 $\rho$ 响应相同，终端后缀记录相同，但上下文响应不同。删去上下文响应便丢失区别。另在 $H=72,L=5,i=1,P=32$，$(6,10)$ 为 AA，$(10,19)$ 为 AR，二者都接受上下文，$M=72$，而原目标组成分别 $(8,16)$、$(4,36)$；删去 $\rho$ 响应也丢失区别。两种响应在本程序的逆解中都有实际作用。

再取 $H=80,i=5$。实际供应点 $(11,20)$、$(13,20)$ 分别由 $\omega_{2,9}$、$\omega_{6,7}$ 实现，原标签1组成为 $(8,36)$、$(24,28)$。本程序的 $c_5=18,P=8$ 给二者 AR，入口52、60；若将这个实际动作改为全 $\alpha$ 长度40，二者都拒绝前缀，再接受 $\rho$ 至80，当前 $E_0=1$，当前目标均为 $(0,1,80)$，完整记录也相同。TM38.1排除所有后来修复。共同参数化程序必须保留“真实标签—实际上下文身份”的关系，不能把公式相同误当实际上下文相同。$\square$

<a id="TM58-P17"></a>
**命题 58.17（受限十纤维字典的原样扩展失败）。** TM56-T3 的十纤维成功不能将其同一符号、同一程序原样扩展为完整 $U_H$ 的恢复。对每个 $H=36+\delta$，$0\le\delta\le3$，原样扩展在实际点 $(5,7)$ 与 $(6,7)$ 上永久碰撞。

证明。实际词可取 $\omega_{3,2}$ 和 $\omega_{5,1}$，原标签1组成为 $(12,8)$、$(20,4)$，不同。两者都拒绝第一上下文 $v_{H-19}$，因为候选大小分别为 $H+1$、$H+5$。随后同一上下文 $K$ 的当前／下一增量 $(d,e)$ 按 $\delta=0,1,2,3$ 分别为 $(1,1),(1,2),(2,3),(3,4)$；可取实际叶词 $\alpha,\beta,\alpha\beta,\alpha^2\beta$，固定公开括号。两源均接受这个上下文，再接受 $\rho$ 到大小 $28+e$，当前读积均为 $E_1(K)$；下一候选为 $4(z+7)+d+e>H$，故当前目标、完整前缀记录相同。TM38.1给出永久碰撞。这一计算只用原守卫和传输，不将受限族成功当作全族前提。本章的两源标签分别为2、3；前者发出 $c_2=8$ 的上下文而进入 AA，后者在 $c_3=10\ge h$ 真实省略并进入 OA，均由完整字典覆盖。$\square$

### 58.6 原供应比较、CPF 边界与未解的必要系数

<a id="TM58-P18"></a>
**命题 58.18（与实际 TM55 证书的字母表比较）。** TM55-T6 的实际全族证书为 $B_{55}(h)=\lfloor(h+1)/3\rfloor$，而非 $\lceil h/3\rceil$。对所有 $h\ge2$，本章 $L\le B_{55}(h)$；严格不等式恰在 $h=8,11,12$ 和每个 $h\ge14$ 成立。比较保留各自同一执行的联合证书，不给逐路径调用数或总成本的支配关系。

证明。$L=1$ 的 $h=2,3,4$ 直接有 $B_{55}=1$。$L\ge2$ 时 $h+1\ge4L-2\ge3L$，所以 $B_{55}\ge L$。若 $L\ge5$，$h+1\ge4L-2\ge3L+3$，故 $B_{55}\ge L+1$。$L=4$ 的 $h=14,15,16$ 也有 $h+1\ge15=3L+3$。其余 $h=2,\ldots,13$ 直接代入两公式，等号恰在 $2,3,4,5,6,7,9,10,13$，严格点为8、11、12，完成所有端点比较。$\square$

TM55 的 $h=2,3,4$ 基例省略前缀上下文，有更细的 $\lceil\log_2H\rceil+2$ 调用界；本章 $h=3,4$ 发出实际正上下文，可能使用 $+3$。TM51 的 $h=2$ 还允许直接零调用输出，$h=3$ 有零接受替换深度的专门方案。这些较细成本不被本章统一构造替代。对于 $H=400,401,402,403$，本章25符号、TM55实际33符号；两者各自无 `Read`、接受深度至多1、调用至多12。但字母表下降不总降低定长位宽：$H=80$ 时5与7符号都需3位。整宏调用界也不是物理时间单位。

OR68–69 的完整 unrestricted 小上限精确结果仍为

<a id="TM58-E14"></a>
$$
A_U(H)=\begin{cases}
1,&8\le H\le19,\\
2,&20\le H\le39,\\
3,&40\le H\le55.
\end{cases}
\tag{TM.5814}
$$

特别在 $h=9$ 和 $h=13$，本章分别使用3、4符号，既有专门最优值分别为2、3。OR68.2 的配对构造有自己的至多一次接受替换、$\lceil\log_2H\rceil+4$ 调用证书；OR69.2、69.4 的专门组合有自己的至多一次接受替换、$\lceil\log_2H\rceil+5$ 调用证书。较小字母表和它所属控制器的成本须一同保留，不能借其字母表配上本章控制器的 $+3$ 界。

<a id="TM58-P19"></a>
**命题 58.19（共同正前缀类别的精确边界）。** 按 TM56-D1，CPF 要求在第一次 $\rho$ 前对所有供应符号使用一个相同的实际非空上下文及固定侧别，仅容许无修改读穿插，且此前没有其他修改尝试。定义58.3的程序在 $L\ge2$ 时不属于此类别；在 $h=3,4$ 时属于单符号 CPF，在 $h=2$ 时因省略而不属于。

证明。引理58.4保证所有符号被实际占用。若 $L\ge2$，符号1发出前缀，因为 $2L<h$。若某符号省略，则缺少 CPF 要求的共同非空前缀；若全部发出，符号1与2的实际上下文长度相差8，树身份不同，故也不能满足共同前缀。$h=3,4$ 只有一个符号，实际程序确为一个正前缀后一次 $\rho$，满足该类别定义；$h=2$ 没有前缀。一个共同程序从标签计算上下文，并不把不同的实际树变成同一棵树。故 TM56-T1 的 CPF 必要障碍保留其限定域，未成为原 unrestricted 任务的必要系数；本章上界与该障碍的量词不同。$\square$

既有 TM54.3–4 的全策略必要下界、OR70.2–3 的点态／Ferrers 必要条件，以及（TM.5814）都保留其原假设。特别已有的

<a id="TM58-E15"></a>
$$
\gamma h-O(1)\le A_U(H)\le\left\lceil\frac h4\right\rceil
=\frac h4+O(1)=\frac H{16}+O(1),\qquad
\gamma=\frac{7-3\sqrt3}{11},
\tag{TM.5815}
$$

仍有间隙。这里仅新增右侧充分上界。原竞争者没有被限制为组成标签、无读、单侧全 $\alpha$ 上下文、一次替换或本章终端。完整 $A_U(H)$、尖锐首项系数、归一化极限的存在、深层历史能否继续降低字母表，以及任意原历史的最小共同兼容性刻画仍未由此解决；不存在本章所证明的四分之一必要系数或最优性。全 $\mathcal T_H$ 上的 TM37 下界也不能数值照搬到较小单位族。

### 58.7 复用来源、生产边界与数学范围

下表的不可变修订只固定引用文本；来源身份本身不另行断言其命题为真。普通证明的承重关系已经在各条证明中逐项说明。记三个理论卷分别为《Fibonacci 原子关系生成》《递归关系观察、传输与记忆完备》《观察者相对时空因果兼容恢复》；链接给出其实际文件和不可变修订。

| 58来源条目 | 精确已发表定位与不可变修订 | 本章对应及适用边界 |
| --- | --- | --- |
| 58来源生成 | [Atomic359.1–3、Atomic360.2–4](https://github.com/the-omega-institute/trureturing/blob/e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)，修订 `e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74` | 共同正规形、八边平衡连通、全部 Euler 词及全部括号；用于引理58.2的完整实际像，不只用独立窗口可达性。 |
| 58来源行为 | [TM30.1–2（TM.3001–4）、TM31.1、TM38.1](https://github.com/the-omega-institute/trureturing/blob/e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)，同一修订 `e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74` | 原字面目标、整守卫、等号接受、拒绝保持、共同初始化和行为商；永久碰撞还要求同标签、同完整历史及同当前目标，当前目标单独相等不够。 |
| 58来源传输 | [TM45.1–4，尤其（TM.4505）、（TM.4511–14）](https://github.com/the-omega-institute/trureturing/blob/e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)，同一修订 `e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74` | 同一实际来源的有序外因子、Fibonacci 资源与真实历史筛选；原始／当前配对不是消费者的隐藏读口。 |
| 58来源终端 | [TM44.5 证明（TM.4419–20）、TM51.5](https://github.com/the-omega-institute/trureturing/blob/e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)，同一修订 `e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74` | 仅要求实际 ambient 入口在 $[1,H]$ 的破坏性尺寸取得、真实终端拒绝及 $\log+1$ 界；未借用更强的完整窗口取得合同。 |
| 58来源提升规划 | [TM47.1–2（TM.4701–2）、TM47.4、47.8；TM51.2–3、51.9–11](https://github.com/the-omega-institute/trureturing/blob/e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)，同一修订 `e33c70ab6b3d80f132f5d7cb2fa82ebbc62fce74` | 完整认证目标覆盖和同目标代表提升；全上下文对应与稳健有限规划在其完整认证表、精确表示前提下已存在；本构造不在线调用规划器。原树保持生产障碍及分项成本继续适用。 |
| 58来源必要 | [TM54.3–4（TM.5412）、（TM.5414）](https://github.com/the-omega-institute/trureturing/blob/c469d049349b2f4b53daef9cee7d6db13bc9f805/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)，修订 `c469d049349b2f4b53daef9cee7d6db13bc9f805` | 原 unrestricted 同源条件问题的必要下界；保留其全部竞争者，不由新充分构造收窄域。 |
| 58来源三分之一 | [TM55.5–6，TM55-T6，（TM.5524–25）](https://github.com/the-omega-institute/trureturing/blob/9a21d168ab93cf1da72ebb98e64f4575437050f2/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#TM55-T6)，修订 `9a21d168ab93cf1da72ebb98e64f4575437050f2` | 完整相同任务的实际 $\lfloor(h+1)/3\rfloor$ 证书及自己的联合成本；小基例 $+2$ 保留。新增量是定义58.3、58.10和引理58.5–9的全域标签／动作分配及逆解。 |
| 58来源共同前缀 | [TM56-D1、TM56-T1、TM56-T3](https://github.com/the-omega-institute/trureturing/blob/25a023d7f087268131a63ca799cb530a0b0796b7/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#TM56-D1)，修订 `25a023d7f087268131a63ca799cb530a0b0796b7` | 共同实际正前缀类别及十纤维比较；本章完整构造的正面证明不以其定理作新增前提。命题58.17的失败由原接口直接计算。 |
| 58来源小上限 | [OR68.1、68.2、68.4–5、69.2、69.4–5](https://github.com/the-omega-institute/trureturing/blob/511f1920bceaaf9f6ec6411030fbd4da42abfbfd/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md)，修订 `511f1920bceaaf9f6ec6411030fbd4da42abfbfd` | 同完整单位任务，OR68 的 $\nu$ 为本章 $w$，OR69 的 $(x,y)$ 为本章 $(z,w)$；保留精确小上限和各自 $+4$、$+5$ 成本。 |
| 58来源点态 | [OR70.2–3，（70.5）、（70.15）](https://github.com/the-omega-institute/trureturing/blob/4f981b86a637c4aff1f1825ec0efe41dd5bb36e2/docs/develop/theory/OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md)，修订 `4f981b86a637c4aff1f1825ec0efe41dd5bb36e2` | 同域 Ferrers／点态必要条件；比较项，不是本章显式上界的前提。 |
| 58来源不同接口 | [Atomic383.1–2](https://github.com/the-omega-institute/trureturing/blob/f42b6ac7f772ac7d14711ced02a4f84d6302878e/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)，修订 `f42b6ac7f772ac7d14711ced02a4f84d6302878e` | 有限正整数索引集的 totient 支撑、Fibonacci 最小公倍数收费和 Robin 对数分母传输；没有本章的整树观察、同源供应或原目标接口，未供应本章标签分割或逆解的前提。 |

<a id="TM58-P20"></a>
**命题 58.20（条件供应不消除原树保持的生产障碍）。** 按 TM51.9 的原接口生产任务，一个共同初始化且在每个单位输入上保持精确初始原树的生产者只能输出常量；本章非恒定供应不由这样的生产者免费获得。

证明。每个单位输入有正 $\beta$ 数。接受非空上下文严格增叶，接受 $\rho$ 也严格增叶；原接口没有删除或逆操作，故若最终精确原树保持，途中不可能接受任何修改。当前读因此始终为单位，全部尝试的修改若发生都只能拒绝。共同初始化、同读和同响应给出同动作序列及同输出，输出只能为常量。这是既有生产边界的应用，不影响定义58.1以已经真实持有原目标信息为前提的条件消费者，但生产、同源认证和交付仍须单独承担。$\square$

在紧凑整数和公开上下文名字的表示约定下，$H,i,P,l,u,U,M$ 及必要模式、响应位只需 $O(\log(H+1))$ 个可变工作位；这只是本程序的充分摘要，不是完整记录、字面输出、展开上下文、证据档案或物理存储的上界，更不是最小存储结论。上下文身份及括号的生成、展开和交付，被拒候选材料与工作，整守卫与替换计算，整数运算、完整记录及输出、原始证据与身份配对、供应的生产交付保留以及物理持续时间均是独立资源坐标。一个来源调用不承担这些坐标之间的等价关系。

本章的新增分割和逆解属于 repo-derived 普通数学结果，其全称证明是引理58.5–9与定理58.11–13，不以有限样本或有限策略搜索替代。它恢复的是原行为目标，未恢复精确原树、括号、旧物理轨迹或物理时空。列明来源的复用不作全局文献原创性主张，普通证明也不构成 Lean 核验或物理仪器符合性结论。

## 追加锚（本行以下为增补区）

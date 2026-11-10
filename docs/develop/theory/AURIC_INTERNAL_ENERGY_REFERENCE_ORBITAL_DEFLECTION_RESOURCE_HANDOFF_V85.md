# 内部能量参照、轨道偏转与资源接力

从有限均值校准到二元能隙匹配

**AURIC v85：一个完整候选及其量子理论**

项目连续研究稿

2026 年 11 月 2 日

## 摘要

本轮承接 v84，研究持续原子门的圆轨道、当前态与切向的组合、不同轨迹的相交，以及轨道偏转是否必须借入能量。首先给出归一态的精确圆弧分解，说明有限态差与水平切向之间的区别；固定生成元在有效二能级载体上产生 Bloch 圆，但多频率生成元可以产生非闭合轨道。完整自治流的唯一性与投影读出的交叉并不矛盾。

本文只新增一个候选 $C_{85}$：在已重建的有限酉执行载体上，对事先固定的内部总能量读口，只要求完整本征参照框的输出均值等于输入读数。酉矩阵的双随机关系使能隙平方和非负，并将这些有限均值条件提升为全部能量块保持、全输入分布守恒及内部时间平移协变。同一候选还能压缩为一个明确的能量反权混合标定态的零均值漂移，并给出有限误差界。其系统—资源表达是每条非零转移振幅的二元能隙配平。

另一方面，将参考生成元与新增生成元的两个中心化方向作三维 Gram 提升，得到横向偏转的精确分解：能量流项加正 Gram 余量。有效二能级时余量为零；高维时即使能量分布和净平均功不变，也可改变原轨道。多米诺现象对应预存势能、触发阈值与耦合路径的共同作用；给出守恒的五级量子资源接力及有路径却完全相消的反例。最后接回共同正核、酉门、薛定谔方程、Born 读出、密度矩阵、张量积与仪器，明确能量守恒与实际控制供应各自的条件。

全部数学为解析证明，未执行数学程序、数值试验或候选枚举。

## 目录

- [1. 版本承接、源依据与本轮新增内容](#section-1)
- [2. 当前态加切向：精确有限式与 Hilbert 依赖](#section-2)
- [3. 持续同一个门，什么时候确实绕圆](#section-3)
- [4. 轨迹相交、相切与信息量](#section-4)
- [5. 能量在 Ω 中怎样定义](#section-5)
- [6. 唯一新候选：有限能量参照均值闭合](#section-6)
- [7. 同一候选的单标定态压缩与有限误差](#section-7)
- [8. 反向删除审计：为什么保留这些条件](#section-8)
- [9. 系统与资源的二元配平及三维提升](#section-9)
- [10. 借能量、借相干与资源归还](#section-10)
- [11. 轨道偏转的三维分解：能量流加正余量](#section-11)
- [12. 偏离原轨道需要多少相对作用](#section-12)
- [13. 多米诺：储备、阈值与耦合路径](#section-13)
- [14. 有连接路径，还要检查相位与实际控制](#section-14)
- [15. 接回现有量子公理的完整条件链](#section-15)
- [16. 一段完整白话与结论范围](#section-16)
- [来源与版本关系](#references)

<a id="section-1"></a>

## 1. 版本承接、源依据与本轮新增内容

本轮记为 v85，直接承接已交付 v84。可核验项目基线为

`c63ab162315fddd0801cbe9f47dbf3eda6e13360`。

两次有限的实时 HEAD 获取均失败，本轮不能认证该提交之后的差异。项目结论以下述固定原文及对话 v84 为依据。

| 来源 | 已有关系 | 本轮接续 |
| --- | --- | --- |
| 整体静态理论 | 正历史、内部参考、双随机重叠、原生菜单 | 区分工作轨迹、记录、控制与资源 |
| FIB 续卷 V | 投影型实际脉冲与 $K_j^{10}=I$ | 说明原生二谱门的有效圆轨道 |
| V74 | 水平几何、三维 Gram、生成元余块、相对时钟 | 精确偏转分解及轨道作用量界 |
| V78 综合稿 | 可微酉生成元、期望导数与自治守恒 | 把全输入守恒压到有限能量校准 |
| v84 | 正历史回返与有限锚刚性推出实际酉门 | 作为 $C_{85}$ 的酉执行背景 |

能量守恒与总 Hamiltonian 对易、能量匹配、相干资源和电池要求已有文献 [6](#ref-aberg)–[8](#ref-chiribella)。本轮新增的是项目接口：有限能量参照的均值闭合、其单标定态等价式，以及它与已有二元三维几何、轨道偏转和内部资源路径的组合。这不是文献优先权声明。

固定快照现存 16 份所查 Markdown 中未检得相同有限校准接口；该检索范围也不代表全仓库穷尽查重。

所有准备、参考、读口、时钟、控制和资源均放在 $\Omega$ 内部。有限载体是一个声明的执行切口，并不把整体 $\Omega$ 断言为有限维。持续增长的完整日志若纳入被比较对象，必须一起检查；不能用工作态回返代替完整日志回返。

**白话图景。**本轮把“要改变路线，内部究竟借了什么”变成可以逐项检查的问题。已有的量子表示继续使用；新增的是一条能量校准约束，以及它怎样约束门、资源和轨迹。

<a id="section-2"></a>

## 2. 当前态加切向：精确有限式与 Hilbert 依赖

约定内积第二变量线性，归一态 $a,b\in H$。若存在 $v\perp a$ 使 $b=a+v$，则

$$
1=\lVert b\rVert^2=\lVert a\rVert^2+\lVert v\rVert^2=1+\lVert v\rVert^2,
$$

故 $v=0$。非平凡有限更新必须补归一化或径向修正。

### 定理 2.1（二态圆弧分解）

设 $c=\langle a,b\rangle$，$\theta=\arccos|c|\in[0,\pi/2]$。当 $0<|c|<1$ 时，取相位 $\phi=\arg c$，令

$$
\widetilde b=e^{-i\phi}b,
\qquad
\eta=\frac{\widetilde b-\cos\theta\,a}{\sin\theta}.
$$

则 $\langle a,\eta\rangle=0$、$\lVert\eta\rVert=1$，且

$$
\boxed{\widetilde b=\cos\theta\,a+\sin\theta\,\eta.}
$$

曲线 $\gamma(s)=\cos s\,a+\sin s\,\eta$ 是水平单位大圆，其射线是 $a,b$ 之间的一条 Fubini–Study 最短测地线。这里距离约定为

$$
d_{\rm FS}([a],[b])=\arccos|\langle a,b\rangle|.
$$

**证明。**相位选择给 $\langle a,\widetilde b\rangle=|c|=\cos\theta$，正交性直接成立。展开范数得 $\lVert\widetilde b-\cos\theta a\rVert^2=1-\cos^2\theta=\sin^2\theta$。曲线归一且 $\langle\gamma,\dot\gamma\rangle=0$、$\lVert\dot\gamma\rVert=1$；它在复二维张成空间中的水平圆弧长度为 $\theta$，达到所声明的射影距离。

$\theta=0$ 时两者同射线，无须指定 $\eta$；$\theta=\pi/2$ 时可选任意相对相位的 $\widetilde b$，测地线不再唯一。若相对相位被内部参考实际读出，则 $e^{i\phi}$ 必须保留在完整内容中，不能当成未观察到的冗余。

当 $0<\theta<\pi/2$，还可写成

$$
w=\tan\theta\,\eta,
\qquad
\boxed{\widetilde b=\frac{a+w}{\sqrt{1+\lVert w\rVert^2}}.}
$$

$\theta=0$ 时直接取 $w=0$。微分式 $\gamma(s+ds)=\gamma(s)+\dot\gamma(s)ds+O(ds^2)$ 只是一阶表示；二阶径向修正确保态仍在单位球面。由端点确定的 $\eta$ 是测地初方向；一条实际历史即使连接相同端点，也不必以这个方向起步，更不必始终留在这一个二元复载体中。对水平速度 $v$，圆弧展开给

$$
\gamma(t)=a+tv-\tfrac12t^2\lVert v\rVert^2a+O(t^3).
$$

### 命题 2.2（局部二态分解不能单独建立共同 Hilbert 空间）

每个二元关系单独能作归一几何表示，不足以保证所有关系来自同一内积空间。

**证明。**取实对称关系表

$$
K=\begin{pmatrix}
1&-3/4&-3/4\\
-3/4&1&-3/4\\
-3/4&-3/4&1
\end{pmatrix}.
$$

每个二阶主块均正定，其行列式为 $1-9/16>0$；但对 ${\bf1}=(1,1,1)^{\mathsf T}$，

$$
{\bf1}^{\mathsf T}K{\bf1}=3-18/4=-3/2<0.
$$

故它不可能是任何三个共同 Hilbert 向量的 Gram 矩阵。

本轮使用此前共同复正核及其所有有限 Gram 正性，以免把单对表示误充为整体相容证明。实内积空间也允许正交分解；仅从这幅图景不能排除实关系模型。

**白话图景。**你的“当前态加一个朝向目标的方向”可以保留，精确写法是先把两个正交方向配上余弦与正弦，再保持总长度为一。局部这一步有画面，但整个理论还要求不同局部图景能拼在同一张关系表里。

<a id="section-3"></a>

## 3. 持续同一个门，什么时候确实绕圆

一个离散门 $U$ 只指定一次端点作用。要谈持续工作，必须指定实际连续脉冲或生成元；同一个有限 $U$ 有不同矩阵对数，不能自行选一个插值冒充实际轨迹。项目 V74 已明确采样与生成元的区别 [3](#ref-v74)。

### 定理 3.1（固定生成元的有效谱载体）

设 $H=H^\dagger$ 有限维，

$$
\psi(t)=e^{-itH/\hbar}\psi_0,
\qquad
H=\sum_{\lambda}\lambda P_\lambda.
$$

令 $m$ 为 $P_\lambda\psi_0\ne0$ 的不同本征值数。全部 $\psi(t)$ 的复线性张成空间维数恰为 $m$。故轨道落在某个至多二维复载体的射影空间内，当且仅当 $m\le2$；$m=1$ 给固定射线。

**证明。**轨迹显然落在 $\Span_\C\{P_\lambda\psi_0\}$，非零谱分量彼此正交。反过来，轨迹张成空间在有限维下闭合，包含其各阶导数，从而包含 $H^k\psi_0$。对 $k=0,\ldots,m-1$，不同 $\lambda$ 的 Vandermonde 矩阵可逆，故每个 $P_\lambda\psi_0$ 都属于该张成空间。

当 $m=2$，写

$$
\psi(t)=\sqrt p\,e^{-iE_1t/\hbar}u+
\sqrt{1-p}\,e^{-iE_2t/\hbar}v,
\qquad u\perp v.
$$

去掉共同相位后，它的有效 Bloch 向量为

$$
r(t)=\bigl(2\sqrt{p(1-p)}\cos\vartheta(t),\;
2\sqrt{p(1-p)}\sin\vartheta(t),\;2p-1\bigr),
$$

其中 $\vartheta(t)$ 按能隙匀速变化。$0<p<1$ 时为纬圆，周期 $2\pi\hbar/|E_2-E_1|$；$p=1/2$ 时是大圆，端点 $p=0,1$ 是固定射线。这是射线／有效 Bloch 圆的陈述；保留所有绝对相位的 Hilbert 向量曲线不能不加说明地视为同一个圆。

项目的实际投影型脉冲

$$
U_j(t)=e^{i\alpha t}\bigl[I+(e^{i\alpha t}-1)P_j\bigr],
\qquad \alpha=3\pi/5,\quad 0\le t\le1
$$

只有两个谱扇区。任一固定输入只占据这两个扇区各一个向量，所以其有效 Bloch 轨道正是上述圆或固定点 [2](#ref-fib)。整圆由相同完整正脉冲的重复及其连续轨迹给出。原生菜单只供应完整单位脉冲，式中的中间参数不自动授权分数停止、读出或负时间调用。

### 命题 3.2（固定门流未必是圆或具有精确周期）

取 $H=\hbar\omega\,\operatorname{diag}(0,1,\sqrt2)$、$\omega>0$，以及 $\psi_0=(1,1,1)^{\mathsf T}/\sqrt3$。其射影轨道没有正的精确回返周期，也不处在复射影直线中。

**证明。**三个有效谱分量给三维复张成空间。若正时间 $T$ 回到同射线，第一分量固定迫共同相位为 1，从而 $\omega T=2\pi n$、$\sqrt2\,\omega T=2\pi m$，与 $\sqrt2$ 无理及 $T>0$ 矛盾。

**白话图景。**项目这类投影型基础门确实只转动两个有效分量，所以能看到圆。更多频率一起变化，会形成更复杂的路线。“同一个门一直工作”和“只有一个相对转动频率”需要分别声明。

<a id="section-4"></a>

## 4. 轨迹相交、相切与信息量

### 定理 4.1（完整自治轨道的交叉约束）

设完整状态流满足局部 Lipschitz 自治方程 $\dot x=X(x)$，并在所讨论区间有唯一解。若两条解在时刻 $t_1,t_2$ 达到同一完整状态，则在共同存在区间内，它们只是同一轨道的时间平移，不能在该完整状态横截相交后走向不同未来。

**证明。**把两条曲线分别平移到交点时刻零，它们满足同一方程及同一初值；初值唯一性使两条解重合。

不同生成元、不同内部控制标签，或遗漏时钟与记忆的约化读出，不满足这个“同一完整方程同一完整状态”的前提。两条不同控制轨迹可以相交，也可相切后分开；一个态及瞬时切向不能确定全部未来控制。V74 的完整生成元表达还包含未被当前切向确定的余空间作用 [3](#ref-v74)。

例如对正交归一的 $a,b,c$，两条归一曲线

$$
\psi_1(t)=\cos t\,a+\sin t\,b,
\qquad
\psi_2(t)=\frac{\cos t\,a+\sin t\,b+t^2c}{\sqrt{1+t^4}}
$$

在零时刻同为 $a$，切向同为 $b$，二阶导数却分别是 $-a$ 与 $-a+2c$。它们相切后分开，分别可由 V74 的曲线生成元构造实现，但不是同一完整自治向量场的两条不同解。

### 命题 4.2（同一量子轨迹的二维读出可以横截相交）

取

$$
\psi(t)=\frac1{\sqrt3}(1,e^{-it},e^{-2it})^{\mathsf T},
$$

$$
A=\frac{3i}{2}(\ket0\bra1-\ket1\bra0),
\qquad
B=\frac{3i}{2}(\ket0\bra2-\ket2\bra0).
$$

则 $(\langle\psi,A\psi\rangle,\langle\psi,B\psi\rangle)=(\sin t,\sin2t)$。$t=0,\pi$ 均读出 $(0,0)$，切向为 $(1,2)$、$(-1,2)$，彼此横截；完整态却分别为 $(1,1,1)/\sqrt3$ 与 $(1,-1,1)/\sqrt3$。

**证明。**代入两个矩阵直接展开期望；两切向行列式为 $4$，故不共线。两完整态不成比例，不能视为同一射线。

轨迹的形状、长度和门数也不单独定义信息量。共同酉门保持 $\langle U\psi,U\phi\rangle=\langle\psi,\phi\rangle$，因而不会仅凭把路径变复杂就增加这些输入间的可区分关系。一段闭合门词可以增加完整日志，却不改变工作端点。若要量化路径信息，须声明可读记录、先验集合和允许的读出；同一几何路径以不同速度走过，也会有不同的内部时钟关系。

**白话图景。**图上的交叉，可能只是两个不同的完整内容被读成了同一个位置。把控制器、时钟和记录补回去，未来为何不同就有了内部来源。路线绕得更复杂，记录可能更多，但工作态本身的信息并不会自动按路长增加。

<a id="section-5"></a>

## 5. 能量在 Ω 中怎样定义

### 定义 5.1（内部能量接口）

一个有限能量接口包含：按不同能量值分组的一组完整谱投影 $\Pi_\lambda$，满足

$$
\Pi_\lambda\Pi_\mu=\delta_{\lambda\mu}\Pi_\lambda,
\qquad \sum_\lambda\Pi_\lambda=I,
$$

标定实值 $g_\lambda$，以及与内部时钟相容的自伴读口

$$
G=\sum_\lambda g_\lambda\Pi_\lambda.
$$

对态 $\rho$，一次读出为某个 $g_\lambda$，其分布为 $\operatorname{tr}(\rho\Pi_\lambda)$，均值为 $\operatorname{tr}(\rho G)$。若 $G$ 被称为物理能量，还须与所声明内部时间平移 $T(t)=e^{-itG/\hbar}$ 的生成元标定相容。

能量算子、一次读数、平均值与方差是不同类型的内部对象。把概念内生化，意味着同时保留其测量程序与相容关系，而不是把整个读出规则压成某一次读数。

### 命题 5.2（独立内部时钟的组合给出加性生成元）

若 $T_S(t)=e^{-itH_S/\hbar}$、$T_R(t)=e^{-itH_R/\hbar}$ 在同一内部参数下独立组合为 $T_S(t)\otimes T_R(t)$，其生成元为

$$
\boxed{G=H_S\otimes I+I\otimes H_R.}
$$

**证明。**在 $t=0$ 对张量积使用乘积求导，再乘 $i\hbar$。

这里 $S$ 是工作部分，$R$ 可以包含储能、相位参考、控制器及开关。两者都在 $\Omega$ 内部。

待测完整操作 $U$ 与 $G$ 必须分别固定。若事后为每个 $U$ 单独选取 $\log U$ 当能量，$[U,G]=0$ 会成为定义恒等式，失去约束作用。加性预算适用于已声明的非相互作用比较端点或明确的相容耦合模型。若有未消失的相互作用 $V_{\rm int}$，总账必须包含它；一般只有

$$
\Delta\langle H_S\rangle+\Delta\langle H_R\rangle+\Delta\langle V_{\rm int}\rangle=0
$$

这一类完整预算，不能省略相互作用项。

静态来源的内部移动参考仍沿用 V74：

$$
\psi=R(t)^\dagger\Omega,
\qquad
H_{\rm rel}=-i\hbar R^\dagger\dot R,
$$

其中 $\Omega$ 在此式中特指该载体上的固定归一向量表示，$R(t)$ 为可微酉参考。时钟重标会重标生成元；$\hbar$ 的数值和能量单位不能从归一化独自算出。

**白话图景。**能量可以完全属于 $\Omega$：读数、读数的刻度、时钟和操作设备都在里面。但“这个数叫能量”还必须与时间变化怎样生成相容。要问借了什么，就要把系统、储备、控制和相互作用放进同一份内部预算。

<a id="section-6"></a>

## 6. 唯一新候选：有限能量参照均值闭合

沿用 v84 已重建的有限酉完整操作 $U\in U(\mathcal H)$，$N=\dim_\C\mathcal H<\infty$。先固定同一个自伴能量读口 $G$，取完整本征参考框

$$
G\ket k=g_k\ket k,
\qquad k=1,\ldots,N.
$$

允许简并；完整框包含简并空间中的全部基方向。

### 定义 6.1（候选 $C_{85}$）

对被声明为相对于 $G$ 封闭的完整操作，只要求有限组本征参照的输出均值闭合：

$$
\boxed{m_k:=\langle Uk,GUk\rangle=g_k,\qquad k=1,\ldots,N.}
\tag{$C_{85}$}
$$

不预先要求所有叠加态守恒，也不预先要求输出落在同一能量块。“封闭”在这里由本条件及已声明的完整载体约束，不能预先把结论写进定义。

### 定理 6.2（有限均值闭合迫使全部能量分布守恒）

在上述背景下，下列条件等价：

1. $C_{85}$；
2. $[G,U]=0$；
3. 对所有谱投影 $\Pi_\lambda$，有 $U\Pi_\lambda=\Pi_\lambda U$；
4. 对全部输入态 $\rho$，能量读出分布保持；
5. $U$ 与同一内部时间平移 $e^{-itG/\hbar}$ 对所有 $t$ 对易。

**证明。**令 $P_{jk}=|\langle j,Uk\rangle|^2$。酉性给列和与行和都为 1，故 $P$ 双随机，并且

$$
m_k=\sum_jg_jP_{jk}.
$$

定义能隙平方量

$$
D_G(U)=\sum_{j,k}(g_j-g_k)^2P_{jk}.
$$

展开并利用两种归一化，

$$
\begin{aligned}
D_G(U)
&=\sum_jg_j^2+\sum_kg_k^2-2\sum_kg_km_k\\
&=2\sum_kg_k(g_k-m_k)\\
&=\lVert[G,U]\rVert_{\rm HS}^2.
\end{aligned}
$$

候选使右边为零，而左边每项非负。因此

$$
\boxed{(g_j-g_k)\langle j,Uk\rangle=0\quad\text{对每一对 }j,k.}
$$

这就是 $[G,U]=0$，它强制 $U$ 保持全部能量块。

谱投影是有限谱上 $G$ 的多项式，故条件 2 与 3 等价。条件 3 给

$$
\operatorname{tr}(U\rho U^\dagger\Pi_\lambda)=\operatorname{tr}(\rho\Pi_\lambda),
$$

即 4；由全部分布保持可回取各本征态均值。条件 2 给指数对易；条件 5 在零处求导给条件 2。

这个证明的局部内容是非零振幅连接的两端能量必须相等；全局内容是共同的有限完整参考框及酉性把全部局部项同时锁住。它没有预先假设概率振幅矩阵对称，也没有要求每一对正反转移的概率相等。

由于 $\sum_k(m_k-g_k)=0$，任意 $N-1$ 个精确均值条件已经迫使最后一个；完整参考框是共同关系载体，不意味着每一条测试等式都逻辑独立。

### 推论 6.3（更大的允许结构）

令 $n_\lambda=\operatorname{rank}\Pi_\lambda$。能量闭合完整酉门恰组成

$$
\boxed{\{U:[U,G]=0\}\cong\prod_\lambda U(n_\lambda).}
$$

**证明。**与全部谱投影对易等价于按能量块分块对角，每个块独立酉。

因此同一总能量块内部仍可有非平凡变化。非简并时此群仍有多个独立相位，通常大于一条 $\{e^{-itG/\hbar}:t\in\mathbb R\}$ 轨道。守恒不会自动把全部合法门限制成同一个圆。

**白话图景。**每个确定能量的参照，操作后只要求平均读数回来，看起来允许向上和向下的变化互相抵消。但完整酉门还保留全部输入与输出方向的总量。把所有参照一起比较，这些隐藏的能量跨越会形成一串非负平方；总和必须为零，于是每一项都只能为零。最终不只是均值回来，整份能量分布都被保住。

<a id="section-7"></a>

## 7. 同一候选的单标定态压缩与有限误差

### 定理 7.1（一个明确混合标定态已足够）

固定 $\Lambda>g_{\max}$，令

$$
Z=N\Lambda-\operatorname{tr}G>0,
\qquad
\tau_G=\frac{\Lambda I-G}{Z}.
$$

这是满秩归一态。在既有酉背景下，

$$
\boxed{
\operatorname{tr}\bigl[G(U\tau_GU^\dagger-\tau_G)\bigr]
=\frac{\lVert[G,U]\rVert_{\rm HS}^2}{2Z}\ge0.
}
$$

因此这个特定内部标定态的零均值漂移，与 $C_{85}$ 完全等价。

**证明。**$\tau_G$ 在能量基中的权重为 $(\Lambda-g_k)/Z$。由于 $\sum_km_k=\sum_kg_k$，其均值变化为

$$
\frac1Z\sum_k(\Lambda-g_k)(m_k-g_k)
=-\frac1Z\sum_kg_k(m_k-g_k)
=\frac{D_G(U)}{2Z}.
$$

这只是同一候选的等价压缩，不另立新公理。标定态的准备与概率混合使用已声明的内部准备接口。它不能被任意混合态替换；尤其 $I/N$ 被每个酉门固定，对能量跨越没有区分力。有限统计样本只能给有置信水平的近似证据，不能被直接写成精确等式。

### 命题 7.2（有限误差的能隙平方界）

令 $\delta_k=m_k-g_k$，$W=g_{\max}-g_{\min}$。若 $|\delta_k|\le\varepsilon$，则

$$
\boxed{D_G(U)\le NW\varepsilon,
\qquad \lVert[G,U]\rVert_{\rm op}\le\sqrt{NW\varepsilon}.}
$$

若存在不同能量，令 $\gamma=\min_{g_j\ne g_k}|g_j-g_k|>0$，则

$$
\frac1N\sum_{g_j\ne g_k}P_{jk}
\le\frac{W\varepsilon}{\gamma^2}.
$$

若单标定态的实际均值漂移不超过 $\epsilon_\tau$，则 $D_G(U)\le2Z\epsilon_\tau$。

**证明。**$\sum_k\delta_k=0$。取 $c=(g_{\max}+g_{\min})/2$，有

$$
D_G(U)=-2\sum_k(g_k-c)\delta_k
\le2\sum_k|g_k-c|\,|\delta_k|\le NW\varepsilon.
$$

算子范数不超过 HS 范数；每个跨能量项至少贡献 $\gamma^2P_{jk}$。单标定态结论用上一恒等式。

当 $W=0$ 时 $G$ 为标量，本来就与全部门对易，不定义不存在的最小非零能隙。这些界不要求把能量原点固定在零，整体平移不影响结论。

**白话图景。**一组能量参照还可以混成一个专门的标定态：低能量方向多放一点，高能量方向少放一点。任何跨能量的酉混合都会使它的平均读数向上漂移。因此，这一个经过明确定义的读出比较，就能检查整份能量配平。它之所以有效，是因为准备权重已与同一个能量读口对应好。

<a id="section-8"></a>

## 8. 反向删除审计：为什么保留这些条件

### 命题 8.1（单一任意输入的均值不够）

取 $G=\operatorname{diag}(-1,0,1)$。可选酉门把中间本征态映到两端等幅叠加；该输入均值保持为零，能量分布却从确定值变成两端分布。

**证明。**两端等幅叠加与中间态均归一，映射可补齐成酉。输出均值为 $(-1+1)/2=0$，输出方差为 $1$，而原方差为零。这个类型的已知反例亦见 [6, Appendix A.2](#ref-aberg)。

### 命题 8.2（失去酉性及双随机保障，全部锚均值也可能不够）

令 $G=\operatorname{diag}(0,1,2)$，取 Kraus 算子

$$
A_1=\ket0\bra0,\quad
A_2=\ket0\bra1/\sqrt2,\quad
A_3=\ket2\bra1/\sqrt2,\quad
A_4=\ket2\bra2.
$$

它们给保持迹的完全正通道，全部能量本征锚的均值都保持，但中间锐能量变成两端混合。

**证明。**$\sum_\alpha A_\alpha^\dagger A_\alpha=I$。中间输入输出 $\tfrac12(\ket0\bra0+\ket2\bra2)$，均值 1 保持，方差由零变成 1；两端输入保持。该转移矩阵仅列随机，不是双随机，所以主证明所需的行和恒等式缺失。

同一能隙平方论证可扩展到双随机通道并约束其 Kraus 能量块，但这种通道仍可能退相干；那不是本轮完整酉门的替代重建。

| 删除或偷换的条件 | 后果 |
| --- | --- |
| 完整参照覆盖 | 只检查一个子空间时，可在未检验的两个不同能量方向上交换。 |
| 指定反权标定态 | 最大混合态对任意酉都不变，无法认证能量守恒。 |
| 独立固定的 $G$ | 每次为 $U$ 另选一个对数当 $G$，对易变成自选定义。 |
| 完整资源与相互作用 | 系统吸收的能量可能来自被删去部分；约化均值变化不能判定整体创造能量。 |
| 能量与内部时钟标定 | 同样论证只证明某个自伴量守恒，尚不能识别它是物理能量。 |
| 原生控制供应 | 能隙匹配只给允许条件，不保证相应门可以实际调用。 |
| 有限谱与共同定义域 | 无界无限体系不能直接使用上述有限迹及完整有限参考证明。 |

**白话图景。**反推不是给每条条件贴上“显然必要”的标签，而是指出删掉后哪个关系会漏掉。不看完整参照会漏方向，不保留完整资源会漏能量来源，不固定读口会让守恒变成自我命名。每一项都有具体任务。

<a id="section-9"></a>

## 9. 系统与资源的二元配平及三维提升

取前后读口相容的

$$
G=H_S\otimes I+I\otimes H_R,
\qquad H_S\ket i=E_i\ket i,
\qquad H_R\ket a=\epsilon_a\ket a.
$$

由 $C_{85}$，

$$
\boxed{
\langle j,b|U|i,a\rangle\ne0
\ \Longrightarrow\ 
(E_j-E_i)+(\epsilon_b-\epsilon_a)=0.
}
$$

这把“借了什么”落实到一条非零二元转移上。对任意初始联合态（不要求无关联），加性总能量守恒还给

$$
\Delta\langle H_S\rangle=-\Delta\langle H_R\rangle.
$$

如果总账有相互作用，则应使用包含该项的完整版本。

### 定理 9.1（一对匹配端点的有限三维关系）

设 $x=\ket{i,a}$、$y=\ket{j,b}$ 正交，且具有相同总能量。对

$$
\Psi=\alpha x+\beta y,
\qquad |\alpha|^2+|\beta|^2=1,
$$

定义

$$
r_1=2\operatorname{Re}(\overline\alpha\beta),
\qquad r_2=2\operatorname{Im}(\overline\alpha\beta),
\qquad r_3=|\alpha|^2-|\beta|^2.
$$

则 $r_1^2+r_2^2+r_3^2=1$。在这个共同能量块内，令

$$
K=g(\ket x\bra y+\ket y\bra x),
\qquad g\in\mathbb R,
$$

则 $[K,G]=0$，且

$$
e^{-itK/\hbar}x
=\cos(gt/\hbar)x-i\sin(gt/\hbar)y.
$$

系统平均能量变化为

$$
\Delta\langle H_S\rangle
=(E_j-E_i)\sin^2(gt/\hbar),
$$

资源端给精确相反量。

**证明。**平方恒等式用 $(|\alpha|^2+|\beta|^2)^2=1$。$G$ 在该二态块上为同一标量，故与 $K$ 对易；$K^2=g^2I$ 在该块上成立，指数级数给正弦余弦式。部分能量期望由两条正交联合分量的权重求出。

这是整体相同能量中的内部重分配。能隙匹配使该耦合相容，但其原生可实现性及控制时长仍需供应。若 $E_j\ne E_i$，资源两端也有不同能量；忽略资源时，系统可能成为混合态，不能把联合相干直接说成系统独立纯态相干。

**白话图景。**工作部分向上走一格，资源部分向下走对应的一格；两者合起来仍在同一个总能量层上。这个局部二元交换可以画成一个三维球上的圆。整体没有凭空多出能量，改变的是内部哪一部分承载了它，以及相干关系放在哪里。

<a id="section-10"></a>

## 10. 借能量、借相干与资源归还

### 定理 10.1（静止资源只给时间协变的约化通道）

若 $[U,H_S+H_R]=0$、$[\sigma_R,H_R]=0$，定义

$$
\Phi(\rho)=\operatorname{tr}_R[U(\rho\otimes\sigma_R)U^\dagger].
$$

则

$$
\boxed{\Phi(T_S(t)\rho T_S(t)^\dagger)
=T_S(t)\Phi(\rho)T_S(t)^\dagger.}
$$

因此从 $[\rho,H_S]=0$ 出发，不能产生跨不同系统能量块的相干。

**证明。**$\sigma_R=T_R(t)\sigma_RT_R(t)^\dagger$。将 $T_S(t)\otimes T_R(t)$ 移过 $U$，再用部分迹资源酉共轭不变，即得协变式。输入时间不变时输出也时间不变；有限维中这等价于与 $H_S$ 对易。

这与已有相干资源理论一致 [7](#ref-lostaglio)。高平均能量和合适相干性是不同的资源坐标；一个很高但锐利的资源能级，不自动供应跨能级相干控制。

### 命题 10.2（零净能量交换仍可使用相干资源）

令系统与资源为同能隙 $\Delta>0$ 的量子比特，

$$
G=\Delta(\ket1\bra1\otimes I+I\otimes\ket1\bra1).
$$

SWAP 与 $G$ 对易。初态

$$
\rho_S=I/2,
\qquad
\rho_R=\ket+\bra+,
\qquad
\ket+=(\ket0+\ket1)/\sqrt2
$$

经过 SWAP 后交换。系统取得跨能级相干和纯度，资源失去它们；两边各自的初末平均能量都为 $\Delta/2$，初末能量分布也各自相同。

**证明。**相同局部 Hamiltonian 的和在交换下不变。两输入态在能量基中的对角元均为 $(1/2,1/2)$，但只有 $\ket+\bra+$ 含非零非对角元。

### 命题 10.3（全输入精确酉门的零平均归还边界）

设完整 $U$ 守恒加性 $G=H_S+H_R$，资源初态固定。若对每个系统输入 $\rho$，系统输出精确为 $W\rho W^\dagger$，且资源末态的平均能量等于初态，则

$$
\boxed{[W,H_S]=0.}
$$

**证明。**总均值守恒和资源均值归还给

$$
\operatorname{tr}[\rho(W^\dagger H_SW-H_S)]=0
$$

对所有 $\rho$ 成立。自伴算子的全态二次型为零迫该算子为零，即得结论。

这里不要求资源末态没有关联；加性期望预算已经足够。条件只涉及当前声明的全输入精确实现。已知单个输入、近似实现，或不再要求资源平均能量归还的实现，需要另作分析。资源末态可以改变或形成关联，只要其平均能量归还，本定理仍适用；改变控制菜单本身也不撤销相同假设下的结论。

更强的有限资源实现限制已有文献 [8](#ref-chiribella)：一般跨能级目标门的高精度全输入实现需要足够的初始电池资源。这种容量／相干要求不能直接改写成每个门都耗散固定能量；合适构造可以在连续门之间回收资源。

**白话图景。**“借”不只是一块电池的平均电量，也可能是它提供了相位参考和合适的能量分布。如果要求对所有未知输入都精确完成任意跨能级门，同时资源平均值每次完全归还，这些要求会相互冲突。对某个已知态做一次变化、用近似控制完成任务，是另一种明确范围。

<a id="section-11"></a>

## 11. 轨道偏转的三维分解：能量流加正余量

本节给本轮的几何核心，承接 V74 的二元 Gram 几何。这里比较完整纯态载体；若局部系统与资源纠缠，应使用联合纯态，或另行声明混合态几何，不能把约化混合态直接套入本节纯态公式。

固定自伴参考 $H_0$，实际演化为

$$
i\hbar\dot\psi=(H_0+V(t))\psi,
$$

其中 $\psi$ 为归一 $C^1$ 曲线，$V(t)=V(t)^\dagger$ 连续。在同一时刻定义

$$
\begin{gathered}
u=(H_0-\langle H_0\rangle)\psi,
\qquad
v=(V-\langle V\rangle)\psi,\\
h=\lVert u\rVert^2=(\Delta H_0)^2,
\qquad
k=\lVert v\rVert^2=(\Delta V)^2,\\
c=\operatorname{Re}\langle u,v\rangle,
\qquad
w=\operatorname{Im}\langle u,v\rangle,
\qquad
D=hk-|\langle u,v\rangle|^2\ge0.
\end{gathered}
$$

参考水平切向和新增水平切向为

$$
\xi_0=-iu/\hbar,
\qquad
\delta\xi=-iv/\hbar.
$$

沿用 $g=2\hbar\operatorname{Re}\langle\cdot,\cdot\rangle$、$\omega=2\hbar\operatorname{Im}\langle\cdot,\cdot\rangle$ 的 V74 物理尺度。

### 定理 11.1（横向偏转恒等式）

当 $h>0$，相对于参考实切线的横向新增分量

$$
\delta\xi_\perp
=\delta\xi-\frac{c}{h}\xi_0
$$

满足

$$
\boxed{
\hbar^2\lVert\delta\xi_\perp\rVert^2
=k-\frac{c^2}{h}
=\frac{w^2+D}{h}.
}
$$

参考能量电流

$$
 j_0=\frac{d}{dt}\langle H_0\rangle
=\frac{i}{\hbar}\langle[V,H_0]\rangle
=\frac{2w}{\hbar}
$$

因而给

$$
\boxed{
\lVert\delta\xi_\perp\rVert^2
=\frac{j_0^2}{4(\Delta H_0)^2}
+\frac{D}{\hbar^2(\Delta H_0)^2}.
}
$$

并有

$$
\frac{|j_0|}{2\Delta H_0}
\le\lVert\delta\xi_\perp\rVert
\le\frac{\Delta V}{\hbar}.
$$

**证明。**实内积投影公式给 $\lVert\delta\xi_\perp\rVert^2=\hbar^{-2}(k-c^2/h)$。由 $D=hk-c^2-w^2$ 得第二式。期望求导给 $j_0=(i/\hbar)\langle[V,H_0]\rangle$，而 $\langle[H_0,V]\rangle=2iw$，所以 $j_0=2w/\hbar$。非负 $D$ 给下界；正交投影不增范数给上界。

若 $h=0$，参考射线瞬时静止；此时直接用 $\lVert\delta\xi\rVert=\Delta V/\hbar$，不除以零。

当 $hk>0$，定义

$$
(r_1,r_2,r_3)=\frac{(c,w,\sqrt D)}{\sqrt{hk}},
\qquad r_1^2+r_2^2+r_3^2=1,
\qquad r_3\ge0.
$$

则

$$
\lVert\delta\xi_\perp\rVert
=\frac{\Delta V}{\hbar}\sqrt{r_2^2+r_3^2},
\qquad
j_0=\frac{2\Delta H_0\Delta V}{\hbar}r_2.
$$

$r_1$ 记录顺切关系；$r_2$ 记录能量流／有向关系；$r_3$ 记录超出同一复直线的正余量。在 V74 尺度下还恰有

$$
j_0=\omega(\xi_0,\delta\xi)=\omega(\xi_0,\xi_0+\delta\xi).$$

### 推论 11.2（用户直觉成立的二能级范围）

若两个中心化方向位于同一复直线，特别是它们都属于同一个闭合复二维载体的水平切空间，则 $D=0$。在 $\Delta H_0>0$ 时，

$$
\delta\xi_\perp\ne0\quad\Longleftrightarrow\quad j_0\ne0.
$$

**证明。**复线性相关给 Gram 行列式为零，再用恒等式。

这只涉及瞬时横向偏转；顺着原轨道改变速度或反向走，不在横向项中。有限时间是否离开整条原轨道集合，下一节再给精确界。

### 命题 11.3（高维零净平均功仍可改变原轨道）

取

$$
H_0=E\,\operatorname{diag}(-1,0,1),
\qquad
V=\lambda\,\operatorname{diag}(1,-2,1),
\qquad
\psi_0=(1,1,1)^{\mathsf T}/\sqrt3,
$$

其中 $E\lambda\ne0$。令 $H(t)=H_0+f(t)V$，$f$ 为首尾归零的光滑非零实脉冲。则沿全程

$$
\langle H_0\rangle=\langle V\rangle=0,
\qquad
\operatorname{Cov}(H_0,V)=0,
\qquad
[H_0,V]=0.
$$

系统 $H_0$ 的全部能量分布不变，平均功率 $\langle\dot H(t)\rangle=f'(t)\langle V\rangle=0$，但 $f(t)\ne0$ 时新增切向完全横向，大小为

$$
\lVert\delta\xi_\perp(t)\rVert
=\frac{\sqrt2\,|\lambda f(t)|}{\hbar}.
$$

**证明。**对角演化保持三个能级人口均为 $1/3$。直接求和给两个均值与协方差为零；$V$ 的方差为 $2\lambda^2$。$f(t)\ne0$ 时参考与新增方向非零且实正交，所以横向分量等于新增方向；$f(t)=0$ 时两边均为零。

若需要非负能谱，可给参考及完整 Hamiltonian 加足够大常数，不改变以上射影结论。这个给定输入、给定控制模型的零净平均功反例不声称控制器在任何硬件中都无成本；它证明的是“偏离旧轨迹必然增加平均能量或耗散正功”并不普遍成立。

**白话图景。**在最简单的二能级图景里，离开原来的能量圆需要能量流，你的直觉在这里有严格形式。更高维多出第三个关系余量：系统可以保持所有能量人口不变，只重新安排多个相位的相对速度，便离开原来的那条路。偏转需要横向生成作用；这种作用不必等于正的平均能量消耗。

<a id="section-12"></a>

## 12. 偏离原轨道需要多少相对作用

### 定理 12.1（相对参考轨迹的有限时间界）

设参考与实际演化同初态，参考由 $H_0(t)$ 生成，实际由 $H_0(t)+V(t)$ 生成。有限维自伴连续条件下，

$$
\boxed{
\hbar\,d_{\rm FS}([\psi(T)],[\psi_{\rm ref}(T)])
\le\int_0^T\Delta_{\psi(t)}V(t)\,dt
\le\frac12\int_0^T\operatorname{diam}\operatorname{Spec}V(t)\,dt.
}
$$

**证明。**令参考传播为 $U_0(t)$，交互绘景态 $\eta(t)=U_0(t)^\dagger\psi(t)$。它由 $V_I=U_0^\dagger VU_0$ 生成，方差等于实际态上的 $\Delta V$。Fubini–Study 速度为 $\Delta V/\hbar$，路径长控制端点距离；共同酉变换不改端点距离。若谱位于 $[a,b]$，对中心 $c=(a+b)/2$，$\operatorname{Var}(V)\le\langle(V-cI)^2\rangle\le(b-a)^2/4$。

### 定理 12.2（扣除顺切改速后的轨道偏离界）

固定 $H_0$，假设区间内 $\Delta H_0>0$。令

$$
a(t)=1+\frac{\operatorname{Cov}_\psi(H_0,V)}{(\Delta_\psi H_0)^2},
\qquad
\tau(T)=\int_0^T a(t)\,dt.
$$

则

$$
\boxed{
 d_{\rm FS}\bigl([\psi(T)],[e^{-iH_0\tau(T)/\hbar}\psi(0)]\bigr)
\le\int_0^T\lVert\delta\xi_\perp(t)\rVert\,dt.
}
$$

若横向项处处为零，实际射线只沿原轨道重标时钟。若另有 $a(t)>0$，该重标保留原先方向。

**证明。**以 $a(t)H_0$ 作参考，剩余生成元为 $W(t)=V(t)+(1-a(t))H_0$。其中心化作用是 $v-(c/h)u$，方差恰为 $\hbar^2\lVert\delta\xi_\perp\rVert^2$。应用上一有限时间界。横向积分为零时端点距离对每一时刻均为零。

在横向项处处为零时，即使 $a$ 可负，结论仍是同一轨道上的参数变化，但可能反向。该定理说明真正离开原轨道需要非零横向作用积分；它不把轨道上的普通改速也算成新的几何方向。这里的 $a(t)$ 是针对给定历史构造的比较时钟，不自动供应能对未知输入原生调用的反馈控制。

**白话图景。**把顺着旧路线加速或减速的部分先扣掉，剩下的才是真正的转向。偏离得越远，就需要越多这样的横向作用积累。这比说“必须多花一份能量”更精确：它度量生成元怎样改变关系，也保留了内部时钟。

<a id="section-13"></a>

## 13. 多米诺：储备、阈值与耦合路径

面积标签 $1,2,3,4,5$ 本身不足以确定真实骨牌能否接力。质量、厚高比、间距、转轴、接触几何及碰撞损失都影响结果。真实多米诺放大模型须同时处理翻倒与碰撞；仅用一个总守恒式不足以确定动力学 [9](#ref-domino)。

### 命题 13.1（单块骨牌的触发势垒与可释放储备）

理想刚性矩形骨牌高 $h$、厚 $b$、质量 $m$，绕底部边缘翻转，不滑动。在均匀重力下，从直立到重心经过转轴上方的势垒为

$$
B=\frac{mg}{2}\bigl(\sqrt{h^2+b^2}-h\bigr).
$$

若最终平放且 $h>b$，直立到平放释放势能

$$
R=\frac{mg}{2}(h-b)>0.
$$

**证明。**重心到转轴的距离为 $\sqrt{h^2+b^2}/2$，直立与平放重心高度分别为 $h/2,b/2$；分别取重力势能差即得。

后续骨牌已经被放到有势能的直立状态。第一块主要触发释放；最终能量不全来自第一推。若把地球与支撑也纳入 $\Omega$，此描述仍完全内生。

### 定义 13.2（明确的阈值接力模型）

第 $j$ 个待触发单元具有势垒 $B_j\ge0$、储备 $R_j\ge0$。入射可用量 $x_j\ge0$ 达到 $B_j$ 才允许开启；开启后输出

$$
x_{j+1}=x_j+R_j-d_j,
\qquad 0\le d_j\le x_j+R_j.
$$

阈值是触发所需水平，$d_j$ 记录不能回收的损失。这是一项声明的粗粒化模型，不替代真实碰撞方程。

### 定理 13.3（接力不创造能量）

若每步触发条件成立，连续执行到 $n$ 后，

$$
\boxed{x_{n+1}+\sum_{j=2}^n d_j=x_2+\sum_{j=2}^n R_j.}
$$

取能量单位 $\Delta>0$，令 $x_2=\Delta$、$B_j=(j-1)\Delta$、$R_j=\Delta$、$d_j=0$，$j=2,\ldots,5$。则四个中间触发依次成功，而相同种子直接触发第五个单元失败。

**证明。**递推式逐项相加得到预算。该实例归纳给 $x_j=(j-1)\Delta$，等于每步阈值；直接输入第五单元仍只有 $\Delta<4\Delta=B_5$。

### 定理 13.4（五级守恒量子资源接力）

信号载体 $P$ 有态 $\ket1,\ldots,\ket5$，

$$
H_P=\sum_{j=1}^5j\Delta\ket j\bra j.
$$

四个资源位 $R_j$ 各有能量 $\Delta$ 的 $\ket1$ 与能量零的 $\ket0$。原生 $V_j$ 交换

$$
\ket j_P\ket1_{R_j}
\longleftrightarrow
\ket{j+1}_P\ket0_{R_j},
$$

在其余局部基态上恒等，并对其他资源位作用为恒等。则每个 $V_j$ 酉且守恒总加性能量，并有

$$
\boxed{\ket1\ket{1111}
\xrightarrow{V_1,V_2,V_3,V_4}
\ket5\ket{0000}.}
$$

**证明。**每个交换对两端能量都等于 $(j+1)\Delta$，所以交换与总能量对易。交换矩阵酉；四次按次序应用即给端点。初末总能量都是 $5\Delta$，每步信号增加的 $\Delta$ 来自一个资源位。

若菜单只供应相邻 $V_j$，没有单次 $1\to5$ 操作，但有四步实现。更一般地，若每个守恒原子只接触信号与一个能谱宽度为 $w_R$ 的资源，二元能隙配平直接给

$$
|E_{\rm out}-E_{\rm in}|
=|\epsilon_{\rm in}-\epsilon_{\rm out}|
\le w_R.
$$

本例单资源位的谱宽为 $\Delta$，而 $1\to5$ 需要 $4\Delta$，因此任何这种单接触原子都不能直跳；四次接入不同资源则可以。能量守恒本身并不禁止直接交换上述两个等总能量端点；若允许同时接触四个资源，多体直接交换便不受上述单资源谱宽限制。缺少直边来自耦合范围、菜单或阈值合同。

**白话图景。**小骨牌没有把自己的能量凭空放大成大骨牌的全部能量。它开启了下一块已经准备好的储备，下一块再开启更大的储备。量子版本也可以这样接力：每个内部资源位交出一份能量，信号逐级提高。中间结构同时解决触发门槛和可用连接；两者都要放进完整描述。

<a id="section-14"></a>

## 14. 有连接路径，还要检查相位与实际控制

### 命题 14.1（有两条路径却完全没有传输）

在同一个总能量块内取四个正交态，令

$$
K=g\bigl(\ket2\bra1+\ket3\bra1+
\ket4\bra2-\ket4\bra3+\text{h.c.}\bigr),
\qquad g\in\mathbb R\setminus\{0\}.
$$

耦合图有路径 $1\to2\to4$ 与 $1\to3\to4$，但对全部实时间

$$
\boxed{\bra4 e^{-itK/\hbar}\ket1=0.}
$$

**证明。**令 $\ket\pm=(\ket2\pm\ket3)/\sqrt2$。$K$ 只耦合 $1\leftrightarrow+$ 与 $4\leftrightarrow-$，两块均不变。初态 $\ket1$ 始终留在 $\operatorname{Span}\{\ket1,\ket+\}$，与 $\ket4$ 正交。

```text
      2          4
     / \        /
    1   ?      /
     \ /      /
      3

1--2 and 1--3 have amplitude g;
2--4 has amplitude g, while 3--4 has amplitude -g.
The symmetric block {1,+} and antisymmetric block {4,-} are invariant.
```

若原生控制可以独立开关各边，可以选择单一路径；固定全部同时工作的 $K$ 则不能把该权限自行补入。因此辅助结构的存在、可准备性、相位相容、控制顺序与成本分别需要核验。

**白话图景。**有路不代表一定走得到。在量子关系中，两条路可以把同一个结果相互抵消。因此“关系的关系”还包括不同路径之间的相位。中间结构真正有用，需要能按允许的方式触发，并让最终振幅实际留下来。

<a id="section-15"></a>

## 15. 接回现有量子公理的完整条件链

本节明确区分继承接口与本轮新增。$C_{85}$ 使用既有复 Hilbert 表示、酉性和概率响应；不能再把这些已使用内容宣称由 $C_{85}$ 一条条件独自推出。

### 定理 15.1（共同正核的态表示）

给内容集合上的共同归一复正核 $k$，在形式有限和上定义

$$
\left\langle\sum_i c_i\delta_{x_i},\sum_jd_j\delta_{y_j}\right\rangle
=\sum_{i,j}\overline{c_i}k(x_i,y_j)d_j.
$$

商去零范数方向并完成化，得到 Hilbert 表示；有限秩切口给有限维 $H$，且 $k(x,y)=\langle\iota(x),\iota(y)\rangle$。

**证明。**全部有限 Gram 正性给半内积和 Cauchy–Schwarz；零范数方向与所有向量正交，所以商内积良定义。有限维时自动完备。

### 定理 15.2（v84 的完整门接口）

在同维有限单位球面上，实际 $F$ 全输入不扩张；完整实正交框的每个正反对可由 $F$ 的共同正迭代任意精度回返；有限复基满足 $F(ia_j)=iF(a_j)$。则实际 $F$ 唯一扩展为复线性酉算子。

**证明。**正反点距离原为 2，非扩张及回返迫第一步距离仍为 2，故 $F(-b)=-F(b)$。分别比较任意 $x$ 与 $b,-b$，夹定 $\operatorname{Re}\langle Fx,Fb\rangle=\operatorname{Re}\langle x,b\rangle$。完整实框锁住全部坐标，实际 $F$ 因而实线性正交；有限 $i$ 相容再迫复线性，同维有限性给酉性。

### 定理 15.3（动力学、记录与 Born 读出）

可微实际酉族给

$$
H=i\hbar\dot UU^\dagger=H^\dagger,
\qquad i\hbar\dot\psi=H\psi.
$$

内部记录准备 $\ket0$、记录基 $\ket e$ 给

$$
M_e=(I\otimes\bra e)U(I\otimes\ket0),
\qquad\sum_eM_e^\dagger M_e=I.
$$

在既有分支强度—概率标定下，

$$
E_e=M_e^\dagger M_e,
\qquad
p(e|\psi)=\lVert M_e\psi\rVert^2
=\langle\psi,E_e\psi\rangle.
$$

非零结果后继为 $M_e\psi/\lVert M_e\psi\rVert$；合并记录给完全正仪器。

**证明。**微分酉条件给反自伴切向生成元；记录基完备给 Kraus 完备式；其余为效果定义、既有概率标定和条件化。

同一读出概念需在不同记录实现间相容，不能把同一个数值平方自动解释为频率或概率。

### 定理 15.4（密度矩阵与复合系统）

若对所有效果 $0\le E\le I$ 有同一个非负归一响应 $f$，且对合法和部分可加，则存在唯一

$$
\rho\ge0,
\qquad\operatorname{tr}\rho=1,
\qquad f(E)=\operatorname{tr}(\rho E).
$$

若独立准备核相乘，且乘积准备张成声明复合载体，则 $H_{AB}\cong H_A\otimes H_B$。

**证明。**部分可加性给有理齐次，正性给单调性及实齐次。对正算子用正整数 $n\ge\lVert A\rVert$ 的 $nf(A/n)$ 延伸，再用自伴差与有限维迹对偶得到 $\rho$；正性和归一给其两项条件。乘积准备映到向量张量积时保持全部内积，零范数商给等距，张成给满射。

投影效果 $P$ 再加该结果操作固定 $\operatorname{ran}P$ 内每个纯态，得到 $\rho\mapsto P\rho P$：Kraus 算子先由效果关系满足 $A_\alpha=A_\alpha P$，再由每个范围内向量保持射线及线性叠加，得到 $A_\alpha=c_\alpha P$；$P\ne0$ 时 $\sum|c_\alpha|^2=1$，$P=0$ 时全部为零。局部张量端口对易；远端完整仪器的 Kraus 完备式保证忽略结果后本端响应不变。

### 定理 15.5（有限过程重建与新增能量层）

上述准备、共同核、酉门、内部记录及粗粒化生成的有限过程，具有标准复量子态、效果、酉演化与完全正仪器表示。添加同一 $G$ 的 $C_{85}$，封闭完整过程被限制为与 $G$ 对易的酉子群；系统与资源的非零转移满足二元能隙配平。

**证明。**前述各定理给正向表示。反向，对任意 $\sum_\alpha M_\alpha^\dagger M_\alpha=I$，

$$
W\psi=\sum_\alpha M_\alpha\psi\otimes\ket\alpha
$$

是等距，在足够大的有限载体上补齐为酉；读记录恢复原仪器。迹不增族先补 $\sqrt{I-\sum_\alpha M_\alpha^\dagger M_\alpha}$ 对应的剩余结果。任意密度矩阵有谱准备或纯化，任意效果可用 $\sqrt E,\sqrt{I-E}$ 两分支。能量部分由本轮主定理及加性谱直接推出。

这些数学扩张不自动获得原生调用权限。若控制菜单供应全部相应对象，得到整个有限维量子过程类；若另要求固定 $G$ 守恒，系统端的其他操作还需要声明合适资源及精度，不能据一般酉扩张就声称任何能量约束下都可精确实现。

| 标准规则／新结果 | 内部关系来源 | 保留的条件 |
| --- | --- | --- |
| 复 Hilbert 态空间 | 共同复正核的零范数商 | 所有有限 Gram 相容 |
| 实际线性酉门 | v84 正历史回返与有限锚刚性 | 完整同维载体、全输入不扩张、$J$ |
| 薛定谔方程 | 可微酉族的生成元 | 实际内部时钟及单位标定 |
| Born 读出与仪器 | 内部记录、分支效果 | 同一概率标定与记录完备 |
| 密度矩阵 | 全效果正归一可加响应 | 跨读口一致性 |
| 张量积与纠缠 | 独立准备核相乘及张成 | 相干准备和实际复合端口 |
| 能量分布守恒 | $C_{85}$ 有限均值闭合 | 固定共同 $G$、完整酉操作 |
| 系统—资源配平 | 总能量的加性谱 | 交互预算、资源和开关不遗漏 |
| 相干资源约束 | 完整守恒与约化协变 | 辅助态的时间相干条件 |
| 轨道偏转 | 两个中心化生成方向的 Gram 几何 | 固定参考、非零方差分母 |
| 多级接力 | 预存资源、阈值、允许耦合 | 不从能量守恒补造控制边 |

**白话图景。**共同关系给态空间，正向回返保护完整差别，得到酉门。内部时钟把酉变化写成生成元；记录读出给效果、概率与条件后继；组合相容给复合系统。本轮再加一条有限能量校准，把能量交换锁进完整内部账本。这是一套逐项可检查的有限理论，具体自然系统是否满足各项，仍须相应的内部读出和实现证据。

<a id="section-16"></a>

## 16. 一段完整白话与结论范围

**白话图景。**$\Omega$ 中同时有内容、参照、时钟、控制和储备。一个投影型基础门反复工作，只改变两个有效分量的相对相位，所以可以绕出圆；更多频率一起变化，会形成更复杂的路线。

要从当前态走向另一个态，可以把目标分成当前方向和一个正交切向，但两部分要按余弦、正弦共同归一。要离开旧路线，需要新的横向生成作用；在二能级中它与能量流直接对应，高维还允许不交换平均能量的相位重排。

能量既是内部读口，也是内部时钟生成元的标定。只要完整门保留有限能量参照的均值，酉关系就迫使每条非零转移的总能量配平：工作部分取得的那一份，要在资源或相互作用中找到对应来源。

多米诺就是逐级释放已经准备好的储备；中间结构负责触发和连接，相干路径还必须检查会不会相互抵消。因此真正完整的描述，是内容、路线、时钟、资源和记录之间的共同关系。

本轮严格证明的核心是有限能量均值校准与能量块保持的等价，其单标定态与有限误差形式，以及相对生成元的三维偏转恒等式。未把任意轨迹都叫圆、未把面积或路径长度直接当信息量，也未把资源容量、净平均功和耗散混成同一个量。$\Omega$ 的内生性指定概念所属的整体；选择哪些内部约束刻画实际世界，仍是有内容的理论条件。

本轮没有修改远端仓库，也没有认证未取得的新 HEAD。无限维定义域、具体 Hamiltonian、物理常数与实际原生控制供应仍保留其明确接口。

<a id="references"></a>

## 来源与版本关系

<a id="ref-omega"></a>

1. trureturing， [整体静态相容纤维理论固定原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。本轮沿用正历史、控制菜单及双随机重叠接口。

<a id="ref-fib"></a>

2. trureturing， [AURIC 量子原则与相干重建续卷 V](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_V.md)，第 1 节完整正向脉冲。

<a id="ref-v74"></a>

3. trureturing， [V74：光滑历史、余切动力学与内生运动](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)，第 4、5、9、10 节。

<a id="ref-v78"></a>

4. trureturing， [V78 综合稿](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md)，第 16 节生成元、期望求导与时钟标定。

<a id="ref-v84"></a>

5. 对话研究稿，AURIC v84，《正历史回返、手性原子与椭圆读出》，2026 年 11 月 2 日。本轮直接承接其有限锚正回返候选及完整证明。

<a id="ref-aberg"></a>

6. Johan Åberg， [Catalytic Coherence](https://arxiv.org/html/1304.1060v3)，Physical Review Letters 113, 150402 (2014)。本轮核读 Appendix A.1–A.2、B.2–B.3 的能量块、全输入均值等价及内部时钟资源说明。

<a id="ref-lostaglio"></a>

7. Matteo Lostaglio, David Jennings, Terry Rudolph， [Description of quantum coherence in thermodynamic processes requires constraints beyond free energy](https://arxiv.org/pdf/1405.2188)，Nature Communications 6, 6383 (2015)。Theorem 1 与 Methods 的协变证明。

<a id="ref-chiribella"></a>

8. Giulio Chiribella, Yuxiang Yang, Renato Renner， [Fundamental Energy Requirement of Reversible Quantum Operations](https://arxiv.org/pdf/1908.10884)，Physical Review X 11, 021014 (2021)。电池初始资源需求与每步耗散分开。

<a id="ref-domino"></a>

9. J. M. J. van Leeuwen， [Domino Magnification](https://arxiv.org/pdf/1301.0615)。本轮使用翻倒势垒、预存势能、碰撞及几何条件，未使用其数值计算作为本轮证明。

<a id="ref-anandan"></a>

10. J. Anandan and Y. Aharonov， [Geometry of quantum evolution](https://doi.org/10.1103/PhysRevLett.65.1697)，Physical Review Letters 65, 1697–1700 (1990)。沿用前轮已核读的能量方差与射影速度联系。

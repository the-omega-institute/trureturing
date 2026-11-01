# 情境时空算术的量子扩展：仪器历史与记忆容量

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](053_071_PREDICTION_AND_READOUT.md) · [续卷](099_120_CORRELATION_AND_INSTRUMENTS.md)

<a id="section-72"></a>


## 72. 仪器级历史误差、参考系统与自适应读出

第 70–71 节的 $\delta$ 比较的是系统末态：它可以说明一次记录后系统态相差多少，却不能自动说明完整的多时记录分布相差多少。要把“历史是否被保留”放到可检验的对象上，需要把记录仪器和它写下的经典寄存器一起纳入通道。

设 $\{\mathcal I_y\}_{y\in Y}$ 是一个有限结果的量子仪器。每个 $\mathcal I_y$ 是完全正的无迹非增映射，非选择通道为

$$
\mathcal N=\sum_{y\in Y}\mathcal I_y.
$$

以下假设 $\mathcal N$ 是 CPTP；因此 $\mathcal I_y$ 是一组合法的仪器分支。若实际模型只给出一个未归一化的 CP 分支，必须另外保留其发生概率，不能直接把条件化后的态代入下面的无条件距离界。

用经典寄存器 $C$ 保存结果，定义仪器的非选择抬升：

$$
\widehat{\mathcal I}(\rho)
=
\sum_{y\in Y}
|y\rangle\langle y|_C\otimes\mathcal I_y(\rho).
$$

若 $R$ 是没有被仪器直接读取的参考系统，则抬升到联合系统的通道为

$$
\widehat{\mathcal I}_R
=
\operatorname{id}_R\otimes\widehat{\mathcal I}.
$$

这一步不是给系统添加一个外部观察者。$C$ 是整体内部的一部分，$R$ 则表示我们允许在检验时保留的关联自由度。只对系统取边缘，或者只看单步的 $\mathcal N(\rho)$，都会忘掉这两个寄存器中的可用区别。

<a id="entry-287"></a>

### 72.1 完整历史的通道距离

设 $\Phi_k$ 是第 $k$ 个时间槽的物理演化，$\widehat A_k$ 和 $\widehat B_k$ 是同一记录协议下的两种候选槽通道。例如，未先丢弃当前不可见部分的候选可以写成

$$
\widehat A_k
=
\widehat{\mathcal I}_k\Phi_k,
$$

而先执行当前粗粒化的候选写成

$$
\widehat B_k
=
\widehat{\mathcal I}_k\Phi_k\mathcal E_k.
$$

这里的帽号表示：槽通道同时更新系统和历史寄存器；它不是只对系统矩阵取一个偏迹。令

严格地说，$\widehat A_k$、$\widehat B_k$ 应是同一累计协议中的完整轮次通道：它们把

$$
X_k=H_{k-1}\otimes S_k\otimes M_k
$$

映到共同的

$$
X_{k+1}=H_k\otimes S_{k+1}\otimes M_{k+1},
$$

旧历史由恒等或共同控制保留，必要时对 codomain 做 padding。$\eta_k$ 是这两个完整映射的半 diamond 距离；这样 $\widehat A_{1:n}=\widehat A_n\circ\cdots\circ\widehat A_1$ 的复合才有类型。只定义 $S\to C\otimes S$ 的单槽映射还不足以直接写望远镜复合。

$$
\eta_k
=
\frac12
\left\|
\widehat A_k-\widehat B_k
\right\|_\diamond,
$$

其中 diamond 范数已经对任意有限维参考系统取上确界。设 $\widehat A_{1:n}$ 与 $\widehat B_{1:n}$ 是由这些槽按同一历史寄存器协议组成的 $n$ 步过程通道，则通道范数的望远镜展开给出

$$
\boxed{
\frac12
\left\|
\widehat A_{1:n}-\widehat B_{1:n}
\right\|_\diamond
\le
\min\!\left\{1,\sum_{k=1}^{n}\eta_k\right\}.
}
$$

在均匀界 $\eta_k\le\eta$ 下，这给出 $\min\{1,n\eta\}$。证明只使用每个槽的三角不等式、其余槽通道的 diamond 收缩性，以及望远镜分解；因此它比较的是完整抬升过程，而不是把系统末态距离误称为历史分布距离。

对任意初始联合态 $\rho_{RS}$，有

$$
\frac12
\left\|
\bigl(\operatorname{id}_R\otimes\widehat A_{1:n}\bigr)(\rho_{RS})
-
\bigl(\operatorname{id}_R\otimes\widehat B_{1:n}\bigr)(\rho_{RS})
\right\|_1
\le
\min\!\left\{1,\sum_{k=1}^{n}\eta_k\right\}.
$$

再对系统、参考或量子寄存器取偏迹，并对 $C$ 做任意经典读出，距离只能下降。因此，对完整记录序列的概率分布 $p_{1:n}$、$q_{1:n}$，总变差距离满足

$$
\boxed{
\operatorname{TV}(p_{1:n},q_{1:n})
\le
\min\!\left\{1,\sum_{k=1}^{n}\eta_k\right\}.
}
$$

这个结论给出了“保留的历史是否足以区分两种过程”的直接判据：必须先指定记录寄存器和参考系统，再计算抬升过程的通道距离。

<a id="entry-288"></a>

### 72.2 幂等记录的强化范围

一次性界只有在固定的累计空间上才可使用。令 $X$ 是包含系统、历史寄存器和活动工作记忆的固定有限维空间，另以 $R$ 表示未被过程直接操作的惰性参考系统；$P:X\to X$ 是 CPTP 且满足

$$
P^2=P.
$$

令 $A,B:X\to X$ 是 CPTP，并假设

$$
P\circ A=A,
\qquad
P\circ B=B,
\qquad
A\circ P=B\circ P
$$

最后一个等式要作为完全有界映射理解，即对任意参考系统 $R$ 都有

$$
(A\otimes\operatorname{id}_R)\circ(P\otimes\operatorname{id}_R)
=
(B\otimes\operatorname{id}_R)\circ(P\otimes\operatorname{id}_R).
$$

在这些条件下，归纳得到 $A^mP=B^mP$，并且对 $n\ge1$ 有

$$
A^n-B^n=A^{n-1}P(A-B).
$$

因此

$$
\boxed{
\frac12\lVert A^n-B^n\rVert_\diamond
\le
\frac12\lVert A-B\rVert_\diamond.
}
$$

这里的 $P$ 必须是固定累计空间上的 endomap。新鲜记录的抬升通常是 $S\to C\otimes S$，第二次作用已经改变了空间，不能直接写成 $P^2$；若每轮都追加新历史，应该使用 72.1 的完整轮次通道和式。若旧记录被相干地重新写入，也必须把它放进 $X$ 后重新检查完全有界的 $A\circ P=B\circ P$，不能只用系统态上的相等。

这一区分解释了两个看似矛盾的事实：一次系统记录可以已经落在经典像空间，而完整历史过程仍然保留跨时关联；一次系统态的误差可以不随 $n$ 累积，而自适应控制器对整段记录的可区分误差仍然需要逐槽预算。

<a id="entry-289"></a>

### 72.3 自适应协议与参考系统不能被省略

若第 $k+1$ 个操作根据前面记录 $y_{1:k}$ 选择不同的 $\Phi_{k+1,y_{1:k}}$，则过程不再是一个与历史无关的固定幂。可以把经典控制器并入 $C$，把每个分支的控制动作写进一条抬升通道；对所有分支统一取 diamond 范数后，72.1 的望远镜界仍可使用。这里要求实际协议和理想协议使用同一个控制器；若控制器本身也随协议改变，其差异必须计入相应的 $\eta_k$。若控制器还保有会在后续操作中参与的量子记忆，则必须把该记忆并入活动系统和通道；只有从整个过程中始终不被操作的辅助系统，才可作为惰性参考 $R$。否则只比较系统边缘会漏掉可重新参与的相位。对经典历史寄存器逐分支取最大误差，只能在每一步先去相干、输入确实是经典块对角时替代整合通道的 diamond 范数。

因此，对任意长度不超过 $H$ 的前缀都要分别检查

$$
\operatorname{TV}(p_{1:k},q_{1:k})
\le
\sum_{j=1}^{k}\eta_j,
\qquad
1\le k\le H,
$$

不能用终点 $k=H$ 的界替代所有前缀，也不能把只对 $\mathcal E^H$ 成立的 $q^H$ 衰减直接套到交错的 $\mathcal E\Phi$ 过程。若研究的是联合历史、参考系统和自适应策略的最坏情况，所需对象是过程或 comb 的距离；系统态的单步闭合缺陷只是其中一个输入量。

<a id="entry-290"></a>

### 72.4 与 Zeckendorf 合法构型的连接

对长度 $L$ 的无相邻 $1$ 合法窗口

$$
\mathcal W_L
=
\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
\qquad
|\mathcal W_L|=F_{L+2},
$$

可以把 $w$ 作为仪器输入标签，把记录结果 $y_w$ 作为内部历史寄存器的一个槽，并假设这些标签两两不同、来自同一个 POVM。只有在同一个槽的 POVM 对所需的构型或未来响应类满足

$$
\Pr(y=y_w\mid w')
=
\mathbf 1_{w=w'}
$$

时，才可以把 $F_{L+2}$ 直接代入完美记忆容量下界。若仪器只保留 Zeckendorf 数值的某个函数，或只需预测后续任务 $F(w)$，则应先按仪器级响应分组，再对真正需要区分的标签数使用容量定理。

在近似情形，给定容许错误 $\epsilon$，应报告

$$
\operatorname{TV}(p_{1:H},q_{1:H}),
\qquad
D(\rho_w^M,\rho_{w'}^M),
\qquad
\left|\langle r_{w'}\mid r_w\rangle\right|,
$$

并说明它们对应的是完整历史、记忆态还是单步相干。最后一个 Gram 重叠只适用于条件记录是纯态 $|r_w\rangle$ 的情形；若记录态是混态，应改报迹距离、保真度或明确选定的广义 Gram 量。三者不能互相替代。于是，Zeckendorf 提供的是合法输入的递归索引；仪器抬升决定哪些索引进入历史；diamond 或过程距离决定这些历史在允许参考系统和控制器下是否仍可被区分。

若记忆态或参考系统本身可被后续操作访问，它们必须计入活动系统的维数与通道；若它们被声明为不可访问环境，则只能在明确取迹后使用收缩性。对后选择分支，归一化会除以分支概率，可能放大条件误差，所以必须使用未归一化 CP 分支的距离，或另给出统一的分支概率下界。

本节还需要一个编码层面的限定。`FiniteMemoryHistoryCapacity` 的有限索引结论适用于同一个 POVM 完美区分 $N$ 个密度态；把 $|\mathcal W_L|=F_{L+2}$ 代入它，还需要给出合法窗口与 $\operatorname{Fin}(F_{L+2})$ 的明确枚举或双射。若只知道构型计数而没有这条重索引，不能直接把 Fibonacci 数写成定理中的 $N$。若记忆可访问的是联合 $M\otimes R$，容量维数也应取联合空间；多轮自适应协议可以使用较小的瞬时记忆，不能从单轮的 $F_{L+2}$ 计数推出每一轮都需要同样大小的记忆。

上述 diamond 望远镜、过程抬升和自适应控制边界是本卷在已有记录、偏迹和容量结果上的新组合；它们不是当前仓库已经冻结的单一 Lean 定理。涉及具体仪器时，仍需在选定的有限维通道、Kraus 数据、记录空间和 axiom 闭包下单独形式化与构建。

本节把“历史回流”从系统末态的比喻改写成了一个可计算的过程级问题：先固定仪器、记录寄存器、参考系统和控制策略，再对完整过程取距离。没有这些对象，单个 $\delta$、单个 $q^H$ 或单个历史条数都不足以证明稳定的经典预测。

<a id="section-73"></a>

## 73. 预测尾空间的最小维数与 Zeckendorf 记录压缩

第 71 节的记忆容量回答的是“要一次完全区分多少个记录态”，第 72 节的过程距离回答的是“两个完整仪器协议相差多少”。两者之间还缺一个更贴近预测的问题：如果我们只要求重现允许实验的全部未来响应，当前状态描述的最小线性维数是多少？

设 $K$ 是一个域，$U$ 是输入方向空间，$Y$ 是读出方向空间，给定一列线性响应

$$
 m=(m_n)_{n\ge0},
 \qquad
 m_n:U\to Y.
$$

这里的 $m_n$ 可以是第 $n$ 步的记录期望、中心化 effect 的坐标，或固定实验族下的线性概率响应。它不是自动等于完整密度矩阵；若原始概率带有归一化约束，应先明确选取线性坐标和剩余的归一化条件。

定义所有未来尾的线性空间：

$$
\mathcal T(m)
=
\operatorname{span}_K
\left\{
 i\longmapsto m_{i+j}(u):
 j\in\mathbb N,\ u\in U
\right\}
\subseteq(\mathbb N\to Y).
$$

它保留的不是历史词的身份，而是历史在所有未来时刻和允许输入方向下能够产生的响应形状。相同的当前读数但不同的未来尾，会在这个空间中留下不同方向。

<a id="entry-292"></a>

### 73.1 有限尾空间恰好等价于有限线性预测实现

仓库的 `D5.S3.Observer.Hankel.SequenceHankelRealization` 已给出以下等价关系：

$$
\boxed{
\mathcal T(m)\text{ 有限维}
\iff
\text{存在有限维线性系统完整重现 }m.
}
$$

更具体地，若系统为

$$
(V,A,B,C),
\qquad
A:V\to V,\quad B:U\to V,\quad C:V\to Y,
$$

其 Markov 响应为

$$
 m_n=C A^n B,
$$

则每个未来尾都来自 $V$ 的像，所以

$$
\dim\mathcal T(m)\le\dim V.
$$

反向地，把尾空间本身作为状态空间，令左移成为动力学，当前坐标成为输出，就得到一个重现全部 $m_n$ 的有限实现。因此最小状态维数不是凭经验选出的记忆长度，而是

$$
\boxed{
 d_{\mathrm{pred}}(m)
=\operatorname{finrank}_K\mathcal T(m).
}
$$

这个等式的适用范围是线性响应实现。它不声称任意非线性控制器、任意量子通道或任意带后选择的条件概率都能被同一个线性载体代表。

<a id="entry-293"></a>

### 73.2 低于尾空间维数的压缩必然留下未来见证

若 $\mathcal T(m)$ 有限维，取一个线性压缩

$$
Q:\mathcal T(m)\to W
$$

并假设

$$
\operatorname{finrank}W
<
\operatorname{finrank}\mathcal T(m),
$$

则仓库定理 `smaller_compression_has_future_witness` 给出某个非零尾方向 $x$，满足

$$
Qx=0,
$$

但存在有限时刻 $n$ 使

$$
\operatorname{out}(A^n x)\ne0.
$$

因此，压缩器当前看不到的方向，会在某个有限未来实验中重新出现。这个结论把“历史回流”改成了有限见证：不需要假定无限复杂的过去，只要压缩低于尾空间秩，就存在一个可定位的未来读出将其分开。

它也给出了与第 71 节不同的容量概念：

$$
\text{完美记录容量}
\quad\ne\quad
\text{线性预测维数}.
$$

前者要求一次 POVM 区分记录态；后者只要求对指定响应族重现未来输出。很多原始历史可以共享一个预测状态，只要它们在全部允许的未来尾上相同。

<a id="entry-294"></a>

### 73.3 有限 Hankel 窗口与可执行校准

对行数 $r$、列数 $c$ 定义有限数据 Hankel 映射

$$
H_{r,c}(u_0,\ldots,u_{c-1})
=
\left(
\sum_{j=0}^{c-1}m_{i+j}(u_j)
\right)_{0\le i<r}.
$$

当 $r,c$ 都不小于 $\operatorname{finrank}\mathcal T(m)$ 时，已有定理 `dataHankel_rank_eq_tailSpace` 给出

$$
\operatorname{rank}H_{r,c}
=
\operatorname{finrank}\mathcal T(m).
$$

这把“需要观察多深”变成了可校准的有限窗口条件。若实际数据带误差，不能直接把观测矩阵的数值秩当成精确秩；应使用第 67 节的条件数和最小二乘噪声界，并声明截断阈值、误差模型与任务容限。

第 72 节的 diamond 距离控制的是完整仪器过程；Hankel 尾空间控制的是选定线性响应坐标。两者的连接需要一个明确的读出映射：先由过程产生记录分布或 effect 期望，再把它们送入 $Y$。没有这个映射，不能用一个状态空间秩替代过程级历史距离。

<a id="entry-295"></a>

### 73.4 Zeckendorf 合法构型只给输入索引，不直接给预测维数

令

$$
\mathcal W_L
=
\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
\qquad
|\mathcal W_L|=F_{L+2}.
$$

可以把每个 $w\in\mathcal W_L$ 作为一个输入标签，构造一个输入空间 $U$。但从标签集合到线性空间还需要指定编码：例如选择基向量 $e_w$，再给出每个未来实验对 $e_w$ 的响应 $m_n(e_w)$。只有在这些响应方向线性独立、并且全部时间移位都落在这组方向所张成的同一个预测载体中时，才会得到

$$
\operatorname{finrank}\mathcal T(m)=F_{L+2}.
$$

合法标签本身并不给出无条件的 $\operatorname{finrank}\mathcal T(m)\le F_{L+2}$：时间移位可能产生额外的动力学方向，使尾空间维数大于瞬时输入标签数。只有在另有一个维数至多为 $F_{L+2}$ 的预测载体，并且所有移位尾都通过它因子化时，才能推出这个上界。反过来，在指定任务的全部未来响应中，不同 Zeckendorf 字串也可能落入同一个尾方向，使实际预测维数严格小于标签数；如果允许的响应还包含未编码的相位、参考关联或历史寄存器，预测空间则可能大于单个 Zeckendorf 数值的像。

所以，Fibonacci 数量、完美记忆维数和预测 Hankel 秩分别回答三个问题：

$$
\begin{aligned}
&F_{L+2}: &&\text{有多少个合法输入构型？}\\
&d_M: &&\text{一次读取能完美区分多少个记忆态？}\\
&d_{\mathrm{pred}}: &&\text{指定未来响应需要多少个线性预测方向？}
\end{aligned}
$$

把三者直接相等，必须额外给出编码双射、同一 POVM 的完美区分以及未来响应方向的独立性。否则 Zeckendorf 只是适配约束的坐标尺，不是自动生成的物理记忆大小。

本节复用的是仓库已冻结的 Hankel 尾空间与最小实现结果；将其解释为量子过程的预测维数仍需明确线性读出、状态域和仪器协议。具体量子模型若要得到新的 Lean 结论，应先固定有限维通道和 effect 坐标，再分别证明过程到 $m_n$ 的映射、尾空间有限性及其噪声稳定性。

<a id="section-74"></a>

## 74. 投影残差、有限视界误差与可接受的历史压缩

第 73 节给出了预测尾空间的最小维数，但实际记录通常还要压缩。压缩是否可接受，不能只看状态维数下降了多少；需要计算压缩动力学与完整动力学在指定视界内产生的输出差异。

取实赋范线性空间

$$
V,W,U,Y
$$

完整线性实现为

$$
 x_{n+1}=Ax_n+Bu_n,
 \qquad
 y_n=Cx_n.
$$

选择一个压缩映射和一个提升映射

$$
P:V\to W,
\qquad
J:W\to V,
$$

并用实际压缩动力学

$$
\widetilde A=PAJ,
\qquad
\widetilde B=PB,
\qquad
\widetilde C=CJ
$$

生成近似输出。这里不要求

$$
PJ=I_W.
$$

如果它不是回缩投影，下面的残差仍然有定义，但不能把这两个映射自动称为同一个子空间的正交投影。

定义动力学和输入残差：

$$
R_A=AJ-J\widetilde A,
\qquad
R_B=B-J\widetilde B.
$$

它们分别测量提升后的压缩一步与完整一步的差，以及输入没有被压缩提升完整保留的差。令完整状态和压缩状态从零初值出发，定义

$$
e_n=x_n-J\widetilde x_n.
$$

由实际递推直接得到

$$
 e_{n+1}
=
Ae_n+R_A\widetilde x_n+R_Bu_n.
$$

<a id="entry-297"></a>

### 74.1 有限视界的残差和界

仓库的 `D5.S3.Observer.Hankel.ProjectedRealizationError` 已证明，在任意有限步

$$
n
$$

有

$$
\boxed{
\|e_n\|
\le
\sum_{k=0}^{n-1}
\|A\|^{n-1-k}
\left(
\|R_A\|\,\|\widetilde x_k\|
+
\|R_B\|\,\|u_k\|
\right).
}
$$

再由输出映射得到

$$
\boxed{
\|y_n-\widetilde y_n\|
\le
\|C\|
\sum_{k=0}^{n-1}
\|A\|^{n-1-k}
\left(
\|R_A\|\,\|\widetilde x_k\|
+
\|R_B\|\,\|u_k\|
\right).
}
$$

这条界说明“删除历史”造成的误差具有时间方向：较早的残差会被后续完整动力学反复传播，传播权重是

$$
\|A\|^{n-1-k}.
$$

因此，相同的静态压缩维数在不同的预测视界和动力学下可以有完全不同的可靠性。

如果输入满足

$$
\|u_k\|\le M,
$$

且压缩动力学和完整动力学分别满足

$$
\|\widetilde A\|<1,
\qquad
\|A\|<1,
$$

则已有的 uniform 结果给出一个与

$$
n
$$

无关的充分界：

$$
\boxed{
\|y_n-\widetilde y_n\|
\le
\|C\|
\frac{
\|R_A\|
\dfrac{\|\widetilde B\|M}{1-\|\widetilde A\|}
+
\|R_B\|M
}{1-\|A\|}.
}
$$

这个结论的稳定性假设是范数收缩，而不是仅仅谱半径小于一。若只有谱半径信息，还需要另一个范数转换或暂态增长界；不能直接把上式套用。

<a id="entry-298"></a>

### 74.2 任务误差与历史压缩的停止条件

给定预测视界

$$
H
$$

、任务输出容限

$$
\varepsilon_{\mathrm{task}}
$$

和输入界

$$
M\ge0
$$

，可以把压缩接受条件写成

$$
\max_{0\le n\le H}
\|y_n-\widetilde y_n\|
\le
\varepsilon_{\mathrm{task}}.
$$

有限视界时，直接使用 74.1 的残差和界即可；若需要所有未来时刻的统一保证，则需使用 74.1 的收缩条件或独立的尾项可和性证明。这个停止条件保留的是任务所需的响应精度，而不是任意恢复完整原始历史。

第 73 节的低维压缩见证与这里的残差界互补：

$$
\begin{aligned}
&\text{若压缩载体维数小于 }d_{\mathrm{pred}}(m)\text{，且对同一完整响应族的全部允许输入与时刻残差为零}
&&\Longrightarrow\text{违反第 73 节的最小实现性；}\\
&\text{压缩载体维数下降但残差有界}
&&\Longrightarrow\text{只在给定 }H,M,\varepsilon_{\mathrm{task}}\text{ 内可接受；}\\
&\text{残差上界无界或任务容限趋于零}
&&\Longrightarrow\text{该上界本身不能证成预测等价。}
\end{aligned}
$$

这里的第一行要求零残差覆盖整个指定响应族；若只对一个输入序列或一个时刻为零，最多得到该任务实例的精确复现，不能推出尾空间维数矛盾。

因此，“稳定经典对象”可以采用一个带误差的预测接口：接口不保留所有历史方向，但对指定输入界和视界给出可核验的输出误差。

<a id="entry-299"></a>

### 74.3 量子读出与 Zeckendorf 编码的适用边界

若量子过程先经过一个明确的线性读出映射

$$
L:\rho\longmapsto x(\rho)\in V,
$$

再用

$$
C
$$

读取目标响应，那么 74.1 可以用于这组坐标。要把坐标误差转成量子态的迹距离或概率误差，还必须给出

$$
L,
$$

和

$$
C
$$

与所选距离之间的范数转换；第 67 节的帧下界和第 72 节的 diamond 距离分别承担不同层面的稳定性，不能互相替代。

对 Zeckendorf 合法构型

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
$$

若合法字串的基向量

$$
e_w\in U
$$

作为输入坐标送入动力学，则压缩输入是

$$
\widetilde B e_w=PB e_w,
$$

而不是在没有给定类型识别时直接写成 $$P e_w$$。只有另有注入

$$
I:U\to V
$$

时，才可以把状态空间中的压缩写成 $$P I(e_w)$$。若两个合法字串在压缩后相同，并且在同一后续输入协议、同一初态约定下的未来响应差异超过

$$
2\varepsilon_{\mathrm{task}},
$$

则不存在一个同时使两者误差不超过 $$\varepsilon_{\mathrm{task}}$$ 的共同近似接口；仅超过 $$\varepsilon_{\mathrm{task}}$$ 还不足以推出这一点。若它们的全部指定响应差异被残差界覆盖，则可以在该有限任务中共享一个预测接口。

这里不把

$$
|\mathcal W_L|=F_{L+2}
$$

直接当作压缩后的维数。Fibonacci 计数只给合法输入构型数；实际可接受的预测维数由

$$
P, A, B, C
$$

、输入界、视界和误差容限共同决定。若压缩还要保留纯态相位或可访问参考关联，则这些方向必须进入

$$
V
$$

，否则实线性残差界没有覆盖它们。

本节直接复用 `ProjectedRealizationError` 的有限残差和、输出误差和收缩统一界；这些声明针对实赋范线性系统。将它们提升为量子通道的 trace/diamond 界，需要另外证明读出嵌入、完全正性、参考系统和距离转换，不能由线性公式自动推出。

<a id="section-75"></a>

## 75. 精确下降的选择性：投影态先精确，读出还需因子化

第 74 节的残差界允许完整状态和压缩状态之间存在误差，并用有限视界控制这种误差。仓库还给出了一个更强、但适用范围更窄的结果：如果动力学先在选定投影下精确下降，且目标读出只依赖这个投影，那么目标输出可以逐步完全相同，即使提升回完整空间的状态仍有残差。

令完整系统、压缩系统和读出分别由

$$
A:V\to V,
\qquad
B:U\to V,
\qquad
C:V\to Y,
$$

以及

$$
P:V\to W,
\qquad
J:W\to V
$$

给出，并定义

$$
\widetilde A=PAJ,
\qquad
\widetilde B=PB,
\qquad
\widetilde C=CJ.
$$

对零初态和任意输入序列，完整状态与压缩状态满足

$$
 x_{n+1}=Ax_n+Bu_n,
 \qquad
 \widetilde x_{n+1}=\widetilde A\widetilde x_n+\widetilde B u_n.
$$

`D5.S3.Observer.Hankel.ProjectedExactDescent` 的第一条条件是

$$
PA=(PAJ)P.
$$

它表示下一步的投影状态只依赖当前投影状态。对任意输入序列和每个有限时刻，源码证明

$$
\boxed{
Px_n=\widetilde x_n.
}
$$

这是一条精确的投影态结论。它不需要输入有界，也不需要

$$
\|A\|<1
\qquad\text{或}\qquad
\|\widetilde A\|<1.
$$

不过它还没有说明任意读出都相同。要让目标读出也完全下降，还必须增加因子化条件

$$
C=(CJ)P.
$$

在这个附加条件下，源码的 `outputs_eq_of_descent` 给出

$$
\boxed{
Cx_n=\widetilde C\widetilde x_n
}
$$

对同一输入序列和每个时刻都成立。这里是充分条件；该声明没有把因子化判据说成必要条件。

<a id="entry-301"></a>

### 75.1 可见输出精确，不等于完整状态精确

第 74 节的两个残差在这里写成

$$
R_A=AJ-JPAJ,
\qquad
R_B=B-JPB.
$$

它们可以非零。因子化条件直接推出

$$
CR_A=0,
\qquad
CR_B=0.
$$

因此，提升后的完整状态可以沿着压缩状态没有表示的方向变化，但这些变化被当前选定的读出湮灭。这里应说“对该输出不可见”，不能在没有附加投影假设时把它称为正交投影遗漏。

源码没有要求

$$
PJ=I_W.
$$

如果另行加入这个回缩条件，则可以进一步得到

$$
PR_A=0,
\qquad
PR_B=0,
$$

从而把残差放入投影核；但这仍然不等于残差在某个给定内积下正交。没有回缩条件时，连这个投影核解释也不能直接使用。

一个两坐标例子把区别写得很清楚。取

$$
V=\mathbb R^2,
\qquad
W=U=Y=\mathbb R,
$$

并令

$$
P(x,h)=x,
\qquad
J(w)=(w,0),
\qquad
C(x,h)=x,
$$

$$
A=
\begin{pmatrix}
 a&0\\
 c&d
\end{pmatrix},
\qquad
B u=
\begin{pmatrix}
 b_1u\\
 b_2u
\end{pmatrix}.
$$

此时

$$
PA=(PAJ)P,
\qquad
C=(CJ)P.
$$

所以第一坐标的压缩递推和完整递推完全一致。但只要

$$
 c\ne0
 \qquad\text{或}\qquad
 b_2\ne0,
$$

就有

$$
R_A(w)=(0,cw),
\qquad
R_B(u)=(0,b_2u),
$$

它们不是零。可见输出仍然精确，而隐藏坐标可以持续接收来自可见坐标或外部输入的变化。

这也说明“没有隐藏到可见回流”与“没有可见到隐藏泄漏”是两个方向。仓库的 `VisibleAutonomyCriterion` 对幂等投影把可见下降等价于

$$
P T(1-P)=0
$$

等条件，同时保留一个反例：可见到隐藏的反向块仍可非零。稳定对象所需的是前一个方向不回流到任务读出，而不是完整联合状态永远停留在提升像中。

<a id="entry-302"></a>

### 75.2 与有限视界残差界的关系

第 74 节回答的是：当压缩不精确时，完整状态和目标输出的误差上界怎样随视界增长。第 75 节回答的是一个更窄的情形：当选定投影满足全局下降、且读出因子化时，目标输出误差直接为零。

因此，两节的逻辑关系是

$$
\begin{aligned}
&\text{全局下降}+\text{读出因子化}
&&\Longrightarrow
\text{指定输出的逐步精确闭合};\\
&\text{残差有界但不满足因子化}
&&\Longrightarrow
\text{使用第 74 节的有限视界误差界};\\
&\text{没有输出因子化}
&&\Longrightarrow
\text{投影态精确不保证目标读出精确}.
\end{aligned}
$$

精确输出不等于完整状态可恢复，也不等于参考系统或环境中的关联已经消失。若后续任务改变读出，或允许访问此前未读的记录，原先的因子化条件可能不再适用。对非零初态，源码中的零初态归纳还需要把压缩初态明确设为

$$
\widetilde x_0=Px_0
$$

并重新检查零时刻的输出因子化；不能把源码的零初态结论无条件推广到任意初态。

<a id="entry-303"></a>

### 75.3 对量子记录与 Zeckendorf 的边界

若量子过程先被送入一个明确的线性坐标空间，再选定一个任务读出，上述精确下降可以作为该坐标任务的模型。但它仍然是实线性算子结论，不自动给出量子态的迹距离、参考系统上的完全有界距离或 diamond 距离界；这些量需要另行指定算子空间、通道结构和范数转换。

同样，若把 Zeckendorf 合法字串映为输入坐标，两个字串被同一个 $$P$$ 或相应的 $$PB$$ 输入映射合并，只能说明它们在当前投影坐标中相同。只有当目标任务的读出满足因子化，并且后续动力学满足下降条件时，这种合并才是该任务中的精确压缩。Fibonacci 数

$$
F_{L+2}
$$

仍然只是合法标签数，不是自动的完整记忆维数，也不证明任何物理 Hamiltonian 保持该合法子空间。

所以，对“多少约束足以形成稳定经典现实”的更细回答是：首先要求当前记录对指定动力学形成可见下降；然后要求真正关心的读出因子化；只有在这两条失败时，才需要用第 74 节的残差、视界和误差容限计算还要保留多少历史。

本节复用 `ProjectedExactDescent` 与 `VisibleAutonomyCriterion` 的精确下降结果，并把它们与第 74 节的残差界连接起来。它没有把可见任务的精确闭合提升为全态恢复、量子通道等价或唯一的经典现实。

<a id="section-76"></a>

## 76. 有限未来关系塔的终止、类预算与 Zeckendorf 标签边界

第 75 节说明了一个选定读出何时可以由压缩状态精确产生。下一步要问的是：需要观察多少个未来时刻，才足以确定这个任务的全部未来响应？对有限状态载体，仓库已有一个不依赖收缩率的答案。

设 $$X$$ 是有限状态载体，

$$
\tau:X\to X,
\qquad
q:X\to O
$$

分别是更新和当前读出。对每个有限深度 $$m$$，定义

$$
x\sim_m x'
\quad\Longleftrightarrow\quad
\forall k\le m,
\ q\bigl(\tau^{[k]}x\bigr)=q\bigl(\tau^{[k]}x'\bigr),
$$

并定义完全未来关系

$$
 x\sim_\infty x'
 \quad\Longleftrightarrow\quad
 \forall k,
 \ q\bigl(\tau^{[k]}x\bigr)=q\bigl(\tau^{[k]}x'\bigr).
$$

这里的 $$\tau^{[k]}$$ 表示迭代 $$k$$ 次。源码中的 `finiteFutureRelation` 和 `infiniteFutureRelation` 正是这两种关系。记

$$
R_m=\sim_m,
\qquad
R_\infty=\sim_\infty,
$$

并记相应商类数为

$$
C_m=\lvert X/R_m\rvert,
\qquad
C_\infty=\lvert X/R_\infty\rvert.
$$

<a id="entry-305"></a>

### 76.1 相邻稳定已经足够确定全部未来

`FiniteEquivalenceDescent` 给出有限未来关系的递归

$$
R_0=\ker q,
$$

$$
R_{m+1}
=
\left\{(x,x')\in R_0:
(\tau x,\tau x')\in R_m\right\},
$$

以及有限交表示

$$
R_m
=
\bigcap_{0\le k\le m}
\left\{(x,x'):
q\bigl(\tau^{[k]}x\bigr)=q\bigl(\tau^{[k]}x'\bigr)
\right\}.
$$

因此关系塔只能变细，商类数只能增加：

$$
C_m\le C_{m+1}.
$$

`FiniteStabilityClassBound` 定义最小相邻稳定深度

$$
 d=\min\left\{m:R_m=R_{m+1}\right\}.
$$

它证明

$$
\boxed{
R_d=R_{d+1}=R_\infty.
}
$$

并且对任意满足

$$
R_n=R_{n+1}
$$

的 $$n$$，都有

$$
 d\le n.
$$

所以在有限载体上，“再看一个时刻没有产生新区分”已经足以推出全部未来读出相同。这个结论不需要范数收缩、谱隙、输入振幅界或量子通道结构；它是有限关系塔的组合稳定性。它也不是说任意系统都有一个与任务无关的稳定深度：$$d$$ 依赖更新 $$\tau$$ 和读出 $$q$$。

<a id="entry-306"></a>

### 76.2 稳定深度消耗的是商类预算

初始类数不是状态数本身，而是当前读出能够区分的商类数：

$$
C_0
=
\left\lvert X/\ker q\right\rvert
=
\left\lvert\operatorname{range}q\right\rvert.
$$

完全未来类数为 $$C_\infty$$。在源码的自然数减法语境下，`finite_stability_class_bound` 给出两段类预算

$$
\boxed{
 d\le C_\infty-C_0,
}
$$

以及

$$
\boxed{
 C_\infty-C_0
 \le
 \lvert X\rvert-C_0.
}
$$

这表示每次关系塔严格细化，都必须消耗至少一个新的商类；它不是说每一步一定恰好增加一个类，也不是最小线性预测维数定理。若 $$q$$ 满射到有限字母表 $$O$$，则

$$
C_0=\lvert O\rvert,
$$

从而得到

$$
 d\le C_\infty-\lvert O\rvert
 \le
 \lvert X\rvert-\lvert O\rvert.
$$

更一般地，若初始关系不是当前读出的核，而是任意有限载体上的 Setoid $$R$$，`finite_equivalence_descent_and_stability_bound` 给出相应的形式

$$
 d\le C_\infty-\lvert Y/R\rvert
 \le
 \lvert Y\rvert-\lvert Y/R\rvert.
$$

所以“需要保留多少历史”在这个有限确定性模型中首先表现为一个商类预算：不是保存每条历史词，而是继续细分那些仍会在未来读出中分开的类。

<a id="entry-307"></a>

### 76.3 Zeckendorf 标签只提供载体大小

取长度为 $$L$$、禁止相邻两个 $$1$$ 的合法字串集合

$$
\mathcal W_L
=
\left\{w\in\{0,1\}^L:
 w_jw_{j+1}=0\right\}.
$$

其合法构型数为

$$
\lvert\mathcal W_L\rvert=F_{L+2}.
$$

只有在更新和读出真的定义在同一个有限载体

$$
\tau:\mathcal W_L\to\mathcal W_L,
\qquad
q:\mathcal W_L\to O
$$

上时，才可以把上一节的类预算代入为

$$
 d\le C_\infty-C_0
 \le
 F_{L+2}-C_0.
$$

若 $$q$$ 满射到 $$O$$，则右侧可写成

$$
 d\le C_\infty-\lvert O\rvert
 \le
 F_{L+2}-\lvert O\rvert.
$$

这只是把有限载体大小代入稳定深度上界。它不把 Fibonacci 数自动变成预测维数。反例很直接：若 $$q$$ 在 $$\mathcal W_L$$ 上单射，则

$$
C_0=F_{L+2},
\qquad
 d=0,
$$

但载体仍有 $$F_{L+2}$$ 个状态。相反，若所有未来读出都相同，则

$$
C_\infty=C_0=1,
\qquad
 d=0,
$$

即使合法标签很多，也不需要更深的未来窗口来区分任务响应。

因此应分开报告三种量：

$$
\boxed{
\text{合法标签载体大小 }F_{L+2},
\qquad
\text{完全未来商类数 }C_\infty,
\qquad
\text{稳定深度 }d.
}
$$

Hankel 预测维数还取决于未来响应的线性秩，量子模型则可能需要算符空间、相位方向、可访问记录和参考系统。它们都不能仅由 $$F_{L+2}$$ 的离散计数推出。即使有限未来商已经稳定，也只说明指定经典更新和读出上的确定性响应已经闭合；它不自动证明密度算符相等、迹距离为零、diamond 距离为零或某个物理 Hamiltonian 保持合法 Zeckendorf 子空间。

第 76 节把“稳定经典接口”进一步拆成了三个可测层次：载体允许哪些合法构型，完全未来还能区分多少类，以及需要看到多深才达到全部未来等价。只有在额外证明编码、更新、读出和预测实现之间的同构时，才可以把其中两个量合并；一般情况下，Fibonacci 标签数只是适用载体的大小，而不是世界必须保留的历史长度。

本节复用 `FiniteEquivalenceDescent`、`FiniteStabilityClassBound` 和 `StableDepthCardinalityBounds` 的既有声明；它们适用于有限确定性更新与读出关系。将这套关系塔解释为量子通道的过程记忆，需要另行给出量子状态空间、仪器协议和距离转换。

<a id="section-77"></a>

## 77. 量子任务的可见商、序列核与不可见物理状态

第 62 节已经给出顺序词效果的正交残差，第 59 节已经给出目标可见性的充分性与失败见证。第 75 节则把状态坐标上的投影下降接到输出因子化，第 76 节把有限确定性载体上的未来关系塔接到稳定深度。本节只做它们之间的接口：说明量子任务中的“同一个对象”应当由允许词的统计签名定义，并列出把这个签名接成动力学商时必须补上的条件。

<a id="entry-309"></a>

### 77.1 允许词的量子签名

固定有限矩阵维数 $$d$$、字母表 $$\mathsf A$$、允许词族

$$
\mathcal A\subseteq \operatorname{List}(\mathsf A),
$$

以及每个字母对应的 Heisenberg 线性作用

$$
\mathsf I_a:
\operatorname{Herm}_d
\longrightarrow
\operatorname{Herm}_d.
$$

令 $$E_w$$ 表示仓库 `sequentialWordEffect` 对词 $$w$$ 产生的 Hermitian effect。定义允许词的可见空间、不可见残差和统计签名：

$$
V_{\mathcal A}
=
\operatorname{span}_{\mathbb R}
\{E_w:w\in\mathcal A\},
$$

$$
K_{\mathcal A}=V_{\mathcal A}^{\perp},
$$

$$
\Sigma_{\mathcal A}(s)
=
\bigl(
\langle s,E_w\rangle_{\mathbb R}
\bigr)_{w\in\mathcal A}.
$$

这里的内积是 Hermitian 空间上的实内积；它只记录所选词效果的实线性响应。它不是完整密度矩阵，也不是自动包含参考系统或环境的联合状态。

`unified_sequential_kernel` 给出精确等价：

$$
\boxed{
\Sigma_{\mathcal A}(s)
=
\Sigma_{\mathcal A}(s')
\quad\Longleftrightarrow\quad
s-s'\in K_{\mathcal A}.
}
$$

因此，量子任务中的当前对象应先定义为签名的纤维，而不是把所有物理态直接认作同一个点。若增加允许词族

$$
\mathcal A_H\subseteq\mathcal A_{H+1},
$$

则

$$
V_{\mathcal A_H}
\subseteq
V_{\mathcal A_{H+1}},
\qquad
K_{\mathcal A_{H+1}}
\subseteq
K_{\mathcal A_H}.
$$

这是第 76 节未来关系塔

$$
R_{H+1}\subseteq R_H
$$

的线性量子对应：观察视界扩大时，允许区分的方向增加，不可见残差减少。这里得到的是子空间包含关系，不能直接改写成有限商类数；全体密度态是连续集合，不能套用有限载体的基数界。

<a id="entry-310"></a>

### 77.2 目标预测的充分性与不可见见证

对一族实际效应 $$E_i$$，定义含单位方向的可见空间

$$
V
=
\operatorname{span}_{\mathbb R}
\bigl(\{I\}\cup\{E_i\}_i\bigr).
$$

单位方向必须显式加入，因为密度态的迹已经固定；没有它，效应签名不能自动控制标量部分。

这里的 $$E_i$$ 必须先满足源码中的物理效应条件：它们是 Hermitian、正半定，且 $$I-E_i$$ 也正半定。`target_prediction_sufficiency` 的第一半可表述为：若目标算子子空间 $$T$$ 满足

$$
T\subseteq V,
$$

那么两个密度态对全部 $$E_i$$ 的 trace 读数相同，就对每个 $$A\in T$$ 给出相同的目标期望。对 Hermitian 矩阵，仓库中的实内积与 trace 公式通过实部对应；该对应需要在具体有限维载体中明确，不能把两种配对无条件混写。

第二半给出相反方向的物理见证。若

$$
A\notin V,
$$

则存在非零 Hermitian 方向 $$D\in V^{\perp}$$、某个 $$\varepsilon>0$$ 以及两个合法密度态

$$
\rho_{\pm}
=
\frac{I}{d}\pm\varepsilon D
$$

使得对每个已选效应 $$E_i$$，

$$
\operatorname{tr}(\rho_+E_i)
=
\operatorname{tr}(\rho_-E_i),
$$

但目标读数满足

$$
\operatorname{tr}(\rho_+A)
-
\operatorname{tr}(\rho_-A)
=
2\varepsilon\operatorname{tr}(DA)
\ne0.
$$

这说明当前签名对该目标并不充分。它是一个存在性见证：源码只保证某个正 $$\varepsilon$$ 存在，不给出统一的数值下界；结论也不是迹距离或 diamond 距离下界。

若目标是第 $$n$$ 步的效应 $$B$$，应先把 Heisenberg 回拉

$$
A=(\Phi^*)^n(B)
$$

放入目标空间，再检查 $$A\in V$$。当前读出空间只含 $$B$$ 而不含其回拉，并不能推出当前签名足以预测未来的 $$B$$ 读数。

<a id="entry-311"></a>

### 77.3 从可见空间到动力学下降的附加条件

不能把 effect 空间 $$V$$ 与状态空间上的投影自动视为同一个算子。前者在 Heisenberg 的 Hermitian 算子空间，后者在 Schrödinger 状态坐标；需要有限维 Hilbert--Schmidt 对偶识别、明确的 adjoint，以及一个真正幂等的状态投影 $$P_H$$。

在这些额外结构已经给定后，若 Schrödinger 作用为 $$T_a$$，并且其 Hilbert--Schmidt 对偶满足

$$
T_a^*=\mathsf I_a,
$$

再假设允许所有长度不超过 $$H$$ 的词，并且该词空间已经稳定：

$$
V_H=V_{H+1},
$$

则对任意 $$k\in V_H^{\perp}$$ 和 $$v\in V_H$$，

$$
\langle T_a k,v\rangle
=
\langle k,T_a^*v\rangle
=0.
$$

所以

$$
T_a(V_H^{\perp})
\subseteq
V_H^{\perp},
$$

等价地，若 $$P_H$$ 是 $$V_H$$ 的正交投影，则

$$
P_HT_a(I-P_H)=0.
$$

这是 `VisibleAutonomyCriterion` 所需的 hidden-to-visible 不泄漏条件。由它可得到可见递推的因子化；再加上第 75 节 `ProjectedExactDescent` 的投影动力学条件，才可对任意输入历时推出

$$
P_Hx_n=\widetilde x_n
$$

以及在输出因子化条件下的

$$
Cx_n=\widetilde C\widetilde x_n.
$$

这里必须保留三条限制：没有 $$P_H^2=P_H$$，不能称为投影下降；没有 state/effect 对偶与 adjoint，不能从 effect span 推出状态不变性；没有量子正性、迹保持和通道假设，这些等式仍只是线性系统结论。

若 $$V_H=V_{H+1}$$ 只是在任意集合中偶然相等，而允许词族没有前缀闭合性，则不能推出更长词仍在 $$V_H$$。永久稳定需要词族对前缀扩展闭合，或另行证明全部后续 Heisenberg 效果仍落在该空间。

<a id="entry-312"></a>

### 77.4 何时能接回第 76 节的有限商预算

若选定一个有限物理状态样本

$$
X\subseteq\operatorname{DensityState},
$$

有确定更新 $$\tau:X\to X$$，并且第 $$k$$ 步的输出正好等于指定签名坐标，那么可定义

$$
x\sim_Hx'
\quad\Longleftrightarrow\quad
\Sigma_H(x)=\Sigma_H(x').
$$

这时才能把 $$x\sim_Hx'$$ 与第 76 节的 $$R_H$$ 对齐，并使用有限商类数和稳定深度界。对于包含多条分支或多字母选择的词族，不能直接把它写成单一的 $$q(\tau^{[k]}x)$$；必须固定字母调度，或把分支与历史并入扩大的确定状态。若状态空间是全部密度态，集合通常是连续的，应该报告

$$
\dim V_H,
\qquad
\dim K_H,
$$

或 centered trace-zero 塔，而不是报告 $$|X/R_H|$$ 的有限数值。

同样，Zeckendorf 合法字串的数量

$$
|\mathcal W_L|=F_{L+2}
$$

只在明确指定

$$
w\longmapsto s_w,
\qquad
\tau:\mathcal W_L\to\mathcal W_L,
\qquad
q:\mathcal W_L\to O
$$

以及实际的序列仪器后，才是一个合法的有限载体大小。它不能自动等于

$$
\dim V_H,
\qquad
d^2-1,
$$

也不能自动等于量子记忆维数、Hankel 秩或 Hamiltonian 不变子空间的维数。Zeckendorf 负责组织合法标签；effect、仪器和更新负责决定哪些标签差异进入可见响应。

<a id="entry-313"></a>

### 77.5 本节对“稳定经典现实”的精确含义

在这条接口上，“稳定的经典现实”可以写成三个同时满足的任务条件：

$$
\boxed{
\text{签名商定义当前可区分对象}
\;+
\text{可见空间对目标足够}
\;+
\text{隐藏方向在指定动力学下不回流}
}
$$

第一项由 $$\Sigma_H$$ 和 $$K_H$$ 给出；第二项由目标是否落在含单位方向的 effect span 决定；第三项需要真正的投影、对偶和下降条件。三项中任何一项缺失，当前读数都不能单独承担“以后仍然如此”的含义。

因此，“要保留多少历史”没有一个脱离任务的整数答案。对有限 Zeckendorf 载体，先报告合法构型数量；对给定词族，再报告可见 span 与正交残差；对给定更新，最后检验目标回拉是否留在该 span，以及隐藏到可见的耦合是否为零。只有这些对象、操作和误差范围都被指定后，才可以说某一层记录已经足以支撑稳定的经典预测。

本节复用 `unified_sequential_kernel`、`target_prediction_sufficiency`、`finite_time_observer_monotonicity` 和 `incomplete_observer_physical_counterexample` 的现有冻结声明，并把它们接到第 75、76 节的下降与有限关系塔。上述声明均在标准项目公理闭包下通过定向构建；本节没有新增 Lean 定理，也没有把线性 effect 结果提升为 CPTP、trace-distance 或 diamond 等价。

<a id="entry-314"></a>

## 追加锚（新终端）

<a id="section-78"></a>

## 78. 精确预测闭合与后揭测量的共同经典存储障碍

<a id="entry-316"></a>

### 78.1 序列统计、目标充分性与下降的适用条件

**定义 78.1（按设置归一化的序列任务）。** 设 $d\ge1$，$\operatorname{Herm}_d$ 为 $d$ 阶 Hermitian 矩阵的实向量空间，内积为 $\langle A,B\rangle=\operatorname{tr}(AB)$。物理输入取密度矩阵 $\rho\ge0$、$\operatorname{tr}\rho=1$。对每个可选设置 $b$，分别给定有限个复线性、完全正且迹不增的分支 $\mathcal J_{b,s}$，并要求

$$
\sum_s\mathcal J_{b,s}\quad\text{对每个固定的 }b\text{ 都迹保持。}
$$

令 $\mathcal J_{b,s}^*$ 为 Hilbert--Schmidt 伴随。按时间顺序记录词 $w=((b_1,s_1),\ldots,(b_n,s_n))$，定义

$$
E_\varnothing=I_d,\qquad
E_w=\mathcal J_{b_1,s_1}^*\cdots\mathcal J_{b_n,s_n}^*(I_d),
\qquad
p_\rho(w)=\operatorname{tr}(\rho E_w).
$$

设置是外部选择；若设置也随机化，其概率由另行指定的归一化策略给出，不把不同设置的全部分支直接合成一个仪器。

**命题 78.2（第 77 节线性接口的物理限定）。** 第 77.1 节的签名核等价只需实 Hermitian 线性作用；把其中的响应解释为物理序列概率，须另加定义 78.1 的输入和仪器假设。第 77.2 节的目标充分性适用于 $d\ge1$ 及含单位方向的空间

$$
V=\operatorname{span}_{\mathbb R}\bigl(\{I_d\}\cup\{E_i\}_i\bigr),
\qquad 0\le E_i\le I_d.
$$

其中加入 $I_d$ 是利用已知的迹一约束，不要求额外测量单位算子；对任何标量目标 $aI_d$，期望已经恒等于 $a$。若 $A\notin V$，则有对所有 $E_i$ 同读数、对 $A$ 异读数的两个密度矩阵。

证明。Hermitian 矩阵满足

$$
\overline{\operatorname{tr}(AB)}
=\operatorname{tr}((AB)^\dagger)
=\operatorname{tr}(BA)=\operatorname{tr}(AB),
$$

故所写内积为实数。对任何实线性词效果族，所有配对相等当且仅当状态差正交于这些效果的实张成空间；这就是第 77.1 节 `unified_sequential_kernel` 的线性内容，它不包含密度输入、完全正性或归一化假设。在定义 78.1 下，分支复合把正输入送到正矩阵，其迹给出非负分支概率；对每个已经选定的设置，将该步的结果求和保持输入迹。逐步求和即得每个有限策略树的概率归一化。一般实线性作用没有这些保证，例如作用 $A\mapsto2A$ 从单位效果产生 $2I_d$，对迹一输入的响应为二。

若 $A=aI_d+\sum_i a_iE_i$，其中只有有限个 $a_i$ 非零，则

$$
\operatorname{tr}(\rho A)=a+\sum_i a_i\operatorname{tr}(\rho E_i),
$$

直接给出充分性。反向令 $D=A-\operatorname{proj}_V A$。于是 $D\ne0$、$D\perp V$、$\operatorname{tr}D=0$，且

$$
\operatorname{tr}(DA)=\operatorname{tr}(D^2)>0.
$$

取 $0<\varepsilon<1/(d\|D\|_{\rm op})$，则 $\rho_\pm=I_d/d\pm\varepsilon D$ 的最小特征值至少为 $1/d-\varepsilon\|D\|_{\rm op}>0$，迹为一。正交性给出相同的 $E_i$ 读数，而两态的 $A$ 读数相差 $2\varepsilon\operatorname{tr}(D^2)>0$。这也是第 77.2 节 `target_prediction_sufficiency` 中正维数假设和单位方向的作用；原节关于标量部分的说明应以迹一约束所给的上述公式为准。证毕。

**命题 78.3（全自由词稳定性与确定下降的限定）。** 对任意实线性生成作用 $(L_a)_a$，令 $E_\varnothing=I_d$、$E_{aw}=L_aE_w$，并用全部长度不超过 $H$ 的词定义 $V_H=\operatorname{span}_{\mathbb R}\{E_w:|w|\le H\}$。若 $V_H=V_{H+1}$，则每个生成作用都保持 $V_H$，且 $V_m=V_H$ 对所有 $m\ge H$ 成立。任意前缀闭合的允许子集，或把词族固定截断后得到的相邻相等，不具有这一推论。

第 77.3 节引用的受驱下降等式具有如下精确形式。给定线性映射 $A,B,P,J,C$，令

$$
\widetilde A=PAJ,\quad\widetilde B=PB,\quad\widetilde C=CJ,
\qquad PA=\widetilde A P,
$$

$$
x_0=0,\quad x_{n+1}=Ax_n+Bu_n,
\qquad
\widetilde x_0=0,\quad\widetilde x_{n+1}=\widetilde A\widetilde x_n+\widetilde B u_n.
$$

则 $Px_n=\widetilde x_n$；若另有 $C=\widetilde C P$，则 $Cx_n=\widetilde C\widetilde x_n$。这些是零初态的受驱响应等式；任意密度制备并非它们的初态假设。

证明。对 $|w|\le H$，有 $L_aE_w=E_{aw}\in V_{H+1}=V_H$。线性性把这个包含推广到整个 $V_H$，再对词长归纳，所有词效果都在 $V_H$ 中。与 $V_H\subseteq V_m$ 合用即得永久稳定。这是第 77.3 节所涉及的 `sequential_visible_space_once_stable_permanently` 的生成元不变性论证；不需要在全自由词假设之外再加一条前缀条件。若 $T_a^*=L_a$，同一论证还给出

$$
\langle T_ak,v\rangle=\langle k,L_av\rangle=0
\quad(k\in V_H^\perp,\ v\in V_H),
$$

故 $T_a(V_H^\perp)\subseteq V_H^\perp$。对于删去某些扩展的允许子集，上述 $aw$ 未必被允许，不能作这一步推导；命题 78.5 给出一个物理分支反例。

受驱响应在 $n=0$ 时满足 $Px_0=0=\widetilde x_0$。若第 $n$ 步等式成立，则

$$
Px_{n+1}=PAx_n+PBu_n
=\widetilde A\widetilde x_n+\widetilde B u_n
=\widetilde x_{n+1}.
$$

输出等式由 $C=\widetilde C P$ 代入。这正是 `ProjectedExactDescent` 中 `projectedState_eq_of_descent` 与 `outputs_eq_of_descent` 所用的零初态 `drivenState` 和全局下降条件。对另行指定的非零初态，相同归纳还需要 $\widetilde x_0=Px_0$；它不是任意两个初态之间的结论。证毕。

第 77.4 节接用第 76 节的有限商预算时，增广后的载体必须实际为有限集，更新必须是该集上的同一个时间齐次确定映射。把任意长历史、无界时钟或随机结果添作坐标，本身不满足这一假设：前两者可以产生无限多坐标值，后者仍需给定确定的更新规则。只有明确构造出有限且封闭的确定增广系统，才可使用第 76 节的有限类数和稳定深度界。第 77.5 节的三项条件在这些限定内给出所选任务的精确预测接口；它们不能作为“稳定经典现实”或一个可物理取得的共同经典记录的充分条件。以下同一模型同时满足预测闭合与共同经典存储不可能性。

<a id="entry-317"></a>

### 78.2 两个 Lüders 设置的精确可见闭合

**定义 78.4（量子比特任务及未归一化坐标）。** 在计算基 $|0\rangle=(1,0)^T$、$|1\rangle=(0,1)^T$ 中取

$$
I=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

对 $b\in\{X,Z\}$、$s\in\{+1,-1\}$，定义

$$
P_s^b=\frac{I+sb}{2},\qquad
\mathcal J_{b,s}(A)=P_s^bAP_s^b.
$$

任意 Hermitian $A$ 唯一写为

$$
A=\frac{tI+xX+yY+zZ}{2},
\qquad (t,x,y,z)\in\mathbb R^4,
\qquad t=\operatorname{tr}A.
$$

允许的操作只有这些分支；有限策略可以依赖已记录的设置和结果选择下一设置或停止，并可使用与输入独立的经典随机数。策略不插入任意旋转、不补充新的量子输入，也不测量外部参考系统。

**命题 78.5（分支递推与所有有限词的闭合）。** 每个固定 $b$ 的二分支族是 Lüders 仪器。分支在可见坐标 $(t,x,z)$ 上的作用恰为

$$
\mathcal J_{X,s}:\ (t,x,z)\longmapsto
\left(\frac{t+sx}{2},\frac{st+x}{2},0\right),
$$

$$
\mathcal J_{Z,s}:\ (t,x,z)\longmapsto
\left(\frac{t+sz}{2},0,\frac{st+z}{2}\right).
$$

密度输入恰满足 $t=1$、$x^2+y^2+z^2\le1$。对全部长度不超过 $H$ 的词效果，其实可见空间与稳定正交残差为

$$
V_0=\operatorname{span}_{\mathbb R}\{I\},\qquad
V_H=V=\operatorname{span}_{\mathbb R}\{I,X,Z\}\quad(H\ge1),
\qquad K=V^\perp=\operatorname{span}_{\mathbb R}\{Y\}.
$$

这些递推精确决定定义 78.4 内全部有限策略的记录概率。

证明。矩阵相乘给出 $X^2=Y^2=Z^2=I$，不同 Pauli 矩阵反对易，且 $I,X,Y,Z$ 两两 Hilbert--Schmidt 正交、平方范数均为二。这证明坐标表示的唯一性。无迹部分满足

$$
(xX+yY+zZ)^2=(x^2+y^2+z^2)I,
$$

故 $A$ 的特征值为 $(t\pm\sqrt{x^2+y^2+z^2})/2$，得到所述密度条件。

每个 $P_s^b$ 都是迹一的正交投影，且 $P_+^b+P_-^b=I$。若 $P=|v\rangle\langle v|$、$\|v\|=1$，则对任意矩阵 $A$，

$$
PAP=\langle v,Av\rangle P=\operatorname{tr}(AP)P.
$$

因此

$$
\mathcal J_{X,s}(A)=\frac{t+sx}{2}P_s^X,
\qquad
\mathcal J_{Z,s}(A)=\frac{t+sz}{2}P_s^Z,
$$

展开投影即得坐标递推，并且分支后的 $y$ 坐标为零。对任意辅助空间和任意正矩阵 $B$，

$$
(\mathcal J_{b,s}\otimes\mathrm{id})(B)
=(P_s^b\otimes I)B(P_s^b\otimes I)\ge0,
$$

所以分支完全正。对 $A\ge0$，其迹为 $\operatorname{tr}(AP_s^b)\in[0,\operatorname{tr}A]$；固定 $b$ 后对 $s$ 求和等于 $\operatorname{tr}A$。这证明每个设置的仪器性质。反之，将两个设置的四个分支不加权相加，输出迹为 $2\operatorname{tr}A$，并非归一化仪器。

这些分支关于 Hilbert--Schmidt 配对自伴随。对非空词 $w=(a_1,\ldots,a_n)$，写 $P_j=P_{s_j}^{b_j}$。秩一压缩逐次给出

$$
E_w=
\left(\prod_{j=1}^{n-1}\operatorname{tr}(P_jP_{j+1})\right)P_1,
$$

其中空积为一。事实上 $E_{(a_n)}=P_n$；若后缀效果为 $cP_{j+1}$，则 $P_j(cP_{j+1})P_j=c\operatorname{tr}(P_jP_{j+1})P_j$，倒序归纳即得公式。同一设置的相邻投影重叠为 $\delta_{s_j,s_{j+1}}$，不同设置的重叠为 $1/2$，因为

$$
\operatorname{tr}(P_s^bP_u^c)
=\frac{1+su\,\delta_{b,c}}2.
$$

故所有词效果在 $V$ 内，长度一的效果已通过 $P_+^X-P_-^X=X$、$P_+^Z-P_-^Z=Z$ 张成 $V$，空词给出 $I$。Pauli 正交性给出 $K$。特别地，每个分支都消去 $Y$，所以隐藏方向不会回流到可见坐标。

这也提供命题 78.3 所需的子集反例：只允许全部 $X$ 设置的词，是整个 $X,Z$ 字母表中的前缀闭合子集；其长度一及长度二的可见空间均为 $\operatorname{span}_{\mathbb R}\{I,X\}$，但 $\mathcal J_{Z,+}^*(I)=(I+Z)/2$ 不在其中。只保留这些词的长度一截断，仍有同样的相邻相等和失败。

最后，对一条终止记录 $h$，令 $q_h$ 是沿记录各次设置选择及终止决定的策略概率的乘积；确定策略时它等于零或一。因策略只依赖已有记录，$q_h$ 不依赖隐藏的输入坐标。该记录的概率是 $q_h\operatorname{tr}(\rho E_h)$，而各节点的分支迹按已证的递推求出。有限树上的求和及停止记录均因此精确确定。全程保存未归一化的 $t$；零迹的正分支必为零矩阵，继续递推仍为零，不在零概率记录上除以 $t$。证毕。

这里的精确经典数值预测以输入的精确 $x,z$ 已作为数值资料给定为前提；它没有提供从一份未知量子态中取得这两个数值的测量方法。

<a id="entry-318"></a>

### 78.3 可见正投影的完全正性障碍

**命题 78.6（正而非完全正的预测投影）。** 在全复矩阵空间 $M_2(\mathbb C)$ 上，以计算基转置定义复线性映射

$$
\Pi(A)=\frac{A+A^T}{2}.
$$

它正、迹保持、保单位且幂等。在实 Hermitian 空间上，它是到 $V$ 的 Hilbert--Schmidt 正交投影；在全复矩阵空间上的像则为 $\operatorname{span}_{\mathbb C}\{I,X,Z\}$。它保持定义 78.4 的全部有限策略统计，却不是完全正映射。

证明。$I^T=I$、$X^T=X$、$Y^T=-Y$、$Z^T=Z$，故 $\Pi$ 恰好删去 $Y$ 坐标。实 Hermitian 限制上的正交性由 Pauli 正交基给出；一般复矩阵也有唯一的复 Pauli 展开，因此其复像是所写复张成空间，不能与实空间 $V$ 等同。

若 $A\ge0$，则 $A^T=\overline A$，且对任意复向量 $v$，

$$
v^\dagger A^T v
=\overline{\overline v^{\,\dagger}A\overline v}\ge0.
$$

右边被共轭的数本来就是非负实数，所以转置保持正性，平均映射 $\Pi$ 也正。记转置作用为 $T(A)=A^T$；它保持迹和单位，且 $T^2=\mathrm{id}$，因此

$$
\operatorname{tr}\Pi(A)=\operatorname{tr}A,\qquad
\Pi(I)=I,\qquad
\Pi^2=\tfrac14(\mathrm{id}+2T+T^2)=\Pi.
$$

又因 $A-\Pi(A)$ 在 Hermitian 空间上属于 $K$，命题 78.5 的所有词效果对该差配对为零，所有允许策略统计都被保持。

令

$$
|\Phi\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2},\quad
\rho_\Phi=|\Phi\rangle\langle\Phi|,\quad
F=\sum_{i,j=0}^1|ij\rangle\langle ji|.
$$

由 $\rho_\Phi=\tfrac12\sum_{i,j}|i\rangle\langle j|\otimes|i\rangle\langle j|$ 得到

$$
(T\otimes\mathrm{id})(\rho_\Phi)=\frac F2,\qquad
(\Pi\otimes\mathrm{id})(\rho_\Phi)=\frac{\rho_\Phi}{2}+\frac F4.
$$

归一化反对称向量 $|\Psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$ 与 $|\Phi\rangle$ 正交，并满足 $F|\Psi^-\rangle=-|\Psi^-\rangle$，所以

$$
\langle\Psi^-|(\Pi\otimes\mathrm{id})(\rho_\Phi)|\Psi^-\rangle=-\frac14.
$$

因此 $\Pi\otimes\mathrm{id}$ 不保持正性，$\Pi$ 非完全正。完全正性、Choi 正性及 Kraus 表示的标准等价见 John Watrous，*The Theory of Quantum Information*，Cambridge University Press，2018，[Theorem 2.22](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)；这里的归一化 Bell 见证直接算出了负期望。证毕。

这个见证排除的是把 $\Pi$ 本身当作量子通道；它没有排除其他编码。参考系统在这里用于检验完全正性，并未成为定义 78.4 的可查询对象。任意共同经典编码的障碍由下一命题单独证明。

<a id="entry-319"></a>

### 78.4 后揭设置前不存在精确共同经典存储

**定义 78.7（单份输入的后揭二元查询）。** 存储者收到一份未知量子比特密度矩阵 $\rho$，在请求的设置 $b\in\{X,Z\}$ 揭示之前，固定使用任意有限父 POVM

$$
M_\lambda\ge0,\qquad\sum_{\lambda\in\Lambda}M_\lambda=I,
$$

只保留经典结果 $\lambda$。设置揭示后只允许归一化随机译码

$$
k_b(s\mid\lambda)\ge0,\qquad\sum_{s=\pm1}k_b(s\mid\lambda)=1.
$$

其有效效应与输出概率为

$$
E_s^b=\sum_\lambda k_b(s\mid\lambda)M_\lambda,
\qquad p_{M,k}(s\mid\rho,b)=\operatorname{tr}(\rho E_s^b).
$$

同一 $M,k$ 必须对所有密度输入和两个设置适用。任务只有一个后揭查询，不允许保留量子输出、再次取得输入副本或依输入改变存储方案。

**命题 78.8（任意有限父 POVM 的精确存储不可能性）。** 定义 78.7 中不存在满足

$$
\operatorname{tr}(\rho E_s^b)=\operatorname{tr}(\rho P_s^b)
\quad\text{对全部 }\rho,b,s
$$

的存储和译码方案。

证明。对任意这样的方案，定义四个正效应

$$
G_{su}=\sum_\lambda k_X(s\mid\lambda)k_Z(u\mid\lambda)M_\lambda.
$$

由两个译码核的归一化，

$$
\sum_{s,u}G_{su}=I,\qquad
\sum_uG_{su}=E_s^X,\qquad
\sum_sG_{su}=E_u^Z.
$$

这是构造联合边缘的数学乘积耦合，不要求同时运行两次实际查询。若假设中的全部密度态读数相等，则 $E_s^b=P_s^b$：Hermitian 差若非零，其某个非零特征值的单位本征向量所定义的纯态就给出非零读数，矛盾。因此

$$
0\le G_{su}\le P_s^X,\qquad0\le G_{su}\le P_u^Z.
$$

沿用第 38 节的正效应支撑论证：若 $0\le G\le P$ 且 $P$ 是正交投影，对 $v\in\ker P$ 有

$$
0\le\langle v,Gv\rangle\le\langle v,Pv\rangle=0.
$$

因 $\langle v,Gv\rangle=\|G^{1/2}v\|^2$，有 $Gv=0$。再由自伴随性，$\operatorname{ran}G\subseteq(\ker P)^\perp=\operatorname{ran}P$。这里 $P_s^X$ 的值域由 $(|0\rangle+s|1\rangle)/\sqrt2$ 张成，而 $P_u^Z$ 的值域由 $|0\rangle$ 或 $|1\rangle$ 张成；它们的交为零。故每个 $G_{su}=0$，与 $\sum_{s,u}G_{su}=I$ 矛盾。

这一支撑原则也是 Heinosaari、Reitzner、Stano，*Notes on Joint Measurability of Quantum Observables*，[arXiv:0811.0783，附录 Proposition 8](https://arxiv.org/abs/0811.0783) 中处理任意联合 POVM 的关键：一个锐边缘已强制相容性。此处直接使用值域交为零的量子比特特例，不以“联合测量本身也是锐测量”为前提。证毕。

**命题 78.9（首次实际查询后的有限标签模拟）。** 若第一次设置已经揭示并实际执行其 Lüders 测量，则每个正概率结果 $(b,s)$ 后的归一化状态恰为 $P_s^b$。此后定义 78.4 的任意有限策略，可把量子状态替换为四个标签 $(X,+1),(X,-1),(Z,+1),(Z,-1)$ 并作经典随机更新，精确模拟后续记录。策略控制仍可使用已记录的完整经典历史；四个标签只替代量子状态，不声称压缩策略自身的记忆。

证明。秩一压缩给出 $\mathcal J_{b,s}(\rho)=\operatorname{tr}(\rho P_s^b)P_s^b$；只在该系数为正时归一化。若当前标签为 $(b,s)$，下一设置为 $c$，结果 $u$ 的概率为

$$
\operatorname{tr}(P_s^bP_u^c)=\frac{1+su\,\delta_{b,c}}2,
$$

发生后把标签改为 $(c,u)$。与已记录历史所决定的策略选择结合，对步骤数归纳即得整个后续记录分布。标签是在首次实际查询之后取得，不是定义 78.7 要求的设置揭示之前的共同存储。证毕。

<a id="entry-320"></a>

### 78.5 共同经典存储的精确极小极大代价

**定理 78.10（后揭 $X,Z$ 查询的二元总变差最优值）。** 对定义 78.7 的任意有限父 POVM 和随机译码，定义

$$
e(M,k)=\sup_{\rho,\,b\in\{X,Z\}}
\frac12\sum_{s=\pm1}
\left|\operatorname{tr}(\rho P_s^b)-\operatorname{tr}(\rho E_s^b)\right|.
$$

则在所有这类方案上，

$$
\inf_{M,k}e(M,k)=e_*=
\frac{1-1/\sqrt2}{2},
$$

且下确界由一个四结果 POVM 达到。下界不要求边缘无偏，也不预设父 POVM 的结果数。

证明。固定任意方案，记 $e=e(M,k)$，并使用命题 78.8 的乘积耦合 $G_{su}$。取四个等概率测试输入 $P_s^X,P_u^Z$，在存储后揭示其所属设置。在输入 $P_s^b$ 上，理想二元输出确定为 $s$，故总变差恰为 $1-\operatorname{tr}(P_s^bE_s^b)$。因此每个正确标签概率至少为 $1-e$，平均成功率满足

$$
\begin{aligned}
1-e\le S
&=\frac14\sum_s\operatorname{tr}(P_s^XE_s^X)
+\frac14\sum_u\operatorname{tr}(P_u^ZE_u^Z)\\
&=\sum_{s,u}\operatorname{tr}(G_{su}R_{su}),
\qquad R_{su}=\frac{P_s^X+P_u^Z}{4}.
\end{aligned}
$$

采用第 40 节的谱奖励上界方法。因为 $XZ+ZX=0$，

$$
(sX+uZ)^2=2I,\qquad
R_{su}=\frac I4+\frac{sX+uZ}{8}.
$$

$sX+uZ$ 无迹、Hermitian，故特征值为 $\pm\sqrt2$，从而

$$
R_{su}\le cI,\qquad
c=\frac{1+1/\sqrt2}{4}.
$$

正性给出 $\operatorname{tr}(G_{su}(cI-R_{su}))\ge0$；这也可写成正矩阵 $G_{su}^{1/2}(cI-R_{su})G_{su}^{1/2}$ 的迹。因此，对所有有限父 POVM 与随机译码，

$$
S\le c\sum_{s,u}\operatorname{tr}G_{su}
=c\operatorname{tr}I=2c,
\qquad
 e\ge1-2c=e_*.
$$

为证明达到该界，取父 POVM

$$
G_{su}^{\rm opt}=\frac14\left(I+\frac{sX+uZ}{\sqrt2}\right),
\qquad s,u\in\{+1,-1\}.
$$

由同一平方恒等式，其特征值为零和 $1/2$，故各项正；对四个符号求和，非单位项相消，得到 $\sum_{s,u}G_{su}^{\rm opt}=I$。请求 $X$ 时输出 $s$，请求 $Z$ 时输出 $u$，其边缘恰为

$$
E_s^b=\frac{I+sb/\sqrt2}{2}.
$$

对任意密度输入，两个结果的概率差符号相反，故实际二元总变差为

$$
\frac12\sum_{s=\pm1}
\left|\operatorname{tr}\!\left(\rho\frac{s(1-1/\sqrt2)b}{2}\right)\right|
=e_*|\operatorname{tr}(\rho b)|\le e_*.
$$

最后一个不等式来自 $b$ 的谱为 $\{+1,-1\}$；在 $b$ 的任一本征态上取等号。因此该方案的上确界为 $e_*$，与下界相同。误差是对所有态统一有界，并非每个态都等于 $e_*$；例如 $\rho=I/2$ 时为零。证毕。

Heinosaari、Reitzner、Stano 的上述论文 Proposition 1、式 (5) 给出无偏二元量子比特效应的判据 $\|a+b\|+\|a-b\|\le2$；取两个正交方向及共同收缩系数 $\eta\ge0$，它化为 $2\sqrt2\eta\le2$，与构造中的 $\eta=1/\sqrt2$ 一致。该无偏判据并不代替上面对任意有偏译码的下界。Carmeli、Heinosaari、Toigo，*State discrimination with post-measurement information and incompatibility of quantum measurements*，[arXiv:1804.09693，§V.2，式 (27)](https://arxiv.org/abs/1804.09693) 给出两个等概率量子比特本征基的平均后测量信息成功率

$$
\frac12\left(1+\sqrt{\frac{1+|\cos\theta|}{2}}\right).
$$

在 $\theta=\pi/2$ 时，该值为 $2c=1-e_*$。本定理从四态测试得到极小极大下界，再用构造的逐态误差得到一致上界，补足平均成功率与最坏态代价之间的桥接。$e_*$ 只是在定义 78.7 资源约束下的一次后揭查询最优值，不是可见闭合缺陷、退相干速率或跨任务的普适阈值。

<a id="entry-321"></a>

### 78.6 三个 Zeckendorf 标签中的等距嵌入

**命题 78.11（合法窗口内的支撑转移及全载体可见空间）。** 沿用本卷定义 1.1 及 Zeckendorf 扩展的开放窗口约定，

$$
\mathcal W_2=\{00,01,10\},\qquad
\mathcal H_{\mathcal W_2}=\operatorname{span}_{\mathbb C}\{|00\rangle,|01\rangle,|10\rangle\}.
$$

定义等距嵌入 $U:\mathbb C^2\to\mathcal H_{\mathcal W_2}$ 为 $U|0\rangle=|00\rangle$、$U|1\rangle=|01\rangle$，并令

$$
Q=UU^\dagger=|00\rangle\langle00|+|01\rangle\langle01|,
\quad R=I_3-Q=|10\rangle\langle10|,
\quad\widehat X=UXU^\dagger,\quad\widehat Z=UZU^\dagger.
$$

每个设置 $b\in\{X,Z\}$ 使用三个投影

$$
\widehat P_s^b=\frac{Q+s\widehat b}{2}\quad(s=\pm1),
\qquad R,
$$

及相应的压缩分支 $A\mapsto\widehat P_s^b A\widehat P_s^b$、$A\mapsto RAR$。对支撑在 $Q$ 的输入，命题 78.5 的序列统计、命题 78.8 的精确存储不可能性及定理 78.10 的二元代价 $e_*$ 全部原值转移。对整个三维载体和含补空间结果的全部词族，长度至少一的实可见空间为

$$
\widehat V_H=\operatorname{span}_{\mathbb R}\{Q,R,\widehat X,\widehat Z\}
\quad(H\ge1),
$$

而长度零的空间为 $\operatorname{span}_{\mathbb R}\{I_3\}$。

证明。两位二进制词中，开放相邻约束只排除 $11$，故合法词恰为上述三个。所选基向量正交，给出 $U^\dagger U=I$、$UU^\dagger=Q$、$RU=0$。因此

$$
\widehat X^2=\widehat Z^2=Q,\qquad
\widehat X\widehat Z+\widehat Z\widehat X=0,\qquad
\widehat P_s^b=UP_s^bU^\dagger.
$$

于是 $\widehat P_+^b,\widehat P_-^b,R$ 两两正交、各自幂等、自伴随，且和为 $I_3$。命题 78.5 的单 Kraus 正性与迹求和论证逐项适用，证明每个设置分别归一化。

支撑在 $Q$ 的密度矩阵唯一为 $\widehat\rho=U\rho U^\dagger$，其中 $\rho=U^\dagger\widehat\rho U$ 是量子比特密度矩阵。直接计算

$$
\widehat P_s^b\widehat\rho\widehat P_s^b
=U(P_s^b\rho P_s^b)U^\dagger,
\qquad R\widehat\rho R=0,
\qquad
\operatorname{tr}(\widehat\rho\widehat P_s^b)
=\operatorname{tr}(\rho P_s^b).
$$

因此全部支撑内序列递推相同。若三维父 POVM 为 $(M_\lambda)_\lambda$，则 $(U^\dagger M_\lambda U)_\lambda$ 是量子比特父 POVM，保留同一译码后，在所有支撑内输入上的二元概率完全相同；故精确不可能性和 $e_*$ 下界都转移。反向把最优量子比特父 POVM 扩为 $(UG_{su}^{\rm opt}U^\dagger)_{s,u}$ 加上 $R$，并在结果 $R$ 上任选归一化二元译码。支撑内输入对 $R$ 的概率为零，故上界也原值转移。这一二元比较的输入域严格限定在 $Q$ 上。

在整个载体上，长度一的效果含 $\widehat P_\pm^X,\widehat P_\pm^Z,R$；它们的和与差给出 $Q,\widehat X,\widehat Z,R$。四者实线性独立：限制到 $Q$ 后由 $I,X,Z$ 独立性得前三个系数为零，限制到 $R$ 得最后系数为零。所有这些投影均秩一，命题 78.5 的压缩归纳仍使每个非空词效果为首个投影的标量倍数，故更长词不增加方向。空词效果 $I_3=Q+R$ 也在该空间内。这证明完整可见空间的等式，不能把它写成只有三个实方向的量子比特空间。证毕。

这里的 Zeckendorf 结构提供合法标签及一个明确的等距嵌入。仪器由所写投影指定；没有从 Fibonacci 权重推导自然能谱、实验耦合、普适几何或经典性，也没有改变支撑内的一次查询存储界。

<a id="section-79"></a>

## 79. 可见算子系统、可编码子系统与 Zeckendorf 记忆成本

<a id="entry-323"></a>

### 79.1 预测闭合不等于代数闭合

第 78 节中的 $X/Z$ 任务给出一个最小反例。其所有有限词效果都落在

$$
V_{XZ}=\operatorname{span}_{\mathbb R}\{I,X,Z\},
$$

并且 $Y$ 方向不会回流到这些读数。因而 $V_{XZ}$ 对这组仪器是预测闭合的。然而

$$
XZ=iY\notin V_{XZ}.
$$

所以 $V_{XZ}$ 不是复矩阵代数，也不是一个可以直接当作独立量子系统的乘法闭子空间。

这一区分可以写成两个不同的要求。先取一个已经固定的、单一的 Heisenberg 更新 $H$ 和初始效果族 $S$，令

$$
V_0=\operatorname{span}_{\mathbb R}(\{I\}\cup S),
\qquad
V_{n+1}=V_n+H(V_n).
$$

**预测闭合**是在某个 $N$ 后满足

$$
V_N=V_{N+1},
$$

这时已有的 `operator_system_tower_once_stable_permanently`（其前提是一个明确给定的保单位完全正 Heisenberg 映射）保证后续塔保持不变。多个设置或自适应协议需要先给出打包后的单一通道，或另证族版本；不能由该定理直接推出。**代数闭合**则要求在复化后还满足

$$
V_{\mathbb C}V_{\mathbb C}\subseteq V_{\mathbb C},
\qquad
V_{\mathbb C}^{\ast}=V_{\mathbb C}.
$$

前者保证指定实验的未来统计可由当前坐标预测；后者只说明存在一个有限维含单位的 $*$-子代数候选载体。要把它解释成独立的 $C^*$ 子系统，仍需另给编码、恢复和动力学交换图。前者不推出后者。

证明 $V_{XZ}$ 的失败只需计算 $XZ=iY$。这也解释了第 78 节正投影 $\Pi$ 的地位：它可以在实 Hermitian 读数上保持全部指定统计，却不能直接当作完全正的量子通道。若要求一个物理编码，必须额外提供完全正的嵌入、压缩和其相容的动力学；仅有线性正投影不足以完成这一步。

<a id="entry-324"></a>

### 79.2 物理编码的最小接口

设 $\mathcal H_S$ 是完整系统，$\mathcal H_R$ 是候选记忆空间。下面把一个“可独立访问的量子记忆”作为额外的强假设，定义为一对映射

$$
\iota:\mathcal B(\mathcal H_R)\longrightarrow\mathcal B(\mathcal H_S),
\qquad
\mathcal R:\mathcal B(\mathcal H_S)\longrightarrow\mathcal B(\mathcal H_R),
$$

其中 $\iota$ 要求为 Heisenberg 意义下的保单位 $*$-单同态（若只给 UCP 映射，则还须另加 complete-order embedding 假设），$\mathcal R$ 是保单位完全正映射，并满足

$$
\mathcal R\circ\iota=\operatorname{id}_{\mathcal B(\mathcal H_R)}.
$$

若只要求把完整演化商到记忆上，要求某个记忆演化 $H_R$ 满足

$$
\mathcal R\circ H=H_R\circ\mathcal R.
$$

这三条分别保证代数嵌入、Heisenberg 商的可定义性和预测闭合；它们是定义中的额外条件，不是由 operator system 自动得到的。若要求记忆内部作为完整子系统演化，还要加强为

$$
H\circ\iota=\iota\circ H_R.
$$

在 Schrödinger 对偶方向，这些 UCP 条件对应相应的 CPTP 编码与解码条件。它们比“$V$ 是一个稳定实向量空间”严格得多。

在有限维情形，若只要求任务效果而非整个矩阵代数，则可以把 $\mathcal R$ 的像限制为一个含单位的 Hermitian operator system；这正是第 77--78 节可见空间的适用范围。若要求任意后续量子操作都能在记忆内实现，则必须进一步验证乘法闭合或给出一个更大的代数载体。因而“对象”至少有两层：

$$
\text{任务对象}=\text{对指定实验闭合的 operator system},
$$

$$
\text{量子子系统}=\text{带完全正编码与回收的代数对象}.
$$

把第一层直接称为第二层，会把预测充分性误报成物理可实现性。

<a id="entry-325"></a>

### 79.3 共享经典存储的成本不是只数当前标签

设 $N$ 个历史在目标实验族中要求精确区分，并且它们必须被一次性写入一个 $d$ 维量子记忆。仓库的 `finite_memory_history_capacity` 在明确假设“$N$ 个密度态由同一个 POVM 一次性完美区分”时给出

$$
N\le d.
$$

若记忆由 $b$ 个量子比特组成，则 $d=2^b$，因此

$$
 b\ge \lceil\log_2N\rceil.
$$

对长度为 $L$、禁止相邻两个 $1$ 的 Zeckendorf 合法构型，

$$
|\mathcal W_L|=F_{L+2}.
$$

若每个合法构型先被编码成记忆 Hilbert 空间中的一个密度态，且任务要求同一个 POVM 一次性完美区分所有这些态，便得到必要条件

$$
 b\ge \left\lceil\log_2 F_{L+2}\right\rceil.
$$

这只是完美区分的下界。若只需预测一个目标族，历史可以按未来响应合并，所需维数由响应等价类数量决定，而不由原始构型总数决定。反过来，若两个当前标签在当前测量下相同、但在后续实验中可分开，则把它们合并会破坏闭合，即使当前标签数已经很小。

因此记忆预算应写成三元组，而不是一个整数：

$$
(\text{响应类数},\ \text{闭合误差},\ \text{可回收关联}).
$$

第一项控制需要多少可区分记录，第二项控制有限预测视界内的近似程度，第三项控制暂时不可见的相干是否可能重新出现。

<a id="entry-326"></a>

### 79.4 Zeckendorf 约束改变的是载体维数，不是动力学

令

$$
\mathcal W_L=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
\qquad
\mathcal H_{Z,L}=\operatorname{span}\{|w\rangle:w\in\mathcal W_L\}.
$$

对 $L\ge2$，并取 $\mathcal W_0=\{\epsilon\}$、$\mathcal W_1=\{0,1\}$，分解首位可得

$$
\mathcal W_L=0\mathcal W_{L-1}\sqcup10\mathcal W_{L-2},
$$

从而

$$
\dim\mathcal H_{Z,L}=F_{L+2}.
$$

这一步只决定允许的基态数量。若 $P_Z$ 是投影到该空间的投影，实际 Hamiltonian $H$ 还必须满足

$$
[H,P_Z]=0
$$

才能保证合法构型空间在连续演化下保持不变；离散更新则需要

$$
UP_Z=P_ZUP_Z.
$$

否则，Zeckendorf 只是对初始构型的编号，演化会产生不在该刻度内的状态。仓库已有的 `prime_diagonal_saturation` 说明了相近但不同的边界：当可见观测属于素数占据生成的对角代数时，完全对角 pinching 不改变这些观测的迹配对；该结论没有把对角代数之外的相干宣称为不存在，也没有给出任意 Hamiltonian 的不变性。

对 $L=2$，合法字串为 $00,01,10$。可把 $|01\rangle,|10\rangle$ 嵌入一个量子比特的两个基态，并把 $|00\rangle$ 作为剩余结果 $R$。这是一种任务特定的编码；它不等于把三维合法空间整体识别成二维量子比特。若后续操作能区分 $|00\rangle$ 与其余两态，$R$ 必须继续保留，否则该信息会在下一步回流中丢失。

<a id="entry-327"></a>

### 79.5 可检验的“稳定经典现实”条件

结合前面各节，可以把一个有限任务上的稳定对象**提议**定义为四元组

$$
\mathfrak O=(V,\mathfrak T,H,\varepsilon),
$$

其中 $V$ 是含单位的可见 operator system，$\mathfrak T$ 是允许的实验族，$H$ 是预测视界，$\varepsilon$ 是允许误差。其候选精度条件应写成：对所有密度矩阵 $\rho,\sigma$，若

$$
\forall A\in V,\quad \operatorname{tr}(\rho A)=\operatorname{tr}(\sigma A),
$$

则要求

$$
\sup_{T\in\mathfrak T,\,|w|\le H}
\operatorname{TV}\bigl(p_T(w\mid\rho),p_T(w\mid\sigma)\bigr)
\le\varepsilon.
$$

实验族 $\mathfrak T$ 应包含所允许的设置选择、记录和自适应停止规则。记录通道与动力学的闭合缺陷还须另行定义并纳入同一预算；这里的条件是研究接口，不是仓库现有的一个单独 Lean 判据。若再要求一个真正的量子子系统，则追加完全正的 $\iota,\mathcal R$ 及交换图条件。

因此问题“保留多少历史才得到经典现实”没有独立于任务的答案。精确形式是：寻找最小的 $V$，使其在给定 $\mathfrak T$、$H$ 和 $\varepsilon$ 下闭合，同时满足所需的物理编码条件。在明确给出成本函数和闭合缺陷定义后，才可把它写成如下研究中的受约束优化问题：

$$
\min_V\ \operatorname{cost}(V)
\quad\text{subject to}\quad
\operatorname{closure\_defect}(V;\mathfrak T,H)\le\varepsilon,
$$

这里的 $\operatorname{cost}$ 和 $\operatorname{closure\_defect}$ 都是待定义的研究量；物理版本还须追加“存在完全正编码、恢复和交换图”的约束，不能把它替换成尚未定义的标量等式。

这把“相对性”限制在明确的实验族、时间范围和误差预算内：换实验族会改变最小 $V$，增加预测视界会暴露原先隐藏的方向，要求物理可编码又会排除只有线性闭合而没有完全正回收的候选空间。

本节使用的永久稳定、可见维数、有限记忆容量和对角饱和均来自现有 Lean 模块；`FutureStatisticsEquivalence` 还把“所有未来读数相同”精确连接到差态对无限 Heisenberg 生成 operator system 的湮灭。$X/Z$ 的非代数例子、完全正编码接口和 Zeckendorf 投影不变条件是对这些结果的组合解释。它们给出可形式化的后续目标，但不宣称仓库已经证明任意 operator system 都有物理回收映射，也不把任务特定的二维嵌入提升为普遍量子存储定理。

<a id="entry-328"></a>

## 追加锚（新终端）

<a id="section-80"></a>

## 80. 中心标签、块内自由度与可组合历史

<a id="entry-330"></a>

### 80.1 预测算子系统与代数闭包

第 79 节的 $X/Z$ 例子说明，预测闭合和乘法闭合是不同要求。设一个固定的 Heisenberg 映射为 $H$，初始效果族为 $S$，定义

$$
V_0=\operatorname{span}_{\mathbb R}(\{I\}\cup S),
\qquad
V_{n+1}=V_n+H(V_n).
$$

全体有限回拉的实线性空间为

$$
V_\infty
=\operatorname{span}_{\mathbb R}
\{H^k(A):A\in V_0, k\in\mathbb N\}.
$$

`operator_system_tower_once_stable_permanently` 说明，在单一保单位完全正 Heisenberg 映射的前提下，一层相邻稳定就会永久稳定；`future_statistics_iff_annihilates_infinite_system` 则在其密度态、Schrödinger 通道、保单位 Heisenberg 对偶和迹配对前提下，把所有未来统计相同精确连接到差态对 $V_\infty$ 的迹配对全部为零。因此，$V_\infty$ 是相对于这组初始效果和这一个通道的预测载体。

但令

$$
\mathcal A_\infty
=\operatorname{Alg}^{\ast}_{\mathbb C}(V_\infty)
$$

表示包含 $V_\infty$ 的最小含单位复 $\ast$-子代数。一般只有

$$
V_\infty\subseteq (\mathcal A_\infty)_{\mathrm{sa}},
$$

而没有等号。两个可见效果的乘积、交换子或条件组合，可能产生原始未来词中没有出现的新方向。特别地，$V_{XZ}=\operatorname{span}_{\mathbb R}\{I,X,Z\}$ 对第 78 节指定仪器足以预测，却因为 $XZ=iY$ 而不是代数。

因此必须区分：

$$
V_\infty=\text{对指定未来统计最小的线性预测载体},
$$

$$
\mathcal A_\infty=\text{对指定可组合操作最小的代数载体}.
$$

若后续实验只查询原先的效果，加入所有乘积可能是过度保留；若实际协议的组合观测明确包含某个乘积（例如把 $AB$ 作为新的效应或关联观测），该乘积才会进入新的响应，不能只依靠 $V_\infty$ 上的读数。一般序列仪器的响应仍由具体 instrument 和 Heisenberg 共轭决定。`prediction_closure_minimal_dynamical_repair` 给出相应的线性最小不变闭包，但没有把该闭包提升为乘法代数。

<a id="entry-331"></a>

### 80.2 固定代数的中心与块内量子自由度

设 $\Lambda$ 有限、每个 $n_\lambda$ 有限，并先选定一个代数同构，使有限维固定代数具有块分解

$$
\mathcal A
\cong
\prod_{\lambda\in\Lambda}M_{n_\lambda}(\mathbb C).
$$

仓库的 `record_fixed_center_eq_block_scalars` 精确给出规范乘积代数的中心；经上述同构输运后得到这里的中心公式：

$$
Z(\mathcal A)
=
\left\{(c_\lambda I_{n_\lambda})_{\lambda\in\Lambda}:c_\lambda\in\mathbb C\right\}.
$$

因此（维数公式使用有限直积的标准线性代数维数计算）

$$
\dim_{\mathbb C}Z(\mathcal A)=|\Lambda|,
\qquad
\dim_{\mathbb C}\mathcal A=\sum_{\lambda\in\Lambda}n_\lambda^2.
$$

只有当所有 $n_\lambda=1$ 时，代数才交换，中心才等于整个代数。若某个 $n_\lambda>1$，同一个中心标签仍允许一个非平凡的块内量子系统；把标签 $\lambda$ 当成完整经典对象，会把这部分可由后续操作恢复的关系一并丢掉。

这给“经典记录”的含义加上一个边界：在给定记录通道确实固定这些中心投影、且允许观测族只读取它们时，中心投影才可作为稳定的经典标签；抽象代数的中心本身不自动给出物理记录通道。中心标签的数量不等于完整联合系统的 Hilbert 维数，也不等于可组合算子的维数。`FiniteMemoryHistoryCapacity.finite_memory_history_capacity` 的 $N\le d$ 也只在 $N$ 个密度态被同一个 POVM 一次性完美区分时成立，不能把中心标签数自动解释成所有物理记忆的维数。

<a id="entry-332"></a>

### 80.3 Zeckendorf 标签只决定中心数量的特殊情形

取禁止相邻 $11$ 的合法集合

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
\qquad
|\mathcal W_L|=F_{L+2}.
$$

若每个合法字串只对应一个一维块，则得到纯经典代数

$$
\mathcal A_Z
=\bigoplus_{w\in\mathcal W_L}\mathbb C,
$$

其中心维数、代数维数和标签数都等于 $F_{L+2}$。这正是 Zeckendorf 刻度与经典记录完全吻合的特殊情况。

若每个标签后面仍保留大小为 $n_w$ 的块，则

$$
\mathcal A_Z^{\mathrm{block}}
=\bigoplus_{w\in\mathcal W_L}M_{n_w}(\mathbb C),
$$

并且

$$
\dim_{\mathbb C}Z(\mathcal A_Z^{\mathrm{block}})=F_{L+2},
\qquad
\dim_{\mathbb C}\mathcal A_Z^{\mathrm{block}}
=\sum_{w\in\mathcal W_L}n_w^2.
$$

若物理 Hilbert 空间是一个有限维表示，并在第 $w$ 个块上含有重数 $m_w$（且这些重数满足所选表示的忠实性要求），其载体维数则为

$$
\dim\mathcal H=\sum_{w\in\mathcal W_L}m_wn_w.
$$

这三个数分别回答三个问题：合法标签有多少，可组合的算子有多少，实际联合载体有多少。因此不能从 $F_{L+2}$ 单独推出量子记忆维数、可见算子维数或未来统计的 Hankel 秩。

第 78 节的三构型嵌入已经展示了同一组合法字串在加入补空间后会出现额外记录方向；这里的块分解把“标签之外仍有内部状态”写成了统一公式。若后续实验只访问中心，块内状态可以暂时隐藏；若允许块内操作，隐藏部分必须继续保留在模型中。

<a id="entry-333"></a>

### 80.4 近似乘法闭包与历史预算

对一个有限维预测截断 $V\subseteq V_\infty$，先选定矩阵范数，并令距离取该范数到子空间的距离；定义乘法缺陷

$$
\eta(V)
=
\sup_{\substack{A,B\in V\\\|A\|,\|B\|\le1}}
\operatorname{dist}(AB,V+iV).
$$

这里 $V+iV$ 是 $V$ 的复化；有限维保证该子空间闭合。若 $\eta(V)=0$，则所有单位范数以内的可见乘积都落在复化空间中，因而该截断对这些乘积精确闭合。若 $\eta(V)>0$，至少有一对当前可见关系的组合产生了新的方向。这个量是研究定义，不是已冻结的物理误差；研究上有两种不同处理：

$$
\begin{aligned}
&\text{扩大记录，加入产生该乘积的历史关系；}\\
&\text{固定允许误差，把 }\eta(V)\text{ 纳入预测误差预算。}
\end{aligned}
$$

$\eta(V)$ 只量化一步的乘法缺口，不自动给出任意多步实验的误差界。多步控制、参考系统和有记忆环境仍需使用联合通道距离或相应的序列误差界；本节没有把 $\eta$ 宣称为一个已冻结的物理误差定理。

因此，对“保留多少历史才能得到稳定经典现实”的问题，三层结构可以写成

$$
\boxed{
\begin{gathered}
\text{只预测指定未来读数：保留 }V_\infty;\\
\text{允许可组合后续操作：保留 }\mathcal A_\infty;\\
\text{只读取稳定经典标签：保留 }Z(\mathcal A_\infty);\\
\text{存在量子块时：还要保留每个中心块的内部自由度。}
\end{gathered}}
$$

Zeckendorf 约束可以决定中心标签的自然组织和数量 $F_{L+2}$，但不能替代 Heisenberg 演化、乘法闭包或块内量子动力学。所谓稳定经典现实不是一个脱离任务的单独刻度，而是相对于实验族和后续操作选择的三层对象：预测算子系统、可组合代数以及其中心记录。只有明确当前实验使用哪一层，才知道哪些历史可以安全丢弃，哪些历史会在下一次组合操作中重新显现。

本节复用 `operator_system_tower_once_stable_permanently`、`future_statistics_iff_annihilates_infinite_system`、`prediction_closure_minimal_dynamical_repair`、`record_fixed_center_eq_block_scalars` 和 `finite_memory_history_capacity` 的现有结果。中心维数、块内自由度、乘法缺陷 $\eta(V)$ 与 Zeckendorf 分块的组合是本节的开放研究桥接，不冒充已有 Lean 定理。

<a id="entry-334"></a>

## 追加锚（新终端）

<a id="section-81"></a>

## 81. 记录重叠、恢复误差与可访问历史

<a id="entry-336"></a>

### 81.1 记录不是标签数，而是条件记录的重叠

第 80 节把中心标签与块内自由度分开，但还缺少一个量化问题：当记录被压缩后，剩余的相干究竟还能被恢复多少？仓库的 `FiniteRecordRecoveryError` 给出一个直接的有限模型。

取有限支持的复系数序列 $c_k$，满足

$$
\sum_{k\in\mathbb Z}\lVert c_k\rVert^2=1,
$$

并令记录的平移重叠为

$$
\gamma(\ell)
=
\sum_{k\in\mathbb Z}c_{k+\ell}\,\overline{c_k}.
$$

若系统构型 $i$ 被放置在整数位置 $q(i)$，记录通道对矩阵元的作用为

$$
\Lambda(A)_{ij}
=
\gamma\bigl(q(i)-q(j)\bigr)A_{ij}.
$$

因此对角项保持不变，而构型 $i,j$ 之间的相干按记录重叠 $gamma(q(i)-q(j))$ 缩放。这个量同时保留模长和相位；它不是“记录了几次”的计数。

`coefficient_gamma_neg` 保证

$$
\gamma(-\ell)=\overline{\gamma(\ell)},
$$

所以成对的非对角矩阵元仍满足 Hermitian 对称。对于有限支持记录，$gamma$ 是记录波形与其平移的自相关；记录形状、位置差和相位约定共同决定可见相干，而不是 Zeckendorf 标签本身单独决定。

<a id="entry-337"></a>

### 81.2 任意恢复都有一个由记录重叠决定的下界

设 $q(i)-q(j)\ne0$。`finite_record_recovery_error_lower_bound` 对任意量子通道 $R$ 都给出

$$
\frac{1-\lVert\gamma(q(i)-q(j))\rVert}{2}
\le
\sup_{\rho}
\frac12
\left\|
R\!\left(\Lambda(\rho)\right)-\rho
\right\|_1.
$$

更准确地说，右侧是该误差集合的上确界；定理还构造了两个输入态，它们在记录通道前的迹距离为 $1$，经过记录后变为 $\lVert\gamma(q(i)-q(j))\rVert$。迹距离的收缩性说明，任何恢复通道都必须支付上述损失。

这给出两个极端：

$$
\lVert\gamma(q(i)-q(j))\rVert=1
\quad\Longrightarrow\quad
\text{该下界为 }0,
$$

说明相干可能只是旋转或保留相位，不能从下界推出已经经典化；而

$$
\gamma(q(i)-q(j))=0
\quad\Longrightarrow\quad
\text{任意恢复的最坏误差至少为 }\frac12.
$$

所以“记录已经抹掉历史”必须附带记录模型和误差指标。相同的标签数量可以对应完全不同的 $\gamma$，相同的单步去相干也可以对应不同的多步恢复能力。

<a id="entry-338"></a>

### 81.3 Zeckendorf 位置与重叠谱

若把合法 Zeckendorf 构型 $w\in\mathcal W_L$ 映射到整数坐标 $q(w)$，例如使用权重 $(F_2,F_3,\ldots,F_{L+1})$ 的规范读数，则记录通道的相干矩阵为

$$
R_{wv}=\gamma\bigl(q(w)-q(v)\bigr).
$$

这说明 Zeckendorf 的作用是提供一组离散位置差；真正决定哪两条历史仍能相干汇聚的，是这些位置差落在记录自相关 $\gamma$ 的什么位置。

即使 $q(w)$ 唯一，仍可能出现

$$
q(w)-q(v)\ne q(w')-q(v')
\quad\text{但}\quad
\gamma(q(w)-q(v))=\gamma(q(w')-q(v')),
$$

也可能出现不同的位置差产生同一相位。于是“编码唯一”与“物理记录可区分”是两件事：前者是整数表示性质，后者是记录波形和相互作用的性质。

若记录设计满足对所有不同合法构型

$$
\left|\gamma(q(w)-q(v))\right|\le q_0<1,
$$

则重复使用独立同形记录时，相应的非对角系数至多按 $q_0^N$ 衰减；若记录是同一联合自由度的相干复用，则必须保留联合系统，不能把每轮都替换成无记忆的乘法通道。第 78 节的 fresh/reuse 对照正是这两个模型的差别。

<a id="entry-339"></a>

### 81.4 局部读数丢失不等于联合历史消失

`reduced_irreversibility_is_access_defect` 给出另一个边界。存在两个整体输入 $\rho,\sigma$，满足它们的对角读数相同而某个相干元不同。受控记录耦合后，联合态仍不同，但环境偏迹相同：

$$
\operatorname{Tr}_E(\Omega_\rho)
=
\operatorname{Tr}_E(\Omega_\sigma),
\qquad
\Omega_\rho\ne\Omega_\sigma.
$$

因此不存在只依赖这个局部边缘态的统一恢复函数

$$
D\!\left(\operatorname{Tr}_E\Omega\right)=\Omega
$$

来恢复这两个联合记录。可是访问完整记录并施加受控耦合的逆操作后，二者都能恢复到各自的空记录输入：

$$
U^\dagger\Omega_\rho U=\rho\otimes|0\rangle\langle0|,
\qquad
U^\dagger\Omega_\sigma U=\sigma\otimes|0\rangle\langle0|.
$$

这把“历史是否存在”改写成一个可操作的问题：历史关系是否仍在允许访问的联合自由度中，而不是是否已经出现在某个局部数值上。局部边缘的经典化可以与整体可逆性同时成立。

<a id="entry-340"></a>

### 81.5 对稳定经典现实的修正

结合第 79、80 节，稳定经典现实至少需要三个独立条件：

$$
\boxed{
\begin{aligned}
&\text{记录重叠谱在目标视界内足够收缩；}\\
&\text{可见 operator system 对指定实验闭合；}\\
&\text{被省略的联合记录在允许操作族中不会重新回流，或其回流误差有界。}
\end{aligned}}
$$

第一条由 $\gamma$ 的模长和恢复误差下界约束，第二条由 $V_\infty$ 或其有限稳定阶段约束，第三条由可访问环境范围和联合通道决定。Zeckendorf 可以为第一条提供规范位置差，为第二条提供合法构型索引，但不能单独证明任一条的物理前提。

因此，问题“要保留多少历史”现在可以写成一个带任务参数的优化：在给定实验族 $\mathfrak T$、预测视界 $H$、允许误差 $\varepsilon$ 和允许访问的记录代数 $\mathcal R$ 下，寻找最小保留结构，使

$$
\sup_{T\in\mathfrak T,\,n\le H}
\operatorname{TV}\bigl(p_T^{\mathrm{full}}(n),p_T^{\mathrm{retained}}(n)\bigr)
\le\varepsilon,
$$

同时满足记录重叠诱导的恢复下界、operator-system 闭合和联合访问约束。这个优化问题仍是开放的研究接口；本节只把已有的重叠谱、恢复下界和局部访问反例接到同一条可检验主线上。

本节复用 `coefficient_gamma_neg`、`finite_record_recovery_error_lower_bound` 和 `reduced_irreversibility_is_access_defect` 的现有 Lean 结果。Zeckendorf 位置映射、重复记录的多步误差和最后的保留结构优化是组合推导，不冒充仓库已有的统一恢复定理。

<a id="entry-341"></a>

## 追加锚（新终端）

<a id="section-82"></a>

## 82. 有限预测深度、完整证书与 Zeckendorf 载体

<a id="entry-343"></a>

### 82.1 深度不是时间长度，而是可见空间的秩增量

第 80 节中的 $V_\infty$ 是所有有限 Heisenberg 回拉的线性闭包。对一个有限维载体，真正需要观察多深，不等于实验运行了多少物理时间，而取决于这条回拉链还能增加多少个线性独立方向。

设 $d\ge1$，固定一个字母表和一个单一的 instrumentDual，并令 $V_n$ 为长度不超过 $n$ 的 sequential word effects 的实线性张成。若所有有限词效果最终张成整个 Hermitian 载体，则 `finite_sequential_completeness_depth` 给出某个

$$
N\le d^2-1
$$

使得长度不超过 $N$ 的词已经张成全部 Hermitian 效果空间。

这个上界来自实 Hermitian 维数的有限性：去掉由迹固定的单位方向后，trace-zero Hermitian 方向至多有 $d^2-1$ 个独立维度。每一步若还没有稳定，中心化空间至少增加一个维度；因此不可能在超过这个维数增量后继续严格增加。它不是任意效果标签数或物理时间长度的普遍上界。

这里的 $N$ 是一个最坏情形证书深度，不是任意系统的实际最小深度。若初始效果已经包含很多方向，实际深度可能远小于 $d^2-1$；若词族不能张成完整 Hermitian 空间，则该完整性定理的前提不成立，不能从维数直接宣称所有状态都可区分。多设置、自适应协议或参考系统必须先并入同一个有限载体和固定协议，不能直接套用这个单一 instrumentDual 的结论。

<a id="entry-344"></a>

### 82.2 稳定深度与终端预测空间

对 trace-zero Hermitian 载体上的一个固定线性 Heisenberg 更新，`centered_effect_stability_depth_bound` 给出更精细的形式：若 $T_n$ 是该固定更新下的中心化效果塔，$T_0$ 的维数为 $r_0$，终端预测空间的维数为 $r_\infty$，则最小一步稳定深度满足

$$
\operatorname{depth}_{\mathrm{stable}}
\le r_\infty-r_0
\le d^2-1-r_0.
$$

一旦某一层满足

$$
T_N=T_{N+1},
$$

该层就等于所有后续层的并空间：

$$
T_N=\bigvee_{n\ge0}T_n.
$$

这把“递归观察最终会不会停”变成了一个可检查的秩条件。它不要求先找到一个无限历史的终点；只要在有限维空间中检测到相邻层维数不再增加，就可以把当前层作为永久稳定候选。这里的深度是固定线性更新的词层数，不是任意物理时间，也不直接适用于未中心化的原始效果塔。

但这条结论仍然相对于一个固定线性更新和一个固定效果族。改变允许设置、引入自适应仪器、增加参考系统，都会改变 $T_n$ 的载体和相应的稳定深度；不能把一个任务的 $d^2-1$ 上界当作所有观察协议的普遍历史长度。

<a id="entry-345"></a>

### 82.3 信息完整性也有有限证书

若一个由正 effect 组成、且每个 $1-E$ 也为正的效果族，对所有密度态的原始概率读数是单射的，`finite_informational_effect_certificate` 进一步给出有限子族 $S$，满足

$$
|S|\le d^2-1,
$$

并且其中心化效果已经张成全部 trace-zero Hermitian 空间。原始效果在这个有限子族上的概率读数仍然可以区分所有密度态。

因此“保留多少个历史读数”与“保留多少个线性方向”不是同一个问题。一个无限的候选效果族可能只需要至多 $d^2-1$ 个精心选择的效果作为信息完整证书；但这不意味着任意抽取的 $d^2-1$ 个标签都足够，也不意味着这些效果在物理实验中可以同时、无噪声地获得。

对纯经典的 $D$ 个状态，信息完整记录通常只需区分 $D$ 个中心标签；对完整量子载体，状态空间的实参数维数为 $D^2-1$。这正是第 80 节必须区分中心标签数与块内自由度的原因：Zeckendorf 合法构型数 $F_{L+2}$ 可以是中心标签数，但若每个标签仍带量子块，完整预测证书的规模按块结构而非只按标签数计算。

<a id="entry-346"></a>

### 82.4 对 Zeckendorf 合法空间的条件上界

令

$$
D_L=|\mathcal W_L|=F_{L+2},
\qquad
\mathcal H_{Z,L}=\operatorname{span}\{|w\rangle:w\in\mathcal W_L\}.
$$

若明确把 $\mathcal H_{Z,L}$ 作为一个 $D_L$ 维物理 Hilbert 空间，并且所选仪器的 Heisenberg 效果在这个空间上满足完整性前提，那么把 $d=D_L$ 代入上述定理得到条件上界

$$
N_Z\le D_L^2-1
=(F_{L+2})^2-1.
$$

同样，信息完整效果族存在一个至多

$$
(F_{L+2})^2-1
$$

个效果的有限证书。

这只是一个载体维数上界。它没有从 Zeckendorf 递推自动推出实际 Hamiltonian、仪器完备性或实验可达性。若系统只允许某个受限 operator system，或存在块分解

$$
\mathcal A_Z^{\mathrm{block}}
=\bigoplus_w M_{n_w}(\mathbb C),
$$

则可见深度取决于实际 Heisenberg 作用在该空间上的秩增长；不能只把 $F_{L+2}$ 代入 $d$ 而跳过物理载体的构造。

<a id="entry-347"></a>

### 82.5 这给“保留多少历史”增加了一个可检验预算

对于给定载体、仪器和目标实验族，可以把历史保留预算拆为

$$
\boxed{
\begin{aligned}
&\text{结构预算：}\quad d^2-1\text{ 个 trace-zero 方向的最坏上界；}\\
&\text{深度预算：}\quad r_\infty-r_0\text{ 个实际秩增量；}\\
&\text{证书预算：}\quad \le d^2-1\text{ 个信息完整效果；}\\
&\text{恢复预算：}\quad \gamma\text{ 谱给出的不可恢复误差下界。}
\end{aligned}}
$$

第一项只由载体维数控制，第二项由具体动力学控制，第三项由任务的读出选择控制，第四项在第 81 节的具体记录模型和迹距离误差定义下由记录耦合与可访问环境控制。它们互相不能替代：较小的中心标签数不会消除块内维数，有限证书也不会保证记录通道可逆，深度稳定更不会自动产生经典吸引子。

所以，对用户最初的命题，一个更严格的有限版本是：在给定 Zeckendorf 合法载体、仪器族、预测视界和恢复访问范围后，保留的历史必须至少支撑任务所需的可见秩、有限证书和恢复误差预算；只有在这些条件同时满足时，才可以把当前层称为稳定的有效经典记录。

本节复用 `finite_sequential_completeness_depth`、`centered_effect_stability_depth_bound` 和 `finite_informational_effect_certificate` 的现有 Lean 结果。将 $d=F_{L+2}$ 代入 Zeckendorf 载体是条件性组合推导，不是仓库已经证明的受约束量子系统构造。

<a id="entry-348"></a>

## 追加锚（新终端）

<a id="section-83"></a>

## 83. 多上下文记录的独立预算

<a id="entry-350"></a>

### 83.1 一个上下文只能暴露一个有限切面

第 82 节给出了完整量子载体的维数界，但实际记录通常被分成多个上下文：同一系统可以在不同设置、不同基底或不同局部协议下留下不同结果。设上下文集合为有限集 $X$，上下文 $x$ 有 $m_x$ 个结果。去掉单位方向并把结果写成中心化效果后，每个上下文最多提供

$$
\operatorname{independentCount}(x)=m_x-1
$$

个独立结果方向。

这不是说一个上下文的所有结果都没有物理意义；被去掉的最后一个中心化效果由其余效果的和决定。这里计数的是能独立增加状态区分能力的实线性方向，不是 $m_x-1$ 个经典 bit，也不是一个可执行仪器的自动成本。仓库的 `SingleContextVisibleRemainderDimension` 在秩一基底上下文满足 `IsRecordMeasurement` 的条件下给出了相同的几何边界：单个完整基底的概率方向只有 $d-1$ 个独立中心化方向，剩余的 trace-zero Hermitian 方向仍需其他上下文或其他效应补足。

<a id="entry-351"></a>

### 83.2 联合信息完整性的下界

`multi_context_budget_lower_bound` 的假设是：每个上下文的中心化效果满足

$$
\sum_{j=1}^{m_x}E_{x,j}=0
$$

（单位方向已剥离；这些 $E_{x,j}$ 不是定理中自动带有正性的 POVM outcome），并且所有上下文的联合读数对密度态是单射的。若输入 Hilbert 空间维数为 $d\ge1$，则定理给出

$$
\boxed{
 d^2-1
 \le
 \sum_{x\in X}(m_x-1).
}
$$

证明的结构很直接：每个上下文删去一个由归一化决定的结果，剩余效果仍必须张成整个 trace-zero Hermitian 空间；该空间的实维数是 $d^2-1$，所以独立效果总数不能更少。这里是必要条件，不是充分条件；达到这个计数并不保证效果彼此独立、正性成立或存在一个可执行的仪器。

对第 78 节的三构型合法空间，如果明确把 $00,01,10$ 构造成一个三维正交 Hilbert 基，并要求多个上下文联合地完整区分任意密度态，则

$$
 d=3,qquad
\sum_x(m_x-1)\ge 8.
$$

若每个上下文只有两个结果，这个必要条件变成至少八个独立二元上下文方向。它不能被误读成“八次测量一定足够”：上下文之间的线性关系、完全正性和实际序列仪器仍需单独验证。

<a id="entry-352"></a>

### 83.3 Zeckendorf 长度下的条件预算

若长度为 $L$ 的合法字串空间被明确实现为一个完整物理载体，并且

$$
D_L=|\mathcal W_L|=F_{L+2},
$$

并且所选中心化效果满足逐上下文求和为零、联合读数对该载体上的全部密度态是单射，则联合信息完整的多上下文记录必须满足

$$
\boxed{
(F_{L+2})^2-1
\le
\sum_{x\in X}(m_x-1).
}
$$

这个式子把两种“尺度”接起来：Zeckendorf 递推给出合法构型的载体维数，量子上下文预算则给出分辨其全部密度态所需的独立中心化方向数。它只在合法构型确实成为正交物理基、上下文效果满足归一化、联合读数对所有密度态单射时成立。

若每个 Zeckendorf 标签后面带有量子块，则应将 $D_L$ 替换为实际联合 Hilbert 维数，或改用第 80 节的块代数和所选 operator system 的真实维数。只把 $F_{L+2}$ 当成总维数，会漏掉块内自由度；只把上下文结果数相加，又可能重复计算线性相关的效果。

<a id="entry-353"></a>

### 83.4 父记录、上下文专用记录与量子保留

这个下界还揭示三种存储方案的差别。

第一，**上下文专用记录**可以在设置 $x$ 已知后，只保存该上下文的 $m_x-1$ 个独立线性读出方向；这不是说需要 $m_x-1$ 个经典 bit，实际编码成本还取决于读数精度和物理实现。

第二，**共同经典记录**必须在设置尚未揭示时同时支持所有上下文的联合读数。这是额外的 parent-record 问题，不能由本节的线性计数下界单独推出父 POVM 不可能；第 78 节的 $X/Z$ 二元模型才给出了一个具体的完全精确父 POVM no-go。计数下界只说明联合完整读数所需的独立中心化方向不能凭空消失。

第三，**保留量子载体**不必预先把所有上下文结果写成经典标签，而是保留足够的量子自由度，在设置揭示后再选择测量。这样可以避免把不相容结果同时写入一个经典表格，但其物理成本转移为保存 Hilbert 空间、控制相互作用和限制环境回流。

因此，“保留多少历史”必须先说明设置何时揭示：

$$
\begin{aligned}
&\text{设置先揭示：}\quad\text{可以使用上下文专用记录；}\\
&\text{设置后揭示：}\quad\text{需要共同父记录，或保留量子载体；}\\
&\text{允许有限误差：}\quad\text{需要把上下文缺陷和读出距离纳入预算。}
\end{aligned}
$$

多上下文预算不推翻第 80 节关于中心和块的区分，也不替代第 81 节的恢复误差下界。它补充的是另一项必要条件：即使没有任何隐藏回流，联合完整记录本身也需要足够多的独立中心化方向。若任务只预测一个受限 observable system，而不是区分全部密度态，则应改用该任务空间的维数，不能直接套用 $d^2-1$ 的全 tomography 下界。

本节复用 `multi_context_budget_lower_bound` 和 `single_context_visible_remainder_dimension` 的现有结果。将 $d=F_{L+2}$ 代入得到的 Zeckendorf 预算是条件性组合推导；共同父 POVM 的精确不可能性仍由第 78 节的具体二元模型承担，不把计数下界冒充为一般 no-go 定理。

<a id="section-84"></a>

## 84. 互补上下文怎样补齐剩余方向

<a id="entry-355"></a>

### 84.1 从预算下界到正交补齐

第 83 节只给出了联合记录必须拥有多少个独立中心化方向的必要条件。现有的 `CompleteContextTomography` 与 `MutuallyUnbiasedDiagonalPlanes` 还给出一个更有结构的条件性实现：如果一个 $d$ 维物理载体存在 $d+1$ 个秩一上下文，并且任意两个不同上下文满足

$$
\operatorname{Tr}(P_{x,j}P_{y,k})=\frac1d
\qquad(x\ne y),
$$

并且再加上一个载体识别条件：每个上下文的中心化对角平面确实等同于其 $d$ 维 trace-zero 对角载体。记第 $x$ 个平面为 $\mathsf P_x$，则在这个附加条件下，每个平面有 $d-1$ 个独立方向，而且不同上下文的这些平面彼此正交：

$$
\dim \mathsf P_x=d-1,
$$

$$
\mathsf P_x\perp\mathsf P_y\quad(x\ne y),
$$

从而

$$
\dim\Bigl(\bigoplus_{x=0}^{d}\mathsf P_x\Bigr)
=(d+1)(d-1)=d^2-1.
$$

右端正好是 trace-zero Hermitian 方向的维数。因此，在这些重叠条件和完整物理载体假设下，第 83 节的必要预算被恰好填满：单位方向由归一化提供，$d^2-1$ 个中心化方向由 $d+1$ 个互补上下文提供。

这里的逻辑方向必须保持清楚。仓库定理证明的是：**给定**这些上下文和重叠假设，就能得到唯一分解、无共同不可见 trace-zero 残差，以及由所有上下文概率确定 Hermitian trace-one 矩阵。它没有证明任意维数都存在这样的物理仪器，也没有把一组形式上的 `RankOneContext` 自动解释成实验室中可实现的 POVM。

<a id="entry-356"></a>

### 84.2 互补不是额外标签，而是剩余空间的几何补偿

一个上下文的去相位通道可以写成

$$
\mathcal D_x(X)=\sum_j\operatorname{Tr}(P_{x,j}X)P_{x,j}.
$$

它把 $X$ 保留在第 $x$ 个对角平面和单位方向上，而把与该平面正交的方向压到当前读数不可见。若 $x\ne y$ 的两个上下文互补，则现有定理给出，对 Hermitian $X$：

$$
\mathcal D_x\mathcal D_y(X)
=\frac{\operatorname{Tr}(X)}{d}I,
$$

以及交换次序后的同样等式。特别地，对 trace-zero 部分 $X_0$ 有

$$
\mathcal D_x\mathcal D_y(X_0)=0.
$$

这不是说第二次观测把整体量子信息从宇宙中删除；它说的是：在只保留第一次和第二次去相位之后的系统边缘记录时，两个互补切面连续作用会把 trace-zero 方向都压到单位方向，当前这组经典记录看不到原来的方向。若环境或记录寄存器仍可访问，联合系统可以保留更多信息；因此“消失”必须带有访问范围的下标。

这也说明为什么“上下文数量”不能直接等同于“历史长度”。两个上下文可以提供互相正交的新方向，也可以在连续去相位协议中抹掉此前可见的方向。真正的资源是记录代数中保留下来的独立方向和仍可访问的联合关联。

<a id="entry-357"></a>

### 84.3 三种协议的区别

设设置变量为 $x$，系统状态为 $\rho$。

**上下文先揭示。** 若 $x$ 在相互作用前已知，可以只实施 $\mathcal D_x$，并保存该上下文的 $d-1$ 个独立中心化读数。对于只预测该上下文后续响应的任务，这可以是足够的有效记录；它不承诺对未选择的上下文仍然可回答。

**设置后揭示。** 若 $x$ 在记录之后才揭示，则一份共同的经典记录必须同时支撑各个 $\mathcal D_x$ 的统计预测。这是共同父记录问题。第 84.1 节的正交分解说明在完整量子载体上怎样用多上下文效果补齐信息，但它不构造一个预先写好所有不相容答案的经典表，也不由维数等式单独推出共同父 POVM 的存在或不存在。

**延迟测量。** 若设置尚未揭示而又不要求立即产生经典标签，可以保留 $\rho$ 或一个足够大的联合量子载体，待 $x$ 确定后再实施相应测量。代价转移为保存载体、抑制环境回流并控制联合演化；收益是没有把不相容上下文强行压缩成同一份经典记录。

因此，“保留多少历史”的答案依赖设置揭示顺序：

$$
\begin{array}{c|c|c}
\text{设置时序}&\text{可保留结构}&\text{主要约束}\\
\hline
\text{先揭示}&\text{上下文专用经典记录}&d-1\text{ 个中心化方向}\\
\text{后揭示}&\text{共同父记录或量子载体}&\text{上下文兼容性与联合访问}\\
\text{允许延迟}&\text{未去相位的量子关联}&\text{载体保存与环境回流}
\end{array}
$$

<a id="entry-358"></a>

### 84.4 Zeckendorf 合法空间的两个小模型

取禁止相邻 `11` 的合法空间 $\mathcal H_{Z,L}$，并明确假设每个合法字串对应一个正交物理基态。

当 $L=2$ 时，合法构型为

$$
\mathcal W_2=\{00,01,10\},
\qquad d=|\mathcal W_2|=F_4=3.
$$

若要在这个三维载体上做完整态层析，$d+1=4$ 个互补三结果上下文每个提供 $d-1=2$ 个中心化方向，总数为

$$
4\times2=8=3^2-1.
$$

这与第 78 节的三构型模型相容：一个上下文只能看到二维的概率差，另外六个 trace-zero 方向必须由其他设置补足。这里的“四个上下文”是满足互补重叠假设时的条件性层析设计，不是声称仓库已经为该 Zeckendorf 模型构造了具体实验 Hamiltonian。

当 $L=3$ 时，合法构型为

$$
\mathcal W_3=\{000,001,010,100,101\},
\qquad d=|\mathcal W_3|=F_5=5.
$$

相应的完整互补上下文条件需要 $d+1=6$ 个五结果上下文，每个有 $4$ 个独立中心化方向，总预算为

$$
6\times4=24=5^2-1.
$$

Zeckendorf 在这里提供的是合法载体和离散索引；它没有决定这六个上下文的投影矩阵、相互作用角度或记录噪声。若实际系统只允许其中一部分局部效果，预算应改用可达 operator system 的真实维数，不能继续套用 $d^2-1$。

<a id="entry-359"></a>

### 84.5 对“稳定经典现实”的进一步限制

互补上下文的正交补齐给出的是**信息完整性**，不是**经典吸引性**。即使

$$
\bigoplus_x\mathsf P_x
=\operatorname{Herm}_0,
$$

仍需另外检查记录通道的非对角 Gram 系数是否满足严格收缩、隐藏关联是否会回流，以及当前保留结构是否对目标演化近似闭合。信息完整意味着“有一组上下文能够区分载体上的状态”；它不意味着一次记录后所有相干都会衰减，也不意味着不同记录会自动形成共同的经典父变量。

因此当前研究对象可以写成三层条件的交集：

$$
\boxed{
\begin{aligned}
&\text{几何完整：}&\quad&\sum_x\mathsf P_x=\operatorname{Herm}_0,\\
&\text{动力学闭合：}&\quad&\mathcal E\Phi\approx\mathcal E\Phi\mathcal E,\\
&\text{记录吸引：}&\quad&|R_{ij}|<1\text{（对需要经典化的关系）}.
\end{aligned}}
$$

第一条回答“哪些上下文合起来足以测量”；第二条回答“丢掉的差异会不会在未来返回”；第三条回答“被记录的相干是否真的衰减”。只有把三条分别验证，才有资格把某个有限层次称为稳定的有效经典现实。

本节直接复用 `complete_context_tomography` 与 `mutually_unbiased_diagonal_planes` 的现有条件性结果。$L=2,3$ 的 Zeckendorf 计数、正交平面维数相加以及三种协议的区分是组合推导；共同父 POVM 的一般存在性、具体 Zeckendorf Hamiltonian 和实验噪声模型仍保持开放。

<a id="section-85"></a>

## 85. 完备上下文的纯度证书与经典化边界

<a id="entry-361"></a>

### 85.1 互补记录可以测出纯度，但纯度不是状态本身

在第 84 节的完整互补上下文假设下，仓库已有 `complete_context_purity_identities`。令

$$
p_{l,j}=\operatorname{Tr}(\rho P_{l,j}),
\qquad d=\dim\mathcal H,
$$

并假设 $\rho$ 是正半定且迹为一。该恒等式给出

$$
\boxed{
\sum_{l=0}^{d}\sum_{j=0}^{d-1}
\left(p_{l,j}-\frac1d\right)^2
=\operatorname{Tr}(\rho^2)-\frac1d.
}
$$

等价地，所有上下文概率平方和满足

$$
\boxed{
\sum_{l=0}^{d}\sum_{j=0}^{d-1}p_{l,j}^2
=1+\operatorname{Tr}(\rho^2).
}
$$

因此，完备互补记录不仅能在原则上重建状态，还能把纯度写成一个直接的记录能量。最大混合态的中心化能量为零；纯态的中心化能量为 $1-1/d$。

但纯度只是一个标量不变量。不同的密度态可以拥有相同的 $\operatorname{Tr}(\rho^2)$，所以这两条恒等式本身不能替代第 84 节的全状态层析，也不能把“纯度已经测出”说成“历史已经唯一恢复”。它们提供的是一个低成本的完整性检查：若重建的概率不满足该恒等式，记录、归一化、正性或上下文重叠假设至少有一项不相容。

<a id="entry-362"></a>

### 85.2 Zeckendorf 小载体上的数值刻度

在 $L=2$ 的三构型载体中，$d=F_4=3$。若状态为纯态，则

$$
\sum_{l,j}\left(p_{l,j}-\frac13\right)^2=\frac23;
$$

若状态为最大混合态，则该和为零。在 $L=3$ 的五构型载体中，$d=F_5=5$，相应的纯态值为

$$
\sum_{l,j}\left(p_{l,j}-\frac15\right)^2=\frac45.
$$

这些数值只使用合法构型数作为明确的 Hilbert 维数，并把互补上下文假设作为输入。Zeckendorf 权重本身不决定纯度；它只决定被记录的离散基态如何编号。

若实际系统只实现受限的 observable system，平方和应改成该系统内的投影能量，并重新证明相应恒等式。不能把全空间公式直接套到缺失上下文或带量子块的模型。

<a id="entry-363"></a>

### 85.3 纯度证书不能替代动力学闭合

纯度证书回答的是“当前记录是否携带了足够的二次信息来检验一个状态不变量”。它不回答：

$$
\mathcal E\Phi=\mathcal E\Phi\mathcal E
$$

是否成立，也不回答非对角 Gram 系数是否严格小于一。一个过程可以保持纯度而在不同上下文之间相干旋转；也可以在记录后纯度下降，却因隐藏记录仍可访问而保持整体可逆。

因此，在当前研究主线上，至少要分开三种证书：

$$
\begin{aligned}
&\text{层析证书：}&\quad&\{p_{l,j}\}\text{ 是否唯一确定目标载体上的状态；}\\
&\text{纯度证书：}&\quad&\sum_{l,j}(p_{l,j}-1/d)^2\text{ 是否与 }\operatorname{Tr}(\rho^2)-1/d\text{ 一致；}\\
&\text{动力学证书：}&\quad&\mathcal E\Phi\approx\mathcal E\Phi\mathcal E\text{ 且隐藏回流误差是否受控。}
\end{aligned}
$$

只有第一项和第二项成立时，我们得到的是“可测且可校验的当前状态”；加入第三项后，才得到“在指定预测视界内可作为有效对象使用的记录”。这正是“稳定经典现实”不能由单一观测次数或单一纯度数值定义的原因。

本节复用 `complete_context_purity_identities` 的现有条件性结果。$L=2,3$ 的数值代入和三类证书的区分是组合解释；有限精度下的统计置信区间、缺失上下文时的残差界以及带量子块载体的纯度分解仍是开放接口。

<a id="section-86"></a>

## 86. 目标相对的记录充分性与未来残差

<a id="entry-365"></a>

### 86.1 记录预算应按目标算，而不是按全部状态算

设当前记录效果为 $E_i$，把单位方向一并保留，定义可见算子空间

$$
\mathcal V
=\operatorname{span}_{\mathbb R}\{I,E_i:i\in\mathcal I\}.
$$

冻结定理 `target_prediction_sufficiency` 给出一个严格的二分。

若目标 observable $A$ 满足

$$
A\in\mathcal V,
$$

那么任何两个当前记录相同的物理态，对 $A$ 的期望值也相同。换言之，若任务只要求预测 $\mathcal V$ 内的目标，当前记录已经对该目标充分；不需要为了一个目标自动保存完整 $d^2-1$ 个 trace-zero 方向。

若

$$
A\notin\mathcal V,
$$

定理构造一个非零的 trace-zero Hermitian 残差 $D\in\mathcal V^\perp$，以及足够小的 $\varepsilon>0$，使

$$
\rho_\pm=\frac1dI\pm\varepsilon D
$$

仍是物理密度态。它们满足所有当前效果的读数相同，但

$$
\operatorname{Tr}(D A)\ne0,
$$

因而对目标 $A$ 的期望不同。当前记录对该目标不充分，不是因为缺少更精细的标签，而是因为目标方向落在可见算子空间之外。

这把第 83 节的全 tomography 预算收紧成任务相对的版本：

$$
\boxed{
\text{所需历史}\\
\text{由目标族在可见算子空间中的覆盖决定。}
}
$$

若目标族是所有 Hermitian observable，才需要把 $\mathcal V$ 扩展到完整载体；若目标族只包含 Zeckendorf 数值和若干局部模式，则可以只扩展到这些目标生成的子空间。

<a id="entry-366"></a>

### 86.2 Zeckendorf 数值是一个目标，不是完整状态

在 $L=2$ 的合法基底

$$
\{00,01,10\}
$$

上，按权重 $(2,1)$ 定义 Zeckendorf 数值 observable

$$
A_Z=0|00\rangle\langle00|
 +1|01\rangle\langle01|
 +2|10\rangle\langle10|.
$$

如果当前记录效果的实线性张成包含 $I$ 与 $A_Z$，那么记录相同的两个态必然拥有相同的 Zeckendorf 数值期望。这个结论只涉及一个目标方向；它不推出两态对非对角相位、其他上下文或未来 Hamiltonian 的响应相同。

若后续动力学把 $A_Z$ 的 Heisenberg 回拉带到新的方向 $U^\dagger A_ZU$，则记录预算必须扩大到这些回拉方向的张成空间。于是“保留一个 Zeckendorf 数”只对当前目标成立；要预测一族后续实验，必须把该实验族的目标闭包纳入 $\mathcal V$。

<a id="entry-367"></a>

### 86.3 未来误差是两个残差的相关

对一个有限效果塔，令 $\mathcal V_m$ 为当前深度可见的 trace-zero 空间，$\mathcal R_m=\mathcal V_m^\perp$ 为隐藏残差空间。对密度态 $\rho$，记其中心化 trace-zero 坐标为 $s_\rho$；未来效果 $F$ 也指 Heisenberg 回拉得到的中心化 Hermitian 方向。`future_probability_residual_correlation` 给出：以可见投影构造线性预测代表后，预测误差满足

$$
\boxed{
\operatorname{error}
=\left\langle
\Pi_{\mathcal R_m}(s_\rho),
\Pi_{\mathcal R_m}(F)
\right\rangle,
}
$$

并有 Cauchy--Schwarz 界

$$
|\operatorname{error}|
\le
\sqrt{\operatorname{residualMass}(\mathcal V_m,s_\rho)}
\,\left\|\Pi_{\mathcal R_m}(F)\right\|.
$$

因此未来误差不是一个只由“隐藏维数”决定的常数。它同时取决于两件事：当前状态在隐藏方向上有多少分量，以及未来目标本身有多少分量会探测这些方向。隐藏空间很大但目标完全正交时，误差仍可为零；隐藏空间很小但未来目标正好对准它时，误差可以达到该界的量级。

同一个隐藏残差还控制压缩动力学本身的不自然性。若环境动力学在 trace-zero 载体上是 $L$-Lipschitz，`residual_controls_naturality` 给出

$$
\Delta_m(X)
\le L\,\left\|\Pi_{\mathcal R_m}X\right\|,
$$

其中 $\Delta_m$ 是“先完整演化再投影”和“先投影再演化”的距离差。在密度态的中心化坐标上，进一步有

$$
\Delta_m(s_\rho)\le L\sqrt{\operatorname{residualMass}(\mathcal V_m,s_\rho)}.
$$

所以同一个 $\sqrt{M_m}$ 同时出现在未来观测误差和动力学压缩缺陷的上界中；前者还乘以未来目标的残差敏感度，后者还乘以动力学的 Lipschitz 常数。两者是共同受残差控制的两个不同量，不是同一个误差的恒等改写。

这个定理还包含一个必要警告：把状态的可见投影加回单位部分得到的线性预测代表，未必是正半定矩阵。因此“用当前记录预测未来”首先是一个 observable 期望的线性近似，不能自动解释成一个新的物理密度态。若需要物理态级别的预测，必须另加正性、完全正性或误差通道的证明。

<a id="entry-368"></a>

### 86.4 历史保留的目标闭包判据

设目标族为 $\mathfrak A$，允许的 Heisenberg 更新为 $\mathfrak U$。一个有限记录空间 $\mathcal V$ 对任务足够的必要条件是

$$
\operatorname{span}\{U^\dagger A U:
A\in\mathfrak A,\ U\in\langle\mathfrak U\rangle\}
\subseteq\mathcal V,
$$

其中右侧也应包含单位方向。若该包含关系成立，目标闭包中的每个未来期望都由当前签名决定；若失败，`target_prediction_sufficiency` 的残差构造给出一对当前不可区分、未来可区分的物理态。

这提供了一个比“保留多少历史”更精确的工作流程：先列出任务目标和允许的后续操作，再计算它们的有限线性闭包，最后只保留能覆盖该闭包的记录方向。Zeckendorf 合法构型给出初始离散坐标；真正决定历史成本的是目标闭包的秩和隐藏残差与未来目标的相关。

本节复用 `target_prediction_sufficiency`、`future_probability_residual_correlation` 和 `residual_controls_naturality` 的现有结果。$A_Z$ 的有限 Zeckendorf 构造、目标闭包的物理可达性，以及把线性误差界提升为完整通道距离，仍是条件性组合推导或开放接口。

<a id="section-87"></a>

## 87. 一次经典记录能保存多少个可完美区分的历史

<a id="entry-370"></a>

### 87.1 完美区分数受载体维数限制

第 86 节讨论的是目标 observable 的线性覆盖；现在考虑更强的任务：用同一个 POVM 一次性、无误差地识别一组历史状态。设记忆 Hilbert 空间维数为 $d$，候选密度态为 $\rho_i$，记录效果为 $E_j$，满足

$$
E_j\succeq0,
\qquad
\sum_jE_j=I,
$$

并要求完美配对

$$
\operatorname{Tr}(E_j\rho_i)=\delta_{ij}.
$$

冻结定理 `finite_memory_history_capacity` 证明：若这些条件成立，候选历史数 $N$ 必须满足

$$
\boxed{N\le d.}
$$

证明的几何核心是：每个 $\rho_i$ 的支撑落在 $E_i$ 的单位特征子空间中，并与其他效果的支撑正交；因此从每个非零密度态中选出的向量构成一组两两正交的记忆向量，数量不能超过 Hilbert 维数。

这条界与第 82、83 节的 $d^2-1$ 方向预算承担不同任务：

$$
\begin{aligned}
&d^2-1 &&\text{控制连续量子状态的 trace-zero 参数方向；}\\
&d &&\text{控制同一 POVM 一次可完美区分的经典历史标签数。}
\end{aligned}
$$

一个 $d$ 维系统可以有 $d^2-1$ 个连续可观测方向，却不能用一次固定经典读出去完美区分超过 $d$ 个任意历史状态。把这两个数字混为同一个“记忆容量”会错误估算所需约束。

<a id="entry-371"></a>

### 87.2 Zeckendorf 合法载体的容量读法

若长度为 $L$ 的禁止相邻 `11` 合法空间确实实现为一个完整正交载体，则

$$
d=D_L=F_{L+2}.
$$

在同一个一次性 POVM 下，完美可区分历史数满足

$$
\boxed{N\le F_{L+2}.}
$$

所以：

$$
L=2\Rightarrow N\le F_4=3,
\qquad
L=3\Rightarrow N\le F_5=5.
$$

这里的 $N$ 是可完美区分的密度态或记录历史数，不是合法字符串总数以外的额外物理自由度；它也不是可重建任意密度态所需的 $d^2-1$ 个概率方向。若每个 Zeckendorf 标签后面带有量子块，必须将 $d$ 换成实际联合 Hilbert 维数；仅用标签数量代入会低估一次性记录容量的需求。

<a id="entry-372"></a>

### 87.3 超过容量时，历史必须改变形态

当候选历史数满足

$$
N>d,
$$

同一个记忆载体和同一个 POVM 不可能同时实现上述 Kronecker 配对。要继续区分这些历史，至少需要改变一个条件：

$$
\begin{aligned}
&\text{增加载体维数；}\\
&\text{使用多个设置或多轮记录；}\\
&\text{保留联合量子关联而延迟最终读出；}\\
&\text{放宽为近似区分，并给出统计误差界。}
\end{aligned}
$$

这不是说超过 $d$ 个历史就不能被任何实验区分。多轮协议可以把历史编码到更大的联合载体，多个上下文可以在可重复制备上完成层析，延迟测量可以保留不相容设置所需的相位。定理只限制“同一个有限记忆、同一个一次性完美 POVM”的协议。

因此，稳定经典记录的历史成本至少有两种不同读法：若目标只是当前一次的无误标签，容量受 $d$ 限制；若目标是未来任意上下文的连续预测，成本由第 86 节的目标闭包和残差半径决定。增加标签数量不能替代增加可访问的量子载体或保留历史关联。

本节复用 `finite_memory_history_capacity` 的现有结果。将 $d=F_{L+2}$ 代入是条件性 Zeckendorf 载体解释；近似区分、重复实验的总容量、带记忆环境的联合编码和块结构载体仍需分别建模。


<a id="section-88"></a>

## 88. 观测细化中的容量—残差守恒

<a id="entry-374"></a>

### 88.1 可见容量与不可见残差

设记忆载体为 $d$ 维 Hilbert 空间，当前效果集合为 $\mathcal E$。把单位效果也纳入后，定义

$$
\mathcal V(\mathcal E)
=
\operatorname{span}_{\mathbb R}
\bigl(\{I\}\cup\mathcal E\bigr),
$$

并令

$$
C(\mathcal E)
=
\dim_{\mathbb R}\mathcal V(\mathcal E)-1,
\qquad
R(\mathcal E)
=
\dim_{\mathbb R}\mathcal V(\mathcal E)^\perp.
$$

现有定理 observer_capacity_conservation 给出

$$
\boxed{
C(\mathcal E)+R(\mathcal E)=d^2-1.
}
$$

这里的 $d^2-1$ 是完整 trace-zero Hermitian 载体的总方向数，不是历史条数或 POVM outcome 数。若粗效果集满足

$$
\mathcal E_{\mathrm{coarse}}
\subseteq
\mathcal E_{\mathrm{fine}},
$$

则

$$
C(\mathcal E_{\mathrm{coarse}})
\le
C(\mathcal E_{\mathrm{fine}}),
\qquad
R(\mathcal E_{\mathrm{fine}})
\le
R(\mathcal E_{\mathrm{coarse}}).
$$

因此细化记录只把原先不可见的方向转移到当前可见空间；线性相关的新增标签不会增加容量。

<a id="entry-375"></a>

### 88.2 Zeckendorf 载体上的预算

若长度为 $L$ 的禁止相邻 11 合法空间明确实现为完整正交载体，则

$$
d=F_{L+2},
\qquad
C(\mathcal E)+R(\mathcal E)
=
(F_{L+2})^2-1.
$$

所以

$$
L=2:\quad C+R=8,
\qquad
L=3:\quad C+R=24.
$$

这与第 87 节的

$$
N\le F_{L+2}
$$

是不同容量：前者计算连续 Hermitian 方向，后者计算一次固定 POVM 可完美区分的离散历史态数。若合法构型后面带有量子块，或仪器只作用在受限 operator system 上，必须使用实际载体或任务空间的维数，不能只按 Zeckendorf 标签数代入。

<a id="entry-376"></a>

### 88.3 细化不制造总信息

若某个差异仍位于

$$
\mathcal V(\mathcal E_{\mathrm{fine}})^\perp,
$$

则当前效果族仍无法区分它。要让它进入后续预测，必须加入能与之配对的效果，或让动力学把它旋转进可见空间。这把“保留更多历史”改写成一个线性选择问题：寻找能降低 $R(\mathcal E)$、并覆盖目标闭包的独立效果，而不是盲目保存更多原始词。

精确维数守恒不等于近似预测误差已经足够小。残差维数为零时才得到完整线性可见性；残差非零时，误差仍由第 86 节的状态残差与未来目标残差相关界控制：

$$
|\operatorname{error}|
\le
\sqrt{\operatorname{residualMass}}
\,
\|\text{未来目标的残差分量}\|.
$$

反过来，残差维数很大也不必然造成当前任务误差，因为当前状态或目标可能在这些方向上的投影为零。因此稳定经典记录至少需要同时报告可见容量、残差容量和目标敏感度。

本节复用 observer_capacity_conservation 的现有结果。将 $d=F_{L+2}$ 代入以及与第 86 节误差界的组合是条件性理论桥；近似容量、噪声成本和具体 Zeckendorf 物理仪器仍保持开放。

<a id="entry-377"></a>

## 追加锚（新终端）

<a id="section-89"></a>

## 89. 记录关联、熵增与可恢复历史

<a id="entry-379"></a>

### 89.1 预测量把相干搬到联合系统，而不是把它直接抹掉

设系统的密度态为 $\rho$，记录自由度起初为空白。项目中的 `coherentCopyState` 给出一个有限维的理想预测量模型：输入矩阵的每个条目被放置在相关基底向量之间，特别是

$$
\bigl(\operatorname{coherentCopyState}(\rho)\bigr)_{(i,i),(j,j)}
=
\rho_{ij}.
$$

因此，联合态仍然保留原来的非对角条目。若只看其中一边，另一边被偏迹掉，则两个边缘态都变成同一个基底去相位态：

$$
\rho_S
=
\rho_E
=
\operatorname{basisPinchingState}(\rho).
$$

这给“历史消失”一个更严格的解释：

> 对局部访问而言，非对角历史不再出现在边缘矩阵中；对整体联合态而言，它仍可能保存在系统—记录关联的相关条目里。

项目还证明相干复制是等距扩张，联合态的 von Neumann 熵保持不变：

$$
S\!\left(\operatorname{coherentCopyState}(\rho)\right)=S(\rho).
$$

所以这里没有把一个可逆的整体过程直接等同为无条件的热力学熵增。增加的是局部可见的经典记录以及系统与记录之间的相关，而不是由这条等距复制定理单独推出的总熵增加。

<a id="entry-380"></a>

### 89.2 关联的“成本”由记录熵和相干删除项共同组成

对同一个联合态，项目中的 `coherent_copy_correlation_tax` 给出精确分解：

$$
\boxed{
I(S:E)
=
S\!\left(\operatorname{basisPinchingState}(\rho)\right)
+D\!\left(
\rho\middle\|\operatorname{basisPinchingState}(\rho)
\right).
}
$$

右侧第一项是去相位后保留下来的记录熵；第二项是原态相对于去相位态的量子相对熵。对本节这个基底去相位特例，若采用相对熵非负这一有限维性质，则系统—记录互信息至少包含记录边缘的熵，并且还包含一项由原始相干与局部经典化之间的差异贡献的项。这里的非负性不是 `coherent_copy_correlation_tax` 等式本身额外返回的独立结论；重复协议的公开定理在第 89.4 节明确给出相应每步项的非负性。

这里的“成本”是信息论分解中的成本，不能直接改写成实验室中的热量、功或不可逆熵产生。要作热力学解释，还需要指定温度、能量、环境初态和实际耗散通道。当前定理只处理有限维密度矩阵、偏迹、基底去相位和相对熵。

这一区分也修正了一个容易混淆的说法：

$$
\text{局部读数变得经典}
\not\Rightarrow
\text{整体信息已经销毁}.
$$

在联合描述中，关联承担了原先由局部非对角项承担的部分信息；只有当记录自由度不可访问、被进一步偏迹，或者动力学把这些关联真正带出允许的联合操作范围时，才可以在给定任务上把它视为不可恢复。

<a id="entry-381"></a>

### 89.3 可恢复性取决于访问范围，而不是只取决于边缘读数

`CanonicalRecordAccessRecovery` 提供了一个二能级的具体边界。取两个状态 $\rho$ 和 $\sigma$，假设它们在选定基底上的对角元完全相同，但存在某个非对角元不同：

$$
\forall i,\ \rho_{ii}=\sigma_{ii},
\qquad
\exists i\ne j,\ \rho_{ij}\ne\sigma_{ij}.
$$

一个可逆受控耦合可以把两者写成不同的联合记录态；对记录做偏迹后，两者得到相同的局部约化态，因此不存在一个只接受该约化态、就能同时恢复两个联合记录的函数。可是，如果仍能访问记录，并施加该耦合的伴随操作，则两个联合态都可以恢复到各自的空白记录输入。

这说明“不可恢复”必须带有访问限定：

$$
\text{不可由当前边缘恢复}
\ne
\text{在整个联合系统中不可逆}.
$$

对稳定经典现实的研究，因而不能只问“相干是否变成零”，还必须问：允许的后续操作是否包括记录寄存器、环境的某个子系统或联合控制？改变可访问范围，会改变哪些历史仍然能够影响未来。

<a id="entry-382"></a>

### 89.4 反复记录时，熵增是每一步相对熵的和

考虑一个固定的幺正矩阵 $U$，以及满足

$$
\rho_{k+1}
=
\operatorname{basisPinchingState}
\left(U\rho_kU^\dagger\right)
$$

的离散协议。项目中的 `entropy_production_coherence_deletion_identity` 证明每一步的熵差为

$$
\boxed{
S(\rho_{k+1})-S(\rho_k)
=
D\!\left(
U\rho_kU^\dagger
\middle\|
\operatorname{basisPinchingState}(U\rho_kU^\dagger)
\right)
\ge 0.
}
$$

并且对任意 $N$ 有望远镜求和：

$$
\boxed{
S(\rho_N)-S(\rho_0)
=
\sum_{k=0}^{N-1}
D\!\left(
U\rho_kU^\dagger
\middle\|
\operatorname{basisPinchingState}(U\rho_kU^\dagger)
\right).
}
$$

这里的非负性来自每一步去相位相对于幺正演化后状态的量子相对熵；幺正共轭本身保持 von Neumann 熵。于是，重复记录协议中的可见熵增加可以逐步结算为“本轮被删除的相干”之和。

这条公式同时给出一个停止条件：如果某一步的相对熵项为零，则该步的幺正后状态已经位于所选基底的去相位固定点；若所有后续步骤都保持这一条件，记录熵不再增加。反过来，固定点集合是经典对角态并不保证任意初态都会到达它；还需检查实际动力学是否持续把非对角分量送入被去相位的方向。

<a id="entry-383"></a>

### 89.5 Zeckendorf 只提供合法索引，不决定关联与熵

若把长度为 $L$ 的禁止相邻 `11` 合法串作为构型标签，并令

$$
d=F_{L+2},
$$

则可以把这些标签映射到一个 $d$ 维正交载体，再在其上定义 $\rho$、$U$、基底去相位和记录寄存器。此时第 88 节的容量守恒给出

$$
C(\mathcal E)+R(\mathcal E)=d^2-1=(F_{L+2})^2-1.
$$

但本节的互信息、相对熵和熵产生公式还需要额外指定：

$$
\text{构型到 Hilbert 基底的映射},
\quad
\text{记录耦合},
\quad
\text{幺正动力学},
\quad
\text{去相位基底}.
$$

Zeckendorf 权重本身不决定 $U$，也不决定记录 Gram 矩阵、互信息或相对熵。它只说明哪些有限构型作为离散载体是合法的，以及如何给这些构型提供规范编号。若更换局部约束，合法载体维数和适合的索引递推也会改变；若保留同一标签而更换记录耦合，关联谱和熵变化同样会改变。

因此，对“保留多少历史才能得到稳定经典现实”的当前回答应写成：

$$
\boxed{
\begin{aligned}
&\text{整体层：保留联合态中的记录关联；}\\
&\text{局部层：只保留给定任务可访问的边缘记录；}\\
&\text{动力学层：结算每一步相对熵和未来回流；}\\
&\text{编码层：用 Zeckendorf 组织合法构型，但不把编码当作动力学。}
\end{aligned}}
$$

“历史消失”于是被拆成三个可检验问题：边缘是否已经去相位、联合关联是否仍可访问、以及允许的后续操作是否能把关联重新转回目标读数。只有在指定实验族、访问范围和误差容限下，这三个问题都给出稳定答案时，才可以把该层记录称为有效的经典现实。

本节复用 `coherentCopyState_correlated_entry`、`marginalRight_coherentCopyState`、`marginalLeft_coherentCopyState`、`vonNeumannEntropy_coherentCopyState`、`coherent_copy_correlation_tax` 和 `entropy_production_coherence_deletion_identity`。关于“相对熵就是实际热力学熵产生”、任意 Zeckendorf 物理实现、无限环境中的恢复能力，以及对所有未来实验的经典闭合，仍需额外模型与证明；本节不把这些条件性组合推导冒充为仓库已有结论。

<a id="entry-384"></a>

## 追加锚（新终端）

<a id="section-90"></a>

## 90. 记录重叠、可区分性与复制边界

<a id="entry-386"></a>

### 90.1 记录重叠给出一条精确的可见性预算

设两个归一化纯记录为 $|r_0\rangle$ 和 $|r_1\rangle$，令

$$
c=\langle r_0|r_1\rangle,
\qquad
V=|c|,
\qquad
D=\sqrt{1-V^2}.
$$

项目中的 `pure_record_distinguishability_coherence_complementarity` 证明：

$$
\boxed{D^2+V^2=1.}
$$

这里的 $V$ 是两条记录之间仍保留的相干可见度；$D$ 是由这两个记录向量的重叠所定义的几何区分度。它们不是两个可以独立增加的预算：在记录向量已经归一化的条件下，提高一个就必然降低另一个。

两个端点尤其清楚：

$$
\begin{aligned}
&c=0
&&\Longrightarrow
&&D=1,\quad V=0;\\
&V=1
&&\Longrightarrow
&&D=0.
\end{aligned}
$$

第一种情形是正交记录；在允许相应投影测量时，它们可以完全区分。第二种情形在归一化向量的标准 Hilbert 空间几何中对应同一条量子态射线，只留下整体相位约定，不能提供区分信息。这里形式化结果直接保证的是 $V=1$ 时几何区分度为零。若 $D=1$，则 $c=0$，任何后续振幅乘上 $c$ 都被消除；若 $V=1$，几何区分度为零。

这把第 89 节的关联公式进一步具体化：记录 Gram 矩阵中的非对角元就是这种重叠。对每一对候选历史，$|R_{ij}|$ 越接近零，局部记录越能把它们分开；$|R_{ij}|$ 越接近一，越多相干仍可在联合演化中保留。不能只报告记录的数量，还要报告记录向量之间的重叠谱。

<a id="entry-387"></a>

### 90.2 完美复制只适用于正交或相同的历史

设 $U$ 是同一 Hilbert 空间张量平方上的复线性等距等价，并设三个向量都归一化：输入历史为 $\psi,\phi$，空白记录为 $b$。若同一个 $U$ 满足

$$
U(\psi\otimes b)=\psi\otimes\psi,
\qquad
U(\phi\otimes b)=\phi\otimes\phi,
$$

则 `no_cloning_inner_product_criterion` 给出

$$
\langle\phi|\psi\rangle
=
\langle\phi|\psi\rangle^2.
$$

因此

$$
\boxed{
\phi=\psi
\quad\text{或}\quad
\langle\phi|\psi\rangle=0.
}
$$

证明的核心只是等距映射保持内积，而张量积把重叠相乘。这个结果的适用范围必须保留：它针对同一个线性等距复制过程、同一个归一化空白记录和两个精确复制方程。它不是说任何形式的近似记录、带噪声记录或任务相关压缩都不可能。

对历史档案而言，结论是：任意两个非正交量子历史不能被一个固定的可逆过程无损复制成两份独立副本。若试图把每个历史都写入新的独立记录，就必须满足记录态之间的正交条件，或接受近似误差、改变任务、保留联合关联而不宣称已经产生两份副本。

<a id="entry-388"></a>

### 90.3 Zeckendorf 标签可以复制，标签上的任意叠加不能任意复制

若长度为 $L$ 的合法 Zeckendorf 字符串被实现为一组正交计算基态

$$
\{|w\rangle:w\in\mathcal W_L\},
$$

则对不同 $w\ne v$ 有

$$
\langle w|v\rangle=0.
$$

在这个离散基底上，受控复制可以把经典标签写入空白寄存器；这与第 90.2 节并不冲突，因为被复制的是一组彼此正交的基态。可是，对叠加态

$$
|\Psi\rangle=\sum_{w\in\mathcal W_L}a_w|w\rangle
$$

不能把同一个过程解释为对任意未知 $|\Psi\rangle$ 都实现

$$
|\Psi\rangle|0\rangle\longmapsto|\Psi\rangle|\Psi\rangle.
$$

线性演化会把基态复制协议延伸为纠缠的相干复制态，而不是右侧所写的非线性平方。于是，Zeckendorf 的合法性约束只决定可用的正交标签集合；它不能绕过量子态重叠的复制边界，也不能把标签复制自动升级为历史的独立物理副本。

<a id="entry-389"></a>

### 90.4 稳定经典记录需要区分“复制标签”和“保留关联”

由前两节可以把记录协议分成三种情形：

$$
\begin{aligned}
&|R_{ij}|=0
&&\Rightarrow&&
\text{该对历史可被当前记录完全区分；}\\
&0<|R_{ij}|<1
&&\Rightarrow&&
\text{记录获得部分区分，同时保留部分相干；}\\
&|R_{ij}|=1
&&\Rightarrow&&
\text{当前记录没有区分这对历史的能力。}
\end{aligned}
$$

第一种情形适合形成可复制的经典标签；第二种情形必须把后续相位、访问范围和恢复操作纳入模型；第三种情形若仍要预测两条历史的差异，就不能把当前记录当作充分状态。

因此，“稳定经典现实”不能定义为把所有历史都复制到无限多个寄存器。更精确的条件是：对指定目标实验族，相关历史已经落入可区分的记录扇区，且被省略的联合关联在预测视界内不会重新进入目标读数。正交复制解决的是一次无误标签任务；它不自动解决未来动力学闭合。

<a id="entry-390"></a>

### 90.5 与 Zeckendorf 刻度的组合边界

对合法构型集合 $\mathcal W_L$，Zeckendorf 数值只提供一个离散坐标

$$
\nu(w)=\sum_j F_{j+2}w_j.
$$

若记录耦合另行定义为 $|w\rangle\mapsto|r_w\rangle$，真正进入局部预测的是

$$
R_{wv}=\langle r_w|r_v\rangle,
$$

而不是 $\nu(w)-\nu(v)$ 本身。两个 Zeckendorf 数值相差很大，记录向量仍可能重合；两个数值相邻，也可能被特定耦合映射到正交记录。必须同时给出编码、记录态和允许操作，才能判断历史是否已经成为稳定的经典标签。

本节复用 `pure_record_distinguishability_coherence_complementarity` 与 `no_cloning_inner_product_criterion`。由它们得到的等式和正交/相同二分是 Lean 已证明的有限 Hilbert 空间结果；把它们推广到近似复制、带噪声环境、无限记录链或具体 Zeckendorf 里德伯动力学，仍需额外的通道模型和误差界。

<a id="entry-391"></a>

## 追加锚（新终端）

<a id="section-91"></a>

## 91. 局部边缘的相关盲区与历史容量

<a id="entry-393"></a>

### 91.1 双系统的无读相关扇区

设两个有限 Hilbert 因子的维数分别为 $m,n$，并在双系统的 trace-zero Hermitian 空间中区分三个子空间：第一因子的局部扇区 $L_A$、第二因子的局部扇区 $L_B$，以及相关扇区 $C$。`local_marginal_correlation_blind_spot` 给出它们的正交分解：

$$
\boxed{
L_A\oplus^{\perp}L_B\oplus^{\perp}C
=
\operatorname{bipartiteTraceZero}(m,n).
}
$$

完整局部边缘能够看到的方向数为

$$
\dim(L_A\oplus L_B)
=(m^2-1)+(n^2-1),
$$

而相关扇区的维数为

$$
\boxed{
\dim C=(m^2-1)(n^2-1).
}
$$

总的 trace-zero 方向数是 $(mn)^2-1$，所以相关盲区占比为

$$
\boxed{
\frac{\dim C}{\dim\operatorname{bipartiteTraceZero}(m,n)}
=
\frac{(m^2-1)(n^2-1)}{m^2n^2-1}.
}
$$

这里的“盲”有严格范围：$C$ 与两个局部扇区在 Hilbert—Schmidt 配对下正交，因此只使用完整的两个局部边缘时，$C$ 中的差异不会改变这些局部线性读数。它不表示相关差异在联合系统中不存在，也不表示任何允许联合操作的实验都无法恢复它。

<a id="entry-394"></a>

### 91.2 两个量子态可以有相同边缘而不同整体

项目同时构造两个二能级双系统状态。一个是 Bell 纯态密度矩阵 $\rho_{\mathrm{Bell}}$，另一个是只在 $00$ 与 $11$ 上各占一半的经典相关混合 $\rho_{\mathrm{cl}}$。它们满足

$$
\operatorname{Tr}_A(\rho_{\mathrm{Bell}})
=
\operatorname{Tr}_A(\rho_{\mathrm{cl}}),
\qquad
\operatorname{Tr}_B(\rho_{\mathrm{Bell}})
=
\operatorname{Tr}_B(\rho_{\mathrm{cl}}),
$$

但

$$
\rho_{\mathrm{Bell}}\ne\rho_{\mathrm{cl}}.
$$

Lean 还保留了两者的结构差异：Bell 密度矩阵的秩为 $1$，而经典相关混合不是幂等矩阵。因此，完整边缘读数相同并不意味着联合态相同；被局部观察删去的正是相关扇区中的信息。

这给第 89 节的“访问范围”提供了一个有限维反例：若只访问两个边缘，无法从边缘函数恢复这两种联合记录；若允许联合测量，则可以选择与相关扇区有非零配对的效果来区分它们。后半句是由正交分解得到的操作性组合解释，不是该定理额外证明了某个特定 POVM 的实现。

<a id="entry-395"></a>

### 91.3 两个量子比特的数值预算

取 $m=n=2$，则

$$
\dim\operatorname{bipartiteTraceZero}(2,2)=2^4-1=15,
$$

局部可见方向为

$$
(2^2-1)+(2^2-1)=6,
$$

相关盲区为

$$
(2^2-1)(2^2-1)=9,
$$

占比为

$$
\frac{9}{15}=\frac35.
$$

这说明“两个局部系统各自都被完整读出”仍只覆盖 $6$ 个独立的 trace-zero 方向；剩下的 $9$ 个方向不是两个边缘容量的简单相加可以得到的。它们需要联合效果、联合动力学，或保留跨系统记录。

<a id="entry-396"></a>

### 91.4 与 Zeckendorf 载体的边界

若要把本节代入 Zeckendorf 合法载体，必须先给出双系统分解。例如可以额外假设

$$
 m=F_{L_A+2},
\qquad
 n=F_{L_B+2},
$$

并把两组合法构型分别实现为两个正交载体。此时才可形式上写出

$$
\dim C
=
\bigl(F_{L_A+2}^2-1\bigr)
\bigl(F_{L_B+2}^2-1\bigr).
$$

单独知道一个长度为 $L$ 的合法空间有 $F_{L+2}$ 个标签，并不能自动把它分解成维数为 $m$ 与 $n$ 的两个物理子系统；更不能从单一 Fibonacci 标签数直接推出相关扇区的维数。编码、张量分解和局部读出必须分别指定。

因此，本节把“历史保留多少”再收紧一层：如果任务只访问局部边缘，相关扇区可以暂时留在不可见残差中；如果未来任务允许联合操作，相关扇区必须进入目标闭包，或者给出忽略它所造成的误差界。

本节复用 `local_marginal_correlation_blind_spot`。其正交分解、维数公式和 Bell/经典相关混合的等边缘反例是 Lean 已证明的有限维结果；把相关盲区解释为具体实验中的不可恢复信息、把 Zeckendorf 标签实现为双系统载体，以及把联合效果提升为物理仪器，仍需额外模型与验证。

<a id="entry-397"></a>

## 追加锚（新终端）

<a id="section-92"></a>

## 92. 完备互补上下文中的碰撞统计与纯度

<a id="entry-399"></a>

### 92.1 互补记录把算子信息压缩成碰撞和

设系统维数为 $n+1$，有 $n+2$ 个秩一记录上下文。每个上下文都满足记录测量条件，并假设同一上下文内的投影正交、不同上下文之间满足

$$
\operatorname{Tr}(P_{l,j}P_{k,r})
=
\begin{cases}
\delta_{jr},&l=k,\\[2pt]
\dfrac{1}{n+1},&l\ne k.
\end{cases}
$$

这是一组有限维的完备互补上下文条件。`complete_context_collision_conservation` 在这些假设下证明算子恒等式

$$
\boxed{
\sum_{l,j}P_{l,j}\otimes P_{l,j}
=I+\operatorname{Swap}.
}
$$

右侧的交换算子说明：这些上下文的联合记录不只是把每个结果标签分别列出来，而是在二次张量层面覆盖了交换对称的方向。它因此能够把状态的二次信息投影到一个可计算的碰撞统计量。

<a id="entry-400"></a>

### 92.2 碰撞概率直接读出纯度

对满足正半定和单位迹条件的密度矩阵 $\rho$，令

$$
 p_{l,j}=\operatorname{basisProbability}(\rho,\text{context }l,j).
$$

同一定理给出

$$
\boxed{
\sum_{l,j}p_{l,j}^{\,2}
=
1+\operatorname{Re}\operatorname{Tr}(\rho^2).
}
$$

因此，在这组完备互补上下文中，所有结果概率的平方和不是任意的“记录总量”，而是状态平方迹的一个平移。若另有条件使 $\operatorname{Tr}(\rho^2)=1$，则碰撞和等于 $2$；一般情况下仍应保留右侧的平方迹，而不能仅凭上下文数量把状态称为纯态。

这条关系把第 89 节的关联记录和第 91 节的相关盲区连接起来：单个局部边缘只能看到局部扇区，而完备互补上下文的整体碰撞和可以对全局二次结构敏感。它仍然不是说一次实验同时读取了所有不相容上下文；这些概率来自在可重复制备上分别执行各上下文，再把统计结果组合起来。

<a id="entry-401"></a>

### 92.3 记录细化的代价与收益

完备上下文增加了可访问的读出方向，但它并没有免费消除历史成本。每个上下文仍有自己的结果标签和实验设置；要估计碰撞和，需要在相应设置下积累统计数据。若只保留一个上下文的结果，通常不能从该单一切面恢复右侧的完整平方迹；若保留全部上下文的概率表，才可以使用上式形成纯度证书。

所以“保留多少历史”在这里有两个不同层次：

$$
\begin{aligned}
&\text{状态方向预算：}&d^2-1&\text{ 个连续 trace-zero 方向；}\\
&\text{碰撞证书预算：}&\sum_{l,j}p_{l,j}^2&\text{ 所需的多上下文统计记录。}
\end{aligned}
$$

第二项是一个任务特定的标量证书，不等于保存了完整密度矩阵，也不等于已经构造出一个无记忆的经典状态。不同状态可以共享某个单一统计量；若任务还要求预测未来效果，仍需检查第 86 节的目标闭包和残差条件。

<a id="entry-402"></a>

### 92.4 Zeckendorf 载体只能作为附加实现假设

如果要把这条碰撞守恒放到 Zeckendorf 合法空间上，必须先选择一个 $L$，令合法构型数满足

$$
 d=F_{L+2},
$$

再额外构造一族作用在该 $d$ 维空间上的 $d+1$ 个互补秩一上下文，并验证每对投影的重叠条件。Zeckendorf 递推本身只提供 $d$ 个离散标签；它不自动产生完备上下文、交换算子恒等式或碰撞统计。

相应地，若系统被分成两个载体，必须同时满足张量维数分解 $d=mn$，并分别说明局部上下文和联合上下文。第 91 节的相关扇区不会因为给每个构型附上 Fibonacci 编号就自动消失。

本节复用 `complete_context_collision_conservation`。算子恒等式和碰撞—平方迹关系是在明确的有限维互补上下文假设下由 Lean 证明的；上下文在物理实验中的可实现性、有限样本误差、与热力学熵的关系，以及 Zeckendorf 载体上具体构造这些上下文，仍需额外模型与误差分析。

<a id="entry-403"></a>

## 追加锚（新终端）

<a id="section-93"></a>

## 93. 算术权重、对角固定点与有效热记录

<a id="entry-405"></a>

### 93.1 固定点先由记录基底决定

设 $B$ 是 $d$ 维 Hilbert 空间上的秩一记录上下文，并假设其投影族满足 `IsRecordMeasurement`。项目中的 `basis_measurement_eq_self_iff` 给出固定点刻画：

$$
\boxed{
\operatorname{basisMeasurement}_B(A)=A
\iff
A\in\operatorname{diagonalSubspace}(B).
}
$$

这条等价式的重点不是某个特殊权重，而是记录机制先选定了一个对角子空间。被保留下来的信息是该上下文中的经典对角方向；其余非对角方向不会成为这个记录通道的固定信息。

因此，“经典现实”在这个有限模型中的第一层含义可以写成：

$$
\text{稳定记录}
=
\text{被指定记录通道固定的算子子空间中的元素}.
$$

它仍然是相对于上下文 $B$ 的定义。更换记录基底，会更换 diagonalSubspace，也会更换哪些差异被视为稳定记录。

<a id="entry-406"></a>

### 93.2 有限 zeta 权重自动落入这个固定点

对有限索引集 $S\subseteq\operatorname{Fin}(d)$，项目定义

$$
Z_s(S)=\sum_{n\in S}(n+1)^{-s},
$$

并构造加权算子

$$
\tau_{B,s,S}
=
\sum_{n\in S}
\frac{(n+1)^{-s}}{Z_s(S)}P_{B,n}.
$$

`zeta_thermal_state_mem_diagonal` 证明

$$
\tau_{B,s,S}\in\operatorname{diagonalSubspace}(B),
$$

所以 `zeta_thermal_state_pinching_fixed` 给出

$$
\boxed{
\operatorname{basisMeasurement}_B(\tau_{B,s,S})
=\tau_{B,s,S}.
}
$$

这里的“thermal”只表示一种有限 zeta 权重的构造命名。当前定理证明的是它属于指定上下文的对角子空间并被该测量固定；它没有单独证明 $Z_s(S)\ne0$、正迹归一化、某个 Hamiltonian 的 Gibbs 形式，或与实验温度的对应关系。若要把 $\tau_{B,s,S}$ 当作物理密度态，还必须另加这些条件。

<a id="entry-407"></a>

### 93.3 固定不等于由动力学达到

第 89 节已经区分了去相位后的固定点与实际熵产生；本节提供一个算术权重的具体固定点例子，但不改变这个边界：

$$
\operatorname{basisMeasurement}_B(\tau)=\tau
\quad\not\Rightarrow\quad
\rho_k\longrightarrow\tau.
$$

要得到趋近结论，必须指定动力学 $\Phi$，并证明 $\tau$ 是 $\Phi$ 的吸引子，或者至少证明从给定初态出发的迭代误差界。固定点等式只说明“如果已经在这个记录子空间中，当前记录不会再改变它”。

同样，两个不同的权重参数 $s$ 或两个不同的有限集 $S$ 可以给出不同的稳定对角状态；记录通道本身不会从固定点等价式中选出唯一的 $s$。选择参数属于模型或实验标定，而不是 Zeckendorf 编码的逻辑后果。

<a id="entry-408"></a>

### 93.4 与 Zeckendorf 刻度的关系

若把有限合法 Zeckendorf 构型 $w\in\mathcal W_L$ 映射到上下文 $B$ 的正交基向量，并令索引集 $S$ 对应这些构型，则可以在 $	au_{B,s,S}$ 中使用 Fibonacci 标签、素数指数或其他离散坐标作为权重输入。可是，当前 zeta 固定点定理只使用有限索引 $n$、秩一投影和对角子空间；它没有证明

$$
(n+1)^{-s}
$$

必须等于某个 Fibonacci 能量，也没有证明 Zeckendorf 数值就是热力学能量。两者的安全连接是：Zeckendorf 提供合法离散索引，zeta 权重提供一种可计算的对角加权，记录测量负责规定这些加权态是否稳定可读。

因此可以把三种角色分开：

$$
\boxed{
\begin{aligned}
&\text{编码：}&w&\longmapsto\text{合法离散标签};\\
&\text{加权：}&n&\longmapsto (n+1)^{-s};\\
&\text{记录：}&B&\longmapsto\operatorname{diagonalSubspace}(B)\text{ 与其固定点}.
\end{aligned}}
$$

只有在额外给出载体映射、归一化和动力学之后，才能讨论这些层是否共同形成一个可预测的有效热记录。

本节复用 `basis_measurement_eq_self_iff`、`zeta_thermal_state_mem_diagonal` 和 `zeta_thermal_state_pinching_fixed`。Lean 已证明的是有限秩一记录上下文中的对角固定性；物理 Gibbs 态、热平衡、唯一吸引子、Zeckendorf 能量解释和无限 zeta 极限仍需额外假设与证明。

<a id="entry-409"></a>

## 追加锚（新终端）

<a id="section-94"></a>

## 94. 局部动力学不能自动填补相关盲区

<a id="entry-411"></a>

### 94.1 局部扇区在迭代下保持封闭

继续使用第 91 节的双系统分解。令

$$
L=L_A\oplus L_B
$$

表示两个局部扇区的和，令 $C$ 表示相关扇区。设 Heisenberg 演化是一个实线性映射

$$
\mathsf H:
\operatorname{BipartiteHermitian}(m,n)
\longrightarrow
\operatorname{BipartiteHermitian}(m,n),
$$

并假设

$$
\mathsf H(L)\subseteq L.
$$

`local_dynamics_no_tomography` 证明对任意离散时间 $t$，

$$
\boxed{
\mathsf H^{t}(L)\subseteq L.
}
$$

这是一个纯粹的迭代闭合结论：如果一步演化不离开局部可见空间，那么重复应用它也不会从局部方向产生新的相关方向。

<a id="entry-412"></a>

### 94.2 局部读数不能靠自身迭代完成联合层析

同一定理还给出更强的交集结论：若 $x\in L$ 且某次迭代同时落入相关扇区，

$$
\mathsf H^t x\in C,
$$

则

$$
\boxed{
\mathsf H^t x=0.
}
$$

原因是 $L$ 与 $C$ 在 Hilbert—Schmidt 几何下正交；保持局部扇区的迭代结果既属于 $L$，又属于 $C$，只能落在零交集。这把“局部边缘看不见相关历史”改成了一个动力学判据：只使用保持 $L$ 的局部 Heisenberg 操作，不能把相关扇区拉回局部坐标，也不能用局部数据完成联合层析。

这里的条件非常具体。定理没有说任何物理动力学都保持 $L$，也没有说相关扇区对所有联合操作都不可见；它只约束满足上述线性不变性假设的演化族。只要加入一个把局部方向送入相关方向的联合相互作用，或者允许直接测量 $C$ 中的效果，结论的适用范围就改变。

<a id="entry-413"></a>

### 94.3 对“保留多少历史”的影响

第 91 节给出相关扇区的维数

$$
\dim C=(m^2-1)(n^2-1).
$$

第 94 节说明：若未来实验族的 Heisenberg 闭包仍满足 $\mathsf H(L)\subseteq L$，那么这些相关方向不会被局部动力学主动暴露。对只回答局部目标的问题，可以把 $C$ 留在残差空间；对需要联合目标的任务，则必须在实验族中加入能够离开 $L$ 的操作，或直接保留联合记录。

因此，历史预算不只由静态维数决定，还由动力学的扇区不变性决定：

$$
\boxed{
\text{局部预算足够}
\iff
\text{目标闭包仍在 }L\text{ 中};
\qquad
\text{联合目标需要 }C\text{ 的访问或生成机制}.
}
$$

这个判据与第 86 节的目标闭包条件相容，但不能替代对具体目标族和误差容限的计算。若演化只近似保持 $L$，则需要额外的 Lipschitz 或泄漏范数来给出近似版本；当前定理只给出精确离散不变性。

<a id="entry-414"></a>

### 94.4 Zeckendorf 双载体的边界

若两个局部载体分别由 Zeckendorf 合法空间实现，必须先给出

$$
 m=F_{L_A+2},
\qquad
 n=F_{L_B+2},
$$

以及一个实际作用在 $m\times n$ 联合空间上的 Heisenberg 映射。只有在验证该映射保持 $L_A\oplus L_B$ 后，才能应用上述闭合结论。Fibonacci 计数本身既不保证局部扇区不变，也不保证相关扇区一定能被某个物理相互作用访问。

本节复用 `local_dynamics_no_tomography`。Lean 已证明的是实线性、精确扇区保持下的迭代闭合和零交集结论；近似局部动力学、开放系统通道、有限样本误差和具体 Zeckendorf Hamiltonian 仍需额外模型。

<a id="entry-415"></a>

## 追加锚（新终端）

<a id="section-95"></a>

## 95. 有限移位记录的余弦误差地板

第 81 节已经给出有限移位记录中以 $|\gamma(\ell)|$ 表示的恢复下界。本节的新增内容是对同一个特定通道证明有限窗口的余弦估计，从而把未知的自相关系数替换成显式的标签间距和窗口长度界。

<a id="entry-417"></a>

### 95.1 一个可计算的有限记录通道

设 $c:\mathbb Z\to\mathbb C$ 只支撑在有限窗口 $0,1,\ldots,N$，并满足

$$
\sum_{k\in\mathbb Z}|c_k|^2=1.
$$

给每个系统标签 $i$ 一个整数位置 $q_i$，定义移位相关函数

$$
\gamma(t)
=
\sum_{k\in\mathbb Z}c_{k+t}\,\overline{c_k}.
$$

`finite_record_cosine_obstruction` 构造了一个具体的有限记录通道 $C$。在它的系统边缘作用上，矩阵元按标签差异衰减为

$$
\boxed{
\Lambda(A)_{ij}
=
\gamma(q_i-q_j)A_{ij}.
}
$$

这把记录重叠写成了一个离散自相关函数：对角元不变，标签间距为 $t$ 的相干项乘上 $\gamma(t)$。这里的 $C$ 是定理在给定有限窗口、整数标签和记录向量后构造出的特定通道；不能把这个存在性结论改写成任意有限记录装置都具有同一形式。

<a id="entry-418"></a>

### 95.2 任意系统端恢复都有一个最坏误差下界

若存在一对标签满足

$$
q_i-q_j=\ell\ne0,
$$

对任意只作用在系统端的恢复通道 $R$，定理对所有输入密度态取最坏误差上确界，得到

$$
\boxed{
\frac{1-|\gamma(\ell)|}{2}
\le
\sup_{\rho\in\mathrm{DensityState}}
D\!\left(R(C(\rho)),\rho\right).
}
$$

更精确地，Lean 结论把左侧误差集合写成一个非空有界集合的上确界，并同时证明它与对应的矩阵迹范数误差集合相等。这个量是“对所有输入状态的最坏误差”，不是说每个输入态都达到该下界，也不是说该下界在所有通道中都是最佳常数。

下界的来源是一个成对的相干见证：可以选取只在 $i,j$ 两个标签上有相反相位的两个纯态，它们输入时迹距离为 $1$，记录通道后只剩下由 $\gamma(q_i-q_j)$ 缩放的非对角差异；迹距离收缩和三角不等式迫使任意恢复保留这项误差。

<a id="entry-419"></a>

### 95.3 有限窗口给出严格的余弦地板

令

$$
 d=|\ell|,
\qquad
 m=\left\lfloor\frac{N}{d}\right\rfloor.
$$

`coefficient_gamma_le_cosine` 对有限支撑的每个非零整数移位给出

$$
|\gamma(\ell)|
\le
\cos\!\left(\frac{\pi}{m+2}\right).
$$

因此 `finite_record_cosine_obstruction` 进一步得到

$$
\boxed{
\frac{1-\cos\!\left(\frac{\pi}{m+2}\right)}{2}
\le
\sup_{\rho}
D\!\left(R(C(\rho)),\rho\right),
\qquad
\frac{1-\cos\!\left(\frac{\pi}{m+2}\right)}{2}>0.
}
$$

余弦上界来自把整数索引按模 $d$ 分成 residue blocks；每个长度为 $m+1$ 的实非负范数序列满足最近邻二次型的有限路径上界，再把各块的质量相加。它是统一上界，由此产生严格正的误差地板；当前定理没有为每个 $c$ 提供达到该上界的等号见证，因此不把这个恢复下界称为普适 sharp 常数。

两个边界值得保留：如果所有 $q_i$ 都相同，则不存在非零标签差，定理的量化条件为空；如果 $d>N$ 或 $N=0$，则 $m=0$，地板为

$$
\frac{1-\cos(\pi/2)}{2}=\frac12.
$$

当 $m$ 增大时，地板可以变小；这只说明更长的有限窗口可以降低该特定模型的下界，不表示已经得到无限记录极限或任意通道的无误恢复。

<a id="entry-420"></a>

### 95.4 与 Zeckendorf 历史预算的关系

若把合法 Zeckendorf 构型映射为整数标签 $q_i$，则本节告诉我们：标签间距、记录窗口长度 $N$ 和自相关 $\gamma$ 共同决定系统端恢复成本。仅增加合法标签的数量并不能保证历史可恢复；还必须指定这些标签如何嵌入有限记录序列，以及记录寄存器是否仍可被联合访问。

因此，对一个给定的非零间距 $\ell$，可以把

$$
\varepsilon_{N,\ell}
=
\frac{1-\cos\!\left(\frac{\pi}{\lfloor N/|\ell|\rfloor+2}\right)}{2}
$$

作为该有限移位记录模型中的保守恢复预算。它是标签族和记录协议的函数，不是 Zeckendorf 数值本身的普适误差，也不是对所有环境或恢复操作的定律。

本节复用 `finite_record_cosine_obstruction`、`coefficient_gamma_le_cosine` 和 `finite_record_recovery_error_lower_bound`。Lean 已证明的是有限支撑、归一化记录序列、整数标签和系统端恢复通道下的具体下界；联合访问记录环境、近似无限窗口、其他编码和物理 Hamiltonian 仍需分别建模。

<a id="entry-421"></a>

## 追加锚（新终端）

<a id="section-96"></a>

## 96. 静态效果相同，仪器历史仍可不同

前面的不完整观察者结果已经说明：当前效果族存在正交残差时，不同密度态可以拥有完全相同的单次读数。本节补上一个更具体的物理桥：即使当前 POVM 的每个效果都完全相同，**仪器在分支后怎样更新状态**仍会改变下一次读数。

<a id="entry-423"></a>

### 96.1 同一个 POVM 不决定同一个仪器

在一个量子比特上，令

$$
P_0=|0\rangle\langle0|,
\qquad
P_1=I-P_0,
\qquad
X=|0\rangle\langle1|+|1\rangle\langle0|.
$$

考虑两组单 Kraus 分支：

$$
K_b=P_b,
\qquad
L_b=XP_b,
\qquad b\in\{0,1\}.
$$

它们的静态效果完全相同，因为

$$
K_b^\dagger K_b=P_b,
$$

而

$$
L_b^\dagger L_b
=P_bX^\dagger XP_b
=P_b.
$$

两组效果都满足

$$
\sum_{b=0}^1P_b=I.
$$

因此，只看当前一次测量的 outcome 概率，无法区分这两台仪器。

<a id="entry-424"></a>

### 96.2 下一步联合统计却相反

取共同初态 $$\rho=P_0$$，并比较第一步得到 $$b=0$$ 后、第二步读取效果 $$P_1$$ 的概率。

对于第一台仪器，分支态为

$$
K_0\rho K_0^\dagger=P_0,
$$

所以第二步的未归一化权重为

$$
\operatorname{Tr}(P_1P_0)=0.
$$

对于第二台仪器，分支态为

$$
L_0\rho L_0^\dagger
=XP_0X^\dagger
=P_1,
$$

所以第二步权重为

$$
\operatorname{Tr}(P_1P_1)=1.
$$

项目定理 `same_effects_different_two_step_joint_law` 已在有限矩阵中同时证明了四件事：两组分支效果逐 outcome 相等、两组效果都归一化，以及上述第二步概率分别为 $$0$$ 和 $$1$$。

于是得到一个比“当前边缘读数不完整”更强的结论：

$$
\boxed{
\text{相同 POVM 效果}
\not\Rightarrow
\text{相同后续过程}.
}
$$

静态效果只记录 $$K_b^\dagger K_b$$；它没有记录 Kraus 分支留下的状态变换。后续实验访问的正是这部分历史。

<a id="entry-425"></a>

### 96.3 需要保留的不是全部过去，而是分支更新

设当前记录只保存 outcome $$b$$，却丢弃分支后的更新算子。上面的两台仪器在当前记录层完全相同，但它们的下一步响应不同。因此，把对象压成

$$
\text{当前 outcome 分布}
$$

不足以支撑未来预测；至少要保留下面三者之一：

$$
\boxed{
\text{分支更新 }\mathcal J_b,
\quad
\text{足以模拟未来的预测摘要},
\quad或
\quad
\text{可访问的联合记录}.
}
$$

这正是“保留多少历史”的操作性版本：历史预算由未来实验能否重建分支后的状态决定，而不是由已经读出的标签数量决定。若允许的未来目标只属于当前效果的线性张成，已有的 `target_prediction_sufficiency` 可以给出签名充分性；若目标包含分支更新产生的新方向，则必须扩大到相应的序列效果或 Heisenberg 闭包。

<a id="entry-426"></a>

### 96.4 与 Zeckendorf 构型的接法

把 Zeckendorf 合法字串 $$w$$ 当作系统标签时，静态读出可以先定义为

$$
P_w=|w\rangle\langle w|,
$$

但这只指定了“读到哪个构型”。若构型读出后还允许执行条件更新 $$\mathcal J_w$$，则未来统计由

$$
E_{w_1\cdots w_n}
=
\mathcal J_{w_1}^*\cdots
\mathcal J_{w_n}^*(I)
$$

决定，而不由 Zeckendorf 数值 $$a(w)$$ 单独决定。不同的 $$\mathcal J_w$$ 可以共享相同的单步效果，却产生不同的多步响应。

因此，Zeckendorf 继续承担离散构型的合法编号；仪器分支和后续动力学承担历史如何回流。要声称某个合法字串的当前标签已经足够，必须先证明所有允许的未来词效果都由该标签因子化，或给出未因子化部分的误差界。

本节复用 `same_effects_different_two_step_joint_law`，并与已有的 `target_prediction_sufficiency`、`unified_sequential_kernel` 和 `all_future_statistics_sufficiency` 相接。Lean 已证明的是明确二能级单 Kraus 仪器的有限矩阵反例；它没有证明任意 POVM 都具有该差异，也没有替具体 Zeckendorf Hamiltonian 选择唯一的分支更新。

<a id="section-97"></a>

## 97. 用反向搜索计算最早未来分离深度

第 76 节给出了有限未来关系塔的稳定深度，但没有指定怎样从一个具体的有限更新表中计算每一对状态的首次分离时刻。项目的 `reverse_bfs_correct_and_quadratic` 提供了一个直接算法。

<a id="entry-428"></a>

### 97.1 定义成对的未来分离距离

设 $$Y$$ 是有限状态集，

$$
\tau:Y\to Y,
\qquad
q:Y\to O
$$

分别是确定性更新和当前读出。对有序状态对 $$(x,y)$$，定义

$$
\delta(x,y)
=
\min\left\{n\in\mathbb N:
q(\tau^n x)\ne q(\tau^n y)\right\},
$$

若不存在这样的时刻则记为 $$\delta(x,y)=\infty$$。这正是源码中的 `exactSeparationDepth`：它返回 `some n` 或 `none`，而不是把永远不可分的状态强行赋予一个有限距离。

$$
\boxed{
\delta(x,y)=\infty
\iff
x,y\text{ 对全部未来读数保持等价}.
}
$$

因此，稳定对象的边界可以按对区分：有限距离表示还需要保留一个有限未来窗口，$$\infty$$ 表示在指定更新和读出下无需再区分。

<a id="entry-429"></a>

### 97.2 反向 BFS 的正确性

把状态对写成一个成对节点

$$
(x,y)\longmapsto(\tau x,\tau y).
$$

先把当前读数不同的节点放入源集合：

$$
M_0
=\{(x,y):q(x)\ne q(y)\}.
$$

再沿成对更新边反向扩张：

$$
M_{k+1}
=
M_k
\cup
\left\{(x,y):(\tau x,\tau y)\in M_k\right\}.
$$

第 $$k$$ 层恰好包含那些在不超过 $$k$$ 步的未来某个时刻会分离的状态对。因而反向搜索首次访问层数满足

$$
\operatorname{reverseBfsDistance}(x,y)
=
\delta(x,y).
$$

这不是启发式搜索；Lean 定理逐对证明了它与源语义 `exactSeparationDepth` 的相等。

<a id="entry-430"></a>

### 97.3 历史预算的可计算上界

显式保存每个有序状态对的一条反向边，边数恰为

$$
|Y|^2.
$$

项目定理给出

$$
\boxed{
T\le 2|Y|^2,
\qquad
S\le 3|Y|^2,
}
$$

其中 $$T$$ 是该显式表和逐对访问的单位成本上界，$$S$$ 是边表、距离表和队列的存储上界。这个界没有使用收缩率或概率近似；它只依赖有限状态和确定性更新。

若所有有限的 $$\delta(x,y)$$ 中取最大值

$$
H_*=
\max\{\delta(x,y):\delta(x,y)<\infty\},
$$

那么观察到 $$H_*$$ 的未来窗口后，所有本来会被分开的状态对都已经分开；剩下的对在整个未来中保持同一读数。若不存在任何分离对，可约定 $$H_*=0$$。

这给出“需要保留多少历史”的一个可执行版本：在这个经典有限模型里，保留到 $$H_*$$ 就足够完成指定读出族的未来分类；不需要保留每一条更长历史。

<a id="entry-431"></a>

### 97.4 Zeckendorf 窗口与量子边界

若合法 Zeckendorf 构型集 $$\mathcal W_L$$ 被明确赋予

$$
\tau:\mathcal W_L\to\mathcal W_L,
\qquad
q:\mathcal W_L\to O,
$$

则

$$
|Y|=|\mathcal W_L|=F_{L+2}
$$

代入上面的算法预算，得到二次于合法构型数量的校准成本。这里的 $$F_{L+2}$$ 只是载体大小；$$H_*$$ 仍由实际更新和读出表决定。

这条反向 BFS 结论属于有限确定性模型。对量子通道，状态空间通常是连续的，且未来区分可能是概率差异而非精确标签不等式；此时应使用前面的效果闭包、预测投影或误差距离，而不能把 $$|Y|^2$$ 的枚举界直接宣称为量子记忆复杂度。

本节复用 `reverse_bfs_correct_and_quadratic`。Lean 已证明的是有限状态、确定性更新、有限读出字母表下的精确分离深度与预算；Zeckendorf 映射、量子概率阈值和噪声鲁棒版本仍需另行指定。

<a id="entry-432"></a>

## 追加锚（新终端）

<a id="section-98"></a>

## 98. 占据历史链的精确振幅与最小记忆债务

第 97 节处理有限确定性状态表的未来分离。另一条更接近“历史怎样被压缩”的项目结果来自 `SequentialOccupationHistory`：它把一个有限占据多重集的逐步生成写成量子等距链，并直接计算每个切口必须保留的记忆维数。

<a id="entry-434"></a>

### 98.1 边界不是标签，而是部分历史

给定有限多重集 $$a$$，令 $$\operatorname{Boundary}(a,t)$$ 表示从 $$a$$ 中取出恰好 $$t$$ 个占据的部分历史。若当前边界为 $$b$$，下一步加入符号 $$i$$ 的合法条件是

$$
\operatorname{count}_b(i)<\operatorname{count}_a(i).
$$

项目定义转移矩阵

$$
N_t(i,c;b)
=
\begin{cases}
\sqrt{\dfrac{\operatorname{count}_{a-b}(i)}{|a|-t}},
&c=b+\{i\},\\[6pt]
0,&\text{否则}.
\end{cases}
$$

它保留了“哪些前缀历史仍可继续”以及“剩余占据给每个后继多少振幅”两种信息。对 $$t<|a|$$，Lean 定理 `next_step_gram` 给出

$$
\boxed{
N_t^\dagger N_t=I.
}
$$

所以每个合法一步都是等距的；`next_step_quantum_channel` 进一步构造了相应的有限维量子通道。这里的等距性不是说记忆已经被压成一个标量，而是说这一步在保留的边界载体上不丢失内积。

<a id="entry-435"></a>

### 98.2 多步收缩精确等于占据扇区振幅

对一个词 $$w$$，把所有合法边界路径的局部转移振幅相乘并求和，得到 `contraction`。项目定理 `contraction_eq_sector` 证明：当剩余长度与切口满足

$$
|a|=t+n,
$$

时，逐步收缩恰好等于占据扇区向量的分量：

$$
\boxed{
\operatorname{contraction}(a,n,t,w,b)
=
\operatorname{sectorVector}_n(a-b,w).
}
$$

从初始空边界出发，`history_sequential_preparation` 因而给出整个合法占据历史的精确制备振幅。这个等式把“历史求和”落实为有限矩阵乘法；中间边界是被保留的历史接口，末端扇区向量是完整输出。

<a id="entry-436"></a>

### 98.3 每个切口都有一个不可绕开的秩下界

把长度 $$t+s$$ 的完整振幅按切口拆成前缀和后缀，定义系数矩阵 $$C_a^{t,s}$$。任意一个有限链若能精确产生同一个扇区振幅，`sequential_coefficient_factorization` 给出

$$
C_a^{t,s}=P_tQ_s,
$$

其中中间指标空间就是该切口的 bond carrier。因此

$$
\operatorname{rank}(C_a^{t,s})
\le
\dim(\text{bond at }t).
$$

项目进一步把扇区系数矩阵的秩写成边界数量，得到 `sequential_memory_necessity`：

$$
\boxed{
|\operatorname{Boundary}(a,t)|
\le
\dim(\text{任何精确链在切口 }t\text{ 的记忆} ) .
}
$$

这是一条比“历史越长，内存越多”更精确的说法。真正的债务由前缀与后缀振幅的线性秩决定；大量字面不同的历史如果在系数矩阵中线性相关，可以共享记忆，而线性独立的边界不能被同一个更小的切口载体精确表示。

<a id="entry-437"></a>

### 98.4 5040 的精确实例

项目中的 `occupation5040` 与算术卷中的 5040 具有同一数值对象，但两者承担的编码角色不同。算术卷给出

$$
5040=2^4\cdot3^2\cdot5\cdot7
$$

及其 Zeckendorf 指数行；量子占据链把一个具体多重集的逐步历史写成振幅链。对这个占据多重集，源码证明

$$
|a|=8,
$$

并且所有精确制备链的最大 bond 都满足

$$
\boxed{
\max_t\dim(\text{bond at }t)\ge12.
}
$$

`history_5040_minimum_maximum_bond` 证明下界可达；`history_5040_occupation_chain_attainment` 同时给出链长为 $$8$$、最大 bond 为 $$12$$，并且每个长度八的词振幅都精确等于对应扇区向量。

因此，这个实例给出一个完整的“约束—历史—量子记忆”数值链：

$$
\text{固定占据约束}
\longrightarrow
\text{合法边界族}
\longrightarrow
\text{切口秩}
\longrightarrow
\text{最小记忆 }12.
$$

但必须保留编码边界：源码没有证明 Zeckendorf 合法字串空间与这个 occupation boundary 空间同构，也没有证明 12 是所有能完成同一物理任务的任意量子协议的普适记忆维数。它是该多重集、该精确振幅目标和该有限链模型下的最小最大 bond。

<a id="entry-438"></a>

### 98.5 对“稳定经典现实”的补充

这条结果把前面的预测闭合条件再细化了一层。若只要求当前概率标签，可能只需保存一个粗读数；若要求保留完整后续振幅，则每个切口必须保存足以承载系数矩阵秩的边界信息。两者对应不同任务：

$$
\text{标签预测任务}
\not\equiv
\text{完整相干历史制备任务}.
$$

Zeckendorf 可以继续提供合法构型的离散坐标，occupation chain 则给出在一个具体相干任务中这些历史怎样组合、怎样跨切口传输。只有把两者之间的编码映射、目标振幅和允许误差明确写出，才能把 Fibonacci 构型数量转换成实际量子记忆预算。

本节复用 `next_step_gram`、`next_step_quantum_channel`、`contraction_eq_sector`、`sequential_memory_necessity`、`minimum_maximum_bond_characterization` 和 `history_5040_minimum_maximum_bond`。Lean 已证明的是有限多重集占据链的等距性、精确收缩和切口下界；Zeckendorf—occupation 同构、噪声容错记忆以及任意开放系统中的最优压缩仍是未完成接口。

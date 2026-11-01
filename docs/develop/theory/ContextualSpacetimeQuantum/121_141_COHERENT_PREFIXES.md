# 情境时空算术的量子扩展：共同前缀、活动记忆与端点纠缠

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](099_120_CORRELATION_AND_INSTRUMENTS.md) · [续卷](142_158_REPORTS_AND_OBSERVERS.md)

<a id="section-121"></a>

## 121. 记录接口的 Blackwell 偏序与缺陷复合

第 120 节用过程 diamond 缺陷控制任意后续量子决策风险。本节固定一个历史参数集，研究不同记录接口之间的可模拟关系：若较粗记录可以由较细记录通过与历史无关的退化得到，则较细记录对所有固定任务都不劣；若只能近似退化，则缺陷沿记录链次可加。这给“保留多少历史”提供一个偏序，而不是单一标量。

<a id="entry-577"></a>

### 121.1 经典记录的 Blackwell 预序

设有限历史集为 $H$，有限记录集为 $Y,Z$。记录接口是条件概率核

$$
E(y\mid h),
\qquad
F(z\mid h),
$$

其中对每个 $h$ 有 $\sum_yE(y\mid h)=\sum_zF(z\mid h)=1$。随机退化核 $K(z\mid y)$ 作用为

$$
(K E)(z\mid h)=\sum_yK(z\mid y)E(y\mid h).
$$

定义 Blackwell 预序

$$
E\succeq_B F
\quad\Longleftrightarrow\quad
\exists K\;F=K\circ E.
$$

它是自反且传递的预序：自反性取恒等核；若 $F=K_1E$ 且 $G=K_2F$，则 $G=(K_2K_1)E$。互相可以退化的接口应视为同一个等价类；一般情况下预序不反对称，因此不能把所有记录接口排成一条全序链。

对有限动作集 $A$、先验 $\pi$ 和损失 $0\le\ell(a,h)\le L$，记录 $E$ 的最优风险为

$$
R_E
=
\inf_\delta
\sum_{h\in H}\pi(h)
\sum_{y\in Y}E(y\mid h)
\sum_{a\in A}\delta(a\mid y)\ell(a,h),
$$

其中 $\delta(a\mid y)$ 是从记录到动作的随机决策规则。若 $E\succeq_BF$，固定一个实现 $F=K E$。任意使用 $F$ 的决策规则都可在 $E$ 上先施加 $K$ 再执行，因此

$$
\boxed{R_E\le R_F.}
$$

该不等式对每个固定先验、动作集和有界损失分别成立；它不构成跨任务的单一风险全序，也不说明某条记录在未声明的动力学或自适应实验中仍然充分。

<a id="entry-578"></a>

### 121.2 经典近似缺陷的复合律

定义从 $E$ 模拟 $F$ 的最坏行总变差缺陷

$$
\delta_B(F\mid E)
=
\inf_K\max_{h\in H}
\operatorname{TV}\bigl(F_h,(K E)_h\bigr),
$$

其中 $E_h$、$F_h$ 表示固定历史 $h$ 的记录分布。设有第三个接口 $G$，且记录空间允许复合相应随机核。对任意 $K_1,K_2$，由三角不等式和随机核对总变差距离的收缩性，得到

$$
\operatorname{TV}\bigl(G_h,(K_2K_1E)_h\bigr)
\le
\operatorname{TV}\bigl(G_h,(K_2F)_h\bigr)
+
\operatorname{TV}\bigl((K_2F)_h,(K_2K_1E)_h\bigr)
\le
\operatorname{TV}\bigl(G_h,(K_2F)_h\bigr)
+
\operatorname{TV}\bigl(F_h,(K_1E)_h\bigr).
$$

取历史最坏值和两个核的下确界，得到

$$
\boxed{
\delta_B(G\mid E)
\le
\delta_B(F\mid E)+\delta_B(G\mid F).
}
$$

因此沿接口链 $E_0\succeq_B E_1\succeq_B\cdots\succeq_B E_m$，若第 $i$ 步近似缺陷为 $\varepsilon_i$，则端点缺陷至多为 $\sum_i\varepsilon_i$。对单位区间损失，记录风险的相应偏差至多为同一数值；对上界为 $L$ 的损失，乘以 $L$。

<a id="entry-579"></a>

### 121.3 量子记录接口

经典核的退化对应量子记录态族之间的 CPTP 模拟。设每个历史 $h$ 在接口 $E$、$F$ 下分别产生密度算子 $\rho_h^E$、$\rho_h^F$。定义

$$
E\succeq_QF
\quad\Longleftrightarrow\quad
\exists\Lambda\ \text{CPTP},
\quad
\rho_h^F=\Lambda(\rho_h^E)\quad(\forall h).
$$

量子接口的状态族模拟缺陷为

$$
\delta_Q(F\mid E)
=
\inf_{\Lambda\ \mathrm{CPTP}}
\max_{h\in H}
\frac12\left\|\rho_h^F-\Lambda(\rho_h^E)\right\|_1.
$$

CPTP 映射保持迹距离收缩，因此 $E\succeq_QF$ 时，对任意 POVM 决策和有界损失都有 $R_E\le R_F$；近似情形下，被模拟方向满足 $R_E\le R_F+L\,\delta_Q(F\mid E)$。近似缺陷还满足复合律

$$
\boxed{
\delta_Q(G\mid E)
\le
\delta_Q(F\mid E)+\delta_Q(G\mid F).
}
$$

证明与经典情形相同：对近似模拟器 $\Lambda_1:E\to F$、$\Lambda_2:F\to G$ 复合，并使用

$$
\frac12\left\|\Lambda_2(\sigma)-\Lambda_2(\tau)\right\|_1
\le
\frac12\left\|\sigma-\tau\right\|_1.
$$

这里的量子预序只比较一组状态族和一次 CPTP 读出。若后续实验可以访问多槽活动记忆、插入自适应控制或保留参考，应回到第 120 节的过程缺陷；单次状态族的 $\delta_Q$ 不自动支配 comb 或 strategy 的风险。

<a id="entry-580"></a>

### 121.4 历史保留的操作判据

令 $E_k$ 表示保留深度为 $k$ 的记录接口，且忘却核满足

$$
E_{k+1}\succeq_BE_k
$$

或其量子对应 $E_{k+1}\succeq_QE_k$。给定目标未来接口 $T$、损失上界 $L$ 和容许风险误差 $\varepsilon$，若存在满足条件的 $k$，则可以选择最小的 $k$ 使

$$
L\,\delta(T\mid E_k)\le\varepsilon,
$$

其中 $\delta$ 取与任务匹配的 $\delta_B$、$\delta_Q$ 或第 120 节的过程 diamond 缺陷。这个 $k$ 是相对于历史参数集、后续决策类和误差预算的最小充分记录深度；改变任一项都可能改变它。

该判据不声称存在跨所有任务的唯一“客观历史长度”。Blackwell 预序提供的是可比较性：一条记录若能无损模拟另一条，就对所有固定任务支配；两条记录若互不可退化，则需要指定先验、损失或后续实验才能比较。

<a id="entry-581"></a>

### 121.5 与 Zeckendorf 构型的连接

在合法语言

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_jw_{j+1}=0\}
$$

上，可把 $h=w$ 作为历史参数，把 Zeckendorf 数值、奇偶性或局部模式作为不同记录接口。当 $E_k$ 是 $E_{k+1}$ 的历史无关粗粒化（由函数或随机核给出）时，存在忘却核，因而 $E_{k+1}\succeq_BE_k$。但若记录接口还包含相位、活动记忆或参考，粗粒度函数未必能由经典核模拟；必须把这些量纳入量子状态族并计算 $\delta_Q$，或回到第 120 节的过程缺陷。

这解释了为什么同一组合法构型可以有不同的“现实稳定度”：稳定度不是由 Fibonacci 维数 $F_{L+2}$ 单独决定，而是由所选记录接口在 Blackwell 预序中的位置及其对目标未来的缺陷共同决定。

<a id="entry-582"></a>

### 121.6 形式化边界与追加锚

本节的经典预序、总变差复合律、量子 CPTP 预序和状态族迹距离复合律是有限集合与有限维量子态上的普通数学推导。指定版本的 Lean 库已有随机核、有限 Kraus 通道和迹距离收缩等支点；其中 `FiniteDeficiencyTriangle.lean` 与 `FiniteDeficiencyRiskTransfer.lean` 分别提供有限缺陷三角和有界损失风险传递。Blackwell 命名、接口预序与量子状态族的统一组合尚无一个单一冻结定理；本节不冒充新增 kernel 证明。多槽自适应过程仍应使用第 120 节的过程级范数。

新增锚为

$$
\boxed{
\text{记录的充分性形成 Blackwell 预序；缺陷沿可复合的退化链次可加；在模拟方向上，风险增加至多为损失上界乘以缺陷。}
}
$$

因此，“需要保留多少历史”可以先问三个可计算问题：哪些记录可以无损退化，近似退化的缺陷如何沿链累加，以及给定未来任务的风险预算允许多大的端点缺陷。只有在这三个量都被指定后，稳定经典现实才有可检验的记录深度。

<a id="section-122"></a>

## 122. 双向缺陷、操作等价与历史深度

第 121 节给出了有向的 Blackwell 缺陷：较细接口能否模拟较粗接口，以及模拟误差如何沿链累加。本节补上两个边界。第一，若要称两个接口“同一现实接口”，需要同时控制两个方向；第二，嵌套历史接口只有在忘却核与任务缺陷相容时，才会产生可证明的最小保留深度。

<a id="entry-584"></a>

### 122.1 双向缺陷不是标签相等

对经典接口定义

$$
\Delta_B(E,F)
=
\max\left\{\delta_B(F\mid E),\delta_B(E\mid F)\right\},
$$

对量子状态族定义

$$
\Delta_Q(E,F)
=
\max\left\{\delta_Q(F\mid E),\delta_Q(E\mid F)\right\}.
$$

第 121 节的有向次可加律立即给出三角不等式

$$
\Delta_B(E,G)
\le
\Delta_B(E,F)+\Delta_B(F,G),
$$

以及量子对应式

$$
\Delta_Q(E,G)
\le
\Delta_Q(E,F)+\Delta_Q(F,G).
$$

两者都满足自反性，但一般不满足严格的同一性判别：若两个接口可以在所有历史上互相近似退化，可能仍然不是字节相等、标签相等或通道同构。它们只是在指定历史实验族下操作等价。因此 $\Delta_B$ 与 $\Delta_Q$ 更准确地说是伪度量；在互相零缺陷的接口等价类上，才得到真正的度量结构。 在有限接口且模拟器集合紧的条件下，定义 $E\sim F\iff\Delta(E,F)=0$ 得到等价关系，商空间上的诱导距离才是度量；若只给定部分任务族，只能称为任务相对等价。

若 $\Delta(E,F)\le\varepsilon$ 且 $\Delta(F,G)\le\varepsilon$，只能推出 $\Delta(E,G)\le2\varepsilon$。所以“误差不超过 $\varepsilon$ 的等价”本身不是传递等价关系；跨多层接口时必须把预算累加，或提高允许阈值。

<a id="entry-585"></a>

### 122.2 双向缺陷与任务风险

若损失上界为 $L$，第 121 节的单向结论分别给出

$$
R_E\le R_F+L\,\delta(F\mid E),
\qquad
R_F\le R_E+L\,\delta(E\mid F).
$$

因此

$$
\boxed{
\left|R_E-R_F\right|
\le
L\,\Delta(E,F).
}
$$

这里的风险必须针对同一个先验、动作集和损失函数；改变任务后，$\Delta$ 仍可作为接口距离，但这条风险界需要重新代入新的 $L$ 与决策类。量子状态族的 POVM 决策同样满足该双向界，迹距离收缩是唯一使用的量子性质。

<a id="entry-586"></a>

### 122.3 嵌套历史接口的单调性

设 $E_k$ 是保留前 $k$ 层历史的接口。若存在与历史无关的忘却核 $W_k$，满足

$$
E_k=W_k\circ E_{k+1},
$$

则有精确 Blackwell 关系

$$
E_{k+1}\succeq_BE_k.
$$

对任意目标接口 $T$，把从 $E_k$ 到 $T$ 的近似模拟器与 $W_k$ 复合，得到

$$
\boxed{
\delta_B(T\mid E_{k+1})
\le
\delta_B(T\mid E_k).
}
$$

量子状态族在存在 CPTP 忘却映射时满足完全相同的单调性：若 $\rho_h^{E_k}=\Lambda_k(\rho_h^{E_{k+1}})$，则

$$
\delta_Q(T\mid E_{k+1})
\le
\delta_Q(T\mid E_k).
$$

单调性只说明增加可模拟的历史不会变差；它不保证缺陷严格下降，也不保证任意“看起来更长”的记录都存在这样的忘却核。嵌套性必须由接口的实际构造给出。

<a id="entry-587"></a>

### 122.4 有限历史深度与开放边界

给定目标未来接口 $T$、容许接口缺陷 $\varepsilon$ 和损失上界 $L$，定义

$$
k_\varepsilon(T)
=
\min\left\{k:\ L\,\delta(T\mid E_k)\le\varepsilon\right\},
$$

但只有集合非空时该最小值才存在。若对所有可用 $k$ 都不满足条件，应保留“无有限深度”的开放状态，不能以增加计算预算代替缺失的历史信息。

当 $E_k$ 嵌套且存在忘却核时，上一节单调性保证可行深度集合是向上的：一旦某个 $k$ 满足预算，所有更深层接口也满足。于是 $k_\varepsilon(T)$ 的含义是明确的最小充分记录深度，而不是任意截断点。 若令 $e_k=\delta(T\mid E_k)$、$e_\infty=\inf_k e_k$，则严格满足 $\varepsilon>L e_\infty$ 时可由单调收敛得到某个有限可行 $k$；$\varepsilon<L e_\infty$ 时不存在可行深度；等号情形只有在某个有限 $k$ 达到极限时才可行，否则仍是开放边界。

第 120 节的过程 diamond 缺陷可直接替换这里的 $\delta$，但需要把 $E_k$ 视为完整过程接口并保留参考与活动记忆。若只用单次状态族的 $\delta_Q$，则所得深度只对一阶段 POVM 任务有效。

<a id="entry-588"></a>

### 122.5 Zeckendorf 合法空间中的实例化

在

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_jw_{j+1}=0\}
$$

中，令 $E_k$ 保留 Zeckendorf 合法字串的前 $k$ 个坐标，令 $W_k$ 忘却其余坐标。只要粗读出确实是这些坐标的函数，$E_k=W_k\circ E_{k+1}$ 成立，因而形成 Blackwell 链。

若目标任务读取完整数值、相位或跨坐标历史，坐标前缀未必足够；此时应把目标接口 $T$ 的后态与记忆纳入缺陷计算。合法构型总数 $F_{L+2}$ 只给出状态空间规模，不决定 $k_\varepsilon(T)$。

因此，同一个 Zeckendorf 刻度可以在一个任务上很快达到小缺陷，在另一个任务上始终有非零缺陷。差异来自目标实验族和可访问关联，而不是编码是否唯一。

<a id="entry-589"></a>

### 122.6 形式化边界与追加锚

本节的双向伪度量、风险绝对差界和嵌套接口单调性，均由第 121 节的有向缺陷复合与 CPTP/随机核收缩推出。指定版本的 Lean 支点仍是有限缺陷三角、风险传递和通道收缩；本节未新增 Lean 声明，也没有把这些普通数学组合冒充 kernel 已证结果。

新增锚为

$$
\boxed{
\text{“同一现实接口”只能表示指定实验族下的双向小缺陷；历史深度只有在忘却核、任务和误差预算同时给定时才可计算。}
}
$$

这使“保留多少历史”获得两个可审计的失败模式：没有双向模拟时，接口不能称为操作等价；没有满足预算的有限 $k$ 时，结论必须保持开放，而不是把更长的 Zeckendorf 标签自动当作充分历史。
<a id="section-123"></a>

## 123. 逆极限中的幽灵历史与载体完备化

第 122 节把记录深度写成相对于目标任务的缺陷预算。本节补上一个不同的边界：即使每个有限层都可实现，且层与层之间完全相容，也不保证这些有限记录来自原先的对象载体。逆极限会把所有有限层一致的塔组织起来；原载体能否覆盖这些塔，是一个独立的满射与完备化问题。

<a id="entry-591"></a>

### 123.1 有限接口塔与自然嵌入

设有有限层接口 $q_n:X\to Q_n$，以及忘却映射 $\pi_n:Q_{n+1}\to Q_n$，满足

$$
\pi_n\circ q_{n+1}=q_n.
$$

定义兼容塔

$$
\varprojlim Q_n
=
\left\{(z_n)_n:\ \pi_n(z_{n+1})=z_n\ \text{对所有 }n\right\}.
$$

每个 $x\in X$ 给出一个塔

$$
\iota(x)=(q_n(x))_n.
$$

令

$$
R_\infty=\bigcap_n\ker(q_n),
\qquad
x\mathrel{R_\infty}y
\Longleftrightarrow
q_n(x)=q_n(y)\ \text{对所有 }n.
$$

则 $\iota$ 唯一因子化为

$$
\bar\iota:X/R_\infty\longrightarrow\varprojlim Q_n,
$$

并且 $\bar\iota$ 是单射。这里的单射只使用所有层读数同时相等才定义的商关系；它不要求原载体已经完备。

<a id="entry-592"></a>

### 123.2 满射缺陷不是逐层一致性能够消除的

嵌入 $\bar\iota$ 满射，当且仅当每一个兼容塔 $(z_n)_n$ 都存在单个 $x\in X$，使

$$
q_n(x)=z_n
\qquad\text{对所有 }n.
$$

因此，“每个有限层都有实现”只说明塔属于逆极限，不说明塔属于原像。定义载体的完备化缺陷为

$$
\operatorname{Ghost}(X;Q_\bullet)
=
\left(\varprojlim Q_n\right)\setminus\operatorname{im}(\bar\iota).
$$

这个集合为空，才可以说当前载体对这组有限接口是完备的；非空时，逆极限引入了原类型中没有的理想记录。这里的“幽灵”是表示边界的数学名称，不是额外物理实体。

<a id="entry-593"></a>

### 123.3 Zeckendorf 前缀的具体幽灵

令 $X_{\mathrm{fs}}$ 为所有只有有限多个 $1$ 的无限合法串：

$$
X_{\mathrm{fs}}
=
\left\{x\in\{0,1\}^{\mathbb N}:x_ix_{i+1}=0,\ \exists N\ \forall i\ge N,\ x_i=0\right\}.
$$

令 $Q_n=\mathcal W_n$ 为长度 $n$ 的无相邻 $1$ 字串，$\pi_n$ 删除最后一位，$q_n$ 取前缀。兼容性给出

$$
\varprojlim Q_n
\cong
\left\{z\in\{0,1\}^{\mathbb N}:z_i z_{i+1}=0\right\},
$$

即所有无限合法串，而不仅是有限支持串。

交替串

$$
z=1010101010\cdots
$$

的每个有限前缀都属于某个 $Q_n$，并且每个前缀都可由一个有限 Zeckendorf 整数实现；但不存在 $x\in X_{\mathrm{fs}}$ 同时实现全部前缀，因为 $x$ 最终必须全为 $0$。所以 $z$ 是逆极限中的元素，却不在 $\bar\iota$ 的像中。

若把对象类型扩张为所有无限合法串

$$
\widehat X
=
\left\{x\in\{0,1\}^{\mathbb N}:x_ix_{i+1}=0\right\},
$$

则前缀映射对该逆系统满射。扩张载体解决了满射缺陷，但也改变了对象类型：它加入了有限整数模型没有的无限历史。不能把这一步描述成在原对象中发现了一个普通整数。

<a id="entry-594"></a>

### 123.4 动力学必须保持原像

若每层有操作 $T_n:Q_n\to Q_n$，并满足

$$
\pi_n\circ T_{n+1}=T_n\circ\pi_n,
$$

则得到逆极限上的操作

$$
\widehat T((z_n)_n)=(T_n z_n)_n.
$$

若原载体上存在 $T:X\to X$，且

$$
q_n\circ T=T_n\circ q_n,
$$

则

$$
\widehat T\circ\iota=\iota\circ T.
$$

但层间相容本身不保证 $\widehat T$ 保持有限支持像。对 Hilbert 型有界线程，还需要统一的算子界

$$
\sup_n\|T_n\|\le M<\infty
$$

来保证逐层作用仍给出有界线程；没有这个界，层操作可能把可实现的线程推出载体。要让完备化后的动力学仍然代表原模型，必须另行证明

$$
\widehat T\bigl(\operatorname{im}(\bar\iota)\bigr)
\subseteq
\operatorname{im}(\bar\iota),
$$

或给出离开该像集的泄漏指标。否则，一个只在无限完备化中存在的幽灵历史，可能被层操作激活并进入后续读数；这不是原有限对象动力学的结论。

<a id="entry-595"></a>

### 123.5 与历史深度和量子接口的边界

本节的逆极限问题与第 122 节的缺陷预算正交。缺陷衡量某个接口对目标实验的预测损失；逆极限满射衡量所有兼容有限记录是否能由同一原对象实现。一个载体可以在任务意义下具有很小缺陷，却仍有非空的完备化缺陷；反过来，载体完备也不保证记录足以闭合未来动力学。

指定版本已经有两个直接相关的 Lean 支点。`D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction.lean` 中的 `bounded_inverse_limit_reconstruction` 证明：单调子空间序列的有界、正交投影相容族，与累积闭子空间之间存在规范的线性等距双射；因此在 Hilbert 载体中，“逆极限线程”还必须带有统一有界性。`D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.lean` 中的 `compatible_unbounded_coordinates` 给出反例：`partialOnes n` 满足每个有限层的投影相容性，但

$$
\|\mathrm{partialOnes}(n)\|^2=n,
$$

故范数无界；它既不是某个 $\ell^2$ 向量的投影族，也不属于有界逆极限。这个例子把“逐层一致”与“存在一个实际状态”之间缺失的有界性条件具体化了。

对量子接口，$Q_n$ 应替换为带态、相位和活动记忆的有限接口，忘却映射应替换为保持合法性的量子通道。逐层状态族的一致性仍不自动给出完整过程的可实现性；若后续实验能访问参考或旧记录，必须回到第 120 节的过程 diamond 缺陷。Gram 矩阵的正定性、通道的完全正性和像集不变性，都是额外的整体相容条件。

本节的因子化、Zeckendorf 前缀反例和动力学像集条件是逆系统与有限字串上的普通数学推导；Hilbert 载体中的有界重建与无界线程反例则由上述两个已有 Lean 声明直接支撑。本节没有新增 Lean 声明，也不声称重建了物理时空的完备性。指定版本的项目已有上下文等价、有限接口和记录通道支点，但没有一个冻结定理把这些支点自动组合成 Zeckendorf 逆极限的满射定理。

新增锚为

$$
\boxed{
\text{逆极限组织所有有限层一致记录；原载体的可实现性还要求满射、完备性或有界性，动力学则必须额外保持该像集。}
}
$$

因此，“无限递归”应当分成两个可检验问题：有限层是否相容，以及相容塔是否仍由当前对象类型承载。前者失败时要拒绝该关系网络；后者失败时要明确报告完备化新增的理想历史，并重新指定允许的动力学与测量范围。
<a id="entry-596"></a>

## 追加锚（本行以下为增补区）

<a id="section-124"></a>

## 124. 有限前缀量子模拟与连续延拓

本节固定一个经典数字载体和一个有限维量子输出空间，把第 122 节的前缀缺陷与第 123 节的完备化联系起来。目标是刻画何时有限前缀能一致逼近一个态制备任务；载体加入无限合法串，并不自动使任意任务连续。以下定义与证明均在通常数学中进行。

**定义 124.1（合法串、有限核心与实际前缀像）。** 所有下标从 $0$ 开始，令
$$
\widehat X=\{x\in\{0,1\}^{\mathbb N}:\ \forall j\ge0,\ x_jx_{j+1}=0\},\qquad
X_{\rm fs}=\{x\in\widehat X:\ \exists N\ \forall j\ge N,\ x_j=0\}.
$$
对 $k\in\mathbb N$，以同一符号 $q_k$ 表示两个域上的前缀限制，置
$$
q_kx=(x_0,\ldots,x_{k-1}),\qquad
W_k=q_k[X_{\rm fs}]=q_k[\widehat X],\qquad
F_{k,w}=\{x\in X_{\rm fs}:q_kx=w\}.
$$
$W_k$ 恰是全部长度 $k$ 的无相邻 $1$ 字串；任一这种字串补零即给两个域中的原像。因此每个 $F_{k,w}$ 非空，$W_k$ 有限非空，$W_0=\{\varnothing\}$。记 $\tau_kz$ 为 $z$ 保留前 $k$ 位后补零的串。
取前缀距离
$$
p(x,y)=
\begin{cases}
0,&x=y,\\
2^{-m},&x\ne y,\ m=\min\{j:x_j\ne y_j\}.
\end{cases}
$$
这是 Z 卷定理 477.3 的 $d_{1/2}$。Z 卷定义 371.1 的距离另为 $d_K(x,y)=\sum_{j\ge0}2^{-j-1}|x_j-y_j|$，二者满足 $p/2\le d_K\le p$，并非同一数值公式。上述数字核心也不是 CSA 定义 1–3 的带事件、偏序、区域与选择的档案载体；CSA §§14–16 中的读数与语言仍保留各自的类型。

**命题 124.2（紧完备载体与逐柱稠密性）。** $p$ 是给出二元离散乘积之子空间拓扑的超度量，$\widehat X$ 紧且完备，$X_{\rm fs}$ 在其中稠密。更精确地，对每个 $k,w$，$F_{k,w}$ 在柱集 $\widehat F_{k,w}=\{z\in\widehat X:q_kz=w\}$ 中稠密，且
$$
q_kx=q_ky\ \Longleftrightarrow\ p(x,y)\le2^{-k},\qquad
p(\tau_kz,z)\le2^{-k}.
$$
证明。两对串共享的前缀长度取较小者，仍是第三对共享的前缀长度，故
$p(x,z)\le\max\{p(x,y),p(y,z)\}$；分离性和对称性由定义得到。
前缀柱集是有限个离散坐标条件的交；任意有限坐标条件又包含一个足够长的前缀条件。距离球与前缀柱集因而给出同一拓扑，所列等价含 $k=0$。

违反合法性的串在某对相邻坐标上取值 $11$，这是一项开柱条件；所以 $\widehat X$ 在二元乘积中闭。为具体证明紧性，对任意序列依次选第 $0,1,2,\ldots$ 位恒定的无限子序列，再取对角子序列。各坐标最终恒定所得的极限仍无相邻 $1$，前缀距离保证收敛。度量空间的序列紧性给紧性。
若序列是 Cauchy，对每个 $j$，距离最终小于 $2^{-j}$，故第 $j$ 位最终恒定；同一构造给合法极限并证明原序列收敛，故完备。

补零不制造相邻 $1$，故 $\tau_mz\in X_{\rm fs}$ 且趋于 $z$。若 $z\in\widehat F_{k,w}$，则所有 $m\ge k$ 的截断都在 $F_{k,w}$，得到逐柱稠密性。若首差在 $j$，加权距离的首项为 $2^{-j-1}$、尾和至多 $2^{-j}$，也直接验证定义 124.1 的距离比较。这给 Z371.1–2、Z477.3 的载体在所选前缀距离下的具体实现。

**定义 124.3（固定有限维的静态态制备任务）。** 固定整数 $d\ge1$，输出态空间与距离为
$$
\mathcal D_d=\{\rho\in M_d(\mathbb C):\rho=\rho^*,\ \rho\succeq0,\ \operatorname{tr}\rho=1\},\qquad
D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1.
$$
这里 $\|A\|_1=\operatorname{tr}\sqrt{A^*A}$，允许任意混态，不限于纯态。
任务是任意总函数 $T:X_{\rm fs}\to\mathcal D_d$，起初不假定连续。

深度 $k$ 的输入寄存器为 $\mathcal H_k=\mathbb C^{W_k}$，取以 $w\in W_k$ 标记的正交标准基，并置
$$
E_{k,x}=|q_kx\rangle\langle q_kx|.
$$
模拟器遍历所有 CPTP 映射 $\Lambda:M_{|W_k|}(\mathbb C)\to M_d(\mathbb C)$；它须对所有 $x$ 共用，只能从给定寄存器获得前缀。这里 $x$ 是经典制备标签，未给不相容量子可观测量预先指定共同测量结果。

**命题 124.4（CPTP 模拟器与混态表的精确等价）。** 上述输入族上的全部可实现输出恰为任意混态表 $(\sigma_w)_{w\in W_k}\in\mathcal D_d^{W_k}$。每张表都可由
$$
\Lambda_\sigma(A)=\sum_{w\in W_k}\langle w|A|w\rangle\sigma_w
$$
实现，因此只对 $E_{k,x}$ 计算的最坏误差，在所有 CPTP 映射与所有混态表上取下确界相同。
证明。任一 CPTP 映射给出密度态 $\sigma_w=\Lambda(|w\rangle\langle w|)$，于是输入 $x$ 的输出只依赖 $q_kx$。
反向对每个 $w$ 作谱分解 $\sigma_w=\sum_{a=1}^d\lambda_{wa}|v_{wa}\rangle\langle v_{wa}|$，其中 $\lambda_{wa}\ge0$、$\sum_a\lambda_{wa}=1$。取 Kraus 算子
$$
K_{wa}=\sqrt{\lambda_{wa}}\,|v_{wa}\rangle\langle w|.
$$
则 $\sum_{w,a}K_{wa}^*K_{wa}=I_{\mathcal H_k}$，且 $\sum_{w,a}K_{wa}AK_{wa}^*=\Lambda_\sigma(A)$。Kraus 形式给完全正性，前一等式给保迹性，代入基态即得指定表。这个等价只规定输入族上的行为，不规定一般相干叠加输入上的通道行为。

**定义 124.5（前缀缺陷、纤维振幅与半径）。** 对定义 124.3 的固定任务，令
$$
e_k(T)=\inf_{\Lambda\ {\rm CPTP}}\ \sup_{x\in X_{\rm fs}}
D\bigl(T(x),\Lambda(E_{k,x})\bigr)
=\inf_{\sigma\in\mathcal D_d^{W_k}}\ \sup_{x\in X_{\rm fs}}D\bigl(T(x),\sigma_{q_kx}\bigr),
$$
$$
\omega_{k,w}(T)=\sup_{x,y\in F_{k,w}}D(T(x),T(y)),\qquad
\omega_k(T)=\max_{w\in W_k}\omega_{k,w}(T),
$$
$$
f_{k,w}(\sigma)=\sup_{x\in F_{k,w}}D(T(x),\sigma),\qquad
r_{k,w}(T)=\inf_{\sigma\in\mathcal D_d}f_{k,w}(\sigma).
$$
所有上确界都在非空集上且取值于 $[0,1]$。纤维可以无限且不紧，$T$ 也可以不连续，所以这里没有把无限纤维上的上确界写成最大值。只有有限集合 $W_k$ 上使用最大值。

**定理 124.6（精确纤维半径公式与最优表存在）。** $\mathcal D_d$ 在 $D$ 下紧且完备，任意两态间的距离属于 $[0,1]$。对任意 $T:X_{\rm fs}\to\mathcal D_d$ 及任意 $k$，每个纤维都有最优中心，且
$$
e_k(T)=\max_{w\in W_k}\ \min_{\sigma\in\mathcal D_d}
\sup_{x\in F_{k,w}}D(T(x),\sigma)
=\max_{w\in W_k}r_{k,w}(T).
$$
存在一张表达到 $e_k(T)$，并由命题 124.4 实现为 CPTP 模拟器。
证明。Hermitian 矩阵组成有限维实向量空间，迹范数在该空间上给完备的度量。
若一列密度矩阵趋于 $\rho$，则对每个 $v\in\mathbb C^d$，
$$
v^*\rho v=\lim_n v^*\rho_n v\ge0,\qquad
\rho^*=\rho,\qquad \operatorname{tr}\rho=\lim_n\operatorname{tr}\rho_n=1.
$$
所以态空间闭。半正定矩阵的特征值非负，迹等于特征值之和，因此
$$
\|\rho\|_1=\operatorname{tr}\rho=1,\qquad
\tfrac12\|\rho-\sigma\|_1\le\tfrac12(\|\rho\|_1+\|\sigma\|_1)=1.
$$
闭有界性在有限维给紧性，闭子集又继承完备性；迹范数的一半仍是度量。

对任何 $\sigma,\eta\in\mathcal D_d$，逐点三角不等式及取上确界给
$$
f_{k,w}(\sigma)\le f_{k,w}(\eta)+D(\sigma,\eta),\qquad
|f_{k,w}(\sigma)-f_{k,w}(\eta)|\le D(\sigma,\eta).
$$
故纤维目标函数对中心是 $1$-Lipschitz，尽管它对 $x$ 不要求连续。紧集 $\mathcal D_d$ 上的连续实函数达到最小值，取一个中心 $\sigma_w^*$。
任意表的全局目标恰为 $\max_w f_{k,w}(\sigma_w)$，因为非空纤维有限个且分割 $X_{\rm fs}$。每一项至少为 $r_{k,w}$，故任何表的目标至少为 $\max_w r_{k,w}$；对有限个 $w$ 分别选取上述中心，便同时达到这个下界。
证明不要求中心来自 $T[F_{k,w}]$，也不给中心唯一性或不同深度最优表之间的相容性。

**命题 124.7（直径界、单调性与有限层精确性）。** 对所有 $k\ge0$，
$$
\tfrac12\omega_k(T)\le e_k(T)\le\omega_k(T),\qquad
e_{k+1}(T)\le e_k(T),\qquad
\omega_{k+1}(T)\le\omega_k(T).
$$
而且
$$
e_k(T)=0\quad\Longleftrightarrow\quad
\exists t_k:W_k\to\mathcal D_d\ \forall x\in X_{\rm fs},\ T(x)=t_k(q_kx).
$$
证明。对同纤维的 $x,y$ 和任一中心 $\sigma$，有
$D(T(x),T(y))\le D(T(x),\sigma)+D(T(y),\sigma)\le2f_{k,w}(\sigma)$。
先对 $x,y$ 取上确界，再对中心取下确界，得 $\omega_{k,w}\le2r_{k,w}$。
从非空纤维选一个 $x_w$，用 $T(x_w)$ 作中心，得 $r_{k,w}\le\omega_{k,w}$；定理 124.6 给全局两界。

将深度 $k$ 的最优中心复制给每个具有相同父前缀的长度 $k+1$ 字串，新表逐点输出与旧表相同。因此新最优误差不增；新纤维包含于父纤维，也使 $\omega_k$ 不增。这个复制表不必是新层最优表。
若 $e_k=0$，则 $\omega_k=0$，每个非空纤维上的 $T$ 恒定，按此值定义 $t_k$；反向因子化表逐点误差为零。所有结论也覆盖 $d=1$，此时态空间只有一个元素，全部缺陷恒为零。

**定理 124.8（误差趋零与唯一连续延拓的等价）。** 对固定有限 $d\ge1$ 和任意 $T:X_{\rm fs}\to\mathcal D_d$，以下四项等价：

1. $\lim_{k\to\infty}e_k(T)=0$。
2. $\lim_{k\to\infty}\omega_k(T)=0$。
3. $T:(X_{\rm fs},p)\to(\mathcal D_d,D)$ 一致连续，即
$$
\forall\varepsilon>0\ \exists\delta>0\ \forall x,y\in X_{\rm fs},\quad
p(x,y)<\delta\ \Longrightarrow\ D(T(x),T(y))<\varepsilon.
$$
4. 存在唯一连续函数 $\widehat T:(\widehat X,p)\to(\mathcal D_d,D)$，使 $\widehat T|_{X_{\rm fs}}=T$。

该延拓实际上是一致连续的。这里第三项的定义域是有限支持核心，第四项的定义域是全部无限合法串；不能把第三项降为核心上的逐点连续，也不能把第一项换成逐输入的误差极限。

证明。命题 124.7 的两侧界直接给第一、二项等价。
若第二项成立，给定 $\varepsilon>0$ 选 $K$ 使 $\omega_K<\varepsilon$。当 $p(x,y)<2^{-K}$ 时两点共享前 $K$ 位，故 $D(T(x),T(y))\le\omega_K<\varepsilon$，得到第三项。
若第三项成立，先对 $\varepsilon/2$ 选一致连续性的 $\delta$，再选 $K$ 使 $2^{-K}<\delta$。对每个 $k\ge K$ 的同纤维两点，距离不超过 $2^{-k}<\delta$，故目标距离小于 $\varepsilon/2$。取上确界后 $\omega_k\le\varepsilon/2<\varepsilon$，得到第二项。

现由第二项构造第四项。固定 $z\in\widehat X$，对 $m,n\ge K$，截断 $\tau_mz,\tau_nz$ 共享前 $K$ 位，故
$$
D\bigl(T(\tau_mz),T(\tau_nz)\bigr)\le\omega_K(T).
$$
因此这是一列 Cauchy 态；由 $\mathcal D_d$ 的完备性定义
$$
\widehat T(z)=\lim_{n\to\infty}T(\tau_nz)\in\mathcal D_d.
$$
它不依赖截断以外的近似选择：若 $x_n\in X_{\rm fs}$ 且 $p(x_n,z)\to0$，则对固定 $K$，充分大的 $n$ 有 $q_Kx_n=q_Kz$。同样对 $m\ge K$ 有 $q_K\tau_mz=q_Kz$，于是 $D(T(x_n),T(\tau_mz))\le\omega_K$。令 $m\to\infty$ 后仍有 $D(T(x_n),\widehat T(z))\le\omega_K$；再让 $K$ 增大，得到 $T(x_n)\to\widehat T(z)$。有限支持的 $z$ 最终等于自身截断，故延拓确实等于 $T$。

若 $q_Kz=q_Kz'$，则 $n\ge K$ 时的两截断也共享该前缀，令 $n\to\infty$ 得
$$
D(\widehat T(z),\widehat T(z'))\le\omega_K(T).
$$
选 $\omega_K<\varepsilon$ 并取输入距离阈值 $2^{-K}$，这证明延拓一致连续，特别连续。
任一连续延拓 $U$ 都满足 $U(z)=\lim_n U(\tau_nz)=\lim_n T(\tau_nz)=\widehat T(z)$，所以唯一。

最后若第四项成立，命题 124.2 给紧域，Heine–Cantor 定理使连续的 $\widehat T$ 一致连续。
这里也可直接证明所需的紧性步骤：若不一致连续，存在 $\varepsilon_0>0$ 和两列 $z_n,z_n'\in\widehat X$，满足
$$
p(z_n,z_n')<1/(n+1),\qquad
D(\widehat T(z_n),\widehat T(z_n'))\ge\varepsilon_0.
$$
由紧性取 $z_n$ 的收敛子序列，沿同一下标的 $z_n'$ 也趋于同一点。连续性和目标距离三角不等式迫使输出距离趋零，矛盾。
故限制到 $X_{\rm fs}$ 也一致连续，得到第三项。完备性在构造目标极限时使用，紧性在这个反向推导时使用；它们承担不同义务。

**命题 124.9（连续延拓保持每个有限缺陷）。** 若存在连续延拓 $\widehat T:\widehat X\to\mathcal D_d$，把定义 124.5 中的定义域换成 $\widehat X$，而保持 $W_k$ 与模拟器类不变，则对每个 $k$ 有
$$
e_k(\widehat T)=e_k(T),\qquad \omega_k(\widehat T)=\omega_k(T).
$$
更强地，对每个 $w\in W_k$ 与每个中心 $\sigma\in\mathcal D_d$，
$$
\sup_{z\in\widehat F_{k,w}}D(\widehat T(z),\sigma)
=\sup_{x\in F_{k,w}}D(T(x),\sigma).
$$
证明。核心包含于完备载体给右边不大于左边。任一 $z\in\widehat F_{k,w}$ 的截断 $\tau_nz$ 在 $n\ge k$ 时属于 $F_{k,w}$；连续性使其到中心的距离趋于 $D(\widehat T(z),\sigma)$，每项又不超过右侧上确界，故反向不等式成立。
逐对截断同样证明每个柱上的直径上确界不变；对中心取下确界、对有限个柱取最大值便给两个结论。无限串可以使某个上确界真正达到，但不会在连续延拓下增大任何有限层最坏误差。

**命题 124.10（连续而永无精确有限深度的量子比特任务）。** 本命题取 $d=2$，复用 Z477.3 的函数
$$
S(z)=\sum_{j\ge0}4^{-j-1}z_j,\qquad
T_S(x)=\operatorname{diag}(1-S(x),S(x)),\qquad
c_k=\tfrac4{15}4^{-k}.
$$
则 $0\le S(z)\le4/15$，$T_S$ 连续延拓到 $\widehat X$，且对每个 $k\ge0$，
$$
\omega_k(T_S)=c_k,\qquad e_k(T_S)=\tfrac12c_k=\tfrac2{15}4^{-k}>0.
$$
证明。若从位置 $k$ 开始的尾部首位不受前一位限制，每对位置 $k+2r,k+2r+1$ 至多一个 $1$，所以该对的加权贡献至多为 $4^{-(k+2r)-1}$。求几何级数得
$$
\sum_{j\ge k}4^{-j-1}z_j
\le\sum_{r\ge0}4^{-(k+2r)-1}
=\frac{4^{-k-1}}{1-4^{-2}}=c_k.
$$
交替尾 $1010\cdots$ 达到此值；其任意长的有限截断都合法，尾和趋于 $c_k$。取 $k=0$ 得全局范围，因此所写矩阵确为密度态。

固定前缀 $w$，置 $s_w=\sum_{j<k}4^{-j-1}w_j$。当 $k=0$ 或 $w_{k-1}=0$ 时，尾部范围的下确界为 $0$、上确界为 $b_w=c_k$。当 $k\ge1$ 且 $w_{k-1}=1$ 时，第 $k$ 位被迫为零，位置 $k+1$ 起可自由接交替尾，故 $b_w=c_{k+1}$。下端用全零尾达到；上端由对应交替尾的有限截断逼近。
有限支持串无法达到正的上端：达到成对求和界需要无限多对各自达到最大贡献。完备载体上的交替尾则达到上端。

两对角态的迹距离等于第二个对角元之差的绝对值，因此纤维直径的上确界为 $b_w$。合法态
$$
\sigma_w=\operatorname{diag}\bigl(1-s_w-b_w/2,\ s_w+b_w/2\bigr)
$$
是两端态的中点，对整个纤维的误差至多 $b_w/2$；两端态合法，因为对应无限合法串的 $S$ 仍在 $[0,4/15]$。命题 124.7 的逐纤维下界又迫使任何中心，包括非对角中心，半径至少为 $b_w/2$。
全零前缀（含空前缀）给 $b_w=c_k$，其余 $b_w\le c_k$，定理 124.6 因而给出精确缺陷。

同前缀的 $S$ 差不超过 $c_k\to0$，所以无穷级数给出的对角态函数在 $\widehat X$ 连续，并由定理 124.8 唯一延拓核心任务。每个有限 $k$ 的缺陷仍严格为正；“任意小误差都有有限深度”不蕴含“某个有限深度误差为零”。

**命题 124.11（逐输入最终正确仍有固定最坏缺陷）。** 本命题取 $d=2$，记 $P_a=|a\rangle\langle a|$，$a\in\{0,1\}$，以 $0^\infty$ 表示总零串。定义
$$
T_0(x)=\begin{cases}P_0,&x=0^\infty,\\P_1,&x\ne0^\infty.\end{cases}
$$
则对每个有限 $k$，$\omega_k(T_0)=1$、$e_k(T_0)=1/2$。但存在一列确定性前缀预测器，对每个固定输入最终完全正确。
证明。全零前缀纤维同时包含 $0^\infty$ 和仅在某个 $j\ge k$ 取 $1$ 的合法串；它们的目标态距离为 $D(P_0,P_1)=1$。其余纤维若含已见 $1$，目标态恒为 $P_1$。故最大纤维直径为 $1$，一般下界给 $e_k\ge1/2$。
对全零前缀输出 $(P_0+P_1)/2$，对已见 $1$ 的前缀输出 $P_1$，便把最坏误差控制在 $1/2$，证明等式。

另取确定性表 $A_k(w)$：已经见到 $1$ 时输出 $P_1$，否则输出 $P_0$。总零输入在所有深度都正确；任一非零输入有首个 $1$ 的下标 $j$，从 $k=j+1$ 起永远正确。因此
$$
\forall x\in X_{\rm fs},\quad
\lim_{k\to\infty}D(T_0(x),A_k(q_kx))=0,
\qquad
\forall k,\quad\sup_{x\in X_{\rm fs}}D(T_0(x),A_k(q_kx))=1.
$$
后式由每层尚未出现的单个 $1$ 实现。这个确定性表并非最优混态表，不能将其误差 $1$ 与最优缺陷 $1/2$ 混用；同样不能把纤维直径误写成 $1/2$。
远处的单个 $1$ 趋于总零串，目标态却恒为 $P_1$，所以 $T_0$ 在核心的总零点不连续，更无连续延拓。

**命题 124.12（任务逐个有限与整个任务族一致有限的区别）。** 本命题取 $d=2$，对每个 $j\ge0$ 定义坐标任务 $T_j(x)=P_{x_j}$，则
$$
e_k(T_j)=\begin{cases}0,&j<k,\\1/2,&j\ge k.\end{cases}
$$
若先提供前缀、再揭示任务 $j$，允许模拟器按 $(j,w)$ 选择态，但在所有 $j,x$ 上评价最坏误差，则
$$
E_k=\inf_{(\sigma_{j,w})\in\mathcal D_2^{\mathbb N\times W_k}}
\sup_{j\in\mathbb N,\ x\in X_{\rm fs}}D(T_j(x),\sigma_{j,q_kx})=1/2
$$
对每个有限 $k$ 成立。这不是一次同时制备所有任务的联合量子态的要求。
证明。$j<k$ 时该位已被记录，直接输出 $P_{w_j}$ 即精确。$j\ge k$ 时，总零串与仅第 $j$ 位为 $1$ 的串同属全零前缀纤维，迫使误差至少为 $1/2$；常值中点态表给上界。
对任务族，任意表固定取 $j=k$，同一对串仍迫使最坏误差至少为 $1/2$。同时给所有已记录任务输出对应纯态、所有未记录任务输出中点态，达到该界。

每个 $T_j$ 都连续延拓且在深度 $j+1$ 精确；有限非空任务集 $J$ 有共同精确深度 $1+\max J$，空任务集没有约束。然而对无限任务族，以下两个量词序列不同：
$$
\forall j\ \exists K\ \forall k\ge K,\ e_k(T_j)=0,
\qquad
\exists K\ \forall j\ \forall k\ge K,\ e_k(T_j)=0.
$$
本例满足前者而否定后者，甚至对任意小于 $1/2$ 的共同误差预算也否定后者的近似版本。
一般固定有限维、由非空集合 $J$ 标记的任务族 $\{T_j:X_{\rm fs}\to\mathcal D_d\}_{j\in J}$，将上式的 $\mathbb N$ 换成 $J$ 定义共同缺陷。其趋零须由共同的一致连续性条件控制：
$$
\forall\varepsilon>0\ \exists\delta>0\ \forall j\in J\ \forall x,y\in X_{\rm fs},\quad
p(x,y)<\delta\ \Longrightarrow\ D(T_j(x),T_j(y))<\varepsilon.
$$
在通常集合选择下，这也是充要条件：逐任务、逐纤维选择最优中心使共同缺陷等于 $\sup_j e_k(T_j)$；两侧直径界将其趋零化为 $\sup_j\omega_k(T_j)\to0$，再用定理 124.8 中相同的前缀阈值证明。仅有每个任务各自的一致连续性不提供这个共同模量。

**命题 124.13（第 123 节逐层条件与线程完备性的勘注）。** 对第 123 节的逆系统，以下条件必须分开：$z_n\in q_n[X]$ 对每个 $n$ 成立；以及 $\pi_n(z_{n+1})=z_n$ 对每个 $n$ 成立。第 123.2 节“每个有限层都有实现”若被单独用来推出逆极限成员身份，须替换为这两项的合取。
证明与精确定义。取 $X=\{0,1\}$，各层 $Q_n=X$，$q_n$ 和 $\pi_n$ 都是恒等映射。令 $z_n$ 依奇偶交替为 $0,1$；每一层都有实现，但相邻两层不相容，故不在逆极限。

对非空 $X$，若使用实际像 $Q_n=q_n[X]$，每个 $Q_n$ 有限且取离散拓扑，连接映射由兼容读数限制而来，则自然像 $\iota[X]$ 在 $\varprojlim Q_n$ 中稠密。事实上，取线程 $z$ 的任一基本邻域，它只限制有限多个坐标；令 $m$ 为受限坐标的最大值，选 $x$ 使 $q_mx=z_m$。反复使用相容性，便有所有 $n\le m$ 的 $q_nx=z_n$，所以该像点在邻域中。没有坐标限制时任取 $x\in X$ 即可。
因此这里定义
$$
\operatorname{Ghost}(X)=\left(\varprojlim q_n[X]\right)\setminus\iota[X]
$$
才能只计实际有限读数相容后仍无法实现的线程。若改用较大陪域，$X=\{0\}$、各层 $Q_n=\{0,1\}$、$q_n(0)=0$、$\pi_n={\rm id}$ 已给反例：常值 $1$ 线程从未在任何层命中，也不在自然像的闭包中。

代数术语 $\operatorname{ThreadComplete}$ 的定义是 $\iota:X\to\varprojlim Q_n$ 满射；若各层不分离对象，也可等价说商嵌入 $\bar\iota$ 满射。它不是对任意给定拓扑或度量的完备性结论。例如在 $X_{\rm fs}$ 上改取离散距离，空间完备，但前缀线程仍含不属于核心的交替无限串。第 123.3 节与本节命题 124.2 指定前缀拓扑、稠密嵌入和完备载体，才把该具体线程空间识别为度量完备化。

**命题 124.14（第 123.4 节 Hilbert 动力学界的充分条件）。** 设 $H$ 为 Hilbert 空间，$S_n\subseteq H$ 为递增闭子空间，$P_n:H\to S_n$ 为正交投影。每个 $T_n:S_n\to S_n$ 是有界线性算子，并满足对所有 $n\le m$ 和 $u\in S_m$，
$$
P_n(T_mu)=T_n(P_nu).
$$
若有有限 $M\ge0$ 使 $\sup_n\|T_n\|\le M$，则逐层作用保持有界相容线程，并有
$$
\sup_n\|T_nz_n\|\le M\sup_n\|z_n\|.
$$
证明。令 $B=\sup_n\|z_n\|<\infty$，则 $\|T_nz_n\|\le\|T_n\|\|z_n\|\le MB$。而线程相容性给
$P_n(T_mz_m)=T_n(P_nz_m)=T_nz_n$，两项条件俱全。
这将第 123.4 节的算子界明确为上述类型中的充分条件；本命题不把它断言为无条件必要条件，也不从它推出有限支持像保持。

后一个限制可具体检验。取 $H=\ell^2(\mathbb N)$、$S_n$ 为前 $n$ 个坐标子空间，$v_j=2^{-j-1}$，则 $\|v\|^2=1/3$。令 $T_0=0$，$n\ge1$ 时置 $T_nu=u_0P_nv$。它们投影相容且 $\|T_n\|\le\|v\|$，但由有限支持向量 $e_0$ 所给的线程，经逐层作用后重建为无限支持的 $v$。故保持 Hilbert 有界线程与保持原有限支持载体是两项不同要求。

**命题 124.15（第 123.5 节归一化记录 Gram 条件的勘注）。** 有限复矩阵 $G$ 能表示某个有限维 Hilbert 空间内一族归一化记录向量的 Gram 矩阵，当且仅当它是 Hermitian、半正定且对角元全为 $1$。若预先固定记录空间维数为 $r$，还须且只须 $\operatorname{rank}G\le r$；严格正定不是必要条件。
证明。若 $G_{ab}=\langle v_a,v_b\rangle$，则 $c^*Gc=\|\sum_a c_av_a\|^2\ge0$，共轭对称性给 Hermitian 性，归一化给单位对角；秩不超过记录空间维数。
反向由有限维谱分解取 $B$ 使 $G=B^*B$，$B$ 的各列即所需向量，对角条件使各列范数为 $1$。只保留非零特征值可在维数 $\operatorname{rank}G$ 中实现，再嵌入给定的 $r$ 维空间。
至少两个记录全取同一单位向量时，Gram 矩阵全为 $1$，秩为 $1$，合法而奇异。因此第 123.5 节的“Gram 矩阵的正定性”在归一化记录意义下应读作上述半正定条件；它与通道完全正性、动力学像集不变性仍是不同类型的要求。

**约定 124.16（来源、证明范围与后续问题）。** 本节所引 CSA、Z 与 Q 分别指 `CONTEXTUAL_SPACETIME_ARITHMETIC.md`、`CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md` 与本量子卷。CSA 定义 1–3、§§14–16，Z371.1–2、Z477.3，以及 Q54.7、Q57、Q120–122 的引用版本均为仓库提交 `58d94fb6c3b75e5f0fc33f184e510f46949efdca`；Q123 的引用版本为 `71d892f05c219488670b0a10ca6b9bf11b975cfe`。Q54.7 给纤维直径与近似预测的两侧界，Q57 固定特定未来实验族；Q120 使用含参考的过程 diamond 缺陷，Q121–122 的态族缺陷和 Q123 的线程问题各保留原类型。本节将历史参数集明确换成 $X_{\rm fs}$ 并使用上确界，所需证明已逐项给出。

同一基线版本的 `D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction.lean` 中，`bounded_inverse_limit_reconstruction` 在完备内积空间、单调且具有正交投影的子空间序列上，给累积闭子空间与有界相容线程的规范线性等距双射，并给最终残余商的同类表示。`D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.lean` 的 `compatible_unbounded_coordinates` 给实际 $\ell^2$ 坐标截断线程、范数平方为 $n$、无界及无法由单个 $\ell^2$ 向量投影实现等结论。`D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean` 的 `ThreadComplete` 定义为 `stateThread` 满射，`stateThread_bijective_iff_complete_and_separates` 对应线程完备与各层联合分离的合取，不带拓扑完备性的假设或结论。这些声明分别支持所写类型中的既有结果，不承载本节的新前缀缺陷桥。

一般完备延拓与 Heine–Cantor 原理可见钉版 Mathlib（`lake-manifest.json` 的 mathlib 修订 `db584cd6d46c92f209a44c0f1c829460d327499d`，`v4.33.0`）：`Mathlib/Topology/UniformSpace/Completion.lean` 的 `UniformSpace.Completion.extension`、`extension_coe`、`uniformContinuous_extension`、`extension_unique`，以及 `Mathlib/Topology/UniformSpace/HeineCantor.lean` 的 `CompactSpace.uniformContinuous_of_continuous`。延拓的正确限制要求原映射一致连续；目标完备且分离时具有相应唯一性，不能仅凭对任意函数可写下 extension 定义就声称得到延拓。本节是结合这些通常原理与所引仓内模型的 `repo-derived` 普通证明，不提出新颖性或新增 Lean 认证主张。

本节的静态制备模型只比较指定经典输入族的输出态，不保证隐藏参考关联、相干输入行为或自适应过程的模拟；这些要求须另指定联合态或完整过程。定理 124.8 的存在性不提供有效连续模量或高效求最优中心的算法，有限维紧性所得中心存在性也未推广到无限维态空间。下一项研究问题因此是：在增加参考或过程结构后，哪些可检验的连续性与紧性条件仍能给出相应缺陷的精确延拓判据。

<a id="entry-598"></a>

## 追加锚（本行以下为增补区）

<a id="section-125"></a>

## 125. 均匀相干态的局部极限与表示边界

本节复用 Q109 的有限均匀态及定义 124.1 的零下标合法串 $W_L$、紧载体 $\widehat X$ 和有限支持核心 $X_{\rm fs}$。固定左端第 $0$ 位而向右增加长度，取 $\varphi=(1+\sqrt5)/2$、$\alpha=\varphi^{-1}$，于是 $0<\alpha<1$ 且 $\alpha+\alpha^2=1$。记 $D_L=|W_L|=F_{L+2}$，其中 $F_0=0,F_1=1$，特别地 $D_0=1$。在完整 qubit 空间 $\mathcal K_L=(\mathbb C^2)^{\otimes L}$ 中沿用
$$
|\Omega_L\rangle=|\Psi_L\rangle
=D_L^{-1/2}\sum_{w\in W_L}|w\rangle.
$$
所讨论的是这一个指定态族的局部极限及其柱读数的表示条件；数字载体仍区别于 CSA 定义 1–3 的事件档案。以下均为普通数学定义与证明。

**命题 125.1（固定左窗口的约化极限）。** 固定整数 $n\ge1$，令 $L=n+m$，$m\ge1$，并在完整张量积上定义
$$
\rho_n^{(L)}=\operatorname{Tr}_{\{n,\ldots,L-1\}}
|\Omega_L\rangle\langle\Omega_L|.
$$
对 $u,v\in W_n$，有
$$
(\rho_n^{(L)})_{uv}=
\begin{cases}
D_m/D_L,&u_{n-1}=v_{n-1}=0,\\
D_{m-1}/D_L,&\text{其余合法前缀对}.
\end{cases}
$$
含非法前缀的行或列全为零。置
$$
s_n=\sum_{u\in W_n}|u\rangle,\qquad
t_n=\sum_{\substack{u\in W_n\\u_{n-1}=0}}|u\rangle.
$$
当 $L\to\infty$ 且 $n$ 固定时，$\rho_n^{(L)}$ 在迹范数下收敛到
$$
\rho_n=\alpha^{n+1}|s_n\rangle\langle s_n|
       +\alpha^{n+2}|t_n\rangle\langle t_n|.
$$
每个 $\rho_n$ 都正、迹为 $1$、秩恰为 $2$，且在完整 qubit 空间之间满足
$$
\operatorname{Tr}_{\{n\}}\rho_{n+1}=\rho_n.
$$

证明。偏迹的矩阵元是使 $uz$ 与 $vz$ 同时合法的长度 $m$ 尾字 $z$ 的数量除以 $D_L$。若两个前缀末位均为 $0$，任意 $z\in W_m$ 均可；否则 $z$ 的首位必须为 $0$，余下 $m-1$ 位任意合法，数量为 $D_{m-1}$。这个计数也含 $m=1$ 的情形。非法前缀不可能被延长为合法字，故相应行列为零。

由 Binet 公式 $F_k=(\varphi^k-(-\varphi^{-1})^k)/\sqrt5$，固定 $n$ 时有
$$
\lim_{m\to\infty}\frac{D_m}{D_{m+n}}=\alpha^n,
\qquad
\lim_{m\to\infty}\frac{D_{m-1}}{D_{m+n}}=\alpha^{n+1}.
$$
两前缀末位均为 $0$ 时，所列 $\rho_n$ 的矩阵元为 $\alpha^{n+1}+\alpha^{n+2}=\alpha^n$；其余合法对为 $\alpha^{n+1}$，所以它正是逐元极限。固定维数 $2^n$ 下，矩阵元收敛给 Hilbert–Schmidt 范数收敛，再由 $\|B\|_1\le\sqrt{2^n}\|B\|_{\rm HS}$ 给迹范数收敛。

两个系数严格为正，故 $\rho_n$ 正且其核为 $s_n^\perp\cap t_n^\perp$。向量 $t_n$ 非零；合法词 $0^{n-1}1$ 在 $s_n$ 中的系数为 $1$，在 $t_n$ 中为 $0$，而 $0^n$ 在两者中的系数都为 $1$，故两向量线性独立，秩恰为 $2$。这里直接计算极限的秩，并未假定取极限保持有限态的秩。

为核对偏迹，对任意长度 $n$ 的前缀对求
$$
(\operatorname{Tr}_{\{n\}}\rho_{n+1})_{uv}
=\sum_{a\in\{0,1\}}(\rho_{n+1})_{ua,va}.
$$
若 $u,v$ 合法且末位均为 $0$，附 $0$ 与附 $1$ 两项分别是 $\alpha^{n+1}$、$\alpha^{n+2}$，和为 $\alpha^n$。其余合法对只有共同附 $0$ 的项非零，为 $\alpha^{n+1}$。含非法前缀的两项均为零。这证明全矩阵偏迹相容。最后
$$
\rho_1=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix},
\qquad \operatorname{Tr}\rho_1=\alpha+\alpha^2=1;
$$
偏迹保持迹，逐层得到全部归一化。Q109 的有限 Schmidt 秩与谱公式在此只作为既有有限态背景。

**命题 125.2（完整局部代数上的态及局部弱星极限）。** 令 $\mathcal A_n=M_{2^n}(\mathbb C)$，嵌入为 $A\mapsto A\otimes I_2$，以 $\mathcal A_{\rm loc}$ 表示按这些嵌入识别后的代数并，$\mathcal A$ 为其算子范数完备化，即单侧 qubit UHF 代数。存在唯一态 $\omega:\mathcal A\to\mathbb C$ 满足
$$
\omega(A)=\operatorname{Tr}(\rho_n A)\qquad(A\in\mathcal A_n).
$$
将每个有限态 $|\Omega_L\rangle\langle\Omega_L|$ 接上全零乘积尾态，得到 $\mathcal A$ 上的态 $\widetilde\omega_L$，则
$$
\widetilde\omega_L(A)\longrightarrow\omega(A)\qquad(A\in\mathcal A).
$$
这里弱星收敛指 $\sigma(\mathcal A^*,\mathcal A)$ 下逐可观测量收敛。任意其它态延拓，只要在前 $L$ 位与该有限密度一致，也有同一极限。上述代数嵌入不由合法空间上的压缩自动给出。

证明。令 $\omega_n(A)=\operatorname{Tr}(\rho_n A)$。命题 125.1 给
$$
\omega_{n+1}(A\otimes I_2)=\omega_n(A),\qquad
|\omega_n(A)|\le\|A\|,\qquad \omega_n(I)=1.
$$
所以这些泛函在 $\mathcal A_{\rm loc}$ 上定义一个良定、范数为 $1$ 的线性泛函，并唯一连续延拓到 $\mathcal A$。为核对延拓的正性，给定 $B\in\mathcal A$，取局部 $B_j\to B$，则 $B_j^*B_j\to B^*B$ 且 $\omega(B_j^*B_j)\ge0$，故 $\omega(B^*B)\ge0$。$\mathcal A$ 是 $C^*$ 代数，每个正元都是其正平方根的平方，故延拓为正；其单位值仍为 $1$，即为态。稠密性也给唯一性。

全零尾延拓可具体按有限层定义：前 $k\le L$ 位取 $|\Omega_L\rangle\langle\Omega_L|$ 的约化密度，前 $k>L$ 位取
$$
|\Omega_L\rangle\langle\Omega_L|
\otimes|0^{k-L}\rangle\langle0^{k-L}|.
$$
这组密度正、归一且偏迹相容，故由刚才的延拓论证给 $\widetilde\omega_L$。固定 $A\in\mathcal A_n$，当 $L\ge n+1$ 时，
$$
|\widetilde\omega_L(A)-\omega(A)|
\le\|\rho_n^{(L)}-\rho_n\|_1\|A\|\longrightarrow0.
$$
对一般 $A\in\mathcal A$ 及 $\varepsilon>0$，取局部 $B$ 使 $\|A-B\|<\varepsilon$。两态范数均为 $1$，故差值不超过 $2\varepsilon+|\widetilde\omega_L(B)-\omega(B)|$，得到逐点收敛。同一论证只用前 $L$ 位的密度和态范数为 $1$，因而适用于所说的任何延拓。固定窗口的迹范数收敛与这里的弱星收敛，不给出全局密度的迹范数收敛结论。

压缩的区别已有两位反例。令 $Q$ 为 $\mathcal K_2$ 到 $\operatorname{span}\{|00\rangle,|01\rangle,|10\rangle\}$ 的正交投影，$X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$，定义 $\kappa(A)=Q(A\otimes I_2)Q$，视为合法子空间上的算子。因为 $(X\otimes I_2)|01\rangle=|11\rangle$，有
$$
\kappa(X)^2|01\rangle=0,
\qquad
\kappa(X^2)|01\rangle=|01\rangle.
$$
所以这条压缩不是乘法同态，不能用它把 $M_{|W_n|}(\mathbb C)$ 自动组成通常张量嵌入塔。这只否定所写压缩方案，不排除其它受约束代数的构造，也不规定完整局部代数的所有动力学保持无相邻 $1$ 的约束。

**命题 125.3（固定左边界柱律与 Z 圆周概率）。** 对 $u\in\{0,1\}^n$，$n\ge1$，记 $[u]=\{x\in\widehat X:q_nx=u\}$，并约定 $[\varnothing]=\widehat X$。存在唯一 Borel 概率 $\mu$ 满足
$$
\mu([u])=\omega(|u\rangle\langle u|)=
\begin{cases}
\alpha^{n+u_{n-1}},&u\in W_n,\\
0,&u\notin W_n.
\end{cases}
$$
在 Q124.1 对 Z 卷载体 $K$ 与 $\widehat X$ 的相同数字及 Borel 结构的识别下，$\mu=(s_Z)_*\lambda$，其中 $\lambda$ 是 Z396.1 的圆周长度概率，$s_Z:\mathbb T\to K$ 是 Z400.1 的 Borel 截面。此柱律的初始分布与行随机转移矩阵为
$$
q=(\alpha,\alpha^2),\qquad
P=\begin{pmatrix}\alpha&\alpha^2\\1&0\end{pmatrix}.
$$
它等同于虚拟左邻位固定 $x_{-1}=0$ 后由 $P$ 生成的边界律，而非以
$$
\pi=\frac{(\varphi^2,1)}{\varphi^2+1}
$$
为初始分布的平稳 Parry 律。

证明。命题 125.1 的对角元给显示的柱读数。为建立其 Borel 概率实现而不只保留一组有限分布，记 Z 卷相位映射为 $H_Z$，则 $H_Zs_Z=\operatorname{id}_{\mathbb T}$。$s_Z$ 为 Borel，故 $\nu=(s_Z)_*\lambda$ 是 $K$ 上的 Borel 概率。

将 Z381.2 对应于合法词 $u$ 的柱集和定向开弧分别记作 $C_u^Z$、$A_u^Z$；其两个端点为 $E_i,E_j$，该条定向弧的长度为 $\alpha^{n+u_{n-1}}$。那里的完整端点公式给
$$
C_u^Z=H_Z^{-1}(A_u^Z)\cup\{e_i^+,e_j^-\}.
$$
由于截面逐点落在相应相位纤维中，这个等式蕴含
$$
s_Z^{-1}(C_u^Z)\mathbin{\triangle}A_u^Z
\subseteq\{E_i,E_j\}.
$$
Z396.1 给两个端点的质量均为零，开弧的质量等于其长度，因而
$$
\nu(C_u^Z)=\lambda(s_Z^{-1}(C_u^Z))
=\lambda(A_u^Z)=\alpha^{n+u_{n-1}}.
$$
非法柱为空，空前缀柱为整个载体，故可取 $\mu=\nu$。前缀柱集连同空集构成生成 Borel 集的 $\pi$ 系统：交集或为空、或为其中更深的柱集，且这些柱集是可数拓扑基。概率测度的唯一性定理遂使任意具有全部相同柱读数的 Borel 概率都等于 $\nu$。这里不需要 $H_Z$ 或 $s_Z$ 为双射，也不忽略开弧内部可能存在的分裂纤维。

每个合法柱都具有正质量，可以逐柱计算条件概率。若 $u_{n-1}=0$，则
$$
\frac{\mu([u0])}{\mu([u])}=\alpha,
\qquad
\frac{\mu([u1])}{\mu([u])}=\alpha^2.
$$
若 $u_{n-1}=1$，则 $u1$ 非法，而
$$
\frac{\mu([u0])}{\mu([u])}
=\frac{\alpha^{n+1}}{\alpha^{n+1}}=1,
\qquad
\frac{\mu([u1])}{\mu([u])}=0.
$$
初始一位柱质量给 $q$，上述比值只依赖末位，证明 Markov 性及所列 $P$；$q$ 正好是 $P$ 的第 $0$ 行。由 $\pi_1=\pi_0\alpha^2$ 与 $\pi_0+\pi_1=1$，得到所列唯一平稳分布，亦即 `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY.md` 第1594部的分布。

明确地，对数字左移 $\sigma(x)_j=x_{j+1}$，有
$$
\mu(\sigma^{-1}[1])=(qP)_1=\alpha^3
\ne\alpha^2=\mu([1]).
$$
所以非平稳性是相对于数字左移而言；它不把数字左移与 Z 卷的算术后继或圆周旋转认作同一变换。与 Z 概率相同的只是对角柱数据，不能据此认定整个量子态相同：例如 $\langle0|\rho_1|1\rangle=\alpha^2>0$，是柱概率本身未指定的相干读数。

**命题 125.4（有限支持基上的 normal 密度障碍及其表示边界）。** 在 $H_{\rm fs}=\ell^2(X_{\rm fs})$ 中取标准基 $(e_x)_{x\in X_{\rm fs}}$，对每个有限词 $u$ 定义柱投影
$$
C_ue_x=\mathbf1_{\{q_{|u|}x=u\}}e_x.
$$
不存在正迹类算子 $R$ 满足 $\operatorname{Tr}R=1$ 且同时对所有有限词有 $\operatorname{Tr}(RC_u)=\mu([u])$。尽管每个有限深度的全部柱读数都可由该空间上的有限秩密度精确实现，这些实现不能由一个这样的 $R$ 统一承担。此外，$\mu$ 的每个单点质量均为零，$\mu(X_{\rm fs})=0$。局部态 $\omega$ 仍有 GNS 表示及其中的秩一密度实现。

证明。有限支持核心可写为
$$
X_{\rm fs}=\bigcup_{N\ge0}\{u0^\infty:u\in W_N\},
$$
故它可数；补零保持合法性。对任意 $x\in\widehat X$，递减的柱集 $[q_nx]$ 的交恰为 $\{x\}$，由概率测度的从上连续性有
$$
\mu(\{x\})=\lim_{n\to\infty}\mu([q_nx])
\le\lim_{n\to\infty}\alpha^n=0.
$$
单点为闭集，可数个这样的单点给 $X_{\rm fs}$ 为 Borel 零测集。

假设所说的 $R$ 存在。对每个 $x\in X_{\rm fs}$ 及 $n\ge1$，秩一投影满足 $|e_x\rangle\langle e_x|\le C_{q_nx}$。正迹类算子定义正迹泛函；具体地，对正有界 $B$ 有 $\operatorname{Tr}(RB)=\operatorname{Tr}(R^{1/2}BR^{1/2})\ge0$。所以
$$
0\le\langle e_x,Re_x\rangle
\le\operatorname{Tr}(RC_{q_nx})
=\mu([q_nx])\le\alpha^n\longrightarrow0.
$$
每个基对角元均为零，而正迹类算子的迹等于任意可数正交标准基上的对角元之和，得到
$$
1=\operatorname{Tr}R
=\sum_{x\in X_{\rm fs}}\langle e_x,Re_x\rangle=0,
$$
矛盾。证明没有要求 $R$ 对角化或与柱投影对易，也没有假定整个 UHF 代数在 $H_{\rm fs}$ 上具有某个自然表示。

为给出有限深度的准确对照，对固定 $N\ge1$ 定义
$$
R_N=\sum_{u\in W_N}\mu([u])
|e_{u0^\infty}\rangle\langle e_{u0^\infty}|.
$$
这些不同的补零串是正交基标记，系数非负且和为 $1$，故 $R_N$ 为正归一有限秩密度。对 $|v|\le N$，深度 $N$ 的细柱分割 $[v]$，从而
$$
\operatorname{Tr}(R_NC_v)
=\sum_{\substack{u\in W_N\\u|_{|v|}=v}}\mu([u])
=\mu([v]).
$$
这里仅匹配对角柱读数，没有把 $R_N$ 与 Q109 的相干纯态或其约化矩阵认作同一密度。

最后直接给 $\omega$ 的通常 GNS 构造。取
$$
\mathcal N_\omega=\{B\in\mathcal A:\omega(B^*B)=0\},
\qquad
\langle[B],[C]\rangle=\omega(B^*C)
$$
并以第二变量线性的内积约定使用此式。正性作用于 $(B+zC)^*(B+zC)$ 给 Cauchy–Schwarz 不等式，故零半范数元与所有元正交，商 $\mathcal A/\mathcal N_\omega$ 上的内积良定。由 $A^*A\le\|A\|^2I$ 得
$$
\omega(B^*A^*AB)\le\|A\|^2\omega(B^*B).
$$
因此 $\mathcal N_\omega$ 是左理想，左乘 $[B]\mapsto[AB]$ 良定且范数至多 $\|A\|$；它延拓到商内积空间的完备化 $H_\omega$，记作 $\pi_\omega(A)$。左乘保持乘法和单位，且由内积公式其伴随为 $\pi_\omega(A^*)$，所以 $\pi_\omega$ 是幺星表示。向量 $\xi=[I]$ 的范数为 $1$，$\pi_\omega(A)\xi=[A]$ 的线性张成稠密，故 $\xi$ 循环，且
$$
\omega(A)=\langle\xi,\pi_\omega(A)\xi\rangle
=\operatorname{Tr}_{H_\omega}
\bigl(|\xi\rangle\langle\xi|\,\pi_\omega(A)\bigr).
$$
秩一密度位于 $B(H_\omega)$，其向量态限制到 $\pi_\omega(\mathcal A)$ 不因此必为纯态。normal 实现依赖指定的可观测量与表示，不能只由抽象 Hilbert 空间的基数判断。因而本命题给的是有限支持基及上述柱投影的实现障碍，同时保留了全局代数态及其它 Hilbert 表示的实现。

**约定 125.5（引用与证明范围）。** Q、Z、CSA 分别指本量子卷、`CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md`、`CONTEXTUAL_SPACETIME_ARITHMETIC.md`。本节所引 Q109、Q123–124、Z381.2、Z396.1、Z400.1、CSA 定义 1–3 及 `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY.md` 第1594部，均取仓库提交 `c225a37b44971d289ae51b8b324f5cef78e31b82` 的版本。Q123–124 的载体与相容性问题在这里落实为有限相干态、局部代数态和指定表示中的柱读数问题；所用局部极限不另申报 Q109 的有限 Schmidt 结论。

同一版本 `D5/S1/Digit/Infinite/WindowCylinderPartition.lean` 的 `window_cylinder_partition` 给合法窗口的区间几何、准确弧长及定向端点纤维，其结论不含本节的量子态构造。`D5/S3/Quantum/Measurements/OrthogonalAdditivity.lean` 的 `orthogonal_additivity` 在 `SequentiallyNormal` 与 `strong_complete` 等假设下给正交投影族的可数可加性；命题 125.4 使用直接的正迹类论证，不把这些假设省略后援引该声明。

钉版 Mathlib 修订 `db584cd6d46c92f209a44c0f1c829460d327499d` 的 `Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` 提供 `PositiveLinearMap.gnsStarAlgHom`，该文件明确将单位循环向量的构造列为 TODO，故它不作为上文完整循环向量结论的现成证明；上文已独立给出通常 GNS 构造。本节为结合所引模型与标准概率、算子代数方法的 `repo-derived` 普通推导，不提出新颖性或新增 Lean 认证主张。

<a id="entry-600"></a>

## 追加锚（本行以下为增补区）

<a id="section-126"></a>

## 126. 固定尾零载体上的事件组合预算与精确最优误差

固定非负整数 $K,N$ 与正整数 $M$，令 $\alpha=(\sqrt5-1)/2$，$F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$。沿用 Q123–125 的前缀方向，以
$$
X=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\ \text{对所有 }j\ge0\},
\qquad W_n=q_n[X],\qquad W_0=\{\varnothing\}
$$
表示完整合法流及其长度 $n$ 前缀，$q_nx=(x_0,\ldots,x_{n-1})$。记 $[u]=\{x\in X:q_nx=u\}$，$[\varnothing]=X$，并固定尾零载体
$$
S_K=\{w0^\infty:w\in W_K\},\qquad
D_K=|S_K|=|W_K|=F_{K+2}.
$$
$\operatorname{Prob}(S_K)$ 指集中在这个指定集合上的全部概率，允许个别原子质量为零；$U_K$ 为每点质量 $1/D_K$ 的均匀概率，即 Q109 有限均匀态的基测量分布补零后的概率。

目标取 Q125.3 的固定虚拟左邻位为零的边界律，其全部柱读数在此明确为
$$
\mu([\varnothing])=1,\qquad
\mu([u])=
\begin{cases}
\alpha^{n+u_{n-1}},&u\in W_n,\ n\ge1,\\
0,&u\notin W_n.
\end{cases}
$$
这些权重由 $\alpha+\alpha^2=1$ 相容：末位为零的柱分成权重比为 $\alpha,\alpha^2$ 的两柱，末位为一的柱只能接零且质量不变；初层质量之和为一。因此通常的相容有限分布延拓与柱集唯一性给出 $X$ 上的唯一 Borel 概率。该律不对数字左移平稳，因为 $\mu(x_1=1)=\alpha^3\ne\alpha^2=\mu(x_0=1)$。这里的数字流与概率事件保留各自类型，不与 CSA 定义 1–3 的情境档案混同。

**命题 126.1（同层柱集组合预算的精确极小极大值）。** 对 $\nu\in\operatorname{Prob}(S_K)$ 定义
$$
d_M(\nu,\mu)=\sup_{n\ge1}\,
\max_{\substack{J\subseteq W_n\\|J|\le M}}
\left|\nu\left(\bigcup_{u\in J}[u]\right)
      -\mu\left(\bigcup_{u\in J}[u]\right)\right|.
$$
每个 $J$ 中的柱集必须有同一个深度 $n$，空 $J$ 允许。则
$$
\min_{\nu\in\operatorname{Prob}(S_K)}d_M(\nu,\mu)
=\min\left(1,\frac{M}{D_K}\right).
$$
若 $M<D_K$，唯一经典最优分布是 $U_K$；若 $M\ge D_K$，全部 $\nu$ 的误差均为 $1$。后一情形在 $K\ge1$ 时不唯一，在 $K=0$ 时定义域本身只有 $\delta_{0^\infty}=U_0$。对 $U_K$，任一有限深度的上述事件差都严格小于所列上确界，故不能把对深度的 $\sup$ 换成 $\max$。

证明。将 $D=D_K$ 个原子质量排序为 $p_1\ge\cdots\ge p_D\ge0$，令 $m=\min(M,D)$、$T_m=\sum_{i=1}^mp_i$。在每个 $n>K$，前 $m$ 个原子的深度 $n$ 前缀给两两不交的隔离柱，每柱在 $\mu$ 下均有质量 $\alpha^n$，故
$$
d_M(\nu,\mu)\ge |T_m-m\alpha^n|.
$$
令 $n\to\infty$，得到 $d_M(\nu,\mu)\ge T_m\ge m/D$，最后一步是最大 $m$ 个质量的平均值不小于全部质量的平均值。

下面证明 $U_K$ 的上界。若 $1\le n\le K$、$u\in W_n$ 且 $b=u_{n-1}$，合法延长计数给
$$
U_K([u])=\frac{F_{K-n+2-b}}{D_K}.
$$
末位零时可接任意长度 $K-n$ 的合法尾字；末位一且仍需延长时，下一位被迫为零。这两种计数也包含 $n=K$ 时的空延长，分别为 $F_2=F_1=1$。置 $r=K-n+2-b$、$s=K+2$，则 $1\le r<s$、$s-r=n+b$。Binet 公式给
$$
F_r-\alpha^{s-r}F_s
=\frac{-(-\alpha)^r+\alpha^{s-r}(-\alpha)^s}{\sqrt5},
\qquad
\left|F_r-\alpha^{s-r}F_s\right|
\le\frac{2\alpha}{\sqrt5}<1.
$$
因此每个这样的柱误差严格小于 $1/D_K$。

若 $n>K$，每个柱在 $U_K$ 下的质量为零或 $1/D_K$，而
$$
0<\mu([u])\le\alpha^n\le\alpha^{K+1}<\frac1{D_K}
\qquad(u\in W_n).
$$
最后一个严格不等式在 $K=0$ 时是 $\alpha<1$；在 $K\ge1$ 时，深度 $K$ 的柱权重 $\alpha^K$ 与 $\alpha^{K+1}$ 均出现且总和为一，故其平均值满足
$$
\alpha^{K+1}<\frac1{D_K}<\alpha^K.
$$
这也使每个深柱误差严格小于 $1/D_K$。同层柱集互不相交，对至多 $M$ 项求和并用三角不等式，得到事件差至多 $M/D_K$；概率差又至多为一。结合下界即得最优值。$M<D_K$ 时，有限深度事件差严格小于 $M/D_K$；$M\ge D_K$ 时，有限层的 $\mu_n$ 对每个合法词赋正质量，所以不存在两概率相差为一的事件，仍严格小于上确界一。

当 $M<D$ 且 $\nu$ 最优时，下界迫使 $T_M=M/D$。于是
$$
\sum_{i\le M<j}(p_i-p_j)=D T_M-M=0.
$$
每项非负，故所有跨越分界的差均为零；两侧均非空，遂使全部质量相等，证明唯一性。若 $M\ge D$，下界已为一，概率上界给每个 $\nu$ 都取一，包括 $K=0$ 的单点定义域。

**命题 126.2（有限窗口总变差及截断的最优者）。** 记 $\nu_n=(q_n)_*\nu$、$\mu_n=(q_n)_*\mu$，在有限集 $W_n$ 上取
$$
\operatorname{TV}(p,q)=\frac12\sum_{u\in W_n}|p(u)-q(u)|.
$$
则
$$
\min_{\nu\in\operatorname{Prob}(S_K)}
\max_{0\le n\le N}\operatorname{TV}(\nu_n,\mu_n)
=\begin{cases}
0,&N\le K,\\
1-D_K\alpha^N,&N>K.
\end{cases}
$$
$N\le K$ 时最优者恰为满足 $\nu_N=\mu_N$ 的分布；$N>K$ 时最优者恰为原子质量
$$
p_w=\nu(\{w0^\infty\})\ge\alpha^N
\qquad(w\in W_K)
$$
的分布。令 $\tau_Kx=(q_Kx)0^\infty$、$\nu^{\rm cut}=(\tau_K)_*\mu$，则 $\nu^{\rm cut}$ 是唯一同时对所有非负整数 $N$ 最优的分布。$U_K$ 与 $\nu^{\rm cut}$ 都对每个固定 $N>K$ 最优，但
$$
d_1(\nu^{\rm cut},\mu)=\alpha^K,
\qquad
\alpha^K>\frac1{D_K}\quad(K\ge1).
$$
$K=0$ 时两分布相同，$N=0$ 的误差为零，$N>0$ 的最优误差为 $1-\alpha^N$，而 $d_1=1$。

证明。前缀投影收缩总变差，故对每个固定 $\nu$ 有
$$
\max_{0\le n\le N}\operatorname{TV}(\nu_n,\mu_n)
=\operatorname{TV}(\nu_N,\mu_N).
$$
当 $N\le K$ 时，$q_N:S_K\to W_N$ 满射，任意目标前缀都可补零至长度 $K$，因此可以给这些原像分配质量以精确实现 $\mu_N$；总变差为零当且仅当两有限分布相同。这也包括 $N=0$，此时所有概率的空前缀分布相同。

当 $N>K$ 时，$\nu_N$ 集中在
$$
A_{K,N}=\{w0^{N-K}:w\in W_K\}\subseteq W_N,
\qquad |A_{K,N}|=D_K
$$
上，其中每个词在 $\mu_N$ 下的质量都是 $a=\alpha^N$。有限概率的重叠质量公式遂给出精确式
$$
\operatorname{TV}(\nu_N,\mu_N)
=1-\sum_{w\in W_K}\min(p_w,a)
\ge1-D_Ka.
$$
逐项 $\min(p_w,a)\le a$，等号成立当且仅当每项 $p_w\ge a$。命题 126.1 证明中的 $a\le\alpha^{K+1}<1/D_K$ 说明这些条件可由 $U_K$ 同时满足，故下界可达。

截断概率在所有 $n\le K$ 精确保持柱读数，且其原子质量为
$$
\nu^{\rm cut}(\{w0^\infty\})=
\begin{cases}
\alpha^{K+w_{K-1}},&K\ge1,\\
1,&K=0.
\end{cases}
$$
$K\ge1$ 时每项至少为 $\alpha^{K+1}$，$K=0$ 时唯一质量为一，所以它也满足每个 $N>K$ 的等号条件。反过来，同时最优必在 $N=K$ 精确实现 $\mu_K$；$q_K:S_K\to W_K$ 是双射，故原子质量被唯一确定为截断概率。这证明全部窗口同时最优的唯一性，并不把固定深窗口的两类最优者分开。

为计算截断概率的 $d_1$，$n\le K$ 的柱误差为零。$K\ge1$ 且 $n>K$ 时，含有支撑原子的柱误差为 $p_w-\alpha^n$，其中 $\alpha^{K+1}\le p_w\le\alpha^K$；不含支撑原子的柱误差至多为 $\alpha^n\le\alpha^{K+1}$。故 $d_1\le\alpha^K$，而 $[0^n]$ 上的差为 $\alpha^K-\alpha^n$，趋于 $\alpha^K$，证明等号。$K=0$ 时同一柱上的差为 $1-\alpha^n$，上确界为一。命题 126.1 中的严格平均值界给 $K\ge1$ 时与 $1/D_K$ 的严格差异。因此，精确保留截至 $K$ 的读数与优化全深度的受限事件误差是不同任务，虽然后者的均匀最优者与截断概率都优化每个 $N>K$ 的固定窗口。

由命题 126.1，固定 $M$ 时最优误差随 $K\to\infty$ 趋于零；若正整数预算 $M_K$ 随 $K$ 变化，则该误差趋零当且仅当 $M_K/D_K\to0$。$M$ 只计一次事件表达允许使用的同深度柱集数，不是运行时间、能量或物理存储量。若完全取消这个数目的限制，有限层事件变分式给全层事件差的最大值为 $\operatorname{TV}(\nu_n,\mu_n)$；对任意固定 $K$ 与 $\nu\in\operatorname{Prob}(S_K)$，事件 $A_{K,n}$ 的差为 $1-D_K\alpha^n$，故全部深度上的上确界为一。这是 Z458.5 的有限或可数支撑对无原子概率的既有分离机制在前缀事件中的体现，不另作为新增结论。

量子读数只给如下带条件的下界。固定 $n>K$，在 $\mathcal K_n=(\mathbb C^2)^{\otimes n}$ 的计算基上，令 $P_{K,n}$ 为投到 $\operatorname{span}\{|u\rangle:u\in A_{K,n}\}$ 的正交投影。设 $\sigma_n,\rho_n$ 为密度算子，且
$$
\sigma_n=P_{K,n}\sigma_nP_{K,n},\qquad
\langle u|\rho_n|u\rangle=\mu_n(u)
\quad(u\in\{0,1\}^n),
$$
其中非法词的目标对角质量为零。以 $D(\sigma,\rho)=\tfrac12\|\sigma-\rho\|_1$ 记迹距，则
$$
D(\sigma_n,\rho_n)
\ge\left|\operatorname{Tr}\bigl(P_{K,n}(\sigma_n-\rho_n)\bigr)\right|
=1-D_K\alpha^n.
$$
证明此测量界只需将迹零 Hermitian 算子 $H=\sigma_n-\rho_n$ 写成正负谱部分 $H_+-H_-$：两部分的迹均为 $\|H\|_1/2$，而 $0\le P_{K,n}\le I$ 使 $\operatorname{Tr}(P_{K,n}H)$ 位于这两个相反界之间。支撑条件使 $\operatorname{Tr}(P_{K,n}\sigma_n)=1$，指定对角律使另一迹为 $D_K\alpha^n$。若每个 $n>K$ 的前缀都满足所列条件，则由迹距至多为一得到全深度上确界一。仅有秩或 Hilbert 空间维数不能推出这里的支撑条件；经典最优等式也不直接给量子迹距的等号或相干态最优者唯一性。

本节引用的 Q109、Q123–124、Z381.2（柱弧）、Z396.1（长度概率）、Z400.1（Borel 截面）、Z458.5 及 CSA 定义 1–3，取仓库提交 `ca874c0d5f5c42b3546795595814b36df13d1013`；Q125.3 的正文版本为 `7af72f9910546ca2aa0bfa3a6bbaed4d8a393efb`。前一提交的 `D5/S3/TotalVariation/Metric.lean` 中 `total_variation_eq_sup_event_gap` 给等质量有限函数的事件变分式，`D5/S3/TotalVariation/DataProcessing.lean` 中 `total_variation_channel_le` 给随机通道收缩，`D5/S1/Scale/FibonacciErrorRatio.lean` 中 `fibonacci_golden_residual` 给相邻 Fibonacci 数的黄金残差。这些是所用既有输入；本节的两条最优性命题及条件量子界为 `repo-derived` 普通数学推导，不据此提出外部新颖性、Lean 准入或完整 Lean 认证主张。

<a id="entry-602"></a>

## 追加锚（本行以下为增补区）

<a id="section-127"></a>

## 127. 固定尾零支撑下相干局部态的精确迹距离

固定整数 $n>K\ge0$，令 $\alpha=(\sqrt5-1)/2$、$F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$，并沿用从第 $0$ 位向右的前缀方向。记
$$
W_j=\{w\in\{0,1\}^j:w_iw_{i+1}=0\ \text{对所有 }0\le i<j-1\},
\qquad W_0=\{\varnothing\},
\qquad \mathcal K_n=(\mathbb C^2)^{\otimes n}.
$$
在完整 $n$ qubit 空间的计算基上，取未归一化向量及指定目标
$$
s_n=\sum_{u\in W_n}|u\rangle,
\qquad
t_n=\sum_{\substack{u\in W_n\\u_{n-1}=0}}|u\rangle,
\qquad
\rho_n=\alpha^{n+1}|s_n\rangle\langle s_n|
       +\alpha^{n+2}|t_n\rangle\langle t_n|.
$$
这正是 Q125.1 的相干局部极限；非法词方向上的行、列均为零。预算固定的是具体计算基支撑
$$
A=A_{K,n}=\{w0^{n-K}:w\in W_K\},
\qquad
P=P_{K,n}=\sum_{u\in A}|u\rangle\langle u|,
\qquad
\mathcal F_{K,n}=\{\sigma\ge0:\operatorname{Tr}\sigma=1,\ \sigma=P\sigma P\}.
$$
可行态允许混合及支撑内的任意相干。以
$$
d_{\rm tr}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1,
\qquad \|X\|_1=\operatorname{Tr}\sqrt{X^*X}
$$
采用半迹范数约定，字母 $D$ 只用于计数。以下简记
$$
D=F_{K+2},\qquad B=F_{n+1},\qquad C=F_n,\qquad b=B-D,
$$
$$
m=D\alpha^n,\qquad
\delta=\alpha^{2n+3}BC,\qquad
\eta=\alpha^{2n+3}bC,\qquad
c=1-m-\delta,
$$
并置
$$
|a\rangle=D^{-1/2}\sum_{u\in A}|u\rangle,
\qquad \tau_{K,n}=|a\rangle\langle a|.
$$

**命题 127.1（指定相干目标的尾零最优误差）。** 对所有整数 $n>K\ge0$，$\tau_{K,n}$ 达到
$$
e_{K,n}=\min_{\sigma\in\mathcal F_{K,n}}d_{\rm tr}(\rho_n,\sigma).
$$
精确值 $e_{K,n}$ 是三次方程
$$
x^3-cx-\eta=0
$$
的唯一严格正实根。边界为
$$
e_{K,K+1}=\alpha^{K+2}\sqrt{F_{K+1}F_{K+3}},
\qquad e_{0,1}=\sqrt2\,\alpha^2.
$$
若 $\mu_n(u)=\langle u|\rho_n|u\rangle$ 为计算基读数，在全部集中于 $A$ 的经典概率 $\nu$ 上取
$$
\operatorname{TV}(\nu,\mu_n)
=\frac12\sum_{u\in\{0,1\}^n}|\nu(u)-\mu_n(u)|,
$$
则有严格比较
$$
e_{K,n}>1-m
=\min_{\nu:\,\nu(A)=1}\operatorname{TV}(\nu,\mu_n).
$$
其中经典最小值由 $\tau_{K,n}$ 的对角分布达到。固定 $K$ 后，同一个有限均匀态
$$
|\Psi_K\rangle=D^{-1/2}\sum_{w\in W_K}|w\rangle
$$
接上全零尾部，给出所有 $n>K$ 的上述量子最优者，因为
$$
\tau_{K,n}=|\Psi_K\rangle\langle\Psi_K|
\otimes|0^{n-K}\rangle\langle0^{n-K}|.
$$
$K=0$ 时 $|\Psi_0\rangle$ 按空张量积的单位向量理解。

证明。先核对计数与归一化。长度 $n\ge1$ 的合法词中，末位零、末位一的数量分别是 $B=F_{n+1}$、$C=F_n$：末位零可由任意长度 $n-1$ 合法词接零得到；末位一在 $n\ge2$ 时由长度 $n-2$ 合法词接 $01$ 得到，$n=1$ 时两类各有一词。连同 $|W_0|=1,|W_1|=2$，这给 $|W_j|=F_{j+2}$。补零把 $W_K$ 单射到末位零的一类，故 $|A|=D\le B$、$b\ge0$，且 $C,D>0$。Fibonacci 数从下标 $2$ 起严格递增，所以在本参数域内 $b=0$ 当且仅当 $n=K+1$。

由 $\alpha+\alpha^2=1$，$\rho_n$ 的合法对角元为
$$
\mu_n(u)=
\begin{cases}
\alpha^n,&u_{n-1}=0,\\
\alpha^{n+1},&u_{n-1}=1.
\end{cases}
$$
非法词的对角元为零。恒等式
$$
\alpha^n(F_{n+1}+\alpha F_n)=1
$$
在 $n=1$ 时是 $\alpha(1+\alpha)=1$；若它在 $n$ 成立，则
$$
\alpha^{n+1}(F_{n+2}+\alpha F_{n+1})
=\alpha^n\bigl(\alpha(1+\alpha)F_{n+1}+\alpha F_n\bigr)
=\alpha^n(F_{n+1}+\alpha F_n)=1.
$$
因此所列正算子 $\rho_n$ 的迹为一，而且
$$
\operatorname{Tr}(P\rho_n)=m,
\qquad 0<m\le B\alpha^n=1-C\alpha^{n+1}<1.
$$

现在证明最优性。在本证明内简写 $\tau=\tau_{K,n}$。由于 $A$ 的全部词都以零结尾，
$$
Ps_n=Pt_n=\sqrt D\,|a\rangle.
$$
$Q=P-\tau$ 是正交投影，$R=I-Q$ 也是正交投影，且 $Qs_n=Qt_n=0$。取 $\operatorname{ran}Q$ 的正交标准基 $(q_j)_{j=1}^{D-1}$，以 $R$ 及 $|a\rangle\langle q_j|$ 为 Kraus 算子。它们满足
$$
R^*R+\sum_{j=1}^{D-1}
\bigl(|a\rangle\langle q_j|\bigr)^*
\bigl(|a\rangle\langle q_j|\bigr)
=R+Q=I,
$$
故
$$
\Phi(X)=RXR+\operatorname{Tr}(QX)\tau
$$
是完全正保迹通道。$Q\rho_n=\rho_nQ=0$ 使 $\Phi(\rho_n)=\rho_n$。另一方面，$RP=PR=\tau$，所以每个 $\sigma\in\mathcal F_{K,n}$ 都满足
$$
R\sigma R=\langle a|\sigma|a\rangle\tau,
\qquad
\operatorname{Tr}(Q\sigma)=1-\langle a|\sigma|a\rangle,
\qquad \Phi(\sigma)=\tau.
$$
这里 $D=1$ 时 $Q=0$，Kraus 求和为空，等式仍成立。由迹距离在通道下的收缩性，
$$
d_{\rm tr}(\rho_n,\tau)
=d_{\rm tr}(\Phi(\rho_n),\Phi(\sigma))
\le d_{\rm tr}(\rho_n,\sigma).
$$
收缩性也可直接从正负谱部分核对：对 Hermitian 算子 $Y=Y_+-Y_-$，正性、保迹性与三角不等式给
$$
\|\Phi(Y)\|_1
\le\operatorname{Tr}\Phi(Y_+)+\operatorname{Tr}\Phi(Y_-)
=\operatorname{Tr}Y_++\operatorname{Tr}Y_-=\|Y\|_1.
$$
$\tau$ 本身可行，故最小值确由它达到。$\Phi$ 在这里是比较态的数学通道，不以它属于某个物理可实现的制备资源集为前提。

为求这个最小值，置 $H=\rho_n-\tau$。将合法词分成三个互不相交的词组：$A$、末位零但不在 $A$ 的词、末位一的词。$H$ 在各非空词组的均匀向量张成空间之外为零。由于 $C>0$，始终定义
$$
|v\rangle=C^{-1/2}\sum_{\substack{u\in W_n\\u_{n-1}=1}}|u\rangle.
$$
当 $b>0$ 时再定义
$$
|z\rangle=b^{-1/2}\sum_{\substack{u\in W_n\setminus A\\u_{n-1}=0}}|u\rangle.
$$
此时 $(a,z,v)$ 是正交标准组，其上的实际三维压缩为
$$
H_3=\alpha^n
\begin{pmatrix}
D&\sqrt{Db}&\alpha\sqrt{DC}\\
\sqrt{Db}&b&\alpha\sqrt{bC}\\
\alpha\sqrt{DC}&\alpha\sqrt{bC}&\alpha C
\end{pmatrix}
-\operatorname{diag}(1,0,0).
$$
当 $b=0$ 时不定义空词组的归一化向量 $z$，只用 $(a,v)$，实际二维压缩为
$$
H_2=\alpha^n
\begin{pmatrix}
D&\alpha\sqrt{DC}\\
\alpha\sqrt{DC}&\alpha C
\end{pmatrix}
-\operatorname{diag}(1,0).
$$
在两种情形下都有 $\operatorname{Tr}H=0$。对 $y\perp a$，
$$
\langle y|H|y\rangle=\langle y|\rho_n|y\rangle\ge0,
\qquad
\langle a|H|a\rangle=m-1<0.
$$
若负谱子空间至少二维，它与 $a^\perp$ 有非零交，便同时给出严格负和非负的二次型值，矛盾。因此 $H$ 恰有一个负特征值，记为 $-e$，其中 $e>0$。迹为零使正特征值之和为 $e$，从而 $\|H\|_1/2=e=e_{K,n}$。

接着计算不变量。$\rho_n$ 在整个末位零类与末位一类的两个归一化均匀向量上具有矩阵
$$
\alpha^n
\begin{pmatrix}
B&\alpha\sqrt{BC}\\
\alpha\sqrt{BC}&\alpha C
\end{pmatrix}.
$$
其行列式为
$$
\alpha^{2n}(\alpha-\alpha^2)BC
=\alpha^{2n+3}BC=\delta>0,
$$
其中 $\alpha-\alpha^2=\alpha^3$。这个二维矩阵之外 $\rho_n$ 为零，且其迹为一，所以
$$
\operatorname{Tr}\rho_n^2=1-2\delta,
\qquad
\operatorname{Tr}H^2
=\operatorname{Tr}\rho_n^2-2\langle a|\rho_n|a\rangle+1
=2(1-m-\delta)=2c.
$$
$H\ne0$ 为 Hermitian 算子，故 $c>0$。

当 $b>0$ 时，$\rho_n$ 的三维压缩秩为二、行列式为零。将它的第一对角元减去一，行列式恰减去对应的余子式，得到
$$
\det H_3
=-\alpha^{2n}(\alpha-\alpha^2)bC
=-\eta.
$$
迹零三维矩阵的二次基本对称式为 $-\operatorname{Tr}H_3^2/2=-c$，于是
$$
\det(\lambda I_3-H_3)=\lambda^3-c\lambda+\eta.
$$
代入唯一负特征值 $\lambda=-e$ 得 $e^3-ce-\eta=0$。反过来，每个严格正实根 $x$ 都使 $-x$ 成为 $H_3$ 的负特征值，故严格正实根唯一。

当 $b=0$ 时使用实际的 $H_2$：它的迹为零、平方迹为 $2c$，所以
$$
\det H_2=-c,\qquad
\operatorname{spec}(H_2)=\{-\sqrt c,\sqrt c\}.
$$
此时 $\eta=0$，三次方程是 $x(x^2-c)=0$，唯一严格正实根仍是 $e=\sqrt c$；二维行列式是 $-c$，不是三维补零矩阵的零行列式。

在边界 $n=K+1$，有 $D=B$，归一化恒等式进一步把实际二维矩阵写成
$$
H_2=\alpha^{n+1}
\begin{pmatrix}
-C&\sqrt{DC}\\
\sqrt{DC}&C
\end{pmatrix}.
$$
因此
$$
e_{K,K+1}^2=\alpha^{2n+2}C(C+D)
=\alpha^{2K+4}F_{K+1}F_{K+3},
$$
由 $e_{K,K+1}>0$ 即得所列平方根。$K=0$ 时 $D=1$，可行支撑为 $|0^n\rangle$ 张成的一维空间，上述通道与谱论证对每个 $n>0$ 仍适用；其中 $n=1$ 给 $C=D=1$，故 $e_{0,1}=\sqrt2\,\alpha^2$。

最后核对经典最优值与严格差距。显式对角律在 $A$ 上每词赋质量 $\alpha^n$，总质量为 $m$。对任意 $\nu(A)=1$，总变差的事件界给
$$
\operatorname{TV}(\nu,\mu_n)\ge|\nu(A)-\mu_n(A)|=1-m.
$$
该事件界直接来自差函数总和为零，其正部、负部之和各等于总变差。令 $\nu$ 在 $A$ 上均匀，则 $m<1$ 给 $1/D>\alpha^n$，从而 $A$ 内外的绝对差之和分别为
$$
\sum_{u\in A}\left(\frac1D-\alpha^n\right)=1-m,
\qquad
\sum_{u\notin A}\mu_n(u)=1-m.
$$
半和恰为 $1-m$，这既证明经典最优值，也说明 $\tau$ 的对角分布达到它。

量子严格性则来自 $H$ 的非对角作用。无论 $b$ 是否为零，末位一类的均匀向量 $v$ 都已定义且与 $a$ 正交，并满足
$$
\langle v|H|a\rangle=\alpha^{n+1}\sqrt{DC}>0.
$$
因此 $a$ 不是 $H$ 的特征向量。Rayleigh 商达到最小特征值当且仅当向量属于相应特征空间，故
$$
-e_{K,n}=\lambda_{\min}(H)
<\langle a|H|a\rangle=m-1,
$$
即 $e_{K,n}>1-m$。张量积公式直接由 $A$ 的定义得到，证明固定的 $|\Psi_K\rangle$ 接全零尾部同时给出每个 $n>K$ 的最优者。证毕。

这里的差距比较完整 POVM 所能取得的态区分总变差与只读计算基的总变差。它依赖所列相干目标及固定尾零支撑，不是对所有目标或每种受限测量的结论，也不是过程的 diamond 范数界。它不表示最优值依赖计算基的相位角：任意计算基对角酉算子 $U$ 都与 $P$ 对易，共轭使 $\mathcal F_{K,n}$ 双射到自身，迹范数的酉不变性便给
$$
\min_{\sigma\in\mathcal F_{K,n}}d_{\rm tr}(U\rho_nU^*,\sigma)=e_{K,n}.
$$
固定支撑也不能换成仅有维数的预算；若 $K\ge1$，则 $D\ge2$，而上面的正二维行列式给 $\operatorname{rank}\rho_n=2$，允许任选 $D$ 维子空间就能令其包含 $\operatorname{ran}\rho_n$，以 $\sigma=\rho_n$ 达到零误差。

本节的 Q109、Q125.1、Q125.3 取仓库提交 `7af72f9910546ca2aa0bfa3a6bbaed4d8a393efb`；Q126.2 的固定尾零载体及经典窗口比较取提交 `dc4af5d3b06e66c8be5fe63ffd5fc1ace63e2c7e`，这里已从显式对角律独立证明所需经典最优值。迹距离的数据处理是既有标准结论，前一提交的 `D5/S3/Quantum/Foundation/FiniteTraceDistance.lean` 中 `traceDistance_contract` 对应所用收缩性，其范围不包含本节完整最优化。命题 127.1 为 `repo-derived` 普通数学推导，不提出外部新颖性或完整 Lean 认证主张。

<a id="entry-604"></a>

## 追加锚（本行以下为增补区）

<a id="section-128"></a>

## 128. 尾零量子最优者的唯一性与短窗口保真的代价

固定整数 $n>K\ge0$，取 $\alpha=(\sqrt5-1)/2$、$F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$。窗口从第 $0$ 位向右延伸，记
$$
W_j=\{w\in\{0,1\}^j:w_iw_{i+1}=0\ \text{对所有 }0\le i<j-1\},
\qquad W_0=\{\varnothing\},
\qquad D_K=|W_K|=F_{K+2}.
$$
完整载体与其中的合法词子空间分别为
$$
\mathcal K_j=(\mathbb C^2)^{\otimes j},
\qquad
\mathcal L_j=\operatorname{span}\{|w\rangle:w\in W_j\}\subseteq\mathcal K_j,
\qquad \mathcal K_0=\mathcal L_0=\mathbb C.
$$
目标是 Q125.1、Q127.1 所指定的相干态族：$\rho_0=(1)$，而对 $j\ge1$，
$$
s_j=\sum_{w\in W_j}|w\rangle,
\qquad
t_j=\sum_{\substack{w\in W_j\\w_{j-1}=0}}|w\rangle,
\qquad
\rho_j=\alpha^{j+1}|s_j\rangle\langle s_j|
       +\alpha^{j+2}|t_j\rangle\langle t_j|.
$$
这里 $s_j,t_j$ 未归一化，$\rho_j$ 是完整 $\mathcal K_j$ 上的密度算子，非法词方向上的行、列为零。补零等距映射及可行域为
$$
V=V_{K,n}:\mathcal L_K\longrightarrow\mathcal K_n,
\qquad V|w\rangle=|w0^{n-K}\rangle,
\qquad P=VV^*,
$$
$$
\mathcal F_{K,n}
=\{\sigma\text{ 为 }\mathcal K_n\text{ 上的密度算子}:\sigma=P\sigma P\}.
$$
因此固定的是 $\{w0^{n-K}:w\in W_K\}$ 的具体尾零支撑，允许该支撑内的混合及任意相干。置
$$
|\Psi_K\rangle=D_K^{-1/2}\sum_{w\in W_K}|w\rangle,
\qquad |a\rangle=V|\Psi_K\rangle,
\qquad \tau=\tau_{K,n}=|a\rangle\langle a|,
\qquad Q=P-\tau.
$$
采用半迹范数 $d_{\rm tr}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$。Q127.1 的普通证明给出
$$
e=e_{K,n}=d_{\rm tr}(\rho_n,\tau)
=\min_{\sigma\in\mathcal F_{K,n}}d_{\rm tr}(\rho_n,\sigma)
>1-D_K\alpha^n>0,
$$
并给出 $H=\rho_n-\tau$ 的负谱子空间恰为一维。取其中单位向量 $\zeta$，使 $H\zeta=-e\zeta$，定义
$$
r=r_{K,n}=\|P\zeta\|^2.
$$
谱投影 $|\zeta\rangle\langle\zeta|$ 及 $r$ 均与 $\zeta$ 的相位选择无关。对 $K\ge1$ 再记
$$
B_K=F_{K+1},\qquad C_K=F_K,\qquad D_K=B_K+C_K,
\qquad \kappa_K=\alpha^{K+2}\frac{B_KC_K}{D_K},
$$
并单独定义 $\kappa_0=0$；空词不使用末位分类。

**命题 128.1（投影余量、唯一最优者与短窗口保真冲突）。** 对所有上述整数 $n>K\ge0$，有 $0<r_{K,n}<1$。每个 $\sigma\in\mathcal F_{K,n}$ 若记 $p=\langle a|\sigma|a\rangle$，则
$$
d_{\rm tr}(\rho_n,\sigma)
\ge e_{K,n}+(1-r_{K,n})(1-p).
$$
因而 $\tau_{K,n}$ 是该可行域内唯一的迹距离最优者。

每个可行态唯一写成 $\sigma=V\theta V^*$，其中 $\theta$ 是 $\mathcal L_K$ 上的密度算子；把 $\theta$ 在非法词方向延零，视为完整 $\mathcal K_K$ 上的算子，则其完整张量积偏迹为
$$
\operatorname{Tr}_{\{K,\ldots,n-1\}}\sigma=\theta.
$$
所以精确保留前 $K$ 位目标 $\rho_K$ 的唯一可行延拓是
$$
\sigma^{\rm cut}_{K,n}=V\rho_KV^*
=\rho_K\otimes|0^{n-K}\rangle\langle0^{n-K}|.
$$
乘积 $V\rho_KV^*$ 中的 $\rho_K$ 取其在 $\mathcal L_K$ 上的限制，右端及偏迹仍在完整 qubit 空间中解释。此延拓也精确保留所有 $0\le j\le K$ 的目标前缀 $\rho_j$。令
$$
p_K=\langle\Psi_K|\rho_K|\Psi_K\rangle.
$$
对 $K\ge1$，有
$$
p_K=\alpha^{K+1}D_K+\alpha^{K+2}\frac{B_K^2}{D_K},
\qquad 1-p_K=\kappa_K>0,
$$
以及严格的长窗口额外误差
$$
g_{K,n}:=d_{\rm tr}(\rho_n,\sigma^{\rm cut}_{K,n})-e_{K,n}
\ge(1-r_{K,n})\kappa_K>0.
$$
对 $K=0$，$p_0=1$，唯一可行态就是 $\tau_{0,n}=\sigma^{\rm cut}_{0,n}$，没有这种冲突。

更一般地，任取非负容差 $\varepsilon_{\rm short},\varepsilon_{\rm large}$。若某个可行态及其短窗口 $\theta$ 同时满足
$$
d_{\rm tr}(\theta,\rho_K)\le\varepsilon_{\rm short},
\qquad
d_{\rm tr}(\rho_n,\sigma)\le e_{K,n}+\varepsilon_{\rm large},
$$
则必有
$$
\varepsilon_{\rm large}
\ge(1-r_{K,n})\max\{\kappa_K-\varepsilon_{\rm short},0\}.
$$
这只是必要条件，一般并不充分，也不是可达误差对的精确 Pareto 边界。

对每个固定的 $K\ge1$，各有限 $n>K$ 的冲突严格为正，但实际差距满足
$$
0<g_{K,n}\le1-e_{K,n}<D_K\alpha^n\longrightarrow0
\qquad(n\to\infty).
$$
因而不存在对所有 $n>K$ 统一成立的正差距下界。投影余量的系数也退化：
$$
e_{K,n}\le r_{K,n}<1,
\qquad
0<1-r_{K,n}\le1-e_{K,n}<D_K\alpha^n\longrightarrow0.
$$

证明。先构造实际用于余量界的测量。由于支撑中的每个词均以零结尾，
$$
Ps_n=Pt_n=\sqrt{D_K}\,|a\rangle.
$$
$Q=P-\tau$ 是正交投影，且 $Qs_n=Qt_n=0$，故 $Q\rho_n=\rho_nQ=0$ 及 $QH=HQ=0$。由
$$
0=QH\zeta=-eQ\zeta
$$
和 $e>0$ 得 $Q\zeta=0$。于是
$$
P\zeta=\tau\zeta=\langle a|\zeta\rangle a,
\qquad r=|\langle a|\zeta\rangle|^2.
$$
若 $r=0$，则
$$
-e=\langle\zeta|H|\zeta\rangle
=\langle\zeta|\rho_n|\zeta\rangle\ge0,
$$
矛盾。若 $r=1$，则单位向量 $\zeta$ 属于 $\operatorname{ran}P$，结合 $Q\zeta=0$ 可知它与 $a$ 平行，故 $a$ 必为 $H$ 的特征向量。然而 Q127.1 中始终非空的末位一词组给单位向量
$$
|v\rangle=F_n^{-1/2}\sum_{\substack{u\in W_n\\u_{n-1}=1}}|u\rangle,
\qquad v\perp\operatorname{ran}P,
$$
并且由显式目标直接有
$$
\langle v|H|a\rangle
=\alpha^{n+1}\sqrt{D_KF_n}>0.
$$
这与 $a$ 为特征向量矛盾，故 $0<r<1$。这里 $F_n>0$ 对每个 $n>K\ge0$ 成立，$n=K+1$ 也无需引入任何空词组的归一化向量。

由 $Q\zeta=0$，两个正交投影 $|\zeta\rangle\langle\zeta|$ 与 $Q$ 的乘积在两个方向上均为零，因此
$$
E=|\zeta\rangle\langle\zeta|+Q,
\qquad E^*=E,\qquad E^2=E,\qquad 0\le E\le I.
$$
它与 $I-E$ 构成二元投影测量。对任意可行 $\sigma$，支撑条件和 $P\zeta=\langle a|\zeta\rangle a$ 给
$$
\operatorname{Tr}(E\sigma)
=\langle\zeta|\sigma|\zeta\rangle+\operatorname{Tr}(Q\sigma)
=rp+1-p.
$$
另一方面，$Q\rho_n=0$ 及 $H\zeta=-e\zeta$ 给
$$
\operatorname{Tr}(E\rho_n)
=\langle\zeta|\rho_n|\zeta\rangle
=\langle\zeta|(H+\tau)|\zeta\rangle=r-e.
$$
在本次应用中，将迹零 Hermitian 算子 $Y=\sigma-\rho_n$ 写成正负谱部分 $Y_+-Y_-$；两部分的迹都是 $\|Y\|_1/2$，且 $0\le\operatorname{Tr}(EY_\pm)\le\operatorname{Tr}Y_\pm$，所以
$$
|\operatorname{Tr}(EY)|\le\tfrac12\|Y\|_1=d_{\rm tr}(\rho_n,\sigma).
$$
两个期望相减恰为 $e+(1-r)(1-p)>0$，这便证明投影余量界。

Q127.1 已给 $\tau$ 达到最小值 $e$。若 $\sigma$ 也达到该值，$1-r>0$ 与 $0\le p\le1$ 迫使 $p=1$。此时
$$
\operatorname{Tr}\bigl((I-\tau)\sigma(I-\tau)\bigr)=1-p=0.
$$
括号中的算子为正，迹零使它为零，消去了 $a^\perp$ 内的全部方向。对任意 $x\perp a$，正算子的 Cauchy–Schwarz 不等式又给
$$
|\langle x|\sigma|a\rangle|^2
\le\langle x|\sigma|x\rangle\langle a|\sigma|a\rangle=0,
$$
其共轭交叉项也为零。因此 $\sigma=p\tau=\tau$，唯一性成立；这里并未使用迹范数的严格凸性。

下面核对短窗口及其唯一延拓。$V^*V=I_{\mathcal L_K}$，故可行态给出密度算子 $\theta=V^*\sigma V$，且 $V\theta V^*=P\sigma P=\sigma$；反向乘以 $V^*,V$ 也证明 $\theta$ 唯一。按合法词基展开，
$$
V\theta V^*
=\sum_{w,u\in W_K}\theta_{wu}
  |w\rangle\langle u|\otimes|0^{n-K}\rangle\langle0^{n-K}|.
$$
尾部秩一投影的迹为一，故在完整张量积上取尾部偏迹正好得到延零后的 $\theta$，并非在较小的合法空间上另定义偏迹。特别地，短窗口等于 $\rho_K$ 当且仅当 $\theta=\rho_K$，得到所列唯一的 $\sigma^{\rm cut}_{K,n}$。Q125.1 的完整偏迹相容性逐层迭代，使该态的前 $j$ 位等于 $\rho_j$，$1\le j\le K$；空窗口为标量迹一，即 $\rho_0$。

对 $K\ge1$，末位零、末位一的词数分别为 $B_K,C_K$，两者均正。由未归一化向量的定义，
$$
\langle\Psi_K|s_K\rangle=\sqrt{D_K},
\qquad
\langle\Psi_K|t_K\rangle=\frac{B_K}{\sqrt{D_K}},
$$
从而得到陈述中的 $p_K$。归一化在同一记号下为
$$
1=\operatorname{Tr}\rho_K
=\alpha^{K+1}D_K+\alpha^{K+2}B_K.
$$
两式相减，利用 $D_K-B_K=C_K$，即得
$$
1-p_K
=\alpha^{K+2}\left(B_K-\frac{B_K^2}{D_K}\right)
=\alpha^{K+2}\frac{B_KC_K}{D_K}=\kappa_K>0.
$$
$\sigma^{\rm cut}_{K,n}$ 的 $p$ 正是 $p_K$，代入余量界给严格额外误差。$K=0$ 时 $\mathcal L_0$ 一维，唯一密度为 $\rho_0=(1)$，$\Psi_0$ 是单位空张量；因此 $p_0=1$、$\kappa_0=0$ 及全部无冲突结论直接成立。

对容差结论，$\sigma=V\theta V^*$ 给 $p=\langle\Psi_K|\theta|\Psi_K\rangle$。对完整 $\mathcal K_K$ 上的迹零算子 $\theta-\rho_K$ 应用刚才的正负部分论证，并取投影 $|\Psi_K\rangle\langle\Psi_K|$，得到
$$
|p-p_K|\le d_{\rm tr}(\theta,\rho_K)\le\varepsilon_{\rm short}.
$$
由于 $p\le1$，这蕴含
$$
1-p\ge\max\{\kappa_K-\varepsilon_{\rm short},0\}.
$$
与长窗口余量界和假设的长窗口上界合并，便是所列必要条件，$K=0$ 时右端为零。

为验证它一般不充分，取 $K=1$、任意 $n>1$，以及 $\varepsilon_{\rm large}=0$、$\varepsilon_{\rm short}=\kappa_1$。这对预算满足所列必要不等式。若有可行态满足两项预算，长窗口预算及唯一性却迫使它为 $\tau_{1,n}$，短窗口只能是 $|\Psi_1\rangle\langle\Psi_1|$。此时 $\kappa_1=\alpha^3/2=\alpha-1/2>0$，由 Q125.1 的一位矩阵得到
$$
|\Psi_1\rangle\langle\Psi_1|-\rho_1
=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}
 -\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}
=\kappa_1\begin{pmatrix}-1&1\\1&1\end{pmatrix}.
$$
这个迹零矩阵的特征值为 $\pm\sqrt2\,\kappa_1$，故短窗口迹距离是 $\sqrt2\,\kappa_1>\varepsilon_{\rm short}$，矛盾。这给出了必要条件与可达性的严格区别。

最后，任意两个密度算子的迹距离至多为一，所以对 $K\ge1$，已证的严格性与 Q127.1 的 $e_{K,n}>1-D_K\alpha^n$ 共同给
$$
0<g_{K,n}\le1-e_{K,n}<D_K\alpha^n.
$$
固定 $K$ 时右端趋零，夹逼的是实际差距本身。又因 $E$ 与 $\rho_n$ 均为正算子，
$$
0\le\operatorname{Tr}(E\rho_n)=r_{K,n}-e_{K,n},
$$
故 $r_{K,n}\ge e_{K,n}$，同时 $r_{K,n}<1$，得到所列系数退化界。证毕。

本命题刻画指定相干目标与准确尾零支撑下的静态窗口相容性。Q126.2 中经典截断概率与均匀概率均优化每个固定深窗口的总变差；这里的唯一量子最优者则在 $K\ge1$ 时不能同时精确保留 $\rho_K$。投影 $E$ 是完整 $n$ 窗口上允许任意联合测量时的数学效应，未附加局域性、实施成本或可访问性条件。所证范围不包含时间演化、动态预测、任意维数预算、一般目标态或形而上必然性。

本节的 Q125.1、Q126.2、Q127.1 均取[仓库不可变提交 `ac40238901406b5bba4518e306d5bb2da9fe8ba1` 的量子卷](https://github.com/the-omega-institute/trureturing/blob/ac40238901406b5bba4518e306d5bb2da9fe8ba1/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)，依其显式普通证明使用。测量期望受迹距离控制属于 Helstrom 变分框架；Q127.1 所引同仓 `D5/S3/Quantum/Foundation/FiniteTraceDistance.lean` 提供既有有限迹距离数据处理，其覆盖范围不是本节的完整唯一性与保真冲突。命题 128.1 是 `repo-derived` 普通数学推导，不主张外部新颖性或 Lean 认证。

<a id="entry-606"></a>

## 追加锚（本行以下为增补区）

<a id="section-129"></a>

## 129. 移动边界下的非消失尾零代价

取 $\alpha=(\sqrt5-1)/2$、$F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$，在完整 qubit 载体中记
$$
\mathcal K_j=(\mathbb C^2)^{\otimes j},
\qquad
W_j=\{w\in\{0,1\}^j:w_iw_{i+1}=0\ \text{对所有 }0\le i<j-1\},
\qquad W_0=\{\varnothing\},
$$
$$
\mathcal L_j=\operatorname{span}\{|w\rangle:w\in W_j\}\subseteq\mathcal K_j,
\qquad \mathcal K_0=\mathcal L_0=\mathbb C.
$$
目标取命题 125.1 的指定密度算子 $\rho_0=(1)$ 及
$$
\rho_j=\alpha^{j+1}|s_j\rangle\langle s_j|
       +\alpha^{j+2}|t_j\rangle\langle t_j|\quad(j\ge1),
\qquad
|s_j\rangle=\sum_{w\in W_j}|w\rangle,
\qquad
|t_j\rangle=\sum_{\substack{w\in W_j\\w_{j-1}=0}}|w\rangle.
$$
对每个整数 $K\ge0$ 取 $n=K+1$，置
$$
C=F_{K+1},\qquad D=F_{K+2},\qquad s=\alpha^{K+2},
$$
$$
A=\{w0:w\in W_K\},
\qquad P=\sum_{u\in A}|u\rangle\langle u|,
\qquad
\mathcal F_{K,K+1}=\{\sigma\ge0:\operatorname{Tr}\sigma=1,\ \sigma=P\sigma P\},
$$
其中 $\sigma$ 作用于完整 $\mathcal K_{K+1}$。定义精确尾零等距映射与向量
$$
V:\mathcal L_K\longrightarrow\mathcal K_{K+1},
\qquad V|w\rangle=|w0\rangle,
\qquad
|\Psi_K\rangle=D^{-1/2}\sum_{w\in W_K}|w\rangle,
$$
$$
|a\rangle=V|\Psi_K\rangle,
\qquad \tau=|a\rangle\langle a|,
\qquad
|v\rangle=C^{-1/2}\sum_{\substack{u\in W_{K+1}\\u_K=1}}|u\rangle,
\qquad \mathcal M=\operatorname{span}\{a,v\}.
$$
采用半迹范数约定，并以命题 127.1 的可行域定义最优误差：
$$
d_{\rm tr}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1,
\qquad \|X\|_1=\operatorname{Tr}\sqrt{X^*X},
\qquad
e_{K,K+1}=\min_{\sigma\in\mathcal F_{K,K+1}}d_{\rm tr}(\rho_{K+1},\sigma).
$$
记 $H=\rho_{K+1}-\tau$，令 $\Pi_-$ 为 $H$ 在完整载体上的负谱投影，定义
$$
r_{K,K+1}=\langle a|\Pi_-|a\rangle,
\qquad
\sigma^{\rm cut}_{K,K+1}=V(\rho_K|_{\mathcal L_K})V^*,
\qquad
g_K=d_{\rm tr}(\rho_{K+1},\sigma^{\rm cut}_{K,K+1})-e_{K,K+1}.
$$
这里乘积中的 $\rho_K$ 识别为它在合法支撑 $\mathcal L_K$ 上的限制；$\rho_K$ 本身仍指完整 $\mathcal K_K$ 上、在非法词方向延零的算子。对 $K\ge1$ 沿用命题 128.1 的记号
$$
\kappa_K=\alpha^{K+2}\frac{F_{K+1}F_K}{F_{K+2}}.
$$

**命题 129.1（移动边界的非消失尾零代价）。** 对上述指定目标与具体尾零支撑，对所有整数 $K\ge0$，在完整载体上有
$$
\sigma^{\rm cut}_{K,K+1}=\rho_K\otimes|0\rangle\langle0|,
\qquad
e_{K,K+1}=d_{\rm tr}(\rho_{K+1},\tau)=s\sqrt{C(C+D)}>0.
$$
$H$ 在正交标准基 $(a,v)$ 上的矩阵及其平方为
$$
H_2=s\begin{pmatrix}-C&\sqrt{CD}\\\sqrt{CD}&C\end{pmatrix},
\qquad H_2^2=e_{K,K+1}^2I_2.
$$
$H$ 在 $\mathcal M^\perp$ 上为零，其完整负谱投影为二维负谱投影的延零：
$$
\Pi_{-,2}=\frac{I_2-H_2/e_{K,K+1}}2,
\qquad \Pi_-=\Pi_{-,2}\oplus0_{\mathcal M^\perp}.
$$
当 $K\ge1$ 时，$\dim\ker H=2^{K+1}-2>0$，而 $(I_{\rm full}-H/e_{K,K+1})/2$ 在此核上作用为单位算子的一半，故不是负谱投影。当 $K=0$ 时，$\mathcal K_1=\mathcal M$，该完整单位算子表达式成立。对所有 $K\ge0$，重叠量为
$$
r_{K,K+1}=\frac{1+\sqrt{F_{K+1}/F_{K+3}}}{2}.
$$
取 $\kappa_0=0$，则 $g_0=0$；对 $K\ge1$ 有
$$
g_K\ge(1-r_{K,K+1})\kappa_K>0.
$$
沿 $n=K+1$ 令 $K\to\infty$，有三个极限
$$
e_{K,K+1}\longrightarrow\frac1{\sqrt5},
\qquad
1-r_{K,K+1}\longrightarrow\frac{1-\alpha}{2}=\frac{\alpha^2}{2},
\qquad
\kappa_K\longrightarrow\frac{\alpha^3}{\sqrt5},
$$
以及
$$
\liminf_{K\to\infty}g_K\ge L:=\frac{\alpha^5}{2\sqrt5}>0.
$$
另一方面，固定任意整数 $K\ge1$，令 $n>K$ 增大，并沿用命题 127.1、128.1 在具体支撑 $A_{K,n}=\{w0^{n-K}:w\in W_K\}$ 上的最优误差 $e_{K,n}$，记
$$
D_K=F_{K+2},
\qquad
\sigma^{\rm cut}_{K,n}=\rho_K\otimes|0^{n-K}\rangle\langle0^{n-K}|,
\qquad
g_{K,n}=d_{\rm tr}(\rho_n,\sigma^{\rm cut}_{K,n})-e_{K,n}.
$$
则
$$
0<g_{K,n}\le1-e_{K,n}<D_K\alpha^n,
\qquad
g_{K,n}\longrightarrow0,
\qquad
e_{K,n}\longrightarrow1,
\qquad
d_{\rm tr}(\rho_n,\sigma^{\rm cut}_{K,n})\longrightarrow1.
$$

证明。按合法词基展开 $\rho_K|_{\mathcal L_K}$，每个矩阵单位 $|w\rangle\langle u|$ 经 $V$ 变为 $|w0\rangle\langle u0|$，即 $|w\rangle\langle u|\otimes|0\rangle\langle0|$。在非法词方向延零，得到陈述中的完整载体等式。

命题 127.1 的计数给 $|A|=D$、末位一合法词数为 $C$，且 $C,D>0$。当 $n=K+1$ 时，$A$ 恰为全部末位零合法词，故 $(a,v)$ 正交归一，且
$$
|s_{K+1}\rangle=\sqrt D\,|a\rangle+\sqrt C\,|v\rangle,
\qquad |t_{K+1}\rangle=\sqrt D\,|a\rangle.
$$
因此 $H$ 在 $\mathcal M^\perp$ 上为零。将这两式代入目标公式，并用命题 127.1 的归一化恒等式 $\alpha^{K+1}(D+\alpha C)=1$，即得所列 $H_2$。直接相乘，
$$
H_2^2=s^2
\begin{pmatrix}C^2+CD&0\\0&CD+C^2\end{pmatrix}
=s^2C(C+D)I_2.
$$
$H_2$ 的迹为零，其特征值为 $\pm s\sqrt{C(C+D)}$。命题 127.1 给 $\tau$ 达到可行域上的最小值，半迹范数遂给 $e_{K,K+1}=s\sqrt{C(C+D)}>0$。两特征值非零，故 $\ker H=\mathcal M^\perp$。有限维谱分解给 $\Pi_{-,2}=(I_2-H_2/e_{K,K+1})/2$，在正交补上延零才是完整负谱投影。$K\ge1$ 时正交补维数 $2^{K+1}-2>0$，完整单位算子表达式在该补空间上为一半；$K=0$ 时完整空间只有两维、正交补为零，因而该表达式有效。

负谱为一维，取其单位向量 $\zeta$。由于 $Pa=a$、$Pv=0$ 且 $\zeta\in\mathcal M$，这里的 $r_{K,K+1}$ 与命题 128.1 的 $\|P\zeta\|^2=|\langle a|\zeta\rangle|^2$ 相同。二维投影的第一个对角元为
$$
r_{K,K+1}=\langle a|\Pi_-|a\rangle
=\frac12\left(1+\frac{sC}{e_{K,K+1}}\right)
=\frac12\left(1+\sqrt{\frac{C}{C+D}}\right).
$$
用 $C+D=F_{K+3}$ 即得对所有 $K\ge0$ 的重叠公式，且 $0<r_{K,K+1}<1$。

令 $h_j=\alpha^jF_j$。命题 125.1 所用 Binet 公式在本参数下给精确残差
$$
h_j=\frac{1-(-\alpha^2)^j}{\sqrt5},
\qquad h_j\longrightarrow\frac1{\sqrt5},
$$
因为 $0<\alpha<1$。边界误差、重叠比值和 $\kappa_K$ 满足三个缩放恒等式：
$$
e_{K,K+1}^2=\alpha^{2K+4}F_{K+1}F_{K+3}=h_{K+1}h_{K+3},
$$
$$
\frac{F_{K+1}}{F_{K+3}}=\alpha^2\frac{h_{K+1}}{h_{K+3}},
$$
$$
\kappa_K=\alpha^{K+2}\frac{F_{K+1}F_K}{F_{K+2}}
=\alpha^3\frac{h_{K+1}h_K}{h_{K+2}}.
$$
最后一式的指数抵消为 $K+2-(K+1)-K+(K+2)=3$；它在 $K=0$ 时也因 $F_0=h_0=0$ 与定义 $\kappa_0=0$ 一致。各分母的极限严格为正，取正平方根、商及乘积的极限，结合 $1-\alpha=\alpha^2$，得到陈述中的三个极限。

命题 128.1 对此 cut 态给 $1-\langle a|\sigma^{\rm cut}_{K,K+1}|a\rangle=\kappa_K$，并由其投影余量界得到
$$
g_K\ge(1-r_{K,K+1})\kappa_K>0\qquad(K\ge1).
$$
因此
$$
\liminf_{K\to\infty}g_K
\ge\lim_{K\to\infty}(1-r_{K,K+1})\kappa_K
=\frac{\alpha^2}{2}\frac{\alpha^3}{\sqrt5}
=\frac{\alpha^5}{2\sqrt5}>0.
$$
$K=0$ 时，$\rho_0=(1)$ 且 $\sigma^{\rm cut}_{0,1}=\tau=|0\rangle\langle0|$，故 $g_0=0$；改变这一有限项不影响下极限。

最后，对每个固定 $K\ge1$，命题 128.1 的实际上界是 $0<g_{K,n}\le1-e_{K,n}<D_K\alpha^n$。右端随 $n\to\infty$ 趋零，故 $g_{K,n}\to0$；再用 $e_{K,n}\le1$ 得 $e_{K,n}\to1$，从而 $d_{\rm tr}(\rho_n,\sigma^{\rm cut}_{K,n})=e_{K,n}+g_{K,n}\to1$。这是固定 $K$ 的窗口序列；沿 $n=K+1$ 的窗口序列则有 $e_{K,K+1}\to1/\sqrt5<1$ 及上述正的下极限界。证毕。

<a id="entry-608"></a>

## 追加锚（本行以下为增补区）
<a id="section-130"></a>

## 130. 固定二维活动记忆的相干前缀生成与容量下界

**命题 130.1（同一等距的逐位生成与受限最小容量）。** 取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad 0<\alpha<1,\qquad \alpha+\alpha^2=1,
$$
并令 $B=M=\mathbb C^2$，两者均以 $|0\rangle,|1\rangle$ 为正交标准基。输出空间为完整张量积 $H_n=B^{\otimes n}$，$H_0=\mathbb C$。记 $W_n\subseteq\{0,1\}^n$ 为不含相邻 $11$ 的词集，$W_0=\{\varnothing\}$；对 $n\ge1$，令 $\ell(w)=w_{n-1}$ 为末位，并置
$$
s_n=\sum_{w\in W_n}|w\rangle,\qquad
t_n=\sum_{\substack{w\in W_n\\\ell(w)=0}}|w\rangle,
$$
$$
\rho_n=\alpha^{n+1}|s_n\rangle\langle s_n|
       +\alpha^{n+2}|t_n\rangle\langle t_n|,\qquad \rho_0=(1).
$$
这里的 $\rho_n$ 是命题 125.1 的固定左边界相干局部态，作为 $H_n$ 上的算子取值。

在活动记忆中定义
$$
m_1=|0\rangle,\qquad m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,
$$
并以基像定义线性映射 $T:M\to B\otimes M$：
$$
T|0\rangle=|0\rangle\otimes m_0,\qquad
T|1\rangle=|1\rangle\otimes m_1.
$$
它是等距。令 $\Xi_0=m_0$，始终按输出在前、记忆在后的次序递推
$$
\Xi_{n+1}=(I_{H_n}\otimes T)\Xi_n\in H_{n+1}\otimes M
\qquad(n\ge0).
$$
则所有 $\Xi_n$ 均为单位向量，且对每个 $n\ge1$，
$$
\Xi_n=\sum_{w\in W_n}\alpha^{(n+\ell(w))/2}|w\rangle\otimes m_{\ell(w)}
=\alpha^{(n+1)/2}s_n\otimes|0\rangle
 +\alpha^{(n+2)/2}t_n\otimes|1\rangle.
$$
因而在完整输出空间上，对所有 $n\ge0$ 有
$$
\operatorname{Tr}_M|\Xi_n\rangle\langle\Xi_n|=\rho_n.
$$
非法词对应的行、列均为零，等式包含全部非对角相干项。后续只作用于记忆与新输出的等距保持已发出前缀的约化态，所以同一递推同时给出全部有限前缀。

这个 $T$ 可由同一个二比特幺正实现。令
$$
R=\begin{pmatrix}\sqrt\alpha&-\alpha\\\alpha&\sqrt\alpha\end{pmatrix},\qquad
C_0(R)=|0\rangle\langle0|\otimes R+|1\rangle\langle1|\otimes I_M,
\qquad W=C_0(R)\operatorname{SWAP}
$$
作用于 $B_{\rm new}\otimes M$，其中 $\operatorname{SWAP}(|b\rangle\otimes|c\rangle)=|c\rangle\otimes|b\rangle$，乘积中先作用 $\operatorname{SWAP}$。每次新输出取与已有系统独立的纯空白 $|0\rangle$，初始记忆为 $R|0\rangle=m_0$，则
$$
W(|0\rangle\otimes\psi)=T\psi\qquad(\psi\in M).
$$

最小活动记忆容量取 Hilbert 空间维数，且仅在如下类别中比较：记忆空间 $K$ 的维数固定为 $d$，初始记忆为纯态，每次引入独立纯空白；每步为顺序等距，已经发出的寄存器不再受作用；不存在未计入 $K$ 的环境、纯化参考、共享随机性或其它记忆。吸收纯空白的插入后，竞争映射可写作 $V_j:K\to B\otimes K$，允许随 $j$ 改变。若这种生成器精确实现全部 $\rho_n$，则 $d\ge2$；上述固定 $T$ 达到 $d=2$。该最小性只比较指定输出态族在此类别中的精确生成，等式所确定的是已发出前缀上的全部联合测量概率，不是任意记忆干预的过程等价或普适最小预测器。

证明。首先 $\|m_1\|^2=1$、$\|m_0\|^2=\alpha+\alpha^2=1$，而
$$
\langle m_1,m_0\rangle=\sqrt\alpha.
$$
$T$ 的两列具有单位范数，其内积为
$$
\langle |0\rangle\otimes m_0,|1\rangle\otimes m_1\rangle
=\langle0|1\rangle\langle m_0,m_1\rangle=0.
$$
因此 $T^*T=I_M$；这里使两列正交的是输出基，而非两个记忆标签。由线性性，
$$
Tm_0=\sqrt\alpha\,|0\rangle\otimes m_0+\alpha|1\rangle\otimes m_1,
\qquad Tm_1=|0\rangle\otimes m_0.
$$
初态为单位向量，各步等距，故 $\|\Xi_n\|=1$，包括 $n=0$。

对所列词展开从 $n=1$ 开始归纳，不为空词定义末位。$W_1=\{0,1\}$，$\Xi_1=Tm_0$ 的两个系数分别为 $\alpha^{1/2}$ 与 $\alpha$，正是公式。设公式对某个 $n\ge1$ 成立。若 $w\in W_n$ 末位为 $0$，它的项在下一步变为
$$
\alpha^{n/2}|w\rangle\otimes Tm_0
=\alpha^{(n+1)/2}|w0\rangle\otimes m_0
 +\alpha^{(n+2)/2}|w1\rangle\otimes m_1.
$$
这两个延长都合法，系数分别等于 $\alpha^{(n+1+\ell(w0))/2}$ 与 $\alpha^{(n+1+\ell(w1))/2}$。若 $w$ 末位为 $1$，只有附加 $0$ 合法，且
$$
\alpha^{(n+1)/2}|w\rangle\otimes Tm_1
=\alpha^{(n+1)/2}|w0\rangle\otimes m_0.
$$
其系数同样是所需的 $\alpha^{(n+1+\ell(w0))/2}$，而附加 $1$ 的振幅为零。每个长度 $n+1$ 的合法词具有唯一长度 $n$ 前缀，故这些项无遗漏、无重复，归纳成立。

将每项的记忆向量改写到正交计算基上。末位为 $0$ 的词给出的两个记忆列系数为
$$
\alpha^{n/2}\sqrt\alpha=\alpha^{(n+1)/2},\qquad
\alpha^{n/2}\alpha=\alpha^{(n+2)/2};
$$
末位为 $1$ 的词只给记忆 $|0\rangle$ 列，系数也为 $\alpha^{(n+1)/2}$。因此得到陈述中的 $s_n,t_n$ 两列展开。对这两个正交记忆列取偏迹，交叉项为零，立即给
$$
\operatorname{Tr}_M|\Xi_n\rangle\langle\Xi_n|
=\alpha^{n+1}|s_n\rangle\langle s_n|
 +\alpha^{n+2}|t_n\rangle\langle t_n|=\rho_n\qquad(n\ge1).
$$
具体地，对所有 $u,v\in\{0,1\}^n$，完整矩阵元为
$$
\langle u|\rho_n|v\rangle=
\begin{cases}
\alpha^n,&u,v\in W_n,\ \ell(u)=\ell(v)=0,\\
\alpha^{n+1},&u,v\in W_n,\ \text{至少一个末位为 }1,\\
0,&u\notin W_n\ \text{或 }v\notin W_n.
\end{cases}
$$
第一种情形使用 $\alpha^{n+1}+\alpha^{n+2}=\alpha^n$。这也直接核对了命题 125.1 的全部相干项。$n=0$ 时，对整个记忆取迹给 $\|m_0\|^2=1=\rho_0$，无需使用词展开。

为核对已经发出的边际，取任意 $A\in\mathcal L(H_n)$。由 $T^*T=I_M$，
$$
\langle\Xi_{n+1},(A\otimes I_B\otimes I_M)\Xi_{n+1}\rangle
=\langle\Xi_n,(A\otimes T^*T)\Xi_n\rangle
=\operatorname{Tr}(\rho_nA).
$$
这对所有 $A$ 成立，所以再发出一位后前 $n$ 位的密度仍是 $\rho_n$。迭代即得对每个 $0\le k\le n$，
$$
\operatorname{Tr}_{B^{\otimes(n-k)}\otimes M}
|\Xi_n\rangle\langle\Xi_n|=\rho_k.
$$
特别地，任意前缀上的联合 POVM $(E_a)_a$ 满足 $\Pr(a)=\operatorname{Tr}(\rho_kE_a)$。偏迹在此描述停止时的输出态；继续生成使用的是仍与旧输出相关联的同一记忆。

两个条件记忆标签不能被当作可完美读取的经典标志。事实上，若效应 $0\le E\le I_M$ 满足 $\langle m_0,Em_0\rangle=1$、$\langle m_1,Em_1\rangle=0$，正性给 $(I_M-E)^{1/2}m_0=0$ 及 $E^{1/2}m_1=0$，于是 $Em_0=m_0$、$Em_1=0$。自伴性将给
$$
\sqrt\alpha=\langle m_1,m_0\rangle
=\langle m_1,Em_0\rangle=\langle Em_1,m_0\rangle=0,
$$
矛盾。

现核对显式幺正。由 $\alpha+\alpha^2=1$，直接相乘得 $R^*R=RR^*=I_M$。两个控制投影正交且和为 $I_B$，故
$$
C_0(R)^*C_0(R)=C_0(R)C_0(R)^*=I_{B\otimes M}.
$$
$\operatorname{SWAP}$ 置换正交标准基且平方为恒等，亦为幺正，因此 $W$ 在整个四维空间上幺正。任取 $\psi=a|0\rangle+b|1\rangle$，先交换、再施加零控制的 $R$，得到
$$
\begin{aligned}
W(|0\rangle\otimes\psi)
&=C_0(R)(\psi\otimes|0\rangle)\\
&=a|0\rangle\otimes R|0\rangle+b|1\rangle\otimes|0\rangle\\
&=a|0\rangle\otimes m_0+b|1\rangle\otimes m_1=T\psi.
\end{aligned}
$$
这是整个输入记忆空间上的线性等式，与旧输出张量恒等后也成立，所以每次插入独立空白并作用同一 $W$ 就给上述递推。在固定纯空白上逐槽作用幺正，其有限链振幅由逐槽矩阵元收缩给出，单位初态的范数保持为一（[SequentialRegisterCircuit，circuit_initialized_coefficients 与 initialized_norm](../../../../D5/S3/Quantum/Entanglement/SequentialRegisterCircuit.lean)）；这里所需的特殊基像由刚才的直接计算确定。

最后证明限定类别中的下界。对任意竞争生成器，第一位输出后，输出与全部活动记忆的联合态为纯态 $\eta\in B\otimes K$，因为输入记忆与独立空白均纯，且第一步为等距。在 $K$ 的正交标准基 $e_1,\ldots,e_d$ 下写
$$
\eta=\sum_{j=1}^d x_j\otimes e_j,\qquad x_j\in B.
$$
其输出密度为 $\sum_{j=1}^d|x_j\rangle\langle x_j|$，像包含于 $\operatorname{span}\{x_1,\ldots,x_d\}$，所以若精确匹配第一位，必有 $\operatorname{rank}\rho_1\le d$。由目标公式，
$$
\rho_1=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix},\qquad
\det\rho_1=\alpha^3-\alpha^4=\alpha^3(1-\alpha)=\alpha^5>0.
$$
故 $\operatorname{rank}\rho_1=2$，从而 $d\ge2$。上面的构造使用纯初始记忆、独立纯空白及固定幺正，没有其它环境，并达到 $d=2$。下界只用第一步，对时间依赖的竞争等距同样成立。

固定活动容量与固定总档案是不同的资源条件：第 $n$ 步后保留的是 $n$ 个输出 qubit 加一个活动 qubit，联合空间为 $H_n\otimes M$，维数 $2^{n+1}$。输出寄存器随 $n$ 增加；有限个输出并未容纳一个无限词。若把这些有限前缀统一为命题 125.4 指定的 $\ell^2(X_{\rm fs})$ 上的单个正迹类密度，并沿用其柱投影 $C_u$，则全部柱读数须为 $\alpha^{|u|+\ell(u)}$（非空合法 $u$）。命题 125.4 排除了这样的密度；这里变化的输出空间并不提供该固定表示。

同一 $T$ 也不使边界态移位平稳。由已证对角元，第一位与第二位为 $1$ 的概率分别为
$$
\Pr(w_0=1)=\alpha^2,\qquad
\Pr(w_1=1)=\langle01|\rho_2|01\rangle+\langle11|\rho_2|11\rangle
=\alpha^3\ne\alpha^2.
$$
这与命题 125.3 的固定左边界律一致。若第一步后丢弃记忆并独立重置，第二步后两位输出为乘积态；若还要保持上述两个单点概率，便会给 $\Pr(11)=\alpha^5>0$，而目标值为零。因此停止时取偏迹不能替代生成途中保留记忆关联。当 $n\ge1$ 时，命题 125.3 的经典 Markov 抽样在计算基中给 $\sum_{w\in W_n}\alpha^{n+\ell(w)}|w\rangle\langle w|$，只匹配对角元；例如目标的 $\langle0|\rho_1|1\rangle=\alpha^2>0$。这一比较限于抽样所得的对角态，不排除另带相干制备的经典控制协议，也不把本命题的容量下界推广到其假设以外的模型。证毕。

<a id="entry-610"></a>

## 追加锚（本行以下为增补区）

<a id="section-131"></a>

## 131. 活动记忆的边界遗忘与平稳窗口的构型相干

**命题 131.1（精确记忆衰减、统一未来窗口界与保留首记录的正下界）。** 沿用命题 130.1 的固定等距，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad 0<\alpha<1,\qquad \alpha+\alpha^2=1,
\qquad B=M=\mathbb C^2,\qquad H_\ell=B^{\otimes\ell},\qquad H_0=\mathbb C.
$$
$B$ 与 $M$ 均取正交标准基 $|0\rangle,|1\rangle$。令
$$
m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,\qquad
m_1=|0\rangle,\qquad P_j=|m_j\rangle\langle m_j|\quad(j=0,1),
$$
$$
T:M\longrightarrow B\otimes M,\qquad T|j\rangle=|j\rangle\otimes m_j.
$$
每步对已发出输出张量恒等，始终按输出在前、活动记忆在后的次序定义
$$
T_0=I_M,\qquad T_{\ell+1}=(I_{H_\ell}\otimes T)T_\ell:
M\longrightarrow H_{\ell+1}\otimes M.
$$
对 $X\in\mathcal L(M)$ 定义记忆通道与输出通道
$$
\mathcal M(X)=\operatorname{Tr}_B(TXT^*),\qquad
\Gamma_\ell(X)=\operatorname{Tr}_M(T_\ell XT_\ell^*),\qquad
\Gamma_0(X)=\operatorname{Tr}X.
$$
原初记忆为纯态 $\sigma_0=P_0$，记
$$
\sigma_n=\mathcal M^n(P_0),\qquad
\Omega_n=T_nP_0T_n^*,\qquad
\rho_n=\Gamma_n(P_0)\quad(n\ge0).
$$
这里 $\rho_n$ 是命题 125.1 的完整相干密度，由命题 130.1 的等式识别；$\rho_0=1$。任意同一有限维空间上的两个密度采用半迹范数距离
$$
D(\theta,\vartheta)=\frac12\|\theta-\vartheta\|_1,
\qquad \|A\|_1=\operatorname{Tr}\sqrt{A^*A}.
$$
令
$$
\mathrm{den}=1+\alpha^2,\qquad
\pi_0=\frac1{\mathrm{den}},\qquad
\pi_1=\frac{\alpha^2}{\mathrm{den}},\qquad
\sigma_*=\pi_0P_0+\pi_1P_1.
$$
则记忆通道的显式形式、唯一不动密度及从指定初态出发的轨道满足
$$
\mathcal M(X)=X_{00}P_0+X_{11}P_1,\qquad
\mathcal M(\sigma_*)=\sigma_*,
$$
$$
\sigma_n=(1-p_n)P_0+p_nP_1,\qquad
p_0=0,\qquad p_{n+1}=\alpha^2(1-p_n),\qquad
p_n=\pi_1\bigl(1-(-\alpha^2)^n\bigr).
$$
带符号的系数偏差 $p_n-\pi_1=-\pi_1(-\alpha^2)^n$ 在偶数 $n$ 时严格为负，在奇数 $n$ 时严格为正；它是两个非正交密度的混合系数偏差，不是可完美读取的记忆标志概率。对所有整数 $n\ge0$，精确记忆距离为
$$
D(\sigma_n,\sigma_*)=
\frac{\alpha^3}{\mathrm{den}}\alpha^{2n}.
$$

对整数 $n\ge0,\ell\ge1$，在 $H_\ell$ 上定义无条件未来窗口和比较密度
$$
\beta_{n,\ell}=\operatorname{Tr}_{\text{前 }n\text{ 位}}\rho_{n+\ell},
\qquad \eta_\ell=\Gamma_\ell(\sigma_*),\qquad \eta_0=1.
$$
此前 $n$ 位输出及最终记忆均被忽略；允许的未来窗口效应在联合空间上形如 $I_{H_n}\otimes E\otimes I_M$，其中 $0\le E\le I_{H_\ell}$。此范围不含读取旧记录、按旧记录条件化、访问纯化参考、反馈或任意记忆干预。则
$$
\beta_{n,\ell}=\Gamma_\ell(\sigma_n),\qquad
D(\beta_{n,\ell},\eta_\ell)
\le\frac{\alpha^3}{\mathrm{den}}\alpha^{2n}
\quad(n\ge0,\ \ell\ge1),
$$
其中同一个上界适用于每个有限 $\ell$。对所有整数 $\ell\ge0$，比较族左右边缘均相容：
$$
\operatorname{Tr}_{\text{末位}}\eta_{\ell+1}=\eta_\ell,
\qquad
\operatorname{Tr}_{\text{首位}}\eta_{\ell+1}=\eta_\ell.
$$
特别地，对所有整数 $r,s,\ell\ge0$，将剩余输出依序识别为 $H_\ell$ 后，
$$
\operatorname{Tr}_{\text{前 }r\text{ 位与后 }s\text{ 位}}
\eta_{r+\ell+s}=\eta_\ell.
$$

在所指定的记忆基与输出构型基中，矩阵分别为
$$
\Gamma_1(X)=
\begin{pmatrix}X_{00}&\sqrt\alpha\,X_{01}\\
\sqrt\alpha\,X_{10}&X_{11}\end{pmatrix},
\qquad
\sigma_*=
\frac1{\mathrm{den}}
\begin{pmatrix}1&\alpha\sqrt\alpha\\
\alpha\sqrt\alpha&\alpha^2\end{pmatrix},
$$
$$
\eta_1=\frac1{\mathrm{den}}
\begin{pmatrix}1&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix},
\qquad
\langle0|\eta_1|1\rangle=\frac{\alpha^2}{\mathrm{den}}>0,
\qquad
\det\sigma_*=\frac{\alpha^4}{\mathrm{den}^2}>0.
$$
若以 $\Delta_B(Y)=\sum_{j=0}^1|j\rangle\langle j|Y|j\rangle\langle j|$ 表示该输出基中的完全去相干，则 $\Delta_B(\eta_1)\ne\eta_1$。此单位置结论只判定给定基中的去相干，不给出纠缠、情境性或 Bell 非局域性的判据。比较族的此项构造使用秩二的混合初始记忆 $\sigma_*$，不属于命题 130.1 比较最小容量时限定的纯初态类别；这里不对 $\eta_\ell$ 在该类别中的可达性或最小容量作断言。

最后，若比较保留首记录的完整窗口，则对每个整数 $\ell\ge1$ 有
$$
D(\rho_\ell,\eta_\ell)\ge
\frac{\sqrt2\,\alpha^4}{\mathrm{den}}>0.
$$
上述未来窗口上界与完整窗口下界均是在各自有限空间 $H_\ell$ 内的距离不等式，不是把增长中的窗口视为同一空间中的范数极限；$n$ 表示略去的输出位数，不是物理时间。

证明。命题 130.1 给 $T^*T=I_M$，故由递推 $T_\ell^*T_\ell=I_M$。各 $\Gamma_\ell$ 将密度映为密度，包括 $\ell=0$ 的标量密度。对矩阵单位直接展开，
$$
TXT^*=\sum_{i,j=0}^1X_{ij}|i\rangle\langle j|\otimes|m_i\rangle\langle m_j|.
$$
对输出基取偏迹，只保留 $i=j$ 项，得到
$$
\mathcal M(X)=X_{00}P_0+X_{11}P_1.
$$
密度 $X$ 的两个对角元非负且和为 $1$，故任何不动密度都必须落在 $P_0,P_1$ 的凸混合像中。这两密度不同，因而其混合系数唯一。设 $X=(1-p)P_0+pP_1$、$0\le p\le1$，则
$$
X_{11}=\alpha^2(1-p),\qquad
X_{00}=\alpha(1-p)+p=1-\alpha^2(1-p).
$$
因此 $\mathcal M(X)$ 的 $P_1$ 系数是 $\alpha^2(1-p)$。不动点方程为
$$
p=\alpha^2(1-p),\qquad
p=\frac{\alpha^2}{1+\alpha^2}=\pi_1,
$$
所以 $\sigma_*$ 存在且是不动密度中的唯一者。从 $p_0=0$ 归纳，递推保持 $p_n\in[0,1]$；减去不动点方程得
$$
p_{n+1}-\pi_1=-\alpha^2(p_n-\pi_1),\qquad
p_n-\pi_1=-\pi_1(-\alpha^2)^n.
$$
这证明轨道公式及奇偶符号。又 $\langle m_1,m_0\rangle=\sqrt\alpha\ne0$。若效应 $E$ 能以概率 $1$ 区分这两个纯态，则交换标签后可设 $Em_0=m_0$、$Em_1=0$：这些等式由 $E$ 与 $I_M-E$ 的正性推出。自伴性却会给
$$
\sqrt\alpha=\langle m_1,m_0\rangle
=\langle m_1,Em_0\rangle=\langle Em_1,m_0\rangle=0,
$$
矛盾，故混合分量不是可完美读取的标志。

为计算精确距离，在记忆基中有
$$
P_1-P_0=
\begin{pmatrix}\alpha^2&-\alpha\sqrt\alpha\\
-\alpha\sqrt\alpha&-\alpha^2\end{pmatrix},
\qquad \operatorname{Tr}(P_1-P_0)=0,
$$
$$
(P_1-P_0)^2=(\alpha^4+\alpha^3)I_M=\alpha^2I_M.
$$
末式使用 $\alpha+\alpha^2=1$。此自伴矩阵的两个特征值为 $\alpha,-\alpha$，故 $D(P_0,P_1)=\alpha$。于是对 $n\ge0$，
$$
\sigma_n-\sigma_*=(p_n-\pi_1)(P_1-P_0),\qquad
D(\sigma_n,\sigma_*)=|p_n-\pi_1|\alpha
=\frac{\alpha^3}{\mathrm{den}}\alpha^{2n}.
$$
特别地，$n=0$ 给 $D(P_0,\sigma_*)=\pi_1\alpha=\alpha^3/\mathrm{den}$。

现从实际联合态求未来窗口。递推并保留张量次序，归纳得到
$$
T_{n+\ell}=(I_{H_n}\otimes T_\ell)T_n
\qquad(n,\ell\ge0).
$$
对任意 $A\in\mathcal L(H_n\otimes M)$，在 $H_n$ 的正交标准基中写 $A=\sum_{u,v}|u\rangle\langle v|\otimes A_{uv}$，便有
$$
\operatorname{Tr}_{H_n}
\bigl[(I_{H_n}\otimes T_\ell)A(I_{H_n}\otimes T_\ell^*)\bigr]
=\sum_uT_\ell A_{uu}T_\ell^*
=T_\ell(\operatorname{Tr}_{H_n}A)T_\ell^*.
$$
这个恒等式适用于相关联合态。取 $\ell=1$，再对新输出取偏迹，并从 $\Omega_0=P_0$ 归纳，得到
$$
\operatorname{Tr}_{H_n}\Omega_n=\mathcal M^n(P_0)=\sigma_n.
$$
现在取 $A=\Omega_n$，再对最终记忆取偏迹，结合命题 130.1 对完整相干输出的识别，得到
$$
\begin{aligned}
\beta_{n,\ell}
&=\operatorname{Tr}_{H_n\otimes M}
\bigl[(I_{H_n}\otimes T_\ell)\Omega_n(I_{H_n}\otimes T_\ell^*)\bigr]\\
&=\operatorname{Tr}_M(T_\ell\sigma_nT_\ell^*)
=\Gamma_\ell(\sigma_n).
\end{aligned}
$$
这里没有把 $\Omega_n$ 分解成旧输出与记忆的乘积；被忽略的旧输出是通过偏迹消去的。

以下使用有限维迹距离的效应变分式（参见 John Watrous，[The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/)，Cambridge University Press，2018，量子态判别部分）。为同时处理不同输入、输出维数，直接给出所需推导。任意有限维空间 $K$ 上的两个密度 $\theta,\vartheta$ 之差 $A=\theta-\vartheta$ 自伴且迹零。取正、负谱部分 $A_+,A_-$，则
$$
A=A_+-A_-,\qquad A_+A_-=0,\qquad
\operatorname{Tr}A_+=\operatorname{Tr}A_-=\tfrac12\|A\|_1.
$$
对 $0\le E\le I_K$，正性给 $0\le\operatorname{Tr}(EA_\pm)\le\operatorname{Tr}A_\pm$，所以
$$
|\operatorname{Tr}(EA)|\le\tfrac12\|A\|_1.
$$
取 $E$ 为 $A$ 的正谱投影即达到右端，因而
$$
D(\theta,\vartheta)=\sup_{0\le E\le I_K}
|\operatorname{Tr}(E(\theta-\vartheta))|.
$$
对输出空间 $H_\ell$ 上任意效应 $E$，回拉为记忆空间上的
$$
F=T_\ell^*(E\otimes I_M)T_\ell.
$$
由于 $T_\ell$ 等距，
$$
F\ge0,\qquad
I_M-F=T_\ell^*((I_{H_\ell}-E)\otimes I_M)T_\ell\ge0.
$$
故对 $M$ 上的两个密度 $\theta,\vartheta$，偏迹的定义与迹的循环性给
$$
\begin{aligned}
|\operatorname{Tr}(E(\Gamma_\ell(\theta)-\Gamma_\ell(\vartheta)))|
&=|\operatorname{Tr}(F(\theta-\vartheta))|\\
&\le D(\theta,\vartheta).
\end{aligned}
$$
在 $H_\ell$ 上对 $E$ 取上确界，得到
$$
D(\Gamma_\ell(\theta),\Gamma_\ell(\vartheta))
\le D(\theta,\vartheta).
$$
这一步不要求 $\dim H_\ell=\dim M$。取 $\theta=\sigma_n,\vartheta=\sigma_*$，便得所述未来窗口界，右端与 $\ell$ 无关。

为证明边缘相容，先取任意记忆密度 $X$ 与 $A\in\mathcal L(H_\ell)$。由最后一步 $T_{\ell+1}=(I_{H_\ell}\otimes T)T_\ell$，
$$
\begin{aligned}
\operatorname{Tr}\bigl[(A\otimes I_B)\Gamma_{\ell+1}(X)\bigr]
&=\operatorname{Tr}\bigl[T_\ell XT_\ell^*(A\otimes T^*T)\bigr]\\
&=\operatorname{Tr}\bigl[A\Gamma_\ell(X)\bigr].
\end{aligned}
$$
因这对所有 $A$ 成立，$\operatorname{Tr}_{\text{末位}}\Gamma_{\ell+1}(X)=\Gamma_\ell(X)$。另一方面，按第一步分组为 $T_{\ell+1}=(I_B\otimes T_\ell)T$，利用刚才的偏迹交换恒等式得
$$
\operatorname{Tr}_{\text{首位}}\Gamma_{\ell+1}(X)
=\operatorname{Tr}_M\bigl[T_\ell\operatorname{Tr}_B(TXT^*)T_\ell^*\bigr]
=\Gamma_\ell(\mathcal M(X)).
$$
两式在 $\ell=0$ 时均为取整个单点密度的迹，值为 $1$。取 $X=\sigma_*$ 并用 $\mathcal M(\sigma_*)=\sigma_*$，即得左右相容；反复略去末位与首位给所有平移窗口的同一密度 $\eta_\ell$。

对 $TXT^*$ 的展开改为取记忆偏迹，矩阵元变为 $X_{ij}\langle m_j,m_i\rangle$。两记忆向量均为单位向量，交叉内积为 $\sqrt\alpha$，所以得到所列 $\Gamma_1(X)$。再将 $\pi_0,\pi_1$ 代入 $\sigma_*$：
$$
\sigma_*=
\frac1{\mathrm{den}}
\begin{pmatrix}\alpha+\alpha^2&\alpha\sqrt\alpha\\
\alpha\sqrt\alpha&\alpha^2\end{pmatrix}
=\frac1{\mathrm{den}}
\begin{pmatrix}1&\alpha\sqrt\alpha\\
\alpha\sqrt\alpha&\alpha^2\end{pmatrix}.
$$
应用 $\Gamma_1$ 得 $\eta_1$ 的非对角元 $\sqrt\alpha\,\alpha\sqrt\alpha/\mathrm{den}=\alpha^2/\mathrm{den}$，严格为正，故 $\eta_1\ne\Delta_B(\eta_1)$。同时
$$
\det\sigma_*=
\frac{\alpha^2-\alpha^3}{\mathrm{den}^2}
=\frac{\alpha^2(1-\alpha)}{\mathrm{den}^2}
=\frac{\alpha^4}{\mathrm{den}^2}>0.
$$
$\sigma_*$ 为密度且秩二，故此比较族确实使用混合初态。

最后，由命题 125.1 的单点矩阵，令 $c=\alpha^4/\mathrm{den}>0$，则
$$
\rho_1=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix},\qquad
\rho_1-\eta_1=c\begin{pmatrix}-1&1\\1&1\end{pmatrix}.
$$
右边矩阵的平方为 $2c^2I_B$ 且迹零，特征值为 $\sqrt2c,-\sqrt2c$，所以 $D(\rho_1,\eta_1)=\sqrt2c$。命题 130.1 的前缀相容与已证 $\eta$ 的末位相容给
$$
\operatorname{Tr}_{\text{后 }\ell-1\text{ 位}}\rho_\ell=\rho_1,
\qquad
\operatorname{Tr}_{\text{后 }\ell-1\text{ 位}}\eta_\ell=\eta_1.
$$
在效应变分式中将单点效应 $E$ 提升为 $E\otimes I_{H_{\ell-1}}$，即得偏迹收缩；因此
$$
D(\rho_\ell,\eta_\ell)\ge D(\rho_1,\eta_1)
=\frac{\sqrt2\,\alpha^4}{\mathrm{den}}>0
\qquad(\ell\ge1).
$$
故略去左端记录后，所有有限未来窗口的距离都受随 $n$ 趋零的同一上界控制；保留旧首记录的窗口则始终具有上述正的可区分度下界。证毕。

<a id="entry-612"></a>

## 追加锚（本行以下为增补区）
<a id="section-132"></a>

## 132. 边界遗忘下的相邻输出纠缠与统一有限位置见证

**命题 132.1（平稳双位置纠缠及同一轨道的严格负见证界）。** 沿用命题 130.1 的固定等距及命题 131.1 的记号：
$$
\alpha=\frac{\sqrt5-1}{2},\qquad 0<\alpha<1,\qquad \alpha+\alpha^2=1,
\qquad \mathrm{den}=1+\alpha^2,\qquad
\pi_0=\frac1{\mathrm{den}},\qquad \pi_1=\frac{\alpha^2}{\mathrm{den}}.
$$
取 $B=M=\mathbb C^2$，均以 $|0\rangle,|1\rangle$ 为正交标准基，并令
$$
m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,\qquad
m_1=|0\rangle,\qquad P_j=|m_j\rangle\langle m_j|,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1).
$$
顺序始终为输出在前、记忆在后；$T_0=I_M$，$T_{\ell+1}=(I_{B^{\otimes\ell}}\otimes T)T_\ell$，且
$$
\Gamma_\ell(X)=\operatorname{Tr}_M(T_\ell XT_\ell^*),\qquad
\sigma_*=\pi_0P_0+\pi_1P_1,\qquad
\eta_\ell=\Gamma_\ell(\sigma_*),\qquad
\rho_\ell=\Gamma_\ell(P_0).
$$
命题 131.1 给出的 $\sigma_*$ 是秩二混合不动密度，$\eta_\ell$ 为平稳比较族；原族 $\rho_\ell$ 仍从纯记忆 $P_0$ 出发。此混合比较初态不改变命题 130.1 的纯初态容量定理及其适用类别。

以下张量分割为两个实际发出位置的完整空间 $B_1\otimes B_2=\mathbb C^2\otimes\mathbb C^2$。称其上的密度 $\theta$ 可分，是指存在有限分解
$$
\theta=\sum_{r=1}^N q_r A_r\otimes C_r,\qquad
q_r\ge0,\qquad \sum_{r=1}^N q_r=1,
$$
其中 $A_r,C_r$ 分别为 $B_1,B_2$ 上的密度，即正半定且迹为一的算子。不满足此定义者称为纠缠态。合法支撑 $\operatorname{span}\{|00\rangle,|01\rangle,|10\rangle\}$ 只是完整空间的子空间，不另赋予它一个张量分割。

在字典序 $00,01,10,11$ 下，平稳双位置密度为
$$
\eta_2=\pi_0
\begin{pmatrix}
\alpha&\alpha^2&\alpha^2&0\\
\alpha^2&\alpha^2&\alpha^3&0\\
\alpha^2&\alpha^3&\alpha^2&0\\
0&0&0&0
\end{pmatrix}.
$$
定义 Hermitian 算子
$$
W_{\rm ent}=\alpha^4|00\rangle\langle00|+|11\rangle\langle11|
-\alpha^2\bigl(|01\rangle\langle10|+|10\rangle\langle01|\bigr).
$$
则对每个可分密度 $\theta$ 有 $\operatorname{Tr}(W_{\rm ent}\theta)\ge0$，而
$$
\operatorname{Tr}(W_{\rm ent}\eta_2)=-\pi_0\alpha^5<0.
$$
因此 $\eta_2$ 在两个发出位置之间纠缠。$W_{\rm ent}$ 有负特征值，因而不是正的 POVM 效应；这里使用的是其期望值作为纠缠见证。

同一命题还适用于原纯初态轨道的每个有限位置。对整数 $n\ge0$，令
$$
\beta_{n,2}=\operatorname{Tr}_{\text{前 }n\text{ 位}}\rho_{n+2}.
$$
这些窗口均忽略前 $n$ 位及最终记忆，不作条件化、反馈或其它干预。命题 131.1 的实际相关前缀恒等式与递推给
$$
\beta_{n,2}=\Gamma_2(\sigma_n),\qquad
\sigma_n=(1-p_n)P_0+p_nP_1,\qquad
p_0=0,\qquad p_{n+1}=\alpha^2(1-p_n).
$$
同一个 $W_{\rm ent}$ 满足
$$
\operatorname{Tr}(W_{\rm ent}\beta_{n,2})
=\alpha^5\bigl((\alpha-2)+(3-\alpha)p_n\bigr)
\le-2\alpha^8<0\qquad(n\ge0),
$$
且 $n=1$ 时等号成立。故原族的每个平移相邻窗口也纠缠；$-2\alpha^8$ 是此固定见证沿指定轨道的期望最大值，不是对所有态或见证优化的纠缠量。

证明。由 $T$ 的基像及顺序递推，
$$
T_2|0\rangle=\sqrt\alpha\,|00\rangle\otimes m_0
+\alpha|01\rangle\otimes m_1,\qquad
T_2|1\rangle=|10\rangle\otimes m_0.
$$
为核对全部矩阵元，对 $u\in\{00,01,10,11\}$ 定义记忆系数映射
$$
L_u=(\langle u|\otimes I_M)T_2,\qquad
L_{00}=\sqrt\alpha\,|m_0\rangle\langle0|,\quad
L_{01}=\alpha|m_1\rangle\langle0|,\quad
L_{10}=|m_0\rangle\langle1|,\quad L_{11}=0.
$$
于是对任意 $X\in\mathcal L(M)$ 及任意 $u,v$，
$$
\langle u|\Gamma_2(X)|v\rangle=\operatorname{Tr}(L_uXL_v^*).
$$
两个记忆向量的实际内积为
$$
\langle m_0,m_0\rangle=\langle m_1,m_1\rangle=1,\qquad
\langle m_0,m_1\rangle=\langle m_1,m_0\rangle=\sqrt\alpha.
$$
具体地，对非零的三个 $L_u=c_u|m_{k_u}\rangle\langle j_u|$，上式等于
$$
c_uc_vX_{j_uj_v}\langle m_{k_v},m_{k_u}\rangle,
\qquad
(c_u,j_u,k_u)=
\begin{cases}
(\sqrt\alpha,0,0),&u=00,\\
(\alpha,0,1),&u=01,\\
(1,1,0),&u=10.
\end{cases}
$$
任一指标为 $11$ 时则为零。三个对角元依次是 $\alpha X_{00},\alpha^2X_{00},X_{11}$；三个上三角非对角元依次是
$$
\sqrt\alpha\,\alpha X_{00}\langle m_1,m_0\rangle=\alpha^2X_{00},\qquad
\sqrt\alpha\,X_{01}\langle m_0,m_0\rangle=\sqrt\alpha\,X_{01},\qquad
\alpha X_{01}\langle m_0,m_1\rangle=\alpha\sqrt\alpha\,X_{01}.
$$
反向指标仍由同一公式给出，无需假设 $X$ 自伴。因此全部十六个矩阵元为
$$
\Gamma_2(X)=
\begin{pmatrix}
\alpha X_{00}&\alpha^2X_{00}&\sqrt\alpha\,X_{01}&0\\
\alpha^2X_{00}&\alpha^2X_{00}&\alpha\sqrt\alpha\,X_{01}&0\\
\sqrt\alpha\,X_{10}&\alpha\sqrt\alpha\,X_{10}&X_{11}&0\\
0&0&0&0
\end{pmatrix}.
$$
这里的相干项来自记忆向量的内积，非法扇区的整行整列由 $L_{11}=0$ 消失，并非只计算经典转移概率。

将命题 131.1 的矩阵
$$
\sigma_*=\pi_0
\begin{pmatrix}1&\alpha\sqrt\alpha\\
\alpha\sqrt\alpha&\alpha^2\end{pmatrix}
$$
代入，便得到陈述中的完整 $\eta_2$。它由密度 $\sigma_*$ 经等距及偏迹得到，故为正半定；同时
$$
\operatorname{Tr}\eta_2=\pi_0(\alpha+2\alpha^2)
=\pi_0(1+\alpha^2)=1.
$$
命题 131.1 的左右边缘相容性已保证，这也是该平稳比较族中任意两个相邻位置的密度。

现证明见证对全部可分态非负。任取复向量
$$
a=a_0|0\rangle+a_1|1\rangle\in B_1,\qquad
b=b_0|0\rangle+b_1|1\rangle\in B_2,
$$
不要求归一化，也不限制其乘积向量的支撑。直接展开给
$$
\begin{aligned}
\langle a\otimes b,W_{\rm ent}(a\otimes b)\rangle
&=\alpha^4|a_0b_0|^2+|a_1b_1|^2
-2\alpha^2\operatorname{Re}\bigl(\overline{a_0b_1}\,a_1b_0\bigr)\\
&=\left|a_1\overline{b_1}-\alpha^2a_0\overline{b_0}\right|^2\ge0.
\end{aligned}
$$
第二个因子的共轭不可省略：该等式使用任意复坐标，而非实向量的限制。若 $A,C$ 为两个因子上的密度，有限维谱分解给
$$
A=\sum_r\lambda_r|a^{(r)}\rangle\langle a^{(r)}|,\qquad
C=\sum_s\mu_s|b^{(s)}\rangle\langle b^{(s)}|,\qquad
\lambda_r,\mu_s\ge0,
$$
其中谱向量为单位向量，两组特征值各自和为一。按张量积及迹的线性性，
$$
\operatorname{Tr}\bigl(W_{\rm ent}(A\otimes C)\bigr)
=\sum_{r,s}\lambda_r\mu_s
\left|a^{(r)}_1\overline{b^{(s)}_1}
-\alpha^2a^{(r)}_0\overline{b^{(s)}_0}\right|^2\ge0.
$$
再对可分密度的有限凸组合应用线性性，即得 $\operatorname{Tr}(W_{\rm ent}\theta)\ge0$。这正是块正算子在可分锥上配对非负的成熟可分性数学（[CompositeConeDuality，blockPositive_iff_forall_separable_pairing_nonneg](../../../../D5/S3/Resource/CompositeConeDuality.lean)）。

此见证的偏转置来源也可直接表示为
$$
W_{\rm ent}=\operatorname{PT}_2\bigl(|v\rangle\langle v|\bigr),\qquad
v=|11\rangle-\alpha^2|00\rangle,\qquad
\operatorname{PT}_2(|ij\rangle\langle kl|)=|il\rangle\langle kj|,
$$
其中 $\operatorname{PT}_2$ 按此基公式线性延伸。偏转置的可分性判据见 Asher Peres，Separability Criterion for Density Matrices，Physical Review Letters 77，1413–1415（1996），[DOI:10.1103/PhysRevLett.77.1413](https://doi.org/10.1103/PhysRevLett.77.1413)，[arXiv:quant-ph/9604005](https://arxiv.org/abs/quant-ph/9604005)。这里仅使用其数学含义，不把偏转置当作物理操作；所需非负性已由平方模及谱分解直接证明。

$W_{\rm ent}$ 的两个交叉项互为伴随，故它自伴。而
$$
W_{\rm ent}(|01\rangle+|10\rangle)
=-\alpha^2(|01\rangle+|10\rangle),
$$
所以它不是正半定算子，也不满足 POVM 效应所需的 $0\le E\le I$。由 $\eta_2$ 的上述矩阵元，
$$
\begin{aligned}
\operatorname{Tr}(W_{\rm ent}\eta_2)
&=\alpha^4\langle00|\eta_2|00\rangle
+\langle11|\eta_2|11\rangle
-\alpha^2\bigl(\langle10|\eta_2|01\rangle+\langle01|\eta_2|10\rangle\bigr)\\
&=\pi_0\alpha^5-2\pi_0\alpha^5=-\pi_0\alpha^5<0.
\end{aligned}
$$
这与可分密度的非负性矛盾，证明平稳双位置态纠缠。

最后处理同一纯初态轨道的有限位置。将
$$
P_0=\begin{pmatrix}\alpha&\alpha\sqrt\alpha\\
\alpha\sqrt\alpha&\alpha^2\end{pmatrix},\qquad
P_1=\begin{pmatrix}1&0\\0&0\end{pmatrix}
$$
代入已求出的 $\Gamma_2$，得到
$$
G_0:=\Gamma_2(P_0)=
\begin{pmatrix}
\alpha^2&\alpha^3&\alpha^2&0\\
\alpha^3&\alpha^3&\alpha^3&0\\
\alpha^2&\alpha^3&\alpha^2&0\\
0&0&0&0
\end{pmatrix},
$$
$$
G_1:=\Gamma_2(P_1)=|0\rangle\langle0|\otimes\rho_1
=\begin{pmatrix}
\alpha&\alpha^2&0&0\\
\alpha^2&\alpha^2&0&0\\
0&0&0&0\\
0&0&0&0
\end{pmatrix},\qquad
\rho_1=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}.
$$
由命题 131.1 已在相关联合态上证明的窗口恒等式与 $\Gamma_2$ 的线性性，
$$
\beta_{n,2}=(1-p_n)G_0+p_nG_1.
$$
因而
$$
\operatorname{Tr}(W_{\rm ent}G_0)=\alpha^6-2\alpha^5
=\alpha^5(\alpha-2),\qquad
\operatorname{Tr}(W_{\rm ent}G_1)=\alpha^5,
$$
$$
\operatorname{Tr}(W_{\rm ent}\beta_{n,2})
=\alpha^5\bigl((\alpha-2)+(3-\alpha)p_n\bigr).
$$
递推映射 $p\mapsto\alpha^2(1-p)$ 将闭区间 $[0,\alpha^2]$ 映到
$$
[\alpha^2(1-\alpha^2),\alpha^2]=[\alpha^3,\alpha^2]
\subseteq[0,\alpha^2].
$$
从 $p_0=0$ 归纳得 $0\le p_n\le\alpha^2$ 对所有 $n\ge0$ 成立，且 $p_1=\alpha^2$。用 $\alpha+\alpha^2=1$ 化简，有
$$
(\alpha-2)+(3-\alpha)\alpha^2=-2\alpha^3,
$$
$$
\operatorname{Tr}(W_{\rm ent}\beta_{n,2})+2\alpha^8
=\alpha^5(3-\alpha)(p_n-\alpha^2)\le0.
$$
由于 $\alpha>0$、$3-\alpha>0$，这给出陈述中的统一严格负界，并在 $n=1$ 达到等号。每个 $\beta_{n,2}$ 因此均不可分。命题 130.1 的已发出前缀不变性还保证，继续生成任意有限个后续输出再忽略它们，不改变这一对已发出位置的边际。

同时，直接引用命题 131.1 在同一无条件窗口上的结论，
$$
D(\beta_{n,2},\eta_2)\le\frac{\alpha^3}{\mathrm{den}}\alpha^{2n}
\longrightarrow0\qquad(n\longrightarrow\infty).
$$
因此此固定生成器的边界遗忘与相邻输出纠缠同时成立。这里在单位置的指定基相干之外，进一步判定了跨两个输出因子的不可分性；此结论不蕴含 Bell 非局域性或情境性，不量化所有平稳态，也不构成物理空间的推导、最优负性或距离的断言。证毕。

<a id="entry-614"></a>

## 追加锚（本行以下为增补区）
<a id="section-133"></a>

## 133. 忽略间隔后的分块可分性与平稳占据关联的非零尾

**命题 133.1（相关输入的间隔分解与交替衰减的平稳协方差）。** 沿用命题 130.1 的同一个固定等距及命题 131.1 的记忆通道。取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad 0<\alpha<1,\qquad \alpha+\alpha^2=1,
\qquad B=M=\mathbb C^2,\qquad H_n=B^{\otimes n},\qquad H_0=\mathbb C,
$$
$$
m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,\qquad
m_1=|0\rangle,\qquad P_j=|m_j\rangle\langle m_j|,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1).
$$
两份二维空间均取正交标准基 $|0\rangle,|1\rangle$。以 $\dagger$ 表示伴随，$I_K$ 表示空间 $K$ 上的恒等算子，$\operatorname{Id}_K$ 表示算子空间 $\mathcal L(K)$ 上的恒等超算子。输出在前、记忆在后的顺序固定为
$$
T_0=I_M,\qquad T_{n+1}=(I_{H_n}\otimes T)T_n,
\qquad T^\dagger T=I_M,
$$
$$
\mathcal M(X)=\operatorname{Tr}_B(TXT^\dagger)=X_{00}P_0+X_{11}P_1,
\qquad \Gamma_n(X)=\operatorname{Tr}_M(T_nXT_n^\dagger),
\qquad \mathcal M^0=\operatorname{Id}_M.
$$
这里 $M$ 是 Hilbert 空间，$\mathcal M$ 是记忆通道。再记
$$
\pi_0=\frac1{1+\alpha^2},\qquad \pi_1=\frac{\alpha^2}{1+\alpha^2},\qquad
\sigma_*=\pi_0P_0+\pi_1P_1,\qquad
\eta_n=\Gamma_n(\sigma_*),\qquad \rho_n=\Gamma_n(P_0).
$$
命题 131.1 给出 $\mathcal M(\sigma_*)=\sigma_*$ 及 $\eta$ 的平稳边缘相容性。

第一，设 $L$ 为任意有限维复 Hilbert 空间，$\Omega$ 为 $L\otimes M$ 上任意密度，允许两因子相关或纠缠。旧因子 $L$ 始终不受作用。对整数 $g,b\ge1$，依序发出 $g$ 个被忽略的中间输出及 $b$ 个保留的右侧输出；完整次序为 $L\otimes H_g\otimes H_b\otimes M$。保留态定义为实际联合态的偏迹
$$
\omega_{LR}
=\operatorname{Tr}_{H_g,M}\bigl[
(I_L\otimes T_{g+b})\Omega(I_L\otimes T_{g+b}^\dagger)
\bigr]\in\mathcal L(L\otimes H_b).
$$
令
$$
A_j=(I_L\otimes\langle j|)\Omega(I_L\otimes|j\rangle),
\qquad w_j=\operatorname{Tr}A_j\quad(j=0,1).
$$
则 $A_j\ge0$、$w_j\ge0$、$w_0+w_1=1$，并且
$$
\begin{aligned}
\omega_{LR}
&=\bigl(\operatorname{Id}_L\otimes(\Gamma_b\circ\mathcal M^g)\bigr)(\Omega)\\
&=\sum_{j=0}^1 A_j\otimes\Gamma_b\bigl(\mathcal M^{g-1}(P_j)\bigr)\\
&=\sum_{\substack{j=0,1\\w_j>0}}
w_j\,\frac{A_j}{w_j}\otimes\Gamma_b\bigl(\mathcal M^{g-1}(P_j)\bigr).
\end{aligned}
$$
复合中先作用 $\mathcal M^g$，再作用 $\Gamma_b$。每个右因子均为 $H_b$ 上的密度；$w_j=0$ 时 $A_j=0$，不对此项归一化。最后一式是在完整 $L\mid H_b$ 张量分割上的有限凸乘积态分解，因而 $\omega_{LR}$ 可分。$g=1$ 时右因子就是 $\Gamma_b(P_j)$，此结论不包含 $g=0$ 的可分性断言。任意有限维且不受作用的参考系统均可并入 $L$；假设只允许所写的固定顺序等距及无条件偏迹，不包含联合控制、读取间隔记录、条件化或恢复间隔的操作。

特别地，对 $X=\sigma_*$ 或 $X=P_0$、整数 $r\ge0$ 及 $a,g,b\ge1$，按 $H_r\otimes H_a\otimes H_g\otimes H_b$ 分组的
$$
\theta^X_{r;a,g,b}
=\operatorname{Tr}_{H_r,H_g}\Gamma_{r+a+g+b}(X)
$$
在完整 $H_a\mid H_b$ 分割上可分。这里左块之前恰有 $r$ 个被忽略输出，两块之间恰有 $g$ 个被忽略输出；再生成任意有限个右侧输出并忽略它们，也不改变此保留态。

第二，仅对平稳族 $\eta$，将输出从 $0$ 编号。在 $H_{d+1}$ 上令
$$
N_i=I_{H_i}\otimes|1\rangle\langle1|\otimes I_{H_{d-i}}
\qquad(0\le i\le d).
$$
对每个整数 $d\ge1$，两处占据均值均为 $\pi_1$，且
$$
\operatorname{Cov}_d
:=\operatorname{Tr}(\eta_{d+1}N_0N_d)-\pi_1^2
=\pi_0\pi_1(-\alpha^2)^d.
$$
此值在每个有限 $d$ 均非零，奇数距离为负、偶数距离为正，绝对值 $\pi_0\pi_1\alpha^{2d}$ 趋于零。对 $d\ge2$，忽略中间 $g=d-1\ge1$ 个位置后的双位置态可分，却不是乘积态；更一般地，任何相隔 $g\ge1$ 个被忽略位置的非空平稳有限块也不是乘积态。

证明。先在相关联合态上识别被忽略输出的作用。按记忆标准基展开
$$
\Omega=\sum_{i,k=0}^1\Omega_{ik}\otimes|i\rangle\langle k|,
\qquad
\Omega_{ik}=(I_L\otimes\langle i|)\Omega(I_L\otimes|k\rangle).
$$
真实的一步等距给出 $L\otimes B\otimes M$ 上的算子
$$
(I_L\otimes T)\Omega(I_L\otimes T^\dagger)
=\sum_{i,k=0}^1\Omega_{ik}\otimes|i\rangle\langle k|
\otimes|m_i\rangle\langle m_k|.
$$
新输出因子的 $|i\rangle\langle k|$ 的迹是 $\delta_{ik}$，故取该输出的偏迹恰好消去 $i\ne k$ 项，得到
$$
\operatorname{Tr}_B\bigl[(I_L\otimes T)\Omega(I_L\otimes T^\dagger)\bigr]
=\sum_{j=0}^1A_j\otimes P_j
=(\operatorname{Id}_L\otimes\mathcal M)(\Omega).
$$
这保留了 $\Omega$ 的两个对角算子块，并未以两边的边缘态替换 $\Omega$。

为在以后各步沿用此等式，直接使用命题 131.1 的相关偏迹恒等式并保留旁观因子 $L$。具体地，设 $E$ 为已发出而待忽略的因子，$Z$ 为 $L\otimes E\otimes M$ 上的算子，取 $E$ 的正交基 $(e_u)$ 并写
$$
D_{uv}=(I_L\otimes\langle e_u|\otimes I_M)
Z(I_L\otimes|e_v\rangle\otimes I_M)
\in\mathcal L(L\otimes M).
$$
在 $L\otimes E\otimes H_\ell\otimes M$ 的顺序下，取 $E$ 的对角块后求和给
$$
\begin{aligned}
&\operatorname{Tr}_E\bigl[
(I_L\otimes I_E\otimes T_\ell)Z
(I_L\otimes I_E\otimes T_\ell^\dagger)\bigr]\\
&\quad=\sum_u(I_L\otimes T_\ell)D_{uu}(I_L\otimes T_\ell^\dagger)\\
&\quad=(I_L\otimes T_\ell)(\operatorname{Tr}_E Z)
(I_L\otimes T_\ell^\dagger).
\end{aligned}
$$
所以先取旧因子的偏迹与继续只作用记忆的等距可交换。由一步公式归纳，
$$
\operatorname{Tr}_{H_g}\bigl[
(I_L\otimes T_g)\Omega(I_L\otimes T_g^\dagger)\bigr]
=(\operatorname{Id}_L\otimes\mathcal M^g)(\Omega)
=\sum_{j=0}^1A_j\otimes\mathcal M^{g-1}(P_j)
\qquad(g\ge1).
$$
再按顺序分组
$$
T_{g+b}=(I_{H_g}\otimes T_b)T_g,
$$
应用刚才的偏迹交换式，最后取记忆偏迹，便得到陈述中的 $\omega_{LR}$ 两个线性表达式。

对任意 $v\in L$，
$$
\langle v,A_jv\rangle
=(\langle v|\otimes\langle j|)\Omega(|v\rangle\otimes|j\rangle)\ge0,
\qquad \sum_j\operatorname{Tr}A_j=\operatorname{Tr}\Omega=1.
$$
因此 $A_j$ 正半定；若其迹为零，所有非负特征值之和为零，故 $A_j=0$。正权重项的 $A_j/w_j$ 是密度。命题 131.1 的记忆通道及输出通道均由等距共轭与偏迹给出，保持正性与迹；$P_j$ 是密度，故 $\Gamma_b(\mathcal M^{g-1}(P_j))$ 也是密度。由此得到所述有限凸分解，包括仅一个权重为正的情形。

这一步所用的测量后制备可分性是成熟的纠缠破坏通道数学：Michael Horodecki、Peter W. Shor、Mary Beth Ruskai，[General Entanglement Breaking Channels，arXiv:quant-ph/0302031v2](https://arxiv.org/abs/quant-ph/0302031v2)（该版本 PDF 的题头为 Entanglement Breaking Channels），定理 4 的 (A)、(B)、(D) 分别给出测量后制备表示、纠缠破坏性质及秩一 Kraus 表示的等价性。其保迹资格在这里由测量效应 $|j\rangle\langle j|$ 构成 POVM 以及
$$
C_j=|m_j\rangle\langle j|,\qquad
\mathcal M(X)=\sum_{j=0}^1 C_jXC_j^\dagger,\qquad
\sum_{j=0}^1 C_j^\dagger C_j=I_M
$$
落实；制备态为单位迹的 $P_j$。上面的相关算子块计算是该等价性在此固定生成器中的直接应用。

现在取 $L=H_a$、$\Omega=T_aXT_a^\dagger$。在 $H_a\otimes H_g\otimes H_b\otimes M$ 上，迭代的分组恒等式把此后的联合态识别为 $T_{a+g+b}XT_{a+g+b}^\dagger$，故前述 $\omega_{LR}$ 正是 $\Gamma_{a+g+b}(X)$ 忽略中间 $g$ 位后的首 $a$ 位、末 $b$ 位约化态。若还有被忽略的前缀 $r\ge0$，先按 $H_r\otimes H_a\otimes M$ 分组；命题 131.1 的同一偏迹恒等式给
$$
\Omega^{(r,a)}
:=\operatorname{Tr}_{H_r}(T_{r+a}XT_{r+a}^\dagger)
=T_a\mathcal M^r(X)T_a^\dagger.
$$
于是保留左块之前的实际记忆输入是 $\mathcal M^r(X)$，而左块发出后的实际输入是相关密度 $\Omega^{(r,a)}$。将其代入第一部分即得 $\theta^X_{r;a,g,b}$ 的可分性。$r=0$ 时 $H_0=\mathbb C$，式子同样成立。最后，命题 130.1 的已发出前缀不变性，或命题 131.1 的末位边缘相容恒等式，说明继续生成再忽略任意有限后缀保持所有这些约化态。这同时适用于纯边界族与平稳族。

下面计算平稳占据关联。令 $Y_i\in\{0,1\}$ 表示第 $i$ 个输出在计算基中的测量值，并用未归一化分支映射
$$
\mathcal J_j(X)=C_jXC_j^\dagger=X_{jj}P_j.
$$
它确实来自实际发出输出的投影，因为 $(\langle j|\otimes I_M)T=C_j$。旧输出上的投影可与以后仅作用记忆及新输出的步骤交换；依次收缩各个输出因子，对任意词 $w=(j_0,\ldots,j_{n-1})$ 有
$$
(\langle w|\otimes I_M)T_n=C_{j_{n-1}}\cdots C_{j_0},
$$
$$
\langle w|\eta_n|w\rangle
=\operatorname{Tr}\bigl[
(\mathcal J_{j_{n-1}}\circ\cdots\circ\mathcal J_{j_0})(\sigma_*)
\bigr].
$$
故这些分支的迹是完整相干态 $\eta_n$ 的实际对角概率，而非以去相干态代替原联合态所得的假设。

$\sigma_*$ 的两个对角元为
$$
(\sigma_*)_{00}=\pi_0\alpha+\pi_1=\pi_0,
\qquad (\sigma_*)_{11}=\pi_0\alpha^2=\pi_1.
$$
因此首次概率为 $(\pi_0,\pi_1)$；任一正概率分支发出 $j$ 后，归一化记忆为 $P_j$。由
$$
\operatorname{diag}P_0=(\alpha,\alpha^2),\qquad
\operatorname{diag}P_1=(1,0)
$$
得到以旧值标行、新值标列的转移矩阵
$$
K=\begin{pmatrix}\alpha&\alpha^2\\1&0\end{pmatrix},
\qquad \pi=(\pi_0,\pi_1),\qquad \pi K=\pi.
$$
更明确地，$\mathcal J_k(P_j)=K_{jk}P_k$，所以对所有词，包括概率为零的词，都有
$$
(\mathcal J_{j_{n-1}}\circ\cdots\circ\mathcal J_{j_0})(\sigma_*)
=\pi_{j_0}\left(\prod_{t=1}^{n-1}K_{j_{t-1}j_t}\right)P_{j_{n-1}},
$$
$$
\Pr(Y_0=j_0,\ldots,Y_{n-1}=j_{n-1})
=\pi_{j_0}\prod_{t=1}^{n-1}K_{j_{t-1}j_t}\qquad(n\ge1).
$$
空乘积取一。这一未归一化恒等式处理零分支而无需除以零，且给出实际计算基词律的平稳 Markov 递推。

由于 $\pi_1>0$，可定义
$$
q_d=\Pr(Y_d=1\mid Y_0=1),\qquad q_0=1.
$$
转移到 $1$ 的概率从 $0$ 出发为 $\alpha^2$，从 $1$ 出发为零，故
$$
q_{d+1}=\alpha^2(1-q_d),\qquad
\pi_1=\alpha^2(1-\pi_1),\qquad
q_{d+1}-\pi_1=-\alpha^2(q_d-\pi_1).
$$
从 $q_0-\pi_1=\pi_0$ 归纳得到
$$
q_d=\pi_1+\pi_0(-\alpha^2)^d\qquad(d\ge0).
$$
每个位置的占据均值由 $\pi K=\pi$ 等于 $\pi_1$；$N_0N_d$ 的联合均值则为
$$
\operatorname{Tr}(\eta_{d+1}N_0N_d)
=\Pr(Y_0=1,Y_d=1)=\pi_1q_d.
$$
减去 $\pi_1^2$ 即得协方差公式。特别地，$q_1=0$，且
$$
\operatorname{Cov}_1=-\pi_0\pi_1\alpha^2=-\pi_1^2,
$$
与相邻词 $11$ 的概率为零一致。$0<\alpha<1$ 及 $\pi_0\pi_1>0$ 给出所有有限距离的非零性、符号交替与衰减极限。

若 $d\ge2$，第一部分取 $a=b=1$、$g=d-1$、$X=\sigma_*$ 即得端点态可分；乘积态上两个局部占据算子的期望乘法分解，协方差必为零，故这里的端点态不是乘积态。对两个非空平稳块，取左块末位与右块首位，距离为 $g+1$；平稳边缘相容性给出同一个非零协方差，因而两块也不是乘积态。

这里 $\langle m_0,m_1\rangle=\sqrt\alpha\ne0$，分解指标 $j$ 不构成可完美读取的记忆标志。上述可分性不蕴含零量子失协、固定乘积基中的对角性或量子条件独立性，也不判定整个多位置态的多体纠缠；占据协方差的非零尾不等于纠缠，亦不给出所有关联的有限支撑。$d$ 只计输出位置间距，不表示物理长度或时间。结合命题 132.1 的 $\eta_2$ 及每个 $\beta_{n,2}$ 的相邻纠缠，同一生成器中相邻输出纠缠、平稳族在每个有限距离的非零衰减占据关联，与无条件忽略任意含 $g\ge1$ 个输出的间隔后两侧有限块的可分性同时成立。证毕。

<a id="entry-616"></a>

## 追加锚（本行以下为增补区）

<a id="section-134"></a>

## 134. 选择性局部测量下的有限间隔端点纠缠

**命题 134.1（纯边界的指定纠缠分支与无条件可分平均）。** 沿用命题 130.1 的固定生成器，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
\alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1).
$$
两份二维空间均取正交标准基 $|0\rangle,|1\rangle$，$\dagger$ 表示伴随。记
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad
T_0=I_M,\qquad T_{n+1}=(I_{H_n}\otimes T)T_n,\qquad
\Xi_n=T_nm_0.
$$
对整数 $g\ge0$，从纯初始记忆 $m_0$ 恰好生成 $n=g+2$ 个输出，按
$$
B_L\otimes H_g\otimes B_R\otimes M
$$
分组：$L$、$R$ 分别是第一个、最后一个已发出的输出 qubit，$M$ 是生成结束后的活动记忆。左端点之前没有被忽略的输出前缀。假设生成结束后可以分别测量每个内部输出及最终活动记忆，并可访问这些测量的经典结果记录以选择分支；两个端点均保留。

在内部输出上使用正交基
$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
|-\rangle=\frac{|0\rangle-|1\rangle}{\sqrt2},
$$
在最终活动记忆上使用计算基。对全部 $\varepsilon\in\{+,-\}^g$、$k\in\{0,1\}$，令 $|\varepsilon\rangle=|\varepsilon_1\rangle\otimes\cdots\otimes|\varepsilon_g\rangle$，定义实际联合向量的收缩
$$
v_{\varepsilon,k}
=(I_{B_L}\otimes\langle\varepsilon|\otimes I_{B_R}\otimes\langle k|)\Xi_{g+2}
\in B_L\otimes B_R.
$$
$g=0$ 时内部字符串为空，$|\varepsilon\rangle=1\in H_0$，其 bra 为恒等收缩。各个被测因子上的物理投影彼此交换，其联合投影为
$$
Q_{\varepsilon,k}
=I_{B_L}\otimes|\varepsilon\rangle\langle\varepsilon|
 \otimes I_{B_R}\otimes|k\rangle\langle k|.
$$

选择全部内部结果为 $+$ 且最终记忆结果为 $0$，记 $v_g=v_{(+,\ldots,+),0}$。令
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
v_g=\sum_{i,j=0}^1 C_g(i,j)|i\rangle_L\otimes|j\rangle_R,
$$
其中系数矩阵以左端点位值为行、右端点位值为列。则
$$
C_g=\frac{s^{g+3}}{(\sqrt2)^g}J^{g+1},\qquad
C_0=\alpha sJ,\qquad
\det C_g=-\alpha^3\left(-\frac\alpha2\right)^g\ne0.
$$
该联合事件的 Born 概率及条件密度为
$$
p_g=\|v_g\|^2=\operatorname{Tr}(C_gC_g^\dagger),\qquad
0<p_g<1,\qquad
\theta_g=\frac{|v_g\rangle\langle v_g|}{p_g}.
$$
这里可分性始终指完整 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$ 上的有限凸可分性：密度 $\omega$ 可分，当且仅当存在有限个权重 $\lambda_a\ge0$、$\sum_a\lambda_a=1$ 及各自二维空间上的密度 $\sigma_a,\tau_a$，使
$$
\omega=\sum_a\lambda_a\,\sigma_a\otimes\tau_a.
$$
对每个有限 $g\ge0$，$\theta_g$ 均不可分；它的密度算子秩为 $1$，而其系数矩阵秩、亦即 Schmidt 秩为 $2$。

对完整测量的每个结果令 $p_{\varepsilon,k}=\|v_{\varepsilon,k}\|^2$，仅在 $p_{\varepsilon,k}>0$ 时定义 $\theta_{\varepsilon,k}=|v_{\varepsilon,k}\rangle\langle v_{\varepsilon,k}|/p_{\varepsilon,k}$。则
$$
\begin{aligned}
\Theta_g
&:=\operatorname{Tr}_{H_g,M}|\Xi_{g+2}\rangle\langle\Xi_{g+2}|\\
&=\sum_{\varepsilon\in\{+,-\}^g}\sum_{k=0}^1
 |v_{\varepsilon,k}\rangle\langle v_{\varepsilon,k}|\\
&=\sum_{\substack{\varepsilon\in\{+,-\}^g,\ k\in\{0,1\}\\p_{\varepsilon,k}>0}}
 p_{\varepsilon,k}\theta_{\varepsilon,k},\qquad
\sum_{\varepsilon,k}p_{\varepsilon,k}=1.
\end{aligned}
$$
零概率项在未归一化求和中为零。对 $g\ge1$，此无条件端点密度 $\Theta_g$ 可分；这一可分性结论不包含 $g=0$。

证明。记 $W_n$ 为长度 $n$ 的不含相邻 $11$ 的二进制词集，$W_n^0$ 为其中末位为 $0$ 的词集。命题 130.1 在完整输出与最终记忆空间上给出
$$
\Xi_n
=s^{n+1}\sum_{w\in W_n}|w\rangle\otimes|0\rangle
 +s^{n+2}\sum_{w\in W_n^0}|w\rangle\otimes|1\rangle
\qquad(n\ge1).
$$
取 $n=g+2$。最终记忆的 $\langle0|$ 选出第一列；每个内部计算基位值与 $\langle+|$ 的内积均为 $1/\sqrt2$，所以
$$
C_g(i,j)=\frac{s^{g+3}}{(\sqrt2)^g}
\#\{u\in\{0,1\}^g:(i,u,j)\in W_{g+2}\}.
$$
这是对完整联合向量的线性收缩。这里的 $1/\sqrt2$ 是基向量的内积，不是单次结果具有概率 $1/2$ 或结果相互独立的假设。

$J_{ab}$ 恰为相邻位值 $a,b$ 的相容性指示数。展开矩阵乘法，固定 $x_0=i$、$x_{g+1}=j$，有
$$
(J^{g+1})_{ij}
=\sum_{(x_1,\ldots,x_g)\in\{0,1\}^g}
 \prod_{t=0}^{g}J_{x_tx_{t+1}}.
$$
每个乘积在对应整词合法时为 $1$，否则为 $0$，故此式正好计数上面的内部词。$g=0$ 时求和只有空内部词这一项，乘积为 $J_{ij}$，从而同样得到 $C_0=s^3J=\alpha sJ$。于是所有 $g\ge0$ 的系数矩阵公式成立。由于 $\det J=-1$，行列式的乘法性给
$$
\det C_g
=\frac{s^{2g+6}}{2^g}(\det J)^{g+1}
=\frac{\alpha^{g+3}}{2^g}(-1)^{g+1}
=-\alpha^3\left(-\frac\alpha2\right)^g.
$$
$\alpha>0$，故任意有限 $g$ 下该行列式均不为零，特别地 $v_g\ne0$。

命题 130.1 给 $\|\Xi_{g+2}\|=1$。正交投影是压缩，且所选测量因子均为单位向量，故
$$
p_g=\langle\Xi_{g+2},Q_{(+,\ldots,+),0}\Xi_{g+2}\rangle
=\|v_g\|^2\le1.
$$
按端点正交基展开范数，得到 $\|v_g\|^2=\sum_{i,j}|C_g(i,j)|^2=\operatorname{Tr}(C_gC_g^\dagger)$；$v_g\ne0$ 给 $p_g>0$。为证严格上界，在上面的第二记忆列中，全零输出词的系数为 $s^{g+4}$。因此最终记忆为 $1$ 的边缘概率至少为 $s^{2g+8}>0$，而所选事件要求记忆为 $0$，所以
$$
p_g\le\Pr(M=0)=1-\Pr(M=1)\le1-s^{2g+8}<1.
$$
这个边缘概率下界来自联合向量的正交基展开，无需测量保留的端点。归一化后，$\theta_g$ 为正、迹为 $1$，其像恰为 $\mathbb Cv_g$，所以密度秩为 $1$。

现证明这种纯密度不可能具有有限凸乘积分解。设 $\psi=v_g/\sqrt{p_g}$，并反设 $|\psi\rangle\langle\psi|=\sum_a\lambda_a\sigma_a\otimes\tau_a$。对每个二维密度作有限谱分解，再展开张量积并删去零权重项，便得到
$$
|\psi\rangle\langle\psi|
=\sum_{b=1}^{N}q_b|a_b\otimes b_b\rangle\langle a_b\otimes b_b|,
\qquad q_b>0,\qquad\sum_{b=1}^{N}q_b=1,
$$
其中 $a_b,b_b$ 为各自空间中的单位向量，$N$ 有限。对任意 $z\perp\psi$ 测试二次型，
$$
0=\sum_{b=1}^{N}q_b\,|\langle z,a_b\otimes b_b\rangle|^2.
$$
每项非负，故每个正权重乘积向量都与全部 $\psi^\perp$ 正交，从而属于同一条射线 $\mathbb C\psi$。由于至少有一个正权重项，$\psi$ 本身必为乘积向量。非零乘积向量的系数矩阵为两个非零列向量的外积 $ab^{\mathsf T}$，秩为 $1$；但 $\psi$ 的系数矩阵为 $C_g/\sqrt{p_g}$，其行列式不为零，秩为 $2$，矛盾。因此 $\theta_g$ 不可分。上述论证使用的是两个完整输出因子的张量分割；合法词集只规定联合向量的支撑，不另给合法支撑赋予张量分解。

最后，$\{|\varepsilon\rangle\otimes|k\rangle\}_{\varepsilon,k}$ 是全部被测因子 $H_g\otimes M$ 的正交标准基。各局部投影作用于互不相同的因子，故彼此交换，并满足 $\sum_{\varepsilon,k}Q_{\varepsilon,k}=I$。按此基展开实际 $\Xi_{g+2}$，其每个端点系数向量就是 $v_{\varepsilon,k}$；在 $H_g,M$ 上取偏迹时，不同基指标的交叉项消失，遂得
$$
\operatorname{Tr}_{H_g,M}|\Xi_{g+2}\rangle\langle\Xi_{g+2}|
=\sum_{\varepsilon,k}|v_{\varepsilon,k}\rangle\langle v_{\varepsilon,k}|.
$$
取迹给全部联合 Born 概率之和为 $1$，对正概率项再归一化即得陈述中的加权平均。这个恒等式对所有结果求和；归一化分支的均匀平均或仅对所选成功结果作平均，均不是此偏迹恒等式。

令 $P_0=|m_0\rangle\langle m_0|$。由命题 130.1，$\operatorname{Tr}_M|\Xi_{g+2}\rangle\langle\Xi_{g+2}|=\rho_{g+2}=\Gamma_{g+2}(P_0)$。因而在相同的输出分组下，$\Theta_g=\operatorname{Tr}_{H_g}\rho_{g+2}$ 正是命题 133.1 中取 $X=P_0$、$r=0$、$a=b=1$ 的 $\theta^{P_0}_{0;1,g,1}$。该命题对 $g\ge1$ 给出完整 $B_L\mid B_R$ 分割上的有限凸乘积态分解，故这里同一纯边界族的 $\Theta_g$ 可分。

可分性的量词是存在一个有限凸乘积态分解，并不要求一个密度的每个纯态系综都由乘积向量组成。因此，对 $g\ge1$，可依据完整经典测量记录选择正概率的纠缠分支 $\theta_g$，与忘却全部记录后得到可分的 Born 平均 $\Theta_g$ 相容。证毕。

<a id="entry-618"></a>

## 追加锚（本行以下为增补区）

<a id="section-135"></a>

## 135. 指定纠缠分支的联合概率与固定乘积态极限

**命题 135.1（有限间隔纠缠、消失的联合概率与固定端点极限）。** 沿用命题 134.1 的纯边界与生成器：
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1).
$$
对每个整数 $g\ge0$，从初始活动记忆 $m_0$ 恰好生成 $g+2$ 个输出，保留第一个及最后一个已发出的 qubit $L,R$；左端点之前没有被丢弃的输出前缀。假设可访问全部内部输出的测量记录及最终活动记忆：在每个内部输出的正交基 $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$ 中选择结果 $+$，在最终活动记忆的计算基中选择结果 $0$。此处选中的记忆向量是 $|0\rangle$，不是非正交记忆标签 $m_0$；两个端点始终都是已发出的输出。所有 $B_L\otimes B_R$ 通过各自带标签的计算基识别为同一个固定空间 $\mathbb C^2\otimes\mathbb C^2$。

以命题 134.1 的完整联合向量 $\Xi_{g+2}$ 定义
$$
v_g=(I_{B_L}\otimes\langle+|^{\otimes g}\otimes I_{B_R}\otimes\langle0|)\Xi_{g+2}
=\operatorname{vec}_{LR}(C_g),\qquad
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1 C(i,j)|i\rangle_L\otimes|j\rangle_R.
$$
$g=0$ 时内部 bra 是空张量积的恒等收缩。矩阵的行指标为 $L$ 位值，列指标为 $R$ 位值。记 $\operatorname{adj}(A)$ 为共轭转置，$\operatorname{outer}(x)=|x\rangle\langle x|$，并在本命题内令
$$
p_g=\|v_g\|^2=\operatorname{Tr}(C_g\operatorname{adj}(C_g)),\qquad
\psi_g=\frac{v_g}{\sqrt{p_g}},\qquad
\theta_g=\operatorname{outer}(\psi_g).
$$
这里 $p_g$ 是上述整个记录的联合 Born 概率，包含最终记忆结果 $0$ 的概率，不是预先条件于记忆成功后的概率，也不是命题 131.1 的记忆混合参数；$\theta_g$ 只表示固定端点空间上的选中密度。命题 134.1 已给出
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
\kappa_g=\frac{s^{g+3}}{(\sqrt2)^g},\qquad
C_g=\kappa_gJ^{g+1},\qquad \det C_g\ne0,\qquad 0<p_g<1.
$$

令
$$
\mathrm{den}=1+\alpha^2,\qquad
u_+=\frac{|0\rangle+\alpha|1\rangle}{\sqrt{\mathrm{den}}},\qquad
u_-=\frac{-\alpha|0\rangle+|1\rangle}{\sqrt{\mathrm{den}}},\qquad
e_+=u_+\otimes u_+,\qquad e_-=u_-\otimes u_-,
$$
$$
\varepsilon_g=(-1)^{g+1},\qquad t_g=\alpha^{2g+2},\qquad
b=\frac1{2\alpha},\qquad r_g=\kappa_g\alpha^{-g-1}>0.
$$
则 $u_+,u_-$ 是实正交单位向量，且有固定基展开
$$
C_g=r_g\bigl(\operatorname{outer}(u_+)+\varepsilon_gt_g\operatorname{outer}(u_-)\bigr),\qquad
\psi_g=\frac{e_++\varepsilon_gt_ge_-}{\sqrt{1+t_g^2}},\qquad
r_g^2=\alpha b^g.
$$
相对符号在偶数 $g$ 时为负，在奇数 $g$ 时为正。联合概率的精确式为
$$
p_g=\frac{\alpha^{g+3}}{2^g}
\bigl(\alpha^{-2g-2}+\alpha^{2g+2}\bigr)
=\alpha b^g\bigl(1+\alpha^{4g+4}\bigr).
$$
两端约化密度 $\operatorname{Tr}_{B_R}\theta_g$、$\operatorname{Tr}_{B_L}\theta_g$ 在各自的 $u_+,u_-$ 基下具有相同的两个特征值
$$
w_+=\frac1{1+t_g^2},\qquad w_-=\frac{t_g^2}{1+t_g^2}.
$$
每个有限 $g$ 下二者均为正；非负 Schmidt 系数是 $\sqrt{w_+},\sqrt{w_-}$。因此 $\theta_g$ 的密度算子秩为 $1$，而系数矩阵及两端约化密度的秩均为 $2$，$\theta_g$ 对完整 $B_L\mid B_R$ 分割不可分。

对有限维矩阵采用迹范数及密度间迹距离
$$
\operatorname{traceNorm}(A)=\operatorname{Tr}\sqrt{\operatorname{adj}(A)A},\qquad
D(\rho,\sigma)=\frac12\operatorname{traceNorm}(\rho-\sigma),
$$
其中平方根取唯一正半定平方根，故其迹为实数。这与 [FiniteTraceDistance 的 traceNorm、traceDistance](../../../../D5/S3/Quantum/Foundation/FiniteTraceDistance.lean) 的约定一致。令与 $g$ 无关的纯乘积密度为
$$
\Pi_+=\operatorname{outer}(e_+)
=\operatorname{outer}(u_+)\otimes\operatorname{outer}(u_+).
$$
则
$$
D(\theta_g,\Pi_+)=\frac{t_g}{\sqrt{1+t_g^2}},\qquad
0<D(\theta_g,\Pi_+)\le\alpha^{2g+2},
$$
并且沿全部非负整数指标有
$$
0<p_g\le3\alpha^3b^g\longrightarrow0,\qquad
w_-\longrightarrow0,\qquad
D(\theta_g,\Pi_+)\longrightarrow0.
$$
故这个指定分支在每个有限间隔仍纠缠，同时联合成功概率趋零，密度在固定四维端点空间的迹距离下趋于一个固定纯乘积态。上述距离针对指定的 $\Pi_+$，不是对可分密度的最小化，也不是对所有可分密度的距离下界。

证明。由 $\alpha+\alpha^2=1$，有 $1/2<\alpha<1$ 及 $1+\alpha=\alpha^{-1}$。向量 $u_+,u_-$ 的范数平方均为 $1$，内积为 $(-\alpha+\alpha)/\mathrm{den}=0$。直接矩阵乘法给出
$$
J\begin{pmatrix}1\\\alpha\end{pmatrix}
=\begin{pmatrix}1+\alpha\\1\end{pmatrix}
=\alpha^{-1}\begin{pmatrix}1\\\alpha\end{pmatrix},\qquad
J\begin{pmatrix}-\alpha\\1\end{pmatrix}
=\begin{pmatrix}1-\alpha\\-\alpha\end{pmatrix}
=-\alpha\begin{pmatrix}-\alpha\\1\end{pmatrix}.
$$
这两个特征对亦见 [FibonacciEigen 的 fibonacci_substitution_spec](../../../../D5/S1/Scale/FibonacciEigen.lean)：其中扩张向量为 $(\alpha^{-1},1)$，收缩向量为 $(-\alpha,1)$，分别乘以 $\alpha/\sqrt{\mathrm{den}}$、$1/\sqrt{\mathrm{den}}$ 即为这里的 $u_+,u_-$。因它们构成二维空间的正交单位基，谱分解给
$$
J^{g+1}=\alpha^{-g-1}\operatorname{outer}(u_+)
+(-\alpha)^{g+1}\operatorname{outer}(u_-).
$$
将此式代入命题 134.1 的 $C_g=\kappa_gJ^{g+1}$，提出正因子 $r_g$，即得所述 $C_g$ 展开。

按上述行列指标约定，对一般复向量 $u$，
$$
\operatorname{vec}_{LR}(\operatorname{outer}(u))
=u\otimes\overline u,
$$
其中横线表示计算基中的逐坐标共轭。这里 $u_+,u_-$ 的坐标全为实数，才有 $\operatorname{vec}_{LR}(\operatorname{outer}(u_\pm))=e_\pm$。由局部正交性，$e_+,e_-$ 也是正交单位向量，故
$$
v_g=r_g(e_++\varepsilon_gt_ge_-),\qquad
p_g=r_g^2(1+t_g^2),\qquad
\psi_g=\frac{e_++\varepsilon_gt_ge_-}{\sqrt{1+t_g^2}}.
$$
因 $s^2=\alpha$，
$$
r_g^2=\frac{s^{2g+6}}{2^g}\alpha^{-2g-2}
=\frac{\alpha^{1-g}}{2^g}=\alpha b^g,
$$
代入 $p_g$ 即得两个概率闭式。归一化因子 $(\sqrt2)^{-g}$ 来自每个内部投影 bra；最终记忆的 $\langle0|$ 已在 $C_g$ 中，未作任何记忆成功条件化。此计算只使用联合向量的 Born 范数，不假设各结果等概率或相互独立。

将纯密度展开为
$$
\theta_g=\frac{
\operatorname{outer}(e_+)+t_g^2\operatorname{outer}(e_-)
+\varepsilon_gt_g\bigl(|e_+\rangle\langle e_-|+|e_-\rangle\langle e_+|\bigr)
}{1+t_g^2}.
$$
在右端取偏迹时，交叉项分别乘以 $\langle u_-,u_+\rangle$、$\langle u_+,u_-\rangle$，均为零；对角项乘以相应单位向量的范数平方。因此
$$
\operatorname{Tr}_{B_R}\theta_g
=w_+\operatorname{outer}(u_+)_L+w_-\operatorname{outer}(u_-)_L.
$$
在左端取偏迹同理得到
$$
\operatorname{Tr}_{B_L}\theta_g
=w_+\operatorname{outer}(u_+)_R+w_-\operatorname{outer}(u_-)_R.
$$
$t_g>0$ 给两个正特征值。带符号的固定基展开中，把 $\varepsilon_g$ 吸收到右端第二个局部向量，得到真正的非负 Schmidt 展开
$$
\psi_g=\sqrt{w_+}\,u_+\otimes u_+
+\sqrt{w_-}\,u_-\otimes(\varepsilon_gu_-).
$$
每侧两个局部向量仍正交归一，故 Schmidt 秩为 $2$；不可分性亦与命题 134.1 的非零行列式结论一致。整个密度仍是一个单位向量的外积，故秩为 $1$。相对符号虽在两端约化谱中消失，却仍保留在 $\theta_g$ 的交叉项中。

在有序正交基 $(e_+,e_-)$ 所张成的子空间上，差 $\theta_g-\Pi_+$ 的矩阵为
$$
\frac1{1+t_g^2}
\begin{pmatrix}
-t_g^2&\varepsilon_gt_g\\
\varepsilon_gt_g&t_g^2
\end{pmatrix},
$$
并在其正交补上为零。这个实对称块的迹为零，行列式为 $-t_g^2/(1+t_g^2)$，故两个特征值恰为
$$
\lambda_+=\frac{t_g}{\sqrt{1+t_g^2}},\qquad
\lambda_-=-\frac{t_g}{\sqrt{1+t_g^2}}.
$$
对 Hermitian 矩阵，$\operatorname{adj}(A)A=A^2$；在正交特征基中，其正半定平方根的特征值为原特征值的绝对值。因此取以上两个绝对值之和的一半，便得到
$$
D(\theta_g,\Pi_+)=\frac{t_g}{\sqrt{1+t_g^2}}\le t_g.
$$
这直接计算了两个已归一化密度的差，不使用保迹映射的压缩性去处理非线性的分支归一化。

边界 $g=0$ 的内部测量为空，最终记忆测量仍在。由 $J$ 的三个非零矩阵元，
$$
C_0=s^3J,\qquad p_0=3\alpha^3,\qquad
\psi_0=\frac{|00\rangle+|01\rangle+|10\rangle}{\sqrt3}.
$$
又因 $J^2=\begin{pmatrix}2&1\\1&1\end{pmatrix}$，
$$
C_1=\frac{s^4}{\sqrt2}\begin{pmatrix}2&1\\1&1\end{pmatrix},\qquad
p_1=\frac{7\alpha^4}{2},\qquad
\psi_1=\frac{2|00\rangle+|01\rangle+|10\rangle+|11\rangle}{\sqrt7}.
$$
两式中的概率都保留了最终记忆结果 $0$ 的概率因子。

最后，由 $1/2<\alpha<1$ 得 $0<b<1$。又由 $\alpha^2=1-\alpha$，可得 $\alpha^4=2-3\alpha$，从而
$$
\alpha(1+\alpha^4)=3\alpha(1-\alpha)=3\alpha^3.
$$
对所有 $g\ge0$，$\alpha^{4g+4}\le\alpha^4$，所以
$$
0<p_g=\alpha b^g(1+\alpha^{4g+4})\le3\alpha^3b^g,\qquad
0<w_-\le t_g^2=\alpha^{4g+4},\qquad
0<D(\theta_g,\Pi_+)\le\alpha^{2g+2}.
$$
由于 $b$、$\alpha^2$、$\alpha^4$ 均严格介于 $0$ 与 $1$，三个右端是趋零的几何序列；夹逼即给沿全部整数指标的三个极限，而非只沿某个奇偶子列的极限。尤其不存在对所有 $g$ 都成立的联合成功概率正下界，也不存在到这个固定 $\Pi_+$ 的距离正下界；这不改变任何有限 $g$ 下的精确非零性及纠缠性。

这里比较的是每个有限 $g$ 的正概率条件态在同一端点空间内的极限，不是增长的完整输出空间中的极限，也没有对一个概率为零的无限测量事件定义条件态。命题 134.1 的 $\Theta_g$ 仍是对完整结果集按联合 Born 概率求和的无条件端点密度，与选中的 $\theta_g$ 为不同对象。证毕。

<a id="entry-620"></a>

## 追加锚（本行以下为增补区）

<a id="section-136"></a>

## 136. 最终记忆未读时的内部选择与有限间隔端点纠缠

**命题 136.1（只选择内部全加结果的秩二纠缠态）。** 沿用命题 130.1、134.1、135.1 的同一个纯边界生成器，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1).
$$
两份二维空间均取正交标准基。记 $\operatorname{adj}(A)$ 为共轭转置，$\operatorname{outer}(x)=|x\rangle\langle x|$，并令
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad T_0=I_M,\qquad
T_{n+1}=(I_{H_n}\otimes T)T_n,\qquad \Xi_n=T_nm_0.
$$
对每个整数 $g\ge0$，恰好生成 $g+2$ 个输出，按输出在前、活动记忆在后的次序分组为
$$
B_L\otimes H_g\otimes B_R\otimes M.
$$
$L,R$ 分别为第一个、最后一个已发出的 qubit，左端点之前没有被忽略的前缀，初始记忆始终为纯向量 $m_0$。假设可以在每个内部输出上测量正交基
$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
|-\rangle=\frac{|0\rangle-|1\rangle}{\sqrt2},
$$
访问这些内部结果并选择全部为 $+$ 的记录。最终活动记忆完全以偏迹忽略，不测量它，也不选择其计算基结果 $0$ 或记忆向量 $m_0$。两个端点均保留，可分性取完整 $B_L\mid B_R$ 分割：密度可分是指它有有限凸乘积密度分解。

内部全加记录收缩后的未归一化向量为
$$
\chi_g=(I_{B_L}\otimes\langle+|^{\otimes g}\otimes I_{B_R}\otimes I_M)\Xi_{g+2}
\in B_L\otimes B_R\otimes M,
$$
其中 $g=0$ 的内部 bra 是空张量积上的恒等收缩。沿用命题 134.1、135.1 的系数矩阵，定义
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
\kappa_g=\frac{s^{g+3}}{(\sqrt2)^g},\qquad C_g=\kappa_gJ^{g+1},\qquad
E_0=\begin{pmatrix}1&0\\0&0\end{pmatrix},
$$
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C(i,j)|i\rangle_L\otimes|j\rangle_R,
\qquad \|C\|_F^2=\operatorname{Tr}(C\operatorname{adj}(C)).
$$
行指标为 $L$ 位值，列指标为 $R$ 位值，故右乘 $E_0$ 选择最后一个已发出位值为 $0$ 的列。则
$$
\chi_g=\operatorname{vec}_{LR}(C_g)\otimes|0\rangle
+s\operatorname{vec}_{LR}(C_gE_0)\otimes|1\rangle,
$$
$$
Q_g:=\operatorname{Tr}_M\operatorname{outer}(\chi_g)
=\operatorname{outer}(\operatorname{vec}_{LR}(C_g))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_gE_0)),
$$
$$
q_g:=\operatorname{Tr}Q_g
=\|C_g\|_F^2+\alpha\|C_gE_0\|_F^2,\qquad
0<q_g\le1,\qquad \theta_g^{\mathrm{unread}}:=\frac{Q_g}{q_g}.
$$
这里 $q_g$ 是只含内部全加记录的 Born 概率，$\theta_g^{\mathrm{unread}}$ 是最终记忆未读的实际条件密度；它们分别不同于命题 134.1、135.1 中额外选择最终记忆结果 $0$ 的 $p_g$ 与纯条件密度 $\theta_g$。对每个有限 $g\ge0$，$\theta_g^{\mathrm{unread}}$ 的算子秩为 $2$，且在完整 $\mathbb C^2\otimes\mathbb C^2$ 上纠缠。空内部记录满足
$$
q_0=1,\qquad \alpha^3(3+2\alpha)=1,\qquad
Q_0=\theta_0^{\mathrm{unread}}=\Gamma_2(P_0)=G_0,
\qquad P_0=\operatorname{outer}(m_0),
$$
其中 $\Gamma_2$ 与 $G_0$ 是命题 132.1 的同名对象。

对全部内部记录 $e\in\{+,-\}^g$，令 $|e\rangle=|e_1\rangle\otimes\cdots\otimes|e_g\rangle$，并在同一个相关联合向量上定义
$$
\chi_e=(I_{B_L}\otimes\langle e|\otimes I_{B_R}\otimes I_M)\Xi_{g+2},\qquad
Q_e=\operatorname{Tr}_M\operatorname{outer}(\chi_e),\qquad q_e=\operatorname{Tr}Q_e.
$$
则完整结果的 Born 平均满足
$$
\overline\Theta_g:=\sum_{e\in\{+,-\}^g}Q_e
=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2})
=\sum_{\substack{e\in\{+,-\}^g\\q_e>0}}q_e\frac{Q_e}{q_e},
\qquad \sum_e q_e=1.
$$
未归一化求和包含全部记录，零概率项只从归一化表达式中省去。对 $g\ge1$，$\overline\Theta_g$ 可分；$g=0$ 时它等于上述纠缠密度 $G_0$。

证明。令 $W_n$ 为不含相邻 $11$ 的长度 $n$ 二进制词集，$W_n^0$ 为其中末位为 $0$ 的词集。命题 130.1 的实际联合态两列展开给
$$
\Xi_n=s^{n+1}\sum_{w\in W_n}|w\rangle\otimes|0\rangle
+s^{n+2}\sum_{w\in W_n^0}|w\rangle\otimes|1\rangle
\qquad(n\ge1),\qquad \|\Xi_n\|=1.
$$
取 $n=g+2$，在两列上施加同一组归一化内部 bra。对每个内部计算基词 $u$，有 $\langle+|^{\otimes g}|u\rangle=(\sqrt2)^{-g}$。因此第一列的端点系数为
$$
\kappa_g\#\{u\in\{0,1\}^g:(i,u,j)\in W_{g+2}\}
=C_g(i,j),
$$
这里最后一个等号正是命题 134.1 的相容矩阵计数 $(J^{g+1})_{ij}$。第二列仍只对末位为 $0$ 的合法词求和，故其系数为
$$
\frac{s^{g+4}}{(\sqrt2)^g}
\#\{u\in\{0,1\}^g:(i,u,j)\in W_{g+2},\ j=0\}
=sC_g(i,j)\,\mathbf1_{\{j=0\}}
=s(C_gE_0)(i,j).
$$
这同时给出所述 $\chi_g$，包括只有空内部词的 $g=0$。此处把最终记忆写在计算基中只是同一向量的坐标展开，不是额外实施一次记忆测量；两列均保留原振幅，未分别归一化。正交记忆基的交叉项在偏迹中消失，而第二列的平方系数为 $s^2=\alpha$，遂得 $Q_g$ 与 $q_g$ 的公式。内部 bra 的因子 $1/\sqrt2$ 是内积，不假设各结果等概率或独立。

由 $\det J=-1$、$\kappa_g>0$，
$$
\det C_g=\kappa_g^2(-1)^{g+1}\ne0.
$$
故 $C_g$ 可逆且非零，$q_g\ge\|C_g\|_F^2>0$。内部全加事件在完整联合空间上的正交投影是
$$
\mathsf P_g=I_{B_L}\otimes\operatorname{outer}(|+\rangle^{\otimes g})
\otimes I_{B_R}\otimes I_M.
$$
于是
$$
q_g=\|\chi_g\|^2=\langle\Xi_{g+2},\mathsf P_g\Xi_{g+2}\rangle\le1,
$$
因为 $\Xi_{g+2}$ 为单位向量。$Q_g$ 为正半定，除以其正迹得到密度。$g=0$ 时 $\mathsf P_0=I$，故 $q_0=1$。直接由 $C_0=s^3J$，在字典序 $00,01,10,11$ 下有
$$
Q_0=\alpha^3
\begin{pmatrix}
1+\alpha&1&1+\alpha&0\\
1&1&1&0\\
1+\alpha&1&1+\alpha&0\\
0&0&0&0
\end{pmatrix}
=\begin{pmatrix}
\alpha^2&\alpha^3&\alpha^2&0\\
\alpha^3&\alpha^3&\alpha^3&0\\
\alpha^2&\alpha^3&\alpha^2&0\\
0&0&0&0
\end{pmatrix}=G_0.
$$
此处 $\alpha^3(1+\alpha)=\alpha^2$；取迹给 $\alpha^3(3+2\alpha)=2\alpha^2+\alpha^3=1$，最后一步用 $\alpha^3=2\alpha-1$。这与命题 132.1 的无条件首两位密度 $\Gamma_2(P_0)$ 完全一致。

现以一个局部合同变换检验混合态可分性。设
$$
A_g=C_g^{-1},\qquad F_g=A_g\otimes I_{B_R},\qquad
\phi=|00\rangle+|11\rangle.
$$
按行优先的向量化约定，对任意两个二阶矩阵 $A,C$，逐坐标展开有
$$
(A\otimes I_{B_R})\operatorname{vec}_{LR}(C)
=\sum_{k,j}\left(\sum_i A(k,i)C(i,j)\right)|k\rangle_L\otimes|j\rangle_R
=\operatorname{vec}_{LR}(AC).
$$
故 $A_gC_g=I$、$A_gC_gE_0=E_0$ 给出
$$
F_gQ_g\operatorname{adj}(F_g)=S,\qquad
S:=\operatorname{outer}(\phi)+\alpha\operatorname{outer}(|00\rangle),
$$
$$
F_g\theta_g^{\mathrm{unread}}\operatorname{adj}(F_g)=\frac{S}{q_g},\qquad
\operatorname{Tr}\left(\frac{S}{q_g}\right)=\frac{2+\alpha}{q_g}>1.
$$
这里 $S/q_g$ 是未归一化正算子，不将分母换成 $2+\alpha$。$F_g$ 只用于代数合同变换；本命题没有实施此滤波，也不赋予未缩放的逆矩阵任何确定性或迹不增操作的资格。

沿用命题 132.1 的偏转置约定，在右端计算基上定义并线性延伸
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|.
$$
在相同字典序下直接得到
$$
\operatorname{PT}_R(S)=
\begin{pmatrix}
1+\alpha&0&0&0\\
0&0&1&0\\
0&1&0&0\\
0&0&0&1
\end{pmatrix}.
$$
单位向量 $v=(|01\rangle-|10\rangle)/\sqrt2$ 满足
$$
\langle v,\operatorname{PT}_R(S)v\rangle=-1,\qquad
\left\langle v,\operatorname{PT}_R\left(\frac{S}{q_g}\right)v\right\rangle=-\frac1{q_g}<0.
$$

反设实际密度可分，即存在有限分解
$$
\theta_g^{\mathrm{unread}}=\sum_{a=1}^N\lambda_a D_a\otimes E_a,
\qquad \lambda_a\ge0,\qquad \sum_{a=1}^N\lambda_a=1,
$$
其中 $D_a,E_a$ 为各自端点上的密度。局部合同变换及偏转置的线性性给
$$
\operatorname{PT}_R\bigl(F_g\theta_g^{\mathrm{unread}}\operatorname{adj}(F_g)\bigr)
=\sum_{a=1}^N\lambda_a
\bigl(A_gD_a\operatorname{adj}(A_g)\bigr)\otimes E_a^{\mathsf T}.
$$
第一因子正半定，因为在任意 $x$ 上的二次型等于 $\langle\operatorname{adj}(A_g)x,D_a\operatorname{adj}(A_g)x\rangle\ge0$。若 $E_a=\sum_b\mu_b\operatorname{outer}(z_b)$ 是谱分解，$\mu_b\ge0$，则
$$
E_a^{\mathsf T}=\sum_b\mu_b\operatorname{outer}(\overline{z_b})\ge0,
$$
其中共轭逐计算基坐标取值。正半定因子的张量积及其非负有限和仍正半定，因此上式必须正半定，与 $v$ 上严格负的二次型矛盾。此论证只用可分态偏转置为正的必要性，且在未归一化的可分正半定锥中成立；不调用其逆命题，不把偏转置视为物理通道。由此对每个有限 $g$ 证明实际密度纠缠。

向量 $\phi$ 与 $|00\rangle$ 线性无关且 $\alpha>0$，所以 $S$ 的像是它们张成的二维空间。可逆合同变换及除以 $q_g>0$ 均保持秩，故 $\operatorname{rank}\theta_g^{\mathrm{unread}}=2$。系数矩阵的可逆性在此用来构造合同变换，没有对混合态使用纯态的 Schmidt 判据。

最后，$\{|e\rangle:e\in\{+,-\}^g\}$ 是 $H_g$ 的正交标准基，其投影之和为 $I_{H_g}$。对同一个 $\Xi_{g+2}$ 在此基中展开，再取内部空间的偏迹，得到 $\sum_e\operatorname{outer}(\chi_e)$；继续取 $M$ 的偏迹即得
$$
\sum_e Q_e=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2})=\overline\Theta_g.
$$
取迹给 $\sum_eq_e=1$。各 $Q_e$ 正半定，故 $q_e=0$ 蕴含 $Q_e=0$；仅对正概率项归一化即得陈述中的加权平均，不能用归一化分支的等权平均替代。

由命题 130.1 的 $\operatorname{Tr}_M\operatorname{outer}(\Xi_{g+2})=\Gamma_{g+2}(P_0)$，此平均正是命题 133.1 中 $X=P_0$、$r=0$、$a=b=1$ 的 $\theta^{P_0}_{0;1,g,1}$。因此对 $g\ge1$ 直接应用该命题得到完整端点分割上的可分性；其假设明确要求非空间隔。$g=0$ 时平均只有空记录一项，等于 $G_0$，并已证纠缠。可分性要求存在一个有限凸乘积密度分解，不要求同一密度的每个系综都由可分分量组成，故可分平均与所选的纠缠分量相容。

本命题给出的是上述纯边界、内部测量及全加记录选择下，对每个有限间隔都纠缠的一种指定协议；最终记忆访问不是该协议的假设。它不对所有测量记录、任意混合初态或所有协议量化，不给出普遍最小访问条件、最优纠缠、确定性交付、信号传递、物理距离或时间的结论，也不给出关于 $g$ 的统一纠缠量正下界。证毕。

<a id="entry-622"></a>

## 追加锚（本行以下为增补区）

<a id="section-137"></a>

## 137. 未读最终记忆时任意局部秩一内部记录的端点分类

**命题 137.1（正概率记录的乘积与秩二纠缠二分）。** 取命题 130.1 的纯边界生成器及命题 136.1 的向量化约定：
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad
\Xi_0=m_0,\qquad \Xi_{n+1}=(I_{H_n}\otimes T)\Xi_n.
$$
两份二维空间均取正交标准基。对任意整数 $g\ge0$，恰好生成 $g+2$ 个输出，按发出次序分组为
$$
B_L\otimes H_g\otimes B_R\otimes M.
$$
$L,R$ 是第一个和最后一个已发出的 qubit，左端点之前没有被忽略的前缀。对第 $k$ 个内部输出，选取单位复向量
$$
|\eta_k\rangle=\eta_{k,0}|0\rangle+\eta_{k,1}|1\rangle,
\qquad |\eta_{k,0}|^2+|\eta_{k,1}|^2=1\quad(1\le k\le g),
$$
其秩一投影为该位置某个固定局部正交基测量的一个结果。记记录为 $\eta=(\eta_1,\ldots,\eta_g)$；只对内部输出作这些测量及结果选择，生成过程没有反馈、记忆测量或重置，最终活动记忆以偏迹忽略。两个端点保留完整空间 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$；可分密度指此分割上的有限凸乘积密度和，非可分密度称为纠缠态。

令 $\operatorname{adj}$ 表示共轭转置，$\operatorname{outer}(v)=v\operatorname{adj}(v)$，并定义
$$
D_k=\operatorname{diag}(\overline{\eta_{k,0}},\overline{\eta_{k,1}}),\qquad
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
E_0=\operatorname{diag}(1,0),
$$
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1 C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad \|C\|_F^2=\sum_{i,j=0}^1|C_{ij}|^2,
$$
$$
C_\eta=s^{g+3}JD_1JD_2\cdots JD_gJ,\qquad C_\varnothing=s^3J.
$$
其中矩阵因子从左到右按内部位置 $1,\ldots,g$ 排列，所有空乘积取一。实际记录收缩及其最终记忆偏迹满足
$$
\begin{aligned}
\chi_\eta
&=(I_{B_L}\otimes\langle\eta_1|\otimes\cdots\otimes\langle\eta_g|
\otimes I_{B_R}\otimes I_M)\Xi_{g+2}\\
&=\operatorname{vec}_{LR}(C_\eta)\otimes|0\rangle
+s\operatorname{vec}_{LR}(C_\eta E_0)\otimes|1\rangle,\\
Q_\eta&:=\operatorname{Tr}_M\operatorname{outer}(\chi_\eta)
=\operatorname{outer}(\operatorname{vec}_{LR}(C_\eta))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_\eta E_0)),\\
q_\eta&:=\operatorname{Tr}Q_\eta
=\|C_\eta\|_F^2+\alpha\|C_\eta E_0\|_F^2\in[0,1].
\end{aligned}
$$
$q_\eta$ 是实际内部投影的 Born 概率，且 $q_\eta=0$ 当且仅当 $C_\eta=0$；只在 $q_\eta>0$ 时定义条件密度 $\theta_\eta=Q_\eta/q_\eta$。有
$$
\det C_\eta=(-1)^{g+1}\alpha^{g+3}
\prod_{k=1}^g\overline{\eta_{k,0}\eta_{k,1}}.
$$
每个正概率记录恰属于以下一类。

第一，若至少一个内部向量有零计算基分量，则 $C_\eta$ 非零且秩为一。存在非零复系数列向量 $a,b\in\mathbb C^2$，使 $C_\eta=ab^{\mathsf T}$，其中 $\mathsf T$ 是普通转置。此时
$$
\theta_\eta=
\frac{\operatorname{outer}(a)}{\|a\|^2}\otimes
\frac{\operatorname{outer}(b)+\alpha\operatorname{outer}(E_0b)}
{\|b\|^2+\alpha|b_0|^2}.
$$
这是左因子为纯态的乘积密度，右因子不必为纯态。

第二，若所有内部向量的两个计算基分量均非零，则 $C_\eta$ 可逆，记录必有正概率，且 $\theta_\eta$ 是秩为二的纠缠密度。这包含 $g=0$ 的空记录；此时
$$
q_\varnothing=1,\qquad Q_\varnothing=\theta_\varnothing=G_0=\Gamma_2(P_0),
\qquad P_0=\operatorname{outer}(m_0),
$$
其中 $G_0$ 是命题 132.1 的纯边界相邻双位置密度。

对每个内部位置固定一个正交标准基 $\{|\eta_{k,0}^{\rm bas}\rangle,|\eta_{k,1}^{\rm bas}\rangle\}$，对全部记录 $e\in\{0,1\}^g$ 以上述定义取 $\eta_k=\eta_{k,e_k}^{\rm bas}$，并把所得算子及概率记为 $Q_e,q_e$。这个完整测量的平均为
$$
\overline\Theta_g:=\sum_{e\in\{0,1\}^g}Q_e
=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2})
=\sum_{\substack{e\in\{0,1\}^g\\q_e>0}}q_e\theta_e,
\qquad \sum_{e\in\{0,1\}^g}q_e=1.
$$
对 $g\ge1$，此平均由命题 133.1 可分；$g=0$ 时它等于纠缠密度 $G_0$。特别地，$g\ge1$ 时在所有内部位置测计算基，正概率记录恰为不含相邻 $11$ 的内部词，每个这样的记录均给乘积密度。若每个内部位置均测
$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
|-\rangle=\frac{|0\rangle-|1\rangle}{\sqrt2},
$$
则对每个 $g\ge0$，全部 $2^g$ 个记录均有正概率，均给秩二纠缠密度；这些概率和条件密度不要求彼此相等。

在混合选基记录中，任何含零分量的正概率记录仍给上述乘积密度。若恰有一个 $D_k$ 奇异，其余 $D_k$ 均可逆，则 $C_\eta$ 必为非零秩一矩阵，因而 $q_\eta>0$；两个或更多奇异因子则可以使整个矩阵为零。具体地，$g=2$ 的计算基内部记录 $(|1\rangle,|1\rangle)$ 概率为零，$g=3$ 的记录 $(|0\rangle,|-\rangle,|0\rangle)$ 也恰有零概率，后者即使存在合法计算基路径仍相消。

证明。令 $W_n$ 为不含相邻 $11$ 的长度 $n$ 二进制词集。命题 130.1 从实际 $T$ 递推所得的两个记忆列为
$$
\Xi_n=s^{n+1}\sum_{w\in W_n}|w\rangle\otimes|0\rangle
+s^{n+2}\sum_{\substack{w\in W_n\\w_{n-1}=0}}|w\rangle\otimes|1\rangle
\quad(n\ge1),\qquad \|\Xi_n\|=1.
$$
取 $n=g+2$。对任意内部计算基词 $u=(u_1,\ldots,u_g)$，复 bra 收缩的权重是
$$
(\langle\eta_1|\otimes\cdots\otimes\langle\eta_g|)|u\rangle
=\prod_{k=1}^g\overline{\eta_{k,u_k}}.
$$
置 $x_0=i$、$x_k=u_k$（$1\le k\le g$）、$x_{g+1}=j$。由 $J_{ab}=0$ 恰当 $a=b=1$，第一记忆列在端点 $i,j$ 上的系数为
$$
\begin{aligned}
s^{g+3}\sum_{u\in\{0,1\}^g}
\left(\prod_{t=0}^g J_{x_t,x_{t+1}}\right)
\left(\prod_{k=1}^g\overline{\eta_{k,u_k}}\right)
&=s^{g+3}(JD_1JD_2\cdots JD_gJ)_{ij}\\
&=(C_\eta)_{ij}.
\end{aligned}
$$
这是矩阵乘法对所有内部指标的求和：$D_k$ 的对角元在第 $k$ 个内部指标处插入，故次序是从左端点沿发出位置到右端点的 $D_1,\ldots,D_g$。$g=0$ 时求和只有空词，唯一边因子为 $J_{ij}$，仍给 $C_\varnothing=s^3J$。第二记忆列只允许末位 $j=0$，并多出一个 $s$，所以对全部 $i,j$，其系数为
$$
s(C_\eta)_{ij}\mathbf1_{\{j=0\}}=s(C_\eta E_0)_{ij}.
$$
因此得到所述 $\chi_\eta$。两个记忆列保留其原振幅；在正交记忆基中取偏迹消掉交叉项，以 $s^2=\alpha$ 得到 $Q_\eta$。它是正半定，取迹给 $q_\eta$ 的两个平方范数之和。该和为零当且仅当 $C_\eta=0$，此时 $\chi_\eta=0$、$Q_\eta=0$。

写 $|\eta\rangle=\bigotimes_{k=1}^g|\eta_k\rangle$，空张量积为 $H_0$ 的单位向量。实际内部事件的投影为
$$
\mathsf P_\eta=I_{B_L}\otimes\operatorname{outer}(|\eta\rangle)
\otimes I_{B_R}\otimes I_M.
$$
各局部向量单位化，故 $0\le\mathsf P_\eta\le I$，于是
$$
q_\eta=\|\chi_\eta\|^2
=\langle\Xi_{g+2},\mathsf P_\eta\Xi_{g+2}\rangle\in[0,1].
$$
这既证明概率的 Born 含义，也说明只可对正概率记录归一化，不能分别归一化两列再混合。$g=0$ 时 $\mathsf P_\varnothing=I$，所以 $q_\varnothing=1$；此时偏迹就是 $\Gamma_2(P_0)=G_0$，与命题 132.1、136.1 的相邻密度一致。

二阶矩阵的标量倍数在行列式中贡献标量的平方。由乘法性、$g+1$ 个 $J$ 因子及 $s^2=\alpha$，
$$
\begin{aligned}
\det C_\eta
&=(s^{g+3})^2(\det J)^{g+1}\prod_{k=1}^g\det D_k\\
&=\alpha^{g+3}(-1)^{g+1}
\prod_{k=1}^g\overline{\eta_{k,0}\eta_{k,1}}.
\end{aligned}
$$
由于 $\alpha>0$，这恰在至少一个计算基分量为零时消失。若 $q_\eta>0$ 且有这样的零分量，$C=C_\eta$ 非零且行列式为零，所以秩为一。选一个非零主元 $C_{i_*j_*}$，逐坐标定义
$$
a_i=C_{ij_*},\qquad b_j=\frac{C_{i_*j}}{C_{i_*j_*}}\quad(i,j\in\{0,1\}).
$$
秩一给出所有二阶子式关系
$$
C_{ij}C_{i_*j_*}=C_{ij_*}C_{i_*j}.
$$
故 $C_{ij}=a_ib_j$，且 $a_{i_*}\ne0$、$b_{j_*}=1$。这里是复系数的双线性分解 $C=ab^{\mathsf T}$，不对 $b$ 取共轭。由向量化定义及 $E_0^{\mathsf T}=E_0$，
$$
\operatorname{vec}_{LR}(C)=a\otimes b,\qquad
\operatorname{vec}_{LR}(CE_0)=a\otimes E_0b,
$$
$$
Q_\eta=\operatorname{outer}(a)\otimes
\bigl(\operatorname{outer}(b)+\alpha\operatorname{outer}(E_0b)\bigr),
\qquad q_\eta=\|a\|^2(\|b\|^2+\alpha|b_0|^2)>0.
$$
两个因子均为非零正半定算子；按其迹归一化得到陈述中的乘积密度，左因子的秩为一。右因子确实可以混合：取 $g=1$、$\eta_1=|0\rangle$，则
$$
C_\eta=s^4JE_0J=s^4\begin{pmatrix}1&1\\1&1\end{pmatrix}.
$$
可取 $a=s^4(1,1)^{\mathsf T}$、$b=(1,1)^{\mathsf T}$；右因子归一化前的矩阵为
$$
\begin{pmatrix}1+\alpha&1\\1&1\end{pmatrix},
$$
其行列式为 $\alpha>0$，所以归一化后仍秩二。

若每个分量均非零，则行列式非零，$C=C_\eta$ 可逆，且 $q_\eta\ge\|C\|_F^2>0$。直接应用命题 136.1 的局部合同论证：其中逐坐标恒等式
$$
(A\otimes I_{B_R})\operatorname{vec}_{LR}(C)=\operatorname{vec}_{LR}(AC)
$$
对任意复矩阵 $A,C$ 成立，并不要求矩阵为实。取
$$
F=C^{-1}\otimes I_{B_R},\qquad \phi=|00\rangle+|11\rangle,
\qquad S=\operatorname{outer}(\phi)+\alpha\operatorname{outer}(|00\rangle),
$$
便有
$$
FQ_\eta\operatorname{adj}(F)=S,\qquad
F\theta_\eta\operatorname{adj}(F)=\frac{S}{q_\eta},\qquad
\operatorname{Tr}\left(\frac{S}{q_\eta}\right)=\frac{2+\alpha}{q_\eta}.
$$
这是代数合同变换，不是本命题允许实施的操作；其归一化输入的像也不是单位迹密度。

命题 136.1 的可分正半定锥论证同样允许复系数：若 $X=\sum_r A_r\otimes B_r$ 且 $A_r,B_r\ge0$，则
$$
FX\operatorname{adj}(F)
=\sum_r(C^{-1}A_r\operatorname{adj}(C^{-1}))\otimes B_r
$$
仍是有限个正半定乘积之和。第一因子的非负性来自二次型；若 $B_r=\sum_t\mu_t\operatorname{outer}(z_t)$、$\mu_t\ge0$ 是谱分解，则
$$
B_r^{\mathsf T}=\sum_t\mu_t\operatorname{outer}(\overline{z_t})\ge0.
$$
所以在右计算基上取偏转置后，上述每个张量因子及有限和仍正半定。采用命题 132.1、136.1 的约定
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|,
$$
在字典序 $00,01,10,11$ 下已有
$$
\operatorname{PT}_R(S)=
\begin{pmatrix}
1+\alpha&0&0&0\\
0&0&1&0\\
0&1&0&0\\
0&0&0&1
\end{pmatrix},\qquad
v=\frac{|01\rangle-|10\rangle}{\sqrt2},\qquad
\langle v,\operatorname{PT}_R(S)v\rangle=-1.
$$
若 $\theta_\eta$ 可分，则 $Q_\eta=q_\eta\theta_\eta$ 也在该锥中，合同后的 $S$ 必有正半定偏转置，与此负二次型矛盾。因此 $\theta_\eta$ 纠缠。所用的仅是可分性的偏转置正性必要条件（Asher Peres，Separability Criterion for Density Matrices，Physical Review Letters 77，1413–1415，1996，[DOI:10.1103/PhysRevLett.77.1413](https://doi.org/10.1103/PhysRevLett.77.1413)），其复数情形已由上述谱分解落实。

若 $\lambda\operatorname{vec}_{LR}(C)+\mu\operatorname{vec}_{LR}(CE_0)=0$，向量化的单射性给 $C(\lambda I+\mu E_0)=0$。左乘 $C^{-1}$，比较两个对角元，得到 $\lambda=0$、$\lambda+\mu=0$，故 $\mu=0$。两向量线性无关，$\alpha>0$，于是 $Q_\eta$ 这两个正权重外积之和的像恰为它们张成的二维空间：其核是两向量的共同正交补。这证明 $\operatorname{rank}\theta_\eta=2$，并未对混合密度使用纯态的 Schmidt 判据。行列式的两种情形穷尽所有正概率记录，故分类成立。

现在证明完整测量的平均。各个局部基的正交完备性给
$$
\sum_{e_k=0}^1\operatorname{outer}(|\eta_{k,e_k}^{\rm bas}\rangle)=I_B,
\qquad
\sum_{e\in\{0,1\}^g}\operatorname{outer}(|\eta_e^{\rm bas}\rangle)=I_{H_g},
\qquad
|\eta_e^{\rm bas}\rangle=\bigotimes_{k=1}^g|\eta_{k,e_k}^{\rm bas}\rangle.
$$
将同一个 $\Xi_{g+2}$ 在这个内部正交基上展开，每个系数正是 $\chi_e$；取内部偏迹时，正交性消掉不同记录间的交叉项，因此
$$
\operatorname{Tr}_{H_g}\operatorname{outer}(\Xi_{g+2})
=\sum_e\operatorname{outer}(\chi_e).
$$
再取 $M$ 的偏迹即得 $\sum_eQ_e=\overline\Theta_g$，取迹得 $\sum_eq_e=\|\Xi_{g+2}\|^2=1$。零概率项已经证明为零算子，只在写成 $q_e\theta_e$ 时省去。由命题 130.1 的实际输出偏迹，这个平均恰为命题 133.1 的
$$
\overline\Theta_g=\theta^{P_0}_{0;1,g,1}\qquad(g\ge1),
$$
即纯边界 $X=P_0$、无前缀 $r=0$、左右块长 $a=b=1$、忽略 $g$ 个内部输出的态；其可分性直接由该命题得出。$g=0$ 的完整基只有空记录，平均为上面已识别的纠缠密度 $G_0$。

在计算基测量中，记录 $u\in\{0,1\}^g$ 的权重只选中该内部词。若 $u$ 含相邻 $11$，没有合法完整词含此内部片段，路径式处处为零；若 $u$ 不含相邻 $11$，完整词 $(0,u,0)$ 合法，因此 $(C_u)_{00}=s^{g+3}\ne0$。这证明正概率记录恰为合法内部词；当 $g\ge1$ 时，每个此类记录含零分量，故分类的第一项给出乘积密度。该论证的全乘积结论不含 $g=0$。在加减基中，每个局部向量的两分量均非零，故每条记录的行列式非零，分类的第二项适用于全部 $2^g$ 条记录，包括空记录。完整测量的权重始终是各自的 $q_e$；正交完备性只给它们的和为一，不给等概率或相同条件密度。

最后，单位向量有零分量时另一个分量非零，所以奇异的 $D_k$ 本身秩为一。若这样的因子恰有一个，把整个乘积写作 $U D_k V$，其中包含非零标量及所有其余因子的 $U,V$ 均可逆；左右乘可逆矩阵保持秩，故 $C_\eta$ 秩一且非零。对多个奇异因子，令 $E_1=\operatorname{diag}(0,1)$，则
$$
E_1JE_1=0,\qquad
C_{(|1\rangle,|1\rangle)}=s^5JE_1JE_1J=0.
$$
另令 $Z=\operatorname{diag}(1,-1)$，则
$$
JZJ=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
E_0JZJE_0=0,
$$
$$
C_{(|0\rangle,|-\rangle,|0\rangle)}
=\frac{s^6}{\sqrt2}JE_0JZJE_0J=0.
$$
第二个记录在每对端点 $i,j$ 上都有两个合法词 $(i,0,0,0,j)$ 与 $(i,0,1,0,j)$，其内部 bra 权重分别为 $1/\sqrt2$ 与 $-1/\sqrt2$，故等幅相消；最终记忆的两列同时为零。两例均由 $C_\eta=0$ 得到 $q_\eta=0$，不定义其条件密度。证毕。

<a id="entry-624"></a>

## 追加锚（本行以下为增补区）

<a id="section-138"></a>

## 138. 固定局部正交测量的平均端点 concurrence 与精确衰减界

**命题 138.1（未读最终记忆的分支凸顶与固定选基最优值）。** 沿用命题 130.1、137.1 的纯边界生成器，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad
\Xi_0=m_0,\qquad \Xi_{n+1}=(I_{H_n}\otimes T)\Xi_n.
$$
两份二维空间均取正交标准基。对每个整数 $g\ge0$，恰好发出 $g+2$ 个输出，次序为 $B_L\otimes H_g\otimes B_R\otimes M$。端点是第一个与最后一个已发出的 qubit，保留完整空间 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$，左端点之前没有被忽略的前缀。最终记忆不可访问，只取偏迹；生成途中无记忆读取、重置或反馈。

对每个内部位置 $1\le k\le g$，事先固定一个局部正交标准基
$$
\mathcal B_k=(|\eta_{k,0}\rangle,|\eta_{k,1}\rangle),\qquad
|\eta_{k,r}\rangle=\eta_{k,r,0}|0\rangle+\eta_{k,r,1}|1\rangle,
\qquad \langle\eta_{k,r}|\eta_{k,t}\rangle=\delta_{rt}.
$$
允许的测量恰为这些内部位置上的局部正交秩一投影，选基不依赖任何结果，保留完整记录 $\mathbf r=(r_1,\ldots,r_g)\in\{0,1\}^g$。以下最大值只在这个固定非自适应选基族中取；不包含 POVM、一般仪器、端点滤波、Bell 转换或记忆操作，初始记忆始终是上述纯 $m_0$。

记 $\operatorname{adj}$ 为共轭转置，$\operatorname{outer}(z)=z\operatorname{adj}(z)$，并按左端点为行、右端点为列定义
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad E_0=\operatorname{diag}(1,0).
$$
对一条记录，令 $|\eta_k\rangle=|\eta_{k,r_k}\rangle$，其分量简记为 $\eta_{k,j}=\eta_{k,r_k,j}$。直接采用命题 137.1 的实际分支公式：
$$
D_k=\operatorname{diag}(\overline{\eta_{k,0}},\overline{\eta_{k,1}}),\qquad
C_{\mathbf r}=s^{g+3}JD_1JD_2\cdots JD_gJ,\qquad C_\varnothing=s^3J,
$$
$$
v_{\mathbf r}=\operatorname{vec}_{LR}(C_{\mathbf r}),\qquad
w_{\mathbf r}=s\operatorname{vec}_{LR}(C_{\mathbf r}E_0),\qquad
Q_{\mathbf r}=\operatorname{outer}(v_{\mathbf r})+\operatorname{outer}(w_{\mathbf r}),
$$
$$
q_{\mathbf r}=\operatorname{Tr}Q_{\mathbf r}
=\|C_{\mathbf r}\|_F^2+\alpha\|C_{\mathbf r}E_0\|_F^2,\qquad
\det C_{\mathbf r}=(-1)^{g+1}\alpha^{g+3}
\prod_{k=1}^g\overline{\eta_{k,0}\eta_{k,1}}.
$$
这里 $\|C\|_F^2=\operatorname{Tr}(C\operatorname{adj}(C))$，$Q_{\mathbf r}$ 是实际内部复 bra 收缩后对最终记忆取偏迹的未归一化端点算子，$q_{\mathbf r}$ 是该记录的 Born 概率。命题 137.1 给出 $q_{\mathbf r}=0$ 当且仅当 $C_{\mathbf r}=0$；仅在 $q_{\mathbf r}>0$ 时定义 $\theta_{\mathbf r}=Q_{\mathbf r}/q_{\mathbf r}$。特别地，$q_\varnothing=1$；计算基记录 $(1,1)$ 及混合记录 $(|0\rangle,|-\rangle,|0\rangle)$ 的精确零事件均不定义条件密度，其中 $|-\rangle=(|0\rangle-|1\rangle)/\sqrt2$。

对单位向量 $z=\operatorname{vec}_{LR}(Z)$ 定义纯态 concurrence 为 $c(z)=2|\det Z|$。对完整双 qubit 空间上的密度 $\theta$，定义其凸顶 concurrence 为
$$
\mathcal C(\theta)=\inf\left\{
\sum_{\ell=1}^Np_\ell c(\psi_\ell):
\begin{array}{l}
N\ge1\text{ 为有限整数},\quad p_\ell\ge0,\quad \sum_{\ell=1}^Np_\ell=1,\\
\|\psi_\ell\|=1,\quad
\theta=\sum_{\ell=1}^Np_\ell\operatorname{outer}(\psi_\ell)
\end{array}\right\}.
$$
下确界遍历所有有限复单位纯态系综，不限制于实际记忆列给出的分解；它是密度的数学定义，与对物理测量基的最大化是两个不同的取值域。谱分解保证上述集合非空。术语及纯态 concurrence 的约定见 William K. Wootters，*Entanglement of Formation of an Arbitrary State of Two Qubits*，[arXiv:quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)，式 (7) 及式 (19)–(22) 的系综平均讨论；期刊版为 *Physical Review Letters* **80**，2245–2248（1998），[DOI:10.1103/PhysRevLett.80.2245](https://doi.org/10.1103/PhysRevLett.80.2245)。

则 $0\le c(z)\le1$、$0\le\mathcal C(\theta)\le1$，且每条正概率记录满足精确公式
$$
\mathcal C(\theta_{\mathbf r})=\frac{2|\det C_{\mathbf r}|}{q_{\mathbf r}}.
$$
令
$$
B_k=\sum_{r=0}^1|\eta_{k,r,0}\eta_{k,r,1}|,\qquad
A_g(\mathcal B_1,\ldots,\mathcal B_g)
=\sum_{\substack{\mathbf r\in\{0,1\}^g\\q_{\mathbf r}>0}}
q_{\mathbf r}\mathcal C(\theta_{\mathbf r}).
$$
则
$$
A_g=2\alpha^{g+3}\prod_{k=1}^gB_k,\qquad
\max_{\mathcal B_1,\ldots,\mathcal B_g}A_g=2\alpha^{g+3}.
$$
当 $g\ge1$ 时取到最大值当且仅当每个局部基均平衡，即其两个基向量的两个计算基分量的模均为 $1/\sqrt2$。所有赤道基
$$
\left(\frac{|0\rangle+e^{i\varphi_k}|1\rangle}{\sqrt2},
\frac{|0\rangle-e^{i\varphi_k}|1\rangle}{\sqrt2}\right),\qquad \varphi_k\in\mathbb R,
$$
以及它们逐向量改相位或互换次序后的基均取等，包括加减基。任一内部位置采用计算基（允许相位及次序改变）即有 $A_g=0$。$g=0$ 时空乘积为一，只有空记录及恒等仪器，$A_0=2\alpha^3$，无选基条件。最大值随 $g$ 以比值 $\alpha$ 几何衰减至零。

对每个有限 $g\ge0$，全加减基的每条记录均有非零行列式、正概率和正 concurrence，因而其条件密度不可写成有限凸乘积密度和。不过对 $g\ge1$，命题 133.1、137.1 的无条件端点平均
$$
\overline\Theta_g=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2})
$$
可分，故 $\mathcal C(\overline\Theta_g)=0$，而全加减基的条件 concurrence 的 Born 加权平均为 $2\alpha^{g+3}>0$。

证明。若 $Z=(Z_{ij})_{i,j=0}^1$，三角不等式与 $2uv\le u^2+v^2$ 给出
$$
\begin{aligned}
2|\det Z|&\le2|Z_{00}Z_{11}|+2|Z_{01}Z_{10}|\\
&\le |Z_{00}|^2+|Z_{11}|^2+|Z_{01}|^2+|Z_{10}|^2
=\operatorname{Tr}(Z\operatorname{adj}(Z)).
\end{aligned}
$$
当 $\operatorname{vec}_{LR}(Z)$ 为单位向量时右侧为一。每个有限系综的平均也在 $[0,1]$ 内，结合谱分解的存在便得所述凸顶取值范围。

固定一条 $q=q_{\mathbf r}>0$ 的记录，简写 $C,v,w,Q,\theta$。先设 $C$ 奇异。由 $q>0$ 可知 $C\ne0$，故 $C$ 秩一。按命题 137.1 的复秩一分解，存在非零复列向量 $a,b$ 使 $C=ab^{\mathsf T}$，其中 $\mathsf T$ 是普通转置。由行列约定，
$$
v=a\otimes b,\qquad w=s\,a\otimes E_0b.
$$
把 $v,w$ 中每个非零列 $h$ 化成单位向量 $h/\|h\|$，赋权 $\|h\|^2/q$；这些权重和为一，且所得外积加权和为 $\theta$。每个单位向量均为乘积向量，系数矩阵行列式为零；若 $w=0$ 就省去该列。因此这给出平均 concurrence 为零的有限系综，由非负性得 $\mathcal C(\theta)=0=2|\det C|/q$。

再设 $C$ 可逆。若 $xv+yw=0$，向量化的单射性给出
$$
C(xI+s yE_0)=0.
$$
左乘 $C^{-1}$ 并比较两个对角元得 $x=0$、$x+s y=0$，而 $s>0$，所以 $y=0$。于是矩阵 $H=[\,v\ \ w\,]$ 满列秩，$Q=H\operatorname{adj}(H)$，且
$$
F=(\operatorname{adj}(H)H)^{-1}\operatorname{adj}(H),\qquad FH=I_2
$$
是其左逆。

任取定义中一个有限单位纯态系综 $\theta=\sum_\ell p_\ell\operatorname{outer}(\psi_\ell)$，删去零权重，置 $z_\ell=\sqrt{q p_\ell}\,\psi_\ell$，于是
$$
Q=\sum_\ell\operatorname{outer}(z_\ell)=H\operatorname{adj}(H).
$$
对任意 $u\perp\operatorname{range}H$，
$$
0=\operatorname{adj}(u)Qu=\sum_\ell|\operatorname{adj}(u)z_\ell|^2.
$$
各项非负，故每个 $z_\ell$ 都正交于 $(\operatorname{range}H)^\perp$，即属于 $\operatorname{range}H$。满列秩保证唯一表示 $z_\ell=x_\ell v+y_\ell w$。记 $t_\ell=(x_\ell,y_\ell)^{\mathsf T}=Fz_\ell$，则
$$
\sum_\ell\operatorname{outer}(t_\ell)
=FQ\operatorname{adj}(F)
=FH\operatorname{adj}(H)\operatorname{adj}(F)=I_2.
$$
逐矩阵元读取此式，得到
$$
\sum_\ell|x_\ell|^2=\sum_\ell|y_\ell|^2=1,\qquad
\sum_\ell\overline{x_\ell}y_\ell=0,\qquad
\sum_\ell x_\ell\overline{y_\ell}=0.
$$
若 $z_\ell=\operatorname{vec}_{LR}(Z_\ell)$，线性性给
$$
Z_\ell=C(x_\ell I+s y_\ell E_0),\qquad
\det Z_\ell=\det C\,x_\ell(x_\ell+s y_\ell).
$$
不必改变任何系综相位。由于 $|x_\ell|=|\overline{x_\ell}|$，包括 $x_\ell=0$，有
$$
\begin{aligned}
\sum_\ell|\det Z_\ell|
&=|\det C|\sum_\ell|x_\ell(x_\ell+s y_\ell)|\\
&=|\det C|\sum_\ell|\overline{x_\ell}(x_\ell+s y_\ell)|\\
&\ge |\det C|\left|\sum_\ell
\bigl(|x_\ell|^2+s\overline{x_\ell}y_\ell\bigr)\right|
=|\det C|.
\end{aligned}
$$
二阶行列式的齐次性及 $z_\ell=\sqrt{q p_\ell}\,\psi_\ell$ 又给
$$
\sum_\ell p_\ell c(\psi_\ell)
=\frac2q\sum_\ell|\det Z_\ell|
\ge\frac{2|\det C|}{q}.
$$
所取系综任意，故这是全部有限复纯态系综的共同下界。另一方面，实际两列 $v,w$ 按范数平方除以 $q$ 赋权的单位纯态分解满足
$$
\det(sCE_0)=0,\qquad
\frac{\|v\|^2}{q}c\left(\frac{v}{\|v\|}\right)
+\frac{\|w\|^2}{q}c\left(\frac{w}{\|w\|}\right)
=\frac{2|\det C|}{q}.
$$
可逆情形两列均非零，所以此式无零除。它达到下界，证明 $\mathcal C(\theta)=2|\det C|/q$。这里的两列系综是已取记忆偏迹之密度的数学分解，不引入记忆测量；其最优性来自刚证的共同下界，不是对任意混合分解的最优性断言。整个分支公式由以上有限维论证得到。

现在对固定的完整局部测量求平均。命题 137.1 的正交完备性恒等式为
$$
\sum_{\mathbf r\in\{0,1\}^g}Q_{\mathbf r}
=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2})
=\overline\Theta_g,\qquad
\sum_{\mathbf r\in\{0,1\}^g}q_{\mathbf r}=1.
$$
它由 $\sum_{r=0}^1\operatorname{outer}(|\eta_{k,r}\rangle)=I_B$ 的有限张量积及 $\|\Xi_{g+2}\|=1$ 给出，亦适用于 $g=0$。先用已证分支凸顶公式，得到每条正概率记录的 $q_{\mathbf r}\mathcal C(\theta_{\mathbf r})=2|\det C_{\mathbf r}|$。零概率记录有 $C_{\mathbf r}=0$，其行列式为零，故只在行列式之和中补入这些零项，而不定义它们的条件密度。命题 137.1 的行列式公式及有限乘积展开遂给
$$
\begin{aligned}
A_g
&=2\sum_{\mathbf r\in\{0,1\}^g}|\det C_{\mathbf r}|\\
&=2\alpha^{g+3}\sum_{r_1=0}^1\cdots\sum_{r_g=0}^1
\prod_{k=1}^g|\eta_{k,r_k,0}\eta_{k,r_k,1}|\\
&=2\alpha^{g+3}\prod_{k=1}^g
\left(\sum_{r=0}^1|\eta_{k,r,0}\eta_{k,r,1}|\right).
\end{aligned}
$$
这里分解的是行列式权重之和；正交完备性不要求 Born 概率彼此相等，也不要求这些概率按位置分解。

任意二维复正交标准基可写成
$$
\bigl((a,b)^{\mathsf T},\ e^{i\chi}(-\overline b,\overline a)^{\mathsf T}\bigr),
\qquad |a|^2+|b|^2=1,\qquad \chi\in\mathbb R,
$$
因为第一向量的正交补是一维，所列第二向量是其中的单位向量。因此对应的局部因子及其精确差额为
$$
B=2|ab|,\qquad 1-B=(|a|-|b|)^2\ge0.
$$
故 $0\le B\le1$；$B=1$ 当且仅当 $|a|=|b|=1/\sqrt2$，而 $B=0$ 当且仅当 $a=0$ 或 $b=0$，也就是计算基相差相位及排列的情形。对 $g\ge1$，有限个 $[0,1]$ 因子的乘积为一当且仅当每个因子为一：若有 $B_k<1$，则乘积不大于该因子，严格小于一。平衡基同时实现所有因子为一，于是最大值存在，且等号条件恰如陈述。逐向量去整体相位可将任意平衡基写成所列赤道基；加减基是 $\varphi_k=0$ 的情形。任一计算基因子为零就使整个平均为零。

当 $g=0$，由 $C_\varnothing=s^3J$ 得 $|\det C_\varnothing|=\alpha^3$，由 $q_\varnothing=1$ 得 $A_0=2\alpha^3$，与空乘积公式一致，不附加任何不存在的内部位置条件。若记上述最大值为 $M_g$，则
$$
M_{g+1}=\alpha M_g,\qquad M_g=2\alpha^{g+3}\longrightarrow0,
$$
因为 $0<\alpha<1$。这是一列有限协议的平均值极限，不对无限记录事件作条件化。

最后，全加减基的每个选中向量都有两非零分量，故对每个有限 $g$ 及每条记录，命题 137.1 的行列式非零，进而 $q_{\mathbf r}>0$，已证分支公式给 $\mathcal C(\theta_{\mathbf r})>0$。若双 qubit 密度可分，即为有限凸乘积密度和，则分别谱分解每个乘积因子的两个局部密度，再分配有限求和，得到一个有限单位乘积纯态系综。每个乘积纯态的系数矩阵秩一，故 $c=0$，该密度的凸顶也为零。因此正凸顶排除了上述可分性。对 $g\ge1$，命题 133.1 取纯输入 $P_0=\operatorname{outer}(m_0)$、无前缀 $r=0$、左右块长均为一，正给出 $\overline\Theta_g$ 的有限凸乘积密度分解，故同一谱细化论证给 $\mathcal C(\overline\Theta_g)=0$；全加减基的 $A_g=2\alpha^{g+3}>0$ 则由平均公式得出。两者分别是平均密度的凸顶和保留完整结果记录时各条件密度凸顶的平均，取值顺序不同。证毕。

<a id="entry-626"></a>

## 追加锚（本行以下为增补区）

<a id="section-139"></a>

## 139. 经典记录反馈下逐分支相同的最优端点 concurrence

**命题 139.1（固定次序自适应正交测量的平均最优值与最坏记录保证）。** 沿用命题 130.1 的纯边界生成器，令
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad
\Xi_0=m_0,\qquad \Xi_{n+1}=(I_{H_n}\otimes T)\Xi_n.
$$
两份二维空间均取正交标准基。对每个整数 $g\ge0$，在任何测量之前恰好生成 $g+2$ 个输出，次序为
$$
B_L\otimes B_1\otimes\cdots\otimes B_g\otimes B_R\otimes M.
$$
$L,R$ 是第一个与最后一个已发出的 qubit，左端点之前没有被忽略的前缀，端点保留完整空间 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$。最终记忆只以偏迹忽略，生成及测量均不读取、测量或重置记忆，也不对端点施加操作。

定义策略类 $\mathfrak P_g$ 如下：每个内部位置只测量一次，次序固定为 $1,\ldots,g$；在已观察到历史 $h=(r_1,\ldots,r_t)\in\{0,1\}^t$、$0\le t<g$ 时，策略 $\mathcal P$ 为下一个位置 $t+1$ 指定一个正交标准基
$$
\mathcal B_h=(|\eta_{h,0}\rangle,|\eta_{h,1}\rangle),\qquad
\langle\eta_{h,b}|\eta_{h,d}\rangle=\delta_{bd}\quad(b,d\in\{0,1\}).
$$
此选择只能依赖已知模型、$g$ 和历史 $h$，测量为该基的两个秩一正交投影，保留全部结果记录。零概率历史处可任意补齐正交标准基，使策略定义于整棵有限二叉树，但不为这些历史定义归一化条件态。以下两个最大值仅在 $\mathfrak P_g$ 中取；任意 LOCC、POVM、滤波、可变测量次序、重复测量同一位置及记忆访问均不属于此取值域。

记 $\operatorname{adj}$ 为共轭转置，$\operatorname{outer}(z)=z\operatorname{adj}(z)$，并以左端点为行、右端点为列定义
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad E_0=\operatorname{diag}(1,0).
$$
对每个形式完整记录 $r=(r_1,\ldots,r_g)$，置 $r_{<k}=(r_1,\ldots,r_{k-1})$，并记该路径上实际选中的向量及其分量为
$$
|\eta_{r,k}\rangle:=|\eta_{r_{<k},r_k}\rangle
=\eta_{r,k,0}|0\rangle+\eta_{r,k,1}|1\rangle,\qquad
|\eta_r\rangle=\bigotimes_{k=1}^g|\eta_{r,k}\rangle.
$$
当 $g=0$ 时只有空记录 $\varnothing$，其空张量积是 $H_0$ 的单位向量。逐路径采用命题 137.1 的收缩约定，定义
$$
D_{r,k}=\operatorname{diag}(\overline{\eta_{r,k,0}},\overline{\eta_{r,k,1}}),\qquad
C_r=s^{g+3}JD_{r,1}JD_{r,2}\cdots JD_{r,g}J,\qquad C_\varnothing=s^3J.
$$
实际分支、未归一化端点算子及其 Born 权重为
$$
\begin{aligned}
\chi_r
&=(I_{B_L}\otimes\langle\eta_r|\otimes I_{B_R}\otimes I_M)\Xi_{g+2}\\
&=\operatorname{vec}_{LR}(C_r)\otimes|0\rangle
+s\operatorname{vec}_{LR}(C_rE_0)\otimes|1\rangle,\\
Q_r&=\operatorname{Tr}_M\operatorname{outer}(\chi_r)
=\operatorname{outer}(\operatorname{vec}_{LR}(C_r))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_rE_0)),\\
q_r&=\operatorname{Tr}Q_r
=\|C_r\|_F^2+\alpha\|C_rE_0\|_F^2,
\qquad \|C\|_F^2=\sum_{i,j=0}^1|C_{ij}|^2.
\end{aligned}
$$
有 $q_r=0$ 当且仅当 $C_r=0$，仅对 $q_r>0$ 定义 $\theta_r=Q_r/q_r$，且
$$
\det C_r=(-1)^{g+1}\alpha^{g+3}
\prod_{k=1}^g\overline{\eta_{r,k,0}\eta_{r,k,1}}.
$$
这里的两个记忆列及其权重是实际振幅与偏迹所得，不分别归一化；路径公式不将自适应策略等同于一组固定局部基的笛卡尔积。

采用命题 138.1 的 concurrence 定义，记作 $\mathcal C_{\rm conc}=\mathcal C$：单位向量 $z=\operatorname{vec}_{LR}(Z)$ 的纯态值为 $c(z)=2|\det Z|$，密度 $\theta$ 的值为
$$
\mathcal C_{\rm conc}(\theta)
=\inf\left\{\sum_{\ell=1}^Np_\ell c(\psi_\ell):
\begin{array}{l}
N\ge1\text{ 为有限整数},\quad p_\ell\ge0,\quad\sum_{\ell=1}^Np_\ell=1,\\
\|\psi_\ell\|=1,\quad
\theta=\sum_{\ell=1}^Np_\ell\operatorname{outer}(\psi_\ell)
\end{array}\right\}.
$$
下确界遍历全部有限复单位纯态系综。该定义及其本族恒等式 $\mathcal C_{\rm conc}(Q_r/q_r)=2|\det C_r|/q_r$ 均取自命题 138.1；该命题对全部系综的证明不以实际两记忆列限制取值域。纯态术语的文献约定亦见该命题所引 Wootters，*Entanglement of Formation of an Arbitrary State of Two Qubits*，Physical Review Letters 80，2245–2248（1998），[DOI:10.1103/PhysRevLett.80.2245](https://doi.org/10.1103/PhysRevLett.80.2245)。

定义平均值与最坏正概率记录保证为
$$
A_g(\mathcal P)=\sum_{\substack{r\in\{0,1\}^g\\q_r>0}}
q_r\mathcal C_{\rm conc}(\theta_r),\qquad
G_g(\mathcal P)=\min_{\substack{r\in\{0,1\}^g\\q_r>0}}
\mathcal C_{\rm conc}(\theta_r).
$$
则对任意 $\mathcal P\in\mathfrak P_g$，形式记录向量 $|\eta_r\rangle$ 构成 $H_g$ 的正交标准基，并有
$$
\sum_rQ_r=\overline\Theta_g
:=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2}),\qquad
\sum_rq_r=1.
$$
所以定义 $G_g$ 的有限集合非空，而且
$$
G_g(\mathcal P)\le A_g(\mathcal P)
=2\sum_{r\in\{0,1\}^g}|\det C_r|
\le2\alpha^{g+3}.
$$
存在仅使用既有经典记录的策略 $\mathcal P_*$，使每条完整记录都满足
$$
q_r=2^{-g},\qquad
\mathcal C_{\rm conc}(\theta_r)=2\alpha^{g+3}.
$$
因此两个最大值均达到，且恰为命题 138.1 的固定选基平均最优值：
$$
\max_{\mathcal P\in\mathfrak P_g}G_g(\mathcal P)
=\max_{\mathcal P\in\mathfrak P_g}A_g(\mathcal P)
=2\alpha^{g+3}.
$$
在 $g=0$ 时唯一记录满足 $C_\varnothing=s^3J$、$q_\varnothing=1$、$\mathcal C_{\rm conc}(\theta_\varnothing)=2\alpha^3$，没有选基步骤。两个最优值随 $g$ 以比值 $\alpha$ 几何衰减至零，故不存在对所有 $g$ 一致严格为正的此类保证下界。$g$ 仅是内部输出数，不赋予物理距离或时间含义。

这里逐记录相同的结论仅指这个纠缠量，不附加端点密度相同、谱相同、局部幺正等价、纯 Bell 对或同一校正操作的结论，也不定义 Bell 产率。遗忘全部记录时，对 $g\ge1$ 仍得到命题 133.1 的可分无条件端点密度，故其 concurrence 为零；此陈述只涉及指定态族与指定取值域，不是普适经典性结论。

证明。固定任意策略及一条完整记录。在这条路径上，每个已选局部向量已确定，顺序投影作用在不同内部因子上，其乘积就是这些局部投影的张量积。去掉投影后保留的单位内部向量，端点及记忆的系数向量恰为 $\chi_r$；这一步不需要预先固定其他路径的基。命题 137.1 的复 bra 收缩公式逐路径适用，给出上述 $C_r$ 和两记忆列；取记忆偏迹给 $Q_r$ 及 $q_r$。两个平方范数之和为零当且仅当 $C_r=0$。又因 $\det J=-1$、$s^2=\alpha$，行列式的乘法性给出所列 $\det C_r$，包含空记录。这样保留了左行右列及所有 bra 的复共轭，概率也是整条分支的未归一化范数平方。

任取两条不同形式记录 $r,r'$，令 $k$ 为首次分歧位置。它们在此之前的历史相同，因此第 $k$ 个位置采用同一个正交标准基，而两个结果标签不同，故
$$
\langle\eta_{r,k}|\eta_{r',k}\rangle=0,\qquad
\langle\eta_r|\eta_{r'}\rangle
=\prod_{j=1}^g\langle\eta_{r,j}|\eta_{r',j}\rangle=0.
$$
每个张量向量范数为一，共有 $2^g=\dim H_g$ 个，所以它们是正交标准基，$\sum_r\operatorname{outer}(|\eta_r\rangle)=I_{H_g}$。不可达历史处的任意正交补齐同样满足这一论证。把 $\Xi_{g+2}$ 在此内部基上展开后取内部偏迹，再取记忆偏迹，得到 $\sum_rQ_r=\overline\Theta_g$；由命题 130.1 的 $\|\Xi_{g+2}\|=1$，取迹得 $\sum_rq_r=1$。当 $g=0$ 时基仅含空张量积，两个等式仍成立。因此至少有一条正概率记录，且归一化条件密度只在这个非空有限子集上使用。

由命题 138.1 已对全部有限系综证明的本族公式，每条正概率记录有 $q_r\mathcal C_{\rm conc}(\theta_r)=2|\det C_r|$。零概率记录有 $C_r=0$，只向行列式求和补入零项，便得
$$
A_g(\mathcal P)
=2\alpha^{g+3}\sum_{r\in\{0,1\}^g}
\prod_{k=1}^g|\eta_{r,k,0}\eta_{r,k,1}|.
$$
任一单位 qubit 向量满足
$$
2|\eta_{r,k,0}\eta_{r,k,1}|
\le |\eta_{r,k,0}|^2+|\eta_{r,k,1}|^2=1.
$$
故每条形式记录的乘积不超过 $2^{-g}$，共有 $2^g$ 条，直接得到 $A_g(\mathcal P)\le2\alpha^{g+3}$。这个估计逐记录成立，不对含历史依赖的求和作逐位置因子分解。正概率权重之和为一，每个对应的 concurrence 均不小于其最小值，故 $G_g(\mathcal P)\le A_g(\mathcal P)$。

现在构造达到这两个上界的策略。先定义仅由已知输出密度和已观察到的历史确定的条件密度。令
$$
\Omega_{\rm out}=\operatorname{Tr}_M\operatorname{outer}(\Xi_{g+2}).
$$
对于长度 $t<g$ 的历史 $h$，沿其已选路径置
$$
K_h=I_{B_L}\otimes
\left(\bigotimes_{k=1}^t\langle\eta_{h_{<k},h_k}|\right)
\otimes I_{B_{t+1}\otimes\cdots\otimes B_g\otimes B_R},
\qquad X_h=K_h\Omega_{\rm out}\operatorname{adj}(K_h),\qquad q_h=\operatorname{Tr}X_h.
$$
这里 $q_h$ 是前缀事件的 Born 概率，空历史有 $K_\varnothing=I$、$q_\varnothing=1$。同一定义在 $t=g$ 时保留的末因子仅为 $B_R$，此时 $X_r=Q_r$。在 $q_h>0$ 且 $t<g$ 时，下一内部位置的归一化条件密度为
$$
\rho_h=\frac1{q_h}
\operatorname{Tr}_{B_L,B_{t+2},\ldots,B_g,B_R}X_h
=\begin{pmatrix}a&c\\\overline c&1-a\end{pmatrix},
\qquad a\in[0,1],\quad c\in\mathbb C.
$$
$t=g-1$ 时上式只迹去 $B_L,B_R$。这一定义对已知 $\Omega_{\rm out}$ 收缩过去的投影，除以实际前缀权重，再迹去其余输出；没有读取隐藏记忆值、测定未知态、使用未来结果或访问最终记忆。由于此前投影仅在输出上，先对记忆取偏迹与这些收缩可交换，故它正是该事件下下一位置的 Born 密度。

在每个已到达历史 $h$ 上，精确地定义
$$
\kappa_h=
\begin{cases}
i\,\overline c/|c|,&c\ne0,\\
1,&c=0,
\end{cases}
\qquad
|\eta_{h,0}\rangle=\frac{|0\rangle+\kappa_h|1\rangle}{\sqrt2},\qquad
|\eta_{h,1}\rangle=\frac{|0\rangle-\kappa_h|1\rangle}{\sqrt2}.
$$
两种情形均有 $|\kappa_h|=1$，所以两向量范数为一，内积为 $(1-|\kappa_h|^2)/2=0$；它们构成平衡正交标准基。按照所写的非对角元约定 $\rho_{h,01}=c$，对两个标签直接计算得
$$
\begin{aligned}
\Pr(0\mid h)&=\langle\eta_{h,0}|\rho_h|\eta_{h,0}\rangle
=\frac12+\operatorname{Re}(\kappa_hc),\\
\Pr(1\mid h)&=\langle\eta_{h,1}|\rho_h|\eta_{h,1}\rangle
=\frac12-\operatorname{Re}(\kappa_hc).
\end{aligned}
$$
若 $c\ne0$，则 $\kappa_hc=i|c|$，实部为零；若 $c=0$，则 $\kappa_hc=0$，实部也为零。故两个条件概率严格等于 $1/2$。这里 $c=0$ 是精确分支；任意非零复数 $c$，无论其模多小，均采用第一行公式。

从 $q_\varnothing=1$ 开始按历史长度归纳。若长度 $t<g$ 的每个历史已满足 $q_h=2^{-t}>0$，则它们的 $\rho_h$ 全部存在，上述两个基向量也均已定义；对 $b=0,1$ 有
$$
q_{hb}=q_h\Pr(b\mid h)=2^{-(t+1)}>0.
$$
这同时证明下一层全部可达，并允许继续定义该策略，没有用尚未证明为正的权重归一化。有限归纳给出整棵树及其全部完整记录，且 $q_r=2^{-g}$。每个被选向量的两个计算基分量的模都为 $1/\sqrt2$，故路径行列式满足
$$
|\det C_r|=\alpha^{g+3}2^{-g}>0,\qquad
\mathcal C_{\rm conc}(\theta_r)
=\frac{2\alpha^{g+3}2^{-g}}{2^{-g}}=2\alpha^{g+3}.
$$
于是 $\mathcal P_*$ 同时达到 $A_g$ 和 $G_g$ 的上界。这一存在性构造不包含自适应性为必要条件的断言。平衡性本身也不蕴含等概率：$g=1$ 的固定实加减基由同一 $Q_r$ 公式给出 $q_+=1/2+\alpha^3$、$q_-=1/2-\alpha^3$，两者不同；上面的等概率来自所选相位与条件非对角元的关系。

在 $g=0$ 时无内部测量，完备性给 $q_\varnothing=1$，而 $|\det(s^3J)|=\alpha^3$，命题 138.1 的本族公式给唯一 concurrence 为 $2\alpha^3$。令任一最优值为 $M_g=2\alpha^{g+3}$，则 $M_{g+1}=\alpha M_g$ 且 $M_g\to0$。因此对任意 $\varepsilon>0$，存在有限 $g$ 使每个允许策略都满足 $G_g(\mathcal P)\le M_g<\varepsilon$，排除跨全部 $g$ 的一致正下界。

最后，任意策略遗忘记录后的密度都等于已证的 $\overline\Theta_g$。当 $g\ge1$，命题 133.1 取纯输入 $P_0=\operatorname{outer}(m_0)$、被忽略前缀长为零、左右块长均为一，给出该密度的有限凸乘积密度分解。将两个局部密度各自谱分解，可细化为有限单位乘积纯态系综，各项行列式为零，故 $\mathcal C_{\rm conc}(\overline\Theta_g)=0$。相反，上述策略保留记录时的条件 concurrence 平均为 $2\alpha^{g+3}>0$；这里分别是平均密度的 concurrence 与条件 concurrence 的平均。又因构造中每个 $C_r$ 可逆，命题 137.1 给每个条件密度秩二，故这些分支并非纯 Bell 对；同一 concurrence 等式没有比较端点密度、谱或局部幺正轨道，也未增加任何端点校正或转换操作。证毕。

<a id="entry-628"></a>

## 追加锚（本行以下为增补区）

<a id="section-140"></a>

## 140. 原始结果坐标的删除与联合奇偶记录的条件纠缠

**命题 140.1（固定选基下的坐标遗忘、独立擦除与两内部位奇偶反例）。** 取命题 130.1 的纯边界生成器，令
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha^2+\alpha=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad
\Xi_0=m_0,\qquad \Xi_{n+1}=(I_{H_n}\otimes T)\Xi_n.
$$
两份二维空间均取正交标准基。对每个整数 $g\ge0$，在任何测量之前恰好生成 $g+2$ 个输出，完整次序为
$$
B_L\otimes B_1\otimes\cdots\otimes B_g\otimes B_R\otimes M.
$$
$L,R$ 是第一个和最后一个已发出的 qubit，左端点之前没有被忽略的前缀，端点保留完整空间 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$。生成途中不读取、测量或重置记忆；最终记忆不可访问并取偏迹。

测量族取命题 138.1 的固定非自适应族：对每个内部位置，事先选定局部正交标准基
$$
\mathcal B_k=(|\eta_{k,0}\rangle,|\eta_{k,1}\rangle),\qquad
|\eta_{k,r}\rangle=\eta_{k,r,0}|0\rangle+\eta_{k,r,1}|1\rangle,
\qquad \langle\eta_{k,r}|\eta_{k,t}\rangle=\delta_{rt}.
$$
每个内部位置仅在此基测量一次，全部基在任何结果出现之前确定。以命题 139.1 的历史记号表示，这里要求 $\mathcal B_h=\mathcal B_{|h|+1}$ 对全部历史成立；不取该命题的一般历史依赖选基族。端点不施加操作，结果不用于后续选基或其他反馈控制；下文仅允许对已完成测量的经典记录作所指定的处理，该处理不耦合到端点或记忆。测后的内部输出及结果的其他物理副本均不可访问，所声明的经典接口是唯一可访问记录。因而一个结果此前是否被用于物理控制，与它此后是否仍可访问，是分别受限的两个假设；事后删除记录不撤销既往控制。

写 $[g]=\{1,\ldots,g\}$，$[0]=\varnothing$。沿用命题 137.1 的分支及左行右列向量化记号，$\operatorname{adj}$ 表示共轭转置，$\operatorname{outer}(z)=z\operatorname{adj}(z)$，并令
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad E_0=\operatorname{diag}(1,0).
$$
对完整原始记录 $r=(r_1,\ldots,r_g)\in\{0,1\}^g$，置
$$
D_{k,r_k}=\operatorname{diag}(\overline{\eta_{k,r_k,0}},\overline{\eta_{k,r_k,1}}),\qquad
C_r=s^{g+3}JD_{1,r_1}JD_{2,r_2}\cdots JD_{g,r_g}J,
\qquad C_\varnothing=s^3J.
$$
命题 137.1 的实际收缩公式为
$$
\begin{aligned}
\chi_r
&=(I_{B_L}\otimes\langle\eta_{1,r_1}|\otimes\cdots\otimes
\langle\eta_{g,r_g}|\otimes I_{B_R}\otimes I_M)\Xi_{g+2}\\
&=\operatorname{vec}_{LR}(C_r)\otimes|0\rangle
+s\operatorname{vec}_{LR}(C_rE_0)\otimes|1\rangle,\\
Q_r&=\operatorname{Tr}_M\operatorname{outer}(\chi_r)
=\operatorname{outer}(\operatorname{vec}_{LR}(C_r))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_rE_0)),\\
q_r&=\operatorname{Tr}Q_r=\|C_r\|_F^2+\alpha\|C_rE_0\|_F^2,
\qquad \|C\|_F^2=\sum_{i,j=0}^1|C_{ij}|^2.
\end{aligned}
$$
其中 $q_r$ 是 Born 概率，$q_r=0$ 当且仅当 $C_r=0$；仅在 $q_r>0$ 时定义 $\theta_r=Q_r/q_r$，且 $\sum_rq_r=1$。两记忆列保留实际振幅，不分别归一化。

采用命题 138.1 的 concurrence，记 $\mathcal C_{\rm conc}=\mathcal C$。单位向量 $z=\operatorname{vec}_{LR}(Z)$ 的纯态值为 $c(z)=2|\det Z|$，密度 $\theta$ 的值定义为
$$
\mathcal C_{\rm conc}(\theta)=\inf\left\{
\sum_{\ell=1}^Np_\ell c(\psi_\ell):
\begin{array}{l}
N\ge1\text{ 为有限整数},\quad p_\ell\ge0,\quad\sum_{\ell=1}^Np_\ell=1,\\
\|\psi_\ell\|=1,\quad\theta=\sum_{\ell=1}^Np_\ell\operatorname{outer}(\psi_\ell)
\end{array}\right\}.
$$
下确界遍历全部有限复单位纯态系综。直接采用命题 138.1 已证恒等式
$$
\mathcal C_{\rm conc}(\theta_r)=\frac{2|\det C_r|}{q_r}\quad(q_r>0),\qquad
B_k=\sum_{r=0}^1|\eta_{k,r,0}\eta_{k,r,1}|\le1,
$$
$$
A_g(\mathrm{full})
:=\sum_{r:q_r>0}q_r\mathcal C_{\rm conc}(\theta_r)
=2\alpha^{g+3}\prod_{k=1}^gB_k.
$$
可分密度采用命题 132.1 的有限凸乘积密度和定义；相应的可分正锥为
$$
\operatorname{Sep}_+(L:R)=\left\{\sum_{\nu=1}^N U_\nu\otimes V_\nu:
N\ge1\text{ 为有限整数},\quad U_\nu\ge0,\quad V_\nu\ge0\right\},
$$
它包含零算子。则以下三项成立。

（A）对每个有限 $g\ge1$、固定真子集 $S\subsetneq[g]$ 及保留值 $y\in\{0,1\}^S$，定义
$$
Q_{S,y}=\sum_{r:r_S=y}Q_r,\qquad q_{S,y}=\operatorname{Tr}Q_{S,y}.
$$
有 $Q_{S,y}\in\operatorname{Sep}_+(L:R)$，包括 $Q_{S,y}=0$。当 $q_{S,y}>0$ 时，$Q_{S,y}/q_{S,y}$ 是可分密度且 concurrence 为零。这里遗忘的是一组固定的原始结果坐标，不量化记录的任意非单射函数。

（B）对所有 $g\ge0$ 及 $S\subseteq[g]$，沿用同一求和式定义 $Q_{S,y}$、$q_{S,y}$，故完整掩码满足 $Q_{[g],r}=Q_r$、$q_{[g],r}=q_r$。完成全部局部测量后，将每个原始标志独立通过经典擦除：第 $k$ 个标志以固定概率 $t_k\in[0,1]$ 保留，擦除随机性独立于全部结果值，且各位置相互独立。接口同时揭示保留掩码 $S$ 和保留值 $y$，不留其他可访问副本。令
$$
w_S=\prod_{k\in S}t_k\prod_{k\notin S}(1-t_k).
$$
事件 $(S,y)$ 的未归一化端点算子及概率分别为 $w_SQ_{S,y}$ 和 $w_Sq_{S,y}$；仅在 $w_Sq_{S,y}>0$ 时，其条件密度定义为
$$
\theta^{\rm erased}_{S,y}=\frac{w_SQ_{S,y}}{w_Sq_{S,y}}
=\frac{Q_{S,y}}{q_{S,y}}.
$$
按这一掩码与值接口求平均，则
$$
\begin{aligned}
A_g(\mathrm{erased})
&:=\sum_{\substack{S\subseteq[g],\ y\in\{0,1\}^S\\w_Sq_{S,y}>0}}
w_Sq_{S,y}\mathcal C_{\rm conc}(\theta^{\rm erased}_{S,y})\\
&=\left(\prod_{k=1}^gt_k\right)A_g(\mathrm{full})
=2\alpha^{g+3}\prod_{k=1}^g(t_kB_k).
\end{aligned}
$$
当 $g=0$ 时只有空记录、空掩码，所有空乘积为一，平均值为 $2\alpha^3$。若存在 $t_k=0$，则对任意上述固定基族，平均值均为零。这里取的是条件密度 concurrence 的平均，不是平均密度的 concurrence。值无关性是必要的适用假设：若掩码选择依赖结果，揭示掩码本身可以揭示联合关系，事件算子不自动等于 $w_SQ_{S,y}$。

（C）取 $g=2$，两个内部位置均测加减基
$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
|-\rangle=\frac{|0\rangle-|1\rangle}{\sqrt2},
$$
标签分别为 $0,1$。在完成全部测量后，仅保留经典位 $b=r_1\mathbin{\oplus}r_2$，不独立保留任何原始值。两个事件算子为
$$
Q_{\rm even}=Q_{00}+Q_{11},\qquad Q_{\rm odd}=Q_{01}+Q_{10}.
$$
两事件概率均严格为正，其条件端点密度均纠缠；而仅保留任一原始位的条件端点密度均由（A）可分。因此一个联合奇偶位与一个原始坐标位具有不同的条件纠缠性质。此反例的参数限定为 $g=2$，所保留的性质是纠缠，不是完整记录对所有端点实验的预测：同属偶事件的正概率记录 $00,11$ 满足
$$
\Pr(01\mid00)=\frac4{18+13\alpha}>0,\qquad
\Pr(01\mid11)=0.
$$
故奇偶位不是完整端点密度的充分统计量。

证明。先证（A）。置 $\Omega_{\rm out}=\operatorname{Tr}_M\operatorname{outer}(\Xi_{g+2})$，任取 $k\notin S$。对第 $k$ 个输出因子，固定正交标准基的完备性给出对任意联合算子 $X$ 的恒等式
$$
\sum_{r_k=0}^1
(I\otimes\langle\eta_{k,r_k}|\otimes I)X
(I\otimes|\eta_{k,r_k}\rangle\otimes I)
=\operatorname{Tr}_{B_k}X.
$$
两个恒等因子各表示该位置前、后的全部旁观因子。这是偏迹在任意正交标准基下的表达。其余位置上的选择都是固定的，作用在不相交张量因子上，所以其 bra 收缩及隐藏结果求和均与此求和、偏迹交换；对最终记忆取偏迹也同样交换。这一步无需假设各测量结果独立。

先不施加任何其余位置的投影，将第 $k$ 个输出两侧取为完整非空块
$$
K_-=B_L\otimes B_1\otimes\cdots\otimes B_{k-1},\qquad
K_+=B_{k+1}\otimes\cdots\otimes B_g\otimes B_R.
$$
这两块的长度分别为 $k\ge1$ 和 $g+1-k\ge1$。命题 133.1 的纯边界分块公式取输入 $P_0=\operatorname{outer}(m_0)$、忽略前缀长度 $0$、左块长度 $k$、间隔长度 $1$、右块长度 $g+1-k$，即给
$$
\operatorname{Tr}_{B_k}\Omega_{\rm out}
=\theta^{P_0}_{0;k,1,g+1-k}
=\sum_{\nu=1}^N U_\nu\otimes V_\nu,
\qquad U_\nu\ge0,\quad V_\nu\ge0.
$$
其中凸权重已吸收入正因子，分解是在 $K_-\mid K_+$ 上进行的；命题 133.1 允许发出左块后左块与活动记忆相关，并未以独立边缘替换该相关输入。

在 $K_-$ 上，对 $S\cap\{1,\ldots,k-1\}$ 的位置作指定 $y$ 的 bra 收缩，对其余内部位置取偏迹，记所得局部线性映射为 $\Phi_-:\mathcal L(K_-)\to\mathcal L(B_L)$。同样定义 $\Phi_+:\mathcal L(K_+)\to\mathcal L(B_R)$。每一步 $X\mapsto KX\operatorname{adj}(K)$ 与偏迹均保持正性，所以两映射把各正因子送到正因子；它们可以不保迹。由刚才的交换恒等式与有限求和的分配律，
$$
\begin{aligned}
Q_{S,y}
&=(\Phi_-\otimes\Phi_+)(\operatorname{Tr}_{B_k}\Omega_{\rm out})\\
&=\sum_{\nu=1}^N\Phi_-(U_\nu)\otimes\Phi_+(V_\nu)
\in\operatorname{Sep}_+(L:R).
\end{aligned}
$$
这恰是所有相容完整分支的未归一化和，因此保留实际 Born 权重，而不是先归一化每条分支再等权混合。上述等式也包含零事件。

若 $q=q_{S,y}>0$，写 $A_\nu=\Phi_-(U_\nu)$、$F_\nu=\Phi_+(V_\nu)$ 及 $a_\nu=\operatorname{Tr}A_\nu$、$f_\nu=\operatorname{Tr}F_\nu$。正算子迹为零则算子为零；删去 $a_\nu f_\nu=0$ 的零乘积项后，
$$
\frac{Q_{S,y}}q
=\sum_{\nu:a_\nu f_\nu>0}
\frac{a_\nu f_\nu}{q}\,
\frac{A_\nu}{a_\nu}\otimes\frac{F_\nu}{f_\nu},\qquad
\sum_\nu\frac{a_\nu f_\nu}{q}=1.
$$
这就是有限凸乘积密度分解。按命题 138.1 证明中的谱细化，将每个局部密度各自谱分解再分配求和，得到有限单位乘积纯态系综。每个乘积纯态的系数矩阵秩一，故纯态 concurrence 为零；凸顶非负且不超过这个零平均值，所以也为零。（A）成立。

对（B），完整测量后的经典记录与端点联合态可写成
$$
\sum_{r\in\{0,1\}^g}|r\rangle\langle r|\otimes Q_r.
$$
值无关且相互独立的擦除使任一给定记录 $r$ 产生掩码 $S$ 的概率恰为 $w_S$，与 $r$ 无关；它产生接口值 $(S,y)$ 当且仅当 $r_S=y$。经典通道的线性性于是给出事件算子
$$
\sum_{r:r_S=y}w_SQ_r=w_SQ_{S,y},
$$
其迹为 $w_Sq_{S,y}$。只有该迹为正时才归一化，此时 $w_S>0$、$q_{S,y}>0$，约去 $w_S$ 即得所列条件密度。所有事件的概率之和为
$$
\sum_{S\subseteq[g]}w_S\sum_yq_{S,y}
=\sum_{S\subseteq[g]}w_S
=\prod_{k=1}^g(t_k+(1-t_k))=1.
$$
这里对每个固定掩码有 $\sum_yq_{S,y}=\sum_rq_r=1$，不对 Born 权重作逐位置分解。

当 $g\ge1$，所有真子掩码的正概率分支由（A）贡献零 concurrence；完整掩码 $S=[g]$ 的权重是 $w_{[g]}=\prod_kt_k$，其保留值就是完整记录。因此正概率项的求和给
$$
A_g(\mathrm{erased})=w_{[g]}
\sum_{r:q_r>0}q_r\mathcal C_{\rm conc}(\theta_r)
=\left(\prod_kt_k\right)2\alpha^{g+3}\prod_kB_k.
$$
若 $w_{[g]}=0$，完整掩码没有正概率事件，上式两侧均为零，未对这些事件定义条件态。若 $g=0$，唯一的空掩码同时是完整掩码，$C_\varnothing=s^3J$、$q_\varnothing=1$；命题 138.1 给唯一 concurrence 为 $2\alpha^3$，也与命题 132.1 的纯边界相邻密度 $G_0$ 相符。故空乘积公式同样成立。任一 $t_k=0$ 的结论随之得到。若改成结果相关的掩码律 $p(S\mid r)$，对应算子应为 $\sum_{r:r_S=y}p(S\mid r)Q_r$；不能把这个因子移出求和。这说明值无关性在证明中的确切作用。

最后证（C）。令 $Z=\operatorname{diag}(1,-1)$。两局部 bra 给 $D_{k,0}=I/\sqrt2$、$D_{k,1}=Z/\sqrt2$，故直接在命题 137.1 的转移乘积中相乘得
$$
C_r=\frac{s^5}{2}M_r,\qquad M_r=JZ^{r_1}JZ^{r_2}J,
$$
$$
M_{00}=\begin{pmatrix}3&2\\2&1\end{pmatrix},\quad
M_{01}=\begin{pmatrix}1&2\\0&1\end{pmatrix},\quad
M_{10}=\begin{pmatrix}1&0\\2&1\end{pmatrix},\quad
M_{11}=\begin{pmatrix}-1&0\\0&1\end{pmatrix}.
$$
每个 $M_r$ 非零，故四个完整记录均有正概率。若 $v_r=\operatorname{vec}_{LR}(M_r)$、$e_r=\operatorname{vec}_{LR}(M_rE_0)$，则
$$
Q_r=\frac{\alpha^5}{4}\bigl(v_rv_r^{\mathsf T}+\alpha e_re_r^{\mathsf T}\bigr).
$$
此处向量均实，所以普通转置就是伴随。记录已经经典化，按奇偶合并只对 $Q_r$ 相加，不产生不同记录振幅的交叉项；不把这个经典处理替换成内部量子系统上的相干奇偶投影或 $C_{00}+C_{11}$ 的分支振幅。

置 $u=1+\alpha$。在 $00,01,10,11$ 次序下，逐项外积给出显式未归一化矩阵
$$
Q_{\rm even}=\frac{\alpha^5}{4}
\begin{pmatrix}
10u&6&6u&2\\
6&4&4&2\\
6u&4&4u&2\\
2&2&2&2
\end{pmatrix},\qquad
Q_{\rm odd}=\frac{\alpha^5}{4}
\begin{pmatrix}
2u&2&2u&2\\
2&4&0&2\\
2u&0&4u&2\\
2&2&2&2
\end{pmatrix}.
$$
取迹并用 $\alpha^5=5\alpha-3$、$\alpha^2=1-\alpha$，有
$$
\begin{aligned}
q_{\rm even}
&=\frac{\alpha^5}{4}(20+14\alpha)
=\frac{(5\alpha-3)(20+14\alpha)}4
=\frac52-3\alpha,\\
q_{\rm odd}
&=\frac{\alpha^5}{4}(12+6\alpha)
=\frac{(5\alpha-3)(12+6\alpha)}4
=3\alpha-\frac32.
\end{aligned}
$$
两式的首个表达式直接为正，末个表达式相加为一。

采用命题 132.1、137.1 的右偏转置约定
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|.
$$
记 $P_b=(4/\alpha^5)\operatorname{PT}_R(Q_b)$，则
$$
P_{\rm even}=\begin{pmatrix}
10u&6&6u&4\\
6&4&2&2\\
6u&2&4u&2\\
4&2&2&2
\end{pmatrix},\qquad
P_{\rm odd}=\begin{pmatrix}
2u&2&2u&0\\
2&4&2&2\\
2u&2&4u&2\\
0&2&2&2
\end{pmatrix}.
$$
为展开行列式，偶矩阵第一行四个不带符号的三阶余子式依次为
$$
8(2\alpha+1),\quad 8(2\alpha+1),\quad-8(3\alpha+1),\quad-8\alpha;
$$
奇矩阵第一行前三个相应余子式为 $8(2\alpha+1)$、$8(2\alpha+1)$、$-8u$，第四项的系数为零。因此沿第一行展开给
$$
\begin{aligned}
\frac{\det P_{\rm even}}{16}
&=5u(2\alpha+1)-3(2\alpha+1)-3u(3\alpha+1)+2\alpha
=\alpha^2-\alpha-1,\\
\frac{\det P_{\rm odd}}{16}
&=u(2\alpha+1)-(2\alpha+1)-u^2
=\alpha^2-\alpha-1.
\end{aligned}
$$
由 $\alpha^2+\alpha=1$，两者均等于 $-2\alpha$。恢复四维矩阵的标量因子，便得两个精确恒等式
$$
\det\operatorname{PT}_R(Q_{\rm even})
=\det\operatorname{PT}_R(Q_{\rm odd})
=\left(\frac{\alpha^5}{4}\right)^4(-32\alpha)
=-\frac{\alpha^{21}}8<0.
$$
两偏转置矩阵均为 Hermitian；正半定 Hermitian 矩阵的特征值非负，其行列式作为特征值之积亦非负，所以此负行列式排除正半定性。另一方面，若 $Q=\sum_\nu A_\nu\otimes F_\nu$ 且各因子正半定，则
$$
\operatorname{PT}_R(Q)=\sum_\nu A_\nu\otimes F_\nu^{\mathsf T}\ge0,
$$
因为正矩阵的转置仍正。这是可分性之偏转置正性的必要条件，亦见命题 132.1 所引 Asher Peres，*Separability Criterion for Density Matrices*，Physical Review Letters 77，1413–1415（1996），[DOI:10.1103/PhysRevLett.77.1413](https://doi.org/10.1103/PhysRevLett.77.1413)。由于 $q_b>0$，归一化只将对应行列式除以自己的 $q_b^4$：
$$
\det\operatorname{PT}_R(Q_b/q_b)=-\frac{\alpha^{21}}{8q_b^4}<0
\quad(b=\mathrm{even},\mathrm{odd}).
$$
故两个条件端点密度均纠缠。仅保留 $r_1$ 或仅保留 $r_2$，则分别取（A）的 $S=\{1\}$ 或 $S=\{2\}$，均为真子集，得到可分条件态；这并不适用于联合标签 $r_1\mathbin{\oplus}r_2$。

同一例也落实了（B）的值无关性边界：若规定偶记录揭示 $S=\varnothing$，奇记录揭示 $S=\{1\}$ 及其保留值，则所有揭示的掩码都是真子集，但空掩码事件的算子是 $Q_{\rm even}$，其正概率条件态纠缠。该掩码选择依赖联合结果，并非（B）的独立擦除。

最后，由所列 $M$ 矩阵及两记忆列的实际权重，
$$
q_{00}=\frac{\alpha^5}{4}(18+13\alpha)>0,\qquad
q_{11}=\frac{\alpha^5}{4}(2+\alpha)>0,
$$
$$
\langle01|Q_{00}|01\rangle=\frac{\alpha^5}{4}\,4,
\qquad \langle01|Q_{11}|01\rangle=0.
$$
分别除以各自的正概率即得陈述中的两个条件预测，它们不同而奇偶值相同。因而这里保留纠缠的单比特反例不保留完整记录的全部端点预测，也不给出任意 $g$ 的奇偶结论或一般压缩最优性、比特或熵下界。全部结论的量词限于所写的固定生成、固定选基及无反馈记录接口，不附加物理擦除代价、Bell 产率、任意局部操作与经典通信的结论，亦不赋予 $g$ 时空度量含义。证毕。

<a id="entry-630"></a>

## 追加锚（本行以下为增补区）

<a id="section-141"></a>

## 141. 两内部位经典奇偶记录的独立翻转与精确可分阈值

**命题 141.1（带噪奇偶报告的条件端点可分性）。** 沿用命题 140.1（C）的完整加减基仪器与命题 130.1 的纯边界生成器，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha^2+\alpha=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
\Xi_0=m_0,\qquad
\Xi_{n+1}=(I_{B^{\otimes n}}\otimes T)\Xi_n\quad(0\le n<4).
$$
各空间均取正交标准基，恰好发出四位，完整次序为
$$
B_L\otimes B_1\otimes B_2\otimes B_R\otimes M.
$$
左右端点分别是第一位和第四位，左端点之前没有被忽略的前缀。生成过程中不读取、测量或重置记忆，最终记忆取偏迹且不可访问。两个内部输出分别在事先固定的局部正交基
$$
|\eta_r\rangle=\frac{|0\rangle+(-1)^r|1\rangle}{\sqrt2}
\quad(r=0,1),\qquad |\eta_0\rangle=|+\rangle,\quad |\eta_1\rangle=|-\rangle
$$
中测量一次。测量全部完成且结果已为经典记录后，形成
$$
b=r_1\mathbin{\oplus}r_2\in\{0,1\}.
$$
结果不用于反馈、后续选基或端点操作；测后的内部系统及原始记录、奇偶记录的其他副本均不可访问，不允许环境重新耦合或记录的相干重组。端点的张量分割始终是完整的 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$。

记 $Q_0=Q_{\rm even}$、$Q_1=Q_{\rm odd}$ 为命题 140.1（C）的实际未归一化端点算子，$\operatorname{adj}$ 表示共轭转置。在 $00,01,10,11$ 次序下，令
$$
Q_b=\frac{\alpha^5}{4}N_b,\qquad
N_0=\begin{pmatrix}
10(1+\alpha)&6&6(1+\alpha)&2\\
6&4&4&2\\
6(1+\alpha)&4&4(1+\alpha)&2\\
2&2&2&2
\end{pmatrix},\qquad
N_1=\begin{pmatrix}
2(1+\alpha)&2&2(1+\alpha)&2\\
2&4&0&2\\
2(1+\alpha)&0&4(1+\alpha)&2\\
2&2&2&2
\end{pmatrix}.
$$
其实际先验概率为
$$
\begin{aligned}
q_0=\operatorname{Tr}Q_0
&=\frac{\alpha^5}{4}(20+14\alpha)=\frac52-3\alpha>0,\\
q_1=\operatorname{Tr}Q_1
&=\frac{\alpha^5}{4}(12+6\alpha)=3\alpha-\frac32>0,
\end{aligned}
\qquad q_0+q_1=1,\qquad q_0\ne q_1.
$$
在此经典奇偶位上施加独立二元对称通道：翻转位 $e$ 独立于测量记录及其端点系综，满足
$$
\Pr(e=1)=\epsilon\in[0,1],\qquad y=b\mathbin{\oplus}e.
$$
唯一保留的接口是 $y$；不保留 $b$ 或原始记录的隐藏副本，翻转位 $e$ 不可访问。这一通道只处理已经经典化的记录。相应事件算子、概率及条件密度定义为
$$
\widetilde Q_0=(1-\epsilon)Q_0+\epsilon Q_1,\qquad
\widetilde Q_1=\epsilon Q_0+(1-\epsilon)Q_1,
$$
$$
\widetilde q_y=\operatorname{Tr}\widetilde Q_y>0,\qquad
\rho_y=\frac{\widetilde Q_y}{\widetilde q_y}\quad(y=0,1).
$$
特别地，实际归一化混合权重是贝叶斯后验
$$
\Pr(b\mid y)=\frac{\Pr(y\mid b)q_b}{\widetilde q_y},\qquad
\Pr(y\mid b)=
\begin{cases}1-\epsilon,&y=b,\\ \epsilon,&y\ne b,\end{cases}
\qquad
\rho_y=\sum_{b=0}^1\Pr(b\mid y)\frac{Q_b}{q_b}.
$$
先验不等，故直接以原通道权重混合两个归一化密度一般得到不同的态。

可分性采用命题 132.1 的有限凸乘积密度和定义，纠缠指不可分。沿用右偏转置约定
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|.
$$
称密度为 PPT，是指其右偏转置正半定；NPT 指其右偏转置不是正半定。则对每个 $\epsilon\in[0,1]$ 和每个 $y\in\{0,1\}$，
$$
\rho_y\text{ 为 NPT}
\quad\Longleftrightarrow\quad
\rho_y\text{ 纠缠}
\quad\Longleftrightarrow\quad
\epsilon(1-\epsilon)<\frac{\alpha^3}{2},
$$
$$
\rho_y\text{ 为 PPT}
\quad\Longleftrightarrow\quad
\rho_y\text{ 可分}
\quad\Longleftrightarrow\quad
\epsilon(1-\epsilon)\ge\frac{\alpha^3}{2}.
$$
置
$$
\epsilon_*=\frac{1-\sqrt{1-2\alpha^3}}2\in(0,1/2).
$$
两种报告的条件态均在 $[0,\epsilon_*)\cup(1-\epsilon_*,1]$ 上纠缠，在闭区间 $[\epsilon_*,1-\epsilon_*]$ 上可分；两个边界均为 PPT，且
$$
\operatorname{rank}\operatorname{PT}_R(\rho_y)=3
\qquad(\epsilon=\epsilon_*\text{ 或 }1-\epsilon_*).
$$
等价的纠缠条件为 $|1-2\epsilon|>\sqrt{1-2\alpha^3}$。同时令 $Q_+=Q_0+Q_1$、$Q_-=Q_0-Q_1$，则
$$
\widetilde Q_0+\widetilde Q_1=Q_+,\qquad
\widetilde Q_0-\widetilde Q_1=(1-2\epsilon)Q_-.
$$
其中 $Q_+$ 是迹为一的可分端点密度。$\epsilon=0$ 给出完整奇偶报告，$\epsilon=1$ 交换两个报告标签，而 $\epsilon=1/2$ 时两个归一化分支均恰为 $Q_+$。

证明。命题 140.1（C）的完整仪器在两条最终记忆列上取偏迹，给出上述 $Q_b\ge0$、正迹 $q_b$ 及其和为一。测量后的奇偶记录与端点联合态为
$$
\sum_{b=0}^1|b\rangle\langle b|\otimes Q_b.
$$
独立经典通道将报告为 $y$ 的项合并为 $\sum_b\Pr(y\mid b)Q_b$，正是所列 $\widetilde Q_y$，没有不同原始记录间的振幅交叉项。其迹是两个严格正数 $q_0,q_1$ 的凸组合，所以对整个闭参数区间均严格为正；除以该迹即得贝叶斯公式。由于 $N_0,N_1$ 的同一非零矩阵元 $01,01$ 均为 $4$，而迹不同，$Q_0/q_0\ne Q_1/q_1$。例如 $\epsilon=1/2$ 时后验仍为 $q_b$，以 $1/2,1/2$ 混合这两个不同密度便与实际后验混合不同。

取任意 $t\in[0,1]$，令 $N(t)=(1-t)N_0+tN_1$。按右偏转置定义逐块转置，得到
$$
A(t):=\operatorname{PT}_R(N(t))
=\begin{pmatrix}d&\operatorname{adj}(v)\\v&B\end{pmatrix},\qquad
d=(10-8t)(1+\alpha),\qquad
v=\begin{pmatrix}6-4t\\(6-4t)(1+\alpha)\\4-4t\end{pmatrix},
$$
$$
B=\begin{pmatrix}4&2&2\\2&4+4\alpha&2\\2&2&2\end{pmatrix}.
$$
对任意 $z=(z_0,z_1,z_2)^{\mathsf T}\in\mathbb C^3$，直接展开有
$$
\operatorname{adj}(z)Bz
=2|z_0|^2+(2+4\alpha)|z_1|^2+2|z_0+z_1+z_2|^2.
$$
三个系数均严格为正；右边为零先迫使 $z_0=z_1=0$，继而 $z_2=0$，故 $B>0$。其分解及行列式为
$$
B=\operatorname{adj}(L)DL,\qquad
L=\begin{pmatrix}1&0&0\\0&1&0\\1&1&1\end{pmatrix},\qquad
D=\operatorname{diag}(2,2+4\alpha,2),\qquad
\det B=8+16\alpha>0.
$$
令 $S(t)=d-\operatorname{adj}(v)B^{-1}v$。对任意 $x\in\mathbb C$ 及 $z\in\mathbb C^3$，完整二次型配方为
$$
\operatorname{adj}\begin{pmatrix}x\\z\end{pmatrix}
A(t)\begin{pmatrix}x\\z\end{pmatrix}
=S(t)|x|^2+
\operatorname{adj}(z+B^{-1}vx)B(z+B^{-1}vx).
$$
变量变换 $(x,z)\mapsto(x,z+B^{-1}vx)$ 可逆且行列式为一。因此 $A(t)$ 与 $\operatorname{diag}(S(t),B)$ 合同，并有
$$
A(t)\ge0\quad\Longleftrightarrow\quad S(t)\ge0,
\qquad \det A(t)=(\det B)S(t).
$$
在这一矩阵族内，$B>0$ 因而使正半定性等价于行列式非负；这一步依赖所证的正定块。

为显式计算标量补量，记 $h=6-4t$、$w=4-4t$，则 $h-w=2$，且由上面的三角分解，
$$
\begin{aligned}
\operatorname{adj}(v)B^{-1}v
&=\frac{(v_0-v_2)^2}{2}
+\frac{(v_1-v_2)^2}{2+4\alpha}+\frac{v_2^2}{2}\\
&=2+\frac{(2+\alpha h)^2}{2+4\alpha}+\frac{w^2}{2}.
\end{aligned}
$$
这里 $v$ 为实向量，故这些平方也等于平方模。乘以 $\det B$ 后逐项展开给
$$
\begin{aligned}
\det A(t)
&=(8+16\alpha)\left((10-8t)(1+\alpha)-2-\frac{(4-4t)^2}{2}\right)
-4\bigl(2+\alpha(6-4t)\bigr)^2\\
&=-32\alpha+64(2+\alpha)t(1-t)
+16(\alpha^2+\alpha-1)\bigl(1+4t(1-t)\bigr)\\
&=-32\alpha+64(2+\alpha)t(1-t).
\end{aligned}
$$
第二行是尚未施加 $\alpha^2+\alpha=1$ 的多项式恒等式，第三行才用该关系。再由 $\alpha^3=2\alpha-1$ 及 $(2+\alpha)\alpha^3=\alpha$，得到
$$
\det A(t)=64(2+\alpha)\left(t(1-t)-\frac{\alpha^3}{2}\right).
$$
由于 $2+\alpha>0$，结合配方即得 $A(t)$ 正半定当且仅当 $t(1-t)\ge\alpha^3/2$；严格反向不等式时 $S(t)<0$，取 $x=1$、$z=-B^{-1}v$ 就给出严格负二次型。

对报告 $y$ 分别取
$$
t_0=\epsilon,\qquad t_1=1-\epsilon.
$$
于是 $t_y(1-t_y)=\epsilon(1-\epsilon)$，且
$$
\operatorname{PT}_R(\widetilde Q_y)=\frac{\alpha^5}{4}A(t_y),\qquad
\operatorname{PT}_R(\rho_y)=\frac{\alpha^5}{4\widetilde q_y}A(t_y),
$$
$$
\det\operatorname{PT}_R(\widetilde Q_y)
=\left(\frac{\alpha^5}{4}\right)^4
\bigl[-32\alpha+64(2+\alpha)\epsilon(1-\epsilon)\bigr],
$$
$$
\det\operatorname{PT}_R(\rho_y)
=\frac{(\alpha^5/4)^4}{\widetilde q_y^4}
\bigl[-32\alpha+64(2+\alpha)\epsilon(1-\epsilon)\bigr].
$$
所有缩放因子均为正，故两报告具有同一个 PPT/NPT 判定。归一化行列式各除以自己的 $\widetilde q_y^4$，不要求两值相等。在等号边界 $S(t_y)=0$ 而 $B>0$，合同式给出右偏转置秩恰为 $3$，同时为正半定。

当偏转置不是正半定时，命题 136.1 证明中使用的 Peres 必要条件排除可分性：若 $\rho=\sum_\nu p_\nu U_\nu\otimes V_\nu$ 是有限凸乘积密度和，则
$$
\operatorname{PT}_R(\rho)=\sum_\nu p_\nu U_\nu\otimes V_\nu^{\mathsf T}\ge0,
$$
因为正矩阵的转置仍正。该必要条件见 Asher Peres，*Separability Criterion for Density Matrices*，Physical Review Letters 77，1413–1415（1996），[DOI:10.1103/PhysRevLett.77.1413](https://doi.org/10.1103/PhysRevLett.77.1413)。

当偏转置正半定时，使用 M. Horodecki、P. Horodecki、R. Horodecki，*Separability of Mixed States: Necessary and Sufficient Conditions*，[arXiv:quant-ph/9605038](https://arxiv.org/abs/quant-ph/9605038)，[第二版定理 3，PDF 第 8 页](https://arxiv.org/pdf/quant-ph/9605038v2)，Physics Letters A 223，1–8（1996），[DOI:10.1016/S0375-9601(96)00706-2](https://doi.org/10.1016/S0375-9601(96)00706-2) 的 $\mathbb C^2\otimes\mathbb C^2$ 充分性：此空间上的密度若 PPT，则可分。这里的 $\rho_y$ 已是该完整空间上的密度，故符合该定理的维数与正性、迹条件。

该文第 3 页以有限凸乘积密度和在迹范数中的闭包定义可分态；它与这里的有限和定义一致。事实上，两个局部密度集合均为有限维紧集，故乘积密度集合
$$
\mathcal P=\{U\otimes V:U,V\ge0,\ \operatorname{Tr}U=\operatorname{Tr}V=1\}
$$
亦紧，且包含在实仿射维数为 $15$ 的四阶迹一 Hermitian 空间中。若一个凸组合含超过 $16$ 个正权重项 $\sum_i p_i R_i$，仿射相关性给出不全为零的实数 $c_i$，满足
$$
\sum_i c_i=0,\qquad \sum_i c_iR_i=0.
$$
其中有正的 $c_i$。取 $\lambda=\min_{c_i>0}p_i/c_i$，将权重改为 $p_i-\lambda c_i$，保持非负性、总和与所表示的态，并至少消去一项。有限次消元将项数降至至多 $16$。因此 $\operatorname{conv}(\mathcal P)$ 是紧集 $\Delta_{15}\times\mathcal P^{16}$ 在连续映射 $((p_i),(R_i))\mapsto\sum_i p_iR_i$ 下的像；这里 $\Delta_{15}=\{p\in\mathbb R^{16}:p_i\ge0,\sum_i p_i=1\}$，不足的项补零权重。这个凸包紧而闭，在有限维迹范数中也闭，故上述闭包没有加入新的态。这便使所引充分性恰好给出本命题所用的有限凸分解意义下的可分性，并与必要条件共同完成两个等价式。

最后，$\alpha^3=\sqrt5-2$ 给
$$
1-2\alpha^3=5-2\sqrt5\in(0,1),\qquad
\epsilon(1-\epsilon)=\frac{1-(1-2\epsilon)^2}{4}.
$$
前一个区间由 $2<\sqrt5<5/2$ 得到。因此两个根为 $\epsilon_*$ 和 $1-\epsilon_*$，分别严格位于 $0$ 与 $1/2$、$1/2$ 与 $1$ 之间；二次式在两根之间达到或超过阈值，外侧严格低于阈值。这证明所列闭中间区间、两外侧区间及记录对比的等价不等式。

经典通道的两条线性式直接相加、相减，便得 $Q_+$ 不变与 $Q_-$ 乘以 $1-2\epsilon$。完整仪器的结果求和等于忽略内部输出，故
$$
Q_+=\operatorname{Tr}_{B_1,B_2,M}\operatorname{outer}(\Xi_4)
=\theta^{P_0}_{0;1,2,1},\qquad P_0=\operatorname{outer}(m_0).
$$
命题 133.1 在纯输入 $P_0$、忽略前缀长度 $0$、两端块长度各为 $1$、忽略间隔长度 $2$ 时给出此密度的可分性。$\epsilon=0,1$ 的两式分别保留、交换 $Q_0,Q_1$。$\epsilon=1/2$ 时 $\widetilde Q_0=\widetilde Q_1=Q_+/2$、$\widetilde q_0=\widetilde q_1=1/2$，故两个条件密度均为 $Q_+$，与阈值判定一致。证毕。

# 情境时空算术的量子扩展：关联、相干与仪器风险

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](072_098_HISTORY_AND_CAPACITY.md) · [续卷](121_141_COHERENT_PREFIXES.md)


<a id="entry-439"></a>

## 追加锚（新终端）

<a id="section-99"></a>

## 99. 单素数轴读数与多素数相关残差

算术卷中的 $$K(n)(p,j)$$ 把每个素数轴上的指数写成一行 Zeckendorf 字串。若把这些轴进一步放进一个有限张量模型，项目的 `single_prime_visible_space` 给出一个精确边界：所有逐轴 Hermitian 读数只能看到空支撑和单轴支撑，不能自动看到两个或更多素数轴之间的相关方向。

<a id="entry-441"></a>

### 99.1 扇区分解

设有限索引集为 $$\iota$$，第 $$i$$ 个局部因子维数为 $$d_i$$。对每个有限支撑集 $$S\subseteq\iota$$，定义一个扇区：在 $$S$$ 上取局部 trace-zero Hermitian 方向，在 $$S$$ 外取标量恒等方向。记该扇区为 $$\mathcal V_S$$。

于是全局 Hermitian 张量空间按支撑集合分解为

$$
\mathsf{Herm}_{\mathrm{global}}
=\bigoplus_{S\subseteq\iota}\mathcal V_S.
$$

空支撑 $$S=\varnothing$$ 是整体恒等方向；单点支撑 $$S=\{i\}$$ 是第 $$i$$ 条局部轴的中心化读数；$$|S|\ge2$$ 则表示跨轴相关方向。

<a id="entry-442"></a>

### 99.2 逐轴读数的完整像

令 `singlePrimeVisibleSpace` 表示由常数和所有完整单因子 Hermitian effect 生成的可见空间。Lean 定理 `single_prime_visible_space` 证明

$$
\boxed{
\mathsf V_{\mathrm{single}}
=\mathcal V_{\varnothing}
\oplus
\bigoplus_{i\in\iota}\mathcal V_{\{i\}}.
}
$$

如果每个扇区维数满足

$$
\dim_{\mathbb R}\mathcal V_S
=\prod_{j\in S}(d_j^2-1),
$$

则逐轴可见空间的维数为

$$
\boxed{
\dim_{\mathbb R}\mathsf V_{\mathrm{single}}
=1+\sum_{i\in\iota}(d_i^2-1).
}
$$

它是逐轴读数的完整线性容量；不是全部全局 Hermitian 空间的维数。

<a id="entry-443"></a>

### 99.3 多轴相关方向的精确盲区

同一定理给出可见空间正交残差

$$
\mathsf R_{\mathrm{multi}}
=\bigoplus_{\substack{S\subseteq\iota\\|S|\ge2}}\mathcal V_S,
$$

以及

$$
\boxed{
\dim_{\mathbb R}\mathsf R_{\mathrm{multi}}
=\left(\prod_{i\in\iota}d_i\right)^2
-1
-\sum_{i\in\iota}(d_i^2-1).
}
$$

因此，只要这个数非零，就存在全局 Hermitian 差异，它对每条单轴读数都为零，却可能在联合 effect 上有非零响应。两因子情形退化为

$$
(d_1^2-1)(d_2^2-1),
$$

与前面二分系统的相关扇区维数一致。

这说明“逐素数轴都读过了”仍不等于“整体历史已经被读出”。逐轴记录保存的是一阶轴向信息；多素数耦合、联合进位或跨轴相位可以落在 $$\mathsf R_{\mathrm{multi}}$$ 中。

<a id="entry-444"></a>

### 99.4 与 $$K(n)$$ 的准确接口

把 $$\iota$$ 取作一个有限素数集合时，可以把算术记录的每条 $$K(n)(p,\cdot)$$ 视为第 $$p$$ 轴的离散标签。但要把上面的维数公式用于量子模型，必须额外指定一个映射

$$
K(n)(p,\cdot)
\longmapsto
\text{第 }p\text{ 个局部 Hilbert 空间中的状态或 effect}.
$$

仓库当前定理只处理给定局部维数、给定扇区分解和给定单因子 Hermitian 读数；它没有从 Zeckendorf 行自动构造这些 Hilbert 空间，也没有把算术乘法的进位自动变成跨因子 Hamiltonian。

所以，若当前任务只询问每个素数轴的指数，单轴可见空间可能足够；若任务询问乘积、规范化进位、跨素数联合概率或联合相位，就必须加入至少一个 $$|S|\ge2$$ 的扇区，或者给出该相关残差对目标读数的误差界。

<a id="entry-445"></a>

### 99.5 对稳定经典接口的后果

本节把“保留多少约束”改写成一个可量化选择：

$$
\boxed{
\text{逐轴经典接口}
\quad\text{vs.}\quad
\text{包含多轴相关的联合接口}.
}
$$

前者的容量是 $$1+\sum_i(d_i^2-1)$$；后者还要承担 $$\mathsf R_{\mathrm{multi}}$$ 中的方向。若后续动力学始终保持单轴可见空间不变，相关残差可以对该任务保持隐藏；若动力学或目标 effect 进入多轴扇区，当前逐轴记录就不再预测闭合。

这与两份算术卷的边界一致：Zeckendorf 唯一表示保证每条轴上的规范坐标，但不保证跨轴联合记录的唯一性、可见性或物理可逆性。稳定的经典现实因此不能由“每条轴都有合法刻度”单独推出，还必须说明哪些跨轴相关是任务允许继续访问的。

本节复用 `single_prime_visible_space`。Lean 已证明的是有限张量族、Hermitian 扇区和完整单因子读数下的可见空间及残差维数；素数轴到物理局部系统的编码、算术进位的联合动力学以及具体 Zeckendorf Hamiltonian 仍是待建接口。

<a id="entry-446"></a>

## 追加锚（新终端）

<a id="section-100"></a>

## 100. 记录份额的阈值：一份隐藏，两份恢复

前面的章节主要按可见算子空间或历史秩计量信息。本节补上一个离散而完整的访问阈值实例：`QutritThresholdSharing` 构造三份 qutrit 记录，使任意单份边缘完全没有输入信息，而任意两份联合访问可以恢复输入振幅。

<a id="entry-448"></a>

### 100.1 三份编码

输入标签取 $$s\in\mathbb Z/3\mathbb Z$$。对每个 $$s$$，编码支持在三元组

$$
(j,\,j+s,\,j+2s),
\qquad j\in\mathbb Z/3\mathbb Z,
$$

上，并以 $$1/\sqrt3$$ 归一化。对任意输入振幅函数 $$\psi(s)$$，这给出一个三 qutrit 联合态。

编码的关键是：单个坐标只保留一个线性组合后的 qutrit，而两坐标的差值携带 $$s$$。这不是把每个记录份额单独写成完整输入副本。

<a id="entry-449"></a>

### 100.2 任意单份边缘完全混合

项目定理 `qutrit_single_share_maximally_mixed` 证明，对任意输入密度态 $$\rho$$ 和任意份额索引 $$i\in\{0,1,2\}$$，取其余两坐标的偏迹后都有

$$
\boxed{
\rho_i
=\frac13 I_3.
}
$$

因此单份记录对输入标签、输入相位和输入混合权重都不携带可读信息。这个结论是完整密度矩阵等式，而不是只比较某一个统计量。

它给出了“当前局部读数相同但整体不同”的一个编码实例：不同 $$\rho$$ 的每个单份边缘都相同，但三份联合态仍然可以不同。

<a id="entry-450"></a>

### 100.3 任意两份的显式恢复

对任意循环相邻的两份，项目定义置换解码

$$
(a,b)\longmapsto(b-a,\,2b-a).
$$

`qutrit_two_share_reconstruction` 证明，应用该置换后，两份联合振幅可写成

$$
\psi(a)
\times
\left[
\frac1{\sqrt3}
\sum_j
\mathbf 1_{(b,r)=(j,j)}
\right],
$$

其中第二因子是与输入无关的固定纠缠因子。于是输入振幅 $$\psi$$ 被恢复到第一解码坐标，剩余坐标只保留固定辅助态。

因此该具体编码满足

$$
\boxed{
\text{任意一份：完全隐藏};
\qquad
\text{任意两份：可逆恢复}.
}
$$

<a id="entry-451"></a>

### 100.4 对历史预算的含义

这个实例说明，“保留几份记录”不能脱离访问协议回答。若未来任务只允许访问一份，所需的经典接口只能报告一个与输入无关的最大混合态；若允许访问两份，联合差分结构立即恢复输入。记录数相同但访问集合不同，也会产生不同的可预测性。

它还区分了三种资源：

$$
\text{份额数量}
\not\equiv
\text{单份边缘信息量}
\not\equiv
\text{联合恢复能力}.
$$

三 qutrit 代码中每份边缘的信息量为零，但两份的联合恢复能力是完整的。故不能用“每份都看不见”推出“整体没有历史”，也不能用“总 Hilbert 维数”直接代替任务所需的最小访问份额。

<a id="entry-452"></a>

### 100.5 与 Zeckendorf 记录的接口

若把有限 Zeckendorf 合法构型分配到多个记录份额，必须先指定编码映射与可访问集合。Fibonacci 合法性只约束哪些构型标签存在；它不自动决定一份记录是否隐藏、两份是否恢复，也不自动产生阈值共享的线性解码器。

可以把三 qutrit 结果作为一个设计模板：选择份额映射，使单份效果落入当前可见空间的核，而联合份额的效果进入目标闭包。随后再用前面的 `all_future_statistics_sufficiency` 或 `future_statistics_iff_annihilates_infinite_system` 检验联合访问是否足以覆盖所需未来统计。

本节复用 `qutrit_single_share_maximally_mixed`、`qutrit_two_share_reconstruction` 和 `qutrit_matrix_unit_marginal`。Lean 已证明的是该三 qutrit 编码的精确偏迹与两份解码；它没有证明任意 Zeckendorf 编码都存在同样的阈值，也没有给出噪声下的最优份额数。

<a id="entry-453"></a>

## 追加锚（新终端）

<a id="section-101"></a>

## 101. Zeckendorf 频率相位与顺序遗失

前面的记录模型说明历史差异可以藏在相位或相关中。本节把算术卷的 Zeckendorf 位直接接到仓库已有的素数频率相位模块，得到一个明确的边界：刻度位可以选择相位频率，但单一标量相位会忘掉步骤顺序。

<a id="entry-455"></a>

### 101.1 Zeckendorf 位选择两种黄金步长

对素数 $$p$$ 和层数 $$\ell$$，项目定义一步频率增量

$$
\omega_{p,\ell}
=
\operatorname{primeLayerFrequency}(p,\ell+1)
-
\operatorname{primeLayerFrequency}(p,\ell).
$$

`prime_step_frequency_zeckendorf` 证明，最低 Zeckendorf 位决定两种频率之一：

$$
\boxed{
\begin{aligned}
2\notin\operatorname{wdigits}(\ell)
&\Longrightarrow
\omega_{p,\ell}=\varphi^2\log p,\\
2\in\operatorname{wdigits}(\ell)
&\Longrightarrow
\omega_{p,\ell}=\varphi\log p.
\end{aligned}
}
$$

相应的单位圆相位为

$$
\Phi_{p,\ell}(t)
=
\exp\!\left(i\,t\,\omega_{p,\ell}\right).
$$

`prime_step_phase_euler` 和 `prime_step_phase_norm` 给出

$$
\Phi_{p,\ell}(t)
=\cos(t\omega_{p,\ell})+i\sin(t\omega_{p,\ell}),
\qquad
|\Phi_{p,\ell}(t)|=1.
$$

所以在这个明确模型中，Zeckendorf 位改变的是旋转速度；它本身不产生衰减。长步还满足

$$
\exp(i t\varphi^2\log p)
=
\exp(i t\varphi\log p)\,
\exp(i t\log p),
$$

因为 $$\varphi^2=\varphi+1$$。这是一条频率分解，不是说物理系统必然存在两个独立的记录寄存器。

<a id="entry-456"></a>

### 101.2 标量相位的交换律会抹掉顺序

对任意有限频率列表 $$(\omega_1,\ldots,\omega_m)$$，定义标量相位积

$$
\Pi(t)
=\prod_{r=1}^{m}\exp(-i t\omega_r).
$$

`ordered_phase_product_collapse` 证明

$$
\boxed{
\Pi(t)
=\exp\!\left(-i t\sum_{r=1}^{m}\omega_r\right).
}
$$

因此任意排列都给出同一个标量结果：

$$
\Pi_{(\omega_1,\ldots,\omega_m)}(t)
=
\Pi_{(\omega_{\pi(1)},\ldots,\omega_{\pi(m)})}(t).
$$

`adjacent_step_order_invisible` 将这个边界写成相邻两步的交换律。它不是说原始历史不存在，而是说**在只保留一个复标量相位的读出中，顺序没有可见坐标**。

这与第 96 节的仪器反例相互补：第 96 节中，静态 POVM 丢掉了分支后的更新；本节中，标量相位读出丢掉了频率序列的排列信息。两者都说明当前读数相同不等于后续过程相同。

<a id="entry-457"></a>

### 101.3 “共振”必须区分相位与振幅

`PrimeGoldenComplexMode` 将一个素数模式写成

$$
M_p(\sigma,t)
=
\exp\!\left(-\sigma\,\lambda_p\right)
\exp\!\left(i t\lambda_p\right),
$$

其中 $$\lambda_p$$ 是指定的黄金素数谱值。于是

$$
|M_p(\sigma,t)|=\exp(-\sigma\lambda_p).
$$

当 $$\sigma>0$$ 时，源码定理 `first_golden_complex_mode_injective_of_pos` 证明模长读出对素数保持单射；当 $$\sigma=0$$ 时，所有模式模长都等于一，而 `finite_zero_sigma_complex_mode_recurrence` 证明有限素数集的相位可以在任意晚时间重新接近完全相干：

$$
\forall\varepsilon>0,\ \forall B>0,
\quad
\exists t>B,
\quad
|M_p(0,t)-1|<\varepsilon
\quad\text{对有限个 }p.
$$

因此“出现振荡”不等于“出现可区分记录”：

$$
\boxed{
\text{振幅衰减提供可校准的大小差异；}
\quad
\text{纯相位运动可以长期回归而不留下单调记录。}
}
$$

<a id="entry-458"></a>

### 101.4 需要什么才能保留历史顺序

若任务只关心总频率 $$\sum_r\omega_r$$，标量相位足够；若任务关心 Zeckendorf 步骤的先后、素数轴切换或进位路径，则至少需要下列一种扩展：

$$
\boxed{
\text{时间分辨的连续读出},
\quad
\text{非交换算子乘积},
\quad
\text{或可再次访问的记忆寄存器}.
}
$$

在非交换升格中，两个步骤一般是

$$
U_2U_1\ne U_1U_2,
$$

顺序才会进入可观测量；在标量 $$U(1)$$ 层，交换律会把这部分信息全部压掉。这个区别与第 97 节的未来分离深度、第 98 节的切口 bond、第 100 节的联合份额访问共同说明：历史预算取决于允许的读出代数，而不是只取决于合法 Zeckendorf 标签的数量。

本节复用 `prime_step_frequency_zeckendorf`、`prime_step_phase_euler`、`long_step_phase_factorization`、`ordered_phase_product_collapse`、`adjacent_step_order_invisible` 和 `complex_mode_amplitude_phase_dichotomy`。Lean 已证明的是这些显式频率—相位模型中的代数关系；它没有证明物理系统必然采用该频率定义，也没有把标量相位自动升级为量子 Hamiltonian 或实验共振谱。

<a id="section-102"></a>

## 102. 时间有序记忆曲率：顺序何时重新进入观测

第 101 节给出一个严格边界：如果每一步只留下一个复标量相位，那么不同频率的乘积落入交换的 $$U(1)$$，步骤排列会被压成总频率。仓库中另一个更强的构造说明，顺序信息并不必然消失；它可以转移到一个被保留、并再次参与演化的记忆坐标。

<a id="entry-460"></a>

### 102.1 同一个完整寄存器上的逐槽演化

`SequentialRegisterCircuit` 把寄存器写成

$$
\operatorname{Register}(A,K,n)=(\operatorname{Fin}(n)\to A)\times K.
$$

第一因子保存已经访问过的物理槽，第二因子是共享记忆。`firstGate` 和 `tailGate` 都是同一个完整 Hilbert 空间上的幺正等距同构；`partial_circuit_succ_gate` 进一步给出：第 $$m+1$$ 步是在保留全部槽的空间上，追加一个明确的局部门

$$
\operatorname{partialCircuit}(U,n,m+1,t)
=
\operatorname{partialCircuit}(U,n,m,t)\circ
\operatorname{slotGate}(U(t+m),n,m).
$$

因此，未被当前读出的槽并没有从整体动力学中删除。它们仍可在以后门中参与作用。对空白初态，`circuit_blank_succ` 与 `circuit_basis_coefficients` 将最终振幅递归为有限链的系数；这正是“历史被保留为可再次访问的寄存器”而不是“历史已经被重新命名为一个当前数值”的形式化版本。

这一区别很重要：若每一步都把旧寄存器替换成新的无记忆环境，可以得到逐步通道的乘法衰减；若同一寄存器继续参与，后续门会看到旧的相关性，顺序效应就可能返回。

<a id="entry-461"></a>

### 102.2 时间有序事件的仿射记忆律

在 `TimeOrderedPrimeMemoryCocycle` 中，一个带时间的事件包含局部标量因子 $$\lambda$$、基准注入 $$b$$、频率 $$\omega$$ 和时间 $$t$$。实际注入为

$$
\widetilde b
=
\exp(-i t\omega)b.
$$

给定稳定因子 $$a$$，它作用在二元状态 $$ (x,m) $$ 上的更新为

$$
(x,m)
\longmapsto
\bigl(a x+\widetilde b\,m,\;\lambda m\bigr).
$$

对事件列表 $$W=(e_1,\ldots,e_n)$$，源码定理 `time_ordered_evolution_affine` 证明整体作用仍是上三角仿射形式：

$$
(x,m)
\longmapsto
\left(
 a^n x+M_a(W)m,
 \Lambda(W)m
\right),
$$

其中 $$\Lambda(W)=\prod_r\lambda_r$$ 是标量词，而 $$M_a(W)$$ 是记忆坐标的有序累积。

对前后两段事件词，`time_ordered_cocycle_append_laws` 给出精确拼接律

$$
\Lambda(W_1W_2)=\Lambda(W_1)\Lambda(W_2),
$$

以及

$$
M_a(W_1W_2)
=
 a^{|W_2|}M_a(W_1)+M_a(W_2)\Lambda(W_1).
$$

第二式不是普通的交换乘法。后发生的词会把先发生的记忆注入乘上稳定传播因子；先发生的标量又会调制后续记忆。顺序因此进入一个半直积样的仿射结构，即使标量坐标本身仍然满足交换乘法。

<a id="entry-462"></a>

### 102.3 两步交换曲率是顺序的最小见证

对两个事件 $$P,Q$$，`time_ordered_two_event_swap_curvature` 证明：交换次序时，标量输出完全相同，而记忆坐标的差为

$$
\Delta_{P,Q}
=
(a-\lambda_Q)\widetilde b_P
-
(a-\lambda_P)\widetilde b_Q.
$$

也就是

$$
\boxed{
M_a(PQ)-M_a(QP)=\Delta_{P,Q}.
}
$$

如果初始记忆为 $$m$$，完整状态的第一坐标差为 $$\Delta_{P,Q}m$$；第二坐标相同。于是：

$$
\text{标量读出相同}
\quad\not\Rightarrow\quad
\text{联合状态相同}.
$$

`PrimeSwapCurvature.prime_swap_curvature_spec` 还证明三件事：

$$
\Delta_{Q,P}=-\Delta_{P,Q},
$$

记忆原点变换

$$
\widetilde b_r\mapsto
\widetilde b_r+(a-\lambda_r)c
$$

不改变 $$\Delta_{P,Q}$$，并且在两个共振间隙非零时，

$$
\Delta_{P,Q}
=
(a-\lambda_P)(a-\lambda_Q)
\left(
\frac{\widetilde b_P}{a-\lambda_P}
-
\frac{\widetilde b_Q}{a-\lambda_Q}
\right).
$$

因此交换曲率不是任意坐标选择造成的假象。它是一个对记忆原点平移不变的顺序缺陷；曲率为零，当且仅当两个事件给出的局部观测者原点估计相同（在非共振条件下）。

<a id="entry-463"></a>

### 102.4 Zeckendorf 频率进入记忆，而不仅是标量相位

把第 101 节的 Zeckendorf 频率选择接入事件频率：

$$
\omega_{p,\ell}
=
\begin{cases}
\varphi^2\log p,&2\notin\operatorname{wdigits}(\ell),\\
\varphi\log p,&2\in\operatorname{wdigits}(\ell).
\end{cases}
$$

则两个事件的有效注入为

$$
\widetilde b_{p,\ell}
=
\exp(-it\omega_{p,\ell})b_{p,\ell}.
$$

Zeckendorf 位仍只决定局部旋转速度；顺序是否可见，取决于这些旋转后的注入是否进入共享记忆，以及稳定因子与局部因子是否产生非零曲率：

$$
\Delta_{P,Q}
=
(a-\lambda_Q)e^{-it_P\omega_P}b_P
-
(a-\lambda_P)e^{-it_Q\omega_Q}b_Q.
$$

所以同一组 Zeckendorf 标签可以有两种完全不同的接口：

$$
\Delta_{P,Q}=0
\quad\Longrightarrow\quad
\text{该记忆读出对这次交换不可见},
$$

而

$$
\Delta_{P,Q}\ne0
\quad\Longrightarrow\quad
\text{在访问记忆坐标的后续实验中，顺序可被区分}.
$$

这把“历史是否存在”改写成了可计算问题：不是问标签是否记录了先后，而是问允许的读出是否包含一个对交换曲率敏感的记忆坐标。

<a id="entry-464"></a>

### 102.5 对“需要保留多少历史”的新结论

现在至少可以区分三个层次：

$$
\boxed{
\begin{aligned}
\text{只保留标量相位}
&\Rightarrow\text{顺序按交换律折叠};\\
\text{保留共享记忆的一维坐标}
&\Rightarrow\text{两步顺序由 }\Delta_{P,Q}\text{ 检验};\\
\text{保留完整寄存器与访问协议}
&\Rightarrow\text{可继续检验更长词的历史回流}.
\end{aligned}
}
$$

因此，“稳定经典现实”所需的历史预算不能只按记录次数或 Zeckendorf 合法字串数量计数。对一个给定实验族，最小预算至少要保留所有会在预测窗口内产生非零交换曲率、回流核或联合恢复效应的坐标。若任务只问总频率，标量接口可能已经闭合；若任务问路径顺序、素数轴切换或可逆恢复，就必须保留共享记忆，或保留足以重建它的寄存器子空间。

本节直接复用 `SequentialRegisterCircuit` 的逐槽幺正组合、`time_ordered_evolution_affine` 的仿射演化、`time_ordered_cocycle_append_laws` 的时间有序拼接律、`time_ordered_two_event_swap_curvature` 的交换缺陷，以及 `prime_swap_curvature_spec` 的反对称性与规范不变性。Lean 已证明这些有限列表和有限寄存器模型中的精确代数关系；它没有证明所有物理系统都具有该记忆坐标，也没有把非零曲率自动等同于实验上已经完成的测量。后者仍取决于实际可访问的读出、噪声模型和预测时间窗。

<a id="section-103"></a>

## 103. 连续可见流与离散隐藏扇区

时间有序记忆说明了“已有记忆怎样让顺序返回”。Solenoid 模块补上另一个边界：有些隐藏差异不是被连续动力学慢慢抹平，而是根本不属于同一个连续路径扇区。

<a id="entry-466"></a>

### 103.1 每条连续历史的唯一分解

`universal_solenoid_visible_hidden_motion_classification` 证明，任意连续历史 $$\gamma:\mathbb R\to\operatorname{UniversalSolenoid}$$ 都有唯一数据

$$
(a,h)\in C(\mathbb R,\mathbb R)\times\operatorname{projection.ker}
$$

使得

$$
\boxed{
\gamma(t)=\operatorname{realFlow}(a(t))+h.
}
$$

其中 $$a(t)$$ 是可见的实流坐标，而 $$h$$ 是恒定的隐藏偏移；`frozen_streamline_throat_component_constant` 进一步把对应隐藏地址写成恒定的 $$\operatorname{hiddenKernelAddEquiv}^{-1}(h)$$。于是，在只允许连续实流操作的实验族中，状态自然分解为

$$
\text{可见相位流}\times\text{隐藏扇区标签}.
$$

这给出了一个比“历史可能存在”更严格的闭合候选：如果任务只允许沿 $$\operatorname{realFlow}(t)$$ 演化，那么隐藏扇区可以作为守恒的块索引；若只看投影，则它是一个潜变量。

<a id="entry-467"></a>

### 103.2 同投影不等于同一连续可达类

同一投影纤维中的两个点不一定能由连续路径连接。`visible_path_hidden_address_dichotomy` 给出

$$
\operatorname{Joined}(x,y)
\iff
\exists t\in\mathbb R,
\quad
 y=\operatorname{realFlow}(t)+x.
$$

更精确地说，底层 `same_fiber_path_orbit_criterion` 将同投影时的可达时间收缩到整数轨道；若两个点的隐藏坐标不同，分类定理构造出非零整数作用

$$
\operatorname{jump}:\mathbb Z\to\operatorname{HiddenAddress}
$$

并证明不存在连续加法流把整数嵌入延拓为该跳跃：

$$
\neg\exists\,\operatorname{flow}:\mathbb R\to\operatorname{HiddenAddress},
\quad
\operatorname{flow}|_{\mathbb Z}=\operatorname{jump}.
$$

因此跨扇区变化若要发生，必须由离散操作、显式记忆寄存器或改变实验协议来承担。它不能被悄悄解释成同一连续相位的更细刻度。

这里有一个必须保留的拓扑限制：该结果说的是连续路径可达性与隐藏地址的刚性，不是说整个空间不连通。源码同时证明 UniversalSolenoid 连通而非道路连通；拓扑连通与连续路径可达是两种不同性质。

<a id="entry-468"></a>

### 103.3 对经典接口的影响

设粗观察只保留投影 $$\pi(x)$$，而不保留隐藏商坐标

$$
 c(x)=\operatorname{QuotientAddGroup.mk'}(\operatorname{range}(\operatorname{realFlowHom}))(x).
$$

对仅由连续实流组成的操作族，有

$$
 c(\gamma(t))=c(\gamma(0)).
$$

所以这类操作下，丢掉 $$c$$ 不会在同一连续扇区内立即造成预测分裂；它只是把不同扇区压进同一个粗标签。可是，一旦实验族加入离散 jump、可访问的隐藏寄存器，或第 102 节中的共享记忆回流，两个原先相同的粗读数就可能在后续被分开。

因此预测闭合必须带有操作族下标：

$$
\text{closure}\bigl(\pi,\mathfrak T_{\mathrm{continuous}}\bigr)
\ne
\text{closure}\bigl(\pi,\mathfrak T_{\mathrm{continuous}}\cup
\mathfrak T_{\mathrm{jump}}\bigr).
$$

这把“保留多少历史”具体化为：先规定允许的时间操作，再判断隐藏扇区是否可以安全商掉。若未来协议允许跨扇区访问，当前的经典接口必须补回 $$c$$，或保留一个能恢复它的记忆寄存器。

本节使用 `visible_path_hidden_address_dichotomy` 与 `universal_solenoid_visible_hidden_motion_classification` 的现成结论。Lean 已证明的是 UniversalSolenoid、连续路径和 HiddenAddress 之间的这些结构关系；它没有证明现实物理系统必然采用该拓扑模型，也没有把“隐藏扇区”自动识别成实验中的某个具体粒子或场。

<a id="section-104"></a>

## 104. 切口 Schmidt 谱：记忆维数之外还要保留哪些历史权重

第 98 节给出了精确相干制备的切口秩下界。`CoherentHistorySchmidt` 进一步计算这个切口中每个边界扇区的权重，因此可以区分“必须保留多少个正交方向”和“哪些方向对当前任务贡献最大”。

<a id="entry-470"></a>

### 104.1 完整历史矩阵按边界因子化

取一个有限占据多重集 $$a$$，把总长度写成

$$
|a|=t+s.
$$

令 $$u$$ 是长度 $$t$$ 的前缀，$$v$$ 是长度 $$s$$ 的后缀。源码定义完整合法词的系数矩阵

$$
C_a^{t,s}(u,v)
=
\\begin{cases}
\\operatorname{multiplicity}(|a|,a)^{-1/2},
&\\operatorname{occupation}(u\\mathbin{+!!+}v)=a,\\\\
0,&\\text{否则}.
\\end{cases}
$$

`coefficient_factorization` 证明它可以经过边界集合分解：

$$
C_a^{t,s}=P_{a,t}Q_{a,t,s},
$$

其中中间指标 $$b\\in\\operatorname{Boundary}(a,t)$$ 记录前缀占据，后缀占据被确定为 $$a-b$$。这说明切口记忆不是任意压缩标签，而是前缀与后缀仍然能够匹配的边界扇区。

选取每个边界的代表词后，`coefficient_diagonal_restriction` 给出一个对角子矩阵：

$$
C_a^{t,s}(u_b,v_c)
=
\\begin{cases}
\\operatorname{multiplicity}(|a|,a)^{-1/2},&b=c,\\\\
0,&b\\ne c.
\\end{cases}
$$

所以 `coefficient_rank` 得到精确等式

$$
\\boxed{
\\operatorname{rank}(C_a^{t,s})
=
|\\operatorname{Boundary}(a,t)|.
}
$$

第 98 节的 bond 下界因此可以被理解为 Schmidt 秩下界：任何精确实现同一纯历史振幅的切口，都必须至少携带这么多彼此独立的边界方向。

<a id="entry-471"></a>

### 104.2 每个边界方向的 Schmidt 权重

源码进一步定义边界 $$b$$ 的 Schmidt 系数

$$
\\lambda_b
=
\\frac{
\\sqrt{\\operatorname{multiplicity}(t,b)}
\\sqrt{\\operatorname{multiplicity}(s,a-b)}
}{
\\sqrt{\\operatorname{multiplicity}(t+s,a)}
}.
$$

`schmidt_coefficient_sq` 和 `schmidt_coefficient_sq_binomial` 证明

$$
\\boxed{
\\lambda_b^2
=
\\frac{
\\operatorname{multiplicity}(t,b)\\,\\operatorname{multiplicity}(s,a-b)
}{
\\operatorname{multiplicity}(t+s,a)
}
=
\\frac{
\\displaystyle\\prod_z
\\binom{a(z)}{b(z)}
}{
\\binom{t+s}{t}
}.
}
$$

这些权重之和为一，因为它们来自完整均匀合法词的边界分解。于是一个切口有两个不同的复杂度量：

$$
\\begin{aligned}
\\text{精确记忆维数}&=|\\operatorname{Boundary}(a,t)|,\\\\
\\text{历史权重分布}&=(\\lambda_b^2)_b.
\\end{aligned}
$$

前者回答“零误差地保留全部相干需要多少维”；后者回答“若只允许近似预测，哪些边界方向承载主要概率质量”。不能从第二个量的集中性直接推出第一个量可以在精确任务中减少。

<a id="entry-472"></a>

### 104.3 精确压缩与近似压缩的边界

若任务要求保留完整纯态的所有振幅，任何丢弃一个 $$\\lambda_b\\ne0$$ 的边界方向都会降低切口 Schmidt 秩，因此不可能由同一较小 bond 精确实现。若任务只要求某个有限观测族的近似预测，可以按权重排序选取一个子集 $$S$$，并定义被丢弃的质量

$$
\\varepsilon_S^2
=
\\sum_{b\\notin S}\\lambda_b^2.
$$

在标准纯态 Schmidt 截断解释下，$$\\varepsilon_S$$ 是态向量级别的尾部范数；但把它转成具体测量概率、迹距离或多步预测误差，还需要指定归一化、测量族和后续动力学。仓库当前定理证明了 $$\\lambda_b$$ 的精确公式，没有自动证明任意截断协议的统一实验误差界。

因此可以把“历史保留多少”拆成两个问题：

$$
\\boxed{
\\begin{aligned}
\\text{精确相干任务:}&\\quad
\\text{保留全部非零边界方向};\\\\
\\text{有限精度任务:}&\\quad
\\text{给定预测族后控制被丢弃 Schmidt 尾部及其回流}.
\\end{aligned}
}
$$

第二行仍要与第 79、86 节的未来 observable 闭包结合。一个很大的 Schmidt 尾部如果完全落在实验不可见方向，未必造成可见误差；一个很小的尾部若被后续操作放大或回流，也不能仅凭当前质量安全丢弃。

<a id="entry-473"></a>

### 104.4 与 Zeckendorf 合法空间的严格接口

对禁止相邻两个 $$1$$ 的 Zeckendorf 合法集合 $$\\mathcal W_L$$，可以把每个合法字串按切口分成前缀和后缀，并令边界集合只保留满足跨切口相邻约束的占据模式。若能证明该受限系数矩阵具有与某个 occupation sector 相同的因子化，则可以把上面的边界秩和 Schmidt 权重转移到 Zeckendorf 模型。

但这一步目前不能直接从 `CoherentHistorySchmidt` 得出。现有定理的词空间是由有限多重集占据约束定义的；它没有证明“禁止相邻 $$11$$”与某个固定多重集 sector 的系数矩阵同构，也没有给出受限边界的闭式 Schmidt 谱。因此目前只能保留如下条件性桥：

$$
\\text{若给定 Zeckendorf 振幅能因子化为边界扇区，}
\\quad
\\text{则其精确切口记忆下界等于该边界矩阵的秩。}
$$

这正是下一步可形式化的具体目标：构造一个带相邻约束的系数矩阵，证明其切口因子化，再比较其秩与 Fibonacci 合法构型数 $$F_{L+2}$$。不能把一般 occupation 的 Schmidt 权重直接冒充 Zeckendorf 量子模型的实验谱。

本节复用 `coefficient_factorization`、`coefficient_rank`、`schmidt_coefficient_sq`、`schmidt_coefficient_sq_binomial` 和 `normalized_coefficient_factorization`。Lean 已证明的是有限占据 sector 的精确切口分解、秩和权重；Zeckendorf 相邻约束的 Schmidt 理论、近似截断的多步误差以及对应的物理编码仍保持为条件性或开放问题。

<a id="section-105"></a>

## 105. 预测商：稳定对象是未来响应的最大不变商

前几节分别给出了切口记忆、共享寄存器和隐藏扇区的例子。它们可以被一个更一般的有限状态构造统一：不是先猜一个“真正对象”的内部标签，而是从当前读出和更新规则反复检查哪些历史在未来仍会分开。

<a id="entry-475"></a>

### 105.1 有限未来关系逐步细化

设状态空间为 $$Y$$，更新为 $$\tau:Y\to Y$$，当前读出为 $$q:Y\to O$$。定义长度 $$m$$ 的未来关系

$$
R_m(y,y')
\iff
q(\tau^k y)=q(\tau^k y')
\quad\text{对所有 }0\le k\le m.
$$

`finite_horizon_kernel_succ_iff` 精确给出

$$
R_{m+1}(y,y')
\iff
R_m(y,y')
\land
q(\tau^{m+1}y)=q(\tau^{m+1}y').
$$

所以每增加一个未来坐标，关系只会细化，不会重新合并：

$$
m\le n\quad\Longrightarrow\quad R_n\subseteq R_m.
$$

若某一对状态在前 $$m$$ 步相同、在第 $$m+1$$ 步第一次不同，`finite_horizon_first_new_coordinate_strict` 证明

$$
R_{m+1}\subsetneq R_m.
$$

这把“隐藏历史何时重新出现”变成一个可枚举的首次分离深度，而不是一句关于无限历史的直觉。

<a id="entry-476"></a>

### 105.2 完整未来核与最大的前向不变关系

把所有未来读出合并为完整 itinerary：

$$
\operatorname{Itin}(y)
=
\bigl(q(y),q(\tau y),q(\tau^2y),\ldots\bigr).
$$

完整未来核为

$$
R_\infty(y,y')
\iff
\operatorname{Itin}(y)=\operatorname{Itin}(y').
$$

`complete_kernel_eq_iInf_finite_horizon` 证明它是有限未来核的无穷交：

$$
R_\infty=\bigcap_{m\ge0}R_m.
$$

更强的 `predictive_completion_maximal_invariant_quotient` 把它刻画为当前读出核中的最大前向不变关系：

$$
R_\infty
=
\operatorname{gfp}(\mathcal R),
$$

其中 $$\mathcal R$$ 保留当前读出相同，并要求关系在 $$\tau$$ 下继续保持。于是 canonical quotient

$$
Y_{\mathrm{pred}}=Y/R_\infty
$$

携带唯一下降的读出与更新。它正是“相对于这组更新和读出，未来响应完全相同”的最粗状态空间。

这里的“最粗”有明确方向：若两个状态在 $$Y_{\mathrm{pred}}$$ 中被识别，它们所有未来读出都相同；若一个摘要仍能精确预测全部未来读出，则它必须细于或等价于这个商。

<a id="entry-477"></a>

### 105.3 任何精确历史接口都因子化到预测商

设另一个记忆摘要为 $$r:Y\to M$$，并且当前读出与更新都通过它因子化：

$$
q=\bar q\circ r,
\qquad
r\circ\tau=\bar\tau\circ r.
$$

`predictive_memory_minimal_quotient` 证明存在唯一映射

$$
\theta:\operatorname{range}(r)\to Y_{\mathrm{pred}}
$$

使得 canonical projection 满足

$$
\operatorname{completionProjection}
=
\theta\circ\operatorname{rangeFactorization}(r).
$$

因此，任何能够精确预测所有未来读出的记忆接口，都会唯一映射到 canonical predictive state。这个结论比“某个编码看起来够用”更严格：它给出所有 exact predictive memories 的共同目标，而不要求先指定哪一个内部标签才是真实对象。

`prediction_completion_universality` 还说明，若当前读出和一步更新已经通过某个粗状态半共轭因子化，那么完整未来 itinerary 自动通过同一个粗状态因子化。换句话说，真正的闭合条件一旦成立，不需要为每个未来时刻重新发明一个独立记录。

<a id="entry-478"></a>

### 105.4 有限状态何时可以停止继续保留历史

若 $$Y$$ 有限，`finite_horizon_stabilizes_at_completionDepth` 给出某个有限深度 $$H_*$$，使

$$
R_{H_*}=R_\infty.
$$

`FiniteHistoryPermanentStability` 的对应结论更局部：如果某一步的相等关系已经不再细化，即

$$
R_m=R_{m+1},
$$

则对所有 $$r\ge0$$ 都有

$$
R_{m+r}=R_m.
$$

所以“现在没有新分离”只有在这个等式对全部状态成立时才是停止证据；一条样本轨迹暂时没有分开，不能推出全局闭合。

在线性有限维模型中，`FutureReadoutQuotient` 给出同一结构的商版本。对状态空间 $$V$$、线性更新 $$T$$ 和读出 $$C$$，隐藏子空间为

$$
\mathcal N_\infty
=
\bigcap_{k\ge0}\ker(C\circ T^k).
$$

商空间 $$V/\mathcal N_\infty$$ 携带唯一诱导动力学，并恢复所有未来读出。`MaximalUnobservableSubspace.future_kernel_is_maximal_invariant` 进一步说明 $$\mathcal N_\infty$$ 是当前不可见空间中最大的 $$T$$-不变部分；这正是“不会在未来回流到可见读出”的隐藏方向，而不是所有当前看不见方向的简单集合。

<a id="entry-479"></a>

### 105.5 与 Zeckendorf 和量子记忆的接口

若把长度 $$L$$ 的 Zeckendorf 合法构型作为初始状态集 $$Y=\mathcal W_L$$，并把一个具体量子或经典更新协议投影成 $$\tau$$ 与 $$q$$，则历史预算应按以下顺序计算：

$$
\boxed{
\begin{aligned}
\text{合法构型数}&=F_{L+2},\\
\text{未来预测商大小}&=|\mathcal W_L/R_\infty|,\\
\text{有限停止深度}&=\min\{m:R_m=R_\infty\},\\
\text{量子精确载体}&\text{还需满足相应切口秩、POVM 或完全正编码约束}.
\end{aligned}
}
$$

第一行是 Zeckendorf 的组合计数；第二、三行依赖实际更新和读出，不能由 Fibonacci 数自动给出；第四行又把预测商与量子可实现性区分开来。若记录通道留下共享相干，经典商可能过早合并状态；若所有未来读出都已在商上闭合，则继续保留更细的历史只增加成本，不增加该任务的预测力。

因此，对“用多少约束保留历史才能得到稳定经典现实”的最精确回答是：先计算允许实验族的完整未来核，再取其最大前向不变商；只有在这个商还能由物理记忆、测量和动力学实现时，它才是一个可交付的经典接口。

本节复用 `finite_horizon_kernel_succ_iff`、`finite_horizon_kernel_antitone`、`complete_kernel_eq_iInf_finite_horizon`、`finite_horizon_stabilizes_at_completionDepth`、`predictive_completion_maximal_invariant_quotient`、`predictive_memory_minimal_quotient`、`prediction_completion_universality` 与 `future_readout_quotient_is_coarsest_with_unique_dynamics`。Lean 已证明的是这些有限状态和有限维线性模型中的核、商与唯一因子关系；将其具体实例化到 Zeckendorf 受限量子通道、噪声环境和实验成本函数，仍是后续形式化目标。

<a id="section-106"></a>

## 106. 操作族扩大后的历史预算：从单一路径到受控闭合

第 105 节固定了一个更新 $$\tau$$。真实的实验协议通常还允许选择输入、脉冲或局部门；此时只检查自然时间序列会低估历史债务。`ControlledFiniteStability` 把未来关系改为对所有有限控制词同时检查。

<a id="entry-481"></a>

### 106.1 控制词关系

令有限状态为 $$Y$$，输入字母为 $$U$$，读出为 $$q:Y\to O$$，每个输入 $$u$$ 给出更新

$$
F_u:Y\to Y.
$$

对输入词 $$w=(u_1,\ldots,u_k)$$，记

$$
F_w=F_{u_k}\circ\cdots\circ F_{u_1}.
$$

深度 $$m$$ 的受控关系定义为

$$
R_m^{\mathrm{ctrl}}(y,y')
\iff
q(F_w(y))=q(F_w(y'))
\quad\text{对所有 }|w|\le m.
$$

空词包含当前读出，所以每个 $$R_m^{\mathrm{ctrl}}$$ 都细于当前读出核。完整关系为

$$
R_\infty^{\mathrm{ctrl}}(y,y')
\iff
q(F_w(y))=q(F_w(y'))
\quad\text{对所有有限控制词 }w.
$$

这比单一 $$\tau$$ 的 itinerary 更强：两个历史可能沿默认路径永远相同，但只要存在一个可执行输入词把它们分开，它们就不能在受控预测商中合并。

<a id="entry-482"></a>

### 106.2 一步稳定即对所有控制词永久稳定

`controlled_finite_stability` 证明，在 $$Y,U,O$$ 都有限、读出满射且非空的条件下，如果某个深度满足

$$
R_m^{\mathrm{ctrl}}=R_{m+1}^{\mathrm{ctrl}},
$$

那么对所有 $$r\ge0$$ 都有

$$
R_{m+r}^{\mathrm{ctrl}}=R_m^{\mathrm{ctrl}}.
$$

原因是一步稳定等价于关系对每一个输入更新都不变；之后任意控制词都只能在这个不变关系内部演化。

完整受控关系还满足最大不动点刻画：

$$
R_\infty^{\mathrm{ctrl}}
=
\operatorname{gfp}(\mathcal R_{\mathrm{ctrl}}),
$$

其中 $$\mathcal R_{\mathrm{ctrl}}$$ 同时要求当前读出相同，并且对每个 $$u\in U$$ 将关系保持在自身中。它也是所有“细于当前读出且对每个控制更新不变的等价关系”中的最大者。

因此，扩大操作族只会细化预测商：

$$
\mathfrak U_1\subseteq\mathfrak U_2
\quad\Longrightarrow\quad
R_\infty(\mathfrak U_2)\subseteq R_\infty(\mathfrak U_1).
$$

一个在单一动力学下看似经典的对象，可能在加入第二种脉冲或局部重排后被分裂。这正是“相对某个操作族稳定”的精确定义。

<a id="entry-483"></a>

### 106.3 深度预算由商类增长支付

定义深度商类数

$$
C_m=|Y/R_m^{\mathrm{ctrl}}|,
\qquad
C_\infty=|Y/R_\infty^{\mathrm{ctrl}}|.
$$

源码证明 $$C_m$$ 单调不减，并给出最小稳定深度 $$H_{\mathrm{ctrl}}$$ 的界：

$$
\boxed{
H_{\mathrm{ctrl}}
\le
C_\infty-|O|
\le
|Y|-|O|.
}
$$

这里使用了读出满射，因此深度零的商类数正好是 $$|O|$$；每一个尚未稳定的深度至少增加一个商类。这个界不是量子 Hilbert 维数界，也不是时间步数的物理定律，而是有限确定性控制模型中的结构预算。

若把长度 $$L$$ 的 Zeckendorf 合法集合作为有限状态集，则

$$
|Y|=|\mathcal W_L|=F_{L+2}.
$$

在一个具体受控更新族上，能够得到的只是

$$
H_{\mathrm{ctrl}}
\le
F_{L+2}-|O|,
$$

以及更精确的 $$C_\infty-|O|$$ 界。不能把 $$F_{L+2}$$ 直接解释成所需历史深度；如果许多合法构型对所有允许控制词都具有相同响应，预测商会远小于原始构型集。

<a id="entry-484"></a>

### 106.4 对经典现实的操作性结论

现在“稳定”必须带有操作族标记：

$$
\boxed{
\text{稳定对象}
=
\text{受控完整响应的最大不变等价类}.
}
$$

如果只允许连续实流，103 节的隐藏扇区可以作为不被跨越的块索引；如果加入离散 jump，它们必须在受控关系中重新测试；如果加入共享量子记忆，控制词还要作用在联合寄存器上，而不能只作用在局部粗读数上。

所以增加约束并不自动产生更稳定的经典现实。约束减少初始合法构型数，操作族却可能增加未来可区分的方向。真正的历史预算是二者的交点：

$$
\text{可行历史接口}
=
\text{合法构型空间}
\big/\text{对全部允许控制词的响应等价}.
$$

本节复用 `controlled_finite_stability` 的最大不变关系、永久稳定和商类深度界。Lean 已证明的是有限状态、有限输入字母和满射读出下的受控闭合；将控制输入提升为连续脉冲、量子仪器序列或含噪声的完全正通道，需要另外定义相应的控制关系和误差度量。

<a id="section-107"></a>

## 107. 黄金禁词相位：局部约束保留，标量端点仍会遗失顺序

第 101 节只说明 Zeckendorf 位可以选择两种相位频率。`GoldenEulerGapWordConstraints` 进一步证明，这些频率并非任意二字母串：Zeckendorf 的局部结构把它们组织成一个带禁词的时间序列。

<a id="entry-486"></a>

### 107.1 两种频率字母

对素数 $$p$$ 和层数 $$\ell$$，定义短、长两种步长

$$
S_p=\varphi\log p,
\qquad
L_p=\varphi^2\log p.
$$

`golden_true_selects_long_frequency` 与 `golden_false_selects_short_frequency` 证明

$$
\operatorname{goldenWord}(\ell)=\mathrm{true}
\Longrightarrow
\omega_{p,\ell}=L_p,
$$

$$
\operatorname{goldenWord}(\ell)=\mathrm{false}
\Longrightarrow
\omega_{p,\ell}=S_p.
$$

因此 Zeckendorf 位不是被动标签，而是频率字母的选择器。

<a id="entry-487"></a>

### 107.2 禁词从位约束传递到相位约束

项目已有的黄金词性质给出两条局部规则：

$$
S_pS_p\quad\text{不会出现},
$$

$$
L_pL_pL_p\quad\text{不会出现}.
$$

`short_frequency_forces_next_long` 证明每个短步之后必为长步；`two_long_frequencies_force_next_short` 证明连续两个长步之后下一步必为短步。通过 `short_phase_forces_next_long` 和 `two_long_phases_force_next_short`，同样的规则传递到

$$
\Phi_{p,\ell}(t)=\exp(i t\omega_{p,\ell})
$$

构成的相位字母：

$$
S\text{-phase}\,\Longrightarrow\,L\text{-phase},
\qquad
LL\text{-phase}\,\Longrightarrow\,S\text{-phase}.
$$

这给出一个比“黄金比例出现了”更严格的结构：合法时间序列属于一个局部受限语言。它与第 102、106 节的历史预算直接相连，因为预测下一步至少需要知道当前的局部禁词上下文。

<a id="entry-488"></a>

### 107.3 局部禁词不等于标量端点可恢复

尽管相位字母满足禁词，若只保留所有步的标量乘积，则

$$
\prod_{r=1}^{m}\exp(i t\omega_r)
=
\exp\left(i t\sum_{r=1}^{m}\omega_r\right).
$$

由交换律，所有满足相同字母计数的排列给出同一端点相位。于是存在这样的情形：两个序列都满足

$$
SS\text{ 不出现},
\qquad
LLL\text{ 不出现},
$$

并且包含相同数量的 $$S$$ 与 $$L$$，但其局部先后不同；它们的标量端点读出仍然相同。

所以局部约束保存了“哪些序列合法”，却没有自动保存“合法序列究竟按什么顺序发生”。要让顺序进入结果，至少要加入一种非交换或有记忆的读出：

$$
\boxed{
\text{时间分辨相位序列}
\quad\text{或}\quad
\text{共享记忆中的有序注入}
\quad\text{或}\quad
\text{非交换事件算子}.
}
$$

第 102 节的交换曲率正是第二种机制；它把相位旋转后的注入带入共享记忆坐标，使两个排列的差异不再被标量交换律抹掉。

<a id="entry-489"></a>

### 107.4 与禁止相邻 $$11$$ 的 Zeckendorf 空间不要混同

本节的黄金相位字母满足的是

$$
SS\text{ 禁止},
\qquad
LLL\text{ 禁止},
$$

而第 79、98、104 节使用的有限 Zeckendorf 构型空间满足的是二进制约束

$$
11\text{ 禁止}.
$$

两者都来自 Fibonacci 型递归，但字母表、状态含义和可实现动力学不同。不能因为它们都出现 Fibonacci 数，就把黄金频率时间序列直接识别成一个禁止相邻激发的量子 Hilbert 空间。

可以建立一个条件性桥：若给定实验把 $$S/L$$ 相位字母编码为合法构型，并且联合更新保持该编码空间，那么第 105、106 节的预测商和受控稳定深度可以应用于这个有限语言。现有 Lean 结果只证明了相位字母的频率选择和禁词继承；它没有证明该相位语言存在唯一的物理寄存器编码，也没有证明其商类数等于某个 Fibonacci Hilbert 维数。

本节复用 `zeckendorf_selects_layer_gap_phase`、`golden_true_selects_long_frequency`、`golden_false_selects_short_frequency`、`short_frequency_forces_next_long`、`two_long_frequencies_force_next_short`、`short_phase_forces_next_long` 和 `two_long_phases_force_next_short`。Lean 已证明的是黄金词约束到频率与相位的精确传递；标量端点的顺序不可见性来自交换乘法，顺序恢复、物理编码和量子噪声下的稳定深度仍需另建模型。

<a id="section-108"></a>

## 108. 合法性记忆不等于历史记忆

前面已经区分了合法构型数、预测商和量子载体维数。`GoldenZeckendorfLanguage` 给出一个最小的反例：判断一个输入是否属于 Zeckendorf 合法语言，只需要记住前一个符号是否为一；但这远远不够回答该输入代表哪个整数、产生哪种相位或怎样参与后续干涉。

<a id="entry-491"></a>

### 108.1 两状态自动机只负责检查局部约束

源码中的状态为

$$
Q=\{\mathrm{clear},\mathrm{previousOne}\}.
$$

转移规则是

$$
\begin{aligned}
\mathrm{clear}\xrightarrow{0}&\mathrm{clear},
&\mathrm{clear}\xrightarrow{1}&\mathrm{previousOne},\\
\mathrm{previousOne}\xrightarrow{0}&\mathrm{clear},
&\mathrm{previousOne}\xrightarrow{1}&\text{非法}.
\end{aligned}
$$

`zeckendorfMSDWord_noAdjacentOnes` 证明任意自然数的规范密集 Zeckendorf 字都满足这个语言约束；`zeckendorfMSDWord_base_success` 则证明这些字都能在该部分自动机中成功执行。

因此，对任务

$$
\text{“当前前缀后面还能不能接一个一？”}
$$

两状态确实是一个充分的有限接口。它保存的是局部合法性所需的最小上下文，而不是完整输入的数值。

<a id="entry-492"></a>

### 108.2 三种不同的“记忆维数”

同一个 Zeckendorf 字可以对应至少三种不同的资源量：

$$
\boxed{
\begin{aligned}
\text{合法性记忆}&=|Q|=2,\\
\text{有限窗口构型载体}&=|\mathcal W_L|=F_{L+2},\\
\text{任务预测或相干记忆}&=\text{由未来商、切口秩和物理编码决定}.
\end{aligned}
}
$$

第一项只回答语言接受问题；第二项列出窗口中可能出现的合法基态；第三项还要考虑允许的更新、测量、相位和恢复操作。把第一项当成第二项，或者把第二项当成第三项，都会低估历史债务。

例如，两个前缀都处于 $$\mathrm{clear}$$ 状态时，它们都允许下一位为一；但它们已经累积的 Fibonacci 权重可能不同，之后的数值读数、素数频率或共享记忆注入也可能不同。自动机状态把这些前缀合并，只在“合法性”这个观察族下闭合。

<a id="entry-493"></a>

### 108.3 合法性商何时可以成为经典对象

设 $$q_{\mathrm{legal}}$$ 只读出自动机状态，$$q_{\mathrm{value}}$$ 读出完整 Fibonacci 数值，$$q_{\mathrm{phase}}$$ 读出后续相位响应。一般有

$$
\ker q_{\mathrm{value}}
\subseteq
\ker q_{\mathrm{legal}},
\qquad
\ker q_{\mathrm{phase}}
\subseteq
\ker q_{\mathrm{legal}},
$$

因为数值和相位任务会区分更多前缀。只有当允许的后续实验族确实只查询合法性，并且更新不把被合并的前缀重新分开时，二状态商才满足第 105、106 节的预测闭合条件。

若加入算术读数、黄金 Euler 相位或量子干涉，必须重新计算完整未来核：

$$
R_\infty^{\mathrm{legal}}
\supseteq
R_\infty^{\mathrm{value}},
\qquad
R_\infty^{\mathrm{legal}}
\supseteq
R_\infty^{\mathrm{phase}}.
$$

商关系越小，所需历史接口越细。于是“约束减少了状态”只对指定观察任务成立；换一个任务，原先被约掉的历史可能重新成为可见差异。

<a id="entry-494"></a>

### 108.4 对量子实现的边界

两状态自动机可以作为一个经典控制器，决定某个量子门是否允许施加；它本身不构成把所有合法字编码为两个正交量子态的物理实现。若要求保留合法构型的相干叠加，至少还要给出

$$
\mathcal H_{Z,L}
=
\operatorname{span}\{|w\rangle:w\in\mathcal W_L\}
$$

的编码、在该空间上保持合法性的联合演化，以及测量和恢复的完全正映射。自动机状态可以附加在寄存器上，但不能替代第 98、104 节中由切口秩决定的相干 bond。

所以一个更准确的分工是：

$$
\text{自动机}
\longrightarrow
\text{约束可执行性},
\qquad
\text{预测商}
\longrightarrow
\text{未来响应闭合},
\qquad
\text{量子寄存器}
\longrightarrow
\text{相干历史与可恢复关联}.
$$

本节复用 `ZeckendorfBaseState`、`zeckendorfBaseStep`、`zeckendorfMSDWord_noAdjacentOnes` 和 `zeckendorfMSDWord_base_success`。Lean 已证明的是规范 Zeckendorf 字的局部合法性和两状态部分自动机的成功执行；它没有证明两状态自动机足以承载数值、相位或任意量子预测任务。

<a id="section-109"></a>

## 109. 禁止相邻 `11` 的均匀态：Fibonacci 标签与 bond 维数分离

现在可以对第 104 节留下的受限 Schmidt 问题做一个完全有限的计算模型。令

$$
\mathcal W_L
=
\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
\qquad
D_L=|\mathcal W_L|=F_{L+2},
$$

并取均匀纯态

$$
|\Psi_L\rangle
=
\frac1{\sqrt{D_L}}
\sum_{w\in\mathcal W_L}|w\rangle.
$$

这一步是一个明确指定的有限量子模型；它不是声称仓库已有的 occupation sector 定理已经覆盖了相邻约束。

<a id="entry-496"></a>

### 109.1 切口只看到两种边界状态

把字串切成长度 $$t$$ 与 $$s$$ 的前后两段，其中 $$t+s=L$$ 且 $$t,s\ge1$$。定义

$$
a_0=\#\{u\in\mathcal W_t:u\text{ 以 }0\text{ 结尾}\},
\qquad
a_1=\#\{u\in\mathcal W_t:u\text{ 以 }1\text{ 结尾}\},
$$

以及

$$
b_0=\#\{v\in\mathcal W_s:v\text{ 以 }0\text{ 开头}\},
\qquad
b_1=\#\{v\in\mathcal W_s:v\text{ 以 }1\text{ 开头}\}.
$$

每个前缀和后缀的内部约束已经在 $$\mathcal W_t$$、$$\mathcal W_s$$ 中满足；跨切口唯一新增的条件是

$$
u\text{ 以 }1\text{ 结尾}
\quad\text{且}\quad
v\text{ 以 }1\text{ 开头}
\quad\Longrightarrow\quad
uv\text{ 非法}.
$$

因此，把所有相同边界类型的前缀、后缀分别归一化后，完整系数矩阵等价于

$$
M_{t,s}
=
\frac1{\sqrt{D_L}}
\begin{pmatrix}
\sqrt{a_0b_0}&\sqrt{a_0b_1}\\
\sqrt{a_1b_0}&0
\end{pmatrix}.
$$

这不是把所有合法字串粗暴合并成一个标签；它是把矩阵中真正相同的行、列向量正交化后得到的精确边界表示。

<a id="entry-497"></a>

### 109.2 精确 Schmidt 秩恒为二

只要 $$t,s\ge1$$，四个边界计数都为正，且

$$
\det M_{t,s}
=
-\frac{\sqrt{a_0a_1b_0b_1}}{D_L}
\ne0.
$$

所以

$$
\boxed{
\operatorname{SchmidtRank}(|\Psi_L\rangle;t|s)=2
\qquad(1\le t,s<L).
}
$$

这给出一个很强的容量分离：合法构型总数随长度按

$$
D_L=F_{L+2}\sim\frac{\varphi^{L+2}}{\sqrt5}
$$

增长，但均匀态跨任意内部切口只需一个两维 bond。Fibonacci 数量描述的是全局标签空间大小；局部相干历史只需记录切口的两个边界状态。

<a id="entry-498"></a>

### 109.3 两个 Schmidt 权重的闭式表达

由于 $M_{t,s}$ 的 Frobenius 范数为一，其两个 Schmidt 权重的平方是 $M_{t,s}M_{t,s}^{\ast}$ 的两个特征值。令

$$
\Delta_{t,s}
=
\frac{a_0a_1b_0b_1}{D_L^2}.
$$

则

$$
\boxed{
\lambda_\pm^2
=
\frac{1\pm\sqrt{1-4\Delta_{t,s}}}{2}.
}
$$

例如，中心切口的直接计算给出：

$$
\begin{array}{c|c|c|c}
L&D_L&\text{切口}&(\lambda_+^2,\lambda_-^2)\\
\hline
2&3&1|1&(0.872677996,\ 0.127322004)\\
3&5&1|2&(0.912310563,\ 0.087689437)\\
4&8&2|2&(0.933012702,\ 0.066987298)\\
5&13&2|3&(0.923076923,\ 0.076923077)\\
6&21&3|3&(0.910325903,\ 0.089674097)\\
8&55&4|4&(0.919070203,\ 0.080929797)\\
10&144&5|5&(0.915739710,\ 0.084260290)
\end{array}
$$

数值表只用于展示这个明确矩阵模型的谱；它不是对真实实验参数的测量，也不是当前 Lean 中的认证数值定理。

<a id="entry-499"></a>

### 109.4 这对历史预算意味着什么

若任务是精确制备均匀合法态并允许任意切口上的相干恢复，则两维 bond 已经足够承载这个特定态族的全部跨切口相关；不需要为每个 $$F_{L+2}$$ 个合法字串分配一个独立的切口记忆槽。

若任务改为区分每个合法字串、读取完整 Fibonacci 数值，或允许能访问字串内部位置的控制操作，则预测商会变细，所需接口可能重新随 $$L$$ 增长。于是必须区分

$$
\text{均匀态的相干 bond}
\quad\ne\quad
\text{所有构型的可区分记录容量}.
$$

这也解释了第 108 节的两状态自动机为何不矛盾：自动机和两维 bond 都只是在特定任务中保留边界信息；它们都没有声称能完成所有数值和量子任务。

<a id="entry-500"></a>

### 109.5 形式化边界

本节的矩阵 $M_{t,s}$、秩为二和谱公式是从有限集合的直接计数与 $2\times2$ 线性代数得到的组合推导，目前没有冒充为仓库已有 Lean 声明。下一步若要把它纳入唯一真源，需要在 D5 中定义相邻约束词空间、前后缀边界计数和对应系数矩阵，再证明其行列因子化与行列式非零。

一旦完成这一步，才能把

$$
F_{L+2}\quad\text{与}\quad 2
$$

的分离从一个可复算模型升级为形式化定理；在此之前，它只承担研究报告中的明确、可检验桥接。

<a id="section-110"></a>

## 110. 同一 Zeckendorf 语言的任务依赖状态复杂度

第 108 节的两状态自动机只检查“是否出现相邻两个一”。仓库还给出一个任务复杂度完全不同的对照：对同一类规范 Zeckendorf 输入，若任务是计算黄金比例的稀疏 radix-4 输出，则状态下界可以大得多。

<a id="entry-502"></a>

### 110.1 合法性任务只需两状态

`ZeckendorfBaseState` 只有

$$
\{\mathrm{clear},\mathrm{previousOne}\},
$$

因此验证局部合法性只需保存一个比特级上下文：前一位是否为一。`zeckendorfMSDWord_base_success` 证明每个规范 Zeckendorf 输入都能在这个部分自动机中成功运行。

这个自动机并不输出输入代表的整数，也不计算黄金比例的 radix-4 数字。它的闭合任务只有语言成员关系。

<a id="entry-503"></a>

### 110.2 算术输出任务需要保存更多可区分前缀

`GoldenBase4AutomataOracle` 定义了另一项任务：输入是

$$
\operatorname{zeckendorfMSDWord}(4^i),
$$

输出是

$$
\left\lfloor 4^{i+1}\varphi\right\rfloor
-4\left\lfloor4^i\varphi\right\rfloor,
$$

的 radix-4 数字。此时前缀不仅要保持合法性，还要保留足以决定未来输出的算术信息。

源码中的 `phi_base4_twenty_two_state_minimality` 给出条件性最小性结论：若存在一个 22 状态全局模型，并且对 21 状态模型的指定有限前缀反驳已经由 LRAT 证书提供，则

$$
\operatorname{IsMinimalStateCount}(\operatorname{base4Problem},22).
$$

对应的 M16 定理直接排除至多 21 状态的模型，但它的使用条件仍是显式的有限反驳证书。这里不能把“22”脱离这些前提写成无条件的现实物理常数。

<a id="entry-504"></a>

### 110.3 这与量子历史预算是同一类区别

两种任务的状态数对照为

$$
\begin{array}{c|c|c}
\text{任务}&\text{必须保留的关系}&\text{现有状态规模}\\
\hline
\text{检查 Zeckendorf 合法性}&\text{最近一位的局部约束}&2\\
\text{计算稀疏黄金 radix-4 输出}&\text{未来算术输出等价类}&\text{条件性至少 }22\\
\text{均匀禁止相邻态的局部相干}&\text{切口边界}&2\\
\text{完整量子预测}&\text{未来 effect/仪器词闭包}&\text{由商空间与载体决定}
\end{array}
$$

因此“约束只产生两个状态”和“这个系统只需要两个状态”是不同命题。前者只关于一个局部语言；后者必须对指定的所有后续操作和输出任务成立。

<a id="entry-505"></a>

### 110.4 对稳定经典现实的修正

如果观察者只问一个局部约束问题，二状态摘要可以是稳定经典对象。若观察者随后要求数值解码、黄金相位预测、不同控制词下的输出，二状态摘要通常不再满足第 105、106 节的预测闭合条件。对应的最小对象应改为

$$
\text{当前前缀}/\text{未来任务响应等价},
$$

而不是

$$
\text{当前前缀}/\text{局部合法性等价}.
$$

量子模型中完全相同：一个两维边界 bond 可以精确承载第 109 节的均匀相干态，但不能因此承载所有合法构型的任意数值、相位和恢复协议。任务一旦扩大，预测商会细化，必须重新计算历史预算。

本节复用 `zeckendorfMSDWord_base_success`、`m16_phi_base4_exclude_at_most_twenty_one` 和 `phi_base4_twenty_two_state_minimality`。Lean 已证明的是两状态合法性执行以及带上界模型和 LRAT 反驳前提的状态最小性接口；它没有把 22 状态结论无条件推广到所有 Zeckendorf 任务，也没有把自动机状态数等同于量子 Hilbert 维数。

<a id="section-111"></a>

## 111. 预测商的条件熵下界：标签、bond 与信息成本

前几节已经区分了三种容易混淆的数量：合法构型的总数、一个特定量子态跨切口所需的 Schmidt bond，以及为未来预测而必须保留的状态数。仓库中的 `PredictiveMemoryEntropyLowerBound.lean` 再增加一个可以直接比较的量：**在当前读出已经给定以后，记忆还必须携带多少条件熵。**

<a id="entry-507"></a>

### 111.1 精确预测记忆的定义

设有限状态集合为

$$
X
$$

当前读出为

$$
q:X\to O,
$$

一步更新为

$$
F:X\to X,
$$

候选记忆接口为

$$
r:X\to M.
$$

源码中的 `IsExactPredictiveMemory q F r` 要求存在两个因子化：当前读出可以由记忆恢复，且更新后的记忆仍只依赖旧记忆。用普通数学语言写成，就是存在

$$
\bar q:M\to O,
\qquad
\bar F:M\to M
$$

使得

$$
q=\bar q\circ r,
\qquad
r\circ F=\bar F\circ r.
$$

第一条保证当前观测不会被记忆丢掉；第二条保证记忆接口对下一步操作闭合。它把前面讨论的预测闭合落实为记忆接口条件：

$$
r\circ F=\bar F\circ r.
$$

这里还显式保留当前读出因子化条件。

<a id="entry-508"></a>

### 111.2 canonical predictive quotient 是所有 exact memory 的共同下界

由更新和当前读出共同决定的 canonical predictive projection 记作

$$
\pi_{F,q}:X\to Q_{F,q}.
$$

它把两个状态归并，当且仅当它们在当前读出下相同，并且在所有后续迭代中都保持相同的可预测响应。`MinimalPredictiveCompletionQuotient.lean` 以最大 forward congruence 的商实现了这一构造：它保持当前读出，承载更新，并且其投影能够因子化通过任意满足相同闭合条件的商。

因此，对于任意 `IsExactPredictiveMemory q F r`，canonical projection 在每个记忆纤维上都是常值的。于是它在实现的记忆像

$$
r(X)\subseteq M
$$

上因子化为

$$
g:r(X)\to Q_{F,q},
\qquad
\pi_{F,q}=g\circ r.
$$

若另加非空状态假设，或只讨论非零质量分支，可以选择一个延拓到整个记忆类型的函数；零状态情形不应无条件声称存在这样的全域函数。这句话的方向很重要：canonical predictive state 是候选记忆中必然包含的预测信息，而不是任意标签都能替代它。若两个历史在

$$
\pi_{F,q}
$$

中不同，任何 exact memory 都必须把它们放在可区分的记忆纤维中；否则某个后续读出会把它们分开。

<a id="entry-509"></a>

### 111.3 条件熵下界

给定一个非负质量函数

$$
\mu:X\to\mathbb R,
\qquad
0\le\mu(x),
$$

定义当前读出与记忆状态的联合质量

$$
J_{q,s}(o,z)
=
\sum_{x:(q(x),s(x))=(o,z)}\mu(x).
$$

那么仓库定理 `predictive_memory_entropy_lower_bound` 精确证明：

$$
\boxed{
H\bigl(\pi_{F,q}\mid q\bigr)
\le
H\bigl(r\mid q\bigr).
}
$$

这里的熵是由上述联合质量计算的条件 Shannon 熵；定理允许质量函数只是非负而未预先归一化。总质量为零时两边都退化为零；总质量为正时，证明把该质量函数归一化，应用条件熵的数据处理不等式，再乘回总质量。因而这不是把“概率”偷偷扩展成任意带符号的线性权重。

定理中的数学关系可以压缩成：

$$
\pi_{F,q}=g\circ r
\quad\Longrightarrow\quad
H(\pi_{F,q}\mid q)\le H(r\mid q).
$$

右侧记忆可能包含额外的、对预测无用的历史；左侧只保留在未来实验中不可省略的部分。于是 canonical quotient 不只是商类最粗，还在这个有限质量模型中给出条件熵意义下的最低记忆成本。

<a id="entry-510"></a>

### 111.4 与 Fibonacci 构型数和 Schmidt bond 的三重分离

对禁止相邻两个一的长度

$$
L
$$

合法语言，构型总数是

$$
|\mathcal W_L|=F_{L+2}.
$$

第 109 节的均匀态在任意非平凡切口上只有二维有效边界矩阵，所以其 Schmidt rank 为

$$
\operatorname{SchmidtRank}=2.
$$

而第 111 节的预测商条件熵是另一种量：它取决于选定的当前读出、更新、允许的未来操作族，以及质量函数。即使把质量函数归一化为概率，使指数熵具有无量纲解释，也一般不存在等式

$$
F_{L+2}
=
2
=
\exp H(\pi_{F,q}\mid q).
$$

这三个量分别回答不同问题：

$$
\begin{array}{c|c}
\text{量}&\text{回答的问题}\\
\hline
F_{L+2}&\text{有多少个合法构型}\\
2&\text{这个特定均匀态跨切口需要多少相干边界维度}\\
H(\pi_{F,q}\mid q)&\text{当前读出已知后，为预测未来还需保留多少平均信息}
\end{array}
$$

例如，若当前读出已经把所有合法字串区分开，则

$$
H(\pi_{F,q}\mid q)=0,
$$

即使合法构型数仍为

$$
F_{L+2}
$$

因为当前读出已经携带了全部预测商信息。反过来，若当前质量所支持的历史都落在同一个当前读出纤维中，而更新把它们送到当前读出可以区分的后续状态，则预测商可以在该支持上分成

$$
k
$$

个等质量的未来响应类。质量归一化为概率后，条件熵可以达到

$$
H(\pi_{F,q}\mid q)=\log k.
$$

这时任何 exact memory 的条件熵都至少为

$$
\log k.
$$

这里的

$$
k
$$

与 Fibonacci 构型总数没有必然相等关系。

<a id="entry-511"></a>

### 111.5 非负质量不是装饰性条件

同一 Lean 文件中的 `nonnegative_mass_is_necessary` 给出带符号质量的反例：在两点状态上取质量

$$
2
$$

与

$$
-1,
$$

identity memory 仍然是 exact predictive memory，但条件熵下界会失败。原因不是 canonical quotient 失去共轭性，而是 Shannon 熵的数据处理不等式需要非负、可归一化的质量。

因此，以下三句话必须分开：

$$
\text{线性振幅可以是复数，}
$$

$$
\text{形式上的 signed weight 可以用于代数恒等式，}
$$

$$
\text{条件 Shannon 熵的输入必须是非负质量。}
$$

量子振幅的相位不能直接当作熵的概率权重。若要把第 111 节用于量子模型，必须先指定正的 Born 概率、密度矩阵对角分布，或其它明确的正测度。

<a id="entry-512"></a>

### 111.6 对“需要保留多少历史”的精确回答

结合前面的 Zeckendorf 约束、Schmidt 分解和预测闭合，当前问题可以写成四步：

$$
\text{合法构型空间}
\longrightarrow
\text{选定读出 }q
\longrightarrow
\text{计算未来响应商 }\pi_{F,q}
\longrightarrow
\text{比较 }H(\pi_{F,q}\mid q)\text{ 与候选记忆成本}.
$$

若候选接口

$$
r
$$

达到 exact predictive memory 条件，并且其条件熵等于 canonical 下界，则在这个质量与任务下，它没有产生额外的条件熵成本；这不单独排除零质量纤维上的冗余标签。若严格大于下界，说明在这个质量和任务下存在额外的平均记忆成本；若小于下界，则它不可能仍然精确预测全部指定未来读出。

这给“稳定经典现实”一个可计算的有限版本：不是要求记忆保存全部历史，也不是只保存当前整数标签，而是保存足以使

$$
\pi_{F,q}=g\circ r
$$

成立的那部分关系，并在给定误差预算下使剩余回流可以忽略。Zeckendorf 的

$$
F_{L+2}
$$

只规定合法构型的组合规模；Schmidt bond 只规定某个态族的跨切口相干规模；条件熵下界才开始回答当前观察已经给定以后，未来预测还必须保留多少历史信息。

<a id="entry-513"></a>

### 111.7 形式化边界与下一步

本节直接复用仓库已有的 `minimal_predictive_completion_quotient`、`predictive_memory_entropy_lower_bound` 与 `nonnegative_mass_is_necessary`。Lean 已证明的是有限类型、确定性更新、非负有限质量和精确记忆接口下的条件熵下界，以及带符号质量会破坏该不等式。它没有证明任意无限链、任意量子通道或任意实验噪声下都存在同一个有限熵预算。

要把它接到前面的 Zeckendorf 量子模型，还需额外指定并分别验证：

$$
\text{合法字串状态 }X,
\qquad
\text{实际更新 }F\text{ 或量子通道的有效状态更新},
$$

$$
\text{当前读出 }q,
\qquad
\text{非负的 Born 质量（总质量可为零） }\mu,
$$

以及未来操作族是否比单一步更新更丰富。若未来允许的控制词不止迭代更新，就必须把它们加入预测商的定义；不能把单一步闭合误报成对所有仪器和所有历史协议的闭合。上面的熵例子也只是在指定质量支持和后续读出结构下的条件性组合，不是对全局常数读出的断言。

所以，当前最稳固的研究命题是：

$$
\boxed{
\text{在固定读出、更新和非负有限质量之后，}
\text{canonical predictive quotient 给出 exact memory 的条件熵下界。}
}
$$

它把“保留多少历史才能得到稳定现实”从一个总量问题，改写成了一个可逐任务计算的问题：先确定未来响应等价，再测量任何候选记忆相对于当前读出的剩余信息成本。


<a id="section-112"></a>

## 112. 保留模数的乘积容量：算术记录何时足以恢复历史

第 111 节给出了预测任务下的条件熵下界。另一个更离散的问题是：如果记录接口只保留若干个模数余数，什么时候这些记录足以把一个有限状态集合完全恢复出来？仓库中的 RetainedResidueRecoveryCriterion.lean 给出一个精确的双向判据。

<a id="entry-515"></a>

### 112.1 联合余数记录

设有限索引集合为

$$
\iota,
$$

每个索引携带一个正模数

$$
m:\iota\to\mathbb N,
\qquad
0<m(i),
$$

并假设这些模数两两互素：

$$
\operatorname{Pairwise}\bigl(\operatorname{Nat.Coprime}\;\mathrm{on}\;m\bigr).
$$

对状态区间

$$
\operatorname{Fin}(K)=\{0,1,\ldots,K-1\},
$$

保留的记录是联合余数读出

$$
R(x)
=
\bigl(x\bmod m(i)\bigr)_{i\in\iota}.
$$

在 Lean 中，这个读出由 jointReadout 组织，余数坐标以

$$
\mathbb Z/m(i)\mathbb Z
$$

表示。它不是把原始历史直接写回，而是把历史压缩到一组可组合的局部记录中。

<a id="entry-516"></a>

### 112.2 精确恢复的充要条件

retained_residue_recovery_iff_product_capacity 证明：

$$
\boxed{
R\text{ 在 }\operatorname{Fin}(K)\text{ 上单射}
\quad\Longleftrightarrow\quad
K\le\prod_{i\in\iota}m(i).
}
$$

正向部分只是有限单射导致的基数不超过目标基数。反向部分使用有限模数的乘积同构：两两互素使联合余数同构于乘积模数，若

$$
0\le x,y<K\le\prod_i m(i)
$$

且所有保留余数相同，那么

$$
x\equiv y\pmod{\prod_i m(i)}.
$$

由于 x 和 y 都落在一个完整模周期内，只能有

$$
x=y.
$$

这里的“容量”是乘积，而不是模数个数。增加一个与已有模数互素的新记录通道，会把可无歧义恢复的状态范围按该模数倍增；但若新通道与已有通道不互素，不能直接使用同一个乘积公式。

<a id="entry-517"></a>

### 112.3 与 Zeckendorf 合法构型的连接

长度参数为 L 的禁止相邻两个一语言有

$$
|\mathcal W_L|=F_{L+2}
$$

个合法构型。若先给这些构型一个双射标签

$$
e:\mathcal W_L\to\operatorname{Fin}(K),
\qquad
K=F_{L+2},
$$

再用保留模数记录标签，那么由第 112 节的判据，完整恢复所有合法构型的充分且必要条件是

$$
F_{L+2}
\le
\prod_{i\in\iota}m(i).
$$

这只是一个条件性组合桥：它要求先固定一个有限编码

$$
e
$$

以及实际使用的余数记录。Lean 定理本身证明的是任意有限区间

$$
\operatorname{Fin}(K)
$$

上的恢复，不自动构造 Zeckendorf 语言到区间的双射，也不说明物理系统真的读取这些模数。

在最小例子中，

$$
\mathcal W_3=\{000,001,010,100,101\},
\qquad
|\mathcal W_3|=5.
$$

保留模数

$$
2,\quad3
$$

时乘积为

$$
6,
$$

因此任何先编码为

$$
\operatorname{Fin}(K),
\qquad
K\le6,
$$

的有限状态都可以由这两个余数联合恢复。若只保留模数

$$
2,
$$

容量只有

$$
2,
$$

最多只能无歧义表示两个状态；五个合法构型不能全部由单个二模余数区分。

<a id="entry-518"></a>

### 112.4 这不是 Hilbert 维数，也不是预测熵

乘积容量回答的是一个严格的可逆编码问题：

$$
\text{给定记录，能否唯一恢复有限标签？}
$$

它不等同于以下数量：

$$
F_{L+2},
\qquad
\operatorname{SchmidtRank},
\qquad
H(\pi_{F,q}\mid q).
$$

前者统计合法构型；Schmidt rank 描述特定量子态跨切口的线性相关维度；条件熵下界描述给定当前读出后未来预测所需的平均信息。模数乘积则描述一套离散记录接口的最坏情形无歧义容量。

例如，若当前任务只需判断一个局部约束是否合法，二状态自动机可能已经闭合；若任务要求恢复所有

$$
F_{L+2}
$$

个合法构型，就必须检查记录容量是否达到该数值。若任务只要求预测后续动力学，完整恢复甚至可能过度，因为不同构型可能属于同一个未来响应类。于是：

$$
\text{完整历史恢复容量}
\quad\ge\quad
\text{任务预测所需容量}
$$

一般只是任务依赖的比较关系，不是普适的数值等式。

<a id="entry-519"></a>

### 112.5 与素数指数档案的边界

项目中的

$$
K(n)(p,j)=s\bigl(v_p(n)\bigr)_j
$$

把每个素数轴上的指数写成 Zeckendorf 行。第 112 节的余数读出可以作为另一种有限记录协议，例如对选定的状态标签保留若干互素模数；但它没有把素数指数轴自动变成余数轴，也没有证明某个具体的

$$
K(n)
$$

在余数记录下可逆。

要建立这样的桥，至少还需指定：

$$
\text{原始档案空间},
\qquad
\text{有限截断范围},
\qquad
\text{余数记录作用在哪个数值或标签上}.
$$

只有在这些数据固定后，才能把

$$
K\le\prod_i m(i)
$$

解释为该档案截断的恢复条件。否则把“素数轴很多”直接等同于“历史记录容量很大”，会把坐标数量误当成可逆信息量。

<a id="entry-520"></a>

### 112.6 对稳定经典现实的补充判据

第 111 节说，稳定对象应当保留未来预测所需的 canonical quotient。第 112 节补充了一个更强、也更昂贵的选择：如果要求对象保留全部有限标签，而不是只保留预测等价类，那么必须提供一个对该标签集单射的记录接口。

因此可以区分两种预算：

$$
\text{预测预算}
=
\text{使未来响应可闭合的最小记忆},
$$

$$
\text{恢复预算}
=
\text{使目标历史标签可逆的最小记录容量}.
$$

对余数协议，恢复预算由

$$
\prod_i m(i)
$$

控制；对预测协议，预算由

$$
H(\pi_{F,q}\mid q)
$$

及其误差版本控制。恢复预算通常更高，因为它拒绝把未来行为相同的历史合并。

这使“用多少约束才能得到稳定经典现实”有了两层可检验答案：

$$
\boxed{
\begin{aligned}
&\text{若只要求稳定预测：计算 canonical predictive quotient；}\\
&\text{若要求完整历史可恢复：检查记录容量是否覆盖目标标签集。}
\end{aligned}
}
$$

两者都不自动给出物理 Hamiltonian 或量子测量定律；它们分别刻画关系结构的预测闭合和离散记录的可逆性。

<a id="entry-521"></a>

### 112.7 形式化边界

Lean 已证明的是正的两两互素模数、有限索引族和有限状态区间上的精确单射充要条件。它没有证明 Zeckendorf 合法语言的某个具体物理实现会采用这些模数，也没有把乘积容量转译成 Hilbert 空间维数、实验信道容量或量子纠错阈值。

因此第 112 节当前最强的可复用结论是：

$$
\boxed{
\text{在两两互素的保留余数协议中，}
\operatorname{Fin}(K)\text{ 可被精确恢复}
\iff
K\le\prod_i m(i).
}
$$

把它应用于 Fibonacci 合法构型、素数指数档案或量子记录，都必须另外给出编码、读出和物理实现的桥接假设。


<a id="section-113"></a>

## 113. 粗粒化不能凭空增加经典互信息

第 112 节讨论的是保留记录是否仍然可逆。第 113 节处理另一种更弱的要求：即使不要求恢复全部历史，确定性的粗粒化也不应凭空制造原始记录中没有的经典相关。仓库中的 CoarseGrainingCannotAddInformation.lean 对有限、归一化的联合律给出了这个方向的不等式。

<a id="entry-523"></a>

### 113.1 从微观联合律到粗记录

设微观状态为有限集合

$$
X,
$$

两次相邻记录的联合质量为

$$
p:X\times X\to\mathbb R,
$$

并满足

$$
p(z)\ge0,
\qquad
\sum_z p(z)=1.
$$

设确定性的记录压缩为

$$
c:X\to C.
$$

粗粒化后的联合律把所有具有相同粗标签的微观对相加：

$$
p_c(a,b)
=
\sum_{\substack{x,y\in X\\c(x)=a,\ c(y)=b}}p(x,y).
$$

在项目定义中，这个对象叫作 coarseGrainedJoint。它描述的是同一份经典联合记录经过确定性标签压缩后的统计，而不是一次新的物理相互作用。

<a id="entry-524"></a>

### 113.2 互信息数据处理不等式

Lean 定理 coarse_graining_cannot_add_information 精确证明：

$$
\boxed{
I_{p_c}(C_{\mathrm{past}};C_{\mathrm{future}})
\le
I_p(X_{\mathrm{past}};X_{\mathrm{future}}).
}
$$

证明把右坐标的确定性映射写成一个 Markov channel，先应用一次互信息数据处理，再交换左右坐标并应用第二次。非负性与总质量为一是定理的必要输入，因为仓库中的 mutualInformation 是有限 Shannon 量。

因此，若只是把历史标签重新命名、合并或忘掉部分坐标，就不会让过去与未来的经典互信息增加。粗粒化可能保留一部分相关，也可能把相关抹掉，但它不能从零生成新的经典相关。

<a id="entry-525"></a>

### 113.3 与“观测改变现实”的边界

这条不等式不能推出“任何观测都没有物理影响”。它只描述一个特定操作：

$$
\text{同一份经典联合律}
\longrightarrow
\text{确定性标签映射}
\longrightarrow
\text{新的边缘化联合律}.
$$

如果中间步骤实际施加了量子通道、写入环境记录、重置仪器，或改变了后续 Hamiltonian，那么后续联合律已经不是原来的

$$
p
$$

经过单纯标签函数得到的

$$
p_c.
$$

此时应把相互作用本身纳入新的通道模型，再分别计算输入和输出的互信息。第 113 节只阻止把“压缩标签”误报成“凭空增加信息”，不阻止物理操作改变系统的相关结构。

<a id="entry-526"></a>

### 113.4 与预测商和余数容量的关系

第 111 节的 canonical predictive quotient 追问：

$$
\text{为了预测未来，最少要保留哪些区别？}
$$

第 112 节的乘积容量追问：

$$
\text{为了可逆恢复目标标签，记录接口能承载多少状态？}
$$

第 113 节追问：

$$
\text{把这些标签粗粒化以后，还剩多少过去—未来相关？}
$$

三者作用不同。一个粗标签映射可能满足

$$
I(p_c)<I(p),
$$

但仍然保留完整的预测商；也可能因为把预测上必需的纤维合并而破坏后续闭合。反过来，一个足容量的余数接口可以保持标签可逆，却携带远超当前预测任务所需的冗余信息。

因此不能从互信息单调性单独推出最小记忆，也不能从记录容量单独推出预测充分性。需要同时检查：

$$
\text{可逆性},
\qquad
\text{预测闭合},
\qquad
\text{相关信息损失}.
$$

<a id="entry-527"></a>

### 113.5 一个零相关的边界例子

若微观联合律是独立律

$$
p(x,y)=p_1(x)p_2(y),
$$

则

$$
I_p(X_{\mathrm{past}};X_{\mathrm{future}})=0.
$$

确定性粗粒化后仍有

$$
I_{p_c}(C_{\mathrm{past}};C_{\mathrm{future}})=0.
$$

这说明粗粒化不能把没有的经典相关变出来。它不表示粗粒化后的变量没有意义；它们仍可能对某个单时刻任务有用，只是不能被解释成过去对未来的额外共享信息。

<a id="entry-528"></a>

### 113.6 形式化边界

Lean 已证明的是有限类型、非负归一化联合律和同一个确定性粗粒化映射作用于两个坐标时的互信息不增。它没有证明量子互信息在任意测量协议下的完整演化，也没有把经典互信息直接等同于第 111 节的条件熵成本或第 112 节的可逆容量。

所以，第 113 节当前可复用的结论是：

$$
\boxed{
\text{确定性经典粗粒化不能增加有限联合律的互信息；}
}
$$

而“观测是否改变现实”仍需另外指定观测通道、环境记录和后续动力学。把标签压缩、物理测量和量子退相干写成同一个动作，会丢掉它们之间最关键的区别。


<a id="section-114"></a>

## 114. 记录细化的创新能量：从条件熵到预测风险

第 111 节的条件熵比较的是记忆接口平均携带多少离散信息。第 114 节换一个问题：对于一个具体的实值目标，加入更多记录后，最小平方预测误差到底减少了多少？仓库中的条件期望模块给出了一个正交分解。

<a id="entry-530"></a>

### 114.1 两层记录生成两个预测空间

设底层状态空间为

$$
X,
$$

带有测度

$$
\mu,
$$

并设当前记录生成的 sigma 代数为

$$
\mathcal G_c,
$$

加入更多历史或未来记录后得到更细的 sigma 代数

$$
\mathcal G_f.
$$

它们满足

$$
\mathcal G_c\le\mathcal G_f\le\mathcal A,
$$

其中

$$
\mathcal A
$$

是环境的 ambient measurable space。给定一个实值平方可积目标

$$
Y\in L^2(\mu),
$$

定义两种条件期望预测：

$$
\widehat Y_c=\mathbb E[Y\mid\mathcal G_c],
\qquad
\widehat Y_f=\mathbb E[Y\mid\mathcal G_f].
$$

在 Zeckendorf 模型中，可以把

$$
\mathcal G_c
$$

理解为当前合法构型读出生成的记录，而把

$$
\mathcal G_f
$$

理解为加入若干历史位、余数记录或后续可访问接口后的记录。这里的 sigma 代数是一个抽象的可测结构；它没有自动等同于量子 Hilbert 子空间。

<a id="entry-531"></a>

### 114.2 Pythagoras 分解

conditional_expectation_refinement_pythagoras 精确证明：

$$
\boxed{
\|Y-\widehat Y_c\|_2^2
=
\|Y-\widehat Y_f\|_2^2
+
\|\widehat Y_f-\widehat Y_c\|_2^2.
}
$$

同时有

$$
\|Y-\widehat Y_f\|_2^2
\le
\|Y-\widehat Y_c\|_2^2.
$$

最后一项

$$
\Delta_{\mathrm{refine}}
=
\|\widehat Y_f-\widehat Y_c\|_2^2
$$

可以称作记录细化的创新能量。它不是一个新的 Lean 定义，而是上述分解中已经出现的平方范数项。它的解释是：

$$
\text{细化后新增的可预测部分}
=
\text{细化前后预测器之间的距离}.
$$

如果

$$
\Delta_{\mathrm{refine}}=0,
$$

则两层记录给出的 L^2 预测器相同；这说明新增记录对这个目标和这个测度没有带来平方风险上的改进。这个等价解释只针对该目标、该测度和该二次损失，不能推广成新增记录在所有任务中都无用。

<a id="entry-532"></a>

### 114.3 与第 111 节的条件熵成本互补

第 111 节给出的是

$$
H(\pi_{F,q}\mid q)
\le
H(r\mid q),
$$

它回答候选记忆还携带多少平均离散信息。第 114 节给出的是

$$
\|Y-\widehat Y_f\|_2^2
\le
\|Y-\widehat Y_c\|_2^2,
$$

它回答加入记录后一个指定目标的预测误差减少多少。

两者可能朝不同方向变化：

$$
\text{记忆条件熵增加}
\quad\not\Rightarrow\quad
\text{指定目标风险一定下降},
$$

因为新增记录可能只包含与该目标无关的历史；同样，

$$
\text{指定目标风险下降}
\quad\not\Rightarrow\quad
\text{全部未来响应都已闭合}.
$$

因此，稳定对象的记忆预算至少有两个坐标：

$$
\begin{array}{c|c}
\text{坐标}&\text{测量内容}\\
\hline
\text{预测记忆熵}&\text{当前读出已知后还保留多少离散预测信息}\\
\text{创新能量}&\text{细化记录对指定平方损失目标减少多少误差}
\end{array}
$$

这也是为什么不能用单一的“历史长度”替代所有任务的成本描述。

<a id="entry-533"></a>

### 114.4 零风险的可测性判据

zero_prediction_risk_iff_ae_observation_measurable 给出一个更强的边界。设

$$
\operatorname{obs}:X\to O
$$

是可测观测，且

$$
Y:X\to\mathbb R
$$

属于

$$
L^2(\mu).
$$

在概率测度条件下，定理证明：

$$
\boxed{
\int
\left(
Y-
\mathbb E[Y\mid\sigma(\operatorname{obs})]
\right)^2
\,d\mu
=0
\quad\Longleftrightarrow\quad
Y\text{ 在 }\sigma(\operatorname{obs})\text{ 上几乎处处可测}.
}
$$

这里的

$$
\sigma(\operatorname{obs})
$$

由观测映射的 comap 构造。左侧是零平方预测风险，右侧表示观测已经保留了足以重建该目标的全部信息，允许测度零集合上的差异。

因此，如果当前 Zeckendorf 读出生成的 sigma 代数已经使目标可测，那么继续保存更多历史不会降低这个目标的平方误差。反之，只要目标还含有当前记录不可测的部分，零风险就不可能由该记录单独达到。

<a id="entry-534"></a>

### 114.5 一个有限离散化的解释

在有限状态且均匀概率的模型中，可以把 sigma 代数看成状态划分。当前记录把状态分成若干纤维，条件期望在每个纤维上取目标平均值。加入更细记录就是把纤维进一步拆分：

$$
\text{粗纤维}
\longrightarrow
\text{细纤维}
\longrightarrow
\text{更准确的纤维内平均}.
$$

Pythagoras 分解说明，粗预测误差中有一部分正好等于“细平均”与“粗平均”的平方差。若新增历史只是在每个粗纤维内部加入与目标无关的标签，那么

$$
\widehat Y_f=\widehat Y_c,
$$

创新能量为零；只有当细化后的纤维条件均值确实偏离对应的粗纤维均值时，创新能量才为正。仅仅把目标值不同的状态拆开，并不保证这一点，因为正负偏差可能在纤维平均中抵消。

这个解释与第 113 节的互信息不增并不冲突。粗粒化的互信息定理比较的是过去—未来联合相关；条件期望定理比较的是一个指定目标的平方风险。它们对不同函数和不同损失进行测量。

<a id="entry-535"></a>

### 114.6 与量子模型的边界

第 114 节使用的是：

$$
\mathbb R\text{-值目标},
\qquad
L^2\text{ 范数},
\qquad
\text{条件期望},
\qquad
\text{概率测度}.
$$

它没有直接处理复振幅、密度矩阵的 von Neumann 熵、非交换观测或量子通道。要把创新能量接到前面的量子记录模型，必须额外选择一个正的经典输出或 POVM 统计量，把它作为实值目标

$$
Y
$$

再指定观测生成的 sigma 代数。未经这一步，不能把

$$
\|\widehat Y_f-\widehat Y_c\|_2^2
$$

解释成普适的量子相干衰减量。

因此，当前可以安全使用的桥是：

$$
\boxed{
\text{记录细化的预测收益}
=
\text{条件期望的正交创新能量};
}
$$

而量子物理解释仍需另外证明记录通道如何产生这些经典统计和测度。

<a id="entry-536"></a>

### 114.7 对稳定现实的进一步约束

把第 111–114 节合起来，历史保留问题可以写成一个三重约束：

$$
\begin{aligned}
&\text{预测闭合：}&
\pi_{F,q}&=g\circ r,\\
&\text{信息成本：}&
H(\pi_{F,q}\mid q)&\le H(r\mid q),\\
&\text{目标风险：}&
\|Y-\widehat Y_f\|_2^2&\le\|Y-\widehat Y_c\|_2^2.
\end{aligned}
$$

若要求某个目标达到零风险，还必须满足

$$
Y
$$

在当前记录生成的 sigma 代数上几乎处处可测。若要求完整历史可恢复，还要另行满足第 112 节的乘积容量判据。于是“稳定经典现实”不是由一项单独的状态数决定，而是由任务、观测和误差准则共同决定。

<a id="entry-537"></a>

### 114.8 形式化边界

Lean 已证明的是有限或测度论的实值

$$
L^2
$$

条件期望分解、细化不增加平方预测风险，以及概率测度下零风险与观测可测性的等价。它没有证明这些对象自动来自 Zeckendorf Hamiltonian，也没有把二次预测风险与量子互信息或退相干率等同。

下一步若要继续形式化桥接，应先固定一个有限合法字串空间、一个实际读出函数和一个正的目标统计量，再把其离散划分映射到 sigma 代数或有限条件期望模型。只有这样，创新能量才会成为该具体量子记录协议的可计算量。

<a id="section-115"></a>

## 115. 行动闭合：公开状态相同但所需动作不同的硬反例

第 111 节把稳定对象定义为对未来预测足够的记忆商；第 114 节把记录细化带来的预测收益写成条件期望的创新能量。但“能预测一个目标”还不是“能作为一个行动状态”。如果系统下一步必须选择动作，那么当前记录还必须足以决定在允许的情境下应采取什么行动。

仓库中的 `D5/S3/ConceptDynamics/Policy/MemorylessActionObstruction.lean` 给出了这个要求的最小形式化。设

$$
q:T\to S
$$

是时间或历史到公开状态的读出，设

$$
\alpha:T\to A
$$

是实际要求的动作。如果存在两个时刻 $$t,u$$ 满足

$$
q(t)=q(u),
\qquad
\alpha(t)\ne\alpha(u),
$$

则不存在一个只看公开状态的策略

$$
\pi:S\to A
$$

使得对所有时刻都有

$$
\pi(q(v))=\alpha(v).
$$

证明只有一行内积式的等式传递：若这样的策略存在，则

$$
\alpha(t)
=\pi(q(t))
=\pi(q(u))
=\alpha(u),
$$

与动作不同矛盾。Lean 已经在任意类型 $$T,S,A$$ 上编译并证明了这个命题；它没有引入量子假设，因此是一个比具体物理模型更基础的行动闭合障碍。

<a id="entry-539"></a>

### 115.1 从预测闭合到控制闭合

第 111 节的预测商只要求：在指定未来操作族中，当前记忆能决定未来读数。行动闭合增加了一个不同的要求：同一个公开状态必须允许同一个策略动作。可以把两者写成两个因子化条件。

令 $$r$$ 是保留的记忆接口，令 $$q$$ 是当前公开读出。预测闭合要求

$$
q=\overline q\circ r,
\qquad
r\circ F=\overline F\circ r,
$$

其中 $$F$$ 是状态更新；控制闭合要求实际行动 $$\alpha$$ 满足

$$
\alpha=\pi\circ r.
$$

前两式说“先演化再压缩”和“先压缩再用有效更新”一致，并且当前读出可以由记忆接口恢复；后一式说“所需行动”本身能够由压缩后的状态决定。当前状态分类即使满足预测闭合，也可能不满足控制闭合，因为行动可能依赖没有进入 $$r$$ 的历史变量。

因此，稳定经典对象至少要通过两道检查：

$$
\boxed{
\text{预测闭合} + \text{控制闭合}.
}
$$

如果研究目标只有被动预测，控制闭合可以暂不要求；如果对象要参与反馈、干预或实验设计，控制闭合就是必要条件。

<a id="entry-540"></a>

### 115.2 与第 111 节 canonical quotient 的关系

令 $$r:T\to M$$ 是某个保留的记忆接口。若所有允许的预测和动作都只依赖 $$r$$，则存在函数 $$g_F$$ 与 $$\pi$$ 使得

$$
q(F(t))=g_F(r(t)),
\qquad
\alpha(t)=\pi(r(t)).
$$

第 111 节的 canonical predictive quotient 只对第一类函数取共同商；第 115 节说明，若要得到可执行对象，商必须再细化到能够因子化所有相关动作的程度。换句话说，预测等价关系

$$
 t\sim_{\mathrm{pred}}u
$$

只在所有未来读数相同的历史之间合并；控制等价关系还要求

$$
\alpha(t)=\alpha(u)
$$

对所有被合并的历史成立。若动作不同，两个历史必须继续分开，即使它们当前所有公开读数都相同。

这给出“需要保留多少历史”的一个更强答案：

$$
\boxed{
\text{所需记忆至少要区分所有会导致不同未来动作的历史。}
}
$$

条件熵下界仍然适用，但现在的任务族扩大了。若 $$\Pi$$ 表示允许的策略动作集合，应该以同时支配预测读出与动作的最小商来定义记忆，而不能只根据一个目标变量计算成本。

<a id="entry-541"></a>

### 115.3 一个有限反例：同一个 Zeckendorf 粗读数（奇偶）对应不同动作

取长度为三、禁止相邻两个一的合法构型

$$
000,\quad001,\quad010,\quad100,\quad101,
$$

并用权重 $$3,2,1$$ 读出 Zeckendorf 数值。这个读出把五个构型标成 $$0,1,2,3,4$$。现在假定公开接口只保留奇偶性

$$
q(w)=a(w)\bmod 2,
$$

其中 $$a(w)$$ 是上述数值；于是 $$001$$ 与 $$100$$ 都读成公开状态 $$1$$。

如果控制任务规定：数值为 $$1$$ 时执行动作 $$A_1$$，数值为 $$3$$ 时执行动作 $$A_3$$，且 $$A_1\ne A_3$$，那么公开奇偶状态无法支持正确策略。两个历史具有相同的公开值，却要求不同动作。要恢复控制闭合，至少必须保留一个能区分这两个构型的额外记录，例如完整数值、最高位位置，或直接保留它们所属的预测—动作等价类。

这个例子不说明奇偶记录“错误”。它只说明记录的适用范围：它可以足以回答某些二元问题，却不足以承担这个控制任务。Zeckendorf 刻度提供合法构型的组织方式；究竟要保留多少位，则由预测目标、动作集合和允许误差共同决定。

<a id="entry-542"></a>

### 115.4 量子边界：策略依赖记录，不等于预先填写所有测量答案

在量子模型中，行动闭合必须相对于一个实际可访问的记录系统来表述。若记录通道为

$$
\mathcal C(\rho)_{ij}=R_{ij}\rho_{ij},
$$

则一个控制器可以依赖当前记录寄存器、系统的允许操作和已建立的相关，而不能自动依赖被环境保留但控制器无法访问的完整历史。

这不意味着为所有不相容测量预先填写一张经典答案表。控制闭合只要求：在明确给定的实验协议和可访问记录下，存在一个实现动作的映射。更换可访问记录、测量上下文或联合操作，可能改变可实现的策略集合。`WindowCharacter` 所表达的非交换障碍仍然保留：不能把所有相容性关系压成一个保乘法的复数读数，再把该读数当成万能控制状态。

一个最小的相位反例来自合法基态 $$|01\rangle,|10\rangle$$。令

$$
|B\rangle=\frac{|01\rangle+|10\rangle}{\sqrt 2},\qquad
|D\rangle=\frac{|01\rangle-|10\rangle}{\sqrt 2}.
$$

计算基底读出对二者给出相同分布，但若允许的后续耦合在该子空间中满足

$$
H|01\rangle=g|00\rangle,\qquad H|10\rangle=g|00\rangle,\qquad
H|00\rangle=g(|01\rangle+|10\rangle),
$$

则

$$
H|B\rangle=\sqrt 2g|00\rangle,\qquad H|D\rangle=0.
$$

因此，相同当前读数不能保证相同控制响应；把这个耦合加入任务族后，动作完备的记录必须保留相对相位所区分的历史。

同样，局部读数相同也不代表联合状态相同。若控制器能够访问记录自由度并执行允许的联合操作，`CanonicalRecordAccessRecovery` 所刻画的恢复机制可能重新暴露被局部读出隐藏的区别；若记录不可访问，则该区别对当前控制器仍然是隐藏变量，并可能通过历史回流影响后续行动。

<a id="entry-543"></a>

### 115.5 与第 114 节预测风险的合并

把目标预测误差和行动错误分别记为

$$
\mathcal R_Y(q)=\mathbb E\left[(Y-\widehat Y_q)^2\right],
$$

以及一个动作损失

$$
\mathcal R_A(q)=\mathbb E\left[\ell(\alpha,\widehat\alpha_q)\right].
$$

第 114 节的 Pythagoras 分解说明，记录细化带来的目标风险下降等于新增条件均值的平方能量。第 115 节补充一个离散的零风险边界：若同一公开状态上存在不同必需动作，则任何确定性无记忆策略的动作风险都不可能为零。即使目标 $$Y$$ 已经可以被当前读出无误预测，动作风险仍可能保持正值。

因此，一个面向行动的稳定现实应同时满足

$$
\mathcal R_Y(q)\le\varepsilon_Y,
\qquad
\mathcal R_A(q)\le\varepsilon_A,
$$

并且在零误差的确定性情形满足

$$
\alpha=\pi\circ q.
$$

若允许随机策略，确定性障碍会转化为条件动作分布必须在同一公开状态上相同；不同历史诱导不同的最优动作分布时，仍需保留能区分它们的记录。这个推广需要额外的概率化 Lean 定理，当前仓库只冻结了确定性命题。

<a id="entry-544"></a>

### 115.6 对“稳定经典现实”的更新定义

到这里，“稳定”不能只理解为某个记录通道的固定点是对角的，也不能只理解为某个目标的预测误差很小。更完整的有限任务定义是：给定允许的读出、演化和行动族，一个记录接口 $$q$$ 满足

$$
\begin{aligned}
& q\circ F=g_F\circ q &&\text{对相关预测操作成立},\\
& \alpha=\pi\circ q &&\text{对相关控制任务成立},\\
& \mathcal R_Y(q)\le\varepsilon_Y,\\
& \mathcal R_A(q)\le\varepsilon_A.
\end{aligned}
$$

若量子记录还会被重复复用，则必须把记录的可访问性和历史回流一并放进允许操作族；不能只按“观测次数”估算记忆成本。若进一步展开内部结构不会改变这些预测与行动，或改变量低于给定误差界，当前接口才可以作为该尺度上的有效对象。

所以第 115 节把此前的问题推进了一步：

$$
\boxed{
\text{稳定现实不仅要能回答“接下来会看到什么”，还要能决定“接下来能做什么”。}
}
$$

公开状态相同而所需动作不同，是一个可机器验证的反例，说明任何声称“当前读数已经构成完整对象”的理论，都必须说明它保留了哪些行动相关历史，以及这些历史在什么操作族中可以被忽略。

<a id="entry-545"></a>

### 115.7 形式化边界

Lean 已证明的是任意类型上的确定性记忆无关策略障碍：重复公开状态若对应不同动作，则不存在只依赖公开状态的全局策略。它没有证明某个具体 Zeckendorf 读出在物理实验中必须承担哪一种控制任务，也没有把确定性策略自动推广为随机、量子反馈或有记忆环境中的最优控制。

当前可复用的桥是：

$$
\boxed{
\text{预测闭合控制未来读数，行动闭合控制未来干预；两者必须按同一任务族分别检验。}
}
$$

下一步若继续形式化，应固定一个有限合法构型空间、一个可访问记录映射和一个有限动作集合，再证明该记录对指定动作族的因子化条件，最后把动作风险与第 114 节的预测风险放在同一个有限概率模型中比较。

<a id="section-116"></a>

## 116. 干预闭包的最小修复：把可执行历史组织成响应轨迹

第 115 节给出了行动闭合失败的最小障碍：相同公开状态可能要求不同动作。下一步不是无条件恢复全部历史，而是问：给定一族允许干预，怎样构造一个刚好足以保持闭合的细化接口？仓库中的 `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean` 给出了一个一般答案。

设原始概念读出为

$$
 c:X\to A,
$$

允许的干预族为

$$
 I:U\to X\to X.
$$

若两个状态被当前概念归为同一类，即

$$
 c(x)=c(y),
$$

那么概念对干预族闭合，是指对每个干预 $$u$$ 都有

$$
 c(I(u,x))=c(I(u,y)).
$$

这正是“当前合并掉的历史，不会在下一次允许操作后重新显现”的形式化条件。

<a id="entry-547"></a>

### 116.1 动态闭包记录什么

对一个有限干预词

$$
 w=[u_1,\ldots,u_k]\in U^*,
$$

令 $$I_w(x)$$ 表示从 $$x$$ 出发依次执行这些干预。动态闭包读出为

$$
 \operatorname{Dyn}_I(c)(x)(w)=c(I_w(x)).
$$

因此

$$
\operatorname{Dyn}_I(c):X\to(U^*\to A)
$$

不是只保存当前标签，而是保存“在所有有限干预词之后会看到什么”的响应轨迹。空词给出原始读出：

$$
\operatorname{Dyn}_I(c)(x)([]) = c(x).
$$

这立即说明动态闭包细化了原始概念。若两个状态在动态闭包下相同，它们在空词下当然相同；反方向一般不成立。

<a id="entry-548"></a>

### 116.2 它确实对每个允许干预闭合

若 $$x,y$$ 的动态轨迹相同，则对任意干预 $$u$$ 和任意后续词 $$w$$，有

$$
\operatorname{Dyn}_I(c)(I(u,x))(w)
=
\operatorname{Dyn}_I(c)(x)(u::w)
=
\operatorname{Dyn}_I(c)(y)(u::w)
=
\operatorname{Dyn}_I(c)(I(u,y))(w).
$$

所以

$$
\boxed{
\operatorname{Dyn}_I(c)\text{ 对 }I\text{ 的每一个干预都闭合}.
}
$$

这里的关键不是把状态变成一个更长的静态标签，而是把干预前缀加入响应坐标。任何可能使两个状态分开的下一步，都已经成为轨迹中的一个坐标。

<a id="entry-549"></a>

### 116.3 最小性：所有闭合细化都必须包含它

设另一个接口

$$
 d:X\to B
$$

满足两个条件：

$$
 c=\bar c\circ d,
$$

即 $$d$$ 至少保留原始概念；并且 $$d$$ 对所有干预闭合，即

$$
 d(x)=d(y)
\Longrightarrow
 d(I(u,x))=d(I(u,y)).
$$

那么仓库中的 `dynamic_closure_is_least` 证明：存在一个从 $$d$$ 到动态闭包的因子，使得动态闭包不会保留任何一个所有闭合细化都可以安全丢掉的坐标。按项目中的 `Refines` 方向写成：

$$
\boxed{
 d\text{ 闭合且细化 }c
\Longrightarrow
 d\text{ 细化 }\operatorname{Dyn}_I(c).
}
$$

等价地说，动态闭包是所有干预闭合细化的最小公共要求。证明沿干预词归纳：闭合性把单步等价逐步传播到任意有限词；原始概念因子化则把每一条轨迹坐标从候选接口恢复出来。

这一步把第 115 节的“必须保留额外历史”变成了一个可构造的最小方案：只保留那些会在允许干预轨迹中显现的差异。

<a id="entry-550"></a>

### 116.4 与预测商的精确关系

第 111 节的 predictive quotient 由指定未来读出族决定；第 116 节把未来族具体化为所有有限干预词。若未来任务只允许观测而不允许干预，动态闭包退化为相应的观测响应商。若加入一个新的可执行干预 $$u_*$$，任务族变为

$$
\mathfrak T' = \mathfrak T\cup\{u_*\},
$$

动态闭包会加入以 $$u_*$$ 开头的响应坐标。于是原先可以合并的两个状态，可能因为

$$
 c(I(u_*,x))\ne c(I(u_*,y))
$$

而被分开。

因此，记忆需求不是只由当前读出决定，而是由三元组共同决定：

$$
\boxed{
(\text{当前读出},\ \text{允许干预族},\ \text{预测任务族}).
}
$$

扩大实验能力会细化等价类；缩小实验能力可能允许更粗的有效对象。这里的“相对性”具有明确的单调方向，而不是任意描述都同样有效。

<a id="entry-551"></a>

### 116.5 Zeckendorf 合法空间中的有限截断

在长度 $$L$$、禁止相邻两个一的合法空间中，令

$$
\mathcal W_L=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
$$

并令 $$c(w)$$ 是 Zeckendorf 数值或某个局部记录。若干预是保持合法性的局部翻转族

$$
 I_u:\mathcal W_L\to\mathcal W_L,
$$

则动态闭包可以在有限干预深度 $$N$$ 截断为

$$
\operatorname{Dyn}_{I,N}(c)(w)
=
\bigl(c(I_v(w))\bigr)_{|v|\le N}.
$$

对于固定 $$L,N$$，这仍然是有限记录接口，可以直接枚举和比较。它回答的是有限实验范围内的闭合问题：两个合法构型若在所有长度不超过 $$N$$ 的允许干预下都有相同读出，就可以在该实验预算内合并；若某条长度至多 $$N$$ 的词把它们分开，则当前接口不闭合。

但有限截断不等于无限闭包。若只证明

$$
\operatorname{Dyn}_{I,N}(c)(x)=\operatorname{Dyn}_{I,N}(c)(y),
$$

不能推出对所有更长干预词都相同。这个边界正是“有限预测范围”和“全局可恢复历史”的区别。第 112 节的完整恢复容量条件也因此不能由一个有限截断自动替代。

<a id="entry-552"></a>

### 116.6 量子版本的边界

在量子系统中，不能直接把 $$I_u$$ 当作任意函数；它应由允许的量子通道、幺正演化或测量—反馈协议给出，并且当前读出应由一个明确的 POVM 或记录通道产生。若用 $$\mathcal C$$ 表示记录，$$\Phi_u$$ 表示干预后的通道，那么有限响应轨迹的坐标可以写成

$$
\mathcal C\circ\Phi_{u_k}\circ\cdots\circ\Phi_{u_1}(\rho).
$$

这只是把动态闭包的结构翻译到量子通道语言；它没有自动证明这些坐标彼此可同时读取，也没有把量子态压成一张预先填写所有不相容测量答案的经典表。不同轨迹坐标可能依赖不同上下文，必须保留测量机制和允许的联合操作。

对于前文的 Zeckendorf 受约束 Hilbert 空间，若投影到合法子空间的投影为 $$P_Z$$，还要分别检查：

$$
[H,P_Z]=0
$$

是否保证连续演化保持合法空间，以及每个测量或反馈通道是否把合法密度矩阵送回合法状态集合。动态闭包只描述“哪些响应需要保留”，不替代物理实现条件。

<a id="entry-553"></a>

### 116.7 对稳定经典现实的进一步定义

结合第 115 节，稳定接口不再只是满足一个静态固定点，而应满足：

$$
\begin{aligned}
&\text{当前读出可由接口恢复},\\
&\text{接口对允许更新和干预闭合},\\
&\text{指定预测与动作在接口上因子化},\\
&\text{截断或近似时给出明确误差界}.
\end{aligned}
$$

动态闭包提供了一个极端但清楚的上界：保留全部有限响应轨迹，必然不会遗漏允许干预能暴露的差异。其最小性定理又说明，在同一任务族中，任何安全的闭合接口都必须至少保留这些响应信息。

实际研究通常会在动态闭包与更便宜的近似接口之间选择。第 111 节的条件熵、第 114 节的创新能量和第 115 节的动作风险，可以用来衡量删去哪些轨迹坐标后仍满足给定精度；删去后若出现新的干预分离，则由动态闭合条件给出精确反例。

因此，“保留多少历史”现在有一个可执行的答案：

$$
\boxed{
\text{保留到允许干预族下的响应轨迹闭合；若只做有限实验，就保留到指定深度并报告截断误差。}
}
$$

<a id="entry-554"></a>

### 116.8 形式化边界

Lean 已证明的是纯确定性概念动力学中的三件事：原始概念被动态闭包细化；动态闭包对每个干预闭合；任何闭合且细化原概念的候选接口都细化动态闭包。证明使用任意类型和有限列表干预词，不依赖概率、Hilbert 空间或量子公理。

它没有证明无限干预族的有限表示一定存在，也没有证明某个具体 Zeckendorf 翻转规则对应真实物理 Hamiltonian，更没有证明量子通道的非交换响应可以无损地嵌入一个经典轨迹函数。那些桥接仍然开放，必须在固定有限构型、通道、测量和误差指标后分别验证。

当前可复用的最强桥是：

$$
\boxed{
\text{动态闭包是指定干预族下保持预测与行动闭合的最小响应细化。}
}
$$

这使“对象”获得了一个更严格的操作性判据：它不是当前读数的名字，而是对允许实验族足够闭合的响应接口。

<a id="section-117"></a>

## 117. 有限时域控制的下沉：预测闭合还必须保留价值递归

第 116 节说明，若只要求响应对干预闭合，可以用动态闭包构造最小细化。但行动任务通常还有一个更强的问题：不是只问“允许什么动作”，而是问“在有限未来时域内，哪个动作最优”。这要求记录接口不仅保持状态更新，还要保持奖励和终值的结构。

仓库中的 `D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization.lean` 形式化了这个桥。设微观状态、宏观状态和动作分别为

$$
S_{\mathrm{micro}},\qquad S_{\mathrm{macro}},\qquad A,
$$

有一个抽象映射

$$
\alpha:S_{\mathrm{micro}}\to S_{\mathrm{macro}}.
$$

微观转移和宏观转移为

$$
T_m:A\times S_{\mathrm{micro}}\to S_{\mathrm{micro}},
\qquad
T_M:A\times S_{\mathrm{macro}}\to S_{\mathrm{macro}}.
$$

若对每个动作和微观状态都有

$$
\alpha(T_m(a,s))=T_M(a,\alpha(s)),
$$

则抽象与受控动力学相容。

<a id="entry-556"></a>

### 117.1 奖励和终值也必须因子化

仅有状态转移相容还不够。有限时域最优控制还使用阶段奖励和终端价值。设

$$
r_m:S_{\mathrm{micro}}\times A\to\mathbb R,
\qquad
r_M:S_{\mathrm{macro}}\times A\to\mathbb R,
$$

以及终端价值

$$
V^0_m:S_{\mathrm{micro}}\to\mathbb R,
\qquad
V^0_M:S_{\mathrm{macro}}\to\mathbb R.
$$

需要同时满足

$$
 r_m(s,a)=r_M(\alpha(s),a),
$$

以及

$$
 V^0_m(s)=V^0_M(\alpha(s)).
$$

这三个条件分别保证：执行同一个动作后的状态一致、即时收益一致、停止时的价值一致。缺少任意一个条件，宏观读出都可能无法承担控制价值。

<a id="entry-557"></a>

### 117.2 Bellman 值逐时域因子化

对有限动作集，定义 Bellman 值

$$
V_0(s)=V^0(s),
$$

并递归为

$$
V_{n+1}(s)
=
\max_{a\in A}
\left(r(s,a)+V_n(T(a,s))\right).
$$

Lean 定理 `finite_horizon_value_factorization` 证明：在上一节的三项相容条件下，对每个有限时域 $$n$$ 都有

$$
\boxed{
V^{\mathrm{micro}}_n(s)
=
V^{\mathrm{macro}}_n(\alpha(s)).
}
$$

证明对 $$n$$ 做归纳。零时域就是终值因子化；后继时域中，每个动作的即时奖励和递归续值逐项相等，因此有限动作集合上的最大值也相等。

这比“一步更新可预测”更强：它说明相同宏观状态的微观历史，在整个指定有限时域内拥有相同的最优价值。

<a id="entry-558"></a>

### 117.3 最优动作集合也下沉

令有限时域 $$n$$ 下的最优动作集合为

$$
\operatorname{Opt}_n(s)
=
\left\{
 a:\ r(s,a)+V_n(T(a,s))
 \text{达到所有动作中的最大值}
\right\}.
$$

仓库中的 `finite_horizon_optimal_actions_descend` 进一步证明

$$
\boxed{
\operatorname{Opt}^{\mathrm{micro}}_n(s)
=
\operatorname{Opt}^{\mathrm{macro}}_n(\alpha(s)).
}
$$

因此，抽象接口不仅能计算宏观价值，还能准确给出所有最优动作。若微观状态 $$s,t$$ 满足

$$
\alpha(s)=\alpha(t),
$$

那么在这些假设下，它们的有限时域最优动作集合完全相同。这里的“行动闭合”不再只是存在某个动作函数，而是整个有限时域 Bellman 递归在接口上闭合。

<a id="entry-559"></a>

### 117.4 对第 115 节障碍的精确修复条件

第 115 节的障碍是：

$$
q(s)=q(t),
\qquad
\text{但所需动作不同}.
$$

第 117 节给出一个可验证的充分条件，保证这种分离不会发生在有限时域最优控制中：抽象 $$\alpha$$ 必须同时保持转移、奖励和终值。此时不是把动作差异强行抹去，而是证明它们在任务定义下本来就不构成差异：

$$
\alpha(s)=\alpha(t)
\Longrightarrow
\operatorname{Opt}_n(s)=\operatorname{Opt}_n(t).
$$

如果实际系统出现两个同一抽象类中的状态，却有不同的最优动作集合，那么至少有一项因子化假设失败。具体可能是：转移没有闭合，奖励读出了隐藏历史，或终端目标依赖被丢弃的变量。此时应增加记录，或者缩小允许任务族，不能继续声称当前抽象是控制完备的。

<a id="entry-560"></a>

### 117.5 Zeckendorf 约束空间中的解释

取合法构型空间

$$
\mathcal W_L=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
$$

把 $$w$$ 作为微观状态，把某个 Zeckendorf 粗读出作为宏观状态。若局部更新保持合法空间，并且满足

$$
\alpha(T_m(a,w))=T_M(a,\alpha(w)),
$$

那么还必须检查阶段奖励和终端目标是否只依赖 $$\alpha(w)$$。例如，若奖励是完整 Zeckendorf 数值的函数，而宏观接口只保留最后一位或奇偶性，则通常不能直接使用值函数下沉定理；需要证明该奖励在每个宏观纤维上相同，或扩展宏观状态。

反过来，若任务只奖励“是否仍为合法构型”，局部有限状态接口可能已经足够。由此可见，合法语言的最小自动机状态数、数值读出所需记忆、有限时域控制所需状态数和量子 Hilbert 空间维数仍然是不同的量。

<a id="entry-561"></a>

### 117.6 与量子记录模型的边界

Bellman 因子化定理是有限动作、确定性转移和实值奖励的经典定理。它可以用于量子实验的经典输出层：先固定一个 POVM 或记录通道，把每次实验的输出和代价定义成实值函数，再检查这些输出是否在选定记录接口上因子化。

但它没有直接证明量子通道的密度矩阵、复振幅或非交换观测满足 Bellman 递归。若动作本身是量子通道，或者状态只以概率分布给出，必须另外选择随机控制、部分可观测控制或量子控制的数学模型。不能把有限经典 $$\max$$ 自动解释成量子测量中的普适优化规则。

同样，值函数相等不等于完整历史相等。两个微观状态可以在指定有限时域和奖励下具有相同价值，却在加入新的测量、不同终值或更长时域后被区分。值函数因子化是任务相对的闭合结果，不是本体论上的全局同一。

<a id="entry-562"></a>

### 117.7 对稳定经典现实的更新

目前“稳定”的条件可以按强度分层：

$$
\begin{aligned}
&\text{读出闭合}: && q=\bar q\circ r,\\
&\text{状态闭合}: && r\circ T=\bar T\circ r,\\
&\text{行动闭合}: && \operatorname{Opt}_n=\overline{\operatorname{Opt}}_n\circ r,\\
&\text{价值闭合}: && V_n=\bar V_n\circ r.
\end{aligned}
$$

第 116 节给出对指定干预族的最小响应细化；第 117 节说明，当任务还带有奖励和终值时，真正需要的是 Bellman 价值与最优动作的共同下沉。于是“保留多少历史”可按任务逐层增加，而不是一开始就保留全部微观状态。

如果只要求一步读出，读出闭合可能足够；如果要求有限时域行动，就必须验证值函数闭合；如果新增动作、奖励或终值使因子化失败，就必须细化接口或明确任务边界。

<a id="entry-563"></a>

### 117.8 形式化边界

Lean 已证明的是有限动作集、非空动作类型、确定性转移、实值阶段奖励和实值终端函数下的有限时域 Bellman 值因子化，以及最优动作集合的精确相等。定向构建确认 `finite_horizon_value_factorization` 使用标准公理闭包

$$
[\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}].
$$

这些定理没有证明无限时域极限、随机策略、部分可观测控制或量子通道的最优性。它们提供的可复用桥是：

$$
\boxed{
\text{若转移、奖励和终值都尊重同一抽象，有限时域价值和最优动作就完全下沉到该抽象。}
}
$$

这把第 115 节的行动闭合从一步逻辑障碍推进到有限未来的控制递归，并给出了一个可以直接检验的历史保留准则。
<a id="section-118"></a>

## 118. 响应闭合的适用条件：支持集、有限视野与动作选择

**定义 118.1（原档案载体与两种数位索引）。** 沿用[《情境时空算术》定义 1–6](../CONTEXTUAL_SPACETIME_ARITHMETIC.md)，完整表示为

$$
\mathbf x=(C,A_{\rm sel}),\qquad
C=(E,\prec,t,x,\sigma,\rho,\Omega),\qquad
A_{\rm sel}\subseteq\Omega\subseteq E.
$$

其中 $E$ 是有限事件出现集，$\prec$ 是严格偏序，整数时刻沿偏序严格增加，位置取值于 $\mathbb Z^3$，符号取值于 $\{+1,-1\}$，来源取值于有限来源树。档案、当前区域和当前选择是不同数据；本节的状态集 $X$ 可取这些完整表示的指定集合，或另行明确的状态描述集合。一个表示的档案有限不意味着全部表示组成有限集合。原数值读数为

$$
q_{\rm CSA}(\mathbf x)=\sum_{e\in A_{\rm sel}}\sigma(e).
$$

[《情境时空算术的 Zeckendorf 观察》定义 3、4、9、11](../CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)中的权重与两种索引分别为

$$
G_0=1,\quad G_1=2,\quad G_{j+2}=G_{j+1}+G_j,
\qquad a(c)=\sum_jG_jc_j,
$$

$$
a_p(r)=\sum_jG_jr(p,j),\qquad N(r)=\prod_p p^{a_p(r)}.
$$

单个自然数的规范行 $c=(c_0,c_1,\ldots)$ 与正整数的素数指数表 $r=(r(p,j))$ 不同；$a(c)$、$a_p(r)$、$N(r)$ 也不与 $q_{\rm CSA}$ 混同。源卷的字串按低位到高位书写。第 115.3 节的三位字串采用反向书写约定：其字串为 $c_2c_1c_0$，从左到右的权重恰为

$$
(G_2,G_1,G_0)=(3,2,1).
$$

因此该节的 $001$ 与 $100$ 分别是数值一与三；若按源卷低位到高位书写，同两行分别写为 $100$ 与 $001$。这里只交换书写方向，不交换素数标签与数位索引。概率分布是额外数据，重复来源标签本身不规定概率或独立性。

**假设 118.2（部分操作的定义域与失败观察）。** 第 116、117 节使用总更新时，须固定当前读出 $c:X\to O$ 及如下操作解释。每个字母 $u\in U$ 指定一个原操作的确定部分映射

$$
I_u:D_u\subseteq X\longrightarrow X.
$$

多元原操作通过固定其他参数及孔的位置给出这样的映射；$D_u$ 保留原定义域。例如原时间复合的守卫仍为

$$
\forall e\in E_{\mathbf x}\ \forall f\in E_{\mathbf y},
\qquad t_{\mathbf x}(e)<t_{\mathbf y}(f).
$$

应用总更新结论时，或者限制到一个非空不变域 $X_0$，使每个允许字母在全部 $X_0$ 上合法且 $I_u(X_0)\subseteq X_0$；或者使用带不交失败标签的扩张

$$
X_\bot=X\sqcup\{\bot\},\qquad
\widehat I_u(z)=
\begin{cases}
I_u(z),&z\in D_u,\\
\bot,&z\in X\setminus D_u\text{ 或 }z=\bot,
\end{cases}
$$

$$
\widehat c(z)=
\begin{cases}
\operatorname{ok}(c(z)),&z\in X,\\
\operatorname{fail},&z=\bot,
\end{cases}
\qquad \operatorname{fail}\notin\operatorname{ok}(c[X]).
$$

成功后继须仍在所选 $X$ 内；失败严格传播。此扩张与[原卷定义 16 的严格观察](../CONTEXTUAL_SPACETIME_ARITHMETIC.md)及[Zeckendorf 卷定义 446.1](../CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)一致。若还要优化控制，须对失败规定终止、奖励和终值，或只使用在全域合法的共同动作集；不能以固定动作集上的最大值代替未说明的状态依赖合法动作域。

**命题 118.3（第 115 节开篇的等式论证）。** 设 $q:T\to S$，$b:T\to A$，且有

$$
q(t)=q(u),\qquad b(t)\ne b(u).
$$

则不存在满足下式的全局确定性策略：

$$
\pi:S\to A,\qquad \forall v\in T,\quad \pi(q(v))=b(v).
$$

第 115 节开篇“内积式的等式传递”应理解为函数对相等的保持及等式传递；该命题不要求内积、概率或量子结构。这里 $b(v)$ 是任务规定必须实现的标签，不是从多个最优标签中任意挑出的一个标签。

证明。若 $\pi$ 存在，对 $q(t)=q(u)$ 应用 $\pi$，得到

$$
b(t)=\pi(q(t))=\pi(q(u))=b(u),
$$

与假设矛盾。这正是[无记忆动作障碍](../../../../D5/S3/ConceptDynamics/Policy/MemorylessActionObstruction.lean)的等式论证。

**定义 118.4（有限任务的期望动作风险）。** 取有限非空集合 $T,A$、函数 $q:T\to S$ 与必须实现的标签 $b:T\to A$，并令 $S=q[T]$。给定概率质量

$$
\mu:T\to[0,1],\qquad \sum_{v\in T}\mu(v)=1,
\qquad T_+=\{v\in T:\mu(v)>0\}.
$$

随机策略是 $K:S\to\Delta(A)$，其中 $\Delta(A)$ 是 $A$ 上概率向量的集合；确定性策略 $\pi$ 对应 $K_s=\delta_{\pi(s)}$。零一损失及其风险定义为

$$
\ell_{01}(v,a)=\mathbf 1_{\{a\ne b(v)\}},
\qquad
\mathcal R_{01}(K)=
\sum_{v\in T}\mu(v)\sum_{a\in A}K_{q(v)}(a)\ell_{01}(v,a).
$$

所有策略只能依赖 $q(v)$；这里的随机化不包含额外获知 $v$ 的旁信息。

**命题 118.5（第 115.5 节的支持集修正）。** 在定义 118.4 下，若 $q(t)=q(u)$ 且 $b(t)\ne b(u)$，则每个确定性或随机策略满足

$$
\mathcal R_{01}(K)\ge\min\{\mu(t),\mu(u)\}.
$$

因此这对碰撞给出严格正的下界，须有 $\mu(t)>0$ 且 $\mu(u)>0$。存在零风险策略当且仅当 $b$ 在每个 $q$ 纤维与 $T_+$ 的交上恒定；存在处处正确的确定性策略当且仅当 $b$ 在每个完整 $q$ 纤维上恒定。第 115.5 节“存在不同必需动作，则任何确定性无记忆策略的动作风险都不可能为零”须以上述支持集与损失条件代替。

证明。记共同记录为 $s$，$m=\min\{\mu(t),\mu(u)\}$。损失非负，且不同标签的概率之和至多一，故

$$
\begin{aligned}
\mathcal R_{01}(K)
&\ge\mu(t)(1-K_s(b(t)))+\mu(u)(1-K_s(b(u)))\\
&\ge m\bigl(2-K_s(b(t))-K_s(b(u))\bigr)\ge m.
\end{aligned}
$$

风险为零时，每个正质量点的非负项都为零，因此 $K_{q(v)}(b(v))=1$。同一纤维不能以概率一输出两个不同标签。反之，若每个正质量纤维的标签相同，令策略输出该标签；无正质量点的纤维任选 $A$ 中一个标签，风险即为零。把 $T_+$ 换成 $T$，同一逐纤维构造与命题 118.3 给出处处正确的充要条件。

零质量反例为

$$
T=A=\{0,1\},\quad S=\{*\},\quad q(0)=q(1)=*,
\quad b(v)=v,\quad \mu(0)=1,\quad\mu(1)=0.
$$

常策略 $\pi(*)=0$ 的期望风险为零，却在点一错误；全局正确策略不存在。由此，几乎处处零风险与全局可实现性不能互换。

**命题 118.6（一般损失所需的分离）。** 保持定义 118.4 的有限集合与概率，改取有限实值损失 $\ell:T\times A\to[0,\infty)$，并按同一公式定义 $\mathcal R_\ell$。若 $t\ne u$、$q(t)=q(u)$，且存在 $\eta>0$ 使

$$
\forall a\in A,\qquad \ell(t,a)+\ell(u,a)\ge\eta,
$$

则所有只依赖 $q$ 的随机策略满足

$$
\mathcal R_\ell(K)\ge\eta\min\{\mu(t),\mu(u)\}.
$$

仅有不同标签而没有损失分离不蕴含此结论。

证明。非负性允许删去其余状态的风险项，再将两质量分别降低到其最小值。共同动作分布的总质量为一，所以

$$
\mathcal R_\ell(K)
\ge\min\{\mu(t),\mu(u)\}
\sum_{a\in A}K_{q(t)}(a)\bigl(\ell(t,a)+\ell(u,a)\bigr)
\ge\eta\min\{\mu(t),\mu(u)\}.
$$

若 $\ell$ 恒零，即使 $t,u$ 都有正质量且指定标签不同，每个策略仍有零风险。若损失可取负值，其余状态的负贡献又能抵消碰撞代价，因此非负性也不能无条件删除。

**命题 118.7（第 116.3 节最小性的准确方向）。** 对总更新 $I_u:X\to X$ 及读出 $c:X\to O$，令空词作用为恒等，非空词先执行首字母，再执行尾词，并定义

$$
\operatorname{Dyn}_I(c)(x)(w)=c(I_w(x)),\qquad w\in U^*.
$$

细化关系的方向固定为

$$
\operatorname{Refines}(c,d)
\quad\Longleftrightarrow\quad
\exists f:D\to O,\quad c=f\circ d,
\qquad d:X\to D.
$$

若 $d$ 保留 $c$ 且每个 $I_u$ 保持 $d$ 的纤维，则

$$
\operatorname{Refines}(\operatorname{Dyn}_I(c),d),
\quad\text{即}\quad
\exists g:D\to(U^*\to O),\quad \operatorname{Dyn}_I(c)=g\circ d.
$$

这保留当前 $c$ 及全部未来 $c$，不包含任何未进入读出的独立动作要求。

证明。直接应用[动态闭包最小性定理](../../../../D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean)，其前提正是 $c=f\circ d$ 与纤维保持，结论正是所列 $g$。空词求值给出 $c(x)=\operatorname{Dyn}_I(c)(x)([])$。该结论中的全部响应坐标均为 $c\circ I_w$，没有未指定的动作读出。

**命题 118.8（行动完备所需的联合读出）。** 第 115.2 节把预测商用于行动时，以及第 116.3 节末段和第 116.8 节“保持预测与行动闭合的最小响应细化”的表述，须相对于指定的必须动作读出 $b:X\to A$ 使用

$$
\widetilde c(x)=(c(x),b(x)).
$$

$\operatorname{Dyn}_I(\widetilde c)$ 是同时保留 $c,b$ 的干预闭合细化中的最小者；其空词坐标恢复当前必须动作。若仍使用 $\operatorname{Dyn}_I(c)$，则当前行动完备需要另外假设存在

$$
\beta:\operatorname{Dyn}_I(c)[X]\to A,
\qquad b=\beta\circ\operatorname{Dyn}_I(c),
$$

其中复合使用动态闭包到其实际像的映射。

证明。干预后任意词的响应等于干预前加上该首字母的词响应，故动态闭包的纤维被每次干预保持。联合读出的两投影恢复 $c,b$；任何同时保留两者的接口 $d$ 都通过配对因子保留 $\widetilde c$，再应用命题 118.7 的最小性。原读出单独不足的反例是

$$
X=A=\{0,1\},\quad O=\{*\},\quad U=\{e\},
\quad I_e=\operatorname{id},\quad c(x)=*,\quad b(x)=x.
$$

此时 $\operatorname{Dyn}_I(c)$ 恒定，不能恢复 $b$；而 $\operatorname{Dyn}_I(\widetilde c)$ 的空词已经区分两个状态。故独立动作要求不能由原动态闭包自动获得。若有多个必须动作或其他任务读出，应将它们的乘积一起纳入初始读出，结论按同一投影与配对适用。

**命题 118.9（第 116.4 节的整个操作语言与被动演化）。** 若 $u_*\notin U$ 是新增字母，旧字母的更新保持原样，则响应坐标的指标集由 $U^*$ 扩为

$$
(U')^*=(U\cup\{u_*\})^*,
\qquad
(U')^*\setminus U^*=\{w\in (U')^*:w\text{ 至少含一次 }u_*\}.
$$

新增字母可在词的任意位置出现，也可重复出现；不只增加以 $u_*$ 开头的词。因此完整响应等价满足

$$
\ker\operatorname{Dyn}_{I'}(c)
\subseteq\ker\operatorname{Dyn}_I(c).
$$

若没有输入字母，或所有允许更新均为恒等，则动态闭包与当前 $c$ 有相同纤维。若“没有干预”仍包含被动演化 $F$，则须把 $F$ 明确纳入更新或任务族，才会要求保留 $c(F^n(x))$。

证明。有限词属于 $(U')^*$ 而不属于 $U^*$，恰当其中出现了新字母。将扩充响应函数限制到旧词，即恢复旧响应，给出核的包含。空字母表只有空词；恒等更新的任意复合也是恒等，所以这两个情形均只比较当前 $c$。被动 $F$ 未列入时，所定义的词作用中没有 $F$，因而不能从该定义推出其未来读数相同。

**命题 118.10（第 116.5 节的剩余视野与稳定条件）。** 在固定的总更新模型上定义

$$
E_N(x,y)\quad\Longleftrightarrow\quad
\forall w\in U^*,\ |w|\le N\Longrightarrow c(I_w(x))=c(I_w(y)).
$$

有限深度接口恰保留被查询的这些响应；其正确递归为

$$
E_0(x,y)\Longleftrightarrow c(x)=c(y),
$$

$$
E_{N+1}(x,y)
\Longleftrightarrow
c(x)=c(y)\ \land\ \forall u\in U,\ E_N(I_u(x),I_u(y)).
$$

所以

$$
E_{N+1}\subseteq E_N,\qquad
E_{N+1}(x,y)\Longrightarrow E_N(I_u(x),I_u(y)),
$$

$$
N\ge1,\ E_N(x,y)\Longrightarrow E_{N-1}(I_u(x),I_u(y)).
$$

这些式子不宣称 $E_N$ 被一步更新保持在同一深度。若整个二元关系满足 $E_N=E_{N+1}$，则该层对全部更新稳定，并永久等于全部有限词的响应关系。这里需要关系在所有状态对上的相等，不能以一个状态对在相邻两层都成立来代替。

证明。将非空词唯一分成首字母与尾词，尾词长度减少一，得到递归；缩小查询词集得到包含。由全关系相等和递归，$E_N$ 的每对后继仍在 $E_N$ 中；沿词归纳，得到任意长度响应相等。这是第 106.2 节所用的永久稳定原理。在 $X,U,O$ 固定有限非空、更新为总函数且 $c:X\to O$ 满射时，直接使用第 106.3 节及[ControlledFiniteStability](../../../../D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.lean)的已有结论：存在最小稳定深度 $H$，并有

$$
H\le |X/E_\infty|-|O|\le |X|-|O|,
\qquad E_\infty=\bigcap_{n\ge0}E_n.
$$

应用该界时可把 $O$ 限制为实际像 $c[X]$，以满足满射条件；该有限性条件不能由只固定一个查询深度代替。递减视野的部分操作版本亦见[Zeckendorf 卷定理 446.2](../CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)。

同层闭合与逐对稳定的反例可同时取

$$
X=\{0,1,2,3,4\},\quad U=\{e\},\quad
I_e(i)=\min\{i+1,4\},\quad c(i)=\mathbf 1_{\{i=4\}}.
$$

状态零与一在深度一及二的响应都相同，但三次更新后的读数分别为零与一。因此 $E_1(0,1)$ 与 $E_2(0,1)$ 都成立，不蕴含完整等价；同时 $E_2(0,1)$ 成立而 $E_2(I_e(0),I_e(1))=E_2(1,2)$ 不成立。

若某个记录 $q$ 合并 $x,y$，而某词 $w$ 使 $c(I_w(x))\ne c(I_w(y))$，该词证明任务 $c\circ I_w$ 不能经 $q$ 因子化。第 116.5 节“某条长度至多 $N$ 的词把它们分开，则当前接口不闭合”应按这一任务不足解释；它本身不证明深度 $N$ 接口违反同层更新不变性，后者须另检验上面的后继关系。

**命题 118.11（第 117.3、117.4 节的时域及共同选择）。** 固定共同的有限非空动作集 $A$、确定性总转移 $T$、实值奖励 $r$ 与终值 $V^0$，令

$$
V_0=V^0,\qquad
Q_n(s,a)=r(s,a)+V_n(T(a,s)),
\qquad V_{n+1}(s)=\max_{a\in A}Q_n(s,a),
$$

$$
\operatorname{Opt}_n(s)=\operatorname*{arg\,max}_{a\in A}Q_n(s,a).
$$

第 117.3 节的下标 $n$ 计续接的 $n$ 个阶段；再加当前动作，所优化的总阶段数是 $n+1$。若微观与宏观模型通过 $\alpha$ 同时满足第 117.1 节的转移、奖励和终值三项因子化，则对同一个 $n$ 有

$$
Q_n^{m}(s,a)=Q_n^{M}(\alpha(s),a),\qquad
\operatorname{Opt}_n^{m}(s)=\operatorname{Opt}_n^{M}(\alpha(s)).
$$

这些集合非空。固定 $A$ 上一个全序，取每个集合的最小元素，就得到只依赖 $\alpha(s)$ 与剩余阶段数的共同确定性最优选择。它不要求不同历史任意挑出的最优标签相等。

证明。由[有限时域值因子化](../../../../D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization.lean)恢复续值，再用奖励与转移相容，得到各动作分数相同；[最优动作下沉](../../../../D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent.lean)给出集合相等。有限非空实值集合有最大值，其最大化动作集合因此非空；相同非空集合在固定全序下有同一最小元素。

更一般地，对任意记录 $q$ 和同一时域的最优集合，只要求存在共同最优策略的准确条件是

$$
\forall z\in q[X],\qquad
\bigcap_{s\in q^{-1}(z)}\operatorname{Opt}_n(s)\ne\varnothing.
$$

策略的共同输出给出交集中的元素；反向在每个交集中按固定全序取最小元素即可。故集合相等是足够条件，单纯两个选择标签不同不是障碍判据。若在共同动作、同一时域和同一任务下，确有同一抽象纤维的最优集合不同，才可据前述因子化定理断定三项相容条件不能全部成立。第 117.7 节“如果要求有限时域行动，就必须验证值函数闭合”仅适用于任务还要求恢复最优价值的情形；仅选择一个最优动作时，上述非空交集已是准确判据。例如两状态使用恒等转移、单一动作、零终值，阶段奖励分别为零与一，常记录仍支持唯一动作，但正时域 $n$ 的值分别为零与 $n$。

**命题 118.12（并列最优及跨时域选择的两个反例）。** 第 117.4 节“保证这种分离不会发生”仅排除在其假设下最优集合的分离，不排除任意最优标签选择的分离；第 115.5 节末段所说“不同的最优动作分布”也不能仅凭分布不同排除共同最优策略。各时域最优集合在抽象纤维上相同，还不保证存在对所有时域都最优的、与剩余阶段数无关的平稳策略。

证明。第一个例子取微观状态 $\{0,1\}$、宏观状态 $\{*\}$、常抽象、动作 $A=\{L,R\}$。两层每个动作的转移均为恒等，全部奖励与终值均为零。三项因子化全部成立，且

$$
\forall n,s,\qquad V_n(s)=0,\qquad\operatorname{Opt}_n(s)=\{L,R\}.
$$

在状态零选择 $L$、在状态一选择 $R$，两者都是最优动作；对应的两个点质量分布也都最优。固定选 $L$ 仍是共同最优策略。若另把这两个不同标签规定成必须实现的 $b(0),b(1)$，那是命题 118.3 的另一个任务，不能与只要求最优混同。

第二个例子取状态 $\{s,g\}$、动作 $\{W,H\}$、恒等抽象与零终值。规定

$$
T(W,s)=s,\quad r(s,W)=1,\qquad
T(H,s)=g,\quad r(s,H)=0,
$$

$$
T(a,g)=g,\quad r(g,a)=2\qquad(a\in\{W,H\}).
$$

恒等抽象满足全部因子化。一步时在 $s$ 的分数为一与零，故 $\operatorname{Opt}_0(s)=\{W\}$；两步值为 $V_2(s)=2,V_2(g)=4$，三步的当前分数为三与四，故 $\operatorname{Opt}_2(s)=\{H\}$。同一平稳选择不能同时满足这两个单点要求。

**命题 118.13（值相等不能反推全部控制因子）。** 第 117.6 节的值相等只给指定任务的数值结论。即使所有有限时域的值都在同一纤维上相等，也不蕴含最优动作集合、转移或奖励因子化；只给一个正时域的值相等，还不能推出终值因子化。若相等的时域包含零，则终值因子化由 $V_0=V^0$ 直接成立，但仍不推出另外两项。

证明。先取两个状态 $x,y$、常记录、动作 $\{L,R\}$、恒等转移和零终值，令

$$
r(x,L)=r(y,R)=1,\qquad r(x,R)=r(y,L)=0.
$$

于是 $V_n(x)=V_n(y)=n$，而对每个 $n\ge0$，最优集合分别为 $\{L\}$ 与 $\{R\}$；奖励也不经常记录因子化。

再取三个状态 $x,y,z$，$\alpha(x)=\alpha(y)=0,\alpha(z)=1$，一个动作 $a$，零奖励与零终值，令

$$
T(a,x)=x,\qquad T(a,y)=z,\qquad T(a,z)=z.
$$

全部值恒零，但同一抽象初值零有抽象后继零与一，不存在相容的宏观转移。

最后取两个状态、常记录、一个动作与恒等转移，令

$$
r(x,a)=0,\quad V^0(x)=0,\qquad
r(y,a)=-1,\quad V^0(y)=1.
$$

一步值均为零，终值却不同。三个例子分别排除所述逆推；关于零时域的限定直接来自递归初值。

**命题 118.14（有限构型与密度矩阵的不同载体）。** 第 115.4、116.6、117.6 节的量子解释不由经典构型有限性自动成立。即使合法构型集 $\mathcal W_L$ 有限，若

$$
\mathcal H_Z=\operatorname{span}\{|w\rangle:w\in\mathcal W_L\},
\qquad \dim\mathcal H_Z\ge2,
$$

其全部密度矩阵集合 $\mathcal D(\mathcal H_Z)$ 仍为无限集。对指定通道词 $\Phi_w$ 与 POVM $\{M_o\}_o$，可以定义抽象响应函数

$$
\rho\longmapsto
\left(\operatorname{tr}(M_o\Phi_w(\rho))\right)_{w,o},
\qquad M_o\ge0,\quad\sum_oM_o=\mathbf 1.
$$

这是每个指定实验的概率函数族。第 116.8 节关于“经典轨迹函数”的量子边界须区分此集合论函数与物理编码：前者可以如此定义，后者不由定义给出。该函数不自动给出一个物理 CPTP 编码，也不自动给出从同一次制备中同时读出这些概率精确值的经典寄存器。

证明。取两个正交合法基态 $|e_0\rangle,|e_1\rangle$，则

$$
\rho_p=p|e_0\rangle\langle e_0|+(1-p)|e_1\rangle\langle e_1|,
\qquad 0\le p\le1
$$

彼此不同，已构成连续一族密度矩阵。故有限 Hilbert 维数并非有限状态集合的基数。

抽象函数与物理精确标签编码的区别甚至在此对角族上存在。若某通道 $\mathcal E$ 能把 $p=0,\tfrac12,1$ 的精确概率标签输出为三个互相正交的确定经典旗标，则既要求

$$
\mathcal E(\rho_{1/2})=|f_{1/2}\rangle\langle f_{1/2}|,
$$

又由通道的仿射性要求

$$
\mathcal E(\rho_{1/2})
=\tfrac12|f_0\rangle\langle f_0|+\tfrac12|f_1\rangle\langle f_1|.
$$

两式的支持子空间不同，矛盾。抽象地写出各响应概率不受此限制，因为它没有宣称存在这种确定标签通道。抽样获得一个结果、在重复制备下估计概率、以及一次制备输出概率的精确标签，是不同的输出任务。

**命题 118.15（第 115.4 节相位响应的物理假设与行动边界）。** 在指定的有限维正交基下，若使用该节的 Schur 形式作为记录通道，须要求同阶记录矩阵 $R$ 半正定且 $R_{ii}=1$；此时

$$
\mathcal C(\rho)_{ij}=R_{ij}\rho_{ij}
$$

确为 CPTP 映射。若使用该节的三态耦合，取 $g\in\mathbb R\setminus\{0\}$，在合法子空间 $\operatorname{span}\{|00\rangle,|01\rangle,|10\rangle\}$ 上规定

$$
H=g\bigl(|00\rangle\langle01|+|00\rangle\langle10|
+|01\rangle\langle00|+|10\rangle\langle00|\bigr).
$$

取 $\hbar=1$；若嵌入更大的空间，要求自伴扩张满足 $[H,P_Z]=0$，其他允许通道也须保持合法态域。则对该节的 $|B\rangle,|D\rangle$，时间 $\tau$ 后测量 $|00\rangle\langle00|$ 的概率分别为

$$
p_B(\tau)=\sin^2(\sqrt2g\tau),\qquad p_D(\tau)=0.
$$

当 $\sin^2(\sqrt2g\tau)>0$ 时，这是不同实验响应的见证；要进一步推出必须动作或最优动作不同，还须指定相应任务或奖励，不能只用耦合差异推出行动标签差异。

证明。半正定矩阵分解给出系数 $v_{i\lambda}$ 满足

$$
R_{ij}=\sum_\lambda v_{i\lambda}\overline{v_{j\lambda}},
\qquad \sum_\lambda|v_{i\lambda}|^2=1.
$$

对角 Kraus 算子 $K_\lambda=\operatorname{diag}(v_{i\lambda})$ 实现 $\mathcal C$，且 $\sum_\lambda K_\lambda^\dagger K_\lambda=\mathbf1$。相位耦合的 $H$ 自伴，并满足

$$
H|B\rangle=\sqrt2g|00\rangle,\quad
H|00\rangle=\sqrt2g|B\rangle,\quad H|D\rangle=0.
$$

因此

$$
e^{-i\tau H}|B\rangle
=\cos(\sqrt2g\tau)|B\rangle-i\sin(\sqrt2g\tau)|00\rangle,
\qquad e^{-i\tau H}|D\rangle=|D\rangle.
$$

Born 规则给出所列概率。另一方面，若所有动作奖励和终值均为零，任何允许动作均最优，故响应不同并不强制最优标签不同。

**命题 118.16（重复测量与反馈的条件性经典描述）。** 第 117.6 节“先固定一个 POVM 或记录通道”不足以直接得到确定性 Bellman 模型。设动作集 $A$ 与结果集 $O$ 有限非空，对每个动作给定量子仪器

$$
\{\mathcal J_{a,o}:o\in O\},
\qquad \mathcal J_{a,o}\text{ 完全正且不增迹},
\qquad \sum_o\mathcal J_{a,o}\text{ 保迹}.
$$

每个分支须保持指定合法子空间；若有可回流的环境记忆，态描述须包含它或足以预测其影响的信息。仪器给出

$$
p(o\mid\rho,a)=\operatorname{tr}\mathcal J_{a,o}(\rho),
\qquad
\rho'_{a,o}=\frac{\mathcal J_{a,o}(\rho)}{p(o\mid\rho,a)}
\quad\text{仅在 }p(o\mid\rho,a)>0\text{ 时定义}.
$$

若另有一个非空有限经典状态描述集 $Z$，控制器在决策前能由实际可访问记录确定 $z$，每个动作在每个可达描述处均允许，且在同一当前描述 $z$ 下的所有可达历史，对每个动作均有相同的后继描述与结果联合分布

$$
P_a(z',o\mid z),\qquad
\sum_{z',o}P_a(z',o\mid z)=1,
$$

并且阶段奖励和终值分别由实值函数 $r(z,a,z',o)$ 与 $V^0(z)$ 给出，则有限时域的期望价值递归为

$$
V_0(z)=V^0(z),\qquad
V_{n+1}(z)=\max_{a\in A}
\sum_{z',o}P_a(z',o\mid z)
\bigl(r(z,a,z',o)+V_n(z')\bigr).
$$

此结论以所列受控 Markov 充分性为假设；当前输出字母有限、记录寄存器维数有限或给定一个 POVM，都不单独蕴含该假设。若每个 $(z,a)$ 的后继描述边缘集中在一个 $T(a,z)$，并定义

$$
\bar r(z,a)=\sum_{z',o}P_a(z',o\mid z)r(z,a,z',o),
$$

则在这一确定后继描述下，上式化为

$$
V_{n+1}(z)=\max_{a\in A}\bigl(\bar r(z,a)+V_n(T(a,z))\bigr).
$$

使用第 117 节的确定性因子化结论时，还须对这个 $T,\bar r,V^0$ 验证同一抽象的三项条件。

证明。完全正与迹条件使各分支概率非负且总和为一；正概率分支的归一化输出为密度矩阵，零概率分支不要求定义后验。给定受控 Markov 充分性，先条件于当前动作，再条件于下一描述与结果，有限期望的全概率分解及剩余时域归纳给出递归。有限非空动作集保证最大值可达，随机化当前动作只形成动作价值的凸组合，不能超过其最大值。若后继描述边缘为点质量，续值项从求和中提出，即得最后一式。

随机后继的直接例子是对 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ 作计算基底投影测量。两结果各有概率 $1/2$；记录结果的两个后继历史不同，条件态也分别为 $|0\rangle\langle0|$ 与 $|1\rangle\langle1|$。因此重复或反馈测量一般产生随机受控核。将结果平均后的通道作为密度矩阵上的确定函数，是另一个明确的状态描述；它不自动保留可按结果分支的反馈策略。经典核的风险与价值结论由所指定实验及其经典描述承担，不把该核认同为全部相干量子动力学。

<a id="entry-565"></a>

## 追加锚（本行以下为增补区）
<a id="section-119"></a>

## 119. 记录模拟的缺陷与决策风险：从保留历史到可执行误差界

**定义 119.1（原历史载体与有限观察的取域）。** 原情境仍取[《情境时空算术》定义 1–6](../CONTEXTUAL_SPACETIME_ARITHMETIC.md)的

$$
C=(E_C,\prec,t,x,\sigma,\rho,\Omega),\qquad
\eta=(C,A_{\rm sel}),\qquad A_{\rm sel}\subseteq\Omega\subseteq E_C,
$$

其中 $E_C$ 是有限事件出现集，$\prec$ 是严格偏序，$t:E_C\to\mathbb Z$、$x:E_C\to\mathbb Z^3$、$\sigma:E_C\to\{+1,-1\}$ 及来源树映射 $\rho$ 保留原类型，且 $e\prec f$ 蕴含 $t(e)<t(f)$。算术载体仍要求 $\sum_{e\in\Omega}\sigma(e)=0$，读数为 $q_{\rm CSA}(\eta)=\sum_{e\in A_{\rm sel}}\sigma(e)$。选择是当前区域的任意子集；若任务还使用各阶段的选择或区域快照，就将这些快照另列为历史数据。时间复合的原定义域仍为

$$
\forall e\in E_{C_1}\ \forall f\in E_{C_2},\qquad t_1(e)<t_2(f).
$$

用于下述有限观察比较的历史族，是预先指定的原合法对象或合法执行历史的有限非空族；每条执行路径分别满足其操作守卫。有限标签及其概率律是这个族的观察数据，不替换档案、来源、绝对时间、偏序、当前区域或选择。若只讨论抽象统计实验，则直接使用定义 119.2，不预设其标签已实现为原历史。

**定义 119.2（有限实验、共同决策与单向缺陷）。** 设隐藏参数集 $\Theta$、目标观察集 $Y$、保留观察集 $Z$、共同动作集 $A$ 均有限非空。参数 $\theta\in\Theta$ 固定而对决策者未知。实验由实值行概率给出：

$$
F(y\mid\theta)\ge0,\quad \sum_{y\in Y}F(y\mid\theta)=1,
\qquad
E(z\mid\theta)\ge0,\quad \sum_{z\in Z}E(z\mid\theta)=1.
$$

记相应概率行为 $F_\theta,E_\theta$。模拟器 $S:Z\to\mathcal P(Y)$ 表示从 $Z$ 到 $Y$ 的随机核，其中 $\mathcal P(Y)$ 是 $Y$ 上的概率单纯形，即 $S(y\mid z)\ge0$ 且 $\sum_yS(y\mid z)=1$；同一个 $S$ 用于所有 $\theta$，不能读取隐藏参数。复合律与全变差约定为

$$
(SE)_\theta(y)=\sum_z E(z\mid\theta)S(y\mid z),\qquad
\operatorname{TV}(p,q)=\frac12\sum_i|p(i)-q(i)|.
$$

定义模拟误差及单向缺陷

$$
\varepsilon(S)=\max_{\theta\in\Theta}\operatorname{TV}(F_\theta,(SE)_\theta),
\qquad
\delta(F\mid E)=\inf_{S:Z\to\mathcal P(Y)}\varepsilon(S),
$$

方向是从保留实验 $E$ 模拟目标实验 $F$；“目标”与“保留”本身不预设信息次序。给定先验 $\mu(\theta)\ge0$、$\sum_\theta\mu(\theta)=1$ 及损失 $0\le\ell(\theta,a)\le1$，观察集为 $O$ 的实验 $G$ 上的随机决策为 $d:O\to\mathcal P(A)$，其代价及最优 Bayes 风险为

$$
\mathcal C_{\mu,\ell}(G,d)
=\sum_{\theta\in\Theta}\mu(\theta)
  \sum_{o\in O}\sum_{a\in A}G(o\mid\theta)d(a\mid o)\ell(\theta,a),
\qquad
R_{\mu,\ell}(G)=\inf_d\mathcal C_{\mu,\ell}(G,d).
$$

比较中始终使用同一 $\mu,\ell,A$，简记风险为 $R(G)$。这里 $E,F,S,d$ 均为非负归一的概率核，不能以任意带符号矩阵替代。

**命题 119.3（有限实值极值与扩展非负实数的对应）。** 在定义 119.2 下，$R(E),R(F),\delta(F\mid E)$ 都是 $[0,1]$ 中的实数，其下确界均可取到。把非负实数嵌入 $[0,\infty]$ 后，这些值分别等于同一随机核族上的扩展非负实数下确界。此对应适用于[有限实验风险与缺陷的定义及定理 `deficiency_risk_bound`](../../../../D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.lean)所采用的下确界约定。

证明。概率行的全变差在 $[0,1]$ 内，且每个代价是 $[0,1]$ 中损失值的概率加权和。非空输出集提供常值确定性核，所以各优化域非空。有限个概率单纯形的乘积是非空紧集；代价是连续函数，模拟误差是有限个连续全变差函数的最大值，亦连续。因此三种下确界均为取得的有限最小值。非负实数的嵌入保持这些值的次序及最小元，故在 $[0,\infty]$ 中取下确界得到同一个嵌入值。证毕。

**定理 119.4（缺陷控制有界决策风险）。** 在定义 119.2 的全部假设下，

$$
R(E)\le R(F)+\delta(F\mid E).
$$

这是[定理 `deficiency_risk_bound`](../../../../D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.lean)在上述有限实值约定下的风险转移结论；固定模拟器的风险比较见[定理 `bounded_loss_risk_stability_of_simulator`](../../../../D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.lean)。

证明。先给出两个有限概率不等式。若 $p,q$ 是同一有限集上的概率，$h_i=p(i)-q(i)$，则 $\sum_i h_i=0$，从而

$$
\sum_{h_i>0}h_i=\sum_{h_i<0}(-h_i)=\frac12\sum_i|h_i|.
$$

对 $0\le f(i)\le1$，丢掉非正项并以一控制正项，得到 $\sum_i h_i f(i)\le\operatorname{TV}(p,q)$；交换 $p,q$ 得

$$
\left|\sum_i p(i)f(i)-\sum_i q(i)f(i)\right|
\le\operatorname{TV}(p,q).
$$

因此 $[0,1]$ 损失对应的系数是一。其次，任一共同随机核 $K$ 满足

$$
\begin{aligned}
\operatorname{TV}(Kp,Kq)
&=\frac12\sum_j\left|\sum_i(p(i)-q(i))K(j\mid i)\right|\\
&\le\frac12\sum_i|p(i)-q(i)|\sum_jK(j\mid i)
=\operatorname{TV}(p,q).
\end{aligned}
$$

现在固定模拟器 $S$ 和基于 $F$ 的任意决策 $d_F$，在 $E$ 上执行

$$
d_E(a\mid z)=\sum_y S(y\mid z)d_F(a\mid y).
$$

各项非负，且 $\sum_a d_E(a\mid z)=\sum_yS(y\mid z)=1$，所以 $d_E$ 是合法决策。有限和交换给出 $d_EE_\theta=d_F(SE)_\theta$。对每个 $\theta$，随机后处理的全变差收缩及上述损失不等式给

$$
\begin{aligned}
\sum_a(d_EE)_\theta(a)\ell(\theta,a)
&\le\sum_a(d_FF)_\theta(a)\ell(\theta,a)
   +\operatorname{TV}(d_F(SE)_\theta,d_FF_\theta)\\
&\le\sum_a(d_FF)_\theta(a)\ell(\theta,a)+\varepsilon(S).
\end{aligned}
$$

以非负的 $\mu(\theta)$ 加权求和，并使用 $\sum_\theta\mu(\theta)=1$，得到

$$
R(E)\le\mathcal C_{\mu,\ell}(E,d_E)
\le\mathcal C_{\mu,\ell}(F,d_F)+\varepsilon(S).
$$

任取 $\eta>0$，分别选取代价小于 $R(F)+\eta/2$ 的决策和误差小于 $\delta(F\mid E)+\eta/2$ 的模拟器。两者的优化域独立，故 $R(E)<R(F)+\delta(F\mid E)+\eta$。对所有 $\eta>0$ 成立即得结论；此步只需下确界逼近，不依赖选择最优核。证毕。

**命题 119.5（真实经典粗化的双边风险界与必要方向）。** 若另有一个与 $\theta$ 无关的随机核 $C:Y\to\mathcal P(Z)$ 满足

$$
E_\theta(z)=(CF)_\theta(z)=\sum_yF_\theta(y)C(z\mid y)
\qquad(\theta\in\Theta),
$$

则

$$
0\le R(E)-R(F)\le\delta(F\mid E).
$$

若只给定义 119.2 的两个实验，则 $R(F)\le R(E)$ 不必成立，定理 119.4 的单向风险界仍成立。

证明。任取 $E$ 上的决策 $d_E$，令 $d_F(a\mid y)=\sum_z C(z\mid y)d_E(a\mid z)$。它是随机核，且 $d_FF=d_EE$，所以两代价相等。对所有 $d_E$ 取下确界给出 $R(F)\le R(E)$，再用定理 119.4 得到双边界。

为证明没有粗化关系时左界可以失败，取 $\Theta=Z=A=\{0,1\}$、$Y=\{*\}$、均匀先验和 $\ell(\theta,a)=\mathbf1_{\{a\ne\theta\}}$，令 $E_\theta=\delta_\theta$、$F_\theta=\delta_*$。观察 $E$ 后选 $a=\theta$ 给 $R(E)=0$。只观察 $*$ 的任意决策成功率均为 $\tfrac12(d(0\mid*)+d(1\mid*))=1/2$，故 $R(F)=1/2$。丢弃 $E$ 的输出能精确模拟 $F$，所以 $\delta(F\mid E)=0$；单向不等式为 $0\le1/2$，而左界失败。证毕。

**定理 119.6（确定性标签压缩的精确缺陷）。** 设 $X$ 为有限非空标签集，$q:X\to B$ 满射到其实际像 $B$。取 $\Theta=Y=X$、$Z=B$，并令

$$
F_x=\delta_x,\qquad E_x=\delta_{q(x)},\qquad
X_b=q^{-1}(b),\qquad m_b=|X_b|,\qquad m_{\max}=\max_{b\in B}m_b.
$$

则 $m_b\ge1$，且

$$
\delta(F\mid E)=1-\frac1{m_{\max}}.
$$

证明。对任意模拟器 $S:B\to\mathcal P(X)$，记 $S_b(x)=S(x\mid b)$。概率归一性给

$$
\operatorname{TV}(\delta_x,S_{q(x)})
=\frac12\left(1-S_{q(x)}(x)+\sum_{u\ne x}S_{q(x)}(u)\right)
=1-S_{q(x)}(x).
$$

取最大纤维 $X_{b_*}$。由于 $\sum_{x\in X_{b_*}}S_{b_*}(x)\le1$，其中至少一个 $x$ 满足 $S_{b_*}(x)\le1/m_{\max}$，所以每个模拟器的最坏参数误差至少为 $1-1/m_{\max}$。反向定义只依赖保留标签的模拟器

$$
S(x\mid b)=
\begin{cases}
1/m_b,&q(x)=b,\\
0,&q(x)\ne b.
\end{cases}
$$

每行在非空纤维上均匀且总和为一。参数 $x\in X_b$ 的误差恰为 $1-1/m_b$，其最大值为 $1-1/m_{\max}$。上下界相合，得精确公式。这个模拟器只读取 $b$，并未读取真正的 $x$。证毕。

**定理 119.7（任意先验下的完整标签重建风险）。** 沿用定理 119.6，另取动作 $A=X$、损失 $\ell(x,a)=\mathbf1_{\{a\ne x\}}$ 及任意概率先验 $\mu$，允许任意标签的先验质量为零。则

$$
R(F)=0,\qquad
R(E)=1-\sum_{b\in B}\max_{x\in X_b}\mu(x).
$$

证明。细观察直接给出 $x$，选 $a=x$ 即得零代价，非负性给 $R(F)=0$。粗观察决策 $d$ 的总成功率为

$$
\operatorname{Succ}(d)=\sum_{b\in B}\sum_{x\in X_b}\mu(x)d(x\mid b).
$$

令 $M_b=\max_{x\in X_b}\mu(x)$。每个纤维对成功率的贡献是动作概率对系数 $\mu(a)\mathbf1_{\{a\in X_b\}}$ 的凸组合，故

$$
\sum_{x\in X_b}\mu(x)d(x\mid b)
\le M_b\sum_{x\in X_b}d(x\mid b)\le M_b.
$$

在每个非空有限纤维中选择一个达到 $M_b$ 的代表 $x_b$，并令 $d(x_b\mid b)=1$，则同时达到所有上界。失败风险等于一减成功率，得到所述公式。即使 $M_b=0$，任一代表仍达到上界，证明无需按该纤维质量做条件归一化。证毕。

**命题 119.8（三位合法行的奇偶压缩）。** 取[Zeckendorf 源卷定义 3、9、11](../CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)的权重 $G_0=1,G_1=2,G_2=3$。本条显示字 $w=w_2w_1w_0$ 按高位到低位书写，是该源定义 9 中低位到高位次序 $(c_0,c_1,c_2)$ 的反转。令

$$
X=\{000,001,010,100,101\},\qquad
V(w)=3w_2+2w_1+w_0,\qquad q(w)=V(w)\bmod2.
$$

这是单行数值观察：源中的 $s(n)$ 是整数 $n$ 自身的规范行，而 $K(n)(p,j)=s(v_p(n))_j$ 是正整数的逐素数指数表；本条的 $V$ 与 $q$ 不把这两个编码认作同一对象。对 $F_w=\delta_w$、$E_w=\delta_{q(w)}$，有

$$
\delta(F\mid E)=\frac23.
$$

在 $X$ 上取均匀先验、完整标签重建动作及零一损失，则

$$
R(F)=0,\qquad R(E)=\frac35.
$$

证明。三个位置没有相邻两个一的全部合法字恰为所列五字，其 $V$ 值依次为 $0,1,2,3,4$。因此

$$
X_0=\{000,010,101\},\qquad X_1=\{001,100\},
\qquad m_0=3,\quad m_1=2.
$$

定理 119.6 给出 $1-1/3=2/3$。均匀先验使两个纤维的最大单点质量都为 $1/5$，定理 119.7 给出 $1-1/5-1/5=3/5$。这些公式已对全部随机决策取最优值；$3/5$ 是该先验和重建任务的平均风险，$2/3$ 是不依赖先验的最坏参数模拟缺陷。证毕。

**命题 119.9（任务相对性与资源量的独立性）。** 若存在共同动作 $a_*\in A$，满足

$$
\ell(\theta,a_*)=\min_{a\in A}\ell(\theta,a)
\qquad(\theta\in\Theta),
$$

则对定义 119.2 的任意实验 $G$，

$$
R(G)=\sum_\theta\mu(\theta)\ell(\theta,a_*).
$$

因而即使 $\delta(F\mid E)>0$，也可以有 $R(E)-R(F)=0$；完整标签重建的缺陷不强制等于某个指定预测或动作任务的风险损失。另给每个核任意正实数值的执行时间或资源费用函数，在保持 $E,F,\mu,\ell$ 不变时，定义 119.2 的缺陷与风险均不变。

证明。对固定 $\theta$，任意随机动作的期望损失至少为 $\ell(\theta,a_*)$。加权求和给出风险下界；不看观察而总选 $a_*$ 达到它。取命题 119.8 的实验，并取具有恒零损失的共同动作，得到缺陷为 $2/3$ 而风险差为零的实例。最后，缺陷和风险的定义只用实验概率、先验、损失及随机核族；所附执行时间和费用不出现在这些表达式中，改变它们不改变表达式的值。因此仅凭纤维基数和这些风险公式，不能推出物理时间、存储或耗散的数值关系。证毕。

**假设 119.10（固定量子制备、实际测量与记录层）。** 取有限维非零复 Hilbert 空间 $\mathcal H$ 和有限非空制备标签集 $\Theta$。每个 $\theta$ 指定密度算子 $\varrho_\theta\ge0$、$\operatorname{tr}\varrho_\theta=1$。给定实际采用的固定有限 POVM

$$
H_y\ge0,\quad\sum_{y\in Y}H_y=I_{\mathcal H},
\qquad
G_z\ge0,\quad\sum_{z\in Z}G_z=I_{\mathcal H},
$$

其中 $Y,Z$ 非空，且两族效应不依赖未知 $\theta$。采用 Born 律定义

$$
F_\theta(y)=\operatorname{tr}(\varrho_\theta H_y),\qquad
E_\theta(z)=\operatorname{tr}(\varrho_\theta G_z).
$$

这里 $\theta$ 是制备标签，不预设为未知计算基底标签；允许 $\varrho_\theta$ 在合法 Zeckendorf 子空间内具有相干非对角项。若要把 $E$ 称为已形成细记录的实际经典压缩，另假设先形成 $y$，随后仅用与 $\theta$ 无关的随机核 $C(z\mid y)$ 产生 $z$。此时该压缩的效应为 $G_z=\sum_yC(z\mid y)H_y$。单独的效应等式只规定当前概率，不规定输出的量子后态或测量仪器。

**命题 119.11（固定 Born 实验的风险界及联合样本的非唯一性）。** 在假设 119.10 下，$E,F$ 满足定义 119.2 的行概率条件。故对同一有限非空动作集、概率先验及 $[0,1]$ 损失，定理 119.4 适用；若另有该假设中的实际经典压缩，则命题 119.5 的双边风险界适用。给定这两个当前实验的概率行，并不唯一确定它们之间的联合样本律，更不提供不相容测量在同一次运行中的反事实样本值。

证明。$\operatorname{tr}(\varrho_\theta H_y)=\operatorname{tr}(\varrho_\theta^{1/2}H_y\varrho_\theta^{1/2})\ge0$，对 $y$ 求和为 $\operatorname{tr}\varrho_\theta=1$；$G$ 同理。实际经典压缩时由全概率公式得到 $E=CF$，所以直接应用对应的风险界。上述论证不要求密度算子在某一基底对角。

联合律的非唯一性已在一个制备标签、两个均匀二元边缘上出现：令 $J_1(0,0)=J_1(1,1)=1/2$、其余为零，或令四个 $J_2(y,z)=1/4$，两者边缘相同而联合律不同。这只是概率律之间两种数学耦合，不断言任一耦合是两个不相容量子测量的共同物理实现。模拟器同样只构造目标概率律，不能由此识别为另一测量在同次运行中本会产生的结果。证毕。

**命题 119.12（同奇偶效应、零当前缺陷与不同的两阶段辨识风险）。** 取命题 119.8 的高位到低位合法三位集合 $X$，令

$$
\mathcal H_Z=\operatorname{span}\{|w\rangle:w\in X\},\qquad
P_w=|w\rangle\langle w|,\qquad
Q_b=\sum_{w\in X_b}P_w\quad(b\in\{0,1\}),
$$

其中所列基正交归一，$I$ 表示 $\mathcal H_Z$ 上的恒等算子。考虑两种理想投影测量仪器的未归一分支：粗奇偶 Lüders 仪器

$$
\mathcal L_b(\varrho)=Q_b\varrho Q_b
$$

与完整基底测量后只在经典层忘记细标签的仪器

$$
\mathcal M_b(\varrho)=\sum_{w\in X_b}P_w\varrho P_w.
$$

它们的每个分支均完全正且不增迹，全部分支之和保迹，并有相同的奇偶效应 $Q_b$，所以对每个密度算子给出相同的即时奇偶概率。令隐藏制备标签为 $\theta\in\{+,-\}$，取

$$
|\psi_+\rangle=\frac{|000\rangle+|010\rangle}{\sqrt2},\qquad
|\psi_-\rangle=\frac{|000\rangle-|010\rangle}{\sqrt2},\qquad
\varrho_\theta=|\psi_\theta\rangle\langle\psi_\theta|.
$$

记第一阶段粗 Lüders 奇偶记录的实验为 $E$，完整基底记录的实验为 $F$。则

$$
E_+=E_-=\delta_0,\qquad
F_+=F_-=\tfrac12\delta_{000}+\tfrac12\delta_{010},\qquad
\delta(F\mid E)=\delta(E\mid F)=0.
$$

这里的参数是制备标签 $\{+,-\}$，不同于命题 119.8 中待完整重建的基底标签 $X$；两个缺陷公式属于不同的实验族。令 $P_+=|\psi_+\rangle\langle\psi_+|$，在上述两种仪器之后都对残余系统实际执行第二次测量 $\{P_+,I-P_+\}$，以 $r=1$ 记 $P_+$ 结果，则

$$
\Pr_{\mathcal L}(r=1\mid+) =1,\qquad
\Pr_{\mathcal L}(r=1\mid-) =0,\qquad
\Pr_{\mathcal M}(r=1\mid\theta)=\frac12\quad(\theta=+,-).
$$

因此在均匀先验、动作 $\{+,-\}$ 和零一辨识损失下，以完整两阶段经典记录作决策的风险分别为

$$
R(\mathcal L\hbox{ 的两阶段记录})=0,\qquad
R(\mathcal M\hbox{ 的两阶段记录})=\frac12.
$$

此命题是“相同即时效应不决定两步联合律”的一个合法三位实例；另一明确的二维仪器分离结论见[定理 `same_effects_different_two_step_joint_law`](../../../../D5/S3/Quantum/Measurement/StaticEffectSequentialSeparation.lean)。

证明。$Q_0,Q_1$ 是互相正交且和为 $I$ 的投影。$\mathcal L$ 的 Kraus 算子为 $Q_b$，$\mathcal M$ 的分支 Kraus 算子为 $\{P_w:w\in X_b\}$；分别有 $Q_b^*Q_b=Q_b$ 与 $\sum_{w\in X_b}P_w^*P_w=Q_b$。故两仪器完全正，分支不增迹，全部分支之和保迹，且

$$
\operatorname{tr}\mathcal L_b(\varrho)
=\operatorname{tr}(\varrho Q_b)
=\operatorname{tr}\mathcal M_b(\varrho)
$$

对全部 $\varrho$ 成立。$000,010$ 都在偶纤维中，故 $Q_0\psi_\theta=\psi_\theta$、$Q_1\psi_\theta=0$，而两个非零基底振幅的模平方均为 $1/2$，得到所述第一阶段行概率。由 $S(\cdot\mid b)=\tfrac12\delta_{000}+\tfrac12\delta_{010}$（对两个 $b$ 都取此行）可从 $E$ 精确模拟 $F$；由确定性奇偶核可从 $F$ 精确模拟 $E$。这些核与 $\theta$ 无关，故两个单向缺陷均为零。

两种仪器的第一阶段实际后态则为

$$
\mathcal L_0(\varrho_\theta)=\varrho_\theta,\qquad
\mathcal M_0(\varrho_\theta)=\tau:=\frac{P_{000}+P_{010}}2,
\qquad
\mathcal L_1(\varrho_\theta)=\mathcal M_1(\varrho_\theta)=0.
$$

由于偶结果概率为一，零分支以外不需要再归一。正交关系 $\langle\psi_+,\psi_-\rangle=0$ 给出 $\operatorname{tr}(P_+\varrho_+)=1$、$\operatorname{tr}(P_+\varrho_-)=0$，而

$$
\operatorname{tr}(P_+\tau)
=\frac12\bigl(|\langle\psi_+,000\rangle|^2+|\langle\psi_+,010\rangle|^2\bigr)=\frac12.
$$

因此 $\mathcal L$ 的两阶段记录 $(b,r)$ 完全区分两种制备，按 $r=1$ 选 $+$、$r=0$ 选 $-$ 得零风险。$\mathcal M$ 的两阶段记录在两种制备下具有同一律 $J$；任意决策的均匀先验成功率为

$$
\frac12\sum_{b,r}J(b,r)\bigl(d(+\mid b,r)+d(-\mid b,r)\bigr)=\frac12,
$$

所以其风险恰为 $1/2$。即使保留完整基底的第一阶段标签 $w$，第二协议的联合概率也为 $\Pr(w,r\mid\theta)=1/4$，其中 $w\in\{000,010\}$、$r\in\{0,1\}$，仍与 $\theta$ 无关；该额外经典标签不能恢复已消去的相干项。

第一阶段的 $E,F$ 只含当前经典记录，未包含测量后的量子载体与相位敏感未来，故两个当前缺陷为零与两阶段风险不同并不冲突。将第二次实际测量结果纳入观察后，两阶段行律已有上述区别，应对这些完整记录律重新计算缺陷；若还允许选择后续反馈操作，则需给定相应的路径核或量子过程及可访问载体。单步律的模拟关系并不是经典结果与量子后态联合对象的模拟关系，也不把这里的理想仪器假设推成不可逆坍缩、观察者客观性或唯一结果的结论。证毕。

<a id="entry-567"></a>

## 追加锚（本行以下为增补区）

<a id="section-120"></a>

## 120. 量子仪器缺陷与后续决策风险

第 119 节把“保留多少历史”写成有限经典实验的缺陷与风险界。本节把同一问题提升到完整量子仪器：被丢弃的部分可以包含活动记忆、参考系和尚未读取的历史寄存器，因此只比较一次测量的边缘分布是不够的。需要比较整个过程在任意输入和任意保留参考上的可区分性。

<a id="entry-569"></a>

### 120.1 完整过程与保留过程

设参数集为有限集合 $\Theta$，先验为 $\mu$。令 $X,Y,\widetilde Y$ 为有限维算子空间；对每个 $\theta\in\Theta$，令

$$
I_\theta:X\longrightarrow Y
$$

是共同输入空间 $X$ 与共同输出空间 $Y$ 上、各参数同型的完整 $n$ 槽量子过程（固定槽接线后视为一个 CPTP 通道）。输出空间 $Y$ 包含全部仍可访问的历史寄存器与活动记忆；惰性的外部参考系统记为任意有限维 $R$，在比较时以 $I_\theta\otimes\operatorname{id}_R$ 处理。压缩后的过程为

$$
\widetilde I_\theta:X\longrightarrow \widetilde Y.
$$

压缩不是把 $Y$ 的坐标重新命名，而是实际丢弃了一部分过程输出。设 $S:\widetilde Y\to Y$ 是与 $\theta$、输入以及后续决策均无关的 CPTP 模拟器。定义过程缺陷

$$
\boxed{
\delta_\diamond(I\mid\widetilde I)
=
\inf_S\;\sup_{\theta\in\Theta}
\frac12\left\|I_\theta-S\circ\widetilde I_\theta\right\|_\diamond .
}
$$

diamond 范数的辅助系统量化了最坏情形下保留参考的影响；因此这里的缺陷不是某个选定初态上的迹距离。允许实验者选择共同输入 $\rho_{XR}$ 和读出 $D:Y\otimes R\to A$，其中 $D$ 是量子到经典的 CPTP 映射；模拟器在参考上作用为 $S\otimes\operatorname{id}_R$。若模型固定无参考输入，则取一维 $R$ 即可。

对损失函数

$$
0\le \ell(\theta,a)\le 1
$$

定义完整过程的最优 Bayes 风险

$$
R^*(I)
=
\inf_{R,\rho_{XR},D}
\sum_{\theta\in\Theta}
\mu(\theta)\,
\mathbb E_{a\sim D((I_\theta\otimes\operatorname{id}_R)(\rho_{XR}))}
[\ell(\theta,a)],
$$

并以同样方式定义 $R^*(\widetilde I)$。这里的后处理可以包含任意对输出记忆的量子控制，但模拟器 $S$ 必须在所有参数之间共用。

<a id="entry-570"></a>

### 120.2 缺陷支配后续决策风险

在上述有限参数、共同输入空间、CPTP 后处理和单位区间损失的条件下，有

$$
\boxed{
R^*(\widetilde I)
\le
R^*(I)+\delta_\diamond(I\mid\widetilde I).
}
$$

证明只使用通道范数的定义和测量的收缩性。固定任意模拟器 $S$、输入 $\rho_{XR}$ 与完整过程读出 $D$，把 $D\circ(S\otimes\operatorname{id}_R)$ 作为压缩过程上的决策。若

$$
\frac12\left\|I_\theta-S\circ\widetilde I_\theta\right\|_\diamond
\le\varepsilon
$$

对所有 $\theta$ 成立，则对该输入及任意参考系统，输出态的迹距离至多为 $\varepsilon$；再经 $D$ 后，经典总变差距离仍至多为 $\varepsilon$。单位区间损失的期望差至多为同一数值，对 $\mu$ 加权后仍至多为 $\varepsilon$。先对策略取下确界，再对 $S$ 取下确界，得到所示不等式。

若反向缺陷也有定义，则同时应用两次上界，得到

$$
\boxed{
\left|R^*(I)-R^*(\widetilde I)\right|
\le
\max\left\{
\delta_\diamond(I\mid\widetilde I),
\delta_\diamond(\widetilde I\mid I)
\right\}.
}
$$

该结论的量词顺序很重要：模拟器不能依赖于未知参数，且缺陷控制的是所有输入、所有参考和所有允许后处理。只比较某一次实验的输出概率，不能推出这个统一风险界。

<a id="entry-571"></a>

### 120.3 逐槽误差与历史保留

若完整过程由固定接线后的 $n$ 个槽组成，并且第 $k$ 槽存在与输入、记忆和参考兼容的抬升模拟误差 $\eta_k$，且各槽模拟器可以复合为同一输出空间上的全局模拟器 $S$（共同余域时可取相应的恒等填充），则第 72.1 节的望远镜不等式给出

$$
\boxed{
\delta_\diamond(I\mid\widetilde I)
\le
\min\left\{1,\sum_{k=1}^{n}\eta_k\right\}.
}
$$

与第 72.1 节相同，这要求逐槽抬升在同一复合空间上比较，并把中间记忆保留下来。若后续干预可以在各槽之间交错，完整对象应视为 comb 或 strategy；此时不能把 comb 无条件当作一个普通末态通道，而应改用相应的 strategy 范数，或先完成逐槽抬升再应用本节界。

这给出一个可操作的历史预算：在预测时域 $n$ 内，若允许总风险误差为 $\varepsilon$，则满足

$$
\sum_{k=1}^{n}\eta_k\le\varepsilon
$$

足以保证任何单位区间损失的后续决策风险增加不超过 $\varepsilon$。该预算只对所声明的过程族、参考系统和后处理有效，不是对所有未来实验的宇宙级保证。

<a id="entry-572"></a>

### 120.4 即时统计相同仍可能有后续风险

Zeckendorf 合法构型空间可取为

$$
\mathcal W_L
=
\{w\in\{0,1\}^L:w_jw_{j+1}=0\}.
$$

令 $P_w=|w\rangle\langle w|$，并按某个粗读出 $q:\mathcal W_L\to Q$ 定义两种过程。第一种是粗 Lüders 过程

$$
L_q(\rho)
=
\sum_{r\in Q}Q_r\rho Q_r,
\qquad
Q_r=\sum_{q(w)=r}P_w;
$$

第二种是先精确记录构型再忘记标签

$$
M_q(\rho)
=
\sum_{r\in Q}\sum_{q(w)=r}P_w\rho P_w.
$$

二者在当前粗标签的经典概率上相同，但保留的后态不同。若把标签写入经典寄存器，两个仪器对结果 $r$ 的概率都为 $\operatorname{Tr}(Q_r\rho)$；差异出现在条件后态及其可供后续操作访问的相干。取三位合法构型中的 $000$ 与 $010$，并令

$$
|\psi_\pm\rangle
=
\frac{|000\rangle\pm|010\rangle}{\sqrt2}.
$$

若粗读出把这两个构型归入同一类，则在过程缺陷定义中取参数集为单元素，并令完整通道为 $L_q$、压缩通道为 $M_q$；diamond 范数的上确界对输入取值，下面的两个态只是其中的测试输入：

$$
M_q(|\psi_+\rangle\langle\psi_+|)
=
M_q(|\psi_-\rangle\langle\psi_-|)
=\tau,
$$

而 $L_q$ 保留两个相反相位的纯态。两者满足

$$
D\!\left(L_q(|\psi_+\rangle\langle\psi_+|),L_q(|\psi_-\rangle\langle\psi_-|)\right)=1,
\qquad
D\!\left(M_q(|\psi_+\rangle\langle\psi_+|),M_q(|\psi_-\rangle\langle\psi_-|)\right)=0.
$$

因此对任意不依赖参数的模拟器 $S$，若其半 diamond 误差至多为 $\varepsilon$，则特别地，对两个制备输入有 $D\!\left(L_q(|\psi_\pm\rangle\langle\psi_\pm|),S\tau\right)\le\varepsilon$，三角不等式给出

$$
1
\le
D\!\left(L_q(|\psi_+\rangle\langle\psi_+|),S\tau\right)
+
D\!\left(S\tau,L_q(|\psi_-\rangle\langle\psi_-|)\right)
\le2\varepsilon,
$$

从而

$$
\boxed{
\delta_\diamond(L_q\mid M_q)\ge\frac12.
}
$$

这说明“即时经典统计完全相同”并不意味着过程缺陷为零。被遗忘的相位在后续联合操作中仍可转回可见读数；风险界必须针对完整过程，而不是单步标签分布。这里的例子把第 96 节和第 119 节的边界现象放进同一个过程缺陷框架。

<a id="entry-573"></a>

### 120.5 Zeckendorf 刻度的正确位置

Zeckendorf 编码在本节中承担的是参数与输入构型的离散组织。它决定合法窗口的索引、粗读出纤维 $q^{-1}(r)$ 以及可能被丢弃的历史分支；它不决定通道的 Hamiltonian、CPTP 结构、记录强度或 diamond 范数。

例如，三位合法构型

$$
000,\quad001,\quad010,\quad100,\quad101
$$

按权重 $3,2,1$ 读为 $0,1,2,3,4$。若只保留奇偶性，构型会被分成两个纤维；但过程缺陷仍需比较这些纤维在后态、活动记忆和参考上的可模拟程度。不能用合法构型数 $F_{L+2}$、单步 Gram 系数或一个整数标签，替代完整过程的缺陷计算。

因此，历史保留量不是一个只由编码长度决定的数字，而是相对于三项共同确定的预算：允许的过程族、可执行的后续策略和容许风险误差。改变其中任一项，最小充分记录都可能改变。

<a id="entry-574"></a>

### 120.6 研究命题与形式化边界

本节提出的可检验命题是：对于给定过程族和后续策略类，存在一个过程缺陷 $\delta$，它统一上界任何单位区间损失的 Bayes 风险增量；若缺陷按逐槽误差累积，则历史预算可由望远镜界给出。该命题是有限维 CPTP 数学推导，与仓库已有的有限 Kraus 通道、迹距离收缩、过程望远镜和投影动力学结果相容。

指定版本尚无一个直接给出“diamond 缺陷蕴含后续 Bayes 风险界”的单一 Lean 定理；本节的组合证明因此保留为普通数学推导，不能冒充新增 kernel 证明。可继续的形式化任务是：先在有限维矩阵上定义带辅助系统的过程缺陷，再分别形式化风险函数、测量收缩和下确界传递；最后把 Zeckendorf 合法窗口作为参数族接入，而不是把编码本身当作物理动力学。

由此，对“用多少约束和历史才能得到稳定经典现实”的回答获得一个强度受控的版本：在给定实验与误差预算内，只需保留使 $\delta_\diamond\le\varepsilon$ 的过程信息；若更换后续操作、允许访问旧记忆或扩大参考系统，原有预算必须重新计算。稳定性是过程相对于任务的近似闭合，而不是所有未来关系都已被证明消失。

<a id="entry-575"></a>

### 120.7 追加锚

本节新增的边界固定为：

$$
\boxed{
\text{即时读数的相同性只约束当前统计；}
\quad
\text{过程 diamond 缺陷才统一约束任意后续决策风险。}
}
$$

后续章节可以在这一锚上研究三类问题：不同记忆结构下的缺陷复合律、comb/strategy 范数的逐槽推广，以及 Zeckendorf 粗读出在给定实验族中的最小充分记录。若没有这些额外假设，不得把“记录看起来经典”升级为“整体过程已经经典”。

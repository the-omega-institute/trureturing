# NS、观察反向与 RH：第一组形式化理论

## 1. 范围与原始对象

本卷承接《Navier–Stokes、观察取反与黎曼假设的动力学桥接理论》的第一组证明目标，覆盖原稿命题 1.2、5.1、5.2，以及观察恢复判据和现有 Weil 奇偶轨道的连接。原稿 Markdown 的 SHA-256 为 `41d2da32560e1f075ac0e07f7cb59743ad1f9d6f205e0e7fadfe9fcd45d5bac4`。本卷是这些结果的源对象、证明和形式化范围说明，并非原稿全部 39 条命题的完成报告。

起始 dev 为 `4ee990c9cb7eb3c8692f0c3f6e5be53cf28f9c85`。集成快照为 `982d1a178ee9191d7c26877f1d9d4e45c1790793`，其新增 8 个提交与本组新增路径不重叠。Mathlib 固定在 `db584cd6d46c92f209a44c0f1c829460d327499d`，对应仓库现有 Lean 4.33.0 环境。

本卷区分三种命题。状态反向是否可由当前观察确定，是纤维上的恢复问题；观察能否决定自己的变化率，是动力闭包问题；整个过程能否倒放，则取决于方程的时间反演条件。以下反例发生在第二层，即使第一层已经成立，第二层仍然可以失败。

## 2. 已有定义与实际依赖

| 已有源码 | 复用的内容 | 新消费者 |
|---|---|---|
| `D5/S0/Conventions/InvolutionDecomposition.lean` | 实线性对合的标准半和、半差分解 | `VisibleNegationLifts` |
| `D5/S0/Rewriting/Quotients/AnswerabilityCriterion.lean` | 目标因子分解与观察纤维常值的等价 | `QuadraticObservationClosure` |
| `D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition.lean` | 原始谱样本的奇偶通道、重数及四点轨道能量 | `OrbitReversalObservation` |

`InvolutionDecompositionUniqueness` 已有半和、半差的唯一性结论，本组没有重证该定理。`CanonicalLiLocalExpansion` 所属 PR #6172 已合并；其实际 canonical Li 序列应由后续 Li 路线复用，本组不另外定义 Li 系数，也不把未合并的概率半群分支当成 dev 依赖。

代码与 PR 检索还检查了 Navier、Leray、FourierPolynomial、反射及二次投影相关名称。没有在所查范围内发现本组具体流体模式消费者。检索未命中不构成整个数学文献或整个 Lean 生态的优先权证明。

## 3. 所有可见负号的隐藏提升

设实线性观察为 \(P:E\to F\)，状态操作为实线性 \(R:E\to E\)。本组证明

\[
\boxed{
R^2=I\ \land\ PR=-P
\quad\Longleftrightarrow\quad
\exists H,\ H^2=H,\ PH=0,\ R=2H-I.
}
\]

右侧的 \(H\) 由完整 \(R\) 唯一确定：

\[
H=\tfrac12(I+R).
\]

**证明。** 取标准对合分解的固定部分 \(H\)。已有定理给出 \(RH=H\)，于是 \(H^2=H\)。观察线性且 \(PR=-P\)，故 \(PH=(P+PR)/2=0\)。反向展开 \((2H-I)^2=4H^2-4H+I=I\)，并由 \(PH=0\) 得到 \(PR=-P\)。唯一性通过 \(R=2H-I\) 解出 \(H\)。

这个结论对任意实模成立，不要求有限维、正交性或内积保持。同一个可见负号允许不同的隐藏固定子空间。要讨论可实现的物理反射，需要另加几何和动力条件。

若 \(P:E\to E\) 本身幂等，则

\[
R_{\rm vis}=I-2P
\]

是一个具体对合，满足 \(PR_{\rm vis}=-P\)，并固定 \(\ker P\) 中的每个向量。它与整体取负 \(-I\) 在可见层相同，在隐藏层不同。

形式化主声明：`visible_negation_iff_hidden_idempotent`。唯一性和可见反射的性质分别由 `hidden_idempotent_unique`、`visibleReflection_spec` 承载。

## 4. 二次动力闭包的完整判据

设 \(P:E\to E\) 为实线性幂等投影，\(L:E\to E\) 线性，\(B:E\times E\to E\) 双线性，不要求对称。定义

\[
V(x)=Lx-B(x,x).
\]

观察闭包意味着存在一个可为非线性的函数 \(f:E\to E\)，使

\[
PV(x)=f(Px)\qquad\text{对所有 }x\text{ 成立}.
\]

本组证明，该条件当且仅当下列三项同时成立：

\[
\begin{aligned}
Pb=0&\Longrightarrow PLb=0,\\
Pb=0&\Longrightarrow PB(b,b)=0,\\
Pa=a,\ Pb=0&\Longrightarrow P\bigl(B(a,b)+B(b,a)\bigr)=0.
\end{aligned}
\tag{4.1}
\]

这是原稿动力纤维判据在二次向量场上的具体加强：它把整条闭包条件化为线性项、隐藏自作用和混合作用的实际系数条件。

**必要性。** 在零观察纤维中分别使用 \(b\) 与 \(-b\)，得到

\[
PLb-PB(b,b)=0,\qquad -PLb-PB(b,b)=0.
\]

相加并除以二得 \(PB(b,b)=0\)，再得 \(PLb=0\)。对同一纤维中的 \(a\) 与 \(a+b\) 比较，双线性展开留下第三项。

**充分性。** 对任意 \(x\) 令 \(a=Px\)、\(b=x-Px\)。由幂等性有 \(Pa=a\)、\(Pb=0\)。展开

\[
PV(a+b)-PV(a)=PLb-P(B(a,b)+B(b,a))-PB(b,b),
\]

三项均为零。取 \(f(y)=PV(y)\) 即得闭包。

`quadratic_closure_iff` 承载两个方向的证明。`quadratic_fiber_criterion` 通过已有 `answerability_criterion` 将它接到观察纤维语言。它没有要求闭包函数线性，也没有把某个已知闭包放进前提。

## 5. 两种反向的加速度差

当 \(Pb=0\) 时，整体反向与只反向可见部分给出

\[
P(-a-b)=P(-a+b)=-Pa.
\]

若此外 \(PLb=0\)，则双线性展开给出

\[
\boxed{
PV(-a-b)-PV(-a+b)
=-2P\bigl(B(a,b)+B(b,a)\bigr).
}
\tag{5.1}
\]

这个公式由 `reversal_acceleration_gap` 承载。保留全部交叉项是关键。状态读数的同一性不会消去这些项。Fang、Bos、Shao 和 Bertoglio 对湍流全尺度及部分尺度反转的研究提供直接物理背景。[1]

该通用代数源与下面具体 Fourier 源分别给出证明。后者没有通过伪造一个完整 PDE 实例来调用前者；当前实际 import 边见第 9 节。

## 6. 一个从输入系数计算的 Fourier 见证

考虑两个连续实参数 \(\alpha,\beta\) 的周期速度族

\[
u_{\alpha,\beta}(x,y,z)=
\bigl(\beta\cos(y-x),\ \alpha\cos x+\beta\cos(y-x),\ 0\bigr).
\]

其四个输入频率为

\[
(1,0),\ (-1,0),\ (-1,1),\ (1,-1),
\]

均以第三频率为零嵌入三维。每对相反频率各取一半实余弦振幅。实际系数由有限求和定义，同频率重复项也按求和语义处理。

`lowObservation` 保留全部 \(|k|^2\le1\) 的整数频率及三个速度分量。于是

\[
\operatorname{lowObservation}(\alpha,\beta)
=\operatorname{lowObservation}(\alpha,\beta')
\]

对所有 \(\alpha,\beta,\beta'\) 成立；隐藏参数 \(\beta\) 不由这一观察确定。

定义双线性对流的实际 Fourier 系数

\[
\widehat{(u\cdot\nabla)u}(k)
=i\sum_{p+q=k}(q\cdot\widehat u(p))\widehat u(q).
\]

源码计算全部 16 对输入相互作用，并对每个整数输出频率定义系数，没有丢弃新生成的低频。压力消去使用实际乘子

\[
\mathbb P_\sigma(k)=I-\frac{kk^T}{|k|^2},
\]

零频率取恒等。随后定义

\[
\widehat V_\nu(k)=-\nu|k|^2\widehat u(k)
-\mathbb P_\sigma(k)\widehat{(u\cdot\nabla)u}(k).
\]

对全部实数 \(\nu,\alpha,\beta\)，源码推出

\[
\boxed{\widehat V_\nu(0,1)_1=-\frac{i\alpha\beta}{4}.}
\tag{6.1}
\]

以 \((\alpha,\beta)=(-1,-1)\) 和 \((-1,1)\) 比较，整个低频状态相同，式 (6.1) 的目标系数相差 \(-i/2\)。任何只依赖该低频状态的确定性复数预测器，至少在其中一个输入上有不小于 \(1/4\) 的误差。三角不等式给出这个下界，无需假定预测器连续、线性或来自某个学习模型。

`no_low_mode_acceleration_closure` 进一步排除在整个双参数族上精确恢复这个系数的单值函数。因此它排除了更强的完整低频加速度闭包，但不讨论通过记忆或额外观察进行恢复的可能性。

**归一化。** \(1/4\) 是一个复 Fourier 系数的绝对误差下界。原稿的 \(1/(2\sqrt2)\) 是归一化连续 \(L^2\) 范数中的场误差；本组没有通过 Parseval 形式化两种量的换算，也不将两者混写。

## 7. 输入数据到真实光滑场的识别

`ReversalWaveSynthesis` 用同一组系数乘以

\[
\chi_k(x,y)=\cos(k_1x+k_2y)+i\sin(k_1x+k_2y)
\]

作有限合成，证明结果逐分量等于上述实余弦速度场。随后证明两变量的联合 \(C^\infty\) 光滑性、各坐标的 \(2\pi\) 周期性，以及普通坐标导数下的零散度：

\[
\partial_xu_1+\partial_yu_2
=\beta\sin(y-x)-\beta\sin(y-x)=0.
\]

所有输入频率的振幅也分别满足 \(k\cdot\widehat u(k)=0\)。这两种证明分别检查系数和真实场。

本组仍未构造完整 Sobolev 空间上的 Leray 算子，也没有证明上述系数加速度与任意已有 Fréchet-PDE 实现逐项相等。周期真实场、精确 Fourier 非线性和低频分离已经在各自源码中给出；无限维定义域、一般解存在性、轨迹误差传播和爆破不属于本组声明。

## 8. 接到现有 RH 奇偶轨道

对谱样本对 \(v=(A,B)\)，令 \(R(A,B)=(B,A)\)，观察取为原库的奇通道

\[
O(A,B)=\frac{A-B}{2}.
\]

则 \(OR=-O\)，而标准固定部分为

\[
H(A,B)=\left(\frac{A+B}{2},\frac{A+B}{2}\right),\qquad OH=0.
\]

`OrbitReversalObservation` 直接复用 `evenSpectralChannel`、`oddSpectralChannel` 的原始定义。它用通用提升性质证明 \(H^2=H\) 及 \(OH=0\)，并在实际 `ZeroData`、`WeilTestFunction`、谱参数和重数上调用已有四点轨道定理，得到

\[
Q_{\rm orbit}(g)=4m\,|H(A,B)_1|^2-4m\,|O(A,B)|^2.
\]

这一模块是明确的对象识别与定理绑定。它不重证已有奇偶分解，也不宣称这条等式是新发现。交换谱样本没有被等同为测试函数空间反射或物理时间反演。

实际 RH 问题还需要由固定的素数项、Gamma 项和可实现测试函数控制奇通道。任意 \((A,B)\) 是否来自同一个测试函数，不能省略；加上奇能量修正后的正性，也不等于原始 Weil 二次型的正性。本组没有解除这些算术条件。

## 9. 新源码与依赖图

| 新 Lean 模块 | 公开定义/缩写 | 公开定理 | 主要内容 |
|---|---:|---:|---|
| `Observer/Reversal/VisibleNegationLifts` | 2 | 5 | 隐藏幂等提升的完整分类 |
| `Observer/Reversal/QuadraticObservationClosure` | 1 | 5 | 二次动力闭包充要条件和反向差 |
| `FluidDynamics/Fourier/LowModeReversalWitness` | 10 | 7 | 实际系数卷积、压力乘子、无闭包见证 |
| `FluidDynamics/Fourier/ReversalWaveSynthesis` | 3 | 4 | 同一系数的真实场合成、光滑、周期、零散度 |
| `Weil/HolonomyBridge/OrbitReversalObservation` | 2 | 3 | 原有 Weil 奇偶轨道的反向观察识别 |

合计 18 个公开定义/缩写、24 个公开定理。每个公开声明对应一个 Scribe `StatementSource.FromLean()` 句柄，并有 `#print axioms` 指令。指令存在不代表它已经执行。

```text
InvolutionDecomposition -> VisibleNegationLifts -> OrbitReversalObservation
OffLineOrbitParityDecomposition ---------------> OrbitReversalObservation
AnswerabilityCriterion -> QuadraticObservationClosure
Mathlib Fourier coefficient arithmetic -> LowModeReversalWitness
LowModeReversalWitness -> ReversalWaveSynthesis
```

通用二次闭包公式与具体 Fourier 见证间当前是已显示的数学对应，不伪造为 Lean import 边。后续统一的有限 Fourier 双线性 API 可以把两者接为实例化定理。

## 10. 检查范围与后续证明目标

本组完成数学推导的自审和精确符号交叉核对。独立的 Laurent 多项式实现按空间导数构造对流，与源码的 16 对卷积产生的 9 个输出模式作 27 项分量比较；另有 100 组精确有理参数回归、真实余弦场合成检查、隐藏二次系数检查和既有 Weil 能量恒等式检查。这是同一作者的第二种实现，不冒充独立作者审稿。

当前作者环境无 Lean、Lake 或 .NET。没有执行新的 elaboration、Lean 内核检查、公理闭包收集或 Scribe 发射。源码是经过逻辑检查的候选证明；词法上无新增 axiom、sorry、admit、native_decide，不足以替代编译及传递依赖检查。

下一项直接消费者是统一有限 Fourier 系数与实际空间微分的算子级识别，再把系数见证作为通用二次闭包定理的实例。之后才能严格接入局部解、记忆核和相应预测误差。原稿的 Schur–记忆积分、隐藏耗散、Gamma 尾项认证、canonical Li 增长到 RH、热变形零点运动等目标仍各有独立证明义务，未由本组完成。

已有 RH 理论继续由 `RH_RESEARCH_LANE_THEORY.md` 承载。本卷只增加此前尚无专门源卷的 NS 观察动力主题，后续本主题增量在这里累积。

## 来源

[1] L. Fang, W. J. T. Bos, L. Shao, J.-P. Bertoglio. *Time-reversibility of Navier–Stokes turbulence and its implication for subgrid scale models*. arXiv:1112.0659, 2011; Journal of Turbulence, 2012. https://arxiv.org/abs/1112.0659 。用于全尺度与部分尺度反转的研究背景；本组的具体双参数系数恒等式由显示的四个模式重新推导。

[2] Y. T. Lin, Y. Tian, M. Anghel, D. Livescu. *Data-driven learning for the Mori–Zwanzig formalism: a generalization of the Koopman learning framework*. arXiv:2101.05873, 2021. https://arxiv.org/abs/2101.05873 。用于说明缺乏状态闭包时保留记忆的后续方向，本组未调用其分析定理。

[3] The Omega Institute. `D5/S0/Conventions/InvolutionDecomposition.lean`, `involution_even_odd_decomposition`；`D5/S0/Rewriting/Quotients/AnswerabilityCriterion.lean`, `answerability_criterion`。原始读取提交为 `4ee990c9cb7eb3c8692f0c3f6e5be53cf28f9c85`，在上述集成提交中未修改。

[4] The Omega Institute. `D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition.lean`, `off_line_orbit_parity_decomposition`。读取 blob `299a01acdde3e62892738ff790779729715e8938`。新桥保留该定理全部离线、非自共轭和重数条件。

[5] The Omega Institute. PR #6172, `CanonicalLiLocalExpansion`。本轮读取为已合并状态，列作后续 Li 路线的已有源对象，不是本组直接依赖。

## 11. OpenAI 完整 NS 形式化的源核对与稳定性接入

### 11.1 原始结果和当前接入范围

2026-09-08，OpenAI 发布 Navier–Stokes 论文与完整 Lean 项目 `openai/NavierStokesAndEuler`。[6] 本轮读取的 main 为 `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`，更新日期为 2026-09-10。其 `NavierStokes/ComparatorSolution.lean` 给出两项实际终端声明：对每个正黏性 nu，存在满足相应条件的光滑初值和外力，使 R³ 或周期 R³/Z³ 上所规定的全局光滑解不存在；全空间分支的解要求还含统一能量界。[7] 这是官方表述的 C、D 分支。外力变量及其条件属于原定理，不得删除；单独的无外力 Euler 项目也不能替代 NS 的量词。

本轮核对了公开声明及相关证明模块，没有在当前环境重新构建完整上游工程，也没有宣称完成独立专家审查或奖项认证。完整上游项目存在，与本库是否已有全部依赖闭包，是不同事实。本库现役 `Cone/ConePositivity.lean` 已注明从上游 `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` 移植 `ConeAlgebra.lean`；它给出应力锥与二阶矩阵正定性的等价，没有给出任意 NS 流的全局吸引性。

本库固定 Lean 4.33.0，上游固定 Lean 4.34.0-rc2。本轮保持既有 toolchain 和 mathlib revision 不变，选择有真实消费者的证明切片作署名移植。没有添加无法解析的外部 import，也没有把上游终端结论重述成 axiom。

### 11.2 实际源模块的不同用途

| 上游真源 | 核读的结论 | 本轮用途 |
|---|---|---|
| `NavierStokes/ComparatorSolution.lean` | 带规定外力的 C、D 终端结果 | 核对范围，不移植为稳定性假设 |
| `NavierStokes/R3/H3Energy.lean` | 实际 L² 曲线求导、弱导数分部积分、两解之差的能量增长界和唯一性 | 保留真正 PDE 接入目标，尚未移植其全部 H³ 依赖 |
| `NavierStokes/R3/ComparisonGronwall.lean` | 闭区间连续、内点可导下的误差界和空间截断耗尽 | 核对端点条件与正增长估计的边界 |
| `NavierStokes/ViscousPropagator.lean` | 实 Hilbert 空间上，从实际右侧微分方程推导带强迫的范数界 | 三个私有证明切片已移植，并被新公开结论直接调用 |

H³ 比较证明给出 E'≤2GE 一类上界，其中 G 非负。它用于初始差为零时的唯一性；不能通过更换解释，把正增长上界写成指数吸引。本轮使用 `ViscousPropagator` 的真正加权范数论证，并额外要求实际算子具有严格负的二次型界。

三段移植的上游原名为 `hasDerivWithinAt_norm_of_ne_zero`、`norm_le_initial_add_integral`、`weighted_norm_le_initial_add_integral`。[8] 本地仅调整 namespace、私有可见性、辅助名称与所需 Mathlib imports；保留闭区间连续性、右导数与正权重条件。源代码保留 OpenAI 仓库、确切提交、文件路径及 Apache-2.0 归属。它们位于同一个具有后续实质结论的模块中，没有另建无人调用的包装库。

### 11.3 来自真实方程的指数误差管

新增 `D5/S3/FluidDynamics/Stability/OpenAIViscousAttraction.lean`，配套同名 Scribe。设 H 为实内积空间，实际轨迹满足

\[
w'(t)=A(t)w(t)+r(t),\qquad
\langle z,A(t)z\rangle\leq-\gamma\|z\|^2,\quad\gamma>0,
\qquad\|r(t)\|\leq\rho.
\]

在所声明的闭时间区间内，证明

\[
\boxed{\|w(t)\|\leq e^{-\gamma t}\|w(0)\|
 +\frac{\rho}{\gamma}(1-e^{-\gamma t}).}
\tag{11.1}
\]

具体证明调用上游移植的加权范数定理，取 W(t)=exp(-gamma*t)。积分项由 rho*exp(gamma*t) 控制，再用显式原函数 (rho/gamma)*exp(gamma*t) 与微积分基本定理求出。初始误差、实际时间、负增长率及持续扰动均未被隐藏。轨迹过零的情形由上游右导数比较处理，没有除以零范数。

公开声明是 `norm_le_exponential_tube`、`unforced_norm_contraction`、`scalar_equilibrium_tube`。最后一项将实际标量轨迹 a(t) 平移到误差 a(t)-c，适用于 a'=-gamma*(a-c)+r。持续误差允许的极限范围是 rho/gamma；rho=0 时得到指数衰减。全时间收敛仍要求轨迹全局存在，且同一个 gamma 在全部时间有效；有限区间估计自身不证明全局存在。

该一般模块的 A(t) 是有界连续线性算子。全空间 L² 上的 Stokes 算子通常无界，不能直接塞进这一类型。有限 Galerkin 系统、标量不变族可以直接消费本定理；一般 PDE 需要保留算子定义域及能量形式，或证明一致逼近后才能过渡。低维观察的趋零也不能替代这里实际状态范数的趋零。

### 11.4 实际受迫 NS 不动点的消费者

新增 `D5/S3/FluidDynamics/Stability/ForcedShearFixedPoint.lean` 及同名 Scribe，直接复用同一 PR 的 `ToralIsogenyShearNS` 中真实波形、普通导数与完整 NS 残差。固定空间周期 2pi，令

\[
\Phi_k(x,y)=(1,k)\cos(-2kx+2y),\qquad
\Gamma_k=4\nu(k^2+1),\qquad u_a(t,x,y)=a(t)\Phi_k(x,y).
\]

普通求导证明 div(u_a)=0，且零压力 NS 残差为

\[
\partial_tu_a+(u_a\cdot\nabla)u_a-\nu\Delta u_a
 =(a'+\Gamma_k a)\Phi_k.
\tag{11.2}
\]

非线性对流的两个分量完整保留，随后由速度方向 (1,k) 与波矢 (-2k,2) 的配对为零而消去。没有从一张预设乘子表假定 PDE 成立。

固定 c 后，真实场 u_*=c Phi_k 满足时间不变外力 f_*=Gamma_k*c*Phi_k 的 NS 方程。该不动点通过实际导数证明构造出来。若外力再加 r(t)Phi_k，实际幅度方程就是 a'=-Gamma_k*(a-c)+r。nu>0 推出 Gamma_k>0，因而可以直接调用式 (11.1)。结合每个实际分量的 |Phi_k,i|≤1+k，得到对所有 x,y 和两个分量同时成立的界

\[
|u_{a,i}(t,x,y)-u_{*,i}(x,y)|\leq
(1+k)\left[e^{-\Gamma_k t}|a(0)-c|
 +\frac{\rho}{\Gamma_k}(1-e^{-\Gamma_k t})\right].
\tag{11.3}
\]

`amplitude_readout` 还证明 a(t)=u_a(t,0,0)_0，因此幅度确为原速度场上的读数。关键声明是 `field_equation`、`stationary_forced_solution`、`forced_shear_attraction`。空间界采用分量绝对值，没有擅自改写成连续 L² 范数。

无扰动时，显式幅度 a(t)=c+(a(0)-c)exp(-Gamma_k*t) 给出全局趋近该不动点的普通解公式。本轮源码的主要认证结论是上述实际方程和有限区间误差界，没有额外声称已完成任意受迫 PDE 的解构造。稳定性范围为同一剪切不变族，任意非共线或三维扰动均未纳入。这里的时间不变外力也不等同于 C、D 分支中有指定时间衰减条件的外力；两类问题不能交换假设。

### 11.5 一般稳定不动点需要补齐的分析链

对同一固定外力下的候选稳态 u_*，设 w=u-u_*。在光滑周期、散度为零且压力正交等条件下，目标是从实际方程获得

\[
\frac12\frac{d}{dt}\|w\|_{L^2}^2+\nu\|\nabla w\|_{L^2}^2
 =-\int w\cdot((w\cdot\nabla)u_*)+\int w\cdot r.
\tag{11.4}
\]

这与已核读的上游 H³ 比较证明使用同一类分部积分和压力处理，但必须保留黏性耗散项。若实际零均值子空间满足 Poincare 下界 D≥lambda_1 E，且已验证的稳态伸长界为 G，则

\[
\gamma=\nu\lambda_1-G>0
\]

才是吸引证书的负增长裕量。可用完整梯度算子范数作 G 的充分上界，也可进一步证明对称梯度的更精确控制。零均值或固定均值条件不可省略，R³ 上也不能自动使用周期域的正谱隙。式 (11.4)、Poincare 接入与这些充分条件是下一轮待证明目标，本轮未将它们包装成已经完成的 PDE 结论。

实际路线因此是：复用上游弱导数和能量空间；为我们的同一速度场建立空间对象对应；保留耗散、压力和非线性项；验证稳态方程与正裕量；最后将估计传到真实观察或记忆核。若目标通过有限 Fourier 数据给出，还需认证未解析高频尾项与残差，而非假设截断解就是 PDE 稳态。

OpenAI 的终端爆破结果说明，不能期望对所有允许外力和初值存在无条件的全局吸引固定点。可研究的目标应明确固定方程、外力、状态空间、对称性及吸引域。数学表示中的不动点、速度场演化的稳态、以及空间环面作用的固定点，是需要以实际映射连接的不同对象。

### 11.6 当前证据和文献归属

本次交付为普通数学证明、署名源码移植、直接消费者及配套 Scribe。当前环境没有 Lean、Lake 或 .NET；没有新增内核认证、C# 编译、独立评审或完整上游重建。`#print axioms` 指令仅供后续执行。实际诊断包括 9 项符号恒等式和 1617 项精确整数幅度/强迫关系；另有源码占位扫描、Scribe 词法括号检查和本地/远端 Git blob 对照。有限诊断不替代全称证明的内核检查，临时诊断文件未提交。

本轮没有宣称新的外部开放问题解答。指数输入误差界和剪切解属于经典机制；新增价值是让上游实际证明成为本库实际状态和 NS 场的可复用依赖，并明确通往一般不动点稳定证书所缺的分析定理。

[6] OpenAI. *On the Navier–Stokes Millennium Prize Problem*. 2026-09-08，页面更新至 2026-09-10。https://openai.com/index/navier-stokes-solution/ 。用于核对发布、范围与源码入口，不代表本轮完成独立证明审查。

[7] OpenAI. `NavierStokes/ComparatorSolution.lean`，提交 `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`。https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ComparatorSolution.lean 。两项终端陈述及实际外力量词。

[8] OpenAI. `NavierStokes/ViscousPropagator.lean`，同一提交，Apache-2.0。https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ViscousPropagator.lean 。本轮移植的三项 Hilbert 范数证明来源；没有添加虚构的单个作者署名。

[9] OpenAI. `NavierStokes/R3/H3Energy.lean` 与 `NavierStokes/R3/ComparisonGronwall.lean`，同一提交。https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3Energy.lean ；https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/ComparisonGronwall.lean 。实际弱导数、能量比较和截断耗尽的后续依赖；本轮尚未移植其完整分析闭包。

## 12. Mathlib 独立重证：耗散、稳态残差与记忆恢复

### 12.1 当前证明来源及历史更正

第 11 节记录 `e9ccb7a1` 阶段的源调查与移植方案。该阶段已由本节替代：PR 中的 `OpenAIViscousAttraction.lean` 及同名 Scribe 已删除；三段外部移植证明全部移出当前候选树。新 `DissipativeAttraction.lean` 采用独立的正则化能量证明，直接 import mathlib。`ForcedShearFixedPoint` 的实际场与方程不变，已改用新证明。第 11 节的旧文件名及“已移植”语句只描述历史状态。

当前外部形式化依赖只有仓库固定的 mathlib。本节复用本库自有数学对象，外部论文用于比较研究问题和限定新颖性，不作为证明前提。本次没有修改 toolchain、CI 或其他贡献者的既有 Cone 文件；该 Cone 文件不在本节新证明的依赖链中。这里没有声称重写了整个仓库或完整三维 NS 证明。

本节给出完整普通数学论证及候选 Lean 脚本。环境中未发现 Lean、Lake、dotnet，未执行内核、C# 编译或独立作者审稿。因此“源码中有证明”与“本轮已通过内核”仍分开记载。已推送的原始移植历史保留在 Git 历史中，来源记录没有被重新署名为独立成果。

### 12.2 独立的正则化能量比较

设实内积空间中的实际轨迹 u 在 [0,T] 连续，在 [0,T) 有强右导数 du，且 gamma>0、rho>=0 满足

$$\langle u(t),du(t)\rangle\leq-\gamma\|u(t)\|^2+\rho\|u(t)\|.$$

对任意 delta>0 定义 z_delta(t)=sqrt(||u(t)||²+delta²)。平方根的被开方数严格为正，所以普通链式求导合法，包括 u(t)=0 的时刻。记 n=||u(t)||、z=z_delta(t)，则 z>=n、z>=delta，且

$$z_\delta'(t)=\frac{\langle u(t),du(t)\rangle}{z_\delta(t)}
\leq-\gamma z_\delta(t)+\rho+\gamma\delta.$$

关键代数差可精确展开为

$$(-\gamma z+\rho+\gamma\delta)z-(-\gamma n^2+\rho n)
=\rho(z-n)+\gamma\delta(z-\delta)-\gamma(z^2-n^2-\delta^2).$$

最后一项为零，前两项非负。在负增长系数 -gamma 下调用 mathlib 的标量 Gronwall 定理，随后利用 delta 处的连续性令 delta 从正侧趋于零，得到式 (11.1) 的相同精确上界。完整证明不使用第 11 节的三个外部辅助引理，也不需要在零范数处定义范数导数。

新主声明 `norm_tube_of_energy` 直接接受真实轨迹的能量不等式；它不要求存在定义在整个 H 上的有界生成算子。因此，在线性有界方程之外，满足同样强导数条件的非线性轨迹或无界生成元定义域内的强解也可使用。弱解是否满足这些强导数条件仍须独立证明。`norm_le_exponential_tube`、`unforced_norm_contraction` 和 `scalar_equilibrium_tube` 是该新证明的直接消费者，原剪切稳态界保留。

### 12.3 同一正裕量控制动态吸引和静态残差

新增 `QuadraticEquilibriumCertificate.lean`。定义真实二次向量场 F(x)=Lx-B(x,x)+f，其中 L 线性、B 双线性，且

$$\langle b,B(a,b)\rangle=0\qquad\text{对全部 }a,b.$$

完整展开而不要求 B 对称，得到

$$\langle w,F(v+w)-F(v)\rangle
=\langle w,Lw\rangle-\langle w,B(w,v)\rangle.$$

参考流输运项 B(v,w) 与扰动自作用 B(w,w) 的能量配对分别消失。若实际估计为

$$\langle w,Lw\rangle\leq-\mu\|w\|^2,\qquad
-\langle w,B(w,v)\rangle\leq G\|w\|^2,$$

则 gamma=mu-G>0 给出严格负能量裕量。对于已验证 F(v)=0 的同一稳态，有两项结论：

$$\|u(t)-v\|\leq e^{-\gamma t}\|u(0)-v\|
 +\frac{\rho}{\gamma}(1-e^{-\gamma t})\quad(u'=F(u)+r,\ \|r\|\leq\rho),$$

$$\boxed{\|x-v\|\leq\frac{\|F(x)\|}{\gamma}.}$$

第二项来自 -<x-v,F(x)> 的耗散下界与 Cauchy-Schwarz 上界，再约去非零误差范数；x=v 的情形单独处理。它还推出该模型内稳态的唯一性。小残差只在已经存在并通过所列条件验证的 v 周围给出距离认证，本轮没有从小残差推断未知稳态存在。

主要声明：`difference_energy_identity`、`shifted_energy_bound`、`residual_controls_state`、`equilibrium_unique`、`nonlinear_equilibrium_tube`。这里是由实际双线性条件得到的通用代数/轨迹定理。应用到连续 NS 时，零均值、压力正交、Poincare 谱隙、函数空间和导数定义域仍需在真实对象上证明；不能把这些条件贴到任意低维模型后声称已认证 PDE。对有限 Fourier 候选，需要控制完整残差及未解析尾项，单独的投影残差可能漏掉隐藏方向。

### 12.4 稳定耗散与可恢复性是两组不同的条件

新增 `ObserverMemory/Dynamics/DampedExchangeMemory.lean`。本节使用一个实际可解的二状态系统作共同对象：

$$x'=-a x+b y,\qquad y'=-b x-d y.$$

其中 x 为可见状态，y 为隐藏状态，b 为实耦合常数。实际欧氏平方能量 E=x²+y² 满足

$$E'=-2ax^2-2dy^2.$$

只要 a,d>=gamma>0，就有 E(t)<=E(0)exp(-2gamma*t)，对任意 b 成立。`state_energy_decay` 直接对实际坐标求导并调用 mathlib 标量比较，没有把谱稳定当成输入。

同一系统的真实状态和变化率给出

$$y=\frac{x'+a x}{b}\quad(b\ne0).$$

若读数误差分别为 epsilon_x 和 epsilon_v，实际重建满足

$$|\widehat y-y|\leq\frac{\epsilon_v+|a|\epsilon_x}{|b|}.$$

因此，固定正 a,d 并令 b 趋近零，可以保持同一个状态能量衰减率，而上述瞬时重建的条件数恶化。b=0 时 y 无法通过 x 及其变化率识别，但在 d>0 下隐藏状态自身仍会衰减。这是稳定性、可观测性与可检测性之间的具体区分，不把一个损失信息的观察趋零等同于全状态恢复。

主要声明：`exchange_energy_identity`、`state_energy_decay`、`exact_jet_recovery`、`noisy_jet_recovery`。此线性对象没有被宣称为原非线性 NS 的某个已识别截断。原环面矩阵参数 k、模 2 检测障碍与这里的实耦合 b 也没有被人为等同。

### 12.5 同一个系统产生精确记忆方程与有限历史误差界

对同一隐藏 ODE 乘以 exp(dt) 并实际求导，得到

$$\frac{d}{dt}(e^{dt}y(t))=-b e^{dt}x(t).$$

微积分基本定理给出

$$y(t)=e^{-dt}\left(y(0)-b\int_0^t e^{ds}x(s)\,ds\right).$$

代回实际 x 导数，得到精确 Volterra 方程

$$x'(t)=-a x(t)+b e^{-dt}y(0)+\int_0^t K(t-s)x(s)\,ds,$$

$$\boxed{K(\tau)=-b^2e^{-d\tau}.}$$

`memoryTerm_factored` 先在实际积分内验证指数因式分解；`hidden_history_formula` 从原 y 方程证明历史表达式；`resolved_memory_equation` 才将其接回原 x 方程。隐藏初值项没有删除。该负号来自当前反对称交换结构，不能推广为任意非线性 Mori-Zwanzig 核的符号规律。

对于相同的给定可见输入 x，两个不同初始化的隐藏解 y,z 有

$$|b(y(t)-z(t))|\leq |b|e^{-dt}|y(0)-z(0)|.$$

这是 `hidden_restart_error`。将时间原点移到历史窗口左端，即得到同输入下重启隐藏记忆的定量误差。一个具体初始化上界 Y 与可容忍反馈误差 eta，在 |b|Y>eta 时给出普通数学的充分窗口长度 tau>=log(|b|Y/eta)/d。该对数重排尚未另写 Lean。完整闭环截断后，可见轨迹也会改变，所以还需要把输入变化反馈纳入误差方程，不能直接把同输入重启界宣称为全部降阶轨迹误差。

在静态层面，原 y 方程等于零意味着 y=-bx/d，原 x 右端随即变成 -(a+b²/d)x。`stationary_hidden_elimination` 因而把稳态 Schur 修正、记忆与瞬时恢复接到同一实际系统。这里没有将无限区间的核积分当作已形式化对象。

### 12.6 下一项研究：保持耗散的更小记忆实现

当前具体模型提示下一项应先证明有限维块系统

$$\dot x=-Ax+B^*y,\qquad \dot y=-Bx-Dy,$$

在 A,D 的对称部分有正下界时，真实总能量的交叉项完全消去；消去 y 后的实际核为 -B^*exp(-Dt)B。这一有限维矩阵指数与积分的证明应从 mathlib 自行构建，并保留隐藏初值项。核的负号、对称性和度量一起决定稳定结构，不能通过只拟合少量轨迹来替代。

在进一步要求 D 自伴时，可研究由 D^j Bx 生成的实际 Krylov 子空间。要证明缩减隐藏空间后核完全不变、耗散下界保留，并明确给定观察能否恢复这个缩减对象。该路线与本库 Gramian、Hankel 和最小预测商的研究相接。最小状态维数、稳定裕量和观测条件数需要分别给出；不能只按衰减快慢删除状态，或只按当前观察是否可见来删除状态。

再往实际 NS 推进，应固定真实正交 Fourier 投影，证明其双线性能量消去和完整残差界；随后处理非共线扰动、压力项与高频尾项。连续极限还要求统一估计及原对象识别。本节未完成这些 PDE 接口，也未给出新的学界开放问题解答。后续新价值应落在具体 NS 子空间中保持同一目标核和负耗散裕量的有效最小化，以及有限时间、有限精度下的恢复误差，而非重列已知线性消元结论。

### 12.7 文献、独立实现与本轮核验

本轮以 pinned mathlib 的 `Analysis/ODE/Gronwall.lean`、`Analysis/InnerProductSpace/Calculus.lean`、`MeasureTheory/Integral/IntervalIntegral/FundThmCalculus` 为外部形式化基础。源码检索未发现上述新端点的重复 owner；该检索范围不构成数学优先权证明。新增 Lean 均有同名 Scribe，配套说明原假设和真实消费者。

外部数学背景与新颖性边界：Zhu-Dominy-Venturi 已研究短记忆与有限记忆近似的误差和收敛条件 [10]；Gouasmi-Parish-Duraisamy 明确区分可精确求出的线性核与非线性正交动力学近似 [11]；Zhu-Venturi 对特定随机系统的有效 Mori-Zwanzig 核给出指数收敛分析 [12]。这些文献说明记忆误差与稳定性已有成熟研究，本节具体线性结果不计为新开放问题解决。这里只核读了原始摘要和版本信息，没有声称逐页审阅这些论文或复现其全部结论。

[10] Yuanran Zhu, Jason M. Dominy, Daniele Venturi. *On the estimation of the Mori-Zwanzig memory integral*. arXiv:1708.02235v3, 2018-05-15. https://arxiv.org/abs/1708.02235 。用于限定已有短记忆误差与收敛结果的范围；无外部 Lean 依赖。

[11] Ayoub Gouasmi, Eric Parish, Karthik Duraisamy. *A Priori Estimation Of Memory Effects In Coarse-Grained Nonlinear Systems Using The Mori-Zwanzig Formalism*. arXiv:1611.06277v2, 2017-05-09. https://arxiv.org/abs/1611.06277 。本文实际线性消元不含其非线性近似假设。

[12] Yuanran Zhu, Daniele Venturi. *Hypoellipticity and the Mori-Zwanzig formulation of stochastic differential equations*. arXiv:2001.04565v3, 2021-08-29. https://arxiv.org/abs/2001.04565 。其随机/次椭圆假设没有被删去或替换成本节的确定性二维条件。

实际执行的本轮诊断为 11 项符号恒等式与 180 组精确有理参数/状态检查。它们检查正则化差、非线性差能量、交换消去、一个解析输入的隐藏 ODE、记忆回代、噪声恢复及稳态消元。检查脚本仅保存在工作容器，未提交工程文件。没有执行 Lean 编译，因而本节所有新增源码仍需本地内核核验；不能把有限诊断计作形式化全称定理的机器证明。

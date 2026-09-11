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

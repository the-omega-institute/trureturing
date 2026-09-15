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

## 11. 耗散误差管与受迫剪切不动点

### 11.3 实 Hilbert 空间中的指数误差管

**假设。** 设 $H$ 为实 Hilbert 空间，$T>0$，轨迹 $w:[0,T]\to H$ 连续并在 $[0,T)$ 上可右微；对每个 $t$，$A(t):H\to H$ 为线性算子，且

\[
w'(t)=A(t)w(t)+r(t).
\]

**假设。** 存在常数 $\gamma>0$ 与 $\rho\geq 0$，使每个 $t\in[0,T)$ 及 $z\in H$ 都满足

\[
\langle z,A(t)z\rangle\leq-\gamma\|z\|^2,
\qquad \|r(t)\|\leq\rho.
\]

**定理。** 在上述假设下，对每个 $t\in[0,T]$ 都有指数误差管

\[
\boxed{\|w(t)\|\leq e^{-\gamma t}\|w(0)\|
+\frac{\rho}{\gamma}(1-e^{-\gamma t}).}
\tag{11.1}
\]

**证明。** 在 $w(t)\neq0$ 时，范数的右导数满足

\[
\frac{d^+}{dt}\|w(t)\|
=\frac{\langle w(t),w'(t)\rangle}{\|w(t)\|}
\leq-\gamma\|w(t)\|+\rho.
\]

**证明。** 在 $w(t)=0$ 时，相同上界由范数的右上导数得到。乘以 $e^{\gamma t}$ 并在 $[0,t]$ 上积分，便有

\[
e^{\gamma t}\|w(t)\|-\|w(0)\|
\leq\rho\int_0^t e^{\gamma s}\,ds
=\frac{\rho}{\gamma}(e^{\gamma t}-1),
\]

**证明。** 这与式 (11.1) 等价。

**命题。** 若 $\rho=0$，则 $\|w(t)\|\leq e^{-\gamma t}\|w(0)\|$。若标量轨迹满足 $a'=-\gamma(a-c)+r$ 且 $|r|\leq\rho$，则

\[
|a(t)-c|\leq e^{-\gamma t}|a(0)-c|
+\frac{\rho}{\gamma}(1-e^{-\gamma t}).
\]

**证明。** 第一式是在式 (11.1) 中取 $\rho=0$；第二式对误差 $w=a-c$ 应用同一定理。

### 11.4 受迫剪切流的残差、不动点与吸引界

**定义。** 在二维环面 $\mathbb T^2=(\mathbb R/2\pi\mathbb Z)^2$ 上，取 $T>0$、$k\in\mathbb N$、$\nu>0$ 以及可微函数 $a:[0,T]\to\mathbb R$，并定义

\[
\Phi_k(x,y)=(1,k)\cos(-2kx+2y),\qquad
\Gamma_k=4\nu(k^2+1),\qquad
u_a(t,x,y)=a(t)\Phi_k(x,y).
\]

**命题。** 场 $u_a$ 无散度，并满足零压力 Navier--Stokes 残差恒等式

\[
\partial_tu_a+(u_a\cdot\nabla)u_a-\nu\Delta u_a
=(a'(t)+\Gamma_k a(t))\Phi_k.
\tag{11.2}
\]

**证明。** 速度方向 $(1,k)$ 与波矢 $(-2k,2)$ 的内积为 $-2k+2k=0$，故 $\nabla\cdot u_a=0$ 且 $(u_a\cdot\nabla)u_a=0$。又有

\[
\Delta\Phi_k=-4(k^2+1)\Phi_k,
\qquad \partial_tu_a=a'(t)\Phi_k,
\]

**证明。** 代入即得式 (11.2)。

**定义。** 固定 $c\in\mathbb R$，令

\[
u_*(x,y)=c\Phi_k(x,y),\qquad
f_*(x,y)=\Gamma_kc\Phi_k(x,y).
\]

**定理。** 场 $u_*$ 是外力 $f_*$ 下的定常零压力解。

**假设。** 设外力为 $f_*+r(t)\Phi_k$，其中 $|r(t)|\leq\rho$，并设幅度满足

\[
a'(t)=-\Gamma_k(a(t)-c)+r(t),
\]

**定理。** 在上述外力和幅度方程的假设下，对 $i\in\{1,2\}$、$t\in[0,T]$ 及 $(x,y)\in\mathbb T^2$，

\[
|u_{a,i}(t,x,y)-u_{*,i}(x,y)|\leq
(1+k)\left[e^{-\Gamma_k t}|a(0)-c|
+\frac{\rho}{\Gamma_k}(1-e^{-\Gamma_k t})\right].
\tag{11.3}
\]

**证明。** 对常幅 $a=c$ 使用式 (11.2)，得到残差 $\Gamma_kc\Phi_k=f_*$。对一般 $a$，式 (11.2) 与幅度方程给出残差 $(\Gamma_kc+r)\Phi_k=f_*+r\Phi_k$。由于 $\Gamma_k>0$，式 (11.1) 作用于 $a-c$；再由 $|\Phi_{k,i}(x,y)|\leq1+k$ 得式 (11.3)。

**命题。** 对每个 $t$ 都有 $a(t)=u_{a,1}(t,0,0)$。当 $r=0$ 时，

\[
a(t)=c+(a(0)-c)e^{-\Gamma_k t},
\]

**命题。** 若 $r=0$ 且 $a$ 的定义域为 $[0,\infty)$，则同一剪切不变族内的解全局趋近 $u_*$。

**证明。** 因为 $\Phi_{k,1}(0,0)=1$，第一式成立。第二式是线性方程 $a'=-\Gamma_k(a-c)$ 的解；$\Gamma_k>0$ 蕴含指数项趋于零。

### 11.5 周期 Navier--Stokes 稳态的扰动能量恒等式

**假设。** 设 $u$ 与 $u_*$ 是光滑周期无散度向量场，$u$ 满足带外力 $f+r$ 的 Navier--Stokes 方程，$u_*$ 满足带外力 $f$ 的定常方程。令 $w=u-u_*$，并假设周期分部积分以及压力与无散度场的 $L^2$ 正交性成立。

**命题。** 扰动 $w$ 满足

\[
\frac12\frac{d}{dt}\|w\|_{L^2}^2
+\nu\|\nabla w\|_{L^2}^2
=-\int_{\mathbb T^d}w\cdot((w\cdot\nabla)u_*)
+\int_{\mathbb T^d}w\cdot r.
\tag{11.4}
\]

**证明。** 两个方程相减后，对 $w$ 作 $L^2$ 配对。周期边界与无散度条件使

\[
\int w\cdot((u_*\cdot\nabla)w)=0,
\qquad
\int w\cdot((w\cdot\nabla)w)=0,
\]

**证明。** 压力项也为零，而黏性项经分部积分成为 $\nu\|\nabla w\|_{L^2}^2$，余项即为式 (11.4)。

**假设。** 再假设 $w$ 属于零均值子空间，并满足 Poincare 不等式

\[
\|\nabla w\|_{L^2}^2\geq\lambda_1\|w\|_{L^2}^2
\]

**假设。** 同时假设

\[
-\int_{\mathbb T^d}w\cdot((w\cdot\nabla)u_*)
\leq G\|w\|_{L^2}^2,
\qquad
\gamma=\nu\lambda_1-G>0.
\]

**定理。** 若 $\|r(t)\|_{L^2}\leq\rho$，则 $\|w(t)\|_{L^2}$ 满足式 (11.1) 的指数误差管。

**证明。** 由式 (11.4)、Poincare 不等式和 Cauchy--Schwarz 不等式，

\[
\frac12\frac{d}{dt}\|w\|_{L^2}^2
\leq-\gamma\|w\|_{L^2}^2+\rho\|w\|_{L^2}.
\]

**证明。** 对 $\|w\|_{L^2}$ 应用第 11.3 节的比较论证即得结论。

## 12. 正则化能量、二次平衡证书与记忆消元

### 12.2 零范数处的正则化能量比较

**假设。** 设 $H$ 为实 Hilbert 空间，轨迹 $u:[0,T]\to H$ 连续并在 $[0,T)$ 上有强右导数 $u'$。设 $\gamma>0$、$\rho\geq0$，且

\[
\langle u(t),u'(t)\rangle
\leq-\gamma\|u(t)\|^2+\rho\|u(t)\|.
\tag{12.1}
\]

**定义。** 对 $\delta>0$，定义正则化范数

\[
z_\delta(t)=\sqrt{\|u(t)\|^2+\delta^2}.
\]

**定理。** 在上述假设下，对每个 $t\in[0,T]$，

\[
\|u(t)\|\leq e^{-\gamma t}\|u(0)\|
+\frac{\rho}{\gamma}(1-e^{-\gamma t}).
\tag{12.2}
\]

**证明。** 记 $n=\|u(t)\|$、$z=z_\delta(t)$。由于 $z>0$，链式法则在 $u(t)=0$ 时仍可使用。恒等式

\[
(-\gamma z+\rho+\gamma\delta)z-(-\gamma n^2+\rho n)
=\rho(z-n)+\gamma\delta(z-\delta)
-\gamma(z^2-n^2-\delta^2)
\]

**证明。** 上式的末项为零，其余两项非负。因此式 (12.1) 给出

\[
z_\delta'(t)
=\frac{\langle u(t),u'(t)\rangle}{z_\delta(t)}
\leq-\gamma z_\delta(t)+\rho+\gamma\delta.
\]

**证明。** 标量比较于是得到

\[
z_\delta(t)\leq e^{-\gamma t}z_\delta(0)
+\left(\frac{\rho}{\gamma}+\delta\right)(1-e^{-\gamma t}).
\]

**证明。** 令 $\delta\downarrow0$，利用 $z_\delta(t)\to\|u(t)\|$，即得式 (12.2)。

### 12.3 同一正裕量的动态与静态结论

**定义。** 设 $H$ 为实 Hilbert 空间，$L:H\to H$ 为线性映射，$B:H\times H\to H$ 为双线性映射，$f\in H$，并定义

\[
F(x)=Lx-B(x,x)+f.
\]

**假设。** 对所有 $p,q\in H$，假设

\[
\langle q,B(p,q)\rangle=0.
\tag{12.3}
\]

**假设。** 再设 $v\in H$ 满足 $F(v)=0$。假设存在 $\mu,G\in\mathbb R$，使每个 $w\in H$ 都满足

\[
\langle w,Lw\rangle\leq-\mu\|w\|^2,
\qquad
-\langle w,B(w,v)\rangle\leq G\|w\|^2,
\qquad
\gamma=\mu-G>0.
\tag{12.4}
\]

**命题。** 对每个 $w\in H$，有差能量恒等式

\[
\langle w,F(v+w)-F(v)\rangle
=\langle w,Lw\rangle-\langle w,B(w,v)\rangle.
\tag{12.5}
\]

**证明。** 双线性展开给出

\[
B(v+w,v+w)=B(v,v)+B(v,w)+B(w,v)+B(w,w).
\]

**证明。** 由式 (12.3)，$B(v,w)$ 与 $B(w,w)$ 对 $w$ 的配对均为零，故只余式 (12.5) 的两项。

**定理。** 若轨迹 $u:[0,T]\to H$ 连续并在 $[0,T)$ 上有强右导数，且满足 $u'=F(u)+r$ 与 $\|r(t)\|\leq\rho$，则同一个正裕量 $\gamma$ 给出

\[
\|u(t)-v\|\leq e^{-\gamma t}\|u(0)-v\|
+\frac{\rho}{\gamma}(1-e^{-\gamma t}).
\tag{12.6}
\]

**定理。** 对每个 $x\in H$，同一个 $\gamma$ 还给出静态残差界

\[
\boxed{\|x-v\|\leq\frac{\|F(x)\|}{\gamma}.}
\tag{12.7}
\]

**定理。** 特别地，$v$ 是 $F$ 的唯一零点。

**证明。** 令 $w=u-v$。由式 (12.4)--(12.5)，

\[
\langle w,w'\rangle
\leq-\gamma\|w\|^2+\rho\|w\|,
\]

**证明。** 故式 (12.2) 给出式 (12.6)。对静态点令 $w=x-v$，则

\[
\gamma\|w\|^2
\leq-\langle w,F(x)\rangle
\leq\|w\|\,\|F(x)\|.
\]

**证明。** $w=0$ 时结论显然；$w\neq0$ 时约去 $\|w\|$ 得式 (12.7)。若 $F(x)=0$，式 (12.7) 强制 $x=v$。

### 12.4 耗散稳定与瞬时恢复的条件分离

**定义。** 设 $T>0$、$a,b,d\in\mathbb R$，并考虑可微的可见状态 $x:[0,T]\to\mathbb R$ 与隐藏状态 $y:[0,T]\to\mathbb R$ 构成的系统

\[
x'=-ax+by,
\qquad
y'=-bx-dy.
\tag{12.8}
\]

**命题。** 平方能量 $E=x^2+y^2$ 满足

\[
E'=-2ax^2-2dy^2.
\tag{12.9}
\]

**命题。** 若 $a,d\geq\gamma>0$，则对任意耦合 $b$，

\[
E(t)\leq E(0)e^{-2\gamma t}.
\tag{12.10}
\]

**证明。** 对 $E$ 求导并代入式 (12.8)，两个交叉项 $2bxy$ 与 $-2bxy$ 抵消，得到式 (12.9)。再由 $E'\leq-2\gamma E$ 积分即得式 (12.10)。

**定理。** 若 $b\neq0$，则隐藏状态由可见状态及其导数精确恢复为

\[
y=\frac{x'+ax}{b}.
\tag{12.11}
\]

**假设。** 若观测量 $\widehat x,\widehat v$ 满足

\[
|\widehat x-x|\leq\varepsilon_x,
\qquad
|\widehat v-x'|\leq\varepsilon_v,
\]

**定理。** 在上述误差假设下，令 $\widehat y=(\widehat v+a\widehat x)/b$，则

\[
|\widehat y-y|
\leq\frac{\varepsilon_v+|a|\varepsilon_x}{|b|}.
\tag{12.12}
\]

**证明。** 式 (12.11) 由式 (12.8) 的第一式移项并除以 $b$ 得到。两种恢复式相减后应用三角不等式，即得式 (12.12)。

**命题。** 固定满足 $a,d\geq\gamma>0$ 的 $a,d$ 时，能量衰减率式 (12.10) 与 $b$ 无关，而恢复的误差放大系数 $1/|b|$ 随 $|b|\downarrow0$ 发散；当 $\varepsilon_v+|a|\varepsilon_x>0$ 固定时，式 (12.12) 的右端也随之发散。当 $b=0$ 时，$x'=-ax$ 与隐藏初值无关，因而 $x$ 及 $x'$ 不能确定 $y$；同时 $y'=-dy$ 仍使隐藏状态指数衰减。

**证明。** 第一项直接来自式 (12.10) 与式 (12.12)。当 $b=0$ 时，任取两个不同隐藏初值而保持同一可见初值，所得可见轨迹相同，隐藏轨迹却不同；又有 $y(t)=e^{-dt}y(0)$。

### 12.5 精确记忆方程与有限历史误差界

**假设。** 设 $d>0$，且可微函数 $x,y$ 满足式 (12.8)。

**定理。** 隐藏状态具有精确历史表示

\[
y(t)=e^{-dt}\left(y(0)-b\int_0^t e^{ds}x(s)\,ds\right).
\tag{12.13}
\]

**定理。** 因此可见状态满足精确 Volterra 方程

\[
x'(t)=-ax(t)+be^{-dt}y(0)
+\int_0^tK(t-s)x(s)\,ds,
\qquad
\boxed{K(\tau)=-b^2e^{-d\tau}.}
\tag{12.14}
\]

**证明。** 由隐藏方程，

\[
\frac{d}{dt}\bigl(e^{dt}y(t)\bigr)=-be^{dt}x(t).
\]

**证明。** 在 $[0,t]$ 上积分并乘以 $e^{-dt}$ 得式 (12.13)。将其代入 $x'=-ax+by$，并使用 $e^{-dt}e^{ds}=e^{-d(t-s)}$，即得式 (12.14)。

**假设。** 给定同一个可见输入 $x$，设 $y$ 与 $z$ 分别满足

\[
y'=-bx-dy,
\qquad
z'=-bx-dz,
\]

**定理。** 则对任意 $0\leq s\leq t$，

\[
|b(y(t)-z(t))|
\leq |b|e^{-d(t-s)}|y(s)-z(s)|.
\tag{12.15}
\]

**假设。** 再设 $|y(s)-z(s)|\leq Y$、$|b|Y>\eta>0$，并且窗口长度满足

\[
t-s\geq\frac1d\log\frac{|b|Y}{\eta}
\tag{12.16}
\]

**定理。** 在上述窗口假设下，$|b(y(t)-z(t))|\leq\eta$。

**证明。** 差 $h=y-z$ 满足 $h'=-dh$，故 $h(t)=e^{-d(t-s)}h(s)$，从而式 (12.15) 成立。把 $|h(s)|\leq Y$ 代入式 (12.15)，再对指数不等式取对数，即得式 (12.16) 的充分性。

**命题。** 在静态隐藏约束 $0=-bx-dy$ 且 $d\neq0$ 下，

\[
y=-\frac bd x,
\qquad
-ax+by=-\left(a+\frac{b^2}{d}\right)x.
\tag{12.17}
\]

**证明。** 第一式由静态隐藏约束直接解出，代入可见方程右端即得第二式。

### 12.6 有限维块系统的耗散与记忆核

**定义。** 设 $T>0$，$X,Y$ 为有限维实 Hilbert 空间，$A:X\to X$、$D:Y\to Y$、$B:X\to Y$ 为线性映射，$B^*:Y\to X$ 为 $B$ 的伴随。考虑可微轨迹 $x:[0,T]\to X$、$y:[0,T]\to Y$ 满足的块系统

\[
\dot x=-Ax+B^*y,
\qquad
\dot y=-Bx-Dy.
\tag{12.18}
\]

**命题。** 系统 (12.18) 的总能量满足

\[
\frac{d}{dt}\bigl(\|x\|^2+\|y\|^2\bigr)
=-2\langle x,Ax\rangle-2\langle y,Dy\rangle.
\tag{12.19}
\]

**命题。** 若对所有 $\xi\in X$、$\eta\in Y$ 都有 $\langle \xi,A\xi\rangle\geq\alpha\|\xi\|^2$ 与 $\langle \eta,D\eta\rangle\geq\delta\|\eta\|^2$，其中 $\alpha,\delta>0$，则

\[
\|x(t)\|^2+\|y(t)\|^2
\leq e^{-2\min\{\alpha,\delta\}t}
\bigl(\|x(0)\|^2+\|y(0)\|^2\bigr).
\]

**证明。** 对总能量求导。由伴随关系，交叉项

\[
2\langle x,B^*y\rangle-2\langle y,Bx\rangle
\]

**证明。** 上述交叉项恰好抵消，得到式 (12.19)；下界随即给出

\[
\frac{d}{dt}\bigl(\|x\|^2+\|y\|^2\bigr)
\leq-2\min\{\alpha,\delta\}
\bigl(\|x\|^2+\|y\|^2\bigr).
\]

**命题。** 消去隐藏状态后，

\[
y(t)=e^{-tD}y(0)-\int_0^t e^{-(t-s)D}Bx(s)\,ds,
\]

**命题。** 将上述隐藏状态表示代入可见方程，则

\[
\dot x(t)=-Ax(t)+B^*e^{-tD}y(0)
+\int_0^tK(t-s)x(s)\,ds,
\qquad
K(\tau)=-B^*e^{-\tau D}B.
\tag{12.20}
\]

**证明。** 对隐藏方程应用常系数线性方程的变参数公式，得到 $y(t)$ 的表示；将该表示代回可见方程，积分项的算子系数即为式 (12.20) 中的 $K$。

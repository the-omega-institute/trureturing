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
## 15. 有限含噪矩的精确极值与全时间 Laplace 谱底恢复

### 15.1 定义：有限矩观察与外部原子

设 $N\geq1$，$x_1,\ldots,x_N$ 是两两不同的实数，$y$ 不等于任一节点。设 $\ell_i$ 为相应 Lagrange 基多项式，$c_i=\ell_i(y)$，$J=\{i:c_i>0\}$，并定义

\[
p=\sum_{i\in J}\ell_i,\quad P=p(y),\quad
L=\sum_{k=1}^{N-1}|p_k|.
\tag{15.1}
\]

定义 $d_0=0$；对 $k\geq1$，当 $p_k\geq0$ 时取 $d_k=1$，否则取 $d_k=-1$。再定义

\[
r_i=\sum_{k=0}^{N-1}d_k[\ell_i]_k,\qquad
B=\sum_{i=1}^{N}\left|\frac LP-\frac{r_i}{c_i}\right|.
\tag{15.2}
\]

所有 $c_i$ 均非零，$\sum_i c_i=1$，所以 $P=\sum_{i\in J}c_i\geq1$。记 $\mathcal W_\varepsilon(x,y)$ 为所有满足下列条件的 $w\geq0$ 构成的集合：存在 $u_i,v_i\geq0$，使

\[
w+\sum_i u_i=\sum_i v_i=1,\qquad
\left|wy^k+\sum_i u_i x_i^k-\sum_i v_i x_i^k\right|\leq\varepsilon
\quad(0\leq k<N).
\tag{15.3}
\]

这些是实际概率测度 $\mu=w\delta_y+\sum_i u_i\delta_{x_i}$、$\nu=\sum_i v_i\delta_{x_i}$ 的矩约束。零次矩误差恒为零。

### 15.2 定理：显式噪声区间内的精确可达极值

当

\[
0\leq\varepsilon\leq\frac1{2P(1+B)},
\]

时，

\[
\boxed{\max\mathcal W_\varepsilon(x,y)=\frac{1+\varepsilon L}{P}.}
\tag{15.4}
\]

**证明。** 记 $w_*=(1+\varepsilon L)/P$，构造

\[
b_i=w_*c_i-\varepsilon r_i,\qquad
u_i=\max\{-b_i,0\},\qquad v_i=\max\{b_i,0\}.
\tag{15.5}
\]

这里式 (15.5) 中的 $u_i$ 是 $\mu$ 的节点权重。对任意次数小于 $N$ 的多项式 $f$，Lagrange 恒等式为 $f=\sum_i f(x_i)\ell_i$。对其分别在 $y$ 求值及作用线性泛函 $D(f)=\sum_{k=0}^{N-1}d_k f_k$，得到

\[
\sum_i c_i x_i^k=y^k,\qquad
\sum_i r_i x_i^k=d_k,\qquad
\sum_i r_i=0,\qquad\sum_{i\in J}r_i=D(p)=L.
\tag{15.6}
\]

由噪声条件，每个 $i$ 满足

\[
\frac1P+\varepsilon\left(\frac LP-\frac{r_i}{c_i}\right)
\geq\frac1{2P}>0.
\]

而 $b_i$ 等于该正数乘以 $c_i$，因此所有节点的符号保持不变。于是

\[
\sum_i v_i=\sum_{i\in J}b_i=w_*P-\varepsilon L=1,
\qquad \sum_i b_i=w_*.
\]

从 $v_i-u_i=b_i$ 得到 $w_*+\sum_i u_i=1$。式 (15.6) 又给出每个矩误差精确等于 $\varepsilon d_k$，所以构造可行。

对任意可行概率对，由 $p(x_i)\in\{0,1\}$、$p(y)=P$ 和非负权重，有

\[
wP\leq\int p\,d\mu\leq\int p\,d\nu+\varepsilon L\leq1+\varepsilon L.
\]

其中常数系数不贡献误差，因为两边总质量完全相同。除以 $P>0$ 即得上界，与式 (15.5) 构造相等。此证明同时计算了极值、可达分布和保持正性的噪声区间。多项式矩对偶的背景参见 [15-A]、[15-B]。

### 15.3 命题：一个有理数取等族

当节点为 $1/4,1/2,3/4$，外部点为 $1$ 时，

\[
c=(1,-3,3),\quad p(x)=4-16x+16x^2,\quad P=4,\quad L=32,\quad
r=(18,-32,14),\quad B=16.
\]

因而式 (15.4) 在 $0\leq\varepsilon\leq1/136$ 上给出 $w_*=1/4+8\varepsilon$。实际取等概率对为

\[
\begin{aligned}
\mu_\varepsilon&=(1/4+8\varepsilon)\delta_1+(3/4-8\varepsilon)\delta_{1/2},\\
\nu_\varepsilon&=(1/4-10\varepsilon)\delta_{1/4}+(3/4+10\varepsilon)\delta_{3/4}.
\end{aligned}
\tag{15.7}
\]

**证明。** 直接代入 Lagrange 基和式 (15.2) 得到列出的常数。两边总质量为一，一次矩误差为 $-\varepsilon$，二次矩误差为 $\varepsilon$。这些具体权重在更大的区间 $[0,1/40]$ 上仍非负，因此此特例的取等区间可延伸到 $1/40$；通用充分半径 $1/136$ 没有被声称是最大半径。

### 15.4 定理：Chebyshev 节点给出的连续支撑精确界

设 $n\geq1$，$0<a<b<y$，取递减的 Chebyshev--Lobatto 节点

\[
x_j=\frac{a+b}{2}+\frac{b-a}{2}\cos(j\pi/n),\qquad j=0,\ldots,n,
\quad z=\frac{2y-a-b}{b-a}>1.
\]

对所有支撑于 $[a,y]$ 的概率测度 $\mu$ 和支撑于 $[a,b]$ 的概率测度 $\nu$，若二者前 $n+1$ 个矩完全相同，则外部点 $y$ 的最大可能质量为

\[
\boxed{\mu(\{y\})\leq\frac2{1+T_n(z)},}
\tag{15.8}
\]

而此上界由实际有限原子概率对达到。

**证明。** Lagrange 乘积的分子全正，递减节点使其分母的符号为 $(-1)^j$，故 $\operatorname{sign}(c_j)=(-1)^j$。在节点上 $T_n((2x_j-a-b)/(b-a))=(-1)^j$。次数不超过 $n$ 的插值唯一性给出

\[
p(x)=\frac{1+T_n((2x-a-b)/(b-a))}{2},\qquad
P=\frac{1+T_n(z)}2.
\]

在 $[a,b]$ 上 $0\leq p\leq1$，在 $[b,y]$ 上 $p\geq1$，因此 $\mu(\{y\})P\leq\int p\,d\mu=\int p\,d\nu\leq1$。式 (15.5) 在零噪声时给出支撑于所声明区间的取等分布。该证明不把支撑事先限制在节点上。

若使用逐矩噪声上界 $\varepsilon$，则在式 (15.2) 的显式充分噪声区间内，连续支撑问题的最大外部原子质量为

\[
\boxed{
\frac{2+\varepsilon\left[
T_n\!\left(\frac{2+a+b}{b-a}\right)
-T_n\!\left(\frac{a+b}{b-a}\right)\right]}
{1+T_n(z)}.
}
\tag{15.9}
\]

**证明。** 对非节点支撑仍使用同一个非负多项式上界。移位 Chebyshev 多项式的全部零点在 $(a,b)$，故其系数符号交替。将它在 $-1$ 处求值，并减去常数系数的绝对值，得到非恒定系数的绝对值和

\[
\sum_{k=1}^n\left|[T_n((2x-a-b)/(b-a))]_k\right|
=T_n\!\left(\frac{2+a+b}{b-a}\right)-T_n\!\left(\frac{a+b}{b-a}\right).
\]

式 (15.4) 的正权重构造达到相同上界。超出显式噪声区间后，上界仍有效，但此处不声称取等公式继续成立。

### 15.5 定理：固定原子权重下的有限前缀分辨率

固定 $0<\eta<1$。在式 (15.8) 的支撑设置下，存在匹配次数 $0,\ldots,n$ 的概率对，且 $\mu(\{y\})\geq\eta$，当且仅当

\[
y-b\leq\frac{b-a}{2}\left[
\cosh\left(\frac{\operatorname{arcosh}(2/\eta-1)}n\right)-1\right].
\tag{15.10}
\]

在边界取等时，两种概率测度各自在其最大支撑点的质量都至少为 $\eta$。

**证明。** 当 $z>1$，$T_n(z)=\cosh(n\operatorname{arcosh}z)$ 严格递增。对式 (15.8) 反解即得等价。边界处第一种测度在 $y$ 上的质量为 $\eta$；另一种在最大节点 $b=x_0$ 上的质量为 $c_0/P$。乘积公式

\[
c_0=\prod_{j=1}^n\frac{y-x_j}{b-x_j}>1
\]

给出 $c_0/P>1/P=\eta$。对固定 $\eta$，式 (15.10) 的宽度是 $\Theta(n^{-2})$。

对 $x=e^{-hE}$，$h>0$，次数 $0,\ldots,n$ 的相同矩对应时间 $0,h,\ldots,nh$ 的完全相同 Laplace 读数，而两种最低能量相差 $h^{-1}\log(y/b)$。这只给出所列采样时刻的精确匹配。

### 15.6 定理：全时间绝对噪声下的谱底 minimax 阶

固定 $0\leq E_-<E_+<\infty$ 与 $0<\eta<1$。令 $\mathcal M$ 为所有支撑于 $[E_-,E_+]$ 的概率测度 $\sigma$，要求其最低支撑点

\[
g(\sigma)=\min\operatorname{supp}\sigma
\]

具有质量 $\sigma(\{g(\sigma)\})\geq\eta$。观察为任意函数 $Y:[0,\infty)\to\mathbb R$，满足

\[
\sup_{t\geq0}|Y(t)-C_\sigma(t)|\leq\varepsilon,
\qquad C_\sigma(t)=\int e^{-tE}\,\sigma(dE).
\]

对任意估计函数 $\widehat g$，定义统一最坏误差及 minimax 误差

\[
\mathcal R(\varepsilon)=\inf_{\widehat g}\ \sup_{\sigma\in\mathcal M}
\sup_{\|Y-C_\sigma\|_\infty\leq\varepsilon}
|\widehat g(Y)-g(\sigma)|.
\tag{15.11}
\]

存在只依赖固定参数的正数 $c,C,\varepsilon_0$，使

\[
\boxed{
\frac{c}{\log^2(1/\varepsilon)}
\leq\mathcal R(\varepsilon)
\leq\frac{C}{\log^2(1/\varepsilon)}
\qquad(0<\varepsilon<\varepsilon_0).
}
\tag{15.12}
\]

下界可以只用有限原子测度实现，但其原子数随精度增加；定理不规定一个固定维数上限。

**上界证明。** 取 $h=1/E_+$、$a=e^{-1}$、$b_0=e^{-E_-/E_+}$、$a_0=a/2$。推送 $x=e^{-hE}$ 把所有测度支撑送入 $[a,b_0]$。考虑两个能与同一 $Y$ 相容的测度，其最大 $x$ 支撑点分别为 $y>b$。它们在时间 $kh$ 的读数差不超过 $2\varepsilon$。

令 $A_b(x)=(2x-a_0-b)/(b-a_0)$，并取

\[
p_n(x)=\frac{1+T_n(A_b(x))}{2}.
\]

该多项式在第一测度的支撑上非负，在第二测度的支撑上位于 $[0,1]$。由于 $b\geq a$，其仿射内层系数范数满足

\[
\|A_b\|_{\mathrm{coef},1}=\frac{2+a_0+b}{b-a_0}
\leq S:=\frac{2+a_0+b_0}{a-a_0}.
\]

设 $Q=2S+1>1$。由 $T_{k+1}=2A_bT_k-T_{k-1}$，归纳得到 $\|T_n(A_b)\|_{\mathrm{coef},1}\leq Q^n$。常数项由总质量抵消，于是

\[
\eta p_n(y)\leq1+\varepsilon Q^n.
\]

对足够小的 $\varepsilon$ 取 $n=\lfloor\log(1/\varepsilon)/(2\log Q)\rfloor\geq1$。则 $\varepsilon Q^n\leq1$，所以令 $A_\eta=\operatorname{arcosh}(4/\eta-1)$，有

\[
y-b\leq\frac{b-a_0}{2}[\cosh(A_\eta/n)-1]
\leq\frac{b_0A_\eta^2\cosh(A_\eta)}{4n^2}.
\]

最后使用 $h^{-1}\log(y/b)\leq(y-b)/(ha)$，得到同一噪声数据的所有相容最低能量构成的集合直径为 $O(\log^{-2}(1/\varepsilon))$。以该集合上下确界的中点为估计，若集合为空则任取 $E_-$，即可得到统一上界。这是估计函数的存在性证明，不附带计算复杂度结论；所用信息实际上只是 $O(\log(1/\varepsilon))$ 个等间距样本。

**下界证明。** 选固定 $a<A<B<Y<b_0$，并记 $D_\eta=\operatorname{arcosh}(2/\eta-1)>0$。对足够大的偶数 $n$，令

\[
y_n=B+\frac{B-A}{2}[\cosh(D_\eta/n)-1]<Y.
\]

用区间 $[A,B]$ 上的式 (15.8) 取等构造，得到支撑于 $[A,Y]$ 的概率对，匹配次数 $0,\ldots,n$ 的矩，最大支撑点分别为 $y_n$ 与 $B$，且两端原子质量都至少为 $\eta$。

选择固定 $\rho>1$，使区间 $[A,Y]$ 的闭 Bernstein 椭圆完全包含于开集 $\{z:\operatorname{Re}z>0,\ |z|<1\}$。这样的 $\rho$ 存在，因为 $[A,Y]$ 紧含于 $(0,1)$。对所有 $s\geq0$，主值分支 $f_s(z)=\exp(s\operatorname{Log}z)$ 在此椭圆的邻域解析，并且 $|f_s(z)|=|z|^s\leq1$。Bernstein--Chebyshev 估计 [15-C] 给出一个次数不超过 $n$ 的多项式 $q_{n,s}$，满足

\[
\sup_{x\in[A,Y]}|x^s-q_{n,s}(x)|\leq\frac{2\rho^{-n}}{\rho-1}
\quad\text{对所有 }s\geq0.
\]

两种测度对 $q_{n,s}$ 的积分完全相同。各自总质量为一，所以其 $x^s$ 积分之差最多为 $4\rho^{-n}/(\rho-1)$。取 $s=t/h$，得到真正的全时间估计

\[
\sup_{t\geq0}|C_1(t)-C_0(t)|\leq\frac{4\rho^{-n}}{\rho-1}.
\tag{15.13}
\]

选最小的足够大偶数 $n$ 使右侧不超过 $2\varepsilon$；于是 $n=O(\log(1/\varepsilon))$。两个最低能量之差满足

\[
\frac1h\log\frac{y_n}{B}
\geq\frac{y_n-B}{hY}
\geq\frac{(B-A)D_\eta^2}{4hY n^2}.
\]

两条全时间读数的中点同时与二者在误差 $\varepsilon$ 内相容，任意估计函数在至少一个模型上的误差不小于该能量差的一半，得到式 (15.12) 的下界。

**推论。** 在上述维数不受统一限制的模型类中，不存在统一的 $O(\varepsilon^\alpha)$ 谱底恢复保证，其中 $\alpha>0$ 任意。因为 $\varepsilon^\alpha\log^2(1/\varepsilon)\to0$。最低态权重在构造中始终至少为固定 $\eta$；下界不依赖让该权重趋于零。

### 15.7 定理：共同循环观察与 Jacobi 边界实现

第 15.6 节下界所用的偶数 $n=2m$ 的零噪声正测度对，可以实现为同一个 $(m+1)$ 维实 Hilbert 空间上的两个正定自伴收缩矩阵 $K_0,K_1$，以及同一个循环单位向量 $e_0$，满足

\[
\langle e_0,K_0^k e_0\rangle=\langle e_0,K_1^k e_0\rangle
\quad(0\leq k\leq2m).
\tag{15.14}
\]

两个 $K$ 可取 Jacobi 三对角矩阵，且仅最后一个对角元不同。其最低能量算子定义为 $H_j=-h^{-1}\log K_j$，则式 (15.13) 对其实际关联函数成立。

**证明。** 符号交替使两种概率测度分别有 $m+1$ 个不同、正权重的原子。它们的次数至 $2m$ 矩完全相同，所以次数不超过 $m$ 的多项式内积完全相同且正定。对 $1,x,\ldots,x^m$ 作正首项系数的 Gram--Schmidt，得到共同正交多项式 $p_0,\ldots,p_m$。乘法算子 $f\mapsto xf$ 在这组基下的矩阵是 Jacobi 矩阵，次对角系数为相邻首项系数之比，严格为正。

矩阵元 $\langle p_i,xp_j\rangle$ 只涉及次数不超过 $i+j+1$ 的矩。除了 $i=j=m$ 外，此次数均不超过 $2m$，所以只有最后的对角元可能不同。有限原子 $L^2$ 空间中，乘法算子的谱就是原子位置，因此两者正定且范数小于一；常数多项式 $p_0=1$ 对应同一个 $e_0$，其各谱方向权重均非零，故为循环向量。谱函数演算给出 $e^{-tH_j}=K_j^{t/h}$，于是测度积分成为实际算子关联函数。

这里秩一边界差属于 $K_0,K_1$。矩阵对数 $H_0,H_1$ 不被断言保持三对角性或局域相互作用。该有限算子构造不指定规范群、场论公理、体积极限或 Yang--Mills 相互作用。

### 15.8 引用

[15-A] Yohann de Castro and Fabrice Gamboa. *Exact Reconstruction Using Beurling Minimal Extrapolation*. Journal of Mathematical Analysis and Applications 395(1), 336--354, 2012. arXiv:1103.4951. https://arxiv.org/abs/1103.4951 . 有限测度广义矩及多项式对偶的背景。

[15-B] Cameron Musco, Christopher Musco, Lucas Rosenblatt and Apoorv Vikram Singh. *Sharper Bounds for Chebyshev Moment Matching, with Applications*. arXiv:2408.12385v3, 18 May 2026. https://arxiv.org/abs/2408.12385v3 . 含噪 Chebyshev 矩与分布恢复的背景；其 Wasserstein 目标与这里的支撑端点目标不同。

[15-C] Lloyd N. Trefethen. *Approximation Theory and Approximation Practice*, Theorems 8.1--8.2. SIAM, 2013; extended edition, 2019. Chapter 8 source: https://github.com/chebfun/ATAP/blob/development/chap8.m . 解析函数的 Chebyshev 系数界和截断误差 $2M\rho^{-n}/(\rho-1)$。

[15-D] Lin Lin and Yu Tong. *Heisenberg-Limited Ground-State Energy Estimation for Early Fault-Tolerant Quantum Computers*. PRX Quantum 3, 010318, 2022. DOI: 10.1103/PRXQuantum.3.010318. https://doi.org/10.1103/PRXQuantum.3.010318 . 其相干量子查询模型与式 (15.11) 的被动含绝对噪声 Laplace 观察模型不同，二者不共享本文下界的查询前提。

## 16. 固定模态数、遗漏质量与谱底识别的阶数

### 16.1 定义：单侧稀疏矩比较

设 $d\geq1$，$x_i\in[0,1]$、$u_i\geq0$（$1\leq i\leq d$），并令 $\rho$ 为 $[0,1]$ 上总质量不超过 $\tau$ 的有限正测度。设 $\nu$ 为支撑于 $(-\infty,b]$ 的有限正测度，且本节所用矩有限。定义

\[
\mu=\sum_{i=1}^d u_i\delta_{x_i}+\rho,\qquad
m_k(\sigma)=\int t^k\,\sigma(dt).
\]

假设 $b\geq0$，存在指标 $i_*$ 使 $x_*>b$、$u_{i_*}\geq\eta>0$，其中 $x_*=x_{i_*}$；并且

\[
|m_k(\mu)-m_k(\nu)|\leq\varepsilon\quad(0\leq k\leq2d-1),\qquad\varepsilon\geq0.
\tag{16.1}
\]

节点可以重合，权重可以为零，不要求概率归一化。$\rho$ 是遗漏的正质量，不要求它只位于高能或低能一侧。

### 16.2 定理：选择性消去与独立的尾误差代价

令 $S=\{i:x_i\leq b\}$、$s=|S|$，则

\[
\eta(x_*-b)^{2s+1}\leq2^{2s+1}\varepsilon+\tau,
\qquad
\boxed{\eta(x_*-b)^{2d-1}\leq2^{2d-1}\varepsilon+\tau.}
\tag{16.2}
\]

**证明。** 构造

\[
q(t)=(t-b)\prod_{i\in S}(t-x_i)^2,\qquad D=2s+1\leq2d-1.
\]

在保留节点中，$x_i\leq b$ 时 $q(x_i)=0$，$x_i>b$ 时 $q(x_i)\geq0$；在比较测度的支撑上 $q\leq0$。所有根都不大于 $b$，故 $q(x_*)\geq(x_*-b)^D$。由于 $0\leq b<x_*\leq1$，所有根与 $[0,1]$ 内的点的距离都不超过一，故 $\sup_{[0,1]}|q|\leq1$。因此

\[
\eta(x_*-b)^D\leq\int q\,d(\mu-\nu)+\tau.
\tag{16.3}
\]

若线性泛函 $F$ 对次数至 $D$ 的单项式满足 $|F(t^k)|\leq\varepsilon$，每乘一个根 $a\in[0,1]$ 的线性因子，就有

\[
|F((t-a)t^k)|\leq |F(t^{k+1})|+a|F(t^k)|\leq2\varepsilon.
\]

对实际因子列表归纳，得 $|F(q)|\leq2^D\varepsilon$。把 $F(f)=\int f\,d(\mu-\nu)$ 代入式 (16.3) 即得第一式。最后由 $0<x_*-b\leq1$、$D\leq2d-1$ 得第二式。根的选择避免了让 $x_*$ 与同侧邻近节点之间的距离进入分母；只有位于比较阈值以下的保留节点被消去。多项式主次化和支撑控制的方法背景见 [16-A, §3, Lemma 15]，无分离稀疏矩恢复的算法背景见 [16-B]。

**推论。** 当 $\rho=0$ 时，$x_*-b\leq2(\varepsilon/\eta)^{1/(2d-1)}$。当 $\rho\neq0$ 时，式 (16.2) 明确区分观察误差 $\varepsilon$ 与遗漏质量 $\tau$；有限观察本身不提供 $\tau$ 的独立上界。

### 16.3 定义：被动 Laplace 观察的两个模型类

固定 $0\leq E_-<E_+<\infty$、$0<\eta<1$。令 $\mathcal M_d$ 为 $[E_-,E_+]$ 上至多有 $d$ 个原子的概率测度，要求其最小支撑点 $g(\sigma)$ 的质量至少为 $\eta$。令 $\mathcal M_{\rm fin}=\bigcup_{j\geq1}\mathcal M_j$，并定义

\[
C_\sigma(t)=\int e^{-tE}\,\sigma(dE),\quad t\geq0,
\qquad
\mathcal R_d(\varepsilon)=\inf_{\widehat g}\sup_{\sigma\in\mathcal M_d}\sup_{\|Y-C_\sigma\|_\infty\leq\varepsilon}
|\widehat g(Y)-g(\sigma)|.
\tag{16.4}
\]

估计函数可读取所有非负时间的被动观测，没有相干量子查询或直接矩阵访问。另定义只有一侧具有模态数约束的可辨识直径

\[
\Omega_d(\varepsilon)=\sup\{|g(\mu)-g(\nu)|:\mu\in\mathcal M_d,\ \nu\in\mathcal M_{\rm fin},\ \|C_\mu-C_\nu\|_\infty\leq\varepsilon\}.
\tag{16.5}
\]

这里上确界同时遍历稀疏侧的全部位置和权重，允许接近碰撞；它不等同于固定一个已分离矩阵后的局部误差。

### 16.4 定理：固定模态数的全时间尖锐幂指数

对每个固定 $d\geq1$，存在正数 $c_d,C_d,\varepsilon_d$，只依赖 $d,E_-,E_+,\eta$，使

\[
\boxed{c_d\varepsilon^{1/(2d-1)}\leq\mathcal R_d(\varepsilon)
\leq C_d\varepsilon^{1/(2d-1)}}\qquad(0<\varepsilon<\varepsilon_d).
\tag{16.6}
\]

**上界证明。** 取 $h=1/E_+$，推送 $x=e^{-hE}$，使所有节点属于 $[e^{-1},1]$。同一数据的两个相容模型在次数 $0,\ldots,2d-1$ 的矩差至多为 $2\varepsilon$。把具有较小最低能量、即较大最大 $x$ 的模型作为式 (16.2) 的稀疏侧，零权重补足 $d$ 个槽位。其最大节点权重至少为 $\eta$，得到节点差不超过 $2(2\varepsilon/\eta)^{1/(2d-1)}$。又有

\[
|g(\mu)-g(\nu)|=h^{-1}|\log x_{\max,\mu}-\log x_{\max,\nu}|
\leq eE_+|x_{\max,\mu}-x_{\max,\nu}|.
\]

取相容谱底集合上下确界的中点为估计；空相容集任取 $E_-$。其最坏误差不超过上述直径的一半。这只是估计函数存在性；所用信息可缩至 $2d$ 个等间距时刻。

**下界构造。** 记 $T_n$ 为满足 $T_n(\cos\theta)=\cos(n\theta)$ 的第一类 Chebyshev 多项式。先设 $d\geq2$，令 $n=2d-2$、$A_\eta=\operatorname{arcosh}(2/\eta-1)>0$、

\[
x_j=\tfrac12(1+\cos(j\pi/n)),\quad j=0,\ldots,n,
\qquad y=\tfrac12(1+\cosh(A_\eta/n))>1.
\]

令 $\ell_j$ 为这些节点的 Lagrange 基，$c_j=\ell_j(y)$。乘积公式给 $\operatorname{sign}(c_j)=(-1)^j$。由于 $\sum c_j=1$，以及节点上的 $T_n(2x_j-1)=(-1)^j$，插值恒等式给

\[
P:=\sum_{j\ {\rm even}}c_j=\frac{1+T_n(2y-1)}2=\frac1\eta.
\]

因此

\[
\alpha=P^{-1}\delta_y+P^{-1}\sum_{j\ {\rm odd}}(-c_j)\delta_{x_j},\qquad
\beta=P^{-1}\sum_{j\ {\rm even}}c_j\delta_{x_j}
\tag{16.7}
\]

是两个各有 $d$ 个正原子的概率测度，匹配次数 $0,\ldots,2d-2$ 的矩。$\alpha$ 在 $y$ 上的质量为 $\eta$；$\beta$ 在最大节点 $1$ 上的质量为 $c_0/P>\eta$，因为 $c_0=\prod_{j\ne0}(y-x_j)/(1-x_j)>1$。这一步控制两个模型的端点权重，超出了仅有交错支撑矩匹配的存在陈述 [16-A, Lemma 30]。

反射坐标 $\xi=y-x$ 后，两种分布支撑于 $[0,W]$，$W=y$，最小点分别为 $0$ 与 $\Delta=y-1>0$，前 $2d-1$ 个矩仍相同。取固定 $E_0\in(E_-,E_+)$ 且 $E_0>0$，将能量设为 $E=E_0+s\xi$，其中 $sW\leq E_+-E_0$。记 $q=2d-1$。对任意 $t\geq0$，在 $\xi=0$ 展开到 $q-1$ 阶，Taylor 余项的绝对值不超过 $(stW)^q/q!$。匹配的多项式部分积分相消，故

\[
|C_\alpha(t)-C_\beta(t)|\leq2e^{-E_0t}\frac{(stW)^q}{q!}
\leq2\left(\frac{sW}{E_0}\right)^q.
\tag{16.8}
\]

末步由 $e^{E_0t}\geq(E_0t)^q/q!$ 得出，对全部时间同时成立。取 $s=(E_0/W)\varepsilon^{1/q}$；对充分小的 $\varepsilon$ 能量仍在固定区间内。两条曲线之差至多为 $2\varepsilon$，而谱底差为 $s\Delta$。中点观测同时相容，任何估计在至少一侧的误差不小于 $s\Delta/2$，得下界。

$d=1$ 时用 $\delta_{E_0}$ 与 $\delta_{E_0+s}$，并用 $e^{-E_0t}(1-e^{-st})\leq st e^{-E_0t}\leq s/E_0$。经典矩比较中的 $1/(2d-1)$ 指数已见 [16-A, Proposition 1]；这里给出的是固定最低态权重和全部时间绝对误差下的端点构造及上下界。

### 16.5 定理：多允许一个隐藏模态的代价

对每个固定 $d\geq1$，式 (16.5) 的直径满足

\[
\boxed{\Omega_d(\varepsilon)=\Theta_{d,E_-,E_+,\eta}(\varepsilon^{1/(2d)})}
\qquad(\varepsilon\downarrow0).
\tag{16.9}
\]

下界只需令竞争模型属于 $\mathcal M_{d+1}$，不需要任意大的模式数。

**上界证明。** 仍取 $x=e^{-E/E_+}$。如果稀疏侧的最大节点更大，则式 (16.2) 给出更强的 $1/(2d-1)$ 阶，从而对 $\varepsilon/\eta\leq1$ 也给出 $1/(2d)$ 阶。如果竞争侧的最大节点 $y_*$ 大于稀疏侧的最大节点 $b$，构造

\[
Q(t)=\prod_{i=1}^d(t-x_i)^2.
\]

零权重槽位可补在 $b$。这个多项式在稀疏测度上积分为零，在竞争测度上非负，且 $Q(y_*)\geq(y_*-b)^{2d}$。因子归纳给其系数预算不超过 $2^{2d}$，所以

\[
\eta(y_*-b)^{2d}\leq\int Q\,d\nu\leq2^{2d}\varepsilon.
\]

再次应用对数的 Lipschitz 界，得到所需上界。平方消去的思想与 [16-A, Proposition 2 and Lemma 15] 一致。

**下界证明。** 在式 (16.7) 的构造中改取 $n=2d-1$。奇偶计数给 $\alpha$ 有 $d+1$ 个原子、$\beta$ 有 $d$ 个原子，二者矩匹配至次数 $2d-1$，端点权重仍都至少为 $\eta$。在反射、能量平移与缩放后，式 (16.8) 改为 $q=2d$，得到全时间曲线差不超过 $\varepsilon$ 而端点差为 $c\varepsilon^{1/(2d)}$。例如取 $s=(E_0/W)(\varepsilon/2)^{1/(2d)}$ 即可。这对 $d=1$ 也有效。由于 $\beta\in\mathcal M_d$、$\alpha\in\mathcal M_{d+1}$，得到式 (16.9)。

**推论。** 仅在 $\mathcal M_d$ 内有效的误差保证，不能在允许未排除的额外模式时直接声称同样精度。若一个区间估计必须对全部 $\mathcal M_{\rm fin}$ 及噪声半径 $\varepsilon/2$ 保持覆盖，则上述两条曲线的中点迫使它在某个 $d$ 模态真实模型上具有至少 $c\varepsilon^{1/(2d)}$ 的区间长度。该量词允许真实模型随精度变化，不否定额外分离条件下的点态适应性。

### 16.6 定理：同时保留维数依赖的下界

存在仅依赖 $E_-,E_+,\eta$ 的常数 $c>0$，使对所有整数 $d\geq1$ 及 $0<\varepsilon<1$，有

\[
\mathcal R_d(\varepsilon)\geq c\max_{1\leq m\leq d}\frac{\varepsilon^{1/(2m-1)}}{m^2}.
\tag{16.10}
\]

**证明。** 固定 $E_0\in(E_-,E_+)$、$\kappa=\tfrac12\min\{E_0,E_+-E_0\}>0$。对任意 $m\geq2$，在式 (16.7) 取 $n=2m-2$。此时 $W=y\leq W_\eta=(1+\cosh A_\eta)/2$，并且

\[
\Delta=y-1\geq\frac{A_\eta^2}{4n^2}\geq\frac{A_\eta^2}{16m^2}.
\]

取 $s=\kappa\varepsilon^{1/(2m-1)}/W_\eta$，则所有能量位于固定区间内，式 (16.8) 右侧不超过 $2\varepsilon$。谱底间距至少为 $\kappa A_\eta^2\varepsilon^{1/(2m-1)}/(16W_\eta m^2)$。中点论证及 $\mathcal M_m\subseteq\mathcal M_d$ 给出每个 $m\leq d$ 的下界。$m=1$ 由上述 Dirac 构造给出；减小常数使其也成立，然后取最大值。

**推论。** 当 $0<\varepsilon\leq e^{-1}$ 且 $d\geq\lceil\log(1/\varepsilon)\rceil$ 时，$\mathcal R_d(\varepsilon)\geq c'/\log^2(1/\varepsilon)$，其中 $c'>0$ 仍只依赖固定能量区间及 $\eta$。

**证明。** 在式 (16.10) 取 $m=\lceil L\rceil$、$L=\log(1/\varepsilon)\geq1$。有 $m\leq2L$、$2m-1\geq L$，所以 $\varepsilon^{1/(2m-1)}\geq e^{-1}$。代入即得 $c'=c/(4e)$。这个全时间下界只使用实 Taylor 余项及正测度构造。

### 16.7 问题：维数与精度的统一过渡

在定义 (16.4) 的同一模型和固定 $E_-,E_+,\eta$ 下，是否存在与 $d$ 无关的常数 $C$ 和 $\varepsilon_0>0$，使

\[
\mathcal R_d(\varepsilon)\leq C\max_{1\leq m\leq d}\frac{\varepsilon^{1/(2m-1)}}{m^2}
\qquad(d\geq1,\ 0<\varepsilon<\varepsilon_0)?
\tag{16.11}
\]

式 (16.10) 已给出对应下界；固定 $d$ 的定理 (16.6) 没有给出这个统一上界。问题 (16.11) 明确区分固定维数常数与联合渐近，不将其作为已证命题或已发表具名猜想。另一项问题是，在只保证一个质量至少为 $1-\tau$ 的 $d$ 模态部分且要求目标最低态被该部分保留的模型中，求 $d,\varepsilon,\tau$ 的联合最优可辨识直径。

### 16.8 引用

[16-A] Yihong Wu and Pengkun Yang. *Optimal estimation of Gaussian mixtures via denoised method of moments*. Annals of Statistics 48(4), 1981–2007, 2020. DOI: 10.1214/19-AOS1873. https://arxiv.org/abs/1807.07237 . Proposition 1、Proposition 2、Lemma 15 和 Lemma 30 分别提供两侧稀疏与单侧稀疏矩比较、支撑多项式及交错正测度构造的成熟背景；本节不把这些方法或经典幂指数归为新发现。

[16-B] Zhiyuan Fan and Jian Li. *Efficient Algorithms for Sparse Moment Problems without Separation*. COLT 2023, PMLR 195:3510–3565. https://proceedings.mlr.press/v195/fan23b.html . 分离无关的稀疏矩算法与误差分析。
### 16.9 推论：有限支撑情形的一致次数界

设 $d\geq1$、$m,\ell\geq0$，并给定三个有限原子族

\[
x_i\in[0,1],\ u_i\geq0\quad(1\leq i\leq d),\qquad
z_j\in[0,1],\ a_j\geq0\quad(1\leq j\leq m),
\]

\[
y_r\leq b,\ v_r\geq0\quad(1\leq r\leq\ell).
\]

假设 $b\geq0$，存在指标 $i_*$ 使 $x_*=x_{i_*}>b$、$u_{i_*}\geq\eta>0$，并且

\[
\sum_{j=1}^{m}a_j\leq\tau,\qquad \varepsilon\geq0,
\]

以及对每个整数 $0\leq k\leq2d-1$ 都有

\[
\left|
\sum_{i=1}^{d}u_i x_i^k+
\sum_{j=1}^{m}a_j z_j^k-
\sum_{r=1}^{\ell}v_r y_r^k
\right|\leq\varepsilon.
\tag{16.12}
\]

这里空原子族的和取零。则

\[
\boxed{
\eta(x_*-b)^{2d-1}\leq2^{2d-1}\varepsilon+\tau.
}
\tag{16.13}
\]

**证明。** 令 $S=\{i:x_i\leq b\}$、$s=|S|$，并置

\[
q(t)=(t-b)\prod_{i\in S}(t-x_i)^2,
\qquad D=2s+1.
\]

由于 $i_*\notin S$，有 $D\leq2d-1$。多项式 $q$ 的全部 $D$ 个线性因子的根都属于 $[0,b]\subseteq[0,1]$。对保留族，若 $i\in S$，则 $q(x_i)=0$；若 $i\notin S$，则 $q(x_i)\geq0$。对比较族有 $y_r\leq b$，故 $q(y_r)\leq0$。再令 $\delta=x_*-b$，则 $0<\delta\leq1$，并且

\[
q(x_*)=(x_*-b)\prod_{i\in S}(x_*-x_i)^2\geq\delta^D.
\]

另一方面，对每个 $z_j\in[0,1]$，每个线性因子的绝对值都不超过一，所以 $|q(z_j)|\leq1$。定义有限和线性泛函

\[
L(f)=\sum_{i=1}^{d}u_i f(x_i)+
\sum_{j=1}^{m}a_j f(z_j)-
\sum_{r=1}^{\ell}v_r f(y_r).
\]

利用上述符号、$u_{i_*}\geq\eta$ 以及 $\sum_j a_j\leq\tau$，得到

\[
\eta\delta^D\leq L(q)+\tau\leq |L(q)|+\tau.
\tag{16.14}
\]

现将 $q$ 的因子按次序写成 $\prod_{h=1}^{D}(t-c_h)$，其中 $0\leq c_h\leq1$。式 (16.12) 即 $|L(t^k)|\leq\varepsilon$。逐个乘入因子，并使用

\[
|L((t-c_h)p)|\leq |L(tp)|+c_h|L(p)|,
\]

作归纳可得：只要 $j+k\leq2d-1$，前 $j$ 个因子的乘积再乘 $t^k$ 后，其 $L$ 值的绝对值不超过 $2^j\varepsilon$。取 $j=D$、$k=0$，便有

\[
|L(q)|\leq2^D\varepsilon.
\]

代入式 (16.14)，再用 $0<\delta\leq1$、$D\leq2d-1$ 与 $\varepsilon\geq0$，即得

\[
\eta\delta^{2d-1}\leq\eta\delta^D
\leq2^D\varepsilon+\tau
\leq2^{2d-1}\varepsilon+\tau.
\]


## 17. 有限观察窗口的谱底恢复与时间精度过渡

### 17.1 定义：固定最低态权重的被动观察模型

固定 $0\leq E_-<E_+<\infty$ 及 $0<\eta<1$。令 $\mathcal M$ 为支撑于 $[E_-,E_+]$ 的 Borel 概率测度 $\mu$，要求
\[
g(\mu)=\min\operatorname{supp}\mu,\qquad \mu(\{g(\mu)\})\geq\eta.
\]
令 $\mathcal M_d$ 为其中至多有 $d$ 个原子的子类。对 $T>0$，定义
\[
C_\mu(t)=\int e^{-tE}\,\mu(dE),\quad 0\leq t\leq T,
\]
以及统一绝对噪声下的确定性 minimax 误差
\[
\mathcal R_T(\varepsilon)=\inf_{\widehat g}\sup_{\mu\in\mathcal M}
\sup_{\|Y-C_\mu\|_{L^\infty[0,T]}\leq\varepsilon}
|\widehat g(Y)-g(\mu)|.
\tag{17.1}
\]
这里范数取逐点上确界，$Y$ 可为任意实值函数；估计函数不限计算复杂度。将 $\mathcal M$ 换成 $\mathcal M_d$ 得到 $\mathcal R_{d,T}$。没有对低能原子之外的支撑间距作假设。

### 17.2 定理：从原始矩构造的端点证书

设 $0\leq a<b$，$\mu,\nu$ 为概率测度，分别支撑于 $[a,\infty)$ 与 $[a,b]$，所用矩绝对可积。假设 $x_*\geq b$、$\mu(\{x_*\})\geq\eta>0$，且
\[
\left|\int x^k\,d\mu-\int x^k\,d\nu\right|\leq\delta,
\quad 0\leq k\leq n,
\qquad \delta\geq0.
\]
记
\[
Q=2\frac{2+a+b}{b-a}+1.
\]
则
\[
\boxed{2\eta n^2(x_*-b)\leq(b-a)\bigl[2(1-\eta)+\delta Q^n\bigr].}
\tag{17.2}
\]

**证明。** 使用第一类 Chebyshev 多项式 $T_0=1,T_1=z,T_{k+2}=2zT_{k+1}-T_k$。对 $z\geq1$，共同归纳两个不变量
\[
T_k(z)\geq1+k^2(z-1),\qquad
T_{k+1}(z)-T_k(z)\geq(2k+1)(z-1).
\tag{17.3}
\]
第一式在下一阶由当前两式相加得到。第二式的递推使用
\[
T_{k+2}-T_{k+1}=(T_{k+1}-T_k)+2(z-1)T_{k+1}
\]
及 $T_{k+1}(z)\geq1$。基例 $k=0$ 直接成立。

对实线性泛函 $F$，若 $|F(x^j)|\leq\delta$ 对 $j\leq n$ 成立，令 $S=|\alpha|+|\beta|$，则
\[
|F(T_n(\alpha x+\beta))|\leq\delta(2S+1)^n.
\tag{17.4}
\]
证明对次数作强归纳：泛函 $F_A(f)=F((\alpha x+\beta)f)$ 在下一阶可用的原始矩预算为 $S\delta$。递推项因此不超过
\[
2S\delta(2S+1)^{n-1}+\delta(2S+1)^{n-2}
\leq\delta(2S+1)^n.
\]
次数零、一分别由常数矩和一次矩直接处理。

现在取
\[
A(x)=\frac{2x-a-b}{b-a},\qquad p_n(x)=\frac{1+T_n(A(x))}{2}.
\]
在 $[a,b]$ 上有 $0\leq p_n\leq1$；在 $[b,\infty)$ 上有 $p_n\geq1$。由式 (17.3)，
\[
p_n(x_*)\geq1+\frac{n^2(x_*-b)}{b-a}.
\]
对 $F(f)=\int f\,d\mu-\int f\,d\nu$ 应用式 (17.4)。两测度的总质量均为一，故 $F(1)=0$，而 $S=(2+a+b)/(b-a)$。于是
\[
\eta p_n(x_*)\leq\int p_n\,d\mu
\leq\int p_n\,d\nu+\frac{\delta Q^n}{2}
\leq1+\frac{\delta Q^n}{2}.
\]
整理得到式 (17.2)。这也证明了一般测度版本；有限原子情形的积分就是实际加权幂和。

### 17.3 定理：可直接选择采样时刻的非渐近界

取整数 $n\geq1$、$T>0$，记
\[
U=E_+T,\quad u=\min\{1,U/n\},\quad h=u/E_+,
\quad K_n=64\max\{1,n/U\}.
\]
若 $\mu,\nu\in\mathcal M$ 在时刻 $0,h,\ldots,nh\subseteq[0,T]$ 上满足
\[
|C_\mu(kh)-C_\nu(kh)|\leq2\varepsilon\quad(0\leq k\leq n),
\qquad \varepsilon K_n^n\leq1,
\]
则
\[
\boxed{|g(\mu)-g(\nu)|\leq\frac{3eE_+}{\eta n^2}.}
\tag{17.5}
\]

**证明。** 推送 $x=e^{-hE}$，令 $a=e^{-u}$、$a_0=(3a-1)/2$。由于 $0<u\leq1$ 和 $e<3$，有 $0<a_0<a$。两测度的变换支撑均在 $[a,1]$。设其最大支撑点为 $y>b$，并将端点为 $y$ 的一侧作为式 (17.2) 的第一测度。比较区间选 $[a_0,b]$。它满足
\[
b-a_0\geq(1-a)/2,\qquad b-a_0\leq3(1-a)/2.
\]
对应的放大常数满足
\[
Q\leq\frac{16}{1-a}+1\leq\frac{17}{1-a}
\leq\frac{17e}{u}\leq K_n,
\]
其中 $1-e^{-u}\geq u/e$。原始矩正好是 $C(kh)$，在式 (17.2) 中使用 $\delta=2\varepsilon$，得到
\[
y-b\leq\frac{(b-a_0)(1-\eta+\varepsilon Q^n)}{\eta n^2}
\leq\frac{3(1-a)}{\eta n^2}.
\]
最后 $b\geq a\geq e^{-1}$、$1-a\leq u$，所以
\[
|g(\mu)-g(\nu)|=h^{-1}\log(y/b)
\leq\frac{y-b}{ha}\leq\frac{3eE_+}{\eta n^2}.
\]
端点相同的情形显然成立。这个结果不使用未采样时间的读数。

### 17.4 定理：具有固定端点权重的正测度下界构造

固定
\[
E_0=(E_-+E_+)/2>0,\qquad
\kappa=\min\{(E_+-E_0)/2,E_0/(4e)\}>0,
\]
并记 $A_\eta=\operatorname{arcosh}(2/\eta-1)>0$、$W_\eta=1/\eta$。
对每个奇数 $q\geq3$，存在两个各有 $(q+1)/2$ 个正原子的测度 $\mu_q,\nu_q\in\mathcal M$，使
\[
|g(\mu_q)-g(\nu_q)|\geq\frac{\kappa A_\eta^2}{4W_\eta q^2},
\tag{17.6}
\]
并且对每个 $T>0$，
\[
\boxed{\sup_{0\leq t\leq T}|C_{\mu_q}(t)-C_{\nu_q}(t)|
\leq2\left[\frac14\min\{1,E_+T/q\}\right]^q.}
\tag{17.7}
\]

**证明。** 令 $n=q-1$ 为偶数，取
\[
x_j=\frac{1+\cos(j\pi/n)}2\quad(0\leq j\leq n),\qquad
Y=\frac{1+\cosh(A_\eta/n)}2>1.
\]
设 $\ell_j$ 为节点的 Lagrange 基，$c_j=\ell_j(Y)$。乘积表达式给出 $\operatorname{sign}(c_j)=(-1)^j$；插值常数和 $T_n(2x-1)$ 分别给
\[
\sum_jc_j=1,\qquad
P:=\sum_{j\ \mathrm{even}}c_j
=\frac{1+T_n(2Y-1)}2=\frac1\eta.
\]
因此
\[
\alpha=P^{-1}\delta_Y+P^{-1}\sum_{j\ \mathrm{odd}}(-c_j)\delta_{x_j},\qquad
\beta=P^{-1}\sum_{j\ \mathrm{even}}c_j\delta_{x_j}
\]
为概率测度，匹配次数 $0,\ldots,q-1$ 的矩。二者分别在最大支撑点 $Y$ 与 $1$ 上具有质量 $\eta$ 与 $c_0/P>\eta$；后者由
\[
c_0=\prod_{j=1}^n\frac{Y-x_j}{1-x_j}>1
\]
得到。通过 $\xi=(Y-x)/Y$ 将支撑送入 $[0,1]$，最小点分别为零与 $(Y-1)/Y$。由于 $Y\leq W_\eta$ 和 $\cosh v-1\geq v^2/2$，二者端点间距至少为 $A_\eta^2/(4W_\eta q^2)$。

再推送到能量 $E=E_0+\kappa\xi$，得到所需模型和式 (17.6)。矩匹配在仿射变换下保持。对 $e^{-\kappa t\xi}$ 在 $\xi=0$ 处展开至 $q-1$ 阶，实 Taylor 余项在 $[0,1]$ 上不超过 $(\kappa t)^q/q!$。两测度的多项式项相消、总质量均为一，故
\[
|C_{\mu_q}(t)-C_{\nu_q}(t)|
\leq2e^{-E_0t}\frac{(\kappa t)^q}{q!}.
\]
分别使用 $e^{E_0t}\geq(E_0t)^q/q!$ 以及 $q!\geq(q/e)^q$，得到
\[
\sup_{0\leq t\leq T}|C_{\mu_q}(t)-C_{\nu_q}(t)|
\leq2\min\{(\kappa/E_0)^q,(e\kappa T/q)^q\}.
\]
由 $\kappa/E_0\leq1/4$、$e\kappa/E_+\leq1/4$ 得式 (17.7)。这一估计控制整个连续时间窗口。

### 17.5 定理：观察时长与噪声精度的统一匹配阶

存在仅依赖 $E_-,E_+,\eta$ 的正数 $c,C,L_0$，使对所有 $L=\log(1/\varepsilon)\geq L_0$ 和所有 $T\geq1/E_+$，有
\[
\boxed{
c\left[\frac{\log(e+L/(E_+T))}{L}\right]^2
\leq\mathcal R_T(\varepsilon)
\leq C\left[\frac{\log(e+L/(E_+T))}{L}\right]^2.
}
\tag{17.8}
\]
这些常数与 $T$ 无关。即使把模型类限制为任意有限原子数的并集，同一个匹配阶仍成立。

**上界证明。** 写 $U=E_+T\geq1$、$A=\log(e+L/U)\geq1$，取
\[
c_0=\frac1{4(1+\log64)},\qquad n=\lfloor c_0L/A\rfloor.
\]
由于 $A\leq\log(e+L)$，可选择与 $T$ 无关的 $L_0$，保证 $n\geq c_0L/(2A)\geq1$。又因 $n\leq L$，
\[
\log K_n\leq\log64+A\leq(1+\log64)A,
\qquad n\log K_n\leq L/4.
\]
因此 $\varepsilon K_n^n\leq e^{-3L/4}\leq1$。对给定数据 $Y$，考虑所有在第 17.3 节所选采样网格上与 $Y$ 相差不超过 $\varepsilon$ 的模型。任意两个相容模型之间的矩差至多为 $2\varepsilon$，其谱底距离由式 (17.5) 控制。取相容谱底集合上下确界的中点；若该集合为空，任取 $E_-$。真模型总在相容集中，所以统一误差不超过 $C A^2/L^2$。

**下界证明。** 令 $q$ 为不小于 $8L/A$ 的最小奇数。增大 $L_0$ 后有 $3\leq q\leq10L/A$。式 (17.7) 的右端不超过 $2\varepsilon$。为核对这一点，写 $r=L/U$。当 $r<1$ 时，$A<2$，故 $q\log4\geq4L$。当 $r\geq1$ 时，初等不等式
\[
\log(e+r)\leq2\sqrt r,\qquad \sqrt{e+r}\leq2\sqrt r
\]
给 $A\sqrt{e+r}\leq4r$，从而
\[
4q/U\geq32r/A\geq8\sqrt{e+r},\qquad
q\log(4\max\{1,q/U\})\geq qA/2\geq4L.
\]
两种情形下曲线距离都至多为 $2e^{-4L}\leq2\varepsilon$。两条曲线的中点同时是二者的合法观测，任意估计在至少一侧的误差不小于谱底间距的一半。式 (17.6) 和 $q\leq10L/A$ 因而给出下界。

### 17.6 推论：固定窗口的代价与足够长的窗口

对任意固定 $T>0$，有
\[
\mathcal R_T(\varepsilon)
=\Theta_{T,E_-,E_+,\eta}\left(
\frac{\log\log(1/\varepsilon)}{\log(1/\varepsilon)}\right)^2.
\tag{17.9}
\]
当 $T\geq1/E_+$ 时，这是式 (17.8) 的直接渐近结论。对固定的更小正 $T$，同一证明中 $A\sim\log L$ 以及 $L/A\to\infty$ 仍成立，允许起始阈值依赖于该 $T$，得到相同结论。

若窗口 $T=T(\varepsilon)\geq1/E_+$ 可随精度增长，则在常数因子意义下达到全时间的 $\log^{-2}(1/\varepsilon)$ 阶，当且仅当 $E_+T(\varepsilon)$ 至少为 $\log(1/\varepsilon)$ 的一个固定正常数倍。更精确地，若 $E_+T/L\to0$，式 (17.8) 的下界与 $L^{-2}$ 的比值趋于无穷；若 $E_+T\geq c_1L$，$c_1>0$，则式 (17.8) 给出匹配的 $L^{-2}$ 阶。

### 17.7 定理与问题：同时限制模态数时的联合下界

存在仅依赖 $E_-,E_+,\eta$ 的 $c>0$，使对 $d\geq1$、$0<\varepsilon<1$、$U=E_+T\geq1$，有
\[
\boxed{\mathcal R_{d,T}(\varepsilon)\geq
c\max_{1\leq m\leq d}\frac1{m^2}
\min\left\{1,\varepsilon^{1/(2m-1)}\max\{1,(2m-1)/U\}\right\}.}
\tag{17.10}
\]

**证明。** 对 $m\geq2$，在第 17.4 节的构造中取 $q=2m-1$，并将能量缩放系数 $\kappa$ 换成 $\kappa v$，其中
\[
M=\max\{1,q/U\},\qquad v=\min\{1,\varepsilon^{1/q}M\}.
\]
端点间距至少为 $c_2v/m^2$，而整个窗口的曲线差不超过
\[
2\left[\frac v4\min\{1,U/q\}\right]^q
=2(v/(4M))^q\leq2\varepsilon.
\]
中点论证给出对应风险下界。$m=1$ 用 $\delta_{E_0}$ 与 $\delta_{E_0+\kappa\varepsilon}$，因为 $U\geq1$ 时该项的 $v=\varepsilon$；由 $e^{-E_0t}(1-e^{-\kappa\varepsilon t})\leq\kappa\varepsilon/E_0$ 得相同结论。最后使用 $\mathcal M_m\subseteq\mathcal M_d$ 并对 $m$ 取最大值。

**问题。** 在同一模型类中，式 (17.10) 是否有一个常数与 $d,T$ 无关的匹配上界？式 (17.8) 已处理不限制模态数的情形，但不自动给出固定或缓慢增长的 $d$ 下的这个统一上界。还需区分：已知确切模态数、只知道模态上限、允许未排除的额外模式，以及允许正残余质量的模型。

### 17.8 引用

[17-A] NourElHouda Bourguiba and Abderrazek Karoui. *Weighted finite Laplace transform operator: spectral analysis and quality of approximation by its eigenfunctions*. Integral Transforms and Special Functions 29(9), 679–698, 2018. DOI: 10.1080/10652469.2018.1489804. https://arxiv.org/abs/1804.05207 . 有限 Laplace 算子的超指数谱衰减背景；其加权 $L^2$ 算子问题与这里固定端点原子权重的恢复风险不同。

[17-B] Cameron Musco, Christopher Musco, Lucas Rosenblatt and Apoorv Vikram Singh. *Sharper Bounds for Chebyshev Moment Matching, with Applications*. arXiv:2408.12385v3, 18 May 2026. https://arxiv.org/abs/2408.12385v3 . 含噪 Chebyshev 矩的 Wasserstein 恢复背景；本节的支撑端点泛函及有限时间观察条件单独定义。

[17-C] Zhiyuan Fan and Jian Li. *Efficient Algorithms for Sparse Moment Problems without Separation*. COLT 2023, PMLR 195:3510–3565. https://proceedings.mlr.press/v195/fan23b.html . 无分离条件的稀疏矩恢复背景。
## 18. 含噪矩极值的精确转折点与取等刚性

### 18.1 定义：初始线性上界的有效区间

沿用第 15.1 节的不同实节点 $x_1,\ldots,x_N$、离节点点 $y$、Lagrange 基 $\ell_i$、系数 $c_i=\ell_i(y)$、集合 $J=\{i:c_i>0\}$，以及
\[
p=\sum_{i\in J}\ell_i,\quad P=p(y)\geq1,\quad
L=\sum_{k=1}^{N-1}|p_k|,\quad d_0=0,\quad
 d_k=\begin{cases}1,&p_k\geq0,\\-1,&p_k<0,\end{cases}
\quad r_i=\sum_{k=0}^{N-1}d_k[\ell_i]_k.
\]
定义转折斜率、初始仿射值及候选有符号权重
\[
A_i=\frac{Pr_i}{c_i}-L,\qquad
w_\varepsilon=\frac{1+\varepsilon L}{P},\qquad
b_i(\varepsilon)=w_\varepsilon c_i-\varepsilon r_i
=\frac{c_i}{P}(1-\varepsilon A_i).
\tag{18.1}
\]
所有分母均非零。对 $\varepsilon\geq0$，称 $(w,u,v)$ 可行，是指 $w,u_i,v_i\geq0$、$w+\sum_i u_i=\sum_i v_i=1$，以及
\[
|e_k|\leq\varepsilon\quad(0\leq k<N),\qquad
e_k=wy^k+\sum_i u_ix_i^k-\sum_i v_ix_i^k.
\tag{18.2}
\]
这是两个实际概率测度的原始矩误差。两边归一化使 $e_0=0$。记最大可行外部质量为 $W(\varepsilon)$。有限维可行集闭且有界，且取 $w=0,u=v$ 可知它非空，所以最大值存在。

### 18.2 定理：取等的必要充分条件与唯一权重

假设 $p_k\neq0$ 对全部 $1\leq k<N$ 成立。对任意 $\varepsilon\geq0$，一组权重 $(w_\varepsilon,u,v)$ 可行，当且仅当
\[
\boxed{
\varepsilon A_i\leq1\quad(1\leq i\leq N),\qquad
u_i=\max\{-b_i(\varepsilon),0\},\qquad
v_i=\max\{b_i(\varepsilon),0\}.
}
\tag{18.3}
\]
因此，达到初始仿射上界的概率对唯一；转折点处出现零权重仍允许取等。此处的非零条件是对指定多项式的非恒定系数而言，不等同于一般线性规划的非退化性。

**必要性证明。** 对任意可行三元组，定义非负差额
\[
\Delta=1+\varepsilon L-wP.
\]
直接按实际矩展开，得到具有逐项非负右端的恒等式
\[
\boxed{
\Delta=\sum_i u_i p(x_i)+\sum_i v_i(1-p(x_i))
+\sum_{k=1}^{N-1}\bigl(\varepsilon|p_k|-p_ke_k\bigr).
}
\tag{18.4}
\]
非负性分别来自 $p(x_i)\in\{0,1\}$、正权重及 $|e_k|\leq\varepsilon$。当 $w=w_\varepsilon$ 时 $\Delta=0$，故每个右端项都为零。由于 $p_k\neq0$，所有非恒定矩误差被强制为
\[
e_k=\varepsilon d_k.
\tag{18.5}
\]
对实际观测差泛函作用 $\ell_i$，插值的节点取值给出
\[
wc_i+u_i-v_i=\sum_k[\ell_i]_ke_k=\varepsilon r_i,
\]
从而 $v_i-u_i=b_i(\varepsilon)$。式 (18.4) 还强制 $u_i=0$（$i\in J$）及 $v_i=0$（$i\notin J$）。结合非负性，正负部分被唯一确定，且 $b_i/c_i\geq0$。式 (18.1) 与 $P>0$ 随即给出全部 $\varepsilon A_i\leq1$。这排除了用另一组可行权重绕过初始构造的符号障碍。

**充分性证明。** 条件 $\varepsilon A_i\leq1$ 保证 $b_i$ 与 $c_i$ 同号或为零。取式 (18.3) 的正负部分，使用 Lagrange 恒等式得到
\[
\sum_i c_i=1,\quad\sum_i r_i=0,\quad
\sum_{i\in J}c_i=P,\quad\sum_{i\in J}r_i=L.
\]
于是 $\sum_i v_i=w_\varepsilon P-\varepsilon L=1$，而 $\sum_i(v_i-u_i)=w_\varepsilon$，所以另一侧也归一化。对每个 $k<N$，插值给出 $\sum_i c_ix_i^k=y^k$ 和 $\sum_i r_ix_i^k=d_k$，故实际误差就是 $\varepsilon d_k$。这证明可行性，包括边界零权重。$N=1$ 时条件为空，结论退化为唯一的 $w=1,u=0,v=1$。

### 18.3 推论：精确第一转折点

若 $N\geq2$ 且第 18.2 节的系数条件成立，则 $L>0$，并且
\[
M=\max_i A_i>0,\qquad \varepsilon_*=\frac1M
\tag{18.6}
\]
满足
\[
W(\varepsilon)=\frac{1+\varepsilon L}{P}\quad(0\leq\varepsilon\leq\varepsilon_*),
\qquad
W(\varepsilon)<\frac{1+\varepsilon L}{P}\quad(\varepsilon>\varepsilon_*).
\tag{18.7}
\]

**证明。** 式 (18.4) 对所有可行对给出 $wP\leq1+\varepsilon L$。若全部 $A_i\leq0$，式 (18.3) 会对任意大 $\varepsilon$ 构造可行的 $w_\varepsilon$；但 $L>0$ 会使 $w_\varepsilon>1$，与概率归一化矛盾。因此 $M>0$。当 $0\leq\varepsilon\leq1/M$ 时，式 (18.3) 构造取等。超过该阈值时至少一个条件失败，而必要性排除了所有取等概率对。由于最大值确实取得，故为严格不等式。第 15.2 节的 $1/[2P(1+B)]$ 是有效的充分半径；式 (18.6) 给出此系数条件下的精确半径。

### 18.4 命题：近最优概率对的定量刚性

在第 18.2 节的系数条件下，设 $(w,u,v)$ 任意可行，不要求已经取等。令 $\Delta$ 如式 (18.4)，并定义
\[
b_i(w,\varepsilon)=wc_i-\varepsilon r_i,
\qquad B_i=\sum_{k=1}^{N-1}\frac{|[\ell_i]_k|}{|p_k|}.
\]
则
\[
|e_k-\varepsilon d_k|\leq\frac{\Delta}{|p_k|}\quad(1\leq k<N),
\tag{18.8}
\]
且对每个节点有
\[
\boxed{
|u_i-\max\{-b_i(w,\varepsilon),0\}|\leq\Delta(1+B_i),\qquad
|v_i-\max\{b_i(w,\varepsilon),0\}|\leq\Delta(1+B_i).
}
\tag{18.9}
\]

**证明。** 式 (18.4) 中每个非负项均不超过 $\Delta$。在 $|e_k|\leq\varepsilon$ 下，系数项恰好等于 $|p_k|\,|e_k-\varepsilon d_k|$，得到式 (18.8)。对 $\ell_i$ 展开实际误差并用三角不等式，得
\[
|(v_i-u_i)-b_i(w,\varepsilon)|\leq\Delta B_i.
\]
若 $p(x_i)=1$，则 $u_i\leq\Delta$；否则 $v_i\leq\Delta$。故 $\min\{u_i,v_i\}\leq\Delta$。使用
\[
u_i=\max\{-(v_i-u_i),0\}+\min\{u_i,v_i\},\quad
v_i=\max\{v_i-u_i,0\}+\min\{u_i,v_i\}
\]
及实正部分函数的 1-Lipschitz 性得到式 (18.9)。该估计把最优值差额变成实际权重误差；其条件数包含 $1/|p_k|$，因此不能无条件跨越系数趋零的情形。

### 18.5 命题：三节点模型在所有噪声水平下的完整解

取 $x=(1/4,1/2,3/4)$、$y=1$。则
\[
p=4-16X+16X^2,\quad P=4,\quad L=32,\quad
c=(1,-3,3),\quad r=(18,-32,14),\quad
A=(40,32/3,-40/3).
\]
因此精确第一转折点为 $1/40$。对全部 $\varepsilon\geq0$，
\[
\boxed{W(\varepsilon)=\min\left\{
\tfrac14+8\varepsilon,\quad
\tfrac13+\tfrac{14}3\varepsilon,\quad
\tfrac8{15}+\tfrac{16}{15}\varepsilon,\quad 1\right\}.}
\tag{18.10}
\]
四段的转折依次为 $1/40,1/18,7/16$。

**上界证明。** 三个多项式
\[
p_1=4-16X+16X^2,\qquad p_2=1-6X+8X^2,\qquad p_3=2X^2-\tfrac18
\]
在三个节点上的值均属于 $[0,1]$。它们在 $y=1$ 处的值分别为 $4,3,15/8$，非恒定系数绝对值和分别为 $32,14,2$。将各自代入式 (18.4) 所对应的多项式上界，再使用 $w\leq1$，得到式 (18.10) 的四条直线。

**取等构造。** 当 $0\leq\varepsilon\leq1/40$ 时，使用式 (15.7)。当 $1/40\leq\varepsilon\leq1/18$ 时，取
\[
w=\tfrac13+\tfrac{14}3\varepsilon,\quad
\mu=w\delta_1+\tfrac{40\varepsilon-1}{3}\delta_{1/4}
 +(1-18\varepsilon)\delta_{1/2},\quad \nu=\delta_{3/4}.
\]
两组误差为 $(-\varepsilon,\varepsilon)$。当 $1/18\leq\varepsilon\leq7/16$ 时，取
\[
w=\tfrac8{15}+\tfrac{16}{15}\varepsilon,\quad
\mu=w\delta_1+(1-w)\delta_{1/4},\quad\nu=\delta_{3/4}.
\]
误差为 $((8\varepsilon-1)/10,\varepsilon)$，其绝对值均不超过 $\varepsilon$。最后当 $\varepsilon\geq7/16$，取 $\mu=\delta_1,\nu=\delta_{3/4}$，误差为 $(1/4,7/16)$。各段内权重非负且归一化，在端点处相容，因此证明全部区间的取等。

### 18.6 命题与后续问题：零系数产生的自由噪声面

若允许部分 $p_k=0$，定义紧凸集合
\[
\mathcal D_p=\{d\in\mathbb R^N:d_0=0,\ |d_k|\leq1,\
 d_k=\operatorname{sign}(p_k)\text{ whenever }p_k\neq0,\ 1\leq k<N\}.
\]
对 $d\in\mathcal D_p$ 定义 $r_i(d)=\sum_kd_k[\ell_i]_k$、$A_i(d)=Pr_i(d)/c_i-L$。则 $w_\varepsilon=(1+\varepsilon L)/P$ 可行，当且仅当存在 $d\in\mathcal D_p$ 满足
\[
\varepsilon A_i(d)\leq1\quad\text{对所有 }i.
\tag{18.11}
\]
若 $L>0$，其精确第一取等区间为 $[0,1/M_*]$，其中
\[
\boxed{M_* = \min_{d\in\mathcal D_p}\max_i A_i(d)>0.}
\tag{18.12}
\]

**证明。** 当 $\varepsilon>0$ 且存在取等概率对时，令 $d_k=e_k/\varepsilon$。式 (18.4) 强制所有非零系数上的饱和，零系数保留 $[-1,1]$ 自由度。逐个作用 $\ell_i$ 和节点互补性后得到式 (18.11)。反向对指定的 $d$ 使用第 18.2 节的正负部分构造；所需恒等式 $D(p)=L$ 不依赖零系数处的选择。$\varepsilon=0$ 时直接使用零噪声构造。若某个 $d$ 的全部 $A_i(d)\leq0$，该方向会让仿射值在任意大噪声下可行，与 $L>0$ 及 $w\leq1$ 矛盾。连续函数 $\max_i A_i(d)$ 在紧集上取得严格正最小值，给出式 (18.12)。这个最小化是一个固定节点下的有限线性规划。

第 18.2 节给出非零系数下的精确分类。第 18.4--18.6 节给出定量近最优性、三节点完整曲线和零系数面；它们尚未合并为处理后续支撑变化的通用算法。下一项具体问题是式 (18.11) 的自由面及其构造性求解，以及这些面在节点数增加时如何影响有限观察的最坏谱端点界。维数、时长和精度的联合 minimax 上界仍未由本节证明。

### 18.7 文献定位

[18-A] Yohann de Castro and Fabrice Gamboa. *Exact Reconstruction Using Beurling Minimal Extrapolation*. Journal of Mathematical Analysis and Applications 395(1), 336--354, 2012. arXiv:1103.4951. https://arxiv.org/abs/1103.4951 . 提供有限测度矩重建与插值、多项式对偶的背景；本节单独计算含噪极值的精确取等面。

[18-B] Milan Hladík. *Linear programming sensitivity measured by the optimal value worst-case analysis*. Optimization Methods and Software 39(5), 1168--1184, 2024. DOI: 10.1080/10556788.2024.2329590. https://doi.org/10.1080/10556788.2024.2329590 . 讨论线性规划最优值对区间数据扰动的敏感性及一般退化情形的未解决复杂度问题。本节只涉及固定节点矩阵、固定目标及坐标误差预算，非零多项式系数条件也不同于一般 LP 非退化性；不据此宣称解决该文的一般开放问题。

## 追加锚（本行以下为增补区）
## 19. 两矩连续支撑极值、网格偏差与最优节点配置

### 19.1 定义：两组概率分布的含噪矩比较

固定 $0\leq a<b<1$。令 $\mu,\nu$ 为 Borel 概率测度，满足
\[
\operatorname{supp}\mu\subseteq[a,1],\qquad
\operatorname{supp}\nu\subseteq[a,b],\qquad
\left|\int x^k\,d\mu-\int x^k\,d\nu\right|\leq\varepsilon
\quad(k=1,2),\quad\varepsilon\geq0.
\tag{19.1}
\]
定义 $W(\varepsilon)$ 为全部可行对中的最大 $\mu(\{1\})$。对开区间 $(l,r)\subset[a,1)$，再要求 $\mu((l,r))=0$，得到最大值 $W_{l,r}(\varepsilon)$。下面给出的上界对任意上述测度成立，且由有限原子测度取得，所以将模型类限制为任意有限原子数的并集不改变这些最大值。

此处 $\varepsilon$ 比较两种真实模型的矩。若它们分别与同一读数相差至多 $\delta$，则应使用 $\varepsilon=2\delta$。当 $a>0$、$x=e^{-hE}$ 且 $h>0$ 时，两矩分别对应 $h,2h$ 时刻的 Laplace 读数。式 (19.1) 没有假设其他时间的读数相近。一般矩极值的多项式对偶背景见 [19-A]。

### 19.2 定理：移动原子的精确极值与支撑空隙代价

设
\[
a\leq l<r\leq b,\qquad l\leq t\leq r,\qquad
2t\leq a+b,\qquad l+r\leq a+b.
\]
定义
\[
\varepsilon(t)=\frac{(1-b)(b-t)}{2+t},\quad
c(t)=\frac{(1-b)(2+b)}{2+t},\quad
w_c(t)=1-\frac{c(t)}{1-t},
\]
\[
w_h(t;l,r)=\frac{(b-l)(b-r)+\varepsilon(t)(1+l+r)}{(1-l)(1-r)}.
\tag{19.2}
\]
则
\[
\boxed{W(\varepsilon(t))=w_c(t),\qquad
W_{l,r}(\varepsilon(t))=w_h(t;l,r),}
\]
并且
\[
\boxed{w_c(t)-w_h(t;l,r)
=\frac{(1-w_c(t))(t-l)(r-t)}{(1-l)(1-r)}.}
\tag{19.3}
\]
当 $l<t<r$ 时差严格为正；在两个端点处差为零。

**构造。** 无空隙时取
\[
\mu_c=w_c\delta_1+(1-w_c)\delta_t,\qquad\nu_c=\delta_b.
\tag{19.4}
\]
有空隙时取
\[
\mu_h=w_h\delta_1+u_l\delta_l+u_r\delta_r,\qquad\nu_h=\delta_b,
\]
\[
u_l=\frac{c(t)(r-t)}{(1-l)(r-l)},\qquad
u_r=\frac{c(t)(t-l)}{(1-r)(r-l)}.
\tag{19.5}
\]
这里式 (19.5) 的 $u_l,u_r$ 为残余概率质量。所有分母为正，$u_l,u_r\geq0$，而
\[
w_c=\frac{(b-t)(1+b+t)}{(1-t)(2+t)}\geq0,\qquad
1-w_c=\frac{(1-b)(2+b)}{(1-t)(2+t)}>0.
\]
式 (19.2) 给 $w_h\geq0$。直接代入得到
\[
w_h+u_l+u_r=1,
\]
\[
\int x\,d(\mu_c-\nu_c)=\int x\,d(\mu_h-\nu_h)=-\varepsilon(t),\qquad
\int x^2\,d(\mu_c-\nu_c)=\int x^2\,d(\mu_h-\nu_h)=\varepsilon(t).
\tag{19.6}
\]
因此两组都是实际可行概率对。

**普遍上界。** 记任意可行对的误差为 $e_1,e_2$。对 $q(x)=x^2-sx+p$，$s\geq0$，若 $q$ 在 $\mu$ 的残余支撑上非负，并且在 $[a,b]$ 上不超过 $B$，则归一化与实际矩误差给出
\[
\mu(\{1\})q(1)\leq\int q\,d\mu
=\int q\,d\nu+e_2-se_1\leq B+\varepsilon(1+s).
\tag{19.7}
\]
取 $q_c(x)=(x-t)^2$。在 $[a,b]$ 上，
\[
q_c(b)-q_c(x)=(b-x)(b+x-2t)\geq0,
\]
所以 $B=(b-t)^2$。式 (19.7) 的上界由 (19.4) 取得，给出 $W=w_c$。

取 $q_h(x)=(x-l)(x-r)$。它在 $(l,r)$ 之外非负，而
\[
q_h(b)-q_h(x)=(b-x)(b+x-l-r)\geq0\quad(a\leq x\leq b).
\]
式 (19.7) 的上界由 (19.5) 取得，给出 $W_{l,r}=w_h$。最后，(19.4) 与 (19.5) 具有相同前两矩及总质量，故对 $q_h$ 积分相同。于是
\[
w_hq_h(1)=w_cq_h(1)+(1-w_c)q_h(t),
\]
即为式 (19.3)。严格性来自 $1-w_c>0$ 及区间内部的两个正因子。

### 19.3 定理：连续支撑模型的完整噪声曲线

记
\[
m=\frac{a+b}{2},\quad h=\frac{b-a}{2},\quad
\varepsilon_1=\frac{(1-b)(b-a)}{4+a+b},\quad
\varepsilon_2=\frac{(1-b)(b-a)}{2+a},\quad
\varepsilon_3=1-b^2.
\]
有 $0<\varepsilon_1<\varepsilon_2<\varepsilon_3$，且对全部 $\varepsilon\geq0$，
\[
\boxed{
W(\varepsilon)=
\begin{cases}
\dfrac{h^2+\varepsilon(1+2m)}{(1-m)^2},&0\leq\varepsilon\leq\varepsilon_1,\\[4pt]
\dfrac{\varepsilon(1+2b)-\varepsilon^2}{(1-b)^2+3\varepsilon},&\varepsilon_1\leq\varepsilon\leq\varepsilon_2,\\[4pt]
\dfrac{b^2-a^2+\varepsilon}{1-a^2},&\varepsilon_2\leq\varepsilon\leq\varepsilon_3,\\[4pt]
1,&\varepsilon\geq\varepsilon_3.
\end{cases}}
\tag{19.8}
\]
相邻表达式在转折点相等。

**证明。** 第一段使用 $q=(x-m)^2$，它在比较支撑上的最大值为 $h^2$，故式 (19.7) 给出上界。取
\[
\mu=W\delta_1+(1-W)\delta_m,\qquad
\nu=\lambda\delta_a+(1-\lambda)\delta_b,
\]
\[
\lambda=\frac{(1-b)(b-a)-\varepsilon(4+a+b)}{(b-a)(2-a-b)}.
\tag{19.9}
\]
在该区间内 $0\leq\lambda\leq1$。$W$ 从非负值线性增长到式 (19.4) 在 $t=m$ 时小于一的值，故 $0\leq W<1$。两矩误差为 $(-\varepsilon,\varepsilon)$，得到取等。

第二段将式 (19.2) 反解为
\[
t(\varepsilon)=\frac{b(1-b)-2\varepsilon}{1-b+\varepsilon}.
\tag{19.10}
\]
这个函数严格递减，将 $[\varepsilon_1,\varepsilon_2]$ 映到 $[a,m]$，端点分别为 $m,a$。将其代入 (19.4) 得到式 (19.8) 的第二段，普遍上界用 $q=(x-t)^2$。该上界不依赖提前指定残余节点。

第三段使用 $q=x^2-a^2$，其在 $[a,1]$ 上非负、在 $[a,b]$ 上不超过 $b^2-a^2$。取
\[
\mu=W\delta_1+(1-W)\delta_a,\qquad\nu=\delta_b.
\]
此时二次矩误差为 $\varepsilon$，一次矩误差为
\[
e_1=\frac{\varepsilon-(1-b)(b-a)}{1+a}.
\]
条件 $\varepsilon\geq\varepsilon_2$ 保证 $e_1\geq-\varepsilon$，而 $a\geq0$ 保证 $e_1\leq\varepsilon$；$\varepsilon\leq\varepsilon_3$ 保证 $W\leq1$。最后一段取 $\mu=\delta_1,\nu=\delta_b$，误差为 $(1-b,1-b^2)$，两者均不超过 $\varepsilon_3$。这证明了所有区间的上界、取等与转折。

### 19.4 推论：固定网格的严格偏差及一个精确反例

设固定有限网格 $G\subset[a,b]$ 包含 $a,m,b$。将 $\mu$ 的残余支撑和 $\nu$ 的支撑都限制在 $G$，记最大端点质量为 $W_G(\varepsilon)$。若 $\varepsilon\in(\varepsilon_1,\varepsilon_2)$ 且 $t=t(\varepsilon)\notin G$，令 $l<r$ 为夹住 $t$ 的相邻网格节点。因为 $m\in G$，有 $a\leq l<t<r\leq m$。式 (19.5) 的全部节点属于允许支撑，且 $G\cap(l,r)=\varnothing$，故
\[
\boxed{W_G(\varepsilon)=w_h(t;l,r),\qquad
W(\varepsilon)-W_G(\varepsilon)
=\frac{(1-W(\varepsilon))(t-l)(r-t)}{(1-l)(1-r)}>0.}
\tag{19.11}
\]
若 $t\in G$，式 (19.4) 给出零偏差。因此有限网格在这个整个开噪声区间中只能于有限多个噪声值精确。有限原子取等不蕴含一个预先固定的有限节点集合足够。

对 $a=1/4,b=3/4,G=\{1/4,1/2,3/4\}$ 和 $\varepsilon=1/25$，
\[
t=\frac{43}{116},\quad W=\frac{984}{1825},\quad W_G=\frac{13}{25},\quad
W-W_G=\frac7{365}.
\tag{19.12}
\]
连续模型的取等分布为
\[
\mu=\frac{984}{1825}\delta_1+\frac{841}{1825}\delta_{43/116},\qquad
\nu=\delta_{3/4}.
\]
两矩误差恰为 $(-1/25,1/25)$。在整个中间区间 $1/40\leq\varepsilon\leq1/18$，网格偏差为
\[
W-W_G=\frac{(1-18\varepsilon)(40\varepsilon-1)}{3(48\varepsilon+1)}.
\tag{19.13}
\]
该比较保持了固定网格问题本身的正确性，只改变允许的支撑模型类。

### 19.5 定理：每个网格单元的精确最坏偏差

令 $K=(1-b)(2+b)>0$，并定义严格递增坐标
\[
\psi(t)=\sqrt{\frac{2+t}{1-t}},\qquad 0\leq t<1.
\]
对任意 $a\leq l<r\leq m$，在 $t\in[l,r]$ 对应的噪声段内，式 (19.11) 的最大偏差恰为
\[
\boxed{\max_{l\leq t\leq r}(w_c-w_h)
=\frac K9\bigl(\psi(r)-\psi(l)\bigr)^2.}
\tag{19.14}
\]
最大值在
\[
t_* =\frac{\psi(l)\psi(r)-2}{\psi(l)\psi(r)+1}\in(l,r)
\]
取得。

**证明。** 令 $s=(2+t)/(1-t)$、$s_l=(2+l)/(1-l)$、$s_r=(2+r)/(1-r)$。将式 (19.3) 中的 $1-w_c=K/[(2+t)(1-t)]$ 代入，精确化为
\[
w_c-w_h=\frac K9\frac{(s-s_l)(s_r-s)}s
=\frac K9\left(s_l+s_r-s-\frac{s_ls_r}s\right).
\]
对 $s>0$，
\[
s+\frac{s_ls_r}s-2\sqrt{s_ls_r}
=\frac{(s-\sqrt{s_ls_r})^2}s\geq0.
\]
因此在 $s=\sqrt{s_ls_r}=\psi(l)\psi(r)$ 处取得且仅取得最大值。该点严格位于两端之间，反变换给出 $t_*$，而最大值为式 (19.14)。

### 19.6 定理：保留校准节点的最优有限网格

固定整数 $M\geq1$，考虑所有网格
\[
G=\{g_0,g_1,\ldots,g_M,b\},\qquad
a=g_0<g_1<\cdots<g_M=m.
\]
这类网格保留 $a,m,b$ 三个校准节点，并允许在 $[a,m]$ 内选择 $M-1$ 个附加节点。则
\[
\boxed{\inf_G\sup_{\varepsilon\geq0}\bigl(W(\varepsilon)-W_G(\varepsilon)\bigr)
=\frac{(1-b)(2+b)}{9M^2}\bigl(\psi(m)-\psi(a)\bigr)^2.}
\tag{19.15}
\]
唯一最优的有序节点由
\[
\psi_j=\psi(a)+\frac jM\bigl(\psi(m)-\psi(a)\bigr),\qquad
\boxed{g_j=\frac{\psi_j^2-2}{\psi_j^2+1}\quad(0\leq j\leq M)}
\tag{19.16}
\]
给出。

**证明。** 式 (19.9) 和第三、四阶段的取等分布只使用 $a,m,b,1$，所以所有这些网格在移动阶段之外都精确。移动阶段内，式 (19.14) 给出
\[
\sup_{\varepsilon\geq0}(W-W_G)
=\frac K9\max_{0\leq j<M}\bigl(\psi(g_{j+1})-\psi(g_j)\bigr)^2.
\]
$M$ 个正增量之和固定为 $\psi(m)-\psi(a)$，其最大值至少为该和除以 $M$。等号成立当且仅当全部增量相等，得到式 (19.15)--(19.16)。这是固定有限 $M$ 下的精确最优值，因而也给出 $M^{-2}$ 误差阶。节点数预算和保留校准节点的条件是结论的一部分；未要求保留这些节点的更大设计类没有在此被优化。

### 19.7 范围与下一项问题

Lean 定理 `TwoMomentSupportHole.two_moment_support_hole_sharp` 对任意有限原子数的真实 Prony 矩给出第 19.2 节的两项最大值及精确差额；其证明包含移动原子与双端残余的正权重构造和普遍上界。第 19.3--19.6 节的完整分段曲线、固定网格结论和最佳网格配置在本节有普通证明，尚未作为新的 Lean 声明完成。一般 Borel 测度版本由相同有界多项式积分论证给出。

接下来的具体问题是：对三阶及更高阶含噪矩，是否能得到类似的支撑移动分类、可认证的网格误差和全局最佳节点配置？更一般的自由节点一致逼近仍有独立的最优性问题 [19-C]，本节只解决由指定两矩极值诱导、且保留校准节点的设计类。它不结算一般自由节点样条问题，也不证明维数、时长与精度的联合谱底 minimax 上界。

### 19.8 文献定位

[19-A] Dimitris Bertsimas and Ioana Popescu. *Optimal Inequalities in Probability Theory: A Convex Optimization Approach*. SIAM Journal on Optimization 15(3), 780--804, 2005. DOI: 10.1137/S1052623401399903. https://epubs.siam.org/doi/10.1137/S1052623401399903 . 一般矩约束下紧概率界及多项式优化的背景；不把二次证书或矩对偶方法本身归为本节新发现。

[19-B] Ken'ichiro Tanaka and Alexis Akira Toda. *Discretizing Distributions with Exact Moments: Error Estimate and Convergence Analysis*. SIAM Journal on Numerical Analysis 53(5), 2158--2177, 2015. DOI: 10.1137/140971269. https://epubs.siam.org/doi/10.1137/140971269 . 研究矩保持离散化的误差与收敛；其给定分布的近似问题与本节两种可变测度间的最坏端点质量问题不同。

[19-C] Vinesha Peiris, Nadezda Sukhorukova and Duy Khoa Pham. *Best free knot linear spline approximation and its application to neural networks*. IMA Journal of Applied Mathematics 91(3), 273--292, June 2026. DOI: 10.1093/imamat/hxag015. https://academic.oup.com/imamat/advance-article/doi/10.1093/imamat/hxag015/8706326 . 研究一般自由节点一致逼近，给出单内部节点的优化与充分最优性条件。这里的有限网格公式针对特殊矩极值曲线的受限设计类，不替代该文的一般问题。

## 20. 鸽笼平均界、嵌套网格与逐次加点的精确代价

### 20.1 定义与命题：按误差坐标分配有限区间

沿用第 19 节的 $0\leq a<b<1$、$m=(a+b)/2$、$K=(1-b)(2+b)$ 和 $\psi(t)=\sqrt{(2+t)/(1-t)}$。记
\[
L=\psi(m)-\psi(a)>0,\qquad A=KL^2/9>0.
\]
对校准网格 $G=\{a=g_0<\cdots<g_M=m,b\}$，其中 $M\geq1$，定义归一化区间长度
\[
p_j=\frac{\psi(g_{j+1})-\psi(g_j)}L\quad(0\leq j<M),\qquad D(G)=\max_jp_j.
\]
这些数严格为正且总和为一。第 19.4--19.6 节的实际两矩极值证明给出
\[
\mathcal E(G):=\sup_{\varepsilon\geq0}\bigl(W(\varepsilon)-W_G(\varepsilon)\bigr)=A D(G)^2.
\tag{20.1}
\]
因此
\[
D(G)\geq1/M,\qquad \mathcal E(G)\geq A/M^2,
\tag{20.2}
\]
等号成立当且仅当全部 $p_j=1/M$。

**证明。** 若每个 $p_j<1/M$，求和将严格小于一。若每个 $p_j\leq1/M$ 且有一项严格小于，则总和同样严格小于一。因此最大值至少为平均值，而达到平均值时全部相等。这是有限实权重的鸽笼平均论证 [20-A]。式 (20.1) 依赖此前构造的真实正测度与精确单元代价；鸽笼论证自身不提供变换 $\psi$，也不构造不可辨识的谱测度。

### 20.2 命题：近最优网格在变换坐标中的稳定性

若 $\rho\geq0$ 且 $\mathcal E(G)\leq(1+\rho)A/M^2$，令 $q=\sqrt{1+\rho}-1$，则
\[
\sum_{j=0}^{M-1}(p_j-1/M)^2\leq\frac qM.
\tag{20.3}
\]
对每个 $0\leq j\leq M$，还满足
\[
-\frac{(M-j)q}{M}\leq
\frac{\psi(g_j)-\psi(a)}L-\frac jM
\leq\frac{jq}{M}.
\tag{20.4}
\]

**证明。** 式 (20.1) 给每个 $p_j\leq(1+q)/M$，故 $\sum p_j^2\leq(\max p_j)\sum p_j\leq(1+q)/M$。展开平方和得到式 (20.3)。对前 $j$ 个长度分别求和得到式 (20.4) 的上界，对其余 $M-j$ 个求和再从一中减去得到下界。$q=0$ 恢复唯一最优网格。本节给出有效的定量界，不宣称每个稳定性常数均尖锐。

### 20.3 定义与定理：保留旧节点的真实细分历史

一个嵌套校准历史是网格族 $G_M$，$M\geq1$，满足 $G_1=\{a,m,b\}$，并且每次只在 $[a,m]$ 中某个已有开单元加入一个新节点，旧节点永不移动或删除。在归一化的 $\psi$ 坐标中，这等价于从长度列表 $[1]$ 开始，每步将一个正长度 $\ell_k$ 分成 $\alpha_k\ell_k$ 和 $(1-\alpha_k)\ell_k$，其中 $0<\alpha_k<1$。第 $M$ 阶段有 $M$ 个正单元，总长为一。记它们为 $p_{M,j}$，最大长度为 $D_M$，并定义
\[
H_M=-\sum_{j=1}^M p_{M,j}\ln p_{M,j},\qquad
h(\alpha)=-\alpha\ln\alpha-(1-\alpha)\ln(1-\alpha).
\]
对任意这样的历史，定义逐步损失
\[
z_k=(D_k-\ell_k)\ln2+\ell_k\bigl(\ln2-h(\alpha_k)\bigr)\geq0.
\tag{20.5}
\]
则对每个 $M\geq1$ 有有限历史界
\[
\boxed{\ln(1/D_M)+\sum_{k=1}^{M-1}z_k
\leq\ln2\sum_{k=1}^{M-1}D_k.}
\tag{20.6}
\]
第一部分损失记录没有选择最大单元，第二部分记录分裂比例偏离一半。

**证明。** 分裂的两个子长度之和等于父长度，所以由历史归纳得到始终正且总长为一。逐项展开对数，未改变的单元全部抵消，得到真实熵增
\[
H_{k+1}-H_k=\ell_k h(\alpha_k).
\]
二元熵满足 $h(\alpha)\leq\ln2$ [20-B]，父单元长度也满足 $\ell_k\leq D_k$，所以式 (20.5) 非负。由于 $H_1=0$，精确求和给出
\[
H_M+\sum_{k=1}^{M-1}z_k=\ln2\sum_{k=1}^{M-1}D_k.
\]
另一方面，每个 $p_{M,j}\leq D_M$，对数单调性及总长一给出
\[
H_M\geq-\sum_jp_{M,j}\ln D_M=\ln(1/D_M).
\]
两式合并即得式 (20.6)。Lean 定理 `NestedGridEntropy.binary_refinement_entropy_budget` 从实际列表替换恒等式推导该链条，并允许用每阶段任意合法上界代替精确最大单元。定理以零次分裂对应 $M=1$；没有把熵增或最终熵下界放入假设。

### 20.4 定理：嵌套历史的严格额外代价

每个嵌套历史都满足
\[
\boxed{\limsup_{M\to\infty} M D_M\geq\frac1{\ln2}.}
\tag{20.7}
\]

**证明。** 假设存在 $c<1/\ln2$ 和 $M_0$，使所有 $M\geq M_0$ 都有 $D_M\leq c/M$。因为 $D_M>0$，可以取 $c>0$。丢掉式 (20.6) 中的非负损失，有限个初始阶段的贡献记入常数 $B$，得到
\[
\ln M-\ln c\leq \ln(1/D_M)
\leq B+c\ln2\sum_{k=M_0}^{M-1}\frac1k
\leq B+c\ln2(1+\ln M).
\]
由于 $1-c\ln2>0$，这对任意大 $M$ 不可能成立。因此对每个 $c<1/\ln2$ 都有任意晚的阶段满足 $MD_M>c$，得到式 (20.7)。这条证明区分了单个阶段的平均界与整条历史受到的约束。

### 20.5 构造：达到下界的经典对数细分

定义正长度
\[
\ell_j=\frac{\ln((j+1)/j)}{\ln2}\quad(j\geq1).
\tag{20.8}
\]
从标签为一、长度为 $\ell_1=1$ 的单元开始。当有 $M$ 个单元时，选择标签为 $M$ 的单元，以固定左右次序分成标签 $2M$ 与 $2M+1$ 的两段。恒等式
\[
\ell_{2M}+\ell_{2M+1}=\ell_M
\]
保证这是保持旧边界的合法二分。归纳可知第 $M$ 阶段的标签集恰为 $\{M,M+1,\ldots,2M-1\}$。由于 $\ell_j$ 随 $j$ 严格递减，此时
\[
\boxed{D_M=\ell_M=\frac{\ln(1+1/M)}{\ln2},\qquad
MD_M<\frac1{\ln2},\qquad MD_M\longrightarrow\frac1{\ln2}.}
\tag{20.9}
\]
最后两个结论来自 $\ln(1+x)<x$ 以及 $\ln(1+x)/x\to1$。

这一空间分割还可显式给出。标签 $j$ 若满足 $2^q\leq j<2^{q+1}$，其对应区间为
\[
[\log_2j-q,\ \log_2(j+1)-q].
\]
它的两个孩子具有相同外边界，内部新增点为 $\{\log_2(2j+1)\}$。因此，第 $j$ 次插入的归一化坐标是
\[
s_j=\{\log_2(2j+1)\}\quad(j\geq1).
\tag{20.10}
\]
这正是 Niederreiter 的经典低离散度对数序列，在已放置零端点后重新编号；Weiss 的论文明确给出其历史归属及精确间隔结构 [20-C,20-D]。此处不将该序列或常数 $1/\ln2$ 归为新的数论发现。上述标签证明说明该构造确实是一条保留全部旧节点的历史。

### 20.6 定理：实际两矩误差的最佳全程倍率

令 $\mathcal E_M^*=A/M^2$ 为单独给定 $M$ 时允许重新布点的最优误差。对全部嵌套校准历史，有
\[
\boxed{
\inf_{(G_M)\,\mathrm{nested}}\sup_{M\geq1}
\frac{\mathcal E(G_M)}{\mathcal E_M^*}
=\frac1{(\ln2)^2}=2.081368981\ldots.
}
\tag{20.11}
\]
将上确界换成 $M\to\infty$ 的上极限，最优值相同。

**证明。** 式 (20.1) 使每阶段比值精确等于 $(MD_M)^2$。式 (20.7) 给出所有历史的下界。将式 (20.10) 的新增点送回原始支撑坐标，取
\[
v_j=\psi(a)+Ls_j,\qquad g^{\mathrm{new}}_j=\frac{v_j^2-2}{v_j^2+1},
\]
并始终保留 $a,m,b$。这给出合法的嵌套校准网格，式 (20.9) 给所有有限阶段的比值严格小于 $1/(\ln2)^2$，而极限恰好等于该值，所以它的上确界取得所需最优值。

对照地，每次在最大归一化单元的中点插入，若 $2^q\leq M<2^{q+1}$，则 $D_M=2^{-q}$。因此此常用二分策略的全程倍率上确界为四。每次二等分最大化当前父单元的熵增，但不保证所有未来节点预算上的最大单元最小。单次均匀网格与逐次保留旧点的最优性是两个不同的量词问题。

更简单地，$M$ 等分网格包含在 $N$ 等分网格中，当且仅当 $M$ 整除 $N$：必要性由节点 $1/M$ 必须等于某个 $k/N$ 得到，充分性直接逐节点验证。故 $2$ 等分到 $3$ 等分已经排除了每个相邻预算都保持单次唯一最优的可能。式 (20.11) 给出这项不相容性的精确全程误差代价。

### 20.7 形式化范围与后续问题

Lean 已证明第 20.3 节的实际二分历史熵预算，包括显式非负损失。静态平均界直接复用既有数学，不另增包装定理。第 20.2、20.4--20.6 节在此给出普通证明；完整上极限推导、经典对数序列的空间实现和它与第 19 节的实际矩极值之间的形式化连接仍需各自完成。普通推导不属于 Lean 内核已验证的结论。

本节回答了指定两矩模型中保留校准节点、一次只加一点时的最佳全程倍率。它不证明此前的维数、时长与噪声联合 minimax 上界，不宣称解决外部具名开放猜想。更高阶矩下还需从真实极值构造判断是否存在能将单元代价化为长度幂的坐标；只有建立该联系，经典分割序列才能提供相应的实际误差保证。

### 20.8 来源

[20-A] Mathlib, `Mathlib/Combinatorics/Pigeonhole.lean`. https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Pigeonhole.html . 有限权重鸽笼及平均值形式的已有基础。

[20-B] Mathlib, commit `db584cd6d46c92f209a44c0f1c829460d327499d`, `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`, `Real.binEntropy_le_log_two` 与 `Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub`. https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean . Lean 定理调用的二元熵基础。

[20-C] Christian Weiss. *An Explicit non-Poissonian Pair Correlation Function*. arXiv:2304.14202v3, 16 June 2026. https://arxiv.org/html/2304.14202v3 . Introduction 与 Proposition 2.1 给出经典低离散度对数序列的归属与间隔结构。本节只使用并重新证明所需间隔结构，不使用该文的成对相关主定理。

[20-D] Harald Niederreiter. *On a measure of denseness for sequences*. In *Topics in Classical Number Theory*, Budapest 1981, Colloquia Mathematica Societatis Janos Bolyai 34, North-Holland, Amsterdam, 1984, pp. 1163--1208. 原始出处由 [20-C] 明确引用；本文未直接核查 1984 年原文。

## 21. 实际旋转读出、柱集几何与可认证相位分辨率

### 21.1 对象与已有接口

固定无理数 $\alpha\in(0,1)$，相位取 $x\in[0,1)$，读出窗口为 $[1-\alpha,1)$。定义实际旋转读出
\[
s_k(x)=\mathbf1_{[1-\alpha,1)}(\{x+k\alpha\}),\qquad
O_n(x)=(s_0(x),\ldots,s_{n-1}(x)).
\tag{21.1}
\]
花括号为实数小数部分。对 $k\geq0$ 定义
\[
c_k=1-\{(k+1)\alpha\}=\{-(k+1)\alpha\}.
\]
无理性保证 $0<c_k<1$，且这些点两两不同。把集合
\[
\{0,1,c_0,\ldots,c_{n-1}\}
\]
递增排序为 $0=q_0<q_1<\cdots<q_{n+1}=1$，并令 $I_j=[q_j,q_{j+1})$。$n=0$ 时只有 $[0,1)$。

这里的排序切点及半开弧直接复用 `RotationGapArcs` 的 `rotationCut`、`rotationGapArc`，参数为 $N=n+1$。已有黄金词结果针对黄金斜率的轨道起点，本节处理任意无理斜率的全部相位。一般机械词、进位恒等式、排序弧的覆盖与不交性均为已有证明接口。Sturmian 的 $n+1$ 复杂度与三间隙理论属于经典数学 [21-A]；本节明确承担的是实际读出到区间纤维、估计误差及细分的对象识别。

### 21.2 定理：实际 bit 记录决定全部切点测试

对任意 $x,y\in[0,1)$ 和 $n\geq0$，
\[
\boxed{O_n(x)=O_n(y)
\iff \forall k<n,\ (c_k\leq x\iff c_k\leq y).}
\tag{21.2}
\]

**证明。** 窗口读出与实际取整增量相等：
\[
s_k(x)=\lfloor x+(k+1)\alpha\rfloor-\lfloor x+k\alpha\rfloor\in\{0,1\}.
\]
从 $\lfloor x\rfloor=0$ 起累加这些 bit，得到每一个 $\lfloor x+k\alpha\rfloor$，$0\leq k\leq n$。反之，相邻两个这样的整数之差恢复每一位读出。已有进位恒等式给出
\[
\lfloor x+(k+1)\alpha\rfloor
=\lfloor(k+1)\alpha\rfloor+\mathbf1_{\{c_k\leq x\}}.
\]
因此全部累计整数相等，当且仅当全部切点测试相等，即得式 (21.2)。这一步没有把累计计数、柱集几何或切点测试与实际读出的等价性放入假设。

### 21.3 定理：精确柱集与全部有效估计器的分类

对每个 $0\leq j\leq n$，
\[
\boxed{\{x\in[0,1):O_n(x)=O_n(q_j)\}=[q_j,q_{j+1}).}
\tag{21.3}
\]
并且对任意实数中心 $z$ 与半径 $R$，
\[
\boxed{
\bigl[\forall x\in[0,1),\ O_n(x)=O_n(q_j)\Rightarrow |x-z|\leq R\bigr]
\iff q_{j+1}-R\leq z\leq q_j+R.
}
\tag{21.4}
\]
所以该读出的最佳统一估计半径为 $(q_{j+1}-q_j)/2$，唯一最优中心为 $(q_j+q_{j+1})/2$。

**证明。** 由式 (21.2)，相同读出等价于落在每一个切点的同一侧。两个有序初始段包含关系固定，故具有相同切点测试等价于相同切点秩；复用排序弧的秩刻画即得式 (21.3)。它同时包含左端点并排除右端点，不将边界约定视为可忽略。

若统一误差界成立，在左端点代入给 $z\leq q_j+R$ 及 $q_j\leq z+R$。若 $z+R<q_{j+1}$，则点 $x=(z+R+q_{j+1})/2$ 严格位于该半开区间内，同时 $x-z>R$，矛盾。因此 $q_{j+1}-R\leq z$。反向由两端不等式及 $q_j\leq x<q_{j+1}$ 直接得到 $-R\leq x-z\leq R$。区间 $[q_{j+1}-R,q_j+R]$ 非空当且仅当 $2R\geq q_{j+1}-q_j$；在相等时它只有中点一个元素。这也解释了为什么右端点虽然不在柱集中，仍决定最坏误差上确界。

Lean `rotation_prefix_cell_and_decoder` 同时给出式 (21.3) 与 (21.4)，并在证明中完成第 21.2 节的算术识别。没有增加独立的中点代入包装定理。

### 21.4 定理：每一步只有一个旧柱集被真正分裂

令 $\beta=\{-(n+1)\alpha\}$。对全部 $x,y\in[0,1)$，有
\[
\boxed{O_{n+1}(x)=O_{n+1}(y)
\iff O_n(x)=O_n(y)\ \land\ (\beta\leq x\iff\beta\leq y).}
\tag{21.5}
\]
存在唯一 $j$ 使 $q_j<\beta<q_{j+1}$。这一旧柱集变为 $[q_j,\beta)$ 与 $[\beta,q_{j+1})$，其余旧柱集保持不变。两侧都非空，且可以明确选择
\[
x=(q_j+\beta)/2,\qquad y=\beta
\]
使 $O_n(x)=O_n(y)$、$O_{n+1}(x)\neq O_{n+1}(y)$。

**证明。** 在式 (21.2) 中把 $n+1$ 个测试分成旧测试与最后一个测试即得式 (21.5)。若 $\beta$ 等于旧切点，则某个非零整数倍的 $\alpha$ 是整数，与无理性矛盾。又因 $0<\beta<1$，排序弧的覆盖给出包含它的旧弧，不交性给出唯一性；不在旧边界上使包含关系严格。式 (21.5) 此后给出全部纤维的细分和所列显式分离点。

Lean `rotation_prefix_single_cut` 证明式 (21.5) 及带显式分离见证的唯一旧弧存在性。排序后的新端点数组与旧数组的逐项插入恒等式没有另作 Lean 声明。该结论足以在普通数学中识别实际的一次二分过程，不需要假设整个信息划分的演化规则。

### 21.5 推论：实现词数、全局相位误差与前缀度量

实际实现的长度 $n$ 词恰好有 $n+1$ 个。令 $D_n=\max_j(q_{j+1}-q_j)$，对所有基于长度 $n$ 词的实值估计函数定义
\[
\mathcal R_n^{\rm phase}=\inf_f\sup_{x\in[0,1)}|x-f(O_n(x))|.
\]
则
\[
\boxed{\mathcal R_n^{\rm phase}=D_n/2\geq\frac1{2(n+1)}.}
\tag{21.6}
\]

**证明。** 不交的非空区间给出不同读出，并覆盖全部相位，故词数恰为 $n+1$。在每个实现词上选其中点给出全局上界。对最长柱集，式 (21.4) 给任意估计的下界。全部正单元长度之和为一，最大值至少为 $1/(n+1)$，得最后一式。

若无限词的前缀距离定义为 $d_{\rm pre}(u,v)=2^{-\ell(u,v)}$，则不能存在固定 $C,\gamma>0$，使实际相位解码统一满足 $|x-y|\leq C d_{\rm pre}(O_\infty(x),O_\infty(y))^\gamma$。最长长度 $n$ 柱集内有两个内部相位相距至少 $1/[2(n+1)]$，而共同前缀长度至少为 $n$。因此所述估计会强制 $1/[2(n+1)]\leq C2^{-\gamma n}$ 对所有 $n$ 成立，矛盾。这里使用切开后的线性相位距离；没有把指数前缀尺度识别为几何间隔。

### 21.6 推论：真实细分的决策收益与信息时间

给定均匀相位分布，只观察 $O_n(X)$。对阈值事件 $P_\theta=\{X\leq\theta\}$，最小判错概率记为 $B_n(\theta)$。若 $\theta\in[q_j,q_{j+1}]$，则
\[
B_n(\theta)=\min\{\theta-q_j,q_{j+1}-\theta\}.
\]
所以
\[
\sup_\theta B_n(\theta)=D_n/2,\qquad
\int_0^1 B_n(\theta)\,d\theta=\frac14\sum_j(q_{j+1}-q_j)^2.
\tag{21.7}
\]
由第 21.4 节，设新增切点在旧单元内产生正长度 $u,v$，则平均阈值错误率恰好下降 $uv/2$，柱集熵恰好增加
\[
(u+v)\left[-\frac u{u+v}\log\frac u{u+v}
-\frac v{u+v}\log\frac v{u+v}\right].
\tag{21.8}
\]

**证明。** 阈值只穿过一个单元，其他单元上的事件已确定；该单元上的最优判断取概率较大的一侧，得到逐单元公式。积分为底长 $q_{j+1}-q_j$、高为其一半的三角形面积。平方和变化由 $(u+v)^2-u^2-v^2=2uv$ 得出；熵变化直接展开 $-u\log u-v\log v+(u+v)\log(u+v)$，其余单元抵消。令 $\tau_{\min}(n)=\min_j[-\log(q_{j+1}-q_j)]$，还有 $D_n=e^{-\tau_{\min}(n)}$。这些度量依赖真实柱集及指定测度，不能从全部 $2^n$ 个标签或 Fibonacci 稳定语言的大小直接推断。

本节的积分和熵推论为普通证明。当前新 Lean 声明建立了它们需要的实际纤维和唯一细分输入，尚未把概率测度、风险积分与列表熵源串成一条新的内核验证依赖链。

### 21.7 命题：含误码读出中的几何边界

设 $x\leq y$，令 $z_0=0$，并对 $1\leq k\leq n$ 定义 $z_k=\mathbf1_{\{c_{k-1}\in(x,y]\}}$。则
\[
s_k(y)-s_k(x)=z_{k+1}-z_k,\qquad
\boxed{d_H(O_n(x),O_n(y))=\sum_{k=0}^{n-1}|z_{k+1}-z_k|.}
\tag{21.9}
\]
这里 $d_H$ 是普通 Hamming 距离。其大小由被跨过切点在时间顺序中的变化决定，不能仅由跨过的切点数量决定。

**证明。** 第 21.2 节的进位表达式给出 $\lfloor y+k\alpha\rfloor-\lfloor x+k\alpha\rfloor=z_k$，相邻两个等式相减即得读出差。每位为零或一，其绝对差正好是该位不一致的指示函数，累加得到式 (21.9)。

一个边界例说明必须先固定损失函数。对 $n\geq1$，最左与最右柱集的读出仅第一位不同：对应 $z_0=0,z_1=\cdots=z_n=1$。因此，如果允许最多一位任意翻转，又用切开后的线性距离 $|x-\widehat x|$ 计误差，则所有长度 $n$ 读出的全局 minimax 半径都为 $1/2$。下界可让真实相位分别为零和任意接近一的最右柱集点，再将两个读出变为同一收到词；上界取恒定估计 $1/2$。这个障碍来自圆周切口，圆距离下不能使用同一个反例。抗误码的圆相位估计是下一项不同的、可精确陈述的研究任务；式 (21.9) 提供其实际观察约束。

### 21.8 形式化范围与参考来源

本节新增的两个 Lean 定理承载第 21.3--21.4 节，并从真实窗口读出完成第 21.2 节的算术识别。第 21.5--21.7 节保留上述普通证明。数量级 $D_n\asymp1/n$ 需要额外控制连分数部分商；本节没有对全部无理斜率声称这个速率，也没有从任意柱集定义直接得到三间隙的长度公式。

Automath 的 `Omega/SPG/SturmianCylinderInformationTime.lean` 接收显式 `hCyl` 上下界后推出信息时间的对数夹逼。本节补入真实观察纤维及其细分关系，定量连分数间隙估计仍需继续证明。另一项承重义务是以圆距离和允许的 Hamming 误码预算研究相位恢复，不把第 21.7 节的切口效应误判为真实圆周不可辨识性。

[21-A] Antoine Julien and Ian F. Putnam. *Spectral triples for subshifts*. Journal of Functional Analysis 270(3), 1031--1063, 2016. DOI: 10.1016/j.jfa.2015.12.002. https://arxiv.org/abs/1411.6800 . Proposition 2.10 与 Theorem 2.11 提供经典 Sturmian 复杂度、旋转区间和三间隙频率背景；这里不把这些经典事实归为新发现。

[21-B] The Omega Institute, trureturing, inspected dev `c37b4b0c0b93c0eca12961440bcd5a23bda0e742`. `D5/S1/Words/Mechanical/MechanicalBalance.lean`, `D5/S1/Words/Mechanical/FloorFractShift.lean`, `D5/S1/Words/ReturnWords/RotationGapArcs.lean` 为本节实际复用的形式证明接口；`GoldenOccurrenceGaps.lean` 与 `GoldenRankArcs.lean` 为已存在的黄金轨道起点版本。

[21-C] The Omega Institute, automath, dev `60ce0a1548858b977dd8719efb939ceb3e87effe`. `lean4/Omega/SPG/ScanErrorDiscrete.lean` 定义实际观察纤维及扫描错误；`lean4/Omega/SPG/SturmianCylinderInformationTime.lean` 的 `hCyl` 明确保留了柱集长度前提。本节不把条件推论误报为已有完整几何识别。

## 22. 二进制极限逼近、机械读出敏感性与保序权重

### 22.1 定义与已有完成结果的边界

对 $0\leq\alpha<1$、$x\in[0,1)$，使用已有实际机械词
\[
s_k(\alpha,x)=\lfloor x+(k+1)\alpha\rfloor-\lfloor x+k\alpha\rfloor\in\{0,1\},\qquad
O_n(\alpha,x)=(s_0,\ldots,s_{n-1}).
\]
它等于窗口 $[1-\alpha,1)$ 对真实旋转 $\{x+k\alpha\}$ 的读出。定义
\[
E_n(\alpha,\beta)=\{x\in[0,1):O_n(\alpha,x)\neq O_n(\beta,x)\}.
\tag{22.1}
\]
测度 $\lambda$ 为长度测度，亦为该单位相位区间上的均匀概率。

当前 `BisectionCompletion` 证明有理二分区间的精确宽度 $(u-l)2^{-p}$、端点 Cauchy 性及共同完成极限；其中对任意集合的上界判断使用经典选择，不能直接视为可执行的比较 oracle。`ReadoutTopology` 在其指定的有理探针拓扑与容量空间中刻画了有限总容量与连续实值延拓的等价。以下处理参数完成之后的真实离散读出，没有将这些连续延拓结论自动应用到不连续的阈值函数。

### 22.2 定理：构造局部参数区间及全部错误区域

固定无理 $\alpha\in(0,1)$ 和整数 $n\geq0$。对 $1\leq k\leq n$ 令 $c_k=1-\{k\alpha\}$，并令
\[
g_n=\min\bigl(\{1-\alpha\}\cup\{c_k:1\leq k\leq n\}
\cup\{|c_i-c_j|:1\leq i<j\leq n\}\bigr),\qquad
r_n=\frac{g_n}{2(n+1)}.
\]
有限集合中全部元素严格为正，故 $r_n>0$。对全部 $0\leq\delta\leq r_n$，有 $\alpha+\delta<1$，且
\[
\boxed{E_n(\alpha,\alpha+\delta)
=\bigsqcup_{k=1}^n[c_k-k\delta,c_k),\qquad
\lambda(E_n)=\frac{n(n+1)}2\delta.}
\tag{22.2}
\]
对第 $k$ 个区域内的每个相位，实际有符号读出差为
\[
\boxed{s_j(\alpha+\delta,x)-s_j(\alpha,x)
=\mathbf1_{\{j=k-1\}}-\mathbf1_{\{j=k\}},\quad 0\leq j<n.}
\tag{22.3}
\]
当 $k=n$ 时只有最后一位增加一；当 $k<n$ 时实际出现相邻 $01\to10$，其余位不变。$n=0$ 时错误集为空。

**证明。** 无理性使每个 $k\alpha$ 非整数；若两个 $c_k$ 相等，则某个非零整数倍的 $\alpha$ 是整数，矛盾。参数区间满足 $0\leq k\delta<g_n$，所以切点不越过零，实际 $k\alpha$ 的整数部分保持不变，且各扫过区间两两不交。直接展开取整进位得到
\[
D_k(x):=\lfloor x+k(\alpha+\delta)\rfloor-\lfloor x+k\alpha\rfloor
=\mathbf1_{[c_k-k\delta,c_k)}(x),\quad D_0=0.
\]
相邻累计整数相减给 $s_j(\alpha+\delta,x)-s_j(\alpha,x)=D_{j+1}-D_j$。区间不交保证至多一个 $D_k$ 非零，故得到式 (22.3)。在区间并集之外所有 $D_k$ 为零；在每个区间内第 $k-1$ 位实际改变，故错误集恰为该并集。有限测度可加性及 $\sum_{k=1}^n k=n(n+1)/2$ 给出测度公式。

`MechanicalSlopeSensitivity.local_slope_disagreement_law` 构造上述正半径，证明真实取整差、区间不交、错误集等式、测度及全部有符号变化。半径仅为明确的充分半径，没有被宣称最大。

**推论。** 对 $n\geq1$，记实际 Hamming 差为 $H_n(x)$，则在同一参数区间内
\[
\lambda(H_n=1)=n\delta,\qquad
\lambda(H_n=2)=\frac{n(n-1)}2\delta,\qquad
\lambda(H_n=0)=1-\frac{n(n+1)}2\delta,
\]
\[
\int_0^1 H_n(x)\,dx=n^2\delta.
\tag{22.4}
\]
**证明。** 最后一个扫过区间长度为 $n\delta$，此前每个区域改变两位，且没有其他错误区域。各区域的长度直接给出全部公式。

### 22.3 定理：保序数值读出的完整权重分类

对任意实权重 $w_0,\ldots,w_m$，定义非空有限读出
\[
V_w(\alpha,x)=\sum_{j=0}^m w_j s_j(\alpha,x).
\]
对每个固定无理 $\alpha\in(0,1)$，以下两项等价：
\[
\exists r>0,\quad \alpha+r<1,\quad
\forall\delta\in[0,r],\ \forall x\in[0,1),\quad
V_w(\alpha+\delta,x)\geq V_w(\alpha,x);
\]
\[
\boxed{w_0\geq w_1\geq\cdots\geq w_m\geq0.}
\tag{22.5}
\]

**必要性证明。** 将任何声称有效的正半径与第 22.2 节的正半径取较小值的一半，得到严格正扰动。每个扫过区间都非空，可选择其中点。对第 $k$ 个区域，实际数值变化为 $w_{k-1}-w_k$，$1\leq k\leq m$；最后一个区域的变化为 $w_m$。因此保序性强制全部列出的不等式。若任一条件失败，同一构造给出任意小参数扰动下的真实反例相位，没有假设任意二元模式均能由旋转实现。

**充分性证明。** 对任意 $\alpha\leq\beta$ 和同一实相位 $x$，令
\[
D_k=\lfloor x+k\beta\rfloor-\lfloor x+k\alpha\rfloor\geq0,\qquad D_0=0.
\]
从实际机械词展开，有限求和分部恒等式给
\[
V_w(\beta,x)-V_w(\alpha,x)
=w_mD_{m+1}+\sum_{k=1}^m(w_{k-1}-w_k)D_k\geq0.
\tag{22.6}
\]
该恒等式可按观察长度归纳：增加最后一项后，中间边界项恰好抵消。它还证明满足式 (22.5) 的权重在整个斜率顺序上保序。取任意 $r\in(0,1-\alpha)$ 得到所需局部命题。

Lean 定理 `MechanicalReadoutOrder.local_order_iff_decreasing_weights` 给出这一等价，必要性直接消费已构造的实际错误区域，充分性在证明内推出真实累计取整的求和分部恒等式。求和分部方法本身属于已有数学。

### 22.4 定理：二进制数值完成是一个全局 L1 等距读出

定义
\[
B_n(\alpha,x)=\sum_{j=0}^{n-1}2^{-j-1}s_j(\alpha,x),\qquad
B_\infty(\alpha,x)=\sum_{j=0}^{\infty}2^{-j-1}s_j(\alpha,x).
\]
该级数一致收敛，且 $0\leq B_\infty-B_n\leq2^{-n}$。对任意 $0\leq\alpha,\beta<1$，不要求无理，也不要求局部扰动，
\[
\boxed{\int_0^1|B_n(\beta,x)-B_n(\alpha,x)|\,dx
=(1-2^{-n})|\beta-\alpha|,}
\]
\[
\boxed{\int_0^1|B_\infty(\beta,x)-B_\infty(\alpha,x)|\,dx
=|\beta-\alpha|.}
\tag{22.7}
\]
因此 $\alpha\mapsto B_\infty(\alpha,\cdot)$ 给出到 $L^1([0,1])$ 的保序等距嵌入。这里的对象是关于同一均匀相位的函数，不是一个标量就无损恢复任意无限词的声明。

**证明。** 二进制权重非负且递减，式 (22.6) 给出 $\alpha\leq\beta$ 时每个相位上的 $B_n(\alpha,x)\leq B_n(\beta,x)$，一致极限也保持这一顺序。对每个固定 $k$，旋转窗口读出的积分为 $\alpha$：把 $x\mapsto\{x+k\alpha\}$ 在其唯一回绕点切成两段平移，窗口原像的总长度就是 $\alpha$。所以
\[
\int_0^1 B_n(\alpha,x)\,dx=\alpha(1-2^{-n}).
\]
有序情况下绝对差就是差，积分给有限公式；交换两参数覆盖另一顺序。最后由一致尾界交换极限与积分，得到无限公式。所有函数都是有限取整组合的可测函数或其一致极限。

**推论。** 在第 22.2 节的局部区间中，同一对模型同时满足
\[
\lambda(O_n(\alpha,\cdot)\neq O_n(\alpha+\delta,\cdot))
=\frac{n(n+1)}2\delta,
\qquad
\|B_n(\alpha+\delta,\cdot)-B_n(\alpha,\cdot)\|_1
=(1-2^{-n})\delta.
\tag{22.8}
\]
完整记录相等与数值编码接近是两个不同的目标。这条等式不声称 $L^\infty$ 参数稳定性。

### 22.5 命题：定向二进制逼近与边界不稳定

对无理 $\alpha\in(0,1)$，设
\[
\alpha_p^-=2^{-p}\lfloor2^p\alpha\rfloor,\qquad
\alpha_p^+=2^{-p}\lceil2^p\alpha\rceil.
\]
两种有理逼近到 $\alpha$ 的误差都严格小于 $2^{-p}$，并分别从下方、上方逼近。对固定有限 $n$，若 $x+k\alpha$ 对 $1\leq k\leq n$ 全都不是整数，则任意收敛参数序列最终都给出正确的长度 $n$ 词。

**证明。** 有限多个非整数各自到相邻整数有正距离。取这些距离除以相应 $k$ 后的正最小值，参数误差小于它时全部累计取整保持不变，从而全部 bit 保持不变。

这个结论不能同时覆盖全部相位。固定 $x=1-\alpha$，则
\[
s_0(\alpha,x)=1,\qquad s_0(\alpha_p^-,x)=0\quad\text{对每个 }p.
\tag{22.9}
\]
**证明。** $x+\alpha=1$，但 $x+\alpha_p^-\in(0,1)$；直接取整即可。即使参数的每一位精度持续增加，指定边界上的 bit 仍不等于极限处的读出。相反，从上方逼近时，有限多个取整函数的右连续性使每个固定相位、固定长度的读出最终正确；这个起始精度依赖相位，不能取为一个统一的有限值。

已有 `MechanicalPeriodicity` 还证明有理斜率的机械词从起点周期，而 $(0,1)$ 中无理斜率的机械词不最终周期。因此有限精度参数的无限时间周期性，不能被转述为极限动力系统的周期性。普通二进制与带符号数字表示之间的可计算性差异见 [22-A,22-B]。

### 22.6 推论：黄金斜率下的显式参数位数预算

令 $\alpha=\phi-1=\phi^{-1}$，$n\geq1$。已有 `GoldenHurwitzBound.golden_hurwitz_bound` 对有理数 $a/k$ 的约分分母给出
\[
\|k\phi\|>\frac1{\sqrt5\,k+1}>\frac1{4k},
\]
其中 $\|\cdot\|$ 为到最近整数的距离。于是第 22.2 节所有切点到零的距离及不同切点的距离均大于 $1/(4n)$，且 $1-\alpha>1/4$，故 $g_n>1/(4n)$。因此
\[
0\leq\delta\leq\frac1{8n(n+1)}
\quad\Longrightarrow\quad
\lambda(E_n(\alpha,\alpha+\delta))=\frac{n(n+1)}2\delta.
\tag{22.10}
\]

**证明。** 对 $a/k$ 应用上述有理逼近界，其约分分母至多为 $k$，再乘 $k$ 得最近整数界。两个切点之差的圆距离是 $(i-j)\alpha$ 到整数的距离，线性距离至少为圆距离。代入实际半径公式即可。该推导复用了新 dev 混合性论证中同一个算术间隔来源，没有把混合时间定理当成斜率稳定性定理。

对 $0<\eta\leq1/16$，只要
\[
\boxed{2^{-p}\leq\frac{2\eta}{n(n+1)},}
\tag{22.11}
\]
上方二进制逼近 $\alpha_p^+$ 引起错误记录的相位比例就严格小于 $\eta$。等价的充分整数预算为
\[
p\geq\left\lceil\log_2\frac{n(n+1)}{2\eta}\right\rceil.
\]
**证明。** 式 (22.11) 蕴含 $2^{-p}\leq1/[8n(n+1)]$，故实际误差 $\delta_p<2^{-p}$ 位于已证局部区间。将它代入式 (22.10) 即得结论。该预算控制均匀相位下的错误比例，不保证每个相位的所有 bit 精确，也不是对某个特定二进制尾误差的必要位数声明。

### 22.7 定理：联合相位校准的局部精确代价

固定无理 $\alpha\in(0,1)$ 和 $n\geq1$。令 $g>0$ 不大于 $\alpha,1-\alpha$、全部 $c_k,1-c_k$ 和不同切点的两两距离。对足够小的 $\delta,u$，满足
\[
\max_{0\leq k\leq n}|u+k\delta|\leq g/4,\qquad 0<\alpha+\delta<1,
\]
则
\[
\boxed{\lambda\{x:O_n(\alpha+\delta,x+u)\neq O_n(\alpha,x)\}
=\sum_{k=0}^n|u+k\delta|.}
\tag{22.12}
\]
机械词对相位的一周期平移不变，故这里 $x+u$ 不需要限制在 $[0,1)$。

**证明。** 对 $k\geq1$，累计取整差仅在切点 $c_k$ 扫过的长度 $|u+k\delta|$ 区间上非零，符号是 $u+k\delta$ 的符号。对 $k=0$，当 $u>0$ 时该区域是 $[1-u,1)$，当 $u<0$ 时是 $[0,-u)$，符号分别为正、负。各区域两两不交，且其端点处理与取整约定一致。每个区域恰好改变一个累计整数，因 $n\geq1$ 必然改变至少一位实际读出。区域之外全部累计整数不变。有限可加性给出式 (22.12)。

当 $n|\delta|\leq g/4$ 时，在上述局部校准类内，最小错误比例为
\[
\boxed{|\delta|\left\lfloor\frac{(n+1)^2}{4}\right\rfloor.}
\tag{22.13}
\]
**证明。** $\sum_{k=0}^n|u+k\delta|$ 在 $u=-\delta t$、$t$ 为 $0,1,\ldots,n$ 的任一中位数时最小。可取 $t=n/2$，它满足局部条件。将两端关于中位数配对求和，得到 $\lfloor(n+1)^2/4\rfloor|\delta|$。这将零相位校准的主系数约减半，但保留 $n^2|\delta|$ 阶；没有对局部参数区间以外的全部相位平移声称全局最优。

### 22.8 证明覆盖与保留边界

本节的核心证明链由四个 Lean 源和各自的 Scribe 承载。`MechanicalSlopeSensitivity.local_slope_disagreement_law` 给出实际错误区域及其测度；`MechanicalReadoutOrder.local_order_iff_decreasing_weights` 给出保序权重的必要充分条件；同源的 `geometric_readout_isometric_completion` 给出第 22.9 节的一般几何完成、积分与混合误差恒等式；`MechanicalReadoutRegularity.geometric_readout_continuity_and_jump` 给出第 22.10 节的精确连续性判据及跳变下界；`MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound` 给出第 22.12 节的逐相位一致误差界和联合预算。所有这些声明均从实际机械词出发，不以读出均值、极限存在或跳变公式作为前提。第 22.4 节的二进制积分结论由一般比率结果覆盖；第 22.5--22.7 节的二进制边界推论、黄金预算、联合校准，第 22.11 节的精确原子表示，以及第 22.12 节的极限次序，目前保留本卷所列普通证明。有限记录相等、相位平均数值误差、固定相位连续性及改变位权后的平均化，具有不同量词和损失函数，不互相替代。带误码的圆相位恢复和第 16.7、17.7 节的联合最优上界仍是独立问题，不作为本节的已证前提或完成结论。

[22-A] Donghyun Lim and Martin Ziegler. *Quantitative Coding and Complexity Theory of Continuous Data*. arXiv:2002.04005v5, 2021. https://arxiv.org/abs/2002.04005v5 . 连续数据表示与定量可接受性的背景，不将有理完成等同于任意离散后处理的有效性。

[22-B] Franziskus Wiesnet and Nils Köpp. *Limits of real numbers in the binary signed digit representation*. Logical Methods in Computer Science 18(3:24), 2022. DOI: 10.46298/lmcs-18(3:24)2022. https://arxiv.org/abs/2103.15702v5 . 带收敛模量的带符号数字流极限与可验证程序提取；其 Minlog 结果不被算作本库新的 Lean 声明。

[22-C] The Omega Institute, trureturing. `BisectionCompletion.lean`、`ReadoutTopology.lean`、`MechanicalBalance.lean`、`MechanicalPeriodicity.lean`、`GoldenHurwitzBound.lean` 提供本节使用的形式接口。`RECURSIVE_RELATIONAL_OBSERVATION.md` 第 36 节研究固定精确动力下的有限读出混合性；这里不将其有限混合性转述为全空间谱隙或数值替代后的同一性质。

### 22.9 定理：一般几何完成与参数、截断的联合误差

设 $0\leq r<1$、$0\leq\alpha,\beta<1$，并定义
\[
q_j=(1-r)r^j,\qquad P_{r,n}(\alpha,x)=\sum_{j=0}^{n-1}q_js_j(\alpha,x),\qquad
G_r(\alpha,x)=\sum_{j=0}^{\infty}q_js_j(\alpha,x).
\]
对每个实相位 $x$，级数收敛，且
\[
\boxed{0\leq G_r(\alpha,x)-P_{r,n}(\alpha,x)\leq r^n.}
\tag{22.14}
\]
两个完成读出在 $[0,1)$ 上可积，并满足
\[
\int_0^1|P_{r,n}(\beta,x)-P_{r,n}(\alpha,x)|\,dx
=(1-r^n)|\beta-\alpha|,
\]
\[
\boxed{\int_0^1|G_r(\beta,x)-G_r(\alpha,x)|\,dx=|\beta-\alpha|.}
\tag{22.15}
\]
若 $\beta\leq\alpha$，则参数替代与输出截断的联合误差恰为
\[
\boxed{\int_0^1|G_r(\alpha,x)-P_{r,n}(\beta,x)|\,dx
=\alpha-\beta(1-r^n)=(\alpha-\beta)+\beta r^n.}
\tag{22.16}
\]

**证明。** 由实际字母属于 $\{0,1\}$，每项位于 $[0,q_j]$；而 $\sum q_j=1$、$\sum_{j<n}q_j=1-r^n$。正项级数比较同时给出收敛及式 (22.14)，包括 $r=0$ 和 $n=0$ 的约定 $r^0=1$。

对任意实数 $t$，在 $x\in[0,1)$ 上直接展开进位：
\[
\lfloor x+t\rfloor=\lfloor t\rfloor+
\mathbf1_{[1-\{t\},1)}(x).
\]
两边可积，右端积分是 $\lfloor t\rfloor+\{t\}=t$。相邻累计取整相减，便得到每个实际字母的积分为 $\alpha$，从而 $\int P_{r,n}(\alpha,x)dx=\alpha(1-r^n)$。几何权重递减且非负，式 (22.6) 证明有序参数对应逐相位有序读出；通过正项极限后，$G_r$ 也保序。有限读出在 $[0,1]$ 中，支配收敛给出完成读出的可积性及 $\int G_r(\alpha,x)dx=\alpha$。对有序参数，绝对差就是差，故积分得到式 (22.15)，交换参数覆盖另一顺序。最后由
\[
P_{r,n}(\beta,x)\leq G_r(\beta,x)\leq G_r(\alpha,x)
\]
消去式 (22.16) 的绝对值，使用已证明的两个均值即得结论。

此证明由 `geometric_readout_isometric_completion` 承载，实际积分来自进位区间。二进制 $r=1/2$ 是其特例。若 $\beta$ 是 $p$ 位下方二进制逼近，则式 (22.16) 严格小于 $2^{-p}+2^{-n}$；这个预算控制相位平均误差，没有宣称全部相位上的同一界。

### 22.10 定理：固定相位连续性的完整判据

固定 $0<r<1$、$0<\alpha<1$ 和任意实相位 $x$。则
\[
\boxed{\beta\longmapsto G_r(\beta,x)\text{ 在 }\alpha\text{ 连续}
\iff \forall k\geq1,\quad x+k\alpha\notin\mathbb Z.}
\tag{22.17}
\]
若 $x+k\alpha=z\in\mathbb Z$，其中 $k\geq1$，则对每个 $0\leq\beta<\alpha$ 都有
\[
\boxed{G_r(\alpha,x)-G_r(\beta,x)\geq(1-r)^2r^{k-1}>0.}
\tag{22.18}
\]
这里连续性使用完整的实数邻域；由于 $\alpha$ 是内部点，可把邻域限制在 $(0,1)$。$r=0$ 被明确排除，因为它只保留第一位，后续累计整数命中未必影响数值。

**无整数命中时的证明。** 对给定 $N$，每个 $x+k\alpha$，$1\leq k\leq N$，到相邻整数的距离均为正。令
\[
d_N=\frac12\min\left(\{\alpha,1-\alpha\}\cup
\left\{\frac{\min(\{x+k\alpha\},1-\{x+k\alpha\})}{k}:1\leq k\leq N\right\}\right)>0.
\]
$N=0$ 时内侧集合为空。若 $|\beta-\alpha|<d_N$，则 $\beta\in(0,1)$，前 $N$ 个累计取整完全相同，故 $P_{r,N}(\beta,x)=P_{r,N}(\alpha,x)$。两个尾部都位于 $[0,r^N]$，因此
\[
|G_r(\beta,x)-G_r(\alpha,x)|\leq r^N.
\]
给定正误差，取足够大的 $N$ 使 $r^N$ 小于它，便得到连续性。

**整数命中时的证明。** 令
\[
D_j=\lfloor x+j\alpha\rfloor-\lfloor x+j\beta\rfloor\geq0,\qquad D_0=0.
\]
对任意 $N$，实际读出满足有限恒等式
\[
P_{r,N}(\alpha,x)-P_{r,N}(\beta,x)
=q_ND_N+\sum_{j=0}^{N-1}(q_j-q_{j+1})D_{j+1}.
\tag{22.19}
\]
它由展开相邻取整差后逐项抵消得到，也可按 $N$ 归纳。若在时间 $k$ 命中整数，则每个较小参数都有 $D_k\geq1$。因为
\[
q_j-q_{j+1}=(1-r)^2r^j>0,
\]
对 $N\geq k$，式 (22.19) 的右端至少为 $(1-r)^2r^{k-1}$。让 $N$ 增大，并使用式 (22.14)，该下界保留到完成读出，得到式 (22.18)。任意邻域中都能选择 $\beta<\alpha$，所以连续性不成立。这一论证处理了实际相邻 bit 的正负变化，未假设数值跳变不会抵消。

`geometric_readout_continuity_and_jump` 同时承载式 (22.17) 的显式 $\varepsilon$-$\delta$ 形式与式 (22.18)。证明中的正前缀半径和无限下界均由真实取整计算导出。

### 22.11 定理：原子分布表示及跳变的精确总量

固定 $0<r<1$ 和 $0\leq x<1$，令
\[
a_k=(1-r)^2r^{k-1},\qquad
\nu_{r,x}=\sum_{k=1}^{\infty}a_k\sum_{j=1}^{k}\delta_{(j-x)/k}.
\tag{22.20}
\]
则 $\nu_{r,x}$ 是支撑于 $(0,1]$ 的概率测度，且对 $0\leq\alpha\leq1$，
\[
\boxed{G_r(\alpha,x)=\nu_{r,x}((0,\alpha])
=\sum_{k=1}^{\infty}a_k\lfloor x+k\alpha\rfloor.}
\tag{22.21}
\]
因此，内部斜率处的左跳变恰为
\[
\boxed{G_r(\alpha,x)-G_r(\alpha-,x)
=\sum_{\substack{k\geq1\\x+k\alpha\in\mathbb Z}}(1-r)^2r^{k-1}.}
\tag{22.22}
\]

**证明。** 对 $N\geq1$，有限 Abel 展开保留终端项为
\[
P_{r,N}(\alpha,x)
=(1-r)r^{N-1}\lfloor x+N\alpha\rfloor
+\sum_{k=1}^{N-1}a_k\lfloor x+k\alpha\rfloor.
\]
这里 $\lfloor x\rfloor=0$。在所给参数范围内 $0\leq\lfloor x+N\alpha\rfloor\leq N$，终端项趋于零。又有 $\sum_{k\geq1}ka_k=1$，所以余下级数绝对且一致收敛。对每个 $k$，$\lfloor x+k\alpha\rfloor$ 精确计数满足 $(j-x)/k\leq\alpha$ 的 $j\in\{1,\ldots,k\}$。代入即得式 (22.21)，而 $\sum ka_k=1$ 给测度归一化。概率测度从下连续性给左极限，减去后只余单点质量，从而得到式 (22.22)。右连续性同样由分布函数得到。上述级数与测度推导是普通证明，不冒充新的 Lean 测度声明。

当 $x=0$、$\alpha=p/q\in(0,1)$ 且分数既约时，命中时间恰好是 $q,2q,\ldots$，所以
\[
\boxed{G_r(p/q,0)-G_r((p/q)-,0)
=\frac{(1-r)^2r^{q-1}}{1-r^q}.}
\tag{22.23}
\]
当固定相位 $x$ 无理时，有理斜率不会命中整数；如果某个无理斜率命中一次，则不能再命中第二次，否则相减会强制斜率有理。因此这一情形的跳变若存在，就恰为单个 $a_k$。这说明连续性不能只按斜率的有理性分类，固定相位也参与判定。

**推论：平均原子测度成为长度测度。** 对 $[0,1]$ 中任意 Borel 集 $A$，
\[
\boxed{\int_0^1\nu_{r,x}(A)\,dx=\lambda(A).}
\tag{22.24}
\]
**证明。** 对固定 $k,j$，变量变换 $t=(j-x)/k$ 把均匀相位推送为区间 $((j-1)/k,j/k]$ 上密度 $k$ 的测度。对 $j=1,\ldots,k$ 求和得到 $k\lambda(A)$；再用非负级数与积分交换以及 $\sum ka_k=1$ 即得结论。各个相位的读出都是原子分布函数，而相位平均产生长度测度。这给出了点态跳变与式 (22.15) 的精确 $L^1$ 距离相容的具体机制，没有把两种拓扑等同。

### 22.12 推论：改变位权的平均化与极限次序

对 $0<r<1$、$0\leq\alpha<1$、$0\leq x<1$，式 (22.21) 给出
\[
G_r(\alpha,x)-\alpha
=\sum_{k=1}^{\infty}a_k\bigl(x-\{x+k\alpha\}\bigr).
\]
由于 $\sum a_k=1-r$，得到
\[
\boxed{(1-r)(x-1)\leq G_r(\alpha,x)-\alpha\leq(1-r)x,
\qquad |G_r(\alpha,x)-\alpha|\leq1-r.}
\tag{22.25}
\]
因此 $r\uparrow1$ 时，完成读出对斜率、相位一致趋于 $\alpha$。这里改变的是位权本身，固定二进制比率 $r=1/2$ 的读出不包含这个极限。

另一方面，固定有限 $n$ 时，每个权重 $(1-r)r^j$ 随 $r\uparrow1$ 趋于零，因此 $P_{r,n}(\alpha,x)\to0$。故
\[
\lim_{r\uparrow1}\lim_{n\to\infty}P_{r,n}(\alpha,x)=\alpha,
\qquad
\lim_{n\to\infty}\lim_{r\uparrow1}P_{r,n}(\alpha,x)=0.
\tag{22.26}
\]
这两个极限在 $\alpha>0$ 时不同。若同时改变参数、位权和记录长度，对任意 $0\leq\beta<1$，三角不等式、式 (22.14) 与式 (22.25) 给出逐相位预算
\[
\boxed{|P_{r,n}(\beta,x)-\alpha|
\leq r^n+(1-r)+|\beta-\alpha|.}
\tag{22.27}
\]
所以 $\beta\to\alpha$、$r\uparrow1$、$r^n\to0$ 是一种明确的联合收敛方案。`geometric_readout_uniform_slope_bound` 从累计机械词误差的有限分部求和证明 $|G_r(\beta,x)-\beta|\leq1-r$，并与已证几何尾界结合给出式 (22.27)；式 (22.25) 更细的单侧界及式 (22.26) 的极限次序仍是本卷的普通证明。这些结论不宣称固定几何位权在参数上的一致连续性。

### 22.13 文献关系

[22-D] Michel Laurent and Arnaldo Nogueira. *Rotation number of contracted rotations*. Journal of Modern Dynamics 12, 175--191, 2018. DOI: 10.3934/jmd.2018007. https://www.aimsciences.org/article/doi/10.3934/jmd.2018007 . 使用 Hecke--Mahler 级数研究收缩旋转的参数与旋转数关系。相关的取整级数与阶梯现象属于已有研究；本节对指定实际机械读出、任意固定相位和所给误差泛函逐项证明，没有把不同参数映射直接识别。

[22-E] DoYong Kwon. *A devil's staircase from rotations and irrationality measures for Liouville numbers*. arXiv:0709.1642, 2007. https://arxiv.org/abs/0709.1642 . 研究由机械词构造的另一阶梯函数及其连续性和单侧极限。其目标映射与本节的几何加权相位函数不同；本节不把无理连续、有理跳变的一般现象宣称为首次发现。

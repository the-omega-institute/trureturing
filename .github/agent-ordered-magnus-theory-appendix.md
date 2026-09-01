
---

# 2026-09-01 追加：二阶 Magnus 可观测性与标准 Weil/Pick 主干修订

## 1. 修订目标

本轮关闭二阶 Magnus 层内部的四个有限缺口，并校正 RH lane 的中央算术桥：

1. 将 alternating two-slot kernel 的范数上界提升为精确平方公式；
2. 将该 kernel 识别为有限 Fourier 代数生成元交换子的精确系数；
3. 给出逐频率对校准时钟下的精确反向可观测性；
4. 给出 ordered-time simplex 的闭式平均公式；
5. 直接复用已冻结的 `FixedScaleWeilQuadraticForm`，不再另建平行的有限 Weil 定义；
6. 将后续中央开放边拆为 holonomy-to-Weil transport、xi-ratio Pick kernel 与 negative-index detection。

本轮仍只维护这一统一理论卷，不创建节点级 theory 文档。

## 2. 精确 kernel 强度

沿用冻结对象：

\[
K_{p,q}(t_1,t_2)
=
\chi_{\omega_p}(t_1)\chi_{\omega_q}(t_2)
-
\chi_{\omega_q}(t_1)\chi_{\omega_p}(t_2),
\qquad
\chi_\omega(t)=e^{-it\omega}.
\]

令：

\[
A_{p,q}(t_1,t_2)
=(t_1-t_2)\frac{\omega_p-\omega_q}{2}.
\]

新真源 `SecondMagnusKernelNormSquare` 机器证明：

\[
\boxed{
|K_{p,q}(t_1,t_2)|^2
=4\sin^2 A_{p,q}(t_1,t_2).
}
\]

所以既有界 \(|K_{p,q}|\le2\) 是 sharp bound。若 \(\omega_p\ne\omega_q\)，取：

\[
t_1=\frac{\pi}{\omega_p-\omega_q},
\qquad t_2=0,
\]

则：

\[
\boxed{|K_{p,q}(t_1,0)|^2=4.}
\]

这给出 pairwise faithfulness。任意非零频差均存在显式最大响应时刻。它尚未给出所有频率对共享的单一时钟。

## 3. kernel 已进入真实交换子

设 \(A\) 为复结合代数，有限生成元族为 \(G_p\in A\)，定义：

\[
H_G(t)=\sum_p\chi_{\omega_p}(t)G_p.
\]

新真源 `FiniteFourierMagnusCommutator` 机器证明：

\[
\boxed{
[H_G(t_1),H_G(t_2)]
=
\sum_{p,q}K_{p,q}(t_1,t_2)G_pG_q.
}
\]

因此 `SecondMagnusSwapCurvature` 的 alternating kernel 已经成为有限 Fourier 生成元交换子中的精确系数。当前仍未构造 Banach 或 Hilbert 空间上的 time-ordered exponential、Bochner integral、Magnus 级数收敛或无限频率极限。

## 4. pair-calibrated 精确反向可观测性

对有限单射频率族 \(\omega:I\to\mathbb R\)，定义：

\[
T_{p,q}
=
\begin{cases}
0,&p=q,\\
\displaystyle\frac\pi{\omega_p-\omega_q},&p\ne q.
\end{cases}
\]

设 \(C_{p,q}\in\mathbb C\) 且 \(C_{p,p}=0\)。定义：

\[
E_{\mathrm{cal}}(\omega,C)
=
\sum_{p,q}|K_{p,q}(T_{p,q},0)C_{p,q}|^2.
\]

新真源 `PairCalibratedSecondMagnusObservability` 机器证明：

\[
\boxed{
E_{\mathrm{cal}}(\omega,C)
=4E_{\mathrm{hol}}(C),
}
\]

其中：

\[
E_{\mathrm{hol}}(C)=\sum_{p,q}|C_{p,q}|^2.
\]

并得到：

\[
E_{\mathrm{cal}}(\omega,C)=0
\iff
\forall p,q,\ C_{p,q}=0.
\]

这说明固定两时刻缺少反向界的原因是 resonance 与采样协议。允许 pair-adapted clocks 后，完整 off-diagonal curvature 可被精确恢复。

## 5. ordered-time simplex 的闭式响应

二阶 Magnus 项使用有序区域：

\[
0\le t_2\le t_1\le T.
\]

对仅依赖时间差 \(\tau=t_1-t_2\) 的标量响应，二重积分约化为三角权重的一重积分。定义：

\[
\mathcal A_g(T)
=
\int_0^T(T-\tau)
4\sin^2\left(\frac{g\tau}{2}\right)d\tau.
\]

新真源 `OrderedTimeSimplexSecondMagnusAverage` 对 \(g\ne0\) 机器证明：

\[
\boxed{
\mathcal A_g(T)
=T^2-\frac{2(1-\cos(gT))}{g^2}.
}
\]

同时：

\[
\mathcal A_0(T)=0,
\qquad
T\ge0\Longrightarrow\mathcal A_g(T)\ge0.
\]

由 \(0\le1-\cos(gT)\le2\) 可读出下一步下界：

\[
\mathcal A_g(T)\ge T^2-\frac4{g^2}.
\]

对有限单射频率族，令：

\[
\Delta_\omega=
\min_{p\ne q}|\omega_p-\omega_q|>0.
\]

则所有非对角频率对同时满足：

\[
\mathcal A_{\omega_p-\omega_q}(T)
\ge T^2-\frac4{\Delta_\omega^2}.
\]

当 \(T>2/\Delta_\omega\) 时，右侧严格为正。因此下一真源应为：

\[
\boxed{\texttt{FiniteFrequencyOrderedSimplexCoercivity}.}
\]

它应冻结统一窗口双边界：

\[
c_{\omega,T}E_{\mathrm{hol}}(C)
\le E_{\mathrm{simplex}}(\omega,C;T)
\le T^2E_{\mathrm{hol}}(C),
\qquad c_{\omega,T}>0.
\]

## 6. 三种可观测性分层

当前二阶 Magnus 层具有三个不同强度的结论：

1. pointwise boundedness：
   \[
   0\le E^{(2)}(t_1,t_2)\le4E_{\mathrm{hol}};
   \]
2. adaptive identifiability：
   \[
   E_{\mathrm{cal}}=4E_{\mathrm{hol}};
   \]
3. common-window observability coefficient：
   \[
   \mathcal A_g(T)=T^2-2(1-\cos(gT))/g^2.
   \]

后续不得把三者混写为同一类 Magnus positivity。固定采样可共振，pair-adapted sampling 精确，ordered window 将统一强制性归约为最小频差问题。

## 7. 中央算术桥的修订

仓库已经冻结：

\[
\boxed{\texttt{D5/S3/Weil/ZetaBridge/FixedScaleWeilQuadraticForm}.}
\]

该真源已经包含 convolution-square Weil test、von Mangoldt prime-power contribution、Archimedean multiplier、pole rank-one energy、zero-side sum 与 fixed-scale positivity equivalence。

因此不再建立第二套有限 Weil quadratic form。缺失对象是从 chronological holonomy 数据进入既有标准 Weil 对象的运输：

\[
\boxed{
\text{finite Fourier memory/holonomy}
\longrightarrow
\text{admissible Weil test function}
\longrightarrow
\texttt{FixedScaleWeilQuadraticForm}.
}
\]

下一开放边命名为：

\[
\boxed{\texttt{HolonomyToFixedScaleWeilTransport}.}
\]

它至少需要证明：

- finite coefficients 到 `WeilTestFunction` 的构造；
- support 半径记账；
- prime-power 权重与 \(\log n\) 频率匹配；
- Gamma 与 pole 项保留；
- truncation remainder；
- holonomy energy 与 fixed-scale Weil form 的等式、下界或带误差比较。

显式公式应成为 prime-side 与 zero-side 相遇的标准中介。当前自定义 holonomy energy 到自定义 off-line energy 的直接 domination 不再作为 primitive hard heart。

## 8. Pick/Pontryagin 负指标接口

仓库已经冻结抽象真源：

\[
\boxed{\texttt{HermitianKernelNegativeSquares}.}
\]

下一步需要输入一个来自 completed xi 的具体函数。标准候选为：

\[
\Theta_\omega(z)
=
\frac{\xi(\frac12-\omega-iz)}
{\xi(\frac12+\omega-iz)},
\qquad\omega>0.
\]

相应 half-plane Pick kernel 可规范化为：

\[
K_{\Theta_\omega}(z,w)
=
\frac{1-\Theta_\omega(z)\overline{\Theta_\omega(w)}}
{-i(z-\overline w)}.
\]

下一真源命名为：

\[
\boxed{\texttt{XiRatioPickKernel}.}
\]

它应证明定义域、极点排除、Hermitian symmetry、reflection compatibility、临界线假设下的 Schur/inner implication，以及有限 Gram 矩阵到 `HermitianKernelNegativeSquares` 的接口。

随后建立：

\[
\boxed{\texttt{OfflineZeroPickIndexLowerBound}.}
\]

第一阶段只要求一个被窗口与采样隔离的离线零点轨道产生至少一个有限负方向。精确计数：

\[
\kappa_{\omega,T}=N_{\mathrm{off}}(\omega,T)
\]

仍登记为后续 index theorem。

## 9. determinant 与极限层

冻结的 `HorizonEffectiveIndex` 给出有限严格收缩矩阵的 barrier：

\[
\operatorname{Ind}_{\mathrm{hor}}(H)
=
\det(I-H^*H)^{-1}
=
\prod_j(1-\sigma_j^2)^{-1}.
\]

当前核心结论对一般严格收缩矩阵成立。Hankel 假设尚未承担主证明。后续需要从具体 xi/Weil symbol 构造 Hankel operator，证明 finite-section、Hilbert-Schmidt 或 trace-class 条件、负指标稳定与 Fredholm determinant 极限。

候选真源为：

\[
\boxed{
\texttt{FiniteIndexLimitStability},
\qquad
\texttt{FredholmHorizonIndexLimit}.
}
\]

## 10. 黄金周期边界

离线 monodromy 的双曲判据：

\[
4\sinh^2(\delta T)>0
\iff\delta\ne0
\]

对任意 \(T>0\) 成立。因此 \(T_\varphi=2\log\varphi\) 目前是合法采样周期与规范化选择。它尚未获得 small-divisor、continued-fraction return、frame lower bound、condition number 或 Weil/Pick index 上的独立最优性。

应先冻结：

\[
\boxed{\texttt{OfflineZeroMonodromyPeriodIndependence}.}
\]

只有一般周期定理建立后，才适合定义 `GoldenPeriodOptimalityCriterion`。

## 11. 修订后的 theorem DAG

```text
PrimeFrequencyPhaseFlow                         Frozen
        |
        v
TimeOrderedPrimeMemoryCocycle                   Frozen
        |
        v
SecondMagnusSwapCurvature                       Frozen
        |
        +-----------------------------+
        |                             |
        v                             v
SecondMagnusKernelNormSquare       FiniteFourierMagnusCommutator
        |                             |
        v                             |
PairCalibratedSecondMagnusObservability          |
        |                             |
        +---------------+-------------+
                        |
                        v
OrderedTimeSimplexSecondMagnusAverage
                        |
                        v
FiniteFrequencyOrderedSimplexCoercivity         Open
                        |
                        v
HolonomyToFixedScaleWeilTransport               Open
                        |
                        v
FixedScaleWeilQuadraticForm                     Frozen
                        |
                        v
XiRatioPickKernel                               Open
                        |
                        v
HermitianKernelNegativeSquares                  Frozen
                        |
                        v
OfflineZeroPickIndexLowerBound                  Open
                        |
                        v
FiniteIndexLimitStability / Fredholm limit      Open
                        |
                        v
Uniform global Weil positivity                  Open
                        |
                        v
RH
```

## 12. 接下来的形式化顺序

### P0. `FiniteFrequencyOrderedSimplexCoercivity`

利用本轮闭式积分与有限最小频差，冻结统一时间窗口双边界。

### P1. `HolonomyToFixedScaleWeilTransport`

复用既有 fixed-scale Weil 真源，构造 finite Fourier/curvature coefficients 到合法 test function 的运输。

### P2. `XiRatioPickKernel`

定义 completed-xi ratio 的具体 half-plane kernel，并证明 Hermitian 与 reflection laws。

### P3. `OfflineZeroPickIndexLowerBound`

把被隔离的离线零点运输成有限 Gram 负方向。

### P4. `FiniteIndexLimitStability`

控制采样、窗口、prime-power cutoff 与 operator dimension 增长时的负指标逃逸。

### P5. `FredholmHorizonIndexLimit`

把有限 determinant barrier 提升到 trace-class Fredholm determinant。

## 13. 当前 claim boundary

本轮机器证明：

- alternating kernel 的精确 squared norm；
- 非零频差的显式最大响应采样；
- 有限 Fourier 代数生成元的精确 commutator expansion；
- pair-adapted clocks 下四倍 holonomy energy 的精确恢复；
- ordered-time simplex scalar response 的闭式公式；
- 零频差响应为零；
- 非负窗口上的响应非负。

本轮没有证明公共固定时刻的全频率可观测性、finite-family ordered-window coercivity、time-ordered exponential、Magnus 级数收敛、holonomy-to-Weil transport、xi-ratio Pick positivity、离线零点数与负平方数的等式、Fredholm 极限、全局 Weil 正性或 RH。

本轮关闭的有限链为：

\[
\boxed{
\text{Fourier chronology}
\longrightarrow
\text{algebra commutator}
\longrightarrow
\text{exact kernel strength}
\longrightarrow
\text{pairwise reverse observability}
\longrightarrow
\text{ordered-simplex response}.
}
\]

中央开放边现在被压缩为：

\[
\boxed{
\texttt{FiniteFrequencyOrderedSimplexCoercivity}
\rightarrow
\texttt{HolonomyToFixedScaleWeilTransport}
\rightarrow
\texttt{XiRatioPickKernel}
\rightarrow
\texttt{OfflineZeroPickIndexLowerBound}.
}

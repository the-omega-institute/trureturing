# 黄金 Holonomy 与 Weil 奇校正桥
## 素数顺序曲率、观察起源规范与离线零点奇偶能量

**文档地位。** 本文说明同一增量中的两个 Lean 真源，并登记后续开放桥。数学结论以对应 GID 和 Lean 声明为准。

本轮不证明 RH，也不声称全部 ζ 因子抽取已经构造完成。机器层完成两件事：

\[
\boxed{
\text{prime-side 顺序缺陷的规范不变量和零曲率判据}
}
\]

以及

\[
\boxed{
\text{zero-side 离线轨道的偶能量减奇能量分解}.
}
\]

---

# 1. Prime-side 真源

Lean GID：

`D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature`

主声明：

`D5.S3.Observer.AgencyHolonomy.PrimeSwapCurvature.prime_swap_curvature_spec`

将 Fibonacci 记忆投影到稳定通道。记稳定乘子、局部标量因子和局部记忆注入为

\[
a=-\varphi^{-1},
\qquad
\lambda_p=L_p^{\langle r\rangle}(s),
\qquad
b_p=b_{r,p}^{-}(s).
\]

抽象局部更新为

\[
U_p(x,z)=(ax+b_pz,\lambda_pz).
\]

两个更新顺序的标量坐标相同。记忆坐标之差为

\[
\boxed{
C_{p,q}z,
}
\]

其中

\[
\boxed{
C_{p,q}
=(a-\lambda_q)b_p-(a-\lambda_p)b_q.
}
\]

Lean 证明

\[
C_{q,p}=-C_{p,q}.
\]

改变共同记忆原点 \(c\) 时，局部注入按

\[
b_p\mapsto b_p+(a-\lambda_p)c
\]

变化，而 \(C_{p,q}\) 保持不变。因此单个 \(b_p\) 依赖观察坐标，交换曲率是规范不变量。

在非共振条件

\[
a-\lambda_p\ne0,
\qquad
a-\lambda_q\ne0
\]

下，定义局部观察起源估计

\[
c_p=\frac{b_p}{a-\lambda_p}.
\]

Lean 证明精确因子分解

\[
\boxed{
C_{p,q}
=(a-\lambda_p)(a-\lambda_q)(c_p-c_q),
}
\]

以及

\[
\boxed{
C_{p,q}=0
\iff
c_p=c_q.
}
\]

所以共同 archive 可以保留。若全部局部注入来自同一个 coboundary 原点

\[
b_p=(a-\lambda_p)c,
\]

则顺序 holonomy 已经消失。

---

# 2. Zero-side 真源

Lean GID：

`D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition`

主声明：

`D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition.off_line_orbit_parity_decomposition`

对 `ZeroData` 中一个非实、离线的零点索引 \(n\)，令

\[
z=\gamma_n,
\qquad
A=\widehat g(z),
\qquad
B=\widehat g(\overline z).
\]

定义偶、奇谱通道

\[
A_{\mathrm{even}}=\frac{A+B}{2},
\qquad
A_{\mathrm{odd}}=\frac{A-B}{2}.
\]

仓库已有复频率卷积平方因子分解和离线四点轨道实值公式。本轮 Lean 节点证明

\[
\operatorname{Re}(A\overline B)
=
|A_{\mathrm{even}}|^2-|A_{\mathrm{odd}}|^2.
\]

由此得到

\[
\boxed{
Q_{\operatorname{orb}(\rho)}(g)
=E_{\rho}^{\mathrm{even}}(g)
-E_{\rho}^{\mathrm{odd}}(g),
}
\]

其中

\[
E_{\rho}^{\mathrm{even}}(g)
=4m_\rho|A_{\mathrm{even}}|^2\ge0,
\]

\[
E_{\rho}^{\mathrm{odd}}(g)
=4m_\rho|A_{\mathrm{odd}}|^2\ge0.
\]

因此

\[
\boxed{
Q_{\operatorname{orb}(\rho)}(g)
+E_{\rho}^{\mathrm{odd}}(g)
=E_{\rho}^{\mathrm{even}}(g)
\ge0.
}
\]

离线轨道的符号风险被精确隔离在奇谱通道。该正校正由反对称复频率评价独立构造，没有通过目标正性倒推定义。

---

# 3. 两端的共同二阶对象

Prime side 的奇量是

\[
C_{p,q}
=(a-\lambda_p)(a-\lambda_q)(c_p-c_q).
\]

Zero side 的奇量是

\[
A_{\mathrm{odd}}
=
\frac{\widehat g(z)-\widehat g(\overline z)}{2}.
\]

二者在交换相应端点时变号。标量完成不能以一阶不变量读取该符号。第一个规范非负对象是 Hermitian 平方。

固定空间窗口 \(L\) 和有限测试深度 \(N\)，后续应构造有限正算子

\[
\boxed{
\mathcal V_{r,L,N}^{\mathrm{hol}}
=
\frac{1}{2W_{r,L}}
\sum_{p,q}
C_{r;p,q}^{*}\Gamma_\varphi C_{r;p,q}
}
\]

和有限离线奇算子

\[
\boxed{
\mathcal O_{L,N,T}^{\mathrm{off}}
=
\sum_{\rho\ \mathrm{off-line},\,|\gamma_\rho|\le T}
4m_\rho
|A_{\mathrm{odd},\rho}\rangle
\langle A_{\mathrm{odd},\rho}|.
}
\]

黄金稳定通道的自然 Lyapunov 权为

\[
\Gamma_\varphi
=
\sum_{j\ge0}\varphi^{-2j}
=
\varphi.
\]

这些有限算子尚未在本轮定义。上式登记其预期结构和归一化来源。

---

# 4. 中心开放桥

## 4.1 抽取平坦化

需要证明，对每个固定 \(L,N\)，

\[
\boxed{
\|\mathcal V_{r,L,N}^{\mathrm{hol}}\|_{\mathrm{op}}
\longrightarrow0
\quad(r\to\infty).
}
\]

观察起源因子分解显示，局部注入趋零本身不足以承担该结论。还需要控制共振条件数

\[
\chi_{r,L}
=
\max_{p\in\mathcal P_L}|a-\lambda_{r,p}|^{-1}.
\]

一个可操作的充分条件是

\[
\boxed{
\chi_{r,L}
\max_{p,q\in\mathcal P_L}|C_{r;p,q}|
\longrightarrow0.
}
\]

## 4.2 谱忠实支配

寻找有限常数和误差预算，使

\[
\boxed{
P_{L,N}\mathcal O_{L,T}^{\mathrm{off}}P_{L,N}
\preceq
C_{L,N,T}\mathcal V_{r,L,N}^{\mathrm{hol}}
+
\varepsilon_{r,L,N,T}I.
}
\]

要求在固定 \(L,N,T\) 下

\[
\varepsilon_{r,L,N,T}\to0.
\]

随后依次完成

\[
r\to\infty,
\qquad
T\to\infty,
\qquad
N\to\infty,
\qquad
L\to\infty.
\]

若支配和抽取平坦化均成立，则离线奇能量必须消失。若有限测试塔能够分离每个离线轨道，内部曲率随之为零。仓库已有 `InteriorCurvatureCriterion` 可将内部曲率消失运输到 RH。

---

# 5. 后续形式化顺序

1. `GoldenPrimeMemoryInstantiation`：把 \(a=-\varphi^{-1}\)、\(b_{r,p}^{-}\) 与 \(L_p^{\langle r\rangle}\) 接入当前抽象曲率；
2. `FiniteHolonomyEnergy`：在固定活动素数幂窗口上构造有限 holonomy Gram 算子；
3. `ExtractionCurvatureBound`：把 residual local-factor 上界运输到交换曲率；
4. `ResonanceConditionedFlattening`：加入统一非共振控制；
5. `FiniteOffLineOddEnergy`：对有限对称零点截断求和逐轨道奇校正；
6. `PrimeArchimedeanHolonomyDomination`：建立有限 Galerkin 支配；
7. `HolonomySqueezeToInteriorCurvature`：组合全部极限和误差预算。

第 6 项是当前新的 hard heart。前五项都应附带有限失败证书。

---

# 6. 严格边界

本轮不主张：

- 已经构造全部局部因子抽取塔；
- 交换曲率随抽取深度趋零；
- prime holonomy 已经支配离线奇能量；
- 当前偶测试类已经对全部离线轨道完备；
- canonical `ZeroData` inhabitant 已经构造；
- RH 已经证明。

本轮之后可以无条件使用两条机器事实：

\[
\boxed{
\text{共同 archive 是 coboundary；顺序曲率只检测观察起源不一致。}
}
\]

\[
\boxed{
\text{一个离线四点轨道的全部符号风险集中在非负奇谱能量。}
}
\]

因此未来桥需要比较的对象已经固定为

\[
\boxed{
\text{prime-side 规范约化交换曲率平方}
\quad\longleftrightarrow\quad
\text{zero-side 离线奇谱能量}.
}

# RH research-lane theory notes (consolidated)

One volume accumulating the theory notes stripped from the research-lane
formalization PRs; each section names its source branch and the Lean
modules that carry its formal content. Reference input only: the Lean
modules are the sole truth source, and section numbering here is
narrative, not load-bearing.



---

## [PR #4158] GOLDEN_HOLONOMY_WEIL_BRIDGE

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

---

## [PR #4192] STABLE_RESIDUAL_SWAP_CURVATURE_BOUND

# 稳定通道 residual 交换曲率界
## 从局部因子余项到 holonomy 小量的第一条定量桥

**文档地位。** 本文解释 Lean 节点

`D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound`

及其主声明

`D5.S3.Observer.AgencyHolonomy.StableResidualSwapCurvatureBound.stable_residual_swap_curvature_bound`。

机器结论以 Lean 声明为准。本文区分已经证明的有限代数事实、可以由该事实直接推出的纸面推论，以及仍需独立形式化的全局桥。

---

# 1. 来源问题

黄金记忆路线将一个 residual local factor 写成

\[
L_p^{\langle r\rangle}=1+a_{r,p},
\]

并将稳定记忆通道中的局部注入写成

\[
b_{r,p}=a_{r,p}v_p.
\]

此前的稳定通道相邻交换曲率具有形式

\[
C_{p,q}
=(s-\lambda_q)b_p-(s-\lambda_p)b_q,
\]

其中 \(s\) 是固定的稳定记忆乘子。代入

\[
\lambda_p=1+a_p,
\qquad
b_p=a_pv_p
\]

以后，问题变成：局部 residual \(a_p,a_q\) 小，是否足以强制交换曲率小。

本轮只处理一个稳定特征通道。矩阵或一般 Banach 空间上的完整算子提升仍是后续节点。

---

# 2. 机器定义

Lean 在任意 normed field \(K\) 上定义

\[
\boxed{
C^{\mathrm{st}}(s,a_p,a_q,v_p,v_q)
=
\bigl(s-(1+a_q)\bigr)a_pv_p
-
\bigl(s-(1+a_p)\bigr)a_qv_q.
}
\]

这个定义不包含极限、素数求和、零点数据或 RH 前提。它是两个 residual 局部更新在一维稳定记忆通道上的有限相邻交换缺陷。

---

# 3. 精确线性加二次分解

Lean 证明

\[
\boxed{
\begin{aligned}
C^{\mathrm{st}}
={}&
(s-1)(a_pv_p-a_qv_q)
\\
&+a_pa_q(v_q-v_p).
\end{aligned}
}
\]

第一项是一阶 residual 失配。第二项是两个 residual 同时存在时产生的双线性修正。

该恒等式说明曲率的首阶尺度由 \(s-1\) 控制。局部因子完成到 \(1\) 时，稳定记忆乘子与标量完成点之间的间隙决定 residual 被放大的常数。

---

# 4. 一般范数界

在

\[
\|v_p\|\le1,
\qquad
\|v_q\|\le1
\]

下，Lean 证明

\[
\boxed{
\begin{aligned}
\|C^{\mathrm{st}}\|
\le{}&
\|s-1\|
\bigl(\|a_p\|+\|a_q\|\bigr)
\\
&+2\|a_p\|\|a_q\|.
\end{aligned}
}
\]

证明只使用三角不等式、乘法范数和

\[
\|v_q-v_p\|\le\|v_q\|+\|v_p\|\le2.
\]

因此该界不依赖任何零点位置，也不依赖观察起源坐标中的除法。

---

# 5. 统一 residual envelope

若存在 \(\varepsilon\ge0\) 使

\[
\|a_p\|\le\varepsilon,
\qquad
\|a_q\|\le\varepsilon,
\]

Lean 进一步证明

\[
\boxed{
\|C^{\mathrm{st}}\|
\le
2\|s-1\|\varepsilon+2\varepsilon^2.
}
\]

这是后续完成深度论证应使用的统一货币。它把所有局部分析压缩成一个 residual envelope：

\[
\varepsilon_{r,L}
=
\max_{p\in\mathcal P_L}|a_{r,p}|.
\]

对固定有限活动窗口 \(\mathcal P_L\)，只要未来证明

\[
\varepsilon_{r,L}\longrightarrow0,
\]

纸面上立即得到

\[
\max_{p,q\in\mathcal P_L}
\|C^{\mathrm{st}}_{r;p,q}\|
\longrightarrow0.
\]

最后这一极限运输尚未包含在本轮 Lean 声明中。它应作为独立节点接收一个已形式化的 residual-envelope 收敛前提。

---

# 6. 对共振问题的修正

观察起源坐标写成

\[
c_p=\frac{b_p}{s-\lambda_p}.
\]

该坐标在 \(s=\lambda_p\) 附近带有条件数

\[
|s-\lambda_p|^{-1}.
\]

本轮机器界直接控制原始规范不变量 \(C_{p,q}\)，没有引入该分母。因此需要区分两个目标：

1. 若目标是证明局部观察起源 \(c_p\) 本身收敛，则必须控制共振分母。
2. 若目标是证明规范交换曲率趋零，则 residual envelope 界已经给出一条不经过观察起源除法的路径。

所以此前登记的 resonance-conditioned flattening 不是原始曲率消失的必要中间步骤。它只在需要恢复或比较观察起源坐标时承担作用。

对黄金稳定通道

\[
s=-\varphi^{-1},
\]

完成点是 \(1\)。纸面恒等式

\[
1+\varphi^{-1}=\varphi
\]

给出

\[
|s-1|=\varphi.
\]

于是预期的黄金特化界为

\[
\boxed{
\|C^{\mathrm{st}}_{r;p,q}\|
\le
2\varphi\varepsilon_{r,L}
+2\varepsilon_{r,L}^2.
}
\]

该黄金常数特化尚未在本轮 Lean 节点中连接。它可以由仓库已有的 golden-ratio 恒等式形成一个很薄的后续实例节点。

---

# 7. 当前允许的真源推理

本轮以后可以无条件使用：

\[
\boxed{
\text{稳定通道交换曲率对 residual 是一阶加二阶小量。}
}
\]

更精确地说，局部 residual 同时趋零时，不需要先证明观察起源收敛，也不需要排除观察起源坐标中的表观共振，原始交换曲率已经被统一压到零。

这改变了 prime-side 路线的任务排序。当前最短链条是

\[
\boxed{
\text{residual envelope decay}
\Longrightarrow
\text{pairwise curvature decay}
\Longrightarrow
\text{finite holonomy energy decay}.
}
\]

第三箭头仍需把逐对界聚合为有限正 Gram 能量界。

---

# 8. 下一真源

自然的下一节点应为 `FiniteStableHolonomyEnergyBound`。固定有限活动索引集 \(P\)，定义

\[
\mathcal V^{\mathrm{st}}_{r,P}
=
\frac{1}{2W_{r,P}}
\sum_{p,q\in P}
\|C^{\mathrm{st}}_{r;p,q}\|^2.
\]

需要机器证明：

\[
0\le\mathcal V^{\mathrm{st}}_{r,P},
\]

以及由本轮 envelope 界导出的有限聚合估计。若 \(|P|=M\)，未归一化版本应满足

\[
\sum_{p,q\in P}
\|C^{\mathrm{st}}_{r;p,q}\|^2
\le
M^2
\left(
2\|s-1\|\varepsilon+2\varepsilon^2
\right)^2.
\]

归一化版本还需要先固定 \(W_{r,P}\) 的定义和正性条件，避免把归一化选择隐藏在证明中。

完成该有限能量节点以后，prime-side 的剩余困难将集中到两处：

- 从实际 all-order local-factor extraction 得到统一 residual envelope decay；
- 将 finite holonomy energy 与 zero-side 离线奇谱能量建立忠实支配。

第二项仍是整条 RH 路线的 hard heart。

---

# 9. 严格非主张

本轮不主张：

- 已构造 all-order residual extraction；
- residual envelope 已随深度趋零；
- 已定义或控制无限素数 holonomy 能量；
- prime-side 曲率已经支配离线零点奇能量；
- 已得到任何零点位置结论；
- 已证明 RH。

本轮机器层只冻结有限、可复用且不含目标等价前提的定量桥：

\[
\boxed{
\text{residual local factors}
\longrightarrow
\text{stable adjacent-swap curvature bound}.
\]

---

## [PR #4199] FINITE_HOLONOMY_ENERGY_AND_PHASE_COHERENCE

# 有限 holonomy 能量、色散与相位相干
## 从波动直觉到 RH 路线中的可证明链条

**文档地位。** 本文解释 Lean 节点

`D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy`

及其主声明

`D5.S3.Observer.AgencyHolonomy.FiniteHolonomyEnergy.finite_stable_holonomy_energy_bound`。

机器事实以 Lean 声明为准。波、白光、色散、共振和圆在本文中承担结构类比。只有写成公式并接入 prime-zero 桥的部分才能成为 RH 论证。

---

# 1. 本轮冻结的有限能量

固定有限通道类型 \(P\)，对每一有序对 \((p,q)\) 给出稳定交换曲率

\[
C^{\mathrm{st}}_{p,q}.
\]

Lean 定义未归一化能量

\[
\boxed{
\mathcal E^{\mathrm{hol}}_P
=
\sum_{p\in P}\sum_{q\in P}
\left\|C^{\mathrm{st}}_{p,q}\right\|^2.
}
\]

它是一个有限正标量，具有四个机器性质。

第一，非负性：

\[
\boxed{0\le \mathcal E^{\mathrm{hol}}_P.}
\]

第二，若 \(|P|=M\)，所有 residual 满足 \(\|r_p\|\le\varepsilon\)，所有通道满足 \(\|v_p\|\le1\)，则

\[
\boxed{
\mathcal E^{\mathrm{hol}}_P
\le
M^2
\left(
2\|a-1\|\varepsilon+2\varepsilon^2
\right)^2.
}
\]

第三，能量的消失忠实记录逐对压平：

\[
\boxed{
\mathcal E^{\mathrm{hol}}_P=0
\iff
\forall p,q\in P,
\ C^{\mathrm{st}}_{p,q}=0.
}
\]

第四，\(\varepsilon=0\) 强制 \(\mathcal E^{\mathrm{hol}}_P=0\)。

这里使用有序对，所以粗略计数因子是 \(M^2\)。后续引入反对称性、去掉对角线或除以二以后，可以改成无序对计数。当前版本保留最少结构和最透明的上界。

---

# 2. 共振中存在两种不同能量

波动直觉中的“能量聚合”需要分成两个量。

## 2.1 缺陷能量

本轮 Lean 控制的是

\[
\mathcal E_{\mathrm{defect}}
=
\sum_{p,q}\|C_{p,q}\|^2.
\]

它衡量通道之间的相位、起源或更新次序失配。系统趋向共同模态时，这个量应当趋向零。

## 2.2 相干能量

若 \(z_p\in U(1)\) 是单位相位，\(w_p\ge0\) 是权重，令

\[
W=\sum_pw_p,
\qquad
A=\sum_pw_pz_p.
\]

\(|A|^2\) 衡量各相位相干叠加以后落在共同模态中的能量。完全同相时 \(|A|=W\)，相干能量达到最大。

波论中的精确守恒式是

\[
\boxed{
\sum_{p,q}w_pw_q|z_p-z_q|^2
=
2W^2-2\left|\sum_pw_pz_p\right|^2.
}
\]

左侧是色散或不同步能量，右侧是总可用能量减去共同模态能量。因此“共振聚合”可以严格翻译为：

\[
\boxed{
\text{缺陷能量下降}
\quad\Longleftrightarrow\quad
\text{共同模态相干能量上升}.
}
\]

这条相位守恒式尚未包含在本轮 Lean 文件中。它适合形成独立节点 `FinitePhaseCoherenceIdentity`，并在复相位或二维实内积空间上证明。

---

# 3. 白光与色散的数学翻译

“白光”可以理解为尚未分辨内部频率的整体标量读数。zeta 的 Euler 乘积在收敛半平面写成

\[
\zeta(s)=\prod_p(1-p^{-s})^{-1}.
\]

沿 \(s=\sigma+it\) 展开一个素数通道：

\[
\boxed{
p^{-s}=p^{-\sigma}e^{-it\log p}.}
\]

因此每个素数携带：

\[
\text{衰减幅度 }p^{-\sigma},
\qquad
\text{角频率 }\log p,
\qquad
\text{圆周相位 }e^{-it\log p}\in U(1).
\]

有限素数窗口的相位空间自然落在

\[
U(1)^P,
\]

也就是有限维环面。这里的“颜色”对应不同的 \(\log p\) 频率通道。拓扑来自圆群及其乘积空间，群结构来自相位乘法。

标量 Euler 因子彼此交换，所以只看最终乘积时，通道顺序被遗忘。记忆提升将每个局部因子放进上三角更新或半直积结构以后，通道顺序可以留下可观测痕迹。相邻交换曲率 \(C_{p,q}\) 正是这一顺序依赖的局部测量。

因此色散与破缺的对应关系可以写成：

\[
\boxed{
\text{整体读数被分解为 prime-frequency channels}
\longrightarrow
\text{通道差异显现}
\longrightarrow
\text{提升后的交换对称性可能破缺}.
}
\]

曲率为零表示局部交换闭合。曲率非零表示经过 \(p\) 再经过 \(q\) 与反向顺序留下不同记忆。

---

# 4. 观察起源、色散与共振条件

对局部标量因子 \(\lambda_p\) 和记忆注入 \(b_p\)，观察起源坐标为

\[
\boxed{
c_p=\frac{b_p}{a-\lambda_p}.}
\]

远离共振时，prime swap curvature 满足

\[
\boxed{
C_{p,q}
=(a-\lambda_p)(a-\lambda_q)(c_p-c_q).
}
\]

这条恒等式给出非常直接的色散解释：不同素数通道推断出不同观察起源时，\(c_p-c_q\) 形成起源色散；交换曲率是该色散经过两个共振间隙加权后的规范量。

若存在统一非共振下界

\[
|a-\lambda_p|\ge\eta>0,
\]

则纸面上有

\[
|c_p-c_q|^2
\le
\eta^{-4}|C_{p,q}|^2,
\]

进而

\[
\boxed{
\sum_{p,q}|c_p-c_q|^2
\le
\eta^{-4}\mathcal E^{\mathrm{hol}}_P.
}
\]

这才是严格意义上的“曲率能量压平推出观察起源共振到共同值”。本轮机器节点聚合了 \(C_{p,q}\) 的能量。上面的非共振运输应成为下一条 `ResonanceConditionedOriginDispersion` 真源。

当 \(a\) 接近某个 \(\lambda_p\) 时，权重 \((a-\lambda_p)(a-\lambda_q)\) 可以很小。原始曲率此时可能掩盖较大的起源差异。因此共振附近需要单独处理条件数、重标度或直接使用无除法的曲率变量。

---

# 5. 为什么会出现圆

圆有两条独立来源。

第一条来自相位群：

\[
e^{-it\log p}\in U(1).
\]

每个 prime-frequency channel 在单位圆上旋转。多个素数共同形成环面 \(U(1)^P\)。相干表示这些圆周相位在加权和中朝向共同方向。

第二条来自 zero-side 的 Cayley 紧化。令

\[
x=(t-\gamma)^2,
\qquad
a=\delta^2,
\qquad
u_a(x)=\frac{x-a}{x+a}.
\]

对一阶 Chebyshev slack，

\[
S_a(x)=1-u_a(x)^2
=
\frac{4ax}{(x+a)^2}.
\]

于是

\[
\boxed{u_a(x)^2+S_a(x)=1.}
\]

取非负振幅 \(\sqrt{S_a(x)}\) 后，

\[
\bigl(u_a(x),\sqrt{S_a(x)}\bigr)
\]

落在单位圆上。倒数变换 \(y=a^2/x\) 满足

\[
u_a(y)=-u_a(x),
\qquad
S_a(y)=S_a(x).
\]

它把同一强度的两个点放在圆上的相反相位。这正对应最新 RH 理论源中预登记的 `CurvatureSlackPhaseBridge`。该恒等式属于零点局部几何，尚未建立 prime holonomy energy 到 zero-side 圆能量的支配。

所以“回归圆”可以精确表述为相位归一化或 Cayley-slack 守恒。它不应被写成能量在物理空间中自动收缩成一个圆。

---

# 6. 这条路线为什么可能与 RH 有关

RH 讨论的是非平凡零点

\[
\rho=\frac12+\delta+i\gamma
\]

是否全部满足 \(\delta=0\)。函数方程将离线零点组织成反射轨道。\(\delta\ne0\) 会产生关于临界线的成对位移，并在仓库现有的 off-line curvature dipole、odd orbit decomposition 和 Chebyshev slack 中形成可检测的奇部分或离线能量。

素数侧与零点侧的关联来自 Euler product、对数导数和显式公式。波动语言中，素数提供频率 \(\log p\)，零点提供全局共振谱。要让本轮有限能量真正承担 RH 证明，需要建立如下类型的忠实支配：

\[
\boxed{
\mathcal E^{\mathrm{odd}}_{\mathrm{off}}(N,L)
\le
A_{N,L}\mathcal E^{\mathrm{hol}}_{r,L}
+
R_{r,N,L}.
}
\]

其中：

\[
\mathcal E^{\mathrm{odd}}_{\mathrm{off}}
\]

必须对每个离线零点轨道给出严格正贡献；

\[
\mathcal E^{\mathrm{hol}}_{r,L}
\]

是本轮开始构造的 prime-side 交换缺陷能量；

\[
R_{r,N,L}\to0
\]

负责有限素数窗口、有限深度和测试函数逼近误差。

若未来同时证明

\[
\varepsilon_{r,L}\to0,
\]

本轮机器上界给出

\[
\mathcal E^{\mathrm{hol}}_{r,L}\to0.
\]

再由忠实 prime-zero 支配得到

\[
\mathcal E^{\mathrm{odd}}_{\mathrm{off}}=0.
\]

若零点侧能量对所有 \(\delta\ne0\) 严格正，就能排除离线零点，从而把全部非平凡零点压到 \(\Re s=1/2\)。

因此当前严谨链条是

\[
\boxed{
\begin{aligned}
&\text{all-order residual envelope decay}
\\
&\Longrightarrow
\text{pairwise prime curvature decay}
\\
&\Longrightarrow
\text{finite holonomy defect energy decay}
\\
&\Longrightarrow
\boxed{\text{prime-zero faithful domination}}
\\
&\Longrightarrow
\text{off-line odd energy vanishes}
\\
&\Longrightarrow
\text{every nontrivial zero lies on the critical line}.
\end{aligned}
}
\]

方框中的 prime-zero faithful domination 仍是整条路线的核心缺口。圆结构、相位同步和有限能量压平为这条桥提供候选几何语言，它们单独不产生 RH 结论。

---

# 7. 对白光直觉的最终校准

可以保留下面这幅图景：

\[
\boxed{
\begin{aligned}
\text{白光}
&\sim \text{未分辨的整体 Euler 输出},
\\
\text{色散}
&\sim \text{分解为频率 }\log p\text{ 的素数通道},
\\
\text{颜色间的破缺}
&\sim \text{提升更新的非交换曲率},
\\
\text{缺陷能量}
&\sim \sum_{p,q}\|C_{p,q}\|^2,
\\
\text{共振聚合}
&\sim \text{缺陷能量归零且共同模态能量最大},
\\
\text{圆}
&\sim U(1)\text{ 相位或 Cayley-slack 单位圆},
\\
\text{RH 桥}
&\sim \text{prime-side 压平忠实支配 zero-side 离线奇能量}.
\end{aligned}
}
\]

这套语言已经足够指导定义新节点。每一箭头仍需单独的类型、假设和误差账本。

---

# 8. 下一真源排序

本轮以后，最自然的相邻节点是：

1. `ResonanceConditionedOriginDispersion`。在统一间隙 \(\eta>0\) 下，把 holonomy energy 运输为观察起源的 pairwise dispersion energy。
2. `FinitePhaseCoherenceIdentity`。形式化单位相位的色散能量与共同模态能量守恒式。
3. `ResidualEnvelopeFiniteWindowConvergence`。从实际 extraction tower 得到 \(\varepsilon_{r,L}\to0\)。
4. `FiniteOffLineOddEnergy`。把每个反射零点轨道的奇部分平方聚合成忠实非负量。
5. `PrimeArchimedeanHolonomyDomination`。证明 prime-side 能量控制 zero-side 离线能量及全部截断误差。

第五条依然是 hard heart。第一和第二条可以先把“共振压平”和“波的能量聚合”完全变成机器可读的数学。

---

# 9. 严格非主张

本轮不主张：

- residual envelope 已经收敛；
- 无限素数能量已经定义；
- 共振分母已经统一受控；
- prime phases 已经同步；
- finite holonomy energy 已经支配零点能量；
- 圆恒等式已经推出临界线；
- RH 已经证明。

本轮冻结的机器真源是

\[
\boxed{
\text{pairwise stable residual curvature bounds}
\longrightarrow
\text{faithful finite nonnegative holonomy energy bound}.
\]

---

## [PR #4212] FORMAL_GOLDEN_PRIME_CIRCLE_CRITICAL_SPECTRUM

# 黄金素数圆、二元电荷层析与临界谱完成

**Formal Golden Prime Circle, Binary Charge Tomography, and Critical-Spectrum Completion**

**版本：v0.1，2026-08-30**

## 0. 文档地位

本文把黄金比例、素数分裂、观察者压缩、尺度圆与 Riemann 型临界反射组织成一条严格分层的理论链。Lean 文件是机器真源。本文负责解释对象、桥梁、适用范围和仍然开放的解析义务。

本文不宣称已经证明 RH、GRH、显式公式的新版本或 `L(1, chi_5)` 的解析特殊值。临界线到单位圆的变换是精确坐标重写。它的研究价值来自与黄金尺度、二元分裂电荷和 observer completion 的兼容性。

---

## 1. 三种压缩必须分开

### 1.1 阿贝尔化

素数是正有理数乘法群的自由生成元：

\[
\mathbb Q_{>0}^{\times}\cong\bigoplus_p\mathbb Z[p].
\]

从有序素数观察词进入该群会删除顺序，只保留素因子指数。

### 1.2 字符投影

普通 zeta 对应平凡字符通道。对黄金二次域，非平凡字符 `chi_5` 读取 split/inert 电荷。联合通道

\[
(\mathbf 1,\chi_5)
\]

是群 `C_2` 上的完整 Fourier 坐标。

### 1.3 反射偶化

completed reflection

\[
\mathcal R(s)=1-\overline{s}
\]

把法向偏差 `delta` 变为 `-delta`。对称标量观察会消去奇通道，同时保留乘积、平方和曲率等偶不变量。

---

## 2. 黄金尺度圆

定义黄金正定向周期

\[
L_\varphi=2\log\varphi.
\]

对正尺度 `x`，定义未取商坐标

\[
\eta_\varphi(x)=\frac{\log x}{L_\varphi}.
\]

机器定理证明

\[
\eta_\varphi(xy)=\eta_\varphi(x)+\eta_\varphi(y)
\]

以及

\[
\eta_\varphi(\varphi^2x)=\eta_\varphi(x)+1.
\]

因此取模 `Z` 后得到黄金尺度圆。当前 Lean owner 保留未取商实坐标，以避免把 circle quotient 的拓扑接口与本批代数定理混在一起。

其 Fourier 基频为

\[
\omega_\varphi=\frac{2\pi}{L_\varphi}=\frac{\pi}{\log\varphi}.
\]

机器闭合的精确桥为

\[
2\pi k\,\eta_\varphi(x)
=
(k\omega_\varphi)\log x.
\]

这解释了黄金圆的 Fourier 模式为什么对应 Mellin 变量的垂直平移。

---

## 3. 相同电荷与不同观察者

设壳层读出为

\[
q_r:X\to Y_r,
\]

并存在电荷投影

\[
c_r:Y_r\to C
\]

满足

\[
c_r\circ q_r=\chi.
\]

所有壳层读取同一个电荷 `chi`。它们仍可保留不同残余信息，因此 kernel 不必相同。机器反模型使用一个只读取 Boolean charge 的粗壳和一个同时保留 residual bit 的细壳，证明共同电荷不推出观察者相同。

---

## 4. 黄金 `C_2` 电荷层析

令 split 与 inert 信号为 `(S,I)`。定义

\[
N=S+I,
\qquad
C=S-I.
\]

反演为

\[
S=\frac{N+C}{2},
\qquad
I=\frac{N-C}{2}.
\]

这里 `N` 是中性通道，`C` 是二次电荷通道。该反演已经机器证明。

对单个未分歧素数，`chi_5(p)=+1` 给 split 指示器，`chi_5(p)=-1` 给 inert 指示器。`p=5` 是分歧通道，需要单独保留。

---

## 5. 黄金局部 Euler 三分律

令形式局部变量为 `X`，定义

\[
D_\chi(X)=(1-X)(1-\chi X).
\]

机器证明

\[
\begin{aligned}
D_{+1}(X)&=(1-X)^2,\\
D_{-1}(X)&=1-X^2,\\
D_0(X)&=1-X.
\end{aligned}
\]

它们分别对应 split、inert、ramified 三种黄金局部类型。仓库已有 prime classification 证明素数的黄金分裂类型由 `p mod 5` 决定。本批新增 residue-to-charge-to-Euler-denominator 的桥接 owner。

---

## 6. 黄金临界半径

对复变量 `s` 定义

\[
b(s)=\Re(s)-\frac12
\]

和黄金临界半径

\[
R_\varphi(s)=\exp(L_\varphi b(s)).
\]

机器证明

\[
R_\varphi(s)=1
\iff
\Re(s)=\frac12.
\]

临界反射满足

\[
b(\mathcal R s)=-b(s)
\]

以及

\[
R_\varphi(\mathcal R s)=R_\varphi(s)^{-1}.
\]

因此每一对反射伙伴都满足

\[
R_\varphi(s)R_\varphi(\mathcal R s)=1.
\]

这只是成对平衡。逐点中性要求

\[
R_\varphi(s)=1.
\]

所以函数方程型对称提供 pairwise balance，Riemann 型临界线命题要求 pointwise neutrality。Lean 中已经给出显式反例，说明乘积为一不能推出每个因子为一。

---

## 7. 与 RH 和 GRH 的精确边界

对任意候选零点集 `Z`，机器定理证明

\[
\forall s\in Z,\ \Re(s)=\frac12
\iff
\forall s\in Z,\ R_\varphi(s)=1.
\]

当 `Z` 被实例化为 completed zeta 或某个 completed `L`-函数的非平凡零点集时，这成为对应 RH 或 GRH 的等价坐标表达。该实例化本身需要仓库中严格定义的 completed function、zero predicate 和 trivial-zero exclusion。

本批不把坐标等价冒充为零点位置证明。

---

## 8. 后续解析桥

下列内容保留为后续形式化目标：

1. 在绝对收敛半平面中建立有限或无限黄金壳测度的 Fourier 系数与 `-L'/L` 垂直采样之间的定理；
2. 形式化 `L(1,chi_5)=2 log(phi)/sqrt(5)`，并连接黄金 Möbius Lyapunov 指数；
3. 将 explicit formula 实现为 prime-shell test space 与 zero-spectrum distribution 之间的连续线性泛函恒等式；
4. 构造足够完备的 golden Weil frame，并证明其正性是否等价于完整 Weil criterion；
5. 证明任何新增传递算子的酉性或自伴随性，不能从 determinant 的成对平衡直接推出。

---

## 9. 机器 owner

```text
D5/S3/Observer/GoldenPrimeCircle/
  GoldenScaleCircle.lean
  GoldenVerticalSampling.lean
  SharedChargeDifferentShells.lean

D5/S3/PrimeForms/GoldenEuler/
  GoldenChargeTomography.lean
  GoldenLocalEulerTrichotomy.lean
  GoldenResidueChargeBridge.lean

D5/S3/Weil/GoldenCriticalSpectrum/
  GoldenCriticalRadius.lean
  GoldenReflectionTransfer.lean
```

---

## [PR #4221] PRIME_FREQUENCY_PHASE_FLOW_AND_OBSERVER_TIME

# 素数频率相位流、傅立叶对偶与观察者时间
## 色散给出频率分解，记忆次序给出可观察的历时

**文档地位。** 本文解释 Lean 节点

`D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow`

及其三个主定理：

- `fourier_phase_character_laws`；
- `ordered_phase_product_collapse`；
- `finite_fourier_synthesis_laws`。

机器事实以 Lean 声明为准。本文将“色散以后是不是通过傅立叶变换出现时间”拆成可证明的傅立叶角色、标量次序遗忘和记忆提升三个部分。

---

# 1. 本轮机器对象

Lean 定义傅立叶相位

\[
\boxed{
\chi_\omega(t)=e^{-it\omega}.
}
\]

这里 \(t,\omega\in\mathbb R\)，值位于复数单位圆。对自然数地址 \(n\)，进一步定义

\[
\boxed{
\chi_n^{\log}(t)
=
\chi_{\log n}(t)
=
e^{-it\log n}.
}
\]

当地址是素数 \(p\) 时，这正是

\[
p^{-\sigma-it}
=
p^{-\sigma}e^{-it\log p}
\]

中的振荡部分。

对有限通道类型 \(P\)，振幅 \(a_p\in\mathbb C\) 和频率 \(\omega_p\in\mathbb R\)，Lean 定义有限傅立叶合成

\[
\boxed{
S(t)=\sum_{p\in P}a_p e^{-it\omega_p}.
}
\]

这是一条有限谱线信号。本文未定义一般 \(L^1\) 或 \(L^2\) 傅立叶变换，也未使用傅立叶反演或 Plancherel 定理。

---

# 2. 时间作为频率的对偶参数

Lean 证明

\[
\boxed{
\chi_\omega(0)=1,
}
\]

以及

\[
\boxed{
\chi_\omega(t+u)
=
\chi_\omega(t)\chi_\omega(u).
}
\]

因此固定 \(\omega\) 后，映射

\[
t\longmapsto\chi_\omega(t)
\]

是加法群 \((\mathbb R,+)\) 到单位圆乘法群的角色。这里的 \(t\) 就是傅立叶对偶中的原变量。频率 \(\omega\) 标记该原变量上的角色。

同一个核也满足

\[
\boxed{
\chi_{\omega+\nu}(t)
=
\chi_\omega(t)\chi_\nu(t).
}
\]

所以固定 \(t\) 后，它对频率变量同样是加法角色。Lean 还证明

\[
\boxed{
\chi_\omega(t)=\chi_t(\omega),
}
\]

因为数值上只出现双线性配对 \(t\omega\)。这个对称性表示傅立叶核中的数值互易，不表示时间和频率在模型中具有相同语义。

因此最准确的回答是：

\[
\boxed{
\text{色散识别频率通道，傅立叶配对使这些通道随参数 }t\text{ 形成相位流。}
}
\]

时间不是由“把颜色排了一个顺序”自动制造出来。它来自一个已经存在的加法参数群及其傅立叶角色。如果只给出无序频率集合 \(\{\omega_p\}\)，还没有时间原点、时间方向或因果箭头。

---

# 3. 单位圆与环面

Lean 证明

\[
\boxed{
|\chi_\omega(t)|=1.
}
\]

所以单个通道沿 \(U(1)\) 运动。有限通道族

\[
\bigl(\chi_{\omega_p}(t)\bigr)_{p\in P}
\]

沿环面

\[
\boxed{U(1)^P}
\]

形成一参数轨道。

这给“白光色散为多种颜色”一个精确版本：整体信号被分解为多个频率角色，每个角色在自己的圆相位上旋转，联合状态位于相位环面。

当 \(\omega_p=\log p\) 时，轨道是

\[
\boxed{
t\longmapsto
\left(e^{-it\log p}\right)_{p\in P}.}
\]

其中 \(t\) 是 zeta 竖直方向的虚部坐标，也可以称为谱时间。它不是未经额外解释即可认定的物理时间。

---

# 4. 色散次序本身会不会产生时间

本轮最关键的边界定理考虑一个频率列表

\[
\Omega=[\omega_1,\ldots,\omega_m]
\]

和按列表书写的标量相位乘积

\[
\Pi_\Omega(t)
=
\prod_{j=1}^m e^{-it\omega_j}.
\]

Lean 证明

\[
\boxed{
\Pi_\Omega(t)
=
e^{-it\sum_j\omega_j}.
}
\]

右侧只依赖频率总和。因此在标量复数层：

\[
\boxed{
\text{先 }\omega_p\text{ 后 }\omega_q
=
\text{先 }\omega_q\text{ 后 }\omega_p.
}
\]

标量傅立叶相位能够表示时间演化，却无法记录通道经过的先后次序。换句话说：

\[
\boxed{
\text{傅立叶时间}
\neq
\text{序列历史}.
}
\]

这恰好解释了为什么前面的记忆提升是必要的。若更新仍在复数乘法中，所有局部相位交换，路径历史被压缩成频率总和。把局部因子提升为上三角更新、半直积或其他非交换作用以后，才可能出现

\[
U_qU_p-U_pU_q
\]

以及对应的 swap curvature。

所以存在两种“次序”：

1. **谱次序。** 按大小排列 \(\log p\) 或按索引列出频率。这是一种表示选择，标量傅立叶核不保存该排列。
2. **作用次序。** 观察器先接受通道 \(p\)，随后接受通道 \(q\)。若记忆更新不交换，该次序形成可观察的历时。

第二种次序才与 chronology、路径和 holonomy 直接有关。

---

# 5. 有限傅立叶合成中的时间平移

Lean 对

\[
S(t)=\sum_pa_p\chi_{\omega_p}(t)
\]

证明精确平移律

\[
\boxed{
S(t+u)
=
\sum_p
\bigl(a_p\chi_{\omega_p}(t)\bigr)
\chi_{\omega_p}(u).
}
\]

每个频率通道在时间平移 \(u\) 下乘以自己的相位因子。频率不同意味着平移以后积累的相位不同。这就是通常意义上的相位色散。

Lean 同时证明

\[
\boxed{
|S(t)|
\le
\sum_p|a_p|.
}
\]

因为所有相位因子模长为一，时间流只旋转每个通道，不改变单通道振幅。整体振幅的变化来自通道之间的相长和相消干涉。

---

# 6. 时间、历时与时间箭头

当前真源允许区分三层。

## 6.1 参数时间

\[
t\in\mathbb R
\]

给出一参数群。正负时间均存在，演化可逆。傅立叶角色属于这一层。

## 6.2 观察历时

一串更新

\[
U_{p_m}\cdots U_{p_2}U_{p_1}
\]

记录观察器依次吸收通道的历史。更新不交换时，改变顺序会改变最终记忆状态。这一层由 holonomy 和曲率测量。

## 6.3 时间箭头

时间箭头需要更强结构，例如：

- 只有正时间的半群；
- 不可逆压缩；
- 熵或缺陷能量的单调性；
- 信息丢失；
- 边界条件选择。

傅立叶角色和非交换次序本身都不自动证明时间箭头。它们分别提供可逆时间参数和可观察历时。

因此你的直觉可以校准为

\[
\boxed{
\text{色散}
\longrightarrow
\text{频率角色}
\longrightarrow
\text{可逆谱时间},
}
\]

以及

\[
\boxed{
\text{记忆提升}
+
\text{非交换作用次序}
\longrightarrow
\text{可观察历时}.
}
\]

将二者组合并再加入耗散或单调性，才可能形成时间箭头。

---

# 7. 与前两条 holonomy 真源的连接

上一条真源给出有限交换缺陷能量

\[
\mathcal E^{\mathrm{hol}}
=
\sum_{p,q}\|C_{p,q}\|^2.
\]

本轮给每个通道加入时间相位

\[
z_p(t)=e^{-it\omega_p}.
\]

下一条自然定义是相位扭曲的局部更新

\[
\boxed{
\widetilde U_p(t)
=
U_p\cdot z_p(t)
}
\]

或在记忆注入中写成

\[
\boxed{
b_p(t)=z_p(t)b_p.}
\]

随后定义时间依赖曲率

\[
\boxed{
C_{p,q}(t)
=
(a-\lambda_q)b_p(t)
-
(a-\lambda_p)b_q(t).
}
\]

它会同时测量：

- residual 幅度失配；
- prime-frequency 相位失配；
- 观察器更新次序失配。

由于 \(|z_p(t)|=1\)，单通道范数不变；曲率能量随 \(t\) 的变化来自通道之间的相对相位。相对频率是

\[
\omega_p-\omega_q.
\]

在素数特化下，它成为

\[
\boxed{
\log p-\log q
=
\log\frac pq.
}
\]

因此 pairwise holonomy 的时间振荡自然由素数比值的对数频率控制。

该相位扭曲曲率尚未在本轮 Lean 文件中定义。它应形成下一节点 `PhaseTwistedStableSwapCurvature`。

---

# 8. 与 RH 的关系

在 zeta 的 Euler 侧，素数通道携带频率 \(\log p\)。在显式公式和傅立叶分析中，测试函数在这些频率上取值，零点则出现在对应的全局谱表达中。

本轮冻结了最底层的动力结构：

\[
\boxed{
\log p
\longleftrightarrow
e^{-it\log p}.
}
\]

它解释了为什么虚部坐标 \(t\) 可以被视为 prime-frequency flow 的谱时间，也说明仅靠标量 Euler 相位无法留下素数通道次序。为了让次序参与 RH 路线，必须通过记忆提升将通道作用非交换化，再证明时间依赖 holonomy 能量与零点侧离线奇能量之间的忠实桥。

预期链条变成

\[
\boxed{
\begin{aligned}
&\text{prime log-frequency characters}
\\
&\Longrightarrow
\text{phase-twisted memory updates}
\\
&\Longrightarrow
\text{time-dependent holonomy energy}
\\
&\Longrightarrow
\boxed{\text{explicit-formula faithful domination}}
\\
&\Longrightarrow
\text{off-line odd zero energy}.
\end{aligned}
}
\]

其中方框仍是核心缺口。傅立叶角色本身不定位零点，也不把 \(t\) 自动解释为物理时间。

---

# 9. 下一真源排序

当前最自然的推进顺序是：

1. `PhaseTwistedStableSwapCurvature`。把 \(e^{-it\omega_p}\) 写入稳定 residual 注入，推导精确相位扭曲曲率分解和范数界。
2. `FinitePhaseCoherenceIdentity`。证明 pairwise 相位色散能量与共同模态相干能量的守恒恒等式。
3. `FourierPhaseGenerator`。形式化
   \[
   \frac{d}{dt}e^{-it\omega}=-i\omega e^{-it\omega},
   \]
   把频率识别为时间流生成元。
4. `ResonanceConditionedOriginDispersion`。将 holonomy 能量运输到观察起源色散。
5. `PrimeArchimedeanHolonomyDomination`。通过显式公式连接 prime-side 时间曲率与 zero-side 离线奇能量。

第一条把用户提出的“色散、次序、时间”直接接回已有 holonomy 路线。第三条会给出频率作为时间生成元的机器版本。

---

# 10. 严格非主张

本轮不主张：

- 已定义完整连续傅立叶变换；
- 已证明傅立叶反演或 Plancherel；
- 频率排列本身产生时间；
- 已得到时间方向或不可逆性；
- zeta 虚部已经等同于物理时间；
- 相位扭曲 holonomy 已经支配零点能量；
- 已定位任何 zeta 零点；
- 已证明 RH。

本轮机器真源是

\[
\boxed{
\text{Fourier character time flow}
+
\text{scalar order collapse}
+
\text{finite synthesis laws}.
}

---

## [PR #4222] PHASE_TWISTED_HOLONOMY_AND_RELATIVE_PRIME_TIME

# 相位扭曲 holonomy 与相对素数时间
## 把傅立叶谱时间写入记忆通道后的第一条定量真源

**文档地位。** 本文解释 Lean 节点

`D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature`

及其主要声明：

- `phase_twisted_channel_norm`；
- `relative_phase_reconstruction`；
- `relative_log_address_phase_reconstruction`；
- `phase_twisted_curvature_zero_time`；
- `phase_twisted_stable_swap_curvature_bound`；
- `phase_twisted_finite_holonomy_energy_bound`。

机器事实以 Lean 声明为准。本文说明傅立叶参数时间如何进入非交换观察历时，并区分已经证明的统一能量界与尚未证明的同步、耗散和 prime-zero 桥。

---

# 1. 从频率角色到时间依赖记忆注入

前一节点定义

\[
\chi_\omega(t)=e^{-it\omega}.
\]

现在给每个通道 \(p\) 配置频率 \(\omega_p\) 和记忆向量 \(v_p\)，定义相位扭曲通道

\[
\boxed{
\widetilde v_p(t)
=
\chi_{\omega_p}(t)v_p
=
e^{-it\omega_p}v_p.
}
\]

若 residual 为 \(r_p\)，相应记忆注入变成

\[
\boxed{
\widetilde b_p(t)
=
r_p\widetilde v_p(t)
=
r_pe^{-it\omega_p}v_p.
}
\]

稳定通道 swap curvature 因此成为

\[
\boxed{
\widetilde C_{p,q}(t)
=
\bigl(a-(1+r_q)\bigr)r_p e^{-it\omega_p}v_p
-
\bigl(a-(1+r_p)\bigr)r_q e^{-it\omega_q}v_q.
}
\]

这里的 \(t\) 是傅立叶角色的一参数群坐标。通道经过观察器的先后顺序仍由记忆更新的乘法次序表达。两个结构在该定义中第一次同时出现：

\[
\boxed{
\text{spectral time phase}
+
\text{memory-order curvature}.
}
\]

---

# 2. 单位相位不会放大局部通道

Lean 证明

\[
\boxed{
\|\widetilde v_p(t)\|
=
\|v_p\|.
}
\]

原因是

\[
|e^{-it\omega_p}|=1.
\]

所以傅立叶时间流在每个单通道上是酉旋转。它改变相位，不改变通道振幅。

这一点很重要。任何随时间发生的总能量变化只能来自：

- 通道之间的相对相位；
- 不同残差和通道向量的组合；
- 记忆更新的非交换结构；
- 后续另行加入的耗散或增益。

单个傅立叶相位自身不产生耗散。

---

# 3. 真正可观察的是相对频率

Lean 证明

\[
\boxed{
\chi_{\omega_p-\omega_q}(t)
\chi_{\omega_q}(t)
=
\chi_{\omega_p}(t).
}
\]

因此两通道之间的相对相位由

\[
\boxed{
\Delta\omega_{p,q}
=
\omega_p-\omega_q
}
\]

生成。

对自然数地址使用

\[
\omega_n=\log n,
\]

Lean 证明无除法版本

\[
\boxed{
e^{-it(\log p-\log q)}e^{-it\log q}
=
e^{-it\log p}.}
\]

若另外假设地址为正，则纸面上可以写成

\[
\log p-\log q
=
\log\frac pq.
\]

所以 prime pair 的相对频率是

\[
\boxed{
\Delta\omega_{p,q}
=
\log p-\log q.
}
\]

这比单独的 \(\log p\) 更接近 swap curvature 的自然变量，因为曲率本来就是一个两通道量。

因此“色散产生时间”的更精确版本是：

\[
\boxed{
\text{频率差异}
\Longrightarrow
\text{相对相位随 }t\text{ 累积}
\Longrightarrow
\text{两通道干涉随 }t\text{ 改变}.
}
\]

---

# 4. 零时间切片恢复原始观察器

Lean 证明

\[
\boxed{
\widetilde C_{p,q}(0)
=
C_{p,q}.
}
\]

因为所有通道在 \(t=0\) 时满足

\[
\chi_{\omega_p}(0)=1.
\]

这把原来的静态 holonomy 真源识别为时间依赖系统的零时间切片。静态曲率并未被抛弃，它现在成为一参数曲率族的基点。

---

# 5. 精确相位扭曲 residual 分解

Lean 证明

\[
\boxed{
\begin{aligned}
\widetilde C_{p,q}(t)
={}&
(a-1)
\left(
r_p\widetilde v_p(t)
-r_q\widetilde v_q(t)
\right)
\\
&+
r_pr_q
\left(
\widetilde v_q(t)
-
\widetilde v_p(t)
\right).
\end{aligned}
}
\]

第一项是一阶 residual 注入失配。第二项是双 residual 修正。时间只通过两个旋转通道进入。

这给后续分析两个分解方向：

1. 固定 residual 深度，研究 \(t\) 上的相位干涉；
2. 固定谱时间，研究 extraction 深度上 residual envelope 的衰减。

最终需要处理一个双参数极限或统一界：

\[
(r,t)
\longmapsto
\widetilde C^{\langle r\rangle}_{p,q}(t).
\]

---

# 6. pairwise 曲率界在时间上统一

若

\[
\|v_p\|\le1,
\qquad
\|v_q\|\le1,
\]

Lean 证明

\[
\boxed{
\|\widetilde C_{p,q}(t)\|
\le
\|a-1\|
\bigl(\|r_p\|+\|r_q\|\bigr)
+
2\|r_p\|\|r_q\|
}
\]

对每个 \(t\in\mathbb R\) 成立。

若

\[
\|r_p\|,\|r_q\|\le\varepsilon,
\]

则

\[
\boxed{
\|\widetilde C_{p,q}(t)\|
\le
2\|a-1\|\varepsilon
+2\varepsilon^2.
}
\]

右侧不含 \(t\)。因此 residual envelope 一旦收敛，就可以得到对整个谱时间轴统一的 pairwise 曲率控制，前提是通道向量的单位界本身统一成立。

这是本轮最重要的定量结果：

\[
\boxed{
\text{unitary spectral-time twisting does not consume residual control.}
}
\]

---

# 7. 有限 holonomy 能量的统一时间界

对有限通道集 \(P\)，Lean 定义

\[
\boxed{
\widetilde{\mathcal E}^{\mathrm{hol}}_P(t)
=
\sum_{p,q\in P}
\|\widetilde C_{p,q}(t)\|^2.
}
\]

若 \(|P|=M\)，所有通道单位有界，所有 residual 由同一 \(\varepsilon\ge0\) 控制，Lean 证明

\[
\boxed{
0
\le
\widetilde{\mathcal E}^{\mathrm{hol}}_P(t)
\le
M^2
\left(
2\|a-1\|\varepsilon
+2\varepsilon^2
\right)^2
}
\]

对所有谱时间成立。

同时：

\[
\boxed{
\widetilde{\mathcal E}^{\mathrm{hol}}_P(t)=0
\iff
\forall p,q\in P,
\widetilde C_{p,q}(t)=0.
}
\]

所以该能量在每个时间切片上仍然是忠实的非负缺陷量。

需要注意，统一上界不表示能量对时间恒定。各项内部存在不同相位，\(\widetilde C_{p,q}(t)\) 的范数可以随时间变化。机器结论只说明它始终被同一个 residual envelope 控制。

---

# 8. 现在出现了哪一种时间

当前系统已有两个严格结构。

## 8.1 可逆谱时间

\[
t\mapsto e^{-it\omega_p}
\]

是加法群的一参数酉作用。它允许正时间和负时间，天然可逆。

## 8.2 可观察的作用历时

\[
U_q(t)U_p(t)
\quad\text{与}\quad
U_p(t)U_q(t)
\]

在记忆提升以后可以不同。swap curvature 记录这种路径差异。

二者结合得到“随谱时间演化的观察历时”。这里仍没有时间箭头，因为没有证明

\[
\frac{d}{dt}
\widetilde{\mathcal E}^{\mathrm{hol}}_P(t)
\le0
\]

或任何不可逆半群性质。

时间箭头需要再加入耗散、粗粒化、单调 Lyapunov 量、只允许正时间的边界条件，或其他选择机制。

---

# 9. 与共振压平的关系

相位扭曲以后，通道同步意味着相对相位

\[
e^{-it(\omega_p-\omega_q)}
\]

在有效观察窗口内接近一，同时 residual 注入和通道起源也需要兼容。

仅出现某个时刻的相位重合不足以给出全局压平。更强目标可能是：

\[
\boxed{
\int_I
\widetilde{\mathcal E}^{\mathrm{hol}}_P(t)w(t)\,dt
\longrightarrow0
}
\]

或

\[
\boxed{
\sup_{t\in I}
\widetilde{\mathcal E}^{\mathrm{hol}}_P(t)
\longrightarrow0.
}
\]

本轮统一 residual 界支持第二种路线，因为右侧与 \(t\) 无关。实际结论仍依赖 residual envelope decay。

下一条 `FinitePhaseCoherenceIdentity` 应负责把 pairwise 相位差能量与共同相干模态能量连接起来。随后可以研究该相干能量在时间平均、测试函数加权和显式公式下如何投影到零点侧。

---

# 10. 与 RH 路线的更新连接

当前 prime-side 链条已经变成

\[
\boxed{
\begin{aligned}
&\log p\text{ frequency channels}
\\
&\Longrightarrow
e^{-it\log p}\text{ spectral-time phases}
\\
&\Longrightarrow
\widetilde C_{p,q}(t)\text{ phase-twisted swap curvature}
\\
&\Longrightarrow
\widetilde{\mathcal E}^{\mathrm{hol}}_P(t)
\text{ finite defect energy}
\\
&\Longrightarrow
\boxed{\text{explicit-formula faithful domination}}
\\
&\Longrightarrow
\text{off-line odd zero energy}.
\end{aligned}
}
\]

方框仍是核心缺口。当前新内容提供一个适合被测试函数积分的时间依赖 prime-side 能量候选。它尚未证明该积分等于、支配或逼近任何 zero-side 量。

一个关键新观察是：显式公式中的测试函数本来就在对 \(t\) 或其傅立叶对偶进行加权。现在 holonomy 也成为 \(t\) 的函数，因此可以第一次提出类型正确的桥：

\[
\boxed{
\mathcal E_{\mathrm{off}}^{\mathrm{odd}}(g)
\le
A_g
\int_{\mathbb R}
\widetilde{\mathcal E}^{\mathrm{hol}}_P(t)
\,d\mu_g(t)
+R_{P,g}.
}
\]

其中 \(\mu_g\) 必须由允许的测试函数类产生，\(R_{P,g}\) 必须显式记账并可控。该不等式目前只是下一阶段的目标类型。

---

# 11. 下一真源

当前最自然的下一节点是：

1. `FinitePhaseCoherenceIdentity`。把
   \[
   \sum_{p,q}w_pw_q|z_p-z_q|^2
   \]
   写成最大总能量减共同模态能量。
2. `FourierPhaseGenerator`。证明频率是谱时间流的生成元。
3. `TimeAveragedPhaseHolonomyEnergy`。定义测试函数加权的时间积分能量并证明非负性和 residual 上界。
4. `ResonanceConditionedOriginDispersion`。把时间依赖曲率运输到观察起源色散。
5. `PrimeArchimedeanHolonomyDomination`。尝试建立显式公式忠实桥。

第三条会把当前有限点态界变为适合进入 explicit formula 的积分对象。

---

# 12. 严格非主张

本轮不主张：

- 相位已经同步；
- holonomy 能量随时间单调；
- 已构造时间箭头；
- residual envelope 已经衰减；
- 时间积分能量已经定义；
- prime-side 能量已经等于或支配 zero-side 能量；
- 已定位任何 zeta 零点；
- 已证明 RH。

本轮机器真源是

\[
\boxed{
\text{unitary prime-frequency phase twist}
\Longrightarrow
\text{time-dependent stable curvature}
\Longrightarrow
\text{time-uniform finite residual-energy bound}.
\]

## [PR #4233] NEGATIVITY_REFLECTION_TIME_THEORY

# 负性、负平方与负时间理论
## 反射分裂、观察锥与时间定向研究卷；不是 RH 证明声明

仓库取阅基线：`the-omega-institute/trureturing` 的 `dev` 提交 `23747a66fdb518fd82dbccc6ca5fca0126d6d33c`。本卷与同一 PR 中的 Lean 真源共同提交。

本卷把“负性”“负平方”“负时间”拆成可独立审计的数学角色。核心原则是：负号不自带统一含义。它总是相对于一个正锥、允许支撑、时间定向、谱稳定域或二次型而出现。

文中使用三种标签：

- `[formalized-here]`：由同一 PR 的 Lean 真源机器证明。
- `[repo-derived]`：由现有 `dev` 真源支持。
- `[research-target]`：由已闭合事实导出的下一条定义或定理目标，尚未冒充内核结论。

## 一、负性是相对于正锥的越界

设对象空间为 $X$，允许对象形成正锥 $C\subseteq X$。若存在对偶观察器 $\ell$ 满足

$$
\ell(c)\ge 0\qquad(c\in C),
$$

但对某个对象 $x$ 有

$$
\ell(x)<0,
$$

则 $\ell$ 是 $x$ 离开正锥的负性证书：

$$
\operatorname{NegativeWitness}_{C}(x)
\;:\Longleftrightarrow\;
\exists\ell\in C^{\vee},\ \ell(x)<0.
$$

以下对象必须保持强类型区分：

1. 负标量：$a<0$。
2. 负支撑：正质量位于禁止区域，例如 $x<0$。
3. 负质量：测度系数本身为负。
4. 负方向：存在 $v\ne0$ 使二次型 $Q(v)<0$。
5. 负指数：最大负定子空间的维数。
6. 负时间：相对于选定正向时间锥的反向参数或逆向完成。
7. 负频率：Fourier 相位的反向绕行，它不等于过去时间。

这些概念之间可以建立运输定理，不能直接互相替换。

## 二、负平方不是实数平方小于零

对实数 $\delta$，算术平方始终满足

$$
\delta^2\ge0.
$$

本路线所说的“负平方”是

$$
-\delta^2,
$$

即先形成反射不变量 $\delta^2$，再用负号记录该量进入了一个带符号的结构位置。

在 RH 的法向坐标中，令

$$
\delta=\Re\rho-\frac12.
$$

函数方程反射交换 $\delta$ 与 $-\delta$。反射商空间无法保留左右标签，只能保留偏移大小 $\delta^2$。若还需要记录轨道位于临界线外，则候选有符号法向坐标为

$$
\boxed{x_{\perp}=-\delta^2.}
$$

负号表达“离线扇区”或“禁止支撑扇区”，并不表示平方运算产生负数。

## 三、术语校正：负平方是行列式，不是标准多项式判别式

考虑反射生成率对

$$
+\delta,\qquad-\delta.
$$

一阶和完全抵消：

$$
\delta+(-\delta)=0.
$$

二阶乘积留下：

$$
\delta(-\delta)=-\delta^2.
$$

若把生成元写成

$$
A_{\delta}=\begin{pmatrix}\delta&0\\0&-\delta\end{pmatrix},
$$

则

$$
\operatorname{tr}A_{\delta}=0,
\qquad
\det A_{\delta}=-\delta^2,
\qquad
A_{\delta}^2=\delta^2I.
$$

对形式谱变量 $r$：

$$
(r-\delta)(r+\delta)=r^2-\delta^2.
$$

因此负量 $-\delta^2$ 是反射生成元的有符号行列式，也是特征多项式的常数项。本卷把它定义为

$$
\boxed{
\operatorname{ReflectionPairSignedDeterminant}(\delta)
=-\delta^2.
}
$$

标准二次多项式判别式必须单独计算。对

$$
r^2-\delta^2,
$$

其标准判别式为

$$
\boxed{
\Delta_{\mathrm{poly}}
=0^2-4\cdot1\cdot(-\delta^2)
=4\delta^2.
}
$$

[formalized-here] 同一 Lean 节点同时证明 $-\delta^2$ 的有符号行列式身份和 $4\delta^2$ 的标准判别式身份，防止术语混同。

## 四、增长与衰减是负平方的有向时间实现

定义一对指数分支

$$
g_{+}(t)=e^{\delta t},
\qquad
g_{-}(t)=e^{-\delta t}.
$$

[formalized-here] 它们满足

$$
g_{+}(-t)=g_{-}(t),
\qquad
g_{-}(-t)=g_{+}(t),
$$

以及

$$
g_{+}(t)g_{-}(t)=1.
$$

因此时间反演不会删除分裂。它交换扩张与收缩分支。

[formalized-here] 当 $\delta>0$ 且 $t>0$ 时：

$$
g_{+}(t)>1,
\qquad
g_{-}(t)<1.
$$

在负时间方向，两个角色交换。反射对整体没有预先选定唯一稳定箭头。稳定性依赖观察者声明的正向时间锥。

## 五、反射增长对位于正双曲线上

由乘积守恒：

$$
g_{+}(t)g_{-}(t)=1,
$$

反射增长对落在正双曲线

$$
xy=1,
\qquad x>0,\ y>0
$$

上。

定义偶、奇坐标

$$
E_{\delta}(t)
=\frac{g_{+}(t)+g_{-}(t)}{2},
$$

$$
O_{\delta}(t)
=\frac{g_{+}(t)-g_{-}(t)}{2}.
$$

则预期有

$$
E_{\delta}(t)=\cosh(\delta t),
\qquad
O_{\delta}(t)=\sinh(\delta t),
$$

以及

$$
\boxed{
E_{\delta}(t)^2-O_{\delta}(t)^2=1.
}
$$

时间反演保持偶坐标并翻转奇坐标：

$$
E_{\delta}(-t)=E_{\delta}(t),
$$

$$
O_{\delta}(-t)=-O_{\delta}(t).
$$

[research-target] 这组等式应形成 `ReflectedGrowthPairEvenOddDecomposition`。它将把“时间方向信息”精确定位到奇通道，而把“反射不变量”定位到偶通道和负平方行列式。

## 六、对称观察商丢失时间箭头

定义分支遗忘读出

$$
S_{\delta}(t)=g_{+}(t)+g_{-}(t).
$$

[formalized-here] 有

$$
S_{\delta}(-t)=S_{\delta}(t).
$$

因此该观察器无法区分 $t$ 与 $-t$。有向二分支状态仍保留时间方向，对称商只保留时间反演轨道

$$
\{t,-t\}.
$$

[research-target] 应进一步机器证明：当 $\delta\ne0$ 时，有向映射

$$
t\longmapsto(g_{+}(t),g_{-}(t))
$$

是单射，而对称读出在任意 $t\ne0$ 处都发生

$$
S_{\delta}(t)=S_{\delta}(-t),
\qquad
t\ne-t.
$$

这会给出一个最小的 observer theorem：

$$
\boxed{
\text{有向完成保留负时间，分支遗忘商丢失时间方向。}
}
$$

加入奇通道 $O_{\delta}$ 后，可以恢复方向。对 $\delta>0$，其符号预期与 $t$ 的符号一致。

## 七、负时间的五种角色

必须区分：

1. $t<0$：坐标位于选定原点之前。
2. $t\mapsto-t$：时间反演 involution。
3. $U(-t)=U(t)^{-1}$：可逆动力学的逆向演化。
4. $\omega<0$：负频率或反向相位绕行。
5. 度量中的 $-dt^2$：时间方向在不定二次型中的符号。

只有第三项要求演化构成群。耗散、投影、测量与粗粒化通常只给出 $t\ge0$ 的半群。此时负时间是过去完成问题。

若前向观察为

$$
q:X\to Y,
$$

则给定当前读数 $y$ 的全部可能过去为

$$
\operatorname{PastFiber}(y)=\{x\in X:q(x)=y\}.
$$

当 $q$ 非单射时，逆向时间是集合值 completion fiber。加入足够记忆后，提升映射

$$
\widetilde q:X\to Y\times M
$$

可能恢复单射，从而在完成后的状态空间中恢复双向时间。

[research-target] 对当前反射增长对，应定义逐坐标乘法并证明

$$
G_{\delta}(s+t)=G_{\delta}(s)\odot G_{\delta}(t),
$$

$$
G_{\delta}(0)=(1,1),
$$

$$
G_{\delta}(-t)=G_{\delta}(t)^{-1}.
$$

这会把负时间从直觉上的“另一侧”升级为有向完成群中的真实逆元。

## 八、负支撑、负方向与 negative square

对测度

$$
\nu=\sum_jm_j\delta_{x_j},
$$

“负质量”指 $m_j<0$。“负支撑”指 $m_j>0$ 但 $x_j<0$。当前 RH normal-resolvent 路线更自然地把异常放在支撑位置：

$$
m_{\rho}>0,
\qquad
x_{\rho}=-\delta^2<0.
$$

若测试函数 $p$ 在允许支撑 $[0,\infty)$ 上非负，而在 $-\delta^2$ 处为负，则

$$
\int p(x)\,d\nu(x)<0.
$$

这把负支撑运输成负矩，再运输成 Toeplitz、Pick 或 Weil 二次型的负方向。

对于 Hermitian 核 $K$，有限采样矩阵

$$
G_{jk}=K(z_j,z_k)
$$

若存在 $c\ne0$ 使

$$
c^{*}Gc<0,
$$

则出现一个 negative square。负平方指数是最大独立负子空间的维数。它记录系统拥有多少个彼此独立的向下方向。

## 九、负平方是二阶算子的负谱值

令

$$
L=-\frac{d^2}{dt^2}.
$$

对增长分支 $g_{\pm}(t)=e^{\pm\delta t}$，预期有

$$
\frac{d^2}{dt^2}g_{\pm}(t)
=\delta^2g_{\pm}(t),
$$

因此

$$
\boxed{
Lg_{\pm}=-\delta^2g_{\pm}.
}
$$

这给出负平方的谱解释：$-\delta^2$ 是前向增长和衰减模式在算子 $-d^2/dt^2$ 下的共同负谱值。

对振荡模式 $e^{\pm i\gamma t}$，同一算子产生正谱值 $+\gamma^2$。由此出现一个候选三分法：

$$
\begin{array}{c|c|c}
\text{生成元类型}&\text{有符号行列式}&\text{动力学}\
\hline
\text{双曲}&-\delta^2&\text{增长/衰减}\
\text{中性}&0&\text{无分裂}\
\text{椭圆}&+\gamma^2&\text{单位模振荡}
\end{array}
$$

[research-target] 先形式化 `ReflectedGrowthPairSecondOrderSpectrum`，再建立 `EllipticHyperbolicReflectionTrichotomy`。第二条需要复指数或实二维旋转生成元，不能由本轮标量定理直接宣称。

## 十、负平方与 Laplace 时间的桥

对适当的 $u$，有

$$
\frac1{u+x}=\int_0^{\infty}e^{-ut}e^{-xt}\,dt.
$$

若 $x>0$，则 $e^{-xt}$ 在正时间衰减。若 $x=-\delta^2<0$，则

$$
e^{-xt}=e^{\delta^2t}
$$

在正时间增长。总核只有在外加阻尼超过增长率时收敛：

$$
\boxed{
u>\delta^2.}
$$

在该区域：

$$
\boxed{
\int_0^{\infty}e^{-(u-\delta^2)t}\,dt
=\frac1{u-\delta^2}.
}
$$

由此可定义稳定化债务

$$
\boxed{
\operatorname{StabilizationDebt}(-\delta^2)=\delta^2.
}
$$

它是压过负支撑增长所需的最小附加阻尼阈值。

[research-target] `NegativeSquareLaplaceResolvent` 应证明积分值、可积条件和阈值处的极点。比只证明积分公式更重要的是完整刻画：

$$
\operatorname{Integrable}
\left(e^{-(u-\delta^2)t};\ t>0\right)
\quad\Longleftrightarrow\quad
u>\delta^2.
$$

## 十一、与离线零点曲率 dipole 的关系

[repo-derived] 对离线反射对，仓库已有曲率真源

$$
K_{\delta,\gamma}(t)
=2\frac{(t-\gamma)^2-\delta^2}
{((t-\gamma)^2+\delta^2)^2}.
$$

分子

$$
(t-\gamma)^2-\delta^2
$$

是一个不定二次型。区域 $|t-\gamma|<|\delta|$ 为负核心，外部为正翼，总质量为零。故离线缺陷是一种局部重分配。零频率或只读取总积分的观察器无法检测它。

将

$$
\tau=t-\gamma
$$

代入后，符号边界

$$
\tau^2-\delta^2=0
$$

形成两条特征线 $\tau=\pm\delta$。这与反射生成元的特征因子

$$
(r-\delta)(r+\delta)=r^2-\delta^2
$$

具有同一代数骨架。

[research-target] 应建立一个明确的 observer agreement：曲率 dipole 的负核心宽度、反射增长对的双曲率和 signed normal atom 的位置都由同一个参数 $\delta^2$ 控制。只有获得精确等式或带误差运输，这一结构相似性才能承担 RH 路径。

## 十二、本轮形式化边界

同一 PR 的 Lean 真源只冻结以下无条件事实：

1. 交换两个指数分支等于时间反演。
2. 两个分支的乘积恒为一。
3. 反射生成率对的迹为零。
4. 反射对有符号行列式精确等于 $-\delta^2$。
5. 标准二次多项式判别式精确等于 $4\delta^2$。
6. 特征因子为 $r^2-\delta^2$。
7. 在 $\delta>0,t>0$ 时，一支严格扩张，另一支严格收缩。
8. 对称分支和是时间偶函数。

本轮不声明：

- zeta ordinate 是物理时间；
- completed zeta 已经拥有该指数 realization；
- 任意离线零点已经被有限观察器隔离；
- 全局 signed normal spectral measure 已构造；
- 上述一般结构推出 RH。

## 十三、后续 theorem DAG

```text
ReflectedGrowthPairNegativeSquare
        |
        +--> ReflectedGrowthPairTimeGroup
        |          |
        |          v
        |    OrientedTimeRecoverySymmetricTimeLoss
        |
        +--> ReflectedGrowthPairEvenOddDecomposition
        |          |
        |          v
        |    EvenObserverFirstOrderBlindness
        |
        +--> ReflectedGrowthPairSecondOrderSpectrum
        |          |
        |          v
        |    EllipticHyperbolicReflectionTrichotomy
        |
        v
NegativeSquareLaplaceResolvent
        |
        v
SignedNormalSpectralAtom
        |
        v
ChebyshevNegativeSupportSeparator
        |
        v
FiniteMomentNegativeWitness
        |
        v
Toeplitz/Pick/Weil Negative Direction
```

## 十四、下一步优先级

### P0：`ReflectedGrowthPairSecondOrderSpectrum`

机器证明

$$
g_{\pm}''=\delta^2g_{\pm},
\qquad
- g_{\pm}''=-\delta^2g_{\pm},
$$

以及

$$
S_{\delta}'(0)=0,
\qquad
S_{\delta}''(0)=2\delta^2.
$$

该节点直接把有符号行列式接成真实负谱值，并证明对称观察器的一阶盲性与二阶可见性。

### P0：`OrientedTimeRecoverySymmetricTimeLoss`

机器证明有向 pair flow 的群律、负时间逆元、$\delta\ne0$ 时的单射性，以及对称读出的 $t/-t$ 碰撞。该节点把“负时间是 completion fiber”写成最小可复用观察者定理。

### P1：`NegativeSquareLaplaceResolvent`

证明稳定化阈值 $u>\delta^2$、积分 resolvent 和阈值极点。该节点把时间增长接入 signed support、Stieltjes 和 positive-real completion。

### P1：`EllipticHyperbolicReflectionTrichotomy`

引入振荡对与实二维旋转生成元，严格区分正行列式的椭圆振荡、零行列式的中性模式和负行列式的双曲增长/衰减。该节点将为临界线振子与离线径向分裂提供共同分类语言。

## [PR #4243] REFLECTED_ZERO_MODE_PHASE_FLATTENING_THEORY

# 反射零点模式与相位压平理论
## 从临界位移、频率与辅助时间中分离三个反向操作

仓库基线：`the-omega-institute/trureturing` 的 `dev` 分支，分支创建时提交为 `2deefdd8b7de08ef84311b00fed4f60516194fba`。

本卷承接负性、负平方与负时间理论。前一层指出，反射增长率对 `delta` 与 `-delta` 的一阶和为零，有符号行列式为 `-delta^2`。本层进一步把这一通用双曲结构接到仓库已经冻结的 zeta 零点生成元坐标，并严格区分函数方程反射、复共轭和辅助模式时间反演。

本卷不是 RH 证明声明。这里的 `time` 是指数模式参数，不被解释为物理时间。所有关于 completed zeta、Weil 正性和全局谱完成的结论仍需额外桥梁。

## 一、归一化零点生成元

对任意复点

$$
rho=sigma+i gamma,
$$

定义相对临界线的有符号横向位移

$$
delta(rho)=\operatorname{Re}rho-\frac12.
$$

仓库现有 `CriticalDampingGenerator` 在消去统一阻尼平移后留下的标量生成元为

$$
\boxed{
g(rho)=-delta(rho)+i\operatorname{Im}rho.
}
$$

于是定义辅助指数模式

$$
\boxed{
M_rho(t)=\exp(g(rho)t).
}
$$

生成元实部控制幅度变化，虚部控制相位旋转：

$$
\operatorname{Re}g(rho)=-delta(rho),
\qquad
\operatorname{Im}g(rho)=\operatorname{Im}rho.
$$

因此

$$
\overline{g(rho)}=-g(rho)
$$

当且仅当

$$
\operatorname{Re}rho=\frac12.
$$

这与现有零点族级别的 skew-adjoint 判据相容。本层把它提升为任意单点的明确坐标恒等式。

## 二、径向通道与相位通道

定义径向通道

$$
R_rho(t)=\exp(-delta(rho)t),
$$

以及公共相位通道

$$
P_rho(t)=\exp(i\operatorname{Im}(rho)t).
$$

则

$$
\boxed{
M_rho(t)=R_rho(t)P_rho(t).
}
$$

相位通道满足

$$
|P_rho(t)|=1.
$$

所以模式的模长完全由横向位移控制：

$$
|M_rho(t)|=\exp(-delta(rho)t).
$$

定义相位压平观察

$$
\operatorname{Flat}(rho,t)
=M_rho(t)\exp(-i\operatorname{Im}(rho)t).
$$

则精确得到

$$
\boxed{
\operatorname{Flat}(rho,t)=R_rho(t).
}
$$

相位压平没有近似误差，也不需要选择对数分支。它只利用整个函数 `exp` 的乘法恒等式。

## 三、三个容易混淆的反向操作

### 1. 函数方程反射

定义

$$
F(rho)=1-rho.
$$

若 `rho` 的坐标为 `(delta,gamma)`，则

$$
F:(delta,gamma)\mapsto(-delta,-gamma).
$$

生成元满足

$$
g(F(rho))=-g(rho).
$$

因此

$$
\boxed{
M_{F(rho)}(t)=M_rho(-t).
}
$$

函数方程反射在辅助模式层等同于完整生成元的时间反演。它同时翻转径向速率和频率。

### 2. 复共轭

定义

$$
C(rho)=\overline{rho}.
$$

其坐标作用为

$$
C:(delta,gamma)\mapsto(delta,-gamma).
$$

生成元满足

$$
g(C(rho))=\overline{g(rho)}.
$$

模式满足

$$
\boxed{
M_{C(rho)}(t)=\overline{M_rho(t)}.
}
$$

复共轭保留径向增长率，只反转相位绕行方向。它对应负频率，不等同于负时间。

### 3. 同高度临界线镜像

定义

$$
H(rho)=1-\overline{rho}.
$$

其坐标作用为

$$
H:(delta,gamma)\mapsto(-delta,gamma).
$$

它可以写成

$$
H=F\circ C=C\circ F.
$$

生成元满足

$$
g(H(rho))=-\overline{g(rho)}.
$$

相位压平后，`rho` 与 `H(rho)` 的两个径向模式互为倒数：

$$
\boxed{
\operatorname{Flat}(rho,t)\operatorname{Flat}(H(rho),t)=1.
}
$$

这正是离线反射对的增长和衰减双支结构。

## 四、对称方形

三个非平凡变换与恒等变换组成一个 Klein 四群：

$$
\{I,F,C,H\},
\qquad
F^2=C^2=H^2=I,
\qquad
FC=CF=H.
$$

其坐标表为：

| 变换 | 位移 `delta` | 频率 `gamma` | 模式作用 |
| --- | ---: | ---: | --- |
| `I` | `delta` | `gamma` | 原模式 |
| `F` | `-delta` | `-gamma` | 辅助时间反演 |
| `C` | `delta` | `-gamma` | 复共轭 |
| `H` | `-delta` | `gamma` | 同相位的径向互反 |

仓库的 `ZeroData` 已经分别保存 `reflection` 和 `conjugation` 两个零点索引置换。由于零点枚举无重复，两个复平面复合都落到同一个同高度镜像点，从而两个索引置换交换：

$$
\boxed{
R(C(n))=C(R(n)).
}
$$

这里的交换不是额外假设。它由两个零点图像相等和枚举单射性推出。

## 五、临界线的模式含义

当

$$
delta(rho)=0,
$$

径向通道退化为常数一：

$$
R_rho(t)=1.
$$

归一化模式成为纯单位模旋转：

$$
M_rho(t)=\exp(i\gamma t).
$$

因此临界线可以解释为归一化生成元没有径向增长或衰减。离线点则产生一对同相位的互反径向分支。

这个解释与负平方真源相连。若同高度镜像位移为 `delta` 和 `-delta`，对应径向生成率为 `-delta` 和 `delta`，则它们的有符号行列式为

$$
-delta^2.
$$

本层没有重复形式化该行列式，因为相应真源仍在独立 PR 中。本层只冻结从实际零点坐标到径向互反对的精确表示桥。

## 六、形式化边界

同一 PR 的 Lean 真源只建立以下无条件事实：

1. 仓库现有阻尼平移表达式精确化简为 `g(rho)`。
2. `g(rho)` 为 skew 当且仅当 `rho` 位于临界线。
3. `M_rho` 精确分解为径向通道与单位相位通道。
4. 相位压平精确恢复径向通道。
5. 函数方程反射在模式层等于辅助时间反演。
6. 共轭只反转相位频率。
7. 同高度临界线镜像在相位压平后给出互为倒数的径向分支。
8. `ZeroData` 的反射与共轭置换交换。

本层不声明：

- 指数模式参数等于物理时间；
- 所有 `ZeroData` 的构造已经无条件存在；
- completed zeta 是某个有限维动力系统的特征行列式；
- 相位压平本身产生 Weil 或 Pick 负证书；
- 任意离线零点已经被有限测试函数隔离；
- 上述表示桥推出 RH。

## 七、基于形式化真理的下一研究义务

### 1. 二阶谱节点

对径向模式应形式化

$$
\frac{d^2}{dt^2}R_rho(t)=delta(rho)^2R_rho(t),
$$

从而

$$
-\frac{d^2}{dt^2}R_rho(t)=-delta(rho)^2R_rho(t).
$$

这会把有符号行列式 `-delta^2` 升级为实际二阶算子的负谱值，并连接 normal jet。

### 2. 偶奇观察节点

定义

$$
E(t)=\frac{R(t)+R(-t)}2,
\qquad
O(t)=\frac{R(t)-R(-t)}2.
$$

应证明偶通道保存位移平方而丢失方向，奇通道在非零位移下恢复时间定向。

### 3. 负平方 Laplace resolvent

在明确条件 `u>delta^2` 下形式化

$$
\int_0^\infty e^{-(u-delta^2)t}\,dt
=\frac1{u-delta^2}.
$$

这会把负谱值连接到稳定化债务和 resolvent 极点。

### 4. 曲率互作用节点

需要把相位压平后的径向互反对与已有 `OffLineCurvatureDipole` 的法向二阶对数曲率精确连接。目标不是结构类比，而是一个可运输误差和符号的等式。

## 八、更新后的 theorem DAG

```text
CriticalDampingGenerator
        |
        v
ReflectedZeroModePhaseFlattening
        |
        +-----------------------------+
        |                             |
        v                             v
SecondOrderRadialSpectrum       EvenOddModeObserver
        |                             |
        +--------------+--------------+
                       |
                       v
          NegativeSquareLaplaceResolvent
                       |
                       v
          OffLineCurvatureModeIntertwiner
                       |
                       v
             SignedNormalSpectralAtom
                       |
                       v
       Chebyshev / Toeplitz / Pick / Weil witness
```

下一真源的最高优先级是 `ReflectedZeroModeSecondOrderSpectrum`。它将第一次把本层的表示分解变成一个真正的负谱陈述。

---

## [PR #4373] RH_RESEARCH_LANE_LEDGER — Time-Ordered Prime Memory Cocycle

> **统一理论卷规则(本节起生效)。** RH research lane 的新理论推理统一追加到本卷。后续形式化节点继续拥有各自的 Lean GID、Scribe 源和 Blueprint 镜像，但不再为每个节点新建独立 theory 文档。本卷 append-only：勘误以新追加的正文发表，不改动既有字节。

# RH Research Lane Theory
## 累积研究真源、约束账本与下一桥梁

> **统一理论卷规则。** 从本文件建立以后，RH research lane 的新理论推理统一追加到 `RH_RESEARCH_LANE_THEORY.md`。后续形式化节点继续拥有各自的 Lean GID、Scribe 源和 Blueprint 镜像，但不再为每个节点新建独立 theory 文档。
>
> 本文件在 `dev` 尚不存在同名卷时初始化。此前的 `GOLDEN_OBSERVER_RH_ROUTE.md`、`OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY.md` 以及已合并的节点级理论文件继续作为历史来源和 digestion 输入。本文件承担向前演化的单一研究账本，不在本轮删除历史文件，以免破坏已有引用和内容寻址记录。

---

# 0. 认识论状态与使用规则

本研究卷严格区分三种状态。

## 0.1 已冻结机器事实

只有已经进入对应 Lean GID，并通过仓库 admission 的声明，才可以作为后续推理的无条件前提。

当前与黄金素数记忆、色散和 RH 路线直接相关的已冻结节点包括：

- `D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature`
- `D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound`
- `D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy`
- `D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow`
- `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature`
- `D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition`
- `D5/S3/Analytic/Boundary/InteriorCurvatureCriterion`

本轮候选节点为：

- `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle`

在该候选通过 canonical Lean report 和 content-addressed admission 以前，本节新增结论仍应标为 candidate truth。

## 0.2 条件桥

条件桥是形式上足以连接 RH，但其关键前提尚未由 prime side 独立构造的定理。当前最重要的条件桥是：

\[
P_{L,N}\mathcal O^{\mathrm{off}}_{L,T}P_{L,N}
\preceq
C_{L,N,T}\mathcal V^{\mathrm{hol}}_{r,L,N}
+
\varepsilon_{r,L,N,T}I.
\]

这里 \(\mathcal V^{\mathrm{hol}}\) 是 prime-side 规范约化 holonomy 能量，\(\mathcal O^{\mathrm{off}}\) 是 zero-side 离线奇谱能量。该支配仍是路线的 hard heart。

## 0.3 解释性图景

白光、色散、共振、圆、观察者和时间可以指导定义。它们本身不构成证明。每个解释必须最终落到以下一种可审计对象：

\[
\text{定义},\quad
\text{恒等式},\quad
\text{不等式},\quad
\text{极限},\quad
\text{反例},\quad
\text{有限失败证书}.
\]

---

# 1. 当前主路线的机器骨架

带记忆的局部素数观察器可以写成上三角更新：

\[
\mathbf U_{r,p}(s)
=
\begin{pmatrix}
\mathbf F & \bigl(L_p^{\langle r\rangle}(s)-1\bigr)v_p\\
0 & L_p^{\langle r\rangle}(s)
\end{pmatrix}.
\]

将 Fibonacci 记忆投影到稳定特征通道后，记：

\[
a=-\varphi^{-1},
\qquad
\lambda_p=L_p^{\langle r\rangle}(s),
\qquad
b_p=b^-_{r,p}(s).
\]

一维稳定更新为：

\[
U_p(m,z)
=
\bigl(am+b_pz,\lambda_pz\bigr).
\]

## 1.1 标量完成与记忆历史

标量因子满足交换律：

\[
\lambda_p\lambda_q=\lambda_q\lambda_p.
\]

所以标量输出只能读取 prime multiset，无法读取观察词的次序。

记忆提升一般不交换。两事件交换曲率为：

\[
\boxed{
C_{p,q}
=
(a-\lambda_q)b_p-(a-\lambda_p)b_q.
}
\]

已冻结的 `PrimeSwapCurvature` 证明：

\[
C_{q,p}=-C_{p,q},
\]

并证明共同记忆原点变换

\[
b_p\mapsto b_p+(a-\lambda_p)c
\]

不改变 \(C_{p,q}\)。因此共同 archive 属于 coboundary，交换曲率只读取不同通道之间无法由同一观察起源解释的部分。

远离共振时，定义：

\[
c_p=\frac{b_p}{a-\lambda_p}.
\]

机器结论为：

\[
\boxed{
C_{p,q}
=(a-\lambda_p)(a-\lambda_q)(c_p-c_q),
}
\]

以及：

\[
\boxed{
C_{p,q}=0
\iff
c_p=c_q.
}
\]

## 1.2 residual 控制曲率

写：

\[
\lambda_p=1+r_p,
\qquad
b_p=r_pv_p.
\]

`StableResidualSwapCurvatureBound` 已证明：

\[
\boxed{
\begin{aligned}
C^{\mathrm{st}}_{p,q}
={}&
(a-1)(r_pv_p-r_qv_q)
\\
&+r_pr_q(v_q-v_p).
\end{aligned}
}
\]

在 \(\|v_p\|,\|v_q\|\le1\) 下：

\[
\boxed{
\|C^{\mathrm{st}}_{p,q}\|
\le
\|a-1\|\bigl(\|r_p\|+\|r_q\|\bigr)
+2\|r_p\|\|r_q\|.
}
\]

若 \(\|r_p\|,\|r_q\|\le\varepsilon\)，则：

\[
\boxed{
\|C^{\mathrm{st}}_{p,q}\|
\le
2\|a-1\|\varepsilon+2\varepsilon^2.
}
\]

## 1.3 有限 holonomy 能量

对有限活动通道集 \(P\)，定义：

\[
\mathcal E_P^{\mathrm{hol}}
=
\sum_{p\in P}\sum_{q\in P}
\|C_{p,q}\|^2.
\]

`FiniteHolonomyEnergy` 已证明：

\[
\mathcal E_P^{\mathrm{hol}}\ge0,
\]

\[
\mathcal E_P^{\mathrm{hol}}=0
\iff
C_{p,q}=0
\quad\forall p,q\in P,
\]

以及在 \(|P|=M\) 和共同 residual envelope 下：

\[
\boxed{
\mathcal E_P^{\mathrm{hol}}
\le
M^2
\left(
2\|a-1\|\varepsilon+2\varepsilon^2
\right)^2.
}
\]

这使 prime-side 最短链条成为：

\[
\boxed{
\text{uniform residual decay}
\Longrightarrow
\text{pairwise curvature decay}
\Longrightarrow
\text{finite holonomy energy decay}.
}
\]

---

# 2. Fourier 色散已经产生谱时间

`PrimeFrequencyPhaseFlow` 定义：

\[
\boxed{
\chi_\omega(t)=e^{-it\omega}.
}
\]

机器结论包括：

\[
\chi_\omega(0)=1,
\]

\[
\chi_\omega(t+u)
=
\chi_\omega(t)\chi_\omega(u),
\]

\[
\chi_{\omega+\nu}(t)
=
\chi_\omega(t)\chi_\nu(t),
\]

\[
|\chi_\omega(t)|=1.
\]

在 zeta prime channel 中：

\[
p^{-s}
=
p^{-\sigma}e^{-it\log p},
\qquad
s=\sigma+it.
\]

所以：

\[
\boxed{
\omega_p=\log p
}
\]

是素数的自然 Fourier 频率，\(t=\operatorname{Im}s\) 是其对偶参数。

有限通道相位空间为：

\[
U(1)^P.
\]

每个通道在单位圆上旋转。标量相位乘积满足：

\[
\prod_{j=1}^n\chi_{\omega_j}(t)
=
\chi_{\sum_j\omega_j}(t).
\]

因此标量 Fourier 层仍然遗忘列表次序。谱时间已经存在，操作 chronology 尚未被标量层读取。

`PhaseTwistedStableSwapCurvature` 将 Fourier 相位乘到记忆通道：

\[
v_p(t)=\chi_{\omega_p}(t)v_p.
\]

由于相位模长为一，已有 residual 曲率界和有限能量上界对 \(t\) 一致成立。

---

# 3. Append 001. Time-Ordered Prime Memory Cocycle

**候选 GID：**

`D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle`

本节是本统一理论卷的第一次正式增补。

## 3.1 两种时间必须分开

一个 timed event 记为：

\[
e=(\lambda_e,b_e,\omega_e,t_e).
\]

其中：

- \(t_e\) 是 Fourier phase 的实参数；
- \(\omega_e\) 是频率，prime specialization 为 \(\log p\)；
- 事件在列表中的位置是操作次序；
- 列表次序不由 \(t_e\) 的数值自动决定。

因此当前系统至少具有两个不同坐标：

\[
\boxed{
\begin{aligned}
t &: \text{连续谱时间},\\
k &: \text{离散操作次序}.
\end{aligned}
}
\]

本轮形式化将二者耦合，但不把它们识别为同一个时间，也不假设事件列表已经按实数时间单调排序。

## 3.2 Fourier-timed 有效注入

定义：

\[
\boxed{
\beta_e
=
\chi_{\omega_e}(t_e)b_e.
}
\]

事件更新为：

\[
\boxed{
U_e(m,z)
=
\bigl(am+\beta_ez,\lambda_ez\bigr).
}
\]

机器节点证明时间平移：

\[
\boxed{
\beta_e(t_e+u)
=
\beta_e(t_e)\chi_{\omega_e}(u).
}
\]

这说明 Fourier 时间平移作用于每个局部注入。该作用仍然可逆，不产生时间箭头。

对于自然数地址 \(n\)，构造频率：

\[
\omega_n=\log n.
\]

节点证明对应有效注入正好使用已有 `logAddressPhase`。当地址是素数 \(p\) 时，这就是 \(e^{-it\log p}\) 通道。

## 3.3 标量 cocycle 与记忆 cocycle

对 chronology word：

\[
w=e_1e_2\cdots e_n,
\]

定义标量摘要：

\[
\boxed{
\Lambda(w)
=
\prod_{j=1}^n\lambda_{e_j}.
}
\]

定义记忆摘要的递推：

\[
M_a(\varnothing)=0,
\]

\[
\boxed{
M_a(e_1w)
=
a^{|w|}\beta_{e_1}
+M_a(w)\lambda_{e_1}.
}
\]

将递推展开得到纸面闭式：

\[
\boxed{
M_a(w)
=
\sum_{j=1}^n
 a^{n-j}\beta_{e_j}
 \prod_{k<j}\lambda_{e_k}.
}
\]

该闭式解释两个方向的运输：

1. 事件 \(e_j\) 之前出现的 scalar factors 通过 \(\prod_{k<j}\lambda_{e_k}\) 改变它接收到的 scalar input；
2. 事件 \(e_j\) 之后还剩余的记忆步骤通过 \(a^{n-j}\) 运输其注入。

所以同一批事件采用不同次序时，标量乘积相同，记忆权重一般不同。

## 3.4 精确 affine word action

候选 Lean 定理证明：

\[
\boxed{
U_w(m,z)
=
\left(
 a^{|w|}m+M_a(w)z,
 \Lambda(w)z
\right).
}
\]

这一步把“记忆保存历史”从解释转化成一个精确有限公式。

初始记忆 \(m\) 只经过统一稳定乘子 \(a^{|w|}\)。事件历史全部压缩进 \(M_a(w)\)。标量世界全部压缩进 \(\Lambda(w)\)。

## 3.5 拼接律是真正的 cocycle 结构

设先执行 prefix \(u\)，再执行 suffix \(v\)。候选 Lean 定理证明：

\[
\boxed{
\Lambda(uv)
=
\Lambda(u)\Lambda(v),
}
\]

\[
\boxed{
M_a(uv)
=
a^{|v|}M_a(u)
+M_a(v)\Lambda(u).
}
\]

完整演化满足：

\[
\boxed{
U_{uv}
=
U_v\circ U_u.
}
\]

因此 summary triple

\[
\bigl(|w|,\Lambda(w),M_a(w)\bigr)
\]

带有半直积型合成：

\[
\boxed{
(n,\Lambda,M)\star(m,\Gamma,N)
=
\left(
 n+m,
 \Lambda\Gamma,
 a^mM+N\Lambda
\right).
}
\]

这里第一个 word 先执行，第二个 word 后执行。

这就是目前最精确的“时间产生 holonomy”表述：连续 Fourier 时间旋转局部注入，离散 chronology 通过扭曲 cocycle 决定这些注入如何积累。

## 3.6 两事件交换恢复 prime curvature

对两个 timed events \(p,q\)，候选 Lean 定理证明：

\[
\Lambda(pq)=\Lambda(qp),
\]

并证明任意初始状态上的记忆差为：

\[
\boxed{
\pi_1U_{pq}(m,z)
-
\pi_1U_{qp}(m,z)
=
C_{p,q}^{\mathrm{time}}z,
}
\]

其中：

\[
\boxed{
C_{p,q}^{\mathrm{time}}
=
(a-\lambda_q)\beta_p
-
(a-\lambda_p)\beta_q.
}
\]

在 cocycle 层：

\[
\boxed{
M_a(pq)-M_a(qp)
=
C_{p,q}^{\mathrm{time}}.
}
\]

所以原有 `PrimeSwapCurvature` 不再只是一个局部代数差。它现在被识别为两个 chronology words 的精确 memory holonomy。

## 3.7 residual 与 phase-twisted 曲率的连接

对 residual event：

\[
\lambda_p=1+r_p,
\qquad
b_p=r_pv_p.
\]

允许两个事件拥有不同 Fourier 时间：

\[
t_p,\qquad t_q.
\]

候选 Lean 定理证明：

\[
\boxed{
M_a(pq)-M_a(qp)
=
C^{\mathrm{st}}
\left(
 a,r_p,r_q,
 \chi_{\omega_p}(t_p)v_p,
 \chi_{\omega_q}(t_q)v_q
\right).
}
\]

当：

\[
t_p=t_q=t,
\]

节点恢复已经冻结的 common-time phase-twisted curvature：

\[
\boxed{
M_a(pq)-M_a(qp)
=
C^{\mathrm{phase}}_{p,q}(t).
}
\]

这证明新节点严格扩展已有真源，没有重新定义一个平行 curvature。

---

# 4. 对“色散的次序产生时间”的校准

现在可以将直觉写成三层。

## 4.1 色散给频率差

prime channels 的频率为：

\[
\omega_p=\log p.
\]

两个通道之间的自然频率差为：

\[
\boxed{
\Delta\omega_{p,q}
=
\log p-\log q
=
\log\frac pq.
}
\]

## 4.2 Fourier 变换给对偶时间

相位：

\[
\chi_{\omega_p}(t)
=
e^{-it\omega_p}
\]

把频率与连续参数 \(t\) 配对。该参数具有加法群结构：

\[
\chi_\omega(t+u)
=
\chi_\omega(t)\chi_\omega(u).
\]

所以 Fourier 对偶已经给出严格的谱时间。

## 4.3 记忆让次序可观测

标量 phase product 和 scalar Euler product 都遗忘事件排序。时间参数本身也不会自动产生 chronology。

列表提升以后：

\[
e_1e_2\cdots e_n
\]

决定 affine update 的操作次序。扭曲 cocycle \(M_a(w)\) 使这个次序可见。

因此最精确的句子是：

\[
\boxed{
\text{色散产生频率差，Fourier 对偶产生谱时间，记忆 cocycle 使操作次序可观测。}
}
\]

时间不是由排序凭空创造。当前系统中：

- \(t\) 来自 Fourier duality；
- \(k\) 来自 event chronology；
- \(r\) 来自 extraction depth；
- 后续需要研究三者是否组成兼容的多参数 cocycle。

---

# 5. 与波、共振和能量聚合的关系

对单位相位 \(z_p\in U(1)\) 和权重 \(w_p\ge0\)，定义：

\[
W=\sum_pw_p,
\qquad
A=\sum_pw_pz_p.
\]

相位色散能量满足纸面恒等式：

\[
\boxed{
\sum_{p,q}w_pw_q|z_p-z_q|^2
=
2W^2-2|A|^2.
}
\]

所以：

\[
\boxed{
\text{色散缺陷能量下降}
\iff
\text{共同模态相干能量上升}.
}
\]

time-ordered memory cocycle 增加了另一个层次。即使单时刻相位相干，历史注入仍可能因 local factors 和 chronology 的运输方式不同而产生非零 holonomy。

因此完整压平需要同时处理：

\[
\boxed{
\begin{aligned}
\text{phase dispersion} &\to0,\\
\text{memory swap curvature} &\to0,\\
\text{residual envelope} &\to0.
\end{aligned}
}
\]

这三者不能在定义上相互替代。

---

# 6. 与 RH 的关系

RH 要排除：

\[
\rho
=
\frac12+\delta+i\gamma,
\qquad
\delta\ne0.
\]

仓库 zero side 已经把一个离线四点轨道写成：

\[
\boxed{
Q_{\operatorname{orb}(\rho)}
=
E_\rho^{\mathrm{even}}
-
E_\rho^{\mathrm{odd}},
}
\]

其中：

\[
E_\rho^{\mathrm{even}}\ge0,
\qquad
E_\rho^{\mathrm{odd}}\ge0.
\]

全部符号风险集中在 odd spectral channel。

本轮 time-ordered cocycle 给 prime side 一个更具体的候选输入：

\[
C_{r;p,q}(t_p,t_q)
=
(a-\lambda_q)\chi_{\omega_p}(t_p)b_p
-
(a-\lambda_p)\chi_{\omega_q}(t_q)b_q.
\]

可以由它构造 finite time-frequency holonomy energy：

\[
\boxed{
\mathcal V_{r,P,T}^{\mathrm{time}}
=
\sum_{p,q\in P}
\int_{\Delta_T}
\left\|
K_{p,q}(t_1,t_2)
C_{r;p,q}
\right\|^2
\,dt_2dt_1,
}
\]

其中：

\[
\Delta_T
=
\{(t_1,t_2):0<t_2<t_1<T\}
\]

是有序时间单纯形，\(K_{p,q}\) 是下一节登记的 Fourier slot-swap kernel。

真正连接 RH 仍需证明：

\[
\boxed{
\mathcal E^{\mathrm{odd}}_{\mathrm{off}}(L,N,T)
\le
A_{L,N,T}
\mathcal V_{r,P,T}^{\mathrm{time}}
+
R_{r,L,N,T},
}
\]

且：

\[
R_{r,L,N,T}\to0.
\]

若 extraction tower 再给出：

\[
\mathcal V_{r,P,T}^{\mathrm{time}}\to0,
\]

则离线 odd energy 必须消失。通过已冻结的内部曲率判据，才可进入 RH。

当前节点本身没有建立这个支配。

---

# 7. 下一真源. SecondMagnusSwapCurvature

下一节点不应再次定义列表 cocycle。它应建立连续 time-ordering 的二阶核。

对两个 prime-frequency channels：

\[
\chi_p(t)=e^{-it\omega_p},
\qquad
\chi_q(t)=e^{-it\omega_q},
\]

定义 fixed-slot swap kernel：

\[
\boxed{
K_{p,q}(t_1,t_2)
=
\chi_p(t_1)\chi_q(t_2)
-
\chi_q(t_1)\chi_p(t_2).
}
\]

令：

\[
\bar t=\frac{t_1+t_2}{2},
\qquad
\Delta t=t_1-t_2,
\]

\[
\bar\omega=\frac{\omega_p+\omega_q}{2},
\qquad
\Delta\omega=\omega_p-\omega_q.
\]

目标精确分解为：

\[
\boxed{
K_{p,q}(t_1,t_2)
=
-2i
 e^{-2i\bar t\bar\omega}
 \sin\left(
 \frac{\Delta t\,\Delta\omega}{2}
 \right).
}
\]

因此：

\[
\boxed{
|K_{p,q}(t_1,t_2)|^2
=
4\sin^2\left(
\frac{\Delta t\,\Delta\omega}{2}
\right).
}
\]

在小尺度下：

\[
|K_{p,q}|^2
\sim
(\Delta t)^2(\Delta\omega)^2.
\]

prime specialization 给出：

\[
\boxed{
|K_{p,q}|^2
\sim
(t_1-t_2)^2
\log^2\frac pq.
}
\]

随后定义连续生成元：

\[
H(t)
=
\sum_pA_p\chi_p(t).
\]

二阶 Magnus 项为：

\[
\boxed{
\Omega_2(T)
=
\frac12
\int_{0<t_2<t_1<T}
[H(t_1),H(t_2)]
\,dt_2dt_1.
}
\]

展开以后，每个 \((p,q)\) 对应：

\[
K_{p,q}(t_1,t_2)[A_p,A_q].
\]

该结构同时要求：

\[
\Delta t\ne0,
\qquad
\Delta\omega\ne0,
\qquad
[A_p,A_q]\ne0.
\]

任一因子为零，二阶 order defect 消失。

下一 Lean 节点应先形式化有限两通道代数核和范数恒等式，不应立即承担积分收敛或 prime-zero domination。

---

# 8. 后续任务账本

## 8.1 已闭合或候选闭合

\[
\begin{aligned}
&\text{prime swap curvature and gauge invariance},\\
&\text{residual curvature bound},\\
&\text{finite holonomy energy},\\
&\text{prime-frequency Fourier flow},\\
&\text{phase-twisted residual curvature},\\
&\text{time-ordered finite memory cocycle}.\
\end{aligned}
\]

## 8.2 下一批有限节点

1. `SecondMagnusSwapCurvature`
2. `ResonanceConditionedOriginDispersion`
3. `FinitePhaseCoherenceIdentity`
4. `ResidualEnvelopeFiniteWindowConvergence`
5. `FiniteOffLineOddEnergy`

## 8.3 当前 hard heart

\[
\boxed{
\texttt{PrimeArchimedeanHolonomyDomination}
}
\]

目标是把 independently constructed prime-side time-ordered holonomy energy 运输到 zero-side off-line odd energy，并明确记录：

\[
\text{prime cutoff error},
\quad
\text{time cutoff error},
\quad
\text{Galerkin error},
\quad
\text{Archimedean error},
\quad
\text{zero-tail error}.
\]

---

# 9. 本轮严格非主张

本轮不主张：

- event list 已按实数时间排序；
- Fourier 时间具有不可逆方向；
- extraction depth 等于物理时间；
- time-ordered exponential 已经构造；
- Magnus expansion 已经形式化；
- residual envelope 已经随抽取深度趋零；
- 无限 prime holonomy energy 已经存在；
- prime-side cocycle 已经支配 zero-side odd energy；
- 离线零点已经被排除；
- RH 已经证明。

本轮候选机器增量精确到：

\[
\boxed{
\text{Fourier-timed local events}
\longrightarrow
\text{finite affine word action}
\longrightarrow
\text{twisted append cocycle}
\longrightarrow
\text{two-event prime swap curvature}.
}
\]

最凝练的理论结论是：

\[
\boxed{
\text{Fourier 对偶给出谱时间，事件列表给出操作 chronology，记忆 cocycle 将二者耦合并保存顺序。}
}
\]

---

# 10. Append 002. Second-Magnus Swap Curvature

**候选 GID：**

`D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature`

本增补建立在修复后的 `TimeOrderedPrimeMemoryCocycle` 上。原文件中的 Lean 变量 `prefix`、`suffix` 分别统一改为 `earlierWord`、`laterWord`。该改名只修复 source-bound 解析，不改变 cocycle 的定义、定理陈述或依赖图。两个节点在 PR admission 完成以前都仍是 candidate truth。

## 10.1 二阶核是时间槽与频率槽的交替行列式

继续使用：

\[
\chi_\omega(t)=e^{-it\omega}.
\]

定义：

\[
\boxed{
K_{p,q}(t_1,t_2)
=
\chi_{\omega_p}(t_1)\chi_{\omega_q}(t_2)
-
\chi_{\omega_q}(t_1)\chi_{\omega_p}(t_2).
}
\]

它是两个 evaluation vectors 的二阶外积系数，也可写为一个 \(2\times2\) 行列式。因此机器节点证明：

\[
\boxed{K_{q,p}=-K_{p,q}},
\qquad
\boxed{K_{p,q}(t_2,t_1)=-K_{p,q}(t_1,t_2)},
\]

\[
\boxed{t_1=t_2\Longrightarrow K_{p,q}=0},
\qquad
\boxed{\omega_p=\omega_q\Longrightarrow K_{p,q}=0},
\]

以及：

\[
\boxed{|K_{p,q}|\le2}.
\]

频率标签与时间槽同时交换时，两个负号抵消。由此，\(K\) 保存的是二维 orientation，不是单个相位的大小。

## 10.2 中心变量与相对变量完全分离

令：

\[
\bar\omega=\frac{\omega_p+\omega_q}{2},
\qquad
\delta\omega=\frac{\omega_p-\omega_q}{2}.
\]

节点证明中心分解：

\[
\boxed{
K_{p,q}
=
\chi_{\bar\omega}(t_1+t_2)
\left[
\chi_{\delta\omega}(t_1-t_2)
-
\chi_{-\delta\omega}(t_1-t_2)
\right].
}
\]

其正弦形式为：

\[
\boxed{
K_{p,q}
=
-2i e^{-i(t_1+t_2)(\omega_p+\omega_q)/2}
\sin\left(
\frac{(t_1-t_2)(\omega_p-\omega_q)}2
\right).
}
\]

共同中心相位模长恒为一。全部可观测二阶强度只依赖 time-frequency area：

\[
\mathfrak a_{p,q}
=(t_1-t_2)(\omega_p-\omega_q).
\]

所以二阶破缺需要时间分离与频率分离同时存在。即使两者都非零，仍有共振消零：

\[
\boxed{
\mathfrak a_{p,q}\in2\pi\mathbb Z
\Longrightarrow K_{p,q}=0.
}
\]

这说明点态二阶核不是 holonomy 的 faithful 探针。

## 10.3 有限二阶 Magnus 能量

对有限通道集 \(P\) 与已有交换曲率 \(C_{p,q}\)，定义：

\[
\boxed{
\mathcal E^{(2)}_{P}(t_1,t_2)
=
\sum_{p,q\in P}
\left|K_{p,q}(t_1,t_2)C_{p,q}\right|^2.
}
\]

机器节点证明：

\[
\boxed{
0\le\mathcal E^{(2)}_{P}(t_1,t_2)
\le4\mathcal E^{\mathrm{hol}}_{P}.
}
\]

再与已冻结的 stable residual holonomy bound 组合，得到：

\[
\mathcal E^{(2)}_{P}(t_1,t_2)
\le
4|P|^2
\left(
2\lVert a-1\rVert\varepsilon+2\varepsilon^2
\right)^2,
\]

并证明 \(\varepsilon=0\) 时二阶能量为零。因此新增严格链为：

\[
\boxed{
\text{residual envelope decay}
\Longrightarrow
\text{finite holonomy energy decay}
\Longrightarrow
\text{finite second-Magnus energy decay}.
}
\]

该链严格单向。共振格可以使 \(K_{p,q}C_{p,q}=0\)，同时允许 \(C_{p,q}\ne0\)。因此当前节点不能从二阶能量小反推出 holonomy 小。

## 10.4 为什么它对应真正的二阶 Magnus 系数

令有限生成元为：

\[
H(t)=\sum_{p\in P}\chi_{\omega_p}(t)A_p.
\]

则交换子展开为：

\[
[H(t_1),H(t_2)]
=
\sum_{p,q\in P}
K_{p,q}(t_1,t_2)[A_p,A_q].
\]

所以 \(K_{p,q}\) 是连续 time-ordering 的纯 Fourier slot coefficient，\(C_{p,q}\) 是离散记忆更新的非交换系数。二者乘积把两种破缺分层记账：

\[
\boxed{
K_{p,q}:\text{time-frequency orientation defect},
\qquad
C_{p,q}:\text{memory-channel holonomy defect}.
}
\]

本节点只形式化有限代数核及其能量支配，尚未形式化 ordered-simplex integral、Magnus series 收敛或无限 prime 极限。

## 10.5 黄金、素数频率、色散与拓扑的精确关系

当前路线里有两个已冻结但尚未同一化的黄金位置。

第一，黄金记忆稳定特征值：

\[
a=-\varphi^{-1}.
\]

它进入 \(C_{p,q}\)，控制历史注入的收缩和运输。

第二，黄金尺度圆的基本频率：

\[
\Omega_\varphi=\frac{\pi}{\log\varphi},
\qquad
\omega_k=k\Omega_\varphi.
\]

将黄金 Fourier modes 代入新核可得：

\[
K_{k,\ell}(t_1,t_2)
=
-2i e^{-i(t_1+t_2)(k+\ell)\Omega_\varphi/2}
\sin\left(
\frac{(t_1-t_2)(k-\ell)\pi}{2\log\varphi}
\right).
\]

而 zeta 的 prime frequencies 是：

\[
\omega_p=\log p.
\]

仓库当前没有证明 \(\log p\in\Omega_\varphi\mathbb Z\)，该关系通常也不成立。黄金 Fourier lattice 与 prime log-frequency set 是两套坐标。后续需要明确的 sampling、projection、aliasing 或 Poisson 型运输定理，才能把它们接入同一 RH 桥梁。

拓扑层面，定义：

\[
v_{p,q}(t)=
\bigl(\chi_{\omega_p}(t),\chi_{\omega_q}(t)\bigr)\in\mathbb C^2.
\]

则：

\[
K_{p,q}(t_1,t_2)
=
v_{p,q}(t_1)\wedge v_{p,q}(t_2)
\in\Lambda^2\mathbb C^2.
\]

\(K=0\) 是 evaluation map 的 rank-drop locus，\(K\ne0\) 表示两个时间切片张成有向二维单元。当前只获得 exterior-algebra 与 rank-locus 结构。尚未构造 coboundary、cohomology class、Chern class 或全局 bundle invariant。

## 10.6 对 RH 路线的下一步校准

点态上界只能证明 residual 衰减足以压低二阶能量。要把二阶能量变成可识别的 holonomy 探针，下一真源应消除孤立共振零点。对 \(\Delta\omega\ne0\)，有序时间单纯形平均的纸面候选为：

\[
\mathcal A_T(\Delta\omega)
=
\int_{0<t_2<t_1<T}|K_{p,q}(t_1,t_2)|^2\,dt_2dt_1
=
T^2-
\frac{2\bigl(1-\cos(T\Delta\omega)\bigr)}{(\Delta\omega)^2}.
\]

对固定非零 \(\Delta\omega\)，其归一化满足：

\[
\frac{\mathcal A_T(\Delta\omega)}{T^2}\longrightarrow1.
\]

有限 prime cutoff 下，若最小 log-frequency gap 为正，便可寻求统一 frame lower bound。建议下一 GID 为：

`D5/S3/Observer/AgencyHolonomy/OrderedTimeSimplexSecondMagnusAverage`

它应先证明积分恒等式、非负性、非零频率差下的正性，以及依赖 finite gap 的加权下界。完成后，路线才可能从单向 domination 升级为 resonance-controlled observability。

## 10.7 严格非主张

本增补不主张：黄金 Fourier modes 已与 prime log frequencies 同一化；点态二阶能量 faithfully 恢复 holonomy；有序时间积分已经形式化；Magnus series 已收敛；二阶核已给出全局拓扑不变量；prime-side 能量已支配 zero-side odd energy；离线零点已排除；RH 已证明。

---

## [PR #4372] RH_RESEARCH_LANE_THEORY — Reflected Growth Pair Second-Order Spectrum

# RH_RESEARCH_LANE_THEORY

## 累积式 RH 研究真理卷

本文件是 `trureturing` 中 RH 研究路线唯一的累积理论文档。后续理论进展只在本文件中追加、修订和标注状态，不再为每个研究波次创建新的 `docs/develop/theory/*THEORY.md` 文档。每个独立 Lean 节点仍可保留仓库要求的 `Blueprint` Scribe 真源与确定性 Markdown 投影。

当前追加基线：`dev` 提交 `6aef3e41d2365d365fd3de24f44f4ba2a8779f96`。

本卷不是 RH 证明声明。它用于区分已经机器闭合的事实、定义性重写、候选桥梁、开放义务、误差预算和目标泄漏风险。

---

## 0. 状态语言

本卷统一使用以下状态：

- **Frozen**：已经存在于 `dev` 的 Lean proof term。
- **Candidate**：当前 PR 中已经给出 Lean 形式化，尚待仓库 admission 或合并。
- **Derived**：可以由 Frozen/Candidate 定理直接推出，但尚未拥有独立 Lean 名称。
- **Bridge target**：连接两个已经形式化对象所需的精确新定理。
- **Open**：当前没有证明，不得作为后续定理的无标注前提。
- **Consumer from RH**：以 RH 或 RH 等价性质为前提，只能用于后果分析，不能作为朝向 RH 的证明边。

RH 路线中的每一个承重命题都应记录：

1. 输入对象来自哪里；
2. 是否使用 RH 或已知等价命题；
3. 结论方向；
4. 有限证书及其严格裕量；
5. 截断、尾项和运输误差；
6. 第一条尚未闭合的边。

---

## 1. 研究主架构

当前 RH 研究被拆成三类彼此独立的桥。

### 1.1 反例检测桥

目标是证明：

\[
\neg\mathrm{RH}
\Longrightarrow
\exists\text{ finite certified negative witness}.
\]

候选观察图表包括：

- Cayley/Li 矩；
- Toeplitz 最小特征值；
- Pick negative square；
- normal jet；
- signed normal support；
- Chebyshev 负支撑分离器；
- Weil 紧支撑测试函数。

检测桥只说明离线零点最终可见。它不解释素数侧为何排除该离线零点。

### 1.2 算术强制桥

目标是从素数、Gamma、pole、边界项和窗口几何推出全部有限观察层非负。当前最精确的开放形式包括：

\[
\texttt{BalancedPrimePickInnovationLowerBound}
\]

和：

\[
\texttt{PrimeArchimedeanBlindSchurCoercivity}.
\]

这部分是目前最主要的 RH 承重开放边。

### 1.3 完成与全局化桥

目标是证明一致的有限正完成在统一预算和紧性条件下产生一个全局正谱对象。必须区分：

- 每个固定深度可行；
- 跨深度兼容；
- 统一 resolvent 预算；
- weighted weak-* 紧性；
- 全局正完成；
- 原子支撑与真实零点的进一步识别。

有限层逐层可行本身不足以推出全局对象。

---

## 2. 负性、负平方与负时间的强类型区分

“负”不是单一对象。它总是相对于某个正锥、允许支撑、二次型、稳定半平面或时间定向定义。

必须区分：

1. 负标量：\(a<0\)。
2. 负质量：signed measure 的某个权重为负。
3. 负支撑：正质量位于禁止区域，例如 \(x<0\)。
4. 负方向：存在 \(v\ne0\) 使 \(Q(v)<0\)。
5. negative square：有限 Hermitian Gram 矩阵拥有一个独立负方向。
6. 负指数：最大负定子空间的维数。
7. 负频率：Fourier 相位的反向绕行。
8. 负时间：相对于选定时间锥的反向参数、逆动力学或历史完成。

这些对象之间可以存在运输定理，不能直接互换。

### 2.1 正锥分离定义

设允许对象形成锥 \(C\)。如果对偶观察器 \(\ell\) 满足：

\[
\ell(c)\ge0\qquad(c\in C),
\]

而：

\[
\ell(x)<0,
\]

则 \(\ell\) 是对象 \(x\) 越过正锥边界的负性证书。

因此有限 RH 反例证书的最终形式应是：

\[
\boxed{
\ell\in C^\vee,
\qquad
\ell(X_\zeta)<-\eta,
\qquad
\eta>0.
}
\]

严格正裕量 \(\eta\) 用于吸收尾项和数值误差。

---

## 3. Frozen：反射增长对与负平方有符号行列式

当前 `dev` 的真源：

```text
D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.lean
```

定义反射增长对：

\[
G_\delta(t)
=
\left(e^{\delta t},e^{-\delta t}\right).
\]

已经机器证明：

\[
G_\delta(-t)=\operatorname{swap}G_\delta(t),
\]

\[
e^{\delta t}e^{-\delta t}=1,
\]

以及生成率对 \((\delta,-\delta)\) 满足：

\[
\operatorname{tr}=0,
\qquad
\det=-\delta^2.
\]

这里的 \(-\delta^2\) 是反射生成元的**有符号行列式**。它不是二次多项式的标准判别式。特征多项式为：

\[
(r-\delta)(r+\delta)=r^2-\delta^2,
\]

而标准判别式为：

\[
4\delta^2.
\]

所以：

\[
\boxed{
\text{signed determinant}=-\delta^2,
\qquad
\text{polynomial discriminant}=4\delta^2.
}
\]

函数方程型反射消除了线性方向标签，二阶平方大小仍然保留。

---

## 4. Candidate append 2026-08-31：反射增长对的二阶负谱

当前候选真源：

```text
D5/S3/Analytic/Adelic/ReflectedGrowthPairSecondOrderSpectrum.lean
```

该节点只依赖已经冻结的 `ReflectedGrowthPairNegativeSquare` 和 Mathlib 的实指数 iterated derivative 定理。

### 4.1 两条径向分支

定义：

\[
g_+(t)=e^{\delta t},
\qquad
g_-(t)=e^{-\delta t}.
\]

对任意 \(n\ge0\)：

\[
\frac{d^n}{dt^n}g_+(t)
=
\delta^n g_+(t),
\]

\[
\frac{d^n}{dt^n}g_-(t)
=
(-\delta)^n g_-(t).
\]

特别地：

\[
g_+''(t)=\delta^2g_+(t),
\qquad
g_-''(t)=\delta^2g_-(t).
\]

定义负二阶观察器：

\[
\mathcal L=-\frac{d^2}{dt^2}.
\]

于是：

\[
\boxed{
\mathcal Lg_+(t)=-\delta^2g_+(t),
\qquad
\mathcal Lg_-(t)=-\delta^2g_-(t).
}
\]

结合上一真源：

\[
\operatorname{reflectionPairSignedDeterminant}(\delta)
=-\delta^2,
\]

得到精确 observer agreement：

\[
\boxed{
\text{反射生成元的有符号行列式}
=
\text{负二阶算子的谱值}.
}
\]

这不是类比，而是同一个标量 \(-\delta^2\) 在有限生成元图表和微分算子图表中的完全相同读数。

### 4.2 分支遗忘后的对称读出

定义：

\[
S_\delta(t)
=
g_+(t)+g_-(t)
=
e^{\delta t}+e^{-\delta t}.
\]

该函数已经在前一真源中证明为偶函数。本轮进一步得到：

\[
S_\delta''(t)=\delta^2S_\delta(t),
\]

因此：

\[
\mathcal LS_\delta(t)
=-\delta^2S_\delta(t).
\]

对称观察没有删除负二阶谱值。它只删除了哪一支是增长、哪一支是衰减的方向标签。

### 4.3 一阶盲性与二阶可见性

在反射中心 \(t=0\)：

\[
S_\delta'(0)=0,
\]

而：

\[
\boxed{
S_\delta''(0)=2\delta^2.
}
\]

若 \(\delta\ne0\)，则：

\[
S_\delta''(0)>0.
\]

所以：

\[
\boxed{
\text{对称性压平一阶方向，二阶曲率仍严格检测分裂大小。}
}
\]

这个结论解释了为什么 normal observer 中奇数法向层容易因函数方程对称而消失，而偶数层仍然可能携带离线信息。

### 4.4 当前命题边界

本节点没有证明：

- 参数 \(t\) 是物理时间；
- completed zeta 已经实现为上述二分支系统；
- 任意离线零点已被有限测试函数隔离；
- 二阶局部信号能够压过其他零点、Gamma 因子或截断尾项；
- 负二阶谱值已经产生 Weil、Pick 或 Toeplitz 负方向；
- RH 或其否定。

它关闭的是一个纯表示桥：

\[
\boxed{
\text{reflected split}
\longrightarrow
\text{signed determinant }-\delta^2
\longrightarrow
\text{negative second-order spectral value}.
}
\]

---

## 5. 与 completed-xi normal jet 的关系

当前 `dev` 的 `NormalJetFormula` 已经从真实 completed-xi normal intensity：

\[
I(\delta,t)
=
\left|
\xi\left(\frac12+\delta+it\right)
\right|^2
\]

构造偶阶 Taylor 系数，并机器证明前若干 normal jet 的导数公式。

本轮二阶真源说明了一个局部模型：反射增长率 \(\pm\delta\) 的方向信息在对称和中消失，而平方大小 \(\delta^2\) 在二阶读出中出现。

仍缺少的精确桥是：

\[
\boxed{
\texttt{OffLineCurvatureModeIntertwiner}
}
\]

它应把 phase-flattened reflected zero mode 的二阶对数曲率与已有离线曲率 dipole：

\[
K_{\delta,\gamma}(t)
=
2\frac{(t-\gamma)^2-\delta^2}
{((t-\gamma)^2+\delta^2)^2}
\]

严格连接起来。

在该桥建立以前，以下关系只能标记为结构一致：

- 有符号行列式包含 \(-\delta^2\)；
- 负二阶谱值为 \(-\delta^2\)；
- curvature dipole 的负核心由 \((t-\gamma)^2-\delta^2<0\) 控制；
- signed normal support 候选位置为 \(-\delta^2\)。

---

## 6. 新的结构推论

### 6.1 双曲模式与圆周模式的分界

对二阶算子 \(-D^2\)：

- 振荡模式 \(e^{i\gamma t}\) 的谱值是 \(+\gamma^2\)；
- 反射增长模式 \(e^{\pm\delta t}\) 的谱值是 \(-\delta^2\)。

因此正平方和负平方分别对应：

\[
\boxed{
+\gamma^2
\leftrightarrow
\text{elliptic / oscillatory sector},
}
\]

\[
\boxed{
-\delta^2
\leftrightarrow
\text{hyperbolic / growth-decay sector}.
}
\]

在 RH 的局部模式语言中，临界线对应纯相位旋转。离线位移引入互反的增长与衰减分支。

### 6.2 二阶读出不恢复方向

\(S_\delta''(0)=2\delta^2\) 可以恢复分裂大小，但不能区分 \(\delta\) 和 \(-\delta\)。

因此观察语言分层为：

\[
(\delta,\gamma)
\longrightarrow
\delta
\longrightarrow
\delta^2.
\]

- 完整复模式保存径向方向和频率方向；
- 相位压平保存径向方向；
- 对称二阶观察只保存径向分裂大小。

若后续任务需要恢复时间定向或分支方向，必须增加奇通道，例如：

\[
O_\delta(t)
=
\frac{e^{\delta t}-e^{-\delta t}}{2}.
\]

### 6.3 负平方是稳定化债务

对候选负支撑位置：

\[
x=-\delta^2,
\]

Laplace 时间因子为：

\[
e^{-xt}=e^{\delta^2t}.
\]

要使：

\[
e^{-ut}e^{-xt}
=
e^{-(u-\delta^2)t}
\]

在正半轴可积，需要：

\[
\boxed{u>\delta^2.}
\]

因此可以定义候选稳定化债务：

\[
\operatorname{StabilizationDebt}(-\delta^2)=\delta^2.
\]

这一结论的积分、可积性当且仅当条件和 resolvent 极点仍需独立 Lean 真源。

---

## 7. 下一承重形式化方向

### P0. NegativeSquareLaplaceResolvent

在精确条件 \(u>\delta^2\) 下证明：

\[
\int_0^\infty e^{-(u-\delta^2)t}\,dt
=
\frac1{u-\delta^2}.
\]

并证明可积性阈值：

\[
\operatorname{IntegrableOn}
\left(e^{-(u-\delta^2)t},[0,\infty)\right)
\iff
u>\delta^2.
\]

该节点把负二阶谱值连接到前向增长、附加阻尼预算和 resolvent 极点。

### P1. ReflectedGrowthPairEvenOddObservation

定义偶通道和奇通道：

\[
E_\delta(t)
=
\frac{e^{\delta t}+e^{-\delta t}}2,
\qquad
O_\delta(t)
=
\frac{e^{\delta t}-e^{-\delta t}}2.
\]

目标：

\[
E_\delta(-t)=E_\delta(t),
\qquad
O_\delta(-t)=-O_\delta(t),
\]

\[
E_\delta(t)^2-O_\delta(t)^2=1.
\]

偶通道保存反射不变量。奇通道保存定向。

### P2. OffLineCurvatureModeIntertwiner

把反射模式的二阶对数曲率精确运输到离线 dipole 公式。该节点应明确：

- 目标轨道贡献；
- 其他零点污染；
- Gamma 与 pole 项；
- 正翼和负核心；
- 截断误差；
- 剩余严格负裕量。

### P3. SignedNormalSpectralAtom

构造一个真正的 signed-normal support chart，使临界线轨道落在允许支撑：

\[
[0,\infty),
\]

离线反射轨道产生正质量的负支撑位置：

\[
-\delta^2<0.
\]

随后用 Chebyshev 多项式或 rational separator 将负支撑运输成有限矩和 Gram 负方向。

---

## 8. 当前 theorem DAG

```text
ReflectedGrowthPairNegativeSquare                 Frozen
        |
        v
ReflectedGrowthPairSecondOrderSpectrum            Candidate
        |
        +-----------------------------+
        |                             |
        v                             v
Even/Odd Observation               NegativeSquareLaplaceResolvent
        |                             |
        v                             v
Orientation Recovery               Stabilization Debt / Resolvent Pole
        |                             |
        +---------------+-------------+
                        |
                        v
              OffLineCurvatureModeIntertwiner
                        |
                        v
                SignedNormalSpectralAtom
                        |
                        v
             Chebyshev Negative-Support Witness
                        |
                        v
             Toeplitz / Pick / Weil Negative Direction
```

并行的算术强制链仍为：

```text
Prime / Gamma / Pole data
        |
        v
Balanced finite observer innovation
        |
        v
Blind-sector Schur coercivity
        |
        v
All finite Gram layers nonnegative
        |
        v
Uniform positive completion
        |
        v
Weil positivity
        |
        v
RH
```

检测链和强制链最终需要在同一个有限 master observer 上相遇。

---

## 9. 当前第一开放边

就负平方与时间方向这一子路线而言，下一条最小且无条件的真源是：

\[
\boxed{
\texttt{NegativeSquareLaplaceResolvent}.
}
\]

就整个 RH 路线而言，第一承重开放边仍然不是上述表示恒等式，而是：

\[
\boxed{
\texttt{PrimeArchimedeanBlindSchurCoercivity}
}
\]

或等价的逐层素数侧创新下界。前者负责说明离线缺陷怎样产生有限负证书。后者负责说明真实算术数据为什么不允许该负证书存在。
---

## [PR #4441] GOLDEN_SECOND_MAGNUS_SAMPLING

# 黄金二阶 Magnus 采样、时间色散与壳层商拓扑

**候选 GID：**

`D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling`

## 0. 本增补的地位

本增补把此前已经分别冻结的三层结构连接起来：

1. `GoldenScaleCircle` 给出黄金对数尺度与整壳平移；
2. `GoldenVerticalSampling` 给出黄金 Fourier 模式对应的 Mellin 竖直频率；
3. `SecondMagnusSwapCurvature` 给出时间槽与频率槽的交替二阶核。

本轮不重新定义 Fourier character，也不重新定义二阶 Magnus 核。新增节点只负责证明既有对象在黄金采样格上的兼容性，以及这些对象对完整黄金壳层平移的下降性质。

机器真源进入 admission 以前，本节全部标记为 candidate append。PR 通过 canonical Lean report、Scribe 一致性和 content-addressed admission 后，才可把相应陈述视为冻结真源。

---

## 1. 黄金对数周期与 Mellin 采样时间

已有黄金尺度周期为：

\[
\boxed{
L_\varphi=2\log\varphi.
}
\]

已有黄金基本角频率为：

\[
\boxed{
\Omega_\varphi
=\frac{\pi}{\log\varphi}
=\frac{2\pi}{L_\varphi}.
}
\]

本轮定义第 \(k\) 个整数黄金采样时间：

\[
\boxed{
t_k=k\Omega_\varphi,
\qquad k\in\mathbb Z.
}
\]

因此：

\[
\boxed{
t_kL_\varphi=2\pi k.}
\]

这个恒等式是壳层不可见性的核心。一个完整黄金壳层在对数尺度上前进 \(L_\varphi\)，整数采样模式只积累 \(2\pi k\) 的整圈相位。

这里的 \(t_k\) 是 Mellin 竖直参数的离散采样值，也就是 prime-frequency Fourier flow 的谱时间。它没有被解释为实验室物理时间。

---

## 2. 从正乘法群下降到黄金尺度圆

继续使用未取商坐标：

\[
\eta_\varphi(x)
=\frac{\log x}{L_\varphi}.
\]

对正数 \(x,y\)，已有：

\[
\eta_\varphi(xy)
=\eta_\varphi(x)+\eta_\varphi(y).
\]

本轮把它投影到单位加法圆：

\[
\boxed{
\vartheta_\varphi(x)
=\eta_\varphi(x)\pmod{\mathbb Z}
\in\mathbb R/\mathbb Z.
}
\]

机器证明：

\[
\boxed{
\vartheta_\varphi(xy)
=\vartheta_\varphi(x)+\vartheta_\varphi(y),
\qquad x,y>0.
}
\]

对任意 \(n\in\mathbb N\)，已有未取商平移律：

\[
\eta_\varphi\bigl((\varphi^2)^n x\bigr)
=\eta_\varphi(x)+n.
\]

因此机器证明：

\[
\boxed{
\vartheta_\varphi\bigl((\varphi^2)^n x\bigr)
=\vartheta_\varphi(x).
}
\]

这给出严格的商拓扑对象：

\[
\boxed{
\mathbb R_{>0}^{\times}/\varphi^{2\mathbb Z}
\longrightarrow
\mathbb R/\mathbb Z.
}
\]

本轮 Lean owner 使用自然数壳层平移，因为现有 `GoldenScaleCircle` 的公开迭代定理以 \(n\in\mathbb N\) 陈述。双向整数壳层作用和其商空间同胚仍可在后续节点中单独封装。

---

## 3. 黄金尺度 character 与既有 Fourier phase 是同一个对象

定义整数模式的黄金尺度 character：

\[
\boxed{
\Theta_k(x)
=
\exp\left(-2\pi i k\eta_\varphi(x)\right).
}
\]

它也可以理解为单位圆点 \(\vartheta_\varphi(x)\) 上的第 \(k\) 个 character。

本轮机器证明：

\[
\boxed{
\Theta_k(x)
=
\chi_{\log x}(t_k)
=
\exp(-it_k\log x).
}
\]

这条等式把两套已经存在的坐标精确识别：

\[
\boxed{
\text{黄金尺度圆的整数 Fourier mode}
=
\text{log-frequency flow 的黄金 Mellin 采样}.
}
\]

因此新增节点没有引入第二套相位语义。`goldenScaleFourierPhase` 是既有 `fourierPhase` 的黄金坐标表达。

机器同时证明：

\[
\boxed{|\Theta_k(x)|=1},
\]

以及对正数 \(x,y\)：

\[
\boxed{
\Theta_k(xy)=\Theta_k(x)\Theta_k(y).
}
\]

所以每个整数模式都是正乘法群到 \(U(1)\) 的酉 character。

---

## 4. 完整黄金壳层对整数模式不可见

由：

\[
\eta_\varphi\bigl((\varphi^2)^n x\bigr)
=\eta_\varphi(x)+n,
\]

得到：

\[
\Theta_k\bigl((\varphi^2)^n x\bigr)
=
\Theta_k(x)e^{-2\pi i kn}.
\]

因为 \(k\in\mathbb Z\) 且 \(n\in\mathbb N\)：

\[
e^{-2\pi i kn}=1.
\]

机器证明：

\[
\boxed{
\Theta_k\bigl((\varphi^2)^n x\bigr)
=
\Theta_k(x).
}
\]

这不是近似周期，也不是渐近自相似，而是精确下降关系。

因此整数黄金 Fourier family 只能看到壳层轨道：

\[
[x]
=
\left\{(\varphi^2)^n x:n\in\mathbb N\right\}.
\]

未取商尺度中的整壳编号被该观察器遗忘。这个遗忘正是 topology quotient 的含义，不应描述为信号在真实空间中消失。

---

## 5. 黄金采样把二阶 Magnus 核变成 character alternant

既有二阶核为：

\[
K_{x,y}(t_1,t_2)
=
\chi_{\log x}(t_1)\chi_{\log y}(t_2)
-
\chi_{\log y}(t_1)\chi_{\log x}(t_2).
\]

在两个黄金采样时间 \(t_{k_1},t_{k_2}\) 上，本轮机器证明：

\[
\boxed{
\begin{aligned}
K_{x,y}(t_{k_1},t_{k_2})
={}&
\Theta_{k_1}(x)\Theta_{k_2}(y)
\\
&-
\Theta_{k_1}(y)\Theta_{k_2}(x).
\end{aligned}
}
\]

所以该核是两个黄金 circle characters 的交替行列式：

\[
\boxed{
K_{x,y}(t_{k_1},t_{k_2})
=
\det
\begin{pmatrix}
\Theta_{k_1}(x)&\Theta_{k_1}(y)\\
\Theta_{k_2}(x)&\Theta_{k_2}(y)
\end{pmatrix}.
}
\]

这个表达把时间、色散和 topology 的职责分开：

- \(k_1,k_2\) 选择黄金尺度圆上的两个 character readouts；
- \(x,y\) 选择两个乘法尺度通道；
- 行列式读取两个 readout vectors 张成的有向面积；
- 交换通道或交换时间槽会翻转 orientation；
- 两行或两列退化时，二阶核归零。

该行列式解释沿用 `SecondMagnusSwapCurvature` 已经冻结的反对称结构。本轮只证明它在黄金采样格上的精确 realization。

---

## 6. 二阶核下降到壳层轨道

对任意自然姴壳层编号 \(n_x,n_y\)，本轮机器证明：

\[
\boxed{
\begin{aligned}
&K_{(\varphi^2)^{n_x}x,
      (\varphi^2)^{n_y}y}
  (t_{k_1},t_{k_2})
\\
&\qquad=
K_{x,y}(t_{k_1},t_{k_2}),
\qquad x,y>0.
\end{aligned}
}
\]

两个通道可以独立移动任意完整黄金壳层。相位矩阵的四个条目分别保持，因此 determinant 保持。

所以在黄金采样格上，二阶 Magnus 核通过以下商对象因子化：

\[
\boxed{
\left(
\mathbb R_{>0}^{\times}/\varphi^{2\mathbb Z}
\right)^2.
}
\]

这里形成的 topology 结论是 factorization through quotient。它不是 winding number、Chern class 或非平凡 line bundle 的存在定理。

---

## 7. 有限二阶 Magnus 能量也下降到壳层商

设有限通道类型为 \(P\)，每个通道具有正尺度 \(s_p\)、壳层编号 \(n_p\) 和既有曲率系数 \(C_{p,q}\)。定义黄金采样能量：

\[
\mathcal E^{(2),\varphi}_{P;k_1,k_2}(s,C)
=
\sum_{p,q\in P}
\left|
K_{s_p,s_q}(t_{k_1},t_{k_2})C_{p,q}
\right|^2.
\]

本轮机器证明：

\[
\boxed{
\mathcal E^{(2),\varphi}_{P;k_1,k_2}
\left(
\bigl((\varphi^2)^{n_p}s_p\bigr)_{p\in P},C
\right)
=
\mathcal E^{(2),\varphi}_{P;k_1,k_2}(s,C).
}
\]

因此该有限能量只依赖每个通道的黄金壳层轨道，不依赖所选代表元。

结合已经冻结的统一上界：

\[
0\le
\mathcal E^{(2)}_P(t_1,t_2)
\le
4\mathcal E^{\mathrm{hol}}_P,
\]

可以得到以下严格结构链：

\[
\boxed{
\begin{aligned}
&\text{residual envelope control}
\\
&\Longrightarrow
\text{finite holonomy energy control}
\\
&\Longrightarrow
\text{golden-sampled second-Magnus energy control}
\\
&\Longrightarrow
\text{the controlled observable descends through golden shell orbits}.
\end{aligned}
}
\]

最后一箭头描述观察空间的商结构，不增加新的衰减率。

---

## 8. 时间、色散、破缺与 topology 的当前严格关系

本轮以后，这五个概念可以按类型分层：

\[
\boxed{
\begin{array}{c|c}
\text{对象}&\text{机器中的角色}\\
\hline
L_\varphi&\text{黄金对数壳层周期}\\
t_k&\text{整数 Fourier mode 的 Mellin 谱时间}\\
\log x-\log y&\text{两个乘法通道的频率色散}\\
K&\text{时间槽与频率槽的反对称二阶响应}\\
\mathbb R_{>0}^{\times}/\varphi^{2\mathbb Z}
&\text{整数黄金模式可见的尺度商空间}
\end{array}
}
\]

色散本身是频率差：

\[
\Delta\omega_{x,y}
=\log x-\log y
=\log\frac{x}{y},
\qquad x,y>0.
\]

时间差与色散差共同进入已有正弦核：

\[
\left|K_{x,y}(t_{k_1},t_{k_2})\right|
=
2\left|
\sin\left(
\frac{(t_{k_1}-t_{k_2})(\log x-\log y)}2
\right)
\right|.
\]

因此反对称破缺的可见性需要：

1. 两个采样模式可区分；
2. 两个尺度通道可区分；
3. 对应 time-frequency area 不落在共振零点［
4. 被调制的曲率系数 \(C_{p,q}\) 本身非零。

本轮的壳层 invariance 说明，同一 quotient class 内的代表元变化不改变上述可见性。

---

## 9. 素数特化

取：

\[
x=p,
\qquad
y=q,
\]

其中 \(p,q\) 为素数。则：

\[
\Theta_k(p)
=
\exp\left(
-2\pi i k\frac{\log p}{2\log\varphi}
\right)
=
p^{-it_k}.
\]

黄金采样的素数对 kernel 为：

\[
\boxed{
K_{p,q}(t_{k_1},t_{k_2})
=
\Theta_{k_1}(p)\Theta_{k_2}(q)
-
\Theta_{k_1}(q)\Theta_{k_2}(p).
}
\]

它读取的相对尺度为：

\[
\frac{\log(p/q)}{2\log\varphi}.
\]

本轮没有证明该数对所有不同素数都无理，也没有证明黄金采样下的 kernel 对所有非平凡 mode pair 都非零。这些属于下一条非共振节点的义务。

---

## 10. 与 RH 的精确边界

零点侧已有黄金径向坐标和黄金周期 monodromy：

\[
M_\rho
=
\operatorname{diag}
\left(
\varphi^{2\delta},
\varphi^{-2\delta}
\right),
\qquad
\delta=\Re\rho-\frac12.
\]

prime side 的本轮对象位于 unitary angular layer：

\[
\Theta_k(p)\in U(1).
\]

zero side 的离线缺陷位于 radial hyperbolic layer：

\[
\delta\ne0
\Longrightarrow
M_\rho\text{ hyperbolic}.
\]

本轮建立的是 prime-side angular object 对黄金尺度商的拓扑下降。它没有提供 angular energy 到 radial hyperbolic discriminant 的 coercive transport。

RH 路线仍需要一条承重桥：

\[
\boxed{
\text{prime-side golden-sampled holonomy/Magnus data}
\Longrightarrow
\text{zero-side off-line radial or odd defect control}.
}
\]

这条桥可以走显式公式、Weil positivity、Schur coercivity或独立构造的 integral monodromy。当前节点没有选择其中任何一种作为已证事实。

---

## 11. 下一真源排序

本轮以后，最邻近的机器节点为：

1. `GoldenPrimeRatioNonresonance`。证明不同素数通道的相对黄金尺度不产生精确整数混叠，并精确列出证明所需的数论输入。
2. `FiniteGoldenMagnusCesaroRecovery`。在有限通道上证明黄金采样的 Cesàro 平均恢复非对角 holonomy energy。
3. `GoldenScaleSolenoidMemoryLift`。把完整壳层在可见圆上的闭合提升为 solenoid 隐藏 profinite fiber 中的非平凡记忆位移。
4. `CriticalStripIntegralMonodromyCollapse`。在明确的 integral-lattice realization 假设下，把临界带内的整数迹间隙运输为 \(\delta=0\)。
5. `PrimeArchimedeanBlindSchurCoercivity`。建立 prime-side 数据对 zero-side blind sector 的真正强制桥。

第一条和第二条继续完成黄金采样的可识别性。第三条负责 topology memory。第四条是条件性拓扑排除器。第五条仍是整个 RH 路线的解析 hard heart。

---

## 12. 严格非主张

本轮不主张：

- 黄金采样对不同素数频率具有统一正间隙；
- 所有不同素数对在所有非平凡 mode pair 上都具有非零 kernel；
- Cesàro 平均已经恢复 finite holonomy energy；
- 黄金尺度圆已经携带非零 winding、Chern class 或 Berry curvature；
- 自发对称破缺或物理时间箭头已经构造；
- 无限素数 second-Magnus energy 已经定义；
- prime-side 壳层商已经支配 zero-side radial defect；
- 离线零点已经排除；
- RH 已经证明。

本轮候选机器增量精确到：

\[
\boxed{
\begin{aligned}
&\text{golden logarithmic scale}
\\
&\Longrightarrow
\text{integral Mellin sample characters}
\\
&\Longrightarrow
\text{golden realization of the frozen second-Magnus alternant}
\\
&\Longrightarrow
\text{kernel and finite energy descend through whole-shell orbits}.
\end{aligned}
}
\]

---

## [PR #4443] ORDERED_MAGNUS_OBSERVABILITY — 二阶 Magnus 可观测性追加

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

---

## [PR #5065] CANONICAL_ZERO_DATA_NONVACUITY

# Canonical `ZeroData` inhabitant 与全称命题非空洞性

**候选 GID：**

- `D5/S3/Weil/ZetaBridge/RiemannVonMangoldtCountGrowth`
- `D5/S3/Weil/ZetaBridge/CanonicalZeroDataFromRiemannVonMangoldt`
- `D5/S3/Weil/ZetaBridge/ZeroDataSemanticNonvacuity`
- `D5/S3/Weil/ZetaBridge/CanonicalZeroDataProvider`
- `D5/S3/Weil/ZetaBridge/CanonicalZeroDataNonvacuityAssembly`

## 1. 语义空洞位于 `ZeroData` 的外层类型

仓库的 `ZeroData` 使用固定索引类型 `ℕ`。一旦存在一个值

```lean
Z : ZeroData
```

则 `Z.zero 0` 已经是由结构字段证明的非平凡 zeta 零点。因此本路线中的语义空洞风险不来自单个 `ZeroData` 的索引集为空，而来自类型 `ZeroData` 本身可能没有 inhabitant。

此时一个命题

\[
\forall Z:\operatorname{ZeroData},\;P(Z)
\]

可以在没有任何零点枚举被实例化时成立。

新节点定义：

\[
\boxed{
\operatorname{RealizedZeroDataClaim}(P)
\iff
\exists Z:\operatorname{ZeroData},\;P(Z).
}
\]

并形式化两条逻辑边：

\[
\neg\operatorname{Nonempty}(\operatorname{ZeroData})
\Longrightarrow
\forall Z:\operatorname{ZeroData},\;P(Z),
\]

\[
\operatorname{Nonempty}(\operatorname{ZeroData})
\land
\bigl(\forall Z:\operatorname{ZeroData},\;P(Z)\bigr)
\Longrightarrow
\exists Z:\operatorname{ZeroData},\;P(Z).
\]

所以后续审计必须区分“全称条件定理已经证明”和“该定理已经在真实 zeta 零点枚举上实现”。

## 2. Riemann–von Mangoldt 关闭非空洞链

`RiemannVonMangoldtCountGrowth` 从仓库已有结构字段中抽取：

\[
N_Z(T,2T)
=
\frac{T}{2\pi}\ell_1(T)+O(\log T),
\]

并证明：

\[
\boxed{
N_Z(T,2T)\longrightarrow+\infty.
}
\]

将其应用于 set-level canonical source `Zeta23.zetaZeroConfig`，得到：

\[
\boxed{
\begin{aligned}
&\operatorname{RiemannVonMangoldt}
  (\operatorname{zetaZeroConfig})
\\
&\Longrightarrow
N(T,2T)\to\infty
\\
&\Longrightarrow
\operatorname{zetaZeroConfig.carrier}\text{ infinite}
\\
&\Longrightarrow
\{\rho:\operatorname{IsNontrivialZero}(\rho)\}\text{ infinite}
\\
&\Longrightarrow
\operatorname{Nonempty}(\operatorname{ZeroData}).
\end{aligned}
}
\]

最后一箭头直接复用仓库已有的精确定理：

\[
\operatorname{Nonempty}(\operatorname{ZeroData})
\iff
\{\rho:\operatorname{IsNontrivialZero}(\rho)\}\text{ infinite}.
\]

因此新节点没有再次构造可数性、枚举、解析重数、反射、共轭或局部有限性证明。

## 3. Canonical provider 的含义

定义：

```lean
structure CanonicalZeroDataSource : Prop where
  riemannVonMangoldt :
    Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig
```

由该 source 选择：

\[
\operatorname{canonicalZeroData}(S)
:
\operatorname{ZeroData}.
\]

该值满足：

1. 每个枚举项都是真实非平凡 zeta 零点；
2. 每个真实非平凡 zeta 零点恰有一个自然数索引；
3. 存储的解析重数严格为正；
4. `ρ ↦ 1 - ρ` 的函数方程反射在索引上忠实实现并保持重数；
5. 复共轭在索引上忠实实现并保持重数；
6. 每个对称谱半径截断是有限集。

“canonical”在此表示 canonical zeta-zero object 及其不依赖枚举的观察量。自然数排序由 classical choice 选出，不声称是可计算或唯一的顺序。

仓库已有枚举不变性定理被直接复用。对任何另一份 `Z : ZeroData`：

\[
\operatorname{truncatedZeroSum}
(\operatorname{canonicalZeroData}(S),g,T)
=
\operatorname{truncatedZeroSum}(Z,g,T),
\]

对应的 `SymmetricConvergent` 命题等价，收敛后的 `zeroSum` 值相等。

## 4. 最终 certificate 与闭合主定理

`CanonicalZeroDataCertificate` 将下游消费者所需义务显式打包：

```text
actual ZeroData value
exact representation
unique exhaustive index
positive analytic multiplicity
reflection fidelity
conjugation fidelity
finite symmetric cutoffs
```

其精确表示定理为：

\[
\boxed{
\operatorname{IsNontrivialZero}(\rho)
\iff
\exists!n\in\mathbb N,\ C.data.zero(n)=\rho.
}
\]

主装配定理：

```lean
canonical_zeroData_closed_chain
```

证明：

\[
\boxed{
\operatorname{RvM}(\mathcal Z_\zeta)
\Longrightarrow
\left[
\mathcal Z_\zeta\text{ infinite}
\land
\operatorname{Nonempty}(\operatorname{ZeroData})
\land
\exists C:\operatorname{CanonicalZeroDataCertificate}
\right].
}
\]

扩展定理 `exists_faithful_zeroData_of_riemannVonMangoldt` 直接返回一个实际 `ZeroData`，以及全部表示、重数、对称和局部有限保证。

## 5. 全称命题的语义实现

对任意谓词：

```lean
P : ZeroData → Prop
```

如果已经证明：

```lean
h : ∀ Z : ZeroData, P Z
```

则 canonical source 给出：

\[
\boxed{
\exists C:\operatorname{CanonicalZeroDataCertificate},
\quad
P(C.data)
\land
\exists\rho:\mathbb C,
\operatorname{IsNontrivialZero}(\rho).
}
\]

因此围绕 `ZeroData` 的全称定理可以被实例化到一个真实、穷尽、重数忠实的 zeta 零点枚举上。外层类型为空导致的语义空洞由该 certificate 消除。

## 6. 当前 claim boundary

本 PR 关闭的是以下完整逻辑链：

\[
\boxed{
\begin{aligned}
\operatorname{RiemannVonMangoldt}
  (\operatorname{zetaZeroConfig})
&\Longrightarrow
N(T,2T)\to\infty
\\
&\Longrightarrow
\text{nontrivial-zero set infinite}
\\
&\Longrightarrow
\operatorname{Nonempty}(\operatorname{ZeroData})
\\
&\Longrightarrow
\text{actual exhaustive multiplicity-aware enumeration}
\\
&\Longrightarrow
\text{canonical provider and certificate}
\\
&\Longrightarrow
\text{universal ZeroData claims are realized}.
\end{aligned}
}
\]

`RiemannVonMangoldt zetaZeroConfig` 在本 PR 中仍作为显式 source。把 provider 进一步升级为 hypothesis-free 常量，需要将仓库中的 global Riemann–von Mangoldt assembly 独立接入该 source。该剩余步骤属于解析数论 owner 的实例化，不再是 `ZeroData` 的枚举、重数、对称或语义逻辑缺口。

本节不声明 RH，不使用 RH，也不把尚未经过 admission 的 Candidate 描述为 Frozen。

---

## [PR #5065] UNCONDITIONAL_CANONICAL_ZERO_DATA_CLOSURE

# 无参数 `zetaZeroData` 与解析来源闭合

本增补恢复本 PR 误删的历史理论段，并把此前显式接收 `RiemannVonMangoldt zetaZeroConfig` 的条件链升级为无参数机器构造。

新增 proof-complete 路径为：

\[
\boxed{
\begin{aligned}
\texttt{GammaStirlingVert.mu\_stirling}
&\Longrightarrow \texttt{GammaFacts},\\
\texttt{GammaFacts}
&\Longrightarrow \texttt{RiemannVonMangoldt(zetaZeroConfig)},\\
\texttt{RiemannVonMangoldt}
&\Longrightarrow N(T,2T)\to\infty,\\
&\Longrightarrow \mathcal Z_\zeta\text{ infinite},\\
&\Longrightarrow \operatorname{Nonempty}(\texttt{ZeroData}),\\
&\Longrightarrow \texttt{zetaZeroData : ZeroData}.
\end{aligned}
}
\]

机器 owner 为：

```text
D5/S3/Weil/ZetaGamma/GammaIntMu.lean
D5/S3/Weil/ZetaGamma/GammaFactsComplete.lean
D5/S3/Weil/ZetaPntBase/ZetaConj.lean
D5/S3/Weil/ZetaRvm/Defs.lean
D5/S3/Weil/ZetaRvm/NcountWindow.lean
D5/S3/Weil/ZetaRvm/GammaSide.lean
D5/S3/Weil/ZetaRvm/BacklundDefs.lean
D5/S3/Weil/ZetaRvm/ReZeroCount.lean
D5/S3/Weil/ZetaRvm/Backlund.lean
D5/S3/Weil/ZetaRvm/Fold.lean
D5/S3/Weil/ZetaRvm/MainTerm.lean
D5/S3/Weil/ZetaRvm/Statement.lean
D5/S3/Weil/ZetaBridge/UnconditionalCanonicalZeroData.lean
```

`zetaZeroData` 是一个固定的自然数索引 presentation。其顺序由 `Classical.choice` 选出。canonical 内容位于它穷尽表示的真实非平凡零点集合、解析重数、反射与共轭作用，以及已经证明为枚举不变的零点观察量。

无参数接口闭合以下事实：

1. `ZeroData` 确实有 inhabitant；
2. 每个 `zetaZeroData.zero n` 都是真实非平凡 zeta 零点；
3. 每个真实非平凡零点恰有一个索引；
4. 存储重数是严格正的解析零点阶；
5. 函数方程反射与复共轭由索引置换忠实实现，并保持重数；
6. 每个对称谱半径截断有限；
7. 枚举上的全称命题与真实非平凡零点上的全称命题等价；
8. 围绕 `ZeroData` 的任意全称结构定理都可以直接实例化到 `zetaZeroData`。

本增补没有为自然数编号赋予高度排序、可计算性或内在意义，也没有使用 RH。它关闭的是实际零点对象进入既有 `ZeroData` consumer DAG 的语义入口。


---

## [PR #5065] MIRROR_KREIN_OPERATOR_GEOMETRY

# 无参数 zeta 零点的镜像 Krein 算子几何

**候选 GID：**

```text
D5/S3/Weil/ZetaBridge/ZeroDataPresentationEquiv
D5/S3/Midline/Cayley/CanonicalZetaMirrorFundamentalSymmetry
D5/S3/Midline/Cayley/CanonicalZetaCayleyJUnitary
D5/S3/Midline/Cayley/FiniteMirrorKreinIndex
```

本节建立在同一 PR 的无参数对象 `zetaZeroData : ZeroData` 之上。全部陈述在 admission 完成以前属于 Candidate，Lean 声明承担唯一承重角色。

### 1. presentation 选择与 canonical 内容

任意两个 `ZeroData` 值之间存在唯一的零点保持重标号：

\[
e_{Z,Z'}:\mathbb N\simeq\mathbb N,
\qquad
Z'.\operatorname{zero}(e_{Z,Z'}n)=Z.\operatorname{zero}(n).
\]

该等价同时保持解析重数、谱参数、函数方程反射、复共轭和同高度镜像，并满足恒等、逆与复合律。因此自然数编号仍是 choice-based presentation，零点、重数、对称作用以及沿唯一重标号运输的观察量具有 presentation-independent 内容。

### 2. 同高度镜像与固定点

定义 \(M_Z=C_Z\circ R_Z\)，其中 \(R_Z\) 是函数方程反射，\(C_Z\) 是复共轭。机器节点证明：

\[
Z.\operatorname{zero}(M_Zn)=1-\overline{Z.\operatorname{zero}(n)},
\]

\[
M_Z^2=I,
\qquad
m_{M_Zn}=m_n,
\qquad
\gamma_{M_Zn}=\overline{\gamma_n},
\]

以及：

\[
\boxed{M_Zn=n\iff\operatorname{Re}\rho_n=\frac12.}
\]

所以临界线是由函数方程与实结构预先确定的 involution 固定集。

### 3. fundamental symmetry 与严格负方向

镜像通过解析重数提升到：

\[
\mathcal I_Z=\sum_{n:\mathbb N}\operatorname{Fin}(m_n),
\]

并在 \(\mathcal H_Z=\ell^2(\mathcal I_Z)\) 上给出 involutive linear isometry \(J_Z\)。机器节点证明：

\[
J_Z^2=I,
\qquad
\langle J_Z\psi,\phi\rangle=\langle\psi,J_Z\phi\rangle.
\]

定义：

\[
[\psi,\phi]_{J_Z}=\langle\psi,J_Z\phi\rangle.
\]

每个被镜像移动的坐标 \(v\) 给出奇向量 \(v_-=e_v-J_Ze_v\)，并满足：

\[
J_Zv_-=-v_-,
\qquad
[v_-,v_-]_{J_Z}=-\|v_-\|^2<0.
\]

### 4. Cayley 算子无条件 J-unitary

对 \(c(\rho)=(\rho-1)/\rho\)，镜像坐标满足：

\[
c(1-\overline\rho)=\overline{c(\rho)}^{-1}.
\]

因此 multiplicity-expanded 对角 Cayley 算子 \(U_Z\) 满足：

\[
\boxed{U_Z^*J_ZU_Z=J_Z.}
\]

该结论只使用函数方程与复共轭对称，不使用 RH。普通 Hilbert 酉性是更强的临界线条件。

### 5. 有限镜像 Krein 指数

在有限对称谱窗口 \(S_T\) 中，从每个非固定二元镜像轨道选一个代表，并按解析重数展开。定义：

\[
\kappa_T=\sum_{\substack{n\in S_T\\n<M_Zn}}m_n.
\]

机器节点证明有限奇坐标空间的基数为 \(\kappa_T\)，其标准负型在每个非零向量上严格为负，并且：

\[
\boxed{\kappa_T=0\iff\forall n\in S_T,\ \operatorname{Re}\rho_n=\frac12.}
\]

---

## [PR #5065] MIRROR_KREIN_SECOND_LAYER_CLOSURE

# 换枚举不变性、正交偶奇分解、Krein 逆与真实 Gram 惯性

**候选 GID：**

```text
D5/S3/Midline/Cayley/ZeroDataHilbertPresentationTransport
D5/S3/Midline/Cayley/CanonicalZetaMirrorEvenOddDecomposition
D5/S3/Midline/Cayley/CanonicalZetaCayleyKreinInverse
D5/S3/Midline/Cayley/FiniteMirrorKreinGramInertia
```

### 1. 整个 Hilbert 算子系统与 presentation 无关

唯一零点保持重标号提升为 unitary：

\[
T_{Z,Z'}:\mathcal H_Z\simeq_u\mathcal H_{Z'}.
\]

它同时满足：

\[
TJ_Z=J_{Z'}T,
\qquad
TU_Z=U_{Z'}T,
\qquad
[T\psi,T\phi]_{J_{Z'}}=[\psi,\phi]_{J_Z}.
\]

因此镜像、Cayley 动力学和不定内积不依赖 choice-based 自然数编号。

### 2. 规范化偶奇投影

定义：

\[
P_+=\frac{I+J}{2},
\qquad
P_-=\frac{I-J}{2}.
\]

机器节点证明幂等性、互相湮灭、精确重建、\(\pm1\) 镜像本征律和 Hilbert 正交性。Krein 能量精确分解为：

\[
\boxed{\operatorname{Re}[\psi,\psi]_J=\|P_+\psi\|^2-\|P_-\psi\|^2.}
\]

所以负扇区是实际 mirror-odd spectral range。

### 3. 显式有界 Krein 逆

镜像互反使倒数 Cayley 系数可以由已有有界系数经镜像置换和共轭获得。由此构造有界双侧逆，并证明：

\[
\boxed{U^{-1}=JU^*J,}
\qquad
UJU^*=J.
\]

这一步不需要普通酉性或 RH。

### 4. 真实有限奇向量 Gram 惯性

对每个有限镜像轨道代表和每个重数副本，取实际 Hilbert 奇向量 \(v_i^-=e_i-Je_i\)。机器节点计算：

\[
[v_i^-,v_j^-]_J=-2\delta_{ij}.
\]

因此实际 Gram 矩阵是 \(G_T^-=-2I\)，并由仓库统一惯性接口证明：

\[
\boxed{\operatorname{negIndex}(G_T^-)=\kappa_T.}
\]

该定理确认零点目标几何本身拥有 \(\kappa_T\) 维负空间。它不意味着指定的标量 Weil 观察器能覆盖该完整 multiplicity-expanded 空间。

---

## [PR #5065] REDUCED_WEIL_OBSERVER_AND_MULTI_ORBIT_NEGATIVITY

# 标量偶 Weil 观察器的可达空间、约化因子分解与多轨道负证书

**候选 GID：**

```text
D5/S3/Weil/ZetaBridge/WeilEvaluationObservableSubspace
D5/S3/Weil/ZetaBridge/FiniteMirrorReducedWeilFactorization
D5/S3/Weil/ZetaBridge/FiniteEvenWeilOddInterpolation
D5/S3/Weil/ZetaBridge/QuantitativeMultiOrbitWeilNegativeCertificate
```

本增补修正“标量偶 Weil 测试满秩覆盖完整 multiplicity-expanded mirror-odd 空间”的过强目标。真实观察器只访问一个约化空间。所有新陈述在 admission 完成以前属于 Candidate。

### 1. 两个真实秩障碍

对有限窗口 \(I_T\)，标量评价为：

\[
E_T(g)(n)=\widehat g(\gamma_n),
\qquad
\widetilde E_T(g)(n,k)=\widehat g(\gamma_n).
\]

所以评价在每个解析重数纤维上常值，不能区分同一零点的不同副本。

同时，`WeilTestFunction` 的偶性给出 \(\widehat g(-z)=\widehat g(z)\)，而 \(\gamma_{R(n)}=-\gamma_n\)。因此：

\[
E_T(g)(R(n))=E_T(g)(n).
\]

新节点构造显式目标向量并证明：

\[
m_n\ge2\Longrightarrow\widetilde E_T\text{ 不满射},
\]

以及窗口中存在移动的反射对时：

\[
E_T\text{ 不满射到全部 distinct-zero vectors}.
\]

这说明 ambient Krein 负空间和 observer-reachable 负空间必须分开计算。

### 2. 约化有限镜像形式

定义 `FiniteReflectionEvenVector Z T` 为满足反射偶约束的 distinct-zero 向量。解析重数作为形式中的正权重保留，不再被重复解释为独立标量观察坐标。

对 \(v_g(n)=\widehat g(\gamma_n)\)，定义：

\[
B_T(v,w)=\sum_{n\in I_T}m_n v(n)\overline{w(M(n))}.
\]

机器节点证明实际有限卷积平方零点和满足：

\[
\boxed{\operatorname{truncatedZeroSum}(Z,\operatorname{convolutionSquare}(g),T)=B_T(v_g,v_g).}
\]

对任意有限选择的非实离线四点轨道块，已有单轨道公式被聚合为：

\[
\boxed{Q_{\mathrm{block}}=E_{\mathrm{even}}-E_{\mathrm{odd}},\qquad E_{\mathrm{even}},E_{\mathrm{odd}}\ge0.}
\]

### 3. 约化奇空间上的显式线性插值

`FiniteEvenWeilOrbitFrame` 记录有限个离线非实轨道通道及其两组节点 \(\gamma_i,\overline{\gamma_i}\)，并显式携带仓库有限偶插值定理所需的 sign-separation 条件。

对任意 \(a:\iota\to\mathbb C\)，机器节点构造偶 Weil 测试函数，使：

\[
\widehat g(\gamma_i)=a_i,
\qquad
\widehat g(\overline{\gamma_i})=-a_i.
\]

约化奇读数：

\[
O_i(g)=\frac{\widehat g(\gamma_i)-\widehat g(\overline{\gamma_i})}{2}
\]

于是满足 \(O_i(g)=a_i\)。节点进一步选择坐标测试函数 \(g_i\)，定义显式有限线性合成：

\[
S(a)=\sum_i a_i g_i,
\]

并证明：

\[
\boxed{O_j(S(a))=a_j.}
\]

因此 \(S\) 是约化奇读数的右逆，并且是单射。

### 4. 可观察奇 Gram 的精确负指数

定义约化奇形式：

\[
B^-(g,h)=-4\sum_i m_i\overline{O_i(g)}O_i(h).
\]

坐标插值基满足 \(B^-(g_i,g_j)=-4m_i\delta_{ij}\)。所以真实可观察奇 Gram 为：

\[
\boxed{G_{\mathrm{obs}}^-=-4\operatorname{diag}(m_i).}
\]

解析重数严格为正，因此：

\[
\boxed{\operatorname{negIndex}(G_{\mathrm{obs}}^-)=|\iota|.}
\]

每个 independently interpolated orbit channel 贡献一个负方向。重数决定权重与稳定裕量，不增加标量观察器维数。

### 5. 整个负子空间的定量稳定性

对一般有限权重 \(w_i\ge m>0\)，定义 \(Q_0(a)=-\sum_iw_i|a_i|^2\)。若完整形式满足：

\[
Q(a)=Q_0(a)+R(a),
\]

并且存在统一二次余项界：

\[
|R(a)|\le\varepsilon\sum_i|a_i|^2\quad\text{对所有 }a,
\]

且 \(\varepsilon<m\)，则新通用定理证明：

\[
\boxed{a\ne0\Longrightarrow Q(a)<0.}
\]

这是整个有限维负子空间的稳定性结论。仅逐基向量控制余项不足，因为交叉项仍可能破坏线性组合上的负定性。

在 Weil 特化中：

\[
Q_{\mathrm{target}}(a)=-4\sum_i m_i|a_i|^2,
\]

\[
Q_{\mathrm{full}}(a)=\operatorname{Re}\operatorname{zeroSum}\left(Z,S(a)*\widetilde{S(a)}\right),
\]

并精确定义 \(R(a)=Q_{\mathrm{full}}(a)-Q_{\mathrm{target}}(a)\)。`QuantitativeMultiOrbitCertificate` 只要求一个正重数下界 \(m_*\)、统一余项界和 \(\varepsilon<4m_*\)。随后得到：

\[
\boxed{a\ne0\Longrightarrow Q_{\mathrm{full}}(a)<0,}
\]

且合成映射 \(S\) 单射。这给出一整个有限维、彼此独立的严格负完整 Weil 测试族。

### 6. 与现有单轨道 separator 的关系

仓库已有 `OffLineNonrealZeroNegativeWeilSquare` 使用 finite even interpolation、closed-strip Fourier–Laplace decay、convolution-power amplification 和 absolute zero summability，将一个指定离线轨道的负贡献压过其余零点尾项。

新多轨道链没有重复该单轨道构造。它抽取了多维推广所需的正确接口：

\[
\boxed{\text{统一余项的 operator-norm 型二次界}}
\]

而不是每个坐标单独的标量尾界。

下一解析节点应从已有 Burnol powering 与 closed-strip decay 中构造 `HasUniformMultiOrbitRemainderBound F epsilon`，并证明其 \(\varepsilon\) 可低于 \(4m_*\)。

### 7. 当前严格边界

本轮已经形式化：

1. scalar even Weil evaluation 的 multiplicity-fiber constancy；
2. functional-equation reflection evenness；
3. 对 ambient expanded space 和 unrestricted distinct-zero space 的显式非满射证书；
4. 有限实际卷积平方零点和的约化镜像因子分解；
5. 有限 orbit block 的 even-minus-odd 聚合；
6. sign-separated 多轨道约化奇读数的同时插值；
7. 显式有限线性 right inverse；
8. 可观察奇 Gram \( -4\operatorname{diag}(m_i) \)；
9. 其负指数等于独立可观察轨道数；
10. 统一二次余项小于最小负裕量时，整个有限维负子空间保持严格负定；
11. 对真实 `zeroSum` 的条件性多轨道负测试族。

本轮没有证明任意未经筛选的有限轨道集合自动满足 frame 的 sign-separation，也没有从 zeta 尾项具体构造 uniform multi-orbit remainder bound。它没有把 observer negative index 与完整 multiplicity-expanded ambient Krein index混同，也没有证明无限维负指数稳定、prime-side coercivity 或 RH。

### 8. 下一承重方向

下一条分析真源应为：

```text
MultiOrbitBurnolUniformRemainder
```

目标是从已有 closed-strip decay、convolution power 和绝对零点可和性，给有限 frame 构造共同 peak packet 与共同 exception killer，并证明：

\[
|R_N(a)|\le\varepsilon_N\|a\|_2^2,
\qquad
\varepsilon_N\to0.
\]

关键义务包括全部选定轨道上的目标读数同时保持、其余有限异常零点同时消去、远端零点统一几何衰减、交叉项按 Gram/operator norm 共同控制，以及常数随 frame 大小与最小节点分离显式记账。


---

## [PR #5065] UNIFORM_MULTI_ORBIT_BURNOL_REMAINDER

Candidate formalization, 2026-09-05. No successful Lean compilation or axiom audit is claimed by this source-write operation. The reviewed development baseline was `a2412c6c5cbfdcf38145b6386ac54a3cdc536408`; the existing candidate frame APIs were read at `fcfc744126d37ede7750dbecc4b840b5a8923bd7`. This increment stays on the existing draft PR, without merge or rebase.

### Correction and library-first reuse

Scalar even Weil tests remain constant on multiplicity copies and under functional-equation reflection. The result concerns independently observable four-point orbit channels. Multiplicity sets a weight and margin, not extra scalar rank.

The earlier basis constructor chose a witness after forgetting its full signed values. It is now selected from `exists_even_weil_frame_interpolant`. The public `frameOddBasisTest_target_values` and `frameOddSynthesis_target_values` retain the exact +a/-a values and hence zero target even channel.

Eight previously private helper declarations in the existing single-orbit Burnol owner are made public with unchanged proof bodies. These supply the reflection quotient, gamma injectivity, sign separation, actual zero summability, geometric-depth choice, and equality of the symmetric zero sum with its ordinary tsum. They are reused rather than independently redefined.

### Closed finite-frame chain

The four owners below construct a common peak, a common finite exceptional ball, simultaneous signed killers, an absolutely summable majorant for ALL mixed terms, and finally a single common power depth at which every nonzero coefficient vector gives a negative FULL Weil zero sum.

For E(a)=sum_i |a_i|^2, the actual target union contributes -4 sum_i m_i |a_i|^2. The actual complement satisfies

`|R_N(a)| <= (1/4)^(N+1) C_basis E(a)`.

C_basis is the sum of the absolute mixed-convolution majorants. Its finiteness is proved from existing zeta summability. It depends on the fixed finite basis, but not on a or N. The power factor tends to zero. Since each analytic multiplicity is at least one, one common finite N suffices for strict negativity on the whole nonzero coefficient space.

This constructs a jointly localized basis. It does not assert that the older arbitrarily chosen fixed synthesis already had the full remainder estimate.

### Source-level details

#### `FiniteReflectionCompatibleWeilInterpolation`

Status: Candidate source and author projection. Kernel and Scribe reconciliation remain separate checks.

For actual zero data Z, a finite set E of indices, and complex values a satisfying a(R j)=a(j), the module constructs a compact smooth even Weil test g with FT(g)(gamma_j)=a(j) for every j in E.

The construction reuses the reflection representative and frequency-injectivity lemmas from the existing single-orbit separator. It invokes `even_weilTestFunction_finite_interpolation` on the sign quotient. It does not reconstruct the Fourier-Laplace interpolation theorem.

The constant assignment gives a simultaneous unit peak on any finite union of zero orbits.

Main declarations:

- `even_weil_interpolation_on_finite_indices`
- `exists_even_weil_finite_unit_peak`

#### `FiniteOrbitBurnolPacket`

Status: Candidate source and author projection.

For a valid `FiniteEvenWeilOrbitFrame`, the module first proves that the actual four-point zero orbits are pairwise disjoint. It then constructs one peak b, a finite exceptional spectral ball E, and tests k_i satisfying:

1. FT(b)=1 at both selected conjugate spectral nodes of every channel.
2. FT(k_i)(gamma_j)=delta_ij and FT(k_i)(conj gamma_j)=-delta_ij.
3. Every k_i vanishes at all exceptional zero indices outside the target union.
4. Outside E, both conjugate evaluations of b have norm at most 1/2.

Existence follows from finite compatible interpolation and the existing closed-strip decay estimate. The simultaneous exceptional set is essential: multiplying separately chosen single-orbit packets would not automatically preserve the other target values.

Main declarations: `frame_orbits_pairwise_disjoint`, `exists_common_exceptional_ball`, `exists_orbitBurnolPacket`.

#### `FiniteMixedWeilMajorant`

Status: Candidate source and author projection.

For a finite basis k_i define the actual mixed terms

`M_ij(n) = zeroSummand Z (convolve (k_i) (involution (k_j))) n`.

Every M_ij is absolutely summable by the existing zeta summability theorem. The complete coefficient expansion is

`s_n(a) = sum_ij a_i conjugate(a_j) M_ij(n)`.

With `E(a)=sum_i |a_i|^2` and `B(n)=sum_ij |M_ij(n)|`, the module proves

`|s_n(a)| <= E(a) B(n)` and `sum_n |s_n(a)| <= E(a) C`, where `C=sum_n B(n)`.

B is proved summable. C depends on the fixed basis and includes every mixed term. It is not postulated as an operator-norm hypothesis.

Main declarations: `mixedWeilSummand_summable`, `zeroSummand_finite_synthesis_expansion`, `finiteMixedMajorant_summable`, `finite_synthesis_absolute_sum_le`.

#### `MultiOrbitBurnolUniformRemainder`

Status: Candidate source and author projection. No successful Lean compilation is claimed by this document.

The actual synthesized tests are

`f_N,a = sum_i a_i (b^{*(N+1)} * k_i)`.

Both target signs are preserved at every N. In particular the selected even channels vanish. The exact selected-orbit union contributes

`-4 sum_i m_i |a_i|^2`.

Writing the complete, absolutely convergent Weil zero sum as that contribution plus R_N(a), the module derives

`|R_N(a)| <= (1/4)^(N+1) C_basis sum_i |a_i|^2`.

The factor tends to zero independently of a. Positive integral analytic multiplicities give the target margin 4, so one finite common N makes the full form strictly negative on every nonzero coefficient vector. Reduced odd evaluation remains a right inverse, proving synthesis injective.

This closes the finite-frame remainder obligation that was previously an input to `QuantitativeMultiOrbitWeilNegativeCertificate`. It does not instantiate that older certificate for its arbitrary fixed basis; it constructs a new, jointly localized basis with proved estimates.

The valid frame is the only orbit assumption. Neither existence of off-line zeros nor a uniform estimate over all moving frames is asserted. Empty frames give the zero-dimensional case; a nonempty frame is required to extract an actual negative test.

Main declarations: `burnolSynthesis_target_union_value`, `multiOrbitBurnol_uniform_remainder`, `multiOrbitBurnol_error_tendsto_zero`, `exists_common_depth_strictly_negative`, `finite_multiOrbit_full_weil_negative_family`.

### Boundaries and next quantitative problems

A valid finite frame of nonreal off-line orbits is an input; existence of an off-line zero is never asserted. An empty frame is zero-dimensional. A nonempty frame is required for an actual negative test.

The constant and selected depth are classical and frame dependent. No computable estimate in minimum node separation, frame size, support radius, or height is established. Convolution depth may enlarge support. No uniform support window over all frames, infinite negative-index stability, prime-side coercivity, RH, or stronger zero-density theorem is claimed.

Next load-bearing goals are to package the actual full mixed Gram as a Hermitian matrix and identify its negative inertia with the realized test dimension, then derive explicit interpolation-conditioning and support-growth bounds and independently verifiable prime/Archimedean margins.


## [PR #5065] EXACT_OBSERVABLE_RANGE_AND_FULL_WEIL_GRAM_INERTIA

[PR #5065] Status: Candidate formalization. This section records the mathematical source increment, not an admission verdict. A source-write workflow, a targeted Lean replay, transitive axiom auditing and the repository required checks are different pieces of evidence. No merge or ready transition is authorized by this appendix.

### [PR #5065] Exact image of the original scalar even observer

[PR #5065] For a fixed ZeroData presentation Z and symmetric finite window T, write I_T for its distinct-zero indices and C_T for the dependent sum of the actual multiplicity copies. The original state space remains all WeilTestFunction values. The new owner `WeilEvaluationExactObservableRange` proves that an index vector v is a genuine Fourier-Laplace evaluation of an actual compact smooth even test if and only if v is invariant under the existing reflection permutation. The proof extends v by zero outside the window and reuses `even_weil_interpolation_on_finite_indices`. Symmetric-window closure proves that the extension remains compatible.

[PR #5065] At the expanded-coordinate level the exact characterization is: w is reachable if and only if w is constant on each multiplicity fiber and its collapsed index vector is reflection even. Every actual analytic multiplicity is positive, so collapse can read its zeroth genuine copy. Expansion and collapse are inverse on the fiber-constant subspace. The previously defined `finiteWeilReducedEvaluation` is consequently surjective onto its specified reduced codomain. These statements supply the converse missing from the earlier necessary-constraint package.

### [PR #5065] Intrinsic-information interpretation on the unchanged arena

[PR #5065] The same new owner proves, for arbitrary original test states g and h, that equality of multiplicity-expanded readouts is equivalent to equality of distinct-zero readouts. Adding the expanded readout as a joint observer also leaves the kernel unchanged. Therefore no pair of original states can witness strict fiber separation by multiplicity replication. This is a semantic zero-gain theorem. Multiplicity still changes the quadratic weight and negative margin, while repeated copies contribute no additional scalar information.

[PR #5065] This interpretation follows `docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md`: no truth-conditioned State subtype, certificate label or compilation status is used as an observable. The arena is infinite and complex-valued, so this increment does not apply finite pair-count probabilities to it, invent a normalized measure, or claim a new PrimLawSpec/admission. The observable subtype is a codomain characterization, never a restricted state arena. Host-side source delivery and diagnostics supply no Lean theorem assumptions.

### [PR #5065] Mixed finite factorization on the exact range

[PR #5065] `truncatedZeroSum_mixed_eq_reducedMirrorForm` extends the earlier convolution-square identity to arbitrary actual tests g and h. The finite zero sum of convolve(g, involution(h)) is exactly the existing mirror sesquilinear form evaluated on their reduced readouts. This identifies all off-diagonal finite Gram entries and preserves one analytic multiplicity weight per distinct zero. It reuses the existing mirror permutation and form instead of rebuilding them.

### [PR #5065] The actual complete Gram matrix

[PR #5065] The new owner `WeilFullGramInertia` defines W(g,h) as the complete absolutely convergent sum of the actual mixed summands, and sets G_ij = W(b_j,b_i). The index order gives the standard conjugate-linear row convention. Mirror reindexing preserves multiplicity and conjugates the spectral parameter, proving conjugate(W(g,h)) = W(h,g), hence G is Hermitian. Mixed absolute summability permits both finite coefficient sums to commute with the complete zero sum. The resulting exact identity is

```math
a^*G a = Z\!\left(\left(\sum_i a_i b_i\right)*
  \left(\sum_i a_i b_i\right)^*\right).
```

[PR #5065] Here Z denotes the actual full Weil zero functional, not a finite target-only replacement. Every infinite-tail cross term remains in G. In particular this appendix does not assert that the full Gram equals the finite target diagonal -4 diag(m_i).

### [PR #5065] Exact spectral inertia of the realized family

[PR #5065] The existing `finite_multiOrbit_full_weil_negative_family` constructs an injective finite linear synthesis whose complete Weil square has strictly negative real part on every nonzero complex coefficient vector. The new Gram identity transports this result to Matrix.PosDef(-G). Hermitian reality justifies passing from the real-part inequality to the complex star order. The existing RHLinalg negative-index implementation and the standard positive-definite eigenvalue theorem then give

```math
\boxed{\operatorname{negIndex}(G)=\#\{\text{independent observable orbit channels}\}.}
```

[PR #5065] The final declaration is `exists_actual_full_weil_gram_with_exact_negative_index`. Its matrix is built from actual tests and the complete zero sum. No assumed uniform remainder remains beyond the already constructed common Burnol packet. The theorem retains a valid finite separated nonreal off-line orbit frame as input; it does not assert existence of an off-line zero. Empty frames give dimension zero. It does not equate this observable index with the multiplicity-expanded ambient index, prove RH or prime-side coercivity, or supply computable support and conditioning bounds uniform over moving frames.

### [PR #5065] Source interfaces and next quantitative obligation

[PR #5065] Both owners have Scribe sources, author Markdown projections and explicit #print axioms requests for their main declarations. The full-Gram module imports the exact-range owner and the existing common Burnol owner, so it is a single dependency-closure replay root for this increment. Matrix interfaces were checked against the repository-pinned Mathlib v4.33.0 source, including `Matrix.PosDef.of_dotProduct_mulVec_pos`, `Matrix.IsHermitian.im_star_dotProduct_mulVec_self` and `Complex.pos_iff`. The eigenvalue-to-index step reuses the repository pattern in `FiniteMirrorKreinGramInertia`. Provenance of the integration is repo-derived; no independent novelty claim for classical interpolation or spectral inertia is made.

[PR #5065] The next quantitative work is to bound interpolation conditioning and convolution support growth for specified frames, then transport an explicit remaining negative margin through the prime/Archimedean explicit-formula interface. A finite full negative-index realization alone supplies no prime-side positive coercivity and no contradiction to a hypothesized off-line frame.


## [PR #5065] FINITE_OBSERVABLE_TO_FULL_FORM_LIMIT_AND_REPLAY_CORRECTIONS

[PR #5065] The full-Gram owner now includes `reducedMirrorForm_tendsto_fullMixedWeilForm`: for each actual pair of Weil tests, the multiplicity-weighted reduced mirror forms on growing symmetric windows converge to the actual complete mixed Weil form. The proof uses `truncatedZeroSum_tendsto` from the existing ZeroSum owner and the exact mixed factorization. This is a genuine finite-to-full mathematical dependency on the exact observable range layer.

[PR #5065] Pinned root observations 33969082693 and 33969495413 both failed. The first exposed obsolete finite-sum syntax and an unclosed mirror inverse simplification. The second verified the repaired mirror inverse with only standard axioms, then exposed a finite-window unfolding mismatch and a accidentally omitted second ZeroData binder introduced during the source repair. This revision explicitly unfolds `ZeroConfig.window` and restores that binder, without changing the intended theorem statements or admitting a placeholder. Compiler error recovery containing `sorryAx` is rejected as validation evidence. The new frozen source revision still requires its own observed successful root replay and independent required checks before any admission claim.


---

## RH_EQUIVALENCE_ATLAS_20260908

### RH 等价形式图谱：规范对象、跨领域证明与形式化路线

资料核查日期：2026-09-08。项目：`the-omega-institute/trureturing`。

本节在现有 RH 理论卷中建立一个可逐项实现的等价判据图谱。第一版包含 **18 个判据族、64 个规格节点**：A001 是标准 RH，另外 63 个是经典判据或有用的派生表达。这些节点共享若干重大解析定理，不能解释成 63 项彼此独立的新发现，也不声称穷尽文献中一切重参数化的 RH 表述。后续新增判据进入相应判据族，并保留其原始对象、量词和证明来源。

数学目标是同时获得两种成果：对每个具体命题证明 `RiemannHypothesis ↔ P`；对不同领域之间的转换，进一步构造实际函数、矩阵、测度、残差和失败见证。后者使图谱能够承担新的定量研究。

本节给出文献中的数学定理、项目现状、若干完整纸面推导和待实现的接口。**本次增补没有新增 Lean 证明，也没有执行 Lean 编译或核验传递公理闭包。** 表中的“经典”指数学文献中的等价定理，“派生”指从注明的桥梁得到的数学表达；两者都不自动表示对应 Lean 端点已经完成。

### 1. 当前 dev 与所有开放 PR 的接入位置

主要数学源读取固定在 dev `aee1eaff34f997e44f04147cee1010bb482c4c1b`。提交前再次捕获 dev `3a8854105ef7bc1a480c4473cdc50b16d6993146`，树为 `717a3fee18b949f40ce178b595cb7d109fb24981`；本卷 blob 仍为 `1e9316d22d780b370a70aa340009ab0a5604819d`，原文未变。下表的开放 PR head 已再次刷新；这些快照日期不表示执行了全库编译。下列路径均相对仓库根目录；固定版本可用 `https://github.com/the-omega-institute/trureturing/blob/<commit>/<path>` 读取。

#### 1.1 应复用的数学真源

| 现有真源 | 本次读到的数学内容 | 图谱中的使用方式 |
| --- | --- | --- |
| `D5/S3/Weil/ZeroData/UnconditionalCanonicalZeroData.lean` | 无外部解析参数的 `zetaZeroData`，实际非平凡零点的穷尽性、唯一索引、正解析重数、反射与共轭；blob `a5ef2be4da1c3a6cf361b911d447bacc22be622f` | 所有零点判据共用这一实际对象。旧文档中“尚无 ZeroData 实例”的说法不再适用。 |
| `D5/S3/Zeros/Endpoints/CanonicalLiLocalExpansion.lean` | 从 `xiReading` 导数定义的 Li 系数、全部阶数的 Taylor 系数恒等式、局部生成展开及第一系数正性；blob `0fb04eb79f87389016b51af25cdf6078d5616b7c` | 不另定义替代 Li 序列。局部展开与全单位圆盘展开分开登记。 |
| `D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion.lean` | 实际零点和与 pole-minus-prime-plus-Archimedean 表达的运输；签名仍有每个卷积平方的 Archimedean 收敛输入 | 固定 canonical ZeroData 后，继续从相应解析真源构造收敛证明。不要删除该输入而不提供证明。 |
| `D5/S3/Weil/TestFunctions/LiCurvatureCriterion.lean` | 有限 Toeplitz Gram 恒等式、几何多项式能量、二阶差分重建；blob `b509cde8c62c3ed60756cfc9264b98cf357102d2` | 主等价定理目前仍接收 Li 判据、RH 下 Fourier 表示和无限 Herglotz 表示。第 6 节给出更短的反向证明。 |
| `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.lean` | 实际复数半直线 L² 载体、分数部分向量、目标指示函数、有限 Gram 与伪逆距离公式；blob `0bec9ac0ed53094607b7e34a7555aac7a3ebd6c8` | 在真实算术函数上完成 Nyman–Beurling 解析桥，直接消费已有有限距离。 |
| `D5/S3/Observer/Hilbert/NymanBeurlingTargetQuotientCriterion.lean` | 闭包成员、商类为零、正交残差为零和有限距离趋零的 Hilbert 等价；blob `a9518c6af492f2cae3dd8d4df58eeb7920a71581` | 当前 RH 连接仍作为 `nymanBeurling` 参数传入；它是待补的解析边。 |
| `D5/S3/Zeros/Jensen/JensenPolynomialObstruction.lean` | Jensen 多项式定义与有限失败见证的逻辑；blob `cb40a8e7c32caa84b36e1d86730fc2d45e903157` | 当前两个 Jensen–Pólya 桥仍是参数，且 RH 参数可为任意命题。最终端点必须使用实际 ξ 系数与标准 RH。 |
| `D5/S3/Constants/NewtonHankelRealRootCriterion.lean` | 共轭稳定有限根族的实根性与 Newton–Hankel 半正定双向证明；blob `1b30a277e90ec2fdca2e10712bdc543c37acc195` | 复用其插值负方向；为实际 Jensen 多项式构造根枚举或 companion-trace 适配器。 |

本卷已有 #5065 的共同 Burnol packet、多轨道完整 Weil 负子空间、实际 Gram 负指数和有限观察形式到完整混合形式的极限。图谱承接这些成果。新的任务是显式的支撑增长、插值条件数和误差运输，不能把已经写出的共同余项构造重新列为完全空白。

当前 `JensenPolynomialObstruction.PolynomialHyperbolic` 的实际定义要求每个复根为实，因此零多项式不满足它。注释中“包含零多项式”应在后续源维护中修正。本节使用严格正的规范系数，保证需要的 Jensen 多项式非零；次数零的正常数另行处理。

#### 1.2 开放 PR 全量筛选及相关源读取

本次使用无作者过滤的开放 PR 集合，第一页容量 100，第二页返回空集，得到以下 **14 个开放 PR**。全部读取了元数据和正文，并对与图谱直接有关的选定真源作进一步读取；这不是对所有历史 PR、所有文件或所有证明的完整重编译。已经合入的其他作者成果通过当前 dev 接入。表中记录实际 head，避免把正文中的旧 head 当成当前版本。

| PR | 捕获的实际 head | 与本图谱的关系 |
| --- | --- | --- |
| [#5236](https://github.com/the-omega-institute/trureturing/pull/5236) | `f65251d3d85ad5fe7f1e254291e3e56bc3b0ec1a` | PrimeGaps186。正文保留实际积分义务；不能用有限算术检查代替解析定理，不作为 RH 等价边。 |
| [#5284](https://github.com/the-omega-institute/trureturing/pull/5284) | `9adf54557f6ce3aecac3ae09c567e38379e8ca00` | 黄金自动机的有限样本运输。没有加入 RH 数学依赖。 |
| [#5405](https://github.com/the-omega-institute/trureturing/pull/5405) | `aaee9b75616627192369518e786fde83c06e4dc0` | 黄金四次幂状态下界。有限前缀与全指标结论的区别适用于本图谱，具体定理不构成 RH 判据。 |
| [#5602](https://github.com/the-omega-institute/trureturing/pull/5602) | `7d01130cfc3ce2d7c3d0c4d99a44843ce70c636f` | 实际 Weil/prolate 模型、完整余项与尺度运输。读取最新 `WeilGroundModeShiftBarrier.lean`，blob `2ab192cdf8db9f892a69606367b3bb986f34b846`；支撑边界及完整形式必须保留。 |
| [#5895](https://github.com/the-omega-institute/trureturing/pull/5895) | `023e6d1eccb223a563939590d301085a220b38f2` | 偶不变子空间的全尾界与归一化读数。偶扇区阈值不能自动替换全空间阈值。 |
| [#5897](https://github.com/the-omega-institute/trureturing/pull/5897) | `b6653823add96ea81c6f3c8cec3dd3db47029cd6` | 方格 hard-core 零点自由区域；未把其图递归定理转称 RH 定理。 |
| [#6029](https://github.com/the-omega-institute/trureturing/pull/6029) | `7e1a8c9b33d28d778d80392da5bb06bdcc966f7f` | 实际相对 Gamma 对角线的正项级数、完整尾界和频率一致窗口修正；对角线正性不足以控制混合项。 |
| [#6033](https://github.com/the-omega-institute/trureturing/pull/6033) | `d54250a5bd1ae4764dc15d876926e8a28b2a2881` | 因果耦合与最优界。没有加入 RH 数学依赖。 |
| [#6038](https://github.com/the-omega-institute/trureturing/pull/6038) | `608ebf0929b708832c268e9a5954f58bfb36574a` | 临时 MUB 文本拼接分支，不登记为数学结果。 |
| [#6114](https://github.com/the-omega-institute/trureturing/pull/6114) | `a65f9130d7f17c3bd6dcf7e450d1d53588ab92d2` | Li 曲率到 Herglotz、负型、Schoenberg 和实际圆周概率半群；读取 `LiCurvatureSchoenbergSemigroup.lean`，blob `d616bc1fc8a8f6176883f942809900136f92d577`。 |
| [#6143](https://github.com/the-omega-institute/trureturing/pull/6143) | `7abe3cf91cbf071d025c4dedef773e69dfbc6602` | MUB 区间证书与覆盖。没有加入 RH 数学依赖。 |
| [#6219](https://github.com/the-omega-institute/trureturing/pull/6219) | `8e3982e87642ba3987239f2a4623e6d7ef4b8e55` | 规范 Li 圆盘等价与零点半径增长障碍；读取 `CanonicalLiDiskEquivalence.lean`，blob `251c989b6312a577d24e87950a267cdefcdaae3f`。 |
| [#6221](https://github.com/the-omega-institute/trureturing/pull/6221) | `b1e737aa90c6a3d0f08e39fe481092b68a0d128a` | Scribe 的真实声明标识输出；有助于定位证明，不充当数学前提。 |
| [#6254](https://github.com/the-omega-institute/trureturing/pull/6254) | `34a2c0fe82403b5028456d02b99f9b2d3b11e320` | 临时 prolate 理论拼接分支，不重复计为独立成果。 |

#6114、#6219 及相关新谱源保留其候选、未执行编译的状态。#6219 已经使用规范导数系数，通过解析方程 `F'=GF` 的延拓与零点阶数排除，给出全圆盘判据的候选双向证明。它没有借用一个作为参数传入的 Li 判据。这是应保留的实质性进展。

### 2. 共同对象与变换约定

#### 2.1 ξ、Ξ、实际零点与 Möbius 圆盘

采用经典归一化

\[
\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
\qquad \xi(0)=\xi(1)=\frac12,
\qquad \Xi(z)=\xi\!\left(\frac12+iz\right).
\]

在 Lean 中消费现有 `xiReading` 与其端点、整性、函数方程、共轭性质。记 \(\mathcal Z\) 为实际非平凡零点集合，\(m_\rho\) 为解析重数；枚举变化不改变带重数的规范和。

定义

\[
w_\rho=1-\rho^{-1},\qquad
D=\{z\in\mathbb C:|z|<1\},\qquad
F(z)=\xi((1-z)^{-1}),
\]

\[
G(z)=(1-z)^{-2}\frac{\xi'}{\xi}((1-z)^{-1}).
\]

\(G\) 的解析性是需要证明的性质，定义它时不能预先要求整个圆盘零点自由。Lean 对除法的全函数约定也不能把分母零点变成解析延拓证明。

直接代数给出

\[
|w_\rho|^2-1=\frac{1-2\Re\rho}{|\rho|^2},\qquad
w_{1-\rho}=w_\rho^{-1},\qquad
w_{\bar\rho}=\overline{w_\rho}.
\tag{E1}
\]

故临界线对应单位圆，右半临界带的零点对应圆盘内部。若使用 Suzuki 的谱坐标，本节固定 \(\gamma_\rho=i(\rho-\tfrac12)\)，即 \(\xi(\tfrac12-i\gamma_\rho)=0\)。它与惯用正虚部 ordinate 的符号差异必须通过现有坐标适配器处理。[L02, L03]

#### 2.2 规范 Li 系数、曲率及正定性的量词

\[
\lambda_0=0,\qquad
\lambda_n=\frac1{(n-1)!}
\left.\frac{d^n}{ds^n}\bigl(s^{n-1}\log\xi(s)\bigr)\right|_{s=1}
\quad(n\ge1).
\]

局部对数由 \(\xi(1)=1/2\) 选定，所得系数为实数。复用现有第一系数

\[
L=\lambda_1=1+\frac{\gamma_{\!E}}2-\log(2\sqrt\pi)>0.
\]

其中 \(\gamma_E\) 专指 Euler–Mascheroni 常数。定义规范实偶曲率

\[
c_0=1,\qquad
c_k=\frac{\lambda_{|k|+1}-2\lambda_{|k|}+\lambda_{|k|-1}}{2L}
\quad(k\ne0),\qquad \psi(k)=\lambda_{|k|}.
\]

\(T^{(n)}=(c_{j-k})_{0\le j,k<n}\)。仓库 `toeplitzMatrix c N` 的大小为 \(N+1\)，因此 \(n\ge1\) 时它对应参数 \(N=n-1\)。圆周 Fourier 约定沿用

\[
\widehat\sigma(k)=\int_{\mathbb T}z^{-k}\,d\sigma(z).
\]

正定函数 \(h\) 表示：任意有限索引组 \(x_i\) 和任意复系数 \(a_i\) 都满足
\(\sum_{i,j}\overline{a_i}a_jh(x_i-x_j)\ge0\)。条件负定的量词相同，但要求 \(\sum_i a_i=0\)，不等式反向。所有概率测度均为正测度且总质量为一。[L02–L04]

#### 2.3 Jensen 的正偶阶系数

定义

\[
a_n=\frac{n!}{(2n)!}\xi^{(2n)}\!\left(\frac12\right)>0,
\qquad
\xi\!\left(\frac12+z\right)=\sum_{n\ge0}\frac{a_n}{n!}z^{2n}.
\]

严格正性由实际 theta 积分的偶矩给出，应独立形式化。用级数定义整函数
\(\Psi(u)=\sum_{n\ge0}a_nu^n/n!\)，避免依赖平方根分支；有 \(\Psi(-z^2)=\Xi(z)\)。定义

\[
J_{d,m}(X)=\sum_{j=0}^d\binom dj a_{m+j}X^j.
\]

[L05] 的系数归一化为 \(\gamma_n=8a_n\)。这个共同正因子不改变多项式根，但必须先证明与本项目导数定义一致。不能直接拿 \(\Xi\) 的交错 Taylor 系数，或包含恒零奇阶项的序列，替代这里的 \(a_n\)。

#### 2.4 Nyman–Beurling 的两个真实载体

在 \(L^2(0,1)\) 中，令 \(B_0\) 为所有有限复线性组合

\[
\sum_{j=1}^r u_j\{\theta_j/x\},\qquad
0<\theta_j\le1,\qquad \sum_j u_j\theta_j=0.
\]

在 \(H=L^2((0,\infty),dx;\mathbb C)\) 中，定义

\[
\chi=\mathbf1_{(0,1)},\quad v_a(x)=\{1/(ax)\}\ (a\ge1),\quad
S_N=\operatorname{span}\{v_1,\ldots,v_N\},\quad d_N=\operatorname{dist}(\chi,S_N).
\]

\(G_N\) 和 \(b_N\) 分别是这些实际向量的 Gram 矩阵与目标内积列，\(G_N^\dagger\) 是 Moore–Penrose 伪逆。已有真源给出

\[
d_N^2=1-b_N^*G_N^\dagger b_N.
\tag{E2}
\]

Gram 矩阵的半正定性在这里无条件成立；RH 所要求的是完整逼近残差趋零。[L07]

#### 2.5 Weil 的完整形式与有限窗口算子

令 \(Q_W\) 为现有显式公式对应的完整 Weil 二次型，测试函数取复值 \(C_c^\infty(\mathbb R)\)。在与谱坐标匹配的 Fourier 约定下，它的零点侧为

\[
Q_W(f)=\Re\sum_{\rho\in\mathcal Z}m_\rho\,
\widehat f(\gamma_\rho)\overline{\widehat f(\overline{\gamma_\rho})}.
\]

测试函数的固定带衰减、零点计数与绝对可和性需来自真实解析真源。混合形式由同一对象极化；不能把交叉项改成逐零点的模平方。

在窗口 \((-a,a)\) 上，令

\[
\ell(a)=\inf_{0\ne f\in C_c^\infty(-a,a)}\frac{Q_W(f)}{\|f\|_2^2}.
\]

\(A_a\) 专指该实际下半有界形式的 Friedrichs 实现。使用谱判据前，必须构造闭形式、证明核心与算子对应，不能从任意自伴算子出发重新命名。仓库的偶测试函数版本、`Zeta23.EF.weilTest` 的非受限版本和 [L01] 的形式之间分别需要精确适配。记 \(E(g)\) 为现有 `poleTerm - primeTerm + archimedeanTerm` 在实际卷积平方上的实部。[L01, L03]

### 3. 64 个规格节点及其数学等价关系

标签：**R** 为标准根命题，**C** 为文献中的经典判据，**D** 为由本节指明桥梁得到的派生表达。每行都是未来具体端点的目标陈述；实现进度由第 1、10 节的真源与解析义务决定。

所有大 O 都在趋于无穷时使用，\(O_\varepsilon\) 明确表示
\(\forall\varepsilon>0\;\exists C_\varepsilon,X_\varepsilon\;\forall x\ge X_\varepsilon\)，常数允许依赖 \(\varepsilon\)。复数表达的非负性按实 Hermitian 二次型解释。

#### F01. 零点几何与圆盘（A001–A005）

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A001 | R | 每个实际非平凡零点 \(\rho\) 满足 \(\Re\rho=1/2\)，使用 Mathlib 的标准 `RiemannHypothesis`。 |
| A002 | D | \(\Xi\) 的每个复零点均为实数。 |
| A003 | D | \(\xi(s)\ne0\) 对全部 \(\Re s>1/2\) 成立。 |
| A004 | D | 对每个实际非平凡零点，\(\vert 1-1/\rho\vert =1\)。 |
| A005 | D | \(F(z)\ne0\) 对全部 \(z\in D\) 成立。 |

依赖：端点填值、真实零点对应、函数方程与 (E1)。A003 的反向使用反射；省略反射只能排除半边零点。

#### F02. Li 系数与解析半径（A006–A013）

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A006 | C | \(\lambda_n\ge0\) 对所有整数 \(n\ge1\)。 |
| A007 | D | \(\lambda_n>0\) 对所有整数 \(n\ge1\)。 |
| A008 | D | 实际 \(G\) 在整个 \(D\) 上解析。 |
| A009 | D | 对每个 \(z\in D\)，\(\sum_{n\ge0}\lambda_{n+1}z^n\) 收敛且和为实际 \(G(z)\)。 |
| A010 | D | 对每个 \(0\le r<1\)，\(\sum_{n\ge0}\vert \lambda_{n+1}\vert r^n<\infty\)。 |
| A011 | D | 对每个 \(0<R<1\)，存在 \(C_R\ge0\)，使所有 \(n\ge0\) 满足 \(\vert \lambda_{n+1}\vert R^n\le C_R\)。 |
| A012 | D | \(\limsup_{n\to\infty}\vert \lambda_{n+1}\vert ^{1/n}\le1\)，根指数从 \(n\ge1\) 起。 |
| A013 | D | 对全部 \(n\ge0\)，\(\vert \lambda_n\vert \le L n^2\)。 |

A006 用 Li 定理 [L02, L03]。A007 的严格性由 RH 下正零点贡献和无穷零点得到，\(n=0\) 不包含在严格式中。A008–A012 使用实际 Taylor 恒等式、Cauchy–Hadamard 与 `F'=GF` 的零点阶数论证；A013 的正向见第 6 节，反向通过 A010。#6219 已有其中若干候选端点，不应平行重写。

#### F03. 圆周测度、负型与概率演化（A014–A020）

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A014 | D | 规范 \(c\) 的所有 \(T^{(n)}\) 半正定，\(n\ge1\)。 |
| A015 | D | 存在圆周概率测度 \(\sigma\)，使 \(\widehat\sigma(k)=c_k\) 对所有 \(k\in\mathbb Z\)。 |
| A016 | D | 存在圆周概率测度 \(\sigma\)，使 \(\lambda_n=L\int\vert \sum_{j<n}z^j\vert ^2d\sigma\) 对所有 \(n\ge0\)。 |
| A017 | D | 实际 \(\psi(k)=\lambda_{\vert k\vert }\) 在 \(\mathbb Z\) 上条件负定。 |
| A018 | D | 对每个实数 \(t\ge0\)，\(k\mapsto e^{-t\psi(k)}\) 在 \(\mathbb Z\) 上正定。 |
| A019 | D | 存在弱连续圆周概率卷积半群 \((\rho_t)_{t\ge0}\)，\(\rho_0=\delta_1\)，且全部 Fourier 系数为 \(e^{-t\psi(k)}\)。 |
| A020 | D | 存在实 Hilbert 空间、\(\mathbb Z\) 的正交表示 \(U\) 和 cocycle \(b(n+m)=b(n)+U(n)b(m)\)，满足 \(\Vert b(n)\Vert ^2=\psi(n)\)。 |

这里同时需要 Herglotz、Schoenberg 与 cocycle 表示的实际构造。A016 到 A015 可先将测度与共轭推前平均，以获得实偶 Fourier 矩，再应用二阶差分唯一性。A020 不能削弱成任意有指定范数的向量族。#6114 已提供通用构造的候选源；真正的 RH 连接仍要识别规范算术曲率。[L02–L04；第 6 节]

#### F04. Weil 正性、矩阵与实际窗口谱（A021–A026）

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A021 | C | \(Q_W(f)\ge0\) 对每个复值 \(f\in C_c^\infty(\mathbb R)\)。 |
| A022 | D | 在现有偶 `WeilTestFunction` 载体上，固定 `zetaZeroData` 的每个完整卷积平方零点和的实部非负。 |
| A023 | D | 每个相同测试函数上的实际 \(E(g)\ge0\)，收敛项与显式公式齐备。 |
| A024 | D | 任意有限实际测试函数组的完整混合 Weil Gram 矩阵半正定。 |
| A025 | D | 对每个 \(a>0\)，\(\ell(a)\ge0\)。 |
| A026 | D | 对每个 \(a>0\)，实际 \(A_a\) 的谱包含于 \([0,\infty)\)。 |

A021–A024 需要两个测试函数载体的完整适配和现有 separator。A025 使用所有支撑窗口的穷尽；A026 使用闭形式与谱定理。有限截断矩阵的正性只有在全尾控制和核心证明完成后才能进入这些端点。[L01, L03]

#### F05. 整函数、Jensen 与 Newton–Hankel（A027–A032）

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A027 | C | \(\Xi\) 属于 Laguerre–Pólya 类。 |
| A028 | D | 存在非零、仅有实根的实多项式序列，在每个复紧集上一致收敛到 \(\Xi\)。 |
| A029 | C | 每个 \(J_{d,0}\) 仅有实根，\(d\ge0\)。 |
| A030 | C | 每个 \(J_{d,m}\) 仅有实根，\(d,m\ge0\)。 |
| A031 | D | 对每个 \(d\ge1,m\ge0\)，实际反转多项式 \(x^dJ_{d,m}(-1/x)\) 的带重数根所构成的 Newton–Hankel 矩阵半正定。 |
| A032 | D | A031 中每一个有限矩阵的所有主子式均非负。 |

这里使用 \(\Psi(-z^2)=\Xi(z)\)、正系数和 Jensen–Pólya 定理，再消费现有有限根定理。[L05, L06] 的“固定次数、充分大 shift”结果只覆盖量词的一部分，不能取代 A030。

#### F06. Nyman–Beurling 与最佳逼近（A033–A040）

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A033 | C | \(B_0\) 在 \(L^2(0,1)\) 中稠密。 |
| A034 | C | 常数函数 \(1\) 属于 \(\overline{B_0}\)。 |
| A035 | C | \(\chi\in\overline{\operatorname{span}\{v_a:a\in\mathbb R,a\ge1\}}\subset H\)。 |
| A036 | C | \(\chi\in\overline{\operatorname{span}\{v_n:n\in\mathbb N,n\ge1\}}\subset H\)。 |
| A037 | D | \(d_N\to0\)。 |
| A038 | D | \(b_N^*G_N^\dagger b_N\to1\)，按其已证明的实值理解。 |
| A039 | D | 每个 \(h\in H\) 若与全部整数 \(v_n\) 正交，则与 \(\chi\) 正交。 |
| A040 | D | \(\chi\) 在 \(H/\overline{\operatorname{span}\{v_n:n\ge1\}}\) 中的商类为零。 |

A036 的整数限制是 Báez-Duarte 的强化定理 [L07]，不能仅靠 Hilbert 抽象几何推出。A037–A040 的几何大部分已有真源。第 7 节给出实际离线零点在两个原始载体中的连续分离泛函。

#### F07. Möbius 抵消与素数分布误差（A041–A044）

记 \(M(x)=\sum_{n\le x}\mu(n)\)，\(\psi_{\rm vM}(x)=\sum_{n\le x}\Lambda(n)\)，\(\vartheta(x)=\sum_{p\le x}\log p\)，\(\operatorname{li}_2(x)=\int_2^xdt/\log t\)，\(x\ge2\)。

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A041 | C | 对每个 \(\varepsilon>0\)，\(M(x)=O_\varepsilon(x^{1/2+\varepsilon})\)。 |
| A042 | C | \(\psi_{\rm vM}(x)-x=O(x^{1/2}\log^2x)\)。 |
| A043 | D | \(\vartheta(x)-x=O(x^{1/2}\log^2x)\)。 |
| A044 | C | \(\pi(x)-\operatorname{li}_2(x)=O(x^{1/2}\log x)\)。 |

依赖实际 Dirichlet 级数、Perron/显式公式、部分求和及 prime-power 余项。[L08]。无条件已有 Mertens 或 Gronwall 极限不能取代这里的 RH 级误差。

#### F08. Robin、Lagarias 与 Nicolas 的整数不等式（A045–A047）

记 \(\sigma(n)=\sum_{d\mid n}d\)，\(H_n=\sum_{j=1}^n1/j\)，\(P_k\) 为前 \(k\) 个素数的乘积，\(\varphi\) 为 Euler 函数。

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A045 | C | 对每个整数 \(n\ge5041\)，\(\sigma(n)<e^{\gamma_E}n\log\log n\)。 |
| A046 | C | 对每个整数 \(n\ge1\)，\(\sigma(n)\le H_n+e^{H_n}\log H_n\)。 |
| A047 | C | 对每个整数 \(k\ge1\)，\(P_k/\varphi(P_k)>e^{\gamma_E}\log\log P_k\)。 |

A045 的阈值与严格号、A046 的 \(n=1\) 等号以及 A047 的 primorial 输入必须保留。[L09, L10]。项目已有 Robin 单元证书、素指数重排和 Gronwall 上下包络可复用；它们不自动提供以上全称等价定理。

#### F09. Riesz 与离散 Báez-Duarte 变换（A048–A049）

定义

\[
R(x)=x\sum_{j\ge0}\frac{(-1)^jx^j}{j!\zeta(2j+2)},\qquad
b_k=\sum_{j=0}^k(-1)^j\binom kj\frac1{\zeta(2j+2)}.
\]

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A048 | C | 对每个 \(\varepsilon>0\)，\(R(x)=O_\varepsilon(x^{1/4+\varepsilon})\)，\(x\to+\infty\)。 |
| A049 | C | 对每个 \(\varepsilon>0\)，\(b_k=O_\varepsilon(k^{-3/4+\varepsilon})\)，整数 \(k\to\infty\)。 |

这里 \(b_k\) 与 Li 曲率 \(c_k\) 是不同对象。不得把 \(\varepsilon=0\) 的更强界当作等价式。[L11]。第 8 节给出精确变换与误差义务。

#### F10. 导数零点（A050）

**A050，C，Speiser：** \(\zeta'(s)\) 在 \(0<\Re s<1/2\) 内没有零点。对象是实际解析导数；开带边界、平凡导数零点和极点需分别处理。[L12]

#### F11. Balazard–Saias–Yor 对数积分（A051）

**A051，C：**

\[
I_{\rm BSY}=\int_{\mathbb R}\frac{\log|\zeta(1/2+it)|}{1/4+t^2}\,dt=0.
\]

必须证明对数奇点与无穷尾的积分意义；孤立零点处的取值只能按已证明的几乎处处等价处理。[L13]。截断积分趋零是该积分结论的一个实现方式，有限截断的小值不构成等价定理。

#### F12. Farey 分数的偏差（A052–A053）

Farey 阶数为整数 \(N\)，列出分母不超过 \(N\) 的既约分数 \(0<r_1<\cdots<r_{m_N}=1\)，其中 \(m_N=\sum_{q=1}^N\varphi(q)\)。令 \(\delta_j=r_j-j/m_N\)。

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A052 | C | 对每个 \(\varepsilon>0\)，\(\sum_{j=1}^{m_N}\delta_j^2=O_\varepsilon(N^{-1+\varepsilon})\)。 |
| A053 | C | 对每个 \(\varepsilon>0\)，\(\sum_{j=1}^{m_N}\vert \delta_j\vert =O_\varepsilon(N^{1/2+\varepsilon})\)。 |

规模变量为分母上界 \(N\)，不是项数 \(m_N\)。[L14] 的引言准确重述 Franel–Landau 判据；其新的同余类、k-free 分母问题含有更强 L-function/GRH 范围，不能自动纳入普通 RH。

#### F13. Redheffer 算术矩阵（A054）

令 \(A_N\) 的行列为 \(1,\ldots,N\)，当 \(j=1\) 或 \(i\mid j\) 时元素为一，其余为零。

**A054，C：** 对每个 \(\varepsilon>0\)，\(\vert \det A_N\vert =O_\varepsilon(N^{1/2+\varepsilon})\)。精确桥为 \(\det A_N=M(N)\)，见第 8 节。[L15, L16]

#### F14. de Bruijn–Newman 热形变（A055–A056）

定义

\[
\Phi(u)=\sum_{n\ge1}(2\pi^2n^4e^{9u}-3\pi n^2e^{5u})e^{-\pi n^2e^{4u}},
\qquad
H_t(z)=\int_0^\infty e^{tu^2}\Phi(u)\cos(zu)\,du.
\]

该约定满足 \(H_0(z)=\xi(1/2+iz/2)/8\)。令 \(\Lambda_{\rm dBN}\) 为“\(H_t\) 全部零点实当且仅当 \(t\ge\Lambda_{\rm dBN}\)”的实阈值。

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A055 | C | \(\Lambda_{\rm dBN}\le0\)。 |
| A056 | D | \(\Lambda_{\rm dBN}=0\)。 |

A056 还消费 Rodgers–Tao 的无条件 \(\Lambda_{\rm dBN}\ge0\) 深定理。[L17]。阈值存在性、热积分与 ξ 的尺度恒等式和这条下界都要独立形式化。

#### F15. 全正函数与双边 Laplace 变换（A057–A058）

\(PF_\infty(k)\) 表示 \(k\) 是非零可积实函数，且对所有严格递增实数列 \(x_1<\cdots<x_r\)、\(y_1<\cdots<y_r\)，所有阶数 \(r\ge1\) 都有 \(\det[k(x_i-y_j)]\ge0\)。

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A057 | C | 明确函数 \(K(x)=(2\pi)^{-1}\int_{\mathbb R}e^{-ix\tau}/\xi(1/2+\tau)\,d\tau\) 满足 \(PF_\infty(K)\)。 |
| A058 | D | 存在 \(PF_\infty(k)\) 和 \(a>0\)，使 \(\int_{\mathbb R}k(x)e^{-sx}dx=1/\Xi(s)\) 在整个 \(\vert \Re s\vert <a\) 内绝对收敛并成立。 |

这里 A057 分母使用 **实轴方向的 \(\xi(1/2+\tau)\)**。不能换成经过临界线零点的 \(\Xi(\tau)\)。全正性要求独立的两组有序节点，强于只检验相同节点的 Gram 主子式。A058 是 [L06] 的 Schoenberg 表示的局部条带版本；解析恒等与唯一性将它接回相同的 Ξ。

#### F16. 真实 zeta screw function 与实线概率（A059–A062）

为使对象独立于 RH，先用 [L04] 的原始算术公式定义 \(g_\zeta\)。对 \(t\ge0\)，

\[
\begin{aligned}
g_\zeta(t)={}&-4(e^{t/2}+e^{-t/2}-2)
+\sum_{n\le e^t}\frac{\Lambda(n)}{\sqrt n}(t-\log n)\\
&-\frac t2\left(\frac{\Gamma'}\Gamma(1/4)-\log\pi\right)\\
&+\frac14\left[e^{-t/2}\operatorname{LerchPhi}(e^{-2t},2,1/4)
-\operatorname{LerchPhi}(1,2,1/4)\right].
\end{aligned}
\]

向负数作偶延拓，\(g_\zeta(0)=0\)。完整无条件显式公式给出

\[
g_\zeta(t)=\sum_{\rho\in\mathcal Z}m_\rho
\frac{e^{-i\gamma_\rho t}-1}{\gamma_\rho^2}.
\tag{E3}
\]

须先证明实际算术公式、实值连续性及紧集上一致绝对收敛，不能在定义中假定 \(\gamma_\rho\) 都为实数。

| ID | 类别 | 精确目标 |
| --- | --- | --- |
| A059 | C | \(K_g(t,u)=g_\zeta(t-u)-g_\zeta(t)-g_\zeta(-u)+g_\zeta(0)\) 的每个有限复 Gram 矩阵半正定。 |
| A060 | C | \(e^{g_\zeta}\) 是某个实线无穷可分概率分布的特征函数。 |
| A061 | D | 对每个 \(v\ge0\)，\(t\mapsto e^{v g_\zeta(t)}\) 在实加法群上正定。 |
| A062 | D | 存在弱连续实线概率卷积半群，其每个时刻 \(v\) 的特征函数恰为 \(e^{v g_\zeta(t)}\)。 |

这是 [L01, L04] 的实际 zeta 概率方向。它与 A019 的圆周概率半群具有相似结构，但载体、频率及 Lévy 测度不同，不能直接识别为同一个半群。

#### F17. 模型空间中的实际范数公式（A063）

取 \(s=1/2-it\)，用 [L03] Proposition 2.1 的实际零点级数定义

\[
G_n^{\rm Suz}(t)=\frac{\xi(s)}{\xi(s)+\xi'(s)}
\sum_{\rho\in\mathcal Z}m_\rho\frac{1-w_\rho^n}{s-\rho},\qquad n\ge1,
\]

并在可去奇点处取解析延拓值。该定义的级数收敛、连续性和实线 L² 性质，以及它与 [L03] 原始对数导数公式的相等，都是需要构造的无条件前置。

**A063，C：** 对每个 \(n\ge1\)，
\(\lambda_n=(2\pi)^{-1}\Vert G_n^{\rm Suz}\Vert _{L^2(\mathbb R)}^2\)。

必须使用这个固定的原始函数族。任意选择范数为 \(\sqrt{2\pi\lambda_n}\) 的向量，既没有定义负系数情形，也没有得到模型空间判据。

#### F18. Volchkov 的嵌套对数积分（A064）

**A064，C：**

\[
\int_0^\infty\frac{1-12t^2}{(1+4t^2)^3}
\left(\int_{1/2}^\infty\log|\zeta(\sigma+it)|\,d\sigma\right)dt
=\frac{\pi(3-\gamma_E)}{32}.
\]

采用 [L18] Eq. (2.1) 所列 Volchkov 表达，避免未规定路径的 `arg zeta`。对极点、零点的对数奇性和两层无穷积分分别证明合法性，不能只用截断数值代替等式。

### 4. 跨领域证明的共同骨架

在标准 RH 根之外，最重要的几条可复用解析链为

```text
actual xi / actual ZeroData / functional equation
  |-- Mobius disk -- canonical Li generator -- coefficient growth
  |                         |-- Li curvature -- circle moments
  |                         |                    |-- negative type / cocycle
  |                         |                    `-- probability semigroup
  |-- explicit formula -- full Weil form -- finite windows / actual spectrum
  |-- even xi coefficients -- Jensen / Laguerre-Polya -- Newton-Hankel
  |-- Mellin transform -- Nyman-Beurling -- original Gram distances
  |-- reciprocal zeta / Mobius sums -- Riesz / discrete transform / Redheffer
  |-- prime error terms -- divisor extrema / Farey discrepancy
  |-- logarithmic integrals -- BSY / Volchkov
  `-- heat deformation / total positivity / actual zeta probability
```

箭头代表要构造的数学映射及其定理，不保证所有箭头已经在仓库完成。已知两条 `RH ↔ P` 可以导出 `P ↔ Q`，但这类命题传递性不会自动产生误差界、矩阵大小、有效截断、测度对应或恢复算法。

同理，RH 等价命题之间的逻辑等价不表示项目中两个观察映射的不可区分核相同。后者必须固定同一原始状态空间并证明实际读出之间的恢复关系。不能凭 64 个闭命题构造新的信息逃逸分数或宣称全体读出有相同内核。

### 5. 当前文献对谱主线的具体修订

Suzuki 的 *Weil's quadratic form via the screw function* 已从 2026-06-08 的 v1 修订为 **2026-08-17 的 v2**。[L01] Theorem 1.1 提供实际 Friedrichs 实现，Theorem 1.3 研究最低谱值的连续性，Theorem 1.4 的正性、单性、偶性及渐近适用于充分小的窗口参数。其最终无穷窗口谱解释仍包含明确提出的猜想。

因此，A025–A026 的全部 \(a>0\) 量词不能由小窗口定理替代。对 #5602、#5895、#6029 的具体接入应保持同一个算术形式、同一个实际模型和完整混合余项。#5602 最新 shift barrier 消费的平移测试还要求物理支撑余量；两次平移使用 \(2t\) 余量，尖锐边界裁剪不自动满足这一条件。

[L19] 的 zeta spectral triples 与 [L20] 的 2026 综述为该路线提供背景。由明确模型得到的函数极限、由真实最低模态得到同一极限、以及将极限连到 RH 是不同定理。当前理论图谱没有将这些尚待完成的比较猜想计作已证明的 RH 等价判据。

Farey 工作 [L14] 已于 2026-09-02 修订到 v3；它与 2025 的 Redheffer 工作 [L16] 提供另外两条现代接口：前者要求区别普通 RH 和带同余类的 GRH，后者要求区别行列式中的 Möbius 抵消与最大奇异向量行为。跨领域联系保留被研究的实际量。

### 6. 完整纸面推导一：有限 Li–Toeplitz 重建

#### 6.1 双重望远镜求和

先不使用 RH。设实序列 \(u_0=0,u_1=L\ge0\)，Hermitian 序列 \(c\) 满足 \(c_0=1\)，并有

\[
u_{n+1}-2u_n+u_{n-1}=2L\Re c_n\quad(n\ge1).
\]

写 \(d_n=u_n-u_{n-1}\)，则 \(d_1=L\)，\(d_{n+1}-d_n=2L\Re c_n\)。先对差分求和，再对 \(d_n\) 求和，得到

\[
u_n=L\left[n+2\sum_{k=1}^{n-1}(n-k)\Re c_k\right].
\tag{E4}
\]

令 \(e_n=(1,\ldots,1)^T\in\mathbb C^n\)。按 Toeplitz 对角线逐条计数，距离 \(k\) 的两条对角线各含 \(n-k\) 项，因而

\[
e_n^*T^{(n)}e_n=nc_0+\sum_{k=1}^{n-1}(n-k)(c_k+c_{-k}).
\]

与 (E4) 比较可得精确恒等式

\[
\boxed{u_n=L\Re(e_n^*T^{(n)}e_n).}
\tag{E5}
\]

因此所有 Toeplitz 矩阵半正定立即推出所有 \(u_n\ge0\)，无需先构造一个无限 Herglotz 测度。删除原反向证明的 Herglotz 前提时，必须显式保留 \(c_0=1\)；旧概率表示曾隐含提供它。

#### 6.2 定量负方向与二次增长

若 \(L>0,u_n<0\)，由于 \(\Vert e_n\Vert ^2=n\)，Rayleigh 商给出

\[
\lambda_{\min}(T^{(n)})\le\frac{u_n}{nL}<0.
\tag{E6}
\]

这是指定矩阵大小和指定见证向量的运输。另一方面，所有两点主压缩半正定给出 \(\vert c_k\vert \le c_0=1\)。由 (E4)

\[
|u_n|\le L\left[n+2\sum_{k=1}^{n-1}(n-k)\right]=Ln^2.
\tag{E7}
\]

对规范 Li 系数，这给出

\[
\text{A014}\Longrightarrow\text{A013}\Longrightarrow\text{A010}
\Longrightarrow\text{A005}\Longrightarrow\mathrm{RH}.
\]

最后两步应复用 #6219 的实际解析延拓候选源，并完成所需编译检查。该反向路线不需要把 Li 判据本身作为参数传入。

#### 6.3 正向使用实际零点的概率测度

在 RH 下，对每个上半平面实际零点 \(\rho\)，写 \(w_\rho=e^{i\theta_\rho}\)。规范零点求和给出

\[
\lambda_n=2\sum_{\Im\rho>0}m_\rho(1-\cos n\theta_\rho).
\]

在 \(w_\rho\) 和 \(\bar w_\rho\) 各放置质量
\(m_\rho(1-\cos\theta_\rho)/L\)。总质量等于一；权重的完整可和性来自实际零点的平方倒数可和性。有限几何级数恒等式给出

\[
\lambda_n=L\int_{\mathbb T}\left|\sum_{j=0}^{n-1}z^j\right|^2d\sigma(z).
\tag{E8}
\]

由此得到规范曲率的圆周表示和 A014。解析重点是将导数定义的 \(\lambda_n\) 与带重数的实际零点和相等，并证明所有交换与尾界；任意抽象 Li-type 序列不够。

#6114 的几何 cocycle、Schoenberg 和概率半群可以在这个实际输入上接通。圆周恒等点处的原子与二次增长项应完整保留，直到针对规范测度给出排除证明。

### 7. 完整纸面推导二：同一离线零点的三种定量见证

设 \(\rho\) 是实际非平凡零点，\(\beta=\Re\rho>1/2\)，并记 \(r=\vert w_\rho\vert \in(0,1)\)。这些推导以存在这样的零点为条件，不断言其存在。

#### 7.1 原始 Nyman Mellin 恒等式

对 \(0<\theta\le1\)、\(0<\Re s<1\)，

\[
\int_0^1\{\theta/x\}x^{s-1}dx
=\frac\theta{s-1}-\frac{\theta^s\zeta(s)}s.
\tag{E9}
\]

可先在 \(\Re s>1\) 将 floor 写为指示函数和并逐项积分，再用左侧在 \(\Re s>0\) 的解析性作延拓，处理 \(s=1\) 的可去抵消。复幂使用正实数的实对数。

在 \(L^2(0,1)\) 上，\(\mathcal L_\rho f=\int_0^1f(x)x^{\rho-1}dx\) 的范数为 \((2\beta-1)^{-1/2}\)。由 (E9) 及 \(B_0\) 的约束，\(\mathcal L_\rho\) 消去整个 \(B_0\)，而 \(\mathcal L_\rho1=1/\rho\)。故

\[
\operatorname{dist}(1,\overline{B_0})\ge\frac{\sqrt{2\beta-1}}{|\rho|}.
\tag{E10}
\]

#### 7.2 直接作用于项目半直线载体的分离泛函

为避免把 (E10) 的范数常数未经证明转移到另一个载体，在原始 \(H=L^2(0,\infty)\) 上直接构造

\[
\mathcal J_\rho f=
\int_0^1f(x)x^{\rho-1}dx
-\frac1{\rho-1}\int_1^\infty\frac{f(x)}x\,dx.
\]

两项的 Riesz 向量支撑不交，故

\[
\|\mathcal J_\rho\|^2=\frac1{2\beta-1}+\frac1{|\rho-1|^2}.
\]

由于 \(v_a(x)=1/(ax)\) 在 \(x>1\) 上成立，(E9) 在 \(s=\rho\) 给出 \(\mathcal J_\rho v_a=0\) 对所有实 \(a\ge1\)；同时 \(\mathcal J_\rho\chi=1/\rho\)。因此对项目中的每个有限整数空间都有

\[
\begin{aligned}
d_N^2&\ge\frac{1}{|\rho|^2\left((2\beta-1)^{-1}+|\rho-1|^{-2}\right)}\\
&=\frac{(2\beta-1)|\rho-1|^2}{|\rho|^4}
=\boxed{r^2(1-r^2)}>0.
\end{aligned}
\tag{E11}
\]

同一界也适用于完整闭包的距离。这是实际半直线函数的连续分离证明，不依赖 Gram 矩阵可逆或有限数值条件数。它应复用仓库的实际 `target`、`sourceVector` 和 `distance` 定义。

#### 7.3 BSY 的同一半径读数

[L13] 的无条件恒等式为

\[
I_{\rm BSY}=2\pi\sum_{\Re\alpha>1/2}m_\alpha
\log\left|\frac\alpha{1-\alpha}\right|.
\]

右侧每项为正，因此给定零点 \(\rho\) 产生

\[
\boxed{I_{\rm BSY}\ge-2\pi m_\rho\log r>0.}
\tag{E12}
\]

这里按全部实际零点带重数计数，不再额外重复乘一个共轭对因子。

#### 7.4 Li 生成函数的同一半径障碍

该零点对应 \(F(w_\rho)=0\)。一旦在半径大于 \(r\) 的圆盘内有实际解析函数 \(G\) 满足 \(F'=GF\)，零点阶数比较就产生矛盾。#6219 的候选 `CanonicalLiRadiusObstruction` 将其量化为：对 \(r<R\le1\)，

\[
\forall N\;\forall C\;\exists n\ge N,
\qquad |\lambda_{n+1}|R^n>C.
\tag{E13}
\]

(E11)–(E13) 使用同一个实际 \(w_\rho\)：它在逼近论中给出正距离，在对数积分中给出正缺陷，在系数空间中排除每一个指定指数包络。由此可以研究转换中的显式常数，而非只依赖命题传递性。

这不提供最早失败指标，也不证明每个充分大的 Li 系数均超过包络。有限 Weil 负方向另由现有 separator 和共同 Burnol packet 构造；将其支撑半径与这里的 \(r\) 定量比较仍是新的研究任务。

### 8. 两条独立的算术变换桥

#### 8.1 Riesz 与二项式离散化

记 \(a_j^\zeta=1/\zeta(2j+2)\)，它与 Jensen 的 \(a_j\) 无关。对 \(x>0\)，完整指数生成关系为

\[
\frac{R(x)}x=e^{-x}\sum_{k\ge0}b_k\frac{x^k}{k!}.
\tag{E14}
\]

证明从有限二项式变换展开，交换绝对收敛级数，再求 \(\sum_{k\ge j}\binom kjx^k/k!=x^je^x/j!\)。实际 Möbius 展开进一步给出

\[
R(x)=x\sum_{n\ge1}\frac{\mu(n)}{n^2}e^{-x/n^2},\qquad
b_k=\sum_{n\ge1}\frac{\mu(n)}{n^2}(1-n^{-2})^k.
\tag{E15}
\]

[L11] 的完整误差比较 \(R(k)/k-b_k=O(k^{-3/2})\) 连同整数之间的控制，将两种增长界接通。形式化必须保留全部 \(n\) 尾部，证明从整数到实变量的运输；只验证有限项的二项式恒等式没有完成 A048–A049。

#### 8.2 Redheffer 行列式精确等于 Möbius 部分和

令 \(D_{ij}=1_{i\mid j}\)，\(1\le i,j\le N\)。它是单位上三角矩阵，且

\[
(D^{-1})_{ij}=\begin{cases}\mu(j/i),&i\mid j,\\0,&\text{其他}.\end{cases}
\]

令 \(u=(0,1,\ldots,1)^T\)，则 \(A_N=D+u e_1^T\)。矩阵行列式引理给出

\[
\boxed{\det A_N=\det D\,(1+e_1^TD^{-1}u)=\sum_{n=1}^N\mu(n)=M(N).}
\tag{E16}
\]

所需核心是除数卷积 \(\mu*1=\varepsilon\)，可以消费已有算术函数库。A054 的有限对象与 A041 的完整渐近完全一致。[L15, L16] 的奇异值研究不替代这一行列式身份。

### 9. Jensen、Weil 与正性的必要区分

对有限共轭稳定根族 \(z_1,\ldots,z_d\)，现有 Newton–Hankel 恒等式是

\[
a^THa=\frac1d\Re\sum_{j=1}^d q_a(z_j)^2.
\]

发现非实共轭根时，实系数插值可令 \(q_a(z)=i,q_a(\bar z)=-i\)，其余不同根取零，得到负方向。这个机制消费 **平方**；替换成 \(\vert q_a(z_j)\vert ^2\) 会使表达自动非负，从而失去检测能力。

Weil 的离线轨道同样通过交叉配对产生不定性，但把有限插值推广到完整零点和，还要控制全部其余零点。项目已有单轨道与多轨道 Burnol 机制负责这一分析层。Jensen 的有限矩阵结果也不能越过实际 ξ 系数与整函数极限。

[L06] 同时指出，某些倒数函数 Taylor 系数构成的矩 Hankel 正性只是 Laguerre–Pólya 的必要条件。它与本项目“给定有限多项式全部根的 Newton–Hankel 判据”是不同命题。不得凭 Hankel 同名把必要条件升级成 RH 等价。

另外，半正定判据要求所有主子式；只有全部顺序领先主子式的弱非负通常不足。严格正定的 Sylvester 判据、半正定判据和全正核的任意两组节点行列式，应各用其实际定理。

### 10. 按共享解析义务推进形式化

以下是实现单元，不是新建 64 个相互独立模块。最终每个公开端点必须以现有标准 `RiemannHypothesis` 和本节实际对象表达，且不接收一个同等困难的 `RH ↔ P` 作为未证明参数。通用引理仍可以参数化，只需与规范算术端点分开。

| 阶段 | 主要工作及复用点 | 完成时应得到的具体成果 |
| --- | --- | --- |
| P0：规范对象 | 复用 canonical ZeroData、xiReading、Li 导数；固定坐标、重数、Fourier 号和 Jensen 偶阶归一化 | A001–A005 的真实几何连接；每个定义与文献对象的对应定理。 |
| P1：Li 与概率 | 在现有曲率真源增加 (E4)–(E7)；接入 #6219 的圆盘分析和 #6114 的概率构造；证明实际导数系数等于规范零点和 | A006–A020 的共享解析闭环；显式有限负方向和指数包络障碍。 |
| P2：整函数与有限矩阵 | 证明实际偶阶系数严格正、Ψ 与 Ξ 的关系、Jensen–Pólya 定理；复用 NewtonHankelRealRootCriterion | A027–A032；实际多项式到矩阵与根失败见证的双向运输。 |
| P3：Nyman 解析桥 | 证明 (E9)、两个连续分离泛函、Beurling 稠密性与整数强化；复用实际 Gram、伪逆和闭包模块 | A033–A040，并得到 (E11) 的原始载体距离下界。 |
| P4：算术与误差 | 复用 Möbius、除数卷积、Mertens 和 prime-power 所有者；补 Perron、部分求和、极值整数及 Farey 运输；证明 (E14)–(E16) | A041–A049、A052–A054。每个 epsilon、阈值和尾部都有实际证明。 |
| P5：完整谱与函数空间 | 接合实际 Weil 载体及 Friedrichs 实现；证明全窗口/核心/谱对应；补 Speiser、BSY、Volchkov、Schoenberg PF、实际 zeta 概率、模型空间与热形变 | A021–A026、A050–A051、A055–A064；较重的共享分析定理可以再分解为有独立用途的子项目。 |

P1 与 P3 的有限恒等式和显式分离泛函可优先推进。P2 具有可直接消费的现有有限根定理。Rodgers–Tao 下界、Nyman 整数强化以及完整显式公式等大型前置按各自原定理实现，不以接口包装计作已解决。

每个最终端点的必要检查包括：两个方向均有证明；原函数和原序列没有被替代；实/复域与全部测试向量正确；重数与截断顺序正确；除法、对数和逆矩阵的定义域正确；无限和及积分换序合法；量词为全阶数、全尺度或全 epsilon；真源与 Scribe 指向同一声明。核验执行后再记录相应版本的编译与公理闭包，文档中的纸面推导不充当机器回执。

### 11. 可以进一步产生研究价值的定量问题

本图谱把“证明等价”与“利用等价”接在一起。近期可以提出以下直接面对原始对象的问题。

第一，给定实际离线零点位置、重数及一个有效邻域，将 (E11)、(E12) 与已有 Burnol 负测试统一为可检查的证书，显式控制测试支撑、次数、矩阵维度和尾误差。现有 (E13) 只保证每条指数包络在任意尾部失败；有效首次失败指标需要新的估计。

第二，将 Jensen 根分离裕量转成 Newton–Hankel 的负特征值裕量，再控制 ξ 系数的有限精度误差。插值条件数、根碰撞与矩阵大小会影响稳定性，不能把多项式根保持定理视为均匀鲁棒性结论。

第三，在 Nyman 原始 Gram 系统中同时控制计算误差和最佳逼近误差。伪逆公式容许奇异矩阵，却不会消除接近奇异时的数值敏感性。若使用正则化，应证明实际残差和正则化残差之间的定量关系。

第四，将 #5602/#5895/#6029 的完整算术余项与 [L01] 的实际形式域接合，研究随窗口无界增长的一致估计。固定窗口和固定扇区的进步保留其价值，但对 A025–A026 的全称命题还需要真正的尺度控制。

后续可扩展到广义 Li/Bombieri–Lagarias 参数族、完整广义 Laguerre 不等式塔、乘子序列、变差递减以及更细的算术极值判据。新条目必须先固定原定理、范围和量词。单个 Turán 不等式、弱 Mertens 加零点单性、某个有限样本成功、或尚未证明的 Hilbert–Pólya 模型，都不能直接加进已知 RH 等价清单。

### 12. 原始文献与精确定位

以下文献按本节用途引用。2026 新稿使用实际版本记录；引文支持指定数学陈述，不表示本次独立重证了每篇全文。经典结果的完整移植仍按第 10 节推进。

- **[L01]** Masatoshi Suzuki, *Weil's quadratic form via the screw function*, [arXiv:2606.09096v2](https://arxiv.org/abs/2606.09096v2), revised 2026-08-17. Theorems 1.1, 1.3, 1.4，形式核心与最终谱极限猜想。相关 PR 中 v1 引用应在实际采用新定理时更新。
- **[L02]** Jeffrey C. Lagarias, *Li Coefficients for Automorphic L-Functions*, [arXiv:math/0404394](https://arxiv.org/abs/math/0404394), Annales de l'Institut Fourier 57 (2007), 1689–1740. Li 导数、零点表达与增长判据的经典来源。
- **[L03]** Masatoshi Suzuki, *Li coefficients as norms of functions in a model space*, [arXiv:2301.05779v2](https://arxiv.org/html/2301.05779v2), 2023. Theorem 1.1；Propositions 2.1–2.2；Li–Weil 特殊测试函数恒等式。该特殊测试函数不属于原始光滑紧支撑类，使用时另证正则化和尾部运输。
- **[L04]** Takashi Nakamura and Masatoshi Suzuki, *On infinitely divisible distributions related to the Riemann hypothesis*, [arXiv:2306.08317v1](https://arxiv.org/html/2306.08317v1), 2023. Theorem 1.1、算术 screw function、实际零点展开及实线无穷可分分布。
- **[L05]** Michael Griffin, Ken Ono, Larry Rolen and Don Zagier, *Jensen polynomials for the Riemann zeta function and other sequences*, [arXiv:1902.07321v2](https://arxiv.org/html/1902.07321v2), 2019. 系数归一化、Jensen 实根塔及固定次数的大 shift 定理。
- **[L06]** Karlheinz Gröchenig, *Schoenberg's Theory of Totally Positive Functions and the Riemann Zeta Function*, [arXiv:2007.12889v1](https://arxiv.org/html/2007.12889v1), 2020. Theorems 1, 3, 4, 8；倒数矩 Hankel 必要条件与充分性的区别。
- **[L07]** Luis Báez-Duarte, *A strengthening of the Nyman-Beurling criterion for the Riemann hypothesis*, [arXiv:math/0202141](https://arxiv.org/abs/math/0202141), 2002. 实际半直线 L² 载体与整数 dilation 强化。
- **[L08]** J. Brian Conrey, *Riemann's Hypothesis*, [author-hosted text](https://aimath.org/~kaur/publications/90.pdf), 2019. 素数计数、Chebyshev 误差与 Möbius 部分和的等价表述；不采用其发表时的有限零点计算数量作为当前数据。
- **[L09]** Jeffrey C. Lagarias, *An Elementary Problem Equivalent to the Riemann Hypothesis*, [arXiv:math/0008177v2](https://arxiv.org/html/math/0008177v2). Main theorem；Robin 判据、Gronwall 与约数和极值背景。
- **[L10]** YoungJu Choie, Michel Planat and Patrick Solé, *On Nicolas criterion for the Riemann Hypothesis*, [arXiv:1012.3613v2](https://arxiv.org/abs/1012.3613v2). Primorial 输入与正反两种 RH 情况下的符号结论。
- **[L11]** Jan Cisło and Marek Wolf, *On the Riesz and Baez-Duarte criteria for the Riemann Hypothesis*, [arXiv:0807.2971v1](https://arxiv.org/abs/0807.2971v1), 2008. 指数生成恒等式、Möbius 表达、Lemma 3 与 Theorem 1 的完整误差运输。
- **[L12]** Farr and Pauli, *Zeros of the derivatives of the Riemann zeta function on the left half plane*, [author-hosted text](https://mat112.uncg.edu/pauli/publications/farr-pauli_zeta-deriv-left-half-plane.pdf). Theorem 1 重述 Speiser 等价；这里只使用该经典零点带判据。
- **[L13]** H. M. Bui, S. J. Lester and M. B. Milinovich, *On Balazard, Saias, and Yor's equivalence to the Riemann Hypothesis*, [arXiv:1306.0856v1](https://arxiv.org/html/1306.0856v1), 2013. Eqs. (1.1)–(1.2)；Theorem 1.2 给出带全部尾项的截断关系。其结果亦说明不能任意假定更强截断衰减率。
- **[L14]** Bittu Chahal, Tapas Chatterjee and Sneha Chaubey, *Distribution of Farey fractions with k-free denominators*, [arXiv:2507.00228v3](https://arxiv.org/html/2507.00228v3), revised 2026-09-02. 本节只消费引言准确列出的普通 Franel–Landau 判据；其带同余类推广不混作普通 RH。
- **[L15]** Herbert S. Wilf, *The Redheffer matrix of a partially ordered set*, [arXiv:math/0408263v1](https://arxiv.org/abs/math/0408263v1), 2004. 算术 incidence 结构与行列式。
- **[L16]** François Clément and Stefan Steinerberger, *On the largest singular vector of the Redheffer matrix*, [arXiv:2502.09489v1](https://arxiv.org/html/2502.09489v1), 2025. 原始矩阵定义、Möbius 行列式背景与独立的奇异向量问题。
- **[L17]** Brad Rodgers and Terence Tao, *The de Bruijn-Newman constant is non-negative*, [arXiv:1801.05914v5](https://arxiv.org/abs/1801.05914v5), revised 2021-07-03. 热核归一化、阈值与无条件下界。
- **[L18]** Yang-Hui He, Vishnu Jejjala and Djordje Minic, *From Veneziano to Riemann: A String Theory Statement of the Riemann Hypothesis*, [arXiv:1501.01975v2](https://arxiv.org/html/1501.01975v2), 2015. Eq. (2.1) 重述 Volchkov 的嵌套对数积分。本文不消费其中推测性的物理解释。
- **[L19]** Alain Connes, Caterina Consani and Henri Moscovici, *Zeta Spectral Triples*, [arXiv:2511.22755v1](https://arxiv.org/abs/2511.22755v1), 2025. 真实谱模型与极限研究背景。
- **[L20]** Alain Connes, *The Riemann Hypothesis*, [arXiv:2602.04022v1](https://arxiv.org/abs/2602.04022v1), 2026. 当前谱路线与算术结构的综述背景。

本图谱的下一步是逐条补齐真实解析边并消费已有真源。完成一个判据族的端到端证明，就将该族的规范对象、双向定理和见证运输接回这里的共同图谱，保留全部尚未完成的量词与分析义务。


---

## RH_PUBLIC_COVERAGE_AUDIT_20260908

### 13. 公开覆盖目标与本轮计数

第一版是 18 个判据族、64 个规格节点，其中 A001 为标准 RH，其余 63 个为替代或派生表述。**这一范围没有覆盖全部公开判据。** 本次新增 A065–A093 共 29 条规格，累计 **93 个节点、92 个替代表述规格、21 个判据族**。三个新增族为 F19 自逼近、F20 Salem 积分方程、F21 置换最大阶；其他条目扩展已有族。这里的条目数包含参数族和派生表达，不能解释为 92 项独立数学发现或 92 项已完成的 Lean 定理。

目标是公开文献逐项覆盖，不以 40、50、64 或 93 为上限。完整参数定理只建一个参数化规格，不把每个数值代入另算一个发现。已发表定理、公开预印本、仅有单向证明和需要额外假设的命题分别标注。

审查入口是 Broughan 三卷、AIM 专家纲要及原始论文，同时补检 2024–2026 年文献。**这几个来源集合的逐定理核对尚未完成，故本次仍不宣称全部公开等价形式已经覆盖。** Q01–Q10 明列剩余缺口，未计入新增规格。原始 PR 起点为 `8265370d41979f8659b97f6249f9a9e3530f57f4`，完整理论 blob 为 `5899285d185d0b5b288e84b400f3523d8bed99d7`；前文 dev/PR 审查保留其原有时间和提交范围。

### 14. 自逼近、Hardy 空间和 Salem 方程

#### F19：自逼近

令 \(S=\{s:1/2<\Re s<1\}\)。对补集连通的非空紧集 \(K\subset S\)，定义

\[
d_{K,\epsilon}(T)=T^{-1}\operatorname{meas}\{\tau\in[0,T]:
\sup_{s\in K}|\zeta(s+i\tau)-\zeta(s)|<\epsilon\}.
\]

**A065，Bagchi：** 对所有上述 \(K\) 及所有 \(\epsilon>0\)，\(\liminf_{T\to\infty}d_{K,\epsilon}(T)>0\)。[E01, Theorem 2]

**A066，Laurinčikas：** 对每个上述 \(K\)，存在至多可数 \(E_K\subset(0,\infty)\)，使每个正数 \(\epsilon\notin E_K\) 对应的 \(\lim_{T\to\infty}d_{K,\epsilon}(T)\) 存在且严格为正。[E01, Theorem 4]

两条分别与 RH 等价。可数例外集合、密度归一化和全部紧集的量词必须保留；其他平移比例的自逼近可能无条件成立。

#### 扩展 F06：两个实际 Hardy 载体

半平面空间采用
\(\|f\|^2=\sup_{x>1/2}(2\pi)^{-1}\int_{\mathbb R}|f(x+it)|^2dt\)。

**A067，Bagchi：** \(E(s)=1/s\) 属于 \(G_k(s)=(k^{-s}-k^{-1})\zeta(s)/s\)、\(k\ge2\) 在 \(H^2(\Re s>1/2)\) 中的闭复线性包。\(s=1\) 处构造可去延拓。[E02, Theorem 2.2]

**A068，Noor：** 在标准单位圆盘 \(H^2\) 中，常数 \(1\) 属于下列函数的闭复线性包：

\[
h_k(z)=\frac1{1-z}\log\left(\frac{1+z+\cdots+z^{k-1}}k\right),\quad k\ge2.
\]

对数在原点取 \(-\log k\) 的解析分支。[E02, Theorem 2.1] 两条分别等价于 RH。闭包存在性不指定自然 Möbius 部分和。2026 年 [E02] 的较右半平面收敛和数值实验不能替代临界 Hardy 空间的结论。

#### F20：Salem 积分方程

**A069，Salem：** 对每个 \(1/2<\delta<1\)，每个有界可测复函数 \(f\)，若

\[
\int_0^\infty\frac{t^{\delta-1}f(t)}{e^{xt}+1}dt=0\quad\text{对所有 }x>0,
\]

则 \(f=0\) 几乎处处。所有 \(\delta\) 的合取与 RH 等价。[E03]

**A070，显式 Mellin 表达：** 对所有 \(1/2<\delta<1\)、\(\gamma\in\mathbb R\)，
\(\int_0^\infty t^{\delta-1+i\gamma}/(e^t+1)dt\ne0\)。

直接桥梁为

\[
\int_0^\infty\frac{t^{s-1}}{e^{xt}+1}dt
=x^{-s}\Gamma(s)(1-2^{1-s})\zeta(s),\quad x>0,\ \Re s>0.
\tag{E17}
\]

\(s=1\) 按可去抵消解释。目标开带上 Gamma 与 \(1-2^{1-s}\) 不为零，故 A070 与 RH 等价。[E03] 任意有界函数的 Salem 唯一性仍需自己的分析证明；显式幂函数读法不替代它。2026 预印本的发表状态与经典 Mellin 恒等式分开，不主张新的数学优先权。

### 15. 广义 Li、完整实根判据与横向单调性

#### 扩展 F02：完整实参数族

固定 \(a\in\mathbb R\setminus\{1/2\}\)，使用实际非平凡零点及解析重数定义

\[
S_n(a)=\lim_{T\to\infty}\sum_{|\Im\rho|\le T}m_\rho
\left[1-\left(\frac{\rho-a}{\rho+a-1}\right)^n\right],\quad
D_n(a)=\left.\frac1{(n-1)!}\frac{d^n}{ds^n}
\bigl((s-a)^{n-1}\log\xi(s)\bigr)\right|_{s=1-a}.
\]

对称极限、实值性和局部对数先证明合法。每个固定许可参数下，以下三条各自与 RH 等价。[E04, Theorems 1、2、5]

| ID | 精确陈述 |
| --- | --- |
| A071 | 对所有 \(n\ge1\)，\(S_n(a)\ge0\)。 |
| A072 | 对所有 \(n\ge1\)，\((1-2a)D_n(a)\ge0\)，保留左右参数区域的相反符号。 |
| A073 | 对每个 \(\epsilon>0\)，存在 \(C_{a,\epsilon}\ge0\)，使所有 \(n\ge1\) 满足 \(S_n(a)\ge-C_{a,\epsilon}e^{\epsilon n}\)。 |

原 Li 系数的特例身份要与已有导数定义证明一致。一个固定指数下界或有限前缀不能代替 A073 的全部 epsilon。

#### 扩展 F05、F15：完整不等式塔与全正性

对实际 \(\Xi\) 定义

\[
L_k[\Xi](x)=\sum_{j=0}^{2k}\frac{(-1)^{j+k}}{(2k)!}\binom{2k}{j}
\Xi^{(j)}(x)\Xi^{(2k-j)}(x).
\]

**A074，经典广义 Laguerre 判据：** 对全部 \(k\ge0,x\in\mathbb R\)，\(L_k[\Xi](x)\ge0\)。完整阶数塔等价于 RH；单个 Turán/Laguerre 不等式只提供必要条件。[E05, Section 2]

复用前文 \(a_n=n!\xi^{(2n)}(1/2)/(2n)!>0\)。

**A075，Pólya–Schur 特化：** 对每个实根实多项式 \(\sum p_jX^j\)，系数乘子输出 \(\sum a_jp_jX^j\) 仍实根，零多项式按通用乘子定义允许。[E05] 通过 \(\Psi(u)=\sum a_nu^n/n!\) 的 Laguerre–Pólya I 类性质连接 RH。

令 \(b_n=a_n/n!\) 对 \(n\ge0\)，\(b_n=0\) 对 \(n<0\)。

**A076，离散 PF∞：** 对全部阶数 \(r\ge1\)，全部严格递增非负整数行索引 \(i_p\) 和列索引 \(j_q\)，\(\det[b_{j_q-i_p}]_{p,q=1}^r\ge0\)。[E06] 使用实际 \(\Psi\) 的亏格零性质与 Aissen–Schoenberg–Whitney–Edrei 表示；不能把亏格零误写成增长阶为零。该全正性等价于 RH，所有两组索引不能缩为主子式。2026 年的巨大 shift 区域结果不完成全称判据。

#### 扩展 F01：实际 ξ 的横向性质

**A077：** 对每个 \(t\in\mathbb R\)，\(\sigma\mapsto|\xi(\sigma+it)|\) 在 \((1/2,\infty)\) 严格递增。[E07, Corollary 1] 左半平面严格递减版本由函数方程归入同族。

**A078：** 对全部 \(\Re s>1/2\)，\(\Re(\xi'(s)\overline{\xi(s)})>0\)。[E07, E15.C5c] 这是对数导数正性的无除法表达；零点处左侧为零，反向不会偷用未证明的非零分母。两条各自等价于 RH，但一般函数的严格单调不等同于导数处处严格正。

### 16. 极值整数、置换群和算术平滑

#### 扩展 F08：极丰数及超丰数子集

定义 \(F(n)=\sigma(n)/(n\log\log n)\)，

\[
XA=\{10080\}\cup\{n>10080:\ \forall\,10080\le m<n,\ F(m)<F(n)\}.
\]

**A079：** \(XA\) 无限。这与 RH 等价，保留起点 10080 及严格纪录条件。[E08, Theorem 2.4]

**A080，预印本规格，待独立核验：** 对全部 superabundant 正整数 \(n\)，\(\sigma(n)\le H_n+e^{H_n}\log H_n\)。superabundant 指每个 \(1\le m<n\) 都满足 \(\sigma(m)/m<\sigma(n)/n\)。[E09, Theorem 3.1] 声称最小 Lagarias 反例必为 superabundant；其有限初始区间与阈值单调性尚待独立复核。本条进入公开规格数量，但不能与独立核验完毕的经典定理或机器证明合并统计。

#### F21：Landau 最大置换阶

\(g(n)\) 为对称群 \(S_n\) 中元素的最大阶。使用 \(\operatorname{li}(x)=\operatorname{Ei}(\log x)\) 的主值归一化及其在 \(x>1\) 上的反函数，不能换成前文相差常数的 \(\int_2^xdt/\log t\)。设

\[
q_n=\frac{\sqrt{\operatorname{li}^{-1}(n)}-\log g(n)}{(n\log n)^{1/4}},\ n\ge2,
\quad d=\frac{2-\sqrt2}{3},\quad c=\sum_{\rho\in\mathcal Z}\frac{m_\rho}{|\rho(\rho+1)|}.
\]

\(c\) 使用实际全体零点与完整可和性。以下各条分别等价于 RH。[E10, Theorem 1.1、Corollary 1.3]

| ID | 精确陈述 |
| --- | --- |
| A081 | 所有 \(n\ge1\) 满足 \(\log g(n)<\sqrt{\operatorname{li}^{-1}(n)}\)。 |
| A082 | 存在 \(N\ge1\)，使 A081 的不等式对所有 \(n\ge N\) 成立。 |
| A083 | 所有 \(n\ge2\) 满足 \(q_n\ge d-c-\tfrac{43}{100}\tfrac{\log\log n}{\log n}>0\)。 |
| A084 | 所有 \(n\ge19425\) 满足 \(q_n\le d+c+\tfrac{51}{50}\tfrac{\log\log n}{\log n}\)。 |
| A085 | 所有 \(n\ge2\) 满足 \(\tfrac{694}{6250}<q_n\le q_2\)，其中有理下界等于 0.11104。 |
| A086 | \(d-c\le\liminf q_n\le\limsup q_n\le d+c\)。上下极限用扩展实数定义。 |
| A087 | 存在最终有界实序列 \(u_n,v_n\)，使所有充分大 \(n\) 满足 \((d-c)(1+\tfrac{\log\log n+u_n}{4\log n})\le q_n\le(d+c)(1+\tfrac{\log\log n+v_n}{4\log n})\)。 |

A087 显式保留两项 \(O(1)\)。原论文的有限计算和阈值证书未在本轮执行。群论的最大阶与 prime-power 优化必须证明是同一个对象。相近的 squarefree 优化 \(h(n)\) 或 \(\omega(g(n))\) 结论另需核对，不能据外形相同推定。

#### Nicolas 2024：全部整数上的 totient 阈值

\(p_j\) 为第 \(j\) 个素数，\(P_k=\prod_{j\le k}p_j\)，\(k=120568\)。定义

\[
A=P_k\frac{p_{k+1}p_{k+2}}{p_kp_{k-10}},\qquad
\delta=e^{\gamma_E}(4+\gamma_E-\log(4\pi)),
\]

\[
C_\varphi(n)=\left(\frac n{\varphi(n)}-e^{\gamma_E}\log\log n\right)\sqrt{\log n},\quad n\ge2.
\]

| ID | 与 RH 等价的陈述 |
| --- | --- |
| A088 | 对所有整数 \(n>A\)，\(C_\varphi(n)<\delta\)。 |
| A089 | \(\limsup_{n\to\infty}C_\varphi(n)=\delta\)。 |
| A090 | 存在实数 \(B\) 与整数 \(N\ge2\)，使全部 \(n\ge N\) 满足 \(C_\varphi(n)\le B\)。 |

[E11, Theorem 1.1、Eqs. (1.5)–(1.12)] 给出 RH 下的阈值及 limsup，非 RH 下 limsup 为正无穷。原文 \(C_\varphi(A)>\delta\)，所以输入必须是 \(n>A\)。这些全部整数的精细误差不能由原 primorial 判据 A047 直接替换。

#### 扩展 F09：完整平滑参数族

**A091，Hardy–Littlewood：** 定义整函数 \(H(x)=\sum_{j\ge1}(-x)^j/(j!\zeta(2j+1))\)。对每个 \(\epsilon>0\)，\(H(x)=O_\epsilon(x^{-1/4+\epsilon})\) 当 \(x\to+\infty\)，当且仅当 RH。[E12, Introduction] 它对应 \(\sum\mu(n)e^{-x/n^2}/n\) 的自然部分和极限；也可用绝对收敛的 \(\sum\mu(n)(e^{-x/n^2}-1)/n\) 定义，再消费无条件 \(\sum\mu(n)/n=0\)。

**A092：** 对每个固定 \(k\ge1,\ell>0\)，令 \(P_{k,\ell}(x)=\sum_{n\ge1}\mu(n)n^{-k}e^{-x/n^\ell}\)。RH 等价于

\[
\forall\epsilon>0,\quad P_{k,\ell}(x)=O_{k,\ell,\epsilon}(x^{-k/\ell+1/(2\ell)+\epsilon}).
\]

[E12, Theorem 3.10 的 zeta 特化] 每个许可参数对各自给出等价定理；\(k=1\) 的自然部分和极限不能误称绝对收敛。

**A093：** 固定整数 \(r\ge0\)、实数 \(k\ge r+1,\ell>0\)。令 \(\sigma_r(n)=\sum_{d\mid n}d^r\)，其 Dirichlet 卷积逆为 \(\sigma_r^{-1}=\mu*(n\mapsto n^r\mu(n))\)。RH 等价于

\[
\forall\epsilon>0,\quad
\sum_{n\ge1}\sigma_r^{-1}(n)n^{-k}e^{-x/n^\ell}
=O_{k,r,\ell,\epsilon}(x^{-k/\ell+(1+2r)/(2\ell)+\epsilon}).
\]

[E12, Theorem 3.13] 卷积逆不等于逐点倒数。边界参数的级数收敛须单独证明；相邻公式为使用 \(1/\zeta'(\rho)\) 所加的单零点假设不能未经核对混入此端点。一般 L-function 的版本另记为 GRH 范围。

### 17. 来源覆盖账与尚未编号的缺口

每项分别登记：来源已定位、精确陈述已提取、双向数学证明已审查、原对象上的 Lean 定理已核验。当前新增条目主要完成前两阶段。公开来源中的定理并不因此自动成为本项目的机器真值。

| 来源集合 | 已接入 | 尚未完成 |
| --- | --- | --- |
| Broughan I（2017） | 原算术族及本次极丰数、Landau、totient | 极值整数、纪录型和误差变体仍须逐定理对照。 |
| Broughan II（2017） | 原 Li/Weil/Nyman；本次 Hardy、Salem、完整实根和全正性 | 正交多项式、分圆、积分方程、离散测度、Hermitian forms、smooth numbers 未完成逐条核对。 |
| Broughan III（2023） | 原 dBN/Jensen；本次自逼近入口 | prime-counting、divisor-count、zero-gap、Dobner、Gonek–Bagchi、可判定性尚未逐定理区分附加假设。 |
| AIM 纲要 Section C | 大部分已列经典入口 | 空标题和未提取公式不能算已经覆盖；下面 Q 表保留原始论文义务。 |
| 现代论文 [E01]–[E12] | A065–A093 的明确规格 | 原始证明、精度证书及参数边界按每条来源继续核验；A080 明确保留预印本状态。 |

| 登记号 | 已找到的方向 | 尚待精确提取或核对 |
| --- | --- | --- |
| Q01 | Amoroso（1995）的分圆多项式乘积高度，AIM C3a | \(F_N=\prod_{n\le N}\Phi_n\) 的 \((2\pi)^{-1}\int_{-\pi}^{\pi}\log^+\vert F_N(e^{it})\vert dt=O_\epsilon(N^{1/2+\epsilon})\) 已见专家纲要；原始全文和全部条件未核完。 |
| Q02 | Broughan II Chapter 6；Romik 的 Hermite、Meixner–Pollaczek、continuous Hahn 展开 | 仅存在正交展开不构成 RH 等价；需要原始系数、零点或完备性判据。 |
| Q03 | Weingartner 的加权余数向量投影，[E02] 文献链 | 固定 \(r_k(j)=j\bmod k\) 的权重、索引及投影系数趋向 \(-\mu(k)/k\) 的完整量词。 |
| Q04 | Lapidus–Maier（1995）的分形弦逆谱问题 | Minkowski 维数、计数渐近、可测性以及逐维无零点与全部非中线维数的区别。 |
| Q05 | Nicolas 的 \(\pi(x)\) 与 divisor-count 判据，Broughan III Chapters 1–2 | 约数个数 \(d(n)\) 与约数和 \(\sigma(n)\) 不同，原 Robin 不能代替。 |
| Q06 | \(\omega(g(n))\) 与 squarefree 最大乘积 \(h(n)\) | 各自反向结论及精确阈值，不能从 A081 外推。 |
| Q07 | Mikolás、Pólya/Newman 积分、Grommer inequalities | AIM 部分标题没有完整命题；需追溯原函数、参数和全部阶数。 |
| Q08 | Broughan II 的离散测度、Hermitian forms、smooth numbers | 具体算术对象与必要充分性；通用 Gram 正性不够。 |
| Q09 | Mazet–Saias、Laurinčikas、Gonek–Bagchi 的离散/短区间自逼近 | 步长、例外集、区间长度及密度归一化，不能仅用 A065 代替全部变体。 |
| Q10 | Dobner、zero-gap、可判定性 | 普通 RH、GRH、RH 加单零点和逻辑附加假设逐条分类。 |

Q01–Q10 没有算入 A001–A093。它们表明目前覆盖审查尚未完成，不能通过增加同义节点宣称全公开覆盖。固定来源集合的每个实际等价定理应映射到一个 ID，或注明参数特化、同义表达、范围不同、仅单向等理由；新增公开来源继续追加。

### 18. 形式化接入与证据边界

保留 P0–P5。广义 Li 和整函数条目复用 canonical Li、实际 ξ、Jensen 与 Newton–Hankel；Hardy/Nyman 共用 Mellin 与有界变换；Salem 使用实际 ζ 的 Mellin 核和独立唯一性；极值整数复用算术函数、primorial、Gronwall/Robin；Landau 构造实际有限群与 prime-power 优化的对应；平滑参数族复用 Möbius 卷积与完整可和性。每个新 Lean 真源配套 Scribe，理论继续追加本卷。

本轮没有新增 Lean、运行编译或核验传递公理闭包。93 个节点是文献与数学规格，不能包装成接收 92 个未知等价式参数的结构后宣称形式化完成。完整终点仍是每个原始命题与 `RiemannHypothesis` 的两个方向。

### 19. 新增参考文献

- **[E01]** A. Laurinčikas, *Remarks on the Connection of the Riemann Hypothesis to Self-Approximation*, Computation 12(8), 164 (2024), [DOI:10.3390/computation12080164](https://www.mdpi.com/2079-3197/12/8/164). Theorems 2、4。
- **[E02]** J. Manzur, W. Noor, G. Quintero, *A Hardy space approximation supporting zero-free half-planes for the ζ-function*, [arXiv:2606.16097v1](https://arxiv.org/html/2606.16097v1). Theorems 2.1–2.2 重述原始 Noor、Bagchi 判据；不采用数值实验作证明。
- **[E03]** González, Negrín, *A new equivalence to the Riemann Hypothesis by means of the Salem integral equation*, [arXiv:2604.15396v1](https://arxiv.org/html/2604.15396v1). 经典 Salem 与显式幂函数读法；预印本。
- **[E04]** S. K. Sekatskii, *Generalized Bombieri–Lagarias’ theorem and generalized Li’s criterion*, [arXiv:1304.7895v3](https://arxiv.org/abs/1304.7895v3). Theorems 1、2、5。
- **[E05]** I. Wagner, *On a new class of Laguerre–Pólya type functions with applications in number theory*, [arXiv:2108.01827v2](https://arxiv.org/abs/2108.01827v2). 经典 Pólya–Schur 与广义 Laguerre 引用链；不将 shifted 类结果升级为 RH。
- **[E06]** W. Michałowski, *An explicit uniform cubic wedge for consecutive Toeplitz minors of the Riemann ξ-coefficients*, [arXiv:2607.16795v1](https://arxiv.org/html/2607.16795v1). 使用引言的经典 PF∞ 对应，巨大 shift 结果没有在本轮独立核验。
- **[E07]** J. Sondow, C. Dumitrescu, *A monotonicity property of Riemann’s xi function and a reformulation of the Riemann Hypothesis*, [arXiv:1005.1104](https://arxiv.org/abs/1005.1104). Corollary 1。
- **[E08]** S. Nazardonyavi, S. Yakubovich, *Extremely abundant numbers and the Riemann hypothesis*, [arXiv:1211.2147](https://arxiv.org/abs/1211.2147). Theorem 2.4。
- **[E09]** A. MacArevey, *On the Lagarias Inequality and Superabundant Numbers*, [arXiv:2602.15905v2](https://arxiv.org/html/2602.15905v2). Theorem 3.1；A080 待独立核验。
- **[E10]** M. Deléglise, J.-L. Nicolas, *The Landau function and the Riemann hypothesis*, [arXiv:1907.07664](https://arxiv.org/abs/1907.07664). Theorem 1.1、Corollary 1.3、Section 2.2。
- **[E11]** J.-L. Nicolas, *A Robin inequality for n/phi(n)*, New Zealand Journal of Mathematics 55 (2024), 1–9, [DOI:10.53733/324](https://nzjmath.org/index.php/NZJMATH/article/view/324). Theorem 1.1 与 Eqs. (1.5)–(1.12)。
- **[E12]** Garg, Maji, *Equivalent criteria for the Riemann hypothesis for a general class of L-functions*, [arXiv:2409.17708v2](https://arxiv.org/html/2409.17708v2). Introduction、Theorems 3.10、3.13；这里只收普通 ζ 范围。
- **[E13]** K. Broughan, *Equivalents of the Riemann Hypothesis*, Volume I (2017), [DOI:10.1017/9781108178228](https://doi.org/10.1017/9781108178228); Volume II (2017), [DOI:10.1017/9781108178266](https://doi.org/10.1017/9781108178266). 已核目录与部分对应原文，未完成全书逐定理核对。
- **[E14]** K. Broughan, Volume III (2023), [DOI:10.1017/9781009384780](https://doi.org/10.1017/9781009384780). 逐定理覆盖审查仍开放。
- **[E15]** American Institute of Mathematics, [RH expert workshop outline](https://www.aimath.org/WWN/rh/rh.pdf), Section C。第一方专家目录与原文追溯入口，空标题不充当完整定理。

**当前状态：93 个节点、92 个替代表述规格、21 个判据族；公开文献全覆盖仍未完成，Q01–Q10 是明确未决项。**

- Parallel #5602 source at `4804c4020d7d9f165a2e2683c42b01e3d47a8be4`: `WeilPrimeActivationEdge.lean`, blob `5cd36bfeef88311e1f5e6c140fc11e52b16e8881`; `certify_prime3_scale_schur.py`, blob `496333f97d20a6898d47f848a2abd839249e9207`.


---

## [PR #5602] SAME_PROLATE_SCALE_FLOW_AND_CENTERED_READOUT_TRANSPORT

# 2026-09-07：同一真实 prolate 族的尺度流与中心化读出运输

本节继续使用已认证的半宽区间 I={|a-a0|<=2e-8}，a0=log3/2。新结论处理随 a 变化的真正 prolate 模型，以及其原点归一化 Fourier 值和 model-centered 代表元。它不把中心尺度的种子固定后重新命名成真实尺度族，也不将模型的变化界当作新区间上真实 Weil ground 的误差界。

新 Lean 为 `WeilMellinScaleFlow.lean`，有同名 Scribe；主程序为 `certify_prime3_prolate_scale_transport.py`。其 110、130 位定向运行均通过。Lean elaboration、Scribe emission 与传递公理审查未运行。标准正规 prolate 实现、谱投影、积分变量代换与以下范数运输是纸面桥；新 Lean 保存原 `Zeta23.paperFT` 的有限多项式尺度对应。

## 1. 固定种子的精确尺度流，包含新整数进入的边界

对固定连续偶种子 H 于 [-1,1]，物理种子为 h_a(t)=H(t exp(-a))，于 t>exp(a) 置零。实际未偶化算术函数为

\[
p_{a,H}(x)=1_{[-a,a]}(x)\,4e^{x/2}\sum_{1\le m\le e^{a-x}}H(me^{x-a}).
\]

令 s=1/2+iz，Phi_(a,H)(z)=paperFT(p_(a,H))(z)。按每个 m 的实际支撑积分，作 t=m exp(x-a) 代换，得到

\[
\boxed{\Phi_{a,H}(z)=4e^{as}\sum_{m\le e^{2a}}m^{-s}
\int_{me^{-2a}}^1H(t)t^{s-1}\,dt.}
\tag{SF1}
\]

正 t 上的复幂均按实对数定义，有限窗口内无分支歧义。固定可见整数集合的开区间内，微分下端积分给出

\[
\boxed{(\partial_a-s)\Phi_{a,H}(z)=8e^{-as}\sum_{m\le e^{2a}}H(me^{-2a}).}
\tag{SF2}
\]

在 a_m=log(m)/2，新 m 项的上下积分限同为 1，其 Fourier 质量严格为零。因此 Phi 连续，可将两侧的导数上界相接。其该项的一阶导数右减左为 8 exp(-a_m s)H(1)，不应把整个尺度族无条件当成 C1。偶化值是 [Phi(z)+Phi(-z)]/2，两边均按同一公式处理。对真正变化的 H_a，本节不对其求导，而用下一节的独立谱误差分开运输。

当 H(t)=sum_(r<d)B_r*t^(2r)，物理多项式的系数是 B_r exp(-2ra)。新定义 `scaledPolynomialWindow` 直接把这些系数送入已有 `polynomialMellinWindow`。`scaled_polynomial_centered_paperFT` 证明

\[
\boxed{e^{-as}\Phi_{a,H}(z)=4\sum_{m=1}^M\sum_{r<d}
B_rm^{2r}\frac{e^{-(s+2r)\log m}-e^{-2(s+2r)a}}{s+2r}.}
\tag{SF3}
\]

假设是各纳入整数满足 log(m)<=2a 及 Im(z)<1/2。可积性及实际端点积分来自原 owner。`scaled_polynomial_paperFT_scale_difference` 进一步证明两尺度的 (SF3) 相减只留下后一个指数的差。代码不假设目标误差界或积分值，也未新定义 Fourier。一般固定连续 H 的 (SF1)-(SF2) 为纸面推导；有限多项式情形的代数导数由独立符号测试核对。

## 2. 对所有尺度重新认证实际 prolate 模式

在固定 [-1,1] 上，实际正规偶 prolate 算子为

\[
\mathcal L_a=-\partial_t((1-t^2)\partial_t)+q(a)^2t^2,
\qquad q(a)=2\pi e^{2a}.
\]

使用前文同一个正交归一偶 Legendre 基与正规自伴实现。J=32 个保留系数外的整个块仍有下界 2J(2J+1)=4160，因为乘法势 q(a)^2t^2 非负。跨块只有一项 b(a)。对每个实移位 eta<4160，真实 Schur 块夹在 A_J(a)-eta I 与 A_J(a)-eta I-b(a)^2/(4160-eta)*e_last e_last^* 之间。

程序直接将 q(a)^2 作为整个闭区间，分别对两条固定 dyadic 提案中心 mu_i 的 mu_i-50 和 mu_i+50 检查两个 Schur 端点的严格惯性。四个计数依次为 (0,0,1,1) 和 (2,2,3,3)，对所有 a∈I 成立。这识别了真实偶谱编号 0、2，也保证它们各自为单特征值；未信任有限本征求解器或旧结果 JSON。

为避免丢失尺度参数的相关性，残差使用精确算子关系

\[
(\mathcal L_a-\mu_i)v_i=(\mathcal L_{a0}-\mu_i)v_i
+[q(a)^2-q(a0)^2]t^2v_i.
\tag{SF4}
\]

两项的完整范数都包含第 J 个遗漏坐标。独立算出的 ||t^2 v_i|| 约为 0.04535432874 和 0.28854567727。由其余谱与 mu_i 距离至少 50，真实单位模式的符号对齐误差 <=sqrt(2)*r_i/50。两个零阶 Legendre 系数均以严格正下界固定符号。

设 rho=v_(4,0)/v_(0,0)，固定多项式组合 Htilde=v4-rho*v0。实际零积分组合为 H_a=psi_(4,a)-(psi_(4,a))_0/(psi_(0,a))_0*psi_(0,a)。两条单位模式误差 eps0、eps4 给出

\[
\Delta_\rho=(\epsilon_4+|\rho|\epsilon_0)/(v_{0,0}-\epsilon_0),\quad
\|H_a-\widetilde H\|_2\le\epsilon_4+(|\rho|+\Delta_\rho)\epsilon_0+\Delta_\rho.
\tag{SF5}
\]

分母被独立认证为正。本次整个区间的 (SF5) 小于 652/10^9；中心尺度独立计算的相同预算小于 3.142e-29。实际模式与固定多项式仅在这个明确误差内对应。

## 3. 实际窗口、种子误差和归一化一起运输

在本区间只有整数 1、2、3 可能出现。变量代换 t=m exp(x-a) 给出

\[
\|p_{a,H}-p_{a,G}\|_2\le C_a\|H-G\|_2,\qquad
C_a=4e^{a/2}\sum_{m=1}^3m^{-1/2}.
\tag{SF6}
\]

对 |Im(z)|<=b，Fourier 差再乘 sqrt(2a) exp(ab)。有限 Legendre 展开给出固定 Htilde 的 ||Htilde||_2<=1+|rho| 及 ||Htilde||_infinity<7.610。后者由 |P_n(t)|<=1 保留所有系数，不是假设真实 H_a 有该相同上界。

取复圆盘 D={|z-(20+i/4)|<=1/1000}，b=251/1000。令 a_-、a_+ 为尺度区间端点，B_b=sqrt(2a_+) exp(a_+b) C_(a_+)。由 (SF2) 与 |s|<21，固定种子整个尺度区间内的分段导数界为

\[
K_b=21B_b(1+|\rho|)+24e^{-a_-(1/2-b)}\|\widetilde H\|_\infty.
\tag{SF7}
\]

原点单独用 K_0=B_0(1+|rho|)/2+24 exp(-a_-/2)||Htilde||_infinity。将真实种子到多项式、固定种子的尺度流、多项式到中心真实种子三段相加，得到所有 a∈I、z∈D 的原始 Fourier 差 E_z<2.2230e-5，原点差 E_0<1.1189e-5。这些是参数区间和复圆盘的一致预算，没有抽样替代全称量词。

中心多项式原点由原 Mellin 端点公式计算为约 2.33619788660；加入中心种子误差以及 E0 后，对本节固定的零积分组合标度有

\[
\boxed{|\widehat p_{a,H_a}^{+}(0)|>23/10\quad(a\in I).}
\tag{SF8}
\]

令 P_a(z)=paperFT(p_(a,H_a)^+)(z)/paperFT(p_(a,H_a)^+)(0)。以中心原点模长下界 b0 和中心圆盘分子上界 M0 代入精确复商差式，

\[
|P_a(z)-P_{a0}(z)|\le(E_z+M_0E_0/b_0)/(b_0-E_0).
\]

计算所得上预算约 9.549046646e-6，严格证明

\[
\boxed{\sup_{a\in I,\ z\in D}|P_a(z)-P_{a0}(z)|<10^{-5}.}
\tag{SF9}
\]

(SF8) 的原始范数依赖本节固定标度；(SF9) 代数消去一切整体尺度和相位，与此前原点归一化模型完全相同。

## 4. 对接新的 model-centered 读出，而不冻结错误的中心系数

本轮实际读取 #5895 提交 `44a831a15abe4d00268d973976101e0d62d66fd2` 中 `GenuineModelDualTransport.lean` 的 `model_centered_readout_identity` 和 `annihilating_energy_dual_transport`。其系数必须是同一真实模型的比值，且其对偶预算必须另行认证。

在共同空间 L2([-1,1])，定义 g_(a,z)(y)=conjugate(cos(a z y))，g0=1，以及 h_(a,z)=g_(a,z)-conjugate(P_a(z))*g0。对真实模型的酉伸缩向量 e_a，严格有 <h_(a,z),e_a>=0，sqrt(a) 因子在原点比值中消去。由复指数核导数与 (SF9)，

\[
\|h_{a,z}-h_{a0,z}\|_2
\le\sqrt2\,|z|e^{a_+b}|a-a0|+\sqrt2\,|P_a(z)-P_{a0}(z)|.
\]

定向程序证明

\[
\boxed{\sup_{a\in I,\ z\in D}\|h_{a,z}-h_{a0,z}\|_2<15/10^6.}
\tag{SF10}
\]

这是实际中心化代表元的变化预算。它没有证明全对偶残差，因为还需要同一试探函数上的 (A_a-A_a0)v，以及正移位、候选/模型正交补和分母界的统一组合。不能将中心 z、a0 的旧 C 值无修改地用于整个参数区间。

## 5. 研究来源、实际执行和剩余承重义务

CCM, *Zeta Spectral Triples*, arXiv:2511.22755v1, Section 8 仍明确区分最低模态的单纯偶性与充分精确的真实模型对应。DLMF 30.3 的正规 spheroidal 模式和参数性质用于核对对象；此处数值隔离由实际无限 Jacobi 界独立认证，未由定性解析性代替误差率。Suzuki arXiv:2606.09096 的原始版本页此次返回 v1；未使用聚合站声称的未核验新版结果。

也读取 loning/5040 研究链 #6204 的实际 `GronwallUpperEnvelope.lean`，提交 `0805069c8c630f909f89b0573dbe672c98f275bc`。它复用 Mertens III 得到归一化 divisor sum 最终 <=1+epsilon。这个标量包络没有提供严格 Robin 全称界或当前算子谱间隔；本节不将它混作前提。其已合并状态已从 PR 元数据核对，作者自报的编译未在此复验。

新 verifier 以固定 proposal 的 SHA-256 为输入检查，并在 110、130 位定向精度分别运行通过；未读取旧数值谱结论、未用 eigensolver 或数值求积。种子比值、所有遗漏 Legendre 分量、激活边界、原点分母和中心化代表元变化均明确计入。独立表达式诊断核对了 24 条符号尺度/导数/激活等式、5 个错误 seed 缩放的失败对照，以及 12 次原物理窗口积分对照。后者为非定向 65 位诊断，最大相对差约 4.121e-66，不作为区间证明依据。

Verifier SHA-256：`fe1d574f38a13e0dbcc185649c0e6c32dfd9e1cb676ceebb73ad7c6c31218b4f`。Proposal SHA-256：`242c9897bbd247ef0485039e6dcde819a351c5900ceac52fecc420934c1896db`。三个新公开 Lean 定义/定理有三个 FromLean Scribe 项。Lean、Scribe 编译及公理闭包未执行，测试由同一助手完成，无独立作者审查或数学优先权声明。

本轮提供同一尺度区间中真正 prolate 族的 Fourier 和中心化读出变化率。此前的统一 simple-even/gap 证书已另行写回并重跑；它与 (SF9) 之间仍缺真实 Weil ground 的统一方向误差，不能据此宣称已得到区间 ground/prolate 的完整逼近或 Xi 极限。下一实际算术任务是联合验证变尺度对偶作用及其完整 Schur 补，保留本节已确定的同模型中心系数。

参考：

- Connes, Consani, Moscovici, arXiv:2511.22755v1, Sections 7-8. https://arxiv.org/html/2511.22755v1
- NIST DLMF 30.3, 30.8, regular spheroidal eigenvalues and Legendre expansions. https://dlmf.nist.gov/30.3 ; https://dlmf.nist.gov/30.8
- Suzuki, arXiv:2606.09096v1. https://arxiv.org/abs/2606.09096
- Actual #5895 `GenuineModelDualTransport.lean`, blob `d6940d2ee2cc91ebe1f6faed01b75b9adc8cd7e3`; #6204 `GronwallUpperEnvelope.lean`, blob `75eb28885ee1250985d9dbd19b73fa76f3502d04`.

参考：Connes-Consani-Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, Sections 7-8；Connes, arXiv:2602.04022；既有 `WeilPolynomialMellinWindow`、`WeilMellinScaleFlow` 和本卷 prolate Jacobi 实现。


---

## [PR #5602] SAME_SCALE_GROUND_PROLATE_AND_RESIDUAL_INVERSE_ENERGY

# 2026-09-08：同尺度 ground/prolate 联合区间证书与残差驱动的逆能量

新 Lean：`D5/S3/Weil/GroundMode/ResidualDrivenProjectiveEnergy.lean`，配套同名 Scribe。
主程序：`research/weil_ground_mode/certify_prime3_uniform_ground_readout.py`；主结果为 `prime3_uniform_ground_readout_certificate.json`。
第二表达检查：`test_uniform_ground_readout.py` 与 `uniform_ground_readout_regression.json`。

本节连接前两节分别完成的统一 Weil 谱分离和真实 prolate 尺度传递。对同一个连续尺度区间和同一个复圆盘，直接认证实际最低模态与同尺度真实模型的原点归一化差。方法以实际候选残差和观察代表元在完整逆能量中的预算为输入，不再预设一条绝对的统一最低特征值下界。数值证书使用新鲜重放的全空间算术矩阵、高补空间和真实 prolate 数据；其 Fourier/core、高空间估计和逆形式识别仍是纸面分析，不冒称端到端内核结果。

## 1. 精确交付目标与同一对象

保持
\[
a_0=\tfrac12\log3,\quad I=[a_0-2\cdot10^{-8},a_0+2\cdot10^{-8}],
\quad D=\{z:|z-(20+i/4)|\le10^{-3}\}.
\tag{UG1}
\]
令 u_a 为原 Weil Friedrichs 实现的真实最低模态，p_a^+ 为前节同一个真实零积分 prolate 构造的算术合成与偶化。两个原点分母都需单独证明非零。本节的计算机辅助结论为
\[
\boxed{\sup_{a\in I,z\in D}
\left|\frac{\widehat u_a(z)}{\widehat u_a(0)}-
\frac{\widehat p_a^+(z)}{\widehat p_a^+(0)}\right|<\frac1{5000}.}
\tag{UG2}
\]
实际充分上预算小于 0.000187345067。区间没有扩大，但原先缺少的同尺度 ground/model 连接现在被兑现。#5895 已记录中心尺度上更小的 7/50000 预算，本节不宣称改进其中心精度；这里同时覆盖整个 I 和 D，并去掉旧绝对 ground 下界这一数值前提。所有出现的十进制“上预算区间”都只用于上界，不能把其左端点解读为未知真实误差的正下界。

用 J_a f(y)=sqrt(a)f(ay) 统一到 H=L2([-1,1])。k 为原 129 个整数坐标归一化后的固定实偶候选。记 A=J_a A_a J_a^-1、mu=<k,Ak>，本节所有内积第一变量反线性。原区间程序重新验证 mu<U=3/2500000、全候选正交补 q>=tau||.||^2，其中 tau=3/500000，并独立验证奇扇区下界。因此 lambda_0<U、最低模态单纯偶性以及原全空间间隔 >4.8e-6 在本节通过新鲜重放取得，不以历史结果 JSON 为输入。

## 2. 新残差能量步骤：无需绝对 ground 下界

在偶不变域设 M=A-U，Q 为 k 的正交补投影，r=QAk=Ak-mu k。设该补空间有 q_M(f)>=kap||f||^2、kap>0，并已由实际候选残差的独立计算得到
\[
|\langle r,f\rangle|^2\le E q_M(f)\qquad(f\perp k).
\tag{UG3}
\]
令 alpha=<k,u>。如果 alpha=0，非零 u 位于该补空间，但 q_M(u)=(lambda_0-U)||u||^2<=0，与正 coercivity 矛盾。因此 alpha 非零。精确误差 w=u/alpha-k 满足 w perpendicular k，由本征方程有
\[
\boxed{q_M(w)+(U-\lambda_0)\|w\|^2=-\Re\langle w,r\rangle.}
\tag{UG4}
\]
于是 0<=q_M(w)<=|<w,r>|；(UG3) 给出 q_M(w)^2<=E q_M(w)，从而
\[
\boxed{q_M(w)\le E,\qquad \|w\|^2\le E/\mathrm{kap}.}
\tag{UG5}
\]
新 Lean `residual_driven_projective_energy` 从同一线性域上的 eigen-equation、非正 shifted eigenvalue、单位 k 和完整 residual-functional bound 证明非零 overlap、正交性及 (UG5)。其 residual 是 M(k)-Re<k,M(k)>k。真实自伴性用于数值消费者的谱和逆能量识别；这条代数/能量引理本身不额外要求未使用的对称性。没有接收未知 w 的误差界或绝对 lambda_0 下界作为假设。

若实际 centered Fourier 代表元 g 另有 |<g,f>|^2<=C q_M(f) 于同一补空间，则 |<g,w>|^2<=EC。该最后一步是既有能量对偶思想的直接使用，不建立第二套通用读出 owner。

## 3. 完整逆能量由实际 Schur 数据控制

令 v 为原候选尚未归一化的有限实偶坐标，v=sqrt(beta)k，beta=||v||^2 由整数精确决定。考虑稳定化的偶扇区算子
\[
G=A-U+vv^*.
\]
它在 k 的正交补上与 M 具有相同二次型。低/高分块写成 G=[[L,C^*],[C,H]]，H>=D0>0，原生产者重新计算的 Wup 满足 Wup>=C^*D0^-1 C。D0 对近场 shells 取已证明下界 d_shell-tau；因 U<tau，这也保守控制 G 的高块。远场采用同一高空间公式在 M_cut+1 的下界，取 M_cut=32768。

若 S=L-Wup>0，则 G_D=[[L,C^*],[C,D0]] 正定且 G>=G_D。对任意完整 load b=(b_L,b_H)，变分逆单调性和完整平方分解给出
\[
\begin{aligned}
\langle b,G^{-1}b\rangle
&\le\langle b,G_D^{-1}b\rangle\\
&= e_H+\langle b_L-y,(L-C^*D_0^{-1}C)^{-1}(b_L-y)\rangle\\
&\le e_H+\langle b_L-y,S^{-1}(b_L-y)\rangle,
\quad e_H=\langle b_H,D_0^{-1}b_H\rangle,\quad y=C^*D_0^{-1}b_H.
\end{aligned}
\tag{UG6}
\]
这些等式先对有限高组合和低坐标配对证明，再由加权平方可和及形式表示推广；所有高坐标是实际无限空间，未把截断逆矩阵当作完整逆。C 的列是真实有限低基函数的高算子像，属于 L2；D0 下界正，交叉项由 Cauchy-Schwarz 收敛。

浮点 Cholesky 只提出方阵 R，其每项随后固定为分母 2^32 的精确 dyadic。定向乘法与 Gershgorin 逐行认证
\[
R^*S R\succeq(99/100)I.
\]
因此 R 必可逆，S^-1<=RR^*/(99/100)。认证器实际使用
\[
\boxed{\langle b,G^{-1}b\rangle\le e_H+
\|R^*(b_L-y)\|^2/(99/100).}
\tag{UG7}
\]
R 的数值产生过程不提供正确性或最优性假设。把全逆变分 supremum 限制到 k 的正交补，只会使它变小，所以 (UG7) 同时给出 (UG3) 与观察量的完整双范数预算。

另一次独立严格区间 LDL 检查增强偶 sector 的 coercivity。令 d_min 为首个高偶 shell 的下界，rho=(d_min-tau)/(d_min-U-kap)，取 kap=1/1000；对所有更高 d，(d-tau)/(d-U-kap)<=rho。程序验证 d_min>U+kap 和
\[
A_{\rm low}+vv^*-(U+\mathrm{kap})I-\rho W_{\rm up}>0.
\]
完整 Schur 推出 G>=kap I，因而同一偶 candidate complement 上 q_M>=kap||.||^2。这是新的整区间偶扇区检查；不能把 kap 赋给奇扇区或声称它是全空间 ground gap。

## 4. 候选残差先保留共同高符号，再求完整逆能量

取正 parity 基 E0=1/sqrt2、En=(-1)^n cos(pi*n*y)。设 k_n 为该基中的实际归一化候选坐标，s_n 为原 prime/pole/Gamma 边界符号。对 m>64，候选残差高坐标等于
\[
\boxed{r_m=
\sum_{n=1}^{64}\frac{2n k_n s_n}{\pi(m^2-n^2)}
-s_m\left\{\frac{\sqrt2 k_0}{\pi m}+
\sum_{n=1}^{64}\frac{2m k_n}{\pi(m^2-n^2)}\right\}.}
\tag{UG8}
\]
与原 parity 列相加完全相同，但同一个 s_m 只在候选求和之后乘一次。这保留了真实相关抵消。低残差则用同一完整低矩阵计算 Ak-mu k，没有假设有限候选是本征向量。

所有 65<=m<=32768 的高 load、加权平方和及 y 的每个坐标都以向外舍入区间计算。最终批量求和将 binary64 上下端点精确转换为有理数，再向外包一次，不使用无误差预算的浮点求和。工作精度 100/120 位不意味着每个 bulk 输入有同样准确度。

远场保留候选的两个真实边界 jet：
\[
t_0=k_0+\sqrt2\sum n^0k_n,\qquad t_1=\sqrt2\sum n k_n s_n,
\quad K_1=|k_0|+\sqrt2\sum|k_n|.
\]
原符号 |s_n|<=B=4 由原生产者的真实 Gamma、pole、两个素数预算重新验证。原有列的二阶展开给出
\[
|r_m|\le a_1/m+a_2/m^2+a_3/m^3,
\quad a_1=\sqrt2 B|t_0|/\pi,\ a_2=\sqrt2|t_1|/\pi,
\quad a_3=\frac{2\sqrt2 BN^2K_1}{\pi(1-N/M_{\rm cut})}.
\tag{UG9}
\]
因此远场加权平方尾为至多
\[
f_{\rm tail}\sum_{i,j=1}^3
\frac{a_i a_j}{(i+j-1)M_{\rm cut}^{i+j-1}}.
\]
正 parity 坐标已经包含两个原始 Fourier 方向，不能再重复乘二。每个交叉坐标的远场模长用 sqrt(T_i e_tail) 控制，T_i 是原耦合列的完整加权尾上界。复圆盘外包为矩形会增加保守性，但不会丢掉相位或尾部。没有终端频率截止。

## 5. 真正的 Fourier 观察量与整体归一化

固定空间中取 g_(a,z)(y)=conjugate(cos(a*z*y))，K0=<1,k>=sqrt2*k0，与 a 无关。令 K_a(z)=<g_(a,z),k>/K0，并把代表元中心化为
\[
h_{a,z}=g_{a,z}-\overline{K_a(z)}\,1.
\]
它在 k 上严格读出零。写 zeta=conjugate(a z)，正 parity Fourier 系数为
\[
(g_{a,z})_0=\sqrt2\sin\zeta/\zeta,
\qquad(g_{a,z})_n=\frac{2\zeta\sin\zeta}{\zeta^2-\pi^2n^2}\quad(n>0).
\]
中心化只改变零坐标，实际采用 h0=-sum_(n>0)k_n*g_n/k0，因此候选配对恒等式先精确消去。中心 z0 非实且 a>0，实际有限分母非零。对所有 m>M_cut 且 M_cut>=2|zeta|/pi，|h_m|<=4|2zeta sin zeta|/(3pi^2m^2)，完整加权平方尾由相应 m^-4 积分覆盖。

把同一 (UG7) 分别用于 r_a 和 h_(a,z0)，两档执行均认证
\[
\boxed{E_a<4.4\cdot10^{-9},\qquad C_{a,z_0}<3.7.}
\tag{UG10}
\]
实际充分上表达式的上端分别约为 4.353429552e-9、3.678035788。前者的原始近高加权质量约 1.19402e-9，剩余无限高尾上预算约 5.80375e-12，低 load 与全部高交叉相消后的预算也计入。

令 b=251/1000、a_+=sup I、rho_z=1/1000。有限窗口 Fourier 导数和固定 k 给出
\[
\|h_{a,z}-h_{a,z_0}\|\le
\sqrt2 a_+e^{a_+b}(1+\sqrt2/|K0|)\rho_z=:d.
\]
由于整个偶扇区 G>=kap I，在其逆能量范数中应用三角不等式，得
\[
C_{a,D}\le(\sqrt{C_{a,z_0}}+d/\sqrt{\mathrm{kap}})^2<4.
\tag{UG11}
\]
这是整个复圆盘的解析控制，不是采样网格。

由 (UG5)，||w_a||<=sqrt(E_a/kap)。固定空间的 projective 原点分母满足
\[
b_a=|\langle1,k+w_a\rangle|\ge |K0|-\sqrt2\sqrt{E_a/\mathrm{kap}}>27/25.
\tag{UG12}
\]
这里 K0 约为 -1.085330103，是伸缩到 [-1,1] 后的积分；不要与旧物理窗口中的 -0.804394472 混用。物理 Fourier 积分有 sqrt(a) 因子，它在原点归一化中消去。精确中心化恒等式给出
\[
\boxed{\sup_{a\in I,z\in D}
\left|\frac{\widehat u_a(z)}{\widehat u_a(0)}-K_a(z)\right|
\le\frac{\sqrt{E_a C_{a,D}}}{b_a}<1/8000.}
\tag{UG13}
\]
实际上预算小于 0.000120866616。固定区间的 ground placement、偶性和所有分母均已支付，没有每个 z 单独选择的相位。

## 6. 接回同尺度真实 prolate 模型

主程序实际重跑原中心 `certify_prime3_prolate_model.py` 和区间 `certify_prime3_prolate_scale_transport.py`。两者包含真实无限 Legendre 补空间和完整 residual，不从存储结果读取真假。保持此前同一个零积分组合和全局符号，中心单位模型与 k 的距离仍按新鲜结果 <113/100000 运输；多项式 Mellin 端点积分给出中心 Fourier 和原点值，真实模型误差及其分母变化全部保留。

用代表元的频率变化界控制中心尺度的整个 D，再加固定 k 的尺度变化及前节真实 prolate 原点归一化尺度差，得到
\[
\boxed{\sup_{a\in I,z\in D}|K_a(z)-P_a(z)|<67\cdot10^{-6}.}
\tag{UG14}
\]
其实际上预算小于 0.000066478451。相加 (UG13)、(UG14) 得 (UG2)，且粗有理界已满足 1/8000+67/10^6<1/5000。主程序还直接相加未粗化区间以保留更窄的数值余量。

## 7. 源码复用、复验与边界

原 `certify_prime3_scale_interval.py` 只增加关键字 `with_components` 返回已经完成全部 checks 的新鲜算术矩阵、symbols、shells 和耦合列，避免复制其计算或读取旧 JSON。默认执行和数学结论保持不变；单独重新执行 70 位后，解析后的结果与原记录唯一差异为源哈希。现行结果记录随之更新，排版变化不承担精度。原有 Lean/Scribe 字节不修改。

新主程序最终源码在 100、120 位分别执行通过。每次都重跑全部 full-space Weil interval、两个真正 prolate 验证器、完整 loads、逆 Schur、增强偶 coercivity、原点与 Fourier 预算。旧绝对 ell、旧中心 ground 下界和旧能量对偶成功 JSON 均不作为数值前提。没有 zeta 零点、未验证 eigensolver 或随机采样作为全称证明。

同一作者的第二表达检查通过 60 个精确复 Schur 恒等式、60 个高块逆单调比较、180 个残差能量例子、4 个原始列代数恒等式及9个完整尾原函数。60 个错误交叉符号都被发现；去掉非正 shifted eigenvalue 有一个精确失败例子。三个不允许的精度和一个错误输入 pin 均在重计算前拒绝；启用 Python -O 也实际拒绝。人工矩阵只检验代数，不被称为实际 Weil 数值证据或独立作者审稿。

Lean 的唯一公开定理有同名 FromLean Scribe 条目。当前环境未取得 Lean/lake 执行，故没有 elaboration、公理闭包或 Scribe 发射成功声明。新定理是逻辑审查后的 Candidate；原 Fourier/core、完整高空间下界、逆形式和无限 block 消元继续属于明确的纸面桥。精确/区间重放不是内核验收。

主程序 SHA-256：`9dd3a99fc5881b2acf59853633821a705d3416bc7d0f1b0b69d9ae43bdd74e15`。
新鲜矩阵生产者 SHA-256：`13b50abcec06663e35ad8f704cac6de9f3c1a2c37159e7f63e8c24fee4681993`。

## 8. 最新相关研究与剩余开放目标

实际读取 #5895 at `023e6d1eccb223a563939590d301085a220b38f2` 的 `InvariantSectorEnergyReadout.lean`：不变 readout 可只支付本 sector 的 coercivity，但不能把该阈值充当全空间间隔。本节保留这一分工，并对更宽的前节 I 重做完整偶检查；未隐式导入未合并模块。#5882 的 `ProjectiveEnergyDual.lean` at `65339a3acbe99e661c6955dbb21728c4c62dfe76` 使用绝对 ell 和 U-ell，本节改用 (UG3)-(UG5) 中实际 residual 的双能量输入，未重复其通用读出包装。

5040 研究 #6398 的 `PrimeValuationGap.lean` at `efd0a8a82d885491b22497822ad25da8cc2ee0bd` 已有固定素数/有界指数类的 Robin 尖锐渐近上包络。实际源码先固定 boost，再取整数阈值，保留量词顺序；该标量结果没有被移作当前谱假设。本节也不把“每个窄区间可认证”误写成无界尺度统一收敛。

再次核对 CCM arXiv:2511.22755v1 Sections 7-8 的实际模型和缺失步骤，以及 Dusson-Sigal-Stamm arXiv:2008.10871 的 Schur 方法背景。残差后验估计、逆单调性和 block 配方为经典工具；这里的工作是同一算术对象的完整兑现，不宣称方法优先权。任何外部 Schrödinger 正则性假设均未移入本算子。

本节完成的连接是：在一个跨 prime-3 激活的连续参数区间上，统一谱分离、真实模型尺度流和同尺度规范化 Fourier 误差终于同时可用。区间仍窄，复圆盘仍小，不能给出 Xi 极限。下一承重任务是扩展实际可认证的参数跨度，或在无界尺度序列上同时控制残差逆能量 E_a、centered 观察预算 C_(a,K)、非零原点 b_a 和正确模型识别，使 E_a C_(a,K)/b_a^2 趋零。本节不证明该全尺度率、一般简单偶最低族或 RH。

## [PR #5602] UNIFORM_SCHUR_CERTIFICATE_RECEIPTS

Verifier SHA-256：`c527fa349cc1b6e14afedaffae0a44eb453cfff68aea12709dac0379236fa7d6`。
90 位结果 SHA-256：`d02b04f9318ccea70a8a7bc5d239f18a59142823608157739f57f1ab6185a146`。
120 位结果 SHA-256：`9d9ad89760bcd2635bd569549810c74ddca582d9069d670bdb18e232a60064f0`。
诊断源 SHA-256：`fd24021b55526ae061f22ecf327030c929836dd343d699aa2a89e2252edc8aff`。

校核补记：第二表达诊断最初复用了一个已消耗的迭代器，导致有理复向量求和只检查实部。现已先物化系数列表，加入非零虚部控制，并重新执行全部诊断。主区间验证器、两个精度的谱结果和前述解析证明均未改变。

三条公开 Lean 定义/定理具有三个对应 FromLean Scribe 条目。没有新 authored sorry、admit 或 axiom；Lean elaboration、Scribe 发射与传递公理报告未执行。计算机辅助结果依赖明确的 Fourier/core、无限尾纸面证明，以及 Python、NumPy、mpmath 的算术实现；没有独立作者审查。

- https://arxiv.org/html/2511.22755v1 , Sections 7-8.
- https://arxiv.org/html/2606.09096v1 , Sections 1.2 and 2.1.
- https://arxiv.org/abs/math/0503328 , primary abstract and methodological scope.

## [PR #5895] MODEL_CENTERED_ENERGY_READOUT_AND_NORMALIZED_SINGLE_RATE

### 1. Target and the additional exact information

The target remains the actual lowest-Weil-mode comparison with the SAME
prolate family in Connes, Consani and Moscovici, arXiv:2511.22755v1,
Section 8, distinct from the explicit-model limit in Lemma 7.3. This increment
addresses the normalized observable F(u)(z)/F(u)(0). The normalization removes
global phase and amplitude, but its denominator still needs a certificate.

The current #5602 source at 4b56b742eb5d3bc67e0e1bba3de8457224b4abc9 already
has an origin-normalized fixed-window certificate, with error <51/100000 on
a disk of radius 1/1000 around 20+i/4. It also adds Gamma form-scale moduli.
Those computations and scale results are not repeated or claimed here. The
new result retains an exact annihilation identity in the positive-form
transport and derives a single normalized directional-rate condition.
The actual EnergyDualPaperFT source on #5882 was reread. Its original
unnormalized full-residual limit transport is not redefined.

Loning's #5326 was inspected at PR-description scope for its distinction
between finite boundary evidence and actual limiting functions. The 2026
paper Wu and Zhang, arXiv:2607.23850, was read at primary-abstract scope for
output-specific adjoint error estimation. Its PDE assumptions and error
representation are not imported as Weil theorems. Suzuki, arXiv:2606.09096v1,
retains the localized form-domain/lower-bound distinction used here. The
centered linear functional, positive-form Young estimate and quotient
identity are classical algebraic tools; no priority is claimed.

### 2. Center against the actual model before bounding

Let g0,g_z be the actual Riesz vectors for the origin and target readouts.
The inner product is conjugate-linear in its first entry. For the genuine
unit model e, assume d_e=<g0,e> is nonzero and set

    r_e(z)=<g_z,e>/<g0,e>,
    h_(e,z)=g_z-conj(r_e(z))*g0.

The SAME model appears on both sides of the exact identities

    <h_(e,z),e>=0,
    <g_z,p>/<g0,p>-r_e(z)=<h_(e,z),p>/<g0,p>.             (CE1)

The second identity applies when the actual denominator is nonzero. The
source derives that nonvanishing in the eigenmode consumer below. The complex
conjugation in h is essential. The old complete dual coefficient for g_z is
not automatically a coefficient for h_(e,z); it must be recomputed for this
centered readout, retaining its correlation with g0.

### 3. Multiplicative energy transport with no independent G term

Use the existing actual complex-linear domain maps iota,M and
q(f)=Re<iota(f),M(f)>. Assume symmetry and whole-domain shifted positivity,
unit k, ||e-k||<=eps<1 and q(e)<=nu. Suppose the already-justified new
complement satisfies q(f)>=kap||f||^2 on e-perp, kap>0. Suppose an old
FULL-residual certificate gives

    |<h,f>|^2<=C q(f) on k-perp, C>=0, and <h,e>=0.

For f perpendicular to e, choose

    beta=<k,f>/<k,e>,      v=f-beta e.

The candidate-overlap floor gives |beta|<=eps||f||/(1-eps); v is
k-orthogonal. Crucially <h,v>=<h,f> exactly. The previously proved positive
energy Young inequality gives, for any t>0,

    q(v)<=(1+t)q(f)+(1+1/t)|beta|^2 q(e).

Consequently

    |<h,f>|^2 <= A_t*C*q(f),
    A_t=(1+t)+(1+1/t)*(eps/(1-eps))^2*nu/kap.             (CE2)

This is purely multiplicative. It neither ignores the candidate readout nor
claims it is small: annihilation preserves the entire readout in the change
of hyperplane. No repaired trial's infinite action, model graph norm or new
exact inverse is invoked by this argument.

The original positive-form angle condition

    eps^2*(kappa/2+delta)<=kappa/4,   q(k)<=delta,

already derives kap=kappa/4 from the k-complement gap. With additionally
0<=eps<=1/2 and nu<=kappa/4, t=1 gives A_t<=4. Thus the source proves both

    q(f)>=(kappa/4)||f||^2,
    |<h,f>|^2<=4C q(f),    f perpendicular to e.           (CE3)

Whole-domain shifted positivity is essential. No unshifted all-window Weil
positivity is assumed. The older uncentered readout theorem remains valid;
one cannot delete its G term without changing and certifying the readout.

### 4. Derive the actual eigenmode anchor and normalized error

Let M u=lambda*u with u nonzero, 0<=lambda<kap and q(e)<=nu<kap, where e is
unit. The existing projective Rayleigh theorem and energy identity yield

    p_e=u/<e,u>=e+w,    w perpendicular to e,
    0<=q(w)<=nu,       kap||w||^2<=nu.

For b>0 assume the independently checkable squared origin margin

    b<=|<g0,e>|,
    ||g0||^2*nu<=kap*(|<g0,e>|-b)^2.                     (CE4)

Cauchy-Schwarz then gives |<g0,p_e>|>=b, so <g0,u> is nonzero as well.
Combining this conclusion with CE1-CE2 proves for the actual eigenvector

    |<g_z,u>/<g0,u>-<g_z,e>/<g0,e>|^2
       <= A_t*C*nu/b^2.                                 (CE5)

The raw eigenvector may have any nonzero complex phase and scale. Both
cancel algebraically. The hypotheses supply its eigenpair and spectral
placement; the theorem does not create the eigenvector.

The new moving-domain theorem uses CE3 and proves standard Mathlib
TendstoUniformlyOn for the ACTUAL ratio difference when, on the target set K,

    nu_j*Cbar_j/b_j^2 -> 0.                              (CE6)

The centered coefficient, actual gap/energy and squared origin margins
remain explicit. All Hilbert spaces and operator domains may vary with j.
There is no additional W*eps^2*|F(k)|^2/kappa rate in this bound. This reduces
the sufficient estimate to one correctly centered observable. It does not
prove CE6 for the unbounded arithmetic Weil/prolate family, and a bound on
the old uncentered C does not prove it either. Convergence of the SAME
normalized model functions to Xi(z)/Xi(0) is a separate final input.

### 5. New actual centered full-residual computation

The local interval consumer replays the archived complete-residual verifier
at c=3 on the unchanged finite candidate k and trial v. It uses the same
true aligned prolate model and inherited <1e-23 polynomial model-error cap.
It encloses the true ratio r_e(z) on the complete closed box of half-width
1/100000 around 20+i/4, using the inherited compact-support derivative bound.
All model and spectral premises retain their earlier paper/interval scope.

In the translated Fourier basis the origin representer is g0=sqrt(L)*e0,
L=log(3). Thus centering changes only the finite residual head. Every
nonzero exterior coefficient and the complete uncomputed tail stay exactly
the same, rather than being dropped or refitted.

For R=P_k(g_z-Mv), k real unit, and q=conj(r_e(z))*sqrt(L), the exact head
update is

    ||R-q*(e0-k0*k)||^2
       =||R||^2+|q|^2*(1-k0^2)-2 Re(q*conj(R0)).          (CE7)

The objective changes by -2 Re(r_e(z)*sqrt(L)*v0). Both the direct finite
sum and covariance formula were evaluated and compared. All omitted positive
and negative modes remain in the inherited exterior budget. The resulting
centered coefficient has upper endpoint about 107.800065579058, hence

    C_centered<108.                                      (CE8)

For the archived exact energy numbers use the positive-form gap parameter
s=1/100000 and CE2 parameter t=1/50000. Exact Fraction arithmetic gives
A_t<20001/20000. The true origin floor exceeds 805/1000. With b=39/50,
log(3)<11/10 and CE4, the derived p_e anchor is at least 39/50. The exact
rational guards give

    A_t*108*nu/(39/50)^2 < (9/10000)^2.                   (CE9)

Thus, conditional on the recorded actual domain/spectral/model identities,
the normalized true-mode to SAME prolate-model error is <9/10000 everywhere
on this box. This is a validation of the new centered-energy consumer. It
does not improve #5602's tighter 51/100000 result on a larger disk, produce
a new eigenvalue enclosure, or certify a physical unbounded-scale rate.

### 6. Formal source and validation boundaries

The existing GenuineModelDualTransport Lean/Scribe pair is extended by six
public theorems: model_centered_readout_identity,
annihilating_energy_dual_transport, positive_form_centered_readout_bound,
model_centered_projective_ratio_bound, model_centered_normalized_uniform_limit,
and prime_three_centered_budget. The prior ten declarations remain unchanged.
The new import uses the existing projective Rayleigh proof rather than
reproving the eigenmode identity. The last theorem checks only the exact
rational arithmetic in CE9 and the anchor budget, not its interval premises.

The generic readout theorem can consume the already-identified Fourier Riesz
vector from #5882. This extension does not redefine Fourier transforms or
copy its different unnormalized uniform-limit owner. The concrete analytic
identification, upstream spectrum and model records have not been reverified
by the new interval consumer. The actual unbounded-scale estimate remains CE6.

Executed local diagnostics: 600 exact complex centered positive-form cases,
600 elimination/readout identities, 600 multiplicative bounds, 600 four-C
bounds and 600 full-head covariance checks; 300 exact eigenpair ratio cases
and 900 complex phase/scale checks. All 600 missing-conjugation mutations
were detected. Negative controls retain the need for exact model annihilation,
a coefficient for the CENTERED readout, and an actual denominator margin.
The new full-residual centered consumer was replayed at 100 and 120 decimal
digits with the same rational conclusions. These are single-author checks.

Lean elaboration, kernel acceptance, transitive axiom reports and Scribe
emission have not been executed. The six statements remain logically reviewed
Candidate proof scripts. Exact and interval diagnostics are retained in the
reproduction package; the repository changes only the existing Lean, its
Scribe, and this theory volume. No synthetic scale sequence is presented as
an actual Weil experiment. No all-scale prolate rate or RH conclusion is claimed.

Primary references read in this continuation:

- https://arxiv.org/html/2511.22755v1 , Lemma 7.3 and Section 8.
- https://arxiv.org/html/2606.09096v1 , localized forms and domain distinctions.
- https://arxiv.org/abs/2607.23850 , primary abstract only; output-specific
  adjoint estimation as a methodological comparison, without its PDE premises.

[PR #5065] Pinned root observations 33969082693 and 33969495413 both failed. The first exposed obsolete finite-sum syntax and an unclosed mirror inverse simplification. The second verified the repaired mirror inverse with only standard axioms, then exposed a finite-window unfolding mismatch and a accidentally omitted second ZeroData binder introduced during the source repair. This revision explicitly unfolds `ZeroConfig.window` and restores that binder, without changing the intended theorem statements or admitting a placeholder. Compiler error recovery containing `sorryAx` is rejected as validation evidence. The new frozen source revision still requires its own observed successful root replay and independent required checks before any admission claim.

---

## [PR #6219] Canonical Li curvature and actual analytic zero-freeness

本节补入上一轮已经完成的数学追加。基准 dev 为 `55a96922002fdbf5644c47264702e325d0b475c9`，已有六份 Lean/Scribe 在本次补写前的远端提交为 `b14a5818d44baadbdb28367e97825548367babb5`。本轮复用已合并 #6172 的实际 `canonicalLiCoefficient`、`xiReading`、局部 Keiper–Li 展开和首系数正性。这里没有另造一份 Li 序列，也不主张经典生成函数方法的文献优先权。

### 1. 实际算术对象与局部关系

记仓内从实际 xiReading 高阶导数定义的系数为 λ_n，λ_0=0。令

\[
G(z)=\sum_{n\ge0}\lambda_{n+1}z^n,
\qquad F(z)=\xi\left(\frac1{1-z}\right).
\]

已合并来源给出零附近的实际局部展开

\[
G(z)=(1-z)^{-2}\frac{\xi'}{\xi}\left(\frac1{1-z}\right).
\]

由 ξ(1)=1/2 和连续性，先在零附近确认 F 非零，再由实际链式求导得到局部交叉相乘恒等式 F'=GF。没有在全盘预先引入 log F 或假定 ξ'/ξ 无极点。

### 2. 全索引增长控制与全域解析延拓

若实际系数满足对所有 n 的 |λ_n|≤Cn²，则对每个 0≤r<1，有

\[
\sum_{n\ge0}|\lambda_{n+1}|r^n
\le C\sum_{n\ge0}(n+1)^2r^n<\infty.
\]

候选真源 `AnalyticLogarithmicContinuation` 复用钉版 Mathlib 的标量 formal series 收敛半径 API，证明原系数之和在单位圆盘上全纯。实际 F 由 ξ 为整函数而全纯。F' 与 GF 都在全盘全纯，因此局部 F'=GF 经恒等定理延拓到整个连通圆盘。

注意延拓的对象是 F'−GF。即便正在排查 F 的零点，这个函数仍然全纯；不需要事先把 F'/F 延到全盘。

### 3. 解析零点阶数排除

假设 F 在盘内 z0 处为零。由于 F(0)=1/2，解析恒等定理排除了在 z0 无限阶为零。若其有限阶数为 k≥1，则 F' 的阶数为 k−1，而 G 全纯意味着 GF 的阶数至少为 k。全域等式 F'=GF 导致矛盾。

对于任意 Re(s)>1/2，取 z=1−1/s，有精确恒等式

\[
1-|z|^2=\frac{2\Re(s)-1}{|s|^2}>0,
\qquad (1-z)^{-1}=s.
\]

因此实际 xiReading 在 Re(s)>1/2 无零点。再复用既有 xi 与非平凡 zeta 零点的识别及右半条带反射归约，得到标准 Mathlib RiemannHypothesis。

`canonical_li_quadratic_growth_implies_rh` 保留全索引绝对二次界作为输入。它没有输入抽象 Li 判据、期望中的全局对数公式、RH 或无零点前提。该算术增长界本身尚未无条件证明。

### 4. 从实际 canonical 曲率矩阵导出所需界

定义 c_0=1，对于 n≠0 取

\[
c_n=\frac{\lambda_{|n|+1}-2\lambda_{|n|}+\lambda_{|n|-1}}{2\lambda_1}.
\]

这是实际 canonical 序列的实值偶延拓，λ_1>0 复用已有首系数定理。在原 Toeplitz 约定 T_N(c)_(jk)=c_(j-k) 下，从第 n 阶矩阵取索引 0、n 的主压缩，即

\[
\begin{pmatrix}1&c_n\\c_n&1\end{pmatrix}.
\]

若原矩阵正半定，向量 (1,1) 与 (1,−1) 给出 2+2c_n≥0 和 2−2c_n≥0。因此

\[
|\lambda_{n+1}-2\lambda_n+\lambda_{n-1}|\le2\lambda_1.
\]

对一般实序列 L，假设 L_0=0、|L_1|≤a，且全部二阶差分绝对值≤2a。第一次归纳得到 |L_(n+1)−L_n|≤a(2n+1)，第二次归纳得到 |L_n|≤an²。系数可以带符号。

由此得到候选端点 `canonical_curvature_posSemidef_implies_rh`：全部实际 canonical 曲率 Toeplitz 矩阵正半定蕴含标准 RH。共同 Herglotz 测度、抽象 Li 判据、期望中的递推和零点测度识别不再是该端点的额外输入。

这仍然没有证明全部实际矩阵正半定。单项 |c_n|≤1 对一般序列也不能反推全矩阵正性。本轮采用正性到二点界的方向，然后使用这一个实际 canonical 序列已有的解析展开。

### 5. 与概率支线及剩余任务

#6114 的 `normalized_curvature_quadratic_bound` 给出一般概率重建序列的二次包络。本轮 `canonical_li_probability_envelope_implies_rh` 消费这个包络在 L=canonicalLiCoefficient 时的特化。新分支从已含 #6172 的 dev 创建，没有复制未合并概率模块或处理旧分支冲突。

当前是 canonical 增长或全阶曲率正性到 RH 的前向解析连接。没有证明 RH 到完整 canonical 曲率正性的反向，也没有完成无条件全阶算术正性。失败 RH 的反证结论仅说明存在某个失败矩阵阶数或越过任何给定二次包络的系数，不提供统一检测截止阶数。

三个 Lean 模块有配套 Scribe 候选。没有执行 elaboration、内核接受、公理闭包检查或 Scribe emission。有限有理数检查检验代数、递推、Möbius 几何和零点阶数的有限 jet。它不验证全索引 canonical 算术前提，也不能替代无限域解析证明。

上一轮交付包内的标准库精确诊断现已重放：119 个多项式几何尾式、86 组带符号二阶差分序列、180 个有理复数 Möbius 往返、216 个复 Toeplitz Gram 恒等式及 96 个有限零阶障碍。重放是作者自检，不是独立复核或 Lean 内核证据。源码与该数学追加的远端身份另外通过 commit/blob 回读核对。

- Existing owners: `WeilInfiniteComplementLeakage`, `WeilArithmeticCouplingJet`, `WeilEvenDualStencil`; actual #6029 and #6204 sources at the blobs above.


---

## [PR #5602] UNIFORM_SCHUR_CERTIFICATE_ACROSS_PRIME_THREE

# 2026-09-07：穿过素数 3 激活点的完整区间 Schur 证书与奇块三次抑制

本节的两个源码为 `D5/S3/Weil/ZetaBridge/WeilPrimeThresholdParity.lean` 及其同名 Scribe。数值源为 `research/weil_ground_mode/certify_prime3_scale_interval.py`，独立表达式诊断为 `test_prime3_scale_interval.py`。下面给出的有限区间数字已在 70、100 位定向区间精度执行；Lean elaboration、Scribe emission 和传递公理报告没有执行。完整 Fourier/闭形式实现、Neumann 比较和以下无穷 Schur 推导仍为纸面桥，不能视作端到端内核结果。

本次对一个非退化参数区间直接认证，而不从上节的最坏情形 resolvent 模量逐步传播：

\[
I_*=[a_*-2\cdot10^{-8},a_*+2\cdot10^{-8}],\qquad a_*=\tfrac12\log3.
\tag{PT1}
\]

在整个区间中，明确的同一 Fourier 系数候选族满足 q_a(k_a)<1.2e-6，整个候选正交形式域满足 q_a(f)>=6e-6||f||^2。因此真实最低模态简单、偶，并有统一间隔大于 4.8e-6。此数值证书不假设旧的数值谱间隔或最低值包络。区间仍很窄，尚未认证这里的真模态/prolate 误差，也未成为无界尺度证明。

## 1. 当前研究背景与实际复用

CCM, *Zeta Spectral Triples*, arXiv:2511.22755v1，Section 8 将真实最低模态的单纯偶性与充分精确的 prolate 比较分开。这里直接处理前者在一个含激活点的参数区间上的完整证书，不以增加孤立数值点代替它。

本轮读取 #5895 在 `83f2bd4c2059bbe555447a594abc492fb16f6452` 的实际 `GenuineModelDualTransport.lean`，特别是正移位形式的能量 Young 不等式及 `positive_form_complement_coercivity`。该工作处理同一形式中候选方向的改变；本节处理形式随 a 改变，因此不复制其通用论证，也不将未合并源码隐式导入。

读取 loning 研究链 #6171 的 `Mertens/Third.lean`，blob `435484ecbfc11097a057d6b435045728a6e41f01`。其标量 Mertens III 对 Robin/Gronwall 研究有用，未作为本节 s=1/2 平移作用的范数估计。上节 5040 的首缺失素数 11 提醒了普通范数跳变；当前区间同样跨过素数 3 的真实激活。

交付期间，同一研究分支并行推进到 `4804c4020d7d9f165a2e2683c42b01e3d47a8be4`。实际读取其 `WeilPrimeActivationEdge.lean` 和 `certify_prime3_scale_schur.py`：前者处理偶块 rank-one 主项和零 trace 偶模板的五次界，后者记录 N=128、半宽 1e-8 的证书。本节的奇轮廓三次界与其互补；数值部分借鉴保留 Gram 方向性的 Young 处理，但重新独立计算 N=64、半宽 2e-8 的全部加权 Schur 数据。没有把初步完成的半宽 1e-9 证书重复报告为最新前沿，也没有将并行结果文件作为当前证明输入。

Dusson-Sigal-Stamm, arXiv:2008.10871 的 Feshbach-Schur/Fourier 谱离散分析提供经典方法背景。本节所有 Gamma、prime、pole 和高补空间估计均按同一个 Weil 算子推导，不移植 Schrödinger 正则性假设。原 `certify_prime3_refined.py` 以 SHA-256 `8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0` 固定，仅复用其算术区间例程和明确候选数据，不执行其旧谱结果作为输入。

## 2. 同一个实参数算术矩阵，激活项精确表示

令 L=2a，使用原基 V_n(x)=(-1)^n exp(2pi*i*n*x/L)/sqrt(L)，窗口外零延拓。经 J_a 酉伸缩，其基在 [-1,1] 上固定为 (-1)^n exp(i*pi*n*y)/sqrt(2)。固定候选整数系数除以其精确范数后定义 k_a；没有把未知 ground 当作 k_a。

在 (PT1) 上，log2<L<2log2，素数 4 及更大 prime powers 尚未进入。定义实际归一化交叠长度

\[
h_2=2-2\log2/L,\qquad h_3=\max(0,2-2\log3/L),\qquad
w_p=\log p/\sqrt p.
\tag{PT2}
\]

在边界符号和实际对角中，两个素数的贡献分别为

\[
s^{\rm prime}_L(n)=\sum_{p=2,3}w_p\sin(\pi n h_p),\qquad
A^{\rm prime}_{nn}=-\sum_{p=2,3}w_ph_p\cos(\pi n h_p).
\tag{PT3}
\]

这是原 -w_p sin(omega_n log p) 与 -2w_p(1-log p/L)cos(omega_n log p) 的精确格点相位改写；h_p=0 时两项均为零。端点等号是 L2 零测作用，(PT3) 跨阈值有效。程序对 L 的整个闭区间计算正部分包络，不将抽样或中心条件当作区间条件。

完整边界符号为原 pole、无限 Gamma 边界级数与 (PT3) 的和，omega_n=2pi n/L。完整对角使用同一 digamma、trigamma、指数修正、pole 及 (PT3)。Gamma 指数修正保留前 32 项并显式包住无限尾。新的 sine 例程在选择整数周期后先严格检查余量位于 (-4,4)，再以 63 次 Taylor 多项式和 4^64/64! 的明确尾界覆盖整个参数区间；浮点周期选择不提供正确性假设。有限工作精度与 bulk binary64 符号包络的准确度分开：每个 bulk 运算都向外舍入，最终各项误差继续进入矩阵证书。

## 3. 先做实际奇偶合并，再产生区间 Gram

对原 a_mn=(s_n-s_m)/(pi(m-n))，s_-n=-s_n。实际偶、奇配对列是

\[
C^+_{mn}=\frac{2(ns_n-ms_m)}{\pi(m^2-n^2)},\qquad
C^-_{mn}=\frac{2(ms_n-ns_m)}{\pi(m^2-n^2)}.
\tag{PT4}
\]

新 Lean `arithmetic_parity_pair_columns` 从原 `couplingColumn` 展开证明两式，使用已证明的原符号奇性，并先排除全部分母碰撞。Lean 的 c 参数仍按原 owner 为自然数；实 L 的算术表达及其奇性在本节独立按同一公式解释，没有把 c 自然数定理冒用成实尺度实现。

在正交归一 parity 基 E_0=V_0、E_n=(V_n+V_-n)/sqrt2、O_n=(V_n-V_-n)/sqrt2 中，正高编号之间的矩阵元素恰是 (PT4)，偶零列为 -sqrt2*s_m/(pi*m)。偶低块的 n>0 对角是 A_nn-s_n/(pi*n)，奇低块是 A_nn+s_n/(pi*n)。奇扇区乘整体 i 不改变矩阵或能量。

这些相消在区间量化之前完成。实际高空间的正负编号已合并为一个正交 parity 坐标，因此后续不得再重复乘二。程序对每个 parity 块分别形成全体 65<=m<=32768 的 Gram，并保留参数区间造成的系数半径。

## 4. 新 Lean 的另一个具体结果：奇低块的三次激活能量

在固定空间采用实奇基 (-1)^n sin(pi*n*y)，其范数为 1。对有限复系数 v_n，记 F(t)=sum v_n sin(pi*n*t)。当新平移 s=2-h、0<=h<=1，左、右条带的轮廓分别为 F(t) 和 -F(h-t)。所以实际 Weil 的负对称 prime 项恰为

\[
Q^-_{w,h}(v)=w\int_0^h
\{\overline{F(t)}F(h-t)+\overline{F(h-t)}F(t)\}\,dt.
\tag{PT5}
\]

新 `oddPrimeActivation` 先独立定义这个完整复积分。其 integrand 是连续函数，所有交叉项保留。由 |sin(pi*n*t)|<=pi*n*|t|，令 B=sum n|v_n|，则积分内模长至多 2pi^2 B^2 t(h-t)。有限 Cauchy-Schwarz 和精确多项式积分给出

\[
\boxed{\|Q^-_{w,h}(v)\|\le
\frac{w\pi^2h^3}{3}
\left(\sum n^2\right)\left(\sum|v_n|^2\right),\qquad w,h\ge0.}
\tag{PT6}
\]

`odd_prime_activation_cubic_bound` 保存 (PT6)，不接收边界值、组装后能量或积分值的假设。其积分表达对任意非负 h 都成立；与两个不交物理条带的识别使用 h<=1，正编号基下的系数平方和是实际 L2 范数。

(PT1) 内 h3<=7.281914e-8，取 S={1,...,64} 后，对实际 w3 的 (PT6) 右侧系数再作定向检查，得到低奇块的新增素数能量范数上界小于 1e-16。这里是该有限块的预算，完整 Schur 计算仍使用未粗化的矩阵。

(PT6) 的常数随有限频率集合增长。因此它与上一节全空间范数跳变、参考形式仅有对数模量完全相容。数值证书仍使用完整实际矩阵元素，没有用粗的 h^3 上界代替高低耦合计算。

## 5. 整个高补空间的统一下界

令 L_+=log3+4e-8、n0=65、w=w_2+w_3。整个参数区间内，每个可见非零 prime 平移在固定空间的位移大于 1，其对称块范数至多 1；故全高空间 prime 债保守使用完整 w，绝不以 h3 很小为理由省去 w3。

偶空间沿用原 Neumann Gamma resolvent 完成式及偶 pole 非负性。对所有高偶系数 y_n，得到 q_a(y)>=sum d^+_n |y_n|^2，其中

\[
d^+_n=\log(n/L_+)-L_+/(\pi n)-w.
\tag{PT7}
\]

奇空间的独立全高界可以从原 Γ 对角和离散 Hilbert 交换子直接核对。首先，digamma 调和极限与 t/(t^2+y^2) 的积分比较给出 Re psi(x+iy)>=log|y|-1/|y|，x>0、y!=0；误差由该函数总变差不超过 1/|y| 控制。因而 gamma(omega_n)>=log(n/L)-L/(pi*n)。

Gamma 对角相对乘子值的边界修正模长至多 L/(2pi^2*n^2)+1/(4n)。这是用 (2/L)sum 1/(b_j^2+omega_n^2) 包住完整边界级数，再将递减求和与积分比较得到。高空间 Gamma 边界符号满足 |sGamma_n|<=pi/4+1/|omega_n|；标准离散 Hilbert 核 1/[pi(m-n)] 的 l2 范数为 1，所以其交换子范数至多 pi/2+L_+/(pi*n0)<2。这个最后严格界在程序中执行检查。

奇 pole 的负范数为 2sinh(L/2)-L。合并并作安全的 n0 统一放宽，得到整个奇高空间下界

\[
d^-_n=\log(n/L_+)-2-\frac{2L_++1}{\pi n_0}
-\frac{L_+}{2\pi^2n_0^2}-w-\{2\sinh(L_+/2)-L_+\}.
\tag{PT8}
\]

这些是整个高子空间的形式不等式，不能只从逐对角值推出。有限高组合通过已有共同闭形式域的稠密性推广；没有遗漏 Gamma 非对角项。每个 dyadic shell 使用其首编号的经过检查的有理下界。n=65 的偶、奇下界分别为 `24750975/8388608` 与 `927117/1048576`，均远大于本次 tau=6e-6。

## 6. 全无限 Schur 上预算和严格区间合同检查

令 tau=6/10^6。对每个 parity，低高块为 C、高块为 H。由 (PT7)-(PT8)，H-tau>=diag(d_n-tau)>0，所以 Schur 扣除项满足

\[
C^*(H-\tau)^{-1}C\preceq C^*\operatorname{diag}((d_n-\tau)^{-1})C.
\tag{PT9}
\]

先对 65..32768 的实际区间 C 取 dyadic 中点 X，分母 2^44，逐项误差半径分母 2^60。每个 shell 的 X^*X 用有溢出 guard 的整数算法精确算出，误差半径平方和使用任意精度整数。设 D 是正的 shell 权重，e>=||D^(1/2)(C-X)||_F^2。取明确正有理数 theta=1/200，逐向量应用 Young 不等式得到 C^*DC<=(1+theta)X^*DX+(1+1/theta)e I。程序因此保留 201/200 倍的原 Gram 方向性，只增加 eta=201e 的单位阵预算；theta 的额外正代价也完整扣入 Schur 补。中点和误差都是从当前整个参数区间重新计算，不能省去任一项。

m>32768 的所有模式使用完整边界符号包络 B=4，其实际有限 prime、pole、Gamma 上界在程序中重查。原二阶耦合展开保留四个矩，配合正负 parity 给出秩至多四的正尾预算，另加 `2/10^12` 倍单位阵的余项。该余项逐次检查大于 16B^2 N^4(2N+1)/[pi^2(1-N/M)^2 M^5]。所有无穷平方级数由积分比较包住，没有更远的终端截断。

合并 shell 与无限尾后的矩阵 W_+、W_- 是 (PT9) 的上界。偶低块另加实际未归一化候选 vv^*，奇块不加。最终需要同时确认

\[
A^+_{\rm low}-W_+-\tau I+vv^*\succ0,\qquad
A^-_{\rm low}-W_--\tau I\succ0.
\tag{PT10}
\]

原坐标的 interval LDL 曾无法判定，不能由此推断负特征值。程序用浮点 Cholesky 仅提出坐标变换，再舍入成分母 2^32 的精确 dyadic 方阵 R。对完整区间矩阵直接计算 R^T A R，再作严格定向 LDL。正定 R^T A R 本身蕴含 R 单射，方阵即双射，所以无需相信浮点可逆性或中点 Cholesky 的判断。输出的 pivot 只是合同后计算诊断，不是原算子的特征值下界。

## 7. 一次认证覆盖整个参数区间

70 位和 100 位运行分别确认 (PT10)，并在同一个区间包络中确认明确归一化候选 k_a 的 Rayleigh 上界。结果为

\[
\boxed{q_a(k_a)<U=\frac6{5\cdot10^6},\qquad
f\perp k_a\Longrightarrow q_a(f)\ge\tau\|f\|^2,
\quad\tau=\frac6{10^6},\quad a\in I_*.}
\tag{PT11}
\]

实际候选 Rayleigh 的区间显示约为 [-9.5152736e-7,1.0637090e-6]，因此 U 留有裕量。偶加秩一证书在候选正交方向上严格消去该秩一项；奇扇区整体高于 tau。由已有同一 Friedrichs 实现的紧 resolvent 与 min-max，

\[
\boxed{\lambda_0(a)<U<\tau\le\lambda_1(a),\qquad
\lambda_1(a)-\lambda_0(a)>\frac3{625000}.}
\tag{PT12}
\]

最低特征值单纯；若最低向量为奇，则与奇扇区下界矛盾，故为偶；它与 k_a 的内积也不能为零。这是实际一族窗口的 simple-even/gap 证书，不是某个有限子矩阵的本征值图。此轮没有宣称 A_a 全空间非负，没有假设旧的数值 ell、U、T，也没有把新的 k_a 认作 prolate 模型。

旧的通用形式连续性半径是 2^-9259287090。本次直接区间证书覆盖半宽 2e-8，不需要沿那个极小半径做数十亿次传播。即便如此，当前新区间仍很窄，不能称为实用的无界尺度扫描。证明更大跨度和控制真实模态/prolate Fourier 误差仍然是下一项。

## 8. 复验、形式化范围和未解决部分

最终交付数值源 SHA-256：`0bbadda0977f11052c7c492d2d44f958f6318b89954587486edc4bc6db796688`。诊断源 SHA-256：`5467e6f5b50395ebcfb033e5d4f92949458f8a9ce953c784fca4814c03c19257`。本次补交只删除了若干 Python 注释，并纠正 Scribe 中过时的区间半径说明；程序执行逻辑未改，最终版本重新在 70、100 位精度运行通过，诊断也重新运行通过。结果 JSON 的排版不作为数值精度证据。

诊断通过三个符号恒等式、800 个精确 parity 列等式、120 个精确 Gram 半径例子、36 个独立原符号参考值、45 个原对角参考值和 72 个原 prime 相位比较。另有 20 个直接物理奇轮廓积分与 (PT5) 的对照。后面的点值与求积使用非定向高精度，仅为另一表达式的诊断，不是 (PT11) 的区间证明。其 Gamma 指数参考尾小于 3.28e-248。三个不定/奇异矩阵均被严格 LDL 拒绝。

Lean 的三个公开定义/定理有三个对应 FromLean Scribe 项。区间认证器复用原算术例程的固定源码，新的中点 Cholesky 只产生待验证坐标；它不运行 eigensolver、不使用 zeta 零点、不用旧的数值谱结论，也没有把 CI 或 Scribe 状态计为数学证据。不存在已执行的新 Lean 内核、传递公理或独立作者审稿声明。

本节推进的是：保留实际 parity 抵消、全高块下界和低高耦合后，可以跨过真实素数激活点直接得到一个连续参数族的完整余维一强制性。剩余任务是将该区间方法与真实 prolate 族和既有能量对偶读出联合，扩大跨度并控制归一化 Fourier 差。无界尺度上的 Xi 极限或 RH 未由本节建立。

参考：

- Connes, Consani, Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, Sections 3-4 and 8. https://arxiv.org/html/2511.22755v1
- Dusson, Sigal, Stamm, *Analysis of the Feshbach-Schur method for the Fourier spectral discretizations of Schrödinger operators*, arXiv:2008.10871. https://arxiv.org/abs/2008.10871
- NIST DLMF 5.7.6, digamma partial fractions; mathematical constants and tail identities retain the pinned arithmetic source conventions. https://dlmf.nist.gov/5.7.E6
- Actual #5895 `GenuineModelDualTransport.lean` at `83f2bd4c2059bbe555447a594abc492fb16f6452`; loning research #6171 `Mertens/Third.lean`, blob `435484ecbfc11097a057d6b435045728a6e41f01`.
- Parallel #5602 source at `4804c4020d7d9f165a2e2683c42b01e3d47a8be4`: `WeilPrimeActivationEdge.lean`, blob `5cd36bfeef88311e1f5e6c140fc11e52b16e8881`; `certify_prime3_scale_schur.py`, blob `496333f97d20a6898d47f848a2abd839249e9207`.

上一轮交付包内的标准库精确诊断现已重放：119 个多项式几何尾式、86 组带符号二阶差分序列、180 个有理复数 Möbius 往返、216 个复 Toeplitz Gram 恒等式及 96 个有限零阶障碍。重放是作者自检，不是独立复核或 Lean 内核证据。源码与该数学追加的远端身份另外通过 commit/blob 回读核对。

---

## [PR #6219 continuation] Canonical disk equivalence and radius-dependent coefficient obstruction

日期：2026-09-07。首先恢复上一轮缺失的理论追加：`b00b74c874b7fe6afbd975182d660e034ce1072a` 将已完成的 canonical 增长到实际 ξ 无零点推导补入本卷，87 行新增、零删除。六份既有 Lean/Scribe 的完整远端内容已重新回读。恢复并没有改变这些候选证明的编译状态。

本轮继续使用 merged #6172 的同一 canonicalLiCoefficient、liGenerator 和 generator_taylor_coefficient。新扫描 dev 为 `65457467c879007d1e91f71ef861a4d3f7d462c3`；canonical 来源 blob 仍为 `0fb04eb79f87389016b51af25cdf6078d5616b7c`，当前 v4.3 规范 blob 为 `473d684ffda13d291c7df78f0edd8d4922550be6`。跨作者的相关 PR 与默认分支检索未找到可直接替代本轮全盘反向端点的新实现；工程类命中未作为数学来源。未将空检索结果解释为全库不存在。

### 1. 从 RH 导出实际 canonical 全盘展开

令 λ_n 是既有导数定义的 canonical 系数，F(z)=xiReading((1-z)^(-1))，G 使用既有 liGenerator。本轮 `CanonicalLiDiskEquivalence` 先证明 |z|<1 蕴含 Re((1-z)^(-1))>1/2。标准 RH 与既有 xi/nontrivial-zero 识别给出 F 在全盘非零。因此此方向下，实际 G 在全盘全纯。

Mathlib 钉版 `db584cd6d46c92f209a44c0f1c829460d327499d` 的 Taylor 定理提供 G 的全盘展开，#6172 已证明的全阶系数恒等式将它识别为

\[
G(z)=\sum_{n\ge0}\lambda_{n+1}z^n,\qquad |z|<1.
\]

`rh_canonical_li_global_expansion` 保留实际 HasSum。复数是有限维实范数空间，钉版 `summable_norm_iff` 将其无条件可和性转成绝对可和性；这里没有把任意条件收敛级数误当成绝对收敛。

结合上一轮通过 F'=GF 和零点阶数排除得到的反向，`rh_iff_canonical_li_disk_summable` 证明

\[
\mathrm{RH}\iff
\forall r\in[0,1),\quad\sum_{n\ge0}|\lambda_{n+1}|r^n<\infty.
\]

`rh_iff_canonical_li_global_expansion` 同时将实际全盘 HasSum 等式与 RH 等价起来。这个反向不使用 RH，也没有外加抽象 Li 判据。本轮闭合的是全盘收敛判据的两向，并非 RH 与完整 canonical 曲率矩阵正性的两向。

### 2. 全半径加权包络也是精确等价条件

`CanonicalLiRadiusObstruction` 从 RH 下的绝对和构造每个半径的常数 C_R，证明

\[
\mathrm{RH}\iff
\forall R\in[0,1),\ \exists C_R\ge0,\ \forall n\ge0,
\quad |\lambda_{n+1}|R^n\le C_R.
\]

常数允许依赖 R。反向在任意 r<1 与 1 之间选择 R，保留精确恒等式

\[
|\lambda_{n+1}|r^n=(|\lambda_{n+1}|R^n)(r/R)^n
\le C_R(r/R)^n,
\]

再用几何级数得到所需绝对收敛。等价的指数表述是：对每个 q>1 存在有限 C_q，使全部 |λ_(n+1)|≤C_q q^n。Lean 公共端点采用上面的加权半径表述，没有另外新增一个同义指数谓词。

### 3. 指定实际零点导致每个尾段中的增长障碍

本轮还把上一轮的全索引增长条件局部化到任意正半径 R≤1。若从某一阶起有 |λ_(n+1)|R^n≤C，Mathlib 的 `le_radius_of_eventually_le` 仍然保证相同 scalar series 在 |z|<R 解析。有限个初始系数不会改变这个结论。将旧的局部交叉相乘等式限制到这个圆盘并延拓，得到实际 F 在该盘无零点。

因此对一个假设给定的实际 ξ 零点 ρ，记 z_ρ=1−1/ρ。若

\[
|z_\rho|<R\le1,
\]

则 `xi_zero_forces_weighted_tail_escape` 给出

\[
\forall N\in\mathbb N,\ \forall C\in\mathbb R,\ \exists n\ge N,
\qquad |\lambda_{n+1}|R^n>C.
\]

这是每个尾段无界，强于某个系数超过一个给定二次界。若 |z_ρ|<1，可以选 |z_ρ|<R<1，故系数在任意尾段都会超过任意给定倍数的 R^(-n)。没有证明每一项最终都大，也没有给出第一次越界的索引上界。零点的存在始终是条件，没有假定或声称已找到离线零点。

严格半径条件不可删除。有限诊断的模型 F(z)=(1-z/a)^m 有 G(z)=−m/(a-z)，其系数为 −m/a^(n+1)。在 R=|a| 时，加权模长恒等于 m/|a|，可以保持有界；零点此时在边界，不在 theorem 的开盘结论内。

### 4. 读出半径对应真实 s 平面的位置，而非只对应高度

令 ρ=β+iγ，有精确代数式

\[
|1-1/\rho|^2=1-\frac{2\beta-1}{\beta^2+\gamma^2}.
\]

因此控制 R 只排除满足 |1-1/s|<R 的零点。对于 0<R<1，这在原 s 平面等价于

\[
\left|s-\frac1{1-R^2}\right|<\frac{R}{1-R^2}.
\]

最后一个圆盘形状是本轮精确代数诊断和纸面解释，不是额外具名 Lean 定理。Lean 零点端点直接保留完整复数及其真实 Möbius 像。

这个关系解释了为什么仅有限阶或固定读出半径不能直接得到全局 RH：每个半径控制一个确定区域，而全盘判据需要任意接近一的半径及各自的全索引界。黄金固定周期读出导致的层数丢失也不会由这一解析等价自动消除。

### 5. 文献定位、实际复用与验证范围

Li 系数、增长与 Weil 形式的联系已有成熟文献，例如 Lagarias, *Li Coefficients for Automorphic L-Functions*, Annales de l'Institut Fourier 57 (2007), 1689–1740, arXiv:math/0404394v4。Suzuki, *Li coefficients as norms of functions in a model space*, arXiv:2301.05779v2 (2023)，研究具体范数表示与 RH 判据。当前主要记录及摘要已核对；本轮不冒领这些经典解析关系的优先权，也未宣称重新审定两篇论文的全部证明。贡献是沿已合并 canonical 定义完成可组合的实际函数证明端点和尾段障碍。

两份新 Lean 共 321 行、15 个公共定理，配套两个 Scribe 共 84 行，15 个 `StatementSource.FromLean()` 绑定全部匹配。四份代码通过字符串/注释感知的括号检查；新源码没有自定义 axiom、sorry、admit 或 native_decide。没有 Lean、Lake 或 dotnet 可执行程序，因此没有执行 elaboration、内核接受、传递公理报告或 Scribe emission。旧候选依赖也不因新增消费者而获得新的验证状态。

seed 20260907 的 Fraction/有理复数重放通过 90 个有限解析多项式模型、3240 项 F'=GF 有限 jet 恒等式、1080 项精确几何余项、6480 项加权半径比较、864 项指定尾段越界实例、240 项 Möbius 往返、720 项原 s 平面圆盘测试、21 项临界线边界以及 90 项边界零点有界包络。五个负对照保留严格半径、全索引而非有限前缀、正半径、非零初值及完整复数零点位置等条件。完整重跑与结果文件逐字节一致。诊断是作者的第二实现，未计算真实 zeta 零点或 canonical 全序列，也不是独立审稿或 Lean 抽取代码。

诊断源码 SHA-256：`1912d84a162e5328ac588487d17d0cc163265b26342d18dc4208aa27d1d48fad`；结果 SHA-256：`c197242b343bded46173e6286a745266d4fec049f769ecfdc0091481169f3662`。上一轮交付 ZIP 内的原诊断已另行重跑，JSON 与原包逐字节一致。研究产物保持在本 PR 的 Lean、配套 Scribe 和本卷追加；没有修改 CI 或冻结登记。

- https://arxiv.org/abs/2607.23850 , primary abstract only; output-specific
  adjoint estimation as a methodological comparison, without its PDE premises.

## [PR #5895] INVARIANT_EVEN_SECTOR_AND_COMPLETE_CENTERED_DISK_BOUND

### 1. Verified prior delivery and the specific next target

The preceding centered-readout work was reread at remote commit
44a831a15abe4d00268d973976101e0d62d66fd2. Its Lean, Scribe and existing
RH theory blobs match the delivered archive. The present increment preserves
that content and continues the actual lowest-Weil-mode/prolate comparison in
Connes, Consani and Moscovici, Zeta Spectral Triples, arXiv:2511.22755v1,
Section 8. The explicit-model limit and actual-mode approximation remain
separate. The moving-scale rate has not been proved by the finite result below.

The same paper's Section 5.2, Lemma 5.2, identifies the matrix involution
V_n -> V_-n and its commutation with the truncated Weil matrix. The actual
domain-level reflection and form-core realization remain required when this
symmetry is used for the infinite operator. Suzuki, arXiv:2606.09096v1,
provides the localized form/Friedrichs-domain context. These are classical
invariant-sector and variational arguments; no priority claim is made.

The latest #5602 sources were read at
5b1c54e84706acdca64e2ec042b51a5d52c5fcea. Its new full-space scale certificate
covers |a-log(3)/2|<=1e-8 with candidate-complement floor 1/200000. Its
prime-activation, Gamma and complete Schur construction is the arithmetic
reference for the independent stronger EVEN-sector test here. Loning's
#5326 and #5296 were inspected at PR-description scope for the importance of
preserving channels and independently certifying boundary readouts. Their
theory descriptions are not used as arithmetic spectral hypotheses.

The preceding centered coefficient paid the old whole-space gap even though
the candidate, trial and centered Fourier readout are even. That can overpay
for a direction invisible to the observable. We therefore certify an actual
even candidate-complement floor and prove exactly when its readout estimate
can be used in the existing whole-space centered transport.

### 2. Exact invariant-sector energy and readout lifting

Let iota,M:D->H be complex-linear maps on an actual linear domain. Let J be
a linear involution on D and U a compatible complex-linear Hilbert isometry:

    J^2=I,  iota(Jf)=U(iota(f)),  M(Jf)=U(M(f)),
    <Ux,Uy>=<x,y>.

Write q(f)=Re<iota(f),M(f)> and

    f_+=(f+Jf)/2,       f_-=(f-Jf)/2.

Domain linearity and inner-product invariance prove

    Jf_+=f_+,  Jf_-=-f_-,  q(f)=q(f_+)+q(f_-).             (IS1)

The identity needs no positivity or gap. If Jk=k and Ug=g, then

    <iota(k),iota(f_+)>=<iota(k),iota(f)>,
    <g,iota(f_+)>=<g,iota(f)>.

Suppose an actual dual certificate on the invariant sector gives

    |<g,iota(v)>|^2<=C_+ q(v),
    Jv=v, v perpendicular to k, C_+>=0.

If q is nonnegative on the opposite sector, then for every f perpendicular
to k, IS1 implies

    |<g,iota(f)>|^2<=C_+ q(f).                            (IS2)

No positive opposite-sector gap appears in this lift. Its nonnegative
SHIFTED energy remains essential. The conclusion concerns the readout,
not a stronger full-space coercivity estimate. Dropping invariance of g,
commutation of the action, or opposite-sector nonnegativity invalidates the
argument; all three have explicit negative controls in the local diagnostics.

For the arithmetic application J is reflection, M=A-ell, and the existing
whole-space lower bound at a=log(3)/2 supplies shifted nonnegativity. The
centered even Riesz vector is invariant because both its Fourier component
and origin component are invariant. The original actual-mode evenness and
Fourier/kernel identification still have their existing analytic scope.

### 3. A complete uniform even Schur certificate

The new verifier independently constructs the actual matrix and exterior
couplings on the whole interval

    |a-log(3)/2|<=1/100000000,    L=2a.                    (IS3)

It uses N=128 retained positive/negative Fourier modes and explicitly sums
both exterior signs through M_cut=8192. The prime-3 term is absent on the
left of activation and present on the right. The diagonal overlap positive
part and the column sine hull retain both cases, including the vanishing
activation value. Gamma, pole, prime-2 and prime-3 contributions remain.
The length enters interval expressions, not a collection of sampled scales.

The original finite positive Gamma resolvent sum gives a uniform full
high-complement floor beta>1; its computed lower endpoint exceeds
1.009070267917372763. The near coupling is enclosed by a dyadic matrix and
an exact two-sided Frobenius error. Young's inequality with parameter 1/20
bounds its full Gram. The complete paired second-jet Gram and its nonzero
far remainder pay every mode beyond 8192. No weighted pairing is substituted
for this Gram or for an unweighted residual norm.

Let G_upper bound the entire low-to-high coupling Gram, and let c be the
same padded finite candidate coordinate vector. On the retained even basis,
the verifier certifies positive definiteness of

    A_low - T_+ I - G_upper/(1-T_+) + c c*,
    T_+=1/1000.                                         (IS4)

The basis is e_0 followed by e_n+e_-n, without an unrecorded unit rescaling.
The rank-one term vanishes on the candidate complement. The complete Schur
argument therefore gives, under the original Fourier/core and high-complement
identifications,

    q_a(f)>=||f||^2/1000
    for all even f perpendicular to the transported candidate,
    at EVERY a in IS3.                                  (IS5)

This is an even candidate-complement bound. The odd sector and the full
candidate complement are not assigned the threshold 1/1000. This increment
also does not prove the historical positive ell is a lower bound throughout
IS3. The normalized readout computation below uses that inherited ell only
at the central physical window a=log(3)/2.

Floating eigenvalues only propose congruence coordinates. Each matrix entry
is enclosed about a 44-bit dyadic center, a 32-bit dyadic congruence is
applied with exact integers, and an exact Gershgorin lower bound certifies
positivity. Its positive bound is

    322613388022726078131097863949363 /
      324518553658426726783156020576256.

This number belongs to the CONGRUENT matrix; it is not reported as the
original operator's gap. The signed radix-20 integer Gram calculation has
explicit overflow guards and was separately compared with object-integer
multiplication on 80 matrices. Both 90- and 120-digit sector runs passed.

### 4. Recompute the actual centered coefficient with the relevant gap

At a=log(3)/2 retain the exact historical ell and the SAME candidate, trial,
genuine model e, and centered readout h_(e,z) from the preceding appendix.
The original complete residual is replayed, including its covariance-corrected
finite head and every exterior mode. The model approximation and original
whole-space spectral records remain inherited analytic premises.

The even trial and even residual can use

    kappa_+=1/1000-ell >999/1000000.

The actual upper data are

    J<=1173667110482754901/10^18,
    R^2<=1273652293764969/10^18.

The new complete coefficient is

    C_+<=J+R^2/kappa_+
       <=100239558744515453640283630281893 /
           40957747186193000000000000000000
       <49/20.                                         (IS6)

It is about 2.4473894594062675. The same centered residual with the old
whole-space gap gave about 107.800065579058. This compares two sufficient
coefficients, not the unknown optimal coefficient or actual Fourier error.
The residual did not become smaller and no high mode was dropped.

The energy-dual theorem is applied on the invariant linear domain. IS2 then
lifts this readout inequality to the whole candidate complement. Crucially,
the OLD global model-recentering factor and origin certificate are retained.
We never substitute T_+ into a theorem requiring full-space coercivity.

### 5. Pay variation on the full complex disk

For a unit genuine model e, nonzero d_e=<g0,e> and any g,g', direct algebra
and Cauchy-Schwarz give

    ||(g'-conj(<g',e>/d_e)g0)-(g-conj(<g,e>/d_e)g0)||
       <=||g'-g||*(1+||g0||/|d_e|).                     (IS7)

The changing model ratio is retained. For supported Fourier kernels and
|Im z|<=251/1000, the full L2 derivative estimate is

    D_F=a*sqrt(2a)*exp(a*251/1000).

The inherited model origin is greater than 805/1000. Directed arithmetic
therefore gives the centered-kernel Lipschitz bound

    D_F*(1+sqrt(2a)/(805/1000))<8/5.

This elementary compact-support integral/derivative specialization remains
paper analysis; its generic centered-vector inequality is a new Lean proof.

On the entire disk |z-(20+i/4)|<=1/1000, the readout-vector variation from
its center is at most 8/5000. The same even-sector coercivity and a second
Young inequality give

    C_disk<=(31/30)*(49/20)+31*(8/5000)^2/(999/1000000)
          =521699/199800 <21/8.                          (IS8)

This is a full-disk statement from an independently bounded derivative,
not a sampled-frequency inference. Every centered readout on the disk stays
in the invariant sector and annihilates the SAME genuine model.

The preceding global model-centering factor is below 20001/20000 and its
derived projective origin lower bound is b=39/50. With the inherited model
energy width nu=929549/15625000000000-ell, exact arithmetic proves

    (20001/20000)*(21/8)*nu/(39/50)^2 <(7/50000)^2.

Consequently, under the recorded actual spectrum, domain and Fourier/model
identifications,

    |FT(u)(z)/FT(u)(0)-FT(e)(z)/FT(e)(0)| <7/50000
    for EVERY |z-(20+i/4)|<=1/1000.                      (IS9)

The genuine model, normalization, physical window and disk are the same as
#5602's earlier origin-normalized certificate with upper bound 51/100000.
IS9 improves that sufficient radius by the factor 51/14, greater than 3.6.
It does not measure the actual error, certify a new Xi zero, increase the
physical window, or improve the full-space ground spectral gap.

### 6. What this changes for the remaining scale problem

The previous single-rate theorem can now consume centered coefficients
certified in the invariant sector and lifted by IS2. The relevant rate is
still

    nu_a * C^circ_(+,a,K) / b_a^2 -> 0.

An opposite-sector small positive gap need not amplify C^circ_+. This is a
structural saving at every scale where the stated invariance, opposite-sector
shifted positivity and complete even-sector certificate hold. It does not
prove how the even threshold, model energy, origin floor or centered trial
quality behave along unbounded physical windows.

The older global spectral placement and positive-form/model-centering
conditions have not disappeared from the complete chain. In particular,
this continuation does not certify them throughout an unbounded family or
replace them by the stronger even bound. The new results consist of a
universal sector-lift proof, an actual full-exterior uniform interval test,
and a quantitatively improved actual same-model disk certificate.

### 7. Sources, executed checks and formalization scope

New Lean owner and paired Scribe:

    D5/S3/Weil/GroundMode/InvariantSectorEnergyReadout.lean
    Blueprint/D5/S3/Weil/GroundMode/InvariantSectorEnergyReadout.scribe.cs

Five public proof scripts cover the actual domain energy split, sector
readout lift, readout-neighborhood budget, model-centered vector variation
and exact rational implications. They introduce no replacement Fourier
transform, canonical zero data, full-space gap or energy-dual definition.
Lean elaboration, transitive axiom reports and Scribe emission were not run.
The operator/domain and interval identities are not automatically kernel
validated by these generic proof bodies.

Two new research programs and their actual outputs are committed under
research/weil_ground_mode/. The sector program is a fresh evaluation of
#5602's complete scale-Schur arithmetic with a different, sector-specific
threshold and its own exact Gram/congruence calculation. The normalized
consumer reuses and reruns this session's earlier centered-residual formulas
with explicit source, trial and model-directory arguments. It checks the
sector result's producer binding but does not rerun that producer internally;
the latter was separately executed in this continuation.

Final sector programs ran at 90 and 120 digits; final readout programs ran
at 100 and 120 digits. The rational sector/readout conclusions agree. Local
exact diagnostics cover 400 complex invariant splits, 400 sector lifts,
400 neighborhood estimates, 400 centered-vector variation checks and 80
signed integer Grams. Three mathematical negative controls test the missing
invariance, commutation and opposite-sector positivity; integer-overflow,
minimum-int64 and noninteger-array inputs are also rejected. Of the centered
phase tests, 369 detect omission of the conjugation. These are single-author
finite checks, not independent proof review or a synthetic Weil experiment.

The arithmetic loader executes only its already inspected AST projection;
complete local input bytes are identified separately and are not claimed
identical to the full remote arithmetic owner. True-prolate and original
global-spectrum verifiers were not rerun. Their selected mathematical fields,
full model-proposal hash and analytic obligations retain the prior scope.

Primary sources reread:

- https://arxiv.org/html/2511.22755v1 , Section 5.2, Lemma 5.2,
  and Section 8's genuine-mode approximation problem.
- https://arxiv.org/html/2606.09096v1 , localized lower-bounded forms
  and the distinction between form cores and operator domains.
- https://arxiv.org/abs/2008.10871 , complete-exterior spectral discretization
  methodology; its Schrodinger assumptions are not asserted for the Weil form.

- Parallel #5602 source at `4804c4020d7d9f165a2e2683c42b01e3d47a8be4`: `WeilPrimeActivationEdge.lean`, blob `5cd36bfeef88311e1f5e6c140fc11e52b16e8881`; `certify_prime3_scale_schur.py`, blob `496333f97d20a6898d47f848a2abd839249e9207`.


---

## [PR #5602] UNIFORM_TRUE_PROLATE_SCALE_TRANSPORT_AND_CENTERED_MELLIN_FLOW

# 2026-09-08：真实 prolate 尺度族与移动算术窗口的定量 Fourier 传递

本节补齐已在研究分支提交的 `WeilMellinScaleFlow.lean`、同名 Scribe 与 `certify_prime3_prolate_scale_transport.py` 的解析依据。处理的是同一个真正 prolate 模型随尺度的变化；前节提供的真实 Weil 最低模态谱分离是另一个结果。两者不能未经误差桥接就合并为同尺度 ground/prolate 逼近。

本次回读确认，前一轮未交付的六个 `WeilPrimeThresholdParity` / `prime3_scale_interval` 工作产物和原理论卷的 184 行追加已经位于远端，后续 `5d22480c06da2ae5716d804129153ba47e115f2a` 又包含本节六个 scale-flow 工作产物。旧 Lean 真源字节保持不变；Scribe 的过时半径改为 2e-8，Python 仅删去说明注释，结果源哈希同步更新。验证了现行源码，并实际重放 70、100 位的统一 Weil 区间程序和 110、130 位的真实 prolate 尺度程序。以下数学内容追加到原卷，不覆盖并行成果。

## 1. 保持同一个模型及原始 Fourier 约定

令 a0=log3/2，I=[a0-epsilon,a0+epsilon]，epsilon=1/50000000。相应 c=exp(2a) 跨过整数 3，但始终在 (2,4)。固定空间 [-1,1] 上的实际正规 prolate 算子为

\[
J(a)=-\partial_t((1-t^2)\partial_t)+(2\pi e^{2a})^2t^2.
\tag{MF1}
\]

其偶 Legendre 自伴实现、紧 resolvent 和有界乘法势沿用 (PM1)-(PM5)，全部尺度具有相同算子域。psi_(0,a)、psi_(4,a) 是编号 0、2 的真实偶模式，单位归一化并以零阶 Legendre 系数为正固定符号。定义

\[
H_a=\psi_{4,a}-\frac{(\psi_{4,a})_0}{(\psi_{0,a})_0}\psi_{0,a},
\qquad h_a(u)=H_a(e^{-a}u).
\]

实际算术函数为

\[
p_{a,H}(x)=1_{[-a,a]}(x)4e^{x/2}
\sum_{1\le m\le e^{a-x}}H(me^{x-a}),\qquad
p_a^+=(p_{a,H_a}(x)+p_{a,H_a}(-x))/2.
\tag{MF2}
\]

Fourier 仍为原 `Zeta23.paperFT`，即 integral f(x)exp(i*z*x)dx。定义待比较的明确归一化 P_a(z)=FT(p_a^+)(z)/FT(p_a^+)(0)，其分母在本节独立认证。没有将 H_a、p_a、前节 dyadic k_a 或未知 Weil 最低模态相互重新命名。

## 2. 全区间上的真实无限 prolate 谱认证

现行验证器读取原来的 32 维、分母 2^250 的固定提案 v_0、v_4。它们本身不被当作真实特征向量。J(a) 的偶 Legendre Jacobi 矩阵为 D0+q(a)^2 V，q(a)=2pi exp(2a)，V 是真实 t^2 乘法算子。V 对角和相邻项由标准 Legendre 递推给出。遗漏空间的完整形式下界仍为 2K(2K+1)=4160。

在两个固定 dyadic 中心 mu_i 的 mu_i-50 和 mu_i+50 处，对整个 a 区间同时检验有限矩阵与其完整尾修正矩阵的惯性。两种 Schur 端点计数分别为 (0,0;1,1) 和 (2,2;3,3)。所以每个区间有且仅有一个对应编号的真实简单特征值，其余全部无限谱到固定中心的距离至少为 50。不能把有限 Jacobi 矩阵的单独计数当作这一步。

保留参数差的相关性，完整残差满足

\[
\|(J(a)-\mu_i)v_i\|
\le\|(J(a_0)-\mu_i)v_i\|
+|q(a)^2-q(a_0)^2|\,\|t^2v_i\|.
\tag{MF3}
\]

两个范数都包括第 K 个遗漏坐标。谱分解和单位向量相位比较给出 eta_i=sqrt(2)*rhs/50 的模式误差。零阶坐标大于 eta_i 的检查固定同一符号。定向区间结果为 eta_0<3.646331e-8、eta_4<2.319807e-7；对应中心误差也从实际残差重新计算，没有读历史成功 JSON 作谱前提。

令 r=v_(4,0)/v_(0,0)，固定多项式 Htilde=v_4-rv_0。其零阶系数严格为零。真实系数比的误差满足

\[
\delta_r\le(\eta_4+|r|\eta_0)/(v_{0,0}-\eta_0),
\quad
\|H_a-\widetilde H\|\le\eta_4+(|r|+\delta_r)\eta_0+\delta_r.
\tag{MF4}
\]

验证器认证右侧小于 652/10^9；中心版本小于 3.142e-29。固定多项式的范数预算是 1+|r|，一致值预算是 sum_j |Htilde_j|sqrt((4j+1)/2)<7.61，来自真实 Legendre 系数。

## 3. 实际移动窗口的精确尺度流

先保持 H 为固定连续函数。设 s=1/2+iz。对每个整数 m 用 t=m exp(x-a) 代换，得到实际积分

\[
F_{a,H}(z)=4e^{as}\sum_{m\le e^{2a}}m^{-s}
\int_{me^{-2a}}^1 H(t)t^{s-1}\,dt.
\tag{MF5}
\]

在可见整数集合不变的尺度区间内，微分得到

\[
\boxed{\partial_a F_{a,H}(z)=sF_{a,H}(z)
+8e^{-as}\sum_{m\le e^{2a}}H(me^{-2a}).}
\tag{MF6}
\]

新整数刚进入时，其 (MF5) 中积分区间长度为零。因此 F 在激活点连续，左右导数可不同，(MF6) 在每个开区间成立；有限个激活点两侧的统一导数界可以积分相加，得到跨阈值的 Lipschitz 界。没有将 moving-cutoff 项删除，也没有从函数的 L2 支撑差粗略推断线性误差。

对固定偶多项式 H(t)=sum_(r<d) B_r t^(2r)，设 s_r=2r+s。复用原多项式 Fourier 定理，已提交的新 Lean 证明

\[
\boxed{e^{-as}F_{a,H}(z)=4\sum_{m=1}^M\sum_{r<d}
B_rm^{2r}\frac{e^{-s_r\log m}-e^{-2as_r}}{s_r}.}
\tag{MF7}
\]

条件是全部纳入的 m 满足 log m<=2a，Im z<1/2；原 integrand 的可积性由既有 owner 保证。`scaled_polynomial_centered_paperFT` 保存 (MF7)，`scaled_polynomial_paperFT_scale_difference` 将两尺度的上端项精确消去，留下下端指数差。后者要求两个尺度具有同一合法 M；跨激活点的连续拼接是 (MF5)-(MF6) 的纸面步骤，不能误称为该 Lean 声明直接覆盖变动索引集。偶化使用 F(z)、F(-z) 的平均，两个方向都保留。

## 4. 真正变动模式的统一运输

设 a_-、a_+ 为 I 的两端。单个整数项用 t=m exp(x) 代换，再合成并偶化，得到从固定 H 坐标到物理窗口的 L2 算子预算

\[
C=4e^{a_+/2}\sum_{m=1}^3m^{-1/2}.
\]

对 |Im z|<=b，记 W_b=sqrt(2a_+)exp(a_+b)C，W_0=sqrt(2a_+)C。在 D={|z-(20+i/4)|<=1/1000} 上取 b=251/1000，|s|<21。对固定 Htilde，(MF6) 给出导数上界

\[
L_b=21W_b(1+|r|)+24e^{-a_-(1/2-b)}\|\widetilde H\|_\infty,
\quad
L_0=\tfrac12W_0(1+|r|)+24e^{-a_-/2}\|\widetilde H\|_\infty.
\tag{MF8}
\]

这里 24=8*3 保留所有可能可见整数。令 E_I、E_0 为 (MF4) 的区间和中心种子误差。分解真实函数的变化为“当前真实模式减固定多项式”、“同一固定多项式的尺度流”、“固定中心多项式减中心真实模式”，得到

\[
\sup_{a\in I,z\in D}|\widehat p_a^+(z)-\widehat p_{a_0}^+(z)|
\le W_b(E_I+E_0)+\epsilon L_b=:d_b,
\]

\[
\sup_{a\in I}|\widehat p_a^+(0)-\widehat p_{a_0}^+(0)|
\le W_0(E_I+E_0)+\epsilon L_0=:d_0.
\tag{MF9}
\]

只对固定多项式求尺度导数，未假设未知真模式导数或其连续常数。实际 d_b<2.2230e-5、d_0<1.1190e-5。

原中心多项式的 Fourier 端点公式算出原点约为 2.336197886604782；减中心真模式误差得到 beta_0，再减 d_0 得到所有尺度的正下界 beta_I>23/10。这个正下界对应 (MF1)-(MF2) 的固定原始标度；原点归一化结果与非零整体标度无关。中心分子的圆盘上界 M_D 也包含真实模式误差和 Fourier 代表元导数，而非只用中心点值。精确商恒等式给出

\[
\sup_{a\in I,z\in D}|P_a(z)-P_{a_0}(z)|
\le\frac{d_b+M_Dd_0/\beta_0}{\beta_I}.
\tag{MF10}
\]

两种精度的实际验证均得到

\[
\boxed{\inf_{a\in I}|\widehat p_a^+(0)|>23/10,
\qquad \sup_{a\in I,z\in D}|P_a(z)-P_{a_0}(z)|<10^{-5}.}
\tag{MF11}
\]

充分上预算约为 9.54904664569e-6。令 r_(a,z)(y)=conjugate(cos(a z y)-P_a(z)) 于 [-1,1]，直接对指数核估计可再得

\[
\boxed{\sup_{a\in I,z\in D}\|r_{a,z}-r_{a_0,z}\|_{L^2[-1,1]}<15/10^6.}
\tag{MF12}
\]

其实际预算约为 1.41537868833e-5。复共轭不改变范数；r_(a,z) 是针对同一真模型中心化的 Fourier 代表元，尚未假定它在真实 ground 上的读出很小。

## 7. 研究意义、复验及尚缺的连接

前节已经在同一个 I 上认证实际 Weil ground 的简单偶性和大于 4.8e-6 的间隔。本节消除了模型端尚无统一尺度误差及原点分母控制的缺口。不能因此声称 ground/model 的同尺度差已经小：还需要实际 q_a 正交补上的能量对偶试探及完整 residual，或有效的低能谱投影传递。中心尺度已有的 0.00051 归一化 ground/model 圆盘界，也不能未经 ground 传递误差预算就扩展到整个 I。

本次重新核对 CCM arXiv:2511.22755 的官方版本页（取得的记录列出 v1）和正文 Sections 7-8；其模型极限与真实模式充分逼近保持分开。Connes 2026 综述 arXiv:2602.04022 为同一路线背景。实际读取 5040/Mertens 研究链 #6204 的 `GronwallUpperEnvelope.lean`，blob `75eb28885ee1250985d9dbd19b73fa76f3502d04`：该结论是 sigma(n)/(exp(gamma)*n*loglog n) 的渐近上包络，不是本节的算子间隔或 prolate 估计，不将标量渐近移作谱假设。原有 #5882 能量对偶、#5895 正移位形式和归一化消费者继续作为下游目标，未新建通用包装。

现行模型源 SHA-256：`fe1d574f38a13e0dbcc185649c0e6c32dfd9e1cb676ceebb73ad7c6c31218b4f`；固定提案 SHA-256：`242c9897bbd247ef0485039e6dcde819a351c5900ceac52fecc420934c1896db`。本次实际重放 110、130 位定向区间计算，全部惯性、完整残差、符号、原点和误差 guard 通过。110 位结果 Git blob 与远端 `45c149e61156ad85ce1c5cd0cbde1ba297ec790f` 完全一致；其 SHA-256 为 `bd57ff4bf4b7a388dc086519f708ee33b381f1202af25a11cba0d0bfc81f4d0a`。同时重放前节 70、100 位的全空间 Weil 区间证书通过。本轮的重放不等于独立作者审稿。

Lean 的三个公开声明与三个同名 Scribe handles 对应，完整谱实现、积分变换、跨激活拼接和归一化运输仍是上述纸面桥。Lean elaboration、Scribe emission、传递公理报告未执行，没有新增冻结或 CI 状态声明。经典谱残差、Leibniz 公式和商估计不作数学优先权主张。当前窄尺度区间和小复圆盘尚不能推出无界尺度族上的 Xi 极限或 RH。

参考：Connes-Consani-Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, Sections 7-8；Connes, arXiv:2602.04022；既有 `WeilPolynomialMellinWindow`、`WeilMellinScaleFlow` 和本卷 prolate Jacobi 实现。

- https://arxiv.org/abs/2008.10871 , complete-exterior spectral discretization
  methodology; its Schrodinger assumptions are not asserted for the Weil form.

## [PR #5895] SIGNED_MODEL_RESIDUAL_PAIRING_AND_GOAL_CORRECTION

### 1. The open problem and the role of the old sufficient rate

The target is still the actual lowest-Weil-mode comparison with the same
correctly normalized prolate family in Connes, Consani and Moscovici,
Zeta Spectral Triples, arXiv:2511.22755v1, Section 8. The explicit-model
transform limit of Lemma 7.3 is a separate step. This increment preserves the
signed complex primal/dual pairing before estimating the remaining error.
It does not establish that pairing's decay along unbounded physical windows.

The preceding condition nu*C_centered/b^2 -> 0 is sufficient. It is not a
necessary condition for the actual normalized readout error to vanish.
Directional residual cancellation may be lost when the full model error is
bounded first by a single energy budget. The following exact identity is a
complementary certificate; all earlier inequalities remain valid.

The primary methodological reference is Wu and Zhang, Goal-Oriented Error
Estimation for Least-Squares Finite Element Methods via Physically Meaningful
Adjoint PDEs, arXiv:2607.23850v1 (26 July 2026), Section 4, especially the
corrected-output and product-remainder statements. That paper explicitly
retains the classical Giles--Suli lineage. Its elliptic PDE assumptions and
least-squares estimates are not used as hypotheses for the Weil operator.
The domain-level identity here needs neither a Galerkin solution nor an exact
dual inverse. No priority for residual correction is claimed.

Cross-session readback: #6029 at 99b3e1ca03e88f42a9b7c6ccadecc545e8c64a97
identifies actual zero-extended Fourier convolutions with the exterior
arithmetic column; it still separates the diagonal regularization and actual
operator-domain realization. #5602 at 5b1c54e84706acdca64e2ec042b51a5d52c5fcea
retains the complete genuine prolate model residual and newer scale work.
Those results are not reimplemented or counted as this continuation's work.
The numerical inputs below are the previously pinned c=3 records, not
unverified values inferred from a more recent PR title or description.

The final concurrent readback found #5895 advanced to
e6a7b1837783c6b9b4eb00d90240ae53e4543045, adding only the separate
InvariantSectorEnergyReadout Lean/Scribe pair. Its actual first 100 source
lines were read: the invariant-sector split keeps opposite-sector shifted
positivity separate from a positive gap. This contribution is not ours.
No numerical sector improvement is substituted into SG7-SG9. The three
paths proposed here were unchanged by that concurrent commit. This payload
was subsequently delivered on top of 023e6d1eccb223a563939590d301085a220b38f2,
preserving the completed parallel sector computation and theory appendix.

### 2. Signed identity with the actual eigenvalue uncertainty

Let iota,M:E->H be complex-linear maps on an actual operator domain, symmetric
there. Inner products are conjugate-linear in their first argument. Suppress
iota in the equations. Let e be a unit model and p an aligned eigenvector,

    Mp=lambda p,       <e,p>=1,       w=p-e perpendicular to e.

For g0 and g the actual origin and target readouts, put

    h=g-conj(<g,e>/<g0,e>)*g0,       <h,e>=0.

Choose a domain trial v perpendicular to e and ANY real spectral center sigma.
Define the complete quantities

    r_sigma=Me-sigma e,
    s_sigma=P_(e-perp)(h-(Mv-sigma v)),
    D=<v,r_sigma>.

Symmetry and the actual eigenvalue equation give the exact complex identity

    <h,p> + D = <s_sigma,w> + (lambda-sigma)<v,w>.          (SG1)

The correction is -D. Dropping lambda-sigma is invalid unless it is zero
or has been separately budgeted. Dropping the exterior of s_sigma is also
invalid. No scalar norm inequality or approximation theorem is assumed to
produce SG1.

For certified bounds ||s_sigma||<=S, |lambda-sigma|<=eta, ||v||<=V and
||w||<=R, Cauchy--Schwarz yields

    |<h,p> + D| <= (S+eta V)R.                             (SG2)

The right side is a product of the actual mode-error radius and the full
dual-residual/shift uncertainty. A small signed pairing does not by itself
make this remainder small, nor does it determine the actual output sign.

### 3. The model-origin correction and the actual denominator

Write d_e=<g0,e> and d_p=<g0,p>. From ||g0||<=G0 and the actual error bound,

    |d_p-d_e|<=G0 R.

If b,b0>0 and b+G0 R<=b0<=|d_e|, then |d_p|>=b. The existing centered-readout
identity supplies the quotient difference. Normalizing the computable
correction by the MODEL origin gives

    |<g,p>/<g0,p> - <g,e>/<g0,e> + D/d_e|
      <= (S+eta V)R/b + |D| G0 R/(b0 b).                 (SG3)

The second term is the cost of replacing d_p by d_e. It remains even if the
unscaled dual remainder vanishes. It is derived from the exact identity

    H/d_p + D/d_e = (H+D)/d_p + D(d_p-d_e)/(d_e d_p),
    H=<h,p>.

The public projective consumer constructs p=u/<e,u> using the existing
Rayleigh enclosure, derives the error radius from nu<=kap*R^2, and obtains
SG3 for the ACTUAL raw eigenvector ratios. Arbitrary complex phase and scale
cancel. The old eigenpair, spectral placement, domain and unit-model
conditions are retained; the theorem does not manufacture an eigenvector.

A scale limit to the ORIGINAL prolate model requires the normalized correction
D_a/d_(e,a) to tend uniformly to zero, as well as the product remainder in
SG3. Convergence to a newly corrected model alone does not establish the
original Xi/Xi(0) limit. The model has not been silently redefined here.

### 4. Why the finite trial can compute the genuine signed defect

Let mu=Re<e,Me>. Symmetry makes this diagonal pairing real, so the actual
Rayleigh residual r_mu=Me-mu e obeys <e,r_mu>=0. Therefore subtracting ANY
multiple of e from a domain trial leaves its pairing with r_mu unchanged:

    <v-beta e,r_mu>=<Mv,e>-mu<v,e>.                       (SG4)

In particular let v_e=v-<e,v>e be the repaired trial used in SG1. Since
v_e is e-orthogonal, its pairing with r_sigma also equals its pairing with
r_mu. Thus its signed correction is exactly <(M-mu)v,e>, computed from the
ORIGINAL finite v. The full action (M-mu)v is still generally infinite.
SG4 does not assert finite support of that action or of the repaired trial.

Split that action into finite a_head and exterior a_tail. A complete pairing
budget can use a known finite candidate k with <a_tail,k>=0:

    |<a_head+a_tail,e>-<a_head,e_approx>|
      <= ||a_tail|| ||e-k|| + ||a_head|| ||e-e_approx||.    (SG5)

For a sharper tail budget, unit normalization and orthogonal Fourier
projection give

    ||e_tail||^2 = 1-||e_head||^2
      <= 1-(||e_approx,head||-gamma)^2,                  (SG6)

provided ||e_head-e_approx,head||<=gamma<=||e_approx,head||.
Subtract the approximation error before squaring. The near cancellation in
one minus captured energy must use outward rounding. SG5 and SG6 have new
Candidate Lean proof bodies; the actual Fourier/Parseval identification and
model-approximation record are still the same separate analytic inputs.

### 5. Executed signed pairing for the same genuine c=3 model

The same archived 129-coordinate finite complex trial and aligned UNIT
true prolate model are used. No eigensolver, zero-location table or numerical
quadrature enters the new scalar consumer. The full arithmetic primitive
projection and model proposal are pinned to the previous delivery.

The actual pairing is

    D=<v,(A-mu)e>=<(A-mu)v,e>.

Both positive and negative column coefficients are evaluated independently.
Fourier model coefficients are explicitly evaluated through |n|<=P=512.
Action squares in the remaining finite exterior are evaluated through
M=8192. The full analytic column tail beyond M retains all four boundary
moments. The model tail is paid separately using SG6; no high coefficient
is assigned zero.

Two directed-interval executions, at 110 and 120 decimal digits, give the
same outward rational enclosures. Convenient rounded statements are

    -5.300e-6 < Re D < -5.288e-6,
     1.209e-6 < Im D <  1.222e-6,
    |D| < 5.44e-6.                                      (SG7)

The actual interval endpoints and exact input hashes are in the local
reproduction result. The all-tail radius is below 5.634e-9. A fixed rational
complex approximation is

    Dapprox=-10588081114283/2000000000000000000
                 + i*(1215543485777/1000000000000000000),
    |D-Dapprox| < 6/10^9.                                (SG8)

The captured model energy gives a full model-tail norm below approximately
5.065e-6. Combined with the complete column-tail energy, this is much tighter
than using the old model/candidate distance 0.00113 for this scalar pairing.
The basic product bound ||v||*rho<7*9.16662e-5 is over 117 times the new
upper bound on |D|. This comparison concerns sufficient SCALAR-PAIRING budgets,
not a 117-fold improvement of the actual mode or the final Fourier error.

A P=128 calculation also completed. An exploratory P=1024 call hit the
execution time limit and is not counted as a completed certificate. There
is no claim of an optimal P, a converged unknown infinite-mode value, or
an unbounded physical scale experiment.

### 6. Complete corrected-output budget on the prior small box

Use the same closed box of half-width 1/100000 around 20+i/4, the prior
whole-domain lower bound ell, old candidate energy width delta and genuine
model width nu. The previous centered full-residual verifier was replayed
at 100 digits in this continuation. Its two-sided exterior is unchanged.

Choose sigma=eta=delta/2, since the inherited eigenvalue enclosure gives
0<=lambda<=delta for M=A-ell. The old complete centered residual radius is
less than 357/10000. Recentring it with the full model residual and retaining
the spectral-center shift yields

    ||s_sigma|| < 3572/100000,
    ||w|| < 194/10000,
    ||v_e|| < 7,
    ||g0|| < 21/20,
    |d_e| > 805/1000,       |d_p| > 784/1000.

The raw centered candidate component is below 13/1000, obtained from the
prior uncentered component, the actual model ratio and the origin-kernel
norm. Its contribution is not discarded. The original model graph residual
is used here only to transport the full dual residual; it is not substituted
for the signed scalar pairing in SG7.

Exact Fraction arithmetic and a Candidate norm_num theorem give

    |ratio(u)-ratio(e)+Dapprox/d_e| < 885/1000000,
    |ratio(u)-ratio(e)| < 891/1000000.                    (SG9)

These inherit the recorded canonical operator/domain, full spectrum, genuine
model and Fourier identities. They are weaker than #5602's previously
reported normalized bound 51/100000 on a larger disk. The useful new output
is the signed defect and the product-remainder route, not a superior
fixed-window zero-free region. The remainder is currently much larger than
the signed defect, so no sign of the ACTUAL Fourier error is inferred.

### 7. A control showing the preceding single rate is not necessary

For a synthetic three-dimensional family let t=1/j, j>=10,

    c=(1-t^2)/(1+t^2),   s=2t/(1+t^2),
    M=diag(0,8s^2,1),   k=e=(c,0,s),   u=(1,0,0),
    h=(0,1,0),   g0=(1,0,0),   v=(0,1/(8s^2),0).

The old complement gap kappa=8s^2, model energy nu=s^2, eps=0 and anchor
b=1/4 satisfy the old centered theorem's conditions. The sharp old coefficient
is C=1/(8s^2), so nu*C/b^2=2 for every j. Nevertheless the actual normalized
readout error is identically zero, as are D and the complete dual residual
at sigma=lambda=0. The closed-form algebra proves the example; 101 exact
instances were also replayed. This is not an arithmetic Weil family and is
not evidence for its asymptotic cancellation.

It demonstrates a precise methodological point: failure to prove the old
single sufficient rate does not itself obstruct the original open problem.
The signed product estimate can see output cancellation hidden by that rate.
Conversely, a fixed-window nonzero D says nothing about whether D_a/d_(e,a)
will decay in the physical scale limit. Both questions remain separate.

### 8. Candidate sources and execution boundary

This continuation adds eight public theorem scripts to the existing
GenuineModelDualTransport.lean and eight matching canonical Scribe handles.
All original source text is preserved except the syntactic closing delimiter
needed to append Scribe entries. No new Fourier or dualBudget definition is
introduced. This theory text is now appended to the existing volume.
No Lean elaboration, transitive axiom audit or Scribe emitter was executed.

Executed checks include 600 exact Hermitian eigenpair cases and signed
identities, 600 product and ratio bounds, 600 repaired arbitrary-shift
pairings, 480 captured-head model-tail checks, 1800 raw phase/scale checks,
and negative controls for omitted eigenvalue uncertainty and omitted
actual-denominator correction. Wrong signs and complex-conjugation mutations
are detected. These are single-author finite diagnostics, not independent
proof review or a universal kernel verdict.

The previous exact centered diagnostics and 100-digit interval transport
were rerun in the original computation. The 512-mode scalar calculation was
run at 110 and 120 digits. At delivery the exact diagnostics, source/patch
checks and rational budget assembly were rerun. The original full spectral,
genuine-prolate and graph-norm verifiers were not rerun. Their input scope
remains explicit. The local input projections are not misrepresented as
complete upstream-file attestations.

Primary references read in the original computation:

- https://arxiv.org/html/2511.22755v1 , Lemma 7.3 and Section 8.
- https://arxiv.org/html/2607.23850v1 , Section 4 and the abstract's
  no-Galerkin/product-error qualifications, 26 July 2026.
- https://arxiv.org/html/2606.09096v1 , localized forms and operator domains.

## [PR #5895] SIGNED_SECTOR_CERTIFICATE_AND_ORIGINAL_MODEL_CLOSURE

### 1. Which logical chain is now assembled

The signed primal-dual proofs and their eight Scribe bindings from the previous
round were delivered first at 088584353834d97bd5396f04b06abb13ef519612. That
normal child preserves the independent invariant-sector work at
023e6d1eccb223a563939590d301085a220b38f2. This continuation combines those two
mathematical increments on the actual restricted domain. It also proves the
terminal implication to the ORIGINAL model limit, explicitly retaining its
unproved arithmetic scale hypotheses.

The open problem remains CCM, Zeta Spectral Triples, arXiv:2511.22755v1,
Section 8: actual lowest-mode approximation by the same normalized prolate
family. Section 5.2 supplies the reflection setting, and the explicit model
limit in Section 7 is a distinct input. Wu and Zhang, arXiv:2607.23850v1,
Section 4, provides the classical output-correction/product-remainder
comparison. Suzuki, arXiv:2606.09096v1, supplies the localized form and domain
context. These versions were reread; their PDE hypotheses or unproved
all-window conclusions are not asserted for the present operator.

### 2. Use the even lower bound only inside the even domain

The independently executed complete-sector certificate on this PR gives
q_A(f)>=||f||^2/1000 for even k-orthogonal vectors, in the stated neighborhood
of a=log(3)/2. Its source blob is c29d0459429becf39f294221949975a23894ef47.
The normalized sector-readout report has blob
05f5b73fabd92d68893fbb9c32d69816c71f3fb3. Both were reread at the immutable
head above. Their Fourier/core, full high-complement and reflected-domain
identifications remain inherited analytic premises. The sector producer was
not rerun in this continuation.

Let F be the complex submodule of actual even domain vectors. Require
k,e,u,v in F. Restrict the original maps by iota_F=iota composed with the
subtype map and M_F=M composed with that map. The stronger lower bound is
used on F only. No assertion about an odd or full-space gap is made.

At the CENTRAL window take the independently inherited global ell and set

    kappa=1/1000-ell,   delta=q_M(k) upper,   nu=q_M(e) upper,
    ||e-k||<=epsilon,
    kap=kappa*(1-epsilon^2)/(1+t)-delta*epsilon^2/t.       (SC1)

The already-proved positive shifted-form theorem derives the e-complement
bound on F. The new sector_projective_signed_ratio_bound then calls the
already-proved actual projective signed-output theorem on that restricted
domain. Its hypotheses include actual eigenvalue placement, unit model,
trial membership, full residual and origin margins. It does not receive a
new-complement estimate or final output bound as an unexplained oracle.

A whole-domain symmetric realization is used in this particular statement;
positivity is needed only on F. The old global ell is not asserted uniform
on the neighboring scale interval. Membership of the selected actual ground
mode in the even sector is still supplied by the established symmetry chain.

### 3. The fixed trial controls the entire frequency disk

For the same e and trial v, let

    h_z=g_z-conj(F(e)(z)/F(e)(0))*g0,
    s_z=P_e(h_z-(M-sigma)v).

Since v and sigma are FIXED as z changes,

    s_z-s_z0=P_e(h_z-h_z0),
    ||s_z||<=||s_z0||+||h_z-h_z0||.                      (SC2)

The new signed_goal_residual_neighborhood proves this identity's norm
consequence using the existing orthogonal projection contraction. The
residual is a full Hilbert-space vector, including every omitted Fourier
coefficient. No positive high-frequency term disappears during transport.

The parallel same-model readout certificate independently proves
||h_z-h_z0||<=(8/5)|z-z0| on |z-z0|<=1/1000, z0=20+i/4. It includes the
variation of the true-model ratio, not just the raw Fourier kernel. The
signed model pairing D=<v,(M-sigma)e> is constant across this disk because
the repaired trial, model and spectral center are fixed.

The previous complete centered residual calculation was rerun at 100 digits,
and the complete signed 512-mode pairing was rerun at 120 digits. Both agree
with the recorded outward rational enclosures. Model Fourier coefficients
are evaluated through 512, arithmetic columns through 8192, and all remaining
modes have their original complete tail budgets. The same arithmetic AST,
finite trial, unit-model alignment and model-proposal hash are retained.

### 4. Exact synthesis on the same physical disk

The old global ell, delta, nu and epsilon are unchanged. Taking t=1/100000
in SC1 gives approximately kap=0.0009999335842419315. Exact arithmetic proves

    delta<kap, nu<kap, nu<kap*(212/100000)^2.

Thus the actual model-aligned EVEN eigenvector p_e=u/<e,u> has

    ||p_e-e||<=R,       R=212/100000.                     (SC3)

This uses the full sector lower bound, not a truncated matrix eigenvalue.
For sigma=eta=delta/2, V=7, the previously certified central full residual is
below 3572/100000. SC2 gives the disk-wide cap

    S=3572/100000+(8/5)*(1/1000)=0.03732.

The same origin kernel has G0=21/20 as an upper bound. Set b0=805/1000 and
b=802/1000. The exact inequality b+G0*R<b0 proves |F(p_e)(0)|>=b.

Retain the full signed model pairing and its finite approximation from SG7-8:

    |D|<544/10^8,
    Dapprox=-10588081114283/(2*10^18)+i*1215543485777/10^18,
    |D-Dapprox|<6/10^9.

The new finite_pairing_corrected_ratio_bound transports the computational
radius as q/b0, with q=6/10^9. The resulting full error expression is

    E=(S+eta*V)*R/b+|D|*G0*R/(b0*b)+q/b0
      <0.000098677591663762 <99/10^6.                    (SC4)

Consequently, on the ENTIRE closed disk |z-(20+i/4)|<=1/1000,

    |F(u)(z)/F(u)(0)-F(e)(z)/F(e)(0)+Dapprox/F(e)(0)|
       <99/10^6.                                       (SC5)

Adding the certified magnitude of the correction proves the original-model
bound, rather than only a bound to a corrected surrogate:

    |F(u)(z)/F(u)(0)-F(e)(z)/F(e)(0)|
       <99/10^6+(544/10^8+6/10^9)/(805/1000)
       <53/500000=0.000106.                             (SC6)

This improves the preceding sector certificate's sufficient original-model
error 7/50000=0.00014 on the SAME disk by factor 70/53>1.32. The unknown
actual error has not been measured. There is no larger support window, new
spectral enclosure or Xi-zero conclusion. The output radius still exceeds
the leading signed correction; no sign of the actual Fourier error follows.

The numeric synthesis is a new exact consequence of independently certified
sector and model data. The inherited global spectrum, true-prolate spectrum,
operator-domain identification and sector Schur producer are not reverified
by this arithmetic. The new prime_three_sector_signed_budget checks the
rational implications in SC1-SC6; it does not attest those upstream premises.

### 5. Terminal implication to the original model limit

The signed_goal_original_model_uniform_limit theorem permits a different
Hilbert space and actual linear operator domain at each scale. Its inputs
are actual eigenpairs, model energy and complement bounds, trial vectors,
complete dual residual bounds S_j, spectral uncertainty eta_j, trial bounds
V_j, derived-error radius data R_j, origin kernel bounds and margins b_j,b0_j.
For the actual signed pairing assume a uniform finite bound |D_(j,z)|<=B_j.
It invokes the existing projective signed theorem and proves convergence of
the actual normalized eigenmode functions to the SAME limiting function as
the original normalized models, provided

    B_j/b0_j ->0,                                       (SC7)
    (S_j+eta_j*V_j)*R_j/b_j
       +B_j*G0_j*R_j/(b0_j*b_j) ->0,                    (SC8)

and the original normalized models tend uniformly to that function on K.
The triangle inequality adds SC7, SC8 and the original-model convergence.
There is no assumed final mode-error estimate and no silent replacement of
the model by a corrected one. If the correction does not vanish, convergence
to the corrected surrogate alone gives a different possible limit.

SC7-SC8 are still arithmetic hypotheses for the intended unbounded Weil
windows. The theorem proves the complete implication from them, not those
physical rates themselves. The finite-window certificates above establish
neither an unbounded sequence of spectral enclosures nor the all-scale
simple-even and model-normalization premises of CCM. Calling this endpoint
an unconditional proof of the original open problem would be incorrect.

### 6. Source and computation audit

Five new declarations extend the existing GenuineModelDualTransport owner,
with five matching canonical Scribe entries. No new Fourier transform,
energy budget, model definition or logical axiom is introduced. The old
signed proofs and the parallel invariant-sector module remain unchanged.
All new statements have proof bodies, but Lean elaboration, transitive
axiom reports and Scribe emission have not been executed in this runtime.
The sources remain logically reviewed Candidates.

New exact diagnostics exercise 400 restricted-domain examples, 400
positive-form model-gap consequences, 400 full-residual frequency variations,
400 finite pairing-error transports, 400 signed ratio bounds and 1200
phase/scale identities. Negative controls retain the necessity of the actual
sector restriction, the signed correction's vanishing in an original-model
limit, full frequency variation and finite-pairing uncertainty. Those finite
examples are not arithmetic Weil experiments or an independent review.

The same old 512-mode interval calculation was actually replayed at 120
digits and the full centered residual at 100. Their key intervals match the
previous records. The local exact synthesis checks the named remote sector
and readout fields as semantic projections, not an attestation or replay of
their full spectral producers. All scripts, precise inputs and results are
retained in the accompanying reproducibility archive.

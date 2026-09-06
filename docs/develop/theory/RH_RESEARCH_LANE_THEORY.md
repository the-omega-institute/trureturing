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
&\sim \text{提升后的非交换曲率},
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

1. 在绝对收敛半平面中建立有限或无限黄金壳测度的 Fourier 系数与 `-L'/L` 竖直采样之间的定理；
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
2\|a-1\|\varepsilon+2\varepsilon^2
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
\frac{e^{\delta t}-e^{-\delta t}}2.
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
\]

---

## [PR #5602] WEIL_GROUND_MODE_SHIFT_BARRIER

# Weil 最低模态路线中的内部平移障碍与算术边界项

对应真源：`D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.lean`。
配套 Scribe：`Blueprint/D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.scribe.cs`。

本节补入前一轮已提交 Lean 的理论推导。有限平移恒等式、紧支撑非消失性和平方残差下界已有 Lean 证明脚本，尚未经本环境编译。尺度族推论及算术边界展开是纸面推导。没有证明完整算术强制性、最低模态单纯偶性或 RH。

## 1. 同一算术对象与平移探针

令

\[
C(f,g)(s)=\int_{\mathbb R}f(x)\overline{g(x-s)}\,dx,
\qquad W(f,g)=\operatorname{literatureRHS}(C(f,g)).
\]

直接使用 `Zeta23.EF.weilTest` 与 `Zeta23.EF.literatureRHS`，保留实际 von Mangoldt 素数幂系数、两个极点项和 `gammaBracket`。这里的原始相关函数载体允许一般复值函数。已有 `WeilTestFunction` 的偶性约束不能代替完整奇偶空间上的最低模态论证。

Fourier 约定为 `hat f(z)=integral f(x)*exp(i*z*x) dx`。固定 `t>0`，定义

\[
S_tf(x)=f(x-t)+f(x+t),\qquad B=S_t-\alpha I.
\]

对归一化候选 `k`，取实数 `alpha=<S_t k,k>`，则 `|alpha|<=2` 且 `Bk` 与 `k` 正交。相关函数满足精确恒等式

\[
C(Bf,g)=C(f,Bg),\qquad C(Bk,Bk)=C(k,B^2k).
\]

这些等式在作用整个 `literatureRHS` 之前成立，因此不会丢掉 prime、pole 和 Gamma 项之间的抵消。

## 2. 已提交的方向性残差障碍

当 `Bk` 和 `B^2k` 都是同一窗口算子的合法测试函数时，令

\[
\mu=\langle k,A_ak\rangle,\qquad R=(A_a-\mu)k,\qquad r=\|R\|_2.
\]

则

\[
q_a(Bk)-\mu\|Bk\|_2^2=\Re\langle R,B^2k\rangle.
\]

结合该方向的强制性与残差配对上界，Lean 证明脚本给出

\[
\boxed{\delta^2\|Bk\|_2^2\le3(2+\alpha^2)r^2.}
\]

它没有证明算术强制性本身。利用 `|alpha|<=2`，可读出

\[
\boxed{r/\delta\ge\|Bk\|_2/\sqrt{18}.}
\]

## 3. 固定内缩候选的尺度族障碍

设归一化候选满足

\[
\operatorname{supp}k_a\subset[-a+2t,a-2t],
\qquad k_a\longrightarrow k_\infty\ne0\text{ in }L^2(\mathbb R),
\]

其中 `t>0` 固定。内缩余量使一次、两次平移仍为原窗口合法测试函数。此时

\[
B_ak_a\longrightarrow(S_t-\alpha_\infty)k_\infty.
\]

右侧非零，因为 Fourier 乘子 `2*cos(t*xi)-alpha_infty` 的零集离散，非零 L2 函数不可能完全支撑于该零测集。因此，若余维一强制性成立，必有

\[
\boxed{\liminf_{a\to\infty}r_a/\delta_a>0.}
\]

这个障碍已经存在于偶子空间内部，因为对称平移保持偶性。

## 4. 对明确 Xi 核截断的应用

令

\[
\Phi(x)=\sum_{n=1}^\infty
\left(4\pi^2n^4e^{9x/2}-6\pi n^2e^{5x/2}\right)
\exp(-\pi n^2e^{2x}).
\]

此 theta 核为偶函数，满足上述 Fourier 约定下的 `hat Phi=Xi`，并具有双指数衰减。取具有固定内缩余量的偶光滑截断 `chi_a`，令

\[
k_a=\chi_a\Phi/\|\chi_a\Phi\|_2,
\qquad c_a=\|\chi_a\Phi\|_2.
\]

双指数衰减给出 `c_a*hat k_a=hat(chi_a*Phi)` 在复平面紧集上一致收敛到 Xi，并且 `c_a` 趋向非零常数。另一方面，第 3 节说明：若强制性成立，

\[
|c_a|\sqrt{2a}e^{ba}r_a/\delta_a\longrightarrow0
\]

甚至在 `b=0` 也不成立。因此固定内缩的 Xi 核截断不能同时实现该强制性与此充分收敛条件。本推导不排除触及边界的 prolate 候选，也不排除直接控制 Fourier 观察误差的较弱机制。

## 5. 保留边界后的精确缺陷

令 `P` 为窗口正交截断，`Q=I-P`，`Pk=k`，并记

\[
v=PBk,\quad h=QBk,\quad w=PBv,\quad e=QBv.
\]

在混合 Weil 配对合法的条件下，相关函数转移给出

\[
W(v,v)+W(h,v)=W(k,w)+W(k,e).
\]

由此

\[
q_a(v)-\mu\|v\|_2^2
=\Re\langle R,w\rangle+\mathcal B_a(k,t),
\]

\[
\mathcal B_a(k,t)=\Re\{W(k,e)-W(h,v)\}.
\]

因为 `v` 与 `k` 正交且 `||w||<=4||v||`，强制性要求

\[
\boxed{\mathcal B_a(k,t)\ge\delta\|v\|_2^2-4r\|v\|_2.}
\]

中心化系数 `alpha` 在这个边界泛函中抵消。因此该量由明确候选、窗口与平移步长独立决定。边界贡献需要支撑所需谱分离，不能仅以边界 L2 质量小为由忽略。

## 6. 有限素数幂表达与 Abel 变换

设

\[
d=C(k,e)-C(h,v),\qquad H(s)=\Re(d(s)+d(-s)),\qquad M=2a+t.
\]

对紧支撑、有限分段光滑的候选，相关函数具有所需正则性。窗口内外正交性及支撑端点给出 `H(0)=H(M)=0`。定义

\[
\mathfrak D_M(H)=
\sum_{2\le n\le e^M}\frac{\Lambda(n)}{\sqrt n}H(\log n)
-\int_0^Me^{s/2}H(s)\,ds.
\]

保留极点与连续主项的抵消，得到

\[
\boxed{
\mathcal B_a(k,t)=-\mathfrak D_M(H)
-\int_0^M\frac{e^{-5s/2}}{1-e^{-2s}}H(s)\,ds.
}
\]

令 `Psi(x)=sum_{n<=x} Lambda(n)`，`E(x)=Psi(x)-x+1`。Abel 分部积分给出

\[
\mathfrak D_M(H)=-\int_0^ME(e^s)e^{-s/2}
\left(H'(s)-\tfrac12H(s)\right)ds.
\]

因此明确候选必须通过的必要检验是

\[
\begin{aligned}
&\int_0^ME(e^s)e^{-s/2}\left(H'(s)-\tfrac12H(s)\right)ds\\
&\quad-\int_0^M\frac{e^{-5s/2}}{1-e^{-2s}}H(s)\,ds
\ge\delta\|v\|_2^2-4r\|v\|_2.
\end{aligned}
\]

该候选下界仍未证明，也不足以单独替代所有正交方向上的强制性。分段光滑定义域延拓、上述边界展开与 Abel 变换尚未全部形式化。

---

## [PR #5602] CANONICAL_GAMMA_TAIL_BOUNDARY_MOMENTS

# 2026-09-05：保留边界矩的 Gamma 尾项压缩与最低模态误差预算

对应 Lean：`D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.lean`。
配套 Scribe：`Blueprint/D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.scribe.cs`。

本增补接续内部平移障碍。目标是保留实际候选的边界行为，并量化有限计算省略的 Gamma 尾项。下面第 3 节的逐频率密度误差已有 Lean 证明脚本；脚本经过数学和源码审查，尚未在本环境编译。Fourier 识别、积分预算、正投影修正、奇扇区推广和残差推论是本轮纸面推导。有限频带上的全方向估计与整个窗口 Hilbert 空间上的余维一强制性必须分别证明。

## 1. 文献接口与本轮选择

Connes、Consani、Moscovici 的 *Zeta Spectral Triples*，arXiv:2511.22755v1，第 7 节尤其 Lemma 7.3，已经证明其明确 prolate 模型在相应归一化下具有条带内的 Xi 极限；第 8 节继续要求真实最低模态的单纯偶性及与模型之间足够精确的逼近。该模型极限不能替代真实最低模态识别。

Connes、van Suijlekom 的 *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*，arXiv:2511.23257v1，提供规定分布与定义域条件下的实零点机制。Suzuki 的 *Weil's quadratic form via the screw function*，arXiv:2606.09096v1，给出实际 Weil 算子与 Friedrichs 扩张的另一种描述。使用这些结果需要保持同一算术形式及其定义域，不能将某个微分表达式的最小域直接等同于完成后的算子域。

Groskin 的 *A finite Guinand–Weil dictionary and archimedean tail order for the truncated Weil quadratic form*，arXiv:2607.02828v1，Theorem 3.2 给出有限 Galerkin Gamma 尾项的精确 Cauchy Gram 密度，Lemma 3.1 给出大频率 Gamma 包络。该文已经提供 cutoff-free 组装和区间 LDL 分解。因此本轮不宣称首次消除 Gamma 截断，也不宣称优于其现有算法。本轮从该具体核继续推导保留边界矩的有限秩修正及显式误差预算。投影与几何级数工具本身是经典工具；未作原创优先权声明。

参考地址：

- https://arxiv.org/html/2511.22755v1
- https://arxiv.org/html/2511.23257v1
- https://arxiv.org/html/2606.09096v1
- https://arxiv.org/html/2607.02828

## 2. 归一化与具体 Gamma 尾项

令窗口为 `[-L/2,L/2]`，`L=2a=log c>0`，有限素数幂 cutoff 为 `c=exp L`。定义

\[
\rho=\frac{2\pi}{L},\qquad b=\rho N,
\qquad \gamma(t)=\Re\psi_\Gamma(1/4+it/2)-\log\pi.
\]

这里 `gamma` 直接是仓库已有 `Zeta23.EF.gammaBracket`。Fourier 仍取

\[
\widehat f(t)=\int_{\mathbb R}f(x)e^{itx}\,dx.
\]

在零延拓的偶子空间上，取正交归一基

\[
\varphi_0=L^{-1/2}\mathbf1_I,\qquad
\varphi_k=(-1)^k\sqrt{2/L}\cos(\rho kx)\mathbf1_I\quad(k\ge1),
\qquad I=[-L/2,L/2].
\]

相位 `(-1)^k` 是坐标约定的一部分。删掉它会改变后面的 Cauchy 响应。令 `sigma_0=1`，`sigma_k=sqrt(2)` 对 `k>0`，并设

\[
f_v=\sum_{k=0}^Nv_k\varphi_k,\qquad
R_v(t)=\sum_{k=0}^N\frac{\sigma_kv_k}{1-(\rho k/t)^2}.
\]

逐项积分给出，对 `t>b`，

\[
\widehat f_v(t)=\frac2{\sqrt L}\frac{\sin(Lt/2)}tR_v(t).
\]

于是从 `|t|>T` 省略的真实 Gamma 能量矩阵为

\[
\boxed{v^*E_Tv=\int_T^\infty w_L(t)|R_v(t)|^2\,dt,}
\]

其中

\[
\boxed{w_L(t)=\frac{2\rho}{\pi^2}\gamma(t)\frac{\sin^2(Lt/2)}{t^2}.}
\]

这个公式也由上述 Cauchy Gram 密度经过等距偶嵌入得到。此处只处理 Gamma 积分尾项，prime 与 pole 块保持完整。真实 Weil 形式的其他部分没有被改成正核。

## 3. 已提交的逐频率全方向误差

固定任意自然数 `m`，允许 `m=0`。定义有限矩

\[
M_{2j}(v)=\sum_{k=0}^N\sigma_k(\rho k)^{2j}v_k,
\qquad
P_{m,v}(t)=\sum_{j=0}^{m-1}t^{-2j}M_{2j}(v).
\]

这些矩直接记录有限三角候选的边界偶阶导数：

\[
f_v^{(2j)}(L/2)=(-1)^jL^{-1/2}M_{2j}(v).
\]

保留矩允许候选具有非零边界值及导数。没有要求候选属于 moment-neutral 子空间。

设

\[
q(t)=(b/t)^2<1.
\]

精确有限几何余项为

\[
R_v(t)-P_{m,v}(t)
=\sum_{k=0}^N\sigma_kv_k
\frac{(\rho k/t)^{2m}}{1-(\rho k/t)^2}.
\]

因为

\[
\left(\sum_k\sigma_k|v_k|\right)^2
\le(2N+1)\sum_k|v_k|^2,
\]

有

\[
|R_v|,|P_{m,v}|
\le\frac{\sqrt{2N+1}}{1-q(t)}\|v\|_2,
\]

\[
|R_v-P_{m,v}|
\le\frac{\sqrt{2N+1}\,q(t)^m}{1-q(t)}\|v\|_2.
\]

相乘得到

\[
\boxed{
\bigl||R_v(t)|^2-|P_{m,v}(t)|^2\bigr|
\le\frac{2(2N+1)q(t)^m}{(1-q(t))^2}\|v\|_2^2.
}
\]

Lean 主声明 `even_archimedean_tail_density_jet_error` 证明将两边乘以 `|w_L(t)|` 后的精确密度不等式。量词覆盖任意 `N,m`、`L>0`、`t>rho*N` 和任意复系数向量。`N=0`、`m=0` 均包含在陈述内。该定理不假设 Gamma 的符号。

即使在 `w_L>=0` 的区域，两个 Gram 密度之差也不必正半定。因此该直接 Taylor jet 只提供双边误差，不能直接声称一个有序的正修正。

## 4. 直接 jet 的积分误差

以下使用外部 Lemma 3.1 的独立输入

\[
0<\gamma(t)\le\log t-\frac85\qquad(t\ge7).
\]

本轮没有重新运行该文用于检查 `gamma(7)>0` 的 Arb 区间程序，也没有把该输入写成新公理。它不属于本轮 Lean 主声明的前提或结论。

取 `T>=7`、`T>b`，记 `theta=b/T<1`。定义

\[
v^*E_T^{[m]}v=\int_T^\infty w_L(t)|P_{m,v}(t)|^2\,dt.
\]

逐频率界和

\[
\int_T^\infty t^{-p-2}\left(\log t-\frac85\right)dt
=T^{-p-1}\left(\frac{\log T-8/5}{p+1}+\frac1{(p+1)^2}\right)
\]

给出纸面结论

\[
\boxed{
\|E_T-E_T^{[m]}\|\le\varepsilon_m,
}
\]

\[
\varepsilon_m=
\frac{4\rho(2N+1)}{\pi^2}
\frac{\theta^{2m}}{(1-\theta^2)^2T}
\left(\frac{\log T-8/5}{2m+1}+\frac1{(2m+1)^2}\right).
\]

积分式与算子范数运输尚未写入本轮 Lean。

## 5. 正交投影给出有序的有限秩修正

为获得正半定余量，在加权 Hilbert 空间

\[
\mathcal H_T=L^2((T,\infty),w_L(t)dt)
\]

中定义

\[
h_k(t)=\frac{\sigma_k}{1-(\rho k/t)^2},
\qquad Vv=\sum_kv_kh_k.
\]

此时 `E_T=V^*V`。令 `Pi_m` 是到

\[
\operatorname{span}\{1,t^{-2},\ldots,t^{-2(m-1)}\}
\]

的正交投影，并定义

\[
\boxed{E^{\mathrm{opt}}_{T,m}=V^*\Pi_mV.}
\]

这个修正由 Gamma 核、有限带宽和明确矩空间独立构造，不使用未知最低模态。其矩阵可直接写为

\[
E^{\mathrm{opt}}_{T,m}=C^*M^{-1}C,
\]

\[
M_{ij}=\int_T^\infty w_L(t)t^{-2(i+j)}dt,
\qquad C_{ik}=\int_T^\infty w_L(t)t^{-2i}h_k(t)dt.
\]

对 `m>0`，`M` 正定：非零的 `t^{-2}` 多项式不可能在一个区间上恒零，而权密度在离散的正弦零点以外严格为正。对 `m=0` 直接令修正为零，无须求逆。

投影的最小二乘性质给出

\[
\|(1-\Pi_m)Vv\|_{\mathcal H_T}^2
\le\|R_v-P_{m,v}\|_{\mathcal H_T}^2.
\]

结合精确几何余项，得到本轮较强的纸面定理：

\[
\boxed{
0\preceq E_T-E^{\mathrm{opt}}_{T,m}
=V^*(1-\Pi_m)V\preceq\kappa_mI,
\qquad \operatorname{rank}E^{\mathrm{opt}}_{T,m}\le m,
}
\]

其中

\[
\boxed{
\kappa_m=
\frac{2\rho(2N+1)}{\pi^2}
\frac{\theta^{4m}}{(1-\theta^2)^2T}
\left(\frac{\log T-8/5}{4m+1}+\frac1{(4m+1)^2}\right).
}
\]

证明中先平方余项，使幂次从 `theta^(2m)` 改善到 `theta^(4m)`，再使用 `sin^2<=1` 和 Gamma 包络积分。正余量来自正交投影恒等式，绝不能从直接 Taylor Gram 近似擅自推断。

该定理是本轮纸面证明，尚未经 Lean 验证。实际数值实现还需对 `M`、`C` 的积分以及线性求解做区间控制。使用缩放基 `(T/t)^(2j)` 可以避免部分幂次尺度问题，但它不自动提供良好的矩矩阵条件数。

## 6. 奇扇区的相邻纸面结论

奇基可取 `(-1)^k*sqrt(2/L)*sin(rho*k*x)`，`1<=k<=N`。忽略共同的单位复相位后，其 Fourier 响应为

\[
R^-_v(t)=\sum_{k=1}^N\sqrt2v_k
\frac{\rho k/t}{1-(\rho k/t)^2}.
\]

将矩空间改为

\[
\operatorname{span}\{t^{-1},t^{-3},\ldots,t^{-(2m-1)}\}
\]

并重复平方余项证明，得到

\[
0\preceq E^-_T-E^{-,\mathrm{opt}}_{T,m}\preceq\kappa^-_mI,
\]

\[
\kappa^-_m=
\frac{2\rho(2N)}{\pi^2}
\frac{\theta^{4m+2}}{(1-\theta^2)^2T}
\left(\frac{\log T-8/5}{4m+3}+\frac1{(4m+3)^2}\right).
\]

`N=0` 时奇子空间为零空间。这个相邻结论尚未形式化。它提供奇偶两侧一致的尾项处理方式，没有证明最低模态位于偶扇区。

## 7. 对候选残差和谱分离的用途

这一节仍固定同一个有限 Galerkin 子空间。记

\[
Q_\infty^N=\widetilde Q^N+S,
\qquad \widetilde Q^N=Q_T^N+E^{\mathrm{opt}}_{T,m},
\qquad 0\preceq S\preceq\kappa_m I.
\]

对归一化明确候选 `k`，令

\[
\widetilde\mu=\langle k,\widetilde Q^Nk\rangle,
\quad\eta=\langle k,Sk\rangle\in[0,\kappa_m],
\quad\mu=\widetilde\mu+\eta.
\]

若修正矩阵已在 `k` 的正交补上具有间隔 `tilde_delta>kappa_m`，则完整 Gamma 尾项加入后，仍可取

\[
\delta\ge\widetilde\delta-\kappa_m>0.
\]

对残差，有更精确的中心化控制：由 `S^2<=kappa_m*S`，

\[
\|(S-\eta I)k\|^2
=\langle k,S^2k\rangle-\eta^2
\le\kappa_m\eta-\eta^2\le\kappa_m^2/4.
\]

因此

\[
\boxed{
r\le\widetilde r+\kappa_m/2,
\qquad
\frac r\delta\le
\frac{\widetilde r+\kappa_m/2}{\widetilde\delta-\kappa_m}.
}
\]

这里的 `r` 是完整 Gamma 积分下有限矩阵的残差。整个 Hilbert 空间上的残差还包括 Galerkin 正交补中的分量，整个空间的强制性也需要该正交补的独立下界与块间耦合控制。二者不能由以上有限矩阵估计省略。

## 8. 参数族与诊断量

若 `theta<=theta_0<1`，则

\[
\kappa_m\le A(L,N,T,\theta_0)\theta_0^{4m},
\]

\[
A=\frac{2\rho(2N+1)}{\pi^2}
\frac{\log T-8/5+1}{(1-\theta_0^2)^2T}.
\]

所以当 `0<theta_0<1` 时，选取

\[
m\ge\frac{\max\{0,\log(A/\epsilon)\}}{4\log(1/\theta_0)}
\]

足以使这个尾项预算不超过给定 `epsilon>0`。此处每个尺度的 `L,N,T` 仍显式保留，没有偷换为一个固定窗口定理。

在文献使用的 `c=100,N=200,T=800` 参数处，代入本轮公式得到

\[
\theta\approx0.34109408846,
\qquad \kappa_{32}\approx1.13078458\times10^{-62}.
\]

该数只是解析预算的高精度数值评价。没有实际组装 `Eopt`、没有认证 `M` 的条件数、没有得到新的最低特征值区间。75 组覆盖零阶、零带宽、复系数和接近带边的随机诊断均满足推导不等式；这些测试也不替代形式证明或区间证书。

## 9. 仍需消除的数学假设

本轮将具体 Gamma 尾项误差变成一个可按精度选择的有限矩预算。完整研究目标仍要求：

1. 对明确算术候选证明有限修正矩阵中的正交补下界，并控制 prime、pole 与边界贡献之间的抵消。
2. 对 Galerkin 子空间以外的全部方向给出强制性和耦合估计，将矩阵结论提升到同一 Friedrichs Weil 算子。
3. 沿无界尺度序列联合控制实际候选残差与谱间隔，使误差足以承受复频率权重，并接到文献已有 prolate 模型的 Xi 极限。

其中第 1、2 项仍然是算术承重问题。本轮没有证明新的全空间尺度实例，没有获得无界尺度的单纯偶性，也没有证明真实最低模态变换收敛到 Xi。

---

## [PR #5602] INFINITE_WEIL_COMPLEMENT_COERCIVITY

# 2026-09-06：无限 Galerkin 补空间的显式算术下界

对应 Lean：`D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage.lean`。
配套 Scribe：`Blueprint/D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage.scribe.cs`。

本节处理此前尚未控制的全部高模态方向。这里的截断参数 N 删除的是空间 Fourier 基的低阶模式；上一节的 T 截断的是组装 Gamma 积分时的连续频率变量。两种尾项不同，上一节的有限矩阵精度不能消除本节的无限维义务。

本节的无限 Cauchy 级数低频质量界已有 Lean 证明脚本。级数绝对收敛、连续性和积分可积性包含在证明内。真实 Fourier 展开识别、完整 Weil 补空间下界、含素数尺度实例和 Schur 运输是以下纸面证明，尚未全部连接成 Lean 中的算子定理。Lean 与 Scribe 编译未在本环境运行。

## 1. 文献接口与保留的对象

Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1，第 7 节和 Lemma 7.3 已给出明确 prolate 模型的 Xi 极限，第 8 节保留真实最低模态识别与单纯偶性。Connes–van Suijlekom, arXiv:2511.23257v1，提供精确分布与算子定义域条件下的实零点定理。

Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v1，Theorem 1.1 识别同一 Weil 形式的 Friedrichs 实现，并建立相关对数型形式域的紧嵌入。因此本节不将紧 resolvent 或抽象高谱发散登记为新发现。Groskin, *A finite Guinand–Weil dictionary and archimedean tail order for the truncated Weil quadratic form*, arXiv:2607.02828v1，Theorem 3.2 处理有限 Galerkin Gamma 尾项。本节使用同一 Fourier 约定，但补空间没有有限上截止。

仓库中直接可复用的 Gamma 真源为 `Zeta23.MuFields.mu_monotoneOn`、`mu_zero_le`、`neg_one_lt_mu_zero` 和 `Zeta23.mu_even`。本文 gamma=2*pi*mu，即既有 `Zeta23.EF.gammaBracket`。平移项和极点项仍来自 `literatureRHS(weilTest f f)`。未通过零点位置、RH 或目标正性构造输入。

参考：

- https://arxiv.org/html/2511.22755v1
- https://arxiv.org/html/2511.23257v1
- https://arxiv.org/html/2606.09096v1
- https://arxiv.org/html/2607.02828v1

本节矩阵元采用内积对第二变量线性的约定；相关函数与 Fourier 约定保持不变。

## 2. 全部无限 Fourier 尾部的低频泄漏界

固定 L=2a>0，I=[-L/2,L/2]，rho=2*pi/L。使用零延拓的正交归一基

\[
e_n(x)=(-1)^nL^{-1/2}e^{i\rho n x}\mathbf1_I(x),\qquad n\in\mathbb Z.
\]

令 P_N 是到 |n|<=N 的正交投影，N>=1。对任意 g 属于 P_N 的正交补，记其两侧系数为 u_j 和 v_j，对应 n=N+j+1 及 n=-(N+j+1)。Parseval 给出

\[
A=\sum_{j\ge0}|u_j|^2+\sum_{j\ge0}|v_j|^2=\|g\|_2^2.
\]

定义

\[
C(d,u)=\sum_{j\ge0}\frac{u_j}{d+j+1}.
\]

对 d>0，有逐项可求和的正上界

\[
\sum_{j=0}^{M-1}(d+j+1)^{-2}
\le d^{-1}-(d+M)^{-1}\le d^{-1}.
\]

由此和 Cauchy–Schwarz 得到绝对收敛，以及

\[
|C(d,u)|^2\le d^{-1}\sum_{j\ge0}|u_j|^2.
\]

在 |s|<=N/4 上，N+s 和 N-s 均至少为 3N/4。因此

\[
|C(N+s,u)-C(N-s,v)|^2\le\frac8{3N}A.
\]

对有限 Fourier 和逐项积分，再取 L2 极限，得到

\[
\boxed{
|\widehat g(\rho s)|^2
=\frac L{\pi^2}\sin^2(\pi s)
|C(N+s,u)-C(N-s,v)|^2.
}
\]

极限交换无需边界正则性：支撑固定在 I 时，L2 收敛蕴含 L1 收敛，且 Fourier 变换在实轴上以 sqrt(L) 倍的 L2 误差一致收敛。右侧 Cauchy 级数在该紧带上一致绝对收敛，故与同一 Fourier 极限一致。一般 L2 向量不必具有端点值。

使用 sin^2<=1 并积分，得到

\[
\boxed{
\frac1{2\pi}\int_{|t|\le R_N}|\widehat g(t)|^2dt
\le\epsilon_*\|g\|_2^2,
\quad R_N=\frac{\pi N}{2L},
\quad\epsilon_*=\frac4{3\pi^2}<\frac17.
}
\tag{IC1}
\]

Lean 主声明 `infinite_complement_low_frequency_mass` 证明 dimensionless 密度在 [-N/4,N/4] 上可积及其归一化积分界。输入是两条任意平方可和复序列，没有有限上截止、偶性、实值性、边界消失或谱间隔前提。Fourier 基展开与 Parseval 的上述识别仍为纸面桥，未冒充已形式化。

## 3. 对实际 Gamma、素数幂和极点的完整下界

记

\[
\gamma(t)=\Re\psi_\Gamma(1/4+it/2)-\log\pi.
\]

它在 |t| 上递增，且 gamma(t)>=gamma(0)>-2*pi。对完整 Friedrichs 形式域中的 g，式 (IC1) 和 Plancherel 给出

\[
q_\Gamma(g)\ge
\big[(1-\epsilon_*)\gamma(R_N)+\epsilon_*\gamma(0)\big]\|g\|_2^2.
\]

设

\[
P_a=2\sum_{2\le n\le e^{2a}}\frac{\Lambda(n)}{\sqrt n}.
\]

实际相关函数满足 |C(g,g)(s)|<=||g||_2^2，故素数项至少为 -P_a||g||_2^2。两个极点在完整奇偶空间上的精确贡献为

\[
2|\langle g,\cosh(x/2)\rangle|^2
-2|\langle g,\sinh(x/2)\rangle|^2.
\]

由于

\[
\int_{-a}^a\sinh^2(x/2)dx=\sinh a-a,
\]

极点项至少为 -2(sinh(a)-a)||g||_2^2。于是得到纸面定理：

\[
\boxed{
q_a(g)\ge\beta_{a,N}\|g\|_2^2
\quad\text{对所有 }g\in\operatorname{Dom}(q_a)\cap P_N^\perp,
}
\tag{IC2}
\]

\[
\boxed{
\beta_{a,N}=(1-\epsilon_*)\gamma\!\left(\frac{\pi N}{4a}\right)
+\epsilon_*\gamma(0)-P_a-2(\sinh a-a).
}
\]

量词覆盖无限补空间中的所有允许向量。Gamma 形式积分在其形式域中有定义；有限素数平移及极点项是 L2 上的有界形式。因此同一不等式适用于该 Friedrichs 实现，不额外假定每个向量在算子域中。对偶向量，极点的负 sinh 通道为零，可删除最后一项。

这个下界不假定补空间非负。所有常数由 a、N、Gamma 和不超过 e^(2a) 的素数幂独立给出。

## 4. 一个完全显式的模态截止族

以下初等 Gamma 下界避免在本节另用未经运行的区间 digamma 计算。令 z=alpha+ib，alpha,b>0，并设

\[
f(x)=\frac{x+\alpha}{(x+\alpha)^2+b^2}.
\]

实 digamma 部分分式级数及 H_M-log M 的极限给出

\[
\Re\psi_\Gamma(z)=\lim_{M\to\infty}
\left(\log M-\sum_{n=0}^{M-1}f(n)\right).
\]

每个单位区间上用导数积分控制左 Riemann 和误差，有

\[
\left|\sum_{n=0}^{M-1}f(n)-\int_0^Mf(x)dx\right|
\le\int_0^M|f'(x)|dx\le\frac1b.
\]

最后一个不等式来自 f 最多先增后减且最大值不超过 1/(2b)。其总变差在 alpha<=b 时等于 1/b-f(0)，在 alpha>b 时等于 f(0)，均不超过 1/b。计算积分并取极限，得到

\[
\Re\psi_\Gamma(\alpha+ib)\ge\log|\alpha+ib|-1/b\ge\log b-1/b.
\]

故对 t>0，

\[
\boxed{\gamma(t)\ge\log\frac t{2\pi}-\frac2t.}
\tag{IC3}
\]

本节的 Riemann 和、总变差及 digamma 极限论证是纸面证明，尚未写入 Lean。

令 D_a=2(sinh(a)-a)。对任意实阈值 tau，选自然数 N 满足

\[
N>\max\left\{1,\frac{8a}{\pi},
8a\exp\left(1+\frac{\tau+P_a+D_a+2\pi\epsilon_*}{1-\epsilon_*}\right)\right\}.
\tag{IC4}
\]

将 (IC3) 代入 (IC2)，直接得到 beta(a,N)>tau。因此每个尺度均有明确有限 cutoff，使其无限补空间高于指定阈值；也可沿任何无界尺度序列使用这一公式。固定 a 时 beta(a,N) 趋向正无穷。

代价必须保留：这里对素数项用了绝对值和，未利用算术抵消。该阈值可能非常大，不能据此声称已经获得可实际组装的低维全空间证书。

## 5. 含实际素数平移的具体尺度

取

\[
a=\tfrac12\log3,\qquad N=1024.
\]

素数 2 的平移距离 log2 严格小于窗口直径 log3，因此该窗口确实包含非零素数项。边界处 n=3 的相关函数贡献为零；下面仍把它计入 P_a，保持保守上界。

用 exp 的正项有限 Taylor 和可验证 log2<7/10、log3<11/10，并有 sqrt2>7/5、sqrt3>17/10。因而

\[
P_a<2\left(\tfrac12+\tfrac{11}{17}\right)=\frac{39}{17}.
\]

a<11/20，且 sinh 的正项级数给出

\[
2(\sinh a-a)
\le\frac{(11/20)^3}{3(1-(11/20)^2/20)}<\frac3{50}.
\]

pi>31/10 给出 epsilon_*<1/7。pi<22/7 给出 gamma(0)>-44/7。R_N>1024，而

\[
\gamma(1024)\ge\log(512/\pi)-1/512>4.
\]

最后一个严格界可由 e<3、sqrt3<7/4 核验：exp(9/2)<81*7/4<512/(22/7)，故 log(512/pi)>9/2。

于是

\[
\boxed{
\beta_{\log3/2,1024}>
\frac{24}{7}-\frac{44}{49}-\frac{39}{17}-\frac3{50}
=\frac{7351}{41650}>\frac16.
}
\tag{IC5}
\]

这给出含素数项窗口的整个无限高模态补空间严格正下界。没有据此断言整个 q_a>=1/6，也没有断言前 2049 个 Fourier 模态中的最低特征值单纯。该尺度结果的数学证明为本节的解析及有理数估计，不是浮点特征值实验，也尚未获得完整 Lean 算子证明。

## 6. 剩余有限问题必须保留完整耦合

若某个明确候选 k 已位于 P_NH 中，令 E=P_NH intersect k-perp，Q_N=I-P_N。对 tau=mu+delta<beta(a,N)，完整 (A) 的一个充分条件是

\[
\boxed{
\left.P_N(A_a-\tau)P_N\right|_E
-\frac1{\beta_{a,N}-\tau}
\left.P_NA_aQ_NA_aP_N\right|_E\succeq0.
}
\tag{IC6}
\]

证明是将 f=x+y 分解到 E 和 Q_NH，使用 (IC2) 后配方。只有 beta 由本节独立下界控制；上述有限矩阵不等式尚未对实际候选证明。不能把它当作已成立输入来宣布 (A) 完成。

对算子域中的有限基底，耦合 Gram 可由完整算子图像计算：

\[
G_{ij}=\langle A_ae_i,A_ae_j\rangle
-\sum_{|n|\le N}\langle A_ae_i,e_n\rangle
\langle e_n,A_ae_j\rangle.
\]

零延拓 Fourier 基属于本算子的形式域和算子域：其 Fourier 变换 O(1/|t|)，Gamma 乘子为 O(log(2+|t|))，故 Gamma 乘子作用后仍在 L2；有限平移与极点项有界。对应 Friedrichs 形式配对的表示向量是压回窗口后的这些完整算子项。该定义域识别仍是纸面桥。

同样，对有限候选，实际算子残差满足

\[
\boxed{
\|(A_a-\mu)k\|_2^2
=\|P_N(A_a-\mu)k\|_2^2+\|Q_NA_ak\|_2^2.
}
\tag{IC7}
\]

第二项不会因为有限矩阵的 Gamma 积分算得很准而消失。候选来自 prolate 模型时，还需把原模型与所选有限 Fourier 近似的误差计入，而非假设原模型已经属于 P_NH。

## 7. 本节消除的假设和下一承重边

纸面上，补空间的下界与某个阈值以上的 cutoff 存在性已被显式 (IC2)–(IC4) 替代，并有 (IC5) 的含素数实例。Lean 保存的是支撑此结论的无限序列低频质量估计，含绝对收敛与可积性；真实 Fourier/L2 接口、完整算术形式和阈值例证尚未全部形式化。

剩余承重边是对明确候选认证 (IC6) 中的有限算术块与完整耦合，并让 (IC7) 的全算子残差相对于所得谱间隔足够小。对素数项的粗绝对值处理会放大 N；下一步应保持 prime/pole/boundary 抵消，改进这两个有限矩阵量，而非继续添加抽象 Schur 包装。

未证明无界尺度的最低模态单纯偶性，未证明条件 (C)，未证明真实最低模态 Fourier 变换收敛到 Xi，未证明 RH。本节的投影和 Fourier 估计属于经典工具的具体应用，未作原创优先权声明。

---

## [PR #5602] ARITHMETIC_COUPLING_AND_PRIME3_GROUND_MODE

# 2026-09-06：具体算术耦合与一个含素数窗口的单纯偶最低模态证书

Lean：`D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.lean`。
Scribe：`Blueprint/D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.scribe.cs`。
可复验程序：`research/weil_ground_mode/certify_prime3.py`。
本次实际输出：`research/weil_ground_mode/prime3_certificate.json`。

本节将前面的无限高模态下界接到具体算术耦合，完成一个固定含素数窗口的计算机辅助余维一强制性证明。Lean 保存算术边界符号的绝对收敛、独立统一上界及逐外部模态的耦合余项。完整 Fourier/算子域识别、无限 Gram 尾项求和、区间计算的正确性及变分推论属于以下纸面与计算机辅助证明，尚未组成 Lean 内核定理。Lean 和 Scribe 编译没有在本环境运行。本文不将数值 LDL 的通过等同于 Lean 编译通过。

## 1. 同一 Weil 对象及文献接口

继续使用上一节的 L=2a、正交归一基 e_n 和 Fourier 约定。闭形式为

\[
q_a(f)=\frac1{2\pi}\int_{\mathbb R}\gamma(t)|\widehat f(t)|^2dt
+2\Re\{\widehat f(i/2)\overline{\widehat f(-i/2)}\}
-2\sum_{2\le j<e^L}\frac{\Lambda(j)}{\sqrt j}\Re C(f,f)(\log j).
\]

端点 j=e^L 若为整数，其相关函数值为零。Gamma 乘子仍是既有 gammaBracket，未改变素数、极点或边界归一化。先在紧支撑光滑核心比较 `literatureRHS(weilTest f f)`，随后取同一个闭形式的 Friedrichs 实现。有限基向量的 Fourier 变换为 O(1/|t|)，gamma(t)=O(log(2+|t|))，因此 gamma*hat(e_n) 属于 L2；有限素数平移和两个极点项有界。对应的压回窗口表示向量证明 e_n 属于该算子域。这里不要求 e_n 属于 A_a 的平方定义域。

Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1，Lemma 2.3、Proposition 3.2 和 Section 4 给出本节使用的 Fourier 矩阵计算。Suzuki, arXiv:2606.09096v1，Theorem 1.1 及形式域分析提供闭形式实现与紧 resolvent 的接口。Groskin, arXiv:2607.02828v1 已有有限矩阵的 cutoff-free 组装和区间 LDL 方法。本节保留该文献背景，新增任务是认证全部无限耦合后的余维一估计。

另检索到 Kim 等人的 arXiv:2607.24830，研究 Suzuki 算子的数值实现和第一个素数阈值。本节不把有限特征值数值稳定当作全空间证明，也不提出首创优先权声明。Connes–van Suijlekom 的实零点结论仍须承接它规定的分布、核心和算子条件；本文没有仅由自伴性直接推出实零点。

## 2. 具体算术边界符号与除差矩阵

以下令 c>=2 为整数，L=log c，omega_n=2*pi*n/L，beta_r=2r+1/2。定义

\[
\begin{aligned}
s_c(n)={}&-\frac{2\omega_n(\cosh(L/2)-1)}{\omega_n^2+1/4}\\
&-\sum_{r\ge0}\frac{\omega_n(1-e^{-\beta_rL})}{\beta_r^2+\omega_n^2}
-\sum_{2\le j<c}\frac{\Lambda(j)}{\sqrt j}\sin(\omega_n\log j).
\end{aligned}
\tag{AC1}
\]

这是一个由实际算术数据独立构造的实奇序列。它不使用未知最低特征函数或零点位置。设 K(t)=e^{-t/2}/(1-e^{-2t})。对 n!=m，相关函数偶化为

\[
C(e_n,e_m)(t)+C(e_n,e_m)(-t)
=\frac{\sin(\omega_nt)-\sin(\omega_mt)}{\pi(m-n)},\qquad 0\le t\le L.
\]

将其代入完整 Weil 形式，使用 K(t)=sum_r exp(-beta_r*t)，以及 exp(i*omega_n*L)=1，得到

\[
\boxed{A_{nm}=\frac{s_c(n)-s_c(m)}{\pi(m-n)},\qquad n\ne m.}
\tag{AC2}
\]

这一步保留 prime、pole 和 Gamma 的完整耦合。Gamma 逐项积分可由 |sin(omega*t)|<=|omega|*t 和 sum beta_r^-2<infinity 正当化。

对角元同样有精确公式。记 z_n=1/4+i*omega_n/2，psi_1 为 trigamma：

\[
\begin{aligned}
A_{nn}={}&\gamma(\omega_n)+\frac{\Re\psi_1(z_n)}{2L}
-\frac2L\sum_{r\ge0}e^{-\beta_rL}\Re(\beta_r-i\omega_n)^{-2}\\
&+\frac{4(\cosh(L/2)-1)}L\Re(1/2+i\omega_n)^{-2}\\
&-2\sum_{2\le j<c}\frac{\Lambda(j)}{\sqrt j}
\left(1-\frac{\log j}L\right)\cos(\omega_n\log j).
\end{aligned}
\tag{AC3}
\]

例如 Gamma 项可先写成

\[
\gamma(\omega_n)+\frac2L\int_0^LtK(t)\cos(\omega_nt)dt
+2\int_L^\infty K(t)\cos(\omega_nt)dt.
\]

延长第一个积分到正半轴后，剩余尾项是 -(2/L)*integral_L^infinity (t-L)K(t)cos(omega_n*t)dt，给出 (AC3)。因此对角公式中的 trigamma 系数和指数尾项符号都有直接检查。

## 3. 已提交 Lean：算术符号有独立统一界

令

\[
B_c=2\cosh(L/2)+\sum_{0\le j<c}\left|\Lambda(j)/\sqrt j\right|.
\]

则

\[
\boxed{|s_c(n)|\le B_c\quad(n\in\mathbb Z).}
\tag{AC4}
\]

Gamma 部分的证明没有假设这个上界。令 w>=0，d_j=w+2j+1/2，有

\[
\frac w{(2j+5/2)^2+w^2}
\le w\left(d_j^{-1}-(d_j+2)^{-1}\right).
\]

分母交叉相乘后，差由 (w-2j-3/2)^2 和非负余项控制。对所有有限部分和望远镜求和，再加第零项 w/(1/4+w^2)<=1，得到

\[
\sum_{r\ge0}\frac w{(2r+1/2)^2+w^2}\le2.
\]

这也给出绝对收敛。因 0<=1-exp(-beta_r*L)<=1，(AC1) 的 Gamma 级数被同一正级数支配。极点的绝对值最多为 2(cosh(L/2)-1)，有限素数项的绝对值最多为权重绝对值和。三者相加得到 (AC4)。

Lean 主声明 `arithmetic_boundary_symbol_bound` 同时保存实际 Gamma 级数的绝对收敛与 (AC4)。没有以 RH、Gamma 尾项正性、谱间隔或一个待证明的算子范数作为输入。

## 4. 已提交 Lean：保留两个边界矩的耦合余项

对支撑于 |n|<=N 的任意有限复向量 v，记

\[
a_0(v)=\sum v_n,\qquad b_0(v)=\sum s_c(n)v_n,
\qquad d_m(v)=\sum_{|n|\le N}A_{nm}v_n.
\]

每个 |m|>N 都满足

\[
\boxed{
d_m(v)=\frac{b_0(v)-s_c(m)a_0(v)}{\pi m}+R_m(v),
\quad
|R_m(v)|\le\frac{2B_cN}{\pi|m|(|m|-N)}\sum|v_n|.
}
\tag{AC5}
\]

其承重恒等式是

\[
\frac{s_n-s_m}{\pi(m-n)}-\frac{s_n-s_m}{\pi m}
=\frac{(s_n-s_m)n}{\pi m(m-n)}.
\]

Lean 主声明 `arithmetic_coupling_first_jet_error` 对任意有限整数索引集和复系数证明该误差。内部半径 N 可以是任意非负实数，外部没有有限上截止。两个边界矩没有被强行置零。

对整数 M>N，将 (AC5) 平方求和，保留边界矩，得到纸面结论

\[
\boxed{
\sum_{|m|>M}|d_m(v)|^2
\le\frac8{\pi^2M}\left(|b_0(v)|^2+B_c^2|a_0(v)|^2\right)
+\epsilon_{N,M}\|v\|^2,
}
\tag{AC6}
\]

\[
\boxed{
\epsilon_{N,M}=\frac{16B_c^2N^2(2N+1)}{\pi^2(1-N/M)^2M^3}.
}
\]

这里分别使用 |x+y|^2<=2|x|^2+2|y|^2、sum_{m>M}m^-2<=1/M，以及 sum_{m>M}m^-4<=M^-2*sum m^-2<=M^-3。没有使用更小的 1/(3M^3) 常数。有限 Cauchy–Schwarz 给出 (sum|v_n|)^2<=(2N+1)||v||^2。

因此，全部无限耦合的剩余 Gram 块有一个显式正的秩至多二修正和一个三次衰减的标量余量。它有参数 c,N,M，可以用于无界尺度族；本节并未证明所得全尺度有限矩阵均满足所需强制性。

## 5. c=3 的无限高模态块可在 N=64 处认证

取

\[
c=3,\quad L=\log3,\quad a=L/2,\quad N=64.
\]

只有素数 2 在内部真正起作用。令 h=log2，则 L<2h。压回 I 的平移 U_h 与 U_h^* 的输出支撑互不相交，输入所覆盖的两段也互不相交。因此

\[
\|(U_h+U_h^*)f\|^2=\|U_hf\|^2+\|U_h^*f\|^2\le\|f\|^2.
\]

所以实际素数项的下界改进为 -(log2/sqrt2)||f||^2。这里没有将有限素数矩阵的特征值当作整个平移算子的界。

令 eps=4/(3*pi^2)、R=pi*N/(4*a)。利用上一节无限 Fourier 补空间的低频质量界，全部高模态满足

\[
q_a(y)\ge\beta\|y\|^2,\qquad
\beta=(1-\mathrm{eps})\gamma(R)+\mathrm{eps}\gamma(0)
-\frac{\log2}{\sqrt2}-2(\sinh a-a).
\]

Gamma 的独立下界通过正级数构造：

\[
\gamma(0)=-\gamma_E-\pi/2-3\log2-\log\pi,
\]

\[
\gamma(R)\ge\gamma(0)+\sum_{j=0}^{511}
\frac{(R/2)^2}{(j+1/4)((j+1/4)^2+(R/2)^2)}.
\]

省略项全部非负。区间程序验证该下界给出的 beta>1.04126>1，同时 B_3<3。因此后续只使用精确保守常数 beta=1、B=3。与上一节 N=1024 的粗实例相比，这里真正利用了首个素数平移的支撑结构。

## 6. 实际运行的有限算术与无限耦合证书

固定 M=32768、tau=1/1000000。文件中的 CANDIDATE 是一个已固定、非零、偶的 129 维 dyadic 向量 v，分母为 2^40，索引按 -64,...,64 排列。令 k=v/||v||。候选由一次有限矩阵探索得到后被写成整数常量；认证程序不会调用特征向量求解器，也不会用未知真实最低模态替换候选。

程序以区间运算计算 (AC2)–(AC3)，并验证

\[
\mu=\langle k,A_ak\rangle
\in[5.6090783527\ldots,5.6090823856\ldots]\,10^{-8}
<10^{-7}.
\tag{AC7}
\]

上式的小数仅供显示；实际检查比较的是完整区间和精确有理阈值。程序还计算全部 64<|m|<=32768 的耦合行。每项区间被量化为分母 2^40 的 dyadic 数，逐项验证误差小于 2^-38。设量化矩阵为 C_q，其 Gram 矩阵 G_q=C_q^*C_q 以整数分块乘法精确求和，检查每一步均不会溢出。

设 e^2=2(M-N)(2N+1)*2^-76。精确有理数检查给出 ||C_q||_F<4，以及

\[
64e^2<(10^{-7}-e^2)^2,\quad e^2<10^{-7}.
\]

因此量化造成的 Gram 算子误差小于 eta=10^-7。全部 |m|>M 的尾部由 (AC6) 覆盖，其标量余项小于 1/4000000。令 s=(s_3(n))_{|n|<=64}、one=(1,...,1)，定义

\[
\overline G=G_q+\frac8{\pi^2M}(ss^*+9\,\mathrm{one}\,\mathrm{one}^*)
+\left(\frac1{10^7}+\frac1{4000000}\right)I.
\]

则完整耦合 C_N=Q_NA_a|_{P_NH} 满足 C_N^*C_N<=overline(G)。这里始终使用有界有限域映射 C_N 的 Gram，不要求 A_a^2 的定义域。

最终认证的矩阵为

\[
\boxed{
H=A_N-\tau I-\frac{\overline G}{1-\tau}+vv^*\succ0.
}
\tag{AC8}
\]

反射对称在精确算术上成立，G_q 的反射对称也由整数检查确认。程序在 e_0,e_j+e_-j 的 65 维偶块和 e_j-e_-j 的 64 维奇块分别作区间 LDL。两个块的全部主元严格为正；最小主元下端点的显示值分别约为 0.2649730942 和 0.03969194858。这些是 LDL 主元，不是矩阵特征值下界。

## 7. 区间与特殊函数误差的验证边界

有限矩阵及常数使用 mpmath.iv 的 45 位区间运算。大批耦合行只用 IEEE binary64 的基本四则运算，每一步用 nextafter 向外舍入。sin 与 arctan 使用明确区间多项式及余项，未假设系统 libm 的超越函数正确舍入。

arctan 约化后 |x|<0.501，保留 36 个奇次项，余量用 0.501^73/73<10^-23 控制。sin 约化后 |x|<3.15，保留至 49 次，余量用 3.15^50/50!<10^-38 控制。这些比较使用精确有理数核验。约化整数只用于选取等价公式，最终区间范围检查承担有效性。

digamma 和 trigamma 用 z->z+16 的精确递推以及至 B_20 的 Euler–Maclaurin 展开。对 Re Z=65/4，周期 Bernoulli 积分余项给出

\[
|R_\psi(Z)|\le\frac{|B_{20}|}{20(65/4)^{20}}<2\,10^{-23},
\qquad
|R_{\psi_1}(Z)|\le\frac{|B_{20}|}{(65/4)^{21}}.
\]

这些界来自 Hurwitz zeta 的 Euler–Maclaurin 余项在 s=1 的有限部分及其 z 导数；|periodic B_20|<=|B_20|，积分绝对值由实部控制。可对照 DLMF 25.11(iii)、5.11。c=3 时指数尾项按 9^-r 衰减，保留 32 项后显式控制省略部分。

大 Gram 的哈希是

`6f93db1396440d4cd436594dce755d341f135ce554adf89c001474a384655473`。

实际运行环境是 Python 3.13.5、NumPy 2.3.5、mpmath 1.3.0、SymPy 1.14.0。JSON 记录运行源文件 SHA-256、固定候选、预算和全部通过状态。可用 `python research/weil_ground_mode/certify_prime3.py` 复验；程序禁止 Python 的 -O 模式，以免跳过断言。

该证书依赖所列区间实现、IEEE 基本运算、整数运算和解释器。它尚未被 Lean 内核重放。本节不宣称区间软件已形式化，也没有运行 GitHub CI。

## 8. 从具体证书得到全形式域上的余维一强制性

对任意 f 属于 Dom(q_a) 且 f 与 k 正交，分解 f=x+y，其中 x=P_Nf、y=Q_Nf，则 x 与 v 正交。(AC8) 给出

\[
q_a(x)-\tau\|x\|^2\ge\frac{\|C_Nx\|^2}{1-\tau}.
\]

上一节已证明 q_a(y)>=||y||^2。因 x 属于算子域，完整混合配对是 <A_ax,y>，故配方得到

\[
\begin{aligned}
q_a(f)-\tau\|f\|^2
&\ge\frac{\|C_Nx\|^2}{1-\tau}+2\Re\langle C_Nx,y\rangle
+(1-\tau)\|y\|^2\\
&=(1-\tau)\left\|y+\frac{C_Nx}{1-\tau}\right\|^2\ge0.
\end{aligned}
\]

因此本轮纸面与区间认证共同给出固定尺度结论

\[
\boxed{
a=\tfrac12\log3,\quad f\perp k
\quad\Longrightarrow\quad
q_a(f)\ge10^{-6}\|f\|^2
\quad(f\in\operatorname{Dom}(q_a)).
}
\tag{AC9}
\]

结合 mu<10^-7，可取 delta=tau-mu>9*10^-7。紧 resolvent 与变分原理于是给出

\[
\lambda_0\le\mu<10^{-7},\qquad
\lambda_1\ge10^{-6},\qquad
\lambda_1-\lambda_0>9\,10^{-7}.
\]

最低特征值因此单纯、孤立。算子保反射，候选 k 为偶；若该唯一最低模态为奇，则它属于 k 的正交补，违背上述严格能量分离。因此最低模态为偶函数。这是完整算子的固定窗口结论，已经计入所有无限耦合方向。

## 9. 当前完成范围与剩余研究

本节在 c=3 处将单纯性、偶性和隔离从假设推进为纸面与计算机辅助证明。Lean 真源只覆盖 (AC4) 和 (AC5) 对应的实际算术收敛及余项，不包括 (AC9) 的完整内核验证。

本候选是独立固定的有限 Fourier 函数，尚未被识别为文献的 prolate 候选。没有证明它与真实最低模态的残差/间隔比达到条带极限所需尺度，也没有证明上述强制性沿 c->infinity 成立。完整最低特征值的非负性亦未由本证书推出，因为它只给出 lambda_0 的上界及其余方向的下界。

后续应利用 (AC1)–(AC6) 的参数化结构，保持算术抵消，推进无界尺度族与实际全算子残差；同时将 Fourier 识别、闭形式接口和区间有理证书接成可内核重放的证明。当前没有证明条件 (C)、真实最低模态 Fourier 变换的 Xi 极限或 RH。

参考：

- https://arxiv.org/html/2511.22755v1
- https://arxiv.org/html/2511.23257v1
- https://arxiv.org/html/2606.09096v1
- https://arxiv.org/html/2607.02828v1
- https://arxiv.org/abs/2607.24830
- https://dlmf.nist.gov/25.11
- https://dlmf.nist.gov/5.11

---

## [PR #5602] SECOND_JET_RAYLEIGH_ENCLOSURE_AND_REAL_ZEROS

# 2026-09-06：完整正下包络、射影模态误差与固定窗口的实零点极限

本节补齐上一轮 `WeilRayleighEnclosureModeCapture` 与 `WeilArithmeticCouplingSecondJet` 的理论说明，并记录本轮 `WeilArithmeticCouplingParityGram`、`certify_prime3_refined.py` 和实际输出 `prime3_refined_certificate.json`。三个 Lean owner 均有对应 Scribe。Lean elaboration、`#print axioms` 和 Scribe compiler 未在本环境执行；下面明确区分源码中的证明脚本、纸面推导和已执行的区间计算。

## 1. 三个认证数取代未量化的近基态断言

固定同一闭 Weil 形式及其自伴实现 A。设归一化候选 k 属于算子域，真实归一化最低模态 u 满足 Au=lambda*u。记 mu=q(k)。已证的变分关系为 lambda<=mu。若实际算术证书给出

\[
ell\le\lambda\le\mu\le U<T,\qquad
f\perp k\Longrightarrow q(f)\ge T\|f\|^2,
\tag{RE1}
\]

则可以直接用能量包络捕获最低模态。这里 ell 是完整算子的下界，不能用有限 Ritz 最低值充当 ell；T 的量词覆盖全部形式域中的正交方向。

令 alpha=<k,u>、v=u-alpha*k，内积对第二变量线性。由对称性及特征方程，

\[
\langle v,Ak\rangle=\overline\alpha(\lambda-\mu),\qquad
q(v)=\lambda\|v\|^2+|\alpha|^2(\mu-\lambda).
\tag{RE2}
\]

因 v 与 k 正交，得到

\[
(T-\lambda)\|v\|^2\le|\alpha|^2(\mu-\lambda).
\tag{RE3}
\]

此前 Lean owner `WeilRayleighEnclosureModeCapture` 在实不变线性算子域 D 上，以嵌入 iota:D->H 和作用 A:D->H 证明了较松的

\[
(T-U)\|v\|^2\le U-ell.
\]

该表示允许非有界算子；没有把真实 Weil 算子替换为处处有定义的有限矩阵。到实际复 Hilbert 空间的实不变域识别另需承接。本节的复数版 (RE2) 及以下射影加强为纸面证明。

若 alpha=0，则 v=u，(RE3) 与 T>lambda、||u||=1 矛盾。所以 alpha 非零。保留 (RE3) 中的重叠因子可直接得到

\[
\boxed{
\left\|\frac{u}{\alpha}-k\right\|^2
\le\frac{\mu-\lambda}{T-\lambda}
\le\frac{U-ell}{T-ell}<1.
}
\tag{RE4}
\]

第二个不等式先使用 mu<=U，再使用 x->(U-x)/(T-x) 在 x<T 上递减及 ell<=lambda。最后一个严格不等式直接来自 U<T。因此无需额外假设前一轮松预算 R=(U-ell)/(T-U)<1，也无需再将其放大为 R/(1-R)。归一化的改变只有非零标量，不改变 Fourier 变换的零点。

若某个独立模型族 k_a 已有 c_a*hat(k_a)->Xi 的条带紧集一致极限，则 (RE4) 与固定支撑 Fourier 估计给出新的充分条件

\[
\boxed{
|c_a|\sqrt{2a}\,e^{ba}
\sqrt{\frac{U_a-ell_a}{T_a-ell_a}}\longrightarrow0
\qquad(0\le b<1/2).
}
\tag{RE5}
\]

本节没有证明这条无界尺度极限。还需证明所选有限候选与文献 prolate 模型之间的相容性。

修正此前会话中的过强判断：换成 Rayleigh 包络并不证明已经绕过固定内缩平移障碍。它改变了可认证的误差量；该误差量能否在所需候选尺度族上衰减，仍是数学任务。尤其不能将另一个已知 Xi 极限的模型和本次有限候选默认为同一对象。

## 2. 已提交的二阶算术 jet 与实际反射奇性

沿用本卷 (AC1) 的真实算术符号 s_c(n)，以及

\[
A_{nm}=\frac{s_c(n)-s_c(m)}{\pi(m-n)}\quad(n\ne m),\qquad |s_c(n)|\le B_c.
\]

从

\[
\frac1{m-n}=\frac1m+\frac n{m^2}+\frac{n^2}{m^2(m-n)}
\]

得到已有 `WeilArithmeticCouplingSecondJet` 主定理：对任意复系数及 |m|>N，

\[
|d_m(v)-J_m(v)|\le
\frac{2B_cN^2}{\pi|m|^2(|m|-N)}\sum_{|n|\le N}|v_n|,
\tag{PJ1}
\]

其中

\[
J_m(v)=\frac{B_0-s_c(m)A_0}{\pi m}
+\frac{B_1-s_c(m)A_1}{\pi m^2},
\]

\[
A_0=\sum v_n,\quad B_0=\sum s_c(n)v_n,\quad
A_1=\sum nv_n,\quad B_1=\sum n s_c(n)v_n.
\]

没有将任何边界矩设为零。新增 `WeilArithmeticCouplingParityGram.arithmetic_boundary_symbol_neg` 从实际 pole、Gamma 级数和有限 von Mangoldt 正弦项逐项推出

\[
s_c(-m)=-s_c(m).
\tag{PJ2}
\]

在 c>=2 的算术范围，Gamma 级数的绝对收敛已由前置真源独立证明。

令

\[
X_m=-s_c(m)A_0+B_1/m,\qquad Y_m=B_0-s_c(m)A_1/m.
\]

则 J_m=(X_m+Y_m)/(pi*m)、J_-m=(X_m-Y_m)/(pi*m)。新增 Lean 主定理 `arithmetic_second_jet_pair_energy` 对任意复向量证明

\[
\boxed{
|J_m|^2+|J_{-m}|^2
=\frac2{\pi^2m^2}(|X_m|^2+|Y_m|^2).
}
\tag{PJ3}
\]

这是复内积空间 parallelogram identity 在既有真实算术 jet 上的应用。系数无需为偶或实，有限索引集无需反射闭合。

## 3. 两个正的矩 Gram 块及完整无限尾

(PJ3) 对正整数 m>M 求和，将 jet 能量分成两个 2x2 正半定矩块。对 (A0,B1) 的块为

\[
\frac2{\pi^2}\sum_{m>M}
\begin{pmatrix}
s_m^2/m^2&-s_m/m^3\\
-s_m/m^3&1/m^4
\end{pmatrix},
\]

对 (B0,A1) 的块为

\[
\frac2{\pi^2}\sum_{m>M}
\begin{pmatrix}
1/m^2&-s_m/m^3\\
-s_m/m^3&s_m^2/m^4
\end{pmatrix}.
\]

每项是一个实行向量的 Gram，因而正性不依赖符号猜测。|s_m|<=B 保证各项绝对可和。这里保留的交叉矩 sum s_m/m^3 可以在后续获得更锋利的证书。本次计算使用下述更保守且独立的四矩上界，并未声称实际计算了这两个精确无限块。

利用 |x+y|^2<=2|x|^2+2|y|^2、(PJ1)、(PJ3)、有限 Cauchy-Schwarz 和

\[
\sum_{m>M}m^{-2}\le M^{-1},\quad
\sum_{m>M}m^{-4}\le M^{-3},\quad
\sum_{m>M}m^{-6}\le M^{-5},
\]

得到纸面定理

\[
\boxed{
\begin{aligned}
\sum_{|m|>M}|d_m(v)|^2\le{}&
\frac8{\pi^2}\left[
\frac{B^2|A_0|^2+|B_0|^2}{M}
+\frac{B^2|A_1|^2+|B_1|^2}{M^3}\right]\\
&+\epsilon^{(2)}_{N,M}\|v\|^2,
\end{aligned}
}
\tag{PJ4}
\]

\[
\boxed{
\epsilon^{(2)}_{N,M}=
\frac{16B^2N^4(2N+1)}{\pi^2(1-N/M)^2M^5}.
}
\tag{PJ5}
\]

具体地，两个余项的平方和不超过
8*B^2*N^4*(sum|v_n|)^2/[pi^2*(1-N/M)^2*m^6]；再由 actual=jet+remainder 的二倍平方界得到 (PJ5) 中的 16。上述支配同时证明 square summability。完整无限求和仍是纸面桥，不能把 Lean 的逐模态等式标成整个 Gram 尾已内核验证。

## 4. 实际执行的 c=3 精化证书

保持 a=log3/2、N=64、M=32768 及前一节的同一 129 维 dyadic 偶候选 v，令 k=v/||v||。本轮不使用 zeta 零点或真实最低特征向量作为输入，认证程序中也没有特征向量求解器。

高模态正下界继续由实际 Gamma 正级数、prime-2 压缩平移的支撑几何及极点负通道给出。区间程序重新验证

\[
beta>1.04126433194457,\qquad B_3<3,
\]

因此在完整无限空间 Q_NH 上仍保守使用 q(y)>=||y||^2。数字 beta 只是显示，程序比较的是区间与精确常数 1。

本次不再把所有耦合条目误差统一替换为同一个最坏上界。正外部行的近似条目量化为 2^-44 的整数倍；每项的向外舍入误差半径再向上量化为 2^-60 的整数倍。令整数半径为 r_mn，则完整正负耦合误差满足

\[
\|E\|_F^2\le e^2=2\sum_{m,n}r_{mn}^2\,2^{-120}.
\]

求和采用整数运算，并在运算前核验 int64 不溢出。反射将负模态 Gram 精确识别为正模态 Gram 的逆序共轭。完整 Gram G_q 使用分块整数乘积精确构造。实际运行得到

\[
e^2=\frac{2249064940320895}
{664613997892457936451903530140172288}.
\]

设 eta=10^-10。程序以精确有理数验证

\[
e^2<eta,\qquad4\operatorname{tr}(G_q)e^2<(eta-e^2)^2.
\]

由 ||C_q||<=||C_q||_F 得到

\[
\|C^*C-G_q\|\le2\sqrt{\operatorname{tr}(G_q)}\sqrt{e^2}+e^2<eta.
\]

这把旧的 10^-7 Gram 量化预算压到 10^-10，且没有假定 BLAS 浮点矩阵乘积精确。

(PJ5) 在相同参数上的解析余项小于 9*10^-13。写 s=(s_3(n))、t=(n)、b=(n*s_3(n))、one=(1)，完整耦合 Gram 的认证上界为

\[
\overline G=G_q+
\frac8{\pi^2}\left[
\frac{ss^*+9\,one\,one^*}{M}
+\frac{bb^*+9tt^*}{M^3}\right]
+(10^{-10}+9\cdot10^{-13})I.
\tag{PC1}
\]

每个矩阵条目仍按实际 s 值取区间。PC1 控制的是 C_N^*C_N，其中 C_N=Q_NA|P_NH；没有对 A^2 的定义域作假设。

## 5. 完整算子首次在本 PR 得到双边正包络

定义精确有理常数

\[
ell=\frac{103}{2000000000},\qquad
U=\frac{560909}{10000000000000},\qquad
T=\frac1{200000}.
\tag{PC2}
\]

同一算术矩阵、同一完整耦合上界及同一固定候选通过了两个区间 LDL 检验：

\[
\boxed{A_N-ell I-\frac{\overline G}{1-ell}\succ0,}
\qquad
\boxed{A_N-TI-\frac{\overline G}{1-T}+vv^*\succ0.}
\tag{PC3}
\]

两者分别在 e0、ej+e-j 的偶块和 ej-e-j 的奇块上作非正交基的精确合同变换。最小 LDL 主元下端点的显示值分别为

| 检验 | 偶块 | 奇块 |
|---|---:|---:|
| 完整下界 | 0.0031531449201242043 | 0.03974454928419704 |
| 候选正交补 | 0.2649527465156704 | 0.03954403713951146 |

这些主元用于证明矩阵正定，不能当作矩阵的最小特征值界。

候选 Rayleigh 商仍由实际完整算术矩阵算出，其区间为

\[
mu\in[5.6090783527585\ldots,5.6090823855575\ldots]\cdot10^{-8}<U.
\]

对任意形式域向量 f=x+y，x=P_Nf、y=Q_Nf，使用 q(y)>=||y||^2，并对每个 shift=ell,T 配方。第一个矩阵检验给出所有 f 上的完整下界；第二个检验在 f 与 k 正交时消去 vv^* 项。由此得到

\[
\boxed{q(f)\ge ell\|f\|^2\quad\text{对全部 }f\in\operatorname{Dom}(q),}
\]

\[
\boxed{f\perp k\Longrightarrow q(f)\ge T\|f\|^2.}
\tag{PC4}
\]

这是纸面算子识别、无限尾估计和已执行区间证书共同给出的固定尺度结果。PC4 尚未成为 Lean 中完整算子定理。

紧 resolvent 和 min-max 原理于是给出

\[
5.15\cdot10^{-8}\le\lambda_0<5.60909\cdot10^{-8},
\qquad\lambda_1\ge5\cdot10^{-6},
\]

\[
\lambda_1-\lambda_0>4.943909\cdot10^{-6}.
\tag{PC5}
\]

唯一最低模态为偶：若其反射本征值为 -1，则该模态与偶候选 k 正交，与 lambda0<T 矛盾。实际算子还保复共轭，所以该单纯最低线可选取实偶归一化代表。

由 (RE4) 得到本次真正的模态捕获数字

\[
\boxed{
\left\|u/\langle k,u\rangle-k\right\|^2
\le\frac{U-ell}{T-ell}
=\frac{15303}{16495000}
<\left(\frac{61}{2000}\right)^2.
}
\tag{PC6}
\]

因而射影重归一化后的真实最低模态与明确候选的 L2 距离严格小于 0.0305。

## 6. 实际运行与可信计算边界

完整可复验源为 `research/weil_ground_mode/certify_prime3_refined.py`，SHA-256：

`8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0`。

实际输出为 `research/weil_ground_mode/prime3_refined_certificate.json`，其中记录精确 Gram SHA-256：

`7f4e1049624807432efe96a68fe63babbc1c3bd37f2d40600a4cddadbddb85a9`。

运行使用 Python 3.13.5、NumPy 2.3.5、mpmath 1.3.0、SymPy 1.14.0。有限矩阵采用 55 位区间；向量化耦合使用每步 nextafter 向外舍入的 binary64 基本运算。正弦、反正切、digamma、trigamma 和指数尾项保留前一节已经说明的独立余项。量化、整数 Gram 及半径平方和均有运算前的精确溢出检查。认证以全部区间严格比较通过为准，JSON 中的十进制主元仅作显示。

程序已实际运行；没有把数值探索当成认证。该计算依赖所列区间实现、IEEE 基本运算、整数实现与 Python 解释器；这些实现未被 Lean 形式化。新 Lean 文件中没有 sorry、admit 或新公理声明，但 #print axioms 未执行，不能据此称整条证明链已内核闭合。

## 7. 固定窗口的真实最低模态 Fourier 变换只有实零点

本节补上一条纸面文献桥，使固定窗口结论真正到达实零点对象。它不直接把自伴性代入 Connes-van Suijlekom 的 Theorem 6.1。该定理的精确陈述要求规定的分布二次型及三角多项式域上的本质自伴性。以下使用他们的有限维 Theorem 5.6，并显式通过同一 Weil 形式的 form core 取极限。

令 P_JH 为 |n|<=J 的完整奇偶 Fourier 空间，J>=64，A_J 为真实 q 在其上的矩阵。由 PC4，任意 J>=64 都有

\[
\lambda_{0,J}\le mu<T,\qquad\lambda_{1,J}\ge T.
\]

因此其最低特征值单纯，且由同一偶候选排除奇性。矩阵

\[
Q_J=A_J-\lambda_{0,J}I
\]

正半定并有一维偶核。其对角值为偶序列，非对角值精确为

\[
(Q_J)_{nm}=\frac{b_n-b_m}{n-m},\qquad b_n=-s_c(n)/\pi,
\quad b_{-n}=-b_n.
\]

这正是 Connes-van Suijlekom (11) 的矩阵类；减去实标量对角不改变该结构。Theorem 5.6(ii) 应用于这个实际矩阵，给出对应三角函数的 Fourier 变换只有实零点。其 [0,1] 坐标经 y=x/L+1/2 变为本卷的 e_n=(-1)^n*L^-1/2*exp(2*pi*i*n*x/L)；平移只乘无零点指数，实尺度变换及 Fourier 正负号变换保持实零点性。

实际 Weil 形式的三角多项式 form-core 性由 Connes-Consani, Spectral triples and zeta-cycles, arXiv:2106.01715v1, Lemma 2.2 及 Proposition 2.3 给出；Suzuki, arXiv:2606.09096v1, Lemma 3.1 的证明及 Section 3.2 明确复述并用于同一个 Q_W^a。故 Rayleigh-Ritz 最低值满足

\[
\lambda_{0,J}\downarrow\lambda_0.
\]

设 u_J 为相位与 u 对齐的归一化有限最低模态，分解 u_J=alpha_J*u+w_J，w_J 与 u 正交。完整算子谱间隔给出

\[
\|w_J\|^2\le
\frac{\lambda_{0,J}-\lambda_0}{T-\lambda_0}\longrightarrow0,
\]

从而 u_J->u in L2。同一固定支撑 [-a,a] 上，

\[
\sup_{z\in K}|\widehat u_J(z)-\widehat u(z)|
\le\sqrt{2a}\,e^{a\sup_K|\Im z|}\|u_J-u\|_2\longrightarrow0
\]

对每个复紧集 K 成立。u 非零，Fourier 唯一性保证 hat(u) 非恒零。分别在上、下半平面应用 Hurwitz，得到

\[
\boxed{\widehat u(z)=0\Longrightarrow z\in\mathbb R
\quad\text{在本次 }a=\tfrac12\log3\text{ 的固定窗口}.}
\tag{RZ1}
\]

这里的无限极限是 J->infinity 且 a 固定；它没有证明 a->infinity 时 hat(u_a) 的归一化极限是 Xi。RZ1 是文献有限维定理、既有 form-core 性与本次完整算术证书的纸面推论，尚未接成 Lean 的解析零点定理。

## 8. 文献比较与下一条真正承重的误差

Connes-Consani-Moscovici, arXiv:2511.22755v1, Lemma 7.3 已给出明确 prolate 模型 k_lambda 的 Xi 极限。其 Section 8 仍要求实际最低模态的简单偶性及足够精确的模型逼近。本节在一个固定含素数窗口给出后验模态估计，不宣称证明该模型的无界尺度识别。

另检索并读取了 Marcus Chuk, arXiv:2608.24827 的原始摘要。摘要报告半宽 0.8 窗口上的全空间正性和 simple-even 最低模态；这比本节 log3/2 约 0.5493 的窗口更大。因此本轮成果的价值是与仓库真实符号和可复验后验误差的接合，不是刷新最大正性窗口。该摘要所述 Landau-Widom 曲线拟合不能当作已证尺度渐近律；本轮未取得该预印本全文并逐项复核其证明。

当前新的研究重点是误差分层。量化误差和未计算尾项已能任意指定预算；但在固定 P_N 和固定候选下，完整耦合导致的能量下降不会随算术精度提高自动消失。必须区分

\[
\text{数值/尾项包络宽度},\quad
\text{保守 Schur 估计的松弛},\quad
\text{候选与真实最低线的固有偏差}.
\]

下一步应让高模态按其实际能量进入候选适配的 Schur/Feshbach 下包络，或者构造带外部修正的明确候选，并证明其与 prolate 模型的对应。继续只提高 scalar jet 阶数不保证 (RE5)。最终承重任务仍是：沿明确 a_n->infinity 的序列，独立推出 (RE1) 和 (RE5)，并识别同一 k_a 的 Xi 极限。

参考：

- Connes, Consani, Moscovici, Zeta Spectral Triples, arXiv:2511.22755v1, Sections 3, 4, 7, 8.
- Connes, van Suijlekom, Quadratic Forms, Real Zeros and Echoes of the Spectral Action, arXiv:2511.23257v1, (11), Theorems 5.6 and 6.1. The matrix and theorem pages were inspected as PDF images.
- Suzuki, Weil's quadratic form via the screw function, arXiv:2606.09096v1, Lemma 3.1 and Sections 3.2, 4.1.
- Connes, Consani, Spectral triples and zeta-cycles, Enseign. Math. 69 (2023), 93-148; arXiv:2106.01715v1, Lemma 2.2 and Proposition 2.3. The arXiv text and the publisher bibliographic record were checked.
- Marcus Chuk, Weil positivity in compact windows: certified two-sided bounds and a Landau-Widom decay law, arXiv:2608.24827, original abstract only in this round.

---

## [PR #5602] NEUMANN_COMPLETION_CANONICAL_MODEL_AND_FOURIER_OBSERVATION

# 2026-09-06: arithmetic high-mode weights, a finite prolate candidate family, and complex observation error

This append supplies the previously unwritten theory for
`WeilArchimedeanHighModeBounds` and `WeilNeumannGammaBoundary`, records the
replayed combined certificate, and explains the new
`WeilEvenFourierObservationTail` Lean/Scribe pair. It keeps the same
`literatureRHS(weilTest f f)`, `gammaBracket`, operator realization, and
Fourier convention. The results below distinguish mathematical proofs,
executed interval computations, and Lean proof scripts. No Lean elaboration,
Scribe compilation, or `#print axioms` execution was performed in this round.

## 1. Cross-PR inputs and the actual open problem

The research target remains the two missing steps in Connes-Consani-Moscovici
(CCM), *Zeta Spectral Triples*, arXiv:2511.22755v1, Section 8: simple-even
lowest modes of the actual Weil operator and sufficiently accurate
approximation by their explicit prolate model along unbounded scales.
A fixed-window certificate does not close either unbounded-scale assertion.

The following actual sources were read, including both authors' work:

* loning, PR #5326, head `3beb435bf9ca8aa35aa6079ea4033a9c2e6c9007`,
  `RH_OFFLINE_ZERO_LEE_YANG_INSTANTANEOUS_PHASE_TRANSITION_THEORY.md`,
  Sections C14-C15: a Schur floor incurs a dimension-dependent determinant
  floor. Its canonical determinant identity and boundary approximation
  remain independent obligations. This motivates controlling the scalar
  Fourier output directly rather than introducing another determinant.
* AlyciaBHZ, PR #5580, head `e1699ed18ff0e8145870c2d44374193d83766851`,
  `OrderedStableBalancedTruncation.lean`: stability and an output error
  bound concern the same constructed reduced system. Its discrete Stein
  hypotheses are not hypotheses of the unbounded Weil operator; no direct
  application of that theorem is asserted here.
* AlyciaBHZ, PR #5562, branch `work/prime-weil-foundations-probe-20260905`,
  `ScaledComplexQuadraticRowBound.lean`, blob
  `1b94a72bebdf5128d020fe755b285099a35b70a1`: complex coefficients, individual
  energy weights, and absolute series budgets are already supported.
  Its scaled-row assumptions are not automatically true for our arithmetic
  matrix. No duplicate general row-bound owner is added.

Suzuki, arXiv:2606.09096v1, already studies the same closed Weil realization,
small-window ground modes, and an inverse Neumann Laplacian in Section 8.2.
His inverse on mean-zero functions differs from the massive resolvent
comparison below. Neumann ideas, Hilbert inequalities, projection estimates,
and Schur/Feshbach methods are classical. No priority claim is made for them.

## 2. Restore the all-parity logarithmic comparison

Let L=2a>0, omega_n=2*pi*n/L, b_j=2j+1/2. Extract the Gamma part of the
existing arithmetic boundary symbol:

\[
g_L(n)=\sum_{j\ge0}\frac{\omega_n(1-e^{-b_jL})}{b_j^2+\omega_n^2}.
\]

For w>0 the positive telescoping inequality

\[
\frac{w}{(2j+5/2)^2+w^2}
\le w\left(\frac1{w+2j+1/2}-\frac1{w+2j+5/2}\right)
\]

and the zeroth term give an absolutely convergent majorant with sum at most
1+1/w. The actual symbol therefore satisfies

\[
|g_L(n)|\le1+\frac{L}{2\pi|n|}\qquad(n\ne0).
\tag{CO1}
\]

The same-source Fourier diagonal is

\[
d_n^\Gamma=\gamma(\omega_n)+\frac2L\sum_{j\ge0}
(1-e^{-b_jL})\frac{b_j^2-\omega_n^2}{(b_j^2+\omega_n^2)^2}.
\]

The absolute correction series is bounded by the preceding majorant divided
by |omega_n|, because |b_j^2-omega_n^2|<=b_j^2+omega_n^2. Thus

\[
|d_n^\Gamma-\gamma(\omega_n)|
\le\frac1{\pi|n|}+\frac{L}{2\pi^2n^2}.
\tag{CO2}
\]

The existing `arithmetic_archimedean_high_mode_bounds` proof script proves
(CO1) for the actual extracted symbol, absolute summability of the correction,
and its bound. Identification of the series with the actual diagonal is the
Fourier calculation already recorded in (AC3), using the trigamma series.

On l2(Z), H_nm=1/(m-n) for m!=n and H_nn=0 has norm at most pi.
Indeed its circle Fourier multiplier is, up to the sign convention,
i*(pi-theta) on 0<theta<2*pi. Its coefficients follow by integration by parts;
Parseval proves the bound on finite sequences and then by density on l2.
Every coordinate compression has the same bound. On |n|>=n0>=1 the complete
Gamma off-diagonal block is [D_{-g},H]/pi, so (CO1) bounds its norm by
2+L/(pi*n0), including all cross-shell couplings.

Use the previously proved gamma(t)>=log(t/(2*pi))-2/t for t>0. Let P_L be
an independently justified norm budget for the actual finite prime block,
and D_L=2*(sinh(L/2)-L/2) its actual pole negative-channel budget. Then

\[
q_a(y)\ge\sum_{|n|\ge n_0}d_o(L,n;n_0)|y_n|^2,
\tag{CO3}
\]

\[
d_o(L,n;n_0)=\log\frac{|n|}{L}-2-
\frac{2L+1}{\pi n_0}-\frac{L}{2\pi^2n_0^2}-P_L-D_L.
\]

This is a simultaneous lower form, first proved on finite Fourier vectors.
For extension to the whole high form domain, subtract the finite low
projection from a trigonometric form-core approximation. That projection
is form-norm continuous since its finitely many basis vectors are in the
operator domain. Add a constant to make the displayed diagonal weights
nonnegative and use lower semicontinuity of the weighted coefficient sum.
This also proves finiteness of that sum for a vector in the original form
domain. The actual form core is the one of Connes-Consani,
arXiv:2106.01715v1, Lemma 2.2 and Proposition 2.3. The Hilbert, Fourier and
form-domain bridges here remain paper proofs, not declarations of CO1's owner.

For c=3, L=log3 and n0=65, use P_L=log2/sqrt2. The compressed prime-2
translations have disjoint input and output segments since L<2log2; hence
the norm of their sum is at most one. At n0, (CO3) gives a constant greater
than 1.5184518986360646, verified by directed interval arithmetic. It grows
as log(|n|/65). This supplies the previous logarithmic-weighted certificate
and the odd-sector weights in the combined certificate below.

## 3. Restore the exact Neumann Gamma completion

Set I=[-a,a]. For b>0 define independently the compressed free resolvent
and the Neumann resolvent of -d^2/dx^2+b^2 by their Green kernels:

\[
R_b^F(x,y)=\frac{e^{-b|x-y|}}{2b},\qquad
R_b^N(x,y)=
\frac{\cosh(b(\min(x,y)+a))\cosh(b(a-\max(x,y)))}{b\sinh(2ba)}.
\]

The latter has zero endpoint derivative and a derivative jump -1 at x=y.
A direct hyperbolic calculation, separately for x<=y and y<=x, gives

\[
2b(R_b^N-R_b^F)(x,y)=
\frac{2\cosh(bx)\cosh(by)}{e^{bL}-1}
+\frac{2\sinh(bx)\sinh(by)}{e^{bL}+1}.
\tag{CO4}
\]

Its integrated quadratic form is the sum of the corresponding two positive
squares of boundary moments. Every kernel is bounded on the fixed compact
square and L2(I) is included in L1(I); thus the complex-valued integrated
identity follows from Fubini, not from an assumed sign of the Weil form.

The digamma partial-fraction formula gives

\[
\gamma(t)-\gamma(0)=\sum_{r\ge0}\frac{2t^2}{b_r(b_r^2+t^2)},
\qquad b_r=2r+\tfrac12.
\tag{CO5}
\]

Each summand corresponds to (2/b_r)I-2b_r R^F_{b_r}. Replace the free
resolvent by the Neumann one and use (CO4). With the orthonormal Neumann
basis nu_0=L^(-1/2) and
nu_j=sqrt(2/L)*cos(pi*j*(x+a)/L), j>=1, one obtains

\[
\begin{aligned}
q_\Gamma(f)={}&\sum_{j\ge0}\gamma(\pi j/L)|\langle\nu_j,f\rangle|^2\\
&+2\sum_{r\ge0}\left[
\frac{|\langle\cosh(b_r\,\cdot),f\rangle|^2}{e^{b_rL}-1}
+\frac{|\langle\sinh(b_r\,\cdot),f\rangle|^2}{e^{b_rL}+1}\right].
\end{aligned}
\tag{CO6}
\]

To justify every infinite expression, first subtract gamma(0)*||f||^2.
All resolvent increments, Neumann frequency increments, and boundary
squares are then nonnegative. Prove the finite-mixture identity and use
Tonelli and monotone convergence. This is an equality of extended forms;
on the actual Gamma form domain the terms on the right are finite.
The original Weil realization is unchanged. Neumann conditions belong to
a comparison operator, not to a replacement for the original domain.

On the even sector use the canonical phase-adjusted cosine basis
phi_n=(-1)^n*sigma_n*cos(2*pi*n*x/L)/sqrt(L), with sigma_0=1 and
sigma_n=sqrt2 for n>=1. Write omega_n=2*pi*n/L and
M_b(v)=sum sigma_n*v_n/(b^2+omega_n^2). Direct integration gives

\[
\langle\cosh(b\,\cdot),f\rangle
=\frac{2b\sinh(bL/2)}{\sqrt L}M_b(v).
\]

Combining the b_0=1/2 boundary square with the actual even pole contribution
2*|<cosh(x/2),f>|^2 yields

\[
q_{\Gamma+\mathrm{pole}}(f)=\sum_{n\ge0}\gamma(\omega_n)|v_n|^2
+\frac2L\sum_{r\ge0}b_r^2\eta_r(L)|M_{b_r}(v)|^2,
\tag{CO7}
\]

where eta_0=e^(L/2)-1 and eta_r=1-e^(-b_r L) for r>=1. All eta_r are
positive. Consequently the whole even high form has the lower weight

\[
d_e(L,n)=\gamma(2\pi n/L)-P_L
\ge\log(n/L)-\frac{L}{\pi n}-P_L.
\tag{CO8}
\]

At c=3 and n>=65 this is greater than 7/2. For example use log3<11/10,
pi>3, log2/sqrt2<1/2 and log(65/log3)>401/100. The last comparison follows
from e<11/4, e^(1/100)<100/99 and (11/4)^4*(100/99)<650/11. Then
401/100-11/1950-1/2>7/2. These are direct rational comparisons.
The old `WeilNeumannGammaBoundary` scripts prove (CO4), its finite real
quadratic identity and finite canonical-mixture positivity. The complex
L2, infinite-mixture and operator-domain consequences are the paper proof
above. The even weight (CO8) is not assigned to the odd Fourier sector.

## 4. Replayed combined certificate with all exterior modes retained

The actual checker is
`research/weil_ground_mode/certify_prime3_neumann_weighted.py`, SHA-256
`d6c150268b3f041701a40b804499218bd164555dede6d9c2bd30e7a10a195a99`.
It verifies the pinned dependency `certify_prime3_refined.py` before import;
its SHA-256 remains
`8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0`.

Keep the same 129-entry dyadic even candidate, N=64, M=32768, 44-bit
coefficient quantization and 60-bit directed error radii. The even block
uses (CO8); the odd block uses (CO3). For each shell a rational lower
energy is selected and verified strictly below its directed analytic
interval. All resolvent weights use T=3/250000. They therefore also bound
the correction at every shift ell<=T. The exact shell Gram and weighted
radius energies are accumulated with checked integer/rational arithmetic.
For each sector, if t is the weighted squared Frobenius norm of the
quantized matrix and e its weighted error energy, the checks

\[
e<\eta,\qquad4te<(\eta-e)^2
\]

prove a Gram norm error below eta. This follows by applying the ordinary
Gram perturbation identity to W^(1/2)C; it does not multiply an unweighted
matrix inequality by a noncommuting weight. The entire |m|>M tail uses
the prior second-jet four-moment positive majorant, with scalar budget
9e-13, divided by the relevant energy denominator at M+1.

The weighted Gram error budgets are 4/152587890625 (even) and
8/152587890625 (odd). The sum of the integer shell Grams has exactly the
previous hash `7f4e1049624807432efe96a68fe63babbc1c3bd37f2d40600a4cddadbddb85a9`.
No zero data or eigensolver is used. All final positive LDL tests were
executed; the entire final output was reproduced exactly in a second run.
A failed intermediate LDL search is not evidence of a negative eigenvalue.

Let k be this fixed candidate normalized in L2. The final rational bounds are

\[
\ell=\frac{2252813807}{40960000000000000},\quad
U=\frac{560909}{10000000000000},\quad T=\frac3{250000}.
\tag{CO9}
\]

The even full-lower test, even k-orthogonal test, and odd test are strictly
positive. Their displayed minimum LDL pivots are respectively
0.003202644247409436, 0.26802217563245934, and 0.040988013296152585.
These pivots prove positivity, not eigenvalue lower bounds. Weighted square
completion on the entire form domain gives

\[
q(f)\ge\ell\|f\|^2,\qquad f\perp k\Longrightarrow q(f)\ge T\|f\|^2.
\]

The odd lower bound T also exceeds ell, so the full lower bound covers both
parities. The actual Rayleigh interval is below U. Compact resolvent and
min-max give a simple isolated even lowest line, with

\[
5.50003370849609375\cdot10^{-8}\le\lambda_0<5.60909\cdot10^{-8},
\quad\lambda_1\ge1.2\cdot10^{-5}.
\]

The existing projective argument (RE4) consequently gives

\[
\left\|u/\langle k,u\rangle-k\right\|^2
\le\frac{44669457}{489267186193}<\frac1{10000}.
\tag{CO10}
\]

This improves the earlier 0.01475 bound to 0.01 for the same candidate and
window. The preceding Neumann-only replay had threshold 1/200000 and bound
0.02; it did not improve 0.01475. The successful improvement uses different
justified weights in the two parity sectors. The full operator theorem
remains a paper/computer-assisted result, not a Lean kernel-certified result.

## 5. The new Lean estimate controls the actual complex Fourier observable

For n>0 direct integration in the same basis gives

\[
\widehat\phi_n(z)=
\frac{2\sqrt{2/L}\,z\sin(Lz/2)}{z^2-(2\pi n/L)^2}.
\tag{CO11}
\]

The paired positive and negative modes cancel the leading inverse-frequency
term. Let y=sum_{n>N}v_n phi_n be any even L2 tail, N>=1. If L*|z|<=pi*N,
put w=L*z/(2*pi); then |n^2-w^2|>=3*n^2/4. The identity

\[
\frac1{3x^3}-\frac1{3(x+1)^3}-\frac1{(x+1)^4}
=\frac{6x^2+4x+1}{3x^3(x+1)^4}\ge0
\]

proves sum_{n>N}n^(-4)<=1/(3N^3), including convergence. Young's inequality
and this positive majorant prove absolute convergence of the Cauchy series
for every square-summable complex v. Finite Cauchy-Schwarz followed by its
sum limit proves

\[
\boxed{|\widehat y(z)|^2\le
\frac{8L^3}{27\pi^4N^3}|z\sin(Lz/2)|^2\|y\|_2^2.}
\tag{CO12}
\]

`WeilEvenFourierObservationTail.even_exterior_fourier_observation_bound`
proves absolute convergence and the precise normalized coefficient-series
inequality. There is no upper exterior cutoff or assumed boundary
cancellation. To identify that response with the actual L2 Fourier tail,
use Parseval and convergence of the finite cosine sums in L2(I), hence L1(I).
Their transforms converge at each complex z by Cauchy-Schwarz on the fixed
window. Equation (CO11) identifies the finite sums, and the proved absolute
series convergence identifies their limit. This last Fourier-space bridge
is a paper proof rather than a second hidden Lean assumption.

On |z|<=R, |Im z|<=b, use |sin(Lz/2)|<=exp(bL/2) to obtain

\[
|\widehat y(z)|\le\sqrt{\frac8{27\pi^4}}L^{3/2}R e^{ba}N^{-3/2}\|y\|_2.
\tag{CO13}
\]

When a certified high energy is at least beta*||y||^2, the squared
observation budget is divided by beta. This controls the entire exterior
observation. It does not assert that the low component of a ground-mode
error is small, or that exp(ba) has disappeared.

## 6. Fix the Mellin normalization before identifying Xi

Use the exact standard definition Xi(z)=xi(1/2+iz),
xi(s)=s*(s-1)*pi^(-s/2)*Gamma(s/2)*zeta(s)/2, and dx=du/u.
CCM (7.1)-(7.2) write

\[
h(u)=\frac\pi2u^2(2\pi u^2-3)e^{-\pi u^2},\qquad
\mathcal E h(u)=u^{1/2}\sum_{m\ge1}h(mu).
\]

For our chosen Haar and Fourier normalization, the exact scalar is checked
by a Mellin calculation, not inferred from a zero plot:

\[
\int_0^\infty h(t)t^{s-1}dt
=\frac{s(s-1)}8\pi^{-s/2}\Gamma(s/2).
\tag{CO14}
\]

For Re s>1 the absolute sum-integral interchange gives

\[
\int_0^\infty\mathcal E h(u)u^{s-1/2}\frac{du}{u}=\xi(s)/4.
\]

The written h is self-Fourier, has h(0)=0 and integral zero. Poisson
summation gives E h(u)=E h(1/u), and its Gaussian tail gives entire Mellin
continuation. Hence the inverse Fourier kernel for our Xi is

\[
\Phi(x)=4\mathcal E h(e^x),\qquad\widehat\Phi=\Xi.
\tag{CO15}
\]

This agrees with the theta kernel already written in this volume. The
factor 4 corrects a scalar mismatch when importing the literal h in CCM;
it does not alter zeros or invalidate a statement made only up to a scalar.
A numerical check at z=0 gave the ratio 1/4 for the unscaled transform;
that check is a diagnostic, while (CO14) supplies the proof.

## 7. An explicit finite dyadic prolate family with the correct strip limit

This construction is separate from the fixed 129-entry certificate vector.
Take lambda=e^a along the integers lambda>=2, so the arithmetic cutoff
c=lambda^2 is integral and tends to infinity. Use the canonical spheroidal
functions ps_n^0(x/lambda;(2*pi*lambda^2)^2) in the convention of CCM (7.10).
The explicit normalizations

\[
h_{0,\lambda}=2^{-1/2}\lambda^{-1/2}\operatorname{ps}_0^0,
\qquad h_{4,\lambda}=3\,2^{-1/2}\lambda^{-1/2}\operatorname{ps}_4^0
\]

have the Hermite limits in CCM (7.11)-(7.12). Set I_j(lambda)=integral of
h_{j,lambda} over [-lambda,lambda] and

\[
h_\lambda=\frac{\sqrt3}{2^{11/4}}
\left(h_{4,\lambda}-\frac{I_4(\lambda)}{I_0(\lambda)}h_{0,\lambda}\right).
\tag{CO16}
\]

The first prolate mode has positive integral, so the denominator is nonzero.
CCM Lemma 7.2 and its Fourier-eigenvalue argument give
I_j(lambda)=h_j(0)+O(lambda^-2). Thus (CO16) has integral zero and
sup_{[-lambda,lambda]}|h_lambda-h|<=C*lambda^-2 for a fixed finite C at
large lambda. This is the published prolate approximation input, not a
new Lean theorem and not a statement about the unknown Weil ground mode.

Define, with zero extension outside [-a,a],

\[
p_a(x)=4e^{x/2}\sum_{1\le m\le\lambda e^{-x}}h_\lambda(me^x),
\qquad p_a^+(x)=\frac{p_a(x)+p_a(-x)}2.
\tag{CO17}
\]

There are at most lambda^2 summands. Evenization is explicit: finite prolate
Fourier eigenvalues need not coincide, so reciprocal symmetry of this
finite model is not assumed.

Retain the omitted Gaussian terms when comparing (CO17) with (CO15).
For u in [lambda^-1,lambda], monotonicity of t^4*exp(-pi*t^2) on t>=1 and
integration by parts give

\[
|\mathcal E h_\lambda(u)-\mathcal E h(u)|
\le u^{-1/2}\bigl(C/\lambda+R_H(\lambda)\bigr),
\]

\[
R_H(\lambda)=\pi^2e^{-\pi\lambda^2}
\left(\lambda^5+\frac{\lambda^3}{2\pi}
+\frac{3\lambda}{4\pi^2}+\frac3{8\pi^3\lambda}\right).
\tag{CO18}
\]

For some explicit finite D, R_H(lambda)<=D/lambda for lambda>=1; each
polynomial-Gaussian factor has a bounded maximum. Consequently
|p_a(x)-Phi(x)|<=4(C+D)e^-a*e^(-x/2) inside the window. Its squared L2
error is at most 16(C+D)^2*e^-a. The exterior Phi tail is double-exponential.
In particular ||p_a^+|| is bounded by a constant B independent of large a.
For every b<1/2, weighted integration of the same bound gives

\[
\sup_{|\Im z|\le b}|\widehat{p_a^+}(z)-\Xi(z)|
\le C_b e^{-(1/2-b)a}.
\tag{CO19}
\]

The integrals on the negative and positive half-windows are respectively
(e^((1/2+b)a)-1)/(1/2+b) and (1-e^(-(1/2-b)a))/(1/2-b), multiplied by
4(C+D)e^-a. Evenization averages the bounds at z and -z. These formulas
justify the claimed strip rate without discarding a nonzero Gaussian tail.

Now project onto the actual canonical even Fourier space P_N. Its
coefficients are explicit finite integrals:

\[
b_{a,j}=4\sum_{m=1}^{\lambda^2}
\int_{-a}^{\log(\lambda/m)}e^{x/2}h_\lambda(me^x)\phi_j(x)\,dx.
\tag{CO20}
\]

Because phi_j is even these also equal the coefficients of p_a^+.
Set d_{a,j}=2^-p*floor(2^p*b_{a,j}+1/2), and define the finite dyadic model
p_tilde_a=sum_{j=0}^N d_{a,j} phi_j. Rounding gives an L2 error at most
sqrt(N+1)*2^-p. Applying (CO13) to the entire projection tail gives, on
|z|<=R and |Im z|<=b with LR<=pi*N,

\[
\begin{aligned}
|\widehat{\widetilde p_a}(z)-\Xi(z)|\le{}&
C_b e^{-(1/2-b)a}
+\sqrt{\frac8{27\pi^4}}L^{3/2}R e^{ba}N^{-3/2}B\\
&+\sqrt{L(N+1)}e^{ba}2^{-p}.
\end{aligned}
\tag{CO21}
\]

For example the explicit choices

\[
N_a=\lceil(a+1)e^{a/3}\rceil,\qquad
p_a^{\rm bits}=\left\lceil\frac{2a/3+2\log(a+1)}{\log2}\right\rceil
\tag{CO22}
\]

give, on every compact substrip rectangle,

\[
\boxed{\sup_{|z|\le R,|\Im z|\le b}
|\widehat{\widetilde p_a}(z)-\Xi(z)|
\le C_{R,b}e^{-(1/2-b)a}.}
\tag{CO23}
\]

Indeed N_a+1<=3(a+1)e^(a/3) for a>=log2. The projection term then has the
same exponential rate, and the rounding term is at most sqrt6 times that
rate. The pole-free band condition holds eventually for each fixed R.
Xi(0)>0, also seen from the positive Phi on x>=0, shows p_tilde_a is nonzero
eventually. With c_a=||p_tilde_a|| and k_a=p_tilde_a/c_a, (CO23) proves
c_a*hat(k_a)->Xi for this specified family.

(CO22) is a resolution sufficient for the function limit, not a sufficient
resolution for the arithmetic spectral certificate. One may choose any
larger N and choose p so that
sqrt(L*(N+1))*2^-p<=exp(-a/2); then the same rate is retained. Resolving an
exponentially small arithmetic gap may require vastly more precision.
No executable certified evaluator for all the prolate integrals in (CO20)
is asserted here. Their definition and analytic approximation are explicit;
their interval implementation remains a separate numerical obligation.
The old certified k at c=3 is not identified with (CO20).

## 8. A directional Schur estimate for the same Fourier observable

The following paper estimate specifies what the remaining arithmetic work
must control. It is not an assertion that its certificates hold at every
scale. Suppose the actual same candidate has been certified to satisfy
ell<=lambda<=mu<=U<T, q(f)>=T||f||^2 on k-perp, and the simple even ground
mode u has norm one. Set alpha=<k,u> and w=u/alpha-k. The earlier projective
argument proves alpha!=0, w perpendicular to k, and

\[
q(w)-\lambda\|w\|^2=\mu-\lambda,\quad
\|w\|^2\le\frac{\mu-\lambda}{T-\lambda}<1.
\]

It follows, retaining the actual energy instead of just the gap, that

\[
q(w)-\ell\|w\|^2\le U-\ell.
\tag{CO24}
\]

Assume k lies in P_NH. Put x=P_Nw, y=Q_Nw, C=Q_N A|P_NH, and let
D=diag(d_e(L,n)-ell), n>N, have a strictly positive lower bound. Suppose
an actual complete coupling majorant Gbar>=C^*D^-1 C has been certified,
and the finite matrix

\[
H=A_N-\ell I-\overline G+\rho kk^*,\qquad\rho>0,
\]

is positive definite. Since x is perpendicular to k, weighted completion
and (CO24) give

\[
\langle x,Hx\rangle+
\|D^{1/2}y+D^{-1/2}Cx\|^2\le U-\ell.
\tag{CO25}
\]

On the even space the actual complex Fourier functional has representer
g_z(t)=cos(conj(z)*t), since the inner product is linear in the second
argument. Let g_P and g_Q be its two components and set

\[
h_z=P_{k^\perp}(g_P-C^*D^{-1}g_Q),\qquad
\mathcal D_a(z)=\langle h_z,H^{-1}h_z\rangle
+\langle g_Q,D^{-1}g_Q\rangle.
\tag{CO26}
\]

Writing the Fourier output in the two coordinates of (CO25) and applying
Cauchy-Schwarz in their direct-sum energy norm proves

\[
\boxed{|\widehat w(z)|^2\le(U-\ell)\mathcal D_a(z).}
\tag{CO27}
\]

All high pairings are legitimate: the original form domain is included
in the D form domain, C has finite domain and l2 images, and D^-1 is
bounded. The second term of (CO26) has the explicit N^-3 observation
bound (CO12), divided by the lower bound of D. The first term is a
finite inverse quadratic form with an arithmetic high-mode correction.
That correction still requires an interval evaluation and an infinite-tail
bound; it is not assigned a numerical value in this round.

For the family (CO20), a sufficient remaining arithmetic target is

\[
c_a^2(U_a-\ell_a)\sup_{z\in K}\mathcal D_a(z)\longrightarrow0
\tag{CO28}
\]

for every compact K in |Im z|<1/2, together with the actual full-space
coercivity certificates used in (CO24)-(CO25). This is a directly observed
error budget, not a determinant floor raised to the realization dimension.
It can be used with the repository's rectangle Rouche machinery when
strict boundary lower bounds and errors are actually available. No such
all-rectangle certificate or ground-family limit is claimed here.

## 9. What has and has not been removed from the problem

The executed fixed-window estimate has genuinely improved. On paper, the
actual high-mode weights have an independent arithmetic proof, and an
explicit finite dyadic prolate family now has a calibrated Xi limit with
quantified projection and rounding errors. The new Lean increment proves
the infinite complex observation-tail bound with absolute convergence.

The first open research obligation is still to certify the *same* family
(CO20) against the actual Weil operator along an unbounded scale sequence,
and make (CO28), or the earlier weighted projective bound, tend to zero.
No finite matrix positivity assumption has been promoted to an arithmetic
theorem without its certificate. Neither the Neumann comparison nor the
new observable estimate is claimed to evade the earlier shift barrier.
The remaining low-mode error, prime cancellations, and prolate integral
certification require further work. No RH proof, universal simple-even
family theorem, or end-to-end Lean real-zero limit is asserted.

References used for this append:

* Connes, Consani, Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1,
  (7.1)-(7.12), Lemmas 7.2-7.3 and Section 8. The literal normalization was
  independently checked by (CO14), and the omitted Gaussian tail is retained.
* Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v1,
  Theorems 1.1-1.4 and Section 8.2. Results stated under RH are not used.
* Connes, Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715v1,
  Lemma 2.2 and Proposition 2.3, for the actual form core.
* Dusson, Sigal, Stamm, *Analysis of the Feshbach-Schur method for the Fourier
  spectral discretizations of Schrodinger operators*, arXiv:2008.10871v2.
  The elimination principle is classical; its Schrodinger regularity
  assumptions are not silently imported into the Weil problem.
* DLMF 5.7.6, digamma partial fractions, and the Gamma integral and recurrence,
  for the elementary resolvent and Mellin computations.

---

## [PR #5602] ARITHMETIC_FOURIER_DUAL_TAIL_AND_CERTIFIED_ZERO_COUNT

# 2026-09-06: effective arithmetic dual observations and a counted simple ground-transform zero

Lean: `D5/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail.lean`.
Scribe: `Blueprint/D5/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail.scribe.cs`.
Executed checker: `research/weil_ground_mode/certify_prime3_directional.py`.
Actual replay output: `research/weil_ground_mode/prime3_directional_certificate.json`.

The open problem is still CCM, arXiv:2511.22755v1, Section 8: prove simple-even
actual Weil ground modes and sufficient approximation by the explicit prolate
model on an unbounded scale family. The present increment makes the arithmetic
correction in (CO26) effectively computable, then certifies a local zero count
for the actual fixed-window ground transform. It does not identify that zero
with a Xi zero. The infinite operator/domain and variational implications
below are paper proofs; the new Lean script proves the concrete infinite
arithmetic series estimate. Lean and Scribe compilation were not run.

## 1. Cross-author input determines the mathematical deliverable

loning's merged PR #5326, head 3beb435bf9ca8aa35aa6079ea4033a9c2e6c9007,
separates a boundary Rouché inequality from a Schur floor and distinguishes
behavioral Hankel minimality from determinant preservation. His #5296 also
keeps dominant-channel boundary transversality separate from spectral
splitting. These are relevant warnings against inserting an unproved
arithmetic determinant or taking absolute values before signed couplings
have been combined.

AlyciaBHZ's draft #5882, head e89269583d0b05b24dca01939ae7245b62b12c35 at
inspection, already develops complex projective Rayleigh recovery and sharp
scalar readout bounds. We do not add a second generic projection owner.
The preceding (CO26)-(CO28) specifies the actual Weil Fourier correction
but had no evaluated arithmetic dual tail. Here the new owner uses the
existing actual symbol, proves an infinite-tail rate, and feeds a checker
that produces a strict complex-boundary zero-count certificate.
Classical Schur, Cauchy-Schwarz and Rouché principles are not claimed as
new results. The specific arithmetic evaluation and its quantified consumer
are the mathematical deliverable.

## 2. Keep the actual even coordinate normalization

Use the same L=2a=log(c), plus-sign Fourier transform, and basis e_n of (AC2).
For the unnormalized even basis set psi_0=e_0 and psi_n=e_n+e_-n for n>0.
Its mass matrix is M_0=diag(1,2,...,2). For an exterior positive index m>N,
the coupling row C^+ from low even coordinates to the e_m coordinate is

\[
 C^+_{m0}=-\frac{s_c(m)}{\pi m},\qquad
 C^+_{mn}=\frac{2(ns_c(n)-ms_c(m))}{\pi(m^2-n^2)}\quad(n>0).
 \tag{DZ1}
\]

This follows by adding the actual entries A_mn and A_m,-n and using the
proved oddness of s_c. In particular no abstract row is substituted.
The Fourier rows are

\[
 f_0(z)=\frac{2\sin(Lz/2)}{\sqrt L\,z},\qquad
 f_n(z)=\frac{4z\sin(Lz/2)}{\sqrt L\,(z^2-(2\pi n/L)^2)}\quad(n>0).
 \tag{DZ2}
\]

They equal the entire transforms away from the displayed removable poles.
The certified disk below lies strictly away from those poles. Even high
coordinates have energy 2*sum D_m*|y_m|^2 and readout sum f_m*y_m. Thus the
pure high dual energy has the factor 1/2 in sum |f_m|^2/(2D_m), while the
low correction is sum C^+_mn*f_m/D_m with no additional factor two.

## 3. New Lean theorem: the actual arithmetic dual tail is summable

Let c>=2, 0<=n<M be natural numbers, m=M+j+1, energy(j)>=beta>0, and
w be complex with |w|<=M/2. Define the explicit summand

\[
 T_j=\frac{ns_c(n)-ms_c(m)}{(m^2-n^2)\,\operatorname{energy}(j)\,(m^2-w^2)}.
\]

The existing arithmetic source proves |s_c(n)|<=B_c independently from its
prime, pole and absolutely convergent Gamma terms. The new main declaration
`arithmetic_even_fourier_dual_tail_bound` proves

\[
 \boxed{\sum_{j\ge0}|T_j|<\infty,\qquad
 \left|\sum_{j\ge0}T_j\right|\le
 \frac{2B_c}{3\beta M(M-n)}.}
 \tag{DZ3}
\]

No spectral gap, zero configuration, desired dual bound or Xi convergence
is an input. The energy hypothesis is just an explicit positive scalar
floor for the chosen diagonal comparison weights. Their applicability to
an actual operator must be proved independently, as (CO8) does here.

For completeness, the proof uses the exact difference of squares:

\[
 \left|\frac{ns_c(n)-ms_c(m)}{m^2-n^2}\right|\le\frac{B_c}{m-n},
 \quad |m^2-w^2|\ge\frac34m^2,
 \quad m-n\ge\frac{M-n}{M}m.
\]

Consequently |T_j|<=4*B_c*M/(3*beta*(M-n))*m^(-3). The identity

\[
 \frac1{2x^2}-\frac1{2(x+1)^2}-\frac1{(x+1)^3}
 =\frac{3x+1}{2x^2(x+1)^3}\ge0\quad(x>0)
\]

proves both summability and sum_{m>M}m^(-3)<=1/(2M^2), by bounded positive
partial sums and telescoping. Applying the triangle inequality to the
absolutely convergent complex series gives (DZ3).

For the physical observation put w=L*z/(2*pi), and t_0=1, t_n=2 for n>0.
Combining (DZ1)-(DZ3) gives the effective missing dual component

\[
 \boxed{\left|\sum_{m>M}\frac{C^+_{mn}f_m(z)}{D_m}\right|
 \le\frac{2t_nB_cL^{3/2}}{3\pi^3\beta M(M-n)}
 |z\sin(Lz/2)|.}
 \tag{DZ4}
\]

The pure high component follows from the previously proved even observation
bound, equivalently from (DZ2) and sum_{m>M}m^(-4)<=1/(3M^3):

\[
 \sum_{m>M}\frac{|f_m(z)|^2}{2D_m}
 \le\frac{8L^3}{27\pi^4\beta M^3}|z\sin(Lz/2)|^2.
 \tag{DZ5}
\]

Both inequalities cover the entire uncomputed tail, for arbitrary complex
z in the stated band, and retain the exponential complex-frequency weight.

## 4. Constrain the low inverse to the actual candidate-orthogonal space

Let ell<=lambda_0<=mu<U<T be certified for the same normalized candidate k
and actual lowest eigenvector u. Put alpha=<k,u> and e=u/alpha-k. The
projective argument in (RE2)-(RE4) gives alpha!=0, e perpendicular to k,
and ||e||^2<1. Its exact energy identity therefore yields

\[
 q(e)-\ell\|e\|^2=(\mu-\lambda_0)
 +(\lambda_0-\ell)\|e\|^2\le U-\ell.
 \tag{DZ6}
\]

Use explicit high weights D_m=beta_m-T>0. They also bound the high part of
q-ell*||.||^2, since ell<T. In the coordinates of Section 2 suppose the
complete weighted coupling satisfies 2*(C^+)^*D^-1*C^+<=Gbar, and put
S=A_even-ell*M_0-Gbar. For e=x+y, Schur completion gives

\[
 x^*Sx+2\sum_{m>N}D_m|y_m+(C^+x)_m/D_m|^2\le U-\ell.
 \tag{DZ7}
\]

For the actual dyadic candidate v, v_0 is nonzero. Set p_i=2v_i/v_0 and
let P have columns E_i-p_i*E_0, i=1,...,N. This parameterizes exactly the
low space perpendicular to k in the correct mass matrix. Define

\[
 J=P^*SP,\qquad
 a_n(z)=f_n(z)-\sum_{m>N}C^+_{mn}f_m(z)/D_m,\qquad h(z)=P^Ta(z).
\]

When the actual J is positive definite, Cauchy-Schwarz in the direct-sum
energy coordinates of (DZ7) gives

\[
 \boxed{|\widehat e(z)|^2\le(U-\ell)\mathcal D(z),\qquad
 \mathcal D(z)=h(z)^*J^{-1}h(z)+\sum_{m>N}\frac{|f_m(z)|^2}{2D_m}.}
 \tag{DZ8}
\]

J is real symmetric. Thus the row-functional conjugation convention gives
the same inverse quadratic form in (DZ8). This removes the candidate line
exactly rather than paying for an arbitrary lifted inverse direction.
All high pairings are well-defined: the high form dominates D, D^-1 is
bounded, C^+ has finite domain and square-summable images, and (DZ3)-(DZ5)
prove the needed dual convergence. No domain of A^2 is assumed.

## 5. Executed arithmetic realization at c=3

Keep L=log3, N=64, M=32768, and the same fixed 129-entry even dyadic
candidate from `certify_prime3_refined.py`. The checker re-certifies

\[
 \ell=\frac{11}{200000000},\quad
 U=\frac{560909}{10^{13}},\quad T=\frac1{200000}.
 \tag{DZ9}
\]

The even high weights use (CO8). The odd threshold is rechecked using the
original all-parity lower bound beta>1 and full unweighted coupling.
Nine positive-mode shells have integer endpoints 65..128, 129..256, ...,
16385..32768. Their dyadic floors are chosen strictly below the directed
interval for log(n/L)-L/(pi*n)-log2/sqrt2 at the first shell index; this
lower expression is increasing. Every resolvent uses beta_shell-T, so the
same majorant also applies at ell. The far energy after subtraction of T
is bounded below by 502427869/51200000.

Four interval LDL tests pass: odd threshold, even full lower, even
candidate-orthogonal threshold, and the exact constrained J. They establish
the hypotheses used in (DZ6)-(DZ8) with every omitted high mode accounted
for. Their pivots certify positivity and are not eigenvalue lower bounds.
The resulting state-space bound is only ||e||^2<=10909/49450000<1/2500.
This is deliberately not advertised as an improvement of (CO10); the goal
is the actual scalar output near a zero.

All quantized Gram products use exact integers and checked intermediate
int64 bounds. The ordinary Gram hash remains
`7f4e1049624807432efe96a68fe63babbc1c3bd37f2d40600a4cddadbddb85a9`.
The weighted and unweighted error budgets are respectively
4/152587890625 and 1/10^10; the full second-jet scalar tail is below 9/10^13.

A new exact endpoint accumulator avoids unchecked floating reductions in
the directional sums. It decodes each finite binary64 endpoint as a signed
integer significand times a power of two, shifts to a common exponent,
adds Python integers, and converts the exact result outward into iv only
at the end. Signed zero and subnormal inputs are handled. Thirty-four
regressions against exact Fraction sums, including severe cancellation,
pass. The interval primitives, special-function remainders and interpreter
remain trusted numerical infrastructure, not Lean-certified software.

## 6. A strict complex-disk Rouché certificate

Let F=Fourier(u/alpha), K=Fourier(k), and set the exact rational center and
radius

\[
 z_0=\frac{2827}{200}=14.135,\qquad r=\frac1{250}=0.004.
\]

The checker encloses (DZ8) on the entire complex square
|Re z-z_0|<=r, |Im z|<=r containing the closed disk. The band L*|z|<pi*N
is separately checked. Computed quantities satisfy

\[
 \sup\mathcal D(z)<0.536805,\qquad
 \sup|F(z)-K(z)|<2.42\cdot10^{-5}.
 \tag{DZ10}
\]

The entire high observation energy is at most 4.601986*10^-7, and each
uncomputed dual correction is at most 1.995*10^-10. These are rounded
outward displays of the directed bounds; the verifier uses the full
interval comparisons.

Use the independently computed affine function
Q(z)=K(z_0)+K'(z_0)*(z-z_0). The actual candidate gives

\[
 K(z_0)=2.3040934104782876\ldots\cdot10^{-6},\quad
 K'(z_0)=0.0101016602716698139\ldots>0.
\]

On the disk boundary,

\[
 |Q(z)|\ge r|K'(z_0)|-|K(z_0)|>3.81\cdot10^{-5}.
 \tag{DZ11}
\]

Since ||k||=1 and integral_I x^4 dx=L^5/80, differentiating the compactly
supported Fourier integral twice gives the uniform Taylor remainder

\[
 |K(z)-Q(z)|\le\frac{r^2}{2}e^{ar}\sqrt{L^5/80}
 <1.14\cdot10^{-6}.
 \tag{DZ12}
\]

Equations (DZ10)-(DZ12) imply |F-Q|<|Q| on the full circle, with actual
strict interval margin greater than 1.2769*10^-5. The affine root is inside
the disk because r|K'|>|K|. Rouché gives exactly one zero of F there, counted
with multiplicity. The actual simple-even ground line can be chosen real,
and the candidate is real, so F respects conjugation. Uniqueness in this
conjugation-invariant disk forces the zero to be real; multiplicity one
forces it to be simple. Evenness yields the reflected conclusion:

\[
 \boxed{\text{Each of }|z-14.135|<0.004\text{ and }|z+14.135|<0.004
 \text{ contains exactly one simple real zero of }F.}
 \tag{DZ13}
\]

The positive zero lies in (14.131,14.139). We do not claim it is the first
positive zero, since smaller frequencies have not been globally excluded.
No Xi evaluations, zeta-zero positions or eigensolver enter the checker.
The center is a fixed rational examination window, not a supplied zero
identity. The argument counts zeros of the actual infinite-dimensional
ground transform through the full-form certificate, rather than counting
only roots of the finite candidate transform.

## 7. Replay, formal scope and the remaining arithmetic problem

Final checker SHA-256:
`4343355f261f800e77b518244946b311eae3a656e79dcf9b6421d901382dfc4b`.
Pinned arithmetic dependency SHA-256:
`8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0`.
The final source was replayed successfully, and its remote Git blob equals
the local replay source. The recorded JSON belongs to that exact source.
Both the executable inequality and the elementary all-scale series proof
have been reviewed. There was no Lean/lake or Scribe compiler in this runtime.
No kernel acceptance or executed #print axioms report is asserted.

The new Lean declaration proves (DZ3) and absolute convergence using the
actual arithmetic symbol. (DZ4) is its paper Fourier normalization,
(DZ6)-(DZ8) are the paper operator/variational transport, and (DZ9)-(DZ13)
are the executed interval realization and its Rouché consequence. These
layers must not be confused with an end-to-end Lean theorem about A_a.

This removes one concrete unresolved quantity from (CO26): the arithmetic
infinite dual correction now has a complete effective tail estimate and an
executed consumer. It does not remove the main scale-family obligation.
For the explicitly constructed prolate family of (CO20), one must still
establish actual simple-even coercivity and prove, on each compact substrip K,

\[
 |c_a|^2(U_a-\ell_a)\sup_{z\in K}\mathcal D_a(z)\longrightarrow0.
 \tag{DZ14}
\]

The dyadic c=3 candidate has not been identified with that prolate family.
The local counted zero in (DZ13) is not a new result about the zeros of Xi.
It is a concrete, reproducible test of the analytic approximation mechanism
required by CCM's open problem. The next mathematical work is to evaluate
these same signed observations on an explicit growing-scale candidate
family, rather than to add another general positivity or RH-implication
wrapper. No novelty priority or completion of RH is claimed.

References and source interfaces:

* Connes, Consani, Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1,
  Sections 4, 7 and 8; the simple-even and model-approximation tasks are
  explicitly distinguished in Section 8.
* Connes, Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715v1,
  Lemma 2.2 and Proposition 2.3, for the actual Weil form core.
* Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096,
  for the same closed form and Friedrichs interface.
* loning, trureturing PR #5326, Sections C14-C15, and #5296, the separate
  boundary-transversality obligation. Neither theoretical transfer is
  treated as a proved identity with this Weil ground transform.
* AlyciaBHZ, trureturing PR #5882, complex projective recovery and readout
  sharpness; those general results are not duplicated in the new owner.

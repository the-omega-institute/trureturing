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

因此该有限��量只依赖每个通道的黄金壳层轨道，不依赖所选代表元。

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

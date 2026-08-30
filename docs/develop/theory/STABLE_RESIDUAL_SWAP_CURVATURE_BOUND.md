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

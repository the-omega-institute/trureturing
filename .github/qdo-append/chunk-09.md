\[
\boxed{
\Phi(a)=V^*\pi(a)V.
}
\]

量子通道在 Schrödinger 图像中可写成：

\[
\boxed{
\Phi_*(\rho)
=
\operatorname{Tr}_E
\bigl[
U(\rho\otimes\sigma_E)U^*
\bigr].
}
\]

这说明：

\[
\boxed{
\text{局部的广义测量、噪声与非酉性，可以是更大系统的投影、酉演化与遗忘。}
}
\]

但不能由此推出某个唯一隐藏整体。扩张只在适当最小性意义下唯一到酉等价；系统—环境分解、环境初态与具体实现仍是额外结构。

因此：

\[
\boxed{
\text{“可扩张为确定线性结构”}
\ne
\text{“物理世界已被证明具有唯一经典确定本体”.}
}
\]

---

## 30.14 退相干是相对于上下文的正交投影

设 \((P_i)\) 为完整正交投影族。定义 pinching/dephasing 映射

\[
\boxed{
\mathcal D_P(X)
=
\sum_iP_iXP_i.
}
\]

在有限维 Hilbert–Schmidt 空间

\[
\mathsf{HS}(\mathscr H)
\]

上取内积

\[
\langle X,Y\rangle_{\mathrm{HS}}
=
\operatorname{Tr}(X^*Y).
\]

令

\[
\mathcal B_P
=
\{X:P_iXP_j=0\text{ 当 }i\ne j\}
\]

为相对于该上下文的块对角子空间。

### 定理 30.22（去相干映射是 Hilbert–Schmidt 正交投影）

有

\[
\boxed{
\mathcal D_P^2=\mathcal D_P,
}
\]

\[
\boxed{
\mathcal D_P^*=\mathcal D_P
}
\]

于 Hilbert–Schmidt 内积，并且

\[
\boxed{
\operatorname{range}\mathcal D_P=\mathcal B_P.
}
\]

因此

\[
\boxed{
X
=
\mathcal D_PX
+
(I-\mathcal D_P)X
}
\]

是 Hilbert–Schmidt 正交分解，且

\[
\boxed{
\|X\|_{\mathrm{HS}}^2
=
\|\mathcal D_PX\|_{\mathrm{HS}}^2
+
\|X-\mathcal D_PX\|_{\mathrm{HS}}^2.
}
\]

#### 证明

利用 \(P_iP_j=\delta_{ij}P_i\)：

\[
\mathcal D_P^2(X)
=
\sum_{i,j}P_iP_jXP_jP_i
=
\sum_iP_iXP_i.
\]

又

\[
\langle\mathcal D_PX,Y\rangle
=
\sum_i\operatorname{Tr}(X^*P_iYP_i)
=
\langle X,\mathcal D_PY\rangle.
\]

像空间恰是所有交叉块消失的算子。自伴幂等算子即为正交投影，Pythagoras 随之成立。 \(\square\)

所以一个状态可分解为：

\[
\boxed{
\rho
=
\underbrace{\mathcal D_P(\rho)}_{\text{相对于上下文可见的经典块}}
+
\underbrace{\bigl(\rho-\mathcal D_P(\rho)\bigr)}_{\text{跨扇区相干余量}}.
}
\]

“经典性”因此不是状态的绝对属性，而是相对于投影上下文的块对角性：

\[
\boxed{
\rho=\mathcal D_P(\rho).
}
\]

同一个 \(\rho\) 可以对一个上下文完全经典，对另一个上下文保持相干。

---

## 30.15 动力学相对性：概率流由跨界面耦合控制

设封闭系统由自伴 Hamiltonian \(H\) 生成：

\[
U_t=e^{-itH},
\qquad
\rho_t=U_t\rho U_t^*.
\]

对投影 \(P\)，定义事件概率

\[
p_P(t)=\operatorname{Tr}(\rho_tP).
\]

### 定理 30.23（投影概率流公式）

在有限维或满足相应定义域条件时，

\[
\boxed{
\frac{d}{dt}p_P(t)
=
i\operatorname{Tr}(\rho_t[H,P]).
}
\]

因此若

\[
[H,P]=0,
\]

则

\[
\boxed{
p_P(t)=p_P(0)
}
\]

对全部 \(t\) 成立。

#### 证明

\[
\dot\rho_t=-i[H,\rho_t].
\]

故

\[
\begin{aligned}
\dot p_P(t)
&=
-i\operatorname{Tr}([H,\rho_t]P)\\
&=
-i\operatorname{Tr}(H\rho_tP-\rho_tHP)\\
&=
i\operatorname{Tr}(\rho_t(HP-PH))\\
&=
i\operatorname{Tr}(\rho_t[H,P]).
\end{aligned}
\]

\(\square\)

相对于分解

\[
\mathscr H=P\mathscr H\oplus(I-P)\mathscr H,
\]

Hamiltonian 的跨界面耦合是

\[
PH(I-P),
\qquad
(I-P)HP.
\]

若二者为零，则 \(P\) reducing，事件扇区在动力学下闭合；若非零，则概率可以在已知／余空间之间流动。

这与第 28 节块矩阵判据完全一致：

\[
\boxed{
\text{观察界面的时间稳定性由跨块耦合决定，而不是只由各块内部维数决定。}
}
\]

---

## 30.16 状态完成严格弱于空间完成

设投影塔

\[
P_n\uparrow P_\infty
\]

于强算子拓扑，最终余投影为

\[
Q_\infty=I-P_\infty.
\]

### 定义 30.24（空间完成）

\[
\boxed{
Q_\infty=0.
}
\]

### 定义 30.25（状态完成）

对状态 \(\rho\)：

\[
\boxed{
\operatorname{Tr}(\rho Q_\infty)=0.
}
\]

### 定理 30.26（状态完成判据）

对正迹类 \(\rho\)，下列条件等价：

1. \(\operatorname{Tr}(\rho Q_\infty)=0\)；
2. \(Q_\infty\rho^{1/2}=0\)；
3. \(\operatorname{supp}\rho\le P_\infty\)；
4. \(\operatorname{Tr}(\rho P_n)\to1\)。

#### 证明

\[
\operatorname{Tr}(\rho Q_\infty)
=
\operatorname{Tr}(\rho^{1/2}Q_\infty\rho^{1/2})
=
\|Q_\infty\rho^{1/2}\|_{\mathrm{HS}}^2.
\]

故 1 与 2 等价；2 等价于状态支撑位于 \(P_\infty\) 中。又由 \(P_n\uparrow P_\infty\) 及正态迹的单调连续性：

\[
\operatorname{Tr}(\rho P_n)
\to
\operatorname{Tr}(\rho P_\infty)
=
1-\operatorname{Tr}(\rho Q_\infty).
\]

\(\square\)

所以：

\[
\boxed{
Q_\infty=0
\Longrightarrow
\operatorname{Tr}(\rho Q_\infty)=0,
}
\]

但反向一般不成立。

这给出一条统一解释：

- 在 RH 的 Nyman–Beurling 表述中，不要求整个最终余空间消失，只要求目标态 \(\chi\) 的余质量为零；
- 在量子观察中，不要求观察者覆盖全部可能态，只要求当前状态的支撑落在完成可见空间；
- 在有限模型中，不要求全状态空间统一逼近，只要求任务相关状态族的余概率可控。

---

## 30.17 对角化、量子上下文与完成失败不是同一个障碍

三种结构容易被语言混合，但其类型不同。

### Cantor–Lawvere 对角障碍

给定评价映射

\[
e:A\to Y^A,
\]

无不动点扭曲产生

\[
d_e\notin\operatorname{range}e.
\]

它是**自应用表示的满射失败**。

### Hilbert 正交余障碍

给定闭子空间 \(S\subsetneq\mathscr H\)，存在

\[
e\in S^\perp,

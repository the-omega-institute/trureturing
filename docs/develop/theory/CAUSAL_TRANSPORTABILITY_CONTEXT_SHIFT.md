# 跨域因果运输：机制锚、上下文漂移与锐利失败界

> **本卷的机器契约。** 本文是 \`docs/develop/theory/\` 下的纯理论参考输入，只增不减；不承担 Lean、消化账本或冻结状态的数学真值。作者种类为 **AI**，作者/模型为 **OpenAI GPT-6 via Codex**，来源/会话标识为 **持续因果理论目标，2026-09-28**。本文不声称原创性或形式验证。

在不同人群、设备、实验室或环境中，源域数据不能自动变成目标域的因果效应。一个可运输的效应至少由两部分组成：

$$
\boxed{
\text{结构响应核}
\;+\;
\text{目标域上下文分布}.
}
$$

即使每个分层内的干预响应保持不变，只要目标域的分层权重改变，总体效应也会改变；若某些分层的机制没有桥接证据，源域实验还不能确定目标域效应的方向。本卷把这两种不确定性分开，给出精确分解、锐利区间和失败反例。

## 1. AHH：箭头本身不携带跨域不变量

令域标签为 $d\in\{s,t\}$，分别表示源域和目标域。固定有限上下文集 $Z$、二元处理 $a\in\{0,1\}$ 和二元结果 $Y\in\{0,1\}$。

域 $d$ 的分层干预核为

$$
K_d^a(y\mid z)
=
\Pr_d(Y=y\mid \operatorname{do}(A=a),Z=z),
$$

域上下文分布为 $\mu_d\in\Delta(Z)$。总体干预效应定义为

$$
\theta_d
=
\sum_{z\in Z}\mu_d(z)
\left[
K_d^1(1\mid z)-K_d^0(1\mid z)
\right].
$$

记分层响应差为

$$
\delta_d(z)=K_d^1(1\mid z)-K_d^0(1\mid z)\in[-1,1].
$$

于是

$$
\theta_d=\langle\mu_d,\delta_d\rangle.
$$

这条等式把「机制」与「上下文」拆开：

- $\delta_d$ 描述在同一个分层内改变处理会怎样；
- $\mu_d$ 描述目标域实际把多少质量放在各个分层；
- $\theta_d$ 是两者的加权组合。

$$
\boxed{
\text{机制不变}\ (\delta_t=\delta_s)
\quad\not\Rightarrow\quad
\text{总体效应不变}\ (\theta_t=\theta_s),
}
$$

除非上下文权重也满足相应的积分相等式。

## 2. 结构核、上下文和桥接集合

**定义 2.1（源域可见响应）。** 源域随机干预实验给出

$$
r_s^a(z)=K_s^a(1\mid z),
\qquad
\delta_s(z)=r_s^1(z)-r_s^0(z).
$$

这是假定分层 $z$ 在源域可以被校准、记录并与处理接口相容。

**定义 2.2（机制桥接集合）。** 令 $B\subseteq Z$ 满足：对每个 $z\in B$ 和 $a\in\{0,1\}$，有目标—源核相同，

$$
K_t^a(\,\cdot\mid z)=K_s^a(\,\cdot\mid z).
$$

未被桥接的分层记为

$$
U=Z\setminus B.
$$

桥接是一个关系假设，不是由「源域和目标域名称相似」自动得到的事实。目标域的上下文权重 $\mu_t$ 若已由独立抽样或登记获得，仍不能补足 $U$ 上未知的机制核。

**定义 2.3（局部效应界）。** 对每个 $z\in U$，若只知道

$$
\ell_z\le\delta_t(z)\le u_z,
\qquad
-1\le\ell_z\le u_z\le1,
$$

称 $(\ell_z,u_z)$ 为该分层的目标效应界。没有任何信息时取 $\ell_z=-1$、$u_z=1$。

## 3. 精确运输的必要质量条件

**定理 3.1（桥接质量为一时的精确运输）。** 若

$$
\mu_t(U)=0,
$$

则目标域效应唯一确定为

$$
\boxed{
\theta_t
=
\sum_{z\in B}\mu_t(z)\delta_s(z).
}
$$

### 证明

按定义分解：

$$
\theta_t
=
\sum_{z\in B}\mu_t(z)\delta_t(z)
+
\sum_{z\in U}\mu_t(z)\delta_t(z).
$$

在 $B$ 上桥接条件给出 $\delta_t(z)=\delta_s(z)$。第二项因 $\mu_t(U)=0$ 而为零，得到结论。证毕。

这个定理的关键不是「源域效应可以复制」，而是目标域所有正质量都落在机制已桥接的上下文纤维上。若目标域把任意正质量放到 $U$，源域响应表就不再足以唯一确定总效应。

**推论 3.2（全桥接的标准化公式）。** 若 $B=Z$，则对任意目标上下文分布 $\mu_t$，

$$
\theta_t
=
\sum_{z\in Z}\mu_t(z)\delta_s(z).
$$

因此，当机制核保持不变时，运输任务退化为把同一个结构响应函数对新的上下文分布积分。

## 4. 未桥接分层的锐利运输区间

**定理 4.1（局部界下的锐利区间）。** 在桥接集合 $B$ 和局部界 $(\ell_z,u_z)_{z\in U}$ 已知时，所有与这些条件相容的目标效应恰好组成区间

$$
\boxed{
\left[
\sum_{z\in B}\mu_t(z)\delta_s(z)
+
\sum_{z\in U}\mu_t(z)\ell_z,\;
\sum_{z\in B}\mu_t(z)\delta_s(z)
+
\sum_{z\in U}\mu_t(z)u_z
\right].
}
$$

### 证明

对任意相容目标核，逐项有

$$
\mu_t(z)\ell_z
\le
\mu_t(z)\delta_t(z)
\le
\mu_t(z)u_z
\qquad(z\in U),
$$

因为 $\mu_t(z)\ge0$。在 $B$ 上 $\delta_t=\delta_s$，求和得到区间包含性。

反过来，取任意 $\lambda\in[0,1]$，在每个 $z\in U$ 定义

$$
\delta_t(z)=
(1-\lambda)\ell_z+\lambda u_z.
$$

由于 $\ell_z,u_z\in[-1,1]$，可以构造二元概率核，例如令

$$
K_t^0(1\mid z)=\frac{1-\delta_t(z)}2,
\qquad
K_t^1(1\mid z)=\frac{1+\delta_t(z)}2.
$$

这给出合法的 Bernoulli 核，并在 $B$ 上使用桥接核。令各 $z$ 的 $\lambda$ 同时从 $0$ 变到 $1$，目标效应连续取得区间两端之间的每个值。故所给区间锐利。证毕。

无局部信息时，结论退化为

$$
\theta_t\in
\left[
\sum_{z\in B}\mu_t(z)\delta_s(z)-\mu_t(U),\;
\sum_{z\in B}\mu_t(z)\delta_s(z)+\mu_t(U)
\right].
$$

于是 $\mu_t(U)$ 是一个精确的未桥接质量预算：它既是未知效应对总体结果的最大幅度，也是区间端点可以达到的实际误差。

## 5. 同结构核下的上下文漂移界

现在考虑更强情形：

$$
\delta_t=\delta_s=\delta
\qquad\text{在全部 }Z\text{ 上}.
$$

机制没有改变，但上下文分布可能改变。定义总变差距离

$$
\operatorname{TV}(\mu_t,\mu_s)
=
\frac12\sum_{z\in Z}
|\mu_t(z)-\mu_s(z)|,
$$

以及响应振幅

$$
\operatorname{osc}(\delta)
=
\max_{z\in Z}\delta(z)-\min_{z\in Z}\delta(z).
$$

**定理 5.1（上下文漂移的锐利界）。**

$$
\boxed{
|\theta_t-\theta_s|
\le
\operatorname{TV}(\mu_t,\mu_s)\,
\operatorname{osc}(\delta).
}
$$

### 证明

令 $\nu=\mu_t-\mu_s$。因为两者都是概率分布，

$$
\sum_z\nu(z)=0.
$$

取任意常数 $c$，有

$$
\sum_z\nu(z)\delta(z)
=
\sum_z\nu(z)(\delta(z)-c).
$$

令 $\nu^+$、$\nu^-$ 为 $\nu$ 的正、负变差，则

$$
\nu^+(Z)=\nu^-(Z)=\operatorname{TV}(\mu_t,\mu_s).
$$

取 $c=\min\delta$ 或 $c=\max\delta$ 并分别在正负支撑上估计，得到

$$
\sum_z\nu(z)\delta(z)
\le
\nu^+(Z)\,[\max\delta-\min\delta],
$$

以及反向不等式。合并即得结论。证毕。

**等号条件。** 当 $\mu_t-\mu_s$ 的正质量只落在 $\delta$ 取最大值的层，负质量只落在 $\delta$ 取最小值的层（或交换正负）时，等号成立。因此这不是只在特殊欧氏范数下成立的松界，而是对给定总变差和响应振幅的锐利界。

**推论 5.2（机制平稳不等于效应平稳）。** 即使每个分层的干预核完全不变，只要 $\mu_t\ne\mu_s$ 且 $\delta$ 在不同分层取值不同，就可能有

$$
\theta_t\ne\theta_s.
$$

只有当上下文漂移落在 $\delta$ 的等值层内，或两分布对 $\delta$ 的积分恰好相同，整体效应才保持不变。

## 6. 机制偏差与上下文漂移的精确分解

在一般情形下，定义机制偏差

$$
e(z)=\delta_t(z)-\delta_s(z).
$$

**定理 6.1（运输误差分解）。**

$$
\boxed{
\theta_t-\theta_s
=
\underbrace{\sum_z(\mu_t(z)-\mu_s(z))\delta_s(z)}_{\text{上下文漂移}}
+
\underbrace{\sum_z\mu_t(z)e(z)}_{\text{目标机制偏差}}.
}
$$

### 证明

将 $\delta_t=\delta_s+e$ 代入：

$$
\begin{aligned}
\theta_t-\theta_s
&=
\sum_z\mu_t(z)\delta_t(z)-\sum_z\mu_s(z)\delta_s(z)\\
&=
\sum_z(\mu_t(z)-\mu_s(z))\delta_s(z)
+\sum_z\mu_t(z)e(z).
\end{aligned}
$$

证毕。

若已知点态机制误差预算

$$
|e(z)|\le\varepsilon_z,
$$

则有

$$
\left|
\theta_t-\theta_s-
\sum_z(\mu_t(z)-\mu_s(z))\delta_s(z)
\right|
\le
\sum_z\mu_t(z)\varepsilon_z.
$$

该界同样锐利：在每个正权重分层上取 $e(z)=+\varepsilon_z$ 或 $-\varepsilon_z$ 即达到对应端点，只要这些误差核仍落在合法的二元概率范围内。

这条分解禁止把两种失败混成一个「域差异」数字：上下文变了，是权重项；机制变了，是核项；它们需要不同的额外测量与桥接假设。

## 7. 源数据、目标上下文与未桥接正质量的反例

**定理 7.1（同观察纤维、异目标效应）。** 假设存在 $z_\ast\in U$ 满足 $\mu_t(z_\ast)>0$。则可以构造两个目标域模型 $T_+$ 与 $T_-$，使得：

1. 两者有相同的源域核和相同的源域全部干预记录；
2. 两者有相同的目标上下文分布 $\mu_t$；
3. 两者在桥接集合 $B$ 上的目标核完全相同；
4. 但目标效应相差 $2\mu_t(z_\ast)$。

### 证明

在 $B$ 上两模型都采用桥接核。在 $z_\ast$ 上令

$$
\delta_{T_+}(z_\ast)=1,
\qquad
\delta_{T_-}(z_\ast)=-1.
$$

可用确定性 Bernoulli 核实现这两个极端：$T_+$ 令处理 $1$ 必然给结果 $1$、处理 $0$ 必然给结果 $0$；$T_-$ 交换两者。其他未桥接分层使用相同合法核。

前三项由构造直接成立。两模型效应之差为

$$
\theta_{T_+}-\theta_{T_-}
=
\mu_t(z_\ast)\,[1-(-1)]
=
2\mu_t(z_\ast),
$$

若其他未桥接分层取相同核则没有额外差异。证毕。

因此，源域所有被动与干预记录、目标域上下文直方图和桥接层记录都相同，仍不能从观察纤维中选出目标效应的符号。缺失的是 $z_\ast$ 上的机制关系，而不是更多源域样本的数量。

## 8. 运输方块与上下文推前

有时两个域之间给出一个上下文映射，而不是逐层同名。设有限集合 $Z_s,Z_t$，并有确定映射

$$
T:Z_t\to Z_s.
$$

目标分布 $\mu_t$ 的推前为

$$
(T_\#\mu_t)(z_s)
=
\sum_{z_t:T(z_t)=z_s}\mu_t(z_t).
$$

设源域有结构响应 $\delta_s:Z_s\to\mathbb R$。若目标响应满足交换条件

$$
\delta_t(z_t)=\delta_s(T(z_t))
\qquad\forall z_t\in Z_t,
$$

则有：

**定理 8.1（运输方块交换）。**

$$
\boxed{
\langle\mu_t,\delta_t\rangle
=
\langle T_\#\mu_t,\delta_s\rangle.
}
$$

### 证明

直接按纤维分组：

$$
\begin{aligned}
\langle\mu_t,\delta_t\rangle
&=
\sum_{z_t}\mu_t(z_t)\delta_s(T(z_t))\\
&=
\sum_{z_s}
\left(\sum_{z_t:T(z_t)=z_s}\mu_t(z_t)\right)
\delta_s(z_s)\\
&=
\langle T_\#\mu_t,\delta_s\rangle.
\end{aligned}
$$

证毕。

这个方块清楚区分两项工作：

- $T$ 把目标域上下文搬回源域的坐标；
- $\delta_t=\delta_s\circ T$ 才是机制桥接。

只有上下文映射而没有响应交换条件，不能推出效应运输。相反，若交换条件成立，源域核可以在推前后的目标上下文上重新积分。

## 9. 何时需要增加实验？

本卷的区间公式可以反向给出实验设计条件。若当前已知桥接集合为 $B$，而目标域上下文质量为 $\mu_t(U)$，无局部约束时运输区间宽度为

$$
2\mu_t(U).
$$

要把目标效应不确定度压到 $\eta>0$，至少需要让以下之一成立：

1. 把未桥接质量降到 $\mu_t(U)\le\eta/2$；
2. 在 $U$ 上增加局部效应界，使
   $$
   \sum_{z\in U}\mu_t(z)(u_z-\ell_z)\le\eta;
   $$
3. 取得机制交换或更强的结构假设，把 $U$ 并入桥接集合；
4. 改变目标问题，使它只询问桥接层的条件效应。

这不是把样本量当作抽象补丁：每种缩窄区间的方式都对应一类不同的关系信息。若新增数据只重复源域的已知核而不触及 $U$，它不能改变上述锐利区间。

## 10. 结论：可运输的是关系方块，不是一个孤立数字

跨域因果运输的基本对象可以写成：

$$
\boxed{
(\mu_d,\delta_d)
\longmapsto
\theta_d=\langle\mu_d,\delta_d\rangle.
}
$$

从源域到目标域，必须分别说明：

- 哪些上下文纤维的机制核由桥接关系固定；
- 目标域把多少概率质量放到这些纤维；
- 未桥接纤维上的核允许落在哪个范围；
- 上下文映射是否与响应核组成交换方块。

因此，「同一个箭头」和「同一个因果效应」是两种不同断言。前者可能只说某个分层内的响应相同，后者还要把目标域上下文权重接回同一个结构关系。

> **AHH：因果效应不是一枚可以跨域搬运的标签，而是结构响应核在目标上下文上的积分；跨域失败的最小见证是一块未桥接且具有正目标质量的上下文纤维。**

## 追加锚（本行以下为增补区）

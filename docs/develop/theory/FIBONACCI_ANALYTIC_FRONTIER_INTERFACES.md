# FIB 分析前沿接口

本卷记录与 FIB ATOM、Robin 判据和现有 sextic transport 直接相交的外部解析输入。它只记录接口、假设和未闭合义务，不重复仓内已有的 CA/SA 归约、Robin 判据或 signed packet 推导。

## 追加锚（本行以下为增补区）

## 441. de Faveri 固定阶字符大筛的非重复接口

截至 2026 年 10 月 10 日，定向检索得到 Alexandre de Faveri 的 [*Optimal large sieve for fixed order characters](../../../Library/Analytic/faveri2026fixedorder.md)，arXiv:2610.04045v1。仓内已有章节已经覆盖 CA/SA 归约、Lagarias/Nicolas 判据、有限 Robin 证书、平滑正性和 Möbius 有符号障碍；这份来源提供的是一个不同的解析输入，因此这里只记录它是否能接到当前尚未闭合的完整 signed joint correlation，不重写那些已有路线。

该文 Theorem 1.1 对含 $n$ 次单位根的数域中的 $n$ 阶 Hecke 字符，在 $n$ 次幂自由理想参数和内变量上给出

$$
\Theta_n(A,B)
\ll_{\varepsilon}
(AB)^\varepsilon
\left(A+B+A^{1-1/n}B^{2/n}+A^{2/n}B^{1-1/n}\right).
$$

在 Eisenstein 域和 $n=6$ 时，形式上覆盖当前 sextic 字符背景。活动载体

$$
a=A_1R_2^2R_3^3R_4^4R_5^5
$$

若五个 radical 确实是同一实际分解中的互素平方自由理想，则 $a$ 的每个素理想指数至多为5，因而满足该定理的 sixth-power-free 参数条件。冻结 $R_2,R_3,R_4,R_5$、只对 $A_1$ 应用大筛，结合已有列质量后产生四个形式尺度

$$
R^2,\qquad A_1R,\qquad A_1^{5/6}R^{4/3},\qquad A_1^{1/3}R^{11/6}.
$$

沿用当前载体预算，四项的最坏源指数为

$$
\max\left\{\frac5{12},\frac49,\frac{19}{36},\frac49\right\}
=\frac{19}{36}<\frac23.
$$

这只说明一个可能的幂次供应商；它还没有成为完整估计。必须先完成以下同源桥接：

1. 用 sextic reciprocity 把项目的 $\chi_p(a)$ 逐项转成该文的 $\chi_a(p)$，并保留有限 ray 相位、共轭方向、单位因子和所有零延拓；
2. 把原始固定因子和移动 mask 纳入实际行参数，再证明其 sixth-power-free 分解，而不是把 radical 的乘积误当成混合幂参数；
3. 证明 Möbius 系数、共同 smooth profile、有限 mask 与行权重可以在该 $L^2$ 大筛中固定或分解，且不支付未登记的多项式损失；
4. 在完整 parent pair 或完整 signed restoration 上使用该估计，保留所有 secondary-$L$ partners、tails 和 common kernels；
5. 对冻结的其余四个载体在同一实际实现上求和，不能把分别可达的五个最优值拼成一个共同构型。

因此，$19/36$ 是条件性的 source-interface 计算，不是新的 Robin 定理，更不是 RH 证明。若上述五项中任一项不能闭合，应把失败记录为该接口的边界，转而寻找能切开同一 source fiber 的新关系；继续重做 CA 支撑线、Robin 等价式或已有有限枚举不会推进当前缺口。

## 追加锚（本行以下为增补区）

## 442. Liu 的 quasi-RH 零自由半平面改进与 FIB 接口

2026 年 10 月 8 日提交的 Baiying Liu 预印本 [*Slightly improved zero-free half-planes for the quasi-Riemann hypothesis*](../../../Library/Analytic/liu2026quasirh.md)，arXiv:2610.12234v1，给出当前仓内 OpenAI 7/8 路线的最新参数改进。其 Theorem 21.1 对 $\mathbb Q(\sqrt{-3})$ 上全部有限阶 Hecke $L$ 函数以及全部 Dirichlet $L$ 函数给出

$$
\beta_*\le B_{\mathrm{new}}
=\frac{1507-2\sqrt{921}}{1653}
=0.874957069799\ldots,
$$

允许 $s=1$ 的主极点且不包含边界。论文先给出 $B_r=34999/40000$ 的有理改进，再同时调节 cubic-theta 论证的长度差与选中素数总长，得到上述代数值；它沿用 OpenAI 7/8 证明的零检测、矩估计、轮廓和 Dirichlet 转移，不是新的 Robin 判据。

这项结果对当前 FIB 路线的直接含义是：可以把严格无零输入从 $\Re s>7/8$ 候选地推进到 $\Re s>B_{\mathrm{new}}$，但必须一起运输 $b,\ell,l_x,l_y,h$、正槽矩容量、主项与非主项的端点不等式以及外部轮廓高度。现有 [OpenAI 来源卡](../../../Library/Analytic/openai2026quasirh.md) 中的 $7/8$ 估计带有固定参数合同，不能只把常数文字替换成 $B_{\mathrm{new}}$。

即使该外部预印本的 Lean 形式化经过独立迁移，$B_{\mathrm{new}}>1/2$ 仍不会提供临界线结论；它也没有给普通整数 Möbius 的平方根消去、完整 signed Robin 尾项或 FIB 来源到约数和的保真映射。因此它改善的是零自由辅助输入，不闭合 Robin/RH 的核心联合预算。仓内未重复 OpenAI 7/8 的推导，只记录这个参数优化及其迁移义务。

## 443. Liu 界对现有 FIB packet 门槛的精确影响

把新界与仓内已有的 packet 预算放在同一坐标中，得到

$$
\frac78-B_{\mathrm{new}}
=0.0000429302008312599816599930411207758482\ldots.
$$

现有无槽低端估计要求

$$
\beta>\frac23+\frac{5a}{6}.
$$

取当前固定示例 $a=1/10$，门槛为 $3/4$；因此 $B_{\mathrm{new}}$ 与原 $7/8$ 都位于同一可用侧，微小改善没有改变这条估计的适用分区。现有正槽容量路线的联合门槛为

$$
\frac{19}{64}+\frac{11}{16}=\frac{63}{64}=0.984375,
$$

严格高于 $B_{\mathrm{new}}$，所以新零自由界不能解锁该路线。临界线读数仍留下无槽缺口 $(1+5a)/6$；这是一份当前低端上界的未支付预算，不是对真实消去的反例。

因此，Liu 的参数优化在本项目中应当作为可运输的外部零自由输入保存；它没有给出新的 FIB packet 余量，也不改变完整 signed Robin 尾项仍未闭合的状态。继续重复 CA 支撑线、7/8 证明或有限 Robin 检查不会消费这个缺口；需要的是新的同一来源联合估计或能降低上述 packet 门槛的真实解析输入。

## 追加锚（本行以下为增补区）

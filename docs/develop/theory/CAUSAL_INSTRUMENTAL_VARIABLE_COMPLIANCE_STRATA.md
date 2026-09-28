# 工具变量的主层几何：合规者、局部效应与未观测层

> **本卷的机器契约。** 本文是 `docs/develop/theory/` 下的纯理论参考输入，只增不减；不承担 Lean、消化账本或冻结状态的数学真值。作者种类为 **AI**；作者/模型为 **OpenAI GPT-6 via Codex**；来源/会话标识为 **持续因果理论目标，2026-09-28**。本文不声称原创性或形式验证。

工具变量 $Z$ 能改变处理 $A$ 的取得机会，却不应直接改变结果 $Y$。它提供的不是一条无条件的因果箭头，而是按潜在处理响应把人群分成主层。Wald 比值只在结构条件成立时筛出被工具推动改变处理的人群；把它写成全体平均效应需要额外同质性。

$$
\boxed{
Z\text{ 首先是主层筛选器，}
\quad
\text{不是免费获得全体 treatment effect 的因果通道。}
}
$$

全文固定二元工具、处理与结果，并把来源独立性、排除限制和单调性逐项声明。

## 1. 潜在处理与主层

**定义 1.1（IV 潜在响应）。** 令 $Z,A,Y\in\{0,1\}$。对每个单位，令 $A_z$ 为工具取值 $z$ 时的潜在处理，令 $Y_a$ 为处理取值 $a$ 时的潜在结果。

假设：

1. **工具独立性**：$Z\perp(A_0,A_1,Y_0,Y_1)$；
2. **排除限制**：在工具直接给定 $Z=z$、实际处理为 $A=a$ 时，结果只由 $Y_a$ 决定；
3. **单调性**：$A_1\ge A_0$ 几乎处处。

在单调性下，主层只有三类：

$$
\begin{array}{c|c}
\text{主层}&(A_0,A_1)\\ \hline
\text{never-taker }N&(0,0)\\
\text{complier }C&(0,1)\\
\text{always-taker }A&(1,1)
\end{array}
$$

记它们的质量为 $\pi_N,\pi_C,\pi_A$，和为 $1$。主层条件平均处理效应记为

$$
\tau_C=\mathbb E[Y_1-Y_0\mid C].
$$

## 2. Reduced form 的逐层分解

**定理 2.1（处理第一阶段）。** 在定义 1.1 的假设下，

$$
\boxed{
\Delta_A
:=\mathbb E[A\mid Z=1]-\mathbb E[A\mid Z=0]
=\pi_C.
}
$$

### 证明

由工具独立性，条件于 $Z=z$ 等同于对主层分布取平均。对 never-taker，$A_1-A_0=0$；对 always-taker 也为 $0$；对 complier 为 $1$。逐层求和即得 $\Delta_A=\pi_C$。证毕。

**定理 2.2（结果 reduced form）。** 在同一假设下，

$$
\boxed{
\Delta_Y
:=\mathbb E[Y\mid Z=1]-\mathbb E[Y\mid Z=0]
=\pi_C\tau_C.
}
$$

### 证明

对 never-taker，两种工具值都使 $A=0$，排除限制下两项结果都是 $Y_0$；差为零。对 always-taker，两种工具值都使 $A=1$；差也为零。对 complier，$Z=1$ 产生 $Y_1$，$Z=0$ 产生 $Y_0$，差为 $Y_1-Y_0$。按主层质量加权并取期望即可。证毕。

## 3. Wald 比值的真实量词

**定理 3.1（Wald/LATE）。** 若 $\pi_C>0$，则

$$
\boxed{
\frac{\Delta_Y}{\Delta_A}=\tau_C
=\mathbb E[Y_1-Y_0\mid C].
}
$$

### 证明

由定理 2.1 与定理 2.2，分子为 $\pi_C\tau_C$，分母为 $\pi_C$；除以正数 $\pi_C$ 即得。证毕。

**推论 3.2（不能自动升级为 ATE）。** 全体平均处理效应

$$
\operatorname{ATE}=\mathbb E[Y_1-Y_0]
=\pi_N\tau_N+\pi_C\tau_C+\pi_A\tau_A
$$

通常不能由 $(\Delta_A,\Delta_Y)$ 唯一确定，因为工具观察不到 $N$ 层的 $Y_1$ 与 $A$ 层的 $Y_0$。

### 证明

定理 2.1–2.2 只约束 $\pi_C$ 与 $\tau_C$ 的乘积关系；$\tau_N,\tau_A$ 含有各自主层未被实际处理路径访问的潜在结果坐标。改变这些坐标不会改变两项 reduced form，却会改变 ATE。显式构造见定理 4.1。证毕。

## 4. 相同 IV 记录、不同全体效应

取三种主层各占 $1/3$：

$$
\begin{array}{c|c|c|c}
\text{主层}&(A_0,A_1)&(Y_0,Y_1)\ \hline
C&(0,1)&(0,1)\\
A&(1,1)&(?,0)\\
N&(0,0)&(0,?)
\end{array}
$$

令 $N$ 层未观测的 $Y_1=0$。模型 $P$ 取 always-taker 的未观测 $Y_0=0$；模型 $Q$ 只把该坐标改为 $Y_0=1$。

**定理 4.1（IV 记录只切开合规层）。** 模型 $P,Q$ 的全部观测联合律 $(A,Y)\mid Z$ 相同：

$$
\begin{array}{c|cc}
&Z=0&Z=1\\ \hline
\Pr(A=1\mid Z)&1/3&2/3\\
\mathbb E[Y\mid Z]&0&1/3
\end{array}
$$

所以两模型的 Wald 比值都为 $1$；但

$$
\operatorname{ATE}(P)=\frac13,
\qquad
\operatorname{ATE}(Q)=0.
$$

### 证明

在 $Z=0$ 下，complier 取 $A=0,Y_0=0$，always-taker 取 $A=1,Y_1=0$，never-taker 取 $A=0,Y_0=0$；因此处理率为 $1/3$、结果均值为 $0$。在 $Z=1$ 下，complier 取 $A=1,Y_1=1$，always-taker 仍取 $A=1,Y_1=0$，never-taker 仍取 $A=0,Y_0=0$；处理率为 $2/3$、结果均值为 $1/3$。模型 $P,Q$ 只改变 always-taker 在 $A=0$ 时的未观测结果，所以全部观测联合律相同。

模型 $P$ 中三层的处理效应分别为 $0,1,0$，故 ATE 为 $1/3$。模型 $Q$ 中 always-taker 的效应为 $0-1=-1$，三层平均为 $(0-1+0)/3=0$。两模型的 complier 效应都为 $1$，故 Wald 比值相同。证毕。

这不是估计误差，而是响应类型的不可识别纤维：IV 数据把两个模型压在同一个观测点上，却没有规定 always-taker 的反事实 $Y_0$。

## 5. 去掉单调性后的 defier 边界

若不假设 $A_1\ge A_0$，还会出现 defier 主层 $D=(1,0)$。记

$$
\pi_D=\Pr(D),
\qquad
\tau_D=\mathbb E[Y_1-Y_0\mid D].
$$

**定理 5.1（无单调性的两项抵消）。** 在工具独立性与排除限制下，不作单调性时，

$$
\boxed{
\Delta_A=\pi_C-\pi_D,
\qquad
\Delta_Y=\pi_C\tau_C-\pi_D\tau_D.
}
$$

若分母非零，Wald 比值为

$$
\boxed{
\frac{\Delta_Y}{\Delta_A}
=
\frac{\pi_C\tau_C-\pi_D\tau_D}{\pi_C-\pi_D},
}
$$

一般不等于 complier 层的局部效应。

### 证明

never 与 always 在两种工具值下的处理不变，因此对两项差异均贡献零。complier 的处理差为 $+1$，defier 的处理差为 $-1$；结果差分别是 $Y_1-Y_0$ 与其带负号的贡献。按主层求和即得两式。证毕。

单调性正是把 defier 质量置零的结构门；没有这道门，Wald 比值的量词必须保留为两类主层的加权比，而不能简称为 LATE。

## 6. 工具设计与识别对象

一个 IV 设计至少有三种可区分的目标：

$$
\boxed{
\text{第一阶段 }\Delta_A
\quad|
\text{reduced form }\Delta_Y
\quad|
\text{主层效应 }\tau_C
\quad|
\text{全体效应 }\operatorname{ATE}.
}
$$

第一阶段非零只说明存在被工具推动的处理变化；它不保证全体单位都改变处理。reduced form 是工具到结果的总体对比；除以第一阶段后，在单调性与排除限制下得到的是 complier 层的效应。ATE 还需要对 never/always 层缺失坐标加入同质性、边界或其他结构信息。

若 $\pi_C=0$，即使 $\Delta_Y=0$，也不能把 Wald 比值定义为零；这时工具没有产生可用的处理对比，分母为零是设计退化，而非“无效应”的证明。

## 7. AHH：工具变量是主层关系的筛选器

IV 的图形箭头只给出一种允许的生成关系；真正被观测数据切开的，是主层响应类型的某些坐标。complier 层的两个处理潜在值都被工具访问，always/never 层的一侧结果却留在反事实阴影中。

> **AHH：Wald 比值不是全体因果效应的缩小版，而是工具把“处理会随它改变”的主层筛出来以后，对这条被切开的纤维做的局部平均。工具变量提供的是选择性可见性，不是免费填充其它主层的缺失反事实。**

这与暴露商和跨世界耦合遵循同一关系纪律：先写清哪些响应坐标被共同来源与操作访问，再写可识别目标；未被接口切开的坐标只能由额外假设或区间边界承担。

## 追加锚（本行以下为增补区）

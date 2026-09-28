# 因果干预接口的 Blackwell 序与缺失度：可模拟性先于标量强度

> **本卷的机器契约。** 本文是 `docs/develop/theory/` 下的纯理论参考输入，只增不减；不承担 Lean、消化账本或冻结状态的数学真值。作者种类为 **AI**，作者/模型为 **OpenAI GPT-6 via Codex**，来源/会话标识为 **持续因果理论目标，2026-09-28**。本文不声称原创性或形式验证。

一个干预接口可能记录种子、动作、位置事件或完整历史。比较两个接口时，单独比较某个互信息或某个事件概率，不能回答“一个接口能否由另一个接口模拟”。本卷把这个问题写成有限实验之间的 Blackwell 偏序，并用缺失度量化不能精确模拟的残差。

$$
\boxed{
\text{因果接口的首要关系是可模拟性，}
\quad
\text{标量信息预算只是这个关系的单调投影。}
}
$$

固定有限隐藏状态集；它可以表示来源类型、反事实响应类型或已经声明的干预情形。所有“更强”都相对于允许的记录和后处理规则。

## 1. 干预实验与决策规则

**定义 1.1（有限干预实验）。** 令 $\Theta$ 为有限隐藏状态集，$\Omega$ 为有限记录集。一个实验 $E$ 是通道

$$
K_E(\omega\mid\theta),
\qquad
\sum_{\omega\in\Omega}K_E(\omega\mid\theta)=1.
$$

它可以来自一次干预、一个时序协议或一组位置探测的完整记录。对每个 $\theta$，记行分布为 $K_E^\theta$。

**定义 1.2（记录的随机后处理）。** 若 $G:\Omega\to\Xi$ 是通道，实验 $E$ 经过后处理后的实验记为 $E G$：

$$
(K_EG)(\xi\mid\theta)
=
\sum_{\omega\in\Omega}K_E(\omega\mid\theta)G(\xi\mid\omega).
$$

后处理只能读取已经记录的 $\omega$，不能访问 $\theta$。

**定义 1.3（Blackwell 支配）。** 写

$$
E\succeq_B F
$$

若存在一个不依赖 $\theta$ 的通道 $G$，使得

$$
\boxed{K_F=K_EG.}
$$

这表示 $F$ 的整份记录律可以由 $E$ 的记录经过合法随机后处理精确重现。

给定有限动作集 $A$ 和损失 $\ell:\Theta\times A\to\mathbb R$，实验 $E$ 的决策规则是 $\delta:A\mid\Omega$，即 $\delta(a\mid\omega)$ 是观察记录后选动作 $a$ 的概率。对状态 $\theta$ 的风险为

$$
R_E(\delta,\theta)
=
\sum_{\omega,a}
K_E(\omega\mid\theta)\delta(a\mid\omega)\ell(\theta,a).
$$

## 2. Blackwell 序的基本定理

**定理 2.1（自反、传递与风险单调性）。** 有：

1. $E\succeq_B E$；
2. $E\succeq_B F$ 且 $F\succeq_B H$ 蕴含 $E\succeq_B H$；
3. 若 $E\succeq_B F$，则对任意有限决策问题，
   $$
   \inf_\delta\max_{\theta}R_E(\delta,\theta)
   \le
   \inf_\gamma\max_{\theta}R_F(\gamma,\theta).
   $$
   对任意先验 $\pi$，对应的 Bayes 风险也满足同样不等式。

### 证明

第一项取恒等通道。第二项若 $K_F=K_EG$ 且 $K_H=K_FH'$，则

$$
K_H=K_E(GH'),
$$

故复合后处理给出传递性。

对第三项，给定 $F$ 上任意规则 $\gamma(a\mid\xi)$，在 $E$ 上使用

$$
\delta(a\mid\omega)
=
\sum_\xi G(\xi\mid\omega)\gamma(a\mid\xi).
$$

代入风险并交换有限求和，得到

$$
R_E(\delta,\theta)=R_F(\gamma,\theta)
\qquad\forall\theta.
$$

因此 $E$ 能实现 $F$ 的每个决策规则，分别取极小值后得到 minimax 与 Bayes 风险不增。证毕。

这一定理的方向很具体：完整记录较丰富时，可以主动丢弃部分记录来模拟较粗接口；反方向需要一个不依赖隐藏状态的随机解码器，不能由“两个接口都包含同一个事件”推出。

## 3. 缺失度：不能模拟的最小残差

**定义 3.1（行距离与缺失度）。** 对有限分布令

$$
\operatorname{TV}(p,q)=\frac12\sum_z|p(z)-q(z)|.
$$

定义实验 $E$ 模拟 $F$ 的缺失度为

$$
\delta(E,F)
=
\min_{G:\Omega\to\Xi}
\max_{\theta\in\Theta}
\operatorname{TV}
\bigl(K_EG(\cdot\mid\theta),K_F(\cdot\mid\theta)\bigr).
$$

它的方向与 Blackwell 序一致：$E\succeq_B F$ 正好对应零缺失度。

**引理 3.2（最小值存在）。** 定义 3.1 中的最小值总能达到。

### 证明

所有通道 $G(\xi\mid\omega)$ 构成有限个闭区间的乘积，并由每列归一化条件切出一个紧集。目标函数是有限个绝对值与有限求和的最大值，连续；紧集上的连续函数取到最小值。证毕。

**定理 3.3（零缺失度判据）。**

$$
\boxed{
\delta(E,F)=0
\iff
E\succeq_B F.
}
$$

### 证明

若 $K_F=K_EG$，取该 $G$ 得零值。反过来，若最小值为零，由引理 3.2 存在最优 $G_*$；最大行距为零意味着每个状态行都逐坐标相等，即 $K_F=K_EG_*$。证毕。

**定理 3.4（缺失度的三角不等式）。** 对三个实验 $E,F,H$，

$$
\boxed{
\delta(E,H)\le\delta(E,F)+\delta(F,H).
}
$$

### 证明

取任意后处理 $G:E\to F$ 与 $H':F\to H$。对每个 $\theta$，总变差在后处理下不增加，所以

$$
\begin{aligned}
\operatorname{TV}(K_EGH',K_H)
&\le
\operatorname{TV}(K_EGH',K_FH')
 +\operatorname{TV}(K_FH',K_H)\\
&\le
\operatorname{TV}(K_EG,K_F)
 +\operatorname{TV}(K_FH',K_H).
\end{aligned}
$$

对状态取最大值，再分别在 $G,H'$ 上取最小值即可。证毕。

**推论 3.5（Blackwell 等价类上的伪度量）。** 定义

$$
d_B(E,F)=\max\{\delta(E,F),\delta(F,E)\}.
$$

则 $d_B$ 对称、满足三角不等式；$d_B(E,F)=0$ 当且仅当两个实验互相 Blackwell 支配。

### 证明

对称性直接来自定义。三角不等式由定理 3.4 分别应用于两个方向，再使用

$$
\max\{a+c,b+d\}\le\max\{a,b\}+\max\{c,d\}.
$$

零值判据由定理 3.3 的两个方向给出。证毕。

缺失度把“接口差异”与“某个选定任务的差异”分开：$\delta(E,F)>0$ 只说明不存在一个统一后处理在所有隐藏状态上精确复制 $F$；它不自动指定哪一个损失函数最敏感。

## 4. 位置事件或因果命题的精确解码

**定义 4.1（目标事件实验）。** 给定一个二值目标

$$
t:\Theta\to\{0,1\},
$$

定义目标实验 $T_t$ 为确定输出 $t(\theta)$ 的通道。它可以表示“该干预是否使位置事件发生”“该来源类型是否允许某个局部影响”或任意二值因果命题。

**定理 4.2（精确事件解码判据）。** $E\succeq_B T_t$ 当且仅当存在函数 $g:\Omega\to[0,1]$，使

$$
\boxed{
\sum_{\omega\in\Omega}K_E(\omega\mid\theta)g(\omega)=t(\theta)
\qquad\forall\theta\in\Theta.
}
$$

### 证明

若 $E\succeq_B T_t$，取后处理 $G(1\mid\omega)=g(\omega)$。后处理后的输出为一的概率正是左式；由于目标实验是确定输出，左式必须等于 $t(\theta)$。反过来，由给定 $g$ 定义二值后处理 $G$，则输出为一与为零的概率分别等于 $t(\theta)$ 与 $1-t(\theta)$，故 $K_{T_t}=K_EG$。证毕。

当 $t$ 在隐藏状态上变化时，定理要求记录的不同状态行由同一个 $g$ 完全分开。普通的高预测率只要求左式接近 $t(\theta)$；精确因果认证要求等式对全部状态成立。

## 5. 一个锐利的记录层级见证

令 $\Theta=\{0,1\}$。定义完全揭示实验 $R$：

$$
K_R(\omega\mid\theta)=\mathbf 1\{\omega=\theta\}.
$$

定义擦除实验 $E_\varepsilon$，其输出为 $0,1,\perp$，以概率 $1-\varepsilon$ 输出 $\theta$，以概率 $\varepsilon$ 输出 $\perp$，其中 $0<\varepsilon<1$。

**定理 5.1（揭示严格支配擦除）。**

$$
R\succeq_B E_\varepsilon,
\qquad
E_\varepsilon\not\succeq_B R.
$$

并且

$$
\delta(E_\varepsilon,R)=\frac{\varepsilon}{2}.
$$

### 证明

从 $R$ 的记录 $\theta$ 出发，按概率 $1-\varepsilon$ 原样输出，按概率 $\varepsilon$ 输出 $\perp$，即可得到 $E_\varepsilon$。

反向不可能。擦除实验的两行分布总变差为 $1-\varepsilon$，而揭示实验两行总变差为 $1$。总变差在任意后处理下不增加，所以任何 $E_\varepsilon$ 的后处理仍有两行距离至多 $1-\varepsilon<1$，不可能等于 $R$。

要算缺失度的精确值，先用下界：对任意后处理，两个输出行的总变差至多 $1-\varepsilon$，而目标两行相距 $1$。若两个状态行的误差分别为 $e_0,e_1$，三角不等式给出

$$
1\le e_0+(1-\varepsilon)+e_1,
$$

故 $\max\{e_0,e_1\}\ge\varepsilon/2$。再取后处理 $G$ 将 $0,1$ 原样保留，并把 $\perp$ 映到均匀二元结果；两个行误差都恰为 $\varepsilon/2$，达到下界。故 $\delta(E_\varepsilon,R)=\varepsilon/2$。证毕。

这个见证把“公开种子”与“隐藏动作”之间的区别写成接口偏序：一次擦除并非只减少某个数字，而是产生一个不能由粗记录精确恢复的目标实验。

## 6. 干预协议的组合与缺失预算

**定理 6.1（协议后处理的序关系）。** 若一个时序协议的完整记录实验为 $E$，任何只读取该记录并输出新记录的合法协议后处理都给出 $E\succeq_B F$。若再接一个后处理，Blackwell 序按协议顺序传递。

### 证明

完整协议的所有随机性已经包含在 $K_E$ 中；后处理只是一组与隐藏状态无关的条件概率。定理 2.1 的自反性与传递性逐步应用即可。证毕。

**推论 6.2（路径缺失度的可加界）。** 若 $E\to F$ 的候选后处理为 $G$，$F\to H$ 的候选后处理为 $H'$，则

$$
\boxed{
\max_\theta\operatorname{TV}(K_EGH',K_H)
\le
\max_\theta\operatorname{TV}(K_EG,K_F)
+
\max_\theta\operatorname{TV}(K_FH',K_H).
}
$$

### 证明

这正是定理 3.4 证明中的逐状态不等式。证毕。

因此，沿多段记录协议累计的模拟误差可以逐段记账；任何一段的零缺失度都允许把其接口折叠为一次精确后处理。

## 7. Blackwell 序与相对熵预算的关系

**定理 7.1（可模拟性支配信息预算）。** 若 $E\succeq_B F$，则对任意先验标签 $U\to\Theta$，

$$
I(U;\Xi_F)\le I(U;\Omega_E).
$$

若用相对熵收缩系数表示两个接口的最坏输入区分能力，则

$$
\boxed{
\eta_{\mathrm{KL}}(F)\le\eta_{\mathrm{KL}}(E).
}
$$

### 证明

写 $\Xi_F$ 为对 $\Omega_E$ 的后处理输出。由有限通道的数据处理不等式，互信息不增。对任意状态分布 $p,q$，

$$
D(pK_F\Vert qK_F)
=D(pK_EG\Vert qK_EG)
\le D(pK_E\Vert qK_E).
$$

再分别除以 $D(p\Vert q)$ 并取上确界，得到收缩系数不等式。证毕。

标量预算是 Blackwell 序的必要单调量，却不是充分刻画：两个接口可以有相同的最坏收缩系数，但没有一个共同后处理把其中一个逐状态地变成另一个。可模拟性保留的是整张条件记录关系，而不是一个压缩后的数字。

## 8. 因果接口的三层区分

对一个干预—记录系统，应分开声明：

$$
\boxed{
\text{记录的条件律}
\;\longrightarrow\;
\text{是否存在状态无关的后处理}
\;\longrightarrow\;
\text{目标事件能否被精确解码}.
}
$$

第一层决定实验本身；第二层决定两个接口是否处于同一可模拟性纤维；第三层决定一个位置事件或因果命题是否能从记录中被认证。互信息、总变差和相对熵可以量化层间损失，但不能代替第二层的存在性判据。

## 9. AHH：因果强度首先是接口序，而非单一数字

如果完整实验 $E$ 能通过状态无关的后处理模拟 $F$，那么 $E$ 至少包含 $F$ 对全部隐藏状态的记录关系；如果只能做到正的缺失度，缺少的是一份逐状态、可复用的关系，而不是某个待补的常数。

> **AHH：因果接口的第一问题不是“它有多少信息”，而是“它能否在不偷看隐藏状态的情况下生成另一份接口”。Blackwell 序给出可模拟性，缺失度给出不能模拟的最小残差；相对熵预算只是这张序上的一个单调投影。**

这也限定了位置与局域事件的解释：一次记录能否认证某个事件，要看是否存在对全部允许来源同时成立的解码器；一组平均成功率或单一初态上的高相关，不能冒充这样的状态无关关系。

## 追加锚（本行以下为增补区）

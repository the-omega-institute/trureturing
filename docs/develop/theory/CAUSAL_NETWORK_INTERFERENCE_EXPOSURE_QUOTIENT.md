# 网络干扰的暴露商：结构局部性与设计支持的两道因果门

> **本卷的机器契约。** 本文是 `docs/develop/theory/` 下的纯理论参考输入，只增不减；不承担 Lean、消化账本或冻结状态的数学真值。作者种类为 **AI**；作者/模型为 **OpenAI GPT-6 via Codex**；来源/会话标识为 **持续因果理论目标，2026-09-28**。本文不声称原创性或形式验证。

单点 treatment 的记法会把一个网络 assignment profile 压得过早。若节点 $v$ 的潜在结果还依赖邻居 treatment，那么“$v$ 的处理值”不是它的完整因果输入；反过来，即使结构上确实只依赖某个 exposure，统计上没有覆盖该 exposure 的 assignment，也不能从数据估计它的响应。

本卷把两件事分开：

$$
\boxed{
\text{结构响应是否通过 exposure 商因子化}
\quad\longrightarrow\quad
\text{设计是否覆盖目标商上的必要纤维}.
}
$$

核心 AHH 是：**无观察到 spillover** 可能来自真实的结构不变性，也可能只是未采到相应的 assignment；两者在数学上不是同一句话。

全文固定有限节点、有限 assignment、有限结果集。潜在结果可以是确定函数，也可以是条件概率核。

## 1. Assignment profile 与暴露映射

**定义 1.1（网络 assignment）。** 令 $V$ 为有限节点集。每个节点的处理字母表为有限集 $\mathcal A_v$，全网 assignment 空间为

$$
\mathcal A=\prod_{u\in V}\mathcal A_u.
$$

对目标节点 $v$，其潜在结果核写作

$$
K_v(y\mid a),
\qquad
a\in\mathcal A,
\quad y\in\mathcal Y_v,
$$

其中 $\mathcal Y_v$ 是有限结果集。确定性响应 $f_v:\mathcal A\to\mathcal Y_v$ 是点质量核的特殊情形。

**定义 1.2（暴露映射）。** 一个 exposure map 是映射

$$
e_v:\mathcal A\to\mathcal E_v,
$$

把完整 assignment 压成目标节点允许使用的暴露标签。最粗的单点 treatment 记法是 $e_v(a)=a_v$；邻域暴露可以是 $e_v(a)=a|_{N(v)}$；更进一步还可以把对结果无差异的邻域构型合并。

**定义 1.3（暴露商相容性）。** 称 $e_v$ 对响应核是合法暴露商，若

$$
e_v(a)=e_v(a')
\Longrightarrow
K_v(\cdot\mid a)=K_v(\cdot\mid a')
\qquad\forall a,a'\in\mathcal A.
$$

确定性情形把核相等替换为 $f_v(a)=f_v(a')$。

这个条件是对全部 assignment 的结构命题；在一组有限实验中暂时没有观察到差异，不会自动给出它。

## 2. 暴露商的精确因子化

**定理 2.1（暴露商充要性）。** 对确定性响应 $f_v$，以下命题等价：

1. $e_v(a)=e_v(a')$ 蕴含 $f_v(a)=f_v(a')$；
2. 存在唯一函数 $\bar f_v:e_v(\mathcal A)\to\mathcal Y_v$，使
   $$
   \boxed{f_v=\bar f_v\circ e_v.}
   $$

对概率核同样成立：条件 1 中的函数值相等替换为核相等，结论中的 $\bar f_v$ 替换为唯一核 $\bar K_v(\cdot\mid e)$。

### 证明

由 1，在暴露像上定义

$$
\bar f_v(e_v(a))=f_v(a).
$$

若两个 assignment 给出同一个 $e_v(a)$，条件 1 保证右端相同，所以定义良好。$e_v(\mathcal A)$ 上的满射性给出唯一性，并且直接得到 $f_v=\bar f_v\circ e_v$。反过来，若有该因子化，相同的暴露标签代入同一个 $\bar f_v$ 即得 1。

核情形逐个输出 $y$ 应用完全相同的证明。证毕。

**推论 2.2（合法摘要的最小性）。** 若 $e_v$ 合法，任何对响应核充分的摘要 $s:\mathcal A\to\mathcal S$ 都必须满足

$$
s(a)=s(a')
\Longrightarrow
K_v(\cdot\mid a)=K_v(\cdot\mid a').
$$

因此，响应核的真正最小商是按

$$
a\sim_v a'
\Longleftrightarrow
K_v(\cdot\mid a)=K_v(\cdot\mid a')
$$

得到的商；一个邻域 exposure 只有在它至少细于这个响应商时才不会丢失目标响应。

### 证明

若 $s(a)=s(a')$ 却有不同响应核，则任何只通过 $s$ 恢复响应的函数在这两个 assignment 上必须给出同一个值，产生矛盾。相反，按核相等定义的商显然使响应核因子化。证毕。

图上的邻域只是一个候选坐标。它可能比真正的响应商更细，也可能漏掉一个远端共同来源或全局约束而过粗。

## 3. 局部结构如何保证暴露商

**定理 3.1（结构局部性推出邻域暴露）。** 设目标节点的结构响应满足

$$
K_v(\cdot\mid a)=G_v(\cdot\mid a|_{N(v)})
$$

对某个邻域 $N(v)\subseteq V$ 与核 $G_v$ 成立。令

$$
e_v(a)=a|_{N(v)}.
$$

则 $e_v$ 是合法暴露商。任何进一步的商

$$
q_v:\mathcal A|_{N(v)}\to\mathcal E_v
$$

只要 $G_v(\cdot\mid z)=G_v(\cdot\mid z')$ whenever $q_v(z)=q_v(z')$，也给出合法的复合暴露 $q_v\circ e_v$。

### 证明

若 $e_v(a)=e_v(a')$，则 $a|_{N(v)}=a'|_{N(v)}$；代入结构假设得到两个响应核相等。进一步商的结论再应用定理 2.1。证毕。

**边界。** 该定理的前提是结构响应确实只读取 $a|_{N(v)}$。如果环境变量、控制器记忆或边界条件把远端 assignment 带入 $G_v$，把“图上邻域”写成 exposure 并不能消除这种依赖；必须把这些通道放回暴露标签或扩大邻域。

## 4. 纤维冲突是暴露商失效的最小证据

**命题 4.1（单个纤维冲突即足够反驳）。** 若存在 $a,a'$ 使

$$
e_v(a)=e_v(a'),
\qquad
K_v(\cdot\mid a)\ne K_v(\cdot\mid a'),
$$

则任何只依赖 $e_v(a)$ 的摘要都不能复现 $K_v$ 的全部 assignment 响应。

### 证明

只依赖 $e_v$ 的摘要在 $a,a'$ 上取相同值；任何后续恢复函数因而也必须给出相同的输出核，与两者不同矛盾。证毕。

**最小结构例子。** 取两个节点 $V=\{1,2\}$，目标为 $v=1$，二元 assignment $a=(a_1,a_2)$。若错误地使用

$$
e_1(a)=a_1,
$$

模型 $P$ 可取 $Y_1(a)=a_1$，而模型 $Q$ 可取

$$
Y_1(a)=a_1\oplus a_2.
$$

在 $e_1=0$ 的纤维中，$P$ 恒为 $0$，但 $Q$ 在 $(0,1)$ 上为 $1$；在 $e_1=1$ 的纤维中同样有冲突。因此单点 treatment 不能作为这两个结构的合法 exposure。

## 5. 设计支持与可识别性是第二道门

**定义 5.1（随机化设计）。** 令 $\pi$ 是 assignment 空间上的设计分布，支持为

$$
S_\pi=\{a\in\mathcal A:\pi(a)>0\}.
$$

设有限结果 $Y_v(a)$ 具有已定义的均值

$$
m_v(a)=\mathbb E[Y_v(a)].
$$

对已支持的 assignment，假设随机化观测核能识别 $m_v(a)$。给定固定权重 $w(a)\ge0$ 且 $\sum_aw(a)=1$，目标为

$$
\mu_w=\sum_{a\in\mathcal A}w(a)m_v(a).
$$

**定理 5.2（全 assignment 加权平均的正性判据）。** 在不额外假设 exposure 因子化时，$\mu_w$ 能由这些被支持 assignment 的均值唯一确定，当且仅当

$$
\boxed{
w(a)>0\Longrightarrow a\in S_\pi.
}
$$

### 证明

若条件成立，目标中的每一项均已识别，有限加权和也已识别。

反过来，若存在 $a_*$ 使 $w(a_*)>0$ 但 $a_*\notin S_\pi$，取两个响应函数 $m,m'$，在 $S_\pi$ 上完全相同，只令 $m'(a_*)=m(a_*)+c$，其中 $c\ne0$ 且仍落在允许结果范围内。设计下的所有观测相同，但

$$
\mu'_w-\mu_w=w(a_*)c\ne0.
$$

所以目标不唯一。证毕。

**推论 5.3（商上的正性与结构假设）。** 若已独立证明合法 exposure 因子化

$$
m_v(a)=\bar m_v(e_v(a)),
$$

且目标权重只要求每个 exposure cell 的平均响应，那么识别所需的是每个具有正目标质量的 cell 至少有一个具有正设计概率的代表 assignment；同一 cell 内其余 assignment 的均值由结构商等式补回。

### 证明

因子化把 cell 内所有均值等同为同一个 $\bar m_v(e)$。每个正质量 cell 只要有一个支持代表，就能识别对应的 $\bar m_v(e)$；代回 cell 权重和即可。若某 cell 没有支持代表，可以把该 cell 的共同响应整体改动而不改变任何观测，目标随之改变。证毕。

这里的“一个代表足够”依赖已经成立的结构等式。没有该等式，设计支持不能替代结构局部性。

## 6. 缺失 assignment 的最小反例

继续取 $V=\{1,2\}$、二元 assignment 与目标节点 $1$。令设计只支持

$$
S_\pi=\{(0,0),(1,0)\}.
$$

构造两个确定性模型：

$$
P:\quad Y_1(a_1,a_2)=a_1,
$$

以及

$$
Q:\quad
Y_1(a_1,a_2)=
\begin{cases}
a_1,&a_2=0,\\
1,&a_2=1.
\end{cases}
$$

**定理 6.1（正性失败与结构差异可分离）。** 在该设计下，$P$ 与 $Q$ 的全部观测相同，但均匀全 assignment 平均分别为

$$
\mu_{1/4}(P)=\frac12,
\qquad
\mu_{1/4}(Q)=\frac34.
$$

同时，$Q$ 在单点 exposure $e_1(a)=a_1$ 下不满足暴露商相容性。

### 证明

在设计支持的两个 assignment 上，$a_2=0$，两模型都给出 $Y_1=a_1$，故观测完全相同。模型 $P$ 的四个结果为 $0,1,0,1$，平均为 $1/2$；模型 $Q$ 的四个结果为 $0,1,1,1$，平均为 $3/4$。最后，$Q(0,0)=0$ 而 $Q(0,1)=1$，这两个 assignment 具有相同的 $e_1$，故纤维冲突成立。证毕。

若把 $Q$ 改为 $Y_1=a_1\oplus a_2$，全 assignment 平均恰好仍可能与 $P$ 相同，但 spillover 对比

$$
Y_1(0,1)-Y_1(0,0)
$$

从 $0$ 变为 $1$。因此一个总平均碰巧相同，也不能证明暴露商合法。

## 7. 直接效应、溢出效应与估计对象

固定目标节点 $v$，对两个 assignment $a,a'$ 定义响应对比

$$
\Delta_v(a,a')=m_v(a)-m_v(a').
$$

若 $a$ 与 $a'$ 只在 $v$ 的 treatment 坐标不同，这是一个直接对比；若只改变邻居坐标，则是一个 spillover 对比。对一般网络，二者都只是完整 assignment 空间上的边方向，不能先假定存在一个只由 $a_v$ 标记的标量效应。

**推论 7.1（暴露商下的对比压缩）。** 若 $m_v=\bar m_v\circ e_v$，则

$$
e_v(a)=e_v(a')\Longrightarrow\Delta_v(a,a')=0.
$$

因此 exposure 商把一部分 assignment 对比合法地压成零；但不同 exposure cell 之间的对比仍需相应设计支持或结构假设。

### 证明

相同 exposure 给出相同 $\bar m_v$ 值，直接相减即得。证毕。

**命题 7.2（SUTVA 是特例而非默认前提）。** 令 $e_v(a)=a_v$。这时定理 2.1 的因子化正是“节点响应只依赖自身 treatment”的 SUTVA 型条件；在网络模型中，必须把它作为结构假设证明或登记，不能因 assignment 被逐点记录就自动得到。

## 8. 因果网络的两阶段关系图

对目标节点的一个可识别结论，至少要经过两层：

$$
\boxed{
\text{完整 assignment profile}
\longrightarrow
\text{合法 exposure 商}
\longrightarrow
\text{设计支持下的 cell 响应}
\longrightarrow
\text{直接/溢出目标}.
}
$$

第一层是结构约束：哪些 assignment 可以被同一个响应函数值代表。第二层是统计约束：这些代表是否真的在设计中以正概率出现。第一层失败时，增加样本量不能修复错误的商；第二层失败时，图上已经知道局部性也不能凭空提供未采 assignment 的响应。

## 9. AHH：网络因果不是节点标签，而是 assignment 的商几何

在有干扰的网络中，因果对象首先是完整 assignment 空间上的响应核。一个 exposure map 只有在每个纤维内响应恒定时才是合法坐标；一旦商合法，设计支持才有资格讨论该商上的平均与对比。

> **AHH：网络因果是两次取商。第一次把完整 assignment 按结构上不可区分的响应纤维压成 exposure；第二次把设计实际覆盖的纤维筛出来。把“未见 spillover”直接当成“没有 spillover”，就是把这两道门混成了一道。**

这一区分也适用于位置或局域事件：事件接口可以只读取一个区域标签，但是否能抹去远端关系，取决于完整响应核在相应纤维上是否真的相等；是否能估计该标签的事件率，则还取决于准备与探测协议对该纤维的支持。

## 追加锚（本行以下为增补区）

## 10. 线性干扰下的设计秩

网络响应有时被限制为一个有限特征的线性模型。令

$$
\varphi(a)=
\bigl(1,a_v,(a_u)_{u\in N(v)}\bigr)\in\mathbb R^d,
\qquad
q_v(a)=\theta^\mathsf T\varphi(a),
$$

并只考虑使所有 $q_v(a)$ 落在允许结果区间内的参数 $\theta$。把设计支持中的特征行堆成矩阵

$$
\Phi_{S_\pi}
=
\begin{bmatrix}
\varphi(a_1)^\mathsf T\\
\vdots\\
\varphi(a_k)^\mathsf T
\end{bmatrix},
\qquad
q_{S_\pi}=\Phi_{S_\pi}\theta.
$$

**定理 10.1（线性对比的设计秩判据）。** 给定参数线性对比 $c^\mathsf T\theta$，由支持 assignment 上的精确响应 $q_{S_\pi}$ 唯一确定，当且仅当

$$
\boxed{
c\in\operatorname{rowspan}(\Phi_{S_\pi}).
}
$$

全部 direct 与 spillover 系数均可识别，当且仅当

$$
\boxed{
\operatorname{rank}(\Phi_{S_\pi})=d.
}
$$

### 证明

若 $c=r^\mathsf T\Phi_{S_\pi}$，则

$$
c^\mathsf T\theta=r^\mathsf Tq_{S_\pi},
$$

右端只由观测响应确定。

反过来，若 $c$ 不在行空间，由有限维线性代数存在 $\delta\in\ker\Phi_{S_\pi}$ 使 $c^\mathsf T\delta\ne0$。取一个使所有 assignment 响应严格落在允许区间内部的参数 $\theta_0$；由于有限个 assignment 只有有限距离，取足够小的非零 $\epsilon$，使 $\theta_0+\epsilon\delta$ 仍然合法。两组参数在 $S_\pi$ 上满足

$$
\Phi_{S_\pi}(\theta_0+\epsilon\delta)
=\Phi_{S_\pi}\theta_0,
$$

但目标对比改变了 $\epsilon c^\mathsf T\delta\ne0$，所以不可能唯一确定。最后一项是取 $c$ 为各坐标基向量的联合判据。证毕。

**例 10.2（支持别名遮住直接与溢出）。** 两个节点的 assignment 为 $(a_1,a_2)\in\{0,1\}^2$，令特征为

$$
\varphi(a)=(1,a_1,a_2),
$$

但设计只支持 $(0,0)$ 与 $(1,1)$。此时

$$
\Phi_{S_\pi}
=
\begin{bmatrix}1&0&0\\1&1&1\end{bmatrix},
\qquad
\operatorname{rank}(\Phi_{S_\pi})=2<3.
$$

常数模型

$$
q_P(a)=\frac12
$$

与

$$
q_Q(a)=\frac12+\frac14(a_1-a_2)
$$

在支持的两个 assignment 上都给出 $1/2$，且四个 assignment 上都落在 $[0,1]$。但 $P$ 的直接系数与邻居 spillover 系数均为零，$Q$ 的两个系数分别为 $1/4$ 与 $-1/4$；未支持的 $(1,0)$ 或 $(0,1)$ 才能把它们切开。

这说明随机化设计的支持不仅决定平均值是否可估计，还决定不同因果方向在参数空间中是否发生别名。结构 exposure 商与线性设计秩分别回答“哪些坐标可以合并”和“剩下的坐标能否从读数中分开”。

## 追加锚（本行以下为增补区）

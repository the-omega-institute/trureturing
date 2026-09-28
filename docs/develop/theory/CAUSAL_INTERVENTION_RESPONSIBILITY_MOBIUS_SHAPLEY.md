# 干预责任的 Möbius—Shapley 几何：协同、抵消与接口归因

> **本卷的机器契约。** 本文是 \`docs/develop/theory/\` 下的纯理论参考输入，只增不减；不承担 Lean、消化账本或冻结状态的数学真值。作者种类为 **AI**，作者/模型为 **OpenAI GPT-6 via Codex**，来源/会话标识为 **持续因果理论目标，2026-09-28**。本文不声称原创性或形式验证。

当多个干预端共同改变一个目标时，「谁负责」不是某一条箭头上预先带着的数。它取决于整张联盟干预响应表，以及对不同干预顺序或联盟的归因规则。

本卷把每个干预联盟的完整结果律保留下来，并在有限幂集格上做两步分解：

$$
\boxed{
\text{联盟响应}
\;\longrightarrow\;
\text{Möbius 交互谱}
\;\longrightarrow\;
\text{Shapley 平均责任}.
}
$$

高阶项表示只有多个端同时出现才产生的协同或抵消；Shapley 值则是一个明确声明过的、对所有合法排列平均的责任分配。它是接口相对的读数，不是模型之外新增的一种因果力。

## 1. AHH：因果效应属于干预联盟格

令 $N=\{1,\ldots,n\}$ 是有限干预端集。对每个联盟 $A\subseteq N$，设一个合法联合干预 $\operatorname{do}(A)$ 已被声明，并给出有限结果集 $Y$ 上的概率律

$$
\mu_A\in\Delta(Y).
$$

$\mu_\varnothing$ 是基线结果律。若只关心某个事件 $E\subseteq Y$，其标量响应为

$$
v_E(A)=\mu_A(E).
$$

但完整的 $\mu_A$ 比单个事件概率保存更多接口信息，下面先在有限 signed-measure 向量空间中工作。

$$
\boxed{
\text{“端 $i$ 有责任”必须相对于}
\quad
A\mapsto\mu_A
\quad
\text{和合法联盟族来定义}.
}
$$

单端响应为零，不排除高阶协同；总响应为零，也不排除正负贡献相互抵消。若只保留基线和全体干预的两张照片，通常连责任分配所需的中间联盟信息都没有。

## 2. 干预格上的 Möbius 交互谱

**定义 2.1（Möbius 交互项）。** 对每个 $T\subseteq N$，定义 signed measure

$$
\Gamma_T
=
\sum_{S\subseteq T}
(-1)^{|T|-|S|}\mu_S.
$$

其中 $T=\varnothing$ 时 $\Gamma_\varnothing=\mu_\varnothing$。

$\Gamma_T$ 是在所有严格子联盟贡献被扣除后，第一次由联盟 $T$ 共同出现的交互项。它可以是带符号的 signed measure，因此不要求自身是概率律。

**定理 2.2（格反演）。** 对任意 $A\subseteq N$，

$$
\boxed{
\mu_A=\sum_{T\subseteq A}\Gamma_T.
}
$$

### 证明

代入定义并交换有限求和：

$$
\begin{aligned}
\sum_{T\subseteq A}\Gamma_T
&=
\sum_{T\subseteq A}
\sum_{S\subseteq T}
(-1)^{|T|-|S|}\mu_S\\
&=
\sum_{S\subseteq A}\mu_S
\sum_{S\subseteq T\subseteq A}
(-1)^{|T|-|S|}.
\end{aligned}
$$

令 $R=T\setminus S$。内层和为

$$
\sum_{R\subseteq A\setminus S}(-1)^{|R|}
=
\begin{cases}
1,&S=A,\\
0,&S\ne A.
\end{cases}
$$

故只剩 $\mu_A$。证毕。

**推论 2.3（唯一性与零质量）。**

1. $\{\Gamma_T\}_{T\subseteq N}$ 是重构全部联盟响应的唯一谱；
2. 对每个非空 $T$，
   $$
   \Gamma_T(Y)=0;
   $$
3. 若某个 $\Gamma_T=0$，则没有纯粹属于 $T$ 的交互项。

### 证明

唯一性由有限 Möbius 反演的逆性得到。对非空 $T$，把定义在 $Y$ 上求总质量：

$$
\Gamma_T(Y)
=
\sum_{S\subseteq T}(-1)^{|T|-|S|}\mu_S(Y)
=
\sum_{S\subseteq T}(-1)^{|T|-|S|}
=
(1-1)^{|T|}=0.
$$

最后一项是定义解释。证毕。

对事件 $E$ 作线性投影，得到标量谱

$$
m_E(T)=\Gamma_T(E),
\qquad
v_E(A)=\sum_{T\subseteq A}m_E(T).
$$

所以事件概率只是完整结果律谱的一个线性切片。

## 3. Shapley 责任的定义

对端 $i\in N$ 和联盟 $S\subseteq N\setminus\{i\}$，定义组合权重

$$
w_{n,S}
=
\frac{|S|!(n-|S|-1)!}{n!}.
$$

它等于在均匀随机排列中，$S$ 恰好是端 $i$ 之前的前缀的概率。

**定义 3.1（完整结果律的 Shapley 责任）。**

$$
\phi_i
=
\sum_{S\subseteq N\setminus\{i\}}
w_{n,S}
\bigl(\mu_{S\cup\{i\}}-\mu_S\bigr).
$$

$\phi_i$ 是 signed measure。对事件 $E$ 的责任为

$$
\phi_i(E)
=
\sum_{S\subseteq N\setminus\{i\}}
w_{n,S}
\bigl(v_E(S\cup\{i\})-v_E(S)\bigr).
$$

这一定义明确选择了「所有端排列等权」的协议。若某些联盟干预不合法，必须改用相应的合法排列分布，不能继续把这个等权数值冒称为唯一责任。

## 4. Möbius 谱到 Shapley 责任

**定理 4.1（Möbius 归因公式）。** 对每个 $i\in N$，

$$
\boxed{
\phi_i
=
\sum_{\substack{T\subseteq N\\i\in T}}
\frac{\Gamma_T}{|T|}.
}
$$

### 证明

由定理 2.2，

$$
\mu_{S\cup\{i\}}-\mu_S
=
\sum_{\substack{T\subseteq S\cup\{i\}\\i\in T}}\Gamma_T.
$$

因为 $i\notin S$，参与差分的 $T$ 必须满足 $i\in T$ 且 $T\setminus\{i\}\subseteq S$。交换有限求和后，$\Gamma_T$ 的系数为

$$
\sum_{S:\,T\setminus\{i\}\subseteq S\subseteq N\setminus\{i\}}
\frac{|S|!(n-|S|-1)!}{n!}.
$$

这个系数正是随机排列中 $T\setminus\{i\}$ 的所有成员都排在 $i$ 之前、且 $T$ 中 $i$ 是最后一个的概率。对 $T$ 内部的 $|T|$ 个位置等可能，故概率为 $1/|T|$。于是得到所给公式。证毕。

**推论 4.2（效率）。**

$$
\boxed{
\sum_{i\in N}\phi_i
=
\mu_N-\mu_\varnothing.
}
$$

### 证明

对每个非空 $T$，公式 4.1 中 $\Gamma_T$ 在恰好 $|T|$ 个端上出现，每次系数 $1/|T|$，总系数为一。再用定理 2.2 的 $A=N$ 与 $A=\varnothing$ 两式相减。证毕。

效率只说责任总和恢复全体干预相对于基线的变化；它不说每个分量都是非负概率，也不把 signed measure 当成新的结果律。

## 5. 四条公理下的唯一分配

把一个「联盟响应游戏」写成任意有限维向量值映射

$$
g:2^N\to V,
\qquad
g(\varnothing)=0,
$$

其中 $V$ 可以是实数、事件概率向量或 signed-measure 向量。一个责任规则给每个端 $i$ 一个 $\Psi_i(g)\in V$。

考虑以下四条接口公理：

1. **效率**：$\sum_i\Psi_i(g)=g(N)$；
2. **对称性**：交换两个在所有联盟边际上等价的端，责任也交换；
3. **虚无端**：若 $g(S\cup\{i\})=g(S)$ 对所有 $S$，则 $\Psi_i(g)=0$；
4. **加性**：$\Psi_i(g+h)=\Psi_i(g)+\Psi_i(h)$。

**定理 5.1（Shapley 唯一性）。** 满足上述四条公理的责任规则唯一，并且等于定义 3.1 的 Shapley 规则。

### 证明

对每个非空 $T\subseteq N$ 和 $v\in V$，定义 unanimity 游戏

$$
u_T^v(A)
=
\begin{cases}
v,&T\subseteq A,\\
0,&T\nsubseteq A.
\end{cases}
$$

Möbius 反演把任意 $g$ 唯一写成

$$
g=\sum_{\varnothing\ne T\subseteq N}u_T^{m(T)},
$$

其中 $m(T)$ 是其交互谱。

在 $u_T^v$ 中，$T$ 外端是虚无端，$T$ 内端由对称性必须获得相同值。效率要求 $T$ 内各端之和为 $v$，所以每个端必须获得 $v/|T|$。由加性，

$$
\Psi_i(g)
=
\sum_{T\ni i}\frac{m(T)}{|T|},
$$

这正是定理 4.1。证毕。

唯一性依赖于四条公理和全体联盟响应；改变合法排列权重或删除联盟后，公理系统与结论都会改变。

## 6. 协同反例：没有单端效应仍有责任

取 $N=\{1,2\}$、$Y=\{0,1\}$，令

$$
\mu_\varnothing=\delta_0,
\qquad
\mu_{\{1\}}=\delta_0,
\qquad
\mu_{\{2\}}=\delta_0,
\qquad
\mu_{\{1,2\}}=\delta_1.
$$

单端干预都不改变结果：

$$
\mu_{\{1\}}-\mu_\varnothing=0,
\qquad
\mu_{\{2\}}-\mu_\varnothing=0.
$$

但 Möbius 项为

$$
\Gamma_{\{1,2\}}=\delta_1-\delta_0,
$$

因此

$$
\phi_1=\phi_2=\frac12(\delta_1-\delta_0).
$$

全体效应完全由二端协同产生。把「单端无效」解释成「两端都没有责任」会遗漏这份高阶关系。

## 7. 抵消反例：总效应为零不等于路径贡献为零

仍取 $N=\{1,2\}$，令

$$
\mu_\varnothing=\delta_0,
\qquad
\mu_{\{1\}}=\delta_1,
\qquad
\mu_{\{2\}}=\delta_1,
\qquad
\mu_{\{1,2\}}=\delta_0.
$$

以事件 $E=\{1\}$ 的概率为标量响应，则

$$
v(\varnothing)=0,\quad
v(\{1\})=v(\{2\})=1,\quad
v(\{1,2\})=0.
$$

相应交互项为

$$
m(\{1\})=m(\{2\})=1,
\qquad
m(\{1,2\})=-2.
$$

于是

$$
\phi_1=1+\frac{-2}{2}=0,
\qquad
\phi_2=1+\frac{-2}{2}=0,
$$

而全体效应也为零。这里零责任是正单端项与负协同项抵消后的归因结果，不是说中间联盟响应没有改变。

## 8. 只看首末联盟不能决定谁负责

**定理 8.1（端点响应的责任不可识别）。** 存在两个联盟响应族，它们具有相同的 $\mu_\varnothing$ 与 $\mu_N$，但 Shapley 责任向量不同。

### 证明

取 $N=\{1,2\}$、$Y=\{0,1\}$。模型 $A$ 为

$$
\mu_\varnothing=\delta_0,\quad
\mu_{\{1\}}=\delta_1,\quad
\mu_{\{2\}}=\delta_0,\quad
\mu_{\{1,2\}}=\delta_1.
$$

模型 $B$ 交换两个单端联盟：

$$
\mu_\varnothing=\delta_0,\quad
\mu_{\{1\}}=\delta_0,\quad
\mu_{\{2\}}=\delta_1,\quad
\mu_{\{1,2\}}=\delta_1.
$$

两者首末响应完全相同。模型 $A$ 的标量事件责任为

$$
(\phi_1,\phi_2)=(1,0),
$$

模型 $B$ 的责任为

$$
(\phi_1,\phi_2)=(0,1).
$$

因此端点记录不能恢复端点之间的归因。证毕。

这是一种信息缺口而不是计算困难：任何只读取 $\mu_\varnothing,\mu_N$ 的后处理函数，在两个模型上输入相同，不能输出两种不同责任。

## 9. 被动相关不替代联盟干预表

责任谱使用的是 $\mu_A$，即同一模型中一组共同允许的干预响应。被动联合分布只给出观察条件下哪些读数一起出现，不能自动提供每个 $\operatorname{do}(A)$ 的结果律。

若两个结构模型在被动联合分布上相同，但某个局部干预后的目标律不同，则它们的 $\mu_A$ 谱和 Shapley 责任也可能不同。于是：

$$
\boxed{
\text{观察相关表}
\;\not\Rightarrow\;
\text{联盟响应表}
\;\not\Rightarrow\;
\text{唯一责任分配}.
}
$$

只有在干预接口、共同来源和所有联盟的结果律都被声明后，Möbius—Shapley 计算才有其操作对象。

## 10. 有限查询阶数造成责任盲核

若实验只取得所有满足 $|A|\le k$ 的联盟响应，那么任何支持在 $|T|>k$ 的谱项都不会出现在这些读数中。对任意非零 signed measure $q$，可在一个完整模型中加入高阶项

$$
\Gamma_T=q,\qquad |T|>k,
$$

并通过调整可行的基础概率律构造另一个模型，使所有低阶 $\mu_A$ 保持相同，而高阶联盟不同。

因此低阶记录只能确定责任谱的低阶投影：

$$
\{\Gamma_T:|T|\le k\},
$$

不能确定每个端的完整

$$
\phi_i=\sum_{T\ni i}\frac{\Gamma_T}{|T|}.
$$

这和「能否识别高阶交互」是同一个信息边界的两个读法：高阶交互未被查询切开时，责任分配也留在盲核中。

## 11. 合法顺序改变时，责任规则改变

若不是所有联盟或排列都可执行，令 $\Pi$ 是一份声明过的合法排列分布。对排列 $\pi$，记 $P_i^\pi$ 为端 $i$ 在 $\pi$ 中之前的前缀。定义协议相对的责任：

$$
\phi_i^\Pi
=
\mathbb E_{\pi\sim\Pi}
\left[
\mu_{P_i^\pi\cup\{i\}}-\mu_{P_i^\pi}
\right].
$$

当 $\Pi$ 是全体排列的均匀分布时，它退化为 $\phi_i$。一般 $\Pi$ 下，某个高阶项 $\Gamma_T$ 分到端 $i$ 的系数为

$$
q_i^\Pi(T)
=
\Pr_{\pi\sim\Pi}
\bigl(
i\text{ 是 }T\text{ 中最后出现的端}
\bigr),
$$

且

$$
\phi_i^\Pi
=
\sum_{T\ni i}q_i^\Pi(T)\Gamma_T,
\qquad
\sum_{i\in T}q_i^\Pi(T)=1.
$$

所以责任不是脱离协议的坐标不变量。同步规则、资源限制或安全约束若改变可执行排列集合，必须重新声明 $\Pi$；把新的分配继续称为原来的「唯一责任」会隐藏接口变化。

## 12. 位置事件是责任谱的线性投影

设目标事件为一个区域点击、位置记录或任意 $E\subseteq Y$。由线性性，

$$
\phi_i(E)
=
\left(\phi_i\right)(E),
\qquad
m_E(T)=\Gamma_T(E).
$$

因此：

- 完整结果律谱相同，所有事件责任都相同；
- 完整结果律谱不同，某个事件投影可能仍然看不见差异；
- 一个位置事件的零责任只说明该事件投影中的边际与交互相消，不说明完整记录律没有责任结构。

这把位置归因放回已声明的探测接口，而不是把「责任」当作粒子额外携带的标签。

## 13. 结论：责任是格上的选择性压缩

本卷的核心等式是

$$
\boxed{
\mu_A=\sum_{T\subseteq A}\Gamma_T,
\qquad
\phi_i=\sum_{T\ni i}\frac{\Gamma_T}{|T|}.
}
$$

第一式保存完整联盟响应的交互谱；第二式在等权合法排列下把每个高阶项平均分给其参与端。协同项、抵消项、端点不可识别和顺序依赖都由同一幂集格显现出来。

> **AHH：因果责任不是箭头上的固定重量，而是对完整干预联盟关系所作的一次有规则的压缩；先保留高阶交互，再谈谁分到多少。**

若没有完整联盟接口，责任问题可能是不可识别的；若改变合法排列规则，责任读数也会改变。结论始终相对于模型、可执行干预族、结果接口和归因协议。

## 追加锚（本行以下为增补区）

# 动力接口—余量演算
## ——商下降、carry、交换子流、预测闭包、记忆与因果查询的统一形式理论

**版本：v1.0，2026-08-22**

---

## 摘要

本文把仓库近期分别出现于概念动力学、量子观察者、有限记忆、Hilbert 残余塔、因果查询与负底黄金进制前沿中的结构，压缩为一个共同问题：

> 给定完整状态、观察接口与动力学，动力学何时能在观察者所见的商空间上良定义？若不能，缺失部分应如何分类、度量与修复？

核心对象是三元组

\[
\mathfrak I=(X,q,F),
\]

其中 \(X\) 是完整状态空间，\(q:X\to B\) 是观察接口，\(F:X\to X\) 是更新。本文证明：在有效像上，以下陈述等价：动力学沿 \(q\) 精确下降；\(q\) 的核关系被 \(F\) 保持；不存在 carry witness；一步未来读数由当前读数唯一决定。有限系统中，这还等价于读数函数代数对 Koopman 拉回闭合，以及有限未来词精化在当前深度稳定。

在线性与量子实例中，同一缺陷变成块矩阵的交叉项。若 \(P\) 是可见投影、\(Q=I-P\)，则

\[
[P,T]=PTQ-QTP.
\]

其中 \(PTQ\) 是隐藏方向对下一步可见读数的影响，正是线性化的一步 carry；\(QTP\) 是可见方向向隐藏余量的泄漏。对自伴生成元，两者互为伴随，因而一侧消失即两侧同时消失。对 Hamiltonian 流，投影事件概率的导数

\[
\frac{d}{dt}\operatorname{Tr}(\rho_tP)
=
\operatorname{Re}\!\left(i\operatorname{Tr}(\rho_t[H,P])\right)
\]

是接口缺陷的无穷小通量。

本文进一步建立：

1. 有限未来词塔是 carry 的规范最小修复；
2. 最小预测商是当前读数核中最大的前向不变等价关系；
3. 其对偶是包含当前读数代数的最小动力学不变可观测代数；
4. 随机系统中的对应条件是强 lumpability，TV 缺陷给出任何近似下降的不可突破误差下界；
5. 有限确定性预测核在线性化后分解为幂零暂态与可逆周期核；
6. 因果观察、干预与反事实是同一查询商理论中逐层收缩的 kernel；
7. 无限维或超限观察塔必须区分强完成与一致完成，残余维数本身不能作为完成进度；
8. 当前 negative-base-\(\varphi\) 三叉戟前沿的剩余问题可精确重写为一个相位接口上的两值 gap 因子化命题。

本文是单一 Markdown 理论稿。除明确列出的仓库 Lean 锚点外，新增统一定理均为本文给出的 paper-level 证明，不声称已经 Lean 闭合。

---

# 0. 真值层级、符号与非主张

## 0.1 真值层级

本文使用四种状态标签：

- **定义**：保守引入记号；
- **本文定理**：在本文中给出数学证明，但不声称仓库已有 Lean proof term；
- **Lean 锚点**：仓库已有机器证明，本文只抽取其结构含义；
- **条件命题／路线**：依赖尚未闭合的桥，不得当作已证结论。

## 0.2 基本符号

给定集合或类型 \(X,B\)：

\[
q:X\to B
\]

称为接口。其核关系为

\[
x\sim_q y
\iff
q(x)=q(y).
\]

为避免非满射接口在像外产生任意延拓，定义有效像：

\[
B_q:=\operatorname{Im}(q),
\qquad
\widehat q:X\twoheadrightarrow B_q.
\]

后文所有“唯一下降”均指向有效像上的唯一性。

## 0.3 非主张

本文不主张：

1. carry、交换子、因果混杂与量子退相干在物理本体上完全相同；本文只证明它们共享同一类**接口下降障碍**；
2. 任意非交换性都来自观察不完备；
3. 所有量子不可逆性都只是访问权缺陷；仓库现有定理给出的是一个显式有限维反模型；
4. 预测完成等于自描述完成；
5. 本文推进或证明黎曼假设；
6. 当前 negative-base-\(\varphi\) 主定理已经闭合；本文只重新定位其最后余量。

---

# 1. 接口不是状态压缩，而是目标相对的商

## 定义 1.1（接口核）

\[
K_q:=\{(x,y)\in X^2:q(x)=q(y)\}.
\]

接口保留的不是“多少字节”，而是哪些状态对仍可区分。两个不同编码只要具有相同核，便在纯确定性目标因子化意义下表达同一个观察能力。

## 定义 1.2（目标充分性）

对目标 \(T:X\to Y\)，称 \(q\) 对 \(T\) 充分，若存在

\[
\overline T:B_q\to\operatorname{Im}(T)
\]

满足

\[
T=\overline T\circ\widehat q.
\]

## 定理 1.1（核判据）

以下等价：

\[
T\text{ 沿 }q\text{ 因子化};
\]

\[
K_q\subseteq K_T;
\]

\[
q(x)=q(y)\Longrightarrow T(x)=T(y).
\]

### 证明

若 \(T=\overline T\circ\widehat q\)，则相同 \(q\)-值经同一 \(\overline T\) 得到相同 \(T\)-值。反向定义

\[
\overline T(\widehat q(x)):=T(x).
\]

核包含保证该定义与代表元无关；有效像满射保证唯一性。\(\square\)

## 推论 1.1（充分性只对目标成立）

一个接口可能对决策目标充分，却对完整 payoff profile 不充分；可能对单世界干预边缘充分，却对跨世界 joint 不充分；可能对每个固定有限时间窗充分，却对全部未来不充分。

因此“观察者完整”必须写出目标族，不能作为无下标形容词使用。

---

# 2. 精确动力学下降与 carry 的完全等价

给定更新

\[
F:X\to X.
\]

## 定义 2.1（精确下降）

称 \(F\) 沿接口 \(q\) 精确下降，若存在唯一

\[
\overline F:B_q\to B_q
\]

使交换方块成立：

\[
\boxed{
\widehat q\circ F
=
\overline F\circ\widehat q.
}
\]

## 定义 2.2（carry witness）

\[
\operatorname{Carry}(q,F)
:=
\{(x,y):q(x)=q(y),\ q(Fx)\neq q(Fy)\}.
\]

它表示当前接口把 \(x,y\) 合并，但下一步又要求区分它们。

## 定理 2.1（动力接口基本等价定理）

以下等价：

1. \(F\) 沿 \(q\) 精确下降；
2. \(K_q\) 对 \(F\) 前向不变：
   \[
   (x,y)\in K_q\Longrightarrow(Fx,Fy)\in K_q;
   \]
3. \(\operatorname{Carry}(q,F)=\varnothing\)；
4. 下一步读数 \(q\circ F\) 沿 \(q\) 因子化。

### 证明

(1) 推出 (2)：若 \(q(x)=q(y)\)，则

\[
q(Fx)=\overline F(qx)=\overline F(qy)=q(Fy).
\]

(2) 与 (3) 只是同一命题的否定形式。

(2) 推出 (1)：定义

\[
\overline F(\widehat q(x)):=\widehat q(Fx).
\]

前向不变性保证与代表元无关；满射给出唯一性。

(1) 与 (4) 的等价由定理 1.1 立即得到。\(\square\)

## Lean 锚点 2.1

仓库定理

`D5/S3/ConceptDynamics/Dialectics/ExactDescentNoCarry.exact_descent_has_no_carry`

已经机器证明“精确交换方块排除 carry witness”的方向。本文定理 2.1 补齐其有效像上的反向构造，并把它提升为统一核判据。

## 原理 2.1（carry 不是神秘额外量）

carry 不是附加到动力学上的新实体；它正是交换方块无法填写时留下的见证：

\[
\boxed{
\text{carry}
=
\text{failure of descent}.
}
\]

---

# 3. 有限未来词塔：carry 的规范最小修复

一次 carry 的直接修复不是猜测隐藏本体，而是把实际需要的下一步读数加入接口。

## 定义 3.1（有限未来词接口）

对 \(n\in\mathbb N\)，定义

\[
q^{[n]}(x)
:=
\bigl(q(x),q(Fx),\ldots,q(F^n x)\bigr).
\]

其核为

\[
K_n
:=
K_{q^{[n]}}
=
\bigcap_{j=0}^{n}(F^j\times F^j)^{-1}K_q.
\]

于是

\[
K_{n+1}\subseteq K_n.
\]

## 定理 3.1（一步修复的普适性质）

接口

\[
q^{[1]}=(q,q\circ F)
\]

是同时保留当前读数并决定下一步读数的最粗接口。

更精确地，若 \(r:X\to C\) 且存在 \(a,b\) 使

\[
q=a\circ r,
\qquad
q\circ F=b\circ r,
\]

则

\[
q^{[1]}=(a,b)\circ r.
\]

### 证明

逐点代入即可：

\[
q^{[1]}(x)
=(a(r(x)),b(r(x))).
\]

故任意完成这两个任务的接口都必须至少区分 \(q^{[1]}\) 所区分的状态。\(\square\)

## 定理 3.2（有限窗最小充分性）

\(q^{[n]}\) 是对目标族

\[
\{q,q\circ F,\ldots,q\circ F^n\}
\]

同时充分的最粗接口。

### 证明

将定理 3.1 的二元乘积替换为有限 dependent product。\(\square\)

## 定理 3.3（稳定即下降）

以下等价：

\[
K_n=K_{n+1};
\]

\[
K_n\text{ 对 }F\text{ 前向不变};
\]

\[
F\text{ 沿 }q^{[n]}\text{ 精确下降}.
\]

### 证明

\(K_n\) 已经记录第 \(0\) 至 \(n\) 步。要求 \(F\)-不变，只额外要求第 \(n+1\) 步相等，恰好是 \(K_{n+1}\) 不再严格细化。再应用定理 2.1。\(\square\)

## 定义 3.2（全未来核）

\[
K_\infty
:=
\bigcap_{n\ge0}K_n
=
\{(x,y):\forall n,\ q(F^nx)=q(F^ny)\}.
\]

## 定理 3.4（最小预测完成）

\(K_\infty\) 是包含于 \(K_q\) 的最大 \(F\)-不变等价关系。因此

\[
Z_q:=X/K_\infty
\]

是保留当前读数并使动力学下降的最粗精化。

### 证明

首先，若 \(xK_\infty y\)，则对所有 \(n\)，

\[
q(F^n(Fx))=q(F^{n+1}x)=q(F^{n+1}y)=q(F^n(Fy)),
\]

故 \(FxK_\infty Fy\)。

设 \(R\subseteq K_q\) 为任意 \(F\)-不变等价关系。若 \(xRy\)，反复使用不变性得 \(F^nx\,R\,F^ny\)；再由 \(R\subseteq K_q\) 得所有未来读数相等，因此 \(R\subseteq K_\infty\)。\(\square\)

## 定理 3.5（有限稳定界）

若 \(X\) 有限，则存在最小 \(m_*\) 使

\[
K_{m_*}=K_{m_*+1}=K_\infty,
\]

且

\[
\boxed{
 m_*
\le
|X/K_\infty|-|X/K_q|
\le
|X|-|\operatorname{Im}(q)|.
}
\]

### 证明

每次严格细化都使等价类数至少增加一，而类数从 \(|\operatorname{Im}(q)|\) 起步、至多达到 \(|X|\)。一旦不再严格细化，由定理 3.3 得前向不变，此后永久稳定。\(\square\)

---

# 4. 对偶表述：最小动力学不变可观测代数

本节令 \(X\) 为有限集合，\(\mathbb K\) 为至少含两个元素的域，通常取 \(\mathbb C\)。

## 定义 4.1（接口代数）

\[
\mathcal A_q
:=
\{f\circ q:f:B_q\to\mathbb K\}
\subseteq
\mathbb K^X.
\]

它恰由所有在 \(K_q\)-类上常值的函数组成。

定义 Koopman 拉回：

\[
F^*g:=g\circ F.
\]

## 定理 4.1（下降—代数闭合对偶）

以下等价：

1. \(F\) 沿 \(q\) 下降；
2. \(F^*\mathcal A_q\subseteq\mathcal A_q\)；
3. 每个当前可观测量的下一步值仍是当前接口的函数。

### 证明

若 \(qF=\overline Fq\)，则

\[
F^*(f\circ q)
=f\circ q\circ F
=f\circ\overline F\circ q\in\mathcal A_q.
\]

反向，取足以分离 \(B_q\) 中点的函数族。若 \(q(x)=q(y)\)，闭合性令所有函数在 \(q(Fx),q(Fy)\) 上取同值，故两点相等。应用定理 2.1。\(\square\)

## 定义 4.2（深度代数）

\[
\mathcal A_n
:=
\mathcal A_{q^{[n]}}.
\]

## 定理 4.2（代数递推）

\[
\boxed{
\mathcal A_{n+1}
=
\operatorname{Alg}\bigl(\mathcal A_0\cup F^*\mathcal A_n\bigr).
}
\]

这里右侧是在 \(\mathbb K^X\) 中生成的最小含幺函数代数。

### 证明

\(\mathcal A_0\) 区分当前读数，\(F^*\mathcal A_n\) 区分第 \(1\) 至 \(n+1\) 步读数。二者共同诱导的等价关系是

\[
K_q\cap(F\times F)^{-1}K_n=K_{n+1}.
\]

有限集合上，含幺函数代数由其点分离关系唯一决定。\(\square\)

## 推论 4.1（最小不变代数）

\[
\mathcal A_\infty
:=
\bigcup_n\mathcal A_n
\]

在有限系统中稳定为包含 \(\mathcal A_q\) 的最小 \(F^*\)-不变含幺代数，并与最小预测商满足

\[
\mathcal A_\infty\cong\mathbb K^{Z_q}.
\]

## Lean 锚点 4.1

仓库定理

`D5/S3/Quantum/Dynamics/LeastInvariantObservableAlgebra.least_invariant_observable_algebra`

已经在有限预测塔实例中机器证明最小稳定可观测代数。本文给出其集合商版本与核关系证明。

---

# 5. 线性接口：carry 变成交叉块

令 \(H\) 为 Hilbert 空间，\(P:H\to H\) 为正交投影，

\[
Q:=I-P,
\qquad
H=V\oplus R,
\quad
V=\operatorname{ran}P,
\quad
R=\operatorname{ran}Q.
\]

令 \(T:H\to H\) 为有界线性算子。

## 定理 5.1（四块分解）

\[
\boxed{
T=PTP+PTQ+QTP+QTQ.
}
\]

其中：

- \(PTP:V\to V\) 是可见内动力学；
- \(QTQ:R\to R\) 是余量内动力学；
- \(PTQ:R\to V\) 是隐藏对下一步可见量的影响；
- \(QTP:V\to R\) 是可见状态向余量的泄漏。

## 定理 5.2（线性下降判据）

把接口取为 \(q=P:H\to V\)。以下等价：

1. 存在线性 \(\overline T:V\to V\) 使
   \[
   PT=\overline TP;
   \]
2. \(PTQ=0\)；
3. \(PTx\) 只依赖于 \(Px\)。

此时唯一下降为

\[
\overline T=PT|_V.
\]

### 证明

若 \(PT=\overline TP\)，右乘 \(Q\) 得 \(PTQ=\overline TPQ=0\)。反向由

\[
PT=PT(P+Q)=PTP
\]

并取 \(\overline T=PT|_V\)。\(\square\)

## 定理 5.3（不变、余不变与 reducing）

\[
T(V)\subseteq V
\iff
QTP=0,
\]

\[
T(R)\subseteq R
\iff
PTQ=0,
\]

而

\[
V\text{ reducing for }T
\iff
PTQ=QTP=0.
\]

注意：**一步可见下降只要求 \(PTQ=0\)**；它不要求可见方向永不泄漏到隐藏方向。若泄漏随后反馈回来，多步预测仍可能失败，这正是未来词塔继续精化的原因。

## 定理 5.4（交换子就是双向交叉块）

\[
\boxed{
[P,T]=PTQ-QTP.
}
\]

因此

\[
[P,T]=0
\iff
PTQ=QTP=0.
\]

### 证明

\[
PT-TP
=PT(P+Q)-(P+Q)TP
=PTQ-QTP.
\]

两项的定义域和值域互换，故同时为零恰为 reducing。\(\square\)

## 定理 5.5（Hilbert–Schmidt 缺陷恒等式）

若 \(H\) 有限维，则

\[
\boxed{
\|[P,T]\|_{HS}^2
=
\|PTQ\|_{HS}^2+
\|QTP\|_{HS}^2.
}
\]

若 \(T=T^*\)，则

\[
PTQ=(QTP)^*,
\]

从而

\[
\boxed{
\|[P,T]\|_{HS}^2
=2\|PTQ\|_{HS}^2
=2\|QTP\|_{HS}^2.
}
\]

### 证明

\(PTQ\) 与 \(QTP\) 在 Hilbert–Schmidt 内积下正交，因为交叉项含 \(PQ=QP=0\)。自伴情形由取伴随直接得到。\(\square\)

## 最深解释 5.1

集合论 carry 与线性交换子不是比喻关系，而是以下精确对应：

\[
\boxed{
\begin{aligned}
q(x)=q(y),\ q(Tx)\neq q(Ty)
&\longleftrightarrow
PTQ\neq0,\\
\text{可见方向泄入余量}
&\longleftrightarrow
QTP\neq0,\\
\text{双向接口完全闭合}
&\longleftrightarrow
[P,T]=0.
\end{aligned}
}
\]

---

# 6. 未读测量：算子空间中的正交接口

令 \((P_i)_{i\in I}\) 为有限完备正交投影族，定义 pinching／未读测量通道

\[
\mathcal D(X):=\sum_iP_iXP_i.
\]

## Lean 锚点 6.1

仓库定理

`D5/S3/Observer/Conditioning/UnreadStateOrthogonalProjection.unread_state_orthogonal_projection`

已经机器证明：

\[
\mathcal D^2=\mathcal D,
\]

\[
\langle\mathcal D(X),Y\rangle_{HS}
=
\langle X,\mathcal D(Y)\rangle_{HS},
\]

\[
\operatorname{ran}\mathcal D
=
\{X:\forall i\neq j,\ P_iXP_j=0\},
\]

以及

\[
X=\mathcal D(X)+(I-\mathcal D)(X),
\]

\[
\|X\|_{HS}^2
=
\|\mathcal D(X)\|_{HS}^2
+
\|(I-\mathcal D)(X)\|_{HS}^2.
\]

因此 \(\mathcal D\) 不是“像投影”，而是在 Hilbert–Schmidt 算子空间中真正的正交投影。

## 定义 6.1（通道级 carry）

对线性演化生成元或一步超算子 \(\mathcal L\)，定义

\[
\mathcal C_{\mathrm{in}}
:=
\mathcal D\mathcal L(I-\mathcal D),
\]

\[
\mathcal C_{\mathrm{out}}
:=
(I-\mathcal D)\mathcal L\mathcal D.
\]

前者是未读相干余量对下一步可见块的影响，后者是可见块向相干余量的生成。

## 定理 6.1（通道交换子分解）

\[
\boxed{
[\mathcal D,\mathcal L]
=
\mathcal C_{\mathrm{in}}-
\mathcal C_{\mathrm{out}}.
}
\]

并且：

\[
\mathcal L\text{ 沿 }\mathcal D\text{ 一步下降}
\iff
\mathcal C_{\mathrm{in}}=0;
\]

\[
\operatorname{ran}\mathcal D\text{ 对 }\mathcal L\text{ 不变}
\iff
\mathcal C_{\mathrm{out}}=0;
\]

\[
[\mathcal D,\mathcal L]=0
\iff
\text{可见块与相干余量均被分别保持}.
\]

### 证明

将定理 5.2–5.4 应用于算子 Hilbert 空间中的投影 \(\mathcal D\)。\(\square\)

## 推论 6.1（记录丢弃与动力学不闭合是两个问题）

即使 \(\mathcal D\) 本身是完美正交投影，也不代表后续动力学在其像上闭合。测量接口的几何正确性与动力学自然性必须分开审计。

---

# 7. Hamiltonian 流：交换子是接口缺陷的无穷小通量

令

\[
U_t=e^{-itH},
\qquad
\rho_t=U_t\rho U_t^*,
\]

其中 \(H=H^*\)，令 \(P=P^2=P^*\) 为事件投影。

## Lean 锚点 7.1

仓库定理

`D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.projection_probability_flow`

已经机器证明：

\[
p_P(t):=\operatorname{Tr}(\rho_tP)
\]

满足

\[
\boxed{
\frac{d}{dt}p_P(t)
=
\operatorname{Re}\!\left(
 i\operatorname{Tr}(\rho_t(HP-PH))
\right).
}
\]

并且

\[
[H,P]=0
\Longrightarrow
p_P(t)=p_P(0)
\quad\forall t\in\mathbb R.
\]

## 定理 7.1（无穷小 reducing 判据）

在有限维中，以下等价：

\[
[H,P]=0;
\]

\[
[U_t,P]=0\quad\forall t;
\]

\[
P\text{ 与 }Q=I-P\text{ 的两块在整个 Hamiltonian 流下分别不变}.
\]

### 证明

\([H,P]=0\) 时指数函数与 \(P\) 交换。反向对 \([U_t,P]=0\) 在 \(t=0\) 求导，得到 \(-i[H,P]=0\)。\(\square\)

## 原理 7.1（单态零导数不等于接口闭合）

某个特定 \(\rho,t\) 上

\[
\operatorname{Tr}(\rho_t[H,P])=0
\]

只表示该状态在该时刻的净通量抵消；它不推出 \([H,P]=0\)。结构闭合要求对全部状态成立，等价于算子交换子本身为零。

## 统一句 7.1

\[
\boxed{
\text{deterministic carry}
\rightarrow
\text{linear cross block}
\rightarrow
\text{Hamiltonian commutator}
\rightarrow
\text{probability flux}.
}
\]

这是同一接口缺陷从离散到线性、再到无穷小动力学的逐级表示。

---

# 8. 随机动力学：强 lumpability 与定量 carry

令 \(K(x,\cdot)\) 为 \(X\) 上 Markov kernel，\(q:X\to B\)。记

\[
q_*K_x
\]

为从状态 \(x\) 出发一步后观察到的 \(B\)-分布。

## 定义 8.1（强 lumpability）

\[
q(x)=q(y)
\Longrightarrow
q_*K_x=q_*K_y.
\]

## 定理 8.1（随机下降定理）

以下等价：

1. 存在有效像上的 Markov kernel \(\overline K\) 满足
   \[
   q_*K_x=\overline K_{q(x)};
   \]
2. \(K\) 对 \(q\) 强 lumpable；
3. 一步观察 law 只依赖当前观察值。

### 证明

与定理 2.1 相同，只把确定性下一状态替换为概率测度，并按 fiber 定义 \(\overline K\)。\(\square\)

## 定义 8.2（TV carry 缺陷）

\[
\delta_q(K)
:=
\sup_{q(x)=q(y)}
\operatorname{TV}(q_*K_x,q_*K_y).
\]

于是

\[
\delta_q(K)=0
\iff
K\text{ 对 }q\text{ 强 lumpable}.
\]

## 定理 8.2（任何近似下降的误差下界）

定义最佳 Markov 下降误差

\[
\varepsilon_q^*(K)
:=
\inf_{\overline K}
\sup_x
\operatorname{TV}
\bigl(q_*K_x,\overline K_{q(x)}\bigr).
\]

则

\[
\boxed{
\frac12\delta_q(K)
\le
\varepsilon_q^*(K).
}
\]

若每个 fiber 选定代表元，则还有

\[
\varepsilon_q^*(K)
\le
\delta_q(K).
\]

### 证明

对同一 fiber 中任意 \(x,y\)，三角不等式给出

\[
\operatorname{TV}(q_*K_x,q_*K_y)
\le
e_x+e_y,
\]

故至少一个误差不小于该 pair 距离的一半。取上确界与下确界得到下界。上界取每个 fiber 的代表分布作为 \(\overline K\)。\(\square\)

## 定理 8.3（目标后处理收缩）

对任意可测后处理 \(r:B\to C\)，定义固定 source fiber 上的后处理缺陷：

\[
\delta_q^{r}(K)
:=
\sup_{q(x)=q(y)}
\operatorname{TV}
\bigl(r_*q_*K_x,r_*q_*K_y\bigr).
\]

则

\[
\boxed{
\delta_q^{r}(K)
\le
\delta_q(K).
}
\]

### 证明

全变差距离在 Markov 后处理下不增加。\(\square\)

## 警告 8.1（source coarsening 没有单调律）

把 source 接口从 \(q\) 改为 \(r\circ q\) 会同时扩大待比较 fiber、又压缩目标分布，两个效应方向相反。因此总体缺陷可能增大、减小或被完全掩盖。不得把数据处理不等式误用于 source coarsening。

---

# 9. 组合律、隐藏 carry 与规范修复

## 定理 9.1（下降的组合）

若

\[
qF=\overline Fq
\]

且

\[
r\overline F=\widetilde F r,
\]

则

\[
(rq)F=\widetilde F(rq).
\]

### 证明

交换方块复合。\(\square\)

## 反例 9.1（粗接口可以隐藏 carry）

取

\[
X=\{a,b,c\},
\]

\[
q(a)=q(b)=0,
\qquad
q(c)=1,
\]

以及

\[
F(a)=a,
\qquad
F(b)=c,
\qquad
F(c)=c.
\]

则 \((a,b)\) 是 \(q\) 的 carry witness，因为

\[
q(a)=q(b),
\qquad
q(Fa)=0\neq1=q(Fb).
\]

但若 \(r:\{0,1\}\to\{*\}\) 为常值映射，则 \(r\circ q\) 总能下降。

所以

\[
(rq)\text{ 可下降}
\not\Rightarrow
q\text{ 可下降}.
\]

粗接口的“闭合”可能只是把缺陷目标一起删除。

## 定义 9.1（隐藏 carry）

若 \(rq\) 可下降而 \(q\) 不可下降，则称 carry 被后处理 \(r\) 隐藏。

## 原理 9.1（修复三分）

面对 carry 有三种数学上不同的处理：

1. **源接口精化**：加入未来词、记忆或新传感器；
2. **目标压缩**：只保留能沿当前接口下降的后处理；
3. **动力学约束**：修改或控制 \(F\)，使其保持当前 kernel。

三者分别对应“看得更多”“要求更少”“让世界按接口闭合”。它们不能互相冒充。

---

# 10. 记忆不是历史副本，而是最小闭合状态

## 定义 10.1（预测记忆）

若接口 \(r:X\to M\) 满足：

1. 当前读数沿 \(r\) 因子化；
2. \(F\) 沿 \(r\) 下降；

则称 \(r\) 是一个精确预测记忆。

## 定理 10.1（最小记忆）

最小预测商

\[
\pi_\infty:X\to Z_q=X/K_\infty
\]

是所有精确预测记忆中的最粗者：对任意 \(r\)，存在唯一

\[
\theta:\operatorname{Im}(r)\to Z_q
\]

使

\[
\pi_\infty=\theta\circ r.
\]

### 证明

若 \(r(x)=r(y)\)，下降性给出 \(r(F^nx)=r(F^ny)\)；当前读数沿 \(r\) 因子化，故全部未来 \(q\)-读数相等，即 \(xK_\infty y\)。应用核判据。\(\square\)

## 推论 10.1（记忆下界）

对有限随机状态 \(X_0\)，任意精确预测记忆 \(M=r(X_0)\) 满足

\[
H(Z_q\mid q(X_0))
\le
H(M\mid q(X_0)).
\]

因此

\[
\boxed{
H(Z_q\mid q(X_0))
}
\]

是从当前读数升级到精确预测状态所需附加信息的规范下界。

## Lean 锚点 10.1

仓库已有有限预测完成、未来 congruence、最小可观测代数等定理。本文把它们统一解释为：

\[
\boxed{
\text{memory}
=
\text{the coarsest refinement that kills all future carry}.
}
\]

---

# 11. 信息分解：每一次精化支付多少新信息

令随机初态为 \(X_0\)，定义

\[
O_n:=q(F^nX_0),
\qquad
W_n:=(O_0,\ldots,O_n).
\]

## 定理 11.1（未来词信息链）

\[
\boxed{
H(W_n)
=H(O_0)
+
\sum_{j=1}^{n}
H(O_j\mid O_0,\ldots,O_{j-1}).
}
\]

### 证明

Shannon chain rule。\(\square\)

## 定义 11.1（第 \(j\) 层 carry 信息）

\[
\Delta_j
:=
H(O_j\mid O_0,\ldots,O_{j-1}).
\]

它不是“系统生成的新熵”的普遍物理断言，而是当前有限读数历史尚不能决定第 \(j\) 步读数时，需要补充的预测信息。

## 定理 11.2（稳定与零条件熵）

若

\[
K_n=K_{n+1},
\]

则对任意初态分布

\[
H(O_{n+1}\mid W_n)=0.
\]

反之，若初态分布在 \(X\) 上满支撑且该条件熵为零，则

\[
K_n=K_{n+1}.
\]

### 证明

稳定时 \(O_{n+1}\) 是 \(W_n\) 的确定函数。反向，有限满支撑下零条件熵意味着每个可达词值对应唯一下一输出，因此相同 \(W_n\) 的状态具有相同 \(O_{n+1}\)。\(\square\)

## Lean 锚点 11.1

仓库定理

`D5/S3/Entropy/Fusion/QuotientFiberDecomposition.quotient_fiber_entropy_decomposition`

机器证明有限 law 的 quotient–fiber 熵分解。本文的动态链把该静态余量沿未来词塔逐层展开。

---

# 12. 有限确定性闭环：幂零暂态与周期预测核

令有限状态更新为

\[
\tau:Y\to Y.
\]

在线性化空间 \(\mathbb C^{(Y)}\) 上定义 transfer operator

\[
T_\tau e_y=e_{\tau(y)}.
\]

## Lean 锚点 12.1

仓库定理

`D5/S3/ObserverMemory/FunctionalGraphs/FiniteFunctionalGraphFittingDecomposition.finite_functional_graph_fitting_decomposition`

已经机器证明：在稳定指数 \(N\) 处，

\[
\mathbb C^{(Y)}
=
\ker T_\tau^N
\oplus
\operatorname{ran}T_\tau^N,
\]

其中

\[
T_\tau|_{\ker T_\tau^N}
\]

幂零，而

\[
T_\tau|_{\operatorname{ran}T_\tau^N}
\]

双射，并在周期点基上表现为置换。

## 推论 12.1（预测完成后的双阶段动力学）

把上述定理应用于最小预测商 \(Z_q\) 上的下降动力学 \(\overline F\)，得到：

\[
\boxed{
\text{minimal predictive dynamics}
=
\text{nilpotent transient distinctions}
\oplus
\text{reversible periodic core}.
}
\]

被幂零部分消灭的不是完整世界状态，而是**在最小预测表示中的暂态坐标**。周期核保存长期可循环的预测差异。

## 原理 12.1（有限性不等于立即退化）

有限系统最终进入周期核，但：

- 周期可能极长；
- 暂态可能极长；
- 周期语义质量可高可低；
- “最终周期”不推出“短期重复”或“低复杂度”。

形式理论只给动力学形态，不替代质量函数。

---

# 13. 约化不可逆性：kernel、访问权与全局可逆性

## Lean 锚点 13.1

仓库定理

`D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect.reduced_irreversibility_is_access_defect`

构造了一个显式 unitary record coupling，满足：

1. 两个输入具有相同对角读数、不同相干项；
2. 写入环境记录后的两个联合状态不同；
3. 对环境取 partial trace 后，两个约化系统状态相同；
4. 不存在只依赖约化状态的恢复函数同时恢复两个联合记录；
5. 对联合系统施加逆 unitary 可精确恢复两个输入。

## 定理 13.1（访问 kernel 解释）

上述不可恢复性完全由 partial trace 接口的非单射性给出：

\[
\rho_{SE}\neq\sigma_{SE},
\qquad
\operatorname{Tr}_E\rho_{SE}
=
\operatorname{Tr}_E\sigma_{SE}.
\]

因此任意只通过 \(\operatorname{Tr}_E\) 的恢复器都必须在这两个输入上给出同一输出。

### 证明

这是定理 1.1 的直接应用：联合状态目标不沿约化接口因子化。\(\square\)

## 边界 13.1

该结论证明“约化不可逆性可以纯粹是访问缺陷”，不证明所有宏观热力学不可逆性、所有开放系统耗散或所有实际测量不可逆性都能被同一有限模型消解。

---

# 14. 因果层级：查询商而不是“更多数据”

令 \(\mathcal M\) 为模型类。给定查询族

\[
\mathcal Q=(Q_i:\mathcal M\to Y_i)_{i\in I},
\]

定义查询画像

\[
E_\mathcal Q(M):=(Q_i(M))_{i\in I}.
\]

## 定义 14.1（查询 kernel）

\[
K_\mathcal Q
:=
\{(M,N):E_\mathcal Q(M)=E_\mathcal Q(N)\}.
\]

## 定理 14.1（识别即 kernel 包含）

目标 \(T:\mathcal M\to Z\) 由查询族 \(\mathcal Q\) 识别，当且仅当

\[
\boxed{
K_\mathcal Q\subseteq K_T.
}
\]

等价地，\(T\) 唯一因子化通过查询商

\[
\mathcal M/K_\mathcal Q.
\]

### 证明

定理 1.1，取状态空间为模型类。\(\square\)

## 定义 14.2（目标因果 residual）

\[
\operatorname{CRes}(\mathcal Q,T)
:=
\{(M,N):E_\mathcal Q(M)=E_\mathcal Q(N),\ T(M)\neq T(N)\}.
\]

于是

\[
T\text{ 可识别}
\iff
\operatorname{CRes}(\mathcal Q,T)=\varnothing.
\]

## 定理 14.2（观察—干预—反事实 kernel 链）

若干预查询族包含空干预的观察 law，反事实查询族包含所有单世界干预边缘，则

\[
\boxed{
K_{\mathrm{cf}}
\subseteq
K_{\mathrm{int}}
\subseteq
K_{\mathrm{obs}}.
}
\]

两个包含都可以严格。

### 证明

加入查询只会增加相等条件，因此 kernel 只能缩小。严格性由标准方向反转反模型与相同单世界边缘、不同 cross-world coupling 的反模型给出。\(\square\)

## 原理 14.1

\[
\boxed{
\text{association}
\neq
\text{intervention}
\neq
\text{counterfactual coupling}.
}
\]

它们可以使用同一种概率记号，但对应不同查询族与不同 kernel。

---

# 15. 有限干预设计就是目标 pair 的 set cover

假设模型类 \(\mathcal M\) 与候选实验集 \(\mathcal E\) 有限。当前证据接口为 \(E_0\)，目标为 \(T\)。

## 定义 15.1（未解决目标 pair）

\[
\mathcal P_T
:=
\{\{M,N\}:E_0(M)=E_0(N),\ T(M)\neq T(N)\}.
\]

每个实验 \(e\in\mathcal E\) 覆盖的 pair 集为

\[
S_e
:=
\{\{M,N\}\in\mathcal P_T:Q_e(M)\neq Q_e(N)\}.
\]

## 定理 15.1（有限实验 cover 判据）

实验子集 \(A\subseteq\mathcal E\) 足以识别 \(T\)，当且仅当

\[
\boxed{
\mathcal P_T
=
\bigcup_{e\in A}S_e.
}
\]

因此最小非自适应实验设计正是集合覆盖问题。

### 证明

加入 \(A\) 后仍未被任何实验分开的 pair，恰是新 evidence kernel 中仍违反 \(K_E\subseteq K_T\) 的 pair。\(\square\)

## 推论 15.1（实验价值是 kernel 缩减，不是数据量）

一个产生大量样本但不切开任何目标 residual pair 的实验，对目标识别价值为零；一个只产生一比特、却切开最后一个 residual pair 的实验具有决定性价值。

---

# 16. kernel、image、coupling、gauge 与 carry 必须分账

## 定义 16.1（五类余量）

对模型／状态到证据的接口，区分：

### 16.1.1 Kernel residual

\[
x\neq y,
\qquad
q(x)=q(y).
\]

它记录接口合并了哪些对象。

### 16.1.2 Carry residual

\[
q(x)=q(y),
\qquad
q(Fx)\neq q(Fy).
\]

它记录当前 kernel 不是动力学 congruence。

### 16.1.3 Image defect

给定形式证据值 \(b\)，问

\[
b\in\operatorname{Im}(q)?
\]

兼容坐标族不一定由真实对象实现。

### 16.1.4 Coupling residual

边缘族 \((\mu_i)\) 已知，但 joint coupling

\[
\Gamma((\mu_i)_i)
\]

不唯一。

### 16.1.5 Gauge residual

不同参数化、坐标或外生变量表示给出相同全部目标查询。它应取商，而不应被误报为经验不确定性。

## 原理 16.1（修复必须对症）

- kernel 太大：增加分离性查询；
- carry 非空：增加记忆、限制动力学或压缩目标；
- image 失败：修正模型类／实现约束；
- coupling 非唯一：加入 cross-world 结构、界或部分识别；
- gauge 非唯一：规范化或取商。

更多样本只改善固定接口上的估计误差，不自动修复上述任一结构缺陷。

---

# 17. Prime-indexed 接口：局部观察、乘积与 gluing

令每个素数 \(p\) 给出局部接口

\[
q_p:X\to B_p.
\]

对有限素数集 \(S\)，定义

\[
q_S=(q_p)_{p\in S},
\qquad
K_S=\bigcap_{p\in S}K_{q_p}.
\]

若 \(S\subseteq T\)，则

\[
K_T\subseteq K_S.
\]

## 定义 17.1（全素数核）

\[
K_{\mathbb P}
:=
\bigcap_pK_{q_p}.
\]

## 定理 17.1（有限局部塔的最小全局商）

全局 prime profile 商

\[
X/K_{\mathbb P}
\]

是所有有限局部接口的共同精化极限：任意能恢复每个 \(q_p\) 的接口都因子化到该商。

### 证明

核为全部局部核的交，应用定理 1.1。\(\square\)

## 警告 17.1（局部一致不等于全局实现）

有限投影族中的每组坐标都可实现，不推出整个无限兼容族位于全局 image。该缺陷属于 image／gluing，而不是 kernel。纯粹继续增加素数读数可能缩小 kernel，却不自动证明逆极限坐标来自一个真实全局对象。

## 原理 17.1（prime-time carry）

若动力学更新在每个有限 \(S\) 上可下降，但不存在与所有投影兼容的全局下降，则障碍位于下降映射族的 gluing，而不是任一局部 carry。需要分别审计：

\[
\text{local descent},
\qquad
\text{transition compatibility},
\qquad
\text{global realization}.
\]

---

# 18. 无限维与超限完成：强完成不等于一致完成

令 \((V_\alpha)\) 为递增闭子空间塔，\(P_\alpha\) 为正交投影，

\[
R_\alpha:=V_\alpha^\perp.
\]

## 定理 18.1（极限残余）

在极限阶段 \(\lambda\)，若

\[
V_\lambda
=
\overline{\bigcup_{\alpha<\lambda}V_\alpha},
\]

则

\[
\boxed{
R_\lambda
=
\bigcap_{\alpha<\lambda}R_\alpha.
}
\]

### 证明

正交补把闭线性生成的上确界变成交。\(\square\)

## Lean 锚点 18.1

仓库定理

`D5/S3/Quantum/Completion/TransfiniteBasisResidualTower.transfinite_basis_residual_tower`

已经机器证明初始良序 Hilbert 基的后继分裂、极限交、每个真初始段的同基数尾部，以及终端残余为零。

## 定理 18.2（强完成）

若

\[
\overline{\bigcup_\alpha V_\alpha}=H,
\]

则对每个固定 \(x\in H\)，

\[
P_\alpha x\to x.
\]

等价地，

\[
\|(I-P_\alpha)x\|\to0.
\]

## 定理 18.3（一致完成障碍）

若每个阶段 \(V_\alpha\neq H\)，则

\[
\boxed{
\|I-P_\alpha\|=1
}
\]

对所有 \(\alpha\) 成立。因此 \(P_\alpha\) 不可能在算子范数中收敛到 \(I\)。

### 证明

真闭子空间的非零正交补中取单位向量 \(r\)，则

\[
(I-P_\alpha)r=r,
\]

给出范数下界 1；正交投影余算子的范数至多 1。\(\square\)

## Lean 锚点 18.2

仓库定理

`D5/S3/Quantum/Completion/InfiniteDimensionalProjectionSeparation.infinite_dimensional_projection_separation`

已经机器证明上述“逐向量完成但算子范数恒距 1”的分离。

## 原理 18.1（维数不是完成进度）

无限维中可能出现

\[
\dim R_\alpha=\dim H
\]

对每个真阶段成立，而终端

\[
R_{\mathrm{terminal}}=0.
\]

因此必须使用：

- 固定目标向量的残余能量；
- 强／弱／范数拓扑；
- target-specific factorization；
- gluing 与 image 条件；

而不能仅凭残余维数判断观察者“还差多少”。

---

# 19. 当前 negative-base-\(\varphi\) 前沿的重新定位

仓库当前已经闭合以下结构：

1. admissible negative prefix 的 core 无限；
2. 可由严格枚举得到真实 core frontier；
3. 连续枚举值构成相邻 core pair；
4. 给定左端点，相邻右端点唯一；
5. phase-enriched trace 与 exact gap phase 等价。

对应 Lean 锚点包括：

- `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentCore.core_infinite_proved`；
- `D5/X_Frontier/BasePhiNegativePrefixTrident.frontier_step_semantics_proved`；
- `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.frontier_consecutive_core_adjacent`；
- `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.adjacent_core_point_right_unique`；
- `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.phase_enriched_core_trace_iff_gap_phase`。

## 定义 19.1（gap 目标）

对 frontier certificate \(c\)，定义

\[
g(n):=c(n+1)-c(n).
\]

定义相位接口

\[
s(n)
:=
\bigl(
\operatorname{phase}(c),
\operatorname{familyLetter}(c,n)
\bigr).
\]

## 条件命题 19.1（剩余核心的因子化形式）

当前两个剩余 provider 的共同核心可写成：存在二值函数

\[
\gamma(s)
=
\begin{cases}
a,&\text{selected letter}=1,\\
b,&\text{selected letter}=0,
\end{cases}
\]

使

\[
\boxed{
g=\gamma\circ s.}
\]

换言之，实际相邻 gap 必须沿“六态相位 + aperiodic Fibonacci 输入位”接口下降。

## 推理 19.1

此前困难可能被描述为：

- 是否存在下一 core 点；
- 下一点是否唯一；
- gap 是否属于 \(\{a,b\}\)；
- F/G/H itinerary 是否正确。

最新证明已经结算前两项。于是最后余量不再是“寻找相邻点”，而是：

\[
\boxed{
\text{证明唯一真实相邻边的长度，只依赖当前相位接口。}
}
\]

这正是定理 1.1／2.1 的目标因子化问题。`PhaseEnrichedCoreTrace` 不是附加装饰，而是该因子化的显式 witness 类型。

## 最小下一步 19.1

要闭合该前沿，最直接的证明目标不是继续证明唯一性，而是构造对每个 \(n\) 的实际相邻边 witness，并证明其 additive 字段：

\[
(c(n+1):\mathbb Z)
=
c(n)+
\begin{cases}
a,&\ell_n=1,\\b,&\ell_n=0.
\end{cases}
\]

一旦该式成立：

\[
\text{PhaseEnrichedCoreTrace}
\Longrightarrow
\text{source-index delta}
\Longrightarrow
\text{six-phase gap stream}
\Longrightarrow
\text{F/G/H sequence reconstruction}.
\]

因此当前主线已经从十五节点链压缩为一个**相位接口下降桥**。

## 边界 19.1

主定理 `negative_prefix_trident_classification` 仍有前沿占位；本文不把上述重新定位冒充最终证明。

---

# 20. 自描述边界：预测完成不推出对角完成

## 定理 20.1（固定状态域上的完全接口）

若 \(q:X\to B\) 单射，则对任意普通目标 \(T:X\to Y\)，\(T\) 沿 \(q\) 因子化。

### 证明

\(K_q\) 为对角关系，故 \(K_q\subseteq K_T\)。\(\square\)

## 原理 20.1（对角逃逸需要类型扩张）

若 \(q\) 已在固定 \(X\) 上单射，却仍声称存在“不可表达对象”，那么缺陷不再位于状态区分，而位于：

- 表示清单 \(g:B\to X\) 非满射；
- 目标语言／对象类型被扩张；
- 自应用产生了原类型之外的新对象；
- realizability 或 admission 拒绝某些形式坐标。

因此必须分开：

\[
\boxed{
\text{state faithfulness}
\neq
\text{representation surjectivity}
\neq
\text{dynamic closure}
\neq
\text{self-description closure}.
}
\]

## Lean 锚点 20.1

仓库定理

`D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness.nonfaithful_interface_future_incomplete`

已经机器证明非单射接口必遗漏一个显式 Boolean collision obligation。本文补充：当接口已单射时，再谈 diagonal escape 必须明确发生了类型或表示宇宙扩张。

---

# 21. 统一表示定理

## 定理 21.1（有限确定性动力接口六重等价）

设 \(X\) 有限，\(q:X\to B\)，\(F:X\to X\)。以下等价：

1. 存在唯一有效下降 \(\overline F:B_q\to B_q\)；
2. \(K_q\) 是 \(F\)-congruence；
3. \(\operatorname{Carry}(q,F)=\varnothing\)；
4. \(q\circ F\) 沿 \(q\) 因子化；
5. \(F^*\mathcal A_q\subseteq\mathcal A_q\)；
6. \(K_0=K_1\)。

### 证明

(1)–(4) 为定理 2.1；(1) 与 (5) 为定理 4.1；(2) 与 (6) 由

\[
K_1=K_q\cap(F\times F)^{-1}K_q
\]

立即等价。\(\square\)

## 推论 21.1（线性实例）

若 \(q=P\) 为有限维 Hilbert 空间上的正交投影，\(F=T\) 为线性算子，则上述等价条件进一步等价于

\[
PTQ=0.
\]

若 \(T=T^*\)，则又等价于

\[
[P,T]=0.
\]

## 推论 21.2（随机实例）

把确定性 \(F\) 替换为 Markov kernel \(K\)，则对应零缺陷条件为

\[
\delta_q(K)=0,
\]

即强 lumpability。

## 统一原理 21.1

\[
\boxed{
\begin{array}{c|c}
\text{表示语言}&\text{同一结构障碍}\\
\hline
\text{集合商}&K_q\text{ 不被 }F\text{ 保持}\\
\text{确定性动力学}&\operatorname{Carry}(q,F)\neq\varnothing\\
\text{函数代数}&F^*\mathcal A_q\not\subseteq\mathcal A_q\\
\text{线性分解}&PTQ\neq0\\
\text{双向 reducing}&[P,T]\neq0\\
\text{随机过程}&\delta_q(K)>0\\
\text{因果查询}&K_\mathcal Q\not\subseteq K_T
\end{array}
}
\]

这些不是把不同学科强行改名，而是同一个因子化／自然性问题在不同范畴中的具体实现。

---

# 22. 新的研究推论

## 推论 22.1（观察者时间是 kernel 精化时间）

物理时间参数 \(n\) 与观察者完成深度 \(m\) 不同。\(n\) 描述系统运行多少步；\(m\) 描述需要看多长的未来词，才能让当前表示成为 Markov／闭合状态。

因此：

\[
\boxed{
\text{clock time}
\neq
\text{predictive refinement depth}.
}
\]

同一个系统可以运行很久而 \(m_*=0\)，也可以一步更新却需要很深的隐藏预测状态。

## 推论 22.2（交换子范数是双向接口活动，不是单一预测误差）

\[
\|[P,T]\|_{HS}^2
=
\|PTQ\|_{HS}^2+
\|QTP\|_{HS}^2.
\]

其中只有 \(PTQ\) 直接阻止一步可见下降；\(QTP\) 测量可见坐标向余量的泄漏。故单用交换子范数会把“隐藏影响可见”与“可见生成隐藏”合并。需要方向性审计时，应分别报告两个块。

## 推论 22.3（退相干强度与预测不闭合不是同一标量）

未读测量删除多少 Hilbert–Schmidt 相干余量，衡量的是静态投影损失；后续生成元是否把余量重新送回可见块，衡量的是 \(\mathcal D\mathcal L(I-\mathcal D)\)。前者大而后者可为零；前者小而后者可非零。

## 推论 22.4（因果实验价值是定向 kernel transversal）

一个实验的价值不是其 mutual information 的无条件大小，而是它是否横切当前目标 residual。若实验只区分 \(T\) 相同的模型，它可有高信息量而对目标识别无价值。

## 推论 22.5（局部闭合与全局闭合之间还有 gluing 层）

每个有限 prime 窗口、每个有限时间窗或每个局部图表都可下降，不推出存在一个兼容全局下降。局部定理闭合后仍需检查 transition maps、逆极限 image 与 cocycle obstruction。

## 推论 22.6（完成进度应以目标残余而非载体大小计量）

无限维残余可在每个真阶段保持与整体同维。合理的进度量是

\[
\|P_{R_\alpha}x\|,
\qquad
\sup_{x\in\mathcal T}\|P_{R_\alpha}x\|,
\qquad
K_{q_\alpha}\cap K_T,
\]

即固定目标／测试族上的残余，而不是裸维数。

---

# 23. 有限反模型册

## 23.1 当前读数相同、下一读数不同

反例 9.1 展示最小 carry。它同时证明：

- 当前接口非 Markov；
- 当前观察代数不 invariant；
- 一步未来词严格精化；
- 常值后处理可以掩盖缺陷。

## 23.2 单世界边缘相同、cross-world joint 不同

取二元 potential outcomes \((Y^0,Y^1)\)，固定两者边缘均为 Bernoulli\((1/2)\)。可选择：

\[
Y^0=Y^1
\]

或

\[
Y^0=1-Y^1.
\]

全部单世界边缘相同，但

\[
\Pr(Y^1>Y^0)
\]

不同。该缺陷是 coupling residual，不是更多单世界样本能修复的估计误差。

## 23.3 强收敛但不一致收敛

取 \(H=\ell^2(\mathbb N)\)，\(V_n\) 为前 \(n\) 个标准基向量张成空间。则

\[
P_nx\to x
\]

对每个 \(x\) 成立，但

\[
\|I-P_n\|=1
\]

恒成立。

## 23.4 约化状态相同、联合记录不同

仓库 `ReducedRecordAccessDefect` 给出机器验证实例。它同时反驳：

\[
\text{same reduced state}
\Longrightarrow
\text{same global record}.
\]

## 23.5 决策充分但完整预测不充分

仓库

`D5/S3/ConceptDynamics/DecisionValue/DecisionWithoutFullPrediction.decision_sufficiency_without_full_prediction`

给出常值概念决定最优动作、却不能决定完整 payoff profile 的机器验证反模型。

---

# 24. 与当前仓库 Lean 真值的对应表

以下条目是本文依赖的主要机器真值锚点；本文不修改它们：

| 结构 | Lean 锚点 | 本文中的角色 |
|---|---|---|
| 精确下降排除 carry | `D5/S3/ConceptDynamics/Dialectics/ExactDescentNoCarry.exact_descent_has_no_carry` | 定理 2.1 的已闭合方向 |
| 最小不变观察代数 | `D5/S3/Quantum/Dynamics/LeastInvariantObservableAlgebra.least_invariant_observable_algebra` | 第 4 节有限实例 |
| 未读测量正交投影 | `D5/S3/Observer/Conditioning/UnreadStateOrthogonalProjection.unread_state_orthogonal_projection` | 第 6 节 |
| 投影概率交换子流 | `D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.projection_probability_flow` | 第 7 节 |
| quotient–fiber 熵分解 | `D5/S3/Entropy/Fusion/QuotientFiberDecomposition.quotient_fiber_entropy_decomposition` | 第 11 节 |
| 有限 Fitting 分解 | `D5/S3/ObserverMemory/FunctionalGraphs/FiniteFunctionalGraphFittingDecomposition.finite_functional_graph_fitting_decomposition` | 第 12 节 |
| 约化访问缺陷 | `D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect.reduced_irreversibility_is_access_defect` | 第 13 节 |
| 无限维强／一致分离 | `D5/S3/Quantum/Completion/InfiniteDimensionalProjectionSeparation.infinite_dimensional_projection_separation` | 第 18 节 |
| 超限基残余塔 | `D5/S3/Quantum/Completion/TransfiniteBasisResidualTower.transfinite_basis_residual_tower` | 第 18 节 |
| 多目标最小充分性 | `D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency.multi_target_minimal_sufficiency` | 第 1、15 节 |
| 非忠实接口遗漏未来义务 | `D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness.nonfaithful_interface_future_incomplete` | 第 20 节 |
| 相邻 core 边唯一 | `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.frontier_consecutive_core_adjacent` | 第 19 节 |
| 相位 trace 与 gap phase 等价 | `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.phase_enriched_core_trace_iff_gap_phase` | 第 19 节 |

---

# 25. 建议的 Lean 形式化顺序

本文只给路线，不在本 PR 中添加 Lean 文件。

## 25.1 第一阶段：纯集合核

```text
D5/S3/Observer/Interfaces/
  EffectiveImageDescent.lean
  CarryEquivalence.lean
  FutureWordKernel.lean
  MinimalPredictiveCongruence.lean
```

优先闭合：

1. 有效像下降的双向等价；
2. \(K_{n+1}=K_q\cap F^{-1}K_n\)；
3. 稳定即前向不变；
4. \(K_\infty\) 最大不变子关系；
5. 有限稳定类数界。

## 25.2 第二阶段：函数代数对偶

```text
D5/S3/Observer/ObservableAlgebras/
  KernelFunctionAlgebra.lean
  PullbackDescentEquivalence.lean
  FutureWordAlgebraClosure.lean
```

目标是把 partition refinement 与现有 least invariant observable algebra 接成同一 theorem family。

## 25.3 第三阶段：线性方向性缺陷

```text
D5/S3/Observer/Residuals/
  ProjectionDescentBlocks.lean
  ProjectionCommutatorBlocks.lean
  HilbertSchmidtCarryIdentity.lean
```

必须分别命名 \(PTQ\) 与 \(QTP\)，避免只报一个无方向交换子范数。

## 25.4 第四阶段：随机 lumpability

```text
D5/S3/Observer/Stochastic/
  StrongLumpabilityDescent.lean
  TotalVariationCarry.lean
  ApproximateDescentBounds.lean
```

有限 PMF 版本足以先闭合 \(\delta/2\) 下界与代表元上界。

## 25.5 第五阶段：因果查询商

```text
D5/S3/Observer/Causal/Queries/
  QueryKernel.lean
  TargetIdentifiability.lean
  FiniteInterventionCover.lean
  CounterfactualCouplingResidual.lean
```

先做纯有限函数与显式反模型，不必一开始引入完整 DAG／do-calculus。

## 25.6 第六阶段：三叉戟最后桥

不再增加平行 provider 名称；直接围绕

```text
PhaseEnrichedCoreTrace
```

构造每一步实际相邻边的 additive witness。成功后沿已有链自动推出 delta、gap stream 与 sequence reconstruction。

---

# 26. 最终结论

## 结论 26.1

观察者不是一个附加于世界的实体，而是一张接口：

\[
q:X\to B.
\]

接口的静态余量由 \(K_q\) 给出；接口的动态失败由 \(K_q\) 是否被 \(F\) 保持给出。

## 结论 26.2

\[
\boxed{
\text{carry}
=
\text{current equivalence ceases to be valid after update}.
}
\]

## 结论 26.3

在线性空间中：

\[
\boxed{
\text{one-step carry}=PTQ,
\qquad
\text{outward leakage}=QTP,
\qquad
\text{two-way defect}=[P,T].
}
\]

## 结论 26.4

在量子连续时间中：

\[
\boxed{
[H,P]
}
\]

是事件接口的无穷小动力学缺陷，其状态期望给出概率通量；但单个状态上的零通量不等于结构交换。

## 结论 26.5

记忆的本质不是保存任意过去，而是构造最小精化

\[
X/K_\infty
\]

使未来更新在观察者状态上闭合。

## 结论 26.6

因果知识也不是单一分布，而是查询族诱导的商。观察、干预、反事实分别收缩不同 kernel；未识别目标就是该 kernel 中仍存在目标差异。

## 结论 26.7

无限完成必须带拓扑：

\[
P_\alpha x\to x
\]

不推出

\[
\|P_\alpha-I\|\to0.
\]

每个真阶段残余与整体同维，也不妨碍终端残余为零。

## 结论 26.8

当前 negative-base-\(\varphi\) 前沿已经不再缺“相邻边是否存在、是否唯一”；最后核心是证明真实 gap 沿 phase-enriched interface 因子化。换言之，剩余难点已经精确 collapse 为：

\[
\boxed{
\text{one finite-state interface must carry the exact aperiodic gap law}.
}
\]

## 最终统一式

\[
\boxed{
\begin{aligned}
\text{state distinction}
&\xrightarrow{q}
\text{observable quotient},\\
\text{future incompatibility}
&\xrightarrow{\operatorname{Carry}}
\text{predictive refinement},\\
\text{linearized incompatibility}
&\xrightarrow{PTQ,QTP}
\text{commutator defect},\\
\text{random incompatibility}
&\xrightarrow{\delta_{TV}}
\text{lumpability defect},\\
\text{causal incompatibility}
&\xrightarrow{K_\mathcal Q\not\subseteq K_T}
\text{identification residual},\\
\text{completion}
&=
\text{the least refinement on which the dynamics descends}.
\end{aligned}
}
\]

这条链给出一个统一但不混同层级的答案：所谓观察者缺失的信息，不是一个无类型的“隐藏量”；它是目标、动力学与接口共同决定的余量。只有把 kernel、carry、image、coupling、gauge 与 completion topology 分账，才能精确知道下一步究竟应增加读数、增加记忆、改变实验、约束动力学、补 gluing，还是承认目标在当前接口上根本不可识别。

---

# 2026-09-06 增补：离散平衡截断的实际系统与能量误差界

本节承接有限时间残差界，将合法约化系统接到离散时间平衡截断的尾和估计。对应源码为 `BalancedSteinEnergy`、`BalancedTruncationStep`、`BalancedTruncationTail`，均位于 `D5/S3/Observer/Hankel/`，并配套同名 Scribe。这里给出完整的候选证明源码；本轮尚未执行 Lean 内核与 Scribe 发射检查。

## A. 两个标准 Stein 不等式

取实矩阵系统
\[
x_{k+1}=Ax_k+Bu_k,\qquad y_k=Cx_k,\qquad x_0=0.
\]
令 \(D=\operatorname{diag}(w_0,\ldots,w_{n-1})\)，其中每个 \(w_i>0\)。假设
\[
A^TDA+C^TC\preceq D,\qquad ADA^T+BB^T\preceq D.
\]
`BalancedStein` 用对所有实向量成立的二次型不等式直接表达这两个条件。其定义不包含逆储能界、约化误差界或误差可求和性。

记 \(E_D(x)=\sum_i w_i x_i^2\)。对 \(t=Ax+Bu\) 取 \(z=D^{-1}t\)，加权 Young 不等式与转置配对给出
\[
2E_{D^{-1}}(t)
\le E_D(A^Tz)+\lVert B^Tz\rVert_2^2+E_{D^{-1}}(x)+\lVert u\rVert_2^2
\le E_{D^{-1}}(t)+E_{D^{-1}}(x)+\lVert u\rVert_2^2.
\]
因此 `inverse_energy_step` 推出
\[
E_{D^{-1}}(Ax+Bu)\le E_{D^{-1}}(x)+\lVert u\rVert_2^2.
\]
坐标平方和与默认 Pi 空间的上确界范数严格区分；有限时间输出范数通过 Mathlib 的 `EuclideanSpace` 连接到这些平方和。

## B. 实际截断、继承性与交叉项消去

保留前 \(n-1\) 个坐标，构造投影 \(P\) 和零填充 \(J\)。源码直接构造
\[
A_r=A_{11}=PAJ,\qquad B_r=B_1=PB,\qquad C_r=C_1=CJ.
\]
`truncated_model_is_projected` 将这三个矩阵与已有 `ProjectedRealizationError` 的构造逐一等同；轨道复用原有 `drivenState`。

`truncate_preserves_stein` 在零填充向量上应用完整系统不等式，删除非负的遗漏坐标项，证明两个 Stein 不等式对截断系统继续成立。离散时间截断一般不保持原 Gramian 等式，本节没有使用这种错误的继承前提。

单次删除权重 \(\sigma=w_{n-1}\)。令 \(z_k\) 为实际约化状态，并定义
\[
e_k=x_k-Jz_k,\quad s_k=x_k+Jz_k,\quad
v_k=(AJz_k+Bu_k)_{n-1},\quad
V_k=E_D(e_k)+\sigma^2E_{D^{-1}}(s_k).
\]
两个实际递推给出的遗漏坐标交叉项精确抵消。`single_step_dissipation` 证明
\[
V_{k+1}+\lVert y_k-y_{r,k}\rVert_2^2+2\sigma |v_k|^2
\le V_k+4\sigma^2\lVert u_k\rVert_2^2.
\]
在 \(0\le k<N\) 上累加，且 \(V_0=0\)，得到保留终端储能的有限时间界
\[
V_N+\sum_{k<N}\lVert y_k-y_{r,k}\rVert_2^2
+2\sigma\sum_{k<N}|v_k|^2
\le4\sigma^2\sum_{k<N}\lVert u_k\rVert_2^2.
\]
上述两个不等式从具体矩阵与具体轨道推导；不要求 \(\lVert A\rVert<1\) 或 \(\lVert A_r\rVert<1\)。

## C. 任意保留维数与整个半轴

`prefixA`、`prefixB`、`prefixC` 直接截取前 \(r\) 个状态坐标。利用已证明的 Stein 继承性逐坐标删除，再用有限窗口欧氏范数的三角不等式，`balanced_truncation_window_bound` 证明
\[
\boxed{\lVert y-y_r\rVert_{2,[0,N)}
\le2\left(\sum_{i=r}^{n-1}w_i\right)\lVert u\rVert_{2,[0,N)}}
\qquad(0\le r\le n,\ N\in\mathbb N).
\]
逐次删除得到的系统在源码中与直接前缀截断的系统一致。结论同时涵盖零维约化、完整保留和重复权重；尾和不等式本身不要求权重排序。

若输入具有有限总能量，`balanced_truncation_l2_bound` 首先证明误差平方和可求和，再证明
\[
\boxed{\sum_{k=0}^{\infty}\lVert y_k-y_{r,k}\rVert_2^2
\le\left(2\sum_{i=r}^{n-1}w_i\right)^2
\sum_{k=0}^{\infty}\lVert u_k\rVert_2^2.}
\]
该极限步骤通过统一的非负部分和界与 Mathlib 的实级数定理完成，没有假设误差已属于 \(\ell_2\)。

## D. 与原有结论及后续完整平衡实现的关系

这是既有合法约化构造的一条专门误差路线。原残差定理处理任意投影和一般有限时间输入；本节增加共同正对角 Stein 条件，得到不依赖严格范数收缩的全时间能量保证。

另需沿用 `ProjectedExactDescent` 对本卷第 5.3 节的勘正：固定全局算子满足精确下降 \(PA=A_rP\) 时，\(PA^k=A_r^kP\) 对全部 \(k\) 成立。此时隐藏方向的非零泄漏本身不会造成后续可见预测失败。

本节从已给出的正对角 Stein 数据出发。一般稳定最小实现的平衡坐标构造、该对角与真正 Hankel 奇异值的识别、截断后的严格内部稳定性以及时间域诱导范数与频域 \(H^\infty\) 范数的等同，仍是独立的后续证明义务。对任意共同 Stein 上界，不能直接将其对角权重称为精确 Hankel 奇异值。有限噪声 Ho–Kalman 输出满足这些平衡前提，也需要单独建立。

本节形式化的是经典平衡截断误差机制，不声称提出新的数值误差常数。可对照 Sandberg 与 Rantzer 的 *Balanced Truncation of Linear Time-Varying Systems*，IEEE TAC 49(2), 217–229 (2004), DOI `10.1109/TAC.2003.822862`。近期 Anand 与 Sandberg 的 *On Frequency-Weighted Extended Balanced Truncation*，arXiv:2512.02298v1 (2025)，第 2.1 节仍以 Lyapunov 不等式、平衡坐标和两倍尾和组织广义截断；其频率加权和 extended-LMI 算法不属于本节已经证明的范围。

---

# 2026-09-06 增补：实际 Gramian、平衡坐标与无限 Hankel 的完整 Schmidt 分解

本节消除上一增补中“已经给定正对角 Stein 数据”的前提。新增五个候选 Lean 模块为 `PositiveGramianBalancing`、`ExactGramianSeries`、`BalancedRealizationTransport`、`InfiniteHankelGramian` 与 `BalancedHankelSchmidt`，路径均为 `D5/S3/Observer/Hankel/`，各有同名 Scribe。以下证明已写成完整候选源码，尚未执行 Lean 内核与 Scribe 发射检查。

## A. 原系统上的明确假设

取实有限维系统
\[
x_{k+1}=Ax_k+Bu_k,\qquad y_k=Cx_k,\qquad x_0=0.
\]
本节使用三个直接作用于原矩阵的条件：
\[
\sum_{k\ge0}\lVert A^k\rVert_2^2<\infty,
\qquad
\bigcap_{k\ge0}\ker(CA^k)=\{0\},
\qquad
\bigcap_{k\ge0}\ker(B^T(A^T)^k)=\{0\}.
\]
最后一个条件采用对偶观察的明确表述；正文推导不调用尚未提供的跨定义可控性转换。

第一项是幂的平方可和性，不能在源码中无证明地改写为“所有特征值模小于一”。`power_square_summable_of_bound` 已证明：若有 \(\lVert A^k\rVert_2\le Mq^k\)，其中 \(0\le q<1\)，则该条件成立。它允许单步范数不小于一。谱半径条件与这一稳定性输入的正式转换仍可单独补充。

## B. 实际无穷级数产生正定 Gramian

直接构造
\[
Q=\sum_{k\ge0}(CA^k)^T(CA^k),
\qquad
P=\sum_{k\ge0}(A^kB)(A^kB)^T.
\]
范数估计
\[
\lVert (CA^k)^T(CA^k)\rVert_2
\le\lVert C\rVert_2^2\lVert A^k\rVert_2^2
\]
给出算子范数收敛；对偶系统给出 \(P\) 的收敛。把连续二次型作用于收敛级数，得到
\[
x^TQx=\sum_{k\ge0}\lVert CA^kx\rVert_2^2.
\]
非零 \(x\) 至少具有一次非零真实未来读数，因此 \(Q\) 正定；同理 \(P\) 正定。正定性没有被作为输入矩阵的附加公理。

拆分第零项并移动收敛级数，得到精确 Stein 等式
\[
A^TQA+C^TC=Q,\qquad APA^T+BB^T=P.
\]
进一步，令 \(Q_N=\sum_{k<N}(CA^k)^T(CA^k)\)，则
\[
\boxed{Q=Q_N+(A^N)^TQA^N.}
\]
`observationGramian_eq_existing` 证明矩阵系列通过 Euclidean 连续线性映射解释后，恰为已有 `DiscountedObservabilityGramianPositivity.discountedObservabilityGramian` 在折扣参数一处的对象。该等同使新矩阵实现与原算子所有者相接。

## C. 从两个正定矩阵真实构造平衡坐标

设 \(L=P^{1/2}\)，通过 Mathlib 的正连续函数演算构造。由 \(L^2=P\) 与 \(\det P>0\) 得 \(L\) 可逆，并证明其正定性。再对正定 Hermitian 矩阵
\[
K=LQL
\]
使用正交谱分解：
\[
K=U\operatorname{diag}(\lambda_i)U^T,
\qquad \lambda_i>0.
\]
令
\[
\sigma_i=\sqrt{\lambda_i},\quad D=\operatorname{diag}(\sigma_i),\quad
T=LUD^{-1/2},\quad S=D^{1/2}U^TL^{-1}.
\]
逐一证明
\[
ST=TS=I,\qquad SPS^T=D,\qquad T^TQT=D.
\]
`coordinates_nonempty` 从 \(P,Q\) 的正定性构造全部见证。`Coordinates` 是该构造的输出证书，主终点没有要求用户提供一个已经满足这些等式的变换。

定义实际平衡实现
\[
\bar A=SAT,\qquad \bar B=SB,\qquad \bar C=CT.
\]
精确矩阵等式给出共同对角的两个 Stein 等式，再给出上一增补所需的 `BalancedStein`。对实际强迫递推归纳，还证明
\[
x_k=T\bar x_k,\qquad y_k=\bar y_k
\]
对任意输入与全部时间成立。

乘积 \(PQ\) 一般不对称。源码通过相似变换而非错误的自伴假设处理它：
\[
S(PQ)T=D^2,
\qquad
\boxed{\chi_{PQ}(z)=\prod_i(z-\sigma_i^2).}
\]
重复特征值及其重数保留。该精确数学构造使用谱定理和选择，属于 `noncomputable` 构造，不等同于可执行浮点特征值算法。

## D. 真正的无限 Hankel 算子及其谱识别

令输入与输出信号分别属于 \(\ell_2(\mathbb N,\mathbb R^m)\) 与 \(\ell_2(\mathbb N,\mathbb R^p)\)。直接构造全部未来输出算子
\[
(\mathcal Ox)_i=CA^ix.
\]
前述真实能量级数证明其值确实属于 \(\ell_2\)。从有限维状态域的线性连续性得到有界算子。对偶系统的未来算子记为 \(\mathcal Z\)，再定义
\[
\mathcal R=\mathcal Z^*,\qquad \mathcal H=\mathcal O\mathcal R.
\]
证明
\[
\mathcal O^*\mathcal O=Q,\qquad \mathcal R\mathcal R^*=P.
\]
对年龄为 \(j\) 的单点输入 \(e_jv\)，证明
\[
\mathcal R(e_jv)=A^jBv,
\qquad
\boxed{(\mathcal H(e_jv))_i=CA^{i+j}Bv.}
\]
这里明确固定 \(i+j\) 的 Hankel 索引。Mathlib 的 \(\ell_2\) 单点求和定理与有界线性映射连续性，进一步给出任意完整 \(\ell_2\) 输入的求和语义。

令 \(E=D^{-1/2}\)，构造
\[
F=\mathcal OTE,\qquad G=\mathcal ZS^TE.
\]
由真实 Gramian 恒等式推导 \(F^*F=G^*G=I\)，因此这两个映射为等距嵌入。直接相乘得
\[
\boxed{\mathcal H=FDG^*.}
\]
定义 \(\ell_i=Fe_i\)、\(r_i=Ge_i\)。这两族是真实无限信号空间中的正交单位向量，并满足
\[
\mathcal Hr_i=\sigma_i\ell_i,\qquad
\mathcal H^*\ell_i=\sigma_i r_i.
\]
对每个 \(u\in\ell_2\)，证明完整分解
\[
\boxed{\mathcal Hu=\sum_i\sigma_i\langle r_i,u\rangle\ell_i.}
\]
另外证明
\[
\mathcal Hu=0\iff\forall i,\ \langle r_i,u\rangle=0.
\]
`nonzero_squared_singular_value` 还证明：若非零 \(u\) 满足 \(\mathcal H^*\mathcal Hu=\lambda u\) 且 \(\lambda\ne0\)，则存在 \(i\) 使 \(\lambda=\sigma_i^2\)。因此没有额外的非零奇异方向，重复权重则由对应的正交模态保留重数。

`constructed_hankel_schmidt` 将实际 Gramian、构造坐标、正交性、双向奇异向量方程、全部输入上的展开、核刻画和特征多项式连成一个原系统终点。现有有限维 `hankel_gramian_singular_values` 同时被 `constructed_core_singular_values` 用实际平方根实例化。有限核心与上述无限算子的证明分别保留，没有将有限窗口的奇异值直接认作全局谱。

## E. 原系统直接获得真实奇异权重的降阶界

`constructed_reduction_window_bound` 与 `constructed_reduction_l2_bound` 使用原矩阵及 A 节条件，构造 \(P,Q,T,S\)，证明平衡前提，再复用上一增补的实际前缀截断。

对构造的约化输出 \(y_r\)，得到
\[
\lVert y-y_r\rVert_{2,[0,N)}
\le2\left(\sum_{i\text{ 被删除}}\sigma_i\right)\lVert u\rVert_{2,[0,N)},
\]
以及有限能量输入上的
\[
\sum_{k\ge0}\lVert y_k-y_{r,k}\rVert_2^2
\le\left(2\sum_{i\text{ 被删除}}\sigma_i\right)^2
\sum_{k\ge0}\lVert u_k\rVert_2^2.
\]
误差的可求和性也被推出。本节已将权重识别为原系统真实无限 Hankel 的完整正奇异值族；当前输出枚举没有声明递减排序，因此“保留前 r 个”依照构造返回的顺序，不能直接宣传成自动保留最大的 r 个。加入有序重排后才可采用惯常的排序尾和记法。

## F. 验证状态与剩余数学接口

本轮实际执行了独立 Python/Sympy 精确有理数回归与 NumPy/SciPy 数值回归。有限截断的正交性和奇异值检验属于近似检验；精确有理数检查的对象包括 Stein 等式、坐标逆关系、特征多项式、有限余项与 Hankel 核分解。这些检验不代替 Lean 内核验证。

本节尚未证明或执行：从单纯谱半径判据产生幂平方可和证书、有序重排的规范接口、约化系统的严格内部稳定性、时间域诱导范数与频域 \(H^\infty\) 范数的等同，以及对带噪 Ho–Kalman 估计族统一认证这些输入条件。零初态、实矩阵及上述稳定性与双侧读数条件均保留在精确类型中。

平方根平衡方法与 Schmidt 分解属于经典系统理论。本节的工作是构造与连接完整证明项候选，不主张新的数学误差常数或首次形式化优先权。平方根算法可参照 pyMOR 官方 balanced truncation 教程；所复用 Mathlib 矩阵谱定理、正函数演算、Hilbert 和与伴随 API 均按仓库固定版本 `db584cd6d46c92f209a44c0f1c829460d327499d` 审查。

---

# 2026-09-06 增补：有序真实截断与严格内部稳定性

本节连接上一增补已构造的真实无限 Hankel 奇异权重与实际降阶系统。新增 `OrderedBalancedCoordinates`、`DiscreteSteinCompressionStability`、`OrderedStableBalancedTruncation` 三个候选 Lean 模块及同名 Scribe；文件位于 `D5/S3/Observer/Hankel/` 与相应 Blueprint 路径。文献定位与签名比较见 `Library/Control/discrete_balanced_truncation_stability.md`。本节候选证明源码尚未经过 Lean 内核或 Scribe 发射验证。

## A. 排序作用于整个坐标构造

给定已构造的 `Coordinates P Q`，以 Mathlib `Tuple.sort` 对负权重排序，得到置换 \(e\)。新权重为 \(\sigma'_i=\sigma_{e(i)}\)，同时以同一置换重排 \(T\) 的列与 \(S\) 的行。`reindexCoordinates` 重新证明
\[
S'T'=T'S'=I,\qquad S'P(S')^T=D',\qquad (T')^TQT'=D'.
\]
相应的实际状态矩阵满足
\[
\bar A'_{ij}=\bar A_{e(i),e(j)},\quad
\bar B'_{ij}=\bar B_{e(i),j},\quad
\bar C'_{ij}=\bar C_{i,e(j)}.
\]
`ordered_weight_antitone` 给出递减顺序；`retained_weight_ge_discarded` 给出每个保留权重不小于每个删除权重。权重多重集保持不变，所有递减排列具有相同的值序列。重复权重允许存在，对应特征向量的唯一性没有被断言。

`ordered_hankel_schmidt` 将同一有序构造接到原系统真实无限 Hankel 的正交模态、双向奇异向量方程、全部 \(\ell_2\) 输入上的完整展开和核刻画。这里没有仅排序一个数值列表后继续使用未置换的系统矩阵。

## B. 离散 Stein 不等式给出严格稳定性

一般稳定性引理只要求 \(D=\operatorname{diag}(w_i)>0\)、
\[
A^TDA+C^TC\preceq D,
\qquad \bigcap_{k\ge0}\ker(CA^k)=\{0\}.
\]
它不要求控制 Stein 不等式、奇异值排序、截断间隙或约化系统本身可观。

把矩阵按保留与删除坐标分块，取任意复特征对 \(A_{11}v=\lambda v\)，其中 \(v\ne0\)。将实不等式分别作用于复向量的实部和虚部，得到复能量不等式。对零扩展 \(x=(v,0)\)，有
\[
(1-|\lambda|^2)v^*D_1v
\ge \lVert C_1v\rVert_2^2+(A_{21}v)^*D_2(A_{21}v)\ge0.
\]
因为 \(v^*D_1v>0\)，首先得到 \(|\lambda|\le1\)。若等号成立，则两项非负能量同时为零：
\[
C_1v=0,\qquad A_{21}v=0.
\]
因此零扩展是完整系统的特征向量，\(Ax=\lambda x\) 且 \(Cx=0\)，从而 \(CA^kx=0\) 对全部 \(k\) 成立。完整实系统的可观性经实部、虚部转移为复可观性，推出 \(x=0\)，矛盾。

`principal_truncation_eigenvalue_lt_one` 写出上述实际矩阵与投影能量证明；`principal_truncation_spectrum_lt_one` 经 Mathlib 的有限维谱与特征向量等价，得到标准复谱上的结论
\[
\boxed{\forall\lambda\in\operatorname{spec}_{\mathbb C}(A_{11}),\quad |\lambda|<1.}
\]
复共轭极点、重复权重、完整保留及零维截断均包含在类型中。没有以只检查实特征值或自定义空泛稳定性字段代替该结论。

## C. 同一个有序模型同时具有稳定性与误差保证

`balanced_full_observable` 通过 \(T\bar A^k=A^kT\) 及逆坐标关系，从原系统的全部未来读数推导完整平衡实现的可观性。该步骤对排序后的 `Coordinates` 同样有效。

`orderedSystemCoordinates` 从原始 \(A,B,C\) 出发，沿上一增补的实际级数、正定性与平衡构造，再执行上述排序。终点 `ordered_stable_reduction` 的各个子句共同使用
\[
A_r=(S'AT')_{[0,r),[0,r)},\quad
B_r=(S'B)_{[0,r),:},\quad C_r=(CT')_{:,[0,r)}.
\]
对这个唯一指定的约化模型，证明保留最大的 \(r\) 个权重、全部复谱位于开单位圆内，以及
\[
\lVert y-y_r\rVert_{2,[0,N)}
\le2\left(\sum_{i=r}^{n-1}\sigma'_i\right)\lVert u\rVert_{2,[0,N)}.
\]
对有限能量输入，还同时证明误差能量可求和及整个半轴的平方尾和界。原系统上的前提仍是幂平方可和、实际未来读数的联合单射性以及实际对偶读数的联合单射性；没有输入约化模型已稳定的前提。

## D. 文献匹配与重复权重的准确含义

Duff 与 Kürschner 的 `arXiv:1902.01652v1` 第 3.2.1 节、打印页 8，明确区分普通无限时域离散平衡截断的稳定性保持与有限时域版本。本文以观测侧 Stein 不等式及完整可观性给出直接证明，未将该文有限时域 Proposition 3.1 的不同前提直接套用。

Varga 的 *Balanced truncation model reduction of periodic systems* 第 3 节、第三 PDF 页，在分块权重间隙条件下给出周期系统的稳定性与最小性联合结论。本文没有形式化周期版本，也没有把稳定性自动升级成约化最小性。

例如 \(A=\begin{pmatrix}0&1\\0&0\end{pmatrix}\)、\(B=(0,1)^T\)、\(C=(1,0)\) 满足真实 \(P=Q=I\)，两个奇异权重相等。保留第一坐标得到 \(A_r=0,B_r=0,C_r=1\)：严格稳定，但不可控。这个精确有理数实例说明，在重复权重内截断时，本节稳定性结论仍适用，而约化最小性需要另行处理。

无间隙稳定性论证依赖离散时间的正项 \(A_{21}^*D_2A_{21}\)。本节没有将同一论证直接推广到连续时间 Lyapunov 方程，或带有限时域残差的 Gramian。它形式化经典稳定性机制及仓库连接，不主张新的误差常数或首次证明优先权。

本轮独立运行了精确有理数及复有理数代数检查、数值复极点检查与有限时间误差回归。它们不执行 Lean，也不证明全称定理。排序和严格内部稳定性已具有完整候选证明脚本；谱半径到幂可和输入的转换、频域 \(H^\infty\) 范数接口及带噪 Ho–Kalman 的统一输入条件认证仍不属于本节已交付范围。

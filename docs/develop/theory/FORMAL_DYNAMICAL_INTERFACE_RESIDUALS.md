# 动力接口—余量演算
## ——商下降、carry、交换子流、预测闭包、记忆与因果查询的统一形式理论

**版本：v1.1，2026-09-05。第 27 节增补数据实现与降阶误差；第 5.3 节勘正全局精确下降的多步含义。**

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

**勘正，2026-09-05：** 一步可见下降只要求 \(PTQ=0\)，不要求 \(QTP=0\)。但对固定的 \(P,T\)，若该条件是全局算子恒等式，则 \(PT=\overline TP\) 归纳推出 \(PT^n=\overline T^{\,n}P\) 对所有 \(n\) 成立。因此向隐藏方向的泄漏不能在保持 \(PTQ=0\) 的同时于未来反馈破坏可见下降。原文“若泄漏随后反馈回来，多步预测仍可能失败”在此全局假设下错误，现予删除。有限采样上的一步吻合、单条轨道的吻合或随时间改变的接口不具有同样的全局前提，须另行处理。第 27.7 节给出有外部输入的精确下降版本。

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

# 27. 从完整行为构造最小线性实现与残差可认证降阶

## 27.1 本次增补的真值状态与已有接口

本节给出完整的数学推导，并对应三份已提交的 Lean 证明候选及配套 Scribe。**本次会话未运行 Lean 编译器或 Scribe 发射器，因此以下新声明不能标记为本轮已取得机器验证的 Lean 锚点。** 没有添加新的公理或证明占位，也没有手写冻结、覆盖或准入记录。有限有理数检验只用于排查公式错误，不能替代内核检查。

最小实现源文件位于 PR #5578：

`D5/S3/Observer/Hankel/SequenceHankelRealization.lean`。

降阶与精确下降源文件位于 PR #5580：

`D5/S3/Observer/Hankel/ProjectedRealizationError.lean`；

`D5/S3/Observer/Hankel/ProjectedExactDescent.lean`。

三份 Scribe 均位于 `Blueprint/` 下的同名 `.scribe.cs` 路径，并通过 `StatementSource.FromLean()` 引用声明。这里沿用 `HankelMinimalStateDimension` 的 `FiniteLinearRealization`，以及现有的 `markovParameter`、`reachableSubspace`、`eventualKernel` 和有限 Hankel 秩定理。现有商空间构造以给定的状态实现为起点，本节补充从完整数据本身产生实现的方向。

## 27.2 数据尾空间及其规范动力学

令 \(K\) 为域，\(U,Y\) 为 \(K\)-向量空间，给定完整输入输出参数序列

\[
m_n:U\longrightarrow Y\qquad(n\ge0).
\]

每个 \(m_n\) 都是线性映射。对年龄 \(j\) 和输入方向 \(u\)，定义尾序列

\[
h_{j,u}(i):=m_{i+j}u,
\qquad
\mathcal R_m:=\operatorname{span}_K\{h_{j,u}:j\ge0,\ u\in U\}
\subseteq Y^{\mathbb N}.
\]

\(\mathcal R_m\) 是无限块 Hankel 对象的列空间。这里“有限秩”严格表示 \(\mathcal R_m\) 有限维；在 Lean 中使用 `FiniteDimensional K (tailSpace m)`。不能用未经有限维前提保护的自然数 `finrank` 判别有限性，因为其对无限维空间采用零值约定。

定义

\[
(A_mx)(i):=x(i+1),\qquad B_mu:=h_{0,u},\qquad C_mx:=x(0).
\]

由于

\[
A_mh_{j,u}=h_{j+1,u},
\]

左移保持 \(\mathcal R_m\)，故 \(A_m\) 确实是该状态空间上的线性自映射。归纳得到

\[
(A_m^nx)(i)=x(i+n),\qquad
A_m^nB_mu=h_{n,u},\qquad
\boxed{C_mA_m^nB_m=m_n.}
\]

这个构造无需预先给出状态空间，也不要求指数模态分解、简单特征值或可对角化。零序列对应零维状态空间。

对应公开声明为 `sequenceDynamics_pow_apply`、`sequenceDynamics_pow_input`、`sequenceOutput_pow` 和 `sequence_markovParameter_eq`。

## 27.3 有限秩刻画及最小维数的达到

**定理 27.1。** \(\mathcal R_m\) 有限维，当且仅当 \(m\) 存在有限维线性实现。此时上述构造达到全部线性实现中的最小状态维数：

\[
\boxed{
\min\{\dim_K V:m_n=CA^nB\text{ 对所有 }n\}
=\dim_K\mathcal R_m.
}
\]

**证明。** 正向由第 27.2 节的构造。反向设 \((V,A,B,C)\) 是任意匹配完整数据的有限维实现，定义其全未来观察映射

\[
\mathcal O:V\to Y^{\mathbb N},\qquad
\mathcal O(v)(i)=CA^iv.
\]

对每个生成元，

\[
\mathcal O(A^jBu)(i)=CA^{i+j}Bu=m_{i+j}u=h_{j,u}(i).
\]

因此 \(\mathcal R_m\subseteq\operatorname{ran}\mathcal O\)。像空间有限维，且

\[
\dim_K\mathcal R_m
\le\dim_K\operatorname{ran}\mathcal O
\le\dim_K V.
\]

规范构造本身的状态空间恰为 \(\mathcal R_m\)，故下界达到。\(\square\)

对应声明：`tailSpace_le_futureOutput_range`、`finite_tailSpace_of_realization`、`tailSpace_finrank_le_stateDimension`、`finite_tailSpace_iff_exists_realization`、`realizationFromSequence_is_minimal`。

标量情形取 \(U=Y=K\)、\(m_n(u)=a_nu\)，得到 \(a_n=C_mA_m^nb\)，其中 \(b=B_m1\)。这刻画线性状态维数，不给出一般非线性观察者的最小记忆，也不等于 DFA 状态数。

## 27.4 有限窗口达到全局秩，以及压缩失败见证

规范系统可达，因为其输入迭代正好是张成状态空间的全部尾序列。它可观，因为

\[
C_mA_m^nx=x(n),
\]

全部未来读数为零即全部坐标为零。由仓库现有的稳定有限 Hankel 秩定理，若 \(r=\dim_K\mathcal R_m\)，且两个窗口边长 \(p,q\ge r\)，则直接由数据定义的块矩阵满足

\[
\boxed{\operatorname{rank}[m_{i+j}]_{0\le i<p,\,0\le j<q}=r.}
\]

这个步骤实际消费已有 `hankel_rank_eq_reachable_dim_sub_inter_unobservable_dim`，在新构造上代入可达空间为顶、不可见空间为底。对应声明为 `sequence_reachable_eq_top`、`sequence_eventualKernel_eq_bot`、`dataHankel_rank_eq_tailSpace`。

**定理 27.2。** 对任意线性压缩 \(L:\mathcal R_m\to W\)，若 \(W\) 有限维且 \(\dim_KW<r\)，则存在 \(x\) 与有限时间 \(n\)，使

\[
\boxed{Lx=0,\qquad C_mA_m^nx\ne0.}
\]

**证明。** 若所有被压成零的状态在每个未来时刻都不可见，则可观性给出 \(\ker L=0\)。秩零度定理推出 \(r=\dim\operatorname{ran}L\le\dim W\)，与假设矛盾。\(\square\)

对应声明 `smaller_compression_has_future_witness`。该 \(x\) 是有限多个输入历史方向的线性组合；本定理没有声称两个离散输入词发生同样的碰撞。窗口秩达到的结论也不自动提供从任意有限噪声样本识别未知无限序列的算法。

## 27.5 合法降阶模型与从递推推导的残差方程

以下取实赋范空间与连续线性映射。给定全系统 \(A:V\to V\)、\(B:U\to V\)、\(C:V\to Y\)，选择约化载体 \(W\)、压缩 \(P:V\to W\) 和提升 \(J:W\to V\)。实际构造

\[
\boxed{A_r=PAJ,\qquad B_r=PB,\qquad C_r=CJ.}
\]

当 \(W\) 有限维，这三张映射包装为已有 `FiniteLinearRealization`。要称为降维还须实际选择 \(\dim W<\dim V\)；该不等式不由构造名称保证。\(PJ=I_W\) 给出通常的回缩解释，下面的误差估计不需要这个附加等式。

令零初态全系统和约化系统分别满足

\[
x_{n+1}=Ax_n+Bu_n,\qquad
z_{n+1}=A_rz_n+B_ru_n,\qquad x_0=z_0=0.
\]

定义实际残差映射和状态误差

\[
R_A:=AJ-JA_r,\qquad R_B:=B-JB_r,\qquad e_n:=x_n-Jz_n.
\]

直接展开两条更新并使用线性性，得到

\[
\boxed{e_{n+1}=Ae_n+R_Az_n+R_Bu_n.}
\]

误差等式是证明的结论，未作为调用者必须提供的假设。对应声明 `stateError_succ`。

**定理 27.3，有限时间证书。** 对任意输入、任意 \(n\)，

\[
\boxed{
\|e_n\|\le
\sum_{k=0}^{n-1}\|A\|^{n-1-k}
\bigl(\|R_A\|\|z_k\|+\|R_B\|\|u_k\|\bigr).
}
\]

因此

\[
\|Cx_n-C_rz_n\|
\le\|C\|\sum_{k=0}^{n-1}\|A\|^{n-1-k}
\bigl(\|R_A\|\|z_k\|+\|R_B\|\|u_k\|\bigr).
\]

**证明。** 残差方程给出

\[
\|e_{n+1}\|\le\|A\|\|e_n\|+\|R_A\|\|z_n\|+\|R_B\|\|u_n\|.
\]

从 \(e_0=0\) 归纳展开有限卷积。输出差为 \(Ce_n\)，再使用算子范数不等式。\(\square\)

对应声明 `stateError_le_residual_sum`、`outputError_le_residual_sum`。本结论不要求稳定性，所需残差均来自构造出的合法状态系统。

## 27.6 收缩条件下的显式一致输出误差

设 \(M\ge0\)、\(\|u_k\|\le M\)，且在所选范数下

\[
\alpha:=\|A\|<1,\qquad\beta:=\|A_r\|<1.
\]

由约化状态递推归纳可得

\[
\|z_n\|\le Z:=\frac{\|B_r\|M}{1-\beta}.
\]

记 \(\delta=\|R_A\|\)、\(\varepsilon=\|R_B\|\)。量

\[
E:=\frac{\delta Z+\varepsilon M}{1-\alpha}
\]

满足 \(\alpha E+\delta Z+\varepsilon M=E\)。从初始误差零和第 27.5 节的递推，再次归纳得到 \(\|e_n\|\le E\)。于是

\[
\boxed{
\|Cx_n-C_rz_n\|
\le
\frac{\|C\|M}{1-\alpha}
\left(\frac{\delta\|B_r\|}{1-\beta}+\varepsilon\right)
\quad\text{对所有 }n.
}
\]

对应声明 `drivenState_norm_le_of_contraction`、`outputError_uniform_of_contraction`。分母为正由两条严格收缩假设保证。谱半径小于一不能直接替换这些算子范数条件；需要另行构造适合的范数或幂次增长界。

若 \(R_A=R_B=0\)，有限时间证书直接给出对全部输入和时刻的精确输出一致，且无须收缩。对应 `zero_residuals_preserve_outputs`。

这是残差型可认证降阶。当前没有证明平衡坐标构造、平衡截断的稳定性保持、Hankel 范数最优性或 \(2\sum\sigma_k\) 型误差界，也没有把普通矩阵低秩逼近当作动力学降阶。

## 27.7 精确可见下降与全状态重建误差的区分

**定理 27.4。** 若固定映射满足全局下降恒等式

\[
PA=A_rP,
\]

则对同一输入与零初态，

\[
\boxed{Px_n=z_n\quad\text{对所有 }n.}
\]

若还有 \(C=C_rP\)，则 \(Cx_n=C_rz_n\) 对所有 \(n\) 成立。

**证明。** 初始时等式显然。若 \(Px_n=z_n\)，则

\[
Px_{n+1}=PAx_n+PBu_n=A_rPx_n+B_ru_n
=A_rz_n+B_ru_n=z_{n+1}.
\]

输出结论再代入 \(C=C_rP\)。\(\square\)

对应 `ProjectedExactDescent.projectedState_eq_of_descent` 与 `ProjectedExactDescent.outputs_eq_of_descent`。这给出第 5.3 节勘正的带输入版本。精确可见输出并不要求 \(x_n=Jz_n\)，也不要求提升残差 \(R_A\) 为零。

例如

\[
A=\begin{pmatrix}1/2&0\\3&1/3\end{pmatrix},\quad
P=\begin{pmatrix}1&0\end{pmatrix},\quad J=P^\mathsf T,\quad
B=\begin{pmatrix}1\\0\end{pmatrix},\quad C=P.
\]

此时 \(A_r=1/2\)，\(PA=A_rP\)，但 \(AJ-JA_r=(0,3)^\mathsf T\ne0\)。隐藏坐标可以持续获得输入影响，可见输出仍在所有时刻精确闭合。该矩阵例是本节的显式数学示例，本轮对其另做了 50 步精确有理数回归；没有将这项有限检验冒充一个独立的已编译 Lean 实例。

## 27.8 验证范围、归属及剩余工程

本批单会话数学审查之外，实际完成了确定性种子 `20260905` 的精确有理数检验：60 个状态实现案例、60 个投影模型案例、1,260 项有限时间误差检查及在双收缩假设成立处的 1,155 项一致界检查。案例包含多输入多输出、零行为、幂零 Jordan 块、重复特征值、非正交回缩及谱稳定但所选算子范数大于一的情形。全部这些有限检查通过；它们不证明全称命题，也不产生 Lean 内核或 Scribe 发射状态。

一般有限秩实现与残差传播是经典数学结构。本批不主张数学首创或首次形式化；仓库增量是消除预先提供实现的假设，实际构造可达可观状态，消费既有有限 Hankel 秩结果，并为合法降阶给出完整的残差误差链。

还需分别完成：坐标化并可执行的有限数据 Ho–Kalman 构造；噪声与扰动稳定性；平衡截断及其专门误差界；一般稳定系统的幂次范数控制。无限 Herglotz／强 Szegő、黄金编码素数语言免疫性、Petz／Fawzi–Renner 和黄金 Denjoy–Koksma 属于另外的既定目标，本节没有将它们记为已完成。

若

\[
PQ\ne QP,
\]

则不存在同时保留二者锐利性的共同 Boolean 精化。量子相对性不是普通坐标变换，因为坐标变换不能把非交换关系消除为交换关系。

---

## 30.9 量子上下文是一张局部经典图

### 定义 30.18（测量上下文）

一个量子上下文是 \(\mathcal A\) 中的最大交换含幺 \(C^*\)-子代数

\[
\mathcal C\subseteq\mathcal A.
\]

有限维时，\(\mathcal C\) 由一族最小正交投影

\[
P_1,\ldots,P_m,
\qquad
\sum_iP_i=I
\]

生成。

状态限制

\[
\omega|_{\mathcal C}
\]

对应经典概率分布

\[
\boxed{
p_i=\omega(P_i).
}
\]

所以：

\[
\boxed{
\text{每一个量子上下文本身都是一个经典概率界面。}
}
\]

不同上下文 \(\mathcal C,\mathcal D\) 在交集

\[
\mathcal C\cap\mathcal D
\]

上必须给出相同限制，因为它们来自同一个全局状态 \(\omega\)。

### 定义 30.19（上下文预层）

对每个上下文 \(\mathcal C\)，令

\[
\mathsf{Val}(\mathcal C)
\]

表示其锐利 \(0/1\) 赋值或更一般的概率赋值集合。若

\[
\mathcal D\subseteq\mathcal C,
\]

则有自然限制映射

\[
\operatorname{res}_{\mathcal C,\mathcal D}:
\mathsf{Val}(\mathcal C)\to\mathsf{Val}(\mathcal D).
\]

局部赋值族 \((v_{\mathcal C})\) 若在所有交集上兼容，就形成一个相容局部截面族。

### 定义 30.20（全局经典化）

若存在一个上下文无关赋值 \(v\)，其对每个 \(\mathcal C\) 的限制均等于 \(v_{\mathcal C}\)，则称该局部族可全局经典化。

Kochen–Specker 型障碍说明，在维数至少三的量子投影结构中，满足函数关系的锐利局部赋值一般不存在全局截面。这里的严格结构是：

\[
\boxed{
\text{每张局部图可以经典化，但全部图不能同时拼平。}
}
\]

因此量子性可以表述为一种相对完成失败：

\[
\boxed{
\text{局部 Boolean 商均存在，全球 Boolean 逆极限点不存在。}
}
\]

该陈述引用经典 Kochen–Specker 结果作为外部数学事实；本节没有重新证明其有限构型。

---

## 30.10 “绝对量子态”不是一个隐藏的全局经典答案表

密度算子 \(\rho\) 确实对每个 effect 给出统一数值

\[
E\mapsto\operatorname{Tr}(\rho E).
\]

但这不是给所有投影预先指定 \(0/1\) 结果。它是一个非交换事件代数上的概率状态。

因此必须区分：

\[
\boxed{
\text{全局量子状态}
}
\]

与

\[
\boxed{
\text{全局经典确定赋值}.
}
\]

前者存在；后者一般不存在。

量子态统一的是所有上下文的**概率兼容性**：

\[
\omega|_{\mathcal C\cap\mathcal D}
\]

从两侧一致。

它不统一为所有上下文中的确定结果同时存在。

所以“绝对是全部相对关系的闭合”在量子理论中的正确版本是：

\[
\boxed{
\text{全局量子状态是所有局部经典概率图在重叠处的一致状态，}
}
\]

而不是：

\[
\boxed{
\text{存在一张隐藏的全局经典样本表。}
}
\]

---

## 30.11 纠缠是局部商无法分配的关联余量

设复合系统

\[
\mathscr H_{AB}
=
\mathscr H_A\otimes\mathscr H_B.
\]

全局状态为 \(\rho_{AB}\)。局部观察界面是限制到子代数

\[
\mathcal A_A\otimes I_B.
\]

其代表密度算子为偏迹

\[
\boxed{
\rho_A=\operatorname{Tr}_B\rho_{AB}.
}
\]

两个全局状态若具有相同 \(\rho_A\)，则相对于所有 \(A\)-局部测量不可区分，即落入同一个局部观察纤维。

### 定理 30.21（纯全局态可投影成混合局部态）

取 Bell 态

\[
|\Phi^+\rangle
=
\frac{|00\rangle+|11\rangle}{\sqrt2}.
\]

则

\[
\rho_{AB}
=
|\Phi^+\rangle\langle\Phi^+|
\]

为秩一纯态，但

\[
\boxed{
\rho_A
=
\operatorname{Tr}_B\rho_{AB}
=
\frac12I_A.
}
\]

#### 证明

展开

\[
\rho_{AB}
=
\frac12(
|00\rangle\langle00|
+
|00\rangle\langle11|
+
|11\rangle\langle00|
+
|11\rangle\langle11|
).
\]

对 \(B\) 偏迹时，交叉项含

\[
\langle1|0\rangle
\quad\text{或}\quad
\langle0|1\rangle
\]

而消失，对角项分别留下 \(|0\rangle\langle0|\) 与 \(|1\rangle\langle1|\)。 \(\square\)

所以局部混合不是必然源于一个预先存在的经典混合，而可以来自：

\[
\boxed{
\text{全局纯关联被局部界面遗忘。}
}
\]

纠缠余量并不属于某个单独局部余空间；它存在于张量因子之间的关联结构中。

---

## 30.12 测量必须拆成概率、记录与条件更新

一个量子仪器由完全正映射族

\[
(\mathcal I_i)_i
\]

组成，且总映射保持迹。定义 effect

\[
E_i=\mathcal I_i^*(I).
\]

对状态 \(\rho\)：

\[
\boxed{
p_i
=
\operatorname{Tr}(\mathcal I_i(\rho))
=
\operatorname{Tr}(\rho E_i).
}
\]

若 \(p_i>0\)，结果 \(i\) 后的条件状态为

\[
\boxed{
\rho_i
=
\frac{\mathcal I_i(\rho)}{p_i}.
}
\]

因此一次测量至少包含三个不同对象：

\[
\boxed{
\begin{aligned}
E_i
&=\text{概率事件},\\
i
&=\text{经典记录标签},\\
\mathcal I_i
&=\text{状态更新规则}.
\end{aligned}
}
\]

仅知道 POVM \((E_i)\) 一般不能唯一决定条件状态更新。

理想 Lüders 投影测量是特殊情形：

\[
\mathcal I_i(\rho)=P_i\rho P_i,
\]

于是

\[
p_i=\operatorname{Tr}(\rho P_i),
\qquad
\rho_i=\frac{P_i\rho P_i}{p_i}.
\]

所以“坍缩”不是概率本身，而是给定记录后的条件状态更新。

---

## 30.13 Naimark 与 Stinespring：相对随机性可由更大空间中的锐利结构实现

### Naimark 扩张

对 POVM

\[
E_i\ge0,
\qquad
\sum_iE_i=I_{\mathscr H},
\]

存在更大 Hilbert 空间 \(\mathscr K\)、等距嵌入

\[
V:\mathscr H\to\mathscr K
\]

及正交投影族 \((\Pi_i)\)，使

\[
\boxed{
E_i=V^*\Pi_iV.
}
\]

因此

\[
\boxed{
\operatorname{Tr}(\rho E_i)
=
\operatorname{Tr}(V\rho V^*\Pi_i).
}
\]

### Stinespring 扩张

对完全正映射

\[
\Phi:\mathcal A\to\mathcal B(\mathscr H),
\]

存在表示 \(\pi\) 与算子 \(V\)，使


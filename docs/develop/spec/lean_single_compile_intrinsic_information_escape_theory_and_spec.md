# Lean 4 单次编译内生信息逃逸定理系统

## 纯数学理论与工程实现规范

**文档状态：** 规范性草案（Normative Draft）  
**版本：** 3.0 — Single-Compilation / No-Baseline / No-Scoring  
**适用对象：** `the-omega-institute/trureturing` 中由 Lean 4 定义、证明、登记和编译的数学定理族  
**核心约束：** 一次 `lake build` 完成定理枚举、信息逃逸计算、伴随命题证明、失败判定与只读产物发射。

---

# 摘要

本规范定义一个完全位于 Lean 4 内部的数学系统。系统的输入不是论文、自然语言标签、人工评分或历史版本差分，而是同一次编译中已经 elaborated 的 Lean 定理对象及其数学概念读出。

设当前完整定理族为

$$
\mathcal T=\{\tau_i\}_{i\in I}.
$$

每个定理对象包含：

$$
\tau_i=(P_i,p_i,c_i),
$$

其中：

- $P_i:\mathrm{Prop}$ 是原定理陈述；
- $p_i:P_i$ 是 Lean kernel 接受的证明；
- $c_i:X\to O_i$ 是该定理在其数学语义空间 $X$ 上建立、约束或公开的概念读出；
- $O_i$ 可以依赖于 $i$，只要求其相等关系可判定。

对任意定理子族 $S\subseteq I$，定义其联合不可区分核：

$$
K_S
=
\left\{
(x,y)\in X^2
\;\middle|\;
\forall i\in S,\ c_i(x)=c_i(y)
\right\}.
$$

去除对角线后，定义该定理子族尚未消除的信息逃逸：

$$
E_S
=
K_S\setminus\Delta_X,
\qquad
\Delta_X=\{(x,x):x\in X\}.
$$

在有限非平凡状态空间上，信息逃逸率唯一地取为均匀有序非对角 pair 的碰撞概率：

$$
\varepsilon(S)
=
\frac{|E_S|}{|X|(|X|-1)}.
$$

本系统不使用历史基线。对当前定理族中的每个 $i$，在同一个完整族中构造其**留一反事实族**：

$$
I^{-i}=I\setminus\{i\}.
$$

定理 $\tau_i$ 的内生信息增益定义为：

$$
\delta_i(\mathcal T)
=
\varepsilon(I^{-i})-\varepsilon(I).
$$

等价地，定义该定理独有捕获的状态对：

$$
U_i
=
E_{I^{-i}}\setminus E_I.
$$

则：

$$
\delta_i(\mathcal T)
=
\frac{|U_i|}{|X|(|X|-1)}.
$$

因此定理的伴随信息命题为：

$$
G_i(\mathcal T)
:\Longleftrightarrow
\varepsilon(I)<\varepsilon(I^{-i}),
$$

也即：

$$
G_i(\mathcal T)
\Longleftrightarrow
U_i\neq\varnothing.
$$

系统最终为每个原定理构造增强定理：

$$
\widehat\tau_i
:
P_i\land G_i(\mathcal T).
$$

其证明为：

$$
\widehat p_i
=
\langle p_i,g_i\rangle,
$$

其中 $g_i:G_i(\mathcal T)$ 由同一次 Lean 编译对当前完整定理族精确计算并由 kernel 检查。

整个准入条件只有一个：

$$
\boxed{
\forall i\in I,\quad \delta_i(\mathcal T)>0
}
$$

即当前定理族必须是一个语义不可约的概念族：删除任意一个定理，信息逃逸率都严格上升。

本规范明确取消以下对象：

- 历史 baseline；
- parent catalog；
- 前后 commit 差分；
- 人工 novelty score；
- 用户可调权重；
- 用户可调 target；
- 用户可调阈值；
- 研究价值等级；
- 外部 C#／Python 判官；
- 两阶段生成源码再编译；
- 按提交顺序计算的边际贡献。

所有判断只来自当前完整 Lean 定理族自身所诱导的核、残余、有限计数和严格不等式。

---

# 第一部　纯数学理论

## 1. 基本对象

### 1.1 数学状态空间

固定一个类型：

$$
X:\mathrm{Type}.
$$

$X$ 不是评价者选择的测试集，而是该组数学概念共同作用的本体状态空间。若研究对象是有限自动机，则 $X$ 是自动机状态；若研究对象是有限编码，则 $X$ 是编码状态；若研究对象是有限模型，则 $X$ 是模型状态。

数值硬门要求：

$$
2\le |X|<\infty.
$$

一般无限理论仍可使用严格核包含版本，但不能伪装成可执行的有限逃逸率。

### 1.2 定理索引族

固定有限索引类型：

$$
I:\mathrm{Type},
\qquad
|I|<\infty.
$$

$I$ 中每个元素对应当前完整编译中的一个被登记数学定理对象。

### 1.3 异构定理读出

对每个 $i\in I$，给定一个输出类型：

$$
O_i:\mathrm{Type},
$$

以及概念读出：

$$
c_i:X\to O_i.
$$

不同定理可以有不同输出类型。联合核只逐坐标比较同一个定理的输出，因此无需把所有 $O_i$ 强制编码进同一总类型。

### 1.4 定理对象

一个可分析定理对象写作：

$$
\tau_i=(P_i,p_i,c_i),
$$

其中：

$$
P_i:\mathrm{Prop},
\qquad
p_i:P_i.
$$

$c_i$ 是定理数学内容的概念侧，而不是外部评价字段。原 theorem 与概念读出的联系必须在 Lean 中由其标准陈述形式或一个 kernel-checked 语义实现定理建立。

系统不得接受：

```text
importance = high
novelty = 0.91
weight = 37
```

系统只接受 Lean 项与 Lean 证明。

---

## 2. 联合观察与不可区分核

### 2.1 子族联合读出

对任意 $S\subseteq I$，联合读出可抽象写作：

$$
C_S(x)=(c_i(x))_{i\in S}.
$$

因输出依赖于 $i$，严格类型是一个 dependent function：

$$
C_S(x):\prod_{i:S}O_i.
$$

### 2.2 联合核

定义：

$$
K_S
=
\ker C_S
=
\left\{
(x,y)\in X^2
\;\middle|\;
C_S(x)=C_S(y)
\right\}.
$$

展开后：

$$
(x,y)\in K_S
\Longleftrightarrow
\forall i\in S,\ c_i(x)=c_i(y).
$$

$K_S$ 表示定理子族 $S$ 仍无法区分的全部状态对。

### 2.3 核的反单调性

若：

$$
S\subseteq T,
$$

则：

$$
K_T\subseteq K_S.
$$

证明直接来自量词范围扩大：更多概念坐标只会增加相等约束，不可能制造新的不可区分状态对。

### 2.4 对角线

定义：

$$
\Delta_X
=
\{(x,x):x\in X\}.
$$

对角线不是信息逃逸，因为任何正确观察都应允许状态与自身不可区分。

---

## 3. 内生信息逃逸

### 3.1 逃逸集合

定义定理子族 $S$ 的内生信息逃逸集合：

$$
E_S
=
K_S\setminus\Delta_X.
$$

等价地：

$$
E_S
=
\left\{
(x,y)\in X^2
\;\middle|\;
x\neq y
\land
\forall i\in S,\ c_i(x)=c_i(y)
\right\}.
$$

本定义不需要外部 target。目标固定为状态身份本身：不同状态应当被完整概念族尽可能区分。

在仓库既有概念语言中，它等价于：

$$
E_S
=
\operatorname{defectRelation}(C_S,\operatorname{id}_X).
$$

因此这是已有 `defectRelation` 在固定 identity target 上的内生特化，而不是新增一套平行定义。

### 3.2 逃逸单调性

若：

$$
S\subseteq T,
$$

则：

$$
E_T\subseteq E_S.
$$

加入定理只能缩小或保持逃逸集合。

### 3.3 完全区分

定理族 $S$ 完全区分状态，当且仅当：

$$
E_S=\varnothing.
$$

等价地：

$$
K_S=\Delta_X.
$$

等价地：

$$
C_S:X\to\prod_{i:S}O_i
$$

为单射。

完整系统不要求当前数学必须已经完备，因此准入不强制 $E_I=\varnothing$。系统只要求每个保留定理具有严格非零边际。

---

## 4. 唯一无权重逃逸率

### 4.1 有序非对角状态对

定义：

$$
D_X=X^2\setminus\Delta_X.
$$

若 $|X|=n$，则：

$$
|D_X|=n(n-1).
$$

### 4.2 均匀逃逸率

定义：

$$
\varepsilon(S)
=
\frac{|E_S|}{|D_X|}
=
\frac{|E_S|}{|X|(|X|-1)}.
$$

因此：

$$
0\le\varepsilon(S)\le1.
$$

### 4.3 概率解释

从 $D_X$ 上均匀抽取一个有序不同状态对 $(X_1,X_2)$。则：

$$
\varepsilon(S)
=
\Pr[C_S(X_1)=C_S(X_2)].
$$

所以信息逃逸率就是：

> 两个真实不同状态在当前定理概念族下仍发生观察碰撞的概率。

### 4.4 为什么没有权重参数

在有限 $D_X$ 上，要求测度同时满足：

1. 非负；
2. 有限可加；
3. 总质量为 $1$；
4. 对 $D_X$ 的任意置换不变；

则每个单点必须具有相同质量：

$$
\mu(\{p\})=\frac1{|D_X|}.
$$

因而对任意 $A\subseteq D_X$：

$$
\mu(A)=\frac{|A|}{|D_X|}.
$$

故在“不允许对任意状态 pair 赋予特殊优先权”的对称性原则下，均匀计数率是唯一选择。

这里不存在：

- 人工权重；
- 领域权重；
- theorem 权重；
- 风险系数；
- 成本系数；
- 手工阈值。

---

## 5. 单次编译中的留一反事实

### 5.1 完整族

当前编译完成后，完整被分析定理族是：

$$
I.
$$

这里的完整意味着“本次 root module 导入并登记的全部 theorem units”，不是历史仓库状态。

### 5.2 留一族

对每个 $i\in I$，定义：

$$
I^{-i}=I\setminus\{i\}.
$$

$I^{-i}$ 不是 baseline，不保存、不导入、不来自旧 commit。它只是当前有限族 $I$ 内部的一个反事实删除子集。

### 5.3 完整逃逸与留一逃逸

定义：

$$
E=E_I,
$$

$$
E^{-i}=E_{I^{-i}}.
$$

由单调性：

$$
E\subseteq E^{-i}.
$$

### 5.4 定理独有捕获集

定义：

$$
U_i
=
E^{-i}\setminus E.
$$

展开：

$$
U_i
=
\left\{
(x,y)\in X^2
\;\middle|\;
\begin{array}{l}
x\neq y,\\
\forall j\neq i,\ c_j(x)=c_j(y),\\
c_i(x)\neq c_i(y)
\end{array}
\right\}.
$$

$U_i$ 中的每一个 pair 都是：

- 其他所有定理联合仍无法区分；
- 只有保留 $i$ 才能区分；
- 因而构成 $i$ 在当前完整族中的不可替代信息。

### 5.5 留一信息增益

定义：

$$
\delta_i
=
\varepsilon(I^{-i})-\varepsilon(I).
$$

由 $E\subseteq E^{-i}$：

$$
\delta_i\ge0.
$$

又由有限不交分割：

$$
E^{-i}=E\;\dot\cup\;U_i,
$$

所以：

$$
|E^{-i}|=|E|+|U_i|.
$$

因此：

$$
\boxed{
\delta_i
=
\frac{|U_i|}{|X|(|X|-1)}
}
$$

### 5.6 严格降低命题

定义：

$$
\operatorname{LowersEscape}(\mathcal T,i)
:\Longleftrightarrow
\varepsilon(I)<\varepsilon(I^{-i}).
$$

等价地：

$$
\operatorname{LowersEscape}(\mathcal T,i)
\Longleftrightarrow
\delta_i>0.
$$

等价地：

$$
\operatorname{LowersEscape}(\mathcal T,i)
\Longleftrightarrow
U_i\neq\varnothing.
$$

---

## 6. 结构版本：不依赖有限计数

在任意类型 $X$ 上，定义：

$$
\operatorname{StructurallyLowersEscape}(\mathcal T,i)
:\Longleftrightarrow
K_I\subsetneq K_{I^{-i}}.
$$

因为：

$$
K_I
=
K_{I^{-i}}\cap\ker(c_i),
$$

严格包含等价于存在：

$$
\exists x,y,
\quad
\left(\forall j\neq i,\ c_j(x)=c_j(y)\right)
\land
c_i(x)\neq c_i(y).
$$

若额外要求 $x\neq y$，该 witness 自动成立，因为 $c_i(x)\neq c_i(y)$ 已推出 $x\neq y$。

有限非平凡 $X$ 上：

$$
\operatorname{StructurallyLowersEscape}(\mathcal T,i)
\Longleftrightarrow
\operatorname{LowersEscape}(\mathcal T,i).
$$

因此：

- 严格核缩小是基础数学命题；
- 精确逃逸率差是有限可执行实现；
- 二者不是两套评价体系，而是同一命题的结构层与计数层。

---

## 7. 语义闭包刻画

### 7.1 其他定理的语义闭包

定义：

$$
\operatorname{SemanticClosure}(I^{-i})
=
\left\{
q:X\to Q
\;\middle|\;
K_{I^{-i}}\subseteq\ker(q)
\right\}.
$$

即 $q$ 在其他所有定理无法区分的每个 fiber 上保持常值。

### 7.2 零增益等价

有：

$$
\delta_i=0
\Longleftrightarrow
U_i=\varnothing
\Longleftrightarrow
K_I=K_{I^{-i}}
\Longleftrightarrow
c_i\in\operatorname{SemanticClosure}(I^{-i}).
$$

### 7.3 正增益等价

有：

$$
\delta_i>0
\Longleftrightarrow
K_I\subsetneq K_{I^{-i}}
\Longleftrightarrow
c_i\notin\operatorname{SemanticClosure}(I^{-i}).
$$

这正是严格核新颖性准则在“当前完整族减去自身”上的内生应用。

---

## 8. 定理族不可约性

### 8.1 定义

定义当前完整定理族语义不可约：

$$
\operatorname{Irredundant}(\mathcal T)
:\Longleftrightarrow
\forall i\in I,\quad\delta_i>0.
$$

### 8.2 闭包形式

等价地：

$$
\operatorname{Irredundant}(\mathcal T)
\Longleftrightarrow
\forall i\in I,
\quad
c_i\notin\operatorname{SemanticClosure}(I^{-i}).
$$

### 8.3 核形式

等价地：

$$
\operatorname{Irredundant}(\mathcal T)
\Longleftrightarrow
\forall i\in I,
\quad
K_I\subsetneq K_{I^{-i}}.
$$

### 8.4 witness 形式

等价地：

$$
\operatorname{Irredundant}(\mathcal T)
\Longleftrightarrow
\forall i\in I,
\ \exists x_i,y_i,
\quad
\begin{cases}
\forall j\neq i,\ c_j(x_i)=c_j(y_i),\\
c_i(x_i)\neq c_i(y_i).
\end{cases}
$$

### 8.5 系统总准入定理

一次编译成功的数学条件就是：

$$
\boxed{
\operatorname{Irredundant}(\mathcal T)
}
$$

系统不比较哪个定理“更漂亮”，也不规定增益必须大于某个人工阈值。严格正值已经是无任意参数的平凡／非平凡分界。

---

## 9. 平凡与冗余的纯数学定义

### 9.1 平凡定理对象

相对于当前完整族，定义：

$$
\operatorname{TrivialInCatalog}(i)
:\Longleftrightarrow
\delta_i=0.
$$

这不等价于 proof 很短，也不等价于 theorem 名称简单。

### 9.2 常值概念

若 $c_i$ 为常值函数，则：

$$
\ker(c_i)=X^2.
$$

因此：

$$
K_I=K_{I^{-i}},
$$

从而：

$$
\delta_i=0.
$$

### 9.3 可由其他联合读出恢复

若存在函数：

$$
r:\prod_{j\neq i}O_j\to O_i
$$

使：

$$
c_i=r\circ C_{I^{-i}},
$$

则：

$$
c_i\in\operatorname{SemanticClosure}(I^{-i}),
$$

从而：

$$
\delta_i=0.
$$

### 9.4 同核重述

若存在 $j\neq i$，且：

$$
\ker(c_i)=\ker(c_j),
$$

则在同时保留 $i,j$ 时：

$$
\delta_i=\delta_j=0.
$$

因此以下形式会被自动排除：

- 可逆改名；
- 输出类型同构；
- 布尔取反；
- 坐标重新编码；
- theorem alias；
- 完全相同 concept 的不同 proof；
- 只改变 theorem 名称的重复声明。

### 9.5 超集包装

若 $c_i$ 是其他读出的 product 包装，而包装中的每个坐标都已由别的定理独立存在，则 $c_i$ 可由其他联合读出恢复，故：

$$
\delta_i=0.
$$

反过来，如果只保留 product theorem，删除各坐标 theorem，则 product theorem 可以具有正增益。

系统不会替人选择哪一种不可约基；它只拒绝同一编译中同时保留一个过完备族。

---

## 10. 重复、替代与基选择

### 10.1 重复双方同时为零

若两个定理提供同一个核，留一计算会得到：

$$
\delta_i=0,
\qquad
\delta_j=0.
$$

这是正确结果，而不是系统无法决定“保留谁”。当前族确实不是不可约族。

编译必须失败并报告 collision class。开发者删除任一重复项后重新编译，剩余代表将重新获得正边际。

### 10.2 不设置名称优先级

系统不得通过以下方式自动挑选重复代表：

- 文件路径字典序；
- theorem 名称长度；
- 提交时间；
- 作者身份；
- proof term 长度；
- 是否先出现；
- 人工 owner。

这些规则都不是信息逃逸数学。

### 10.3 多个不可约基

同一个联合核可能存在多个不同不可约生成族。系统允许每一个不可约族通过，但不在它们之间创造无根据的总排名。

因此系统解决的是：

$$
\text{当前族是否包含零边际成员？}
$$

而不是：

$$
\text{所有数学表达中哪一个基具有唯一审美最优性？}
$$

---

## 11. 次序、名称与表示不变性

### 11.1 索引置换不变性

若 $\pi:I\simeq I'$ 是索引等价，并据此重排定理族，则：

$$
\varepsilon(S)
=
\varepsilon(\pi(S)).
$$

对应定理的 $\delta_i$ 保持不变。

### 11.2 theorem 名称不变性

重命名 theorem declaration 不改变 $c_i$，因此不改变：

$$
K_S,
\quad
E_S,
\quad
\varepsilon(S),
\quad
\delta_i.
$$

### 11.3 输出双射不变性

若：

$$
f_i:O_i\simeq O_i',
$$

并替换：

$$
c_i'=f_i\circ c_i,
$$

则：

$$
\ker(c_i')=\ker(c_i),
$$

所有逃逸量不变。

### 11.4 proof term 不变性

只要原 theorem 的数学 concept 不变，替换证明项不会改变信息逃逸率。

所以系统不会因为：

- proof 更长；
- tactic 更多；
- 使用自动化；
- 手写 term；

而改变数学增益。

---

## 12. 信息熵解释

### 12.1 均匀状态变量

令随机变量 $X_0$ 在有限状态空间 $X$ 上均匀分布。

对 $S\subseteq I$，定义联合观察随机变量：

$$
Y_S=C_S(X_0).
$$

### 12.2 状态残余熵

定义：

$$
H_S=H(X_0\mid Y_S).
$$

加入更多 theorem concept 不会增加残余熵：

$$
S\subseteq T
\Longrightarrow
H_T\le H_S.
$$

### 12.3 留一条件信息

定理 $i$ 的熵增益是：

$$
\Delta H_i
=
H(X_0\mid Y_{I^{-i}})
-
H(X_0\mid Y_I).
$$

由于 $c_i(X_0)$ 是 $X_0$ 的确定函数：

$$
\Delta H_i
=
I(X_0;c_i(X_0)\mid Y_{I^{-i}})
=
H(c_i(X_0)\mid Y_{I^{-i}}).
$$

### 12.4 正值等价

在均匀全支撑有限分布下：

$$
\Delta H_i>0
\Longleftrightarrow
U_i\neq\varnothing.
$$

所以 kernel-counting 版本与 Shannon 版本在“是否严格提供独有信息”上完全一致。

### 12.5 为什么工程硬门使用 pair counting

Shannon entropy 包含对数和实数运算，通常是 `noncomputable` 或需要额外解析证明。pair counting：

- 完全精确；
- 只使用 `Nat` 与 `Rat`；
- 可由 `decide`／`native_decide` 计算；
- 与严格正条件等价；
- 不引入浮点误差。

故工程硬门使用 $|U_i|>0$，熵值作为数学等价投影而非判官。

---

## 13. 增强定理

### 13.1 原定理

对每个 $i\in I$：

$$
p_i:P_i.
$$

### 13.2 伴随逃逸降低命题

定义：

$$
G_i
:=
\operatorname{LowersEscape}(\mathcal T,i).
$$

### 13.3 增强陈述

定义：

$$
\widehat P_i
:=
P_i\land G_i.
$$

### 13.4 增强证明

若编译计算得到：

$$
g_i:G_i,
$$

则：

$$
\widehat p_i
:=
\langle p_i,g_i\rangle
:
\widehat P_i.
$$

### 13.5 不修改原 API

工程实现不得破坏已有 theorem 名称及使用方式。它应生成伴随 theorem：

```lean
theorem originalName.__escape_enriched :
    OriginalStatement ∧ LowersEscape compiledCatalog originalIndex :=
  ⟨originalName, originalName.__lowers_escape⟩
```

原 theorem 继续保持：

```lean
theorem originalName : OriginalStatement := ...
```

---

## 14. 一次编译而非历史比较

### 14.1 内部反事实

系统唯一比较的是：

$$
\mathcal T
\quad\text{与}\quad
\mathcal T\setminus\{\tau_i\}.
$$

二者都由当前编译中的同一个有限 catalog 纯函数生成。

### 14.2 不存在持久 baseline

规范中禁止：

```text
previous_snapshot
parent_commit
baseline_catalog
accepted_before
candidate_after
```

### 14.3 不存在顺序边际

系统不按：

$$
\tau_1,\tau_2,\ldots,\tau_n
$$

依次计算贡献。所有 $\delta_i$ 都相对于同一个完整族同步计算，因此结果与声明顺序无关。

### 14.4 新 theorem 可以使旧 theorem 变零

若加入新 theorem 后，旧 theorem 已可由其余族恢复，则旧 theorem 的 leave-one-out 增益会变为零。

这不是评价体系变化，而是当前数学族从不可约变成过完备。

编译应失败，直到当前定理族重新成为不可约基。

---

## 15. 系统自应用

### 15.1 系统数学也是定理对象

定义 `jointKernel`、`escapePairs`、`uniqueCapture`、`LowersEscape` 并证明其性质的 Lean theorem，与其他数学 theorem 没有本体差异。

只要它们被构造成相应数学 arena 中的 theorem unit，就由同一公式计算：

$$
\delta_i
=
\varepsilon(I^{-i})-\varepsilon(I).
$$

### 15.2 不特殊豁免系统 theorem

系统不得写：

```text
if theorem.namespace == ResearchAudit then accept
```

系统核心 authored theorem 与普通 authored theorem 使用同一个 registry 和同一个 `LowersEscape` 定义。

### 15.3 最终编译命令不是数学 theorem

`#seal_information_theory` 是 elaborator command。它执行枚举、构造证明项和发射产物，但不作为被分析 concept 加入 catalog。

其数学正确性由普通 Lean theorem 证明，而这些 soundness theorem 本身可以进入 catalog 接受自应用。

这样避免：

$$
\text{seal theorem 必须为自己生成 seal theorem}
$$

的无穷回归。

### 15.4 生成证书不是新信息 concept

`originalName.__lowers_escape` 与 `originalName.__escape_enriched` 是原 theorem 的证明证书，不被重新登记为新的 observer。否则每次编译会人为制造一层“证明此 theorem 有增益的 theorem”，造成无意义增长。

这不是特殊评价规则，而是输入／证书类型的数学区分：

- theorem unit 是被观察概念；
- certificate 是该 unit 性质的证明项。

---

## 16. 纯数学核心定理清单

以下 theorem 必须在 Lean 内正式证明。

### IE-001　联合核反单调

$$
S\subseteq T
\Longrightarrow
K_T\subseteq K_S.
$$

### IE-002　逃逸集合反单调

$$
S\subseteq T
\Longrightarrow
E_T\subseteq E_S.
$$

### IE-003　单 theorem 加入律

$$
K_{S\cup\{i\}}
=
K_S\cap\ker(c_i).
$$

### IE-004　单 theorem 逃逸加入律

$$
E_{S\cup\{i\}}
=
E_S\cap\ker(c_i).
$$

### IE-005　留一包含

$$
E_I\subseteq E_{I^{-i}}.
$$

### IE-006　独有捕获分割

$$
E_{I^{-i}}
=
E_I\;\dot\cup\;U_i.
$$

### IE-007　精确计数差

$$
|E_{I^{-i}}|
=
|E_I|+|U_i|.
$$

### IE-008　增益公式

$$
\delta_i
=
\frac{|U_i|}{|X|(|X|-1)}.
$$

### IE-009　正增益 witness

$$
\delta_i>0
\Longleftrightarrow
\exists x,y,
\left(\forall j\neq i,\ c_j(x)=c_j(y)\right)
\land
c_i(x)\neq c_i(y).
$$

### IE-010　严格核等价

$$
\delta_i>0
\Longleftrightarrow
K_I\subsetneq K_{I^{-i}}.
$$

### IE-011　语义闭包零增益

$$
\delta_i=0
\Longleftrightarrow
c_i\in\operatorname{SemanticClosure}(I^{-i}).
$$

### IE-012　可恢复概念零增益

若：

$$
c_i=r\circ C_{I^{-i}},
$$

则：

$$
\delta_i=0.
$$

### IE-013　同核双零

若 $i\neq j$ 且：

$$
\ker(c_i)=\ker(c_j),
$$

则：

$$
\delta_i=\delta_j=0.
$$

### IE-014　常值零增益

若 $c_i$ 为常值，则：

$$
\delta_i=0.
$$

### IE-015　索引置换不变

定理重排不改变对应增益。

### IE-016　输出等价不变

对输出施加双射不改变增益。

### IE-017　全族不可约等价

$$
\operatorname{Irredundant}(\mathcal T)
\Longleftrightarrow
\forall i,\delta_i>0.
$$

### IE-018　碰撞概率表示

$$
\varepsilon(S)
=
\Pr[C_S(X_1)=C_S(X_2)\mid X_1\neq X_2].
$$

### IE-019　条件信息表示

$$
\Delta H_i
=
I(X_0;c_i(X_0)\mid C_{I^{-i}}(X_0)).
$$

### IE-020　正熵与正 pair 增益等价

在有限均匀全支撑条件下：

$$
\Delta H_i>0
\Longleftrightarrow
|U_i|>0.
$$

### IE-021　均匀测度唯一性

有限非对角 pair 空间上，置换不变概率测度唯一等于归一化计数测度。

### IE-022　增强 theorem 构造

$$
P_i\to G_i\to(P_i\land G_i).
$$

### IE-023　全 catalog 增强

若：

$$
\forall i,\ G_i,
$$

则：

$$
\forall i,\ \widehat P_i.
$$

---

# 第二部　Lean 4 核心工程规范

## 17. 工程目标

实现一个 Lean-native 系统，使一次：

```bash
lake build Trureturing.InformationRoot
```

完成：

1. 加载全部相关模块；
2. 从 Lean persistent environment registry 枚举 theorem units；
3. 按数学 arena 分组；
4. 构造每个 arena 的当前完整有限 catalog；
5. 对每个 theorem 执行 leave-one-out；
6. 精确计算 `escapeFull`、`escapeWithout`、`uniqueCapture`；
7. 在 Lean 内构造 `LowersEscape` 证明；
8. 为原 theorem 构造增强 conjunction theorem；
9. 若任一 theorem 增益为零，则当前 compilation 失败；
10. 若全部通过，则写出只读 JSON／CSV／DOT 报告。

不得：

- 生成 `.lean` 文件后再次调用 Lean；
- 读取上一版报告；
- 调用 C# 决定通过／失败；
- 调用 Python 决定通过／失败；
- 让 JSON 参与 theorem 证明；
- 依赖 Git diff；
- 依赖 PR base；
- 依赖 commit 时间。

---

## 18. 建议模块布局

```text
D5/S3/InformationEscape/
  Arena.lean
  TheoremUnit.lean
  JointKernel.lean
  EscapePairs.lean
  EscapeRate.lean
  LeaveOneOut.lean
  SemanticClosure.lean
  EntropyBridge.lean
  AugmentedTheorem.lean
  CoreTheorems.lean

tools/lean-information-audit/
  Registry.lean
  Syntax.lean
  Reify.lean
  CatalogBuilder.lean
  ProofBuilder.lean
  SealCommand.lean
  Emit.lean
  Main.lean

D5/InformationRoot.lean
```

`D5/InformationRoot.lean` 必须导入所有需要审计的模块，并以唯一终局命令结束：

```lean
#seal_information_theory
```

---

## 19. 核心类型

以下接口是规范级草案。实现可调整字段名字，但不得改变数学含义。

### 19.1 Arena

```lean
universe u v w

namespace D5.S3.InformationEscape

structure Arena where
  State : Type u
  stateFintype : Fintype State
  stateDecidableEq : DecidableEq State
  stateNontrivial : 2 ≤ @Fintype.card State stateFintype
```

在使用 arena 时：

```lean
letI := arena.stateFintype
letI := arena.stateDecidableEq
```

### 19.2 PackedObserver

```lean
structure PackedObserver (arena : Arena) where
  Output : Type v
  outputDecidableEq : DecidableEq Output
  observe : arena.State → Output
```

### 19.3 TheoremUnit

```lean
structure TheoremUnit (arena : Arena) where
  observer : PackedObserver arena
  Statement : Prop
  proof : Statement
```

`observer` 是 theorem unit 的数学组成，不是评分元数据。

### 19.4 可选语义实现约束

对原生 information theorem，可要求 theorem 陈述严格采用 arena 的标准 law：

```lean
structure LawArena extends Arena where
  Law : (observer : PackedObserver toArena) → Prop

structure NativeTheoremUnit (arena : LawArena) where
  observer : PackedObserver arena.toArena
  proof : arena.Law observer
```

对 legacy theorem：

```lean
structure LegacyRealization
    (arena : LawArena)
    (statement : Prop)
    (observer : PackedObserver arena.toArena) where
  equivalence : statement ↔ arena.Law observer
```

这确保 concept 与 theorem 的连接仍然是 Lean 数学命题，而非字符串注释。

### 19.5 Catalog

```lean
structure Catalog (arena : Arena) where
  Index : Type w
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  theoremAt : Index → TheoremUnit arena
```

### 19.6 完整索引集

```lean
def Catalog.fullIndexSet
    (catalog : Catalog arena) : Finset catalog.Index := by
  letI := catalog.indexFintype
  exact Finset.univ
```

---

## 20. 核与逃逸 Finset API

### 20.1 对角线外 pair

```lean
def offDiagonalPairs (arena : Arena) : Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact Finset.univ.filter fun pair => pair.1 ≠ pair.2
```

### 20.2 子族不可区分

```lean
def indistinguishable
    (catalog : Catalog arena)
    (selected : Finset catalog.Index)
    (left right : arena.State) : Prop :=
  ∀ index, index ∈ selected →
    (catalog.theoremAt index).observer.observe left =
      (catalog.theoremAt index).observer.observe right
```

必须提供：

```lean
instance indistinguishableDecidable ... :
    Decidable (indistinguishable catalog selected left right)
```

该实例必须使用：

- `selected` 有限性；
- 每个 observer 的 `outputDecidableEq`；
- 不得使用 classical oracle 伪装成可执行计算。

### 20.3 逃逸 pair

```lean
def escapePairs
    (catalog : Catalog arena)
    (selected : Finset catalog.Index) :
    Finset (arena.State × arena.State) :=
  (offDiagonalPairs arena).filter fun pair =>
    indistinguishable catalog selected pair.1 pair.2
```

### 20.4 留一索引集

```lean
def without
    (catalog : Catalog arena)
    (index : catalog.Index) : Finset catalog.Index :=
  (catalog.fullIndexSet).erase index
```

### 20.5 独有捕获 pair

可直接定义：

```lean
def uniqueCapturePairs
    (catalog : Catalog arena)
    (index : catalog.Index) :
    Finset (arena.State × arena.State) :=
  (escapePairs catalog (without catalog index)).filter fun pair =>
    (catalog.theoremAt index).observer.observe pair.1 ≠
      (catalog.theoremAt index).observer.observe pair.2
```

也必须证明它等于差集：

```lean
theorem uniqueCapturePairs_eq_sdiff :
  uniqueCapturePairs catalog index =
    escapePairs catalog (without catalog index) \
      escapePairs catalog catalog.fullIndexSet := by
  ...
```

---

## 21. 精确逃逸率 API

### 21.1 分母

```lean
def escapeDenominator (arena : Arena) : Nat :=
  (offDiagonalPairs arena).card
```

必须证明：

```lean
theorem escapeDenominator_pos (arena : Arena) :
    0 < escapeDenominator arena := by
  ...
```

### 21.2 分子

```lean
def escapeNumerator
    (catalog : Catalog arena)
    (selected : Finset catalog.Index) : Nat :=
  (escapePairs catalog selected).card
```

### 21.3 精确有理率

```lean
def escapeRate
    (catalog : Catalog arena)
    (selected : Finset catalog.Index) : ℚ :=
  (escapeNumerator catalog selected : ℚ) /
    (escapeDenominator arena : ℚ)
```

不得使用：

- `Float`；
- `Double`；
- 十进制近似作为真源。

### 21.4 独有捕获数

```lean
def uniqueCaptureCount
    (catalog : Catalog arena)
    (index : catalog.Index) : Nat :=
  (uniqueCapturePairs catalog index).card
```

### 21.5 增益率

```lean
def theoremGainRate
    (catalog : Catalog arena)
    (index : catalog.Index) : ℚ :=
  (uniqueCaptureCount catalog index : ℚ) /
    (escapeDenominator arena : ℚ)
```

### 21.6 降低逃逸命题

```lean
def LowersEscape
    (catalog : Catalog arena)
    (index : catalog.Index) : Prop :=
  escapeRate catalog catalog.fullIndexSet <
    escapeRate catalog (without catalog index)
```

### 21.7 可执行等价命题

必须证明：

```lean
theorem lowersEscape_iff_uniqueCaptureCount_pos :
    LowersEscape catalog index ↔
      0 < uniqueCaptureCount catalog index := by
  ...
```

这是编译硬门使用的核心 theorem。

---

## 22. 结构 API

### 22.1 Set 级联合核

```lean
def jointKernel
    (catalog : Catalog arena)
    (selected : Set catalog.Index) :
    Set (arena.State × arena.State) :=
  {pair | ∀ index, index ∈ selected →
    (catalog.theoremAt index).observer.observe pair.1 =
      (catalog.theoremAt index).observer.observe pair.2}
```

### 22.2 结构降低

```lean
def StructurallyLowersEscape
    (catalog : Catalog arena)
    (index : catalog.Index) : Prop :=
  jointKernel catalog Set.univ ⊂
    jointKernel catalog {j | j ≠ index}
```

### 22.3 结构／有限桥

```lean
theorem structurallyLowersEscape_iff_lowersEscape :
    StructurallyLowersEscape catalog index ↔
      LowersEscape catalog index := by
  ...
```

### 22.4 语义闭包

```lean
def semanticClosureWithout
    (catalog : Catalog arena)
    (index : catalog.Index) :
    Set (PackedObserver arena) :=
  {candidate | ∀ left right,
    (∀ j, j ≠ index →
      (catalog.theoremAt j).observer.observe left =
        (catalog.theoremAt j).observer.observe right) →
    candidate.observe left = candidate.observe right}
```

异构 observer 的集合相等需要选择固定输出 universe；实现也可用 predicate-only 形式避免 observer 结构的 `DecidableEq`。

必须证明：

```lean
theorem lowersEscape_iff_not_mem_semanticClosureWithout :
    LowersEscape catalog index ↔
      (catalog.theoremAt index).observer ∉
        semanticClosureWithout catalog index := by
  ...
```

---

## 23. 增强 theorem API

### 23.1 增强陈述

```lean
def AugmentedStatement
    (catalog : Catalog arena)
    (index : catalog.Index) : Prop :=
  (catalog.theoremAt index).Statement ∧
    LowersEscape catalog index
```

### 23.2 增强证明构造

```lean
def augmentedProof
    (catalog : Catalog arena)
    (index : catalog.Index)
    (gain : LowersEscape catalog index) :
    AugmentedStatement catalog index :=
  ⟨(catalog.theoremAt index).proof, gain⟩
```

### 23.3 catalog 全正命题

```lean
def CatalogIrredundant
    (catalog : Catalog arena) : Prop :=
  ∀ index, LowersEscape catalog index
```

### 23.4 可判定实例

```lean
instance catalogIrredundantDecidable
    (catalog : Catalog arena) :
    Decidable (CatalogIrredundant catalog) := by
  ...
```

该实例可基于：

```lean
∀ index, 0 < uniqueCaptureCount catalog index
```

的有限决定过程构造。

---

## 24. theorem 登记语法

### 24.1 新 theorem 原生语法

建议命令：

```lean
information_theorem theoremName
  in ArenaName
  observing observerExpression
  : Proposition := by
  proof
```

展开语义：

```lean
theorem theoremName : Proposition := by
  proof

private def theoremName.__information_unit :
    TheoremUnit ArenaName :=
  {
    observer := packObserver observerExpression
    Statement := Proposition
    proof := theoremName
  }
```

并把：

```text
(theoremName, theoremName.__information_unit, ArenaName)
```

登记进 persistent environment extension。

### 24.2 legacy theorem 登记

```lean
register_information_theorem existingTheorem
  in ArenaName
  observing observerExpression
  realization existingTheoremSemanticRealization
```

其中 `realization` 必须是 Lean theorem，不得是字符串说明。

### 24.3 禁止字段

登记结构中不得出现：

```text
score
weight
importance
priority
minimum_gain
threshold
baseline
parent
previous
owner_override
novelty_class
```

### 24.4 唯一登记

每个 authored theorem declaration 在一个 information root 中：

- 恰有一个 theorem unit；
- 恰属于一个 canonical arena；
- 恰有一个 concept observer。

多重登记必须 fail-closed，因为多个可选语义视图会重新引入人为选择。

---

## 25. Persistent Environment Extension

### 25.1 registry entry

```lean
structure InformationRegistryEntry where
  theoremName : Name
  unitName : Name
  arenaName : Name
```

### 25.2 持久性

registry 必须使用 Lean persistent environment extension，使：

- 每个模块编译时登记本模块 theorem units；
- `.olean` 保存登记结果；
- root module 导入后能看到所有 imported entries；
- 无需扫描源文本；
- 无需 Git 文件列表。

### 25.3 环境真源

最终 catalog 只由：

```lean
Environment
```

中的已 elaborated declaration 和 registry 构造。

不得从以下内容决定 theorem 集：

- Markdown；
- Blueprint；
- YAML；
- 文件头注释；
- 正则表达式；
- Git diff。

### 25.4 registry 完整性

必须检查：

- theoremName 存在；
- theoremName 的 kind 是 theorem；
- unitName 存在；
- unitName 的类型是期望的 `TheoremUnit arena`；
- unit.proof 的类型与 theoremName 的 type 定义相同或可由 kernel 证明相等；
- arenaName 存在且可关闭实例；
- 没有重复 theoremName；
- 没有重复 unitName。

---

## 26. 单次终局命令

### 26.1 命令形式

```lean
#seal_information_theory
```

可选只读输出路径：

```lean
#seal_information_theory
  output "build/information-theory"
```

路径只控制 artifact 写出位置，不影响任何数学判词。

### 26.2 命令执行顺序

命令必须在一次 elaboration 中执行以下步骤：

1. 读取 registry；
2. 校验 entry；
3. 按 arenaName 确定性排序；
4. 每个 arena 内按 theorem canonical `Name` encoding 排序；
5. 构造有限 index type 或等价数组 catalog；
6. 构造完整 `Finset.univ`；
7. 枚举 `offDiagonalPairs`；
8. 计算完整族 `escapePairs`；
9. 对每个 index 计算 `without`；
10. 计算 `uniqueCapturePairs`；
11. 计算 exact Nat／Rat 数值；
12. 为 `0 < uniqueCaptureCount` 构造 proof；
13. 经 `lowersEscape_iff_uniqueCaptureCount_pos` 得到 `LowersEscape` proof；
14. 添加 private 或 namespaced companion theorem；
15. 若任一 count 为零，发出 elaboration error；
16. 全部 theorem proof 加入 environment 后，写出只读 artifact；
17. 命令成功结束。

### 26.3 不得启动第二次 Lean

实现不得：

```text
write Generated.lean
lake env lean Generated.lean
```

所有 generated declaration 必须通过当前 elaborator process 的 `addDecl`／等价受支持接口加入当前 environment。

### 26.4 fail-closed

以下任一情形使命令报错并使编译失败：

- arena 无法实例化；
- state cardinal 小于 2；
- observer 输出无 `DecidableEq`；
- theorem unit 非闭合；
- theorem 语义登记重复；
- 任一 `uniqueCaptureCount = 0`；
- proof builder 无法构造 kernel 可接受证明；
- artifact 在数学检查之前被写出；
- registry 与 environment 不一致。

---

## 27. 伴随 theorem 命名规范

对 theorem：

```text
D5.S3.Domain.SomeResult.main_theorem
```

生成：

```text
D5.S3.Domain.SomeResult.main_theorem.__lowers_escape
D5.S3.Domain.SomeResult.main_theorem.__escape_enriched
```

规范类型：

```lean
theorem main_theorem.__lowers_escape :
    LowersEscape compiledArenaCatalog compiledIndex := by
  ...

 theorem main_theorem.__escape_enriched :
    OriginalStatement ∧
      LowersEscape compiledArenaCatalog compiledIndex :=
  ⟨main_theorem, main_theorem.__lowers_escape⟩
```

生成 declaration 必须：

- `includeInStatement = false` 或等价 internal 标记；
- 不进入 information registry；
- 不参与下一次同编译 catalog 枚举；
- 可由 inspector 输出为 certificate；
- 不被计算为新增数学 theorem unit。

---

## 28. 编译证明构造

### 28.1 首选反射证明

所有有限计算函数应满足：

```lean
@[implemented_by ...]
```

或普通可归约定义，并有 correctness theorem。

终局命令可以构造：

```lean
by native_decide
```

等价 proof，但规范更推荐：

1. 计算具体 `Nat`；
2. 生成 equality proof；
3. 通过通用 correctness theorem 得到目标命题。

### 28.2 不信任计算输出

一个 meta 程序打印：

```text
uniqueCaptureCount = 5
```

本身不是数学证明。

必须最终生成 Lean proof term：

```lean
0 < uniqueCaptureCount catalog index
```

并由 kernel 接受。

### 28.3 可信边界

数学信任边界是：

- Lean kernel；
- core reduction；
- theorem definitions；
- 通用 correctness proofs。

Meta／IO 层只负责：

- 枚举环境；
- 组织表达式；
- 请求 elaboration；
- 输出投影。

---

## 29. 单次编译数据流

```text
Lean source theorem units
          │
          ▼
module elaboration + persistent registry
          │
          ▼
final root Environment
          │
          ▼
#seal_information_theory
          │
          ├── group by mathematical arena
          ├── build current full catalog
          ├── construct leave-one-out families
          ├── compute exact escape pairs
          ├── prove every strict decrease
          ├── add companion theorems
          └── fail on any zero marginal
          │
          ▼
Lean kernel accepts final environment
          │
          ▼
read-only JSON / CSV / DOT artifacts
```

没有环节读取旧状态。

---

## 30. 只读 artifact 规范

### 30.1 JSON 根结构

```json
{
  "schema": "lean-intrinsic-information-escape-v1",
  "catalog_mode": "single-compilation-leave-one-out",
  "arenas": []
}
```

### 30.2 arena 记录

```json
{
  "arena": "D5.S3.Example.BoolPairArena",
  "state_card": 4,
  "off_diagonal_pair_count": 12,
  "full_escape_count": 0,
  "full_escape_rate": {
    "numerator": 0,
    "denominator": 12
  },
  "theorems": []
}
```

### 30.3 theorem 记录

```json
{
  "theorem": "D5.S3.Example.first_coordinate_theorem",
  "unit": "D5.S3.Example.first_coordinate_theorem.__information_unit",
  "full_escape_count": 0,
  "without_escape_count": 4,
  "unique_capture_count": 4,
  "gain_rate": {
    "numerator": 4,
    "denominator": 12
  },
  "lowers_escape": true,
  "certificate": "D5.S3.Example.first_coordinate_theorem.__lowers_escape"
}
```

### 30.4 禁止字段

artifact 中不得出现：

```text
baseline_commit
parent_snapshot
human_score
importance
manual_weight
approval_override
minimum_threshold
```

### 30.5 artifact 不可回写

下一次编译不得读取该 JSON 作为数学输入。

它可以用于：

- 可视化；
- 文档；
- 趋势观察；
- 人类审阅；

但不能影响准入。

---

## 31. 编译错误规范

建议错误码：

### IE-C001　UnregisteredTheoremUnit

需要审计的 authored theorem 没有 theorem unit。

### IE-C002　DuplicateRegistration

同一 theorem 被登记超过一次。

### IE-C003　ArenaResolutionFailed

arena declaration 无法关闭。

### IE-C004　DegenerateArena

$$
|X|<2.
$$

### IE-C005　ObserverEqualityUndecidable

observer 输出类型缺少可执行相等判定。

### IE-C006　StatementProofMismatch

theorem unit 中的 proof 与登记 theorem type 不一致。

### IE-C007　ZeroUniqueCapture

$$
|U_i|=0.
$$

错误信息必须同时报告：

- theorem 名；
- arena 名；
- full escape count；
- leave-one-out escape count；
- 同核／闭包候选（若可证明）；
- 不得建议提高人工分数。

### IE-C008　OvercompleteCollisionClass

多个 observer 具有相同 kernel，导致成员共同零边际。

### IE-C009　ProofConstructionFailed

计算结果存在，但无法构造 kernel proof。

### IE-C010　ArtifactPrematureWrite

数学检查完成前尝试发射产物。

### IE-C011　GeneratedCertificateRegistered

伴随 certificate 被错误地重新加入 theorem unit registry。

### IE-C012　ExternalDecisionAttempt

检测到外部程序试图提供 accept/reject 判词。

---

## 32. 反平凡化硬规则

### R-001　零边际一律失败

```text
uniqueCaptureCount = 0  => compilation error
```

无 owner override。

### R-002　正值无人工阈值

```text
uniqueCaptureCount > 0 => mathematical nontriviality condition satisfied
```

系统不得写：

```text
uniqueCaptureCount >= 10
```

除非 `10` 本身由另一个数学 theorem 唯一推出；v1 不允许此扩展。

### R-003　proof 长度不参与

proof AST、tactic 数量、文件行数仅可作为性能诊断，不得进入 `LowersEscape`。

### R-004　名称不参与

Name、GID、路径仅用于寻址，不得进入增益公式。

### R-005　文献新颖性不参与数学率

外部文献是否已有该结论属于来源学问题，不是 kernel escape rate 的组成。文献审计可以作为独立投影，但不能改变 $\delta_i$。

### R-006　过完备族整体失败

若加入一个新 theorem 使旧 theorem 变为零边际，当前完整族失败。系统不得因为旧 theorem 先存在而保留它。

### R-007　无顺序优先

先声明或后声明不影响结果。

### R-008　无历史优先

旧 theorem 或新 theorem 不具有先验所有权。

### R-009　无 API 冒领

仅用于命名、包装、simp 或重导出的 theorem 若其 observer 可由其他族恢复，则自动为零。

### R-010　辅助证明不拆成 theorem unit

内部 proof support 应优先使用：

- private theorem；
- local have；
- section lemma；
- implementation detail declaration；

只有作为独立数学 concept 对完整族提供正边际时，才进入 public information theorem catalog。

---

## 33. 性能规范

设：

$$
n=|X|,
\qquad
m=|I|.
$$

### 33.1 朴素算法

直接对每个 theorem、每个 pair、每个其他 theorem 比较：

$$
O(m^2n^2).
$$

### 33.2 推荐签名算法

对每个状态 $x$ 计算完整观察签名：

$$
\sigma(x)=(c_i(x))_{i\in I}.
$$

对每个 $i$ 计算留一签名：

$$
\sigma_{-i}(x)=(c_j(x))_{j\neq i}.
$$

可通过 prefix/suffix hash 或结构化 persistent vector 达到约：

$$
O(mn+mn\log n)
$$

的 grouping 成本，而不枚举所有 pair。

### 33.3 fiber 计数公式

完整签名等价类大小为 $a_k$ 时：

$$
|E_I|
=
\sum_k a_k(a_k-1).
$$

对留一签名的 fiber $B$，其中按完整第 $i$ 坐标再分为 $B_v$，则：

$$
|U_i|
=
\sum_B
\left[
|B|(|B|-1)
-
\sum_v |B_v|(|B_v|-1)
\right].
$$

这与有序 pair 定义完全一致。

### 33.4 witness 提取

当 `uniqueCaptureCount > 0` 时，实现应确定性提取字典序最小 witness pair：

```text
(left, right)
```

用于报告和 proof term 压缩，但 witness 选择不得影响 count。

### 33.5 内存

禁止为大状态空间同时物化每个 theorem 的完整 $n^2$ pair 集。应优先存储：

- 状态签名；
- fiber sizes；
- 每 theorem 的留一 grouping；
- 至多一个 canonical witness。

---

## 34. Hash 与确定性

### 34.1 canonical ordering

仅用于 artifact 稳定性的排序键：

1. arena canonical Lean Name encoding；
2. theorem canonical Lean Name encoding；
3. state canonical `Repr` 不得作为数学顺序；
4. state witness 排序必须由 arena 明确提供 `LinearOrder State`，或不输出“最小” witness。

### 34.2 hash 不参与数学

statement SHA、source SHA、artifact SHA 可以用于完整性校验，但不得进入：

$$
K_S,
E_S,
\varepsilon(S),
\delta_i.
$$

### 34.3 重编译确定性

相同 Lean environment 和相同 compiler/toolchain 应产生字节稳定 artifact。

若 artifact 不稳定但 kernel theorem 相同，数学通过状态不应改变；不过工程测试仍应报告非确定性。

---

## 35. 测试矩阵

### T-001　单一非恒等 observer

状态：`Bool`。  
observer：`id`。  
期望：

$$
E_I=\varnothing,
$$

删除 observer 后：

$$
|E^{-i}|=2,
$$

故：

$$
|U_i|=2>0.
$$

### T-002　常值 observer

状态：`Bool`。  
observer：常值。  
期望：

$$
|U_i|=0.
$$

编译失败。

### T-003　两个互补坐标

状态：`Bool × Bool`。  
observer：`Prod.fst`、`Prod.snd`。  
期望：两者均正增益，完整逃逸为零。

### T-004　重复坐标

状态：`Bool × Bool`。  
observer：`Prod.fst` 与 `Bool.not ∘ Prod.fst`。  
两者 kernel 相同。  
期望：两者同时零边际，collision class，编译失败。

### T-005　product 包装过完备

observer：`Prod.fst`、`Prod.snd`、`id`。  
`id` 可恢复两个坐标；两个坐标也可由 `id` 恢复。  
期望：当前三元素族过完备，多成员零边际，编译失败。

### T-006　只保留 product

observer：`id : Bool × Bool → Bool × Bool`。  
期望：正增益，通过。

### T-007　只保留两坐标

observer：`Prod.fst`、`Prod.snd`。  
期望：二者正增益，通过。

### T-008　名称变化

重命名 theorem，concept 不变。  
期望：count 与 rate 完全不变。

### T-009　proof 改写

替换 theorem proof，statement 与 observer 不变。  
期望：count 与 rate 完全不变。

### T-010　索引重排

改变导入／声明顺序。  
期望：按 theorem 对齐后的结果相同。

### T-011　输出双射

把 Bool 输出取反。  
期望：kernel 与 rate 不变。

### T-012　多 arena

两个不同 State 类型。  
期望：分别计算，不产生跨 arena 人工加权总分。

### T-013　系统 theorem 自登记

把 `lowersEscape_iff_uniqueCaptureCount_pos` 的数学 concept 登记进其 arena。  
期望：使用相同 leave-one-out 规则，无命名空间豁免。

### T-014　certificate 回流

尝试把 `.__lowers_escape` 登记为 theorem unit。  
期望：IE-C011。

### T-015　artifact 篡改

修改上次 JSON 后重新编译。  
期望：结果完全不受影响，因为编译不读取 JSON。

### T-016　无历史文件

删除全部旧报告。  
期望：当前编译仍完整工作。

### T-017　零状态／单状态 arena

期望：IE-C004。

### T-018　精确分数

检查：

$$
\text{withoutEscapeCount}
=
\text{fullEscapeCount}
+
\text{uniqueCaptureCount}.
$$

### T-019　结构／计数桥

检查 strict kernel inclusion 与 positive count 等价。

### T-020　全 catalog theorem

检查：

```lean
CatalogIrredundant catalog
```

只有在所有 theorem companion proofs 构造成功时成立。

---

## 36. 与现有仓库数学内核的合并原则

### 36.1 必须复用

优先复用已有 canonical declarations：

```text
Concept
conceptJoin
conceptKernel
jointKernel
SemanticClosure
PrimitiveEscape
ProductiveSeparation
defectRelation
residual_join_law
strict_kernel_novelty_criterion
```

### 36.2 identity target 特化

本规范的内生逃逸：

$$
E_S
=
\operatorname{defectRelation}(C_S,\operatorname{id}_X)
$$

应作为已有 target residual 理论的特化证明，而不是复制 `defectRelation`。

### 36.3 StrictKernelNoveltyCriterion 特化

对：

$$
\Gamma=I^{-i},
\qquad
\text{candidate}=c_i,
$$

现有严格核准则直接给出：

$$
K_I\subsetneq K_{I^{-i}}
\Longleftrightarrow
c_i\notin\operatorname{SemanticClosure}(I^{-i}).
$$

新模块只需补齐：

- identity target；
- off-diagonal finite counting；
- leave-one-out；
- exact rate；
- aggregate compiler command。

### 36.4 Inspector 复用边界

当前 Lean inspector 的 environment 枚举、declaration kind、依赖及 axiom closure 代码可以复用。

但：

- 数学 rate 必须由 Lean 定义计算；
- accept/reject 必须由 Lean proof 决定；
- `.NET` compactor 不得参与；
- C# duplicate advisory 不再是研究非平凡性的真源。

---

## 37. 迁移规范

### Phase 1　纯数学核心

新增：

```text
JointKernel
IntrinsicEscape
LeaveOneOut
UniqueCapture
EscapeRate
Irredundancy
```

并证明 IE-001 至 IE-017。

### Phase 2　有限执行层

实现：

```text
offDiagonalPairs
escapePairs
uniqueCapturePairs
uniqueCaptureCount
escapeRate
```

建立 Set／Finset 桥。

### Phase 3　theorem unit

实现：

```text
Arena
PackedObserver
TheoremUnit
Catalog
```

加入 Bool 测试模型。

### Phase 4　registry

实现 persistent environment extension 与：

```lean
information_theorem
register_information_theorem
```

### Phase 5　单次 seal

实现：

```lean
#seal_information_theory
```

禁止任何 generated source second pass。

### Phase 6　伴随 theorem

为每个 theorem 生成：

```text
.__lowers_escape
.__escape_enriched
```

### Phase 7　artifact

仅在全部 proof 被 environment 接受后发射 JSON／CSV／DOT。

### Phase 8　仓库接入

先选一个有限 arena 目录试点；稳定后扩展到更多 concept families。

---

## 38. 明确删除旧设计

实现与文档中必须删除或弃用以下概念：

```text
AnalysisDomain.target
ResearchProblem
ResearchReceipt as semantic root
parentCatalog
baselineCatalog
CatalogSnapshot as next-run input
previousAccepted
epoch comparison
candidate commit
minimum captured weight
manual triage value
cost-adjusted priority
Shapley allocation
historical delta gate
Stage A generated source
Stage B recompilation
```

允许保留 `Catalog` 一词，但其含义必须是：

> 当前单次编译中完整 theorem unit 有限族。

不得表示历史快照。

---

## 39. 完成定义

工程实现只有同时满足以下条件才算完成。

### AC-001　单命令

一条 `lake build` 完成全部数学检查和报告。

### AC-002　零外部判官

删除 C#／Python accept/reject 路径后，结果不变。

### AC-003　零历史输入

删除旧 JSON、旧 cache、旧 snapshot、Git metadata 后，结果不变。

### AC-004　全精确

所有 rate 以 `Nat`／`Rat` 表示。

### AC-005　kernel proof

每个 accepted theorem 都有：

```lean
original.__lowers_escape
```

以及：

```lean
original.__escape_enriched
```

### AC-006　不可约总 theorem

root environment 中存在一个内部 theorem：

```lean
compiledCatalog_irredundant : CatalogIrredundant compiledCatalog
```

该 theorem 可由所有 companion proofs组装，也可由一次有限决定直接证明。

### AC-007　零边际失败

插入常值、重复、可恢复或 wrapper observer 时编译必失败。

### AC-008　次序不变

交换 module import 和 theorem 登记顺序不改变结果。

### AC-009　系统自应用

至少一个系统核心 theorem unit 通过同一 registry 和同一 leave-one-out 公式被分析。

### AC-010　artifact 单向

artifact 可删除、可重建、不可回写判词。

---

# 第三部　最小 Lean 参考骨架

以下代码是实现骨架，需按仓库实际 universe、namespace 与已存在定义调整。

```lean
universe u v w

namespace D5.S3.InformationEscape

structure Arena where
  State : Type u
  stateFintype : Fintype State
  stateDecidableEq : DecidableEq State
  stateNontrivial : 2 ≤ @Fintype.card State stateFintype

structure PackedObserver (arena : Arena) where
  Output : Type v
  outputDecidableEq : DecidableEq Output
  observe : arena.State → Output

structure TheoremUnit (arena : Arena) where
  observer : PackedObserver arena
  Statement : Prop
  proof : Statement

structure Catalog (arena : Arena) where
  Index : Type w
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  theoremAt : Index → TheoremUnit arena

namespace PackedObserver

variable {arena : Arena}

/-- Executable equality of the outputs produced by one observer. -/
def agrees (observer : PackedObserver arena)
    (left right : arena.State) : Bool := by
  letI := observer.outputDecidableEq
  exact decide (observer.observe left = observer.observe right)

end PackedObserver

namespace Catalog

variable {arena : Arena} (catalog : Catalog arena)

def fullIndexSet : Finset catalog.Index := by
  letI := catalog.indexFintype
  exact Finset.univ

def without (index : catalog.Index) : Finset catalog.Index := by
  letI := catalog.indexDecidableEq
  exact (fullIndexSet catalog).erase index

def offDiagonalPairs : Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact Finset.univ.filter fun pair => pair.1 ≠ pair.2

/-- Executable conjunction of all selected observer equalities. -/
def indistinguishableB
    (selected : Finset catalog.Index)
    (left right : arena.State) : Bool :=
  selected.toList.all fun index =>
    (catalog.theoremAt index).observer.agrees left right

/-- Proposition reflected by `indistinguishableB`. -/
def indistinguishable
    (selected : Finset catalog.Index)
    (left right : arena.State) : Prop :=
  indistinguishableB catalog selected left right = true

def escapePairs
    (selected : Finset catalog.Index) :
    Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact (offDiagonalPairs catalog).filter fun pair =>
    indistinguishableB catalog selected pair.1 pair.2 = true

def uniqueCapturePairs
    (index : catalog.Index) :
    Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact (escapePairs catalog (without catalog index)).filter fun pair =>
    (catalog.theoremAt index).observer.agrees pair.1 pair.2 = false

def escapeDenominator : Nat :=
  (offDiagonalPairs catalog).card

def escapeNumerator
    (selected : Finset catalog.Index) : Nat :=
  (escapePairs catalog selected).card

def uniqueCaptureCount
    (index : catalog.Index) : Nat :=
  (uniqueCapturePairs catalog index).card

def escapeRate
    (selected : Finset catalog.Index) : ℚ :=
  (escapeNumerator catalog selected : ℚ) /
    (escapeDenominator catalog : ℚ)

def theoremGainRate
    (index : catalog.Index) : ℚ :=
  (uniqueCaptureCount catalog index : ℚ) /
    (escapeDenominator catalog : ℚ)

def LowersEscape
    (index : catalog.Index) : Prop :=
  escapeRate catalog (fullIndexSet catalog) <
    escapeRate catalog (without catalog index)

def AugmentedStatement
    (index : catalog.Index) : Prop :=
  (catalog.theoremAt index).Statement ∧
    LowersEscape catalog index

def CatalogIrredundant : Prop :=
  ∀ index, LowersEscape catalog index

end Catalog

end D5.S3.InformationEscape
```

生产实现必须继续证明 `PackedObserver.agrees` 与 Lean 等式、`indistinguishableB` 与量化版联合核之间的 reflection correctness；Bool 计算结果只有经这些 theorem 传回 Prop 后才能用于最终 kernel certificate。

---

# 第四部　最小数学示例

## 40. Bool 单 observer

设：

$$
X=\mathrm{Bool},
$$

$$
c_0=\operatorname{id}.
$$

完整族区分 `false` 与 `true`：

$$
E_I=\varnothing.
$$

删除唯一 theorem 后，没有任何观察坐标：

$$
E_{I^{-0}}
=
\{(false,true),(true,false)\}.
$$

故：

$$
|U_0|=2,
$$

$$
\delta_0=1.
$$

增强 theorem 成立。

## 41. Bool 常值 observer

设：

$$
c_0(x)=false.
$$

完整族与空族具有同一核：

$$
K_I=K_{I^{-0}}=X^2.
$$

故：

$$
|U_0|=0,
$$

编译失败。

## 42. Bool pair 的不可约坐标基

设：

$$
X=\mathrm{Bool}\times\mathrm{Bool},
$$

$$
c_0=\operatorname{fst},
\qquad
c_1=\operatorname{snd}.
$$

完整族联合读出等于 identity，因此：

$$
E_I=\varnothing.
$$

删除 `fst` 后，具有相同 `snd` 的不同 pair 逃逸；删除 `snd` 后同理。因此：

$$
\delta_0>0,
\qquad
\delta_1>0.
$$

该族通过。

## 43. 加入 identity 后的过完备族

再加入：

$$
c_2=\operatorname{id}.
$$

则：

- 删除 `id`，`fst` 与 `snd` 仍联合完全区分；
- 删除 `fst`，`id` 仍完全区分；
- 删除 `snd`，`id` 仍完全区分。

故：

$$
\delta_0=\delta_1=\delta_2=0.
$$

系统拒绝整个过完备族。

开发者必须选择：

$$
\{\operatorname{id}\}
$$

或：

$$
\{\operatorname{fst},\operatorname{snd}\}.
$$

两者都是合法不可约基，系统不引入审美规则选择其一。

---

# 第五部　最终规范句

## 44. 唯一数学判词

对当前一次编译形成的完整定理族 $\mathcal T$，每个定理 $\tau_i$ 的数学价值命题是：

$$
\boxed{
\varepsilon(\mathcal T)
<
\varepsilon(\mathcal T\setminus\{\tau_i\})
}
$$

这不是历史增量，而是当前族内部的留一反事实。

## 45. 唯一准入条件

$$
\boxed{
\forall i,
\quad
\varepsilon(\mathcal T)
<
\varepsilon(\mathcal T\setminus\{\tau_i\})
}
$$

等价地：

$$
\boxed{
\forall i,
\quad
c_i\notin
\operatorname{SemanticClosure}
(\mathcal T\setminus\{\tau_i\})
}
$$

等价地：

$$
\boxed{
\forall i,
\quad
\exists x,y,
\left(\forall j\neq i,\ c_j(x)=c_j(y)\right)
\land
c_i(x)\neq c_i(y)
}
$$

## 46. 唯一实现闭环

```text
current Lean theorem units
        ↓
current full theorem catalog
        ↓
leave-one-out kernels
        ↓
exact information escape rates
        ↓
Lean proofs of strict decrease
        ↓
augmented companion theorems
        ↓
one compilation succeeds or fails
        ↓
read-only artifacts
```

## 47. 本体结论

该系统不是一个附着在数学之外的评价平台。

它只做一件事：

> 对当前 Lean 数学定理族中的每一个 theorem，构造并证明另一个 Lean 数学命题：若从同一个完整定理族中删除该 theorem，则联合概念核严格变粗，信息逃逸率严格上升。

因此接纳对象为：

$$
\boxed{
\widehat\tau_i
:
P_i
\land
\left[
\varepsilon(\mathcal T)
<
\varepsilon(\mathcal T\setminus\{\tau_i\})
\right]
}
$$

整个系统、系统定理、被分析定理、逃逸率、严格下降证明与最终封印都位于 Lean 4 中。

没有 baseline。

没有人工评分。

没有可调评价体系。

没有外部判官。

只有当前数学定理族自身的不可区分核，以及删除任一 theorem 后该核是否严格增大。

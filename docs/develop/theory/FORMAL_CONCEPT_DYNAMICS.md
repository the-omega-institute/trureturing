# 形式概念动力学与构造性界面—余量哲学
## 相对同一性、下降缺陷、因果完成、观察者、规范与辩证修复
### Formal Concept Dynamics and Constructive Interface–Remainder Philosophy

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-19

> **文档地位。** 本文是 `docs/develop/theory` 中的单一、自包含哲学理论稿与后续形式化摄入源，不是 Lean 数学真源。仓库既有结论以相应 Lean 声明为准；本文新增定义、定理和证明在获得 proof term、依赖闭包、仓库 admission 与冻结收据以前不得标记为 `Closed`。
>
> **单卷约束。** 本理论的概念内核、本体论、认识论、因果论、时间论、心灵哲学、行动论、伦理学、社会哲学、语言哲学、科学哲学、数学哲学、美学、宗教哲学、辩证法、有限模型、Lean 路线及严格非主张全部保存在本文件中。后续修正采用追加式勘误、扩展或替代定理，不回写删除既有段落。
>
> **基础约束。** 本文把 C-IRPT 作为构造性底层语言，但不把 CUT、FLOW、ADMIT、ANCHOR 宣称为逻辑原语，也不声称仅凭定义可证明对象存在、世界实现、意识涌现、规范真理或任何开放数学问题。
>
> **解释约束。** 对柏拉图、亚里士多德、笛卡尔、斯宾诺莎、莱布尼茨、休谟、康德、黑格尔、胡塞尔、维特根斯坦、尼采、福柯、罗尔斯等传统的对应均是可审计的结构重构，不是对其全部文本的历史同一性断言。
>
> **机械范围。** 本文只新增一个 Markdown 文件，不删改既有理论文件，不新增 Lean 源码、workflow、临时载荷或并行附录。

---

## 摘要

本文建立一套可定义、可反驳、可比较、可逐步形式化的统一哲学理论。其基本对象不是孤立命题，而是一个由状态类型、概念界面、过程、准入谓词和实际锚点组成的哲学模型：

\[
\mathfrak M
=
(X,\operatorname{Adm},a,\mathcal F,\mathcal C).
\]

一个概念不是单纯谓词，而是分类映射：

\[
C=(B_C,q_C),
\qquad
q_C:X\to B_C.
\]

它规定相对同一性：

\[
x\sim_Cy
\iff
q_C(x)=q_C(y),
\]

并留下依赖余纤维：

\[
R_C(b)
=
\sum_{x:X}(q_C(x)=b).
\]

由此得到规范分解：

\[
X
\simeq
\sum_{b:B_C}R_C(b).
\]

概念精化由映射因子化定义；联合概念是共同精化；有效概念同构类与等价关系格反序对应。给定过程 \(F:X\to Y\)，若存在宏观过程 \(\overline F\) 使

\[
q_DF=\overline Fq_C,
\]

则过程从当前概念下降到未来概念。若当前同类状态经过过程后产生不同未来读出，则得到 causal carry：

\[
\operatorname{Carry}(F;C,D)
=
\sum_{x,y:X}
(q_Cx=q_Cy)
\times
(q_DFx\ne q_DFy).
\]

精确下降排除 carry；反之在有限可判定模型中，无 carry 可用于构造有效像上的下降。概念理论的发展因此不是修辞替换，而是：

\[
\boxed{
\text{提出概念}
\to
\text{计算余纤维}
\to
\text{构造缺陷见证}
\to
\text{形成最小精化}
\to
\text{证明普适性质}.
}
\]

本文进一步把本质定义为相对于目标行为的最小充分概念，把知识定义为真命题在证据余纤维上的稳定，把 Gettier 情形定义为锚点真理和辩护存在但证据纤维仍含反例，把休谟归纳问题定位为有限历史不能无前件下降到未来，把实体定义为过程族下的不变量概念，把偶性变化定义为身份概念保持而性质概念改变，把自由区分为可选性、内部控制、理由响应和分支非唯一性，把责任定义为规范评价向控制—知识概念的下降，把道德运气定义为该下降的失败，把正义定义为制度对道德无关差异的不变性，把意识形态定义为内部自然但对相关现实不忠实的分类系统，把承认定义为多观察者描述在共同实现像中的兼容，把辩证法定义为由显式缺陷强制出的最小概念完成。

全文严格区分：

\[
\boxed{
\text{定义}
\ne
\text{存在}
\ne
\text{合法}
\ne
\text{实现}
\ne
\text{真理}
\ne
\text{知识}.
}
\]

该框架的目标不是以一个数学词典取代哲学，而是建立一门能够证明概念间关系、生成有限反模型、隔离隐藏前件、比较历史体系并接受 Lean kernel 审计的形式概念动力学。

---

# 1. 仓库锚点与理论边界

本文复用但不冒充已经完全形式化的仓库结构包括：

- `D5/S0/Diagonal/EscapeCount.lean`：有限自应用列表、twisted diagonal 与精确逃逸计数；
- `D5/S3/ObserverMemory/FiniteReadoutKernel.lean`：线性读出按核取商后与可达像的线性等价；
- `D5/S3/ObserverMemory/Prediction/ItineraryCompletion.lean`：未来读出 itinerary 与预测商；
- `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean`：行为商的普适性质；
- `D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality.lean`：局部距离证书、预测完成、状态数最小性与验证复杂度；
- `D5/S3/Observer/MetricGeometry/WindowObserverDistance.lean`：有限窗口上的观察者距离；
- `D5/S3/Quantum/GNSMatrix.lean`、`D5/S3/QuantumStates/GNSStateCone.lean` 与相关正锥文件：状态、正性与 GNS 模型的既有锚点；
- `docs/develop/theory/QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md`：投影、商余、完成、观察者、对角化与 C-IRPT 的单卷纸面发展。

本文不声称这些文件已经蕴含全部哲学结论。准确关系是：

\[
\boxed{
\text{仓库既有形式定理}
+
\text{本文新增定义与纸面证明}
+
\text{未来 Lean 依赖闭包}
}
\]

共同构成形式哲学路线。

本文的第一条方法论禁令为：

\[
\boxed{
\text{不得因为一个哲学概念可被定义，
便宣称其指称对象已被构造。}
}
\]

第二条禁令为：

\[
\boxed{
\text{不得因为一个模型内部闭合，
便宣称它忠实、现实或规范正当。}
}
\]

第三条禁令为：

\[
\boxed{
\text{不得把历史哲学解释当作数学等价，
也不得把数学重构当作文本事实。}
}
\]

---

# Part I：基础层与无暗账纪律

# 2. 冻结基础与保守定义扩张

设基础语言为 \(\mathcal L_0\)，基础理论为 \(T_0\)。本文加入的概念语言记为：

\[
\mathcal L_{\Phi}
\supseteq
\mathcal L_0.
\]

## 定义 2.1（定义展开）

定义翻译：

\[
(-)^\flat:
\mathcal L_{\Phi}
\to
\mathcal L_0
\]

递归展开所有新符号。

## 定义 2.2（无领域公理）

若 \(\Phi\)-理论只加入可展开定义，而不加入关于特定哲学对象存在或必然满足某性质的新公理，则称其相对于 \(T_0\) 无领域公理。

## 定理 2.1（定义性保守性）

对任何旧语言命题 \(\varphi\in\mathcal L_0\)，若：

\[
T_{\Phi}\vdash\varphi,
\]

且 \(T_{\Phi}\) 仅为定义扩张，则：

\[
T_0\vdash\varphi.
\]

### 证明

展开推导中所有新增定义。展开后的证明完全位于旧语言和旧推理规则中。故新增术语不能仅凭命名产生旧语言中的新无条件定理。\(\square\)

因此，形式哲学的价值只能来自：

1. 新的普适性质；
2. 更精确的前件分离；
3. 新的模型转移；
4. 新的有限反例；
5. 新的缺陷分解；
6. 新的构造与最小性；
7. 对传统争论的型别诊断；
8. 可由 Lean kernel 审计的证明链。

---

# 3. 六层存在纪律

对类型 \(X\)、谓词 \(A:X\to\mathsf{Prop}\) 和概念 \(C:X\to B\)，必须区分：

\[
\begin{aligned}
E_0(X)
&:\quad X\text{ 可形成};\\
E_1(X)
&:\quad \|X\|;\\
E_2(X,A)
&:\quad \left\|\sum_{x:X}A(x)\right\|;\\
E_3(X,A)
&:\quad a:\sum_{x:X}A(x);\\
E_4(C,b,A)
&:\quad \left\|\sum_{x:X}A(x)\times(Cx=b)\right\|;\\
E_5(F,a,A)
&:\quad \forall n,\ A(F^na).
\end{aligned}
\]

它们分别表示：

\[
\text{可定义、非空、合法可实现、实际锚定、可显现、持续存在}.
\]

一般没有无条件蕴涵：

\[
E_0\Rightarrow E_1,
\qquad
E_1\Rightarrow E_2,
\qquad
E_2\Rightarrow E_3.
\]

命题截断中的非空性也不自动给出可计算见证。

## 原理 3.1（存在见证纪律）

任何“存在某对象”主张必须明确给出以下之一：

- 一个构造项；
- 一个非空证明；
- 一个经典存在证明及其使用的原则；
- 一个模型中的实际锚点；
- 一个现实实现桥梁。

定义 `Soul`、`FreeAgent`、`JustWorld`、`NecessaryBeing`、`ConsciousState` 或 `ObjectiveValue` 只构造候选类型，不证明其中有项。

---

# 4. 哲学模型的最小结构

## 定义 4.1（原始哲学模型）

一个原始模型包括：

\[
\boxed{
\mathfrak M_{\mathrm{raw}}
=
(X,\operatorname{Adm},a,U,F,O,\mathcal C).
}
\]

其中：

\[
\begin{aligned}
X&:\mathsf{Type} &&\text{状态或世界类型},\\
\operatorname{Adm}&:X\to\mathsf{Prop} &&\text{准入谓词},\\
a&:\sum_{x:X}\operatorname{Adm}(x) &&\text{实际锚点},\\
U&:\mathsf{Type} &&\text{行动／过程索引},\\
F&:U\to X\to X &&\text{过程族},\\
O&:\mathsf{Type} &&\text{观察者类型},\\
\mathcal C&:O\to\operatorname{Concept}(X) &&\text{观察者概念族}.
\end{aligned}
\]

## 定义 4.2（合法性）

`IsLawful` 是附着于原始模型的性质，而不是模型定义中隐藏的全局公理。它可包含：

- FLOW 保持准入；
- 概念读出良定义；
- 过程组合律；
- 观察者相容性；
- 概率归一化；
- 正性；
- 可计算性；
- 连续性；
- 领域特定守恒律。

## 原理 4.1（Raw／Lawful 分离）

必须分开：

\[
\texttt{RawModel}
\qquad\text{与}\qquad
\texttt{IsLawful RawModel}.
\]

不得添加：

```lean
axiom everyRawModel_isLawful : ∀ M, IsLawful M
```

而应对每个具体模型给出证明。

---

# Part II：概念内核

# 5. 概念不是词，而是分类界面

## 定义 5.1（概念）

对状态类型 \(X\)，一个概念是：

\[
\boxed{
C=(B_C,q_C),
\qquad
q_C:X\to B_C.
}
\]

其中 \(B_C\) 为概念值类型，\(q_C\) 为读出。

命题概念是 \(B_C=\mathsf{Prop}\) 的特殊情况；数值概念、颜色概念、法律身份、社会角色、证据状态、未来行为、现象结构与价值等级通常是多值概念。

## 定义 5.2（有效概念）

概念的有效值空间为：

\[
\operatorname{Im}(q_C)
=
\sum_{b:B_C}\|R_C(b)\|.
\]

若只研究实际出现的分类，可以把 \(B_C\) 缩减到该像。原始 codomain 中没有实现的标签不应被误报为现实类别。

## 定义 5.3（相对同一性）

\[
\boxed{
x\sim_Cy
\iff
q_C(x)=q_C(y).
}
\]

必须区分：

\[
\begin{aligned}
x=y
&:\text{恒等类型中的同一};\\
x\sim_Cy
&:\text{概念相对同一};\\
x\simeq y
&:\text{结构等价};\\
x\sim_{\mathrm{orbit}}y
&:\text{过程轨道等价};\\
x\equiv_{\mathrm{law}}y
&:\text{法律或制度同一}.
\end{aligned}
\]

哲学争论中的“同一个”必须标明是哪一种关系。

---

# 6. 依赖余纤维与规范分解

## 定义 6.1（概念余纤维）

对 \(b:B_C\)：

\[
\boxed{
R_C(b)
=
\sum_{x:X}(q_Cx=b).
}
\]

加入准入：

\[
\boxed{
R_C^{\operatorname{Adm}}(b)
=
\sum_{x:X}
\operatorname{Adm}(x)
\times
(q_Cx=b).
}
\]

余纤维不是“缺失信息”的模糊隐喻，而是概念值固定以后仍可变化的完整依赖类型。

## 定理 6.1（规范概念—余量分解）

对任意 \(q_C:X\to B_C\)：

\[
\boxed{
X
\simeq
\sum_{b:B_C}R_C(b).
}
\]

### 构造

正向：

\[
x\mapsto(q_Cx,x,\operatorname{refl}_{q_Cx}).
\]

反向：

\[
(b,x,h)\mapsto x.
\]

一个方向定义性成立，另一个方向由路径归纳成立。\(\square\)

同理：

\[
\boxed{
\sum_{x:X}\operatorname{Adm}(x)
\simeq
\sum_{b:B_C}R_C^{\operatorname{Adm}}(b).
}
\]

## 推论 6.2（形式—余量双层）

任何概念都把对象写成：

\[
\boxed{
\text{可表达坐标}
+
\text{该坐标下的依赖余量}.
}
\]

但不能未经证明写成：

\[
X\simeq B_C\times R.
\]

统一余量类型、连续平凡化或全局代表选择均是额外结构。

---

# 7. 概念精化与决定关系

## 定义 7.1（精化）

概念 \(D\) 精化 \(C\)，记为：

\[
C\preceq D,
\]

当且仅当存在：

\[
p:B_D\to B_C
\]

和逐点等式：

\[
q_C=p\circ q_D.
\]

这意味着知道 \(D\) 即可计算 \(C\)。

## 定理 7.1（精化缩小不可区分性）

若 \(C\preceq D\)，则：

\[
\boxed{
x\sim_Dy
\Longrightarrow
x\sim_Cy.}
\]

### 证明

对 \(q_Dx=q_Dy\) 应用 \(p\)，再使用因子化等式。\(\square\)

## 定理 7.2（精化复合）

若：

\[
C\preceq D,
\qquad
D\preceq E,
\]

则：

\[
C\preceq E.
\]

恒等映射给出自反性。因此概念连同精化数据形成因子化范畴；在忽略具体因子映射并按概念等价取商后形成预序。

## 定义 7.2（概念等价）

\[
\boxed{
C\simeq_{\mathrm{con}}D
\iff
C\preceq D
\land
D\preceq C.
}
\]

它表示相同的区分能力，不要求相同名称、相同标签或相同 codomain。

---

# 8. 联合概念、共同粗化与概念格

## 定义 8.1（联合概念）

\[
\boxed{
C\vee D
=
(B_C\times B_D,
 x\mapsto(q_Cx,q_Dx)).
}
\]

于是：

\[
x\sim_{C\vee D}y
\iff
x\sim_Cy
\land
x\sim_Dy.
\]

## 定理 8.1（联合概念的普适性质）

有：

\[
C\preceq C\vee D,
\qquad
D\preceq C\vee D.
\]

若 \(C\preceq E\) 且 \(D\preceq E\)，则：

\[
\boxed{C\vee D\preceq E.}
\]

### 证明

从 \(E\) 的值分别计算 \(C,D\)，再配对即可。\(\square\)

## 定义 8.2（极端概念）

最粗概念：

\[
\bot_X=(\mathbf1,!).
\]

最细概念：

\[
\top_X=(X,\operatorname{id}_X).
\]

对所有 \(C\)：

\[
\bot_X\preceq C\preceq\top_X.
\]

## 定义 8.3（共同粗化）

在具有有效 quotient 的基础中，令：

\[
\ker C=\{(x,y)\mid x\sim_Cy\}.
\]

\(C,D\) 的最细共同粗化对应于包含 \(\ker C\cup\ker D\) 的最小等价关系，即其等价闭包。取相应 quotient 得到 \(C\wedge D\)。

## 定理 8.2（概念格—等价关系格反序）

在有效 quotient、函数外延与适当等价商下：

\[
\boxed{
\operatorname{Con}(X)/\simeq_{\mathrm{con}}
\cong
\operatorname{EqRel}(X)^{\mathrm{op}}.
}
\]

概念越精细，核等价关系越小。联合概念对应等价关系交；共同粗化对应等价闭包后的并。

该定理把“概念关系”从词语相似度提升为一个可计算的偏序结构。

---

# 9. 定义性、蕴涵与概念决定必须分开

给定命题 \(P,Q:X\to\mathsf{Prop}\)。

## 定义 9.1（逻辑蕴涵）

\[
P\models_{\operatorname{Adm}}Q
\iff
\forall x,\operatorname{Adm}(x)\to P(x)\to Q(x).
\]

## 定义 9.2（概念决定）

命题 \(P\) 可由概念 \(C\) 决定，当：

\[
\boxed{
P\preceq C,
}
\]

即存在：

\[
\overline P:B_C\to\mathsf{Prop}
\]

使：

\[
P=\overline P\circ q_C.
\]

## 定义 9.3（锚点真）

\[
\operatorname{True}_a(P)
\iff
P(a).
\]

逻辑蕴涵、概念决定和锚点真理属于不同类型的关系。

例如：

- \(P\models Q\) 不表示知道 \(P\) 的概念值足以计算 \(Q\)；
- \(Q\preceq C\) 不表示 \(Q(a)\) 为真；
- \(Q(a)\) 为真不表示观察者能从证据判定 \(Q\)。

---

# 10. 忠实性、自然性与完整性

## 定义 10.1（忠实概念）

概念 \(C\) 对状态类型忠实，当 \(q_C\) 单射：

\[
q_Cx=q_Cy
\Longrightarrow
x=y.
\]

## 定义 10.2（对目标忠实）

对目标 \(K:X\to Y\)，概念 \(C\) 对 \(K\) 忠实，当：

\[
K\preceq C.
\]

即 \(C\) 不删除会改变 \(K\) 的差异。

## 定义 10.3（自然性）

给定过程 \(F\) 与概念 \(C,D\)，自然性表示存在交换方格：

\[
q_DF=\overline Fq_C.
\]

自然性不等于忠实性。最粗概念 \(\bot_X\) 对任何过程都可产生平凡闭合，但删除全部状态差异。

## 命题 10.1（盲自然性）

存在概念 \(C\) 和过程 \(F\)，使宏观方格严格交换，但 \(C\) 对相关目标 \(K\) 不忠实。

### 最小构造

取 \(C=\bot_X\)。则任意 \(F:X\to X\) 都下降到单点自映射。但只要 \(K\) 非常值，就没有 \(K\preceq C\)。\(\square\)

因此，制度、理论或观察模型的内部一致性不能替代其对相关现实的分辨能力。

---

# 11. 概念兼容与联合实现

## 定义 11.1（兼容像）

对概念 \(C,D\) 与准入谓词：

\[
\boxed{
\operatorname{Compat}_{\operatorname{Adm}}(C,D)
=
\left\{
(c,d)\mid
\exists x,
\operatorname{Adm}(x)
\land q_Cx=c
\land q_Dx=d
\right\}.
}
\]

一般只有：

\[
\operatorname{Compat}_{\operatorname{Adm}}(C,D)
\subseteq
\operatorname{Im}_{\operatorname{Adm}}(C)
\times
\operatorname{Im}_{\operatorname{Adm}}(D).
\]

## 定义 11.2（实现独立）

若上式为等号，则称 \(C,D\) 在准入模型中实现独立。

实现独立不是概率独立。前者只说明每一对允许值都能共同实现；后者还依赖概率分布。

## 定义 11.3（兼容亏损）

在有限非空模型中：

\[
\boxed{
\chi_{\mathrm{comp}}(C,D)
=
\log
\frac{
|\operatorname{Im}(C)|
|\operatorname{Im}(D)|
}{
|\operatorname{Compat}(C,D)|
}
\ge0.
}
\]

它衡量分别合法的概念状态中有多少组合不能共同属于同一个世界。

---

# Part III：过程、下降、carry 与完成

# 12. FLOW 与宏观下降

## 定义 12.1（过程）

一个过程是有类型映射：

\[
F:X\to Y.
\]

它不预设可逆、连续、线性、正、局部、因果、可计算或保测度；这些均为附加性质。

## 定义 12.2（精确下降）

给定概念：

\[
C=(B_C,q_C)\text{ on }X,
\qquad
D=(B_D,q_D)\text{ on }Y,
\]

过程 \(F\) 从 \(C\) 下降到 \(D\)，当存在：

\[
\overline F:B_C\to B_D
\]

使：

\[
\boxed{
q_DF=\overline Fq_C.
}
\]

这表示宏观未来完全由当前概念值决定。

## 定理 12.1（有效像上的唯一性）

若 \(q_C\) 满射，则下降映射 \(\overline F\) 唯一。

若不满射，则它只在 \(\operatorname{Im}(q_C)\) 上由 \(F\) 唯一决定；像外的值需要附加定义。

### 证明

对任意 \(b\) 选取或由满射见证得到 \(x\) 使 \(q_Cx=b\)，则：

\[
\overline F(b)=q_D(Fx).
\]

若只在像上工作，不需全局选择。\(\square\)

---

# 13. causal carry

## 定义 13.1（carry 见证）

\[
\boxed{
\operatorname{Carry}(F;C,D)
=
\sum_{x,y:X}
(q_Cx=q_Cy)
\times
(q_DFx\ne q_DFy).
}
\]

它表达：

\[
\boxed{
\text{当前概念删除的差异，
经过过程后成为未来概念可见的差异。}
}
\]

## 定理 13.1（下降排除 carry）

若存在精确下降，则 carry 类型为空。

### 证明

若 \(q_Cx=q_Cy\)，则：

\[
q_DFx
=
\overline F(q_Cx)
=
\overline F(q_Cy)
=
q_DFy.
\]

与未来不等矛盾。\(\square\)

## 定理 13.2（有限反向判据）

若 \(X,B_C,B_D\) 有限可判定，\(q_C\) 取有效像，且 carry 为空，则存在唯一有效像下降：

\[
\overline F:\operatorname{Im}(q_C)\to B_D.
\]

### 构造

对每个实现值选择有限枚举中的首个代表；无 carry 保证结果与代表无关。有限性和可判定性承担代表提取。\(\square\)

在一般构造性无限模型中，不能从“没有反例”无条件提取一个全局函数。

---

# 14. 定量下降缺陷

若 \(B_D\) 上有伪度量 \(d_D\)，对候选 \(\overline F\) 定义：

\[
\boxed{
\delta(F;C,D,\overline F)
=
\sup_x
d_D(q_DFx,\overline Fq_Cx).
}
\]

在加性模型中定义：

\[
\epsilon_F
=
q_DF-\overline Fq_C.
\]

## 定理 14.1（组合链式律）

对：

\[
X\xrightarrow{F}Y\xrightarrow{G}Z
\]

及候选宏观映射 \(\overline F,\overline G\)：

\[
\boxed{
\epsilon_{GF}
=
\epsilon_G\circ F
+
\overline G\circ\epsilon_F.
}
\]

### 证明

加上再减去 \(\overline Gq_DF\)：

\[
\begin{aligned}
q_EGF-\overline G\overline Fq_C
&=(q_EG-\overline Gq_D)F
+\overline G(q_DF-\overline Fq_C).
\end{aligned}
\]

\(\square\)

若 \(\overline G\) 为 Lipschitz，则得到次可加缺陷界。哲学误差由此可以沿推理链、制度链或时间链运输，而不只是被笼统称为“偏差”。

---

# 15. 截面、代表、gauge 与概念接缝

## 定义 15.1（截面）

对满射概念 \(q:X\to B\)，截面是：

\[
s:B\to X,
\qquad
qs=\operatorname{id}_B.
\]

截面为每个概念值选择一个代表，但它不是概念本身的定义性数据。

## 原理 15.1（无规范代表）

若不存在规范截面，则不能把每个概念类中的一个对象称为“真正代表”。任何代表选择都携带 gauge。

## 定义 15.2（加法 carry cocycle）

在扩张：

\[
0\to R\to X\xrightarrow qB\to0
\]

及截面 \(s\) 下：

\[
\kappa_s(a,b)
=s(a)+s(b)-s(a+b).
\]

结合律蕴含：

\[
\boxed{
\kappa_s(a,b)+\kappa_s(a+b,c)
=
\kappa_s(b,c)+\kappa_s(a,b+c).
}
\]

若改变截面：

\[
s'(a)=s(a)+\beta(a),
\]

则：

\[
\kappa_{s'}
=
\kappa_s+\delta\beta.
\]

因此局部描述可以改变，而 cocycle 类记录不能由单一代表重命名消除的全局接缝。

哲学上，这区分：

- 观点差异：截面或坐标不同；
- 实质障碍：所有 gauge 下仍非平凡的接缝类；
- 纯语言争执：可由 gauge 变化消除；
- 结构冲突：不能由重命名消除。

---

# 16. 概念完成

给定当前概念 \(C\) 和目标读出 \(K:X\to Y\)。令目标概念为：

\[
E_K=(Y,K).
\]

## 定义 16.1（相对完成）

\[
\boxed{
\operatorname{Comp}_K(C)
=C\vee E_K.
}
\]

即：

\[
x\mapsto(q_Cx,Kx).
\]

## 定理 16.1（最小保守完成）

\(\operatorname{Comp}_K(C)\) 满足：

\[
C\preceq\operatorname{Comp}_K(C),
\qquad
E_K\preceq\operatorname{Comp}_K(C).
\]

若概念 \(D\) 同时满足：

\[
C\preceq D,
\qquad
E_K\preceq D,
\]

则：

\[
\boxed{
\operatorname{Comp}_K(C)\preceq D.
}
\]

所以它是保留旧概念并使目标可决定的最小共同精化。\(\square\)

## 定理 16.2（完成算子律）

对固定 \(K\)，在概念等价意义下：

\[
\begin{aligned}
C&\preceq\operatorname{Comp}_K(C),\\
C\preceq D
&\Longrightarrow
\operatorname{Comp}_K(C)\preceq\operatorname{Comp}_K(D),\\
\operatorname{Comp}_K(
\operatorname{Comp}_K(C))
&\simeq_{\mathrm{con}}
\operatorname{Comp}_K(C).
\end{aligned}
\]

因此相对完成是概念预序上的闭包算子。

---

# 17. 预测完成、本质与记忆

给定离散过程：

\[
F:X\to X
\]

和读出：

\[
q:X\to B.
\]

定义完整未来 itinerary：

\[
\boxed{
K_q(x)(n)=q(F^nx).
}
\]

## 定义 17.1（预测等价）

\[
x\sim_q^\infty y
\iff
\forall n,\ q(F^nx)=q(F^ny).
\]

## 定义 17.2（预测完成）

\[
\boxed{
Z_q=X/{\sim_q^\infty}.
}
\]

## 定理 17.1（预测充分性）

过程 \(F\) 下降为：

\[
\overline F_q:Z_q\to Z_q,
\qquad
\overline F_q([x])=[Fx].
\]

读出也下降到 \(Z_q\)。

### 证明

若 \(x\sim_q^\infty y\)，则对全部 \(n\)：

\[
q(F^nFx)=q(F^{n+1}x)=q(F^{n+1}y)=q(F^nFy).
\]

故 \(Fx\sim_q^\infty Fy\)。\(\square\)

## 定理 17.2（预测最小性）

任何能够同时承载闭合更新和完整未来读出的概念都必须精化 \(Z_q\)。

因此：

\[
\boxed{
\text{相对于未来行为的本质}
=
\text{完整未来的最小充分概念}.
}
\]

## 定义 17.3（记忆扩张）

若当前读出 \(q\) 不闭合，引入：

\[
m:X\to M,
\qquad
q^m(x)=(q(x),m(x)).
\]

使过程下降。

最小记忆问题是在指定复杂度或精化序下寻找最粗的此类 \(q^m\)。

所以：

\[
\boxed{
\text{记忆}
=
\text{为状态化历史 carry 而保留的最小附加坐标}.
}
\]

---

# 18. 观察者塔、形式完成与现实完成

设指标范畴为 \(I\)，每层有 \(X_i\)，层间映射：

\[
p_{ji}:X_j\to X_i.
\]

## 定义 18.1（形式观察者）

\[
\boxed{
\operatorname{Obs}(\mathbf X)
=
\sum_{x:\prod_iX_i}
\prod_{j\succeq i}p_{ji}(x_j)=x_i.
}
\]

它是逆极限 cone 的项类型。

## 定义 18.2（现实观察者）

若每层有准入 \(A_i\)，则：

\[
\boxed{
\operatorname{PhysObs}
=
\sum_{x:\operatorname{Obs}(\mathbf X)}
\prod_iA_i(x_i).
}
\]

## 定义 18.3（形式／现实完成）

\[
\widehat X_{\mathrm{form}}
=
\varprojlim_iX_i,
\]

\[
\widehat X_{\mathrm{real}}
=
\sum_{x:\widehat X_{\mathrm{form}}}
\operatorname{Realizable}(x).
\]

形式相容不推出现实可实现。一个理论可以内部融贯而没有实际模型；一个无穷精度概念可以形式存在，却违反能量、正性、可计算性、normality、可积性或经验准入。

---

# Part IV：真理、知识与归纳

# 19. 真理的分层

给定命题：

\[
P:X\to\mathsf{Prop}.
\]

## 定义 19.1（锚点真理）

\[
\boxed{
\operatorname{True}_a(P)
\iff
P(a).
}
\]

## 定义 19.2（模型有效性）

\[
\boxed{
\mathfrak M\models P
\iff
\forall x,\operatorname{Adm}(x)\to P(x).
}
\]

## 定义 19.3（概念稳定）

\[
\boxed{
\operatorname{Stable}_C(P,a)
\iff
\forall x,
\operatorname{Adm}(x)
\land q_Cx=q_Ca
\to
(P(x)\leftrightarrow P(a)).
}
\]

## 定义 19.4（理论融贯）

理论约束族 \(T\) 融贯，当其模型或相容 section 类型非空。

## 定义 19.5（实用成功）

给定价值准则 \(V\)、策略 \(\pi\) 和阈值 \(\theta\)：

\[
\operatorname{Successful}(T,\pi,a)
\iff
V(F_\pi a)\succeq\theta.
\]

一般不存在：

\[
\operatorname{Coherent}
\Rightarrow
\operatorname{Corresponding}
\Rightarrow
\operatorname{Successful}.
\]

融贯、符合与实用成功是不同谓词。

---

# 20. 知识是证据纤维上的真理稳定

设观察者的证据概念为：

\[
E:X\to B_E.
\]

## 定义 20.1（稳健知识）

\[
\boxed{
\begin{aligned}
\operatorname{Know}_E(P,a)
\iff{}&
\operatorname{Adm}(a)
\land P(a)\\
&\land
\forall x,
\operatorname{Adm}(x)
\land E(x)=E(a)
\to P(x).
\end{aligned}
}
\]

即命题不仅在实际锚点为真，而且在所有与当前证据不可区分的合法状态中都为真。

## 定理 20.1（事实性）

\[
\operatorname{Know}_E(P,a)
\Longrightarrow
P(a).
\]

## 定理 20.2（证据精化单调性）

若：

\[
E\preceq E',
\]

即 \(E'\) 更精细，则：

\[
\boxed{
\operatorname{Know}_E(P,a)
\Longrightarrow
\operatorname{Know}_{E'}(P,a).
}
\]

### 证明

\(E'\)-纤维包含于 \(E\)-纤维；在大纤维上稳定必在子纤维上稳定。\(\square\)

## 定理 20.3（知识合取）

若知道 \(P\) 且知道 \(Q\)，则知道 \(P\land Q\)。

## 定理 20.4（已知蕴涵下的闭包）

若知道 \(P\)，并且：

\[
\forall x\in R_E^{\operatorname{Adm}}(E(a)),
P(x)\to Q(x),
\]

则知道 \(Q\)。

这里必须使用证据纤维内有效的蕴涵，而不是观察者不知道的外部元理论蕴涵。

---

# 21. 信念、辩护与 Gettier 缺陷

定义信念策略：

\[
\beta:B_E\to\mathcal P(\operatorname{Prop}(X)).
\]

\[
\operatorname{Bel}_E(P,a)
\iff
P\in\beta(E(a)).
\]

另给辩护关系：

\[
\operatorname{Just}(E(a),P).
\]

## 定义 21.1（Gettier 见证）

\[
\boxed{
\begin{aligned}
\operatorname{Gettier}(P,a)
\iff{}&
P(a)
\land\operatorname{Bel}_E(P,a)
\land\operatorname{Just}(E(a),P)\\
&\land
\exists x,
\operatorname{Adm}(x)
\land E(x)=E(a)
\land\neg P(x).
\end{aligned}
}
\]

因此：

\[
\boxed{
\text{Gettier 缺陷}
=
\text{锚点真理}
+
\text{信念与辩护}
-
\text{证据纤维稳定性}.
}
\]

## 最小模型 21.1

取：

\[
X=\{w_0,w_1\},
\qquad
E(w_0)=E(w_1)=e.
\]

令：

\[
P(w_0)=\mathsf{True},
\qquad
P(w_1)=\mathsf{False},
\]

实际锚点为 \(w_0\)，并让信念规则与辩护规则在证据 \(e\) 下接受 \(P\)。则得到真且有辩护的信念，但不是稳健知识。

---

# 22. 怀疑主义的四个层级

## 定义 22.1（局部怀疑）

\[
\exists x,
\operatorname{Adm}(x)
\land E(x)=E(a)
\land\neg P(x).
\]

## 定义 22.2（有限历史怀疑）

对每个有限历史概念 \(H_n\)，实际纤维中仍有 \(P\)-反例。

## 定义 22.3（观察极限怀疑）

即使合并全部允许观察，\(P\) 仍不由联合概念决定。

## 定义 22.4（实现怀疑）

存在形式相容完成，但没有可实现锚点：

\[
\widehat X_{\mathrm{form}}\ne\varnothing,
\qquad
\widehat X_{\mathrm{real}}=\varnothing.
\]

局部怀疑只针对当前证据；极限怀疑针对整个允许观察体系；实现怀疑针对形式—现实桥梁。它们不能被同一句“我们永远不知道”替代。

---

# 23. 休谟归纳问题

定义长度 \(n\) 的历史概念：

\[
\boxed{
H_n(x)
=
(q(x),q(Fx),\ldots,q(F^nx)).
}
\]

设未来目标：

\[
K:X\to Y.
\]

## 定理 23.1（归纳充分性判据）

从有限历史 \(H_n\) 唯一决定 \(K\)，当且仅当：

\[
\boxed{K\preceq H_n.}
\]

即存在：

\[
\overline K_n:\operatorname{Im}(H_n)\to Y
\]

使：

\[
K=\overline K_nH_n.
\]

若不存在，则在有限可判定模型中可构造：

\[
H_n(x)=H_n(y),
\qquad
K(x)\ne K(y).
\]

因此过去重复本身不能推出未来重复。归纳推理还需要显式前件，例如：

- 有限状态稳定；
- 平稳性；
- Markov 完成；
- 解析性；
- 因果闭合；
- 复杂度界；
- 生成机制不变性。

休谟问题的形式核心为：

\[
\boxed{
\text{有限过去}
\not\Rightarrow
\text{未来规律};
\qquad
\text{有限过去}
+
\text{下降前件}
\Rightarrow
\text{未来预测}.
}
\]

---

# Part V：本体论与形而上学

# 24. 现象、对象与物自身

对观察概念 \(C\)：

\[
\operatorname{Phen}_C(x)=q_Cx.
\]

对象的完整相对结构位于：

\[
R_C(q_Cx).
\]

## 定义 24.1（现象同一）

\[
x\sim_Cy.
\]

## 定义 24.2（相对本体余量）

同一现象值下的非平凡纤维：

\[
|R_C^{\operatorname{Adm}}(b)|>1.
\]

这只证明相对于概念 \(C\) 有未区分余量，不证明存在一个绝对不可知的神秘实体。

## 定理 24.1（联合忠实性／莱布尼茨判据）

对概念族 \((C_i)_{i\in I}\)，定义：

\[
Q(x)=(q_i(x))_i.
\]

以下等价：

1. \(Q\) 单射；
2. 对所有 \(x,y\)，若对全部 \(i\) 有 \(q_i(x)=q_i(y)\)，则 \(x=y\)；
3. \(\bigcap_i\ker(q_i)=\operatorname{Eq}_X\)。

所以不可分辨者同一原则是概念族联合忠实的条件，而不是脱离概念族的无条件逻辑律。

## 康德式结构模型

若现象概念 \(Q\) 不忠实，且不存在规范全局截面：

\[
s:\operatorname{Im}(Q)\to X,
\qquad
Qs=\operatorname{id},
\]

则不能从每种现象规范选择一个独立于观察方式的对象代表。

若纤维还不能统一平凡化，则“物自身余量”不是一个固定隐藏变量，而是一族依赖于现象值并由局部接缝拼合的纤维。

---

# 25. 形式与质料

由：

\[
X\simeq\sum_{b:B_C}R_C(b)
\]

得到一个结构化重构：

\[
\boxed{
\begin{aligned}
b&=\text{形式坐标};\\
R_C(b)&=\text{实现该形式的依赖质料空间}.
\end{aligned}
}
\]

质料不是完全脱离形式的统一裸底物；不同形式值下的纤维可以具有不同大小、拓扑、代数结构或准入条件。

## 定义 25.1（形式充分）

若目标行为 \(K\) 通过形式概念 \(C\) 因子化，则该形式对 \(K\) 充分。

## 定义 25.2（质料相关）

若存在同一形式类中的两个实现产生不同目标：

\[
q_Cx=q_Cy,
\qquad
Kx\ne Ky,
\]

则被形式删除的质料差异对目标仍相关。

因此形式与质料不是两个独立实体词，而是相对于所选分类和目标行为的双层结构。

---

# 26. 实体、偶性与变化

设 \(S:X\to B_S\) 为身份概念，\(A:X\to B_A\) 为性质概念。

## 定义 26.1（过程相对实体）

若对过程族 \(\mathcal F\)：

\[
\forall F\in\mathcal F,\forall x,
\quad
S(Fx)=S(x),
\]

则 \(S\) 是该过程族下的实体身份概念。

## 定义 26.2（偶性变化）

\[
\boxed{
\operatorname{AccidentalChange}_{S,A,F}(x)
\iff
S(Fx)=S(x)
\land
A(Fx)\ne A(x).
}
\]

## 定义 26.3（实质变化）

\[
\boxed{
\operatorname{SubstantialChange}_{S,F}(x)
\iff
S(Fx)\ne S(x).
}
\]

“同一个对象发生变化”因此不是矛盾，而是一个概念保持、另一个概念改变。

## 定义 26.4（实体强度）

若身份概念在更多过程下保持不变，则其过程相对稳定性更强。但过粗概念也可能平凡不变，因此实体候选还应对相关行为忠实。

合理实体概念需要同时满足：

\[
\boxed{
\text{过程稳定}
+
\text{目标忠实}
+
\text{非平凡分辨率}.
}
\]

---

# 27. 潜能、现实与五类模态

## 定义 27.1（现实）

\[
\operatorname{Actual}(P,a)
\iff
P(a).
\]

## 定义 27.2（领域可能）

\[
\Diamond_{\operatorname{Adm}}P
\iff
\exists x,\operatorname{Adm}(x)\land P(x).
\]

## 定义 27.3（动力可达）

\[
\Diamond_F^aP
\iff
\exists u,n,
\operatorname{Adm}(F_u^na)
\land P(F_u^na).
\]

## 定义 27.4（主体能力）

\[
\operatorname{Can}_\pi(P,a)
\iff
\exists u\in\operatorname{Available}_\pi(a),
P(F_u a).
\]

## 定义 27.5（领域必然）

\[
\Box_{\operatorname{Adm}}P
\iff
\forall x,\operatorname{Adm}(x)\to P(x).
\]

## 定义 27.6（证据必然）

\[
\Box_{E,a}P
\iff
\forall x,
\operatorname{Adm}(x)
\land E(x)=E(a)
\to P(x).
\]

## 定义 27.7（动力必然）

\[
\Box_F^aP
\iff
\forall x\in\operatorname{Reach}_F(a),
P(x).
\]

逻辑必然、领域必然、证据必然、动力必然和规范必然不能混用。定义一种模态并不自动给出模态间的可达关系或桥梁公理。

---

# 28. 本质是相对于目标的最小充分概念

设目标：

\[
K:X\to Y.
\]

## 定义 28.1（K-充分概念）

概念 \(C\) 对 \(K\) 充分，当：

\[
K\preceq C.
\]

## 定理 28.1（规范本质）

目标概念：

\[
E_K=(Y,K)
\]

是所有 \(K\)-充分概念中的最粗概念。

### 证明

任何 \(K\)-充分概念按定义都存在 \(K=\overline Kq_C\)，即 \(E_K\preceq C\)。\(\square\)

因此：

\[
\boxed{
\operatorname{Essence}_K(X)
=E_K.
}
\]

本质不是无条件附着在对象上的神秘清单，而是相对于要解释、预测、保存或规范化的行为目标定义的最小充分分类。

## 定义 28.2（个体本质属性）

\[
\boxed{
\operatorname{Essential}_K(P,a)
\iff
P(a)
\land
\forall x,
\operatorname{Adm}(x)
\land Kx=Ka
\to P(x).
}
\]

在保持指定本质行为不变的全部合法实现中，属性 \(P\) 均保持。

化学本质、法律本质、生物功能本质、人格本质和程序行为本质可以对应不同目标 \(K\)，不必被压成一个绝对本质。

---

# 29. 普遍者、个体与名义

一个普遍概念可表示为：

\[
q:X\to B.
\]

个体是 \(x:X\)，概念值是 \(q(x):B\)。

可区分三种结构模型：

## 29.1 实在论模型

\(B\) 作为独立类型给出，并可携带自身结构；实例通过 \(q\) 分有或实现概念值。

## 29.2 名义论模型

只保留扩展、名称或等价类，把 \(B\) 缩减为 \(\operatorname{Im}(q)\) 或对象上的分类关系。

## 29.3 概念论模型

概念依赖观察者或语言共同体：

\[
q_o:X\to B_o.
\]

争论的形式核心变为：

- 分类空间是否独立于观察者；
- 不同观察者概念间是否有规范 transport；
- 概念等价是否只在实际像上成立；
- 是否存在观察者不变的共同 quotient。

核心形式理论不预先选择三者，而允许构造模型分离它们。

---

# 30. 随附、还原与涌现

设低层概念 \(L\)，高层概念 \(H\)。

## 定义 30.1（随附）

\[
\boxed{
H\text{ 随附于 }L
\iff
H\preceq L.
}
\]

即低层同一蕴含高层同一。

## 定义 30.2（多重实现）

若 \(H\preceq L\)，但某个高层值对应多个不同低层值，则高层状态被多重实现。

## 定义 30.3（严格还原）

还原至少需要：

1. 静态因子化 \(H\preceq L\)；
2. 高层动力从低层动力下降；
3. 因子映射可构造；
4. 复杂度受控；
5. 相关准入与解释结构被保持。

随附本身不等于解释性还原。

## 定义 30.4（结构涌现）

若：

\[
H\not\preceq L_{\mathrm{local}},
\qquad
H\preceq L_{\mathrm{global}},
\]

则高层性质不能由单个局部读出决定，但能由整体联合状态决定。

## 定义 30.5（动态涌现）

高层概念上存在闭合过程：

\[
q_HF=\overline F_Hq_H,
\]

但组成部分的局部概念上没有相应独立下降。

## 定义 30.6（计算涌现）

形式因子化存在，但所有允许构造都超过指定时间、空间或描述复杂度。

这样，“涌现”被分成结构、动态和计算三种命题。

---

# Part VI：因果、时间、主体与心灵

# 31. 干预因果

carry 只说明隐藏差异改变未来。完整因果模型还需干预结构。

设干预：

\[
I_u:X\to X,
\]

背景概念 \(B\)、原因概念 \(C\)、结果概念 \(D\)。

## 定义 31.1（局部干预因果见证）

\[
\boxed{
\begin{aligned}
\operatorname{Cause}_{C\to D}(a;u,v)
\iff{}&
q_B(I_ua)=q_B(I_va)\\
&\land q_C(I_ua)\ne q_C(I_va)\\
&\land q_D(F(I_ua))\ne q_D(F(I_va)).
\end{aligned}
}
\]

它要求背景保持，原因变量被改变，结果随之改变。

## 定义 31.2（因果充分）

若结果概念沿当前原因—背景联合概念下降，则其对该结果预测充分。

## 定义 31.3（候选混杂）

若原因—背景联合概念同类的两个状态产生不同结果，则余纤维中存在未控制差异；它是候选混杂，而不是自动被命名为唯一原因。

## 定义 31.4（中介）

概念 \(M\) 为中介，当过程可分解为：

\[
C\to M\to D
\]

并且相应方格下降。

必须区分：

\[
\boxed{
\text{相关}
\ne
\text{预测充分}
\ne
\text{carry}
\ne
\text{干预因果}
\ne
\text{实际因果链}.
}
\]

---

# 32. 决定论不等于宏观可预测性

## 定理 32.1（最小反例）

令：

\[
X=\{0,1,2\},
\]

概念：

\[
q(0)=q(1)=A,
\qquad
q(2)=B.
\]

确定过程：

\[
F(0)=0,
\qquad
F(1)=2,
\qquad
F(2)=2.
\]

则：

\[
q(0)=q(1),
\]

但：

\[
q(F0)=A\ne B=q(F1).
\]

所以不存在宏观函数 \(\overline F\) 使：

\[
qF=\overline Fq.
\]

尽管微观过程是完全确定函数。\(\square\)

因此：

\[
\boxed{
\text{微观决定论}
\not\Rightarrow
\text{任意观察层的闭合可预测性}.
}
\]

观察者不确定性可以来自当前概念隐藏的余量，而不必来自微观随机性。

---

# 33. 时间、记录与不可逆性

给定过程 \(F:X\to X\) 和读出 \(q\)。

定义历史概念：

\[
H_n(x)
=(q(x),q(Fx),\ldots,q(F^nx)).
\]

有：

\[
H_n\preceq H_{n+1}.
\]

## 定义 33.1（记录增长）

若：

\[
H_n\prec H_{n+1},
\]

则新时刻增加了可区分记录。

## 定义 33.2（观察者时间箭头）

时间箭头由以下组合给出：

1. FLOW 的有序迭代；
2. 记录概念的严格精化；
3. 被删除余量不能通过准入保持的逆过程恢复。

## 定理 33.1（有限稳定）

若 \(X\) 有限，则核关系链：

\[
\ker H_0
\supseteq
\ker H_1
\supseteq
\cdots
\]

最终稳定。

若初始类数为 \(c_0\)，最终预测类数为 \(c_\infty\)，则严格细化次数至多：

\[
\boxed{c_\infty-c_0\le |X|-c_0.}
\]

有限系统中的无限未来预测区别在有限深度后全部显现，但该深度可能依赖整个系统。

## 定义 33.3（热力学型余量）

给定粗概念 \(C\) 和概率分布 \(\mu\)，条件熵：

\[
H_\mu(X\mid C(X))
\]

测量概念余纤维中的平均未分辨信息。不可逆粗粒化对应该余量无法由允许记录恢复。

---

# 34. 自我与人格同一性

自我不是唯一概念。至少区分：

\[
\begin{aligned}
S_{\mathrm{body}}&:\text{身体连续性};\\
S_{\mathrm{memory}}&:\text{记忆连续性};\\
S_{\mathrm{agency}}&:\text{行动与承诺连续性};\\
S_{\mathrm{narrative}}&:\text{自我报告生成状态};\\
S_{\mathrm{legal}}&:\text{制度身份};\\
S_{\mathrm{observer}}&:\text{观察者塔中的相容 section}.
\end{aligned}
\]

## 定义 34.1（通时身份）

给定时间索引状态 \((x_t)\)，概念 \(S\) 下的通时身份为：

\[
S(x_t)=S(x_{t+1})
\]

或更一般的指定 transport 相容性。

## 定义 34.2（强人格 section）

一个人格是身体、记忆、行动、规范承诺和自我叙述概念塔中的兼容 section。

## 命题 34.1（人格理论非唯一性）

不同人格同一性理论选择不同概念和不同相容条件。它们给出不同结论不必意味着对同一恒等命题直接矛盾。

## 定义 34.3（分裂与融合）

若一个旧身份类通过过程进入多个互不相容的新身份类，则产生分裂；多个旧类进入一个新类则产生融合。此时数值同一、记忆继承和规范责任可能不能由同一个等价关系同时表达。

---

# 35. 意向性、意识与第一／第三人称间隙

## 定义 35.1（意向结构）

主体状态类型为 \(S\)，对象世界为 \(X\)。意向结构：

\[
\boxed{
I:S\to\operatorname{Concept}(X).
}
\]

每个主体状态选择一种对象呈现方式。

对象在主体状态 \(s\) 下的 noema 为：

\[
q_{I(s)}(x),
\]

其地平线为：

\[
R_{I(s)}(q_{I(s)}x).
\]

## 定义 35.2（通达意识）

设报告、规划、行动选择和工作记忆目标为 \(K_1,\ldots,K_n\)。概念 \(A\) 是通达意识概念，当：

\[
K_i\preceq A
\quad\text{对全部 }i.
\]

即这些行为可由 \(A\) 的状态决定。

## 定义 35.3（现象概念）

候选现象概念：

\[
\Phi:X\to B_\Phi.
\]

公共行为联合概念：

\[
P_{\mathrm{pub}}=\bigvee_iK_i.
\]

若：

\[
\Phi\preceq P_{\mathrm{pub}},
\]

则现象差异随附于公共可访问信息。

若存在：

\[
P_{\mathrm{pub}}(x)=P_{\mathrm{pub}}(y),
\qquad
\Phi(x)\ne\Phi(y),
\]

则得到形式 zombie witness。

它只证明所选现象概念不由所选公共概念决定，不证明现实世界存在哲学僵尸。

## 定义 35.4（第一／第三人称桥）

第一人称概念 \(C_1\) 与第三人称概念 \(C_3\) 之间的完整桥要求：

\[
C_1\simeq_{\mathrm{con}}C_3
\]

或至少指定方向的因子化。

若两者都不决定对方，则存在双向解释余量。若只有 \(C_3\preceq C_1\)，第一人称包含更多区分；若只有 \(C_1\preceq C_3\)，第三人称包含主体不能内省恢复的区分。

---

# 36. 自我表示与对角边界

给定：

\[
g:A\to(A\to Y)
\]

和无固定点 twist：

\[
\tau:Y\to Y,
\qquad
\forall y,\tau(y)\ne y.
\]

定义：

\[
d_g(a)=\tau(g(a)(a)).
\]

## 定理 36.1（构造性对角逃逸）

\[
\boxed{d_g\notin\operatorname{range}(g).}
\]

### 证明

若存在 \(a_0\) 使 \(g(a_0)=d_g\)，则在 \(a_0\) 处：

\[
g(a_0)(a_0)
=d_g(a_0)
=\tau(g(a_0)(a_0)),
\]

产生 twist 固定点，矛盾。\(\square\)

该结论限制特定自应用表示清单，不推出“意识不可形式化”或“人类必然超越机器”。任何哲学外推都必须证明现实心灵满足该对角架构的全部前件。

---

# 37. 行动、能力与自由

设过程：

\[
F:X\times U\to X,
\]

主体策略：

\[
\pi:X\to U.
\]

行动读出：

\[
A:U\to B_A.
\]

## 定义 37.1（可选性）

锚点 \(a\) 具有多个允许行动：

\[
|\operatorname{Available}(a)|>1.
\]

## 定义 37.2（内部控制）

给定理由／内部状态概念 \(R:X\to B_R\)，行动由内部状态控制，当：

\[
A\pi=\overline\pi_RR.
\]

## 定义 37.3（外部可预测）

给定外部概念 \(E\)，若：

\[
A\pi=\overline\pi_EE,
\]

则行动可由外部读出预测。

内部控制和外部可预测可以同时成立，因此可预测性本身不排除兼容主义自由。

## 定义 37.4（理由响应）

存在背景相同而理由不同的状态，使行动不同：

\[
B(x)=B(y),
\quad
R(x)\ne R(y),
\quad
A(\pi x)\ne A(\pi y).
\]

## 定义 37.5（自主自由）

自主自由至少包括：

\[
\boxed{
\text{可选性}
+
\text{内部控制}
+
\text{理由响应}
+
\text{非强迫准入}.
}
\]

## 定义 37.6（分支自由）

若要求完全相同的微观过去仍允许多个未来，则过程不能只是函数，而应为关系或分布：

\[
F:X\to\mathcal P(X),
\qquad
|F(a)|>1.
\]

分支自由比自主自由更强；两者不可由同一个“自由意志”词无差别表达。

---

# Part VII：规范、伦理与社会

# 38. 是—应当独立性

描述性结构包括：

\[
(X,\operatorname{Adm}_{\mathrm{phys}},F,C,a).
\]

规范结构另给：

\[
\operatorname{Permitted}:X\times U\to\mathsf{Prop}.
\]

## 定理 38.1（描述性还原不足）

若规范谓词不在描述语言中定义，则仅凭描述性结构不能唯一推出一个非平凡规范谓词。

### 模型分离证明

构造两个模型 \(\mathfrak M_1,\mathfrak M_2\)，共享完全相同的：

\[
X,\operatorname{Adm}_{\mathrm{phys}},F,C,a,
\]

但令：

\[
\operatorname{Permitted}_1(x,u)=\mathsf{True},
\]

\[
\operatorname{Permitted}_2(x,u)=\mathsf{False}.
\]

所有纯描述命题在两模型中取值相同，而规范命题不同。因此描述性还原不能决定规范结构。\(\square\)

所以从“是”到“应当”的任何推导必须显式加入：

- 价值序；
- 规范前提；
- 权利约束；
- 承诺；
- 角色义务；
- 共同体准入 doctrine；
- 或其他可审计桥梁。

---

# 39. 伦理理论的不同型别

## 39.1 后果论

评价附着于结果：

\[
V:Y\to L,
\]

\[
\operatorname{Permitted}(x,u)
\iff
V(F(x,u))\succeq\theta
\]

或选择极大值行动。

## 39.2 义务论

评价附着于行动形式、承诺、权利或转换：

\[
\operatorname{Permitted}_{D}:X\times U\to\mathsf{Prop}.
\]

## 39.3 德性论

评价附着于主体政策或长期稳定性：

\[
\operatorname{Virtuous}:\operatorname{Policy}\to\mathsf{Prop}.
\]

## 39.4 关怀伦理

评价依赖关系史、具体他者和脆弱性概念：

\[
\operatorname{CareValue}
\preceq
C_{\mathrm{relation}}
\vee
C_{\mathrm{history}}
\vee
C_{\mathrm{need}}.
\]

这些理论分别评价结果、行动、主体策略和关系过程。证明它们等价需要显式桥梁，不能因为都使用“善”或“正当”就视为同一谓词。

---

# 40. 责任与道德运气

设主体控制—知识概念：

\[
C_{\mathrm{ctrl}}:X\to B_{\mathrm{ctrl}},
\]

规范评价：

\[
J:X\to L.
\]

## 定义 40.1（控制原则）

若存在：

\[
\overline J:B_{\mathrm{ctrl}}\to L
\]

使：

\[
\boxed{J=\overline JC_{\mathrm{ctrl}},}
\]

则评价完全下降到主体控制和可知的事实。

## 定义 40.2（道德运气见证）

\[
\boxed{
\operatorname{MoralLuck}(x,y)
\iff
C_{\mathrm{ctrl}}x=C_{\mathrm{ctrl}}y
\land
Jx\ne Jy.
}
\]

## 定理 40.1（道德运气—下降等价）

在有效有限模型中，控制原则成立，当且仅当没有道德运气见证。

这不决定应当接受控制原则还是结果责任；它准确定位两者的结构分歧：规范评价是否允许依赖主体不可控制的余量。

---

# 41. 公平、正义与权利

## 定义 41.1（相关性公平）

给定道德相关概念 \(R\) 和制度待遇 \(T\)：

\[
\boxed{
R(x)=R(y)
\Longrightarrow
T(x)=T(y).
}
\]

即待遇通过相关概念因子化。

## 定义 41.2（群对称公平）

设群 \(G\) 表示道德上无关的身份置换。制度 \(T\) 公平，当：

\[
\boxed{
T(gx)=T(x)
\quad
\forall g,x.
}
\]

在有效轨道 quotient 下，公平等价于 \(T\) 通过 \(X/G\) 因子化。

## 定义 41.3（权利）

权利是一类被禁止的转换：

\[
\operatorname{RightViolation}
\subseteq
X\times U\times X.
\]

合法制度 FLOW 必须避开这些转换，即使违反权利可提高某个总价值函数。

## 定义 41.4（规范冲突）

两规范在状态 \(x\) 冲突，当共同允许行动纤维为空：

\[
\{u\mid N_1(x,u)\land N_2(x,u)\}=\varnothing.
\]

这是一种兼容性失败，不等于逻辑系统爆炸。解决冲突需要优先级、例外、权衡或更细背景概念。

---

# 42. 制度与四类权力

一个制度可表示为：

\[
\mathcal I
=(X,C_{\mathrm{inst}},F_{\mathrm{inst}},
\operatorname{Adm}_{\mathrm{inst}},a_{\mathrm{canon}}).
\]

权力至少分为：

\[
\begin{aligned}
\text{分类权力}
&=\text{决定哪些 CUT 被制度采用};\\
\text{过程权力}
&=\text{决定哪些 FLOW 可发生};\\
\text{准入权力}
&=\text{决定哪些对象、主张或行动被接受};\\
\text{锚定权力}
&=\text{决定谁被当作典型、合法或有资格发言的主体}.
\end{aligned}
\]

这些权力作用在不同型别上，不能只用一个资源总量概念替代。

---

# 43. 意识形态：内部自然但外部不忠实

## 定义 43.1（制度闭合）

官方概念 \(C_{\mathrm{off}}\) 对制度过程闭合：

\[
q_{\mathrm{off}}F
=
\overline F_{\mathrm{off}}q_{\mathrm{off}}.
\]

## 定义 43.2（相关伤害盲点）

对伤害概念 \(H\)，存在：

\[
C_{\mathrm{off}}x=C_{\mathrm{off}}y,
\qquad
H(Fx)\ne H(Fy).
\]

## 定义 43.3（意识形态缺陷）

\[
\boxed{
\operatorname{IdeologyDefect}
=
\text{官方闭合}
+
\text{对相关目标不忠实}.
}
\]

一个制度可以高度稳定、统计一致、可计算并成功预测自己的官方指标，同时系统性删除对人们实际后果重要的差异。

## 最小模型 43.1

令四个状态按官方概念只分为“合规／不合规”，但按伤害概念还区分“低伤害／高伤害”。若制度对所有合规状态实施同一处理，却使其中两类产生不同伤害，则官方模型闭合而伤害 carry 非空。

---

# 44. 认识不正义、异化与支配

## 定义 44.1（证言不正义）

设主体可靠性概念 \(R_s\) 与制度可信度概念 \(T_{\mathrm{inst}}\)。若：

\[
T_{\mathrm{inst}}\not\succeq R_s
\]

且制度在同一可靠性类内因身份余量给予不同可信度，则出现证言不正义见证。

## 定义 44.2（解释资源缺失）

若主体经验目标 \(K\) 不由共同语言概念 \(L\) 决定：

\[
K\not\preceq L,
\]

则共同概念体系无法表达会改变主体经验判断的差异。这是解释资源缺失的结构形式。

## 定义 44.3（分类异化）

主体自我概念 \(S\) 不通过制度概念因子化：

\[
S\not\preceq C_{\mathrm{inst}}.
\]

## 定义 44.4（过程异化）

制度视为同一的状态对主体自我产生不同后果：

\[
\operatorname{Carry}(F_{\mathrm{inst}};
C_{\mathrm{inst}},S)
\ne\varnothing.
\]

## 定义 44.5（支配）

主体 \(A\) 支配主体 \(B\)，当 \(A\) 能单向修改：

- \(B\) 的允许行动纤维；
- 适用于 \(B\) 的准入规则；
- 表示 \(B\) 的官方概念；
- 或 \(B\) 的制度锚点资格；

而 \(B\) 没有对称反向能力，且该不对称不通过双方接受的相关规范概念因子化。

---

# 45. 承认与多观察者兼容

设两个观察者概念：

\[
C_1:X\to B_1,
\qquad
C_2:X\to B_2.
\]

联合概念像：

\[
\operatorname{Im}(C_1\vee C_2)
\hookrightarrow
\operatorname{Im}(C_1)
\times
\operatorname{Im}(C_2).
\]

## 定义 45.1（相互承认）

状态对 \((b_1,b_2)\) 被共同承认，当：

\[
\boxed{
(b_1,b_2)
\in
\operatorname{Im}_{\operatorname{Adm}}(C_1\vee C_2).
}
\]

即存在一个共同合法世界同时实现双方描述。

承认不是简单同意，也不要求两种概念相同。它要求描述之间存在共同实现。

## 定义 45.2（承认缺陷）

若双方分别允许的自我描述组合不在兼容像中，则产生承认缺陷。该缺陷可能来自：

- 概念冲突；
- 准入冲突；
- 对同一锚点的不同身份约束；
- 缺少共同背景状态；
- 或制度禁止某种组合存在。

---

# Part VIII：语言、解释与知识生产

# 46. 语言意义作为语境索引概念

设表达式类型为 \(L\)，语境为 \(K\)。

## 定义 46.1（语义解释）

\[
\boxed{
\llbracket-\rrbracket:
K\to L\to\operatorname{Concept}(X).
}
\]

一个词的意义包括：

\[
\begin{aligned}
\text{内涵}
&=\llbracket t\rrbracket_k,\\
\text{实际读出}
&=q_{\llbracket t\rrbracket_k}(a),\\
\text{实际余量}
&=R_{\llbracket t\rrbracket_k}
(q_{\llbracket t\rrbracket_k}(a)).
\end{aligned}
\]

## 定义 46.2（语境同义）

\[
t_1\equiv_kt_2
\iff
\llbracket t_1\rrbracket_k
\simeq_{\mathrm{con}}
\llbracket t_2\rrbracket_k.
\]

## 定义 46.3（歧义）

同一表达式在两个语境中诱导不等价概念。

## 定义 46.4（忠实翻译）

翻译 \(T:L_1\to L_2\) 忠实，当它保持源语言相关概念的精化与非等价关系。

## 定义 46.5（完全翻译）

若目标相关概念也都能由某个源表达式恢复，则翻译完全。

不可通约不是“完全不能交流”，而是不存在满足指定忠实性、完全性、复杂度和准入条件的共同翻译。

---

# 47. 言语行为与制度现实

语言不仅读出世界，也可改变世界。

## 定义 47.1（言语行为 FLOW）

\[
\operatorname{Say}:X\times L\to X.
\]

宣判、承诺、授权、命名、签约、投票和道歉可以改变法律、规范或关系状态。

## 定义 47.2（有效言语行为）

言语行为有效，当说话者、语境、程序和对象通过相应 ADMIT 谓词。

因此同一句话在不同锚点、角色或制度中可能只描述事实，也可能产生新事实。

---

# 48. 解释学循环作为双向概念完成

设文本结构为 \(T\)，读者概念为 \(C_n\)，解释结果为 \(K_n\)。

定义：

\[
C_{n+1}
=
\operatorname{Comp}_{K_n}(C_n),
\]

同时新的概念改变下一轮文本读出：

\[
K_{n+1}
=
\operatorname{Interpret}(T,C_{n+1}).
\]

这形成：

\[
C_n\to K_n\to C_{n+1}\to K_{n+1}\to\cdots.
\]

## 定义 48.1（解释固定点）

若：

\[
C_{n+1}\simeq_{\mathrm{con}}C_n
\]

且解释结果稳定，则达到相对于文本、读者准入和解释规则的固定点。

解释固定点不是唯一绝对意义；不同准入、背景和评价目标可能产生不同固定点。客观解释主张需要证明这些固定点之间存在不变共同因子。

---

# 49. 科学理论、经验等价与欠决定

设理论空间 \(\Theta\)，经验预测：

\[
K:\Theta\to\mathcal D(O^{\mathbb N}).
\]

## 定义 49.1（经验等价）

\[
\theta\sim_K\theta'
\iff
K(\theta)=K(\theta').
\]

## 定义 49.2（理论欠决定）

\[
\theta\ne\theta',
\qquad
K(\theta)=K(\theta').
\]

不同理论属于同一经验余纤维。

## 工具主义 quotient

把理论按经验核取商，只保留预测状态。

## 实在论余量

拒绝把经验同类中的全部差异自动删除，认为部分差异可能对应真实结构或更远未来预测。

争论的形式核心是：

\[
\boxed{
\text{是否把经验预测核商视为完整理论同一性}.
}
\]

## 定义 49.3（可证伪见证）

对理论 \(\theta\)，若存在准入观察 \(o\) 不在其预测支持中，则构成显式反例。

“尚未证明理论”与“已经构造反例”必须分开。

## 定义 49.4（解释）

解释概念 \(E\) 至少应满足：

\[
K\preceq E,
\]

并附加机制、结构、复杂度或模型转移要求。预测正确本身不等于解释。

---

# 50. 数学存在与数学哲学

在依赖类型论中：

\[
P:\mathsf{Prop}
\]

是命题，而：

\[
p:P
\]

是证明项。

必须区分：

\[
\begin{aligned}
\text{语法存在}
&=\text{表达式可形成};\\
\text{证明存在}
&=\text{具有 proof term};\\
\text{模型存在}
&=\text{理论有模型};\\
\text{构造存在}
&=x:X;\\
\text{经典存在}
&=\|X\|\text{ 或经典存在命题};\\
\text{现实实现}
&=\operatorname{Realizes}(M,x).
\end{aligned}
\]

形式主义、构造主义、结构主义和柏拉图主义可以作为不同的存在准入 doctrine：

- 形式主义强调可推导性；
- 构造主义要求显式项；
- 结构主义按结构同构确定对象身份；
- 柏拉图主义增加独立实现域。

形式内核允许比较这些模型，但不能仅凭自身定义选择其中唯一正确者。

---

# 51. 美学

设艺术品类型 \(X\)，观察者 \(o\)，评价：

\[
V_o:X\to L_o.
\]

形式概念：

\[
C_{\mathrm{form}}:X\to B_{\mathrm{form}}.
\]

## 定义 51.1（形式一致性）

作品内部变换在形式概念上具有低下降缺陷。

## 定义 51.2（原创性）

作品相对于既有生成或风格映射发生像外逃逸。

## 定义 51.3（共同品味）

多个观察者评价具有共同因子概念。

## 定义 51.4（审美客观性）

评价对允许的观察者变换保持不变。

## 定义 51.5（审美多元性）

合法观察者评价之间存在不能由共同因子消除的余量。

本理论不定义唯一“美函数”，而是分离个人评价、形式结构、共同不变量和观察者余量。

---

# 52. 宗教哲学的非循环纪律

可以定义：

\[
\operatorname{NecessaryBeing}:X\to\mathsf{Prop},
\]

或：

\[
G
=
\sum_{x:X}P_1(x)\times\cdots\times P_n(x).
\]

但：

\[
G:\mathsf{Type}
\]

不产生：

\[
g:G.
\]

任何神学存在论证必须明确：

1. 基础逻辑；
2. 模态框架；
3. 完满性质；
4. 准入条件；
5. 从前件到存在项的证明；
6. 是否使用选择、排中、模态公理或语义完备性。

不得把存在写入定义后再将投影字段误报为存在证明。

---

# Part IX：辩证法与历史哲学重构

# 53. 辩证法不是逻辑爆炸，而是缺陷驱动的最小修复

给定当前概念 \(C\)、过程 \(F\) 与目标 \(K\)。

若存在 carry：

\[
q_Cx=q_Cy,
\qquad
K(Fx)\ne K(Fy),
\]

则当前概念对问题不闭合。

定义修复：

\[
C^+
=
\operatorname{Comp}_{K\circ F}(C).
\]

## 定理 53.1（最小辩证修复）

\(C^+\) 是：

- 保留 \(C\) 的全部区分；
- 足以决定目标后果；
- 在所有满足前两项的概念中最粗；

的概念。

因此可作结构重构：

\[
\boxed{
\begin{aligned}
\text{肯定}
&=C;\\
\text{否定}
&=\text{显式 carry 见证};\\
\text{扬弃}
&=\operatorname{Comp}_{K\circ F}(C);\\
\text{具体普遍性}
&=\text{该完成的普适最小性}.
\end{aligned}
}
\]

否定不是 \(P\land\neg P\)，而是当前概念的闭合主张被反例击穿。

---

# 54. 辩证序列与成熟概念

定义问题序列 \((K_n)\)：

\[
C_{n+1}
=
\operatorname{Comp}_{K_n}(C_n).
\]

则：

\[
C_0\preceq C_1\preceq C_2\preceq\cdots.
\]

## 定义 54.1（相对成熟）

若对所有当前问题 \(K_n\)：

\[
\operatorname{Comp}_{K_n}(C_\infty)
\simeq_{\mathrm{con}}
C_\infty,
\]

则 \(C_\infty\) 相对于该问题族成熟。

新的目标、观察者、过程或现实反例仍可打破成熟状态。概念完成不是绝对终局，而是相对于问题族的固定点。

## 定理 54.1（有限终止）

若 \(X\) 有限，并且每次严格修复都严格细化等价关系，则概念序列最多经过有限次严格变化后稳定。

上界不超过从初始概念类数到 \(|X|\) 的类数差。

无限模型中可能出现严格无限精化塔，需要逆极限和现实实现审计。

---

# 55. 西方哲学结构映射

以下仅为模型映射：

| 传统概念 | 形式重构 |
|---|---|
| 柏拉图的形式与分有 | 独立分类空间 \(B\) 与实例映射 \(q:X\to B\) |
| 亚里士多德形式—质料 | \(X\simeq\sum_bR_q(b)\) |
| 实体与偶性 | 身份概念在 FLOW 下保持，性质概念改变 |
| 潜能与现实 | 从锚点出发的准入保持可达性与当前成立 |
| 笛卡尔心身二元论 | 心灵、身体概念互不决定，并需额外交互 FLOW |
| 斯宾诺莎双属性 | 同一底层 \(X\) 上的两个属性 CUT |
| 莱布尼茨不可分辨者同一 | 联合概念映射单射 |
| 休谟因果与归纳问题 | 有限历史不足以无前件下降到未来 |
| 康德现象—物自身 | 现象 CUT、非平凡余纤维与可能不存在的规范 section |
| 黑格尔辩证发展 | carry 反例迫使最小概念完成 |
| 胡塞尔意向性与地平线 | 主体状态索引概念及其余纤维 |
| 维特根斯坦语言游戏 | 语境索引语义与言语行为 FLOW |
| 尼采／福柯权力 | 对 CUT、FLOW、ADMIT、ANCHOR 的控制 |
| 罗尔斯无知之幕 | 删除身份坐标后的群不变规范选择 |

任何具体历史主张仍需文本证据、版本语境和解释竞争分析；数学对应只给出可检验结构。

---

# Part X：定量哲学与有限反模型

# 56. 概念信息、余量与目标盲度

给定有限概率状态 \(X\sim\mu\)。

## 定义 56.1（概念信息）

\[
I_\mu(C)
=H(q_C(X)).
\]

## 定义 56.2（概念余量）

\[
R_\mu(C)
=H(X\mid q_C(X)).
\]

## 定理 56.1（精化单调）

若 \(C\preceq D\)，则：

\[
I_\mu(C)\le I_\mu(D),
\]

\[
R_\mu(D)\le R_\mu(C).
\]

更细概念表达更多信息，留下更少条件余量。

## 定义 56.3（目标盲度）

对目标 \(K\)：

\[
\boxed{
\operatorname{Blind}_\mu(C;K)
=H(K(X)\mid q_C(X)).
}
\]

## 定理 56.2（完成信息成本）

\[
H(C(X),K(X))-H(C(X))
=H(K(X)\mid C(X)).
\]

所以为使目标可预测而加入的平均新增信息，正是当前概念对目标的条件盲度。

注意：条件熵为零通常只给出分布支持上的几乎处处决定，不自动给出全类型上的严格函数因子化。

---

# 57. 六个最小反模型

## 57.1 决定但不可宏观预测

使用第 32 节三状态模型。它分离微观决定论和宏观下降。

## 57.2 Gettier 两世界模型

两个证据同类世界具有不同命题真值，实际锚点落在真世界。它分离真信念／辩护和稳健知识。

## 57.3 道德运气模型

两个主体具有相同意图、知识与控制概念值，但环境余量使结果不同；若责备按结果变化，则评价不能下降到控制概念。

## 57.4 意识形态模型

官方分类对制度过程闭合，但同一官方类中的人承受不同伤害。它分离内部自然性和现实忠实性。

## 57.5 承认兼容模型

令：

\[
X=\{x_0,x_1\},
\]

两个观察者分别只有两个可能描述，但共同像只包含：

\[
(0,0),(1,1).
\]

则各自可能值的交叉组合 \((0,1),(1,0)\) 无共同实现。多主体状态空间是直积中的兼容子集。

## 57.6 结构涌现模型

令微观状态为两个 bit：

\[
X=\{0,1\}^2,
\]

高层性质为 parity：

\[
H(x_1,x_2)=x_1\oplus x_2.
\]

\(H\) 不由任一单独 bit 决定，但由联合概念决定。这是结构涌现而非神秘新实体。

---

# 58. 哲学争论的型别诊断

在进入真假争论前，应先分类：

\[
\boxed{
\begin{aligned}
\text{事实争论}
&=\text{同模型、同概念、同锚点下命题取值不同};\\
\text{概念争论}
&=\text{使用不同 CUT};\\
\text{因果争论}
&=\text{使用不同 FLOW 或干预结构};\\
\text{本体争论}
&=\text{使用不同对象类型或 ADMIT};\\
\text{视角争论}
&=\text{使用不同 ANCHOR 或观察者概念};\\
\text{规范争论}
&=\text{使用不同价值序或准入 doctrine};\\
\text{语义含混}
&=\text{推理中无 transport 地切换概念};\\
\text{范畴错误}
&=\text{把不同型别上的谓词直接比较};\\
\text{实现争论}
&=\text{形式模型是否有现实 section};\\
\text{历史解释争论}
&=\text{数学模型与文本证据的对应不同}.
\end{aligned}
}
\]

这不是取消哲学争论，而是避免用逻辑矛盾掩盖模型、概念、准入和锚点差异。

---

# Part XI：范畴结构、Lean 路线与研究计划

# 59. 范畴论定位

一个基本哲学方格为：

\[
\begin{array}{ccc}
X&\xrightarrow{F}&Y\\
\downarrow q_C&&\downarrow q_D\\
B_C&\xrightarrow{\overline F}&B_D.
\end{array}
\]

其中：

- 水平箭头是过程；
- 垂直箭头是概念界面；
- 方格记录下降或缺陷；
- ADMIT 是对象和箭头上的 indexed doctrine；
- ANCHOR 是点、section 或 compatible cone；
- defect 可取值于有序幺半对象、距离、正锥或见证类型。

自然容器是：

\[
\boxed{
\text{defect-enriched double category of concepts and processes}.
}
\]

概念格给出静态语义；双范畴给出概念与过程的交互；fibration 给出依赖余量；completion 给出缺陷修复；observer cone 给出主体；doctrine 给出合法性与规范性。

---

# 60. 最小 Lean 核心草案

```lean
universe u v w

structure Concept (X : Type u) where
  View : Type v
  read : X → View

namespace Concept

def ObsEq (C : Concept X) (x y : X) : Prop :=
  C.read x = C.read y

def Fiber (C : Concept X) (b : C.View) : Type _ :=
  {x : X // C.read x = b}

def AdmissibleFiber
    (C : Concept X)
    (admit : X → Prop)
    (b : C.View) : Type _ :=
  {x : X // admit x ∧ C.read x = b}

def Refines (fine coarse : Concept X) : Type _ :=
  Σ p : fine.View → coarse.View,
    ∀ x, coarse.read x = p (fine.read x)

def Joint (C D : Concept X) : Concept X where
  View := C.View × D.View
  read x := (C.read x, D.read x)

def Descends
    (current : Concept X)
    (future : Concept Y)
    (F : X → Y) : Type _ :=
  Σ fbar : current.View → future.View,
    ∀ x, future.read (F x) = fbar (current.read x)

def CarryWitness
    (current : Concept X)
    (future : Concept Y)
    (F : X → Y) : Type _ :=
  Σ x y : X,
    current.read x = current.read y ×
      future.read (F x) ≠ future.read (F y)

def StableAt
    (C : Concept X)
    (admit : X → Prop)
    (P : X → Prop)
    (a : X) : Prop :=
  ∀ x, admit x → C.read x = C.read a →
    (P x ↔ P a)

def Knows
    (C : Concept X)
    (admit : X → Prop)
    (P : X → Prop)
    (a : X) : Prop :=
  admit a ∧ P a ∧
    ∀ x, admit x → C.read x = C.read a → P x

end Concept
```

第一承重定理：

```lean
theorem noCarry_of_descends
    (h : Concept.Descends current future F) :
    IsEmpty (Concept.CarryWitness current future F)
```

第二承重定理：

```lean
theorem joint_least_common_refinement :
  Concept.Refines (Concept.Joint C D) C ×
  Concept.Refines (Concept.Joint C D) D ×
  (∀ E,
    Concept.Refines E C →
    Concept.Refines E D →
    Concept.Refines E (Concept.Joint C D))
```

具体参数方向在正式实现时应与仓库统一，并通过编译校正。

---

# 61. Lean 依赖顺序

建议单一依赖链：

```text
FormalPhilosophy/Kernel/Concept
→ FormalPhilosophy/Kernel/Fiber
→ FormalPhilosophy/Kernel/Refinement
→ FormalPhilosophy/Kernel/Joint
→ FormalPhilosophy/Kernel/Descent
→ FormalPhilosophy/Kernel/Carry
→ FormalPhilosophy/Kernel/Completion
→ FormalPhilosophy/Prediction/Itinerary
→ FormalPhilosophy/Epistemology/Truth
→ FormalPhilosophy/Epistemology/Knowledge
→ FormalPhilosophy/Epistemology/Gettier
→ FormalPhilosophy/Metaphysics/Essence
→ FormalPhilosophy/Metaphysics/Substance
→ FormalPhilosophy/Causality/Intervention
→ FormalPhilosophy/Time/Record
→ FormalPhilosophy/Mind/ObserverSelf
→ FormalPhilosophy/Agency/Freedom
→ FormalPhilosophy/Normativity/IsOught
→ FormalPhilosophy/Ethics/Responsibility
→ FormalPhilosophy/Social/Institution
→ FormalPhilosophy/Dialectics/Completion
→ FormalPhilosophy/Models/Historical
```

应优先复用仓库现有预测完成、线性 quotient、观察者距离和对角逃逸结果，不复制平行定理。

---

# 62. 第一批必须关闭的定理链

## 62.1 概念内核链

1. 规范依赖分解；
2. refinement 自反与复合；
3. joint 的普适性质；
4. 有效概念与 kernel quotient；
5. 概念同构类与有限等价关系格反序对应。

## 62.2 过程链

1. descent 排除 carry；
2. 有限无 carry 反向构造；
3. 定量 defect 组合律；
4. completion 的 extensive、monotone、idempotent；
5. 预测完成最小性。

## 62.3 认识论链

1. 知识事实性；
2. 证据精化单调；
3. 合取闭包；
4. Gettier 最小反模型；
5. 有限历史归纳充分性判据。

## 62.4 形而上学链

1. 莱布尼茨联合忠实性；
2. 实体—偶性变化分类；
3. 相对本质普适性；
4. 随附／多重实现；
5. parity 结构涌现反例。

## 62.5 规范与社会链

1. 是—应当模型独立性；
2. 道德运气—下降等价；
3. 群公平—轨道 quotient 因子化；
4. 自然性—忠实性分离；
5. 多观察者兼容像定理。

## 62.6 辩证链

1. 最小修复普适性；
2. completion 闭包算子；
3. 有限概念修复终止；
4. 无限塔的形式逆极限；
5. 现实实现与形式固定点分离。

---

# 63. 可发表结构

第一篇核心论文应限制为：

> **Formal Concept Dynamics: Relative Identity, Descent Defects, and Minimal Conceptual Completion**

承重内容：

- 概念格；
- 依赖余纤维；
- descent／carry；
- completion 闭包算子；
- 有限模型；
- Lean 核心。

第二篇：

> **Predictive Essence and Fiber-Stable Knowledge**

处理：

- 预测本质；
- 知识；
- Gettier；
- 归纳；
- 观察者完成。

第三篇：

> **Normative Descent, Moral Luck, and Institutional Blindness**

处理：

- 是—应当独立性；
- 责任；
- 公平；
- 意识形态；
- 承认。

第四篇：

> **Dialectical Completion as Defect-Driven Concept Repair**

处理闭包算子、有限终止、无限塔和历史哲学模型。

不应在第一篇同时宣称解决意识难题、自由意志、宗教本体论、全部伦理学和全部西方哲学史。

---

# 64. 研究协议

对任何待形式化哲学概念，依次执行：

1. 指定状态类型 \(X\)；
2. 指定准入谓词；
3. 指定实际锚点或说明只研究模型有效性；
4. 把概念写成 \(q:X\to B\)；
5. 计算其 kernel 与余纤维；
6. 指定相关过程；
7. 指定目标概念；
8. 检查 descent；
9. 构造 carry 或证明 NoCarry；
10. 区分有限反向、经典反向与一般构造性边界；
11. 构造最小 completion；
12. 证明普适性质；
13. 建立至少一个有限模型和一个反模型；
14. 与仓库既有 Lean 声明建立依赖；
15. 标记定义、纸面定理、Lean 定理和开放桥梁；
16. 对历史哲学解释另列文本证据责任。

形式哲学不以术语数量评价，而以以下指标评价：

\[
\boxed{
\text{定义清晰度}
+
\text{反例强度}
+
\text{最小性}
+
\text{模型转移}
+
\text{kernel 可审计性}.
}
\]

---

# Part XII：严格非主张

# 65. 本文不声称

1. 不声称哲学可以脱离基础逻辑、类型形成规则和推理规则。
2. 不声称定义概念即可证明概念对象存在。
3. 不声称定义观察者即可证明观察者非空。
4. 不声称形式观察者塔必有现实实现。
5. 不声称每个 quotient 都有全局截面。
6. 不声称每个余纤维都同构于统一余数类型。
7. 不声称所有概念争论都只是语言争论。
8. 不声称所有语言争论都可由 gauge 消除。
9. 不声称自然方格交换就意味着概念忠实。
10. 不声称无 carry 在一般构造性无限模型中自动给出下降函数。
11. 不声称相关性、carry、干预因果和实际因果相同。
12. 不声称微观决定论推出宏观可预测性。
13. 不声称宏观不可预测性证明微观随机性。
14. 不声称预测本质是唯一绝对本质。
15. 不声称随附等于还原。
16. 不声称结构涌现证明新实体独立存在。
17. 不声称知识定义已经解决全部认识论争议。
18. 不声称 Gettier 的所有历史变体都被两世界模型穷尽。
19. 不声称有限历史永远不能预测未来；只声称预测需要因子化前件。
20. 不声称形式融贯等于现实真理。
21. 不声称实用成功等于真理。
22. 不声称描述性结构能够无规范前件推出应当。
23. 不声称控制原则是唯一正确责任原则。
24. 不声称道德运气的存在自动决定制度应如何评价。
25. 不声称群不变性穷尽全部正义。
26. 不声称权利可完全还原为结果价值。
27. 不声称意识形态只是一种计算错误。
28. 不声称社会权力可由单一数值完全排序。
29. 不声称多观察者兼容等于价值一致。
30. 不声称第一／第三人称概念不等价即证明意识不可物理解释。
31. 不声称形式 zombie witness 证明现实僵尸存在。
32. 不声称对角逃逸证明人类心灵超越一切形式系统。
33. 不声称自由的不同定义彼此等价。
34. 不声称外部可预测性排除内部控制。
35. 不声称宗教对象的类型定义构成存在论证明。
36. 不声称审美不变量给出唯一美学标准。
37. 不声称数学模型与历史哲学文本完全同一。
38. 不声称 C-IRPT 是普通范畴论、煤代数、抽象解释、sheaf、Markov category 或类型论的替代品。
39. 不声称本文新增纸面定理已经通过 Lean kernel。
40. 不声称本文已关闭全部哲学问题。

---

# 66. 最终统一

## 66.1 最底层结构

\[
\boxed{
\mathfrak M
=
(X,\operatorname{Adm},a,\mathcal F,\mathcal C).
}
\]

## 66.2 概念公式

\[
\boxed{
C=(B_C,q_C),
\qquad
X\simeq\sum_{b:B_C}R_C(b).
}
\]

## 66.3 过程公式

\[
\boxed{
q_DF
=
\overline Fq_C
+
\epsilon_F.
}
\]

零缺陷表示下降；非零缺陷由 carry、距离或关系见证表达。

## 66.4 完成公式

\[
\boxed{
\operatorname{Comp}_K(C)
=C\vee E_K.
}
\]

它是保留旧概念并决定目标的最小精化。

## 66.5 观察者公式

\[
\boxed{
\operatorname{Observer}
=
\operatorname{AdmissibleCompatibleAnchor}
(\mathcal C^\infty).
}
\]

## 66.6 哲学字典

\[
\boxed{
\begin{aligned}
\textbf{存在}
&=\text{合法类型中的被见证项};\\
\textbf{概念}
&=\text{规定相对同一性的分类界面};\\
\textbf{现象}
&=\text{对象通过概念后的可见坐标};\\
\textbf{余量}
&=\text{同一概念值下仍未区分的状态};\\
\textbf{形式}
&=\text{概念坐标};\\
\textbf{质料}
&=\text{该坐标下的依赖实现纤维};\\
\textbf{实体}
&=\text{过程族下稳定且对相关行为忠实的身份概念};\\
\textbf{偶性变化}
&=\text{身份保持而性质概念改变};\\
\textbf{本质}
&=\text{保留指定行为的最小充分概念};\\
\textbf{真理}
&=\text{命题在实际锚点上的成立};\\
\textbf{知识}
&=\text{真理在证据余纤维上的稳定};\\
\textbf{怀疑}
&=\text{证据纤维仍包含目标反例};\\
\textbf{因果缺口}
&=\text{隐藏余量经过 FLOW 成为未来差异};\\
\textbf{记忆}
&=\text{为关闭历史 carry 保留的最小状态};\\
\textbf{时间}
&=\text{FLOW、记录精化与不可逆余量丢失的有序组合};\\
\textbf{主体}
&=\text{观察者塔中的合法相容锚定 section};\\
\textbf{自由}
&=\text{可选性、内部控制、理由响应及指定分支条件};\\
\textbf{规范}
&=\text{不能由纯描述结构唯一推出的准入 doctrine};\\
\textbf{责任}
&=\text{评价向控制—知识概念的下降};\\
\textbf{道德运气}
&=\text{该下降的显式失败};\\
\textbf{正义}
&=\text{制度对道德无关差异的不变性及权利约束};\\
\textbf{权力}
&=\text{对 CUT、FLOW、ADMIT、ANCHOR 的非对称控制};\\
\textbf{意识形态}
&=\text{内部闭合但对相关现实不忠实的概念系统};\\
\textbf{承认}
&=\text{多主体描述在共同实现像中的兼容};\\
\textbf{语言}
&=\text{语境索引概念与能够改变制度状态的言语 FLOW};\\
\textbf{解释}
&=\text{目标充分、结构明确且复杂度受控的因子化};\\
\textbf{辩证法}
&=\text{由显式缺陷强制出的最小概念修复};\\
\textbf{对角边界}
&=\text{自表示系统在无固定点 twist 下的逃逸审计}.
\end{aligned}
}
\]

## 66.7 总公式

\[
\boxed{
\text{哲学的发展}
=
\text{定义概念}
\to
\text{计算余纤维}
\to
\text{构造反例}
\to
\text{识别 carry}
\to
\text{建立最小完成}
\to
\text{证明跨模型普适性}.
}
\]

## 66.8 最终命题

世界的哲学复杂性不主要来自拥有多少术语，而来自：

\[
\boxed{
\text{任何有限概念界面都可能留下余量；
任何过程都可能把余量带回未来；
任何完成都需要现实准入；
任何自表示都可能遭遇对角逃逸。}
}
\]

形式哲学的任务不是消灭这些边界，而是准确说明：

- 哪个概念删除了什么；
- 哪个过程重新显现了什么；
- 哪个规范准入了什么；
- 哪个观察者锚定了什么；
- 哪个反例迫使概念如何最小地改变；
- 哪些结论已经成为证明，哪些仍只是定义、模型或开放桥梁。

这就是形式概念动力学的核心：

\[
\boxed{
\text{概念不是静态标签，
而是被反例、过程、观察者和实现条件持续审计的可修复结构。}
\]

---

# Part XIII：充分性、闭包、伴随与双修复

# 67. 一切哲学充分性都是因子化问题

固定状态类型 \(X\)。对任意目标 \(T:X\to Y\)，定义规范目标概念：

\[
E_T=(\operatorname{Im}T,T).
\]

## 定理 67.1（普遍充分性）

以下等价：

\[
E_T\preceq C
\]

与存在：

\[
\overline T:B_C\to\operatorname{Im}T,
\qquad
T=\overline T\circ q_C.
\]

因此证据充分、预测充分、责任充分、公平相关性充分与解释充分都可视为目标沿概念的因子化。

---

# 68. 概念完成是闭包算子与反射

固定目标 \(T\)，定义：

\[
\operatorname{cl}_T(C)=C\vee E_T.
\]

## 定理 68.1（闭包三律）

在概念等价意义下：

\[
C\preceq\operatorname{cl}_T(C),
\]

\[
C\preceq D
\Longrightarrow
\operatorname{cl}_T(C)\preceq\operatorname{cl}_T(D),
\]

\[
\operatorname{cl}_T(\operatorname{cl}_T(C))
\simeq_{\mathrm{con}}
\operatorname{cl}_T(C).
\]

## 定理 68.2（固定点—充分性等价）

\[
\boxed{
\operatorname{cl}_T(C)\simeq C
\iff
E_T\preceq C.
}
\]

## 定理 68.3（反射普适性质）

令：

\[
\operatorname{Suff}_T
=\{D\mid E_T\preceq D\}.
\]

若 \(D\in\operatorname{Suff}_T\)，则：

\[
\boxed{
\operatorname{cl}_T(C)\preceq D
\iff
C\preceq D.
}
\]

所以完成把任意概念送到最近的目标充分固定点。

---

# 69. 固定目标完成必然交换

对固定目标 \(S,T\)：

\[
\operatorname{cl}_S\operatorname{cl}_T(C)
\simeq
C\vee E_T\vee E_S
\simeq
\operatorname{cl}_T\operatorname{cl}_S(C).
\]

因此真正的历史路径依赖不能只来自固定目标的静态 join。它至少需要目标、过程、准入、可实现性或对象类型随历史改变。

---

# 70. 内生目标与辩证固定点

设批判目标依赖当前概念：

\[
T:\operatorname{Con}(X)\to\operatorname{Target}(X).
\]

定义：

\[
\Phi(C)=C\vee E_{T(C)}.
\]

若 \(\Phi\) 单调，则其固定点是对自身生成问题闭合的成熟概念。若概念格完备，则可由固定点理论定义包含初始概念的最小成熟固定点。有限 \(X\) 上迭代必有限稳定；无限模型可能需要 \(\omega\)-连续性或超限迭代。

---

# 71. 每个过程诱导概念伴随

给定：

\[
F:X\to Y,
\]

对未来概念 \(D\) 定义拉回：

\[
F^*D=(B_D,q_D\circ F).
\]

定义最大可预测未来概念：

\[
F_*C
=\bigvee\{D\mid F^*D\preceq C\}.
\]

## 定理 71.1（过程伴随）

在相应 join 和有效像存在时：

\[
\boxed{
F^*D\preceq C
\iff
D\preceq F_*C.
}
\]

因此：

\[
F^*\dashv F_*.
\]

未来要求的拉回与当前概念能够可靠决定的最大未来后果形成伴随。

---

# 72. 缺陷具有两种规范修复

若目标 \(D\) 不能沿当前概念 \(C\) 通过过程 \(F\) 下降，则存在两种方向。

## 源端扩张

\[
\boxed{
C^+=C\vee F^*D.
}
\]

它是保留旧概念并使完整目标可预测的最小源概念扩张。

## 目标端压缩

若概念 meet 存在，定义：

\[
\boxed{
D^-=D\wedge F_*C.
}
\]

它是在不增加源信息时仍能合法维持的最丰富目标主张。

因此面对不足，可选择“看得更多”或“说得更少”。形式理论只给出两个规范边界；具体规范选择仍需 ADMIT 或价值 doctrine。

---

# Part XIV：知识、共同知识与审计边界

# 73. 知识是命题代数上的内部算子

在合法状态子类型上定义：

\[
K_C(P)(a)
\iff
\forall x,\ x\sim_Ca\to P(x).
\]

## 定理 73.1

\(K_C\) 满足：

- 事实性：\(K_CP\subseteq P\)；
- 单调性；
- 幂等性：\(K_CK_CP=K_CP\)；
- 合取保持。

定义：

\[
\Diamond_CP(a)
\iff
\exists x,\ x\sim_Ca\land P(x).
\]

则 \(\Diamond_C\) 是相应闭包算子。在经典或适当稳定条件下：

\[
K_CP=\neg\Diamond_C\neg P.
\]

---

# 74. Gettier 缺陷具有逻辑最小修复

定义：

\[
C_P^+=C\vee E_P.
\]

它是保留原证据并使 \(P\) 在所有纤维上恒定的最粗概念。该修复逻辑上最小，但可能把目标真值本身直接加入证据，因此认识论还必须要求证据来源独立、非循环和可获得。

---

# 75. 共同概念与联合概念

对观察者族 \((C_o)\)，定义：

\[
C_{\mathrm{common}}=\bigwedge_oC_o,
\qquad
C_{\mathrm{joint}}=\bigvee_oC_o.
\]

有：

\[
C_{\mathrm{common}}\preceq C_o\preceq C_{\mathrm{joint}}.
\]

共同概念表示每个观察者单独都能恢复的最精细内容；联合概念表示信息融合后的总分辨能力。客观共同因子、集体认识能力与共同实现兼容像是三个不同结构。

---

# 76. 内部审计不能发现自身分类删除的差异

若审计概念 \(A\preceq C\)，则：

\[
C(x)=C(y)\Longrightarrow A(x)=A(y).
\]

任意多个都通过 \(C\) 因子化的审计联合以后仍通过 \(C\) 因子化。因此完全使用官方分类可表达数据的审计无法发现官方分类纤维内部的伤害差异。独立审计的形式要求不是组织独立，而是审计概念不能完全通过被审计概念因子化。

---

# 77. 固定本体上的概念天花板

\[
\top_X=(X,\operatorname{id}_X)
\]

决定固定 \(X\) 上的任意目标，因此：

\[
\operatorname{cl}_T(\top_X)\simeq\top_X.
\]

无限开放的哲学发展若要超出 \(\top_X\)，必须改变对象类型、准入域、过程、语言、观察者或内生问题生成机制。概念精化与本体生成不可混同。

---

# 78. 概念完整性与对角完整性正交

\(\top_X\) 对已有对象完全忠实，但一个表示清单仍可能无法枚举全部自应用对象。必须区分：

\[
\begin{aligned}
\text{概念忠实性}&=q\text{ 是否单射};\\
\text{表示完整性}&=g\text{ 是否满射};\\
\text{动力闭合性}&=FLOW\text{ 是否下降};\\
\text{现实实现性}&=\text{形式对象是否通过 ADMIT}.
\end{aligned}
\]

四者互不自动推出。

---

# 79. 理由是 proof-relevant 因子化见证

一个理由不是一句自然语言解释，而是：

\[
\overline T:B_C\to Y
\]

及交换证明：

\[
T=\overline T\circ q_C.
\]

因此：

\[
\boxed{
\text{理由}=
\text{使目标沿相关概念因子化的构造见证}.
}
\]

反例 \(C(x)=C(y)\) 且 \(T(x)\neq T(y)\) 证明所给理由类型不足以承载目标结论。

---

# 80. 缺陷关系演算

定义：

\[
\boxed{
\Delta(C;T)=\ker C\setminus\ker T.
}
\]

在集合模型或有效 quotient 条件下：

\[
\boxed{
T\text{ 通过 }C\text{ 因子化}
\iff
\ker C\subseteq\ker T
\iff
\Delta(C;T)=\varnothing.
}
\]

完成的核公式为：

\[
\boxed{
\ker\operatorname{Comp}_T(C)
=\ker C\cap\ker T.
}
\]

---

# 81. 复合缺陷定位

对：

\[
X\xrightarrow F Y\xrightarrow G Z
\]

和概念 \(C,D,E\)，若复合有 carry，则在中间概念相等可判定时，要么 \(F:C\to D\) 已有 carry，要么 \(G:D\to E\) 有 carry。因果审计因此可以寻找隐藏差异第一次穿过哪个 CUT。

---

# 82. 最大可预测未来商的关系构造

在可达未来 \(Y_F=\operatorname{Im}F\) 上，以关系：

\[
yS_{F,C}y'
\iff
\exists x,x',\ Fx=y,\ Fx'=y',\ Cx=Cx'
\]

生成最小等价闭包 \(\approx_{F,C}\)。定义：

\[
\operatorname{Pred}_F(C)=Y_F/{\approx_{F,C}}.
\]

它是当前概念 \(C\) 能可靠决定的最精细未来概念，并具体实现第 71 节的 \(F_*C\)。

---

# 83. 零误差概念修复的信息复杂度

在有限模型中，对每个概念值 \(b\) 定义：

\[
N_b(C;T)=|\{T(x)\mid C(x)=b\}|.
\]

令：

\[
m^*(C;T)=\max_bN_b(C;T).
\]

## 定理 83.1

加入辅助标签 \(M:X\to\{1,\ldots,m\}\) 并要求 \(T\) 通过 \((C,M)\) 因子化所需的最小标签数恰为：

\[
\boxed{m^*(C;T).}
\]

最坏情形零误差二进制修复成本为：

\[
\boxed{\lceil\log_2m^*(C;T)\rceil.}
\]

平均信息成本则由 \(H(T\mid C)\) 给出。

---

# 84. 无信息复活

若中间表示与输出都只通过 \(C\) 计算：

\[
Z=h\circ C,
\qquad
W=g\circ Z,
\]

则 \(W\preceq C\)。因此任何只接收 \(C\)-值的确定程序都不能恢复被 \(C\) 删除的区别。独立随机性可以改变错误分布，却不能以概率一恢复两个具有同一 \(C\)-值而不同目标值的状态。

---

# 85. 溯因解释是 section 选择

假说空间 \(H\)、观察空间 \(O\)、预测：

\[
P:H\to O.
\]

观察 \(o\) 的所有解释组成纤维 \(R_P(o)\)。解释器是 section：

\[
s:\operatorname{Im}P\to H,
\qquad
Ps=\operatorname{id}.
\]

若群 \(G\) 保持预测且在某观察纤维上无固定点，则不存在同时保持预测和全部 \(G\)-对称的唯一解释选择。唯一解释必须加入先验、复杂度、机制、历史锚点或其他 doctrine。

---

# 86. 反事实需要跨世界 transport

不同干预可具有不同状态类型 \(X_u\)。要表达“同一个人在另一干预下”，必须给出共同身份基底与 transport：

\[
I_u:X_u\to B,
\qquad
\tau_{v,u}:X_u\to X_v,
\]

满足：

\[
I_v\tau_{v,u}=I_u.
\]

路径独立要求：

\[
\tau_{w,v}\tau_{v,u}=\tau_{w,u}.
\]

闭路 transport 非恒等时出现反事实身份 holonomy。

---

# 87. 认识论三重伴随

令 \(\operatorname{Sat}_C\) 为在 \(C\)-纤维上恒定的命题，\(i\) 为其到全部命题的包含。则在相应逻辑条件下：

\[
\boxed{
\Diamond_C\dashv i\dashv K_C.
}
\]

\(\Diamond_CP\) 是包含 \(P\) 的最小 \(C\)-可表达命题，\(K_CP\) 是包含于 \(P\) 的最大 \(C\)-可表达命题。

---

# 88. 分布式知识与共同知识

对观察者族：

\[
C_{\mathrm{joint}}=\bigvee_iC_i,
\qquad
C_{\mathrm{common}}=\bigwedge_iC_i.
\]

定义：

\[
D_IP=K_{C_{\mathrm{joint}}}P,
\qquad
C_IP=K_{C_{\mathrm{common}}}P.
\]

“每个人都知道”记为 \(E_IP=\bigwedge_iK_{C_i}P\)。一般：

\[
\boxed{C_IP\Longrightarrow E_IP\Longrightarrow D_IP,}
\]

反向均可失败。集体融合能够知道无人单独知道的事实；人人知道也不自动形成无限层相互知道。

---

# 89. 公告学习与观察学习不同

真实公告 \(P\) 将准入域更新为：

\[
A_P(x)=A(x)\land P(x).
\]

它不必改变概念 \(C\)，却缩小合法纤维。观察式学习是：

\[
C\mapsto C\vee E,
\]

公告式学习是：

\[
A\mapsto A\land P.
\]

前者增加区分，后者删除不再合法的世界。假公告若删除实际锚点，则产生形式模型而非知识增长。

---

# Part XV：抽象不可能性、隐私、公平与集体行动

# 90. 非平凡抽象必有盲点

若概念 \(C\) 非单射，则存在二值目标 \(T:X\to\mathbf2\) 不能通过 \(C\) 因子化。因此唯一能够对全部可能目标无损的概念是忠实概念。不存在脱离目标族的绝对最佳抽象。

---

# 91. 资源限制产生概念多元主义

若概念成本沿精化非减，而预算低于 \(\operatorname{Cost}(\top_X)\)，则所有可行概念必对某些目标存在盲点。不同目标可能产生彼此不可比较的 Pareto 最优概念，因此有限资源下的多元主义可以是结构结果，而非语义混乱。

---

# 92. 隐私—公平—精确性兼容判据

设允许公开概念 \(P\)、道德相关概念 \(R\)、精确目标 \(T\)。若制度既只能使用 \(P\)，又只能依赖 \(R\)，还要精确实现 \(T\)，则必要且充分的结构条件为：

\[
\boxed{E_T\preceq P\wedge R.}
\]

若失败，则完全隐私、完全相关性公平与目标精确实现至少要放弃一项。修复所需额外信息量可由第 83 节的最小标签数计算。

---

# 93. 去中心化行动与最小通信

行动者 \(i\) 的本地概念为 \(C_i\)，联合行动分量为 \(u_i\)。存在本地策略 \(\pi_i\) 使 \(u_i=\pi_iC_i\) 当且仅当：

\[
E_{u_i}\preceq C_i.
\]

若所有人必须独立产生同一动作 \(v\)，则：

\[
E_v\preceq\bigwedge_iC_i.
\]

允许通信消息 \(M_i\) 后，最小消息字母数由 \(m^*(C_i;u_i)\) 给出。通信复杂度是个体概念对行动目标的精确修复成本。

---

# 94. 纯描述中立不能唯一选择规范

若两个规范方案由保持全部描述事实的对称自同构交换，则不存在既唯一又完全描述不变的确定性选择器。任何唯一规范裁决必须引入价值、权利、优先级、历史承诺、角色锚点或元规范。

---

# 95. 语义历史的 holonomy

概念随历史阶段变化：

\[
C_t:X\to B_t,
\]

相邻意义 transport 为 \(p_{t+1,t}\)。闭环复合给出：

\[
H:B_0\to B_0.
\]

局部重命名把 \(H\) 共轭变换，因此其共轭类是 gauge 不变量。若 \(H\neq\operatorname{id}\)，则概念经历一轮历史后虽回到同一词语，却没有回到同一区分结构。真正语义历史需要 transport 与 holonomy，而不只是固定目标 join。

---

# 96. 本体扩张无规范延拓

若旧对象类型嵌入新对象类型：

\[
i:X\hookrightarrow X',
\]

旧概念 \(q:X\to B\) 不能仅凭自身唯一决定对新增对象的分类。只要存在新对象且目标概念至少有两个值，就可构造两个在旧域完全一致、在新对象上不同的扩展。概念精化与本体扩张是不同操作。

---

# 97. 四种闭合方向

必须分别审计：

1. 区分闭合：概念是否忠实；
2. 动力闭合：过程是否下降；
3. 表达闭合：表示目录是否满射；
4. 实现闭合：形式对象是否通过 ADMIT。

四者互不自动推出。完整哲学体系不能由单一 completeness 谓词表达。

---

# 98. 四层统一结构

固定 \(X\) 上有静态概念格 \(\operatorname{Con}(X)\)；每个过程诱导 \(F^*\dashv F_*\)；每个概念诱导认识论三重伴随 \(\Diamond_C\dashv i\dashv K_C\)；每个目标诱导完成反射 \(\operatorname{cl}_T\)。其外部仍有实现边界与对角边界。

---

# 99. 第二层总公式

\[
\boxed{
\begin{aligned}
\text{主张}&=\text{目标映射};\\
\text{理由}&=\text{因子化见证};\\
\text{反例}&=\text{同纤维异目标};\\
\text{修复}&=\text{源端扩张或目标端压缩};\\
\text{成熟}&=\text{闭包固定点};\\
\text{开放性}&=\text{内生新目标、本体扩张或对角逃逸}.
\end{aligned}
}
\]

---

# Part XVI：翻译、学习、因果识别与表演性反馈

# 100. 哲学模型翻译的商结构

对模型翻译 \(h:X\to Y\)，未来概念 \(D\) 的拉回是 \(h^*D\)。若 \(h\) 满射，则 \(Y\) 上的概念恰对应 \(X\) 上在 \(h\)-纤维恒定的概念。若 \(h\) 非单射，则存在源概念不能由目标模型表达；概念完备翻译因此不可能。

---

# 101. 行为等价是最大双模拟

对过程 \(F:X\to X\) 与读出 \(q\)，定义：

\[
x\approx_Fy
\iff
\forall n,\ q(F^nx)=q(F^ny).
\]

该关系是保持读出的最大双模拟。任何既保存当前读出又支持闭合更新的身份概念，其同类状态必为 \(\approx_F\)-等价。预测 quotient 因而是行为身份的最粗闭合概念。

---

# 102. 局部一致不推出全局实现

三个局部约束：

\[
a=b,\qquad b=c,\qquad a\neq c
\]

各自非空，并在单变量交叠支持上相容，但不存在全局 \((a,b,c)\) 同时满足它们。局部模型非空与交叠投影一致并不保证全局 section；局部—全局实现缺陷需要单独审计。

---

# 103. 客观性不是多数共识

多观察者形成群胚，视角变换给出 transport。全局客观对象是满足全部 transport coherence 的 section。若某闭路 holonomy 无固定点，则不存在全局 section。共识只是局部读出相同；客观性是跨坐标变换的结构不变。

---

# 104. 不可比较价值不能无损标量化

若价值偏序含不可比较元素，则不存在忠实嵌入实数全序的标量效用。任何单一效用必须增加比较、合并不同价值或放弃反射原偏序。唯一价值排序需要额外权重、词典序、权利优先级或其他规范 doctrine。

---

# 105. 权利约束不能自动还原为结果效用

若两个行动具有相同结果效用却许可状态不同，则许可谓词不能通过结果效用因子化。权利、承诺、程序与意图若能够区分结果相同的行动，就属于过程或关系层的规范结构，而不是另一种结果数值。

---

# 106. 完全对称数据不能产生唯一选择

若输入数据被群作用固定，而候选集合没有公共固定点，则不存在保持该对称性的确定性唯一选择器。随机化可以保持分布对称，却不能创造规范确定代表。

---

# 107. 有限样本不能无前件决定未观察事实

若样本只覆盖 \(S\subsetneq X\)，取未观察点 \(x_*\)，总能构造两个目标谓词在 \(S\) 上完全相同而在 \(x_*\) 上不同。任何只依赖样本的学习器至少对其中一个目标失败。泛化必须依赖假说类、平滑性、因果结构、复杂度或先验准入。

---

# 108. 观察等价不推出因果等价

设模型观察读出 \(O\) 与干预读出 \(I\)。干预行为可由观察数据识别当且仅当：

\[
E_I\preceq E_O.
\]

共同原因模型与直接因果模型可以拥有相同观察联合分布却在 `do` 干预下不同。因果解释需要至少区分干预行为不同的模型。

---

# 109. Goodhart 缺陷与表演性完成

指标 \(M\) 在初始域上可能足以决定真实目标 \(T\)，但优化该指标产生响应过程 \(F_M\) 后，若存在：

\[
M(F_Mx)=M(F_My),
\qquad
T(F_Mx)\neq T(F_My),
\]

则出现 Goodhart carry。更一般地，概念决定过程 \(C\mapsto F_C\) 时，定义：

\[
\Phi(C)=C\vee E_{T\circ F_C}.
\]

其固定点是表演性稳定概念。

---

# 110. 概率一不等于结构知识

结构知识要求命题在整个合法证据纤维成立，因此推出条件概率一；反向一般失败，因为零测度反例仍可存在。有限模型中，只使用概念 \(C\) 预测目标 \(T\) 的最小分类错误为：

\[
\boxed{
e^*(C;T)=1-\sum_b\max_y\mu(C=b,T=y).
}
\]

正 Bayes 误差可以是概念信息不足而不是算法能力不足。

---

# 111. 可定义对象必须被结构自同构固定

若对象由结构语言中的无参数公式唯一指定，则所有结构自同构必须固定它。处于非单点自同构轨道中的对象不能由该语言无参数唯一指称。名字、坐标、位置、历史或外部锚点是打破对称的附加结构。

---

# 112. 二值概念识别有限世界的最小数目

若 \(|X|=n\)，使用二值概念联合忠实识别每个状态，所需最小概念数为：

\[
\boxed{\lceil\log_2n\rceil.}
\]

下界来自 \(k\) 个 bit 最多给出 \(2^k\) 个标签；上界由给状态分配不同二进制编码实现。

---

# 113. Sorites 来自把局部容忍误当等价

度量概念上的局部容忍关系：

\[
xT_\varepsilon y\iff d(Cx,Cy)\le\varepsilon
\]

通常不传递。若二值谓词在链首尾取值不同，则必有某个相邻步骤改变真值；问题在于边界可观测性、稳定性、语境和灰区，而不是从局部小差异推出首尾完全相同。

---

# 114. de dicto 存在不推出 de re section

“每个可能世界都有某个满足 \(P\) 的对象”只给出逐世界非空；“同一个对象贯穿全部世界”要求身份 transport 下的相容 section。若模态 holonomy 无固定点，则可有逐世界非空而无 de re 个体。

---

# 115. 基础主义、融贯主义与无限主义的依赖几何

基础主义使用良基依赖图并终止于锚点；融贯主义允许环并要求整体固定点；无限主义允许无限依赖并要求兼容极限。循环约束可以有多个、零个或唯一固定点，因此融贯本身不保证存在、唯一或现实真理。

---

# 116. 稳健知识半径

在度量概念空间定义：

\[
K_C^\varepsilon(P,a)
\iff
\forall x,
\operatorname{Adm}(x)\land d(Cx,Ca)\le\varepsilon
\to P(x).
\]

反例距离：

\[
m_C(P,a)=\inf\{d(Ca,Cx)\mid\operatorname{Adm}(x)\land\neg P(x)\}.
\]

若 \(\varepsilon<m_C(P,a)\)，则 \(\varepsilon\)-知识成立。该量给出知识对观测扰动的稳健半径。

---

# 117. 随机概念与信息降级序

把确定概念推广为 Markov kernel \(K:X\rightsquigarrow B\)。定义：

\[
K\preceq_{\mathrm{garble}}L
\iff
\exists G,\ K=G\circ L.
\]

后处理不能提高任意决策问题中的能力。确定性 refinement 是该信息序的特殊情况。

---

# 118. 概念格与可观察函数代数

有限模型中定义：

\[
\mathcal A_C
=\{f:X\to\mathbb R\mid Cx=Cy\Rightarrow f(x)=f(y)\}.
\]

则：

\[
C\preceq D
\iff
\mathcal A_C\subseteq\mathcal A_D.
\]

联合概念对应由两个可观察代数生成的代数，共同粗化对应代数交。目标完成在代数侧就是加入目标生成元后取闭包。

---

# 119. 三重语义表示

固定有限 \(X\) 上，一个概念可以等价理解为：

1. 分类界面；
2. 相对同一性关系；
3. 可观察函数代数。

概念、等价关系和观察代数分别给出信息、不可区分性和可表达性的三种语言。

---

# 120. 第二层总统一

形式哲学的核心困难可统一为某种结构能否沿信息受限界面有效下降。修复只有四个根本方向：精化、压缩、锚定、扩域。它们不可互相冒充。

---

# Part XVII：缺陷图、协同、冗余、动态完成与自审计

# 121. 缺陷的单调序

\[
\Delta(C;T)=\ker C\setminus\ker T.
\]

若 \(C\preceq D\)，则：

\[
\boxed{\Delta(D;T)\subseteq\Delta(C;T).}
\]

若目标 \(S\preceq T\)，则：

\[
\boxed{\Delta(C;S)\subseteq\Delta(C;T).}
\]

更细源概念缩小缺陷；更细目标扩大潜在缺陷。

---

# 122. 缺陷图与最小图着色修复

有限 \(X\) 上定义缺陷图 \(G(C;T)\)：同一 \(C\)-纤维中目标值不同的状态之间连边。若用辅助标签 \(M\) 修复，则 \(M\) 必须对每条缺陷边赋不同标签，因此是合法图着色。

## 定理 122.1

\[
\boxed{
|L|_{\min}=\chi(G(C;T))
=\max_b|\{T(x)\mid C(x)=b\}|.
}
\]

所以概念修复可以计算为缺陷图的最小着色。

---

# 123. 结构协同与最小充分支持

对概念族 \((C_i)\)，子集 \(S\) 充分当：

\[
E_T\preceq\bigvee_{i\in S}C_i.
\]

定义协同阶：

\[
\operatorname{syn}(T;C_i)
=\min\{|S|\mid S\text{ 充分}\}.
\]

parity 目标对逐 bit 概念的协同阶等于全部 bit 数。涌现可以形式化为目标只在概念联合中出现的高阶协同。

---

# 124. 冗余与知识韧性

定义充分性失效割：

\[
\kappa_T(C_i)
=\min\{|R|\mid E_T\not\preceq\bigvee_{i\notin R}C_i\}.
\]

系统可容忍 \(\kappa_T-1\) 个任意信息源失效。若存在 \(m\) 个两两不相交的充分支持，则 \(\kappa_T\ge m\)。真正独立验证对应不相交信息支持，而非重复复制同一来源。

---

# 125. 最小不一致核与击中集修复

命题族 \((P_i)\) 的子集 \(S\) 的模型类型为：

\[
\operatorname{Model}(S)=\sum_x\prod_{i\in S}P_i(x).
\]

有限不一致理论必有最小不一致核。删除集 \(H\) 使理论恢复一致，当且仅当 \(H\) 击中每个最小不一致核。因此理论、法律和规范冲突修复可以转化为最小击中集问题。

---

# 126. 矛盾与欠决定是纤维基数的两个极端

对准入纤维 \(R_C^A(b)\)：

\[
|R|=0\Rightarrow\text{不可实现},
\]

\[
|R|=1\Rightarrow\text{唯一决定},
\]

\[
|R|>1\Rightarrow\text{欠决定}.
\]

矛盾和含混都可被看作描述界面与实现纤维之间不同的基数相位。

---

# 127. 多行动动态完成

若幺半群 \(M\) 作用于 \(X\)，定义：

\[
\operatorname{Dyn}_M(C)
=\bigvee_{m\in M}F_m^*C.
\]

其同一关系为：

\[
x\sim y
\iff
\forall m,\ C(F_mx)=C(F_my).
\]

所有允许行动都在 \(\operatorname{Dyn}_M(C)\) 上下降；它是保留当前概念并使全部行动闭合的最小概念。

---

# 128. 静态完成与动态完成一般不交换

\[
\operatorname{Dyn}_M(\operatorname{cl}_T(C))
=
\operatorname{Dyn}_M(C)
\vee
\bigvee_mE_{T\circ F_m},
\]

而：

\[
\operatorname{cl}_T(\operatorname{Dyn}_M(C))
=
\operatorname{Dyn}_M(C)\vee E_T.
\]

前者通常更精细。当前知道目标值不等于知道目标在全部未来行动后如何演化。两者的差异可由“时间泄漏见证”显式审计。

---

# 129. 遗忘是严格概念粗化

若 \(D=h\circ C\)，则 \(D\preceq C\)。知识沿精化单调，所以遗忘不能产生新知识。只有当 \(h\) 在实际概念像上单射时，遗忘可无损恢复；否则任何仅使用 \(D\) 的内部程序都不能无误恢复被删除的 \(C\)-区别。

---

# 130. 解释唯一性取决于 doctrine 的 meet 闭合

令 \(\mathcal E\subseteq\operatorname{Con}(X)\) 为允许解释类，\(\mathcal E_T=\{C\in\mathcal E\mid E_T\preceq C\}\)。若 \(\mathcal E_T\neq\varnothing\) 且 \(\mathcal E\) 对相关 meet 闭合，则：

\[
C_T^*=\bigwedge_{C\in\mathcal E_T}C
\]

是唯一最粗可接受解释。若 doctrine 不对 meet 闭合，则可出现多个互不可比较的最小解释，没有规范唯一核心。

---

# 131. 解释必须保留证明来源

定义：

\[
\operatorname{Reason}_C(T)
=\sum_{\overline T:B_C\to Y}\prod_x(Tx=\overline T(q_Cx)).
\]

若 \(q_C\) 满射，因子映射外延唯一；但不同程序、机制、因果链、前提与复杂度仍可实现相同函数。因此真正解释应是 proof-relevant：

\[
\operatorname{Explains}_C(T)
=\sum_{r:\operatorname{Reason}_C(T)}\operatorname{Provenance}(r).
\]

---

# 132. 未实现概念值上的反事实欠决定

若 \(q_C\) 不满射，则因子化只决定 \(\overline T\) 在 \(\operatorname{Im}q_C\) 上的值。像外概念值的反事实输出可有多个不同扩张。因此实际数据一致不推出对未实现状态的唯一反事实回答；需要连续性、机制、结构方程或其他扩张 doctrine。

---

# 133. 端到端反例不能自动定位责任接口

复合链最终出现 carry 时，在有限可判定模型中可定位给定状态对第一次变得概念可区分的层。但若多个局部方格都未认证，仅凭端到端失败不能唯一决定哪个接口错误。异常归因需要端到端反例加其余接口的独立闭合证书。

---

# 134. 压缩—对角不完备二分

设模型分类 \(q:\mathcal M\twoheadrightarrow B\)，并声称用 \(B\) 索引全部布尔批判 \(g:B\to(B\to\mathbf2)\)。若 \(q\) 非单射，则系统存在概念盲点；若 \(q\) 单射，则它为双射，可构造：

\[
P(m)=\neg g(qm)(qm)
\]

并由对角论证证明 \(P\) 不在内部目录。故一个自审计体系要么压缩世界并留下盲点，要么不能用同一分类索引穷尽全部自应用批判。该结论依赖明确的自应用与无固定点 twist 前件。

---

# 135. 缺陷生成器与哲学终结

令批判生成器：

\[
\operatorname{Crit}:\operatorname{Con}(X)\to\operatorname{Target}(X),
\]

并定义：

\[
\Phi(C)=C\vee E_{\operatorname{Crit}(C)}.
\]

若每次批判都产生严格新区别，则有限 \(X\) 上不可能无限进行。长期开放发展至少要求批判停止、遗忘旧区别、本体扩张、准入改变、语言升阶或进入更高表示层。

---

# 136. 非忠实概念存在随机猜测级目标

若 \(C\) 非单射，取被它合并的两个状态并赋均匀概率，构造在两状态上取不同值的二值目标。任何只依赖 \(C\) 的预测器最优错误率为 \(1/2\)。因此任何真正压缩世界的概念都存在某个目标使其至多达到随机猜测水平；抽象质量只能相对于目标族评价。

---

# 137. 第三层统一对象

形式概念动力学可进一步由五个对象组织：

1. 缺陷关系 \(\Delta(C;T)\)；
2. 缺陷图 \(G(C;T)\)；
3. 最小充分支持超图 \(\mathcal H_T(C_i)\)；
4. 动态完成 \(\operatorname{Dyn}_M(C)\)；
5. 解释、实现与 provenance doctrine。

它们分别计算反例、修复成本、协同冗余、时间闭合和非循环解释。

---

# 138. 四组结构对偶

## 矛盾／欠决定

\[
R=\varnothing,\quad |R|=1,\quad |R|>1.
\]

## 协同／冗余

\[
\operatorname{syn}
=\text{最少需要多少来源},
\qquad
\kappa
=\text{最少删除多少来源才失败}.
\]

## 扩张／遗忘

\[
C\vee E_T
\quad\text{vs.}\quad
D=h\circ C.
\]

## 当前闭合／时间闭合

\[
\operatorname{cl}_T(C)
\quad\text{vs.}\quad
\operatorname{Dyn}_M(\operatorname{cl}_T(C)).
\]

这些对偶把概念发展的静态、信息、时间与一致性结构放在同一序理论中。

---

# 139. 第三层最终命题：成熟是缺陷定位能力

形式哲学的成熟不等于“没有缺陷”。更严格的成熟条件是能够回答：

- 哪个概念纤维含有反例；
- 缺陷第一次在哪个过程界面显现；
- 修复需要多少额外标签或信息位；
- 哪些信息源协同、哪些冗余；
- 哪个最小不一致核导致整体不可实现；
- 解释的共同核心是否仍被 doctrine 接受；
- 反事实回答是否只是在离像点上的任意扩张；
- 当前完成在时间和行动后是否保持闭合；
- 自审计目录是否存在压缩盲点或对角逃逸。

因此：

\[
\boxed{
\textbf{哲学成熟}
=
\text{缺陷见证}
+
\text{缺陷定位}
+
\text{修复复杂度}
+
\text{非循环审计}.
}
\]

整套理论由此升级为：

\[
\boxed{
\textbf{Formal Concept Dynamics}
=
\textbf{a theory of factorization, defect geometry, repair complexity, dynamic completion, and self-audit boundaries.}
}
\]

其总运动不再只是：

\[
\text{概念}\to\text{余量}\to\text{carry}\to\text{完成},
\]

而是：

\[
\boxed{
\text{界面}
\to
\text{不可区分关系}
\to
\text{缺陷与反例}
\to
\text{最小修复}
\to
\text{动态闭合}
\to
\text{实现审计}
\to
\text{自审计边界}.
}
\]
以下从 **§140** 继续。仍然只做纸面推理，不处理 GitHub，也不把下述命题标记为 Lean `Closed`。

---

# Part XVIII：概念依赖、规律自然性与非交换过程

# 140. 概念依赖演算

固定状态类型 (X)。定义：

[
\boxed{
A\Rightarrow B
\iff
B\preceq A
}
]

表示概念 (A) 足以决定概念 (B)。

亦即存在：

[
f:B_A\to B_B
]

满足：

[
q_B=f\circ q_A.
]

这不是命题蕴涵，而是函数依赖。

## 定理 140.1（概念依赖的基本规则）

下列规则全部成立。

### 自反性

[
\boxed{
A\Rightarrow A.
}
]

### 投影

[
\boxed{
A\vee B\Rightarrow A,
\qquad
A\vee B\Rightarrow B.
}
]

### 传递性

[
A\Rightarrow B,
\qquad
B\Rightarrow C
]

推出：

[
\boxed{
A\Rightarrow C.
}
]

### 增广

[
A\Rightarrow B
]

推出：

[
\boxed{
A\vee C
\Rightarrow
B\vee C.
}
]

### 合并

[
A\Rightarrow B,
\qquad
A\Rightarrow C
]

推出：

[
\boxed{
A\Rightarrow B\vee C.
}
]

### 分解

[
A\Rightarrow B\vee C
]

推出：

[
\boxed{
A\Rightarrow B,
\qquad
A\Rightarrow C.
}
]

### 伪传递

[
A\Rightarrow B,
\qquad
B\vee C\Rightarrow D
]

推出：

[
\boxed{
A\vee C\Rightarrow D.
}
]

### 证明

全部由因子映射的恒等、复合、配对和投影构造得到。比如增广中，若：

[
q_B=f(q_A),
]

则：

[
(q_B,q_C)
=========

(f\times\operatorname{id})(q_A,q_C).
]

(\square)

这意味着概念间的决定关系具有一套独立于具体哲学领域的推理演算。

---

## 定义 140.1（依赖闭包）

给定一组已知概念依赖 (\Sigma)，定义概念 (A) 的依赖闭包：

[
\boxed{
\operatorname{Dep}_{\Sigma}(A)
==============================

\bigvee
\left{
B
;\middle|;
\Sigma\vdash A\Rightarrow B
\right}.
}
]

在有限概念族中，该算子满足：

[
A\preceq\operatorname{Dep}_{\Sigma}(A),
]

单调性与幂等性。

所以概念理论至少包含两个不同的闭包：

[
\begin{aligned}
\operatorname{cl}*T(A)
&=A\vee E_T,
&&\text{由目标强迫的语义完成};\
\operatorname{Dep}*{\Sigma}(A)
&=\text{由既有依赖规则推出的推理闭包}.
\end{aligned}
]

前者加入当前概念尚不能表达的新区别；后者只展开已经隐含在现有依赖中的后果。

---

# 141. 多目标的规范共同本质

给定目标族：

[
(T_i:X\to Y_i)_{i\in I},
]

定义联合目标概念：

[
\boxed{
E_{\mathcal T}
==============

\bigvee_{i\in I}E_{T_i}.
}
]

## 定理 141.1（多目标最小充分性）

概念 (C) 同时足以决定全部 (T_i)，当且仅当：

[
\boxed{
E_{\mathcal T}\preceq C.
}
]

而 (E_{\mathcal T}) 是所有同时充分概念中的最粗者。

### 证明

(C) 同时决定全部 (T_i)，等价于：

[
E_{T_i}\preceq C
]

对全部 (i) 成立。

由 join 的普适性质，这等价于：

[
\bigvee_iE_{T_i}\preceq C.
]

(\square)

因此，一个领域的“完整理论状态”应相对于它实际承诺解释的目标族定义：

[
\boxed{
\operatorname{Essence}_{\mathcal T}
===================================

E_{\mathcal T}.
}
]

目标族越大，规范本质越精细。

---

## 定理 141.2（总信息成本与顺序无关）

在有限概率模型中，对任意目标排列 (\pi)：

[
\boxed{
H(T_1,\ldots,T_n\mid C)
=======================

\sum_{k=1}^n
H!\left(
T_{\pi(k)}
\mid
C,T_{\pi(1)},\ldots,T_{\pi(k-1)}
\right).
}
]

总完成成本与加入目标的顺序无关，但每个目标的边际贡献依赖顺序。

这与静态 completion 的交换性一致：

[
\operatorname{cl}*{T_i}
\operatorname{cl}*{T_j}
\simeq
\operatorname{cl}*{T_j}
\operatorname{cl}*{T_i}.
]

所以两件事必须分开：

[
\boxed{
\text{总理论信息量是顺序不变的；
发现信用与边际贡献可能是顺序依赖的。}
}
]

---

# 142. 规律不是单一语境中的拟合，而是自然因子化

设 (\mathcal E) 为语境、实验条件或制度环境组成的范畴。

对每个语境 (e)，给出：

[
X_e,
\qquad
C_e:X_e\to B_e,
\qquad
T_e:X_e\to Y_e.
]

对语境变换：

[
u:e\to e',
]

给出 transport：

[
X_u:X_e\to X_{e'},
]

[
B_u:B_e\to B_{e'},
]

[
Y_u:Y_e\to Y_{e'}.
]

要求概念和目标本身相容：

[
\boxed{
C_{e'}X_u
=========

B_uC_e,
}
]

[
\boxed{
T_{e'}X_u
=========

Y_uT_e.
}
]

每个语境中若有局部规则：

[
f_e:B_e\to Y_e
]

满足：

[
T_e=f_eC_e,
]

则还需要检查规则本身是否跨语境相容。

## 定义 142.1（自然规律）

局部规则族 ((f_e)) 是自然规律，当：

[
\boxed{
Y_uf_e
======

f_{e'}B_u
}
]

对每个语境变换 (u:e\to e') 成立。

---

## 定理 142.1（有效像上的自然性）

若 (C,T) 的 transport 方格自然，且：

[
T_e=f_eC_e,
\qquad
T_{e'}=f_{e'}C_{e'},
]

则：

[
Y_uf_e
======

f_{e'}B_u
]

至少在：

[
\operatorname{Im}(C_e)
]

上成立。

### 证明

对任意 (x:X_e)：

[
\begin{aligned}
Y_uf_e(C_ex)
&=
Y_uT_e(x)\
&=
T_{e'}(X_ux)\
&=
f_{e'}C_{e'}(X_ux)\
&=
f_{e'}B_u(C_ex).
\end{aligned}
]

(\square)

若 (C_e) 满射，则自然性在整个 (B_e) 上成立。

---

## 定义 142.2（语境规律缺陷）

若 (Y_{e'}) 带度量，定义：

[
\boxed{
\epsilon_u(b)
=============

d!\left(
Y_uf_e(b),
f_{e'}B_u(b)
\right).
}
]

单一语境中：

[
T_e=f_eC_e
]

只表示局部拟合。

真正规律要求：

[
\boxed{
\text{局部因子化}
+
\text{跨语境自然性}
+
\text{有效域覆盖}.
}
]

所以科学规律、法律原则和语义规则都不应只由一个数据域中的零误差定义。

---

# 143. 通过删去反例，任何概念都能伪装成完美规律

设 (X) 有限，概念：

[
C:X\to B,
]

目标：

[
T:X\to Y.
]

记：

[
X_b={x\mid C(x)=b},
]

[
X_{b,t}
=

{x\mid C(x)=b,\ T(x)=t},
]

[
n_{b,t}=|X_{b,t}|.
]

我们寻找子域：

[
A\subseteq X
]

使 (T|_A) 能通过 (C|_A) 因子化。

这要求对每个 (b)，集合：

[
A\cap X_b
]

只包含一种目标值。

## 定理 143.1（最大无反例覆盖）

满足：

[
T|_A
\text{ 通过 }
C|_A
\text{ 因子化}
]

的最大子域大小为：

[
\boxed{
\max_A|A|
=========

\sum_b\max_t n_{b,t}.
}
]

### 证明

对每个 (C)-纤维，合法子域最多保留一个目标块，因此至多保留：

[
\max_tn_{b,t}
]

个状态。

分别选择每个纤维中最大的目标块，即达到该上界。 (\square)

---

## 定义 143.1（最大规律覆盖率）

[
\boxed{
\operatorname{Cov}(C;T)
=======================

\frac{
\sum_b\max_tn_{b,t}
}{
|X|
}.
}
]

最少需要删除的反例数为：

[
\boxed{
|X|-
\sum_b\max_tn_{b,t}.
}
]

这与均匀分布下只使用 (C) 预测 (T) 的最优准确率相同。

---

## 推论 143.2（领域免疫化）

任何不充分概念都可以通过缩小 ADMIT 域而变成零缺陷概念。

因此：

[
\boxed{
\text{零反例}
\not\Rightarrow
\text{强规律};
}
]

还必须审计：

[
\boxed{
\text{理论删去了多少状态，
以及准入域是否独立于目标反例定义。}
}
]

若每次出现反例便修改：

[
\operatorname{Adm}
]

把该反例排除，则理论可以永远保持闭合，但经验内容不断缩小。

---

# 144. 静态概念本身不产生观察顺序效应

真正的观察不一定只是读出，也可能改变状态。

## 定义 144.1（观察仪器）

一个观察仪器为：

[
\boxed{
\mathcal I_C=(o_C,p_C),
}
]

其中：

[
o_C:X\to B_C
]

是观察结果，

[
p_C:X\to X
]

是观察后的状态更新。

先观察 (C)，再观察 (D)，所得联合结果为：

[
\boxed{
J_{C;D}(x)
==========

\left(
o_C(x),
o_D(p_Cx)
\right).
}
]

反向顺序并重新排列坐标：

[
\boxed{
J_{D;C}^{\mathrm{swap}}(x)
==========================

\left(
o_C(p_Dx),
o_D(x)
\right).
}
]

## 定义 144.2（观察顺序效应）

若存在 (x)：

[
J_{C;D}(x)
\neq
J_{D;C}^{\mathrm{swap}}(x),
]

则存在观察顺序效应。

---

## 定理 144.1（互不扰动排除顺序效应）

若：

[
o_Dp_C=o_D,
]

且：

[
o_Cp_D=o_C,
]

则：

[
\boxed{
J_{C;D}
=

J_{D;C}^{\mathrm{swap}}.
}
]

### 证明

[
J_{C;D}(x)
==========

(o_Cx,o_Dx),
]

[
J_{D;C}^{\mathrm{swap}}(x)
==========================

(o_Cx,o_Dx).
]

(\square)

若进一步：

[
p_Dp_C=p_Cp_D,
]

则连最终状态也与顺序无关。

---

## 推论 144.2（纯读出交换）

若：

[
p_C=p_D=\operatorname{id},
]

则任何两个静态概念读出都无顺序效应。

因此，以下现象若存在真实顺序效应：

* 量子测量；
* 问卷顺序；
* 司法询问；
* 医疗诊断流程；
* 心理启动；
* 制度分类；

就不能仅由两个静态函数：

[
X\to B_C,
\qquad
X\to B_D
]

描述，必须引入观察 backaction、语境依赖或状态更新。

---

# 145. 修复顺序的概念曲率

设：

[
\Phi,\Psi:
\operatorname{Con}(X)
\to
\operatorname{Con}(X)
]

为两个概念修复算子。

定义它们在概念 (C) 上的曲率关系：

[
\boxed{
\Omega_{\Phi,\Psi}(C)
=====================

\ker(\Phi\Psi C)
\triangle
\ker(\Psi\Phi C),
}
]

其中 (\triangle) 为对称差。

## 定义 145.1（平坦修复）

若：

[
\Omega_{\Phi,\Psi}(C)=\varnothing,
]

则两种修复在 (C) 上路径无关。

若非空，则存在状态对在两种修复顺序下获得不同的相对同一性。

---

## 定理 145.1（固定目标完成零曲率）

对固定目标 (S,T)：

[
\boxed{
\Omega_{\operatorname{cl}_S,\operatorname{cl}_T}(C)
===================================================

\varnothing.
}
]

因为：

[
\operatorname{cl}_S\operatorname{cl}_T(C)
\simeq
C\vee E_T\vee E_S
\simeq
\operatorname{cl}_T\operatorname{cl}_S(C).
]

所以静态、无限资源、无遗忘的目标累加是平坦的。

---

## 推论 145.2（曲率来源）

真正非零曲率必须来自至少一种非静态结构：

[
\boxed{
\begin{aligned}
&\text{目标依赖当前概念};\
&\text{观察改变对象};\
&\text{每次修复后发生遗忘或预算压缩};\
&\text{ADMIT 域随路径变化};\
&\text{对象类型被过程扩张};\
&\text{不同修复改变后续可用过程}.
\end{aligned}
}
]

所以“历史路径依赖”可以被定义为修复算子的非零曲率，而不仅是叙事上的先后差异。

---

# 146. 干预的非交换性是因果相互作用

设干预族：

[
F_u:X\to X.
]

对目标 (T:X\to Y)，定义干预交换缺陷：

[
\boxed{
\operatorname{Comm}_T(u,v)
==========================

\left{
x
;\middle|;
T(F_uF_vx)
\neq
T(F_vF_ux)
\right}.
}
]

若该集合非空，则干预顺序会改变目标。

## 定理 146.1（状态交换推出所有目标交换）

若：

[
F_uF_v=F_vF_u,
]

则对任意目标 (T)：

[
\operatorname{Comm}_T(u,v)=\varnothing.
]

---

## 定理 146.2（忠实观察下的反向判据）

设目标族：

[
(Q_i:X\to B_i)_{i\in I}
]

联合忠实。

若对全部 (i,x)：

[
Q_i(F_uF_vx)
============

Q_i(F_vF_ux),
]

则：

[
\boxed{
F_uF_v
======

F_vF_u.
}
]

### 证明

联合映射：

[
Q=(Q_i)_i
]

单射，而两种复合在全部联合读出上相等，因此状态相等。 (\square)

---

## 推论 146.3（非加性相互作用）

若 (X) 是阿贝尔群，且干预只是独立平移：

[
F_u(x)=x+a_u,
]

则：

[
F_uF_v=F_vF_u.
]

所以任何非零干预交换缺陷都排除了“独立阿贝尔加法效应”模型。

这为：

* 药物先后顺序；
* 法律措施顺序；
* 学习课程顺序；
* 创伤与修复；
* 多原因干预；

提供一个严格的相互作用见证。

---

# 147. 路径敏感规范不能还原为结果伦理

设过程路径类型为：

[
\Gamma.
]

终点映射：

[
e:\Gamma\to X.
]

规范评价：

[
J:\Gamma\to L.
]

## 定义 147.1（结果可还原规范）

若存在：

[
\overline J:X\to L
]

使：

[
\boxed{
J=\overline J\circ e,
}
]

则规范评价只依赖最终结果。

---

## 定理 147.1（历史敏感性阻碍结果还原）

若存在两条路径：

[
\gamma,\gamma'\in\Gamma
]

满足：

[
e(\gamma)=e(\gamma'),
]

但：

[
J(\gamma)\neq J(\gamma'),
]

则不存在结果函数 (\overline J) 表示该规范。

### 证明

若 (J=\overline Je)，则相同终点必给出相同评价，矛盾。 (\square)

因此：

[
\boxed{
\text{程序正义、承诺、同意、权利、背叛与历史责任}
}
]

只要区分同一终点的不同路径，就不能被单纯结果效用完全表示。

其规范缺陷为：

[
\boxed{
\Delta(e;J)
===========

\ker e\setminus\ker J.
}
]

---

# Part XIX：证据相位、集体推理与创新

# 148. 证据纤维的四种认识相位

给定证据概念：

[
E:X\to B,
]

准入谓词 (A)，证据值 (b)，以及命题 (P)。

证据纤维：

[
R_E^A(b)
========

{x\mid A(x)\land E(x)=b}.
]

定义四种相位。

## 不可能证据

[
\boxed{
R_E^A(b)=\varnothing.
}
]

## 稳定为真

[
\boxed{
R_E^A(b)\neq\varnothing
\land
\forall x\in R_E^A(b),\ P(x).
}
]

## 稳定为假

[
\boxed{
R_E^A(b)\neq\varnothing
\land
\forall x\in R_E^A(b),\ \neg P(x).
}
]

## 未决定

[
\boxed{
\exists x,y\in R_E^A(b),
\quad
P(x)\land\neg P(y).
}
]

---

## 定理 148.1（有限经典模型中的四分律）

若纤维有限、成员关系和 (P) 可判定，则上述四种相位恰有一种成立。

所以认识状态并非只有“知道／不知道”二分，而是：

[
\boxed{
\text{不可能、知道真、知道假、证据不足}.
}
]

---

## 定理 148.2（实际精化的稳定性）

若 (b=E(a)) 来自实际锚点，则“不可能证据”被排除。

若概念 (D) 精化 (E)，且取实际 (D(a))-纤维，则：

* 已稳定为真的命题仍稳定为真；
* 已稳定为假的命题仍稳定为假；
* 未决定状态可能被解析为真、假，或继续未决定。

因此真实证据精化不会推翻已经在较粗纤维上结构稳定的知识。

---

# 149. ANCHOR 排除空纤维上的虚假全知

若把知识粗略定义成：

[
K'_E(P,b)
\iff
\forall x,\
A(x)\land E(x)=b
\to
P(x),
]

那么当：

[
R_E^A(b)=\varnothing
]

时，有：

[
K'_E(P,b)
]

并且：

[
K'_E(\neg P,b)
]

同时成立。

这是空域上的全称命题真，不是实际主体的知识。

## 定理 149.1（空证据的虚假全知）

不附加纤维非空性或实际锚点时，任意不可能证据值都会“知道”所有命题。

所以稳健知识必须包含：

[
\boxed{
\text{实际锚点}
\quad\text{或至少}\quad
\text{证据纤维非空见证}.
}
]

这说明 ANCHOR 不是哲学装饰，而是排除 vacuous omniscience 的逻辑承重结构。

---

# 150. 有限世界中的真实讨论必然稳定

设群体初始联合概念为：

[
C_0.
]

第 (n) 轮公开消息为：

[
M_n:X\to B_n.
]

真实信息累积定义为：

[
\boxed{
C_{n+1}
=

C_n\vee M_n.
}
]

因此：

[
C_n\preceq C_{n+1}.
]

## 定理 150.1（有限讨论稳定）

若 (X) 有限，且每次非冗余消息都严格细化当前概念，则严格信息增长次数至多：

[
\boxed{
|X|-
|\operatorname{Im}(C_0)|.
}
]

### 证明

每次严格精化至少增加一个等价类，而等价类总数不超过 (|X|)。 (\square)

所以有限世界中的无限真实讨论，最终只能：

* 重复已有信息；
* 改变规范；
* 改变对象域；
* 忘记旧区别；
* 或引入新的外部观察。

---

## 定理 150.2（全信息不推出规范共识）

即使：

[
C_\infty\simeq\top_X,
]

两个主体仍可使用不同规范函数：

[
d_1:X\to U,
\qquad
d_2:X\to U,
]

并在同一状态上选择不同。

因此：

[
\boxed{
\text{认识分歧可以被信息解决；
规范分歧不必随信息完整而消失。}
}
]

反之，群体也可能在：

[
C_\infty\prec\top_X
]

时形成一致意见；这种一致可能只是共同盲点。

---

# 151. 回音室定理

设所有消息都来自同一个共同来源概念：

[
S:X\to B_S.
]

即对每个 (n)：

[
M_n\preceq S.
]

## 定理 151.1（共同来源上界）

[
\boxed{
\bigvee_nM_n
\preceq
S.
}
]

### 证明

每个 (M_n) 都由 (S) 计算，故它们的联合也由 (S) 计算。 (\square)

若初始概念也满足：

[
C_0\preceq S,
]

则所有讨论后的概念仍满足：

[
C_\infty\preceq S.
]

---

## 推论 151.2（重复共识不能突破源盲点）

若：

[
E_T\not\preceq S,
]

则任意数量来自 (S) 的：

* 转述；
* 摘要；
* 评论；
* 投票；
* 再训练；
* 多智能体复述；

都不能使目标 (T) 变得可决定。

所以：

[
\boxed{
\text{参与者数量}
\neq
\text{独立信息源数量}.
}
]

突破回音室至少需要一个消息 (M) 满足：

[
M\not\preceq S.
]

即真正引入当前共同来源不能表达的新区别。

---

# 152. 创新的四种类型

固定当前概念 (C)、表达目录 (g) 和状态类型 (X)。

## 152.1 重组创新

新目标：

[
W=f\circ C.
]

于是：

[
E_W\preceq C.
]

它是旧信息的新组合，不增加状态分辨率。

## 152.2 认识创新

加入新概念 (D)，使：

[
\boxed{
C\prec C\vee D.
}
]

它真正缩小不可区分纤维。

## 152.3 表达创新

产生一个不在当前表达目录像中的表达：

[
r\notin\operatorname{range}(g),
]

但其语义仍可能通过 (C) 因子化。

## 152.4 本体创新

对象类型从：

[
X
]

扩张到：

[
X'.
]

出现旧类型中不存在的新对象或角色。

## 152.5 规范创新

改变：

[
\operatorname{Adm},
\qquad
V,
\qquad
\operatorname{Permitted},
]

从而改变什么被接受、追求或禁止。

---

## 定理 152.1（内部计算不产生认识创新）

任何只接收 (C(x)) 的确定性程序：

[
h:B_C\to Y
]

产生的输出：

[
W=h\circ C
]

均满足：

[
E_W\preceq C.
]

所以内部计算可以产生复杂输出、意外组合甚至新的表达，但不能恢复输入概念已经删除的真实区别。

---

## 推论 152.2（对角新颖性不等于新知识）

对角构造可以产生：

[
r\notin\operatorname{range}(g),
]

即表达目录外的新对象。

但这不自动意味着：

[
C\prec C\vee E_r
]

在世界状态概念上成立。

因此：

[
\boxed{
\text{对角化可以产生表示新颖性，
但不必产生关于世界的新增信息。}
}
]

这调和了两条看似冲突的原则：

[
\text{无信息复活}
]

与：

[
\text{自应用表示逃逸}.
]

---

# 153. 信息源依赖形成一般闭包系统，而不必形成向量空间

给定概念族：

[
(C_i)_{i\in I}.
]

对子集 (S\subseteq I)，定义：

[
\boxed{
\operatorname{cl}(S)
====================

\left{
i\in I
;\middle|;
C_i
\preceq
\bigvee_{j\in S}C_j
\right}.
}
]

它表示可由 (S) 中信息源恢复的全部来源。

## 定理 153.1（来源闭包三律）

[
S\subseteq\operatorname{cl}(S),
]

[
S\subseteq T
\Longrightarrow
\operatorname{cl}(S)\subseteq\operatorname{cl}(T),
]

[
\operatorname{cl}(\operatorname{cl}(S))
=======================================

\operatorname{cl}(S).
]

所以信息源依赖天然形成闭包空间。

---

## 定理 153.2（最小生成集大小可以不同）

令：

[
X={0,1}^2.
]

定义：

[
C_1(x_1,x_2)=(x_1,x_2),
]

[
C_2(x_1,x_2)=x_1,
]

[
C_3(x_1,x_2)=x_2.
]

则全部来源的联合概念为 (\top_X)。

它有两个最小生成集：

[
{C_1},
]

和：

[
{C_2,C_3}.
]

前者大小为 (1)，后者大小为 (2)。

因此一般不存在唯一的“独立信息源数量”。

只有在额外满足交换公理等结构时，最小生成集才可能具有统一维数。

所以：

[
\boxed{
\text{认识依赖一般是闭包几何，
而不必是线性代数或 matroid 几何。}
}
]

---

# Part XX：控制、因果涌现、修正与社会选择

# 154. 控制身份是所有可行动后果的规范商

设行动幺半群 (M) 作用于状态类型 (X)：

[
F_m:X\to X.
]

给定结果读出：

[
q:X\to O.
]

定义状态 (x) 的完整控制轮廓：

[
\boxed{
K_{\mathrm{ctl}}(x)(m)
======================

q(F_mx).
}
]

定义控制等价：

[
\boxed{
x\sim_{\mathrm{ctl}}y
\iff
\forall m\in M,\quad
q(F_mx)=q(F_my).
}
]

控制商：

[
\boxed{
Z_{\mathrm{ctl}}
================

X/{\sim_{\mathrm{ctl}}}.
}
]

---

## 定理 154.1（控制商的普适最小性）

(Z_{\mathrm{ctl}}) 是满足以下条件的最粗概念：

1. 当前读出 (q) 可由它恢复；
2. 所有行动 (F_m) 在其上闭合；
3. 所有行动后果 (q(F_mx)) 可由其当前值决定。

这就是动态完成：

[
\operatorname{Dyn}_M(q)
]

的行动论解释。

---

## 定理 154.2（控制身份精化被动预测身份）

若被动世界只允许实际过程子族：

[
P\subseteq M,
]

则：

[
\boxed{
Z_{\mathrm{passive}}
\preceq
Z_{\mathrm{ctl}}.
}
]

因为全部行动相同必推出被动行动相同，反向一般失败。

---

## 最小反模型

令两个状态 (x,y) 在默认行动下都读出 (0)。

但存在替代行动 (u)：

[
q(F_ux)=0,
\qquad
q(F_uy)=1.
]

则 (x,y) 被动不可区分，却控制可区分。

因此：

[
\boxed{
\text{知道世界会怎样自行发展}
\neq
\text{知道世界在可选行动下会怎样发展}.
}
]

主体能力的规范状态不是单一未来 itinerary，而是完整控制轮廓。

---

# 155. 控制原则具有规范的最大保留部分

设完整规范评价：

[
J:X\to L,
]

控制概念为：

[
C_{\mathrm{ctl}}.
]

定义：

[
\boxed{
J_{\mathrm{fair}}
=================

E_J\wedge C_{\mathrm{ctl}}.
}
]

这里 (J_{\mathrm{fair}}) 不是强行把 (J) 变成同一值域中的函数，而是保留 (J) 中所有能够由控制轮廓恢复的最大区别。

## 定理 155.1（最大控制相容评价）

(J_{\mathrm{fair}}) 满足：

[
J_{\mathrm{fair}}\preceq E_J,
]

[
J_{\mathrm{fair}}\preceq C_{\mathrm{ctl}}.
]

若评价概念 (K) 同时满足：

[
K\preceq E_J,
\qquad
K\preceq C_{\mathrm{ctl}},
]

则：

[
\boxed{
K\preceq J_{\mathrm{fair}}.
}
]

所以 (J_{\mathrm{fair}}) 是完整评价中可由主体控制条件合法保留的最精细部分。

---

## 定义 155.1（规范运气余量）

[
\boxed{
\Delta_{\mathrm{luck}}
======================

\ker C_{\mathrm{ctl}}
\setminus
\ker J.
}
]

其元素是控制轮廓完全相同、评价却不同的状态对。

因此对道德运气有两种精确修复：

[
\boxed{
\begin{aligned}
\text{扩大责任概念}
&:\quad
C_{\mathrm{ctl}}\vee E_J;\
\text{压缩评价}
&:\quad
J_{\mathrm{fair}}.
\end{aligned}
}
]

前者把更多外部事实纳入责任；后者放弃无法由控制恢复的评价区别。

哪一种规范上正确，不由形式结构单独决定。

---

# 156. 宏观层可以提高因果效率，但不能创造绝对信息

设：

[
X_t
]

为平稳随机过程，概念：

[
C:X\to B.
]

定义绝对一步预测信息：

[
\boxed{
I_C
===

I(C(X_t);C(X_{t+1})).
}
]

定义概念容量：

[
H_C
===

H(C(X_t)).
]

若 (H_C>0)，定义预测效率：

[
\boxed{
\eta_C
======

\frac{I_C}{H_C}.
}
]

---

## 定理 156.1（粗化不增加绝对预测信息）

由于 (C(X_t)) 和 (C(X_{t+1})) 分别是微观状态的确定函数：

[
\boxed{
I_C
\le
I(X_t;X_{t+1}).
}
]

这是数据处理单调性。

所以宏观层不能凭空产生微观过程中不存在的绝对时间信息。

---

## 定理 156.2（宏观效率可以严格提高）

令：

[
X_t=(S_t,N_t),
]

其中：

[
S_{t+1}=S_t
]

为持久的一位信息，

而：

[
N_{t+1}
]

每一步重新独立均匀采样。

假设 (S_t,N_t) 均为独立均匀 bit。

则：

[
H(X_t)=2,
]

[
I(X_t;X_{t+1})=1,
]

所以：

[
\eta_{\mathrm{micro}}=\frac12.
]

取宏观概念：

[
C(S,N)=S.
]

则：

[
H_C=1,
\qquad
I_C=1,
]

因此：

[
\boxed{
\eta_C=1.
}
]

宏观层删除了无预测价值的噪声，从而提高了单位表示容量中的因果效率。

所以：

[
\boxed{
\text{因果涌现可以表现为效率提高，
而不是绝对信息违反数据处理地增加。}
}
]

---

# 157. 条件化、世界演化与理论修订是三种不同算子

设当前可能状态集合为：

[
A\subseteq X.
]

## 条件化

对命题 (P\subseteq X)：

[
\boxed{
\mathsf{Cond}_P(A)
==================

A\cap P.
}
]

## 世界演化

对过程 (F:X\to Y)：

[
\boxed{
\mathsf{Evol}_F(A)
==================

F[A].
}
]

## 理论修订

当：

[
A\cap P=\varnothing
]

时，仅做条件化会得到空模型。

给定距离 (d)，可定义最近修订：

[
\boxed{
\mathsf{Rev}_{P,d}(A)
=====================

\operatorname{argmin}_{x\in P}d(x,A).
}
]

它可能为空、非唯一或依赖距离。

---

## 定理 157.1（条件化交换）

[
\boxed{
\mathsf{Cond}_P
\mathsf{Cond}_Q
===============

\mathsf{Cond}_Q
\mathsf{Cond}_P.
}
]

因为集合交交换。

---

## 定理 157.2（演化—证据拉回恒等式）

对未来命题 (Q\subseteq Y)：

[
\boxed{
F[A\cap F^{-1}(Q)]
==================

F[A]\cap Q.
}
]

### 证明

若 (y) 属于左侧，则：

[
y=F(x),
\quad
x\in A,
\quad
F(x)\in Q,
]

故 (y\in F[A]\cap Q)。

反向同理。 (\square)

这意味着，对未来证据 (Q)，正确的当前更新是先拉回：

[
F^{-1}(Q),
]

再演化。

---

## 推论 157.3（条件化与演化一般不交换）

一般：

[
F[A\cap P]
\neq
F[A]\cap P,
]

甚至两端可能位于不同状态类型。

因此必须区分：

[
\boxed{
\begin{aligned}
\text{世界变了}
&=\mathsf{Evol};\
\text{得知世界原来如此}
&=\mathsf{Cond};\
\text{旧理论无法容纳证据而被重构}
&=\mathsf{Rev}.
\end{aligned}
}
]

修订算子通常不交换，也未必唯一；其路径依赖来自距离、优先级和保留原则。

---

# 158. 观察公平与反事实公平彼此独立

设保护属性：

[
P:X\to B_P,
]

相关资格：

[
R:X\to B_R,
]

制度决定：

[
J:X\to Y.
]

## 观察公平

在实际准入域上：

[
\boxed{
R(x)=R(y)
\Longrightarrow
J(x)=J(y).
}
]

即决定通过相关概念因子化。

## 反事实公平

对改变保护属性的身份保持干预 (I_g)：

[
\boxed{
J(I_gx)=J(x).
}
]

---

## 定理 158.1（观察公平不推出反事实公平）

令状态为：

[
(p,r)\in{0,1}^2,
]

实际准入只允许：

[
(0,0),(1,1).
]

令：

[
J(p,r)=r.
]

则决定完全通过相关资格 (R=r) 因子化，所以观察公平成立。

但若改变保护属性的干预同时因果性地使：

[
r:=p,
]

则：

[
(0,0)\mapsto(1,1),
]

制度决定从 (0) 变为 (1)。

所以反事实公平失败。

---

## 定理 158.2（反事实公平不推出群体结果均等）

令：

[
J(p,r)=r,
]

保护属性干预只改变 (p)，保持 (r) 不变。

则：

[
J(I_gp,r)=J(p,r),
]

所以反事实公平成立。

但若实际分布满足：

[
r=p
]

几乎处处，则两个保护群体的决定率完全不同。

因此：

[
\boxed{
\text{个体反事实不变性}
\neq
\text{观察群体结果均等}.
}
]

公平不是单一谓词，而是一族不可互换的下降或不变性条件。

---

# 159. 完全对称的民主平局不存在确定性中立裁决

设有两个候选项：

[
a,b,
]

两个选民。

考虑平局偏好：

[
p=(a,b),
]

即第一人选择 (a)，第二人选择 (b)。

设社会选择规则：

[
F:\operatorname{Profile}\to{a,b}.
]

要求：

## 匿名性

交换选民不改变结果：

[
F(\tau q)=F(q).
]

## 中立性

交换候选项会交换结果：

[
F(\sigma q)=\sigma F(q).
]

## 确定性完备

对每个 profile，规则必须唯一选择 (a) 或 (b)。

---

## 定理 159.1（对称平局不可能）

不存在同时满足上述三项的规则。

### 证明

候选交换 (\sigma) 把：

[
p=(a,b)
]

变为：

[
(b,a).
]

选民交换 (\tau) 又把 ((b,a)) 变回 (p)。

所以：

[
\tau\sigma p=p.
]

于是：

[
\begin{aligned}
F(p)
&=
F(\tau\sigma p)\
&=
F(\sigma p)
\qquad\text{由匿名性}\
&=
\sigma F(p)
\qquad\text{由中立性}.
\end{aligned}
]

但候选交换 (\sigma) 在 ({a,b}) 上没有固定点。

矛盾。 (\square)

因此对称平局需要至少一种额外结构：

[
\boxed{
\text{随机化、主席票、时间优先、现状偏好或其他锚点}.
}
]

这些不是从完全对称的偏好数据中推出的。

---

# 160. 对规范理论赋概率并不足以决定行动

设存在多个可能正确的规范 doctrine：

[
N_i.
]

每个 doctrine 在自己的价值空间中评价行动：

[
V_i:A\to L_i.
]

即使赋予 doctrine 概率：

[
p_i,
]

仍不能直接计算：

[
\sum_ip_iV_i(a),
]

因为不同 (L_i) 未必具有共同加法与共同尺度。

若要做期望聚合，必须额外给出：

[
u_i:L_i\to\mathbb R.
]

---

## 定理 160.1（概率不决定跨规范尺度）

考虑两个行动 (a,b)，两个 doctrine，概率各为 (1/2)。

第一 doctrine 只要求：

[
a\succ_1b.
]

第二 doctrine 只要求：

[
b\succ_2a.
]

选取实数表示：

[
u_1(a)=\alpha,
\qquad
u_1(b)=0,
]

[
u_2(a)=0,
\qquad
u_2(b)=\beta,
]

其中：

[
\alpha,\beta>0.
]

这保持两个 doctrine 的内部顺序不变。

聚合期望为：

[
EU(a)=\frac{\alpha}{2},
]

[
EU(b)=\frac{\beta}{2}.
]

若：

[
\alpha>\beta,
]

选择 (a)。

若：

[
\beta>\alpha,
]

选择 (b)。

所以 doctrine 概率和各自内部排序保持完全相同，最终选择却可因跨理论尺度变化而反转。

(\square)

因此：

[
\boxed{
\text{规范不确定性}
+
\text{概率}
\not\Rightarrow
\text{唯一行动}.
}
]

还需要元规范数据：

[
\boxed{
\text{跨理论标度、权利优先级、最坏情形原则、
后悔最小化或共同许可交集}.
}
]

如果全部 doctrine 的许可集交为空，则不存在“所有理论都允许”的行动，必须进入真正的元规范冲突解决。

---

# 161. 第四层统一：从概念闭合走向规律、行动与创新的统一理论

经过 §140–§160，形式概念动力学可以进一步压缩为六个核心判据。

## 161.1 规律判据

[
\boxed{
\text{规律}
=========

\text{局部因子化}
+
\text{跨语境自然性}
+
\text{足够领域覆盖}
+
\text{干预稳定性}.
}
]

单域拟合、删除反例或观察相关性都不足以构成强规律。

---

## 161.2 观察判据

[
\boxed{
\text{观察}
=========

\text{读出}
+
\text{可能的状态 backaction}.
}
]

静态概念天然交换；顺序效应属于仪器和过程层。

---

## 161.3 知识判据

[
\boxed{
\text{知识}
=========

\text{实际锚定的非空证据纤维上的真值稳定}.
}
]

它排除：

* 空纤维上的虚假全知；
* 概率一但存在零测度反例；
* 共识但信息来源完全依赖；
* 讨论重复但没有新观测。

---

## 161.4 行动判据

[
\boxed{
\text{主体的控制状态}
==============

\text{全部可行动后果的最小充分 quotient}.
}
]

被动预测身份和控制身份不同。

责任若超出控制 quotient，便包含道德运气余量。

---

## 161.5 规范判据

[
\boxed{
\text{规范}
=========

\text{作用在状态、行动、路径、关系和准入上的多型 doctrine}.
}
]

结果相同不推出规范相同。

概率化规范不确定性也不能消除跨理论尺度问题。

---

## 161.6 创新判据

[
\boxed{
\begin{aligned}
\text{重组创新}
&=\text{旧可观察代数中的新组合};\
\text{认识创新}
&=\text{严格缩小世界余纤维};\
\text{表达创新}
&=\text{逃逸既有表示目录};\
\text{本体创新}
&=\text{扩张对象类型};\
\text{规范创新}
&=\text{改变 ADMIT 或价值结构}.
\end{aligned}
}
]

内部计算不能产生认识创新，但可以产生重组和表示创新。

---

# 162. 当前最深层总命题

形式哲学中的一个系统，不能只接受“是否内部一致”的单项审计。

它至少必须回答：

[
\boxed{
\begin{aligned}
&\text{依赖是否可由因子映射组合？}\
&\text{局部规律能否跨语境自然运输？}\
&\text{零反例是否只是通过删除领域得到？}\
&\text{观察是否改变了被观察对象？}\
&\text{修复顺序是否产生概念曲率？}\
&\text{干预是否具有非交换相互作用？}\
&\text{规范评价是否依赖历史路径？}\
&\text{证据纤维是空、真、假还是未决定？}\
&\text{共识是否来自独立信息？}\
&\text{新颖性究竟是表达、认识、本体还是规范层的？}\
&\text{主体的被动未来与可控制未来是否相同？}\
&\text{宏观解释提高的是绝对信息还是表示效率？}\
&\text{当前变化是条件化、世界演化还是理论修订？}\
&\text{公平主张是观察性的还是反事实的？}\
&\text{规范不确定性是否偷偷加入了跨理论标度？}
\end{aligned}
}
]

由此，总公式进一步发展为：

[
\boxed{
\begin{aligned}
\textbf{Formal Concept Dynamics}
={}&
\textbf{dependency calculus}\
&+
\textbf{natural laws}\
&+
\textbf{instrument backaction}\
&+
\textbf{conceptual curvature}\
&+
\textbf{control quotients}\
&+
\textbf{path-sensitive normativity}\
&+
\textbf{collective epistemic closure}\
&+
\textbf{typed novelty}.
\end{aligned}
}
]

其最凝练的哲学结论是：

[
\boxed{
\text{世界并不因被正确分类而停止变化；
分类也不因内部闭合而成为规律；
规律不因预测成功而成为因果；
因果不因可控制而自动成为正当；
正当不因多数同意而获得唯一尺度；
创新也不因表达新颖而自动成为新知识。}
]

因此，完整的形式哲学不应追求一个把所有问题压成单一真值的终极概念，而应建立一套能够区分：

[
\boxed{
\text{信息、规律、过程、行动、规范、历史和创新}
}
]

各自闭合条件与失败见证的多层审计系统。
以下从 **§163** 继续。仍然只做纸面推理，不处理 GitHub，也不把新增结论视为已经通过 Lean kernel 的 `Closed` 定理。

---

# Part XXI：信任、证明责任与可审计代理

# 163. 信任不是“相信别人”，而是委托一个目标因子化

设主体 (A) 无法直接观察世界 (X)，主体 (B) 有概念：

[
C_B:X\to B_B.
]

(B) 向 (A) 发送报告：

[
R:B_B\to M.
]

主体 (A) 希望判断目标：

[
T:X\to Y.
]

整个委托链为：

[
X\xrightarrow{C_B}B_B\xrightarrow{R}M.
]

## 定义 163.1（目标相对信任）

称 (A) 对 (B) 在目标 (T) 上可结构性信任，当存在：

[
\overline T:M\to Y
]

满足：

[
\boxed{
T
=

\overline T\circ R\circ C_B.
}
]

因此：

[
\boxed{
\text{信任}
=========

\text{允许通过他人的报告界面完成自己的目标因子化}.
}
]

这不是心理状态定义，而是一个功能充分性定义。

---

## 定理 163.1（信任是目标相对的）

若：

[
T_1
===

f\circ R\circ C_B,
]

并不推出另一个目标 (T_2) 也能通过同一报告链因子化。

因此：

[
\boxed{
\operatorname{Trust}_A(B;T_1)
\not\Rightarrow
\operatorname{Trust}_A(B;T_2).
}
]

“这个来源可信”必须进一步类型化成：

[
\boxed{
\text{对什么目标、什么语境、什么误差范围可信。}
}
]

---

# 164. 可信报告需要真实性与充分性两个独立条件

仅仅：

[
T=\overline T\circ R\circ C_B
]

说明报告若正确产生，就足以决定目标。

但报告可能被主体 (B) 错误地产生。

设真实报告机制为：

[
R_{\mathrm{true}}:X\to M,
]

实际发送机制为：

[
R_{\mathrm{send}}:X\to M.
]

## 定义 164.1（报告真实性）

[
\boxed{
R_{\mathrm{send}}(x)=R_{\mathrm{true}}(x).
}
]

## 定义 164.2（报告充分性）

[
\boxed{
T=\overline T\circ R_{\mathrm{true}}.
}
]

## 定理 164.1（可信性的二因素分解）

若：

[
R_{\mathrm{send}}=R_{\mathrm{true}}
]

且：

[
T=\overline T\circ R_{\mathrm{true}},
]

则：

[
T=\overline T\circ R_{\mathrm{send}}.
]

但两条件彼此不推出。

因此必须区分：

[
\boxed{
\text{诚实}
\neq
\text{有能力提供充分信息}.
}
]

一个主体可以：

* 完全诚实但观察概念太粗；
* 拥有充分观察能力但故意错误报告；
* 两者都满足；
* 两者都不满足。

这是信任理论中的两个正交轴。

---

# 165. 可审计信任必须携带 provenance

报告：

[
m:M
]

本身不足以说明它是怎么产生的。

定义证明携带报告：

[
\boxed{
\operatorname{CertifiedReport}(m)
=================================

\sum_{\pi:\Pi}
\operatorname{Valid}(\pi,m).
}
]

其中 (\pi) 可以包括：

* 数据来源；
* 观测设备；
* 时间；
* 推理程序；
* 中间证明；
* 签名；
* 依赖版本；
* 准入前件。

---

## 定义 165.1（proof-carrying trust）

主体 (A) 接受报告 (m)，仅当存在：

[
\pi
]

使：

[
\operatorname{Valid}(\pi,m).
]

因此：

[
\boxed{
\text{可审计信任}
============

\text{报告值}
+
\text{来源证明}
+
\text{验证规则}.
}
]

这与此前的：

[
\operatorname{Explains}_C(T)
============================

\sum_r\operatorname{Provenance}(r)
]

完全统一。

---

## 定理 165.1（外延正确不等于可接受）

即使两个报告：

[
m_1=m_2,
]

它们也可能拥有不同 provenance：

[
\pi_1,\pi_2,
]

其中一个通过准入，另一个不通过。

所以：

[
\boxed{
\text{报告内容相同}
\not\Rightarrow
\text{认识论地位相同}.
}
]

这给出形式上的“证词来源重要性”。

---

# 166. 委托链中的信任可以组合，但错误预算也组合

设：

[
X\xrightarrow{R_1}M_1\xrightarrow{R_2}M_2\xrightarrow{R_3}Y.
]

如果全部方格精确，则：

[
T=R_3R_2R_1
]

给出精确委托链。

若每一步具有度量误差：

[
\epsilon_i,
]

并且后续映射 Lipschitz 常数分别为：

[
L_2,L_3,
]

则总误差满足：

[
\boxed{
\epsilon_{\mathrm{total}}
\le
L_3L_2\epsilon_1
+
L_3\epsilon_2
+
\epsilon_3.
}
]

这与前面 defect chain rule 同型。

所以：

[
\boxed{
\text{长信任链的风险}
==============

\text{早期误差经过后续 transport 被放大}.
}
]

这适用于：

* 多级官僚体系；
* AI agent delegation；
* 审计链；
* 科学引用链；
* 法律证词；
* 金融数据供应链。

---

# Part XXII：反例覆盖、测试与理论脆弱性

# 167. 反例不是点，而可以形成“测试基”

给定理论概念 (C) 和目标 (T)。

缺陷关系：

[
\Delta(C;T)
===========

{(x,y)\mid Cx=Cy,\ T(x)\neq T(y)}.
]

一个测试：

[
\tau
]

可以覆盖若干缺陷见证。

定义：

[
\operatorname{Cover}(\tau)
\subseteq
\Delta(C;T).
]

## 定义 167.1（完整测试集）

测试族：

[
\mathcal S
]

是完整的，当：

[
\boxed{
\bigcup_{\tau\in\mathcal S}
\operatorname{Cover}(\tau)
==========================

\Delta(C;T).
}
]

---

## 定理 167.1（最小审计集是 set cover）

寻找最少测试覆盖全部已知缺陷，正是：

[
\boxed{
\min
\left{
|\mathcal S|
\mid
\bigcup_{\tau\in\mathcal S}
\operatorname{Cover}(\tau)
==========================

\Delta(C;T)
\right}.
}
]

所以理论验证成本可以转化为覆盖问题。

---

## 推论 167.2

如果某测试族只覆盖：

[
\Delta_0
\subsetneq
\Delta(C;T),
]

那么全部测试通过最多说明：

[
\Delta_0
]

被排除，而不能推出：

[
\Delta(C;T)=\varnothing.
]

因此：

[
\boxed{
\text{测试全部通过}
\not\Rightarrow
\text{理论没有缺陷},
}
]

除非测试族本身具有 completeness certificate。

---

# 168. 最脆弱反例与鲁棒边界

若 (X) 有度量 (d)，定义缺陷距离：

[
\boxed{
\rho(C;T)
=========

\inf
\left{
d(x,y)
\mid
Cx=Cy,\ T(x)\neq T(y)
\right}.
}
]

若无缺陷，设：

[
\rho=+\infty.
]

## 解释

* (\rho=+\infty)：完全充分；
* (\rho>0)：存在缺陷，但需要有限扰动才能触发；
* (\rho=0)：任意小扰动附近都可能出现同概念异目标。

---

## 定理 168.1（零脆弱半径）

若存在序列：

[
x_n,y_n
]

满足：

[
d(x_n,y_n)\to0,
]

[
C(x_n)=C(y_n),
]

[
T(x_n)\neq T(y_n),
]

则：

[
\boxed{
\rho(C;T)=0.
}
]

这定义了概念的 adversarial boundary。

所以一个概念即使在训练分布中表现完美，也可能具有：

[
\rho=0
]

的结构脆弱性。

---

# 169. 鲁棒充分性比普通充分性更强

普通充分性只要求：

[
Cx=Cy\Rightarrow Tx=Ty.
]

鲁棒充分性还要求在小扰动邻域中目标不跨界。

给定 (\varepsilon>0)，定义：

[
\boxed{
\operatorname{RobustSuff}_\varepsilon(C;T)
}
]

当所有距离不超过 (\varepsilon) 且概念不可区分的状态都具有相同目标值。

即：

[
Cx=Cy
\land
d(x,y)\le\varepsilon
\Longrightarrow
Tx=Ty.
]

若普通充分性成立，则任意 (\varepsilon) 都成立。

但在近似概念、量化读出或容差概念中，普通零误差和扰动鲁棒性必须分开。

---

# Part XXIII：主体的层级、身份与自修改

# 170. 主体不是一个状态，而是多个尺度概念的相容族

设主体存在多个层：

[
X_0,X_1,\ldots,X_n.
]

例如：

[
\text{身体}
\to
\text{神经状态}
\to
\text{心理状态}
\to
\text{叙事状态}
\to
\text{法律身份}.
]

层间投影：

[
p_{j,i}:X_j\to X_i.
]

## 定义 170.1（多层主体）

一个主体是：

[
\boxed{
s=(s_i)_i
}
]

满足：

[
p_{j,i}(s_j)=s_i.
]

所以主体身份不是某一个层的点，而是一个跨层相容 cone。

---

## 定理 170.1（单层身份不足）

若某一层投影：

[
p_{j,i}
]

非单射，则：

[
s_i
]

不能唯一恢复：

[
s_j.
]

因此从法律人格、叙事身份或行为身份中，不能无条件恢复微观主体。

反过来，微观状态也不自动决定高层规范身份，除非给出合法 quotient。

---

# 171. 自修改主体需要身份 transport

设主体更新：

[
U:X\to X.
]

若简单要求：

[
U(x)=x,
]

则任何真正修改都会破坏身份。

更合理的是给出身份概念：

[
I:X\to B_I.
]

## 定义 171.1（身份保持修改）

[
\boxed{
I(Ux)=I(x).
}
]

这是“修改了自己，但仍是同一个主体”。

---

## 定义 171.2（能力改变）

设控制轮廓：

[
K_{\mathrm{ctl}}(x).
]

若：

[
I(Ux)=I(x)
]

但：

[
K_{\mathrm{ctl}}(Ux)\neq K_{\mathrm{ctl}}(x),
]

则主体保持身份，但能力发生改变。

这形式化：

[
\boxed{
\text{同一个人可以成为一个不同能力结构的人}.
}
]

---

# 172. 自修改的合法性不能完全由修改后的主体回溯决定

设当前规范：

[
N_x
]

决定哪些修改 (U) 合法。

修改后规范：

[
N_{Ux}.
]

如果只要求：

[
N_{Ux}(U)=\mathsf{True},
]

则主体可以通过一次修改先改变规则，再让新规则批准自身。

这产生循环合法化。

## 定义 172.1（前置合法性）

修改 (U) 在状态 (x) 合法，当：

[
\boxed{
N_x(U)=\mathsf{True}.
}
]

## 定义 172.2（双重合法性）

更强要求：

[
\boxed{
N_x(U)
\land
N_{Ux}(U).
}
]

---

## 定理 172.1（后验自批准不足）

存在修改 (U) 使：

[
\neg N_x(U)
]

但：

[
N_{Ux}(U).
]

因此：

[
\boxed{
\text{修改后认为修改合法}
\not\Rightarrow
\text{修改在原规范下合法}.
}
]

这适用于：

* 宪法修订；
* AI self-modification；
* 人格承诺变化；
* 公司治理规则；
* 法律制度自我修订。

---

# 173. 宪制稳定是规范固定点，不是规则静止

设制度状态 (x) 决定修订规则：

[
R_x.
]

实际修订过程：

[
U_R(x).
]

定义制度规范状态更新：

[
\Phi(x)=U_R(x).
]

## 定义 173.1（宪制稳定）

制度在 (x) 稳定，当：

[
\boxed{
N_{\Phi(x)}
\simeq
N_x
}
]

或者至少其元修订规则保持等价。

这不要求所有法律不变，而只要求：

[
\boxed{
\text{改变法律的规则本身在改变后仍被保留}.
}
]

如果元规则也变化，则需要更高一层 meta-meta rule。

由此出现修订塔：

[
N^{(0)},
N^{(1)},
N^{(2)},\ldots
]

---

# 174. 无有限元层级可以绝对封闭所有自修改规范

假设每一层规范：

[
N^{(k)}
]

都由更高一层：

[
N^{(k+1)}
]

判断其修改是否合法。

如果存在最高层 (N^{(n)})，则还必须回答：

[
\boxed{
\text{谁判断 }N^{(n)}\text{ 自身的修改？}
}
]

有三个选择：

1. 禁止最高层修改；
2. 让最高层自批准；
3. 引入更高层。

第一种牺牲完全自修改能力。

第二种重新引入循环。

第三种没有有限终点。

因此：

[
\boxed{
\text{完全自修改}
+
\text{非循环外部合法化}
+
\text{有限元层级}
}
]

三者不能同时满足。

这是一种元规范 trilemma。

---

# Part XXIV：反思平衡与信念—规范共演化

# 175. 反思平衡是两个闭包算子的耦合固定点

设：

[
B
]

表示事实信念概念，

[
N
]

表示规范 doctrine。

规范会决定哪些事实相关：

[
R(N).
]

事实又会暴露规范反例：

[
D(B,N).
]

定义更新：

[
\boxed{
\Phi_B(B,N)
===========

B\vee E_{R(N)},
}
]

[
\boxed{
\Phi_N(B,N)
===========

\operatorname{Repair}(N;D(B,N)).
}
]

联合更新：

[
\boxed{
\Phi(B,N)
=========

(\Phi_B(B,N),\Phi_N(B,N)).
}
]

## 定义 175.1（反思平衡）

[
\boxed{
(B^*,N^*)
}
]

满足：

[
\Phi(B^*,N^*)
=============

(B^*,N^*).
]

即：

* 当前规范不再要求新的事实区别；
* 当前事实不再迫使规范修订。

---

## 定理 175.1（有限单调系统终止）

若：

* (B,N) 所在序集有限；
* 更新单调；
* 每次非固定更新严格精化或严格推进；

则迭代有限步达到固定点。

但不同初始状态可能进入不同固定点。

所以：

[
\boxed{
\text{反思平衡存在}
\not\Rightarrow
\text{反思平衡唯一}.
}
]

---

# 176. 多固定点意味着哲学世界观可能局部自洽却彼此不可归并

若联合更新 (\Phi) 有两个固定点：

[
(B_1,N_1),
\qquad
(B_2,N_2),
]

且：

[
(B_1,N_1)
\not\preceq
(B_2,N_2),
]

反向也不成立，则存在多个不可比较的稳定哲学体系。

这不是简单“谁都可以”。

还需比较：

* 实现域；
* 预测能力；
* 解释复杂度；
* 规范代价；
* 外部反例；
* 对新观察的稳定性。

所以：

[
\boxed{
\text{内部稳定}
\neq
\text{全局优越}.
}
]

---

# 177. 反思平衡的吸引域解释思想传统

给定更新算子 (\Phi)，定义固定点 (z^*) 的吸引域：

[
\boxed{
\operatorname{Basin}(z^*)
=========================

{z\mid \Phi^n(z)\to z^*}.
}
]

不同初始概念和价值可能落入不同吸引域。

于是“哲学传统”可以被形式重构为：

[
\boxed{
\text{一组初始状态在同一反思修订动力学下收敛到同一稳定结构}.
}
]

这比把传统理解成“共享一组教条”更动态。

---

# Part XXV：解释、压缩与科学理论选择

# 178. 最短解释不是最真解释，除非复杂度 doctrine 被显式给出

设所有足以决定目标 (T) 的解释程序集合为：

[
\mathcal P_T.
]

给程序长度：

[
K(p).
]

定义最短解释：

[
p^*
===

\operatorname{argmin}_{p\in\mathcal P_T}K(p).
]

但最短长度来自一个编码语言。

换一个编码：

[
K'(p)
]

可能改变有限对象上的排序。

因此：

[
\boxed{
\text{最短解释}
}
]

不是绝对概念，而是相对于表示语言和复杂度 doctrine。

---

## 定理 178.1（有限解释排序的编码依赖）

对有限解释集合：

[
{p_1,\ldots,p_n},
]

可以构造前缀编码，使指定某个 (p_i) 获得最短编码。

所以在没有约束编码语言时：

[
\boxed{
\text{“最短”不能唯一选出客观解释}.
}
]

只有在限制到某类可接受通用语言，并接受不变性常数以后，复杂度最小化才有更强意义。

---

# 179. 简单性和预测充分性是两条独立轴

定义：

[
\operatorname{Suff}(C;T)
]

以及复杂度：

[
K(C).
]

一种理论选择可以解：

[
\boxed{
\min_C K(C)
\quad
\text{s.t.}
\quad
E_T\preceq C.
}
]

也可以允许误差：

[
\boxed{
\min_C
\left[
K(C)
+
\lambda,\operatorname{Defect}(C;T)
\right].
}
]

这给出理论选择的 Pareto 边界：

[
\boxed{
\text{复杂度}
\leftrightarrow
\text{缺陷}.
}
]

没有 (\lambda) 或其他 doctrine 时，不存在唯一最优折中。

这与：

* MDL；
* Occam；
* 模型压缩；
* 科学理论选择；

结构一致。

---

# 180. 理论越压缩，潜在问题空间越大

若：

[
C\preceq D,
]

则 (D) 更精细。

由此前结果：

[
\Delta(D;T)
\subseteq
\Delta(C;T)
]

对任意固定 (T)。

因此更粗概念 (C) 对更多目标容易产生缺陷。

定义目标族：

[
\mathcal T.
]

理论风险：

[
\boxed{
\mathcal R(C;\mathcal T)
========================

{T\in\mathcal T\mid \Delta(C;T)\neq\varnothing}.
}
]

## 定理 180.1（精化单调降低目标风险）

若：

[
C\preceq D,
]

则：

[
\boxed{
\mathcal R(D;\mathcal T)
\subseteq
\mathcal R(C;\mathcal T).
}
]

所以压缩越强，潜在失败目标集合越大。

但精化成本也通常越高。

由此理论选择本质上是：

[
\boxed{
\text{压缩收益}
\leftrightarrow
\text{未来目标风险}.
}
]

---

# Part XXVI：制度、博弈与自实现分类

# 181. 分类可以改变被分类者，从而使“真值”成为固定点问题

设制度使用概念：

[
C:X\to B.
]

被分类者响应分类结果：

[
R:B\times X\to X.
]

实际闭环更新：

[
\boxed{
F_C(x)=R(Cx,x).
}
]

分类后的新分类为：

[
\boxed{
\Psi_C(x)
=========

C(F_Cx).
}
]

## 定义 181.1（分类自实现）

状态 (x) 对分类 (C) 自实现，当：

[
\boxed{
\Psi_C(x)=C(x).
}
]

即被贴标签以后，主体响应最终仍支持原标签。

---

## 定义 181.2（分类自破坏）

若：

[
\Psi_C(x)\neq C(x),
]

则分类行为本身破坏了原分类。

因此制度分类不是单纯读取：

[
X\to B,
]

而是一个闭环：

[
\boxed{
X
\xrightarrow{C}
B
\xrightarrow{\text{response}}
X
\xrightarrow{C}
B.
}
]

---

# 182. 稳定社会分类是闭环固定点

定义：

[
\Theta_C(x)=F_C(x).
]

若：

[
\Theta_C(x^*)=x^*,
]

则状态在分类—响应闭环下稳定。

但更弱的分类稳定只要求：

[
C(\Theta_Cx)=C(x).
]

所以存在：

[
\boxed{
\text{状态固定点}
\Rightarrow
\text{分类固定点},
}
]

反向不成立。

主体可能不断变化，但始终被制度归入同一类别。

这可对应：

* 信用评分；
* 犯罪风险标签；
* 教育分层；
* 社会阶层；
* 身份政治；
* 医疗诊断。

---

# 183. 制度分类可能制造自己声称“发现”的规律

假设初始世界中目标 (T) 不由概念 (C) 决定：

[
E_T\not\preceq C.
]

但分类诱导过程 (F_C) 后：

[
T\circ F_C
]

可能通过 (C) 因子化。

于是：

[
\boxed{
E_{T\circ F_C}\preceq C
}
]

即制度使标签变成预测性的。

这不证明标签原本揭示了本体事实。

它可能是：

[
\boxed{
\text{制度先分类，再通过差异化处理制造分类后果}.
}
]

因此必须区分：

[
\begin{aligned}
\text{发现性预测}
&:\quad T\preceq C;\
\text{表演性预测}
&:\quad T\circ F_C\preceq C.
\end{aligned}
]

两者经验上可能表现出相同高准确率。

---

# 184. 公平审计必须区分“标签预测力来源”

若群体标签：

[
G
]

在干预前不能决定结果：

[
E_T\not\preceq G,
]

但制度流程 (F_G) 后：

[
E_{T\circ F_G}\preceq G,
]

则标签的高预测性是制度内生的。

因此：

[
\boxed{
\text{高预测相关性}
\not\Rightarrow
\text{群体属性本身具有因果本质}.
}
]

公平审计必须比较：

[
T
]

与：

[
T\circ F_G.
]

---

# Part XXVII：自指、预测者与反身行动

# 185. 预测公开以后，主体可以使预测失效

设预测器：

[
P:X\to A
]

预测主体将采取动作 (A(x))。

若主体看到预测结果后可以选择相反动作，设无固定点反应：

[
\tau:A\to A,
\qquad
\tau(a)\neq a.
]

定义主体策略：

[
\boxed{
S(x)
====

\tau(P(x)).
}
]

如果预测器声称：

[
P(x)=S(x)
]

对所有 (x) 成立，则：

[
P(x)
====

\tau(P(x)),
]

矛盾。

## 定理 185.1（公开预测对抗定理）

若主体：

1. 能读取预测器对自己的预测；
2. 有能力实施无固定点反应 (\tau)；
3. 预测器目标是准确预测最终动作；

则不存在对所有状态都正确的公开确定预测器。

这是对角结构在行动论中的版本。

---

## 边界

若：

* 主体看不到预测；
* 主体不能反向行动；
* (\tau) 有固定点；
* 预测是概率性的；
* 主体不是完全响应预测；

结论都需要重新分析。

所以它不是“自由意志证明”，而是：

[
\boxed{
\text{公开自相关预测}
+
\text{可执行对抗响应}
}
]

之间的不相容。

---

# 186. 自我知识也可能改变被认识对象

设主体内部状态：

[
x\in X.
]

自我认识过程：

[
K:X\to B
]

同时引发状态更新：

[
U_K:X\to X.
]

若主体知道自己是：

[
b=K(x),
]

但这一知识导致：

[
K(U_Kx)\neq b,
]

则出现反思不稳定。

## 定义 186.1（反思稳定自知识）

[
\boxed{
K(U_Kx)=K(x).
}
]

所以某些自我描述不是单纯真假问题，而是：

[
\boxed{
\text{被知道后是否仍然保持为真}.
}
]

这适用于：

* “我不会改变主意”；
* “我现在没有焦虑”；
* “我会在知道预测后按原计划行动”；
* “这个市场策略一旦公开仍然有效”。

---

# 187. 反思真理比普通真理更强

普通真理：

[
P(x).
]

反思真理要求：

[
P(x)
]

并且在得知 (P) 后：

[
P(U_Px).
]

更强地，定义稳定闭包：

[
U_P^n.
]

## 定义 187.1（反思稳健真理）

[
\boxed{
\forall n\ge0,\quad
P(U_P^nx).
}
]

因此：

[
\boxed{
\text{真}
\neq
\text{知道后仍真}
\neq
\text{反复知道后仍真}.
}
]

这为反身经济学、社会预测与主体哲学引入新的真理层级。

---

# Part XXVIII：理论之间的可比较性与元理论

# 188. 两个理论的比较需要共同目标语言

设理论：

[
C_1:X\to B_1,
\qquad
C_2:X\to B_2.
]

如果没有目标族：

[
\mathcal T,
]

说“(C_1) 比 (C_2) 好”没有充分定义。

相对于目标族定义支配：

[
\boxed{
C_1\succeq_{\mathcal T}C_2
}
]

当对每个 (T\in\mathcal T)：

[
\Delta(C_1;T)
\subseteq
\Delta(C_2;T).
]

如果还考虑成本：

[
K(C),
]

则只有 Pareto 比较：

[
\boxed{
\text{缺陷更少}
\quad\text{且}\quad
\text{成本不更高}.
}
]

所以：

[
\boxed{
\text{理论比较永远隐含一个目标集合与资源模型}.
}
]

---

# 189. “统一理论”可以精确定义为共同充分概念

给多个领域目标族：

[
\mathcal T_1,\ldots,\mathcal T_n.
]

每个领域的最小概念：

[
E_i
===

\bigvee_{T\in\mathcal T_i}E_T.
]

统一理论最小概念：

[
\boxed{
U
=

E_1\vee\cdots\vee E_n.
}
]

它是同时足以决定全部领域目标的最粗共同概念。

因此统一不是：

[
\text{用一个词解释所有东西},
]

而是：

[
\boxed{
\text{找到一个共同状态表示，使所有领域目标都可以因子化。}
}
]

---

## 定义 189.1（统一增量）

第 (j) 个领域加入已有统一理论 (U_{j-1}) 所需的新信息：

[
\boxed{
\Delta_j
========

H(E_j\mid U_{j-1})
}
]

在有限概率模型中。

若：

[
\Delta_j=0,
]

则新领域已被旧统一结构决定。

若：

[
\Delta_j>0,
]

则它贡献真正的新区别。

这可以定量比较所谓“统一”究竟是：

* 真正跨领域压缩；
* 还是简单把多个独立变量并排拼接。

---

# 190. 伪统一与真统一

若：

[
U=E_1\vee E_2
]

但：

[
E_1,E_2
]

彼此没有共同因子，也没有规律耦合，则只是并置。

定义共同核心：

[
\boxed{
K=E_1\wedge E_2.
}
]

若：

[
K=\bot,
]

且动力学也完全分离，则所谓“统一理论”只是产品：

[
\boxed{
\text{juxtaposition}.
}
]

若存在非平凡：

[
K\neq\bot
]

或共同机制 (M) 使两个领域目标均通过 (M) 因子化，则存在真正结构统一。

因此：

[
\boxed{
\text{统一}
\neq
\text{把所有变量放进一个大 tuple}.
}
]

真正统一至少需要：

[
\boxed{
\text{共同因子、共同机制或共同普适性质}.
}
]

---

# Part XXIX：元不完备与开放哲学

# 191. 任何固定目标族都有相对完备概念

给固定目标族：

[
\mathcal T.
]

定义：

[
\boxed{
C_{\mathcal T}
==============

\bigvee_{T\in\mathcal T}E_T.
}
]

则：

[
E_T\preceq C_{\mathcal T}
]

对全部 (T\in\mathcal T)。

因此：

[
\boxed{
\text{相对于固定目标族，概念完备性总是可定义的。}
}
]

这说明“没有任何形式体系可以完备”太强。

正确说法是：

[
\boxed{
\text{完备性永远相对于对象域、目标族、表示语言和准入规则。}
}
]

---

# 192. 哲学开放性来自目标生成器，而不是固定目标本身

设当前概念：

[
C.
]

如果目标族固定，则：

[
C_{\mathcal T}
]

给出最终充分概念。

真正开放需要一个目标生成器：

[
\boxed{
G:
\operatorname{Con}(X)
\to
\mathcal P(\operatorname{Target}(X)).
}
]

使当前概念本身决定新的问题。

迭代：

[
C_{n+1}
=

C_n
\vee
\bigvee_{T\in G(C_n)}E_T.
]

如果存在固定点：

[
C^*
===

C^*
\vee
\bigvee_{T\in G(C^*)}E_T,
]

则当前问题生成机制被关闭。

若对所有 (C) 都能产生新目标：

[
E_T\not\preceq C,
]

则不存在固定点。

---

# 193. 自我批判能力与最终闭合之间存在张力

定义体系的自我批判能力：

[
\operatorname{Crit}(C)
]

返回一个当前体系内部可构造的审计目标。

若对所有 (C)：

[
\operatorname{Crit}(C)
\preceq C,
]

则批判永远只能说出已有概念能够表达的东西。

此时系统可能闭合，但自批判不产生真正新区别。

若要求真正批判：

[
E_{\operatorname{Crit}(C)}
\not\preceq C,
]

则每次批判迫使严格 refinement。

因此：

[
\boxed{
\text{完全闭合}
\quad\text{与}\quad
\text{永久产生真实新批判}
}
]

不能在固定有限概念格中同时成立。

---

# 194. 哲学的“终结”有四种完全不同含义

必须区分：

## 目标终结

固定目标族全部可决定：

[
\forall T\in\mathcal T,\quad
E_T\preceq C.
]

## 动力终结

所有相关过程都下降：

[
\forall F,\quad
F^*C\preceq C.
]

## 表达终结

全部允许表达都在当前目录像中。

## 问题终结

目标生成器不再产生新目标：

[
G(C)\subseteq
{T\mid E_T\preceq C}.
]

一个体系可以目标完备但问题未终结。

这可能是哲学持续发展的真正形式原因。

---

# 195. 最终统一：从“真理体系”转向“可审计生成体系”

到目前为止，整个框架已经不再适合被理解为一个静态的“真理集合”。

更准确的对象是：

[
\boxed{
\mathfrak P
===========

(
X,
\operatorname{Con}(X),
\operatorname{Target},
\operatorname{Flow},
\operatorname{Adm},
\operatorname{Anchor},
\operatorname{Crit},
\operatorname{Repair},
\operatorname{Provenance}
).
}
]

它需要同时规定：

[
\begin{aligned}
\text{世界是什么}
&:\quad X;\
\text{如何区分}
&:\quad\operatorname{Con}(X);\
\text{要回答什么}
&:\quad\operatorname{Target};\
\text{世界如何变化}
&:\quad\operatorname{Flow};\
\text{什么可实现}
&:\quad\operatorname{Adm};\
\text{实际站在哪里}
&:\quad\operatorname{Anchor};\
\text{如何发现缺陷}
&:\quad\operatorname{Crit};\
\text{如何修复}
&:\quad\operatorname{Repair};\
\text{为什么接受这个结论}
&:\quad\operatorname{Provenance}.
\end{aligned}
]

所以一套真正成熟的哲学不是：

[
\boxed{
\text{“我拥有最终答案”},
}
]

而是：

[
\boxed{
\text{“对于每个答案，我能够说明它依赖什么；
对于每个失败，我能够构造见证；
对于每个修复，我能够说明增加了什么、删除了什么；
对于每个新问题，我能够判断它是否真的超出了当前概念。”}
}
]

---

# 196. 当前最深的新结论

把 §163–§195 压缩，出现了五条新的承重结论。

第一，**信任是代理因子化，而不是人格标签**：

[
\boxed{
\text{Trust}(B;T)
=================

T\text{ 能否通过 }B\text{ 的报告链因子化}.
}
]

第二，**理论验证本身有组合复杂度**：

[
\boxed{
\text{最小测试}
===========

\text{缺陷覆盖问题}.
}
]

第三，**主体身份、能力和规范可以分别变化**：

[
\boxed{
\text{Identity}
\neq
\text{Control Profile}
\neq
\text{Normative State}.
}
]

第四，**制度或主体一旦读取预测并响应预测，就进入反身系统**：

[
\boxed{
\text{预测}
\to
\text{行动}
\to
\text{被预测对象改变}.
}
]

第五，也是最重要的：

[
\boxed{
\text{哲学完备性不是绝对属性；
它只相对于固定目标族成立。
哲学开放性来自能够生成当前体系尚不能回答的新问题。}
}
]

于是整套理论的最高层形式变成：

[
\boxed{
\textbf{Philosophy}
===================

\textbf{a self-auditing process that generates targets,
constructs factorization proofs,
locates defects,
repairs interfaces,
and tracks the provenance and cost of every repair.}
}
]

这时“哲学是什么”已经可以得到一个很严格的回答：

[
\boxed{
\textbf{哲学不是答案的集合，而是关于“什么能从什么推出、什么不能，以及缺了什么”的形式科学。}
}
]
以下从 **§197** 继续。仍然只进行纸面推理，不处理 GitHub，也不把新增命题标记为已经获得 Lean proof term 的 `Closed` 结论。

---

# Part XXX：问题、实验与主动认识

# 197. 问题本身就是一个概念

设状态类型为 (X)。一个问题并不只是自然语言句子，而是一个答案映射：

[
\boxed{
Q:X\to A_Q.
}
]

其中 (A_Q) 是允许的答案类型。

例如：

[
\begin{aligned}
Q_{\mathrm{yes/no}}&:X\to\mathbf 2,\
Q_{\mathrm{identity}}&:X\to I,\
Q_{\mathrm{prediction}}&:X\to Y,\
Q_{\mathrm{normative}}&:X\to L.
\end{aligned}
]

因此，一个问题恰好诱导目标概念：

[
E_Q=(A_Q,Q).
]

## 定义 197.1（可回答性）

问题 (Q) 能由概念 (C) 回答，当：

[
\boxed{
E_Q\preceq C.
}
]

也就是存在：

[
\overline Q:B_C\to A_Q
]

使：

[
Q=\overline Q\circ q_C.
]

## 定理 197.1（可回答性判据）

假设状态空间 (X) 非空。

以下等价：

[
E_Q\preceq C,
]

[
q_C(x)=q_C(y)\Longrightarrow Q(x)=Q(y),
]

[
\Delta(C;Q)=\varnothing.
]

所以：

[
\boxed{
\text{一个问题能否回答}
===============

\text{它是否在当前概念的每个余纤维上恒定}.
}
]

---

## 定义 197.2（问题精化）

问题 (Q_1) 比 (Q_2) 更精细，当：

[
\boxed{
E_{Q_2}\preceq E_{Q_1}.
}
]

即知道 (Q_1) 的答案足以恢复 (Q_2) 的答案。

联合问题：

[
Q_1\vee Q_2:
x\mapsto(Q_1(x),Q_2(x)).
]

所以问题也形成与概念相同的精化格。

这意味着哲学研究的第一步不是立即回答问题，而应先判断：

[
\boxed{
\text{当前证据界面是否具有回答该问题所需的分辨率。}
}
]

---

# 198. 被动实验族的识别定理

设可用实验由索引集 (U) 参数化，每个被动实验为：

[
E_u:X\to O_u.
]

“被动”表示实验只读出状态，不改变状态。

对实验子集 (S\subseteq U)，定义联合实验概念：

[
\boxed{
E_S(x)=\bigl(E_u(x)\bigr)_{u\in S}.
}
]

## 定义 198.1（实验可识别性）

目标 (T:X\to Y) 可由实验集 (S) 识别，当：

[
\boxed{
E_T\preceq E_S.
}
]

## 定理 198.1（实验识别判据）

以下等价：

[
E_T\preceq E_S,
]

[
\bigcap_{u\in S}\ker E_u
\subseteq
\ker T,
]

[
\forall x,y,\quad
\left[
\forall u\in S,\ E_u(x)=E_u(y)
\right]
\Longrightarrow
T(x)=T(y).
]

所以一个实验族足够，当且仅当所有在实验上不可区分的状态，在目标上也不可区分。

---

## 定义 198.2（完整被动观察概念）

[
\boxed{
E_{\mathrm{all}}
================

\bigvee_{u\in U}E_u.
}
]

所有被动实验能够识别的目标恰好是：

[
\boxed{
{T\mid E_T\preceq E_{\mathrm{all}}}.
}
]

这给出了一个实验制度的绝对边界：

> 当前实验体系能回答什么，不由研究者的推理能力决定，而由全部实验联合后留下的余纤维决定。

---

# 199. 自适应实验协议

被动实验不必一次全部执行。后一个实验可以依赖此前结果。

## 定义 199.1（有限自适应协议）

一个协议是一棵有限决策树：

* 每个内部节点选择实验 (u)；
* 边由实验输出标记；
* 下一实验可以依赖此前全部输出；
* 叶节点给出最终回答。

对每个状态 (x)，协议产生一条完整 transcript：

[
\boxed{
\operatorname{Tr}_{\pi}(x).
}
]

所以任何自适应协议仍然诱导一个概念：

[
\operatorname{Tr}*{\pi}:X\to B*{\pi}.
]

## 定理 199.1（自适应识别）

协议 (\pi) 能精确回答目标 (T)，当且仅当：

[
\boxed{
E_T\preceq\operatorname{Tr}_{\pi}.
}
]

即目标在每个叶节点对应的状态集合上恒定。

---

## 定理 199.2（二值实验深度下界）

假设当前已经知道概念 (C)，后续每个实验只有两个结果。

定义每个当前纤维中的目标多样性：

[
N_b
===

\left|
{T(x)\mid C(x)=b}
\right|.
]

令：

[
m^*(C;T)=\max_bN_b.
]

若一个最坏深度为 (d) 的二值自适应协议能够回答 (T)，则：

[
\boxed{
d\ge
\left\lceil
\log_2m^*(C;T)
\right\rceil.
}
]

### 证明

深度 (d) 的二叉树最多有：

[
2^d
]

个叶节点。

在某个 (C)-纤维中若有 (m^*) 个不同目标值，则协议至少需要 (m^*) 个不同叶节点区分它们。因此：

[
2^d\ge m^*.
]

(\square)

---

## 定理 199.3（无约束二值问题下的可达性）

如果允许任意设计二值问题，则存在深度：

[
\boxed{
\left\lceil
\log_2m^*(C;T)
\right\rceil
}
]

的协议精确识别 (T)。

### 构造

在每个 (C)-纤维中，为不同目标值分配长度：

[
\left\lceil\log_2m^*\right\rceil
]

的二进制编码，逐位询问即可。

因此，在无实验限制时：

[
\boxed{
\text{最小自适应询问深度}
================

\text{最坏情形精确修复位数}.
}
]

---

# 200. 自适应性不能突破被动实验的联合盲点

对所有被动实验构造：

[
E_{\mathrm{all}}
================

\bigvee_{u\in U}E_u.
]

## 定理 200.1（被动自适应上界）

任何只使用实验族 (U) 的确定性自适应协议，其 transcript 都通过 (E_{\mathrm{all}}) 因子化：

[
\boxed{
\operatorname{Tr}*{\pi}\preceq E*{\mathrm{all}}.
}
]

### 证明

若两个状态在所有实验 (E_u) 上结果相同，则协议在第一步得到相同结果，从而选择相同的第二实验；归纳地，整条路径完全相同。 (\square)

## 推论 200.2

若：

[
E_T\not\preceq E_{\mathrm{all}},
]

则不存在任何自适应协议能够精确识别 (T)。

所以：

[
\boxed{
\text{自适应性可以降低实验成本，
但不能突破全部被动实验共同留下的余纤维。}
}
]

要突破该边界，必须：

* 引入新的实验；
* 改变对象；
* 进行干预；
* 扩大观测类型；
* 或增加领域前件。

---

# 201. 主动实验与经验商

被动观察只读取当前状态。主动实验先改变状态，再读取结果。

设：

[
F_u:X\to X
]

为干预，

[
O:X\to B_O
]

为公共读出。

对行动序列：

[
\alpha=(u_1,\ldots,u_n),
]

定义结果轨迹：

[
\boxed{
\operatorname{Trace}_{\alpha}(x)
================================

\left(
O(x),
O(F_{u_1}x),
O(F_{u_2}F_{u_1}x),
\ldots
\right).
}
]

## 定义 201.1（实验等价）

[
\boxed{
x\sim_{\mathrm{exp}}y
\iff
\forall\alpha,\quad
\operatorname{Trace}_{\alpha}(x)
================================

\operatorname{Trace}_{\alpha}(y).
}
]

实验商：

[
\boxed{
Z_{\mathrm{exp}}
================

X/{\sim_{\mathrm{exp}}}.
}
]

## 定理 201.1（经验商的普适性）

任何由允许干预和公共读出构成的实验协议，其输出都通过：

[
Z_{\mathrm{exp}}
]

因子化。

反之，任何在 (\sim_{\mathrm{exp}})-类上恒定的目标，都原则上可以视为该实验制度下的经验目标。

所以：

[
\boxed{
\text{经验可识别的对象}
===============

\text{实验商上的函数}.
}
]

若目标在同一实验类中变化，则它在当前实验制度下不可识别，无论进行多少推理。

---

# 202. 实验的目标相对价值

设当前概念为 (C)，新增实验为 (E)，目标为 (T)。

定义新增实验修复的缺陷对：

[
\boxed{
\operatorname{Gain}(E;C,T)
==========================

\Delta(C;T)
\setminus
\Delta(C\vee E;T).
}
]

它包含：

> 原本被 (C) 错误合并，但经实验 (E) 后被分开的目标相关状态对。

## 定义 202.1（目标无关实验）

若：

[
\operatorname{Gain}(E;C,T)=\varnothing,
]

则 (E) 对目标 (T) 没有结构增益。

这并不表示 (E) 没有信息，只表示它增加的区别与当前目标无关。

---

## 定理 202.1（实验精化的收益单调性）

若：

[
E\preceq E',
]

即 (E') 更精细，则：

[
\boxed{
\operatorname{Gain}(E;C,T)
\subseteq
\operatorname{Gain}(E';C,T).
}
]

因为：

[
C\vee E\preceq C\vee E',
]

所以更精细实验不会重新引入已经删除的目标缺陷。

---

# 203. 不存在脱离目标的唯一最佳实验

设实验概念 (E_1,E_2) 不可比较：

[
E_1\not\preceq E_2,
\qquad
E_2\not\preceq E_1.
]

取目标：

[
T_1=E_1,
\qquad
T_2=E_2.
]

则：

[
E_{T_1}\preceq E_1,
]

但：

[
E_{T_1}\not\preceq E_2.
]

反之：

[
E_{T_2}\preceq E_2,
]

但：

[
E_{T_2}\not\preceq E_1.
]

## 定理 203.1（目标相对实验优越性）

若两个实验在精化序中不可比较，则存在目标使 (E_1) 严格优于 (E_2)，也存在目标使 (E_2) 严格优于 (E_1)。

因此：

[
\boxed{
\text{实验的绝对信息优越性}
=================

\text{概念精化关系};
}
]

而在不可比较实验之间，优越性必然依赖目标。

---

# Part XXXI：来源代数、信任韧性与分布式证明

# 204. provenance 构成一个证明来源代数

设基础来源为：

[
s_1,\ldots,s_n.
]

对每个结论 (c)，不只记录它是否成立，还记录它依赖哪些来源。

用单调布尔表达式：

[
\varphi_c(s_1,\ldots,s_n)
]

表示来源条件。

解释规则：

[
\begin{aligned}
s_i
&=\text{直接来源 }i;\
\varphi\land\psi
&=\text{两个来源条件都需要};\
\varphi\lor\psi
&=\text{存在任一替代证明路径即可}.
\end{aligned}
]

## 定义 204.1（来源组合）

若一个推理规则需要全部前件：

[
c_1,\ldots,c_k,
]

则该推理路径的 provenance 为：

[
\varphi_{c_1}\land\cdots\land\varphi_{c_k}.
]

若结论有多个不同推理路径，则总 provenance 为这些路径的析取。

---

## 定理 204.1（来源语义正确性）

在有限无环证明图中，对任意可用来源集合 (S)：

[
\boxed{
\varphi_c(S)=\mathsf{True}
}
]

当且仅当存在一条只使用 (S) 中来源的有效证明路径得到 (c)。

### 证明

对证明图拓扑顺序归纳：

* 基础来源按定义成立；
* 合取对应规则全部前件可用；
* 析取对应至少一条证明路径可用。

(\square)

所以 provenance 不是附加注释，而是结论可获得性的逻辑函数。

---

# 205. 最小证明支持与来源割集

## 定义 205.1（最小支持）

来源集合 (S) 是结论 (c) 的最小支持，当：

[
\varphi_c(S)=\mathsf{True},
]

且任意真子集：

[
R\subsetneq S
]

都不能支持 (c)。

记全部最小支持为：

[
\mathcal M_c.
]

## 定义 205.2（来源割集）

集合 (H) 是结论 (c) 的来源割集，当移除 (H) 后结论不可再证明。

## 定理 205.1（割集—击中集对偶）

(H) 是来源割集，当且仅当：

[
\boxed{
\forall S\in\mathcal M_c,\quad
H\cap S\neq\varnothing.
}
]

即 (H) 必须击中所有最小证明支持。

所以：

[
\boxed{
\text{证明韧性}
===========

\text{最小支持超图的最小击中集大小}.
}
]

这与此前的信息冗余和不一致核修复形成同一个超图对偶。

---

# 206. 回音室的 provenance 定理

假设有 (m) 个报告：

[
r_1,\ldots,r_m,
]

但它们全部来自同一基础来源 (s)。

那么：

[
\varphi_{r_i}=s.
]

“至少一个报告支持结论”的 provenance 为：

[
s\lor s\lor\cdots\lor s.
]

在布尔代数中：

[
\boxed{
s\lor\cdots\lor s=s.
}
]

所以无论报告数量多少，最小来源割仍为：

[
{s}.
]

---

如果 (m) 个报告分别来自独立来源：

[
s_1,\ldots,s_m,
]

并且任一来源都足以支持结论，则：

[
\varphi_c
=========

s_1\lor\cdots\lor s_m.
]

要摧毁全部支持，必须删除所有来源：

[
\boxed{
\text{最小割大小}=m.
}
]

因此：

[
\boxed{
\text{报告数量不等于证据冗余；
真正冗余由最小独立 provenance 支持决定。}
}
]

---

# 207. Byzantine 报告的精确阈值

设有 (n) 个具有可验证身份的报告者。

最多 (f) 个报告者可以任意作恶。

所有诚实报告者都报告同一真实二值：

[
b\in{0,1}.
]

采用严格多数规则。

## 定理 207.1（多数恢复充分条件）

若：

[
\boxed{
n>2f,
}
]

则严格多数必然恢复真实值 (b)。

### 证明

诚实报告数至少为：

[
n-f.
]

恶意报告数至多为：

[
f.
]

由 (n>2f) 得：

[
n-f>f.
]

故真实报告严格占多数。 (\square)

---

## 定理 207.2（最坏情形必要性）

若：

[
n\le2f,
]

则不存在仅根据报告向量、对所有允许攻击都正确恢复真实值的确定性规则。

### 证明构造

因为：

[
2(n-f)\le n,
]

可以选择两个不相交集合：

[
H_0,H_1
]

且：

[
|H_0|=|H_1|=n-f.
]

构造同一个报告向量：

* (H_0) 报告 (0)；
* (H_1) 报告 (1)；
* 其余位置任意。

世界 (W_0) 中，(H_0) 为诚实集合，真值为 (0)。

世界 (W_1) 中，(H_1) 为诚实集合，真值为 (1)。

同一报告向量对应两个不同真值，任何规则至少在一个世界失败。 (\square)

因此：

[
\boxed{
n>2f
}
]

是这一简单报告模型中的精确阈值。

---

# 208. Quorum 相交与 (n>3f) 条件

设系统有 (n) 个主体，最多 (f) 个 Byzantine。

每个决议需要 quorum 大小 (q)。

两个 quorum 的交集至少为：

[
\boxed{
2q-n.
}
]

若要保证任意两个 quorum 的交集中至少有一个诚实主体，则必须：

[
2q-n>f.
]

即：

[
\boxed{
2q>n+f.
}
]

另一方面，为保证即使全部 Byzantine 拒绝参与，诚实主体仍能组成 quorum，需要：

[
\boxed{
q\le n-f.
}
]

两个条件能够同时满足，当且仅当：

[
\frac{n+f}{2}<n-f.
]

化简得：

[
\boxed{
n>3f.
}
]

所以：

[
\boxed{
\text{quorum 安全交集}
+
\text{仅靠诚实主体即可推进}
}
]

共同导出 (n>3f)。

这不是神秘的协议常数，而是两个集合基数条件的直接结果。

---

# 209. 信任传递需要目标类型对齐

设主体 (A) 接收 (B) 的报告：

[
R_B:X\to M_B.
]

主体 (B) 又依赖 (C) 的报告：

[
R_C:X\to M_C.
]

若存在：

[
h:M_C\to M_B
]

使：

[
R_B=h\circ R_C,
]

且：

[
T=\overline T\circ R_B,
]

则：

[
T
=

\overline T\circ h\circ R_C.
]

## 定理 209.1（有型信任传递）

如果：

1. (C) 的报告足以生成 (B) 的报告；
2. (B) 的报告足以决定 (A) 的目标；
3. 两层报告真实性成立；

则 (A) 可以在目标 (T) 上通过 (C) 的报告链获得结构性信任。

但：

[
\operatorname{Trust}_A(B;T)
]

和：

[
\operatorname{Trust}_B(C;S)
]

并不自动推出：

[
\operatorname{Trust}_A(C;T),
]

除非 (S) 足以生成 (B) 对 (T) 所需的报告。

所以：

[
\boxed{
\text{信任不是无类型的传递关系；
它是目标和接口对齐后的可组合因子化。}
}
]

---

# Part XXXII：部分可观测世界、信念状态与行动价值

# 210. 信念状态是历史的状态化完成

设隐藏状态类型为 (X)，观察：

[
O:X\to Y,
]

行动：

[
F_u:X\to X.
]

一个历史为：

[
h_t=(o_0,u_0,o_1,\ldots,u_{t-1},o_t).
]

## 定义 210.1（兼容状态集）

[
\boxed{
B(h_t)
======

\left{
x_t\in X
;\middle|;
x_t\text{ 可由某个与历史相容的初态和行动链产生}
\right}.
}
]

递归更新：

[
\boxed{
B(h_{t+1})
==========

\left{
F_u(x)
;\middle|;
x\in B(h_t),
\ O(F_u(x))=o_{t+1}
\right}.
}
]

---

## 定理 210.1（信念集充分性）

给定当前信念集 (B(h_t))，任何未来行动序列下可能出现的观察轨迹集合，只依赖 (B(h_t))，而不依赖生成该信念集的具体历史。

### 证明

未来所有可能轨迹由：

[
x\in B(h_t)
]

分别向前演化后取并集得到。

若两个历史具有相同兼容状态集，则它们产生的未来可能轨迹集合相同。 (\square)

所以：

[
\boxed{
\text{信念状态}
===========

\text{把完整观察历史压缩成未来预测所需状态的一个充分统计量}.
}
]

---

# 211. 信念集并不总是最小：预测信念商

两个不同信念集可能包含不同隐藏状态，却产生完全相同的未来观察可能性。

定义：

[
\boxed{
B_1\sim_{\mathrm{belief}}B_2
}
]

当对所有未来行动序列，两者产生相同的观察轨迹集合。

定义预测信念商：

[
\boxed{
Z_{\mathrm{belief}}
===================

\mathcal P(X)/{\sim_{\mathrm{belief}}}.
}
]

## 定理 211.1（最小预测信念）

任何历史摘要 (S(h)) 若足以决定：

* 所有未来行动下的可能观察；
* 所有基于这些观察的经验目标；

则相同 (S)-值的历史必须属于同一个 (\sim_{\mathrm{belief}})-类。

所以 (Z_{\mathrm{belief}}) 是经验控制问题中的规范最小历史状态。

这区分：

[
\boxed{
\begin{aligned}
\text{原始历史}
&=\text{全部记录};\
\text{兼容状态集}
&=\text{充分但可能冗余};\
\text{预测信念商}
&=\text{最小经验充分状态}.
\end{aligned}
}
]

---

# 212. 更多免费信息不会降低最优行动价值

设概念：

[
C\preceq D,
]

即 (D) 比 (C) 更精细。

允许行动集为 (U)，效用为：

[
V:X\times U\to\mathbb R.
]

基于概念 (C) 的策略是：

[
\pi_C:B_C\to U.
]

基于 (D) 的策略是：

[
\pi_D:B_D\to U.
]

## 定理 212.1（信息价值单调性）

若：

* 信息免费；
* 信息获取不改变世界；
* 可行动集合不改变；
* 主体可以忽略新增信息；

则：

[
\boxed{
V^*(D)\ge V^*(C).
}
]

### 证明

由 (C\preceq D)，存在：

[
p:B_D\to B_C.
]

任意 (C)-策略可由 (D)-策略模拟：

[
\pi_D=\pi_C\circ p.
]

所以 (D) 可实现的策略集合包含 (C) 的策略集合，最优值不会更低。 (\square)

---

# 213. “知道得更多反而更差”必有额外结构

由上一定理，如果新增信息似乎降低福利，则至少有一个前件失败。

可能原因包括：

[
\boxed{
\begin{aligned}
&\text{信息获取有成本};\
&\text{观察改变世界};\
&\text{信息会被他人观察并产生 signaling};\
&\text{主体被规则强制根据新信息行动};\
&\text{信息改变可行动集合};\
&\text{信息造成心理或规范代价};\
&\text{主体不能自由忽略信息}.
\end{aligned}
}
]

## 最小反例：信息成本

设无信息时最优效用为：

[
0.
]

获得精确信息后仍可选择同一行动，但信息成本为：

[
1.
]

则净效用变为：

[
-1.
]

伤害来自成本，不是信息分辨率本身。

所以：

[
\boxed{
\text{纯信息没有负价值；
负价值来自信息进入现实过程后的附加 FLOW 或 ADMIT 变化。}
}
]

---

# 214. 行动具有工具价值和认识价值两个轴

对行动 (u)，定义：

## 工具价值

[
\boxed{
V_{\mathrm{inst}}(u)
====================

\mathbb E[V(F_uX)].
}
]

## 认识价值

若行动后产生观察 (O(F_uX))，定义：

[
\boxed{
V_{\mathrm{epi}}(u)
===================

I(T(X);O(F_uX)\mid C(X)).
}
]

或者使用结构版本：

[
\operatorname{Gain}
\left(
O\circ F_u;
C,T
\right).
]

一个行动可以：

* 工具价值高、认识价值低；
* 认识价值高、工具价值低；
* 两者都高；
* 两者都低。

因此科学实验和主体行动通常是多目标选择：

[
\boxed{
\max_u
\left(
V_{\mathrm{inst}}(u),
V_{\mathrm{epi}}(u)
\right).
}
]

没有给出二者权重时，一般只有 Pareto 前沿，没有唯一最优行动。

---

# 215. 信念充分行动与额外记忆

设主体历史为 (h)，信念状态为 (B(h))，实际行动为：

[
A(h)\in U.
]

## 定义 215.1（信念充分策略）

若存在：

[
\pi
]

使：

[
\boxed{
A(h)=\pi(B(h)),
}
]

则行动完全由当前信念决定。

若存在两个历史：

[
B(h)=B(h'),
]

但：

[
A(h)\neq A(h'),
]

则主体还依赖信念之外的历史余量，例如：

* 承诺；
* 习惯；
* 情绪；
* 路径依赖；
* 隐藏记忆；
* 随机性。

## 定义 215.2（最小行动记忆）

[
\boxed{
M_A
===

B\vee E_A.
}
]

它是保留当前信念并足以决定行动的最小概念。

所以：

[
\boxed{
\text{行动记忆}
===========

\text{信念状态不足以解释行动时所需的最小历史补充}.
}
]

---

# Part XXXIII：多目标修复、隐私泄漏与信息权力

# 216. 多目标修复的联合缺陷图

设目标族：

[
T_1,\ldots,T_n.
]

联合目标：

[
T=(T_1,\ldots,T_n).
]

则：

[
\ker T
======

\bigcap_i\ker T_i.
]

所以：

[
\begin{aligned}
\Delta(C;T)
&=
\ker C\setminus\bigcap_i\ker T_i\
&=
\bigcup_i
\left(
\ker C\setminus\ker T_i
\right).
\end{aligned}
]

即：

[
\boxed{
\Delta(C;T)
===========

\bigcup_i\Delta(C;T_i).
}
]

## 定理 216.1（联合缺陷图）

有限模型中，联合目标的缺陷图满足：

[
\boxed{
G(C;T)
======

\bigcup_iG(C;T_i).
}
]

因此，使全部目标同时可决定的最小辅助标签数为：

[
\boxed{
\chi!\left(
\bigcup_iG(C;T_i)
\right).
}
]

多目标修复不是分别修复后简单相加，因为一个标签区别可以同时修复多个目标缺陷。

---

# 217. 隐私应定义为“共享敏感信息没有增加”

设：

* (P)：当前允许公开的概念；
* (S)：敏感概念；
* (M)：新增信息或模型输出。

定义当前公开信息与敏感概念的最大共同因子：

[
\boxed{
\operatorname{Leak}(P;S)
========================

P\wedge S.
}
]

加入 (M) 后：

[
\operatorname{Leak}(P\vee M;S)
==============================

(P\vee M)\wedge S.
]

## 定义 217.1（结构无新增泄漏）

若：

[
\boxed{
(P\vee M)\wedge S
\simeq
P\wedge S,
}
]

则 (M) 没有增加任何可由公开信息恢复的敏感概念区别。

---

## 定理 217.1（精确目标的强制泄漏）

设目标 (T) 必须通过新增信息精确实现：

[
E_T\preceq P\vee M.
]

令：

[
K=E_T\wedge S
]

为目标和敏感概念的最大共同部分。

则：

[
\boxed{
K\preceq(P\vee M)\wedge S.
}
]

### 证明

因为：

[
K\preceq E_T
\preceq P\vee M,
]

且：

[
K\preceq S.
]

所以 (K) 是 (P\vee M) 与 (S) 的共同下界，故：

[
K\preceq(P\vee M)\wedge S.
]

(\square)

若：

[
K\not\preceq P\wedge S,
]

则无新增泄漏不可能成立。

因此：

[
\boxed{
\text{若目标本身包含当前公开信息尚未暴露的敏感区别，
任何精确实现都必然增加敏感泄漏。}
}
]

---

# 218. 即使内部模型保密，公开输出本身也可能泄漏

即使 (M) 永不公开，只发布目标输出：

[
T,
]

公众可用概念仍从：

[
P
]

变为：

[
P\vee E_T.
]

所以输出无新增敏感泄漏的条件为：

[
\boxed{
(P\vee E_T)\wedge S
\simeq
P\wedge S.
}
]

若该条件失败，则泄漏由输出本身造成，而不是由内部模型参数、训练数据或解释接口造成。

这说明必须区分：

[
\boxed{
\begin{aligned}
\text{模型泄漏}
&=\text{内部表示暴露敏感信息};\
\text{输出泄漏}
&=\text{任务结果本身携带敏感信息}.
\end{aligned}
}
]

后者不能仅靠隐藏模型解决。

---

# 219. 最小标签数不等于最小概念修复

规范最小修复为：

[
\boxed{
C\vee E_T.
}
]

它在精化序中是唯一最粗的充分扩张。

但若成本只计算辅助标签字母表大小，可能出现同样成本但过度精化的修复。

## 反例 219.1

令 (C) 有两个纤维：

[
A={a_0,a_1,a_2},
]

[
B={b_0,b'_0,b_1}.
]

目标：

[
T(a_i)=i,
]

[
T(b_0)=T(b'_0)=0,
\qquad
T(b_1)=1.
]

由于 (A) 中有三个目标值，最小辅助字母表大小为 (3)。

定义规范标签：

[
M_1=T.
]

定义另一标签：

[
\begin{aligned}
M_2(a_0)&=0,&M_2(a_1)&=1,&M_2(a_2)&=2,\
M_2(b_0)&=0,&M_2(b'_0)&=2,&M_2(b_1)&=1.
\end{aligned}
]

目标仍可由：

[
(C,M_2)
]

恢复，因为在 (B)-纤维内标签 (0,2) 都映射到目标 (0)。

但 (M_2) 额外区分：

[
b_0,b'_0,
]

而目标并不要求该区别。

因此：

[
\boxed{
|M_1|=|M_2|=3,
}
]

但：

[
C\vee M_2
]

严格精化：

[
C\vee E_T.
]

所以：

[
\boxed{
\text{最小字母表成本}
\not\Rightarrow
\text{最小信息收集}.
}
]

真正保守修复需要同时最小化：

1. 标签资源；
2. 概念精化；
3. 隐私泄漏；
4. 制度权力。

---

# 220. 信息精化必然扩大可条件化行动能力

对概念 (C) 和行动集合 (U)，定义可实现政策集合：

[
\boxed{
\Pi(C;U)
========

\left{
\pi\circ q_C
;\middle|;
\pi:B_C\to U
\right}.
}
]

## 定理 220.1（信息—政策权力单调性）

若：

[
C\preceq D,
]

则：

[
\boxed{
\Pi(C;U)\subseteq\Pi(D;U).
}
]

### 证明

存在：

[
p:B_D\to B_C.
]

任意 (C)-政策：

[
\pi_C\circ q_C
]

可写成：

[
(\pi_C\circ p)\circ q_D.
]

所以它也是 (D)-政策。 (\square)

---

## 定理 220.2（严格权力增长）

若 (D) 严格区分某两个 (C)-同类状态：

[
q_C(x)=q_C(y),
\qquad
q_D(x)\neq q_D(y),
]

且 (U) 至少有两个行动，则存在一个 (D)-政策能够区别对待 (x,y)，但没有任何 (C)-政策能这样做。

因此：

[
\boxed{
\text{收集更多信息}
=============

\text{扩大能够实施的差别待遇集合}.
}
]

即使制度当前承诺不使用这些区别，能力结构已经改变。

---

# 221. 实际不歧视与具有歧视能力不同

设制度当前政策为：

[
J:X\to U.
]

当前政策可能通过粗概念 (P) 因子化：

[
J=\overline J\circ P.
]

所以实际没有使用更细敏感信息。

但若制度持有更细概念 (D)：

[
P\prec D,
]

则：

[
\Pi(P;U)
\subsetneq
\Pi(D;U).
]

因此必须区分：

[
\boxed{
\begin{aligned}
\text{实际非歧视}
&=\text{当前政策未使用敏感区别};\
\text{能力非歧视}
&=\text{制度甚至不具备根据该区别行动的能力}.
\end{aligned}
}
]

后者是更强的“结构性不可能作恶”条件。

这为隐私提供一种非工具性解释：

[
\boxed{
\text{隐私不仅防止当前滥用，
还限制未来可实施的差别待遇空间。}
}
]

---

# Part XXXIV：假设债务、保守增长与理论修订

# 222. 一个定理应被表示为依赖包

设模型类型为 (\mathcal M)。

结论为：

[
P:\mathcal M\to\mathsf{Prop}.
]

假设包为：

[
A:\mathcal M\to\mathsf{Prop}.
]

证明为：

[
p:
\forall m,\quad
A(m)\to P(m).
]

完整定理包：

[
\boxed{
\operatorname{Claim}(P)
=======================

\sum_{A:\mathcal M\to\mathsf{Prop}}
\left[
\left(
\forall m,\ A(m)\to P(m)
\right)
\times
\operatorname{Provenance}(A,P)
\right].
}
]

因此一个定理不仅包含结论，还包含：

* 有效域；
* 假设；
* proof term；
* 依赖来源；
* 使用的逻辑原则。

---

## 定义 222.1（假设强度）

称 (A_1) 弱于 (A_2)，当：

[
\boxed{
\forall m,\quad
A_2(m)\to A_1(m).
}
]

即 (A_1) 在更多模型上成立。

若同一结论分别有：

[
A_1\to P,
\qquad
A_2\to P,
]

且 (A_1) 弱于 (A_2)，则第一个定理适用范围更广。

所以比较定理强弱时，不能只看结论相同，还必须比较假设域。

---

# 223. 隐藏假设就是声明域中的反模型

设理论公开声明假设为 (A)，并声称结论 (P)。

定义假设缺陷：

[
\boxed{
\Delta_{\mathrm{assump}}(A;P)
=============================

{m\mid A(m)\land\neg P(m)}.
}
]

若该集合非空，则公开假设不足以支持结论。

## 定义 223.1（隐藏假设）

谓词 (H) 是一个隐藏补充假设，当：

[
A\land H
\Longrightarrow
P,
]

但：

[
A\not\Longrightarrow P.
]

因此：

[
\boxed{
\text{隐藏假设债务}
=============

\text{理论实际需要、但未在公开 claim package 中列出的准入条件}.
}
]

---

## 定理 223.1（反模型的假设诊断意义）

任意：

[
m\in\Delta_{\mathrm{assump}}(A;P)
]

都证明至少一项成立：

1. 结论 (P) 错误；
2. 假设列表不完整；
3. 模型 (m) 应被额外 ADMIT 排除；
4. 推理规则错误。

但不能只凭反模型自动决定应修改哪一项。

这正是理论修复的 underdetermination。

---

# 224. 概念 refinement 对旧问题是保守的

若：

[
C\preceq D,
]

则任何旧目标 (T) 若满足：

[
E_T\preceq C,
]

必满足：

[
E_T\preceq D.
]

## 定理 224.1（旧问题保守性）

[
\boxed{
C\preceq D
\Longrightarrow
\operatorname{Ans}(C)
\subseteq
\operatorname{Ans}(D),
}
]

其中：

[
\operatorname{Ans}(C)
=====================

{T\mid E_T\preceq C}.
]

所以概念 refinement 不会破坏旧的精确可回答性。

新增区别只会增加能够回答的问题。

---

## 边界

这不表示人的“信念”不会改变。

精确知识是纤维稳定命题，沿 refinement 保持。

但统计信念、默认推理和最优猜测可能被新证据推翻。

所以：

[
\boxed{
\text{信息单调}
\neq
\text{信念单调}.
}
]

---

# 225. 概率信念可以随证据精化而撤回

设：

[
X={x_1,x_2,x_3}
]

等概率。

命题 (P) 在：

[
x_1,x_2
]

为真，在：

[
x_3
]

为假。

粗概念 (C) 为常值。

则：

[
\Pr(P\mid C)=\frac23.
]

若信念阈值为：

[
\frac12,
]

主体相信 (P)。

假设实际状态为 (x_3)。

精化概念 (D) 单独识别 (x_3)，则在实际 (D)-纤维中：

[
\Pr(P\mid D(x_3))=0.
]

于是信念被撤回。

但原先主体并不知道 (P)，因为粗纤维中存在反例。

所以：

[
\boxed{
\text{结构知识沿精化单调；
高概率信念则可以理性撤回。}
}
]

---

# 226. 理论 revision 一般不交换

设当前允许世界集合为：

[
A\subseteq X.
]

定义一个简单 revision 算子：

[
\boxed{
\operatorname{Rev}_P(A)
=======================

\begin{cases}
A\cap P,&A\cap P\neq\varnothing,\
P,&A\cap P=\varnothing.
\end{cases}
}
]

它表示：

* 若新命题与旧理论一致，则条件化；
* 若完全冲突，则放弃旧域，改以新命题为准。

取：

[
X={1,2,3},
]

[
A={1},
]

[
P={2,3},
]

[
Q={1,2}.
]

先修订 (P)：

[
\operatorname{Rev}_P(A)={2,3}.
]

再修订 (Q)：

[
\operatorname{Rev}_Q\operatorname{Rev}_P(A)
===========================================

{2}.
]

反向：

[
\operatorname{Rev}_Q(A)={1},
]

再修订 (P)：

[
\operatorname{Rev}_P\operatorname{Rev}_Q(A)
===========================================

{2,3}.
]

因此：

[
\boxed{
\operatorname{Rev}_Q\operatorname{Rev}_P
\neq
\operatorname{Rev}_P\operatorname{Rev}_Q.
}
]

所以理论 revision 的路径依赖不是偶然现象，而来自：

* 冲突时保留什么；
* 哪个证据更新得更晚；
* 使用什么距离；
* 哪些前提有更高优先级。

---

# Part XXXV：第一人称余量、意识可检验性与语言边界

# 227. 现象差异可以是公开行为上的惰性余量

设：

[
P:X\to B_P
]

为公共读出，

[
\Phi:X\to B_\Phi
]

为候选现象概念，

行动幺半群 (M) 作用于 (X)。

定义完整公共控制轮廓：

[
\boxed{
\mathcal B_P(x)(m)
==================

P(F_mx).
}
]

## 定义 227.1（公开行为等价）

[
x\sim_{\mathrm{pub}}y
\iff
\forall m\in M,\quad
P(F_mx)=P(F_my).
]

## 定义 227.2（相对表象惰性）

若：

[
x\sim_{\mathrm{pub}}y,
]

但：

[
\Phi(x)\neq\Phi(y),
]

则现象差异相对于允许行动和公共读出是行为惰性的。

这并不证明它在绝对意义上没有因果作用，只证明：

[
\boxed{
\text{当前允许实验无法把该差异运输到公共读出。}
}
]

---

## 定理 227.1（公开因果活性判据）

若存在行动 (m)：

[
P(F_mx)\neq P(F_my),
]

则 (x,y) 不在同一公共动态完成类中。

所以任何能够在允许干预后改变公共结果的私人差异，都会被：

[
\operatorname{Dyn}_M(P)
]

捕获。

由此区分：

[
\boxed{
\begin{aligned}
\text{现象差异}
&=\Phi(x)\neq\Phi(y);\
\text{公开因果活性}
&=\exists m,\ P(F_mx)\neq P(F_my);\
\text{公开表象惰性}
&=\forall m,\ P(F_mx)=P(F_my).
\end{aligned}
}
]

---

# 228. 精确现象报告排除完全公开等价

设语言报告：

[
R:X\to B_R
]

属于公共读出的一部分。

若报告能精确决定现象状态：

[
\boxed{
E_\Phi\preceq E_R,
}
]

则：

[
R(x)=R(y)
\Longrightarrow
\Phi(x)=\Phi(y).
]

## 定理 228.1（真实报告阻碍 inverted-spectrum 等价）

如果两个主体在全部公共结果上等价，尤其有：

[
R(x)=R(y),
]

那么在精确真实报告前件下：

[
\Phi(x)=\Phi(y).
]

所以一个形式 inverted-spectrum 对：

[
\Phi(x)\neq\Phi(y)
]

若要保持公共完全等价，至少必须有一项失败：

1. 现象不能被精确报告；
2. 报告不属于允许公共读出；
3. 主体报告不可靠；
4. 公共等价没有包含全部行动；
5. 现象概念本身定义不稳定。

---

# 229. 不可言说性是语言概念的非充分性

设语言输出概念为：

[
L:X\to B_L.
]

## 定义 229.1（相对不可言说）

现象概念 (\Phi) 相对于语言 (L) 不可精确表达，当：

[
\boxed{
E_\Phi\not\preceq L.
}
]

即存在：

[
L(x)=L(y),
\qquad
\Phi(x)\neq\Phi(y).
]

## 定理 229.1（语言后处理不能表达缺失区别）

任意语言后处理：

[
h:B_L\to Z
]

产生：

[
h\circ L,
]

仍不能区分上述 (x,y)。

所以更复杂的修辞、长文本和递归解释，只要仍完全通过旧语言概念生成，就不能恢复语言已经删除的现象区别。

---

## 最小表达完成

[
\boxed{
L^+
===

L\vee E_\Phi.
}
]

它使现象可表达。

但直接加入一个标签：

[
\text{“这是 }\Phi_7\text{”}
]

只解决指称，不自动解决：

* 结构解释；
* 跨主体翻译；
* 因果机制；
* 经验校准；
* 相似性空间。

所以：

[
\boxed{
\text{命名一个经验}
\neq
\text{解释该经验}.
}
]

---

# 230. 第一人称优势是目标相对的

设：

[
C_1:X\to B_1
]

为第一人称概念，

[
C_3:X\to B_3
]

为第三人称概念。

对目标 (T)：

## 第一人称优势

[
\boxed{
E_T\preceq C_1,
\qquad
E_T\not\preceq C_3.
}
]

## 第三人称优势

[
\boxed{
E_T\preceq C_3,
\qquad
E_T\not\preceq C_1.
}
]

两个概念可能不可比较。

例如：

* 主体直接知道疼痛体验，但不知道神经细胞状态；
* 外部仪器知道神经状态，但不知道主体当前如何概念化体验。

因此：

[
\boxed{
\text{第一人称权威}
}
]

不能作为无类型的全局原则，只能相对于特定目标成立。

---

## 定义 230.1（内省可错性）

设真实内部目标：

[
I:X\to Y.
]

若：

[
E_I\not\preceq C_1,
]

则存在：

[
C_1(x)=C_1(y),
\qquad
I(x)\neq I(y).
]

所以第一人称概念不足以决定真实内部状态。

这给出形式化的：

[
\boxed{
\text{第一人称可能具有特权，
但不必具有普遍无误性。}
}
]

---

# 231. 私人性随实验制度扩张而单调缩小

设允许实验族：

[
\mathcal E\subseteq\mathcal E'.
]

对应实验概念：

[
C_{\mathcal E}
==============

\bigvee_{e\in\mathcal E}E_e,
]

[
C_{\mathcal E'}
===============

\bigvee_{e\in\mathcal E'}E_e.
]

显然：

[
C_{\mathcal E}
\preceq
C_{\mathcal E'}.
]

所以：

[
\ker C_{\mathcal E'}
\subseteq
\ker C_{\mathcal E}.
]

## 定理 231.1（实验扩张缩小经验余量）

新增实验不会增加实验不可区分状态对，只会保持或减少。

因此：

[
\boxed{
\text{“私人”不是绝对属性；
它是相对于当前允许实验、行动和公开读出的余纤维。}
}
]

某个今天不可观察的区别，可能在新仪器或新交互协议出现后变成公开区别。

---

# 232. 理论空间的普遍经验商

设理论或模型空间为：

[
\Theta.
]

允许的实验协议族为：

[
\mathcal P.
]

每个协议 (\pi) 在模型 (\theta) 下产生结果分布：

[
\mathsf{Out}_{\pi}(\theta).
]

定义：

[
\boxed{
\theta\sim_{\mathcal P}\theta'
\iff
\forall\pi\in\mathcal P,\quad
\mathsf{Out}_{\pi}(\theta)
==========================

\mathsf{Out}_{\pi}(\theta').
}
]

经验模型商：

[
\boxed{
\Theta_{\mathrm{emp}}
=====================

\Theta/{\sim_{\mathcal P}}.
}
]

## 定理 232.1（经验可识别性）

模型性质：

[
T:\Theta\to Y
]

可由允许实验制度识别，当且仅当：

[
\boxed{
E_T\preceq\Theta_{\mathrm{emp}}.
}
]

即：

[
\theta\sim_{\mathcal P}\theta'
\Longrightarrow
T(\theta)=T(\theta').
]

若两个理论在全部允许实验中等价，但 (T) 不同，则 (T) 在当前实验制度下属于经验余量。

---

# 233. 经验结构主义与本体余量

经验商：

[
\Theta_{\mathrm{emp}}
]

只保留全部允许实验能够区分的结构。

相应余纤维：

[
R_{\mathrm{emp}}([\theta])
]

包含所有经验等价但内部结构不同的理论。

可以区分两种立场：

## 经验结构主义

把经验商类视为理论身份：

[
\theta\sim_{\mathcal P}\theta'
\Rightarrow
\theta\equiv_{\mathrm{theory}}\theta'.
]

## 本体实在论

保留经验纤维内部的结构差异，认为它们可能在：

* 新实验；
* 更远未来；
* 不同干预；
* 统一理论；
* 非经验解释目标；

中重新变得相关。

形式内核不自动选择二者。

它只说明争论发生在：

[
\boxed{
\text{是否把当前实验核商提升为完整本体同一性。}
}
]

---

# Part XXXVI：交互式形式哲学

# 234. 哲学应建模为一台交互式状态机

定义哲学研究状态：

[
\boxed{
\mathfrak S
===========

(
X,
A,
C,
\mathcal T,
\mathcal P,
\mathcal D,
\mathcal R
).
}
]

其中：

[
\begin{aligned}
X&=\text{当前对象类型};\
A&=\text{准入域};\
C&=\text{当前概念体系};\
\mathcal T&=\text{当前问题／目标族};\
\mathcal P&=\text{proof 与 provenance 库};\
\mathcal D&=\text{已知缺陷和反模型};\
\mathcal R&=\text{修订规则}.
\end{aligned}
]

允许的基本操作包括：

[
\boxed{
\begin{aligned}
\mathsf{Ask}
&:\text{加入目标};\
\mathsf{Observe}
&:\text{精化概念};\
\mathsf{Intervene}
&:\text{改变状态并产生实验读出};\
\mathsf{Prove}
&:\text{构造因子化或逻辑证明};\
\mathsf{Refute}
&:\text{构造缺陷见证};\
\mathsf{Repair}
&:\text{精化、压缩、锚定或扩域};\
\mathsf{Revise}
&:\text{修改准入和假设};\
\mathsf{Audit}
&:\text{检查 provenance、循环性和实现性}.
\end{aligned}
}
]

哲学研究因此不是一次性输出，而是状态转换：

[
\mathfrak S_0
\to
\mathfrak S_1
\to
\mathfrak S_2
\to\cdots.
]

---

# 235. 一个成熟哲学系统的七项不变量

一套形式哲学若要稳定运作，至少应维持以下七项条件。

## 1. 类型正确性

每个概念、过程、目标和规范作用在明确类型上。

## 2. 证明真实性

每个结论携带有效 proof term 或明确标记为 conjecture。

## 3. 假设透明性

所有使结论成立的 ADMIT 和领域前件可见。

## 4. provenance 完整性

每个结论可追踪其数据和推理来源。

## 5. 缺陷开放性

理论允许构造反模型，而不是通过定义排除一切反例。

## 6. 修复保守性

修复应明确说明：

* 新增了哪些区别；
* 删除了哪些目标；
* 排除了哪些世界；
* 增加了哪些权力。

## 7. 实现分离

形式固定点不自动被宣称为现实对象。

由此：

[
\boxed{
\text{哲学严谨性}
============

\text{类型}
+
\text{证明}
+
\text{假设}
+
\text{来源}
+
\text{反例}
+
\text{修复账本}
+
\text{实现审计}.
}
]

---

# 236. 第五层统一：问题、证据、行动、权力与意识的共同内核

经过 §197–§235，可以得到一组新的统一。

## 问题

[
\boxed{
\text{问题}
=========

\text{目标概念}.
}
]

## 实验

[
\boxed{
\text{实验}
=========

\text{用于 refinement 的观察或干预界面}.
}
]

## 发现

[
\boxed{
\text{发现}
=========

\text{某个原本非因子化目标变为可因子化}.
}
]

## 信任

[
\boxed{
\text{信任}
=========

\text{通过他人的报告链委托目标因子化}.
}
]

## 分布式真理

[
\boxed{
\text{分布式可靠性}
=============

\text{独立 proof support、quorum 相交和 adversarial 阈值}.
}
]

## 主体信念

[
\boxed{
\text{信念状态}
===========

\text{完整历史对未来经验后果的状态化压缩}.
}
]

## 行动能力

[
\boxed{
\text{行动能力}
===========

\text{概念所允许实现的政策集合}.
}
]

## 信息权力

[
\boxed{
C\preceq D
\Longrightarrow
\Pi(C)\subseteq\Pi(D).
}
]

所以更多信息不仅提高预测，也扩大区别对待能力。

## 隐私

[
\boxed{
\text{隐私}
=========

\text{限制公共概念与敏感概念的共同因子增长}.
}
]

## 第一人称余量

[
\boxed{
\text{私人体验}
===========

\text{当前公共实验商余纤维中的现象区别}.
}
]

## 哲学研究

[
\boxed{
\text{哲学研究}
===========

\text{交互式生成问题、设计实验、构造证明、
定位缺陷并审计修复代价的过程}.
}
]

---

# 237. 当前最深层的新结论

本轮最重要的推导不是又增加了一批哲学术语，而是揭示了六个此前未完全显式化的结构事实。

第一，**问题与概念是同一种对象**：

[
\boxed{
\text{所谓“无法回答”，往往不是缺少推理，
而是当前证据余纤维仍跨越多个答案值。}
}
]

第二，**自适应实验不能突破全部被动实验的联合盲点**：

[
\boxed{
\text{策略能降低成本，但不能创造实验体系不存在的分辨能力。}
}
]

第三，**信任和共识必须审计 provenance**：

[
\boxed{
\text{一百个同源报告在结构上仍可能只有一个信息源。}
}
]

第四，**更多信息同时意味着更多制度权力**：

[
\boxed{
\text{refinement 不只扩大可知集合，也扩大可差别行动集合。}
}
]

第五，**意识私人性是实验制度相对的，而不是纯粹形而上标签**：

[
\boxed{
\text{私人余量是否可公开化，
取决于允许的行动、报告和观测是否能把它运输到公共读出。}
}
]

第六，也是最承重的一条：

[
\boxed{
\text{形式哲学的基本单位不应是“命题”，
而应是“问题—界面—证明—反例—修复—来源”六元组。}
}
]

可以写成：

[
\boxed{
\mathfrak Q
===========

(
T,
C,
p,
\Delta,
R,
\Pi
),
}
]

其中：

[
\begin{aligned}
T&=\text{要回答的问题};\
C&=\text{当前信息界面};\
p&=\text{因子化或证明见证};\
\Delta&=\text{缺陷和反模型};\
R&=\text{最小修复};\
\Pi&=\text{proof provenance}.
\end{aligned}
]

因此，整套理论的总公式进一步发展为：

[
\boxed{
\begin{aligned}
\textbf{Formal Concept Dynamics}
={}&
\textbf{a calculus of questions}\
&+
\textbf{an algebra of experiments}\
&+
\textbf{a provenance theory of trust}\
&+
\textbf{a belief-state theory of agency}\
&+
\textbf{a structural theory of privacy and power}\
&+
\textbf{an empirical quotient theory of mind and science}.
\end{aligned}
}
]

最凝练的一句是：

[
\boxed{
\text{一个系统知道什么，取决于它能区分什么；
它能控制什么，取决于这些区别能支持什么政策；
它应当被允许知道什么，则取决于我们愿意赋予它多少区别对待世界的能力。}
}
]
以下从 **§238** 继续。仍然只进行纸面推理，不处理 GitHub，也不把这些新增定义与定理标记为已经获得 Lean proof term 的 `Closed` 结论。

---

# Part XXXVII：沟通、欺骗与认识操纵

# 238. 沟通是目标通过消息界面的因子化

设世界状态类型为：

[
X.
]

发送者拥有观察概念：

[
C_S:X\to B_S.
]

编码器为：

[
e:B_S\to M.
]

实际发送的消息概念为：

[
\boxed{
M_S=e\circ C_S:X\to M.
}
]

接收者希望从消息中判断目标：

[
T:X\to Y.
]

解码器为：

[
d:M\to Y.
]

## 定义 238.1（目标精确沟通）

若：

[
\boxed{
T=d\circ M_S,
}
]

则该协议关于目标 (T) 是精确的。

等价地：

[
\boxed{
E_T\preceq M_S.
}
]

所以沟通成功不是“双方使用同样的词”，而是：

[
\boxed{
\text{目标能够通过消息概念因子化。}
}
]

---

## 定理 238.1（沟通充分性判据）

以下等价：

[
T=d\circ M_S
]

对某个 (d) 成立；

[
M_S(x)=M_S(y)
\Longrightarrow
T(x)=T(y);
]

[
\Delta(M_S;T)=\varnothing.
]

因此，消息失败的最小见证是：

[
\boxed{
M_S(x)=M_S(y),
\qquad
T(x)\neq T(y).
}
]

也就是说，同一消息覆盖了两个不同的正确答案。

---

## 定理 238.2（无损编码判据）

若编码器：

[
e|_{\operatorname{Im}C_S}
]

在发送者概念的实际像上单射，则：

[
\boxed{
M_S\simeq_{\mathrm{con}}C_S.
}
]

此时消息没有删除发送者实际拥有的任何概念区别。

若不单射，则消息严格粗化发送者概念，但这些被删除的区别是否重要，仍取决于目标 (T)。

---

# 239. 说真话、说完整话和提供充分理由是三件事

设消息 (M_S) 具有一个字面内容目标：

[
L:X\to Z.
]

若存在：

[
\ell:M\to Z
]

满足：

[
\boxed{
L=\ell\circ M_S,
}
]

则消息对字面内容 (L) 是精确真实的。

但接收者真正关心的目标可能是：

[
T:X\to Y.
]

即使：

[
E_L\preceq M_S,
]

也完全可能：

[
E_T\not\preceq M_S.
]

因此：

[
\boxed{
\text{字面真实}
\not\Rightarrow
\text{目标充分}.
}
]

---

## 定义 239.1（目标相关遗漏）

假设发送者的完整概念足以决定目标：

[
E_T\preceq C_S,
]

但实际消息不足：

[
E_T\not\preceq M_S.
]

则称消息对目标 (T) 发生了目标相关遗漏。

其见证为：

[
M_S(x)=M_S(y),
\qquad
T(x)\neq T(y),
]

而发送者概念能够区分二者：

[
C_S(x)\neq C_S(y).
]

这表示：

> 发送者拥有目标所需的区别，但编码时删除了它。

---

## 定理 239.1（遗漏的最小修复）

目标相关遗漏的规范最小修复为：

[
\boxed{
M_S^+
=====

M_S\vee E_T.
}
]

它保留原消息，并加入恰好足以决定目标的区别。

任何同时满足：

[
M_S\preceq D,
\qquad
E_T\preceq D
]

的修复消息概念 (D)，都必须满足：

[
M_S^+\preceq D.
]

---

# 240. “真实但误导”来自目标异质的消息纤维

设接收者使用推断规则：

[
\delta:M\to Y.
]

在实际状态 (a)，接收者得出：

[
\delta(M_S(a)).
]

## 定义 240.1（误导）

若消息的字面内容真实，但：

[
\boxed{
\delta(M_S(a))
\neq
T(a),
}
]

则接收者在目标 (T) 上被误导。

---

## 定理 240.1（目标充分排除误导）

若：

[
T=d\circ M_S,
]

且接收者使用正确解码器：

[
\delta=d
]

于消息实际像上，则误导不可能发生。

---

## 定理 240.2（异质纤维迫使某处误判）

若存在：

[
x,y
]

满足：

[
M_S(x)=M_S(y),
\qquad
T(x)\neq T(y),
]

则任何确定性推断规则：

[
\delta:M\to Y
]

至少在 (x,y) 中一个状态上错误。

### 证明

由于：

[
M_S(x)=M_S(y),
]

有：

[
\delta(M_S(x))
==============

\delta(M_S(y)).
]

但目标值不同，所以同一个输出不能同时等于两个不同目标值。 (\square)

---

## 定义 240.2（分区操纵）

若发送者：

1. 知道消息纤维内部存在目标异质性；
2. 知道接收者默认规则 (\delta)；
3. 选择一个字面真实但会使 (\delta) 在实际状态上错误的消息；

则称其进行了分区操纵。

其本质不是直接陈述假命题，而是：

[
\boxed{
\text{选择一个过粗的真实分区，使接收者的默认代表选择落在错误状态上。}
}
]

---

# 241. 劝服与操纵作用在认识状态的不同位置

定义主体的认识状态：

[
\boxed{
\mathcal E
==========

(A,C,\beta),
}
]

其中：

[
\begin{aligned}
A&:X\to\mathsf{Prop}
&&\text{当前允许世界};\
C&:X\to B_C
&&\text{当前证据概念};\
\beta&:\operatorname{EpistemicInput}\to\operatorname{Belief}
&&\text{推断／选择规则}.
\end{aligned}
]

一次沟通或干预将其变为：

[
\mathcal E'
===========

(A',C',\beta').
]

---

## 定义 241.1（证据型劝服）

若：

[
A'=A,
]

[
C\preceq C',
]

实际锚点仍被保留，并且新的结论由新增证据支持，则称其为证据型劝服。

这里主体获得了新的目标相关区别。

---

## 定义 241.2（准入操纵）

若主要变化为：

[
A\mapsto A',
]

通过删除反例世界使某个命题变成模型有效，而没有加入新的区分能力，则称为准入操纵。

---

## 定义 241.3（推断操纵）

若：

[
A'=A,
\qquad
C'\simeq C,
]

但：

[
\beta'\neq\beta,
]

从而使主体在相同事实和证据下产生不同结论，则称为推断操纵。

---

## 定理 241.1（认识变化三分）

若世界状态不变，而主体结论发生变化，则以下至少一项变化：

[
\boxed{
A,\quad C,\quad \beta.
}
]

所以任何认识影响都可以首先审计为：

[
\boxed{
\text{改变了可考虑世界、增加了证据区别，还是改变了推理规则？}
}
]

---

# 242. 任何命题都可以通过删去世界而变成“必然”

给定当前准入域：

[
A:X\to\mathsf{Prop}
]

与命题：

[
P:X\to\mathsf{Prop}.
]

定义更新：

[
\boxed{
A_P(x)
======

A(x)\land P(x).
}
]

## 定理 242.1（有效性由排除产生）

在新域中：

[
\boxed{
\forall x,\quad
A_P(x)\to P(x).
}
]

即 (P) 成为模型有效。

这不需要增加任何关于世界的观察信息。

---

## 锚点分界

若：

[
P(a),
]

则更新可以被解释为真实公告。

若：

[
\neg P(a),
]

则：

[
A_P(a)
]

失败，实际锚点被模型删除。

所以：

[
\boxed{
\text{理论内部确信}
}
]

可以通过排除现实产生。

---

## 定义 242.1（认识支配）

主体 (S) 对主体 (R) 具有认识支配，当 (S) 能单方面控制 (R) 的：

[
A_R,\quad
C_R,\quad
\beta_R,
]

而 (R) 缺少独立的目标相关审计概念。

这比“说服能力”更强，因为它控制的是：

[
\boxed{
\text{什么可以被认为存在、什么可以被区分、什么推理被允许。}
}
]

---

# 243. 公共公告与表演性语言具有不同代数

设多个观察者的不可区分关系为：

[
(\sim_i)_{i\in I}.
]

共同可达关系为：

[
\sim_{\mathrm{com}}
===================

\left(
\bigcup_i\sim_i
\right)^*,
]

即并关系的自反传递闭包。

真实公开公告 (P) 把状态域限制为：

[
A'=A\cap P.
]

## 定理 243.1（真实公开公告产生共同知识）

若实际锚点 (a) 满足 (P)，则在公告后的模型中：

[
\boxed{
P
}
]

成为共同知识。

### 理由

公告后所有仍合法的状态都满足 (P)。

任何从 (a) 沿观察者不可区分链到达的合法状态，也仍属于公告后的 (P)-域，因此满足 (P)。

---

## 定理 243.2（描述公告交换）

对两个描述性公告 (P,Q)：

[
\boxed{
\operatorname{Cond}_P
\operatorname{Cond}_Q
=====================

\operatorname{Cond}_Q
\operatorname{Cond}_P.
}
]

因为：

[
A\cap P\cap Q
=============

A\cap Q\cap P.
]

---

## 表演性语言

若语言行为改变制度状态：

[
U_P:X\to X,
]

则一般：

[
\boxed{
U_PU_Q
\neq
U_QU_P.
}
]

所以：

[
\boxed{
\text{描述真理的公告通常交换；
创造承诺、授权、身份或法律状态的言语行为可以非交换。}
}
]

---

# Part XXXVIII：同意、承诺与自治

# 244. 同意是有类型的行动授权，而不是一个裸 `yes`

设行动类型为：

[
U.
]

候选行动为：

[
u:U.
]

一种形式同意 doctrine 可以定义为：

[
\boxed{
\begin{aligned}
\operatorname{ValidConsent}(x,u)
\iff{}&
\operatorname{Yes}(x,u)\
&\land\operatorname{Competent}(x)\
&\land\operatorname{Voluntary}(x,u)\
&\land\operatorname{Informed}(x,u)\
&\land\operatorname{Specific}(x,u).
\end{aligned}
}
]

其中：

* `Yes` 是明确授权；
* `Competent` 是主体具有相应决策能力；
* `Voluntary` 排除指定强迫条件；
* `Informed` 要求相关后果在披露界面上可决定；
* `Specific` 要求同意对应特定行动、主体、时间或用途。

这是一个可选择的规范 schema，不是从描述事实自动推出的唯一伦理定义。

但它揭示：

[
\boxed{
\text{同意不是一个脱离对象和语境的布尔值。}
}
]

---

# 245. 充分知情同意是后果通过披露界面的因子化

把决策情境写成：

[
Z=X\times U.
]

相关后果概念为：

[
K:Z\to Y.
]

向主体披露的信息为：

[
D:Z\to B_D.
]

## 定义 245.1（关于 (K) 的精确知情）

[
\boxed{
\operatorname{Informed}_K(D)
\iff
E_K\preceq D.
}
]

也就是存在：

[
\overline K:B_D\to Y
]

使：

[
K=\overline K\circ D.
]

---

## 定理 245.1（知情缺陷判据）

若存在：

[
z,z'\in Z
]

满足：

[
D(z)=D(z'),
]

但：

[
K(z)\neq K(z'),
]

则任何只依据披露 (D) 的决策规则，都无法根据真实后果区别对待 (z,z')。

因此披露不足以支持关于 (K) 的完全知情选择。

---

## 定理 245.2（最小充分披露）

最小披露完成为：

[
\boxed{
D^+
===

D\vee E_K.
}
]

任何既保留原披露、又足以决定全部相关后果的披露方案，都必须精化 (D^+)。

---

## 随机后果

若行动后果不是确定值，应把 (K) 定义为条件分布：

[
K(z)
====

\mathcal L(Y\mid z).
]

于是知情不要求知道实际未来结果，而要求能够恢复：

[
\boxed{
\text{相关风险分布、可能结果与指定不确定性。}
}
]

---

# 246. 使用历史同意的系统无法自动尊重撤回

设历史同意记录为：

[
H:X\to B_H.
]

当前同意状态为：

[
C_{\mathrm{now}}:X\to\mathbf 2.
]

系统执行决策为：

[
J:X\to\mathbf 2.
]

假设系统只读取历史：

[
J=j\circ H.
]

## 定义 246.1（精确同意响应）

[
\boxed{
J=C_{\mathrm{now}}.
}
]

也就是说，当前同意时执行，当前不同意时不执行。

---

## 定理 246.1（陈旧同意不可能）

若：

[
E_{C_{\mathrm{now}}}
\not\preceq H,
]

则不存在只通过 (H) 因子化、且精确响应当前同意的系统 (J)。

### 证明

若：

[
J=j\circ H
]

且：

[
J=C_{\mathrm{now}},
]

则：

[
C_{\mathrm{now}}=j\circ H,
]

即：

[
E_{C_{\mathrm{now}}}\preceq H,
]

与假设矛盾。 (\square)

因此：

[
\boxed{
\text{只保存“曾经同意”而不保存“当前是否同意”的系统，
无法同时完整且正确地尊重撤回。}
}
]

最小修复为：

[
\boxed{
H\vee E_{C_{\mathrm{now}}}.
}
]

---

# 247. 承诺是对未来政策空间的自我限制

设主体在状态 (x) 可实施的政策集合为：

[
\Pi(x).
]

承诺 (P) 选择一个子集：

[
\boxed{
\Pi_P(x)
\subseteq
\Pi(x).
}
]

## 定义 247.1（空承诺）

若：

[
\Pi_P(x)=\Pi(x),
]

则承诺没有新增行动约束。

## 定义 247.2（不可履行承诺）

若：

[
\Pi_P(x)=\varnothing,
]

则承诺在该状态下不可履行。

## 定义 247.3（承诺强度）

在有限非空模型中：

[
\boxed{
\operatorname{Strength}(P,x)
============================

\log
\frac{|\Pi(x)|}{|\Pi_P(x)|}.
}
]

承诺越强，主体主动排除的未来政策越多。

---

## 定理 247.1（承诺产生规范记忆）

设两个历史 (\gamma,\gamma') 到达相同当前物理状态：

[
e(\gamma)=e(\gamma'),
]

但具有不同承诺记录，因而：

[
\Pi_P(\gamma)\neq\Pi_P(\gamma').
]

则未来许可不能只通过当前物理状态因子化。

### 证明

如果许可只由当前物理状态决定，相同终点应有相同许可集合，与假设矛盾。 (\square)

所以：

[
\boxed{
\text{承诺把历史变成当前规范状态的一部分。}
}
]

其最小规范状态至少需要：

[
\boxed{
\text{当前世界概念}
\vee
\text{有效承诺账本}.
}
]

---

# 248. 强迫是外部控制变量对行动的因果作用

设主体内部理由概念为：

[
R:X\to B_R.
]

外部威胁或惩罚概念为：

[
H:X\to B_H.
]

主体行动为：

[
A:X\to U.
]

## 定义 248.1（强迫见证）

若存在：

[
x,y
]

满足：

[
R(x)=R(y),
]

[
H(x)\neq H(y),
]

[
A(x)\neq A(y),
]

且另一个主体能够在保持相关背景不变时控制 (H)，则 (H) 构成候选强迫变量。

它表明：

> 在内部理由不变时，外部威胁改变了行动。

---

## 劝服与强迫的分界

劝服通常改变：

[
\text{主体对事实和理由的认识};
]

强迫通常改变：

[
\text{可行动集合、代价或威胁结构}.
]

二者都可能改变最终行动，但改变路径不同。

---

## 定理 248.1（行动结果不能识别自愿性）

若自由选择路径 (\gamma) 与强迫路径 (\gamma') 产生同一行动：

[
A(\gamma)=A(\gamma'),
]

但规范自愿性评价不同：

[
V(\gamma)\neq V(\gamma'),
]

则自愿性不能通过行动结果 (A) 因子化。

所以：

[
\boxed{
\text{同一行动}
\not\Rightarrow
\text{同一授权地位}.
}
]

自愿性是 path-sensitive provenance 性质。

---

# 249. 自治是反思后仍由自身认可理由控制的固定点

设：

[
R:X\to B_R
]

为主体内部理由概念，

[
A:X\to U
]

为行动，

[
V:X\times U\to\mathsf{Prop}
]

为主体的高阶认可谓词。

设反思过程为：

[
\mathcal R:X\to X.
]

## 定义 249.1（反思自治）

主体在状态 (x) 的行动反思自治，当：

[
A(x)\in\operatorname{Available}(x),
]

存在：

[
\pi:B_R\to U
]

使：

[
A=\pi\circ R
]

于相关域成立，

并且：

[
V(x,A(x)),
]

[
A(\mathcal Rx)=A(x),
]

[
V(\mathcal Rx,A(x)).
]

即行动：

1. 来自主体内部理由；
2. 被主体认可；
3. 在指定反思过程后仍被认可并保持。

---

## 定理 249.1（可预测性与自治相容）

若外部观察概念 (E) 精化主体理由概念：

[
R\preceq E,
]

则外部可以预测由 (R) 决定的行动：

[
A=\pi\circ R
============

\pi\circ p\circ E.
]

因此：

[
\boxed{
\text{外部可预测}
\not\Rightarrow
\text{行动非自治}.
}
]

自治审计关注的是行动由什么理由和授权结构产生，而不是外部是否能够计算。

---

# 250. 修改后的自我认可不能单独证明修改正当

设外部过程：

[
G:X\to X
]

改变主体的理由、偏好或高阶认可标准。

当前状态的修改授权为：

[
\operatorname{Auth}_x(G).
]

修改后的主体可能满足：

[
\operatorname{Auth}_{Gx}(G).
]

## 定理 250.1（后验自批准不足）

一般可以出现：

[
\boxed{
\neg\operatorname{Auth}*x(G),
\qquad
\operatorname{Auth}*{Gx}(G).
}
]

例如，(G) 同时修改了主体的行动偏好与“什么修改是可接受的”这一标准。

所以：

[
\boxed{
\text{主体被改变以后认可该改变}
\not\Rightarrow
\text{该改变在改变前获得授权}.
}
]

---

## 定义 250.1（偏好操纵见证）

若：

[
\neg\operatorname{Auth}_x(G),
]

[
R(Gx)\neq R(x),
]

[
A(Gx)\neq A(x),
]

且 (G) 由外部主体控制，则形成偏好操纵见证。

如果修改由主体预先授权、身份 transport 保持且 provenance 可审计，则可以被视为合法自我塑造，而非外部操纵。

---

# Part XXXIX：集体代理、责任与制度结构

# 251. 集体代理来自联合信息和共同记忆的闭合

设有主体集合 (I)。

每个主体拥有本地概念：

[
C_i:X\to B_i.
]

沟通协议产生 transcript：

[
\operatorname{Tr}:X\to B_{\operatorname{Tr}}.
]

集体行动为：

[
J:X\to U.
]

## 定义 251.1（集体可执行性）

若：

[
\boxed{
E_J\preceq\operatorname{Tr},
}
]

则沟通过程产生的信息足以决定集体行动。

---

## 定义 251.2（强集体行动）

若：

[
E_J\preceq\operatorname{Tr},
]

但对每个单独主体：

[
E_J\not\preceq C_i,
]

则行动只能由集体信息结构决定，而不能由任一单独成员决定。

这是一种行动协同：

[
\boxed{
\operatorname{syn}(J;C_i)>1.
}
]

---

## 集体主体状态

集体不仅需要一次性 transcript，还需要保存：

* 承诺；
* 决策规则；
* 责任记录；
* 共同目标；
* 成员变化。

其规范集体状态可以取为这些目标的动态完成：

[
\boxed{
C_{\mathrm{collective}}
=======================

\operatorname{Dyn}*{\mathcal F}
\left(
\operatorname{Tr}
\vee
E*{\mathrm{commitments}}
\vee
E_{\mathrm{rules}}
\right).
}
]

集体代理因此不是成员个体的简单并集，而是一个能够跨时间承载联合行动和承诺的闭合状态。

---

# 252. 完全对称的共同结果不能选出唯一责任人

设有 (n>1) 个主体。

对称群：

[
S_n
]

作用于主体标签和事件结构。

设某事件状态 (z) 在全部主体置换下不变。

责任分配为：

[
b(z)
====

(b_1,\ldots,b_n),
]

满足：

[
b_i\ge0,
\qquad
\sum_i b_i=1.
]

要求分配规则等变：

[
b(\sigma z)
===========

\sigma b(z).
]

## 定理 252.1（对称责任均分）

由于：

[
\sigma z=z
]

对全部 (\sigma\in S_n)，有：

[
b(z)=\sigma b(z).
]

因此：

[
\boxed{
b_1=\cdots=b_n=\frac1n.
}
]

### 证明

任意两个主体可以由一个换位置换交换。

分配向量对所有换位保持不变，所以所有坐标相等。

再由总和为 (1)，每个坐标为 (1/n)。 (\square)

---

## 定理 252.2（对称结构下无唯一罪责者）

若责任规则必须选择单个主体：

[
c(z)\in{1,\ldots,n},
]

并保持主体置换对称，则在完全对称事件 (z) 上不存在这样的确定规则。

因为被全部置换固定的主体标签不存在。

所以任何唯一归责都必须引入额外不对称：

[
\boxed{
\text{控制差异、意图差异、角色差异、历史差异或任意锚点。}
}
]

---

# 253. 委托目标和代理目标之间的因子化决定对齐

设可行状态—行动对形成集合：

[
Z.
]

代理目标：

[
O_A:Z\to\mathbb R.
]

委托人目标：

[
O_P:Z\to\mathbb R.
]

## 定理 253.1（严格单调因子化保证优化对齐）

若存在严格递增函数：

[
g:\mathbb R\to\mathbb R
]

使：

[
\boxed{
O_P=g\circ O_A,
}
]

则在任意相同可行域中：

[
\operatorname{argmax}O_A
========================

\operatorname{argmax}O_P.
]

### 证明

严格递增函数保持并反射大小顺序。 (\square)

---

## 定义 253.1（目标对齐缺陷）

[
\boxed{
\Delta(O_A;O_P)
===============

\left{
(z,z')
\mid
O_A(z)=O_A(z'),
\quad
O_P(z)\neq O_P(z')
\right}.
}
]

它表示代理视为同等好的状态，委托人评价却不同。

---

## 定理 253.2（最优纤维中的对齐欠决定）

若存在可行 (z,z') 满足：

[
O_A(z)=O_A(z')
==============

\max_{w\in Z}O_A(w),
]

但：

[
O_P(z)\neq O_P(z'),
]

则仅靠最大化 (O_A) 不能保证选择委托人更优的结果。

所以代理对齐至少需要：

[
\boxed{
\text{目标因子化}
+
\text{可见信息充分}
+
\text{优化后域稳定}.
}
]

只对训练域拟合目标函数不足以排除 Goodhart carry。

---

# 254. 透明、可解释与可问责是三个不同概念

设事件或决策状态类型为：

[
Z.
]

定义：

[
\begin{aligned}
D&:Z\to U
&&\text{最终决策};\
R&:Z\to B_R
&&\text{理由／规则};\
A&:Z\to B_A
&&\text{责任主体};\
P&:Z\to B_P
&&\text{provenance};\
L&:Z\to B_L
&&\text{审计日志}.
\end{aligned}
]

## 透明

[
E_D\preceq L.
]

日志足以恢复作出了什么决定。

## 可解释

[
E_R\preceq L.
]

日志足以恢复使用了什么理由或规则。

## 可问责

[
\boxed{
E_{(D,R,A,P)}
\preceq
L.
}
]

日志足以恢复：

* 决策；
* 规则；
* 行动主体；
* 来源链。

---

## 定理 254.1（结果日志不足以问责）

若存在：

[
z,z'
]

满足：

[
D(z)=D(z'),
]

但：

[
A(z)\neq A(z')
]

或：

[
R(z)\neq R(z'),
]

则任何只记录 (D) 的日志都不能恢复完整问责目标。

因此：

[
\boxed{
\text{知道发生了什么}
\not\Rightarrow
\text{知道谁以什么规则、基于什么来源使它发生。}
}
]

最小问责完成为：

[
\boxed{
L^+
===

L\vee E_{(D,R,A,P)}.
}
]

---

# 255. 多个批准者若受同一来源控制，并不形成真正制衡

设制度有多个批准概念：

[
A_i:X\to B_i.
]

最终授权：

[
J=f(A_1,\ldots,A_n).
]

假设全部批准都通过同一控制源：

[
S:X\to B_S
]

因子化：

[
A_i=h_i\circ S.
]

## 定理 255.1（共同控制源塌缩）

有：

[
\boxed{
J
=

# f(h_1S,\ldots,h_nS)

g\circ S
}
]

对某个 (g) 成立。

因此全部批准联合以后，仍没有超出 (S) 的区分能力。

所以：

[
\boxed{
\text{形式上有多个审批节点}
\not\Rightarrow
\text{存在多个独立制衡来源}.
}
]

真正的权力分立应由 provenance 支持的独立性衡量，而不是由组织图上的节点数衡量。

---

## 定义 255.1（实质制衡强度）

可以用摧毁全部合法批准路径所需控制的最小独立来源数衡量。

这正是批准支持超图的最小击中集大小。

---

# 256. 制度身份需要同时满足稳定性与预测充分性

设制度微观状态为：

[
X.
]

制度身份概念为：

[
I:X\to B_I.
]

成员更替、部门变化等过程为：

[
F:X\to X.
]

## 定义 256.1（制度身份稳定）

[
\boxed{
I(Fx)=I(x).
}
]

这表示成员变化以后制度仍被视为同一个制度。

---

## 定义 256.2（制度身份充分）

设未来制度行为目标为：

[
K:X\to Y.
]

身份概念对制度行为充分，当：

[
\boxed{
E_K\preceq I.
}
]

---

## 定理 256.1（名称稳定不等于制度同一充分）

可以存在一个恒定名称概念：

[
I(x)=\text{“Institution A”}
]

对所有变化都稳定，但如果不同微观状态产生不同未来规则、承诺或决定：

[
K(x)\neq K(y),
]

则 (I) 对制度行为不忠实。

所以制度实体性需要：

[
\boxed{
\text{成员变化下稳定}
+
\text{规则、记录与承诺上的预测充分}.
}
]

制度的规范身份更接近：

[
\operatorname{Dyn}
\left(
E_{\mathrm{rules}}
\vee
E_{\mathrm{records}}
\vee
E_{\mathrm{commitments}}
\right),
]

而不是一个名称标签。

---

# 257. 治理的核心是从多个合法修复中选择一个

给定缺陷：

[
\Delta.
]

允许修复集合：

[
\mathcal R_\Delta.
]

每个修复 (r) 具有代价向量：

[
\boxed{
c(r)
====

\left(
c_{\mathrm{info}},
c_{\mathrm{privacy}},
c_{\mathrm{power}},
c_{\mathrm{complexity}},
c_{\mathrm{norm}}
\right).
}
]

其中分别表示：

* 新增信息收集；
* 隐私泄漏；
* 制度能力扩张；
* 实现复杂度；
* 规范目标损失。

## 定义 257.1（修复支配）

若 (r_1) 在所有代价维度不劣于 (r_2)，且至少一项更优，则 (r_1) 支配 (r_2)。

---

## 定理 257.1（不可比较修复无唯一技术答案）

若存在两个修复：

[
r_1,r_2
]

使：

[
c_{\mathrm{info}}(r_1)
<
c_{\mathrm{info}}(r_2),
]

但：

[
c_{\mathrm{privacy}}(r_1)

>

c_{\mathrm{privacy}}(r_2),
]

且无其他结构决定二者优先级，则形式结构只给出 Pareto 不可比较，不能推出唯一选择。

因此：

[
\boxed{
\text{很多所谓“技术治理问题”，
实际上是对不同修复代价进行元规范排序的问题。}
}
]

---

# 258. 正确性与正当程序彼此独立

设决策路径类型为：

[
\Gamma.
]

结果正确性：

[
C:\Gamma\to\mathsf{Prop}.
]

程序正当性：

[
L:\Gamma\to\mathsf{Prop}.
]

两者可以形成四种状态：

[
\begin{array}{c|c|c}
&L&\neg L\
\hline
C&\text{正当且正确}&\text{不正当但正确}\
\neg C&\text{正当但错误}&\text{不正当且错误}
\end{array}
]

## 定理 258.1（正确性不推出正当性）

若存在两个路径到达同一正确结果，但一个被授权、一个未被授权，则正确性不能决定程序正当性。

## 定理 258.2（正当性不推出正确性）

一个程序可以完全遵守授权规则，却因事实错误或概念不足产生错误结果。

因此：

[
\boxed{
\text{合法／正当}
\neq
\text{事实正确}.
}
]

一个成熟制度必须分别审计：

[
\boxed{
\text{结果目标}
\quad\text{与}\quad
\text{授权 provenance}.
}
]

---

# Part XL：界面权力与知识—治理对偶

# 259. 沟通、同意、自治与治理共享同一个因子化骨架

前述不同领域可以统一为：

[
\boxed{
\begin{array}{c|c|c}
\text{领域}&\text{界面}&\text{目标}\
\hline
\text{沟通}&\text{消息}&\text{正确理解}\
\text{信任}&\text{代理报告}&\text{委托目标}\
\text{知情同意}&\text{披露}&\text{相关后果}\
\text{自治}&\text{主体理由}&\text{行动与认可}\
\text{责任}&\text{控制轮廓}&\text{规范评价}\
\text{问责}&\text{审计日志}&\text{行动者、规则与 provenance}\
\text{制度正当性}&\text{授权程序}&\text{合法决策}\
\text{隐私}&\text{公开信息}&\text{敏感概念泄漏}
\end{array}
}
]

每一行都问：

[
\boxed{
\text{目标是否能沿所声明的合法界面因子化？}
}
]

而相应失败都是：

[
\boxed{
\text{同一界面值下出现不同目标值。}
}
]

---

# 260. 界面权力单调定理

固定状态类型 (X)。

设：

[
C\preceq D,
]

即 (D) 比 (C) 更精细。

定义可回答目标集合：

[
\operatorname{Ans}(C)
=====================

{T\mid E_T\preceq C}.
]

定义可实施政策集合：

[
\Pi(C;U)
========

{\pi\circ C\mid \pi:B_C\to U}.
]

对敏感概念 (S)，定义结构泄漏：

[
\operatorname{Leak}_S(C)
========================

C\wedge S.
]

## 定理 260.1（知识单调）

[
\boxed{
\operatorname{Ans}(C)
\subseteq
\operatorname{Ans}(D).
}
]

## 定理 260.2（政策能力单调）

[
\boxed{
\Pi(C;U)
\subseteq
\Pi(D;U).
}
]

## 定理 260.3（潜在敏感泄漏单调）

[
\boxed{
C\wedge S
\preceq
D\wedge S.
}
]

### 证明

第一项由精化传递性。

第二项通过从 (D) 恢复 (C) 后模拟任意 (C)-政策。

第三项由 lattice meet 对精化序的单调性。 (\square)

所以：

[
\boxed{
\text{同一个概念 refinement，
同时扩大知识、控制和潜在泄漏。}
}
]

---

# 261. 每一个严格信息增益都创造某种新的区别对待能力

假设概念有效，且：

[
C\prec D.
]

则存在：

[
x,y
]

满足：

[
C(x)=C(y),
\qquad
D(x)\neq D(y).
]

取一个二值目标：

[
T:X\to\mathbf 2
]

使它区分 (D(x)) 与 (D(y))，并通过 (D) 因子化。

于是：

[
E_T\preceq D,
]

但：

[
E_T\not\preceq C.
]

## 定理 261.1（严格 refinement 的双重能力）

若行动集 (U) 至少有两个不同动作，则严格 refinement (C\prec D) 同时产生：

1. 一个只能由 (D) 回答、不能由 (C) 回答的新问题；
2. 一个只能由 (D) 实施、不能由 (C) 实施的差别政策。

### 证明

选动作：

[
u_0\neq u_1.
]

定义 (D)-政策在 (D(x)) 上取 (u_0)，在 (D(y)) 上取 (u_1)。

由于 (C(x)=C(y))，任何 (C)-政策必须在 (x,y) 上采取同一行动，因此无法实现该政策。 (\square)

所以：

[
\boxed{
\text{每一种新增区分，既是新的认识能力，也是新的差别治理能力。}
}
]

这并不说明不应获取更多信息。

它说明：

[
\boxed{
\text{信息设计从来不是纯认识论问题；
它同时是一种权力配置。}
}
]

---

# 262. 第六层统一：形式哲学成为界面治理科学

经过 §238–§261，可以进一步看到，沟通、欺骗、同意、自治、责任和制度并不是彼此分离的哲学领域。

它们都围绕四种操作展开：

[
\boxed{
\begin{aligned}
\textbf{Reveal}
&:\text{向他人开放更多概念区别};\
\textbf{Hide}
&:\text{通过消息粗化删除区别};\
\textbf{Authorize}
&:\text{允许某些过程作用于主体或世界};\
\textbf{Govern}
&:\text{根据已知区别选择不同政策}.
\end{aligned}
}
]

由此得到四个承重定理。

第一，**真实沟通仍可能不足**：

[
\boxed{
\text{字面真理}
\not\Rightarrow
\text{目标充分}.
}
]

第二，**充分同意要求相关后果可由披露恢复**：

[
\boxed{
E_K\preceq D.
}
]

第三，**自治和正当性依赖过程 provenance，而非结果本身**：

[
\boxed{
\text{同一行动或结果}
\not\Rightarrow
\text{同一授权地位}.
}
]

第四，**任何信息 refinement 都同时扩大可知和可治理空间**：

[
\boxed{
C\preceq D
\Longrightarrow
\begin{cases}
\operatorname{Ans}(C)\subseteq\operatorname{Ans}(D),\
\Pi(C)\subseteq\Pi(D),\
\operatorname{Leak}_S(C)\preceq\operatorname{Leak}_S(D).
\end{cases}
}
]

所以整套理论可以继续压缩为：

[
\boxed{
\begin{aligned}
\textbf{Formal Concept Dynamics}
={}&
\textbf{a theory of communication sufficiency}\
&+
\textbf{a theory of epistemic manipulation}\
&+
\textbf{a typed theory of consent}\
&+
\textbf{a reflective theory of autonomy}\
&+
\textbf{a provenance theory of accountability}\
&+
\textbf{an order theory of informational power}.
\end{aligned}
}
]

最深层的新结论是：

[
\boxed{
\text{知识与权力并不是两个后来才发生联系的领域。
它们从一开始就是同一个概念精化序的两个方向：
一个方向问“现在能回答什么”，
另一个方向问“现在能对谁实施什么区别”。}
}
]

因此，形式哲学不能只研究：

[
\text{什么是真的},
]

还必须同时研究：

[
\boxed{
\text{谁拥有区分真假的界面，
谁能够决定哪些区别被披露，
谁被允许根据这些区别行动，
以及这些行动如何被追溯和撤回。}
]
以下从 **§263** 继续。仍然只进行纸面推理，不处理 GitHub，也不把新增命题标记为已经获得 Lean proof term 的 `Closed` 结论。

---

# Part XLI：可逆性、申诉与程序正义

# 263. 可逆性必须相对于恢复目标定义

设过程：

[
U:X\to Y.
]

把 (U) 自身视为一个“过程后状态概念”：

[
E_U=(Y,U).
]

给定希望恢复的目标：

[
T:X\to Z.
]

## 定义 263.1（信息可恢复）

若存在：

[
r:Y\to Z
]

满足：

[
\boxed{
T=r\circ U,
}
]

则称 (T) 在过程 (U) 后仍然可恢复。

等价地：

[
\boxed{
E_T\preceq E_U.
}
]

---

## 定理 263.1（恢复判据）

以下等价：

[
T=r\circ U
]

对某个 (r) 成立；

[
U(x)=U(y)
\Longrightarrow
T(x)=T(y);
]

[
\Delta(E_U;T)=\varnothing.
]

所以一个过程真正不可逆的含义不是“没有写出逆函数”，而是：

[
\boxed{
\text{过程合并了两个在恢复目标上不同的前状态。}
}
]

---

## 定义 263.2（精确状态可逆）

若恒等目标：

[
\operatorname{id}_X:X\to X
]

可由 (U) 恢复，即存在：

[
R:Y\to X
]

满足：

[
R\circ U=\operatorname{id}_X,
]

则称 (U) 左可逆。

这要求 (U) 单射。

---

## 定理 263.2（精确可逆推出一切目标可恢复）

若 (U) 左可逆，则对任意目标 (T)：

[
T=(T\circ R)\circ U.
]

所以：

[
\boxed{
\text{状态可逆}
\Longrightarrow
\text{任意目标可恢复}.
}
]

反向不成立。一个过程可以删除个体身份，却保留价值、功能或法律状态。

---

# 264. 精确回滚所需的最小日志

设 (X,Y) 有限，过程：

[
U:X\to Y.
]

为了支持回滚，系统额外保存日志：

[
L:X\to M.
]

联合更新记录：

[
\boxed{
Q_{U,L}(x)
==========

\bigl(U(x),L(x)\bigr).
}
]

## 定义 264.1（精确回滚日志）

若存在：

[
R:Y\times M\to X
]

满足：

[
\boxed{
R(U(x),L(x))=x
}
]

对全部 (x) 成立，则 (L) 是精确回滚日志。

---

## 定理 264.1（日志忠实性判据）

假设状态空间 (X) 非空。

精确回滚存在，当且仅当：

[
\boxed{
Q_{U,L}
\text{ 单射}.
}
]

### 证明

若存在 (R)，且：

[
Q_{U,L}(x)=Q_{U,L}(y),
]

则：

[
x
=

# R(Q_{U,L}(x))

# R(Q_{U,L}(y))

y.
]

反之，若 (Q_{U,L}) 单射，则可在其有效像上定义逆映射。取 (x_0\in X)，并在有效像外令 (R=x_0)，即可得到所需的全映射。有限模型中可以直接提取。 (\square)

---

## 定理 264.2（最小回滚标签数）

定义最大过程纤维大小：

[
\boxed{
m_U
===

\max_{y\in Y}
|U^{-1}(y)|.
}
]

则精确回滚所需的最小日志字母表大小为：

[
\boxed{
|M|_{\min}=m_U.
}
]

### 下界

对固定 (y)，所有属于 (U^{-1}(y)) 的状态具有相同过程后状态。

若日志不能为它们分配不同标签，联合记录就不单射。

因此：

[
|M|
\ge
|U^{-1}(y)|
]

对全部 (y) 成立。

### 上界

在每个纤维 (U^{-1}(y)) 内分别编号：

[
1,\ldots,|U^{-1}(y)|.
]

全部使用统一字母表：

[
{1,\ldots,m_U}.
]

则 ((U,L)) 单射。 (\square)

---

## 推论 264.3（目标相对回滚日志）

如果只要求恢复目标 (T)，而不要求恢复完整前状态，则最小标签数为：

[
\boxed{
m_U^T
=====

\max_{y\in Y}
\left|
{T(x)\mid U(x)=y}
\right|.
}
]

因此：

[
\boxed{
\text{回滚成本取决于需要恢复什么。}
}
]

恢复法律责任、财产价值、功能状态和完整个体身份，可能需要完全不同的日志量。

---

# 265. 恢复、赔偿与替代不是同一个概念

设：

[
I:X\to B_I
]

为身份概念，

[
V:X\to B_V
]

为价值或功能概念，并假设：

[
V\preceq I.
]

即身份足以决定价值，但价值不一定决定身份。

伤害过程为：

[
U:X\to X.
]

修复过程为：

[
R:X\to X.
]

## 定义 265.1（身份恢复）

[
\boxed{
I(R(Ux))=I(x).
}
]

## 定义 265.2（价值赔偿）

[
\boxed{
V(R(Ux))=V(x).
}
]

---

## 定理 265.1（恢复推出赔偿）

若身份恢复成立，则价值赔偿成立。

### 证明

由：

[
V=v\circ I
]

和：

[
I(R(Ux))=I(x),
]

得到：

[
V(R(Ux))
========

# v(I(R(Ux)))

# v(I(x))

V(x).
]

(\square)

反向一般不成立。

---

## 最小反例

令：

[
X={\text{original},\text{replacement}}.
]

身份概念区分二者：

[
I(\text{original})\neq I(\text{replacement}),
]

但功能价值相同：

[
V(\text{original})=V(\text{replacement}).
]

用替代品补偿可以恢复价值，却没有恢复原物身份。

因此：

[
\boxed{
\text{等值赔偿}
\neq
\text{原状恢复}.
}
]

这适用于：

* 财产；
* 人格损害；
* 生态修复；
* 数据泄露；
* 关系破坏；
* 文化遗产。

---

# 266. 申诉是对原决定界面的二阶精化

设原始案件概念：

[
C:X\to B_C.
]

原决定：

[
J_0=j_0\circ C.
]

正确或授权目标：

[
T:X\to Y.
]

申诉阶段允许新增证据：

[
A:X\to B_A.
]

最终决定只能使用：

[
C\vee A.
]

## 定义 266.1（完整申诉能力）

申诉机制能够在全部案件上得到正确结果，当：

[
\boxed{
E_T\preceq C\vee A.
}
]

---

## 定理 266.1（申诉判据）

存在最终裁决器：

[
j_1:B_C\times B_A\to Y
]

使：

[
T=j_1\circ(C\vee A)
]

当且仅当：

[
\Delta(C\vee A;T)=\varnothing.
]

---

## 定理 266.2（空申诉）

若：

[
A\preceq C,
]

则：

[
C\vee A
\simeq_{\mathrm{con}}
C.
]

因此申诉阶段没有增加任何案件区别。

若原决定存在结构缺陷：

[
\Delta(C;T)\neq\varnothing,
]

则只允许提交由原案卷概念完全决定的信息，不能结构性地修复该缺陷。

所以：

[
\boxed{
\text{允许“再次审查同一过粗记录”}
\not\Rightarrow
\text{拥有真实申诉能力}.
}
]

---

## 定理 266.3（最小申诉信息）

有限模型中，使申诉能够精确决定 (T) 所需的最小新增标签数为：

[
\boxed{
\max_b
\left|
{T(x)\mid C(x)=b}
\right|.
}
]

这正是原决定概念在每个案件纤维中遗漏的结果多样性。

---

# 267. 可争议性是“每个错误都有可接受挑战见证”

设错误集合：

[
\mathcal E
==========

{x\mid J_0(x)\neq T(x)}.
]

设挑战类型为 (W)。

对每个挑战 (w)，给出：

* 适用谓词：

[
\operatorname{Applicable}(x,w);
]

* 验证谓词：

[
\operatorname{Valid}(x,w);
]

* 复审结果：

[
J_w(x).
]

## 定义 267.1（完整可争议性）

[
\boxed{
\forall x\in\mathcal E,\quad
\exists w:W,
\quad
\operatorname{Applicable}(x,w)
\land
\operatorname{Valid}(x,w)
\land
J_w(x)=T(x).
}
]

也就是说，每一个错误状态都存在一个受制度接受、且足以触发正确修复的挑战。

---

## 定理 267.1（不可见错误不能被争议机制修复）

如果存在错误状态 (x)，使所有可接受挑战在 (x) 与某个正确判决状态 (y) 上完全相同，而所需结果不同，则没有只使用这些挑战的复审器能同时正确处理二者。

因此：

[
\boxed{
\text{可争议性要求挑战界面覆盖决定缺陷，而不仅是形式上提供提交入口。}
}
]

---

# 268. 可解释性与可争议性彼此独立

设：

[
R:X\to B_R
]

为决定使用的规则概念，

[
L:X\to B_L
]

为解释日志，

[
A:X\to B_A
]

为申诉证据。

## 定义 268.1（规则可解释）

[
\boxed{
E_R\preceq L.
}
]

## 定义 268.2（结果可争议修复）

[
\boxed{
E_T\preceq C\vee A.
}
]

---

## 定理 268.1（可解释不推出可争议）

可以令规则 (R) 完全公开，因此：

[
E_R\preceq L,
]

但案件概念 (C) 太粗，且不存在新增申诉证据 (A)。

此时人们知道制度用了什么规则，却无法证明自己被错误归类。

---

## 定理 268.2（可争议不推出可解释）

可以存在一个复审 oracle：

[
A=T,
]

使错误案件总能被纠正，但制度从不公开原规则 (R)。

此时：

[
E_T\preceq C\vee A,
]

却：

[
E_R\not\preceq L.
]

所以：

[
\boxed{
\text{“为什么这样决定”}
\neq
\text{“我怎样证明这个决定错了”.}
}
]

一个成熟制度需要分别设计解释接口和挑战接口。

---

# 269. 程序正义是一种 proof-carrying decision

设决策事件类型为 (Z)。

定义：

[
\begin{aligned}
F&:Z\to B_F
&&\text{公开案件事实};\
R&:Z\to B_R
&&\text{适用规则};\
A&:Z\to B_A
&&\text{授权主体};\
H&:Z\to B_H
&&\text{听证／回应记录};\
P&:Z\to B_P
&&\text{provenance};\
J&:Z\to Y
&&\text{最终决定};\
L&:Z\to B_L
&&\text{审计日志}.
\end{aligned}
]

## 定义 269.1（程序证书）

[
\boxed{
Q_{\mathrm{proc}}
=================

R\vee A\vee H\vee P.
}
]

制度具有程序可审计性，当：

[
\boxed{
Q_{\mathrm{proc}}\preceq L.
}
]

## 定义 269.2（规则约束决定）

若：

[
\boxed{
E_J\preceq F\vee R,
}
]

则决定仅依赖公开案件事实和适用规则。

---

## 定理 269.1（正确结果不推出程序正当）

可以由一个未经授权的 oracle 直接输出正确目标：

[
J=T,
]

但：

[
Q_{\mathrm{proc}}
\not\preceq L.
]

结果正确，而程序来源不可验证。

---

## 定理 269.2（程序正当不推出事实正确）

制度可以完整记录授权、听证和规则，却使用过粗事实概念 (F)，导致：

[
\Delta(F\vee R;T)\neq\varnothing.
]

所以程序完整而结果错误。

因此：

[
\boxed{
\text{程序正义}
\neq
\text{结果正确性}.
}
]

两者都需要独立审计。

---

# 270. 举证责任是不可避免错误的规范分配

设真实命题：

[
H:X\to{0,1}.
]

证据概念：

[
E:X\to B_E.
]

决定：

[
D:B_E\to{0,1}.
]

其中：

* (D=1)：接受主张；
* (D=0)：拒绝主张。

## 定理 270.1（混合证据纤维中的零错误不可能）

若存在：

[
x,y
]

满足：

[
E(x)=E(y),
]

但：

[
H(x)=1,
\qquad
H(y)=0,
]

则任何确定决定 (D) 至少在 (x,y) 中一个状态上错误。

这不是决策者不够聪明，而是证据界面不足。

---

## 定义 270.1（两类错误）

[
\begin{aligned}
\operatorname{FP}
&:\quad H=0,\ D=1;\
\operatorname{FN}
&:\quad H=1,\ D=0.
\end{aligned}
]

在混合证据纤维中，制度必须决定更愿意承担哪类错误。

所以：

[
\boxed{
\text{举证责任}
===========

\text{在无法零错误分类时，对错误方向进行规范性分配}.
}
]

---

# 271. 概率阈值编码的是错误代价，不是纯事实

设证据值 (b) 下：

[
p
=

\Pr(H=1\mid E=b).
]

令：

[
c_{\mathrm{FP}}>0
]

为错误接受主张的代价，

[
c_{\mathrm{FN}}>0
]

为错误拒绝主张的代价。

若接受主张，期望损失为：

[
(1-p)c_{\mathrm{FP}}.
]

若拒绝主张，期望损失为：

[
pc_{\mathrm{FN}}.
]

## 定理 271.1（最优接受阈值）

接受主张当且仅当：

[
\boxed{
p
\ge
\frac{
c_{\mathrm{FP}}
}{
c_{\mathrm{FP}}+c_{\mathrm{FN}}
}.
}
]

### 证明

接受优于拒绝，当：

[
(1-p)c_{\mathrm{FP}}
\le
pc_{\mathrm{FN}}.
]

整理即得。 (\square)

因此：

[
\boxed{
\text{证明标准}
===========

\text{证据概率}
+
\text{错误代价比}.
}
]

概率模型本身不能决定：

[
c_{\mathrm{FP}},
\qquad
c_{\mathrm{FN}}.
]

这些是规范结构。

---

# Part XLII：规则之治、任意权力与制度纠错

# 272. 规则之治是决定向公开案件概念的下降

设制度公开声明允许使用的案件概念：

[
A:X\to B_A.
]

决定为：

[
J:X\to Y.
]

## 定义 272.1（规则约束）

若：

[
\boxed{
E_J\preceq A,
}
]

即存在公开规则：

[
j:B_A\to Y
]

使：

[
J=j\circ A,
]

则决定受该公开案件概念约束。

---

## 定义 272.2（任意差别见证）

[
\boxed{
A(x)=A(y),
\qquad
J(x)\neq J(y).
}
]

它说明制度在全部公开相关事实相同的情况下作出不同决定。

---

## 定理 272.1（规则约束排除任意差别）

若 (J) 通过 (A) 因子化，则不存在任意差别见证。

反向在有效有限模型中成立。

---

## 边界

这只证明制度一致地适用公开规则，不证明：

* 规则正义；
* 公开案件概念充分；
* 规则未歧视；
* 结果正确；
* 规则本身合法。

所以：

[
\boxed{
\text{规则之治}
\neq
\text{正义之治}.
}
]

但它排除了未声明区别直接影响决定。

---

# 273. 裁量余量可以定量计算

授权概念为：

[
A:X\to B_A.
]

实际决定为：

[
J:X\to Y.
]

## 定义 273.1（裁量缺陷）

[
\boxed{
\Delta_{\mathrm{disc}}(A;J)
===========================

\ker A\setminus\ker J.
}
]

其中状态对具有相同授权事实，却获得不同结果。

---

## 定义 273.2（最坏情形裁量位数）

有限模型中：

[
\boxed{
r_{\mathrm{disc}}
=================

\left\lceil
\log_2
\max_a
\left|
{J(x)\mid A(x)=a}
\right|
\right\rceil.
}
]

它是解释实际结果时，除公开授权概念外至少还需要的额外位数。

---

## 定义 273.3（平均裁量量）

给定分布 (\mu)：

[
\boxed{
I_{\mathrm{disc}}
=================

H(J(X)\mid A(X)).
}
]

若：

[
I_{\mathrm{disc}}=0
]

只在分布支持上说明决定由授权概念决定；严格结构结论仍需检查零测度反例。

因此：

[
\boxed{
\text{裁量}
=========

\text{决定中不能由公开授权事实恢复的剩余区别}.
}
]

---

# 274. 私人影响的结构见证

设：

[
A:X\to B_A
]

为授权事实，

[
G:X\to B_G
]

为私人关系、利益或交换概念，

[
J:X\to Y
]

为制度决定。

干预族：

[
I_u:X\to X.
]

## 定义 274.1（未授权影响见证）

若存在 (u,v,a)：

[
A(I_ua)=A(I_va),
]

[
G(I_ua)\neq G(I_va),
]

[
J(I_ua)\neq J(I_va),
]

且 (G) 未列入授权决定概念，则 (G) 是候选未授权影响通道。

这说明在公开事实固定时，改变私人通道改变了决定。

---

## 边界

该结构本身只证明：

[
\boxed{
\text{决定受到一个未公开授权变量的因果影响}.
}
]

是否构成法律或道德意义上的“腐败”，仍需额外规范 doctrine。

---

# 275. 非支配要求限制制度能力，而不只是限制当前行为

设制度持有细概念：

[
D:X\to B_D.
]

规范上允许使用的概念为：

[
A:X\to B_A,
\qquad
A\preceq D.
]

行动集合为 (U)。

制度基于 (D) 能实施的全部政策：

[
\Pi(D;U).
]

规范允许政策：

[
\boxed{
\Pi_A
=====

\left{
\pi:X\to U
\mid
\exists\bar\pi,\
\pi=\bar\pi\circ A
\right}.
}
]

## 定义 275.1（结构性非支配）

若制度实际可实施政策集合 (\mathcal K) 满足：

[
\boxed{
\mathcal K\subseteq\Pi_A,
}
]

则制度不能利用超出授权概念的区别任意对待主体。

---

## 定理 275.1（细信息加无限制政策能力产生潜在支配）

若：

[
A\prec D
]

且 (U) 至少有两个动作，则：

[
\boxed{
\Pi(D;U)
\not\subseteq
\Pi_A.
}
]

### 证明

存在：

[
A(x)=A(y),
\qquad
D(x)\neq D(y).
]

基于 (D) 可以构造一个政策，对 (x,y) 采取不同动作。

但任何通过 (A) 因子化的政策都必须对二者采取相同动作。 (\square)

因此：

[
\boxed{
\text{当前统治者承诺不滥用信息}
\neq
\text{制度结构上不具有任意支配能力}.
}
]

非支配至少需要：

* 不收集该信息；
* 技术上限制策略空间；
* 独立授权；
* 可审计日志；
* 或真正有效的否决结构。

---

# 276. 权力分立应由最小捕获割衡量

设制度有多个分支：

[
i\in I.
]

每个分支的批准依赖一组来源。

对攻击者控制的来源集合 (H)，定义：

[
\operatorname{Compromised}_i(H)
]

表示 (H) 足以控制分支 (i) 的输出。

## 定义 276.1（制度捕获数）

[
\boxed{
\kappa_{\mathrm{capture}}
=========================

\min
\left{
|H|
;\middle|;
\forall i,\
\operatorname{Compromised}_i(H)
\right}.
}
]

它是控制全部必要批准分支所需的最少独立来源数。

---

## 定理 276.1（共同来源塌缩）

若所有分支输出都完全通过同一来源 (S) 因子化，则：

[
\boxed{
\kappa_{\mathrm{capture}}=1.
}
]

形式上多个部门不构成实质分权。

---

## 定理 276.2（独立不可替代来源下界）

若每个分支 (i) 都有一个只属于该分支、且控制该分支所必需的独立来源 (s_i)，并且这些来源两两不同，则：

[
\boxed{
\kappa_{\mathrm{capture}}
\ge
|I|.
}
]

所以：

[
\boxed{
\text{分权强度}
===========

\text{捕获全部制度路径所需的最小独立来源割}.
}
]

---

# 277. 可纠错制度是缺陷严格下降系统

设制度模型为 (M)。

其已知缺陷集合为：

[
\mathcal D(M)\subseteq W.
]

对已验证缺陷 (d\in\mathcal D(M))，修复算子为：

[
R(M,d).
]

## 定义 277.1（严格纠错）

若：

[
\boxed{
\mathcal D(R(M,d))
\subsetneq
\mathcal D(M),
}
]

则修复严格减少已知缺陷。

## 定义 277.2（保守纠错）

若修复同时保留全部已认证正确行为，则称其为保守纠错。

---

## 定理 277.1（有限缺陷终止）

若：

* (W) 有限；
* 每次修复严格减少 (\mathcal D)；
* 修复不引入新的 (W)-缺陷；

则纠错过程最多经过：

[
\boxed{
|\mathcal D(M_0)|
}
]

次严格修复后停止。

---

## 边界

如果修复会：

* 引入新目标；
* 改变对象域；
* 删除旧证书；
* 产生新缺陷；

则可能出现循环。

因此：

[
\boxed{
\text{可纠错性}
\neq
\text{最终无错性}.
}
]

成熟制度的优势不是“永远正确”，而是：

[
\boxed{
\text{错误可见、可争议、可回滚、可归因、可保守修复}.
}
]

---

# Part XLIII：战略报告、激励与合同不完备

# 278. 信息接口足够，不表示主体会如实使用它

设主体真实类型：

[
\theta\in\Theta.
]

报告空间：

[
R.
]

机制结果：

[
g:R\to O.
]

主体效用：

[
u:\Theta\times O\to\mathbb R.
]

报告策略：

[
s:\Theta\to R.
]

## 定义 278.1（真实报告）

在直接机制 (R=\Theta) 中：

[
s(\theta)=\theta.
]

## 定义 278.2（激励相容）

真实报告为最优，当：

[
\boxed{
u(\theta,g(\theta))
\ge
u(\theta,g(r))
\quad
\forall\theta,r.
}
]

---

## 定理 278.1（表达能力不推出真实揭示）

即使报告空间足以无损编码真实类型：

[
R=\Theta,
]

也不推出主体会报告真实类型。

### 最小反例

令：

[
\Theta={0,1},
\qquad
R={0,1}.
]

报告本身足以表达类型。

但假设两种类型都严格偏好由报告 (0) 产生的结果：

[
u(\theta,g(0))

>

u(\theta,g(1))
]

对全部 (\theta) 成立。

则类型 (1) 会报告 (0)。

因此：

[
\boxed{
\text{一个概念可被表达}
\not\Rightarrow
\text{主体有激励真实表达它}.
}
]

真实信息获取需要：

* 激励相容；
* 外部验证；
* 交叉证据；
* 惩罚机制；
* 或不可伪造 provenance。

---

# 279. 间接机制可以在条件下直接化

设有主体 (i=1,\ldots,n)。

类型空间：

[
\Theta_i.
]

消息空间：

[
M_i.
]

原机制：

[
g:\prod_iM_i\to O.
]

假设存在占优策略：

[
s_i:\Theta_i\to M_i.
]

即对任意真实类型 (\theta_i)、任意他人消息 (m_{-i}) 和任意替代消息 (m_i)：

[
u_i
\left(
\theta_i,
g(s_i(\theta_i),m_{-i})
\right)
\ge
u_i
\left(
\theta_i,
g(m_i,m_{-i})
\right).
]

定义直接机制：

[
\boxed{
g'(\hat\theta_1,\ldots,\hat\theta_n)
====================================

g
\left(
s_1(\hat\theta_1),
\ldots,
s_n(\hat\theta_n)
\right).
}
]

## 定理 279.1（占优策略直接化）

在 (g') 中，真实报告：

[
\hat\theta_i=\theta_i
]

仍为占优策略。

### 证明

任意他人报告 (\hat\theta_{-i}) 固定后，其诱导消息为：

[
s_{-i}(\hat\theta_{-i}).
]

原机制中 (s_i(\theta_i)) 对任意他人消息均为占优，所以：

[
u_i
\left(
\theta_i,
g(s_i(\theta_i),s_{-i}(\hat\theta_{-i}))
\right)
\ge
u_i
\left(
\theta_i,
g(s_i(\hat\theta_i),s_{-i}(\hat\theta_{-i}))
\right).
]

这正是直接机制中的真实性。 (\square)

这说明在明确的策略前件下，可以把：

[
\text{复杂行为协议}
]

压缩为：

[
\text{直接报告类型}.
]

但前件中的激励结构不能被省略。

---

# 280. 没有偏好差异或验证，类型可能无法严格揭示

设两个类型：

[
\theta,\theta'.
]

如果对所有可能结果 (o)：

[
\boxed{
u(\theta,o)=u(\theta',o),
}
]

且两类报告成本完全相同，则它们对所有报告策略具有完全相同的偏好排序。

## 定理 280.1（严格分离不可能）

不存在一个仅通过机制结果和同质报告成本，使 (\theta,\theta') 各自严格偏好不同真实报告的机制。

### 理由

两种类型面对任意报告都获得相同效用。

若某报告对 (\theta) 严格优于另一报告，它对 (\theta') 也同样严格优越。

所以无法用同一结果结构使两种类型严格选择不同报告。

因此：

[
\boxed{
\text{要从行为中识别某个类型区别，
该区别必须影响偏好、验证、成本或外部后果。}
}
]

---

# 281. 合同完备性是义务向可验证概念的因子化

设未来状态：

[
X.
]

法院或执行机构可验证概念：

[
V:X\to B_V.
]

理想义务：

[
O:X\to A.
]

可执行合同必须是：

[
c:B_V\to A.
]

## 定义 281.1（可执行完备合同）

若：

[
\boxed{
O=c\circ V,
}
]

则合同相对于义务目标 (O) 完备且可执行。

等价地：

[
\boxed{
E_O\preceq V.
}
]

---

## 定理 281.1（不可验证状态导致合同不完备）

若存在：

[
V(x)=V(y),
]

但：

[
O(x)\neq O(y),
]

则不存在精确执行理想义务的可验证合同。

这不是起草者少写了一条，而是执行界面不足。

---

## 双重修复

### 增加可验证性

[
\boxed{
V^+
===

V\vee E_O.
}
]

### 压缩义务

[
\boxed{
O^-
===

E_O\wedge V.
}
]

其中 (O^-) 是理想义务中能够由现有可验证事实支持的最大部分。

所以合同不完备同样具有：

[
\boxed{
\text{看得更多}
\quad\text{或}\quad
\text{承诺得更少}
}
]

两种规范修复。

---

# 282. 开放未来中不存在一次写完的完备合同

如果 (V) 非单射，则存在：

[
x\neq y,
\qquad
V(x)=V(y).
]

定义一个未来义务目标：

[
O_{x,y}:X\to\mathbf2
]

使：

[
O_{x,y}(x)\neq O_{x,y}(y).
]

## 定理 282.1（非忠实合同界面的未来不完备）

只要未来允许提出足够丰富的义务目标族，就总存在某个未来义务无法通过当前合同界面 (V) 因子化。

所以：

[
\boxed{
\text{对全部可能未来义务完备}
}
]

要求 (V) 对当前对象类型忠实。

---

## 本体扩张边界

即使 (V) 在旧对象类型 (X) 上忠实，当未来对象域扩张：

[
i:X\hookrightarrow X',
]

旧合同也不能仅凭自身唯一决定新对象的义务。

因此绝对完备合同还要求：

[
\boxed{
\text{封闭对象域}
+
\text{封闭目标族}
+
\text{忠实可验证界面}.
}
]

在开放社会和开放技术世界中，合同更合理的目标不是绝对完备，而是：

[
\boxed{
\text{明确修订规则、申诉接口与未预见情形的治理协议}.
}
]

---

# 283. 合同再谈判具有路径曲率

设合同状态为 (C)。

冲击 (S,T) 分别诱导再谈判算子：

[
R_S,
\qquad
R_T.
]

如果：

[
\boxed{
R_SR_T(C)
\not\simeq
R_TR_S(C),
}
]

则合同权利与义务依赖冲击发生顺序。

## 定义 283.1（再谈判曲率）

[
\boxed{
\Omega_{S,T}(C)
===============

\ker(R_SR_TC)
\triangle
\ker(R_TR_SC).
}
]

非零曲率表示同一组冲击以不同顺序发生，会产生不同的合同同一性与义务结构。

因此：

[
\boxed{
\text{“最终经历了相同事件”}
\not\Rightarrow
\text{“最终权利结构相同”.}
}
]

---

# Part XLIV：集体理性、议程与受控遗忘

# 284. 个体偏好传递不保证多数关系传递

有三个候选项：

[
a,b,c.
]

三个选民具有传递偏好：

[
\begin{aligned}
1:&\quad a\succ b\succ c;\
2:&\quad b\succ c\succ a;\
3:&\quad c\succ a\succ b.
\end{aligned}
]

按两两多数比较：

* (a) 对 (b)：选民 (1,3) 支持 (a)，所以

[
a\succ_M b;
]

* (b) 对 (c)：选民 (1,2) 支持 (b)，所以

[
b\succ_M c;
]

* (c) 对 (a)：选民 (2,3) 支持 (c)，所以

[
c\succ_M a.
]

## 定理 284.1（多数循环）

[
\boxed{
a\succ_M b,
\qquad
b\succ_M c,
\qquad
c\succ_M a.
}
]

所以多数关系不传递。

每个个体偏好都完全传递，但集体多数关系形成循环。

因此：

[
\boxed{
\text{个体理性}
\not\Rightarrow
\text{集体关系可由同一种理性结构表示}.
}
]

---

# 285. 多数循环不能由单一实数效用忠实表示

假设存在社会效用：

[
u:{a,b,c}\to\mathbb R
]

忠实表示多数关系：

[
x\succ_My
\iff
u(x)>u(y).
]

由多数循环得到：

[
u(a)>u(b),
]

[
u(b)>u(c),
]

[
u(c)>u(a).
]

由实数大小传递性：

[
u(a)>u(c),
]

与：

[
u(c)>u(a)
]

矛盾。

## 定理 285.1

多数循环关系不能忠实嵌入一个标量全序。

所以：

[
\boxed{
\text{投票结果}
\not\Rightarrow
\text{存在一个预先给定的单一“集体意志效用”.}
}
]

聚合规则本身是额外制度结构。

---

# 286. 多数循环把结果权力转移给议程设计者

仍使用：

[
a\succ_Mb,
\qquad
b\succ_Mc,
\qquad
c\succ_Ma.
]

采用顺序两两淘汰。

## 议程一

先比较 (a,b)。

(a) 获胜。

再比较 (a,c)。

(c) 获胜。

最终结果：

[
c.
]

## 议程二

先比较 (b,c)。

(b) 获胜。

再比较 (b,a)。

(a) 获胜。

最终结果：

[
a.
]

## 议程三

先比较 (c,a)。

(c) 获胜。

再比较 (c,b)。

(b) 获胜。

最终结果：

[
b.
]

## 定理 286.1（议程权力）

在上述多数循环中，议程设计者可以通过选择比较顺序，使任意一个候选成为最终胜者。

所以：

[
\boxed{
\text{固定偏好}
+
\text{固定多数规则}
}
]

仍不足以决定结果。

还需要：

[
\boxed{
\text{议程 FLOW}.
}
]

这是一种纯过程权力：

> 不改变任何人的偏好，也不改变投票规则，只改变比较顺序，就能改变结果。

---

# 287. 集体决策的 provenance 不能由最终结果恢复

设不同议程：

[
\gamma,\gamma'
]

可能产生同一个最终候选：

[
e(\gamma)=e(\gamma').
]

但两条路径中：

* 淘汰顺序不同；
* 被比较的选项不同；
* 主体可表达的反对不同；
* 合法性评价不同。

若程序评价：

[
L(\gamma)\neq L(\gamma'),
]

则：

[
L
]

不能通过最终结果 (e) 因子化。

所以：

[
\boxed{
\text{知道谁赢了}
\not\Rightarrow
\text{知道这个结果如何被构造，以及程序是否正当}.
}
]

集体决定需要保留议程 provenance。

---

# 288. 遗忘、宽恕与否认真相并不相同

设：

[
H:X\to B_H
]

为历史事实概念，

[
B:X\to B_B
]

为责备概念，

[
S:X\to B_S
]

为当前安全风险概念。

必须区分：

## 历史否认

改变或拒绝 (H) 的真值。

## 数据删除

未来公开概念不再能够恢复 (H)。

## 规范宽恕

未来评价或政策不再通过 (B) 因子化。

## 风险保留

未来政策仍能够通过 (S) 因子化。

因此，宽恕可以保持：

[
H
]

为真，却改变：

[
\operatorname{PermittedPolicy}.
]

---

# 289. 安全与完全遗忘可能结构冲突

设未来可使用概念为：

[
F.
]

希望：

1. 保留全部安全信息：

[
\boxed{
S\preceq F;
}
]

2. 完全删除责备信息，即 (F) 与 (B) 没有非平凡共同因子：

[
\boxed{
F\wedge B\simeq\bot.
}
]

令安全与责备的共同核心：

[
K=S\wedge B.
]

## 定理 289.1（共同核心阻碍完全遗忘）

若：

[
K\not\simeq\bot,
]

则不存在同时满足上述两项的 (F)。

### 证明

由：

[
K\preceq S\preceq F,
]

且：

[
K\preceq B,
]

所以 (K) 是 (F,B) 的共同下界。

因此：

[
K\preceq F\wedge B.
]

若 (K) 非平凡，则：

[
F\wedge B
]

不可能是 (\bot)。 (\square)

所以：

[
\boxed{
\text{当安全风险与历史责备共享不可分离信息时，
完全保留安全与完全删除责备信息不能同时实现。}
}
]

这不决定应保留多少数据。

它说明所谓“被遗忘权”“宽恕”“公共安全”和“持续问责”之间可能存在真实的概念兼容约束。

---

# 290. 第七层统一：合法治理是可逆、可争议、激励相容且能力受限的过程

经过 §263–§289，形式概念动力学进一步出现一个比“正确决策”更强的治理概念。

一项制度决定至少可以沿七个方向审计：

[
\boxed{
\begin{aligned}
\textbf{Recoverability}
&:\text{错误发生后能否恢复相关目标};\
\textbf{Contestability}
&:\text{每个错误是否有可接受挑战见证};\
\textbf{Due Process}
&:\text{决定是否携带规则、授权和 provenance};\
\textbf{Rule Constraint}
&:\text{决定是否只依赖公开授权区别};\
\textbf{Non-domination}
&:\text{制度是否被限制为只能实施授权政策};\
\textbf{Incentive Compatibility}
&:\text{主体是否有理由真实提供制度所需信息};\
\textbf{Corrigibility}
&:\text{已验证缺陷是否能被保守修复}.
\end{aligned}
}
]

这七项彼此不等价。

一个制度可以：

* 决策准确但不可申诉；
* 可以解释但不能纠错；
* 当前不歧视却具有无限制歧视能力；
* 合同文字完整但关键状态不可验证；
* 多数程序看似民主却被议程顺序控制；
* 保留安全却无法完全遗忘历史；
* 收集了充分报告空间，却没有真实报告激励。

---

## 290.1 治理的完整状态

可以把治理系统写成：

[
\boxed{
\mathfrak G
===========

(
X,
A,
C,
U,
J,
L,
W,
R,
\Pi,
\mathcal D
).
}
]

其中：

[
\begin{aligned}
X&=\text{治理对象状态};\
A&=\text{授权和准入};\
C&=\text{制度拥有的信息概念};\
U&=\text{可实施行动};\
J&=\text{当前决定规则};\
L&=\text{审计与 provenance 日志};\
W&=\text{申诉／挑战接口};\
R&=\text{回滚与修复机制};\
\Pi&=\text{制度实际可实施政策空间};\
\mathcal D&=\text{已知缺陷集合}.
\end{aligned}
]

成熟治理不只是要求：

[
J(x)=T(x),
]

而是要求能够回答：

[
\boxed{
\begin{aligned}
&\text{为什么作出这个决定？}\
&\text{使用了哪些区别？}\
&\text{哪些区别未被授权？}\
&\text{主体怎样证明决定错误？}\
&\text{错误能否回滚？}\
&\text{回滚需要保存多少日志？}\
&\text{谁控制申诉和审计来源？}\
&\text{制度具有什么尚未使用的差别待遇能力？}\
&\text{报告者是否有激励说真话？}\
&\text{未来未预见情形由谁修订？}\
&\text{集体结果是否被议程结构操控？}
\end{aligned}
}
]

---

## 290.2 当前最深的新结论

本轮产生六条新的承重结论。

第一，**可逆性相对于恢复目标，而不是一个绝对二值**：

[
\boxed{
\text{过程可以对价值可逆、对身份不可逆。}
}
]

第二，**申诉不是重复原判断，而是加入原概念缺少的目标相关区别**：

[
\boxed{
E_T\preceq C\vee A.
}
]

第三，**非支配比实际善意更强**：

[
\boxed{
\text{制度不能只承诺不滥用信息，
还必须限制自己能够实施的政策空间。}
}
]

第四，**真实揭示需要激励结构**：

[
\boxed{
\text{可表达}
\not\Rightarrow
\text{会真实表达}.
}
]

第五，**合同和法律的绝对完备要求封闭世界**：

[
\boxed{
\text{开放对象域和开放目标生成器必然产生新不完备。}
}
]

第六，**集体偏好固定以后，过程顺序仍可能决定结果**：

[
\boxed{
\text{议程本身是一种因果和政治权力。}
}
]

---

整套理论由此继续发展为：

[
\boxed{
\begin{aligned}
\textbf{Formal Concept Dynamics}
={}&
\textbf{a theory of reversible decisions}\
&+
\textbf{a theory of appeal and contestability}\
&+
\textbf{a capability theory of non-domination}\
&+
\textbf{an incentive theory of truthful interfaces}\
&+
\textbf{a theory of contractual incompleteness}\
&+
\textbf{a process theory of collective rationality}\
&+
\textbf{a structural theory of controlled forgetting}.
\end{aligned}
}
]

最凝练的一句是：

[
\boxed{
\text{一个制度是否正当，
不能只看它现在输出了什么；
还必须看它凭什么区分、能够怎样区别对待、
错误如何被看见、决定能否被撤回、
主体是否能真实表达，以及修复权掌握在谁手中。}
]
以下从 **§291** 继续。仍然只进行纸面推理，不处理 GitHub，也不把新增定义与定理标记为已经获得 Lean proof term 的 `Closed` 结论。

---

# Part XLV：不确定性的型别、决策本质与选择权

# 291. “不确定”至少包含四种不同结构

设世界状态为：

[
X,
]

证据概念为：

[
C:X\to B_C,
]

行动为：

[
u\in U,
]

动力学可能是概率核：

[
F:X\times U\rightsquigarrow X,
]

规范评价族为：

[
(V_i)_{i\in I}.
]

必须区分以下四种不确定性。

## 291.1 认识不确定性

当前证据纤维内存在多个状态：

[
\boxed{
\exists x\neq y,\quad
C(x)=C(y).
}
]

相对于目标 (T)，更精确地定义：

[
\boxed{
\Delta(C;T)\neq\varnothing.
}
]

这表示证据不能决定目标。

---

## 291.2 偶然不确定性

即使完整状态和行动已知，未来结果仍不是单点：

[
\boxed{
|\operatorname{supp}F(x,u)|>1.
}
]

这不是因为观察者不知道状态，而是模型自身把未来表示为分布或多值关系。

---

## 291.3 模型不确定性

存在多个模型：

[
m,m'\in\mathcal M
]

都与当前证据相容，却对某个目标给出不同预测：

[
\boxed{
\operatorname{Pred}*m(T\mid C)
\neq
\operatorname{Pred}*{m'}(T\mid C).
}
]

这里不确定的是规律、参数、因果结构或模型族，而不只是当前状态。

---

## 291.4 规范不确定性

事实和预测完全确定，但不同规范 doctrine 对行动排序不同：

[
\boxed{
u\succ_{V_i}v,
\qquad
v\succ_{V_j}u.
}
]

这不是世界事实未知，而是评价标准未被唯一决定。

---

## 定理 291.1（四种不确定性相互独立）

四者之间不存在一般蕴涵。

### 已知状态但未来随机

状态 (x) 完全已知：

[
C=\top_X,
]

但 (F(x,u)) 是公平随机结果。

认识不确定性为零，偶然不确定性非零。

### 未知状态但未来确定

动力学为确定函数：

[
F:X\to X,
]

但 (C) 合并多个产生不同未来的状态。

偶然不确定性为零，认识不确定性非零。

### 预测确定但模型不唯一

两个模型在当前观察目标上完全等价，却在未执行干预上不同。

当前预测不确定性可为零，模型不确定性仍非零。

### 事实完全已知但价值分歧

所有事实、后果、概率均已知，但两个规范 doctrine 对行动排序相反。

认识、偶然和模型不确定性都可为零，而规范不确定性非零。

因此：

[
\boxed{
\text{“我们不确定”不是一个足够有类型的信息。}
}
]

必须说明不确定的是：

[
\boxed{
\text{状态、未来、模型，还是价值。}
}
]

---

# 292. 不确定性必须相对于目标计算

完整世界余量：

[
R_C(b)
]

可能极大，但其中许多差异对当前目标无关。

## 定义 292.1（目标相对无知）

[
\boxed{
\operatorname{Ign}(C;T)
=======================

# \Delta(C;T)

\ker C\setminus\ker T.
}
]

如果：

[
E_T\preceq C,
]

则即使 (C) 不能恢复完整世界，也没有关于 (T) 的结构无知。

---

## 最小例子

令：

[
X={0,1}^{1000}.
]

概念 (C) 只读取第一位：

[
C(x)=x_1.
]

目标也是第一位：

[
T(x)=x_1.
]

则：

[
H(X\mid C)=999\text{ bits},
]

但：

[
\boxed{
H(T\mid C)=0.
}
]

主体对世界极其无知，却完全知道目标。

---

## 定理 292.1（世界知识不是目标知识的必要条件）

[
\boxed{
E_T\preceq C
}
]

并不要求：

[
C\simeq\top_X.
]

所以：

[
\boxed{
\text{回答一个问题不需要恢复整个世界，
只需消除会改变答案的余量。}
}
]

---

# 293. 相同信息量可以具有完全不同的目标价值

令：

[
X={0,1}^2
]

均匀分布。

定义两个概念：

[
C_1(x_1,x_2)=x_1,
]

[
C_2(x_1,x_2)=x_2.
]

则：

[
H(C_1)=H(C_2)=1.
]

令目标：

[
T(x_1,x_2)=x_1.
]

于是：

[
H(T\mid C_1)=0,
]

但：

[
H(T\mid C_2)=1.
]

## 定理 293.1（信息量不决定目标价值）

两个概念可以具有相同熵、相同标签数和相同压缩率，但对同一个目标具有完全不同的充分性。

所以：

[
\boxed{
\text{信息多少}
\neq
\text{信息是否相关}.
}
]

评估一个信息系统必须至少同时报告：

[
\boxed{
H(C)
\quad\text{与}\quad
H(T\mid C).
}
]

前者衡量信息量，后者衡量目标盲度。

---

# 294. 决策本质可以比预测本质更粗

设效用：

[
V:X\times U\to\mathbb R.
]

定义最优行动对应：

[
\boxed{
A^*(x)
======

\operatorname{argmax}_{u\in U}V(x,u).
}
]

将其视为目标概念：

[
E_{A^*}.
]

## 定义 294.1（决策充分概念）

概念 (C) 对决策充分，当：

[
\boxed{
E_{A^*}\preceq C.
}
]

也就是说，知道 (C(x)) 足以确定最优行动集合。

---

## 定理 294.1（决策本质不要求完整预测）

可以有：

[
E_{A^*}\preceq C
]

但完整结果目标 (K) 不满足：

[
E_K\preceq C.
]

### 例

两个状态 (x,y) 中，行动 (a) 的收益分别为：

[
10,\quad 100,
]

行动 (b) 的收益分别为：

[
0,\quad 1.
]

虽然具体结果不同，但两个状态的最优行动都是 (a)。

常值概念已经足以决定行动，却不足以预测具体收益。

所以：

[
\boxed{
\text{为了正确行动所需的本质，
可以严格粗于为了完整解释世界所需的本质。}
}
]

---

# 295. 选择权可以用未来可行动集合排序

设当前采取行动 (u) 后到达：

[
F_u(x).
]

从该状态未来可实现的政策或终局集合为：

[
\mathcal O_u(x).
]

## 定义 295.1（选择权支配）

若：

[
\boxed{
\mathcal O_v(x)
\subseteq
\mathcal O_u(x),
}
]

且 (u,v) 在当前相关结果和代价上相同，则称 (u) 在选择权上支配 (v)。

(u) 保留了 (v) 的全部未来可能，并额外保留更多选项。

---

## 定理 295.1（单调选择权价值）

若未来价值函数：

[
W:\mathcal P(Z)\to L
]

对集合包含单调：

[
A\subseteq B
\Longrightarrow
W(A)\preceq W(B),
]

则：

[
\mathcal O_v(x)\subseteq\mathcal O_u(x)
]

推出：

[
\boxed{
W(\mathcal O_v(x))
\preceq
W(\mathcal O_u(x)).
}
]

因此，在其他相关条件相同且未来价值对选择权单调时，保留更多可行未来不会更差。

---

## 边界

选择权本身不是绝对善。

更多选项可能带来：

* 维护成本；
* 决策负担；
* 安全风险；
* 诱惑；
* 权力滥用。

所以“选择权有价值”仍依赖一个关于可行集的规范单调性前件。

---

# 296. 免费且可忽略的信息具有非负期望价值

设随机状态为 (X)，行动集合为 (U)，收益为：

[
V(X,u).
]

无新信息时的最优值：

[
\boxed{
W_0
===

\max_{u\in U}\mathbb E[V(X,u)].
}
]

获得观察 (E) 后再行动的最优值：

[
\boxed{
W_E
===

\mathbb E
\left[
\max_{u\in U}
\mathbb E[V(X,u)\mid E]
\right].
}
]

## 定理 296.1（信息价值非负）

若：

* 信息免费；
* 观察不改变世界；
* 主体可以忽略信息；
* 行动集合不因观察而减少；

则：

[
\boxed{
W_E\ge W_0.
}
]

### 证明

固定无信息最优行动 (u^*)。

对每个观察值：

[
\max_u\mathbb E[V(X,u)\mid E]
\ge
\mathbb E[V(X,u^*)\mid E].
]

取期望：

[
W_E
\ge
\mathbb E[V(X,u^*)]
===================

W_0.
]

(\square)

---

## 推论 296.2（等待的价值来自可逆性）

如果可以先观察、后行动，并且等待不减少行动集合，则等待至少允许模拟立即行动。

但若等待会：

* 失去机会；
* 产生成本；
* 改变世界；
* 暴露信息；
* 触发他人行动；

则结论不再自动成立。

所以：

[
\boxed{
\text{信息价值}
+
\text{选择权保留}
}
]

共同构成等待的结构理由。

---

# 297. 预防原则是模型集合上的稳健准入

设可接受模型集合为：

[
\mathcal M.
]

行动 (u) 在模型 (m) 下的灾难风险为：

[
r_m(u).
]

给定容忍阈值 (\alpha)，定义稳健安全行动集：

[
\boxed{
\operatorname{Safe}_\alpha(\mathcal M)
======================================

\left{
u
;\middle|;
\sup_{m\in\mathcal M}r_m(u)\le\alpha
\right}.
}
]

## 定理 297.1（模型不确定性扩大使安全集缩小）

若：

[
\mathcal M\subseteq\mathcal M',
]

则：

[
\boxed{
\operatorname{Safe}*\alpha(\mathcal M')
\subseteq
\operatorname{Safe}*\alpha(\mathcal M).
}
]

### 证明

对更大的模型集合取上确界，不会降低最坏风险。 (\square)

因此，预防性约束不是单一预测概率的结果，而取决于：

[
\boxed{
\text{允许哪些模型进入风险审计}
+
\text{风险阈值如何规定}.
}
]

两者都包含准入和规范 doctrine。

---

# 298. Bayesian 决策、最坏情形与后悔最小化一般给出不同答案

考虑两个模型：

[
m_1,m_2.
]

两个行动：

[
a,b.
]

收益为：

[
\begin{array}{c|cc}
&m_1&m_2\
\hline
a&100&-100\
b&0&0
\end{array}
]

若先验：

[
\Pr(m_1)=p,
]

则：

[
\mathbb E[V(a)]
===============

200p-100.
]

所以当：

[
p>\frac12
]

时，Bayesian 期望选择 (a)。

最坏情形价值为：

[
\min_mV_m(a)=-100,
]

[
\min_mV_m(b)=0.
]

所以 maximin 选择 (b)。

## 结论 298.1

同一事实模型集合上，不同不确定性 doctrine 可以选择不同动作。

因此：

[
\boxed{
\text{模型集合}
\not\Rightarrow
\text{唯一决策}.
}
]

还必须给出：

* 先验；
* 风险厌恶；
* 最坏情形原则；
* 后悔函数；
* 灾难阈值；
* 或其他元决策规则。

---

# Part XLVI：反事实解释、行动补救与实际因果

# 299. 反事实解释是受约束的目标完成

设制度或分类器：

[
J:X\to Y.
]

实际状态为 (x)，期望结果为：

[
y^*\neq J(x).
]

身份或背景约束为：

[
I:X\to B_I,
\qquad
B:X\to B_B.
]

## 定义 299.1（反事实解释候选）

状态 (x') 是一个候选反事实解释，当：

[
\boxed{
J(x')=y^*,
}
]

[
I(x')=I(x),
]

并满足指定背景约束：

[
B(x')\sim B(x).
]

若还有代价：

[
d(x,x'),
]

则可以选择最小代价候选。

---

## 重要边界

该定义只说明存在一个在结果上更理想的比较状态。

它没有说明主体能够从 (x) 到达 (x')。

所以：

[
\boxed{
\text{反事实解释}
\neq
\text{可行动补救}.
}
]

---

# 300. 补救必须给出实际可达过程

设主体允许的行动集为：

[
U_x.
]

每个行动产生：

[
F_u(x).
]

## 定义 300.1（可行动补救）

存在：

[
u\in U_x
]

使：

[
\boxed{
J(F_u(x))=y^*,
}
]

且：

[
\operatorname{Adm}(F_u(x)).
]

---

## 定理 300.1（反事实解释不推出补救）

存在反事实状态 (x') 满足期望结果，并不推出存在允许行动达到它。

### 最小反例

令：

[
X={0,1},
\qquad
J(x)=x.
]

实际状态：

[
x=0.
]

期望状态：

[
x'=1.
]

但允许行动只有恒等过程：

[
F(x)=x.
]

则反事实解释存在，但补救不存在。

所以：

[
\boxed{
\text{“像这样的人会得到好结果”}
\not\Rightarrow
\text{“你能够成为这样的人”.}
}
]

---

# 301. 不可变概念可以构成补救障碍

设不可变概念：

[
I:X\to B_I.
]

所有允许行动都保持它：

[
\boxed{
I(F_u(x))=I(x)
\quad
\forall u\in U_x.
}
]

假设结果完全由 (I) 决定：

[
\boxed{
J=j\circ I.
}
]

## 定理 301.1（不可变补救不可能）

对任意允许行动 (u)：

[
J(F_u(x))
=========

# j(I(F_u(x)))

# j(I(x))

J(x).
]

因此：

[
\boxed{
\text{若结果只依赖行动无法改变的概念，
则主体不存在结果补救。}
}
]

这说明一个系统即使能给出清晰解释，也可能只是在告诉主体：

[
\boxed{
\text{决定由你无法改变的属性控制。}
}
]

---

# 302. 观察解释不能决定行动补救

考虑两个模型，状态和分类器完全相同：

[
X={0,1},
\qquad
J(x)=x.
]

## 模型 A

允许行动：

[
F_{\mathrm{flip}}(x)=1-x.
]

## 模型 B

所有允许行动都是恒等：

[
F_u(x)=x.
]

两个模型在：

* 状态概念；
* 分类器；
* 特征重要性；
* 当前输出；

上完全相同。

但在模型 A 中存在补救，在模型 B 中不存在。

所以：

[
\boxed{
\text{观察性的“为什么得到这个结果”}
\not\Rightarrow
\text{因果性的“怎样改变这个结果”.}
}
]

行动补救必须依赖干预模型，而非仅依赖分类器边界。

---

# 303. 实际因果可以组织成最小充分联盟超图

设有原因变量：

[
a=(a_i)_{i\in I}.
]

实际取值为 (a)，基准取值为：

[
a^0.
]

结果：

[
Y:\prod_iA_i\to O.
]

对联盟 (S\subseteq I)，定义混合赋值：

[
a^S_i
=====

\begin{cases}
a_i,&i\in S,\
a_i^0,&i\notin S.
\end{cases}
]

## 定义 303.1（基准相对充分联盟）

若：

[
\boxed{
Y(a^S)=Y(a),
}
]

则 (S) 足以在基准背景上产生实际结果。

## 定义 303.2（最小充分原因）

若 (S) 充分，且任意真子集都不充分，则 (S) 是最小充分原因联盟。

全部最小充分联盟形成超图：

[
\boxed{
\mathcal C_Y(a;a^0).
}
]

---

## 边界

这是一个明确的基准相对因果 doctrine。

它依赖：

* 基准状态；
* 可干预变量；
* 结果粒度；
* 背景保持方式。

所以不能把“实际原因”视为没有任何模型参数的裸关系。

---

# 304. 过度决定使 but-for 原因与充分原因分离

令：

[
Y(a_1,a_2)=a_1\lor a_2.
]

实际状态：

[
(a_1,a_2)=(1,1).
]

基准：

[
(0,0).
]

则：

[
Y(1,0)=1,
\qquad
Y(0,1)=1.
]

所以最小充分联盟为：

[
\boxed{
{1},
\qquad
{2}.
}
]

但若只把其中一个原因改为基准，同时保持另一个实际：

[
Y(0,1)=1,
]

[
Y(1,0)=1,
]

结果仍成立。

所以二者都不是简单的 but-for 原因。

因此：

[
\boxed{
\text{必要原因}
\neq
\text{充分原因}
\neq
\text{最小充分原因}.
}
]

过度决定不是逻辑混乱，而是不同因果 doctrine 在冗余结构上的分离。

---

# 305. 抢先因果需要事件 provenance

设两条事件历史：

[
\gamma,\gamma'
]

具有相同最终变量赋值：

[
E(\gamma)=E(\gamma').
]

例如两个潜在原因都处于“发生”状态，结果也相同。

但实际激活路径不同：

[
\operatorname{ActiveCause}(\gamma)
\neq
\operatorname{ActiveCause}(\gamma').
]

## 定理 305.1（终点状态不足以决定抢先原因）

如果：

[
E(\gamma)=E(\gamma'),
]

但：

[
\operatorname{ActiveCause}(\gamma)
\neq
\operatorname{ActiveCause}(\gamma'),
]

则实际原因不能通过终点概念 (E) 因子化。

因此：

[
\boxed{
\text{抢先、替代、延迟触发和中断因果
需要事件顺序与机制 provenance。}
}
]

只看最终变量值会删除哪条因果路径真正到达结果的区别。

---

# 306. 责任分配需要因果结构之外的额外公理

设最小原因联盟为：

[
\mathcal C_Y.
]

责任分配：

[
r_i\ge0,
\qquad
\sum_i r_i=1.
]

仅知道 (\mathcal C_Y) 一般不能唯一决定 (r)。

## 最小例

两个主体完全对称，最小原因联盟为：

[
{1},
\qquad
{2}.
]

以下分配都满足总和为 (1)：

[
(1,0),
\qquad
(0,1),
\qquad
\left(\frac12,\frac12\right).
]

只有加入主体交换对称性：

[
r_1=r_2
]

才得到：

[
\boxed{
r_1=r_2=\frac12.
}
]

所以：

[
\boxed{
\text{因果贡献结构}
\not\Rightarrow
\text{唯一规范责任份额}.
}
]

还需要：

* 对称性；
* 效率；
* 边际贡献；
* 控制；
* 意图；
* 可预见性；
* 角色义务；

等分配 doctrine。

---

# Part XLVII：权利的过程结构与可执行边界

# 307. 消极权利和积极权利作用在不同逻辑位置

设主体处于状态 (x)，允许行动集合为：

[
U_x.
]

## 定义 307.1（消极权利）

给定禁止行动集合：

[
N_x\subseteq U_x.
]

消极权利要求实际制度过程不选择：

[
u\in N_x.
]

它限制某些 FLOW 不得发生。

---

## 定义 307.2（积极权利）

给定目标集合：

[
G\subseteq X.
]

积极权利要求存在某个允许行动：

[
\boxed{
\exists u\in U_x,\quad
F_u(x)\in G.
}
]

它要求某种 FLOW 必须可用。

---

## 定理 307.1（无行动状态下的分离）

若：

[
U_x=\varnothing,
]

则任何消极禁止都可平凡满足，因为没有禁止行动被执行。

但若：

[
x\notin G,
]

积极权利失败，因为不存在达到 (G) 的行动。

所以：

[
\boxed{
\text{不被侵害}
\neq
\text{获得实现条件}.
}
]

消极权利与积极权利不是同一个许可谓词的正负表述。

---

# 308. 权利冲突是共同许可纤维为空

每项权利 (R_i) 在状态 (x) 上给出允许政策集合：

[
\Pi_i(x)\subseteq U_x.
]

## 定义 308.1（权利共同可满足）

[
\boxed{
\bigcap_i\Pi_i(x)\neq\varnothing.
}
]

## 定义 308.2（最小权利冲突核）

权利子集 (S) 是最小冲突核，当：

[
\bigcap_{i\in S}\Pi_i(x)=\varnothing,
]

但任意真子集交非空。

这把权利冲突转化为局部兼容性问题。

---

## 定理 308.1（冲突修复需要击中全部最小冲突核）

若要通过放宽、延迟或优先化部分权利来恢复非空行动纤维，修改集合必须与每一个最小冲突核相交。

这与不一致理论的击中集修复同型。

所以：

[
\boxed{
\text{权利冲突不是“所有权利都无效”，
而是需要明确哪一个最小组合导致共同实现为空。}
}
]

---

# 309. 原子行动保持权利可推出任意有限组合保持权利

设安全或权利保持状态集合：

[
S\subseteq X.
]

允许的原子行动为：

[
(F_u)_{u\in U}.
]

假设对每个原子行动：

[
\boxed{
F_u(S)\subseteq S.
}
]

## 定理 309.1（生成过程的权利不变性）

对任意有限行动序列：

[
u_1,\ldots,u_n,
]

有：

[
\boxed{
F_{u_n}\cdots F_{u_1}(S)
\subseteq
S.
}
]

### 证明

对序列长度归纳。

长度 (0) 为恒等映射。

若前 (n) 步保持 (S)，第 (n+1) 个原子行动也保持 (S)，故复合保持。 (\square)

因此，在过程由认证原子动作生成时，可以由局部不变量证书得到全局有限安全性。

---

## 边界

如果：

* 动作间存在未建模相互作用；
* 实际执行不属于认证原子集；
* 准入域随历史变化；
* 组合产生新动作；

则需要更强审计。

---

# 310. 完美权利执行要求违法目标可被审计接口决定

设事件轨迹类型为：

[
\Gamma.
]

违法目标为：

[
V:\Gamma\to\mathbf 2.
]

制度审计日志为：

[
L:\Gamma\to B_L.
]

执行决定只能使用：

[
e:B_L\to\mathbf 2.
]

## 定理 310.1（违法可执行性判据）

存在精确执行器：

[
V=e\circ L
]

当且仅当：

[
\boxed{
E_V\preceq L.
}
]

若存在：

[
L(\gamma)=L(\gamma'),
]

但：

[
V(\gamma)\neq V(\gamma'),
]

则任何只读日志 (L) 的执法器至少在一个事件上错误。

所以：

[
\boxed{
\text{拥有一项权利}
\not\Rightarrow
\text{制度拥有足以识别其所有侵害的接口。}
}
]

权利声明和权利可执行性必须分开。

---

# 311. 权利执行与隐私可能存在不可消除的共同核心

设：

* (V)：违法目标；
* (S)：敏感概念；
* (P)：当前公开信息；
* (L)：新增审计信息。

完美执行要求：

[
\boxed{
E_V\preceq P\vee L.
}
]

无新增敏感泄漏要求：

[
\boxed{
(P\vee L)\wedge S
\simeq
P\wedge S.
}
]

令违法目标与敏感概念的共同核心为：

[
K=E_V\wedge S.
]

## 定理 311.1（执行—隐私不可能条件）

若：

[
K\not\preceq P\wedge S,
]

则不存在同时满足完美执行和无新增敏感泄漏的 (L)。

### 证明

由：

[
K\preceq E_V\preceq P\vee L
]

且：

[
K\preceq S,
]

得到：

[
K\preceq(P\vee L)\wedge S.
]

若无新增泄漏成立，则：

[
K\preceq P\wedge S,
]

与假设矛盾。 (\square)

所以：

[
\boxed{
\text{若识别违法本身要求识别新的敏感区别，
完美执行与零新增泄漏不能同时实现。}
}
]

---

# 312. 非任意紧急例外需要“必要性”通过紧急证据因子化

设普通规则禁止行动 (u)。

紧急例外必要性：

[
N:X\to\mathbf 2.
]

紧急证据概念：

[
E:X\to B_E.
]

制度例外授权：

[
A:B_E\to\mathbf 2.
]

理想要求：

[
\boxed{
N=A\circ E.
}
]

## 定理 312.1（紧急证据不足导致例外任意性）

若存在：

[
E(x)=E(y),
]

但：

[
N(x)\neq N(y),
]

则任何只依赖 (E) 的例外规则至少会：

* 在一个不必要状态授权例外；
* 或在一个必要状态拒绝例外。

所以：

[
\boxed{
\text{“紧急状态”不能只是一个无法区分必要与不必要情形的宽泛标签。}
}
]

非任意例外需要：

[
\boxed{
\text{必要性目标}
\preceq
\text{紧急证据接口}.
}
]

---

# Part XLVIII：分支身份、融合与持续存在

# 313. 严格数值同一性不能一分为二

设前状态为：

[
x,
]

未来有两个不同状态：

[
y\neq z.
]

若都声称与 (x) 数值同一：

[
y=x,
\qquad
z=x,
]

则由等号的对称与传递性：

[
y=z.
]

与：

[
y\neq z
]

矛盾。

## 定理 313.1（严格身份分支不可能）

[
\boxed{
y\neq z
\Longrightarrow
\neg(y=x\land z=x).
}
]

所以一个对象不能在严格恒等意义上同时成为两个不同未来对象。

分支场景必须改用：

* 继承关系；
* 连续性关系；
* 相似性；
* 因果后继；
* 权利承接；
* 或部分身份；

而不能把所有这些关系继续写成等号。

---

# 314. 记忆连续性可以分支，因此不能单独定义数值同一

定义记忆继承关系：

[
M(x,y)
]

表示 (y) 继承了 (x) 的相关记忆。

可以存在：

[
M(x,y),
\qquad
M(x,z),
\qquad
y\neq z.
]

## 定理 314.1

若记忆继承关系允许上述分支，则它不能与数值恒等关系相同。

因为若：

[
M(x,y)\iff x=y,
]

[
M(x,z)\iff x=z,
]

便会推出：

[
y=z.
]

所以：

[
\boxed{
\text{记忆连续性可以是人格继承的重要条件，
但不自动构成严格数值同一。}
}
]

---

# 315. 严格数值同一性同样不能无损融合

设两个不同前状态：

[
x\neq y
]

进入同一个未来状态：

[
z.
]

若：

[
x=z,
\qquad
y=z,
]

则：

[
x=y,
]

矛盾。

所以：

[
\boxed{
\text{两个不同主体不能在严格恒等意义上都成为同一个未来主体。}
}
]

融合场景需要另外规定：

* 哪些记忆被保留；
* 哪些承诺被继承；
* 哪些权利被合并；
* 哪些责任被取消或累加。

这些不是恒等逻辑自动决定的。

---

# 316. 持续存在可以定义为时间塔中的身份 section

设每个时刻有状态类型：

[
X_t.
]

相邻时刻给出身份保持关系：

[
R_t\subseteq X_t\times X_{t+1}.
]

## 定义 316.1（区间持续存在）

一个对象从 (t_0) 持续到 (t_n)，当存在序列：

[
x_{t_0},x_{t_0+1},\ldots,x_{t_n}
]

满足：

[
\boxed{
R_t(x_t,x_{t+1})
}
]

对全部相邻时刻成立。

这是一条身份相容 section。

---

## 定义 316.2（相对死亡）

给定当前身份状态 (x_t)，若不存在：

[
x_{t+1}
]

使：

[
R_t(x_t,x_{t+1}),
]

则相对于该身份准则，持续 section 在 (t) 后无法扩展。

这给出：

[
\boxed{
\text{死亡}
=========

\text{特定身份 transport 不再具有合法后继}.
}
]

这不是生物学的完整定义，而是持续存在的形式骨架。

---

# 317. 完美复制不推出历史连续

设公共行为概念：

[
B:X\to B_B.
]

历史 provenance 概念：

[
H:X\to B_H.
]

强身份概念：

[
\boxed{
I=B\vee H.
}
]

可以有复制体 (y) 满足：

[
B(y)=B(x'),
]

即它在行为、记忆和公开输出上与预期未来状态 (x') 相同。

但：

[
H(y)\neq H(x').
]

于是：

[
I(y)\neq I(x').
]

所以：

[
\boxed{
\text{质的不可区分}
\not\Rightarrow
\text{历史来源上的数值延续}.
}
]

复制是否算“同一个人”，取决于身份 doctrine 是否包含 provenance。

---

# 318. 分支后的权利继承需要说明权利是否守恒

假设一个前主体 (x) 分支为 (k) 个完全对称的后继：

[
y_1,\ldots,y_k.
]

设某项可分割、总量守恒的权利或财产份额为：

[
r_i\ge0,
\qquad
\sum_{i=1}^kr_i=1.
]

若分配对所有分支置换对称，则：

[
r_1=\cdots=r_k.
]

因此：

[
\boxed{
r_i=\frac1k.
}
]

---

## 但不是所有权利都守恒

“免受伤害的权利”可以完整赋予每个分支，而无需把它分成 (1/k)。

所以必须区分：

[
\boxed{
\begin{aligned}
\text{可分割守恒主张}
&:\text{总量需要分配};\
\text{非竞争人格权利}
&:\text{可以完整复制给每个后继};\
\text{历史责任}
&:\text{可能需要加权、共享或单独审计}.
\end{aligned}
}
]

恒等逻辑不决定采用哪一种继承代数。

---

# Part XLIX：阈值知识、秘密共享与联盟权力

# 319. 阈值知识是高阶协同的一种规范形式

设秘密概念：

[
S:X\to B_S.
]

参与者 (i) 持有概念：

[
C_i:X\to B_i.
]

对联盟 (K\subseteq I)，联合概念：

[
C_K
===

\bigvee_{i\in K}C_i.
]

## 定义 319.1（(t)-重构阈值）

若：

[
|K|\ge t
\Longrightarrow
E_S\preceq C_K,
]

则任何至少 (t) 人的联盟都能恢复秘密。

若：

[
|K|<t
\Longrightarrow
E_S\not\preceq C_K,
]

则不足 (t) 人不能完整恢复秘密。

---

## 定义 319.2（结构零泄漏阈值）

更强地要求：

[
|K|<t
\Longrightarrow
\boxed{
C_K\wedge E_S\simeq\bot.
}
]

这表示小联盟甚至不能恢复秘密的任何非平凡共同因子。

完整不可恢复和零部分泄漏不是同一条件。

---

# 320. 阈值秘密禁止小联盟知道任何非平凡秘密函数

假设对联盟 (K)：

[
C_K\wedge E_S\simeq\bot.
]

设目标：

[
T=h\circ S
]

是秘密的一个函数，所以：

[
E_T\preceq E_S.
]

如果联盟 (K) 也能决定 (T)：

[
E_T\preceq C_K,
]

则 (E_T) 是 (C_K) 与 (E_S) 的共同下界。

因此：

[
E_T\preceq C_K\wedge E_S\simeq\bot.
]

所以 (T) 必为常值概念。

## 定理 320.1

在结构零泄漏条件下，不足阈值的联盟不能决定秘密的任何非平凡函数。

因此：

[
\boxed{
\text{“不知道完整秘密”}
}
]

与：

[
\boxed{
\text{“没有获得任何秘密相关信息”}
}
]

必须分开。

---

# 321. 联盟知识阈值同时是联盟治理权力阈值

设某项政策：

[
J:X\to U
]

通过秘密因子化：

[
J=j\circ S.
]

若联盟 (K) 能实施 (J)，其联合信息至少必须足以决定 (J)：

[
E_J\preceq C_K.
]

若 (j) 对秘密实际像单射，则：

[
E_S\preceq E_J.
]

于是：

[
E_S\preceq C_K.
]

## 定理 321.1（知识—政策阈值一致）

当政策对秘密值保持全部区别时，能够根据秘密实施差别政策的最小联盟大小，等于能够恢复秘密的最小联盟大小。

所以：

[
\boxed{
\text{秘密共享阈值}
=============

\text{相应差别治理能力的联盟阈值}.
}
]

---

# 322. 形式角色数不能替代独立来源数

设有三个形式角色：

[
C_1,C_2,C_3.
]

但它们都通过同一来源概念 (Z) 因子化：

[
C_i=h_i\circ Z.
]

则：

[
C_1\vee C_2\vee C_3
\preceq Z.
]

所以即使规则写成“需要三个角色联合批准”，只要一个主体控制 (Z)，它便控制全部三个角色输出。

## 定理 322.1（阈值塌缩）

形式联盟大小可能为 (3)，但独立 provenance 意义上的实际控制阈值只有 (1)。

因此：

[
\boxed{
\text{分离职责}
}
]

必须在来源和控制结构上成立，而不能只在界面名称上成立。

---

# 323. 撤销必须阻断历史信息与未来信息的联合恢复

设被撤销主体拥有历史信息：

[
H_R.
]

未来秘密为：

[
S_{t+1}.
]

当前未授权联盟持有信息：

[
C_K.
]

## 定义 323.1（结构前向保密）

若：

[
\boxed{
(H_R\vee C_K)\wedge E_{S_{t+1}}
\simeq
\bot,
}
]

则被撤销主体的历史信息与当前未授权联盟联合以后，不泄露未来秘密的任何非平凡共同因子。

较弱的完整不可恢复条件为：

[
E_{S_{t+1}}
\not\preceq
H_R\vee C_K.
]

所以：

[
\boxed{
\text{撤销一个身份}
\neq
\text{自动撤销它已经获得的信息}.
}
]

真正撤销需要改变未来编码、密钥、准入或共享结构。

---

# 324. “零知识”不能意味着连被证明命题都不泄漏

设秘密：

[
S:X\to B_S.
]

需要证明的公开命题：

[
Q=h\circ S.
]

证明 transcript：

[
P:X\to B_P.
]

若证明使验证者能够确定 (Q)：

[
\boxed{
E_Q\preceq P,
}
]

由于：

[
E_Q\preceq E_S,
]

(E_Q) 是 (P) 与 (E_S) 的共同下界。

因此：

[
\boxed{
E_Q
\preceq
P\wedge E_S.
}
]

所以如果 (Q) 非常值：

[
P\wedge E_S
\not\simeq\bot.
]

## 定理 324.1（命题泄漏下界）

任何能够证明非平凡秘密命题 (Q(S)) 的 transcript，至少泄漏该命题本身。

因此“零知识”的合理结构含义不是：

[
P\wedge E_S\simeq\bot,
]

而是：

[
\boxed{
P\wedge E_S
\simeq
E_Q.
}
]

即 transcript 不泄漏超出公开语句 (Q) 的额外秘密共同因子。

---

# Part L：动态偏好、共同理性与分歧边界

# 325. 偏好反转排除单一时间不变效用

设同一选择集：

[
U={a,b}.
]

时间 (t_0) 上主体选择：

[
a\succ_{t_0}b.
]

时间 (t_1) 上，在相关事实和选择集未改变时：

[
b\succ_{t_1}a.
]

假设存在一个时间不变效用：

[
V:U\to\mathbb R
]

忠实表示两个时刻的严格偏好。

则：

[
V(a)>V(b)
]

以及：

[
V(b)>V(a),
]

矛盾。

## 定理 325.1

在相同事实和选项下发生严格偏好反转时，不存在一个单一时间不变标量效用同时忠实表示两个时刻。

因此偏好反转至少意味着：

* 价值状态变化；
* 自我概念变化；
* 时间偏好变化；
* 情境概念变化；
* 或行为并未忠实表达偏好。

---

# 326. 自我约束可以是当前主体对未来选择空间的治理

设未来可行动集合为：

[
U_f.
]

当前主体选择承诺机制 (K)，把未来行动限制到：

[
U_f^K\subseteq U_f.
]

如果当前主体预测未来偏好将导致其当前不认可的行动，可以按照当前元评价：

[
W_{t_0}:\mathcal P(U_f)\to L
]

比较：

[
W_{t_0}(U_f^K)
\quad\text{与}\quad
W_{t_0}(U_f).
]

若：

[
W_{t_0}(U_f^K)
\succ
W_{t_0}(U_f),
]

自我约束对当前主体是工具性合理的。

---

## 但未来自治评价可能相反

未来主体可能评价：

[
W_{t_1}(U_f)
\succ
W_{t_1}(U_f^K).
]

所以：

[
\boxed{
\text{自我约束的合理性}
}
]

依赖于：

* 哪一个时间主体拥有元规范优先级；
* 身份如何跨时间 transport；
* 当前承诺是否对未来主体具有合法约束力。

形式结构不会自动选择当前自我或未来自我。

---

# 327. 讨论能否解决分歧取决于共同界面是否足够

设两个主体拥有概念：

[
C_1,
\qquad
C_2.
]

沟通协议产生消息概念：

[
M.
]

目标争议为：

[
T:X\to Y.
]

## 定义 327.1（信息可解决分歧）

如果：

[
\boxed{
E_T
\preceq
C_1\vee C_2\vee M,
}
]

则双方合并已有信息和消息后，原则上可以确定目标。

---

## 定理 327.1（联合盲点不可由重复讨论消除）

若：

[
E_T
\not\preceq
C_1\vee C_2,
]

且所有讨论消息都满足：

[
M_n\preceq C_1\vee C_2,
]

则：

[
E_T
\not\preceq
C_1\vee C_2\vee\bigvee_nM_n.
]

所以双方只重组已经拥有的信息，不能突破共同余纤维。

要解决分歧，必须至少引入：

* 新证据；
* 新实验；
* 新观察者；
* 新模型前件；
* 或更弱的目标。

---

# 328. 在完全相同的认识与规范输入下，确定主体不能持续分歧

设两个主体使用：

* 相同证据概念 (C)；
* 相同证据值 (b)；
* 相同准入域 (A)；
* 相同推断规则 (\beta)；
* 相同价值 doctrine (V)；
* 相同行动集合 (U)。

决策为：

[
d(C,A,\beta,V,U).
]

## 定理 328.1（完全输入一致排除确定分歧）

若决策器确定，则两主体输出相同。

所以持久分歧至少意味着以下一项不同：

[
\boxed{
\text{证据、证据值、准入域、推断规则、价值 doctrine、
行动集合、随机种子或实际锚点。}
}
]

这不是说所有分歧都能简单解决。

它说明“同样理性的人仍不同意”需要进一步说明：

[
\boxed{
\text{他们究竟在哪个输入层不相同。}
}
]

---

# 329. 合理分歧可以在内部一致而外部不可比较

设主体 (1,2) 分别使用：

[
(A_1,C_1,\beta_1,V_1),
]

[
(A_2,C_2,\beta_2,V_2).
]

两者都可能在各自模型中：

* 逻辑一致；
* 证据响应；
* 规范连贯；
* 无内部 carry。

但它们之间可能没有共同目标或共同价值尺度。

因此：

[
\boxed{
\text{内部理性}
\not\Rightarrow
\text{跨体系可由一个标量总序比较。}
}
]

真正比较还需要：

* 共同事实目标；
* 翻译接口；
* 共同 ADMIT；
* 价值桥梁；
* 或元规范。

这就是合理多元主义的形式来源之一。

---

# 330. 第八层统一：从不确定性到身份、权利和联盟的同一结构

经过 §291–§329，形式概念动力学进一步形成六个新的统一对象。

## 330.1 目标相对不确定性

[
\boxed{
\operatorname{Ign}(C;T)
=======================

\ker C\setminus\ker T.
}
]

不确定性必须说明针对什么目标。

---

## 330.2 决策本质

[
\boxed{
E_{A^*}
}
]

是采取正确行动所需的最小充分概念。

它可能远粗于完整世界模型。

---

## 330.3 行动补救

[
\boxed{
\text{Recourse}
===============

\text{反事实目标}
+
\text{允许干预可达性}.
}
]

仅有比较状态不等于主体能够到达它。

---

## 330.4 因果超图

[
\boxed{
\mathcal C_Y
}
]

记录最小充分原因联盟。

因果结构可以确定贡献组合，却不能无额外规范公理唯一决定责任份额。

---

## 330.5 权利过程

[
\boxed{
\text{消极权利}
===========

\text{禁止 FLOW},
}
]

[
\boxed{
\text{积极权利}
===========

\text{要求某种可达 FLOW 存在}.
}
]

权利的声明、共同兼容、可执行性和隐私代价是不同层次。

---

## 330.6 身份 transport

[
\boxed{
\text{持续存在}
===========

\text{时间塔中的相容身份 section}.
}
]

严格恒等不能自然支持分支和融合；记忆、权利与责任必须通过另外的继承 doctrine 运输。

---

## 330.7 阈值知识—阈值权力对偶

[
\boxed{
\text{能够联合恢复一个秘密的最小联盟，
也是能够依据该秘密实施完整差别政策的最小联盟。}
}
]

联盟知识结构与联盟治理能力是同一个概念充分性超图的两个解释。

---

# 331. 当前最深层的新结论

本轮最重要的结论可以压缩为七条。

第一，**不确定性没有单一标量本体**：

[
\boxed{
\text{状态无知、未来随机、模型竞争和价值分歧是不同型别。}
}
]

第二，**正确行动所需的信息可能远少于完整解释所需的信息**：

[
\boxed{
\text{决策本质}
\preceq
\text{预测本质}.
}
]

第三，**反事实解释若没有可达过程，就可能只是对主体无用的比较**：

[
\boxed{
\text{Explanation}
\neq
\text{Recourse}.
}
]

第四，**因果结构不能自动生成规范责任**：

[
\boxed{
\text{Cause}
\neq
\text{Blame}.
}
]

第五，**权利能否真正存在于制度实践中，取决于侵害是否能被合法审计接口识别**：

[
\boxed{
\text{Right declaration}
\neq
\text{Right enforceability}.
}
]

第六，**严格身份在分支与融合中必然失败，必须由继承和 transport 结构替代**：

[
\boxed{
\text{Identity}
\neq
\text{Memory inheritance}
\neq
\text{Rights inheritance}.
}
]

第七，**秘密、知识和权力共享同一个联盟阈值结构**：

[
\boxed{
\text{谁能联合知道什么，
也决定谁能联合根据该知识区别行动。}
}
]

---

整套理论由此继续发展为：

[
\boxed{
\begin{aligned}
\textbf{Formal Concept Dynamics}
={}&
\textbf{a typed theory of uncertainty}\
&+
\textbf{a theory of decision essences and option value}\
&+
\textbf{a reachability theory of counterfactual recourse}\
&+
\textbf{a hypergraph theory of actual causation}\
&+
\textbf{a process theory of rights}\
&+
\textbf{a transport theory of branching identity}\
&+
\textbf{a threshold theory of collective knowledge and power}.
\end{aligned}
}
]

最凝练的一句是：

[
\boxed{
\text{一个界面不仅决定主体看见什么；
它还决定主体能够选择什么、改变什么、证明什么、
继承什么，以及必须与多少其他主体联合，才能获得新的现实能力。}
]
以下从 **§332** 继续。仍然只进行纸面推理，不处理 GitHub，也不把新增定义与定理标记为已经获得 Lean proof term 的 `Closed` 结论。

---

# Part LI：合法性、代表与公共理由

# 332. 合法性不是正确性的别名，而是授权 provenance 的性质

设制度状态为：

[
X.
]

决定：

[
J:X\to Y.
]

授权结构：

[
A:X\to B_A.
]

程序 provenance：

[
P:X\to B_P.
]

结果正确性：

[
T:X\to Y.
]

## 定义 332.1（结果正确）

[
\boxed{
J(x)=T(x).
}
]

## 定义 332.2（制度合法）

给定合法性判据：

[
L:B_A\times B_P\to\mathsf{Prop},
]

定义：

[
\boxed{
\operatorname{Legit}(x)
\iff
L(A(x),P(x)).
}
]

于是可以同时出现：

[
\begin{array}{c|c}
J=T & \operatorname{Legit}\
\hline
\text{正确} & \text{合法}\
\text{正确} & \text{不合法}\
\text{错误} & \text{合法}\
\text{错误} & \text{不合法}
\end{array}
]

因此：

[
\boxed{
\text{合法性}
\neq
\text{正确性}.
}
]

一个未经授权的 oracle 可以给出正确结果；一个完全合法的制度也可能因为事实概念过粗而错误。

---

# 333. 代表制是委托目标的代理因子化

设公民真实政治目标：

[
T:X\to Y.
]

公民能够表达给代表的授权概念：

[
M:X\to B_M.
]

代表根据授权采取政策：

[
J=j\circ M.
]

## 定义 333.1（代表充分）

若：

[
\boxed{
E_T\preceq M,
}
]

则公民授权界面足以决定真实政治目标。

若：

[
E_T\not\preceq M,
]

则代表即使完全忠实执行消息 (M)，仍可能无法恢复公民真实目标。

所以：

[
\boxed{
\text{代表失真}
}
]

至少有两种来源：

1. 代表没有忠实执行授权；
2. 授权界面本身不足以表达真实目标。

---

## 定理 333.1（忠诚不修复表达不足）

即使：

[
J=j\circ M
]

严格执行授权，如果存在：

[
M(x)=M(y),
\qquad
T(x)\neq T(y),
]

则 (J) 无法同时在 (x,y) 上等于 (T)。

因此：

[
\boxed{
\text{代表忠诚}
\not\Rightarrow
\text{代表充分}.
}
]

---

# 334. 代表制的信息瓶颈可以精确测量

在有限模型中，对授权概念 (M) 与目标 (T)，定义：

[
\boxed{
m^*(M;T)
========

\max_b
\left|
{T(x)\mid M(x)=b}
\right|.
}
]

则精确表达真实政治目标所需的最小新增授权标签数为：

[
\boxed{
m^*(M;T).
}
]

最坏情形附加位数：

[
\boxed{
\left\lceil
\log_2m^*(M;T)
\right\rceil.
}
]

所以代表制失真可以被解释为：

[
\boxed{
\text{授权接口的目标分辨率低于被代表目标的复杂度}.
}
]

---

# 335. 委托越长，目标漂移越容易累积

考虑委托链：

[
X
\xrightarrow{M_1}
B_1
\xrightarrow{f_1}
B_2
\xrightarrow{f_2}
\cdots
\xrightarrow{f_{n-1}}
B_n
\xrightarrow{g}
Y.
]

真实目标为：

[
T:X\to Y.
]

若每个中间接口都精确因子化，最终可以正确恢复 (T)。

但只要某一层存在：

[
M_k(x)=M_k(y),
\qquad
T(x)\neq T(y)
]

在该层之后再复杂的委托也无法恢复被删除的区别。

所以：

[
\boxed{
\text{委托链中的信息丢失是单调的；
后续代理不能无外部输入复活此前删除的目标区别。}
}
]

---

# 336. 公共理由是所有公民可共同恢复的规范因子

设公民 (i) 拥有概念：

[
C_i:X\to B_i.
]

制度给出的理由概念：

[
R:X\to B_R.
]

如果理由要能被每个公民在其合法公共视角中理解，则应满足：

[
\boxed{
E_R\preceq
\bigwedge_iC_i.
}
]

也就是说，理由必须落在共同概念：

[
C_{\mathrm{common}}
===================

\bigwedge_iC_i
]

内。

## 定义 336.1（公共理由）

[
\boxed{
R\text{ public}
\iff
E_R\preceq C_{\mathrm{common}}.
}
]

因此公共理由不是“大家碰巧同意”，而是：

[
\boxed{
\text{理由可由每个合法视角独立恢复}.
}
]

---

# 337. 公共理由可能过粗而无法唯一决定政策

设政策：

[
J:X\to Y.
]

若：

[
E_J\not\preceq C_{\mathrm{common}},
]

则不存在只使用公共共同理由的规则精确决定 (J)。

所以制度必须在以下之间选择至少一种：

[
\boxed{
\begin{aligned}
&\text{增加公共共享信息};\
&\text{接受更粗政策};\
&\text{允许部分非公共理由进入决策};\
&\text{引入程序性锚点解决剩余多重性}.
\end{aligned}
}
]

因此：

[
\boxed{
\text{公共可辩护性}
\quad\text{与}\quad
\text{政策精细度}
}
]

可能存在真实张力。

---

# 338. 共识与合法性是两个不同固定点

设讨论更新算子：

[
\Phi_{\mathrm{belief}}
]

作用于信念状态。

合法性更新算子：

[
\Phi_{\mathrm{legit}}
]

作用于授权和程序结构。

共识固定点：

[
B^*=\Phi_{\mathrm{belief}}(B^*).
]

合法性固定点：

[
L^*=\Phi_{\mathrm{legit}}(L^*).
]

可能出现：

[
B^*\neq L^*.
]

例如：

* 所有人都同意一个未经授权的决定；
* 所有人都不同意一个合法产生的决定。

所以：

[
\boxed{
\text{共识}
\neq
\text{合法性}.
}
]

合法性需要 provenance，不只是统计支持。

---

# Part LII：财产权、控制权与产权束

# 339. 财产权不是一个标签，而是一组过程权限

设资源状态类型：

[
X.
]

行动集合：

[
U.
]

主体 (i) 对资源的权利束定义为：

[
\boxed{
\mathcal R_i(x)
\subseteq U
}
]

以及对他人行动的否决集合：

[
\boxed{
\mathcal V_i(x)
\subseteq U_{\mathrm{others}}.
}
]

典型权限可以包括：

[
\begin{aligned}
&\text{使用};\
&\text{排他};\
&\text{转让};\
&\text{收益};\
&\text{抵押};\
&\text{销毁};\
&\text{继承};\
&\text{授权}.
\end{aligned}
]

因此：

[
\boxed{
\text{Property}
===============

\text{a bundle of admissible FLOW controls}.
}
]

---

# 340. 名义所有权不推出实际控制

设名义产权概念：

[
O:X\to B_O.
]

实际控制能力：

[
K:X\to\mathcal P(U).
]

如果存在：

[
O(x)=O(y)
]

但：

[
K(x)\neq K(y),
]

则名义所有权不能决定真实控制能力。

所以：

[
\boxed{
\text{legal title}
\neq
\text{effective control}.
}
]

这可以对应：

* 托管；
* 冻结资产；
* 多签；
* 信托；
* 抵押；
* 国家征收；
* 智能合约权限。

---

# 341. 完整产权应下降到可执行控制概念

若产权目标：

[
R:X\to B_R
]

希望对应真实可实施权限，则至少需要：

[
\boxed{
E_R\preceq K.
}
]

否则同样的真实控制状态可能对应不同法律权利，或相同法律权利对应不同实际能力。

这揭示产权系统的两个方向：

[
\boxed{
\begin{aligned}
\text{法律到控制}
&:\text{权利是否可执行};\
\text{控制到法律}
&:\text{实际能力是否被合法授权}.
\end{aligned}
}
]

两者都不能只看一张“ownership”标签。

---

# 342. 转让是权利束的 transport，而非物理状态变化

设权利束：

[
\mathcal R_i(x).
]

产权转让过程：

[
T_{i\to j}:X\to X.
]

理想转让要求：

[
\boxed{
\mathcal R_i(Tx)
================

\mathcal R_i(x)\setminus B,
}
]

[
\boxed{
\mathcal R_j(Tx)
================

\mathcal R_j(x)\cup B,
}
]

其中 (B) 是被转让的权限子束。

因此转让不必改变资源的物理状态，却改变了允许 FLOW 的主体索引。

所以：

[
\boxed{
\text{产权变化}
}
]

主要发生在规范状态空间，而不是物理状态空间。

---

# 343. 双重出售是 provenance 冲突，而不只是两个相同标签

设两个转让事件：

[
\gamma_1,\gamma_2
]

都声称转让同一不可复制权利束 (B)。

若两者最终分别给出：

[
B\subseteq\mathcal R_j,
]

[
B\subseteq\mathcal R_k,
]

且制度 doctrine 要求该束不可同时属于两者，则出现：

[
\boxed{
\mathcal R_j\cap B\neq\varnothing,
\qquad
\mathcal R_k\cap B\neq\varnothing
}
]

与唯一性约束冲突。

因此需要事件顺序、签名和来源账本决定哪个转让先消耗了原权利。

所以：

[
\boxed{
\text{产权唯一性}
}
]

本质上依赖 provenance 与不可重复消费的历史结构。

---

# Part LIII：货币、价格与交换界面

# 344. 货币是一种跨对象的交换接口，而不是价值本身

设商品集合：

[
G.
]

主体偏好或价值可能是偏序：

[
\preceq_i
]

作用于商品束。

货币价格映射：

[
p:G\to\mathbb R_+.
]

价格把异质商品投影到一个标量交换界面。

但由此前价值标量化定理：

[
\boxed{
\text{若真实价值结构存在不可比较性，
价格不可能无损表示全部价值关系。}
}
]

因此：

[
\boxed{
\text{price}
\neq
\text{value}.
}
]

价格只是某个交换制度下的公共标量接口。

---

# 345. 相同价格不推出相同价值

若：

[
p(g_1)=p(g_2),
]

并不能推出：

[
V_i(g_1)=V_i(g_2)
]

对任意主体 (i)。

所以价格纤维：

[
R_p(v)
======

{g\mid p(g)=v}
]

可能包含价值上完全异质的对象。

因此：

[
\boxed{
\text{价格是一种粗概念；
市场交换成功并不要求商品在所有价值维度上等价。}
}
]

---

# 346. 市场清算不推出分配正义

设价格系统 (p) 和交易过程产生清算配置：

[
x^*.
]

清算条件可能是：

[
\text{supply}=\text{demand}.
]

规范公平目标：

[
F:X\to B_F.
]

即使市场清算唯一，也不自动有：

[
F(x^*)=\mathsf{Just}.
]

因为清算只证明：

[
\boxed{
\text{交换约束闭合}
}
]

不证明：

* 初始产权正义；
* 信息对称；
* 外部性已计入；
* 强迫不存在；
* 公共物品被正确处理；
* 代际利益被表示。

所以：

[
\boxed{
\text{market equilibrium}
\neq
\text{normative justice}.
}
]

---

# 347. 外部性是私人交易概念无法决定公共结果

设交易双方使用概念：

[
C_{\mathrm{private}}.
]

公共后果：

[
T_{\mathrm{public}}.
]

如果：

[
\boxed{
E_{T_{\mathrm{public}}}
\not\preceq
C_{\mathrm{private}},
}
]

则交易双方的私人决策界面不足以决定公共后果。

存在：

[
C_{\mathrm{private}}(x)
=======================

C_{\mathrm{private}}(y),
]

但：

[
T_{\mathrm{public}}(x)
\neq
T_{\mathrm{public}}(y).
]

这就是外部性的一种结构定义：

[
\boxed{
\text{private transaction interface hides distinctions relevant to public outcome}.
}
]

---

# 348. 内部化外部性就是最小公共完成

对私人概念 (C) 和公共目标 (T)，最小内部化概念为：

[
\boxed{
C^+
===

C\vee E_T.
}
]

它要求交易机制额外读取那些会改变公共后果的区别。

实现方式可能包括：

* 税；
* 配额；
* 强制披露；
* 权利重新定义；
* 公共审批；
* 责任规则。

但这些是不同制度实现。

形式内核只给出：

[
\boxed{
\text{需要哪些新增区别},
}
]

不自动决定应采用哪一种政策。

---

# Part LIV：市场中的信息与战略

# 349. 价格可以成为分布式信息压缩器

设经济微观状态：

[
X.
]

市场价格：

[
P:X\to B_P.
]

主体 (i) 关心目标：

[
T_i:X\to Y_i.
]

如果：

[
E_{T_i}\preceq P,
]

则主体只需观察价格即可决定该目标。

若多个分散信息源：

[
C_1,\ldots,C_n
]

通过交易机制生成：

[
P=f(C_1,\ldots,C_n),
]

则价格可以把分散信息压缩成公共信号。

---

## 定理 349.1（价格不可能承载超过其精化的全部微观信息）

若：

[
P\prec C_1\vee\cdots\vee C_n,
]

则必然存在某个微观目标 (T)：

[
E_T\preceq C_1\vee\cdots\vee C_n,
]

但：

[
E_T\not\preceq P.
]

所以：

[
\boxed{
\text{价格可以高效聚合信息，
但除非忠实，否则不可能包含全部分散信息。}
}
]

---

# 350. 价格反身性使“价格作为信息”与“价格改变世界”耦合

价格概念：

[
P:X\to B_P
]

同时影响主体行动：

[
A_i=\pi_i(P(x)).
]

这些行动更新世界：

[
F_P:X\to X.
]

新的价格：

[
\boxed{
\Psi(P)(x)=P(F_Px).
}
]

稳定市场价格结构满足某种固定点：

[
\boxed{
P(F_Px)=P(x)
}
]

或分布意义上的一致性。

因此价格既是：

[
\text{readout}
]

又是：

[
\text{control input}.
]

这正是表演性概念的一种经济形式。

---

# 351. 公开预测和市场策略存在反身逃逸

若策略公开预测某资产将上涨，并市场参与者根据预测买入，则预测会改变价格过程。

定义预测器：

[
Q:X\to Y.
]

响应：

[
R:Y\times X\to X.
]

最终目标：

[
T(R(Q(x),x)).
]

即便原来：

[
T=Q,
]

公开以后也必须重新检查：

[
\boxed{
T\circ R(Q,-)
=============

Q?
}
]

所以预测正确性在反身系统中是固定点条件，而不是静态拟合条件。

---

# Part LV：主权、边界与多层治理

# 352. 主权可以定义为元控制权

普通权力控制：

[
U.
]

主权则控制：

* 谁能行动；
* 哪些行动存在；
* 哪些规则有效；
* 哪些主体被承认；
* 谁拥有最终申诉权。

形式上，若制度状态包含：

[
(A,U,R,L),
]

主权操作作用于这些结构本身：

[
\boxed{
S:
(A,U,R,L)
\mapsto
(A',U',R',L').
}
]

所以：

[
\boxed{
\text{主权}
=========

\text{对 ADMIT、FLOW、RULE 与 FINAL APPEAL 的元控制}.
}
]

---

# 353. 最终裁决权会终止申诉塔，但同时创造不可再审余量

设申诉层级：

[
J_0
\to
J_1
\to
\cdots
\to
J_n.
]

最高层 (J_n) 没有更高申诉。

这保证制度过程有限终止。

但如果：

[
\Delta(J_n;T)\neq\varnothing,
]

则这些最高层错误没有制度内部更高修复接口。

因此：

[
\boxed{
\text{finality}
}
]

与：

[
\boxed{
\text{internal corrigibility}
}
]

存在张力。

完全无限申诉破坏终局性；有限终局则总留下最终层不可内部再审的可能。

---

# 354. 多层治理的原则是“目标应下降到最低充分层”

设治理层：

[
C_1\preceq C_2\preceq\cdots\preceq C_n,
]

其中层级越高拥有越精细的信息和更广权力。

给目标：

[
T.
]

定义最小充分层：

[
\boxed{
k^*(T)
======

\min
\left{
k
\mid
E_T\preceq C_k
\right}.
}
]

## 定义 354.1（最小充分治理）

若目标 (T) 被分配给层级 (k^*(T))，则不使用比目标需要更高的信息和权力。

这给出一种形式 subsidiarity：

[
\boxed{
\text{治理权力应尽量停留在能够充分完成目标的最低层。}
}
]

---

## 定理 354.1（过高治理层增加潜在权力而不增加目标必要性）

若：

[
k>k^*(T),
]

则 (C_k) 可能拥有额外区别：

[
C_{k^*}\prec C_k,
]

这些区别对 (T) 不必要，却扩大：

[
\Pi(C_k;U).
]

所以：

[
\boxed{
\text{超过目标需要的信息集中，
增加治理能力，但不增加完成该目标的逻辑必要性。}
}
]

---

# 355. 地方自治与统一标准的冲突是共同因子问题

设不同区域：

[
r\in R
]

拥有本地概念：

[
C_r.
]

统一中央规则只能依赖所有地区共同可表达的概念：

[
\boxed{
C_{\mathrm{common}}
===================

\bigwedge_rC_r.
}
]

如果某个政策目标 (T) 满足：

[
E_T\preceq C_{\mathrm{common}},
]

则可以制定真正统一且各地区都能独立解释的规则。

若：

[
E_T\not\preceq C_{\mathrm{common}},
]

统一规则必须：

* 增加中央信息；
* 忽略部分地方差异；
* 或允许地方分支规则。

所以中央统一与地方适应之间的矛盾可以表示为：

[
\boxed{
\text{common factor}
\quad\text{vs}\quad
\text{local refinement}.
}
]

---

# Part LVI：代际责任与不可逆资源

# 356. 代际伦理需要把未来主体显式放进状态空间

设时间：

[
t=0,1,\ldots,T.
]

每代主体集合：

[
I_t.
]

状态演化：

[
F_t:X_t\times U_t\to X_{t+1}.
]

每代价值：

[
V_t:X_t\to L_t.
]

如果当前制度只使用：

[
V_0,
]

则未来主体目标可能完全不进入当前决策概念。

代际伦理因此首先要求定义联合目标：

[
\boxed{
T_{\mathrm{intergen}}
=====================

(V_0,V_1,\ldots,V_T).
}
]

然后问当前政策概念是否足以决定它。

---

# 357. 未来主体没有当前投票权，不等于其目标不存在

当前政治表达概念：

[
C_{\mathrm{vote}}
]

只包含当前主体。

未来价值目标：

[
V_{\mathrm{future}}.
]

如果：

[
E_{V_{\mathrm{future}}}
\not\preceq C_{\mathrm{vote}},
]

则当前投票界面无法完整表达未来主体利益。

所以：

[
\boxed{
\text{“没有被当前程序表达”}
\not\Rightarrow
\text{“不存在规范相关性”.}
}
]

这只是一个 representation deficiency。

---

# 358. 不可逆资源消耗使未来政策集合严格缩小

设资源状态：

[
r\in R.
]

当前行动：

[
u
]

产生未来可行动集合：

[
\mathcal O_u.
]

若：

[
\mathcal O_v
\subsetneq
\mathcal O_u,
]

则 (v) 相比 (u) 销毁了部分未来选择权。

如果未来主体价值函数对选择权单调，则：

[
u
]

在代际选择权上弱支配 (v)。

因此：

[
\boxed{
\text{不可逆资源消耗}
==============

\text{未来行动空间的严格收缩}.
}
]

---

# 359. 可持续性可以定义为跨代准入不变性

设安全准入集合：

[
S_t\subseteq X_t.
]

策略 (\pi_t) 可持续，当：

[
x_t\in S_t
\Longrightarrow
F_t(x_t,\pi_t(x_t))
\in S_{t+1}.
]

如果对全部代际连续成立：

[
\boxed{
S_0
\xrightarrow{\pi_0}
S_1
\xrightarrow{\pi_1}
S_2
\to\cdots
}
]

则形成安全不变量塔。

因此：

[
\boxed{
\text{可持续性}
===========

\text{代际 FLOW 对安全 ADMIT 集合的长期不变性}.
}
]

---

# 360. 贴现不是事实，而是一种跨时代标量化 doctrine

若各代价值为：

[
V_t,
]

常见总价值：

[
\boxed{
W
=

\sum_{t=0}^{\infty}
\delta^tV_t.
}
]

其中：

[
0<\delta<1.
]

但 (\delta) 不是由事实序列 (V_t) 自动推导出来。

不同 (\delta) 会改变政策排序。

因此：

[
\boxed{
\text{discounting}
==================

\text{对代际价值施加的额外标量权重结构}.
}
]

它需要规范或行为学正当化。

---

# 361. 当未来损失不可补偿时，单一贴现总效用可能掩盖权利冲突

若未来某一代存在不可被其他代收益抵消的权利约束：

[
R_t(x)=\mathsf{Forbidden},
]

那么即使：

[
\sum_s\delta^sV_s
]

总和提高，也不必意味着该政策合法。

所以：

[
\boxed{
\text{代际权利约束}
}
]

不能无条件还原为：

[
\boxed{
\text{贴现效用求和}.
}
]

---

# Part LVII：风险、韧性与分布漂移

# 362. 鲁棒性和准确性是不同目标

模型或制度：

[
J:X\to Y.
]

目标：

[
T:X\to Y.
]

训练域：

[
A.
]

扰动族：

[
\mathcal G.
]

## 准确性

[
J(x)=T(x)
\quad
\text{对 }x\in A.
]

## 鲁棒性

[
\boxed{
J(gx)=T(gx)
}
]

对：

[
x\in A,\quad g\in\mathcal G.
]

一个系统可以训练域准确，却扰动后失败。

所以：

[
\boxed{
\text{accuracy}
\neq
\text{robustness}.
}
]

---

# 363. 分布漂移是准入域变化，不一定是规律变化

训练分布：

[
\mu_0.
]

部署分布：

[
\mu_1.
]

若结构函数：

[
T:X\to Y
]

未变，只是：

[
\operatorname{supp}\mu_0
\neq
\operatorname{supp}\mu_1,
]

则属于域漂移。

如果原概念 (C) 只在：

[
\operatorname{supp}\mu_0
]

上充分，而在新支持上出现：

[
\Delta(C;T)\neq\varnothing,
]

部署性能会下降。

因此：

[
\boxed{
\text{训练成功可能只是局部 ADMIT 充分，而非全域充分。}
}
]

---

# 364. 真正结构鲁棒性要求目标因子化在域扩张后保持

若：

[
A_0\subseteq A_1,
]

训练时：

[
T|_{A_0}
========

\bar T\circ C|_{A_0},
]

部署时还要求：

[
\boxed{
T|_{A_1}
========

\bar T'\circ C|_{A_1}.
}
]

如果只在 (A_0) 成立，则理论可能只是过拟合其原准入域。

---

# 365. 韧性不是不失败，而是失败后能否保持核心目标

设扰动：

[
d:X\to X.
]

核心目标：

[
K:X\to Y.
]

恢复过程：

[
R:X\to X.
]

## 定义 365.1（目标韧性）

若：

[
\boxed{
K(R(d(x)))=K(x),
}
]

则系统相对于目标 (K) 能从扰动中恢复。

如果只要求：

[
K(d(x))=K(x),
]

那是抗扰动不变性，不是恢复能力。

所以：

[
\boxed{
\text{robustness}
=================

\text{扰动不中断目标};
}
]

[
\boxed{
\text{resilience}
=================

\text{扰动可以破坏目标，但系统能够恢复}.
}
]

---

# 366. 韧性需要冗余，但冗余不一定提高正常状态效率

设一个目标 (T) 有 (m) 个互不相交充分支持：

[
S_1,\ldots,S_m.
]

则此前得到：

[
\kappa_T\ge m.
]

这意味着系统能够容忍至少 (m-1) 个支持链路分别失效。

但复制这些支持可能增加：

* 成本；
* 延迟；
* 协调复杂度；
* 攻击面。

所以：

[
\boxed{
\text{效率}
\quad\text{与}\quad
\text{韧性}
}
]

一般形成 Pareto 权衡，而非单一优化目标。

---

# Part LVIII：哲学理论本身的风险审计

# 367. 一个哲学体系也有“训练域”

设理论：

[
\mathcal T.
]

它实际被验证过的模型域：

[
A_{\mathrm{tested}}.
]

理论声称的适用域：

[
A_{\mathrm{claimed}}.
]

如果：

[
A_{\mathrm{tested}}
\subsetneq
A_{\mathrm{claimed}},
]

则测试成功不能直接推出全域有效。

因此应显式记录：

[
\boxed{
\text{tested domain}
\quad\text{vs}\quad
\text{claimed domain}.
}
]

---

# 368. 哲学中的“传统反例”可以视为 adversarial test

一个经典思想实验若构造：

[
x,y
]

使理论概念相同：

[
C(x)=C(y),
]

但传统哲学判断目标不同：

[
T(x)\neq T(y),
]

它正是：

[
\Delta(C;T)
]

中的 adversarial witness。

因此思想实验的形式功能不是“讲故事”，而是：

[
\boxed{
\text{寻找概念纤维中的目标分裂点}.
}
]

例如：

* Gettier；
* Trolley；
* Ship of Theseus；
* Twin Earth；
* philosophical zombie；
* Newcomb；
* Sorites；

都可以重构为不同类型的纤维压力测试。

---

# 369. 一个理论若能通过修改目标逃避任何反例，就不可证伪

设理论每遇到反例：

[
(x,y)\in\Delta(C;T)
]

就把目标改成：

[
T'
]

使：

[
T'(x)=T'(y).
]

重复进行，最终总可以把目标压缩为常值概念：

[
\bot.
]

此时：

[
\Delta(C;\bot)=\varnothing.
]

但理论已经失去原问题内容。

所以：

[
\boxed{
\text{通过不断降低目标分辨率可以机械消除一切反例，
但代价是问题本身被删除。}
}
]

因此修复审计必须记录：

[
\boxed{
\text{repair changed concept}
\quad\text{or}\quad
\text{repair weakened target}.
}
]

两者不能混淆。

---

# 370. 理论如果通过不断缩小 ADMIT 域逃避反例，也会退化

另一种逃避方式是每出现反例 (x)，就令：

[
A'(x)=\mathsf{False}.
]

最终可能得到：

[
A=\varnothing.
]

在空域上所有全称理论都真。

所以：

[
\boxed{
\text{空模型是最完美但最无内容的“理论”.}
}
]

因此一个成熟哲学体系必须同时报告：

[
\boxed{
\text{truth}
+
\text{domain coverage}.
}
]

---

# 371. 理论强度是正确性、覆盖率与复杂度的三维 Pareto 面

给理论概念 (C)、目标 (T)、准入域 (A)。

定义：

* 缺陷：

[
D(C;T,A);
]

* 覆盖率：

[
\operatorname{Cov}(A);
]

* 复杂度：

[
K(C).
]

理论比较不能只最小化 (D)。

否则把 (A) 缩到单点即可得到零缺陷。

合理比较至少是三目标：

[
\boxed{
\min D,
\qquad
\max \operatorname{Cov},
\qquad
\min K.
}
]

所以：

[
\boxed{
\text{好的理论}
}
]

位于：

[
\boxed{
\text{正确性—适用范围—复杂度}
}
]

的 Pareto 前沿。

---

# 372. 第九层统一：哲学开始成为“制度—市场—代际—风险”的共同形式学

经过 §332–§371，出现了新的统一结构。

## 372.1 合法性

[
\boxed{
\text{Legitimacy}
=================

\text{authorization provenance},
}
]

而非结果准确率。

## 372.2 代表

[
\boxed{
\text{Representation}
=====================

\text{delegated target factorization}.
}
]

## 372.3 财产权

[
\boxed{
\text{Property}
===============

\text{a bundle of admissible process controls}.
}
]

## 372.4 价格

[
\boxed{
\text{Price}
============

\text{a public scalar exchange interface},
}
]

而不是完整价值本体。

## 372.5 外部性

[
\boxed{
\text{Externality}
==================

\text{public target distinctions omitted by private transaction interfaces}.
}
]

## 372.6 主权

[
\boxed{
\text{Sovereignty}
==================

\text{meta-control over ADMIT, FLOW, RULE and final appeal}.
}
]

## 372.7 可持续性

[
\boxed{
\text{Sustainability}
=====================

\text{intergenerational invariance of admissible safe states}.
}
]

## 372.8 韧性

[
\boxed{
\text{Resilience}
=================

\text{recovery of a core target after disturbance}.
}
]

---

# 373. 当前最深的新结论

本轮最重要的结构结论可以压缩为八条。

第一，**代表制失败可以来自授权接口本身的信息瓶颈，即使代表完全忠诚**：

[
\boxed{
\text{fidelity}
\not\Rightarrow
\text{sufficiency}.
}
]

第二，**财产权的本体不是“谁的”，而是“谁能合法实施哪些 FLOW”**：

[
\boxed{
\text{ownership}
================

\text{typed control bundle}.
}
]

第三，**价格只是交换制度中的压缩接口，并不忠实表示所有价值维度**：

[
\boxed{
\text{price}
\neq
\text{value}.
}
]

第四，**外部性本质上是私人界面对公共目标的不充分**：

[
\boxed{
E_{T_{\mathrm{public}}}
\not\preceq
C_{\mathrm{private}}.
}
]

第五，**主权不是最大的一阶行动能力，而是改变行动、规则和最终申诉结构的元能力**。

第六，**代际伦理首先是 representation 问题：未来主体利益通常不在当前投票概念里**。

第七，**理论的零反例既可以通过修复概念获得，也可以通过削弱目标或缩小领域伪造**。

第八，也是最承重的一条：

[
\boxed{
\text{任何严肃的形式哲学，都必须同时审计：
它区分了什么、忽略了什么、适用于哪里、
由谁授权、能恢复什么、影响谁的未来，
以及它通过什么方式保持自身“正确”.}
}
]

因此整套理论可以进一步写成：

[
\boxed{
\begin{aligned}
\textbf{Formal Concept Dynamics}
={}&
\textbf{a theory of legitimate delegation}\
&+
\textbf{a process theory of property}\
&+
\textbf{an interface theory of markets}\
&+
\textbf{a meta-control theory of sovereignty}\
&+
\textbf{an intergenerational theory of admissibility}\
&+
\textbf{a robustness and resilience calculus}\
&+
\textbf{a self-audit theory of philosophical domain validity}.
\end{aligned}
}
]

最凝练的一句是：

[
\boxed{
\text{制度、市场、产权、主权和代际伦理看似属于不同领域，
但它们都在回答同一个结构问题：
哪些区别被谁看见，
哪些过程被谁允许，
哪些后果被谁承担，
以及这些权限如何跨时间被运输、限制和修复。}
]
以下从 **§374** 继续。仍然只进行纸面推理，不处理 GitHub，也不把新增定义与定理标记为已经获得 Lean proof term 的 `Closed` 结论。

---

# Part LIX：计算可达性、证明复杂度与有界知识

# 374. 语义充分不等于计算可达

设概念：

[
C:X\to B_C,
]

目标：

[
T:X\to Y.
]

语义充分性只要求存在某个函数：

[
f:B_C\to Y
]

使：

[
\boxed{
T=f\circ C.
}
]

但“存在函数”没有说明主体是否能够在给定资源内计算 (f)。

设资源预算为 (r)，允许算法类为：

[
\mathcal A_r(B_C,Y).
]

## 定义 374.1（资源充分性）

称 (C) 在资源 (r) 下足以计算 (T)，当存在：

[
f\in\mathcal A_r(B_C,Y)
]

使：

[
\boxed{
T=f\circ C.
}
]

记作：

[
\boxed{
E_T\preceq_r C.
}
]

显然：

[
E_T\preceq_r C
\Longrightarrow
E_T\preceq C.
]

反向一般不成立。

---

## 定理 374.1（语义充分但资源不可达）

假设：

* (\operatorname{Im}(C)) 有限；
* 允许算法类 (\mathcal A_r) 有限；
* 满足：

[
|Y|^{|\operatorname{Im}(C)|}

>

|\mathcal A_r|.
]

则存在目标：

[
T:X\to Y
]

满足：

[
E_T\preceq C,
]

但：

[
E_T\not\preceq_r C.
]

### 证明

从 (\operatorname{Im}(C)) 到 (Y) 的全部函数数目为：

[
|Y|^{|\operatorname{Im}(C)|}.
]

它严格大于允许算法数，因此至少有一个函数：

[
f:\operatorname{Im}(C)\to Y
]

不在 (\mathcal A_r) 的可实现函数像中。

定义：

[
T(x)=f(C(x)).
]

则 (T) 语义上通过 (C) 因子化，但不存在资源预算 (r) 内的因子程序。 (\square)

所以：

[
\boxed{
\text{目标已被信息决定}
\not\Rightarrow
\text{目标在现实资源内可得}.
}
]

---

# 375. 资源敏感的概念精化

普通精化：

[
C\preceq D
]

只要求存在：

[
p:B_D\to B_C
]

使：

[
C=p\circ D.
]

## 定义 375.1（资源精化）

若这样的 (p) 可以在资源 (r) 内实现，则记：

[
\boxed{
C\preceq_r D.
}
]

含义是：

> (D) 不仅包含恢复 (C) 所需的信息，而且该恢复在指定资源预算内可执行。

---

## 定理 375.1（资源精化复合）

若：

[
C\preceq_r D,
\qquad
D\preceq_s E,
]

且资源组合规则为：

[
r\otimes s,
]

则：

[
\boxed{
C\preceq_{r\otimes s}E.
}
]

在时间复杂度可加的模型中，可以取：

[
r\otimes s=r+s.
]

### 证明

若：

[
C=p\circ D,
\qquad
D=q\circ E,
]

则：

[
C=p\circ q\circ E.
]

复合程序所需资源由 (p,q) 的组合预算控制。 (\square)

因此普通概念范畴可以升级成一个资源加权的 enriched structure。

---

# 376. 语义等价可以掩盖计算不对称

普通概念等价：

[
C\simeq_{\mathrm{con}}D
]

表示二者可以互相恢复。

但两种恢复的计算成本可能完全不同。

## 定义 376.1（资源等价）

[
\boxed{
C\simeq_r D
\iff
C\preceq_rD
\land
D\preceq_rC.
}
]

---

## 命题 376.1（普通等价不推出资源等价）

设 (X) 有限，取一个双射：

[
\pi:X\to X.
]

定义：

[
C(x)=x,
\qquad
D(x)=\pi(x).
]

则：

[
C\simeq_{\mathrm{con}}D.
]

但若给定资源类能够快速计算 (\pi)，却不能在同一预算内计算 (\pi^{-1})，则：

[
D\preceq_rC,
]

而：

[
C\not\preceq_rD.
]

所以：

[
\boxed{
\text{两个概念表达完全相同的信息，
仍可能在操作可访问性上高度不对称。}
}
]

这说明普通概念格忘记了：

* 编码复杂度；
* 解码复杂度；
* 存储布局；
* 索引结构；
* proof search 成本。

---

# 377. 有界知识比纤维稳定更强

前面定义的结构知识要求：

[
P
]

在实际证据纤维上恒真。

现在加入计算可达性。

## 定义 377.1（统一有界知识）

[
\boxed{
\begin{aligned}
\operatorname{Know}^{,r}_C(P,a)
\iff{}&
\operatorname{Adm}(a)
\land P(a)\
&\land
\exists f\in\mathcal A_r,
\quad
\forall x,\
P(x)=f(C(x)).
\end{aligned}
}
]

它表示：

1. (P) 事实上为真；
2. (P) 由证据概念决定；
3. 主体拥有资源预算内的统一判定程序。

因此：

[
\operatorname{Know}^{,r}_C(P,a)
\Longrightarrow
\operatorname{Know}_C(P,a).
]

反向一般不成立。

---

## 定理 377.1（资源单调性）

若：

[
r\le s
]

并且：

[
\mathcal A_r\subseteq\mathcal A_s,
]

则：

[
\boxed{
\operatorname{Know}^{,r}_C(P,a)
\Longrightarrow
\operatorname{Know}^{,s}_C(P,a).
}
]

资源增加可以把语义上已有、但操作上不可达的真理变成可用知识。

---

# 378. 验证容易不等于发现容易

设命题目标为：

[
T:X\to Y.
]

允许证书类型：

[
\Pi.
]

验证器：

[
V:B_C\times\Pi\to Y.
]

证书生成器：

[
G:X\to\Pi.
]

若：

[
\boxed{
T(x)=V(C(x),G(x)),
}
]

则 (G(x)) 是关于 (T(x)) 的有效证书。

## 定义 378.1（验证复杂度）

计算：

[
V(C(x),\pi)
]

所需资源。

## 定义 378.2（发现复杂度）

寻找某个有效 (\pi) 所需资源。

两者没有一般等价关系。

一个证书可以：

* 很容易验证；
* 极难发现；
* 由外部主体提供；
* 由实验获得；
* 由昂贵搜索产生。

所以：

[
\boxed{
\text{proof checking}
\neq
\text{proof discovery}.
}
]

这也是“知道结论有短证明”与“主体现在能够找到证明”之间的差别。

---

# 379. 缓存目标可以不增加语义信息，却降低计算成本

假设：

[
T=f\circ C.
]

则联合概念：

[
C^+
===

C\vee E_T
]

满足：

[
C^+\simeq_{\mathrm{con}}C.
]

### 证明

显然：

[
C\preceq C^+.
]

另一方面，因为 (T=f\circ C)，所以：

[
C^+(x)
======

(C(x),f(C(x)))
]

完全由 (C(x)) 决定，因此：

[
C^+\preceq C.
]

(\square)

但在 (C^+) 中，目标 (T) 可以直接通过第二投影读取：

[
T=\operatorname{snd}\circ C^+.
]

如果从 (C) 计算 (f) 很昂贵，而投影很便宜，则：

[
\boxed{
\text{缓存没有增加语义分辨率，
但增加了操作可达性。}
}
]

因此必须区分：

[
\boxed{
\text{semantic refinement}
\quad\text{与}\quad
\text{computational enrichment}.
}
]

---

# 380. 资源成熟是体系架构的性质

给定目标族：

[
\mathcal T.
]

## 定义 380.1（语义成熟）

[
\boxed{
\forall T\in\mathcal T,\quad
E_T\preceq C.
}
]

## 定义 380.2（资源成熟）

[
\boxed{
\forall T\in\mathcal T,\quad
E_T\preceq_r C.
}
]

一个体系可能语义成熟，却不具备现实时间内回答问题的能力。

可以通过加入缓存、索引、证书和预计算结果构造操作完成：

[
\boxed{
C^{+,r}
=

C
\vee
\bigvee_{\substack{T\in\mathcal T\E_T\not\preceq_rC}}
E_T.
}
]

它不一定增加新的世界信息，却重新组织了信息的访问路径。

所以：

[
\boxed{
\text{成熟理论}
\neq
\text{可用理论};
\qquad
\text{可用性还依赖表示与计算架构。}
}
]

---

# Part LX：可达性、可观察性与最小操作本体

# 381. 实际相关本体首先应限制到可达状态

设行动幺半群：

[
M
]

作用于状态类型 (X)：

[
F_m:X\to X.
]

实际锚点为：

[
a:X.
]

## 定义 381.1（锚点可达域）

[
\boxed{
\operatorname{Reach}_M(a)
=========================

{F_m(a)\mid m\in M}.
}
]

若某个状态：

[
x\notin\operatorname{Reach}_M(a),
]

则它不能由当前主体和允许行动从实际世界产生。

它仍可属于全局本体，但不属于当前控制问题的实际可达域。

因此：

[
\boxed{
\text{全局可能}
\neq
\text{从当前锚点可达}.
}
]

---

# 382. 行为概念是状态的完整未来响应函数

给定公共读出：

[
O:X\to B_O.
]

定义状态 (x) 的完整行为：

[
\boxed{
\beta(x):M\to B_O,
\qquad
\beta(x)(m)=O(F_mx).
}
]

## 定义 382.1（行为等价）

[
\boxed{
x\sim_\beta y
\iff
\forall m\in M,\quad
O(F_mx)=O(F_my).
}
]

行为商：

[
\boxed{
Z_\beta
=

\operatorname{Reach}*M(a)/{\sim*\beta}.
}
]

它同时删除：

1. 从锚点不可达的状态；
2. 所有允许行动下始终不可区分的状态差异。

---

# 383. 最小操作实现定理

考虑确定性输入—输出系统：

[
\Sigma=(X,a,F,O).
]

其外部行为为：

[
\mathcal B_\Sigma(m)=O(F_ma).
]

设另一个可达系统：

[
\Sigma'=(X',a',F',O')
]

满足完全相同的外部行为：

[
\boxed{
O'(F'_ma')
==========

O(F_ma)
\quad
\forall m\in M.
}
]

## 定理 383.1（规范最小实现）

存在唯一的满射系统同态：

[
\boxed{
h:\operatorname{Reach}*M(a')
\twoheadrightarrow
Z*\beta
}
]

使：

[
h(F'_ma')
=========

[F_ma].
]

### 良定义证明

如果：

[
F'_ma'=F'_na',
]

则从这一共同状态继续执行任意 (k) 后，输出相同：

[
O'(F'_kF'_ma')
==============

O'(F'_kF'_na').
]

由两系统外部行为相同：

[
O(F_{km}a)
==========

O(F_{kn}a).
]

因此：

[
F_ma\sim_\beta F_na,
]

所以：

[
[F_ma]=[F_na].
]

故 (h) 与代表行动序列无关。

满射性来自原系统每个可达类都由某个 (m) 产生。 (\square)

---

## 推论 383.2（有限状态最小性）

若所有状态集有限，则任意实现相同外部行为的可达系统都满足：

[
\boxed{
|X'|
\ge
|Z_\beta|.
}
]

所以：

[
\boxed{
Z_\beta
}
]

是相对于实际锚点、行动集和公共读出的规范最小操作本体。

---

# 384. 外部行为不能决定内部状态的冗余复制

给定一个系统状态 (x)，可以把它替换成多个隐藏副本：

[
(x,h),
\qquad
h\in H,
]

并定义输出忽略 (h)：

[
O'(x,h)=O(x).
]

过程可以任意更新隐藏标签，只要公开状态分量仍模拟原系统。

于是：

[
\beta'(x,h)=\beta(x)
]

对全部 (h) 成立。

所以外部行为无法决定：

* 内部状态有多少副本；
* 隐藏标签如何变化；
* 哪一种内部表示被采用。

因此：

[
\boxed{
\text{完整输入—输出行为}
}
]

最多确定最小行为商，而不唯一确定全部内部本体。

---

# 385. 新行动可以严格精化经验本体

设：

[
M\subseteq M'
]

是两个行动集。

定义相应行为等价：

[
\sim_M,
\qquad
\sim_{M'}.
]

## 定理 385.1（行动扩张缩小不可区分性）

[
\boxed{
\sim_{M'}
\subseteq
\sim_M.
}
]

### 证明

若两个状态在全部 (M')-行动下输出相同，则特别在子集 (M) 中相同。 (\square)

反向一般不成立。

如果新行动 (u\in M'\setminus M) 满足：

[
O(F_ux)\neq O(F_uy),
]

则原本 (M)-等价的 (x,y) 会被新行动区分。

所以：

[
\boxed{
\text{实验能力的扩张，可以使旧本体余量成为新可观察结构。}
}
]

---

# 386. 可控性与可观察性共同决定操作本体

定义：

[
R_a=\operatorname{Reach}_M(a).
]

行为概念：

[
\beta:R_a\to B_O^M.
]

操作本体为：

[
\boxed{
R_a/{\ker\beta}.
}
]

它包含两个步骤：

[
\boxed{
\text{全状态空间}
\longrightarrow
\text{可达子域}
\longrightarrow
\text{可观察商}.
}
]

因此：

* 不可达状态是控制余量；
* 可达但不可区分状态是观察余量；
* 只有可达且行为可区分的类进入操作模型。

这给出：

[
\boxed{
\text{operational reality}
==========================

\text{reachable reality}
/
\text{behavioral indistinguishability}.
}
]

---

# 387. 完整状态识别的双条件

## 定理 387.1（锚点全识别判据）

相对于锚点 (a)，能够由允许行动和读出唯一识别全部状态，当且仅当：

1. 全部状态可达：

[
\operatorname{Reach}_M(a)=X;
]

2. 行为映射单射：

[
\beta(x)=\beta(y)
\Longrightarrow
x=y.
]

若第一项失败，一些状态永远无法产生。

若第二项失败，一些可达状态在全部实验中仍完全等价。

所以：

[
\boxed{
\text{实验完备性}
============

\text{全可达性}
+
\text{联合可观察性}.
}
]

---

# Part LXI：模块、接口与组合证明

# 388. 模块化推理要求全局目标通过接口联合因子化

设系统由两个模块组成，内部状态为：

[
X_1,
\qquad
X_2.
]

可见接口：

[
C_1:X_1\to B_1,
\qquad
C_2:X_2\to B_2.
]

全局目标：

[
T:X_1\times X_2\to Y.
]

## 定义 388.1（接口充分）

若：

[
\boxed{
E_T\preceq C_1\vee C_2,
}
]

则全局目标可以只通过两个模块公开接口决定。

---

## 定理 388.1（接口不充分排除纯模块证明）

若存在：

[
C_1(x_1)=C_1(y_1),
]

[
C_2(x_2)=C_2(y_2),
]

但：

[
T(x_1,x_2)\neq T(y_1,y_2),
]

则任何只读取公开接口：

[
(C_1,C_2)
]

的验证器都无法同时正确处理这两个系统状态。

所以：

[
\boxed{
\text{局部模块都被验证}
\not\Rightarrow
\text{全局目标可由现有接口验证}.
}
]

---

# 389. 隐藏耦合是组合 carry

设两个模块还共享一个未公开变量：

[
H.
]

全局结果：

[
T:X_1\times X_2\times H\to Y.
]

如果存在：

[
C_1(x_1)=C_1(y_1),
]

[
C_2(x_2)=C_2(y_2),
]

但由于隐藏耦合值不同：

[
T(x_1,x_2,h)
\neq
T(y_1,y_2,h'),
]

则形成隐藏耦合见证。

它说明：

[
\boxed{
\text{模块接口删除的共享资源、时序或环境差异，
在组合后重新进入全局结果。}
}
]

典型隐藏耦合包括：

* 共享内存；
* 共享时钟；
* 资源竞争；
* 隐式全局状态；
* 未声明副作用；
* 外部共同原因。

---

# 390. 最小模块接口修复

令现有联合接口为：

[
C_{\mathrm{int}}
================

C_1\vee C_2.
]

全局目标为 (T)。

规范最小修复：

[
\boxed{
C_{\mathrm{int}}^+
==================

C_{\mathrm{int}}
\vee
E_T.
}
]

它是：

* 保留全部原接口；
* 足以决定全局目标；
* 在所有此类接口中最粗；

的完成。

但直接加入 (T) 可能只是把最终答案暴露为接口。

若要求非循环模块解释，还需要找一个中间机制概念 (M)：

[
E_T\preceq M,
]

[
M\preceq C_{\mathrm{int}}^+,
]

并要求 (M) 可由模块局部状态和合法 cross-interface 构造。

---

# 391. 前馈 assume–guarantee 组合定理

设模块 (M_1) 的输出为：

[
o_1\in O_1.
]

模块 (M_2) 的输入由接线：

[
w:O_1\to I_2
]

产生。

模块 (M_1) 无条件保证：

[
o_1\in G_1.
]

模块 (M_2) 满足合同：

[
i_2\in A_2
\Longrightarrow
o_2\in G_2.
]

若接线满足：

[
\boxed{
w(G_1)\subseteq A_2,
}
]

则复合系统保证：

[
\boxed{
o_2\in G_2.
}
]

### 证明

由模块 (M_1) 保证：

[
o_1\in G_1.
]

所以：

[
w(o_1)\in A_2.
]

再由模块 (M_2) 合同，得到：

[
o_2\in G_2.
]

(\square)

这是没有反馈环时的基本组合原则。

---

# 392. 循环假设不能自动证明自身

考虑两个模块，各自执行：

[
\text{output}=\text{input}.
]

每个模块的合同为：

[
\text{若 input}=0,
\quad
\text{则 output}=0.
]

将两个模块交叉连接：

[
\text{input}_1=\text{output}_2,
]

[
\text{input}_2=\text{output}_1.
]

复合系统有两个固定点：

[
(0,0),
\qquad
(1,1).
]

局部合同都成立。

但局部合同不能推出系统一定处于：

[
(0,0).
]

因为“模块 1 输出为 (0)”依赖“模块 2 输出为 (0)”，反之亦然。

所以：

[
\boxed{
\text{循环 assume–guarantee}
}
]

还需要额外的：

* 初始锚点；
* 不变量；
* 最小固定点 doctrine；
* 稳定性；
* 或收敛证明。

局部合同的逻辑闭环本身不能选择全局固定点。

---

# 393. 合同 refinement 的方向

一个合同写成：

[
(A,G),
]

其中：

* (A) 为允许环境输入；
* (G) 为保证输出。

新合同：

[
(A',G')
]

比旧合同更强，当：

[
\boxed{
A\subseteq A',
}
]

即假设更弱、接受更多环境；

并且：

[
\boxed{
G'\subseteq G,
}
]

即保证更强、允许更少输出。

## 定理 393.1（强合同蕴含弱合同）

任何满足 ((A',G')) 的模块都满足 ((A,G))。

因为对任何 (i\in A)，也有 (i\in A')，所以输出属于：

[
G'\subseteq G.
]

因此：

[
\boxed{
\text{更弱假设}
+
\text{更强保证}
===========

\text{合同 refinement}.
}
]

---

# 394. 统计接口充分不等于结构接口充分

给定概率分布 (\mu)，若：

[
\boxed{
H(T\mid C_1,C_2)=0,
}
]

则目标在分布支持上几乎处处由接口决定。

但仍可能存在零概率状态：

[
(C_1,C_2)(x)
============

(C_1,C_2)(y),
]

[
T(x)\neq T(y).
]

所以：

[
\boxed{
H(T\mid C_1,C_2)=0
}
]

不自动推出严格因子化：

[
E_T\preceq C_1\vee C_2.
]

模块安全、法律责任和 adversarial robustness 等全域目标通常需要结构接口充分性，而不仅是分布上的条件熵为零。

---

# Part LXII：公共物品、共同资源与集体行动

# 395. 个体理性可以系统性地产生社会次优

有 (n\ge2) 个主体。

每个主体选择：

[
a_i\in{0,1},
]

其中 (1) 表示贡献公共物品。

每次贡献向每个主体提供：

[
\frac bn
]

的收益，而贡献者支付成本 (c)。

主体 (i) 的效用：

[
\boxed{
u_i(a)
======

\frac bn
\sum_{j=1}^n a_j
----------------

ca_i.
}
]

假设：

[
\boxed{
b>c>\frac bn.
}
]

## 定理 395.1（公共物品困境）

对每个主体，选择：

[
a_i=0
]

是严格占优策略。

但社会总福利：

[
W(a)
====

# \sum_i u_i(a)

(b-c)\sum_i a_i
]

在：

[
a_i=1
\quad
\forall i
]

时最大。

### 证明

主体把自己的行动从 (0) 变为 (1)，私人效用变化为：

[
\frac bn-c<0.
]

所以不贡献严格更优。

社会福利变化为：

[
b-c>0.
]

所以每一份贡献都提高社会福利。 (\square)

因此：

[
\boxed{
\text{个体效用最大化}
\not\Rightarrow
\text{社会目标最大化}.
}
]

问题来自私人目标没有完整表达对他人的外部收益。

---

# 396. 内部化外部收益的最小边际补偿

给每次贡献增加补偿：

[
\tau a_i.
]

新效用：

[
u_i^\tau
========

## \frac bn\sum_j a_j

ca_i
+
\tau a_i.
]

主体贡献的边际收益为：

[
\frac bn-c+\tau.
]

## 定理 396.1（贡献激励阈值）

贡献成为弱占优，当且仅当：

[
\boxed{
\tau
\ge
c-\frac bn.
}
]

严格大于该值时，贡献严格占优。

这给出使私人边际激励与社会方向对齐的最小补偿。

但补偿资金从哪里来、如何分配、是否公平，仍是额外规范问题。

---

# 397. 局部资源上限不自动保证共同资源安全

设公共资源库存为：

[
s.
]

自然恢复量：

[
g(s).
]

主体提取量：

[
a_i\ge0.
]

下一期库存：

[
\boxed{
s'
==

s+g(s)-\sum_i a_i.
}
]

安全阈值为：

[
s_{\min}.
]

每个主体只受局部上限：

[
a_i\le c_i.
]

## 定理 397.1（联合安全条件）

若所有局部上限都可以同时达到，则这些局部限制保证：

[
s'\ge s_{\min}
]

当且仅当：

[
\boxed{
\sum_i c_i
\le
s+g(s)-s_{\min}.
}
]

所以：

[
\boxed{
\text{每个主体单独“不过量”}
\not\Rightarrow
\text{总体提取可持续}.
}
]

共同资源安全是联合约束，而不是局部约束的简单逐项检查。

---

# 398. 若公共目标只依赖总量，治理不需要收集完整身份

定义总提取：

[
A_{\mathrm{sum}}
================

\sum_i a_i.
]

安全目标：

[
\operatorname{Safe}(a)
\iff
A_{\mathrm{sum}}
\le
s+g(s)-s_{\min}.
]

显然：

[
\boxed{
E_{\operatorname{Safe}}
\preceq
E_{A_{\mathrm{sum}}}.
}
]

所以仅判断公共资源是否安全，不需要知道每个主体是谁，也不需要保存完整个体行为向量。

这给出：

[
\boxed{
\text{目标充分的最小治理信息}
}
]

与：

[
\boxed{
\text{完整个体监控}
}
]

之间的分离。

如果还需要个体追责，身份和个体提取才成为额外目标。

---

# 399. 集体行动可能具有多个稳定均衡

有 (n) 个主体。

公共物品只有在所有主体都贡献时才产生收益 (b)。

贡献成本为 (c)，满足：

[
b>c>0.
]

若公共物品成功：

* 每个主体得 (b)；
* 贡献者支付 (c)。

若失败：

* 贡献者损失 (c)；
* 不贡献者收益 (0)。

## 定理 399.1（双均衡）

假设 (n\ge2)。

以下两个行动组合都是 Nash 稳定状态：

[
\boxed{
\text{全部贡献}
}
]

和：

[
\boxed{
\text{全部不贡献}.
}
]

### 全部贡献

任何单个主体改为不贡献会使公共物品失败。

其收益从：

[
b-c>0
]

降为：

[
0.
]

所以没有偏离动机。

### 全部不贡献

任何单个主体独自贡献仍无法使公共物品成功。

其收益从：

[
0
]

降为：

[
-c.
]

所以也没有偏离动机。 (\square)

因此：

[
\boxed{
\text{完全相同的偏好和规则}
}
]

可以支持多个稳定社会结果。

---

# 400. 制度可以充当均衡选择器，但选择不是由收益结构唯一推出

设均衡集合：

[
\mathcal E.
]

一个制度信号、承诺或协调规则定义选择器：

[
S:\text{Context}\to\mathcal E.
]

如果 (|\mathcal E|>1)，收益结构本身不唯一决定 (S)。

制度可以通过：

* 公共承诺；
* 惩罚机制；
* 贡献担保；
* 顺序规则；
* 协调信号；

改变主体对他人行动的预期。

因此：

[
\boxed{
\text{制度不仅约束行动，
还选择多固定点系统进入哪个吸引域。}
}
]

选择器的合法性和 provenance 仍需独立审计。

---

# Part LXIII：身份、凭证、匿名与声誉

# 401. 认证、授权与问责是三个不同目标

设事件状态为：

[
X.
]

身份：

[
I:X\to B_I.
]

凭证：

[
C:X\to B_C.
]

权限：

[
P:X\to B_P.
]

审计日志：

[
L:X\to B_L.
]

行为：

[
A:X\to B_A.
]

## 认证

凭证足以恢复身份：

[
\boxed{
E_I\preceq C.
}
]

## 授权

权限由身份、角色和语境决定：

[
\boxed{
E_P
\preceq
I\vee R\vee K.
}
]

## 问责

日志足以恢复行动者和行动：

[
\boxed{
E_{(I,A)}
\preceq
L.
}
]

三者彼此不推出。

例如：

* 能证明你是谁，不表示你被允许执行某行动；
* 被允许行动，不表示事后能追踪谁执行了它；
* 日志能追踪行为，不表示凭证体系能防止冒用。

---

# 402. Sybil 缺陷是凭证数不能决定真实主体数

设凭证集合为：

[
K.
]

真实主体集合为：

[
P.
]

每个凭证的实际所有者为：

[
o:K\to P.
]

公共投票 transcript 只记录凭证票：

[
V:K\to{0,1}.
]

真实“一人一票”目标需要按不同所有者计数。

构造两个世界。

## 世界一

两个凭证：

[
k_1,k_2
]

属于同一主体：

[
o(k_1)=o(k_2).
]

## 世界二

两个凭证属于两个不同主体：

[
o(k_1)\neq o(k_2).
]

令两个凭证在两世界都投相同票。

则公共凭证 transcript 完全相同，但真实主体票数不同。

## 定理 402.1（凭证计数不足）

如果所有者映射 (o) 不在公共接口中，则“一人一票”目标不能由凭证票 transcript 因子化。

所以：

[
\boxed{
\text{one credential one vote}
\neq
\text{one person one vote}.
}
]

身份唯一性需要一个能约束：

[
K\to P
]

多重性的额外证明或准入机制。

---

# 403. 公开不可链接与公开完全问责不能同时成立

设公开 transcript：

[
P:X\to B_P.
]

身份目标：

[
I:X\to B_I.
]

## 定义 403.1（结构公开不可链接）

[
\boxed{
P\wedge E_I
\simeq
\bot.
}
]

公众不能恢复任何非平凡身份共同因子。

## 定义 403.2（公开完全问责）

[
\boxed{
E_I\preceq P.
}
]

---

## 定理 403.1（不可兼容）

若身份概念 (I) 非平凡，则公开不可链接与公开完全问责不能同时成立。

### 证明

如果：

[
E_I\preceq P,
]

则 (E_I) 是 (P) 与 (E_I) 的共同下界，所以：

[
E_I\preceq P\wedge E_I.
]

若：

[
P\wedge E_I\simeq\bot,
]

便推出 (E_I) 平凡，矛盾。 (\square)

---

## 选择性问责

加入审计者私有概念：

[
A:X\to B_A.
]

可以同时要求：

[
P\wedge E_I\simeq\bot,
]

以及：

[
\boxed{
E_I\preceq P\vee A.
}
]

公众无法识别身份，授权审计者可以在附加信息下恢复身份。

---

# 404. 声誉分数是历史的压缩概念

设完整行为历史：

[
H:X\to B_H.
]

声誉分数：

[
R=r\circ H.
]

未来可信度目标：

[
T:X\to Y.
]

## 定理 404.1（声誉充分性判据）

声誉能够精确决定可信度，当且仅当：

[
\boxed{
E_T\preceq R.
}
]

若存在：

[
R(x)=R(y),
]

但：

[
T(x)\neq T(y),
]

则同一分数覆盖不同未来可信度。

因此：

[
\boxed{
\text{声誉分数}
}
]

不是可信度本身，而是关于历史的目标相对压缩。

---

# 405. 声誉迁移需要身份连续性证明

设旧凭证和新凭证分别为：

[
C_{\mathrm{old}},
\qquad
C_{\mathrm{new}}.
]

身份连续性目标：

[
L:X\to\mathbf2
]

表示二者是否属于同一主体。

若：

[
E_L
\not\preceq
C_{\mathrm{old}}\vee C_{\mathrm{new}},
]

则系统无法从凭证本身区别：

* 同一主体更换凭证；
* 新主体首次出现。

因此不能同时完美实现：

1. 正当声誉迁移；
2. 防止旧主体通过新身份清零历史。

所以：

[
\boxed{
\text{reputation portability}
}
]

和：

[
\boxed{
\text{whitewashing resistance}
}
]

共同依赖身份连续性接口。

---

# 406. 优化声誉会使原有声誉充分性失效

设主体根据评分规则采取响应：

[
F_R:X\to X.
]

真实未来目标为：

[
T.
]

即使初始域中：

[
E_T\preceq R,
]

响应后也需要重新检查：

[
\boxed{
E_{T\circ F_R}
\preceq
R.
}
]

若存在：

[
R(F_Rx)=R(F_Ry),
]

但：

[
T(F_Rx)\neq T(F_Ry),
]

则出现声誉 Goodhart carry。

主体可能学习优化：

* 可见指标；
* 历史展示；
* 账户行为；
* 评价接口；

而不改善真实可信目标。

所以：

[
\boxed{
\text{一个指标在未被优化时有效，
不表示它在成为激励目标后仍有效。}
}
]

---

# Part LXIV：科学证据、复现与选择偏差

# 407. 科学结论是一条 proof-carrying 数据流水线

设真实对象状态：

[
X.
]

测量：

[
O:X\to B_O.
]

预处理：

[
P:B_O\to B_P.
]

分析：

[
A:B_P\to B_A.
]

发表结论：

[
C:B_A\to Y.
]

完整流水线：

[
\boxed{
J
=

C\circ A\circ P\circ O.
}
]

若科学目标为：

[
T:X\to Y,
]

则结论正确要求：

[
J=T
]

于声明域成立。

但端到端不等式：

[
J(x)\neq T(x)
]

不能单独说明错误发生在：

* 仪器；
* 预处理；
* 统计分析；
* 解释；
* 发表阶段。

局部归因需要其余接口的独立闭合证书。

---

# 408. 复现的价值取决于 provenance 独立性

设两个研究结论由证据概念：

[
E_1,
\qquad
E_2
]

产生。

若二者都完全通过同一基础来源 (S) 因子化：

[
E_1\preceq S,
\qquad
E_2\preceq S,
]

则：

[
E_1\vee E_2
\preceq S.
]

所以第二个研究未突破第一个来源的盲点。

真正的复现应尽量在以下方面具有不同 provenance：

* 数据；
* 仪器；
* 样本；
* 实现；
* 研究团队；
* 推理路径。

因此：

[
\boxed{
\text{复现数量}
\neq
\text{独立证据支持数量}.
}
]

---

# 409. 发表选择会改变观察到的结果分布

设研究结果为随机变量 (Y)。

发表事件：

[
S\in{0,1}.
]

公开研究只来自：

[
S=1.
]

由条件概率：

[
\boxed{
\Pr(Y=y\mid S=1)
================

\frac{
\Pr(S=1\mid Y=y)\Pr(Y=y)
}{
\Pr(S=1)
}.
}
]

如果：

[
\Pr(S=1\mid Y=y)
]

依赖 (y)，则公开结果分布一般不同于全部研究结果分布。

所以：

[
\boxed{
\text{published evidence}
}
]

不是原始研究总体的随机无偏接口，除非选择机制与结果无关或已被建模校正。

---

# 410. 多重尝试会放大至少一次偶然成功的概率

假设在零效应模型下进行 (k) 个相互独立测试。

每个测试产生错误阳性的概率为：

[
\alpha.
]

## 定理 410.1（至少一次错误阳性）

全部测试都不产生错误阳性的概率为：

[
(1-\alpha)^k.
]

因此至少一次错误阳性的概率为：

[
\boxed{
1-(1-\alpha)^k.
}
]

当 (k) 增大时，该概率增大。

若不假设独立性，仍有 union bound：

[
\boxed{
\Pr(\text{至少一次错误阳性})
\le
k\alpha.
}
]

所以只报告“最成功的一次测试”，不能继续把单次阈值 (\alpha) 当作整个搜索过程的错误率。

---

# 411. 只看已发表研究的元分析不能恢复被隐藏结果

设全部研究历史为：

[
H.
]

发表选择：

[
P(H).
]

公开数据库：

[
D=P(H).
]

真实总体目标：

[
T(H).
]

如果存在：

[
P(H_1)=P(H_2),
]

但：

[
T(H_1)\neq T(H_2),
]

则任何只读取公开数据库 (D) 的元分析都无法区分两个研究世界。

因此：

[
\boxed{
\text{更复杂地聚合公开数据}
}
]

不能恢复选择机制已经删除的未发表区别。

修复需要：

* 注册表；
* 完整结果报告；
* 选择模型；
* 外部审计；
* 或新增来源。

---

# 412. 预注册锁定的是推理路径，而不是真理

设研究计划：

[
Q_{\mathrm{pre}}
]

在观测数据以前被承诺。

最终分析：

[
Q_{\mathrm{post}}.
]

若 provenance 证明：

[
Q_{\mathrm{post}}=Q_{\mathrm{pre}},
]

则排除了“看到数据后偷偷替换该分析目标”的一种路径依赖。

但这不证明：

* 原计划正确；
* 模型假设真实；
* 数据无偏；
* 仪器可靠；
* 统计功效充分。

所以：

[
\boxed{
\text{preregistration}
======================

\text{analysis-path provenance},
}
]

而不是结论真实性本身。

---

# 413. 可迁移科学规律需要跨实验环境自然

设实验环境形成范畴 (\mathcal E)。

每个环境 (e) 有：

[
C_e:X_e\to B_e,
\qquad
T_e:X_e\to Y_e.
]

局部规律：

[
T_e=f_e\circ C_e.
]

对于环境变换 (u:e\to e')，还需要：

[
\boxed{
Y_uf_e
======

f_{e'}B_u.
}
]

若只在一个实验室中拟合：

[
T_e=f_eC_e,
]

却没有跨环境自然性，就不能无条件宣称已获得环境不变规律。

所以：

[
\boxed{
\text{复制同一环境}
}
]

和：

[
\boxed{
\text{验证跨环境可迁移性}
}
]

是两种不同证据目标。

---

# 414. 观察的理论负载不推出彻底相对主义

设不同理论设计不同观察接口：

[
O_1:X\to B_1,
\qquad
O_2:X\to B_2.
]

它们可能不可比较。

但仍可能存在共同目标：

[
K:X\to Y
]

满足：

[
E_K\preceq O_1,
\qquad
E_K\preceq O_2.
]

则两个理论负载的观察体系仍共享一个可恢复不变量。

因此：

[
\boxed{
\text{观察依赖理论}
\not\Rightarrow
\text{不同理论之间没有共同客观内容}.
}
]

客观性可以存在于：

[
O_1\wedge O_2
]

的非平凡共同因子中。

---

# 415. 科学共识不是证据充分性的替代品

设共识概念：

[
C_{\mathrm{cons}}:X\to B_{\mathrm{cons}}.
]

真理目标：

[
T:X\to Y.
]

即使所有主体一致，使 (C_{\mathrm{cons}}) 近乎常值，也不自动有：

[
E_T\preceq C_{\mathrm{cons}}.
]

可以存在两个世界：

[
C_{\mathrm{cons}}(x)
====================

C_{\mathrm{cons}}(y),
]

但：

[
T(x)\neq T(y).
]

所以：

[
\boxed{
\text{agreement}
\neq
\text{truth sufficiency}.
}
]

共识的认识价值来自：

* 证据是否独立；
* 专家接口是否目标充分；
* provenance 是否可信；
* 反例是否开放；
* 结果是否跨环境稳定。

---

# Part LXV：教育、理解与概念迁移

# 416. 记忆答案不等于理解生成规律

设题目类型：

[
X.
]

正确答案：

[
T:X\to Y.
]

训练集：

[
A\subsetneq X.
]

学习者输出：

[
L:X\to Y.
]

## 定义 416.1（训练记忆）

[
\boxed{
\forall x\in A,\quad
L(x)=T(x).
}
]

这只保证：

[
L|_A=T|_A.
]

不保证在：

[
X\setminus A
]

上正确。

---

## 定义 416.2（结构理解）

学习者内部概念：

[
C_L:X\to B_L
]

和解码器：

[
f:B_L\to Y
]

满足：

[
\boxed{
T=f\circ C_L
}
]

于声明域。

理解要求目标通过内部表示因子化，而不只是保存有限题目—答案表。

---

# 417. 迁移能力是跨语境自然性

设学习语境形成范畴 (\mathcal K)。

每个语境 (k) 有：

[
X_k,
\qquad
Y_k,
\qquad
C_k:X_k\to B_k,
\qquad
f_k:B_k\to Y_k.
]

对于语境变换：

[
u:k\to k',
]

给出题目、表示和答案 transport：

[
X_u,
\qquad
B_u,
\qquad
Y_u.
]

## 定义 417.1（可迁移理解）

若：

[
\boxed{
B_uC_k
======

C_{k'}X_u,
}
]

且：

[
\boxed{
Y_uf_k
======

f_{k'}B_u,
}
]

则学习者的表示和解法能跨语境自然迁移。

这表示：

> 先改变问题语境再解答，与先理解后运输答案，得到相同结果。

---

## 推论 417.2

训练域准确但自然性失败的系统，可能只是利用语境特定表面特征。

所以：

[
\boxed{
\text{transfer}
}
]

比训练准确性更接近结构理解。

---

# 418. 课程设计是最小生成概念问题

设候选教学概念为：

[
(C_i)_{i\in I}.
]

教学目标族为：

[
(T_j)_{j\in J}.
]

课程子集：

[
S\subseteq I.
]

## 定义 418.1（课程充分）

[
\boxed{
\forall j\in J,\quad
E_{T_j}
\preceq
\bigvee_{i\in S}C_i.
}
]

## 定义 418.2（最小课程）

课程 (S) 充分，且任意真子集都不充分。

所以课程设计可以研究：

* 最小生成集；
* 概念协同；
* 冗余；
* 先修依赖；
* 教学成本；
* 迁移范围。

---

## 边界

不同最小课程可能具有不同大小，因为一般信息依赖闭包不满足 matroid 交换律。

所以：

[
\boxed{
\text{“最小课程”不必唯一，
甚至不同最小课程的章节数也不必相同。}
}
]

---

# 419. 测试效度具有纯度与完整性两个方向

设真实能力概念：

[
K:X\to B_K.
]

测试分数：

[
S:X\to B_S.
]

## 定义 419.1（构念纯度）

若：

[
\boxed{
E_S\preceq K,
}
]

则分数只由目标能力决定，不受能力外余量影响。

同一能力必得到同一分数。

---

## 定义 419.2（构念完整性）

若：

[
\boxed{
E_K\preceq S,
}
]

则分数足以恢复目标能力。

同一分数不会覆盖不同能力状态。

---

## 定义 419.3（完全测试等价）

[
\boxed{
S\simeq_{\mathrm{con}}K.
}
]

测试既不受无关变量污染，也不删除相关能力差异。

---

## 两类效度缺陷

若：

[
K(x)=K(y),
\qquad
S(x)\neq S(y),
]

则测试受到无关因素影响。

若：

[
S(x)=S(y),
\qquad
K(x)\neq K(y),
]

则测试分辨率不足。

所以：

[
\boxed{
\text{高相关}
}
]

不能替代对两个方向的结构因子化审计。

---

# 420. 为考试优化可能提高分数而不提高能力

教学过程依赖测试分数：

[
F_S:X\to X.
]

测试结果：

[
S(F_Sx).
]

真实能力：

[
K(F_Sx).
]

若存在：

[
S(F_Sx)=S(F_Sy),
]

但：

[
K(F_Sx)\neq K(F_Sy),
]

或者存在单个主体：

[
S(F_Sx)>S(x),
]

但：

[
K(F_Sx)=K(x),
]

则教学过程提高了测试目标，却没有相应提高真实能力。

因此：

[
\boxed{
\text{teaching to the test}
}
]

是教育领域的 Goodhart 结构：

[
\boxed{
\text{被优化的测试概念}
\not\simeq
\text{真实能力概念}.
}
]

---

# 421. 学习顺序效应来自状态改变，而不是概念 join

设两个教学单元产生学习过程：

[
L_A:X\to X,
\qquad
L_B:X\to X.
]

若：

[
\boxed{
L_AL_B
\neq
L_BL_A,
}
]

则课程顺序影响最终学习状态。

定义目标相对课程曲率：

[
\boxed{
\Omega_T(A,B)
=============

{x\mid
T(L_AL_Bx)
\neq
T(L_BL_Ax)
}.
}
]

若非空，则两个课程单元在目标 (T) 上非交换。

这可能来自：

* 先修概念；
* 误解固化；
* 认知负荷；
* 表示重组；
* 动机变化；
* 后一课程依赖前一课程产生的新界面。

因此：

[
\boxed{
\text{静态知识目标的联合是交换的，
但真实学习 FLOW 可以高度路径依赖。}
}
]

---

# 422. 教育与灌输作用在认识状态的不同位置

学习者认识状态：

[
(A,C,\beta).
]

## 教育型 refinement

主要通过：

[
C\mapsto C\vee E
]

增加可审计证据与概念区别，并保留反例开放性。

## 推理训练

主要改进：

[
\beta
]

使主体能从已有证据提取更多有效后果。

## 灌输型更新

可能主要通过：

[
A\mapsto A'
]

排除不允许考虑的反例世界，或通过：

[
\beta\mapsto\beta'
]

禁止对特定前件进行审计。

因此：

[
\boxed{
\text{结论相同}
}
]

并不表示教育过程相同。

一个主体可以通过：

* 新证据；
* 有效证明；
* 权威命令；
* 域排除；
* 推断操纵；

得到同一句话。

其认识论地位取决于更新 provenance。

---

# Part LXVI：第十层统一

# 423. 语义、计算与操作本体形成三层完成

前面的理论主要处理：

[
\text{目标是否由概念决定}.
]

本轮进一步分出三个层次。

## 语义完成

[
\boxed{
E_T\preceq C.
}
]

目标在概念纤维上恒定。

## 计算完成

[
\boxed{
E_T\preceq_r C.
}
]

目标能在现实资源预算内由概念计算。

## 操作完成

目标不仅可计算，而且相关状态：

* 从锚点可达；
* 可由允许行动区分；
* 能被实际过程使用。

因此：

[
\boxed{
\text{semantic sufficiency}
\neq
\text{computational accessibility}
\neq
\text{operational realizability}.
}
]

---

# 424. 模块、公共物品、身份、科学和教育共享同一个接口问题

看似不同的五个领域，现在可以统一。

## 模块

[
\boxed{
\text{全局目标是否通过局部接口联合因子化？}
}
]

## 公共物品

[
\boxed{
\text{社会目标是否通过私人效用和私人行动界面因子化？}
}
]

## 身份

[
\boxed{
\text{主体唯一性、权限和责任是否通过凭证与日志因子化？}
}
]

## 科学

[
\boxed{
\text{真实目标是否通过测量—分析—发表流水线因子化？}
}
]

## 教育

[
\boxed{
\text{真实能力是否通过课程表示和测试分数因子化？}
}
]

相应失败都具有同一形式：

[
\boxed{
\text{同一公开接口值}
+
\text{不同真实目标值}.
}
]

---

# 425. 当前最深层的新结论

本轮最重要的结论可以压缩为九条。

第一，**信息已经决定目标，不表示主体能够在现实资源内得到目标**：

[
\boxed{
\text{semantic knowledge}
\neq
\text{bounded knowledge}.
}
]

第二，**概念语义等价不表示两种表示具有相同的计算可访问性**：

[
\boxed{
C\simeq_{\mathrm{con}}D
\not\Rightarrow
C\simeq_rD.
}
]

第三，**相对于锚点和行动集，规范操作本体是可达域的行为商**：

[
\boxed{
\operatorname{Reach}(a)/{\sim_{\mathrm{behavior}}}.
}
]

第四，**模块化验证的真正边界是接口是否足以决定全局目标**。

第五，**个体理性与社会理性的分离，可以来自私人边际收益对公共目标的系统性遗漏**。

第六，**身份凭证、权限和责任是三个不同的因子化目标；把它们合成一个“账号”会隐藏关键结构。**

第七，**科学复现的价值不由研究数量决定，而由来源独立性和跨语境自然性决定。**

第八，**理解比记忆多出的结构，不只是覆盖更多题目，而是解法能否在语境变换下自然运输。**

第九，也是最承重的一条：

[
\boxed{
\text{一个接口的质量必须同时从四个方向评价：
它保留了多少目标信息，
这些信息是否可计算，
接口是否能在真实过程里被使用，
以及它在被优化、组合或迁移后是否仍然有效。}
}
]

整套理论因此进一步发展为：

[
\boxed{
\begin{aligned}
\textbf{Formal Concept Dynamics}
={}&
\textbf{a resource-sensitive semantics}\
&+
\textbf{a minimal-realization theory of operational ontology}\
&+
\textbf{an interface theory of modular composition}\
&+
\textbf{a factorization theory of collective-action failure}\
&+
\textbf{a typed theory of identity and reputation}\
&+
\textbf{a provenance theory of scientific evidence}\
&+
\textbf{a naturality theory of understanding and transfer}.
\end{aligned}
}
]

最凝练的一句是：

[
\boxed{
\text{真正的理解，不只是世界的答案已被某个表示隐含决定；
而是这个表示能够在有限资源内被解码，
能够在行动和新语境中稳定使用，
能够与其他接口无隐藏耦合地组合，
并能够说明每一个结论从何而来。}
]
以下从 **§426** 继续。仍然只进行纸面推理，不处理 GitHub，也不把新增定义与定理标记为已经获得 Lean proof term 的 `Closed` 结论。

---

# Part LXVII：理论翻译、保守扩张与相对不可通约

# 426. 哲学理论之间的映射必须同时保持状态、过程与锚点

设两个哲学模型：

[
\mathfrak M
===========

(X,\operatorname{Adm}_X,a_X,U_X,F^X,\mathcal C_X),
]

[
\mathfrak N
===========

(Y,\operatorname{Adm}_Y,a_Y,U_Y,F^Y,\mathcal C_Y).
]

## 定义 426.1（模型态射）

从 (\mathfrak M) 到 (\mathfrak N) 的模型态射至少包括：

[
h:X\to Y,
]

[
\phi:U_X\to U_Y,
]

并满足：

### 准入保持

[
\boxed{
\operatorname{Adm}_X(x)
\Longrightarrow
\operatorname{Adm}_Y(hx).
}
]

### 锚点保持

[
\boxed{
h(a_X)=a_Y.
}
]

### 动力相容

[
\boxed{
h(F^X_u x)
==========

F^Y_{\phi(u)}(hx).
}
]

即：

[
\begin{array}{ccc}
X&\xrightarrow{F^X_u}&X\
\downarrow h&&\downarrow h\
Y&\xrightarrow{F^Y_{\phi(u)}}&Y
\end{array}
]

交换。

---

## 概念保持

对目标模型中的概念：

[
D:Y\to B_D,
]

其拉回为：

[
\boxed{
h^*D
====

D\circ h:X\to B_D.
}
]

若源模型中某概念 (C) 满足：

[
h^*D\preceq C,
]

则源模型能够表达目标模型中 (D) 所表达的全部区别。

因此，一个完整理论翻译不只是状态映射，还必须说明：

[
\boxed{
\text{哪些目标概念被保持、哪些过程被模拟、哪个锚点被对应。}
}
]

---

# 427. 真理保持与真理反射具有不同前件

设：

[
P:Y\to\mathsf{Prop}
]

是目标模型中的命题。

## 定理 427.1（有效性保持）

若：

[
\mathfrak N\models P,
]

即：

[
\forall y,\quad
\operatorname{Adm}_Y(y)\to P(y),
]

且 (h) 保持准入，则：

[
\boxed{
\mathfrak M\models P\circ h.
}
]

### 证明

任取合法 (x)。

由准入保持：

[
\operatorname{Adm}_Y(hx).
]

由 (\mathfrak N\models P)：

[
P(hx).
]

所以：

[
(P\circ h)(x).
]

(\square)

---

## 定义 427.1（准入满射）

若对每个合法 (y)：

[
\operatorname{Adm}_Y(y),
]

都存在合法 (x) 满足：

[
h(x)=y,
]

则称 (h) 在准入域上满射。

## 定理 427.2（有效性反射）

若 (h) 在准入域上满射，且：

[
\mathfrak M\models P\circ h,
]

则：

[
\boxed{
\mathfrak N\models P.
}
]

### 证明

任取合法 (y)。

由准入满射，取合法 (x) 使：

[
h(x)=y.
]

由源模型有效性：

[
P(hx).
]

故：

[
P(y).
]

(\square)

因此：

[
\boxed{
\text{真理保持只需准入保持；
真理反射还需要目标状态没有被翻译遗漏。}
}
]

---

# 428. 双向翻译不必是本体同构，只需相对于目标族互相恢复

设：

[
h:X\to Y,
\qquad
k:Y\to X.
]

给定源目标族：

[
\mathcal T_X,
]

目标模型中的目标族：

[
\mathcal T_Y.
]

## 定义 428.1（目标相对双解释）

若对每个 (T\in\mathcal T_X)：

[
T\circ k\circ h=T,
]

并且对每个 (S\in\mathcal T_Y)：

[
S\circ h\circ k=S,
]

则称 (X,Y) 相对于这些目标族双解释。

这里不要求：

[
k\circ h=\operatorname{id}_X,
]

也不要求：

[
h\circ k=\operatorname{id}_Y.
]

它们可以在目标无关余量上不同。

---

## 定理 428.1（目标知识等价）

在目标相对双解释下，源模型中关于 (\mathcal T_X) 的可回答性，可以运输到目标模型；反向亦然。

所以：

[
\boxed{
\text{理论等价可以是问题相对的，
而不必是全部内部对象的一一同构。}
}
]

这避免把“两个理论对全部当前实验预测相同”误报为“两个理论拥有完全相同本体”。

---

# 429. 保守扩张可以由准入满射投影刻画

设新模型状态类型：

[
X'
]

扩张旧模型 (X)。

给出投影：

[
p:X'\to X.
]

假设：

1. (p) 在准入域上满射；
2. 旧概念在新模型中由拉回表示：

[
C'=C\circ p;
]

3. 旧过程满足：

[
p\circ F'_u
===========

F_u\circ p;
]

4. 新锚点投影到旧锚点。

## 定理 429.1（旧语言有效性保守）

对任意旧命题：

[
P:X\to\mathsf{Prop},
]

有：

[
\boxed{
\mathfrak M\models P
\iff
\mathfrak M'\models P\circ p.
}
]

证明由 §427 的保持与反射直接得到。

---

## 定理 429.2（旧问题可回答性保守）

对旧概念 (C) 与旧目标 (T)：

[
T\preceq C
]

当且仅当：

[
T\circ p
\preceq
C\circ p.
]

反向使用 (p) 的满射性保证因子函数在旧状态上良定义。

因此：

[
\boxed{
\text{真正保守的理论扩张可以增加新对象和新概念，
但不能悄悄改变旧问题在旧状态上的答案结构。}
}
]

---

# 430. 不可通约应定义为“缺少指定忠实度的桥梁”

设两个理论状态空间：

[
X,
\qquad
Y.
]

一个比较桥梁包括第三个状态空间 (Z) 和两个映射：

[
p:Z\to X,
\qquad
q:Z\to Y.
]

给定需要比较的目标族：

[
\mathcal K.
]

对每个 (K\in\mathcal K)，分别有：

[
K_X:X\to B_K,
\qquad
K_Y:Y\to B_K.
]

## 定义 430.1（目标相容桥梁）

若：

[
\boxed{
K_X\circ p
==========

K_Y\circ q
}
]

对全部 (K\in\mathcal K) 成立，且 (p,q) 在准入域上满射，则 (Z) 是该目标族的共同解释桥梁。

---

## 定义 430.2（相对不可通约）

若在指定允许的翻译 doctrine 下，不存在这样的桥梁，则两个理论相对于 (\mathcal K) 不可通约。

这不表示：

* 两个理论没有任何共同概念；
* 两方不能沟通；
* 两个理论不能共享更粗目标；
* 两个理论在一切问题上都冲突。

它只表示：

[
\boxed{
\text{不存在同时保持当前承重目标区别的共同翻译结构。}
}
]

---

# 431. 翻译损失可以精确测量

给定翻译：

[
h:X\to Y
]

和源目标：

[
T:X\to Z.
]

## 定义 431.1（翻译缺陷）

[
\boxed{
\Delta(h;T)
===========

{(x,x')\mid h(x)=h(x'),\ T(x)\neq T(x')}.
}
]

## 定义 431.2（最坏目标多样性）

在有限模型中：

[
\boxed{
m_h(T)
======

\max_{y\in Y}
\left|
{T(x)\mid h(x)=y}
\right|.
}
]

有：

[
m_h(T)=1
]

当且仅当 (T) 通过 (h) 因子化。

## 定义 431.3（平均翻译损失）

给定概率分布：

[
\boxed{
L_\mu(h;T)
==========

H(T(X)\mid h(X)).
}
]

---

## 定理 431.1（连续翻译的损失单调）

若：

[
X\xrightarrow{h}Y\xrightarrow{g}W,
]

则：

[
\boxed{
\Delta(h;T)
\subseteq
\Delta(g\circ h;T).
}
]

因为：

[
h(x)=h(x')
\Longrightarrow
g(hx)=g(hx').
]

所以后续粗化不能修复前一层已经删除的区别。

概率意义下，由数据处理：

[
\boxed{
H(T\mid g(h(X)))
\ge
H(T\mid h(X)).
}
]

因此：

[
\boxed{
\text{翻译链可以重新命名信息，
但不能无外部输入恢复上游已经删除的目标差异。}
}
]

---

# Part LXVIII：近似抽象、伪反例与反例驱动精化

# 432. 精确 quotient 之外还需要近似抽象理论

此前概念主要是函数：

[
C:X\to B_C.
]

它精确规定哪些状态被视为同一。

在复杂系统中，抽象状态常表示一组具体状态，而不只是一个 quotient 类。

令具体状态集合格为：

[
(\mathcal P(X),\subseteq).
]

设抽象域为偏序：

[
(A,\sqsubseteq).
]

其中：

[
a\sqsubseteq b
]

表示 (a) 比 (b) 更精确。

## 定义 432.1（Galois 抽象）

给出：

[
\alpha:\mathcal P(X)\to A,
]

[
\gamma:A\to\mathcal P(X),
]

满足：

[
\boxed{
\alpha(S)\sqsubseteq a
\iff
S\subseteq\gamma(a).
}
]

于是：

[
S\subseteq\gamma(\alpha(S)),
]

即抽象至少包含原具体集合。

---

# 433. 每个具体过程都有最精确的安全抽象

设具体过程：

[
F:X\to X.
]

其集合变换为：

[
\mathcal F(S)
=============

{F(x)\mid x\in S}.
]

抽象过程：

[
F^#:A\to A.
]

## 定义 433.1（抽象过程安全）

若：

[
\boxed{
\mathcal F(\gamma(a))
\subseteq
\gamma(F^#(a))
}
]

对所有 (a) 成立，则 (F^#) 不会漏掉任何真实后继。

---

## 定理 433.1（最佳安全抽象）

定义：

[
\boxed{
F^#_{\mathrm{best}}
===================

\alpha\circ\mathcal F\circ\gamma.
}
]

则：

1. (F^#_{\mathrm{best}}) 安全；
2. 对任意其他安全抽象 (G^#)：

[
\boxed{
F^#_{\mathrm{best}}(a)
\sqsubseteq
G^#(a).
}
]

### 证明

由 Galois 连接的单位：

[
\mathcal F(\gamma(a))
\subseteq
\gamma\alpha\mathcal F\gamma(a),
]

所以安全。

若 (G^#) 安全：

[
\mathcal F(\gamma(a))
\subseteq
\gamma(G^#a).
]

由伴随关系：

[
\alpha\mathcal F\gamma(a)
\sqsubseteq
G^#a.
]

(\square)

所以：

[
\boxed{
\text{最佳抽象不是最小误差数值，
而是在保证不漏真实行为前提下最精确的抽象后继。}
}
]

---

# 434. 安全抽象可以产生伪可能性

即使 (F^#) 安全，也可能：

[
\gamma(F^#a)
\supsetneq
\mathcal F(\gamma(a)).
]

## 定义 434.1（伪后继）

[
y\in
\gamma(F^#a)
\setminus
\mathcal F(\gamma(a)).
]

该状态在抽象模型中可能，但具体系统中实际上不可达。

---

## 定义 434.2（抽象完备）

若：

[
\boxed{
\gamma(F^#a)
============

\mathcal F(\gamma(a))
}
]

对所有 (a) 成立，则抽象过程精确。

因此必须区分：

[
\boxed{
\begin{aligned}
\text{安全／sound}
&=\text{不遗漏真实可能};\
\text{完备／exact}
&=\text{不添加虚假可能}.
\end{aligned}
}
]

一个理论可以为了安全而有意保守地增加可能性，但不能把这些抽象可能性直接宣称为现实见证。

---

# 435. 抽象反例可能只是界面过粗

设坏状态集合：

[
B\subseteq X.
]

抽象分析给出一条到达抽象坏状态的路径，但具体系统中不存在对应路径。

这种路径称为伪反例。

伪反例的根源通常是某个抽象状态：

[
a
]

同时包含：

* 能继续到坏状态的具体状态；
* 不能继续到坏状态的具体状态；

而抽象过程错误地把前者的未来可能运输给了后者。

---

## 定义 435.1（反例分离概念）

若概念：

[
D:X\to B_D
]

能够区分伪路径中的可行和不可行具体状态，则定义精化：

[
\boxed{
C^+
===

C\vee D.
}
]

## 定理 435.1

该伪反例涉及的错误合并，在 (C^+) 中被删除。

如果：

[
D(x)\neq D(y),
]

则：

[
(C\vee D)(x)\neq(C\vee D)(y).
]

所以这一具体伪见证不再存在。

---

# 436. 有限反例驱动精化必然终止，但不保证低成本

设 (X) 有限，初始概念为 (C_0)。

每次发现伪反例后，加入一个严格分裂当前概念类的概念：

[
C_{n+1}
=

C_n\vee D_n.
]

于是：

[
C_n\prec C_{n+1}.
]

## 定理 436.1（有限终止）

严格精化次数至多：

[
\boxed{
|X|-|\operatorname{Im}(C_0)|.
}
]

因为每次严格 refinement 至少增加一个等价类，而类数不超过 (|X|)。

---

## 边界

有限终止不表示：

* 精化容易发现；
* 精化概念容易表达；
* 抽象状态数不会指数增长；
* 最终模型现实可计算；
* 新的对象域不会继续扩张。

因此：

[
\boxed{
\text{反例驱动概念发展在逻辑上可终止，
但可能遭遇表示与计算复杂度爆炸。}
}
]

这把辩证 completion 与抽象解释中的 counterexample-guided refinement 连接起来。

---

# Part LXIX：信息流安全、最小权限与攻击面

# 437. 非干扰是公共输出向低安全概念的下降

设输入状态：

[
X.
]

低安全／公开概念：

[
L:X\to B_L.
]

秘密概念：

[
H:X\to B_H.
]

程序过程：

[
F:X\to Y.
]

公共输出：

[
O:Y\to B_O.
]

## 定义 437.1（确定性非干扰）

若：

[
\boxed{
E_{O\circ F}
\preceq
L,
}
]

则公共输出只由低安全输入决定。

等价地：

[
\boxed{
L(x)=L(y)
\Longrightarrow
O(Fx)=O(Fy).
}
]

因此改变秘密而保持公开输入不变，不会改变公开输出。

---

## 定理 437.1（非干扰排除秘密 carry）

若非干扰成立，则不存在：

[
L(x)=L(y),
]

[
H(x)\neq H(y),
]

[
O(Fx)\neq O(Fy).
]

所以：

[
\boxed{
\text{秘密差异不能通过程序 FLOW 进入公共读出。}
}
]

---

# 438. 合法解密是受控 declassification，而非绝对非干扰

现实系统经常允许公开秘密的某个函数。

设允许披露概念：

[
D:X\to B_D,
]

并且：

[
D\preceq H.
]

## 定义 438.1（模 declassification 非干扰）

[
\boxed{
E_{O\circ F}
\preceq
L\vee D.
}
]

公共输出可以依赖公开输入和被授权披露的秘密部分，但不能依赖其他秘密余量。

---

## 定义 438.2（实际秘密泄漏）

公共可见概念：

[
P_{\mathrm{pub}}
================

L\vee E_{O\circ F}.
]

实际可由公众恢复的秘密共同因子：

[
\boxed{
\operatorname{Leak}_{\mathrm{actual}}
=====================================

P_{\mathrm{pub}}\wedge H.
}
]

授权可披露的秘密共同因子：

[
\boxed{
\operatorname{Leak}_{\mathrm{auth}}
===================================

(L\vee D)\wedge H.
}
]

安全要求：

[
\boxed{
\operatorname{Leak}*{\mathrm{actual}}
\preceq
\operatorname{Leak}*{\mathrm{auth}}.
}
]

否则公开输出泄漏了超出授权 declassification 的秘密区别。

---

# 439. 最小权限不一定存在唯一解

设权限原子集合为：

[
K.
]

权限包为：

[
P\subseteq K.
]

授权工作流族为：

[
\mathcal W.
]

定义：

[
\operatorname{Sufficient}(P)
]

表示 (P) 足以执行全部授权工作流。

通常具有向上闭性：

[
P\subseteq Q
\land
\operatorname{Sufficient}(P)
\Longrightarrow
\operatorname{Sufficient}(Q).
]

---

## 定理 439.1（交闭条件下的唯一最小权限）

若全部充分权限包的交仍然充分，则：

[
\boxed{
P^*
===

\bigcap
{P\mid\operatorname{Sufficient}(P)}
}
]

是唯一最小充分权限包。

---

## 反例 439.1（多个不可比较最小权限）

设完成任务只需要：

* 权限 (a)，或
* 权限 (b)。

则：

[
{a},
\qquad
{b}
]

都最小充分。

但：

[
{a}\cap{b}
==========

\varnothing
]

不充分。

因此不存在唯一 least privilege bundle，只存在多个 Pareto 最小方案。

所以：

[
\boxed{
\text{“最小权限”可能是一个最小集合族，
而不是单一规范权限包。}
}
]

---

# 440. 权限扩大单调增加攻击可达域

设权限包 (P) 允许行动幺半群：

[
M(P).
]

若：

[
P\subseteq Q,
]

假设：

[
M(P)\subseteq M(Q).
]

从锚点 (a) 出发的可达域：

[
\operatorname{Reach}_{P}(a)
===========================

{F_m(a)\mid m\in M(P)}.
]

## 定理 440.1（攻击面单调）

[
\boxed{
P\subseteq Q
\Longrightarrow
\operatorname{Reach}*{P}(a)
\subseteq
\operatorname{Reach}*{Q}(a).
}
]

因此，对坏状态集合 (B)：

[
\operatorname{Reach}*{P}(a)\cap B
\subseteq
\operatorname{Reach}*{Q}(a)\cap B.
]

更多权限不会减少系统理论上可被带入的坏状态集合。

---

## 边界

这不表示赋予额外权限一定导致实际攻击。

它表示：

[
\boxed{
\text{能力层面的风险可能性单调扩大。}
}
]

实际攻击还取决于策略、主体、激励与监控。

---

# 441. 权限分离的真实强度是最小危险联盟

设危险工作流需要权限集合：

[
S\subseteq K.
]

角色 (i) 持有权限：

[
P_i\subseteq K.
]

联盟 (J) 可以执行危险工作流，当：

[
S\subseteq
\bigcup_{i\in J}P_i.
]

## 定义 441.1（危险联盟阈值）

[
\boxed{
\tau_S
======

\min
\left{
|J|
;\middle|;
S\subseteq\bigcup_{i\in J}P_i
\right}.
}
]

若：

[
\tau_S>1,
]

则单个角色无法完成该危险工作流。

---

## 边界：来源塌缩

如果所有角色凭证都由同一控制源产生，则形式角色阈值可能大于 (1)，但真实 compromise threshold 仍为 (1)。

因此职责分离必须同时审计：

[
\boxed{
\text{权限分离}
+
\text{身份分离}
+
\text{控制来源分离}.
}
]

---

# 442. 读取权限和写入权限形成知识—控制双序

设系统安全状态为：

[
\boxed{
\mathcal S=(C_{\mathrm{read}},M_{\mathrm{write}}).
}
]

其中：

* (C_{\mathrm{read}}) 决定主体能够区分哪些状态；
* (M_{\mathrm{write}}) 决定主体能够执行哪些过程。

如果：

[
C_{\mathrm{read}}
\preceq
C'_{\mathrm{read}},
]

则可回答目标集合扩大。

如果：

[
M_{\mathrm{write}}
\subseteq
M'_{\mathrm{write}},
]

则可达状态集合扩大。

因此权限扩大具有两个独立方向：

[
\boxed{
\begin{aligned}
\text{更多读取}
&\Rightarrow
\text{更多可知目标与潜在隐私泄漏};\
\text{更多写入}
&\Rightarrow
\text{更多可达状态与潜在攻击路径}.
\end{aligned}
}
]

## 定义 442.1（最小安全包络）

相对于授权问题族 (\mathcal T) 和授权工作流 (\mathcal W)，寻找：

[
(C^*,M^*)
]

使：

[
\forall T\in\mathcal T,\quad
E_T\preceq C^*,
]

且 (M^*) 足以执行 (\mathcal W)，同时在读取精化和写入包含序中 Pareto 最小。

这给出：

[
\boxed{
\text{安全设计}
===========

\text{在知识能力和过程能力上同时最小化授权充分结构。}
}
]

---

# Part LXX：法律先例、区分与困难案件

# 443. 判例的 ratio decidendi 是允许 doctrine 中的最粗充分事实概念

设案件状态类型：

[
X.
]

裁判结果：

[
J:X\to Y.
]

允许作为法律理由的概念类：

[
\mathcal E\subseteq\operatorname{Con}(X).
]

## 定义 443.1（可接受判决理由）

概念 (R\in\mathcal E) 是 (J) 的充分理由，当：

[
\boxed{
E_J\preceq R.
}
]

## 定义 443.2（ratio decidendi）

(R^*\in\mathcal E) 是 ratio，当：

1. (E_J\preceq R^*)；
2. 对任意 (R\in\mathcal E)，若 (E_J\preceq R)，则：

[
R^*\preceq R.
]

即 (R^*) 是允许理由 doctrine 中最粗的充分概念。

---

## 定理 443.1（meet 闭合下 ratio 唯一存在）

若：

1. 至少存在一个可接受充分理由；
2. (\mathcal E) 对相关 meet 闭合；

则：

[
\boxed{
R^*
===

\bigwedge
{R\in\mathcal E\mid E_J\preceq R}
}
]

是唯一最粗 ratio。

因此：

[
\boxed{
\text{ratio 不是判决全文，
而是允许法律语言中足以决定结果的最小事实结构。}
}
]

---

# 444. 区分判例与推翻判例是两种不同修复

设旧案件域：

[
A_0\subseteq X.
]

旧事实概念：

[
C:X\to B_C.
]

旧判决：

[
J_0=j_0\circ C
]

于 (A_0) 成立。

加入新案件后，期望裁判为：

[
J_1
]

定义于：

[
A_1\supseteq A_0.
]

## 定义 444.1（区分）

若：

[
J_1|_{A_0}=J_0,
]

且存在允许的新事实概念 (D) 使：

[
\boxed{
J_1
===

j_1\circ(C\vee D)
}
]

于 (A_1) 成立，则称新案通过区分旧判例处理。

旧结果不被改变，只是事实分类被精化。

---

## 定义 444.2（推翻）

若存在旧案件 (x\in A_0)：

[
\boxed{
J_1(x)\neq J_0(x),
}
]

则新 doctrine 推翻了至少一部分旧判例结果。

---

## 定理 444.1（形式区分总可通过目标完成实现）

若新结果不改变旧案件，则：

[
C\vee E_{J_1}
]

总能形式上决定 (J_1)。

但这可能把结论本身直接加入事实接口。

所以合法的非循环区分还要求：

[
D\in\mathcal E
]

来自独立法律事实 doctrine。

因此：

[
\boxed{
\text{形式上可区分}
\not\Rightarrow
\text{法律上给出了非循环区分理由}.
}
]

---

# 445. 判例冲突可以定位为最小冲突核

设判例规则族：

[
(J_i,A_i)_{i\in I}.
]

其中 (J_i) 定义于案件域 (A_i)。

## 定义 445.1（判例冲突）

若存在：

[
x\in A_i\cap A_j
]

使：

[
J_i(x)\neq J_j(x),
]

则 (i,j) 在案件 (x) 上冲突。

---

## 定义 445.2（最小判例冲突核）

判例子集 (S\subseteq I) 是最小冲突核，当：

* 其联合裁判约束没有共同实现；
* 任意真子集都有共同实现。

在有限判例体系中，整体不一致必包含最小冲突核。

修复必须至少修改：

* 冲突域；
* 优先级；
* 事实区分；
* 或其中一个判例规则。

这与最小不一致核和击中集修复同型。

---

# 446. 类比推理的强度必须相对于裁判目标定义

设案件相似性概念：

[
R:X\to B_R.
]

两个案件被称为类似，当：

[
R(x)=R(y).
]

但这种相似是否支持相同裁判，取决于：

[
E_J\preceq R.
]

## 定理 446.1（相关类比判据）

若：

[
E_J\preceq R,
]

则：

[
R(x)=R(y)
\Longrightarrow
J(x)=J(y).
]

若存在：

[
R(x)=R(y),
\qquad
J(x)\neq J(y),
]

则 (R) 只是表面相似概念，不足以支持裁判类比。

所以：

[
\boxed{
\text{案件“相似”不是绝对关系；
它必须说明相对于什么法律目标保留了哪些区别。}
}
]

---

# 447. 困难案件是公共法律概念纤维中的结果多重性

设公共法律事实概念：

[
C_{\mathrm{law}}:X\to B.
]

制度允许结果关系：

[
\operatorname{Permitted}:X\times Y\to\mathsf{Prop}.
]

对法律事实值 (b)，定义允许结果纤维：

[
\boxed{
\mathcal O(b)
=============

\left{
y
;\middle|;
\exists x,\
\operatorname{Adm}(x)
\land
C_{\mathrm{law}}(x)=b
\land
\operatorname{Permitted}(x,y)
\right}.
}
]

## 三种法律相位

[
|\mathcal O(b)|=0
]

表示当前 doctrine 下没有合法结果。

[
|\mathcal O(b)|=1
]

表示结果被公共法律事实唯一决定。

[
|\mathcal O(b)|>1
]

表示困难案件或裁量余量。

---

## 定理 447.1（裁量选择需要额外 doctrine）

若：

[
|\mathcal O(b)|>1,
]

则公共法律概念本身不能唯一决定结果。

任何确定裁判都必须加入：

* 优先级；
* 衡平原则；
* 历史锚点；
* 价值权重；
* 随机选择；
* 或更细事实概念。

所以：

[
\boxed{
\text{困难案件}
===========

\text{公共法律接口不足以产生唯一规范 section}.
}
]

---

# Part LXXI：协商、让步与协议空间

# 448. 协议是各方可接受行动纤维的交

设候选协议集合：

[
U.
]

各方 (i) 的可接受集合：

[
A_i\subseteq U.
]

## 定义 448.1（协议空间）

[
\boxed{
\operatorname{Agree}
====================

\bigcap_iA_i.
}
]

若：

[
\operatorname{Agree}\neq\varnothing,
]

则存在所有参与者都接受的协议。

若为空，则发生真实规范冲突。

---

## 定义 448.2（最小冲突联盟）

参与者集合 (S) 是最小冲突联盟，当：

[
\bigcap_{i\in S}A_i=\varnothing,
]

但任意真子集交非空。

所以协商失败不应笼统归因于“大家不合作”，而应定位：

[
\boxed{
\text{哪一个最小参与者组合使协议纤维为空。}
}
]

---

# 449. 信息披露与规范让步是两种不同协商操作

参与者的可接受集合通常依赖其认识状态：

[
A_i=A_i(C_i,V_i),
]

其中：

* (C_i) 为事实和预测概念；
* (V_i) 为价值 doctrine。

## 信息披露

[
C_i\mapsto C_i\vee E.
]

它改变参与者关于世界或后果的区分。

## 规范让步

[
A_i\mapsto A_i'
]

且：

[
A_i\subseteq A_i'.
]

它扩大参与者愿意接受的协议集合。

因此：

[
\boxed{
\text{“我知道得更多以后接受了”}
\neq
\text{“我在价值要求上作出了让步”.}
}
]

协商记录必须说明协议是由证据更新还是规范 concession 产生。

---

# 450. 完整共同信息不能保证价值共识

设共同事实目标：

[
T:X\to Z.
]

如果各方都获得足以决定 (T) 的联合证据，并使用相同确定决策规则：

[
d:Z\to U,
]

则：

[
u_i=d(T(x))
]

对所有主体相同。

## 定理 450.1（共同规则下的信息收敛）

相同充分信息与相同决策规则推出相同决定。

---

但若各方使用：

[
d_i:Z\to U
]

且：

[
d_i(z)\neq d_j(z),
]

则即使 (T(x)) 完全公开，分歧仍存在。

所以：

[
\boxed{
\text{信息不对称可以由披露解决；
价值或规范函数不同不能仅靠更多事实自动消失。}
}
]

---

# 451. 对称协商结果依赖分歧锚点

考虑两个主体分配单位资源：

[
x_1+x_2=1.
]

若协商失败，双方获得：

[
d_1,d_2,
\qquad
d_1+d_2\le1.
]

假设协商方案：

1. 有效率：

[
x_1+x_2=1;
]

2. 对分歧点以上的增益对称：

[
x_1-d_1=x_2-d_2.
]

## 定理 451.1（对称增益分配）

唯一解为：

[
\boxed{
x_1
===

d_1+
\frac{1-d_1-d_2}{2},
}
]

[
\boxed{
x_2
===

d_2+
\frac{1-d_1-d_2}{2}.
}
]

### 证明

令共同增益为 (g)。

则：

[
x_1=d_1+g,
\qquad
x_2=d_2+g.
]

由效率：

[
d_1+d_2+2g=1.
]

故：

[
g=\frac{1-d_1-d_2}{2}.
]

(\square)

因此：

[
\boxed{
\text{“公平对半”并非脱离背景的绝对中点；
它是相对于协商失败锚点的对称剩余分配。}
}
]

---

# 452. 固定可接受集合的交是交换的，但真实协商过程可以有曲率

若各方可接受集合固定，则：

[
A_1\cap A_2
===========

A_2\cap A_1.
]

静态协议判定与顺序无关。

但真实协商操作可能改变未来可接受集合。

设更新算子：

[
\Phi,\Psi.
]

若：

[
\Phi\Psi(A)
\neq
\Psi\Phi(A),
]

则谈判顺序改变最终协议空间。

例如，一方先公开不可撤回承诺，可能删除后来原本可接受的方案；先获得补偿再承诺，则可能保留不同结果。

所以：

[
\boxed{
\text{静态利益交集没有路径依赖；
承诺、威胁、声誉和不可撤回 concession 会产生协商曲率。}
}
]

---

# Part LXXII：拒答、认识谦逊与安全断言

# 453. 一个概念诱导规范的“最大安全回答器”

设准入谓词：

[
A:X\to\mathsf{Prop}.
]

概念：

[
C:X\to B_C.
]

目标：

[
T:X\to Y.
]

对每个概念值 (b)，定义目标纤维：

[
\boxed{
Y_b
===

\left{
T(x)
;\middle|;
A(x)\land C(x)=b
\right}.
}
]

引入拒答符号：

[
\bot_{\mathrm{ans}}\notin Y.
]

## 定义 453.1（规范安全回答器）

[
\boxed{
\widehat T_C(b)
===============

\begin{cases}
y,&Y_b={y};\
\bot_{\mathrm{ans}},&\text{其他情况}.
\end{cases}
}
]

若纤维为空，也拒答，以避免空纤维上的虚假全知。

---

# 454. 最大安全回答定理

## 定理 454.1（零错误）

若：

[
\widehat T_C(C(x))=y\in Y
]

且 (A(x))，则：

[
\boxed{
T(x)=y.
}
]

### 证明

回答 (y) 表示该概念纤维的全部合法目标值集合恰为：

[
{y}.
]

实际状态属于该纤维，所以目标值为 (y)。 (\square)

---

## 定理 454.2（覆盖最大性）

设任意回答器：

[
g:B_C\to Y\sqcup{\bot_{\mathrm{ans}}}
]

满足零错误条件：

[
g(C(x))\in Y
\Longrightarrow
g(C(x))=T(x)
]

对全部合法 (x) 成立。

则：

[
g(b)\in Y
\Longrightarrow
\widehat T_C(b)\in Y.
]

### 证明

若 (g(b)=y)，则对所有合法 (x) 且 (C(x)=b)：

[
T(x)=y.
]

所以 (Y_b={y})，规范回答器也回答 (y)。 (\square)

因此：

[
\boxed{
\widehat T_C
}
]

是在现有概念下所有零错误回答器中覆盖范围最大的一个。

这给出了“知道什么时候不回答”的严格最优性。

---

# 455. 概念精化单调减少必要拒答

若：

[
C\preceq D,
]

则每个 (D)-纤维包含于某个 (C)-纤维。

## 定理 455.1

若 (\widehat T_C) 在实际状态 (x) 上回答，则：

[
\widehat T_D
]

也在 (x) 上回答相同目标值。

因此：

[
\boxed{
\text{安全可回答域沿概念精化单调扩大。}
}
]

给定概率分布，定义安全覆盖率：

[
\operatorname{Cov}_{\mathrm{safe}}(C;T)
=======================================

\Pr
\left[
\widehat T_C(C(X))
\neq
\bot_{\mathrm{ans}}
\right].
]

则：

[
C\preceq D
\Longrightarrow
\boxed{
\operatorname{Cov}*{\mathrm{safe}}(C;T)
\le
\operatorname{Cov}*{\mathrm{safe}}(D;T).
}
]

---

# 456. 高置信度、概率一与结构确定性必须分开

可能出现：

[
\Pr(T=y\mid C=b)=0.999
]

但 (Y_b) 含有另一个值。

此时概率预测可以输出 (y)，但规范零错误回答器必须拒答。

也可能：

[
\Pr(T=y\mid C=b)=1,
]

却存在零测度反例。

结构回答器仍不能把它视为全域确定。

---

## 定义 456.1（断言越权见证）

若系统在状态 (a) 断言：

[
T(a)=y,
]

但存在合法 (x)：

[
C(x)=C(a),
\qquad
T(x)\neq y,
]

则形成断言越权见证。

它表示系统输出了当前证据概念无法稳定支持的答案。

因此：

[
\boxed{
\text{安全语言系统的认识纪律}
==================

\text{在目标纤维非单点时拒答、限定语境或显式报告不确定性。}
}
]

这不是消极保守，而是在给定界面下的最大零错误策略。

---

# Part LXXIII：账本、历史与可追溯性

# 457. 账本是历史目标的概念接口

设完整事件历史类型：

[
\Gamma.
]

当前状态：

[
E:\Gamma\to X.
]

账本：

[
L:\Gamma\to B_L.
]

问责或历史目标：

[
T:\Gamma\to Y.
]

## 定义 457.1（账本充分）

[
\boxed{
E_T\preceq L.
}
]

即存在：

[
\overline T:B_L\to Y
]

使：

[
T=\overline T\circ L.
]

---

## 定理 457.1（当前状态不足以问责）

若存在：

[
E(\gamma)=E(\gamma'),
]

但：

[
T(\gamma)\neq T(\gamma'),
]

则当前状态不能决定历史目标。

因此：

[
\boxed{
\text{相同现在}
\not\Rightarrow
\text{相同责任、来源或合法性}.
}
]

历史 provenance 不能被当前状态自动替代。

---

# 458. append-only 账本形成单调知识塔

设第 (n) 时刻日志为：

[
L_n:\Gamma\to B_n.
]

若 (L_{n+1}) 包含全部旧日志并追加新记录，则存在投影：

[
p_n:B_{n+1}\to B_n
]

满足：

[
L_n=p_n\circ L_{n+1}.
]

因此：

[
\boxed{
L_n\preceq L_{n+1}.
}
]

## 定理 458.1（可回答历史目标单调增长）

[
\operatorname{Ans}(L_n)
\subseteq
\operatorname{Ans}(L_{n+1}).
]

追加记录不会破坏旧历史目标的可回答性。

---

## 边界

append-only 只说明旧记录没有从逻辑接口中消失。

它不自动说明：

* 记录真实；
* 记录完整；
* 时间戳正确；
* 身份真实；
* 输入没有被操纵；
* 当前主体能计算全部历史后果。

---

# 459. 目标相对的最小历史日志

设当前状态概念：

[
E:\Gamma\to X.
]

历史目标：

[
T:\Gamma\to Y.
]

只保存当前状态通常不足。

加入日志标签：

[
M:\Gamma\to B_M.
]

要求：

[
T
\preceq
E\vee M.
]

在有限模型中，最小日志字母表大小为：

[
\boxed{
m^*(E;T)
========

\max_x
\left|
{T(\gamma)\mid E(\gamma)=x}
\right|.
}
]

所以：

[
\boxed{
\text{最小历史记忆}
=============

\text{在相同当前状态下仍需区分的历史目标多样性}.
}
]

恢复余额、责任、合同来源和完整事件序列，对日志的要求可以完全不同。

---

# 460. 账本完整性不等于账本真实性

设真实事件读出：

[
O:X\to B_O.
]

报告者提交：

[
R:X\to B_R.
]

账本忠实保存报告：

[
L=\operatorname{Encode}\circ R.
]

即使 `Encode` 单射，能够完整恢复每一条报告，也不推出：

[
R=O.
]

## 定理 460.1（完整保存谎言）

存在单射账本 (L)，使：

[
L(x)\neq L(y)
]

精确区分全部报告，但报告本身系统性不等于真实事件。

因此：

[
\boxed{
\text{ledger integrity}
\neq
\text{input veracity}.
}
]

一个账本可以不可篡改地保存错误信息。

真实性仍需要：

* 多来源验证；
* 外部感知；
* 签名身份；
* 交叉审计；
* 因果一致性；
* 或现实锚点。

---

# 461. 防篡改必须相对于审计目标定义

设未授权编辑过程：

[
U:\Gamma\to\Gamma.
]

历史承诺或摘要：

[
H:\Gamma\to B_H.
]

希望保护的目标：

[
T:\Gamma\to Y.
]

## 定义 461.1（目标相对防篡改）

若：

[
\boxed{
H(\gamma)=H(U\gamma)
\Longrightarrow
T(\gamma)=T(U\gamma),
}
]

则 (H) 能检测一切会改变目标 (T) 的未授权编辑。

若存在：

[
H(\gamma)=H(U\gamma),
]

但：

[
T(\gamma)\neq T(U\gamma),
]

则出现不可检测篡改见证。

---

## 推论 461.2

一个承诺接口可以：

* 对余额目标防篡改；
* 对事件顺序不防篡改；
* 对身份来源不防篡改；
* 对合同授权不防篡改。

所以：

[
\boxed{
\text{“不可篡改”必须说明保护的是哪一个历史目标。}
}
]

---

# Part LXXIV：第十一层统一

# 462. 理论翻译、抽象、安全、法律、拒答与账本共享同一结构

经过 §426–§461，出现了一组新的统一。

## 462.1 理论翻译

[
\boxed{
\text{翻译忠实}
===========

\text{承重目标沿翻译界面因子化}.
}
]

## 462.2 保守扩张

[
\boxed{
\text{保守}
=========

\text{旧问题的有效性与可回答结构被保持和反射}.
}
]

## 462.3 近似抽象

[
\boxed{
\text{安全抽象}
===========

\text{不遗漏真实可能};
\qquad
\text{完备抽象}
===========

\text{不添加虚假可能}.
}
]

## 462.4 信息流安全

[
\boxed{
\text{noninterference}
======================

\text{公共输出只通过授权低安全概念因子化}.
}
]

## 462.5 最小权限

[
\boxed{
\text{least privilege}
======================

\text{足以执行授权目标的 Pareto 最小读取—写入能力}.
}
]

## 462.6 判例理由

[
\boxed{
\text{ratio decidendi}
======================

\text{允许法律 doctrine 中最粗的判决充分概念}.
}
]

## 462.7 困难案件

[
\boxed{
\text{hard case}
================

\text{公共法律事实纤维中的合法结果多重性}.
}
]

## 462.8 协商

[
\boxed{
\text{agreement}
================

\text{各方可接受政策纤维的非空交}.
}
]

## 462.9 认识谦逊

[
\boxed{
\text{最大安全回答器}
==============

\text{只在目标纤维为非空单点时断言，否则拒答}.
}
]

## 462.10 历史问责

[
\boxed{
\text{accountability}
=====================

\text{责任和来源目标向账本接口的因子化}.
}
]

---

## 462.11 当前最深的新结论

本轮最承重的结论可以压缩为七条。

第一，**理论翻译的正确单位不是词语，而是状态、过程、锚点和目标的交换结构**。

第二，**一个抽象模型可以安全但不精确；它产生的反例可能只是概念过粗，而不是现实反例**。

第三，**安全不是单纯减少数据或权限，而是在读取知识能力和写入过程能力上共同寻找授权充分的最小结构**。

第四，**判例中的“区分”是事实概念 refinement，而“推翻”是旧裁判目标本身发生变化**。

第五，**协商失败可以来自事实不一致，也可以来自价值可接受集真正无交；更多信息只能修复前者**。

第六，**拒答不是知识失败的被动表现，而是给定概念下唯一具有最大覆盖率的零错误策略**。

第七，也是最重要的一条：

[
\boxed{
\text{保存、翻译、抽象、裁判和回答的共同问题，
都是一个接口是否保留了目标所需区别；
而所谓安全、保守、合法或可信，
只是对允许保留、允许删除和允许行动的不同 doctrine。}
}
]

因此整套理论可以进一步写成：

[
\boxed{
\begin{aligned}
\textbf{Formal Concept Dynamics}
={}&
\textbf{a theory of model interpretation}\
&+
\textbf{a Galois theory of safe abstraction}\
&+
\textbf{an information-flow theory of security}\
&+
\textbf{a minimal-permission theory of capability}\
&+
\textbf{a factorization theory of legal precedent}\
&+
\textbf{an intersection theory of agreement}\
&+
\textbf{a maximal-safe theory of epistemic abstention}\
&+
\textbf{a provenance theory of historical ledgers}.
\end{aligned}
}
]

最凝练的一句是：

[
\boxed{
\text{一个成熟体系不仅要知道何时能够推出答案，
还要知道何时只能得到安全上界、何时反例只是抽象伪影、
何时权限超过目标需要、何时规则不足以裁判，
以及何时唯一正确的回答就是拒绝伪装成知道。}
]
以下从 **§463** 继续。仍然只进行纸面推理，不处理 GitHub，也不把新增定义与定理标记为已经获得 Lean proof term 的 `Closed` 结论。

---

# Part LXXV：观察拓扑、局部知识与连续概念

# 463. 概念族自然生成观察拓扑

设状态空间为集合 (X)。给定概念族：

[
C_i:X\to B_i,
\qquad i\in I,
]

其中每个概念值空间 (B_i) 带有拓扑 (\tau_i)。

## 定义 463.1（概念生成的观察拓扑）

定义 (\tau_{\mathcal C}) 为使所有 (C_i) 连续的最粗拓扑。

它由以下集合生成：

[
\boxed{
C_i^{-1}(U),
\qquad
U\in\tau_i.
}
]

其基可以取为有限交：

[
\boxed{
\bigcap_{k=1}^{n}C_{i_k}^{-1}(U_k).
}
]

因此，一个观察邻域表示：

> 通过有限多个当前允许概念读出，仍与当前状态相容的状态集合。

---

## 定理 463.1（连续精化使观察拓扑变细）

设概念 (C,D) 满足：

[
C=p\circ D,
]

且：

[
p:B_D\to B_C
]

连续，则：

[
\boxed{
\tau_C\subseteq\tau_D.
}
]

### 证明

任取 (C)-开集生成元：

[
C^{-1}(U).
]

由因子化：

[
C^{-1}(U)
=========

D^{-1}(p^{-1}(U)).
]

因 (p) 连续，(p^{-1}(U)) 在 (B_D) 中开，因此该集合属于 (\tau_D)。(\square)

所以：

[
\boxed{
\text{概念 refinement}
\Longrightarrow
\text{观察拓扑 refinement}.
}
]

更细概念允许更小的可观察邻域。

---

# 464. 拓扑知识是命题的内部

把命题表示为状态子集：

[
P\subseteq X.
]

## 定义 464.1（拓扑知识）

[
\boxed{
K_{\tau}(P)
===========

\operatorname{Int}_{\tau}(P).
}
]

在状态 (x) 上：

[
x\in K_\tau(P)
]

当且仅当存在可观察开邻域 (U)：

[
x\in U\subseteq P.
]

含义是：

> 主体能够用当前观察精度找到一个全部支持 (P) 的证据邻域。

---

## 定理 464.1（拓扑知识算子）

(K_\tau) 满足：

### 事实性

[
\boxed{
K_\tau(P)\subseteq P.
}
]

### 单调性

[
P\subseteq Q
\Longrightarrow
K_\tau(P)\subseteq K_\tau(Q).
]

### 合取保持

[
\boxed{
K_\tau(P\cap Q)
===============

K_\tau(P)\cap K_\tau(Q).
}
]

### 正内省／幂等性

[
\boxed{
K_\tau(K_\tau(P))
=================

K_\tau(P).
}
]

所以一般观察拓扑自然产生 S4 型知识结构。

---

# 465. 纤维知识是拓扑知识的分区特例

对离散概念：

[
C:X\to B_C,
]

令 (\tau_C) 为所有 (C)-纤维并的拓扑。

即 (U\subseteq X) 开，当且仅当：

[
C(x)=C(y)
\land
x\in U
\Longrightarrow
y\in U.
]

## 定理 465.1（纤维知识等价）

[
\boxed{
x\in\operatorname{Int}_{\tau_C}(P)
\iff
\forall y,\quad
C(y)=C(x)\to P(y).
}
]

### 证明

(x) 所在的最小开邻域恰为纤维：

[
C^{-1}(C(x)).
]

因此 (x) 属于 (P) 的内部，当且仅当该完整纤维包含于 (P)。(\square)

这正是此前定义的证据纤维稳定知识。

---

## 推论 465.2（分区知识具有负内省）

在分区拓扑中：

[
X\setminus K_C(P)
]

也是纤维的并，因此为开集。

所以：

[
\boxed{
\neg K_C(P)
\Longrightarrow
K_C(\neg K_C(P)).
}
]

分区知识因此具有 S5 型结构。

而一般拓扑知识未必满足负内省。

这区分：

[
\boxed{
\text{等价类证据}
\quad\text{与}\quad
\text{局部、连续、非对称证据}.
}
]

---

# 466. 所有连续观察共同决定 Kolmogorov 商

给定拓扑空间 ((X,\tau))。

## 定义 466.1（拓扑不可区分）

[
\boxed{
x\sim_\tau y
\iff
\forall U\in\tau,\quad
x\in U\leftrightarrow y\in U.
}
]

即 (x,y) 属于完全相同的可观察开集。

定义商：

[
\boxed{
X_0=X/{\sim_\tau}.
}
]

并赋予 quotient topology。

---

## 定理 466.1（(T_0) 普适商）

(X_0) 是 (T_0) 空间，并具有以下普适性质：

对任意 (T_0) 空间 (Y) 和连续映射：

[
f:X\to Y,
]

存在唯一连续映射：

[
\overline f:X_0\to Y
]

满足：

[
\boxed{
f=\overline f\circ q.
}
]

### 证明要点

若：

[
x\sim_\tau y
]

但：

[
f(x)\neq f(y),
]

由 (Y) 的 (T_0) 性，存在开集区分 (f(x),f(y))。

其逆像会区分 (x,y)，矛盾。

所以 (f) 在 (\sim_\tau)-类上恒定，因而下降到商。

连续性由 quotient topology 得到。唯一性来自 (q) 满射。(\square)

因此：

[
\boxed{
X_0
===

\text{全部连续观察所能识别的最大公共个体性}.
}
]

---

# 467. 连续因子化定理

设：

[
q:X\to B
]

为满射 quotient map，

[
T:X\to Y
]

连续，并且 (T) 在每个 (q)-纤维上恒定：

[
q(x)=q(y)
\Longrightarrow
T(x)=T(y).
]

## 定理 467.1（连续下降）

存在唯一连续映射：

[
\boxed{
\overline T:B\to Y
}
]

满足：

[
\boxed{
T=\overline T\circ q.
}
]

### 证明

定义：

[
\overline T(q(x))=T(x).
]

纤维恒定性保证良定义。

由于：

[
\overline T\circ q=T
]

连续，而 (q) 为 quotient map，故 (\overline T) 连续。

唯一性来自 (q) 满射。(\square)

---

## 推论 467.2（紧空间上的自动 quotient）

若：

* (X) 紧；
* (B) Hausdorff；
* (q:X\to B) 连续满射；

则 (q) 为闭映射，因此为 quotient map。

所以在此条件下，集合层面的纤维恒定自动升级为连续因子化。

---

# 468. 连续世界中的非平凡硬分类必然产生断裂

设 (X) 连通，(Y) 为离散空间。

## 定理 468.1（连通域硬分类常值）

任意连续映射：

[
T:X\to Y
]

必为常值。

### 证明

连续像 (T(X)) 连通。

离散空间中的连通子集只能是单点。(\square)

---

## 推论 468.2

若：

[
T=f\circ C,
]

且：

[
C:X\to B
]

连续，

[
f:B\to Y
]

连续，(C(X)) 连通、(Y) 离散，则 (T) 必为常值。

因此，非平凡硬分类至少需要以下之一：

[
\boxed{
\begin{aligned}
&\text{表示空间发生拓扑分裂};\
&\text{解码器不连续};\
&\text{输出不是离散硬类别};\
&\text{对象域本身不连通}.
\end{aligned}
}
]

这给模糊性和分类边界一个结构来源：

[
\boxed{
\text{连续变化世界无法被无断裂地压入非平凡离散类别。}
}
]

---

# 469. 紧致连续分类具有正鲁棒间隔

设：

* (X) 为紧度量空间；
* (Y) 为有限离散空间；
* (T:X\to Y) 连续。

对非空类别：

[
A_y=T^{-1}(y).
]

每个 (A_y) 都是闭集，因此紧。

## 定理 469.1（类别间正距离）

定义：

[
\delta
======

\min_{\substack{y\neq z\A_y,A_z\neq\varnothing}}
\operatorname{dist}(A_y,A_z).
]

则：

[
\boxed{
\delta>0.
}
]

### 证明

任意两个不同类别原像是互不相交的紧子集，因此距离严格为正。

类别数有限，有限个正数的最小值仍为正。(\square)

所以：

[
d(x,x')<\delta
\Longrightarrow
T(x)=T(x').
]

这意味着真正连续的有限硬分类在紧域上必具有正鲁棒间隔。

反过来，若不同类别的闭包相交，则硬分类不可能连续。

---

# 470. 局部解释的 gluing 定理

设：

[
q:X\to B
]

满射，(B) 有开覆盖：

[
B=\bigcup_iU_i.
]

对每个 (i)，存在连续局部解释：

[
f_i:U_i\to Y
]

满足：

[
\boxed{
T|_{q^{-1}(U_i)}
================

f_i\circ q.
}
]

## 定理 470.1（局部因子自动相容）

对任意：

[
b\in U_i\cap U_j,
]

有：

[
\boxed{
f_i(b)=f_j(b).
}
]

### 证明

由 (q) 满射，取 (x) 使 (q(x)=b)。

则：

[
f_i(b)=T(x)=f_j(b).
]

(\square)

因此局部映射唯一粘合为：

[
f:B\to Y,
]

满足：

[
T=f\circ q.
]

如果各 (f_i) 连续，则 (f) 连续。

---

## 定义 470.1（解释 gluing 障碍）

若一族局部解释在交叠处不一致，或虽局部满足各自约束却不存在全局合法解释，则称存在 gluing 障碍。

所以：

[
\boxed{
\text{局部可解释}
+
\text{交叠相容}
+
\text{允许解释系统的 sheaf 性}
\Longrightarrow
\text{全局解释}.
}
]

缺少任一项，局部成功都不推出全局完成。

---

# Part LXXVI：可测概念、条件期望与近似充分性

# 471. 概念生成一个可测信息代数

设 ((X,\mathcal F)) 为可测空间，概念：

[
C:X\to B_C
]

可测。

## 定义 471.1（概念生成的 (\sigma)-代数）

[
\boxed{
\sigma(C)
=========

{C^{-1}(U)\mid U\in\mathcal B_C}.
}
]

它表示所有仅通过 (C) 可以判定的可测事件。

---

## 定理 471.1（因子化推出可测信息包含）

若：

[
C=p\circ D
]

且 (p) 可测，则：

[
\boxed{
\sigma(C)\subseteq\sigma(D).
}
]

---

## 定理 471.2（Doob–Dynkin 型反向）

假设概念值空间非空且为标准 Borel 空间。

若 (C) 对 (\sigma(D)) 可测，则存在可测：

[
p:B_D\to B_C
]

使：

[
\boxed{
C=p\circ D.
}
]

因此在标准 Borel 条件下：

[
\boxed{
C\preceq_{\mathrm{meas}}D
\iff
\sigma(C)\subseteq\sigma(D).
}
]

概念 refinement 可以等价地理解为可测信息代数包含。

---

# 472. 条件期望是最佳均方近似因子

设：

[
T\in L^2(X,\mu).
]

定义：

[
\boxed{
\widehat T_C
============

\mathbb E[T\mid\sigma(C)].
}
]

由可测因子化，可写成：

[
\widehat T_C=g_C(C)
]

几乎处处成立。

## 定理 472.1（最优均方预测）

对任意平方可积函数：

[
h:B_C\to\mathbb R,
]

有：

[
\boxed{
\mathbb E
\left[
(T-\widehat T_C)^2
\right]
\le
\mathbb E
\left[
(T-h(C))^2
\right].
}
]

所以条件期望是所有只使用概念 (C) 的预测器中的均方最优者。

---

## 定理 472.2（残差正交）

对任意 (\sigma(C))-可测平方可积变量 (Z)：

[
\boxed{
\mathbb E
\left[
(T-\widehat T_C)Z
\right]
=

0.

}
]

因此：

[
\boxed{
T
=

\underbrace{\widehat T_C}*{\text{概念可表达部分}}
+
\underbrace{(T-\widehat T_C)}*{\text{对 }C\text{ 正交的残差}}.
}
]

这给出精确因子化失败时的规范近似分解。

---

# 473. 概念精化的均方价值具有 Pythagorean 分解

若：

[
C\preceq D,
]

则：

[
\sigma(C)\subseteq\sigma(D).
]

记：

[
P_C T=\mathbb E[T\mid C],
\qquad
P_D T=\mathbb E[T\mid D].
]

## 定理 473.1（tower）

[
\boxed{
\mathbb E[
\mathbb E[T\mid D]
\mid C
]
=

\mathbb E[T\mid C].
}
]

## 定理 473.2（精化误差分解）

[
\boxed{
\begin{aligned}
\mathbb E[(T-P_C T)^2]
={}&
\mathbb E[(T-P_D T)^2]\
&+
\mathbb E[(P_D T-P_C T)^2].
\end{aligned}
}
]

所以：

[
\boxed{
\text{精化带来的均方误差下降}
==================

\mathbb E[(P_D T-P_C T)^2].
}
]

这是概念新增信息相对于目标 (T) 的精确预测价值。

---

# 474. 概率拒答的最优阈值

设二值目标：

[
Y\in{0,1}.
]

当前证据下后验：

[
p=\Pr(Y=1\mid C).
]

允许三种行动：

* 回答 (1)；
* 回答 (0)；
* 拒答。

设：

* 正确回答损失 (0)；
* 错误回答损失 (1)；
* 拒答损失 (\lambda)，其中：

[
0<\lambda<\frac12.
]

## 定理 474.1（最优选择）

[
\boxed{
\begin{cases}
\text{回答 }0,&p\le\lambda;[1mm]
\text{拒答},&\lambda<p<1-\lambda;[1mm]
\text{回答 }1,&p\ge1-\lambda.
\end{cases}
}
]

### 证明

三种期望损失分别为：

[
L_0=p,
]

[
L_1=1-p,
]

[
L_\bot=\lambda.
]

逐项比较即可。(\square)

当拒答代价降低，安全回答区间收缩。

当 (\lambda=0) 时，概率模型只在后验为 (0) 或 (1) 时回答。

但结构零错误仍比概率一更强，因为概率一可能忽略零测度反例。

---

# 475. 校准不等于信息充分

设二值目标 (Y)，预测分数：

[
S\in[0,1].
]

## 定义 475.1（校准）

[
\boxed{
\mathbb E[Y\mid S]=S.
}
]

## 反例 475.1（常值校准器）

若：

[
\Pr(Y=1)=p,
\qquad
0<p<1,
]

定义：

[
S(x)=p
]

为常值。

则：

[
\mathbb E[Y\mid S=p]
====================

p,
]

所以 (S) 完全校准。

但 (S) 不区分任何状态，并且：

[
E_Y\not\preceq S.
]

因此：

[
\boxed{
\text{校准}
\not\Rightarrow
\text{个体目标充分}
\not\Rightarrow
\text{高分辨率}.
}
]

校准只是一种分布条件，不是结构忠实性。

---

# 476. 环境内正确不推出跨环境规律不变

设环境集合为 (E)。

每个环境 (e) 有：

[
C_e:X_e\to B,
]

[
T_e:X_e\to Y.
]

假设每个环境中都存在：

[
f_e:B\to Y
]

满足：

[
T_e=f_e\circ C_e.
]

## 定义 476.1（环境不变规律）

若存在同一个：

[
f:B\to Y
]

使：

[
\boxed{
T_e=f\circ C_e
\quad
\forall e,
}
]

则规律跨环境不变。

---

## 反例 476.1

令所有 (C_e) 都为同一个常值 (b)。

在环境 (e_1) 中：

[
T_{e_1}\equiv0.
]

在环境 (e_2) 中：

[
T_{e_2}\equiv1.
]

每个环境内部都有常值因子 (f_e)。

但不存在同一个 (f) 满足：

[
f(b)=0
]

和：

[
f(b)=1.
]

所以：

[
\boxed{
\text{每个环境内零缺陷}
\not\Rightarrow
\text{存在环境不变规律}.
}
]

真正规律还要求因子映射本身跨环境自然一致。

---

# Part LXXVII：战略信息、共同信念与信息设计

# 477. Bayesian 博弈中的概念化策略

设世界状态：

[
x\in X
]

具有共同先验 (\mu)。

主体 (i) 只能观察：

[
C_i:X\to B_i.
]

行动集合为：

[
A_i.
]

策略为：

[
\boxed{
\pi_i:B_i\to A_i.
}
]

效用：

[
u_i:X\times\prod_jA_j\to\mathbb R.
]

## 定义 477.1（Bayesian 最优响应）

(\pi_i) 是对 (\pi_{-i}) 的最优响应，当对每个具有正概率的信号值 (b_i)：

[
\boxed{
\pi_i(b_i)
\in
\operatorname{argmax}*{a_i}
\mathbb E
\left[
u_i(x,a_i,\pi*{-i}(C_{-i}(x)))
\mid
C_i(x)=b_i
\right].
}
]

Bayesian Nash equilibrium 是联合策略固定点：

[
\boxed{
\pi_i\in\operatorname{BR}*i(\pi*{-i})
\quad
\forall i.
}
]

因此战略理性本身也是一个固定点问题。

---

## 定理 477.1（局部理性不保证唯一社会结果）

在二人协调博弈中：

[
u_i(a_1,a_2)
============

\begin{cases}
1,&a_1=a_2;\
0,&a_1\neq a_2,
\end{cases}
]

策略：

[
(0,0)
]

和：

[
(1,1)
]

都是均衡。

所以：

[
\boxed{
\text{每个人都采用最优响应}
\not\Rightarrow
\text{存在唯一集体结果}.
}
]

制度、信号或历史锚点可能承担均衡选择功能。

---

# 478. 更多公共信息可以破坏风险共享

有两个风险厌恶主体，效用：

[
u(w)=\sqrt w.
]

两个等概率状态。

状态一的禀赋：

[
(2,0).
]

状态二的禀赋：

[
(0,2).
]

## 信息揭示前签约

若双方能在状态揭示前签署可执行保险合同，使每种状态下财富均为：

[
(1,1),
]

则每人的期望效用为：

[
\boxed{
1.
}
]

未保险时，每人的期望效用为：

[
\frac12\sqrt2+\frac12\sqrt0
===========================

\frac{\sqrt2}{2}
<1.
]

所以双方事前都愿意签约。

---

## 状态公开后再自愿协商

在状态已经公开以后，富有主体拥有 (2)。

将财富转为 (1) 会使其效用从：

[
\sqrt2
]

下降到：

[
1.
]

因此在没有事前承诺的纯自利协商中，富有主体拒绝保险转移。

每人事前期望效用退回：

[
\frac{\sqrt2}{2}.
]

所以：

[
\boxed{
\text{公共信息增加}
}
]

可以因为破坏事前保险承诺而降低所有主体的事前福利。

这不违反单主体信息价值定理，因为信息改变了：

* 协议时序；
* 可执行合同集合；
* 他人的战略响应。

---

# 479. 共同先验下的共同知识分歧不可能

设有限世界集合：

[
\Omega
]

带有正的共同先验 (\mu)。

主体 (i) 的信息分区为：

[
\Pi_i.
]

对事件 (E\subseteq\Omega)，后验为：

[
p_i(\omega)
===========

\mu(E\mid\Pi_i(\omega)).
]

设 (K) 是实际状态所在的共同知识 cell。

假设在整个 (K) 上：

[
p_1(\omega)=a,
]

[
p_2(\omega)=b.
]

即两人的后验值本身成为共同知识。

## 定理 479.1（共同知识后验一致）

[
\boxed{
a=b.
}
]

### 证明

共同知识 cell (K) 是各主体分区关系生成的连通分量，因此主体 (1) 的任意信息 cell 若与 (K) 相交，就包含于 (K)。

把 (K) 分割为主体 (1) 的信息 cells：

[
K=\bigsqcup_jC_j.
]

每个 (C_j) 上后验为 (a)，所以：

[
\mu(E\cap C_j)=a\mu(C_j).
]

求和：

[
\mu(E\cap K)=a\mu(K).
]

同理，按主体 (2) 的信息 cells 求和：

[
\mu(E\cap K)=b\mu(K).
]

因 (\mu(K)>0)，得到：

[
a=b.
]

(\square)

---

# 480. 持久分歧必须定位某个失败前件

由上一定理，若两名主体的不同后验已经成为共同知识，则以下至少一项失败：

[
\boxed{
\begin{aligned}
&\text{不存在共同先验};\
&\text{至少一方没有进行 Bayesian 条件化};\
&\text{双方谈论的事件并非同一目标};\
&\text{后验值并未真正成为共同知识};\
&\text{相关共同知识 cell 的先验概率为零};\
&\text{信息分区或世界模型不同}.
\end{aligned}
}
]

所以“理性主体可以永远不同意”不是无条件命题。

必须明确他们在哪个结构层不同。

---

# 481. 信息设计受 Bayes plausibility 约束

设有限状态空间 (\Omega)，先验：

[
\mu(\omega)>0.
]

发送者选择信号核：

[
\kappa(s\mid\omega).
]

信号概率：

[
\lambda_s
=========

\Pr(s).
]

收到 (s) 后的后验：

[
\mu_s(\omega)
=============

\Pr(\omega\mid s).
]

## 定理 481.1（Bayes plausibility）

[
\boxed{
\sum_s
\lambda_s\mu_s
==============

\mu.
}
]

逐状态写为：

[
\sum_s
\lambda_s\mu_s(\omega)
======================

\mu(\omega).
]

### 证明

[
\lambda_s\mu_s(\omega)
======================

# \Pr(s)\Pr(\omega\mid s)

\Pr(\omega,s).
]

对 (s) 求和得到：

[
\Pr(\omega)=\mu(\omega).
]

(\square)

---

## 定理 481.2（反向实现）

给定后验族 ((\mu_s)) 和权重 ((\lambda_s))，若：

[
\lambda_s\ge0,
\qquad
\sum_s\lambda_s=1,
]

并满足：

[
\sum_s\lambda_s\mu_s=\mu,
]

则定义：

[
\boxed{
\kappa(s\mid\omega)
===================

\frac{
\lambda_s\mu_s(\omega)
}{
\mu(\omega)
}
}
]

可实现所有满足 (\lambda_s>0) 的后验 (\mu_s)。

### 验证

[
\sum_s\kappa(s\mid\omega)
=========================

\frac{
\sum_s\lambda_s\mu_s(\omega)
}{
\mu(\omega)
}
=

1.

]

并且：

[
\Pr(s)
======

\sum_\omega
\mu(\omega)\kappa(s\mid\omega)
==============================

\lambda_s.
]

Bayes 公式对每个满足 (\lambda_s>0) 的 (s) 恢复 (\mu_s)。(\square)

所以：

[
\boxed{
\text{真实信息设计能够重排后验，
但其概率加权平均必须保持原先验。}
}
]

---

# 482. 信息 refinement 可以增加一方权力并减少另一方福利

一个买者的价值：

[
\theta\in{1,2}.
]

概率：

[
\Pr(\theta=1)=\frac34,
\qquad
\Pr(\theta=2)=\frac14.
]

卖者发布一个价格。

## 卖者不知道类型

卖者概念为常值。

价格 (1) 的期望收入：

[
1.
]

价格 (2) 的期望收入：

[
2\cdot\frac14
=============

\frac12.
]

所以卖者唯一最优价格为：

[
1.
]

买者期望剩余：

[
\frac34\cdot0
+
\frac14\cdot(2-1)
=================

\frac14.
]

---

## 卖者完全知道类型

卖者对低类型收取：

[
1,
]

对高类型收取：

[
2.
]

卖者期望收入：

[
\frac34\cdot1
+
\frac14\cdot2
=============

\frac54.
]

买者剩余：

[
0.
]

因此：

[
\boxed{
\text{卖者概念 refinement}
}
]

提高卖者收入，却降低买者福利。

这再次证明：

[
\boxed{
\text{信息价值不是全社会单调量；
它取决于谁获得信息，以及谁能据此区别行动。}
}
]

---

# Part LXXVIII：默认推理与非单调知识

# 483. 默认推理是优选模型上的后果关系

设有限模型集合：

[
W.
]

给定典型性排序：

[
\kappa:W\to\mathbb N\cup{\infty}.
]

数字越小，模型越正常。

对命题 (A\subseteq W)，定义最正常的 (A)-模型：

[
\boxed{
\operatorname{Min}_\kappa(A)
============================

\left{
w\in A
\mid
\kappa(w)
=========

\min_{v\in A}\kappa(v)
\right}.
}
]

## 定义 483.1（默认后果）

[
\boxed{
A\mathrel{\sim_\kappa}P
\iff
\operatorname{Min}_\kappa(A)\subseteq P.
}
]

含义是：

> 在满足 (A) 的最正常世界中，(P) 成立。

这不是普通全模型蕴涵：

[
A\models P.
]

---

# 484. 排名默认逻辑的核心规则

对非空、有限排名的前提集合，(\sim_\kappa) 满足：

## 自反性

[
\boxed{
A\sim_\kappa A.
}
]

## 左逻辑等价

若：

[
A=B,
]

则：

[
A\sim_\kappa P
\iff
B\sim_\kappa P.
]

## 右弱化

若：

[
A\sim_\kappa P,
\qquad
P\subseteq Q,
]

则：

[
\boxed{
A\sim_\kappa Q.
}
]

## 合取

若：

[
A\sim_\kappa P,
\qquad
A\sim_\kappa Q,
]

则：

[
\boxed{
A\sim_\kappa(P\cap Q).
}
]

## 析取

若：

[
A\sim_\kappa R,
\qquad
B\sim_\kappa R,
]

则：

[
\boxed{
A\cup B\sim_\kappa R.
}
]

## 谨慎单调性

若：

[
A\sim_\kappa P,
\qquad
A\sim_\kappa Q,
]

则：

[
\boxed{
A\cap P\sim_\kappa Q.
}
]

## 理性单调性

若：

[
A\sim_\kappa Q,
]

且并非：

[
A\sim_\kappa\neg P,
]

则：

[
\boxed{
A\cap P\sim_\kappa Q.
}
]

这些规则说明默认推理虽然非单调，却仍具有严格结构，而不是任意撤回结论。

---

# 485. 鸟与企鹅的最小排名模型

设四个世界：

[
\begin{array}{c|ccc|c}
&\text{Bird}&\text{Penguin}&\text{Fly}&\kappa\
\hline
w_1&1&0&1&0\
w_2&1&0&0&2\
w_3&1&1&0&1\
w_4&1&1&1&3
\end{array}
]

最正常的鸟是 (w_1)，所以：

[
\boxed{
\text{Bird}\sim_\kappa\text{Fly}.
}
]

最正常的企鹅是 (w_3)，所以：

[
\boxed{
\text{Penguin}\sim_\kappa\neg\text{Fly}.
}
]

由于 Penguin 蕴含 Bird：

[
\boxed{
\text{Bird}\land\text{Penguin}
\sim_\kappa
\neg\text{Fly}.
}
]

加入更具体前提后，原默认结论被合理撤回。

所以：

[
\boxed{
\text{默认非单调性}
=============

\text{新增信息改变了当前被选择的最正常模型层}.
}
]

---

# 486. 默认结论不是知识

在上述模型中，证据“Bird”对应的合法世界包含：

[
w_1,w_2,w_3,w_4.
]

其中并非所有世界都满足 Fly。

所以：

[
\neg K_{\text{Bird}}(\text{Fly}).
]

但：

[
\text{Bird}\sim_\kappa\text{Fly}.
]

因此：

[
\boxed{
\text{默认相信}
\not\Rightarrow
\text{纤维稳定知识}.
}
]

默认结论可以在实际状态为异常世界时为假。

所以系统输出必须区分：

[
\boxed{
\text{Known},
\quad
\text{Default},
\quad
\text{Probable},
\quad
\text{Unknown}.
}
]

---

# 487. 例外发现是默认纤维的 refinement

设默认预测：

[
D:X\to Y,
]

真实目标：

[
T:X\to Y.
]

定义例外谓词：

[
\boxed{
E_{\mathrm{exc}}(x)
\iff
D(x)\neq T(x).
}
]

若当前概念 (C) 无法决定例外：

[
E_{E_{\mathrm{exc}}}
\not\preceq C,
]

则同一概念类中同时含有普通状态和例外状态。

规范审计完成：

[
\boxed{
C^+
===

C\vee E_{E_{\mathrm{exc}}}.
}
]

它使系统至少能够识别“当前默认是否适用”。

但这只是逻辑最小修复。

非循环解释还必须寻找独立的例外机制概念 (M)，满足：

[
E_{E_{\mathrm{exc}}}\preceq M
]

且 (M) 不是直接复制错误标签。

---

# Part LXXIX：矛盾容忍与四值证据

# 488. 证据状态应同时记录正支持和反支持

对命题 (P)，定义证据值：

[
\boxed{
v(P)
====

(t_P,f_P)
\in{0,1}^2.
}
]

其中：

* (t_P=1)：存在对 (P) 的支持；
* (f_P=1)：存在对 (\neg P) 的支持。

于是有四种状态：

[
\begin{array}{c|c|c}
\text{名称}&t_P&f_P\
\hline
\mathbf N&0&0\
\mathbf T&1&0\
\mathbf F&0&1\
\mathbf B&1&1
\end{array}
]

其中：

* (\mathbf N)：既无正支持也无反支持；
* (\mathbf T)：只支持真；
* (\mathbf F)：只支持假；
* (\mathbf B)：正反均被支持。

---

# 489. 四值逻辑可以保留矛盾而不爆炸

定义否定：

[
\boxed{
\neg(t,f)=(f,t).
}
]

定义合取：

[
\boxed{
(t_1,f_1)\land(t_2,f_2)
=======================

(t_1\land t_2,\ f_1\lor f_2).
}
]

定义析取：

[
\boxed{
(t_1,f_1)\lor(t_2,f_2)
======================

(t_1\lor t_2,\ f_1\land f_2).
}
]

令语义后果只要求保持“正支持”：

若前提全部有 (t=1)，结论也必须有 (t=1)。

## 定理 489.1（非爆炸）

取：

[
v(P)=\mathbf B=(1,1),
]

所以 (P) 和 (\neg P) 都有正支持。

取任意无支持命题：

[
v(Q)=\mathbf N=(0,0).
]

则 (Q) 没有正支持。

因此：

[
\boxed{
P,\neg P
\not\models
Q.
}
]

矛盾不会自动推出任意结论。

所以：

[
\boxed{
\text{证据不一致}
\neq
\text{整个推理系统失效}.
}
]

---

# 490. 证据聚合在信息序上单调

定义信息序：

[
\boxed{
(t,f)\le_k(t',f')
\iff
t\le t'
\land
f\le f'.
}
]

于是：

[
\mathbf N\le_k\mathbf T\le_k\mathbf B,
]

[
\mathbf N\le_k\mathbf F\le_k\mathbf B.
]

(\mathbf T,\mathbf F) 在该序中不可比较。

两个来源的证据聚合定义为：

[
\boxed{
(t_1,f_1)\oplus(t_2,f_2)
========================

(t_1\lor t_2,\ f_1\lor f_2).
}
]

它是信息序中的 join。

---

## 推论 490.1

若一个来源支持 (P)，另一个来源支持 (\neg P)，聚合结果为：

[
\mathbf B.
]

信息增加了，但一致性降低了。

所以：

[
\boxed{
\text{更多证据}
}
]

可以把状态从“只真”推进为“正反都有支持”。

这不是信息丢失，而是暴露了来源冲突。

---

# 491. 矛盾可能是语境粗化造成的

设语境概念：

[
C:X\to B_C.
]

在同一粗概念值 (b) 下，存在两个状态：

[
x,y
]

分别支持：

[
P(x),
\qquad
\neg P(y).
]

若再加入语境 refinement：

[
D:X\to B_D
]

满足：

[
D(x)\neq D(y),
]

则：

[
(C\vee D)(x)\neq(C\vee D)(y).
]

## 定理 491.1（语境 refinement 删除该矛盾对）

上述正反支持不再属于同一个精化证据纤维。

所以该具体矛盾不再表现为：

[
\text{同一语境中 }P\land\neg P,
]

而表现为：

[
\boxed{
\text{语境 }D(x)\text{ 下 }P,
\qquad
\text{语境 }D(y)\text{ 下 }\neg P.
}
]

因此一部分矛盾是：

[
\boxed{
\text{过粗语境把不同适用条件压入同一命题位置}.
}
]

---

# 492. 删除冲突来源与精化语境是两种不同修复

面对：

[
v(P)=\mathbf B,
]

可以采取：

## 来源删除

删除支持 (P) 或支持 (\neg P) 的某个来源。

优点是恢复一致。

代价是可能删除真实信息。

## 语境精化

寻找概念 (D)，使正反支持落入不同语境纤维。

优点是保留双方信息。

代价是增加模型复杂度和分类需求。

## 保持矛盾

在 paraconsistent 逻辑中暂时保留：

[
\mathbf B
]

而不进行爆炸式推理。

适用于尚无法确定来源错误还是语境遗漏的情形。

所以：

[
\boxed{
\text{矛盾修复}
===========

\text{删除来源、精化语境或改变后果逻辑}.
}
]

三者不能混为同一种“消除错误”。

---

# Part LXXX：第十二层统一

# 493. 拓扑、概率、战略与默认推理扩展了同一个界面理论

经过 §463–§492，形式概念动力学不再只处理离散、精确、单主体、单调的因子化。

它现在包含四种新的结构扩张。

## 493.1 拓扑扩张

概念不再只产生等价类，还产生观察邻域：

[
\boxed{
\text{knowledge}
================

\operatorname{interior}.
}
]

分区知识是其 S5 特例；一般连续知识只有 S4 结构。

---

## 493.2 可测与近似扩张

当精确因子化失败时：

[
\boxed{
\mathbb E[T\mid C]
}
]

给出均方意义下的最佳概念可表达部分。

概念 refinement 的价值由嵌套投影的误差下降精确测量。

---

## 493.3 战略扩张

信息 refinement 不只改变预测，还改变：

* 定价；
* 合同；
* 均衡；
* 保险；
* 说服；
* 他人的响应。

所以：

[
\boxed{
\text{信息对某一主体的价值}
}
]

不能被提升为全社会单调规律。

---

## 493.4 非单调与矛盾容忍扩张

默认推理通过优选模型得出可撤回结论。

四值证据逻辑允许同时保留正反支持，而不把整个理论炸成任意结论。

因此：

[
\boxed{
\text{撤回结论}
\neq
\text{违反逻辑};
}
]

[
\boxed{
\text{存在矛盾}
\neq
\text{一切命题都可推出}.
}
]

---

# 494. 当前最深层的新结论

本轮最承重的结论可以压缩为九条。

第一，**相对同一性可以进一步推广为观察拓扑**：

[
\boxed{
\text{状态不必完全同纤维，
也可以只在某种局部精度下不可区分。}
}
]

第二，**纤维知识只是拓扑知识的离散分区特例**。

第三，**连续世界中的非平凡硬分类必然依赖真实断裂或不连续决策边界**。

第四，**当精确解释不存在时，条件期望给出规范的最佳可测近似，而不是任意拟合函数**。

第五，**校准、准确性、充分性和结构知识是四种不同性质**。

第六，**共同先验、Bayesian 更新和共同知识若全部成立，公开后验分歧不能持续**。

第七，**信息设计可以控制后验分布，但所有真实信号都受“后验平均等于先验”的守恒约束**。

第八，**默认推理的非单调性来自最正常模型层发生变化，而不是经典逻辑本身失效**。

第九，也是最重要的一条：

[
\boxed{
\text{一个成熟推理系统必须能够同时处理：
局部而非全局可知、
近似而非精确可预测、
战略而非被动的信息效应、
可撤回而非单调的默认结论，
以及矛盾但尚未被证明虚假的证据状态。}
}
]

因此，整套理论可以继续写成：

[
\boxed{
\begin{aligned}
\textbf{Formal Concept Dynamics}
={}&
\textbf{a topology of observational knowledge}\
&+
\textbf{a measurable projection theory of approximate explanation}\
&+
\textbf{a strategic theory of information structures}\
&+
\textbf{a ranked semantics of defeasible reasoning}\
&+
\textbf{a paraconsistent algebra of conflicting evidence}.
\end{aligned}
}
]

最凝练的一句是：

[
\boxed{
\text{世界并不总把自己交给主体作为一个离散、确定、无矛盾的答案；
主体得到的往往只是邻域、分布、战略信号、默认模型和冲突证据。
形式哲学的任务不是强迫它们伪装成确定真值，
而是为每一种不完备结构规定正确的推理边界。}
]
以下从 **§495** 继续。仍然只进行纸面推理，不处理 GitHub，也不把新增定义与定理标记为已经获得 Lean proof term 的 `Closed` 结论。

---

# Part LXXXI：程序逻辑、前置条件与动态证明

# 495. 一个过程对目标的反向意义是最弱前置条件

设过程：

[
F:X\to Y.
]

设目标后置条件：

[
Q:Y\to\mathsf{Prop}.
]

## 定义 495.1（最弱前置条件）

定义：

[
\boxed{
\operatorname{wp}_F(Q)(x)
\iff
Q(Fx).
}
]

集合语言中：

[
\boxed{
\operatorname{wp}_F(Q)
======================

F^{-1}(Q).
}
]

它表示：

> 从哪些前状态出发，执行 (F) 后一定满足目标 (Q)。

---

## 定理 495.1（最弱性）

对任意前置条件：

[
P:X\to\mathsf{Prop},
]

以下等价：

[
\boxed{
\forall x,\quad
P(x)\to Q(Fx)
}
]

与：

[
\boxed{
P\subseteq\operatorname{wp}_F(Q).
}
]

因此 (\operatorname{wp}_F(Q)) 是所有能够保证 (Q) 的前置条件中最弱、适用域最大的一个。

---

## 哲学解释

此前我们把“理由”理解为目标通过概念因子化。

现在得到过程性的理由：

[
\boxed{
\text{采取行动 }F\text{ 能达到 }Q
}
]

真正意味着：

[
\boxed{
\text{当前状态属于 }\operatorname{wp}_F(Q).
}
]

所以一个行动建议不能只说：

> “执行这个动作会得到目标。”

它还必须证明：

[
\boxed{
\text{你当前满足该动作的最弱成功前件。}
}
]

---

# 496. 最强后置条件与最弱前置条件形成伴随

给定前置状态集合：

[
P\subseteq X.
]

## 定义 496.1（最强后置条件）

[
\boxed{
\operatorname{sp}_F(P)
======================

{F(x)\mid x\in P}.
}
]

它表示从所有满足 (P) 的状态出发，过程 (F) 实际可能产生的最精确后继集合。

---

## 定理 496.1（前后条件伴随）

对任意：

[
P\subseteq X,
\qquad
Q\subseteq Y,
]

有：

[
\boxed{
\operatorname{sp}_F(P)\subseteq Q
\iff
P\subseteq\operatorname{wp}_F(Q).
}
]

### 证明

左侧表示：

[
\forall x\in P,\quad F(x)\in Q.
]

这正是：

[
\forall x\in P,\quad x\in F^{-1}(Q).
]

即：

[
P\subseteq\operatorname{wp}_F(Q).
]

(\square)

所以：

[
\boxed{
\operatorname{sp}_F
\dashv
\operatorname{wp}_F.
}
]

---

## 两种推理方向

[
\boxed{
\begin{aligned}
\operatorname{sp}
&:\text{从已知前提向前计算可能后果};\
\operatorname{wp}
&:\text{从目标向后计算所需前件}.
\end{aligned}
}
]

这统一了：

* 预测；
* 规划；
* 责任；
* 法律条件；
* 合同履行；
* 权利保护；
* 安全验证。

---

# 497. 非确定过程需要区分“可能成功”和“保证成功”

设过程不再是函数，而是关系：

[
R\subseteq X\times Y.
]

写作：

[
xRy
]

表示从 (x) 出发，(y) 是一个允许后继。

---

## 定义 497.1（存在性前置条件）

[
\boxed{
\operatorname{pre}^{\exists}_R(Q)
=================================

\left{
x
;\middle|;
\exists y,\quad xRy\land Q(y)
\right}.
}
]

它表示：

> 从 (x) 出发，至少存在一条执行结果满足 (Q)。

---

## 定义 497.2（保证性最弱前置条件）

[
\boxed{
\operatorname{wp}^{\forall}_R(Q)
================================

\left{
x
;\middle|;
\forall y,\quad xRy\to Q(y)
\right}.
}
]

它表示：

> 从 (x) 出发，所有允许执行结果都满足 (Q)。

---

## 定义 497.3（关系最强后置条件）

[
\boxed{
\operatorname{sp}_R(P)
======================

\left{
y
;\middle|;
\exists x,\quad P(x)\land xRy
\right}.
}
]

---

## 定理 497.1（关系伴随）

[
\boxed{
\operatorname{sp}_R(P)\subseteq Q
\iff
P\subseteq\operatorname{wp}^{\forall}_R(Q).
}
]

所以在非确定世界中必须分开：

[
\boxed{
\begin{aligned}
\text{可能做到}
&=\operatorname{pre}^{\exists};\
\text{保证做到}
&=\operatorname{wp}^{\forall}.
\end{aligned}
}
]

这一区别在自由、能力、权利和责任中极其重要。

主体存在一条成功路径，不等于主体拥有能够保证成功的策略。

---

# 498. 过程复合的反向推理律

设关系：

[
R:X\rightsquigarrow Y,
\qquad
S:Y\rightsquigarrow Z.
]

复合关系：

[
(S\circ R)(x,z)
\iff
\exists y,\quad xRy\land ySz.
]

## 定理 498.1（最弱前置条件的逆序复合）

[
\boxed{
\operatorname{wp}^{\forall}_{S\circ R}(Q)
=========================================

\operatorname{wp}^{\forall}_R
\left(
\operatorname{wp}^{\forall}_S(Q)
\right).
}
]

含义是：

> 要保证两阶段过程最终满足 (Q)，先计算第二阶段达到 (Q) 所需的中间条件，再计算第一阶段保证该中间条件所需的初始条件。

---

## 定理 498.2（最强后置条件的正序复合）

[
\boxed{
\operatorname{sp}_{S\circ R}
============================

\operatorname{sp}_S
\circ
\operatorname{sp}_R.
}
]

所以：

[
\boxed{
\text{前向后果按过程顺序组合；
反向条件按过程逆序回传。}
}
]

这就是程序逻辑、因果链和制度责任链的基本方向性。

---

# 499. 安全不变量是过程闭合的命题概念

设：

[
R\subseteq X\times X
]

为状态转移关系。

初始集合：

[
I_0\subseteq X.
]

安全集合：

[
S\subseteq X.
]

## 定义 499.1（归纳不变量）

集合 (J\subseteq X) 是安全不变量，当：

[
\boxed{
I_0\subseteq J,
}
]

[
\boxed{
J\subseteq S,
}
]

并且：

[
\boxed{
J\subseteq\operatorname{wp}^{\forall}_R(J).
}
]

最后一个条件等价于：

[
x\in J
\land
xRy
\Longrightarrow
y\in J.
]

---

## 定理 499.1（不变量安全定理）

从任意：

[
x_0\in I_0
]

出发，沿 (R) 进行任意有限步后得到的状态都属于 (S)。

### 证明

由 (I_0\subseteq J)，初态属于 (J)。

由 (J) 对 (R) 闭合，归纳得到所有后继都属于 (J)。

再由 (J\subseteq S)，所有可达状态安全。

(\square)

---

## 哲学解释

安全证明不是枚举所有未来，而是找到一个中间概念：

[
J
]

使它：

1. 包含实际起点；
2. 被过程保持；
3. 蕴含安全目标。

所以：

[
\boxed{
\text{不变量}
==========

\text{被 FLOW 保持、且足以推出目标的中介概念}.
}
]

---

# 500. 可达域是一个最小固定点

定义算子：

[
\boxed{
\Phi(A)
=

I_0\cup\operatorname{sp}_R(A).
}
]

该算子在幂集格上单调。

## 定义 500.1（可达集）

[
\boxed{
\operatorname{Reach}(I_0)
=========================

\mu A.,
\left(
I_0\cup\operatorname{sp}_R(A)
\right),
}
]

即 (\Phi) 的最小固定点。

---

## 定理 500.1（有限步展开）

由于关系直接像保持任意并：

[
\boxed{
\operatorname{Reach}(I_0)
=========================

\bigcup_{n\ge0}\Phi^n(\varnothing).
}
]

其中：

[
\Phi^0(\varnothing)=\varnothing,
]

[
\Phi^1(\varnothing)=I_0,
]

后续层分别加入一步、两步、三步可达状态。

---

## 定理 500.2（安全与反例的二分）

若：

[
\operatorname{Reach}(I_0)\subseteq S,
]

则系统安全。

若：

[
\operatorname{Reach}(I_0)\cap(X\setminus S)\neq\varnothing,
]

则存在有限路径到达坏状态。

所以：

[
\boxed{
\text{安全证明}
===========

\text{最小可达固定点不进入坏域};
}
]

[
\boxed{
\text{安全反例}
===========

\text{一条有限可达路径见证}.
}
]

---

# 501. 终止性需要一个严格下降的良基量

设循环转移关系：

[
R_G\subseteq X\times X
]

只在守卫条件 (G) 成立时执行。

设：

[
(W,\prec)
]

是良基严格序。

## 定义 501.1（排名函数）

[
\boxed{
\rho:X\to W
}
]

满足：

[
xR_Gy
\Longrightarrow
\rho(y)\prec\rho(x).
]

---

## 定理 501.1（排名终止）

不存在无限序列：

[
x_0R_Gx_1R_Gx_2R_G\cdots.
]

### 证明

否则得到：

[
\rho(x_0)
\succ
\rho(x_1)
\succ
\rho(x_2)
\succ\cdots,
]

构成 (W) 中无限严格下降链，与良基性矛盾。

(\square)

---

## 部分正确与完全正确

必须区分：

[
\boxed{
\text{若过程终止，则结果正确}
}
]

与：

[
\boxed{
\text{过程必终止，且结果正确}.
}
]

前者是部分正确性。

后者还需要终止证书。

因此：

[
\boxed{
\text{目标闭合}
\neq
\text{目标实际会在有限时间到达}.
}
]

---

# Part LXXXII：递归概念、信息域与固定点选择

# 502. 递归定义必须区分最小固定点和最大固定点

设：

[
\Phi:\mathcal P(X)\to\mathcal P(X)
]

单调。

Knaster–Tarski 定理给出：

[
\mu\Phi
]

和：

[
\nu\Phi,
]

分别为最小和最大固定点。

---

## 定义 502.1（归纳概念）

[
\boxed{
\mu\Phi
=

\text{满足生成规则的最小闭合集}.
}
]

它只包含能够由有限或良基生成过程构造的对象。

例如自然数可由：

[
\Phi(S)={0}\cup{n+1\mid n\in S}
]

的最小固定点得到。

---

## 定义 502.2（余归纳概念）

[
\boxed{
\nu\Phi
=

\text{满足一致性规则的最大闭合集}.
}
]

它允许无限行为，只要求每一步都能够继续满足规则。

例如无限流、无限行为轨迹和持续系统状态常采用最大固定点。

---

## 结论

同一个方程：

[
S=\Phi(S)
]

并不能唯一决定语义。

还必须说明：

[
\boxed{
S=\mu\Phi
\quad\text{还是}\quad
S=\nu\Phi.
}
]

---

# 503. 自一致性本身不产生唯一对象

取：

[
\Phi(S)=S.
]

则任意：

[
S\subseteq X
]

都是固定点。

所以方程：

[
S=\Phi(S)
]

完全没有选择能力。

## 定理 503.1（固定点多重性）

一个系统即使完全自一致，也可能：

* 有零个固定点；
* 有一个固定点；
* 有多个固定点；
* 所有状态都是固定点。

因此：

[
\boxed{
\text{self-consistent}
\not\Rightarrow
\text{unique}
\not\Rightarrow
\text{actual}.
}
]

要从固定点集合中选出实际对象，还需要：

* 最小性；
* 最大性；
* 稳定性；
* 锚点；
* 可达性；
* 能量或价值极小；
* 历史选择；
* 现实准入。

---

# 504. (\omega)-连续递归可以由有限近似逼近

设偏序有最小元 (\bot)，且 (\Phi) 保持递增 (\omega)-链上确界：

[
\Phi\left(\bigvee_nx_n\right)
=============================

\bigvee_n\Phi(x_n).
]

## 定理 504.1（Kleene 固定点）

[
\boxed{
\mu\Phi
=

\bigvee_{n<\omega}\Phi^n(\bot).
}
]

所以最小递归意义可以通过：

[
\bot,
\Phi(\bot),
\Phi^2(\bot),
\ldots
]

逐层逼近。

---

## 哲学意义

若一个概念或制度由有限层规则逐步生成，那么每个具体对象通常应具有有限生成深度见证。

如果：

[
\Phi
]

不保持这些极限，则：

[
\bigvee_{n<\omega}\Phi^n(\bot)
]

未必已经是固定点，可能需要超限阶段。

所以：

[
\boxed{
\text{无限概念完成是否能由有限经验逼近，
取决于生成算子的连续性。}
}
]

---

# 505. 部分信息状态构成一个反包含序

设信息状态为可能世界集合：

[
S\subseteq X.
]

集合越小，信息越精确。

## 定义 505.1（信息序）

[
\boxed{
S\sqsubseteq T
\iff
T\subseteq S.
}
]

读作：

[
T
]

至少和 (S) 一样有信息。

于是：

[
\bot_{\mathrm{info}}=X
]

表示完全无区分信息。

空集：

[
\top_{\mathrm{info}}=\varnothing
]

表示不一致信息状态。

单点：

[
{x}
]

表示精确世界。

---

## 定义 505.2（目标答案集）

对目标：

[
T:X\to Y,
]

定义：

[
\boxed{
\operatorname{Ans}_T(S)
=======================

{T(x)\mid x\in S}.
}
]

---

## 定理 505.1（信息精化缩小答案集）

若：

[
S\sqsubseteq S',
]

即：

[
S'\subseteq S,
]

则：

[
\boxed{
\operatorname{Ans}_T(S')
\subseteq
\operatorname{Ans}_T(S).
}
]

更多信息不能增加仍可能的答案。

---

# 506. 目标知识是非空单点答案

## 定义 506.1（信息状态中的知识）

称 (S) 知道目标 (T)，当：

[
\boxed{
S\neq\varnothing
}
]

且：

[
\boxed{
|\operatorname{Ans}_T(S)|=1.
}
]

空集被明确排除，以避免虚假全知。

---

## 定理 506.1（知识沿一致 refinement 单调）

若：

[
S'\subseteq S,
]

[
S'\neq\varnothing,
]

且 (S) 知道 (T)，则 (S') 也知道同一个目标值。

### 证明

若：

[
\operatorname{Ans}_T(S)={y},
]

则：

[
\operatorname{Ans}_T(S')
\subseteq{y}.
]

因为 (S'\neq\varnothing)，其答案集非空，所以也恰为 ({y})。

(\square)

这统一了：

* 纤维知识；
* 公告更新；
* 证据 refinement；
* 安全拒答。

---

# 507. 单调删除式学习在有限世界中必然稳定

设更新算子：

[
U:\mathcal P(X)\to\mathcal P(X)
]

满足：

[
\boxed{
U(S)\subseteq S.
}
]

即每次更新只删除不再可能的世界。

从：

[
S_0
]

开始：

[
S_{n+1}=U(S_n).
]

## 定理 507.1（有限稳定）

若 (X) 有限，则序列最终稳定：

[
\boxed{
S_N=S_{N+1}=S_{N+2}=\cdots.
}
]

严格变化次数至多：

[
|S_0|.
]

因为每次严格更新至少删除一个状态。

---

## 边界

理论 revision 可能重新加入世界：

[
U(S)\not\subseteq S.
]

此时不再是纯学习，而是模型重构。

所以必须区分：

[
\boxed{
\begin{aligned}
\text{learning}
&=\text{缩小当前可能域};\
\text{revision}
&=\text{允许重新扩张或重排可能域}.
\end{aligned}
}
]

---

# Part LXXXIII：因果抽象、干预交换与跨层控制

# 508. 精确因果抽象要求所有干预方格交换

设微观状态：

[
X.
]

宏观状态：

[
Z.
]

抽象概念：

[
C:X\to Z.
]

微观干预：

[
F_u:X\to X.
]

宏观干预：

[
G_u:Z\to Z.
]

## 定义 508.1（精确因果抽象）

若对每个允许干预 (u)：

[
\boxed{
C\circ F_u
==========

G_u\circ C,
}
]

则 (C) 是该干预族的精确因果抽象。

这比被动观察闭合更强。

它要求：

> 微观世界先接受干预再抽象，与先抽象再进行宏观干预，得到相同宏观结果。

---

# 509. 精确因果抽象保持任意有限干预序列

设行动序列：

[
\alpha=(u_1,\ldots,u_n).
]

定义：

[
F_\alpha
========

F_{u_n}\cdots F_{u_1},
]

[
G_\alpha
========

G_{u_n}\cdots G_{u_1}.
]

## 定理 509.1（序列交换）

若每个单步方格交换，则：

[
\boxed{
C\circ F_\alpha
===============

G_\alpha\circ C.
}
]

### 证明

对序列长度归纳。

长度 (0) 为恒等。

若对 (\alpha) 成立，则：

[
\begin{aligned}
C F_uF_\alpha
&=
G_uCF_\alpha\
&=
G_uG_\alpha C.
\end{aligned}
]

(\square)

因此精确单步因果抽象自动保存全部有限实验路径。

---

# 510. 干预 carry 阻碍宏观因果闭合

对干预 (u)，定义：

[
\boxed{
\operatorname{ICarry}_u(C)
==========================

\left{
(x,y)
;\middle|;
C(x)=C(y),
\quad
C(F_ux)\neq C(F_uy)
\right}.
}
]

## 定理 510.1

若存在宏观干预：

[
G_u
]

使：

[
CF_u=G_uC,
]

则：

[
\operatorname{ICarry}_u(C)=\varnothing.
]

反之，在有限有效像模型中，如果 (\operatorname{ICarry}_u(C)) 为空，则存在唯一有效像上的宏观干预 (G_u)。

所以：

[
\boxed{
\text{干预 carry}
===============

\text{宏观因果模型不存在的显式见证}.
}
]

---

# 511. 被动预测闭合不推出因果抽象

令：

[
X={a,b,c}.
]

定义宏观概念：

[
C(a)=C(b)=0,
\qquad
C(c)=1.
]

被动过程为恒等：

[
F_{\mathrm{pass}}=\operatorname{id}.
]

因此被动宏观动力闭合：

[
C F_{\mathrm{pass}}
===================

\operatorname{id} C.
]

现在加入干预 (u)：

[
F_u(a)=a,
]

[
F_u(b)=c,
]

[
F_u(c)=c.
]

则：

[
C(a)=C(b)=0,
]

但：

[
C(F_ua)=0,
\qquad
C(F_ub)=1.
]

所以：

[
\operatorname{ICarry}_u(C)\neq\varnothing.
]

## 结论 511.1

[
\boxed{
\text{被动时间序列在宏观层闭合}
\not\Rightarrow
\text{宏观层支持正确干预推理}.
}
]

一个概念可以很好地预测自然演化，却无法支持行动后的反事实预测。

---

# 512. 动态完成是最小因果抽象 refinement

设允许干预生成幺半群 (M)。

定义：

[
\boxed{
\operatorname{Dyn}_M(C)(x)
==========================

\bigl(
C(F_mx)
\bigr)_{m\in M}.
}
]

即状态在所有允许干预后的完整宏观轮廓。

## 定理 512.1（因果闭合）

每个 (F_u) 都在 (\operatorname{Dyn}_M(C)) 上下降。

宏观更新通过右移行动索引实现：

[
\overline F_u(\phi)(m)
======================

\phi(mu).
]

---

## 定理 512.2（最小性）

若概念 (D) 满足：

[
C\preceq D
]

且所有干预 (F_u) 都在 (D) 上下降，则：

[
\boxed{
\operatorname{Dyn}_M(C)\preceq D.
}
]

### 证明要点

由 (D) 可以恢复 (C)。

又因为每个干预在 (D) 上闭合，所以由当前 (D)-值可以计算任意干预序列后的 (D)-值，进而恢复该时刻的 (C)-值。

因此完整干预轮廓由 (D) 决定。

(\square)

所以：

[
\boxed{
\operatorname{Dyn}_M(C)
=======================

\text{使全部干预精确下降的最小概念修复}.
}
]

---

# 513. 近似因果抽象的误差沿干预链累积

设宏观空间有度量 (d)。

对每个干预 (u)，定义单步缺陷：

[
\boxed{
\epsilon_u
==========

\sup_x
d
\left(
C(F_ux),
G_u(Cx)
\right).
}
]

假设 (G_u) 的 Lipschitz 常数为 (L_u)。

对序列：

[
\alpha=(u_1,\ldots,u_n),
]

有：

[
\boxed{
\begin{aligned}
\epsilon_\alpha
\le{}&
\epsilon_{u_n}
+
L_{u_n}\epsilon_{u_{n-1}}\
&+
L_{u_n}L_{u_{n-1}}\epsilon_{u_{n-2}}
+\cdots\
&+
\left(
\prod_{j=2}^{n}L_{u_j}
\right)
\epsilon_{u_1}.
\end{aligned}
}
]

### 两步证明

[
\begin{aligned}
&d
\left(
CF_vF_ux,
G_vG_uCx
\right)\
\le{}&
d
\left(
CF_vF_ux,
G_vCF_ux
\right)\
&+
d
\left(
G_vCF_ux,
G_vG_uCx
\right)\
\le{}&
\epsilon_v
+
L_v\epsilon_u.
\end{aligned}
]

递归展开即得。

因此：

[
\boxed{
\text{单步误差很小}
\not\Rightarrow
\text{长时干预误差很小}.
}
]

还要审计宏观动力是否放大缺陷。

---

# 514. 精确因果抽象推出有限时域决策充分

设行动集合 (U) 相同。

微观过程：

[
F_u:X\to X.
]

宏观过程：

[
G_u:Z\to Z.
]

满足：

[
CF_u=G_uC.
]

单步奖励满足：

[
\boxed{
r(x,u)
======

\overline r(Cx,u).
}
]

终端价值满足：

[
\boxed{
q(x)
====

\overline q(Cx).
}
]

定义微观有限时域价值：

[
V_0(x)=q(x),
]

[
\boxed{
V_{n+1}(x)
==========

\max_{u\in U}
\left[
r(x,u)+V_n(F_ux)
\right].
}
]

定义宏观价值：

[
\overline V_0(z)=\overline q(z),
]

[
\boxed{
\overline V_{n+1}(z)
====================

\max_{u\in U}
\left[
\overline r(z,u)
+
\overline V_n(G_uz)
\right].
}
]

## 定理 514.1（价值因子化）

对所有 (n)：

[
\boxed{
V_n
===

\overline V_n\circ C.
}
]

### 证明

对 (n) 归纳。

初始情形由终端价值因子化。

假设：

[
V_n=\overline V_nC.
]

则：

[
\begin{aligned}
V_{n+1}(x)
&=
\max_u
\left[
\overline r(Cx,u)
+
\overline V_n(CF_ux)
\right]\
&=
\max_u
\left[
\overline r(Cx,u)
+
\overline V_n(G_uCx)
\right]\
&=
\overline V_{n+1}(Cx).
\end{aligned}
]

(\square)

---

## 推论 514.2（最优行动概念下降）

有限时域最优行动集合只依赖：

[
C(x).
]

因此精确因果抽象不只保存预测，还保存相应奖励 doctrine 下的最优决策。

---

# Part LXXXIV：控制前驱、可达权利与最大安全自由

# 515. 可控前驱是行动版最弱前置条件

设每个状态 (x) 有可用行动：

[
U(x).
]

行动 (u) 产生非空后继集合：

[
R_u(x)\subseteq X.
]

对目标集合 (S\subseteq X)，定义：

[
\boxed{
\operatorname{CPre}(S)
======================

\left{
x
;\middle|;
\exists u\in U(x),
\quad
R_u(x)\subseteq S
\right}.
}
]

它表示：

> 主体存在一个行动，能够保证下一步进入 (S)。

这不是普通存在可达：

[
\exists u,\exists y\in R_u(x)\cap S.
]

而是控制意义上的保证。

---

# 516. 强制到达目标的区域是最小固定点

设目标集合：

[
G\subseteq X.
]

定义：

[
W_0=G,
]

[
\boxed{
W_{n+1}
=

W_n\cup\operatorname{CPre}(W_n).
}
]

## 定理 516.1（有限步可强制到达）

(x\in W_n) 当且仅当主体存在策略，能够保证在至多 (n) 步内到达 (G)。

### 证明

对 (n) 归纳。

(n=0) 时恰为 (x\in G)。

若 (x\in\operatorname{CPre}(W_n))，存在行动使所有后继进入 (W_n)，再由归纳假设至多 (n) 步到达目标。

反向同理分析策略第一步。

(\square)

---

## 定义 516.1（控制可达域）

[
\boxed{
W^*
===

# \bigcup_{n\ge0}W_n

\mu S.,
\left(
G\cup\operatorname{CPre}(S)
\right).
}
]

(W^*) 是能够保证有限步到达目标的全部状态。

---

## 定义 516.2（最小保证步数）

[
\boxed{
d_G(x)
======

\min{n\mid x\in W_n}.
}
]

它是目标相对的控制距离。

---

# 517. 无限安全区域是一个最大固定点

设安全状态集合：

[
S\subseteq X.
]

定义下降序列：

[
K_0=S,
]

[
\boxed{
K_{n+1}
=

S\cap\operatorname{CPre}(K_n).
}
]

有限模型中该序列最终稳定为：

[
K^*.
]

## 定理 517.1（最大安全可控域）

[
\boxed{
K^*
===

\nu K.,
\left(
S\cap\operatorname{CPre}(K)
\right).
}
]

其中每个状态都存在一个行动，使所有后继仍留在 (K^*)。

所以从 (K^*) 出发，主体可以永远保持安全。

而任何能无限保持安全的状态，都必须属于 (K^*)。

---

## 归纳与余归纳的统一

[
\boxed{
\begin{aligned}
W^*
&=\mu\text{-固定点}
&&\text{有限时间达到目标};\
K^*
&=\nu\text{-固定点}
&&\text{无限时间保持安全}.
\end{aligned}
}
]

积极目标通常是最小固定点问题。

持续安全通常是最大固定点问题。

---

# 518. 最大许可安全控制器保留最多自治空间

对：

[
x\in K^*,
]

定义安全行动集合：

[
\boxed{
U_{\mathrm{safe}}(x)
====================

\left{
u\in U(x)
;\middle|;
R_u(x)\subseteq K^*
\right}.
}
]

由 (K^*) 的定义：

[
U_{\mathrm{safe}}(x)\neq\varnothing.
]

## 定理 518.1（安全保持）

任何策略：

[
\pi(x)\in U_{\mathrm{safe}}(x)
]

都会使系统永远留在 (K^*\subseteq S)。

---

## 定义 518.1（最大许可性）

不直接为主体选定唯一安全行动，而是允许全部：

[
U_{\mathrm{safe}}(x).
]

因此：

[
\boxed{
\text{最大许可安全治理}
===============

\text{删除全部会失去长期安全性的行动，
保留其余全部选择}.
}
]

这比单一强制策略保留更多自治空间。

---

# 519. 消极权利与积极权利对应两个不同固定点

## 消极权利

要求主体永远不进入侵害集合：

[
B.
]

安全集合：

[
S=X\setminus B.
]

权利可保障域为：

[
\boxed{
K^*_{\mathrm{right}}
====================

\nu K.,
\left(
S\cap\operatorname{CPre}(K)
\right).
}
]

---

## 积极权利

要求主体能够保证达到目标：

[
G.
]

权利可实现域为：

[
\boxed{
W^*_{\mathrm{right}}
====================

\mu W.,
\left(
G\cup\operatorname{CPre}(W)
\right).
}
]

所以：

[
\boxed{
\begin{aligned}
\text{消极权利}
&=\text{存在持续避开侵害的策略};\
\text{积极权利}
&=\text{存在保证到达目标的策略}.
\end{aligned}
}
]

二者不是同一个许可谓词的正反面。

---

# 520. 反事实解释只有配备控制证书才成为可执行补救

设实际状态：

[
x.
]

目标：

[
G.
]

一个比较状态：

[
x'\in G
]

只是说明目标状态存在。

## 定义 520.1（补救证书）

一个补救证书包括：

[
\boxed{
(u_1,\ldots,u_n)
}
]

以及证明：

1. 每一步行动可用；
2. 所有非确定后继仍在下一层 winning region；
3. 中间状态满足准入；
4. 最终状态进入 (G)。

等价地：

[
x\in W_n.
]

---

## 定理 520.1

如果：

[
x\notin W^*,
]

则不存在能够保证到达 (G) 的行动补救。

即使存在某个：

[
x'\in G,
]

也不构成主体可执行方案。

因此：

[
\boxed{
\text{反事实比较}
+
\text{行动序列}
+
\text{保证证明}
===========

\text{真正补救}.
}
]

---

# Part LXXXV：随机目标、预测分布与决策统计

# 521. 随机目标的本质是条件分布，而不是单个结果

设状态空间为有限集合 (X)。

未来目标为随机变量 (Y)，其条件分布由概率核：

[
\boxed{
K:X\to\Delta(Y)
}
]

给出：

[
K(x)(y)
=

\Pr(Y=y\mid X=x).
]

## 定义 521.1（随机预测充分）

概念：

[
C:X\to B_C
]

对 (Y) 充分，当存在：

[
\overline K:B_C\to\Delta(Y)
]

使：

[
\boxed{
K=\overline K\circ C.
}
]

即同一概念值下，未来目标的完整条件分布相同。

---

## 定理 521.1（随机预测本质）

目标概念：

[
\boxed{
E_K=(\Delta(Y),K)
}
]

是所有随机预测充分概念中的最粗者。

任何充分概念 (C) 都满足：

[
\boxed{
E_K\preceq C.
}
]

所以随机系统中的本质不是“未来会发生什么”，而是：

[
\boxed{
\text{全部未来结果的条件概率轮廓}.
}
]

---

# 522. 随机充分性等价于条件独立

给定先验：

[
\mu(x)>0
]

以及联合分布：

[
\Pr(X=x,Y=y)
============

\mu(x)K(x)(y).
]

设：

[
C=C(X)
]

是状态的确定函数。

## 定理 522.1（有限正支持情形）

以下等价：

[
\boxed{
K=\overline K\circ C
}
]

与：

[
\boxed{
Y\perp X\mid C.
}
]

### 证明

若 (K) 通过 (C) 因子化，则：

[
\Pr(Y=y\mid X=x,C=c)
====================

# K(x)(y)

\overline K(c)(y),
]

只依赖 (c)，所以条件独立。

反之，若条件独立，则：

[
\Pr(Y=y\mid X=x)
================

\Pr(Y=y\mid C=C(x)).
]

定义：

[
\overline K(c)
==============

\mathcal L(Y\mid C=c).
]

于是：

[
K(x)=\overline K(Cx).
]

(\square)

---

## 边界

若某些状态先验概率为零，条件独立只给出几乎处处因子化。

结构充分性还要求零概率状态也满足同一条件分布。

因此仍需区分：

[
\boxed{
\text{almost-sure sufficiency}
\neq
\text{full-domain structural sufficiency}.
}
]

---

# 523. 条件互信息测量剩余预测余量

设概念 (C=f(X))。

## 定义 523.1（剩余预测信息）

[
\boxed{
I(Y;X\mid C).
}
]

它测量：

> 已知概念 (C) 后，完整状态 (X) 仍能为目标 (Y) 提供多少额外信息。

## 定理 523.1

在有限概率模型中：

[
\boxed{
I(Y;X\mid C)=0
}
]

当且仅当：

[
Y\perp X\mid C.
]

所以零条件互信息正是几乎处处随机预测充分。

---

## 加入新概念 (D)

新增预测信息为：

[
\boxed{
I(Y;D\mid C).
}
]

剩余信息变为：

[
I(Y;X\mid C,D).
]

链式分解：

[
\boxed{
I(Y;X\mid C)
============

I(Y;D\mid C)
+
I(Y;X\mid C,D)
}
]

在 (D) 为 (X) 的函数时成立，因为给定 (X) 后 (D) 不再增加信息。

所以：

[
\boxed{
\text{新增概念对预测的价值}
=================

\text{它从原剩余预测余量中解释掉的部分}.
}
]

---

# 524. 随机预测完成

定义：

[
\boxed{
\operatorname{StochComp}_Y(C)
=============================

C\vee E_K.
}
]

它同时记录：

* 原概念值；
* 目标条件分布。

## 定理 524.1

[
\operatorname{StochComp}_Y(C)
]

对 (Y) 随机预测充分。

并且任何同时精化 (C)、又对 (Y) 充分的概念 (D)，都满足：

[
\boxed{
\operatorname{StochComp}_Y(C)
\preceq D.
}
]

因此它是随机目标的最小保守完成。

---

## 注意

若 (K) 已经通过 (C) 因子化，则：

[
\operatorname{StochComp}*Y(C)
\simeq*{\mathrm{con}}
C.
]

这时把预测分布缓存进状态不增加语义信息，但可能降低实时计算成本。

---

# 525. 决策充分性可以严格粗于随机预测充分性

设行动集合：

[
A.
]

损失函数：

[
\ell:A\times Y\to\mathbb R.
]

对状态 (x)，定义每个行动的条件期望损失：

[
\boxed{
L_K(x)(a)
=========

\mathbb E_{Y\sim K(x)}
[\ell(a,Y)].
}
]

定义最优行动集合：

[
\boxed{
A^*(x)
======

\operatorname{argmin}_{a\in A}
L_K(x)(a).
}
]

## 定义 525.1（决策充分概念）

概念 (C) 对该损失问题充分，当：

[
\boxed{
E_{A^*}\preceq C.
}
]

更强地，如果完整期望损失向量通过 (C) 因子化：

[
\boxed{
E_{L_K}\preceq C,
}
]

则所有行动比较都能由 (C) 完成。

---

## 定理 525.1（预测充分推出决策充分）

若：

[
E_K\preceq C,
]

则：

[
E_{L_K}\preceq C,
]

进而：

[
E_{A^*}\preceq C.
]

### 证明

条件分布 (K(x)) 决定所有：

[
\mathbb E_{K(x)}[\ell(a,Y)].
]

所以期望损失向量是 (K) 的函数。

最优行动集合又是期望损失向量的函数。

由因子化传递即得。

(\square)

反向一般不成立。

多个不同未来分布可以对指定损失函数产生相同最优行动。

所以：

[
\boxed{
\text{正确行动所需的信息}
\preceq
\text{完整预测分布所需的信息}.
}
]

---

# 526. 损失族决定决策本质的精细度

设有一族决策问题：

[
\mathcal L
==========

{\ell_j}_{j\in J}.
]

定义联合期望损失轮廓：

[
\boxed{
D_{\mathcal L}(x)
=================

\left(
\mathbb E_{K(x)}[\ell_j(a,Y)]
\right)_{j,a}.
}
]

其规范决策本质为：

[
\boxed{
E_{D_{\mathcal L}}.
}
]

目标损失族越丰富，该概念通常越精细。

---

## 极限情形

如果 (Y) 有限，并且损失族包含每个结果指标：

[
\ell_y(Y)
=========

\mathbf 1_{{Y=y}},
]

则：

[
\mathbb E[\ell_y(Y)\mid x]
==========================

K(x)(y).
]

全部指标联合恢复完整条件分布。

因此：

[
\boxed{
E_{D_{\mathcal L}}
\simeq
E_K.
}
]

所以完整概率本质可以理解为：

[
\boxed{
\text{对全部可能结果敏感的决策问题族的共同最小充分概念}.
}
]

---

# 527. 信息瓶颈是压缩与目标余量之间的 doctrine

设状态随机变量 (X)、目标 (Y)、设计概念 (C)。

概念压缩成本：

[
I(X;C).
]

剩余预测余量：

[
I(Y;X\mid C).
]

一种设计问题是：

[
\boxed{
\min_C I(X;C)
\quad
\text{s.t.}
\quad
I(Y;X\mid C)\le\varepsilon.
}
]

或者：

[
\boxed{
\min_C
\left[
I(X;C)
+
\beta I(Y;X\mid C)
\right].
}
]

---

## 哲学解释

第一项惩罚：

* 记忆；
* 复杂度；
* 隐私；
* 表示成本；
* 政策能力。

第二项惩罚：

* 目标盲度；
* 预测损失；
* 决策错误。

所以信息瓶颈不是“唯一正确概念”的定理，而是一种明确的工程—规范 doctrine：

[
\boxed{
\text{以多少世界区别换取多少目标充分性。}
}
]

不同：

[
\beta,
\qquad
\varepsilon
]

会产生不同 Pareto 最优概念。

---

# 528. 概念缺陷可以用纤维内部的成对分歧概率测量

设：

[
X\sim\mu.
]

给定概念 (C)。

条件于：

[
C(X)=b,
]

独立抽取两个状态：

[
X_b,
\qquad
X'_b.
]

定义目标：

[
T:X\to Y.
]

## 定义 528.1（条件逻辑杂质）

[
\boxed{
\operatorname{Imp}_\mu(C;T)
===========================

\Pr
\left[
T(X)\neq T(X')
\right],
}
]

其中 (X,X') 在给定同一 (C)-值后条件独立同分布。

展开为：

[
\boxed{
\operatorname{Imp}_\mu(C;T)
===========================

\sum_b
\Pr(C=b)
\left[
1-
\sum_t
\Pr(T=t\mid C=b)^2
\right].
}
]

---

## 定理 528.1（零杂质判据）

[
\operatorname{Imp}_\mu(C;T)=0
]

当且仅当对每个正概率概念纤维，(T) 几乎处处为常值。

所以它是目标相对概念不足的平均成对版本。

---

## 定理 528.2（精化降低杂质）

若：

[
C\preceq D,
]

则：

[
\boxed{
\operatorname{Imp}*\mu(D;T)
\le
\operatorname{Imp}*\mu(C;T).
}
]

### 证明要点

对每个粗纤维，目标分布是其细纤维目标分布的混合。

函数：

[
G(p)=1-\sum_t p_t^2
]

是凹函数。

所以粗分布的杂质不小于细分后杂质的加权平均。

(\square)

因此：

[
\boxed{
\text{概念 refinement 单调减少纤维内部的平均目标冲突。}
}
]

---

# Part LXXXVI：第十三层统一

# 529. 程序逻辑、固定点、因果抽象与随机充分性共享同一个骨架

经过 §495–§528，形式概念动力学又出现了四个新的统一层。

## 529.1 前置条件层

[
\boxed{
\operatorname{sp}_F
\dashv
\operatorname{wp}_F.
}
]

从前提向前计算后果，与从目标向后计算所需条件，形成同一个伴随。

---

## 529.2 固定点层

[
\boxed{
\begin{aligned}
\mu\Phi
&=\text{有限生成、可达、积极实现};\
\nu\Phi
&=\text{持续闭合、安全、不变量}.
\end{aligned}
}
]

递归定义必须说明采用归纳还是余归纳语义。

---

## 529.3 因果抽象层

[
\boxed{
CF_u=G_uC
}
]

要求干预在微观和宏观之间自然交换。

被动预测充分不等于干预充分。

动态完成是全部干预闭合的最小概念。

---

## 529.4 控制层

[
\boxed{
\begin{aligned}
\mu W.,(G\cup\operatorname{CPre}(W))
&=\text{能够保证达到目标的区域};\
\nu K.,(S\cap\operatorname{CPre}(K))
&=\text{能够永远保持安全的区域}.
\end{aligned}
}
]

积极权利和消极权利因此分别落在最小固定点与最大固定点上。

---

## 529.5 随机充分层

[
\boxed{
K:X\to\Delta(Y)
}
]

是完整预测分布概念。

条件互信息：

[
I(Y;X\mid C)
]

测量概念之后仍剩余的预测信息。

决策本质可以严格粗于完整概率本质。

---

# 530. 当前最深层的新结论

本轮最承重的结论可以压缩为九条。

第一，**一个行动是否能达到目标，必须通过最弱前置条件审计，而不是只展示一个成功后继。**

第二，**可能成功与保证成功属于存在量词和全称量词两种不同过程逻辑。**

第三，**安全与到达分别是最大固定点和最小固定点问题；它们不是同一种“可行性”。**

第四，**自一致方程不产生唯一意义；递归概念必须声明最小、最大或其他固定点选择 doctrine。**

第五，**宏观模型是否真实因果，取决于干预方格是否交换，而不只取决于被动时间序列是否可预测。**

第六，**动态完成是当前概念在全部允许干预下的最小因果闭包。**

第七，**行动补救不是一个更好结果的比较状态，而是一条具有准入、控制和保证证明的可执行路径。**

第八，**随机世界中的预测本质是条件分布；正确决策所需概念可能远粗于完整分布概念。**

第九，也是最重要的一条：

[
\boxed{
\text{一个理论真正能够指导行动，
不仅要求目标在概念上可表达；
还要求目标前件可计算、过程可控、干预抽象正确、
安全不变量存在，并且随机余量已被明确地保留在条件分布中。}
}
]

因此，整套理论可以进一步写成：

[
\boxed{
\begin{aligned}
\textbf{Formal Concept Dynamics}
={}&
\textbf{a weakest-precondition logic of action}\
&+
\textbf{an inductive–coinductive semantics of recursive concepts}\
&+
\textbf{an intervention-commuting theory of causal abstraction}\
&+
\textbf{a fixed-point theory of reachability and safety}\
&+
\textbf{a stochastic theory of predictive and decision sufficiency}\
&+
\textbf{a quantitative theory of residual fiber impurity}.
\end{aligned}
}
]

最凝练的一句是：

[
\boxed{
\text{知道世界怎样分类，只解决了“它是什么”；
知道最弱前件、控制固定点和干预交换，才开始解决
“从这里能够保证做到什么、永远避免什么，
以及这些行动结论在随机和跨尺度世界中是否仍然真实”。}
]


---

# 531. 语义 holonomy 与分类核的边界

## 定义 531.1（分类核与闭环后的读出）

设 \(C:X\to B\) 为概念读出，\(H:B\to B\) 为标签空间上的闭环 transport。定义

\[
\ker C=\{(x,y)\in X\times X:C(x)=C(y)\},
\qquad C^H=H\circ C.
\]

## 定理 531.1（单射 transport 保持分类核）

若 \(H\) 为单射，则

\[
\boxed{\ker C^H=\ker C.}
\]

**证明。** 对任意 \(x,y\in X\)，由 \(H\) 的单射性及函数保持等式，

\[
H(C(x))=H(C(y))\iff C(x)=C(y).
\]

因此两个关系逐点相同。\(\square\)

## 命题 531.2（非平凡 holonomy 不蕴含区分能力改变）

在定义 7.2 的概念等价意义下，第 95 节的条件 \(H\ne\operatorname{id}\) 不足以推出 \(C^H\) 与 \(C\) 具有不同的分类核或区分能力。具体地，取

\[
X=B=\mathbf2=\{0,1\},\qquad C(b)=b,\qquad H(b)=1-b.
\]

则

\[
\boxed{
H\ne\operatorname{id},\qquad
C^H\ne C,\qquad
\ker C^H=\ker C,\qquad
C^H\simeq_{\mathrm{con}}C.
}
\]

**证明。** \(H(0)=1\ne0\)，故前两个不等式成立。对 \(b\in\mathbf2\)，有 \(H(H(b))=1-(1-b)=b\)，所以 \(H\) 为双射；定理 531.1 给出分类核相等。又

\[
C^H=H\circ C,\qquad C=H\circ C^H,
\]

两向因子化给出定义 7.2 的概念等价。\(\square\)

该反例中的标签读出确实改变，而无标签区分能力相同。因此第 95 节的 transport 历史与分类核是不同数据：若“区分结构”包含指定标签、基点或 transport 历史，这些额外数据必须作为结构的一部分保留，不能仅由分类核表示。对于任意双射 \(g:B\to B'\)，仍有

\[
gHg^{-1}=\operatorname{id}_{B'}\iff H=\operatorname{id}_B,
\]

因为分别在等式两侧复合 \(g^{-1},g\) 或 \(g,g^{-1}\) 即得另一方向；非平凡 holonomy 在重命名下保持非平凡，与上述分类核相等相容。

## 532. 情境受限的概念修复：覆盖扩张、统一充分性与最粗性

### 定义 532.1（覆盖域、固定任务与目标残差）

设 $\Omega$ 为有限对象全集，$\varnothing\ne A\subseteq\Omega$ 为本次分类的覆盖域，给定情境、分类读数与任务目标

$$
c:A\to K,\qquad q:A\to L,\qquad T:A\to Y,\qquad K=c(A).
$$

域外遗漏是 $\Omega\setminus A$；域内目标残差是

$$
\Delta_A(q,T)=\{(x,y)\in A^2:q(x)=q(y),\ T(x)\ne T(y)\}.
$$

目标 $T$ 的选择属于任务数据。比较覆盖域 $A_0\subseteq A_1$ 时，若称目标固定，意指先在 $A_1$ 给定同一个 $T$，再取其在 $A_0$ 上的限制；$q,c$ 同理。另换目标、成功关系或其版本属于任务变更，不能用新任务的成功消去旧 $\Delta_A(q,T)$。域外遗漏与域内残差可同时非空；它们与任务变更不是互斥事件。

若标签还负有适用含义，另给关系 $\Phi\subseteq\Omega\times L$。称 $q$ 在 $A$ 上忠实，当且仅当 $\Phi(x,q(x))$ 对每个 $x\in A$ 成立；忠实完整覆盖还要求 $A=\Omega$。适用域为 $D_\Phi=\{x\in\Omega:\exists\ell\in L,\ \Phi(x,\ell)\}$，故忠实读数要求 $A\subseteq D_\Phi$。关系 $\Phi$、覆盖域 $A$ 与目标 $T$ 是不同输入。

### 定义 532.2（只读情境的修复与两个核）

允许的辅助读数为 $z\circ c$，其中 $z:K\to Z$，$Z$ 可为任意标签集；运行时 $z$ 只读取情境。记

$$
Q_z(x)=(q(x),z(c(x))),\qquad
\Gamma_c=\{Q_z:z:K\to Z,\ Z\text{ 任意}\}.
$$

选择 $z$ 可以使用事先声明的任务及支撑资料；这不把任意状态标签或 $T(x)$ 自动变成运行时可读信息。称 $Q_z$ 对 $T$ 充分，是指存在仅定义在实际像上的恢复器

$$
r_z:Q_z(A)\to Y,\qquad r_z(Q_z(x))=T(x)\quad(x\in A).
$$

辅助编码的情境核与完整读数的实际观察核分别为

$$
E_z=\{(k,k')\in K^2:z(k)=z(k')\},\qquad
\ker_A Q_z=\{(x,y)\in A^2:Q_z(x)=Q_z(y)\}.
$$

它们定义在不同集合上，且满足

$$
(x,y)\in\ker_A Q_z
\iff q(x)=q(y)\ \land\ (c(x),c(y))\in E_z.
$$

对 $K$ 上任意等价关系 $E$，令 $Q_E(x)=(q(x),[c(x)]_E)$。任意 $Q_z$ 与 $Q_{E_z}$ 在实际像上互相重命名，因而具有同一观察核；反之，每个 $E$ 都由商映射 $z(k)=[k]_E$ 实现。因此允许修复可用情境等价关系参数化，但不同 $E$ 未必给出不同观察核。

沿用定义 7.2 的概念等价，以实际像为值域时，两个读数概念等价当且仅当观察核相同；称 $Q$ 比 $Q'$ 粗，当且仅当 $\ker_A Q'\subseteq\ker_A Q$。所用核与因子化的对应见本卷第 7 节及[概念核序对偶中的实际像判据](../../../D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality.lean)。称 $Q_\circ\in\Gamma_c$ 为最粗充分修复，要求它充分，且

$$
\forall Q_z\in\Gamma_c,\qquad
Q_z\text{ 充分}\ \Longrightarrow
\ker_A Q_z\subseteq\ker_A Q_\circ.
$$

这是充分修复族中最大的观察核，不只是一个无法继续粗化的极大核。最小辅助标签数则是另一个量：

$$
m_A=\min\{|z(K)|:Q_z\in\Gamma_c\text{ 对 }T\text{ 充分}\}.
$$

这里计数实际使用的辅助标签，不计未使用的 $Z$ 中元素，也不计完整读数 $Q_z(A)$ 的大小。

### 假设 532.3（各情境对同一目标的局部充分性）

假定

$$
\forall x,y\in A,\qquad
c(x)=c(y)\ \land\ q(x)=q(y)\ \Longrightarrow\ T(x)=T(y).
$$

在此假设下定义情境相容关系

$$
R(k,k')\iff
\forall x,y\in A,\quad
\bigl(c(x)=k\ \land\ c(y)=k'\ \land\ q(x)=q(y)\bigr)
\Longrightarrow T(x)=T(y).
$$

局部充分性给出 $R(k,k)$；交换 $x,y$ 给出 $R(k,k')\iff R(k',k)$。若两个情境没有共同出现的 $q$ 值，它们在此定义下相容。商掉目标分歧的任意做法并非假设的一部分；各情境都使用同一个 $T$。取 $z=\operatorname{id}_K$ 即有充分修复，故定义 532.2 的最小值非空且有限。

### 假设 532.4（实际联合支撑中的共同锚）

定义实际联合支撑

$$
S_A=\{(c(x),q(x),T(x)):x\in A\}\subseteq K\times L\times Y.
$$

假定存在 $\ell_\star\in L$、$y_\star\in Y$，使

$$
K\times\{\ell_\star\}\times\{y_\star\}\subseteq S_A.
$$

亦即对每个 $k\in K$，存在实际对象 $a_k\in A$ 满足

$$
c(a_k)=k,\qquad q(a_k)=\ell_\star,\qquad T(a_k)=y_\star.
$$

此假设指向联合支撑中的对象，不能用 $K=c(A)$、$\ell_\star\in q(A)$、$y_\star\in T(A)$ 这三个边缘事实代替；也不假定全部笛卡尔组合都存在。

### 定理 532.5（共同锚桥与最粗实际修复的准确判据）

在定义 532.1—532.2 及假设 532.3—532.4 下，对 $K$ 上任意等价关系 $E,F$，有

$$
\ker_A Q_E\subseteq\ker_A Q_F\iff E\subseteq F.
$$

而且

$$
\Gamma_c\text{ 中存在最粗充分实际修复}
\iff R\text{ 传递}.
$$

存在时该修复唯一到概念等价为止，由 $Q_R$ 实现；每个最粗充分修复的情境核均为 $R$。唯一性不要求辅助标签的名称相同。

**证明。** 先把既有纤维准则用于本题的允许语言。对任意读数 $Q$，实际像上的恢复存在当且仅当 $T$ 在每个 $Q$ 纤维上恒定；这是[目标恢复准则](../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)的直接应用。具体对应为状态集 $A$、过程读数 $Q:A\to Q(A)$、目标 $T:A\to Y$；$A\ne\varnothing$ 满足该准则的非空前提。恢复值在实际像上由该纤维共同的 $T$ 值确定，不要求规定不存在的观察组合。将定义 532.2 展开，立即得到本证明所用的条件

$$
Q_E\text{ 对 }T\text{ 充分}\iff E\subseteq R. \tag{532.1}
$$

确实，若 $Q_E$ 充分，取 $kEk'$ 以及 $c(x)=k,c(y)=k',q(x)=q(y)$，便有 $Q_E(x)=Q_E(y)$，所以 $T(x)=T(y)$，即 $R(k,k')$。反之，若 $E\subseteq R$，同一 $Q_E$ 纤维中的任意两点满足相容关系的前件，因此目标相同。

若 $E\subseteq F$，定义直接给出 $\ker_A Q_E\subseteq\ker_A Q_F$。反过来，设观察核包含，并任取 $kEk'$。共同锚给出

$$
Q_E(a_k)=(\ell_\star,[k]_E)
=(\ell_\star,[k']_E)=Q_E(a_{k'}).
$$

核包含强迫 $Q_F(a_k)=Q_F(a_{k'})$，故 $kFk'$。这就证明了序反射。此步用到每一对情境中实际存在的共同 $q$ 值；共同的 $T$ 值还保证这些锚行本身不引入目标冲突。

若 $R$ 传递，则由假设 532.3 中的自反性、对称性，$R$ 是等价关系。式（532.1）说明 $Q_R$ 充分；任何充分 $Q_E$ 的 $E$ 都包含于 $R$，故其观察核包含于 $\ker_A Q_R$。于是 $Q_R$ 最粗。

反之，设最粗充分修复为 $Q_{E_\circ}$。任意充分 $Q_E$ 都满足 $\ker_A Q_E\subseteq\ker_A Q_{E_\circ}$；刚证明的序反射给出 $E\subseteq E_\circ$。对每个满足 $R(k,k')$ 的不同情境，取唯一非单点块为 $\{k,k'\}$、其他块均为单点的等价关系 $E^{k,k'}$。自反性、对称性和 $R(k,k')$ 保证 $E^{k,k'}\subseteq R$，故由式（532.1）它充分，进而 $E^{k,k'}\subseteq E_\circ$。对角对本就属于 $E_\circ$，因此 $R\subseteq E_\circ$。又 $Q_{E_\circ}$ 充分给出 $E_\circ\subseteq R$，所以 $R=E_\circ$，必传递。两个最粗修复的核互相包含，故概念等价；序反射再给出其情境核相同。证毕。

### 命题 532.6（同源覆盖扩张保持最小标签数而改变最粗实际修复的存在性）

令 $\Omega=A_1$ 为下表五个形式对象，$A_0=\{b_\star,a_u,c_u\}$。表在 $A_1$ 上一次性规定 $q,c,T$，在 $A_0$ 上只取限制；星号 $\star$ 与 $u$ 是不同的读数符号。

| 对象 $x$ | 情境 $c(x)$ | 读数 $q(x)$ | 目标 $T(x)$ | 属于 $A_0$ |
| --- | --- | --- | --- | --- |
| $a_\star$ | $a$ | $\star$ | $0$ | 否 |
| $b_\star$ | $b$ | $\star$ | $0$ | 是 |
| $c_\star$ | $c$ | $\star$ | $0$ | 否 |
| $a_u$ | $a$ | $u$ | $0$ | 是 |
| $c_u$ | $c$ | $u$ | $1$ | 是 |

两个域都有 $K=\{a,b,c\}$，满足局部充分性，且 $m_{A_0}=m_{A_1}=2$。在 $A_0$ 上，所有充分允许修复只有一个实际概念等价类，故存在最粗者；在 $A_1$ 上，不存在最粗充分允许修复。两域的相容关系相同且不传递。因此，固定目标的覆盖扩张能保持辅助字母表的最小成本，却改变允许修复族在实际信息序中有无最大核；情境分划本身的最粗性与实际观察的最粗性不能混同。

**证明。** 每个域中的每个 $(c,q)$ 组合至多有一行，故局部充分性成立。情境 $a,b$ 之间，在 $A_0$ 没有共同读数，在 $A_1$ 只有共同的 $\star$，且两行目标都为 $0$；故两域都有 $R(a,b)$。同理两域都有 $R(b,c)$。而 $a_u,c_u$ 具有相同读数 $u$ 和不同目标，故两域都不满足 $R(a,c)$。因此两域共同的相容关系为

$$
R=\operatorname{diag}_K\cup\{(a,b),(b,a),(b,c),(c,b)\},
$$

它不传递。在情境核层面，充分的等价关系恰为下列三个分划：

$$
E_1:\ \{a,b\}\mid\{c\},\qquad
E_2:\ \{a\}\mid\{b,c\},\qquad
E_3:\ \{a\}\mid\{b\}\mid\{c\}.
$$

这是因为 $a,c$ 必须分开，而 $b$ 只能加入其中一个块或自成一块。三个分划在两域均由相同情境编码实现。具体取

$$
\begin{aligned}
z_1(a)&=z_1(b)=0,&z_1(c)&=1,\\
z_2(a)&=0,&z_2(b)&=z_2(c)=1.
\end{aligned}
$$

对 $z_1$，星号行的实际读数为 $(\star,0)$ 或 $(\star,1)$，目标一律为 $0$；两条 $u$ 行分别读出 $(u,0),(u,1)$，目标分别为 $0,1$。所以恢复器可取 $r_1(\star,0)=r_1(\star,1)=r_1(u,0)=0$、$r_1(u,1)=1$，再限制到各域实际像。对 $z_2$，星号行仍全取目标 $0$，两条 $u$ 行仍读出 $(u,0),(u,1)$，故同一写法给出恢复器。两个编码在两域都充分并使用两个标签。任何一个标签的编码都把 $a_u,c_u$ 合并，不能恢复原目标，所以两域的最小标签数恰为 $2$。这里使用的是本卷第 122 节缺陷图着色方法在“只能按情境赋标签”下的应用：冲突的情境端点必须异色；不把第 83 节允许任意状态辅助标签的公式直接当成本题公式。零误差辅助信息与着色问题的原始文献见 H. S. Witsenhausen, *The zero-error side information problem and chromatic numbers*, IEEE Transactions on Information Theory 22(5), 592–593 (1976), [doi:10.1109/TIT.1976.1055607](https://doi.org/10.1109/TIT.1976.1055607)。

在 $A_0$ 上，任何充分修复都分开 $a_u,c_u$；唯一的星号行 $b_\star$ 由第一坐标 $q$ 与两条 $u$ 行分开。因此每个充分 $Q_z$ 的实际核都是 $\operatorname{diag}_{A_0}$，三个不同的情境核都给出同一个实际概念。$A_0$ 没有共同锚：情境 $b$ 只有星号读数，而 $a,c$ 只有 $u$ 读数。它直接表明，缺少共同锚时，从情境核没有最大充分者不能推出实际核也没有最大充分者。

在 $A_1$ 上，$a_\star,b_\star,c_\star$ 给出 $\ell_\star=\star,y_\star=0$ 的实际共同锚；定理 532.5 与 $R$ 非传递已推出无最粗者。还可直接检查完整观察核：$Q_{z_1}$ 合并 $a_\star,b_\star$ 而分开 $b_\star,c_\star$；$Q_{z_2}$ 合并 $b_\star,c_\star$ 而分开 $a_\star,b_\star$，故两核互不包含。若一个允许的 $Q_z$ 比两者都粗，前一合并强迫 $z(a)=z(b)$，后一合并强迫 $z(b)=z(c)$，于是 $z(a)=z(c)$。因此 $Q_z(a_u)=Q_z(c_u)$，而两行目标不同，$Q_z$ 不充分。

本卷第 130 节、定理 443.1 及[允许理由的 meet 准则](../../../D5/S3/ConceptDynamics/RefinementAlgebra/CanonicalAllowedReasonMeet.lean)在此只作为一般最粗性前置。具体地，按概念核序对偶，以上两核之并的等价闭包恰有三个块

$$
\{a_\star,b_\star,c_\star\},\qquad\{a_u\},\qquad\{c_u\}.
$$

这是抽象共同粗化 $(q,T)$ 的核，仍然充分；但上述冲突证明它不能由任何允许的 $Q_z$ 实现。因此本例所缺的是允许语言中的相应 meet 闭合，不能用不受取得限制的目标完成代替允许修复。

最后，新增对象恰为 $a_\star,c_\star$，目标值都是旧域已有的 $0$；旧行的 $q,c,T$ 无一改变，$T(A_0)=T(A_1)=\{0,1\}$。覆盖遗漏从这两个对象变为空集，且本例还有

$$
\Delta_{A_0}(q,T)=\Delta_{A_1}(q,T)
=\{(a_u,c_u),(c_u,a_u)\},
$$

其中将 $A_0^2$ 视为 $A_1^2$ 的子集。故连这个残差集合也保持不变，最粗实际修复的存在性仍改变。该表是有限形式构造，不承担任何现实人群分布的经验前提。证毕。

### 命题 532.7（同一构造中的固定目标修复与目标替换）

在命题 532.6 的任一域中，原读数 $q$ 对原目标 $T$ 不充分，而 $Q_{z_1},Q_{z_2}$ 在保持 $T$ 不变时充分。若改取常目标 $T_0(x)=0$，则原读数 $q$ 已充分，且仅需一个辅助标签；但原残差 $\Delta_A(q,T)$ 仍非空。在 $A_1$ 上，抽象读数 $(q,T)$ 对原目标充分，却没有与之概念等价的 $\Gamma_c$ 成员。

**证明。** 原 $q$ 合并 $a_u,c_u$，它们的原目标分别为 $0,1$，故不能由 $q$ 恢复；两个修复的恢复器已在命题 532.6 给出。换成 $T_0$ 后，恢复器 $r_0:q(A)\to\{0,1\}$ 可取常值 $0$，辅助编码也可取常值；因 $K\ne\varnothing$，一个标签就是最小值。但 $T(c_u)=1\ne0=T_0(c_u)$，任务在旧对象上已经改变，原残差的定义没有随之改写。

读数 $(q,T)$ 总可用第二投影恢复 $T$。然而，在 $A_1$ 上它把三条星号行合并；任何与其具有相同核的 $Q_z$ 必须使 $z(a)=z(b)=z(c)$，于是还合并两条 $u$ 行，矛盾。这是本卷第 219 节的无取得限制目标完成与本章情境受限语言之间的明确界线；亦对应第 444 节保持旧结果与更换结果的区别。

上述区别不蕴含“一切概念必有损”。作为同一恢复定义的边界，任何非空域上的恒等读数 $q=\operatorname{id}_A$ 都可用 $r=T$ 恢复任意指定目标；任意读数对于一个常目标都有常值恢复器。因此“信息逃逸”在本章中指指定域、读数及目标下残差非空，不能删去这些下标后断言普遍有损。证毕。

### 定义 532.8（概念相对性与性别相关应用的条件桥）

本章所谓概念的任务相对性，是给定 $(\Omega,A,\Phi,c,q,T,\Gamma_c)$ 后评价忠实覆盖、目标充分性与允许修复，而不把这三种判准当作概念名称自身的属性。固定 $A,T$ 后改变 $q$ 是改变任务读数；保持读数而更换 $T$ 是改变问题。允许取得哪些读数由 $\Gamma_c$ 指定，不能由“存在一个函数”的数学事实代替实际取得条件。

对性别相关的条件模型，分别给定明定的生理特征读数空间 $B$、社会性别关系或位置的读数空间 $G$、认同读数空间 $I$。以

$$
\Omega=X\subseteq B\times G\times I
$$

表示实际支持的组合，仅当这三项足以作为所考察对象的表示时采用这一建模桥；如任务还需个体历史或其他变量，须先把所需变量列入对象。三个坐标不假定相等、可互推、统计独立，也不假定 $X=B\times G\times I$。

对任一具体二标签读数 $q:A\to\{0,1\}$，其适用关系 $\Phi$ 单独给定；标签是否解释为生理判准、社会关系或认同，须在 $\Phi$ 与对应测量的定义中写明。所问任务另由 $T:A\to Y$ 指定，情境 $c$ 的含义及取得方式另给。$X,\Phi,q,c,T$ 与共同锚是否描述真实对象属于模型适用的前提，不由标签数或形式表格保证。命题 532.6 的五行对象未被指定为任何人群的这些坐标。

### 命题 532.9（条件桥下的覆盖、充分性与判准边界）

在定义 532.8 的一个已指定模型中，若存在实际对象 $x,y\in A$ 满足 $q(x)=q(y)$ 而 $T(x)\ne T(y)$，则该二标签读数对该任务不充分；若假设 532.3—532.4 也成立，则其情境受限修复由定理 532.5 判定。若另有 $w\in X$ 满足 $\Phi(w,0)$ 与 $\Phi(w,1)$ 均不成立，则该适用关系没有忠实的完整二标签覆盖，无论是否强制给每个对象赋一个标签。

这些条件分别检验实际同读数对的目标分歧与标签适用关系，不允许仅从“标签只有两个”推出任何具体人群中的失败，也不允许从强制总赋值推出忠实覆盖。对目标的这些条件判断本身不选择医学、社会或法律任务应采用哪个目标或适用标准。

**证明。** 第一个条件给出 $\Delta_A(q,T)$ 的元素，故任何恢复器都须把同一输入送到不同的两个目标值，不可能。加上局部充分性与共同锚时，定义 532.8 未改变定理 532.5 的对象、允许读数或量词，因此可直接应用该定理。对于第二个条件，任何 $\widetilde q:X\to\{0,1\}$ 在 $w$ 上只能取 $0$ 或 $1$，两种选择都不满足 $\Phi(w,\widetilde q(w))$，故总赋值不能修复适用域缺口。

反过来，两个标签本身没有提供同读数异目标的对象，也没有提供无适用标签的对象；例如常目标的恢复器对任意读数都存在，而取 $\Phi=X\times\{0,1\}$ 时任意总赋值都忠实。此处是数学边界模型，不是关于某个人群的经验断言。具体应用须分别给出上述见证或相应的全称充分性、忠实性证明。由于这些推导始终把 $T$ 与 $\Phi$ 作为输入，它们没有推出应以另一目标或适用关系替换该输入的规范结论。证毕。

## 追加锚（本行以下为增补区）

## 533. 共同焦点下固定操作的可识别族：正随机实现的完整分类

### 定义 533.1（共同焦点与关系角色的分别）

本章以“共同焦点”指若干不同关系所共同指向的参照，以“角色”指对象与该参照发生关系的方式；共享参照不在定义上把这些方式合并。此区别的历史参照为亚里士多德《形而上学》Γ.2：健康之物可以保存健康、产生健康、作为健康的征候或能够承受健康；医疗之物可以具有医术、天性适于医术或是医术的功能。他用这些区别说明“是”虽有多义，却都关联于一个起点，而非仅仅同名；其中有些是实体，有些是实体的属性、生成、毁灭、缺失等。他进一步主张，同一科学不仅研究具有一个共同概念的事物，也研究关联于同一共同本性的事物，故存在者之为存在者属于同一科学；科学主要研究其他事物所依赖并由之得名的首要者，因而哲学家须把握实体的原理与原因。这里的共同关联包含统一科学与实体优先的实质主张。引文据 Aristotle, *Metaphysics*, Γ.2，[W. D. Ross 英译](https://classics.mit.edu/Aristotle/metaphysics.4.iv.html)；关于 *pros hen*“关联于一”与实体的首要意义，参见 [*Aristotle’s Metaphysics*, §3](https://plato.stanford.edu/entries/aristotle-metaphysics/#RoleSubsStudBeinQuaBein)，实质修订于 2025-01-24。

以下把“共同参照是否足以决定不同关系之间的操作后果”限定为一个有限随机模型的问题。模型中的焦点状态集不是亚里士多德实体概念的定义；输入、焦点与输出的箭头也不由“健康”或“医疗”这些共同名称推出。保存、产生与征候的历史例子在这里不被赋予具体医学因果律。

### 定义 533.2（固定标签的双通道实现与共同数据）

固定有限带标签集合 $X,H,Y$，其大小分别为 $m,r,n$，其中 $m,n\ge r\ge2$；固定各集合的坐标顺序。记 $\mathbf1_d$ 为 $d$ 维全一列向量，$\Delta_d=\{u\in\mathbb R_{\ge0}^d:\mathbf1_d^Tu=1\}$。列随机矩阵指逐项非负且每列和为一的矩阵。固定严格正的概率列向量 $\mu\in\Delta_m$、$\pi\in\Delta_r$。

一个实现是矩阵对 $(P,S)$，满足

$$
\begin{gathered}
P\in\mathbb R_{>0}^{r\times m},\qquad
S\in\mathbb R_{>0}^{n\times r},\qquad
\operatorname{rank}P=\operatorname{rank}S=r,\\
\mathbf1_r^TP=\mathbf1_m^T,\qquad
\mathbf1_n^TS=\mathbf1_r^T,\qquad P\mu=\pi.
\end{gathered}
$$

同一实现的联合律与端点通道分别规定为

$$
\Pr(x,h,y)=\mu_xP_{hx}S_{yh},\qquad M=SP.
$$

因此 $P$ 是从 $X$ 到 $H$ 的条件通道，$S$ 是从 $H$ 到 $Y$ 的条件通道，$\pi$ 是操作插入前的焦点边缘。这个共同联合律同时给出两类关系的衔接，不从两个各自可实现的边缘关系拼出未经规定的共同实现。

设至少存在一个上述实现生成固定数据 $(M,\mu,\pi)$。其完整实现类定义为

$$
\mathcal F(M,\mu,\pi)=
\left\{(P',S'):
\begin{array}{l}
P'\in\mathbb R_{>0}^{r\times m},\quad
S'\in\mathbb R_{>0}^{n\times r},\\
\operatorname{rank}P'=\operatorname{rank}S'=r,\\
\mathbf1_r^TP'=\mathbf1_m^T,\quad
\mathbf1_n^TS'=\mathbf1_r^T,\\
S'P'=M,\quad P'\mu=\pi
\end{array}
\right\}.
$$

其中的 $X,H,Y,\mu,\pi,M$ 始终固定，不再加入已知零项、特定参数族或已知内部通道等限制。

### 假设 533.3（方向、插入操作与模块保持）

模型预先指定方向 $X\to H\to Y$ 及定义 533.2 的条件分解。一个允许的固定操作由列随机矩阵 $K\in\mathbb R_{\ge0}^{r\times r}$ 表示，$K_{h'h}$ 的含义是把操作前的固定标签 $h$ 送到操作后的固定标签 $h'$ 的概率。允许零项及重置操作，不要求 $K$ 严格正、可逆或预先满足 $K\pi=\pi$。

模块保持假设规定：插入 $K$ 后，两个通道仍为该实现原有的 $P,S$，扩展联合律和端点后果为

$$
\Pr_K(x,h,h',y)=\mu_xP_{hx}K_{h'h}S_{yh'},
\qquad Q_K(P,S)=SKP.
$$

每个竞争实现使用同一个 $K$、同一组焦点标签及同一操作含义。若某个可逆矩阵 $T$ 被用于比较分解，同步把 $K$ 改为 $TKT^{-1}$ 是另外的操作运输问题，不属于这里的固定操作比较。上述方向与模块保持是现代数学重构的假设，不是从共同焦点的名称或端点观察恢复出的因果事实；把此模型用于经验系统还须分别给出这些假设的依据。

### 定义 533.4（固定操作后果的识别）

称数据 $(M,\mu,\pi)$ 识别固定操作 $K$ 的端点后果，当且仅当 $Q_K$ 在全部 $\mathcal F(M,\mu,\pi)$ 上恒定。此处要求完整端点通道相同，因而同时决定每个输入标签的输出律；仅仅决定按 $\mu$ 平均的输出律是较弱目标。

这是本卷第 108 节的观察纤维准则在该实现空间上的用法；一般的目标识别与纤维包含关系亦见[查询族识别准则](../../../D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.lean)及[干预目标因子化准则](../../../D5/S3/ConceptDynamics/RefinementFactorization/InterventionTargetFactorization.lean)。这里的目标为固定 $K$ 的 $Q_K$，观察为 $(SP,P\mu)$，$\mu$ 和全部标签是固定参数。后果可识别不等于内部角色通道 $P,S$ 已被识别，也不赋予取得焦点读数、制造 $K$ 或执行 $K$ 的能力。

### 定理 533.5（共同焦点边缘下可识别固定操作的完整分类）

在定义 533.2 的非空完整实现类与假设 533.3 下，对任意固定列随机矩阵 $K$，下列两项等价：数据 $(M,\mu,\pi)$ 识别 $K$ 的端点后果；存在实数

$$
-\min_{1\le i\le r}\frac{\pi_i}{1-\pi_i}\ \le\ \alpha\ \le\ 1
$$

使

$$
K=\alpha I_r+(1-\alpha)\pi\mathbf1_r^T.
\tag{533.1}
$$

这样的 $\alpha$ 唯一，共同端点后果由数据直接恢复为

$$
Q_K=\alpha M+(1-\alpha)(M\mu)\mathbf1_m^T.
\tag{533.2}
$$

若 $K$ 不属式（533.1）的操作族，则每个 $(P,S)\in\mathcal F(M,\mu,\pi)$ 的任意邻域内都有共同数据相同、固定操作后果不同的竞争实现。因此，共同焦点边缘与完整端点观察决定的恰是这一整族操作后果；它们没有决定任意固定焦点操作的可迁移后果。式（533.1）在 $0\le\alpha\le1$ 时是恒等操作与重置到 $\pi$ 的凸混合，但完整范围还含负 $\alpha$；式（533.2）在负参数时仍是合法通道，因为它等于 $SKP$。

**证明。** 固定任一 $(P,S)\in\mathcal F(M,\mu,\pi)$。满秩使 $P:\mathbb R^m\to\mathbb R^r$ 满射、$S:\mathbb R^r\to\mathbb R^n$ 单射，故 $\operatorname{rank}M=r$。取左逆 $L\in\mathbb R^{r\times n}$ 与右逆 $R\in\mathbb R^{m\times r}$，使 $LS=I_r$、$PR=I_r$；它们仅用于代数消去，不要求非负。

先使用满秩分解的经典基变换事实，其非负分解表述见 Laurberg et al., *Theorems on Positive Data: On the Uniqueness of NMF* (2008), [§3, doi:10.1155/2008/764206](https://doi.org/10.1155/2008/764206)。在这里，若 $S'P'=SP$，则 $\operatorname{im}S'=\operatorname{im}M=\operatorname{im}S$；$S,S'$ 的列都是这个像空间的基。因此存在唯一 $A\in\operatorname{GL}_r(\mathbb R)$ 使 $S'=SA$，再由 $S$ 单射消去得 $P=AP'$。置 $T=A^{-1}$，于是

$$
P'=TP,\qquad S'=ST^{-1}.
\tag{533.3}
$$

由 $P,P'$ 的列和，

$$
(\mathbf1_r^TT-\mathbf1_r^T)P=0.
$$

右乘 $R$ 得 $\mathbf1_r^TT=\mathbf1_r^T$；共同焦点边缘给出 $T\pi=TP\mu=P'\mu=\pi$。因此全部分解变换属于

$$
G_\pi=\{T\in\operatorname{GL}_r(\mathbb R):
\mathbf1_r^TT=\mathbf1_r^T,\ T\pi=\pi\}.
$$

反过来，只要 $T\in G_\pi$ 且 $TP,ST^{-1}$ 逐项严格正，式（533.3）就是合法竞争实现：其乘积为 $M$，其焦点边缘为 $\pi$，其秩保持为 $r$，而

$$
\mathbf1_r^TTP=\mathbf1_m^T,\qquad
\mathbf1_n^TST^{-1}=\mathbf1_r^TT^{-1}=\mathbf1_r^T.
$$

$T$ 是分解之间的代数变换，不要求它或 $T^{-1}$ 非负或列随机；需要严格正且列随机的是变换后两个通道。随机分解中这一非负性区别亦见 Christopher Adams, *Stochastic Matrix Factorization*, [§§2–3, arXiv:1609.05772v1](https://arxiv.org/abs/1609.05772v1)。

因为 $P,S$ 的全部有限个条目严格正，映射 $T\mapsto TP$、$T\mapsto ST^{-1}$ 在 $I_r$ 处连续，故 $G_\pi$ 中存在包含 $I_r$ 的相对开邻域 $U$，其中每个 $T$ 都给出严格正的竞争实现。严格正性在此提供的是所有满足两项线性约束的充分小可逆扰动，而非一条特选扰动曲线。

若 $K$ 的后果恒定，则对每个 $T\in U$ 有

$$
ST^{-1}KTP=SKP.
$$

左乘 $L$、右乘 $R$，得到 $T^{-1}KT=K$，即

$$
KT=TK\qquad(T\in U).
\tag{533.4}
$$

为求这一局部交换条件的全部解，令 $W=\ker(\mathbf1_r^T)$。由于 $\mathbf1_r^T\pi=1$，每个 $z\in\mathbb R^r$ 唯一分解为

$$
z=(\mathbf1_r^Tz)\pi+
\bigl(z-(\mathbf1_r^Tz)\pi\bigr),
\qquad\mathbb R^r=\mathbb R\pi\oplus W.
$$

在此直和下，$T\in G_\pi$ 恰有块式

$$
T=\begin{pmatrix}1&0\\0&D\end{pmatrix},
\qquad D\in\operatorname{GL}(W).
$$

所以 $U$ 包含每个充分接近 $I_W$ 的 $D$ 所对应的变换。$K$ 的列和条件则恰给出

$$
K=\begin{pmatrix}1&0\\v&C\end{pmatrix},
\qquad v\in W,\quad C\in\operatorname{End}(W).
$$

式（533.4）因而等价于 $v=Dv$ 与 $CD=DC$。取充分小非零 $t$ 及 $D=(1+t)I_W$，第一式给出 $v=0$。令 $d=\dim W=r-1\ge1$；若 $d=1$，$C$ 自为标量。若 $d\ge2$，固定 $W$ 的一组基，对每个 $i\ne j$ 取基矩阵 $E_{ij}$。$D=I_W+tE_{ij}$ 在充分小非零 $t$ 时落入上述邻域，故 $CD=DC$ 给出 $CE_{ij}=E_{ij}C$。逐项写成

$$
C_{ai}\delta_{jb}=\delta_{ai}C_{jb}.
$$

取 $a\ne i,b=j$ 得 $C_{ai}=0$，故全部非对角项为零；取 $a=i,b=j$ 得 $C_{ii}=C_{jj}$。于是 $C=\alpha I_W$。这里使用的是与初等剪切矩阵交换强制标量的经典步骤，亦见 [Matrix.mem_range_scalar_of_commute_transvectionStruct](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/Transvection.lean#L228)；本证明中的邻域条件通过非零 $t$ 消去给出它所需的全部基矩阵交换关系。

回到原坐标，对任意 $z$ 有

$$
Kz=(\mathbf1_r^Tz)\pi+
\alpha\bigl(z-(\mathbf1_r^Tz)\pi\bigr),
$$

即式（533.1）。$W\ne\{0\}$ 保证 $\alpha$ 唯一；特别地，$K\pi=\pi$ 是必要性推出的结论，并非对允许操作预加的限制。

现确定非负性的准确范围。$r\ge2$ 与 $\pi$ 严格正给出 $0<\pi_i<1$。当 $i\ne j$ 时，$K_{ij}=(1-\alpha)\pi_i$，故全部非对角项非负当且仅当 $\alpha\le1$；对角项为

$$
K_{ii}=\pi_i+\alpha(1-\pi_i),
$$

故全部对角项非负当且仅当

$$
\alpha\ge\max_i\left(-\frac{\pi_i}{1-\pi_i}\right)
=-\min_i\frac{\pi_i}{1-\pi_i}.
$$

式（533.1）的列和对每个实数 $\alpha$ 都是一，故这两个不等式既必要又充分，且两端点均包含在内。

反向，若 $K$ 有式（533.1）的形式及上述范围，则对任意 $(P',S')\in\mathcal F(M,\mu,\pi)$，

$$
\begin{aligned}
S'KP'
&=\alpha S'P'+(1-\alpha)S'\pi\mathbf1_r^TP'\\
&=\alpha M+(1-\alpha)(S'P'\mu)\mathbf1_m^T\\
&=\alpha M+(1-\alpha)(M\mu)\mathbf1_m^T.
\end{aligned}
$$

这既证明充分性，也证明恢复式（533.2）。

最后证明非族操作的局部不可识别性。若 $K$ 不是式（533.1）的形式，则在上述块式中，或者 $v\ne0$，或者 $v=0$ 而 $C$ 非标量。第一种情形取 $B=I_W$，第二种情形取一个满足 $CB\ne BC$ 的基矩阵 $B=E_{ij}$；这样的基矩阵存在，否则刚才的逐项论证使 $C$ 成为标量。令 $N$ 在直和下为 $\operatorname{diag}(0,B)$，便有

$$
N\pi=0,\qquad \mathbf1_r^TN=0,\qquad KN-NK\ne0.
$$

对每个充分小非零 $\varepsilon$，$T_\varepsilon=I_r+\varepsilon N$ 可逆且属于 $U$，因此

$$
(P_\varepsilon,S_\varepsilon)
=(T_\varepsilon P,ST_\varepsilon^{-1})
\in\mathcal F(M,\mu,\pi),
\qquad(P_\varepsilon,S_\varepsilon)\longrightarrow(P,S).
$$

其操作后果差恰为

$$
\begin{aligned}
S_\varepsilon KP_\varepsilon-SKP
&=ST_\varepsilon^{-1}(KT_\varepsilon-T_\varepsilon K)P\\
&=\varepsilon ST_\varepsilon^{-1}(KN-NK)P\ne0.
\end{aligned}
$$

若末项为零，左乘 $T_\varepsilon L$、右乘 $R$ 就会得到 $KN-NK=0$，矛盾。每个充分小非零扰动都保留共同数据而改变该固定后果，证明所述任意邻域结论。证毕。

### 命题 533.6（同焦点、同方向与同边缘下重置后果仍可不同）

令 $X=H=Y=\{1,2\}$，所有标签及角色类型固定，取

$$
\mu=\pi=\begin{pmatrix}1/2\\1/2\end{pmatrix},\qquad
P=S=\begin{pmatrix}3/4&1/4\\1/4&3/4\end{pmatrix},
$$

$$
P'=\begin{pmatrix}11/16&5/16\\5/16&11/16\end{pmatrix},\qquad
S'=\begin{pmatrix}5/6&1/6\\1/6&5/6\end{pmatrix}.
$$

两实现具有相同数据

$$
M=\begin{pmatrix}5/8&3/8\\3/8&5/8\end{pmatrix},
\qquad P\mu=P'\mu=\pi,
$$

而同一个“重置到标签 $1$”的操作

$$
K=\begin{pmatrix}1&1\\0&0\end{pmatrix}
$$

产生不同的端点通道

$$
SKP=\begin{pmatrix}3/4&3/4\\1/4&1/4\end{pmatrix},\qquad
S'KP'=\begin{pmatrix}5/6&5/6\\1/6&1/6\end{pmatrix}.
$$

因此，即使焦点集合、两类关系的方向、类型、操作含义和焦点边缘都已固定，共同端点资料仍可遗失这些关系经焦点衔接所需的操作信息。在相同 $\pi$ 下，定理 533.5 的负端点 $\alpha=-1$ 则给出可识别的标签交换操作；重置到一个固定标签与重置到共同分布 $\pi$ 也属于不同操作。

**证明。** 四个通道逐项严格正且每列和为一，其行列式依次为 $1/2,1/2,3/8,2/3$，故均满秩。两个 $P$ 矩阵还各自每行和为一，因而保持均匀 $\mu$。直接相乘得 $SP=S'P'=M$。由于 $KP=KP'=K$，两种操作后果分别把 $S,S'$ 的第一列重复两次，得到显示的不同通道。操作 $K$ 不满足 $K\pi=\pi$，亦不在定理 533.5 的族中。

此处的分解变换及其逆为

$$
T=\begin{pmatrix}7/8&1/8\\1/8&7/8\end{pmatrix},\qquad
T^{-1}=\begin{pmatrix}7/6&-1/6\\-1/6&7/6\end{pmatrix},
\qquad P'=TP,\quad S'=ST^{-1}.
$$

$T^{-1}$ 的负条目没有妨碍两个新通道严格正，具体体现了定理中对代数变换与合法通道的分别。最后，均匀 $\pi$ 的参数范围为 $[-1,1]$，且

$$
-I_2+2\pi\mathbf1_2^T=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

该操作的共同后果为 $-M+2(M\mu)\mathbf1_2^T=\begin{pmatrix}3/8&5/8\\5/8&3/8\end{pmatrix}$。它不在 $0\le\alpha\le1$ 的凸混合段内，故不能删除负参数部分。整个构造只比较同一现代模型中的关系实现，没有把健康征候等同于产生健康的关系，也没有从端点数据判定经验因果方向。证毕。

## 追加锚（本行以下为增补区）


## 534. 亚里士多德式事实—目标—因果方向的有限资源关系

### 定义 534.1（共同高斯因果实现与比较空间）

固定参数 $0<\rho<1$、$\sigma=\sqrt{1-\rho^2}$、$h>0$，并令 $a=h/\rho$。对每次全新重置 $t$，在同一个乘积噪声空间上取相互独立的标准正态变量 $(U_{0t},U_{1t},U_{2t})$。未知参数 $\theta\in\{+1,-1\}$ 在整个实验中固定。两种结构模型为

$$
\begin{array}{lll}
M_+:&X_t=U_{0t},&H_t=\rho X_t+\sigma U_{1t},\quad Y_t=\rho H_t+\sigma U_{2t},\\
M_-:&Y_t=U_{0t},&H_t=\rho Y_t+\sigma U_{1t},\quad X_t=\rho H_t+\sigma U_{2t}.
\end{array}
$$

在没有干预时，$(X_t,H_t,Y_t)$ 的共同协方差矩阵为

$$
\Sigma=
\begin{pmatrix}
1&\rho&\rho^2\\
\rho&1&\rho\\
\rho^2&\rho&1
\end{pmatrix}.
$$

这里的同一噪声空间只是比较两种模型的耦合；观察者只能得到规定的观测记录，不能访问未观测的 $U_{it}$，也不能把两个模型的潜在样本同时取得。

### 假设 534.2（操作、历史与逐点许可）

每轮以操作 $\operatorname{do}(X_t=u_t,Y_t=v_t)$ 替换两个端点方程而保留 $H$ 方程，并且只揭示 $H_t$。私有随机带 $R$ 取值于标准 Borel 空间，独立于 $\theta$ 与所有重置噪声；它包括终端随机化所需的全部随机性。第 $t$ 轮的 $(u_t,v_t)$ 是 $R$ 与此前动作—结果历史的 Borel 函数，终端判决也可使用完整历史和 $R$。不存在当前重置噪声、干预前同一单位的额外读数、额外结果或依赖 $\theta$ 的时序访问。

给定有限预算 $B\ge0$，定义

$$
A_B=\{(u,v):u\ge a,\ v\ge a,\ u^2+v^2\le B\}.
$$

许可是逐个 $(R,\text{历史})$ 路径的许可：每个可能输入上动作都必须落在 $A_B$。等价地，指定的观测核在两种模型下的条件均值都至少为 $h$，且端点平方和不超过 $B$；该条件不对动作彩票、轮次平均或 $\theta$ 的后验取平均。

这一区分只作受限的现代重构：亚里士多德《后分析篇》I.2 要求知识以原因作为原因并涉及不能否则，I.13 要求近接原因及互逆推理中的中项，并明确普遍理由并不保证对特殊事实的知识。因此下述均值目标和方向检验不被定义为 *episteme*，也不把历史天文学或医学例子当作现代经验前提。[Aristotle, *Posterior Analytics* I.2, I.13, G. R. G. Mure 英译](https://classics.mit.edu/Aristotle/posterior.1.i.html)；[Stanford Encyclopedia of Philosophy, “Aristotle’s Logic”, §6.1，实质修订 2022-11-22](https://plato.stanford.edu/entries/aristotle-logic/#AriSci)。

### 定义 534.3（记录、方向风险与目标推荐风险）

令 $n\ge1$ 为固定轮数。对任一满足假设 534.2 的策略 $\pi$，记完整记录为

$$
L[n]=(R,(u_t,v_t,H_t)_{t=1}^n).
$$

若 $B\ge2a^2$，定义方向判决的精确有限资源风险

$$
R_n(B,h)=\inf_{\pi,\delta}\max_{\theta\in\{+1,-1\}}
\mathbb P_\theta^\pi\bigl(\delta(L[n])\ne\theta\bigr),
$$

其中 $\delta$ 遍历所有可测的终端随机判决（其随机性已包含于 $R$）。再给定推荐预算 $C\ge0$，允许终端输出可测的 $w=(s,t)$，满足 $s^2+t^2\le C$，但不把推荐当作额外执行的干预。令

$$
\mu_+(w)=\rho s,\qquad \mu_-(w)=\rho t,
$$

并定义目标推荐失败风险

$$
F_n(B,C,h)=\inf_{\pi,w}\max_{\theta\in\{+1,-1\}}
\mathbb P_\theta^\pi\bigl(\mu_\theta(w)<h\bigr),
$$

其中训练阶段仍严格使用同一 $A_B$ 和同一记录类。

### 命题 534.4（被动共同律与干预条件核）

在定义 534.1 的被动情形，两种模型的 $(X,H,Y)$ 都服从 $N(0,\Sigma)$，故被动联合资料对 $\theta$ 不可区分。给定任意历史、$R$ 和当前逐点许可动作 $(u_t,v_t)\in A_B$，新鲜重置保证

$$
H_t\mid(\text{历史},R,u_t,v_t),\theta=+1\sim N(\rho u_t,\sigma^2),
$$

$$
H_t\mid(\text{历史},R,u_t,v_t),\theta=-1\sim N(\rho v_t,\sigma^2).
$$

**证明。** 在 $M_+$ 中，$(X,H,Y)$ 是独立标准正态向量的线性像，均值为零；直接计算给出
$\operatorname{Var}X=\operatorname{Var}H=\operatorname{Var}Y=1$、$\operatorname{Cov}(X,H)=\operatorname{Cov}(H,Y)=\rho$、$\operatorname{Cov}(X,Y)=\rho^2$。在 $M_-$ 中交换端点得到同一协方差矩阵，且同样是联合高斯。因此相同均值和协方差给出相同的完整高斯律，而非仅有相同矩。

执行 $\operatorname{do}(X_t=u_t,Y_t=v_t)$ 后，$M_+$ 的中间方程成为 $H_t=\rho u_t+\sigma U_{1t}$，$M_-$ 成为 $H_t=\rho v_t+\sigma U_{1t}$。新鲜的 $U_{1t}$ 与过去、$R$ 和当前动作独立，故这些式子是对每个历史输入都定义的正则条件核，不依赖在零概率历史上选择条件期望的版本。证毕。

### 命题 534.5（可行集合的精确分离）

$A_B=\varnothing$ 当且仅当 $B<2a^2$。当 $B\ge2a^2$，对任意 $(u,v)\in A_B$，令

$$
 m=\rho\frac{u+v}{2},\qquad
 k=\frac{\rho(u-v)}{2\sigma}.
$$

则 $|k|\le k_*$，其中

$$
 d_* =\sqrt{B-a^2}-a,\qquad k_* =\frac{\rho d_*}{2\sigma}.
$$

等号由 $(u,v)=(\sqrt{B-a^2},a)$ 及其交换取得。

**证明。** 非空性由 $u,v\ge a$ 与 $u^2+v^2\le B$ 的最小平方和立即给出。若 $u\ge v\ge a$，则
$u\le\sqrt{B-v^2}\le\sqrt{B-a^2}$，故 $u-v\le\sqrt{B-a^2}-a$；交换 $u,v$ 处理另一情形。证毕。

### 定理 534.6（全自适应策略的精确方向前沿）

对每个整数 $n\ge1$、$0<\rho<1$、$h>0$ 及有限 $B$，在假设 534.2 与定义 534.3 的完整 Borel 随机策略类上有：

1. 当 $B<2a^2$ 时许可类为空，不赋予其风险值。
2. 当 $B\ge2a^2$ 时，令 $d_*,k_*$ 如命题 534.5，则

$$
R_n(B,h)=\Phi(-\sqrt n\,k_*).
$$

该下确界由逐轮固定动作和阈值判决达到。对 $0<\varepsilon<1/2$，满足 $R_n(B,h)\le\varepsilon$ 的最小预算为

$$
B_{\min}=a^2+\left[a+\frac{2\sigma\Phi^{-1}(1-\varepsilon)}{\rho\sqrt n}\right]^2.
$$

**证明。** 对任一固定策略 $\pi$，标准 Borel 随机化定理把全部非预见随机策略表示为独立种子 $R$ 与逐轮 Borel 映射；把终端随机化一并放入 $R$ 不损失策略类。由命题 534.4，在动作确定后标准化

$$
Z_t=\frac{H_t-m_t}{\sigma}
$$

的条件律为 $N(\theta k_t,1)$，其中 $|k_t|\le k_*$，并且 $k_t$ 可依赖 $R$ 及先前完整历史。

先构造一个不含 $\theta$ 的完整记录模拟器。若 $k_*>0$，给定输入 $T_1,\ldots,T_n$，在内部独立抽取 $R$ 及 $W_t\sim N(0,1)$，递归地由模拟历史计算策略动作，得到对应的 $m_t,k_t$，再置

$$
 Z_t=\frac{k_t}{k_*}T_t+
 \sqrt{1-\left(\frac{k_t}{k_*}\right)^2}\,W_t,
 \qquad H_t=m_t+\sigma Z_t.
$$

系数允许为负。把 $R$、每个动作和每个 $H_t$ 全部输出，所得 Markov 核记为 $K_\pi$。对 $\theta=\pm1$，若输入 $T_t$ 独立服从 $N(\theta k_*,1)$，则在给定模拟过去时 $T_t$ 仍新鲜，故 $Z_t\sim N(\theta k_t,1)$；归纳于轮次 $t$ 得

$$
\operatorname{Law}_\theta^\pi(L[n])
=K_\pi\bigl(N(\theta k_*,1)^{\otimes n}\bigr),
$$

核 $K_\pi$ 对两个 $\theta$ 相同，且只复现实际方向下的律，不声称保留隐藏的跨方向反事实耦合。若 $k_*=0$，命题 534.5 强制每个许可动作为 $(a,a)$，两方向的完整记录律相同，直接取相同律的核，避免除以 $k_*$。

对任意策略和判决，最大错误不小于等先验平均错误。把判决经 $K_\pi$ 拉回后得到产品实验 $N(\pm k_*,1)^{\otimes n}$ 上的随机检验。其对数似然比为 $2k_*\sum_{t=1}^nT_t$，等先验最小错误为
$\Phi(-\sqrt n\,k_*)$，所以这是同一策略类的统一下界；等先验只是下界工具，不是模型附加的先验。

反向取每轮 $(u_t,v_t)=(\sqrt{B-a^2},a)$，则 $k_t=k_*$ 且 $Z_t$ 独立服从 $N(\theta k_*,1)$。判决 $\delta=+1$ 当且仅当 $\sum_tZ_t\ge0$，两方向错误概率都等于 $\Phi(-\sqrt n\,k_*)$，达到下界。$k_*=0$ 时完整记录同律，独立公平硬币达到 $1/2$。最后由高斯尾函数严格单调性解出 $\sqrt{B-a^2}\ge a+2\sigma\Phi^{-1}(1-\varepsilon)/(\rho\sqrt n)$，得到所示 $B_{\min}$。证毕。

**证明附引。** 这里的核归纳与任意自适应历史的全记录支配可与 Song, *Pre-Disclosure Experiment Menus*, v1, Theorem 2.1 的递归核机制比较；高斯组合的参数形式与 Dong–Roth–Su, *Gaussian Differential Privacy*, Theorem 3.2、Corollary 3.3 相容。那些结果是一般中间工具；本定理的内容是带逐点因果许可、共同实现和目标约束的这一特定前沿，而非把通用自适应定理改名重述。[Song, arXiv:2608.22905v1](https://arxiv.org/html/2608.22905v1)；[Dong, Roth and Su, arXiv:1905.02383](https://arxiv.org/html/1905.02383)。

### 命题 534.7（边界、事实成功与单端点权限）

在定理 534.6 的模型中：

1. $B=2a^2$ 时唯一动作是 $(a,a)$，均值目标达到但完整记录与 $\theta$ 无关，故任意有限 $n$ 都有 $R_n=1/2$。
2. $B>2a^2$ 时可选动作产生不同方向律，且 $R_n>0$ 对每个有限 $n,B$ 仍成立；当 $n\to\infty$ 时定理中的最优风险趋于 $0$。同一预算下也存在无信息策略，例如每轮取 $(a,a)$。
3. 对任一有限许可动作，若 $w_+=u_t,w_-=v_t$，则

$$
\mathbb P_\theta(H_t\ge h\mid\text{历史},R,u_t,v_t)
=\Phi\!\left(\frac{\rho w_\theta-h}{\sigma}\right)<1.
$$

在对应端点恰取 $a$ 时该概率为 $1/2$，而非概率一的事实成功；高斯满支撑排除了有限预算下的几乎处处保证。知道结构律和 $\theta$ 仍不等于预先知道某次新鲜重置的特殊实现。
4. 若每轮只准干预一个端点，则在相反方向中 $H$ 保持零均值的新鲜律；$h>0$ 使这种更窄权限类不可行。

**证明。** 前三项直接由命题 534.4 的正态核、$A_B$ 的边界及定理 534.6 的严格正高斯尾得到。第四项中，$M_-$ 下只干预 $X$ 不改变 $H=\rho Y+\sigma U_1$ 的零均值，$M_+$ 下只干预 $Y$ 同理；故至少有一个方向不能满足正的均值目标。这里“均值目标”与“实际特殊事实”分离，也正是 I.13 关于普遍理由和已观察特殊事实的边界在此模型中的有限对应。证毕。

### 定理 534.8（推荐目标何时需要方向信息）

对 $B\ge2a^2$，定义 $F_n$ 如定义 534.3。则

$$
F_n(B,C,h)=
\begin{cases}
1,&0\le C<a^2,\\
R_n(B,h),&a^2\le C<2a^2,\\
0,&C\ge2a^2.
\end{cases}
$$

中间区间的成功推荐集合

$$
G_+=\{(s,t):s^2+t^2\le C,\ s\ge a\},\qquad
G_- =\{(s,t):s^2+t^2\le C,\ t\ge a\}
$$

非空且不相交；因而达到目标的推荐必须解出方向。$C\ge2a^2$ 时 $(a,a)$ 同时属于两集合，方向信息不再是该均值目标的必要条件。该结论只谈推荐失败风险；若部署阶段仍继承逐点许可 $A_B$，$C<2a^2$ 的推荐不因此取得可执行的鲁棒授权。

**证明。** 当 $C<a^2$ 时，任意 $w$ 都有 $s<a$ 且 $t<a$，两方向均失败，故风险为 $1$。当 $a^2\le C<2a^2$ 时，$G_+,G_-$ 非空，且若一点评价同时满足 $s,t\ge a$ 则 $s^2+t^2\ge2a^2>C$，所以二者不交。给定任意策略和推荐，定义解码器：若 $s\ge a$ 输出 $+1$，否则若 $t\ge a$ 输出 $-1$，其余任意。由于成功集合不交，在真实方向下推荐成功必然使解码器正确，故方向错误概率不超过推荐失败概率，取下确界得 $R_n\le F_n$。

反向，对任意方向判决 $\delta$，在 $\delta=+1$ 时推荐 $(a,0)$，在 $\delta=-1$ 时推荐 $(0,a)$；这两个点平方范数均为 $a^2$，且推荐失败事件恰为判决错误，故 $F_n\le R_n$。当 $C\ge2a^2$，恒定推荐 $(a,a)$ 同时满足两方向，风险为零。证毕。

### 命题 534.9（动作彩票平均许可不保持定理 534.6）

考虑不同的、更弱的合同：只要求在动作彩票抽取前、给定过去时
$\mathbb E_\theta[H_t\mid\text{过去}]=h$，但仍要求每个实际动作满足 $u_t^2+v_t^2\le B$。取 $B=4a^2$，每轮独立公平抽取 $S_t\in\{+1,-1\}$，分别选择

$$
S_t=+1:(u_t,v_t)=(2a,0),\qquad
S_t=-1:(u_t,v_t)=(0,2a).
$$

则两模型都满足该较弱均值合同，而每个实际动作在一个模型中违反原先的鲁棒均值许可。保留 $S_t$ 于记录，便有

$$
H_t=h+\theta hS_t+\sigma U_{1t},
\qquad
\frac{S_t(H_t-h)}{\sigma}\ \stackrel{\mathrm{i.i.d.}}\sim
N\!\left(\theta\frac h\sigma,1\right).
$$

因此以 $\sum_tS_t(H_t-h)\ge0$ 判决时，两方向错误均为

$$
\Phi\!\left(-\sqrt n\,\frac h\sigma\right),
$$

严格小于定理 534.6 在 $B=4a^2$ 下的

$$
\Phi\!\left(-\sqrt n\,\frac{h(\sqrt3-1)}{2\sigma}\right).
$$

这只是较弱合同中的一个可达到风险反例，不声称该扩大策略类的精确极小风险。

**证明。** 条件于过去，$S_t$ 独立公平，故在 $M_+$ 中均值为 $(2h+0)/2=h$，在 $M_-$ 中均值为 $(0+2h)/2=h$。但路径 $(2a,0)$ 在 $M_-$、路径 $(0,2a)$ 在 $M_+$ 的原逐点均值分别为零。乘以 $S_t$ 后，$S_tU_{1t}$ 仍为独立标准正态，显示的正态律与阈值错误率随即成立。定理 534.6 在 $B=4a^2$ 时有 $d_*=a(\sqrt3-1)$，且 $\rho a=h$；因 $1>(\sqrt3-1)/2$，高斯尾严格比较成立。证毕。

## 追加锚（本行以下为增补区）

## 535. 家族相似与目的边界：实际交叠中的两种共同信息下界

### 定义 535.1（实际对象、固定目的与情境取得）

设 $A$ 为有限非空的实际对象集，固定映射

$$
c:A\to K,\qquad q:A\to L,\qquad T:A\to Y,
\qquad K=c(A),\quad L=q(A),\quad Y=T(A).
$$

所有有限集合赋予离散可测结构。$c$ 是辅助信息的取得端可读的情境，$q$ 是接收端已观察到的旧读数，$T$ 是本次比较始终保持的目标。假定局部一致性

$$
\forall x,x'\in A,\qquad
c(x)=c(x')\ \land\ q(x)=q(x')\ \Longrightarrow\ T(x)=T(x').
\tag{535.1}
$$

记实际联合支撑及各读数下的活动情境为

$$
S=\{(c(x),q(x)):x\in A\},\qquad
K_\ell=\{k\in K:(k,\ell)\in S\}\quad(\ell\in L).
$$

式（535.1）使 $t:S\to Y$ 由 $t(c(x),q(x))=T(x)$ 良定义。允许不同对象具有相同的 $(c,q)$；不将 $A$ 默认为 $S$，也不补入 $K\times L\setminus S$ 中没有实际对象的组合。

对每个非空标准 Borel 空间 $Z$，允许任意 Markov 核 $W:K\to\operatorname{Prob}(Z)$，记 $W_k=W(\cdot\mid k)$。它产生实际实验

$$
E_W(x)=\delta_{q(x)}\otimes W_{c(x)}\quad(x\in A),\qquad
\Gamma_c=\{E_W:Z\text{ 非空标准 Borel},\ W:K\to\operatorname{Prob}(Z)\}.
\tag{535.2}
$$

选择通道时可以使用固定的 $S,t$，运行时辅助取得只读 $c(x)$，不能再读 $q(x)$、$T(x)$ 或对象身份 $x$。编码器私有随机位已被边缘化进 $W_k$，没有额外揭示；若要把随机种子也交给观察者，必须把它计入输出并重新规定通道。接收端看到的是 $(q(x),z)$。

这一目的限定只对应维特根斯坦《哲学研究》§§65–69 的一个局部问题。§§65–67 用游戏与纤维交叠反对未经考察就要求同名使用必有一个贯穿全部情形的本质；§68 允许给“数”等概念划定边界，也允许未封闭的使用；§69 明说可以“für einen besondern Zweck”划界，却不因此才使概念通常可用。本章将一个特定目的固定为 $T$，考察取得约束下的精确信息边界；这不是全部语言意义的模型，不将家族相似定义为图连通，也不推出所有概念都没有共同性质。下文的最小信息要求是附加的比较问题，既不是日常有用性的必要条件，也不是存在某个目的充分边界的必要条件。[Wittgenstein, *Philosophische Untersuchungen*, §§65–69，德文原文](https://www.wittgensteinproject.org/w/index.php/Philosophische_Untersuchungen#65)；[Stanford Encyclopedia of Philosophy, “Ludwig Wittgenstein”, §3.4，实质修订 2026-09-17](https://plato.stanford.edu/entries/wittgenstein/#LangGameFamiRese)。

### 定义 535.2（逐态恢复、实际实验序与最小性）

称 $E_W$ 对 $T$ 充分，当且仅当存在 Markov 解码核 $D:L\times Z\to\operatorname{Prob}(Y)$，使

$$
\forall x\in A,\qquad
\int_Z D(\{T(x)\}\mid q(x),z)\,W_{c(x)}(dz)=1.
\tag{535.3}
$$

解码器允许独立的私有随机化，但不观察编码器未揭示的随机位。条件是每个实际对象上的概率一恢复，不使用先验。有限 $A$ 上，若另取对每个 $x$ 都严格正的先验，平均错误为零与式（535.3）等价，因为有限和中的非负错误项都必须为零；若先验给某个实际对象零质量，则平均条件不再要求该对象恢复正确。

更一般地，$A$ 上的实验 $E$ 是一族取值于某个非空标准 Borel 空间 $\mathcal E$ 的概率律 $(E_x)_{x\in A}$。对输出空间为 $\mathcal F$ 的另一实验 $F$，定义

$$
F\preceq E
\iff
\exists G:\mathcal E\to\operatorname{Prob}(\mathcal F)\text{ Markov},\quad
\forall x\in A,\quad F_x=\int_{\mathcal E}G(\cdot\mid e)E_x(de).
\tag{535.4}
$$

同一个 $G$ 必须适用于所有实际对象，不能额外依赖 $x$。此序左端信息较少，允许模拟器使用整个源输出并随机化；特别地，源为 $E_W$ 时允许使用已经看到的 $q$，不要求它只作用于辅助坐标，也不预加逐输出保持 $q$ 的限制。记 $E\simeq F$ 表示互相支配。有限统计量 $h:A\to B$ 也用 $h$ 表示其 Dirac 实验；确定性统计量的实际纤维与因子化对应沿用第 7、532 章。对一般实验，目标充分性写作 $T\preceq E$；对 $U$ 的充分性同理写作 $U\preceq E$，其中有限目标的核因子化正是概率一恢复。

记充分族

$$
\mathcal F_T=\{E\in\Gamma_c:E\text{ 对 }T\text{ 充分}\}.
$$

$E_\circ$ 是最小充分实验，意指 $E_\circ\in\mathcal F_T$ 且 $E_\circ\preceq E$ 对每个 $E\in\mathcal F_T$ 成立；若存在，它在 $\simeq$ 下唯一。$E_\circ$ 是极小充分实验，则只要求

$$
\forall F\in\mathcal F_T,\qquad
F\preceq E_\circ\ \Longrightarrow\ E_\circ\preceq F.
$$

“最小”与“极小”分别对应 least 与 minimal，不以辅助字母表的大小或一个标量风险替代。实验 $B$ 是 $\mathcal F_T$ 的共同下界，是指 $B\preceq E$ 对每个 $E\in\mathcal F_T$ 成立；最大共同下界还须支配所有同一比较范围内的共同下界。

式（535.4）采用 Blackwell 的参数无关后处理序；有限通道的标准表述及决策比较等价见 Bertschinger–Rauh, *The Blackwell relation defines no lattice*, Definitions 1–3、Theorem 4。本章直接以核因子化为序的定义，对任意标准 Borel 输出的下述推导不依赖把有限矩阵定理外推为无限输出定理。[arXiv:1401.3146v1](https://arxiv.org/html/1401.3146v1)。

### 定义 535.3（全局相容、实际交叠与局部和全局闭包）

在 $K$ 上定义

$$
\begin{aligned}
R(k,k')&\iff
\forall\ell\in L,\quad
k,k'\in K_\ell\ \Longrightarrow\ t(k,\ell)=t(k',\ell),\\
O(k,k')&\iff\exists\ell\in L,\quad k,k'\in K_\ell,\\
H&=R\cap O.
\end{aligned}
\tag{535.5}
$$

$R$ 自反、对称但不必传递；没有共同读数时相容条件真空成立。$O$ 记录实际共同出现，不能从两个边缘像推得某个共同组合。令 $C$ 为 $K$ 上包含 $H$ 的最小等价关系；令 $C_\ell$ 为 $K_\ell$ 上包含 $R|_{K_\ell\times K_\ell}$ 的最小等价关系。$C$ 的路径可以逐边更换见证交叠的旧读数，$C_\ell$ 的路径则始终留在 $K_\ell$，但其每条边仍须满足在所有实际读数上定义的 $R$。因此不能仅检验当前 $\ell$ 下两个目标相等就添加一条边。

定义有限统计量

$$
\begin{aligned}
\mathcal U&=\bigsqcup_{\ell\in L}\bigl(\{\ell\}\times(K_\ell/C_\ell)\bigr),
&U(x)&=(q(x),[c(x)]_{C_{q(x)}}),\\
\mathcal V&=L\times(K/C),
&V(x)&=(q(x),[c(x)]_C).
\end{aligned}
\tag{535.6}
$$

$V$ 由有限确定性编码 $k\mapsto[k]_C$ 实现，故属于 $\Gamma_c$。$U$ 是实际对象上的抽象统计量；其公式使用当前 $q$ 选择商关系，尚不意味着存在只读 $c$ 的通道与之等价。$R$ 是成对相容关系，$C_\ell,C$ 是两种等价闭包，$\ker_A U,\ker_A V$ 才是相应确定性实验在实际对象上的观察等价；这些关系的定义域与作用不能互换。

### 定理 535.4（整个随机充分族的两种最大共同下界）

在定义 535.1—535.3 下，$\mathcal F_T$ 非空，并有以下结论。

1. 在 $A$ 上所有标准 Borel 输出实验中，$U$ 是 $\mathcal F_T$ 的最大共同下界，即

$$
\forall E\in\mathcal F_T,\quad U\preceq E,
\qquad
\forall F,\quad
\bigl(\forall E\in\mathcal F_T,\ F\preceq E\bigr)\Longrightarrow F\preceq U.
\tag{535.7}
$$

这里 $F$ 可以不保留 $q$。$U$ 本身对 $T$ 充分；在 $\Gamma_c$ 内，对 $T$ 充分和对 $U$ 充分是同一个实验条件。

2. 对任意非空标准 Borel 空间 $Z$ 及任意 $W:K\to\operatorname{Prob}(Z)$，有完整分类

$$
\bigl(\forall E\in\mathcal F_T,\ E_W\preceq E\bigr)
\iff
\bigl(\forall k,k'\in K,\ kCk'\Longrightarrow W_k=W_{k'}\bigr)
\iff E_W\preceq V.
\tag{535.8}
$$

因此 $V$ 是限于 $\Gamma_c$ 的最大共同下界，但不保证充分。

3. 最小充分允许实验存在的准确条件是

$$
\mathcal F_T\text{ 有最小元}
\iff C\subseteq R.
\tag{535.9}
$$

即没有一条 $H$ 路径连接不相容的两个情境。条件成立时 $V$ 最小且 $U\simeq V$；条件不成立时，$U$ 虽充分，却没有与之等价的 $\Gamma_c$ 成员。只允许确定性编码与允许全部标准 Borel 随机编码，最小充分实验存在的条件相同。

**证明。** 先固定实际比较序的一项归约。设 $E_F\preceq E_W$，其中两实验的辅助空间分别为 $Z',Z$，而一个任意模拟核为 $G:L\times Z\to\operatorname{Prob}(L\times Z')$。对每个源读数 $\ell$，取其输出辅助坐标的边缘

$$
G_\ell(B\mid z)=G(L\times B\mid\ell,z)
\quad(B\subseteq Z'\text{ 可测}).
$$

这是定义在全部 $z$ 上的 Markov 核，且由实际行等式取边缘得

$$
\forall(k,\ell)\in S,\qquad
F_k(B)=\int_ZG_\ell(B\mid z)W_k(dz).
\tag{535.10}
$$

反之，给定满足式（535.10）的核族 $G_\ell$，令模拟器在输入 $(\ell,z)$ 上输出 $\delta_\ell\otimes G_\ell(\cdot\mid z)$，就得到原定义中的 $E_F\preceq E_W$。因为 $L$ 有限，该拼接可测。这个归约不是对原 $G$ 作条件化，不涉及在零概率输出上相除，也不要求原 $G$ 在每个输入点保持第一坐标；它证明总能换成一个保留已见 $\ell$ 的模拟器。后文若只在全测集上指定某个核或解码器，则在其余输入上统一取输出空间中一个固定点的 Dirac 律，将它扩成处处定义的核。

现给出零误差分离这一中间事实。对任意 $Z,W$，

$$
E_W\in\mathcal F_T
\iff
\forall k,k'\in K,\quad \neg R(k,k')\Longrightarrow W_k\perp W_{k'}.
\tag{535.11}
$$

右端的互相奇异指存在可测集 $B$ 使 $W_k(B)=1,W_{k'}(B)=0$，不是指某个拓扑支撑不相交。若 $\neg R(k,k')$，取共同实际读数 $\ell$，使 $y=t(k,\ell)\ne t(k',\ell)=y'$。式（535.3）及被积函数位于 $[0,1]$ 给出

$$
D(\{y\}\mid\ell,z)=1\quad W_k\text{-几乎处处},\qquad
D(\{y'\}\mid\ell,z)=1\quad W_{k'}\text{-几乎处处}.
$$

这两个可测集合不交，因为一个概率律不能同时给不同单点质量一。故 $W_k\perp W_{k'}$。

为证反向，取一个有限共同支配测度及可测 Radon–Nikodym 密度

$$
\mu=\sum_{k\in K}W_k,\qquad f_k=\frac{dW_k}{d\mu}.
$$

可取 $f_k\ge0$，且在一个 $\mu$-零集之外所有密度有限并满足 $\sum_k f_k=1$。对每个不相容对，奇异性给出 $f_kf_{k'}=0$ 几乎处处：在分离集上一个密度为零，在其补集上另一个为零。由于 $K$ 有限，把所有这些例外与密度恒等式的例外并入同一个可测零集 $N$。于是对每个 $z\notin N$，集合

$$
I(z)=\{k\in K:f_k(z)>0\}
$$

非空且任意两元素都 $R$-相容。固定 $K$ 的一个线性次序。在输入 $(\ell,z)$ 上，若 $z\notin N$ 且 $I(z)\cap K_\ell\ne\varnothing$，选其中第一个元素 $k_0$，输出 $t(k_0,\ell)$；其余情形输出固定 $y_0\in Y$。这是有限个可测判定给出的可测函数。候选元素都共享 $\ell$ 且两两 $R$-相容，故其目标值相同。对任一实际 $(k,\ell)$，有 $W_k(N)=0$ 及 $W_k(\{f_k=0\})=0$，所以 $k\in I(z)\cap K_\ell$ 几乎处处，输出恰为 $t(k,\ell)$。这证明式（535.11），并同时证明私有随机解码器不扩大充分类。

这个冲突分离条件在有限输出下就是零误差侧信息编码的特征图条件；确定性情形退化为第 532 章的编码纤维包含于 $R$。经典起点为 Witsenhausen, *The zero-error side information problem and chromatic numbers*, IEEE Transactions on Information Theory 22(5), 592–593 (1976), [doi:10.1109/TIT.1976.1055607](https://doi.org/10.1109/TIT.1976.1055607)；这里特征图编码的具体表述参照可得全文 Charpenay–le Treust–Roumy, *Optimal Zero-Error Coding for Computing under Pairwise Shared Side Information*, Definition III.1 与 Theorem III.4，[arXiv:2211.03649v2](https://arxiv.org/html/2211.03649v2)。上面的有限支配测度论证把所需分离同时落实到本章允许的全部标准 Borel 输出，不以有限输出枚举替代该范围。

式（535.1）保证恒等情境编码 $k\mapsto k$ 充分，故 $\mathcal F_T\ne\varnothing$。若取消式（535.1），两个相同 $(c,q)$ 而目标不同的实际对象具有完全相同的实验律，任何同一解码器都不可能分别概率一输出两个不同目标；所以这也正是存在允许充分修复所需的局部前提。

证明第一项。对任一 $E_W\in\mathcal F_T$，沿用上述密度和同一个公共零集。在有效的 $(\ell,z)$ 上，$I(z)\cap K_\ell$ 中所有元素通过 $R|_{K_\ell\times K_\ell}$ 的边直接相连，故属于同一个 $C_\ell$ 类。用同一个首元素规则输出 $(\ell,[k_0]_{C_\ell})$，在无效输入上输出固定 $u_0\in\mathcal U$，便是从 $E_W$ 恢复 $U$ 的可测确定性核。于是 $U\preceq E_W$ 对整个随机充分族成立。

在 $K_\ell$ 内，每条 $R$ 边保持 $t(\cdot,\ell)$，因而沿 $C_\ell$ 的每条有限路径也保持它。故映射

$$
(\ell,[k]_{C_\ell})\longmapsto t(k,\ell)
$$

良定义并恢复 $T$。这证明 $U$ 充分，也证明对 $U$ 充分的允许实验必对 $T$ 充分；刚构造的恢复核给出反向。

还须证明 $U$ 支配任意共同下界，而不只支配确定性下界。令 $F=(F_x)_{x\in A}$ 是任意标准 Borel 输出实验，且对每个 $E\in\mathcal F_T$ 都有 $F\preceq E$。恒等情境实验 $x\mapsto(q(x),c(x))$ 属于 $\mathcal F_T$，所以其相同行在任一后处理下仍相同；因此

$$
c(x)=c(x'),\ q(x)=q(x')\quad\Longrightarrow\quad F_x=F_{x'}.
\tag{535.12}
$$

这一步处理了实际对象的重复表示。接着，对不同的相容情境 $kRk'$，取唯一非单点块为 $\{k,k'\}$、其余为单点的分划，发送其块标签。每一块内元素都 $R$-相容，该确定性实验由式（535.11）充分。若 $k,k'\in K_\ell$，此实验在两条实际 $(k,\ell),(k',\ell)$ 行上相同，其后处理 $F$ 也相同。结合式（535.12），沿任意 $C_\ell$ 路径传播行相等，得到

$$
U(x)=U(x')\quad\Longrightarrow\quad F_x=F_{x'}.
\tag{535.13}
$$

对每个 $u\in U(A)=\mathcal U$ 选择代表对象 $x_u$，从输入 $u$ 输出概率律 $F_{x_u}$。有限输入上的这一核可测；式（535.13）使选择无关并给出 $F\preceq U$。证明没有给 $F$ 添加 $q$ 坐标，也没有限制它的输出字母表，第一项成立。

证明第二项的必要性。若 $E_W$ 是共同下界，对任一不同的 $H$ 相邻情境 $k,k'$，取它们的实际共同读数 $\ell$，再取刚才只合并此对的充分实验。其在这两行上的律相同，故后处理所得

$$
\delta_\ell\otimes W_k=\delta_\ell\otimes W_{k'}.
$$

取辅助坐标边缘得到 $W_k=W_{k'}$。沿 $C$ 的路径传播即得式（535.8）中间条件。这里需要 $O$ 所保证的实际共同读数；真空相容而没有交叠的一对不能直接强迫这项律相等。

反向，每条 $C_\ell$ 路径都是 $H$ 路径，故 $C_\ell\subseteq C$。因此

$$
(\ell,[k]_{C_\ell})\longmapsto(\ell,[k]_C)
$$

是良定义的确定性后处理，给出 $V\preceq U$；第一项说明 $V$ 是共同下界。如果 $W$ 在每个 $C$ 类上恒定，从 $V$ 的输出 $(\ell,B)$ 保留 $\ell$，并按该类任一代表 $k_B$ 的律 $W_{k_B}$ 抽样，即模拟 $E_W$。这对全部 $(\ell,B)\in\mathcal V$ 定义了核，且在每条实际行上正确，故 $E_W\preceq V$。最后，由 $V$ 为共同下界和序的传递性，$E_W\preceq V$ 又推出 $E_W$ 为共同下界。完整分类及最大性成立。

证明第三项。若 $C\subseteq R$，编码 $k\mapsto[k]_C$ 只合并相容情境，由式（535.11）充分；其实际实验 $V$ 已是共同下界，故最小。反之，若某个 $E_W$ 最小充分，第二项强迫 $W_k=W_{k'}$ 对所有 $kCk'$ 成立。若还有 $\neg R(k,k')$，充分性又要求 $W_k\perp W_{k'}$。同一个概率律不可能与自身奇异，矛盾。因此 $C\subseteq R$ 必须成立。

当这个条件成立时，同一 $C$ 类中共享 $\ell$ 的两情境必 $R$-相容，故在 $K_\ell$ 内直接属于同一 $C_\ell$ 类。对每个实际 $V$ 值 $(\ell,B)$，在 $B\cap K_\ell$ 任选 $k$，输出 $(\ell,[k]_{C_\ell})$，便给出 $V$ 到 $U$ 的确定性后处理；在非实际值上取固定回退值即可。结合 $V\preceq U$ 得 $U\simeq V$。若条件失败却存在 $E_W\simeq U$，则 $E_W$ 由第一项充分且低于所有充分允许实验，成为最小元，与必要性矛盾。

若比较范围只含确定性充分编码，恒等编码和每个相容对的合并编码仍在其中。对一个确定性最小元逐条重复第二项的必要性论证，同样强迫其标签在 $C$ 类上相等，再由充分性推出 $C\subseteq R$；满足此条件的有限确定性 $V$ 已低于全部随机充分实验。因此确定性与随机类的存在条件完全相同。

这也准确接回第 532 章：其共同锚使 $O=K\times K$，于是 $C$ 是 $R$ 的等价闭包，$C\subseteq R$ 恰为自反对称关系 $R$ 的传递性。命题 532.6 的无锚域 $A_0$ 则只有 $a,c$ 实际交叠且互不相容，故 $H$ 没有非对角边，$C$ 为对角关系，仍有最小实际实验；不能仅凭该域 $R$ 不传递否定最小性。一般的允许 meet 讨论见第 130、443 章；这里式（535.7）和（535.8）分别识别两种比较范围的具体最大共同下界。Bertschinger–Rauh 的 Theorem 19 说明一般 Blackwell 实验序不是格，并不排除本充分族具有式（535.7）的特殊结构。[arXiv:1401.3146v1, §5](https://arxiv.org/html/1401.3146v1)。

最后将存在条件与已有安全计算判据作精确对应。仅在此对应中，任选概率律 $\pi$，满足

$$
\pi(k,\ell)>0\iff(k,\ell)\in S,
\qquad\sum_{(k,\ell)\in S}\pi(k,\ell)=1.
$$

令随机变量 $(\mathsf K,\mathsf L)$ 服从 $\pi$，并令

$$
\mathsf U=u(\mathsf K,\mathsf L),\qquad
u(k,\ell)=(\ell,[k]_{C_\ell}),\qquad
\operatorname{Law}(M\mid\mathsf K=k,\mathsf L=\ell)=W_k.
$$

$\pi$ 对实际单元满支撑，绝不要求 $S=K\times L$。消息 $M$ 只读 $\mathsf K$，所以 $M\perp(\mathsf L,\mathsf U)\mid\mathsf K$ 自动成立。对 $\mathsf U$ 正确恢复再加接收端隐私

$$
M\perp\mathsf K\mid(\mathsf L,\mathsf U)
\tag{535.14}
$$

等价于该消息实验与 $U$ 互相支配。具体地，正确恢复给出 $U\preceq E_W$；由于 $\pi$ 在每个实际单元上为正，式（535.14）恰说在每个固定 $(\ell,u)$ 的实际纤维上所有 $W_k$ 相等，从而按该公共律模拟消息并附上 $\ell$，得到 $E_W\preceq U$。反之，$E_W\preceq U$ 强迫这些行相等，故有式（535.14）；恢复方向提供正确性。标准 Borel 消息在有限条件变量下的条件律可逐格给出，无需给零质量的非实际单元添加约束。第一项及第三项遂把“存在这种安全计算消息”与“存在最小充分允许实验”对应起来。

在 Data, *Secure Computation of Randomized Functions*, Definitions 1–3、Theorem 1 中，取其输入 $X=\mathsf K$、侧信息 $Y=\mathsf L$、输出 $Z=\mathsf U$，并取确定性输出核 $p_{Z\mid XY}(\cdot\mid k,\ell)=\delta_{u(k,\ell)}$；这个输出核在 $(k,\ell)\in S$ 上按所示公式指定，在非实际单元可统一取固定 $\delta_{u_0}$，而不增添任何正概率单元。其 $Z$ 在此是计算目标，不能与本章辅助空间 $Z$ 混同。该文相邻关系添上对角后变为

$$
kJk'\iff\exists\ell,\quad
k,k'\in K_\ell\ \land\ [k]_{C_\ell}=[k']_{C_\ell}.
$$

其等价闭包正是 $C$：$H\subseteq J$，而每条 $J$ 边本身可在某个 $K_\ell$ 内展开成 $H$ 路径，故 $J\subseteq C$。列单色条件是每个 $C$ 类在同一实际列 $\ell$ 上有相同的 $u(k,\ell)$。若该条件成立，$U$ 决定 $T$ 使 $kCk'$ 的每个共同列目标相等，故 $C\subseteq R$；反之，若 $C\subseteq R$，同类且共列的两点直接 $R$-相连，其 $C_\ell$ 类相同，列单色成立。Data 的定理及发送等价类标签的单消息构造因而给出式（535.9）的已有安全计算路线；其证明中的消息律沿闭包相等，正是这里应归属给既有理论的机制。[Deepesh Data, arXiv:1601.06562v2](https://arxiv.org/html/1601.06562v2)，ISIT 2016，[doi:10.1109/ISIT.2016.7541860](https://doi.org/10.1109/ISIT.2016.7541860)。

这项对应须先识别整个充分族的 $U$；若直接把输出取为原目标 $T$ 并要求 $M\perp\mathsf K\mid(\mathsf L,T)$，则额外禁止了超出 $(q,T)$ 的所有情境披露，条件更强，命题 535.6 给出严格区别。Data–Prabhakaran, *Secure Computation of Randomized Functions: Further Results*, 条件（3）—（5）也分别列出只读发送端输入、正确计算与接收端隐私；其 Theorems 1–2 与 Remark 1 讨论带隐私和不带隐私的速率，不能以其中一个标量最优速率代替式（535.7）—（535.8）的实际实验序分类。[arXiv:1705.07081](https://arxiv.org/html/1705.07081)。证毕。

### 命题 535.5（无共同锚的六行支撑与连续多个极小充分实验）

令 $A$ 恰含下列六个对象，一次性给定它们的 $(c,q,T)$：

$$
\begin{array}{c|ccc}
x&c(x)&q(x)&T(x)\\\hline
a_u&a&u&0\\
b_u&b&u&0\\
b_v&b&v&0\\
c_v&c&v&0\\
a_w&a&w&0\\
c_w&c&w&1
\end{array}
\tag{535.15}
$$

对每个 $p\in[0,1]$，取二元辅助空间 $\{0,1\}$ 及通道

$$
W_a^p=\delta_0,\qquad
W_b^p=(1-p)\delta_0+p\delta_1,\qquad
W_c^p=\delta_1,
\qquad E_p=E_{W^p}.
\tag{535.16}
$$

则每个 $E_p$ 都充分，且在允许任意标准 Borel 输出的整个 $\mathcal F_T$ 中极小；并有

$$
\forall p,r\in[0,1],\qquad E_r\preceq E_p\iff r=p.
\tag{535.17}
$$

所以这是连续多个两两不可比较、互不等价的极小充分实验，其中 $p=0,1$ 是确定性端点。该支撑无共同锚，没有最小充分允许实验，而且作为实际实验

$$
U\simeq(q,T),\qquad V\simeq q.
\tag{535.18}
$$

前一等价类没有 $\Gamma_c$ 中的代表，后一实验在 $w$ 上不充分；式（535.18）不是编码器之间的全局恒等式。

**证明。** 每个实际 $(k,\ell)$ 只有一行，局部一致性成立。只有 $a,c$ 不相容，冲突由 $w$ 见证；$a,b$ 在 $u$ 交叠且相容，$b,c$ 在 $v$ 交叠且相容。因此 $H$ 包含路径 $a-b-c$，$C$ 是全关系而不包含于 $R$。三个活动情境集分别为 $\{a,b\},\{b,c\},\{a,c\}$，没有一个读数被全部情境共享。式（535.16）的 $a,c$ 两律奇异，由式（535.11）每个 $E_p$ 充分；也可直接在 $u,v$ 恒输出 $0$，在 $w$ 输出所见辅助位。

为证全输出类中的极小性，任取 $E_F\in\mathcal F_T$，其辅助输出空间为任意非空标准 Borel 空间 $Z'$，并假设 $E_F\preceq E_p$。由式（535.10）的归约，存在按源读数选择的核 $G_u,G_v,G_w:\{0,1\}\to\operatorname{Prob}(Z')$。在 $u$ 的两条实际行上有

$$
F_a=G_u(\cdot\mid0),\qquad
F_b=(1-p)F_a+pM,
\quad M=G_u(\cdot\mid1).
$$

在 $v$ 的两条实际行上有

$$
F_c=G_v(\cdot\mid1),\qquad
F_b=(1-p)N+pF_c,
\quad N=G_v(\cdot\mid0).
$$

此处 $M,N$ 是概率律，由处处定义的核取得；当系数为零时也没有除法或未定义条件律。于是对所有可测 $B\subseteq Z'$ 同时成立

$$
F_b(B)\ge(1-p)F_a(B),\qquad
F_b(B)\ge pF_c(B).
\tag{535.19}
$$

充分性在实际读数 $w$ 上强迫 $F_a\perp F_c$。取可测分离集 $B_0$，使 $F_a(B_0)=1,F_c(B_0)=0$。对任意可测 $B$，分别在 $B\cap B_0$ 与 $B\setminus B_0$ 上使用式（535.19），得

$$
\begin{aligned}
F_b(B)
&\ge (1-p)F_a(B\cap B_0)+pF_c(B\setminus B_0)\\
&=(1-p)F_a(B)+pF_c(B).
\end{aligned}
$$

故 $F_b-(1-p)F_a-pF_c$ 是非负测度，其总质量为 $1-(1-p)-p=0$，只能为零；所以

$$
F_b=(1-p)F_a+pF_c.
\tag{535.20}
$$

由可测映射 $s(z')=0$（$z'\in B_0$）及 $s(z')=1$（$z'\notin B_0$），三律依次推前为 $\delta_0,(1-p)\delta_0+p\delta_1,\delta_1$。保留原来观察到的 $q$ 并输出 $s(z')$，便得到 $E_p\preceq E_F$。因此 $E_p$ 极小，证明范围包含每个标准 Borel 竞争通道，并非只检验二元或确定性竞争者。

若取 $E_F=E_r$，式（535.19）在辅助输出的单点 $\{0\}$ 上给出 $1-r\ge1-p$，在 $\{1\}$ 上给出 $r\ge p$，故 $r=p$；反向是恒等后处理。全部论证只用非负系数，没有除以 $p$ 或 $1-p$，所以也覆盖两个端点。在 $p=0$ 时式（535.20）就是 $F_b=F_a$，在 $p=1$ 时就是 $F_b=F_c$。

具体计算局部类：$C_u$ 只有块 $\{a,b\}$，$C_v$ 只有块 $\{b,c\}$，$C_w$ 则是 $\{a\},\{c\}$ 两块。因此 $U$ 的实际纤维为

$$
\{a_u,b_u\},\quad\{b_v,c_v\},\quad\{a_w\},\quad\{c_w\},
$$

与 $(q,T)$ 恰相同，有限实际像上的互相重命名证明前一等价。$C$ 只有一个类，所以 $V$ 与 $q$ 互相确定，且 $q(a_w)=q(c_w)$ 而目标不同。定理 535.4 已给出最小元不存在以及 $U$ 不可由允许通道实现到实验等价。还可直接看出：若 $E_W\preceq U$，前两个 $U$ 纤维强迫 $W_a=W_b$ 和 $W_b=W_c$；若同时充分，$w$ 又强迫 $W_a\perp W_c$，矛盾。

最后，当 $0<p<1$ 时，$E_p$ 不与任何确定性情境编码等价。若某个确定性充分 $Q_z$ 满足 $Q_z\preceq E_p$，式（535.20）给出

$$
\delta_{z(b)}=(1-p)\delta_{z(a)}+p\delta_{z(c)},
$$

而充分性要求 $z(a)\ne z(c)$，右端在两个不同单点各有正质量，不能是 Dirac 律。因此随机化确实添加了确定性情形没有的极小等价类，却仍未产生最小元。这不声称式（535.16）穷尽了全部极小实验。证毕。

### 命题 535.6（最小充分性不等于只披露当前目标）

令实际域恰为四行

$$
\begin{array}{c|ccc}
x&c(x)&q(x)&T(x)\\\hline
d_{au}&a&u&0\\
d_{bu}&b&u&0\\
d_{av}&a&v&0\\
d_{bv}&b&v&1
\end{array}
\tag{535.21}
$$

则 $R=C=\operatorname{diag}_{\{a,b\}}$，最小充分允许实验由 $(q,c)$ 给出。任一充分允许实验在 $q=u$ 时也必能概率一辨认情境，尽管那两行的目标相同；没有充分允许实验与 $(q,T)$ 等价。

**证明。** $v$ 的两行目标不同，故 $a,b$ 不相容；因此 $R,H,C$ 都只有对角对，每个 $C_\ell$ 类也是单点。定理 535.4 给出 $V\simeq(q,c)$ 最小且 $U\simeq V$。对任一充分编码 $W$，式（535.11）要求 $W_a\perp W_b$。取相应可测分离集即可在 $u$ 也辨认 $a,b$，因为只读情境的同一个 $W_a,W_b$ 跨读数使用，不能在 $u$ 改成相同律而在 $v$ 改回不同律。

若某个充分 $E_W$ 与 $(q,T)$ 等价，后处理方向 $E_W\preceq(q,T)$ 在 $d_{au},d_{bu}$ 的相同输入 $(u,0)$ 上只能输出同一个律，故 $\delta_u\otimes W_a=\delta_u\otimes W_b$，即 $W_a=W_b$，与奇异性矛盾。对实际四行赋任何严格正先验，要求消息满足 $M\perp\mathsf K\mid(\mathsf L,T)$ 同样会在 $(u,0)$ 上强迫两律相等；所以相对于原目标的这项完美隐私条件不可行，而最小充分实验仍存在。这说明定理 535.4 的安全计算对应必须用派生目标 $U$，不可悄然以原目标隐私取代最小性。这里的额外披露是同一取得约束下被迫发生的可区分性，并不从数学事实推出该披露在任何实际用途中的许可。证毕。

## 追加锚（本行以下为增补区）

## 536. 可见随机种子与极小概念：同一实际支撑上的完整比较

第 535 章把一个目的所需的精确区分，与辅助信息实际上怎样取得分开。本章再固定观察者能否看到编码时的全部随机选择。在同一组实际对象、同一个目标和同一种后处理序下，这一差别会改变极小充分实验。下面给出任意有限多个叶情境的完整分类，并把任意充分通道与全部公开随机化实验作双向比较。第 535.5 项已给出两个叶情境时的连续多个私有极小元；本章补足它未声称的穷尽性，以及公开规范形和任意通道的跨类关系，不重述第 535.4 项的两种共同下界定理。下文 $m=2$ 时的 $a_1,a_2$ 对应第 535.5 项的 $a,c$，参数向量 $(1-t,t)$ 对应该项的二元随机参数 $t$。

### 定义 536.1（固定实际支撑与全部随机位的可见性）

固定整数 $m\ge2$。情境集为 $K=\{b,a_1,\ldots,a_m\}$，其中 $b$ 称为中心，$a_i$ 称为叶。所有读数 $u_i$（$1\le i\le m$）和 $v_{ij}$（$1\le i<j\le m$）两两不同。实际对象集 $A$ 恰有下列 $(c,q,T)$ 行，每行一个对象：

$$
\begin{aligned}
&(b,u_i,0),\ (a_i,u_i,0) &&(1\le i\le m),\\
&(a_i,v_{ij},0),\ (a_j,v_{ij},1) &&(1\le i<j\le m).
\end{aligned}
\tag{536.1}
$$

因此 $|A|=2m+2\binom m2=m(m+1)$，$K=c(A)$，$L=q(A)$，$Y=T(A)=\{0,1\}$。每个读数只有两个活动情境；实际支撑没有补成 $K\times L$。编码端只读情境 $c(x)$。对任意非空标准 Borel 空间 $Z$ 和核 $W:K\to\operatorname{Prob}(Z)$，记

$$
\nu=W_b,\qquad \mu_i=W_{a_i},\qquad
E_W(x)=\delta_{q(x)}\otimes W_{c(x)}.
\tag{536.2}
$$

观察者看到 $(q,z)$。充分性指存在可随机化的解码核 $D:L\times Z\to\operatorname{Prob}(Y)$，使每个实际对象满足

$$
\int_Z D(\{T(x)\}\mid q(x),z)W_{c(x)}(dz)=1.
\tag{536.3}
$$

没有先验平均的替代条件。沿用第 535 章的序：$F\preceq E$ 当且仅当存在一个不额外依赖实际对象的 Markov 核，将每条 $E_x$ 送到 $F_x$；左端信息较少。核可以读取源输出里的 $q$。互相支配写作 $E\simeq F$，$E\prec F$ 表示 $E\preceq F$ 且反向不成立。最小元须低于同一充分族的每个成员；极小元只要求低于自身的充分成员均与自身等价。以下分类均按实际实验的等价类理解。

式（535.10）在这里提供一个可直接使用的归约。若 $E_F\preceq E_W$，从任意模拟核 $G:L\times Z\to\operatorname{Prob}(L\times Z')$ 取辅助输出的边缘，便得到

$$
G_\ell(B\mid z)=G(L\times B\mid\ell,z),\qquad
F_k=\int_ZG_\ell(\cdot\mid z)W_k(dz)
\quad\text{对每个实际 }(k,\ell).
\tag{536.4}
$$

反之，把这些核拼成 $(\ell,z)\mapsto\delta_\ell\otimes G_\ell(\cdot\mid z)$ 就是一个全局核；$L$ 有限，故可测。这里没有假定原模拟器逐点保持 $q$，而是从实际行等式取边缘后，换得一个保持 $q$ 的代表。所有下文按读数构造的模拟器都由此归并为同一个状态无关核。

在支撑（536.1）上，不同叶情境在相应 $v_{ij}$ 上目标相反，中心与任一叶的共同读数则只有 $u_i$，目标同为零。因此式（535.11）恰化为

$$
E_W\text{ 充分}\quad\Longleftrightarrow\quad
\mu_i\perp\mu_j\quad(i\ne j).
\tag{536.5}
$$

中心律 $\nu$ 没有其他充分性约束。互相奇异是可测分离条件，不是拓扑支撑不交。

称全部这些充分 $E_W$ 组成私有允许族 $\mathcal F_{\mathrm{priv}}$：它允许编码器把自己的随机位隐藏在 $W_k$ 中，也允许输出更多内容。公开充分族 $\mathcal F_{\mathrm{pub}}$ 则要求辅助输出具有表示

$$
(R,f(R,k)),\qquad R\sim\rho,\qquad
f:\mathcal R\times K\to Z\text{ 可测},
\tag{536.6}
$$

其中 $\mathcal R,Z$ 是任意非空标准 Borel 空间，$\rho$ 对每个实际状态都是同一个概率律，且给定 $(R,k)$ 后 $f$ 是确定性的。整个 $R$ 被观察者看到；没有留在 $f$ 内的隐藏编码随机位。解码器和模拟器仍可使用自己的随机化。这是 $\mathcal F_{\mathrm{priv}}$ 的子族，两类并不互斥。“公开／私有”只描述编码种子的可见性，不表示隐私保证，也不借用某种通信复杂度中的额外约定。种子自身与状态独立，不表示它与消息合看时仍不提供状态信息。

### 引理 536.2（三种质量与共同叶分划）

对任意充分 $E_W$，令 $\eta_i=\nu+\mu_i$，取非负 Radon–Nikodym 密度 $h_i=d\nu/d\eta_i$、$g_i=d\mu_i/d\eta_i$，定义

$$
\begin{aligned}
\lambda_i&=\int_{\{g_i>0\}}h_i\,d\eta_i,
&\beta_i&=\int_{\{h_i>0\}}g_i\,d\eta_i,\\
\kappa_i&=\int_Z\min(h_i,g_i)\,d\eta_i,
&d_i&=\max\{\lambda_i,\beta_i\}.
\end{aligned}
\tag{536.7}
$$

$\lambda_i$ 是 $\nu$ 相对于 $\mu_i$ 的绝对连续部分的总质量；$\beta_i$ 是反方向的绝对连续质量；$\kappa_i$ 是最大共同子测度 $\nu\wedge\mu_i$ 的质量。它们不依赖密度版本，并且

$$
0\le\kappa_i\le\min\{\lambda_i,\beta_i\}\le d_i\le1,
\qquad \sum_{i=1}^m\lambda_i\le1,
\qquad \sum_{i=1}^m\kappa_i\le1.
\tag{536.8}
$$

还存在可测分划 $Z=D_0\sqcup D_1\sqcup\cdots\sqcup D_m$，满足

$$
\mu_i(D_i)=1,\qquad
\nu|_{D_i}=\nu^{\mathrm{ac}(\mu_i)},\qquad
\nu(D_i)=\lambda_i,\qquad
\nu(D_0)=1-\sum_i\lambda_i.
\tag{536.9}
$$

证明：在单对测度中，$\nu|_{\{g_i>0\}}\ll\mu_i$，因为 $\mu_i(B)=0$ 强迫 $g_i=0$ 在 $B$ 上 $\eta_i$ 几乎处处。其余部分集中在 $\mu_i$ 的零集 $\{g_i=0\}$ 上，故是奇异部分。Lebesgue 分解的唯一性识别出 $\lambda_i$；交换两律就得到 $\beta_i$。测度 $\min(h_i,g_i)\eta_i$ 同时不超过两律。若 $H\le\nu,\mu_i$，则 $H\ll\eta_i$，其密度同时不超过 $h_i,g_i$，从而 $H\le\min(h_i,g_i)\eta_i$。这证明共同子测度的最大性及前三个量的内在定义，也给出逐坐标不等式。

为取得同一分划，使用 $\eta=\nu+\sum_i\mu_i$，记 $n=d\nu/d\eta$、$w_i=d\mu_i/d\eta$。叶律两两奇异，故 $w_iw_j=0$ 在 $\eta$ 几乎处处成立。把有限个这样的例外、密度非负有限及 $n+\sum_iw_i=1$ 的例外合入一个可测 $\eta$-零集 $N$，令

$$
D_i=\{z\notin N:w_i(z)>0\}\quad(1\le i\le m),
\qquad D_0=Z\setminus\bigcup_iD_i.
\tag{536.10}
$$

这些 $D_i$ 两两不交且 $\mu_i(D_i)=1$。与单对密度的论证相同，$\nu|_{D_i}\ll\mu_i$，$\nu|_{Z\setminus D_i}\perp\mu_i$，所以由同一个 Lebesgue 分解唯一性，$\nu|_{D_i}$ 正是式（536.7）定义的绝对连续部分。于是 $\sum_i\lambda_i=\nu(\bigcup_iD_i)\le1$；共同子测度质量的总和也不超过一。证毕。

这些质量不是常数支配系数 $\sup\{c\ge0:\nu\ge c\mu_i\}$；绝对连续部分可以只占 $\mu_i$ 所承载区域的一部分，也可以有变化的密度。符号 $\nu\wedge\mu_i$ 在此只指测度的最大共同子测度，不表示 Blackwell 实验序中的格交，更不依赖另选一个拓扑后的“支撑交集”。

### 引理 536.3（一般二态实验与对称擦除的双向比较）

令 $P,Q$ 是任意非空标准 Borel 空间 $Z$ 上的概率律。二态实验 $(P,Q)$ 分别在状态 $0,1$ 输出这两律；$B_t$（$0\le t\le1$）在每个状态以概率 $t$ 输出擦除符号 $\star$，以概率 $1-t$ 无误输出该状态。记

$$
C=P\wedge Q,\qquad
\alpha=P^{\mathrm{ac}(Q)}(Z),\qquad
\gamma=Q^{\mathrm{ac}(P)}(Z).
$$

按同一状态无关 Markov 后处理序，有

$$
(P,Q)\preceq B_t\quad\Longleftrightarrow\quad t\le C(Z),
\qquad
B_t\preceq(P,Q)\quad\Longleftrightarrow\quad t\ge\max\{\alpha,\gamma\}.
\tag{536.11}
$$

证明第一式。若 $K$ 把 $B_t$ 送到 $(P,Q)$，则 $tK(\cdot\mid\star)$ 是两律的共同子测度，故 $t\le C(Z)$。反之，$t=0$ 时在已揭示的状态 $0,1$ 上分别抽样 $P,Q$ 即可，零概率的擦除输入任取一个概率律。当 $0<t<1$ 且 $t\le c=C(Z)$ 时，令 $H=(t/c)C$；这是质量 $t$ 的共同子测度。令

$$
K(\cdot\mid\star)=H/t,\qquad
K(\cdot\mid0)=(P-H)/(1-t),\qquad
K(\cdot\mid1)=(Q-H)/(1-t).
$$

三者都是概率律，所得状态行恰为 $P,Q$。最后，$t=1$ 时判据强迫 $C(Z)=1$，于是 $P=Q=C$；从唯一实际出现的 $\star$ 抽样这个公共律即可。

证明第二式。若 $K$ 把 $(P,Q)$ 送到 $B_t$，令 $e_0(z)=K(\{0\}\mid z)$。因为状态 $1$ 不能输出 $0$，有 $\int e_0\,dQ=0$，所以 $e_0=0$ 在 $Q$ 几乎处处，进而在 $P^{\mathrm{ac}(Q)}$ 几乎处处也为零。因此

$$
1-t=\int e_0\,dP\le P^{\mathrm{s}(Q)}(Z)=1-\alpha.
$$

交换状态得到 $t\ge\gamma$。这解释了必要条件为什么使用两个方向的绝对连续质量：能够无误宣布某个状态的输出，只能来自该状态相对另一状态的奇异部分。

反之，取 $\xi=P+Q$，$p=dP/d\xi$，$q=dQ/d\xi$，并取不交的可测集

$$
H_0=\{p>0,q=0\},\qquad H_1=\{q>0,p=0\}.
$$

它们分别满足 $P(H_0)=1-\alpha$、$Q(H_1)=1-\gamma$，且 $Q(H_0)=P(H_1)=0$。若 $t<1$ 且判据成立，这两个质量都至少为 $1-t>0$。在 $H_0$ 上以概率 $(1-t)/(1-\alpha)$ 输出 $0$，在 $H_1$ 上以概率 $(1-t)/(1-\gamma)$ 输出 $1$；其他概率全部输出 $\star$。分母为正，概率不超过一，两集不交，故得到一个处处定义的可测核，其两条状态行就是 $B_t$。若 $t=1$，恒输出 $\star$。特别地，$t=0$ 的第二个判据恰要求 $P\perp Q$，上述构造此时完整揭示状态。证毕。

这只是 Lebesgue 分解与共同子测度的经典测度论应用；证明在任意标准 Borel 输出上给出了所需的核，不把有限矩阵结论直接当作无限输出结论。

### 定理 536.4（私有极小元的穷尽及任意通道之下的剩余单纯形）

令

$$
\Delta_{m-1}=\{p\in[0,1]^m:\sum_ip_i=1\}.
$$

对 $p\in\Delta_{m-1}$，定义辅助空间 $\{1,\ldots,m\}$ 上的规范通道

$$
W^{p}_{a_i}=\delta_i,\qquad W^{p}_b=\sum_ip_i\delta_i,
\qquad E_p=E_{W^p}.
\tag{536.12}
$$

每个 $E_p$ 充分。对任意充分 $E_W$ 及任意 $p\in\Delta_{m-1}$，有

$$
\begin{aligned}
E_p\preceq E_W
&\quad\Longleftrightarrow\quad p_i\ge\lambda_i\quad(1\le i\le m),\\
E_W\preceq E_p
&\quad\Longleftrightarrow\quad \nu=\sum_ip_i\mu_i.
\end{aligned}
\tag{536.13}
$$

全部 $E_p$ 都是 $\mathcal F_{\mathrm{priv}}$ 的极小元，不同参数的 $E_p$ 两两不可比，并穷尽该族的全部极小等价类。因此任意 $E_W$ 支配的私有极小类恰由

$$
\{p\in\Delta_{m-1}:p\ge\lambda\}
=\lambda+\left(1-\sum_i\lambda_i\right)\Delta_{m-1}
\tag{536.14}
$$

参数化；此集总非空，是一个平移、缩放后的剩余单纯形，一般不是原单纯形的一个面。任意 $E_W$ 本身极小，当且仅当 $\nu=\sum_ip_i\mu_i$ 对某个 $p\in\Delta_{m-1}$ 成立；这时 $p$ 唯一。$m\ge2$ 时，私有充分族没有最小元。

证明：叶 Dirac 律两两奇异，先得 $E_p$ 充分。若 $E_p\preceq E_W$，在读数 $u_i$ 上使用式（536.4）的核 $K_i$。叶行要求

$$
K_i(\{i\}\mid z)=1\quad\mu_i\text{ 几乎处处}.
$$

同一等式因绝对连续性也在 $\nu^{\mathrm{ac}(\mu_i)}$ 几乎处处成立。中心行则给出

$$
p_i=\int K_i(\{i\}\mid z)\nu(dz)\ge\lambda_i.
$$

为证充分性，取引理 536.2 的共同分划，记 $s=\sum_i\lambda_i$。若 $s<1$，在 $D_i$ 上输出 $i$，在 $D_0$ 上按概率向量

$$
\left(\frac{p_i-\lambda_i}{1-s}\right)_{i=1}^m
$$

抽样。非负性和总和为一来自 $p\ge\lambda$。这个分离核不需要读取 $q$，把每个叶律送到 $\delta_i$，把中心律送到 $p$。若 $s=1$，则 $p=\lambda$；$D_0$ 对所有行都为零，那里任取一个标签即可，无须相除。第一式成立。

若反向 $E_W\preceq E_p$，在 $u_i$ 上的核必须把源标签 $i$ 送到 $\mu_i$；对中心行因而有测度不等式 $\nu\ge p_i\mu_i$。取同一个不交叶分划，对任意可测 $B$ 得

$$
\nu(B)\ge\sum_i\nu(B\cap D_i)
\ge\sum_ip_i\mu_i(B\cap D_i)=\sum_ip_i\mu_i(B).
$$

右端质量为一，所以非负差测度的总质量为零，必有 $\nu=\sum_ip_i\mu_i$。反之，若这个等式成立，从标签 $i$ 抽样 $\mu_i$ 即把 $E_p$ 送到 $E_W$；按 $D_i$ 分离又把 $E_W$ 送回 $E_p$。这两个核同样不需要读取 $q$。混合权重由 $p_i=\nu(D_i)$ 唯一确定，包括 $p_i=0$ 的情形。

现在任取充分 $E_W\preceq E_p$，第二式强迫这个混合等式，所以也有 $E_p\preceq E_W$；这证明每个 $E_p$ 在整个标准 Borel 允许族中极小。以 $E_W=E_r$ 代入第二式，Dirac 叶律使中心混合权重必须为 $p=r$，故不同参数不可比。

对任意充分 $E_W$，式（536.8）保证总能选到 $p\ge\lambda$ 且 $\sum_ip_i=1$；第一式给出一个 $E_p\preceq E_W$。若 $E_W$ 极小，它必须与这个 $E_p$ 等价，再由第二式得到混合条件。因此没有遗漏其他极小等价类，式（536.14）也随之成立。特别地，当 $s=1$ 时只剩 $p=\lambda$ 这一类；但仅有唯一一个受支配的极小类，不强迫 $E_W$ 自身极小，仍须满足混合等式。最后，至少两个不同的单纯形顶点给出不同极小类；若最小元存在，它低于这两个极小元，便须同时与二者等价，矛盾。证毕。

### 定理 536.5（全可见种子的有限规范形与公开极小前沿）

令

$$
Q_m=\{r\in[0,1]^m:\sum_ir_i\le1\},\qquad r_0=1-\sum_ir_i.
$$

对 $r\in Q_m$，定义公开规范实验 $P_r$：种子 $I\in\{0,1,\ldots,m\}$ 与状态独立，$\Pr(I=i)=r_i$；所有叶情境 $a_j$ 在每个种子上都发送标签 $j$，中心在 $I=i\ge1$ 时发送标签 $i$，在 $I=0$ 时发送新标签 $0$。辅助输出是完整的 $(I,\text{标签})$，再与原 $q$ 一同观察。叶标签两两不同，所以每个 $P_r$ 都由式（536.5）充分。

每个公开充分实验都与唯一的 $P_r$ 等价，并且

$$
P_s\preceq P_r\quad\Longleftrightarrow\quad
s_i\ge r_i\quad(1\le i\le m).
\tag{536.15}
$$

公开极小类恰为 $\sum_ir_i=1$ 的 $P_r$；$P_0$ 是公开充分族的最大元，$m\ge2$ 时该族没有最小元。

证明规范形。对一个式（536.6）的充分实验，记 $f_i(R)=f(R,a_i)$、$f_b(R)=f(R,b)$。标准 Borel 空间的对角线可测，故各相等集合 $\{f_i=f_j\}$、$\{f_b=f_i\}$ 可测。若 $\rho\{f_i=f_j\}>0$，将 $\rho$ 限制到这个集合，再沿 $R\mapsto(R,f_i(R))$ 推前，就得到叶 $i,j$ 两个输出律的非零共同子测度，违反它们的奇异性。因此每个相等集合都是 $\rho$-零集。因 $m$ 有限，其并是一个共同零集 $N$，在 $\mathcal R\setminus N$ 上所有叶输出同时不同。

在那里令

$$
S_i=\{R\notin N:f_b(R)=f_i(R)\}\quad(1\le i\le m),
\qquad S_0=\mathcal R\setminus\bigcup_iS_i,
\qquad r_i=\rho(S_i).
\tag{536.16}
$$

这些集合组成可测分划；$N$ 被收入 $S_0$，不影响其概率。因为一个中心值至多等于一个叶值，$S_i$ 两两不交，故 $r\in Q_m$。

从原辅助输出 $(R,z)$ 模拟规范输出时，先读取 $R$ 所在的 $S_I$；若 $z=f_j(R)$，输出标签 $j$，否则输出 $0$。在 $N$ 上或多个叶相等的输入上任取固定回退规则，例如选最小下标。有限次可测相等判定保证这个映射可测。每条实际叶行给出标签 $j$，中心行在 $S_i$ 上给出标签 $i$，在 $S_0\setminus N$ 上给出 $0$，所得律恰为 $P_r$。

反向，对每个 $r_i>0$ 的分块取概率律

$$
\rho_i(B)=\frac{\rho(B\cap S_i)}{r_i}.
\tag{536.17}
$$

收到规范输出 $(i,j)$ 时，先按 $\rho_i$ 抽样 $R$；若 $j\ge1$，输出 $(R,f_j(R))$；若 $j=0$，输出 $(R,f_b(R))$。对中心在 $i\ge1$ 的实际输出，必有 $j=i$，且 $f_i=f_b$ 在 $S_i$ 上成立，所以这个规则也恢复中心律。叶 $a_j$ 则在每个分块恢复 $(R,f_j(R))$。将各分块按 $r_i$ 混合就恢复原来的整个种子及消息联合律。零质量分块和不可达输入可以统一改用输出空间中一个固定点的 Dirac 律；从未对单个种子取条件概率。有限输入上的抽样核可测。两个方向均可附回 $q$，故证明的是实际实验等价，不是两个编码函数逐点相同。

接着比较规范形。在 $u_i$ 的中心、叶 $i$ 两行上，$P_r$ 唯一共同的符号是 $(I,\text{标签})=(i,i)$，两行在那里均有质量 $r_i$；其余输出能无误识别是哪一行。因此这一二态实验与 $B_{r_i}$ 等价：正向把共同符号送到 $\star$，其余符号送到相应状态；反向把 $\star$ 送到 $(i,i)$，对各已揭示状态按其余输出的归一化限制律抽样。$r_i=1$ 时只有共同符号实际出现，$r_i=0$ 时擦除输入不可达，均可任意填补未使用的核值，不做零分母运算。在 $v_{ij}$ 上，两叶的标签始终不同，故是完全可分的二态实验。

引理 536.3 对两擦除实验给出 $B_{s_i}\preceq B_{r_i}$ 当且仅当 $s_i\ge r_i$。各 $u_i$ 提供式（536.15）的必要性，各 $v_{ij}$ 无额外限制；充分性则将这些局部核按式（536.4）拼接。于是互相模拟强迫 $s=r$，规范参数唯一。

若 $\sum_ir_i<1$，增大一个坐标而保持总和不超过一，得到严格更低的公开充分实验；若 $\sum_ir_i=1$，$s\ge r$ 和 $s\in Q_m$ 只能给出 $s=r$。这证明极小前沿。所有 $s\in Q_m$ 都满足 $s\ge0$，所以 $P_s\preceq P_0$。两个不同单纯形顶点是不可比的公开极小类，排除最小元，论证与定理 536.4 相同。证毕。

### 定理 536.6（任意充分通道与全部公开实验的完整跨类序）

令 $E_W$ 是定义 536.1 的任意充分实验，$\lambda,\beta,\kappa,d$ 如式（536.7），令 $r\in Q_m$。则

$$
\boxed{\quad E_W\preceq P_r\iff r\le\kappa,\qquad
P_r\preceq E_W\iff r\ge d.\quad}
\tag{536.18}
$$

向量不等式均逐坐标理解。因此 $E_W$ 之下的公开等价类、以及其上的公开等价类分别为

$$
\begin{aligned}
\{[P_r]:P_r\preceq E_W\}
&=\{[P_r]:r\ge d,\ \sum_ir_i\le1\},\\
\{[P_r]:E_W\preceq P_r\}
&=\{[P_r]:0\le r\le\kappa\}.
\end{aligned}
\tag{536.19}
$$

前者非空当且仅当 $\sum_id_i\le1$，后者总包含 $P_0$。$E_W$ 的等价类中存在公开代表当且仅当

$$
\kappa_i=d_i\quad\text{对全部 }i;
\tag{536.20}
$$

成立时该代表的规范参数唯一，为 $P_\kappa$。两个实验的严格与不可比情形完整地写为

$$
\begin{aligned}
E_W\prec P_r
&\iff r\le\kappa\ \text{且 }r\not\ge d,\\
P_r\prec E_W
&\iff r\ge d\ \text{且 }r\not\le\kappa,\\
E_W\simeq P_r
&\iff r=\kappa=d,\\
E_W\text{ 与 }P_r\text{ 不可比}
&\iff r\not\le\kappa\ \text{且 }r\not\ge d.
\end{aligned}
\tag{536.21}
$$

证明：在每个实际读数 $u_i$ 上，$E_W$ 的两律是 $(\nu,\mu_i)$，$P_r$ 则与 $B_{r_i}$ 等价。引理 536.3 的第一式恰给出 $r_i\le\kappa_i$，第二式恰给出 $r_i\ge\max(\lambda_i,\beta_i)=d_i$。这些必要条件是逐读数从任何全局核边缘化得到的，未限制原全局核的形式。

反向，若相应的逐坐标判据成立，引理 536.3 在每个 $u_i$ 给出同方向的局部核。在每个 $v_{ij}$，$E_W$ 的两叶律互相奇异，$P_r$ 的两叶输出也互相奇异；从任一源实验的分离集识别叶行，再抽样目标的对应行律，即得到所需局部核。读数只有有限个，将它们按输入 $q$ 拼成一个 Markov 核，附回该 $q$，便在（536.1）的每一实际行上得到正确目标律。核使用的是已经观察到的读数，不使用隐藏状态，也没有添加支撑外的等式义务。这同时证明两方向的充分性。

第一集合有成员时必有 $\sum_id_i\le1$；反之取 $r=d$ 即可。因 $\sum_i\kappa_i\le1$，第二集合中的每个向量自动属于 $Q_m$。若两个方向同时成立，则 $d\le r\le\kappa$，再由 $\kappa\le d$ 得到 $r=\kappa=d$；反之这个等式直接给出等价。剩余三种情形是两个判据的其余真假组合，故无遗漏。证毕。

这里 $\lambda,\beta,\kappa$ 的作用不同：$\lambda$ 决定可从 $E_W$ 取得哪些私有极小类，$d$ 决定它能模拟哪些公开实验，$\kappa$ 决定哪些公开实验能模拟它。这些量给出了本定理的全部公开比较，并不声称分类了任意两个私有通道之间的所有比较。

### 推论 536.7（两个单纯形前沿只在顶点相遇）

对定理 536.4 的全部 $p\in\Delta_{m-1}$，包括任意面的边界，有

$$
\lambda_i(E_p)=\kappa_i(E_p)=p_i,\qquad
\beta_i(E_p)=d_i(E_p)=\mathbf1_{\{p_i>0\}}.
\tag{536.22}
$$

因此，对任意 $r\in Q_m$，

$$
E_p\preceq P_r\iff r\le p,
\qquad
P_r\preceq E_p\iff p=r=e_j\text{ 对某个单纯形顶点 }e_j.
\tag{536.23}
$$

尤其当 $p$ 不是顶点时，$E_p\prec P_p$；丢弃 $P_p$ 的种子坐标得到的正是 $E_p$，且 $E_p$ 是 $P_p$ 唯一支配的私有极小类。这时没有任何充分公开实验低于 $E_p$。私有极小前沿和公开极小前沿虽然都由 $\Delta_{m-1}$ 参数化，其代表实验的等价类只在 $m$ 个顶点相同；公开极小实验未必在整个私有允许族中极小。

证明：$\nu=\sum_jp_j\delta_j$、$\mu_i=\delta_i$，所以中心相对叶的绝对连续部分和共同子测度均为 $p_i\delta_i$。若 $p_i>0$，整个 $\delta_i$ 都绝对连续于 $\nu$；若 $p_i=0$，它与 $\nu$ 奇异。这证明式（536.22）。代入定理 536.6 得第一比较式。第二方向要求 $r_i\ge1$ 对每个正坐标 $p_i$ 成立，而 $\sum_ir_i\le1$；所以正坐标只能有一个，必为 $p_j=r_j=1$，其余均为零，反之显然成立。

当 $p$ 非顶点时，第一方向取 $r=p$ 成立而第二方向失败，得到严格支配。$P_p$ 的种子只取 $1,\ldots,m$，因为 $\sum_ip_i=1$；忘掉 $I$ 后叶 $a_j$ 恒发送 $j$，中心按 $p$ 发送标签，正好是 $E_p$。若另一个私有极小类 $E_s$ 低于 $P_p$，第一比较式强迫 $p\le s$，两者总和同为一，故 $s=p$。

最后，记 $J=\{i:p_i>0\}$。非顶点意味着 $|J|\ge2$，因而 $\sum_id_i=|J|>1$，由式（536.19）没有公开充分实验低于它。这覆盖全部正维面的相对内部及其非顶点边界；不需要全部坐标为正。式（536.23）还要求任何支配 $E_p$ 的 $P_r$ 在 $p_i=0$ 的坐标上满足 $r_i=0$。当 $J=\{j\}$ 时，$E_{e_j}\simeq P_{e_j}$；$P_r$ 支配它恰在 $r_i=0$（$i\ne j$）、$0\le r_j\le1$ 时成立，其中 $r_j<1$ 为严格支配，$r_j=1$ 为等价。在 $u_j$ 对应的二态实验上，$r_j=1$ 是完全擦除，$r_j=0$ 是完全揭示，故两个端点均已包含。证毕。

### 例 536.8（相同私有下前沿，仍有不同的公开比较）

取 $m=2$，辅助空间为七个不同点 $z_{10},z_{11},z_{12},z_{20},z_{21},z_{22},o$，令 $\delta_{ij}$ 表示 $z_{ij}$ 上的 Dirac 律。固定两个不交叶律

$$
\mu_i=\frac1{10}\delta_{i0}+\frac1{10}\delta_{i1}+\frac45\delta_{i2}
\quad(i=1,2).
$$

只改变中心律，定义三个充分实验 $E^{\mathrm A},E^{\mathrm B},E^{\mathrm C}$：

$$
\begin{aligned}
\nu_{\mathrm A}&=\frac15\mu_1+\frac15\mu_2+\frac35\delta_o,\\
\nu_{\mathrm B}&=\frac1{10}(\delta_{10}+\delta_{11}+\delta_{20}+\delta_{21})+\frac35\delta_o,\\
\nu_{\mathrm C}&=\frac15\delta_{10}+\frac15\delta_{20}+\frac35\delta_o.
\end{aligned}
\tag{536.24}
$$

三者均在每个叶区域上放置中心质量 $1/5$，所以都有 $\lambda=(1/5,1/5)$，受它们支配的私有极小类完全相同：

$$
\{E_{(t,1-t)}:1/5\le t\le4/5\}.
\tag{536.25}
$$

这个线段是 $\Delta_1$ 的真子线段，两个端点都不是 $\Delta_1$ 的顶点，具体说明式（536.14）一般不是原单纯形的面。

各质量直接由点质量相加及逐点取小值得到：

| 中心律 | $\lambda$ | $\beta$ | $\kappa$ | $d$ |
| --- | --- | --- | --- | --- |
| $\nu_{\mathrm A}$ | $(1/5,1/5)$ | $(1,1)$ | $(1/5,1/5)$ | $(1,1)$ |
| $\nu_{\mathrm B}$ | $(1/5,1/5)$ | $(1/5,1/5)$ | $(1/5,1/5)$ | $(1/5,1/5)$ |
| $\nu_{\mathrm C}$ | $(1/5,1/5)$ | $(1/10,1/10)$ | $(1/10,1/10)$ | $(1/5,1/5)$ |

具体而言，$\nu_{\mathrm A}$ 在每个叶的三个正质量点上都为正，所以反方向绝对连续质量为一；其在该叶上的限制是 $\mu_i/5\le\mu_i$，共同质量为 $1/5$。$\nu_{\mathrm B}$ 只占据每个叶的前两个点，那里中心与叶质量逐点相等，合计 $1/5$，故反方向质量和共同质量均为 $1/5$。$\nu_{\mathrm C}$ 只占据每个叶的第一个点，叶在那里只有 $1/10$，中心有 $1/5$，所以反方向质量和共同质量均为 $1/10$。这也使所有表项的方向清楚可见。

$E^{\mathrm A}$ 之下没有充分公开实验，因为 $d_1+d_2=2$；$E^{\mathrm B}$ 与 $E^{\mathrm C}$ 之下的公开参数却恰为

$$
\{r\in Q_2:r_1\ge1/5,\ r_2\ge1/5\}.
\tag{536.26}
$$

另一方面，支配 $E^{\mathrm A}$ 或 $E^{\mathrm B}$ 的公开参数均为 $[0,1/5]^2$，支配 $E^{\mathrm C}$ 的则是严格较小的 $[0,1/10]^2$。例如取 $r^\circ=(1/5,1/5)$，两个方向的判据分别给出

$$
E^{\mathrm A}\prec P_{r^\circ}\simeq E^{\mathrm B}\prec E^{\mathrm C}.
\tag{536.27}
$$

第一对说明相同 $\lambda$ 不决定有没有公开实验位于其下；后两者有相同 $\lambda$ 和 $d$，但 $P_{r^\circ}$ 能模拟 $E^{\mathrm B}$ 而不能模拟 $E^{\mathrm C}$，说明公开上方的比较还需要 $\kappa$。取 $(1/10,1/10)$ 则确实得到一个能模拟 $E^{\mathrm C}$ 的公开实验。这些区别发生在同一个实际支撑和同一对叶律上，不来自换目标、换先验或添加不存在的行。

### 536.9 来源范围与概念含义

《哲学研究》§§65–67 要求考察具体使用中的交错相似，而不先认定同一名称背后必有一个贯穿全部使用的本质；§§68–69 允许为特定目的划出精确边界，同时否认概念只有经过这种划界才在通常使用中有用。这里沿用第 535 章的这条有限对应：固定目的 $T$ 后研究足够的区分，是一个可另行提出的精确问题，不是对日常语言有用性的先决要求。随机种子、概率一恢复和 Blackwell 后处理序都是本章增加的数学结构，不归于维特根斯坦的原文。家族相似也没有被定义成图连通。[Wittgenstein, *Philosophische Untersuchungen*, §§65–69](https://www.wittgensteinproject.org/w/index.php/Philosophische_Untersuchungen#65)；[Stanford Encyclopedia of Philosophy, “Ludwig Wittgenstein”, §3.4](https://plato.stanford.edu/entries/wittgenstein/#LangGameFamiRese)。

公开选择与隐藏选择的区别已有一般理论。Arthur Américo、Mário S. Alvim、Annabelle McIver 的 *An Algebraic Approach for Reasoning About Information Flow*，Definitions 2–3，用带分支标签的输出与不带标签的混合分别定义 visible choice 和 hidden choice；Theorems 5.2–5.3、Corollary 1 给出可见选择下后验脆弱性的仿射公式、隐藏选择的界及相关比较。其 §2 的安全精化记号 $C_1\sqsubseteq_\circ C_2$ 表示存在 $D$ 使 $C_1D=C_2$，对应本章的信息序 $C_2\preceq C_1$，方向须换算。该文讨论有限通道，这些一般结果不是本章新增的结论，也不能替代这里任意标准 Borel 输出上的证明。[arXiv:1801.08090v4](https://arxiv.org/html/1801.08090v4)。

Zichang Wang 的 *Complementary Information Sources*，§2.2 与 Lemma 2，在有限状态、标准 Borel 信号及紧信息源集合的框架中，以独立于状态的信息源抽签并揭示来源标签，定义 tagged mixture，并证明其决策价值对抽签律仿射。这是来源可见混合的直接相关文献。[arXiv:2609.29066v1，2026-09-24](https://arxiv.org/html/2609.29066v1)。这类可见分支选择允许被选中的通道本身仍随机；只揭示来源标签，不等于揭示编码器的所有随机位。定义 536.1 另要求给定整个 $R$ 与情境后输出确定，因此规范形定理的公开范围不能由一般 tagged mixture 的名称替代。

仓内 [《递归关系观察与波粒事件》§393.3](RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md) 已区分可见独立种子下平均风险和平均成本的仿射等式、正概率分支上的最坏路径成本最大值，以及最坏状态风险的上界；该条明确替代旧 §§325.3–325.4 的相应表述。[《数学与神话匹配》§437.2、§§448–449](MATH_MYTH_MATCH.md) 已分别区分共同子测度质量和有方向的绝对连续质量，并比较翻转与擦除实验。这里复用这些一般工具与区别，接到第 535 章的实际支撑和按读数模拟归约上；上述文献与既有章节提供的是这些明确范围内的先行成分。本章的工作是在（536.1）的支撑上给出私有极小元的穷尽、全可见种子的规范形，以及任意充分通道与公开族的完整双向比较，是在这里逐项证明的支撑特定综合，不据所列来源范围宣称全球原创。

这组结果的概念含义是具体的：目标和实际对象不变时，观察者能否看见产生一个标签的随机选择，会改变哪些充分区分还能进一步删减。对非顶点 $p$，$P_p$ 在全可见种子的范围内已极小；允许把种子隐藏后，同一标签机制降为严格较少信息的 $E_p$，而仍逐态完成原目标。这种差别由实际模拟关系承担，不是由“信息较少”这一名称或一个平均分数决定。它既不证明所有概念都服从本章支撑，也不推出普遍相对主义，更不从可见性增加可区分性推出应当公开随机种子；披露是否合宜仍需要模型以外的用途和规范理由。

## 追加锚（本行以下为增补区）

## 537. 完整信息谱与共同模拟：有限概念指标之外的逃逸

### 定义 537.1（同一实际支撑上的充分私有商与中心质量）

固定定义 536.1 的整数 $m\ge2$、情境 $K=\{b,a_1,\ldots,a_m\}$，以及彼此不同的读数 $u_i,v_{ij}$。实际对象仍恰为

$$
\begin{aligned}
&(b,u_i,0),\ (a_i,u_i,0) &&(1\le i\le m),\\
&(a_i,v_{ij},0),\ (a_j,v_{ij},1) &&(1\le i<j\le m),
\end{aligned}
\tag{537.1}
$$

每行一个对象，共 $m(m+1)$ 个，不添加笛卡尔积中的其他行。编码核 $W$ 只读情境，在任意非空标准 Borel 辅助空间 $Z_W$ 上给出中心律 $\nu_W=W_b$ 和叶律 $\mu_i^W=W_{a_i}$；实际实验是

$$
E_W(x)=\delta_{q(x)}\otimes W_{c(x)}.
$$

观察者读取 $(q,z)$，充分性仍要求对每个实际对象以概率一恢复原目标 $T$。由式（536.5），这恰等价于 $\mu_i^W\perp\mu_j^W$（$i\ne j$），而 $\nu_W$ 可为任意概率律。$E_V\preceq E_W$ 表示存在一个不额外读取实际状态的 Markov 核，把所有 $E_W(x)$ 同时送到 $E_V(x)$；核可以读取 $q$，不预先要求其逐输入保持 $q$。互相模拟定义 $E_V\simeq E_W$，充分私有商记为 $\mathcal P_m=\mathcal F_{\mathrm{priv}}/{\simeq}$，序的左端信息较少。叶标签 $i$ 固定，商不额外识别叶标签的置换。

以下始终复用引理 536.2 的可测分划 $Z_W=D_0^W\sqcup D_1^W\sqcup\cdots\sqcup D_m^W$。取可测密度 $r_i^W$，使

$$
\mu_i^W(D_i^W)=1,\qquad
\nu_W|_{D_i^W}=r_i^W\mu_i^W,\qquad
\lambda_i^W=\int r_i^W\,d\mu_i^W,\qquad
s_W=\nu_W(D_0^W)=1-\sum_i\lambda_i^W.
\tag{537.2}
$$

密度非负且在 $\mu_i^W$ 几乎处处有限；在一个可测零集上改取零，并在 $D_i^W$ 外延为零，得到处处有限可测版本。该零集对 $\nu_W|_{D_i^W}$ 也为零，故此完成不改变任何测度等式。这里取的是中心相对各叶的绝对连续部分，不是拓扑支撑，也不是一个常数支配系数；同一个中心律要求 $\sum_i\lambda_i^W\le1$。

### 引理 537.2（从按读数模拟直接组装共同核）

对定义 537.1 中任意两个充分实验，有

$$
E_V\preceq E_W
\quad\Longleftrightarrow\quad
\exists K:Z_W\longrightarrow\operatorname{Prob}(Z_V),\qquad
\nu_WK=\nu_V,\quad \mu_i^WK=\mu_i^V\quad(1\le i\le m).
\tag{537.3}
$$

右侧的同一个核只读取辅助输出，不读取 $q$ 或情境；因此在这一支撑及充分族内，允许按 $q$ 后处理不会扩大模拟序。

证明：设左侧成立。按式（535.10）及（536.4），从原全局核取目标辅助输出的边缘，在每个 $u_i$ 得到处处定义的可测核 $H_i:Z_W\to\operatorname{Prob}(Z_V)$，满足

$$
\nu_WH_i=\nu_V,\qquad \mu_i^WH_i=\mu_i^V.
$$

此归约只用实际行等式，没有把逐点保持 $q$ 加作原核的假设。令

$$
\tau_i=(\nu_W|_{D_i^W})H_i.
$$

因 $\nu_W|_{D_i^W}\le\nu_W$，有 $\tau_i\le\nu_V$；因 $\nu_W|_{D_i^W}\ll\mu_i^W$，有 $\tau_i\ll\mu_i^V$。后一个结论可直接检验：若 $\mu_i^V(B)=\int H_i(B\mid z)\mu_i^W(dz)=0$，非负被积函数在 $\mu_i^W$ 几乎处处为零，也在 $\nu_W|_{D_i^W}$ 几乎处处为零，所以 $\tau_i(B)=0$。

取目标的共同叶分划 $D_i^V$。绝对连续性保证 $\tau_i$ 全部集中于 $D_i^V$，这些集合两两不交。故对每个可测 $B\subseteq Z_V$，

$$
\sum_i\tau_i(B)
=\sum_i\tau_i(B\cap D_i^V)
\le\sum_i\nu_V(B\cap D_i^V)
\le\nu_V(B).
\tag{537.4}
$$

这一求和必须使用目标叶载集的不交性；仅有每个 $\tau_i\le\nu_V$ 并不能推出其和仍被 $\nu_V$ 支配。于是

$$
\Delta=\nu_V-\sum_i\tau_i
$$

是正测度。每个 $H_i$ 都是概率核，故 $\tau_i(Z_V)=\lambda_i^W$，从而 $\Delta(Z_V)=s_W$。若 $s_W>0$，在整个源空间定义

$$
K(\cdot\mid z)=
\begin{cases}
H_i(\cdot\mid z),&z\in D_i^W,\quad 1\le i\le m,\\
\Delta/s_W,&z\in D_0^W.
\end{cases}
\tag{537.5}
$$

有限个可测块上的核拼接仍可测。每个源叶集中于自己的 $D_i^W$，所以 $\mu_i^WK=\mu_i^V$；中心的像则为 $\sum_i\tau_i+\Delta=\nu_V$。若 $s_W=0$，正测度 $\Delta$ 的质量为零，故 $\Delta=0$；在 $D_0^W$ 上取任意固定目标点的 Dirac 律即可，这一行对源中心和所有源叶都未被使用。

反向，给定右侧的 $K$，在 $(q,z)$ 上使用 $\delta_q\otimes K(\cdot\mid z)$ 即恢复每个实际行的目标律。有限读数空间保证此扩张可测。证毕。此引理的联合组装来自共同中心剩余质量与不交叶载集；其前置是第 535—536 章的实际支撑归约和测度分解，不需要另用耦合存在定理。

### 定理 537.3（同一中心下的完整谱、联合实现与模拟序）

对定义 537.1 的整个充分族，令

$$
\alpha_i^W=(r_i^W)_\#\mu_i^W,\qquad
\chi_i^W(t)=\int_{[0,\infty)}\min(r,t)\,\alpha_i^W(dr)
\quad(t\ge0).
\tag{537.6}
$$

则 $\mathcal P_m$ 由带固定叶标签的完整曲线族 $(\chi_1,\ldots,\chi_m)$ 分类，并有下列联合结论。

1. 每个实验等价于辅助空间

$$
Z^\circ=\{o\}\sqcup\bigsqcup_{i=1}^m\bigl(\{i\}\times[0,\infty)\bigr)
$$

上的规范实验，其叶 $i$ 只在标签 $i$ 上具有律 $\alpha_i$，中心律为

$$
\nu^\circ=\sum_{i=1}^m \bigl(r\,\alpha_i(dr)\bigr)\text{ 放在标签 }i
+s\delta_o,\qquad
s=1-\sum_i\int r\,\alpha_i(dr).
\tag{537.7}
$$

这里的等价由两个共同情境无关核达到。

2. 可实现的完整曲线族恰为满足以下条件的族：每个 $\chi_i:[0,\infty)\to\mathbb R$ 连续、非减、凹，$\chi_i(0)=0$，零点右导数 $\chi'_{i,+}(0)\le1$，且有限极限

$$
\lambda_i=\lim_{t\to\infty}\chi_i(t),\qquad
\sum_i\lambda_i\le1.
\tag{537.8}
$$

相应概率律唯一，由

$$
\alpha_i((t,\infty))=\chi'_{i,+}(t)\quad(t\ge0),\qquad
\alpha_i(\{0\})=1-\chi'_{i,+}(0)
\tag{537.9}
$$

恢复。逐叶的这些条件加上一个共同质量预算即足以联合实现，不要求密度有界或辅助输出有限。

3. 模拟序及等价类的判据分别为

$$
\begin{aligned}
E_V\preceq E_W
&\quad\Longleftrightarrow\quad
\chi_i^W(t)\le\chi_i^V(t)
\quad\text{对全部 }i,\ t\ge0,\\
E_V\simeq E_W
&\quad\Longleftrightarrow\quad
\chi_i^V=\chi_i^W
\quad\text{对全部 }i.
\end{aligned}
\tag{537.10}
$$

相等曲线唯一指定带标签的规范行律及等价类，不声称模拟核唯一。

4. 在读数 $u_i$ 上，另加一个区分中心与叶 $i$ 的二元零一损失任务，令中心、叶的先验分别为 $1/(1+t),t/(1+t)$。其最优错误为

$$
\mathcal B_i^W(t)=\frac{\chi_i^W(t)}{1+t}.
\tag{537.11}
$$

这是额外的区分任务；原 $T$ 在这两行上都为零，且仍在全部实际行上被精确恢复。第 536 章的有限指标是完整谱的下列读数：

$$
\lambda_i=\lim_{t\to\infty}\chi_i(t),\qquad
\beta_i=\chi'_{i,+}(0),\qquad
\kappa_i=\chi_i(1),\qquad
d_i=\max\{\lambda_i,\beta_i\}.
\tag{537.12}
$$

对既有私有极小实验 $E_p$ 与公开实验 $P_r$，相应代入为

$$
\chi_i^{E_p}(t)=\min(p_i,t),\qquad
\chi_i^{P_r}(t)=r_i\min(1,t).
\tag{537.13}
$$

证明：本定理把经典二态似然律、风险曲线和耦合工具接到引理 537.2 的共同实现关系上。二态的风险序、风险与似然律的唯一对应、加权似然律加一个奇异原子的实现，已见 Gushchin–Borzykh, *Integrated quantile functions: properties and applications*（2017），Definition 3、Proposition 2、Corollary 3、Proposition 3(iii) 及其证明。其 Definition 3 以检验区域包含定义信息序；下面另行构造本章标准 Borel 输出上的实际核，并不从区域包含的名称直接推出共同核存在。[原文](https://www.vmsta.org/journal/VMSTA/article/99/text)，[DOI:10.15559/17-VMSTA88](https://doi.org/10.15559/17-VMSTA88)。

先证规范实现。省略 $W$ 上标，在 $D_i$ 上取映射 $z\mapsto(i,r_i(z))$，在 $D_0$ 上取 $z\mapsto o$。它可测，把叶送到标签 $i$ 上的 $\alpha_i$，把 $\nu|_{D_i}=r_i\mu_i$ 送到标签 $i$ 上的 $r\alpha_i(dr)$，把余下中心质量送到 $s\delta_o$。

反向，在 $Z\sim\mu_i$ 下考虑 $(r_i(Z),Z)$ 的联合概率律。第一坐标空间 $[0,\infty)$ 可测，条件目标 $Z$ 为标准 Borel，故存在概率核 $Q_i(dz\mid r)$，满足对可测 $A\subseteq[0,\infty)$、$B\subseteq Z$，

$$
\int_A Q_i(B\mid r)\,\alpha_i(dr)
=\mu_i\bigl(B\cap\{r_i\in A\}\bigr).
\tag{537.14}
$$

这是经典的概率分解定理；所用条件及积分等式见 Cho–Jacobs, *Disintegration and Bayesian Inversion via String Diagrams*，Example 3.7、Theorem 3.12、Corollary 3.13。该文将存在定理归于 Pollard、Faden；这里采用的是 Cho–Jacobs 所陈述的版本。[arXiv:1709.00322v3](https://arxiv.org/html/1709.00322v3)，[DOI:10.1017/S0960129518000488](https://doi.org/10.1017/S0960129518000488)。

式（537.14）由矩形推广到联合空间的可测集。原联合律集中在可测图集 $\{(r,z):z\in D_i,\ r_i(z)=r\}$，故

$$
Q_i\bigl(\{z\in D_i:r_i(z)=r\}\mid r\bigr)=1
\quad\text{对 }\alpha_i\text{ 几乎所有 }r.
\tag{537.15}
$$

图集可测是因为 $r_i$ 可测且实数对角线可测；对其指示函数沿核积分所得函数也可测。因此可以选取一个共同的可测参数零集，在它之外获得该条件载集等式。对任意有界非负可测 $g$，先从简单函数再取极限，由（537.14）得

$$
\int g(r)Q_i(B\mid r)\,\alpha_i(dr)
=\int_B g(r_i(z))\,\mu_i(dz).
$$

再令 $g(r)=r\wedge n$ 并用单调收敛，得到无界但可积密度所需的恒等式

$$
\int r Q_i(B\mid r)\,\alpha_i(dr)
=\int_B r_i\,d\mu_i
=\nu(B\cap D_i).
\tag{537.16}
$$

特别地，$\alpha_iQ_i=\mu_i$ 且 $(r\alpha_i)Q_i=\nu|_{D_i}$。任何 $\alpha_i$-零参数集也是 $r\alpha_i$-零集，所以在这类集合上统一换成一个固定点的 Dirac 律，不会改变任一实际行；可测完成不要求在不可达参数上保留图集条件。

现在令反向核在 $(i,r)$ 上使用 $Q_i(\cdot\mid r)$；若 $s>0$，在 $o$ 上抽样 $\nu|_{D_0}/s$。若 $s=0$，中心与各叶均不给 $o$ 质量，其核值任取。有限标签拼接保证可测，（537.16）和各叶的等式保证同一个核同时恢复全部情境行。这证明第一项，而非只证明每个二态边缘分别存在一个反向核。

再证曲线与联合可实现范围。从任意概率律 $\alpha$ 出发，$t\mapsto\min(r,t)$ 非减、凹且为 $1$-Lipschitz，积分后保留这些性质。支配收敛用于右差商，给出

$$
\chi'_+(t)=\alpha((t,\infty)).
$$

单调收敛给出 $\lim_{t\to\infty}\chi(t)=\int r\,\alpha(dr)$。实际规范中心的总质量恰为一，于是必须满足（537.8）。

反向，给定所列函数 $\chi$，令 $g(t)=\chi'_+(t)$。凹性与非减性使 $g$ 非增且 $0\le g(t)\le g(0)\le1$。它右连续：若 $t_n\downarrow t$，则 $a=\lim_n g(t_n)\le g(t)$；任取 $h>0$，对充分大的 $n$，凹性给出

$$
g(t_n)\ge\frac{\chi(t+h)-\chi(t_n)}{t+h-t_n}.
$$

先令 $n\to\infty$，再令 $h\downarrow0$，得到 $a\ge g(t)$。这里在 $t=0$ 也使用了假设的连续性，故端点没有遗漏。若 $\lim_{t\to\infty}g(t)>0$，割线斜率的下界将迫使 $\chi(t)$ 至少线性增长，与有限极限矛盾；所以此极限为零。

因而令 $F(t)=0$（$t<0$），$F(t)=1-g(t)$（$t\ge0$），便得到一个右连续、非减、两端极限为零和一的分布函数，唯一确定 $[0,\infty)$ 上的概率律 $\alpha$。其零点原子与正半轴尾概率正是（537.9）。凹函数的割线斜率介于零和一之间，故 $\chi$ 为 $1$-Lipschitz，局部绝对连续；右导数与导数几乎处处相同。因此由尾积分公式，

$$
\chi(t)=\int_0^t g(u)\,du
=\int_0^t\alpha((u,\infty))\,du
=\int\min(r,t)\,\alpha(dr),
\qquad
\int r\,\alpha(dr)=\lambda.
\tag{537.17}
$$

这还证明有限一阶矩和唯一性；当 $\lambda=0$ 时 $\chi=0$、$\alpha=\delta_0$，无需剔除这个边界。对各叶分别取得 $\alpha_i$ 后，单一条件 $\sum_i\lambda_i\le1$ 恰保证（537.7）的中心是一条概率律；标签使叶两两奇异，故它在（537.1）上充分。这是经典一维对应的共同中心实现，不是另立的一维唯一性新定理。此时已经得到“曲线唯一确定规范律”，下文证明序判据后才把它提升为“唯一确定模拟等价类”。

现证序判据的必要性。若 $E_V\preceq E_W$，取引理 537.2 的共同核 $K$，也可只取 $u_i$ 上的局部核。对每个 $t\ge0$，源测度

$$
C_{i,t}^W=\nu_W\wedge(t\mu_i^W)
$$

的质量为 $\chi_i^W(t)$。推前后 $C_{i,t}^WK\le\nu_V,t\mu_i^V$，所以由最大共同子测度的定义，

$$
C_{i,t}^WK\le\nu_V\wedge(t\mu_i^V),\qquad
\chi_i^W(t)\le\chi_i^V(t).
\tag{537.18}
$$

核保持有限测度的总质量；这里用的是测度的共同部分，不是实验序的下界。

为证充分性，设全部这些曲线不等式成立，先在规范空间上构造一个共同核。对非负、有限一阶矩概率律 $\alpha$，定义整个实线上的 put 函数

$$
p_\alpha(t)=\int(t-r)^+\,\alpha(dr)
=
\begin{cases}
t-\chi_\alpha(t),&t\ge0,\\
0,&t<0.
\end{cases}
$$

故每个 $i$ 都有 $p_{\alpha_i^V}\le p_{\alpha_i^W}$。Nutz–Stebegg, *Canonical Supermartingale Couplings*，§2 Proposition 2.1，对实线上具有有限一阶矩且总质量相等的有限测度，将 put 函数序与超鞅耦合存在性等价；它不要求均值相等。此处两律的质量均为一，均值分别为有限的 $\lambda_i^V,\lambda_i^W$，完全满足这些条件。[arXiv:1609.02867v2](https://arxiv.org/html/1609.02867v2)，*Annals of Probability* 46(6)（2018），3351–3398，[DOI:10.1214/17-AOP1249](https://doi.org/10.1214/17-AOP1249)。

具体应用时，初始变量取目标 $Y\sim\alpha_i^V$，终止变量取来源 $X\sim\alpha_i^W$，取得联合概率律 $\Pi_i$ 满足

$$
\mathbb E_{\Pi_i}[X\mid Y]=e_i(Y)\le Y.
\tag{537.19}
$$

两个边缘都集中在 $[0,\infty)$，故耦合也集中在那里。$e_i$ 可取非负可测版本，有限性及不等式在 $\alpha_i^V$ 几乎处处成立；在其可测例外零集上令 $e_i(y)=0$，即可处处满足 $0\le e_i(y)\le y$，不改变积分。这里没有把超鞅方向取成来源到目标。

接着用（537.14）所引分解定理，对同一联合律按 $X$ 条件化，得到从来源到目标的概率核 $C_i(dy\mid x)$。其条件目标 $[0,\infty)$ 为标准 Borel，因此核存在；在 $\alpha_i^W$-零参数集上的值可统一补成 $\delta_0$，这类集合对 $x\alpha_i^W(dx)$ 也为零。两个方向的条件化属于同一个 $\Pi_i$，所以

$$
\alpha_i^WC_i=\alpha_i^V,\qquad
\int x C_i(B\mid x)\,\alpha_i^W(dx)
=\mathbb E_{\Pi_i}\!\left[X\mathbf1_{\{Y\in B\}}\right]
=\int_B e_i(y)\,\alpha_i^V(dy).
\tag{537.20}
$$

这些恒等式对非负截断 $X\wedge n$ 先成立，再由单调收敛得到；$X$ 的可积性保证所得有限测度。于是将源标签 $(i,x)$ 送到标签 $i$ 上按 $C_i(\cdot\mid x)$ 抽样的 $Y$，能够正确模拟叶 $i$，并将该分支的中心质量送到 $e_i(y)\alpha_i^V(dy)$。目标中心在此分支尚需的正测度是 $(y-e_i(y))\alpha_i^V(dy)$，质量为 $\lambda_i^V-\lambda_i^W$。

所有分支共用的剩余测度定义为

$$
\Gamma
=\sum_i \bigl((y-e_i(y))\alpha_i^V(dy)\bigr)\text{ 放在标签 }i
+s_V\delta_o.
\tag{537.21}
$$

它非负，且

$$
\Gamma(Z^\circ)
=\sum_i(\lambda_i^V-\lambda_i^W)+s_V
=1-\sum_i\lambda_i^W=s_W.
\tag{537.22}
$$

若 $s_W>0$，把源 $o$ 送到 $\Gamma/s_W$；若 $s_W=0$，则 $\Gamma=0$，所有分支差额和 $s_V$ 都为零，源 $o$ 的未使用行任取一个概率律。这给出一个定义在全部规范空间上的可测概率核，同时送对全部叶行及同一条中心行。不能为每个叶另花一次源剩余质量；（537.22）正是一次性支付全部差额的等式。将该核与已构造的两端规范化核复合，就得到一般标准 Borel 输出上的共同核，再由引理 537.2 得到 $E_V\preceq E_W$。因此没有有限字母表、密度有界或等均值的隐含限制。

双向应用序判据给出曲线相等；由（537.9）各带标签概率律唯一，再由（537.8）剩余质量唯一。反之，相等曲线给出相同规范行律和双向模拟。这在序判据之后完成等价类的唯一性论证。

最后证明风险及旧指标读数。令 $\delta(z)\in[0,1]$ 是在 $u_i$ 上报告中心的概率，额外任务的错误为

$$
\frac1{1+t}\int(1-\delta)\,d\nu
+\frac{t}{1+t}\int\delta\,d\mu_i.
$$

相对 $\nu+\mu_i$ 逐点选择较小成本的一端，得到最小值 $(\nu\wedge t\mu_i)(Z)/(1+t)=\chi_i(t)/(1+t)$；相等处任意随机化，所选阈值规则可测，所以该值确实达到。对应 Gushchin–Borzykh 的符号是 $P=\mu_i$、$P'=\nu$、似然比 $Z=r_i$（在 $P$ 几乎处处），$\pi=1/(1+t)$。其 Bayes 风险定义和式（26）给出同一公式；这里复用这一经典解释而不把原恢复目标换成中心识别。

$\lambda_i$ 的极限公式已证；$\mu_i$ 相对 $\nu$ 的绝对连续部分是 $\mu_i|_{\{r_i>0\}}$，所以 $\beta_i=\alpha_i((0,\infty))=\chi'_{i,+}(0)$；共同质量为 $\kappa_i=\int\min(r,1)\alpha_i(dr)$，再代入 $d_i$ 的定义即得（537.12）。$E_p$ 的叶似然律是 $\delta_{p_i}$；$P_r$ 的叶似然律是 $(1-r_i)\delta_0+r_i\delta_1$，因为只有种子 $i$ 的共同输出具有中心与该叶相等的正质量。代入（537.6）得到（537.13），包括零权重。这些只是与第 536 章相容的代入式。证毕。

本定理的联合部分限于（537.1）的一个中心和互相奇异的叶：经典二态成分提供单支曲线、规范化及序工具，引理 537.2 与（537.7）、（537.21）则保证所有分支确实属于同一条中心律，并由一个核同时模拟。[《数学与神话匹配》§437.2、§§447–449](MATH_MYTH_MATCH.md) 已给出共同质量、单个模拟器与完整决策比较的相关前置；这里补充的是本支撑上整族的精确实现与分类，不据这些列举作全面优先权断言。

### 定理 537.4（充分商中的上界与有条件的最大下界）

在 $\mathcal P_m$ 中取任意 $[E_W],[E_V]$。它们总有最小共同上界，其曲线为

$$
\chi_i^{\,\vee}(t)=\min\{\chi_i^W(t),\chi_i^V(t)\}.
\tag{537.23}
$$

充分共同下界存在当且仅当

$$
\sum_{i=1}^m\max\{\lambda_i^W,\lambda_i^V\}\le1.
\tag{537.24}
$$

这一存在判据已经由定理 536.4 的私有极小元分类推出，以下明确复用。条件成立时，还存在最大充分共同下界。令

$$
f_i(t)=\max\{\chi_i^W(t),\chi_i^V(t)\},\qquad
L_i=\max\{\lambda_i^W,\lambda_i^V\},
$$

则它的曲线是 $f_i$ 在整个 $[0,\infty)$ 上的最小凹上包络 $H_i$，具有公式

$$
H_i(t)=
\sup\left\{
\sum_{j=1}^n a_j f_i(t_j):
\begin{array}{l}
n\ge1,\quad a_j\ge0,\quad t_j\ge0,\\
\sum_j a_j=1,\quad\sum_j a_jt_j=t
\end{array}
\right\}.
\tag{537.25}
$$

这里只用有限混合，但 $t_j$ 不受任何统一上界限制；不声称该上确界必须由某个混合达到。整个充分商不是格。

证明：先看（537.23）。凹函数的下图集 $\{(t,y):t\ge0,\ y\le\chi(t)\}$ 凸，两个下图集的交正是逐点最小值的下图集，所以 $\chi_i^{\,\vee}$ 凹。它连续、非减、在零点为零，且 $0\le\chi_i^{\,\vee}(t)\le t$，故零点右斜率不超过一。其极限为 $\min(\lambda_i^W,\lambda_i^V)$，这些极限之和不超过一。定理 537.3 于是联合实现这组曲线为充分实验 $J$。

因为 $\chi_i^J\le\chi_i^W,\chi_i^V$，序判据给出 $E_W,E_V\preceq J$。若 $U$ 是另一个充分共同上界，则 $\chi_i^U\le\chi_i^W,\chi_i^V$，从而 $\chi_i^U\le\chi_i^J$，即 $J\preceq U$。这证明最小性及等价类意义下的唯一性。

对共同下界的存在性，若充分 $B$ 满足 $B\preceq E_W,E_V$，定理 536.4 保证存在一个私有极小实验 $E_p\preceq B$。传递性给出 $E_p\preceq E_W,E_V$，再由式（536.13）得 $p_i\ge\lambda_i^W,\lambda_i^V$，而 $\sum_i p_i=1$，所以（537.24）必要。反之，若（537.24）成立，取任意 $a\in\Delta_{m-1}$ 并令

$$
p_i=L_i+\left(1-\sum_jL_j\right)a_i.
$$

则 $p\in\Delta_{m-1}$ 且 $p\ge\lambda^W,\lambda^V$。定理 536.4 直接给出充分共同下界 $E_p$。因此存在性没有被当作本章另一项独立发现；尚须构造的是其中最大的下界。

固定一支并省略下标。因每条曲线非减且极限不超过 $L$，有 $0\le f(t)\le\min(t,L)$。公式（537.25）的可选混合非空，单点混合给出 $H(t)\ge f(t)$；对任何可选混合又有

$$
0\le\sum_j a_jf(t_j)\le\sum_j a_jt_j=t,\qquad
\sum_j a_jf(t_j)\le L.
$$

所以

$$
0\le f(t)\le H(t)\le\min(t,L).
\tag{537.26}
$$

取分别逼近 $H(t)$ 与 $H(u)$ 的有限混合，以比例 $\theta,1-\theta$ 拼接，得到均值为 $\theta t+(1-\theta)u$ 的有限混合；令逼近误差趋零，即得

$$
H(\theta t+(1-\theta)u)\ge\theta H(t)+(1-\theta)H(u).
$$

因此 $H$ 凹。若 $G$ 是任意凹函数且 $G\ge f$，有限 Jensen 不等式给出

$$
G(t)\ge\sum_j a_jG(t_j)\ge\sum_j a_jf(t_j)
$$

对全部可选混合成立，取上确界得到 $G\ge H$。这证明最小凹上包络性质，未把半轴截成紧区间。

还须证明 $H$ 属于可实现曲线类。由（537.26），$H(0)=0$，且 $H(t)\to0$ 当 $t\downarrow0$，所以零点连续。有限凹函数在 $(0,\infty)$ 内连续；其零点右导数是 $\lim_{t\downarrow0}H(t)/t$，由凹性存在，并被（537.26）限制在 $[0,1]$。若存在 $0\le u<v$ 使割线斜率 $c=(H(v)-H(u))/(v-u)<0$，凹性使每个 $w>v$ 满足

$$
H(w)\le H(v)+c(w-v).
$$

右端终将为负，与 $H\ge0$ 矛盾。因此 $H$ 非减。又 $f(t)\to L$ 且 $f\le H\le L$，故 $\lim_{t\to\infty}H(t)=L$；当 $L=0$ 时这同时给出 $H=0$。

对全部叶恢复下标，（537.24）保证 $\sum_i\lim H_i=\sum_iL_i\le1$，于是定理 537.3 用一条共同中心律实现 $(H_i)$ 为充分实验 $M$。因 $H_i\ge\chi_i^W,\chi_i^V$，有 $M\preceq E_W,E_V$。若 $B$ 是任意充分共同下界，则 $\chi_i^B\ge f_i$，且 $\chi_i^B$ 凹；最小凹上包络性质给出 $\chi_i^B\ge H_i$，故 $B\preceq M$。这证明最大性。

最后，取两个不同的单纯形参数 $p,q\in\Delta_{m-1}$。其私有极小实验满足 $\lambda(E_p)=p$、$\lambda(E_q)=q$，而

$$
\sum_i\max(p_i,q_i)
=\frac12\sum_i(p_i+q_i+|p_i-q_i|)
=1+\frac12\|p-q\|_1>1.
\tag{537.27}
$$

由（537.24），它们没有充分共同下界，故 $\mathcal P_m$ 不是格。证毕。

本定理中的范围限定属于结论本身：上、下界在充分私有商 $\mathcal P_m$ 内取。本卷第 130 章、定理 443.1 的抽象交闭合准则不自动保证该允许族有交。经典二态格理论亦已存在：Bertschinger–Rauh, *The Blackwell relation defines no lattice*，Proposition 16、Lemma 17 给出有限二态情形的格结构，Theorem 19 给出一般多态情形的非格结论；它们的有限矩阵结果本身不承担这里标准 Borel 输出、无界半轴包络及共同中心预算的论证。[arXiv:1401.3146v1](https://arxiv.org/html/1401.3146v1)。

### 命题 537.5（同一中心律下逃逸于全部旧指标的七输出实例）

取 $m=2$，保留（537.1）的全部六个实际对象。辅助输出依次为 $(e_1,x,y,z,e_2,w,o)$，下列每行向量都除以 $80$：

$$
\begin{aligned}
\nu_{\mathrm A}=\nu_{\mathrm B}
&=\frac1{80}(0,8,20,12,0,16,24),\\
\mu_2^{\mathrm A}=\mu_2^{\mathrm B}
&=\frac1{80}(0,0,0,0,64,16,0),\\
\mu_1^{\mathrm A}
&=\frac1{80}(64,8,5,3,0,0,0),\\
\mu_1^{\mathrm B}
&=\frac1{80}(64,4,10,2,0,0,0).
\end{aligned}
\tag{537.28}
$$

这定义两个充分实验 $E_{\mathrm A},E_{\mathrm B}$。它们拥有相同的中心律、相同的叶 $2$ 律以及相同的全部有限指标

$$
\lambda=(1/2,1/5),\qquad
\beta=\kappa=(1/5,1/5),\qquad
d=(1/2,1/5),
\tag{537.29}
$$

却在 $\mathcal P_2$ 中不可比。它们支配的私有极小类相同，位于它们之下、之上的公开类也分别相同。

证明：四条概率行的分子总和分别为

$$
8+20+12+16+24=80,\quad
64+16=80,\quad
64+8+5+3=80,\quad
64+4+10+2=80.
$$

叶 $1$ 集中于 $\{e_1,x,y,z\}$，叶 $2$ 集中于 $\{e_2,w\}$，两个集合不交，故两个实验都充分。可取 $D_1=\{e_1,x,y,z\}$、$D_2=\{e_2,w\}$、$D_0=\{o\}$。在叶 $1$ 的四个点上，中心质量除以叶质量，实验 $\mathrm A$ 的密度依次为 $0,1,4,4$，实验 $\mathrm B$ 为 $0,2,2,6$；在叶 $2$ 的两个点上均为 $0,1$。因此

$$
\begin{aligned}
\alpha_1^{\mathrm A}
&=\frac45\delta_0+\frac1{10}\delta_1+\frac1{10}\delta_4,\\
\alpha_1^{\mathrm B}
&=\frac45\delta_0+\frac7{40}\delta_2+\frac1{40}\delta_6,\\
\alpha_2^{\mathrm A}=\alpha_2^{\mathrm B}
&=\frac45\delta_0+\frac15\delta_1,\qquad s=\frac3{10}.
\end{aligned}
\tag{537.30}
$$

具体地，$\mathrm A$ 的密度 $4$ 权重为 $(5+3)/80=1/10$，$\mathrm B$ 的密度 $2$ 权重为 $(4+10)/80=7/40$；这两个合并均在同一固定中心律内完成。第一支的均值分别为 $1/10+4/10=1/2$ 和 $14/40+6/40=1/2$，第二支均值为 $1/5$。各支的正密度概率都是 $1/5$，且全部正密度均至少为一，故各支在 $t=1$ 的截断积分也都是 $1/5$。用（537.12）就得到（537.29），剩余中心质量为 $1-1/2-1/5=3/10$。

完整曲线却为

$$
\begin{aligned}
\chi_1^{\mathrm A}(t)
&=\frac1{10}\min(1,t)+\frac1{10}\min(4,t),\\
\chi_1^{\mathrm B}(t)
&=\frac7{40}\min(2,t)+\frac1{40}\min(6,t),\\
\chi_2^{\mathrm A}(t)=\chi_2^{\mathrm B}(t)
&=\frac15\min(1,t).
\end{aligned}
\tag{537.31}
$$

在 $t=3/2$，第一支的值是

$$
\chi_1^{\mathrm A}(3/2)=\frac1{10}+\frac3{20}=\frac14
<\frac3{10}
=\frac{21}{80}+\frac3{80}
=\chi_1^{\mathrm B}(3/2).
$$

在 $t=9/2$，则有相反方向：

$$
\chi_1^{\mathrm A}(9/2)=\frac1{10}+\frac4{10}=\frac12
>\frac{37}{80}
=\frac{28}{80}+\frac9{80}
=\chi_1^{\mathrm B}(9/2).
$$

故（537.10）的两个模拟方向各有一个失败点，两个实验不可比。同一组额外零一损失任务的 Bayes 错误分别为

$$
\begin{array}{c|cc}
t&\mathcal B_1^{\mathrm A}(t)&\mathcal B_1^{\mathrm B}(t)\\ \hline
3/2&1/10&3/25\\
9/2&1/11&37/440
\end{array}
\tag{537.32}
$$

每一行内部先验相同，两个阈值对应的任务先验不同。原 $T$ 的逐态恢复没有任何改变。

最后，定理 536.4 及 536.6 分别给出两者完全相同的三个旧比较集合：

$$
\begin{aligned}
\{[E_{(p,1-p)}]:E_{(p,1-p)}\preceq E_{\mathrm A}\}
&=\{[E_{(p,1-p)}]:1/2\le p\le4/5\},\\
\{[P_r]:P_r\preceq E_{\mathrm A}\}
&=\{[P_r]:r_1\ge1/2,\ r_2\ge1/5,\ r_1+r_2\le1\},\\
\{[P_r]:E_{\mathrm A}\preceq P_r\}
&=\{[P_r]:0\le r_1\le1/5,\ 0\le r_2\le1/5\}.
\end{aligned}
\tag{537.33}
$$

三个左侧分别把 $\mathrm A$ 换成 $\mathrm B$，等式仍成立。这证明有限指标及其决定的这些比较集合没有分辨两者，而完整曲线分辨了两者。证毕。这里“逃逸”专指超出 $\lambda,\beta,\kappa,d$ 及（537.33）这些摘要；本命题不声称每一种有限描述都不充分，两个有限概率表本身就是本例的完整描述。

### 命题 537.6（两个中心时按读数模拟可以严格更强）

引理 537.2 的单中心合同不能直接替换成任意多中心合同。具体地，另取情境 $\{b,c,a_1,a_2\}$，对每个 $h\in\{b,c\}$、$i\in\{1,2\}$ 使用一个不同的读数 $u_{hi}$，实际行恰为 $(h,u_{hi},0),(a_i,u_{hi},0)$，再取不同读数 $v$ 的两行 $(a_1,v,0),(a_2,v,1)$。这是本命题另行规定的十行支撑，位于（537.1）的单中心范围之外。

在辅助空间 $\{0,1,2\}$ 上令

$$
W_b=W_c=\delta_2,\qquad V_b=\delta_0,\qquad V_c=\delta_1,
\qquad
W_{a_i}=V_{a_i}=\delta_{i-1}\quad(i=1,2).
\tag{537.34}
$$

两个实际实验都充分，而且 $E_V\preceq E_W$；但没有一个只读辅助输出的核把所有 $W_k$ 同时送到 $V_k$。

证明：唯一相反目标的共读数对是 $v$ 上的两叶，它们输出不同的 Dirac 点，故可精确解码；其他读数的目标均为零。对每个 $u_{hi}$，令局部核将输入 $i-1$ 保持为 $i-1$，把输入 $2$ 送到 $V_h$；这两个输入点不同，故两个要求相容，未用输入任取。对 $v$，在输入 $0,1$ 上用恒等核。按有限读数拼接并附回 $q$，由式（535.10）得到一个全局状态无关模拟器。

反之，任何只读辅助输出的共同核 $K$ 都有 $\delta_2K=K(\cdot\mid2)$。中心 $b$ 要求它等于 $\delta_0$，中心 $c$ 又要求它等于 $\delta_1$，矛盾。证毕。这个反例只排除了无条件的多中心推广，不提出一般多中心分类；它使引理 537.2 所用“共同中心”成为一个实际承担结论的条件。

### 定义 537.7（概念等价的任务合同与解释范围）

在本章中，把固定实际对象、情境取得规则、可见读数、原恢复任务及允许模拟器之后的 $E_V\simeq E_W$ 称为该合同内的概念等价。只检查原 $T$ 的恢复错误，会把所有充分实验都记为零误差；这并不等于它们可以互相模拟。额外选取所有中心—叶零一损失任务及其先验后，定理 537.3 证明完整风险族恰能判定本合同中的模拟序；命题 537.5 证明旧有限摘要所识别的相同，并非这种等价。改变实际支撑、观察或模拟权限、任务及所选额外决策族，就形成另一个须说明的比较问题，不预断其等价关系一定改变。引理 537.2 给出删去模拟器读取 $q$ 的权限而序不变的特定条件，命题 537.6 给出这一条件失效的具体边界。

本定义对维特根斯坦的对应只保留《哲学研究》§§65–69 的有限读法：§§65–67 通过具体使用及交错相似，反对未考察就要求同一名称背后有贯穿全部使用的单一本质；§§68–69 允许为了一个特定目的增加精确边界，却不把这种划界作为通常语言有用性的前提。这里把目的写为 $T$，再增加统计比较，是本章的数学规定；标准 Borel 通道、超鞅耦合及 Blackwell 序都不被归作维特根斯坦的学说，家族相似也没有被定义成图连通。[Wittgenstein, *Philosophische Untersuchungen*, §§65–69](https://www.wittgensteinproject.org/w/index.php/Philosophische_Untersuchungen#65)；辅助解释见 [Stanford Encyclopedia of Philosophy, “Ludwig Wittgenstein”, §3.4](https://plato.stanford.edu/entries/wittgenstein/#LangGameFamiRese)。

因此本合同的解释范围限于所列可替代性与任务区分：它不推出普遍相对主义，不提供实际性别分类，不从信息可见性推出披露义务，也不证明信息逃逸必然无限持续。本章中的完备性是对（537.1）的充分私有族及其允许核而言；它与日常语言是否必须具有精确边界是不同量词的问题。

## 追加锚（本行以下为增补区）
## 538. 分别相同的二态概念与共同实现：可见种子下的高阶信息纤维

### 定义 538.1（实际支撑、目的与全可见种子的合同）

沿用定义 535.1 的有限非空实际对象集 $A$、情境 $c:A\to K$、旧读数 $q:A\to Q$ 和原目标 $T:A\to Y$，其中 $K=c(A)$、$Q=q(A)$、$Y=T(A)$。本章用 $Q$ 表示第 535 章的读数字母表 $L$，把 $L$ 留给下文的线性投影。仍假定

$$
c(x)=c(x'),\ q(x)=q(x')\ \Longrightarrow\ T(x)=T(x').
\tag{538.1}
$$

记 $S=\{(c(x),q(x)):x\in A\}$，$t(k,q)=T(x)$ 对任一具有该实际行的 $x$ 定义，$A_q=\{k:(k,q)\in S\}$。$A_q$ 是活动情境集合，不是另一个实际对象集；不同对象可以具有相同的行。本章的实验在这样的对象上本来就相同，故用实际行 $s=(k,q)\in S$ 编索引。只使用 $S$，不补入 $K\times Q\setminus S$。

条件（538.1）是可恢复性的必要条件：若同一 $(k,q)$ 对应两个不同目标，而编码只读 $k$，两对象给观察者的概率律就相同；同一解码核不可能在该同一律下以概率一给出两个不同值。以下所有充分性都保持原来的 $T$，不借改变目标消除这个障碍。

种子空间 $\mathcal R$ 和标签空间 $Z$ 为任意非空标准 Borel 空间，$\rho\in\operatorname{Prob}(\mathcal R)$，$f:\mathcal R\times K\to Z$ 可测。种子 $R\sim\rho$ 与实际状态独立，条件于整个种子和情境后编码确定；观察者看到

$$
(q,R,f(R,k)),\qquad
E_{k,q}=\delta_q\otimes\bigl(r\mapsto(r,f(r,k))\bigr)_*\rho.
\tag{538.2}
$$

编码器运行时不读取 $q$；可以在设计时使用固定的 $S,t$。整个随机种子被揭示，不另藏随机位。允许解码器及模拟器独立随机化。称 $E$ 充分，是指存在 Markov 核 $D:Q\times\mathcal R\times Z\to\operatorname{Prob}(Y)$，满足

$$
\forall(k,q)\in S,\qquad
\int D(\{t(k,q)\}\mid q,r,f(r,k))\,\rho(dr)=1.
\tag{538.3}
$$

这是逐态几乎必然恢复，不是给零先验行免除要求的平均恢复。允许族遍历上述种子空间、标签空间及种子律；不要求每个预先指定的原子种子源都能实现该族的全部实验。只有一个种子原子的源只能产生一个确定性编码，这已经说明两种量词不同。

沿用（535.4）的 Blackwell 序：$F\preceq E$ 表示存在一个不额外读取实际状态的 Markov 核将每条 $E_s$ 送到 $F_s$，左端信息较少；双向模拟记为 $E\simeq F$。模拟器可以读取源输出中的 $q$，不预加逐输入保持 $q$ 的公理。定义情境冲突图 $G$：不同 $k,l$ 相邻，当且仅当存在 $q$ 使 $k,l\in A_q$ 且 $t(k,q)\ne t(l,q)$。令 $\Pi_G$ 为 $K$ 的所有分划中每个块都是 $G$ 独立集者，称为全局充分分划。离散分划总在 $\Pi_G$ 中；某对情境在一个读数下同目标，并不排除它们在另一个实际读数下冲突。

第 536 章在特殊中心—叶支撑上给出了公开种子的有限规范形；第 537 章则分类了该支撑的私有随机通道。以下研究任意有限实际支撑上的公开种子族，不把第 537 章的共同中心条件移植为一般假设。所问的成对数据是每个二态限制各自的 Blackwell 等价类，彼此没有对齐的共同输出表示；它不同于保留每一对的完整原始概率核。区分这两种读法是本章结论的条件。

### 定理 538.2（一个全局分划律的规范像与双向可测实现）

对 $P\in\Pi_G$，令

$$
P|_{A_q}=\{B\cap A_q:B\in P,\ B\cap A_q\ne\varnothing\}.
$$

以全部 $(q,C)$、$\varnothing\ne C\subseteq A_q$ 为坐标，定义线性映射 $M$ 和有限凸多面体

$$
(Mp)_C^q=\sum_{P\in\Pi_G}p_P\mathbf1_{\{C\in P|_{A_q}\}},\qquad
\mathcal P=M\Delta(\Pi_G),
\tag{538.4}
$$

其中 $\Delta(\Pi_G)=\{p_P\ge0:\sum_Pp_P=1\}$。对 $w\in\mathcal P$ 定义有限规范实验 $W_w$，其输出空间为 $\mathcal O=\bigsqcup_{q\in Q}\{q\}\times(2^{A_q}\setminus\{\varnothing\})$，行律为

$$
W_w((q',C)\mid k,q)
=\mathbf1_{\{q'=q\}}\mathbf1_{\{k\in C\}}w_C^q.
\tag{538.5}
$$

每个定义 538.1 的充分实验都与某个 $W_w$ 双向可测模拟；反之，恰好 $w\in\mathcal P$ 的这些规范剖面可由允许的公开种子编码实现。所有读数的坐标须来自（538.4）中的同一个 $p$。该 $p$ 是实现见证，不承诺唯一；$w$ 的等价类唯一性由定理 538.3 给出。

证明：先从一般标准 Borel 编码提取分划。对每个实际 $(k,q)$，（538.3）及被积函数取值于 $[0,1]$ 保证

$$
N_{k,q}=\{r:D(\{t(k,q)\}\mid q,r,f(r,k))<1\}
$$

为可测零集。有限并 $N=\bigcup_{(k,q)\in S}N_{k,q}$ 仍为同一个可测零集。在 $r\notin N$ 上，若 $f(r,k)=f(r,l)$ 而 $k,l$ 在某个实际读数下目标不同，同一概率律 $D(\cdot\mid q,r,f(r,k))$ 就必须给两个不同目标各质量一，矛盾。因此由 $k\sim_r l\iff f(r,k)=f(r,l)$ 产生的分划 $P_r$ 属于 $\Pi_G$。在 $N$ 上把 $P_r$ 补成离散分划。标准 Borel 空间 $Z$ 的对角线可测，$K$ 有限，指定一个分划所需的全部相等及不等条件是有限个可测集合的交；故 $r\mapsto P_r$ 可测。取 $p_P=\rho\{r:P_r=P\}$，便得到（538.4）中的一个共同律。

每个局部分划恰有一个块含给定 $k\in A_q$，所以

$$
w_C^q\ge0,\qquad \sum_{C\ni k}w_C^q=1\quad(k\in A_q).
\tag{538.6}
$$

这保证（538.5）为概率核。若 $w_C^q>0$，至少有一个充分全局分划的局部块为 $C$，故 $t(\cdot,q)$ 在 $C$ 上恒定，规范输出也足以恢复原目标。

正向模拟器在收到 $(q,r,z)$、且 $r\notin N$ 时，计算

$$
C(q,r,z)=\{l\in A_q:f(r,l)=z\}.
$$

非空时输出 $(q,C(q,r,z))$。在 $N$ 或所得集合为空的输入上，输出一个预先选定的 $(q,C_q^0)\in\mathcal O$。有限相等判定保证这是处处定义的可测映射。在实际行 $k$ 上，除共同零集外，所得 $C$ 正是 $P_r|_{A_q}$ 中含 $k$ 的块，因此推前行律恰为（538.5）。此映射在接收端使用 $q$，没有赋予原编码器读取 $q$ 的权限。

反向模拟器需要恢复整个种子，不能只输出一个有相同碰撞概率的新标签。对非空 $C\subseteq A_q$ 令

$$
H_C^q=\{r\notin N:C\in P_r|_{A_q}\},\qquad
\rho_C^q(B)=\frac{\rho(B\cap H_C^q)}{w_C^q}\quad(w_C^q>0).
\tag{538.7}
$$

因 $N$ 为零集，分母就是 $\rho(H_C^q)$。从输入 $(q,C)$ 按 $\rho_C^q$ 抽样 $r$，再输出 $(q,r,f(r,k_C))$，其中 $k_C$ 是 $C$ 的一个固定代表。在 $H_C^q$ 上，所有 $k\in C$ 都给同一标签，所以该输出不依赖代表选择。在实际行 $k$ 上，$\{H_C^q:C\ni k\}$ 两两不交且覆盖 $\mathcal R\setminus N$；按 $w_C^q$ 混合这些限制律，正好恢复 $\rho$ 及 $(R,f(R,k))$ 的联合律。若 $w_C^q=0$，该输入在全部实际行均不可达，统一补成某个固定 $(q,r_0,z_0)$ 的 Dirac 律。输入空间有限，正质量行是明确的概率测度推前，故得到处处可测的 Markov 核。既未条件化于单个零质量种子，也未遗失原种子的连续部分。

反之，对任意 $p\in\Delta(\Pi_G)$，用有限标准 Borel 种子空间 $\Pi_G$ 及种子律 $p$，标签取 $K$ 的非空子集，发送

$$
f(P,k)=[k]_P.
\tag{538.8}
$$

该编码只读 $P,k$；观察者取得 $(q,P,[k]_P)$ 后，由非空 $[k]_P\cap A_q$ 上的恒定目标解码，对不可达输入任取固定目标。于是每个实际行精确恢复 $T$，正向规范化给出 $Mp$。这证明整个允许族上的充分必要性。证毕。

（538.6）是经典 CAR 的行方程；无冲突、一个共同读数时，（538.4）正是分划混合的 CCAR 表示。这两项并非本章提出的新一般理论。Gill–Grünwald, *An Algorithmic and a Geometric Characterization of Coarsening At Random*，§2 的 CAR 定义及 CARgen 过程给出对应背景，§6.1 给出 CAR 仿射空间；见 [arXiv:math/0510276v3](https://arxiv.org/html/math/0510276v3)，*Annals of Statistics* 36(5)（2008），2409–2422，[DOI:10.1214/07-AOS532](https://doi.org/10.1214/07-AOS532)。Jaeger, *Ignorability in Statistical and Probabilistic Inference*，Theorem 2.14 明确将 d-CCAR 刻画为分划混合，Example 4.4 给出独立选择分划的生成方式；见 [arXiv:1109.2143v1，印刷页 896、907](https://arxiv.org/pdf/1109.2143v1)，*JAIR* 24（2005），889–917，[DOI:10.1613/jair.1657](https://doi.org/10.1613/jair.1657)。这里在每个实际行施加恢复条件，并把所有读数的局部分划接到同一全局充分分划律；其可测归约还保留了整个一般标准 Borel 种子。Jaeger 的程序稳健性定理另有其定义及假设，不能把本处允许选择任意种子律读作对任意指定源的稳健性结论。

有两个不同的联合障碍。其一，即使每个读数单独都能由分划混合实现，也不一定存在共同 $p$。取 $K=\{1,2,3\}$，实际支撑恰为 $A_{q_{12}}=\{1,2\}$、$A_{q_{23}}=\{2,3\}$、$A_{q_{13}}=\{1,3\}$，所有目标为零。在前两个读数总是合并该对，在第三个读数总是分开；三个局部实验分别合法。若由共同 $p$ 实现，事件 $1\sim_P2$、$2\sim_P3$ 都有概率一，交集也有概率一；每个分划的传递性又使 $1\sim_P3$ 在交集上成立，与第三个要求矛盾。这用的是六条实际行，没有添加别的组合。

其二，单个读数的 CAR 行方程本身也不足够。取 $A_q=\{1,2,3\}$，$w_{12}=w_{13}=w_{23}=1/2$，其他非空子集权重为零；每条行之和确为一。若有分划混合，零权重排除了所有含单点块或三点块的分划，而三点集不可能完全分成二点块，故不存在实现。这正是 Gill–Grünwald §2 Example 1 所引的三角反例，不把它列为本章的新反例。前一个跨读数障碍则说明，即使排除了每个局部的这类 CAR/CCAR 差别，还必须检验（538.4）的共同像条件。

最后，即使保留整个 $w$，潜在分划律也可不同。在无冲突的四情境共同读数上，记 $1|2|3|4$ 为离散分划，则

$$
\begin{aligned}
p&=\tfrac12\delta_{1|2|3|4}+\tfrac12\delta_{12|34},\\
p'&=\tfrac12\delta_{12|3|4}+\tfrac12\delta_{1|2|34}
\end{aligned}
\tag{538.9}
$$

不同，却都给每个单点块权重 $1/2$、给 $12,34$ 各权重 $1/2$，其余为零：第一律的单点来自离散分划，第二律中 $1,2$ 的单点来自第二项，$3,4$ 的单点来自第一项。故 $Mp=Mp'$，相应实验经本定理互相模拟。潜在分划律的多解不是可观察的信息逃逸，也不能作为不可比实验的见证。

### 定理 538.3（允许读取旧读数的精确子集流与等价判据）

固定定义 538.1 的同一 $S,t$，取 $w,v\in\mathcal P$。有 $W_v\preceq W_w$，当且仅当对每个 $q\in Q$ 存在非负数

$$
f_{BC}^q\quad(\varnothing\ne B\subseteq C\subseteq A_q)
$$

满足

$$
\begin{aligned}
\sum_{C\supseteq B}f_{BC}^q&=w_B^q
&& (\varnothing\ne B\subseteq A_q),\\
\sum_{\substack{\varnothing\ne B\subseteq C\\k\in B}}f_{BC}^q&=v_C^q
&& (\varnothing\ne C\subseteq A_q,\ k\in C).
\end{aligned}
\tag{538.10}
$$

这里 $B$ 是源输出、$C$ 是目标输出；流可以依赖已经可见的 $q$，不依赖未知情境。进而

$$
W_v\simeq W_w\quad\Longleftrightarrow\quad v=w.
\tag{538.11}
$$

所以整个充分公开族的实际实验等价类恰由 $\mathcal P$ 中的剖面 $w$ 唯一参数化。

证明：设有任意状态无关模拟核 $H:\mathcal O\to\operatorname{Prob}(\mathcal O)$。先推导活跃输入上的 $q$ 保持性。固定 $q$ 和 $w_B^q>0$ 的源块，取 $k\in B$。在实际行 $(k,q)$，目标输出落在其他读数的总质量为零；它是源块上的非负和，因此

$$
w_B^qH(\{(q',C):q'\ne q\}\mid q,B)=0.
$$

所以该源块上的模拟必保持 $q$。再固定同读数目标块 $C$ 和 $k\notin C$，其目标行概率为零。若 $k\in B$ 且 $w_B^q>0$，同一非负和论证使 $H((q,C)\mid(q,B))=0$。因此任何正质量转移都满足 $B\subseteq C$。两项限制都是实际行等式的后果，未对原核额外设限。

令 $f_{BC}^q=w_B^qH((q,C)\mid(q,B))$。核行和为一及刚得的支撑限制给出（538.10）第一式；对实际行 $(k,q)$ 计算目标块 $C$ 的质量给出第二式。源权重为零的块给零流，不需要辨认该处原核的值。

反向，若（538.10）成立，在 $w_B^q>0$ 时定义

$$
H((q,C)\mid(q,B))=\frac{f_{BC}^q}{w_B^q}
\quad(B\subseteq C),
\tag{538.12}
$$

其他目标输出的概率为零。第一式保证该行为概率律，第二式保证每个 $k\in C$ 的目标质量正确。若 $k\notin C$，所有能到达 $C$ 的 $B$ 都不含 $k$，所以该实际行质量也正确地为零。对 $w_B^q=0$ 的源块任取一个固定输出概率律；它们在所有实际行都不出现。这样按有限个 $q,B$ 拼接成同一个可测、状态无关的核，证明充分性。

为证唯一性，对每个 $q$ 定义 $J_q(w)=\sum_{\varnothing\ne B\subseteq A_q}w_B^q$。把（538.10）第二式对 $k\in C$ 求和后除以 $|C|$，再对 $C$ 求和，得到

$$
J_q(v)=\sum_{B\subseteq C}f_{BC}^q\frac{|B|}{|C|}
\le\sum_{B\subseteq C}f_{BC}^q=J_q(w).
\tag{538.13}
$$

全部求和只含非空子集。等号成立当且仅当每项满足 $f_{BC}^q>0\Rightarrow B=C$，因为真包含时 $|B|/|C|<1$。若双向模拟，每个 $q$ 上两向不等式迫使等号，取其中一向的流就只剩对角项；（538.10）随即给出 $v_C^q=f_{CC}^q=w_C^q$。反之 $v=w$ 使用恒等核。$J_q(w)$ 也等于随机局部分划的期望块数，但证明只依赖剖面和流，不依赖选择哪一个 $p$。证毕。

本定理用有限规范输出直接完成多态共同核比较，不把各二态上分别存在的恢复核当作同一个核。一般统计实验比较与数据处理等号恢复有既有文献，不能将此类原则认作新发现。相关二态完整性结果见 Galke–van Luijk–Wilming, *Sufficiency of Rényi divergences*，[arXiv:2304.12989v6](https://arxiv.org/html/2304.12989v6)，Theorems 13–14 要求所列绝对连续条件，Appendix A Theorem 32 处理非正交而可能带奇异部分的情形；该文发表于 *IEEE Transactions on Information Theory* 70(7)（2024），5057–5076，[DOI:10.1109/TIT.2024.3376395](https://doi.org/10.1109/TIT.2024.3376395)。这些二态定理本身没有提供本章任意实际支撑上的统一多态模拟器；（538.10）承担的正是这里所需的全部同时行约束。

### 定理 538.4（二态等价类的完整读数与固定读数下的反链）

对每个 $q$ 及不同的 $k,l\in A_q$，定义

$$
r_{kl}^q=\sum_{C\supseteq\{k,l\}}w_C^q.
\tag{538.14}
$$

$W_w$ 在实际行 $(k,q),(l,q)$ 上的二态限制，与擦除实验 $B_{r_{kl}^q}$ 等价：在任一状态以相同概率 $r_{kl}^q$ 输出共同符号 $\star$，以其余概率直接报告该状态。$r_{kl}^q$ 是这个带固定状态标签的二态 Blackwell 类的完整不变量。不同读数的任意两实际行则完全可分。因而所有分别保留的二态等价类，恰好给出（538.14）的整组数值，没有提供各对之间对齐的输出表示。

记 $Lw=(r_{kl}^q)_{q,\{k,l\}\subseteq A_q}$。对于同一可实现成对剖面 $r$，不同的 $w,v\in\mathcal P$ 若 $Lw=Lv=r$，则 $W_w,W_v$ 两向都不可模拟。这里的不同指 $w\ne v$，不指某两个潜在实现律 $p\ne p'$。

证明：在固定二态限制中，含 $k,l$ 的输出块具有相同行概率 $w_C^q$，总质量为 $r_{kl}^q$；只含其中一者的输出可以无误识别状态。把前者全部映至 $\star$、后者映至对应状态，得到擦除实验。反向，从 $\star$ 按权重 $w_C^q/r_{kl}^q$ 选择共同块，从已报告状态按其专属块上的权重 $w_C^q/(1-r_{kl}^q)$ 选择输出。两种权重族各自归一化；分母为零时相应输入不可达，任意补成概率律。故两向核均存在。等先验二态识别的最小错误为 $r_{kl}^q/2$：专属输出无错，共同输出的两个状态等可能，最小条件错误为 $1/2$。模拟核可与任何决策复合，所以双向模拟必保留这个最小错误，迫使擦除率相等；率相等又给相同规范实验。这证明完整性，包括 $r=0,1$。不同读数的两行直接由可见 $q$ 分离，故属于完全揭示的二态类。

为证反链，假设 $W_v\preceq W_w$ 并取定理 538.3 的流。省略固定 $q$ 的上标，将目标的成对质量用（538.10）在状态 $k$ 的行展开，再用源流行和展开源的成对质量，得到精确差值

$$
\begin{aligned}
r_{kl}(v)-r_{kl}(w)
&=\sum_{C\supseteq\{k,l\}}
  \sum_{\substack{\varnothing\ne B\subseteq C\\k\in B,\ l\notin B}}f_{BC}
\ge0.
\end{aligned}
\tag{538.15}
$$

确切地，目标展开包含全部 $k\in B\subseteq C$ 且 $k,l\in C$ 的项；源展开为全部 $k,l\in B\subseteq C$ 的项。后者恰抵消前者中 $l\in B$ 的部分，留下右端，故没有把总量上界用作局部下界。若存在 $f_{BC}>0$ 且 $B\subsetneq C$，取 $k\in B$、$l\in C\setminus B$，右端就严格为正。所有成对数值相同排除了每条这样的流，剩余流只在 $B=C$，由（538.10）得 $w=v$。$|A_q|=1$ 时只有一个非空块，已由行和固定，不需成对坐标。对每个 $q$ 应用该论证，即证一向模拟也迫使相等；交换 $w,v$ 得到反链结论。证毕。

须把这个结论与另一种成对保留方式严格分开。若 $|S|\ge2$，所谓“所有成对数据”实际保存的是同一个输出可测空间上、保留原输出标识的所有二行核 $E|_{\{s,s'\}}$，则它们逐字决定每条完整行：对任意 $s$ 任选 $s'\ne s$，读取该二行核的 $s$ 行即可。所有行齐备便决定整个实验，根本没有上述信息残差。此论证不要求输出有限，也不要求不同状态的行律不同。$|S|=1$ 时没有二行限制，空的成对清单不决定该单行的字面概率律，虽然所有单态实验都可用状态无关重抽样互相模拟。本定理的反链只针对分别取商而失去对齐表示的二态类。

### 定理 538.5（共同可实现纤维与剩余高阶碰撞坐标）

固定 $S,t$ 及可行成对值 $r\in L(\mathcal P)$。与全部这些二态类相容的实际实验等价类恰为

$$
\mathcal F_r
=\mathcal P\cap L^{-1}(r)
=\{Mp:p\in\Delta(\Pi_G),\ LMp=r\}.
\tag{538.16}
$$

在该纤维内，全部尚能变化的可观察信息由可实现的高阶碰撞坐标给出。具体地，对 $\varnothing\ne D\subseteq A_q$ 定义

$$
a_D^q=\sum_{C\supseteq D}w_C^q.
\tag{538.17}
$$

单点坐标恒为一，二点坐标是 $r$，且

$$
w_C^q=\sum_{D:\,C\subseteq D\subseteq A_q}
             (-1)^{|D|-|C|}a_D^q.
\tag{538.18}
$$

因此固定二态类后，不同 $w$ 当且仅当某个 $|D|\ge3$ 的 $a_D^q$ 不同。这里“可实现”仍要求（538.16）的同一个全局分划律，不能给高阶坐标任意赋值。若同一个情境子集 $D$ 同时包含在 $A_q,A_{q'}$ 中，那么 $a_D^q=a_D^{q'}$；它是一个共同碰撞事件的概率，不是可独立调整的两个局部参数。

证明：（538.16）由定理 538.2 的实现充要条件、定理 538.3 的等价唯一性及定理 538.4 的二态分类合成。对实现律 $p$，事件“$D$ 的全部成员在 $P$ 的同一个块中”恰等于互不相交的事件之并：局部分划有一个含 $D$ 的块 $C$。其概率就是（538.17）。该事件本身不依赖选哪个含 $D$ 的读数，故跨读数等式成立；若 $D$ 含冲突边，该概率必为零。

为说明（538.18），代入（538.17），某个 $w_E^q$ 的系数为

$$
\sum_{D:\,C\subseteq D\subseteq E}(-1)^{|D|-|C|}
=(1-1)^{|E\setminus C|}.
$$

当 $E=C$ 时这个空集和为一，其他情形为零，故得到所需等式。这只是有限子集格上通常的 Möbius 反演，不是另一个一般反演新定理。单点值由（538.6）给一，二点值由（538.14）给 $r$；全部 $a$ 和全部 $w$ 于是互相决定，结论成立。证毕。

如果每个 $|A_q|\le2$，可行 $r$ 已决定唯一 $w$：二点活动集 $\{k,l\}$ 上 $w_{kl}=r_{kl}$、$w_k=w_l=1-r_{kl}$，单点活动集上权重为一。跨读数限制仍可能使一组候选 $r$ 不可行，但不会使一个已经可行的 $r$ 有两个剖面。相反，某个 $|A_q|\ge3$ 只提供高阶坐标的位置，不保证存在剩余自由度。例如共同三点读数且全部成对碰撞为零，任何含两点以上的块权重都为零，唯一剖面是完全揭示；若活动集内每对情境都由原目标构成冲突，也只允许这一局部剖面。精确问题始终是（538.16）有多少点，而不是最大活动集大小是否超过二。

不在任何 $A_q$ 中共同出现的情境集合，没有本章意义下的可观察 $a_D^q$；它们在某个潜在分划律中的相关性可以变化而不改变 $w$。式（538.9）更说明，即使存在一个全共同读数，块的同时出现方式仍可有潜在多解。高阶残差只包括会改变（538.17）、从而改变实际实验等价类的可行坐标，不包括被 $M$ 消去的实现见证差异。

### 定理 538.6（共同读数的仿射维数与一般边界纤维公式）

先取无冲突的完整共同读数模型：$K=\{1,\ldots,n\}$、$n\ge1$，$Q=\{q_0\}$、$S=K\times\{q_0\}$，$t$ 为常量，没有其他读数引入的冲突。记其剖面多面体为 $\mathcal P_n$，$L$ 仍为全部成对碰撞投影。则

$$
\begin{aligned}
\operatorname{aff}\mathcal P_n
&=\left\{w\in\mathbb R^{2^n-1}:\sum_{C\ni i}w_C=1\ (i=1,\ldots,n)\right\},\\
\dim\mathcal P_n&=2^n-n-1,\\
\operatorname{rank}(L|_{\operatorname{dir}\mathcal P_n})&=\binom n2.
\end{aligned}
\tag{538.19}
$$

其中 $\operatorname{dir}P=\operatorname{span}(P-P)$。若且唯若 $r\in\operatorname{ri}L(\mathcal P_n)$，纤维 $\mathcal F_r$ 与 $\operatorname{ri}\mathcal P_n$ 相交；在此条件下

$$
\dim\mathcal F_r
=2^n-1-\frac{n(n+1)}2.
\tag{538.20}
$$

$\operatorname{ri}$ 始终相对于本身的仿射包取内部。一般实际支撑的 $\mathcal P$ 也有精确边界公式：对非空 $\mathcal F_r$，取 $w^\circ\in\operatorname{ri}\mathcal F_r$，令 $F$ 为 $\mathcal P$ 中含 $w^\circ$ 的最小面，则 $F$ 包含整个纤维，$w^\circ\in\operatorname{ri}F$，且

$$
\dim\mathcal F_r
=\dim F-\operatorname{rank}(L|_{\operatorname{dir}F}).
\tag{538.21}
$$

因此纤维是单点当且仅当右端为零；右端严格为正时它包含连续多个互不可比的实验类。非空条件不可省略。

证明（538.19）。令 $e_C$ 为子集坐标单位向量，离散分划的剖面为 $w^0=\sum_i e_{\{i\}}$。对每个 $B\subseteq K$、$|B|\ge2$，取只有 $B$ 作为非单点块、其余为单点的分划，其剖面与 $w^0$ 的差为

$$
d_B=e_B-\sum_{i\in B}e_{\{i\}}.
\tag{538.22}
$$

这些都是可实现点的差。在所有非单点坐标上，每个 $d_B$ 只在自己的 $B$ 坐标为一，故它们线性独立，共 $2^n-1-n$ 个。另一方面，$n$ 个行方程的系数矩阵在单点列上是单位矩阵，故独立，给出同一维数的上界。于是这些方向张成整个行方程仿射空间的方向，得到前两式。对 $B=\{i,j\}$，$Ld_B$ 正是该成对坐标的单位向量：单点项没有任何成对碰撞，二点块只贡献这一对。因此 $L$ 在方向空间上满秩到 $\mathbb R^{\binom n2}$，证明第三式；$n=1$ 时目标空间为零维，论证仍成立。

相对内部和边界处的断言所需的凸几何事实可在这里直接证明。令任意非空有限多面体 $P=\operatorname{conv}\{u_1,\ldots,u_m\}$，容许生成点有重复。一个点在 $\operatorname{ri}P$ 中，当且仅当它有使用全部生成点的严格正凸组合表示。正组合给相对内部，是因为向量 $u_i-u_1$ 张成 $\operatorname{dir}P$，沿其中一组基作足够小的正负系数扰动并调整第一个系数，所有权重仍为正，因而在该点周围得到一个相对开邻域。反之，设 $x\in\operatorname{ri}P$，$b=m^{-1}\sum_i u_i$；若 $x=b$ 结论已得，否则可取小 $\varepsilon>0$ 使 $y=x+\varepsilon(x-b)\in P$，从

$$
x=\frac{1}{1+\varepsilon}y+
  \frac{\varepsilon}{1+\varepsilon}b
$$

取得全部权重严格为正的表示。

将此事实分别用于 $P$ 和 $LP=\operatorname{conv}\{Lu_i\}$。若 $x\in\operatorname{ri}P$，其正系数组合给 $Lx\in\operatorname{ri}LP$；若 $r\in\operatorname{ri}LP$，以相同正系数组合原来的 $u_i$，便得到 $x\in\operatorname{ri}P$ 且 $Lx=r$。这证明

$$
L(\operatorname{ri}P)=\operatorname{ri}(LP)
\tag{538.23}
$$

而没有假设每个指定原像都在内部。选这样的 $x$，$P\cap L^{-1}(r)$ 在 $x$ 附近包含 $x+(\operatorname{dir}P\cap\ker L)$ 的相对开邻域，其全部点又在这个仿射空间内，故纤维维数为 $\dim P-\operatorname{rank}(L|_{\operatorname{dir}P})$。代入（538.19）即得（538.20）。特别地，正权重使用全部充分分划是得到内部点的一种充分方式；结论不要求某个已经给定的分划见证具有这项正性。

对边界纤维，取 $w^\circ\in\operatorname{ri}\mathcal F_r$。多面体在其仿射包中由有限个线性不等式描述；把 $w^\circ$ 处取等的那些不等式同时取等，所得就是最小面 $F$。其余不等式在该点严格，因此 $w^\circ$ 在 $F$ 中有相对开邻域，即 $w^\circ\in\operatorname{ri}F$。若 $y\in\mathcal F_r$、$y\ne w^\circ$，相对内部性质允许选小 $\varepsilon>0$，使 $z=w^\circ+\varepsilon(w^\circ-y)\in\mathcal F_r$。于是 $w^\circ$ 位于 $y,z$ 之间的开线段上；某个支撑不等式在 $w^\circ$ 取等时，由两端都满足该不等式，它在 $y,z$ 上也取等。因此每个 $y$ 都在 $F$ 中。反过来 $F\subseteq\mathcal P$，故纤维正是 $F\cap L^{-1}(r)$。现在在 $F$ 的相对内部点重复上一段局部邻域论证，得到（538.21）。零维非空凸集恰为单点，正维凸集含非退化线段；定理 538.4 给这些不同点的不可比性。证毕。

$\operatorname{aff}\mathcal P_n$ 与 CAR 的仿射空间相同，不意味着 $\mathcal P_n$ 是全部非负 CAR 行解；定理 538.2 的三角反例已经区分两者。式（538.19）中的 CAR 仿射维数在 Gill–Grünwald §6.1 已有，本章的（538.22）说明分划混合自身也张成该空间，然后对可观察剖面作成对投影和纤维切片。坐标 $w_C>0$ 也不是相对内部的替代判据：在三情境模型中，取 $w_{123}=1/10$、所有二点及单点权重均为 $3/10$，它由三种“二点块加剩余单点”的分划各权重 $3/10$ 及全合并分划权重 $1/10$ 实现，全部七个坐标都正。但令 $R=r_{12}+r_{13}+r_{23}$，对五种三点分划逐个计算可得 $1-R+2w_{123}$ 就是离散分划的权重，因而在 $\mathcal P_3$ 上非负；本例取零，离散分划则取一，故本例位于一个真支撑面上，不在 $\operatorname{ri}\mathcal P_3$。这与它所在的纤维可以另有内部点相容。

成对像 $L(\mathcal P_n)$ 是已知的 clique-partition polytope：每个分划给出“是否同块”的 $0/1$ 成对向量，再取其凸包。Koike–Lin–Wang, *Invariant correlation under marginal transforms*，[arXiv:2306.11188v4，2024-08-15](https://arxiv.org/html/2306.11188v4)，Theorem 4 明确给出该凸包识别，Example 6 列出三情境的五个顶点及 triangular bipyramid。该几何对象的经典来源包括 Grötschel–Wakabayashi, *Facets of the clique partitioning polytope*，*Mathematical Programming* 47（1990），367–387，[DOI:10.1007/BF01580870](https://doi.org/10.1007/BF01580870)；此处只使用其题目、书目信息及定义层面的历史归属，不调用该文全文中的面分类。这里讨论的是已知成对多面体之上的可实现实验剖面纤维，不给它另起新多面体名称，也不把三情境五顶点几何认作新增结果。

### 定理 538.7（三情境固定二态类的全部实现与相反风险）

取定理 538.6 中 $n=3$ 的共同读数、无冲突模型。给定候选成对值 $(r_{12},r_{13},r_{23})\in[0,1]^3$，令

$$
R=r_{12}+r_{13}+r_{23},\qquad
\ell=\max\left(0,\frac{R-1}{2}\right),\qquad
u=\min(r_{12},r_{13},r_{23}).
\tag{538.24}
$$

全部可实现固定成对剖面恰由参数 $t\in[\ell,u]$ 给出，其中 $t=w_{123}$。具体的五种分划权重为

$$
\begin{aligned}
p_{123}&=t,\\
p_{ij|k}&=r_{ij}-t\quad(\{i,j,k\}=\{1,2,3\}),\\
p_{1|2|3}&=1-R+2t.
\end{aligned}
\tag{538.25}
$$

相应全部七个非空块权重为

$$
\begin{aligned}
w_{123}&=t,\\
w_{ij}&=r_{ij}-t,\\
w_i&=1-r_{ij}-r_{ik}+t
\quad(\{i,j,k\}=\{1,2,3\}).
\end{aligned}
\tag{538.26}
$$

若 $\ell>u$，纤维为空；若 $\ell=u$，纤维是唯一剖面；若 $\ell<u$，它是非退化线段，其中不同点的实际实验两向不可比。候选成对坐标若有一个不在 $[0,1]$，也不可能实现。

在三状态均匀先验下，另考虑两个不替换原目标的决策任务。识别任务的行动为 $\{1,2,3\}$，损失 $\lambda_{\mathrm{id}}(k,a)=\mathbf1_{\{k\ne a\}}$；排除任务的行动仍为 $\{1,2,3\}$，损失 $\lambda_{\mathrm{ex}}(k,a)=\mathbf1_{\{k=a\}}$，即尝试报告一个不是真实状态的标签。对应的精确最小风险是

$$
\mathcal R_{\mathrm{id}}(t)=\frac{R-t}{3},\qquad
\mathcal R_{\mathrm{ex}}(t)=\frac{t}{3}.
\tag{538.27}
$$

因此非退化纤维上，增大三方碰撞严格改善识别风险，同时严格恶化排除风险；全部二态类不变，原常量目标仍完全可恢复。

证明：三情境只有五种分划：全分开、三个“合并一对”、全合并。同块对 $ij$ 只在后者及对应的 $ij|k$ 中出现，所以 $r_{ij}=p_{ij|k}+p_{123}$。把 $p_{123}$ 记作 $t$ 后，归一化使剩余离散权重为 $1-R+2t$，即（538.25）；因此这里不存在另一个潜在分划自由度。五权重非负等价于

$$
t\ge0,\quad t\ge(R-1)/2,\quad t\le r_{12},r_{13},r_{23},
$$

恰为 $[\ell,u]$。反之满足这些约束时五权重之和为一，由（538.8）得到充分公开编码。二点块只由其对应分划贡献，单点 $i$ 由离散分划及 $jk|i$ 贡献，得到（538.26）。无需另加看似独立的单点非负条件，它们已经是非负分划权重之和。参数 $t$ 直接是规范剖面中的一个坐标，所以区间到纤维为单射，以上又证明满射；空、单点和线段三种情况穷尽，由定理 538.4 得到线段各异点的反链性质。

风险可以直接按观察到的非空块 $C$ 计算。该输出在均匀先验下的概率为 $|C|w_C/3$；正概率时后验是 $C$ 上的均匀律。识别任务在该输出下的最小条件错误为 $1-1/|C|$，因此

$$
\mathcal R_{\mathrm{id}}
=\frac13\sum_C(|C|-1)w_C
=\frac13\bigl((R-3t)+2t\bigr)
=\frac{R-t}{3}.
$$

排除任务在 $C\ne\{1,2,3\}$ 时选取 $C$ 外的一个行动即可零错；在全块上，每个行动的条件损失都是 $1/3$，而该输出概率为 $t$，故最小风险为 $t/3$。这些规则在有限空间上可测并达到所列值；随机化是行动损失的凸组合，不可能改进逐输出最小值。零权重输出任取行动，不影响风险。可见两项风险之和固定为 $R/3$，并各自随 $t$ 以相反的严格方向变化。证毕。

例如 $r_{12}=r_{13}=r_{23}=1/3$ 时，$R=1$、$0\le t\le1/3$。记端点 $W_{\mathrm A}$ 为 $t=1/3$、$W_{\mathrm B}$ 为 $t=0$。前者以概率 $1/3$ 选全合并分划、概率 $2/3$ 选离散分划；后者均匀选择三种 $ij|k$。由（538.27）直接得到

$$
\begin{array}{c|cc}
 &\mathcal R_{\mathrm{id}}&\mathcal R_{\mathrm{ex}}\\ \hline
W_{\mathrm A}&2/9&1/9\\
W_{\mathrm B}&1/3&0
\end{array}
\tag{538.28}
$$

这对风险的分离有明确的经典先例，不宜当作独立首创。Bertschinger–Rauh, *The Blackwell relation defines no lattice*，[arXiv:1401.3146v1，Example 18](https://arxiv.org/html/1401.3146v1)，使用

$$
\kappa=\begin{pmatrix}
1/2&0&0&1/2\\
0&1/2&0&1/2\\
0&0&1/2&1/2
\end{pmatrix},\qquad
\mu=\begin{pmatrix}
1/2&1/2&0\\
1/2&0&1/2\\
0&1/2&1/2
\end{pmatrix}
\tag{538.29}
$$

并以三行动的“避免真实状态”收益说明一种较弱比较不足以推出 Blackwell 支配。若 $I$ 是三态完全识别通道，$aH\oplus(1-a)I$ 表示先以状态无关概率选择通道、保留互不相交的可见分支标签，再输出相应结果的实验，则

$$
W_{\mathrm A}\simeq\tfrac23\kappa\oplus\tfrac13 I,
\qquad
W_{\mathrm B}\simeq\tfrac23\mu\oplus\tfrac13 I.
\tag{538.30}
$$

验证第一式时，把同一单点上成比例的列合并，得到每个单点权重 $1/3+1/3=2/3$、全块权重 $1/3$；第二式中三个二点列各权重 $1/3$、三个单点列各权重 $1/3$，就是（538.26）的另一端点。合并成比例列可以反向模拟：按这些列的比例作状态无关随机分裂。因此这里的等价是带标签混合后的等价，不是把未标记的矩阵凸组合当成同一实验。$\mu$ 单独对应三角 CAR 例，并不在本公开分划允许族内；第二式只给等价的抽象表示，其真正允许的实现是前述三个 $ij|k$ 的共同分划种子。

（538.28）的数值从明确的均匀先验及零一损失重新推出，不借用该文显示的另一个收益数值。已知端点机制、三角 CAR 障碍、三情境成对像的五顶点几何都是前置；这里将它们放入整个固定二态类纤维，给出全部实现参数、不可比性以及两种风险随同一参数变化的精确关系。

### 定理 538.8（非恒定原目标中的同读数嵌入与提升的排除任务）

将定理 538.7 的三个情境嵌入 $K=\{1,2,3,d\}$。仍只有一个共同读数 $q_0$，实际行恰为

$$
(1,q_0,0),\quad(2,q_0,0),\quad(3,q_0,0),\quad(d,q_0,1).
\tag{538.31}
$$

故原目标 $T$ 非恒定，$q_0$ 单独不能恢复它。全部充分全局分划恰是三点分划再加单点块 $\{d\}$，从而对任何可行的三点 $r$，其固定二态类纤维与定理 538.7 的区间完全相同。特别地，每个 $t$ 的规范剖面满足 $w_{\{d\}}=1$，混含 $d$ 与三点情境的块权重为零，其余块由（538.26）给出。三点内部成对碰撞保持 $r$，三条涉及 $d$ 的碰撞为零。

给定 $0<\alpha<1$，先验取 $\Pr(k=i)=\alpha/3$（$i=1,2,3$）、$\Pr(k=d)=1-\alpha$。四态识别允许行动 $\{1,2,3,d\}$，损失仍为识别错误。提升的排除任务则明确只允许行动 $\{1,2,3\}$，定义

$$
\lambda_{\mathrm{lex}}(k,a)=
\begin{cases}
\mathbf1_{\{k=a\}},&k\in\{1,2,3\},\\
0,&k=d,
\end{cases}
\qquad a\in\{1,2,3\}.
\tag{538.32}
$$

在同一先验下，精确最小风险为

$$
\mathcal R_{\mathrm{id},4}(t)=\alpha\frac{R-t}{3},\qquad
\mathcal R_{\mathrm{lex}}(t)=\alpha\frac{t}{3}.
\tag{538.33}
$$

条件于三点事件，风险分别为 $(R-t)/3$、$t/3$；条件于 $d$，两者均为零。相反，如果把排除行动放宽为全部四个标签并仍用 $\mathbf1_{\{k=a\}}$，其最小风险对本族所有 $t$ 都是零。

证明：$d$ 与每个三点情境在同一读数下目标不同，所以冲突图恰为以 $d$ 为中心的三边星；每个充分分划必须把 $d$ 单独放置，三点内部则没有冲突。删去或添加这个单点块给充分分划集合的双射。对这些分划使用同一分布（538.25）和编码（538.8），便实现所述剖面；反过来每个充分编码经定理 538.2 都来自这种分划律，因此没有遗漏其他充分公开剖面。全局原目标的解码是：输出块为 $\{d\}$ 时报告一，输出在三点内时报告零。它在每个实际行上正确，不取决于先验参数 $\alpha$。

观察到 $\{d\}$ 时真实情境已确定为 $d$，四态识别选择 $d$，提升的排除任务任选允许行动，两项损失均为零。观察到三点内的 $C$ 时，不可能为 $d$，条件后验仍均匀于 $C$。在四态识别中选择 $d$ 必错，故最优行动在三点内，与定理 538.7 相同；提升的排除任务的行动和损失也恰是该定理的三点任务。三点事件本身的先验质量为 $\alpha$，其与 $d$ 事件可被输出精确区分，所以分别乘以 $\alpha$ 就得到（538.33），同时得到两种条件风险。由于最优规则都明确存在，条件最优值和无条件最优值之间没有隐藏的共同决策冲突。

最后，四态 unrestricted 排除在三点块上选行动 $d$，在输出 $\{d\}$ 上选行动 $1$，处处零损失，非负性保证这就是最小值。因此不能把（538.33）的第二式错报为无约束四态排除风险。证毕。

本嵌入在同一个可见读数下使原 $T$ 真正非恒定，且整条非退化纤维上的每个编码都精确完成原任务；识别与提升排除是另外指定的决策任务。对（538.28）的两个端点，无条件风险分别是 $(2\alpha/9,\alpha/9)$ 与 $(\alpha/3,0)$，条件于三点事件则恢复（538.28）。所以成对类不可见的区别并非靠把原目标改成识别任务而产生，也不来自让新读数直接泄露 $T$。

### 定义 538.9（共同使用中的概念等价与解释界限）

在本章合同中，概念编码是否足够，先由原目标的逐态恢复定义；两个充分编码是否可替代，再由对全部实际行使用同一个状态无关模拟器定义。分别保存二态等价类只保留 $r$，完整的实际实验等价类则由 $w$ 给出。定理 538.5 说明二者之差恰位于满足共同实现条件的高阶碰撞坐标；定理 538.4 又说明，在固定 $r$ 的纤维内，不同 $w$ 的差异不能按“一个包含另一个的全部信息”排列。定理 538.7–538.8 把这种差异落实为同一先验、明确行动和损失下的相反风险变化。这为目的相关的概念边界提供一项具体区分：同样完成原目的，甚至在每一对使用情形上具有同等的信息能力，仍未必能在共同的多情境任务中互相替代。

这项区分承接本卷第 535 章对实际支撑与情境取得的分离、第 536 章对整个可见种子的处理、第 537 章对摘要与完整信息谱的分离；亦与[《数学与神话匹配》§§447–449](MATH_MYTH_MATCH.md) 中单项成绩、全部任务和共同模拟器的区分相接。这里增加的综合内容是一般有限支撑上的共同可实现剖面、精确子集流、固定二态类的整个纤维及其任务代价；CAR/CCAR、Blackwell 比较、有限 Möbius 反演、团分划成对像及已知三状态排除机制各按上述出处使用。该组合的用途在于把“缺少某种联合信息”变成可判定的共同律线性约束与可计算的风险差，而非只给一个成对不足的反例。上述具体前置及来源范围不承担全球优先性结论。

与维特根斯坦的对应仅限《哲学研究》§§65–69。§§65–67 要求查看实际使用中的交错相似，反对不经考察就断定同一名称必有贯穿全部使用的单一本质；§§68–69 允许为了“一个特定目的”划界，并明确这种划界不是通常语言得以有用的前提。参见 [Wittgenstein, *Philosophische Untersuchungen*, §§65–69](https://www.wittgensteinproject.org/w/index.php/Philosophische_Untersuchungen#65)，辅助释义见 [Stanford Encyclopedia of Philosophy, “Ludwig Wittgenstein”, §3.4](https://plato.stanford.edu/entries/wittgenstein/#LangGameFamiRese)。本章把目的、可见材料、取得权限及允许转换逐一固定，是一个特定目的下的数学规定；不把分划、标准 Borel 种子或 Blackwell 序归作维特根斯坦的学说，也不把家族相似等同于碰撞图或传递闭包。

因此这里的概念相对性指比较合同的明确依赖，不推出普遍相对主义；它没有给任何真实性别分类提供经验前提，也没有从信息可见性推出披露政策或道德义务。信息逃逸在这里指相对于分别保留的二态类仍存在不同的可实现 $w$，不是相对于所有可能描述都不可说：有限剖面 $w$ 已完整分类本允许族，某些纤维甚至是单点。改变支撑、原目的、随机种子可见性或模拟权限会形成新的问题，不能从本章有限纤维推出逃逸必然无限持续。本章的推导为上述假设下的纸面证明，不赋予这些陈述内核认证地位。

## 追加锚（本行以下为增补区）

## 539. 成对信息损失何时允许整体恢复：公开块实验的逆向误差与最坏识别

### 定义 539.1（同一实际支撑上的比较方向与误差）

固定定义 538.1 的有限非空实际行集 $S=\{(c(x),q(x)):x\in A\}$、活动情境集 $A_q$ 及原目标 $t(k,q)$，仍要求同一实际行具有唯一目标。令 $n_q=|A_q|\ge1$。编码器只读取情境与独立种子，观察者得到整个种子、编码标签和旧读数 $q$；原目标在每个实际行几乎必然恢复。每个实验分别由一个全局充分分划律实现，故其规范剖面属于

$$
\mathcal P=M\Delta(\Pi_G),\qquad
W_w^q(C\mid k)=\mathbf1_{\{k\in C\}}w_C^q,
\qquad \varnothing\ne C\subseteq A_q.
\tag{539.1}
$$

所有读数的 $w^q$ 来自同一个分划律 $p_w$；另一个实验 $v$ 可以有自己的共同律 $p_v$。不要求存在源、目标种子的耦合，使两个随机全局分划逐次同时细化。允许的比较核可以读取已经公开的 $q$ 并重新抽样，不能读取未知实际状态；该核本身不必是一个只读情境的公开编码器。

对同一状态集上的实验 $E,F$，定义从 $E$ 模拟 $F$ 的单向缺损

$$
d(E\longrightarrow F)
=\inf_K\max_{s\in S}\operatorname{TV}(E_sK,F_s),\qquad
\operatorname{TV}(\mu,\nu)=\sup_D|\mu(D)-\nu(D)|.
\tag{539.2}
$$

上确界遍历输出可测集；有限输出时 $\operatorname{TV}=\tfrac12\sum_y|\mu(y)-\nu(y)|$。下确界遍历全部状态无关 Markov 核，包括会在某些输入上改变 $q$ 的核。有限输出时核集合紧、目标连续，故下确界达到。箭头始终从可用实验指向希望恢复的实验。固定一个 $q$ 时用同一记号表示状态集为 $A_q$ 的局部问题。

下文的逆向上界另有承担结论的精确序假设：$W_v\preceq W_w$，即存在对全部实际行同时成立的精确前向核。按定理 538.3，等价地，对每个 $q$ 给定一组非负子集流

$$
\sum_{C\supseteq B}f_{BC}^q=w_B^q,
\qquad
\sum_{\substack{\varnothing\ne B\subseteq C\\k\in B}}f_{BC}^q=v_C^q
\quad(k\in C),
\qquad f_{BC}^q=0\quad\text{若 }B\nsubseteq C.
\tag{539.3}
$$

所有块非空。它在 $w_B^q>0$ 时给出前向核 $f_{BC}^q/w_B^q$；零权重源块任意补成概率行。这个假设不由“分别存在每一对的模拟器”替代，也不由近似前向拟合替代。记成对损失

$$
\Delta_{kl}^q=r_{kl}^q(v)-r_{kl}^q(w),\qquad
r_{kl}^q(w)=\sum_{C\supseteq\{k,l\}}w_C^q,
\quad k\ne l.
\tag{539.4}
$$

在（539.3）下这些差非负。它衡量成对碰撞增加量；对应等先验二态识别风险的增加量为 $\Delta_{kl}^q/2$。本章的常数均以（539.2）的半 $L^1$ 约定为准。

### 定理 539.2（精确前向子集流的反向核与逐态误差）

在定义 539.1 的精确序假设下，对 $v_C^q>0$ 定义

$$
R^q(B\mid C)=
\begin{cases}
\displaystyle\frac{|B|f_{BC}^q}{|C|v_C^q},&\varnothing\ne B\subseteq C,\\
0,&B\nsubseteq C.
\end{cases}
\tag{539.5}
$$

对 $v_C^q=0$ 的输出任选一个同读数的概率行。按 $q$ 拼接所得 $R$ 是合法的状态无关反向核。对每个实际行 $(k,q)$，它的规范实验误差恰为

$$
e_k^q
:=\operatorname{TV}(W_v^q(\cdot\mid k)R^q,W_w^q(\cdot\mid k))
=\sum_{\substack{B\ni k\\C\supseteq B}}
 f_{BC}^q\frac{|C|-|B|}{|C|}.
\tag{539.6}
$$

令 $b_q=\tfrac12\max_{k\in A_q}\sum_{l\in A_q\setminus\{k\}}\Delta_{kl}^q$。则

$$
\begin{aligned}
d(W_v\longrightarrow W_w)
&\le\max_{q,k}e_k^q
\le\min\{1,\max_q b_q\},\\
b_q&\le\frac{n_q-1}{2}\max_{k\ne l\in A_q}\Delta_{kl}^q.
\end{aligned}
\tag{539.7}
$$

当 $n_q=1$ 时，空的成对最大值及空和均约定为零，相应误差为零。（539.6）是给定流与给定逆核的精确误差；（539.7）通常只是最优反向缺损的上界。

证明：固定 $q$ 并省略上标。把（539.3）的第二个等式对 $k\in C$ 求和，得到

$$
|C|v_C=\sum_{\varnothing\ne B\subseteq C}|B|f_{BC}.
\tag{539.8}
$$

所以正分母时（539.5）非负且总和为一。若 $v_C=0$，右侧各项非负而 $|B|>0$，故全部 $f_{BC}=0$；该 $C$ 在每条 $W_v$ 行中质量也为零，所选补全不影响任何恢复行。若 $w_B=0$，则由源流行和可知全部 $f_{BC}=0$。因此下面的有限和可以包括零权重块，无需给 $0/0$ 赋值。

令 $Q_k=W_v(\cdot\mid k)R$。对任一包含 $k$ 的 $B$，只有 $C\supseteq B$ 的项能够贡献，且它们都包含 $k$，从而

$$
Q_k(B)=\sum_{C\supseteq B}\frac{|B|}{|C|}f_{BC}
\le\sum_{C\supseteq B}f_{BC}=w_B.
\tag{539.9}
$$

对不含 $k$ 的 $B$，原始行质量为零，$Q_k(B)\ge0$。因此原始质量所有亏损恰在含 $k$ 的块上，所有盈余恰在不含 $k$ 的块上；两条概率行的总质量相等，半 $L^1$ 等于亏损总和。将（539.9）从源流行和中相减，再对 $B\ni k$ 求和，就得到（539.6）。这一步同时证明 $0\le e_k\le1$，并不把逆核误差假定成其最优值。

式（538.15）对固定 $k$ 的其他状态求和，有

$$
\begin{aligned}
\sum_{l\ne k}\Delta_{kl}
&=\sum_{\substack{B\ni k\\C\supseteq B}}
 f_{BC}|C\setminus B|\\
&=\sum_{\substack{B\ni k\\C\supseteq B}}
 f_{BC}(|C|-|B|).
\end{aligned}
\tag{539.10}
$$

这里每个流项恰被 $l\in C\setminus B$ 计一次。也可直接把目标成对质量按状态 $k$ 的流展开，减去源成对质量，留下 $k\in B,l\notin B,l\in C$ 的项，再交换有限求和。故各项非负，且这确实是同一个共同流的各行关系。

对角项 $B=C$ 在（539.6）、（539.10）中都为零。严格包含的项有 $|C|\ge2$，故 $1/|C|\le1/2$，逐项比较即得 $e_k\le\tfrac12\sum_{l\ne k}\Delta_{kl}$。取最大值并以一截断，得到第一行上界；一行至多有 $n_q-1$ 项，得到第二行。单态时仅有唯一非空块，权重为一，所有流都在对角上，结论照常成立。证毕。

逐态不等式 $e_k\le\tfrac12\sum_{l\ne k}\Delta_{kl}$ 的等号条件也由该证明给出：对所有 $k\in B\subsetneq C$ 且 $f_{BC}>0$ 的项，须有 $|C|=2$；这些项自动满足 $|B|=1$。若没有这样的严格流，两边都为零。逐态等号不保证随后取最大值、取缺损下确界的每一步也取等；命题 539.4 的星形例子将区分它们。

核（539.5）本身是经典贝叶斯反演。取 $A_q$ 上均匀状态先验，源块边缘概率为 $|B|w_B/n_q$，经前向核后的块概率为 $|C|v_C/n_q$，联合块质量为 $|B|f_{BC}/n_q$；贝叶斯公式正给（539.5）。此处的均匀先验只用于构造核，结论（539.6）逐态成立，不假定真实先验均匀。Cho–Jacobs, *Disintegration and Bayesian Inversion via String Diagrams*, Example 3.8 明确给出离散贝叶斯反演及零输出处任意补全；见 [arXiv:1709.00322v3](https://arxiv.org/html/1709.00322v3)，*Mathematical Structures in Computer Science* 29(7)（2019），938–971，[DOI:10.1017/S0960129518000488](https://doi.org/10.1017/S0960129518000488)。这里承担新增关系的是子集流所产生的单边行亏损、（539.10）的共同成对损失以及下文公开实现中的锐度和间隙，不把贝叶斯公式另作新定理。

### 推论 539.3（恢复整个公开种子与有界损失的转移）

设 $E_w,E_v$ 为定义 539.1 中具有剖面 $w,v$ 的原始公开实验，种子和标签空间允许为标准 Borel 空间。若（539.3）成立，则存在一个可读取 $q$ 的状态无关核 $\widetilde R$，输出 $E_w$ 的整个原始种子和标签，满足

$$
\forall(k,q)\in S,\qquad
\operatorname{TV}((E_v)_{k,q}\widetilde R,(E_w)_{k,q})\le e_k^q.
\tag{539.11}
$$

对任意 $S$ 上概率先验 $\pi$、任意非空有限行动集 $D$ 和任意损失 $\lambda:S\times D\to[0,1]$，以 $\mathcal R_E(\pi,\lambda)$ 表示最小 Bayes 风险，有

$$
0\le\mathcal R_{E_v}(\pi,\lambda)-\mathcal R_{E_w}(\pi,\lambda)
\le\sum_{(k,q)\in S}\pi_{k,q}e_k^q
\le\max_{q,k}e_k^q
\le\min\{1,\max_q b_q\}.
\tag{539.12}
$$

这不要求原先验给每条实际行正质量；（539.11）仍约束先验质量为零的实际行。

证明：记定理 538.2 的规范化核为 $C_v:E_v\to W_v$，重建核为 $J_w:W_w\to E_w$，取 $\widetilde R=C_vRJ_w$。为明确整个种子的重建，对输入 $(q,B)$ 且 $w_B^q>0$，令

$$
H_B^q=\{r\notin N_w:B\in P_r^w|_{A_q}\},\qquad
\rho_{w,B}^q(dr)=\frac{\mathbf1_{H_B^q}(r)}{w_B^q}\rho_w(dr).
$$

$N_w$ 是对全部有限实际行统一选取的零集。$J_w$ 按此限制律抽取整个 $r$，并输出 $(q,r,f_w(r,k_B))$，$k_B$ 是 $B$ 的固定代表。在 $H_B^q$ 上所有 $k\in B$ 的标签相同，故没有读取未知状态。$w_B^q=0$ 时选定一个固定原始输出作为补全；这些核行处处定义、可测。定理 538.2 给 $(E_v)_{k,q}C_v=(W_v)_{k,q}$ 和 $(W_w)_{k,q}J_w=(E_w)_{k,q}$。TV 在同一 Markov 后处理下收缩，结合（539.6）得到（539.11）。其右端是规范行误差，因此得到（539.11）的上界。前向核同样通过 $C_wHJ_v$ 作用到原始实验，仍是精确模拟。

对任意 $E_w$ 的决策核 $D_w$，把 $\widetilde R D_w$ 用于 $E_v$。固定状态 $s$，原输出 $y$ 上的条件期望损失 $g_s(y)=\sum_aD_w(a\mid y)\lambda(s,a)$ 位于 $[0,1]$。概率律间对任何这样的函数都满足 $|\int g_s\,d\mu-\int g_s\,d\nu|\le\operatorname{TV}(\mu,\nu)$；例如写成 $g_s(y)=\int_0^1\mathbf1_{\{g_s(y)>u\}}du$ 即得。由（539.11），搬运后逐态风险至多增加 $e_s$。乘以 $\pi_s$ 求和，再对决策取下确界，得到（539.12）的右侧。精确前向核使 $E_w$ 可以执行任意 $E_v$ 决策，故 $\mathcal R_{E_w}\le\mathcal R_{E_v}$，得到左侧。即使不预先使用最优规则的存在性，对任意接近下确界的规则应用同一论证并取极限也成立。证毕。

这一步复用既有有界损失—缺损转移关系。仓内 [FiniteDeficiencyRiskTransfer](../../../D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.lean) 的接口把目标参数放在源参数之前：`finiteDeficiency target source` 对应本章 $d(\mathrm{source}\to\mathrm{target})$，其 `deficiency_risk_bound` 给源风险不超过目标风险加该缺损。这里为整种子核给出独立的纸面概率论推导；接口对应本身不构成对本章陈述的内核认证。

### 命题 539.4（同一逆核在擦除与星形公开实验中的精确性边界）

在一个共同读数、$n\ge2$ 个情境、原目标恒定的模型中，以完全揭示情境的实验 $I$ 为源，比较下列两种公开实验。第一种以概率 $a\in[0,1]$ 使用全合并分划，以概率 $1-a$ 使用离散分划，记为 $W^{\mathrm{era}}$。第二种在状态 $\{0,1,\ldots,n-1\}$ 上，以概率 $\varepsilon$ 使用仅合并 $\{0,i\}$ 的分划，各 $i=1,\ldots,n-1$ 各占一项，其余概率使用离散分划，其中 $0\le\varepsilon\le1/(n-1)$，记为 $W^{\mathrm{star}}$。则

$$
\begin{aligned}
d(W^{\mathrm{era}}\longrightarrow I)&=a(1-1/n),\\
d(W^{\mathrm{star}}\longrightarrow I)&=\frac{n-1}{n}\varepsilon.
\end{aligned}
\tag{539.13}
$$

对这两个实验，源单点到目标块的前向流均为 $f_{\{k\},C}=w_C$（$k\in C$），故（539.5）是在观察块内均匀选状态。它在擦除实验中达到最优；在星形实验中逐态最大误差为 $(n-1)\varepsilon/2$，当 $n>2,\varepsilon>0$ 时严格大于最优值。两者都具有同一公开实现合同，不以非公开 CAR 通道制造间隙。

证明中的共同工具是经典加权 Hall 条件的最大流推论。以下完整写出它到识别损失的对应，作为本命题及后续锐度、平台例子的计算步骤，不将其申报为新的 CAR 一般定理。暂时只固定一个非空有限状态集 $V$，$|V|=n$，并假定

$$
w_C\ge0,\qquad \sum_{C\ni k}w_C=1\quad(k\in V),
\qquad W_w(C\mid k)=\mathbf1_{\{k\in C\}}w_C.
$$

这些 CAR 行方程比公开可实现性弱；此处暂不要求分划混合。对 $\varnothing\ne U\subseteq V$ 定义

$$
h(U)=\sum_{C:C\cap U\ne\varnothing}w_C,\qquad
\beta=\min_{\varnothing\ne U\subseteq V}\frac{h(U)}{|U|}.
\tag{539.14}
$$

非空子集只有有限多个，故最小值达到。单点 $U=\{k\}$ 的比值为一，非负性保证 $0\le\beta\le1$。实际还有 $h(U)\ge1$，从而 $\beta\ge1/n$。直接推导得到

$$
\boxed{
D(w):=d(W_w\longrightarrow I)
=1-\beta
=\max_{\varnothing\ne U\subseteq V}
 \frac1{|U|}\sum_Cw_C(|C\cap U|-1)_+ .}
\tag{539.15}
$$

这里 $(x)_+=\max(x,0)$。该最优值有达到的解码核，且任何取到（539.14）最小值的 $U$ 上的均匀先验都是最不利先验。

先构造达到的核。取有限有向网络，节点依次为源 $s$、每个非空块 $C$、每个状态 $k$、汇 $z$。边 $s\to C$ 容量为 $w_C$，当 $k\in C$ 时有边 $C\to k$，容量取有限数 $M=n+1$，边 $k\to z$ 容量为 $\beta$。最大可能流量不超过 $n\beta\le n<M$。

考察任意割的源侧。令 $U$ 为汇侧的状态集合。若割切断一条 $C\to k$ 边，其容量至少为 $M>n\beta$；这类割不可能阻碍流量达到 $n\beta$。若没有这种边被切断，则每个与 $U$ 相交的块节点都必须在汇侧。固定 $U$ 后，为使割容量最小，把恰好这些块放在汇侧，所有不与 $U$ 相交的块放在源侧。所得割容量恰为

$$
h(U)+\beta(n-|U|)\ge n\beta.
\tag{539.16}
$$

在这里令 $h(\varnothing)=0$，$U=\varnothing$ 给等号割；对非空 $U$，不等式就是 $\beta$ 的定义。额外把不与 $U$ 相交的块放到汇侧只会增加非负容量，故已覆盖全部无大容量边的割。

有限实容量有向网络的最大流最小割原理于是给出流量 $n\beta$。为明确所用版本，不需要假定实数容量上的某个增广算法有限终止：可行流是非空紧多面体，总流量连续，故有最大流；若其正残余容量图中有源汇路径，沿路径增广一个正量便与最大性矛盾。否则取残余可达源侧，跨向汇侧的原边均饱和，反向跨边均为零，由守恒得最大流量等于该割容量。这就证明了此处有向版本的原理。其经典来源是 Ford–Fulkerson, *Maximal Flow Through a Network*, Theorem 1（Minimal cut theorem），*Canadian Journal of Mathematics* 8（1956），399–404，[DOI:10.4153/CJM-1956-045-5](https://doi.org/10.4153/CJM-1956-045-5)；原文的一般网络最小割原理并非逐字陈述（539.15），本处有向网络及其识别解释由上述构造给出。

记达到流中 $C\to k$ 的流量为 $a_{Ck}$。全部 $k\to z$ 都饱和，故

$$
\sum_{C\ni k}a_{Ck}=\beta,
\qquad
\sum_{k\in C}a_{Ck}\le w_C.
$$

对每个非空块 $C$，把剩余量 $w_C-\sum_{k\in C}a_{Ck}$ 任意分配到 $C$ 内，例如全部给一个固定成员，得到 $b_{Ck}\ge a_{Ck}$、$\sum_{k\in C}b_{Ck}=w_C$。若 $w_C>0$，令解码概率为 $D(k\mid C)=b_{Ck}/w_C$（$k\in C$），块外概率为零；若 $w_C=0$，任取 $C$ 内一个成员作为确定输出。这给处处定义的概率核。状态 $k$ 的正确率是 $\sum_{C\ni k}w_CD(k\mid C)=\sum_{C\ni k}b_{Ck}\ge\beta$，因此最大错误不超过 $1-\beta$。恒等实验第 $k$ 行为 $\delta_k$，任何解码后行 $P_k$ 满足 $\operatorname{TV}(P_k,\delta_k)=1-P_k(k)$，所以这也是缺损上界。

反向证书不限制解码器是否在块内输出。对任意解码核和任意非空 $U$，其正确率 $s_k$ 满足

$$
\sum_{k\in U}s_k
=\sum_Cw_C\sum_{k\in C\cap U}D(k\mid C)
\le\sum_{C:C\cap U\ne\varnothing}w_C=h(U).
\tag{539.17}
$$

故某个 $k\in U$ 的正确率不超过 $h(U)/|U|$，特别地最大错误至少为 $1-\beta$。与构造的上界合成，证明第一等式及达到性。再把 CAR 行和对 $k\in U$ 求和，得 $|U|=\sum_Cw_C|C\cap U|$。减去 $h(U)$ 后，逐块留下 $w_C(|C\cap U|-1)_+$，即得（539.15）的第二种形式和 $0\le D(w)\le1$。单态时唯一块权重为一，$\beta=1,D=0$，无额外例外。

最不利先验也由同一个割给出。令先验均匀于一个最小化的 $U$、在其外为零。每个与 $U$ 相交的块，其最优正确概率质量为 $w_C/|U|$：选取任一 $k\in C\cap U$ 即达到；不相交的块在此先验下不可达。总 Bayes 成功率恰为 $h(U)/|U|=\beta$，风险为 $1-\beta$。已构造的核对每个状态错误都不超过此数，故任何先验的最小 Bayes 风险都不超过它。这同时证明最不利性与下界，未假定均匀于整个 $V$ 总是最不利。

若有多个可见读数，令恒等实验输出完整实际行 $(q,k)$，同理得到

$$
d(W_w\longrightarrow I_S)=\max_{q\in Q}D(w^q).
\tag{539.18}
$$

上界由局部最优核按 $q$ 拼接达到。下界取某个 $q$ 和其最小化子集 $U$，在这些实际行上放均匀先验。即使候选核允许输出其他读数，针对正确输出 $(q,k)$ 的概率和仍满足（539.17）；发往其他读数的质量不能增加正确率。故该下界针对全部允许核，而非只针对预设保持 $q$ 的核。

回到本命题。擦除实验的块权重为 $w_V=a$、$w_{\{k\}}=1-a$。每个非空 $U$ 给出（539.15）的值 $a(|U|-1)/|U|$，它随 $|U|$ 非减，满集达到 $a(1-1/n)$。直接在全块均匀猜测、单点如实输出，使每个状态错误也等于此数，故（539.5）最优。这里统一成对碰撞为 $a$；粗化成对上界 $(n-1)a/2$ 在 $n>2,a>0$ 时大于实际误差，说明核本身最优与粗化上界取等是不同问题。

星形实验的显式分划分布给出

$$
w_{\{0,i\}}=\varepsilon\ (1\le i\le n-1),\qquad
w_{\{0\}}=1-(n-1)\varepsilon,\qquad
w_{\{i\}}=1-\varepsilon,
\tag{539.19}
$$

其他块权重为零。中心在 $n-1$ 个二点块中的均匀猜测错误为 $(n-1)\varepsilon/2$，各叶错误为 $\varepsilon/2$。改用如下解码：每个二点块以概率 $(n-1)/n$ 报中心，以概率 $1/n$ 报该叶，单点仍如实输出。中心错误为 $(n-1)\varepsilon/n$，每片叶的错误也是 $\varepsilon(n-1)/n$，得到同一上界。取满集 $U=V$，式（539.15）中的分子恰为全部二点块权重之和 $(n-1)\varepsilon$，给出相同下界。若另取含中心和 $m$ 片叶的子集，该比值为 $m\varepsilon/(m+1)$；不含中心时为零，故满集确实达到最大值。于是（539.13）成立，且 $n>2,\varepsilon>0$ 时间隙严格；$n=2$ 或 $\varepsilon=0$ 时两者相合。证毕。

（539.15）的 CAR 计算并不授予公开实现。具体地，定理 538.2 已引用 Gill–Grünwald 的三角例子 $w_{12}=w_{13}=w_{23}=1/2$、其余零；其行和均为一，（539.15）给 $D=1/2$，但三点无法分成二点块，故不是分划混合。出处为 Gill–Grünwald, *An Algorithmic and a Geometric Characterization of Coarsening At Random*, §2 Example 1，[arXiv:math/0510276v3](https://arxiv.org/html/math/0510276v3)，*Annals of Statistics* 36(5)（2008），2409–2422，[DOI:10.1214/07-AOS532](https://doi.org/10.1214/07-AOS532)。这沿用已有反例，不把它算作本章的新构造。

更一般地，一个读数且正权重块大小至多为二时，公开分划中的二点块必须构成匹配，其余状态为单点。因此公开实现恰要求边权来自匹配的概率混合，单点权重为一减去关联边权之和。必要性来自每次分划的块不相交；充分性是按该匹配分布选种子并附上未匹配单点。仅有每个顶点的关联边权不超过一并不足够，三角例子已证明这一点。多个读数还须进一步满足同一个 $w=Mp$，逐个读数分别可实现不够；这正是第 538 章的共同律限制。上述星形、擦除及下文匹配例子都直接给出分划分布，故没有把行方程误作公开实现的证书。

### 命题 539.5（公开匹配族达到常数与维数尺度）

在一个共同读数、原目标恒定的 $n$ 状态模型中，以 $I$ 为源、公开匹配混合 $W_v$ 为目标，存在以下显式精确前向有序族。对 $\theta\in[0,1]$，若 $n\ge2$ 为偶数，以概率 $\theta$ 均匀选择一个完美匹配分划，以其余概率选择离散分划；若 $n\ge3$ 为奇数，以概率 $\theta$ 均匀选择一个只有一个未匹配单点的近完美匹配分划，以其余概率选择离散分划。整个被选分划就是公开种子，发送其中包含状态的块。其全部成对损失及精确反向缺损为

$$
\begin{array}{c|cc}
 &\Delta_{kl}\ (k\ne l)&d(W_v\longrightarrow I)\\ \hline
n\text{ 为偶数}&\theta/(n-1)&\theta/2\\
n\text{ 为奇数}&\theta/n&\theta(n-1)/(2n).
\end{array}
\tag{539.20}
$$

两族同时达到（539.7）的行和界及最大成对差界。因此行和前的 $1/2$ 不能减小；对固定 $n\ge2$，乘在最大成对损失前的 $(n-1)/2$ 也不能统一减小。即使精确前向序和公开实现都成立，也不存在与状态数无关、当 $\delta\downarrow0$ 时趋于零的函数 $\omega(\delta)$，使所有这些实验满足 $d(W_v\to I)\le\omega(\max_{k\ne l}\Delta_{kl})$。

证明：完全揭示实验可通过按上述独立分布选择分划并输出块来模拟目标；流明确为 $f_{\{k\},C}=v_C$（$k\in C$），满足（539.3）。从单点状态构造这一核不要求两个种子按细化耦合；两边的公开编码也都分别合法。

偶数情形，固定状态的匹配伙伴在其他 $n-1$ 个状态中对称且必有一个，故每对边权为 $\theta/(n-1)$，每个单点权重为 $1-\theta$。块内均匀解码在每个状态的错误为 $\theta/2$。所有二点块的总权重为 $\binom n2\theta/(n-1)=n\theta/2$，故（539.15）的满集证书为 $\theta/2$；上、下界相合。源 $I$ 的成对碰撞为零，故目标边权就是 $\Delta_{kl}$，一行和为 $\theta$。

奇数情形，每个近完美匹配含 $(n-1)/2$ 条边，状态置换对全部边传递。于是指定边出现的概率为 $((n-1)/2)/\binom n2=1/n$，指定状态成为未匹配单点的概率为 $1/n$。混合后的边权为 $\theta/n$、单点权重为 $1-\theta+\theta/n$。均匀解码的逐态错误为 $\theta(n-1)/(2n)$。全部二点块的总权重为 $\theta(n-1)/2$，满集证书除以 $n$ 给相同值。一行成对和为 $\theta(n-1)/n$，故两条界也都取等。

取任意 $\theta>0$ 就验证了常数与尺度的锐度。再固定 $\theta=1$，令偶数 $n$ 趋于无穷，则最大成对损失 $1/(n-1)$ 趋零，而反向缺损恒为 $1/2$；这与任何上述无维数模量矛盾。奇数族也给最大成对损失 $1/n\to0$、缺损趋于 $1/2$。$\theta=0$ 时都是完全揭示，全部误差为零；$n=1$ 的单态情形已由定理 539.2 处理。证毕。

### 命题 539.6（相同二态类与相同最坏识别仍留下不可比信息）

在第 538 章的共同三状态公开纤维中，令 $R=r_{12}+r_{13}+r_{23}$，

$$
t\in\left[\max\{0,(R-1)/2\},\ \min\{r_{12},r_{13},r_{23}\}\right],
\quad
w_{123}=t,\quad w_{ij}=r_{ij}-t,\quad
w_i=1-r_{ij}-r_{ik}+t.
\tag{539.21}
$$

这族的最坏识别损失恰为

$$
D(w(t))=
\max\left\{\frac{r_{12}}2,\frac{r_{13}}2,\frac{r_{23}}2,
                   \frac{R-t}{3}\right\}.
\tag{539.22}
$$

特别地，固定 $(r_{12},r_{13},r_{23})=(3/5,1/5,1/5)$，在整段 $t\in[1/10,1/5]$ 上有 $D(w(t))=3/10$。段中不同剖面却仍两向不可比；均匀先验的识别与排除任务继续给出相反的严格风险变化。因此成对类加上这个精确的最坏识别值，也不能确定完整实验的 Blackwell 类。

证明：在（539.15）中，单点 $U$ 的分子为零；二点 $U=\{i,j\}$ 只由同时包含两点的块贡献，分子为 $r_{ij}$；满集的分子为三个二点块权重之和加二倍三点块权重，即 $(R-3t)+2t=R-t$。穷尽七个非空子集就得到（539.22）。当成对项严格大于满集项时，最不利先验集中在相应的一对状态上，不能用全状态均匀先验代替。

指定的 $r$ 满足 $R=1$，完整公开可行区间是 $[0,1/5]$；这是定理 538.7 的五分划表示。更明确地，其分布为

$$
\begin{aligned}
p_{123}&=t,&p_{12|3}&=3/5-t,\\
p_{13|2}&=1/5-t,&p_{23|1}&=1/5-t,\\
p_{1|2|3}&=2t.
\end{aligned}
\tag{539.23}
$$

各项在此区间非负且总和为一，所以每个点都由同一读数下一个实际公开种子律实现。在子段 $[1/10,1/5]$ 上，$(1-t)/3\le3/10$，而最大的二点项恒为 $r_{12}/2=3/10$，故得到平台。其最不利先验可统一取 $(1/2,1/2,0)$；这并不阻止另一个固定先验区分各点。

例如端点 $t_-=1/10,t_+=1/5$ 的分划概率按（全合并、$12|3$、$13|2$、$23|1$、离散）依次为

$$
(1/10,1/2,1/10,1/10,1/5),\qquad
(1/5,2/5,0,0,2/5).
\tag{539.24}
$$

三态均匀先验下，识别损失为 $\mathbf1_{\{k\ne a\}}$，排除损失为 $\mathbf1_{\{k=a\}}$，两者的行动均为三个状态标签。正概率块上的后验在块内均匀；逐块最优化给识别风险 $(1-t)/3$、排除风险 $t/3$，与（538.27）相同。因此

$$
\begin{array}{c|ccc}
 &D&\mathcal R_{\mathrm{id}}&\mathcal R_{\mathrm{ex}}\\ \hline
t_-&3/10&3/10&1/30\\
t_+&3/10&4/15&1/15.
\end{array}
\tag{539.25}
$$

两个任务的风险差分别为 $-1/30$ 与 $1/30$。若一个实验精确模拟另一个，全部同先验同损失的最优风险必须沿同一方向不降；此处两个任务给相反方向，故两向模拟都不成立。对于任意 $t_1<t_2$，相同计算给差值的绝对量 $(t_2-t_1)/3>0$，并由有界损失转移直接给出两个方向的缺损下界

$$
d(W_{t_1}\longrightarrow W_{t_2})\ge(t_2-t_1)/3,
\qquad
d(W_{t_2}\longrightarrow W_{t_1})\ge(t_2-t_1)/3.
\tag{539.26}
$$

这里下界针对任意状态无关核，没有使用精确前向序；相反，它证明两方向都没有该序。定理 538.4 的同成对纤维反链判据给出同一不可比结论。证毕。

这也明确了定理 539.2 的顺序假设不可删除。沿用定理 538.7 已有的 $r=(1/3,1/3,1/3)$ 及 $t=0,1/3$ 两端点：前者均匀混合三个 $ij|k$ 分划，后者以概率 $1/3$ 全合并、$2/3$ 全分开。它们成对值逐项相等，均匀先验识别风险分别为 $1/3,2/9$，排除风险分别为 $0,1/9$。因此从任一端点模拟另一个的缺损都至少为 $1/9$。这是对已有反例的定量使用；并非另一个新反例。若省略精确前向序，用 $\max_{kl}|r_{kl}(v)-r_{kl}(w)|$ 趋零来保证整体恢复，则连固定三状态、成对差严格为零的情形也失败。平台例子进一步表明，即使再把一个最优识别成绩补入摘要，问题仍未解决。

### 命题 539.7（非恒定原目的下的嵌入不稀释最坏误差）

对命题 539.4–539.6 的任一个共同读数核心 $V$，添加新情境 $d$，实际对象取全部 $V\cup\{d\}$，情境为自身，读数保持同一个 $q_0$。原目标规定为 $T(k)=0$（$k\in V$）、$T(d)=1$。把每个核心分划 $P$ 变成 $P\cup\{\{d\}\}$，使用原分划分布作为独立公开种子。这样得到的实验在每条实际行精确恢复非恒定的原目标，且任意两核心实验 $E,F$ 的提升 $\widehat E,\widehat F$ 满足

$$
d(\widehat E\longrightarrow\widehat F)=d(E\longrightarrow F).
\tag{539.27}
$$

尤其提升实验到完整恒等实验的最坏识别缺损，恰等于核心的 $D$，而不是乘以核心先验质量。不同于这一逐态量，对核心概率先验 $\pi$、总质量 $\alpha\in(0,1)$ 的提升先验 $(\alpha\pi,1-\alpha)$，适当延伸的核心任务之最优 Bayes 风险恰乘以 $\alpha$。

证明：原目标的冲突图在 $d$ 与每个核心状态之间有边，核心内部无边。每个使用的分划均把 $d$ 单列，所以充分且由一个全局分划律实现；发送块的编码依旧只读情境和整个种子。输出 $\{d\}$ 时报告一，核心块时报告零，逐态正确。新增成对碰撞全为零，核心成对剖面保持原值。

先在规范块实验上证明（539.27）。任何核心模拟核都可扩展为在输入 $\{d\}$ 上确定输出 $\{d\}$，在核心输入上照原核执行，其余不可达输入任意补成概率行；新增状态误差零，故提升缺损不大于核心缺损。反过来，给定任何提升模拟核，只取其核心输入，并把所有不属于核心输出字母表的目标输出统一替换成一个固定核心输出，包括 $\{d\}$ 及含 $d$ 的混合块，得到合法的核心核。此投影保持每条核心目标行不变，TV 收缩使核心误差不大于原提升核在相应核心行上的误差。故核心缺损不大于提升缺损，两向合成即得等式。原始整种子实验与规范实验有精确双向核；把任意近似核前后与这些精确核复合，由 TV 收缩可在两种表示之间互证同一缺损，因而等式也适用于原始实验。

风险缩放则是另一种量词。固定核心行动集 $D$ 和 $[0,1]$ 值损失，在提升中保留这些行动，令它们在状态 $d$ 上损失为零；若增加新行动 $d$，则规定它在核心所有状态上的损失为一，在 $d$ 上为零。这样新行动不能改善核心最优值，而输出能精确区分核心与新增状态，后者风险零，故最优风险为 $\alpha\mathcal R_E(\pi,\lambda)$。识别可取全部 $V\cup\{d\}$ 标签；排除则保持行动为 $V$，在核心仍用 $\mathbf1_{\{k=a\}}$，在 $d$ 上损失零。于是平台两端及无序两端的相反风险差都只在先验平均意义下乘以 $\alpha$。如果把排除行动无条件放宽到所有新旧标签并仍用同名相等损失，则可在核心报告 $d$、在 $d$ 报告一个核心标签而处处零错，那已是另一个任务。证毕。

### 定义 539.8（目的相关的近似替代与信息逃逸的范围）

在本章的实际支撑与公开观察合同中，称充分概念编码 $E$ 能以误差至多 $\eta\ge0$ 单向替代 $F$，是指 $d(E\to F)\le\eta$。它保证对任意概率先验 $\pi$、有限非空行动集与 $[0,1]$ 损失 $\lambda$，有 $\mathcal R_E(\pi,\lambda)\le\mathcal R_F(\pi,\lambda)+\eta$；只完成原目的 $T$、只保存各二态类、只保存一个最坏识别值，是三个较少的要求。本章明确区分了它们：精确前向共同流把成对损失接到整体反向上界；有序匹配族表明该控制的尺度随活动状态数增长；星形表明一个显式反向核的误差不等于最优缺损；三态平台则在全部二态类和最坏识别值都固定时，仍留下由其他任务分辨的不可比实验。

这里的块剖面 $w$ 指实际输出概率，既需要 CAR 行方程，也需要公开模型的共同 $w=Mp$ 实现条件。以 $w$ 为固定数据的识别计算允许分配解码概率；这与[《数学与神话匹配》§554](MATH_MYTH_MATCH.md) 中特定二态通道的精确逆误差、§§705–708 的容量优化以及 §§727–729 的分数覆盖优化具有不同变量和约束。有限对偶、加权 Hall/最大流、贝叶斯反演和有界损失转移都是既有方法。本章的仓内新增综合在于把这些方法接到第 538 章的共同公开实现和子集流接口，并用达到常数的族、逆核严格间隙及固定最坏识别值的平台说明各层关系；不把上述经典一般结果、CAR/CCAR 区分或原有同成对反例申报为原创。所列来源与具体对应不构成全球优先性证明。

与维特根斯坦的对应限于《哲学研究》§§65–69。§§65–67 要求考察实际使用中的多种交错相似，而不先要求同一名称贯穿着一个单一本质；§§68–69 允许为了一个特定目的划定边界，也明确这种划界并非通常语言原先能够使用的前提。原文见 [Wittgenstein, *Philosophische Untersuchungen*, §§65–69](https://www.wittgensteinproject.org/w/index.php/Philosophische_Untersuchungen#65)。本章选择 $S,T$、公开材料、模拟权限和误差尺度，属于这样一个特定目的下的数学规定；统计实验、概率分划和缺损不是维特根斯坦的理论。原目的已经逐态恢复，新增任务仍能分辨两个编码，说明“对这个目的够用”与“对其他共同使用可以替代”是不同问题，不把这一区别外推成普遍相对主义。

本章的信息逃逸只相对于所列摘要：完整可实现 $w$ 已分类本允许族，而不同潜在分划律 $p,p'$ 若给相同 $w$，其差别不是可观察逃逸。这里没有给经验性性别结论提供前提，也不从可见性推出披露政策或道德义务；有限例子不证明逃逸必然无限持续。数学范围仍有明确空缺：一般有序 $w,v$ 的最优反向缺损没有被（539.6）求出，仅有给定核的误差及上界；（539.15）只精确解决到恒等实验的识别目标；近似而非精确前向序需要另行控制流的违约量，本章不提供该推广；无序比较也不能只靠成对差。这些均为所列假设下的纸面证明与边界，不是 Lean 内核认证或消化覆盖结论。

## 追加锚（本行以下为增补区）

## 540. 近似前向模拟的恢复率与成对摘要的信息逃逸

### 定义 540.1（近似前向、成对剖面与联合表数据）

固定有限非空状态集 $A$，$n=|A|$，以及两个同一子集字母表上的 CAR 剖面 $w,v$。写

$$
W_i(B)=\mathbf 1_{\{i\in B\}}w_B,
\qquad
V_i(C)=\mathbf 1_{\{i\in C\}}v_C,
\qquad \varnothing\ne B,C\subseteq A .
\tag{540.1}
$$

这里 $W_i,V_i$ 是状态 $i$ 的半 $L^1$ 概率行。给定一个对所有状态共用的状态无关随机核 $H(C\mid B)$，定义

$$
f_{BC}=w_BH(C\mid B),\qquad
F_i(B,C)=\mathbf 1_{\{i\in B\}}f_{BC},\qquad
Q_i(C)=\sum_BF_i(B,C),
\tag{540.2}
$$

并令

$$
\varepsilon_i=\operatorname{TV}(Q_i,V_i),
\qquad
\eta=\max_{i\ne j}\left|\Delta_{ij}\right|,
\qquad
\Delta_{ij}=r_{ij}(v)-r_{ij}(w),
\tag{540.3}
$$

其中 $r_{ij}(w)=\sum_{B\supseteq\{i,j\}}w_B$，$r_{ij}(v)$ 同理，且 $\varepsilon=\max_i\varepsilon_i$。本节约定空成对最大值为零，因此 $n=1$ 时 $\eta=0$；空和也取零。在近似情形 $\Delta_{ij}$ 可以为负；它不是单独的损失预算。假设只有这一份 $H$，而不是为每个 $i$ 另选一个核。有限字母表上的核集合是紧的，故前向缺损的下确界达到；若 $H$ 取到 $d(w\mathbin{\to}v)$，则 $\varepsilon=\max_i\varepsilon_i$ 可以正是该最优前向缺损（也可以只把它当作给定核的统一误差）。

### 定理 540.2（近似联合表与显式反向恢复率）

在定义 540.1 的条件下，存在一个状态无关核 $R(B\mid C)$，使每个状态 $i$ 满足

$$
\operatorname{TV}(V_iR,W_i)\le
b_i:=\frac12\sum_{j\ne i}
\bigl(\Delta_{ij}+\varepsilon_i+\varepsilon_j\bigr).
\tag{540.4}
$$

每一项 $\Delta_{ij}+\varepsilon_i+\varepsilon_j$ 都是非负数。因而

$$
 d(v\mathbin{\to}w)
 \le \min\left\{1,\max_i b_i\right\}
 \le \min\left\{1,\frac{(n-1)\eta}{2}+(n-1)\varepsilon\right\}.
\tag{540.5}
$$

当 $n=1$ 时空和为零，恢复误差为零。

证明：先对每个 $i$ 和 $C$ 定义

$$
 a_i(C)=
 \begin{cases}
 \min\{1,V_i(C)/Q_i(C)\},&Q_i(C)>0,\\
 1,&Q_i(C)=0,
 \end{cases}
 \qquad
 t_i(B,C)=a_i(C)F_i(B,C).
\tag{540.6}
$$

若 $Q_i(C)>0$，则 $0\le t_i$ 且 $\sum_Bt_i(B,C)=\min\{Q_i(C),V_i(C)\}$；若 $Q_i(C)=0$，这一和也为零。因此

$$
 u_i(B)=W_i(B)-\sum_Ct_i(B,C)\ge0,
 \qquad
 z_i(C)=V_i(C)-\sum_Bt_i(B,C)\ge0,
\tag{540.7}
$$

并且

$$
 \sum_Bu_i(B)=\sum_Cz_i(C)=\operatorname{TV}(Q_i,V_i)=\varepsilon_i.
\tag{540.8}
$$

$u_i$ 只在 $i\in B$ 时可能非零：若 $i\notin B$，则 $W_i(B)=F_i(B,C)=0$。同样，$z_i$ 只在 $i\in C$ 时可能非零：若 $i\notin C$，则 $V_i(C)=0$，而 $Q_i(C)>0$ 时（540.6）给出 $a_i(C)=0$，$Q_i(C)=0$ 时 $t_i$ 仍为零。定义联合表

$$
 g_i(B,C)=
 \begin{cases}
 t_i(B,C)+u_i(B)z_i(C)/\varepsilon_i,&\varepsilon_i>0,\\
 t_i(B,C),&\varepsilon_i=0.
 \end{cases}
\tag{540.9}
$$

乘积补项非负，且由（540.8）可知 $g_i$ 的 $B$ 边缘为 $W_i$、$C$ 边缘为 $V_i$。上述支撑说明每个正质量格点都满足 $i\in B\cap C$。这是一个单状态表，不把 $i$ 交给最后的核读取。

对 $i\ne j$，令

$$
 O_{ij}=\sum_{B,C}\min\{g_i(B,C),g_j(B,C)\}.
\tag{540.10}
$$

$F_i,F_j$ 的公共部分恰是 $i,j\in B$ 的格点，质量为 $r_{ij}(w)$。从 $F_i$ 到 $t_i$ 删除的总质量是 $\varepsilon_i$，从 $F_j$ 到 $t_j$ 删除的总质量是 $\varepsilon_j$，故逐点不等式

$$
 \min(t_i,t_j)\ge \min(F_i,F_j)-(F_i-t_i)-(F_j-t_j)
$$

求和后，再用 $g_i\ge t_i,g_j\ge t_j$，得到

$$
 O_{ij}\ge r_{ij}(w)-\varepsilon_i-\varepsilon_j.
\tag{540.11}
$$

对每个同时含 $i,j$ 的 $C$，$g_i,g_j$ 在该列的总质量都为 $v_C$；其他列没有共同支撑，而它们整体的 $C$ 边缘分别为 $V_i,V_j$。于是

$$
 \begin{aligned}
 \frac12\sum_{C\supseteq\{i,j\}}\sum_B|g_i(B,C)-g_j(B,C)|
 &=r_{ij}(v)-O_{ij}\\
 &\le \Delta_{ij}+\varepsilon_i+\varepsilon_j.
 \end{aligned}
\tag{540.12}
$$

左侧非负，故这也证明了（540.4）中的每个有符号预算非负。注意这里只能把 $\Delta_{ij}$ 作为带两个边缘误差的项使用；近似前向并不保证 $\Delta_{ij}\ge0$。

对 $v_C>0$ 定义

$$
 R(B\mid C)=\frac{1}{|C|v_C}\sum_{j\in C}g_j(B,C).
\tag{540.13}
$$

由每个 $g_j$ 的 $C$ 边缘为 $v_C$，右式对 $B$ 求和为一。对 $v_C=0$ 的 $C$ 任取一个概率行；这不会被任何 $g_j$ 的正质量使用。该补全只依赖观测到的 $C$，所以 $R$ 是一个核而不是一族按状态选择的规则。

把 $g_i$ 看成带有 $C$ 标签的联合律，$V_iR$ 是把同一个 $C$ 上的联合律按 $|C|^{-1}$ 平均后再忘掉 $C$。忘掉标签只会收缩 TV；对每个 $C\ni i$，凸性给出

$$
 \operatorname{TV}\!\left(g_i(\cdot,C),\frac1{|C|}\sum_{j\in C}g_j(\cdot,C)\right)
 \le \frac1{|C|}\sum_{j\in C}\operatorname{TV}(g_i(\cdot,C),g_j(\cdot,C)).
\tag{540.14}
$$

其中 $j=i$ 项为零，而 $i,j\in C$ 且 $j\ne i$ 时 $|C|\ge2$，所以 $|C|^{-1}\le1/2$。对 $C$ 求和并应用（540.12），得到

$$
 \operatorname{TV}(V_iR,W_i)
 \le \frac12\sum_{j\ne i}
 \frac12\sum_{C\supseteq\{i,j\}}\sum_B|g_i-g_j|
 \le b_i.
\tag{540.15}
$$

这里外层的 $1/2$ 来自 $i\ne j$ 且 $i,j\in C$ 时的 $1/|C|\le1/2$，内层的 $1/2$ 来自半 $L^1$ TV 定义，故最后正是（540.4）的系数。再由 $\Delta_{ij}\le|\Delta_{ij}|\le\eta$、$\varepsilon_i,\varepsilon_j\le\varepsilon$，每行至多有 $n-1$ 项，得（540.5），并以 $1$ 截断。

若所有 $\varepsilon_i=0$，则 $Q_i=V_i$，故 $a_i=1$、$u_i=z_i=0$，从而 $g_i=F_i$。此时（540.13）化为

$$
 R(B\mid C)=\frac{|B|f_{BC}}{|C|v_C}\quad(B\subseteq C),
\tag{540.16}
$$

在 $v_C=0$ 时仍任意补全，正是定理 539.2 的核（539.5）；（540.15）退化为其半成对和界。因而这里是在 $\varepsilon=0$ 处逐字恢复 539，而不是仅比较一个较弱的极限。证毕。

定理中的补项是单个残差耦合：$u_i z_i/\varepsilon_i$ 的两个边缘分别补齐 $B$ 与 $C$，不需要任何正权重下界，也不需要 Hoffman 型误差常数。它只证明一个明确构造的恢复核的上界；（540.5）没有声称 $\eta$ 或 $\varepsilon$ 的系数最优。

### 推论 540.3（实际 $q$ 纤维的投影与拼接）

设实际支撑只含有限行 $(i,q)$，其实际纤维为 $A_q$，$n_q=|A_q|$。令

$$
 O_q=\{(q,C):\varnothing\ne C\subseteq A_q\}.
$$

取一个固定的 $b_q\in O_q$，定义后处理 $P_q$：它固定 $O_q$ 中的输出，把所有不在 $O_q$ 中的输出送到 $b_q$。对任意候选核 $H$，在观测到源 $q$ 后定义

$$
 H^{\sharp}(\cdot\mid(q,B))=H(\cdot\mid(q,B))P_q.
\tag{540.17}
$$

每个真实源行都支撑在 $O_q$，目标行也支撑在 $O_q$，故 $V_{i,q}P_q=V_{i,q}$，而 TV 收缩给出

$$
 \operatorname{TV}(W_{i,q}H^{\sharp},V_{i,q})
 \le \operatorname{TV}(W_{i,q}H,V_{i,q}).
\tag{540.18}
$$

因此先在每个实际 $A_q$ 上应用定理 540.2，再按观测到的 $q$ 拼成一个全局核，得到

$$
 d_{\mathrm{global}}=\max_{q:\,A_q\ne\varnothing}d_q,
\tag{540.19}
$$

其中最大值只遍历实际出现的纤维。反向方向由任意全局核限制到每个 $q$ 得到，正向方向由各个 $R_q$ 按已观测 $q$ 拼接得到；没有加入不存在的 $(i,q)$ 行，也没有把分别可行的局部律当成一个共同的公开分划律。$n_q=1$ 的纤维按定理 540.2 的空和处理。

### 定理 540.4（整种子、零权重重建与风险双边带）

设 $E_w,E_v$ 是第 538.2 节的原始公开实验，$C_v:E_v\to W_v$ 是规范化核，$J_w:W_w\to E_w$ 是整种子重建核。令 $R$ 为定理 540.2 或推论 540.3 得到的规范核，并置

$$
 R_{\mathrm{raw}}=C_v\,R\,J_w.
\tag{540.20}
$$

则对每条实际行 $s$，

$$
 \operatorname{TV}((E_v)_sR_{\mathrm{raw}},(E_w)_s)
 \le \operatorname{TV}((W_v)_sR,(W_w)_s)\le b_s.
\tag{540.21}
$$

一般近似核可以到达 $w_B=0$ 的块，但对（540.13）的特定核 $R$，实际输出 $V_iR$ 不会到达这些块：由（540.9）中 $g_j$ 的非负性及其 $B$ 边缘为 $W_j$ 可知此时 $g_j(B,C)=0$，而 $v_C=0$ 的列不承载任何实际 $V_i$ 质量。$J_w$ 仍须在这些输入行补成概率行；（540.21）的 Markov 后处理 TV 收缩论证不依赖上述不可达性。反向、正向两边都与第 538.2 节的精确双向映射复合，故原始整种子实验与规范实验的有向缺损相等。

若 $e_s=\operatorname{TV}((W_w)_sH,(W_v)_s)$ 是给定近似前向核的逐行误差，且 $b_s$ 是反向核保证，则对任意先验 $\pi$ 和 $[0,1]$ 损失 $\lambda$ 有

$$
 -\sum_s\pi_s e_s
 \le \mathcal R_{E_v}(\pi,\lambda)-\mathcal R_{E_w}(\pi,\lambda)
 \le \sum_s\pi_s b_s.
\tag{540.22}
$$

左侧由 $H$ 把 $E_w$ 近似送到 $E_v$，右侧由 $R_{\mathrm{raw}}$ 把 $E_v$ 送回 $E_w$；对每个固定决策规则，风险差的绝对值受相应行 TV 控制，再对先验求和并取下确界即可。近似前向时不能沿用 539.3 的“风险差非负”；（540.22）是有效的两侧先验风险带。先验平均量也不等同于最大状态缺损，零先验行仍受逐态核约束。

### 定理 540.5（偶数匹配—擦除族的两向精确缺损）

令 $n\ge4$ 为偶数，$A=\{1,\ldots,n\}$。匹配实验 $M$ 的唯一非零块权重为

$$
 w^M_{\{i,j\}}=\frac1{n-1}\quad(i\ne j),
\tag{540.23}
$$

擦除实验 $E_\gamma$（$0\le\gamma\le1$）的块权重为

$$
 w^{E_\gamma}_{\{i\}}=1-\gamma,
 \qquad w^{E_\gamma}_{A}=\gamma.
\tag{540.24}
$$

则

$$
 d(E_\gamma\mathbin{\to}M)=\gamma\left(1-\frac2n\right),
 \qquad
 d(M\mathbin{\to}E_\gamma)=\frac{1-\gamma}{2}.
\tag{540.25}
$$

证明：两实验可在一个共同公开概率空间实现。取独立的 $Z\sim\operatorname{Bernoulli}(\gamma)$ 与均匀完美匹配 $P$，公开整个 $(Z,P)$ 及观测块。$M$ 忽略 $Z$，输出 $P$ 中含真实状态的二点块；$E_\gamma$ 在 $Z=0$ 输出单点，在 $Z=1$ 输出 $A$，忽略 $P$。偶数性正是存在完美匹配的条件；奇数集不能由全二点块组成。

从 $E_\gamma$ 到 $M$ 的达到核，在输入单点 $\{i\}$ 时均匀输出包含 $i$ 的二点集，在输入 $A$ 时均匀输出全部 $\binom n2$ 个二点集。对状态 $i$，每个相邻二点的质量为

$$
 \frac{1-\gamma}{n-1}+\frac{\gamma}{\binom n2},
$$

目标质量是 $1/(n-1)$；相邻二点的总亏损与非相邻二点的总盈余都为 $\gamma(1-2/n)$，故 TV 正是该值。

任取一个从 $E_\gamma$ 到二点字母表的核 $H$，令 $D=H(\cdot\mid A)$，并令 $I_i$ 为含 $i$ 的二点输出集合。目标 $M_i(I_i^c)=0$，所以

$$
 \operatorname{TV}((E_\gamma)_iH,M_i)
 \ge \gamma D(I_i^c).
\tag{540.26}
$$

对 $i$ 平均时，任意二点输出恰含两个状态，其他输出不含于任何 $I_i$，因而

$$
 \frac1n\sum_iD(I_i^c)=1-\frac2nD\{C:|C|=2\}\ge1-\frac2n.
\tag{540.27}
$$

最大行误差至少为平均值，得到第一式的任意核下界。等价地，这是一个有界决策证书：行动为二点集、损失为真实状态不在行动中；$M$ 的风险为零，而 $E_\gamma$ 的最小风险为 $\gamma(1-2/n)$。

反向达到核从任意二点 $B$ 输出 $A$ 的概率为 $\gamma$，否则均匀输出 $B$ 的端点。状态 $i$ 下，$A$ 的质量为 $\gamma$，正确单点的质量为 $(1-\gamma)/2$，错误单点的总质量为 $(1-\gamma)/2$，故 TV 为 $(1-\gamma)/2$。

为证明任意反向核的下界，对每个状态定义分数

$$
 g_i(C)=
 \begin{cases}
 1,&C=\{i\},\\
 1/2,&C=A,\\
 0,&\text{其他}.
 \end{cases}
\tag{540.28}
$$

对任意二点输入 $B$ 和任意输出 $C$，都有 $\sum_{i\in B}g_i(C)\le1$。于是对均匀先验和任意核 $H$，

$$
 \frac1n\sum_i\int g_i\,d(M_iH)
 \le\frac1{n(n-1)}\sum_{B:|B|=2}\int\sum_{i\in B}g_i\,dH(\cdot\mid B)
 \le\frac12.
\tag{540.29}
$$

而每个目标行的分数期望为 $1-\gamma/2$。TV 支配任意 $[0,1]$ 分数期望的差，故最大行 TV 至少为 $(1-\gamma)/2$。这覆盖所有输出字母，包括目标支撑外的输出；它也可表述为行动为全部状态标签及一个拒答动作的有界决策证书，拒答损失恒为 $1/2$。证毕。

在 $\gamma=1/(n-1)$ 时，两族的成对剖面逐项相同，故 $\eta=0$，而

$$
 \varepsilon=d(E_\gamma\to M)=\frac{n-2}{n(n-1)},
 \qquad
 d(M\to E_\gamma)=\frac{n-2}{2(n-1)},
 \qquad
 \frac{d(M\to E_\gamma)}{\varepsilon}=\frac n2.
\tag{540.30}
$$

因此偶数 $n$ 增长时，成对摘要完全不变、前向误差趋于零，而反向缺损趋于 $1/2$。任何在 $\eta=0$ 时形如 $d(v\to w)\le C_n\varepsilon$ 的普适系数都必须满足 $C_n\ge n/2$。这只给出必要下界；定理 540.2 的统一系数是 $n-1$，没有声称其最优。

最小例子是 $n=4,\gamma=1/3$：$M$ 的六个二点块中每个权重为 $1/3$，$E_{1/3}$ 以 $2/3$ 输出真实单点、以 $1/3$ 输出全集；两向缺损分别为 $1/6$ 与 $1/3$，比值为 $2=n/2$。等成对剖面在所有偶数 $n\ge4$ 上给出同一增长序列。奇数时全二点匹配的公共分划不存在，所以不能把该公开实现直接延伸到奇数。

### 注记 540.6（成对摘要的逃逸、原目的与全任务互换）

在 CAR 类中，$r_{ij}$ 确实决定每一个单独二态实验的碰撞概率；保持全部 $r_{ij}$ 就保持这些分离的二态任务。它没有决定所有状态怎样共享同一个输出表。匹配实验和擦除实验的成对摘要相同，却在“返回一个含真实状态的二点列表”和“允许拒答的识别”两个任务上分别给出不同风险；故摘要逃逸是相对于所选摘要的联合表示缺口，不是说现实凭空产生了新信息，也不是把一个实验排成对所有任务都更好。原目的若为非恒定目标，直接复用命题 539.7 的嵌入；本族的常数目标只用于清楚地隔离比较任务。

这一区别不能被解释为“定义任意所以现实任意”。第 538.1–538.4 节已经固定实际支撑、公开种子、观察权限和共同分划律；第 539.1–539.8 节固定有向缺损、风险和原目的。维特根斯坦《哲学研究》§§65–69 只提供一种解释性对应：可考察交错相似，并可为一个特定目的划界；这些段落不是概率论、CAR 或缺损定理。这里没有经验性性别结论、披露义务或必然无穷逃逸结论。

后续的精确问题是：在同样的 CAR、共同 $H$、逐态 $\varepsilon_i\le\varepsilon$ 和 $\eta=\max|\Delta_{ij}|$ 条件下，是否总有

$$
 d(v\to w)\le
 \min\left\{1,\frac12\max_i\sum_{j\ne i}(\Delta_{ij})_+ +\frac n2\varepsilon\right\}?
\tag{540.31}
$$

式（540.30）说明其中的 $n/2$ 不能在这一公共族上降为维数无关的常数；它没有证明（540.31）的普适充分性。该问题与本章已证的 $n-1$ 系数界保持分开。

来源边界如下。Torgersen, *Comparison of Experiments when the Parameter Space is Finite*, Z. Wahrscheinlichkeitstheorie verw. Geb. 16 (1970), 219–249, DOI [10.1007/BF00534598](https://doi.org/10.1007/BF00534598)，第 220 页说明有界损失与半 $L^1$ 约定之间的因子二转换；第 230 页的测试比较使用所有有符号线性组合，而不只是原始二态对；第 235 页给出比较性加逐对等价推出整体等价的定性结论及缺少比较性时的失败。这里的（540.9）–（540.15）是有限联合表的直接构造，未把那些定性条件当成当前速率。

Peña、Vera、Zuluaga, *An algorithm to compute the Hoffman constant of a system of linear constraints*, arXiv:1804.08418v1 (2018), Proposition 5 的误差界要求非空解纤维并引入依赖约束矩阵的 Hoffman 常数；它不提供（540.5）的显式 $n$ 率，因此本章不以该一般误差界替代联合表证明。仓内 [第 538.2、538.4 节](FORMAL_CONCEPT_DYNAMICS.md)、[第 539.1–539.8 节](FORMAL_CONCEPT_DYNAMICS.md) 提供公共分划、精确映射、成对摘要和原目的接口；[D5/S3/Estimation/DecisionRisk/AsymmetricFamilyDeficiency.lean](../../../D5/S3/Estimation/DecisionRisk/AsymmetricFamilyDeficiency.lean) 及其风险注入模块讨论的是非 CAR 的不对称正似然列，不能替代本章的公共匹配/擦除族。以上是所用来源的范围，不构成全局优先性声明。

## 追加锚（本行以下为增补区）

## 541. 成对信息不变的局部替换：任意共同背景下的精确恢复距离

### 定义 541.1（精确块容量、CAR 背景与公开实现）

沿用定义 540.1 的有限非空状态集 $A$，记 $n=|A|$、$\mathcal B=2^A\setminus\{\varnothing\}$。CAR 剖面及其规范实验满足

$$
w_B\ge0,\qquad \sum_{B\ni i}w_B=1,\qquad
(W_w)_i(B)=\mathbf1_{\{i\in B\}}w_B,
\qquad i\in A,\ B\in\mathcal B.
\tag{541.1}
$$

记 $r_{ij}(w)=\sum_{B\supseteq\{i,j\}}w_B$。本章的有向缺损仍取半 $L^1$ 及最大状态误差：

$$
d(w\to v)=\inf_K\max_{i\in A}
\frac12\sum_{C\in\mathcal B}
\left|\sum_{B\in\mathcal B}(W_w)_i(B)K(C\mid B)-(W_v)_i(C)\right|.
\tag{541.2}
$$

下确界遍历 $\mathcal B$ 到 $\mathcal B$ 的全部随机核；一个核须同时用于所有状态，可以输出目标零权重块，也可以把输入块送到不包含真实状态的块。后文的达到核只是这一允许集中的具体成员。

在一个共同读数、无冲突的模型中，称剖面公开可实现，是指存在 $A$ 的分划集合 $\Pi(A)$ 上的一个概率律 $p$，使

$$
w_B=\sum_{P\in\Pi(A)}p_P\mathbf1_{\{B\in P\}}.
\tag{541.3}
$$

每个状态共用同一个 $p$。这一条件比（541.1）强；不同实验可以有不同的分划律。CAR 行方程、分划混合与二者的区别均沿用定理 538.2，不作为新的定义理论。Gill–Grünwald, *An Algorithmic and a Geometric Characterization of Coarsening At Random*, [arXiv:math/0510276v3，§2、Example 1、§4](https://arxiv.org/html/math/0510276v3) 给出 CAR 方程、三角障碍及均匀多重覆盖表示；多重覆盖表示不等于（541.3）的分划混合。

固定 $U\subseteq A$，$m=|U|\ge3$。对每个 $B\in\mathcal B$ 定义方向

$$
z_U(B)=
\begin{cases}
1,&B=U,\\
m-2,&B=\{i\},\ i\in U,\\
-1,&B\subseteq U,\ |B|=2,\\
0,&\text{其他}.
\end{cases}
\tag{541.4}
$$

这里二点容量 $w_{\{i,j\}}$ 指输出恰为 $\{i,j\}$ 的权重，不能换成所有包含该对的块权重之和 $r_{ij}(w)$。共同背景允许任意满足（541.1）的其余质量，包括同时交于 $U$ 和 $A\setminus U$ 的块；没有分离背景与核心的假设。

### 定理 541.2（任意共同 CAR 背景下的局部双向精确距离）

设 $w^-$ 为 CAR 剖面，$a\ge0$，且

$$
w^-_{\{i,j\}}\ge a\qquad(i,j\in U,\ i\ne j).
\tag{541.5}
$$

置 $w^+=w^-+az_U$。则 $w^+$ 仍为 CAR 剖面，全部成对摘要相同，并且

$$
\boxed{
d(w^+\to w^-)=\frac{a(m-2)}m,
\qquad
d(w^-\to w^+)=\frac{a(m-2)}2.}
\tag{541.6}
$$

两个值均由下述共同核达到，每个 $i\in U$ 的误差都等于相应值，每个 $i\notin U$ 的误差都为零。该断言不要求两个端点公开可实现；若端点另有（541.3）的见证，相同精确值也适用于它们。

证明：只在精确二点块上减去质量，故（541.5）保证非负性。对 $i\in U$，行和的改变量为

$$
a+(m-2)a-(m-1)a=0;
\tag{541.7}
$$

对 $i\notin U$，改变的块均不含 $i$，行和不变。对 $\{i,j\}\subseteq U$，成对摘要中 $U$ 的增量 $a$ 与精确块 $\{i,j\}$ 的减量 $a$ 抵消；其他成对坐标没有改变量。因此归一化和成对保持均成立。另由任一 $i\in U$ 的源行和得 $(m-1)a\le1$。若 $a=0$，两端相同，恒等核达到（541.6）；以下设 $a>0$。

先构造从 $w^+$ 到 $w^-$ 的核。令 $\mathcal Q_U=\{B\subseteq U:|B|=2\}$，$\mathcal Q_{U,j}=\{B\in\mathcal Q_U:j\in B\}$；$\nu_{\mathcal Q_U}$、$\nu_{\mathcal Q_{U,j}}$ 分别为这两个有限非空集合上的均匀律，均视作 $\mathcal B$ 上的概率律。对观察到的块定义

$$
\begin{aligned}
K_{+,-}(\cdot\mid U)
&=\left(1-\frac a{w^+_U}\right)\delta_U
  +\frac a{w^+_U}\nu_{\mathcal Q_U},\\
K_{+,-}(\cdot\mid\{j\})
&=\left(1-\frac{(m-2)a}{w^+_{\{j\}}}\right)\delta_{\{j\}}
  +\frac{(m-2)a}{w^+_{\{j\}}}\nu_{\mathcal Q_{U,j}}
  \quad(j\in U),\\
K_{+,-}(\cdot\mid B)&=\delta_B
  \quad\text{对其余 }B\in\mathcal B.
\end{aligned}
\tag{541.8}
$$

因 $w^+_U=w^-_U+a\ge a>0$，$w^+_{\{j\}}=w^-_{\{j\}}+(m-2)a\ge(m-2)a>0$，全部分母合法，全部系数在 $[0,1]$。从观察块权重 $w_B$ 中抽取质量 $b$，实现为条件概率 $b/w_B$；这是按输出字母定义的操作，不读取状态。其余行包括所有零权重输入，均已由 $\delta_B$ 补全为概率行。

固定 $i\in U$。在目标二点块 $\{i,j\}\subseteq U$ 上，保留的共同质量是 $w^-_{\{i,j\}}-a$，额外进入的质量是

$$
\frac{(m-2)a}{m-1}+\frac a{\binom m2}
=a-\frac{a(m-2)}{m(m-1)}.
\tag{541.9}
$$

所以这 $m-1$ 个块各亏 $a(m-2)/(m(m-1))$。不含 $i$ 的 $U$ 内二点块各获得 $a/\binom m2$，目标行在这些块为零；其总盈余为

$$
\binom{m-1}2\frac a{\binom m2}
=\frac{a(m-2)}m.
\tag{541.10}
$$

在 $U$ 和正确单点上抽出的质量恰好消去新增质量，其余坐标与目标相同，故半 $L^1$ 为（541.10），也等于总亏损。若 $i\notin U$，所有被操作的输入在该状态都不出现，其余输入均保持原字母，故精确恢复。特别地，跨越 $U$ 与补集的背景块在所有行均保持原位。

再构造从 $w^-$ 到 $w^+$ 的核。对每个 $B=\{j,k\}\in\mathcal Q_U$ 定义

$$
K_{-,+}(\cdot\mid B)
=\left(1-\frac a{w^-_B}\right)\delta_B
 +\frac a{w^-_B}
 \left[\frac1{m-1}\delta_U
 +\frac{m-2}{2(m-1)}(\delta_{\{j\}}+\delta_{\{k\}})\right],
\tag{541.11}
$$

其他输入取 $K_{-,+}(\cdot\mid B)=\delta_B$。这里 $w^-_B\ge a>0$，方括号内总质量为 $1/(m-1)+(m-2)/(m-1)=1$，所以仍是一个处处定义的共同核，所有零权重输入均在恒等补全中。

固定 $i\in U$，其 $m-1$ 个相邻二点输入各抽出质量 $a$。于是 $U$ 收到增量 $a$，正确单点 $\{i\}$ 收到 $(m-2)a/2$，每个错误单点 $\{j\}$、$j\in U\setminus\{i\}$ 收到 $(m-2)a/[2(m-1)]$。目标在正确单点要求的增量为 $(m-2)a$，故该处亏损 $(m-2)a/2$，恰等于错误单点的总盈余；其余坐标均正确。半 $L^1$ 因而为 $a(m-2)/2$。外部状态仍从不观察到被操作的二点输入，恢复误差为零。至此仅得到两个上界，最优性还须针对任意核证明。

为此取先验 $\pi_i=1/m$（$i\in U$），$\pi_i=0$（$i\notin U$），记 $k_B=|B\cap U|$。对任意 CAR 剖面 $w$，输出 $B$ 的先验概率为 $k_Bw_B/m$；当此数为正时，后验均匀于 $B\cap U$。考虑以下两个有限决策任务。第一个行动集为 $\mathcal Q_U$，对 $i\in U$ 的损失为

$$
\lambda_2(i,D)=\mathbf1_{\{i\notin D\}},\qquad D\in\mathcal Q_U;
\tag{541.12}
$$

对 $i\notin U$ 规定损失为零。在 $k_B\ge1$ 时，一个二元素列表最多覆盖后验中的 $\min(k_B,2)$ 个状态，且可以达到；故其最小条件损失为 $(k_B-2)_+/k_B$。

第二个行动集为 $U\cup\{\bot\}$，其中 $\bot\notin U$ 是拒答动作。对 $i\in U$，规定

$$
\lambda_{\mathrm r}(i,j)=\mathbf1_{\{i\ne j\}}\quad(j\in U),
\qquad \lambda_{\mathrm r}(i,\bot)=\frac12;
\tag{541.13}
$$

对 $i\notin U$ 所有行动损失仍为零。在正概率输出上，识别的最小条件损失为 $1-1/k_B$，拒答为 $1/2$；随机化不会低于两者的最小值。因此两个最小 Bayes 风险恰为

$$
\begin{aligned}
L_2(w)&=\frac1m\sum_{B\in\mathcal B}w_B(k_B-2)_+,\\
L_{\mathrm r}(w)&=\frac1m\sum_{B\in\mathcal B}
 w_B\min\{(k_B-1)_+,k_B/2\}.
\end{aligned}
\tag{541.14}
$$

当 $k_B=0$ 时，该输出在先验下概率为零，两个求和项也均为零；不对空集定义后验。在 $w_B=0$ 的字母上同样没有风险贡献。可在每个 $k_B\ge1$ 的字母选择上述最优行动，在 $k_B=0$ 时任取一个固定允许行动，由此把决策规则定义在整个 $\mathcal B$，包括目标零权重字母。所有损失始终位于 $[0,1]$。

式（541.14）对 $w$ 线性。共同背景中任何块的 $k_B$ 和权重都不改变，因此它们的风险贡献逐项抵消，不论是否跨越 $U$ 的边界。单点对两式的贡献均为零；二点对 $L_2$ 的贡献为零、对 $L_{\mathrm r}$ 的系数为 $1/m$；$U$ 对两式的系数分别为 $(m-2)/m$ 和 $1/2$。所以

$$
\begin{aligned}
L_2(w^+)-L_2(w^-)&=\frac{a(m-2)}m,\\
L_{\mathrm r}(w^-)-L_{\mathrm r}(w^+)
&=\frac{a}{m}\binom m2-\frac a2
=\frac{a(m-2)}2.
\end{aligned}
\tag{541.15}
$$

现对任意从实验 $X$ 到实验 $Y$ 的候选核 $K$，在其后复合 $Y$ 的上述最优决策规则 $D_Y$。对每个状态 $i$，函数 $g_i(C)=\sum_dD_Y(d\mid C)\lambda(i,d)$ 在整个字母表上取值于 $[0,1]$，故由第 539.3 节所用的有界损失转移，

$$
\mathcal R_X(\pi,\lambda)-\mathcal R_Y(\pi,\lambda)
\le\sum_{i\in U}\frac1m\operatorname{TV}(X_iK,Y_i)
\le\max_{i\in A}\operatorname{TV}(X_iK,Y_i).
\tag{541.16}
$$

第一步是源的最优风险不超过复合规则的风险，然后以 TV 控制该规则与目标风险之差。它未要求 $K$ 保持块包含关系、限制输出支撑或固定外部状态。特别地，向目标零权重块输出也已被 $g_i$ 覆盖。把（541.15）的第一行用于 $X=W_{w^+},Y=W_{w^-}$，第二行用于相反方向，便对每个允许核得到与上界相等的下界。取下确界即得（541.6）。证毕。

此处风险转移是既有方法。Torgersen, *Comparison of Experiments when the Parameter Space is Finite*, [DOI:10.1007/BF00534598](https://doi.org/10.1007/BF00534598)，印刷页 220 使用对 $[-1,1]$ 函数取上确界的全变差范数，并说明改用非负有界损失时的因子二；在概率差上该范数是本章 TV 的两倍。本证明直接使用 $[0,1]$ 损失和半 $L^1$，不挪用未转换的常数。其印刷页 230 的 Theorem 10 对全部有符号混合向量量化，页 235 的逐对等价结论另要求实验可比，均不直接给出（541.6）的任意背景公式。

### 推论 541.3（三状态全部等成对纤维的有向距离）

取 $A=\{1,2,3\}$，给定 $r=(r_{12},r_{13},r_{23})\in[0,1]^3$，并令

$$
\begin{aligned}
\ell_{\mathrm{CAR}}
&=\max\{0,r_{12}+r_{13}-1,r_{12}+r_{23}-1,r_{13}+r_{23}-1\},\\
u&=\min\{r_{12},r_{13},r_{23}\}.
\end{aligned}
\tag{541.17}
$$

全部具有成对值 $r$ 的 CAR 剖面由 $t\in[\ell_{\mathrm{CAR}},u]$ 唯一参数化：

$$
w_{123}(t)=t,\qquad
w_{ij}(t)=r_{ij}-t,\qquad
w_i(t)=1-r_{ij}-r_{ik}+t
\quad(\{i,j,k\}=A).
\tag{541.18}
$$

下端大于上端时纤维为空。对于区间内任意 $t_1,t_2$，不要求 $r$ 对称，有

$$
\boxed{
d(w(t_1)\to w(t_2))
=\frac{(t_2-t_1)_+}{2}+\frac{(t_1-t_2)_+}{3}.}
\tag{541.19}
$$

其中公开子纤维另由定理 538.7 的区间

$$
\left[\ell_{\mathrm{pub}},u\right],\qquad
\ell_{\mathrm{pub}}=\max\left\{0,\frac{r_{12}+r_{13}+r_{23}-1}{2}\right\}
\tag{541.20}
$$

给出，下端大于上端时公开子纤维为空。（541.19）在整个 CAR 区间成立，不能把（541.17）的下端替换成公开下端后仍称为全部 CAR 剖面。

证明：固定三点块权重 $t$ 后，成对方程迫使 $w_{ij}=r_{ij}-t$，三个行方程再迫使单点取（541.18）的值。七项非负恰为（541.17）的上下界，反向代入也满足全部行方程，故这是完整参数化。对于公开实现，沿用（538.25）的五种分划权重：全合并为 $t$，$ij|k$ 为 $r_{ij}-t$，离散分划为 $1-r_{12}-r_{13}-r_{23}+2t$。它们的非负性恰给（541.20）；单点块权重是离散分划权重与对应 $jk|i$ 权重之和，因此公开区间确实包含在 CAR 区间中。此实现判据复用 538.7。

若 $t_1<t_2$，取 $U=A$、$m=3$、$a=t_2-t_1$。对每个精确二点块有

$$
w_{ij}(t_1)-a=r_{ij}-t_2\ge0,
\qquad w(t_2)-w(t_1)=az_A.
\tag{541.21}
$$

故定理 541.2 给 $d(w(t_2)\to w(t_1))=a/3$、$d(w(t_1)\to w(t_2))=a/2$。交换参数及 $a=0$ 的恒等情形便得（541.19）。不对称的单点、二点剩余质量均属该定理允许的共同背景，故没有遗漏不对称 $r$。证毕。

对命题 539.6 的既有平台端点，$r=(3/5,1/5,1/5)$、$t_-=1/10$、$t_+=1/5$，代入 $t_+-t_-=1/10$ 得

$$
d(w(t_+)\to w(t_-))=\frac1{30},\qquad
d(w(t_-)\to w(t_+))=\frac1{20}.
\tag{541.22}
$$

这使（539.26）在后一方向的 $1/30$ 下界严格加强为精确值；原有下界仍有效。对（538.28）的既有均匀端点 $r_{ij}=1/3$、$t=0,1/3$，同理得到从高 $t$ 到低 $t$ 为 $1/9$，反向为 $1/6$。这些端点及相反任务机制来自 538.7、539.6，不是新构造。Bertschinger–Rauh, *The Blackwell relation defines no lattice*, [arXiv:1401.3146v1，Example 18](https://arxiv.org/html/1401.3146v1) 已给出相关三状态通道的非随机因子化障碍和决策分离；该例不承担（541.19）对整个非对称 CAR 纤维的精确缺损公式。仓内 [AsymmetricFamilyDeficiency](../../../D5/S3/Estimation/DecisionRisk/AsymmetricFamilyDeficiency.lean) 的二状态族有不相等的正列似然值，不属于这里的 CAR 等成对纤维，不能用其单向精确模拟结果代替本推导。

### 推论 541.4（所有状态数的公开必要系数与任意小误差）

令 $n\ge3$，$A=\{1,\ldots,n\}$。定义 $P_a,E_a$ 的非零候选块权重为

$$
\begin{aligned}
p^a_{\{i,j\}}&=a\quad(i\ne j),&
p^a_{\{i\}}&=1-(n-1)a,\\
e^a_A&=a,&e^a_{\{i\}}&=1-a,
\end{aligned}
\tag{541.23}
$$

其余块权重为零，零端点允许。两者公开可实现的共同参数范围为

$$
0\le a\le
\begin{cases}
1/(n-1),&n\text{ 为偶数},\\
1/n,&n\text{ 为奇数}.
\end{cases}
\tag{541.24}
$$

在此范围全部 $r_{ij}$ 都等于 $a$，且

$$
d(E_a\to P_a)=\frac{a(n-2)}n,
\qquad
d(P_a\to E_a)=\frac{a(n-2)}2.
\tag{541.25}
$$

因此对每个固定 $n\ge3$，若一个系数 $C_n$ 对全部同成对公开实验满足 $d(v\to w)\le C_n d(w\to v)$，就必须有 $C_n\ge n/2$；即使只要求该不等式在任意给定的正前向误差邻域内成立，也有同一必要条件。

证明：先说明公开实现，所用匹配机制正是命题 539.5。偶数时，以概率 $\theta=(n-1)a$ 均匀选择一个完美匹配分划，否则选离散分划。固定状态的伙伴均匀分布在其余 $n-1$ 个状态，故每条边出现概率 $a$，单点权重为 $1-\theta=1-(n-1)a$。奇数时，以概率 $\theta=na$ 均匀选择一个只有一个未匹配单点的近完美匹配分划，否则选离散分划。每个匹配有 $(n-1)/2$ 条边，置换对称性使指定边的出现概率为 $1/n$，指定状态未匹配的概率也是 $1/n$。混合后边权为 $\theta/n=a$，单点权重为 $1-\theta+\theta/n=1-(n-1)a$。式（541.24）保证混合概率合法；每种构造都给所有状态共用的一个分划律。

该范围也不能在本族中扩大：CAR 行和已要求 $(n-1)a\le1$；公开实现 $P_a$ 的每个正概率分划只能含单点和二点块，其二点块构成匹配，所以

$$
\binom n2 a=\mathbb E[\text{二点块数}]
\le\lfloor n/2\rfloor.
\tag{541.26}
$$

偶数时给 $a\le1/(n-1)$，奇数时给 $a\le1/n$。特别地，奇数的 CAR 容许范围 $a\le1/(n-1)$ 大于公开范围，不能将其全部用于公开锐度。$E_a$ 则以概率 $a$ 使用全合并分划，否则使用离散分划；（541.24）下总是合法。

若要求两实验放在同一个状态无关公开概率空间，取上述两个随机分划的独立乘积 $(P,Q)$ 作为整个公开种子。$P_a$ 发送 $[i]_P$，$E_a$ 发送 $[i]_Q$，两边均揭示整个 $(P,Q)$。这只是共同概率空间上的联合实现，不要求 $P,Q$ 逐次细化，也不把分别为不同状态选分划当成共同实现。经定理 538.2 的双向规范映射，它们分别等价于（541.23）的两个块实验。

最后，（541.23）恰满足 $e^a=p^a+az_A$，其每个精确二点块容量均为 $a$。定理 541.2 以 $U=A,m=n$ 给出（541.25），包括对全部输出核的下界和达到核。若 $a>0$，两距离之比为 $n/2$；令 $a\downarrow0$ 可使前向距离任意小而保持此比值。偶数 $n\ge4$ 且 $a=1/(n-1)$ 时正好回到（540.30），不是替换该已有例子；奇数时保留未匹配单点取得同一比值。$a=0$ 时两实验均完全揭示，距离为零，不作零比值运算。证毕。

### 定义 541.5（摘要等价、任务替代及未决恢复界的范围）

在上述固定状态、观察和共同核合同内，沿用 538.4 的摘要等价 $r(w)=r(v)$，以及 539.8 的误差 $\eta$ 单向替代 $d(w\to v)\le\eta$。定理 541.2 给出两者之间一个精确区分：在其容量条件下沿 $az_U$ 改变时，每一对状态的二态实验类均保持，但均匀于 $U$ 的二元素列表风险增加 $a(m-2)/m$，允许拒答的识别风险减少 $a(m-2)/2$。当 $a>0$ 时，只保留成对类的描述因而丢失了这两个任务之间的区别；只对相同 $r$ 作后处理不能辨认所丢失的 $a$。这不是在共同原始字母表上逐行保留全部二行核的情形，后者按 538.4 已决定全部概率行。

接回实际旧读数 $q$ 时，仅在第 540.3 节的实际有限纤维 $A_q$ 内使用本章公式，并按已观察的 $q$ 拼接；全局缺损取局部最大值。若要求公开实现，各纤维仍须来自第 538.2 节的一个共同全局分划律，不能把逐纤维 CAR 条件或逐纤维公开见证当成全局见证。两个端点已有这样的实现时，复用第 540.4 节的双向精确映射，规范缺损等于原始整种子实验缺损。重建恢复的是目标的整个种子与标签的联合概率律，不是已经发生过的那次种子取值；零权重输入仍按该节补成概率行。

对原目的非恒定的合同，可直接按命题 539.7 给本章已公开可实现的核心添加分离状态并保持同一旧读数：核心目标为零，新状态目标为一，每次分划把新状态单列。该命题的输出投影与核扩张使本章的两向最大状态缺损保持不变。若核心大小为 $m$，距离比仍为 $m/2$；加入分离状态并不把这一个例子的比值改成较大环境状态数的一半。这里较小的先验平均风险与最大状态缺损也按 539.7 保持区分。

局部替换限定 $m\ge3$，不把（541.4）的分段定义套到 $m=1,2$。边界上，单态 CAR 只有权重一的单点，双向缺损为零。二态 CAR 由共同块权重 $r\in[0,1]$ 决定，两个单点权重均为 $1-r$，且

$$
d(W_r\to W_s)=\frac{(r-s)_+}{2}.
\tag{541.27}
$$

这是已有擦除机制的边界计算：$r\le s$ 且 $r<1$ 时，把已识别单点以概率 $(s-r)/(1-r)$ 擦除即可精确模拟；$r=s=1$ 取恒等核。$r>s$ 时，从共同块以概率 $(r-s)/r$ 均匀猜测两个单点，其余保持，逐态错误为 $(r-s)/2$；等先验二态识别风险差给任意核相同的下界。每个二态剖面也都由概率 $r$ 的全合并与概率 $1-r$ 的离散分划实现。因此（540.31）在 $n=1,2$ 没有留下缺口。对一般 $n$，若最优前向缺损为零，有限核达到性给精确前向核，第 540.2 节的 CAR 上界退化为第 539.2 节的半成对行和界；此时各 $\Delta_{ij}\ge0$，与（540.31）的正部一致。

为明确剩余问题，仍令 $\Delta_{ij}=r_{ij}(v)-r_{ij}(w)$、$\varepsilon=d(w\to v)$。所问的普适不等式保持为

$$
d(v\to w)\le
\min\left\{1,\frac12\max_i\sum_{j\ne i}(\Delta_{ij})_+
                 +\frac n2\varepsilon\right\}.
\tag{541.28}
$$

这是（540.31）取最优前向核的同一问题；若能对最优值证明，也就对任一给定核的较大误差预算成立。它在一般 CAR 类和公开分划混合子类中的充分性均仍为 **open**。本章证明三状态等成对纤维的全部有向距离，并证明每个 $n\ge3$ 的公开必要系数为至少 $n/2$；没有证明三状态非零有符号成对差情形，也没有证明一般状态数的等成对充分界。

即使成对差为零，线性方向分解也不能填补这个缺口。事实上，若 $x=v-w$ 满足零行和及零成对和，则有代数恒等式

$$
x=\sum_{\substack{U\subseteq A\\|U|\ge3}}x_Uz_U.
\tag{541.29}
$$

证明只需从 $x$ 减去右侧：每个大小至少为三的块坐标被自己的项消去；剩余向量仍有零成对和，因此每个精确二点坐标为零；再由零行和，所有单点坐标也为零。然而（541.29）中的系数可正可负、各个 $U$ 可相交，它不保证依次替换的中间权重非负，也不提供每一步的精确二点容量；在公开类中还须满足分划混合约束。即使另有一条可行链，缺损的三角不等式也只给端点距离的上界。各步达到下界所用的先验、行动和最优规则未必能合成一个共同任务，使端点的前向下界等于各步之和；不能用链长上界充当所需的前向下界。一般（541.28）还须在同一联合实现中控制非零 $\Delta$ 的正部预算。这些是未完成的组合条件，代数恒等式本身不证明其可能或不可能。

Peña–Vera–Zuluaga, *An algorithm to compute the Hoffman constant of a system of linear constraints*, [arXiv:1804.08418v1，Proposition 5](https://arxiv.org/html/1804.08418v1) 的距离界以等式与不等式解纤维非空为条件，常数依赖矩阵及所选范数；该命题不指定这里的 $n/2$，也不证明上述任务证书可加。CAR/公开表示、匹配机制、二态擦除和有界损失转移均为本章已标明的前置；任意共同背景的精确局部式及其整个三状态纤维应用由本章证明承担。上述具体来源范围不构成全球原创优先性声明。

本定义与维特根斯坦《哲学研究》[§§65–69](https://www.wittgensteinproject.org/w/index.php/Philosophische_Untersuchungen#65) 的对应仅是解释性的：§§65–67 考察实际使用中的交错相似，§§68–69 允许为特定目的划界，而不要求通常语言先取得这种边界。本章固定状态、可见材料、行动和损失之后，才判定哪些关系在更换描述时保持、哪些任务区别未被摘要保存；这些概率论规定不是维特根斯坦的定理。其与现实的连接以实际对象满足该比较合同为条件，不从数学构造断定经验前提成立，不推出普遍相对主义、经验性性别结论或披露义务。完整有限剖面仍可保存这些区别，故这里也不推出必要的无限信息逃逸。

## 追加锚（本行以下为增补区）

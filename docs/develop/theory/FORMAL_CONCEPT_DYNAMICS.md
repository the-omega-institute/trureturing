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
}
\]

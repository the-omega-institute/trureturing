# C-IRPT 四基础角色上的形式概念动力学、完备化与无终局反射理论

## A Conservative Reconstruction of Formal Concept Dynamics from CUT, FLOW, ADMIT, and ANCHOR

**作者：** Auric / The Omega Institute  
**重构版本：** v5.0  
**日期：** 2026-09-04  
**文件地位：** 项目既有理论与 Lean 定理之上的统一重构稿；本文中的新增综合命题在获得独立 Lean proof term、依赖闭包、admission 与冻结收据之前，不标记为 `Closed`。

---

## 记号与状态

本文采用五类状态标记：

- **`[P] Project-defined`**：项目母文中已经明确给出的定义或纪律；
- **`[L] Lean-closed`**：仓库中已有对应机器证明；
- **`[D] Derived`**：可由项目既有定义或 Lean 定理直接推出，但尚未单独封装；
- **`[N] New package`**：本文新增的统一接口、命名或建议形式化定理；
- **`[O] Open bridge`**：仍需新的实质数学、物理或语义桥梁。

本文不重新发明“分、变、向、返”作为新原语。它们至多是下列四个项目既有角色的中文解释：

\[
\boxed{
\mathsf{CUT}
\;+\;
\mathsf{FLOW}
\;+\;
\mathsf{ADMIT}
\;+\;
\mathsf{ANCHOR}.
}
\]

项目母文同时明确规定：这四者是 C-IRPT 的构造性底层语言，但**不是新逻辑原语**。它们可递归展开为类型、函数、谓词、依赖和相等证明，因此相对于底层类型论构成定义性保守扩张。

---

# 第一部　基础校正：四者是角色，不是四种神秘实体

## 1. C-IRPT 的逻辑地位 `[P]`

设底层语言为 \(\mathcal L_0\)，其中已有：

\[
\mathsf{Type},\qquad
\mathsf{Prop},\qquad
\Pi,\qquad
\Sigma,\qquad
(=),\qquad
\text{函数与复合}.
\]

C-IRPT 语言 \(\mathcal L_{\mathrm{CIRPT}}\) 通过显式定义加入 `CUT`、`FLOW`、`ADMIT`、`ANCHOR` 等术语。若：

\[
(-)^\flat:
\mathcal L_{\mathrm{CIRPT}}\longrightarrow
\mathcal L_0
\]

递归展开全部新增术语，则定义性保守性要求：

\[
T_{\mathrm{CIRPT}}\vdash\varphi
\quad\Longrightarrow\quad
T_0\vdash\varphi
\]

对旧语言命题 \(\varphi\) 成立。

所以：

\[
\boxed{
\text{C-IRPT 的价值不来自增加形而上公理，}
}
\]

而来自：

\[
\boxed{
\text{把分类、过程、合法性和实际见证的关系变成可审计的类型结构。}
}
\]

---

## 2. 四个基础角色的精确定义 `[P]`

### 2.1 CUT：界面切分

一个 CUT 是：

\[
\boxed{
q:X\to B.
}
\]

它规定相对同一性：

\[
x\sim_q y
\quad\Longleftrightarrow\quad
q(x)=q(y).
\]

\(B\) 是当前界面保留的可见坐标。

因此 CUT 不是一个词，而是一个分类接口。两个字面标签不同的接口，只要诱导相同相等核，就具有相同区分能力。

---

### 2.2 FLOW：有类型作用

一个 FLOW 是：

\[
\boxed{
F:X\to Y.
}
\]

该定义本身不预设：

- 可逆；
- 连续；
- 线性；
- 保测度；
- 因果；
- 局部；
- 可计算；
- 解析。

这些必须作为额外性质逐项证明。

当 \(X=Y\) 时可定义离散迭代：

\[
F^0=\operatorname{id}_X,
\qquad
F^{n+1}=F\circ F^n.
\]

离散时间是 FLOW 迭代的索引，不是额外本体实体。连续时间则需显式给出半群：

\[
T:\mathbb R_{\ge0}\to(X\to X),
\qquad
T_{s+t}=T_s\circ T_t.
\]

---

### 2.3 ADMIT：准入谓词

一个 ADMIT 是：

\[
\boxed{
A:X\to\mathsf{Prop}.
}
\]

其合法对象类型为：

\[
\boxed{
X_A
=
\sum_{x:X}A(x).
}
\]

定义 \(A\) 不会自动证明 \(X_A\) 非空。

ADMIT 可以实例化在不同载体上：

\[
\begin{aligned}
A_X &: X\to\mathsf{Prop}
&&\text{合法状态},\\
A_U &: U\to\mathsf{Prop}
&&\text{允许行动},\\
A_{\mathrm{Path}} &: \mathrm{Path}\to\mathsf{Prop}
&&\text{合法轨迹},\\
A_{\mathrm{Model}} &: \mathrm{Model}\to\mathsf{Prop}
&&\text{可接受模型},\\
A_{\mathrm{Claim}} &: \mathrm{Claim}\to\mathsf{Prop}
&&\text{可认证主张},\\
A_{\mathrm{Stage}} &: \mathrm{Stage}\to\mathsf{Prop}
&&\text{可准入研究阶段}.
\end{aligned}
\]

因此规范、范围、合法性、许可和实现条件不需要另设第五种基础角色；它们都是 ADMIT 在不同类型上的实例。

---

### 2.4 ANCHOR：实际且证明相关的锚

给定：

\[
q:X\to B,\qquad b:B,
\]

先定义依赖余纤维：

\[
\boxed{
R_q(b)
=
\sum_{x:X}(q(x)=b).
}
\]

一个锚点类型是：

\[
\operatorname{Anchor}(q,b)=R_q(b).
\]

若还要求状态准入 \(A:X\to\mathsf{Prop}\)，则：

\[
\boxed{
\operatorname{AdmissibleAnchor}(q,A,b)
=
\sum_{a:R_q(b)}A(\pi_Xa).
}
\]

ANCHOR 的**类型**可以由 CUT 和 ADMIT 定义；但该类型中的一个**具体项**不能由定义凭空产生。

所以 ANCHOR 的地位是：

\[
\boxed{
\text{语法上是依赖见证，语义上是不可由结构自动替代的实际数据。}
}
\]

---

## 3. REMAINDER 不是第五基础角色 `[P/L]`

余量完全由 CUT 派生：

\[
R_q(b)
=
\sum_{x:X}(q(x)=b).
\]

仓库中的 `ConceptFiberDecomposition` 已证明：

\[
\boxed{
X
\simeq
\sum_{b:B}R_q(b).
}
\]

因此任何状态都可写成：

\[
x
\longleftrightarrow
\bigl(q(x),\ \text{位于 }q(x)\text{ 之下的余纤维项}\bigr).
\]

这给出：

\[
\boxed{
\text{现象坐标}
+
\text{依赖余量}
=
\text{完整状态的 CUT 相对分解}.
}
\]

余量并不是“道”或一个固定隐藏物；它随 CUT 与坐标 \(b\) 改变。

---

## 4. 四角色最小性：逻辑最小性与模型最小性必须分开

### 4.1 逻辑层

在底层类型论中，四者都能展开，因此它们不是不可定义的逻辑原语。

### 4.2 模型角色层

在一个哲学、科学或观察模型中，四种角色不能互相偷换：

- CUT 回答“哪些状态被当作相同”；
- FLOW 回答“状态怎样改变”；
- ADMIT 回答“哪些状态、行动或模型被算作合法”；
- ANCHOR 回答“当前实际是哪一个见证”。

它们形状上有重叠，但语义职责不同。

---

## 定理 4.1　四角色非互相决定 `[D]`

在有限 Boolean 模型上可以构造：

1. 相同 FLOW、ADMIT、ANCHOR，但 CUT 不同；
2. 相同 CUT、ADMIT、ANCHOR，但 FLOW 不同；
3. 相同 CUT、FLOW、ANCHOR，但 ADMIT 不同且均接纳锚点；
4. 相同 CUT、FLOW、ADMIT，但 ANCHOR 不同。

例如取 \(X=\mathbf2\)：

\[
q_1=\operatorname{id},
\qquad
q_2=\mathrm{const};
\]

\[
F_1=\operatorname{id},
\qquad
F_2=\neg;
\]

\[
A_1(x)=\top,
\qquad
A_2(x)\equiv(x=\mathsf{false});
\]

\[
a_1=\mathsf{false},
\qquad
a_2=\mathsf{true}.
\]

所以四角色是模型语义上的独立坐标。

仓库中的 `ObserverConceptReadoutCorrespondence` 进一步机器证明：仅保存联合读数的 kernel quotient，会遗忘 admissibility、anchor，以及读数族如何分解为坐标；并给出同核而准入不同、同核而锚点不同、读数族不同而联合核相同的反模型。

---

# 第二部　项目既有模型的规范重组

## 5. 原始哲学模型 `[P]`

项目的 `FORMAL_CONCEPT_DYNAMICS.md` 已给出：

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
X&:\mathsf{Type}
&&\text{状态或世界类型},\\
\operatorname{Adm}&:X\to\mathsf{Prop}
&&\text{准入谓词},\\
a&:\sum_{x:X}\operatorname{Adm}(x)
&&\text{实际锚点},\\
U&:\mathsf{Type}
&&\text{行动／过程索引},\\
F&:U\to X\to X
&&\text{过程族},\\
O&:\mathsf{Type}
&&\text{观察者类型},\\
\mathcal C&:O\to\operatorname{Concept}(X)
&&\text{观察者概念族}.
\end{aligned}
\]

这已经包含四角色：

\[
\mathcal C=\mathsf{CUT},
\quad
F=\mathsf{FLOW},
\quad
\operatorname{Adm}=\mathsf{ADMIT},
\quad
a=\mathsf{ANCHOR}.
\]

---

## 6. 已有 Lean `ObserverStructure` `[L]`

仓库已有：

```lean
structure ObserverStructure
    (X : Type u) (Index : Type v)
    (Value : Index → Type w) where
  readout : ∀ index, X → Value index
  admissible : (∀ index, Value index) → Prop
  anchor : X
  anchorAdmissible :
    admissible (jointReadout readout anchor)
```

它已直接承载：

- 一族 CUT；
- 联合读数上的 ADMIT；
- ANCHOR；
- 锚点准入证明。

所以不应再平行定义新的 `Concept`、`Observer`、`jointReadout` 或 `AnchorStructure`。

---

## 7. 最小 C-IRPT 适配器 `[N]`

只需把已有观察者结构与 FLOW 过程族配对：

```lean
abbrev CIRPTSystem
    (X : Type u)
    (Index : Type v)
    (Value : Index → Type w)
    (U : Type z) :=
  ObserverStructure X Index Value × (U → X → X)
```

这不是新原语，只是重组已有接口。

对系统 \(S\)，定义：

\[
\begin{aligned}
J_S(x)
&=
\bigl(S.\mathrm{readout}_i(x)\bigr)_i,
\\
A_S(x)
&=
S.\mathrm{admissible}(J_S(x)),
\\
a_S
&=
S.\mathrm{anchor},
\\
F^S_u
&=
S.\mathrm{flow}(u).
\end{aligned}
\]

已有字段给出：

\[
A_S(a_S).
\]

因此实际锚可规范包装为：

\[
\boxed{
\widehat a_S:
\sum_{x:X}A_S(x).
}
\]

---

## 8. 状态级 ADMIT 与坐标级 ADMIT

项目母文采用：

\[
A_X:X\to\mathsf{Prop}.
\]

`ObserverStructure` 采用：

\[
A_B:
\left(\prod_iB_i\right)\to\mathsf{Prop}.
\]

二者通过联合 CUT \(J\) 联系：

\[
A_X^{J}(x)
=
A_B(J(x)).
\]

一个任意状态级 ADMIT \(A_X\) 能够由当前 CUT 执行，当且仅当存在：

\[
\overline A:
\left(\prod_iB_i\right)\to\mathsf{Prop}
\]

使：

\[
\boxed{
A_X
\;\Longleftrightarrow\;
\overline A\circ J.
}
\]

若不存在这种下降，则当前管理员只能看到相同坐标，却必须对同一纤维中的状态作不同准入判断。

这不是纯规范分歧，而是**行政界面不充分**。

---

# 第三部　C-IRPT 的依赖纤维正规形

## 9. CUT 正规形 `[L]`

给定：

\[
q:X\to B,
\]

令：

\[
\Phi_q:
X
\simeq
\sum_{b:B}R_q(b)
\]

为项目已证明的纤维分解等价。

在该坐标中：

\[
q
=
\pi_1\circ\Phi_q.
\]

所以任何 CUT 都可以正规化为第一投影：

\[
\boxed{
(b,r)\longmapsto b.
}
\]

其中：

- \(b\) 是显式界面坐标；
- \(r\in R_q(b)\) 是该坐标下的完整依赖余量。

---

## 10. ADMIT 正规形 `[D]`

状态准入 \(A:X\to\mathsf{Prop}\) 被输运为：

\[
\boxed{
A^\sharp(b,r)
=
A(\Phi_q^{-1}(b,r)).
}
\]

若存在 \(\overline A:B\to\mathsf{Prop}\) 满足：

\[
A^\sharp(b,r)\leftrightarrow\overline A(b),
\]

则 ADMIT 不依赖余量，能够下降到界面。

否则，同一可见坐标 \(b\) 下既有合法余量项，也有非法余量项。

---

## 11. ANCHOR 正规形 `[D]`

实际锚点：

\[
a:\sum_{x:X}A(x)
\]

在 CUT 坐标下成为：

\[
\boxed{
\Phi_q(\pi_Xa)
=
(b_a,r_a),
}
\]

并带有：

\[
A^\sharp(b_a,r_a).
\]

所以：

\[
\boxed{
\text{ANCHOR}
=
\text{一个可见坐标}
+
\text{该坐标下的实际余量项}
+
\text{准入证明}.
}
\]

当前现象只显示 \(b_a\)，并不自动显示 \(r_a\)。

---

## 12. FLOW 正规形 `[D]`

给定：

\[
F:X\to Y,
\qquad
q_X:X\to B,
\qquad
q_Y:Y\to C,
\]

定义共轭后的 FLOW：

\[
\widetilde F
=
\Phi_{q_Y}
\circ F
\circ\Phi_{q_X}^{-1}.
\]

其类型为：

\[
\widetilde F:
\sum_{b:B}R_{q_X}(b)
\longrightarrow
\sum_{c:C}R_{q_Y}(c).
\]

写作：

\[
\widetilde F(b,r)
=
\bigl(
\beta_F(b,r),
\rho_F(b,r)
\bigr).
\]

这里：

\[
\beta_F(b,r)
=
q_Y
\left(
F(\Phi_{q_X}^{-1}(b,r))
\right)
\]

是未来可见坐标，而：

\[
\rho_F(b,r)
\]

是未来余纤维坐标。

---

## 定理 12.1　下降的纤维正规形 `[D]`

以下条件等价：

1. 存在 \(\overline F:B\to C\)，使：

   \[
   q_Y\circ F
   =
   \overline F\circ q_X;
   \]

2. \(\beta_F(b,r)\) 对源余量 \(r\) 不敏感：

   \[
   \forall b,r,r',
   \quad
   \beta_F(b,r)=\beta_F(b,r');
   \]

3. 同一个源 CUT 纤维不会被 FLOW 映入多个目标 CUT 纤维。

在精确下降时：

\[
\boxed{
\widetilde F(b,r)
=
\bigl(
\overline F(b),
F_b(r)
\bigr)
}
\]

对某个依赖纤维映射：

\[
F_b:
R_{q_X}(b)
\to
R_{q_Y}(\overline F(b)).
\]

因此，精确下降并不消灭余量；它只保证：

\[
\boxed{
\text{未来显坐标由当前显坐标决定，隐藏余量在纤维内部输运。}
}
\]

---

## 13. causal carry 的正规形 `[P/D]`

项目定义：

\[
\operatorname{CarryWitness}(F;q_X,q_Y)
=
\sum_{x,y:X}
(q_Xx=q_Xy)
\times
(q_YFx\ne q_YFy).
\]

在依赖纤维正规形中，它等价于：

\[
\boxed{
\sum_{b:B}
\sum_{r,r':R_{q_X}(b)}
\bigl(
\beta_F(b,r)\ne\beta_F(b,r')
\bigr).
}
\]

所以 causal carry 的确切意义是：

\[
\boxed{
\text{当前 CUT 所隐藏的余量，经 FLOW 后改变未来可见坐标。}
}
\]

这比“相关性”更弱地依赖统计结构，却更强地暴露界面失败。

---

## 14. 两种 carry

### 14.1 横向 carry

隐藏余量穿过 FLOW，变成未来 CUT 差异：

\[
r\ne r'
\quad\leadsto\quad
\beta_F(b,r)\ne\beta_F(b,r').
\]

它阻碍 FLOW 在商空间上的下降。

### 14.2 纵向 carry

在加法商余结构中选取截面 \(s\)，项目定义：

\[
\boxed{
\kappa_s(a,b)
=
s(a)+s(b)-s(a+b).
}
\]

且：

\[
q(\kappa_s(a,b))=0.
\]

它表示显坐标上的组合虽然闭合，但经选定 ANCHOR/section 提升后，在余核中积累了差异。

因此：

\[
\boxed{
\begin{aligned}
\text{横向 carry}
&=\text{余量逃向显坐标};\\
\text{纵向 carry}
&=\text{显坐标组合回落到余量}.
\end{aligned}}
\]

---

## 定理 14.1　截面 carry 的二余循环律 `[D]`

若加法结合，则：

\[
\boxed{
\kappa_s(a,b)+\kappa_s(a+b,c)
=
\kappa_s(b,c)+\kappa_s(a,b+c).
}
\]

证明：

\[
\begin{aligned}
\kappa_s(a,b)+\kappa_s(a+b,c)
&=
s(a)+s(b)+s(c)-s(a+b+c),\\
\kappa_s(b,c)+\kappa_s(a,b+c)
&=
s(a)+s(b)+s(c)-s(a+b+c).
\end{aligned}
\]

若改变截面：

\[
s'(a)=s(a)+h(a),
\]

则：

\[
\boxed{
\kappa_{s'}(a,b)
=
\kappa_s(a,b)
+
h(a)+h(b)-h(a+b).
}
\]

所以截面 carry 按 coboundary 改变；适当条件下，其等价类而非某一具体坐标表达是稳定对象。

---

# 第四部　统一下降演算

## 15. 目标也是 CUT

给定任意目标：

\[
T:X\to Z,
\]

它在类型上仍是一个 CUT。

目标不是第五基础角色。区别只在语义职责：

- \(q\) 是当前可用界面；
- \(T\) 是希望由该界面恢复的读数。

---

## 16. 一般目标残差 `[L]`

定义：

\[
\boxed{
\operatorname{Residual}(q,T)
=
\{(x,y):
q(x)=q(y)
\land
T(x)\ne T(y)\}.
}
\]

即：

\[
\operatorname{Residual}(q,T)
=
\ker q\setminus\ker T.
\]

它表示当前 CUT 合并了目标必须区分的状态。

---

## 定理 16.1　统一下降判据 `[L]`

在仓库定理所需的非空条件下，以下等价：

\[
\exists\overline T:B\to Z,
\quad
T=\overline T\circ q;
\]

\[
\forall x,y,\quad
q(x)=q(y)\Rightarrow T(x)=T(y);
\]

\[
\operatorname{Residual}(q,T)=\varnothing.
\]

因此几乎全部概念动力学问题都可归约为：

\[
\boxed{
\text{某个目标是否在当前 CUT 的每个余纤维上保持常值。}
}
\]

---

## 17. 统一实例

令一般目标 \(T\) 分别取为：

\[
\begin{array}{c|c}
T & \text{所得问题}\\ \hline
\text{性质读数} & \text{该性质是否可由概念回答}\\
q_Y\circ F & \text{FLOW 是否沿 CUT 下降}\\
A:X\to\mathsf{Prop} & \text{ADMIT 是否可由界面执行}\\
\pi:X\to U & \text{政策是否可由概念实现}\\
\text{history evaluation} & \text{历史评价是否可约为端点}\\
\text{counterfactual target} & \text{反事实是否可由实验数据恢复}\\
\operatorname{id}_X & \text{CUT 是否忠实／单射}
\end{array}
\]

所以“知识、预测、因果、规范执行、责任、解释”并非各自需要一套新的数学原语；它们是同一下降判据在不同目标类型上的实例。

---

# 第五部　CUT 演算

## 18. 精化 `[P/L]`

给定：

\[
q:X\to B,
\qquad
q':X\to B',
\]

\(q'\) 精化 \(q\)，当且仅当存在：

\[
p:B'\to B
\]

使：

\[
q=p\circ q'.
\]

即：

\[
\operatorname{Refines}(q',q)
=
\sum_{p:B'\to B}
\prod_{x:X}
q(x)=p(q'(x)).
\]

对有效读数，精化等价于反向 kernel 包含：

\[
q'\text{ 精化 }q
\quad\Longleftrightarrow\quad
\ker q'\subseteq\ker q.
\]

---

## 19. 概念格 `[L]`

项目已经证明：

\[
\boxed{
\text{有效概念的互相精化类}
\cong
\operatorname{OrderDual}(\operatorname{Setoid}(X)).
}
\]

因此概念联合：

\[
(q\vee r)(x)=(q(x),r(x))
\]

对应 kernel 交：

\[
\ker(q\vee r)
=
\ker q\cap\ker r.
\]

共同粗化则对应：

\[
\operatorname{EqCl}(\ker q\cup\ker r).
\]

所以：

\[
\boxed{
\begin{aligned}
\text{概念联合}
&=\text{同时保留两者区别};\\
\text{概念共同粗化}
&=\text{遗忘二者不能共同维持的区别}.
\end{aligned}}
\]

---

## 20. 静态 CUT 平坦性 `[D]`

固定 \(d,e\)：

\[
(q\vee d)\vee e
\simeq
(q\vee e)\vee d.
\]

因为：

\[
\ker q\cap\ker d\cap\ker e
\]

与顺序无关。

所以：

\[
\boxed{
\text{固定定义的静态联合不产生曲率。}
}
\]

任何真正路径依赖必须来自：

- 定义由当前残差自适应产生；
- 中途改变 FLOW；
- 中途改变 ADMIT；
- 中途改变 ANCHOR；
- 隐藏记忆被更新；
- 阶段发生反射扩张。

---

## 21. 最小目标完成 `[L]`

定义：

\[
\mathsf C_T(q)=q\vee T.
\]

项目已经证明它是：

- 广延的；
- 单调的；
- 幂等的；
- 在所有同时精化 \(q\) 且决定 \(T\) 的概念中最粗。

因此：

\[
\boxed{
\mathsf C_T(q)
}
\]

是固定目标的规范最小完成。

但：

\[
\mathsf C_T^2(q)\simeq\mathsf C_T(q)
\]

只表示同一目标不需重复加入，不表示所有未来目标均已完成。

---

## 22. 多目标完成 `[L]`

对依赖目标族：

\[
T_i:X\to Y_i,
\]

定义联合目标：

\[
J_T(x)(i)=T_i(x).
\]

项目已证明：

\[
\boxed{
J_T
\text{ 是同时充分于全部 }T_i
\text{ 的最粗概念。}
}
\]

目标族的盲残差则是各分量盲残差的并：

\[
\operatorname{Blind}(J_T)
=
\bigcup_i\operatorname{Blind}(T_i).
\]

因此同时完成整个问题族，严格等价于完成每个分量问题。

---

## 23. 语言盲核 `[L]`

设当前定义语言为 \(\Gamma\)，其共同 kernel：

\[
K_\Gamma
=
\bigcap_{d\in\Gamma}\ker d.
\]

定义：

\[
\boxed{
\operatorname{Blind}(\Gamma,q,T)
=
\operatorname{Residual}(q,T)
\cap
K_\Gamma.
}
\]

若该集合非空，则存在一对状态：

- 当前 CUT 看不见其差异；
- 当前语言中所有定义也看不见；
- 目标却必须区分。

于是：

\[
\boxed{
\text{无限增加旧语言搜索预算也不能切开该对。}
}
\]

必须加入一个不在旧语义闭包内的新 CUT。

---

## 24. 定义创造 `[P/L]`

项目 DECT 将四角色用于定义创造：

\[
\begin{aligned}
\mathsf{CUT}
&=\text{候选定义切割当前纤维};\\
\mathsf{FLOW}
&=\text{残差和定义沿动力学、尺度、推理传播};\\
\mathsf{ADMIT}
&=\text{目标无关、自然、稳定、低成本、可认证约束};\\
\mathsf{ANCHOR}
&=\text{具体反例、构造、解析估计或形式证书}.
\end{aligned}
\]

生产性定义要求：

\[
\exists(x,y)\in\operatorname{Blind}(\Gamma,q,T),
\quad
d(x)\ne d(y).
\]

它不仅是新字符串，而且切开了当前目标相关盲核。

因此：

\[
\boxed{
\text{创造力}
=
\text{生产性逃逸}
+
\text{压缩性恢复}.
}
\]

---

# 第六部　FLOW 演算与动态完成

## 25. 精确下降 `[P/L]`

给定：

\[
q_X:X\to B,
\qquad
q_Y:Y\to C,
\qquad
F:X\to Y,
\]

精确下降是：

\[
\boxed{
\exists\overline F:B\to C,
\quad
q_Y\circ F
=
\overline F\circ q_X.
}
\]

项目已证明，精确下降排除 carry。

---

## 26. 动态闭合概念

对过程族：

\[
F:U\to X\to X,
\]

CUT \(q\) 是干预闭合的，当：

\[
q(x)=q(y)
\Rightarrow
q(F_u x)=q(F_u y)
\]

对所有 \(u\) 成立。

这等价于每个 FLOW 都能下沉到概念商。

---

## 27. 完全行为 CUT `[L]`

定义：

\[
\widehat q_F(x)(w)
=
q(\operatorname{runWord}(F,w,x)),
\qquad
w\in U^*.
\]

项目的 `DynClosure` 正是：

\[
\operatorname{controlledBehavior}(F,q).
\]

项目已证明：

1. \(\widehat q_F\) 精化 \(q\)；
2. \(\widehat q_F\) 对所有干预闭合；
3. 任意精化 \(q\) 且干预闭合的候选概念，都进一步精化 \(\widehat q_F\)。

所以：

\[
\boxed{
\widehat q_F
\text{ 是包含原 CUT 的最小动态闭合精化。}
}
\]

---

## 28. 动态概念核 `[D]`

给定目标：

\[
T:X\to Y,
\]

定义：

\[
\boxed{
\operatorname{Core}_F(T)
=
\bigcap_{w\in U^*}
\ker(T\circ F_w).
}
\]

即：

\[
x\sim_{\operatorname{Core}_F(T)}y
\iff
\forall w,\quad
T(F_wx)=T(F_wy).
\]

它是所有：

- 对 FLOW 稳定；
- 对目标全部未来行为充分；

的等价关系中最粗的一个。

所以：

\[
\boxed{
X/\operatorname{Core}_F(T)
}
\]

是固定 \((X,F,T)\) 下的最小充分动态状态。

这意味着：

\[
\boxed{
\text{固定任务内部可以存在真正的规范最终概念。}
}
\]

---

## 29. 观察、干预、反事实是 FLOW 视界层级 `[L]`

在模型空间 \(\Theta\) 上，不同协议族产生不同 CUT：

\[
\begin{aligned}
q_{\mathrm{obs}}
&=\text{被动观测结果},\\
q_{\mathrm{int}}
&=\text{全部单世界干预结果},\\
q_{\mathrm{cf}}
&=\text{保留个体／外生耦合的反事实结果}.
\end{aligned}
\]

项目在同一个有限 Boolean SCM 类上证明：

\[
\boxed{
\ker q_{\mathrm{cf}}
\subsetneq
\ker q_{\mathrm{int}}
\subsetneq
\ker q_{\mathrm{obs}}.
}
\]

所以因果层级不是三种独立本体，而是三种严格增强的 FLOW 协议分辨率。

---

# 第七部　ADMIT 演算

## 30. ADMIT 的 CUT 下近似 `[N/D]`

给定：

\[
q:X\to B,
\qquad
A:X\to\mathsf{Prop},
\]

定义安全下近似：

\[
\boxed{
A_q^\forall(x)
\iff
\forall y,\ 
q(y)=q(x)
\Rightarrow
A(y).
}
\]

定义宽松上近似：

\[
\boxed{
A_q^\exists(x)
\iff
\exists y,\ 
q(y)=q(x)
\land
A(y).
}
\]

总有：

\[
\boxed{
A_q^\forall
\subseteq
A
\subseteq
A_q^\exists.
}
\]

二者都只依赖 CUT 坐标，因此可下降到 \(B\)。

---

## 31. ADMIT 边界 `[N/D]`

定义：

\[
\boxed{
\partial_qA
=
A_q^\exists
\setminus
A_q^\forall.
}
\]

则：

\[
\partial_qA\ne\varnothing
\]

当且仅当存在：

\[
x,y:X
\]

满足：

\[
q(x)=q(y),
\qquad
A(x),
\qquad
\neg A(y).
\]

它表示同一 CUT 纤维内混有合法与非法状态。

---

## 定理 31.1　准入下降判据 `[D]`

以下等价：

1. 存在 \(\overline A:B\to\mathsf{Prop}\)，使：

   \[
   A(x)\leftrightarrow\overline A(q(x));
   \]

2. \(A\) 在每个 CUT 纤维上保持不变；
3. \(\partial_qA=\varnothing\)；
4. \(A=A_q^\forall=A_q^\exists\)。

若边界非空，则任何只读取 \(q(x)\) 的确定性准入规则，都必须在某个状态上分类错误。

这与项目的 mixed-fiber decision impossibility 属于同一个下降障碍。

---

## 32. 两种准入修复

当 \(\partial_qA\ne\varnothing\) 时有两条规范道路。

### 安全修复

只接纳整条纤维都合法的状态：

\[
A\longmapsto A_q^\forall.
\]

优点是无假阳性；代价是可能拒绝原本合法的边界状态。

### 宽松修复

只要纤维中存在合法状态，就接纳整条纤维：

\[
A\longmapsto A_q^\exists.
\]

优点是无假阴性；代价是可能接纳原本非法的边界状态。

### 信息修复

不改变 \(A\)，而精化 CUT：

\[
q\longmapsto q\vee d
\]

直到准入边界消失。

选择哪条道路不是 CUT/FLOW 的纯描述定理，而属于 ADMIT doctrine 与成本结构。

---

## 33. FLOW 对 ADMIT 的稳定性

给定：

\[
F:X\to Y,
\qquad
A_X:X\to\mathsf{Prop},
\qquad
A_Y:Y\to\mathsf{Prop},
\]

定义合法性泄漏：

\[
\boxed{
\operatorname{Leak}(F;A_X,A_Y)
=
\{x:A_X(x)\land\neg A_Y(Fx)\}.
}
\]

定义合法性生成：

\[
\operatorname{Create}(F;A_X,A_Y)
=
\{x:\neg A_X(x)\land A_Y(Fx)\}.
\]

若：

\[
\operatorname{Leak}=\varnothing,
\]

则 FLOW 保持合法性。

若还要求反射：

\[
A_Y(Fx)\Rightarrow A_X(x),
\]

则 FLOW 在准入意义上精确。

---

## 34. 域免疫错误 `[L]`

项目已证明：任何有限目标缺陷都可以通过把准入域缩到一个单点而在受限域上消失，同时删除其他状态；目标依赖的准入规则还可以系统性排除反例。

因此：

\[
\boxed{
\text{受限域残差为零}
\not\Rightarrow
\text{全域规律成立}.
}
\]

任何“完成”报告都必须同时记录：

\[
\boxed{
\text{残差变化}
+
\text{ADMIT 域变化}
+
\text{被删除状态}.
}
\]

---

# 第八部　ANCHOR 演算与存在纪律

## 35. 六层存在纪律 `[P]`

项目区分：

\[
\begin{aligned}
E_0(X)
&:\ X\text{ 可形成};\\
E_1(X)
&:\ \|X\|;\\
E_2(X,A)
&:\ \left\|\sum_{x:X}A(x)\right\|;\\
E_3(X,A)
&:\ a:\sum_{x:X}A(x);\\
E_4(q,b,A)
&:\ \left\|\sum_{x:X}A(x)\times(qx=b)\right\|;\\
E_5(F,a,A)
&:\ \forall n,\ A(F^na).
\end{aligned}
\]

它们分别表示：

\[
\boxed{
\text{可定义、非空、合法可实现、实际锚定、可显现、持续存在}.
}
\]

一般不存在无条件蕴涵：

\[
E_0\Rightarrow E_1,
\qquad
E_1\Rightarrow E_2,
\qquad
E_2\Rightarrow E_3.
\]

---

## 36. ANCHOR 的多种实例

同一依赖见证角色可实例化为：

\[
\begin{aligned}
a_X &: \sum_{x:X}A_X(x)
&&\text{实际状态锚};\\
a_{\mathrm{data}} &: \mathrm{Dataset}
&&\text{经验记录锚};\\
a_{\mathrm{counterexample}} &: \operatorname{Residual}(q,T)
&&\text{反例锚};\\
a_{\mathrm{proof}} &: P
&&\text{命题 }P\text{ 的证明锚};\\
a_{\mathrm{path}} &: \sum_{\gamma:\mathrm{Path}}A_{\mathrm{Path}}(\gamma)
&&\text{历史锚};\\
a_{\mathrm{model}} &: \sum_{m:\mathrm{Model}}A_{\mathrm{Model}}(m)
&&\text{实现模型锚}.
\end{aligned}
\]

因此 `CERTIFY` 不必成为第五基础角色。证书就是某个证书类型或命题类型中的 ANCHOR。

---

## 37. 锚点影子 `[N/D]`

给定实际状态 \(a:X\)，定义：

\[
\boxed{
\operatorname{Shadow}_q(a)
=
\{x:X:
q(x)=q(a)
\land
x\ne a\}.
}
\]

若：

\[
\operatorname{Shadow}_q(a)=\varnothing,
\]

则当前 CUT 唯一识别该实际锚点。

若对所有 \(a\) 均为空，则 \(q\) 单射。

锚点影子非空表示：

\[
\boxed{
\text{当前现象坐标不足以确定实际状态。}
}
\]

---

## 38. 历史不能总被端点代替 `[L]`

设：

\[
\operatorname{endpoint}:\mathrm{Path}\to X,
\]

\[
\operatorname{evaluation}:\mathrm{Path}\to E.
\]

若两条路径端点相同但评价不同，则不存在：

\[
e:X\to E
\]

使评价只由端点决定。

项目已有机器证明：

\[
\boxed{
\text{同一结果、不同历史评价}
\Rightarrow
\text{评价不能约化为结果函数}.
}
\]

所以路径账本不是冗余 ANCHOR；在历史敏感任务中，它是必要状态。

---

## 39. 形式完成与实现完成 `[P]`

项目定义形式逆极限：

\[
\widehat X_{\mathrm{form}}
=
\varprojlim_iX_i.
\]

然后定义实现谓词：

\[
\operatorname{Realizable}:
\widehat X_{\mathrm{form}}
\to\mathsf{Prop}.
\]

实现完成为：

\[
\boxed{
\widehat X_{\mathrm{real}}
=
\sum_{x:\widehat X_{\mathrm{form}}}
\operatorname{Realizable}(x).
}
\]

该类型仍可能为空。

所以：

\[
\boxed{
\text{形式逆极限}
\neq
\text{现实实现}
\neq
\text{实际锚定}.
}
\]

一个实际实现还需要：

\[
a:\widehat X_{\mathrm{real}}.
\]

这里：

- 形式极限由 CUT/FLOW 兼容条件构造；
- `Realizable` 是 ADMIT；
- 实际实现项是 ANCHOR。

---

# 第九部　四重缺陷与任务相对完备

## 40. CUT 缺陷

给定目标 \(T:X\to Z\)：

\[
\boxed{
D_{\mathsf C}(q,T)
=
\{(x,y):
q(x)=q(y)
\land
T(x)\ne T(y)\}.
}
\]

---

## 41. FLOW 缺陷

给定：

\[
F:X\to Y,
\qquad
q_X:X\to B,
\qquad
q_Y:Y\to C,
\]

定义：

\[
\boxed{
D_{\mathsf F}(F;q_X,q_Y)
=
\{(x,y):
q_X(x)=q_X(y)
\land
q_Y(Fx)\ne q_Y(Fy)\}.
}
\]

这就是 causal carry。

---

## 42. ADMIT 缺陷

定义：

\[
\boxed{
D_{\mathsf A}(q,A)
=
\{(x,y):
q(x)=q(y)
\land
\neg(A(x)\leftrightarrow A(y))\}.
}
\]

它等价于准入边界存在混合纤维。

---

## 43. ANCHOR 缺陷

定义：

\[
\boxed{
D_{\mathsf H}(q,a)
=
\operatorname{Shadow}_q(a).
}
\]

其中 \(\mathsf H\) 表示 anchor/history 轴。

---

## 44. 四重缺陷向量 `[N]`

定义：

\[
\boxed{
\mathbf D
(q,F,A,a;T,q_Y)
=
\left(
D_{\mathsf C},
D_{\mathsf F},
D_{\mathsf A},
D_{\mathsf H}
\right).
}
\]

---

## 定理 44.1　四重任务充分性 `[D/N]`

在适当非空条件下：

\[
\mathbf D=0
\]

等价于同时满足：

1. 存在 \(\overline T\)，使：

   \[
   T=\overline T\circ q;
   \]

2. 存在 \(\overline F\)，使：

   \[
   q_Y\circ F=\overline F\circ q;
   \]

3. 存在 \(\overline A\)，使：

   \[
   A(x)\leftrightarrow\overline A(q(x));
   \]

4. 锚点纤维是单点：

   \[
   q(x)=q(a)\Rightarrow x=a.
   \]

因此当前 CUT 对指定目标、指定 FLOW、指定 ADMIT 和指定 ANCHOR 均充分。

但该结论仍是：

\[
\boxed{
\text{任务相对完备},
}
\]

不是：

\[
\boxed{
\text{终极本体完备}.
}
\]

---

## 45. 为什么不能只保存 kernel quotient `[L]`

项目 `ObserverConceptReadoutCorrespondence` 已证明：联合 CUT 的 kernel quotient 精确保留不可区分关系，但会遗忘：

- ADMIT；
- ANCHOR；
- 原始 CUT 族的坐标分解。

因此：

\[
\boxed{
\text{概念商是 CUT 的完备表示，}
}
\]

但不是完整 C-IRPT 系统的完备表示。

---

# 第十部　C-IRPT 的兼容缺陷矩阵与曲率

## 46. 静态兼容缺陷矩阵 `[N]`

以：

\[
(\mathsf C,\mathsf F,\mathsf A,\mathsf H)
=
(\mathsf{CUT},\mathsf{FLOW},\mathsf{ADMIT},\mathsf{ANCHOR})
\]

为四轴，定义上三角缺陷：

\[
\boxed{
\mathbb D(\Sigma)
=
\begin{pmatrix}
0 & D_{\mathsf{CF}} & D_{\mathsf{CA}} & D_{\mathsf{CH}}\\
 & 0 & D_{\mathsf{FA}} & D_{\mathsf{FH}}\\
 &   & 0 & D_{\mathsf{AH}}\\
 &   &   & 0
\end{pmatrix}.
}
\]

其中：

\[
\begin{aligned}
D_{\mathsf{CF}}
&=
D_{\mathsf F}(F;q_X,q_Y)
&&\text{CUT–FLOW carry};\\
D_{\mathsf{CA}}
&=
D_{\mathsf A}(q,A)
&&\text{CUT 不能执行 ADMIT};\\
D_{\mathsf{CH}}
&=
D_{\mathsf H}(q,a)
&&\text{CUT 不能唯一识别 ANCHOR};\\
D_{\mathsf{FA}}
&=
\{x:A_Xx\land\neg A_Y(Fx)\}
&&\text{FLOW 泄漏出合法域};\\
D_{\mathsf{FH}}
&=
\text{可见端点相同但路径／隐藏状态不同}
&&\text{FLOW–ANCHOR 历史差};\\
D_{\mathsf{AH}}
&=
\text{更新 ADMIT 后既有 ANCHOR 失去准入}
&&\text{准入—实际不相容}.
\end{aligned}
\]

该矩阵描述兼容障碍，还不是严格意义的动态曲率。

---

## 47. 动态更新算子

令完整阶段为：

\[
\Sigma
=
(\mathsf{CUT},\mathsf{FLOW},\mathsf{ADMIT},\mathsf{ANCHOR},
\mathsf{Ledger}).
\]

定义四类阶段更新：

\[
U_{\mathsf C},
\quad
U_{\mathsf F},
\quad
U_{\mathsf A},
\quad
U_{\mathsf H}.
\]

它们分别改变：

- 分类界面；
- 过程或干预模型；
- 准入 doctrine；
- 数据、实际状态或历史锚。

---

## 48. C-IRPT 曲率 `[N]`

对两个更新轴 \(i,j\)，定义：

\[
\boxed{
\Omega_{ij}(\Sigma)
=
U_iU_j(\Sigma)
\not\simeq
U_jU_i(\Sigma).
}
\]

更细地，可以分别比较：

\[
\Omega_{ij}^{\mathsf{CUT}}
=
\ker q_{ij}
\triangle
\ker q_{ji},
\]

\[
\Omega_{ij}^{\mathsf{ADMIT}}
=
A_{ij}
\triangle
A_{ji},
\]

以及 ANCHOR、FLOW、ledger 的差异。

因此：

\[
\boxed{
\text{缺陷是当前不相容，曲率是修复顺序的不交换。}
}
\]

---

## 49. 静态无曲率定理 `[D]`

若所有更新只是加入预先固定的 CUT：

\[
q\longmapsto q\vee d,
\]

则更新交换、结合且幂等。

所以固定定义的静态学习系统没有非平凡顺序曲率，也不可能仅靠单调精化形成非平凡闭路。

非零曲率至少需要：

- 自适应定义选择；
- FLOW 更新；
- ADMIT 更新；
- ANCHOR 或历史更新；
- 遗忘；
- 类型扩张。

---

## 50. FLOW–CUT 曲率

比较：

1. 先对 CUT 做动态闭包，再加入当前目标；
2. 先加入目标，再对联合 CUT 做动态闭包。

两条路径之差由“当前目标相同但未来目标分叉”的状态对组成。

这就是未来命名曲率：

\[
\boxed{
\Omega_F^{\mathrm{future}}(q,T)
=
\mathsf B_F(q)
\cap
\ker T
\cap
\mathsf B_F(T)^c.
}
\]

它精确表示：

\[
\forall w,\ q(F_wx)=q(F_wy),
\qquad
T(x)=T(y),
\]

但：

\[
\exists w,\ T(F_wx)\ne T(F_wy).
\]

---

## 51. CUT–ADMIT 曲率

比较：

1. 先按目标精化 CUT，再执行准入；
2. 先用旧 CUT 执行准入，再在受限域内精化。

第二条路径可能通过删除困难状态制造虚假闭合。

项目的 domain-immunization 定理说明：

\[
\boxed{
\text{先缩 ADMIT 域再验证}
}
\]

与：

\[
\boxed{
\text{先在全域验证再调整 ADMIT}
}
\]

一般不交换。

---

## 52. FLOW–ANCHOR 曲率与 holonomy

设动作词 \(w\) 满足：

\[
q(F_w a)=q(a),
\]

但：

\[
F_w a\ne a.
\]

则可见坐标形成闭路，实际锚却没有返回。

这就是：

\[
\boxed{
\text{可见闭路}
+
\text{隐藏锚变化}
=
\text{holonomy}.
}
\]

若甚至完整当前行为 CUT 也不能区分：

\[
\widehat q_F(F_w a)
=
\widehat q_F(a),
\]

则为沉默 holonomy。

---

## 53. 项目中的 prime-memory 曲率实例 `[L]`

项目已经形式化：

- 标量局部因子交换；
- 提升到隐藏记忆后的两个 prime 更新可以不交换；
- swap defect 反对称；
- 共同改变记忆原点时曲率不变；
- 非共振条件下，零曲率等价于局部观察者原点估计一致。

该结果明确是代数定理，不自动等同于 Zeta Euler factor，也不自动推出零点位置。

它为 C-IRPT 提供了一个严格实例：

\[
\boxed{
\begin{aligned}
\text{标量 CUT}
&=\text{底空间},\\
\text{隐藏记忆}
&=\text{余纤维},\\
\text{prime FLOW}
&=\text{纤维输运},\\
\text{交换缺陷}
&=\text{曲率},\\
\text{闭路残余}
&=\text{holonomy}.
\end{aligned}}
\]

---

# 第十一部　知识、真理与怀疑

## 54. 真理

给定实际锚：

\[
a:\sum_{x:X}A(x)
\]

和命题：

\[
P:X\to\mathsf{Prop},
\]

真理是：

\[
\boxed{
P(\pi_Xa).
}
\]

真理要求 ANCHOR，不能由 CUT 值本身替代。

---

## 55. 知识

给定证据 CUT：

\[
e:X\to E,
\]

定义：

\[
\boxed{
\operatorname{Knows}(e,A,a,P)
\iff
\forall x,\ 
A(x)
\to
e(x)=e(\pi_Xa)
\to
P(x).
}
\]

知识表示：

> \(P\) 不仅在实际锚上成立，而且在当前证据坐标兼容的全部合法余量中稳定。

由于锚点合法，知识推出真理。

---

## 56. 怀疑

定义：

\[
\boxed{
\operatorname{Doubt}(e,A,a,P)
\iff
\exists x,\ 
A(x)
\land
e(x)=e(\pi_Xa)
\land
\neg P(x).
}
\]

于是：

\[
\operatorname{Doubt}
\]

就是证据余纤维中的反例 ANCHOR。

---

## 57. Gettier 型结构

Gettier 型状态至少包含：

1. 实际真理：

   \[
   P(a);
   \]

2. 某个被准入的辩护或推理路径；
3. 证据 CUT 的合法余纤维中仍有：

   \[
   \neg P
   \]

   的状态。

所以问题不是“真理和理由都不存在”，而是：

\[
\boxed{
\text{理由没有把证据余量压缩到真理稳定的程度。}
}
\]

---

# 第十二部　时间、记忆、对象与本质

## 58. 时间

离散时间是：

\[
n\mapsto F^n.
\]

连续时间要求 FLOW 半群。

经验时间还需要 ANCHOR 轨迹：

\[
a_n=F^n(a_0),
\]

以及记录 CUT：

\[
q(a_0),q(a_1),q(a_2),\ldots
\]

时间箭头可以来自：

- FLOW 不可逆；
- ADMIT 域单调收缩；
- 记录只追加不删除；
- 余量不可逆丢失；
- 非零 holonomy。

---

## 59. 记忆

给定当前 CUT \(q\) 和 FLOW 族 \(F\)，若：

\[
\ker q
\ne
\ker\widehat q_F,
\]

则当前概念不是 Markov 的。

记忆需求为：

\[
\boxed{
\ker q
\setminus
\ker\widehat q_F.
}
\]

记忆是为了使 FLOW 能够在概念状态上闭合而必须保留的最小额外区别。

---

## 60. 对象与实体

相对于 CUT \(q\)，对象是商类：

\[
[x]_q.
\]

能够历时保持的对象要求 CUT kernel 被 FLOW 保持。

因此实体可定义为：

\[
\boxed{
\text{在相关 FLOW 族下稳定，并对指定行为充分的身份 CUT。}
}
\]

---

## 61. 本质

给定目标行为 \(T\) 与 FLOW 族 \(F\)，本质是：

\[
\boxed{
\operatorname{Core}_F(T)
}
\]

所确定的最小充分动态概念。

所以：

\[
\boxed{
\text{本质不是对象的全部细节，}
}
\]

而是：

\[
\boxed{
\text{为保留指定行为所必需且充分的最小区分。}
}
\]

---

# 第十三部　行动、规范、权利与责任

## 62. 政策能力 `[L]`

给定 CUT：

\[
q:X\to B
\]

和行动类型 \(U\)，可由该 CUT 实现的政策为：

\[
\boxed{
\operatorname{Policy}(q,U)
=
\{\pi:X\to U:
\exists\bar\pi:B\to U,\ 
\pi=\bar\pi\circ q\}.
}
\]

项目已证明，CUT 精化只能扩大可实现政策集合。

所以：

\[
\boxed{
\text{更细概念增加行动能力，}
}
\]

但不自动决定应选择哪个行动。

---

## 63. 闭环主体

给定：

\[
\bar\pi:B\to U,
\]

实际行动：

\[
u_n=\bar\pi(q(a_n)).
\]

下一锚点：

\[
a_{n+1}=F_{u_n}(a_n).
\]

完整闭环为：

\[
\boxed{
a_{n+1}
=
F_{\bar\pi(q(a_n))}(a_n).
}
\]

主体结构至少需要：

- CUT：感知／自我模型；
- FLOW：可执行行动；
- ADMIT：允许的行动和状态；
- ANCHOR：当前实际状态。

---

## 64. 规范不能由纯描述唯一推出

保持相同 CUT、FLOW 和 ANCHOR，可以选择不同 ADMIT doctrine，只要它们均接纳当前锚。

所以：

\[
\boxed{
\text{事实与动力学不唯一决定准入规范。}
}
\]

这不是说规范没有约束，而是说规范前件必须显式进入 ADMIT，而不能暗藏在描述词中。

---

## 65. 权利

消极权利：

\[
\text{禁止某些 FLOW 被实际选择}.
\]

积极权利：

\[
\exists\text{ 被准入的 FLOW，使锚点进入目标域}.
\]

项目已证明，在无可用行动时，所有消极禁止都可能平凡满足，而积极目标仍无法实现。

所以两者不是同一 permission 谓词的否定形式。

---

## 66. 合法性与正确性

合法性审计检查：

\[
\text{执行的 FLOW 是否满足 ADMIT}.
\]

正确性审计检查：

\[
\text{FLOW 后的结果是否等于目标 CUT}.
\]

项目已证明：

\[
\boxed{
\text{授权完全合法}
\not\Rightarrow
\text{事实结果正确}.
}
\]

---

## 67. 责任与道德运气

设：

\[
E:\mathrm{Path}\to\mathrm{Evaluation}
\]

为规范评价，控制—知识 CUT 为：

\[
q_{\mathrm{ck}}:\mathrm{Path}\to C.
\]

若：

\[
E=\overline E\circ q_{\mathrm{ck}},
\]

则评价只依赖控制与知识。

若同一控制—知识纤维内评价不同，则责任下降失败，形成道德运气残差。

---

# 第十四部　社会、语言与权力

## 68. 多观察者

观察者 \(o\) 给出 CUT：

\[
q_o:X\to B_o.
\]

联合观察者：

\[
J(x)(o)=q_o(x).
\]

共同不可区分关系是：

\[
\bigcap_o\ker q_o.
\]

观察者增多会缩小共同余量，但仍可能存在全部观察者共同看不见的盲核。

---

## 69. 承认

多主体承认要求：

- 各自 CUT 可翻译；
- ADMIT 条件兼容；
- ANCHOR 在共同实现像中一致；
- FLOW 翻译图交换。

承认不是宣布所有视角相同，而是证明不同表示能在共同实现中兼容。

---

## 70. 语言

语言至少包含：

\[
\boxed{
\text{语境索引 CUT}
+
\text{能够改变制度状态的言语 FLOW}.
}
\]

词义相同不是字符串相同，而是：

- kernel 结构相同；
- 可回答问题相同；
- FLOW 下的使用规律相容；
- ADMIT doctrine 与 ANCHOR 语境得到运输。

---

## 71. 翻译损失

若粗读数由细读数确定性后处理得到：

\[
q_{\mathrm{coarse}}
=
h\circ q_{\mathrm{fine}},
\]

则粗读数不能减少目标残差。

项目还证明，在有限概率模型中，确定性后处理不能降低目标剩余条件熵。

所以：

\[
\boxed{
\text{翻译或压缩可保持旧信息，但不能无条件创造被丢失的目标区分。}
}
\]

---

## 72. 权力

项目哲学字典定义：

\[
\boxed{
\text{权力}
=
\text{对 CUT、FLOW、ADMIT、ANCHOR 的非对称控制}.
}
\]

分别对应：

- 决定社会怎样分类人；
- 决定哪些过程可以发生；
- 决定谁和什么被接纳；
- 决定哪些事实、证据和历史被视为实际锚。

---

## 73. 意识形态

意识形态可定义为：

\[
\boxed{
\text{内部闭合，但对相关现实 ANCHOR 或目标 CUT 不忠实的概念系统。}
}
\]

它可能：

- 在自身 ADMIT 域内无残差；
- 通过排除反例保持一致；
- 对真实锚点或干预行为失去充分性。

---

# 第十五部　哲学争论的型别诊断

## 74. 争论分类 `[P]`

\[
\boxed{
\begin{aligned}
\text{事实争论}
&=\text{同模型、同 CUT、同 ANCHOR 下取值不同};\\
\text{概念争论}
&=\text{使用不同 CUT};\\
\text{因果争论}
&=\text{使用不同 FLOW 或干预结构};\\
\text{本体争论}
&=\text{使用不同状态类型或 ADMIT};\\
\text{视角争论}
&=\text{使用不同 ANCHOR 或观察者 CUT};\\
\text{规范争论}
&=\text{使用不同 ADMIT doctrine 或价值序};\\
\text{语义含混}
&=\text{无 transport 地切换 CUT};\\
\text{范畴错误}
&=\text{直接比较不同类型上的谓词};\\
\text{实现争论}
&=\text{形式模型是否有现实 ANCHOR};\\
\text{历史解释争论}
&=\text{数学结构与文本 ANCHOR 的对应不同}.
\end{aligned}}
\]

这不是取消哲学争论，而是先判断争论究竟发生在哪一轴。

---

# 第十六部　科学的递归定义动力学

## 75. 科学循环 `[P]`

项目定义：

\[
\mathsf{Science}
=
(
\mathsf{Define},
\mathsf{Observe},
\mathsf{Predict},
\mathsf{Compare},
\mathsf{Revise},
\mathsf{Reflect}
).
\]

其单步形式为：

\[
S_{n+1}
=
\mathsf{Reflect}
\left(
\mathsf{Revise}
\left(
S_n,
\mathsf{Compare}
(
\mathsf{Predict}(S_n,-),
\mathsf{Observe}(w,-)
)
\right)
\right).
\]

---

## 76. 科学循环的四角色展开 `[D]`

\[
\begin{aligned}
\mathsf{Define}
&=\text{提出新的 CUT};\\
\mathsf{Observe}
&=\text{在 ANCHOR 上执行准入 FLOW 并读取 CUT};\\
\mathsf{Predict}
&=\text{由模型 CUT 与 FLOW 生成目标读数};\\
\mathsf{Compare}
&=\text{产生 residual/carry};\\
\mathsf{Revise}
&=\text{改变 CUT、FLOW、ADMIT 或 ANCHOR};\\
\mathsf{Reflect}
&=\text{在阶段类型上执行更高阶 FLOW};\\
\mathsf{Certify}
&=\text{给出证明、误差或反例类型中的 ANCHOR}.
\end{aligned}
\]

因此 `CERTIFY` 和 `REFLECT` 是四角色在更高类型上的复用，不需升级为新的基础原语。

---

## 77. 六种变化分量 `[P]`

项目区分：

\[
\begin{aligned}
\Delta\mathsf{CUT}
&=\text{对象与变量定义变化};\\
\Delta\mathsf{FLOW}
&=\text{动力学定义变化};\\
\Delta\mathsf{ADMIT}
&=\text{模型或轨迹准入变化};\\
\Delta\mathsf{ANCHOR}
&=\text{操作、仪器与记录接口变化};\\
\Delta\mathsf{CERTIFY}
&=\text{证明和误差证书变化};\\
\Delta\mathsf{REFLECT}
&=\text{方法和元方法变化}.
\end{aligned}
\]

前四个改变基础模型；后两个是证明相关和元层变化。

---

## 78. 实验选择

当前目标缺陷：

\[
E(q,T)=\ker q\setminus\ker T.
\]

实验 CUT \(e\) 的捕获集：

\[
\boxed{
G(e\mid q,T)
=
E(q,T)\cap(\ker e)^c.
}
\]

若有质量 \(\nu\) 与成本 \(c\)，可选择：

\[
e^*
\in
\arg\max_e
\frac{\nu(G(e\mid q,T))}{c(e)}.
\]

项目已证明，在有限可加质量条件下，累计捕获函数具有单调性与次模性，即边际收益递减。

所以定义发现可以成为受约束实验设计，而不是只靠语言直觉。

---

# 第十七部　阶段、反射与无终局

## 79. 阶段

定义完整阶段：

\[
\boxed{
\Sigma
=
(X,U,I,B,q,F,A,a,\Gamma,\mathcal Q,L).
}
\]

其中：

- \(q\) 是 CUT 族；
- \(F\) 是 FLOW 族；
- \(A\) 是 ADMIT；
- \(a\) 是 ANCHOR；
- \(\Gamma\) 是当前定义语言；
- \(\mathcal Q\) 是问题域；
- \(L\) 是来源、证明和历史账本。

前四者是 C-IRPT 基础角色；后三者是组织结构。

---

## 80. 反射不是第五原语

令 \(\mathrm{Stage}\) 为阶段类型。

则反射只是：

\[
\boxed{
\mathsf{Reflect}:
\mathrm{Stage}
\to
\mathrm{Stage}.
}
\]

它是以阶段为状态类型的 FLOW。

同样可在阶段空间上定义：

- Meta-CUT：阶段分类；
- Meta-ADMIT：方法论准入；
- Meta-ANCHOR：当前实际且已认证阶段。

因此 C-IRPT 可递归应用于自身，而无需新增“反射本体”。

---

## 81. 诚实阶段扩张 `[L/D/N]`

设新阶段到旧阶段有投影：

\[
p:X'\to X.
\]

若 \(p\) 满射，则项目已证明：

\[
T\text{ 可由 }q\text{ 回答}
\iff
T\circ p\text{ 可由 }q\circ p\text{ 回答}.
\]

若 \(p\) 不满射，拉回后的新域可能仅因看不见旧状态而虚假消除不可回答性。

因此诚实扩张至少要求：

\[
\boxed{
\text{旧准入域上的满覆盖}
}
\]

即：

\[
\forall x,\ A(x)
\Rightarrow
\exists x',\ A'(x')\land p(x')=x.
\]

还应要求：

\[
\begin{aligned}
q\circ p
&=
\pi_B\circ q',\\
p\circ F'_{\iota(u)}
&=
F_u\circ p,\\
A'(x')
&\Rightarrow A(p(x')),\\
p(a')
&=a.
\end{aligned}
\]

---

## 82. 生产性扩张

扩张 \(\Sigma\to\Sigma'\) 是生产性的，当存在新问题：

\[
P'\in\mathcal Q'
\]

使：

\[
P'\in\operatorname{Answerable}(\Sigma')
\]

但：

\[
P'
\notin
p^*\operatorname{Answerable}(\Sigma).
\]

所以新增文件、术语或类型并不自动构成生产性反射；必须出现严格新问题能力。

---

## 83. 局部终局—全局无终局

对固定：

\[
(X,F,T,A,a),
\]

可以存在最小充分动态 CUT：

\[
\operatorname{Core}_F(T).
\]

所以固定任务可真正闭合。

但反射可以改变：

\[
X,\quad F,\quad T,\quad A,\quad a,\quad\mathcal Q.
\]

因此旧任务终点不一定是新任务终点。

最强的开放反射模式是：

\[
\boxed{
\forall\Sigma,\quad
\exists\Sigma^+\succ\Sigma,
}
\]

其中 \(\succ\) 表示诚实且生产性的扩张。

它推出无最大阶段，但该模式不是由四角色无条件推出的定理。

---

# 第十八部　∞ 与道

## 84. ∞ 的派生类型

\[
\begin{aligned}
\infty_{\mathrm{object}}
&:\ X\text{ 是无限类型};\\
\infty_{\mathrm{flow}}
&:\ FLOW\text{ 可任意长迭代};\\
\infty_{\mathrm{cover}}
&:\ \text{没有有限 CUT 族覆盖全部残差};\\
\infty_{\mathrm{model}}
&:\ \text{最小充分模型复杂度无有限上界};\\
\infty_{\mathrm{reflection}}
&:\ \text{阶段序没有最大元}.
\end{aligned}
\]

这些都从四角色与元层结构派生。

所以：

\[
\boxed{
\infty
\text{不是第五原语。}
}
\]

---

## 85. 无限联合仍然是 CUT

对任意索引类型 \(I\) 的 CUT 族：

\[
q_i:X\to B_i,
\]

定义联合 CUT：

\[
J(x)(i)=q_i(x).
\]

其 kernel：

\[
\ker J
=
\bigcap_i\ker q_i.
\]

所以无限多个名字仍然能被总化为一个名字。

同样，一条无限反射链也能在更高元语言中成为一个对象。

因此：

\[
\boxed{
\text{无限不等于不可言说。}
}
\]

---

## 86. 道不进入 C-IRPT 对象语言

本文不定义：

```lean
constant Dao : Type
```

也不定义：

```lean
axiom daoInfinite : Infinite Dao
```

因为一旦这样做，道已经成为一个被 CUT、ADMIT 和断言规定的对象。

C-IRPT 能表达的只是：

\[
\boxed{
\text{某个阶段为何不能仅凭自身取得终极授权。}
}
\]

所以“道不可言说”的形式痕迹不是一个对象，而是元纪律：

\[
\boxed{
\text{不得把任务相对完成偷换成跨所有反射层的终极完成。}
}
\]

---

## 87. “道可道，非常道”的 C-IRPT 解释

此处只作结构解释，不声称是文本训诂同一性。

\[
\boxed{
\begin{aligned}
\text{名}
&=\mathsf{CUT};\\
\text{名下未尽}
&=\mathsf{REMAINDER};\\
\text{变化}
&=\mathsf{FLOW};\\
\text{何者被算作合法}
&=\mathsf{ADMIT};\\
\text{此刻实际者}
&=\mathsf{ANCHOR}.
\end{aligned}}
\]

“无名”不能被表示为常值 CUT，因为常值 CUT 仍是最粗的名字。

“非常名”可解释为：

\[
\boxed{
\text{任何 CUT 都相对于状态域、FLOW、ADMIT 与 ANCHOR。}
}
\]

“非常道”可解释为：

\[
\boxed{
\text{任何被形式化的阶段仍然只是 C-IRPT 中的一个阶段对象。}
}
\]

---

# 第十九部　形式哲学字典

## 88. 四角色派生字典

\[
\boxed{
\begin{aligned}
\textbf{存在}
&=\text{ADMIT 类型中的 ANCHOR};\\
\textbf{概念}
&=\text{规定相对同一性的 CUT};\\
\textbf{现象}
&=\text{ANCHOR 经 CUT 得到的坐标};\\
\textbf{余量}
&=\text{同一 CUT 坐标下的依赖纤维};\\
\textbf{形式}
&=\text{CUT 坐标};\\
\textbf{质料}
&=\text{坐标下的实现余纤维};\\
\textbf{实体}
&=\text{在相关 FLOW 下稳定的身份 CUT};\\
\textbf{偶性变化}
&=\text{身份 CUT 保持而性质 CUT 改变};\\
\textbf{本质}
&=\text{保留指定 FLOW 行为的最小充分 CUT};\\
\textbf{真理}
&=\text{命题在 ANCHOR 上成立};\\
\textbf{知识}
&=\text{真理在合法证据余纤维上稳定};\\
\textbf{怀疑}
&=\text{同一证据纤维存在反例 ANCHOR};\\
\textbf{因果缺口}
&=\text{余量穿过 FLOW 变成未来 CUT 差异};\\
\textbf{记忆}
&=\text{关闭 FLOW carry 所需的最小 CUT 精化};\\
\textbf{时间}
&=\text{FLOW 迭代与 ANCHOR 记录的有序结构};\\
\textbf{主体}
&=\text{带 ADMIT 与 ANCHOR 的观察 CUT/FLOW 闭环};\\
\textbf{自由}
&=\text{被 ADMIT 的政策可选性、控制与分支结构};\\
\textbf{规范}
&=\text{不能由纯 CUT/FLOW 唯一推出的 ADMIT doctrine};\\
\textbf{责任}
&=\text{评价向控制—知识 CUT 的下降};\\
\textbf{道德运气}
&=\text{该下降的失败};\\
\textbf{正义}
&=\text{ADMIT 对道德无关 CUT 差异的不变性};\\
\textbf{权力}
&=\text{对 CUT、FLOW、ADMIT、ANCHOR 的非对称控制};\\
\textbf{意识形态}
&=\text{内部闭合但对相关 ANCHOR 不忠实的系统};\\
\textbf{承认}
&=\text{多观察者在共同实现中的相容};\\
\textbf{语言}
&=\text{语境 CUT 与言语 FLOW};\\
\textbf{解释}
&=\text{目标充分、结构明确且复杂度受控的下降};\\
\textbf{辩证法}
&=\text{由显式 carry/residual 强制出的最小修复};\\
\textbf{对角边界}
&=\text{自表示目录经固定点自由 twist 的逃逸审计}.
\end{aligned}}
\]

---

# 第二十部　项目本身作为 C-IRPT 系统

## 89. 仓库角色对应

\[
\begin{aligned}
\mathsf{CUT}
&=\text{statement identity、GID、目标陈述与分类接口};\\
\mathsf{FLOW}
&=\text{formalize、deposit、dependency、freeze、retract、migrate};\\
\mathsf{ADMIT}
&=\text{elaboration、依赖闭包、治理 gate 与冻结准入};\\
\mathsf{ANCHOR}
&=\text{proof term、反例、收据、commit 与实际仓库状态}.
\end{aligned}
\]

`residual-open` 是尚未闭合的目标余量。

`coverage edge` 不是笼统“存在证明”，而是：

\[
\boxed{
\text{哪个正式声明覆盖哪个精确目标陈述}.
}
\]

---

## 90. 最终 theorem set 不等于完整研究状态

两个仓库可以拥有相同结论集合，却具有不同：

- 依赖图；
- 证明历史；
- 反例路径；
- 覆盖边；
- 成本；
- 可复用引理；
- 后续研究能力。

所以 append-only ledger 是历史 ANCHOR，而不是冗余日志。

这与“同端点而历史评价不同，评价不能约为端点函数”的 Lean 定理一致。

---

# 第二十一部　Lean 重构路线：只做适配，不造影子 API

## 91. 复用原则

禁止重新定义已有：

- `Concept`;
- `ConceptFiber`;
- `Refines`;
- `conceptJoin`;
- `jointReadout`;
- `ObserverStructure`;
- `controlledBehavior`;
- `DynClosure`;
- `defectRelation`;
- `empiricalSetoid`;
- `TargetClosure`;
- `blindResidual`.

新增工作只应：

1. 组合既有接口；
2. 证明四角色之间的新桥梁；
3. 暴露新的普适性质；
4. 给出有限反模型；
5. 建立 proof-status 审计。

---

## 92. 最小适配文件

```text
D5/S3/ConceptDynamics/CIRPT/
  SystemAdapter.lean
  FiberNormalForm.lean
  FlowFiberNormalForm.lean
  AdmitFiberBoundary.lean
  AnchorShadow.lean
  FourRoleDefectVector.lean
  FourRoleAdequacy.lean
  HonestStageExtension.lean
  ProductiveReflection.lean
  PairwiseCurvature.lean
```

---

## 93. 建议定理清单

### 可直接形式化 `[D→L]`

1. `flow_descent_iff_visible_coordinate_independent_of_remainder`
2. `carry_witness_iff_one_source_fiber_hits_two_target_fibers`
3. `admit_lower_subset_original_subset_upper`
4. `admit_descends_iff_boundary_empty`
5. `anchor_shadow_empty_iff_anchor_fiber_subsingleton`
6. `all_anchor_shadows_empty_iff_injective`
7. `section_carry_cocycle`
8. `section_change_adds_coboundary`
9. `four_role_independence_boolean_models`
10. `four_role_adequacy_iff_four_defects_empty`
11. `static_cut_updates_commute`
12. `certification_is_anchor_on_claim_type`
13. `reflection_is_flow_on_stage_type`
14. `admitted_surjective_extension_reflects_answerability`

### 需要新接口 `[N]`

15. `CIRPTSystem`
16. `FourRoleDefectVector`
17. `PairwiseCompatibilityMatrix`
18. `CIRPTStageMorphism`
19. `HonestExtension`
20. `ProductiveExtension`

### 开放桥梁 `[O]`

21. 从更基础条件推出“每个阶段都有生产性反射后继”；
22. 将一般 C-IRPT 曲率与具体物理可测量量对应；
23. 将 prime-memory 代数曲率与 Zeta 零点机制建立非定义式解析桥；
24. 将 RH 的离线零点构造成显式 naming-congruence defect；
25. 建立现实科学语义中的 `Realizable` 与经验实现之间的正式桥梁。

---

# 第二十二部　严格非主张

本文不声称：

1. CUT、FLOW、ADMIT、ANCHOR 是新的逻辑公理；
2. 定义一个对象类型即可证明对象存在；
3. 形式逆极限必有现实实现；
4. 一个 ANCHOR 足以证明全称规律；
5. 受限 ADMIT 域中的零残差推出全域真理；
6. 静态信息逃逸就是曲率；
7. 无限数据自动消除共同盲核；
8. 对角语法逃逸自动产生世界语义；
9. 信息完备自动产生唯一规范；
10. 观察完成自动产生干预或反事实完成；
11. 反射链存在自动等于道；
12. prime-memory 曲率已经证明 RH；
13. 抽象 naming stability 已经补齐 Zeta 解析桥；
14. 形式化哲学重构与历史哲学文本完全同一。

---

# 第二十三部　最终统一

## 94. 四角色主式

\[
\boxed{
\mathfrak M
=
(
\mathsf{CUT},
\mathsf{FLOW},
\mathsf{ADMIT},
\mathsf{ANCHOR}
).
}
\]

其依赖纤维正规形为：

\[
\boxed{
X
\simeq
\sum_{b:B}R_q(b).
}
\]

其中：

\[
\begin{aligned}
\mathsf{CUT}
&:\ (b,r)\mapsto b;\\
\mathsf{FLOW}
&:\ (b,r)\mapsto(\beta(b,r),\rho(b,r));\\
\mathsf{ADMIT}
&:\ A^\sharp(b,r);\\
\mathsf{ANCHOR}
&:\ (b_a,r_a,A^\sharp(b_a,r_a)).
\end{aligned}
\]

---

## 95. 四角色动力学主式

\[
\boxed{
\Sigma_{n+1}
=
\mathsf{Reflect}
\circ
\mathsf{Revise}_{\Delta\mathsf C,\Delta\mathsf F,
\Delta\mathsf A,\Delta\mathsf H}
\left(
\Sigma_n,
\operatorname{Residual}_n
\right).
}
\]

其中：

- `Reflect` 是阶段空间上的 FLOW；
- `Revise` 改变四角色；
- `Residual` 是失败下降的见证；
- `Certify` 是 proof/counterexample 类型中的 ANCHOR。

---

## 96. 最深的三个结论

第一：

\[
\boxed{
\text{对象不是最小原语；对象是 CUT 纤维的商类。}
}
\]

第二：

\[
\boxed{
\text{曲率不是余量；曲率是 CUT、FLOW、ADMIT、ANCHOR 的更新不交换。}
}
\]

第三：

\[
\boxed{
\text{无终局不是每个固定任务都无法完成，}
}
\]

而是：

\[
\boxed{
\text{任何任务完成都不能预先垄断反射后才出现的新类型、新 FLOW、新 ADMIT 与新 ANCHOR。}
}
\]

---

## 97. 道与本理论的最终边界

\[
\boxed{
\text{道不作为 CUT 的目标值、FLOW 的极限、ADMIT 的最终谓词或 ANCHOR 的最大对象进入理论。}
}
\]

C-IRPT 所能严格表达的是：

\[
\boxed{
\text{每一个被说出的体系，都必须公开它如何 CUT、如何 FLOW、准入什么、锚定于何处。}
}
\]

以及：

\[
\boxed{
\text{任何“完成”都必须说明：完成的是哪个目标、哪个过程族、哪个准入域和哪些锚点。}
}
\]

最终压缩为：

\[
\boxed{
\text{CUT 给出名，REMAINDER 给出未尽；}
}
\]

\[
\boxed{
\text{FLOW 给出变化，ADMIT 给出合法边界；}
}
\]

\[
\boxed{
\text{ANCHOR 给出实际，而反射只是四者在更高类型上的再次展开。}
}
\]

---

# 项目复用锚点

本重构直接依赖或建议复用以下既有路径：

```text
docs/develop/theory/QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md
docs/develop/theory/FORMAL_CONCEPT_DYNAMICS.md
docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md

D5/S3/ConceptDynamics/ConceptFiberDecomposition.lean
D5/S3/ConceptDynamics/ConceptJoinUniversal.lean
D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality.lean
D5/S3/ConceptDynamics/Fibers/ObserverConceptReadoutCorrespondence.lean
D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean
D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean
D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois.lean
D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction.lean
D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency.lean
D5/S3/ConceptDynamics/Audits/DomainImmunizationAudit.lean
D5/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability.lean
D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction.lean
D5/S3/ConceptDynamics/PolicyCapabilityMonotonicity.lean
D5/S3/ConceptDynamics/Decision/MixedFiberZeroErrorImpossible.lean
D5/S3/ConceptDynamics/Causal/FiniteCausalQueryHierarchy.lean
D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture.lean

D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean
D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature.lean
D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.lean
D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence.lean
```

---

# 增补 RK：秩准入改变最小观察深度

本增补把第28节的动态概念核、第34节的域变化边界和第59节的记忆需求落实到同一个固定学习任务。任务始终是固定 X=I_q、Y=0、损失 ||VU||_F²/2 的同步梯度下降，没有重置、标签干预或自由梯度。

## RK.1 模型、实际像与一步读数

设 U 为 m×q 实矩阵，V 为 q×m 实矩阵，W=VU，A=UᵀU，B=VVᵀ。外部 Gram 状态为

$$\Gamma=\begin{pmatrix}A&W^T\\W&B\end{pmatrix}\succeq0,\qquad \operatorname{rank}\Gamma\le m.$$

反向每个满足这两个条件的矩阵都能因子化为真实 U,V。给定非零步长 h，实际输出更新为

$$W^+=W-h(BW+WA)+h^2WW^TW.$$

其余两块更新为

$$A^+=A-2hW^TW+h^2W^TBW,\qquad B^+=B-2hWW^T+h^2WAW^T.$$

这些由原始同步参数更新直接展开，是既有前置。所有结果区分完整参数与 Gram 状态；共同隐藏行的正交换基保持 Gram，因而仍不由本任务识别。

先固定可逆 W_0，其奇异值为互异正数 σ_i。在一套固定的左右奇异向量坐标中写 W_0=Σ=diag(σ_i)，后续全部读数也使用这同一坐标。由 W_0,W_1,h 可以计算

$$L=\frac{\Sigma-W_1}{h}+h\Sigma^3=B\Sigma+\Sigma A.$$

令 s_i=L_ii/σ_i。对 i≠j，读数唯一确定

$$\alpha_{ij}=A_{ij}=\frac{\sigma_iL_{ij}-\sigma_jL_{ji}}{\sigma_i^2-\sigma_j^2},\qquad
\beta_{ij}=B_{ij}=\frac{\sigma_iL_{ji}-\sigma_jL_{ij}}{\sigma_i^2-\sigma_j^2}.$$

令 α_ii=β_ii=0。唯一尚未确定的是 a_i=A_ii，且 B_ii=s_i-a_i。上述等式来自两个对称条目构成的二元线性方程，不预先输入任何隐藏对角数值。

## RK.2 最小宽度的一步纤维至多有 2^q 个实际状态

**假设。** 竞争模型都满足已知宽度 m=q，等价地，在可逆 W_0 下竞争 Gram 的秩为 q。不能只假定真实模型窄，却允许竞争模型任意宽。

**定理 RK1。** 对任意 q≥1、任意相容读数 W_0,W_1，全部实际初始 Gram 候选至多有 2^q 个。每个候选的 a_i 必须满足显式二次方程

$$\boxed{a_i^2-s_i a_i+c_i=0,\qquad
c_i=\sigma_i^2-\sigma_i\sum_{j\ne i}\frac{\alpha_{ij}\beta_{ij}}{\sigma_j}.}\tag{RK1}$$

从这些二次根构造 A=α+diag(a_i)、B=β+diag(s_i-a_i)，再检验

$$A\succ0,\qquad A\Sigma^{-1}B=\Sigma\tag{RK2}$$

得到恰好全部实际候选。因此这是完整可行集描述，而非仅必要条件。

**证明。** W_0 可逆且 m=q，故 U,V 可逆，A 正定，并有 B=ΣA^{-1}Σ。等价地 AΣ^{-1}B=Σ。取第 i 个对角条目，得到

$$a_i(s_i-a_i)/\sigma_i+\sum_{j\ne i}\alpha_{ij}\beta_{ij}/\sigma_j=\sigma_i,$$

即(RK1)。每个首一二次多项式最多有两个实根，q 个对角参数最多给出 2^q 个选择。非对角元及 B 的对角元已经由读数确定，所以不会产生额外连续自由度。

反向满足(RK2)时，B=ΣA^{-1}Σ，构造 U=A^{1/2}、V=ΣA^{-1/2}，便有 UᵀU=A、VVᵀ=B、VU=Σ。恢复公式同时保证 BΣ+ΣA=L，故实际第一步输出正是给定 W_1。证毕。

**尖锐性及永久歧义。** 固定任意互异正 σ_i，令 A、B 对角，并在每个坐标独立选择

$$(A_{ii},B_{ii})=(4\sigma_i,\sigma_i/4)\quad\text{或}\quad(\sigma_i/4,4\sigma_i).$$

这给出 2^q 个不同的秩 q 实际 Gram，它们有相同 W_0 和 s_i=17σ_i/4，所以 W_1 相同。对角性沿更新保持，每个坐标仅使用

$$w^+=(1+h^2w^2)w-hws,\qquad s^+=(1+h^2w^2)s-4hw^2.$$

因此对于任意共同的后续步长序列，这 2^q 个状态的全部输出未来仍相同。有限时刻候选界在这个族上精确达到，并不是靠更多时间总能排除的假候选。

## RK.3 可由数据检查的唯一性条件及显式恢复

对 i≠j 定义完全由读数计算的

$$k_{ij}=-\frac{\alpha_{ij}s_j}{\sigma_j}-
\sum_{\ell\notin\{i,j\}}\frac{\alpha_{i\ell}\beta_{\ell j}}{\sigma_\ell}.$$

**定理 RK3。** 若每个顶点 i 都存在 j≠i 满足

$$\boxed{\beta_{ij}^2\ne\alpha_{ij}^2,}\tag{RK3}$$

则 W_0,W_1 唯一确定全部初始 Gram，且

$$\boxed{
A_{ii}=\sigma_i\frac{\beta_{ij}k_{ij}+\alpha_{ij}k_{ji}}
{\beta_{ij}^2-\alpha_{ij}^2},\qquad B_{ii}=s_i-A_{ii}.
}\tag{RK4}$$

不同可用 j 得到同一真实值。无需枚举 2^q 个二次根。

**证明。** 令 t_i=a_i/σ_i。矩阵方程 AΣ^{-1}B=Σ 的两个非对角条目给出

$$\beta_{ij}t_i-\alpha_{ij}t_j=k_{ij},\qquad
-\alpha_{ij}t_i+\beta_{ij}t_j=k_{ji}.$$

系数行列式为 β_ij²-α_ij²，由(RK3)非零，所以解出(RK4)。每个 i 都有可用边，故所有对角元被确定。原数据相容，真实解存在；这证明唯一性。证毕。

(RK3)是观测到的精确非零性，不是对全部问题实例施加一个隐藏耦合正下界。失败时仍用 RK1 的完整有限候选描述；接近零时恢复会病态，不能宣称统一噪声稳定性。

**一般位置定理 RK4。** 对每个 q≥2 和每个固定简单可逆 W_0，按 A≻0、B=ΣA^{-1}Σ 参数化最小宽度实际状态。在 A 的对称矩阵坐标中，除一个真代数零集外，全部 i≠j 都满足(RK3)，因此一个被动训练步足够。这个成功集合开、稠密且具有满 Lebesgue 测度。零步不够，故一般位置下最小深度为一。

**证明。** 对每对 i<j，坏条件等价于多项式

$$P_{ij}(A)=(A_{ij}\det A)^2-
\sigma_i^2\sigma_j^2(\operatorname{adj}A)_{ij}^2=0.$$

这些多项式不是恒零。统一构造 λ>max_i σ_i、t>0、A=λI+t\mathbf1\mathbf1ᵀ。则

$$A^{-1}=\lambda^{-1}I-
\frac{t}{\lambda(\lambda+qt)}\mathbf1\mathbf1^T,$$

故 i≠j 时 α_ij=t、β_ij=-tσ_iσ_j/[λ(λ+qt)]，并有 |β_ij|<|α_ij|。因此有限乘积 ∏_{i<j}P_ij 非零。非零实多项式的零集无内点且测度为零，限制到正定开集得到结论。零步时固定 W_0 而任取不同 A≻0 都给合法 Gram，故不能识别。证毕。

**微分接口。** 连续零标签梯度流的初始输出速度是 Wdot_0=-L。因此在相同最小宽度先验下，(W_0,Wdot_0) 也满足同一一般位置识别结论。此前连续流的 c·diag(I,-I) 盲方向通常不留在这个秩 q 实际域中。不能把不同秩先验下的结论混为矛盾。

## RK.4 全秩 Gram 的一般位置最小深度为三

**定理 RK5。** 对每个 q≥2、每组三个固定正步长 h_0,h_1,h_2，以及已知允许宽度 m≥2q，存在对称矩阵空间中的一个真代数集合 Z，使每个 Γ_0≻0 且 Γ_0∉Z 的实际状态都满足：W_0,W_1,W_2,W_3 唯一识别初始 Gram，而 W_0,W_1,W_2 不足。成功集合在正定域开、稠密且满测度。

**共同传播观察算子。** 对读数 W_0,...,W_3，置

$$H(W)=\begin{pmatrix}0&W^T\\W&0\end{pmatrix},\quad
P_0=I,\quad P_{n+1}=(I-h_nH(W_n))P_n,$$

$$\mathcal O_W(X)=\big((P_nXP_n^T)_{21}\big)_{n=0}^3.$$

该算子在线性空间 Sym_(2q) 上定义。相同精确输出的竞争初态 X 必须满足 O_W(X)=W；反向，半正定且满足宽度秩约束的 X 若满足这些线性等式，用真实参数更新归纳，就恰好产生同一输出前缀。这里没有把数据依赖的传播矩阵当作另一个自由模型。

**识别判据的自包含证明。** 在 W_0 的简单正奇异坐标 Σ 中，相同 W_1 使初态差成为 diag(x_i)、-diag(x_i)：两个对称条目的系数行列式是 σ_j²-σ_i²。首步后的差为 D_x=diag((1-h_0²σ_i²)x_i) 及 -D_x。相同 W_2 等价于 D_xW_1-W_1D_x=0。若 W_1 的非对角连接图连通，且所有 d_i=1-h_0²σ_i² 非零，则 D_x=cI，初态差只剩

$$c\operatorname{diag}(K,-K),\qquad K=\operatorname{diag}(d_i^{-1}).$$

第三步差精确等于

$$c h_1^2h_2S,\qquad S=W_2W_1^TW_1-W_1W_1^TW_2.$$

所以 S≠0 时 O_W 在整个对称矩阵空间上单射。该证明只用差方程，亦适用于非正的线性扰动。

**所有维数的非零构造。** 固定 D=diag(1,...,q)、λ=q+1、A_*=λI+\mathbf1\mathbf1ᵀ、B_*=λI、W_*=D，并令 Γ_s=sΓ_*，s>0。Γ_*正定，因为 [[λI,D],[D,λI]] 已正定，另加左上正半定块。首步的非对角条目恰为

$$(W_1(s))_{ij}=-h_0s^2 i\quad(i\ne j),$$

故其连接图完整。初始奇异值为 s,2s,...,qs；足够小 s 使全部 d_i 非零。

令 L_1=B_1W_1+W_1A_1。由更新有 S=h_1(W_1W_1ᵀL_1-L_1W_1ᵀW_1)。按 s 的多项式展开，W_1=sD+O(s²)、L_1=s²(B_*D+DA_*)+O(s³)，所以

$$\boxed{S_{12}(s)=-3h_1s^4+O(s^5).}\tag{RK5}$$

这里 O(s⁵) 只是有限多项式更高次数项的缩写；四次系数由 (D²L_*-L_*D²)_12=-3 精确给出。因此足够小的正 s 有 S≠0，构成每个 q 下真实正定且可识别的见证。无需搜索更高维数的数值实例。

**一般位置证明。** 令 n=dim Sym_(2q)=q(2q+1)。在固定对称基下，O_W 的矩阵条目是初始 Γ 的多项式，因为三次实际更新和有限传播乘积都是多项式运算。令 P_obs 为其全部 n×n 子式平方之和。上述全维度见证使 P_obs≠0，所以该多项式不是恒零。再把 det(W_0)、W_0ᵀW_0 的判别式和 det(I-h_0²W_0ᵀW_0) 的零集加入 Z；它们在同一见证上都非零。于是 Z 是真代数集合，之外 O_W 单射且初始谱与非共振条件成立。

**两步下界。** 对这样的任一 Γ_0≻0，上述 c·diag(K,-K) 对足够小的非零 c 仍给正定矩阵，并保持 W_0,W_1,W_2。它们的秩为2q，m≥2q保证全部具有真实参数实现。所以两个被动步不够，第三步足够。证毕。

一般位置是明确的代数/测度断言，不等于任意分布上随机初始化必然成功，也不等于存在统一稳定逆。中间宽度 q<m<2q 的精确最小深度未由本定理确定。

## RK.5 四步才够的正定反例

不能把 RK5 改成不带例外的“三步总够”。取 q=2、m≥4、共同步长 h=1/4，

$$W_0=\operatorname{diag}(1,2),\quad
A_0=\begin{pmatrix}17/8&1/2\\1/2&5/2\end{pmatrix},\quad
B_0=\begin{pmatrix}17/8&-1/2\\-1/2&5/2\end{pmatrix}.$$

Γ_0 的顺序主子式为17/8、81/16、1057/128、1617/256，故严格正定。实际更新得到

$$W_1=\begin{pmatrix}0&1/8\\-1/8&0\end{pmatrix},\quad
W_2=\begin{pmatrix}-7/256&287/8192\\-287/8192&7/256\end{pmatrix}.$$

初始奇异值简单，首步非共振，W_1 连接图连通。但 W_1ᵀW_1=W_1W_1ᵀ=I/64，故第三步检测矩阵 S=0。

前两个训练步留下的全部初始方向为 c·diag(K,-K)，K=diag(16/15,4/3)。足够小 c 给不同的正定真实初态。时刻1差为cJ，时刻2差为c(1023/1024)J，因此时刻3输出仍相同。再计算

$$S_*=W_3W_2^TW_2-W_2W_2^TW_3
=-\frac{1165302369}{70368744177664}
\begin{pmatrix}0&1\\1&0\end{pmatrix}\ne0.$$

第四步输出差是

$$c\frac{1023}{1024}\frac1{64}S_*.$$

所以四步区分全部剩余初态，而三个步无法区分。此例中最小训练深度恰为四。计算只是固定有理矩阵的乘法；其非零性和正定性都可逐式复核。

## RK.6 共同状态接口的含义

这些定理保持同一个 FLOW（固定学习更新）和同一个 CUT（输出轨迹），只改变允许初态的秩谓词：已知秩q时，一步一般位置下足够；允许正定秩2q时，一般位置下恰需三步；例外可以恰需四步或永久不可识别。这是 ADMIT 与观察纤维相互作用的具体数学实例。

本节没有从数学 Gram 的密度矩阵归一化推导一般量子物理等价。量子滤波若要实现相同操作，仍需保留成功概率、尺度、制备和可执行读数。本节也没有把精确可识别性转换成未经证明的有噪声学习算法或一般神经网络结论。

## RK.7 文献与适用范围

精确 Gram 更新与离散二次修正属于已有工具；[Holzmüller–Steinwart](../../../Library/Dynamics/holzmueller2020training.md) 附录C命题C.2给出最近的精确离散合同递推先例。该文的三分量代理不是这里的固定输出观察纤维，也不蕴含本文的最小深度分类。

非零实多项式零集的测度事实可由对变量数归纳与Fubini证明：除系数全部为零的低维零集外，每条一维切片仅有有限根。因此上述一般位置证明不依赖未给出的数值概率假设。

RK.4 的所有维数结论由其非零多项式构造承担；RK.5 的固定有理矩阵只给出 q=2 的校准实例，不替代 RK.4 的全称论证。

---

# 增补 IR：中间秩的端点规则、不可辨识骨架与稳定性边界

本增补延续 RK 的同一个任务：固定输入 `X=I_q`、标签 `Y=0`、损失 `||VU||_F²/2`，同步梯度下降，已知非零步长，读取完整输出矩阵。竞争模型也遵守已知隐藏宽度上界 `m`。主要问题是 `q<m<2q` 时两个训练步后全部相容初态的精确结构。单一秩数字不能决定每个初态的最短识别历史。

## IR.1 观察图给出真实的不变分块

令 `A=UᵀU`、`B=VVᵀ`、`W=VU`，实际 Gram 为

$$\Gamma=\begin{pmatrix}A&W^T\\W&B\end{pmatrix}\succeq0,
\qquad\operatorname{rank}\Gamma\le m.$$

其同步更新为

$$\begin{aligned}
A^+&=A-2hW^TW+h^2W^TBW,\\
B^+&=B-2hWW^T+h^2WAW^T,\\
W^+&=W-h(BW+WA)+h^2WW^TW.
\end{aligned}\tag{IR.1}$$

固定 `W_0` 的一套奇异向量坐标，使 `W_0=Σ=diag(σ_i)`，其中 `σ_i>0`、平方两两不同。只在本增补的两步纤维分类中要求首步非共振

$$d_i=1-h_0^2\sigma_i^2\ne0.$$

在指标集上定义无向图：`i≠j` 有边，当且仅当 `(W_1)_{ij}` 或 `(W_1)_{ji}` 非零。令连通分量为 `C_1,...,C_r`，大小为 `q_1,...,q_r`。

**定理 IR1。** 在这个图的不同连通分量之间，初始 `A,B,W_0` 的交叉条目全为零。所有后续真实更新保持同一分块。给定相容的精确 `W_0,W_1,W_2`，全部对称初始矩阵解在分组坐标中为

$$\boxed{\Gamma(c)=\bigoplus_{a=1}^r M_a(c_a),\qquad
M_a(c_a)=M_{a,0}+c_aJ_a,\qquad
J_a=\operatorname{diag}(K_a,-K_a),\quad
K_a=\operatorname{diag}_{i\in C_a}(d_i^{-1}).}\tag{IR.2}$$

其中代表 `M_{a,0}` 可以由线性读数约束选取，不要求代表本身半正定。每个 `J_a` 都可逆，正负惯性指数均为 `q_a`。

**证明。** 对 `i≠j`，首步条目为

$$ (W_1)_{ij}=-h_0(B_{ij}\sigma_j+\sigma_iA_{ij}),\qquad
(W_1)_{ji}=-h_0(B_{ij}\sigma_i+\sigma_jA_{ij}).$$

两个系数方程的行列式为 `σ_j²-σ_i²≠0`，故两输出条目同时为零当且仅当 `A_{ij}=B_{ij}=0`。跨图分量没有边，得到真实分块；式(IR.1)的乘法、加法和转置保持分块，故它一直不变。

若两个初态给出同一首步输出，用相同二元方程知其差只能为 `ΔA=diag(x_i)`、`ΔB=-diag(x_i)`。首步后差为 `D=diag(d_i x_i)` 和 `-D`。第二步读数相同当且仅当 `DW_1-W_1D=0`，即每条图边的两个 `d_i x_i` 相等。这恰使每个连通分量上有一个独立常数 `c_a`。反向这些差逐步保持前两步输出相同，得到全体解。证毕。

这个图没有在未来自动补回已经缺失的跨块作用。其连通性是当前指定模型中真实耦合是否分块的精确读数。

## IR.2 中间秩的两端点定理

先陈述所需的有限维几何事实。令

$$M(c)=M_0+cJ\quad(c\in\mathbb R),$$

其中 `M_0,J` 为实对称 `n×n` 矩阵，`J` 可逆且同时有正、负特征值。假设半正定参数集合 `I={c:M(c)≽0}` 非空。

**定理 IR2。** `I` 是有界闭区间，可以退化为单点。若 `I=[a,b]`、`a<b`，则每个 `a<c<b` 都给出正定矩阵，而两个端点都奇异。因此，对任意 `m<n`，

$$\boxed{\{c:M(c)\succeq0,\ \operatorname{rank}M(c)\le m\}
\subseteq\{a,b\}.}\tag{IR.3}$$

若 `I` 是单点，只需检验该点的秩。这给出至多两个实际低秩候选。

**证明。** 半正定锥闭且凸，故 `I` 闭且凸。取 `u^TJu>0` 和 `v^TJv<0` 的向量，半正定性分别给参数一个下界和一个上界，故 `I` 有界。

对不同可行参数 `a,b`，记 `P=M(a)`、`Q=M(b)`。如果向量同时属于 `ker P` 与 `ker Q`，则 `(b-a)Jx=0`；因 `J` 可逆，只有零向量。

对 `0<t<1`，若 `x^T[(1-t)P+tQ]x=0`，两项均非负，所以 `x^TPx=x^TQx=0`。对半正定矩阵，零二次型蕴含相应矩阵乘积为零，这可由正交谱分解直接得到。因此 `x` 属于两个核的交，只能为零。所有内点矩阵正定。若区间端点也正定，正定性的开性使其外侧足够近的点仍可行，矛盾。证毕。

**中间宽度推论。** 在 IR1 的连通情形，设 `q<m<2q`。只要精确前缀来自合法模型，其两个训练步后的实际初始 Gram 候选数就恰为一个或两个。此处没有要求第三步检测量非零，也没有假定隐藏耦合或正特征值具有统一下界。

## IR.3 端点的可计算秩判据

**定理 IR3。** 在 IR2 的非退化区间中，取任何可行内点 `c_0`，令

$$P=M(c_0)\succ0,\qquad R=P^{-1/2}JP^{-1/2}.$$

记 `μ_+>0`、`μ_-<0` 为 `R` 的最大和最小特征值，重数分别为 `k_+、k_-`。则

$$\boxed{a=c_0-1/\mu_+,\qquad b=c_0-1/\mu_-,
\qquad\operatorname{rank}M(a)=n-k_+,\quad
\operatorname{rank}M(b)=n-k_-.}\tag{IR.4}$$

因此宽度上界 `m<n` 保留左端点恰当且仅当 `k_+≥n-m`，保留右端点恰当且仅当 `k_-≥n-m`。这在重特征值处仍成立；重数是要读取的条件，不能预先假设为一。

**证明。** 作可逆合同变换，

$$M(c)=P^{1/2}\bigl[I+(c-c_0)R\bigr]P^{1/2}.$$

半正定性等价于对每个特征值 `μ` 都有 `1+(c-c_0)μ≥0`。同时取所有正负约束即得两个端点。端点处恰有相应极端特征值的特征空间变为核，合同变换保持秩。证毕。

若数据为有理或实代数数，也可以直接隔离 `det(M_0+cJ)` 的实根，逐个检验半正定性和秩。该多项式次数为 `n`，因为首项系数 `det J≠0`；低秩候选全部在其根中。无需在连续参数上穷举。这里给出的是精确判定算法，没有把浮点特征值估计当作重数证书。

**单点判据。** 设 `M(0)=Γ≽0` 且奇异，`J` 可逆且不定。则 `I={0}` 当且仅当 `J` 在 `ker Γ` 上的限制二次型既不是正定，也不是负定。

**证明。** 限制不定或奇异时存在非零 `z∈ker Γ` 使 `z^TJz=0`。若某个 `c≠0` 可行，则 `z^TM(c)z=0`，半正定性使 `M(c)z=0`。于是 `cJz=0`，矛盾。

反向，若限制正定，按 `ran Γ⊕ker Γ` 写块矩阵。右下块为 `cJ_{22}≻0`；其 Schur 补为 `Γ_{11}+c(J_{11}-J_{12}J_{22}^{-1}J_{21})`，对足够小 `c>0` 正定。所以非零可行参数存在。负定情形取 `c<0`。证毕。

## IR.4 断连情况下的完整秩预算

对 IR1 每个分量令 `I_a={c_a:M_a(c_a)≽0}`。相容性保证这些区间非空。每个非退化区间的内点秩恰为 `2q_a`；端点秩由 IR3 给出；单点区间只有一个固定秩。

**定理 IR4。** 两个训练步后，给定宽度上界 `m` 的全体实际初态恰为

$$\boxed{\left\{\bigoplus_a M_a(c_a):
c_a\in I_a,\quad \sum_a\operatorname{rank}M_a(c_a)\le m\right\}.}\tag{IR.5}$$

这个集合可以按每个分量的“左端点、内区间、右端点”分解为有限个直积片，再用各片的常数秩和筛选。区间内的连续自由度不能被误计为有限候选。

**证明。** IR1 给出完整线性前缀纤维。分块矩阵半正定当且仅当每块半正定，秩等于块秩和，故必要性成立。反向，每个被保留的矩阵都半正定且秩不超过 `m`，因子分解成不超过 `m` 行的真实 `Z=[U,V^T]`，不足补零。IR1 的逆向差关系保证它确实生成同一前缀。证毕。

所以“至多两个”需要连通或单块假设。对一般断连系统，中间秩的两步纤维可能包含连续族；式(IR.5)保留全部这些情形。

## IR.5 完全解耦时：所有未来相同的立方体骨架

**定理 IR5。** 固定互异正数 `σ_i`、`W_0=diag(σ_i)`，并给定对角首步输出，使读得的 `s_i=A_{ii}+B_{ii}` 满足 `s_i>2σ_i`。设已知宽度上界为 `m=q+s`，`0≤s≤q`。则与全部无限未来输出相容的初始 Gram 集，在逐坐标仿射换码后，精确等于 `q` 维立方体的 `s` 维骨架：所有维数不超过 `s` 的面之并。

恰好秩为 `q+d` 的部分由

$$\boxed{2^{q-d}\binom qd}\tag{IR.6}$$

个互不相交的 `d` 维开面组成。特别地，`s=0` 给出 `2^q` 个候选；任意 `0<s<q` 都有正维连续的永久歧义。

**证明。** 首步输出为对角，加上简单初始谱，IR1 的二元方程迫使所有候选的 `A,B` 都对角。每个 `a_i=A_{ii}` 的半正定约束为

$$a_i(s_i-a_i)\ge\sigma_i^2,\qquad
\ell_i\le a_i\le u_i,\quad
\ell_i,u_i=\frac{s_i\mp\sqrt{s_i^2-4\sigma_i^2}}2.$$

单个 `2×2` 块在区间端点秩为一，在内部秩为二。所以总秩等于 `q` 加内部坐标数，宽度上界恰好允许至多 `s` 个内部坐标。每选 `d` 个内部坐标，其余各有两个端点，得式(IR.6)。

逐坐标真实更新只依赖 `(w_i,s_i)`：

$$w_i^+=(1+h^2w_i^2)w_i-hw_i s_i,
\qquad s_i^+=(1+h^2w_i^2)s_i-4hw_i^2.$$

所以同一立方体骨架内所有候选对任意共同步长序列产生相同全部未来输出。反过来，全部未来相同必然前两次读数相同，已经落在上述集合。证毕。

该定理说明完整 Gram 识别和目标预测必须分开：这些永久不可分的 Gram 可以合并成同一预测状态，闭合坐标就是各个 `(w_i,s_i)`。恢复与目标无关的原始区别并非这项预测任务的必要条件。

## IR.6 有两个中间秩候选时，第三步如何裁决

在连通情形，若 IR3 的宽度筛选保留两个不同端点 `a,b`，定义可观察矩阵

$$S=W_2W_1^TW_1-W_1W_1^TW_2.$$

**定理 IR6。** 这两个真实状态的第三步输出差为

$$\boxed{W_3(b)-W_3(a)=(b-a)h_1^2h_2S.}\tag{IR.7}$$

因此 `S≠0` 时第三步充分且对这条前缀必要；`S=0` 时第三步仍无法区分，不能据此断言以后永远无法区分。

**证明。** 在时刻1，两个状态的 Gram 差恰为 `(b-a)diag(I,-I)`。共同第二步之后，两对角差为 `(b-a)(I-h_1²W_1ᵀW_1)` 和其输出侧负版本。再用(IR.1)比较第三步，当前输出项和共同三次项相消，余项就是(IR.7)。证毕。

**精确读数已知的条件噪声判据。** 前两步精确，第三个输出矩阵误差不超过 `ε`。令

$$\Delta=|b-a|\,|h_1|^2|h_2|\,\|S\|_F.$$

存在对全部合法噪声都正确的二选一规则，当且仅当 `Δ>2ε`。因为两个闭 Frobenius 球不相交恰好满足此不等式；若相交，交点就是同时符合两状态的数据。等号也不能保证区分。这不是前两步也有噪声时的端到端保证。

## IR.7 精确铅笔内的近低秩稳定界

在非退化半正定区间 `[a,b]` 内，设 `P=M(a)`、`Q=M(b)`，则由 IR2 的公共核论证，

$$\kappa=\lambda_{\min}(P+Q)>0.$$

**定理 IR7。** 对任何 `c∈[a,b]`，若 `λ_min(M(c))≤δ`，则

$$\boxed{\operatorname{dist}(c,\{a,b\})
\le(b-a)\delta/\kappa.}\tag{IR.8}$$

对“第 `n-m` 个最小特征值不超过 `δ`”的近秩条件，该结论同样成立。

**证明。** 写 `c=(1-t)a+tb`。半正定顺序给

$$M(c)=(1-t)P+tQ\succeq\min(t,1-t)(P+Q).$$

因此 `λ_min(M(c))≥κ min(t,1-t)`，乘以 `b-a` 即得。更强的近秩条件蕴含所用的最小特征值条件。证毕。

这是一个由实际端点计算的条件证书；没有预先假定所有模型共享同一个 `κ`。若前缀噪声改变了铅笔本身，还须另外控制这些变化，不能直接沿用(IR.8)。

## IR.8 非平凡实际实例

取 `q=2,m=3,h_0=h_1=h_2=1/8,W_0=diag(1,2)`，令

$$A_+=\begin{pmatrix}55/17&-4/17\\-4/17&72/17\end{pmatrix},\quad
B_+=\begin{pmatrix}25/51&-4/17\\-4/17&23/17\end{pmatrix},
\qquad A_-=B_+,\ B_-=A_+.$$

两个 Gram 都半正定、秩为三。令 `K=diag(64/63,16/15)`、`c_*=735/544`，两者的差为 `2c_*diag(K,-K)`，中点正定。因此它们就是整个半正定区间的两个端点，两个都满足该中间宽度。

它们共享

$$W_1=\begin{pmatrix}1795/3264&3/34\\3/34&99/136\end{pmatrix}$$

和 `W_2`，图连通。直接由真实更新算得

$$S_{12}=3636023369/247279386624\ne0.$$

所以该中间秩实例最少恰需三个训练步；两端点候选界达到等号。

作为单候选实例，取 `q=3,m=4,h_0=1/16,Σ=diag(1,2,3)`，

$$A=\begin{pmatrix}1/2&1/10&1/10\\1/10&4&1/10\\1/10&1/10&6\end{pmatrix},
\qquad B=\Sigma A^{-1}\Sigma+\operatorname{diag}(0,0,1).$$

初始 Gram 半正定、秩四，首步图完整。设 `E=[e_1,e_2]`、`Z=[-A^{-1}ΣE;E]`，其列为初始 Gram 的核基。对 `K=diag(256/255,64/63,256/247)`，有

$$\det(Z^T\operatorname{diag}(K,-K)Z)
=-473221905306484736/200502975693371715<0.$$

限制二次型不定，IR3 的单点判据说明半正定纤维已经只有一个点。因此两个训练步充分；这里不另声称一个训练步必然不够。

## IR.9 在可识别子类内仍不存在统一稳定逆

**定理 IR8。** 即使限定 `q=2,m=3,h=1/8`、初始谱固定为 `(1,2)`、首步图连通，且第三步可以唯一识别状态，对任意固定有限观察长度 `N≥3`，仍不存在对该整个子类有效、在零处趋于零的统一逆误差模。

**证明。** 令

$$\Sigma=\operatorname{diag}(1,2),\quad K=\operatorname{diag}(64/63,16/15),
\quad D(t)=\begin{pmatrix}2&t\\t&4\end{pmatrix},$$

$$M_t(c)=\begin{pmatrix}D(t)+cK&\Sigma\\\Sigma&D(t)-cK\end{pmatrix}.$$

对充分小 `|t|`，`M_t(0)` 正定。交换两个块把 `c` 变为 `-c`，故半正定参数区间为 `[-c(t),c(t)]`。在 `t=0`，两个单坐标块给

$$c(0)=63\sqrt3/64>0,$$

另一个坐标的允许阈值严格更大，所以端点具有一个简单零特征值。行列式对 `c` 的导数非零，隐函数定理及其余正特征值的连续性给 `c(t)→c(0)`，且两端点在足够小 `t` 下仍半正定、秩三。

取真实初态 `Γ_±(t)=M_t(±c(t))`。它们位于同一两步纤维，故共享 `W_0,W_1,W_2`。直接在中点代表上计算即可得到共同读数和检测量：

$$W_1(t)=\begin{pmatrix}33/64&-3t/8\\-3t/8&1/8\end{pmatrix},
\qquad S_{12}(t)=-509343t/67108864.$$

因此每个足够小的 `t≠0` 都图连通且 `S≠0`，第三步唯一识别各端点。与此同时

$$\|\Gamma_+(t)-\Gamma_-(t)\|_F
=2c(t)\|\operatorname{diag}(K,-K)\|_F\longrightarrow C_0>0.$$

在 `t=0`，两模型均对角且每个坐标的 `(w_i,s_i)` 相同，所以全部未来输出相同。有限个同步更新都是初始 Gram 的多项式函数。因此对任意固定 `N`，

$$\max_{0\le n\le N}\|W_n^+(t)-W_n^-(t)\|_F\longrightarrow0.$$

若存在趋零的统一逆模，将其应用于这一对处处可识别的 `t≠0` 状态，便会迫使初态距离趋零，与上式矛盾。证毕。

取两个输出前缀的中点，还得到有界噪声下的二点不可区分证据。本定理只针对每个固定有限视界，没有把极限交换为全部无限时间的上确界。它说明“通常可识别”不能替代观测后稳定证书。

## IR.10 完成范围与已有数学

本增补完成了简单初始谱、首步非共振范围内，中间秩两步相容集合的逐数据分类：连通时为一或两个端点；断连时为不变块铅笔的直积加总秩预算；完全解耦时为可以精确计数的永久歧义骨架。它同时给出第三步的充分必要分离条件和严格的稳定性边界。

初始重谱、零谱及首步共振不由式(IR.2)处理；任意更深的所有例外也没有被归结为统一步数。这里没有宣称完成所有非线性模型、所有测量接口的状态识别问题，或建立统一的全噪声最优估计器。

半正定锥的核性质、合同谱分析和隐函数定理属于经典工具；它们不直接给出本固定学习前缀的端点分类。既有 Gram 递推的适用范围沿用 RK.7。

---

# 增补 RS：重谱的四步识别、共振擦除与全时域稳定预测

本增补沿用 RK、IR 的固定零标签两层实线性学习任务。所解决的退化情形是：初始正奇异值可以重复，特别是所有初始奇异值完全相同。完整初态识别、后继状态识别和目标未来预测分别声明。

## RS.1 固定任务与实际状态

令 U∈R^(m×q)、V∈R^(q×m)，固定损失为 ||VU||_F²/2。记

$$W=VU,\quad A=U^TU,\quad B=VV^T,\quad
\Gamma=\begin{pmatrix}A&W^T\\W&B\end{pmatrix}.$$

真实状态恰好满足 Γ≽0、rankΓ≤m：反向因子分解 Γ=ZᵀZ 后，把 Z 的两组列分别作为 U、Vᵀ，不足 m 行补零。同步梯度下降的精确更新为

$$\begin{aligned}
A^+&=A-2hW^TW+h^2W^TBW,\\
B^+&=B-2hWW^T+h^2WAW^T,\\
W^+&=W-h(BW+WA)+h^2WW^TW.
\end{aligned}\tag{RS.1}$$

等价地 Γ⁺=C_h(W)ΓC_h(W)ᵀ，其中

$$C_h(W)=I-h\begin{pmatrix}0&W^T\\W&0\end{pmatrix}.$$

这些递推属于既有前置，不作为新颖性主张。所有实验都是一条被动轨迹；没有重置、修改标签或自由指定梯度。所有识别结论恢复 Gram，不恢复共同隐藏正交坐标。

## RS.2 任意正重谱的完整两步纤维

固定初始奇异向量坐标 W₀=Σ=diag(σ_i)，只要求 σ_i>0，允许任意重数。前两步长度 h₀,h₁ 非零，置 D=I-h₀²Σ²。两个初始对称块对 (A,B)、(Ã,B̃) 共享 W₀。

**定理 RS1。** 两组初态的 W₁、W₂ 都相同，当且仅当存在实对称 X，使

$$\boxed{\widetilde A=A+X,\quad\widetilde B=B-X,\quad
[X,\Sigma]=0,\quad[DX,W_1]=0.}\tag{RS.2}$$

没有假设 D 可逆。实际纤维是这个完整仿射解集与 Γ≽0、rankΓ≤m 的交。

**证明。** 首步输出相同等价于 YΣ+ΣX=0，其中 X=Ã-A、Y=B̃-B。第 ij 与 ji 条目，利用 X,Y 对称，给

$$Y_{ij}\sigma_j+\sigma_iX_{ij}=0,\qquad
Y_{ij}\sigma_i+\sigma_jX_{ij}=0.$$

相加得到 (σ_i+σ_j)(X_ij+Y_ij)=0。因为 σ_i+σ_j>0，必有 Y=-X。代回得 XΣ=ΣX。这一步没有除以任何奇异值间隙。

将初始差 (X,-X) 代入真实首步 Gram 更新，因 X 与 Σ 交换，得到

$$\Delta A_1=DX,\qquad\Delta B_1=-DX,\qquad\Delta W_1=0.$$

比较第二步，当前 W₁ 与三次项均相同，故

$$\Delta W_2=h_1(DXW_1-W_1DX).$$

h₁≠0 给出必要且充分的最后一个条件。反向按同一计算逐步验证即可。证毕。

若 D 可逆，可以把实际剩余变量改成 T=DX。此时 T 对称并同时与 Σ、W₁ 交换，X=D⁻¹T。由于 T 对称，与 W₁ 交换也蕴含与 W₁ᵀ交换。这是有限矩阵代数的自伴交换子空间描述；初始简单谱的图规则是其对角特例。

**擦除子空间。** 在首步输出相同的纤维内，两个完整后继 Gram 相同恰当且仅当 DX=0。若 h₀>0，这些 X 恰支撑在 σ=1/h₀ 的共振特征空间上。维数为 r 的该空间可携带 r(r+1)/2 个对称差异方向，它们在第一步后全部消失，任何后续输出都无法恢复。这里讨论线性差异空间，实际合法方向仍须满足各自初态的 PSD/秩约束。

## RS.3 完全重谱：第一个读数恢复和，第二个读数恢复交换子

令 W₀=σI、σ>0，S=A+B、H=A-B，

$$\alpha=1+h_0^2\sigma^2,\qquad\delta=1-h_0^2\sigma^2.$$

直接由 RS.1 得

$$W_1=\sigma(\alpha I-h_0S),\quad
S_1=\alpha S-4h_0\sigma^2 I,\quad H_1=\delta H.$$

**命题 RS2。** 精确 W₀、W₁、h₀ 唯一确定 S。第二步输出满足

$$\boxed{W_2=W_1-h_1S_1W_1+h_1^2W_1^3
+\frac{h_0h_1\sigma\delta}{2}[S,H].}\tag{RS.3}$$

所以其对称部分由 S 决定，反对称部分恰读取交换子 [S,H]。若 δ≠0，W₀、W₁、W₂ 的全部竞争初态差为 (X,-X)，其中 X 为任意与 S 交换的对称矩阵。

**证明。** 写 A₁=(S₁+H₁)/2、B₁=(S₁-H₁)/2。因为 S₁ 与 W₁ 都是 S 的多项式，

$$B_1W_1+W_1A_1=S_1W_1+\frac12[W_1,H_1].$$

再用 [W₁,H₁]=-h₀σδ[S,H] 得公式。S,H 对称，故交换子反对称。纤维结论也可直接由 RS1 的 D=δI 得到。证毕。

这说明完全相同的初始奇异值不会使全部信息永久不可见；关键在于后续产生的矩阵是否交换。S 自身有重谱、[S,H]=0 等情形没有被预先删除。

## RS.4 四步识别的精确条件与真实下界

假设 δ≠0。选 S 的一套固定正交特征基，设 S 特征值互异，令 W₁=diag(λ_i)，

$$E=I-h_1^2W_1^2,\qquad e_i=1-h_1^2\lambda_i^2\ne0.$$

在该坐标中定义 W₂ 非对角连接图。由 RS.3，对 i≠j 有

$$(W_2)_{ij}=-\frac{h_1\delta}{2}(\lambda_i-\lambda_j)H_{ij}.$$

所以其连通性精确对应 H 在这些不同 S 特征方向之间的耦合。

**定理 RS3。** 图连通时，全部共享 W₀、W₁、W₂、W₃ 的初始对称块对形成一条直线：

$$\boxed{A_c=A_*+\frac{c}{\delta}E^{-1},\qquad
B_c=B_*-\frac{c}{\delta}E^{-1}.}\tag{RS.4}$$

定义可由已有读数计算的

$$T=W_3W_2^TW_2-W_2W_2^TW_3.$$

则第四步差为

$$\boxed{W_4(c)-W_4(0)=c h_2^2h_3 T.}\tag{RS.5}$$

若 T≠0，则 W₀,...,W₄ 唯一确定初始 Gram。若初始 Γ_* 正定且 m≥2q，足够小的非零 c 仍是合法真实状态，所以 W₀,...,W₃ 确实不足。

**证明。** 首步留下任意对称 X，第二步要求 [X,S]=0。简单 S 使 X 对角。时刻2的两块差为 δEX、-δEX。第三步相同恰好要求 δEX 与 W₂ 交换；连接图连通使该对角矩阵等于 cI，即得 RS.4。

时刻2两块之差为 cI、-cI；真实第三步之后为 c(I-h₂²W₂ᵀW₂) 与 -c(I-h₂²W₂W₂ᵀ)。第四步的共同输出项及三次项抵消，余项正是 RS.5。T≠0 强制 c=0。正定性为开条件，故小 c 保持真实满秩实现，给出下界。证毕。

更一般，若 W₂ 图有 r 个分量，第三步后线性纤维维数为 r，每个分量各一个常数。S 重谱时使用 RS.2 的交换子空间；E 奇异时可能有额外擦除方向，不能直接使用其逆。

## RS.5 所有维数的一般位置最小深度四

**定理 RS4。** 固定 q≥2、σ>0、m≥2q、正步长 h₀,h₁,h₂,h₃，且 h₀σ≠1。在初始 W₀=σI 的正定 Gram 域中，除一个真代数零集外，最少恰好需要四个被动训练步识别初始 Gram。即 W₀,...,W₄ 足够，W₀,...,W₃ 不足。成功区域开、稠密且在该域的 A,B 坐标中具有满测度。

**非零见证的全维度构造。** 令 λ_i=-iR，其中 R>0 将取充分大。定义对角 S 为

$$S_{ii}=\frac{\alpha-\lambda_i/\sigma}{h_0},$$

并取 H=z(11ᵀ-I)。初始 A=(S+H)/2、B=(S-H)/2。z=0 时，充分大 R 使每个 S_ii>2σ，故初始 Gram 正定；足够小 z 保持正定。W₁ 的特征值为 λ_i，且 E 可逆；z≠0 时 W₂ 图完整。

剩下要证明 T₁₂ 不恒为零，不能以“通常非零”代替。置

$$\gamma=\delta^2/h_0,\qquad\beta=\alpha/(h_0\sigma),$$

$$p(x)=x[1-h_1(\gamma-\beta x)+h_1^2x^2],\qquad
r(x)=\tfrac12(1+h_1^2x^2)(\gamma-\beta x)-2h_1x^2.$$

在 z=0，W₂ 对角条目为 p(λ_i)，A₂=B₂ 的对角条目为 r(λ_i)。对一对坐标的 x=λ_i、y=λ_j，直接一阶扰动计算给

$$\left.\frac{\partial T_{ij}}{\partial z}\right|_{z=0}
=\frac{h_2\delta}{2}[p(x)-p(y)]^2
\left[(1-h_1^2xy)(p(x)+p(y))
+h_1(x-y)(r(x)-r(y))\right].\tag{RS.6}$$

为核对这一步：W₂的一阶项为反对称矩阵，其 ij 条目是 -h₁δ(x-y)/2；A₂的一阶项为 δ(1-h₁²xy)/2，B₂为其负。令 L₂=B₂W₂+W₂A₂，使用 T=h₂(W₂W₂ᵀL₂-L₂W₂ᵀW₂)，收集一阶项即得 RS.6。在对角基点，其他坐标不参与该 ij 条目的一阶项，因此此式适用于全部 q≥2。

代 x=-R、y=-2R，得到关于 R 的非零多项式，其最高项为

$$\boxed{441\delta h_1^8h_2 R^{11}.}\tag{RS.7}$$

因为 δ≠0，该系数非零。充分大 R 使一阶项非零，再取充分小的非零 z，得到实际正定见证，且 T≠0。

**一般位置与必要性。** 对实际轨迹构造 P₀=I、P_{n+1}=C_{h_n}(W_n)P_n，定义对 Sym_(2q) 的线性算子

$$\mathcal O(X)=((P_nXP_n^T)_{21})_{n=0}^4.$$

其矩阵条目是初始 A,B 的多项式。见证的 RS3 证明该算子单射，所以最大子式平方和不是零多项式。加入 S 的判别式及 det E 的零集仍是真代数例外集。

在例外集外，单射性给上界。对任何 δ≠0、E 可逆的正定初态，RS.4 中的小非零 c 都保持 W₀,...,W₃，因为 E⁻¹与 S、W₁交换且时刻2差为 cI、-cI。这一下界不依赖连接图。故一般位置的最小深度恰为四。证毕。

q=1 时没有这个结论；(w,a+b) 对所有更新已经闭合。秩边界或 m<2q 可能删去竞争方向，不能直接搬用正定域的下界。一般位置也不意味着统一噪声稳定，且本定理没有声称这些固定步长保证训练损失下降。

## RS.6 共振时，隐藏历史被真正擦除，目标未来却闭合

**定理 RS5。** 令 W₀=σI、σ>0，首步取 h₀=1/σ。对每个实际初态，令 S=A₀+B₀、T₁=S-2σI。则

$$\boxed{T_1\succeq0,\qquad A_1=B_1=T_1,\qquad W_1=-T_1.}\tag{RS.8}$$

之后对任意共同步长序列，完整后继 Gram 和输出都由 T₁ 决定，闭合规则为

$$\boxed{T_{n+1}=F_{h_n}(T_n):=T_n(I-h_nT_n)^2,
\qquad A_n=B_n=T_n,\quad W_n=-T_n\quad(n\ge1).}\tag{RS.9}$$

**证明。** RS.1 在 h₀σ=1 时直接给 A₁=B₁=S-2σI、W₁=2σI-S。初态 Gram 对向量 (x,-x) 的非负二次型给 S-2σI≽0。将 A=B=T、W=-T 代入下一更新，三项均化为 RS.9，归纳即可。

原始参数也给同一结论：U₁=U₀-V₀ᵀ、V₁=-(U₁)ᵀ。因而这确实是同步更新产生的状态降秩，不是人工合并未证明的读数。初始 H=A-B 可以不同，甚至存在正定的连续竞争族；其完整后继已经相同，所以再多未来读数也不能恢复它。

不过，后继未来只需要 T₁=-W₁。此处“历史不可恢复”与“目标不可预测”被一个实际算法严格分开。证毕。

## RS.7 全时域不放大的精确步长阈值

固定 L>0、h≥0，令 C_L={T=Tᵀ:0≼T≼LI}。这里距离为 Frobenius 范数，不把它替换为算子范数。

**定理 RS6。** 映射 F_h(T)=T(I-hT)² 在 C_L 上为 Frobenius 非扩张，当且仅当

$$\boxed{0\le hL\le4/3.}\tag{RS.10}$$

在该范围内，它还保持 C_L，并有 0≼F_h(T)≼T。

**证明。** 标量函数 f_h(t)=t(1-ht)² 的导数为

$$f_h'(t)=(1-ht)(1-3ht)=1-4ht+3h²t².$$

在 0≤ht≤4/3 上，该导数位于 [-1/3,1]，故标量 Lipschitz 常数不超过一。而 (1-ht)²≤1 保证 0≤f_h(t)≤t。

对两个不必交换的对称矩阵 T,Q，取正交特征基 u_i,v_j、特征值 t_i,q_j。直接展开 Frobenius 内积得到

$$\|f_h(T)-f_h(Q)\|_F^2
=\sum_{ij}|u_i^Tv_j|^2|f_h(t_i)-f_h(q_j)|^2,$$

$$\|T-Q\|_F^2
=\sum_{ij}|u_i^Tv_j|^2|t_i-q_j|^2.$$

逐项使用标量不等式，得到矩阵非扩张；标量谱范围同时证明区间与半正定顺序保持。

若 hL>4/3，则 f_h'(L)>1。选 L 附近的两个标量，或把它们作为对角矩阵的一个条目，差异严格放大。因此阈值不能提高。证毕。

该谱差恒等式和 Hilbert–Schmidt Lipschitz 原理是已有工具。新的任务结论是 RS5 的实际预测商上存在这个精确步长区间，而非一般标量 Lipschitz 函数在任意矩阵范数中都非扩张。

## RS.8 不恢复旧隐藏状态的无限未来误差控制

**定理 RS7。** 在 RS5 的共振更新之后，假设 T₁∈C_L。测量 Y₁ 满足 ||Y₁-W₁||_F≤ε。将 -Y₁ 在 Frobenius 几何中投影到 C_L，得到 T̂₁。对真实状态和估计状态使用同一后续步长序列，且每步 0≤h_nL≤4/3，则

$$\boxed{\sup_{n\ge1}\|\widehat W_n-W_n\|_F\le\epsilon.}\tag{RS.11}$$

这里 Ŵ_n=-T̂_n，T̂ 按 RS.9 更新。没有恢复初始 H，也没有对 T₁ 的最小正特征值、秩或特征值间隙设下界。

**证明。** C_L 是闭凸集，欧氏投影固定真实 T₁，且到 T₁ 的距离不增加。因此 ||T̂₁-T₁||_F≤ε。RS6 保证两条轨迹始终在 C_L，逐步使用非扩张并归纳，得到每个时刻的界。证毕。

投影可实现为：先取 -Y₁ 的对称部分，再将其特征值截断到 [0,L]。一个可由数据给出的安全上界是 L=||Y₁||_F+ε；若它为零，则真实状态为零，未来恒零。定理比较的是精确模型与同一步长，不包含首步 h₀σ 的误差、非零标签或未预算的后续过程噪声。

**衰减补充。** 令 H_n=∑_{k=1}^{n-1}h_k，则真实和估计状态同时满足

$$0\preceq T_n,\widehat T_n\preceq
\frac{L}{1+2LH_n}I,$$

从而

$$\boxed{\|\widehat W_n-W_n\|_F
\le\min\left\{\epsilon,\frac{\sqrt q\,L}{1+2LH_n}\right\}.}\tag{RS.12}$$

**证明。** 对 0≤x≤4/3，

$$(1-x)^2(1+2x)-1=x^2(2x-3)\le0.$$

因此 f_h(t)≤t/(1+2ht)。对每个非零特征值取倒数并逐步求和；零特征值始终为零。最大初始特征值不超过 L，得到算子界。两个位于 [0,ℓI] 的对称矩阵之差位于 [-ℓI,ℓI]，Frobenius 范数不超过 √qℓ；再与 RS.11 合并。证毕。

常步长 h>0、标量初值 0<T₁<1/h 时，轨迹不在有限时间变零，且 nT_n→1/(2h)。因为 T_n→0，倒数递增量 (2h-h²T_n)/(1-hT_n)²→2h，用 Cesàro 平均即可。故衰减主阶中的系数二不能统一改善。

## RS.9 实际校准与剩余范围

取 q=2 或3，σ=1，四步步长均为1/8，S=diag(4,6,...,2q+2)、H=(11ᵀ-I)/2。初始 Gram 严格对角占优而正定。完整对称矩阵观察算子的核维数，经 W₀、W₁、W₂、W₃、W₄ 逐次约束为

$$q=2:(6,3,2,1,0),\qquad q=3:(12,6,3,1,0).$$

RS.4 给出的足够小非零竞争方向保持正定，并在真实更新中共享 W₀,...,W₃，第四步按 RS.5 分离。有限校准不承担全 q 的一般位置证明，后者由式(RS.6)、(RS.7)的非零构造承担。

本增补没有把初始零奇异值的一般完整纤维、任意固定小宽度的重谱最小历史、或全部非共振模型的全时域稳定性一并宣布解决。RS1 允许重复正谱和首步共振；RS4 专门解决完全重谱的正定一般位置；RS5–RS7 提供真实共振预测商的完全闭合与稳定误差。这些范围不能相互偷换。

## RS.10 文献与适用范围

RS.1 的精确 Gram 更新与有限步、梯度流之别沿用本卷 RK、IR，并可与 [Holzmüller–Steinwart](../../../Library/Dynamics/holzmueller2020training.md) 附录C命题C.2的离散合同递推比较；该先例不蕴含 RS.2 的两步交换子纤维。RS.7 的 Hilbert–Schmidt 非扩张估计由正文中的特征基展开逐项证明，其适用域仍是所声明的 Frobenius 范数与谱区间。

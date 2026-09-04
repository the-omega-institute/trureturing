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
\mathcal L_{\mathrm{CIRPT}}
\longrightarrow
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

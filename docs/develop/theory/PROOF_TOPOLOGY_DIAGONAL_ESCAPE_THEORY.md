# 证明拓扑、对合逻辑与观察逃逸统一理论
## Proof Topology, Involution Logic, and Visible Diagonal Escape

> 状态：理论输入稿，2026-08-25。  
> 真源纪律：本文解释形式结构。Lean 声明、证明项及其 axiom closure 才是 Base 的形式真值。  
> 范围：只讨论关系、偏序、拓扑、读数核、对合、因子化、残差与对角逃逸。工程流程、自动科研角色和论文生产协议不进入承重定义。

---

## 摘要

本理论统一两条此前分开发展的主线。

第一条主线来自定义逃逸与观察者读数：一个表示保留哪些区别，遗漏哪些区别，加入新定义后 residual 怎样缩小，目标何时能从 latent 中恢复，对角对象何时真正增加可回答问题。

第二条主线来自认证 DAG 与拓扑：直接依赖怎样生成可达偏序，偏序怎样生成 Alexandrov 拓扑，深度怎样形成 filtration，dominator 为什么必须保留路径多重性，观察投影怎样制造或隐藏结构。

两条主线在以下链条中会合：

\[
\boxed{
\text{读数族}
\longrightarrow
\text{共同核}
\longrightarrow
\text{观察拓扑}
\longrightarrow
\text{可区分状态商}
}
\]

以及：

\[
\boxed{
\text{对角化生成逃逸，观察决定逃逸是否仍然可见。}
}
\]

本卷还补入相对否定与对合逻辑。集合补集、点值对合和 Boolean 取反属于三个不同层次。点值补集只有在二元素论域中闭合。一般固定点自由对合只提供一条可逆的“另一侧”方向，Boolean 定向还需要每个二元轨道上的横截选择。

---

# 第一部：表示、核与目标残差

## 1.1 表示是读数

设完整状态空间为 \(X\)。一个概念或表示是函数

\[
q:X\to Q.
\]

它诱导核关系

\[
\ker(q)=\{(x,y):q(x)=q(y)\}.
\]

核记录被当前表示压在同一纤维中的状态对。表示越细，核越小。

给定目标

\[
T:X\to Y,
\]

定义目标残差

\[
\mathcal E(q;T)
=
\ker(q)\setminus\ker(T).
\]

即：当前表示认为相同，而目标必须区分的状态对。

## 1.2 目标充分性

表示 \(q\) 对目标 \(T\) 充分，当存在解码器

\[
h:Q\to Y,
\qquad
T=h\circ q.
\]

在非空状态空间上，这等价于目标在每个 \(q\)-纤维上恒定，也等价于

\[
\mathcal E(q;T)=\varnothing.
\]

## 1.3 联合读数与 residual join law

加入候选定义

\[
d:X\to D
\]

后形成联合读数

\[
(q\vee d)(x)=(q(x),d(x)).
\]

其目标残差满足精确恒等式

\[
\boxed{
\mathcal E(q\vee d;T)
=
\mathcal E(q;T)\cap\ker(d).
}
\]

因此新定义不会创造旧目标残差。它只删除自己能够分开的残差对。

---

# 第二部：定义族、Galois 对应与语义闭包

## 2.1 定义族的共同核

给定同值域定义族

\[
\Gamma\subseteq (X\to B),
\]

定义共同核

\[
K_\Gamma
=
\bigcap_{d\in\Gamma}\ker(d).
\]

它表示全部现有定义共同看不见的状态对。

对于关系 \(R\subseteq X^2\)，定义在 \(R\) 上不变的读数族

\[
\operatorname{Inv}(R)
=
\{d:X\to B:(x,y)\in R\Rightarrow d(x)=d(y)\}.
\]

两者形成反变 Galois 对应：

\[
\boxed{
\Gamma\subseteq\operatorname{Inv}(R)
\iff
R\subseteq K_\Gamma.
}
\]

## 2.2 语义闭包

定义

\[
\operatorname{Cl}(\Gamma)
=
\operatorname{Inv}(K_\Gamma).
\]

则闭包满足广延、单调与幂等，并且

\[
\boxed{
K_{\operatorname{Cl}(\Gamma)}=K_\Gamma.
}
\]

闭包加入所有能从旧联合坐标恢复的同值域读数。它提高命名和表达便利性，但不增加对源状态的区分力。

## 2.3 原语逃逸

候选 \(c:X\to C\) 是原语逃逸，当

\[
c\notin\operatorname{Cl}(\Gamma).
\]

等价地，存在 \(x,y\) 满足

\[
\forall d\in\Gamma,\ d(x)=d(y),
\qquad
c(x)\neq c(y).
\]

也就是说，候选切开了旧语言共同核中的一对状态。

## 2.4 生产性逃逸

给定当前读数 \(q\) 与目标 \(T\)，候选 \(c\) 是生产性分离，当它切开语言盲残差中的一对状态：

\[
(x,y)\in \mathcal E(q;T)\cap K_\Gamma,
\qquad
c(x)\neq c(y).
\]

生产性分离必为原语逃逸。

---

# 第三部：认证 DAG 的五层结构

设直接依赖图为

\[
G=(V,E).
\]

## 3.1 直接边图

直接图保存 prerequisite、冗余直接边和路径选择。它是 dominator 与删除影响分析的最低充分层。

## 3.2 路径层

路径由直接边序列组成。不同路径即使端点相同，仍然是不同的构造见证。所有从根到目标的路径都经过某节点，才构成 dominator。

## 3.3 可达偏序

定义

\[
u\preceq v
\iff
u=v\text{ 或存在从 }u\text{ 到 }v\text{ 的有向路径}.
\]

若直接边无环，则 \(\preceq\) 自反、传递、反对称，因此是偏序。

## 3.4 Alexandrov 依赖拓扑

采用上集开集约定：

\[
U\text{ 开}
\iff
x\in U,\ x\preceq y
\Rightarrow y\in U.
\]

主开集与主闭集为

\[
\uparrow x=\{y:x\preceq y\},
\qquad
\downarrow x=\{y:y\preceq x\}.
\]

有

\[
\boxed{
\operatorname{MinOpen}(x)=\uparrow x,
\qquad
\overline{\{x\}}=\downarrow x.
}
\]

并且

\[
u\preceq v
\Rightarrow
\downarrow u\subseteq\downarrow v,
\qquad
\uparrow v\subseteq\uparrow u.
\]

所以 \(\downarrow v\) 是认证基础，\(\uparrow v\) 是结构影响锥。

## 3.5 序复形层

严格链

\[
x_0\prec x_1\prec\cdots\prec x_k
\]

形成序复形的单形。只有在选定此类复形后，Betti 数、同调和持久性才有确定对象。原始 DAG 不自动携带“知识洞”的唯一同调解释。

## 3.6 遗忘边界

从直接图压到可达偏序会遗忘平行路径和冗余直接边。从可达偏序压到 Alexandrov 空间，不再保留路径多重性。

因此：

\[
\boxed{
\text{dominator 不是 Alexandrov 拓扑不变量。}
}
\]

两张图可以具有相同可达偏序，却因增加一条替代直接路径而具有不同 dominator。

---

# 第四部：深度 filtration 与带值单调性

## 4.1 深度兼容性

设

\[
d:V\to\mathbb N
\]

满足每条直接边严格增加：

\[
E(u,v)\Rightarrow d(u)<d(v).
\]

则沿任意非空路径仍有

\[
u\prec v\Rightarrow d(u)<d(v),
\]

沿可达关系有

\[
u\preceq v\Rightarrow d(u)\le d(v).
\]

## 4.2 闭 filtration

定义

\[
F_k=\{v:d(v)\le k\}.
\]

在上集开集约定下，\(F_k\) 是下集，因而是闭集，并且

\[
F_0\subseteq F_1\subseteq F_2\subseteq\cdots.
\]

所以 depth sublevel 是闭 filtration。其补集 \(\{v:k<d(v)\}\) 是开集。

## 4.3 标签沿路径单调

令 \(A:V\to L\) 取值于任意预序。如果

\[
E(u,v)\Rightarrow A(u)\le A(v),
\]

则

\[
u\preceq v\Rightarrow A(u)\le A(v).
\]

集合值 axiom closure 是此定理的实例。实际 truth export 是否满足边局部前件，仍取决于 edge 与 axiom-closure 字段是否使用同一依赖语义。

---

# 第五部：dominator cut

给定根 \(r\)。节点 \(u\) dominate 节点 \(v\)，当每一条从 \(r\) 到 \(v\) 的有向路径都经过 \(u\)。

若 \(u\neq v\) 且 \(u\) dominate \(v\)，删除 \(u\) 后不存在从 \(r\) 到 \(v\) 的路径。

证明只是定义的反证展开：删除后若仍有路径，则该路径也是原图中一条避开 \(u\) 的根到 \(v\) 路径。

该结论刻画当前图表示中的结构瓶颈。它不声称该数学命题在一切未来证明中都无法绕过 \(u\)。

---

# 第六部：观察拓扑等于读数核的几何

给定读数

\[
q:X\to Q,
\]

令 \(Q\) 取离散拓扑，并在 \(X\) 上取诱导拓扑

\[
\tau_q=q^{-1}(\mathcal P(Q)).
\]

开集恰是 \(q\)-纤维的并。

## 6.1 不可分辨性等于核

在 \(\tau_q\) 中：

\[
\boxed{
\operatorname{Inseparable}_{\tau_q}(x,y)
\iff
q(x)=q(y).
}
\]

若读数相同，一切开集同时包含二者或同时排除二者。若读数不同，单个读数值的原像分开二者。

## 6.2 核等价决定拓扑等价

若两个读数 \(q,r\) 满足

\[
q(x)=q(y)\iff r(x)=r(y)
\]

对所有 \(x,y\) 成立，则

\[
\tau_q=\tau_r.
\]

所以 partition topology 只依赖读数核，不依赖未实现的值域坐标或坐标重命名。

## 6.3 T0 商

观察拓扑的不可分辨商自然对应实际实现像

\[
\operatorname{range}(q).
\]

因此有效读数规范化、kernel quotient 与拓扑 T0 反射是同一结构的三种语言。

---

# 第七部：residual 是拓扑分离缺陷

定义拓扑分离缺陷

\[
\operatorname{SepDef}(q,T)
=
\{(x,y):x,y\text{ 在 }\tau_q\text{ 中不可分，且在 }\tau_T\text{ 中可分}\}.
\]

由核等价立即得到

\[
\boxed{
\operatorname{SepDef}(q,T)=\mathcal E(q;T).
}
\]

因此 residual 不是单纯的误差集合。它是当前观察拓扑相对于目标观察拓扑缺少的分离关系。

加入候选定义后：

\[
\operatorname{SepDef}(q\vee d,T)
=
\operatorname{SepDef}(q,T)
\cap
\operatorname{Insep}(\tau_d).
\]

候选只能删除自己能在拓扑上分开的 residual pairs。

---

# 第八部：目标恢复等于连续性

在 \(X\) 上取 \(\tau_q\)，在目标值域 \(Y\) 上取离散拓扑。则：

\[
\boxed{
T\text{ 对 }\tau_q\text{ 连续}
\iff
q(x)=q(y)\Rightarrow T(x)=T(y).
}
\]

在非空 \(X\) 上，结合目标恢复判据：

\[
\boxed{
\exists h:Q\to Y,\ T=h\circ q
\iff
T:(X,\tau_q)\to Y_{\mathrm{disc}}\text{ 连续}.
}
\]

所以 target adequacy 有三个等价表述：

1. 解码因子化；
2. 纤维恒定；
3. 对观察拓扑连续。

---

# 第九部：语义闭包的拓扑惰性

定义族 \(\Gamma\) 的联合读数为

\[
J_\Gamma(x)=(d(x))_{d\in\Gamma}.
\]

语义闭包不改变共同核，因此

\[
\ker J_{\operatorname{Cl}(\Gamma)}
=
\ker J_\Gamma.
\]

由核决定观察拓扑，得到：

\[
\boxed{
\tau_{J_{\operatorname{Cl}(\Gamma)}}
=
\tau_{J_\Gamma}.
}
\]

这给定义增长一个严格分类：

- 闭包内新增：增加可恢复坐标、记号和证明便利，观察拓扑不变；
- 闭包外新增：共同核严格缩小，观察拓扑严格变细。

---

# 第十部：原语逃逸等价于严格拓扑精化

设候选 \(c\) 不属于语义闭包。则存在 \(x,y\) 满足旧联合读数相同而 \(c(x)\neq c(y)\)。加入 \(c\) 后，这一对状态被分开。

旧拓扑中的每个开集在新拓扑中仍开，因为新联合读数投影回旧联合读数。并且集合

\[
c^{-1}(\{c(x)\})
\]

在新拓扑中开，却不可能在旧拓扑中开，因为它只包含旧不可分辨对的一侧。

因此：

\[
\boxed{
 c\notin\operatorname{Cl}(\Gamma)
\iff
\tau_{J_\Gamma}
\subsetneq
\tau_{J_{\Gamma}\vee c},
\qquad
\text{其中 } J_{\Gamma}\vee c \text{ 指并置读数 } x\mapsto(J_{\Gamma}(x),\,c(x)).

}
\]

生产性分离蕴含原语逃逸，所以也蕴含严格观察拓扑精化。

---

# 第十一部：相对否定

给定显式论域 \(U\subseteq X\) 与命题区域 \(A\subseteq U\)，定义

\[
\neg_U A=U\setminus A.
\]

若

\[
A\subseteq U\subseteq V,
\]

则有不交分解

\[
\boxed{
\neg_V A
=
\neg_U A\;\dot\cup\;(V\setminus U).
}
\]

扩大论域后，旧 false 区域被保留，新增加的 false 区域恰是此前不在论域中的部分。否定因此是论域相对的区域运算。

---

# 第十二部：原子否定的二元素刚性

称结构 \(n:X\to X\) 为原子否定，如果

\[
\forall x,y,
\qquad
y\neq x\iff y=n(x).
\]

它要求一个点的所有其他可能性仍然由一个点表示。由定义推出：

\[
n(x)\neq x,
\qquad
n(n(x))=x,
\qquad
X\setminus\{x\}=\{n(x)\}.
\]

在 \(X\neq\varnothing\) 时：

\[
\boxed{
X\text{ admits atomic negation}
\iff
X\simeq\mathbf 2.
}
\]

所以二值逻辑的特殊性是：点层和补集层在二元素空间中意外闭合。

---

# 第十三部：对合横截与 Boolean 定向

设

\[
\kappa:X\to X,
\qquad
\kappa^2=\operatorname{id}.
\]

集合 \(S\subseteq X\) 是轨道横截集，当

\[
\boxed{
\kappa(x)\in S
\iff
x\notin S.
}
\]

等价地：

\[
\kappa^{-1}(S)=X\setminus S.
\]

横截条件强制 \(\kappa\) 无不动点。若 \(\kappa\) 是对合，还得到

\[
\kappa(S)=X\setminus S.
\]

因此 Boolean 化需要两项数据：

\[
\boxed{
\text{固定点自由的二元轨道}
+
\text{每个轨道上的一致选边}.
}
\]

对合提供另一侧方向。横截选择决定哪一侧命名为 true。

---

# 第十四部：Boolean 对合观察量

对命题观察量 \(P:X\to\mathrm{Prop}\)，定义 flip sector：

\[
P(\kappa x)\iff\neg P(x),
\]

定义 invariant sector：

\[
P(\kappa x)\iff P(x).
\]

有如下奇偶律：

1. 两个 flip 观察量的 XOR invariant；
2. 两个 flip 观察量的等价关系 invariant；
3. 一个 flip 与一个 invariant 的 XOR 仍 flip；
4. 在非空空间中，同一观察量不能同时 flip 与 invariant。

这形成一个 \(\mathbb Z_2\) 奇偶结构。偶数个翻转相消为不可见，奇数个翻转保留对合可见性。

---

# 第十五部：对合在观察商上的下降

给定读数

\[
q:X\to Q
\]

与变换 \(\kappa:X\to X\)。定义 kernel stability：

\[
q(x)=q(y)
\Rightarrow
q(\kappa x)=q(\kappa y).
\]

若 \(q\) 满射，则：

\[
\boxed{
\kappa\text{ preserves }q\text{-fibers}
\iff
\exists\bar\kappa:Q\to Q,
\quad
\bar\kappa\circ q=q\circ\kappa.
}
\]

下降映射在满射值域上唯一。若 \(\kappa\) 是对合，则 \(\bar\kappa\) 也是对合。

固定点可见性的精确判据为：

\[
\boxed{
\bar\kappa(q(x))=q(x)
\iff
q(\kappa x)=q(x).
}
\]

因此 quotient 可以制造伪固定点。它们表示一个本体二元轨道被读数压入同一纤维。

若 \(q\) 双射，则固定点自由性必被保留。一般满射不足以保留。

---

# 第十六部：对角逃逸经过观察

设目录

\[
g:I\to(A\to Y)
\]

与候选

\[
d:A\to Y,
\qquad
d\notin\operatorname{range}(g).
\]

给定观察

\[
r:Y\to Z,
\]

观察后的目录和候选为 \(r\circ g_i\) 与 \(r\circ d\)。

## 16.1 单射观察保存逃逸

若 \(r\) 单射，则

\[
\boxed{
d\notin\operatorname{range}(g)
\Rightarrow
r\circ d
\notin
\operatorname{range}(i\mapsto r\circ g_i).
}
\]

因为观察后若等于某一目录项，逐点利用单射性即可恢复原候选等于该目录项。

## 16.2 每个非单射观察都隐藏某个逃逸

只要 \(A\neq\varnothing\)，若 \(r\) 非单射，取 \(y_0\neq y_1\) 且 \(r(y_0)=r(y_1)\)。令唯一目录项为常值 \(y_0\)，候选为常值 \(y_1\)。原候选逃出目录，观察后却与目录项相同。

因此：

\[
\boxed{
r\text{ preserves every one-row catalog escape}
\iff
r\text{ is injective}.
}
\]

## 16.3 Lawvere 对角线

若扭转

\[
f:Y\to Y
\]

无不动点，定义

\[
D(i)=f(g_i(i)).
\]

则 \(D\) 逃出目录。单射观察保持该逃逸。非单射观察可能把该逃逸重新压入旧目录的观察像。

所以：

\[
\boxed{
\text{对角线产生 ontic escape，}
\quad
\text{观察忠实性决定 visible escape。}
}
\]

---

# 第十七部：局部闭合与普遍开放

对固定目标 \(T\)，定义族可以清空 \(\mathcal E(q;T)\)，得到目标相对完成。

对于能够枚举自身全部 decoder 的固定表示语言，固定点自由的相对对角目标无法通过旧联合读数因子化。因此旧语言存在非空盲残差。

这给出两种同时成立的结论：

\[
\boxed{
\text{固定目标可以完成，}
\quad
\text{允许新增目标和自应用的普遍语言保持开放。}
}
\]

对角化证明旧语言不封闭。新定义若能压缩一族逃逸并严格细化目标相关拓扑，才成为可复用规律。

---

# 第十八部：形式化模块映射

## 18.1 DependencyTopology

```text
D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder.lean
D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology.lean
D5/S3/ConceptDynamics/DependencyTopology/DepthClosedFiltration.lean
D5/S3/ConceptDynamics/DependencyTopology/DominatorCut.lean
D5/S3/ConceptDynamics/DependencyTopology/AxiomClosureMonotonicity.lean
```

## 18.2 InvolutionLogic

```text
D5/S3/ConceptDynamics/InvolutionLogic/RelativeNegation.lean
D5/S3/ConceptDynamics/InvolutionLogic/AtomicNegationRigidity.lean
D5/S3/ConceptDynamics/InvolutionLogic/InvolutionTransversal.lean
D5/S3/ConceptDynamics/InvolutionLogic/BooleanInvolutionObservables.lean
```

## 18.3 ObservationTopology

```text
D5/S3/ConceptDynamics/ObservationTopology/InvolutionDescent.lean
D5/S3/ConceptDynamics/ObservationTopology/EscapeUnderObservation.lean
D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel.lean
D5/S3/ConceptDynamics/ObservationTopology/ResidualSeparationTopology.lean
D5/S3/ConceptDynamics/ObservationTopology/TargetContinuityFactorization.lean
D5/S3/ConceptDynamics/ObservationTopology/SemanticClosureTopologyInvariance.lean
D5/S3/ConceptDynamics/ObservationTopology/PrimitiveEscapeStrictRefinement.lean
```

这些模块复用 Base 已有的 `Concept`、`Refines`、`jointReadout`、`jointKernel`、`defectRelation`、`SemanticClosure`、`PrimitiveEscape`、`partitionTopology` 与 Lawvere qualitative escape，不建立平行真源。

---

# 第十九部：有限回放与证明边界

小有限模型回放覆盖依赖偏序、Alexandrov 主开闭集、depth filtration、dominator cut、路径标签单调性、partition kernel、residual separation、semantic-closure topology invariance、target continuity 和 primitive escape strict refinement。

有限回放的功能是寻找小反例。它不提供一般证明，也不能替代 Lean elaboration、kernel checking、axiom inspection 或仓库 admission gate。

关于历史记录的勘误：PR #2904 没有包含此前口头声称已同步的有限回放文件。本轮将新的回放报告明确提交到 `docs/reports/PROOF_TOPOLOGY_FINITE_MODEL_REPLAY.md`，并把其地位限定为补充证据。

---

# 第二十部：主张边界

本理论不声称：

1. module-import dominator 等于数学命题在一切证明中的逻辑不可替代性；
2. depth 在任意 DAG 上都是 graded-poset rank；
3. 二维图布局忠实表达全部偏序结构；
4. 原始 DAG 自动拥有唯一有意义的 Betti 数；
5. 非单射观察总会隐藏每一个逃逸，只证明它会隐藏至少一个逃逸；
6. 对合本身已经选择了 Boolean true 侧；
7. 语义闭包增加新的状态区分能力；
8. 有限模型回放可以代替一般定理证明；
9. 工程中的服务、发布、论文或代理流程是 Base 的数学本体。

---

# 结论

本理论的承重链为：

\[
\boxed{
\begin{aligned}
\text{依赖边}
&\to\text{路径}\to\text{可达偏序}\to\text{Alexandrov 拓扑},\\
\text{读数}
&\to\text{核}\to\text{观察拓扑}\to\text{T0 商},\\
\text{目标}
&\to\text{分离缺陷}\to\text{新定义}\to\text{严格拓扑精化},\\
\text{对合}
&\to\text{轨道}\to\text{横截定向}\to\text{Boolean 奇偶},\\
\text{对角化}
&\to\text{本体逃逸}\to\text{观察忠实性}\to\text{可见逃逸}.
\end{aligned}
}
\]

最终判词是：

\[
\boxed{
\text{逃逸语义闭包的定义创造才严格增加可分辨结构（闭包内定义保持拓扑不变），}
\quad
\text{对角化证明固定语言不封闭，}
\quad
\text{拓扑记录这种增长在何种观察下可见。}
}
\]


---

# 第二十一部：机械历史的精确残差、存储容量与预测

本部把第 1、7、8、15 部的核与目标恢复问题具体化到 #6881 的历史一致性方向。取任意无理数 $0<\alpha<1$，不固定黄金斜率，也不限制窗口长度为 Fibonacci 数。这里区分三个对象：实际发生的字、字的无损表示，以及与后继交换的自主状态表示。后两者不能仅由相同的状态数相互替代。

## 21.1 实际历史，而非独立边见证

固定实截距 $\rho$，设

$$
a_{\alpha,\rho}(i)=\lfloor\rho+(i+1)\alpha\rfloor-\lfloor\rho+i\alpha\rfloor,
\qquad i\in\mathbb N.
$$

它取值于 $\{0,1\}$。定义全部实际长度 $n$ 字的集合

$$
W_n=\{(a_{\alpha,\rho}(i+k))_{0\le k<n}:i\in\mathbb N\}.
$$

同一字在不同位置出现仍只计一个元素。任何 $W_{n+h}$ 的截断来自同一个起点；反向，每个 $W_n$ 的起点都产生一个 $W_{n+h}$ 延伸。因此前缀映射 $\pi_{n,h}:W_{n+h}\to W_n$ 满射。

已有 `MechanicalFactorComplexity.lower_mechanical_factor_complexity` 给出 $|W_n|=n+1$。`MechanicalHistoryCapacity.image_ofFn` 证明有限函数表示与该既有 List 表示逐字相同，再运输基数结论。当 $h>0$，$n+h+1>n+1$，故 $\pi_{n,h}$ 不可能单射。选择两条不同长字的实际起点，得到

$$
\exists i,j,\quad W_n(i)=W_n(j),\qquad W_{n+h}(i)\ne W_{n+h}(j).
$$

这不是给有限图增加一条假定的边，而是给出具有共同短历史的两个实际自然数起点。对应声明为 `actual_future_collision`。经典 Sturmian 特殊词与禁止词背景见 G. Fici, *A Characterization of Bispecial Sturmian Words*, arXiv:1204.1672, 2012；这里不把经典 $n+1$ 复杂度或其分支推论重新声称为发现。

## 21.2 存储定理与 21、60、64 的不同来源

**定理。** 对任意有限集合 $X$，存在无损 $b$ 位二进制编码当且仅当 $|X|\le2^b$。

**证明。** 必要性为单射基数不等式。充分性选择 $X\simeq\operatorname{Fin}(|X|)$ 和 $\{0,1\}^b\simeq\operatorname{Fin}(2^b)$，在中间使用初始区间包含。没有对更新规则施加条件。对应 `bit_encoding_iff`。因此

$$
W_n\text{ 可无损编码为 }b\text{ 位}\iff n+1\le2^b.
$$

这是一条适用于全部 $n,b$ 的曲线。$|W_{59}|=60$、$|W_{63}|=64$、$|W_{64}|=65$ 是其不同点；六位足以编码 $W_{63}$，不足以编码 $W_{64}$。对应 `history_bit_encoding_iff` 与 `six_bit_history_cutoff`。

#6881 的另一对象是容量盒

$$
C_{5040}=\{0,\ldots,4\}\times\{0,1,2\}\times\{0,1\}\times\{0,1\}.
$$

它有 $5\cdot3\cdot2\cdot2=60$ 个状态，最少需要六个二进制位，每个单射六位编码均留下恰好四个未用码字。对应 `capacity5040_card`、`capacity5040_min_bits`、`capacity5040_unused`。

相对地，六个 Zeckendorf 数位禁止相邻两个 1，因而其合法窗口数是 $G_6=21$；原始六位二进制字段的全部码字数才是 $2^6=64$。这里的逻辑是

$$
\text{载体与约束}\longrightarrow |X|\longrightarrow\min\{b:|X|\le2^b\},
$$

而不是 $21\to34\to55\to60\to64$ 的动力递推。容量盒和某个历史集合即使等势，也没有因此得到保持后继的共轭。Fibonacci 深度字典属于另一项必须保留读数与端点的结构定理。

## 21.3 有限存储不蕴含有限自主动力闭合

**定理。** 上述无理机械字不存在有限的精确自主状态模型。

**证明。** 假设有限 $C$ 上存在固定更新 $F:C\to C$、输出 $o:C\to\{0,1\}$ 和状态序列 $q:\mathbb N\to C$，满足

$$
q(i+1)=F(q(i)),\qquad o(q(i))=a_{\alpha,\rho}(i).
$$

若两个起点状态相同，归纳得到其所有后续状态相同，因而任意长度的输出字相同。为每个 $W_n$ 元素选择一个实际起点并取该起点状态，得到单射 $W_n\hookrightarrow C$，所以 $n+1\le|C|$ 对所有 $n$ 成立。取 $n=|C|$ 即矛盾。对应 `model_capacity_bound` 与 `no_finite_autonomous_model`。证毕。

该结论排除全部有限容量，而不只 60 或 64。它不排除有外部输入的自动机、DFAO、含外部时钟的系统或一般可计算生成。无损地记录一个固定有限目标，与用固定有限自主状态永远精确更新，是不同数学要求。

## 21.4 不使用分裂公理的两侧轨迹

对整数 $m,t$ 定义实际双向机械轨迹

$$
\ell_m(t)=\lfloor(t+1-m)\alpha\rfloor-\lfloor(t-m)\alpha\rfloor,
$$
$$
u_m(t)=\lceil(t+1-m)\alpha\rceil-\lceil(t-m)\alpha\rceil.
$$

**定理。** 它们均为二值轨迹，且

$$
\ell_m(t)\ne u_m(t)\iff t\in\{m-1,m\}.
$$

**证明。** 当整数 $k\ne0$，$k\alpha$ 非整数，故 $\lceil k\alpha\rceil=\lfloor k\alpha\rfloor+1$。在 $t\notin\{m-1,m\}$ 时两个修正相消。在另外两个时刻，分别直接得到

$$
(\ell_m(m-1),\ell_m(m))=(1,0),\qquad
(u_m(m-1),u_m(m))=(0,1).
$$

普通 floor 增量不等式给出下机械轨迹二值性，上轨迹由两点交换得到。时间平移满足 $\ell_m(t+1)=\ell_{m-1}(t)$ 及同样的上轨迹公式。对应 `MechanicalPastSeparation.disagree_iff`、`lower_binary`、`upper_binary`、`lower_shift`、`upper_shift`。证毕。

所以这里有实际轨迹、实际后继和完整的共同见证，没有把待证的分裂行为放入结构字段当作公理。

## 21.5 整个过去不能改善统一的覆盖阈值

令 $\mathrm{PastEq}_J(v,w)$ 表示所有起点 $t\le0$ 的长度 $J$ 窗口都相同；特别地，当前窗口包括采样位置 $0,\ldots,J-1$。令 $\mathrm{SegmentEq}_{L,h}$ 表示起点 $0,\ldots,h$ 的全部长度 $L$ 窗口都相同。

**定理。** 对 $L>0$，在上一节定义的双侧边界轨道上，

$$
[\forall v,w,\ \mathrm{PastEq}_J(v,w)\Rightarrow
\mathrm{SegmentEq}_{L,h}(v,w)]\iff L+h\le J.
$$

**证明。** 若 $L+h\le J$，目标中的所有采样位置已在当前窗口中，该方向对任意轨迹成立。否则取 $m=L+h>J$。对每个 $t\le0$ 和 $0\le k<J$，$t+k\le J-1<m-1$，因此整个过去的所有观察相同。但终点窗口的最后一个采样位置 $h+L-1=m-1$ 恰有分歧。对应 `whole_past_prediction_iff` 与其显式见证 `invisible_past_visible_future`。证毕。

这是一条所有无理斜率都成立的完整量词结论。它同时指出“历史很长”与“目标相关的核已经消失”不是同一件事。越过两点后两条轨迹的后续读数重新相同，但此前整段的差异并未消失，也不能把完整双向轨迹说成同一个状态。

这里的 $J,L$ 是机械字采样长度，**不是未经证明替换后的 Zeckendorf 数位深度**。#6881 的原理论字典 $P_L\leftrightarrow B_{G_L-1}$ 若以完整端点约定运输，则对应阈值变为 $G_J\ge G_L+h$；该完整字典在本部源码中未重新建立。已有 `MechanicalGoldenBridge.lowerMechanicalWord_golden` 只提供相应黄金首字母的桥接，不能替代全部无限位字典。

## 21.6 进一步推论：任意采样位置的精确目标判据

下面直接从两点分歧定理推导，不再限制采样为连续窗口。给定任意集合 $A,B\subseteq\mathbb Z$，分别表示已观测位置与目标位置，定义

$$
D(A)=\{m:m-1\in A\ \text{或}\ m\in A\}=A\cup(A+1).
$$

比较的是同一个边界 $m$ 的实际两侧 $(\ell_m,u_m)$。由第 21.4 节，它们在 $A$ 上相等当且仅当 $m\notin D(A)$。所以全部目标相关的边界对残差，精确为

$$
\boxed{R(A;B)=D(B)\setminus D(A).}
$$

因此，在这整族实际成对边界上，

$$
\boxed{\text{已知 }A\text{ 足以确定目标 }B\iff D(B)\subseteq D(A).}
$$

加入新观察集合 $C$ 时，

$$
R(A\cup C;B)=R(A;B)\setminus D(C).
$$

这把本卷的目标残差公式具体化为可计算的整数集合关系。对应 `MechanicalBoundarySampling.residual_eq`、`pair_target_recovery_iff` 与 `residual_after_samples`。它分析完整的同边界两侧族，但**不冒充任意两个不同相位之间的全状态恢复判据**。

连续观察是其特例：对自然数 $J,M$，取 $A=\{t:t<J\}$、$B=\{0,\ldots,M-1\}$，得到

$$
R(A;B)=\{m:J<m\le M\}.
$$

对应 `past_to_segment_residual`；其元素数为 $(M-J)_+$。空目标区间也成立。这里 $A$ 表示完整标量采样过去；它与 $\mathrm{PastEq}_J$ 的采样并集等同需要 $J>0$，不能把空窗口的过去误当成所有负时间样本。

**有限采样下界。** 若有限采样集合 $S$ 区分某个有限边界指标集合 $R$ 中的每一对，则

$$
R\subseteq S\cup(S+1),\qquad |R|\le2|S|.
$$

所以至少需要 $\lceil|R|/2\rceil$ 次点观察。证明为上一判据加上有限并集基数不等式；对应 `boundary_probe_lower_bound`。这只是这族真实残差对的必要下界，不声称已经构造所有相位上的最优观察器。

## 21.7 对一般数学定理的解释及后续承重问题

设全部背景假设定义相容域 $\mathcal S_\Gamma$，已有事实为读数 $E$，目标为 $F$。问题仍是

$$
\ker(E|_{\mathcal S_\Gamma})\subseteq\ker(F|_{\mathcal S_\Gamma}),
$$

而非恢复整个 $\mathcal S_\Gamma$ 中的对象。值域应先限制为实际像；已有 `HistoryPayloadFactorization.ker_beta_subset_ker_payload_iff_unique_factorization` 给出包含空域情形的唯一因子判据，不需要重复另建通用真源。

第 21.6 节说明，真实推进可以是推导一个目标残差的封闭表达式，并证明新事实究竟删除哪部分残差，而不只是给已知事实添加名称。功能可观察性文献也区分目标函数恢复和全状态恢复：C. Kravaris, *On Functional Observability of Nonlinear Systems and the Design of Functional Observers with Assignable Error Dynamics*, arXiv:2501.00167, 后刊于 IFAC-PapersOnLine 59(19), 668–673 (2025)；I. Krauss, V. G. Lopez, M. A. Müller, *On Sample-Based Functional Observability of Linear Systems*, IEEE Control Systems Letters 9, 1393–1398 (2025), arXiv:2506.23744。本文没有把它们的连续微分或线性秩条件套用于上述离散系统。

第 21.8 节将进一步排除一个看似自然、但错误的充分性推广。下一项需要独立证明的具体结构是：构造无限 Zeckendorf 载体到机械 itinerary 的双向字典，逐一保持自然数核心、读数、时间平移及每个分裂端点的侧别。完成后才能把这里的全斜率采样定理运输成 #6881 的全部数位深度预测定理，而不是只比较 Fibonacci 基数。再下一项是完整分类无限过去的相容纤维，并在全载体上检验稀疏观察的充分性；当前成对边界判据及 $|R|\le2|S|$ 为其提供必要条件，但没有预设该条件对全载体充分。


## 21.8 再进一步：边界覆盖不是全状态恢复的充分条件

**定理。** 即使 $D(B)\subseteq D(A)$，不同边界或相位之间也可能出现相同已知观察、不同目标值。

**证明。** 对任意 $1/4<\alpha<1/3$，取两条实际下机械轨迹 $v=\ell_0$、$w=\ell_{-2}$。由

$$
\lfloor\alpha\rfloor=\lfloor2\alpha\rfloor=\lfloor3\alpha\rfloor=0,
\qquad \lfloor4\alpha\rfloor=\lfloor5\alpha\rfloor=1,
$$

得到

$$
(v(0),v(1),v(2))=(0,0,0),\qquad
(w(0),w(1),w(2))=(0,1,0).
$$

令 $A=\{0,2\}$、$B=\{1\}$，则 $D(B)=\{1,2\}\subseteq\{0,1,2,3\}=D(A)$，但 $v|_A=w|_A$ 且 $v|_B\ne w|_B$。对应 `boundary_cover_not_full_recovery`。该族对区间内的每个无理斜率成立，并非脱离机械系统的任意反例。证毕。

因此第 21.6 节的精确判据必须保持其成对边界作用域。全局正向定理还必须处理不同相位分量得到相同观察字的情形。正确的进一步问题不是继续假设边界覆盖充分，而是刻画带有观察字标签的相位分割：同一个观察字的所有分量必须在目标上取同一个值。这重新落在本卷已有的核包含判据中，并给出了具体必须处理的非局部障碍。

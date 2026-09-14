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

**假设。** 以下固定无理数 $0<\alpha<1$；窗口长度为任意自然数。

## 21.1 实际历史与前缀碰撞

**定义。** 固定实截距 $\rho$，令

$$
a_{\alpha,\rho}(i)=\lfloor\rho+(i+1)\alpha\rfloor-\lfloor\rho+i\alpha\rfloor,
\qquad i\in\mathbb N.
$$

定义起点 $i$ 的长度 $n$ 字 $W_n(i)=(a_{\alpha,\rho}(i+k))_{0\le k<n}$，以及全部实际长度 $n$ 字的集合

$$
W_n=\{W_n(i):i\in\mathbb N\}.
$$

**定理。** $a_{\alpha,\rho}(i)\in\{0,1\}$，$|W_n|=n+1$，且对任意 $n,h\in\mathbb N$，前缀映射 $\pi_{n,h}:W_{n+h}\to W_n$ 满射。若 $h>0$，则

$$
\exists i,j,\quad W_n(i)=W_n(j),\qquad W_{n+h}(i)\ne W_{n+h}(j).
$$

**证明。** 由于 $0<\alpha<1$，每个 floor 增量为 $0$ 或 $1$。令 $x=\{\rho+i\alpha\}$。字的前 $k$ 位之和为 $\lfloor x+k\alpha\rfloor$；当 $x$ 走过 $[0,1)$ 时，对 $1\le k\le n$，第 $k$ 个和恰在 $x=1-\{k\alpha\}$ 改变一次。这 $n$ 个点因 $\alpha$ 无理而互异，故所得前缀和向量恰有 $n+1$ 种，且相邻区间的向量不同、各坐标随 $x$ 不减，因此全部向量互异。轨道 $\{\rho+i\alpha\}$ 在圆周上稠密，每个区间均有实际起点；落在端点时的 floor 值与其右侧区间相同。故 $|W_n|=n+1$，空字情形亦然。每个实际短字在同一起点有长度 $n+h$ 的延伸，所以 $\pi_{n,h}$ 满射。若 $h>0$，则 $|W_{n+h}|=n+h+1>n+1=|W_n|$；满射不可能同时单射。取同一前缀的两个不同长字及其实际起点即得结论。

## 21.2 二进制编码与三种有限载体的基数

**定理。** 对任意有限集合 $X$，存在无损 $b$ 位二进制编码当且仅当 $|X|\le2^b$。

**证明。** 无损编码是单射 $X\hookrightarrow\{0,1\}^b$，必要性为单射基数不等式。充分性选择 $X\simeq\operatorname{Fin}(|X|)$ 和 $\{0,1\}^b\simeq\operatorname{Fin}(2^b)$，在中间使用初始区间包含。

**定理。** 对任意 $n,b\in\mathbb N$，

$$
W_n\text{ 可无损编码为 }b\text{ 位}\iff n+1\le2^b.
$$

特别地，$|W_{59}|=60$、$|W_{63}|=64$、$|W_{64}|=65$；六位足以编码 $W_{63}$，不足以编码 $W_{64}$。

**证明。** 由第 21.1 节的 $|W_n|=n+1$ 代入上一编码定理；$2^6=64$，而 $65>64$。

**定义。** 容量盒为

$$
C_{5040}=\{0,\ldots,4\}\times\{0,1,2\}\times\{0,1\}\times\{0,1\}.
$$

**定理。** $|C_{5040}|=60$；其最短无损二进制编码需六位，且每个单射六位编码恰有四个未用码字。

**证明。** 乘法原理给出 $5\cdot3\cdot2\cdot2=60$。由 $2^5=32<60\le64=2^6$ 得最小位数，且单射的像有 $60$ 个元素，故余下 $64-60=4$ 个码字。

**定义。** 令 $G_k$ 为长度 $k$、数位取 $0$ 或 $1$ 且不含相邻两个 $1$ 的字数。

**定理。** $G_6=21$，而全部六位二进制字有 $64$ 个。

**证明。** 按末位分解合法字得 $G_0=1$、$G_1=2$、$G_k=G_{k-1}+G_{k-2}$，于是 $G_2,G_3,G_4,G_5,G_6$ 依次为 $3,5,8,13,21$。不加相邻数位约束则每一位有两个选择，故有 $2^6=64$ 个字。

**定义。** 对有限载体 $X$，其最小无损二进制位数为

$$
\min\{b:|X|\le2^b\}.
$$

**命题。** 有限集合等势不蕴含其给定自映射共轭。

**证明。** 在 $\{0,1\}$ 上分别取恒等映射与常值映射。若存在共轭，其双射须将前者的两个不动点送到后者的两个不动点；后者仅有一个不动点，矛盾。

## 21.3 有限存储不蕴含有限自主动力闭合

**定理。** 若集合 $C$ 上的固定更新 $F:C\to C$、输出 $o:C\to\{0,1\}$ 和状态序列 $q:\mathbb N\to C$ 满足下式，则对每个 $n$ 有 $|C|\ge n+1$；特别地，上述无理机械字不存在有限的精确自主状态模型。

$$
q(i+1)=F(q(i)),\qquad o(q(i))=a_{\alpha,\rho}(i).
$$

**证明。** 若两个起点状态相同，归纳得到其所有后续状态相同，因而任意长度的输出字相同。为每个 $W_n$ 元素选择一个实际起点并取该起点状态，得到单射 $W_n\hookrightarrow C$，所以 $n+1\le|C|$ 对所有 $n$ 成立。若 $C$ 有限，取 $n=|C|$ 即矛盾。

**定义。** 上一定理的自主模型要求 $F$ 仅以当前状态为自变量；带外部输入或时钟的更新不满足此定义。

## 21.4 双侧边界轨迹的分歧与平移

**定义。** 对整数 $m,t$ 定义双向机械轨迹

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

普通 floor 增量不等式给出下机械轨迹二值性，上轨迹由两点交换得到。

**定理。** 对所有 $m,t\in\mathbb Z$，$\ell_m(t+1)=\ell_{m-1}(t)$ 且 $u_m(t+1)=u_{m-1}(t)$。

**证明。** 将两侧定义中的 $t+1-m$ 改写为 $t-(m-1)$，其余项同理。

## 21.5 整个过去不能改善统一的覆盖阈值

**定义。** 令 $\mathrm{PastEq}_J(v,w)$ 表示所有起点 $t\le0$ 的长度 $J$ 窗口都相同；令 $\mathrm{SegmentEq}_{L,h}(v,w)$ 表示起点 $0,\ldots,h$ 的全部长度 $L$ 窗口都相同。

**定理。** 在上一节的双侧边界轨迹族上，对 $J,h\in\mathbb N$、$L>0$，

$$
[\forall v,w,\ \mathrm{PastEq}_J(v,w)\Rightarrow
\mathrm{SegmentEq}_{L,h}(v,w)]\iff L+h\le J.
$$

**证明。** 若 $L+h\le J$，目标中的所有采样位置已在起点 $0$ 的长度 $J$ 窗口中，该方向对任意轨迹成立。否则取 $m=L+h>J$ 及 $v=\ell_m,w=u_m$。对每个 $t\le0$ 和 $0\le k<J$，$t+k\le J-1<m-1$，因此整个过去的所有窗口相同。但终点窗口的最后一个采样位置 $h+L-1=m-1$ 恰有分歧。

**定理。** 对每个 $m$，$\ell_m$ 与 $u_m$ 在 $t<m-1$ 及 $t>m$ 时相同，在 $m-1,m$ 时不同，因而作为整个双向轨迹不相等。

**证明。** 直接应用第 21.4 节的分歧位置等式。

**假设。** 对每个数位深度 $k$，数位观察 $P_k$ 与长度 $G_k-1$ 的机械窗口观察 $B_{G_k-1}$ 存在保持读数、时间平移及两侧端点的双向字典。

**定理。** 在上述字典假设下，对应于第 21.5 节的数位深度预测阈值为 $G_J\ge G_L+h$。

**证明。** 由字典将机械采样长度分别取为 $G_J-1$、$G_L-1$，则第 21.5 节的阈值化为 $(G_L-1)+h\le G_J-1$，即所示不等式。

## 21.6 任意采样位置的边界对残差

**定义。** 给定观察位置 $A\subseteq\mathbb Z$，令

$$
D(A)=\{m:m-1\in A\ \text{或}\ m\in A\}=A\cup(A+1).
$$

对目标位置 $B\subseteq\mathbb Z$，定义同一边界的两侧轨迹对的目标残差

$$
R(A;B)=\{m:\ell_m|_A=u_m|_A,\ \ell_m|_B\ne u_m|_B\}.
$$

**定理。** 对任意 $A,B,C\subseteq\mathbb Z$，

$$
\boxed{R(A;B)=D(B)\setminus D(A),}
\qquad
\boxed{[\forall m,\ \ell_m|_A=u_m|_A\Rightarrow\ell_m|_B=u_m|_B]
\iff D(B)\subseteq D(A),}
$$
$$
R(A\cup C;B)=R(A;B)\setminus D(C).
$$

**证明。** 第 21.4 节给出 $\ell_m|_A=u_m|_A\iff m\notin D(A)$，以及 $\ell_m|_B\ne u_m|_B\iff m\in D(B)$。交集即为差集；残差为空当且仅当所示包含成立。最后 $D(A\cup C)=D(A)\cup D(C)$，对差集取补即得更新式。

**定理。** 对自然数 $J,M$，取 $A=\{t\in\mathbb Z:t<J\}$、$B=\{t\in\mathbb Z:0\le t<M\}$，则

$$
R(A;B)=\{m:J<m\le M\}.
$$

且 $|R(A;B)|=(M-J)_+:=\max(M-J,0)$，包括 $M=0$ 的情形。

**证明。** $D(A)=\{m:m\le J\}$，当 $M>0$ 时 $D(B)=\{1,\ldots,M\}$，空目标时 $D(B)=\varnothing$。取差集并计数即得。若 $J>0$，所有起点 $t\le0$ 的长度 $J$ 窗口采样位置的并集恰为 $\{t:t<J\}$；若 $J=0$，该并集为空，不能等同于此处的 $A$。

**定理。** 若有限采样集合 $S$ 区分某个有限边界指标集合 $R_0$ 中的每一对 $(\ell_m,u_m)$，则

$$
R_0\subseteq S\cup(S+1),\qquad |R_0|\le2|S|,
$$

从而 $|S|\ge\lceil|R_0|/2\rceil$。

**证明。** 每个 $m\in R_0$ 必在 $S$ 上呈现两侧分歧，所以 $m\in D(S)=S\cup(S+1)$。有限并集的基数至多为 $|S|+|S+1|=2|S|$，再取整数上整。

## 21.7 目标核与实际像上的因子

**定义。** 设背景假设确定相容域 $\mathcal S_\Gamma$，读数与目标分别为 $E:\mathcal S_\Gamma\to Y$、$F:\mathcal S_\Gamma\to Z$。写 $\ker E=\{(v,w):E(v)=E(w)\}$，并将 $E$ 的值域限制为实际像 $E(\mathcal S_\Gamma)$。

**定理。** 存在唯一映射 $f:E(\mathcal S_\Gamma)\to Z$ 使 $F=f\circ E$，当且仅当

$$
\ker(E|_{\mathcal S_\Gamma})\subseteq\ker(F|_{\mathcal S_\Gamma}),
$$

包括 $\mathcal S_\Gamma=\varnothing$ 的情形。

**证明。** 若 $F=f\circ E$，则 $E(v)=E(w)$ 蕴含 $F(v)=F(w)$。反之，对实际像中的 $y=E(v)$ 定义 $f(y)=F(v)$；核包含保证此定义不依赖 $v$ 的选择，且每个 $y$ 都有原像，故 $f$ 唯一。空域时实际像为空，空映射仍存在且唯一。


## 21.8 边界覆盖的全局反例

**命题。** 对任意无理数 $1/4<\alpha<1/3$，存在 $A,B\subseteq\mathbb Z$ 及不同边界的实际机械轨迹 $v,w$，使 $D(B)\subseteq D(A)$、$v|_A=w|_A$，但 $v|_B\ne w|_B$。

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

令 $A=\{0,2\}$、$B=\{1\}$，则 $D(B)=\{1,2\}\subseteq\{0,1,2,3\}=D(A)$，但 $v|_A=w|_A$ 且 $v|_B\ne w|_B$。

**定理。** 对任意轨迹集合 $\mathcal T$ 及采样集合 $A,B$，限制映射 $E_A(v)=v|_A$ 在 $\mathcal T$ 上决定 $F_B(v)=v|_B$，当且仅当每个相同观察字的纤维在目标上取同一个值。

**证明。** 对 $E_A,F_B$ 应用第 21.7 节的核包含判据；核包含恰说 $E_A(v)=E_A(w)$ 蕴含 $F_B(v)=F_B(w)$。上面的反例给出第 21.6 节同边界两侧判据不能替代这一条件的实例。
---

# 补编 RD：整数显示、实际黄金纤维与原始状态

## RD.1 原始数位、黄金求值与整数显示

**定义。** 令 $F_0=0,F_1=1,F_{i+2}=F_{i+1}+F_i$，$\varphi^2=\varphi+1$，并定义

$$
\mathcal R=\mathbb N^{(\mathbb N)},\qquad
v(r)=\sum_i r_iF_{i+2},\qquad
\beta(r)=\sum_i r_i\varphi^{i+2}\in\mathbb Z[\varphi].
$$

**命题。** 若 $\pi(a+b\varphi)=b$，则对每个 $r\in\mathcal R$ 有 $\pi(\beta(r))=v(r)$。

**证明。** 由 $\varphi^{i+2}=F_{i+1}+F_{i+2}\varphi$ 逐项取 $\varphi$ 的系数并求和即得。

**定义。** 若 $r_i\le1$ 且任意相邻两个系数不同时为一，则称 $r$ 为规范原始数位表。

**命题。** 在规范原始数位表中，整数显示 $v(r)$ 唯一确定 $r$；在全部 $\mathcal R$ 上，$v$ 不必为单射。若谓词 $P(v(r))$ 只依赖显示，则它在每个 $v$-纤维上恒定。

**证明。** 第一项是 Zeckendorf 唯一性。第二项例如由 $F_{i+4}=F_{i+3}+F_{i+2}$ 得到不同的原始表示。最后一项由函数复合的定义立即成立。

## RD.2 非负原始数位的完整黄金像

**定理 RD1。** 对 $z=a+b\varphi\in\mathbb Z[\varphi]$，

$$
\exists r\in\mathcal R:\beta(r)=z
\quad\Longleftrightarrow\quad
0\le a\le b\le2a.
$$

**证明。** $\varphi^2=1+\varphi$ 的系数位于该锥。乘以 $\varphi$ 将 $(a,b)$ 变成 $(b,a+b)$；若 $0\le a\le b\le2a$，则 $0\le b\le a+b\le2b$。故所有 $\varphi^{i+2}$ 均在锥内，非负整数线性组合仍在锥内。

反过来，置 $u=2a-b\ge0$、$w=b-a\ge0$，则

$$
u\varphi^2+w\varphi^3=(u+w)+(u+2w)\varphi=a+b\varphi.
$$

取 $r=u\delta_0+w\delta_1$。两个系数由 $u=2a-b,w=b-a$ 唯一决定，故这个两槽代表唯一。证毕。

**定理 RD2。** 对每个 $n\in\mathbb N$，

$$
\{\beta(r):v(r)=n\}
=\{a+n\varphi:a\in\mathbb Z,\ a\le n\le2a\}.
$$

该集合中的 $a$ 从 $\lceil n/2\rceil$ 到 $n$ 取遍每个整数，因而黄金像的数量为 $\lfloor n/2\rfloor+1$。

**证明。** 在 RD1 中固定第二坐标 $b=n$。所得闭整数区间含 $n-\lceil n/2\rceil+1=\lfloor n/2\rfloor+1$ 个整数。证毕。

## RD.3 显示对与全部移位观察

**定义。** 令 $\operatorname{shift}_k(r)$ 把每个槽号提高 $k$，并置

$$
v_k(r)=v(\operatorname{shift}_k(r)).
$$

**命题。** 对每个 $k\in\mathbb N$，

$$
\beta(\operatorname{shift}_k(r))=\varphi^k\beta(r),
\qquad v_k(r)=\pi(\varphi^k\beta(r)).
$$

**证明。** 对有限支撑和换元，再用幂的乘法法则及 RD.1 的求值命题。证毕。

**定理 RD3。** 对任意 $n,m\in\mathbb N$，

$$
\exists r:\ v(r)=n\ \land\ v_1(r)=m
\quad\Longleftrightarrow\quad
3n\le2m\ \land\ m\le2n.
$$

每个这样的 $r$ 都满足 $\beta(r)=(m-n)+n\varphi$。

**证明。** 写 $\beta(r)=a+n\varphi$，乘以 $\varphi$ 后读数为 $m=a+n$。RD1 的 $a\le n\le2a$ 恰转成所列两项不等式。反向取 $a=m-n$，由两项不等式及 RD1 构造 $r$。证毕。

**命题。** 当 $n\ge2$ 时，$m=2n$ 与 $m=2n-1$ 都可实现。因此在全部原始数位表上，显示 $n$ 唯一确定黄金像当且仅当 $n\le1$；在规范原始数位表上，每个 $n$ 都由 Zeckendorf 唯一性确定唯一黄金像。

**证明。** 将两个 $m$ 分别代入 RD3；当 $n\ge2$ 时两者不同。$n=0,1$ 的结论由 RD2 的区间直接检验。规范情形由 RD.1 的唯一性。证毕。

**定理 RD4。** 对原始输入 $r,s$，

$$
\beta(r)=\beta(s)
\iff (v(r),v_1(r))=(v(s),v_1(s))
\iff \forall k\in\mathbb N,\ v_k(r)=v_k(s),
$$

并且

$$
v_{k+2}(r)=v_{k+1}(r)+v_k(r).
$$

**证明。** 相同黄金元素乘以每个 $\varphi^k$ 后仍相同。反向由第零与第一读数及 RD3 的恢复式得到两个黄金坐标。递推由 $\varphi^{k+2}=\varphi^{k+1}+\varphi^k$ 乘以 $\beta(r)$ 后取第二坐标得到。证毕。

## RD.4 规范化电荷及其精确谱

**定义。** 令 $\nu(r)$ 为 $r$ 的规范化，$c(r)\in\mathbb Z$ 为进位过程的有符号计数，并假设

$$
\beta(r)-\beta(\nu(r))=c(r)\in\mathbb Z\subset\mathbb Z[\varphi].
$$

再令 $a_0(n)$ 为 $v=n$ 的唯一规范表示之黄金像的常数坐标，则

$$
\beta(r).a=a_0(v(r))+c(r).
$$

**定理 RD5。** 对每个显示 $n$，

$$
\{c(r):v(r)=n\}
=\{c\in\mathbb Z:a_0(n)+c\le n\le2(a_0(n)+c)\},
$$

并且

$$
\beta(r)=\beta(s)
\iff v(r)=v(s)\ \land\ c(r)=c(s).
$$

**证明。** 将 $\beta(r).a=a_0(v(r))+c(r)$ 代入 RD2 得到必要性。反向，对每个满足区间条件的 $a=a_0(n)+c$，RD2 给出一个 $r$；电荷恒等式迫使其电荷等于 $c$。最后的等价由黄金元素的两个坐标直接得到。证毕。

**定理 RD6。** 规范化前后的全部移位读数满足

$$
\boxed{v_k(r)-v_k(\nu(r))=F_kc(r).}
$$

因此规范化保留所有移位读数当且仅当 $c(r)=0$。

**证明。** 将电荷恒等式乘以 $\varphi^k$ 后取第二坐标，并用 $\pi(\varphi^k)=F_k$。必要性取 $k=1$，充分性令电荷为零。证毕。

## RD.5 黄金恢复与原始规范性的分离

**定理 RD7。** 对每个 $i\in\mathbb N$，存在两个原始数位表 $r,s$，其所有移位整数读数相同，但一个规范，另一个非规范并可执行一次进位。

**证明。** 取

$$
r=\delta_{i+2},\qquad s=\delta_i+\delta_{i+1}.
$$

由 $\varphi^{i+4}=\varphi^{i+2}+\varphi^{i+3}$ 得 $\beta(r)=\beta(s)$，RD4 遂给出全部移位读数相同。$r$ 只有一个系数为一，故规范；$s$ 在相邻位置同时为一，故非规范，并可把这两个相邻单位进位成 $r$。证毕。

**定理。** 不存在谓词 $H:(\mathbb N\to\mathbb N)\to\mathrm{Prop}$ 使得

$$
\forall r,\quad r\text{ 规范}\iff H((v_k(r))_{k\ge0}).
$$

**证明。** RD7 中的 $r,s$ 有相同的整段观察，却有不同的规范性；任何只依赖观察序列的 $H$ 必须给它们相同真值，矛盾。证毕。

---

# 补编 PT：整路径概率、观察闭合与可逆投影记忆

## PT.1 有限路径律与条件路径律

**定义。** 设状态空间为 $X$，观察为 $q:X\to Y$，一步核为 $K:X\to\operatorname{PMF}(X)$，初始律为 $\mu$。长度 $n$ 的路径律定义为

$$
\mathbb P_K(x_0,\ldots,x_n)=\mu(x_0)\prod_{j=0}^{n-1}K(x_j)(x_{j+1}).
$$

**定义。** 若事件 $E$ 只依赖观察路径且 $\mathbb P_K(E)>0$，则端点或其他路径约束下的条件律为

$$
\mathbb P_K(\,cdot\mid E)=\frac{\mathbb P_K(E\cap\cdot)}{\mathbb P_K(E)}.
$$

**命题。** 路径律要求相邻转移共享同一个中间状态 $x_j$；逐边分别存在隐藏见证不能推出整条观察路径存在共同隐藏实现。

**证明。** 路径权重的相邻因子 $K(x_{j-1})(x_j)$ 与 $K(x_j)(x_{j+1})$ 含同一个 $x_j$。若逐边见证不同，乘积中不存在相应的共同变量赋值。证毕。

## PT.2 全部移位读数下的进位闭合失败

**定义。** 沿用 RD 的 $\mathcal R,\beta,v_j,c$，令 $T$ 每次处理最低的重数至少为二的槽。

**定理 PT1。** 对每个 $k\ge0$，存在两个非规范原始对象 $r_k,s_k$，满足

$$
v_0(r_k)=v_0(s_k)=6+8k,\qquad
\beta(r_k)=\beta(s_k),\qquad
\forall j\ge0,\ v_j(r_k)=v_j(s_k),\qquad c(r_k)=c(s_k),
$$

两边都可执行一次进位，但

$$
\beta(Tr_k)+1=\beta(Ts_k).
$$

**证明。** 取

$$
r_k=2\delta_0+2\delta_1+k\delta_4,\qquad
s_k=2\delta_2+k\delta_4.
$$

两者的黄金值均为 $(4+5k)+(6+8k)\varphi$，故由 RD4 得到全部移位读数相同，并由 RD5 得到总电荷相同。两者均有重数二的槽，所以都非规范。按最低重复槽进位，

$$
Tr_k=3\delta_1+k\delta_4,\qquad
Ts_k=\delta_0+\delta_3+k\delta_4.
$$

由 $\varphi^2+\varphi^5-3\varphi^3=1$ 得结论。证毕。

**定理。** 不存在从“全部移位读数序列与当前规范性真值”恢复下一黄金值 $\beta(Tr)$ 的函数。

**证明。** PT1 的两对象具有相同的全部移位读数，并且当前都非规范，而其下一黄金值不同。证毕。

## PT.3 强可合并性与整路径下降

**假设。** 存在观察像上的一步核 $L$，使每个 $x\in X$ 都满足

$$
q_\#K(x)=L(q(x)).
$$

**定理 PT2。** 在上述假设下，对任意 $n$ 和任意初始分布，

$$
(q^{n+1})_\#\mathbb P_K=\mathbb P_L.
$$

因此每个观察路径统计量 $F:Y^{n+1}\to Z$ 的分布相同。

**证明。** 对路径长度归纳。长度零时结论是初态推前。设长度 $n$ 已成立；生成长度 $n+1$ 路径时，先按 $K(x)$ 选择共同后继，再生成后段。归纳假设把后段推前换成 $L$ 的后段，一步假设把后继观察的分布换成 $L(q(x))$。这正是商路径的递归定义。最后对初态混合，并对 $F$ 再推前。证毕。

**定义。** 若观察历史 $h=(y_0,\ldots,y_t)$ 的概率非零，令

$$
\nu_h=\operatorname{Law}(X_t\mid Y_{0:t}=h).
$$

**命题。** 下一观察分布为

$$
\sum_{x\in q^{-1}(y_t)}\nu_h(x)\,q_\#K(x).
$$

**证明。** 对条件事件 $X_t=x$ 应用全概率公式。证毕。

## PT.4 Koopman 观察闭合与两步记忆

**定义。** 令 $K$ 为有限维实观察函数空间上的一步转移算子，$P^2=P$，$Q=I-P$，并定义

$$
\overline K=PKP,\qquad
\Delta_2=PK^2P-\overline K^2,\qquad
B=QKP.
$$

**定理 PT3。** 有

$$
\boxed{\Delta_2=PKQKP.}
$$

**证明。** $\overline K^2=PKP^2KP=PKPKP$。在 $K^2$ 的两个 $K$ 之间插入 $P+Q=I$ 后相减。证毕。

**定理 PT4。** 若 $P^*=P$、$K^*=K$，则

$$
\boxed{\Delta_2=B^*B},\qquad
\boxed{\Delta_2=0\iff QKP=0\iff KP=PKP}.
$$

**证明。** $B^*=PKQ$ 且 $Q^2=Q$，故 $B^*B=PKQKP$。实矩阵的 Gram 矩阵为零当且仅当原矩阵为零，再展开 $QKP=KP-PKP$。证毕。

**定理 PT5。** 在 PT4 的条件下，

$$
\Delta_2=0
\iff
\forall m\ge1,\quad PK^mP=(PKP)^m.
$$

**证明。** 由 $KP=PKP$ 对 $m$ 归纳，将最右侧的 $KP$ 替换成 $PKP$。反向取 $m=2$。证毕。

**命题。** PT4 的自伴条件不可删除。

**证明。** 取

$$
P=\operatorname{diag}(1,0),\qquad
K=\begin{pmatrix}0&0\\1&0\end{pmatrix}.
$$

则 $K^2=0$、$PKP=0$，所以 $\Delta_2=0$，但 $QKP=K\ne0$。证毕。

## PT.5 同一平衡分布下的不同路径动力

**定理 PT6。** 对 $a,b\ge0$、$a+b\le1$，取

$$
K_{a,b}=\begin{pmatrix}
1-a&a&0\\
a&1-a-b&b\\
0&b&1-b
\end{pmatrix},\qquad
P=\begin{pmatrix}
1/2&1/2&0\\
1/2&1/2&0\\
0&0&1
\end{pmatrix}.
$$

则 $K_{a,b}$ 非负、行和为一且对称，并对全部参数共享平衡分布 $(1/3,1/3,1/3)$。此外

$$
\Delta_2=\frac{b^2}{8}
\begin{pmatrix}1&1&-2\\1&1&-2\\-2&-2&4\end{pmatrix}.
$$

因此 $\Delta_2(2,2)=b^2/2$，且观察空间闭合当且仅当 $b=0$。

**证明。** 非负性、行和、对称性与平衡分布逐行直接检验。把 $K_{a,b}$ 与 $P$ 代入 PT3 并作矩阵乘法得到所示缺陷；该矩阵为零当且仅当 $b=0$。证毕。

**定理。** 不存在仅从平衡向量恢复转移项 $K(1,2)$ 的函数。

**证明。** 固定 $a=1/4$，分别取 $b=1/4$ 与 $b=1/2$。两个链具有同一平衡向量，而 $K(1,2)=b$ 不同。证毕。

---

# 补编 MF：隐藏初态、历史反馈与反事实的区别

## MF.1 投影分量与反事实对合

**定义。** 在线性状态空间中令 $x_{n+1}=Tx_n$，$P^2=P$，$Q=I-P$。则 $x_n=Px_n+Qx_n$。观察纤维为

$$
\{z:Pz=Px_n\}=x_n+\ker P.
$$

**命题。** 令 $S=2P-I$，则

$$
S^2=I,\qquad PS=P,\qquad QS=-Q,
$$

并且

$$
PT^nx-PT^nSx=2PT^nQx.
$$

**证明。** 使用 $P^2=P$ 展开前三式；又由 $x-Sx=2Qx$，左乘 $PT^n$ 得最后一式。证毕。

## MF.2 隐藏初态与记忆核的精确消元

**定义。** 令可见变量 $y_n\in V$、隐藏变量 $h_n\in H$ 满足

$$
y_{n+1}=Ay_n+Bh_n,\qquad h_{n+1}=Cy_n+Dh_n.
$$

**定理 MF1。** 对全部初态与 $n\ge0$，

$$
h_n=D^nh_0+\sum_{i=0}^{n-1}D^{n-1-i}Cy_i,
$$

并且

$$
\boxed{y_{n+1}=Ay_n+BD^nh_0+\sum_{i=0}^{n-1}BD^{n-1-i}Cy_i.}
$$

**证明。** $n=0$ 时和为空。把 $h_n$ 的表达式代入 $h_{n+1}=Cy_n+Dh_n$，幂次增加一，再把 $Cy_n$ 作为末项加入求和，完成归纳。最后左乘 $B$ 并代入可见更新。证毕。

**定义。** 令

$$
\eta_n=BD^nh_0,\qquad M_j=BD^jC.
$$

$\eta_n$ 是初始隐藏条件的影响，$M_j$ 是可见量进入隐藏通道、传播 $j$ 次再返回的反馈算子。

## MF.3 静默子空间与目标相关隐藏商

**定义。** 令

$$
\mathcal N_H=\bigcap_{n\ge0}\ker(BD^n).
$$

**定理 MF2。** 从 $(0,h)$ 出发的全部可见量恒为零，当且仅当 $h\in\mathcal N_H$。

**证明。** 若可见量一直为零，则 $h_n=D^nh$，下一步可见量为 $BD^nh=0$。反之，若全部 $BD^nh=0$，归纳可得轨迹为 $(0,D^nh)$，其可见量恒为零。证毕。

**命题。** 初始可见量相同的 $(y,h)$ 与 $(y,h')$ 给出相同的全部可见未来，当且仅当 $h-h'\in\mathcal N_H$。因此可见未来所区分的隐藏信息是商空间 $H/\mathcal N_H$。

**证明。** 两条线性轨迹相减后应用 MF2。证毕。

**命题。** 全部反馈核 $M_j$ 为零当且仅当 $\operatorname{range}C\subseteq\mathcal N_H$；这不蕴含任意隐藏初态对未来可见量无影响。

**证明。** $M_j=BD^jC=0$ 对全部 $j$ 成立，恰等价于每个 $Ch$ 属于所有 $\ker(BD^j)$。反例为

$$
y_{n+1}=y_n+h_n,\qquad h_{n+1}=h_n,
$$

其中 $A=B=D=1,C=0$，故 $M_j=0$，但 $y_n=y_0+nh_0$。证毕。

## MF.4 三态链的全部记忆系数

**定义。** 沿用 PT6 的 $K_{a,b},P$，令 $Q=I-P$，并在隐藏方向 $(1,-1,0)$ 上置

$$
\lambda=1-2a-b/2,\quad D=QK_{a,b}Q,\quad C=QK_{a,b}P,\quad B=PK_{a,b}Q.
$$

**定理 MF3。** 对所有实参数和 $j\in\mathbb N$，

$$
\boxed{M_j=BD^jC=\lambda^j\Delta_2,\qquad
\Delta_2=PK_{a,b}^2P-(PK_{a,b}P)^2.}
$$

**证明。** 直接计算得 $DC=\lambda C$，归纳得 $D^jC=\lambda^jC$。又因 $Q^2=Q$，$BC=PK_{a,b}QK_{a,b}P=\Delta_2$。证毕。

**命题。** 有

$$
(M_j)_{22}=\frac{b^2}{2}\lambda^j.
$$

若 $a\ge0,b>0,a+b\le1$，则 $-1<\lambda<1$，并且对 $m\ge0$，

$$
\sum_{j=m}^{\infty}|(M_j)_{22}|=
\frac{b^2|\lambda|^m}{2(1-|\lambda|)}.
$$

**证明。** 第一式由 PT6 的 $\Delta_2(2,2)=b^2/2$ 与 MF3 得到。上界 $\lambda<1$ 来自 $b>0$，下界由 $a\le1-b$ 得 $\lambda\ge-1+3b/2>-1$。最后对几何级数求和。证毕。

**命题。** 在 $a\ge0,b>0,a+b\le1$ 下，若 $\lambda\ne0$，则每个滞后的 $(M_j)_{22}$ 都非零；若 $\lambda=0$，则只有 $j=0$ 项非零。若 $b=0$，则全部反馈核为零。

**证明。** 直接代入 $(M_j)_{22}=b^2\lambda^j/2$；当 $b=0$ 时由 PT6 得 $\Delta_2=0$，再用 MF3。证毕。

## MF.5 无限记忆核与有限阶状态实现

**定义。** 写

$$
x_n=(s_n+h_n,s_n-h_n,r_n),\qquad y_n=(s_n,r_n).
$$

则 PT6 的矩阵给出

$$
y_{n+1}=A_vy_n+B_vh_n,\qquad h_{n+1}=C_vy_n+\lambda h_n,
$$

其中

$$
A_v=\begin{pmatrix}1-b/2&b/2\\b&1-b\end{pmatrix},\quad
B_v=\begin{pmatrix}b/2\\-b\end{pmatrix},\quad
C_v=\begin{pmatrix}b/2&-b/2\end{pmatrix}.
$$

**命题。** 可见向量满足二阶递推

$$
\boxed{y_{n+2}=(A_v+\lambda I)y_{n+1}+(B_vC_v-\lambda A_v)y_n.}
$$

**证明。** 由 $B_vh_n=y_{n+1}-A_vy_n$，将隐藏更新代入下一步可见更新并整理。证毕。

**命题。** 对黄金乘法 $a+e\varphi\mapsto e+(a+e)\varphi$，取可见量 $y=e$、隐藏量 $h=a$，则 $A=B=C=1,D=0$，从而

$$
\eta_0=a_0,\quad \eta_n=0\ (n>0),\quad M_0=1,\quad M_j=0\ (j>0),
$$

并且 $y_{n+1}=y_n+y_{n-1}$（$n\ge1$），$a_0=y_1-y_0$。

**证明。** 把 $a+e\varphi$ 乘以 $\varphi$ 并用 $\varphi^2=\varphi+1$；其余各式代入 MF1 即得。证毕。

## MF.6 退化耦合附近的恢复稳定性

**命题。** 当 $b\ne0$ 时，已知 $s_0,r_0,r_1$ 可恢复

$$
h_0=\frac{bs_0+(1-b)r_0-r_1}{b}.
$$

**证明。** 由 MF.5 的第三坐标更新式解出 $h_0$。证毕。

**定理 MF4。** 对任意 $C_0>0$，取

$$
a=1/4,\qquad b=\frac1{4(C_0+1)},\qquad
x=(1/2,0,1/2),\quad z=(0,1/2,1/2).
$$

则 $x,z$ 非负且质量为一，参数满足严格随机条件，并且

$$
Px=Pz,\qquad |(x_0-x_1)-(z_0-z_1)|=1,
$$

而

$$
PK_{a,b}x-PK_{a,b}z=(b/4,b/4,-b/2),\qquad
\|PK_{a,b}x-PK_{a,b}z\|_1=b,\qquad C_0b<1.
$$

**证明。** 逐坐标代入即得；$b>0$ 且 $a+b<1$，所以随机条件严格成立。又 $C_0b=C_0/(4(C_0+1))<1$。证毕。

**命题。** 在全部有效参数上，不存在于零误差处趋零的统一逆误差模来恢复隐藏对比。

**证明。** MF4 中隐藏对比差恒为一，而完整下一投影差的 $\ell^1$ 范数 $b$ 随 $C_0$ 任意趋近于零。证毕。

## MF.7 相容初态与后续候选

**定义。** 对固定观察序列 $y_0,\ldots,y_n$，令

$$
\mathcal F_n=\{x_0:PT^kx_0=y_k\text{ 对 }0\le k\le n\}.
$$

对应的第 $j$ 步后续候选集合为

$$
\{PT^{n+j}x_0:x_0\in\mathcal F_n\}.
$$

**命题。** 增加一个观察约束会把 $\mathcal F_n$ 与一个新的仿射纤维相交；仅由候选集合不能确定候选上的概率。

**证明。** 第一项由定义中的联立等式直接得到。第二项因为同一个非空集合可以承载不同的概率测度。证毕。

---

# 补编 SM：魔群的迹、观察者相关的记忆与《利维坦》的动力学命题

## SM.1 分次迹与二元 Möbius 恢复

**定义。** 对具有魔群作用的非负分次空间 $V^\natural=\bigoplus_{n\ge0}V_n^\natural$，定义

$$
T_g(q)=\sum_{n\ge0}\operatorname{Tr}(g|V_n^{\natural})q^{n-1}.
$$

当 $g=1$ 时系数为各级维数；一般 $g$ 的系数为字符值。

**定义。** 对整数系数族 $c$，令

$$
H_c(p,q)=\sum_{m,n>0}c(mn)p^mq^n.
$$

**定理。** 若归一化二元形式级数 $D$ 满足

$$
-\log D=\sum_{k\ge1}\frac1kH_c(p^k,q^k),
$$

则

$$
H_c(p,q)=\sum_{k\ge1}\frac{\mu(k)}k[-\log D(p^k,q^k)].
$$

**证明。** 把假设代入右侧并按同步幂代换的总指数收集项。$H_c(p^m,q^m)$ 的系数为

$$
\frac1m\sum_{d\mid m}\mu(d),
$$

它在 $m=1$ 时为一，在 $m>1$ 时为零。证毕。

## SM.2 群平均投影与零反馈

**假设。** 设 $G$ 为有限群，$\rho$ 为特征零表示，并且 $K\rho(g)=\rho(g)K$。

**定义。** 令

$$
P_G=\frac1{|G|}\sum_{g\in G}\rho(g),\qquad Q_G=I-P_G.
$$

**命题。** 有

$$
P_G^2=P_G,\qquad KP_G=P_GK,qquad
Q_GKP_G=P_GKQ_G=0.
$$

**证明。** 对每个 $h\in G$，方程 $g_1g_2=h$ 恰有 $|G|$ 对解，故 $P_G^2=P_G$。交换性逐项求和得到 $KP_G=P_GK$，最后两式由 $Q_G=I-P_G$ 展开。证毕。

**命题。** 若复表示分解为

$$
V=\bigoplus_\lambda W_\lambda\otimes M_\lambda,
$$

则与群作用交换的算子可在重数空间 $M_\lambda$ 内混合。因此两个算子都与群作用交换并不蕴含它们彼此交换。

**证明。** 群只作用于不可约因子 $W_\lambda$；任意 $I_{W_\lambda}\otimes A_\lambda$ 都与群作用交换，而重数空间上的两个 $A_\lambda$ 不必交换。证毕。

## SM.3 带群插入迹与观察记忆的分离

**定义。** 令 $W$ 为非零有限维实空间，

$$
P=\begin{pmatrix}1&0\\0&0\end{pmatrix}\otimes I_W,
\quad Q=I-P,
$$

并对 $a,b\in\mathbb R$ 置 $c=(a+b)/2,d=(a-b)/2$，

$$
K_0=\begin{pmatrix}a&0\\0&b\end{pmatrix}\otimes I_W,
\qquad
K_1=\begin{pmatrix}c&d\\d&c\end{pmatrix}\otimes I_W.
$$

**定理 SM1。** 对任意 $R\in\operatorname{End}(W)$，$K_0,K_1,P$ 均与 $I_2\otimes R$ 交换，且对全部 $k\ge0$，

$$
\operatorname{Tr}((I_2\otimes R)K_0^k)
=\operatorname{Tr}((I_2\otimes R)K_1^k)
=(a^k+b^k)\operatorname{Tr}(R).
$$

但若 $M_j(K)=(PKQ)(QKQ)^j(QKP)$，则

$$
\boxed{M_j(K_0)=0,\qquad M_j(K_1)=d^2c^jP\quad(j\ge0).}
$$

当 $a\ne b$ 时，二者的零滞后核不同。

**证明。** Kronecker 乘法给出交换性。归纳得 $K_0^k=\operatorname{diag}(a^k,b^k)\otimes I$；$K_1^k$ 的对角项为 $(a^k+b^k)/2$，非对角项为 $(a^k-b^k)/2$。取迹并使用张量积的迹相乘公式得到迹等式。$K_0$ 的 $PK_0Q$ 为零；$K_1$ 的分块为 $A=cI,B=dI,C=dI,D=cI$，故 $BD^jC=d^2c^jI$。证毕。

**命题。** $K_0,K_1$ 虽正交共轭，但在固定 $P$ 时具有不同记忆核；若把 $P$ 与动力学同时作同一基变换，记忆核相应共轭。

**证明。** 第一项由 SM1。第二项把每个因子 $P,K,Q$ 同时共轭，乘积中的相邻逆变换消去。证毕。

**命题。** 若 $0<b<a<1$，则 $K_0$ 与 $K_1$ 都自伴且严格收缩。

**证明。** 两个矩阵均对称，且彼此正交共轭；其特征值均为 $a,b$，故算子范数为 $a<1$。证毕。

## SM.4 完整可见响应的因果恢复

**定义。** 沿用 MF.2 的分块更新，从初态 $(v,0)$ 出发定义

$$
R_n(v)=\operatorname{pr}_V T^n(v,0).
$$

则 $R_0=I,R_1=A$，且

$$
R_{n+2}=AR_{n+1}+M_n+
\sum_{i=0}^{n-1}M_{n-1-i}\circ R_{i+1}.
$$

**定理 SM2。** 递归定义

$$
\boxed{\widehat M_n=R_{n+2}-R_1\circ R_{n+1}
-\sum_{i=0}^{n-1}\widehat M_{n-1-i}\circ R_{i+1},}
$$

则对任意环上的模、任意分块映射和全部 $n\ge0$，有 $\widehat M_n=BD^nC$。

**证明。** 当 $n=0$ 时和为空，消元公式给出 $R_2-R_1^2=BC$。假设所有较小指标已恢复，代入递推；MF1 的消元恒等式使右侧只剩 $M_n$。所有组合次序保持不变。证毕。

**命题。** 第 $n$ 个记忆核只由 $R_1,\ldots,R_{n+2}$ 决定；两个系统若具有相同的全部完整可见响应，则具有相同的全部记忆核。

**证明。** 第一项由 SM2 的三角递推对 $n$ 归纳，第二项逐个应用第一项。证毕。

**命题。** 在可见端同态环的形式幂级数中，若

$$
R(z)=\sum_{n\ge0}R_nz^n,qquad M(z)=\sum_{j\ge0}M_jz^j,
$$

则

$$
R(z)=(I-zA-z^2M(z))^{-1}.
$$

**证明。** 将 SM2 之前的响应递推乘以 $z^{n+2}$ 并对 $n\ge0$ 求和；卷积项成为 $z^2M(z)R(z)$，整理并用 $R_0=I$。证毕。

## SM.6 衰减状态的观察重新显现

**定义。** 取

$$
x_0=(1,-1),\qquad x_{n+1}=(ax_n^{(1)},bx_n^{(2)}),\quad0<b<a<1,
$$

并令 $y_n=x_n^{(1)}+x_n^{(2)}$。

**定理 SM3。** 同时有

$$
x_n=(a^n,-b^n),\quad y_0=0,\quad y_n>0\ (n>0),\quad y_n\longrightarrow0,
$$

$$
\|x_{n+1}\|^2<\|x_n\|^2\quad(n\ge0),
$$

以及

$$
y_{n+1}-y_n=(1-b)b^n-(1-a)a^n.
$$

**证明。** 对递归归纳得状态公式。由 $0<b<a$ 得 $b^n<a^n$（$n>0$），故 $y_n>0$。平方范数每步减少

$$
(1-a^2)a^{2n}+(1-b^2)b^{2n}>0.
$$

一阶差由直接展开得到；两个公比均在 $(0,1)$ 中，故 $y_n\to0$。证毕。

**命题。** 对 $n\ge0$，

$$
y_{n+1}>y_n\iff (b/a)^n>(1-a)/(1-b).
$$

**证明。** 在 SM3 的差式中把正数 $(1-b)a^n$ 移到另一侧并相除。证毕。

---

# 补编 FM：有限矩阵元恢复、有限精度与 Bala 的整除猜想

## FM.2 群表示约化后的有限矩阵元

**假设。** 设有限群具有已知的有限维复酉表示，并固定酉等型分解

$$
\mathcal H=\bigoplus_\lambda(\mathbb C^{m_\lambda}\otimes W_\lambda),\qquad
\rho(g)=\bigoplus_\lambda(I_{m_\lambda}\otimes\rho_\lambda(g)).
$$

设收缩算子 $K$ 与正交投影 $P$ 均与所有 $\rho(g)$ 交换。在重数空间中取酉坐标，使

$$
K=\bigoplus_\lambda(K_\lambda\otimes I),\qquad
P=\bigoplus_\lambda(P_\lambda\otimes I),\qquad
P_\lambda=\operatorname{diag}(I_{r_\lambda},0).
$$

**定义。** 在每个 $W_\lambda$ 中固定单位向量 $e_\lambda$，并测量

$$
s_{\lambda ab}(t)=\langle e_a\otimes e_\lambda,
K^t(e_b\otimes e_\lambda)\rangle,
\quad1\le a,b\le r_\lambda,\quad1\le t\le H+2.
$$

**定理 FM1。** 上述矩阵元确定全部观察记忆 $M_j$（$0\le j\le H$）；每个时刻只需 $\sum_\lambda r_\lambda^2$ 个复矩阵元。

**证明。** 这些矩阵元恰为约化可见响应 $R_\lambda(t)=P_\lambda K_\lambda^tP_\lambda$ 在其像上的全部条目。不同不可约块之间无交叉项，同一不可约因子中的其他方向因张量恒等因子给出相同响应。将各小矩阵代入 SM2 的有序因果恢复，得到 $M_{\lambda j}$，再还原

$$
\bigoplus_\lambda M_{\lambda j}\otimes I_{W_\lambda}.
$$

证毕。

## FM.3 非交换因果恢复的有限时间误差

**定义。** 令真实响应与记忆满足

$$
M_n=R_{n+2}-R_1R_{n+1}-\sum_{i=0}^{n-1}M_{n-1-i}R_{i+1},
$$

并用 $\widehat R$ 执行同一有序递推得到 $\widehat M$。

**定理 FM2。** 假设在 $1\le t\le H+2$ 上

$$
\|R_t\|,\|\widehat R_t\|\le1,qquad
\|\widehat R_t-R_t\|\le\eta,
$$

且在 $0\le j\le H$ 上 $\|M_j\|\le1$。则

$$
\boxed{\|\widehat M_j-M_j\|\le(2^{j+2}-1)\eta
\qquad(0\le j\le H).}
$$

**证明。** 保留乘法次序，用

$$
\|ab-cd\|\le\|a-c\|\,\|b\|+\|c\|\,\|b-d\|
$$

逐项比较两个递推。记 $E_j=\|\widehat M_j-M_j\|$，得到

$$
E_n\le3\eta+\sum_{j=0}^{n-1}(E_j+\eta).
$$

强归纳代入 $E_j\le(2^{j+2}-1)\eta$，右侧为 $3\eta+4\eta(2^n-1)=(2^{n+2}-1)\eta$。证毕。

**命题。** 若 FM1 的每个被测复矩阵元误差至多 $\epsilon$，令 $r_*=\max_\lambda r_\lambda$，则径向归一化后

$$
\boxed{\max_{0\le j\le H}\|\widehat M_j-M_j\|
\le2r_*(2^{H+2}-1)\epsilon.}
$$

**证明。** 一个 $r_\lambda\times r_\lambda$ 误差矩阵的算子范数不超过 Frobenius 范数，因而不超过 $r_\lambda\epsilon$。对 $\|R\|\le1$，径向归一化满足

$$
\left\|\frac Z{\max(1,\|Z\|)}-R\right\|\le2\|Z-R\|.
$$

当 $\|Z\|>1$ 时，$\|Z-Z/\|Z\|\|=\|Z\|-1\le\|Z-R\|$；另一情形为恒等映射。以 $\eta=2r_*\epsilon$ 应用 FM2。证毕。

## FM.4 三个固定标量恢复两副本系统的全部滞后

**定义。** 取非零有限维实表示 $\rho:G\to GL(W)$，并在 $W\oplus W$ 上令

$$
P=\begin{pmatrix}1&0\\0&0\end{pmatrix}\otimes I_W,
\qquad
K=\begin{pmatrix}u&v\\v&w\end{pmatrix}\otimes I_W.
$$

对第一副本的固定单位向量 $e$，置

$$
s_t=\langle e,K^te\rangle,qquad t=1,2,3.
$$

**定理 FM3。** 三个读数为

$$
s_1=u,\quad s_2=u^2+v^2,\quad
s_3=u^3+2uv^2+v^2w.
$$

令

$$
g=s_2-s_1^2,qquad z=s_3-2s_1s_2+s_1^3.
$$

则 $g=v^2,z=gw$，且

$$
\boxed{M_j=v^2w^jP
=\begin{cases}0,&g=0,\\g(z/g)^jP,&g>0.
\end{cases}}
$$

**证明。** 计算二次、三次幂得到三个读数。隐藏块满足 $DC=wC$，故 $D^jC=w^jC$，再乘回 $B$ 得 $BD^jC=v^2w^jI$。若 $g>0$，则 $w=z/g$；若 $g=0$，核恒为零。证毕。

**命题。** 若只给前缀时刻 $1,2,3$ 且无额外谱信息，则第三个读数不能由前两个读数决定相同的 $M_1$。

**证明。** 取 $u=0,v=1/4$，分别令 $w=0$ 与 $w=1/2$。两矩阵均实对称且收缩，前两个读数均为 $(0,1/16)$，但 $M_1$ 分别为 $0$ 与 $P/32$。证毕。

## FM.5 三矩有限精度恢复

**假设。** 设 $|u|,|w|\le1$、$|u^2+v^2|\le1$，三个真实读数各有不超过 $\epsilon\ge0$ 的误差。把前两个测量值截断到 $[-1,1]$，记所得值及第三个测量值为 $\widehat s_1,\widehat s_2,\widehat s_3$，并置

$$
\widehat g=\widehat s_2-\widehat s_1^2,\qquad
\widehat z=\widehat s_3-2\widehat s_1\widehat s_2+\widehat s_1^3,
$$

$$
\widehat m_j=
\begin{cases}
0,&\widehat g\le0,\\
\widehat g[\operatorname{clip}_{[-1,1]}(\widehat z/\widehat g)]^j,&\widehat g>0.
\end{cases}
$$

**定理 FM4。** 对全部 $j\ge0$，

$$
\boxed{|\widehat m_j-v^2w^j|\le(3+11j)\epsilon.}
$$

**证明。** 在单位区间上 $|x^k-y^k|\le k|x-y|$，从而

$$
|\widehat g-g|\le3\epsilon,
\qquad |\widehat z-gw|\le8\epsilon.
$$

若 $\widehat g\le0$，则 $0\le g\le3\epsilon$，结论成立。若 $\widehat g>0$，令 $\widehat w=\operatorname{clip}_{[-1,1]}(\widehat z/\widehat g)$。截断不增加到 $w$ 的距离，故

$$
\widehat g|\widehat w-w|
\le|\widehat z-\widehat g w|
\le8\epsilon+3\epsilon|w|\le11\epsilon.
$$

于是

$$
|\widehat g\widehat w^j-gw^j|
\le\widehat g|\widehat w^j-w^j|+|\widehat g-g||w|^j
\le11j\epsilon+3\epsilon.
$$

证毕。

**命题。** 因 $P$ 是非零正交投影，FM4 的标量界等价地给出

$$
\|\widehat m_jP-M_j\|\le(3+11j)\epsilon.
$$

**证明。** 由 FM3，$M_j=v^2w^jP$；又 $\|P\|=1$，故标量乘积的算子范数等于标量绝对值。证毕。

**命题。** 若另有 $0<\theta<1$ 与 $|w|\le\theta$，并把截断区间改成 $[-\theta,\theta]$，则

$$
|\widehat m_j-gw^j|
\le3\epsilon\theta^j+11\epsilon j\theta^{j-1},
$$

其中 $j=0$ 时第二项取零，并且

$$
\sum_{j\ge0}|\widehat m_j-gw^j|
\le\epsilon\left(\frac3{1-\theta}+\frac{11}{(1-\theta)^2}\right).
$$

**证明。** 重复 FM4 的加权差证明，并在幂差中保留 $\theta^{j-1}$；再分别求两个几何级数及其导数级数。证毕。

## FM.6 Bala 阶乘比

**定义。** 令

$$
A(n)=\frac{(30n)!\,n!}{(15n)!\,(10n)!\,(6n)!}.
$$

**命题。** Peter Bala 在 OEIS A211417 中提出 $A(n)/(3n+1)$ 的整性问题。

## FM.7 Bala 的 $3n+1$ 整性定理

**定理 FM5。** 对每个自然数 $n$，

$$
\boxed{(3n+1)(15n)!(10n)!(6n)!\mid(30n)!n!.}
$$

**证明。** $n=0$ 时为 $1\mid1$。以下设 $n>0$。对正整数 $q$ 定义

$$
f(n,q)=\left\lfloor\frac{30n}q\right\rfloor+\left\lfloor\frac nq\right\rfloor
-\left\lfloor\frac{15n}q\right\rfloor-\left\lfloor\frac{10n}q\right\rfloor
-\left\lfloor\frac{6n}q\right\rfloor.
$$

先证 $f(n,q)\ge0$。令 $r=n\bmod q$、$k=\lfloor30r/q\rfloor\in\{0,\ldots,29\}$。由 $30+1=15+10+6$，整部抵消，并有

$$
f(n,q)=k-\lfloor k/2\rfloor-\lfloor k/3\rfloor-\lfloor k/5\rfloor\ge0.
$$

最后一个不等式逐一检查 $0\le k<30$ 的余数类即可。

若 $q\mid3n+1$，则 $3r+1=tq$，其中 $t=1$ 或 $2$。当 $q\ge10$ 时，四个商

$$
(\lfloor30r/q\rfloor,\lfloor15r/q\rfloor,
\lfloor10r/q\rfloor,\lfloor6r/q\rfloor)
$$

分别为

$$
t=1:(9,4,3,1),\qquad t=2:(19,9,6,3),
$$

故 $f(n,q)=1$。当 $q=7$ 时 $r=2$，四个商为 $(8,4,2,1)$，仍有 $f(n,q)=1$。

由 Legendre 公式，对每个素数 $p$，

$$
v_p(A(n))=\sum_{j\ge1}f(n,p^j),
$$

且该和有限。若 $p\ge7$，则对每个 $1\le j\le v_p(3n+1)$，$p^j$ 为 $7$ 或至少为 $10$，所以上段各给一个单位贡献，其余项非负。因此

$$
v_p(A(n))\ge v_p(3n+1).
$$

素数 $3$ 不整除 $3n+1$。对素数 $2$，由 $v_p((pm)!)=v_p(m!)+m$ 反复化简得

$$
v_2(A(n))=v_2\binom{8n}{3n}.
$$

若 $2\mid3n+1$，则 $n$ 与 $5n$ 均为奇数。恒等式

$$
(3n+1)\binom{8n}{3n+1}=5n\binom{8n}{3n}
$$

两边取 $v_2$，得到 $v_2(A(n))\ge v_2(3n+1)$；若 $2\nmid3n+1$，结论平凡。

对素数 $5$，同理有

$$
v_5(A(n))=v_5\binom{5n}{3n}.
$$

若 $5\mid3n+1$，则 $5\nmid2n$，由

$$
(3n+1)\binom{5n}{3n+1}=2n\binom{5n}{3n}
$$

得到 $v_5(A(n))\ge v_5(3n+1)$；若 $5\nmid3n+1$，结论平凡。所有素数的赋值不等式均成立，唯一分解定理遂给出所述整除。证毕。

---

# 补编 PA：素数输入、DFAO 与操作相对的最小状态

本补编把 #6881 的素数状态机直接接到仓库现有 DFAO 真源。固定的研究对象是素数乘积、容量守卫及后续指令，不把矩阵记忆模型或其他载体替换成这个对象。三个新源码位于 `D5/S3/Factorization/Automata/`，配有同名 Scribe。以下普通证明、候选 Lean 源码与已通过内核的上游定理分开记载；新源码尚未在本环境编译。

## PA.1 状态、输出与输入分别是什么

DFAO 是 deterministic finite automaton with output，即带输出的确定性有限状态自动机。有限的是状态集合，不是可读取的输入长度。设状态集合为 S、输入字母表为 A、更新为 delta:S×A→S、输出为 o:S→O，则对任意有限输入词 w，都可以执行 delta_w。两个当前输出相同的状态可以具有不同的后续输出。

固定目标和输入域后，正确的状态等价是

$$
s\sim t\iff\forall w,\quad o(\delta_w(s))=o(\delta_w(t)).
$$

部分操作还必须保留哪些输入合法，或者把失败显式总化为一个吸收状态。仓库 `DFAOStateLowerBound` 复用 mathlib 的 DFA 和 Myhill–Nerode 左商，给出带输出的实际执行以及合法共同后缀的下界；`TypedPartialDFAOOverBase` 已有 Option-valued 部分执行与拼接律。本文复用这些对象，不重复建立通用自动机框架。

对于素数状态机，至少要区别两种字母表：

- 输入素数 p，执行整数乘法 x↦xp；输入的是操作。
- 输入二进制或 Zeckendorf 数位，更新一个数位识别器；输入的是某个整数的表示。

两者都可以使用 DFAO，但同一个字串、一步或状态数没有默认对应。自动机得到外部数位输入，也不等于无输入的有限自主系统能持续生成某个非周期序列。

## PA.2 实际整数上的精确最小性

固定 N>1，令 P_N 为 N 的素因子集合。字母表是 P_N，词值是其各字母的整数乘积，空词值为 1。目标是

$$
L_N=\{w:\operatorname{value}(w)\mid N\}.
$$

构造状态集合

$$
S_N=\{d\in\mathbb N:d\mid N\}\sqcup\{\bot\},
$$

其中 N>0，所以所有实际因数均为正数。初态是 1，全部因数状态输出 true，失败状态输出 false。更新为

$$
\delta(d,p)=
\begin{cases}dp,&dp\mid N,\\\bot,&dp\nmid N,\end{cases}
\qquad \delta(\bot,p)=\bot.
$$

**定理。** 这个自动机对每个素数输入词正确，而且任何对同一完整词域正确的 DFAO 至少有 tau(N)+1 个状态。

**证明。** 若某个前缀的乘积不整除 N，其任意后续乘积也不整除 N，因为前缀乘积整除完整乘积。若前缀合法，则更新保存当前的实际整数乘积。对词长归纳，得到全词正确性。

每个 d|N 都有一个来自其真实素因子分解的输入词。给定两个因数 d,e，取 d 的补因数 N/d，其全部素因子仍属于 P_N。由于 N/d>0，乘法消去给出

$$
e(N/d)\mid N\iff e(N/d)\mid d(N/d)\iff e\mid d.
$$

如果 d≠e，不能同时有 d|e 和 e|d。因此补因数 N/d 或 N/e 的真实素数词能区分这两个前缀。再取 N 的素数词后接任一 p∈P_N，得到真实失败前缀；空后缀就区分它和全部合法前缀。将这 tau(N)+1 个前缀及各对共同后缀交给已有 `state_lower_bound_of_distinguishing_family`，得到下界。构造本身达到该下界。证毕。

候选 Lean 声明：`GuardedPrimeProduct.arithmetic_dfao_minimality`。它把正确性、显式有限载体大小与所有正确有限机的下界共同写出，没有把预期下界放在假设中。N=1 的空素数字母表没有可达失败状态，因此通过显式素数输入前提排除；不能错误地给它套用两状态的最小性。

N=5040=2^4·3^2·5·7 时，tau(N)=5·3·2·2=60。故本任务有 60 个合法状态、61 个总状态；六个二进制位的 64 个码字能容纳总化机器，留下 3 个未用码字。原来只存合法寄存器状态时留下的是 4 个，两个口径不能混用。

如果规定只要求在已经保证合法的输入上输出 true，完全不要求识别溢出，那么一个永远输出 true 的状态就够。60 或 61 的下界依赖实际守卫语义；不能以承诺输入偷偷消除守卫后仍沿用下界，也不能把它解释为最优通用计算机。

## PA.3 有限观察深度的完整状态谱

写 N=product_i p_i^{a_i}，其中 p_i 是互异素数，当前合法状态为 d=product_i p_i^{e_i}。剩余容量是 r_i=a_i-e_i。一个后续词 w 含第 i 个素数 count_i(w) 次，因此唯一分解给出

$$
d\operatorname{value}(w)\mid N
\iff \forall i,\ \operatorname{count}_i(w)\le r_i.
$$

这正是 `PrimeCapacityHorizon.fits` 使用的实际 List 计数语义；不是独立边的存在性拼接。整数素因数到容量坐标的上述运输在这里给出普通证明，未另行声称一个已编译的坐标运输声明。

**定理。** 对任意有限容量向量 a、任意 H≥0，两合法状态在全部总长度不超过 H 的后续词上具有相同合法性，当且仅当

$$
\boxed{\forall i,\quad\min(r_i,H)=\min(s_i,H).}
$$

**证明。** 充分性：每个字母的计数至多为词长，因此至多 H；把剩余容量在 H 处截断，不改变该词是否合法。必要性：对每个 i，连续输入 min(r_i,H) 次第 i 个字母。这是一个合法且长度不超过 H 的词，故在 s 处也合法，推出 min(r_i,H)≤s_i；交换两状态得到反向不等式，结合两者至多 H，便得截断坐标相同。证毕。

截断后的每个坐标可以任取 0,…,min(a_i,H)，并可用同样的剩余容量 r_i 实现。失败状态由空后缀与全部合法状态区分。因此全部观察类数精确为

$$
\boxed{B_H=1+\prod_i\bigl(\min(a_i,H)+1\bigr).}
$$

`finite_horizon_state_classification` 同时证明核等价、到完整 profile 载体的满射与该载体基数，避免只构造一个未证明最小或未证明全部可实现的编码。退化空字母表时该载体仍显式包含一个失败状态，但本定理不声称该失败状态从初态可达；应用于 N>1 的实际素因子表时可达性由 PA.2 给出。

对于 a=(4,2,1,1)，得到：

| 可询问后续的最大长度 H | 合法状态观察类 | 含失败的全部观察类 |
|---:|---:|---:|
| 0 | 1 | 2 |
| 1 | 16 | 17 |
| 2 | 36 | 37 |
| 3 | 48 | 49 |
| 4 及以上 | 60 | 61 |

H=0 只看当前是否合法；H=1 还知道哪些素数已经没有剩余容量；逐步增加 H 才暴露更深余量。这里 60 与 64 的联系是实际算术残差数到二进制编码容量的关系，不是 Fibonacci 递推，也不是生物密码子论断。

更精细地，对 r≠s，两状态的最短区分词长为

$$
1+\min_{i:r_i\ne s_i}\min(r_i,s_i).
$$

取达到最小值的坐标并重复该字母可达此长度；更短的词在每个不同坐标都尚未耗尽较小余量，因此无法区分。这是上述核分类的普通推论，不另造一个绑定包装声明。

## PA.4 固定视野摘要与可更新状态必须分开

C_H(r)=(min(r_i,H)) 只保证当前能回答长度≤H 的问题，不自动保证对同样的 H 持续自治。若某轴容量至少 H+1 且 H>0，则余量 H 与 H+1 具有相同 C_H；各消耗一个单位后，余量成为 H-1 与 H，已被 C_H 区分。故一次更新可能让旧摘要中隐藏的区别变得可见。

但一个预算逐步减少的正面版本成立。对合法的单次消耗，已知 C_H(r) 足以更新 C_{H-1}(r-e_i)：被消耗的坐标使用

$$
\min(r_i-1,H-1)=\min(r_i,H)-1\quad(r_i>0,H>0),
$$

其他坐标再截断至 H-1。这给出精确有限时间预测，与“用同一固定粗状态永远更新”不同。此段是普通算术推论，源码中的主定理没有把它冒充已经具备的自治状态转换。

在恒定容量盒中，达到 H=max_i a_i 后，全部合法余量已被区分，完整状态因而可以自治更新。原来的有限盒本来只有有限状态；加入合法除法不会让这个固定盒凭空变成无限。

## PA.5 同一素数阈值在加入逆操作后需要更多状态

现在明确改变的是允许无界增长的寄存器域：完整整数从 1 开始，输入 + 表示乘以固定素数 p，输入 - 表示在 p|x 时精确除以 p。目标只询问

$$
p^a\mid x,\qquad a>0.
$$

在只允许乘法的同一无界域中，指数 e 的摘要 min(e,a) 足够：它按截断递增更新，输出是否已经达到 a。这个 a+1 状态构造不会保存超过 a 的具体指数，因为以后只乘不除时，超过量再也不影响该目标。

**定理。** 加入有守卫的精确除法后，不存在对全部合法输入词正确的有限 DFAO，即使完全不要求判断非法词。

**证明。** 任取 H。选择 H+1 个前缀：分别执行 a+i 次乘法，0≤i≤H，真实到达 p^{a+i}，当前输出全部相同。若 i<j，给两者接上同一个 i+1 次除法后缀。因为 a≥1，这个后缀对二者都合法。首个达到 p^{a-1}，目标为假；第二个仍有指数 a+j-i-1≥a，目标为真。故任何正确 DFAO 必须对这 H+1 个前缀到达互不相同的状态。取 H 为其假定有限状态数，矛盾。证毕。

`ReversiblePrimeThreshold.no_finite_dfao_for_exact_prime_division` 从实际整数乘除开始，先证明 p^e 坐标的逐步与整词模拟，再构造合法共同后缀族，最后复用现有 DFAO 下界。没有把非法后缀作为区分手段，也没有用输出全部指数来人为制造无限值域。

因此，必须保留多少状态是相对于对象域、操作集合和目标共同决定的。被乘法摘要丢掉的指数超额，在除法下重新变得重要。这是一种确切的操作相对记忆，不需要诉诸未实现现实或任意附加坐标。

## PA.6 整数显示、黄金数位与隐藏信息的范围

在固定互异素数的容量盒里，完整整数乘积 d 本身通过唯一分解就能恢复所有指数 e_i。此处不存在“同一个 d 对应不同指数向量”的隐含自由度。隐藏性来自改成较粗的观察，例如只显示是否合法、只显示某个余数，或只保留有限后续的答案。

之前 RawDigits→GoldenInt→整数读数的多对一映射是另一个已经明确的载体：不同原始数位构造可能具有相同整数求值。不能把那里存在的纤维直接移入这里已唯一分解的 60 状态盒。若要把两者组合，必须显式指定每个素数轴上保留原始数位、黄金坐标还是规范指数，并给出操作如何作用于该载体。

Zeckendorf 可以给这些指数或状态编号提供规范表示，但单纯无损换码不改变继续词等价类数。若读取的是数位字，合法数位语法的状态也必须计入；若读取的是素数指令，语法和运算契约则不同。位翻转成本、读取长度、解码开销与语义状态最小性是不同目标。

## PA.7 与现役 DFAO 开放问题的接口

Barnoff、Bright、Shallit 的论文表明：黄金比例第 n 个 base-b 数位是 b^n 的 Zeckendorf 表示的有限状态函数。仓库的 `golden-ratio-base4-dfao-minimality` 将 base-4 稀疏输入问题单独登记，现有 `DFAOStateLowerBound`、`TypedPartialDFAOOverBase` 及相关 oracle/identification 模块提供基础。

PA.2 对全部素数词的下界，不是对 {Zeckendorf(4^i)} 这个稀疏域的下界；一个补因数词能保持整除问题的输入合法，不意味着它能把两个稀疏前缀都补成 4 的幂。不能扩大正确性域后冒称解决了原来的 22 状态问题。现有唯一合法后缀的 distinguishing-family 容量限制也必须保留。

若一个有限前缀约束的 SAT 编码确实覆盖所有至多 21 状态机器，那么经 soundness 核验的 UNSAT 可以排除全局 21 状态模型，因为全局模型必定满足这个前缀。它仍不能单独证明某个 22 状态表对全部稀疏输入正确，也不能证明唯一性。有限拟合成功则更不能证明全局正确。本批不声称解决该外部猜想。

另一个不同的“prime automata”用语来自 Krohn–Rhodes 分解：其中的素构件指群/复位等转换半群结构，不是给寄存器贴上算术素数标签。这里的只乘法守卫系统中，任意非空词足够多次重复都会进入失败，因而其转换半群没有因此获得 Monster 作用。需要群论桥时，必须证明实际动作保持状态域、守卫和读数；数目相同或术语相同都不是这项证明。

## PA.8 研究价值、验证边界与来源

本批的实质结果是实际素数词的最小状态定理、任意容量和未来深度的完整核分类，以及精确除法破坏有限摘要的全称障碍。一般 Myhill–Nerode 理论、有限状态基本概念与一计数器障碍不作新发现或开放问题解决的宣称。没有 HTML、搜索平台、CI、harness 或冻结修改。

候选源码与普通证明经过逻辑审查；本环境没有 Lean/Lake，未运行 elaboration、kernel、axiom-print 或 Scribe 编译。实际整数检查验证了 5040 全部 60×60 个补因数测试、61 状态机的分区细化；另对多组实际素数和阈值检查 16,275 对合法除法后缀；对 420 组容量与视野实例，独立枚举真实后续词并核对完整 profile。有限检查仅作错误诊断，不替代全称证明。

原理论正文全部保留，本补编不取代其他分支对投影记忆、矩阵恢复或原始进位的结果。下一项承重问题是把实际 RawDigits 进位的目标相关历史和局部守卫，与这里的继续词等价逐项对齐；先确定能否得到有限的精确预测状态，而不是假定 60 个地址能容纳任意隐藏结构。若改用概率路径，应重新履行随机下降和整路径概率保持条件，不能由确定性 DFAO 自动获得。

**来源与复用：**

1. mathlib, `Mathlib.Computability.DFA` and `Mathlib.Computability.MyhillNerode`, pinned revision `db584cd6d46c92f209a44c0f1c829460d327499d`; public documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/MyhillNerode.html . Actual repository adapters were read at dev `5cc2bac9e9591eeaf703d875b077891d335a0025` and compared with the subsequent base `f59ab9427f4336f6718603695e4df5d47560d739`.
2. A. Barnoff, C. Bright, J. Shallit, *Using finite automata to compute the base-b representation of the golden ratio and other quadratic irrationals*, arXiv:2405.02727v1, 4 May 2024, https://arxiv.org/abs/2405.02727 . Its digit-extraction and sparse minimality scope is not silently transferred to prime-command words.
3. A. Ronca, N. Knorozova, G. De Giacomo, *Automata Cascades: Expressivity and Sample Complexity*, arXiv:2211.14028, https://arxiv.org/abs/2211.14028 . Used only to distinguish algebraic prime decomposition from arithmetic prime labels; no cascade sample-complexity result is claimed for the present state machine.
4. Repository sources reused directly: `D5/S0/Automata/DFAOStateLowerBound.lean` and `D5/S0/Automata/TypedPartialDFAOOverBase.lean`; arithmetic inputs use pinned mathlib `Nat.primeFactorsList`, `Nat.divisors`, positive-factor cancellation and prime-power divisibility. No unmerged research module is imported.

---

# 补编 PB：固定素数容量盒的双向观察与合法历史

## PB.1 对象、动作与读数不变，更换的只是允许的续词

继续 PA 的实际素数寄存器，而不引入与整数无关的隐藏坐标。对素数 $p$ 和容量 $a\in\mathbb N$，完整活状态是 $p^e$，$0\le e\le a$。上行动作乘以 $p$，下行动作要求 $p\mid p^e$ 后执行精确除法；每一步的结果必须仍整除 $p^a$。非法步骤进入吸收拒绝状态。目标读数只回答整个指定词是否执行成功，不输出完整指数。

`BoundedPrimeWalk.run_transport` 用实际整数乘除证明指数坐标和全部命令词的运行相对应。它复用 `ReversiblePrimeThreshold.numberStep` 与 `TypedPartialDFAOOverBase.runTransition`，新增上容量守卫，而不是将一个抽象计数器未经证明地改称素数机器。每一步的单态传输先由素数幂整除与实际除法建立，再对词归纳。拒绝结果也被传输。

对于有限互异素数集合及容量向量 $(a_i)$，整数 $\prod_i p_i^{e_i}$ 与指数元组双射。这是完整整数读数，已经确定每个指数。多态同读数来自这里明确选择的合法性布尔读数，或来自另一个明确的更丰富载体；不能归因于唯一分解本身不唯一。

多轴源码定义实际 interleaved `boxStep`：每个命令只更新指定坐标，失败终止。`chronological_legality` 对完整词证明：同一初始元组的联合运行成功，当且仅当每个轴按原先的相对顺序执行其全部局部命令都成功。这解决共同历史见证，禁止用各边不同的见证拼接轨迹。单轴数值传输在 Lean 中完成；多轴指数元组与一个整数乘积的通常唯一分解对应在这里说明，不声称另有一条新编译的乘积共轭声明。

## PB.2 完整历史的守卫，不是终点的净变化

把上行记作 $+1$，下行记作 $-1$。对词 $w$ 的全部前缀（包括空前缀），记净位移为 $s_j$，并令

$$
m(w)=\min_j s_j,\qquad M(w)=\max_j s_j,\qquad \Delta(w)=s_{|w|}.
$$

在指数 $e$ 上，整段历史合法当且仅当

$$
0\le e+s_j\le a\quad\text{对全部 }j,
$$

也就是

$$
-m(w)\le e\le a-M(w).
$$

合法时终点为 $e+\Delta(w)$。这是逐个前缀守卫的直接等价，不是只比较最终整数。比如先除再乘和先乘再除的净位移都为零，但前者要求 $e\ge1$，后者要求 $e\le a-1$。二者与空操作具有不同的定义域。

新源码的运行语义逐步检查这些守卫；PB.7 进一步给出该区间三元组的普通数学分类，作为下一项独立形式化目标，不把它冒充当前已经新增的 Lean 定理。

## PB.3 双向有限视野的精确核

**定理。** 对任意 $a,H\in\mathbb N$ 以及 $e,f\in\{0,\ldots,a\}$，

$$
\begin{aligned}
&\text{每个长度至多 }H\text{ 的乘除词，在 }e,f\text{ 上的合法性相同}\\
&\quad\Longleftrightarrow\quad
\bigl(\min(e,H),\min(a-e,H)\bigr)
=
\bigl(\min(f,H),\min(a-f,H)\bigr).
\end{aligned}
$$

**必要性。** 连续 $k$ 次除法成功当且仅当 $k\le e$；连续 $k$ 次乘法成功当且仅当 $e+k\le a$。分别取 $k=\min(e,H)$、$\min(a-e,H)$ 并交换 $e,f$，得到两个截断距离相等。两种重复词的实际运行语义由 `accepts_down` 和 `accepts_up` 对词长归纳证明。

**充分性。** 对 $H$ 归纳。$H=0$ 只包含空词。对 $H+1$，截断下边界距离相同保证除法的第一步守卫一致，截断上边界距离相同保证乘法的第一步守卫一致。共同失败时结论立即成立；共同成功时，更新后状态在预算 $H$ 上仍有相同的两边界截断距离，于是用归纳假设处理剩余的混合词。该证明不是把混合词换成它的净计数。对应 `BoundedPrimeHorizon.finite_horizon_kernel`。

**精确像。** 若 $a\le2H$，所有活状态都不同。若 $a>2H$，$0,\ldots,H-1$ 各自一类，$H,\ldots,a-H$ 合为一个中心类，$a-H+1,\ldots,a$ 各自一类。源码构造了下列有限编号并证明满射与核相同：

$$
\operatorname{code}_{a,H}(e)=
\begin{cases}
e,&a\le2H,\\
e,&a>2H,\ e\le H,\\
\max(H,e-(a-2H)),&a>2H,\ e>H.
\end{cases}
$$

因此活类数是 $\min(a,2H)+1$，计入拒绝类后为 $\min(a,2H)+2$。拒绝类在空词处已经与全部活状态区分。对应 `profile_classification`，不仅给出基数上界，还实现每个声称的类。

## PB.4 最短分离长度与任意素数盒

**定理。** 若 $e<f$，最短的合法性分离实验长度是

$$
\boxed{d_a(e,f)=\min(e+1,a-f+1).}
$$

这里分离实验允许一边结果为拒绝。连续 $e+1$ 次除法，较小状态失败而较大状态成功；连续 $a-f+1$ 次乘法，较大状态失败而较小状态成功。任意比这两者都短的词，都看不到相应的边界差异：PB.3 的截断距离仍相同。故没有更短的混合词。Lean 的 `shortest_separation` 以“存在长度至多 H 的分离词 iff 上述最小值至多 H”给出全部预算的充要条件。

**最坏情况阈值。** 所有活状态能由长度至多 $H$ 的词族两两区分，当且仅当

$$
a\le2H.
$$

充分性由两边界距离相等推出 $e=f$。反向，当 $a>2H$，实际不同状态 $H$ 与 $H+1$ 都处在未分开的中心类中。对应 `full_separation_threshold`。最小统一预算是 $\lceil a/2\rceil$。

**任意有限素数盒。** 对混合词在第 $i$ 轴上的局部子词，长度不超过总长度；反之任意单轴词都能作为混合词使用，并且其他轴不动。由这两个具体词构造和 PB.1 的联合运行等价，得到整盒精确核：

$$
e\sim_Hf\iff
\forall i,\quad
\min(e_i,H)=\min(f_i,H),\quad
\min(a_i-e_i,H)=\min(a_i-f_i,H).
$$

全部实现类型数（包括拒绝）为

$$
\boxed{B_H^{\pm}=1+\prod_i\bigl(\min(a_i,2H)+1\bigr).}
$$

对应 `PrimeBoxBidirectionalHorizon.mixed_word_profile_classification`，包含满射、全部混合词的核和类型基数。空字母表时额外拒绝点仍是声明的状态，但不宣称它从初态可达。

对 $(4,2,1,1)$，数目在 $H=0,1,2$ 分别为 $2,37,61$，以后保持 $61$。上一轮只乘法的相应数目为 $2,17,37,49,61$。两种动作域下完整状态仍是 60 个活整数加拒绝；除法降低的是分离这些状态所需的最大后续长度，不是完整状态数或输入的所有成本。

对于一般盒，完全分离阈值是 $\max_i\lceil a_i/2\rceil$（空指标集为零）。两个不同元组的最短分离长度是各个不同坐标的

$$
\min\bigl(\min(e_i,f_i)+1,\ a_i-\max(e_i,f_i)+1\bigr)
$$

之最小值。此两项是已证精确核及单轴见证的普通推论，不另造仅作投影与代入的 Lean 包装。

## PB.5 有限视野商不是同预算的永久记忆

PB.3 的归纳同时展示预算下降规则：相同 $(H+1)$-视野的状态，在同一成功操作后，具有相同 $H$-视野。不能去掉这一次预算损耗。例如容量 $a=4$、预算 $H=1$，状态 $1,2$ 当前同类；共同除以 $p$ 后成为 $0,1$，再进行一次除法就能区分。

因此有限问题所需的摘要，与能够永久自治更新的摘要不同。加入除法没有突破这一边界。保留全部有限续词的极限时，盒中的全部活状态都会被分开；这与此前的最小完整 DFAO 结论相容。

## PB.6 区分见证与安全识别实验

所有上述视野结论都针对共同初态候选上的反事实词族：比较某个词在不同起态的结果。它不保证在一个未知的不可复制寄存器上，任意执行一条 H 步路径就能知道初态。

事实上，若初态可能是整个盒，任何非空的单轴乘除词都不可能对所有初态保持合法：第一步若乘法，则上端点失败；第一步若除法，则下端点失败。多轴同样如此，因为任意第一个命令选中的轴都可能处在不利端点。

所以同时要求“无额外读数、无重置、对全部初态安全、仍作非空有效询问”是不可能的。要设计安全识别，必须明列额外条件，例如已知严格内区间、可重置实验、多个一致副本，或一个不会改变状态的整除观察。增加这样的能力会改变数学规格，不能事后隐去其成本。

## PB.7 下一项实际数学对象：完整历史作为区间偏变换

以下是从逐步守卫直接得到的普通数学推论，尚未声称已写入本轮 Lean。

固定单轴容量 $a$，一段任意长命令历史所诱导的非空偏变换，准确形如

$$
x\in[l,u]\longmapsto x+\delta,
\qquad 0\le l\le u\le a,
\qquad -l\le\delta\le a-u.
$$

这不是把完整路径还原为终点：定义域 $[l,u]$ 记录整段历史对所有起态施加的守卫。PB.2 给出 $l=-m(w),u=a-M(w),\delta=\Delta(w)$。任意满足这些条件的三元组都可实现：先下行 $l$ 次，再上行 $l+a-u$ 次，最后下行 $a-u-\delta$ 次。其前缀最小值、最大值和最终位移恰为 $-l,a-u,\delta$，而所有次数非负。

所以，尽管命令历史无限多，其在这个固定盒上的偏变换只有

$$
1+\sum_{k=1}^{a+1}k^2
$$

种：空变换一类；每个长度为 $s$ 的非空定义区间及同长像区间，分别有 $a+2-s$ 种选择。不同定义域或不同位移给出不同偏变换。

有限非空的多轴盒中，非空变换是这些区间平移的乘积；任意坐标失败给出同一个空变换，各局部选择可按轴串接实现。因此数量为

$$
1+\prod_i\left(\sum_{k=1}^{a_i+1}k^2\right).
$$

对 $(4,2,1,1)$，这是 $1+55\cdot14\cdot5\cdot5=19251$。它数的是命令词诱导的不同偏变换，不是机器状态，也不是不同原始历史的数量。

这一商恰好保留插入任意前后命令时的可执行性和最终状态，因为偏函数相等在复合下保持。它不保留步数、全部中间读数或其他路径费用。因此“19251 种操作行为”不能冒称“完整历史只有19251种”。下一项形式化应证明实际词的区间正规形、复合律和实现性，然后才运输此基数。该对象与有限链上的保序偏变换理论有关，但其精确子幺半群是区间平移，不能直接套用更大的保序变换幺半群的计数。

## PB.8 来源、验证边界与公开问题

本批新增三个 Lean 模块与三个配套 Scribe：`BoundedPrimeWalk`、`BoundedPrimeHorizon`、`PrimeBoxBidirectionalHorizon`。证明承担的是实际整数操作传输、对完整词的归纳、精确核和像实现、最短见证及联合运行合法性。有限数值例子只解释一般定理，不建立另一组独立正向实例模块。

本批没有运行 Lean elaboration、kernel checking 或 Scribe 编译；没有伪造 axiom 输出、冻结记录、独立评审或 CI 结果。普通数学证明与源码经过审查，仍须实际 Lean 检查。PB.7 的正规形及偏变换计数仅为普通证明和下一项形式化对象。经典 Myhill–Nerode、有限链偏变换和区分序列的思想不声称为本项目首创。

参考的第一手来源：

1. 钉版 Mathlib 与仓库已有 `DFAOStateLowerBound`、`TypedPartialDFAOOverBase`；Mathlib Myhill–Nerode 文档：<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/MyhillNerode.html>。本批以既有词运行接口为底层，没有改写自动机真源。
2. Aaron Barnoff, Curtis Bright, Jeffrey Shallit. *Using finite automata to compute the base-b representation of the golden ratio and other quadratic irrationals*. arXiv:2405.02727v1, 2024. <https://arxiv.org/abs/2405.02727>。其 2026 年期刊扩展为 *Computing the base-b representation of quadratic irrationals using automata*, Theoretical Computer Science 1071, 115843, DOI <https://doi.org/10.1016/j.tcs.2026.115843>。期刊摘要仍区分已证最小性与只拟合高精度数位的候选。这些数值表示输入并非本批的乘除命令词；本批不宣称解决稀疏 base-4 的22状态问题，也不凭旧问题页断言其全部后续文献状态。
3. Hayrullah Ayık, Vítor H. Fernandes, Emrah Korkmaz. *On the monoid of partial order-preserving transformations of a finite chain whose domains and ranges are intervals*. arXiv:2503.19459, 2025. <https://arxiv.org/abs/2503.19459>。用于定位 PB.7 的现有研究背景；其对象更大，未把摘要中的结果当成本批的现成证明或计数公式。

公开问题仍保留原规格：稀疏输入域不扩大，表示词不换成命令词，候选拟合不升级为全称正确性。本轮的具体进展是同一素数状态机上的可检验一般数学结果，而非再造通用搜索框架。

---

# 补编 PC：素数历史的区间正规形、上下文完备性与最短代表

## PC.1 数学对象与已有结果的关系

继续固定 #6881 的实际单素数寄存器 $p^e$，其中 $p$ 为素数、$0\le e\le a$。命令 $+$ 是乘以 $p$，命令 $-$ 是满足整除守卫时精确除以 $p$；每一步还必须满足结果整除 $p^a$。`BoundedPrimeWalk.run_transport` 已将完整整数运行运输到指数上的部分运行，失败不可在后来恢复。本补编复用该 runner，不把净位移当作实际运行，也不改动先前的状态最小性和有限视野分类。

研究对象从单个状态转为一个实际命令词所诱导的部分变换。目标是判定何时两段历史可在任意前后文中互换，而仍保留整段合法性与终点。原始轨迹、中间读数、概率和成本是更细的对象，不被该等价关系自动保留。

文献归属需要明确：单生成元自由逆幺半群的三个不变量与其复合公式是经典内容。Silva [PC1] 的第 2.2 节、式 (1) 明确用 Munn 区间的左右端点及终点位移表示元素。本补编没有把这一抽象正规形声称为新发现；新增形式化工作是在本仓真实的有限容量素数 runner 上证明语义运输、全部形态的实际实现、观察上下文完备性和最短命令长度。没有假定已形式化自由逆幺半群的普适性质。

## PC.2 每个实际历史的完整守卫正规形

给词 $w=b_1\cdots b_n$，令 $s_0=0$，$s_j$ 为前 $j$ 个命令的整数位移，$+$ 贡献 $1$、$-$ 贡献 $-1$。定义

$$
m(w)=\min_{0\le j\le n}s_j,\qquad
M(w)=\max_{0\le j\le n}s_j,\qquad
\Delta(w)=s_n.
$$

空前缀确保 $m\le0\le M$，且 $m\le\Delta\le M$。源码用结构递归直接计算这三个量：

$$
\begin{aligned}
\Delta(bw)&=\epsilon_b+\Delta(w),\\
m(bw)&=\min(0,\epsilon_b+m(w)),\\
M(bw)&=\max(0,\epsilon_b+M(w)).
\end{aligned}
$$

**定理 PC.2（实际运行充要条件）。** 对任意容量 $a$、任意词 $w$ 和任意合法指数 $e,f$：

$$
\operatorname{run}_a(e,w)=f
\iff
0\le e+m(w),\quad e+M(w)\le a,\quad f=e+\Delta(w).
$$

**证明。** 对命令词归纳。空词恰给出 $f=e$。非空词先分析实际乘法或除法守卫；守卫失败时，前缀极值必已越界。守卫成功时，后继为 $e+\epsilon_b$，再将归纳假设与三个递归等式合并。这样每个中间守卫都由归纳保留，不用终点可行性替代路径可行性。对应 `PrimeHistoryNormalForm.run_spec`。

因此，若 $M-m>a$，该词从全部合法起态都失败，其正规形是唯一空映射。否则其非空正规形是

$$
[l,u;\Delta]=[-m,a-M;\Delta],\qquad e\in[l,u]\longmapsto e+\Delta.
$$

源码的 `IntervalMap a` 要求

$$
0\le l\le u\le a,\qquad 0\le l+\Delta,\qquad u+\Delta\le a.
$$

`normal_correct` 证明其求值等于原 runner 输出指数后的完整 Option 结果，包含失败。`evaluate_injective` 用定义域的两个端点及一个输出恢复全部三个参数，证明该表示没有重复非空形态；空映射与每个非空形态也可区分。

## PC.3 实际可实现性：没有虚构的正规形

**定理 PC.3。** 每个满足上述条件的 $[l,u;\Delta]$ 都来自一条实际有限命令词。

**构造与证明。** 取

$$
w=(-)^l(+)^{a-u+l}(-)^{a-u-\Delta}.
$$

三个长度均非负。其位移依次从 $0$ 到 $-l$，再到 $a-u$，最后到 $\Delta$。条件 $-l\le\Delta\le a-u$ 保证第三段不超出前两段建立的极值。因此完整签名恰为 $(-l,a-u,\Delta)$，实际合法起态区间恰是 $[l,u]$，而不是它的超集。空映射由 $a+1$ 次乘法实现。

`realize_signature` 对实际重复词和拼接计算三个坐标；`normal_surjective` 覆盖非空和空情形。因此可以从正规形构造可执行见证，而不必从无限历史中猜一个。

## PC.4 复合律与共同中间状态

约定先执行 $F=[l,u;d]$，再执行 $G=[l',u';d']$。中间指数 $e+d$ 必须同时属于第二段的定义域，所以复合为

$$
\boxed{
G\circ F=
[\max(l,l'-d),\ \min(u,u'-d);\ d+d']
}
$$

当左端点超过右端点时，复合为空映射；任一输入为空时亦然。

`evaluate_compose` 证明该闭式的求值恰等于先求值 $F$ 再用同一个中间结果求值 $G$ 的 `Option.bind`。`append_signature` 证明

$$
\begin{aligned}
\Delta(vw)&=\Delta(v)+\Delta(w),\\
m(vw)&=\min(m(v),\Delta(v)+m(w)),\\
M(vw)&=\max(M(v),\Delta(v)+M(w)).
\end{aligned}
$$

进而 `normal_append` 将实际词拼接运输为上述复合。一般结合律由真实部分函数复合与表示单射性导出；本轮不为这个既有函数结合律另建独立包装定理或新的幺半群基础设施。

这条交集公式正是“逐边存在不等于整段可行”的具体修复：第二段的条件先拉回第一段的坐标，再与第一段条件求交。空交集表示没有共同中间见证。

## PC.5 只看合法性，也能得到完整上下文判据

**定理 PC.5。** 两个词具有相同正规形，当且仅当任意合法起态 $e$、任意前缀 $u$ 和后缀 $v$ 都满足

$$
\operatorname{accepts}_a(e,u w_1 v)
=
\operatorname{accepts}_a(e,u w_2 v).
$$

**证明。** 正向由正规形复合与实际执行的运输得到，且保留更强的最终指数相等。反向先固定任意前文：一条历史失败而另一条成功，空后缀已能区分。如果两条都成功但得到不同指数，已有 `BoundedPrimeHorizon.full_separation_threshold` 给出一个实际乘除后缀，区分两个终点的合法性。因此所有上下文合法性一致迫使所有实际部分运行相同，再由正规形的外延唯一性得到两个正规形相同。对应 `normal_eq_iff_contextual_run` 与 `normal_eq_iff_contextual_accepts`。

这是一个全称语义结论，不承诺只用一个不可重置、未知的起态就能安全测量整个正规形。其意义是：该正规形保留了这个算术接口下任意后续推理真正需要的历史区别；原词长度或中间访问顺序若也属于目标，就必须使用更细接口。

## PC.6 逆映射不是群消去

对非空正规形有

$$
[l,u;d]^{-1}=[l+d,u+d;-d].
$$

`inverse_graph` 证明逆形态的图恰是原图的反向关系，空与单点区间也成立。结合实际可实现性，逆形态也有命令词见证。将原命令词倒序并交换乘除，同样实现这个逆；这最后一句有普通逐步反向证明，本轮没有另列该词级 Lean 定理。

但 $F^{-1}\circ F$ 只是 $[l,u;0]$，并非整个 $[0,a]$ 上的恒等映射。特别是“先除后乘”与空词不能无条件抵消：它只在 $e\ge1$ 的原定义域上等于恒等。所有平移都保序；有限区间上能在整个载体双射到自身的平移只有零平移。因此群单位只有恒等，而具有局部逆的丰富结构是逆幺半群，不是一个由普通素数标签自动产生的群。

在经典单生成元自由逆幺半群中，区间宽度在左右乘法下不会减小。于是宽度大于 $a$ 的元素组成一个双边理想；把它们全部压成零，正得到这里的有限容量行为对象。这个文献对应解释了为何需要保留访问极值；本轮源码没有宣称形式化了这项抽象 Rees 商同构。[PC1, PC2]

## PC.7 新的精确优化：最短代表的长度

正规形不保留原始成本，但可以定义其行为类中最小的命令长度。对非空 $F=[l,u;d]$，令

$$
W=a-u+l.
$$

**定理 PC.7。** 在全部诱导相同部分映射的命令词中，最短长度恰为

$$
\boxed{L_{\min}(F)=2W-|d|.}
$$

**下界证明。** 任何这样的词都具有同样的最小位移 $m=-l$、最大位移 $M=a-u$ 及终点 $d$。如果先访问 $m$ 后访问 $M$，长度至少为 $2(M-m)-d$；相反顺序则至少为 $2(M-m)+d$，所以统一下界为 $2(M-m)-|d|$。源码的 `word_length_lower_bound` 使用等价的逐词归纳：前缀增加一个单位步时，该所需成本最多增长一，因而给出全部词的符号下界。

**达到下界。** 当 $d\ge0$，使用 PC.3 的先低后高构造，长度恰为 $2W-d$。当 $d<0$，反射整个容量区间、构造对应正位移词，再逐命令交换乘除；得到先高后低的词，长度为 $2W+d$。源码 `shortest_realization` 同时证明实际正规形正确、长度公式以及对全部同正规形词的最小性。

空映射最短长度是 $a+1$：访问宽度不超过步数，处处失败必须有宽度至少 $a+1$，而 $a+1$ 次乘法达到。该空映射长度结论保留普通证明，不冒称为新增 Lean 声明。

此最优化不能解释为恢复原历史的成本。不同长词可同属一个行为类；这里返回的是该类的最省命令实现，也不替代带不同指令权重、概率或中间结构约束的优化问题。

## PC.8 原配置中的三种数量

一个容量为 $a$ 的寄存器有 $a+1$ 个活状态。若正常形定义域含 $k$ 个整数，它有 $a+2-k$ 个可能的起点和相同数量的像区间起点，因此非空正常形数为

$$
\sum_{k=1}^{a+1}(a+2-k)^2=\sum_{j=1}^{a+1}j^2.
$$

再加一个空映射。对非空有限素数轴集合，独立各轴的非空形态组合全部可由串接局部命令实现；任一轴为空则联合映射为空。因此总数为

$$
1+\prod_i\left(\sum_{j=1}^{a_i+1}j^2\right).
$$

对 $(4,2,1,1)$，这是 $1+55\cdot14\cdot5\cdot5=19251$ 个操作行为，而活状态仍是 $5\cdot3\cdot2\cdot2=60$，完整自动机状态仍是加失败后的 61。原始历史没有长度上界，数量仍然无限。基数公式及多轴正规形运输在本补编有普通证明；本轮新增 Lean 精确落实单轴的正常形、实现、复合、观察完备性和最短词，而不把多轴计数描述成已有新编译声明。

## PC.9 下一项可由本结果约束的数学问题

精确正规形已回答“历史是否可替换”；下一项可以问：给定起态、终态和轨迹长度，有多少条真实合法历史，以及这些历史怎样分布到同一个正规形中？同一部分映射并不决定固定长度的路径数，也不决定一次随机反应的概率。正规形可作为分层条件，但统计不能省略被它遗忘的时间信息。

进一步在带概率的实际素数命令过程中，只有证明当前摘要保留所有下一步条件概率，才可从确定性行为等价提升到随机路径律等价。若指令费用不均等，PC.7 的单位成本公式应替换为已知上下界加权的两种极值访问次序，并重新证明；不能直接用无权长度代替物理时间。

这些问题仍以本仓同一个有限容量素数对象为起点，不以换成任意群、线性系统或别的未验证对象代替原目标。

## PC.10 文献与形式化边界

[PC1] Pedro V. Silva. *On the rational subsets of the monogenic free inverse monoid*. arXiv:2205.08854v2 (2022), Section 2.2, equation (1). https://arxiv.org/abs/2205.08854 . 三个区间不变量、经典乘法以及 Munn 表示背景；本文使用其已公开普通数学结构，不导入第三方 Lean 库。

[PC2] L. Elliott, A. Levine, J. D. Mitchell. *Counting monogenic monoids and inverse monoids*. Communications in Algebra 51 (2023), 4654–4661. DOI 10.1080/00927872.2023.2214821. https://doi.org/10.1080/00927872.2023.2214821 . 有限单生成元逆幺半群的分类背景，不把该文较一般的对象或计数直接替代本题。

本轮新增的三个 Lean 模块为 `PrimeHistoryNormalForm`、`PrimeHistoryComposition`、`PrimeHistoryGeodesic`，每个均配套同名 Scribe。它们复用同一分支的 `BoundedPrimeWalk`、`BoundedPrimeHorizon` 和已在 dev 的部分 DFA runner。未建立平行自动机基础设施，未引入 `sorry` 或新公理。普通数学论证与源文经过审查，但当前环境没有 Lean/Lake；没有宣称已 elaborated、内核通过、公理输出已执行、Scribe 已编译或已冻结。有限精确检查仅为补充诊断。抽象逆幺半群正规形不是新的开放问题解决，其他外部猜想没有因此被宣称闭合。

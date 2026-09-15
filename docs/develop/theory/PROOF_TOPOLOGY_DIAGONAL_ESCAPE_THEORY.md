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

# 补编 PA：素数乘法寄存器的有限状态分类

## PA.1 带输出自动机与继续词等价

**定义。** 带输出的确定性有限状态自动机由有限状态集 $S$、输入字母表 $A$、转移 $\delta:S\times A\to S$ 与输出 $o:S\to O$ 组成。对词 $w\in A^*$，记迭代转移为 $\delta_w$；状态的继续词等价定义为

$$
s\sim t\iff\forall w\in A^*,\qquad o(\delta_w(s))=o(\delta_w(t)).
$$

**定义。** 对部分操作，把失败总化为吸收状态 $\bot$，并令 $o(\bot)=\mathsf{false}$。素数指令字母 $p$ 表示整数变换 $x\mapsto xp$；数位字母表示对某种整数表示的读取。两种字母表上的词、转移与继续词等价分别由各自的动作定义，不作默认同一。

## PA.2 算术自动机的正确性与精确最小性

**假设。** 固定整数 $N>1$，令 $P_N$ 为 $N$ 的素因子集合。对词 $w\in P_N^*$，令 $\operatorname{val}(w)$ 为各字母之积，并令空词之值为 $1$。考虑语言

$$
L_N=\{w\in P_N^*: \operatorname{val}(w)\mid N\}.
$$

**定义。** 令

$$
S_N=\{d\in\mathbb N:d\mid N\}\sqcup\{\bot\}.
$$

**定义。** 初态为 $1$，因数状态的输出为 $\mathsf{true}$，$\bot$ 的输出为 $\mathsf{false}$，且

$$
\delta(d,p)=
\begin{cases}
dp,&dp\mid N,\\
\bot,&dp\nmid N,
\end{cases}
\qquad
\delta(\bot,p)=\bot.
$$

**定理。** 上述自动机恰好识别 $L_N$。若 $\tau(N)$ 表示 $N$ 的正因数个数，则任何在完整词域 $P_N^*$ 上识别 $L_N$ 的带输出确定性有限状态自动机至少有 $\tau(N)+1$ 个状态；上述自动机恰有 $\tau(N)+1$ 个状态，因而达到精确最小值。

**证明。** 若当前前缀的乘积整除 $N$，转移后状态仍等于新的实际乘积；若它不整除 $N$，则因该前缀乘积整除任何延长词的乘积，此后均不整除 $N$。对词长归纳即得识别正确性。

**证明。** 每个 $d\mid N$ 都由一个素因子词到达。若 $d,e\mid N$ 且 $d\ne e$，则 $e\nmid d$ 或 $d\nmid e$。在前一种情形，取值为 $N/d$ 的素因子词：它从 $d$ 出发成功，而

$$
e(N/d)\mid N=d(N/d)\iff e\mid d
$$

**证明。** 这表明该词从 $e$ 出发失败；后一种情形交换 $d,e$。故全部 $\tau(N)$ 个因数前缀两两可分。又取值为 $N$ 的词并续接任意 $p\in P_N$，可到达失败前缀；空后缀把它与所有因数前缀区分。因此任一正确自动机至少需要 $\tau(N)+1$ 个状态，而所构造自动机恰有这些状态。证毕。

**命题。** 若输入域先验只含合法词，且输出只要求恒为真，则一个状态足够。

**证明。** 取唯一状态并令每个字母都自环、输出恒为 $\mathsf{true}$。这说明 $\tau(N)+1$ 的下界以识别溢出为必要条件。证毕。

## PA.3 乘法后缀的有限视野核

**假设。** 设

$$
N=\prod_{i\in I}p_i^{a_i},\qquad
d=\prod_{i\in I}p_i^{e_i},\qquad
0\le e_i\le a_i,
$$

**假设。** 其中 $I$ 有限且 $p_i$ 两两不同。令剩余容量 $r_i=a_i-e_i$；对素数词 $w$，令 $c_i(w)$ 为字母 $p_i$ 的出现次数。

**命题。** 后缀 $w$ 从状态 $d$ 出发合法，当且仅当

$$
d\operatorname{val}(w)\mid N
\iff
\forall i\in I,\qquad c_i(w)\le r_i.
$$

**证明。** 唯一分解给出 $d\operatorname{val}(w)$ 在 $p_i$ 上的指数为 $e_i+c_i(w)$；它整除 $N$ 当且仅当对每个 $i$ 都有 $e_i+c_i(w)\le a_i$。证毕。

**定理。** 对 $H\in\mathbb N$，两个合法状态的剩余容量分别为 $r,s$。它们对全部长度不超过 $H$ 的乘法后缀具有相同合法性，当且仅当

$$
\boxed{\forall i\in I,\qquad \min(r_i,H)=\min(s_i,H).}
$$

**证明。** 若截断坐标相同，则 $c_i(w)\le |w|\le H$，所以 $c_i(w)\le r_i$ 与 $c_i(w)\le s_i$ 等价。反之，对每个 $i$ 输入 $\min(r_i,H)$ 个 $p_i$；该词从 $r$ 出发合法，故 $\min(r_i,H)\le s_i$。交换 $r,s$ 后得到反向不等式，截断坐标遂相等。证毕。

**定理。** 计入吸收失败状态后，长度不超过 $H$ 的乘法后缀所区分的状态类数精确为

$$
\boxed{B_H=1+\prod_{i\in I}\bigl(\min(a_i,H)+1\bigr).}
$$

**证明。** 每个截断坐标 $\min(r_i,H)$ 可独立取遍 $0,1,\ldots,\min(a_i,H)$，并由取相应剩余容量的合法状态实现。前一定理说明两个合法状态同类恰在这些坐标全部相同。吸收失败状态由空后缀与全部合法状态区分，故再加一类。证毕。

**命题。** 若 $r\ne s$，则最短乘法分离词的长度为

$$
1+\min_{i:r_i\ne s_i}\min(r_i,s_i).
$$

**证明。** 取使右侧达到最小值的坐标，重复相应素数 $1+\min(r_i,s_i)$ 次，恰有一个状态溢出。任何更短的词在每个不同坐标上的出现次数都不超过两状态较小的余量，在相同坐标上的合法性又一致，故不能分离。证毕。

## PA.4 视野摘要的预算递减

**定义。** 对剩余容量向量 $r$ 与 $H\in\mathbb N$，定义

$$
C_H(r)=\bigl(\min(r_i,H)\bigr)_{i\in I}.
$$

**命题。** 若 $H>0$ 且一次合法操作消耗第 $i$ 个坐标，则 $C_H(r)$ 唯一确定 $C_{H-1}(r-\mathbf e_i)$。

**证明。** 被消耗坐标满足 $r_i>0$，并有

$$
\min(r_i-1,H-1)=\min(r_i,H)-1.
$$

**证明。** 对 $j\ne i$，有 $\min(r_j,H-1)=\min(\min(r_j,H),H-1)$。故所有新坐标都由 $C_H(r)$ 决定。证毕。

**命题。** 固定的 $C_H$ 一般不能在每次操作后仍作为同一 $H$ 的自治摘要。

**证明。** 若某坐标容量至少为 $H+1$ 且 $H>0$，则余量 $H$ 与 $H+1$ 具有相同的 $C_H$ 坐标；各消耗一次后变为 $H-1$ 与 $H$，其 $C_H$ 坐标不同。证毕。

**命题。** 在固定容量盒中，若 $H\ge\max_i a_i$，则 $C_H(r)=r$，因而摘要等于完整合法状态并可自治更新。

**证明。** 每个 $r_i\le a_i\le H$，所以 $\min(r_i,H)=r_i$。证毕。

## PA.5 无界寄存器上的精确除法障碍

**假设。** 固定素数 $p$ 与整数 $a>0$。寄存器状态为 $p^e$，其中 $e\in\mathbb N$；指令 $+$ 把 $p^e$ 变为 $p^{e+1}$，指令 $-$ 仅在 $e>0$ 时把 $p^e$ 变为 $p^{e-1}$。输出命题为

$$
p^a\mid p^e\iff e\ge a.
$$

**命题。** 若只允许指令 $+$，则 $\min(e,a)$ 给出一个具有 $a+1$ 个状态的正确摘要。

**证明。** 转移为 $k\mapsto\min(k+1,a)$，输出为 $k=a$。由归纳可知，它在任意乘法词后等于真实指数在 $a$ 处的截断。证毕。

**定理。** 加入有守卫的精确除法指令 $-$ 后，不存在对全部合法输入词正确的有限带输出确定性自动机，即使不要求它判断非法词。

**证明。** 任取 $H\in\mathbb N$，考虑 $H+1$ 个前缀 $(+)^{a+i}$，其中 $0\le i\le H$。它们分别到达 $p^{a+i}$，当前输出均为真。若 $i<j$，共同后缀 $(-)^{i+1}$ 对二者都合法；它把前者送到 $p^{a-1}$，输出为假，而把后者送到 $p^{a+j-i-1}$，输出为真。故这 $H+1$ 个前缀必须到达两两不同的自动机状态。若自动机有 $q$ 个状态，取 $H=q$ 即得矛盾。证毕。

## PA.6 唯一分解与无损换码

**定理。** 若 $p_i$ 两两不同且 $0\le e_i,f_i\le a_i$，则

$$
\prod_i p_i^{e_i}=\prod_i p_i^{f_i}\iff \forall i,\ e_i=f_i.
$$

**证明。** 对每个 $p_i$ 取素数赋值，等式两边分别给出 $e_i$ 与 $f_i$；反向由逐坐标相等立即得到。证毕。

**命题。** 对状态集合的任意双射换码，继续词等价类的数目不变。

**证明。** 以双射及其逆共轭每个转移，并把输出沿双射搬运。每个原状态与其编码对所有词产生相同输出，故双射在继续词等价类之间诱导双射。证毕。

## PA.7 输入域限制与下界的方向

**定义。** 对允许的继续词集合 $D\subseteq A^*$，定义

$$
s\sim_D t\iff \forall w\in D,\qquad o(\delta_w(s))=o(\delta_w(t)).
$$

**命题。** 若 $D\subseteq E\subseteq A^*$，则 $s\sim_E t$ 蕴含 $s\sim_D t$；因而限制继续词域只能合并等价类，不能由较大词域的分离族自动推出较小词域上的同一下界。

**证明。** 对 $E$ 中全部词成立的输出等式当然对其子集 $D$ 中全部词成立。故每个 $E$-等价类包含于某个 $D$-等价类。证毕。

**命题。** 把 PA.2 中的 $N$ 写成 $N=\prod_i p_i^{a_i}$。对该守卫乘法系统，任意非空词 $w$ 的充分高次重复 $w^k$ 都从每个合法状态进入失败状态。

**证明。** 词 $w$ 至少含一个素数 $p_i$。若其出现次数为 $c_i>0$，则 $w^k$ 在该坐标消耗 $kc_i$；取 $k>a_i/c_i$，便超过该坐标的总容量。证毕。

# 补编 PB：有限素数容量盒的双向词与精确视野

## PB.1 容量盒与按时间顺序的合法性

**假设。** 设 $I$ 为有限指标集，$p_i$ 为两两不同的素数，$a_i\in\mathbb N$。活状态为

$$
e=(e_i)_{i\in I}\in\prod_{i\in I}\{0,1,\ldots,a_i\},
$$

**假设。** 状态 $e$ 对应整数 $\prod_i p_i^{e_i}$。

**定义。** 字母 $(i,+)$ 在 $e_i<a_i$ 时令 $e_i\mapsto e_i+1$，字母 $(i,-)$ 在 $e_i>0$ 时令 $e_i\mapsto e_i-1$，其余坐标不变；守卫不满足时进入吸收失败状态。词的读数是整词是否成功。

**定义。** 对混合词 $w$，令 $\pi_i(w)$ 为删去所有不作用于第 $i$ 轴的字母后所得局部词，并保持余下字母的原相对顺序。

**定理。** 混合词 $w$ 从 $e$ 出发成功，当且仅当对每个 $i\in I$，局部词 $\pi_i(w)$ 从 $e_i$ 出发成功。成功时，联合运行的第 $i$ 个终点等于局部运行 $\pi_i(w)$ 的终点。

**证明。** 对 $w$ 的长度归纳。空词结论显然。设首字母作用于第 $i$ 轴；它的守卫只依赖 $e_i$，且只改变该坐标。若守卫失败，联合词与第 $i$ 个局部词都失败；若守卫成功，对新元组与余词应用归纳假设即可。未被首字母作用的各轴保持其局部词及状态不变，故相对顺序与共同历史同时保留。证毕。

## PB.2 前缀极值给出的完整守卫

**定义。** 在单轴容量 $a$ 上，把 $+$ 记作位移 $1$，把 $-$ 记作位移 $-1$。对词 $w=b_1\cdots b_n$，令 $s_0=0$，令 $s_j$ 为前 $j$ 个字母的净位移，并定义

$$
m(w)=\min_{0\le j\le n}s_j,\qquad
M(w)=\max_{0\le j\le n}s_j,\qquad
d(w)=s_n.
$$

**定理。** 词 $w$ 从 $e\in\{0,\ldots,a\}$ 出发成功，当且仅当

$$
-m(w)\le e\le a-M(w),
$$

**定理。** 成功时终点为 $e+d(w)$。

**证明。** 执行第 $j$ 个前缀后的指数为 $e+s_j$。全部逐步守卫成立等价于对所有 $j$ 都有 $0\le e+s_j\le a$，又等价于 $e+m(w)\ge0$ 且 $e+M(w)\le a$。终点取 $j=n$ 即为 $e+d(w)$。证毕。

**命题。** 词 $-+$、$+-$ 与空词的净位移都为零，但三者诱导的定义域分别为 $[1,a]$、$[0,a-1]$ 与 $[0,a]$。

**证明。** 三个词的前缀极值分别为 $(-1,0)$、$(0,1)$ 与 $(0,0)$，代入前一定理即得。证毕。

## PB.3 双向有限视野的两边界核

**定义。** 对 $e\in\{0,\ldots,a\}$ 与 $H\in\mathbb N$，定义两边界剖面

$$
Q_H(e)=\bigl(\min(e,H),\min(a-e,H)\bigr).
$$

**定理。** 对 $e,f\in\{0,\ldots,a\}$，每个长度至多 $H$ 的乘除混合词在 $e,f$ 上具有相同成功或失败结果，当且仅当

$$
\boxed{Q_H(e)=Q_H(f).}
$$

**证明。** 连续 $k$ 次除法成功当且仅当 $k\le e$，连续 $k$ 次乘法成功当且仅当 $k\le a-e$。分别使用这两类词并交换 $e,f$，可从有限视野等价推出两个截断边界距离相等。

**证明。** 反向对 $H$ 归纳。$H=0$ 时只有空词。对预算 $H+1$，剖面相同保证两个状态对首个 $+$ 或 $-$ 的守卫结果一致。若共同失败，结论成立；若共同成功，执行首字母后的两个状态具有相同的 $H$-剖面，归纳假设遂处理余下长度至多 $H$ 的任意混合词。证毕。

**定理。** 活状态的两边界剖面恰有

$$
\min(a,2H)+1
$$

**定理。** 因而活状态共有 $\min(a,2H)+1$ 个视野类；计入吸收失败状态后，视野类数为 $\min(a,2H)+2$。

**证明。** 若 $a\le2H$，剖面相同迫使 $e=f$，故有 $a+1$ 类。若 $a>2H$，状态 $0,\ldots,H-1$ 各给一个不同的下边界类，状态 $H,\ldots,a-H$ 共同给出剖面 $(H,H)$，状态 $a-H+1,\ldots,a$ 各给一个不同的上边界类，共 $2H+1$ 类。吸收失败状态在空词处与所有活状态不同。证毕。

## PB.4 最短分离、完全分离与混合词类数

**定理。** 若 $0\le e<f\le a$，则分离 $e,f$ 的最短乘除词长度为

$$
\boxed{d_a(e,f)=\min(e+1,a-f+1).}
$$

**证明。** 词 $(-)^{e+1}$ 使 $e$ 失败而使 $f$ 成功，词 $(+)^{a-f+1}$ 使 $f$ 失败而使 $e$ 成功，故右侧是上界。若 $H$ 小于右侧，则 $H\le e<f$ 且 $H\le a-f<a-e$，于是 $Q_H(e)=Q_H(f)=(H,H)$；由 PB.3，长度至多 $H$ 的词不能分离二者。证毕。

**定理。** 单轴容量盒的全部活状态可由长度至多 $H$ 的词两两分离，当且仅当

$$
\boxed{a\le2H}.
$$

**证明。** 若 $a\le2H$，PB.3 中相同剖面迫使状态相等。若 $a>2H$，不同状态 $H$ 与 $H+1$ 具有相同剖面 $(H,H)$，故不能由该视野分离。等价地，最小统一预算为 $\lceil a/2\rceil$。证毕。

**定理。** 对有限素数容量盒，两状态 $e,f$ 对全部长度至多 $H$ 的混合词具有相同合法性，当且仅当对每个 $i$ 都有

$$
\min(e_i,H)=\min(f_i,H),\qquad
\min(a_i-e_i,H)=\min(a_i-f_i,H).
$$

**证明。** 任意混合词在第 $i$ 轴上的投影长度不超过总长度，故逐轴剖面相同结合 PB.1 推出联合合法性相同。反之，任意单轴分离词都可视为只使用第 $i$ 轴字母的混合词，故联合有限视野等价蕴含每一轴的剖面相同。证毕。

**定理。** 计入共同的吸收失败状态后，混合词有限视野类数精确为

$$
\boxed{B_H^{\pm}=1+\prod_{i\in I}\bigl(\min(a_i,2H)+1\bigr).}
$$

**证明。** PB.3 给出第 $i$ 轴恰有 $\min(a_i,2H)+1$ 个可实现剖面。各坐标状态可独立选择，故全部剖面元组均可实现；前一定理说明其核恰是有限视野等价。再加由空词区分的吸收失败类。证毕。

**命题。** 对不同状态向量 $e,f$，最短混合分离词长度为

$$
\min_{i:e_i\ne f_i}
\left(
\min\bigl(\min(e_i,f_i)+1,\ a_i-\max(e_i,f_i)+1\bigr)
\right),
$$

**命题。** 完全分离整个盒的最小统一预算为 $\max_i\lceil a_i/2\rceil$。

**证明。** 对每个不同坐标应用单轴最短分离定理，并把所得单轴词嵌入混合字母表，得到上界。若词短于所示各坐标下界，则每一轴的局部投影都不能分离相应坐标，PB.1 遂给出联合下界。对所有坐标取单轴完全分离预算的最大值，即得统一预算。证毕。

## PB.5 双向视野的预算递减

**命题。** 若 $Q_{H+1}(e)=Q_{H+1}(f)$，且同一个首字母在 $e,f$ 上都成功并分别到达 $e',f'$，则 $Q_H(e')=Q_H(f')$。

**证明。** 对字母 $+$，下边界距离各增一、上边界距离各减一；对字母 $-$ 则相反。把相同的 $H+1$ 截断边界距离作这一单位更新，再在 $H$ 处截断，所得两对坐标仍相同。证毕。

**命题。** 一般不能把前一命题中的预算损耗删去。

**证明。** 若 $H>0$ 且 $a\ge H+1$，状态 $H$ 与 $H+1$ 具有相同 $H$-剖面；共同执行 $-$ 后成为 $H-1$ 与 $H$，其 $H$-剖面不同。证毕。

**命题。** 若两个活状态对所有有限词均有相同合法性，则它们相等。

**证明。** 取 $H\ge\lceil a/2\rceil$，由 PB.4 的完全分离定理即得。证毕。

## PB.6 全域安全非空询问的不可能性

**定理。** 在任意非空有限容量盒中，不存在从每个活初态出发都成功的非空乘除词。

**证明。** 设非空词的首字母作用于第 $i$ 轴。若该字母为 $+$，取满足 $e_i=a_i$ 的初态，首步失败；若该字母为 $-$，取满足 $e_i=0$ 的初态，首步失败。因此任意非空词都在某个活初态失败。证毕。

## PB.7 历史诱导的区间平移

**定义。** 单轴容量 $a$ 上的非空区间平移写作

$$
[l,u;d]:x\in[l,u]\longmapsto x+d,
$$

**定义。** 参数满足

$$
0\le l\le u\le a,\qquad -l\le d\le a-u.
$$

**定理。** 每个不是处处失败的命令词都诱导唯一的区间平移

$$
[-m(w),a-M(w);d(w)],
$$

**定理。** 每个满足上述条件的区间平移都由某个命令词诱导。

**证明。** 第一部分由 PB.2 的运行充要条件直接给出。反之，对给定 $[l,u;d]$ 取

$$
w=(-)^l(+)^{a-u+l}(-)^{a-u-d}.
$$

**证明。** 三段长度均非负；该词的前缀最小值为 $-l$，最大值为 $a-u$，终点位移为 $d$。PB.2 遂给出所需定义域与平移。证毕。

**定理。** 单轴容量 $a$ 上由命令词诱导的不同部分变换共有

$$
1+\sum_{k=1}^{a+1}k^2
$$

**定理。** 因而单轴共有 $1+\sum_{k=1}^{a+1}k^2$ 种；若 $I$ 非空，则多轴容量盒上共有

$$
1+\prod_{i\in I}\left(\sum_{k=1}^{a_i+1}k^2\right)
$$

**定理。** 上式即为多轴部分变换的精确数目。

**证明。** 先计入唯一的处处失败变换。单轴非空定义域若含 $s$ 个整数，则定义域和同长像区间各有 $a+2-s$ 个起点，故该 $s$ 贡献 $(a+2-s)^2$ 种；令 $k=a+2-s$ 即得平方和。多轴非空变换由各轴非空区间平移的独立选择唯一确定，并可把各轴的实现词依次串接而实现；任一轴处处失败时，联合变换都是同一个处处失败变换。证毕。


# 补编 PC：素数历史的区间正规形与最短代表

## PC.1 历史词与部分变换

**假设。** 固定素数 $p$ 与容量 $a\in\mathbb N$。活状态 $e\in\{0,\ldots,a\}$ 表示整数 $p^e$；字母 $+$ 表示乘以 $p$，字母 $-$ 表示在 $e>0$ 时精确除以 $p$，且每一步都须留在 $[0,a]$。

**定义。** 对词 $w$，令 $T_w$ 为它在 $[0,a]\cap\mathbb Z$ 上诱导的部分变换：若从 $e$ 执行整词成功，则 $T_w(e)$ 为终点；否则 $T_w(e)$ 无定义。两个词行为等价，当且仅当它们诱导同一个部分变换。

## PC.2 前缀极值与运行正规形

**定义。** 给定词 $w=b_1\cdots b_n$，令 $s_0=0$，令 $s_j$ 为前 $j$ 个字母的净位移，并定义

$$
m(w)=\min_{0\le j\le n}s_j,\qquad
M(w)=\max_{0\le j\le n}s_j,\qquad
d(w)=s_n.
$$

**命题。** 对首字母 $b$ 的位移 $\varepsilon_b\in\{-1,1\}$，有

$$
\begin{aligned}
d(bw)&=\varepsilon_b+d(w),\\
m(bw)&=\min(0,\varepsilon_b+m(w)),\\
M(bw)&=\max(0,\varepsilon_b+M(w)).
\end{aligned}
$$

**证明。** 非空前缀的位移都等于 $\varepsilon_b$ 加上 $w$ 的一个前缀位移，再与空前缀的位移 $0$ 一同取极值。终点公式是同一分解在完整前缀上的特例。证毕。

**定理。** 对 $e,f\in\{0,\ldots,a\}$，

$$
T_w(e)=f
\iff
0\le e+m(w),\qquad e+M(w)\le a,qquad f=e+d(w).
$$

**证明。** 执行每个前缀后的指数恰为 $e+s_j$。整词成功等价于所有这些数都在 $[0,a]$，也就是最小者 $e+m(w)$ 非负且最大者 $e+M(w)$ 不超过 $a$；成功时完整前缀给出终点 $e+d(w)$。证毕。

**定义。** 若 $M(w)-m(w)>a$，定义 $w$ 的正规形为处处无定义的空映射。否则定义

$$
\mathcal N_a(w)=[-m(w),a-M(w);d(w)],
$$

**定义。** 其中 $[l,u;d]$ 表示 $e\in[l,u]\mapsto e+d$。

**定理。** $T_w$ 等于 $\mathcal N_a(w)$ 所表示的部分变换。每个非空正规形都满足

$$
0\le l\le u\le a,qquad -l\le d\le a-u,
$$

**定理。** 两个非空正规形表示同一部分变换，当且仅当它们的 $l,u,d$ 分别相等。

**证明。** 运行定理把定义域化为 $[-m(w),a-M(w)]$，并把值化为加上 $d(w)$。空前缀保证 $m(w)\le0\le M(w)$ 且 $m(w)\le d(w)\le M(w)$，由此得到参数不等式。若两个非空区间平移相等，则定义域相等给出端点 $l,u$ 相等，再在任一域内点比较像得到位移 $d$ 相等；反向显然。证毕。

## PC.3 每个容许正规形的实现

**定理。** 每个满足

$$
0\le l\le u\le a,qquad -l\le d\le a-u
$$

**定理。** 满足这些条件的 $[l,u;d]$ 都由有限词实现；空映射也由有限词实现。

**证明。** 对非空形取

$$
w=(-)^l(+)^{a-u+l}(-)^{a-u-d}.
$$

**证明。** 各指数非负，位移依次从 $0$ 到 $-l$，再到 $a-u$，最后到 $d$。因 $-l\le d\le a-u$，最后一段不产生新的极值，故 $(m(w),M(w),d(w))=(-l,a-u,d)$；PC.2 给出正规形 $[l,u;d]$。词 $(+)^{a+1}$ 的前缀宽度为 $a+1$，故从每个活初态都失败，实现空映射。证毕。

## PC.4 正规形的复合律

**定理。** 设先执行 $F=[l,u;d]$，再执行 $G=[l',u';d']$。若两者非空，则

$$
\boxed{
G\circ F=
[\max(l,l'-d),\ \min(u,u'-d);\ d+d']
}
$$

**定理。** 当左端点大于右端点时右侧解释为空映射；任一因子为空映射时复合亦为空映射。

**证明。** 起点 $e$ 必须同时满足 $e\in[l,u]$ 与中间状态 $e+d\in[l',u']$。这等价于

$$
e\in[l,u]\cap[l'-d,u'-d]
=[\max(l,l'-d),\min(u,u'-d)].
$$

**证明。** 交集非空时最终状态为 $(e+d)+d'=e+d+d'$；交集为空时没有共同中间状态。证毕。

**命题。** 对先执行 $v$ 再执行 $w$ 的拼接词 $vw$，有

$$
\begin{aligned}
d(vw)&=d(v)+d(w),\\
m(vw)&=\min(m(v),d(v)+m(w)),\\
M(vw)&=\max(M(v),d(v)+M(w)).
\end{aligned}
$$

**证明。** 拼接词的前缀或为 $v$ 的前缀，或为完整 $v$ 后接 $w$ 的一个前缀；后者的位移为 $d(v)$ 加相应的 $w$ 前缀位移。分别取终点、最小值与最大值即得。证毕。

## PC.5 成败观察的上下文完备性

**定义。** 令 $A_a(e,w)$ 表示词 $w$ 从 $e\in[0,a]$ 出发成功。

**定理。** 对任意词 $w_1,w_2$，下列条件等价：

$$
\mathcal N_a(w_1)=\mathcal N_a(w_2),
$$

$$
\forall e\in[0,a],\ \forall x,y\in\{+,-\}^*,\qquad
A_a(e,xw_1y)=A_a(e,xw_2y).
$$

**证明。** 若正规形相同，则 $T_{w_1}=T_{w_2}$。PC.4 的复合律表明在任意前缀 $x$ 与后缀 $y$ 两侧复合后仍得到相同部分变换，故成败相同。

**证明。** 反之，若两个部分变换的定义域不同，取对称差中的起点并令 $x,y$ 为空词，成败已不同。若定义域相同而位移不同，取域中任一起点；两词都成功但终点不同。PB.4 保证存在一个乘除后缀分离这两个终点，令它为 $y$ 且令 $x$ 为空词，即与上下文成败相同矛盾。因此两个部分变换相等，再由 PC.2 的唯一性得到正规形相同。证毕。

## PC.6 逆形与反向图

**定理。** 对非空正规形 $F=[l,u;d]$，定义

$$
F^{-1}=[l+d,u+d;-d].
$$

**定理。** 此时

$$
y=F(x)\iff x=F^{-1}(y).
$$

**定义。** 空映射的逆仍为空映射。

**证明。** $x\in[l,u]$ 当且仅当 $y=x+d\in[l+d,u+d]$，且此时 $x=y-d$。参数条件保证平移后的区间仍在 $[0,a]$。空映射没有图点，其反向关系仍为空。证毕。

**命题。** 若 $F=[l,u;d]$ 非空，则

$$
F^{-1}\circ F=[l,u;0],\qquad
F\circ F^{-1}=[l+d,u+d;0].
$$

**证明。** 代入 PC.4 的复合公式即可。特别地，除非 $[l,u]=[0,a]$，第一式不是全载体上的恒等映射。证毕。

**命题。** 把实现 $F$ 的词倒序并交换 $+$ 与 $-$，所得词实现 $F^{-1}$。

**证明。** 原词的每一步 $x\mapsto x\pm1$ 都由交换后的反向一步 $x\pm1\mapsto x$ 撤回，故 $F$ 的每条合法轨迹都给出反向词的一条合法逆轨迹。反之，反向词的任一合法轨迹再次倒序并交换字母，便成为原词的合法轨迹；所以反向词在 $F$ 的像之外不能成功。其图因而恰是 $F$ 的反向图。证毕。

## PC.7 词长下界与最短代表

**定理。** 对任意词 $w$，若

$$
\operatorname{low}=m(w),\qquad
\operatorname{high}=M(w),\qquad
d=d(w),
$$

**定理。** 此时

$$
\boxed{2(\operatorname{high}-\operatorname{low})-|d|\le |w|.}
$$

**证明。** 若轨迹先首次到达 $\operatorname{low}$ 再首次到达 $\operatorname{high}$，从 $0$ 到低点、再到高点、再到终点 $d$ 的总距离给出

$$
|w|\ge -\operatorname{low}+(\operatorname{high}-\operatorname{low})+(\operatorname{high}-d)
=2(\operatorname{high}-\operatorname{low})-d.
$$

**证明。** 若先到高点再到低点，同理

$$
|w|\ge \operatorname{high}+(\operatorname{high}-\operatorname{low})+(d-\operatorname{low})
=2(\operatorname{high}-\operatorname{low})+d.
$$

**证明。** 两种次序必居其一，而两下界都不小于 $2(\operatorname{high}-\operatorname{low})-|d|$。证毕。

**定理。** 对非空正规形 $F=[l,u;d]$，诱导 $F$ 的词的最短长度精确为

$$
\boxed{L_{\min}(F)=2(a-u+l)-|d|.}
$$

**证明。** 任一实现词都满足 $m=-l$、$M=a-u$，故前一定理给出下界。若 $d\ge0$，词

$$
(-)^l(+)^{a-u+l}(-)^{a-u-d}
$$

**证明。** 实现 $F$，长度为 $2(a-u+l)-d$。若 $d<0$，词

$$
(+)^{a-u}(-)^{a-u+l}(+)^{l+d}
$$

**证明。** 的前缀最小值、最大值和终点分别为 $-l,a-u,d$，且长度为 $2(a-u+l)+d$。两种情形均达到 $2(a-u+l)-|d|$。证毕。

**命题。** 空映射的最短实现长度为 $a+1$。

**证明。** 若词处处失败，则由 PC.2 有 $M(w)-m(w)>a$。单位步轨迹满足 $M(w)-m(w)\le|w|$，故 $|w|\ge a+1$。词 $(+)^{a+1}$ 达到此界。证毕。

## PC.8 正规形的精确数量

**定理。** 单轴容量 $a$ 上的非空正规形数为

$$
\sum_{k=1}^{a+1}(a+2-k)^2
=
\sum_{j=1}^{a+1}j^2,
$$

**定理。** 计入空映射后为 $1+\sum_{j=1}^{a+1}j^2$。

**证明。** 若定义域含 $k$ 个整数，则它在 $[0,a]$ 中有 $a+2-k$ 个可能位置。像区间长度同为 $k$，也有 $a+2-k$ 个可能位置；定义域与像区间的起点唯一决定平移量，故贡献 $(a+2-k)^2$ 个正规形。对 $k$ 求和并换元 $j=a+2-k$，再加唯一空映射。证毕。

**定理。** 对非空有限指标集 $I$，多轴容量盒上由混合词诱导的部分变换数为

$$
\boxed{1+\prod_{i\in I}\left(\sum_{j=1}^{a_i+1}j^2\right).}
$$

**证明。** 联合变换非空时，PB.1 把它唯一分解为各轴的非空正规形；反之，各轴正规形可分别实现，再把各轴词串接即可实现其直积。若任一轴的局部变换为空，则联合变换处处失败，所有这类选择合并为唯一空映射。证毕。

**命题。** 对每个 $a$，命令词集合是无限的，而其诱导的部分变换集合是有限的。

**证明。** 前一定理给出有限性。词族 $(+)^{a+1}(+-)^n$ 随 $n\in\mathbb N$ 两两不同，却都在开头的 $(+)^{a+1}$ 后处处失败，故词集合无限。证毕。

---

# 补编 PM：五倍指标整除、正矩响应与一致性约束下的记忆恢复

## PM.1 Bala 的五倍指标整除

**定义。** 沿用 FM.6 的阶乘比

$$
A(n)=\frac{(30n)!n!}{(15n)!(10n)!(6n)!},\qquad n\in\mathbb N,
$$

并对正整数 $q$ 置

$$
f(n,q)=\left\lfloor\frac{30n}{q}\right\rfloor+\left\lfloor\frac n q\right\rfloor-
\left\lfloor\frac{15n}{q}\right\rfloor-\left\lfloor\frac{10n}{q}\right\rfloor-
\left\lfloor\frac{6n}{q}\right\rfloor.
$$

**定理 PM1。** 若 $q\ge6$ 且 $q\mid5n+1$，则 $f(n,q)=1$。此外，对 $n>0$，若 $10n<q\le30n$，则同样有 $f(n,q)=1$。

**证明。** 先令 $r=n\bmod q$。整数部分由 $30+1=15+10+6$ 抵消，故 $f(n,q)=f(r,q)$。若 $q\mid5n+1$，则 $5r+1=tq$，其中 $t\in\{1,2,3,4\}$。当 $q\ge6$ 时，四个商 $\lfloor30r/q\rfloor,\lfloor15r/q\rfloor,\lfloor10r/q\rfloor,\lfloor6r/q\rfloor$ 依次为

$$
\begin{array}{c|rrrr}
t&\lfloor30r/q\rfloor&\lfloor15r/q\rfloor&\lfloor10r/q\rfloor&\lfloor6r/q\rfloor\\
1&5&2&1&1\\
2&11&5&3&2\\
3&17&8&5&3\\
4&23&11&7&4
\end{array}
$$

且 $\lfloor r/q\rfloor=0$，逐行相减得到一。对于第二项，$\lfloor n/q\rfloor,\lfloor6n/q\rfloor,\lfloor10n/q\rfloor$ 都为零。令 $k=\lfloor30n/q\rfloor\in\{1,2\}$，则 $\lfloor15n/q\rfloor=\lfloor k/2\rfloor$，所以 $f(n,q)=k-\lfloor k/2\rfloor=1$。证毕。

**定理 PM2。** 对全部自然数 $n$，

$$
\boxed{(5n+1)(15n)!(10n)!(6n)!\mid(30n)!n!.}
$$

这是 Peter Bala 在 OEIS A211417 的 2025 年 8 月 28 日评注中提出的 $A(n)/(5n+1)$ 整性条款；不等同于该条目的 $3n+1$ 或 $30n-1$ 条款。来源：[OEIS A211417](https://oeis.org/A211417)。

**证明。** $n=0$ 显然。设 $n>0$。由 FM5 已知分母 $(15n)!(10n)!(6n)!$ 整除分子，故 $A(n)$ 是正整数。FM.7 的余数计算给出 $f(n,q)\ge0$，而 Legendre 公式给出

$$
v_p(A(n))=\sum_{j\ge1}f(n,p^j).
$$

对 $p\ge7$，每个整除 $5n+1$ 的 $p^j$ 都满足 PM1，故各贡献一个单位。素数五不整除 $5n+1$。若 $p\nmid5n+1$，则 $v_p(A(n))\ge0=v_p(5n+1)$。

对素数二，由 $v_2((2m)!)=m+v_2(m!)$ 反复化简，

$$
v_2(A(n))=7n+v_2(n!)-v_2((5n)!)-v_2((3n)!)
=v_2\binom{8n}{5n}.
$$

若 $2\mid5n+1$，则 $n$ 为奇数，$3n$ 是二进单位。恒等式

$$
(5n+1)\binom{8n}{5n+1}=3n\binom{8n}{5n}
$$

遂给出 $v_2(A(n))\ge v_2(5n+1)$。

对素数三，令 $v=v_3(5n+1)$。若 $v=0$，结论显然。否则 $3^j$ 对 $2\le j\le v$ 各贡献一，共 $v-1$ 个单位；不把 $j=1$ 的贡献假定为一。另取

$$
k=\lfloor\log_3(10n)\rfloor+1,\qquad q=3^k.
$$

则 $10n<q\le30n$，PM1 给出 $f(n,q)=1$。又 $q>5n+1$，而 $3^v\le5n+1$，故 $k>v$，这项未被前面的 $2,\ldots,v$ 重复计入。总计至少 $v$ 个单位。全部素数赋值均满足所需不等式，唯一分解给出整除。证毕。

## PM.2 同一阶乘比的正矩表示

**定义。** 令

$$
S=\frac{30^{30}}{15^{15}10^{10}6^6}=2^{14}3^9 5^5,
\qquad r_n=\frac{A(n)}{S^n},
$$

并置

$$
\boldsymbol\alpha=\frac1{30}(1,7,11,13,17,19,23,29),
\qquad
\boldsymbol\beta=\left(\frac15,\frac13,\frac25,\frac12,\frac35,\frac23,\frac45,1\right).
$$

记 $(a)_n=a(a+1)\cdots(a+n-1)$，且 $(a)_0=1$。

**定理 PM3。** 对所有 $n\ge0$，

$$
\boxed{r_n=\prod_{i=1}^{8}\frac{(\alpha_i)_n}{(\beta_i)_n}.}
$$

存在一个在 $(0,1)$ 的每个非空开区间上都有正质量的概率测度 $\mu$，使

$$
\boxed{r_n=\int_0^1 x^n\,d\mu(x).}
$$

**证明。** 阶乘的相邻项比给出

$$
\frac{r_{n+1}}{r_n}
=\frac{\prod_{j=1}^{30}(n+j/30)(n+1)}
{\prod_{j=1}^{15}(n+j/15)\prod_{j=1}^{10}(n+j/10)\prod_{j=1}^{6}(n+j/6)}.
$$

约去公共因子，分子留下八个 $n+\alpha_i$，分母留下八个 $n+\beta_i$；两边在零处都为一，归纳得到第一式。

逐项有 $0<\alpha_i<\beta_i$。取相互独立的随机变量 $X_i$，其密度为

$$
\frac{x^{\alpha_i-1}(1-x)^{\beta_i-\alpha_i-1}}
{\mathrm B(\alpha_i,\beta_i-\alpha_i)},\qquad0<x<1.
$$

Beta 积分给出 $\mathbb E[X_i^n]=(\alpha_i)_n/(\beta_i)_n$。令 $X=\prod_iX_i$，其分布 $\mu$ 便满足矩等式。每个因子密度在 $(0,1)$ 为正；对任意 $x\in(0,1)$，取八个因子均在 $x^{1/8}$ 附近的充分小开区间，其乘积落在 $x$ 的指定邻域，联合概率为正。因此 $\mu$ 在每个非空开区间上有正质量。证毕。

阶乘比与超几何参数消去的背景见 J. W. Bober, *Factorial ratios, hypergeometric series, and a family of step functions*, J. London Math. Soc. 79 (2009), 422–444, [arXiv:0709.1977](https://arxiv.org/abs/0709.1977)。Gamma 型矩与阶乘比 Hausdorff 矩问题见 M. Wang, *Moments of Gamma type and three-parametric Mittag-Leffler function*, [arXiv:2410.19330](https://arxiv.org/abs/2410.19330)。PM3 的具体参数与概率构造由上面的约分和独立乘积给出。

## PM.3 一个具有无限隐藏谱的固定观察实现

**定义。** 在 $\mathcal H=L^2(\mu)$ 上取 $Kf(x)=xf(x)$，令 $e(x)=1$，令 $P$ 为到 $\mathbb C e$ 的正交投影。此处 $K$ 是固定的正收缩演化；不附加保持常数函数的随机转移要求。

**定理 PM4。** 有 $0\le K\le I$、$\|e\|=1$，且

$$
r_n=\langle e,K^ne\rangle.
$$

对每个 $N\ge0$，Hankel 矩阵 $(r_{i+j})_{0\le i,j\le N}$ 严格正定。不存在有限维线性空间上的固定算子 $T$、向量 $v$ 与线性泛函 $c$，使 $r_n=c(T^nv)$ 对所有 $n$ 成立。

**证明。** 乘法函数 $x$ 取值于 $[0,1]$，故算子正且收缩。概率质量为一给出单位范数，矩公式由 PM3 得到。对非零系数向量 $(a_0,\ldots,a_N)$，

$$
\sum_{i,j=0}^{N}\overline a_i r_{i+j}a_j
=\int\left|\sum_{i=0}^{N}a_ix^i\right|^2d\mu(x)>0.
$$

最后一个严格不等式来自非零多项式在某个开区间上不为零，以及 PM3 的满区间支撑。若存在维数 $d$ 的线性实现，则每个 Hankel 矩阵通过映射 $a\mapsto\sum_j a_jT^jv$ 与 $w\mapsto(c(T^iw))_i$ 因子化，秩不超过 $d$。取 $N=d$ 与严格正定性矛盾。证毕。

**命题。** PM4 的矩实现不蕴含某个指定有限群在 $\mathcal H$ 上的作用，也不蕴含该作用与 $K,P$ 的交换性。

**证明。** PM4 的构造仅指定测度、乘法算子和常数投影，没有指定群到酉算子的同态；群作用及交换性是另外的数据和等式。证毕。

## PM.4 正收缩系统的反馈质量界

**假设。** 设 $\mathcal H=V\oplus H$ 为复 Hilbert 空间的正交分解，其中 $1\le d=\dim V<\infty$，$H$ 可为无限维。设固定有界算子满足 $0\le K\le I$，并写

$$
K=\begin{pmatrix}A&B\\B^*&D\end{pmatrix},\qquad
R_n=\operatorname{pr}_V K^n|_V,\qquad
M_j=BD^jB^*.
$$

**定义。** 令 $F_1=A$，$F_{j+2}=M_j$。

**定理 PM5。** 每个 $F_n$ 均半正定，且对所有 $N\ge1$，

$$
\boxed{\sum_{n=1}^{N}F_n\le I_V.}
$$

**证明。** $A,D$ 是正收缩压缩，故 $BD^jB^*\ge0$。令 $H_m=\sum_{j=0}^mD^j$。由于这些幂互相交换，

$$
H_m(I-D)H_m=H_m-H_mD^{m+1}\le H_m.
$$

在 $I-K\ge0$ 的二次型中代入 $(v,H_mB^*v)$，得到

$$
\begin{aligned}
0&\le\langle v,(I-A)v\rangle
-2\langle B^*v,H_mB^*v\rangle
+\langle H_mB^*v,(I-D)H_mB^*v\rangle\\
&\le\langle v,(I-A-BH_mB^*)v\rangle.
\end{aligned}
$$

所以 $A+\sum_{j=0}^mM_j\le I$，而 $N=1$ 由 $A\le I$。证毕。

**定理 PM6。** 在 $\operatorname{End}(V)$ 的形式幂级数环中，

$$
R(z)=I+\sum_{n\ge1}R_nz^n,
\qquad
\boxed{R(z)^{-1}=I-\sum_{n\ge1}F_nz^n.}
$$

因此 $M_j$ 由 $R_1,\ldots,R_{j+2}$ 唯一决定。

**证明。** 把 MF1 应用于零隐藏初态，得到

$$
R_{n+1}=AR_n+\sum_{i=0}^{n-1}M_{n-1-i}R_i,
\qquad R_0=I.
$$

乘以相应形式幂并求和，按既定组合次序有 $(I-zA-z^2M(z))R(z)=I$。常数项为 $I$ 的形式级数有唯一双侧逆，故得到所示等式。逐系数递归时，第 $j$ 个核只消费至 $j+2$ 的响应。证毕。

**命题。** 若 $d=1$，则 $F_n\ge0$ 且 $\sum_{n\ge1}F_n\le1$；响应级数逆的系数绝对值总和至多二。

**证明。** 对 PM5 的单调有界部分和取极限，逆级数的常数项为一，其余项为 $-F_n$。证毕。这与 Kaluza 的倒数级数符号判据及更新级数结构相容；参见 Á. Baricz, J. Vesti, M. Vuorinen, *On Kaluza's sign criterion for reciprocal power series*, Ann. Univ. Mariae Curie-Skłodowska Sect. A 65(2) (2011), 1–16, [arXiv:1010.5337](https://arxiv.org/abs/1010.5337)。

## PM.5 不依赖滞后的有限前缀误差界

**假设。** 两个系统均满足 PM.4，并使用同一个可见空间 $V$；其隐藏空间和算子可以不同。把第二个系统的响应与核记作 $\widehat R_n,\widehat M_j$。设 $H_0\ge0$，且

$$
\max_{1\le n\le H_0+2}\|\widehat R_n-R_n\|\le\eta.
$$

**定理 PM7。** 对全部 $0\le j\le H_0$，

$$
\boxed{\|\widehat M_j-M_j\|\le(d+1)^2\eta.}
$$

在标量可见空间中，该界为 $4\eta$，与 $H_0$、隐藏维数、谱分离距离及非零耦合的最小值无关。

**证明。** 写 $Q(z)=R(z)^{-1}$、$\widehat Q(z)=\widehat R(z)^{-1}$。PM5 与半正定矩阵的 $\|F_n\|\le\operatorname{tr}F_n$ 给出对每个 $N$，

$$
\sum_{n=0}^{N}\|Q_n\|
=1+\sum_{n=1}^{N}\|F_n\|
\le1+\operatorname{tr}\left(\sum_{n=1}^{N}F_n\right)\le1+d,
$$

第二个系统同理。在非交换形式级数环中，

$$
\widehat Q-Q=\widehat Q(R-\widehat R)Q.
$$

比较第 $j+2$ 个系数；每个响应差的指标不超过 $j+2\le H_0+2$，零阶响应差为零。使用次乘法性并扩张有限求和区域，得到

$$
\|\widehat Q_{j+2}-Q_{j+2}\|
\le\eta\left(\sum_{a=0}^{j+2}\|\widehat Q_a\|\right)
\left(\sum_{b=0}^{j+2}\|Q_b\|\right)
\le(d+1)^2\eta.
$$

而 $Q_{j+2}=-M_j$、$\widehat Q_{j+2}=-\widehat M_j$。证明没有分离特征值、除以耦合或选择隐藏坐标。证毕。

**命题。** PM7 的前提强于分别要求每个响应矩阵范数不超过一。

**证明。** 正收缩共同实现要求 $R_n$ 来自同一个算子的幂。标量情形下它还要求例如 $r_0r_2\ge r_1^2$。有界数列 $r_0=1,r_1=1,r_2=0$ 违反此式，虽各项都在 $[0,1]$。因此逐项截断到单位区间或单位球并不能履行 PM7 的前提。证毕。

## PM.6 从有误差的标量数据得到相容恢复

**定义。** 对 $N\ge1$ 定义截断矩集

$$
\mathcal C_N=\left\{\left(\int x^n\,d\nu(x)\right)_{n=1}^{N}:
\nu\text{ 是 }[0,1]\text{ 上的概率测度}\right\}.
$$

**定理 PM8。** $\mathcal C_N$ 是紧集，其中每个向量都可由至多 $N+1$ 个原子的概率测度实现。给定数据 $d_1,\ldots,d_N$，最小化 $\max_{n\le N}|r_n-d_n|$ 的相容向量存在。

**证明。** 令 $\gamma(x)=(x,x^2,\ldots,x^N)$。$\gamma([0,1])$ 紧。其凸包由 Carathéodory 定理表示为至多 $N+1$ 个曲线点的凸组合，因而是紧参数空间 $[0,1]^{N+1}\times\Delta_N$ 的连续像，仍紧。有限原子测度给出凸包中的每一点；任意概率测度的积分可由有限分割上的加权点和逼近，因此属于该闭凸包。最大绝对残差是连续函数，在紧集上取得最小值。证毕。

**定理 PM9。** 设真实 $r_n$ 是任意 $[0,1]$ 概率测度的矩，并有 $|d_n-r_n|\le\epsilon$（$1\le n\le H_0+2$）。取 PM8 中 $N=H_0+2$ 的任一最小残差相容向量，再通过 PM6 恢复 $\widehat m_0,\ldots,\widehat m_{H_0}$。则

$$
\boxed{\max_{0\le j\le H_0}|\widehat m_j-m_j|\le8\epsilon.}
$$

**证明。** 真实矩向量属于可行集，故最优残差不超过 $\epsilon$，三角不等式给出相容估计矩与真实矩的距离至多 $2\epsilon$。对每个实现该有限向量的概率测度，取乘法算子与常数投影，均满足 PM.4，且其前 $H_0+1$ 个记忆系数只依赖这个有限向量。以 $d=1,\eta=2\epsilon$ 应用 PM7。证毕。

## PM.7 对称约化后的矩阵元数量与误差

**假设。** 给定有限群的已知复酉等型分解

$$
\mathcal H=\bigoplus_\lambda\left(V_\lambda\otimes W_\lambda\right),
\qquad \rho(g)=\bigoplus_\lambda(I\otimes\rho_\lambda(g)),
$$

其中 $W_\lambda$ 是两两不等价的有限维不可约表示，重数空间 $V_\lambda$ 可含任意多个隐藏方向。设 $0\le K\le I$，且 $K,P$ 均与群作用交换；$P$ 在第 $\lambda$ 个重数空间保留 $r_\lambda<\infty$ 维，非零 $r_\lambda$ 仅有限多个。固定这些分解与观察坐标。

**定理 PM10。** 在每个 $W_\lambda$ 选定一个单位向量 $e_\lambda$。读取

$$
\left\langle e_a\otimes e_\lambda,K^t(e_b\otimes e_\lambda)\right\rangle,
\quad1\le a,b\le r_\lambda,\quad1\le t\le H_0+2,
$$

足以确定全部 $0\le j\le H_0$ 的观察记忆核。每个时间所需复矩阵元数为 $\sum_\lambda r_\lambda^2$，不依赖 $\dim W_\lambda$。

若逐项数据误差至多 $\epsilon$，并选取任意在这些数据上逐项残差不超过 $\epsilon$ 的共同正收缩响应实现，则令 $r_*=\max_\lambda r_\lambda$，有

$$
\boxed{
\max_{0\le j\le H_0}\|\widehat M_j-M_j\|
\le2r_*(r_*+1)^2\epsilon.
}
$$

**证明。** Schur 分解给出 $K=\bigoplus_\lambda(K_\lambda\otimes I)$ 和相应的 $P$ 分解。所列矩阵元恰是每个保留重数空间上的完整压缩响应条目；用 PM6 逐块恢复后再张量回去。真实实现本身满足数据误差条件，所以要求残差不超过 $\epsilon$ 的正收缩可行集非空。两个实现相对数据各误差至多 $\epsilon$，故每个条目之差至多 $2\epsilon$；一个 $r_\lambda$ 方阵的算子范数不超过其 Frobenius 范数，因而响应误差至多 $2r_\lambda\epsilon$。逐块应用 PM7，再取正交直和的范数上确界，即得所示界。证毕。

## PM.8 有限前缀与尾部的不同要求

**命题。** PM7 至 PM10 不要求任何正谱隙或非零耦合下界，但只控制由已观测前缀确定的核系数。

**证明。** PM7 的卷积系数仅消费不超过 $H_0+2$ 的响应差，未约束更晚的响应；证明未使用隐藏谱间距或逆耦合。证毕。

**定理 PM11。** 在 PM7 的两个系统中，若另有 $\|D\|,\|\widehat D\|\le\theta<1$，其中 $0\le\theta<1$，则

$$
\sum_{j\ge0}\|\widehat M_j-M_j\|
\le(H_0+1)(d+1)^2\eta+\frac{2\theta^{H_0+1}}{1-\theta}.
$$

**证明。** 前 $H_0+1$ 项由 PM7 控制。正收缩的交叉块满足 $\|B\|,\|\widehat B\|\le1$，所以 $\|M_j\|,\|\widehat M_j\|\le\theta^j$；对剩余几何级数求和即得。证毕。

**命题。** PM3–PM4 的具体响应满足 PM7–PM9 的正性前提，并具有无限秩 Hankel 矩阵。PM4 没有给出 $\|D\|<1$ 的严格收缩常数。

**证明。** 前两项分别由乘法算子的正收缩性和 PM4 的严格正定性得到。$\mu$ 的支撑逼近一，故 $\|K\|=1$；已给出的压缩估计只能推出 $\|D\|\le1$，不能用它替代 PM11 所要求的严格上界。证毕。

**定理 PM12（PM10 的更正）。** 在每个 $W_\lambda$ 选定一个单位向量 $e_\lambda$，并设至少有一个 $r_\lambda\ge1$。读取

$$
\left\langle e_a\otimes e_\lambda,K^t(e_b\otimes e_\lambda)\right\rangle,
\quad1\le a,b\le r_\lambda,\quad1\le t\le H_0+2,
$$

足以确定全部 $0\le j\le H_0$ 的观察记忆核。每个时间所需复矩阵元数为 $\sum_\lambda r_\lambda^2$，不依赖 $\dim W_\lambda$。

若逐项数据误差至多 $\epsilon$，并选取任意在这些数据上逐项残差不超过 $\epsilon$ 的共同正收缩响应实现，则令 $r_*=\max_\lambda r_\lambda$，有

$$
\boxed{
\max_{0\le j\le H_0}\|\widehat M_j-M_j\|
\le2r_*(r_*+1)^2\epsilon.
}
$$

**证明。** Schur 分解给出 $K=\bigoplus_\lambda(K_\lambda\otimes I)$ 和相应的 $P$ 分解。所列矩阵元恰是每个保留重数空间上的完整压缩响应条目；用 PM6 逐块恢复后再张量回去。真实实现本身满足数据误差条件，所以要求残差不超过 $\epsilon$ 的正收缩可行集非空。两个实现相对数据各误差至多 $\epsilon$，故每个条目之差至多 $2\epsilon$；一个 $r_\lambda$ 方阵的算子范数不超过其 Frobenius 范数，因而响应误差至多 $2r_\lambda\epsilon$。逐块应用 PM7，再取正交直和的范数上确界，即得所示界。其中 $r_\lambda=0$ 的块不贡献矩阵元或记忆核系数，以下仅在 $r_\lambda\ge1$ 的块上恢复并应用 PM7。证毕。

本定理取代定理 PM10 的陈述与证明；PM10 在允许全部 $r_\lambda=0$ 时其界 $r_*$ 无定义，且其证明对零维块误用 PM7。

# 补编 AT：严格收缩、多重模态与全时域目标恢复

## AT.1 单隐藏模态误差界的保留收缩系数形式

**假设。** 沿用 FM.5 的三个测量、预处理与误差假设，并令 $0<\theta<1$、$|w|\le\theta$。在估计器中把传播参数截断到 $[-\theta,\theta]$。

**命题 AT1。** 对 $j\ge0$，其中第二项在 $j=0$ 时定义为零，

$$
|\widehat m_j-gw^j|
\le 3\epsilon\theta^j+(8+3\theta)\epsilon j\theta^{j-1}.
$$

因此

$$
\boxed{\sum_{j=0}^{\infty}|\widehat m_j-gw^j|
\le \frac{11\epsilon}{(1-\theta)^2}.}
$$

**证明。** FM.5 的估计给出 $|\widehat g-g|\le3\epsilon$ 和 $|\widehat z-gw|\le8\epsilon$。若 $\widehat g\le0$，则 $g\le3\epsilon$，逐项误差不超过 $3\epsilon\theta^j$。若 $\widehat g>0$，截断的非扩张性给出

$$
\widehat g|\widehat w-w|
\le |\widehat z-\widehat g w|
\le (8+3\theta)\epsilon.
$$

利用 $|x^j-y^j|\le j\theta^{j-1}|x-y|$，分解幅度误差和传播误差即得逐项界。求和后，系数为

$$
\frac3{1-\theta}+\frac{8+3\theta}{(1-\theta)^2}
=\frac{11}{(1-\theta)^2}.
$$

证明不需要对 $g$ 或 $\widehat g$ 设正下界。证毕。

## AT.2 稳定消去多项式与尾部常数

**定义。** 对序列 $u=(u_n)_{n\ge0}$，令移位算子 $(Eu)_n=u_{n+1}$。对 $0\le\theta<1$ 和整数 $q\ge0$ 定义

$$
T_q(\theta)=\frac12\left[\left(\frac{1+\theta}{1-\theta}\right)^q-1\right],
\qquad C_q(\theta)=q+T_q(\theta).
$$

**假设。** $u_n$ 取值于复赋范空间，存在 $q$ 个复数 $\lambda_1,\ldots,\lambda_q$，允许重复，满足 $|\lambda_i|\le\theta$ 以及

$$
\prod_{i=1}^q(E-\lambda_i)u=0.
$$

空乘积按恒等算子解释，因此 $q=0$ 的假设表示 $u$ 恒为零。设 $\delta\ge0$，且 $\|u_i\|\le\delta$ 对 $0\le i<q$ 成立。

**定理 AT2。** 对每个 $N\ge0$，

$$
\sum_{n=0}^{N-1}\|u_{q+n}\|\le T_q(\theta)\delta.
$$

特别地，范数序列可求和，并且

$$
\boxed{\sum_{n\ge0}\|u_n\|\le C_q(\theta)\delta.}
$$

（文献：N. G. de Bruijn, Acta Math. Acad. Sci. Hungar. 11 (1960) 213–216, §§3–5）

**证明。** 对消去多项式的次数归纳。零次情形显然。设次数为 $q+1$，选取一个根 $a$，令 $v=(E-a)u$。移位与标量乘法交换，所以 $v$ 被剩余的 $q$ 个因子消去。对 $i<q$，

$$
\|v_i\|\le \|u_{i+1}\|+|a|\|u_i\|\le(1+\theta)\delta.
$$

归纳假设给出

$$
\sum_{n<N}\|v_{q+n}\|\le T_q(\theta)(1+\theta)\delta.
$$

固定有限 $N$，记

$$
S_N=\sum_{n<N}\|u_{q+1+n}\|,\qquad
P_N=\sum_{n<N}\|u_{q+n}\|.
$$

有限和的移位恒等式与 $\|u_q\|\le\delta$ 给出 $P_N\le\delta+S_N$。又由 $u_{n+1}=a u_n+v_n$，

$$
S_N\le\theta P_N+T_q(\theta)(1+\theta)\delta.
$$

因此

$$
(1-\theta)S_N\le
[\theta+(1+\theta)T_q(\theta)]\delta.
$$

$T_0=0$，且所定义的常数直接满足

$$
T_{q+1}(\theta)=
\frac{\theta+(1+\theta)T_q(\theta)}{1-\theta}.
$$

这证明全部有限尾和的界。加上前 $q+1$ 项各自的观测界，得到全部有限部分和有界。非负部分和单调收敛，遂得可求和性与无穷和界。归纳过程中没有预先假设可求和性，也没有对根差、模态权重或特征向量矩阵求逆。证毕。

**注。** 有理生成函数的系数控制与 Turán 型幂和不等式之间的关系见 Batenkov 与 Yomdin，*Taylor Domination, Turán lemma, and Poincaré-Perron Sequences*，arXiv:1301.6033；Contemporary Mathematics 659 (2016), 1–15。AT2 在此给出直接的有限尾和证明。

## AT.3 两个实际有限模态族的目标误差

**假设。** 设

$$
f_n=\sum_{i=1}^d c_i\lambda_i^n,
\qquad \widetilde f_n=\sum_{i=1}^e\widetilde c_i\widetilde\lambda_i^n,
$$

其中节点为实数，$|\lambda_i|,|\widetilde\lambda_i|\le\theta<1$。权重允许有符号或为零，节点允许重复，两个模型可以具有不同模态数。令 $q=d+e$，并假设 $|f_i-\widetilde f_i|\le\delta$ 对 $i<q$ 成立。

**推论 AT3。**

$$
\sum_{n\ge0}|f_n-\widetilde f_n|\le C_q(\theta)\delta.
$$

**证明。** 差序列被所有节点对应的一次移位因子的乘积消去，应用 AT2。也可以对实际模态逐一使用

$$
f_{n+1}-a f_n=\sum_i c_i(\lambda_i-a)\lambda_i^n,
$$

其中节点为 $a$ 的选定项恰好消失。该恒等式对零权重和重复节点同样成立。证毕。

**注。** 无分离条件下的稀疏矩恢复已有相关研究：Fan 与 Li，*Efficient Algorithms for Sparse Moment Problems without Separation*，COLT 2023，PMLR 195:3510–3565，arXiv:2207.13008。该文讨论混合分布的运输距离恢复；AT3 的目标是整个输出序列的绝对误差和。

## AT.4 常数在一般稳定递推类中的最优性

**定理 AT4。** 对固定 $q\ge1$、$0\le\theta<1$，AT2 的常数 $C_q(\theta)$ 在满足该假设的实标量递推类上不能减小。

**证明。** 取唯一满足

$$
(E-\theta)^q u=0,\qquad u_i=(-1)^{q-1-i}\quad(0\le i<q)
$$

的序列。证明其从第 $q-1$ 项开始非负，并且尾和恰为 $T_q(\theta)$，对 $q$ 归纳。$q=1$ 时 $u_n=\theta^n$。若 $q\ge2$，令 $v=(E-\theta)u$，则

$$
v_i=(1+\theta)(-1)^{q-2-i}\quad(0\le i<q-1),
\qquad (E-\theta)^{q-1}v=0.
$$

由归纳假设，$v_n\ge0$ 对 $n\ge q-2$ 成立。又 $u_{q-1}=1$，从而递推 $u_{n+1}=\theta u_n+v_n$ 使全部 $n\ge q-1$ 的 $u_n$ 非负。AT2 已经证明这些序列绝对可求和。对 $n\ge q-1$ 的递推求和，令 $U=\sum_{n\ge q}u_n$，得到

$$
U=\theta(1+U)+(1+\theta)T_{q-1}(\theta),
$$

故 $U=T_q(\theta)$。前 $q$ 项绝对值均为一，所以总绝对和为 $C_q(\theta)$。乘以任意 $\delta\ge0$ 即得相应尺度。证毕。

**推论。** 若 $\theta>0$，即使只允许实的、彼此不同的指数节点，且不对有符号权重施加统一上界，也不存在小于 $C_q(\theta)$ 的通用常数。

**证明。** 选择 $q$ 个彼此不同、从下方趋近 $\theta$ 的节点，并保持 AT4 的前 $q$ 项不变。对应 Vandermonde 系统可逆，确定一个实际指数和。递推系数随节点连续变化，所以任意固定长度的输出前缀收敛到 AT4 的序列。任何小于 $C_q(\theta)$ 的数都小于该极限序列某个有限绝对部分和，故足够近的不同节点也违反这个较小常数。证毕。

**注。** 本最优性允许权重在节点碰撞时变得很大。对正权重、给定总质量或正收缩整体实现的子类，本命题没有断言常数仍然最优。$\theta=0$ 的单纯指数和类与零根 Jordan 递推类也须分别处理。

## AT.5 有限隐藏空间的目标核

**假设。** 两个分块演化具有共同的可见空间，隐藏空间分别为有限维复空间，维数为 $d,e$；核分别为

$$
M_j=B D^j C,\qquad \widetilde M_j=\widetilde B\widetilde D^j\widetilde C.
$$

所有隐藏特征值的模不超过 $\theta<1$。在同一个算子范数中，$\|M_j-\widetilde M_j\|\le\delta$ 对 $j<d+e$ 成立。

**推论 AT5。**

$$
\sum_{j\ge0}\|M_j-\widetilde M_j\|\le C_{d+e}(\theta)\delta.
$$

**证明。** Cayley–Hamilton 定理分别给出两个核序列的特征多项式消去关系。两个特征多项式的乘积消去差序列，在复数域分解后应用 AT2。该论证容许 Jordan 块，也没有要求 $B,C$ 或其乘积可逆。若已知更低次数的目标消去多项式，可用该次数替换 $d+e$。证毕。

**注。** 对实自伴随隐藏传播，谱分解直接把标量矩阵元化为 AT3。对一般实算子作复化时，应显式选择与所声明算子范数相容的复化结构。

## AT.6 从有噪声可见响应到全记忆核

**假设。** 在标量可见空间与至多 $r$ 维实隐藏空间上，真实整体传播为

$$
K=\begin{pmatrix}a&b^*\\b&D\end{pmatrix},\qquad
0\le K\le I,\qquad 0\le D\le\theta I,\quad \theta<1.
$$

记 $s_n=\langle e,K^n e\rangle$，$s_0=1$，$m_j=\langle b,D^j b\rangle$。另一个模型 $\widetilde K$ 满足同样的约束。设 $|s_i-\widetilde s_i|\le\eta$ 对 $1\le i\le L$ 成立。

**引理。** 对 $0\le j\le L-2$，$|m_j-\widetilde m_j|\le4\eta$。

**证明。** 分块消元给出形式幂级数恒等式

$$
R(z)=\sum_{n\ge0}s_nz^n,\qquad
Q(z)=R(z)^{-1}=1-az-z^2\sum_{j\ge0}m_jz^j.
$$

由于 $D\ge0$，$m_j\ge0$。对 $I-K\ge0$ 使用 Schur 补，且 $I-D$ 可逆，得到

$$
a+\sum_{j\ge0}m_j
=a+\langle b,(I-D)^{-1}b\rangle\le1.
$$

因此 $Q$ 的系数绝对和不超过 $2$，另一个模型同样成立。由

$$
\widetilde Q-Q=\widetilde Q\,(R-\widetilde R)\,Q,
$$

截至 $L$ 次的任一系数差不超过 $2\eta\cdot2$。第 $j+2$ 次系数正是负的记忆核差，得到结论。此证明要求两个响应序列均由相容的正收缩模型产生。证毕。

**定义。** 对 $1\le i\le2r+1$ 的有噪声响应 $y_i$，假设 $|y_i-s_i|\le\epsilon$。在固定 $r+1$ 维矩阵空间中，把较低维模型补零，在上述正收缩约束集合上最小化 $\max_i|y_i-\langle e,\widetilde K^i e\rangle|$。

**推论 AT6。** 该全局最小化问题有解，且任意全局最小解满足

$$
\boxed{\sum_{j\ge0}|\widetilde m_j-m_j|
\le8\epsilon\,C_{2r}(\theta).}
$$

**证明。** 约束集合是非空紧集，目标函数连续。真实补零模型的目标值不超过 $\epsilon$，故最小解同样如此，两个模型的响应差不超过 $2\epsilon$。引理给出前 $2r$ 个记忆系数的误差至多 $8\epsilon$。两个隐藏自伴随矩阵各至多有 $r$ 个谱模态，应用 AT3。证毕。

**注。** 这里证明了估计器的存在性与误差保证，没有证明全局最小化的多项式时间算法。独立逐项截断一个任意测量序列不保证它具有相容的正收缩实现。若只求得目标值至多 $\epsilon+\tau$ 的可行模型，上式中的 $8\epsilon$ 改为 $4(2\epsilon+\tau)$。

## AT.7 素数寄存器的一个可逆随机演化实现

**定义。** 取 $m\ge2$ 个互异素数 $p_1,\ldots,p_m$ 和平方自由容量 $N=\prod_i p_i$。状态 $b\in\{0,1\}^m$ 编码为 $n(b)=\prod_i p_i^{b_i}$，定义观察量

$$
F(b)=\boldsymbol1_{\{n(b)\text{ 为素数}\}}
=\boldsymbol1_{\{|b|=1\}}.
$$

在均匀概率测度 $\pi$ 上定义演化

$$
(Kf)(b)=\frac12f(b)+\frac1{2m}\sum_{i=1}^m f(b\oplus e_i).
$$

这里一步操作要么不变，要么翻转一个二态寄存器。编码后的操作为在合法范围内乘以或除以一个已知素数。

**命题 AT7。** $K$ 是自伴随正收缩；坐标置换群 $S_m$ 的表示与 $K$ 交换。其平凡等型分量具有维数 $m+1$。

**证明。** 每条翻转边的正反概率均为 $1/(2m)$，均匀测度满足细致平衡。Walsh 函数 $\chi_S(b)=(-1)^{\sum_{i\in S}b_i}$ 是正交特征基，对应特征值 $1-|S|/m\in[0,1]$。置换同时置换翻转方向，故交换。置换不变函数恰为 Hamming 重量的函数，共有 $m+1$ 个重量层。证毕。

**定义。** 令 $p=m/2^m$，$e=(F-p)/\sqrt{p(1-p)}$。在 $L^2(\pi)$ 中令 $P$ 为到 $\operatorname{span}\{1,e\}$ 的正交投影，$Q=I-P$。

**命题 AT8。** 隐藏传播 $D=QKQ|_{\operatorname{ran}Q}$ 满足

$$
0\le D\le(1-1/m)I.
$$

中心化响应满足

$$
\boxed{\langle e,K^t e\rangle=
\sum_{k=1}^m
\frac{\binom mk(m-2k)^2}{m(2^m-m)}\left(1-\frac km\right)^t.}
$$

$t=0$ 时采用 $0^0=1$ 的幂约定。若 $m$ 为偶数，则 $k=m/2$ 项的权重恰为零。

**证明。** 常数方向属于可见空间，隐藏空间正交于特征值为一的常数模态，其余特征值最大为 $1-1/m$，压缩保持二次型上下界。对 $|S|=k\ge1$，

$$
\langle F,\chi_S\rangle=\frac{m-2k}{2^m}.
$$

除以 $\|F-p\|=\sqrt{m(2^m-m)}/2^m$ 后平方，再把同一 $k$ 的 $\binom mk$ 个模态相加，即得公式。证毕。

**注。** $P$ 在不变子空间内只选择两个方向；它不是投影到整个 $S_m$ 不变子空间的群平均算子。因此 $K$ 的置换对称性不强制 $PKQ=0$。这里的素数标签预先给定；该模型没有给出新素数搜索算法，也没有证明自然数序列中的素数分布。

## AT.8 三个素数寄存器产生两个非零记忆模态

**命题 AT9。** 对 AT.7 的 $m=3$，中心化响应为

$$
s_t=\frac15(2/3)^t+\frac15(1/3)^t+\frac35 0^t,
$$

且

$$
s_1=\frac15,\quad s_2=\frac19,\quad s_3=\frac1{15},
\qquad m_0=\frac{16}{225},\quad m_1=\frac{34}{1125}.
$$

全部记忆系数的生成函数为

$$
\boxed{M(z)=\sum_{j\ge0}m_jz^j
=\frac{16/225-(2/75)z}{1-(4/5)z+(2/15)z^2}.}
$$

因此

$$
m_{j+2}=\frac45m_{j+1}-\frac2{15}m_j,
\qquad \lambda_\pm=\frac25\pm\frac{\sqrt6}{15}.
$$

两个极点没有被分子消去，对应两个非零目标模态，且都小于 $2/3$。

**证明。** 在 AT8 中代入 $m=3$。相加三个几何级数得

$$
R(z)=\frac{1-(4/5)z+(2/15)z^2}{1-z+(2/9)z^2}.
$$

代入 $M(z)=[1-s_1z-R(z)^{-1}]/z^2$ 并约分得所述生成函数。分母的两个特征根为 $\lambda_\pm$，分子只有一个有理根，因而不能消去这两个无理极点。又 $m_0>0$，固定观察下的反馈记忆非零。证毕。

**推论。** 在三个寄存器模型的非恒定对称子空间内，把记忆可达部分限制为两个隐藏维度，可使用 $r=2$、$\theta=2/3$ 的 AT6。由五个中心化响应样本得到的误差保证为 $8\epsilon C_4(2/3)=2528\epsilon$。

**证明。** 响应有三个不同的非零权重谱原子，包括零节点，故循环空间维数为三；移除一个可见方向后，其隐藏部分维数为二。计算 $C_4(2/3)=4+(5^4-1)/2=316$ 即得。该常数是通用上界，没有声称对这个固定正模型最优。证毕。

## AT.9 响应读数的轨迹含义与一个有限抽样界

**命题。** 对平稳初始分布 $\pi$ 的 AT.7 马尔可夫链，

$$
s_t=\mathbb E_\pi[e(X_0)e(X_t)].
$$

这些响应是二时刻相关函数，需要以重复轨迹或具有适当误差保证的统计程序估计。一个时刻的二元读数 $F(X_t)$ 本身不等于 $s_t$。

**证明。** 条件于 $X_0=b$，$\mathbb E[e(X_t)\mid X_0=b]=(K^t e)(b)$，再对初态求期望即为 $\langle e,K^t e\rangle_\pi$。证毕。

**推论。** 对 $m=3$，取 $H$ 条相互独立、各自从均匀分布出发的长度五轨迹。以样本均值估计五个 $s_t$。若 $0<\alpha<1$，且

$$
H\ge\frac{32}{9\epsilon^2}\log\frac{10}{\alpha},\qquad\epsilon>0,
$$

则五个响应误差同时不超过 $\epsilon$ 的概率至少为 $1-\alpha$，相应 AT6 估计器的全核绝对误差以该概率不超过 $2528\epsilon$。

**证明。** $e$ 的两个值为 $5/\sqrt{15}$ 与 $-3/\sqrt{15}$，所以乘积 $e(X_0)e(X_t)$ 位于 $[-1,5/3]$，区间长度为 $8/3$。Hoeffding 不等式给出单个时刻的尾概率上界 $2\exp(-9H\epsilon^2/32)$，再对五个时刻取并集界。轨迹间的独立性足够，同一条轨迹的不同时刻不必独立。证毕。

**引文。** W. Hoeffding，*Probability Inequalities for Sums of Bounded Random Variables*，Journal of the American Statistical Association 58 (1963), 13–30，doi:10.1080/01621459.1963.10500830。

## AT.10 让素数值进入热浴动力学

**定义。** 对一般有限容量状态 $b_i\in\{0,\ldots,A_i\}$，$A_i\ge1$，定义能量和乘积 Gibbs 分布

$$
\mathcal E(b)=\log n(b)=\sum_i b_i\log p_i,
\qquad
\pi_\beta(b)=Z_\beta^{-1}n(b)^{-\beta},
$$

$$
Z_\beta=\sum_{n\mid\prod_i p_i^{A_i}}n^{-\beta}
=\prod_i\sum_{a=0}^{A_i}p_i^{-\beta a}.
$$

令 $H_i$ 把第 $i$ 个坐标重新抽样为分布

$$
\rho_i(a)=\frac{p_i^{-\beta a}}{\sum_{c=0}^{A_i}p_i^{-\beta c}},
$$

并保持其他坐标不变。定义 $K_\beta=m^{-1}\sum_i H_i$。

**命题 AT10。** 在 $L^2(\pi_\beta)$ 中，每个 $H_i$ 是自伴随正交投影，不同 $H_i$ 交换。$K_\beta$ 满足细致平衡，且其谱包含于

$$
\{1,1-1/m,\ldots,0\}.
$$

无论容量和完整状态数多大，任一中心化标量观察的循环空间维数至多为 $m$。

**证明。** $H_i$ 是对其余坐标的条件期望。乘积测度使不同坐标的平均交换。对 $S\subseteq\{1,\ldots,m\}$ 定义

$$
P_S=\prod_{i\in S}(I-H_i)\prod_{i\notin S}H_i.
$$

这些投影两两正交，和为恒等算子，并满足

$$
K_\beta P_S=(1-|S|/m)P_S.
$$

因此，按 $|S|=k$ 求和的投影 $\Pi_k$ 给出至多 $m+1$ 个特征值。中心化观察 $f$ 满足 $\Pi_0 f=0$，其循环空间包含于 $\operatorname{span}\{\Pi_1f,\ldots,\Pi_mf\}$。证毕。

**推论。** 对非零中心化观察，目标核可限制在至多 $m-1$ 维的隐藏循环空间内，并且该空间的隐藏压缩满足 $0\le D\le(1-1/m)I$。可以按此目标维数应用 AT6，而无需恢复完整的 $\prod_i(A_i+1)$ 个状态坐标。

**证明。** 观察的循环空间在自伴随 $K_\beta$ 下约化；从中移除一个可见方向，其余维数至多为 $m-1$。常数特征方向已经被中心化移除，所以非恒定谱的统一上界为 $1-1/m$。证毕。

**注。** 对平方自由容量，$\beta=0$ 时 $H_i=(I+\operatorname{flip}_i)/2$，恰好回到 AT.7。$\beta>0$ 时素数值通过抽样概率进入动力学。对固定且不同的素数标签，坐标置换一般不再是固定参数模型的对称性；投影交换结构仍然成立。

## AT.11 退化模态的出现、消失与连续恢复

**假设。** 在 AT.10 中取 $A_i=1$，$m\ge2$，互异素数标签，观察仍为 $F=\boldsymbol1_{\{|b|=1\}}$。令

$$
x_i=p_i^{-\beta},\quad
P_0=\prod_i(1+x_i)^{-1},\quad
p_F=P_0\sum_i x_i.
$$

**命题 AT11。** 中心化归一化响应在特征值 $1-k/m$ 上的权重为

$$
W_k(\beta)=\frac{P_0^2}{p_F(1-p_F)}
\sum_{|S|=k}\left(\prod_{i\in S}x_i\right)
\left(\sum_{j\notin S}x_j-k\right)^2,
\qquad 1\le k\le m.
$$

对每个 $\beta>0$，所有 $W_k(\beta)$ 都严格为正。对 $\beta=0$，恰在 $m$ 为偶数且 $k=m/2$ 时出现零权重。因此非恒定循环空间的维数在 $\beta>0$ 时为 $m$；在均匀极限，偶数 $m$ 时降为 $m-1$。

**证明。** 第 $i$ 个坐标的归一化中心函数在零和一上的取值分别为 $-\sqrt{x_i}$、$1/\sqrt{x_i}$。对其乘积基函数 $\chi_S$，对恰好一个坐标为一的状态求和，得到

$$
\langle F,\chi_S\rangle
=(-1)^{|S|}P_0\sqrt{\prod_{i\in S}x_i}
\left(\sum_{j\notin S}x_j-|S|\right).
$$

平方并按次数相加，除以方差即得权重公式。若 $1\le k<m$ 且 $W_k=0$，每一个 $k$ 元子集都满足 $\sum_{j\notin S}x_j=k$。选择两个只交换一个元素的子集，便得到任意两个 $x_i,x_j$ 相等。$\beta>0$ 与素数互异使这不可能。$k=m$ 时括号恒为 $-m$，所以该权重也非零。$\beta=0$ 时全部 $x_i=1$，括号为 $m-2k$。互异特征值的非零谱权重数等于循环空间维数。证毕。

**推论。** 若 $m$ 为偶数、$k=m/2$，则

$$
\lim_{\beta\downarrow0}\frac{W_k(\beta)}{\beta^2}
=\frac{\displaystyle\sum_{|S|=k}
\left(\sum_{j\notin S}\log p_j\right)^2}
{m(2^m-m)}>0.
$$

因此，即使只考虑 $\beta>0$、所有目标谱权重均非零的模型族，也不存在对该权重有效的统一正下界。

**证明。** 用 $x_i=1-\beta\log p_i+O(\beta^2)$ 展开 AT11。因 $m-k=k$，括号的常数项为零，一阶项为 $-\beta\sum_{j\notin S}\log p_j$。其他乘积因子连续趋于一，且 $P_0^2/[p_F(1-p_F)]$ 趋于 $1/[m(2^m-m)]$。有限求和允许逐项取极限；各素数对数严格为正。证毕。

## AT.12 预测项的接口与初态记忆的边界

**命题。** 对分块线性演化

$$
y_{n+1}=Ay_n+Bh_n,\qquad h_{n+1}=Cy_n+Dh_n,
$$

有

$$
y_{n+1}=Ay_n+BD^nh_0+\sum_{k=0}^{n-1}M_{n-1-k}y_k.
$$

若 $\sup_k\|y_k\|\le Y$，则沿同一给定历史，把 $M$ 换为 $\widetilde M$ 后，记忆卷积项的变化满足

$$
\sup_n\left\|\sum_{k=0}^{n-1}(\widetilde M_{n-1-k}-M_{n-1-k})y_k\right\|
\le Y\sum_{j\ge0}\|\widetilde M_j-M_j\|.
$$

**证明。** 迭代隐藏更新得到 $h_n=D^nh_0+\sum_{k<n}D^{n-1-k}Cy_k$，左乘 $B$。第二式对有限和使用三角不等式与算子范数，再以全绝对和为上界。证毕。

**注。** 目标核恢复本身没有确定未知初态的 $BD^nh_0$ 项，也没有恢复某条随机轨迹的完整隐藏状态。以上卷积误差比较固定同一历史；若递归使用模型自身预测的历史，还需对闭环误差传播另作稳定性证明。

# 补编 PN：正可逆状态机的全记忆恢复障碍

## PN.1 模型类、观察接口与风险

**定义。** 固定 $0<\kappa<1$。令 $\mathcal C_\kappa$ 为全部有限维实自伴随分块算子与指定单位可见方向组成的类，

$$
K=\begin{pmatrix}a&b^*\\b&D\end{pmatrix},\qquad 0\le K\le\kappa I.
$$

隐藏维数不设统一上界。观察与目标分别为

$$
s_n(K)=\langle e,K^n e\rangle,\qquad s_0=1,
\qquad m_j(K)=\langle b,D^j b\rangle.
$$

观察数据 $y=(y_n)_{n\ge1}$ 满足 $\sup_{n\ge1}|y_n-s_n(K)|\le\epsilon$。估计器可使用整个无限数据序列；其损失定义为 $\sum_{j\ge0}|\widehat m_j(y)-m_j(K)|$，发散时取 $+\infty$。令

$$
\mathfrak R_\kappa(\epsilon)=
\inf_{\widehat m}\sup_{K\in\mathcal C_\kappa}
\sup_{\|y-s(K)\|_\infty\le\epsilon}
\sum_{j\ge0}|\widehat m_j(y)-m_j(K)|.
$$

这是逐坐标有界、可对抗的相关读数误差模型。它没有赋予估计器完整转移矩阵、所有隐藏状态、所有高阶轨迹分布或任意干预读数。

## PN.2 正谱测度之差中的长平台

**定义。** 对 $q\ge1$ 和不同的 $\lambda_1,\ldots,\lambda_q\in(0,1)$，令

$$
c_i=\prod_{\ell\ne i}\frac{1-\lambda_\ell}{\lambda_i-\lambda_\ell},
\qquad u_n=\sum_{i=1}^q c_i\lambda_i^n.
$$

**定理 PN1。** 对所有 $n\ge0$，$0\le u_n\le1$；对 $0\le n<q$，$u_n=1$。此外

$$
\sum_{n\ge0}u_n=\sum_{i=1}^q\frac1{1-\lambda_i}.
$$

（文献：A. Sen, N. Balakrishnan, Statist. Probab. Lett. 43 (1999) 421–426, Theorem 1）

**证明。** 取相互独立的正整数值几何变量 $G_i$，$\Pr(G_i=k)=(1-\lambda_i)\lambda_i^{k-1}$，并令 $T=\sum_iG_i$。其概率生成函数为

$$
\mathbb E z^T=\frac{z^q\prod_i(1-\lambda_i)}{\prod_i(1-\lambda_i z)}.
$$

生存概率的生成函数满足

$$
\sum_{n\ge0}\Pr(T>n)z^n
=\frac{1-\mathbb E z^T}{1-z}.
$$

右式在 $z=1$ 的因子相消。因节点不同且非零，其部分分式为 $\sum_i c_i/(1-\lambda_i z)$：在 $z=1/\lambda_i$ 处乘以 $1-\lambda_i z$ 后取值，所得系数正是所定义的 $c_i$。所以 $u_n=\Pr(T>n)$。概率属于 $[0,1]$，且 $T\ge q$，给出全部逐项结论。非负整数变量的尾和等于期望，故总和为 $\mathbb ET=\sum_i(1-\lambda_i)^{-1}$。也可从有限个绝对收敛的几何级数求和得到同一值。证毕。

**命题。** 上述族可通过显式递归构造而无需预先给出生存概率表示。空节点族取零序列。若尾节点族的权重为 $w_j$，加入不同的新节点 $a$ 后，令

$$
\widetilde w_j=\frac{(1-a)w_j}{\lambda_j-a},
\qquad w_0=1-\sum_j\widetilde w_j.
$$

所得实际指数和满足

$$
f_0=1,\qquad f_{n+1}=a f_n+(1-a)v_n,
$$

其中 $v$ 是尾节点族的指数和。在全部节点属于 $[0,1]$ 时，该递归给出所有时刻 $f_n\in[0,1]$，以及节点数以内的 $f_n=1$，包括端点节点和空族的相应边界。

**证明。** 常数项由 $w_0$ 的定义得到。展开 $f_{n+1}-a f_n$，首节点项消失，其余每项的 $(\lambda_j-a)$ 消去分母，得到 $(1-a)v_n$。对节点数及时间归纳，递推右侧是两个 $[0,1]$ 值的凸组合；在初始平台内两个值均为一。证毕。

**推论。** 对任意正质量预算 $M$ 和任意有限不同节点族，节点均在 $[0,1]$，存在 $\delta>0$ 以及两组非负权重 $w_i^+,w_i^-$，使

$$
\sum_i(w_i^++w_i^-)\le M,
\qquad 0\le m_n^+-m_n^-\le\delta\quad(n\ge0),
\qquad m_n^+-m_n^-=\delta\quad(n<q),
$$

其中 $m_n^\pm=\sum_iw_i^\pm\lambda_i^n$。

**证明。** 对递归构造的权重 $c_i$，令 $S=\sum_i|c_i|$，取 $\delta=M/(1+S)$，并取 $w_i^+=\delta\max(c_i,0)$、$w_i^-=\delta\max(-c_i,0)$。合并质量为 $\delta S\le M$，矩差为 $\delta u_n$；前一命题覆盖端点和空族。证毕。

这里正性属于两份测度各自；它们之差可以包含精确抵消。上述结论没有对单份正测度声称其自身具有长平台。

## PN.3 一个显式指数质量代价

**定义。** 对 $q\ge2$ 取等距节点

$$
\lambda_i=\frac\kappa4+\frac\kappa4\frac{i}{q-1},
\qquad 0\le i<q.
$$

$q=1$ 时取唯一节点 $\kappa/4$。始终有 $\kappa/4\le\lambda_i\le\kappa/2$。

**命题 PN2。** PN1 中这些节点的系数满足

$$
S_q=\sum_i|c_i|\le B_\kappa^{q-1},\qquad B_\kappa=24/\kappa.
$$

**证明。** $q=1$ 时 $S_1=1$。对 $q\ge2$，令 $r=q-1$，网格间距为 $h=\kappa/(4r)$。每个系数的分子绝对值不超过一，分母绝对值等于 $h^r i!(r-i)!$。因此

$$
S_q\le(4r/\kappa)^r\sum_{i=0}^r\frac1{i!(r-i)!}
=\frac{(8r/\kappa)^r}{r!}.
$$

由 $\log(r!)=\sum_{j=1}^r\log j\ge\int_1^r\log x\,dx\ge r\log r-r$ 得 $r!\ge(r/e)^r$。结合 $e<3$，得到 $S_q\le(24/\kappa)^r$。证毕。

## PN.4 两个一致有界的正自伴随实现

**假设。** 采用 PN.3 的节点，并取

$$
0<\delta S_q\le\kappa^2/64,
\qquad w_i^\pm=\delta\max(\pm c_i,0),
\qquad b_i^\pm=\sqrt{w_i^\pm}.
$$

**定义。** 令

$$
D=\operatorname{diag}(\lambda_i),\qquad
K_\pm=\begin{pmatrix}\kappa/4&(b^\pm)^*\\b^\pm&D\end{pmatrix}.
$$

两个系统具有同一个可见方向、同一个可见即时项和同一个隐藏对角传播。

**定理 PN3。** 有

$$
\frac\kappa8 I\le K_\pm\le\frac{5\kappa}8 I<\kappa I,
$$

以及

$$
m_n^+-m_n^-=\delta u_n,\qquad
\sup_n|m_n^+-m_n^-|\le\delta,
\qquad \sum_{n<q}|m_n^+-m_n^-|=q\delta.
$$

（文献：内部正性作为辨识侧信息，见 M. Khosravi, R. S. Smith, SIAM Journal on Control and Optimization 63(1) (2025), 26–56, doi:10.1137/23M1556095）

**证明。** 去掉交叉块后的对角算子在 $[\kappa/4,\kappa/2]$ 内。交叉块 $\left(\begin{smallmatrix}0&b^*\\b&0\end{smallmatrix}\right)$ 的范数为 $\|b\|\le\sqrt{\delta S_q}\le\kappa/8$；二次型扰动界给出所述上下界。直接计算 $\langle b^\pm,D^nb^\pm\rangle=\sum_iw_i^\pm\lambda_i^n$，再用 PN1。证毕。

**命题 PN4。** 两个可见响应在所有时刻满足

$$
\sup_{n\ge0}|s_n(K_+)-s_n(K_-)|\le\frac\delta{(1-\kappa)^2}.
$$

**证明。** 记 $R_\pm(z)=\sum_ns_n(K_\pm)z^n$、$M_\pm(z)=\sum_nm_n^\pm z^n$。分块消元与相同的即时项给出

$$
R_+(z)-R_-(z)=z^2R_+(z)[M_+(z)-M_-(z)]R_-(z).
$$

因为 $0\le K_\pm\le\kappa I$，有 $s_n(K_\pm)\ge0$ 且 $\sum_ns_n(K_\pm)\le(1-\kappa)^{-1}$。逐系数取绝对值，卷积两侧的绝对和与中间系数的上界 $\delta$ 相乘即得；这覆盖任意自然时刻，非有限截止后的外推。证毕。

## PN.5 排除维数无关的线性恢复率

**定理 PN5。** 令

$$
A_\kappa=\frac{\kappa^2}{128(1-\kappa)^2},
\qquad 0<\epsilon\le A_\kappa,
\qquad q=1+\left\lfloor\frac{\log(A_\kappa/\epsilon)}{\log B_\kappa}\right\rfloor.
$$

则

$$
\boxed{\mathfrak R_\kappa(\epsilon)\ge(1-\kappa)^2q\epsilon.}
$$

特别地，不存在只依赖 $\kappa$ 的有限常数 $C$，使全部维数与全部足够小的误差均满足 $\mathfrak R_\kappa(\epsilon)\le C\epsilon$。

（文献：有界噪声下的最坏情形系统辨识与信息直径方法，见 B. Kacewicz, M. Milanese, International Journal of Adaptive Control and Signal Processing 9 (1995), 87–96, doi:10.1002/acs.4480090109）

**证明。** 取 $\delta=2(1-\kappa)^2\epsilon$。PN2 和 $B_\kappa^{q-1}\le A_\kappa/\epsilon$ 给出 $\delta S_q\le\kappa^2/64$，故 PN3 的两模型合法。PN4 给出全部响应差不超过 $2\epsilon$。同一数据

$$
y_n=\frac{s_n(K_+)+s_n(K_-)}2
$$

与两模型的误差均不超过 $\epsilon$。对任意估计器，令 $L_\pm=\sum_{j<q}|\widehat m_j(y)-m_j^\pm|$。逐项三角不等式给出 $L_++L_-\ge q\delta$，故至少一个损失不小于 $q\delta/2=(1-\kappa)^2q\epsilon$。全部绝对损失不小于这个有限前缀损失。由于 $q\to\infty$ 当 $\epsilon\downarrow0$，线性率被排除。证毕。

此下界在所有响应时刻都被提供时成立。它不依赖缺少足够长的观察时间、接近单位圆的隐藏根、Jordan 块、非正规放大或无界耦合范数。

## PN.6 匹配的有限观察上界

**引理。** 对 $K\in\mathcal C_\kappa$，其记忆满足

$$
0\le m_j\le\frac{\kappa^{j+2}}4.
$$

响应逆级数 $Q(z)=R(z)^{-1}=1-az-z^2M(z)$ 的系数绝对和不超过 $1+\kappa$。

**证明。** $a=s_1$，$\|b\|^2=s_2-s_1^2$。在 $[0,\kappa]$ 上 $x^2\le\kappa x$，谱定理给出 $s_2-a^2\le\kappa a-a^2\le\kappa^2/4$。又 $0\le D\le\kappa I$，得第一式。记忆非负且收敛；在 $z=1$，$1-a-M(1)=1/R(1)$，而 $R(1)\le(1-\kappa)^{-1}$。于是 $a+M(1)\le\kappa$，所以 $\|Q\|_{\ell^1}=1+a+M(1)\le1+\kappa$。证毕。

**定理 PN6。** 对每个整数 $J\ge0$，仅使用 $s_1,\ldots,s_{J+1}$ 的误差不超过 $\epsilon$ 的读数，就存在估计器满足

$$
\boxed{\sup_{K,y}\sum_{j\ge0}|\widehat m_j-m_j(K)|
\le2(1+\kappa)^2J\epsilon+
\frac{\kappa^{J+2}}{4(1-\kappa)}.}
$$

**证明。** 在 $[0,\kappa]$ 上的概率测度中，最小化有限响应矩向量到数据的最大坐标距离。有限矩向量构成紧集：它是紧曲线 $x\mapsto(x,\ldots,x^{J+1})$ 的凸包。因此最小值存在，且真实谱测度保证最小残差不超过 $\epsilon$。由有限维凸包定理，可用至多 $J+2$ 个原子实现同一个拟合向量。乘法算子及常数单位向量给出一个相容的有限维正收缩拟合模型 $\widetilde K$。

真实响应与拟合响应在这 $J+1$ 个时刻的差不超过 $2\epsilon$。有序逆级数恒等式

$$
\widetilde Q-Q=\widetilde Q(R-\widetilde R)Q
$$

与引理的 $\ell^1$ 界，给出前 $J$ 个记忆系数差各不超过 $2(1+\kappa)^2\epsilon$。输出这些拟合记忆系数，并在 $j\ge J$ 输出零。前缀误差按项相加；真实尾部由引理给出的几何和控制。证毕。

这里没有要求被测序列经逐项裁剪后自动具有相容模型，也没有要求对真实隐藏维数预先设上界。此证明给出估计器存在性；没有把有限矩拟合的数值复杂度或有限精度实现作为已经证明的结论。

**推论。** 当 $0<\epsilon<1$，取 $J=\lceil\log(1/\epsilon)/\log(1/\kappa)\rceil$。对固定 $\kappa\in(0,1)$，PN5 与 PN6 合起来给出

$$
\boxed{\mathfrak R_\kappa(\epsilon)
=\Theta_\kappa\bigl(\epsilon\log(1/\epsilon)\bigr)
\quad(\epsilon\downarrow0).}
$$

证明由 $\kappa^J\le\epsilon$ 和 PN5 中 $q$ 的显式定义直接完成。精确首项常数没有在此确定。

## PN.7 同一个平衡分布与固定观察下的可逆马尔可夫实现

**定义。** 对 PN3 的两模型，本节把隐藏坐标重标为 $1,\ldots,q$，可见坐标编号为 $0$。令 $r=3\kappa/4$、$h_0=1$，并对 $1\le i\le q$ 定义

$$
h_i=\frac{\sqrt{\delta|c_i|}}{r-\lambda_i}>0,\qquad
Z_h=\sum_{i=0}^qh_i^2,\qquad \pi_i=h_i^2/Z_h.
$$

对两个模型使用同一个 $h$，并定义

$$
T^\pm_{ij}=K^\pm_{ij}\frac{h_j}{h_i},\qquad
 d_i^\pm=1-\sum_jT^\pm_{ij},\qquad
 Z_d^\pm=\sum_i\pi_i d_i^\pm,\qquad
\alpha_j^\pm=\frac{\pi_jd_j^\pm}{Z_d^\pm}.
$$

在共同状态空间 $\{0,\ldots,q\}\times\{-1,+1\}$ 上令

$$
P_\pm((i,\sigma),(j,\tau))=
\boldsymbol1_{\{\sigma=\tau\}}T^\pm_{ij}
+\frac12d_i^\pm\alpha_j^\pm.
$$

**定理 PN7。** 两个 $P_\pm$ 都是每项严格为正的随机矩阵，具有共同的平稳分布 $\bar\pi(i,\sigma)=\pi_i/2$，且满足细致平衡。作为 $L^2(\bar\pi)$ 上的算子，它们是正算子，常数之外的谱包含于 $[\kappa/8,5\kappa/8]$。同一个中心化单位观察

$$
e(i,\sigma)=\frac{\sigma\boldsymbol1_{\{i=0\}}}{\sqrt{\pi_0}}
$$

满足

$$
\langle e,P_\pm^ne\rangle_{\bar\pi}=s_n(K_\pm),
\qquad \|e\|_\infty\le\sqrt{5/4}.
$$

该观察的目标记忆核也等于 PN3 的 $m_n^\pm$。

**证明。** 对活跃隐藏坐标，$T^\pm$ 的行和为 $\lambda_i+(r-\lambda_i)=r$；对不活跃坐标为 $\lambda_i\le r$。可见行和至多

$$
\kappa/4+\sum_i\frac{w_i^\pm}{r-\lambda_i}
\le\kappa/4+(4/\kappa)(\kappa^2/64)=5\kappa/16<r.
$$

因此所有 $d_i^\pm\ge1-r>0$。$\pi_iT^\pm_{ij}=h_ih_jK^\pm_{ij}/Z_h$ 对 $i,j$ 对称；补充项的平衡流为 $\pi_i d_i^\pm\pi_j d_j^\pm/(4Z_d^\pm)$，也对称。行和为一且补充项严格为正，所以两个链不可约、非周期，并具有所述共同平稳分布。

分解符号偶、奇两个子空间。奇子空间上的传播为 $T^\pm$，在等距坐标 $f\mapsto(h_if_i/\sqrt{Z_h})_i$ 中等于 $K_\pm$。偶子空间的对称坐标矩阵为

$$
J_\pm=K_\pm+
\frac{v_\pm v_\pm^*}{h^*v_\pm},
\qquad v_\pm=(I-K_\pm)h.
$$

分母 $h^*(I-K_\pm)h$ 严格为正，故 $J_\pm\ge K_\pm\ge\kappa I/8$。并且 $J_\pm h=h$。这个秩一正更新至多产生一个超过 $5\kappa/8$ 的特征值：若存在两个，取其张成空间内一个正交于 $v_\pm$ 的非零向量，该向量的 Rayleigh 商既超过 $5\kappa/8$ 又等于 $K_\pm$ 的 Rayleigh 商，矛盾。因特征值一已经存在，其余偶谱都不超过 $5\kappa/8$。奇谱使用 PN3 即得。

观察 $e$ 属于奇子空间；在上述等距坐标中恰为第零个标准基向量，所以全部响应相同。奇偶子空间均约化，可见方向只在奇子空间中，消去偶子空间没有交叉贡献；故目标核仍是 $\langle b^\pm,D^nb^\pm\rangle$。最后

$$
Z_h\le1+(16/\kappa^2)\delta S_q\le5/4,
\qquad \|e\|_\infty=\sqrt{Z_h},
$$

得到统一观察幅度界。证毕。

**推论。** PN5 的下界在正、可逆、具有统一谱隙的有限马尔可夫链类上仍然成立，而且下界中的两模型具有同一状态空间、同一平稳分布及同一固定观察。对其中心化传播使用 PN6，给出同阶上界。

这排除了把恢复障碍完全归因于非自伴随传播或不可逆热力学的解释。它没有证明这些链属于 AT.10 的单参数素数热浴子族，也没有证明下界对完整观察历史或可干预观察接口继续成立。

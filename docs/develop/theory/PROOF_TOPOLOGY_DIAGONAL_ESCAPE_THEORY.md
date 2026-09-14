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

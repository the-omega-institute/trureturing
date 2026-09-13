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

# 补编 RD：整数显示、实际黄金纤维与原始状态

本补编将本卷的读数核与目标充分性具体应用到 #6881 的现役数位对象。普通整数本身没有由显示之外自动指定的隐藏坐标。这里的原对象是已有的非负有限数位表，显示是对该表的整数求值；黄金求值保留的内容必须由实际定义及其运算对应来确定。不存在从一个标量名字自动恢复其任意来源的断言。

## RD.1 三个实际对象及其可交换求值

令 $F_0=0,F_1=1,F_{i+2}=F_{i+1}+F_i$，并取现役载体

$$
\mathcal R=\mathbb N^{(\mathbb N)},\qquad
v(r)=\sum_i r_iF_{i+2},\qquad
\beta(r)=\sum_i r_i\varphi^{i+2}\in\mathbb Z[\varphi],
\quad \varphi^2=\varphi+1.
$$

它们分别是 `RawDigits`、`rawValue` 与 `betaDigits`，不是本补编另造的模型。`DoubleFaceLength.betaDigits_b` 已证明

$$
\pi(\beta(r))=v(r),\qquad \pi(a+b\varphi)=b.
$$

因此原始数位表、黄金环元素及显示整数是三个不同的数学对象。原始表的规范性为系数至多一且没有相邻两个一，即现役 `CanonicalRaw`。已知表是规范的时，现役 Zeckendorf 唯一性由显示恢复该表；没有规范性前提时，不能默认选定规范代表就是原输入。

若目标只是普通整数命题 $P(v(r))$，它在每个 $v$ 纤维上自动恒定。若所问性质在同值纤维内改变，它就不是仅关于该整数的性质，而是关于构造或更细语义对象的性质。这一区别先于任何编码选择。

## RD.2 定理：非负原始数位的完整黄金像

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

取 $r=u\delta_0+w\delta_1$ 即为实际原始数位见证。两个系数由 $u=2a-b,w=b-a$ 唯一决定；唯一的是这个两槽代表，并非所有原始表示。证毕。

**推论 RD2。** 对每个 $n\in\mathbb N$，实际可实现的黄金纤维为

$$
\{\beta(r):v(r)=n\}
=\{a+n\varphi:a\in\mathbb Z,\ a\le n\le2a\}.
$$

等价地，$a$ 从 $\lceil n/2\rceil$ 到 $n$ 取每个整数。相应黄金像的数量为 $\lfloor n/2\rfloor+1$，但该数不计原始表达式、规范化路径或历史。正文中的区间分类由 `RealizableFiber.raw_image_iff` 与 `display_fiber_iff` 承载；计数是这个整数区间的算术推论，不另立有限正例模块。

## RD.3 定理：显示对的可实现条件与全部移位观察

使用现役 `shiftDigits`，将每个槽号提高 $k$，并定义

$$
v_k(r)=v(\operatorname{shiftDigits}(k,r)).
$$

这里先作用于实际输入，再求值；不是先规范化，再从显示重新构造输入。有限求和换元与幂法则给出

$$
\beta(\operatorname{shiftDigits}(k,r))=\varphi^k\beta(r),
\qquad v_k(r)=\pi(\varphi^k\beta(r)).
$$

**定理 RD3。** 对任意 $n,m\in\mathbb N$，

$$
\exists r:\ v(r)=n\ \land\ v_1(r)=m
\quad\Longleftrightarrow\quad
3n\le2m\ \land\ m\le2n.
$$

而每个这样的输入满足

$$
\beta(r)=(m-n)+n\varphi.
$$

**证明。** 写 $\beta(r)=a+n\varphi$，乘以 $\varphi$ 后读数为 $m=a+n$。RD1 的 $a\le n\le2a$ 恰转成所列两项不等式。反向取 $a=m-n$，由两项不等式及 RD1 构造原始输入。证毕。

特别地，显示 $n\ge2$ 时，$m=2n$ 与 $m=2n-1$ 都可实现；两者来自不同黄金像。因此单个显示在此域上足以确定黄金像，当且仅当 $n\le1$。若额外假设原输入规范，则规范唯一性另外给出所有 $n$ 的单值性；两项结论的前提不同。

**定理 RD4。** 对原始输入 $r,s$，

$$
\beta(r)=\beta(s)
\iff (v(r),v_1(r))=(v(s),v_1(s))
\iff \forall k\in\mathbb N,\ v_k(r)=v_k(s).
$$

并有实际读数递推

$$
v_{k+2}(r)=v_{k+1}(r)+v_k(r).
$$

**证明。** 相同黄金元素乘以每个 $\varphi^k$ 后相同；反向只取第零与第一读数，使用 RD3 的恢复式。递推由 $\varphi^{k+2}=\varphi^{k+1}+\varphi^k$ 乘以 $\beta(r)$ 后取第二坐标得到。证毕。

对应源码为 `ShiftReadout.display_pair_iff`、`reconstruct_beta`、`beta_eq_iff_all_shifts`、`shiftedValue_recurrence` 与 `display_determines_beta_iff`。这组结果确定的是此实际观察族的核，而不是断言所有数学观察都由两个整数决定。

## RD.4 定理：规范化实际丢弃的坐标及其精确谱

令 $\nu(r)=\operatorname{normalize}(r)$，并令 $c(r)=\operatorname{carrySignedCount}(r)$。后者是现役进位过程的整数电荷；它不是任意添加的标签。现役 `ChargedCarryPath.charged_normalize_exists` 与 `betaDigits_sub_chargedReduces` 给出

$$
\beta(r)-\beta(\nu(r))=c(r)\in\mathbb Z\subset\mathbb Z[\varphi].
$$

规范唯一性又给出 $\beta(\nu(r))=\operatorname{betaGolden}(v(r))$。写

$$
a_0(n)=(\operatorname{betaGolden}(n)).a,
$$

即得到 $\beta(r).a=a_0(v(r))+c(r)$。

**定理 RD5。** 对每个显示 $n$，实际可能的规范化电荷恰为

$$
\{c(r):v(r)=n\}
=\{c\in\mathbb Z:a_0(n)+c\le n\le2(a_0(n)+c)\}.
$$

并且

$$
\beta(r)=\beta(s)
\iff v(r)=v(s)\ \land\ c(r)=c(s).
$$

**证明。** 将电荷坐标式代入 RD2 得到必要性。反向，对每个满足区间条件的 $a=a_0(n)+c$，RD2 给出一个实际输入；其进位电荷由已有路径恒等式强制等于 $c$。最后的等价由两个黄金坐标的相等及电荷坐标式直接推出。证毕。

**定理 RD6。** 规范化前后的全部实际移位读数之差为

$$
\boxed{v_k(r)-v_k(\nu(r))=F_k\,c(r).}
$$

这里两边在 $\mathbb Z$ 中比较。因而规范化保留所有移位读数，当且仅当 $c(r)=0$。

**证明。** 将规范化电荷恒等式乘以 $\varphi^k$ 后取第二坐标，使用现役 `(phi^k).b=F_k`。必要性取 $k=1$；充分性代入零电荷。证毕。

源码为 `NormalizationResidual.charge_spectrum_iff`、`beta_eq_iff_value_charge`、`normalization_shift_defect` 与 `normalization_preserves_all_shifts_iff`。这里推导的是现有电荷的完整取值谱及其观察意义，没有重新宣称发现已证明的路径电荷不变量。

## RD.5 后续推论：完整黄金恢复仍不能判断一个原始定理性质

**定理 RD7。** 对每个 $i\in\mathbb N$，存在两个实际原始数位表 $r,s$，其所有移位整数读数相同，但一个规范、另一个非规范并可执行一次实际进位。

**证明。** 取

$$
r=\delta_{i+2},\qquad s=\delta_i+\delta_{i+1}.
$$

现役 `ChargedCarryStep.adjacent` 给出 $s\to r$ 的零电荷进位。其已有黄金差恒等式推出 $\beta(r)=\beta(s)$，由 RD4 得到全部移位读数相同。单个系数一的表满足 `CanonicalRaw`；$s$ 在相邻位置同时为一，违反该谓词。证毕。

因此不存在任何谓词 $H:(\mathbb N\to\mathbb N)\to\mathrm{Prop}$ 满足

$$
\forall r,\quad\operatorname{CanonicalRaw}(r)
\iff H((v_k(r))_{k\ge0}).
$$

若存在，RD7 中相同的整段观察会被 $H$ 赋予相同真假，和原始规范性不同矛盾。对应 `all_shifts_hide_carry_applicability` 与 `no_shift_only_canonicality_test`。这不是算法运行时间下界，而是不存在这种仅由所给数据决定的函数。

这证明了严格的目标区别。黄金求值足以回答所有移位求值问题；它不足以回答一个已有、明确的原始对象性质 `CanonicalRaw`，也不能以自身作为已经完整保留全部进位适用条件的证明。零电荷不等于原始表没有发生变化；相同的全部读数更不等于表达式或历史相同。

## RD.6 具体研究用途与尚待闭合的问题

本补编回答的是一个已经具体化的识别问题：给定 `rawValue` 的整数显示，哪些实际黄金语义状态可能产生它；哪些额外读数恰好补齐黄金语义；哪些原始性质仍然不能从该语义恢复。第一项的完整像、第二项的充要条件及第三项的全称反例族均有以上普通证明与对应 Lean 源。

外部研究目标采用现有 `Problems/random-zeckendorf-game-gaussianity.md` 登记的随机 Zeckendorf 游戏长度与混合问题。Cheigh 等的 *Towards the Gaussianity of Random Zeckendorf Games* 研究两种路径分布，并得到若干分块上的高斯极限，而不是在摘要中宣称已经解决全部游戏空间的问题。其预印本为 arXiv:2210.11038，正式章节 DOI 为 10.1007/978-3-031-65064-2_4（2025）。本补编不证明该高斯猜想，也不把当前 `CarryStep` 不经比较便认定为论文的完整游戏规则。

RD7 对这个方向给出一个必要的方法边界：仅由数值及黄金电荷得到的摘要甚至不能判断是否已经规范，因而不能直接充当已经保留终止事件、合法动作或局部均匀动作概率的完整随机状态。下一项承重问题是，在固定的真实游戏关系及其路径测度中，证明某个包含局部进位适用条件的观察商保持终止和目标条件分布；然后才研究混合或再生。构造该商不能仅提出字段，必须给出保持条件的定理，或具体证明某些候选仍然丢失目标相关区别。

对当前原始数位关系，更近的数学目标是精确分类：哪些附加的有限局部读数，能在指定子域上把 RD7 的规范性及一步动作歧义消去，同时保留对下一步的闭合性。补充一个点值规范性位只能解决当前规范性，不能据此声称整个下一步结构也恢复；后者仍需单独证明。

参考与复用边界：

- 当前整数求值、黄金环、数位移位、规范唯一性及带电进位路径均使用既有真实对象，不引入平行状态机。
- 当前 dev 的 `LowCutoffObservationFibres` 提供相邻领域的同类证明范式：在实际观察公式中刻画完整纤维，再检查目标是否恒定。本补编没有把其流体模型或连续稳定性断言运输到数位模型。
- Schaeffer、Shallit、Zorcic，*Beatty Sequences for a Quadratic Irrational: Decidability and Applications*，arXiv:2402.08331v3（2026），提供指定二次无理数的 Beatty/Ostrowski 表示背景。本文的全原始输入像分类不以该文的自动机可判定性为前提，也不宣称普通整数算术因为改写坐标而获得新的逻辑真值。
- 基础取整、Fibonacci 恒等式和有限支撑求值属于既有数学。这里的形式化贡献限定为现役载体的完整像、实际显示对及规范化电荷的精确对应，以及完整移位观察仍遗忘规范性的明确障碍；没有主张文献首次性或把随机游戏开放目标记为已解决。

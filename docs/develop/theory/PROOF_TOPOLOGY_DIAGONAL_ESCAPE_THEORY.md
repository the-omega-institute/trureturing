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

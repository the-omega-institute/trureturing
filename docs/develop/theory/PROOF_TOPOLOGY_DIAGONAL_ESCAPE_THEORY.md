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

---

# 补编 PT：整路径概率、观察闭合与可逆投影记忆

## PT.1 物理路径与数学历史的共同问题

本补编沿用 #6881 的共同见证原则：逐条可实现的观察边，不自动组成同一隐藏对象的完整历史。引入随机演化后，还必须区分三个层次：路径是否有共同合法实现、路径集合上采用什么概率、参数是否为实际演化时间。只给出合法路径的集合，不决定路径的相对频率；只匹配单帧边缘分布，也不决定时间相关或首次到达分布。

设完整状态为 $x\in X$，观察为 $q:X\to Y$，真实一步律为 $K:X\to\operatorname{PMF}(X)$。给定初始律 $\mu$，有限路径律是

$$
\mathbb P_K(x_0,\ldots,x_n)=\mu(x_0)\prod_{j=0}^{n-1}K(x_j)(x_{j+1}).
$$

每个中间 $x_j$ 同时出现在前后两个因子中。不能分别在每条观察边上重选互不相容的隐藏见证。若事件 $E$ 只依赖观察路径且概率非零，端点约束下的路径律由 $\mathbb P_K(E\cap\cdot)/\mathbb P_K(E)$ 定义；这不是所有满足端点条件的路径上的均匀分布。

物理来源的启发必须按其实际范围使用。Seong 等的 TPS-DPS [P1] 明确将 Langevin 转移路径作为路径测度处理，并使用包含位置与速度的状态；其离散训练表示不等于已经对所有连续插值给出物理保证。PLaTITO [P2] 学习给定物理间隔的粗粒度转移密度，其生成流时间与物理时间不同，作者明确没有声明无偏动力学、详细平衡或 Chapman–Kolmogorov 一致性的形式保证。DeepPath [P3] 的主动学习使用分子力学能量极小化预言机改善中间结构；低能路径与带正确时钟的路径律仍是不同目标。

具体名称 TPD 和 TDEG 的公司公告 [P6] 宣称整路径生成与快慢运动分离，但本补编没有据此认定其速度数字、完整方法或动力学保证。以下定理只依赖明示的数学对象，不依赖这些宣传性结论。把整个有限路径作为输出，既可用于生成模型，也可用于确定性或概率证明见证；输出方式本身不会证明正确性。

## PT.2 已有全部移位读数仍不能闭合实际进位

沿用补编 RD 的原始对象 $r\in\mathrm{RawDigits}$、求值 $\beta(r)$、移位读数 $v_j(r)$、真实规范化电荷 $c(r)$，这次将操作固定为已有确定性 $T=\mathrm{carryPass}$。

**定理 PT1（增强观察的真实后继障碍）。** 对每个 $k\ge0$，存在两个非规范原始对象 $r_k,s_k$，满足

$$
v_0(r_k)=v_0(s_k)=6+8k,\qquad
\beta(r_k)=\beta(s_k),\qquad
\forall j\ge0,\ v_j(r_k)=v_j(s_k),\qquad c(r_k)=c(s_k),
$$

且两边都执行合法的原始进位，但

$$
\beta(Tr_k)+1=\beta(Ts_k).
$$

**证明。** 用 $\delta_i$ 表示第 $i$ 个原始槽的单个数位，取

$$
r_k=2\delta_0+2\delta_1+k\delta_4,\qquad
s_k=2\delta_2+k\delta_4.
$$

两者的黄金值均为 $(4+5k)+(6+8k)\varphi$，由 RD 的已证核等价得到全部移位读数和总电荷相同。两者均有重数二的槽，所以都不是规范对象。已有确定性规则先处理最低重复槽；因此

$$
Tr_k=3\delta_1+k\delta_4,\qquad
Ts_k=\delta_0+\delta_3+k\delta_4.
$$

因为 $\varphi^2+\varphi^5-3\varphi^3=1$，结论成立。两次更新均是已有 `CarryStep` 的实际构造子。证毕。

对应源码 `CarryStepClosure.actual_carry_closure_failure` 及 `no_shift_and_canonicality_next_map`。后者严格排除一个从“整个移位读数序列与当前规范性布尔值”恢复下一黄金值的函数。这里的全部移位探针不是全部实际进位历史；不能混换两种演化。定理也不排除保留更多局部数据后实现闭合。

这比仅证明当前规范性不可恢复更强：即使把该谓词的真值额外告诉观察者，两边也同为 false，实际下一步仍不同。因而一个充分描述某族数值运算的商，不自动充分描述另一个真实操作。这是数学状态与具体动力学必须一起确定的例子。

## PT.3 强可合并性将一步律提升为整条路径律

已有 `StrongLumpabilityDescent.strong_lumpability_descent_tfae` 说明：在实际观察像上存在一步核 $L$，满足

$$
q_\#K(x)=L(q(x)),
$$

当且仅当 $q_\#K(x)$ 在每个 $q$-纤维上恒定。这是对全部隐藏初态的要求；固定一个初始分布时的弱性质不能替代它。

**定理 PT2（整路径下降）。** 若上述逐点一步恒等式成立，则对任意 $n$ 和任意初始分布，

$$
(q^{n+1})_\#\mathbb P_K=\mathbb P_L.
$$

因此每个观察路径统计量 $F:Y^{n+1}\to Z$ 的分布也相同，包括有限时间内是否经过指定中间区域、端点对以及有限路径费用。

**证明。** 长度零的路径只含初态，结论为点质量的推前恒等式。假设长度 $n$ 已成立。长度 $n+1$ 的路径先按 $K(x)$ 选一个共同后继 $y$，再生成从 $y$ 出发的长度 $n$ 后段，最后在前面接上 $x$。归纳假设将后段的整体推前换成 $L$ 的后段；一步恒等式将 $q(y)$ 的分布换成 $L(q(x))$。这正是商路径的递归定义。最后对初态混合，并对 $F$ 再推前。证毕。

对应 `WholePathDescent.whole_path_descent`、`initial_distribution_path_descent`、`path_statistic_descent`。源码是离散 PMF 的完整联合分布定理，不是连续蛋白 SDE 的认证，也没有对任何神经生成器宣称它已满足前提。端点条件化的推前结论需要另外履行正概率条件，连续精确端点则需正则条件分布等工具。

当强可合并性失败，设实际观察历史为 $h=(y_0,\ldots,y_t)$，则下一观察分布为

$$
\sum_{x\in q^{-1}(y_t)}\nu_h(x)\,q_\#K(x),
\qquad
\nu_h=\operatorname{Law}(X_t\mid Y_{0:t}=h).
$$

这是在该历史概率非零时对隐藏当前状态作全概率分解。历史可通过 $\nu_h$ 改变未来，即使当前 $y_t$ 相同。它把 #6881 的相容隐藏状态集合升级为带权相容对象；集合只决定支持，不决定权重。学习一个 $L(y,\cdot)$ 总能定义自己的马尔可夫模拟器，但不能据此证明它是原系统的精确观察律。

## PT.4 Koopman 观察闭合与两步记忆的精确关系

令 $K$ 为有限维实观察函数空间上的一步转移算子，$P$ 为投影，记 $Q=I-P$。这里 $K$ 作用于函数：$(Kf)(x)$ 是从 $x$ 出发的下一步 $f$ 的条件期望。若 $P$ 来自状态观察 $q$，它应是对所有 $q$-可测函数的条件期望，而不是任意选出的几个慢特征函数。

定义

$$
\overline K=PKP,\qquad
\Delta_2=PK^2P-\overline K^2,\qquad
B=QKP.
$$

**定理 PT3（隐藏往返恒等式）。** 仅要求 $P^2=P$，就有

$$
\boxed{\Delta_2=PKQKP.}
$$

**证明。** $\overline K^2=PKP^2KP=PKPKP$，在 $K^2$ 的两个 $K$ 之间插入 $P+Q=I$ 后相减。证毕。

**定理 PT4（可逆情形的 Gram 判据）。** 若进一步 $P^*=P$、$K^*=K$，则

$$
\boxed{\Delta_2=B^*B.}
$$

所以

$$
\boxed{\Delta_2=0\iff QKP=0\iff KP=PKP.}
$$

**证明。** $B^*=PKQ$，且 $Q^2=Q$，因此 $B^*B=PKQ^2KP=PKQKP$。实矩阵 Gram 为零当且仅当原矩阵为零，再展开 $QKP=KP-PKP$。证毕。

**定理 PT5（两步精确性与全部正整数时间）。** 在 PT4 的条件下，

$$
\Delta_2=0
\iff
\forall m\ge1,\quad PK^mP=(PKP)^m.
$$

**证明。** 由 $KP=PKP$ 对 $m$ 归纳：将最后一个 $KP$ 替换成 $PKP$，再用归纳假设。反向取 $m=2$。只声明正次幂，因为投影空间的恒等算子是 $P$，不是环境空间的 $I$。证毕。

这些结论由 `ReversibleProjectionMemory` 承载，复用 mathlib 的 `Matrix.conjTranspose_mul_self_eq_zero`，不复述 Gram 零判据的证明。一般非均匀可逆链需先运输到 $L^2(\pi)$ 的正交坐标；本源码并未完成这个额外字典。

自伴条件不能删除。例如 $P=\operatorname{diag}(1,0)$、$K=\begin{pmatrix}0&0\\1&0\end{pmatrix}$ 时，$K^2=0$、$PKP=0$，因此 $\Delta_2=0$，但 $QKP=K\ne0$。该普通代数反例只说明一般算子情形的限制，不是随机转移矩阵的例子。

比较的必须是真实 $PK^2P$ 与真实一步压缩的平方。任取一个学到的矩阵 $\widehat K$ 再计算其自身幂，本来就满足自己的半群规则；这不认证它等于物理系统的观察转移。投影产生记忆是 Mori–Zwanzig 的经典机制 [P4,P5]；本节的贡献定位是精确有限矩阵承载及其与 #6881 观察商边界的连接，不主张该机制首次发现。

## PT.5 同一个平衡图景不决定路径速率

**定理 PT6（可逆三态族）。** 对 $a,b\ge0$、$a+b\le1$，取

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

则 $K_{a,b}$ 非负、行和为一、对称，并对全部参数共享平衡分布 $(1/3,1/3,1/3)$。$P$ 是合并前两个状态的实际平衡条件期望。直接乘法得到

$$
\Delta_2=\frac{b^2}{8}
\begin{pmatrix}1&1&-2\\1&1&-2\\-2&-2&4\end{pmatrix}.
$$

因此在零起始索引下 $\Delta_2(2,2)=b^2/2$，且观察空间闭合当且仅当 $b=0$。对应 `stochastic_and_stationary`、`exact_memory_entry` 和 `closed_iff_cross_edge_zero`；源码公开承载所需矩阵项与零缺陷等价，完整显示矩阵是同一次展开的普通数学表达。

固定 $a=1/4$，分别取 $b=1/4$、$1/2$，两个有效可逆链的整个平衡向量完全相同，但 $K(1,2)$ 不同。故不存在仅从平衡向量恢复该转移项的函数；源码为 `no_equilibrium_only_transition_decoder`。证毕。

这里揭示的是平衡信息与动力信息的不同：统一的能量或平衡分布不决定转移频率。不是说指定力场、质量、摩擦、温度、噪声及时间步长也无从定义动力学；后者已经给了更多信息。

当 $b$ 很小而 $a$ 保持非零，模型有快速内部交换与缓慢跨组交换，但缺陷仍不为零，只是该矩阵项准确按 $b^2/2$ 缩小。快慢分解因而是近似闭合的候选，不是精确闭合的自动证明。单个两步误差小，也不能不经长时间估计就保证罕见转移的平均首次到达时间正确。

## PT.6 对物理预言机与主动观察的数学含义

低能、无原子重叠、端点匹配、时间连续以及正确路径律是不同约束。连续低能曲线经过重新参数化仍是同一几何曲线，却可有不同速度。力场预言机返回的是某项明确的能量、力或动力学计算，不能被当作无条件真值预言机。

对项目中的实际原始进位，PT1 说明只加一个当前规范性标志仍不足。对可逆概率模型，PT4 说明遗漏的动力信息由 $QKP$ 精确刻画。两者共同提出一个目标相关的补充观察原则：新增观察应消除对真实下一步或路径统计量仍有影响的纤维差异，而不只是改善当前构型重建。

这不是一个已经实现或已证最优的主动学习算法。可检验的数学目标是：给定新增观察 $r$，证明联合观察 $(q,r)$ 的逐点推前律在纤维上恒定，或在明确范数及时间范围内给出其不恒定的上界。若不能闭合，则须保留相应记忆或增加状态，而不能将隐藏纤维在每步重新初始化。

## PT.7 后续承重问题与适用范围

本补编没有构造连续蛋白路径生成器、没有证明神经模型的物理正确性，也没有解决随机 Zeckendorf 游戏的高斯极限。当前闭合的普通数学链条是：真实进位反例、一步核条件到整路径分布、可逆投影的 Gram 缺陷、同平衡不同动力的显式族；相应 Lean/Scribe 是这些陈述的源码承载，形式认证仍以实际内核报告为准。

下一项具体问题有两个互相联系的方向。第一，在已登记的随机 Zeckendorf 游戏问题 [P7] 中，先固定与文献一致的合法动作及路径测度，找出保留动作适用条件和整路径目标统计的观察商。PT1 排除了“全部移位读数加当前规范性”这个候选；它并不把现行确定性 `carryPass` 自动等同于论文的随机规则。第二，将 PT4 的精确零缺陷判据推进到定量误差：在明确谱隙、记忆衰减及目标事件概率条件下，从有限滞后缺陷约束长时间路径统计。仅用平衡分布或只对模型自身检查半群关系不足以完成任何一个方向。

## PT.8 文献与来源

[P1] K. Seong et al. *Transition Path Sampling with Improved Off-Policy Training of Diffusion Path Samplers*. ICLR 2025; arXiv:2405.19961v5, 25 January 2025. https://arxiv.org/html/2405.19961v5 。用于区分完整相空间状态、连续路径测度与离散训练路径，不与另名 TPD 混同。

[P2] P. Antoniadis, B. Pavesi, S. Olsson, O. Winther. *Protein Language Model Embeddings Improve Generalization of Implicit Transfer Operators*. arXiv:2602.11216v2, 29 May 2026. https://arxiv.org/html/2602.11216v2 。第4.1节区分物理间隔与生成流时间；第6节明确列出粗粒度和半群一致性等限制。

[P3] Y. T. Pang, L. Yang, K. M. Kuo, J. C. Gumbart. *DeepPath: overcoming data scarcity for protein transition pathway prediction using physics-based deep learning*. Chemical Science 17 (2026), 12055–12073; first published 5 May 2026, received 25 October 2025. DOI:10.1039/D5SC08253F. https://doi.org/10.1039/D5SC08253F 。主动学习的分子力学极小化预言机和低能路径是本文采用的来源范围，不据此认定真实路径频率。

[P4] Y. T. Lin, Y. Tian, M. Anghel, D. Livescu. *Data-driven learning for the Mori-Zwanzig formalism: a generalization of the Koopman learning framework*. arXiv:2101.05873 (2021). https://arxiv.org/abs/2101.05873 。投影记忆与 Koopman 学习的既有研究背景。

[P5] F. Wang, P. Benner, J. Heiland. *Partial Observation of Linear Systems with the Mori-Zwanzig Formalism*. arXiv:2606.23341v1, 22 June 2026. https://arxiv.org/html/2606.23341v1 。对部分观察线性系统的 Markov、噪声、记忆项进行显式分解；本补编不把线性有限维结论冒充一般蛋白非线性闭合。

[P6] FLock.io company announcement, retrieved 13 September 2026. https://cn.linkedin.com/company/flock-io 。公告列出 *Transition Path Diffusion for Protein Reactive Trajectories* 和 *Timescale-Disentangled Generative Models of Protein Dynamics*；本补编没有获得对应完整方法文本，不采用其百万倍加速等数字作为数学前提或已核验实验结论。

[P7] C. Cheigh et al. *Towards the Gaussianity of Random Zeckendorf Games*. arXiv:2210.11038; DOI:10.1007/978-3-031-65064-2_4. https://arxiv.org/abs/2210.11038 。仓内已登记目标为 `Problems/random-zeckendorf-game-gaussianity.md`；精确随机规则、测度和统一混合界均不能被确定性规范化的已证内容替代。

---

# 补编 MF：隐藏初态、历史反馈与反事实的区别

## MF.1 固定实际轨迹，不把其他可能世界当作驱动力

在一个已指定的线性状态空间中固定实际轨迹 $x_{n+1}=Tx_n$，令 $P^2=P$，$Q=I-P$。则 $x_n=Px_n+Qx_n$。两项都是同一个实际状态的分量；$Qx_n$ 不是“所有非此实际状态”的集合，也不是已经发生过的完整历史。逻辑补集 $X\setminus\{x_n\}$、观察纤维 $\{z:Pz=Px_n\}=x_n+\ker P$、隐藏分量 $Qx_n$ 属于不同数学对象。

投影的补 $Q$ 满足 $Q^2=Q$，而不是一般意义的双重否定 $Q^2=I$。在线性实空间里，若需要保留可见部分、翻转隐藏方向的真正对合，可以取 $S=2P-I$。展开得到 $S^2=I$、$PS=P$、$QS=-Q$，并有

$$
PT^n x-PT^n Sx=2PT^n Qx.
$$

这是比较两个初态的反事实响应，不是说未实现的 $Sx$ 对实际 $x$ 施加了作用。在约束状态域中还须检查 $Sx$ 可容许；本补编使用的三态概率模型里 $S$ 恰好交换前两个坐标，因此保存非负性与总质量。上述对合代数是定义展开的普通推导，不另立通用 Lean 包装定理。

Mori–Zwanzig 中 $P$ 常作用于观察函数，而非直接作用于物理状态；将其与下面的状态坐标块模型连接，需要指定坐标观察或相应线性表示。本补编不把观察函数向量、概率分布向量与单个物理微观状态无条件混同。[MF1, MF2]

## MF.2 精确消元：初始隐藏影响与记忆核是两项

令可见变量为 $y_n\in V$，隐藏变量为 $h_n\in H$，实际一步更新为

$$
y_{n+1}=Ay_n+Bh_n,\qquad h_{n+1}=Cy_n+Dh_n.
$$

这里 $A:V\to V$、$B:H\to V$、$C:V\to H$、$D:H\to H$ 都是线性映射。对于由投影给出的直接分解，它们是 $PTP$、$PTQ$、$QTP$、$QTQ$ 在对应子空间的限制。不给每一步重新选择隐藏代表。

**定理 MF1（全时间离散记忆消元）。** 对全部初态与 $n\ge0$，

$$
h_n=D^nh_0+\sum_{i=0}^{n-1}D^{n-1-i}Cy_i,
$$

因此

$$
\boxed{y_{n+1}=Ay_n+BD^nh_0+\sum_{i=0}^{n-1}BD^{n-1-i}Cy_i.}
$$

**证明。** $n=0$ 的和为空。将 $h_n$ 的表达式代入 $h_{n+1}=Cy_n+Dh_n$，把每个幂次增加一，再将 $Cy_n$ 加入求和末项，得到 $n+1$ 的表达式。线性映射 $B$ 分配到有限和后，代入可见更新即可。证毕。

源码 `DiscreteMemoryElimination.exact_memory_equation` 在实际递归定义的 `evolve` 上给出这个结论，量词覆盖任意环上的两个模，不要求有限维、随机性或可逆性。它的两项不能合并命名为“想象”：

$$
\eta_n=BD^nh_0,\qquad M_j=BD^jC.
$$

$\eta_n$ 是初始隐藏条件的影响。固定 $h_0$ 后，它完全确定；只有另行引入初始分布时才成为随机量。$M_j$ 是与初态无关的反馈算子，记录可见量经 $C$ 进入隐藏通道、在其中传播 $j$ 次、再经 $B$ 返回的效果。卷积和才是以历史可见值表达的记忆项。连续时间对应的 $Be^{tD}h_0$ 与 $Be^{tD}C$ 见 [MF1]；本次 Lean 源不声称已经证明连续时间半群或非线性 Mori–Zwanzig 定理。

## MF.3 记忆并非全部隐藏方向：与既有 eventualKernel 的连接

dev 的 `ZeroMemoryCriterion` 已定义 $\mathcal N_\infty(C,T)=\bigcap_{n\ge0}\ker(CT^n)$，以及当前核对全未来核的记忆商。本补编复用该真源。

**定理 MF2（隐藏通道的准确静默子空间）。** 在 MF1 的实际耦合系统中，从 $(0,h)$ 出发的全部可见量恒为零，当且仅当

$$
\boxed{h\in\mathcal N_H:=\bigcap_{n\ge0}\ker(BD^n).}
$$

**证明。** 若可见量一直为零，则隐藏更新退化为 $h_n=D^nh$；下一步可见量为零给出 $BD^nh=0$。反之，若全部 $BD^nh=0$，归纳可得实际耦合轨迹正是 $(0,D^nh)$。证毕。源码为 `zero_visible_iff_eventual_kernel`，结论直接使用已有的 `eventualKernel B D`。

线性相减后，具有相同初始可见量的两个状态 $(y,h)$、$(y,h')$ 给出相同全部可见未来，当且仅当 $h-h'\in\mathcal N_H$。因此目标相关的隐藏信息是 $H/\mathcal N_H$，而不是整个 $H$。通过 $\ker P\simeq H$ 的直接分解，该商与已有 `memoryQuotient P T` 对应；没有新建另一个同名记忆本体。已有人可见/不可见维数公式仍由 `MemoryDimensionFormula` 承担。

进一步，全部反馈核为零等价于 $\operatorname{range}C\subseteq\mathcal N_H$。这个条件只控制由可见历史注入的隐藏方向，未必覆盖全部隐藏初态。例如

$$
y_{n+1}=y_n+h_n,\qquad h_{n+1}=h_n
$$

具有 $A=B=D=1,C=0$，所以 $M_j=0$ 对所有 $j$ 成立，但 $y_n=y_0+nh_0$，只知道 $y_0$ 仍无法确定未来。相反，$B=0$ 时，无论隐藏状态自身怎样运动，都没有任何返回可见层面的影响。

所以“反馈核为零”“当前读数对任意初态充分”“隐藏变量不存在”是三个不同命题。前一补编的自伴 Gram 定理使用额外的 $B=C^*$ 关系来排除相应的不对称情形，不能丢掉这个条件。

## MF.4 同一三态模型的全部记忆系数

继续使用 PT.5 的 $K_{a,b}$ 与合并前两态的 $P$，令 $Q=I-P$。在其实际隐藏方向 $(1,-1,0)$ 上，

$$
\lambda=1-2a-b/2,\quad D=QK_{a,b}Q,\quad C=QK_{a,b}P,\quad B=PK_{a,b}Q.
$$

这里 $\lambda$ 是隐藏块上的传播因子，不能称为完整 $K_{a,b}$ 的特征值。

**定理 MF3（实际三态模型的全滞后核）。** 对所有实参数和自然数 $j$，

$$
\boxed{M_j=BD^jC=\lambda^j\Delta_2,\qquad
\Delta_2=PK_{a,b}^2P-(PK_{a,b}P)^2.}
$$

**证明。** 在给定三态矩阵上直接算出 $DC=\lambda C$；归纳给出 $D^jC=\lambda^jC$。由 $Q^2=Q$，$BC=PK_{a,b}QK_{a,b}P=\Delta_2$，其中末式复用原有缺陷定理。证毕。源码为 `ThreeStateMemoryKernel.feedback_geometric`。

沿用既有 `exact_memory_entry`，可读取

$$
(M_j)_{22}=\frac{b^2}{2}\lambda^j.
$$

对有效随机参数 $a\ge0,b>0,a+b\le1$，有 $-1<\lambda<1$：上界来自 $b>0$，下界由 $a\le1-b$ 得到 $\lambda\ge-1+3b/2$。因此若 $\lambda\ne0$，每个滞后都有非零系数，但其幅度衰减；若 $\lambda=0$，只有 $j=0$ 项保留；若 $b=0$，全部反馈为零，即便隐藏块没有衰减。由绝对收敛几何级数，对 $m\ge0$ 得到该矩阵项的精确尾质量

$$
\sum_{j=m}^{\infty}|(M_j)_{22}|=
\frac{b^2|\lambda|^m}{2(1-|\lambda|)}.
$$

此尾质量是指定核矩阵项的和，不是全路径总变差距离、首次到达时间误差或任何神经模型的泛化界。将它用于长时间目标，还需控制输入序列、迭代放大与相应事件灵敏度。

## MF.5 记忆核无限长，不意味着最小状态无限大

将实际向量写成

$$
x_n=(s_n+h_n,s_n-h_n,r_n),\qquad y_n=(s_n,r_n).
$$

展开同一个 $K_{a,b}$ 得到

$$
y_{n+1}=A_vy_n+B_vh_n,\qquad h_{n+1}=C_vy_n+\lambda h_n,
$$

其中

$$
A_v=\begin{pmatrix}1-b/2&b/2\\b&1-b\end{pmatrix},\quad
B_v=\begin{pmatrix}b/2\\-b\end{pmatrix},\quad
C_v=\begin{pmatrix}b/2&-b/2\end{pmatrix}.
$$

这里只有一个隐藏标量。MF1 给出历史卷积；而直接使用 $B_vh_n=y_{n+1}-A_vy_n$，可另写成有限两滞后递推

$$
\boxed{y_{n+2}=(A_v+\lambda I)y_{n+1}+(B_vC_v-\lambda A_v)y_n.}
$$

所以同一个系统可以同时具有一个无限支撑的 Mori–Zwanzig 核、一个额外标量的一阶状态实现，以及一个仅用可见向量的二阶递推。这三种表述在各自所需初值给定后兼容。不能从核支撑无限就宣称有限阶递推不可能。这里的向量演化也不自动决定单条随机粗粒轨迹的 Markov 阶数。

回到 #6881 的实际黄金整数，乘以 $\varphi$ 将 $a+e\varphi$ 变成 $e+(a+e)\varphi$。令可见量 $y=e$、隐藏量 $h=a$，则块系数恰为 $A=B=C=1,D=0$。因此 $\eta_0=a_0$、$\eta_n=0$（$n>0$），$M_0=1$、$M_j=0$（$j>0$）；消去隐藏量后，$y_{n+1}=y_n+y_{n-1}$（$n\ge1$）。一次实际移位读数恢复 $a_0=y_1-y_0$，这与本 PR 已有 `ShiftReadout.reconstruct_beta` 及 `shiftedValue_recurrence` 对齐。它是黄金乘法／原始位置移位的准确实例，不是 `carryPass` 的动力学；全部原始构造仍可能在黄金求值中合并。

这说明“过去被编码在现在”应理解为目标相关的充分摘要，而非历史逐帧全保留。某一向量同时对应多条可见历史，不妨碍其成为特定更新方程的充分初值。若目标改成实际进位规则的合法性，RD/PT 中的原始数位反例仍要求另一组观察；同一摘要不能跨操作族无条件复用。

## MF.6 精确可恢复，不代表有限精度下稳定可恢复

当 $b\ne0$ 时，从已知 $s_0,r_0$ 与下一第三坐标 $r_1$ 可恢复

$$
h_0=\frac{b s_0+(1-b)r_0-r_1}{b}.
$$

固定准确的当前观察时，下一读数的误差被放大 $1/|b|$。这不是把一个较弱算法的病态性误当成结构障碍；可以直接用两组实际概率向量给出统一逆模不存在的见证。

**定理 MF4（退化耦合附近没有统一稳定恢复）。** 对任意 $C_0>0$，取

$$
a=1/4,\qquad b=\frac1{4(C_0+1)},\qquad
x=(1/2,0,1/2),\quad z=(0,1/2,1/2).
$$

两向量非负、质量为一，参数满足严格随机条件，而且

$$
Px=Pz,\qquad |(x_0-x_1)-(z_0-z_1)|=1.
$$

实际完整下一投影之差是

$$
PK_{a,b}x-PK_{a,b}z=(b/4,b/4,-b/2),
$$

因而其 $\ell^1$ 大小为 $b$，满足 $C_0b<1$，第三坐标差还严格非零。证毕。源码 `no_uniform_hidden_recovery` 保留实际投影、完整三个下一读数、全部概率约束和任意 $C_0$ 的量词。

该族说明隐藏对比保持固定时，两次观察可以任意接近，因此没有覆盖整个有效参数域、且在零误差处趋零的统一逆误差模。固定 $b\ne0$ 时的精确可辨识性并未被否定。此处使用的是投影后读数，不能改成 $Kx-Kz$ 的全状态差；后者保留了本来未被观察的坐标。

同样，难以稳定恢复隐藏量，不自动表示指定可见预测误差很大。当耦合很小时，目标对隐藏量本身也可能不敏感。状态恢复误差与目标预测误差需分别建立界。

## MF.7 反事实补全与“想象”的有限数学解释

固定观察序列 $y_0,\ldots,y_n$ 后，集合

$$
\mathcal F_n=\{x_0:PT^kx_0=y_k\text{ 对 }0\le k\le n\}
$$

记录所有相容初态，后续候选为 $\{PT^{n+j}x_0:x_0\in\mathcal F_n\}$。增加观察是在与实际约束作交集；从中选一个候选构造未来，可以被非正式地称为反事实补全或模型想象。但这个集合不是 $X\setminus\{x_{\mathrm{actual}}\}$：在模型准确且数据无误时，它包含实际初态，同时排除了不相容的其他状态。候选数量也不自动给出概率，概率必须来自另行指定的先验与路径律。

因而不能从 MF1–MF4 推出“记忆就是现实的逻辑否定”或“物理记忆等于心理想象”。可以严格保留的是：实际隐藏自由度通过动力学产生反馈；部分观察下的推断需要在相容纤维里工作；足够的预测摘要只须区分导致不同目标未来的纤维类。按相同未来条件分布合并历史的思想在因果状态理论中已有系统研究 [MF3]，但将其应用到某个随机过程仍需指定路径概率，不能把确定性集合分类直接当作概率定理。

## MF.8 下一条数学义务与来源

MF1–MF4 的普通证明分别由两个新 Lean 模块及同名 Scribe 承载。补编其余等式是从所列更新、已有范数/投影代数与几何级数直接推导的解释，不另立绑定包装。新源码尚需实际 elaboration、kernel 与 Scribe 核验；源码存在不等于这些检查已执行。

当前具体的剩余问题是：在含有限精度观察与明确时间范围的真实动态上，求目标相关的最小记忆实现及其最优误差模。MF2 先剔除永远静默的方向；MF3 明确算出记忆尾；MF4 则排除把精确单射性当作统一稳定恢复。对于 #6881 的原始进位关系，还必须把依赖局部守卫的转移对齐到这种可见/隐藏框架，不能把线性位移或分布向量的结果冒充任意进位历史的闭合。对于随机 Zeckendorf 游戏的既有目标，合法动作与选定路径测度仍是前置义务，本补编不主张已经得到混合界或高斯极限。

[MF1] F. Wang, P. Benner, J. Heiland. *Partial Observation of Linear Systems with the Mori-Zwanzig Formalism*. arXiv:2606.23341v1, 22 June 2026. https://arxiv.org/html/2606.23341v1 。第3节分别识别初始隐藏项和历史反馈项；线性消元机制是已有数学，不声明为新发现。

[MF2] Y.-T. Lin, Y. Tian, M. Anghel, D. Livescu. *Data-driven learning for the Mori-Zwanzig formalism: a generalization of the Koopman learning framework*. arXiv:2101.05873. https://arxiv.org/abs/2101.05873 。用于投影空间、Koopman 观察与记忆核学习的定位，不将其数据拟合结论变成当前模型的假设。

[MF3] C. R. Shalizi, J. P. Crutchfield. *Computational Mechanics: Pattern and Prediction, Structure and Simplicity*. Journal of Statistical Physics 104 (2001), 817–879; arXiv:cond-mat/9907176. https://arxiv.org/abs/cond-mat/9907176 。未来条件分布相同的历史等价与最小预测表示；不作为心理学中“记忆等于想象”的依据。

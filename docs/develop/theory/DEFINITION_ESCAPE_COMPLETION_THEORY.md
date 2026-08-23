# 定义逃逸完备化理论
## Definition-Escape Completion Theory（DECT）

> **状态**：理论纲领与可形式化内核，v1.0，2026-08-23。  
> **写入纪律**：本文采用追加式演化；后续版本只在文末增订，不回写、不删除既有段落。  
> **母文关系**：本文承接 `QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md` 尾部的 `CUT + FLOW + ADMIT + ANCHOR` 过程语言，但另立单文件，以免继续扩大母文并保持主题边界。  
> **主张边界**：本文提出一套统一定义、若干直接定理、复杂性归约、定量指标与研究程序；不把邻近领域的已知构件冒领为单项首创，也不把尚未完成的解析估计标成已证定理。

---

## 摘要

许多数学问题真正困难的环节，并不是在既有定理图中寻找一条更长的路径，而是提出一个此前不存在的定义，使原先混合在同一类中的对象被分开。几何辅助线、新坐标、生成函数、累积量、能量泛函、谱、商空间、重整化常数和碰撞历史图，都可以被理解为同一种操作：

\[
\boxed{
\text{对象没有改变，描述对象的纤维结构改变了。}
}
\]

定义通常是保守扩张：把定义展开后并没有凭空增加事实。然而，定义可以改变证明几何，把全局搜索变成局部递推，把组合爆炸变成可求和预算，把不可闭合的当前读数提升为可闭合的记忆态。因此，“定义没有增加逻辑内容”和“定义产生了新的数学能力”并不矛盾；前者谈可消去性，后者谈表示、压缩与推理复杂度。

本文把定义发现的中心对象从“全部可能定义”改为当前表示留下的**目标逃逸残差**。给定完整对象空间 \(X\)、当前概念 \(q:X\to Q\) 与目标 \(T:X\to Y\)，定义

\[
\mathcal E(q;T)
=
\{(x,y)\in X^2:q(x)=q(y),\ T(x)\neq T(y)\}.
\]

它记录了当前概念认为相同、但目标必须区分的对象对。候选新定义 \(d:X\to D\) 与当前概念联合为

\[
(q\vee d)(x)=(q(x),d(x)).
\]

理论的基本恒等式为

\[
\boxed{
\mathcal E(q\vee d;T)
=
\mathcal E(q;T)\cap\ker d.
}
\]

所以一个定义的作用不是神秘地“产生答案”，而是切开一部分目标异质纤维。平凡定义不切开任何残差；直接把目标写入定义虽然瞬间清空残差，却只是答案泄漏；完整身份编码虽然充分，却没有压缩。真正有价值的定义必须在目标无关、低描述成本、结构自然和可迁移等约束下，切开大量现有语言无法区分的逃逸对。

本文由此区分两类问题：

\[
\boxed{
\begin{aligned}
&\text{内层问题：在固定定义语言中选择一组定义；}\\
&\text{外层问题：当固定语言存在盲核时发明新的定义原语。}
\end{aligned}
}
\]

有限显式候选中的内层问题精确归约为加权集合覆盖，因而具有 NP 完备性与次模优化结构；外层问题则是对角逃逸、语法扩展和创造性的真正所在地。结合 Yu Deng、Zaher Hani、Xiao Ma 以及 Yu Deng、Hao Shen 的工作，本文进一步提出：困难解析证明中的新定义，常常不是直接删去复杂历史，而是先构造一个**保持历史的提升**，再证明只有某些历史能够逃出目标观察者的预测纤维；累积量、Feynman 图、collision-history molecules、cutting algorithm、Hepp trees 与尺度自适应展开深度，均可放入这一统一框架。

本文最终得到一个研究纲领：

\[
\boxed{
\text{定义发现不是枚举定义，
而是识别、切割并低成本回收逃逸残差。}
}
\]

---

# 第一部　定义作为纤维切割

## 1.1 定义为何像辅助线

设一个问题已经用语言 \(L\) 描述。普通证明搜索固定 \(L\)，在已有命题、引理和变换之间寻找路径。引入新定义则扩展语言为 \(L[d]\)。若 \(d\) 是显式可展开的，则 \(L[d]\) 对原语言通常是保守扩张；但证明长度、局部性、可组合性和自动化难度可能发生巨变。

因此必须区分：

\[
\begin{aligned}
\text{语义保守性}
&:\quad d\text{ 不加入新的原始事实};\\
\text{证明非保守性}
&:\quad d\text{ 可以极大改变最短证明与搜索空间}.
\end{aligned}
\]

辅助线的作用也不是改变原图形，而是暴露一个原先没有名字的关系。定义的创造性不在“无中生有一个对象”，而在“选择一个恰好使关键关系局部化的坐标”。

## 1.2 定义逃逸系统

一个**定义逃逸系统**记为

\[
\mathfrak D
=
(X,R,r,q,T,\Gamma,\llbracket\cdot\rrbracket,c,\nu).
\]

其中：

- \(X\) 是完整对象或完整状态空间；
- \(R\) 是原始可读取结构的值域；
- \(r:X\to R\) 是原始读数；
- \(q:X\to Q\) 是当前已经采用的概念；
- \(T:X\to Y\) 是希望预测、分类、构造或证明的目标；
- \(\Gamma\) 是允许提出定义的语法；
- \(\llbracket\gamma\rrbracket=d_\gamma:X\to D_\gamma\) 是定义代码的语义；
- \(c(\gamma)\ge0\) 是定义成本；
- \(\nu\) 是定义在 \(X^2\) 或相关残差空间上的权重、计数或测度。

候选定义原则上应从原始结构产生：

\[
d_\gamma=\phi_\gamma\circ r.
\]

这条要求排除了向对象中偷偷注入外部答案，但尚不足以排除目标泄漏；目标依赖必须由语法来源账本另行审计。

## 1.3 概念的核

对任意 \(f:X\to Z\)，定义

\[
\ker f
=
\{(x,y):f(x)=f(y)\}.
\]

DECT 中，概念首先由其纤维结构而不是值域命名决定。两个函数即使值域完全不同，只要核相同，它们提供的区分能力便相同。

定义细化序：

\[
q\preceq p
\quad\Longleftrightarrow\quad
\ker p\subseteq\ker q.
\]

它表示 \(p\) 至少保留了 \(q\) 的全部区分。若使用实现像作为值域，则该关系等价于 \(q\) 通过 \(p\) 因子化。

仓库中的

`D5/S3/ConceptDynamics/ConceptJoinUniversal.lean`

已经用函数因子化定义 `Refines`，并证明联合读数是最小公共细化。本文将其解释为定义切割的代数底座。

## 1.4 联合概念

定义

\[
q\vee d:X\to Q\times D,
\qquad
(q\vee d)(x)=(q(x),d(x)).
\]

立即有

\[
\boxed{
\ker(q\vee d)=\ker q\cap\ker d.
}
\]

对有限定义集 \(S\subseteq\Gamma\)，记

\[
q\vee S
=
\left(x\mapsto
\bigl(q(x),(d_\gamma(x))_{\gamma\in S}\bigr)
\right),
\]

则

\[
\ker(q\vee S)
=
\ker q\cap\bigcap_{\gamma\in S}\ker d_\gamma.
\]

联合定义满足交换、结合与幂等，只在概念等价而不一定在字面类型相同的意义下成立。这与母文强调的“概念级幂等而非载体级字面幂等”一致。

---

# 第二部　目标逃逸残差

## 2.1 目标逃逸关系

定义

\[
\boxed{
\mathcal E(q;T)
=
\ker q\setminus\ker T.
}
\]

亦即

\[
(x,y)\in\mathcal E(q;T)
\iff
q(x)=q(y)
\ \wedge\ 
T(x)\neq T(y).
\]

它是当前问题尚未闭合的精确位置：不是整个对象空间，不是全部未证明命题，而是当前概念纤维内部的目标异质部分。

## 2.2 充分性—逃逸等价定理

以下命题等价：

1. \(\mathcal E(q;T)=\varnothing\)；
2. \(\ker q\subseteq\ker T\)；
3. \(T\) 在每个 \(q\)-纤维上为常值；
4. 存在
   \[
   \overline T:\operatorname{range}(q)\to Y
   \]
   使
   \[
   T=\overline T\circ\operatorname{rangeFactorization}(q).
   \]

证明只需在 \(q\) 的实现像上按纤维常值定义 \(\overline T\)。

仓库中的

`D5/S3/ConceptDynamics/Refinement/InductiveSufficiency.lean`

已形式化这一逻辑骨架：预测不能通过历史因子化，当且仅当存在两个历史相同而预测不同的状态。DECT 把该反例对提升为一整套残差几何。

## 2.3 残差交公式

对任意定义 \(d\)，有

\[
\boxed{
\mathcal E(q\vee d;T)
=
\mathcal E(q;T)\cap\ker d.
}
\]

证明：

\[
\begin{aligned}
\mathcal E(q\vee d;T)
&=\ker(q\vee d)\setminus\ker T\\
&=(\ker q\cap\ker d)\setminus\ker T\\
&=(\ker q\setminus\ker T)\cap\ker d.
\end{aligned}
\]

这一恒等式是全文的中心。它给出一个完全可审计的定义价值判据：

\[
\operatorname{Capture}(d\mid q,T)
=
\mathcal E(q;T)\cap(\ker d)^c.
\]

定义 \(d\) 有效，当且仅当它在至少一个逃逸对上取不同值。

## 2.4 有限定义族

对有限 \(S\subseteq\Gamma\)，

\[
\boxed{
\mathcal E(q\vee S;T)
=
\mathcal E(q;T)
\cap
\bigcap_{\gamma\in S}\ker d_\gamma.
}
\]

因此

\[
\mathcal E(q\vee S;T)=\varnothing
\]

当且仅当

\[
\mathcal E(q;T)
\subseteq
\bigcup_{\gamma\in S}(\ker d_\gamma)^c.
\]

即每一个逃逸对至少被一个定义切开。

## 2.5 规范目标闭包

直接联合目标：

\[
\operatorname{cl}_T(q)=q\vee T.
\]

它必然充分，并且是所有同时细化 \(q\) 且足以决定 \(T\) 的概念中的最粗者，精确意义由核序给出：若 \(p\) 细化 \(q\) 且 \(T\) 通过 \(p\) 因子化，则

\[
\ker p\subseteq\ker q\cap\ker T
=
\ker(q\vee T).
\]

仓库中的

`D5/S3/ConceptDynamics/Completion/TargetClosureOperator.lean`

已经证明该闭包的广延性、单调性和概念等价意义下的幂等性。

但 \(q\vee T\) 只是语义基准，不是定义创造的答案。真正任务是：在禁止语法依赖 \(T\) 的条件下，构造低成本 \(d\)，使

\[
\ker(q\vee d)\subseteq\ker T.
\]

---

# 第三部　平凡定义、泄漏与来源账本

## 3.1 冗余定义

若

\[
\ker q\subseteq\ker d,
\]

则称 \(d\) 相对于 \(q\) 冗余。等价地，\(d\) 是 \(q\) 的函数。

此时

\[
\mathcal E(q\vee d;T)=\mathcal E(q;T)
\]

对任意目标成立。重新命名、同义包装、把已有坐标做可逆编码，均属于零增益定义。

## 3.2 目标泄漏

取

\[
d=T
\]

会立即消灭全部残差；取

\[
d(x)=x
\]

也会决定任意目标。这说明若不限制定义语言，“发现充分定义”是平凡问题。

因此必须同时约束：

\[
\begin{aligned}
&\text{来源：定义不得调用目标或其等价答案接口；}\\
&\text{成本：定义不得只是完整身份编码；}\\
&\text{自然性：定义应尊重问题的对称、局部或组合结构；}\\
&\text{迁移性：定义不应只记住一个训练实例。}
\end{aligned}
\]

## 3.3 外延反泄漏不可能性

设两个定义代码 \(\gamma_1,\gamma_2\) 满足

\[
\llbracket\gamma_1\rrbracket
=
\llbracket\gamma_2\rrbracket,
\]

但 \(\gamma_1\) 直接调用目标，\(\gamma_2\) 独立从原始结构推导同一函数。任何只依赖外延函数图的评分器都无法区分二者。

所以反泄漏不是纯数学函数性质，而是来源性质。必须记录：

- 语法树；
- 依赖 DAG；
- 训练数据与目标访问边界；
- 定义语义证明；
- 非冗余见证；
- 捕获量证书。

## 3.4 定义证书

一个可审计定义证书至少包含

\[
\mathcal C_d=
(
\gamma,
 d,
 \mathsf{Semantics},
 \mathsf{Dependencies},
 \mathsf{TargetFree},
 \mathsf{Witness},
 \mathsf{Capture},
 c(d)
).
\]

其中 `Witness` 给出

\[
q(x)=q(y),
\qquad
T(x)\neq T(y),
\qquad
d(x)\neq d(y),
\]

而 `Capture` 给出该定义对整类残差而非单个样本的作用界。

---

# 第四部　残差覆盖与复杂性

## 4.1 残差图

把 \(X\) 视为顶点集，把 \(\mathcal E(q;T)\) 视为边集，得到残差图

\[
G_{q,T}=(X,\mathcal E(q;T)).
\]

每个定义 \(d\) 产生切集

\[
C_d
=
\{(x,y)\in\mathcal E(q;T):d(x)\neq d(y)\}.
\]

定义集 \(S\) 足以决定目标，当且仅当

\[
\bigcup_{d\in S}C_d
=
\mathcal E(q;T).
\]

因此固定候选语言内的定义选择，就是用允许切集覆盖全部残差边。

## 4.2 最小定义完备化成本

令

\[
C(S)=\sum_{d\in S}c(d).
\]

定义

\[
\boxed{
\operatorname{DefDim}_\Gamma(T\mid q)
=
\inf
\left\{
C(S):
S\subseteq_{\mathrm{fin}}\Gamma,
\ \mathcal E(q\vee S;T)=\varnothing
\right\}.
}
\]

单位成本下，它是最少需要多少个定义；一般成本下，它是从当前表示到目标充分表示的最小描述预算。

## 4.3 与集合覆盖的精确归约

给定集合覆盖实例 \(U=\{u_1,\ldots,u_n\}\) 与子集族 \(A_1,\ldots,A_m\)，构造

\[
X=\{a_u,b_u:u\in U\},
\]

并令

\[
q(a_u)=q(b_u)=u,
\qquad
T(a_u)=0,
\qquad
T(b_u)=1.
\]

对每个 \(A_i\) 定义

\[
d_i(a_u)=0,
\qquad
d_i(b_u)=\mathbf 1_{u\in A_i}.
\]

则 \(d_i\) 切开逃逸对 \((a_u,b_u)\)，当且仅当 \(u\in A_i\)。因此存在不超过 \(k\) 个定义清空全部残差，当且仅当存在不超过 \(k\) 个集合覆盖 \(U\)。

于是，在有限显式函数表模型中：

\[
\boxed{
\text{最小定义选择判定问题是 NP 完备的。}
}
\]

这精确支持“包内搜索本质上会遇到组合爆炸”的直觉，但必须保留边界：NP 结论针对**候选已经给定后的选择问题**；发明候选语言本身不是同一个问题，若语法足够强，语义等价、全局充分性或最短程序问题还可能不可判定。

## 4.4 次模捕获

定义剩余质量

\[
M(S)=\nu(\mathcal E(q\vee S;T))
\]

和总捕获

\[
F(S)=M(\varnothing)-M(S).
\]

则

\[
F(S)
=
\nu\left(
\mathcal E(q;T)
\cap
\bigcup_{d\in S}(\ker d)^c
\right).
\]

这是加权覆盖函数，故单调且次模。若 \(A\subseteq B\) 且 \(d\notin B\)，则

\[
F(A\cup\{d\})-F(A)
\ge
F(B\cup\{d\})-F(B).
\]

定义的边际收益随已有定义增加而递减。由此得到自然贪心规则：

\[
d_{k+1}
=
\arg\max_d
\frac{
M(S_k)-M(S_k\cup\{d\})
}{c(d)}.
\]

这不能解决语言盲核，却为固定候选集内的搜索提供理论保证和停止条件。

---

# 第五部　语言盲核与真正创造

## 5.1 共同不可区分核

定义语言 \(\Gamma\) 的共同核为

\[
\boxed{
K_\Gamma
=
\bigcap_{d\in\Gamma}\ker d.
}
\]

若 \((x,y)\in K_\Gamma\)，则现有全部定义都不能区分二者。

定义语言盲残差

\[
\boxed{
\mathcal B_\Gamma(q;T)
=
\mathcal E(q;T)\cap K_\Gamma.
}
\]

它表示目标必须区分、当前概念没有区分、而现有语言中的所有定义也都无法区分的对象对。

## 5.2 盲核不可能性定理

若

\[
\mathcal B_\Gamma(q;T)\neq\varnothing,
\]

则任意有限或任意点态联合的 \(\Gamma\)-定义都不能使目标因子化。

证明：取盲残差对 \((x,y)\)。所有定义在二者上相等，所以任意联合读数也相等；但目标值不同。

因此：

\[
\boxed{
\begin{aligned}
\mathcal B_\Gamma(q;T)=\varnothing
&\Rightarrow
\text{语言点态足够，剩余问题是选择或紧致化；}\\
\mathcal B_\Gamma(q;T)\neq\varnothing
&\Rightarrow
\text{再强的包内搜索也不会成功。}
\end{aligned}
}
\]

## 5.3 有限紧致性

若 \(X\) 有限且盲残差为空，则存在有限定义集 \(S\subseteq\Gamma\) 清空残差。证明只需为每条有限残差边选一个分离它的定义。

无限空间中，盲残差为空只保证每一对都能被某个定义分开，不保证存在统一有限定义族。若 \(\mathcal E(q;T)\) 在某拓扑下紧，且每个分离集

\[
U_d=\{(x,y):d(x)\neq d(y)\}
\]

在残差子空间中开，则 \(\{U_d\}_{d\in\Gamma}\) 构成开覆盖；紧致性给出有限子覆盖。因此，有限定义完备性可以由残差空间的紧致性而非对象空间的有限性获得。

## 5.4 原语创造与坐标创造

若

\[
K_\Gamma\subseteq\ker d,
\]

则 \(d\) 原则上由现有全部定义联合读数决定。它没有扩张无限预算下的区分能力，但仍可能把一个极其复杂的组合压缩成短坐标，称为**坐标创造**。

若

\[
K_\Gamma\nsubseteq\ker d,
\]

则 \(d\) 切开了现有语言共同忽略的对象对，称为**原语创造**。

相对于目标，定义其生产性为

\[
\boxed{
P_\Gamma(d\mid q,T)
=
\nu\left(
\mathcal B_\Gamma(q;T)
\cap
(\ker d)^c
\right).
}
\]

只有

\[
P_\Gamma(d\mid q,T)>0
\]

时，新定义才真正降低语言盲核。

这给出创造性的第一条精确定律：

\[
\boxed{
\text{不在目录中，不等于不在语言闭包中；
不在语言闭包中，也不自动等于对目标有用。}
}
\]

---

# 第六部　定义逃逸谱

## 6.1 预算逃逸率

假设

\[
M_0=\nu(\mathcal E(q;T))>0.
\]

定义预算 \(L\) 下的最优逃逸率：

\[
\boxed{
\rho_\Gamma(L)
=
\inf_{C(S)\le L}
\frac{
\nu(\mathcal E(q\vee S;T))
}{M_0}.
}
\]

显然

\[
0\le\rho_\Gamma(L)\le1,
\qquad
L_1\le L_2
\Rightarrow
\rho_\Gamma(L_2)\le\rho_\Gamma(L_1).
\]

定义不可消除逃逸率

\[
\rho_\Gamma^\infty
=
\frac{
\nu(\mathcal B_\Gamma(q;T))
}{M_0}.
\]

在适当可数性与测度连续性条件下，预算趋于无穷时

\[
\rho_\Gamma(L)\longrightarrow\rho_\Gamma^\infty.
\]

## 6.2 三类语言

定义语言可分为：

### 有限闭合型

存在有限 \(L\) 使

\[
\rho_\Gamma(L)=0.
\]

### 渐近闭合型

每个有限预算仍有残差，但

\[
\lim_{L\to\infty}\rho_\Gamma(L)=0.
\]

### 结构不完备型

\[
\rho_\Gamma^\infty>0.
\]

第三类不是“搜索不够久”，而是搜索空间缺少必要切割方向。

## 6.3 创造性跃迁

加入新定义 \(d\) 后，逃逸谱可能只发生小幅平移，也可能出现跃迁。定义

\[
J_\Gamma(d;L)
=
\rho_\Gamma(L)-\rho_{\Gamma\cup\{d\}}(L).
\]

一个跨多个预算区间保持显著正值的定义，比只在单一预算点降低残差的定义更有结构价值。若它还同时降低 \(\rho^\infty\)，则是原语创造；若只降低有限预算谱而不改变 \(\rho^\infty\)，则是坐标压缩。

## 6.4 定义前沿

对每个定义或定义集记录三元组

\[
\bigl(C(S),\ M(S),\ \mathsf{ProofCost}(S)\bigr).
\]

不被另一方案同时在三项上严格支配的方案构成**定义前沿**。创造性研究不应只追求残差为零，而应研究成本、残差与证明复杂度之间的 Pareto 几何。

---

# 第七部　对角逃逸的分层

## 7.1 仓库已有对角骨架

仓库中的

`D5/S0/Diagonal/EscapeCount.lean`

定义扭转对角

\[
\operatorname{diag}_f(g)(a)=f(g(a,a))
\]

及其不落入原列表行像的逃逸谓词，并给出有限情况下的精确计数。

`D5/S0/Diagonal/Naturality/RelativeDiagonalEscape.lean`

证明无固定点扭转迫使对角对象逃出。

`D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.lean`

在传递等变情形中得到形如

\[
1-\frac{K}{n^\omega}
\]

的归一化逃逸率。

`D5/S3/ObserverMemory/DiagonalEscape/DiagonalCompletionEscape.lean`

证明任意二进制序列枚举都存在一个与全部有限前缀系统相容、却不同于每一被枚举行的无限序列。

这些结果证明固定列表在自应用扭转下的非闭合性，但“逃出列表”尚不等于“发明有用定义”。

## 7.2 四级逃逸

本文区分：

### 目录逃逸

\[
d\notin\{d_0,d_1,d_2,\ldots\}.
\]

只表示没有被逐字列出。

### 生成闭包逃逸

\[
d\notin\operatorname{Closure}(\Gamma).
\]

表示不能由允许组合操作生成。

### 区分闭包逃逸

\[
K_\Gamma\nsubseteq\ker d.
\]

表示它确实提供现有语言没有的区分方向。

### 生产性逃逸

\[
P_\Gamma(d\mid q,T)>0.
\]

表示它切开了与目标有关的盲残差。

只有第四级直接服务于问题解决。

## 7.3 逃逸—回收双律

随机噪声很容易逃出一个有限目录，极高复杂度的身份编码也能逃出，但二者都未必形成数学创造。必须再有一个低成本回收步骤，把逃逸对象压缩为可复用结构。

定义一个创造事件为二元组

\[
(\Delta,\Pi),
\]

其中 \(\Delta\) 产生闭包外见证，\(\Pi\) 把该见证及其同类压缩成定义模式。于是

\[
\boxed{
\text{创造}
=
\text{结构性逃逸}
+
\text{低成本回收}.
}
\]

对角化负责证明“当前表示不封闭”；新定义负责解释“逃出的对象为什么属于一个简单、稳定、可迁移的新类”。

---

# 第八部　动态预测逃逸

## 8.1 有限时域目标

设

\[
\tau:X\to X
\]

为更新，\(q:X\to O\) 为当前读数。定义长度 \(N\) 的未来轨迹

\[
T_N(x)
=
\bigl(q(x),q(\tau x),\ldots,q(\tau^N x)\bigr).
\]

定义预测逃逸关系

\[
\boxed{
\mathcal E_N(q,\tau)
=
\mathcal E(q;T_N).
}
\]

它记录当前读数相同、但在未来 \(N\) 步内会出现不同读数的状态对。

显然

\[
\mathcal E_N(q,\tau)
\subseteq
\mathcal E_{N+1}(q,\tau).
\]

## 8.2 首次逃逸时间

定义

\[
\operatorname{escTime}_{q,\tau}(x,y)
=
\inf\{n\ge0:q(\tau^n x)\neq q(\tau^n y)\},
\]

若永不分离则取 \(\infty\)。

由此可以研究：

- 第 \(n\) 层新逃逸质量；
- 条件逃逸率；
- 仍未分离的生存函数；
- 一个定义使逃逸时间向后推迟多少；
- 一个记忆定义是否把全部有限时域逃逸推至 \(\infty\)。

定义生存集

\[
S_n=\{(x,y):q(\tau^k x)=q(\tau^k y),\ 0\le k\le n\},
\]

则

\[
S_{n+1}\subseteq S_n.
\]

若有概率或计数权重，可定义条件危险率

\[
h_n
=
\frac{\nu(S_{n-1}\setminus S_n)}{\nu(S_{n-1})}.
\]

这给“对角化逃逸率”增加了真正动态的含义：不是只问是否逃出，而是问逃逸在何时、以何种速率暴露当前定义的预测不足。

## 8.3 无限预测完成

定义

\[
x\sim_\infty y
\iff
\forall n\ge0,
\quad q(\tau^n x)=q(\tau^n y).
\]

仓库中的

`D5/S3/ObserverMemory/Refinement/PredictionCompletion.lean`

正是按这一关系构造完成态，并证明读数细化诱导完成态之间唯一的满射因子。

DECT 的动态问题是：寻找低成本记忆定义 \(d\)，使

\[
\ker(q\vee d)
\subseteq
\sim_\infty.
\]

也就是说，当前读数加上定义出的记忆坐标，足以决定全部未来读数。

## 8.4 预测定义维数

定义

\[
\operatorname{PredDefDim}_N(q,\tau)
=
\inf\{C(S):\mathcal E_N(q\vee S,\tau)=\varnothing\},
\]

以及

\[
\operatorname{PredDefDim}_\infty(q,\tau)
=
\inf\{C(S):\mathcal E_\infty(q\vee S,\tau)=\varnothing\}.
\]

它度量为了使观察过程 Markov 化或预测闭合，至少需要多少附加定义复杂度。

## 8.5 成本—时域逃逸曲面

定义

\[
\boxed{
\rho_\Gamma(L,N)
=
\inf_{C(S)\le L}
\frac{
\nu(\mathcal E_N(q\vee S,\tau))
}{
\nu(\mathcal E_N(q,\tau))
}.
}
\]

这是一张二维曲面：

- 沿 \(L\) 增大，允许更复杂的定义；
- 沿 \(N\) 增大，要求更长的预测寿命。

很多“短时成立、长时失效”的有效理论，可以被解释为固定预算 \(L\) 下，逃逸曲面在某个时域后突然上升。

---

# 第九部　近似、概率与预测影响

## 9.1 容差残差

若目标空间带度量 \(d_Y\)，定义

\[
\mathcal E_\eta(q;T)
=
\{(x,y):q(x)=q(y),\ d_Y(Tx,Ty)>\eta\}.
\]

精确充分性对应 \(\eta=0\)；近似充分性要求纤维内目标直径不超过 \(\eta\)。

定义最坏纤维缺陷

\[
\Delta(q;T)
=
\sup_{q(x)=q(y)}d_Y(Tx,Ty).
\]

若 \(\Delta(q;T)\le\eta\)，则 \(q\) 在误差 \(\eta\) 内决定目标。

## 9.2 预测影响伪距离

对动力学 \(U_t\) 与观察 \(\pi\)，定义

\[
\boxed{
D_T^{\mathrm{pred}}(x,y)
=
\sup_{0\le t\le T}
 d_Z(\pi U_t x,\pi U_t y).
}
\]

它不测量微观对象本身的距离，而测量它们对指定观察者未来读数的可区分程度。

其零核就是有限时域预测等价。无限时域版本的零核对应完整未来完成。

该定义解释了一个重要现象：

\[
\|x-y\|_{\mathrm{raw}}\text{ 很大}
\quad\text{但}
\quad
D_T^{\mathrm{pred}}(x,y)\text{ 很小}.
\]

高阶相关、巨大图族或复杂历史可以真实存在，却对目标观察者几乎无影响。因此必须区分：

\[
\begin{aligned}
\mathsf{CorrelationMass}
&=\text{系统中存在多少相关结构};\\
\mathsf{ObserverInfluence}
&=\text{这些结构改变目标未来读数多少}.
\end{aligned}
\]

## 9.3 近似级联

设第一层闭包误差为 \(\delta\)，第二层映射的 Lipschitz 常数为 \(L\)，第二层自身误差为 \(\eta\)。则组合误差满足

\[
\boxed{
E_{13}\le L\delta+\eta.
}
\]

该不等式是仓库精确 `CascadeCompletion` 的定量版本，也与

`D5/S3/Observer/Naturality/ApproximateSemiconjugacyError.lean`

及

`D5/S3/Observer/Naturality/IteratedDefectAccumulation.lean`

中的缺陷累积结构一致。

对于非均匀单步缺陷 \(\delta_k\)，若抽象更新为 \(L\)-Lipschitz，则第 \(n\) 步误差由

\[
\sum_{k=0}^{n-1}L^{n-1-k}\delta_k
\]

控制。真正困难的部分不是这一外层递推，而是如何从问题结构中构造可求和的 \(\delta_k\)。

---

# 第十部　准备回缩与极限半群

## 10.1 为什么 Boltzmann 不是普通有限尺度商

设 \(\pi_\varepsilon\) 只读取单粒子边缘。两个微观概率律可以有相同单粒子边缘却有不同二粒子相关；BBGKY 层级中低阶未来会受高阶相关影响。因此一般不存在有限尺度精确关系

\[
\pi_\varepsilon U_{\varepsilon,t}
=
S_t\pi_\varepsilon.
\]

把 Boltzmann–Grad 极限简单称为“舍掉高阶关联后的普通商”，会抹去证明的核心：高阶关联不是先验删除，而是被完整追踪后证明其预测影响在目标尺度下变小。

## 10.2 规范准备截面

设

\[
\pi_\varepsilon:X_\varepsilon\to Z
\]

为宏观读数，选择规范准备映射

\[
s_\varepsilon:Z\to X_\varepsilon,
\qquad
\pi_\varepsilon s_\varepsilon=\operatorname{id}_Z.
\]

定义回缩

\[
R_\varepsilon=s_\varepsilon\pi_\varepsilon,
\qquad
R_\varepsilon^2=R_\varepsilon.
\]

候选有效动力学为

\[
S_{\varepsilon,t}
=
\pi_\varepsilon U_{\varepsilon,t}s_\varepsilon.
\]

## 10.3 单步缺陷恒等式

定义

\[
\delta_{\varepsilon,t}(x)
=
 d_Z\left(
\pi_\varepsilon U_{\varepsilon,t}x,
\pi_\varepsilon U_{\varepsilon,t}R_\varepsilon x
\right).
\]

则严格有

\[
\boxed{
 d_Z\left(
\pi_\varepsilon U_{\varepsilon,t}x,
S_{\varepsilon,t}(\pi_\varepsilon x)
\right)
=
\delta_{\varepsilon,t}(x).
}
\]

所以闭包问题被压缩为：真实状态与其规范准备代表在预测影响伪距离中是否渐近不可区分。

## 10.4 半群缺陷恒等式

若 \(U_{\varepsilon,t}\) 是流或半群，则

\[
\begin{aligned}
S_{\varepsilon,t+s}(m)
&=\pi_\varepsilon U_{\varepsilon,t}
U_{\varepsilon,s}s_\varepsilon(m),\\
S_{\varepsilon,t}S_{\varepsilon,s}(m)
&=\pi_\varepsilon U_{\varepsilon,t}
R_\varepsilon U_{\varepsilon,s}s_\varepsilon(m).
\end{aligned}
\]

因此

\[
\boxed{
 d_Z\left(
S_{\varepsilon,t+s}(m),
S_{\varepsilon,t}S_{\varepsilon,s}(m)
\right)
=
\delta_{\varepsilon,t}
\left(U_{\varepsilon,s}s_\varepsilon(m)\right).
}
\]

若该缺陷在相关准备类和有限时域上一致趋零，并且 \(S_{\varepsilon,t}\to S_t\)，则极限动力学满足严格半群律。

于是有效半群可以不是有限尺度精确商，而是由预测纤维渐近坍缩涌现：

\[
\boxed{
\text{微观动力学不必严格保持准备流形；
只需在目标预测度量中渐近保持。}
}
\]

## 10.5 历史保持提升优先于商化

本文提出原则：

\[
\boxed{
\textbf{history-preserving lift before quotient}
}
\]

即先把状态提升为

\[
(\text{宏观坐标},\text{未决相关历史}),
\]

在提升空间中追踪历史如何生成、传播、抵消和切割，再证明未决历史的观察者影响趋零，最后才允许商化。

这与“先忘记，再希望误差小”相反；它要求先保存忘记的来源，再为遗忘提供证书。

---

# 第十一部　Yu Deng 方法论的统一读法

## 11.1 波动动力学：先确定尺度

Yu Deng 与 Zaher Hani 的 `Full derivation of the wave kinetic equation`（arXiv:2104.11204）在特定大盒、弱非线性与动力学时间尺度下，从 NLS 推导波动动力学方程。方法论上的第一条不是先选一个漂亮定义，而是先明确：

\[
\boxed{
\text{定义的有效性依赖尺度族，而不是单个固定系统。}
}
\]

因此观察者、误差、时间窗和定义深度都应带参数：

\[
q_\varepsilon,
\quad
T(\varepsilon),
\quad
\rho_\Gamma(L,T,\varepsilon).
\]

## 11.2 传播混沌：渐近乘积而非精确乘积

`Propagation of chaos and the higher order statistics in the wave kinetic theory`（arXiv:2110.04565）研究高阶统计并证明适当初始独立模式在动力学极限中保持渐近独立。

这不意味着有限尺度系统严格为乘积，而意味着固定阶观察在极限中因子化。用 DECT 语言：

\[
\boxed{
\text{观察者融合在极限中渐近保持 monoidal 结构。}
}
\]

仓库的 `IndependentProductCompletion.lean` 给出精确独立系统的乘积完成；Yu Deng 路线要求的是带缺陷的渐近版本。

## 11.3 坏图、抵消与定义的真实价值

`Derivation of the wave kinetic equation: full range of scaling laws`（arXiv:2301.07063）强调三步：识别任意大的坏图；发现坏图之间的高阶抵消；对剩余图给出统一算法和收敛证明。

这说明定义价值不能只由单对象大小衡量。若每个图都被分别绝对估计，组合数量可能毁掉所有小量。必须先定义正确的等价类或抵消轨道，再对分组和估计：

\[
\left|\sum_{G\in C}A_G\right|
\ll
\sum_{G\in C}|A_G|.
\]

因此 DECT 增加一条原则：

\[
\boxed{
\text{在估计逃逸质量之前，先定义逃逸对象之间的抵消关系。}
}
\]

## 11.4 长时间：可重启闭包

`Long time justification of wave turbulence theory`（arXiv:2311.10082）把短时推导扩展到 WKE 解的整个寿命。抽象结构不是一次性展开全部历史，而是在时间块之间反复重启：

\[
\text{展开}
\to
\text{提取主项}
\to
\text{压缩未决历史}
\to
\text{重新准备}
\to
\text{下一时间块}.
\]

在 DECT 中，这对应沿真实轨道反复比较

\[
U_{\Delta t}x
\quad\text{与}\quad
R_\varepsilon U_{\Delta t}x,
\]

并把每个时间块产生的定义逃逸缺陷交给 Lipschitz 加权累积定理。

## 11.5 硬球到 Boltzmann：完整碰撞历史

`Long time derivation of the Boltzmann equation from hard sphere dynamics`（arXiv:2408.07818）使用长时间 cumulant ansatz，保留相关粒子的完整碰撞历史；核心是证明 cumulant 的 \(L^1\) 小量，并把问题归约为 collision-history molecules 的组合性质，再用 cutting algorithm 处理。

这给出本文最重要的方法论解释：

\[
\boxed{
\text{不是先删除高阶关联，
而是先定义高阶关联的连通历史，
再证明其目标影响可压缩。}
}
\]

累积量把可因子化的平凡部分从高阶矩中剥离；molecule 把真正承载关联的碰撞历史压成组合对象；cutting 把全局复杂对象切成有局部预算的基本块。

## 11.6 Hilbert 第六问题：近似级联

`Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory`（arXiv:2503.01800）把硬球到 Boltzmann 的推导与 Boltzmann 到可压缩 Euler、不可压缩 Navier–Stokes–Fourier 的流体极限组合起来。其主张边界按论文原文应理解为：解决经由 Boltzmann 动理学从 Newton 定律导出这些流体方程的特定气体动力学程序，而不是自动覆盖“物理公理化”的所有可能解释。

抽象地，若

\[
E_{\mathrm{Newton}\to\mathrm{Boltzmann}}\le\delta_{\varepsilon,\alpha},
\]

且

\[
E_{\mathrm{Boltzmann}\to\mathrm{Fluid}}\le\eta_\alpha,
\]

中间降维映射 Lipschitz 常数为 \(L_\alpha\)，则

\[
\boxed{
E_{\mathrm{Newton}\to\mathrm{Fluid}}
\le
L_\alpha\delta_{\varepsilon,\alpha}
+
\eta_\alpha.
}
\]

双参数逐次极限不能无条件替换为任意联合极限；严谨做法是选择对角路径 \((\varepsilon_n,\alpha_n)\)，使两项同时趋零。

## 11.7 临界 SPDE：定义深度必须增长

Yu Deng 与 Hao Shen 的 `The four-dimensional Anderson model: a case study for critical SPDEs`（arXiv:2607.10105）处理需要任意高阶重整化的临界问题。论文指出必须展开到约 \(|\log\varepsilon|\) 阶，同时面对阶乘多个 pairing、增长的重整化项，并使用截断重整化 parametrix、Hepp trees、多尺度分析和排列求和估计控制高阶余项。

这迫使 DECT 放弃“一个固定有限定义深度适用于所有尺度”的默认假设。定义

\[
m_*(\varepsilon,\eta)
=
\min\{m:\operatorname{Defect}^{(m)}_\varepsilon\le\eta\}.
\]

临界情形可能满足

\[
 m_*(\varepsilon,\eta)
\asymp
|\log\varepsilon|.
\]

所以真正的完备化可以是：

\[
\boxed{
\text{定义深度随分辨率增长，
但增长率本身受到证明控制。}
}
\]

## 11.8 Yu Deng 范式的十步抽象

综合上述工作，可抽象为：

1. 指定目标观察量与尺度关系；
2. 找出当前低阶表示的预测逃逸方向；
3. 用 cumulant 或连通对象剥离平凡因子化部分；
4. 用树、图、molecule 或 parametrix 给逃逸历史命名；
5. 识别不能逐项估计的坏类；
6. 先建立抵消分组，再做绝对估计；
7. 用 cutting 或多尺度树把全局对象分解为基本块；
8. 为每个块分配 excess、计数和余项预算；
9. 证明全族可求和并生成单时间块缺陷；
10. 通过可重启闭包与缺陷累积延伸到完整寿命。

这套方法说明：

\[
\boxed{
\text{新定义是证明的编译器：
它把不可计算的全局展开编译成可认证的局部预算。}
}
\]

---

# 第十二部　全族求和证书

## 12.1 单项小不推出全族小

若图族 \(\mathfrak D_m\) 的数量快速增长，即使每个图满足

\[
|A_G|\le\varepsilon^\gamma,
\]

也不能推出

\[
\sum_{G\in\mathfrak D_m}|A_G|\to0.
\]

定义理论必须同时控制：

- 单块解析增益；
- 同型对象数量；
- 抵消分组；
- 切割终止；
- 截断余项；
- 时间块累积。

## 12.2 求和感知证书

提出证书结构

\[
\mathcal C=
(
G,
\operatorname{Class}(G),
\operatorname{Cut}(G),
T_G,
\operatorname{Excess}(G),
\operatorname{Count},
\operatorname{Cancellation},
\operatorname{Remainder}
).
\]

目标不是逐图证明，而是证明

\[
\left|
\sum_{G\in\mathfrak D}A_G
\right|
\le
\sum_C w(C)
\le
\delta_\varepsilon,
\qquad
\delta_\varepsilon\to0.
\]

这里 \(C\) 是抵消类或切割后类型。该 \(\delta_\varepsilon\) 随后作为单步观察者缺陷进入仓库现有的迭代误差模块。

## 12.3 证书链

完整证明链应写成

\[
\boxed{
\begin{array}{c}
\text{diagram classification}\\
\downarrow\\
\text{cancellation/cutting certificate}\\
\downarrow\\
\text{one-block predictive defect}\\
\downarrow\\
\text{iterated defect accumulation}\\
\downarrow\\
\text{lifespan-uniform asymptotic closure}.
\end{array}
}
\]

这使“数学创造”不再止于提出名字；定义必须最终产出可组合误差证书。

---

# 第十三部　定义创造算法

## 13.1 见证优先

标准流程不是先枚举全部定义，而是先找一个最小逃逸见证：

\[
q(x)=q(y),
\qquad
T(x)\neq T(y).
\]

然后询问：

1. 二者差异中哪些已由当前语言表达？
2. 哪些差异与目标无关？
3. 哪个最小结构差异稳定地解释目标分离？
4. 该差异能否推广到一整类残差，而不是只修补此对？
5. 加入该定义后，是否出现局部递推、守恒、单调、正交、因子化或可求和性？

## 13.2 双层循环

### 内层：固定语法选择

在当前候选中按

\[
\frac{\text{边际捕获}}{\text{定义成本}}
\]

选择定义，直到残差清空或边际收益归零。

### 外层：盲核扩展

若剩余残差包含

\[
(x,y)\in\mathcal B_\Gamma(q;T),
\]

则停止包内搜索，转而构造新原语 \(d\)，满足

\[
d(x)\neq d(y)
\]

且不依赖目标。加入语言后重新进入内层。

## 13.3 有限终止

若 \(X\) 有限，且每轮加入的定义至少切开一个当前残差对，则至多经过

\[
|\mathcal E(q;T)|
\]

轮终止。

若每轮至少捕获当前残差质量的 \(\alpha\) 比例，则

\[
M_k\le(1-\alpha)^kM_0.
\]

## 13.4 反例簇而非单反例

单个见证容易导致过拟合定义。应先对当前逃逸对按对称群、局部型、尺度、因果位置或图同构分类，寻找重复出现的残差模式。高价值定义通常对应一个大残差簇的低复杂度不变量。

## 13.5 常见定义算子

从残差见证生成候选定义时，可优先尝试：

- 商：忽略与目标无关的差异；
- 完成：加入决定未来所需的有限或无限记忆；
- 差分/导数：暴露变化而非绝对值；
- 对数/生成函数：把乘法或卷积变成加法；
- 累积量：剥离可因子化部分；
- 能量/势函数：把终止问题转为单调下降；
- 谱：把迭代转为乘法坐标；
- 图/树/molecule：把历史依赖转为组合类型；
- 重整化：把尺度发散分离为规范主项和有限余项；
- 截面/回缩：选择规范代表并度量离开代表流形的缺陷。

这些不是保证成功的模板，而是残差结构到定义类型之间的候选变换库。

---

# 第十四部　定义价值函数

## 14.1 生产效率

定义

\[
\operatorname{ProductiveRate}(d)
=
\frac{P_\Gamma(d\mid q,T)}{c(d)}.
\]

它衡量每单位定义复杂度切开多少语言盲残差。

## 14.2 总残差效率

即使定义没有切开盲核，也可能显著压缩有限预算问题。定义

\[
\operatorname{CaptureRate}(d\mid S)
=
\frac{
M(S)-M(S\cup\{d\})
}{c(d)}.
\]

## 14.3 证明压缩

设固定证明系统中命题 \(\varphi\) 的最短证明长度为 \(L_\mathcal P(\varphi)\)。定义

\[
\operatorname{ProofGain}(d;\varphi)
=
L_\mathcal P(\varphi)
-
\left(c(d)+L_{\mathcal P+d}(\varphi)\right).
\]

若为正，则引入定义后的总描述更短。一个定义可以不增加任何无限预算区分能力，却仍有巨大 `ProofGain`；这正是许多辅助线和标准坐标的价值。

## 14.4 迁移增益

对目标族 \(\mathcal T\)，定义

\[
\operatorname{Transfer}(d)
=
\sum_{T\in\mathcal T}
 w_T
\left[
M_T(\varnothing)-M_T(\{d\})
\right].
\]

只对单个目标有效的定义可能是补丁；跨多个目标、尺度和实例保持捕获能力的定义更可能对应真实结构。

## 14.5 稳定性与自然性

好定义还应满足：

- 对小扰动稳定；
- 对问题对称群自然；
- 对对象同构不依赖表示细节；
- 对尺度变换有明确协变律；
- 对组合系统有可控的乘积或张量行为；
- 对后续证明产生局部证书。

最终可用多目标函数

\[
\mathcal J(d)
=
\alpha\,\operatorname{Capture}
+\beta\,\operatorname{Transfer}
+\gamma\,\operatorname{ProofGain}
-\lambda c(d)
-\mu\,\operatorname{Leakage}
-\eta\,\operatorname{Instability}
\]

比较候选，而不是把单一逃逸率误当成完整创造性指标。

---

# 第十五部　不可逆与观察者的重新定位

## 15.1 不可逆不是单项属性

在有效动力学极限中，不可逆性通常属于组合结构

\[
(U_{\varepsilon,t},\pi_\varepsilon,s_\varepsilon,\varepsilon\to0^+),
\]

而不是微观流、观察者或商中任何一项的单独属性。

微观流可以可逆；宏观读数忽略高阶历史；准备截面选择低关联代表；正向极限证明真实轨迹与反复规范准备轨迹对目标观察者渐近一致。

时间反演后的状态通常带有精细相关，不再属于同一准备类。反向恢复需要完整历史，而宏观读数只保存了低阶坐标。

## 15.2 信息账本与动力学闭包必须分开

总相关熵可以解释边缘熵增长的账本来源，但信息论恒等式本身不能替代对真实动力学的累积量、图与切割估计。

必须分别登记：

\[
\begin{aligned}
\mathsf{EntropyLedger}
&=\text{信息量恒等式};\\
\mathsf{DynamicClosure}
&=\text{真实微观演化逼近有效方程的定量定理}.
\end{aligned}
\]

二者可以互相解释，但不能相互冒充。

---

# 第十六部　可立即形式化的定理原子

## 16.1 第一层：纯集合与函数

建议新增：

```text
D5/S3/DefinitionEscape/Core/
  TargetResidual.lean
  ResidualJoinLaw.lean
  RedundantDefinition.lean
  CanonicalTargetCompletion.lean
```

核心声明：

```lean
def ResidualPair
    (q : X → Q) (T : X → Y) (x y : X) : Prop :=
  q x = q y ∧ T x ≠ T y

theorem residual_join_iff :
  ResidualPair (fun x => (q x, d x)) T x y ↔
    ResidualPair q T x y ∧ d x = d y
```

并形式化充分性—因子化等价、冗余零增益、目标闭包最小性。

## 16.2 第二层：有限覆盖与计数

```text
D5/S3/DefinitionEscape/Finite/
  ResidualGraph.lean
  DefinitionCover.lean
  BlindKernelCompactness.lean
  EscapeCountMeasure.lean
```

证明：

- 定义集充分当且仅当切集覆盖全部残差；
- 有限对象上盲核为空推出有限定义族存在；
- 边际捕获递减；
- 计数逃逸率单调。

## 16.3 第三层：优化与复杂性

```text
D5/S3/DefinitionEscape/Optimization/
  CaptureSubmodularity.lean
  GreedyCapture.lean
  SetCoverReduction.lean
```

其中复杂性类本身若暂不引入完整计算复杂性基础设施，可以先形式化集合覆盖实例与定义选择实例之间的双向正确归约。

## 16.4 第四层：动态完成

```text
D5/S3/DefinitionEscape/Dynamics/
  FiniteHorizonResidual.lean
  EscapeTime.lean
  PredictiveDefinitionDimension.lean
  CostHorizonEscapeSurface.lean
```

与现有 `PredictionCompletion`、`ItineraryCompletion`、`LocalCertificateMinimality` 对接。

## 16.5 第五层：近似闭包

```text
D5/S3/DefinitionEscape/Approximation/
  MetricResidual.lean
  PredictiveInfluence.lean
  PreparedRetraction.lean
  EmergentSemigroup.lean
  ApproximateCascadeDiagonal.lean
```

先证明纯度量恒等式与三角不等式级联，不直接声称已形式化 Boltzmann 或 WKE 解析估计。

## 16.6 第六层：图证书

```text
D5/S3/DefinitionEscape/Diagrammatics/
  CancellationClass.lean
  CuttingCertificate.lean
  ExcessBudget.lean
  SummationAwareCertificate.lean
```

优先形式化纯组合骨架：切割终止、森林生成、预算可加、类型计数。具体积分估计作为明示前件或外部解析锚接入。

---

# 第十七部　理论状态分级

为避免把定义包装当成数学推进，本文把结论分为三层。

## 17.1 已直接证明或一行可证

- 残差交公式；
- 充分性—因子化等价；
- 冗余定义零增益；
- 盲核不可能性；
- 有限对象紧致性；
- 捕获函数次模性；
- 准备回缩单步缺陷恒等式；
- 半群缺陷恒等式；
- 近似级联三角不等式。

## 17.2 可形式化但需要基础设施

- Set Cover 归约；
- 逃逸谱的测度极限；
- 拓扑紧致性版本；
- 贪心近似界；
- 双参数对角极限；
- 动态逃逸危险率；
- 定义前沿与最小成本存在性。

## 17.3 研究纲领或解析接口

- 从具体 PDE、粒子系统或 SPDE 自动提取高价值定义；
- 对 Yu Deng 论文中的 molecule cutting 和高阶积分估计完成 Lean 形式化；
- 证明重要历史定义普遍对应逃逸谱相变；
- 建立跨领域可比较的创造性指标；
- 证明临界问题中最小定义深度的一般增长律。

---

# 第十八部　邻近理论与新颖性边界

DECT 与下列方向相邻：

- 统计充分性：一个统计量何时决定目标分布或参数；
- Blackwell 比较：实验信息之间的后处理序；
- 抽象解释：抽象域的精度与完备性；
- CEGAR：由伪反例驱动抽象细化；
- 特征选择：用有限特征区分标签；
- 集合覆盖与次模优化：候选定义的组合选择；
- MDL 与 Kolmogorov 复杂性：定义和证明的描述压缩；
- 概念格与分划格：概念细化的序结构；
- 自动定理证明：固定语言中的路径搜索；
- 程序综合：从语法中生成满足规格的表达式；
- 对角化：证明固定目录或生成机制不闭合。

本文不声称上述单个构件首次出现。候选独特贡献是把它们统一到同一个中心对象

\[
\ker q\setminus\ker T
\]

之下，并进一步加入：

1. 目录逃逸、闭包逃逸、区分逃逸与生产性逃逸的分层；
2. 语言盲核与包内搜索不可能性的明确边界；
3. 成本—时域—尺度逃逸曲面；
4. 历史保持提升优先于商化；
5. 抵消优先、全族求和感知的定义证书；
6. Yu Deng 长时间 kinetic/SPDE 方法与观察者完成的统一解释；
7. 原语创造和坐标创造的区分。

是否具有文献意义上的整体首创性，需要后续系统审计；本文当前地位是一套自洽、可检验、可形式化并能生成新问题的理论框架。

---

# 第十九部　核心猜想与研究问题

## 猜想 19.1　谱跃迁原则

长期有生命力的数学定义通常使一族目标的逃逸谱在低预算区间发生显著跃迁，而不只是消灭一个孤立反例。

## 猜想 19.2　最小见证提取原则

若一个高价值定义存在，则常可从最小盲残差见证及其对称闭包中提取其核心不变量。

## 猜想 19.3　自然性筛选原则

在多个同等捕获量的定义中，与问题自同构群自然相容者更可能具有迁移性和较短后续证明。

## 猜想 19.4　临界深度原则

临界尺度问题的最小完备定义深度通常发散；真正可证的是其增长率，而不是固定有限深度。

## 猜想 19.5　抵消先于小量原则

在具有阶乘或指数图计数的展开中，任何成功的低复杂度定义体系都必须先暴露抵消类，再建立逐类小量；单项绝对界通常不是正确坐标。

## 猜想 19.6　可重启长时间原则

长时间有效理论成立的关键，不是一次性全历史控制，而是存在一个可在每个时间块重建的低成本定义态，使局部残差可求和。

## 猜想 19.7　跨目标定义核

真正基础性的定义不是针对单一 \(T\)，而是同时切开目标族 \(\mathcal T\) 的共同残差：

\[
\bigcup_{T\in\mathcal T}\mathcal E(q;T).
\]

## 猜想 19.8　创造性双门槛

一个定义只有同时满足

\[
P_\Gamma(d\mid q,T)>0
\]

和

\[
\operatorname{CompressionGain}(d)>0
\]

时，才构成严格意义的生产性数学创造；前者排除同义改写，后者排除身份编码。

## 问题 19.9　定义发现的可计算边界

对哪些受限语法，存在完备而可计算的定义发现程序？对哪些语法，语言盲核非空性、最小定义成本或目标无关性已经不可判定？

## 问题 19.10　领域间逃逸谱能否比较

不同问题的对象空间、目标和测度不同。是否存在自然归一化，使数论、动力系统、PDE 和程序验证中的定义逃逸谱具有可比较意义？

---

# 第二十部　最终统一

母文把过程数学压缩为

\[
\text{CUT}+\text{FLOW}+\text{ADMIT}+\text{ANCHOR}.
\]

DECT 对这四项给出定义创造版本：

\[
\boxed{
\begin{aligned}
\mathsf{CUT}
&=\text{候选定义对当前纤维的切割};\\
\mathsf{FLOW}
&=\text{残差与定义在动力学、尺度和推理中的传播};\\
\mathsf{ADMIT}
&=\text{目标无关、自然、稳定、低成本与可认证约束};\\
\mathsf{ANCHOR}
&=\text{具体反例、解析估计、构造或形式化证书}.
\end{aligned}
}
\]

其派生对象为

\[
\boxed{
\begin{aligned}
\mathsf{RESIDUAL}
&=\ker q\setminus\ker T,\\
\mathsf{BLIND}
&=\mathsf{RESIDUAL}\cap K_\Gamma,\\
\mathsf{INVENTION}
&=\text{低成本切开 }\mathsf{BLIND}\text{ 的目标无关定义},\\
\mathsf{COMPLETION}
&=\mathsf{RESIDUAL}=\varnothing,\\
\mathsf{APPROXIMATE\ COMPLETION}
&=\text{残差质量或预测直径趋零},\\
\mathsf{CREATIVITY}
&=\mathsf{PRODUCTIVE\ ESCAPE}
+\mathsf{COMPRESSIVE\ RECOVERY}.
\end{aligned}
}
\]

最终判断是：

\[
\boxed{
\text{固定语言中的证明搜索，
只在该语言已经能够分离全部目标逃逸对时才原则上足够。}
}
\]

当语言盲核非空时，继续扩大搜索预算不会跨越表示边界。此时真正的数学工作是：找到一个现有全部定义都看不见、但目标必须区分的对象对；从这对对象的结构差异中提取一个目标无关、低成本、可迁移的新坐标；再证明该坐标不仅切开见证，而且把整类不可控残差转化为局部、可组合、可求和的证明对象。

因此：

\[
\boxed{
\text{定义不是答案的别名；
定义是把答案所需的区分结构变成可推理对象的最小接口。}
}
\]

而结合 Yu Deng 方法论，进一步得到：

\[
\boxed{
\text{最强的新定义往往不是立即忘掉复杂性，
而是先完整保存复杂性从何而来，
再证明其中只有一个低维、低影响、可认证的部分能够逃向未来。}
}
\]

---

# 附录 A　符号表

| 符号 | 含义 |
|---|---|
| \(X\) | 完整对象或状态空间 |
| \(q:X\to Q\) | 当前概念/观察 |
| \(T:X\to Y\) | 目标 |
| \(d:X\to D\) | 候选定义 |
| \(q\vee d\) | 联合概念 |
| \(\ker q\) | 当前概念不可区分关系 |
| \(\mathcal E(q;T)\) | 目标逃逸残差 |
| \(\Gamma\) | 候选定义语言 |
| \(K_\Gamma\) | 语言共同不可区分核 |
| \(\mathcal B_\Gamma(q;T)\) | 语言盲残差 |
| \(C(S)\) | 定义集成本 |
| \(M(S)\) | 剩余逃逸质量 |
| \(\rho_\Gamma(L)\) | 预算逃逸谱 |
| \(P_\Gamma(d\mid q,T)\) | 定义对盲残差的生产性捕获 |
| \(D_T^{\mathrm{pred}}\) | 有限时域预测影响伪距离 |
| \(R_\varepsilon\) | 规范准备回缩 |
| \(\delta_{\varepsilon,t}\) | 准备替换后的观察者缺陷 |

---

# 附录 B　论文锚点

1. Yu Deng, Zaher Hani, **Full derivation of the wave kinetic equation**, arXiv:2104.11204.
2. Yu Deng, Zaher Hani, **Propagation of chaos and the higher order statistics in the wave kinetic theory**, arXiv:2110.04565.
3. Yu Deng, Zaher Hani, **Derivation of the wave kinetic equation: full range of scaling laws**, arXiv:2301.07063.
4. Yu Deng, Zaher Hani, **Long time justification of wave turbulence theory**, arXiv:2311.10082.
5. Yu Deng, Zaher Hani, Xiao Ma, **Long time derivation of the Boltzmann equation from hard sphere dynamics**, arXiv:2408.07818.
6. Yu Deng, Zaher Hani, Xiao Ma, **Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory**, arXiv:2503.01800.
7. Yu Deng, Hao Shen, **The four-dimensional Anderson model: a case study for critical SPDEs**, arXiv:2607.10105.

---

# 附录 C　仓库锚点

本文直接承接或计划对接的仓库模块：

```text
D5/S0/Diagonal/EscapeCount.lean
D5/S0/Diagonal/Naturality/RelativeDiagonalEscape.lean
D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.lean
D5/S3/ObserverMemory/DiagonalEscape/DiagonalCompletionEscape.lean
D5/S3/ConceptDynamics/ConceptJoinUniversal.lean
D5/S3/ConceptDynamics/Refinement/InductiveSufficiency.lean
D5/S3/ConceptDynamics/Completion/TargetClosureOperator.lean
D5/S3/ObserverMemory/Refinement/PredictionCompletion.lean
D5/S3/ObserverMemory/Refinement/CascadeCompletion.lean
D5/S3/ObserverMemory/Fusion/IndependentProductCompletion.lean
D5/S3/Observer/Naturality/ApproximateSemiconjugacyError.lean
D5/S3/Observer/Naturality/IteratedDefectAccumulation.lean
D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality.lean
```

---

# 追加账本

## v1.0 — 2026-08-23

首次存入：

- 目标逃逸残差；
- 残差交公式；
- 语言盲核；
- 原语创造/坐标创造二分；
- 定义逃逸谱；
- Set Cover 归约与次模捕获；
- 四级对角逃逸；
- 动态预测逃逸与成本—时域曲面；
- 准备回缩与极限半群；
- history-preserving lift before quotient；
- Yu Deng 长时间 kinetic、Boltzmann、Hilbert VI 与临界 SPDE 方法论统一；
- 全族求和感知证书；
- Lean 形式化路线。

后续增订必须从本节之后继续追加。

---

# 第二十一部　递归定义科学论：纯定义增订
## Recursive Definition Science（RDS）

> **增订状态**：v1.1，2026-08-23。  
> **写入方式**：本增订只追加于 v1.0 之后，不修改前文任何字句。  
> **构造纪律**：本增订不设置额外起始断言，只引入类型、映射、关系、纤维、图、更新算子、反射算子与极限对象；等式来自定义展开，其他结论均保留所需条件。

本增订研究一个高阶问题：科学是否也能被表示为定义活动，以及“定义定义定义”如何避免退化为同义循环。

外延上，科学对象、定律、实验、模型、证明、评价和修订都可以编码为不同载体上的映射或谓词，一个有限科学流程因此可以压成一个复合定义。内涵上，单一复合函数无法保存来源、依赖、适用域、证书、失败条件与修订路径。故更准确的形式是：

\[
\boxed{
\mathsf{Science}
=
\text{能够把自身的定义生成与修订规则再次变成对象的动态有类型定义图。}
}
\]

科学定义对象；科学方法定义如何产生与修订对象定义；科学哲学在方法空间上继续执行定义逃逸完备化；元哲学再把哲学方法变成对象。该递归采用版本化、有类型、受守卫的反射塔，而不是同层无类型自包含。

---

## 21.1 定义宇宙

给定类型 \(X\)，定义

\[
\boxed{
\operatorname{Def}(X)
:=
\sum_{D:\mathcal U}(X\to D).
}
\]

元素写作 \(\mathbf d=(D,d)\)，其中 \(d:X\to D\)。它同时覆盖命名、分类、性质、坐标、统计量、不变量、规范代表和未来轨迹。

定义核：

\[
\ker\mathbf d
:=
\{(x,y):d(x)=d(y)\}.
\]

定义实现像：

\[
\operatorname{Im}(\mathbf d)
:=
\{z:D\mid\exists x,\ d(x)=z\}.
\]

定义概念等价：

\[
\mathbf d\simeq_X\mathbf e
\quad\Longleftrightarrow\quad
\ker\mathbf d=\ker\mathbf e.
\]

定义细化：

\[
\mathbf d\preceq_X\mathbf e
\quad\Longleftrightarrow\quad
\ker\mathbf e\subseteq\ker\mathbf d.
\]

定义元定义宇宙：

\[
\operatorname{MetaDef}(X)
:=
\operatorname{Def}(\operatorname{Def}(X)).
\]

定义生成器：

\[
\operatorname{Generator}(X;S)
:=
S\to\operatorname{Def}(X).
\]

定义变换器：

\[
\operatorname{Transformer}(X,Y)
:=
\operatorname{Def}(X)\to\operatorname{Def}(Y).
\]

给定定义状态与残差状态，定义研究方法：

\[
\boxed{
\operatorname{Method}(X)
:=
\operatorname{DState}(X)
\times
\operatorname{Residual}(X)
\to
\operatorname{Def}(X).
}
\]

所以“方法”不是对象层的另一个性质，而是定义下一项定义的高阶映射。

---

# 第二十二部　外延定义与内涵定义

## 22.1 外延定义

定义

\[
\operatorname{ExtDef}(X)
:=
\sum_D(X\to D).
\]

它只保留定义函数。

## 22.2 定义代码与解释

定义语法类型 \(\operatorname{Code}(X)\) 和解释器：

\[
\llbracket\cdot\rrbracket_X:
\operatorname{Code}(X)	o\operatorname{ExtDef}(X).
\]

## 22.3 来源、依赖与作用域

定义来源标签类型：

\[
\operatorname{Origin}
:=
\{\mathsf{Notation},\mathsf{Construction},\mathsf{Deduction},
\mathsf{Measurement},\mathsf{Calibration},\mathsf{ModelChoice},
\mathsf{Approximation},\mathsf{Convention},\mathsf{Intervention},
\mathsf{Imported}\}.
\]

对代码 \(c\)，定义直接依赖 \(\operatorname{dep}(c)\)、传递闭包 \(\operatorname{Dep}^*(c)\)、适用域 \(\operatorname{Scope}(c)\subseteq X\)、成本 \(\operatorname{Cost}(c)\) 与证书 \(\operatorname{Certificate}(c)\)。

## 22.4 内涵定义

定义

\[
\boxed{
\operatorname{IntDef}(X)
:=
\sum_{c:\operatorname{Code}(X)}
(\operatorname{Origin}(c),
\operatorname{Dep}^*(c),
\operatorname{Scope}(c),
\llbracket c\rrbracket_X,
\operatorname{Cost}(c),
\operatorname{Certificate}(c)).
}
\]

定义外延投影：

\[
\operatorname{ext}:
\operatorname{IntDef}(X)	o\operatorname{ExtDef}(X).
\]

若存在 \(c_1\neq c_2\) 而 \(\llbracket c_1\rrbracket_X=\llbracket c_2\rrbracket_X\)，则外延投影在该对上非单射。由此，直接复制目标与独立构造出同一函数，不能只靠函数图区分；科学审计必须保留定义来源图。

---

# 第二十三部　科学状态作为定义图

## 23.1 有类型定义图

定义

\[
\boxed{
\mathcal G=(V,E,\tau,\sigma,\omega).
}
\]

其中 \(V\) 为节点，\(E\subseteq V\times V\) 为依赖边，\(\tau(v)\) 为节点类型，\(\sigma(v)\) 为内涵定义，\(\omega(v)\) 为版本与状态账本。

对目标节点集 \(A\subseteq V\)，定义依赖切片：

\[
\operatorname{Slice}_{\mathcal G}(A)
:=
\{u:\exists v\in A,\ u\leadsto v\}.
\]

对共同输入 \(X\) 的节点集 \(U\)，定义联合读数：

\[
q_U(x):=(\sigma(u)(x))_{u\in U},
\qquad
R_U:=\ker q_U=\bigcap_{u\in U}\ker\sigma(u).
\]

定义科学状态：

\[
\boxed{
\operatorname{SciState}(X)
:=
(\mathcal G,U,R_U,\mathcal L,\mathcal R),
}
\]

其中 \(\mathcal L\) 是来源与版本账本，\(\mathcal R\) 是未决残差账本。

科学状态由此不是一袋最终句子，而是一张正在演化的区分网络及其尚未闭合的纤维。

---

# 第二十四部　科学构件的不同载体定义

给定世界过程类型 \(W\)，定义对象读数 \(q:W\to Q\)，相对于 \(q\) 的对象为纤维类

\[
[w]_q:=\{w':q(w')=q(w)\}.
\]

定义状态提取 \(s:W\times T\to X\)，轨迹类型 \(\operatorname{Traj}(X,T):=T\to X\)。

定义定律代码为轨迹谓词：

\[
L:\operatorname{Traj}(X,T)\to\mathrm{Prop},
\]

以及允许轨迹子类型：

\[
\operatorname{LawTraj}(L)
:=
\{\gamma:\operatorname{Traj}(X,T)\mid L(\gamma)\}.
\]

“定律可编码为定义”的精确含义只是：它定义模型内哪些轨迹可被准入；它并不通过这一编码自动给出现实过程与该子类型的相符证书。

定义操作类型 \(I\)、记录接口

\[
A:W\times I\to R,
\]

模型参数类型 \(\Theta\) 与预测接口

\[
P:\Theta\times I\to R,
\]

比较器

\[
C:R\times R\to\Delta.
\]

定义实验：

\[
\mathsf{Experiment}:=(I,R,A,\pi),
\]

其中 \(\pi\) 是采样或干预计划。

观察结果 \(r\) 定义模型纤维：

\[
\Theta_r:=\{\theta:C(P(\theta,i),r)=0\}.
\]

定义假设为模型谓词 \(H:\Theta\to\mathrm{Prop}\)，定义证明对象为命题类型的项，定义计算证书为可重放轨迹与检查器的依赖和，定义论文为局部定义图、主张、证据、依赖与作用域的五元组。

由此，对象、定律、模型、仪器、实验、证明和论文都可被编码成定义，但它们作用在不同输入类型，并携带不同来源标签，不应被压平为同一种认识论事件。

---

# 第二十五部　有限科学流程的压平与信息丢失

定义一个有限可执行流程：

\[
\mathcal W=(X_0\xrightarrow{f_1}X_1\xrightarrow{f_2}\cdots\xrightarrow{f_n}X_n).
\]

定义复合：

\[
\operatorname{Comp}(\mathcal W):=f_n\circ\cdots\circ f_1.
\]

对共同输入上的有限定义节点，定义乘积压平：

\[
\operatorname{Flat}_{\times}(\mathcal G)(x)
:=(\sigma(v)(x))_{v\in V_X}.
\]

于是

\[
\ker\operatorname{Flat}_{\times}(\mathcal G)
=
\bigcap_{v\in V_X}\ker\sigma(v).
\]

若后续类型依赖前序值，则定义依赖和压平：

\[
\operatorname{Flat}_{\Sigma}(\mathcal G)
:=
\sum_{z_1:D_1}\sum_{z_2:D_2(z_1)}\cdots
\sum_{z_n:D_n(z_{<n})}\operatorname{Compat}(z_1,\ldots,z_n).
\]

因此有限科学工作流在外延上可以压成一个复合或依赖定义。

定义遗忘映射：

\[
\operatorname{ForgetGraph}:
\operatorname{SciGraph}\to\operatorname{ExtDef}.
\]

若两张不同图有相同遗忘像，它们的最终区分相同，但来源、依赖、次序、成本与修订路径仍可不同。故：

\[
\boxed{
\begin{aligned}
\text{有限科学结果的外延}&=\text{一个复合定义};\\
\text{科学研究的内涵结构}&=\text{不能由复合定义唯一恢复的动态定义图}.
\end{aligned}
}
\]

---

# 第二十六部　对象层、方法层与哲学层残差

给定当前联合读数 \(q_U:X\to Q_U\) 和目标 \(T:X\to Y\)，定义科学问题残差：

\[
\mathcal E_U(T):=\{(x,y):q_U(x)=q_U(y),\ T(x)\neq T(y)\}.
\]

若 \(X=\Theta\) 是模型空间，目标是未来预测，则它记录当前模型表示相同、但未来不同的模型对。

若 \(X=\operatorname{Method}(Z)\)，定义方法残差：

\[
\boxed{
\mathcal E_{\mathrm{method}}(q;T)
:=
\{(M_1,M_2):q(M_1)=q(M_2),\ T(M_1)\neq T(M_2)\}.
}
\]

若 \(X\) 是哲学方法空间，同一公式定义哲学系统把哪些实际表现不同的方法误归为同类。对象科学、科学方法论、科学哲学与元哲学因而共享同一残差构造，只改变输入类型。

---

# 第二十七部　研究方法作为定义生成器

定义状态：

\[
\operatorname{DState}(X):=(\Gamma,\mathcal G,q_\Gamma,\mathcal L).
\]

定义残差状态：

\[
\operatorname{RState}(X,T)
:=(\mathcal E_\Gamma(T),\nu,\operatorname{Classes},\operatorname{Witnesses}).
\]

定义方法：

\[
\boxed{
M_X:
\operatorname{DState}(X)
\times
\operatorname{RState}(X,T)
\to
\operatorname{IntDef}(X).
}
\]

其输出是带来源、依赖、适用域和证书的新定义节点。定义更新：

\[
\Gamma_{n+1}:=\Gamma_n\cup\{d_n\},
\qquad
d_n:=M_X(S_n,E_n),
\]

\[
\mathcal G_{n+1}:=\operatorname{Insert}(\mathcal G_n,d_n),
\qquad
E_{n+1}=E_n\cap\ker d_n.
\]

定义方法轨道：

\[
\operatorname{Orbit}(M,S_0):=(S_0,S_1,S_2,\ldots).
\]

科学研究过程由此成为定义状态在残差驱动生成器下的轨道。

---

# 第二十八部　哲学作为方法空间上的 DECT

定义方法空间

\[
\mathfrak M_X:=\operatorname{Method}(X).
\]

定义当前哲学读数 \(q_{\mathfrak M}:\mathfrak M_X\to Q_{\mathfrak M}\) 与方法目标 \(T_{\mathfrak M}:\mathfrak M_X\to Y_{\mathfrak M}\)。

定义哲学残差：

\[
\boxed{
\mathcal E_{\mathfrak M}
:=
\ker q_{\mathfrak M}\setminus\ker T_{\mathfrak M}.
}
\]

一个哲学定义是

\[
d_{\mathfrak M}:\mathfrak M_X\to D.
\]

加入后：

\[
\mathcal E'_{\mathfrak M}
=
\mathcal E_{\mathfrak M}\cap\ker d_{\mathfrak M}.
\]

定义哲学方法：

\[
M_{\mathfrak M}:
\operatorname{DState}(\mathfrak M_X)
\times
\operatorname{RState}(\mathfrak M_X,T_{\mathfrak M})
\to
\operatorname{IntDef}(\mathfrak M_X).
\]

于是哲学不是在对象科学之外增加另一种逻辑，而是在研究方法空间上重复相同的定义逃逸完备化过程。

---

# 第二十九部　元哲学与层级

定义反射载体算子：

\[
\boxed{
\mathfrak R(X):=\operatorname{Method}(X).
}
\]

从对象层 \(X_0\) 开始，递归定义：

\[
X_{n+1}:=\mathfrak R(X_n).
\]

每层定义

\[
q_n:X_n\to Q_n,
\qquad
T_n:X_n\to Y_n,
\qquad
E_n:=\ker q_n\setminus\ker T_n,
\]

以及

\[
M_n:
\operatorname{DState}(X_n)
\times
\operatorname{RState}(X_n,T_n)
\to
\operatorname{IntDef}(X_n).
\]

\(X_0\) 是对象空间，\(X_1\) 是研究对象的方法空间，\(X_2\) 是研究方法的方法空间。元哲学被定义为 \(X_2\) 上的 DECT，更高有限层同理。构造中没有指定最高层。

---

# 第三十部　守卫自反

对版本 \(S_n\)，定义代码 \(\ulcorner S_n\urcorner:\operatorname{CodeSys}\)。定义反射更新：

\[
\boxed{
S_{n+1}:=\Phi(\ulcorner S_n\urcorner,E_n).
}
\]

定义版本先后关系 \(\prec\)。一个自反定义为守卫的，当所有自引用边满足

\[
S_i\text{ 引用 }S_j\Longrightarrow j<i.
\]

定义守卫反射塔：

\[
S_0\xrightarrow{\Phi}S_1\xrightarrow{\Phi}S_2\xrightarrow{\Phi}\cdots.
\]

该结构与同层无类型表达 \(S=S(S)\) 不同：新版本只把已完成旧版本的代码、记录与残差纳入对象。

定义反射深度：

\[
\operatorname{RefDepth}(S)
:=
\sup\{n:S\text{ 能编码并评价前 }n\text{ 层定义过程}\}.
\]

定义旧版本节点集合 \(N(S_n)\) 与下一版本描述 \(\operatorname{Desc}_{n+1}\)。未覆盖节点为

\[
\operatorname{Undesc}_{n+1}
:=N(S_n)\setminus\operatorname{Dom}(\operatorname{Desc}_{n+1}).
\]

有限情况下定义自描述覆盖率：

\[
\operatorname{SelfCov}_{n+1}
:=1-
\frac{|\operatorname{Undesc}_{n+1}|}{|N(S_n)|}.
\]

---

# 第三十一部　开放反射完成

定义保持映射 \(i_n:S_n\to S_{n+1}\) 及其相容性。定义开放反射完成：

\[
\boxed{
S_\omega:=\varinjlim_{n<\omega}S_n.
}
\]

元素由某个有限层对象及其以后层的相容像表示。

定义有限可反射性：任意有限定义子图最终来自某个 \(S_n\)。

定义稳定层：

\[
\operatorname{StableAt}(N)
\quad\Longleftrightarrow\quad
S_{N+1}\simeq S_N.
\]

定义局部自反、全局封闭与开放反射：

- 局部自反：每个有限子图最终被高层编码；
- 全局封闭：存在单层同时编码全部层及其编码操作；
- 开放反射：局部自反成立，而构造不指定全局封闭层。

RDS 以开放反射塔为对象，因此不需要一次性定义一个“最终知道自己全部定义”的有限系统。

---

# 第三十二部　反射残差与元盲核

对版本 \(S_n\)，定义元目标

\[
T_n^{\mathrm{meta}}:N(S_n)\to Y_n^{\mathrm{meta}},
\]

以及下一版本对旧节点的自描述读数

\[
q_{n+1}^{\mathrm{self}}:N(S_n)\to Q_{n+1}^{\mathrm{self}}.
\]

定义反射残差：

\[
\boxed{
E_{n+1}^{\mathrm{reflect}}
:=
\ker q_{n+1}^{\mathrm{self}}
\setminus
\ker T_n^{\mathrm{meta}}.
}
\]

给定元定义语言 \(\Gamma_{n+1}^{\mathrm{meta}}\)，定义反射盲核：

\[
B_{n+1}^{\mathrm{reflect}}
:=
E_{n+1}^{\mathrm{reflect}}
\cap
\bigcap_{d\in\Gamma_{n+1}^{\mathrm{meta}}}\ker d.
\]

定义预算反射逃逸率：

\[
\rho_{n+1}^{\mathrm{reflect}}(L)
:=
\inf_{C(A)\le L}
\frac{\nu_n(E_{n+1}^{\mathrm{reflect}}\cap\bigcap_{d\in A}\ker d)}
{\nu_n(E_{n+1}^{\mathrm{reflect}})}.
\]

“系统对自己了解多少”因而被表示为预算依赖的元逃逸谱，而不是二元自知宣言。

---

# 第三十三部　记录接口与现实阻力

本节只定义知识系统与输入过程之间的接口。

定义输入类型 \(W\)、操作类型 \(I\)、记录类型 \(R\)，记录接口

\[
A:W\times I\to R,
\]

理论预测接口

\[
P:S\times I\to R,
\]

比较器

\[
d_R:R\times R\to\Delta.
\]

定义记录残差：

\[
\delta(S,w,i):=d_R(P(S,i),A(w,i)).
\]

定义从 \(S\) 出发的允许重定义族 \(\operatorname{Redef}(S)\)。它可以要求保持历史记录、来源账本、既有输出或指定操作接口。

定义持久操作残差：

\[
\operatorname{PersistentOps}(S,w)
:=
\{i:\forall S'\in\operatorname{Redef}(S),\ \delta(S',w,i)\neq0\}.
\]

定义现实阻力：

\[
\boxed{
\operatorname{Resistance}(S,w)
:=
\operatorname{PersistentOps}(S,w).
}
\]

这不是把某个形而上断言写入系统，而是把“在指定允许重定义族下仍不能消去的记录不匹配”命名为阻力。改变操作、记录接口、比较器或允许重定义族，阻力也随之改变；该相对性被写入参数。

---

# 第三十四部　事实与客观性

定义观察协议索引范畴 \(\mathcal O\)。每个对象 \(o\) 有读数 \(q_o:X\to Q_o\)，每个态射 \(f:o\to o'\) 有翻译

\[
Q(f):Q_o\to Q_{o'}.
\]

定义相容读数条件：

\[
Q(f)\circ q_o=q_{o'}.
\]

定义相容记录族 \(r=(r_o)\) 为满足

\[
Q(f)(r_o)=r_{o'}
\]

的族。定义相对于协议系统的事实：

\[
\boxed{
\operatorname{Fact}_{\mathcal O}
:=
\varprojlim_{o\in\mathcal O}Q_o.
}
\]

给定性质读数 \(P_o:Q_o\to Z\)，定义客观性为自然性：

\[
\boxed{
\operatorname{Objective}_{\mathcal O}(P)
\quad\Longleftrightarrow\quad
P_{o'}\circ Q(f)=P_o
\text{ 对所有 }f.
}
\]

若只近似交换，定义客观性缺陷为所有协议翻译上的最大交换缺陷。客观性由此不是定义缺席，而是跨合法定义翻译的相容性。

---

# 第三十五部　真理记录作为范围化交换

定义测试操作域 \(J\subseteq I\)。对系统状态 \(S\) 与输入 \(w\)，定义精确相符：

\[
\boxed{
S\models_J w
\quad\Longleftrightarrow\quad
\forall i\in J,\ P(S,i)=A(w,i).
}
\]

若记录空间带距离，定义近似相符：

\[
S\models_{J,\varepsilon}w
\quad\Longleftrightarrow\quad
\sup_{i\in J}d_R(P(S,i),A(w,i))\le\varepsilon.
\]

定义声明范围

\[
\operatorname{Scope}(S):=(J,\varepsilon,\mathcal C),
\]

其中 \(\mathcal C\) 是条件集合。定义真理记录：

\[
\operatorname{TruthRecord}(S,w)
:=
(J,\varepsilon,\mathcal C,\operatorname{Fit},
\operatorname{Version},\operatorname{Evidence}).
\]

该定义记录理论预测通道与记录通道在什么操作域、条件、误差与版本下交换。

---

# 第三十六部　因果作为干预逃逸

定义观测接口 \(O:X\to R_O\)，干预索引 \(A\)，干预映射

\[
\operatorname{do}:A\times X\to X.
\]

定义干预响应目标：

\[
T^{\operatorname{do}}(x)
:=(T(\operatorname{do}(a,x)))_{a\in A}.
\]

定义因果逃逸：

\[
\boxed{
\mathcal E_{\mathrm{causal}}(O;T,\operatorname{do})
:=
\{(x,y):O(x)=O(y),\ T^{\operatorname{do}}(x)\neq T^{\operatorname{do}}(y)\}.
}
\]

候选因果变量 \(c:X\to C\) 加入后满足普通残差交公式：

\[
\mathcal E_{\mathrm{causal}}(O\vee c;T,\operatorname{do})
=
\mathcal E_{\mathrm{causal}}(O;T,\operatorname{do})\cap\ker c.
\]

定义因果定义维数：

\[
\operatorname{CausalDefDim}(T\mid O,\operatorname{do})
:=
\inf\{C(S):\mathcal E_{\mathrm{causal}}(O\vee S;T,\operatorname{do})=\varnothing\}.
\]

---

# 第三十七部　解释作为多目标压缩

给定目标族 \(\mathcal T=\{T_j\}_{j\in J}\)，定义共同残差：

\[
\mathcal E(q;\mathcal T)
:=
\bigcup_{j\in J}\mathcal E(q;T_j).
\]

定义解释记录：

\[
\operatorname{Explain}(d)
:=
(\operatorname{Capture},\operatorname{Compression},
\operatorname{Transfer},\operatorname{Counterfactual},
\operatorname{MechanismGraph}).
\]

定义多目标捕获：

\[
\operatorname{ExplCapture}(d)
:=
\sum_jw_j\nu_j(\mathcal E(q;T_j)\cap(\ker d)^c).
\]

定义解释压缩：

\[
\operatorname{ExplCompression}(d)
:=
\operatorname{DescriptionCost}(\mathcal T\mid q)
-
\left[C(d)+\operatorname{DescriptionCost}(\mathcal T\mid q\vee d)\right].
\]

给定干预族，反事实闭合由

\[
\ker(q\vee d)\subseteq\ker T^{\operatorname{do}}
\]

定义。一个定义不因重新命名结果就自动成为解释；它的解释记录还需说明多目标捕获、压缩、迁移与干预覆盖。

---

# 第三十八部　自封闭与开放修订

定义修订算子

\[
U:S\times E\to S.
\]

定义系统对残差 \(e\) 静默，当

\[
U(S,e)\simeq S.
\]

定义生产性修订，当更新后原目标残差质量下降。

定义表面消残：只修改比较器、命名或作用域，使新记号下残差为零，而原预测—记录差异未缩小。

定义真正解决：更新后原比较接口下的残差缩小，且历史记录未被删除。

定义自封闭：

\[
\operatorname{SelfSealed}(S)
\quad\Longleftrightarrow\quad
\forall e,\ U(S,e)\simeq S
\ \vee\ 
\operatorname{RelabelErase}(S,e).
\]

定义开放修订：

\[
\operatorname{RevisionOpen}(S)
\quad\Longleftrightarrow\quad
\exists e,\ U(S,e)\not\simeq S
\ \wedge\ 
\operatorname{Resolve}(S,e).
\]

定义科学定义系统结构：

\[
\operatorname{SciDefSys}(S)
:=
(\operatorname{ProvenanceComplete},
\operatorname{RecordPreserving},
\operatorname{RevisionOpen},
\operatorname{CertificateCarrying}).
\]

这只是一个结构类型；具体制度是否具有这些字段，需要提供对应数据和证书。

---

# 第三十九部　科学的递归定义动力学

定义科学系统：

\[
\boxed{
\mathsf{Science}(W)
:=
(\mathsf{Define},\mathsf{Observe},\mathsf{Predict},
\mathsf{Compare},\mathsf{Revise},\mathsf{Reflect}).
}
\]

其中：

\[
\mathsf{Define}:
\operatorname{DState}(W)\times\operatorname{RState}(W,T)
\to\operatorname{IntDef}(W),
\]

\[
\mathsf{Observe}:W\times I\to R,
\quad
\mathsf{Predict}:S\times I\to R,
\]

\[
\mathsf{Compare}:R\times R\to\Delta,
\quad
\mathsf{Revise}:S\times E\to S,
\quad
\mathsf{Reflect}:S_n\to S_{n+1}.
\]

定义单步更新：

\[
\boxed{
S_{n+1}
:=
\mathsf{Reflect}
\left(
\mathsf{Revise}
\left(S_n,
\mathsf{Compare}
(\mathsf{Predict}(S_n,-),\mathsf{Observe}(w,-))
\right)
\right).
}
\]

定义六种变化分量：

\[
\begin{aligned}
\Delta\mathsf{CUT}&=\text{对象和变量定义变化},\\
\Delta\mathsf{ADMIT}&=\text{模型或轨迹准入变化},\\
\Delta\mathsf{FLOW}&=\text{动力学定义变化},\\
\Delta\mathsf{ANCHOR}&=\text{操作、仪器和记录接口变化},\\
\Delta\mathsf{CERTIFY}&=\text{证明与误差证书变化},\\
\Delta\mathsf{REFLECT}&=\text{方法和元方法定义变化}.
\end{aligned}
\]

定义科学哲学：

\[
\mathsf{Philosophy}(S)
:=
\mathsf{Reflect}
(\mathsf{Define},\mathsf{Observe},\mathsf{Predict},
\mathsf{Compare},\mathsf{Revise}).
\]

定义元哲学：

\[
\mathsf{MetaPhilosophy}(S)
:=
\mathsf{Reflect}(\mathsf{Philosophy}(S)).
\]

---

# 第四十部　多层定义创造

对象层定义 \(d_0:X_0\to D_0\) 的生产性由对象残差捕获衡量。方法层定义

\[
d_1:X_1=\operatorname{Method}(X_0)\to D_1
\]

区分当前哲学误归为同类、但实际表现不同的方法。第 \(n\) 层定义

\[
d_n:X_n\to D_n
\]

的生产性为

\[
P_n(d_n)
:=
\nu_n(B_{\Gamma_n}(q_n;T_n)\cap(\ker d_n)^c).
\]

定义跨层定义族 \(\mathbf d=(d_0,\ldots,d_n)\)。给定层间运输 \(F_i:X_i\to X_{i+1}\) 与值域运输 \(G_i\)，定义自然性缺陷：

\[
\operatorname{NatDefect}(\mathbf d)
:=
\sum_i d_{D_{i+1}}(d_{i+1}F_i,G_id_i).
\]

定义局部修订、类型扩展、方法扩展和反射扩展。一个“科学革命”可被记录为：不能由当前概念等价下的有限重命名、冗余节点插入或局部因子重排得到的类型或生成器扩展。

---

# 第四十一部　Yu Deng 方法作为元定义生成器

定义证明病理类型：

\[
\operatorname{Pathology}
:=
(\mathsf{FactorizationFailure},
\mathsf{HistoryEntanglement},
\mathsf{CombinatorialExplosion},
\mathsf{CancellationHidden},
\mathsf{ScaleDivergence},
\mathsf{LongTimeAccumulation}).
\]

定义结构类型：

\[
\operatorname{StructureDef}
:=
(\mathsf{Cumulant},\mathsf{ConnectedGraph},\mathsf{Molecule},
\mathsf{CancellationClass},\mathsf{CuttingForest},\mathsf{HeppTree},
\mathsf{PreparedState},\mathsf{AdaptiveDepth}).
\]

定义 Deng 型方法映射：

\[
\boxed{
M_{\mathrm{Deng}}:
\operatorname{Pathology}
\times\operatorname{ScaleData}
\times\operatorname{TargetObserver}
\to\operatorname{StructureDef}.
}
\]

典型对应为：因子化失败映向 cumulant，历史纠缠映向 molecule，组合爆炸映向 cutting forest，隐藏抵消映向 cancellation class，尺度发散映向 Hepp tree 与 adaptive depth，长时间累积映向 prepared state 与 restart rule。

这不是唯一性声明，而是把 Yu Deng 系列工作的共同创造模式提升成可研究的方法空间。对该方法自身应用 DECT，可继续询问：哪些证明病理尚未被现有结构字典区分，哪些新图对象只是旧对象的坐标压缩，哪些是方法语言的原语扩展，哪些能跨 kinetic、PDE、SPDE 与组合证明迁移。

---

# 第四十二部　定义包与方法包的双层盲核

固定定义候选 \(\Gamma\) 后，定义选择是残差覆盖。固定方法候选集 \(\mathcal M\) 后，定义每个方法的生产域：

\[
C_M:=\{p:M\text{ 在问题 }p\text{ 上生成生产性定义}\}.
\]

定义方法共同核：

\[
K_{\mathcal M}:=\bigcap_{M\in\mathcal M}\ker M.
\]

若两个残差状态落在 \(K_{\mathcal M}\) 中，却需要不同新定义才能解决，则现有方法搜索也无法区分它们。

定义方法原语创造：新方法 \(M'\) 满足

\[
K_{\mathcal M}\nsubseteq\ker M'
\]

且切开方法目标盲残差。

由此形成两重边界：

\[
\boxed{
\begin{aligned}
\text{定义包搜索}&:\Gamma\text{ 是否已有所需切割};\\
\text{方法包搜索}&:\mathcal M\text{ 是否已有产生该切割的生成器}.
\end{aligned}
}
\]

若第二层盲核非空，需要发明新的定义发现方法，而不仅是新的对象定义。

---

# 第四十三部　停止、继续与重新打开

定义目标闭合：

\[
\operatorname{Closed}(S,T)
\Longleftrightarrow
\mathcal E_S(T)=\varnothing.
\]

定义近似闭合：

\[
\operatorname{Closed}_\varepsilon(S,T)
\Longleftrightarrow
\Delta(q_S;T)\le\varepsilon.
\]

定义预算停止：

\[
\operatorname{Stop}_{L}(S)
\Longleftrightarrow
\sup_{c(d)\le L}
\frac{\operatorname{Gain}(d)}{c(d)}\le\lambda.
\]

定义方法停止：\(M(S,E_S)=\mathsf{NoProposal}\)。

若对象域、目标、精度、操作族或定义语言改变并产生新残差，定义系统重新打开。定义局部完成是固定 \((X,T,I,\varepsilon)\) 下闭合；定义开放世界序列为这些参数中至少一个持续变化的序列。一个系统可以在每个固定阶段完成，却在扩张序列中反复重新打开。

---

# 第四十四部　稳定对象的逆极限定义

定义扩张操作族：

\[
\mathcal A_0\subseteq\mathcal A_1\subseteq\cdots.
\]

定义操作等价：

\[
x\sim_ny
\Longleftrightarrow
\forall a\in\mathcal A_n,\ O(a,x)=O(a,y).
\]

于是 \(\sim_{n+1}\subseteq\sim_n\)。定义阶段对象

\[
X_n^{\mathrm{obs}}:=X/\!\sim_n
\]

及限制映射 \(r_{n+1,n}:X_{n+1}^{\mathrm{obs}}\to X_n^{\mathrm{obs}}\)。定义稳定科学对象空间：

\[
\boxed{
X_\infty^{\mathrm{obs}}
:=
\varprojlim_nX_n^{\mathrm{obs}}.
}
\]

元素是在不断增强的合法观察定义下保持相容的对象族。科学对象因此不被绑定于单个观察切割，而被定义为一条相容逆极限轨迹。

---

# 第四十五部　形式化接口草案

```lean
universe u v w

namespace D5.S3.DefinitionEscape.RecursiveScience

structure ExtDef (X : Type u) where
  Codomain : Type v
  read : X → Codomain

def ExtDef.Kernel {X : Type u} (d : ExtDef X) : Setoid X :=
  Setoid.ker d.read

inductive Origin where
  | notation | construction | deduction | measurement
  | calibration | modelChoice | approximation
  | convention | intervention | imported

structure IntDef (X : Type u) where
  Code : Type v
  semantics : Code → ExtDef X
  origin : Code → Origin
  dependencies : Code → Set Code
  scope : Code → Set X
  cost : Code → ℝ≥0∞

structure DefinitionGraph where
  Node : Type u
  Edge : Node → Node → Prop
  carrier : Node → Type v
  definition : (n : Node) → ExtDef (carrier n)

structure DefinitionState (X : Type u) where
  graph : DefinitionGraph
  observation : ExtDef X

structure ResidualState (X : Type u) (T : ExtDef X) where
  current : DefinitionState X
  pair : X → X → Prop := fun x y =>
    current.observation.read x = current.observation.read y ∧
    T.read x ≠ T.read y

abbrev DefinitionMethod (X : Type u) (T : ExtDef X) :=
  DefinitionState X → ResidualState X T → IntDef X

structure RecordInterface (W : Type u) where
  Query : Type v
  Record : Type w
  observe : W → Query → Record

structure ScientificSystem (W : Type u) where
  State : Type v
  interface : RecordInterface W
  predict : State → interface.Query → interface.Record
  compare : interface.Record → interface.Record → Type w
  revise : State → Type w → State
  encode : State → Type w
  reflect : State → State

end D5.S3.DefinitionEscape.RecursiveScience
```

建议路径：

```text
D5/S3/DefinitionEscape/RecursiveScience/
  ExtensionalDefinition.lean
  IntensionalDefinition.lean
  TypedDefinitionGraph.lean
  WorkflowFlattening.lean
  DefinitionMethod.lean
  MethodResidual.lean
  GuardedReflection.lean
  ReflectionTower.lean
  ReflectionEscapeRate.lean
  RecordResistance.lean
  ObjectiveNaturality.lean
  InterventionResidual.lean
  ScientificSystem.lean
```

优先形式化的定义展开包括：联合定义核等于核交；有限定义图乘积压平的核等于节点核交；外延投影非单射的显式双代码见证；方法层残差交公式；守卫引用无同层回边；反射塔有限前缀嵌入；观察协议相容族的逆极限；因果逃逸作为干预轨迹目标的普通残差特例；自封闭与开放修订的有限模型；持久残差关于允许重定义族扩大的反单调性。

---

# 第四十六部　纯定义统一式

\[
\mathsf{OBJECT}:=X/\ker q.
\]

\[
\mathsf{PROBLEM}:=\ker q\setminus\ker T.
\]

\[
\mathsf{DISCOVERY}(d)
:=
\mathsf{PROBLEM}\cap(\ker d)^c.
\]

\[
\mathsf{METHOD}
:=
(\mathsf{STATE},\mathsf{PROBLEM})	o\mathsf{DEFINITION}.
\]

\[
\mathsf{THEORY}
:=
(\mathsf{OBJECT},\mathsf{LAW},\mathsf{PREDICTION},\mathsf{SCOPE}).
\]

\[
\mathsf{EXPERIMENT}
:=
(\mathsf{QUERY},\mathsf{RECORD},\mathsf{OBSERVE},\mathsf{PLAN}).
\]

\[
\mathsf{SCIENCE\ STATE}
:=
(\mathsf{DEFINITION\ GRAPH},
\mathsf{RECORD\ INTERFACE},
\mathsf{RESIDUAL\ LEDGER},
\mathsf{REVISION\ OPERATOR}).
\]

\[
\mathsf{PHILOSOPHY}
:=
\mathsf{DECT}(\mathsf{METHOD\ SPACE}).
\]

\[
\mathsf{REFLECTION}_{n+1}
:=
\operatorname{Define}
(\ulcorner\mathsf{SCIENCE}_n\urcorner,
\mathsf{META\ RESIDUAL}_n).
\]

\[
\mathsf{SCIENCE}_\omega
:=
\varinjlim_n\mathsf{SCIENCE}_n.
\]

\[
\mathsf{OBJECTIVITY}
:=
\operatorname{Naturality}
(\mathsf{PROPERTY},\mathsf{OBSERVER\ TRANSLATION}).
\]

\[
\mathsf{TRUTH\ RECORD}
:=
\operatorname{Commute}
(\mathsf{PREDICT},\mathsf{OBSERVE};
\mathsf{SCOPE},\varepsilon,\mathsf{VERSION}).
\]

\[
\mathsf{RESISTANCE}
:=
\bigcap_{S'\in\operatorname{Redef}(S)}
\mathsf{RECORD\ RESIDUAL}(S').
\]

最终定义：

\[
\boxed{
\mathsf{SCIENCE}
:=
\operatorname{RecursiveDynamics}
(\mathsf{DEFINE},\mathsf{OBSERVE},\mathsf{PREDICT},
\mathsf{COMPARE},\mathsf{REVISE},\mathsf{REFLECT}).
}
\]

---

# 第四十七部　最终结算

“科学也是定义”现在具有三个强度不同的含义。

第一，有限外延意义：有限科学流程可以通过乘积、依赖和与复合压成一个定义。

第二，内涵结构意义：科学不是裸函数，而是保存来源、依赖、作用域、证书和修订规则的动态定义图。

第三，递归自反意义：科学方法定义如何产生定义；哲学定义如何区分和修订科学方法；更高层继续把前层定义机制变成对象。

所以最终形式不是“科学用定义证明自己的定义正确”，而是：

\[
\boxed{
\text{科学定义对象如何被区分，
定义残差如何被记录，
定义下一项定义如何生成，
并把这一生成规则在下一版本中再次定义为对象。}
}
\]

自反的版本化形式为

\[
\boxed{
S_{n+1}=\Phi(\ulcorner S_n\urcorner,E_n),
\qquad
S_\omega=\varinjlim_nS_n.
}
\]

DECT 因而从“如何发明一个定义”扩展到“一个知识系统如何递归定义自己的定义活动”：

\[
\boxed{
\begin{aligned}
\mathsf{DEFINITION}&=\text{建立区分};\\
\mathsf{PROBLEM}&=\text{目标逃出当前区分};\\
\mathsf{METHOD}&=\text{由逃逸生成下一项定义};\\
\mathsf{PHILOSOPHY}&=\text{在方法空间上重复同一过程};\\
\mathsf{REFLECTION}&=\text{把定义生成规则提升为下一层对象};\\
\mathsf{SCIENCE}&=\text{定义—残差—修订—反射过程的版本化动力学}.
\end{aligned}
}
\]

最终一句：

\[
\boxed{
\text{科学在外延上可以是一项定义；
在结构上是一张定义图；
在时间上是一条定义修订轨道；
在哲学上是这条轨道把自身的生成规则再次变成对象。}
}
\]

---

# 追加账本增订

## v1.1 — 2026-08-23

追加存入：

- 定义宇宙 \(\operatorname{Def}(X)\)、元定义、生成器与变换器；
- 外延定义与内涵定义二分；
- 来源标签、依赖闭包、作用域和定义证书；
- 科学状态作为动态有类型定义图；
- 对象、定律、动力学、仪器、实验、假设、证明和论文的统一编码；
- 有限科学流程的乘积压平与依赖和压平；
- 压平结果不能恢复来源和依赖的非单射结构；
- 研究方法作为由残差产生下一项定义的高阶定义；
- 哲学作为方法空间上的 DECT；
- 元哲学与任意有限反射层；
- 守卫、版本化的自反更新；
- 开放反射塔及直接极限 \(S_\omega\)；
- 反射残差、反射盲核和反射逃逸率；
- 记录接口、允许重定义族、持久残差与现实阻力；
- 事实作为相容记录族，客观性作为自然性；
- 真理记录作为范围化预测—观察交换条件；
- 因果变量作为干预逃逸残差的切割；
- 解释作为多目标捕获、压缩、迁移和反事实闭包；
- 自封闭、表面消残、真正解决与开放修订的行为定义；
-科学系统的 Define/Observe/Predict/Compare/Revise/Reflect 六元结构；
- Yu Deng 方法作为从证明病理到结构定义的元生成器；
- 定义包搜索与方法包搜索的双层盲核；
- 局部完成、预算停止与开放世界重新打开；
- 扩张观察族下科学对象的逆极限定义；
- 纯定义 Lean 接口草案。

后续增订继续严格追加于本节之后。

---

# 第四十八部　证据滤过与访问角色

## 48.1 版本化证据滤过

第 23 部把科学状态写成带来源账本与残差账本的有类型定义图；第 33 部给出记录接口。为了区分“系统在何时能够访问什么”，定义版本化证据滤过

\[
\boxed{
\mathcal F_0 \subseteq \mathcal F_1 \subseteq \cdots \subseteq \mathcal F_n \subseteq \cdots
}
\]

令 \(t_n\) 为第 \(n\) 轮承诺冻结事件在访问账本中的序号。\(\mathcal F_k\) 是前 \(k\) 个访问事件所及对象及其反身传递依赖的闭包；特别地，\(\operatorname{Dep}^*(K_n)\subseteq\mathcal F_{t_n}\)。

滤过单调只表示历史可见项不被抹去；它不表示每项证据都可在每个认识论角色中重复使用。删除记录不应被解释为恢复非预见性，因为首次访问事实已经发生并应留在来源账本中。

对任意对象 \(a\)，定义首次可达时刻

\[
\operatorname{FirstSeen}(a) := \inf\{k:a\in\mathcal F_k\}.
\]

若该集合为空，则取 \(\infty\)。该时刻由依赖闭包与访问账本决定，不由后来形成的理论自报。

## 48.2 同一记录的角色分型

定义证据角色类型

\[
\operatorname{EvidenceRole} := \{ \mathsf{Generate}, \mathsf{Tune}, \mathsf{Select}, \mathsf{Adjudicate}, \mathsf{Replicate} \}.
\]

它们分别表示：产生候选、调节候选内部参数、从候选中选择、裁决已冻结承诺、以及在复验协议下重做裁决。\(\mathsf{Replicate}\) 标签本身不证明独立性；若没有新的观察事件与显式协议独立关系，它仍只是证据复用。

同一记录 \(r\) 可以在不同轮次承担不同角色，但每次角色使用必须形成事件

\[
\operatorname{UseEvent} = (\operatorname{EventId},r,n,\mathsf{role},\operatorname{Deps},\operatorname{Protocol},\operatorname{Time}).
\]

其中 \(\operatorname{EventId}\) 唯一，\(\operatorname{Deps}\) 记录该次使用触及的直接依赖对象。定义角色账本为有限有序日志

\[
\mathcal L_{\mathrm{role}} := (e_1,\ldots,e_N), \qquad \operatorname{EventId}(e_i)\neq\operatorname{EventId}(e_j)\ (i\neq j).
\]

同内容的重复使用因事件号不同而不被折叠。对同一记录同一轮，角色不是单值函数，而是由账本导出的集合谓词

\[
\operatorname{Roles}_{\mathcal L}(r,n) := \{\rho:\exists e\in\mathcal L_{\mathrm{role}},\ e.r=r,\ e.n=n,\ e.\mathsf{role}=\rho\}.
\]

角色不是记录的永久本质；它是记录、轮次、协议和访问时间的关系。一个记录在第 \(n\) 轮用于选择后，不能仅靠重新命名就在同一轮变成未见的裁决记录。

## 48.3 角色准入与污染闭包

对承诺 \(K_n\) 和记录 \(r\)，以反身传递依赖闭包定义可达关系

\[
r\leadsto K_n \quad\Longleftrightarrow\quad r\in\operatorname{Dep}^*(K_n).
\]

令一次角色事件触及承诺闭包，当且仅当其 \(\operatorname{Deps}\) 与 \(\operatorname{Dep}^*(K_n)\) 相交。由账本定义适应性使用谓词

\[
\operatorname{AdaptiveUse}_{\mathcal L}(r,K_n) \Longleftrightarrow \exists e\in\mathcal L_{\mathrm{role}},\ e.r=r,\ e.\mathsf{role}\in\{\mathsf{Generate},\mathsf{Tune},\mathsf{Select}\},\ e.\operatorname{Deps}\cap\operatorname{Dep}^*(K_n)\neq\varnothing.
\]

定义第 \(n\) 轮裁决准入

\[
\boxed{
\operatorname{AdmissibleJudge}_{\mathcal L}(r,K_n) \Longleftrightarrow \mathsf{Adjudicate}\in\operatorname{Roles}_{\mathcal L}(r,n) \ \wedge\ t_n<\operatorname{FirstSeen}(r) \ \wedge\ r\not\leadsto K_n \ \wedge\ \neg\operatorname{AdaptiveUse}_{\mathcal L}(r,K_n).
}
\]

若 \(r\) 的任何函数、摘要、标签、人工筛选结果或由其训练出的中间对象可达 \(K_n\)，则 \(r\) 属于污染闭包；只隐藏原始记录标识不能恢复准入。

对记录集 \(R\)，定义

\[
\operatorname{Contam}(R) := \{a:\exists r\in R,\ r\leadsto a\}.
\]

于是裁决集 \(Z_n\) 的非预见条件可写为

\[
\operatorname{Contam}(Z_n)\cap\operatorname{Dep}^*(K_n) = \varnothing, \qquad \forall z\in Z_n,\ t_n<\operatorname{FirstSeen}(z).
\]

该条件是来源图与访问时间条件，不是关于参与者主观记忆的断言。

## 48.4 已知形状与主张边界

本部借用 filtration、数据分割、预注册和 adaptive data analysis 中“访问历史必须进入有效性判断”的已知形状，不主张这些单项构件首创。

本部也对应需求追溯中的双向链：一个裁决结论应能回溯到承诺与记录，一个承诺也应能前向追踪到实际裁决。这里只定义可审计关系；在缺少采样机制、独立性、稳定性或泛化前件时，不推出统计置信界。

\[
\boxed{
\text{证据是否可作前瞻裁决，不由文件名决定； 而由首次访问是否晚于冻结点、且是否不可达本轮承诺共同决定。}
}
\]

---

# 第四十九部　前视承诺与非预见裁决

## 49.1 承诺对象

定义第 \(n\) 轮前视承诺

\[
\boxed{
K_n = ( \operatorname{TargetChain}_n, \operatorname{Scope}_n, \operatorname{Comparator}_n, \operatorname{TestPlan}_n, \operatorname{Baseline}_n, \operatorname{WeightSpec}_n, \operatorname{CommittedArtifact}_n ).
}
\]

其中

\[
\operatorname{Scope}_n=(J_n,\varepsilon_n,\mathcal C_n)
\]

承接第 35 部的范围化真理记录；目标来源链指向第 23 部定义图中的目标版本及其全部上游节点；比较器给出同一记录上的判别坐标；检验计划规定记录如何进入裁决；基线规定改善相对于什么计算；权重规范可为空，否则必须携带外生来源、版本和适用范围。

被承诺对象是候选预测、行动或模型分量的有限有类型束

\[
\operatorname{CommittedArtifact}_n\subseteq_{\mathrm{fin}}\bigl(\operatorname{Prediction}\sqcup\operatorname{Action}\sqcup\operatorname{ModelComponent}\bigr).
\]

写 \(\operatorname{committed}(K_n,a)\) 表示 \(a\) 属于该冻结对象束。所有被承诺对象进入 \(\operatorname{Dep}^*(K_n)\)；因此它们不能在裁决记录到达后替换而仍沿用同一承诺编号。

承诺的冻结记录为

\[
\operatorname{Seal}(K_n) = (\operatorname{Digest}(K_n),t_n,\operatorname{Dep}^*(K_n)).
\]

摘要只用于识别；承诺内容及其依赖闭包仍是承重对象。

## 49.2 冻结与非预见性

设裁决记录 \(z_n\) 的到达时刻为访问账本中的首次可达时刻

\[
u_n:=\operatorname{FirstSeen}(z_n).
\]

定义前视冻结

\[
\operatorname{FrozenBefore}(K_n,z_n) \Longleftrightarrow t_n<u_n.
\]

定义非预见承诺

\[
\boxed{
\operatorname{NonAnticipating}(K_n,z_n) \Longleftrightarrow \operatorname{FrozenBefore}(K_n,z_n) \ \wedge\ z_n\not\leadsto K_n.
}
\]

若裁决对象是记录集 \(Z_n\)，则要求对所有 \(z\in Z_n\) 成立。时间先后是必要条件但不是充分条件：若未来记录的代理、泄漏摘要或预先可得标签进入依赖闭包，仍违反非预见性。

## 49.3 回顾拟合

以下 \(\operatorname{Improves}\) 与 \(\operatorname{Loss}\) 中的行动、模型和预测均指 \(K_n\) 已冻结依赖中的版本；任何事后生成版本都必须使用新的承诺标识。

定义回顾拟合标签

\[
\boxed{
\operatorname{PostdictiveFit}(a,K_n,Z_n) \Longleftrightarrow \operatorname{Improves}(a;K_n,Z_n) \ \wedge\ \neg\operatorname{NonAnticipating}(K_n,Z_n).
}
\]

它不是“无价值”或“错误”的同义词。回顾拟合可以产生候选、解释、压缩、机制猜想和下一轮承诺；它只是不具有本轮前瞻增益的记账资格。

因此必须区分

\[
\begin{aligned}
\mathsf{DiscoveryCredit}
&=\text{从已见记录中形成有用结构};
\\
\mathsf{ProspectiveCredit}
&=\text{在冻结承诺后的新裁决记录上改善}.
\end{aligned}
\]

前者可以进入 \(K_{n+1}\)，不得改写为 \(K_n\) 的后验预言。

## 49.4 事后复制定理骨架

设比较器允许逐记录输出，候选类包含对有限裁决集 \(Z_n\) 的查表复制器

\[
a_{Z_n}(z):=\operatorname{ObservedAnswer}(z).
\]

并设比较器的逐点损失满足 \(\ell(y,y)=0\)，总损失不含额外复杂度或正则罚项，聚合器把逐点全零映为总体零。若所有 \(z\in Z_n\) 已进入 \(a_{Z_n}\) 的依赖闭包，则

\[
\boxed{
\operatorname{Loss}_{K_n}(a_{Z_n};Z_n)=0
}
\]

可以由定义展开得到。

但同时

\[
Z_n\leadsto a_{Z_n}\leadsto K'_n,
\]

故任何把 \(a_{Z_n}\) 纳入同轮承诺的 \(K'_n\) 都满足

\[
\neg\operatorname{NonAnticipating}(K'_n,Z_n).
\]

所以在上述前件下：

\[
\boxed{
\text{回顾残差为零不蕴含前瞻增益为正。}
}
\]

该骨架不声称所有学习器都能零误差，也不声称回顾拟合不能泛化；泛化需要另给稳定性、容量、采样或独立复验前件。

## 49.5 序贯裁决的已知形状

本部借用 Dawid prequential/序贯预测中“先给出预测，再由随后记录裁决”的已知顺序，也借用预注册中“分析坐标先于结果冻结”的已知形状，不主张首创。

DECT 的新增工作只是把该顺序接入定义来源图、目标版本、作用域和残差账本：

\[
\boxed{
K_n \longrightarrow Z_n \longrightarrow \operatorname{Verdict}_n,
}
\]

且箭头不得逆接为 \(Z_n\leadsto K_n\)。

---

# 第五十部　目标账、议程残差与漂移守恒

## 50.1 Target、Question 与 Agenda 的类型

承接第 23 部的有类型定义图，定义目标节点

\[
\operatorname{Target} = ( \operatorname{Carrier}, \operatorname{Readout}, \operatorname{Success}, \operatorname{Scope}, \operatorname{Version}, \operatorname{Origin} ).
\]

定义问题节点

\[
\operatorname{Question} = ( \operatorname{TargetRef}, q, \mathcal E(q;T), \operatorname{ClosureRule} ).
\]

定义议程节点

\[
\operatorname{Agenda} = ( \operatorname{QuestionSet}, \operatorname{Eligibility}, \operatorname{OrderRule}, \operatorname{Version} ).
\]

三者不是同义词：目标规定何种结果算成功，问题记录当前表示相对该目标留下的残差，议程规定哪些问题当前可进入选择与排序。

## 50.2 议程残差

给定外生目的 \(G\)，令

\[
V_G:\operatorname{Agenda}\to Y_G
\]

表示在目的 \(G\) 下对议程后果的读数，令

\[
q_A:\operatorname{Agenda}\to Q_A
\]

表示当前议程语言。定义议程残差

\[
\boxed{
\mathcal E_{\mathrm{agenda}}(q_A;G) = \ker(q_A)\setminus\ker(V_G).
}
\]

它记录当前议程语言视为相同、但在给定目的 \(G\) 下后果不同的议程对。该残差只在 \(G\) 已给定时有意义；它不从事实记录中自动生成终极目的。

## 50.3 目标变更事件与旧轮守恒

定义目标变更事件

\[
\operatorname{TargetChange}_n = ( T_n,T_{n+1}, \operatorname{Reason}, \operatorname{Author}, \operatorname{Time}, \operatorname{AffectedRounds} ).
\]

合法变更产生新版本边

\[
T_n\longrightarrow T_{n+1},
\]

而不是把 \(T_n\)、比较器或范围原地替换。定义第 \(n\) 轮结算

\[
\operatorname{Settle}_n := \operatorname{Evaluate}(K_n,Z_n).
\]

若账本追加、旧承诺不可变，且后续更新只产生 \(K_{n+1}\)，则对任意 \(m>n\) 有条件骨架

\[
\boxed{
\operatorname{Settle}_n^{(m)} = \operatorname{Settle}_n^{(n)}.
}
\]

该等式是版本寻址与纯评价的结果；若评价器调用可变外部状态，则必须把该状态版本也纳入 \(K_n\)。

## 50.4 目标漂白

定义受保护坐标

\[
\operatorname{Protected}(K_n) := (\operatorname{TargetChain}_n,J_n,\varepsilon_n,\mathcal C_n,\operatorname{Comparator}_n,\operatorname{Baseline}_n,\operatorname{WeightSpec}_n).
\]

定义裁决记录到达后的受保护坐标变更

\[
\operatorname{PostArrivalProtectedChange}(K_n,K'_n;Z_n) \Longleftrightarrow \operatorname{Arrival}(Z_n)<\operatorname{Time}(K'_n) \ \wedge\ \operatorname{Protected}(K'_n)\neq\operatorname{Protected}(K_n).
\]

定义冒充归因

\[
\operatorname{AttributesToOriginalCommitment}(K_n,K'_n;Z_n)
\Longleftrightarrow
\operatorname{ReportedAsSuccess}\bigl(\operatorname{Evaluate}(K'_n,Z_n),K_n\bigr).
\]

目标漂白当且仅当三项同时成立：裁决记录到达后修改至少一个受保护坐标；以新坐标重评旧轮；把该重评结果归因于原承诺 \(K_n\)：

\[
\boxed{
\begin{aligned}
\operatorname{TargetLaundering}_n(K'_n;Z_n)
\Longleftrightarrow{}
&\operatorname{PostArrivalProtectedChange}(K_n,K'_n;Z_n)
\\
&\wedge\ \operatorname{RegradesOldRound}(K_n,K'_n;Z_n)
\\
&\wedge\ \operatorname{AttributesToOriginalCommitment}(K_n,K'_n;Z_n).
\end{aligned}
}
\]

该判据不要求新旧分数不同。即使篡改后数值恰好相同，只要仍以新坐标重评旧轮并冒充原承诺结算，目标漂白仍成立。

合法目标学习不被禁止；它必须登记为 \(K_{n+1}\) 的来源，而不能消除 \(K_n\) 已经发生的失败。

该定义细化第 38 部的表面消残：目标漂白是通过回写裁决坐标来消残的版本化特例。

## 50.5 定向算子与 Hume 边界

给定目的 \(G\)，定义可准入目标集

\[
\operatorname{AdmTarget}(G) := \{T:\operatorname{Eligible}(T,G)\}.
\]

定向关系不由 \(G\) 自生，而消费外生只读规范包

\[
\operatorname{OrientationSpec}_G := (\preceq_G,\operatorname{Source},\operatorname{Version},\operatorname{Scope},\operatorname{PreorderProof}).
\]

其中 \(\operatorname{PreorderProof}\) 证明 \(\preceq_G\) 在声明范围内为预序。定义定向算子为该规范包的投影

\[
\boxed{
\operatorname{Orient}_G(\operatorname{OrientationSpec}_G) := \preceq_G.
}
\]

它只在外生且只读的 \(G\) 诱导的可准入集合内排序，不从记录中创造 \(G\)，也不把 \(G\) 改写成事实命题。

本部借用目的—手段区分、需求追溯与变更控制的已知形状，并保留 Hume 边界：从事实相容族到终极目的不存在由本文定义出的无参数规范映射。任何

\[
\operatorname{Fact}_{\mathcal O}\to G
\]

都必须显式携带额外规范前件、授权或价值来源。

---

# 第五十一部　证据管辖域与外推证书

## 51.1 范围化预测读数

第 35 部把真理记录写成 \((J,\varepsilon,\mathcal C)\) 下的预测—观察交换。为研究扩域，设模型空间为 \(\Theta\)，对操作域 \(J\subseteq I\) 定义联合预测读数

\[
P_J:\Theta\to R^J, \qquad P_J(\theta):=(P(\theta,i))_{i\in J}.
\]

若 \(J\subseteq J'\)，存在限制映射

\[
\operatorname{res}_{J',J}:R^{J'}\to R^J
\]

满足

\[
P_J = \operatorname{res}_{J',J}\circ P_{J'}.
\]

因此

\[
\ker P_{J'} \subseteq \ker P_J.
\]

## 51.2 扩域逃逸对

定义从 \(J\) 扩张到 \(J'\) 的扩域逃逸关系

\[
\boxed{
\mathcal E_{\mathrm{expand}}(P;J,J') := \ker P_J\setminus\ker P_{J'}.
}
\]

其元素是旧域内预测完全相同、但在新域中分离的模型对。它精确记录旧证据管辖域没有裁决、扩域后重新出现的区分。

核差恒等式直接给出

\[
\mathcal E_{\mathrm{expand}}(P;J,J')=\varnothing \Longleftrightarrow \ker P_J\subseteq\ker P_{J'}.
\]

结合反向包含，可得空逃逸等价于两域在模型区分能力上核相同。该结论只谈预测纤维，不自动给出现实记录上的误差界。

## 51.3 范围运输与证书

定义范围运输候选

\[
\tau_{J,J'}: \operatorname{TruthRecord}_{J,\varepsilon,\mathcal C} \to \operatorname{Claim}_{J'}.
\]

外推证书至少为

\[
\boxed{
\operatorname{TransportCert}_{J\to J'} = ( \operatorname{Receipt}_{J}, \operatorname{TransportAssumption}_{J\to J'}, \operatorname{FalsifiablePrediction}_{J'\setminus J} ).
}
\]

其中旧域收据锁定原版本、原记录与原误差；运输假设说明哪些结构在域变换下保持；可失败预测规定新域中新记录到来时什么结果会否决运输。

若运输还依赖选择机制、干预一致性、协变量变换或损失稳定性，这些必须进入运输假设，不得藏在“同类情形”一词中。

给定证书 \(\kappa\)、主张 \(c\) 及其版本 \(\nu\)，定义有效外推证书

\[
\boxed{
\begin{aligned}
\operatorname{ValidTransportCert}(\kappa,c;J,J',\nu)
\Longleftrightarrow{}
&\operatorname{ReceiptMatches}(\kappa.\operatorname{Receipt},J,\nu)
\\
&\wedge\
\bigl(
\operatorname{GivenPremises}(\kappa)
\wedge\kappa.\operatorname{TransportAssumption}
\Rightarrow \operatorname{ClaimOn}(c,J')
\bigr)
\\
&\wedge\
\forall z\in J'\setminus J,\
\operatorname{PredictionFails}(\kappa,z)
\Rightarrow\operatorname{Refutes}(z,\kappa,c).
\end{aligned}
}
\]

第一项锁定原域与版本；第二项要求运输假设只在明列前件下蕴含 \(J'\) 上的主张；第三项把预先登记的失败结果定义为对该证书的反驳。仅有三元组数据而不满足此谓词，不构成外推门票。

## 51.4 越权主张与重新打开

定义越权普遍化

\[
\boxed{
\operatorname{Overreach}(c;J,J') \Longleftrightarrow J\subsetneq J' \ \wedge\ \operatorname{Scope}(c)=J \ \wedge\ \neg\exists\kappa,\operatorname{ValidTransportCert}(\kappa,c;J,J',\operatorname{Version}(c)) \ \wedge\ c\text{ 被报告为覆盖 }J'.
}
\]

旧域相符

\[
S\models_{J,\varepsilon}w
\]

一般不蕴含

\[
S\models_{J',\varepsilon}w.
\]

条件反例骨架：只要 \(J'\setminus J\neq\varnothing\) 且记录空间允许在新操作上出现超过 \(\varepsilon\) 的偏差，就可保持 \(J\) 上全部读数不变而使 \(J'\) 上失败。

所以扩域必须重新打开第 43 部的局部完成：

\[
\boxed{
\operatorname{Closed}_{J}(S,T)\not\Rightarrow \operatorname{Closed}_{J'}(S,T).
}
\]

若有运输证书及其全部前件，才可建立特定的条件运输定理。

## 51.5 已知形状与时域特例

本部借用 external validity、transportability、分布迁移和契约作用域的已知形状，不主张首创。DECT 的工作是把它们写成核差、范围化真理记录与可失败证书之间的接口。

第 8 部的时域扩张是本结构的特例。令

\[
J_N:=\{0,1,\ldots,N\}, \qquad P_{J_N}(x):=(q(\tau^k x))_{k\le N},
\]

则对 \(N<N'\)，

\[
\mathcal E_{\mathrm{expand}}(P;J_N,J_{N'}) = \ker T_N\setminus\ker T_{N'}.
\]

它正是旧时域尚未分离、延长时域后首次暴露的预测逃逸对。

---

# 第五十二部　反事实增益账

## 52.1 两个反事实基线

每轮至少登记两个比较对象：

\[
a_{\varnothing} = \text{什么都不做},
\]

以及

\[
a_{\min} = \text{满足本轮充分阈值的最低全生命周期成本替代}.
\]

定义充分替代集合

\[
\operatorname{SuffAlt}(K_n) := \{a:\operatorname{MeetsCommitment}(a,K_n)\}.
\]

若该集合非空且成本下确有最小元，则

\[
a_{\min} \in \arg\min_{a\in\operatorname{SuffAlt}(K_n)} \operatorname{LifecycleCost}(a).
\]

最小元的存在不是无条件定理；无限候选、不可比较成本或未达下确界时，只能记录候选前沿。

## 52.2 五维增益向量

对承诺 \(K_n\) 下每个行动 \(a\)，先在同一公共绝对坐标系中定义

\[
\mathbf v_{K_n}(a) := \bigl(I_n(a),R_n(a),T_n(a),C_n(a),Q_n(a)\bigr).
\]

五项依次为信息读数、目标残差捕获、迁移读数、全生命周期成本及失败、误用与不可逆风险。每一坐标必须对全部行动共用来源、量纲、估计方法和版本；没有概率模型时，\(I_n\) 可用明确的分划细化或可区分对增量替代，不应冒充 Shannon 或 Bayes 量。

对行动 \(a\) 与基线 \(b\)，定义逐对差分增益账

\[
\boxed{
\mathbf G_n(a\mid b) := \Delta_n(a\mid b) := \mathbf v_{K_n}(a)-\mathbf v_{K_n}(b) = ( \Delta I, \Delta R, \Delta T, \Delta C, \Delta Q ).
}
\]

在各坐标为加法群的前件下，该定义直接给出

\[
\Delta_n(a\mid a)=0, \qquad \Delta_n(a\mid b)+\Delta_n(b\mid c)=\Delta_n(a\mid c).
\]

## 52.3 Pareto 裁决

定义弱支配

\[
a\succeq_{K_n} b
\]

当且仅当公共绝对坐标满足

\[
I_n(a)\ge I_n(b),\ R_n(a)\ge R_n(b),\ T_n(a)\ge T_n(b),\ C_n(a)\le C_n(b),\ Q_n(a)\le Q_n(b).
\]

至少一项严格时定义严格支配 \(a\succ_{K_n}b\)。

若各坐标关系为预序，则 \(\succeq_{K_n}\) 在行动上为预序。令 \(a\sim_v b\Longleftrightarrow\mathbf v_{K_n}(a)=\mathbf v_{K_n}(b)\)；当各坐标为偏序时，\(\succeq_{K_n}\) 在行动等价类 \(A/{\sim_v}\) 上诱导偏序。不同但同向量的行动在取商前不可宣称反对称。

不被其他候选严格支配的行动构成

\[
\operatorname{GainFrontier}(K_n).
\]

没有来源权重时，不把五维账压成单标量。若确需

\[
U_w(\mathbf G)= w_I\Delta I+w_R\Delta R+w_T\Delta T-w_C\Delta C-w_Q\Delta Q,
\]

则权重 \(w\) 必须有外生来源、版本和适用范围，并冻结在 \(K_n\) 中。否则标量排名只是未登记的目标变更。

## 52.4 前瞻科学增益

设 \(Z_n\) 是满足第 49 部非预见条件的新裁决记录。定义行动 \(a\) 相对基线 \(b\) 的前瞻改善

\[
\operatorname{ProspectiveImprove}_n(a\mid b) \Longleftrightarrow \operatorname{Loss}_{K_n}(a;Z_n) < \operatorname{Loss}_{K_n}(b;Z_n).
\]

定义本轮可计科学增益

\[
\boxed{
\begin{aligned}
\operatorname{ScientificGain}_n(a\mid b)
\Longleftrightarrow{}
&\operatorname{committed}(K_n,a)
\ \wedge\ b\in\operatorname{Baselines}(K_n)
\\
&\wedge\ \operatorname{NonAnticipating}(K_n,Z_n)
\ \wedge\ \operatorname{ProspectiveImprove}_n(a\mid b).
\end{aligned}
}
\]

该定义只给出记账资格，不自动给出显著性、置信度或长期稳定性。若比较器本身是向量，则改善按 \(K_n\) 中预先冻结的偏序判断。

应同时报告

\[
\mathbf G_n(a\mid a_{\varnothing}) \quad\text{与}\quad \mathbf G_n(a\mid a_{\min}),
\]

以区分“比不做更好”与“比最便宜充分替代更好”。

## 52.5 适应性复用、VOI 与 Goodhart 边界

令 \(\mathcal L_{\mathrm{role},\le n}\) 为有限有序角色日志截至第 \(n\) 轮的前缀。对同一证据的反复适应性使用，定义复用深度

\[
\operatorname{ReuseDepth}(r,n) := |\{e\in\mathcal L_{\mathrm{role},\le n}: e.\operatorname{record}=r\}|\in\mathbb N.
\]

唯一事件号使内容相同但实际发生多次的使用分别计数；有限前缀保证该深度落在折减函数的自然数定义域。

对预先选定的单一坐标或逐坐标，可以登记折减函数

\[
\delta:\mathbb N\to[0,1], \qquad \operatorname{CreditedGain} = \delta(\operatorname{ReuseDepth})\cdot\operatorname{ObservedGain}.
\]

但在没有稳定性、隐私、容量或选择机制定理时，\(\delta\) 只是治理账本，不是统计保证；其正确形状标为 open。

本部借用贝叶斯实验设计与 value of information 中“行动价值相对反事实和信息结构计算”的已知形状。若给定先验 \(\pi\)、损失 \(\ell\) 与采样模型，才可定义特定 VOI；本文不在缺少这些前件时声称 Bayes 最优。

本部也借用 Goodhart 定律的警戒形状：一旦得分坐标同时成为自适应优化对象，分数上升不能独立证明目标改善。DECT 的处置不是禁止指标，而是冻结比较器、保留目标账并要求新记录裁决。

---

# 第五十三部　科学循环的承诺补型

## 53.1 裁决六元循环

第 39 部定义

\[
(\mathsf{Define},\mathsf{Observe},\mathsf{Predict}, \mathsf{Compare},\mathsf{Revise},\mathsf{Reflect}).
\]

为使其可裁决，本部令 \(\mathsf{Define}\) 先产生带预测、行动或模型分量的有类型候选束，再由 \(\mathsf{Commit}\) 把选定对象连同目标、范围、比较器、计划、基线和权重规范封入承诺：

\[
\mathsf{Define}:\Sigma_n\to\operatorname{CandidateBundle}_n, \qquad \mathsf{Commit}:\operatorname{CandidateBundle}_n\to(K_n,\operatorname{Seal}(K_n)).
\]

\[
\boxed{
\Sigma_n\xrightarrow{\mathsf{Define}}\operatorname{CandidateBundle}_n\xrightarrow{\mathsf{Commit}}K_n\xrightarrow{\mathsf{Observe}}Z_n\xrightarrow{\mathsf{Compare}}\operatorname{Verdict}_n\xrightarrow{\mathsf{Revise}}\Sigma_{n+1}^{-}\xrightarrow{\mathsf{Reflect}}\Sigma_{n+1}.
}
\]

并要求 \(\operatorname{CommittedArtifact}_n\subseteq\operatorname{CandidateBundle}_n\)。这不是删除预测；预测从可随时变化的中间动作变成承诺 \(K_n\) 的冻结字段，且不能在观察 \(Z_n\) 后从表外补入。

## 53.2 单轮状态转换

令 \(\mathcal L_{\mathrm{role},\le n}\) 为第 48 部有限有序角色日志的轮前缀，并以带标签直和把它类型化接入内涵账本：

\[
\mathcal L_n:=\mathcal L_n^{\mathrm{source}}\sqcup\mathcal L_{\mathrm{role},\le n}.
\]

定义轮状态

\[
\Sigma_n = (S_n,\mathcal F_{t_n},\mathcal L_n^{\mathrm{source}}\sqcup\mathcal L_{\mathrm{role},\le n},\mathcal R_n).
\]

各步为：

\[
\mathsf{Define}(\Sigma_n) = \operatorname{CandidateBundle}_n\text{，依据旧残差 }\mathcal R_n\text{ 产生候选与问题版本};
\]

\[
\mathsf{Commit}(\operatorname{CandidateBundle}_n) = (K_n,\operatorname{Seal}(K_n));
\]

\[
\mathsf{Observe}(w,\operatorname{TestPlan}_n) = Z_n;
\]

\[
\mathsf{Compare}(K_n,Z_n) = \operatorname{Verdict}_n;
\]

\[
\mathsf{Revise}(S_n,\operatorname{Verdict}_n) = (S_{n+1}^{-},K_{n+1}^{\mathrm{proposal}});
\]

\[
\mathsf{Reflect}(S_{n+1}^{-}) = S_{n+1}.
\]

其中 \(K_{n+1}^{\mathrm{proposal}}\) 尚不是已冻结承诺；下一轮只有在新的 Commit 事件后才获得裁决坐标。

## 53.3 原坐标比较与不可回写

定义原坐标原则

\[
\boxed{
\operatorname{Verdict}_n = \operatorname{Evaluate}(K_n,Z_n),
}
\]

而不是

\[
\operatorname{Evaluate}(K_{n+1},Z_n).
\]

若 Revise 修改目标、比较器、范围、权重或基线，则这些修改只进入 \(K_{n+1}^{\mathrm{proposal}}\)。在追加账本、版本不可变与纯评价前件下，得到条件骨架

\[
\operatorname{Evaluate}(K_n,Z_n) = \operatorname{Evaluate}(\operatorname{Lookup}(n),Z_n)
\]

对所有后续轮次保持不变。

因此循环允许学习，但不允许让学习结果穿越回本轮冻结点。

## 53.4 Gain/cost 停止条件的接入

第 43 部的

\[
\operatorname{Stop}_{L}(S)
\]

使用 \(\operatorname{Gain}/c\) 标量。本增订给出其裁决层前件：只有在增益坐标、成本口径、风险口径和权重来源已冻结时，该比率才有确定含义。

无来源权重时，定义 Pareto 停止

\[
\boxed{
\begin{aligned}
\operatorname{ParetoStop}(K_n)
\Longleftrightarrow
\nexists a\in\operatorname{Candidates}(K_n)\ \text{使得}\quad
&a\succeq_{K_n}a_{\varnothing},\quad
a\succeq_{K_n}a_{\min},
\\
&a\succ_{K_n}a_{\varnothing}
\ \vee\ a\succ_{K_n}a_{\min}.
\end{aligned}
}
\]

这样，最低成本充分替代本身若严格优于不做，也不会被停止式错误排除。若 \(a_{\min}\) 不存在，则第二项替换为相对于当前充分替代前沿的逐点比较。停止是当前承诺、候选集与证据状态下的局部结论；范围扩张、目标变更或新方法出现时仍按第 43 部重新打开。

## 53.5 三类合法产出

每轮产出分为：

\[
\begin{aligned}
\mathsf{ProspectiveResult}
&:\operatorname{ScientificGain}_n\text{ 成立};
\\
\mathsf{PostdictiveDiscovery}
&:\operatorname{PostdictiveFit}\text{ 成立但形成 }K_{n+1};
\\
\mathsf{Unresolved}
&:\text{既未改善，也未形成可检验的新承诺}.
\end{aligned}
\]

三类都可进入历史账本，但只能第一类记为本轮前瞻科学增益。第二类的价值在于生成下一轮可失败预测；第三类保留失败与残差，防止静默消失。

\[
\boxed{
\text{Revise 可以改变下一轮的尺； 不能改变上一轮曾用过哪把尺。}
}
\]

---

# 第五十四部　接线注记、形式化接口与裁决结算

## 54.1 与既有各部的断链接线

- 第 3 部把泄漏定位为来源性质；第 48—49 部补上记录角色、访问滤过与裁决记录不可达承诺的时间化判据。
- 第 8 部的时域逃逸由第 51 部取 \(J_N\subset J_{N'}\) 得到，成为证据管辖域扩张的特例。
- 第 14 部的价值函数只有在权重来源、版本和范围冻结于 \(K_n\) 时才可作标量裁决；否则退回第 52 部公共绝对坐标上的 Pareto 账。
- 第 22 部的内涵定义保存来源与依赖；第 48 部的有限有序角色日志以带标签分量类型化进入 \(\mathcal L_n\)，角色集合与裁决准入均由该日志导出。
- 第 23 部的有类型定义图承载 Target、Question、Agenda 及其版本边；候选预测、行动或模型分量作为 \(\operatorname{CommittedArtifact}_n\) 冻结进 \(K_n\)。
- 第 24 部的实验计划 \(\pi\) 进入 \(K_n\) 的 TestPlan；模型纤维不得与裁决有效性混为一谈。
- 第 25 部说明压平会遗失来源；故承诺不能只保存最终评分函数，必须保存依赖闭包。
- 第 26—27 部的对象层与方法层残差继续生成候选，但候选何时可获前瞻信用由裁决层另行决定。
- 第 33 部的记录接口提供 Observe 与 Predict 的共同载体；第 49 部在两者之间加入不可逆的冻结点。
- 第 34 部的客观性自然性不替代非预见性；跨协议相容与未见记录裁决是两个独立条件。
- 第 35 部的 \((J,\varepsilon,\mathcal C)\) 成为承诺范围与外推证书的源域收据；只有原域与版本匹配、运输蕴含成立且失败可反驳的证书才有效。
- 第 38 部的表面消残在第 50 部被细化为三合取目标漂白事件，不以分数是否变化代替保护坐标是否被回写。
- 第 39 部的六元结构由第 53 部补成带 Commit 的裁决循环；Define 先产有类型候选束，Commit 再把其中对象封入承诺。
- 第 43 部的 Gain/cost 停止接到第 52 部增益账；行动上弱支配为预序，同向量取商后才为偏序；扩域、改目标或新证据仍触发重新打开。

## 54.2 参照系与新颖性边界

本增订分别借用下列成熟构件的已知形状：

- Dawid prequential/序贯预测的先预测后观察；
- 预注册的结果前冻结；
- adaptive data analysis 的适应性访问风险；
- external validity 与 transportability 的范围运输；
- 贝叶斯实验设计与 VOI 的反事实行动比较；
- Goodhart 定律的指标内生化警戒；
- 需求追溯与变更控制的版本、来源和不可回写账。

本文不主张这些构件单项首创。把证据滤过、前视承诺、目标漂移守恒、外推核差、反事实增益账和递归定义循环合成为一个 DECT 裁决层，当前只标记为

\[
\boxed{
\mathsf{suspected\text{-}novel}
}
\]

且未做系统文献检索。任何整体新颖性声明在完成系统检索前均为 open。

## 54.3 最小可形式化定义清单

建议下游优先切分以下纯定义或条件骨架：

```lean
universe u v w

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

inductive EvidenceRole
  | generate | tune | select | adjudicate | replicate

structure UseEvent
    (EventId Evidence Round Artifact Protocol Time : Type u) where
  eventId : EventId
  evidence : Evidence
  round : Round
  role : EvidenceRole
  dependencies : Set Artifact
  protocol : Protocol
  usedAt : Time

structure RoleLedger
    (EventId Evidence Round Artifact Protocol Time : Type u) where
  events : List (UseEvent EventId Evidence Round Artifact Protocol Time)
  uniqueEventIds : (events.map fun e => e.eventId).Nodup

def RolesAt
    {EventId Evidence Round Artifact Protocol Time : Type u}
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (r : Evidence) (n : Round) : Set EvidenceRole :=
  {ρ | ∃ e, e ∈ L.events ∧ e.evidence = r ∧ e.round = n ∧ e.role = ρ}

def AdaptiveUseInClosure
    {EventId Evidence Round Artifact Protocol Time Commitment : Type u}
    (touchesClosure : Set Artifact → Commitment → Prop)
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (r : Evidence) (K : Commitment) : Prop :=
  ∃ e, e ∈ L.events ∧ e.evidence = r ∧
    (e.role = .generate ∨ e.role = .tune ∨ e.role = .select) ∧
    touchesClosure e.dependencies K

def AdmissibleJudge
    {EventId Evidence Round Artifact Protocol Time Commitment : Type u}
    (frozenBeforeRecord : Commitment → Evidence → Prop)
    (dependsOn : Evidence → Commitment → Prop)
    (touchesClosure : Set Artifact → Commitment → Prop)
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (r : Evidence) (n : Round) (K : Commitment) : Prop :=
  .adjudicate ∈ RolesAt L r n ∧ frozenBeforeRecord K r ∧
    ¬ dependsOn r K ∧ ¬ AdaptiveUseInClosure touchesClosure L r K

structure EvidenceFiltration
    (Round Evidence : Type u) [Preorder Round] where
  seen : Round → Set Evidence
  monotone : ∀ {m n}, m ≤ n → seen m ⊆ seen n

structure OrientationSpec
    (Target Source Version Scope : Type u) where
  relation : Target → Target → Prop
  source : Source
  version : Version
  scope : Scope
  refl : ∀ a, relation a a
  trans : ∀ {a b c}, relation a b → relation b c → relation a c

structure ProspectiveCommitment
    (TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec CommittedArtifact : Type u) where
  targetChain : TargetChain
  domain : Domain
  epsilon : Epsilon
  conditions : Condition
  comparator : Comparator
  testPlan : TestPlan
  baseline : Baseline
  weightSpec : WeightSpec
  committedArtifacts : Set CommittedArtifact

structure CommitInterface
    (RoundState CandidateBundle Commitment Seal : Type u) where
  defineStep : RoundState → CandidateBundle
  commitStep : CandidateBundle → Commitment × Seal

def NonAnticipating
    {Commitment Evidence : Type u}
    (frozenBefore : Commitment → Evidence → Prop)
    (dependsOn : Evidence → Commitment → Prop)
    (K : Commitment) (Z : Evidence) : Prop :=
  frozenBefore K Z ∧ ¬ dependsOn Z K

structure ProtectedCoordinates
    (Target Comparator Scope Precision Baseline WeightSpec : Type u) where
  target : Target
  comparator : Comparator
  scope : Scope
  precision : Precision
  baseline : Baseline
  weightSpec : WeightSpec

def TargetLaundering
    {Commitment Evidence Target Comparator Scope
      Precision Baseline WeightSpec : Type u}
    (arrivedBefore : Evidence → Commitment → Prop)
    (coordinates : Commitment →
      ProtectedCoordinates Target Comparator Scope Precision Baseline WeightSpec)
    (regradesOldRound :
      Commitment → Commitment → Evidence → Prop)
    (attributesToOriginal :
      Commitment → Commitment → Evidence → Prop)
    (oldK newK : Commitment) (Z : Evidence) : Prop :=
  arrivedBefore Z newK ∧ coordinates newK ≠ coordinates oldK ∧
    regradesOldRound oldK newK Z ∧
    attributesToOriginal oldK newK Z

def ExpansionEscape
    {Model : Type u} {ReadoutJ : Type v} {ReadoutJ' : Type w}
    (PJ : Model → ReadoutJ) (PJ' : Model → ReadoutJ') :
    Model → Model → Prop :=
  fun x y => PJ x = PJ y ∧ PJ' x ≠ PJ' y

structure TransportCert
    (TruthReceipt TransportAssumption NewDomainPrediction : Type u) where
  oldReceipt : TruthReceipt
  assumption : TransportAssumption
  falsifiablePrediction : NewDomainPrediction

def ValidTransportCert
    {TruthReceipt TransportAssumption NewDomainPrediction Claim
      Domain Version Premises NewEvidence : Type u}
    (receiptMatches : TruthReceipt → Domain → Version → Prop)
    (entails :
      Premises → TransportAssumption → Claim → Domain → Prop)
    (inNewOnlyDomain : NewEvidence → Domain → Domain → Prop)
    (predictionFails : NewDomainPrediction → NewEvidence → Prop)
    (refutes :
      NewEvidence →
      TransportCert TruthReceipt TransportAssumption NewDomainPrediction →
      Claim → Prop)
    (cert : TransportCert TruthReceipt TransportAssumption NewDomainPrediction)
    (premises : Premises) (claim : Claim)
    (J J' : Domain) (version : Version) : Prop :=
  receiptMatches cert.oldReceipt J version ∧
    entails premises cert.assumption claim J' ∧
    ∀ z, inNewOnlyDomain z J J' →
      predictionFails cert.falsifiablePrediction z →
      refutes z cert claim

def Overreach
    {Claim Domain : Type u}
    (strictSubset : Domain → Domain → Prop)
    (scopeIs : Claim → Domain → Prop)
    (hasValidTransportCert : Claim → Domain → Domain → Prop)
    (reportedFor : Claim → Domain → Prop)
    (claim : Claim) (J J' : Domain) : Prop :=
  strictSubset J J' ∧ scopeIs claim J ∧
    ¬ hasValidTransportCert claim J J' ∧ reportedFor claim J'

structure GainVector
    (Coord : Type u) where
  information : Coord
  residualCapture : Coord
  transfer : Coord
  lifecycleCost : Coord
  risk : Coord

def gainDifference
    {Action Coord : Type u} [Sub Coord]
    (value : Action → GainVector Coord) (a b : Action) :
    GainVector Coord :=
  { information := (value a).information - (value b).information
    residualCapture :=
      (value a).residualCapture - (value b).residualCapture
    transfer := (value a).transfer - (value b).transfer
    lifecycleCost := (value a).lifecycleCost - (value b).lifecycleCost
    risk := (value a).risk - (value b).risk }

def ParetoWeak
    {Action Coord : Type u} [LE Coord]
    (value : Action → GainVector Coord) (a b : Action) : Prop :=
  (value b).information ≤ (value a).information ∧
    (value b).residualCapture ≤ (value a).residualCapture ∧
    (value b).transfer ≤ (value a).transfer ∧
    (value a).lifecycleCost ≤ (value b).lifecycleCost ∧
    (value a).risk ≤ (value b).risk

def ScientificGain
    {Commitment Evidence Action : Type u} {Loss : Type v} [LT Loss]
    (nonAnticipating : Commitment → Evidence → Prop)
    (committed : Commitment → Action → Prop)
    (isBaseline : Commitment → Action → Prop)
    (loss : Commitment → Action → Evidence → Loss)
    (K : Commitment) (Z : Evidence) (a b : Action) : Prop :=
  committed K a ∧ isBaseline K b ∧
    nonAnticipating K Z ∧ loss K a Z < loss K b Z

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
```


PostdictiveFit 直接由 \(\operatorname{Improves}\wedge\neg\operatorname{NonAnticipating}\) 派生，不另列为原语。

首先应证明或检查：

1. 依赖闭包污染下裁决准入反单调；
2. 查表复制器零回顾损失与非预见失败可同时成立；
3. 追加式目标变更不改变旧承诺的纯评价结果；
4. \(J\subseteq J'\) 时 \(\ker P_{J'}\subseteq\ker P_J\)；
5. 在限制律成立时，扩域逃逸为空当且仅当两域预测核相同；
6. 各坐标为预序时，公共绝对坐标诱导的 Pareto 弱支配在行动上为预序；各坐标为偏序时，按同向量等价取商后为偏序；
7. 各坐标为加法群时，gainDifference 满足自差为零与三点 cocycle；无来源权重时不能由 GainVector 唯一推出标量排名；
8. Revise 只产生下一轮承诺候选时旧轮结算保持不变；
9. 时域逃逸是 ExpansionEscape 的实例。

涉及概率泛化、显著性、独立复验效力、VOI 最优性和复用折减率的结论必须作为带前件接口，不进入纯定义层的无条件定理。

## 54.4 裁决层的最终结算

DECT v1.0 回答定义如何切开目标残差；v1.1 回答科学如何成为递归定义图。本增订回答递归系统何时有资格把一次改善记为科学进步。

其最小承诺对象为

\[
\boxed{
\mathsf{PROGRESS\ CLAIM}_n = ( K_n, \operatorname{CommittedArtifact}_n, Z_n, \operatorname{NonAnticipating}, \operatorname{OriginalCoordinateVerdict}, \mathbf G_n(\cdot\mid a_{\varnothing}), \mathbf G_n(\cdot\mid a_{\min}), \operatorname{ScopeReceipt} ).
}
\]

因此：

\[
\boxed{
\begin{aligned}
\mathsf{ADAPTATION}
&=\text{系统利用已见证据改变下一轮};
\\
\mathsf{POSTDICTION}
&=\text{系统在已见证据上形成回顾改善};
\\
\mathsf{PROSPECTIVE\ PROGRESS}
&=\text{冻结被承诺对象后在新裁决记录上按原坐标改善};
\\
\mathsf{LAUNDERING}
&=\text{到达后改保护坐标、重评旧轮并冒充原承诺};
\\
\mathsf{TRANSPORT}
&=\text{携带有效且可失败的证书把旧域主张送往新域}.
\end{aligned}
}
\]

最终判断是：

\[
\boxed{
\text{科学进步不是分数变高； 而是一个来源可追、范围可审、目标不回写的承诺， 在其尚不可达的新记录上经受原坐标裁决后取得改善。}
}
\]

---

# 追加账本增订
## v1.2 — 2026-08-24

追加存入：

- 版本化证据滤过与首次可达时刻；
- Generate/Tune/Select/Adjudicate/Replicate 五类证据角色；
- 带唯一事件号的有限有序角色日志、日志导出角色集合、污染闭包与裁决准入；
- 前视承诺 \(K_n\) 的目标来源链、范围、比较器、检验计划、基线、权重规范与被承诺对象；
- 冻结、非预见性与 PostdictiveFit；
- 带零自损失、无罚项与保零聚合前件的事后复制骨架；
- Target、Question、Agenda 的有类型节点；
- 议程残差 \(\mathcal E_{\mathrm{agenda}}(q_A;G)\)；
- 目标变更事件、旧轮守恒与三合取 target laundering；
- 外生只读目的 \(G\)、外生 \(\operatorname{OrientationSpec}_G\) 与定向算子 \(\operatorname{Orient}_G\)；
- 范围限制、扩域逃逸对、外推证书及其有效性谓词；
- 无有效证书普遍化的越权主张与扩域重新打开；
- 公共绝对坐标 \(v(a)\) 及其逐对差分五维增益账；
- 行动上的 Pareto 预序与按同向量取商后的偏序；
- 绑定被承诺行动和预登记基线的新记录前瞻科学增益；
- 适应性证据复用折减的 open 接口；
- Define 产候选束、Commit 冻结其对象的有类型裁决循环；
- 原坐标结算、下一轮修订与 Pareto 停止；
- 与第 3、8、14、22—27、33—35、38—39、43 部的显式接线；
- canonical 命名空间下的最小可形式化定义与条件骨架；
- 整体组合 suspected-novel、未做系统文献检索的主张边界。

后续增订继续严格追加于本节之后。

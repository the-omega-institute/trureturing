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

其中 \(\operatorname{EventId}\) 唯一，\(\operatorname{Deps}\) 记录该次使用触及的直接依赖对象。定义角色账本为有限有序日志；事件号严格递增，并要求轮次与 \(\operatorname{Time}\) 沿事件号不减：

\[
\mathcal L_{\mathrm{role}} := (e_1,\ldots,e_N), \qquad \operatorname{EventId}(e_i)\neq\operatorname{EventId}(e_j)\ (i\neq j).
\]

令 \(d_n\) 与 \(\tau_n\) 分别为第 \(n\) 轮裁决事件号与裁决时间，且冻结事件号 \(t_n\le d_n\)。对角色账本与该裁决快照，先定义全日志有效性

\[
\operatorname{ValidTrace}(\mathcal L_{\mathrm{role}},K_n)
\Longleftrightarrow
\forall e\in\mathcal L_{\mathrm{role}},\
e.\operatorname{evidence}\in\mathcal F_{\operatorname{EventId}(e)}.
\]

这是角色账本与裁决快照的全日志有效性不变量。只有给出该证明，裁决消费者才可读取角色事件；任一已记录事件与同事件号处的 filtration 错配时，整份快照即被拒绝。

在此有效性前提下，定义裁决前缀

\[
\begin{aligned}
\mathcal L_{\mathrm{role},\preceq d_n}
:=\{e\in\mathcal L_{\mathrm{role}}:\;&
\operatorname{EventId}(e)\le d_n,\ e.n\le n,
\\
&e.\operatorname{Time}\le\tau_n\}.
\end{aligned}
\]

该前缀只施加事件号、轮次与时间约束，不再逐事件过滤可见性。账本一致性是裁决前提，错配即拒绝整个快照，不能静默抹去事件后继续裁决。

同内容的重复使用因事件号不同而不被折叠。对同一记录同一轮，角色不是单值函数，而是由该裁决快照导出的集合谓词

\[
\operatorname{Roles}_{\mathcal L}^{\preceq d_n}(r,n)
:=\{\rho:\exists e\in\mathcal L_{\mathrm{role},\preceq d_n},\ e.\operatorname{evidence}=r,\ e.n=n,\ e.\mathsf{role}=\rho\}.
\]

角色不是记录的永久本质；它是记录、轮次、协议和访问时间的关系。一个记录在第 \(n\) 轮用于选择后，不能仅靠重新命名就在同一轮变成未见的裁决记录。账本扩展只允许在尾部追加事件号更大的事件，因此第 \(n+1\) 轮追加不能改变已冻结的 \(\mathcal L_{\mathrm{role},\preceq d_n}\)。

## 48.3 角色准入与污染闭包

对承诺 \(K_n\) 和记录 \(r\)，以反身传递依赖闭包定义可达关系

\[
r\leadsto K_n \quad\Longleftrightarrow\quad r\in\operatorname{Dep}^*(K_n).
\]

令一次角色事件触及承诺闭包，当且仅当其 \(\operatorname{Deps}\) 与 \(\operatorname{Dep}^*(K_n)\) 相交。由账本定义适应性使用谓词

\[
\operatorname{AdaptiveUse}_{\mathcal L}^{\preceq d_n}(r,K_n)
\Longleftrightarrow
\exists e\in\mathcal L_{\mathrm{role},\preceq d_n},\
e.\operatorname{evidence}=r,\
e.\mathsf{role}\in\{\mathsf{Generate},\mathsf{Tune},\mathsf{Select}\},\
e.\operatorname{Deps}\cap\operatorname{Dep}^*(K_n)\neq\varnothing.
\]

定义第 \(n\) 轮裁决准入

\[
\boxed{
\operatorname{AdmissibleJudge}_{\mathcal L}^{\preceq d_n}(r,K_n)
\Longleftrightarrow
\mathsf{Adjudicate}\in\operatorname{Roles}_{\mathcal L}^{\preceq d_n}(r,n)
\ \wedge\ t_n<\operatorname{FirstSeen}(r)
\ \wedge\ r\not\leadsto K_n
\ \wedge\ \neg\operatorname{AdaptiveUse}_{\mathcal L}^{\preceq d_n}(r,K_n).
}
\]

这里的轮次 \(n\)、冻结点 \(t_n\) 与裁决点 \(d_n\) 都是 \(K_n\) 冻结快照的字段，不是调用者另行传入的自由参数。若 \(\mathcal L'=\mathcal L\mathbin{+\!+}\Delta\) 且 \(\Delta\) 中事件号均大于 \(d_n\)，则上式两侧对 \(\mathcal L\) 与 \(\mathcal L'\) 逐字相同；未来追加 Tune 或 Adjudicate 事件不能翻转旧轮准入。

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
\begin{aligned}
\operatorname{FrozenBefore}(K_n,z_n)
\Longleftrightarrow{}
&z_n\in\mathcal F_{d_n}
\\
&\wedge\ z_n\notin\mathcal F_{t_n}.
\end{aligned}
\]

等价地，\(t_n<u_n\le d_n\)：裁决记录必须在裁决点正向到达，而不是仅仅在冻结点尚未出现；从未被观察的记录不满足此前件。

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

其中重评必须携带实际评价见证

\[
v'_n=\operatorname{Evaluate}(K'_n,Z_n),
\]

而不能用一个可任意置真的标签代替。

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

其中 \(\operatorname{PreorderProof}\) 证明 \(\preceq_G\) 在声明范围内为预序。

\[
D_G:=\operatorname{AdmTarget}(G)\cap\operatorname{Scope}(\operatorname{OrientationSpec}_G),
\qquad
\operatorname{PreorderProof}:\operatorname{Preorder}(\preceq_G\!\upharpoonright_{D_G}).
\]

因此关系在 \(D_G\) 外不提供比较事实；\(\operatorname{Scope}\) 是反身律、传递律与关系闭包的共同前件，不是未消费的元数据。定义定向算子为该规范包的投影

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

其中旧域收据锁定原版本、原记录与原误差，并保存被运输主张的内容地址；运输假设说明哪些结构在域变换下保持；可失败预测必须在 \(J'\setminus J\) 上预登记定义域，并刻画至少一个非空失败事件。

若运输还依赖选择机制、干预一致性、协变量变换或损失稳定性，这些必须进入运输假设，不得藏在“同类情形”一词中。

给定证书 \(\kappa\)、主张 \(c\) 及其版本 \(\nu\)，定义有效外推证书

\[
\boxed{
\begin{aligned}
\operatorname{ValidTransportCert}(\kappa,c;J,J',\nu)
\Longleftrightarrow{}
&\operatorname{ReceiptMatches}
(\kappa.\operatorname{Receipt},\operatorname{ClaimAddress}(c),J,\nu)
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
\operatorname{PredictionDefined}(\kappa,z)
\\
&\wedge\
\exists z\in J'\setminus J,\
\operatorname{PredictionDefined}(\kappa,z)
\wedge\operatorname{PredictionFails}(\kappa,z)
\wedge\operatorname{Refutes}(z,\kappa,c).
\end{aligned}
}
\]

第一项把收据同时绑定原域、版本和该主张的内容地址；第二项只给出保留明列前件的条件运输；后两项分别要求预测覆盖整个新域差并存在被预先刻画的失败见证。故把 \(\operatorname{PredictionFails}\) 取恒假不再能真空满足证书。定义

\[
\operatorname{HasValidTransportCert}(c;J,J')
\Longleftrightarrow
\exists\kappa,\operatorname{ValidTransportCert}
(\kappa,c;J,J',\operatorname{Version}(c)).
\]

这个存在闭包由同一 claim-bound 谓词构造，不接收外部布尔门。仅有三元组数据而不满足此谓词，不构成外推门票。

## 51.4 越权主张与重新打开

令运输报告 \(q=(c,J',\Gamma_q)\)，其中 \(\Gamma_q\) 是报告保留的条件。定义有许可证报告

\[
\begin{aligned}
\operatorname{LicensedReport}(q;J,J')
\Longleftrightarrow
\exists\kappa,\ {}
&\operatorname{ValidTransportCert}
(\kappa,c;J,J',\operatorname{Version}(c))
\\
&\wedge\
\bigl(\Gamma_q\Longleftrightarrow
\operatorname{GivenPremises}(\kappa)
\wedge\kappa.\operatorname{TransportAssumption}\bigr).
\end{aligned}
\]

因此无条件报告取 \(\Gamma_q=\top\) 时，必须同时给出全部前件与运输假设的证明；前件未证时，报告只能原样保留该合取作为条件。定义越权普遍化

\[
\boxed{
\operatorname{Overreach}(q;J,J')
\Longleftrightarrow
J\subsetneq J'
\ \wedge\ \operatorname{Scope}(c)=J
\ \wedge\ q\text{ 被报告为覆盖 }J'
\ \wedge\ \neg\operatorname{LicensedReport}(q;J,J').
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

若有运输证书及其全部前件，才可去条件化；否则只能建立并按原条件报告特定的条件运输定理。

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

相对于当前行动 \(a_0\)，纯 Pareto 账最多给出描述性谓词

\[
\operatorname{NoDominatingCandidate}(K_n,a_0)
\Longleftrightarrow
a_0\in\operatorname{Candidates}(K_n)
\ \wedge\ \nexists a\in\operatorname{Candidates}(K_n),\ a\succ_{K_n}a_0.
\]

它要求 \(a_0\) 本身属于当前候选集，并只说明它位于当前候选前沿；不可比候选仍可能满足承诺并带来更高收益，故该谓词不构成停止的充分条件。

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

令 \(\mathcal L_{\mathrm{role},\preceq d_n}\) 为第 48 部绑定 \(K_n\) 裁决点的事件前缀，并要求 \(\operatorname{ValidTrace}(\mathcal L_{\mathrm{role}},K_n)\) 的证明。对同一证据在承诺闭包上的反复适应性使用，定义复用深度

\[
\operatorname{ReuseDepth}(r,K_n)
:=\left|\left\{
e\in\mathcal L_{\mathrm{role},\preceq d_n}:
e.\operatorname{evidence}=r,\
e.\mathsf{role}\in\{\mathsf{Generate},\mathsf{Tune},\mathsf{Select}\},\
e.\operatorname{Deps}\cap\operatorname{Dep}^*(K_n)\neq\varnothing
\right\}\right|\in\mathbb N.
\]

唯一事件号使内容相同但实际发生多次的适应性使用分别计数；有限前缀保证该深度落在折减函数的自然数定义域。\(\mathsf{Adjudicate}\) 与 \(\mathsf{Replicate}\) 不增加该深度，因为它们不是候选生成、调参或选择动作。

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

为使其可裁决，本部令 \(\mathsf{Define}\) 先产生带预测、行动或模型分量的有限有类型候选束，再由 \(\mathsf{Commit}\) 把选定对象连同目标、范围、比较器、计划、基线和权重规范封入承诺：

\[
\mathsf{Define}:\Sigma_n\to\operatorname{CandidateBundle}_n, \qquad \mathsf{Commit}:\operatorname{CandidateBundle}_n\to(K_n,\operatorname{Seal}(K_n)).
\]

\[
\boxed{
\Sigma_n\xrightarrow{\mathsf{Define}}\operatorname{CandidateBundle}_n\xrightarrow{\mathsf{Commit}}K_n\xrightarrow{\mathsf{Observe}}Z_n\xrightarrow{\mathsf{Compare}}\operatorname{Verdict}_n\xrightarrow{\mathsf{Revise}}\Sigma_{n+1}^{-}\xrightarrow{\mathsf{Reflect}}\Sigma_{n+1}.
}
\]

并要求 \(\operatorname{CommittedArtifact}_n\subseteq\operatorname{CandidateBundle}_n\)，且 \(\operatorname{Seal}(K_n)\) 保存整个 \(K_n\)、冻结事件号与 \(\operatorname{Dep}^*(K_n)\)，其摘要以这三者为完整输入。故同一冻结号和同一有限子束若带有不同坐标或依赖闭包，也不能复用同一 Seal。该包含关系是 \(\mathsf{Commit}\) 的输出定律，不是下游证明者可另行选择的谓词。这不是删除预测；预测从可随时变化的中间动作变成承诺 \(K_n\) 的冻结字段，且不能在观察 \(Z_n\) 后从表外补入。

## 53.2 单轮状态转换

令 \(s_n\) 为第 \(n\) 轮 \(\mathsf{Define}\) 开始前的最后事件号。以 \(s_n\) 的事件前缀而非整轮最终日志接入内涵账本：

\[
\mathcal L_n:=\mathcal L_{\mathrm{source},\preceq s_n}\sqcup\mathcal L_{\mathrm{role},\preceq s_n}.
\]

定义轮状态

\[
\Sigma_n = (S_n,\mathcal F_{s_n},\mathcal L_{\mathrm{source},\preceq s_n}\sqcup\mathcal L_{\mathrm{role},\preceq s_n},\mathcal R_n).
\]

其中 \(s_n<t_n\le d_n\)：\(s_n\) 固定 Define 输入，\(t_n\) 固定 Commit，\(d_n\) 固定 Compare 所消费的裁决快照。旧轮结算保存 \((K_n,\mathcal L_{\mathrm{role},\preceq d_n})\) 的内容地址；后续只在尾部追加更大事件号，不能把同轮 Define 之后或下一轮事件回填进 \(\Sigma_n\) 或旧裁决。

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

无来源权重时，\(\operatorname{NoDominatingCandidate}\) 只返回前沿状态，不输出 Stop。若要得到停止判词，必须消费第 50.5 部的外生 \(\operatorname{OrientationSpec}_G\)，或由 \(K_n\) 中已有来源、版本与范围的 \(\operatorname{WeightSpec}_n\) 诱导同类预序。令

\[
\operatorname{Feas}_n
:=\operatorname{Candidates}(K_n)\cap\operatorname{SuffAlt}(K_n)
\]

并令 \(\operatorname{Current}(K_n)\) 为可空的当前行动。空候选束、空可行集或没有当前行动都是合法轮次；只有停止判词才要求存在当前可行行动。对外生关系 \(\preceq_G\) 定义

\[
\boxed{
\begin{aligned}
&\operatorname{OrientedStop}(K_n,\operatorname{OrientationSpec}_G)
\\
&\Longleftrightarrow
\exists a_{\mathrm{cur}},\
\operatorname{Current}(K_n)=\operatorname{some}(a_{\mathrm{cur}})
\\
&\qquad\wedge\ a_{\mathrm{cur}}\in\operatorname{Feas}_n
\\
&\qquad\wedge\ \nexists a\in\operatorname{Feas}_n,\
a_{\mathrm{cur}}\prec_G a.
\end{aligned}
}
\]

这里可行性先于偏好比较，且关系只在规范声明范围与 \(\operatorname{AdmTarget}(G)\) 内求值。于是候选只有 \(a_{\min}=(1,1,0)\)、不做为 \((0,0,0)\) 的反例中，若当前仍是不做，则 \(a_{\mathrm{cur}}\notin\operatorname{Feas}_n\)，不能裁停；纯 Pareto 不可比也只产生 \(\operatorname{NoDominatingCandidate}\)。若当前行动为空或 \(a_{\min}\) 不存在，则记录当前充分替代前沿而不裁停。停止仍是当前承诺、候选集与证据状态下的局部结论；范围扩张、目标变更或新方法出现时按第 43 部重新打开。

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
- 第 22 部的内涵定义保存来源与依赖；第 48 部的有限有序角色日志以带标签分量类型化进入 \(\mathcal L_n\)，角色集合、复用深度与裁决准入均由 \(K_n\) 的事件前缀导出，未来追加不参与旧轮判词。
- 第 23 部的有类型定义图承载 Target、Question、Agenda 及其版本边；候选预测、行动或模型分量以有限子束从 \(\operatorname{CandidateBundle}_n\) 投影为 \(\operatorname{CommittedArtifact}_n\)，连同包含见证冻结进 \(K_n\)。
- 第 24 部的实验计划 \(\pi\) 进入 \(K_n\) 的 TestPlan；模型纤维不得与裁决有效性混为一谈。
- 第 25 部说明压平会遗失来源；故承诺不能只保存最终评分函数，必须保存依赖闭包。
- 第 26—27 部的对象层与方法层残差继续生成候选，但候选何时可获前瞻信用由裁决层另行决定。
- 第 33 部的记录接口提供 Observe 与 Predict 的共同载体；第 49 部在两者之间加入不可逆的冻结点。
- 第 34 部的客观性自然性不替代非预见性；跨协议相容与未见记录裁决是两个独立条件。
- 第 35 部的 \((J,\varepsilon,\mathcal C)\) 成为承诺范围与外推证书的源域收据；收据还绑定被运输 claim 的内容地址，预测须在非空新域差上有定义与失败见证，未证前件必须保留在报告条件中。
- 第 38 部的表面消残在第 50 部被细化为三合取目标漂白事件，不以分数是否变化代替保护坐标是否被回写。
- 第 39 部的六元结构由第 53 部补成带 Commit 的裁决循环；Define 先产有限有类型候选束，Commit 再以输出定律把其中对象与对应 Seal 封入承诺。
- 第 43 部的 Gain/cost 停止接到第 52 部增益账与第 50.5 部外生定向规范；纯 Pareto 只报告无支配候选，不构成停止充分条件；扩域、改目标或新证据仍触发重新打开。

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

structure EvidenceFiltration
    (EventId Evidence : Type u) [Preorder EventId] where
  seen : EventId → Set Evidence
  monotone : ∀ {i j}, i ≤ j → seen i ⊆ seen j

structure RoleLedger
    (EventId Evidence Round Artifact Protocol Time : Type u)
    [LinearOrder EventId] [Preorder Round] [Preorder Time] where
  events : List (UseEvent EventId Evidence Round Artifact Protocol Time)
  uniqueEventIds : (events.map fun e => e.eventId).Nodup
  strictEventOrder :
    events.Pairwise (fun e e' => e.eventId < e'.eventId)
  indexRespectsRound : ∀ {e e'}, e ∈ events → e' ∈ events →
    e.eventId ≤ e'.eventId → e.round ≤ e'.round
  indexRespectsTime : ∀ {e e'}, e ∈ events → e' ∈ events →
    e.eventId ≤ e'.eventId → e.usedAt ≤ e'.usedAt

def RolePrefixAtEvent
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (cutoff : EventId) :
    Set (UseEvent EventId Evidence Round Artifact Protocol Time) :=
  {e | e ∈ L.events ∧ e.eventId ≤ cutoff}

def RolePrefixAtRound
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (n : Round) :
    Set (UseEvent EventId Evidence Round Artifact Protocol Time) :=
  {e | e ∈ L.events ∧ e.round ≤ n}

def RolePrefixAtTime
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (cutoff : Time) :
    Set (UseEvent EventId Evidence Round Artifact Protocol Time) :=
  {e | e ∈ L.events ∧ e.usedAt ≤ cutoff}

structure AdjudicationSnapshot
    (EventId Evidence Round Artifact Time : Type u)
    [Preorder EventId] [Preorder Time] (n : Round) where
  freezeEvent : EventId
  decisionEvent : EventId
  frozenAt : Time
  decidedAt : Time
  freezeBeforeDecision : freezeEvent ≤ decisionEvent
  timeBeforeDecision : frozenAt ≤ decidedAt
  filtration : EvidenceFiltration EventId Evidence
  dependencyClosure : Set Artifact
  evidenceDependencies : Set Evidence

def AppendOnlyExtension
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {n : Round}
    (old new : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (K : AdjudicationSnapshot EventId Evidence Round Artifact Time n) : Prop :=
  ∃ tail, new.events = old.events ++ tail ∧
    ∀ e, e ∈ tail → K.decisionEvent < e.eventId

def ValidTrace
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {n : Round}
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (K : AdjudicationSnapshot EventId Evidence Round Artifact Time n) : Prop :=
  ∀ e, e ∈ L.events → e.evidence ∈ K.filtration.seen e.eventId

def InAdjudicationPrefix
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {n : Round}
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (K : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (_validTrace : ValidTrace L K)
    (e : UseEvent EventId Evidence Round Artifact Protocol Time) : Prop :=
  e ∈ RolePrefixAtEvent L K.decisionEvent ∧
    e ∈ RolePrefixAtRound L n ∧ e ∈ RolePrefixAtTime L K.decidedAt

def RolesAt
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {n : Round}
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (K : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (validTrace : ValidTrace L K)
    (r : Evidence) : Set EvidenceRole :=
  {ρ | ∃ e, InAdjudicationPrefix L K validTrace e ∧ e.evidence = r ∧
    e.round = n ∧ e.role = ρ}

def AdaptiveUseInClosure
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {n : Round}
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (K : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (validTrace : ValidTrace L K)
    (r : Evidence) : Prop :=
  ∃ e, InAdjudicationPrefix L K validTrace e ∧ e.evidence = r ∧
    (e.role = .generate ∨ e.role = .tune ∨ e.role = .select) ∧
    Set.Nonempty (e.dependencies ∩ K.dependencyClosure)

def AdmissibleJudge
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {n : Round}
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (K : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (validTrace : ValidTrace L K)
    (r : Evidence) : Prop :=
  .adjudicate ∈ RolesAt L K validTrace r ∧
    r ∉ K.filtration.seen K.freezeEvent ∧
    r ∉ K.evidenceDependencies ∧
      ¬ AdaptiveUseInClosure L K validTrace r

noncomputable def ReuseDepth
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {n : Round}
    (L : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (K : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (validTrace : ValidTrace L K)
    (r : Evidence) : Nat := by
  classical
  exact (L.events.filter fun e =>
    InAdjudicationPrefix L K validTrace e ∧ e.evidence = r ∧
      (e.role = .generate ∨ e.role = .tune ∨ e.role = .select) ∧
      Set.Nonempty (e.dependencies ∩ K.dependencyClosure)).length

structure OrientationSpec
    (Goal Target Source Version Scope : Type u)
    (AdmTarget : Goal → Set Target)
    (InScope : Scope → Target → Prop) where
  goal : Goal
  relation : Target → Target → Prop
  source : Source
  version : Version
  scope : Scope
  relationInDeclaredDomain : ∀ {a b}, relation a b →
    a ∈ AdmTarget goal ∧ b ∈ AdmTarget goal ∧
      InScope scope a ∧ InScope scope b
  refl : ∀ a, a ∈ AdmTarget goal → InScope scope a → relation a a
  trans : ∀ {a b c},
    a ∈ AdmTarget goal → b ∈ AdmTarget goal → c ∈ AdmTarget goal →
    InScope scope a → InScope scope b → InScope scope c →
    relation a b → relation b c → relation a c

structure CandidateBundle (Artifact : Type u) [DecidableEq Artifact] where
  artifacts : Finset Artifact

structure DecisionSet (Action : Type u) [DecidableEq Action] where
  candidates : Finset Action
  feasible : Finset Action
  current : Option Action
  feasibleFromCandidates : feasible ⊆ candidates

structure ProspectiveCommitment
    (EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u)
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    (n : Round) where
  adjudication : AdjudicationSnapshot EventId Evidence Round Artifact Time n
  targetChain : TargetChain
  domain : Domain
  epsilon : Epsilon
  conditions : Condition
  comparator : Comparator
  testPlan : TestPlan
  baseline : Baseline
  weightSpec : WeightSpec
  decision : DecisionSet Artifact
  committedArtifacts : Finset Artifact
  baselineArtifacts : Finset Artifact
  committedFromCandidates : committedArtifacts ⊆ decision.candidates
  baselinesFromCandidates : baselineArtifacts ⊆ decision.candidates
  committedInClosure : ∀ a, a ∈ committedArtifacts →
    a ∈ adjudication.dependencyClosure

structure CommitmentSeal
    (Digest Commitment EventId Artifact : Type u)
    (digestOf : Commitment → EventId → Set Artifact → Digest)
    (K : Commitment) (freezeEvent : EventId)
    (dependencyClosure : Set Artifact) where
  digest : Digest
  digestCovers : digest = digestOf K freezeEvent dependencyClosure
  sealedCommitment : Commitment
  sealsCommitment : sealedCommitment = K
  sealedFreezeEvent : EventId
  sealsFreezeEvent : sealedFreezeEvent = freezeEvent
  sealedDependencyClosure : Set Artifact
  sealsDependencyClosure : sealedDependencyClosure = dependencyClosure

structure CommitInterface
    (RoundState Digest EventId Evidence Round Artifact Time TargetChain Domain
      Epsilon Condition Comparator TestPlan Baseline WeightSpec : Type u)
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    (n : Round) where
  defineStep : RoundState → CandidateBundle Artifact
  digestOf :
    ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain Domain
      Epsilon Condition Comparator TestPlan Baseline WeightSpec n →
      EventId → Set Artifact → Digest
  commitStep : (bundle : CandidateBundle Artifact) →
    Σ K : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n,
      CommitmentSeal Digest
        (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
          Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
        EventId Artifact digestOf K K.adjudication.freezeEvent
          K.adjudication.dependencyClosure
  candidateBundlePreserved : ∀ bundle,
    (commitStep bundle).1.decision.candidates = bundle.artifacts
  committedFromInput : ∀ bundle,
    (commitStep bundle).1.committedArtifacts ⊆ bundle.artifacts

def NonAnticipating
    {EventId Evidence Round Artifact Time : Type u}
    [Preorder EventId] [Preorder Time] {n : Round}
    (K : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (Z : Evidence) : Prop :=
  Z ∈ K.filtration.seen K.decisionEvent ∧
    Z ∉ K.filtration.seen K.freezeEvent ∧ Z ∉ K.evidenceDependencies

structure ProtectedCoordinates
    (TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec : Type u) where
  targetChain : TargetChain
  domain : Domain
  epsilon : Epsilon
  conditions : Condition
  comparator : Comparator
  baseline : Baseline
  weightSpec : WeightSpec

def protectedCoordinates
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (K : ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n) :
    ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
      Baseline WeightSpec :=
  { targetChain := K.targetChain
    domain := K.domain
    epsilon := K.epsilon
    conditions := K.conditions
    comparator := K.comparator
    baseline := K.baseline
    weightSpec := K.weightSpec }

structure RegradeReport
    (Commitment Evidence Verdict Time : Type u)
    (evaluate : Commitment → Evidence → Verdict) where
  original : Commitment
  revised : Commitment
  evidence : Evidence
  regradedVerdict : Verdict
  regradesOldRound : regradedVerdict = evaluate revised evidence
  attributedTo : Commitment
  occurredAt : Time

def TargetLaundering
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Verdict : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (evaluate :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n →
        Evidence → Verdict)
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence)
    (report : RegradeReport
      (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
      Evidence Verdict Time evaluate) : Prop :=
  Z ∈ newK.adjudication.filtration.seen newK.adjudication.freezeEvent ∧
    protectedCoordinates newK ≠ protectedCoordinates oldK ∧
    report.original = oldK ∧ report.revised = newK ∧
    report.evidence = Z ∧ report.regradedVerdict = evaluate newK Z ∧
    report.attributedTo = oldK ∧
    report.occurredAt = newK.adjudication.frozenAt

def ExpansionEscape
    {Model : Type u} {ReadoutJ : Type v} {ReadoutJ' : Type w}
    (PJ : Model → ReadoutJ) (PJ' : Model → ReadoutJ') :
    Model → Model → Prop :=
  fun x y => PJ x = PJ y ∧ PJ' x ≠ PJ' y

structure TransportCert
    (TruthReceipt NewDomainPrediction : Type u) where
  oldReceipt : TruthReceipt
  givenPremises : Prop
  transportAssumption : Prop
  falsifiablePrediction : NewDomainPrediction

structure TransportReport (Claim Domain : Type u) where
  claim : Claim
  reportedDomain : Domain
  condition : Prop

structure TransportSemantics
    (TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u) where
  claimAddress : Claim → ContentAddress
  claimScope : Claim → Domain
  claimVersion : Claim → Version
  receiptMatches : TruthReceipt → ContentAddress → Domain → Version → Prop
  strictSubset : Domain → Domain → Prop
  claimOn : Claim → Domain → Prop
  inNewOnlyDomain : NewEvidence → Domain → Domain → Prop
  predictionDefined : NewDomainPrediction → NewEvidence → Prop
  predictionFails : NewDomainPrediction → NewEvidence → Prop
  refutes : NewEvidence → TransportCert TruthReceipt NewDomainPrediction →
    Claim → Prop

def ValidTransportCert
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    (S : TransportSemantics TruthReceipt NewDomainPrediction Claim
      ContentAddress Domain Version NewEvidence)
    (cert : TransportCert TruthReceipt NewDomainPrediction) (claim : Claim)
    (J J' : Domain) (version : Version) : Prop :=
  S.strictSubset J J' ∧
    S.receiptMatches cert.oldReceipt (S.claimAddress claim) J version ∧
    (cert.givenPremises → cert.transportAssumption → S.claimOn claim J') ∧
    (∀ z, S.inNewOnlyDomain z J J' →
      S.predictionDefined cert.falsifiablePrediction z) ∧
    ∃ z, S.inNewOnlyDomain z J J' ∧
      S.predictionDefined cert.falsifiablePrediction z ∧
      S.predictionFails cert.falsifiablePrediction z ∧ S.refutes z cert claim

def HasValidTransportCert
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    (S : TransportSemantics TruthReceipt NewDomainPrediction Claim
      ContentAddress Domain Version NewEvidence)
    (claim : Claim) (J J' : Domain) : Prop :=
  ∃ cert, ValidTransportCert S cert claim J J' (S.claimVersion claim)

def Overreach
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    (S : TransportSemantics TruthReceipt NewDomainPrediction Claim
      ContentAddress Domain Version NewEvidence)
    (report : TransportReport Claim Domain) (J : Domain) : Prop :=
  S.strictSubset J report.reportedDomain ∧ S.claimScope report.claim = J ∧
    ¬ ∃ cert, ValidTransportCert S cert report.claim J report.reportedDomain
      (S.claimVersion report.claim) ∧
      (report.condition ↔ cert.givenPremises ∧ cert.transportAssumption)

structure GainVector
    (Information Residual Transfer Cost Risk : Type u) where
  information : Information
  residualCapture : Residual
  transfer : Transfer
  lifecycleCost : Cost
  risk : Risk

def gainDifference
    {Action Information Residual Transfer Cost Risk : Type u}
    [Sub Information] [Sub Residual] [Sub Transfer] [Sub Cost] [Sub Risk]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (a b : Action) : GainVector Information Residual Transfer Cost Risk :=
  { information := (value a).information - (value b).information
    residualCapture :=
      (value a).residualCapture - (value b).residualCapture
    transfer := (value a).transfer - (value b).transfer
    lifecycleCost := (value a).lifecycleCost - (value b).lifecycleCost
    risk := (value a).risk - (value b).risk }

def ParetoWeak
    {Action Information Residual Transfer Cost Risk : Type u}
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (a b : Action) : Prop :=
  (value b).information ≤ (value a).information ∧
    (value b).residualCapture ≤ (value a).residualCapture ∧
    (value b).transfer ≤ (value a).transfer ∧
    (value a).lifecycleCost ≤ (value b).lifecycleCost ∧
    (value a).risk ≤ (value b).risk

def ParetoStrict
    {Action Information Residual Transfer Cost Risk : Type u}
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (a b : Action) : Prop :=
  ParetoWeak value a b ∧ ¬ ParetoWeak value b a

def NoDominatingCandidate
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [LE Information] [LE Residual] [LE Transfer] [LE Cost] [LE Risk]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (D : DecisionSet Action) : Prop :=
  ∃ current, D.current = some current ∧
    current ∈ D.candidates ∧
    ¬ ∃ a, a ∈ D.candidates ∧ ParetoStrict value a current

def OrientedStopOnDecisionSet
    {Goal Action Source Version Scope : Type u}
    [DecidableEq Action]
    (AdmTarget : Goal → Set Action) (InScope : Scope → Action → Prop)
    (O : OrientationSpec Goal Action Source Version Scope AdmTarget InScope)
    (D : DecisionSet Action) : Prop :=
  ∃ current, D.current = some current ∧ current ∈ D.feasible ∧
    (∀ a, a ∈ D.feasible → a ∈ AdmTarget O.goal ∧ InScope O.scope a) ∧
    ¬ ∃ a, a ∈ D.feasible ∧ O.relation current a ∧
      ¬ O.relation a current

def OrientedStop
    {Goal Source Version Scope EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Action]
    (AdmTarget : Goal → Set Action) (InScope : Scope → Action → Prop)
    (O : OrientationSpec Goal Action Source Version Scope AdmTarget InScope)
    {n : Round}
    (K : ProspectiveCommitment EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n) : Prop :=
  OrientedStopOnDecisionSet AdmTarget InScope O K.decision

def ScientificGain
    {EventId Evidence Round Action Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    {Loss : Type v} [LT Loss]
    [LinearOrder EventId] [Preorder Time] [DecidableEq Action]
    {n : Round}
    (evaluate : Comparator → Action → Evidence → Loss)
    (K : ProspectiveCommitment EventId Evidence Round Action Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
    (Z : Evidence) (a b : Action) : Prop :=
  a ∈ K.committedArtifacts ∧ b ∈ K.baselineArtifacts ∧
    NonAnticipating K.adjudication Z ∧
    evaluate K.comparator a Z < evaluate K.comparator b Z

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
```


PostdictiveFit 直接由 \(\operatorname{Improves}\wedge\neg\operatorname{NonAnticipating}\) 派生，不另列为原语。

首先应证明或检查：

1. ValidTrace 把每个已记录角色事件绑定到自身事件号处的 filtration，且所有消费者要求该证明，故错配账本不能靠静默过滤事件而通过；AppendOnlyExtension 绑定旧 K 的 decisionEvent，并要求尾部事件号均大于该点，故 InAdjudicationPrefix 的事件号、轮次和时间前缀及其消费者在旧轮逐项不变；
2. 依赖闭包污染下裁决准入反单调，ReuseDepth 只计裁决前缀内触及闭包的 Generate/Tune/Select；
3. NonAnticipating 同时要求裁决点已见、冻结点未见且无依赖污染，故从未观察的 Z 不能取得 ScientificGain；查表复制器零回顾损失与非预见失败可同时成立；
4. CommitInterface 的输出 Seal 以整个 K、冻结事件号与依赖闭包为摘要输入并逐项保存，且 committedArtifacts 是输入 CandidateBundle 的有限子集并进入依赖闭包；
5. protectedCoordinates 是 ProspectiveCommitment 的直接投影，单改 Condition 必使坐标差成立；RegradeReport 对以新坐标评价旧证据的实际 verdict 等式给出证明，TargetLaundering 合取该等式；
6. ValidTransportCert 的收据绑定 claim 内容地址，新域差上预测有定义且存在失败见证；Overreach 只能由该谓词的存在闭包解除；
7. \(J\subseteq J'\) 时 \(\ker P_{J'}\subseteq\ker P_J\)；
8. 在限制律成立时，扩域逃逸为空当且仅当两域预测核相同；
9. 五个异型坐标各自为预序时，公共绝对坐标诱导的 Pareto 弱支配在行动上为预序；各坐标为偏序时，按同向量等价取商后为偏序；
10. 五个异型坐标各自为加法群时，gainDifference 满足自差为零与三点 cocycle；无来源权重时 NoDominatingCandidate 不能推出 Stop；
11. DecisionSet 允许空候选束、空可行集与空 current；OrientedStop 才要求 current 为某个可行行动，并只消费 K.decision 与声明范围内的外生 OrientationSpec；Revise 只产生下一轮承诺候选时旧轮结算保持不变；
12. 时域逃逸是 ExpansionEscape 的实例。

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
- 带唯一事件号的有限有序角色日志、全日志 ValidTrace、事件/轮次/时间前缀、日志导出角色集合、适应性复用深度、污染闭包与裁决准入；
- 前视承诺 \(K_n\) 的目标来源链、范围、比较器、检验计划、基线、权重规范与被承诺对象；
- 冻结、非预见性与 PostdictiveFit；
- 带零自损失、无罚项与保零聚合前件的事后复制骨架；
- Target、Question、Agenda 的有类型节点；
- 议程残差 \(\mathcal E_{\mathrm{agenda}}(q_A;G)\)；
- 目标变更事件、旧轮守恒、实际重评见证与三合取 target laundering；
- 外生只读目的 \(G\)、外生 \(\operatorname{OrientationSpec}_G\) 与定向算子 \(\operatorname{Orient}_G\)；
- 范围限制、扩域逃逸对、claim-bound 且非真空可失败的外推证书及其有效性谓词；
- 无同谓词证书或丢失条件的越权主张与扩域重新打开；
- 五个异型公共绝对坐标 \(v(a)\) 及其逐对差分增益账；
- 行动上的 Pareto 预序与按同向量取商后的偏序；
- 绑定被承诺行动和预登记基线的新记录前瞻科学增益；
- 适应性证据复用折减的 open 接口；
- Define 产有限候选束、Commit 以包含定律和覆盖全承诺闭包的 Seal 冻结其对象的有类型裁决循环；
- 原坐标结算、下一轮修订、可空决策集、描述性 Pareto 前沿与外生定向停止；
- 与第 3、8、14、22—27、33—35、38—39、43 部的显式接线；
- canonical 命名空间下的最小可形式化定义与条件骨架；
- 整体组合 suspected-novel、未做系统文献检索的主张边界。

后续增订继续严格追加于本节之后。

---

# 第五十五部　裁决层的边界问题

本部只登记开放问题，不给出证明、反例或新定理。以下对象均引用第 48—54 部的既有对象；除陈述 OP1—OP6 所需的有限投影外，不增加裁决层本体。

## 55.1 最小共用定义

固定第 \(n\) 轮 \(\operatorname{ProspectiveCommitment}\) \(K\)、有限记录集 \(Z\)、有限角色账本 \(\mathcal L\) 与证明
\[
v_K:\operatorname{ValidTrace}(\mathcal L,K.\operatorname{adjudication}).
\]
第 54.3 部的 \(\operatorname{AdjudicationSnapshot}\) 仍只指 \(K.\operatorname{adjudication}\)。本部唯一新增的派生名为
\[
\boxed{
\begin{aligned}
&\operatorname{AdjudicationSignature}(K,Z;\mathcal L,v_K)
:=\Bigl(
Z\cap K.\operatorname{adjudication}.\operatorname{filtration}.\operatorname{seen}
  (K.\operatorname{adjudication}.\operatorname{freezeEvent}),\
Z\cap K.\operatorname{adjudication}.\operatorname{filtration}.\operatorname{seen}
  (K.\operatorname{adjudication}.\operatorname{decisionEvent}),\
Z\cap K.\operatorname{adjudication}.\operatorname{evidenceDependencies},
\\
&\quad
\{(e.\operatorname{evidence},e.\operatorname{round},e.\operatorname{role},
\mathbf 1[e.\operatorname{dependencies}\cap
K.\operatorname{adjudication}.\operatorname{dependencyClosure}\neq\varnothing]):
\operatorname{InAdjudicationPrefix}
(\mathcal L,K.\operatorname{adjudication},v_K,e),\
e.\operatorname{evidence}\in Z,
e.\operatorname{role}\in
\{\mathsf{generate},\mathsf{tune},\mathsf{select},\mathsf{adjudicate}\}\}
\Bigr).
\end{aligned}
}
\]
四分量依次为冻结点可见性、裁决点可见性、直接读取 \(\operatorname{evidenceDependencies}\) 的依赖污染，以及**角色存在签名投影**。第四分量只保留消费者所问的角色存在性与“依赖是否触及闭包”这一位；它折叠 \(\operatorname{EventId}\)、\(\operatorname{Time}\)、\(\operatorname{Protocol}\)、具体 \(\operatorname{Deps}\)、事件顺序和重复事件。故它不保存事件多重性，不承载第 48.2、52.5 部 \(\operatorname{ReuseDepth}\) 的复用计数语义，也不得供顺序或复用深度消费者使用。\(\mathsf{replicate}\) 不进入该投影，因为本批四谓词均不读取它。

若 \(S=(S_{\mathrm f},S_{\mathrm d},S_{\mathrm p},S_{\mathrm a})\)，分量遗忘算子只是普通投影：
\[
\boxed{
\pi_{-i}(S):=(S_j)_{j\neq i},
\qquad
i\in\{\mathrm f,\mathrm d,\mathrm p,\mathrm a\}.
}
\]
它不补默认值，也不重建被删信息。

第 54.3 部的四个接口都消费单个 \(\operatorname{Evidence}\)，不是记录集。本文统一采用逐点全称提升
\[
\boxed{
\operatorname{Lift}_Z(P):=\forall z\in Z,\ P(z).
}
\]
因此 \(\operatorname{AdmissibleJudge}\) 对每个 \(r\in Z\) 判定；\(\operatorname{NonAnticipating}\) 与 \(\operatorname{ScientificGain}\) 对每个 \(z\in Z\) 判定；\(\operatorname{TargetLaundering}\) 使用显式报告族 \(z\mapsto\operatorname{report}_z\) 后对每个 \(z\in Z\) 判定。以下单点陈述取逐点全称即得到记录集陈述，不把 \(Z\) 偷换成单个证据。

为冻结全部非投影实参，按原接口定义四个 \(\operatorname{SameOut}\) 关系：

- \(\operatorname{SameOut}_{\mathrm{NA}}\) 固定 \(n\)、类型与序结构、同一证据 \(z\)；谓词为 \(\operatorname{NonAnticipating}(K.\operatorname{adjudication},z)\)。
- \(\operatorname{SameOut}_{\mathrm{AJ}}\) 另固定同一 \(r\)；两侧证明分别具有 \(\operatorname{ValidTrace}(\mathcal L,K.\operatorname{adjudication})\) 的真类型，不要求证明项字面相等；谓词为 \(\operatorname{AdmissibleJudge}(\mathcal L,K.\operatorname{adjudication},v_K,r)\)。
- \(\operatorname{SameOut}_{\mathrm{TL}}\) 固定同一 \(\operatorname{evaluate}\)、同一 \(z\) 与同一 \(\operatorname{report}\) 对象；对 old/new commitments 分别逐字段固定 adjudication 之外的 \(\operatorname{targetChain}/\operatorname{domain}/\operatorname{epsilon}/\operatorname{conditions}/\operatorname{comparator}/\operatorname{testPlan}/\operatorname{baseline}/\operatorname{weightSpec}/\operatorname{decision}/\operatorname{committedArtifacts}/\operatorname{baselineArtifacts}\)，包含 \(\operatorname{protectedCoordinates}\) 的全部字段。包含律证明只须分别具有正确类型，不要求证明项字面相等。谓词为 \(\operatorname{TargetLaundering}(\operatorname{evaluate},\operatorname{oldK},\operatorname{newK},z,\operatorname{report})\)；report.original/revised/evidence/regradedVerdict/attributedTo/occurredAt 的身份检查仍由原谓词执行，不预先冻结其真值。
- \(\operatorname{SameOut}_{\mathrm{SG}}\) 固定同一 \(\operatorname{evaluate}\)、行动身份 \(a,b\)，并逐字段固定 adjudication 之外的同一组 commitment 字段，特别是 \(K.\operatorname{committedArtifacts}\)、\(K.\operatorname{baselineArtifacts}\) 与 \(K.\operatorname{comparator}\)；谓词为 \(\operatorname{ScientificGain}(\operatorname{evaluate},K,z,a,b)\)。

所有 \(\operatorname{SameOut}\) 还固定共同的 \(Z\) 和元素身份。允许变化的历史数据只在 adjudication 与账本内，并受相等的完整 \(\operatorname{AdjudicationSignature}\) 约束；若后续接口增加非历史实参，必须显式加入相应 \(\operatorname{SameOut}\)。

再固定第 53.4 部的非空有限可行集 \(F\)、Action 载体上的完整外生规范 \(O_G\)，并要求
\[
\forall a\in F,\quad a\in\operatorname{AdmTarget}(O_G.\operatorname{goal})
\ \wedge\ \operatorname{InScope}(O_G.\operatorname{scope},a).
\]
令 \(a\sim_Gb\Longleftrightarrow O_G.\operatorname{relation}(a,b)\wedge O_G.\operatorname{relation}(b,a)\)，在 \(F/{\sim_G}\) 上取延伸原商偏序的线性序 \(\leq_\lambda\)，并回拉到 Action：
\[
a\leq^F_\lambda b
\Longleftrightarrow
a\in F\wedge b\in F\wedge[a]\leq_\lambda[b].
\]
令派生范围为 \(\operatorname{scope}_F=(O_G.\operatorname{scope},F)\)，且 \(\operatorname{InScope}_F(\operatorname{scope}_F,a)\Longleftrightarrow\operatorname{InScope}(O_G.\operatorname{scope},a)\wedge a\in F\)。把回拉关系连同
\[
\operatorname{goal}=O_G.\operatorname{goal},\quad
\operatorname{source}=O_G.\operatorname{source},\quad
\operatorname{version}=O_G.\operatorname{version},\quad
\operatorname{scope}=\operatorname{scope}_F
\]
及第 54.3 部要求的域、反身与传递见证打包为完整 \(\operatorname{OrientationSpec}\)，记作 \(O^F_\lambda\)。定义
\[
\boxed{
\operatorname{LinExt}_F(O_G):=\{O^F_\lambda:\leq_\lambda
\text{ 是 }F/{\sim_G}\text{ 上延伸原商偏序的线性序}\}.
}
\]
其元素不是裸关系；来源、版本和原范围由 \(O_G\) 复制，有限范围收窄显式保存在 \(\operatorname{scope}_F\)，观察记录不生成任何定向。

## 55.2 开放问题 OP1—OP6

### 55.2.1 开放问题 OP1：签名充分性

取有限有效历史 \(H=(K,\mathcal L,v_K)\)、\(H'=(K',\mathcal L',v_{K'})\)，记其签名为 \(S(H),S(H')\)。以下四个 atoms 是否逐项成立：
\[
\boxed{
\begin{array}{ll}
\mathrm{OP1\!\!-NA}:&S(H)=S(H')\wedge\operatorname{SameOut}_{\mathrm{NA}}
\Rightarrow(\operatorname{NonAnticipating}(K.\operatorname{adjudication},z)
\leftrightarrow\operatorname{NonAnticipating}(K'.\operatorname{adjudication},z));\\
\mathrm{OP1\!\!-AJ}:&S(H)=S(H')\wedge\operatorname{SameOut}_{\mathrm{AJ}}
\Rightarrow(\operatorname{AdmissibleJudge}(\mathcal L,K.\operatorname{adjudication},v_K,r)
\leftrightarrow\operatorname{AdmissibleJudge}(\mathcal L',K'.\operatorname{adjudication},v_{K'},r));\\
\mathrm{OP1\!\!-TL}:&S(H_o)=S(H'_o)\wedge S(H_n)=S(H'_n)
\wedge\operatorname{SameOut}_{\mathrm{TL}}\\
&\Rightarrow(\operatorname{TargetLaundering}(\operatorname{evaluate},\operatorname{oldK},\operatorname{newK},z,\operatorname{report})
\leftrightarrow\operatorname{TargetLaundering}(\operatorname{evaluate},\operatorname{oldK}',\operatorname{newK}',z,\operatorname{report}));\\
\mathrm{OP1\!\!-SG}:&S(H)=S(H')\wedge\operatorname{SameOut}_{\mathrm{SG}}
\Rightarrow(\operatorname{ScientificGain}(\operatorname{evaluate},K,z,a,b)
\leftrightarrow\operatorname{ScientificGain}(\operatorname{evaluate},K',z,a,b)).
\end{array}
}
\]
其中 TL 的 \(H_o,H_n\) 分别承载 old/new commitment 与各自有效账本；单点式按 \(\operatorname{Lift}_Z\) 提升，TL 使用报告族。真残差：第 48—54 部给出了四谓词及其消费者，却未回答该四分量签名在逐项冻结全部非投影读取后是否因子化四个接口。

结案判据：四个具名 atoms 各自获得证明、有限有效反例或 statement-revise；任一反例必须指出翻转的原签名原子与未被签名保存的字段。

### 55.2.2 开放问题 OP2：逐分量必要性

本题的显式前件是：所选 \(\Phi\) 的 OP1 atom 已获肯定答案，等价地存在函数 \(\bar\Phi\) 使 \(\Phi(C)=\bar\Phi(S(H(C)),\operatorname{Out}_\Phi(C))\)；对 TL，\(S(H(C))\) 是 old/new 两签名的有序对。只在此前件下，对每个 \(i\in\{\mathrm f,\mathrm d,\mathrm p,\mathrm a\}\)，是否存在一个 \(\Phi_i\) 与两上下文 \(C_i^+,C_i^-\)，满足
\[
\boxed{
\operatorname{SameOut}_{\Phi_i}(C_i^+,C_i^-),\quad
\pi_{-i}S(C_i^+)=\pi_{-i}S(C_i^-),\quad
S_i(C_i^+)\neq S_i(C_i^-),\quad
\Phi_i(C_i^+)\leftrightarrow\neg\Phi_i(C_i^-)?
}
\]
被删坐标之外的共同 \(Z\)、证据、行动、evaluate、committed/baseline 集、comparator、protected coordinates 与 report 身份均须按 55.1 逐项相同。若 \(\Phi_i=\mathrm{TL}\)，还须指定被消融的是 old 或 new 签名；另一承诺的完整四坐标及被消融承诺的其余三坐标全部相同。本题只有四个坐标方向，不冒充四坐标乘四谓词的十六项矩阵。真残差：在完整签名确实充分的前件下，既有文本仍未证明四个坐标各有不可删除见证。

结案判据：四个方向各交付满足因子化前件、删外全同且被删值确异的有限机器见证；或证明某分量可由其余分量与 SameOut 数据导出并修订最小签名。

### 55.2.3 开放问题 OP3：可判定两面

令 \(N\) 为整个实例的总编码长度，计入图、闭包根、filtration 表、\(Z\)、角色日志、候选/可行/committed/baseline 集、两份承诺、报告、保护坐标、行动和全部字符串字段。模型为确定性 word-RAM，字长 \(\Theta(\log N)\)：对象用 \([0,N)\) 内编号，集合经一次 \(O(N)\) 预处理成为位表，成员查询为 \(O(1)\)；非编号字段采用规范编码，精确相等的总扫描成本计入 \(N\)。Prop 证明字段在运行时擦除，只验证其对应的有限关系，不把证明项相等当作查询。依赖图以邻接表和根集给出，闭包不作可信预计算，而由一次 BFS/DFS 生成；输入若另带闭包位表，须在线性扫描中与生成结果比较。\(\operatorname{ValidTrace}\) 证明不作为可信证书给定，而以全日志扫描和 filtration 成员查询验证。令 \(C_{\mathrm{eval}}\) 为所有实际 evaluator 调用的总成本。在此模型中，四个逐点提升谓词是否均可在
\[
\boxed{
O(N+C_{\mathrm{eval}})
}
\]
时间、\(O(N)\) 空间内判定？

不可判侧固定 Mathlib 的程序编码 \(c:\operatorname{Nat.Partrec.Code}\) 与行为 \(\operatorname{eval}(c)\)，并定义外延语义依赖
\[
\operatorname{SemDep}(c,z_*):=B(\operatorname{eval}(c),z_*),
\]
其中 \(B\) 对相同行为同值，且有依赖/无依赖两枚 code 见证。对每个 \(c\) 取程序索引语义接口 \(K_c\)，固定 \(z_*\) 在其 decision filtration 可见、在 freeze filtration 不可见，并规定 \(z_*\in K_c.\operatorname{adjudication}.\operatorname{evidenceDependencies}\Longleftrightarrow\operatorname{SemDep}(c,z_*)\)。于是 \(\operatorname{NonAnticipating}(K_c.\operatorname{adjudication},z_*)\) 恰等于 \(\neg\operatorname{SemDep}(c,z_*)\)。已冻结真源 `D5/S0/Computability/ClosureUndecidable.closure_reading_unreachable` 正好排除任何非平凡、行为不变集合的可计算总判定器，故不可判结论应复用该节点，而不重证 Rice 定理。若结案工件要求字面给出多一归约 \(\mathsf{HALT}\leq_m\operatorname{NonAnticipating}\) 的编码函数与双向正确性，则该冻结定理只给非可计算性、不提供这条具体映射，仍需一个新的薄 HALT 桥 atom。

真残差：第 54.3 部只给出 Prop 级接口；上述 RAM 表示下的统一判定器、复杂度证明，以及 \(\operatorname{SemDep}\) 对冻结 Rice 节点的精确实例化或所需 HALT 桥均未给出。

结案判据：交付在上述编码上运行的判定器、\(O(N+C_{\mathrm{eval}})\) 证明与 ValidTrace/闭包核验测试，并交付 `closure_reading_unreachable` 的同层性和非平凡见证实例；若选择 literal-HALT 口径，再交付方向无误的桥。任一义务失败即 statement-revise 输入或归约模型。

### 55.2.4 开放问题 OP4：外推证书五项合取的独立性

允许模型类 \(\mathfrak M_{\mathrm{fin}}\) 只含有限可判语义模型：域由有限点集 \(|J|\) 解释，\(\operatorname{strictSubset}(J,J')\Longleftrightarrow |J|\subsetneq|J'|\)，且 \(\operatorname{inNewOnlyDomain}(z,J,J')\Longleftrightarrow z\in|J'|\setminus|J|\)；TruthReceipt 是内容地址、域和版本的记录，\(\operatorname{receiptMatches}\) 当且仅当三字段精确相等；givenPremises 与 transportAssumption 是固定有限前件表和运输表导出的可判真值；预测是有限部分函数，\(\operatorname{predictionDefined}\) 是图定义域成员关系，\(\operatorname{predictionFails}\) 只能在已定义值违反固定验收关系时成立；\(\operatorname{claimOn}\) 与 \(\operatorname{refutes}\) 由同一固定有限真值/评价表导出，refutes 当且仅当该预测值与该 claim 的表中真值冲突。任意赋值这些 Prop 字段的退化模型不在 \(\mathfrak M_{\mathrm{fin}}\)。

把第 54.3 部 Lean \(\operatorname{ValidTransportCert}\) 的五个顶层合取记为 \(C_1\) 严格扩域、\(C_2\) claim-bound 旧域收据、\(C_3\) 保留前件的条件运输、\(C_4\) 新域差上预测全定义、\(C_5\) 含失败与反驳的非真空见证。第 51.3 部展示式只有后四项；严格扩域在 51.4 的 Overreach 展示式出现，五项顶层合取的归属是第 54.3 部接口。令 \(\operatorname{Weak}_j:=\bigwedge_{k\neq j}C_k\)，并分别固定坏报告类型：非严格扩域、错 claim/域/版本收据、前件成立而新域 claim 假、遗漏一个新域差预测、没有预登记失败/反驳见证。是否有
\[
\boxed{
\forall j\in\{1,2,3,4,5\},\
\exists M_j\in\mathfrak M_{\mathrm{fin}},\quad
\operatorname{Weak}_j(M_j)\wedge\neg C_j(M_j)
\wedge\operatorname{Bad}_j(M_j)?
}
\]
真残差：第 54.3 部用五项堵住上述五类坏报告，但尚未在受约束的有限语义模型类中证明每项删除确实放过对应坏报告，而不只是展示任意 Prop 赋值的纯合取独立性。

结案判据：五个删除方向各给出 \(\mathfrak M_{\mathrm{fin}}\) 内可枚举模型并验证对应 \(\operatorname{Bad}_j\)，或证明某项在该模型类公理下由其余四项蕴含并 statement-revise 最小合取。

### 55.2.5 开放问题 OP5：Pareto 停机与外生序

固定非空有限 \(F=K_n.\operatorname{decision}.\operatorname{feasible}\)、\(K_n.\operatorname{decision}.\operatorname{current}=\operatorname{some}(a_{\mathrm{cur}})\)，以及 Action 上由五维公共坐标诱导的 Pareto 预序 \(\preceq_P\)。取其对称核 \(\sim_P\)，令完整外生规范 \(O_P\) 的 relation 为 \(\preceq_P\)，并按 55.1 构造 \(\operatorname{LinExt}_F(O_P)\)。全部 \(F\) 已要求位于 \(\operatorname{AdmTarget}(O_P.\operatorname{goal})\) 与原声明范围。是否成立
\[
\boxed{
a_{\mathrm{cur}}\text{ 在 }F\text{ 中 Pareto-maximal}
\Longleftrightarrow
\exists O^F_\lambda\in\operatorname{LinExt}_F(O_P),\
\operatorname{OrientedStop}(\operatorname{AdmTarget},\operatorname{InScope}_F,O^F_\lambda,K_n)?
}
\]
是否进一步成立
\[
\boxed{
\bigl(\forall O^F_\lambda\in\operatorname{LinExt}_F(O_P),\
\operatorname{OrientedStop}(\operatorname{AdmTarget},\operatorname{InScope}_F,O^F_\lambda,K_n)\bigr)
\Longleftrightarrow
a_{\mathrm{cur}}\text{ 在 }F\text{ 中为 }\preceq_P\text{-greatest}?
}
\]
不再登记等变唯一选择子问：冻结节点 `D5/S3/ConceptDynamics/DecisionValue/IncomparableRepairCosts.incomparable_repairs_no_unique_choice` 已给出有限二点 Pareto 不可比且成本结构不产生唯一选择；`D5/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit.symmetric_event_admits_no_equivariant_culprit` 已证明至少二标签的完全对称事件不存在等变单值选择。此处没有超出二者的新增残差。真残差：maximal/greatest 与对完整 Action 载体 \(\operatorname{OrientationSpec}\) 的存在/全称线性延伸停机之间的两个等价式。

结案判据：在 \(K_n.\operatorname{decision}.\operatorname{feasible}=F\)、current 与范围前件下证明或反驳两个等价式；反驳须提交保持 source/version/scope 的完整 \(O^F_\lambda\) 有限反模型。

### 55.2.6 开放问题 OP6：前瞻改善不蕴含泛化

固定有限观测历史空间 \(\Omega_{\mathrm{obs}}\)、有限下一记录空间 \(\Omega_{\mathrm{next}}\)，以及两条联合概率质量函数
\[
P,Q:\Omega_{\mathrm{obs}}\times\Omega_{\mathrm{next}}\to[0,1].
\]
它们各自归一化，并在完整已观察 \(\sigma\)-代数上一致；有限情形即
\[
\forall h\in\Omega_{\mathrm{obs}},\quad
\sum_uP(h,u)=\sum_uQ(h,u).
\]
取已观察历史 \(h_*\) 及其末记录 \(z_*\)，要求共同边缘质量 \(p_{\mathrm{obs}}(h_*)=q_{\mathrm{obs}}(h_*)>0\)。固定第 54.3 部的 \(\operatorname{evaluate}\)、冻结承诺 \(K\)、被承诺行动 \(a\) 与预登记基线 \(b\)，并要求单记录命题 \(\operatorname{ScientificGain}(\operatorname{evaluate},K,z_*,a,b)\)。令实值损失 \(\operatorname{Loss}_K(-;u)\) 对两联合律绝对可积；在有限空间中这项仍作为显式检查。定义
\(\Omega_{\mathrm{next}}\) 不直接冒充 \(\operatorname{Evidence}\)：固定全函数 \(\operatorname{nextEvidence}:\Omega_{\mathrm{next}}\to\operatorname{Evidence}\)，并在 OP6 中把同一 evaluator 实例化为 \(\operatorname{evaluate}:\operatorname{Comparator}\to\operatorname{Action}\to\operatorname{Evidence}\to\mathbb R\)。\(\operatorname{Loss}_K\) 不是另一个可选损失，而被唯一规定为
\[
\boxed{
\operatorname{Loss}_K(x;u):=
\operatorname{evaluate}(K.\operatorname{comparator},x,\operatorname{nextEvidence}(u))\in\mathbb R.
}
\]
因此前件中的 \(\operatorname{ScientificGain}\) 与两个条件期望共用同一 \(\operatorname{evaluate}\) 及 \(K.\operatorname{comparator}\)；绝对可积检查就施于此实值映射，差分也只由它派生：
\[
\Delta_K(a,b;u):=\operatorname{Loss}_K(a;u)-\operatorname{Loss}_K(b;u).
\]
是否存在上述全部对象，使
\[
\boxed{
\mathbb E_P[\Delta_K(a,b;U)\mid H=h_*]<0
<
\mathbb E_Q[\Delta_K(a,b;U)\mid H=h_*]
}
\]
或 \(P,Q\) 互换？

真残差：第 52.4 部拒绝从一次 \(\operatorname{ScientificGain}\) 自动推出长期稳定性，却未给出在全部已观察历史分布不可区分、只允许条件未来核分歧时的有限符号反转见证。

结案判据：给出可枚举的有限联合律，机器核验归一化、全观测边缘相等、\(h_*\) 正质量、ScientificGain、绝对可积与两条件期望异号；或在同一概率模型类中证明不存在并 statement-revise 前件。

可判定性与查询复杂度借用有限图算法、停机不可判定与语义性质归约的已知形状；线性延伸借用 Szpilrajn 型延伸定理；可识别性借用统计决策与相容数据律的已知形状。单项不主张首创；它们与 DECT 裁决、漂白、外推、停机及增益接口的组合标为 suspected-novel，未作系统文献检索。

## 55.3 本批承诺

按第 49 部 \(K_n\) 的字段，本批冻结为
\[
\boxed{
\begin{aligned}
\operatorname{target\_chain}
&=\text{GoalArtifact 纯推理产出}\to\text{RDS}\to
\text{v1.2 裁决层}\to\text{本批边界};
\\
\operatorname{scope}
&=\text{有限/显式模型，排除统计显著性与解析估计};
\\
\operatorname{comparator}
&=\text{六个 OP 各由下游 prove/refute/statement-revise 结案并消化为有稳定地址的 atoms};
\\
\operatorname{baseline}
&=\text{不预记无地址 atom 数量；按父 OP 去重计数};
\\
\operatorname{falsifiable\_prediction}
&=\text{在全部冻结 atoms 首次全达终态的账本前缀上，六个 OP 中至少四个不扩作用域存活，至少三个由 kernel 定理或机器反模型结案}.
\end{aligned}
}
\]
分母明确为 OP1—OP6 六个父问题；一个 OP 即使拆成多个 atoms 也只计一次。评估截止事件为“全部冻结 atoms 首次全部处于 proved/refuted/statement-revised 终态的账本前缀”，与成功阈值及结案顺序独立；存活数与结案数都只在该前缀上求值。该前缀存在时，少于四个不扩域存活或少于三个以 kernel 定理/机器反模型结案即判本批预测失败；此前只记 open，不把未到期冒充成功。任一 OP 的真、假、独立性、复杂度或可识别性均未被预记为结论。

上句的结算语义由以下有限账本状态覆盖。令 \(A\) 为本批全部稳定地址 atoms，六个父问题的有限、非空 atom 集 \(A_1,\ldots,A_6\) 两两不交且构成 \(A\) 的分区；等价地，每个 atom 恰属一个父 OP，并由唯一映射 \(p:A\to\{1,\ldots,6\}\) 记录该归属。六集在全部父 OP 首次完成 atomization 时同时冻结，此后不得增删成员。每个 atom 的状态恰取一值
\[
\mathsf{AtomState}:=\{\mathsf{proved},\mathsf{refuted},
\mathsf{statement\mbox{-}revised},\mathsf{open}\}.
\]
每个 atom 以 \(\mathsf{open}\) 为初态，只能原子迁移到其余三个不可再改的终态；\(\mathsf{proved}\) 只由 kernel 定理触发，\(\mathsf{refuted}\) 只由机器核验的反模型触发。记
\[
\operatorname{Terminal}_s(\alpha)
\Longleftrightarrow
s(\alpha)\in\{\mathsf{proved},\mathsf{refuted},\mathsf{statement\mbox{-}revised}\}.
\]
\(\mathsf{proved}\)、\(\mathsf{refuted}\) 和 \(\mathsf{open}\) 均保留该 atom 在 55.2 的原陈述与原作用域；任何陈述改写或作用域变更（含扩大）必须且只能记为 \(\mathsf{statement\mbox{-}revised}\)。对账本状态 \(s\)，每个父 OP 的唯一聚合值为
\[
\operatorname{Agg}_i(s):=
\begin{cases}
\mathsf{open},&\exists\alpha\in A_i,\ s(\alpha)=\mathsf{open};\\
\mathsf{statement\mbox{-}revised},&\text{否则若存在该状态};\\
\mathsf{refuted},&\text{否则若存在该状态};\\
\mathsf{proved},&\text{否则}.
\end{cases}
\]
优先序将任何混合状态映成唯一父级真值：有未决 atom 时父问题仍 open，全部已决时改写优先于反驳，反驳优先于全证成。再定义
\[
\operatorname{Survive}_i(s)\Longleftrightarrow
\forall\alpha\in A_i,\quad
s(\alpha)\in\{\mathsf{proved},\mathsf{refuted}\},
\qquad
\operatorname{Closed}_i(s)\Longleftrightarrow
\operatorname{Agg}_i(s)\in\{\mathsf{proved},\mathsf{refuted}\}.
\]
“存活”要求该父 OP 的全部 atoms 已由 kernel 定理或机器反模型决定且没有改写；“结案”要求同一终态条件并使父聚合值为 proved/refuted。含任一 open atom 的未决父既不计存活也不计结案。故每个父 OP 恰落入三个两两互斥且穷尽的账格之一：\(\mathsf{pending}\)、\(\mathsf{survive\mbox{-}closed}\)、\(\mathsf{revised}\)。

截止点不再取外部“批次”，也不以成功阈值触发。atom 状态迁移各自是带唯一 \(\operatorname{EventId}\) 的原子账本事件，令 \(s_{\le e}\) 为事件前缀的状态，并固定
\[
e_*:=\min\{e:\forall\alpha\in A,\ \operatorname{Terminal}_{s_{\le e}}(\alpha)\}.
\]
若该集为空则预测仍 \(\mathsf{open}\)；否则只在 \(s_{\le e_*}\) 上计算六个父 OP 的两个预测半项，并以
\[
\boxed{
\#\{i:\operatorname{Survive}_i(s_{\le e_*})\}\ge 4
\quad\wedge\quad
\#\{i:\operatorname{Closed}_i(s_{\le e_*})\}\ge 3
}
\]
为成功判据，否定式为失败判据；结案阈值采用“至少三个”的下界语义。运输批次边界不进入此最小前缀谓词；事件顺序可以改变 \(e_*\) 的事件标识，却不能改变同一终态赋值上的两个计数与判词。特别地，两父 closed、四父 revised 的终局在最后一个 atom 达终态时已有 \(e_*\)，两计数均为 2，故判失败而不再永悬；A1—A3 先 closed、A4—A6 后 revised 的顺序与任何产生同一终态赋值的其他顺序，两计数均为 3，故得到同一失败判词。

---

# 追加账本增订
## v1.3 — 2026-08-24

追加存入：

- 从 \(K.\operatorname{adjudication}\) 派生且唯一命名的 \(\operatorname{AdjudicationSignature}\)：冻结/裁决可见性、\(\operatorname{evidenceDependencies}\) 与不保留 ReuseDepth 的角色存在签名投影；
- 单 Evidence 接口的逐点全称提升、四个原签名与逐字段 \(\operatorname{SameOut}\)，以及以 OP1 因子化为前件的四方向坐标消融；
- 总编码长度 \(N\) 的 word-RAM/查询模型、显式闭包与 ValidTrace 核验，以及对冻结 `ClosureUndecidable.closure_reading_unreachable` 的复用边界；
- 受有限集合、收据、部分预测和真值表一致性约束的外推模型类内五项独立性；
- 回拉到 Action 并复制 source/version/scope 的完整线性延伸 OrientationSpec，以及 maximal/greatest 两个未决等价式；等变唯一选择不再列 open，归既有冻结 `IncomparableRepairCosts` 与 `SymmetricEventNoUniqueCulprit`；
- 在完整已观察边缘上一致的 \(\Omega_{\mathrm{obs}}\times\Omega_{\mathrm{next}}\) 双联合律、可积损失与未来条件期望异号问题；
- 不设无地址 atom 总数；六个 OP 为预测分母，每个 atom 恰属一个父 OP，并只在全部冻结 atoms 首次全达 proved/refuted/statement-revised 终态的账本前缀上按“至少四个存活且至少三个 kernel/机器反模型结案”结算；
- 本批只提出问题，零新定理主张，整体组合标为 suspected-novel。

后续增订继续严格追加于本节之后。

---
# 第五十六部　54.3 三处源缺口的有限闭合

## 56.1 增订目的、继承接口与收窄纪律

本部是 v1.4 的追加式增订，只精确化第 54.3 部证明义务 9 的商序半条、证明义务 10 的 Stop 半条，以及证明义务 12 的时域投影半条。第 1—55 部的定义、开放问题、冻结结算与已形式化定理均不回写、不删除，也不因本部而改变原地址。

本部预期进入既有 canonical 命名空间

`D5.S3.ConceptDynamics.DefinitionEscape.Adjudication`

并直接复用其中已经给出的

`GainVector`、`ParetoWeak`、`ParetoStrict`、`NoDominatingCandidate`、`DecisionSet`、`OrientationSpec`、`ProspectiveCommitment`、`OrientedStopOnDecisionSet`、`OrientedStop` 与 `ExpansionEscape`。

本部只使用以下初等构件：

- 有限集、有限子类型与有限过滤；
- 预序、偏序、关系的对称核；
- `Fin (N+1)`、自然数有限迭代与函数外延；
- 布尔有限扫描及其命题正确性。

不引入测度、概率、拓扑、抽象商选择、线性延伸或任意代表选择。所有空类型、空有限集与单点有限集都按定义处理，不暗加 `Nonempty`。

## 56.2 弱支配诱导的有限显式商

### 56.2.1 有限承载、承载枚举与对称核

固定类型

\[
\mathsf{Action},\ \mathsf I,\ \mathsf R,\ \mathsf{Tr},\ \mathsf C,\ \mathsf Q,
\]

其中 `Action` 有可判等号；五个坐标分别带 `Preorder`，且各自的 \(\le\) 可判。固定有限行动集

\[
F:\operatorname{Finset}(\mathsf{Action})
\]

以及公共绝对坐标

\[
v:\mathsf{Action}\to
\operatorname{GainVector}(\mathsf I,\mathsf R,\mathsf{Tr},\mathsf C,\mathsf Q).
\]

定义有限承载子类型与它的显式枚举

\[
A_F:=\{a:\mathsf{Action}\mid a\in F\},
\qquad
\operatorname{carrierEnum}_F:=F.\operatorname{attach}
\in\operatorname{Finset}(A_F).
\]

对 \(x,y:A_F\)，定义承载上的弱支配

\[
\operatorname{ParetoWeakOn}(v,F,x,y)
\Longleftrightarrow
\operatorname{ParetoWeak}(v,x.1,y.1),
\]

并定义弱支配的对称核

\[
\boxed{
\operatorname{ParetoEqOn}(v,F,x,y)
\Longleftrightarrow
\operatorname{ParetoWeakOn}(v,F,x,y)
\wedge
\operatorname{ParetoWeakOn}(v,F,y,x).
}
\]

该等价完全由弱支配诱导；它不是另给标签，也不预先把“同向量”写进定义。

**证明义务 56.2-A（对称核的可判等价律）。** 对上述任意类型、可判预序、\(F\) 与 \(v\)，机器核验

\[
\begin{aligned}
&\forall x:A_F,\quad
\operatorname{ParetoEqOn}(v,F,x,x),\\
&\forall x,y:A_F,\quad
\operatorname{ParetoEqOn}(v,F,x,y)
\to
\operatorname{ParetoEqOn}(v,F,y,x),\\
&\forall x,y,z:A_F,\quad
\operatorname{ParetoEqOn}(v,F,x,y)
\to
\operatorname{ParetoEqOn}(v,F,y,z)
\to
\operatorname{ParetoEqOn}(v,F,x,z),
\end{aligned}
\]

并从五个坐标关系的可判性构造

\[
\forall x,y:A_F,\quad
\operatorname{Decidable}
\bigl(\operatorname{ParetoEqOn}(v,F,x,y)\bigr).
\]

反身与传递部分应复用已冻结的
`pareto_weak_reflexive_transitive`；不得把待证结论重新列为前件。

### 56.2.2 等价类、类像与有限商承载

对 \(x:A_F\)，定义显式等价类

\[
\boxed{
\operatorname{paretoClass}_{v,F}(x)
:=
\operatorname{carrierEnum}_F.\operatorname{filter}
\bigl(\lambda y:A_F,\
\operatorname{ParetoEqOn}(v,F,y,x)\bigr).
}
\]

定义全部类的有限像

\[
\operatorname{paretoClassImage}_{v,F}
:=
\operatorname{carrierEnum}_F.\operatorname{image}
\bigl(\operatorname{paretoClass}_{v,F}\bigr)
\in
\operatorname{Finset}\bigl(\operatorname{Finset}(A_F)\bigr).
\]

定义有限 Pareto 商承载

\[
\boxed{
\operatorname{FiniteParetoQuotient}(v,F)
:=
\left\{
C:\operatorname{Finset}(A_F)
\ \middle|\
C\in\operatorname{paretoClassImage}_{v,F}
\right\}.
}
\]

记该类型为 \(Q_{v,F}\)。再定义它的显式全枚举

\[
\boxed{
\operatorname{quotientEnum}_{v,F}
:=
\operatorname{paretoClassImage}_{v,F}.\operatorname{attach}
\in\operatorname{Finset}(Q_{v,F}).
}
\]

这里的“商”就是有限类像本身；下游不需要选择代表元，也不需要调用抽象 `Quotient`。

**证明义务 56.2-B（类的精确性与枚举完备性）。** 对任意 \(x,y:A_F\) 与 \(C:Q_{v,F}\)，机器核验

\[
\begin{aligned}
&x\in\operatorname{carrierEnum}_F,\\
&y\in\operatorname{paretoClass}_{v,F}(x)
\Longleftrightarrow
\operatorname{ParetoEqOn}(v,F,y,x),\\
&x\in\operatorname{paretoClass}_{v,F}(x),\\
&\operatorname{paretoClass}_{v,F}(x)
=
\operatorname{paretoClass}_{v,F}(y)
\Longleftrightarrow
\operatorname{ParetoEqOn}(v,F,x,y),\\
&C.1.\operatorname{Nonempty},\\
&\forall z:A_F,\ z\in C.1\to
\operatorname{paretoClass}_{v,F}(z)=C.1,\\
&C\in\operatorname{quotientEnum}_{v,F}.
\end{aligned}
\]

最后一式给出 \(Q_{v,F}\) 的显式有限枚举，因而可据此构造 `Fintype Q_{v,F}`，不以 `Nonempty Q_{v,F}` 为前件。退化承载也必须机器核验：

\[
\begin{aligned}
&F=\varnothing
\to
\forall C:Q_{v,F},\ \mathsf{False},\\
&F.\operatorname{card}=1
\to
\exists C:Q_{v,F},\
\forall D:Q_{v,F},\ D=C.
\end{aligned}
\]

所以空 \(F\) 给出空商，单点 \(F\) 给出恰一商类。

### 56.2.3 商上的弱支配

对 \(C,D:Q_{v,F}\)，定义

\[
\boxed{
\begin{aligned}
&\operatorname{QuotientParetoWeak}(v,F,C,D)
\\
&\Longleftrightarrow
\exists x:A_F,\ x\in C.1
\wedge
\exists y:A_F,\ y\in D.1
\wedge
\operatorname{ParetoWeakOn}(v,F,x,y).
\end{aligned}
}
\]

这是“类 \(C\) 弱支配类 \(D\)”的存在代表式。由于类由弱支配的对称核生成，该式必须与代表选择无关。

**证明义务 56.2-C（代表无关、可判与偏序）。** 对任意 \(C,D,E:Q_{v,F}\)，机器核验

\[
\begin{aligned}
&\operatorname{QuotientParetoWeak}(v,F,C,D)
\\
&\quad\Longleftrightarrow
\forall x:A_F,\ x\in C.1\to
\forall y:A_F,\ y\in D.1\to
\operatorname{ParetoWeakOn}(v,F,x,y),\\[1mm]
&\operatorname{Decidable}
\bigl(\operatorname{QuotientParetoWeak}(v,F,C,D)\bigr)
\quad\text{可由 }C.1,D.1\text{ 的有限扫描构造},\\[1mm]
&\operatorname{QuotientParetoWeak}(v,F,C,C),\\
&\operatorname{QuotientParetoWeak}(v,F,C,D)
\to
\operatorname{QuotientParetoWeak}(v,F,D,E)
\to
\operatorname{QuotientParetoWeak}(v,F,C,E),\\
&\operatorname{QuotientParetoWeak}(v,F,C,D)
\to
\operatorname{QuotientParetoWeak}(v,F,D,C)
\to
C=D.
\end{aligned}
\]

后三式分别是反身、传递与反对称。因此
\(\operatorname{QuotientParetoWeak}(v,F,\cdot,\cdot)\)
在有限承载 \(Q_{v,F}\) 上为偏序关系。空商上的三律按空类型全称命题解释，不需要补一个虚构元素。

### 56.2.4 与既有“同向量取商”的一致性

现在加强前件：五个坐标都带偏序，而不只是预序。由原先可判的
\(\le\)
与反对称性，逐坐标构造可判等号，再由五个字段构造
`GainVector`
的可判等号。定义同向量类

\[
\operatorname{sameVectorClass}_{v,F}(x)
:=
\operatorname{carrierEnum}_F.\operatorname{filter}
\bigl(\lambda y:A_F,\ v(y.1)=v(x.1)\bigr).
\]

**证明义务 56.2-D（对称核等价于同向量等价）。** 在五坐标均为偏序的前件下，机器核验

\[
\boxed{
\forall x,y:A_F,\quad
\operatorname{ParetoEqOn}(v,F,x,y)
\Longleftrightarrow
v(x.1)=v(y.1)
}
\]

以及

\[
\boxed{
\forall x:A_F,\quad
\operatorname{paretoClass}_{v,F}(x)
=
\operatorname{sameVectorClass}_{v,F}(x).
}
\]

所以第 52.3 部“按同向量等价取商”的有限限制，与本部“按弱支配对称核取商”的类像外延相同；本部补的是此前缺失的承载、枚举、代表无关关系及反对称证明，不改变旧命题的方向或前件。若 `Action` 本身为有限类型并取
\(F=\operatorname{Finset.univ}\)，本构造覆盖完整行动载体；一般情况下，本部只关闭用户指定的有限承载版本，不冒领无限承载的机器实现。

## 56.3 与 \(K_n\) 结算一致的精确 Stop 目标

### 56.3.1 决策集级与承诺级 Stop 目标

固定类型

\[
\mathsf{Goal},\mathsf{Action},\mathsf{Source},
\mathsf{Version},\mathsf{Scope},
\]

其中 `Action` 有可判等号；固定

\[
\operatorname{AdmTarget}:\mathsf{Goal}\to\operatorname{Set}(\mathsf{Action}),
\qquad
\operatorname{InScope}:\mathsf{Scope}\to\mathsf{Action}\to\operatorname{Prop},
\]

完整外生规范

\[
O:
\operatorname{OrientationSpec}
(\mathsf{Goal},\mathsf{Action},\mathsf{Source},
 \mathsf{Version},\mathsf{Scope},
 \operatorname{AdmTarget},\operatorname{InScope}),
\]

以及 \(D:\operatorname{DecisionSet}(\mathsf{Action})\)。

本部把第 54.3 部第 10 条后半中的未限定词 `Stop` 精确定义为

\[
\boxed{
\begin{aligned}
&\operatorname{AdjudicationStopTargetOnDecisionSet}
(\operatorname{AdmTarget},\operatorname{InScope},O,D)
\\
&\Longleftrightarrow
\exists a_{\mathrm{cur}}:\mathsf{Action},\
D.\operatorname{current}=\operatorname{some}(a_{\mathrm{cur}})
\\
&\quad\wedge\
a_{\mathrm{cur}}\in D.\operatorname{feasible}
\\
&\quad\wedge\
\bigl(
\forall a:\mathsf{Action},\
a\in D.\operatorname{feasible}\to
a\in\operatorname{AdmTarget}(O.\operatorname{goal})
\wedge
\operatorname{InScope}(O.\operatorname{scope},a)
\bigr)
\\
&\quad\wedge\
\neg\exists a:\mathsf{Action},\
a\in D.\operatorname{feasible}
\wedge
O.\operatorname{relation}(a_{\mathrm{cur}},a)
\wedge
\neg O.\operatorname{relation}(a,a_{\mathrm{cur}}).
\end{aligned}
}
\]

这不是新停止准则，而是既有
`OrientedStopOnDecisionSet`
的有名展开式。

对任意第 \(n\) 轮前视承诺 \(K_n\)，定义承诺级目标

\[
\boxed{
\operatorname{AdjudicationStopTarget}
(\operatorname{AdmTarget},\operatorname{InScope},O,K_n)
:=
\operatorname{AdjudicationStopTargetOnDecisionSet}
(\operatorname{AdmTarget},\operatorname{InScope},O,K_n.\operatorname{decision}).
}
\]

停止结算的完整地址是有序对 \((K_n,O)\)。其中 \(O\) 的 source、version 与 scope 是地址和来源字段；停止真值的行动数据只从 \(K_n.\operatorname{decision}\) 读取。此处的 Stop 不指第 43 部未带裁决输入的泛称停止，也不指任意用户自定义布尔标签。

### 56.3.2 有限停止检查器

进一步假设下列三个谓词在固定 \(O\) 上可判：

\[
\begin{aligned}
&\forall a,\quad
\operatorname{Decidable}
\bigl(a\in\operatorname{AdmTarget}(O.\operatorname{goal})\bigr),\\
&\forall a,\quad
\operatorname{Decidable}
\bigl(\operatorname{InScope}(O.\operatorname{scope},a)\bigr),\\
&\forall a,b,\quad
\operatorname{Decidable}
\bigl(O.\operatorname{relation}(a,b)\bigr).
\end{aligned}
\]

定义布尔有限扫描器
\(\operatorname{stopCheck}\)：

\[
\boxed{
\operatorname{stopCheck}
(\operatorname{AdmTarget},\operatorname{InScope},O,D)
:=
\begin{cases}
\mathsf{false},
&D.\operatorname{current}=\operatorname{none},\\
\mathsf{false},
&D.\operatorname{current}=\operatorname{some}(a_{\mathrm{cur}})
\text{ 且 }a_{\mathrm{cur}}\notin D.\operatorname{feasible},\\
\mathsf{false},
&\exists a\in D.\operatorname{feasible},\
a\notin\operatorname{AdmTarget}(O.\operatorname{goal})
\vee
\neg\operatorname{InScope}(O.\operatorname{scope},a),\\
\mathsf{false},
&\exists a\in D.\operatorname{feasible},\
O.\operatorname{relation}(a_{\mathrm{cur}},a)
\wedge
\neg O.\operatorname{relation}(a,a_{\mathrm{cur}}),\\
\mathsf{true},
&\text{否则}.
\end{cases}
}
\]

四个失败分支按所列顺序执行；后三个分支只扫描有限集
\(D.\operatorname{feasible}\)。
定义第 \(n\) 轮停止结算分量

\[
\boxed{
\operatorname{settleStop}
(\operatorname{AdmTarget},\operatorname{InScope},O,K_n)
:=
\operatorname{stopCheck}
(\operatorname{AdmTarget},\operatorname{InScope},O,K_n.\operatorname{decision}).
}
\]

若总体
\(\operatorname{Settle}_n=\operatorname{Evaluate}(K_n,Z_n)\)
还输出其他坐标，则 `settleStop` 只规定其中的停止分量；它不消费 \(Z_n\)，也不重新读取未来账本尾部、未冻结权重或新的目标版本。

**证明义务 56.3-A（定义忠实、边界行为与检查器正确性）。** 在上述任意类型与可判前件下，机器核验

\[
\begin{aligned}
&\operatorname{AdjudicationStopTargetOnDecisionSet}
(\operatorname{AdmTarget},\operatorname{InScope},O,D)
\\
&\qquad\Longleftrightarrow
\operatorname{OrientedStopOnDecisionSet}
(\operatorname{AdmTarget},\operatorname{InScope},O,D),\\
&\operatorname{AdjudicationStopTarget}
(\operatorname{AdmTarget},\operatorname{InScope},O,K_n)
\\
&\qquad\Longleftrightarrow
\operatorname{OrientedStop}
(\operatorname{AdmTarget},\operatorname{InScope},O,K_n),\\
&\operatorname{stopCheck}
(\operatorname{AdmTarget},\operatorname{InScope},O,D)=\mathsf{true}
\\
&\qquad\Longleftrightarrow
\operatorname{AdjudicationStopTargetOnDecisionSet}
(\operatorname{AdmTarget},\operatorname{InScope},O,D),\\
&\operatorname{settleStop}
(\operatorname{AdmTarget},\operatorname{InScope},O,K_n)=\mathsf{true}
\\
&\qquad\Longleftrightarrow
\operatorname{AdjudicationStopTarget}
(\operatorname{AdmTarget},\operatorname{InScope},O,K_n),\\
&\operatorname{settleStop}
(\operatorname{AdmTarget},\operatorname{InScope},O,K_n)=\mathsf{false}
\\
&\qquad\Longleftrightarrow
\neg\operatorname{AdjudicationStopTarget}
(\operatorname{AdmTarget},\operatorname{InScope},O,K_n).
\end{aligned}
\]

为缩短下式，记

\[
\operatorname{StopTarget}_O(D)
:=
\operatorname{AdjudicationStopTargetOnDecisionSet}
(\operatorname{AdmTarget},\operatorname{InScope},O,D).
\]

并分别核验

\[
\begin{aligned}
&D.\operatorname{current}=\operatorname{none}
\to
\neg\operatorname{StopTarget}_O(D),\\
&D.\operatorname{feasible}=\varnothing
\to
\neg\operatorname{StopTarget}_O(D),\\
&D.\operatorname{current}=\operatorname{some}(a)
\wedge a\notin D.\operatorname{feasible}
\to
\neg\operatorname{StopTarget}_O(D).
\end{aligned}
\]

因此空可行集或缺失 current 不会因全称命题真空而误报 Stop。

### 56.3.3 Pareto 前沿不决定 Stop 的有限非退化见证

为排除“候选集与可行集不同”这一平凡解释，以下见证令二者相等。

取

\[
\mathsf{Action}_2:=\operatorname{Fin}(2),
\qquad
D_2.\operatorname{candidates}
=
D_2.\operatorname{feasible}
=
\operatorname{Finset.univ},
\qquad
D_2.\operatorname{current}
=
\operatorname{some}(0),
\qquad
D_2.\operatorname{feasibleFromCandidates}
:
\forall a,a\in D_2.\operatorname{feasible}
\to
a\in D_2.\operatorname{candidates}
\quad\text{取恒等包含证明}.
\]

五坐标都取 \(\mathbb N\)，定义

\[
v_2(0)=(1,0,0,0,0),
\qquad
v_2(1)=(0,1,0,0,0).
\]

这里前两坐标分别使 \(0\) 与 \(1\) 各有一项严格优势，其余三坐标相同，所以二者在
`ParetoWeak`
下不可比；特别地当前行动 \(0\) 不受任何候选严格支配。

再取

\[
\mathsf{Goal}_2=\mathsf{Scope}_2=\operatorname{Unit},
\qquad
\mathsf{Source}_2=\mathsf{Version}_2=\operatorname{Bool},
\]

并令所有行动都属于目标允许集且都在 scope 内：

\[
\operatorname{AdmTarget}_2(\star)=\operatorname{Set.univ},
\qquad
\operatorname{InScope}_2(\star,a)\Longleftrightarrow\mathsf{True}.
\]

定义两个完整、可判的外生规范；两者都取
\(\operatorname{goal}=\star\)
与
\(\operatorname{scope}=\star\)：

\[
\begin{aligned}
&O_{\mathrm{stay}}.\operatorname{source}=\mathsf{false},
\quad
O_{\mathrm{stay}}.\operatorname{version}=\mathsf{false},
\quad
O_{\mathrm{stay}}.\operatorname{relation}(a,b)
\Longleftrightarrow a=b,\\
&O_{\mathrm{advance}}.\operatorname{source}=\mathsf{true},
\quad
O_{\mathrm{advance}}.\operatorname{version}=\mathsf{true},
\quad
O_{\mathrm{advance}}.\operatorname{relation}(a,b)
\Longleftrightarrow a.1\le b.1.
\end{aligned}
\]

两者都携带
`relationInDeclaredDomain`、`refl` 与 `trans`
的直接有限证明；它们不是缺字段的裸关系。

**证明义务 56.3-B（修订后的第 10 条后半）。** 机器核验该具体有限实例满足

\[
\boxed{
\begin{aligned}
&\operatorname{NoDominatingCandidate}(v_2,D_2)
\\
&\quad\wedge\
\operatorname{AdjudicationStopTargetOnDecisionSet}
(\operatorname{AdmTarget}_2,\operatorname{InScope}_2,O_{\mathrm{stay}},D_2)
\\
&\quad\wedge\
\neg
\operatorname{AdjudicationStopTargetOnDecisionSet}
(\operatorname{AdmTarget}_2,\operatorname{InScope}_2,O_{\mathrm{advance}},D_2).
\end{aligned}
}
\]

特别地，

\[
\boxed{
\neg\Bigl(
\operatorname{NoDominatingCandidate}(v_2,D_2)
\to
\operatorname{AdjudicationStopTargetOnDecisionSet}
(\operatorname{AdmTarget}_2,\operatorname{InScope}_2,O_{\mathrm{advance}},D_2)
\Bigr).
}
\]

这就是“不提供有来源的权重或其他完整
`OrientationSpec`
定向时，
`NoDominatingCandidate`
不能推出 Stop”的可证命题：同一非空决策集、同一公共绝对坐标与同一 Pareto 前沿，在两个完整外生规范下得到不同停止真值。结论不声称停止永远不可得；它只证明 Pareto 前沿本身不包含 Stop 所需的来源化定向。

### 56.3.4 停止分量的纯输入守恒

**证明义务 56.3-C（只消费 \(K.\operatorname{decision}\) 与 \(O\)）。** 对同一轮次、同一承诺类型的任意
\(K,K'\)
及同一 OrientationSpec 类型的任意
\(O,O'\)，若

\[
K.\operatorname{decision}=K'.\operatorname{decision}
\quad\wedge\quad
O=O',
\]

则机器核验

\[
\boxed{
\operatorname{settleStop}
(\operatorname{AdmTarget},\operatorname{InScope},O,K)
=
\operatorname{settleStop}
(\operatorname{AdmTarget},\operatorname{InScope},O',K').
}
\]

`settleStop`
的函数签名不含裁决记录 \(Z\)；这是“停止分量不消费 \(Z_n\)”的机器可见边界，而不是另加一个带虚假 \(Z\) 实参的恒等式。56.3-C 不取代第 50.3 部及冻结
`append_only_old_settlement_unchanged`
对完整旧轮结算的守恒定理。向账本追加事件、产生 \(K_{n+1}\) 或登记新 \(O'\) 时，旧地址 \((K_n,O)\) 的停止分量仍由旧输入重算；新地址的结果不得回写旧地址。

## 56.4 有限时域投影机器

### 56.4.1 有限迭代、时域索引与投影

固定任意类型 \(X,O\)、更新

\[
\tau:X\to X
\]

与当前读数

\[
q:X\to O.
\]

定义自然数迭代

\[
\boxed{
\begin{aligned}
&\operatorname{timeIter}_\tau(0,x):=x,\\
&\operatorname{timeIter}_\tau(k+1,x)
:=
\tau(\operatorname{timeIter}_\tau(k,x)).
\end{aligned}
}
\]

对 \(N:\mathbb N\)，定义有限时域索引

\[
\boxed{
\operatorname{TimeIndex}(N):=\operatorname{Fin}(N+1)
}
\]

和时域投影

\[
\boxed{
\begin{aligned}
&\operatorname{timeProjection}(q,\tau,N)
:X\to(\operatorname{TimeIndex}(N)\to O),\\
&\operatorname{timeProjection}(q,\tau,N)(x)(i)
:=
q(\operatorname{timeIter}_\tau(i.1,x)).
\end{aligned}
}
\]

记该投影为 \(P_N^{q,\tau}\)。它正是第 8.1 部

\[
T_N(x)=(q(x),q(\tau x),\ldots,q(\tau^N x))
\]

的有类型有限函数实现。有限性来自索引
\(\operatorname{Fin}(N+1)\)；不要求 \(X\) 或 \(O\) 本身有限。

若 \(h:N\le N'\)，定义保值下标嵌入

\[
\boxed{
\iota_h:
\operatorname{TimeIndex}(N)\hookrightarrow
\operatorname{TimeIndex}(N'),
\qquad
\iota_h(i).1=i.1,
}
\]

以及限制函数

\[
\boxed{
\operatorname{restrictTime}_h
:
(\operatorname{TimeIndex}(N')\to O)
\to
(\operatorname{TimeIndex}(N)\to O),
\qquad
\operatorname{restrictTime}_h(u):=u\circ\iota_h.
}
\]

### 56.4.2 两个独立定义的有限时域逃逸关系

对 \(h:N\le N'\) 与 \(x,y:X\)，不用 `ExpansionEscape` 作为定义，独立定义“延长时域后首次暴露”：

\[
\boxed{
\begin{aligned}
&\operatorname{TimeExpansionEscape}(q,\tau,N,N',h,x,y)
\\
&\Longleftrightarrow
\bigl(
\forall k:\mathbb N,\ k\le N\to
q(\operatorname{timeIter}_\tau(k,x))
=
q(\operatorname{timeIter}_\tau(k,y))
\bigr)
\\
&\quad\wedge\
\exists k:\mathbb N,\
N<k\ \wedge\ k\le N'
\\
&\qquad\qquad\wedge\
q(\operatorname{timeIter}_\tau(k,x))
\neq
q(\operatorname{timeIter}_\tau(k,y)).
\end{aligned}
}
\]

若 \(N=N'\)，新增区间为空，所以该关系为空。

再独立定义第 8 部从当前读数扩到长度 \(N\) 的预测逃逸：

\[
\boxed{
\begin{aligned}
&\operatorname{PredictionEscape}(q,\tau,N,x,y)
\\
&\Longleftrightarrow
q(x)=q(y)
\ \wedge\
\exists k:\mathbb N,\ k\le N
\ \wedge\
q(\operatorname{timeIter}_\tau(k,x))
\neq
q(\operatorname{timeIter}_\tau(k,y)).
\end{aligned}
}
\]

两个关系都以自然数有界量词给出，不把欲证的 `ExpansionEscape` 等式偷写进定义。

### 56.4.3 投影、限制与核的基本律

**证明义务 56.4-A（投影展开与限制律）。** 对任意
\(N,N':\mathbb N\)、\(h:N\le N'\) 与 \(x,y:X\)，机器核验

\[
\boxed{
P_N^{q,\tau}(x)=P_N^{q,\tau}(y)
\Longleftrightarrow
\forall k:\mathbb N,\ k\le N\to
q(\operatorname{timeIter}_\tau(k,x))
=
q(\operatorname{timeIter}_\tau(k,y))
}
\]

以及

\[
\boxed{
\operatorname{restrictTime}_h(P_{N'}^{q,\tau}(x))
=
P_N^{q,\tau}(x).
}
\]

特别地，

\[
P_0^{q,\tau}(x)(0)=q(x).
\]

这些结论只用 `Fin` 边界证明、递归化简与有限函数外延。

**证明义务 56.4-B（时域核反单调）。** 对任意
\(N,N'\)、\(h:N\le N'\)，机器核验

\[
\boxed{
\forall x,y:X,\quad
P_{N'}^{q,\tau}(x)=P_{N'}^{q,\tau}(y)
\to
P_N^{q,\tau}(x)=P_N^{q,\tau}(y).
}
\]

等价地，

\[
\ker P_{N'}^{q,\tau}
\subseteq
\ker P_N^{q,\tau}.
\]

该结论由 56.4-A 的限制律直接得到，不需要动力系统、概率或测度前件。

### 56.4.4 `ExpansionEscape` 的两个精确实例

**证明义务 56.4-C（延长时域实例）。** 假设 \(O\) 有可判等号。对任意
\(N,N'\)、\(h:N\le N'\) 与 \(x,y:X\)，机器核验

\[
\boxed{
\operatorname{TimeExpansionEscape}(q,\tau,N,N',h,x,y)
\Longleftrightarrow
\operatorname{ExpansionEscape}
(P_N^{q,\tau},P_{N'}^{q,\tau})(x,y).
}
\]

从右到左唯一需要的有限见证步骤是：若两个
\(\operatorname{Fin}(N'+1)\to O\)
函数不等，则有限扫描找出一个不等坐标；旧投影相等排除 \(k\le N\)，故该坐标满足 \(N<k\le N'\)。

当 \(N<N'\) 时，该式正是第 51.5 部

\[
\ker P_N^{q,\tau}\setminus\ker P_{N'}^{q,\tau}
=
\operatorname{ExpansionEscape}(P_N^{q,\tau},P_{N'}^{q,\tau})
\]

的逐对版本；当 \(N=N'\) 时，两边同时为空。

**证明义务 56.4-D（第 8 部预测逃逸实例）。** 在 \(O\) 有可判等号的前件下，对任意
\(N:\mathbb N\) 与 \(x,y:X\)，机器核验

\[
\boxed{
\operatorname{PredictionEscape}(q,\tau,N,x,y)
\Longleftrightarrow
\operatorname{ExpansionEscape}
(q,P_N^{q,\tau})(x,y).
}
\]

因此第 8.1 部的

\[
\mathcal E_N(q,\tau)=\mathcal E(q;T_N)
\]

在本部的有类型实现中就是

\[
\mathcal E_N(q,\tau)
=
\operatorname{ExpansionEscape}(q,P_N^{q,\tau}).
\]

56.4-C 与 56.4-D 分别处理“旧时域扩到新时域”和“当前读数扩到有限轨迹”；二者不得再混成一个未定型投影。

**证明义务 56.4-E（有限可判性）。** 若 \(O\) 有可判等号，则对任意
\(N,N'\)、\(h:N\le N'\) 与 \(x,y:X\)，机器从
\(\operatorname{Finset.range}(N+1)\)
和
\(\operatorname{Finset.range}(N'+1)\)
的有限扫描构造

\[
\begin{aligned}
&\operatorname{Decidable}
\bigl(\operatorname{TimeExpansionEscape}(q,\tau,N,N',h,x,y)\bigr),\\
&\operatorname{Decidable}
\bigl(\operatorname{PredictionEscape}(q,\tau,N,x,y)\bigr),\\
&\operatorname{Decidable}
\bigl(P_N^{q,\tau}(x)=P_N^{q,\tau}(y)\bigr).
\end{aligned}
\]

该义务不要求 `Fintype X`、`Fintype O` 或 `Nonempty X`。

## 56.5 对第 54.3 部三条义务的追加式精确重述

从本部追加后，第 54.3 部相关文字按以下自包含命题消费；旧编号不删除。

1. **第 9 条商序半条。** 对任意有限
   \(F:\operatorname{Finset}(\mathsf{Action})\)
   和五个可判预序坐标，弱支配对称核
   `ParetoEqOn`
   形成可判等价关系；显式类像
   `FiniteParetoQuotient`
   上的
   `QuotientParetoWeak`
   代表无关且满足反身、传递、反对称。若五坐标是偏序，则该对称核恰等于同向量等价。证明目标精确为 56.2-A—56.2-D。

2. **第 10 条 Stop 半条。** `Stop` 精确指
   `AdjudicationStopTarget`
   即既有 `OrientedStop`；其有限检查器为 `settleStop`。具体
   \(\operatorname{Fin}(2)\)
   见证满足
   `NoDominatingCandidate`
   而在完整
   \(O_{\mathrm{advance}}\)
   下不满足 Stop，并在完整
   \(O_{\mathrm{stay}}\)
   下满足 Stop。证明目标精确为 56.3-A—56.3-C。第 10 条前半的 gainDifference 自差与 cocycle 继续由已冻结
   `gain_difference_self_zero_and_cocycle`
   承担，本部不重证。

3. **第 12 条时域半条。** 对
   \(P_N^{q,\tau}:X\to(\operatorname{Fin}(N+1)\to O)\)，
   从 \(P_N\) 扩到 \(P_{N'}\) 的时域逃逸是
   `ExpansionEscape P_N P_N'`
   的实例；从当前读数 \(q\) 扩到 \(P_N\) 的第 8 部预测逃逸是
   `ExpansionEscape q P_N`
   的实例。证明目标精确为 56.4-A—56.4-E。

## 56.6 边界、非冒领与第 55 部保持开放

本部不主张弱支配商、有限轨迹、有限状态检查器或预序对称核为首创；这些都是标准初等构件。本部只把它们接到 DECT 已有接口上，以消除“实现即发明”的源缺口。

本部特别不做以下越界：

- 不从 Pareto maximal、greatest 或任意线性延伸推出新的 Stop 等价式；
- 不构造第 55.2.5 部 OP5 的线性延伸，也不改变其 open 状态；
- 不把 `NoDominatingCandidate` 的候选集语义偷换成 Stop 的可行集语义；56.3-B 特意令二者相等以排除该平凡差异；
- 不把有限商上的代表选择隐藏进 Classical.choice；
- 不要求有限承载非空；空集与单点集的行为已经逐条给出；
- 不要求时域状态空间或读数值域有限；只有时间索引有限，机器可判性另以 `DecidableEq O` 为显式前件；
- 不把本部的 Stop 布尔分量冒充完整
  \(\operatorname{Evaluate}(K_n,Z_n)\)
  的全部裁决结果。

因此，本部只关闭三条已被拒绝的源陈述缺口，不结算第 55 部任何开放问题，也不改变五条既有裁决层定理的地址或结论。

---
# 追加账本增订
## v1.4 — 2026-08-26

追加存入：

- 弱支配对称核 `ParetoEqOn`、有限承载枚举、显式等价类像 `FiniteParetoQuotient`、全枚举与代表无关商序；
- 在偏序坐标前件下，对称核等价与既有同向量等价的外延一致性；
- 第 54.3 部 `Stop` 的唯一指称：既有 `OrientedStop` 的有名展开 `AdjudicationStopTarget`；
- 只扫描有限可行集的 `stopCheck`/`settleStop`，以及空可行集、缺失 current 和 current 不可行时必不停止的边界律；
- 一个候选集等于可行集的 `Fin 2` 非退化见证：同一 Pareto 前沿在两个完整、来源化 OrientationSpec 下给出不同停止真值；
- `Fin (N+1)` 时域索引、有限迭代、时域投影、下标嵌入与限制律；
- 延长时域逃逸与第 8 部预测逃逸分别作为 `ExpansionEscape` 的两个精确有限实例；
- 对第 54.3 部第 9、10、12 条缺口的自包含重述；
- 第 55 部 OP1—OP6，尤其 OP5，全部保持 open；
- 零新增首创声明，零测度论前件，零既有段落回写。

后续增订继续严格追加于本节之后。

---

# 第五十七部　保护坐标重评与输运越界的语义闭合

## 57.1 拒因分析、继承接口与收窄纪律

本部是 v1.5 的追加式增订，只精确化第 54.3 部证明义务 5 的保护坐标—目标洗白半条，以及证明义务 6 的输运证书—越界收口半条。第 1—56 部的定义、开放问题、冻结结算、既有 Lean 载体与已证定理均不回写、不删除，也不因本部改变原地址。

本部预期进入既有 canonical 命名空间

`D5.S3.ConceptDynamics.DefinitionEscape.Adjudication`

并直接复用第 54.3 部已经给出的

`ProtectedCoordinates`、`protectedCoordinates`、`RegradeReport`、`TransportCert`、`TransportReport`、`TransportSemantics`、`ValidTransportCert`、`HasValidTransportCert` 与 `Overreach`。

本部只使用以下初等构件：

- 七元有限标签、依值类型与 `Finset`；
- 结构投影、函数外延、等式与不等式；
- `Option` 表示的部分运行结果；
- 合取、存在、否定与带证明的布尔判定；
- 对既有载体的语义解释器及其遗忘映射。

不引入测度、概率、拓扑、统计显著性、任意选择、商代表、外生许可证布尔门或新的目标成功标准。除明确写出的可判等号与可判关系外，不暗加 `Fintype`、`Nonempty` 或有限状态前件。

### 57.1.1 第 54.3-5 条拒因：直接投影不等式不是完整洗白语义

原判词为：

> “Protected-coordinate and target-laundering behavior is not an elementary atom: an honest closure needs a broader semantic regrade and coordinate-witness bundle.”

该拒因指出的不是 `protectedCoordinates` 投影错误，而是源理论只给出了

`protectedCoordinates newK ≠ protectedCoordinates oldK`

这一整体不等式，却缺少使“哪一项保护承诺被改写”成为可审计对象的坐标语义。原结构有七个异型字段；整体不等式只能证明“至少有一项不同”，不能给出：

1. 七个保护字段的有限、穷尽标签；
2. 每个标签对应的依值字段类型；
3. 声称发生变化的标签集合；
4. 集合中每个标签确实变化的可靠性；
5. 所有实际变化标签均被登记的封闭性。

因此必须增加坐标见证束。该见证束不是保护坐标的第二份副本；它只保存标签集合及其正确性证明，字段值仍唯一来自既有 `ProtectedCoordinates`。

原 `RegradeReport` 还只携带修订承诺对旧证据给出的实际判词。它证明

`report.regradedVerdict = evaluate report.revised report.evidence`

却没有同时把原承诺对同一证据的判词放入一个有类型语义对象。若没有这一半，所谓“重评”仍只是单次新评价加若干外部等式，而不是同一证据、原承诺、修订承诺之间的语义关系。

同时，源理论中存在两种不可静默混同的时间口径：

- 正文口径要求证据严格先于修订承诺的冻结时刻到达；
- 后置 Lean 草图要求证据在冻结事件处可见，并另要求报告时间戳等于冻结时刻。

二者只有在显式给出“冻结可见当且仅当严格到达后”的桥时才能互换。故本部把二者定义成两个独立谓词，并把桥本身作为有名结构；不从滤过单调性、事件时钟单调性或首次可达定义中擅自推出该桥。

目标洗白也不要求原判词与修订判词不同。只要到达后改变保护坐标、用修订坐标重评旧证据，并把结果归因于原承诺，即可构成洗白。报告时间戳等于冻结时刻同样只属于后置草图，不进入正文级洗白判据。

### 57.1.2 第 54.3-6 条拒因：Prop 级合取没有给出输运运行语义

原判词为：

> “Transport-certificate and overreach closure is not an elementary atom: an honest closure needs broader transport semantics plus failure and refutation witnesses.”

第 54.3 部的 `TransportSemantics` 把以下项目全部留作互不相关的 Prop 级接口：

- `strictSubset`；
- `inNewOnlyDomain`；
- `predictionDefined`；
- `predictionFails`；
- `refutes`。

这足以陈述一个合取，却没有保证：

1. 严格扩域真的包含一个新域差点；
2. “有定义”“失败”“反驳”来自同一次预测运行；
3. 失败见证携带实际运行结果；
4. 反驳见证是在同一结果上同时证明失败与对主张的反驳；
5. 去掉类型化语义后所得 Prop 级接口精确回到原 `ValidTransportCert`；
6. 越界只能由同一个有效证书谓词及精确保留条件的报告许可证收口。

若把 `predictionFails` 与 `refutes` 任意赋值为两个无关谓词，即使各自存在见证，也不能证明它们描述同一次失败。若另造一个“新证书有效性”谓词，又会与已经冻结的 `ValidTransportCert` 形成第二真源。

因此本部增加一个带部分运行结果的输运语义框架。它不替换 `TransportCert` 或 `TransportReport`，而是解释其预测字段；失败见证保存新域差点、运行结果与失败证明，反驳见证在同一结果上追加反驳证明。新有效性结构经遗忘后必须与原 `ValidTransportCert` 双向等价；越界闭包仍由原有报告条件与同一证书有效性解除。

---

## 57.2 保护坐标语义与坐标见证束

以下 Lean 代码块按出现顺序拼接为一个模块。所有既有名称均指第 54.3 部的 canonical 定义，不在本部重声明。

### 57.2.1 七个保护坐标的有限标签与依值投影

```lean
universe u v

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

inductive ProtectedCoordinateTag
  | targetChain
  | domain
  | epsilon
  | conditions
  | comparator
  | baseline
  | weightSpec
  deriving DecidableEq, Fintype
```

`ProtectedCoordinateTag` 穷尽且只穷尽既有 `ProtectedCoordinates` 的七个字段。`testPlan`、`decision`、被承诺对象与日志坐标不因本部被暗中提升为保护坐标；若未来要改变保护集合，必须另作追加式理论修订，不能只改枚举。

```lean
def ProtectedCoordinateValue
    (TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u) :
    ProtectedCoordinateTag → Type u
  | .targetChain => TargetChain
  | .domain => Domain
  | .epsilon => Epsilon
  | .conditions => Condition
  | .comparator => Comparator
  | .baseline => Baseline
  | .weightSpec => WeightSpec
```

`ProtectedCoordinateValue` 给出标签对应的依值类型。七个字段不被强迫进入同一和类型，也不借助字符串、动态类型或不可核验强制转换抹平其异型性。

```lean
def protectedCoordinateAt
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    (coordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec)
    (tag : ProtectedCoordinateTag) :
    ProtectedCoordinateValue TargetChain Domain Epsilon Condition Comparator
      Baseline WeightSpec tag :=
  match tag with
  | .targetChain => coordinates.targetChain
  | .domain => coordinates.domain
  | .epsilon => coordinates.epsilon
  | .conditions => coordinates.conditions
  | .comparator => coordinates.comparator
  | .baseline => coordinates.baseline
  | .weightSpec => coordinates.weightSpec
```

`protectedCoordinateAt` 是既有保护坐标记录的依值投影。它不保存字段副本；任何坐标见证最终都必须回到该投影的等式或不等式。

### 57.2.2 坐标见证束及其封闭条件

```lean
structure CoordinateWitnessBundle
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    (oldCoordinates newCoordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec) where
  changed : Finset ProtectedCoordinateTag
  sound :
    ∀ tag, tag ∈ changed →
      protectedCoordinateAt oldCoordinates tag ≠
        protectedCoordinateAt newCoordinates tag
```

`CoordinateWitnessBundle` 登记一组声称已经改变的保护标签。`sound` 排除伪报：束中每个标签都必须在既有记录的相应投影上确实不同。该结构故意不要求 `changed` 非空，因为空束仍可诚实表示“没有登记任何变化”；洗白判据将另行要求非空。

```lean
namespace CoordinateWitnessBundle

def Closed
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    {oldCoordinates newCoordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec}
    (bundle : CoordinateWitnessBundle oldCoordinates newCoordinates) : Prop :=
  ∀ tag,
    protectedCoordinateAt oldCoordinates tag ≠
      protectedCoordinateAt newCoordinates tag →
    tag ∈ bundle.changed

end CoordinateWitnessBundle
```

`CoordinateWitnessBundle.Closed` 是完备方向：所有实际变化的标签均必须进入束。与结构内的 `sound` 合并后，`bundle.changed` 恰好等于真实变化标签集；只列出一个方便字段而遗漏其他变化不算封闭见证。

```lean
def HasClosedCoordinateWitnessBundle
    {TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec :
      Type u}
    (oldCoordinates newCoordinates :
      ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec) : Prop :=
  ∃ bundle : CoordinateWitnessBundle oldCoordinates newCoordinates,
    CoordinateWitnessBundle.Closed bundle ∧ bundle.changed.Nonempty
```

`HasClosedCoordinateWitnessBundle` 要求一个可靠、完备且非空的坐标见证束。它是整体坐标不等式的审计化版本：不增加新的字段值事实，只把不等式的有限来源显式登记。

### 57.2.3 语义重评框架

```lean
structure RegradeSemantics
    (Commitment Evidence Verdict Time Coordinate : Type u)
    (Report : Type v) where
  protected : Commitment → Coordinate
  evaluate : Commitment → Evidence → Verdict
  arrival : Evidence → Time
  freezeTime : Commitment → Time
  visibleAtFreeze : Commitment → Evidence → Prop
  reportOriginal : Report → Commitment
  reportRevised : Report → Commitment
  reportEvidence : Report → Evidence
  reportVerdict : Report → Verdict
  reportAttributedTo : Report → Commitment
  reportOccurredAt : Report → Time
  reportVerdictCorrect :
    ∀ report,
      reportVerdict report =
        evaluate (reportRevised report) (reportEvidence report)
```

`RegradeSemantics` 是对既有承诺与报告载体的解释器。它不新建承诺或报告字段，而是说明如何从已有载体读取保护坐标、评价、到达时间、冻结时间、冻结可见性及报告各项。最后一项把“报告判词确为修订承诺对旧证据的实际评价”提升为解释器定律，禁止调用方另传一个不受约束的成功布尔值。

```lean
structure SemanticRegrade
    {Commitment Evidence Verdict Time Coordinate : Type u}
    {Report : Type v}
    (S : RegradeSemantics Commitment Evidence Verdict Time Coordinate Report)
    where
  report : Report
  originalVerdict : Verdict
  originalVerdictCorrect :
    originalVerdict =
      S.evaluate (S.reportOriginal report) (S.reportEvidence report)
```

`SemanticRegrade` 在既有报告之外只增加原承诺对同一证据的实际判词及其正确性证明。修订判词仍唯一来自报告和 `S.reportVerdictCorrect`。该结构不要求两个判词不同；“重评”表示评价坐标发生切换，不表示评价值必然变化。

```lean
def SemanticRegradeAt
    {Commitment Evidence Verdict Time Coordinate : Type u}
    {Report : Type v}
    {S : RegradeSemantics Commitment Evidence Verdict Time Coordinate Report}
    (regrade : SemanticRegrade S)
    (oldK newK : Commitment)
    (Z : Evidence) : Prop :=
  S.reportOriginal regrade.report = oldK ∧
    S.reportRevised regrade.report = newK ∧
    S.reportEvidence regrade.report = Z
```

`SemanticRegradeAt` 把语义重评定位到显式的原承诺、修订承诺与证据。它只表达报告身份，不把时间条件、坐标改变或归因条件重复塞入同一谓词。

```lean
def PostArrivalSemanticRegrade
    {Commitment Evidence Verdict Time Coordinate : Type u}
    {Report : Type v}
    [LT Time]
    (S : RegradeSemantics Commitment Evidence Verdict Time Coordinate Report)
    (regrade : SemanticRegrade S) : Prop :=
  S.arrival (S.reportEvidence regrade.report) <
    S.freezeTime (S.reportRevised regrade.report)
```

`PostArrivalSemanticRegrade` 对应正文级严格时间口径：证据的首次到达时刻严格早于修订承诺的冻结时刻。它不提报告时间戳，也不把事件编号与时钟值视为同一类型。

```lean
def FreezeVisibleSemanticRegrade
    {Commitment Evidence Verdict Time Coordinate : Type u}
    {Report : Type v}
    (S : RegradeSemantics Commitment Evidence Verdict Time Coordinate Report)
    (regrade : SemanticRegrade S) : Prop :=
  S.visibleAtFreeze
    (S.reportRevised regrade.report)
    (S.reportEvidence regrade.report)
```

`FreezeVisibleSemanticRegrade` 对应第 54.3 部后置 Lean 草图的冻结可见口径。它与严格到达后谓词分别命名，因而滤过可见性不能在没有桥的情况下冒充时钟不等式。

```lean
structure RegradeTemporalBridge
    {Commitment Evidence Verdict Time Coordinate : Type u}
    {Report : Type v}
    [LT Time]
    (S : RegradeSemantics Commitment Evidence Verdict Time Coordinate Report) :
    Prop where
  visibility_iff_arrival :
    ∀ K Z,
      S.visibleAtFreeze K Z ↔ S.arrival Z < S.freezeTime K
```

`RegradeTemporalBridge` 是两种时间口径之间唯一允许的转换接口。它必须对相关承诺与证据给出精确双向关系；事件滤过单调、时钟单调或“首次可见”名称本身均不自动生成该结构。

### 57.2.4 正文级洗白、草图级洗白与判定证书

```lean
def SemanticTargetLaunderingAt
    {Commitment Evidence Verdict Time TargetChain Domain Epsilon Condition
      Comparator Baseline WeightSpec : Type u}
    {Report : Type v}
    [LT Time]
    (S :
      RegradeSemantics Commitment Evidence Verdict Time
        (ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
          Baseline WeightSpec)
        Report)
    (oldK newK : Commitment)
    (Z : Evidence)
    (regrade : SemanticRegrade S) : Prop :=
  SemanticRegradeAt regrade oldK newK Z ∧
    PostArrivalSemanticRegrade S regrade ∧
    S.reportAttributedTo regrade.report = oldK ∧
    HasClosedCoordinateWitnessBundle
      (S.protected oldK) (S.protected newK)
```

`SemanticTargetLaunderingAt` 是正文级语义重评判据。它恰有四层：报告定位、严格到达后、归因于原承诺、保护坐标的封闭非空见证束。修订判词的真实性由语义框架承担，原判词的真实性由 `SemanticRegrade` 承担，故这里不再重复评价等式。

该定义不要求：

- 原判词与修订判词不同；
- 报告发生时刻等于冻结时刻；
- 修订承诺与原承诺整体不等；
- 非保护字段保持相同。

它只判定第 54 部所说的保护坐标回写与旧轮归因，不把其他治理违规混入同一原子。

```lean
def SemanticSketchTargetLaunderingAt
    {Commitment Evidence Verdict Time TargetChain Domain Epsilon Condition
      Comparator Baseline WeightSpec : Type u}
    {Report : Type v}
    (S :
      RegradeSemantics Commitment Evidence Verdict Time
        (ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
          Baseline WeightSpec)
        Report)
    (oldK newK : Commitment)
    (Z : Evidence)
    (regrade : SemanticRegrade S) : Prop :=
  SemanticRegradeAt regrade oldK newK Z ∧
    FreezeVisibleSemanticRegrade S regrade ∧
    S.reportOccurredAt regrade.report = S.freezeTime newK ∧
    S.reportAttributedTo regrade.report = oldK ∧
    HasClosedCoordinateWitnessBundle
      (S.protected oldK) (S.protected newK)
```

`SemanticSketchTargetLaunderingAt` 精确保留后置 Lean 草图的两个额外选择：冻结事件可见性和报告时间戳等于冻结时刻。它不是正文级定义的别名；在给出 `RegradeTemporalBridge` 后，它才等价于正文级洗白再合取时间戳条件。

```lean
structure TargetLaunderingDecision
    {Commitment Evidence Verdict Time TargetChain Domain Epsilon Condition
      Comparator Baseline WeightSpec : Type u}
    {Report : Type v}
    [LT Time]
    (S :
      RegradeSemantics Commitment Evidence Verdict Time
        (ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
          Baseline WeightSpec)
        Report)
    (oldK newK : Commitment)
    (Z : Evidence)
    (regrade : SemanticRegrade S) where
  verdict : Bool
  correct :
    verdict = true ↔
      SemanticTargetLaunderingAt S oldK newK Z regrade
```

`TargetLaunderingDecision` 是带正确性证明的判定结果，而不是外生准入门。只有在所需等式与时间关系可判时才能构造该结构；不能先给一个布尔值，再把它当作洗白事实。

### 57.2.5 对第 54.3 部既有载体的标准解释器

```lean
def prospectiveRegradeSemantics
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Verdict : Type u}
    [LinearOrder EventId]
    [Preorder Time]
    [DecidableEq Artifact]
    {n : Round}
    (arrival : Evidence → Time)
    (evaluate :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n →
      Evidence → Verdict) :
    RegradeSemantics
      (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
      Evidence
      Verdict
      Time
      (ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
        Baseline WeightSpec)
      (RegradeReport
        (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
          Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
        Evidence Verdict Time evaluate) where
  protected := protectedCoordinates
  evaluate := evaluate
  arrival := arrival
  freezeTime := fun K => K.adjudication.frozenAt
  visibleAtFreeze := fun K Z =>
    Z ∈ K.adjudication.filtration.seen K.adjudication.freezeEvent
  reportOriginal := fun report => report.original
  reportRevised := fun report => report.revised
  reportEvidence := fun report => report.evidence
  reportVerdict := fun report => report.regradedVerdict
  reportAttributedTo := fun report => report.attributedTo
  reportOccurredAt := fun report => report.occurredAt
  reportVerdictCorrect := fun report => report.regradesOldRound
```

`prospectiveRegradeSemantics` 只是第 54.3 部既有载体的标准解释器。它直接调用 `protectedCoordinates` 和 `RegradeReport` 投影，不复制其七个字段，也不另造报告正确性谓词。后续 Lean 模块若已经导入冻结载体，应构造同形解释器，而不是重新声明 `ProspectiveCommitment`、`ProtectedCoordinates` 或 `RegradeReport`。

---

## 57.3 输运语义与证书

### 57.3.1 带运行结果的输运语义

```lean
structure TransportSemanticFrame
    (TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u)
    (PredictionResult : Type v) where
  claimAddress : Claim → ContentAddress
  claimScope : Claim → Domain
  claimVersion : Claim → Version
  receiptMatches :
    TruthReceipt → ContentAddress → Domain → Version → Prop
  claimOn : Claim → Domain → Prop
  inDomain : NewEvidence → Domain → Prop
  run : NewDomainPrediction → NewEvidence → Option PredictionResult
  fails :
    NewDomainPrediction → NewEvidence → PredictionResult → Prop
  refutes :
    NewDomainPrediction → NewEvidence → PredictionResult → Claim → Prop
```

`TransportSemanticFrame` 把第 54.3 部的 Prop 级预测接口提升为部分运行语义。`run p z = none` 表示预测在该点未定义，`some result` 表示取得一个具体结果；失败与反驳都以同一结果为参数。该框架不假定结果有可判等号、度量、概率或损失结构。

```lean
def SemanticNewOnly
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (z : NewEvidence)
    (J J' : Domain) : Prop :=
  S.inDomain z J' ∧ ¬ S.inDomain z J
```

`SemanticNewOnly` 给出有方向的新域差：点属于报告域而不属于原域。它不接受另一个与成员关系无关的 `inNewOnlyDomain` 黑箱谓词。

```lean
def SemanticStrictSubset
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (J J' : Domain) : Prop :=
  (∀ z, S.inDomain z J → S.inDomain z J') ∧
    ∃ z, SemanticNewOnly S z J J'
```

`SemanticStrictSubset` 由成员语义定义：原域中的每个点仍在新域中，并且至少存在一个新域差点。严格扩域因而自带非空见证，不能把 `strictSubset` 与 `inNewOnlyDomain` 任意解释成互不相干的关系。

```lean
def SemanticPredictionDefined
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (prediction : NewDomainPrediction)
    (z : NewEvidence) : Prop :=
  ∃ result, S.run prediction z = some result
```

`SemanticPredictionDefined` 是部分运行返回具体结果的存在命题。它不是独立可赋值的 Prop 字段。

```lean
def SemanticPredictionFails
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (prediction : NewDomainPrediction)
    (z : NewEvidence) : Prop :=
  ∃ result,
    S.run prediction z = some result ∧
      S.fails prediction z result
```

`SemanticPredictionFails` 要求预测在该点实际运行并产生一个满足失败关系的结果。取恒假失败关系会直接排除任何失败见证，而不是由外部非真空口号补救。

```lean
def SemanticRefutes
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (z : NewEvidence)
    (cert : TransportCert TruthReceipt NewDomainPrediction)
    (claim : Claim) : Prop :=
  ∃ result,
    S.run cert.falsifiablePrediction z = some result ∧
      S.refutes cert.falsifiablePrediction z result claim
```

`SemanticRefutes` 把反驳绑定到证书所登记预测的一次实际运行。它仍是对第 54.3 部 Prop 级接口的遗忘结果；更强的同一结果失败—反驳绑定由下面的类型化见证承担。

### 57.3.2 对原 Prop 级接口的唯一遗忘映射

```lean
namespace TransportSemanticFrame

def toLegacy
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult) :
    TransportSemantics TruthReceipt NewDomainPrediction Claim ContentAddress
      Domain Version NewEvidence where
  claimAddress := S.claimAddress
  claimScope := S.claimScope
  claimVersion := S.claimVersion
  receiptMatches := S.receiptMatches
  strictSubset := SemanticStrictSubset S
  claimOn := S.claimOn
  inNewOnlyDomain := SemanticNewOnly S
  predictionDefined := SemanticPredictionDefined S
  predictionFails := SemanticPredictionFails S
  refutes := SemanticRefutes S

end TransportSemanticFrame
```

`TransportSemanticFrame.toLegacy` 是新语义回到第 54.3 部 `TransportSemantics` 的唯一遗忘映射。后续证明必须通过该映射复用原 `ValidTransportCert` 与 `Overreach`；不得另造第二个不相容的 Prop 级运输接口。

### 57.3.3 失败见证与反驳见证

```lean
structure TransportFailureWitness
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (prediction : NewDomainPrediction)
    (J J' : Domain) where
  evidence : NewEvidence
  newOnly : SemanticNewOnly S evidence J J'
  result : PredictionResult
  observed : S.run prediction evidence = some result
  failed : S.fails prediction evidence result
```

`TransportFailureWitness` 保存新域差点、实际运行结果与失败证明。它排除“在一个点有定义、在另一个点失败”或“只宣称存在失败但不展示运行结果”的弱化解释。

```lean
structure TransportRefutationWitness
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (cert : TransportCert TruthReceipt NewDomainPrediction)
    (claim : Claim)
    (J J' : Domain) where
  failure :
    TransportFailureWitness S cert.falsifiablePrediction J J'
  refutesClaim :
    S.refutes cert.falsifiablePrediction
      failure.evidence failure.result claim
```

`TransportRefutationWitness` 在同一个失败见证及同一个运行结果上追加对被输运主张的反驳。失败与反驳因此既可分别读取，又不能由两个无关结果拼接。

### 57.3.4 证书合法性结构及其 Prop 闭包

```lean
structure SemanticTransportCertificate
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (cert : TransportCert TruthReceipt NewDomainPrediction)
    (claim : Claim)
    (J J' : Domain)
    (version : Version) where
  strictExpansion : SemanticStrictSubset S J J'
  receiptBound :
    S.receiptMatches cert.oldReceipt
      (S.claimAddress claim) J version
  conditionalTransport :
    cert.givenPremises →
      cert.transportAssumption →
      S.claimOn claim J'
  totalOnNewOnly :
    ∀ z, SemanticNewOnly S z J J' →
      SemanticPredictionDefined S cert.falsifiablePrediction z
  refutingFailure :
    TransportRefutationWitness S cert claim J J'
```

`SemanticTransportCertificate` 是证书合法性的类型化证明对象。五项分别对应严格扩域、claim-bound 原域收据、保留前件的条件输运、新域差上的全定义，以及同一运行结果上的失败—反驳见证。它不增加外部“已批准”字段。

```lean
def ValidSemanticTransportCert
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (cert : TransportCert TruthReceipt NewDomainPrediction)
    (claim : Claim)
    (J J' : Domain)
    (version : Version) : Prop :=
  Nonempty
    (SemanticTransportCertificate S cert claim J J' version)
```

`ValidSemanticTransportCert` 只是上述证明对象的存在闭包。它不是与 `ValidTransportCert` 并行的第二套真值；57.3-C 将要求它经 `toLegacy` 后与原谓词双向等价。

### 57.3.5 报告许可证、越界闭包与越界判据

```lean
structure LicensedSemanticTransportReport
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (report : TransportReport Claim Domain)
    (J : Domain) where
  cert : TransportCert TruthReceipt NewDomainPrediction
  valid :
    ValidSemanticTransportCert S cert report.claim J report.reportedDomain
      (S.claimVersion report.claim)
  conditionExact :
    report.condition ↔
      cert.givenPremises ∧ cert.transportAssumption
```

`LicensedSemanticTransportReport` 要求报告携带同一主张、原域、报告域与主张版本上的有效证书，并精确保留证书前件。无条件报告只有在两项前件均成立时才能获得许可证；把报告条件弱化为真、遗漏一项前件或使用其他版本证书均不能构造该结构。

```lean
def OverreachClosure
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (report : TransportReport Claim Domain)
    (J : Domain) : Prop :=
  Nonempty (LicensedSemanticTransportReport S report J)
```

`OverreachClosure` 是越界指控的正向收口证书：存在一个合法报告对象。它不接受外部布尔门，也不允许只证明“某个证书大致有效”而不证明报告条件精确对应其前件。

```lean
def SemanticOverreach
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (report : TransportReport Claim Domain)
    (J : Domain) : Prop :=
  SemanticStrictSubset S J report.reportedDomain ∧
    S.claimScope report.claim = J ∧
    ¬ OverreachClosure S report J
```

`SemanticOverreach` 恰表示：报告严格扩张原主张范围、主张原范围确为 `J`，且不存在合法输运报告对象。严格扩域本身不自动构成许可证；局部闭合也不自动输运到新域。反之，一旦 `OverreachClosure` 成立，同一报告便不再满足该越界谓词。

```lean
end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
```

---

## 57.4 证明义务清单

本部共提出十条义务。每条都只消费 57.2—57.3 已经给出的类型和谓词；不存在“先寻找合适定义”或“补充自然假设”式开放项。

### 57.4.1 保护坐标与目标洗白义务

**证明义务 57.2-A（保护坐标依值外延，预期为定理）。** 对任意适型的七个字段类型及任意 `oldCoordinates newCoordinates : ProtectedCoordinates ...`，证明单一命题

```lean
oldCoordinates = newCoordinates ↔
  ∀ tag,
    protectedCoordinateAt oldCoordinates tag =
      protectedCoordinateAt newCoordinates tag
```

该证明只允许结构外延与对 `ProtectedCoordinateTag` 的有限分类，不需要任何字段可判等号。

**证明义务 57.2-B（封闭非空见证束刻画整体变化，预期为定理）。** 若七个字段类型各自有 `DecidableEq`，则对任意 `oldCoordinates newCoordinates` 证明

```lean
HasClosedCoordinateWitnessBundle oldCoordinates newCoordinates ↔
  oldCoordinates ≠ newCoordinates
```

从右到左应以七标签有限扫描构造真实变化集；从左到右应由非空标签及 `sound` 投影出整体记录不等。

**证明义务 57.2-C（正文级洗白的束消去判据，预期为定理）。** 在 57.2-B 的可判等号前件下，对任意 `S oldK newK Z regrade` 证明

```lean
SemanticTargetLaunderingAt S oldK newK Z regrade ↔
  SemanticRegradeAt regrade oldK newK Z ∧
    PostArrivalSemanticRegrade S regrade ∧
    S.reportAttributedTo regrade.report = oldK ∧
    S.protected oldK ≠ S.protected newK
```

该命题只把完整坐标见证束消去为既有整体不等式，不得删除报告身份、严格时间或归因条件。

**证明义务 57.2-D（草图口径与正文口径的精确桥，预期为定理）。** 对任意 `bridge : RegradeTemporalBridge S`，证明

```lean
SemanticSketchTargetLaunderingAt S oldK newK Z regrade ↔
  SemanticTargetLaunderingAt S oldK newK Z regrade ∧
    S.reportOccurredAt regrade.report = S.freezeTime newK
```

没有 `bridge` 时不得提供该等价式；特别地，不得只凭滤过单调或事件时钟单调省略桥前件。

**证明义务 57.2-E（洗白判定证书，预期为可判定性）。** 若有

```lean
DecidableEq Commitment
DecidableEq Evidence
DecidableEq TargetChain
DecidableEq Domain
DecidableEq Epsilon
DecidableEq Condition
DecidableEq Comparator
DecidableEq Baseline
DecidableEq WeightSpec
DecidableRel (fun a b : Time => a < b)
```

则对任意 `S oldK newK Z regrade` 构造

```lean
Nonempty
  (TargetLaunderingDecision S oldK newK Z regrade)
```

该构造不得要求 `Fintype Commitment`、`Fintype Evidence`、`DecidableEq Verdict`、`Nonempty Commitment` 或原判词与修订判词不同。

### 57.4.2 输运证书与越界收口义务

**证明义务 57.3-A（严格扩域产生新域差见证，预期为定理）。** 对任意 `S J J'` 证明

```lean
SemanticStrictSubset S J J' →
  ∃ z, SemanticNewOnly S z J J'
```

该命题由严格扩域的第二分量得到，不要求域类型或证据类型有限、非空或可判等。

**证明义务 57.3-B（类型化反驳见证的 Prop 投影，预期为定理）。** 对任意 `w : TransportRefutationWitness S cert claim J J'`，证明

```lean
∃ z,
  SemanticNewOnly S z J J' ∧
    SemanticPredictionDefined S cert.falsifiablePrediction z ∧
    SemanticPredictionFails S cert.falsifiablePrediction z ∧
    SemanticRefutes S z cert claim
```

四个结论必须由 `w.failure` 的同一点和同一结果构造，不能分别选择三个互不相关的运行见证。

**证明义务 57.3-C（类型化证书与原有效性谓词的精确等价，预期为定理）。** 对任意 `S cert claim J J' version` 证明

```lean
ValidSemanticTransportCert S cert claim J J' version ↔
  ValidTransportCert S.toLegacy cert claim J J' version
```

从右到左合并 `SemanticPredictionFails` 与 `SemanticRefutes` 的结果时，只可利用二者都等于同一次 `run` 的 `some` 值；不得假设 `DecidableEq PredictionResult`，也不得另加结果唯一性公理。

**证明义务 57.3-D（越界收口判据，预期为定理）。** 对任意 `S report J`，在给定严格扩域和原范围等式时证明

```lean
SemanticStrictSubset S J report.reportedDomain →
S.claimScope report.claim = J →
  (SemanticOverreach S report J ↔
    ¬ OverreachClosure S report J)
```

该式是越界的方向化收口准则，不使用双重否定消去，不要求 `OverreachClosure` 可判。

**证明义务 57.3-E（新越界语义回降到第 54.3 部，预期为定理）。** 对任意 `S report J` 证明

```lean
SemanticOverreach S report J ↔
  Overreach S.toLegacy report J
```

该证明必须经 57.3-C 把许可证中的 `ValidSemanticTransportCert` 回降为原 `ValidTransportCert`；禁止复制原 `Overreach` 合取后把双向等价伪装成第二个独立定理源。

---

## 57.5 与既有冻结定理的关系、唯一真源与非越界边界

### 57.5.1 保护坐标侧的直接复用

57.2 直接消费既有 `ProtectedCoordinates` 与 `protectedCoordinates`。七标签只是该记录的有限索引，不得重新声明第二个七字段结构。义务 57.2-A—57.2-B 只证明“整体不等”与“封闭非空变化标签束”之间的等价。

既有冻结定理

`regrade_report_carries_actual_evaluation`

继续唯一承担“报告判词确为修订承诺对报告证据的实际评价”。`RegradeSemantics.reportVerdictCorrect` 的标准实例必须直接填入该证明字段或其定义相同的投影；不得重建一个独立的评价正确性公理。

既有冻结定理

`target_laundering_criterion`

继续唯一承担正文级三合取：

- 严格到达后的保护坐标改变；
- 对旧证据的实际重评；
- 把修订评价归因于原承诺。

57.2-C 只把其中的保护坐标整体不等式细化为坐标见证束。以冻结载体实例化 `RegradeSemantics` 后，57.2-C 与 `target_laundering_criterion` 合成的桥应作为推论导出；不得在新模块中复制正文级 `TargetLaundering` 定义。

既有冻结定理

`target_laundering_sketch_criterion`

继续唯一承担后置草图的冻结可见性与额外报告时间戳。57.2-D 只说明在显式 `RegradeTemporalBridge` 下，草图语义等于正文语义再合取该时间戳条件。

既有冻结定理

`freeze_visible_iff_post_arrival_under_exact_bridge`

可直接为 57.2-D 提供保护变化部分的转换。其桥前件不得从名称、单调性或首次可达约定中删除。

既有冻结定理

`post_arrival_protected_change_criterion`

可直接用于展开正文级时间条件与保护坐标整体不等式；57.2 不重新证明其时间部分。

既有有限见证定理

`same_verdict_target_laundering`

与

`report_timestamp_not_required_by_boxed_criterion`

是本部定义的强制边界：

- `SemanticTargetLaunderingAt` 不得增加原判词与修订判词不等前件；
- `SemanticTargetLaunderingAt` 不得增加报告时间戳等于冻结时刻前件；
- 时间戳等式只属于 `SemanticSketchTargetLaunderingAt`；
- 任一新增义务若排除上述两个冻结见证，即为 statement-revise，而不是证明失败。

旧轮结算守恒仍由既有冻结的目标变更—结算守恒定理承担。`SemanticRegrade` 是一份带来源的重评对象，不修改原承诺、原报告或原结算值。

### 57.5.2 输运侧的直接复用

57.3 不重声明 `TransportCert`、`TransportReport` 或 `TransportSemantics`。`TransportSemanticFrame` 只为既有预测字段提供运行结果解释，`toLegacy` 是回到原 Prop 级接口的唯一出口。

既有冻结定理

`receipt_matches_original_coordinates`

继续唯一承担收据对原记录、原域、版本、误差与主张地址的锁定。57.3 的 `receiptBound` 不得用一组较弱的字段等式替换该收据谓词。

既有冻结定理

`valid_transport_cert_criterion`

继续唯一承担原 `ValidTransportCert` 的公开合取展开。57.3-C 的目标是证明类型化证书经遗忘后恰为该谓词；不得把 `SemanticTransportCertificate` 的字段再平铺成另一个永久有效性定义并让下游自行选择。

既有冻结定理

`valid_transport_cert_fails_if_any_clause_fails`

可直接用于证明：收据、条件输运、全定义或失败—反驳见证任一缺失时，57.3-C 右侧不成立，因而左侧也不成立。本部不重证四项删除失败律。

既有冻结定理

`falsifiable_prediction_failure_is_not_const_false`

继续排除冻结载体中恒假失败谓词。57.3 的类型化失败见证提供更细的运行结果，但不把该非退化定理改写成新的全局存在公理。

既有冻结定理

`overreach_without_license`

继续唯一承担许可证、条件保留、越界与扩域重开的组合结论。57.3-D—57.3-E 只给出新语义层的收口与遗忘桥，不复制该组合包。

既有冻结定理

`domain_expansion_reopens_completion`

继续提供“旧域闭合不推出扩域闭合”的有限反例。故 `SemanticStrictSubset` 不能被弱化为普通包含，`OverreachClosure` 也不能从旧域局部闭合自动构造。

### 57.5.3 与第 56 部十二条义务的正交关系

第 56 部的十二条义务已经由 Lean 内核结案，本部不得重复：

1. 56.2-A—56.2-D 的有限 Pareto 商只在某个具体输运域被实例化为有限 Pareto 类像时可直接引用；57.3 的一般域语义不要求该实例。
2. 56.3-A—56.3-C 的 `Stop` 指称、有限检查器与非退化见证和本部两条拒因正交；57.x 不从洗白或越界推出新的停止定理。
3. 56.4-A—56.4-E 的有限时域投影、限制律与 `ExpansionEscape` 实例可在 `Domain` 取有限时域时直接引用；本部不重证投影核反单调或预测逃逸等价。
4. `ExpansionEscape` 仍是扩展读数暴露旧核盲点的唯一既有接口；`SemanticNewOnly` 描述的是输运域差点，不得冒充预测核逃逸，二者只有在具体实例给出桥时才能连接。

因此，第 56 部全部十二条义务继续保持已证状态，第 55 部开放问题继续保持 open；本部不借两条新语义闭合结算任何未列出的父问题。

### 57.5.4 唯一真源纪律

入库实现必须遵守以下单源规则：

- 已有冻结载体存在时，只增加 `RegradeSemantics` 或 `TransportSemanticFrame` 的解释器实例，不复制载体；
- 已有冻结谓词存在时，只证明 57.2-C、57.2-D、57.3-C、57.3-E 一类双向桥，不另造供下游选择的同义谓词；
- 坐标见证束只索引既有 `ProtectedCoordinates`，不保存第二份坐标值；
- 失败与反驳见证只解释既有证书中的 `falsifiablePrediction`，不允许替换预测；
- `OverreachClosure` 只由带同一报告、同一主张版本和精确保留条件的许可证对象构造；
- 正文级严格到达与草图级冻结可见保持两个名字，除非显式持有 `RegradeTemporalBridge`；
- 不从本部推出统计泛化、外部有效性、因果输运、显著性、最优停止或跨问题迁移结论。

本部的结案范围精确为：

$\boxed{\text{保护坐标变化有封闭见证，重评有双评价语义，输运失败与反驳绑定同一次运行，越界由同一有效证书闭合。}}$

除此之外均不在 v1.5 的证明承诺内。

---

# 追加账本增订

## v1.5 — 2026-08-28

追加存入：

- 七个既有保护坐标的有限标签 `ProtectedCoordinateTag`、依值类型 `ProtectedCoordinateValue` 与唯一投影 `protectedCoordinateAt`；
- 可靠坐标见证束 `CoordinateWitnessBundle`、完备条件 `Closed` 及封闭非空存在谓词；
- 对既有承诺与报告载体的宇宙多态解释器 `RegradeSemantics`；
- 同时携带原评价证明并复用报告修订评价证明的 `SemanticRegrade`；
- 正文级严格到达、草图级冻结可见及显式 `RegradeTemporalBridge`；
- 不要求判词改变或报告时间戳等于冻结时刻的正文级 `SemanticTargetLaunderingAt`；
- 保留草图额外时间戳条件的 `SemanticSketchTargetLaunderingAt`；
- 带正确性证明的 `TargetLaunderingDecision`；
- 带 `Option` 运行结果、域成员、失败关系与反驳关系的 `TransportSemanticFrame`；
- 由成员关系定义的新域差与严格扩域；
- 同一次运行上的 `TransportFailureWitness` 与 `TransportRefutationWitness`；
- 五项合法性条件组成的 `SemanticTransportCertificate` 及其 Prop 闭包；
- 精确保留报告条件的 `LicensedSemanticTransportReport`、`OverreachClosure` 与 `SemanticOverreach`；
- 回降到第 54.3 部 `TransportSemantics`、`ValidTransportCert` 与 `Overreach` 的唯一遗忘映射及双向桥；
- 五条 57.2 义务与五条 57.3 义务，共十条 elementary 证明目标；
- 第 56 部十二条已证义务零重证，第 55 部开放问题零结算；
- 零新增首创声明，零既有段落回写，零第二真源。

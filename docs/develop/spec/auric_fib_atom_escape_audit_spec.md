# AURIC FIB ATOM 逃逸审计与分层编码规范

**文档状态：** 规范性草案（Normative Draft）
**版本：** 0.1 — Typed-FIB / Two-Level-Arena / Kernel-Residual / Layered-Code / No-Scalar-Score
**适用范围：** 任意定理 occurrence 的作者所有类型化分析合同，以及满足相应来源证据的有限信息逃逸分析和 AURIC FIB ATOM 原生应用。

本规范定义来源所有者提交分析合同的通用入口，并规定 FIB ATOM 有限原子关系在其中的适配。任意定理种类均有资格提交忠实对应原源码的类型化合同；通用入口不以定理名称或某个固定命题类型识别资格。可表示合同不要求正的证明逃逸、正的信息增益、有限状态、已取得概率律或 Fibonacci 语义。有限数值与 FIB 字段各自受后文证据条件约束。规范规定对象、量、证明义务和边界，不把接口要求声明为已实现的编译能力，也不改变现有准入状态。

## 摘要

通用合同连接原定理、实际来源、读出、选定任务与层；分析是普通证明逃逸登记的独立下游读数，不修复或认证四槽登记。满足 FIB 来源对应的应用由两层组成：

1. **微观状态层**：窗口、历史、接缝、守卫和回复构成有限或有界的 Arena.State。逃逸审计在这一层比较读出，形成不可区分核、残余逃逸和分层捕获。
2. **宏观律层**：五模式概率律形成 AURIC FIB ATOM 金字塔。三均值坐标描述粗观察，关联坐标描述被粗观察遗忘的联合关系，原生续接律描述该遗忘怎样影响后续任务。

两层通过实际来源到概率律的推前映射连接。微观读出产生代码碰撞；宏观坐标描述这些碰撞所属的概率律纤维。两层的量不得混作一个无类型标量。

FIB 应用的基本产物是一个分层编码向量，而不是人工评分：

$$
\left(
\operatorname{atom},
\operatorname{seam},
\operatorname{pyramidFiber},
\operatorname{associationResidual},
\operatorname{continuationResidual},
\operatorname{escapeRate},
\operatorname{uniqueCapture},
\operatorname{layerSpectrum}
\right).
$$

现有信息逃逸理论已经提供有限 arena、primitive bundle、联合 kernel、逃逸率、留一增益、generated-kernel lattice 和 layered capture 的数学接口。本规范为 AURIC FIB ATOM 规定接入合同。AURIC FIB ATOM 的理论公式在完成对应 D5 Lean 桥接前属于参考输入，不自动成为形式化真值。

## 1. 角色分离

### 1.1 证明逃逸与信息逃逸

“逃逸”在本规范中有两个互不替代的含义。

**证明逃逸审计**回答：新声明是否产生了相对于既有前置的真实内容，且该内容位于目标结论的活推导路径上。它使用现有登记合同、实现桥、读出、来源选择、族记录和续接字段，以及既有的 CUT、FLOW、ADMIT、ANCHOR primitive 体系。

**信息逃逸分析**回答：一组读出让哪些不同状态保持不可区分，以及增加一个读出后消除了哪些碰撞。它使用状态 arena 与联合不可区分 kernel；取得完整有限呈现后才给出精确计数。

二者必须分别报告。证明逃逸成立不推出信息增益为正；信息增益为正也不替代证明逃逸登记。信息增益不得单独成为新准入状态、人工 novelty 分数或价值等级。

### 1.2 三类对象的边界

以下三类对象必须保持类型区分：

| 对象 | 例子 | 所属层 |
|---|---|---|
| 单个状态或历史 | 五模式标签、接缝、回复、有限窗口历史 | 微观状态层 |
| 来源概率律 | \(p_0,p_2,p_5,p_{25},p_3\)、\((X,Y,Z)\)、\(\kappa\)、\(\Delta\) | 宏观律层 |
| 读出目录 | primitive bundle、catalog、kernel chain | 审计层 |

\(\Delta\) 是来源律的二次统计量，不是一个未经声明的单样本仪器输出。只有当状态空间本身明确取“概率律”或等价的有限律对象时，\(\Delta\) 才能作为该 arena 的 pointwise readout。

### 1.3 不引入总评分

规范不定义以下对象：

- 把纤维宽度、逃逸率、续接损失和取得成本相加的总分；
- 用户可调权重、阈值或 target；
- 将 proof escape、information gain 和研究价值混为一项；
- 用历史 baseline 或提交顺序定义新颖度；
- 用外部程序代替 Lean kernel 对数学桥的检查。

需要选择方案时，使用带单位和条件的向量比较或 Pareto 关系。任何标量化都必须由另一个明确的应用合同单独定义。

## 2. FIB ATOM 单窗对象

### 2.1 合法原子字母

固定占位坐标

$$
x=\text{低位 }2,\qquad
y=\text{高位 }5,\qquad
z=\text{中位 }3.
$$

合法性为

$$
x,y,z\in\{0,1\},\qquad xz=yz=0.
$$

合法原子字母为

$$
\Sigma=\{[null],[2],[5],[25],[3]\}.
$$

\([25]\) 表示两个端点共同占位；它不是一个额外位置。原生高到低读者、组成更新、接缝更新和错误回复必须由各自的 continuation contract 明确给出。

### 2.2 概率律与金字塔投影

固定一份五模式概率律

$$
p=(p_0,p_2,p_5,p_{25},p_3),\qquad
p_s\ge0,\qquad
\sum_s p_s=1.
$$

定义

$$
X=p_2+p_{25},\qquad
Y=p_5+p_{25},\qquad
Z=p_3,\qquad
r=1-Z.
$$

其合法粗坐标域是

$$
\mathcal P=
\{(X,Y,Z):X,Y,Z\ge0,\ X+Z\le1,\ Y+Z\le1\}.
$$

这三项坐标是两张共享同一 \(Z\) 的三角读出的拼接，不是两个独立来源的任意数字。

### 2.3 隐藏关联坐标

令

$$
\kappa=p_{25}.
$$

固定 \((X,Y,Z)\) 后，底面联合表为

$$
Q=
\begin{pmatrix}
r-X-Y+\kappa & Y-\kappa\\
X-\kappa & \kappa
\end{pmatrix}.
$$

合法范围是

$$
\max(0,X+Y-r)\le\kappa\le\min(X,Y).
$$

因此粗观察的遗漏纤维宽度为

$$
w=\min\{X,Y,r-X,r-Y\}.
$$

当 \(w=0\) 时该粗坐标的概率律纤维退化为单点；当 \(w>0\) 时，三均值不能恢复完整五模式律。

定义关联差

$$
\Delta=\det Q=p_0p_{25}-p_2p_5=r\kappa-XY.
$$

当 \(r>0\) 时，\((X,Y,Z,\Delta)\) 恢复 \(\kappa\) 以及全部五个概率。\(\Delta=0\) 在底面条件质量为正时等价于底面端点条件独立；它不等价于整个金字塔中的无条件独立。

### 2.4 目标敏感性

对 \(f:\Sigma\to\mathbb R\)，定义四角系数

$$
J_f=f_{25}-f_2-f_5+f_0.
$$

在固定粗坐标纤维上，目标期望只通过 \(J_f\kappa\) 感受遗漏关联。若 \(p^\ast\) 是条件独立补全 \(\kappa^\ast=XY/r\)，则

$$
\mathbb E_p[f]-\mathbb E_{p^\ast}[f]
=\frac{J_f\Delta}{r}.
$$

仅在 \(r>0\) 时使用该分式；\(r=0\) 直接使用唯一顶点。

目标在完整粗坐标纤维上的可能值宽度为

$$
|J_f|w.
$$

这给出第一种局部定量量：纤维宽度衡量来源律的隐藏空间，\(J_f\) 衡量指定任务对该空间的敏感性。

## 3. 微观状态与原生续接

### 3.1 微观 arena

对固定历史长度 \(L\)，定义有限或显式有界的状态类型

$$
H_L=\{\text{合法长度 }L\text{ 的窗口历史及其 continuation state}\}.
$$

一个状态可以携带：

- 当前或末端原子；
- 输入或输出接缝；
- 原生组成状态；
- 守卫是否接受；
- 指定后缀的回复或拒绝。

只有在这些字段的来源、更新和取值域已声明时，才可把它们放入 Arena.State。

### 3.2 接续读出

原生 continuation contract 必须至少给出：

1. 合法历史的判定；
2. 接缝更新；
3. 每个允许输入的守卫判定；
4. 接受回复和拒绝回复的总输出类型；
5. 指定后缀的目标任务。

守卫拒绝是回复值的一部分，不得把错误质量从状态空间中静默删除。

### 3.3 单样本与来源律

一个已取得样本可以确定该样本的原子或回复，但不能单独确定未知来源律的 \(\Delta\)。经验频率和经验 \(\widehat{\Delta}\) 只描述已取得档案；它们只有在另行声明独立同分布抽样合同后才可作为统计估计。

局部五模式律也不自动确定多窗联合历史律。跨窗任务必须显式声明联合来源、共享接缝或足以恢复目标的跨窗坐标。

## 4. 审计登记、通用分析入口与 FIB 桥

### 4.1 登记对象

普通证明逃逸登记继续由现有 `Contract.Registration` 承载，保留四槽义务、enrollment、实现桥、来源选择、敏感性及现有判词。分析合同由目标源码所有者在对应 Reg 源码中提交，链接确切的 theorem occurrence；它是独立的下游分析，不替代普通登记，也不凭计数结果取得 `declared_validated`。普通登记缺失、无效或未完成时，其原状态照实保留；有效分析合同不使它转绿。

`familyRecord` 遵守实际来源归属：直接 `realization := .source …` 的普通登记必须设 `familyRecord := none`，完整 `DependentFamily.Registration` 证明保留在 `realization`，并携带合法的 enrolled `readout`、`sourceSelection` 与 `continuation := .unknown`。非空 `familyRecord` 仅属于既有有限 catalog / `LegacyPrimitiveRealization` 适配器，并须有其有限实现桥；不得要求所有直接源登记另造有限族记录。这里的 `DependentFamily` 是普通登记的带类型证据接口，其 variation、sensitivity、actual dependence 义务不因分析入口通用化而减弱，也不转作所有分析合同的资格门槛。

任意定理种类，包括依赖参数、无限状态、常量读出或零信息增益的情形，均可由作者提交分析合同。只有忠实来源对应决定合同能否绑定该 occurrence；定理名字、与 `native_execution` 相同的命题类型、自然语言 FIB 标签和已证明结论的真假均不能代替对应证据。可表示不等于每个请求的读数均可取得，更不等于每个定理都有 Fibonacci 解释。

### 4.2 作者分析合同的来源对应义务

以下是通用接口及客户端必须满足的规范义务，不是一个已编译的通用桥定理：

1. **原陈述**：绑定编译器实际导出的来源声明及其完整原陈述，保留 universe 参数、完整依赖 telescope、binder 顺序和依赖、隐式参数、typeclass instance 与 proof context。坐标选择、逆映射和完整重构必须回到该原陈述；不得只保留一个投影、任意等价真命题或固定原生命题的替身。
2. **实际实现**：作者给出有类型的参数族、状态族、实际读出及其输出族、选定任务和层。来源选择与等价或传输桥须对应原陈述的实际对象和操作，所有字段依赖闭合于同一个来源及同一组参数。名称、字符串身份和相同边缘值不证明共同实现。
3. **特化范围**：实例化参数、固定初态、限制历史长度或选取参数纤维必须显式给出代入及原陈述到该实例的对应，保留全部适用前提。单纤维结论只关于该纤维；若声称全族，须在完整 telescope 下提供逐参数证据。不得以有限实例替代原定理的全称量词。
4. **读出、任务和层**：实际读出到声明 kernel 的对应、任务的完整输出域及初层和后继层的来源必须明确。涉及 continuation 时须保持相同实际状态、允许输入、方向、更新和总回复，包括拒绝；涉及层链时须证明其弱细化。正的 unique capture 或严格细化是另需见证的结论，不是合同存在的条件。
5. **可选取得**：有限呈现、可执行表、概率律、pushforward 和 FIB 语义只在请求相应读数时按 §§8–9 补证。未知来源律不阻止定性 kernel 分析或已有完整有限域上的无权计数；未提供有限呈现不阻止类型化来源合同。`continuation unknown` 不证明不可判定，也不补足任何缺失桥。
6. **编译证据**：凡声称对应已验证，必须有该客户端的 Lean 证明项、accepted axiom closure 与当前 compiler/source binding evidence。普通四槽登记按其原合同独立判定。接口声明、散文约定或成功解码本身均不是客户端已验证。

FIB 适配器另须证明其来源、原子、读者和指定任务满足 §§2–3、7 的实际对应；单窗坐标不得冒充多窗联合律。信息增益为零时报告零，有关证据未取得时报告相应缺口，不把两者混作正的 unique capture。

### 4.3 escape witness 与 unique capture 的关系

证明逃逸见证要求新命题不能由既有冻结前置经实例化、投影或规范化直接得到，并且必须位于结论的活推导路径上。

信息层的 unique capture 则要求存在 \(u\ne v\)，使得：

$$
\text{所有其他读出在 }u,v\text{ 上相同},\qquad
\text{当前读出在 }u,v\text{ 上不同}.
$$

前者是证明内容义务，后者是状态核严格细化义务。实现桥和来源桥必须把 unique capture 连接到所登记的实际状态和读出，才能作为其定量附加读数；这不要求先有正的证明逃逸见证，也不认证该见证。

## 5. 信息逃逸与分层编码

### 5.1 联合代码与残余纤维

本节的 kernel、相等和分离关系可用于通用合同的任意实际状态纤维；不要求状态有限或已取得概率律。以下以 \(H_L\) 记该选定状态域，FIB 应用中才取窗口历史。读出可有不同的依赖输出类型，在同一参数纤维内比较。对选定读出族 \(S\)，定义联合代码

$$
C_S(h)=(c_i(h))_{i\in S}.
$$

其不可区分关系为

$$
K_S(h_1,h_2)\iff C_S(h_1)=C_S(h_2).
$$

去除对角线后的残余为

$$
E_S=K_S\setminus\Delta_{H_L}.
$$

有限非退化 arena 的精确逃逸率为

$$
\varepsilon(S)=
\frac{|E_S|}{|H_L|(|H_L|-1)}.
$$

\(\varepsilon(S)=0\) 等价于联合代码在该 arena 上单射；\(\varepsilon(S)>0\) 表示仍有不同历史共享同一代码。

### 5.2 留一增益

对目录成员 \(i\)，令 \(S^{-i}=S\setminus\{i\}\)，定义

$$
U_i=E_{S^{-i}}\setminus E_S,\qquad
\delta_i=\frac{|U_i|}{|H_L|(|H_L|-1)}.
$$

在非退化有限 arena 中：

$$
\varepsilon(S^{-i})-\varepsilon(S)=\delta_i.
$$

\(\delta_i>0\) 表示该成员捕获了至少一对其他读出不能捕获的状态；\(\delta_i=0\) 表示当前目录中没有独有捕获对，不等于证明内容必然为空。

### 5.3 分层捕获谱

给定允许相邻核相等的弱细化 kernel 链

$$
K_0\supseteq K_1\supseteq\cdots\supseteq K_m,
$$

初核 \(K_0\) 可以是合同允许的任意 kernel，不要求为全关系。令

$$
D_{H_L}=(H_L\times H_L)\setminus\Delta_{H_L}.
$$

初层及后继第 \(j\) 层首次消除的有序非对角状态对集合分别为

$$
L_0=D_{H_L}\setminus K_0,\qquad
L_j=D_{H_L}\cap(K_{j-1}\setminus K_j)
\quad(1\le j\le m).
$$

有限 arena 的分层捕获数谱包含初层与全部后继层：

$$
\operatorname{Cap}(j)=|L_j|\quad(0\le j\le m).
$$

在有限非退化 arena 中，相应精确率谱为

$$
\operatorname{CapRate}(j)=
\frac{|L_j|}{|H_L|(|H_L|-1)}
\quad(0\le j\le m).
$$

若 \(K_0=H_L\times H_L\)，则 \(L_0=\varnothing\)、\(\operatorname{Cap}(0)=0\)，且在有限非退化 arena 中 \(\operatorname{CapRate}(0)=0\)。相邻核相等时，该后继层作为 collapsed layer 保留在链和谱中，\(L_j=\varnothing\)、\(\operatorname{Cap}(j)=0\)，且在有限非退化 arena 中 \(\operatorname{CapRate}(j)=0\)。原生 guard 读出由此前读出决定时也属此情形；只有相邻核严格包含时，该后继层捕获数才为正。

最终未解析对集合为

$$
R_m=D_{H_L}\cap K_m=K_m\setminus\Delta_{H_L}.
$$

\(L_0,\ldots,L_m\) 与 \(R_m\) 两两不交并分割整个 \(D_{H_L}\)。因此有限 arena 中，令 \(N=|H_L|\)，有

$$
\sum_{j=0}^{m}\operatorname{Cap}(j)+|R_m|=N(N-1).
$$

在有限非退化 arena 中，最终未解析率及精确率守恒为

$$
\operatorname{UnresolvedRate}=\frac{|R_m|}{N(N-1)},\qquad
\sum_{j=0}^{m}\operatorname{CapRate}(j)
+\operatorname{UnresolvedRate}=1.
$$

最终未解析对数及其适用时的率单列，不混入捕获谱。退化或无界 arena 的上述精确率不适用，遵守 §8.1 的有限性边界。

对每个状态对，可以记录其首次被分开的层号；这就是变长分层码的地址。若一个状态纤维大小为 \(q\)，且另有均匀编码合同，则 \(\log_2 q\) 可以作为剩余地址预算；该预算是派生分析量，不是本规范的准入分数。

### 5.4 Kernel lattice 与几何层

对已给定的有限读出 catalog，不同读出子集若产生相同的关系外延，只计作同一个 generated kernel 节点。满足既有有限 catalog 接口时，节点按关系包含形成有限闭包格；严格生成转换形成 DAG，Hasse 图中的 chain 表示嵌套细化，diamond 表示不可比的区分路线。通用登记资格不自动取得有限 catalog、可判定外延比较或该格的可执行呈现。

FIB 金字塔的几何层 \((X,Y,Z)\)、概率纤维层 \(\kappa/\Delta\)、原生接续层和 kernel lattice 层是不同偏序。不得把几何维数、kernel 深度和取得成本当作同一个“维度”。

## 6. 续接任务的定量残差

### 6.1 目标响应残差

对单窗目标 \(f\)，宏观关联残差由

$$
R_f(p,p^\ast)=\frac{J_f\Delta}{r}
$$

给出。它只在指定概率律、补全规则和 \(r>0\) 的合同下成立。

### 6.2 原生守卫残差

若任务明确规定高到低原生读者、奇偶记录条件 \(A\)、继续输入和拒绝回复，则可定义

$$
R_{\mathrm{guard}}
=P_p(\bot\mid A)-P_{p^\ast}(\bot\mid A).
$$

在固定的金字塔续接合同中，若 \(r>0\) 且条件事件 \(A\) 的质量为 \(Y+Z>0\)，则

$$
R_{\mathrm{guard}}=\frac{\Delta}{r(Y+Z)}.
$$

若 \(Y+Z=0\)，事件 \(A\) 为零质量，条件回复律及其残差不适用，不计算该条件分式。若 \(r=0\)，按 §2.4 直接使用唯一顶点：\(p=p^\ast\)、\(Y+Z=1\)，以该顶点的原生回复律得到零残差，不作除以 \(r\) 的运算。

这不是任意评分函数，而是该具体 continuation 任务对隐藏关联坐标的响应。更换读向、初态、后缀或条件事件时，必须重新证明响应式；不得搬用原式。

### 6.3 局部核与原生核的区分

底面行列式 \(\Delta\) 和原生接缝转移核的行列式属于不同关系：前者描述固定中位条件后的端点联合，后者描述接缝输入到输出的路径核。一个为零不推出另一个为零。任何合并指标必须先声明二者的共同状态、方向和归一化合同。

## 7. 两层桥接结构

固定同一实际来源在 \(H_L\) 上已声明的概率律 \(\mu\in\operatorname{Law}(H_L)\)。令 \(c:H_L\to O\) 为原子、接缝和回复的联合状态读出，\(\pi_{\mathrm{atom}}:O\to\Sigma\) 为原子分量投影，并令 \(a=\pi_{\mathrm{atom}}\circ c\)。状态观察保持为状态映射：

$$
H_L
\xrightarrow{c}
O
\xrightarrow{\pi_{\mathrm{atom}}}
\Sigma.
$$

对应的概率律推前从来源律空间出发：

$$
\operatorname{Law}(H_L)
\xrightarrow{c_*}
\operatorname{Law}(O)
\xrightarrow{(\pi_{\mathrm{atom}})_*}
\operatorname{Law}(\Sigma)
\xrightarrow{\text{pyramid projection}}
\mathcal P.
$$

其中 \(p=a_*\mu=(\pi_{\mathrm{atom}})_*(c_*\mu)\)，且 \(p_s=\mu(\{h\in H_L:a(h)=s\})\)。单个 \(h\) 或 \(c(h)\) 不识别未知来源律 \(\mu\) 或 \(p\)；档案经验律的推前只给出经验五模式律，不认证真实来源律。

微观逃逸分析作用于 \(H_L\) 或其明确的有限商；宏观纤维分析作用于 \(\operatorname{Law}(\Sigma)\)。推前会丢失区别，因此宏观相等不能反推微观历史相等。

单窗推前律 \(p\) 也不能恢复来源 \(\mu\) 的多窗联合关系；跨窗任务仍须遵守 §§3.3、8.3 的联合来源合同。

实现不得把 \(\Delta\) 偷塞进单个微观 readout 来绕过这一点。允许的做法有两种：

1. 在微观层登记足够的原子事件读出，再从联合经验律或声明的来源律推导 \(\Delta\)；
2. 明确建立一个以有限概率律为状态的宏观 arena，在该 arena 上把 \(\Delta\) 作为普通 readout。

两种做法必须分别登记其状态类型、来源、有限性和取得条件。

## 8. 有限性、统计和无限边界

### 8.1 精确率的适用域

精确有序 pair 率只适用于已完整呈现的有限非退化状态 arena，分母为 \(N(N-1)\)，其中 \(N\) 是声明的实际状态域的大小。\(N=0\) 或 \(N=1\) 时仍可给出经验证的计数，率不适用；不得把程序中除零的约定当作率结论。无限或未封顶历史可以使用严格 kernel 包含、残余纤维或定性分离结论，但不得伪造有限分母或有限逃逸率。

取得精确有限分析须满足以下证明义务：

1. **完整域**：提供实际状态的完整、无重复枚举，证明每个枚举项合法、每个实际状态都被枚举且恰出现一次；或提供与该状态域双射的完整有限呈现及其双向逆证明。`Fintype` 的存在不等于已取得可消费枚举。样本档案、可达状态的未证子集或概率支持不能代替完整域，零质量状态不得删除。
2. **表反射**：有限表的行必须经上述对应绑定实际状态。对每个选定读出以及每对行，表代码相等当且仅当实际读出相等（或声明的实际 kernel 关系成立），不得只给单向蕴含、抽查或一张同大小的表。若报告输出值，还须证明其解码等于该实际读出，而不只证明碰撞关系相同。读出索引、留一目录和层顺序也须与选定目录完整对应。
3. **任务与层**：任务值或其有限编码须反射同一实际状态上的完整任务输出；所有合法输入与拒绝回复保留。初核和每一后继核须反射该来源上的指定读出组合，并证明相邻弱细化。保留初层和 collapsed layer，最后未解析对单列，不因零增益省略层。
4. **参数与取商**：写明枚举的是完整来源、一个参数纤维、显式限制的子类型还是有限商。限制须有成员谓词和范围对应；商须有实际商映射，并证明所用读出、任务和层在等价类上良定义。对商的有限呈现必须完整且无重复，但其计数只关于商类；对限制域的计数只关于该域。没有额外的纤维大小或传输证明，不得将二者计数当作原来源计数，也不得跨不同参数纤维拼接状态对。
5. **律依赖读数**：仅在读数依赖概率律时要求来源律、归一化、相应 pushforward 及事件/任务对应；条件律另需条件事件质量严格为正。微观无权 pair 计数和结构 kernel 不要求概率律。实数律的数学存在不保证可执行的精确数值取得；有理质量或其他表示须保留其精确表示和证据范围。

上述义务按客户端和读数取得。通用入口不自动提供这些证明，有限角色数也不推出有限参数、状态或输出。

### 8.2 经验数据边界

有限档案产生经验频率、经验纤维和经验 \(\widehat{\Delta}\)。这些量必须与真实来源律、统计估计、形式证明分栏记录。没有独立同分布、抽样或联合实现合同时，不得把经验率报告为真实律的认证。

### 8.3 多窗边界

单窗 \((X,Y,Z,\Delta)\) 的完整恢复不等于多窗联合历史恢复。多窗任务需声明跨窗联合律、共享接缝或足以恢复指定 continuation 的混合坐标。若跨窗关系保持未知，必须把相应 residual 标为 open 或 continuation unknown。

## 9. 分析输出合同

每个分析请求按读数输出来源、适用范围、所用证据和未取得原因。下表的结构字段适用于通用合同，计数和率以 §8.1 为条件，atom、seam、pyramid 及原生残差仅在相应 FIB 适配器有证据时取值；完整的原生有限分析保留全部字段，不将非 FIB 合同填成五模式数据：

| 字段 | 含义 |
|---|---|
| arena | 实际参数/状态族及所选纤维、限制或商；有限呈现及其证明边界（若已取得） |
| source_contract | 原定理 occurrence、完整来源对应、显式特化，以及读数所需的合法性、抽样或联合实现合同 |
| atom_readout | 五模式原子读出或其等价编码 |
| seam_readout | 接缝、方向和原生状态读出 |
| pyramid_coordinates | \((X,Y,Z)\) 及其定义域 |
| association_coordinate | \(\kappa\) 或 \(\Delta\)，以及取得方式 |
| continuation_target | 作者选定的实际任务；原生应用保留后缀、守卫、回复和拒绝 |
| kernel | primitive bundle 诱导的不可区分关系 |
| escape_pairs | 残余有序非对角状态对 |
| escape_rate | 完整有限且 \(N>1\) 的 arena 上的精确有序 pair 率 |
| unique_capture | 留一独有捕获对和增益 |
| layered_spectrum | 初层 \(L_0\) 与全部后继层 \(L_j\)（\(1\le j\le m\)）的首次捕获数及适用时的精确率，单列最终未解析对数与适用时的未解析率（§5.3） |
| residuals | \(w\)、\(J_f\)、\(R_f\)、\(R_{\mathrm{guard}}\) 等条件量 |
| disposition | 对应证据原有的合法状态及其范围；普通登记状态独立保留，不由分析重新裁决 |

报告不得用一个未经定义的 score 替换这些字段，也不得用报告字段反向制造 Lean 证明。

每项读数区分以下情况，并附具体对象、缺口或不适用条件；这些是分析取得说明，不是新增审计/准入判词：

- **unknown**：该量对选定来源有意义，但其值或所需的来源律尚未知，例如原生来源律 absent 时的 \(\Delta\)。未知不等于零，也不等于已证不可取得。
- **unavailable**：该请求的合同、绑定证据、完整有限呈现或受支持的取得方式缺失、无效或无法解码。指出缺的是哪一项，不否定定理的入口资格，不编造替代数值；不能由解码失败推断其数学值未知或不存在。
- **not-applicable**：已声明的范围不满足该读数的定义条件，例如 \(N\le1\) 或无限域的有限 pair 率、零质量事件的条件律，以及未声明 FIB 语义的普通结构合同的金字塔字段。该结论只涉及这项读数。

同一合同可以同时有可用结构读数、unavailable 有限表和 unknown 来源律。普通登记仍使用既有四个 `DTR-*` Observe 判词；上述说明不扩展状态集合，分析成功也不改变普通登记失败或缺失的事实。

### 9.1 编译取得与声明链接

正常 Inspector 编译报告中的独立 `fib_analysis` 下游分区承载来源所有者 Reg
分析合同的取得数据。通用接口须接受任意定理种类的忠实合同，并将原声明绑定与
可选有限取得分开；`NullReplyFiber.native_execution` 的名称或命题类型均不得定义
核心入口域。没有合同的声明仍可被请求，并得到具名的 missing-contract unavailable
说明。该分区不参与四槽登记、proof escape、seal、冻结或准入状态判定。

编译取得须检查 §4.2 的原 occurrence、rigid universes、完整 telescope、特化映射
及同源依赖；不是只删除一个类型检查而接受任意表。作者可以提交非 FIB 有限合同，
也可以提交依赖/非有限合同而不提供有限数据。请求数值时按 §8.1 核对其实际域的
完整呈现、读出/kernel 表反射、选定任务与层；缺少证据仅限制相应读数。

initialized 单窗 Window 是一个有界原生适配器：它使用全部五个 Window 状态、
初始 seam=false、composition=(0,0) 和高到低读者，再对同一已达状态续接 high。
`NativeBridge.reader_eq` 与 `reply_eq` 承担所有者读者、实际
`rawTransition (rawMachine 0).start` 与同状态高位后缀总回复的对应。该适配器还须
显式保留原定理全称参数到 initialized 单窗实例的映射；这些等式不为任意其他
原定理自动提供来源对应。原子、接缝、守卫和含拒绝的回复由此实际来源导出。

该原生适配器的取得合同可承载精确归一化的声明有理质量、有限原子档案或 absent
来源律。声明质量只认证数学归一化；档案只产生经验推前律；两者都不认证物理真律
或 IID。absent 来源律仍允许完整五状态 arena 的微观计数，宏观坐标与关联残差保持
unknown。零质量原子仍在完整 arena 中，原生分母为 \(5(5-1)=20\)，不是支持大小。

编译器读取当前 olean 的类型、受支持的数据构造子、常量引用及其私有传递依赖，
不得任意执行被审计 Expr 的函数体。Lean 证明、accepted axiom closure 和当前绑定
共同支撑来源对应；可信下游只消费经反射验证的数据，复用通用结构/计数/层数学。
原生有限分析器沿已证明的 Window 对应取得其 FIB 字段。无法安全取得的数据保留
具名 unavailable 原因，不通过求值任意作者程序补齐。源码字符串只提供身份，
不能替代对应证明、有限性或未知来源律。

### 9.2 增量生成与下游消费

Lake 现有 report facet、compiler export/transitive traces、模块材料包和 custody
控制生产及失效，不增加第二份调度器或缓存。每个分析合同的取得数据与实际
目标的完整类型/universes、来源、特化、读者、任务、层、有限反射/律证据及其私有
传递常量闭包共同决定其数据身份；所依赖的 compiler/source/contract 输入变化必须
使相应数据失效。不得只跟踪原生适配器的名称或公开引用。重建模块时，
从原模块材料包复用输入身份与完整取得描述均相同的声明读数；新增、删除、合同
资格变化以及真实依赖变化更新相应成员。未改变的声明读数保留原字节内容，
未失效的模块沿原 facet 保留材料包字节及写入时点。

程序重建是独立必需义务，失败传递；程序字节、HEAD 与完整允许来源目录不进入
读数复用键。汇总与 provenance 随实际成员和材料变化保持一致。完整重生用于首次
取得、显式迁移或有界等价比较，日常增量不得以全量回退代替依赖失效。

`make -C tools auric-fib-report` 先经过正常 `make lean-report`，再从完成的报告与
材料、来源 sidecar 消费 FIB 数据；下游不得把该投影重新作为证明证书。
相同 qualified 输入上的完整与增量消费结果必须一致。

通用入口的工程验收须有不同定理种类的实际编译客户端：原生适配器、真正非原生
有限来源，以及依赖参数/非有限来源。必须通过生产报告及下游消费者验证有效、
拒绝和缺失合同、错误来源/表/特化的拒绝对应、各项取得边界，以及依赖变化、
未变兄弟读数保留和完整/增量等价。入口规范和既有原生通过用例不替代这些证据。

## 10. 形式化接入顺序

通用接口及来源对应义务先于最终工程集成明确。§§10.1–10.3 是 FIB 适配器的数学
顺序，不是任意定理获准提交分析合同的前置；任意定理接入不产生一个“所有定理
都是 Fibonacci”的通用定理。工程必须分别取得客户端对应证明与生产链验证。

### 10.1 单窗有限切片

先固定五模式、有限来源律或有限模式样本，形式化合法性、\((X,Y,Z)\)、\(\kappa\)、\(\Delta\)、纤维宽度和目标响应。该切片不宣称无限树、物理实现或任意历史恢复。

### 10.2 微观审计 arena

在固定长度 \(L=1\) 或其他明确有限长度上，加入 atom、seam、guard、reply primitive，并证明其 realization 与原生 continuation 相符。将这些 primitive 接入现有 catalog、generated kernel 和 layered capture。

### 10.3 宏观—微观桥

证明来源到概率律的 pushforward、原子事件到坐标的对应，以及指定 continuation 目标在两层之间的响应桥。若桥只对某个受限来源族成立，登记中必须保留该来源族，不得泛化到整个合法域。

### 10.4 双窗和更长历史

只有在单窗桥和微观有限 arena 已闭合后，才加入共享接缝、跨窗混合坐标和更长历史。每增加一个历史层，都重新声明状态域、联合律和有限性；不得从单窗指标自动外推多窗结论。

### 10.5 数学复用与接口证据边界

通用结构层复用 `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena`
与 `StructuralCatalog` 的任意状态/kernel 接口；依赖状态与输出族的参数组织参照
`D5/S3/ConceptDynamics/InformationEscape/DependentFamily`。其中普通登记的
`Registration` 还要求 variation、sensitivity 与 observational dependence，不能把
该完整记录直接作为零增益分析的必需入口。其 `Arena.Law` 是 realization 上的命题，
不是本规范中可选取得的来源概率律，两者不得混同。

有限取得复用 `InformationEscapeCounting/Fused` 的 `Arena.StateEnumeration`
（`nodup`、`complete`）以及 `FusedCorrectness` 的
`fusedFull_eq_escapeNumerator`、`fusedUnique_eq_uniqueCaptureCount`、
`fusedWithout_eq_escapeNumerator_without`；kernel 外延与层复用
`InformationEscapeHierarchy/GeneratedKernel`、`KernelChain` 和 `LayeredCapture`
的既有声明，包括 `layeredCapture_partition`。这些结果的原有接口假设保持不变。
它们不自动给出新客户端的有限表反射、源码重构或任务对应。

原生应用继续使用 `NullReplyFiber.native_execution` 的实际读者证明及其 owning
Blueprint 应用说明；来源推前复用 `Entropy/Forgetting/PushforwardComposition`，
单窗与联合历史的边界保留 `NativeContinuation/JointLaw` 的实际来源范围。
本规范的通用入口与可选取得要求不需要新增通用数学声明，不以 bind-only 包装
充作新成果。新接口、任意定理客户端、有限反射及编译取得的证明义务仍须逐项
实现并核验；在此之前不得称其已编译、已实现或工程通过。若具体客户端暴露既有
结果不能覆盖的数学缺口，先报告该缺口及范围，再进入后续工程，不改判官掩盖。

## 11. 不变量与禁止事项

必须保持以下不变量：

1. 加入读出只能细化或保持 kernel，不能增加残余逃逸；有限分析保留保持 kernel 的 collapsed layer 及其零捕获数；
2. 删去成员的逃逸率增量等于其 unique-capture 率；
3. FIB 粗坐标相同不推出完整概率律相同；
4. \(\Delta\) 的取值、符号和零点只在声明的来源律与边界条件下解释；
5. 局部规律、原生接续规律和已取得档案分开记录；
6. 证明登记、信息增益和成本比较不互相冒充；
7. 未形式化的桥接结论标为 open 或 deferred，不以理论卷或经验报告充当 kernel 真值。

禁止：

- 用一个样本声称恢复未知 \(\Delta\)；
- 用两个三角边缘的相容提升冒充唯一联合律；
- 用局部 \(\Delta\) 冒充跨窗联合关系；
- 用原生核行列式替代底面关联行列式；
- 用 \(\log_2\) 纤维大小冒充已完成的编码实现；
- 用正的信息增益替代四槽证明逃逸登记；
- 为了得到正增益而修改判官、减弱状态域、删去拒绝回复或缩小目标任务；
- 把理论文档中的公式直接报告为已冻结 Lean 结论。

## 12. 术语对应

| 本规范术语 | 信息逃逸系统对应 | FIB ATOM 对应 |
|---|---|---|
| 状态 | Arena.State | 窗口或有限历史 |
| 读出 | primitive bundle / concept readout | 原子、接缝、守卫、回复 |
| 核 | indistinguishability kernel | 相同 FIB 观察的状态对 |
| 残余 | escape pairs / unresolved pairs | 同坐标或同回复的不同来源 |
| 唯一捕获 | unique capture | 某个新坐标切开的来源对 |
| 层 | kernel chain / layered capture | 原子—金字塔—关联—续接的细化层 |
| 关联残差 | 宏观 residual analysis | \(\kappa\) 或 \(\Delta\) |
| 续接残差 | continuation task residual | 守卫拒绝或后续回复差 |

## 13. 规范来源与接口

本规范消费下列现有材料，不替换其权威范围：

- [单次编译内生信息逃逸规范](lean_single_compile_intrinsic_information_escape_theory_and_spec.md)：有限 arena、primitive kernel、残余逃逸、精确率、留一增益和 kernel lattice；
- [AURIC FIB ATOM 基础公式与关系](../theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)：五模式、金字塔投影、关联坐标、目标响应和取得边界；
- [AURIC FIB ATOM 关联纤维与原生接续](../theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)：粗坐标纤维、纤维宽度和原生历史边界；
- [AURIC FIB ATOM 行列式与原生守卫接续](../theory/AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md)：\(\Delta\)、条件补全和指定继续任务的响应边界。

当本规范与 Lean 声明、证明项或其 axiom closure 不一致时，以 Lean kernel 验证的内容为准；当本规范与既有审计或准入契约冲突时，以既有权威规范为准。本规范只增加组合建模接口，不降低任何既有验证、登记、冻结或有限性要求。

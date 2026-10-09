# AURIC FIB ATOM 逃逸审计与分层编码规范

**文档状态：** 规范性草案（Normative Draft）
**版本：** 0.1 — Typed-FIB / Two-Level-Arena / Kernel-Residual / Layered-Code / No-Scalar-Score
**适用范围：** AURIC FIB ATOM 金字塔、原生接续任务与内生信息逃逸系统的组合建模、形式化和分析。

本规范定义一个把 FIB ATOM 的有限原子关系接入逃逸审计系统的类型化接口。规范只规定对象、量、证明义务和边界；它不修改现有判官、报告解析器、Lean 编译器或准入状态。

## 摘要

组合系统由两层组成：

1. **微观状态层**：窗口、历史、接缝、守卫和回复构成有限或有界的 Arena.State。逃逸审计在这一层比较读出，形成不可区分核、残余逃逸和分层捕获。
2. **宏观律层**：五模式概率律形成 AURIC FIB ATOM 金字塔。三均值坐标描述粗观察，关联坐标描述被粗观察遗忘的联合关系，原生续接律描述该遗忘怎样影响后续任务。

两层通过实际来源到概率律的推前映射连接。微观读出产生代码碰撞；宏观坐标描述这些碰撞所属的概率律纤维。两层的量不得混作一个无类型标量。

本规范的基本产物是一个分层编码向量，而不是人工评分：

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

**信息逃逸分析**回答：一组读出还让多少不同状态保持不可区分，以及增加一个读出后消除了多少碰撞。它使用状态 arena、联合不可区分 kernel 和精确有限计数。

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

## 4. 审计登记与 FIB 桥

### 4.1 登记对象

每个被登记的 D5 theorem occurrence 由现有 Contract.Registration 合同承载。登记必须把目标声明、实际 realization、读出模板、来源选择、族记录和 continuation 连接到同一语义对象。

FIB 接入不得只写一个自然语言标签。readout 必须具有可检查的类型；sourceSelection 必须确定实际来源族；familyRecord 必须记录目标所需的完整观察；continuation 必须说明观察怎样进入目标回复或保留未知残差。

### 4.2 证明桥的最小义务

一个 FIB 逃逸登记要成为 declared_validated，至少须证明：

1. **实现桥**：登记的 realization 与 FIB 原子、历史或概率律对象定义相符；
2. **读出桥**：每个 enrolled primitive 的 kernel 与声明的状态等价关系相符；
3. **来源桥**：来源选择只包含合同允许的合法窗口或历史；
4. **续接桥**：读出变化确实位于指定 continuation 任务的活路径上；
5. **敏感性或残差**：存在具体状态对、来源律差异或显式未知残差，且其量词与目标一致；
6. **联合性边界**：单窗坐标不得冒充多窗联合律，局部统计不得冒充完整历史档案；
7. **形式证据**：桥接声明、证明项和 axiom closure 通过当前 Lean kernel 检查。

如果只证明了数学内容而没有证明其读出改变当前 kernel，则登记可以保留为信息增益为零或未结算的分析对象，但不得把它标成正的 unique capture。

### 4.3 escape witness 与 unique capture 的关系

证明逃逸见证要求新命题不能由既有冻结前置经实例化、投影或规范化直接得到，并且必须位于结论的活推导路径上。

信息层的 unique capture 则要求存在 \(u\ne v\)，使得：

$$
\text{所有其他读出在 }u,v\text{ 上相同},\qquad
\text{当前读出在 }u,v\text{ 上不同}.
$$

前者是证明内容义务，后者是状态核严格细化义务。只有在实现桥和来源桥把二者连接起来后，unique capture 才能作为该登记的定量附加读数。

## 5. 信息逃逸与分层编码

### 5.1 联合代码与残余纤维

对微观状态类型 \(H_L\) 和选定读出族 \(S\)，定义联合代码

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

第 \(j\) 层首次消除的有序状态对集合为

$$
L_j=K_{j-1}\setminus K_j.
$$

分层捕获谱为

$$
\operatorname{Cap}(j)=|L_j|,\qquad
\operatorname{CapRate}(j)=
\frac{|L_j|}{|H_L|(|H_L|-1)}.
$$

相邻核相等时，该层作为 collapsed layer 保留在链和谱中，\(L_j=\varnothing\)、\(\operatorname{Cap}(j)=0\)，且在有限非退化 arena 中 \(\operatorname{CapRate}(j)=0\)。原生 guard 读出由此前读出决定时也属此情形；只有相邻核严格包含时，该层捕获数才为正。

最终未解析率为

$$
\operatorname{UnresolvedRate}=
\frac{|K_m\setminus\Delta_{H_L}|}{|H_L|(|H_L|-1)}.
$$

对每个状态对，可以记录其首次被分开的层号；这就是变长分层码的地址。若一个状态纤维大小为 \(q\)，且另有均匀编码合同，则 \(\log_2 q\) 可以作为剩余地址预算；该预算是派生分析量，不是本规范的准入分数。

### 5.4 Kernel lattice 与几何层

不同读出子集若产生相同的关系外延，只计作同一个 generated kernel 节点。节点按关系包含形成有限闭包格；严格生成转换形成 DAG，Hasse 图中的 chain 表示嵌套细化，diamond 表示不可比的区分路线。

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

精确有序 pair 率只适用于有限非退化状态 arena。无限或未封顶历史可以使用严格 kernel 包含、残余纤维或定性分离结论，但不得伪造有限分母或有限逃逸率。

### 8.2 经验数据边界

有限档案产生经验频率、经验纤维和经验 \(\widehat{\Delta}\)。这些量必须与真实来源律、统计估计、形式证明分栏记录。没有独立同分布、抽样或联合实现合同时，不得把经验率报告为真实律的认证。

### 8.3 多窗边界

单窗 \((X,Y,Z,\Delta)\) 的完整恢复不等于多窗联合历史恢复。多窗任务需声明跨窗联合律、共享接缝或足以恢复指定 continuation 的混合坐标。若跨窗关系保持未知，必须把相应 residual 标为 open 或 continuation unknown。

## 9. 分析输出合同

一个完成的有限分析至少输出以下带来源的字段：

| 字段 | 含义 |
|---|---|
| arena | 微观或宏观状态类型及有限性证明边界 |
| source_contract | 来源、合法性、抽样或联合实现合同 |
| atom_readout | 五模式原子读出或其等价编码 |
| seam_readout | 接缝、方向和原生状态读出 |
| pyramid_coordinates | \((X,Y,Z)\) 及其定义域 |
| association_coordinate | \(\kappa\) 或 \(\Delta\)，以及取得方式 |
| continuation_target | 后缀、守卫、回复和拒绝的具体任务 |
| kernel | primitive bundle 诱导的不可区分关系 |
| escape_pairs | 残余有序非对角状态对 |
| escape_rate | 有限 arena 上的精确率 |
| unique_capture | 留一独有捕获对和增益 |
| layered_spectrum | 各层首次捕获数与未解析率 |
| residuals | \(w\)、\(J_f\)、\(R_f\)、\(R_{\mathrm{guard}}\) 等条件量 |
| disposition | proved、refuted、open、deferred 或其他现有合法状态 |

报告不得用一个未经定义的 score 替换这些字段，也不得用报告字段反向制造 Lean 证明。

## 10. 形式化接入顺序

### 10.1 单窗有限切片

先固定五模式、有限来源律或有限模式样本，形式化合法性、\((X,Y,Z)\)、\(\kappa\)、\(\Delta\)、纤维宽度和目标响应。该切片不宣称无限树、物理实现或任意历史恢复。

### 10.2 微观审计 arena

在固定长度 \(L=1\) 或其他明确有限长度上，加入 atom、seam、guard、reply primitive，并证明其 realization 与原生 continuation 相符。将这些 primitive 接入现有 catalog、generated kernel 和 layered capture。

### 10.3 宏观—微观桥

证明来源到概率律的 pushforward、原子事件到坐标的对应，以及指定 continuation 目标在两层之间的响应桥。若桥只对某个受限来源族成立，登记中必须保留该来源族，不得泛化到整个合法域。

### 10.4 双窗和更长历史

只有在单窗桥和微观有限 arena 已闭合后，才加入共享接缝、跨窗混合坐标和更长历史。每增加一个历史层，都重新声明状态域、联合律和有限性；不得从单窗指标自动外推多窗结论。

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

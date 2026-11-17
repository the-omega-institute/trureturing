# 正交时间场论 OTF-003：概念、存在与关系纤维

> 理论参考输入：本稿为用户提供的研究正文，包含普通数学证明，未作本候选的 Lean/kernel 认证。图示以文内文字和公式呈现。

OTF RESEARCH SERIES / 003 / VERSION 1.0

正交时间场论

概念、存在与关系纤维

稳定读出、相对原子性、跨块相干与内生语义

Concepts, Existence, and Relational Fibres\
Stable Readouts and Context-Relative Atomicity

**本轮核心** 一个概念可以在给定分辨率下成为不可再分的读出单位， 而它的纤维仍包含许多状态与过程。 量子表示进一步区分概念的关系空间、态实际占据的相干， 以及内部协议能够读出的干涉。

$$
X\cong\bigsqcup_{b\in q(X)}q^{-1}(b),
 \qquad
 T_P\operatorname{Gr}(r,d)\cong\operatorname{Hom}_{\mathbb C}(\operatorname{ran}P,\ker P).
$$

$$
\rho=
 \begin{pmatrix}A&C\\ C^\dagger&B\end{pmatrix},
 \qquad
 \mathcal V_P(\rho)=2\left\|C\right\|_1,
 \qquad
 (2p-1)^2+\mathcal V_P(\rho)^2\leq1.
$$

**范围** 本文建立有限语义模型及其一类量子实现，给出定义、定理、证明、反例和 可执行的有限闭包构造。标准集合论、形式概念分析和量子测量理论保留来源； “概念粒子”是明示的操作性术语，不预设自然语言概念都是物理粒子。

2026 年 11 月 8 日 / Asia–Singapore

项目来源固定于默认分支 dev 的 `c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02`。

本稿独立承接 OTF-001、OTF-002；未宣称新的 Lean 构建或实验验证。

## 摘要

“连量子与存在这些概念本身也具有粒子性”可以怎样发展为可证明的理论？ 本文以概念读出、关系纤维和相对于观察代数的原子性为核心。 首先证明，有限观察菜单的不可区分纤维正是可判定 Boolean 代数的原子； 标签的一维记忆编码不蕴涵其所指集合或状态子空间为一维。 读出能够保留一个否定，当且仅当该命题是完整纤维的并。 随后区分对象、词的出现、概念、实际记录和存在见证， 并以有限量词、子空间并及非分配反例限定它们的逻辑联系。 在量子扩展中，秩 $r$ 的锐概念用投影 $P$ 表示， 其可重复测量容许任意块内量子通道；概念稳定并不排除内部生成。 Lüders 分块保留与仅保留标签概率是不同的压缩： 前者丢失跨块矩阵 $C$，后者一般还丢失块内状态。 本文给出正性纤维、最优跨块可见度和 Grassmann 切空间的完整证明， 将 OTF-002 的二维横向关系推广为实维 $2r(d-r)$ 的关系空间。 纯态相对于自身概念可以没有跨块相干，同时具有非零横向涨落； “关系可能性”与“实际振荡”因此必须分开。 有限未来读出闭包与 Heisenberg 效应闭包进一步提供可计算的预测概念。 所有控制、参考和记录都可置于同一有限整体内。 本文不从名称推出存在，不从各向同性推出空无，也不从圆周几何推出任意物理量的量子化。

**关键词：** 概念读出；存在见证；相对原子性；纤维饱和； 形式概念分析；Lüders 通道；Grassmann 流形；操作闭包。

## 目录

- [1　研究命题与完整候选约束](#section-1)
- [2　概念粒子的严格定义：相对观察的原子](#section-2)
- [3　否定、存在量词与见证纪律](#section-3)
- [4　从观察纤维到形式概念](#section-4)
- [5　量子概念：效应、投影与相对原子性](#section-5)
- [6　稳定命名与内部生成可以共存](#section-6)
- [7　两种压缩与跨块关系](#section-7)
- [8　从关系块到可见波纹](#section-8)
- [9　从二维正交面推广到概念的关系流形](#section-9)
- [10　稳定概念的动力学与最小未来精化](#section-10)
- [11　真正充分的预测读出：效应闭包](#section-11)
- [12　观察者、名称与记录的内生实现](#section-12)
- [13　各向同性、连续射线与量子化边界](#section-13)
- [14　一个完整的四状态、四维例子](#section-14)
- [15　理论的可检验内容与下一轮接口](#section-15)
- [A　符号、类型与适用条件](#section-A)
- [B　当前项目来源与核对范围](#section-B)

<a id="section-1"></a>

## 1　研究命题与完整候选约束

本轮保留的直觉是：被命名、被重复辨认的东西，往往表现为一个稳定单位； 而这个单位仍处于可变化的关系中。需要建立的理论是这种稳定性、关系和变化之间的 精确结构。“一切存在都是线”“面积必然在旋转”等语句不能直接充当证明。 本文分别使用**模型定义、数学结论、表示选择、经验桥梁** 四个层次； 数学结论只在已经列明的模型条件下成立。

### 1.1　四种对象与两种同一性

| 对象 | 本文记号与含义 | 不自动等同于 |
|:---|:---|:---|
| 符号的出现 | 记忆载体中的一次 token，如字符串“量子” | 量子系统或该词的所有所指 |
| 概念界面 | 读出 $q:X\to B$，或量子仪器的响应规则 | 唯一向量、空间位置 |
| 概念所指 | 纤维 $q^{-1}(b)$、谓词外延、投影的支撑空间 | 标签自身的记忆编码 |
| 存在断言 | 在指定域、准入条件及模型中要求见证 | 归一化、逻辑自反性、一次命名 |

同一个字符串出现两次，可以是相同类型的两个 token。 不同状态满足 $q(x)=q(y)$，是 *相对于此概念不可区分* ， 不等于 $x=y$。对象语言中的“存在”一词能够被记录， 也不等于元语言中的存在量词已经获得了见证。

### 1.2　候选 AX-003

以下七条定义一类完整的有限候选模型。 A1–A3 是语义与操作核心；A4–A6 是明确附加的量子实现； A7 规定整体内生性及验证范围。可以只使用经典核心， 而不能把量子实现宣称为已经从命名活动推导出来。

#### 结构约束 1.1：A1：有类型的载体与见证

给定非空有限经典配置集 $X$、准入集合 $X_{\rm adm}\subseteq X$、 概念值集、符号载体与记忆载体；这些类型分别标记。 实际锚点 $a\in X_{\rm adm}$ 若被提供，是模型的额外数据。 任何现实指称必须有另行说明的实现关系。

#### 结构约束 1.2：A2：观察菜单与有效值

经典读出为函数 $q_i:X\to B_i$，有效值限制到数学像 $q_i(X)$。 准入值 $q_i(X_{\rm adm})$ 及已发生的记录值另行区分。 联合读出 $q_\Gamma(x)=(q_i(x))_{i\in\Gamma}$ 定义响应等价。 随机读出使用条件分布；概率响应与一次实际采样结果属于不同层次。 概念原子性始终注明其可访问的命题代数。

#### 结构约束 1.3：A3：过程与闭包

允许过程作为模型数据给出，可以是确定映射或 Markov 核。 确定过程只有满足纤维下降条件才有单值的概念层动力学； Markov 过程则要求能下降为标签上的概率核。 需要未来预测时，将明确允许的过程纳入观察闭包， 不把当前不可区分无条件当作永久不可区分。

#### 结构约束 1.4：A4：可选的有限量子表示

采用有限复 Hilbert 空间 $\mathcal H$，密度矩阵、效应 $0\leq E\leq I$， Born 配对 $p(E\mid\rho)=\operatorname{tr}(\rho E)$，以及有限张量积。 锐二元概念用投影 $P=P^\dagger=P^2$ 表示； 一般概念允许多结果 POVM，不要求均为秩一。 经典模型可嵌入对角子代数，这项嵌入本身不强制非零相干。 量子扩展的“有限”指 Hilbert 维数、寄存器数及每个仪器的结果数有限， 不要求全部密度态或全部参数选择构成有限集合； 效应闭包一节另行假定有限基本菜单。$X$ 可以作为经典扇区或基编码。

#### 结构约束 1.5：A5：仪器与记忆

允许仪器由有限 Kraus 算子给出， $\mathcal I_b(\rho)=\sum_j K_{bj}\rho K_{bj}^\dagger$， $\sum_{b,j}K_{bj}^\dagger K_{bj}=I$。 结果 $b$ 可存于内部正交指针。 可重复性只要求复测同一锐概念得到同一标签； 除非另行规定，不把它加强成块内状态完全不变。

#### 结构约束 1.6：A6：相干、参考与时序合同

每项可见度结论注明可访问效应、控制和参考。 相位扫描及跨块效应只在允许的菜单中使用。 动力学生成元 $H$、时钟参数及 $\hbar>0$ 是额外的动力学与标定数据。 一个非零关系空间不单独指定占据态、频率或传播定律。

#### 结构约束 1.7：A7：整体内生与证据边界

系统、符号载体、观察者、控制、参考、记录和有限时钟均为同一整体 $\Omega$ 的组成部分；条件化是对内部记录的描述。 本稿只声称在这些数据上成立的数学结果。 识别某个模型为自然语言认知或基本物理，需要额外的实验实现及比较检验。

这些约束相容：第 14 节给出四状态经典模型和四维量子模型， 第 12 节给出有限内部实现。

<a id="section-2"></a>

## 2　概念粒子的严格定义：相对观察的原子

#### 定义 2.1：概念、纤维与响应商

概念界面是函数 $q:X\to B$。记 $B_{\rm eff}=q(X)$， $F_b=q^{-1}(\{b\})$，并定义

$$
x\sim_q y\quad\Longleftrightarrow\quad q(x)=q(y).
$$

纤维是固定读出以后仍可变化的完整配置集合， 不预设它是线性空间、平面或量子波。

#### 定理 2.2：概念–纤维分解与最小表示

存在规范双射

$$
X\ \cong\ \bigsqcup_{b\in B_{\rm eff}}F_b,
 \qquad x\longmapsto(q(x),x).
$$

响应商 $X/{\sim_q}$ 与 $B_{\rm eff}$ 双射。 若 $g:X\to Z$ 对每个纤维为常数，则存在唯一 $\bar g:B_{\rm eff}\to Z$ 使 $g=\bar gq$。

**证明。**

分解映射的逆为 $(b,x)\mapsto x$，因为 $x\in F_b$ 已经保证 $q(x)=b$。 映射 $[x]\mapsto q(x)$ 良定义、单射且满射。 若 $g$ 在纤维上常数，令 $\bar g(b)=g(x)$，其中 $q(x)=b$； 常数条件保证与代表元无关，满射性保证其定义及唯一性。 反之，任何因子分解显然在每个纤维上常数。

$\square$

这是现有项目的概念–纤维结构在有限集合中的表述 [\[7\]](#ref-repoConcept), [\[8\]](#ref-repoFibre)，不主张优先性上的新发现。 它确切表达“一个确定的名字仍携带尚未展开的关系内容”。 但是仅保存标签并不会保留纤维的全部结构；需要模型同时给出这些纤维。

#### 定义 2.3：可判定命题与概念原子

定义此读出可判定的命题代数

$$
\mathcal B_q=\{q^{-1}(S):S\subseteq B_{\rm eff}\}.
$$

Boolean 代数中的原子是非空元素 $A$，且不存在同一代数中的 $\varnothing\subsetneq D\subsetneq A$。 本文称 $\mathcal B_q$ 的原子为 *相对于 $q$ 的概念粒子* 。 这是操作性术语，不是物理粒子的定义。

#### 定理 2.4：相对原子性

$\mathcal B_q$ 的原子恰为各个非空纤维 $F_b$。 同一个概念粒子可以包含任意多个配置。

**证明。**

每个可判定命题是若干完整纤维的并。 若这样的非空命题包含两个不同纤维，则其中任何一个是它的非空真子命题， 故它不是原子。单个纤维不能被该代数中的命题进一步分开，因此是原子。 取常值映射 $q$ 即可使唯一原子等于任意给定的非空有限 $X$。

$\square$

#### 推论 2.5：分辨率改变粒子边界

若 $q=f\circ r$，则 $\mathcal B_q\subseteq\mathcal B_r$，每个 $q$-原子是若干 $r$-原子的并。两个读出的联合 $(q_1,q_2)$ 是能同时恢复二者的最粗读出。

**证明。**

$q^{-1}(S)=r^{-1}(f^{-1}(S))$，给出代数包含。 联合读出通过坐标投影恢复二者； 若 $q_i=f_i r$，则 $(q_1,q_2)=(f_1,f_2)r$，给出其最小性。

$\square$

#### 命题 2.6：标签的线与所指的维数不同

在 $\ell^2(X)$ 中令

$$
P_b=\sum_{x\in F_b}|x\rangle\langle x|.
$$

则 $P_b$ 两两正交、$\sum_bP_b=I$，且 $\operatorname{rank}P_b=|F_b|$。 同一标签可以在另一个记忆空间中编码成秩一态 $|b\rangle\langle b|$， 但两者通常具有不同的秩。

**证明。**

不同纤维是不交集，且并为 $X$，故投影正交且完备。 $P_b$ 的像由 $|F_b|$ 个正交基向量张成，因而秩为 $|F_b|$。 记忆编码是另一个空间中的基向量，它没有改变这个计数。

$\square$

例如一个文件名可以是单个记录，而所指文件含有许多页。 同样，“量子”作为词的出现可以是一个稳定符号， 其所指类别并不会因此压缩成一条物理空间直线。 线性书写顺序也不限制所描述对象的数学维数： 一个有限字符串可以编码任意给定大小的矩阵及其索引关系。

<a id="section-3"></a>

## 3　否定、存在量词与见证纪律

### 3.1　否定何时穿过概念压缩

#### 定义 3.1：纤维饱和与可见边界

对 $A\subseteq X$，定义

$$
\operatorname{Sat}_q(A)=q^{-1}(q(A)),\qquad
 \partial_q A=q(A)\cap q(X\setminus A).
$$

当 $A=\operatorname{Sat}_q(A)$ 时，称 $A$ 对 $q$ 饱和。 $\partial_qA$ 是同时容纳 $A$ 和非 $A$ 配置的混合标签。

#### 定理 3.2：否定下降的充要条件

设 $q:X\to B$ 满射。以下四项等价：

$$
\begin{aligned}
 &A\in\mathcal B_q;\\
 &A=q^{-1}(q(A));\\
 &q(X\setminus A)=B\setminus q(A);\\
 &\partial_q A=\varnothing.
\end{aligned}
$$

**证明。**

若 $A=q^{-1}(S)$，满射给出 $q(A)=S$，故第一项等价于第二项。 若第二项成立，则每个纤维要么全在 $A$ 中，要么全在其补集中； 满射保证每个 $b$ 对应非空纤维，故第三项成立。 第三项立即给出第四项。 若第四项成立而 $x\in q^{-1}(q(A))\setminus A$， 则某个 $y\in A$ 有 $q(y)=q(x)$，于是 $q(x)\in\partial_q A$，矛盾。 总有 $A\subseteq q^{-1}(q(A))$，因而得到第二项。

$\square$

这里的像–补集等价是项目已存在的定理 `image_complement_iff_saturated`[\[9\]](#ref-repoNeg)。 若 $q$ 不满射，应把右边的宇宙换成 $q(X)$。

#### 反例 3.3：一个词不足以决定内部否定

令 $X=\{a,b\}$，$q(a)=q(b)=c$，$A=\{a\}$。 则 $q(A)=q(X\setminus A)=\{c\}$，而 $q(X)\setminus q(A)=\varnothing$。 所以“不是 $A$”不能只凭这个单一标签判断。 这是信息不足，不是经典逻辑自身矛盾。

### 3.2　有限存在量词与类型区别

#### 定理 3.4：有限量词的 Boolean 语义

给定有限见证集 $W$ 和命题集合 $A_w\subseteq X$。 则

$$
\exists w:\ x\in A_w
 \quad\Longleftrightarrow\quad
 x\in\bigcup_{w\in W}A_w.
$$

若各 $A_w\in\mathcal B_q$，这个存在命题仍在 $\mathcal B_q$， 并且可在标签空间用并集计算。 在对角 Hilbert 编码中，

$$
P_{\exists w A_w}=I-\prod_{w\in W}(I-P_{A_w}).
$$

空见证集给出零命题。

**证明。**

集合并的定义就是存在某个指标使成员关系成立。 $\mathcal B_q$ 对并封闭，且逆像保持并。 对每个基向量 $|x\rangle$，右边乘积的特征值为 $1-\prod_w(1-\chi_{A_w}(x))$，恰是该并集的指示函数。 空乘积为 $I$，故无见证时结果为零。

$\square$

一般不可以把量词值域看成一个未经解释的正交方向。 在一阶逻辑中 $\exists x\,\varphi(x)$ 是相对于解释域及谓词解释的句子； 在上述构造中，$x$ 是仍被保留的背景配置、$w$ 是被量化的见证。 这和“存在”这个字符串在记忆中出现是不同的命题。

#### 定义 3.5：本稿的六项存在数据

对候选对象类型 $Y$、准入条件 $A(y)$、读出 $q$ 和过程 $F$，区分：

1.  可形成：$Y$ 的定义在所用形式系统中合法；

2.  非空：存在某个 $y\in Y$；

3.  可实现：存在 $y$ 使 $A(y)$；

4.  已给锚点：模型提供一个指定的 $a$ 及 $A(a)$；

5.  可显现标签 $b$：存在 $y$ 使 $A(y)$ 且 $q(y)=b$；

6.  持续：给定锚点及过程后，在指定时间域中 $A(F^n a)$ 恒成立。

现实中实现某对象，还要求理论对象到现实装置或对象的实现关系。

#### 命题 3.6：定义、同一性与现实存在不互相代替

上述可形成不蕴涵非空，非空不蕴涵任意给定准入条件可满足； 指定一个候选码 $b\in B$ 也不蕴涵其纤维非空； 对有效标签 $b\in B_{\rm eff}=q(X)$，非空则已由定义保证。 对象的逻辑自反性 $x=x$ 不等于向量的单位归一化。

**证明。**

空集是合法集合，说明第一项；在非空 $Y$ 上令 $A$ 恒假，说明第二项。 取 $q:X\to\{0,1\}$ 恒为 $0$，则候选码 $1$ 合法而不是有效标签，其纤维为空。 最后，零向量满足 $0=0$，但 $\langle0,0\rangle=0$。 任意非零向量 $v$ 可归一为 $v/\left\|v\right\|$，这是尺度约定； 它不提供任何现实实现关系的见证。

$\square$

在有限经典模型中，已证明非空的可判定集合可以枚举并选出元素。 本文不否认这一事实；“有一个解”与“模型已指定哪个锚点” 仍是不同的数据，更不能由前者直接认定某个现实系统已经实现了它。 项目的六层讨论在类型论中还区分命题截断与给定构造项 [\[7\]](#ref-repoConcept), [\[10\]](#ref-repoExist)，不能抹掉其逻辑前提。

#### 推论 3.7：全域肯定与原子性

肯定所有配置的命题是 $X$。 若 $|B_{\rm eff}|\geq2$，它不是 $\mathcal B_q$ 的原子； 若 $|B_{\rm eff}|=1$，则 $\mathcal B_q=\{\varnothing,X\}$， $X$ 是该代数的唯一原子。

**证明。**

有两个以上非空纤维时，每个纤维都是 $X$ 的真子命题。 只含 $\varnothing,X$ 时，定义直接给出原子性。

$\square$

因而“存在也可以被当作一个单位”在极粗的描述层面成立； 它本身没有确定某个特权方向，也没有产生新的物理预测。

<a id="section-4"></a>

## 4　从观察纤维到形式概念

分区式标签不是全部语义结构。一般概念可以有交叠外延， 适合用对象–属性关系来构造。以下是形式概念分析的标准结构 [\[5\]](#ref-ganter)，并明确给出与观察纤维的衔接。

#### 定义 4.1：形式语境与双极

给定对象集 $X$、属性集 $M$、关系 $R\subseteq X\times M$。 对 $A\subseteq X$ 和 $B\subseteq M$，定义

$$
A'=\{m:\forall x\in A,\ xRm\},\qquad
 B'=\{x:\forall m\in B,\ xRm\}.
$$

形式概念是满足 $A'=B$、$B'=A$ 的一对 $(A,B)$， 分别称为外延和内涵。

#### 定理 4.2：关系生成概念闭包

$B\subseteq A'$ 当且仅当 $A\subseteq B'$。 算子 $A\mapsto A''$ 是广延、单调、幂等的闭包。 所有闭合外延按包含构成完备格，其交为集合交， 其并为集合并的双极闭包。

**证明。**

等价式两边都表示 $\forall x\in A\,\forall m\in B,\ xRm$。 取 $B=A'$ 得 $A\subseteq A''$。 单极反转包含，故双极保持包含。 广延性给出 $A'\subseteq A'''$，而 $A\subseteq A''$ 经反向单极给出 $A'''\subseteq A'$； 故 $A'''=A'$，再取单极得到幂等性。 任意闭合外延的交仍闭合：单调性使其闭包包含在每个成员中， 广延性给出反向包含。包含所有给定外延的最小闭合集 正是它们并集的闭包，故有任意交和并。

$\square$

#### 定理 4.3：观察概念桥梁

对观察菜单 $\Gamma$，取属性为所有读出–取值对 $(i,b)$， 并规定 $xR(i,b)$ 当且仅当 $q_i(x)=b$。 则

$$
\{x\}''=\{y:\forall i,\ q_i(y)=q_i(x)\}.
$$

因此观察等价类正是这个特定形式语境中的单点闭包。

**证明。**

对象 $x$ 具有的属性恰为所有 $(i,q_i(x))$。 一个 $y$ 具有全部这些属性，正是每个 $q_i(y)=q_i(x)$。 这就是双极闭包的定义。

$\square$

该桥梁已有项目源码对应 `extentClosure_singleton_eq_jointKernel_class` [\[11\]](#ref-repoFCA)。对于任意属性关系，闭合外延不必组成分区， 更不必是 Hilbert 空间中的正交子空间。 例如三对象 $a,b,c$ 的属性分别为 $\{u\},\{u,v\},\{v\}$， 则“具有 $u$”和“具有 $v$”的外延分别为 $\{a,b\}$ 与 $\{b,c\}$， 它们交叠，却既不相同也不互为否定。

由此可以精确表达：概念由可共同满足的关系闭包形成。 要进一步引入内积、角度或相位，还需要额外的表示选择。

<a id="section-5"></a>

## 5　量子概念：效应、投影与相对原子性

#### 定义 5.1：量子概念的概率响应

在 $\dim_{\mathbb C}\mathcal H=d$ 中，有限结果概念由效应族 $E_b\geq0$、$\sum_bE_b=I$ 给出。 其概率响应为

$$
q_C(\rho)=\bigl(\operatorname{tr}(\rho E_b)\bigr)_b.
$$

这个函数的值是概率分布，不是某次采样得到的标签。 锐二元概念为 $E_1=P$、$E_0=Q=I-P$。 以下讨论非平凡情况 $0<r=\operatorname{rank}P<d$，记 $s=d-r$、 $E=\operatorname{ran}P$、$F=\operatorname{ran}Q$。

以子空间表达实验命题是量子逻辑的标准出发点 [\[3\]](#ref-birkhoff)。命题子空间不必是一维；仪器还需要指定更新规则。 单凭一个自然语言词不能确定它应对应哪个效应。

#### 定理 5.2：确定性是支撑条件

对密度矩阵 $\rho$，

$$
\operatorname{tr}(\rho P)=1
 \quad\Longleftrightarrow\quad
 \operatorname{supp}\rho\subseteq E
 \quad\Longleftrightarrow\quad
 \rho=P\rho P.
$$

当 $r>1$ 时，确定回答“是”的状态不是唯一纯态。

**证明。**

$\operatorname{tr}(\rho Q)=\operatorname{tr}(\rho^{1/2}Q\rho^{1/2}) =\left\|Q\rho^{1/2}\right\|_2^2$。 它为零当且仅当 $\rho^{1/2}$ 的像在 $E$ 中， 这等价于后两项。若 $r>1$，任意两个不同的单位射线 及它们的任意混合都可支撑于 $E$，因此不是唯一状态。

$\square$

#### 定义 5.3：代数中的原子投影

设 $\mathcal A\subseteq\mathcal B(\mathcal H)$ 为含幺元的 $`*`$-子代数。 非零投影 $P\in\mathcal A$ 是原子，当且仅当不存在 $R\in\mathcal A$ 使 $0<R<P$。 是否拥有这项原子性总是相对于所给代数而言。

#### 定理 5.4：标签原子与射线原子

在标签代数

$$
\mathcal A_P=\{aP+bQ:a,b\in\mathbb C\}
$$

中，$P$ 和 $Q$ 都是原子，不论它们的秩是多少。 在完整 $\mathcal B(\mathcal H)$ 中，$P$ 为原子当且仅当 $r=1$。

**证明。**

$aP+bQ$ 是投影当且仅当 $a,b\in\{0,1\}$， 故 $\mathcal A_P$ 的投影只有 $0,P,Q,I$。 若 $r>1$，任选单位 $u\in E$，则 $0<|u\rangle\langle u|<P$ 是完整代数中的真子投影。 若 $r=1$，$E$ 无非零真子空间，因而无这样的子投影。

$\square$

这个定理为“概念粒子”提供了量子版的明确含义。 同一个概念在标签层面是一个单位， 在更丰富的操作层面可以分解为许多状态。 代数还只是已声明的表示；它的每个效应是否实际可测，仍需协议菜单保证。

#### 定理 5.5：子空间的并与非 Boolean 边界

有限投影族的格并满足

$$
\operatorname{ran}\left(\bigvee_jP_j\right)=\operatorname{supp}\left(\sum_jP_j\right).
$$

若它们两两对易，则 $\bigvee_jP_j=I-\prod_j(I-P_j)$。 一般投影格不满足分配律。

**证明。**

$\langle v,\sum_jP_jv\rangle=\sum_j\left\|P_jv\right\|^2$， 故 $\ker\sum_jP_j=\bigcap_j\ker P_j$。 取正交补得到所有像空间的线性张成，即格并。 对易时可同时对角化，每个特征坐标上的并是有限 Boolean 或，得到乘积式。 非分配性取 $\mathbb C^2$ 中 $L_z=\operatorname{span}|0\rangle$、$L_+=\operatorname{span}(|0\rangle+|1\rangle)$、 $L_-=\operatorname{span}(|0\rangle-|1\rangle)$。则

$$
L_z\cap(L_+\vee L_-)=L_z,\qquad
 (L_z\cap L_+)\vee(L_z\cap L_-)=\{0\}.
$$

两边不等。

$\square$

因而从经典命题到量子投影不能只替换符号而保留全部 Boolean 运算规则。 “子空间并”在非对易场合的操作解释需要单独规定， 不能直接认作任意自然语言存在量词。

#### 反例 5.6：Bloch 正交不是概念否定

对于纯 qubit， $P_{\mathbf n}=(I+\mathbf n\cdot\boldsymbol{\sigma})/2$。 两个方向的投影概率为

$$
\operatorname{tr}(P_{\mathbf n}P_{\mathbf m})
 =\frac{1+\mathbf n\cdot\mathbf m}{2}.
$$

所以 $\mathbf n\perp\mathbf m$ 给出 $1/2$， 并非“不是这个状态”的概率一。 正交 Hilbert 射线对应 Bloch 对跖点 $-\mathbf n$。

#### 命题 5.7：恒真存在效应的边界

若效应 $G$ 对所有密度矩阵都有 $\operatorname{tr}(\rho G)=1$，则 $G=I$。 此时补效应为零，$\operatorname{Hom}_{\mathbb C}(\mathcal H,\{0\})=\{0\}$， 不存在由该二元区分确定的非零跨块关系空间。

**证明。**

对所有单位向量 $u$ 有 $\langle u,(I-G)u\rangle=0$。 $I-G$ 正半定，故它的所有特征值均为零，得到 $G=I$。 其余由零补空间直接得到。

$\square$

若想让“至少有一个粒子”成为非平凡测试， 一种具体模型可以包含给定 $|\mathrm{vac}\rangle$ 的真空扇区与其补空间， 再定义 $P_{\mathrm{occupied}}=I-P_{\mathrm{vac}}$。 它的秩、动力学及可测性都是额外结构。 一个归一化真空态也不是零向量，更不是所有意义上的“不存在”。

<a id="section-6"></a>

## 6　稳定命名与内部生成可以共存

#### 定义 6.1：锐概念的可重复仪器

二元仪器 $\mathcal I_1,\mathcal I_0$ 的效应为 $P,Q$， 即 $\operatorname{tr}\mathcal I_1(\rho)=\operatorname{tr}(P\rho)$。 称它可重复，若每个非零概率的结果分支，立刻复测同一投影 都以概率一重现该结果。

#### 定理 6.2：全部可重复更新的刻画

效应为 $P$ 的分支 $\mathcal I_1(\rho)=\sum_\mu K_\mu\rho K_\mu^\dagger$ 可重复，当且仅当

$$
K_\mu=PK_\mu P,\qquad
 \sum_\mu K_\mu^\dagger K_\mu=P.
$$

等价地，它是 $E$ 内部任意保迹完全正通道作用于 $P\rho P$。 当 $r=1$ 时该分支唯一等于 $P\rho P$； 当 $r\geq2$ 时通常不唯一。

**证明。**

效应条件在 $v\in F$ 上给出 $\sum_\mu\left\|K_\mu v\right\|^2=0$，所以每个 $K_\mu Q=0$。 可重复性意味着所有输入的输出均支撑于 $E$； 对纯输入 $u$，漏出概率 $\sum_\mu\left\|QK_\mu u\right\|^2=0$，所以 $QK_\mu=0$。 合并得到 $K_\mu=PK_\mu P$。 反过来，这个形式保证输出在 $E$ 中，且效应正是 $P$。 限制到 $E$ 后的 Kraus 归一化等于 $I_E$， 故恰为该子空间内任意保迹完全正通道。 若 $r=1$，每个 $K_\mu=k_\mu P$， $\sum_\mu|k_\mu|^2=1$，所以输出为 $P\rho P$。 若 $r\geq2$，恒等更新和固定态制备 $\rho\mapsto\operatorname{tr}(P\rho)\tau_E$ 都可重复，但一般不同。

$\square$

Lüders 更新 $P\rho P$ 是其中保留块内信息的一种指定选择 [\[4\]](#ref-luders)。不能单凭“可重复说出同一个概念”就把内部状态冻结。

#### 定理 6.3：概率稳定的通道判据

对通道 $\Phi(\rho)=\sum_\alpha K_\alpha\rho K_\alpha^\dagger$， 以下等价：

$$
\operatorname{tr}(P\Phi(\rho))=\operatorname{tr}(P\rho)\ \ \forall\rho;
 \qquad
 \Phi^*(P)=P;
 \qquad
 [K_\alpha,P]=0\ \ \forall\alpha.
$$

**证明。**

迹对偶与所有态对 Hermitian 算子的分离性给出前两项等价。 若 $`\Phi^*(P)=P`$，则对 $v\in F$， $\sum_\alpha\left\|PK_\alpha v\right\|^2=0$， 故 $PK_\alpha Q=0$。 通道满足 $`\Phi^*(I)=I`$，所以 $`\Phi^*(Q)=Q`$； 同理 $QK_\alpha P=0$。两个交叉块均为零即对易。 反之，对易与 $\sum_\alpha K_\alpha^\dagger K_\alpha=I$ 给出 $`\Phi^*(P)=P`$。

$\square$

#### 例 6.4：一个稳定概念内的非平凡生成

在 $\mathbb C^3$ 中取

$$
P=|0\rangle\langle 0|+|1\rangle\langle 1|,\qquad
 H=\hbar\omega|1\rangle\langle 1|,\qquad
 |\psi(t)\rangle=\frac{|0\rangle+e^{-\mathrm i\omega t}|1\rangle}{\sqrt2}.
$$

则 $\operatorname{tr}(P|\psi(t)\rangle\langle \psi(t)|)=1$ 始终成立。 但是对 $P_+=|+\rangle\langle +|$、$|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$，

$$
\operatorname{tr}(P_+|\psi(t)\rangle\langle \psi(t)|)
 =\frac{1+\cos(\omega t)}2.
$$

“属于概念 $P$”稳定，同时在这个概念内部发生可见相位演化。

因此，把“存在”和“生成”预设为互斥的正交方向，会排除这个完全一致的模型。 更准确的结构是：稳定标签之下可以有生成；跨越标签边界则是另一种变化。

<a id="section-7"></a>

## 7　两种压缩与跨块关系

相干总是相对于指定基底或分解而说。 标准相干资源理论先固定基底再定义非相干态[\[6\]](#ref-baumgratz)。 本节采用两个子空间的分块版本，并逐项证明。

#### 定义 7.1：分块与 Lüders 非选择通道

相对于 $\mathcal H=E\oplus F$，写

$$
\rho=\begin{pmatrix}A&C\\C^\dagger&B\end{pmatrix},
 \qquad
 A=P\rho P,\quad B=Q\rho Q,\quad C=P\rho Q,
 \qquad p=\operatorname{tr}A.
$$

这里各块分别视为对应子空间之间的映射。 定义

$$
\mathcal D_P(X)=PXP+QXQ,\qquad
 W_P(\rho)=\rho-\mathcal D_P(\rho)=C+C^\dagger.
$$

$C$ 是 *该态相对于此概念* 的实际跨块相干。

#### 定理 7.2：分块条件期望

$\mathcal D_P$ 完全正、保迹、保幺元、幂等， 且是 Hilbert–Schmidt 内积下的正交投影。 其像为

$$
\{X:[X,P]=0\}\cong M_r(\mathbb C)\oplus M_s(\mathbb C),
$$

其核为全部交叉块。 Hermitian 核的实维数为 $2rs$。 对任意与 $P$ 对易的 $A_0,B_0$，

$$
\mathcal D_P(A_0XB_0)=A_0\mathcal D_P(X)B_0.
$$

**证明。**

Kraus 算子为 $P,Q$，其平方和及伴随平方和都是 $I$， 给出完全正、保迹和保幺元。$PQ=0$ 给出幂等性。 循环迹给出 $\operatorname{tr}(X^\dagger\mathcal D_PY)=\operatorname{tr}((\mathcal D_PX)^\dagger Y)$， 故幂等算子也自伴，因而是正交投影。 分块矩阵显示它恰保留对角块，像等于 $P$ 的交换子代数。 Hermitian 核由一个任意复 $r\times s$ 块决定，实维数为 $2rs$。 最后一个等式由 $A_0,B_0$ 的分块对角形式直接相乘得到。

$\square$

#### 推论 7.3：相位平均表述

若 $U_\phi=P+e^{\mathrm i\phi}Q$，则

$$
\mathcal D_P(X)=\frac1{2\pi}\int_0^{2\pi}
 U_\phi XU_\phi^\dagger\,\mathrm d\phi
 =\frac12\bigl(X+(P-Q)X(P-Q)\bigr).
$$

**证明。**

共轭后两个交叉块分别乘 $e^{-\mathrm i\phi}$ 和 $e^{\mathrm i\phi}$， 平均为零。用相位 $0,\pi$ 两点平均也给出同一结果。

$\square$

这是通道的数学表达，不自动断言世界执行了某种随机平均。 更不能把一个内积数值本身当作实际测量仪器。

#### 命题 7.4：只保留标签概率是更粗的压缩

标签代数上的保迹正交投影为

$$
\mathcal E_P(X)=\frac{\operatorname{tr}(PX)}rP+\frac{\operatorname{tr}(QX)}sQ.
$$

它也是完全正通道；在态上只保留 $p$， 而 $\mathcal D_P(\rho)$ 保留全部 $A$ 和 $B$。 两种通道相同当且仅当 $r=s=1$。

**证明。**

该公式先测量二元标签，再在对应块制备最大混合态， 故完全正保迹。直接计算它对 $P,Q$ 的内积即得正交投影性质。 若 $r=s=1$，每个块仅由它的迹决定，所以二者相同。 若某块维数大于一，该块内的纯态被 $\mathcal D_P$ 保留， 而被 $\mathcal E_P$ 变成该块最大混合态，故不同。

$\square$

#### 定理 7.5：固定块读出的正性纤维

固定 $A,B\geq0$ 且 $\operatorname{tr}A+\operatorname{tr}B=1$。 分块矩阵 $\rho$ 正半定，当且仅当

$$
C=A^{1/2}KB^{1/2},\qquad \left\|K\right\|_{\rm op}\leq1,
$$

其中 $K:\operatorname{supp}B\to\operatorname{supp}A$，在核上延拓为零。 若 $a=\operatorname{rank}A$、$b=\operatorname{rank}B$，所有这种 $\rho$ 构成的纤维具有仿射实维数 $2ab$。

**证明。**

若 $u\in\ker A$，考察任意 $tu\oplus v$ 的二次型。 关于任意复数 $t$ 的线性项必须恒为零， 所以 $\langle u,Cv\rangle=0$，即 $C^\dagger u=0$。 同理 $C$ 在 $\ker B$ 上为零。 因此可限制到支持空间，那里 $A,B$ 可逆。 以 $\operatorname{diag}(A^{-1/2},B^{-1/2})$ 作合同变换得到

$$
\rho\geq0
 \quad\Longleftrightarrow\quad
 \begin{pmatrix}I&K\\K^\dagger&I\end{pmatrix}\geq0.
$$

右边的二次型可配方为 $\left\|u+Kv\right\|^2+\langle v,(I-K^\dagger K)v\rangle$， 所以等价于 $\left\|K\right\|_{\rm op}\leq1$。 反向合同变换给出充分性。 支持上的映射 $K\mapsto A^{1/2}KB^{1/2}$ 可逆， 收缩球含复 $ab$ 维空间中零点的开邻域， 故其仿射实维数为 $2ab$。零秩情形直接给出单点。

$\square$

#### 定理 7.6：只固定一个概率的纤维

对 $0<p<1$，

$$
\{\rho\geq0:\operatorname{tr}\rho=1,\ \operatorname{tr}(P\rho)=p\}
$$

的仿射实维数为 $d^2-2$。 $p=1$ 时维数为 $r^2-1$，$p=0$ 时为 $s^2-1$。

**证明。**

Hermitian 算子空间实维数为 $d^2$。 $I$ 与 $P$ 线性独立，两个迹约束独立。 $\rho_0=pP/r+(1-p)Q/s$ 正定， 保证正性没有进一步降低该仿射切片的维数。 端点由定理 5.2 限制到对应子空间的全部归一态， 得到其通常的 Hermitian 维数减去一个迹约束。

$\square$

| $(d,r)$ | 固定 $p\in(0,1)$ | 固定正定块 $A,B$ | 概念可动切空间 |
|:---------:|:------------------:|:------------------:|:--------------:|
| $(2,1)$ |       $2$        |       $2$        |     $2$      |
| $(3,1)$ |       $7$        |       $4$        |     $4$      |
| $(4,2)$ |       $14$       |       $8$        |     $8$      |

表中全为实维数；第三列要求两个固定块在各自整个子空间上正定。 只有最小二能级情形，标签概率剩余量、跨块纤维和概念切空间的维数恰巧相同； 即使维数相同，它们也仍是不同的数学对象。

<a id="section-8"></a>

## 8　从关系块到可见波纹

#### 定理 8.1：跨块相干的界与最优见证

令 $C=P\rho Q$、$p=\operatorname{tr}(P\rho)$。则

$$
\left\|C\right\|_1\leq\sqrt{p(1-p)},\qquad
 \left\|\rho-\mathcal D_P\rho\right\|_1=2\left\|C\right\|_1.
$$

而且

$$
\max_{0\leq G\leq I}
 \left|\operatorname{tr}\bigl(G(\rho-\mathcal D_P\rho)\bigr)\right|=\left\|C\right\|_1.
$$

**证明。**

由定理 7.5 和 Schatten 不等式，

$$
\left\|C\right\|_1
 \leq\left\|A^{1/2}\right\|_2\left\|KB^{1/2}\right\|_2
 \leq\sqrt{\operatorname{tr}A\,\operatorname{tr}B}.
$$

$W=\rho-\mathcal D_P\rho$ 的非零特征值为 $C$ 的奇异值及其相反数， 所以迹范数恒等式成立。 取极分解 $C=V|C|$，定义

$$
B_C=\begin{pmatrix}0&V\\V^\dagger&0\end{pmatrix},
 \qquad G_C=\frac12(I+B_C).
$$

$V$ 为部分等距，故 $\left\|B_C\right\|_{\rm op}\leq1$，$G_C$ 是合法效应， 并有 $\operatorname{tr}(B_CW)=2\operatorname{tr}|C|$、$\operatorname{tr}W=0$。 因此 $\operatorname{tr}(G_CW)=\left\|C\right\|_1$。 另一方面，$W=W_+-W_-$ 无迹，任意效应 $G$ 都满足 $|\operatorname{tr}(GW)|\leq\operatorname{tr}W_+=\left\|W\right\|_1/2$， 证明最优性。$C=0$ 时取 $B_C=0$。

$\square$

最优见证依赖具体的 $C$。这个定理是对允许全部效应的菜单的最优性陈述； 不能由数学存在性自动宣布某个装置已经具备该测量能力。

#### 定义 8.2：平衡跨块比较菜单

允许相位控制 $U_\phi=P+e^{\mathrm i\phi}Q$，以及

$$
G_T=\frac12\left[I+
 \begin{pmatrix}0&T\\T^\dagger&0\end{pmatrix}\right],
 \qquad T:F\to E,\quad\left\|T\right\|_{\rm op}\leq1.
$$

称 $\mathcal V_P(\rho)$ 为该菜单中扫描 $\phi$ 可获得的最大 $(p_{\max}-p_{\min})/(p_{\max}+p_{\min})$。

#### 定理 8.3：可见度与标签可预测度的互补界

在上述菜单条件下，

$$
p_T(\phi)
 =\operatorname{tr}(G_TU_\phi\rho U_\phi^\dagger)
 =\frac12+\Re\!\left(e^{-\mathrm i\phi}\operatorname{tr}(T^\dagger C)\right),
$$

$$
\boxed{\mathcal V_P(\rho)=2\left\|P\rho Q\right\|_1},
 \qquad
 \boxed{(2p-1)^2+\mathcal V_P(\rho)^2\leq1}.
$$

这里 $|2p-1|$ 是二元标签的概率偏置或可预测度，不是动力学稳定性的量度。 纯态取得等号。

**证明。**

共轭令 $C$ 乘以 $e^{-\mathrm i\phi}$，分块相乘即得概率式。 该条纹最大与最小概率分别为 $1/2\pm|\operatorname{tr}(T^\dagger C)|$， 所以可见度是 $2|\operatorname{tr}(T^\dagger C)|$。 迹范数对偶性及极分解 $T=V$ 给出最大值 $2\left\|C\right\|_1$。 再使用定理 8.1 及 $(2p-1)^2+4p(1-p)=1$。 若 $\rho=|\psi\rangle\langle \psi|$，则 $C=|P\psi\rangle\langle Q\psi|$， $\left\|C\right\|_1=\left\|P\psi\right\|\left\|Q\psi\right\|=\sqrt{p(1-p)}$， 故等号成立。

$\square$

对一般非平衡效应，若条纹为 $a+2\Re(e^{-\mathrm i\phi}z)$， 其通常可见度是 $2|z|/a$（$a>0$）。 不能把特定菜单的公式无条件扩张到所有仪器。

#### 命题 8.4：相位是否可读取决于菜单

效应 $G$ 对所有态的 $U_\phi$ 扫描都不敏感， 当且仅当 $[G,P]=0$。 因此反复询问同一个概念 $P$ 本身不能读出跨块相位。

**证明。**

对易时共轭保持 $G$，概率显然不变。 若所有态的概率不变，态分离性给出 $U_\phi^\dagger G U_\phi=G$。 在 $\phi=\pi$ 时两个交叉块变号， 故它们必须为零，即 $[G,P]=0$。

$\square$

这一点与前稿的内部参考合同一致： 相位是否成为可观测差异，需要明确的相干比较装置。 相对一个受限菜单不可见，不等于相对所有可能菜单都没有意义。

<a id="section-9"></a>

## 9　从二维正交面推广到概念的关系流形

### 9.1　高秩概念的切空间

#### 定义 9.1：概念 Grassmann 空间

记 $\operatorname{Gr}(r,d)$ 为 $\mathcal H$ 中所有秩 $r$ 正交投影的集合。 它刻画同样秩的锐概念边界可以如何连续移动。 这里变化的是概念投影 $P$，不是只改变固定 $P$ 下的态 $\rho$。

#### 定理 9.2：关系切空间与自然复结构

对 $P\in\operatorname{Gr}(r,d)$，

$$
T_P\operatorname{Gr}(r,d)
 =\{X=X^\dagger:PXP=QXQ=0\}
 \cong\operatorname{Hom}_{\mathbb C}(E,F).
$$

同构把 $Z:E\to F$ 送到

$$
X_Z=\begin{pmatrix}0&Z^\dagger\\Z&0\end{pmatrix}.
$$

切空间实维数为 $2r(d-r)$，具有复结构

$$
J_PX=\mathrm i[X,P],\qquad J_PX_Z=X_{\mathrm iZ},\qquad J_P^2=-I.
$$

并可定义

$$
\begin{aligned}
 g_P(X_Z,X_W)&=\tfrac12\operatorname{tr}(X_ZX_W)=\Re\operatorname{tr}(Z^\dagger W),\\
 \omega_P(X_Z,X_W)&=g_P(J_PX_Z,X_W)=\Im\operatorname{tr}(Z^\dagger W).
\end{aligned}
$$

**证明。**

对投影曲线 $P(t)^2=P(t)=P(t)^\dagger$ 求导， 得到 $PX+XP=X$ 和 $X=X^\dagger$， 等价于两个对角块为零。 反过来，给定这种 $X$，令 $A=[X,P]$， 则 $A^\dagger=-A$ 且 $[A,P]=X$。 所以 $P(t)=e^{tA}Pe^{-tA}$ 是投影曲线，导数为 $X$。 分块表示给出同构和维数。 直接相乘得到 $\mathrm i[X_Z,P]=X_{\mathrm iZ}$，故 $J_P^2=-I$。 迹计算给出度量式； $\Re\operatorname{tr}((\mathrm iZ)^\dagger W)=\Im\operatorname{tr}(Z^\dagger W)$， 给出反对称形式及正定的 Hermitian 结构。

$\square$

#### 推论 9.3：OTF-002 的二维平面是最小情形

秩一情形为 $\operatorname{Gr}(1,d)=\mathbb{CP}^{d-1}$， 关系空间复维数 $d-1$、实维数 $2(d-1)$。 仅当 $d=2$ 时，它是一条复线，即一个实二维平面。 若 $P_{\mathbf n}=(I+\mathbf n\cdot\boldsymbol{\sigma})/2$， 切向量 $X_{\mathbf u}=(\mathbf u\cdot\boldsymbol{\sigma})/2$ 满足 $\mathbf u\perp\mathbf n$，并有

$$
J_PX_{\mathbf u}=X_{\mathbf n\times\mathbf u}.
$$

**证明。**

秩一投影等同复射线，给出射影空间。 维数由定理 9.2 取 $r=1$ 得到。 Pauli 乘积关系给出 $[\mathbf u\cdot\boldsymbol{\sigma},\mathbf n\cdot\boldsymbol{\sigma}] =2\mathrm i(\mathbf u\times\mathbf n)\cdot\boldsymbol{\sigma}$， 代入 $J_P=\mathrm i[\,\cdot\,,P]$ 即得结论。

$\square$

这就是前稿 $\mathbf n^\perp$ 上 $J_{\mathbf n}\mathbf u=\mathbf n\times\mathbf u$ 的高维推广。 它把“概念旁边存在连续的关系方向”发展为一个精确的几何对象。 在实 $n$ 维定向度量空间中，Hodge 对偶则是 $`*:\Lambda^1\to\Lambda^{n-1}`$； 向量与二向量的直接配对特有于 $n=3$，不适用于任意语义空间。

### 9.2　结构性关系不等于已经占据的相干

#### 定理 9.4：单态关系与实际相干的分离

设 $P=|\psi\rangle\langle \psi|$ 且当前态 $\rho=P$。 则 $P\rho Q=0$，但对 $Z,W:E\to F$，

$$
\langle X_Z\rangle_\psi=0,\qquad
 \langle X_ZX_W\rangle_\psi
 =\langle Z\psi,W\psi\rangle.
$$

特别地，$\operatorname{Var}_\psi(X_Z)=\left\|Z\psi\right\|^2$， 在 $Z\ne0$ 时为正。

**证明。**

$P^2=P$、$PQ=0$ 给出跨块相干为零。 $X_Z$ 将 $\psi\in E$ 送到 $Z\psi\in F$， 因而其期望为零。 $X_ZX_W$ 在 $E$ 上的块为 $Z^\dagger W$， 所以期望为 $\langle\psi,Z^\dagger W\psi\rangle$， 即所给内积。取 $W=Z$ 得方差。 由于 $E$ 一维，$Z\ne0$ 当且仅当 $Z\psi\ne0$。

$\square$

在 qubit 中取横向观测 $\Sigma_{\mathbf u}=\mathbf u\cdot\boldsymbol{\sigma}$、 $\mathbf u,\mathbf v\perp\mathbf n$，可直接恢复前稿的核：

$$
\langle \Sigma_{\mathbf u}\Sigma_{\mathbf v}\rangle_{\mathbf n}
 =\mathbf u\cdot\mathbf v
  +\mathrm i\,\mathbf n\cdot(\mathbf u\times\mathbf v).
$$

因此“状态相对于自身标签没有跨块相干”和“存在非零横向涨落” 并不矛盾。前者描述固定态的密度块，后者描述两个探测方向的复关联。

#### 命题 9.5：关系空间不自动指定频率

在二能级中令 $H=E_P P+E_Q Q$、$\rho=P$， 并取横向算符 $X_Z,X_W$。 若 $\Delta=E_Q-E_P$，

$$
\operatorname{tr}\bigl(PX_Z(t)X_W\bigr)
 =e^{-\mathrm i\Delta t/\hbar}\operatorname{tr}(PX_ZX_W),
 \qquad X_Z(t)=e^{\mathrm iHt/\hbar}X_Ze^{-\mathrm iHt/\hbar}.
$$

同一 $P$ 和关系平面相容于任意 $\Delta$，包括 $\Delta=0$。

**证明。**

$X_W$ 先把 $E$ 中的向量送入 $F$。 $X_Z(t)$ 将它送回 $E$ 的块带有因子 $e^{\mathrm iE_Pt/\hbar}e^{-\mathrm iE_Qt/\hbar}$， 所以得到公式。 $E_P,E_Q$ 可以独立指定而不改变投影，故频率不能由平面独立推出。

$\square$

| 层次 | 精确对象 | 非零需要什么 |
|:---|:---|:---|
| 结构性关系 | $\operatorname{Hom}(E,F)$、$T_P\operatorname{Gr}(r,d)$ | 两个子空间都非零 |
| 实际跨块相干 | $C=P\rho Q$ | 态在该分解下非分块对角 |
| 可见相位条纹 | $p_T(\phi)$ | 非零可耦合相干及允许的比较菜单 |
| 两时关联振荡 | $\operatorname{tr}(\rho X(t)Y)$ | 相关探测通道及相应非零频率 |

纯态自身的例子可以在第二行取零、第一行非零， 并在合适动力学和协议下使第四行振荡。 这个分层保留了前稿的单态关系结构，同时避免把所有“波”定义为同一件事。

<a id="section-10"></a>

## 10　稳定概念的动力学与最小未来精化

### 10.1　经典概念能否独立演化

#### 定理 10.1：确定过程的概念下降

设 $q:X\to B_{\rm eff}$ 满射，$F:X\to X$。 存在唯一 $\bar F:B_{\rm eff}\to B_{\rm eff}$ 使 $qF=\bar Fq$，当且仅当

$$
q(x)=q(y)\ \Longrightarrow\ q(Fx)=q(Fy).
$$

**证明。**

有因子分解时该蕴涵立即成立。 反之令 $\bar F(q(x))=q(Fx)$，所给条件保证良定义， 满射性保证定义域完整及唯一性。

$\square$

如果条件失败，两个当前被称为“同一概念”的状态有不同的下一次读出。 这时单一标签没有闭合的确定动力学； 需要保留纤维中的额外区分，或明确引入概率模型。

#### 定理 10.2：有限未来观察闭包

设 $|X|=N\geq1$，$F:X\to X$，定义

$$
q_m(x)=\bigl(q(x),q(Fx),\ldots,q(F^m x)\bigr).
$$

由这些读出产生的划分逐步精化，至迟 $q_{N-1}$ 的等价关系已经稳定， 并等于

$$
x\sim_\infty y\quad\Longleftrightarrow\quad
 q(F^n x)=q(F^n y)\quad\forall n\geq0.
$$

这个未来响应商允许 $F$ 下降， 且是保留全部这些未来响应的最粗编码。

**证明。**

增加一个坐标只可能拆分纤维。 每次严格精化至少增加一个非空纤维，纤维数最多为 $N$。 如果某一步 $q_{m+1}$ 与 $q_m$ 给出相同划分， 则 $x\sim_m y$ 蕴涵 $q(F^{j+1}x)=q(F^{j+1}y)$ 对 $0\leq j\leq m$ 成立， 即 $Fx\sim_m Fy$。因此该划分已在 $F$ 下不变， 归纳得到所有更远未来都相同。 从至少一个初始纤维起，若前 $N-1$ 步全严格精化， 到此也已成为单点划分，必然稳定。 所以最晚 $q_{N-1}$ 等于全部未来关系。 该关系对 $F$ 不变，定理 10.1 给出下降。 任何保留全部未来响应的编码，其等值纤维必须包含在这些联合响应纤维内， 由定理 2.2 给出最粗性。

$\square$

#### 定理 10.3：Markov 过程的概念闭合

令 $K(x,y)$ 为有限 Markov 转移矩阵。 标签 $q(x)$ 对任意初始分布都形成同一个闭合 Markov 核， 当且仅当对每个目标标签 $b$，

$$
\sum_{y\in F_b}K(x,y)
$$

在每个源纤维 $F_a$ 上为常数。 此时该常数就是 $\bar K(a,b)$。

**证明。**

如果常数条件成立，给定当前状态 $x\in F_a$， 下一标签的条件分布只依赖 $a$； 对任意过去历史和当前纤维内的条件分布再平均， 仍得到同一个 $\bar K(a,\cdot)$，所以标签过程是该 Markov 链。 反之，对同一纤维中的任意两个状态分别取点质量初始分布， 闭合核必须给出相同的下一标签概率， 故上述和在纤维中相同。

$\square$

### 10.2　量子内部生成与跨概念流动

#### 定理 10.4：Hamiltonian 下的概念概率流

设

$$
H=\begin{pmatrix}H_E&L\\L^\dagger&H_F\end{pmatrix},
 \qquad \dot\rho=-\frac{\mathrm i}{\hbar}[H,\rho].
$$

则

$$
\begin{aligned}
 \dot p&=\frac2\hbar\,\Im\operatorname{tr}(LC^\dagger),\\
 \dot C&=-\frac{\mathrm i}{\hbar}
       (H_EC-CH_F+LB-AL).
\end{aligned}
$$

固定 $H$ 对所有初始态保持 $p$，当且仅当 $[H,P]=0$。

**证明。**

分块相乘给出 $E$ 块 $[H_E,A]+LC^\dagger-CL^\dagger$； 对它取迹，交换子项为零， 后两项之差为 $2\mathrm i\Im\operatorname{tr}(LC^\dagger)$。 交叉块直接给出第二式。 若 $[H,P]=0$，$L=0$，故 $p$ 恒定。 反之，对所有初始态的导数为零意味着 $\operatorname{tr}(\rho\,\mathrm i[H,P])=0$ 对所有态成立， 从态分离性得到 $[H,P]=0$。

$\square$

该公式提供三种可同时存在的运动： 块内态在固定概念下变化，跨块相干改变，以及标签概率流动。 $C=0$ 令瞬时 $\dot p=0$，却不一定令 $\dot C=0$； 相干可以由 $LB-AL$ 产生，随后影响标签概率。 若 $\rho=I/d$，则 $LB-AL=0$ 且所有幺正动力学都保持该态， 说明有可用通道仍不等于发生实际变化。

<a id="section-11"></a>

## 11　真正充分的预测读出：效应闭包

一个静态标签代数可能不足以预测经过控制后的读出。 反过来，把几个测量算子生成的整个 $`*`$-代数都宣布可访问，也可能增加 本来没有被允许的操作。最小充分对象首先是允许协议的效应线性空间。

#### 定义 11.1：有限协议菜单

给定有限终端效应集 $\mathcal F$， 以及有限个允许、可任意依次组合的仪器分支 $\Phi_j$（完全正且迹不增）。 令 $`\Gamma_j=\Phi_j^*`$。 允许的序列响应效应为

$$
\Gamma_{j_1}\cdots\Gamma_{j_n}(E),
 \qquad E\in\mathcal F\cup\{I\}.
$$

若衔接限制可由有限状态控制器表达，可把控制寄存器加入模型， 将禁止的衔接置为零分支，并按合法控制位置指定终端效应。 一般控制语法须另行保留合法序列规则，不能直接允许所有词。

#### 定理 11.2：最小效应闭包

定义实 Hermitian 线性空间

$$
\begin{aligned}
 \mathcal S_0&=\operatorname{span}_{\mathbb R}(\{I\}\cup\mathcal F),\\
 \mathcal S_{n+1}&=\mathcal S_n+\sum_j\Gamma_j(\mathcal S_n).
\end{aligned}
$$

该递增序列在有限步稳定，严格增长次数不超过 $d^2-\dim_{\mathbb R}\mathcal S_0$。 稳定空间 $\mathcal S_\infty$ 是包含全部允许序列效应的最小线性空间， 也是包含 $\mathcal S_0$ 的最小 $\Gamma_j$-不变空间。 两个态对全部允许协议不可区分，当且仅当

$$
\operatorname{tr}\bigl((\rho-\sigma)X\bigr)=0\quad\forall X\in\mathcal S_\infty.
$$

**证明。**

归纳可知 $\mathcal S_n$ 正是长度至多 $n$ 的全部序列效应的实线性张成。 Hermitian 空间实维数为 $d^2$，每次严格增长至少增加一维。 一旦 $\mathcal S_{n+1}=\mathcal S_n$，每个 $\Gamma_j$ 都保持该空间， 以后不会再增长。由序列效应的张成得到两个最小性结论。 响应差是与相应效应的迹配对， 对所有生成效应为零当且仅当对其线性张成为零，得到最后的等价式。

$\square$

#### 反例 11.3：生成代数不等于允许的测量菜单

qubit 菜单只允许 $\sigma_x,\sigma_z$ 的 Lüders 测量及其有限顺序、 经典结果处理。所有分支 Kraus 都是实矩阵； 因此全部响应效应是实对称矩阵，

$$
\mathcal S_\infty=\operatorname{span}_{\mathbb R}\{I,\sigma_x,\sigma_z\}.
$$

态 $\rho_\pm=(I\pm\sigma_y)/2$ 对该菜单不可区分。 但 $\sigma_x,\sigma_z$ 生成的复 $`*`$-代数是全部 $M_2(\mathbb C)$， 其中包含可区分两态的 $\sigma_y$。 所以代数乘积闭包不能替代实际协议闭包。

**证明。**

实 Kraus 的伴随作用把实对称矩阵送到实对称矩阵； 该空间在 $2\times2$ 情形恰为所列三维空间。 初始菜单已张成它，因而闭包正好等于它。 $\rho_+-\rho_-=\sigma_y$ 与这个空间迹正交。 而 $\sigma_x\sigma_z=-\mathrm i\sigma_y$，给出代数包络包含缺失方向。

$\square$

#### 反例 11.4：线性压缩不一定是量子通道

在 $\mathbb C^3$ 中只测 $G=\operatorname{diag}(0,\tfrac12,1)$， 令 $\mathcal S=\operatorname{span}_\mathbb R\{I,G\}$。 把 $\rho=\operatorname{diag}(1,0,0)$ 作 Hilbert–Schmidt 正交投影到 $\mathcal S$，结果是

$$
\rho_{\mathcal S}
 =\operatorname{diag}\left(\frac56,\frac13,-\frac16\right).
$$

它保留与 $I,G$ 的迹配对，但不是正态。

**证明。**

右边属于 $\mathcal S$，其迹为 $1$、与 $G$ 的迹配对为 $0$， 和原态的两项配对相同，故确为正交投影。 末项负值表明它不正半定。

$\square$

因此一般响应商应首先理解为响应坐标或对效应空间的正线性泛函。 只有另行证明正性与完全正性，才可以把某个压缩视为实际物理通道。 定理 7.2 已经为特定分块压缩完成了这一步。

<a id="section-12"></a>

## 12　观察者、名称与记录的内生实现

#### 定理 12.1：分类记录的内部实现

给定有限分类 $q:X\to B_{\rm eff}$。 在对象空间 $\ell^2(X)$ 与记忆空间 $\ell^2(B_{\rm eff})$ 中定义

$$
V|x\rangle=|x\rangle\otimes|q(x)\rangle.
$$

则 $V$ 是等距映射，而且

$$
V^\dagger(I\otimes|b\rangle\langle b|)V=P_b.
$$

它可由准备好的内部记忆与一个总空间幺正交互实现。 忽略该记忆后，对象态变成 $\sum_bP_b\rho P_b$。

**证明。**

不同 $|x\rangle$ 的第一因子已经正交， 故像向量仍是正交归一组，$V^\dagger V=I$。 对每个 $|x\rangle$ 检查读出拉回，只有 $q(x)=b$ 时返回 $|x\rangle$， 得到所给投影。 加入记忆准备态 $|\mathrm{ready}\rangle$， 将 $|x\rangle|\mathrm{ready}\rangle\mapsto V|x\rangle$ 定义在准备子空间上。 两个同维子空间间的等距映射可通过补齐正交基扩张为总空间幺正。 最后，

$$
V\rho V^\dagger
 =\sum_{b,c}P_b\rho P_c\otimes|b\rangle\langle c|.
$$

对记忆取偏迹，$\operatorname{tr}(|b\rangle\langle c|)=\delta_{bc}$， 便得到非选择通道。

$\square$

这个构造中，标签记录本身可以是一条记忆射线， 但对应对象投影仍有秩 $|F_b|$。 若对象初态是经典对角混合，联合态也只是

$$
\sum_x\mu(x)|x\rangle\langle x|\otimes
 |q(x)\rangle\langle q(x)|.
$$

它已有命名、分类和记录，却无标准基间的相干。 因而命名本身不能强制产生量子相位。

#### 定理 12.2：普遍无扰动记录不能获取态信息

设固定准备的记忆与系统发生等距交互 $V:\mathcal H\to\mathcal H\otimes\mathcal H_R$。 若对每个单位纯态 $\psi$，交互后系统边缘仍恰为 $|\psi\rangle\langle \psi|$，则存在同一单位记忆态 $\eta$ 使

$$
V|\psi\rangle=|\psi\rangle\otimes|\eta\rangle
 \qquad\forall\psi.
$$

因此该记忆不携带输入态的可区分信息。

**证明。**

纯边缘要求总纯态可分，故 $V|\psi\rangle=|\psi\rangle|\eta_\psi\rangle$，相位吸收入 $\eta_\psi$。 等距性给出

$$
\langle\psi,\varphi\rangle
 =\langle\psi,\varphi\rangle
   \langle\eta_\psi,\eta_\varphi\rangle.
$$

若 $\langle\psi,\varphi\rangle\ne0$， 则两个单位记忆向量的内积为 $1$，所以相同。 任意两条正交射线可用归一化的 $\psi+\varphi$ 连接， 相继两次非零内积也得到相同的记忆向量。 故所有输入共享同一 $\eta$。

$\square$

#### 推论 12.3：恒等总通道的仪器

若 $\sum_b\mathcal I_b=\mathrm{id}$，则 $\mathcal I_b(\rho)=p_b\rho$，其中 $p_b$ 与输入态无关、 $p_b\geq0$ 且 $\sum_bp_b=1$。

**证明。**

对纯态，所有分支 Kraus $K_{bj}$ 都必须把每个 $\psi$ 送入 $\operatorname{span}\psi$；否则某个正的分支会在正交方向留下不可抵消的概率。 一个把每条射线映入自身的线性算子必为标量： 在基向量上设特征值，再对任意两基向量之和作用可知这些值相同。 所以 $K_{bj}=c_{bj}I$，取 $p_b=\sum_j|c_{bj}|^2$ 即得。

$\square$

这里的前提是对 *全部纯态* 无扰动。 定理 12.1 可以无扰动记录正交编码态的类别， 并不违反本定理；跨类别叠加通常会与记忆发生关联。 一个恒真效应 $I$ 的单一回答也不提供输入态信息， 但仅有这个效应条件并不强制其对应通道为恒等； 更新仍须另行规定。

### 12.1　有限整体中的历史与内部时钟

#### 定理 12.4：有限协议的静态历史实现

给定归一化整体初态 $\Psi_0$ 和有限幺正序列 $U_1,\ldots,U_N$， 令 $W_0=I$、$W_k=U_k\cdots U_1$。 包含系统、参考、记忆和时钟的归一化历史态为

$$
|\Omega\rangle=\frac1{\sqrt{N+1}}
 \sum_{k=0}^N|k\rangle_{\rm clock}\otimes W_k|\Psi_0\rangle.
$$

条件于内部时钟记录 $k$，其余系统状态为 $W_k\Psi_0$。 而且存在显式正算子 $K$，使 $\ker K=\operatorname{span}|\Omega\rangle$。

**证明。**

时钟向量正交且每个 $W_k$ 幺正，给出归一化与条件态。 把历史空间中的向量写为 $x=(x_0,\ldots,x_N)$，定义

$$
(Dx)_k=x_k-U_kx_{k-1},\quad 1\leq k\leq N,
 \qquad
 K=D^\dagger D+
 |0\rangle\langle 0|\otimes(I-|\Psi_0\rangle\langle \Psi_0|).
$$

$K$ 为两个正算子之和，其核满足 $x_k=U_kx_{k-1}$ 和 $x_0\in\operatorname{span}\Psi_0$。 故所有分量由同一标量确定，核恰为所列历史态的一维张成。

$\square$

有限 Kraus 仪器也可先扩张成内部等距交互再补成幺正： 取 $V\psi=\sum_{b,j}K_{bj}\psi\otimes|b,j\rangle$， 由 Kraus 归一化得到 $V^\dagger V=I$。 因而本稿使用的有限记录与比较协议都可以放进上述构造。 这给出一个相容的整体模型，不证明自然宇宙唯一等于这个有限模型， 也没有从静态历史形式推导出所选择的初态与门序列。

概念“存在”的符号记录也可以是 $\Omega$ 内的一个寄存器值。 记录语句的存在、该语句所指的对象、语句的真假， 仍由不同的模型关系判断；把记录放入整体不会消除这些类型区别。

<a id="section-13"></a>

## 13　各向同性、连续射线与量子化边界

#### 定理 13.1：完整幺正各向同性

若密度矩阵对所有 $U\in U(d)$ 满足 $U\rho U^\dagger=\rho$， 则 $\rho=I/d$。当 $d\geq2$ 时它不是纯态。

**证明。**

相对于任意固定基，和全部对角相位矩阵对易迫使 $\rho$ 的非对角元为零； 和全部置换矩阵对易迫使各对角元相等。 迹为一给出每项为 $1/d$。 反过来 $I/d$ 显然不变；其纯度 $\operatorname{tr}(\rho^2)=1/d<1$。

$\square$

对 qubit，这表示全 Bloch 旋转不变的态是球心， 而不是球面上的某个“尚未命名的纯方向”。 它依然是归一化模型态，可以给出非零读出概率。 “没有优先方向”不能等同于“没有存在”或“纯波”。

#### 反例 13.2：各向同性必须注明群与表示

在两个 qubit 中， $|s\rangle=(|01\rangle-|10\rangle)/\sqrt2$ 对所有共同 $SU(2)$ 旋转 $U\otimes U$ 不变，却是纯态。 这是因为反对称平方 $\Lambda^2\mathbb C^2$ 为一维， 共同作用在其上等于 $\det U=1$。 它并不对所有 $U(4)$ 变换不变，故不违反定理 13.1。

#### 命题 13.3：一维射线不意味着离散可计数

若 $d\geq2$，纯态射线集合不可数； 但任意一次能完美区分的不同纯态集合至多含 $d$ 个成员。

**证明。**

向量 $(|0\rangle+t|1\rangle)/\sqrt{1+t^2}$，$t\in\mathbb R$， 给出不同射线的单射族，所以不可数。 若纯态 $\psi_i$ 由一个 POVM 完美区分， 则效应 $E_i$ 满足 $E_i\psi_i=\psi_i$、 $E_i\psi_j=0$（$j\ne i$）， 分别由期望为一、为零以及 $0\leq E_i\leq I$ 得到。 因此 $\langle\psi_i,\psi_j\rangle =\langle E_i\psi_i,\psi_j\rangle =\langle\psi_i,E_i\psi_j\rangle=0$。 正交非零向量最多有 $d$ 个。

$\square$

“可以把状态表示成一条射线”与“测量输出离散” 是不同事实。即使一次实验有有限答案，所有可能纯态仍然连续。

#### 定理 13.4：闭合圆周何时给出整数权重

设 $U(\theta)$ 是有限维、可微的幺正群表示， $U(\theta+\phi)=U(\theta)U(\phi)$， $U(0)=I$ 且 $U(\theta+2\pi)=U(\theta)$。 则存在 Hermitian $G$，使

$$
U(\theta)=e^{-\mathrm i\theta G},\qquad
 \operatorname{spec}(G)\subseteq\mathbb Z.
$$

若只要求 $U(2\pi)=e^{\mathrm i\alpha}I$，则只保证特征值之差为整数。

**证明。**

令 $G=\mathrm iU'(0)$。 对幺正条件求导得 $G^\dagger=G$； 群性质给出 $U'(\theta)=-\mathrm iU(\theta)G$， 所以 $U(\theta)=e^{-\mathrm i\theta G}$。 将 $G$ 酉对角化，$e^{-2\pi\mathrm ig_j}=1$ 等价于 $g_j\in\mathbb Z$。 若末端只是公共相位，则 $e^{-2\pi\mathrm i(g_j-g_k)}=1$， 故只约束各特征值差。

$\square$

这是“圆周闭合产生整数”的准确版本。 它要求真实的表示、单值周期条件以及指定生成元， 并不由一张有向面积本身推出。 若令 $\theta=\omega t$，能量间隔还依赖 $\hbar\omega$ 的标定。 一般 Hamiltonian 例如

$$
H=\hbar\omega\,\operatorname{diag}(0,1,\sqrt2),
 \qquad \omega>0,
$$

没有非零共同复现周期： 若 $U(T)$ 是公共相位，零能级迫使此相位为一， 其余两级分别要求 $\omega T$、$\sqrt2\omega T$ 都为 $2\pi$ 的整数倍， 与 $\sqrt2$ 无理矛盾。

#### 注 13.5：内积、外积与投影需要分型

实内积 $\mathbf u\cdot\mathbf v$ 是标量； 单位方向上的向量投影才是 $(\mathbf u\cdot\mathbf v)\mathbf u$。 外积 $\mathbf u\wedge\mathbf v$ 是二向量， 并满足 $\mathbf u\wedge\mathbf u=0$。 三维 Hodge 对偶 $`*\mathbf u`$ 则是另一种运算。 它们各有严格几何用途，但均不是未经仪器规定的测量坍缩， 也不自动等于时间、语言或意识。

<a id="section-14"></a>

## 14　一个完整的四状态、四维例子

### 14.1　经典概念、否定与未来精化

取 $X=\{1,2,3,4\}$，概念 $q$ 只有两个值：

$$
q(1)=q(2)=a,\qquad q(3)=q(4)=b.
$$

观察代数为 $\{\varnothing,\{1,2\},\{3,4\},X\}$。 两个原子各含两个配置；名字是一个单位，所指并不是单个配置。

**图 1：**

四个配置的分类关系为 $1\mapsto a$、$2\mapsto a$、$3\mapsto b$、$4\mapsto b$。两个标签对应的完整纤维分别是 $F_a=\{1,2\}$ 与 $F_b=\{3,4\}$。

若命题 $A=\{1,3\}$，则两个标签的纤维都混合了真与假： $q(A)=q(A^c)=\{a,b\}$。否定不能在此粗读出中完成。 若过程 $F$ 交换 $2,3$、固定 $1,4$， 两个同属 $a$ 的配置有不同下一标签，故 $q$ 没有闭合确定动力学。 一次未来精化已经足够：

$$
\begin{array}{c|cccc}
x&1&2&3&4\\ \hline
(q(x),q(Fx))&(a,a)&(a,b)&(b,a)&(b,b).
\end{array}
$$

四个新原子都成为单点。

### 14.2　量子表示与可见比较

取 $\mathcal H=\mathbb C^4$，

$$
P=|1\rangle\langle 1|+|2\rangle\langle 2|,\qquad
 Q=|3\rangle\langle 3|+|4\rangle\langle 4|.
$$

两者在 $\mathcal A_P$ 中是原子，在完整代数中都不是原子。 记忆中的 $|a\rangle$、$|b\rangle$ 仍可以是两条秩一指针射线。

制备

$$
|\psi_\theta\rangle
 =\frac{|1\rangle+e^{\mathrm i\theta}|3\rangle}{\sqrt2}.
$$

则

$$
A=\tfrac12|1\rangle\langle 1|,\qquad
 B=\tfrac12|3\rangle\langle 3|,\qquad
 C=\tfrac12e^{-\mathrm i\theta}|1\rangle\langle 3|,\qquad p=\tfrac12.
$$

同一个二元概率不区分任何 $\theta$。 取允许的平衡效应

$$
G=\tfrac12\bigl(I+|1\rangle\langle 3|+|3\rangle\langle 1|\bigr),
$$

有

$$
\operatorname{tr}(G|\psi_\theta\rangle\langle \psi_\theta|)
 =\frac{1+\cos\theta}{2}.
$$

因此该菜单中可见度为 $1$。 忽略一个已正交记录 $a/b$ 的记忆以后，跨块项被删除， 同一比较概率变成 $1/2$。 若完整记忆仍可相干访问，整体信息并不由这个偏迹描述而消失； 那属于更丰富的协议菜单。

该例中 $r=s=2$，所以概念切空间实维数为 $8$， 只固定 $p=1/2$ 的全部态纤维实维数为 $14$。 然而这里固定的 $A,B$ 各只有秩一， 故这两个具体块之上的相干纤维实维数仅为 $2$。 这检验了定理 7.5 中必须保留秩条件。

另取 $|\varphi_\theta\rangle=(|1\rangle+e^{\mathrm i\theta}|2\rangle)/\sqrt2$， 则 $p=1$、$P\rho Q=0$，标签 $a$ 完全确定， 但更细的块内比较仍可看到 $\cos\theta$。 “概念内部的生成”与“两个概念之间的相干”在此被直接分开。

最后，若“此模型的归一化态存在”被定义成恒真判断， 其效应为 $I_4$，秩为 $4$，补空间为零。 把词“存在”写进一个指针态，不会把这个效应改成秩一。

<a id="section-15"></a>

## 15　理论的可检验内容与下一轮接口

### 15.1　本轮已经闭合的论证

在所列结构内，已经得到以下完整链条：

$$
\begin{gathered}
 \text{指定观察}\ \Longrightarrow\ \text{响应纤维与相对原子},\\
 \text{指定过程}\ \Longrightarrow\ \text{下降判据与未来精化},\\
 \text{指定量子表示}\ \Longrightarrow\
 \text{高秩概念、关系切空间与跨块相干},\\
 \text{指定参考协议}\ \Longrightarrow\
 \text{可见度、概率流与可区分性}.
\end{gathered}
$$

其中关系纤维不必是线性空间， 关系切空间不必是二维， 实际相干不必非零， 稳定标签也不必意味着内部停止变化。 这些边界都有同一套公理下的明确证明或反例。

本轮的组织性贡献是把前稿的单态轴面结构提升为  *观察相对的概念与关系理论* 。 纤维分解、形式概念闭包、投影逻辑、Lüders 更新等为已有数学； 本文的新组织及具体推论不构成对这些标准结果的优先权主张。

### 15.2　可以失败的模型主张

一个模型若声称某个标签足以确定下一次读出， 就必须通过定理 10.1 的同纤维一致性； 找到同标签而下一响应不同的两个制备，即可反驳该充分性主张。 若声称同一个宏观概率核适用于所有初始配置， 则须通过 Markov 纤维求和条件。 这些都是可枚举或可估计的具体条件。

一个量子实现若给定 $P$、态制备、相位控制与平衡比较菜单， 就预测定理 8.3 的条纹形式与上界。 实验不符合时，应检查这个具体实现、维数、可访问操作和噪声模型是否合适， 而不能用“更深层的波”让模型免于检验。 同样，块内比较若能区分具有相同粗标签的制备， 就说明该标签不能被当作完整纯态描述。

若要把模型用于自然语言意义或认知，应先规定可重复的语义任务、 可记录的回答及允许的过程，再比较经典和量子模型的解释范围。 仅有上下文依赖、顺序效应或非分配概念格，不足以证明物理量子相干： 例如两个经典更新 $F(x)=0$、$G(x)=1$ 已满足 $FG\ne GF$， 完全不需要量子态。 本稿没有预设任何特定脑机制，也没有证明一切意义都由有限读出穷尽。

### 15.3　继续发展的精确接口

第一，可以研究近似相同响应而非完全相同响应， 但距离小于阈值通常不传递，不能直接当作商等价。 需使用误差受控的聚类或近似充分性，并证明预测误差界。 第二，可以把有限未来闭包扩展到带控制与反馈的协议自动机， 计算满足指定预测精度的最小内部记忆。 第三，可以在不同读出代数之间研究哪些相干被恢复、哪些概念原子被细分， 并把代数访问条件与实际仪器成本关联。

这些方向均有清楚的对象、输入数据和失败条件。 关于时空、质量、电荷、引力或一般意识的结论， 还需要相应动力学、对称表示、耦合与经验桥梁；本稿不把它们包含在已证结论内。

### 15.4　不用术语时，本轮理论说了什么

当我们给某种东西取一个名字时，我们通常是在规定： 在当前允许的观察下，哪些差别可以先不管。 所以一个名字能够像一个颗粒那样稳定地被拿起、传递和记录； 但它里面可能包含很多状态，它周围也可能存在许多可以重新区分它的关系。

这种“颗粒”会随分辨率改变。粗看是一个单位，细看可以有内部结构； 同一个名字也可以在自身保持可辨认的同时持续变化。 名字后面的关系并不全是量子波，其中有经典的不确定性、 没有展开的属性、可允许的变化方向，也可能有需要相干比较才能读出的相位。 只有把这些关系的规则写清楚，才知道哪一种“波”实际存在。

“存在”这个词同样可以成为一个稳定记录。 但是一个词被写出来、一个定义合法、模型中有解、 某个现实对象已经被实现，是不同的事实。 理论的作用是说明它们怎样连接、在什么条件下连接， 并保留能够证明或推翻连接的证据。

因此，本轮可以正式提出：

> **概念的粒子性，是相对于观察分辨率的稳定可辨认性； 概念的关系性，是固定该读出后仍被保留的状态、比较和变化结构。 二者由同一个操作模型连接，但没有无条件的一一同义关系。**

这一表述可以继续推导和检验，也容纳“概念自身也是整体内部的一种对象” 这个递归观点，而无需宣称已经抵达人类知识或形式逻辑的终点。

<a id="section-A"></a>

## A　符号、类型与适用条件

| 记号 | 类型 | 适用说明 |
|:---|:---|:---|
| $X,X_{\rm adm},a$ | 经典配置、准入子集、指定锚点 | 三者不同；量子全态集不要求有限 |
| $q:X\to B$ | 确定读出 | 有效值为 $q(X)$，候选值可有空纤维 |
| $F_b,\mathcal B_q$ | 纤维、可判定 Boolean 代数 | 原子性相对于这个代数 |
| $\partial_q A$ | 混合标签集合 | 为零恰当于命题按完整纤维下降 |
| $R,A',B'$ | 对象–属性关系及双极 | 不预设内积、正交或相位 |
| $\mathcal H,d$ | 有限维复 Hilbert 空间及其维数 | 全部密度态通常不可数 |
| $P,Q$ | 正交投影，$Q=I-P$ | 主要分块结果取 $0<\operatorname{rank}P<d$ |
| $E,F$ | $\operatorname{ran}P,\operatorname{ran}Q$ 子空间 | 与一般效应符号按上下文区分 |
| $\operatorname{supp}A$ | 正算子的支撑子空间 | 不是投影；需取其正交投影才得到算子 |
| $A,B,C$ | 态的两个对角块及交叉块 | $C:F\to E$ |
| $p$ | $\operatorname{tr}(P\rho)$ | 概率不等于一次实际记录 |
| $\mathcal D_P,\mathcal E_P$ | 两种完全正压缩通道 | 前者保留块内态，后者只保留标签概率 |
| $\left\Vert \cdot\right\Vert _1$ | 迹范数 | $\left\Vert C\right\Vert _1$ 为奇异值之和 |
| $\left\Vert \cdot\right\Vert _2$ | Hilbert–Schmidt 范数 | $\left\Vert X\right\Vert _2^2=\operatorname{tr}(X^\dagger X)$ |
| $\mathcal V_P$ | 平衡比较菜单的最佳可见度 | 公式要求该菜单可访问 |
| $Z:E\to F$ | 概念的切向关系映射 | 不是当前态的 $C$，方向也相反 |
| $J_P,g_P,\omega_P$ | 复结构、度量、反对称形式 | 位于概念 Grassmann 切空间 |
| $\mathcal S_\infty$ | 允许序列效应的实线性闭包 | 一般不是 $`*`$-代数，也不是态空间 |
| $\Omega$ | 指定内部协议的有限历史态 | 不由形式单独确定自然宇宙 |

<a id="section-B"></a>

## B　当前项目来源与核对范围

本轮实际查询仓库 `the-omega-institute/trureturing`， 默认分支为 **dev**，固定提交为 `c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02`。 该提交的 committer 时间为 2026-11-07 19:00:25 UTC， 即 2026-11-08 03:00:25 新加坡时间。 核对时间为同日 03:06:18 新加坡时间。 这一快照不是把 `main` 分支重新命名为 dev， 也不保证此后仓库没有继续更新。

本轮只读获取并核对了 15 份相关文件的字节数和 SHA256： 5 篇主文、5 对 Lean／Blueprint。 5 对短模块已完整阅读；大主文只读限定相关段落并作限定关键词检索。 理论目录 API 返回 1000 项，存在列表上限， 所以未检索命中不构成全仓库不存在的证据。 **没有运行新的 Lean 构建，也没有递归审计全部导入依赖。**

| 来源 | 实际阅读范围 | 本稿采用及边界 |
|:---|:---|:---|
| 概念动力学主文[\[7\]](#ref-repoConcept) | 236–285；353–410；414–479 行 | 六层存在；概念为 $q_C:X\to B_C$；纤维分解。未将全部哲学命题视为已形式证明。 |
| 概念纤维分解模块[\[8\]](#ref-repoFibre) | Lean 与 Blueprint 全文 | 既有概念纤维分解；沿用其命题，不主张首创。 |
| 概念联合精化模块[\[8\]](#ref-repoFibre) | Lean 与 Blueprint 全文 | 联合读出的最小共同精化。 |
| 存在概念分离模块[\[10\]](#ref-repoExist) | Lean 与 Blueprint 全文 | 形成、构造、外加模型及实现谓词的具体分离见证。 |
| 直接像补集饱和模块[\[9\]](#ref-repoNeg) | Lean 与 Blueprint 全文 | 满射的像保持补集，当且仅当选集饱和；不要求有限性。 |
| 观察–形式概念接口[\[11\]](#ref-repoFCA) | Lean 与 Blueprint 全文 | 特定读出–取值 incidence 中单点闭包等于共同响应核。 |
| C-IRPT 重构主文[\[12\]](#ref-repoReconstruction) | 2015–2031 行 | 主文说明 kernel 商可能遗忘准入、锚点和坐标族；所引对应模块未在本轮下载核读或构建。 |
| AURIC $\Omega$ 静态相融纤维主文[\[13\]](#ref-repoOmega) | 7–23；127–145；289–320；4869–4875 行 | 量子表示为附加条件；响应商；记录重叠；跨块相位需要新增菜单。 |
| 相对门历史与观察商 V22[\[14\]](#ref-repoV22) | 1–45 行 | 作者范围中区分各类商，并要求未来预测闭包；未独立核读整篇证明。 |
| 存在量词与量子记录 V14[\[15\]](#ref-repoV14) | 1–35；635–673 行 | 区分存在聚合与相干抵消；只限定核读所指命题，未把任意概念视为射线。 |

其中否定源码 SHA256 为：

`20729c720209145c230f1feb8cca1be9cf6063e0d98e1936b57e8260ccd40b47`

$\Omega$ 主文与上一轮所读文件内容一致，SHA256 为：

`fbb2a0c6883ef447fb5585c5071dccc4d12bb6aabb9df2fda2e77d2fe6961d80`

本稿的量子正性纤维、可见度和动力学结果给出普通数学证明， 不冒称它们已经对应仓库中的机器验证声明。

## 参考来源

<a id="ref-otf1"></a>

\[1\] OTF-001． *正交时间场论：方向、转向、读出与内禀时钟* ， 版本 1.0，2026-11-07．本系列前稿；局部 qubit 表示、内生响应商及有限历史实现。

<a id="ref-otf2"></a>

\[2\] OTF-002． *正交时间场论：单态的轴面对偶与关联波* ， 版本 1.0，2026-11-08．本系列前稿；横向涨落核、态线、相位协议及定态关联。

<a id="ref-birkhoff"></a>

\[3\] G. Birkhoff and J. von Neumann.  *The Logic of Quantum Mechanics* . Annals of Mathematics 37(4), 823–843 (1936). [doi:10.2307/1968621](https://doi.org/10.2307/1968621)； [原论文扫描](https://gwern.net/doc/philosophy/logic/1936-birkhoff.pdf)。

<a id="ref-luders"></a>

\[4\] G. Lüders.  *Über die Zustandsänderung durch den Meßprozeß* . Ann. Phys. (Leipzig) 8, 322–328 (1951，惯用书目年份). K. A. Kirkpatrick 英译及讨论，Annalen der Physik 15(9), 663–670 (2006). [arXiv:quant-ph/0403007](https://arxiv.org/abs/quant-ph/0403007)， 核读 v2 的选择与非选择更新及兼容性讨论。

<a id="ref-ganter"></a>

\[5\] B. Ganter and R. Wille.  *Formal Concept Analysis: Mathematical Foundations* . Springer (1999), chapter  *Concept Lattices of Contexts* , pp. 17–61. [章节 DOI](https://doi.org/10.1007/978-3-642-59830-2_2)。 核读出版社预览第 17–18 页定义；本稿闭包证明独立写出。

<a id="ref-baumgratz"></a>

\[6\] T. Baumgratz, M. Cramer, and M. B. Plenio.  *Quantifying Coherence* . Physical Review Letters 113, 140401 (2014). [doi:10.1103/PhysRevLett.113.140401](https://doi.org/10.1103/PhysRevLett.113.140401)； [作者全文 arXiv:1311.0275v3](https://arxiv.org/html/1311.0275v3)。

<a id="ref-repoConcept"></a>

\[7\] `FORMAL_CONCEPT_DYNAMICS.md`. 固定 dev 提交 `c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02`。 [项目主文原文](https://github.com/the-omega-institute/trureturing/blob/c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02/docs/develop/theory/FORMAL_CONCEPT_DYNAMICS.md)。

<a id="ref-repoFibre"></a>

\[8\] `D5/S3/ConceptDynamics/ConceptFiberDecomposition.lean`； `ConceptJoinUniversal.lean` 及各自 Blueprint。 [固定提交中的纤维模块](https://github.com/the-omega-institute/trureturing/blob/c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02/D5/S3/ConceptDynamics/ConceptFiberDecomposition.lean)； [联合精化模块](https://github.com/the-omega-institute/trureturing/blob/c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02/D5/S3/ConceptDynamics/ConceptJoinUniversal.lean)。

<a id="ref-repoNeg"></a>

\[9\] `D5/S3/ConceptDynamics/Negation/DirectImageComplementSaturation.lean`， 声明 `image_complement_iff_saturated`。 [固定提交中的源码](https://github.com/the-omega-institute/trureturing/blob/c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02/D5/S3/ConceptDynamics/Negation/DirectImageComplementSaturation.lean)。

<a id="ref-repoExist"></a>

\[10\] `D5/S3/ConceptDynamics/ExistenceNotionSeparation.lean`. [固定提交中的源码](https://github.com/the-omega-institute/trureturing/blob/c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02/D5/S3/ConceptDynamics/ExistenceNotionSeparation.lean)。

<a id="ref-repoFCA"></a>

\[11\] `D5/S3/ConceptDynamics/ObservationFormalConceptAdapter.lean`. [固定提交中的源码](https://github.com/the-omega-institute/trureturing/blob/c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02/D5/S3/ConceptDynamics/ObservationFormalConceptAdapter.lean)。

<a id="ref-repoReconstruction"></a>

\[12\] `CIRPT_FORMAL_CONCEPT_DYNAMICS_RECONSTRUCTION.md`，第 45 节。 [固定提交中的原文](https://github.com/the-omega-institute/trureturing/blob/c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02/docs/develop/theory/CIRPT_FORMAL_CONCEPT_DYNAMICS_RECONSTRUCTION.md)。

<a id="ref-repoOmega"></a>

\[13\] `AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md`， 第 1.3、4.1、82.5 项及记录重叠段。 [固定提交中的原文](https://github.com/the-omega-institute/trureturing/blob/c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。

<a id="ref-repoV22"></a>

\[14\] `AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md`.  *相对门历史与观察商：AURIC 的共同背景消去、关系核与递归闭合* ， v22.0，2026-10-30。 [本轮固定提交中的原文](https://github.com/the-omega-institute/trureturing/blob/c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)。 仅核读第 1–45 行；文中自述历史快照与本轮快照不同。

<a id="ref-repoV14"></a>

\[15\] `AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14.md`.  *AURIC 存在量词、电路半环与量子记录* ，v14.0，2026-10-29。 [本轮固定提交中的原文](https://github.com/the-omega-institute/trureturing/blob/c1aaff1cc4c5e0f15705cf9047d0ee57c0a79b02/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14.md)。 仅核读第 1–35、635–673 行。

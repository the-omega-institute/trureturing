# 候选 N2：共享历史充分性

遗漏关系的三维见证、最小内部补足与维数预算

AURIC v78 后续研究：定义、定理与证明

研究续稿

2026 年 11 月 2 日

## 摘要

本轮只推进一个候选：一个内部参照若被称为两翼的完整共享历史，
它必须解释完两翼的全部交叉幅度；扣除共同部分后，剩余两翼应当正交。
该条件不由“全部对象属于 $\Omega$”单独推出，而被精确定义为共享描述的充分性。

承接项目既有共同复正核、Schur 余核与三记录补全圆盘，
本轮集中证明一个补足问题：保持实际整体的全部关系不变，
只扩大共享参照，最少需要纳入多少个已经存在的相干方向？
令两翼残差空间为 $E_A,E_C$，$T=P_{E_A}|_{E_C}$，
残差交叉 Gram 块为 $Y$，则最少新增共享复维数恰为
$r=\operatorname{rank}  T=\operatorname{rank}  Y$，并可取 $U=\operatorname{ran}  T\subseteq E_A$。
任意 $m$ 维共享预算的最优剩余二元缺陷恰为 $\sigma_{m+1}(T)$；
该缺陷始终按原输入范数计量。

每个奇异模式是一对内部历史的三维关系读口 $(\sigma_\ell,0,0)$。
在已有相位控制与二端口比较可用时，它沿相位参数画圆，
经固定线性读出给椭圆及周期信号。所有结论均给解析证明；
标准投影、块正性和低秩逼近按既有工具归属。
本轮没有重新申请共同复结构、Born 读出或已完成的模型分类，
也不将数学共享空间的补足自动解释成新增物理控制权限。

## 目录

- [1. 唯一候选及其在项目中的位置](#section-1)
- [2. 先反过来：不满足时，究竟哪两个元出问题](#section-2)
- [3. 二元关系归一后，缺口在三维球里有确定位置](#section-3)
- [4. 更大的结构：两张局部正核怎样组成整体](#section-4)
- [5. 把表格变成内在关系：遗漏模式不依赖坐标](#section-5)
- [6. 主定理：最少补入多少已有方向，共享历史才完整](#section-6)
- [7. 有限预算：只补若干方向，最少还会漏多少](#section-7)
- [8. 每个遗漏模式的圆、周期和椭圆读出](#section-8)
- [9. 解析反例：共同来源不能替代实际跨翼关系](#section-9)
- [10. 把公理锁成定义约束：本轮真正完成了什么](#section-10)

<a id="section-1"></a>

## 1. 唯一候选及其在项目中的位置

### 1.1 候选 N2 的完整陈述

> **共享历史充分性。**
> 在同一内部量子关系截口中，若一个共享参照被定义为两翼的完整共同历史，
> 则两翼的全部交叉幅度应由它们在该共享空间中的投影决定。
> 若扣除该部分以后仍有跨翼关系，这项关系就是尚未计入共享描述的内部内容。
> 有限截口中应能用已有相干方向将共享描述补足，
> 并由残差关系自身确定最少补足维数和有限预算下的不可消去缺陷。

这里的“应”在后文被拆成两种严格地位：
完整共享描述由一个投影等式*定义*；
内部补足的存在性、最小维数和误差预算则是*定理*。
证明完成后，N2 可以从待加公理表移入既有量子表示的内部闭合结果。
它没有要求任意选取的参照空间都已充分。

### 1.2 保留已有供应，定位本轮增量

本轮公开仓库固定于提交

`aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e`。

该快照已收录前轮《已证结构的内生闭合》[6](#ref-closure)。
下表来自相关理论文件的定向核读，不作为全库或外部文献优先权认证。

| 已有位置 | 已证内容 | 本轮如何使用 |
| --- | --- | --- |
| V63 §5，定理 5.2--5.3 | 共享锚的 Schur 余核、正性与秩；来源唯一不迫使残差为零 | 直接使用投影残差 |
| Hidden Relations §9，C-9.2、C-9.5 | 三记录补全圆盘、逐参考 Schur 更新、奇异支撑条件 | 作为最小图像与块推导的既有工具 |
| V71 §6；V72 §6 | 奇异 Schur 判据、来源锚定的正交余核及历史接续 | 保留冗余历史和零方向 |
| V77；前轮内生闭合稿 | 全部合成二元测试、共同复结构、事件效果、线性分支与结果核树 | 不重新列为未解决起点 |
| 前轮候选 N1[8](#ref-n1) | 相干桥的整体无损条件与误差传播 | 本轮转向共同参照是否解释完关系 |

可复核位置见文献[1](#ref-v63)、[2](#ref-hidden)、[3](#ref-v71)、[4](#ref-v72)、[5](#ref-v77)、[6](#ref-closure)。
此前声明模型类中的复结构选择仍按 Atlas 的合同保留[7](#ref-atlas)。

**本轮具体增量**是：在*已经给定的实际全局核*上，
将“还漏了多少共同关系”变成最小共享维数 $\operatorname{rank}  Y$，
并给出所有维数预算的精确最优误差 $\sigma_{m+1}(T)$。
投影、正矩阵补全和奇异值截断属于标准工具；
相关经典来源见[9](#ref-grone)、[10](#ref-eckart)。此处贡献是它们在内部共享定义下的完整接合，
不宣称这些线性代数工具首次出现。

**白话图景。**前面已经建立了共同复关系、读出和历史接续，这些继续保留。
现在只问：两边明明还有关联，我们记录的“共同历史”是否漏了一部分？
如果漏了，就在原来的整体里把那部分找出来，明确要补多少，
而不是再从外面加一条“它们一定独立”的要求。

<a id="section-2"></a>

## 2. 先反过来：不满足时，究竟哪两个元出问题

<a id="statement-2-1"></a>

#### 定义 2.1（同一内部截口及共享参照）

在项目已有的共同复正核表示中，取有限历史族
$\mathcal A=\{a_i\}$、$\mathcal B=\{b_j\}$、$\mathcal C=\{c_k\}$。
以 $\mathscr H$ 表示它们所在的内部相干空间，内积对第二变量线性。
令

$$
S=\operatorname{span} \mathcal B,\qquad P_S\text{ 为 }S\text{ 上的正交投影},
$$

$$
E_A=\operatorname{span} \{(I-P_S)a_i\},\qquad
E_C=\operatorname{span} \{(I-P_S)c_k\}.
$$

共享指同一批参考关系被两份描述共同保留；
它不自动表示两翼原有空间的集合交集，也不额外指定共同因果过去。

这些向量及其相干组合使用既有表示，不重新假定一个来自 $\Omega$ 外的空间。
有限性仅限当前所讨论的关系截口，不要求整个 $\Omega$ 有限维。

<a id="statement-2-2"></a>

#### 定义 2.2（幅度关系的共享充分性）

对 $a\in\operatorname{span} \mathcal A$、$c\in\operatorname{span} \mathcal C$，定义共享缺陷

<a id="eq-defect"></a>

$$
D_S(a,c)
=\langle a,c\rangle -\langle P_Sa,P_Sc\rangle 
=\langle (I-P_S)a,(I-P_S)c\rangle .\tag{2.1}
$$

若对两翼全部 $a,c$ 都有 $D_S(a,c)=0$，
称 $S$ 对这两翼的幅度关系**共享充分**。

式 [(2.1)](#eq-defect) 由正交分解直接得到：交叉项
$\langle P_Sa,(I-P_S)c\rangle$ 与 $\langle (I-P_S)a,P_Sc\rangle$ 都为零。
因此定义的内容恰是

<a id="eq-sufforth"></a>

$$
\boxed{S\text{ 共享充分}\quad\Longleftrightarrow\quad E_A\perp E_C.}\tag{2.2}
$$

由于缺陷对第一变量共轭线性、对第二变量线性，
检验原有限历史族的全部跨翼条目已经足够。

<a id="statement-2-3"></a>

#### 命题 2.3（遗漏关系的二元干涉见证）

若 $S$ 不充分，存在 $x\in E_A,y\in E_C$ 使
$h=\langle x,y\rangle \ne0$。
取 $\phi=\arg h$ 及 $\widetilde y=e^{-i\phi}y$，则

<a id="eq-interference"></a>

$$
\boxed{\left\lVert x+\widetilde y\right\rVert ^{2}-\left\lVert x-\widetilde y\right\rVert ^{2}=4|h|>0.}\tag{2.3}
$$

若该二端口比较属于已有可用读口，令
$s=\left\lVert x\right\rVert ^2+\left\lVert y\right\rVert ^2$，其两个返回概率为

<a id="eq-prob"></a>

$$
p_\pm=\frac{\left\lVert x\pm\widetilde y\right\rVert ^{2}}{2s}
=\frac12\pm\frac{|h|}{s}.\tag{2.4}
$$

**证明。**

不充分即某对残差内积非零。
相位选择令 $\langle x,\widetilde y\rangle =|h|$，展开两个范数平方即得。
Cauchy--Schwarz 与 $2\left\lVert x\right\rVert \left\lVert y\right\rVert \le s$ 保证 $p_\pm\in[0,1]$，
且两者之和为一。

□

反向推理至此已经定位了两个元：它们是**两侧扣除共享部分后的残差** $x,y$。
忽略 $h$ 会把式 [(2.4)](#eq-prob) 错写成两个 $1/2$。
该失败不表示实际整体不合法，而表示所选共享描述遗漏了仍可相干比较的内容。

**白话图景。**先从左右两条历史里扣掉已经写进共同记录的部分。
如果剩下的两段还能一加变亮、一减变暗，它们之间就还藏着关系。
这两个残差就是反例的两个元。此时要修的是“共同记录已经完整”这句话，
不是把本来存在的干涉从整体中抹掉。

<a id="section-3"></a>

## 3. 二元关系归一后，缺口在三维球里有确定位置

<a id="statement-3-1"></a>

#### 定义 3.1（二元关系的三维读口）

对 $x,y$，令 $s=\left\lVert x\right\rVert ^2+\left\lVert y\right\rVert ^2>0$，定义

<a id="eq-ball"></a>

$$
\rho_{x:y}=\frac1s
\begin{pmatrix}
\left\lVert x\right\rVert ^2&\overline{\langle x,y\rangle }\\
\langle x,y\rangle &\left\lVert y\right\rVert ^2
\end{pmatrix},\qquad
\mathbf r(x,y)=
\left(
\frac{2\operatorname{Re}\langle x,y\rangle }{s},
\frac{2\operatorname{Im}\langle x,y\rangle }{s},
\frac{\left\lVert x\right\rVert ^2-\left\lVert y\right\rVert ^2}{s}
\right).\tag{3.1}
$$

这里 $\rho_{x:y}$ 是通常 Gram 矩阵的转置归一化，
与此前二端口约定一致；采用标准 Pauli 三轴时其坐标正是 $\mathbf r$。

<a id="statement-3-2"></a>

#### 命题 3.2（合法性与共享充分性是球里的两个不同判断）

记 $\mathbf r=(X_2,Y_2,Z_2)$，则

<a id="eq-ballnorm"></a>

$$
X_2^2+Y_2^2+Z_2^2
=1-\frac{4(\left\lVert x\right\rVert ^2\left\lVert y\right\rVert ^2-|\langle x,y\rangle |^2)}{s^2}\le1.\tag{3.2}
$$

对真实残差对，$\langle x,y\rangle =0$ 当且仅当 $X_2=Y_2=0$。
不要求 $Z_2=0$，因为两侧残差的大小可以不同。
$s=0$ 时两者皆为零，直接判定无缺陷，无须归一化。

**证明。**

展开三坐标的平方和，得到等式；不等式为 Cauchy--Schwarz。
两个横向坐标正是交叉幅度的实部和虚部，故给最后的等价。

□

三维坐标保留一对关系的形状，$s$ 保留其尺度。
不能将丢掉尺度后的球内点当成全部信息，也不能将整个 $\Omega$ 压成三维。
球面饱和等价于这一对向量线性相关；球内点的“混合性”只属于该二元读口。

### 3.1 单个共享历史留下的整个补全圆盘

给三个单位历史 $a,b,c$，记

$$
\alpha=\langle a,b\rangle ,\qquad \beta=\langle b,c\rangle ,\qquad \gamma=\langle a,c\rangle .
$$

取 $S=\operatorname{span} \{b\}$。残差范数平方为
$A_0=1-|\alpha|^2$、$C_0=1-|\beta|^2$，
残差内积为 $\gamma-\alpha\beta$。
于是已知 $\alpha,\beta$ 的全部合法 $\gamma$ 恰为

<a id="eq-disk"></a>

$$
\boxed{|\gamma-\alpha\beta|^2
\le(1-|\alpha|^2)(1-|\beta|^2).}\tag{3.3}
$$

必要性是 Cauchy--Schwarz；充分性可以在参考方向之外取两个残差向量实现该二阶正核。
若任一残差范数为零，圆盘退化成 $\gamma=\alpha\beta$。
这就是项目 Hidden Relations 命题 C-9.2 的等价记号[2](#ref-hidden)，不是本轮新定理。

圆心 $\gamma=\alpha\beta$ 对应 $S$ 共享充分。
圆盘中其他点同样可以合法存在，只是这一个参考还不足以解释所有跨翼关系。

**白话图景。**每一对剩余历史都能画进同一个三维关系球。
横向两轴记录“它们还怎样相干”，竖轴记录“两边还各剩多少”。
共同记录完整时，横向关系消失；两边剩余量不必一样。
如果只知道各自与一个参考的关系，中间仍留着一整片圆盘的可能，
说明“同一个来源”没有自动选定全部交叉关系。

<a id="section-4"></a>

## 4. 更大的结构：两张局部正核怎样组成整体

本节把已有的投影残差写成块形式，用来精确区分
“只给两张局部表”与“已经给定实际整体”。

<a id="statement-4-1"></a>

#### 定义 4.1（局部核与待定交叉块）

给两张在同一共享块上相同的正核

$$
K_{AB}=\begin{pmatrix}G_A&P\\P^\dagger&G_B\end{pmatrix}\succeq0,
\qquad
K_{BC}=\begin{pmatrix}G_B&Q\\Q^\dagger&G_C\end{pmatrix}\succeq0.
$$

令

<a id="eq-schur"></a>

$$
S_A=G_A-PG_B^+P^\dagger,\qquad
S_C=G_C-Q^\dagger G_B^+Q,\tag{4.1}
$$

其中 $G_B^+$ 为 Moore--Penrose 逆，允许 $G_B$ 奇异。
候选全局核与剩余交叉块为

<a id="eq-blocks"></a>

$$
K(X)=\begin{pmatrix}
G_A&P&X\\P^\dagger&G_B&Q\\X^\dagger&Q^\dagger&G_C
\end{pmatrix},\qquad Y=X-PG_B^+Q.\tag{4.2}
$$

<a id="statement-4-2"></a>

#### 定理 4.2（全部补全的收缩参数式）

上述局部正性保证 $S_A,S_C\succeq0$，且

<a id="eq-allcompletions"></a>

$$
\boxed{K(X)\succeq0
\quad\Longleftrightarrow\quad
X=PG_B^+Q+S_A^{1/2}WS_C^{1/2},\quad\left\lVert W\right\rVert \le1.}\tag{4.3}
$$

规范地取
$W:\operatorname{ran}  S_C\to\operatorname{ran}  S_A$ 并在零空间上作零延拓时，
每个合法交叉块对应唯一的

<a id="eq-whiten"></a>

$$
W=S_A^{+1/2}YS_C^{+1/2}.\tag{4.4}
$$

若不限制支撑，完整尺寸的 $W$ 在零方向上可不唯一。

**证明。**

令 $\Pi_B=G_BG_B^+$。
若 $z\in\ker G_B$，局部正核在向量 $(u,tz)$ 上的二次式须对一切
$t\in\mathbb C$ 非负。变化 $t$ 的模长和相位强迫 $Pz=0$。
另一局部核同理给

$$
P=P\Pi_B,\qquad Q=\Pi_BQ.
$$

对可逆块三角矩阵

$$
L=\begin{pmatrix}
I&-PG_B^+&0\\0&I&0\\0&-Q^\dagger G_B^+&I
\end{pmatrix}
$$

作合同变换，得到

$$
LK(X)L^\dagger=
\begin{pmatrix}
S_A&0&Y\\0&G_B&0\\Y^\dagger&0&S_C
\end{pmatrix}.
$$

局部两块的同一变换先给 $S_A,S_C\succeq0$；
全局正性则等价于

<a id="eq-residualblock"></a>

$$
\begin{pmatrix}S_A&Y\\Y^\dagger&S_C\end{pmatrix}\succeq0.\tag{4.5}
$$

零方向的相同论证强迫
$Y=\Pi_A Y\Pi_C$，其中 $\Pi_A,\Pi_C$ 为两残差块的支撑投影。
在支撑上用正平方根作可逆合同变换，式 [(4.5)](#eq-residualblock) 等价于

$$
\begin{pmatrix}I&W\\W^\dagger&I\end{pmatrix}\succeq0.
$$

其二次式可写成

$$
\left\lVert u+Wv\right\rVert ^2+\langle v,(I-W^\dagger W)v\rangle .
$$

因此正性等价于 $I-W^\dagger W\succeq0$，即 $\left\lVert W\right\rVert \le1$。
支撑上的平方根可逆，又给唯一性和式 [(4.4)](#eq-whiten)。

□

这是标准正块矩阵与 Schur 方法在当前接口的直接使用[3](#ref-v71)、[2](#ref-hidden)、[9](#ref-grone)。
其意义是：两张局部表并没有遗漏一个可随意忽略的标量，
而是留下了整个收缩算子 $W$ 的自由度。

<a id="statement-4-3"></a>

#### 推论 4.3（无额外跨翼残差关联的唯一补全）

在全部匹配局部表的补全中，要求两翼残差正交恰好选择

$$
Y=0,\qquad W=0,\qquad X=PG_B^+Q.
$$

这是该条件下唯一的交叉块；不能仅由局部表相同就强制实际整体采用它。

本节分类的是正核表。若另行固定实现空间只有 $d$ 维，
仍须保留 $\operatorname{rank}  K(X)\le d$；正性本身不取消该维数要求。
下一节起直接固定已经实现的整体，不再从补全集里另选一个整体。

**白话图景。**两边都承认同一份共同记录，只能说明它们在共同部分没有冲突。
共同部分以外，还可能有许多成组的相干关系。
把这些关系收在一个算子里，就看清了大结构：每一种合法整体，
都是“共同部分已经解释的关系”加上“一组合法的剩余关系”。
零剩余是一种有明确含义的选择，不是未知信息的默认值。

<a id="section-5"></a>

## 5. 把表格变成内在关系：遗漏模式不依赖坐标

现在固定*实际*全局核及其共同实现，不再变化交叉块 $X$。
取历史列映射

$$
F_A:\mathbb C ^{n_A}\to\mathscr H,\quad
F_B:\mathbb C ^{n_B}\to\mathscr H,\quad
F_C:\mathbb C ^{n_C}\to\mathscr H,
$$

使 $G_A=F_A^\dagger F_A$、$G_B=F_B^\dagger F_B$、$G_C=F_C^\dagger F_C$，
$P=F_A^\dagger F_B$、$Q=F_B^\dagger F_C$、$X=F_A^\dagger F_C$。
于是

<a id="eq-columns"></a>

$$
P_S=F_BG_B^+F_B^\dagger,\qquad
A_0=(I-P_S)F_A,\qquad C_0=(I-P_S)F_C,\tag{5.1}
$$

<a id="eq-colgram"></a>

$$
A_0^\dagger A_0=S_A,\quad
C_0^\dagger C_0=S_C,\quad
A_0^\dagger C_0=Y.\tag{5.2}
$$

投影公式可在 $F_B$ 的非零奇异方向上逐一验证：
对应非零平方根由 $G_B^+$ 抵消，零方向消去。
故它在冗余共享历史存在时仍是正交投影。

<a id="statement-5-1"></a>

#### 定义 5.1（残差间的内在关联算子）

定义

<a id="eq-T"></a>

$$
\boxed{T=P_{E_A}|_{E_C}:E_C\to E_A.}\tag{5.3}
$$

它把右侧剩余历史在左侧剩余空间中的分量取出来。
由于是正交投影的限制，$\left\lVert T\right\rVert \le1$。

<a id="statement-5-2"></a>

#### 定理 5.2（支撑等距与内在奇异模式）

令

$$
J_A=A_0S_A^{+1/2}:\operatorname{ran}  S_A\to E_A,\qquad
J_C=C_0S_C^{+1/2}:\operatorname{ran}  S_C\to E_C.
$$

下文也将 $J_A,J_C$ 视为取值于共同 $\mathscr H$ 的部分等距：
在系数零空间上作零延拓；其伴随作用于全部 $\mathscr H$，
并消去各自像空间的正交补。
两者在所标支撑上的限制均为等距同构，且

<a id="eq-isometry"></a>

$$
W=J_A^\dagger T J_C,\qquad
T=J_AWJ_C^\dagger|_{E_C}.\tag{5.4}
$$

特别地，$W$ 与 $T$ 的非零奇异值相同，并且

<a id="eq-rank"></a>

$$
\boxed{\operatorname{rank}  Y=\operatorname{rank}  W=\operatorname{rank}  T=:r.}\tag{5.5}
$$

**证明。**

由式 [(5.2)](#eq-colgram)，

$$
J_A^\dagger J_A=S_A^{+1/2}S_AS_A^{+1/2}=\Pi_A,
\qquad J_AJ_A^\dagger=P_{E_A}.
$$

第一式给支撑上的等距性，第二式由像空间等于 $E_A$ 得到；$J_C$ 同理。
于是 $A_0=J_AS_A^{1/2}$、$C_0=J_CS_C^{1/2}$，从而

$$
Y=S_A^{1/2}J_A^\dagger J_CS_C^{1/2},\qquad
W=J_A^\dagger J_C=J_A^\dagger T J_C.
$$

两侧等距同构给第二个表示式及奇异值一致性。
在各自支撑上，$S_A^{1/2},S_C^{1/2}$ 可逆，所以它们不改变 $W$ 的秩。

□

**秩与强度须分清。**
遗漏模式的*个数*可以直接用 $\operatorname{rank}  Y$；
模式*强度*应取 $T$ 或支撑归一后的 $W$ 的奇异值。
一般不能拿未经归一的 $Y$ 的奇异值替代它，因为重标历史向量会改变后者。
这些结论也保证添加冗余标签、换基或对共同实现作酉变换不会改变内在答案。

**白话图景。**同一张关系表换一套坐标，不应该改变“究竟漏了几种关系”。
所以先扣共同部分，再按各侧自身的尺度归一。
留下的算子就只描述左、右剩余方向之间真正的夹合关系。
它的秩数遗漏的独立模式，奇异值数各模式有多强。

<a id="section-6"></a>

## 6. 主定理：最少补入多少已有方向，共享历史才完整

<a id="statement-6-1"></a>

#### 定义 6.1（内部补足及原尺度缺陷）

令
$\mathscr H_{\rm loc}=S+\operatorname{span} \mathcal A+\operatorname{span} \mathcal C$。
选内部子空间
$U\subseteq\mathscr H_{\rm loc}\cap S^\perp$，将共同参照扩为
$S'=S\oplus U$。
原始历史向量和全部原始内积保持固定。
定义

<a id="eq-RU"></a>

$$
R_U=P_{E_A}(I-P_U)|_{E_C}
=T-P_{E_A}P_U|_{E_C}.\tag{6.1}
$$

对 $x\in E_A,y\in E_C$，正交投影的自伴性与幂等性给

<a id="eq-RUform"></a>

$$
\langle x,R_Uy\rangle 
=\langle (I-P_U)x,(I-P_U)y\rangle .\tag{6.2}
$$

所以 $S'$ 对原两翼共享充分当且仅当 $R_U=0$。
当两个残差空间均非零时，

<a id="eq-RUmeasure"></a>

$$
\left\lVert R_U\right\rVert 
=\sup_{\substack{x\in E_A,\,y\in E_C\\\left\lVert x\right\rVert =\left\lVert y\right\rVert =1}}
\left|\langle (I-P_U)x,(I-P_U)y\rangle \right|.\tag{6.3}
$$

任一残差空间为零时，此缺陷直接定义为零。
式 [(6.3)](#eq-RUmeasure) 使用**原残差输入的单位尺度**，不把投影后的微小残差重新放大。

<a id="statement-6-2"></a>

#### 定理 6.2（最小内部共享补足）

令 $r=\operatorname{rank}  T=\operatorname{rank}  Y$。则

<a id="eq-minimal"></a>

$$
\boxed{
\min\{\dim_{\mathbb C }U:\ U\subseteq\mathscr H_{\rm loc}\cap S^\perp,
\ R_U=0\}=r.
}\tag{6.4}
$$

一个达到最小值的内部选择是

<a id="eq-Ustar"></a>

$$
\boxed{U_*=\operatorname{ran}  T\subseteq E_A.}\tag{6.5}
$$

**证明。**

先证任何补足都不能更小。
若 $R_U=0$，由式 [(6.1)](#eq-RU)，

$$
T=P_{E_A}P_U|_{E_C}.
$$

右侧的秩不超过 $\dim U$，所以 $r\le\dim U$。
等价地，$Y=A_0^\dagger P_U C_0$ 也立即给同一下界。

再证该下界可由旧内部方向达到。
取 $U_*=\operatorname{ran}  T$，则 $U_*\subseteq E_A\subseteq S^\perp$，且 $\dim U_*=r$。
对于 $y\in E_C$，$Ty$ 已在 $U_*$ 中，故

$$
R_{U_*}=T-P_{U_*}T=0.
$$

这里使用 $P_{E_A}P_{U_*}|_{E_C}=P_{U_*}T$，
它由 $U_*\subseteq E_A$ 得到。于是该选择既充分又最小。

□

<a id="statement-6-3"></a>

#### 推论 6.3（补足后整体的正交结构）

取 $S'=S\oplus U_*$，
$E'_A=(I-P_{U_*})E_A$、$E'_C=(I-P_{U_*})E_C$，则

<a id="eq-orthogonalsum"></a>

$$
\boxed{\mathscr H_{\rm loc}=S'\oplus E'_A\oplus E'_C}\tag{6.6}
$$

为正交直和。它只重组同一个内部空间，没有增加总载体的方向。

**证明。**

两个新残差空间均正交于 $S'$；由定理，二者彼此正交。
因为 $U_*\subseteq E_A$，拆分原两翼的各个向量后仍张成原来的
$S+E_A+E_C=\mathscr H_{\rm loc}$。

□

### 6.1 新增参照怎样由旧历史显式写出

若 $\xi_\ell$ 为 $W$ 的一个非零左奇异方向，对应新增方向为

<a id="eq-internalvector"></a>

$$
u_\ell=J_A\xi_\ell
=\bigl(F_A-F_BG_B^+P^\dagger\bigr)S_A^{+1/2}\xi_\ell.\tag{6.7}
$$

它是旧 $A$、旧 $B$ 历史的相干线性组合。
把该方向列为共同参照时，右翼与它的关系条目也取自原完整核，
不准另行编写。$U_*$ 一般不在 $E_A\cap E_C$ 中；
本定理允许把已有内部方向纳入两份描述的共同参照。
若额外限制新方向必须原先就属于两翼交集，结论会改变。

**白话图景。**现在有了真正的内生补足：看右边剩余的东西究竟碰到了左边哪些方向，
把这些方向列入共同记录就够了。
它们本来就在整体里，公式还明确告诉我们怎样由旧历史组合得到。
遗漏关系若有 $r$ 个独立模式，就必须补 $r$ 个复方向；
少一个，就至少还有一种跨越两边的关系没有被共同记录解释。

<a id="section-7"></a>

## 7. 有限预算：只补若干方向，最少还会漏多少

将 $T$ 的非零奇异值按大小排列：

$$
1\ge\sigma_1\ge\cdots\ge\sigma_r>0,
\qquad \sigma_k=0\quad(k>r).
$$

取相应正交单位方向 $u_\ell\in E_A,v_\ell\in E_C$，使

$$
Tv_\ell=\sigma_\ell u_\ell,\qquad
T=\sum_{\ell=1}^{r}\sigma_\ell|u_\ell\rangle \langle v_\ell|.
$$

<a id="statement-7-1"></a>

#### 定理 7.1（维数预算的精确最优缺陷）

对任意整数 $m\ge0$，

<a id="eq-budget"></a>

$$
\boxed{
\min_{\substack{U\subseteq\mathscr H_{\rm loc}\cap S^\perp\\\dim_{\mathbb C }U\le m}}
\left\lVert R_U\right\rVert =\sigma_{m+1}(T).
}\tag{7.1}
$$

最优值由前 $\min(m,r)$ 个左奇异方向张成的
$U_m$ 达到。下界对允许处在更大内部环境中的任意 $m$ 维 $U\subseteq S^\perp$ 也成立。

**证明。**

任意这样的 $U$ 给

$$
R_U=T-B_U,\qquad B_U=P_{E_A}P_U|_{E_C},\qquad \operatorname{rank}  B_U\le m.
$$

若 $m<r$，考虑 $m+1$ 维空间
$L_m=\operatorname{span} \{v_1,\ldots,v_{m+1}\}$。
秩上界保证其中存在单位向量 $v$ 满足 $B_Uv=0$。
写 $v=\sum_{\ell\le m+1}c_\ell v_\ell$，则

$$
\left\lVert R_Uv\right\rVert ^2=\left\lVert Tv\right\rVert ^2
=\sum_{\ell\le m+1}\sigma_\ell^2|c_\ell|^2
\ge\sigma_{m+1}^2.
$$

从而 $\left\lVert R_U\right\rVert \ge\sigma_{m+1}$。
若 $m\ge r$，零为直接下界。

反向取 $U_m=\operatorname{span} \{u_1,\ldots,u_{\min(m,r)}\}$。
因为 $U_m\subseteq E_A$，

$$
R_{U_m}=(I-P_{U_m})T
=\sum_{\ell>m}\sigma_\ell|u_\ell\rangle \langle v_\ell|,
$$

其范数恰为 $\sigma_{m+1}$。下界达到。

□

这是奇异值截断的标准低秩逼近机制在共享参照问题上的精确实现[10](#ref-eckart)。
它不只证明“存在一种不错的补法”：任何同维补法都不能把最大剩余缺陷降得更低。
当奇异值并列时最优参照可以不唯一，最优误差仍唯一。

<a id="statement-7-2"></a>

#### 推论 7.2（容许误差决定有效共享维数）

给 $\varepsilon\ge0$，使 $\left\lVert R_U\right\rVert \le\varepsilon$ 所需最少维数为

<a id="eq-epsilonrank"></a>

$$
\boxed{r_\varepsilon=\#\{\ell:\sigma_\ell(T)>\varepsilon\}.}\tag{7.2}
$$

**证明。**

式 [(7.1)](#eq-budget) 说明 $m$ 可行当且仅当
$\sigma_{m+1}\le\varepsilon$。恰好保留所有严格大于阈值的模式即给最小 $m$。

□

### 7.1 保留尺度，避免把小缺口重新放大

取正交单位 $e_1,e_2$，令
$E_A=\operatorname{span} \{e_1,e_2\}$、
$E_C=\operatorname{span} \{\sqrt{1-\eta^2}\,e_1+\eta e_2\}$，$0<\eta<1$。
若补入 $U=\operatorname{span} \{e_1\}$，右残差为 $\eta e_2$，式 [(6.3)](#eq-RUmeasure) 的缺陷为 $\eta$。
把该残差重新归一成 $e_2$ 后，与左侧 $e_2$ 的相关系数却等于一。
后者使用不同尺度，不是式 [(7.1)](#eq-budget) 衡量的量。
因此二元三维读口要与残差大小一起保存，不能让归一化遮住误差。

**白话图景。**如果共同记录只能再容纳几个方向，就先收下最强的几种遗漏关系。
补了前 $m$ 种以后，最强的剩余关系正好是第 $m+1$ 个奇异值，
任何别的同维安排都无法把这个最坏缺口压得更小。
很小的剩余量也仍可能方向完全一致，所以既要看球里的方向，
也要保留它到底还剩多少。

<a id="section-8"></a>

## 8. 每个遗漏模式的圆、周期和椭圆读出

<a id="statement-8-1"></a>

#### 命题 8.1（独立模式的二元三维证书）

对上述奇异方向，有

<a id="eq-modepair"></a>

$$
\langle u_\ell,v_k\rangle =\sigma_k\delta_{\ell k}.\tag{8.1}
$$

特别地，每个非零模式的归一二元关系为

<a id="eq-modeball"></a>

$$
\rho_\ell=\frac12\begin{pmatrix}1&\sigma_\ell\\\sigma_\ell&1\end{pmatrix},
\qquad
\boxed{\mathbf r_\ell=(\sigma_\ell,0,0).}\tag{8.2}
$$

**证明。**

$u_\ell\in E_A$，所以
$\langle u_\ell,v_k\rangle =\langle u_\ell,P_{E_A}v_k\rangle  =\langle u_\ell,Tv_k\rangle =\sigma_k\delta_{\ell k}$。
双方范数均为一，代入式 [(3.1)](#eq-ball) 即得。

□

这把“关系的关系”分解成有限多个互不交叉的二元模式。
还可记 $\vartheta_\ell=\arccos\sigma_\ell$，
它是相位对齐后这一对单位历史方向的夹角。
将 $u_\ell$ 补入共享参照后，该左残差变成零，此模式的交叉幅度被共享部分全部承担。
N2 检查的是去掉共享后还剩什么，其通过值是零交叉幅度；
这与 N1 检查原过程是否保住相干属于不同问题，不能给球半径普遍的好坏含义。

<a id="statement-8-2"></a>

#### 命题 8.2（固定模式的相位圆与固定读口的椭圆）

在已有两端口相干比较与相对相位控制可用时，对一个模式取

$$
|\Psi_\theta\rangle 
=\frac{|0\rangle \otimes u_\ell+e^{i\theta}|1\rangle \otimes v_\ell}{\sqrt2}.
$$

对历史部分取读口约化，得到

<a id="eq-phasecircle"></a>

$$
\rho_\ell(\theta)=\frac12
\begin{pmatrix}1&\sigma_\ell e^{-i\theta}\\
\sigma_\ell e^{i\theta}&1\end{pmatrix},\qquad
\mathbf r_\ell(\theta)=
(\sigma_\ell\cos\theta,\sigma_\ell\sin\theta,0).\tag{8.3}
$$

两个固定效果的读数合写为 $q(\theta)\in\mathbb R ^2$，则存在常向量 $q_0$ 与实矩阵 $M$，使

<a id="eq-ellipse"></a>

$$
q(\theta)=q_0+\sigma_\ell M
\begin{pmatrix}\cos\theta\\\sin\theta\end{pmatrix}.\tag{8.4}
$$

当 $\sigma_\ell>0$ 且 $M$ 可逆时，这是椭圆，满足

<a id="eq-ellipseeq"></a>

$$
(q-q_0)^{\mathsf T}(MM^{\mathsf T})^{-1}(q-q_0)=\sigma_\ell^2.\tag{8.5}
$$

当 $MM^{\mathsf T}$ 为正标量倍恒等时为圆；$M$ 秩一时退化为线段，秩零时为点。

**证明。**

端口约化的非对角条目为
$e^{-i\theta}\langle v_\ell,u_\ell\rangle /2$，由式 [(8.1)](#eq-modepair) 即得
式 [(8.3)](#eq-phasecircle)。
既有效果读出对 $\rho$ 线性，因此对三维坐标仿射线性，限制到 $Z_2=0$ 平面后即有
式 [(8.4)](#eq-ellipse)。若 $M$ 可逆，消去单位圆参数给式 [(8.5)](#eq-ellipseeq)；
低秩情形是圆的退化线性像。

□

```latex
\begin{center}
\begin{tikzpicture}[>=Latex,scale=.9]
\begin{scope}
\draw[gray!45] (0,0) circle (1.6);
\draw[->,gray] (-1.9,0)--(1.95,0) node[right] {$X_2$};
\draw[->,gray] (0,-1.8)--(0,1.85) node[above] {$Y_2$};
\draw[very thick,accent] (0,0) circle (1.08);
\draw[accent,->,thick] (1.08,0) arc (0:58:1.08);
\draw[dashed,warm] (0,0)--(58:1.08);
\fill[accent] (58:1.08) circle (2.5pt);
\node[warm,below] at (.45,.35) {$\sigma_\ell$};
\node[align=center,text width=4.2cm] at (0,-2.25) {固定二元模式\\相对相位画圆};
\end{scope}
\draw[->,very thick,ink] (2.55,0)--(4.05,0) node[midway,above] {$M$};
\begin{scope}[shift={(6.5,0)}]
\draw[->,gray] (-1.9,0)--(1.95,0) node[right] {$q_1$};
\draw[->,gray] (0,-1.8)--(0,1.85) node[above] {$q_2$};
\begin{scope}[rotate=25]
\draw[very thick,accent] (0,0) ellipse (1.55 and .68);
\end{scope}
\node[align=center,text width=4.4cm] at (0,-2.25) {同一模式的固定读出\\一般呈椭圆};
\end{scope}
\end{tikzpicture}
\end{center}
```

图示只表示一个模式与一个固定读口的解析关系，非整体现实轨迹的数值模拟。

相位参数具有 $2\pi$ 周期；例如平衡返回读数为

$$
p_+(\theta)=\frac{1+\sigma_\ell\cos\theta}{2}.
$$

若实际历史给 $\theta(t)=\omega t+\theta_0$、$\omega\ne0$，
非零模式的完整二端口态 $\rho_\ell(\theta(t))$ 的最小正时间周期为
$2\pi/|\omega|$；某个固定效果若只给常读数，则不具有最小正周期。
一般历史门序列若同时改变模式强度、参考方向或相位推进规律，
则不能仅凭“有圆”推出全局严格时间周期。
这里相位控制相对于固定比较读口进行；单纯更换向量代表并同步更换读口属于记号变换。

**白话图景。**每一种遗漏关系都可以看成两条历史之间的一根相干联系。
固定它的强度，只转相对相位，三维读口里就画出一个圆；
用两个固定观察量去看这个圆，通常看到椭圆，读数随一周一周的相位重复。
因此圆、椭圆和周期来自同一个内部二元结构。
若历史不断改变这根联系的强度或方向，轨迹也会随之改变，
这时要由实际门序列决定它怎样走。

<a id="section-9"></a>

## 9. 解析反例：共同来源不能替代实际跨翼关系

<a id="statement-9-1"></a>

#### 命题 9.1（完全相同的局部表，可有不同补足成本）

取正交单位方向 $e_0,e_1,e_2$，对 $0\le t<1$ 令

<a id="eq-example"></a>

$$
b=e_0,\qquad a=\frac{e_0+e_1}{\sqrt2},\qquad
c_t=\frac{e_0+t e_1+\sqrt{1-t^2}\,e_2}{\sqrt2}.\tag{9.1}
$$

全部这些整体的两份局部表相同，但

$$
\operatorname{rank}  T=0\quad(t=0),\qquad
\operatorname{rank}  T=1\quad(0<t<1).
$$

**证明。**

三向量均归一，且

$$
\langle a,b\rangle =\langle b,c_t\rangle =\frac1{\sqrt2},\qquad
\langle a,c_t\rangle =\frac{1+t}{2}.
$$

所以两个局部 Gram 块不随 $t$ 变化。
对 $S=\operatorname{span} \{e_0\}$，两残差为

$$
x=\frac{e_1}{\sqrt2},\qquad
y_t=\frac{t e_1+\sqrt{1-t^2}\,e_2}{\sqrt2}.
$$

其交叉块是 $Y=t/2$，而各自范数平方均为 $1/2$，
故规范 $W=t$，$T$ 的唯一非零奇异值在 $t>0$ 时为 $t$。
三原始向量在 $0\le t<1$ 时线性无关，因此该族全部全局核都正定、秩都为三。
不同补足成本并非全局秩退化造成。

□

对 $0<t<1$，$E_A$ 与 $E_C$ 是不同的一维直线，其交集为零，
但它们仍有非零关系；这也直接说明“关系共同”不能只按两空间交集定义。
定理 [6.2](#statement-6-2) 取 $U=\operatorname{span} \{e_1\}$，
把这一个旧内部方向纳入共同参照后就精确充分。

另外，将式 [(9.1)](#eq-example) 的同一代数公式延拓到边界 $t=-1$，
仍得到合法单位历史，此时 $\langle a,c_{-1}\rangle =0$，
而共同贡献为 $1/2$、残差贡献为 $-1/2$。
该边界不属于上面的正定族，此时全局核秩为二。
所以“原两翼内积为零”也不等于“共享已经充分”：
必须先扣除共同贡献，再判断剩余交叉关系。

**白话图景。**可以让两边与共同参考的关系一模一样，却在两边之间保留不同程度的额外联系。
所有对象依旧在同一个整体中，整体也完全合法。
因此内生性要求我们把已有联系找全，而不是把未知联系猜成零。
甚至表面上总关系为零，也可能是共同部分和剩余部分恰好互相抵消。

<a id="section-10"></a>

## 10. 把公理锁成定义约束：本轮真正完成了什么

### 10.1 同一候选的完整逻辑链

在固定实际整体之后，本轮结论可压成

<a id="eq-equivalence"></a>

$$
\begin{aligned}
S\text{ 共享充分}
&\Longleftrightarrow D_S(a,c)=0\quad(\text{所有跨翼 }a,c)\\
&\Longleftrightarrow E_A\perp E_C
\Longleftrightarrow Y=0
\Longleftrightarrow W=0
\Longleftrightarrow T=0.
\end{aligned}\tag{10.1}
$$

不充分时，命题 [2.3](#statement-2-3) 给出两个具体残差及其干涉差；
命题 [3.2](#statement-3-2) 把它们放进有限三维关系球；
定理 [5.2](#statement-5-2) 把全部二元缺口组成一个内在算子；
定理 [6.2](#statement-6-2) 与 [7.1](#statement-7-1) 完成最小内部补足及有限误差版本。

| 所问的问题 | 本轮锁定的对象或结论 |
| --- | --- |
| 公理不满足会怎样 | 共享描述遗漏一个实际非零交叉幅度，干涉读数因而不符 |
| 影响哪两个元 | 去共享投影后的左右残差 $x,y$ |
| 怎样有限三维提升 | 二元关系读口 $\mathbf r(x,y)$ 加保留尺度 $s$ |
| 属于哪个大结构 | 共同正核在共享子空间上的投影分解；全部补全由支撑收缩 $W$ 参数化 |
| 怎样在整体里补足 | 纳入旧内部方向 $U=\operatorname{ran}  T$；原全局核保持不变 |
| 补足是否最小 | 最少新增复维数 $\operatorname{rank}  Y$；$m$ 维最优残差 $\sigma_{m+1}(T)$ |
| 公理最终处于什么地位 | “充分”成为定义；补足存在性与最优性成为已证定理 |

### 10.2 准确的适用范围

本轮在项目已经得到的复正核及相干组合接口内工作。
共同复结构、读出效果、仪器与模型选择继续依其原有证明，
不把 N2 单独宣称为从无前件唯一选出复量子理论的原理。

本轮的 $A,B,C$ 是同一历史关系表的分组，
不是自动给定的三个张量子系统。
因此共享投影后的幅度正交不能直接改名为密度态的
$I(A:C\mid B)=0$，
也不能据本轮正核补全宣布任意一致的两个量子边缘密度态总能拼接。

$r$ 计数新增共享*复线性方向*，不是物理比特数、通信成本或实际可制备历史数。
式 [(6.7)](#eq-internalvector) 证明这些方向属于旧内部相干空间；
若要实际准备或读取，仍使用已经供应的门与读口。
该区分保留了内生性：表示层新增的是对已有关系的命名和分解，
操作层不由此凭空获得新能力。

### 10.3 一段完整白话

两条历史并不是只靠各自的端点决定关系，它们还带着共同部分和各自剩下的部分。
先把已经认作共同历史的部分取出来，再看两边剩下的东西还会不会相干。
如果还会，就说明共同记录漏了一种关系；这关系本来就在 $\Omega$ 里。
把全部遗漏关系拆开，每一份都只牵涉两个内部方向，能放进一个三维关系球。
固定强度转相位就是圆，固定读口看它通常就是椭圆，一周一周走便有周期信号。
若有 $r$ 种独立的遗漏关系，最少把 $r$ 个已有方向纳入共同记录就能解释完整；
若只容许补 $m$ 个，最强的剩余关系正好由第 $m+1$ 个奇异值给出。
于是“共同历史必须完整”不再是一句从外面压进来的公理：
完整是什么意思、哪里不完整、如何在内部补齐、最少需要多少，
都由同一张关系表约束并证明。

## 资料与可复核位置

<a id="ref-v63"></a>

**[1]**
[AURIC V63：原生复结构、稳定装配与有限 Born 读出证书](https://github.com/the-omega-institute/trureturing/blob/aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e/docs/develop/theory/AURIC_NATIVE_COMPLEX_STRUCTURE_STABLE_ASSEMBLY_AND_FINITE_BORN_READOUT_CERTIFICATES_V63.md)，
§5，定义 5.1、定理 5.2--5.3。使用其共享锚、正交残差与来源唯一性的范围说明。

<a id="ref-hidden"></a>

**[2]**
[AURIC FIB-ATOM：隐藏关系、统计、相位与接缝](https://github.com/the-omega-institute/trureturing/blob/aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e/docs/develop/theory/AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)，
§9，C-9.2、C-9.5；§27.4。
使用其三记录补全圆盘、逐参考更新和奇异支撑条件。

<a id="ref-v71"></a>

**[3]**
[AURIC V71：通用二元关系核、商余量与无界递归](https://github.com/the-omega-institute/trureturing/blob/aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e/docs/develop/theory/AURIC_UNIVERSAL_BINARY_RELATION_KERNELS_QUOTIENT_RESIDUALS_AND_UNBOUNDED_RECURSION_V71.md)，
§6，定理 6.1。奇异 Schur 判据；该文将相应先例归于 V52 定理 7.4。

<a id="ref-v72"></a>

**[4]**
[AURIC V72：唯一来源、正交余量与递归门](https://github.com/the-omega-institute/trureturing/blob/aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e/docs/develop/theory/AURIC_UNIQUE_SOURCE_ORTHOGONAL_RESIDUALS_AND_RECURSIVE_GATES_V72.md)，
§6，定理 6.1。来源锚定的正交残差。

<a id="ref-v77"></a>

**[5]**
[AURIC V77：量子公理的逆向定位、二元见证与内部相容](https://github.com/the-omega-institute/trureturing/blob/aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e/docs/develop/theory/AURIC_REVERSE_LOCATION_OF_QUANTUM_AXIOMS_BINARY_WITNESSES_AND_INTERNAL_COMPATIBILITY_V77.md)，
§3。保留全部合成二元对象与整体正性的既有接口。

<a id="ref-closure"></a>

**[6]**
[已证结构的内生闭合：同根有限证书、事件重编码与结果核递归](https://github.com/the-omega-institute/trureturing/blob/aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e/docs/develop/theory/AURIC_ENDOGENOUS_CLOSURE_FINITE_ROOT_CERTIFICATES_AND_OUTCOME_KERNEL_RECURSION_V78_CONTINUATION.md)，
V78 续稿，2026 年 11 月 2 日。
共同复结构的有限证书、权重到效果、结果核与分支、有限结果树。

<a id="ref-atlas"></a>

**[7]**
[Quantum Origin Endogenous Cut Atlas and Discrete Reconstruction Boundaries](https://github.com/the-omega-institute/trureturing/blob/aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md)，
§§26、29。模型选择仍受其明确操作与复合合同限定。

<a id="ref-n1"></a>

**[8]**
《候选 N1：相干桥的整体无损相容：二元三轴、共同记录与有效电阻证书》，
AURIC v78 后续研究，本对话已交付续稿，2026 年 11 月 2 日。
本次固定的公开仓库快照尚未收录该稿。

<a id="ref-grone"></a>

**[9]**
R. Grone, C. R. Johnson, E. M. Sá, H. Wolkowicz,
*Positive definite completions of partial Hermitian matrices*,
Linear Algebra and its Applications 58 (1984), 109--124.
[doi:10.1016/0024-3795(84)90207-6](https://doi.org/10.1016/0024-3795(84)90207-6)。
正矩阵补全的经典背景；本稿所用两块 Schur 与收缩参数式另给完整证明。

<a id="ref-eckart"></a>

**[10]**
C. Eckart and G. Young,
*The Approximation of One Matrix by Another of Lower Rank*,
Psychometrika 1 (1936), 211--218.
[doi:10.1007/BF02288367](https://doi.org/10.1007/BF02288367)。
低秩逼近的经典来源；本稿算子范数预算使用正文给出的独立秩下界与截断证明。

## 源稿前言与排版元数据

```latex
% !TEX program = xelatex
\documentclass[11pt,a4paper]{article}
\usepackage[margin=24mm,headheight=16pt]{geometry}
\IfFileExists{ctex.sty}{\usepackage[UTF8,fontset=auto]{ctex}}{
  \usepackage{fontspec}
  \IfFontExistsTF{Noto Serif CJK SC}{\setmainfont{Noto Serif CJK SC}[AutoFakeBold=1.7]}{\setmainfont{NotoSerifCJKsc-Regular.otf}[Path=fonts/,AutoFakeBold=1.7,AutoFakeSlant=.15]}
  \XeTeXlinebreaklocale "zh"
  \XeTeXlinebreakskip=0pt plus 1pt
}
\usepackage{amsmath,amssymb,amsthm,mathtools,mathrsfs}
\usepackage{xcolor,booktabs,array,tabularx}
\usepackage{fancyhdr,enumitem,hyperref,needspace,tikz}
\usetikzlibrary{arrows.meta,calc,positioning}
\definecolor{ink}{HTML}{17384A}
\definecolor{accent}{HTML}{007D86}
\definecolor{warm}{HTML}{B75B39}
\hypersetup{colorlinks=true,linkcolor=ink,urlcolor=accent,citecolor=ink,
pdftitle={AURIC v78 候选 N2：共享历史充分性与最小内部补足}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC / v78 / 候选 N2}
\fancyhead[R]{\small 共享历史、二元见证与内部补足}
\fancyfoot[C]{\thepage}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{4pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\renewcommand{\baselinestretch}{1.10}
\renewcommand{\contentsname}{目录}
\renewcommand{\abstractname}{摘要}
\renewcommand{\refname}{资料与可复核位置}
\renewcommand{\proofname}{证明}
\numberwithin{equation}{section}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{lemma}[definition]{引理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{remark}[definition]{说明}
\newcommand{\ip}[2]{\langle #1,#2\rangle}
\newcommand{\norm}[1]{\left\lVert #1\right\rVert}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\tr}{\operatorname{Tr}}
\newcommand{\Span}{\operatorname{span}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\ran}{\operatorname{ran}}
\newcommand{\ket}[1]{|#1\rangle}
\newcommand{\bra}[1]{\langle#1|}
\newcommand{\plain}[1]{\par\noindent\textbf{白话图景。}#1\par}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e/#1}{#2}}
\title{\color{ink}\bfseries 候选 N2：共享历史充分性\\[6pt]
\large 遗漏关系的三维见证、最小内部补足与维数预算\\[4pt]
AURIC v78 后续研究：定义、定理与证明}
\author{研究续稿}
\date{2026 年 11 月 2 日}
```

```latex
\begin{document}
\maketitle
\setcounter{tocdepth}{1}
{\small\setlength{\parskip}{0pt}\tableofcontents}
\newpage
\begin{quote}
\end{quote}
\begin{center}\small\texttt{aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e}。\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.27\textwidth}XX@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\noindent\small 图示只表示一个模式与一个固定读口的解析关系，非整体现实轨迹的数值模拟。\normalsize
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.25\textwidth}X@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\clearpage
\begin{thebibliography}{99}\raggedright
\end{thebibliography}
\end{document}
```

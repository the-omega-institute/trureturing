<a id="auric-v20"></a>

# 黄金选择门与递归编译

**AURIC 的 NAND 式普适性与变分原理**

**定义、定理与完整纸面证明**

**v20.0 · 2026 年 10 月 30 日 · Asia/Singapore**

<a id="sec-abstract"></a>

## 摘要

本文回到固定黄金门的递归预测路线，把黎曼猜想仅保留为谱一致性的参考。我们从同一原生门的两个编码地址构造两个十次调用的组合块，证明其行列式严格为一且生成稠密的 $\operatorname{SU}(2)$，由此给出无需外供整体相位的递归编译接口。进一步定义一个固定两比特黄金选择门：在明确的端口调用与计算基辅助位条件下，它既供应单比特稠密操作，也产生纠缠，因而具有单一门型的近似量子普适性。该门与五模式原子的一处四维子空间精确交织；我们同时证明此编码不能按物理导线直接分解，避免把单原子等价误认成全局接线证明。平衡交换子给出误差递推 $\varepsilon_{n+1}\le6\varepsilon_n^{3/2}$，而带原生成本的变分问题具有有限最优字、唯一 Bellman 解与普适性极限判据。静态作用量的正确归一化排除用 $K^{10}=I$ 填充产生的假收敛。最后用后验 Choi 谱、程序记录及最新同源停止前沿，区分编译误差、关系不确定性与观察成本。全文保留 Hilbert 空间、实际门菜单、初始化、评分和读出标定等使用前提。

<strong>结果身份。</strong>本文给出可逐步核查的纸面证明；不报告 Lean 编译、数值实验、最短门枚举或硬件实现。固定黄金数据、Fibonacci 编织、通用门思想、Solovay–Kitaev 递归、Bellman 方程和不可编程定理均有既有来源。本文的推进是把这些结构接成明确的 AURIC 门、相位、资源与观察接口，不主张这些经典原理的历史原创性。

> **转换说明（编者）。** 本文完整转换作者提供的 v20.0 XeLaTeX 稿件；各节共享陈述编号、全部纸面证明、公式、表格、引用与前提沿用源稿。关于项目快照、历史核对、研究连续性与经典结果的叙述均保留作者归属，不表示本次转换进行了独立数学认证。字体、分页与页眉由 Markdown 排版替代；数学宏显式展开，目录、陈述与文献采用独立锚点。

> **公式排版说明（编者）。** 源稿两个编号 `align` 块按原行保留全局公式 (1)–(5)，其中 (1)、(2) 原无标签；`eq:native`、`eq:skerr`、`eq:sklength` 分别指向 (3)、(4)、(5)。选择门定义、递归构造式和 Bellman 方程原在未编号显示环境中，虽有标签，仍不添加数字；引用采用描述性链接。未编号对齐式与矩阵的换行保持原有结构，正文数学未作实质修订。

## 目录

1. [项目快照：本轮究竟推进什么](#sec-1)
2. [先固定门、地址和通用性的含义](#sec-2)
3. [两个十次调用的组合块：把整体相位真正处理掉](#sec-3)
4. [一个明确的两端口黄金选择门](#sec-4)
5. [“反”成为递归纠偏：相位确定的编译定理](#sec-5)
6. [静态图上的预测方程与规范化作用量](#sec-6)
7. [带成本的变分、停止与 Bellman 唯一性](#sec-7)
8. [分辨率提高时，最优程序怎样增长](#sec-8)
9. [与 NAND 的关系：读出、可逆性与资源](#sec-9)
10. [观察者内生：程序的叠加与记录的保留](#sec-10)
11. [连目标关系也未知：后验谱的变分约束](#sec-11)
12. [最新同源观察前沿对编译理论的启示](#sec-12)
13. [黎曼猜想的参考地位与尚待完成的接口](#sec-13)

[文献与项目来源](#sec-bibliography)

<a id="sec-1"></a>

## 1. 项目快照：本轮究竟推进什么

固定公开研究分支 `dev` 的不可变提交为

`837df9a7545012a9e669c61716dac078f5552d96`。

时间为 2026-10-30 03:49:55（Asia/Singapore），PR #23846，标题为 <em>docs: exclude phase-reset finite-hidden producers from attainment</em>。相对前稿 v19 的 `a5a8bcdf…`，理论目录有 6 条变更路径：4 新增、2 修改；当前目录有 1019 个文件。本轮定向核对 15 份当前正文、2 份旧版及 Git blob；这不构成全库定理认证。

与本轮直接相关的事实是：

1. [v15 黄金门正文](https://github.com/the-omega-institute/trureturing/blob/837df9a7545012a9e669c61716dac078f5552d96/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)没有改变：固定 $K$ 已在指定编码和地址条件下具有近似普适性，也已有有限精确表达的算术障碍。其入库正文是此前作者稿件转换。
2. 新收入的[v17 加乘与对数稿](https://github.com/the-omega-institute/trureturing/blob/837df9a7545012a9e669c61716dac078f5552d96/docs/develop/theory/AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)和[v18 三角剖分与递归酉门稿](https://github.com/the-omega-institute/trureturing/blob/837df9a7545012a9e669c61716dac078f5552d96/docs/develop/theory/AURIC_TRIANGULATION_COLLAPSE_AND_RECURSIVE_UNITARY_GATES_V18.md)属于既有手稿转录，不能当作新的独立证明。v18 已明确：固定控制投影的自嵌套只给对易条件相位，不能自动推出通用性。
3. 新的[同源停止均值与空间风险](https://github.com/the-omega-institute/trureturing/blob/837df9a7545012a9e669c61716dac078f5552d96/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_STOPPED_MEAN_SPATIAL_RISK.md)把实际递归观察的风险、已付查询成本和原独立种子放在同一模型中，给出共同达到的前沿和预算变分问题。本文完整读取该文并在第[12](#sec-12)节使用其明确结论。

因此，本轮的目标是：给出一个更直接的两端口候选结构；把已有的稠密性推进到有相位控制和误差界的递归编译；把“预测 = 递归 = 最优化 = 变分”写成同一对象上的严格等价。新提交中的其他组合结果和事件重置桥不作为本文定理的前提。前稿的黎曼猜想接口也不参与任何普适性证明。

<a id="sec-2"></a>

## 2. 先固定门、地址和通用性的含义

<a id="statement-2-1"></a>

#### 定义 2.1（单门类型的编码近似普适性）

给定一个固定局部门 $K$、允许地址、初始化规则和等距编码
$J_n:(\mathbb{C}^2)^{\otimes n}\to\mathcal H_n$。若对任意 $V\in\operatorname{U}(2^n)$ 和 $\varepsilon>0$，存在只由允许地址上的 $K$ 组成的有限正向字 $W$，满足

$$
\inf_{\gamma\in\mathbb{R}}\left\lVert WJ_n-e^{i\gamma}J_nV\right\rVert_{\rm op}<\varepsilon,
$$

则称该资源模型具有单门类型的编码近似普适性。若不允许最小化整体相位，则称为指定相位的近似实现。

“同一种门可布在不同位置”和“一个固定算符只取幂”是不同命题。后者生成交换循环群，不能在维数至少二时覆盖全部射影酉群。普通 NAND 也需要接线、输入和可重复调用；量子版本还必须保留信息和相干性。二输入二输出的单一通用量子门早已有经典构造[[6](#ref-barenco)]，本文研究的是黄金数据下的具体实现与接口。

令

$$
\varphi=\frac{1+\sqrt5}{2},\qquad \omega=e^{3\pi i/5},\qquad
n=\lvert 1\rangle\langle 1\rvert,\quad X=\lvert 0\rangle\langle 1\rvert+\lvert 1\rangle\langle 0\rvert.
$$

原生三位置门采用项目既定矩阵：

<a id="eq-1"></a>

$$
Q_C=\varphi^{-1}(I-n_C)+\varphi^{-2}n_C+\varphi^{-3/2}X_C,
\tag{1}
$$

<a id="eq-2"></a>

$$
\mathcal P=n_Ln_R+(I-n_L)(I-n_R)Q_C,
\tag{2}
$$

<a id="eq-native"></a>

$$
K=\boxed{\omega\,[I+(\omega-1)\mathcal P].}
\tag{3}
$$

未写出的张量单位均理解为存在。$Q_C=vv^T$，其中
$v=(\varphi^{-1/2},\varphi^{-1})^T$、$v^Tv=1$；按左右位分块即得 $\mathcal P$ 为正交投影。因此

$$
K^r=\omega^r(I-\mathcal P)+\omega^{2r}\mathcal P,
\qquad K^{10}=I,\quad K^{-1}=K^9,\quad K^5=2\mathcal P-I.
$$

唯一非对角耦合是 $000\leftrightarrow010$。五种合法模式及标签为

$$
(000,100,010,001,101)\longleftrightarrow(0,1,2,3,13).
$$

五个标签是配置基底，不单凭其数量断定空间维数或推导 Born 规则。

在六位置编码 $J\lvert q\rangle=\lvert 10q010\rangle$ 上，从左起以第 2、3 位为中心调用 $K$，其三位窗口分别为 $(1,0,q)$ 与 $(0,q,0)$。两地址均精确保码，限制后的投影和门为

$$
P=\lvert 1\rangle\langle 1\rvert,\quad
Q=\begin{pmatrix}\varphi^{-1}&\varphi^{-3/2}\\
\varphi^{-3/2}&\varphi^{-2}\end{pmatrix},\qquad
A=\omega[I+(\omega-1)P],\quad B=\omega[I+(\omega-1)Q].
$$

故 $\operatorname{Tr}(PQ)=\lambda_0:=\varphi^{-2}$，$A^{10}=B^{10}=I$，且
$\det A=\det B=\omega^3$。这里 $A,B$ 是同一种原生门的两个地址，不是外加两种任意旋转。

黄金数来自已给定的 Fibonacci 融合/邻接关系 $d^2=d+1$ 的正根。合法路径上的相邻投影满足 $P_iP_{i+1}P_i=\lambda_0P_i$；展开
$[I+(z-1)P][I+(z-1)Q][I+(z-1)P]$ 与交换后的式子，其差为

$$
(z-1)[z+\lambda_0(z-1)^2](P-Q).
$$

非标量编织要求 $z=\omega$ 或 $\bar\omega$。这些是给定融合与表示下的相容结果；不是“所有通用门必须黄金化”的唯一性定理。

<a id="sec-3"></a>

## 3. 两个十次调用的组合块：把整体相位真正处理掉

<a id="statement-3-1"></a>

#### 定义 3.1（相位确定的黄金字母表）

定义

$$
D=A^9B=A^{-1}B,\qquad E=BA^9=BA^{-1},
\qquad \Sigma=\{D,E,D^{-1},E^{-1}\}.
$$

其中 $D^{-1}=B^9A$、$E^{-1}=AB^9$。每个字母都恰有十次原生正向调用，行列式为一。本文把字母串展开后的原生调用数记为 $C(w)=10|w|$，不假定这个实现已经最短。

<a id="thm-dense"></a>

#### 定理 3.2（两个黄金组合块稠密生成 $\operatorname{SU}(2)$）

$$
\boxed{\overline{\langle D,E\rangle}=\operatorname{SU}(2).}
$$

故 $\Sigma$ 是有限、逆封闭、无连续可调参数、指定相位的通用单比特字母表。

**证明。**

直接展开得

$$
\begin{aligned}
\operatorname{Tr} D
&=\omega+\bar\omega+|\omega-1|^2\operatorname{Tr}(PQ)\\
&=-\varphi^{-1}+\varphi^2\varphi^{-2}=\varphi^{-2}.
\end{aligned}
$$

若 $D$ 有限阶，则其特征值是单位根 $\xi,\xi^{-1}$，迹的每一个代数共轭都形如另一单位根与其逆之和，必落在 $[-2,2]$。但 $\varphi^{-2}=(3-\sqrt5)/2$ 的另一共轭是 $\varphi^2=(3+\sqrt5)/2>2$，矛盾。因此 $D$ 无限阶，其幂在一个连续酉圆上稠密。

又 $E=ADA^{-1}$，同迹且非中心。若 $D,E$ 交换，因 $D$ 有两个不同特征值，两者同对角化且 $E=D$ 或 $D^{-1}$。第一种情况要求 $A$ 与 $D=A^{-1}B$ 交换，等价于 $A,B$ 交换；但

$$
AB-BA=\omega^2(\omega-1)^2(PQ-QP)\ne0.
$$

第二种情况要求 $A$ 交换 $D$ 的两条特征线，因此 $A$ 在该基中对角元为零，得到 $\operatorname{Tr} A=0$，与 $\operatorname{Tr} A=\omega+\omega^2\ne0$ 矛盾。故 $D,E$ 不交换。

两个无限阶元素所生成的酉圆因而具有不同轴。$\mathfrak{su}(2)$ 中两个不共线生成元及其交换子张成整个三维 Lie 代数：在 $i\sigma_x,i\sigma_y,i\sigma_z$ 基下，交换子对应叉积。闭子群的 Lie 代数包含它们，故包含整个连通群 $\operatorname{SU}(2)$。反向包含来自每个字母均在 $\operatorname{SU}(2)$。

∎

单个 $K$ 的谱只有十次单位根，两个地址的相对关系却产生无限阶元素。这给“连续表达从离散组合中出现”一个精确版本：连续性是此指定算符范数闭包的性质，每个实现仍为有限字；它没有单独证明物理连续性是幻觉。

<a id="statement-3-3"></a>

#### 推论 3.3（原生二维闭包与相位边界）

令 $\mu_{10}$ 为十次单位根集，则

$$
\overline{\langle A,B\rangle}=G_{10}:=\{U\in\operatorname{U}(2):\det U\in\mu_{10}\}.
$$

对任意 $U\in\operatorname{U}(2)$，若
$\delta(U)=\min_{\eta\in\mu_{10}}|\operatorname{Arg}(\eta/\det U)|$，则

$$
\operatorname{dist}_{\rm op}(U,G_{10})=2\sin\frac{\delta(U)}4.
$$

**证明。**

定理[3.2](#thm-dense)给闭包包含 $\operatorname{SU}(2)$；$\det A=\omega^3$ 生成 $\mu_{10}$，所以全部十个陪集均出现，且行列式连续性排除其他陪集。
若 $U^\dagger W$ 的主值特征角为 $\theta_1,\theta_2$，则
$|\operatorname{Arg}\det(U^\dagger W)|\le|\theta_1|+|\theta_2|$。
若 $\left\lVert U-W\right\rVert_{\rm op}=r$，则 $|\theta_j|\le2\arcsin(r/2)$，所以 $r\ge2\sin(\delta/4)$。取最近行列式相差的有符号角 $\alpha$，令 $W=e^{i\alpha/2}U$，即达到下界。

∎

例如 $T=\operatorname{diag}(1,e^{i\pi/4})$ 在此码内的指定相位距离为
$2\sin(\pi/80)>0$，尽管它的射影操作可以任意逼近。对任意非零投影 $P_0$，受控提升

$$
\mathcal C_{P_0}(U)=(I-P_0)\otimes I+P_0\otimes U
$$

满足 $\left\lVert \mathcal C_{P_0}(U)-\mathcal C_{P_0}(V)\right\rVert_{\rm op}=\left\lVert U-V\right\rVert_{\rm op}$。
因此射影误差为零不保证受控误差为零。这个恒等式是误差传播结论，不赠送一个可调用的受控未知门；本文的字母表在实际 $\operatorname{SU}(2)$ 矩阵层面编译。

<a id="sec-4"></a>

## 4. 一个明确的两端口黄金选择门

<a id="statement-4-1"></a>

#### 定义 4.1（固定黄金选择门）

在两个普通逻辑比特上定义

<a id="eq-selector"></a>

$$
\boxed{G=\lvert 0\rangle\langle 0\rvert\otimes A+\lvert 1\rangle\langle 1\rvert\otimes B.}
$$

第一个端口为选择端口，第二个为数据端口。它仍具有黄金投影形式：

$$
G=\omega[I+(\omega-1)\Pi],\qquad
\Pi=\lvert 0\rangle\langle 0\rvert\otimes P+\lvert 1\rangle\langle 1\rvert\otimes Q.
$$

因此 $G$ 酉，$G^{10}=I$，$G^{-1}=G^9$。

<a id="thm-selector"></a>

#### 定理 4.2（明确端口条件下的单门型通用性）

假设可以把同一个固定 $G$ 作用到任意指定的有序逻辑比特对，并供应计算基辅助位 $\lvert 0\rangle,\lvert 1\rangle$。除这些初始化、端口调用和重复使用外，不供应其他任意酉门。则对每个有限 $n$，该模型的有限 $G$ 电路在 $\operatorname{PU}(2^n)$ 上稠密。

**证明。**

<strong>单比特操作由同一门供应。</strong>选择端口置于 $\lvert 0\rangle$ 或 $\lvert 1\rangle$，分别在数据上精确实现 $A$ 或 $B$，且辅助位保持原计算基态、与数据不纠缠，可再次使用。定理[3.2](#thm-dense)遂给每个数据位的完整 $\operatorname{SU}(2)$ 闭包。这里的连续局部操作来自有限固定门的闭包，不是额外的可调资源。

<strong>两比特相互作用不消失。</strong>置 $D=A^{-1}B$，有

$$
G=(I\otimes A)\bigl(\lvert 0\rangle\langle 0\rvert\otimes I+\lvert 1\rangle\langle 1\rvert\otimes D\bigr).
$$

$\operatorname{Tr} D=\varphi^{-2}$，故 $D\in\operatorname{SU}(2)$ 非标量。适当局部共轭将其对角化为 $e^{i\theta Z}$，$0<\theta<\pi$。移去闭包中已有的局部因子后，闭包包含

$$
E_\theta=\exp[-i(\theta/2)Z\otimes Z],
$$

因为受控 $e^{i\theta Z}$ 等于
$\exp[i(\theta/2)I\otimes Z]E_\theta$。
共轭一个局部 Lie 生成元给

$$
\operatorname{Ad}_{E_\theta}(iI\otimes X)
=i\cos\theta\,I\otimes X+i\sin\theta\,Z\otimes Y.
$$

由 $\sin\theta\ne0$，闭包的 Lie 代数包含 $iZ\otimes Y$。
与已有局部 Pauli 生成元取交换子，即产生全部九个
$i\sigma_a\otimes\sigma_b$；再加六个局部生成元，张成 $\mathfrak{su}(4)$。因此两比特闭包包含 $\operatorname{SU}(4)$。

<strong>扩展到有限寄存器。</strong>任意有序对可调用，故任意两位置上都有上述全部相互作用。由 Pauli 字串归纳：已有某支持集上的非恒等字串时，选支持内一位与新增一位的双位 Pauli，让共有位置的两个 Pauli 反交换；两生成元的交换子产生扩大一位的 Pauli 字串，再用局部共轭选择各轴。于是得到全部 $4^n-1$ 个非恒等 Pauli 生成元，张成 $\mathfrak{su}(2^n)$。有限维闭包含整个 $\operatorname{SU}(2^n)$，因而射影稠密。逆门始终可由 $G^9$ 供应。

∎

此架构要求选择端口既能在调用局部门时固定为计算基值，也能在调用两比特相互作用时承载量子相干态。如果该端口永远只允许经典选择，所有数据作用都只是分别的 $A,B$，上述多比特通用性不成立。

<a id="statement-4-3"></a>

#### 命题 4.3（显式纠缠与条件性的最小门元数）

$G$ 将乘积态 $\lvert +\rangle\lvert 1\rangle$ 变成纯态，其 concurrence 为 $\varphi^{-1/2}>0$。在只允许乘积初始化、单比特酉门和导线置换的模型中，不可能有量子普适性。因此在定理[4.2](#thm-selector)的普通张量比特模型中，两比特是通用酉门所需的最小非平凡作用元数。

**证明。**

输出是 $(\lvert 0\rangle A\lvert 1\rangle+\lvert 1\rangle B\lvert 1\rangle)/\sqrt2$，concurrence 为
$\sqrt{1-|\langle 1\rvert A^\dagger B\lvert 1\rangle|^2}$。
由 $Q_{11}=\varphi^{-2}$，重叠模平方为
$|1+(\omega-1)\varphi^{-2}|^2=\varphi^{-2}$，得到所述值。
单比特门与置换保持每个乘积纯态为乘积态，其闭包也如此，不能逼近 Bell 态生成操作。此最小性不覆盖免费纠缠初态、联合测量或不同局部维数等额外资源模型。

∎

$\lvert +\rangle$ 在上述论证中只是证明纠缠能力的测试向量，并未声称它可由有限原生字精确制备。近似制备已由单比特稠密性供应。

<a id="sec-4-1"></a>

### 4.1. 它确实藏在一个五模式原子内，但接线仍须证明

<a id="thm-cell"></a>

#### 定理 4.4（单原子的精确四维编码）

令 $J_2:\mathbb{C}^2\otimes\mathbb{C}^2\to\mathcal H_{\rm legal}$ 按下表定义。

| 选择位 | 数据位 | 原生合法词 | 模式标签 |
| --- | --- | --- | --- |
| 0 | 0 | 100 | $1$ |
| 0 | 1 | 101 | $13$ |
| 1 | 0 | 000 | $0$ |
| 1 | 1 | 010 | $2$ |

则 $J_2$ 等距，$KJ_2=J_2G$，剩余模式 $001$ 的本征值为 $\omega$。
但是该 $J_2$ 不可能按任何三条物理导线的二分解写成 $J_c\otimes J_t$，即使允许重排物理位。

**证明。**

前两行中原生投影分别给 $0,1$，形成 $P$ 块；后两行正是活动 $Q$ 块。四个不同计算基词正交，得到交织等式。模式 $001$ 的左右位混合，投影为零。

若存在按导线分割的乘积编码，固定数据位为零、改变选择位使 $100\leftrightarrow000$，所以第一物理位必须属于选择因子。固定选择位为零、改变数据位使 $100\leftrightarrow101$，所以第三位属于数据因子；固定选择位为一时 $000\leftrightarrow010$，又迫使第二位属于数据因子。唯一可能分割为第一位与后两位。但同一个数据值一在后两位分别编码为 $01$ 和 $10$，依赖选择值，违背 $J_t$ 的独立性。

∎

因此需要区别三个已明确的命题：单原子有这个四维矩阵块；把 $G$ 作为可调用的两端口门时近似通用；原生多原子设备必须提供同一个全局编码及地址实现，才能使用后一个结论。局部四维交织本身未完成第三项。它也不排除其他共享约束编码或付出成本的相干路由。

原生 $K$ 的另一条多比特路线在 v15 已经写明：$n$ 个四任意子真空块对应 $4n+2$ 个位置，前缀融合路径与原生地址逐项交织；在该桥下使用 Fibonacci 编织稠密性[[7](#ref-flw)]得到编码近似普适性。本文不把两端口 $J_2$ 等价冒充对该全局桥的替代证明。固定原生链保留相邻占据缺陷，也仍排除未编码全寄存器的通用性。

<a id="sec-5"></a>

## 5. “反”成为递归纠偏：相位确定的编译定理

这里的取反首先是逆算符。对酉 $V,W$ 定义群交换子

$$
[V,W]_{\rm g}=VWV^\dagger W^\dagger.
$$

它度量两个相容候选操作交换次序后的差异。下列递归属于经典 Solovay–Kitaev 思路[[8](#ref-sk)]；我们给出在本黄金字母表中可直接使用的严格常数与完整证明。

<a id="lem-balanced"></a>

#### 引理 5.1（精确平衡交换子）

对 $\Delta\in\operatorname{SU}(2)$，令 $d=\left\lVert \Delta-I\right\rVert_{\rm op}$。存在 $V,W\in\operatorname{SU}(2)$ 使

$$
\Delta=[V,W]_{\rm g},\qquad
\left\lVert V-I\right\rVert_{\rm op},\left\lVert W-I\right\rVert_{\rm op}\le\sqrt d.
$$

**证明。**

$0\le d\le2$。取 $\alpha\in[0,\pi/2]$ 满足
$\sin^2\alpha=d/2$，置 $V_0=e^{i\alpha X}$、$W_0=e^{i\alpha Y}$。
由 Pauli 乘法 $XY=iZ$ 及循环关系直接展开有

$$
\operatorname{Tr}[V_0,W_0]_{\rm g}=2-4\sin^4\alpha=2-d^2.
$$

$\Delta$ 的特征值 $e^{\pm i\theta}$ 给 $d^2=2-2\cos\theta$，故 $\operatorname{Tr}\Delta=2-d^2$。$\operatorname{SU}(2)$ 中同迹矩阵有相同特征值，彼此酉共轭；共轭矩阵可乘标量使行列式为一。用同一个共轭变换 $V_0,W_0$ 得到 $V,W$，交换子即为 $\Delta$。最后

$$
\left\lVert V-I\right\rVert_{\rm op}^2
=2-2\sqrt{1-d/2}
=\frac{d}{1+\sqrt{1-d/2}}\le d,
$$

对 $W$ 同理。$d=0$ 可直接取 $V=W=I$。

∎

<a id="lem-stability"></a>

#### 引理 5.2（逆向配对消除一阶大误差）

设四个算符均酉，并满足

$$
\left\lVert V-\widetilde V\right\rVert,\left\lVert W-\widetilde W\right\rVert\le\epsilon,
\qquad \left\lVert V-I\right\rVert,\left\lVert W-I\right\rVert\le r.
$$

则其交换子的误差满足

$$
\left\lVert [V,W]_{\rm g}-[\widetilde V,\widetilde W]_{\rm g}\right\rVert_{\rm op}
\le4r\epsilon+2\epsilon^2.
$$

**证明。**

先只替换 $V$，将 $W$ 写成 $I+(W-I)$；共轭中的恒等项抵消，所以这一差至多
$2\epsilon\left\lVert W-I\right\rVert$。再只替换 $W$，把 $\widetilde V^\dagger$ 写成
$I+(\widetilde V^\dagger-I)$，相应差至多
$2\epsilon\left\lVert \widetilde V-I\right\rVert\le2\epsilon(r+\epsilon)$。
相加即得。这里使用了同一个近似门及其精确逆；若反向因子是独立漂移的硬件操作，该抵消不能无条件沿用。

∎

<a id="thm-sk"></a>

#### 定理 5.3（黄金字母表的递归编译）

给定覆盖 $\operatorname{SU}(2)$ 的有限字初始网，算子误差不超过 $\epsilon_0<1/36$，每个初始字至多含 $L_0$ 个 $\Sigma$ 字母。存在同一字母表上的递归编译器，使每个目标 $U\in\operatorname{SU}(2)$ 的第 $n$ 层近似 $U_n$ 满足

<a id="eq-skerr"></a>

$$
\epsilon_n\le6\epsilon_{n-1}^{3/2}
\le\frac1{36}(36\epsilon_0)^{(3/2)^n},
\tag{4}
$$

<a id="eq-sklength"></a>

$$
L_n\le5^nL_0,\qquad C(U_n)\le10L_0 5^n.
\tag{5}
$$

特别地，原生调用数可取

$$
C(\epsilon)=O\!\left(\log^c\frac1\epsilon\right),
\qquad c=\frac{\log5}{\log(3/2)}.
$$

**证明。**

稠密性与紧性保证存在任何固定正精度的有限覆盖网。基例由该网给出。
假设上一层能以误差 $\epsilon=\epsilon_{n-1}$ 编译每个目标。先得 $U_{n-1}$，令

$$
\Delta=UU_{n-1}^\dagger.
$$

由引理[5.1](#lem-balanced)将它精确写为 $[V,W]_{\rm g}$，因子距恒等至多 $\sqrt\epsilon$。
同一个上一层编译器为 $V,W$ 分别提供 $V_{n-1},W_{n-1}$，定义

<a id="eq-skrec"></a>

$$
\boxed{U_n=V_{n-1}W_{n-1}V_{n-1}^\dagger
W_{n-1}^\dagger U_{n-1}.}
$$

引理[5.2](#lem-stability)给误差不超过
$4\epsilon^{3/2}+2\epsilon^2\le6\epsilon^{3/2}$。
$\epsilon_0<1/36$ 保证误差界递减且始终小于一；令 $q_n=36\epsilon_n$ 即得
$q_n\le q_{n-1}^{3/2}$，得到式[(4)](#eq-skerr)。
逆封闭使反向字与正向字同长，五个因子给 $L_n\le5L_{n-1}$，每个字母十次原生调用，得到式[(5)](#eq-sklength)。消去递归深度 $n$ 得所述多对数长度界。

∎

这正是“预测过程仍由同类过程构成”的一项严格实现：对子门 $V,W$ 的预测仍用同一固定字母表和同一编译器，逆门也不增加门类型。确定 $V,W$ 时使用的矩阵共轭是目标描述的经典运算；真正执行的仍是编译后的有限字。

式[(4)](#eq-skerr)下降的是统一保证误差界，不要求每个特定目标的实际误差逐层下降。若需要后者，可在每一层比较新旧两个完整候选并保留误差较小者，所述长度预算和误差保证仍成立。这也不要求每个原生物理门降低某个能量；$K^{10}=I$ 已排除沿每个非平凡周期都严格下降的全局势函数。

这里有三个实际界线。第一，初始网的存在不等于本文已经列出一份最短网；本轮未做门枚举。第二，目标描述的精度、矩阵运算和网查找均是编译成本，不能由门长界抹掉。第三，这是一个明确可证的经典指数，并不声称是最佳编译指数或最短门字。五因子式来自四因子的交换子加旧近似；它与五模式数目相同，并未因此建立五个模式逐个对应五个因子的自然同构。

<a id="statement-5-4"></a>

#### 命题 5.4（实际门误差的累计界）

若原生字 $U_w=G_L\cdots G_1$ 的实际酉实现为 $\widetilde U_w=\widetilde G_L\cdots\widetilde G_1$，且每次 $\left\lVert \widetilde G_j-G_j\right\rVert_{\rm op}\le\delta_j$，则

$$
\left\lVert \widetilde U_w-U\right\rVert_{\rm op}
\le\left\lVert U_w-U\right\rVert_{\rm op}+\sum_{j=1}^L\delta_j.
$$

**证明。**

逐项替换乘积因子并作望远镜相减，每项两侧的酉乘积不改变算子范数，得到实际字与理想字之差至多为 $\sum_j\delta_j$。再用三角不等式。

∎

这是最坏情况上界，不断增加字长本身不能使它趋零。若门本身也在预测中，递归精度必须与实际校准、误差相关结构或另外声明的纠错资源一起分析；理想矩阵的编译定理没有自动处理这些变量。

<a id="sec-6"></a>

## 6. 静态图上的预测方程与规范化作用量

令一个原生字的切面关系写成

$$
X_j=G_jX_{j-1}\quad(1\le j\le L),\qquad X_0=I.
$$

指标 $j$ 只是在一个固定依赖链上标记切面，不必解释成外部物理时间。全输入门为 $U_w=G_L\cdots G_1$。

<a id="statement-6-1"></a>

#### 定义 6.1（全输入预测残差作用）

对目标门 $V$，让内部 $X_j$ 遍历全部复矩阵，并固定额外边界 $X_{L+1}=V$，定义

$$
\mathcal S_w(X)=\sum_{j=1}^L\left\lVert X_j-G_jX_{j-1}\right\rVert_F^2
+\left\lVert V-X_L\right\rVert_F^2.
$$

额外末边的传输为恒等；该定义也覆盖空字 $L=0$。

<a id="thm-action"></a>

#### 定理 6.2（边界误差与静态变分的精确等价）

$$
\boxed{\min_X\mathcal S_w(X)=\frac{\left\lVert V-U_w\right\rVert_F^2}{L+1}.}
$$

因此 $\frac{L+1}{d}\min_X\mathcal S_w(X)$ 恰为维数 $d$ 下的归一化全输入门误差。

**证明。**

置 $U_j=G_j\cdots G_1$，$Y_j=U_j^\dagger X_j$，并令
$Y_0=I$、$Y_{L+1}=U_w^\dagger V$。酉不变性将作用量化为
$\sum_{j=1}^{L+1}\left\lVert Y_j-Y_{j-1}\right\rVert_F^2$。
所有增量之和固定为 $U_w^\dagger V-I$。Cauchy–Schwarz 给下界
$\left\lVert U_w^\dagger V-I\right\rVert_F^2/(L+1)$，等号由各增量相同达到，即
$Y_j=I+\frac j{L+1}(U_w^\dagger V-I)$。

∎

内部最小化矩阵一般不酉，是相容预测变量，不能当作实际量子执行中间门。若另要求内部每个矩阵都酉，本定理的可行域改变，结论不直接保留。

<a id="statement-6-3"></a>

#### 推论 6.3（切面细化不能免费改善预测）

固定错误边界实现 $U_w\ne V$，在字中插入任意多个 $K^{10}=I$，全输入门不变；未经归一化的最小 $\mathcal S_w$ 却趋于零。故必须乘以相应的 $L+1$，才能把零缺陷解释为门逼近。

对更一般有限 DAG，若不可比顶点作用于互不相交端口，任意两个拓扑序由相邻交换这些顶点连接，因此给出同一边界映射。门之间的依赖关系仍在；“没有外部线性时间”不等于任意不交换算符可以换序。式[递归构造式（源稿未编号）](#eq-skrec)的五个因子是依赖有序的组合关系。

<a id="sec-7"></a>

## 7. 带成本的变分、停止与 Bellman 唯一性

<a id="statement-7-1"></a>

#### 定义 7.1（正规化编译价值）

设 $\mathcal A$ 为有限酉字母表，每个字母有严格正成本 $c_g$。字 $w$ 的成本为 $C(w)=\sum c_g$；允许空字。对目标 $R\in\operatorname{U}(d)$，定义

$$
b(R)=\frac1d\left\lVert R-I\right\rVert_F^2\in[0,4],\qquad
F_\eta(R)=\inf_w\{b(U_w^\dagger R)+\eta C(w)\},\quad\eta>0.
$$

黄金 $\Sigma$ 的每个 $c_g=10$。$\eta$ 是精度与成本的权衡参数，不是黄金重叠 $\lambda_0$。

<a id="thm-bellman"></a>

#### 定理 7.2（有限最优与唯一停止递归）

每个 $\eta>0$ 的下确界由有限字达到，最优字满足 $C(w)\le4/\eta$。并且 $F_\eta$ 是以下方程在值域 $[0,4]$ 内的唯一解：

<a id="eq-bellman"></a>

$$
\boxed{F_\eta(R)=\min\left\{b(R),\ 
\min_{g\in\mathcal A}[\eta c_g+F_\eta(g^\dagger R)]\right\}.}
$$

**证明。**

空字给价值至多四；任何成本大于 $4/\eta$ 的字不可能改善它。由于 $c_{\min}>0$、字母有限，剩下的字只有有限多个，所以最小值存在。
把非空乘积写成最左因子 $g$ 乘余字，误差和成本立即给式[Bellman 方程（源稿未编号）](#eq-bellman)。

若 $H:\operatorname{U}(d)\to[0,4]$ 也满足该式，逐次沿任意字展开给
$H(R)\le\eta C(w)+b(U_w^\dagger R)$，所以 $H\le F_\eta$。
反之，在每个点选择一个达到最小值的分支。若一直不停止，经过 $N$ 条边便有
$H(R)\ge N\eta c_{\min}$，与 $H(R)\le4$ 矛盾。因此有限步停在 $b$ 分支，沿该字得到
$H(R)=\eta C(w)+b(U_w^\dagger R)\ge F_\eta(R)$。两向合并。

∎

这是带可行字语言和正成本的全局 Bellman 递归。它不宣称局部贪心会找到全局最优，也不宣称其求解复杂度因写成递归而变小。

<a id="thm-value"></a>

#### 定理 7.3（普适性等于极限变分缺陷消失）

令 $\mathcal K$ 为可达有限字的闭包，则

$$
\lim_{\eta\downarrow0}F_\eta(R)
=\min_{U\in\mathcal K}\frac1d\left\lVert U-R\right\rVert_F^2.
$$

在紧目标空间上该收敛一致。因此黄金 $\Sigma$ 的指定相位通用性等价于
$F_\eta(R)\to0$ 对所有 $R\in\operatorname{SU}(2)$ 成立。

**证明。**

右侧记为 $f(R)$，紧性保证最小值存在。非负成本给 $F_\eta\ge f$。
给定任意精度，取某有限字使其边界误差接近 $f(R)$；固定此字后令 $\eta\downarrow0$，得到另一方向。
一致性可直接由紧性证明：对每个 $R$ 选一个有限字，使该点误差小于 $f(R)+\epsilon$；误差和 $f$ 都连续，所以同一字在某邻域内小于 $f+2\epsilon$。取有限子覆盖，所有选中字的成本有共同有限上界；令 $\eta$ 足够小即得到全空间的 $3\epsilon$ 界。

∎

若改用 $b_{\rm p}(R)=2-2|\operatorname{Tr} R|/d$，相同证明得到射影版本，常数四换成二。相位确定版本与射影版本不能在受控组合时混用。

<a id="statement-7-4"></a>

#### 命题 7.4（去掉成本后出现假解）

零成本方程

$$
F(R)=\min\{b(R),\min_gF(g^\dagger R)\}
$$

对任意门菜单都有 $F\equiv0$ 解，甚至菜单只有 $I$。因此递归方程“有相容零解”本身不能证明逼近能力。

**证明。**

$b\ge0$，直接代入即成立。菜单只有 $I$ 时，实际有限字始终是 $I$，对于 $R\ne I$ 真正边界误差仍为正。

∎

<a id="sec-8"></a>

## 8. 分辨率提高时，最优程序怎样增长

<a id="statement-8-1"></a>

#### 定理 8.1（正则化路径与程序变化）

固定目标 $R$。$\eta\mapsto F_\eta(R)$ 非减且凹，在任意 $0<a\le\eta\le b$ 上是有限个仿射函数的下包络。若 $\eta_1<\eta_2$，任取两参数的最优字，记成本和误差为 $C_1,e_1^2$ 与 $C_2,e_2^2$，则

$$
C_1\ge C_2,\qquad e_1^2\le e_2^2.
$$

若 $R$ 在可达闭包内却非任一有限字，则当 $\eta\downarrow0$，任意最优字满足

$$
e_\eta\to0,\qquad C_\eta\to\infty,\qquad \eta C_\eta\to0.
$$

**证明。**

每个字给非减仿射函数 $e_w^2+\eta C(w)$；其下确界非减且凹。参数下界 $a>0$ 令所有最优成本至多 $4/a$，只剩有限多个字。
两条最优性不等式相加得到
$(\eta_2-\eta_1)(C_1-C_2)\ge0$，再代回任一不等式得误差排序。
定理[7.3](#thm-value)给 $F_\eta\to0$，所以两个非负项均趋零。若最优成本不趋无穷，存在有界成本子列；有限个字中每个都与 $R$ 保持正距离，产生共同正误差下界，矛盾。

∎

最优程序可以在某些参数值发生离散跳变；价值函数仍连续、分段仿射。这是程序选择的变化，不能单凭“跳变”称为物理隧穿或测量塌缩。

<a id="thm-bounds"></a>

#### 定理 8.2（黄金编译的精度与成本上下界）

令 $c=\log5/\log(3/2)$。对 $\Sigma$ 及任意 $R\in\operatorname{SU}(2)$，有常数 $C_0$，使充分小 $\eta>0$ 下

$$
F_\eta(R)\le C_0\eta\log^c(1/\eta).
$$

任意全局最优字均满足

$$
C_\eta\le C_0\log^c(1/\eta),\qquad
e_\eta^2\le C_0\eta\log^c(1/\eta).
$$

对目标 $R=iX$，结合项目既有的原生奇偶界，进一步有

$$
C_\eta\ge
\frac{\log(1/\eta)-c\log\log(1/\eta)-O(1)}{\log\Gamma},
\quad \Gamma=\varphi^3+\sqrt{\varphi^6-1}<9.
$$

**证明。**

对于两个 $\operatorname{SU}(2)$ 矩阵，其相对酉的特征值为 $e^{\pm i\theta}$，所以
$\left\lVert U-V\right\rVert_F^2/2=\left\lVert U-V\right\rVert_{\rm op}^2$。用定理[5.3](#thm-sk)取误差 $\epsilon=\sqrt\eta$ 的字，原生成本为
$O(\log^c(1/\eta))$，代入价值定义即得上界。最优价值的两个非负项各不超过总值，得到两个最优字界。

下界明确使用[v16 的奇偶残留定理](https://github.com/the-omega-institute/trureturing/blob/837df9a7545012a9e669c61716dac078f5552d96/docs/develop/theory/AURIC_PREDICTION_RECURSION_OPTIMIZATION_AND_VARIATION_V16.md)：标准计算基码中，任意 $L$ 次原生正向字的同输入奇偶输出概率
$q\ge2/(1+\Gamma^L)$。目标 $iX$ 只翻逻辑位，两个物理码字的 Hamming 奇偶相反；故其算子误差平方至少为这个 $q$。于是

$$
C_\eta\ge\frac{\log(2e_\eta^{-2}-1)}{\log\Gamma}.
$$

把已经证明的误差上界代入，展开对数得结果。此处常数依赖固定菜单与初始网；下界供应的适用条件是纯酉原生字、该基编码、无后选择及外供非基态。

∎

这把“观察者的增长”限定为一个可证现象：在指定评分与门语言中，提高精度会迫使最优程序的成本无界增长，同时每个正成本参数仍有有限最优。它没有把未知目标的精确信息、最短程序的有效发现或实际物理校准一起免费推出。

<a id="sec-9"></a>

## 9. 与 NAND 的关系：读出、可逆性与资源

经典 NAND 为 $f(a,b)=1\oplus ab$。其相干可逆扩展是

$$
V_f\lvert a,b,t\rangle=\lvert a,b,t\oplus f(a,b)\rangle,\qquad V_f^2=I.
$$

第三位初置零时给 NAND 值。这个三比特置换还规定叠加输入的相位与相干性，比四个经典输入的正确输出要求更强。

<a id="statement-9-1"></a>

#### 命题 9.1（近似门给出的 NAND 正确率）

若 $\left\lVert WJ-e^{i\gamma}JV_f\right\rVert_{\rm op}\le\epsilon$，并以目标输出投影读出且将泄漏计为失败，则任意计算基输入的 NAND 错误概率至多为 $\epsilon^2$。

**证明。**

错误读出投影 $P_{\rm err}$ 消去理想输出，所以
$\left\lVert P_{\rm err}WJ\lvert a,b,0\rangle\right\rVert\le\epsilon$，采用 Born 标定后取平方即得。

∎

定理[4.2](#thm-selector)供应其架构下的任意精度近似；原生 $K$ 也可在前述 Fibonacci 全局编码桥下使用既有近似普适性。另一方面，v15 的分级/Galois 证明仍排除固定计算基编码中有限原生字的精确 clean $X$、CNOT、Toffoli 和相干可逆 NAND。这不与 $\epsilon\to0$ 的逼近相矛盾。

| 所问性质 | 本文可支持的结论 |
| --- | --- |
| 单一固定门型 | 原生 $K$；两端口候选 $G$ 也固定，无连续控制角。 |
| 同一位置反复调用 | $K^{10}=G^{10}=I$，单独如此不通用。 |
| 取反的作用 | 逆门保证交换子纠偏；只用两地址 $K^5$ 仍仅为实正交闭包。 |
| 单比特指定相位 | 两个十次调用块 $D,E$ 稠密生成 $\operatorname{SU}(2)$。 |
| 多比特近似通用 | $G$ 在明确端口/辅助位架构下成立；原生 $K$ 用已有全局融合编码桥。 |
| 有限字精确 NAND | 不能由近似通用性推出；标准原生码有已证算术障碍。 |
| 全局最短与有效性 | 正成本最优存在；递归上界可证；未宣称求得最短字或免费求解。 |

<a id="sec-10"></a>

## 10. 观察者内生：程序的叠加与记录的保留

<a id="statement-10-1"></a>

#### 定义 10.1（静态程序空间）

令 $\mathcal W$ 为全部有限合法门字，取程序空间 $\ell^2(\mathcal W)$。已知矩阵族定义直和酉算符

$$
\mathrm{SELECT}=\sum_{w\in\mathcal W}\lvert w\rangle\langle w\rvert\otimes U_w.
$$

它把每个程序索引关联到其数据变换。这个数学定义没有证明一个有限装置可以免费执行无界长度程序。

程序态 $\sum_w c_w\lvert w\rangle$ 与数据 $\lvert \psi\rangle$ 经过该算符后成为
$\sum_w c_w\lvert w\rangle U_w\lvert \psi\rangle$。若保留程序，整体仍是相干演化；若丢弃程序，数据通道为

$$
\mathcal E(\rho)=\sum_w|c_w|^2U_w\rho U_w^\dagger.
$$

<a id="statement-10-2"></a>

#### 命题 10.2（丢掉程序通常不能得到一个新酉门）

上述通道是酉通道，当且仅当所有正权 $U_w$ 仅差整体相位。

**证明。**

设 $\lvert u_w\rangle=(I\otimes U_w)\lvert \Phi_d\rangle$，其中
$\lvert \Phi_d\rangle=d^{-1/2}\sum_j\lvert j,j\rangle$。通道的归一化 Choi 矩阵为
$\sum_w|c_w|^2\lvert u_w\rangle\langle u_w\rvert$。酉通道对应秩一 Choi 矩阵；正半定秩一和仍为秩一，当且仅当全部正权向量共线。这恰等价于 $U_w$ 只差相位。可数和的情形可由非负二次型及其正交补同样证明。

∎

<a id="thm-noprogram"></a>

#### 定理 10.3（固定有限处理器的精确程序限制）

设同一个固定酉处理器对任意数据态满足

$$
\mathcal U(\lvert p_U\rangle\otimes\lvert \psi\rangle)
=\lvert q_U\rangle\otimes U\lvert \psi\rangle.
$$

若 $U,V$ 不是同一射影酉操作，则 $\langle p_U,p_V\rangle=0$。因此有限维纯程序寄存器不能确定性、精确地表示全部酉门。

**证明。**

对任意两个数据向量保持内积，得到算符恒等式

$$
\langle p_U,p_V\rangle I
=\langle q_U,q_V\rangle U^\dagger V.
$$

若右侧系数非零，$U^\dagger V$ 必为标量，与前提矛盾。所以两边系数都为零。射影不同的门要求两两正交的程序向量，而有限维空间只有有限多个这样的向量。若原先只知数据输出对所有纯输入都是 $U\lvert \psi\rangle$，线性性和基向量叠加还迫使纯环境输出不依赖 $\psi$，故上述乘积输出形式也随之成立。

∎

这是 Nielsen–Chuang 的不可编程结果[[9](#ref-noprogram)]。它允许我们精确表达内生观察者的一个部分：程序、记录、边界选择也在联合空间内；忽略它们会改变可见操作。它不妨碍变长有限电路的近似通用性，也不证明任意自指过程收敛。

<a id="sec-11"></a>

## 11. 连目标关系也未知：后验谱的变分约束

为了把“关系本身也是预测”写成可检验问题，先固定已标定的有限目标假设
$\{V_j,\pi_j\}$，$\pi_j\ge0$、$\sum_j\pi_j=1$。假设之间可能是完全不同的门，而非只差某一测量数值。

<a id="statement-11-1"></a>

#### 定义 11.1（后验门风险）

用酉 Choi 向量 $\lvert v_j\rangle=(I\otimes V_j)\lvert \Phi_d\rangle$ 定义

$$
M_\pi=\sum_j\pi_j\lvert v_j\rangle\langle v_j\rvert,\qquad
\ell(U,V)=1-\frac{|\operatorname{Tr}(V^\dagger U)|^2}{d^2}.
$$

不限制门表达能力时的最优预测风险为
$\mathcal R(\pi)=\min_{U\in\operatorname{U}(d)}\sum_j\pi_j\ell(U,V_j)$。

<a id="thm-bayes"></a>

#### 定理 11.2（谱约束与不可消失的关系风险）

$$
\boxed{\mathcal R(\pi)
=1-\max_{U\in\operatorname{U}(d)}\langle u\rvert M_\pi\lvert u\rangle
\ge1-\lambda_{\max}(M_\pi).}
$$

等号当且仅当最大本征空间含有一个归一化的酉 Choi 向量。并且

$$
\mathcal R(\pi)=0
\iff \text{所有正权 }V_j\text{ 仅差整体相位。}
$$

**证明。**

$\langle v_j,u\rangle=\operatorname{Tr}(V_j^\dagger U)/d$，求和得等式。酉 Choi 向量只是全单位球的一个紧子集；Rayleigh 商给谱上界，其等号条件就是最大本征空间与该子集相交。若风险为零，每一个正权非负损失均为零；Hilbert–Schmidt Cauchy–Schwarz 等号要求 $V_j$ 与同一个 $U$ 成比例，即只差相位。反向显然。

∎

例如目标等概率为 $I$ 或 $iX$，两条 Choi 向量正交，$\lambda_{\max}=1/2$；取预测 $I$ 即达到风险 $1/2$。再通用的门菜单，也不能在没有额外记录时把这个评分下的风险降到零。编译误差可消失与目标关系已被辨识，是两个命题。

<a id="statement-11-3"></a>

#### 命题 11.3（记录只保证平均最优风险下降）

若实际记录 $a$ 由同一个已给定联合律产生，后验为 $\pi^{(a)}$，则

$$
\sum_a p(a)\mathcal R(\pi^{(a)})\le\mathcal R(\pi).
$$

**证明。**

对每个后验采用原先的最优门也是可行策略；后验最小值不高于该策略的条件风险。取平均并用全期望公式即得。

∎

不等式不保证每个观测分支都下降。它还依赖已标定的共同联合律和明确评分。若连原生门也由未知参数 $\theta$ 决定，就必须把候选字写成 $U_w(\theta)$，风险写成
$\int\ell(U_w(\theta),V(\theta))\,\pi(d\theta)$；对每个 $\theta$ 分别通用，不等于同一个未知参数下的统一编译保证。酉矩阵的普通平均一般也不是酉门。

<a id="sec-12"></a>

## 12. 最新同源观察前沿对编译理论的启示

项目新文的来源是隐藏 $Q\sim\mu$、$\mu((0,1))=1$，独立根 $X_0\sim\operatorname{Bernoulli}(b)$、$a,b>0$、$a+b=1$，给定 $(Q,X_0)$ 后的两条实际臂条件独立且各服从

$$
P_Q=\begin{pmatrix}1-Q&Q\\1&0\end{pmatrix}.
$$

观察者保留原独立种子；查询新边、遇首个 $00$ 标记停止，也可在无标记分支自愿停。它没有给观察者 $Q$ 参数口或免费重置信源。定义

$$
M_j=\int q^j\mu(dq),\quad A_j=M_j-M_{j+1},\quad
v_j=bA_{j-1}-aA_j,\quad J_N=\sum_{j=0}^{N-1}M_j.
$$

该文定理 3.2 在同一策略上同时达到风险与平均已付成本：

$$
\begin{aligned}
K_{2N}&=2J_N-a+aM_N+\sum_{m=1}^{N-1}\min(0,v_m),\\
K_{2N+1}&=2J_N-a+(1+a)M_N+\sum_{m=1}^{N}\min(0,v_m),\\
R_{2N}^*&=R_{2N+1}^*=\min(aM_{N+1},bM_N)\quad(N\ge1).
\end{aligned}
$$

这里 $K_0=0,K_1=1$；$R_0^*=\min(a,b)$、$R_1^*=\min(aM_1,b)$。
证明的关键是各此前偶数深度的形状指标对成本线性；最后偶数深度的形状影响风险却不再进入已付前缀成本，因此可以共同优化。不是把两个分别存在的最优策略拼在一起。

其定理 4.2 和 5.2 进一步把所有合法策略归约到原种子可实现的重放时域分布。记 $\nu$ 为原独立、解码时可见的种子律，$h\in\mathbb{N}_0\cup\{\infty\}$，$R_\infty^*=0$、$K_\infty=\lim_hK_h$，并约定 $0\cdot\infty=0$。则

$$
F_\nu(B)=\inf\left\{\sum_h p_hR_h^*:p\in\mathsf P_\nu,
\ \sum_h p_hK_h\le B\right\}.
$$

原种子无原子时，最优存在且可只使用至多两个时域；两者不必相邻。若原种子有原子，不能免费改成任意实数 Bernoulli 权重。源文明确不由此供应计算、精确矩求值、存储或真实时间成本。

这启发下面的有限编译对应，但它不是将该经典来源直接量子化。

<a id="statement-12-1"></a>

#### 命题 12.1（有限菜单的平均预算前沿）

设有限候选字有成本 $C_j$ 和已声明的平均损失 $r_j$，允许保留选择记录的随机编译。若实际种子能实现任意所需混合，则

$$
\min\left\{\sum_jp_jr_j:p_j\ge0,\ \sum_jp_j=1,
\ \sum_jp_jC_j\le B\right\}
$$

在可行时存在一个至多支持两个字的最优解。

**证明。**

可行集合是紧多面体，线性目标可在极点达到。若极点至少有三个正分量，可在这三个位置选非零向量 $h$ 满足
$\sum h_j=\sum C_jh_j=0$。足够小的正负扰动仍非负且保留约束，将原点写成两不同可行点的中点，矛盾。

∎

若把选择记录丢掉，输出一般是随机酉通道而非一个相干目标门，第[10](#sec-10)节已经证明。平均损失最优不能冒充最坏输入、每次执行或相干门误差最优。可测最优策略的存在也不能代替实际种子实现、有效后验和编译算法。

<a id="sec-13"></a>

## 13. 黎曼猜想的参考地位与尚待完成的接口

本轮所有普适性、递归误差与变分定理都不需要 RH。前稿中的黎曼接口要求把算术数据与特定完成函数的全部零点精确对应；任意黄金门酉性、单位圆谱或一个变分极小值不能替代这个对应。本稿实际使用的谱约束是可直接核验的：原生门单位根谱、相对门的无限阶迹、后验 Choi 谱，以及原生字的算术误差界。

本文建立的完整链条为

$$
\boxed{\begin{gathered}
\text{固定 }K+\text{明确编码与非交换地址}\\
\Downarrow\\
\Sigma\subset\operatorname{SU}(2)\text{ 的稠密性与相位确定性}\\
\Downarrow\\
\text{同类子门的交换子递归编译及误差证书}\\
\Downarrow\\
\text{正成本 Bellman 唯一解与规范化静态变分。}
\end{gathered}}
$$

两端口 $G$ 则在明确接线架构下把单比特能力与纠缠组合成多比特普适性。

仍应单独完成的研究接口是：

1. 对两端口候选给出一个共同全局编码，使全部允许 $G_{ij}$ 与原生多原子地址操作交织，并逐项核算路由、辅助位和泄漏；一个 $J_2$ 不能代替这一组相容等式。
2. 给出带认证覆盖半径的初始黄金网、目标精度输入合同和具体编译实现；本文证明存在与递归误差，不报告已经算出的最短网或某目标最短字。
3. 当门、尺子和目标关系同时不确定时，以同一真实校准记录建立联合后验及鲁棒编译误差；不能把各参数分别可编译直接提升为未知参数下统一成功。

因此，“类似 NAND 的基础量子门”现在有一个明确的条件答案：单一黄金门型在合适的相容接线中近似通用，而且能以同一门型递归编译自身的纠偏子问题。观察的增长可由最优程序与记录增长来刻画；通用性、最优性、目标可辨识性和量子公理的物理起源仍是分别有前件的命题。

<a id="sec-bibliography"></a>

## 文献与项目来源

<a id="ref-project"></a>

1. The Omega Institute. <em>trureturing</em>，研究分支 `dev`。不可变提交
[`837df9a75450`](https://github.com/the-omega-institute/trureturing/tree/837df9a7545012a9e669c61716dac078f5552d96)，2026-10-30。本稿项目链接均固定至此提交；完整 SHA 见第 1 节。

<a id="ref-v15"></a>

2. AURIC research continuation.
[<em>黄金门的 NAND 式普适性与精确实现的算术边界</em>](https://github.com/the-omega-institute/trureturing/blob/837df9a7545012a9e669c61716dac078f5552d96/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md), v15. Author manuscript conversion; especially §§3–10.

<a id="ref-v16"></a>

3. AURIC research continuation.
[<em>预测、递归、最优化与变分</em>](https://github.com/the-omega-institute/trureturing/blob/837df9a7545012a9e669c61716dac078f5552d96/docs/develop/theory/AURIC_PREDICTION_RECURSION_OPTIMIZATION_AND_VARIATION_V16.md), v16. Author manuscript conversion; static action, finite budgets and Galois parity bound.

<a id="ref-v18"></a>

4. AURIC research continuation.
[<em>三角剖分、塌缩与递归酉门</em>](https://github.com/the-omega-institute/trureturing/blob/837df9a7545012a9e669c61716dac078f5552d96/docs/develop/theory/AURIC_TRIANGULATION_COLLAPSE_AND_RECURSIVE_UNITARY_GATES_V18.md), v18. Author manuscript conversion; controlled lifts, braiding and records.

<a id="ref-stopped"></a>

5. The Omega Institute.
[<em>Recursive relational observation: stopped mean cost and spatial risk on one source</em>](https://github.com/the-omega-institute/trureturing/blob/837df9a7545012a9e669c61716dac078f5552d96/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_STOPPED_MEAN_SPATIAL_RISK.md), especially Theorems 3.2, 4.2, 5.2 and Proposition 5.3.

<a id="ref-barenco"></a>

6. A. Barenco. <em>A universal two-bit gate for quantum computation</em>. Proceedings of the Royal Society A 449 (1995), 679–683.
[arXiv:quant-ph/9505016](https://arxiv.org/abs/quant-ph/9505016).

<a id="ref-flw"></a>

7. M. H. Freedman, M. J. Larsen, Z. Wang.
<em>The two-eigenvalue problem and density of Jones representation of braid groups</em>.
Communications in Mathematical Physics 228 (2002), 177–199. Fibonacci representations, §6, Theorem 6.2.
[arXiv:math/0103200](https://arxiv.org/pdf/math/0103200).

<a id="ref-sk"></a>

8. C. M. Dawson, M. A. Nielsen. <em>The Solovay–Kitaev algorithm</em>.
Quantum Information and Computation 6 (2006), 81–95.
[arXiv:quant-ph/0505030v2](https://arxiv.org/pdf/quant-ph/0505030), especially §§2–4.

<a id="ref-noprogram"></a>

9. M. A. Nielsen, I. L. Chuang. <em>Programmable quantum gate arrays</em>.
Physical Review Letters 79 (1997), 321–324.
[arXiv:quant-ph/9703032](https://arxiv.org/pdf/quant-ph/9703032).

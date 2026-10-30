<a id="auric-v15"></a>

# AURIC 黄金门的 NAND 式普适性与精确实现的算术边界

**AURIC 研究续稿 · 从有限阶反射、连续闭包到奇偶选择定理**

**v15.0 · 2026 年 10 月 29 日**

**固定项目版本。** 默认研究分支 `dev`，提交

`52ce13dc5e8c2d73f96845d0a8aad75917c14626`

提交时间：2026 年 10 月 29 日 20:54:36（Asia/Singapore）。

> **转换说明（编者）。** 本文完整转换用户提供的同名 XeLaTeX 稿件，采用独立 Markdown 数学表达；陈述沿用源稿每节共享的编号，公式保留源稿显式标签。作者关于快照审计、外部定理、推进与新颖性的表述均按原稿保留并归属于作者；本次转换不主张重新认证这些历史报告、数学定理或物理实现。

> **格式说明（编者）。** 源稿中的显示公式、显式 tag 标签、label 锚点及 XeLaTeX 宏已转换为 GitHub Markdown/KaTeX 兼容形式；未改变公式、证明、假设、例证、表格、链接或参考文献内容。未运行 Lean、数值实验、最短门搜索或硬件认证。

<a id="sec-abstract"></a>

## 摘要

本稿继续研究同一固定 AURIC 黄金门能否承担 NAND 的普适生成角色。我们给出不依赖多体编织密度定理的单比特初等证明，完整分类门的十种幂次，并证明仅用五次幂反射有不可消除的复相位误差。随后通过逐个融合路径基底和旁观者交织，补全项目原文额外列出的编码桥；多比特近似通用性仍明确调用标准 Fibonacci 编织定理。另一方面，固定最近邻门保留每一条相邻占据缺陷；黄金矩阵的代数整数结构使有限完整记录中的有理概率只能为零或一；更强的分级与 Galois 正性论证排除固定计算基编码中的精确奇偶翻转，因而排除带复原辅助位的精确 NOT、CNOT、Toffoli 与可逆 NAND。针对可逆 NAND 的非恒定奇偶变化，我们还证明丢弃一个固定纯环境也不能消除这一障碍。有限精度近似与这些精确障碍相容。最后给出黄金偏币的条件去偏和完整停止记录，说明后选择与无限重复为何改变可实现集合。所有数学论证为纸面证明；本稿不报告数值实验、最短门搜索、Lean 认证或硬件实现。

**核心结论。** AURIC 黄金门在指定接线与编码下具有单一门类型的近似量子普适性；其有限字的精确表达能力受到明确算术约束。两种性质必须同时进入“NAND 式基础门”的定义。

## 目录

1. [项目进展、问题范围与证明层次](#sec-1)
2. [先定义 NAND 式的量子普适性](#sec-2)
3. [五模式、黄金投影与固定矩阵](#sec-3)
4. [两处同一种门：单比特连续闭包的初等证明](#sec-4)
5. [取反足不足够：全部幂次的二维分类](#sec-5)
6. [补全多比特编码桥与近似 NAND 定理](#sec-6)
7. [为何它不是无编码全寄存器万能门](#sec-7)
8. [有限黄金电路的算术：非平凡有理概率不存在](#sec-8)
9. [比有理概率更强：精确取反的奇偶选择定理](#sec-9)
10. [更强形式：同奇偶压缩块永远可逆](#sec-10)
11. [概率、递归与公平读出的三种资源层次](#sec-11)
12. [静态相容图的解释：门类型、接线与闭包](#sec-12)
13. [当前结论与下一步可核查的问题](#sec-13)

[参考文献](#sec-bibliography)

<a id="sec-1"></a>

## 1. 项目进展、问题范围与证明层次

<a id="sec-1-1"></a>

### 1.1. 本轮核对的最新进展

相对前稿固定的 `6936d5e`，本轮快照的 theory 树共有 1001 个文件，9 个路径变化，其中 3 个新增。我们按主题读取并逐项核对了 14 个目标文件的 Git blob；这不等于审核了全仓全部证明。[黄金门正文](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/AURIC_FIXED_GOLDEN_GATE_AND_BRAID_COMPATIBILITY_ZH.md)、核心融合路径、固定参考编译器、相干重构续卷和选择演算均未变化。黄金门正文是此前稿件的入库转换，入库本身不构成独立认证。

最新修改主要涉及同一实际联合律上的可实现性、源依赖和真实切面恢复。[全局与局部秩文档](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_GLOBAL_LOCAL_RANK_COMPATIBILITY_AND_RESET_VARIANCE_OBSTRUCTION.md) §§10–11 区分分别拟合与共同过程，仍保留额外严格谱条件；[三角源文档](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/TRIANGLE_NETWORK_SOURCE_INDEPENDENCE_AND_FIBER_GEOMETRY.md) §14 研究四符号饱和中的实际源结构；[真实切面恢复文档](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT.md) 要求已取得的真实递归律与实际读出条件。这些进展要求本稿把相容模型、可执行菜单和读出记录写在同一个协议中，并不直接新增黄金门密度证明。

<a id="sec-1-2"></a>

### 1.2. 哪些属于输入，哪些在本稿证明

<a id="ass-model"></a>

#### 假设 1.1（固定操作模型）

有限合法路径以正交基组成复 Hilbert 空间；局部算符采用下文明确的固定矩阵 $K$。同一种 $K$ 可以作用在指定相邻三位置，允许有限次正向重复。初始化采用明确的计算基边界及逻辑编码。概率部分采用 Born 标定；若使用中间测量，必须说明完整结果、反馈菜单、失败分支和终止条件。

本稿直接证明二维密度、幂分类、编码桥、全寄存器障碍、代数整数概率、奇偶选择及相应误差界。多比特密度引用已知 Fibonacci 编织理论（[5](#ref-flw)、[6](#ref-flwdensity)、[7](#ref-drw)）；所用固定 $F,R$ 数据也来自该理论。我们不把五种标签的数量本身当成复数域、Born 规则或物理拓扑保护的证明。文中的“新推进”是相对此前研究链的推进，不是对 Fibonacci 门和数论编译文献的历史原创性声明（[8](#ref-kbs)、[9](#ref-ky)）。

<a id="sec-2"></a>

## 2. 先定义 NAND 式的量子普适性

<a id="def-universal"></a>

#### 定义 2.1（单门类型的编码近似普适性）

固定局部门 $K$、可调用地址、编码等距嵌入 $J_n:(\mathbb{C}^2)^{\otimes n}\to\mathcal H_{N(n)}$ 及初始化规则。若对每个 $n$、$U\in U(2^n)$ 和 $\varepsilon>0$，存在只由这些地址上的 $K$ 组成的有限正向门字 $C$，使某个整体相位 $\gamma$ 满足

<a id="eq-universal"></a>

$$
\|CJ_n-e^{i\gamma}J_nU\|_{\mathrm{op}}<\varepsilon,
\tag{2.1}
$$

则称其为该资源条件下的单门类型编码近似普适性。

该定义不允许把任意额外酉门、任意初态或免费后选择藏在“接线”一词中。它也不声称任意 $U$ 具有关于 $n$ 的多项式长度描述；若目标本来就需指数多参数，普适性不会压缩这些参数。

<a id="prop-nand"></a>

#### 命题 2.2（NAND 的可逆扩展与遗失信息）

令 $f(a,b)=1\oplus ab$。下式是三比特酉置换：

<a id="equation-2-2"></a>

$$
V_f|a,b,t\rangle=|a,b,t\oplus f(a,b)\rangle,\qquad
V_f=X_t\,\operatorname{Toffoli}_{a,b;t},\quad V_f^2=I.
\tag{2.2}
$$

当 $t=0$ 时目标位给出 NAND。若要求把两比特输入纯粹压缩成一比特 NAND 输出并由环境保持可逆性，即

<a id="equation-2-3"></a>

$$
W|a,b\rangle=|f(a,b)\rangle|e_{ab}\rangle
\tag{2.3}
$$

为等距映射，则环境维数至少为 $3$，且该下界可以达到。

**证明。**

对固定 $a,b$，目标位或不动或翻转，因此 $V_f$ 是双射，平方为恒等。$f=1\oplus ab$ 给出与 $X_t$、Toffoli 的乘积关系。三个输入 $00,01,10$ 的 $f$ 都是 $1$，等距性迫使其三个环境向量两两正交，所以环境维数至少为三。取三个正交环境基向量分别对应这三个输入，并让 $11$ 复用其中任一个环境向量；输出位 $0$ 已使最后一个向量与前三个正交，故三维环境足够。

∎

这里的 NAND 真值表指定了一项经典读出，$V_f$ 则还指定叠加输入的相位和相干性。仅在四个经典输入上答对，不足以认证同一个量子酉门。历史上已有单一二比特通用门（[10](#ref-barenco)）；因此下文的三位置结构不是无条件的最小物理门元数。

<a id="sec-3"></a>

## 3. 五模式、黄金投影与固定矩阵

令 $\varphi=(1+\sqrt5)/2$、$\zeta=e^{3\pi i/5}$，并约定 $n=|1\rangle\langle1|$、$X=|0\rangle\langle1|+|1\rangle\langle0|$。三位置按左、中、右记为 $L,C,R$。定义

$$
g=(I-n_L)(I-n_R),\qquad
Q_C=\varphi^{-1}(I-n_C)+\varphi^{-2}n_C+\varphi^{-3/2}X_C,

$$

<a id="eq-k"></a>

$$
\mathcal P=n_Ln_R+gQ_C,\qquad
\boxed{K=\zeta\,[I+(\zeta-1)\mathcal P].}
\tag{3.1}
$$

未写出的张量单位一律理解为存在。三个位置不含相邻 $11$ 的五种模式为

$$
(000,100,010,001,101)\longleftrightarrow(\mathrm{null},1,2,3,13).

$$

这是标签约定；$13$ 表示联合标签 $F[1,3]$。

<a id="thm-spectrum"></a>

#### 定理 3.1（固定黄金门的基本谱性质）

$\mathcal P$ 是实正交投影，$K$ 是整个三比特空间上的酉矩阵，保留上述五维合法子空间，而且

<a id="equation-3-2"></a>

$$
K^r=\zeta^r(I-\mathcal P)+\zeta^{2r}\mathcal P,
\qquad K^{10}=I,\quad K^{-1}=K^9,\quad K^5=2\mathcal P-I.
\tag{3.2}
$$

**证明。**

按左右位分块。左右都是 $0$ 时，$Q_C=vv^T$，其中
$v=(\varphi^{-1/2},\varphi^{-1})^T$，且 $v^Tv=\varphi^{-1}+\varphi^{-2}=1$。左右都是 $1$ 时投影为单位，其余两种左右模式为零。因此 $\mathcal P^2=\mathcal P=\mathcal P^\dagger$。其两个正交谱分量上的 $K$ 相位分别为 $\zeta$ 和 $\zeta^2$，模均为一；取幂即得式 (3.2)。唯一非对角耦合是 $000\leftrightarrow010$，故不产生相邻 $11$。

∎

<a id="sec-3-1"></a>

### 3.1. 黄金数与相位比例怎样进入相容关系

项目[融合路径文档](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md) §§12–14 的邻接矩阵为

$$
A=\begin{pmatrix}0&1\\1&1\end{pmatrix}.

$$

若要求严格正扩展权重 $d=(1,d_\tau)$ 满足 $Ad=\delta d$，则 $d_\tau=\delta$、$1+\delta=\delta^2$，唯一正根为 $\delta=\varphi$。相应路径投影满足

<a id="equation-3-3"></a>

$$
P_iP_{i+1}P_i=\varphi^{-2}P_i,
\qquad [P_i,P_j]=0\quad(|i-j|\ge2).
\tag{3.3}
$$

<a id="prop-braid"></a>

#### 命题 3.2（非标量编织相位比例）

设 $P,Q$ 为不同投影，$PQP=\lambda P$、$QPQ=\lambda Q$，$\lambda=\varphi^{-2}$。对 $B_P=s[I+(z-1)P]$、$B_Q=s[I+(z-1)Q]$，有

<a id="equation-3-4"></a>

$$
B_PB_QB_P-B_QB_PB_Q
=s^3(z-1)[z+\lambda(z-1)^2](P-Q).
\tag{3.4}
$$

若 $s\ne0$、$z\ne1$，则编织关系成立当且仅当 $z=e^{\pm3\pi i/5}$。

**证明。**

令 $u=z-1$，展开三重乘积，交叉项 $PQ+QP$ 抵消，剩下
$[u+u^2+\lambda u^3](P-Q)$，得到 (3.4)。其零条件是
$z^2+(\lambda^{-1}-2)z+1=0$，而 $\lambda^{-1}-2=\varphi^{-1}$。两根的和为 $-\varphi^{-1}=2\cos(3\pi/5)$，积为一，故为所述两相位。

∎

相容性确定这里的非平凡*相位比例*；共同相位 $s$ 仍自由。本稿采用标准手性及 $s=z=\zeta$。式 (3.3)–(3.4) 的编织结论仅在合法路径表示中成立，不能直接推广到整个八维空间。

<a id="sec-4"></a>

## 4. 两处同一种门：单比特连续闭包的初等证明

<a id="sec-4-1"></a>

### 4.1. 无需猜测的二维编码

对一个逻辑比特取

<a id="equation-4-1"></a>

$$
\widehat J_1|q\rangle=|1\,0\,q\,0\,1\,0\rangle.
\tag{4.1}
$$

这些位置依次标为 $b_{-1},b_0,b_1,b_2,b_3,b_4$。分别在中心 $b_0$ 和 $b_1$ 调用同一个 $K$。第一处左控制位为一，投影退化为 $n_1$；第二处两邻位为零，作用为 $Q_C$。两者都精确保留编码，逻辑投影恰为

<a id="equation-4-2"></a>

$$
P=|1\rangle\langle1|,\qquad
Q=\begin{pmatrix}\varphi^{-1}&\varphi^{-3/2}\\\varphi^{-3/2}&\varphi^{-2}\end{pmatrix},
\qquad \operatorname{Tr}(PQ)=\varphi^{-2}.
\tag{4.2}
$$

记限制后的门为 $K_P,K_Q$。以下论证只使用这两个明确矩阵。

<a id="lem-trace"></a>

#### 引理 4.1（迹的代数共轭判据）

若 $U\in SU(2)$ 的实迹 $t$ 有某个代数共轭不属于 $[-2,2]$，则 $U$ 无限阶，其幂的闭包是某一连续圆环。

**证明。**

若 $U$ 有限阶，其特征值为单位根 $\lambda,\lambda^{-1}$。$t=\lambda+\lambda^{-1}$ 的每一个代数共轭都是另一个单位根与其逆之和，必在 $[-2,2]$，矛盾。无限阶 $SU(2)$ 元素酉对角化后是角度为无理 $2\pi$ 倍数的圆旋转，其幂在该圆上稠密。

∎

<a id="lem-circles"></a>

#### 引理 4.2（两个圆的生成）

若闭矩阵子群包含 $\exp(tX)$、$\exp(tY)$，$t\in\mathbb{R}$，且 $X,Y\in\mathfrak{su}(2)$ 实线性无关，则该子群包含 $SU(2)$。

**证明。**

以 $i\sigma_x,i\sigma_y,i\sigma_z$ 为实基，交换子是非零常数倍的叉积。因此 $X,Y,[X,Y]$ 张成 $\mathfrak{su}(2)$。闭子群的单位连通分支包含整个这个 Lie 代数及其指数，故包含连通群 $SU(2)$。

∎

<a id="thm-density"></a>

#### 定理 4.3（黄金门的二维射影普适性）

令 $\mu_r$ 为 $r$ 次单位根集，则

<a id="equation-4-3"></a>

$$
\boxed{\overline{\langle K_P,K_Q\rangle}
=\{U\in U(2):\det U\in\mu_{10}\}.}
\tag{4.3}
$$

特别地，忽略整体相位后可逼近全部单量子比特酉操作。

**证明。**

取 $R_P=K_P^5=2P-I$、$R_Q=K_Q^5=2Q-I$。它们都是实反射，其乘积属于 $SO(2)$，且

$$
\operatorname{Tr}(R_PR_Q)=4\operatorname{Tr}(PQ)-2=4-2\sqrt5.

$$

其代数共轭 $4+2\sqrt5>2$，由引理 [4.1](#lem-trace)，闭包包含整个 $SO(2)$ 圆。

为写出生成元，交换两个基向量，把 $P$ 写成 $\operatorname{diag}(1,0)$。此时
$K_P=\operatorname{diag}(\zeta^2,\zeta)$。令

$$
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
K_PJK_P^\dagger=
\begin{pmatrix}0&-\zeta\\\zeta^{-1}&0\end{pmatrix}
=\cos\alpha\,J-i\sin\alpha\,\sigma_x,

$$

其中 $\alpha=3\pi/5$。因 $\sin\alpha\ne0$，这两个连续圆的生成元不共线，引理 [4.2](#lem-circles) 给 $SU(2)$ 在闭包中。另一方面 $\det K_P=\det K_Q=\zeta^3$，是本原十次单位根，故闭包行列式只能在 $\mu_{10}$。每个允许行列式的陪集由某个 $K_P^r SU(2)$ 填满，得到等式。

∎

只在同一地址重复 $K$，至多有十种操作。连续表达能力来自两个相容但不交换的地址之间的关系。连续圆是有限门字在算符范数下的闭包；每个实际有限精度近似仍是有限字。该证明没有从单个有限周期擅自推断无限维资源。

<a id="sec-5"></a>

## 5. 取反足不足够：全部幂次的二维分类

<a id="thm-square"></a>

#### 定理 5.1（平方门也具有二维射影普适性）

<a id="equation-5-1"></a>

$$
\overline{\langle K_P^2,K_Q^2\rangle}
=\{U\in U(2):\det U\in\mu_5\}.
\tag{5.1}
$$

**证明。**

令 $A=K_P^2$、$B=K_Q^2$。它们均有五阶。为计算，写
$\widehat A=\zeta^{-3}A=\cos\alpha I+i\sin\alpha R_P$，对 $B$ 同理。实际门字
$C=AB^{-1}=\widehat A\widehat B^{-1}$ 属于 $SU(2)$，且

$$
\operatorname{Tr} C=2\cos^2\alpha+2(2\varphi^{-2}-1)\sin^2\alpha=2-\sqrt5.

$$

这里只使用 $\cos^2\alpha=(3-\sqrt5)/8$ 与 $\sin^2\alpha=(5+\sqrt5)/8$。共轭 $2+\sqrt5>2$，故 $C$ 的闭包为连续圆环 $T$。

若 $A$ 正规化 $T$，其共轭在 $T$ 的一维 Lie 代数上只能取 $+1$ 或 $-1$；$A^5=I$ 排除 $-1$，所以 $A$ 中心化 $T$，从而与 $C$ 交换。代入 $C=AB^{-1}$ 得 $A$ 与 $B$ 交换，但

$$
[A,B]=\zeta^4(\zeta^2-1)^2[P,Q]\ne0,

$$

矛盾。因此 $T$ 与 $ATA^{-1}$ 是不同轴的圆，引理 [4.2](#lem-circles) 给出 $SU(2)$。行列式由 $\zeta^6$ 生成，恰为 $\mu_5$；陪集论证同定理 [4.3](#thm-density)。

∎

<a id="cor-powers"></a>

#### 推论 5.2（十类幂的完整分类）

在式 (4.2) 的二维编码中，有下表。

| $k\bmod10$ | $\overline{\langle K_P^k,K_Q^k\rangle}$ | 射影能力 |
| --- | --- | --- |
| $0$ | $\{I\}$ | 平凡 |
| $5$ | $O(2)$，在共同实基中 | 实正交操作 |
| $1,3,7,9$ | $\{U:\det U\in\mu_{10}\}$ | 全部 $PU(2)$ |
| $2,4,6,8$ | $\{U:\det U\in\mu_5\}$ | 全部 $PU(2)$ |

**证明。**

当 $\gcd(k,10)=1$，$K$ 是 $K^k$ 的某个正幂；当 $\gcd(k,10)=2$，$K^k$ 与 $K^2$ 生成同一循环子群，逐地址应用即可。$k=5$ 时所有门字实正交，两个反射已给出稠密的 $SO(2)$，再加一个反射得到 $O(2)$。$k=0$ 显然。所有逆门都能由正向重复得到，所以群记号没有另行添加门类型。

∎

<a id="thm-real"></a>

#### 定理 5.3（纯反射的不可消除相位误差）

对 $S_0=\operatorname{diag}(1,i)$，有

<a id="equation-5-2"></a>

$$
\inf_{O\in O(2),\,\gamma\in\mathbb{R}}
\|O-e^{i\gamma}S_0\|_{\mathrm{op}}=\sqrt{2-\sqrt2}.
\tag{5.2}
$$

对任意实矩阵的复线性编码等距嵌入 $J:\mathbb{C}^2\to\mathbb{C}^D$，任意实正交 $O$ 也满足
$\inf_\gamma\|OJ-e^{i\gamma}JS_0\|_{\mathrm{op}}\ge\sqrt{2-\sqrt2}$。

**证明。**

$O|+\rangle$ 是实单位向量，而 $S_0|+\rangle=|+i\rangle$。任意二维实单位向量 $v$ 都有 $|\langle v|+i\rangle|^2=1/2$，故允许最佳整体相位后的向量距离仍至少是 $\sqrt{2-\sqrt2}$。取 $O=I$、$\gamma=-\pi/4$，两个对角差模均为该值，达到下界。一般编码时 $OJ|+\rangle$ 仍实；由 $J|0\rangle,J|1\rangle$ 实正交，其与 $JS_0|+\rangle$ 的重叠模至多 $1/\sqrt2$，相同下界成立，即使物理输出泄漏也不改善。

∎

**适用范围。**  $K^5$ 是相干反射，但并非经典比特取反。此处排除的是固定复线性实编码的复酉普适性；用额外 rebit 保存实部与虚部的算法模拟是不同编码问题（[11](#ref-rg)）。幂分类只在二维编码中证明，不能自动推出全链只用 $K^2$ 或 $K^5$ 的多比特计算能力。

<a id="sec-6"></a>

## 6. 补全多比特编码桥与近似 NAND 定理

<a id="sec-6-1"></a>

### 6.1. 从四任意子块到合法比特词的逐基对应

令 $V_N^c$ 为 Fibonacci 前缀路径空间，其基底满足

$$
x_0=\mathbf{1},\quad x_N=c,\qquad
x_{j+1}\in\mathsf N(x_j,\tau),\qquad
\tau\otimes\tau=\mathbf{1}\oplus\tau.

$$

采用项目既定的标准 $F,R$ 数据：所有一维 $F$ 块为 $1$，唯一非平凡二维块为

<a id="equation-6-1"></a>

$$
F=\begin{pmatrix}\varphi^{-1}&\varphi^{-1/2}\\\varphi^{-1/2}&-\varphi^{-1}\end{pmatrix},
\qquad R=\operatorname{diag}(\zeta^2,\zeta).
\tag{6.1}
$$

局部编织 $B_i=\zeta[I+(\zeta-1)P_i]$ 只改变 $x_i$，其系数仅依赖 $x_{i-1},x_i,x_{i+1}$。

<a id="thm-bridge"></a>

#### 定理 6.1（真空块编码桥的显式证明）

取 $m=4n-1$。对逻辑词 $q=(q_1,\ldots,q_n)$ 规定

<a id="equation-6-2"></a>

$$
b_{4r-3}=q_r,\quad b_{4r-2}=0,\quad b_{4r-1}=1
\quad(1\le r\le n),\qquad b_{4r}=0\quad(r<n).
\tag{6.2}
$$

再加入 $b_{-1}=1,b_0=0,b_{m+1}=0$ 得到 $\widehat J_n$，共 $4n+2$ 个位置。该编码与 $n$ 个四任意子真空块的标准编码逐个基向量对应。在此对应下，前 $4n$ 个任意子的每个编织生成元 $B_i$，$1\le i\le4n-1$，精确对应中心 $j=i-1$ 上的同一矩阵 $K$。

**证明。**

一个四 $\tau$、总荷为真空的块恰有两条路径
$(\mathbf{1},\tau,a_r,\tau,\mathbf{1})$，取 $a_r=\mathbf{1}$ 当且仅当 $q_r=1$。将 $n$ 个块在真空端点串接，得到

<a id="equation-6-3"></a>

$$
x_{4r-4}=\mathbf{1},\quad x_{4r-3}=\tau,\quad
x_{4r-2}=a_r,\quad x_{4r-1}=\tau,\quad x_{4r}=\mathbf{1}.
\tag{6.3}
$$

不同逻辑词对应不同正交基向量，故这是从 $(V_4^\mathbf{1})^{\otimes n}$ 到 $V_{4n}^\mathbf{1}$ 的等距嵌入。真空接口的单位结合映射在所给规范中都是一维恒等；把块树写成前缀路径不产生额外路径混合或相位。

定义旁观者等距映射

$$
\iota:V_{4n}^\mathbf{1}\to V_{4n+1}^{\tau},\quad
\iota|x_0\cdots x_{4n}\rangle=|x_0\cdots x_{4n},\tau\rangle.

$$

$P_i$ 对 $i\le4n-1$ 不改变 $x_{4n}=\mathbf{1}$，也不依赖新末位，故逐个矩阵元给出

<a id="equation-6-4"></a>

$$
B_i^{(4n+1,\tau)}\iota=\iota B_i^{(4n,\mathbf{1})}.
\tag{6.4}
$$

现在令 $b_j=1\iff x_{j+1}=\mathbf{1}$。式 (6.3) 恰变成 (6.2)，相邻 $11$ 正好是唯一禁止的融合邻接。对内部中心，按左右标签分类，式 (3.1) 的四个控制块分别给出项目局部真空通道投影的四个块。左端中心 $b_0$ 的左邻为一，投影为 $n_1$，也正好判断第一对任意子的真空通道。右端只使用到中心 $4n-2$，保持前缀总荷标记 $b_{4n-1}=1$。因此包括边界在内每个 $B_i$ 都由对应的 $K_{i-1}$ 精确实现。

∎

这补全了黄金门原文定理 5.2 另列的“编码桥假设”，使用的是同一固定 $F,R$ 模型中的基底与生成元对应，不需要在硬件上另行施加一个随目标改变的 $F$ 门。初态准备、可调用的 $K$ 和最终读出仍是实际操作资源。

<a id="thm-multi"></a>

#### 定理 6.2（同一固定门的多比特近似通用性）

在定义 [2.1](#def-universal) 和式 (6.2) 的条件下，黄金门具有编码近似普适性。若供应目标近似的编织词含 $L$ 个正向或逆向生成元，则转成仅正向 $K$ 的门字至多使用 $9L$ 次调用，且不增加算符范数误差。

**证明。**

明确调用同一 Fibonacci 表示在 $V_{4n}^{\mathbf{1}}$ 上的射影密度定理；这是文献 （[6](#ref-flwdensity)） §6 定理 6.2 的零亏格、$4n$ 个非平凡标签情形，亦与 （[5](#ref-flw)、[7](#ref-drw)） 的编码普适性一致。真空外边界可以封口，固定标签的边界扭转在射影表示中不增添操作；选择共轭手性或酉规范不改变密度。

令 $J_{\rm block}$ 为定理 [6.1](#thm-bridge) 的块嵌入，将目标酉延拓为全扇区酉

$$
\widetilde U=J_{\rm block}U J_{\rm block}^\dagger
 +(I-J_{\rm block}J_{\rm block}^\dagger).

$$

射影密度给一个编织词 $B$ 和整体相位 $\gamma$，使
$\|B-e^{i\gamma}\widetilde U\|_{\mathrm{op}}<\varepsilon$。限制到码空间、附上旁观者并用定理 [6.1](#thm-bridge) 逐字母换成 $K$，保持同一个算符及范数。每个逆字母用 $K^9$ 替换，因 $K^{-1}=K^9$，误差不变，调用数至多九倍。

∎

该证明调用多体密度作为明确外部定理；单比特两个非交换矩阵本身并不证明纠缠通用性。中间块的固定真空标记只定义输入与最终逻辑码，计算期间允许暂时改变；始终保持的是合法路径。该论证没有给出最短门字、统一硬件耗时或精确无泄漏纠缠字。

<a id="cor-nanderror"></a>

#### 推论 6.3（近似可逆 NAND 的完整误差保证）

对任意 $\varepsilon>0$，存在有限黄金门字 $C$ 和相位 $\gamma$，满足

<a id="equation-6-5"></a>

$$
\|C\widehat J_3-e^{i\gamma}\widehat J_3V_f\|_{\mathrm{op}}<\varepsilon.
\tag{6.5}
$$

每个计算基输入 $|a,b,0\rangle$ 的错误结果连同最终编码泄漏的总概率至多 $\varepsilon^2$。两等距通道的半 diamond 距离至多 $\varepsilon$，故该保证覆盖与外部参考系统纠缠的输入。

**证明。**

定理 [6.2](#thm-multi) 取 $U=V_f$ 即得 (6.5)。设 $v$ 为理想输出基向量，$w$ 为实际输出，且 $\|w-e^{i\gamma}v\|<\varepsilon$。正交投影到 $v^\perp$ 得错误总质量
$\|(I-vv^\dagger)w\|^2<\varepsilon^2$，其中包括编码外结果。对任意参考系统，等距映射差的算符范数张量单位后仍不变。相应纯输出的迹距离不超过向量差；混合输入可纯化，再取偏迹不会增加迹距离。因此通道差的 diamond 范数至多 $2\varepsilon$。

∎

<a id="sec-7"></a>

## 7. 为何它不是无编码全寄存器万能门

<a id="thm-defect"></a>

#### 定理 7.1（固定最近邻链上的占据缺陷守恒）

在固定物理链上只允许相邻三位置的 $K_j$。令 $D_i=n_i n_{i+1}$，则

<a id="equation-7-1"></a>

$$
[K_j,D_i]=0\qquad\text{对全部 }i,j.
\tag{7.1}
$$

因此该菜单在整个 $2^N$ 维寄存器上不具有无编码近似普适性。某些物理 $X_i$ 与任何有限 $K$ 门字的半 diamond 距离都为 $1$。

**证明。**

唯一非对角项正比于 $(1-n_{j-1})X_j(1-n_{j+1})$。若 $j\notin\{i,i+1\}$，它与 $D_i$ 直接对易；若 $j=i$ 或 $j=i+1$，相邻零控制因子使它与 $D_i$ 的左右乘积均为零。所有其余项均对角，故 (7.1) 成立。

取 $n_i=0,n_{i+1}=1$ 的基态，属于 $D_i=0$ 扇区。任意允许门字仍在该扇区，而 $X_i$ 把它送入 $D_i=1$ 扇区，两个输出正交。一个输入已见证输出迹距离为一，因此半 diamond 距离为最大值一。

∎

该不变量依赖固定最近邻接线；若外加任意重接线或 SWAP，不能继续无条件使用同一组 $D_i$。合法编码处于全部 $D_i=0$ 的共同扇区，故定理 [6.2](#thm-multi) 与此障碍相容。后文的算术障碍在允许同一 $K$ 任意三位置作用时仍成立，是另一种限制。

<a id="sec-8"></a>

## 8. 有限黄金电路的算术：非平凡有理概率不存在

<a id="sec-8-1"></a>

### 8.1. 振幅所在的环

令

<a id="equation-8-1"></a>

$$
\beta=\varphi^{-1/2},\quad t=\beta^2=\varphi^{-1},\quad
F_0=\mathbb{Q}(\zeta),\quad R_0=\mathbb{Z}[\zeta],\quad E=F_0(\beta).
\tag{8.1}
$$

这里 $F_0$ 是数域，不是 AURIC 标签 $F[\mathrm{null}]$。$t=-(\zeta+\zeta^{-1})\in R_0$，$\beta^4+\beta^2-1=0$，所以 $\beta$ 为代数整数。$\zeta$ 是本原十次单位根，$[F_0:\mathbb{Q}]=4$，且 $[E:\mathbb{Q}]\le8$。

<a id="def-finiteprotocol"></a>

#### 定义 8.1（有限完整黄金协议）

固定有限数量的计算基初始化寄存器；允许有限深、有限分支的 $K$ 调用、计算基投影测量，以及依照已取得结果选择后续 $K$ 地址。每个失败和终止结果都保留在总样本空间中。最终事件是有限个完整记录与计算基结果的并集；不用外加随机币，不对成功事件另行归一化。原生量子寄存器的重置若不能由这些操作实现，不包含在本定义中。

<a id="thm-integer"></a>

#### 定理 8.2（有限完整记录的代数整数概率）

在定义 [8.1](#def-finiteprotocol) 下，每个事件概率 $p$ 都是 $E$ 中的实代数整数。因此

<a id="equation-8-2"></a>

$$
\boxed{p\in\mathbb{Q}\quad\Longrightarrow\quad p\in\{0,1\}.}
\tag{8.2}
$$

特别是从计算基开始，有限黄金门字不能精确制备公平量子币、标准等幅 Bell 态，或在当前计算基词编码中精确实现 Hadamard，即使允许任意整体相位。

**证明。**

式 (3.1) 的所有矩阵元都是 $\zeta,\beta$ 的整系数多项式，因而为代数整数。计算基投影的矩阵元为零或一。每个未归一完整分支 Kraus 矩阵 $M_h$ 是有限乘积，其每个矩阵元仍是代数整数。对初态基向量 $|x\rangle$ 和末端基结果 $y$，质量为
$|(M_h)_{yx}|^2$。复共轭保持 $E$ 及代数整数性，有限求和也保持，故任意完整事件概率均为实代数整数。一个有理代数整数只能是整数，而 $0\le p\le1$，得 (8.2)。所列三个目标从某个计算基输入都要求一个计算基事件概率恰为 $1/2$，故被排除。

∎

该定理兼容任意好的近似，因为代数整数在选定实嵌入中的可取值并非离散到存在统一概率间隙。它不覆盖外加 $|+\rangle$、外加公平经典币、任意测量基或对成功分支的条件归一化。

<a id="sec-8-2"></a>

### 8.2. 一个完全显式的有限字长精度下界

<a id="prop-length"></a>

#### 命题 8.3（有理目标概率的数域范数界）

仅考虑长度为 $L$ 的酉黄金门字、一个计算基输入和一个计算基事件。设
$\kappa=1+2\varphi^3$。对 $r=a/b\in(0,1)$，其中 $a,b$ 为正整数，有

<a id="equation-8-3"></a>

$$
\boxed{|p-r|\ge\frac{1}{b\,(b\kappa^{2L}+a)^7}.}
\tag{8.3}
$$

特别是 $r=1/2$ 时，

<a id="equation-8-4"></a>

$$
|p-\tfrac12|\ge\frac{1}{2\,3^7\kappa^{14L}}.
\tag{8.4}
$$

**证明。**

对任一嵌入 $\sigma:E\to\mathbb{C}$，$|\sigma(\zeta)|=1$，而 $\sigma(t)$ 为 $\varphi^{-1}$ 或 $-\varphi$，故 $|\sigma(\beta)|\le\sqrt\varphi$。活跃投影块为 $u u^T$，$u=(\beta,\beta^2)^T$，其嵌入后范数至多 $|\sigma\beta|^2+|\sigma\beta|^4\le\varphi+\varphi^2=\varphi^3$。其余投影块为零或单位，故每个嵌入门的范数至多 $\kappa$，任意长度 $L$ 门字至多 $\kappa^L$。

记输出幅度为 $c_y$，事件集为 $A$。虽然 $\sigma$ 未必与复共轭交换，但 $\sigma\circ\overline{\cdot}$ 本身也是 $E$ 的一个嵌入，故 Cauchy–Schwarz 给

$$
|\sigma(p)|=\left|\sum_{y\in A}\sigma(c_y)\sigma(\overline{c_y})\right|
\le\kappa^{2L}.

$$

$q=bp-a$ 是非零代数整数，其 $E/\mathbb{Q}$ 范数是非零整数。令 $d=[E:\mathbb{Q}]\le8$，隔离恒等嵌入的因子得到

$$
1\le |N_{E/\mathbb{Q}}(q)|
\le b|p-a/b|(b\kappa^{2L}+a)^{d-1}.

$$

因括号至少为一，可把 $d-1$ 放宽为七，得到 (8.3)。当 $a=1,b=2$ 时，$2\kappa^{2L}+1\le3\kappa^{2L}$，得到 (8.4)。

∎

这是一项明确模型中的必要门长约束，并非最优编译定理。带有大量测量分支时仍有定理 [8.2](#thm-integer)，但不能直接把 (8.3) 的酉字长界无条件套用到所有自适应协议。

<a id="sec-9"></a>

## 9. 比有理概率更强：精确取反的奇偶选择定理

<a id="sec-9-1"></a>

### 9.1. 分级振幅与 Galois 正性

记计算基词 $x$ 的 Hamming 权重为 $w(x)$，奇偶为 $\pi(x)=w(x)\bmod2$。

<a id="lem-grading"></a>

#### 引理 9.1（黄金振幅的二元分级）

任意有限黄金门字 $C$ 满足

<a id="equation-9-1"></a>

$$
C_{yx}\in
\begin{cases}
R_0,&\pi(y)=\pi(x),\\
\beta R_0,&\pi(y)\ne\pi(x).
\end{cases}
\tag{9.1}
$$

同样结论适用于有限完整黄金协议的每个未归一分支矩阵。门可作用在任意三位置；仅重排位置的计算基置换也不破坏该分级。

**证明。**

每个 $K$ 的对角元在 $R_0$，唯一非对角项为 $\zeta(\zeta-1)\beta^3$，翻转一个中心位并属于 $\beta R_0$。矩阵乘法中，两次奇偶变化贡献 $\beta^2=t\in R_0$，一次变化贡献 $\beta R_0$，所以按奇偶分级的矩阵类乘法封闭。计算基投影为对角零一矩阵，也属于该类，故每个分支保持性质。

∎

<a id="thm-parity"></a>

#### 定理 9.2（相反奇偶事件不能精确确定发生）

对计算基输入 $x$，取任意有限个完整分支和末端结果组成事件 $A$，其中所有末端词均与 $x$ 奇偶相反。则其概率若为有理数，只能为零。特别地，有限黄金门字不可能满足

<a id="equation-9-2"></a>

$$
C|x\rangle=e^{i\theta}|y\rangle\quad\text{且}\quad \pi(x)\ne\pi(y).
\tag{9.2}
$$

更一般地，输出支撑也不能完全落在相反奇偶子空间。

**证明。**

由引理 [9.1](#lem-grading)，对应未归一幅度均可写为 $\beta c_{h,y}$，$c_{h,y}\in R_0$，所以

<a id="equation-9-3"></a>

$$
p_A=t\sum_{(h,y)\in A}c_{h,y}\overline{c_{h,y}}\in F_0.
\tag{9.3}
$$

取四次分圆域自同构 $\sigma(\zeta)=\zeta^3$。它与复共轭交换，而且

$$
t=-(\zeta+\zeta^{-1}),\qquad \sigma(t)=-\varphi.

$$

于是

<a id="equation-9-4"></a>

$$
\sigma(p_A)=-\varphi\sum_{(h,y)\in A}|\sigma(c_{h,y})|^2\le0.
\tag{9.4}
$$

若 $p_A$ 是正有理数，自同构固定它，便有 $\sigma(p_A)=p_A>0$，矛盾。概率非负，故有理时只能为零。完全转移到相反奇偶子空间将使 $p_A=1$，同样不可能。

∎

这不是物理 Hamming 奇偶守恒：一个 $K$ 已把 $000$ 相干混合到 $010$。限制是有限字不能让原奇偶部分*精确全部消失*，并非相反奇偶幅度必须为零。

<a id="cor-clean"></a>

#### 推论 9.3（标准编码中精确 clean NAND 的排除）

在式 (6.2) 的编码下，任何有限黄金门字若精确实现计算基逻辑置换，并使所有额外计算基辅助位原样返回，则该置换必须保持逻辑 Hamming 奇偶。因此，逻辑 $X$、CNOT、Toffoli 及式 (2.2) 的 $V_f$ 均不能如此精确实现；它们仍可按定理 [6.2](#thm-multi) 任意精度逼近。

**证明。**

编码词含 $n$ 个固定内部一位和一个左边界一位，故

<a id="equation-9-5"></a>

$$
w(\widehat J_n q)=n+1+\sum_{r=1}^n q_r.
\tag{9.5}
$$

复原辅助词在输入输出的奇偶贡献相同。所列每个置换都有某个基输入只翻转一个逻辑位：例如 $V_f|0,0,0\rangle=|0,0,1\rangle$。这要求物理奇偶完全翻转，与定理 [9.2](#thm-parity) 矛盾。

∎

**适用范围。**  这是指定计算基词编码的结论，不排除另用两个同奇偶码词、或让输出垃圾携带奇偶补偿。尤其不能由此宣布任意编码下所有精确经典计算都不可能。它也没有证明全部精确无泄漏纠缠编织都不存在；该广泛问题与有限家族的排除必须区分（[12](#ref-cui)）。

<a id="sec-9-2"></a>

### 9.2. 固定但不复原的环境也不能实现可逆 NAND

<a id="lem-intersection"></a>

#### 引理 9.4（两种幅度级别的交集）

$\beta\notin F_0$，因此 $R_0\cap\beta R_0=\{0\}$。

**证明。**

$\beta$ 为实数；若属于 $F_0$，则属于其实子域 $\mathbb{Q}(\sqrt5)$。但 $\beta^2=\varphi^{-1}$ 在该二次域中的范数为 $-1$，不可能等于有理数 $N(\beta)$ 的平方。故 $\beta\notin F_0$。若 $a=\beta b\ne0$ 且 $a,b\in R_0$，则 $\beta=a/b\in F_0$，矛盾。

∎

<a id="thm-environment"></a>

#### 定理 9.5（丢弃环境后的精确相干置换限制）

采用标准计算基词编码和固定计算基辅助输入。设有限黄金门字在丢弃辅助系统后，对每个逻辑输入都精确实现同一个酉置换，其作用为 $U_\omega|x\rangle=|\omega(x)\rangle$。那么下面的奇偶变化函数

<a id="equation-9-6"></a>

$$
\delta_\omega(x)=\pi(\omega(x))\oplus\pi(x)
\tag{9.6}
$$

必须与 $x$ 无关。因此 CNOT、Toffoli 和 $V_f$ 仍被排除，即使允许最终留下与输入无关、未复原的任意纯环境态。

**证明。**

对每个基输入，精确纯逻辑输出意味着全局纯输出可写成
$|\omega(x)\rangle|\eta_x\rangle$，所有编码与固定边界已吸收进记号。对任意两个输入的叠加，若约化逻辑通道仍精确是 $U_\omega$，交叉项必须保持，迫使 $\langle\eta_{x'}|\eta_x\rangle=1$。所以全体环境态相同，记为 $\eta$；允许的统一整体相位可吸收到 $\eta$。

固定一个环境基结果 $z$，对应全局矩阵元为同一个 $\eta_z$，不依赖 $x$。根据式 (9.1)，其所属幅度级别由 $\delta_\omega(x)$ 加上固定环境输入与 $z$ 的奇偶差决定。如果 $\delta_\omega$ 同时取零和一，则 $\eta_z$ 同时属于 $R_0$ 和 $\beta R_0$，引理 [9.4](#lem-intersection) 迫使 $\eta_z=0$。这对所有 $z$ 成立，违背环境态归一化。故 $\delta_\omega$ 必为常数。CNOT、Toffoli、$V_f$ 的翻转条件依赖输入，故其 $\delta_\omega$ 不恒定。

∎

这里要求精确实现*同一个相干酉置换*。若只要求经典输入的真值表正确，允许环境记录输入，或容许输入依赖的额外相位，就不能直接引用此定理。对 $X$，$\delta\equiv1$ 是常数，故此强化本身不排除以环境奇偶补偿实现 $X$；其 clean 排除已由推论 [9.3](#cor-clean) 给出。

<a id="sec-10"></a>

## 10. 更强形式：同奇偶压缩块永远可逆

上一节的列论证还可以加强到任意具有确定奇偶的叠加态，而无需对输入态的任意复系数施加数域自同构。

<a id="thm-pseudo"></a>

#### 定理 10.1（Galois 度量与压缩块可逆性）

设 $C$ 是 $N$ 个物理比特上的任意有限黄金酉门字，按偶、奇 Hamming 子空间写成

$$
C=\begin{pmatrix}C_{ee}&C_{eo}\\C_{oe}&C_{oo}\end{pmatrix}.

$$

则 $C_{ee}$ 和 $C_{oo}$ 均可逆。因此任意非零、初始奇偶确定的叠加态，都不能完全被送入相反奇偶子空间。

**证明。**

令 $S=\operatorname{diag}(\beta^{w(x)})$、$T=S^{-1}CS$。一个中心位翻转使 Hamming 权重增减一；原非对角系数为 $\zeta(\zeta-1)\beta^3$，经 $S$ 变换后为同一相位因子乘 $\beta^2$ 或 $\beta^4$。两者都在 $R_0$，对角元也在 $R_0$。所以 $T\in\operatorname{Mat}(R_0)$。

由物理酉性 $C^\dagger C=I$ 得

<a id="equation-10-1"></a>

$$
T^\dagger DT=D,\qquad D=S^2=\operatorname{diag}(t^{w(x)}).
\tag{10.1}
$$

在 $F_0$ 上应用 $\sigma(\zeta)=\zeta^3$。因为它与复共轭交换，得到

<a id="equation-10-2"></a>

$$
\sigma(T)^\dagger D'\sigma(T)=D',\qquad
D'=\operatorname{diag}((-\varphi)^{w(x)}).
\tag{10.2}
$$

按奇偶分块，写 $D'=\operatorname{diag}(D_+,-D_-)$，其中 $D_+,D_->0$，并写
$\sigma(T)=\left(\begin{smallmatrix}A&B\\C_0&E_0\end{smallmatrix}\right)$。式 (10.2) 的两个对角块给出

<a id="equation-10-3"></a>

$$
A^\dagger D_+A=D_++C_0^\dagger D_-C_0>0,
\quad
E_0^\dagger D_-E_0=D_-+B^\dagger D_+B>0.
\tag{10.3}
$$

故 $A,E_0$ 可逆。自同构保持行列式是否为零，所以 $T_{ee},T_{oo}$ 也可逆；正对角 $S$ 不混合奇偶，故物理压缩块 $C_{ee},C_{oo}$ 可逆。任意非零偶态经 $C_{ee}$ 后仍有非零偶分量，奇态同理。

∎

式 (10.2) 是证明使用的共轭数域中的不定度量，不是实际实验中的负概率或另一条物理演化。实际门 $C$ 仍保标准正定内积。该结论显示：有限精确实现可以有严格的代数限制，而极限闭包仍包含把某个态完全翻到另一子空间的目标算符；可逆压缩块的最小奇异值可以趋近零。

<a id="sec-11"></a>

## 11. 概率、递归与公平读出的三种资源层次

<a id="sec-11-1"></a>

### 11.1. 完整记录的乘加和相干门字的乘加

对一个有限完整协议，未归一分支记为 $M_h$。一个真实记录事件 $A$ 的概率是

<a id="equation-11-1"></a>

$$
p(A)=\sum_{h\in A}\|M_h\psi\|^2.
\tag{11.1}
$$

一个未被记录的内部路径的振幅则先相加，再平方：

<a id="equation-11-2"></a>

$$
\langle y|K_{j_L}\cdots K_{j_1}|x\rangle
=\sum_{x_1,\ldots,x_{L-1}}
\prod_{\ell=1}^L (K_{j_\ell})_{x_\ell x_{\ell-1}}.
\tag{11.2}
$$

这里 $x_0=x,x_L=y$。式 (11.1) 与 (11.2) 的求和对象不同；实际取得并丢弃一个测量记录一般也已经改变了通道。此前关于存在量词和支撑的研究在此变得具体：有限字可以保留许多可达路径，同时让某些最终振幅相消为零；布尔可达性不能替代黄金电路语义。

<a id="prop-fair"></a>

#### 命题 11.1（黄金读出的独立两次去偏）

用两个已明确按张量积准备的 $|000\rangle$ 块，各调用一次 $K$ 并在计算基测量。令 $B_1,B_2$ 为中心位读出，则

<a id="equation-11-3"></a>

$$
\Pr(B_i=1)=\varphi^{-1},\quad
\Pr(B_i=0)=\varphi^{-2},\quad
\Pr(01)=\Pr(10)=\varphi^{-3}.
\tag{11.3}
$$

只接受 $01,10$，并输出第一个读出位，则成功率为 $s=2\varphi^{-3}$，条件输出恰好公平。

**证明。**

$000\to010$ 的振幅是 $\zeta(\zeta-1)\varphi^{-3/2}$。因 $|\zeta-1|^2=\varphi^2$，其概率为 $\varphi^{-1}$，另一个概率由归一化为 $\varphi^{-2}$。两块的乘积初态和分离门操作使输出仍为乘积态，因此两次结果确实独立，$01,10$ 的质量各为 $\varphi^{-1}\varphi^{-2}=\varphi^{-3}$。除以成功总质量 $2\varphi^{-3}$，两种条件概率均为 $1/2$。

∎

这与定理 [8.2](#thm-integer) 没有矛盾：完整的一轮输出为 $0,1,\mathrm{fail}$，其质量分别为 $\varphi^{-3},\varphi^{-3},1-2\varphi^{-3}$。出现 $1/2$ 的步骤显式使用了后选择除法。若两块只在名称上不同，而实际制备共享相关选择器，则 (11.3) 的乘积推导不成立；项目[相干重构续卷](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md) §63.2 正要求保留这样的实际联合源律。

<a id="thm-repeat"></a>

#### 定理 11.2（无界重复与有限截断的区别）

假定每轮供应新的独立准备，并允许不断重复命题 [11.1](#prop-fair) 直到成功。则成功轮数 $T$ 满足

<a id="equation-11-4"></a>

$$
\Pr(T=r)=(1-s)^{r-1}s,\quad
\Pr(T<\infty)=1,\quad \mathbb E T=s^{-1}=\varphi^3/2.
\tag{11.4}
$$

最终两个输出各有无条件概率 $1/2$。若最多只允许 $M$ 轮，则必须保留

<a id="equation-11-5"></a>

$$
\Pr(\mathrm{abort})=(1-s)^M>0,\qquad
\Pr(0)=\Pr(1)=\frac{1-(1-s)^M}{2}.
\tag{11.5}
$$

**证明。**

独立性使前 $r-1$ 次失败再成功的质量为 $(1-s)^{r-1}s$，其几何级数和为一，期望为 $1/s$。每个成功轮的两个输出质量相等，所以对全部有限成功轮求和后各为一半。截断到 $M$ 轮则留下全失败质量 $(1-s)^M$，其余成功质量平均分给两个输出。

∎

因此“递归到稳定”为何能改变精确可实现集合，有一个严格实例：有界深度只用有限次代数整数运算；条件化引入除法；无界但几乎必然终止的协议还引入可数极限。这三个操作集合不同。有限期望不等于存在统一有限最坏深度，独立新制备与保留停止记录也都要实际供应。文献中加入荷测量、融合、辅助态及随机停止的反馈协议确可扩大精确门能力；其强制测量和重复恢复不能被改写为统一有界深度的结论，必须按实际菜单分析（[13](#ref-bl)）。

<a id="sec-12"></a>

## 12. 静态相容图的解释：门类型、接线与闭包

本稿的门字可以表示为一个有限张量网络或带端口的有向无环电路图。选取不同切面只改变中间指标的组织方式；对同一个有限网络，完整张量收缩不依赖收缩次序。对不相交子系统上的门，乘法交换；对合法路径中的相邻黄金门，有编织恒等式；同一地址有十次返回。这些都是保持同一边界算符的明确重写规则。

相反，任意交换两个共享非交换自由度的门，并不是另一张等价切面。单比特密度证明正需要 $[P,Q]\ne0$；若把所有先后依赖都无条件抹掉，只剩同一个交换代数，就失去了上述通用性来源。这里的先后是电路的依赖关系，不要求把某个外部绝对时钟当成基础公理。

可以据此给出三层严格对象：有限静态图及其端口相容是*程序*，矩阵收缩是*语义*，这些有限语义在误差范数下的闭包是*可逼近的连续操作*。定理 [4.3](#thm-density) 证明连续圆能够出现在固定离散门字的闭包；定理 [8.2](#thm-integer) 和 [9.2](#thm-parity) 证明闭包与有限字集合不能混为一谈。这是关于离散程序与连续有效描述的数学联系，不是断言物理连续性已被否定。

观察者若被纳入模型，其可取得的记录、可选择的地址、尚存辅助态及停止规则均属于协议。一个已写出的理想矩阵不自动供应硬件控制；一个已计算的源描述也不自动恢复实际切面。最新项目对 same-law 与实际取得条件的强调，在这里表现为同一初态、同一相位标定、同一操作菜单和完整记录必须共同满足。

<a id="sec-13"></a>

## 13. 当前结论与下一步可核查的问题

| 问题 | 当前严格结论 |
| --- | --- |
| 单个固定矩阵是否存在？ | 存在，式 (3.1)；参数固定，逆门为九次正向调用。 |
| 单个地址重复是否普适？ | 否，只有十种幂；需要两个以上适当耦合的可选地址。 |
| 二维编码是否普适？ | 射影上是；定理 [4.3](#thm-density) 为自足证明，完整幂分类见推论 [5.2](#cor-powers)。 |
| 只保留取反是否足够？ | 在固定复线性实编码中不够；相位门存在式 (5.2) 的严格误差下界。 |
| 多比特近似普适性？ | 编码桥已逐基补全，再调用明确的标准 Fibonacci 编织密度定理。 |
| 无编码全寄存器普适性？ | 固定最近邻菜单下否；每条相邻 $11$ 缺陷都守恒。 |
| 有限精确 Hadamard／公平币？ | 在基态初始化及计算基完整记录菜单下否；非平凡有理概率被代数整数性排除。 |
| 有限精确可逆 NAND？ | 标准词编码且辅助位复原时否；丢弃固定环境的精确相干实现也被非恒定奇偶变化排除。 |
| 近似 NAND 的可靠性？ | 存在任意精度门字；基输入错误含泄漏至多 $\varepsilon^2$，半 diamond 误差至多 $\varepsilon$。 |
| 递归与后选择能否改变能力？ | 能，黄金读出的两次去偏给出精确例子，但必须保留成功率、失败和停止记录。 |
| 是否最小、最短或已实现？ | 本稿未证明这些不同问题；没有输出最短门字或物理容错认证。 |

接下来最有价值的研究对象可以缩小为三项。第一，给定小型标准逻辑目标，在上述固定编码与保留泄漏的误差标准下，推导可审核的编译构造和长度界，而不以存在性替代编译。第二，分析多体 $K^2$ 子群及纯反射 $K^5$ 在改变实编码后的能力；二维幂分类还不能代替这两项证明。第三，研究同奇偶码词的替代编码是否避开当前精确奇偶障碍，以及它是否同时保持易准备、可读出、可纠缠和可扩展的条件。

这些问题都有明确的可证伪接口：矩阵、编码、输入资源、实际操作、误差与完整记录。AURIC 黄金门的“NAND 式”意义已经可以表述为一项精确数学命题；其含义是固定门类型在指定编码上的近似普适生成，而有限精确能力还受到本稿证明的代数约束。

<a id="sec-bibliography"></a>

## 参考文献

<a id="ref-repogate"></a>

**[1]** trureturing 项目。
[AURIC Fixed Golden Gate and Braid Compatibility](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/AURIC_FIXED_GOLDEN_GATE_AND_BRAID_COMPATIBILITY_ZH.md)，固定提交 `52ce13dc5e8c`，§§2–8；其中定理 5.2 的额外编码桥在本稿定理 [6.1](#thm-bridge) 中显式证明。

<a id="ref-repofusion"></a>

**[2]** trureturing 项目。
[Fusion Spin Chain, QCA and Cut Obstructions](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md)，同一提交，§§12–15。使用其有限融合基、指定规范 $F$ 数据及带权路径投影。

<a id="ref-repocontrol"></a>

**[3]** trureturing 项目。
[FIB Legal Gates, State Machines and Shor Readout](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/FIB_LEGAL_GATES_STATE_MACHINES_AND_SHOR_READOUT.md)；
[FIB Legal Gates: Single Reference and Certified Readout](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/FIB_LEGAL_GATES_SINGLE_REFERENCE_AND_CERTIFIED_READOUT.md)。连续角控制菜单与本稿固定门菜单分别处理。

<a id="ref-reporecords"></a>

**[4]** trureturing 项目。
[AURIC Quantum Principles and Coherent Reconstruction Continuation](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)，§63；
[AURIC Selection Calculus](https://github.com/the-omega-institute/trureturing/blob/52ce13dc5e8c2d73f96845d0a8aad75917c14626/docs/develop/theory/AURIC_FIB_ATOM_SELECTION_CALCULUS.md)，§§10、27。

<a id="ref-flw"></a>

**[5]** M. Freedman, M. Larsen and Z. Wang.
*A modular functor which is universal for quantum computation*.
[arXiv:quant-ph/0001108](https://arxiv.org/abs/quant-ph/0001108)。

<a id="ref-flwdensity"></a>

**[6]** M. H. Freedman, M. J. Larsen and Z. Wang.
*The two-eigenvalue problem and density of Jones representation of braid groups*.
[arXiv:math/0103200](https://arxiv.org/abs/math/0103200)，§6，定理 6.2。

<a id="ref-drw"></a>

**[7]** C. Delaney, E. C. Rowell and Z. Wang.
*Local unitary representations of the braid group and their applications to quantum computing*.
[作者公开全文](https://people.tamu.edu/~rowell/DRWv10.pdf)，§4，尤其多体密度与泄漏范围。

<a id="ref-kbs"></a>

**[8]** V. Kliuchnikov, A. Bocharov and K. M. Svore.
*Asymptotically Optimal Topological Quantum Compiling*.
[arXiv:1310.4150](https://arxiv.org/abs/1310.4150)。精确合成及数论编译背景；其特定算法效率假设须按原文保留。

<a id="ref-ky"></a>

**[9]** V. Kliuchnikov and J. Yard.
*A framework for exact synthesis*.
[arXiv:1504.04350](https://arxiv.org/abs/1504.04350)。

<a id="ref-barenco"></a>

**[10]** A. Barenco.
*A Universal Two-Bit Gate for Quantum Computation*.
[arXiv:quant-ph/9505016](https://arxiv.org/abs/quant-ph/9505016)。

<a id="ref-rg"></a>

**[11]** T. Rudolph and L. Grover.
*A 2 rebit gate universal for quantum computing*.
[arXiv:quant-ph/0210187](https://arxiv.org/abs/quant-ph/0210187)。区分实编码的计算模拟与原复空间任意酉门。

<a id="ref-cui"></a>

**[12]** S. X. Cui, K. T. Tian, J. F. Vasquez, Z. Wang and H. M. Wong.
*The Search For Leakage-free Entangling Fibonacci Braiding Gates*.
[arXiv:1904.01731](https://arxiv.org/abs/1904.01731)。文中的特定家族排除不是一般不可能性定理。

<a id="ref-bl"></a>

**[13]** S. Bigelow and C. Levaillant.
*Realizing an exact entangling gate using Fibonacci anyons*.
[arXiv:1802.01011](https://arxiv.org/abs/1802.01011)。精确受控旋转协议使用编织、荷测量及融合。

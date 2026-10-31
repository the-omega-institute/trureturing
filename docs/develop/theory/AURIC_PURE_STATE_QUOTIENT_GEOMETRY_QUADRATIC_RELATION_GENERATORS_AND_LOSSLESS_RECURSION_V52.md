> **原稿归属与转换说明。** 以下元数据、题名、摘要、正文、断言、证明、表格、引文及历史取得、通读、核对、生产、未运行程序和未修改仓库等陈述，均归原稿作者 AURIC research continuation。“本轮”“亲读”等不表示 Markdown 编者实施了作者所述历史行为。编者必要限定另以署名“编者注”邻接列出，不替换原断言。保存原稿 UTF-8 48,415 字节，SHA-256 <code>e7b44c993e5c<wbr>cb82c1d3aa1f<wbr>4e3ee4c4d1d7<wbr>944c8ebfde07<wbr>32e4c214469b<wbr>afcf</code>。本文是纸面数学文本，不构成形式、kernel、原生实现、物理或经验认证；不认证上游、RH 或无条件量子起源。

**原稿 PDF 元数据与版式**

- 标题：AURIC：纯态商几何、二次关系生成与无损递归
- 作者：AURIC research continuation
- 主题：Hopf quotient, phase-invariant quadratic generators, probability additivity and exact compression
- 原稿排版指示：XeLaTeX，编译两遍；11pt、A4，页边距 23mm、页眉高度 16pt。可定义 `AURICFontPath` 指向 Noto CJK OTF 目录；优先 Noto Serif CJK SC，回退 FandolSong；粗体分别采用其 Bold，斜体采用 Regular，粗斜体采用 Bold；等宽字体 Latin Modern Mono；中文断行，断行伸缩 `0pt plus 1pt`。蓝色 RGB(24,53,79)，链接同色；段首缩进 1.8em，段间距 2pt，紧急伸缩 3em，列表无额外间距、左缩进 2em。页眉左为“AURIC：纯态商几何、二次生成与无损递归”，右为“v52 / 2026-10-31”；页脚居中页码。显示公式允许跨页级别 2。标题行距 7pt、副题前 8pt、日期前 5pt；这三个间隔是标题版式参数。

# AURIC：纯态商几何、二次关系生成<br>与无损递归

**定义、定理与纸面证明　v52.0**

2026 年 10 月 31 日　Asia/Singapore

## 摘要

本文把“纯态允许无损降低参数、平方是最低关系层”的直觉分成可独立证明的命题。
未归一二元 Hopf 映射把两个复振幅模去共同相位后精确表示为三个实量，
其径向长度仍保存总权重；再归一化得到内在二维的 Bloch 球面。
二维图册可以稳定保存纯态信息，但普通正交投影需要分支标记，
整个球面也不存在单张连续单射平面坐标。
在给定复线性空间与共同相位等价后，所有相位不变多项式都由二次关系
$z_i\overline z_j$ 生成，非恒定一次不变量不存在。
平方概率另由正交权重可加，或完整效果域上的分解相容与正可加性确定。
高维纯态可用有序二叉树中的纯二元节点精确重构；固定支持含 $s$ 个分量时有
$s-1$ 个非平凡节点，保留 $2s-2$ 个实参数。
物理无损压缩则受整个态族的线性包络与内部参考相关限制，不能只看单态秩。
结合项目新增 K-bonacci 末端取得协议，给出正秩一实关系到纯态代表的对角相似分解，
并准确保留非对称规范与尺度。
全文采用纸面证明，区分标准结构、仓库既有结果、本轮综合和仍需说明的物理前提。

<a id="section-1"></a>

## 1 主张的准确版本与固定项目

本轮的两条主线是

$$
\boxed{(\mathbb{C}^2\setminus\{0\})/U(1)\cong\mathbb{R}^3\setminus\{0\},}
\qquad
\boxed{\mathbb{CP}^1\cong S^2,}
$$

以及

$$
\boxed{\text{共同相位不变多项式的最低非平凡生成层是二次关系。}}
$$

第一组说明何种“无损降维”成立；第二条说明“平方不可再降”的一个准确代数含义。
概率的平方律还需要可加性或统计混合的一致性，不能仅由维数计数推出。

本轮冻结项目 `dev` 提交为
<code>e42edf53c936<wbr>8a5d53e7e780<wbr>da2d2244493f<wbr>dfcc</code>，
 时间为 2026-10-31 21:49:06（新加坡）。相对 v51 基线
<code>d2950bd36448<wbr>c5d4f6c4a3e5<wbr>671ef7341851<wbr>45c9</code>，

完整 theory 树仅有两篇修改：K-bonacci 端点层析文稿新增第 7 节，
Lyndon 文稿另有新增；没有 Quantum Blueprint 变更。
V24 的 Hopf 计算、V37 的原生编码、V44 的高维图册和 Ω 的响应商均为既有结果。
[1](#ref-head)、[2](#ref-compare)、[7](#ref-kbonacci)、[3](#ref-v24)、[4](#ref-v37)、[5](#ref-v44)、[6](#ref-omega)

所有参考、观察者、记录、辅助因子与环境均解释为同一静态整体中的内部结构。
“无损”须相对于想保留的响应来定义：去掉整个对象的共同相位，与丢掉内部两条相干分支的
相对相位，是不同操作。

#### 定义 1.1（相对于响应族的无损编码）

给定对象集 $\mathcal X$ 与响应族 $\{R_q:\mathcal X\to Y_q\}_{q\in Q}$。
编码 $E:\mathcal X\to Z$ 对该族无损，指存在解码器 $d_q$ 满足 $R_q=d_q\circ E$。
等价地，$E(x)=E(y)$ 必须推出所有 $R_q(x)=R_q(y)$。

**等价性的证明。**

能解码时结论显然。反过来，每个 $R_q$ 在编码纤维上常值，
所以可在达到像 $E(\mathcal X)$ 上定义 $d_q(E(x))=R_q(x)$，且定义无歧义。

□

> **编者注（Markdown 编者）：解码器的定义域。** 上述等价按证明中明定的达到像 $E(\mathcal X)$ 理解。若另要求 $d_q$ 定义在整个 $Z$，还须能向未达到点延拓；例如非空 $Z$ 到空 $Y_q$ 的函数不存在。纤维判据本身不提供这项额外延拓。

这正是项目 Ω 第 4 节的响应商原则。[6](#ref-omega)

<div style="overflow-x:auto" tabindex="0" role="region" aria-label="表格 1">

| 量 | 与本题相关的区别 |
| --- | --- |
| Hilbert 维数 $d$ | 线性振幅空间的复维数 |
| 状态族的实维数 | 一个状态族局部需要多少独立实参数 |
| 矩阵秩 $r$ | 给定密度态的支持维数；不等于整个纯态族的载体维数 |
| 多项式次数 | 坐标函数如何依赖振幅；与上述维数不同 |
| 无损恢复 | 给定编码、目标族、读出或物理解码器的性质 |

</div>

<a id="section-2"></a>

## 2 两个复振幅怎样精确成为三个实关系量

#### 定义 2.1（保尺度的二元 Hopf 坐标）

对非零 $z=(a,b)\in\mathbb{C}^2$，定义

$$
S=|a|^2+|b|^2,\qquad
Q(z)=(2\operatorname{Re}(\overline a b),\,
2\operatorname{Im}(\overline a b),\,|a|^2-|b|^2).
$$

<a id="thm:hopf"></a>

#### 定理 2.2（去共同相位后的三维完备性）

有

$$
\|Q(z)\|=S,
\qquad zz^\dagger=\tfrac12(SI+Q(z)\cdot\sigma).
$$

且

$$
Q(z)=Q(w)\iff w=e^{i\theta}z
$$

对某个实 $\theta$ 成立。$Q$ 满射到 $\mathbb{R}^3\setminus\{0\}$，
诱导同胚 $(\mathbb{C}^2\setminus\{0\})/U(1)\cong\mathbb{R}^3\setminus\{0\}$。

**证明。**

平方恒等式

$$
4|a|^2|b|^2+(|a|^2-|b|^2)^2=(|a|^2+|b|^2)^2
$$

给出范数式，矩阵式由标准 Pauli 矩阵直接展开。
若 $Q(z)=Q(w)$，则两个尺度也相等，因此 $zz^\dagger=ww^\dagger$。
其像空间相同，故 $w=cz$；外积相同又给 $|c|=1$。反向显然。

给定 $q\ne0$，令 $S=\|q\|$。当 $S+q_3>0$ 时，取

$$
a=\sqrt{(S+q_3)/2},\qquad b=\frac{q_1+iq_2}{\sqrt{2(S+q_3)}}.
$$

在另一开图 $S-q_3>0$ 上，取

$$
b=\sqrt{(S-q_3)/2},\qquad a=\frac{q_1-iq_2}{\sqrt{2(S-q_3)}}.
$$

这两开图覆盖全部非零 $q$，重叠处代表仅差共同相位。
这些公式给满射及两张图上连续的商逆，故为同胚。

□

这项构造完整保留 $S$、相对模长和相对相位。
原始四个实参数中的共同相位被商去；它不是四维向量空间到三维的可逆线性投影。
项目 V24 已给单位版本及上述平方恒等式；本定理将其齐次尺度显式保留。[3](#ref-v24)

<a id="cor:sphere"></a>

#### 推论 2.3（归一纯态与球面）

令 $\psi=z/\sqrt S$、$r=Q(z)/S$，则

$$
\rho=\psi\psi^\dagger=\tfrac12(I+r\cdot\sigma),\qquad \|r\|=1.
$$

从而 $S^3/U(1)\cong\mathbb{CP}^1\cong S^2$。
对两纯态 $\rho_r,\rho_s$，

$$
\operatorname{Tr}(\rho_r\rho_s)=|\langle\psi_r,\psi_s\rangle|^2
=\frac{1+r\cdot s}{2}.
$$

**证明。**

归一化消去正尺度；最后一式用 $\operatorname{Tr}\sigma_i=0$、
$\operatorname{Tr}(\sigma_i\sigma_j)=2\delta_{ij}$ 展开。

□

<div style="overflow-x:auto" tabindex="0" role="region" aria-label="表格 2">

| 对象 | 实维数 | 约束或被商去的冗余 |
| --- | --- | --- |
| 原始非零二振幅 $\mathbb{C}^2\setminus\{0\}$ | 4 | 共同相位与正尺度都保留 |
| 未归一秩一正矩阵 $zz^\dagger$ | 3 | 商去共同相位，保留尺度 |
| 单位振幅 $S^3$ | 3 | 固定范数，仍保留共同相位 |
| 归一纯态 $\mathbb{CP}^1\cong S^2$ | 2 | 再商共同相位；三坐标满足球面等式 |
| 全部归一二元密度态 | 3 | 闭 Bloch 球；包含混态径向参数 |

</div>

第三行与第五行虽然都三维，却不是同一对象。
两个复振幅直接给出的归一态总是球面点；球内混态不是另一种二振幅纯态。

共同相位的作用范围也必须固定。例如
$(\lvert 0\rangle\otimes u+\lvert 1\rangle\otimes v)/\sqrt2$
中只将 $v$ 改成 $e^{i\theta}v$，通常改变了整个向量的相对相位。
递归拆分时每个局部参考的变换，必须由连接系数补偿。

<a id="section-3"></a>

## 3 纯态的二维表示：图册、分支与稳定性

<a id="thm:charts"></a>

#### 定理 3.1（二元纯态的两张复图）

在 $a\ne0$ 的图中取 $w=b/a$，则

$$
\psi(w)=\frac{(1,w)^{\mathsf T}}{\sqrt{1+|w|^2}},\qquad
r(w)=\frac{(2\operatorname{Re}w,2\operatorname{Im}w,1-|w|^2)}{1+|w|^2}.
$$

逆式是 $w=(r_x+ir_y)/(1+r_z)$。
在 $b\ne0$ 的另一图取 $v=a/b$，重叠域上 $v=1/w$。
两张图连同换图关系完整表示全部纯态。

**证明。**

第一图取共同相位使第一分量为正实数，归一化给上述代表。
直接展开外积得到三轴，且 $1+r_z=2/(1+|w|^2)>0$ 给逆式。
第二图交换参考分量，比例关系给换图公式。

□

普通正交投影 $(r_x,r_y,r_z)\mapsto(r_x,r_y)$ 则留下

$$
r_z=\pm\sqrt{1-r_x^2-r_y^2}.
$$

纯态约束消去了一个连续自由度，但圆盘内部仍须保留离散半球分支。
$\lvert 0\rangle$ 与 $\lvert 1\rangle$ 的前两轴完全相同，却是正交态。
手性规定哪一侧叫正，不能替未知态决定它在哪一侧。[3](#ref-v24)

#### 命题 3.2（单张全局平面图的拓扑障碍）

不存在连续单射 $f:S^2\to\mathbb{R}^2$。

**证明。**

对球面的每个二维局部图，域不变定理保证其在 $f$ 下的像是 $\mathbb{R}^2$ 的开集。
故 $f(S^2)$ 是开集。另一方面，球面紧致，所以其像紧致且闭。
$\mathbb{R}^2$ 连通，非空既开又闭的像只能是整个 $\mathbb{R}^2$，与紧致性矛盾。
这里使用的标准域不变定理见 Hatcher 定理 2B.3。[10](#ref-hatcher)

□

一个复平面加无穷远点，或者带标记的多张图，可以完整表示球面；
不连续的集合编码则不提供上述几何稳定性。

<a id="thm:chart-stable"></a>

#### 定理 3.3（有界图坐标与迹距离的精确比较）

记 $P_w=\lvert \psi(w)\rangle\langle \psi(w)\rvert$，采用 $D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$。
则

$$
D(P_w,P_v)=\frac{|w-v|}{\sqrt{(1+|w|^2)(1+|v|^2)}}.
$$

若选模较大的振幅为分母并保存图标记，则图内 $|w|,|v|\le1$，从而

$$
\boxed{\tfrac12|w-v|\le D(P_w,P_v)\le|w-v|.}
$$

**证明。**

两纯态的迹距离平方为 $1-|\langle\psi(w),\psi(v)\rangle|^2$，
可在它们张成的二维空间直接对角化证明。
再用

$$
(1+|w|^2)(1+|v|^2)-|1+\overline wv|^2=|w-v|^2.
$$

分母在 $[1,2]$ 内即得双向界。

□

界限适用于同一张被保留标记的图。选图规则在接缝处可以改变；不能删掉标记再声称全局连续。
相比之下，固定半球的正交投影反演在赤道附近条件数发散，
因为法向坐标是 $\sqrt{1-r_x^2-r_y^2}$。

<a id="section-4"></a>

## 4 纯态、矩阵秩和高维参数不是同一个概念

<a id="thm:dimension"></a>

#### 定理 4.1（纯态与固定秩密度族的维数）

$d$ 维复载体上的纯态空间为 $\mathbb{CP}^{d-1}$，实维数 $2d-2$。
秩恰为 $r$ 的密度矩阵流形实维数为

$$
\boxed{2dr-r^2-1,\qquad 1\le r\le d.}
$$

**证明。**

纯态在第 $k$ 个振幅非零的图中由 $d-1$ 个复比值 $z_j/z_k$ 唯一决定。
一般固定秩态先选择 $r$ 维复支持子空间。
在 Grassmann 局部图中，它是 $\mathbb{C}^r\to\mathbb{C}^{d-r}$ 的线性映射之图，
给出 $2r(d-r)$ 个实参数。
在固定支持上，正定 Hermitian 迹一矩阵有 $r^2-1$ 个实参数。
两项相加得到所示公式。

□

所以 qutrit 纯态虽秩一，仍有四个实参数；一般 qubit 混态秩二，有三个实参数。
高维线性空间本身可以完全线性，低维球面也可以是非线性流形。
因此“维数高”与“关系非线性”不能作为互相的定义。
项目 V44 已给 $2d-2$、$d^2-1$ 以及稳定三标量压缩的维数边界。[5](#ref-v44)

#### 定理 4.2（Gram 纯态与完整线性依赖）

给定不全为零的共同向量 $v_1,\ldots,v_k$，令
$G_{ij}=\langle v_i,v_j\rangle$。则

$$
G/\operatorname{Tr} G\text{ 为纯态}\iff
\dim\operatorname{span}\{v_i\}=1.
$$

**证明。**

令 $V e_i=v_i$，则 $G=V^\dagger V$ 且 $\ker G=\ker V$，
所以 $\operatorname{rank} G=\operatorname{rank} V$。非零正迹一矩阵纯恰等价于秩一。[8](#ref-watrous2)

□

这是“纯态对应关系完全线性依赖”的准确版本。二元时等价于
$\|v_1\|^2\|v_2\|^2=|\langle v_1,v_2\rangle|^2$。
这些向量是否具有一个共同 Gram 实现仍须先保证，不能仅逐边声明饱和。

<a id="thm:rank-error"></a>

#### 定理 4.3（降秩近似的最小操作误差）

设 $\rho$ 的特征值为 $\lambda_1\ge\cdots\ge\lambda_d\ge0$。
对 $1\le m\le d$，

$$
\boxed{\min_{\operatorname{rank}\sigma\le m}D(\rho,\sigma)
=\sum_{j>m}\lambda_j,\qquad \sigma\in\mathcal{D}(\mathbb{C}^d).}
$$

特别地，最近纯态距离为 $1-\lambda_1$。

**证明。**

任意候选 $\sigma$ 支持在秩不超过 $m$ 的投影 $Q$ 中。
迹距离控制任何效果的期望差，因此

$$
D(\rho,\sigma)\ge\operatorname{Tr}((I-Q)\rho)
\ge1-\sum_{j\le m}\lambda_j.
$$

最后一个不等式可在 $\rho$ 的特征基中用
$0\le Q_{jj}\le1$、$\sum_jQ_{jj}\le m$ 和特征值排序直接得到。
取前 $m$ 个特征向量上的投影 $P_m$，并令
$\sigma=P_m\rho P_m/s$，其中 $s=\sum_{j\le m}\lambda_j>0$。
共同对角基中，前 $m$ 项差值之绝对值和为 $1-s$，尾部也为 $1-s$，故达到下界。

□

若 $\operatorname{Tr}\rho^2\ge1-\varepsilon$，由 $\operatorname{Tr}\rho^2\le\lambda_1$ 得最近纯态距离不超过
$\varepsilon$。二元时的精确式是

$$
\min_{P\text{ 纯}}D(\rho_r,P)=\frac{1-\|r\|}{2}.
$$

这描述给定态的最优近似；不自动构成对未知态族的同一个可恢复物理压缩。

<a id="section-5"></a>

## 5 平方的生成地位：共同相位不变量定理

#### 定义 5.1（相位不变多项式）

在已给的复线性空间 $\mathbb{C}^d$ 上，将 $z\sim e^{i\theta}z$ 视为共同相位等价。
多项式指全空间实坐标上的多项式；等价地可唯一写成

$$
P(z,\overline z)=\sum_{\alpha,\beta}c_{\alpha\beta}
z^\alpha\overline z^\beta.
$$

若对全部 $z,\theta$ 有 $P(e^{i\theta}z,e^{-i\theta}\overline z)=P(z,\overline z)$，
称其相位不变。

<a id="thm:invariant"></a>

#### 定理 5.2（平衡次数与二次生成）

相位不变的充要条件是每个非零单项式满足 $|\alpha|=|\beta|$。
从而所有不变多项式均由

$$
\boxed{G_{ij}(z)=z_i\overline z_j}
$$

生成，非恒定不变量的最低总次数为二。
每个实值齐次二次不变量唯一写为

$$
Q_H(z)=z^\dagger Hz,\qquad H=H^\dagger.
$$

它对全部 $z$ 非负当且仅当 $H\succeq0$。

**证明。**

共同相位把单项式乘以 $e^{i(|\alpha|-|\beta|)\theta}$。
按整数频率分组，圆上不同字符的线性独立性迫使全部非零频率系数多项式消失。
唯一单项式展开因此只保留平衡项。
若 $|\alpha|=|\beta|=m$，把 $m$ 个 $z$ 因子与 $m$ 个共轭因子逐个配对，
就将该单项式写成 $m$ 个 $G_{ij}$ 的乘积。
二次时只有一个振幅与一个共轭振幅相乘。
对 $e_i,e_i+e_j,e_i+ie_j$ 代入，可见实值条件恰强迫系数矩阵 Hermitian；
非负性就是正半定的定义。

□

<a id="cor:complete-invariant"></a>

#### 推论 5.3（二次关系的完备性与相容方程）

矩阵 $G(z)=zz^\dagger$ 分离全部共同相位轨道，并保留
$\operatorname{Tr} G=\|z\|^2$。它的像为秩不超过一的正矩阵锥，满足

$$
G_{ij}G_{kl}=G_{il}G_{kj}.
$$

非零 $G$ 再作迹归一，才进一步消去正尺度。

**证明。**

外积相等时，非零像空间相同，两个向量只差标量；外积再使标量模为一。
零矩阵仅来自零向量。反向由正矩阵谱分解构造振幅。
显示的乘积恒等式直接来自复标量可交换。

□

在这个代数中，二次关系不能继续分解为两个非恒定*相位不变多项式*的乘积，
因为每个非恒定因子的次数至少二。
所以“平方是最低关系层”在这里获得精确含义。
它仍然是两个非不变振幅的乘积，并非所有数学意义下都不可分。

#### 命题 5.4（参数维数不等于多项式生成元个数）

全体实相位不变多项式的代数恰可由 $d^2$ 个实二次量生成，且不能用更少的代数生成元。

**证明。**

$d$ 个对角量、非对角量的实部与虚部共 $d^2$ 个，定理 [5.2](#thm:invariant) 给出生成性。
任一生成族可减去各自常数项；其非零最低次数至少二。
任何生成表达的二次部分只能是这些生成元二次部分的线性组合，因为两个非恒定因子相乘次数至少四。
实 Hermitian 二次型空间有 $d^2$ 维，所以生成元至少 $d^2$ 个。

□

对 $d=2$，四个全域多项式生成量可取 $S,Q_x,Q_y,Q_z$。
定理 [2.2](#thm:hopf) 用三个 $Q$ 恢复 $S=\|Q\|$，这是非多项式恢复，故不矛盾。
归一化把 $S$ 固定为一；纯态又满足球面方程。

最小次数的结论限于*全域多项式*。
$\|z\|^p$ 可以是相位不变的非多项式函数；在 $z_k\ne0$ 的图上，
$z_j/z_k$ 是零次的有理不变量。
高次量如 $(\operatorname{Tr} G)^2$ 也完全合法。
因此，相位商的二次生成定理还没有独自选定概率必须如何依赖这些生成元。

<a id="section-6"></a>

## 6 概率的平方律：正交可加与分解相容

### 正交合并选择径向平方权重

<a id="thm:weight"></a>

#### 定理 6.1（非负径向权重的唯一性）

设实内积空间 $V$ 的实维数至少二。
有限权重 $W:V\to[0,\infty)$ 只依赖范数，并满足

$$
u\perp v\Longrightarrow W(u+v)=W(u)+W(v).
$$

则存在 $c\ge0$，使 $W(v)=c\|v\|^2$。
复 Hilbert 版本亦成立，此时要求复维数至少二，并对复正交向量使用可加性。

**证明。**

取两个正交单位向量 $e_1,e_2$，令 $F(t)=W(\sqrt t\,e_1)$。
径向性和正交可加性给 $F(s+t)=F(s)+F(t)$。
非负性使 $F$ 单调。令 $c=F(1)$，有理数上的可加性给 $F(q)=cq$，
再以有理数上下夹逼所有非负实数，得到 $F(t)=ct$。
径向性完成证明。无需另加连续性。

□

若 $c>0$、$z\ne0$，将投影分支的概率规定为同一权重的份额，则

$$
p_i(z)=\frac{W(P_i z)}{W(z)}
=\frac{\|P_i z\|^2}{\|z\|^2},
\qquad \sum_iP_i=I,\quad P_iP_j=0\ (i\ne j).
$$

一维投影给出 $p_i=|\langle e_i,z\rangle|^2/\|z\|^2$。
这里输入了内积、正交性、径向性、权重可加与概率份额解释。
推导没有先假定权重的指数，却也没有从“二元逻辑”独立推导整个内积空间。

其他范数当然可以归一化数值；选择平方的进一步结构是内积极化。
对实范数 $Q(v)=\|v\|^2$，若满足平行四边形律

$$
Q(u+v)+Q(u-v)=2Q(u)+2Q(v),
$$

则 $g(u,v)=(Q(u+v)-Q(u-v))/4$ 是产生该范数的唯一实内积。
其证明先由平行四边形律得
$g(x+z,y)+g(x-z,y)=2g(x,y)$，取 $z=x$ 得倍增，
再取 $x=(u+v)/2,z=(u-v)/2$ 得可加；由范数连续性延伸实齐次。
对称性和正定性直接来自 $Q$。若另给等距复结构 $J^2=-I$，
则 $h(u,v)=g(u,v)+i g(Ju,v)$ 给第一变量共轭线性的复内积。
该复结构本身仍是新增条件。

### 整个效果域的可加读出

<a id="thm:effect"></a>

#### 定理 6.2（正可加概率的迹表示）

在有限维效果域 $\mathcal E=\{E:0\preceq E\preceq I\}$ 上，
设 $F:\mathcal E\to[0,1]$ 满足 $F(I)=1$，以及

$$
A,B,A+B\in\mathcal E\Longrightarrow F(A+B)=F(A)+F(B).
$$

则存在唯一密度矩阵 $\rho$，使 $F(E)=\operatorname{Tr}(\rho E)$。
若某个单位秩投影 $P_\psi$ 的读出为一，则 $\rho=P_\psi$，
从而所有效果的读出为 $\psi^\dagger E\psi$。

**证明。**

对正矩阵 $A$，选足够大的正整数 $m$ 使 $A/m\in\mathcal E$，定义
$\widetilde F(A)=mF(A/m)$。
使用共同倍数 $mn$，有限可加性保证定义不依赖 $m$；
取共同大分母又得到正锥上的可加性。
定义 Hermitian 差上的 $L(A-B)=\widetilde F(A)-\widetilde F(B)$。
若有另一分解，由 $A+B'=A'+B$ 可知定义一致。

正性给序保持；对有理数 $q>\|X\|$，
$-qI\preceq X\preceq qI$ 给 $|L(X)|\le q$。
令有理 $q$ 下降到 $\|X\|$，得 $|L(X)|\le\|X\|$。
所以可加泛函连续并实线性，有限维迹配对给唯一 Hermitian $\rho$。
对所有秩一投影的正性给 $\rho\succeq0$，$L(I)=1$ 给迹一。
若 $F(P_\psi)=1$，则 $\operatorname{Tr}(\rho(I-P_\psi))=0$。
正性迫使 $\rho$ 支持在这条射线上，故 $\rho=P_\psi$。

□

这是对完整效果菜单及同一效果不同分解的一致性要求。
项目 Ω 第 6 节已有相同类型的有限量子表示输入；
标准量子理论也将统计混合与密度矩阵凸组合的相容性明确列作假设。[6](#ref-omega)、[8](#ref-watrous2)

<a id="prop:cubic"></a>

#### 命题 6.3（二元归一与三轴吻合仍未决定 Born 读出）

对球面测量射线 $P(n)=(I+n\cdot\sigma)/2$，定义

$$
w(P(n))=\frac{1+n_z^3}{2}.
$$

它在每个正交互补对上归一，三标准轴读数与 $\lvert 0\rangle\langle 0\rvert$ 的 Born 值一致，
却不存在定理 [6.2](#thm:effect) 所要求的全效果可加扩展。

**证明。**

$0\le w\le1$ 且 $w(P(n))+w(P(-n))=1$。
取 $n_\pm=(\pm\sqrt3/2,0,1/2)$，两者读数均为 $9/16$。
但同一效果满足

$$
\tfrac12P(n_+)+\tfrac12P(n_-)
=\tfrac34P(e_z)+\tfrac14P(-e_z).
$$

有限可加性强迫这些有理倍数的齐次性。
左分解会给 $9/16$，右分解会给 $3/4$，矛盾。

□

用 $w_\lambda(P(n))=(1+(\lambda\cdot n)^3)/2$，并同时旋转单位标签 $\lambda$ 与 $n$，
还具有旋转协变性。因此各向同性形式、二元归一和有限三轴吻合不能替代分解相容性。

### 二次层的可检验代数特征

固定 $H=H^\dagger$ 与三条振幅分支 $u,v,w$，令 $Q(x)=x^\dagger Hx$，则

$$
\begin{aligned}
0={}&Q(u+v+w)-Q(u+v)-Q(u+w)-Q(v+w)\\
&+Q(u)+Q(v)+Q(w).
\end{aligned}
$$

证明是展开后所有单分支项与两两关系项抵消。
这是同一二次读出对固定分支的三阶差分消失。
若每次更换装置、改变分支传播，或把每个子实验另行归一化，
就不再是同一个 $Q$ 的上述恒等式，不能据此判断高阶干涉。

<a id="section-7"></a>

## 7 高维关系的精确二元递归

### 纯态的有序二叉树图册

#### 定义 7.1（内部参考与支持标记）

固定有序满二叉树，叶子从左到右标为 $1,\ldots,d$，
对应互相正交的基方向。对非零子树分量，取其第一个非零叶振幅为正实数的单位代表
$\chi_v$。零子树仅保存零标记，不定义单位代表。

<a id="thm:tree"></a>

#### 定理 7.2（纯态的逐节点球面重构）

每个非零内部节点可以写为

$$
\chi_v=a_v\chi_L\oplus b_v\chi_R,
\qquad |a_v|^2+|b_v|^2=1.
$$

左子树非零时 $a_v>0$ 为实数；左零时规定 $b_v=1$。
零子树对应的整项直接取该子空间的零向量，不调用未定义的 $\chi$。
保存该节点的纯二元投影

$$
P_v=\begin{pmatrix}a_v\\b_v\end{pmatrix}
\begin{pmatrix}\overline{a_v}&\overline{b_v}\end{pmatrix},
$$

以及树、叶标签与零标记，就能递归重建整个纯态射线。
固定支持含 $s$ 个非零叶时，非平凡双活分支节点恰有 $s-1$ 个，
共保留 $2s-2$ 个实参数。

**证明。**

左右子空间正交，子树投影的范数平方相加，故分解系数归一。
由于叶次序与左右次序一致，左子树非零时根参考叶就在左子树，
所以父子参考的相位一致，$a_v$ 为正实数。
$P_v$ 与该规范给出唯一系数：左活时

$$
a_v=\sqrt{(P_v)_{00}},\qquad
b_v=(P_v)_{10}/\sqrt{(P_v)_{00}};
$$

仅右活时取 $(0,1)$。
从叶子单位基向量开始递归组合，即恢复每个 $\chi_v$，最终恢复根射线。

反向任取满足标记与规范的节点数据，同样递归产生归一向量，
并返回原节点数据。在固定支持上收缩单活分支，剩下一棵有 $s$ 个叶的满二叉树，
其内部节点为 $s-1$。每个双活节点由一个严格介于零与一的权重和一个圆相位决定，
因此参数数目为 $2(s-1)$。

□

这是一种对描述的精确图册，跨支持边界的规范可能跳变。
它不声称存在把任意未知单份 $\psi$ 免费变成独立节点态张量积的固定 CPTP 操作。
局部代表的相位由父节点连接系数补偿，不能逐节点任意删去。
V44 的共同参考比值图册提供另一种 $d-1$ 个二元节点的精确表示；
本节把它组织为直接反复使用正交和的树结构。[5](#ref-v44)

#### 命题 7.3（节点描述不能普遍物理化为独立节点态）

> **编者注（Markdown 编者）：节点乘积命题的范围。** 此不可能性是含三叶结构的一般树编码障碍，下面证明使用三叶输入；不能将原命题读成每个固定维数均不可能。$d=2$ 时唯一二元节点就是输入纯态，恒等 CPTP 通道可实现；$d=1$ 时没有非平凡节点。对 $d\ge3$，在给定有序树中取三个叶，固定其余零标记，沿单活链保留相同节点，即可嵌入下面的三叶反例。

不存在将每个未知纯态精确转成上述全部归一节点态张量积的固定 CPTP 通道。

**证明。**

考虑三叶树，根分为 $\{1\}\mid\{2,3\}$。
取右子树内两个单位正实向量 $u,v$，令 $0<r=\langle u,v\rangle<1$，并取 $0<\varepsilon<1$。
两个全支撑输入为

$$
\psi=\sqrt{1-\varepsilon}\,e_1+\sqrt\varepsilon\,u,
\qquad
\phi=\sqrt{1-\varepsilon}\,e_1+\sqrt\varepsilon\,v.
$$

它们的根节点相同，右节点分别为 $P_u,P_v$。
所以输出节点张量包的重叠模为 $r$，输入重叠却为
$1-\varepsilon+\varepsilon r>r$。
纯态迹距离公式说明输出距离严格增大，与 CPTP 收缩相矛盾。
这里的收缩可由效果变分式直接看出：通道的伴随把每个输出效果送回输入效果，
故输出期望差的最大值不能增加。[9](#ref-watrous3)

□

### 一般态须保留算子值关系与 Schur 余量

先令两个对角块作用于同一个有限维空间。对块矩阵

$$
M=\begin{pmatrix}A&C\\C^\dagger&B\end{pmatrix},
\quad S=A+B,\ X=C+C^\dagger,\ Y=i(C-C^\dagger),\ Z=A-B,
$$

有精确恒等式

$$
\boxed{M=\tfrac12(I\otimes S+\sigma_x\otimes X+
\sigma_y\otimes Y+\sigma_z\otimes Z).}
$$

继续分解时保留整个 $S,X,Y,Z$，不能用 $\operatorname{Tr} S$ 代替 $S$。
若左右维数不同，可先补零成等大块；不补零时须保留原来的矩形关系类型。
$X,Y,Z$ 一般不是正矩阵，故不能不加类型转换就分别作概率归一。
该递归是 V37、V44 的既有结构。[4](#ref-v37)、[5](#ref-v44)

<a id="thm:schur"></a>

#### 定理 7.4（零 Schur 余量与纯态延续）

对以上有限维 Hermitian 块矩阵，$M\succeq0$ 当且仅当

$$
A\succeq0,\quad \operatorname{Ran} C\subseteq\operatorname{Ran} A,\quad
R=B-C^\dagger A^+C\succeq0.
$$

成立时 $\operatorname{rank} M=\operatorname{rank} A+\operatorname{rank} R$。
若 $A\ne0$，则整体秩一等价于 $A$ 秩一且 $R=0$，并满足该像空间条件。

**证明。**

正性先使 $C^\dagger$ 消去 $\ker A$。
令 $Y=A^+C$，则 $AY=C$，并有

$$
\begin{pmatrix}x\\y\end{pmatrix}^{\!\dagger}
M\begin{pmatrix}x\\y\end{pmatrix}
=(x+Yy)^\dagger A(x+Yy)+y^\dagger Ry.
$$

故得到充要性与可逆合同分解 $A\oplus R$，从而得到秩式。
$A=0$ 时正性先强制 $C=0$，应单独由 $B$ 判断秩。

□

也可以选 $\rho=AA^\dagger$，把 $A$ 的矩阵元组成内部纯化
$\Psi=\sum_{i,a}A_{ia}\lvert i\rangle\lvert a\rangle$，再对该纯向量使用树图册。
部分迹回原系统给出 $\rho$。纯化态与原约化态是不同对象，
增加的因子仍属整体内部；它保存了原混态所需的相关结构。

### 每个标量接口接入同一个原生 AURIC 编码

V37 给出固定等距 $J:\mathbb{C}^2\to\mathbb{C}^5$，$J^\dagger J=I$，
使二元态的原占据均值满足

$$
u(\rho)=u_0+\nu r,\qquad
\nu=(1+2\sqrt3+\sqrt{11})^{-1},
$$

$$
u_0=\left(\tfrac\nu2(\sqrt3+\sqrt{11}),
\tfrac\nu2(\sqrt3+\sqrt{11}),\nu\right).
$$

因而纯节点落在 $\|u-u_0\|=\nu$ 的球面，一般二元节点落在球内。
这使上述每个二元图表都能接回原五模式。
V44 对全部二元主块也已有相干等距 $W_d=(I_{\mathrm{label}}\otimes J)V_d$。
[4](#ref-v37)、[5](#ref-v44)
归一的 null 模式仍是一个事件；单位元的期望或完整分支总质量承担归一化。
三均值在指定编码族上统计完备，并不意味着单次经典结果可以恢复未知量子态。

对于任意数学酉 $U\in U(2)$，同一个编码还给出

$$
\widetilde U=JUJ^\dagger+(I_5-JJ^\dagger).
$$

编码子空间与其正交补互不相交，故交叉项为零，
$\widetilde U^\dagger\widetilde U=JJ^\dagger+I_5-JJ^\dagger=I_5$，且
$\widetilde UJ=JU$。
这说明全部二元数学酉门都能在该子空间相干提升；
给定物理门菜单能否实现该酉及代价多少，仍须另给实现证明。[4](#ref-v37)

<a id="section-8"></a>

## 8 物理无损与降秩：整个态族的压缩定理

#### 定义 8.1（可恢复压缩）

设 $\mathcal E:\mathcal{D}(\mathcal{H})\to\mathcal{D}(\mathbb{C}^m)$ 与
$\mathcal R:\mathcal{D}(\mathbb{C}^m)\to\mathcal{D}(\mathcal{H})$ 为固定 CPTP 映射。
若 $\mathcal R\mathcal E(\rho)=\rho$ 对目标族中全部态成立，称其可恢复地压缩到 $m$ 维。
未计入编码载体的、依赖输入的标签不能再交给解码器；若保留它们，须一并计入载体。

<a id="thm:support-compress"></a>

#### 定理 8.2（固定支持族的精确最小载体）

> **编者注（Markdown 编者）：非零支持。** 本定理的可达到最小载体按 $1\le r<\infty$ 理解，压缩载体维数为正整数。零维支持没有密度态，不能在补全 CPTP 编码时选取其中的固定态；该退化情形不由下面的达到性构造覆盖。

对 $\dim K=r$，若要恢复全部 $\mathcal{D}(K)$，则 $m\ge r$，且可达到。

**证明。**

密度矩阵实线性张成支持 $K$ 上全部 Hermitian 矩阵，维数 $r^2$。
恢复恒等式延伸到此线性包络，使编码在其中单射；目标 Hermitian 空间维数为 $m^2$，
故 $r^2\le m^2$。

取 $V:\mathbb{C}^r\to\mathcal{H}$ 等距且 $VV^\dagger=P_K$。
在支持族上，$\mathcal E(\rho)=V^\dagger\rho V$、$\mathcal R(\sigma)=V\sigma V^\dagger$
互逆。全空间上的 CPTP 编码可补为

$$
\mathcal E(\rho)=V^\dagger\rho V+\operatorname{Tr}((I-P_K)\rho)\tau_0
$$

其中 $\tau_0$ 为固定压缩态。

□

<a id="thm:pure-family"></a>

#### 定理 8.3（任意纯态族的线性包络下界）

若纯态族 $\mathcal F$ 可由上述固定信道精确恢复，则

$$
\boxed{m\ge\dim\operatorname{span}\{\psi:P_\psi\in\mathcal F\}.}
$$

**证明。**

取族中 $r$ 个线性独立的 $\psi_i$，令 $\sigma_i=\mathcal E(P_{\psi_i})$。
对 $\sigma_i$ 谱分解，由纯输出的极端性，每个正权重谱向量 $v_i$ 都满足
$\mathcal R(P_{v_i})=P_{\psi_i}$。
写解码器的 Kraus 等距

$$
Wv=\sum_\alpha K_\alpha v\otimes\lvert \alpha\rangle.
$$

输出为纯态意味着 $Wv_i=\psi_i\otimes\eta_i$，其中 $\|\eta_i\|=1$。
若 $\sum_i c_i\psi_i\otimes\eta_i=0$，在第一因子上逐个作用于 $\psi_i$ 对偶的线性泛函，
得到 $c_i\eta_i=0$，故全部系数为零。
于是 $Wv_i$ 及 $v_i$ 线性独立，压缩空间至少 $r$ 维。

□

每个态秩一，不表示整个纯态族只需一维载体。
另一方面，若只要求重现一个事先已知的边缘密度矩阵，
解码器可直接制备它，即使它混合也可从一维输入产生。
要让单态秩成为恢复下界，应要求保全它与内部参考的相关性。

#### 推论 8.4（保全内部参考恢复固定支持族）

设 $\rho$ 的秩为 $r$，取满 Schmidt 秩纯化

$$
\Omega_\rho=\sum_{i=1}^r\sqrt{\lambda_i}\lvert i\rangle_A\lvert i\rangle_R,
\qquad\lambda_i>0.
$$

若 $((\mathcal R\mathcal E)\otimes\mathrm{id})(P_{\Omega_\rho})=P_{\Omega_\rho}$，
则 $m\ge r$。

**证明。**

比较参考因子上的每个矩阵单位系数，得到
$\mathcal R\mathcal E(\lvert i\rangle\langle j\rvert)=\lvert i\rangle\langle j\rvert$ 对全部 $i,j\le r$ 成立。
所以它恢复全部支持族，使用定理 [8.2](#thm:support-compress) 即可。

□

#### 命题 8.5（完整线性范数保全不降低秩）

若复线性 $V:\mathbb{C}^d\to\mathbb{C}^m$ 对所有单位向量保持单位范数，则
$V^\dagger V=I$，$m\ge d$，且

$$
\operatorname{rank}(V\rho V^\dagger)=\operatorname{rank}\rho.
$$

等维时 $V$ 为酉，密度矩阵谱完全不变。

**证明。**

齐次性使 $V$ 保持全部范数，复极化恒等式使它保持内积。
正交基的像仍正交，故为等距且不降低载体维数。
它将 $\rho$ 的支持单射地映到输出支持，因此秩不变；等维酉共轭保持特征值。

□

所以“识别出秩一约束”“用较少参数描述”“条件化后降秩”和“整体酉演化”需要分别说明。
恒等信道对混态无损；常值重置也能输出纯态却丢掉输入区别。
纯性不是任意编码过程无损的同义词。

<a id="section-9"></a>

## 9 本轮项目新增：K-bonacci 秩一恢复与资源律

本轮真正相关的新段，是端点层析文稿第 7 节的实际取得协议。[7](#ref-kbonacci)
固定整数 $k\ge2$，坐标指标为 $0,\ldots,k-1$，其目标是

$$
R=c\ell^{\mathsf T},\qquad c,\ell\in(0,\infty)^k,
$$

允许非对称；逐元正不等于 Hermitian 半正定。
同源制备权限每次供应精确相同的未知 $c$，固定量具为 $\ell$。
每个长度 $k+1$ 的合法窗口末必须取得并付费一个读数，不能在窗口内部读。

### 来源中的明确取得与重建

记 $C_j=\sum_{i<j}c_i$，初读 $D_0=\ell^{\mathsf T}c$。
项目新定理给固定次序：对 $j=1,\ldots,k-1$ 各使用一次同源制备，
依次执行两个实际合法窗口

$$
1^{k-j}01^j,\qquad 0^{k+2-j}1^{j-1}.
$$

两次窗口末读数为

$$
Y_j=C_j\ell_j,\qquad Z_j=C_j\ell_{j-1}.
$$

取 $b_0=1$、$b_j=b_{j-1}Y_j/Z_j$，便有 $b_j=\ell_j/\ell_0$。
取 $H_0=0$、$H_j=Z_j/b_{j-1}$，则 $H_j=\ell_0C_j$。
再令

$$
a_i=H_{i+1}-H_i\quad(i<k-1),\qquad
a_{k-1}=\frac{D_0-\sum_{i<k-1}a_ib_i}{b_{k-1}}.
$$

直接代入给 $a_i=\ell_0c_i$，所以 $R_{it}=a_ib_t$。
严格正性使所有除法合法。

收费 A 每次制备都必须实际取得并付费初读。
收费 B 必须实际付费取得一次共同初读，后续制备可省略初读；若再次读取仍要收费。
在这两个合同下，最坏资源最小值为

<div style="overflow-x:auto" tabindex="0" role="region" aria-label="表格 4">

| 资源 | 尖锐最小值 |
| --- | --- |
| 同源制备次数 | $k-1$ |
| 窗口次数 | $2k-2$ |
| 收费 A：每次制备都读初值 | $3k-3$ 次总读数 |
| 收费 B：取得共同初读后省去重复初读 | $2k-1$ 次总读数 |

</div>

制备下界是每个正世界上的结论；窗口和总读数下界是最坏世界结论，不能改成逐世界。
来源证明允许策略不连续、不可测、不可计算，但要求确定性、全域正确和逐点有限终止。

制备下界的关键很直接：一个运行的第一次秩一窗口只保留某个前缀和 $C_j$，
后续非零读数只能是同一个 $C_j$ 乘不同 $\ell_t$。
少于 $k-1$ 次制备，加上初读，仍不足以消去 $c$ 的所有线性不可见方向；
在严格正域作足够小的零方向扰动，会产生目标不同而整个确定性历史相同的两个世界。
窗口下界另用有限多项式读出族的共同正则点与常秩纤维，
再回放同一有限历史；本文亲读了该新段，不声称执行了形式验证。

### 本轮推论：秩一归一幂等仍需 Hermitian 类型

<a id="prop:oblique"></a>

#### 命题 9.1（正秩一实关系成为量子纯态的条件）

令 $S=\operatorname{Tr} R=\ell^{\mathsf T}c>0$。
则 $Q=R/S$ 满足 $Q^2=Q$、$\operatorname{Tr} Q=1$、$\operatorname{rank} Q=1$。
它是量子纯态当且仅当 $c$ 与 $\ell$ 正比例。

**证明。**

$R^2=c(\ell^{\mathsf T}c)\ell^{\mathsf T}=SR$，给出幂等与迹、秩。
Hermitian 条件在实情形为 $c_i\ell_j=c_j\ell_i$。
严格正性使这等价于全部 $c_i/\ell_i$ 相等。
此时 $R$ 为一个正向量外积的正倍数，归一后为纯态；反向纯态必须 Hermitian。

□

一般的 $Q$ 是斜投影，不能因为迹一、幂等和秩一就替换为密度态。
这条判据是本轮基于来源类型作出的纸面推论，不是新增入库定理。

<a id="thm:diagonal-bridge"></a>

#### 定理 9.2（保留全部信息的正对角相似分解）

对上述严格正关系，令

$$
u_i=\sqrt{c_i\ell_i},\qquad
D=\operatorname{diag}\sqrt{\ell_i/c_i},\qquad
P=uu^{\mathsf T}/S.
$$

则 $P$ 是实纯态，且

$$
\boxed{DRD^{-1}=uu^{\mathsf T},\qquad R=S D^{-1}PD.}
$$

完整等价数据为总尺度 $S$、正概率向量 $q_i=R_{ii}/S$，
以及正对角 $D$ 模共同正倍数，其逆式为

$$
P_{ij}=\sqrt{q_iq_j},\qquad
\frac{d_j}{d_i}=\sqrt{\frac{R_{ij}}{R_{ji}}},\qquad
R_{ij}=S\sqrt{q_iq_j}\frac{d_j}{d_i}.
$$

**证明。**

逐项相乘得到

$$
\sqrt{\ell_i/c_i}\,c_i\ell_j\sqrt{c_j/\ell_j}
=\sqrt{c_i\ell_i}\sqrt{c_j\ell_j}.
$$

$\|u\|^2=S$，所以 $P$ 正、迹一且秩一。
两方向矩阵元之比给 $R_{ij}/R_{ji}=(d_j/d_i)^2$，
严格正性选择唯一正平方根，并确定 $D$ 的比例类。
任意 $S>0$、正概率 $q$ 与正对角比例类反向给
$c_i=\sqrt S\sqrt{q_i}/d_i$、$\ell_i=\sqrt S\sqrt{q_i}d_i$，
所以表示双向完备。

□

参数账式是

$$
1+(k-1)+(k-1)=2k-1.
$$

只留下纯态代表 $P$，就丢掉尺度及非对称比值。例如固定

$$
P=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad D=\operatorname{diag}(1,t),
$$

所有 $t>0$ 对应

$$
R_t=\frac S2\begin{pmatrix}1&t\\t^{-1}&1\end{pmatrix},
$$

它们共享同一个 $P$，关系却各不相同。
严格正性也不可省略：$\left(\begin{smallmatrix}1&1\\0&0\end{smallmatrix}\right)$
不能由正对角相似变成对称矩阵。

这个 $D$ 依赖目标且通常非酉，给出的是完整代数分解，
没有供应 K-bonacci 到原生 FIB 的来源、操作、物理制备或读数协议桥。
源文的该物理／来源级桥仍开放；本轮分解保留了需要额外传递的规范数据。
新协议也未供应噪声稳定性或有限精度成本，不能把精确单射等同于自动取得。

<a id="section-10"></a>

## 10 内生静态图中的二次传导与条件量子起源

<a id="thm:instrument"></a>

#### 定理 10.1（内部正交记录的平方传导）

给定复线性分支算子 $K_i$，满足 $\sum_iK_i^\dagger K_i=I$。
令记录槽位互相正交，定义

$$
V\psi=\sum_i\lvert i\rangle\otimes K_i\psi.
$$

则 $V$ 是等距，纯输入给出整体纯态。
在定理 [6.1](#thm:weight) 中 $c>0$ 的非零正交权重合同下，记录概率为

$$
p_i=\|K_i\psi\|^2
$$

对单位输入成立。多层记录历史 $h=(i_1,\ldots,i_t)$ 满足

$$
p_h=\|K_{i_t|i_{<t}}\cdots K_{i_1}\psi\|^2,
\qquad\sum_h p_h=1,
$$

其中每个节点的条件分支族均满足完备性。

**证明。**

记录正交给 $\|V\psi\|^2=\sum_i\|K_i\psi\|^2=\|\psi\|^2$，
所以等距。权重定理把每个正交记录分量的权重规定为其平方范数。
多层由逐节点完备性求和，归纳保持总质量。

□

每个正质量历史可条件化；零质量历史保留零标记，不能除以零。
记录、参考与其余系统都可以内生。把多个不可区分的内部路径合成同一个读出时，
则必须按保留的相干或被忽略的记录重新计算，不能将每个符号索引自动当成可读经典结果。
项目 Ω 的记录、传播核和内部扩张正是在这一层面给出框架。[6](#ref-omega)

二次关系矩阵沿线性振幅变换传导为

$$
G=\psi\psi^\dagger\longmapsto UGU^\dagger.
$$

对 $G$ 来说这是线性的；对振幅来说读出 $\operatorname{Tr}(HG)$ 是二次的。
所以“线性关系与平方”可以统一为*不同对象层之间的表示*：
振幅空间的线性作用，经相位不变量提升后，仍在线性关系矩阵空间传导。
这没有要求高维空间本身必须非线性。

#### 命题 10.2（二次零残差与纯态条件的接合）

> **编者注（Markdown 编者）：残差族与态的范围。** 本命题按有限维正常化密度矩阵及有限约束族理解；若允许无限约束族，须先保证正项和定义了所用正算子及二次型，才能使用后文的平方根、迹和支持推理。一般无界算子与非正常态不由此有限证明覆盖。

给定 $H=\sum_jw_jL_j^\dagger L_j$、$w_j>0$，则

$$
\psi^\dagger H\psi=0\iff L_j\psi=0\quad\forall j.
$$

密度态零罚集合为 $\mathcal{D}(\bigcap_j\ker L_j)$，故一维共同核唯一选出纯态。
二元非零正约束有零罚态时，令 $\widehat H=H/\operatorname{Tr} H$，其唯一解是
$\rho_*=I-\widehat H$。

**证明。**

正平方项之和为零当且仅当每项为零。
对密度态用 $\operatorname{Tr}(H\rho)=\|H^{1/2}\rho^{1/2}\|_{\mathrm{HS}}^2$ 得支持判据。
二元非零可满足约束必秩一，核投影就是归一约束投影的正交补。

□

这复用上一轮的约束对偶，并把它放入本轮相位不变量及概率相容结构中。
一般 $\|L\psi\|^q$ 对任意 $q>0$ 也有同一个零集合；
选择二次需要本轮已经明确的正算子表示、内积或可加读出条件。

<a id="section-11"></a>

## 11 本轮可固定的总命题与仍然独立的前提

#### 定理 11.1（复相位关系的二次生成与递归表示原则）

给定有限维复线性振幅空间、共同 $U(1)$ 相位等价，
则全部相位不变多项式关系由 $zz^\dagger$ 的二次矩阵元生成，
该矩阵保留全部相位轨道与总尺度。
二元情况下可由三实 Hopf 坐标完整表示，归一纯态是内在二维球面。
有限高维纯态可由完整二元图册或定理 [7.2](#thm:tree) 的树节点精确重构；
一般态可由全体二元主块或算子值递归保存。

若另要求非负径向权重在正交和上可加，则权重为平方范数；
若在完整效果域要求正可加与归一，则概率为密度态的迹读出，
对纯源得到 Born 平方律。
物理可恢复压缩另受目标族支持与线性包络维数限制。

**证明。**

分别应用定理 [5.2](#thm:invariant)、推论 [5.3](#cor:complete-invariant)、
定理 [2.2](#thm:hopf)、[3.1](#thm:charts)、[7.2](#thm:tree)、
[6.1](#thm:weight)、[6.2](#thm:effect) 与 [8.3](#thm:pure-family)。
全体二元主块给每个对角及非对角矩阵元，故保留质量、标签与相容性时可重构一般态；
算子值递归则是第 7 节的精确块恒等式。

□

可数振幅与关系仍可使用逐有限图册、相容有限截断及明确收敛条件处理；
每个多项式只涉及有限多个变量，二次生成论证逐项保持。
无限级数、无限读出和全局稳定性需要相应收敛与一致预算，
不能从有限层闭合直接省略这些条件。

<div style="overflow-x:auto" tabindex="0" role="region" aria-label="表格 3">

| 直觉表述 | 本轮可证明的准确版本 |
| --- | --- |
| 四维放进三维而无损 | 二元复振幅先商共同相位；三轴保留总尺度及相对信息 |
| 纯态三维信息可放二维 | 归一二元纯态为二维球面；完整二维图册保留接缝或图标记 |
| 纯态就是可以降秩 | 纯态已经秩一；约束减少参数，物理无损压缩须按整个目标族证明 |
| 平方是最低关系 | 共同相位不变的全域多项式中，二次为最低生成层 |
| 高维关系可二元分解 | 保留树结构、标签、尺度、相对相位和跨块关系后有精确递归 |
| 归一化必然选平方概率 | 再加正交权重可加或全效果分解相容，才得到平方读出 |

</div>

三维 qubit 读出依赖于复数域：二阶 Hermitian 矩阵的两个实对角及一个复关系共有四实参数，
迹归一后剩三个。若只用实振幅，关系项只有一个实数，归一二元态给二维圆盘，纯态给圆周。
平方结构在实内积空间中同样成立，因此平方本身不单独选择复量子理论。
复结构、允许的复合系统、概率菜单及可执行操作，还须作为物理前提说明或由其他可检验原则推出。

本轮没有使用数学程序、数值枚举、CAS 或 Lean 执行来代替证明，也未修改项目仓库。
源码身份用固定公开版本与文件哈希核对；这不等于独立认证整个项目。
K-bonacci 第 7 节的精确恢复与资源律是实际新增；
旧 Hopf／图册结论、上一轮蓝图更新与本轮新推论各自保留归属。

## 固定来源、归属与阅读范围

<a id="ref-head"></a>

**[1]**
the-omega-institute/trureturing，固定提交
[e42edf53c936<wbr>8a5d53e7e780<wbr>da2d2244493f<wbr>dfcc](https://github.com/the-omega-institute/trureturing/commit/e42edf53c9368a5d53e7e780da2d2244493fdfcc)，
2026-10-31 21:49:06 SGT，合并 PR #24798。

<a id="ref-compare"></a>

**[2]**
[v51 至 v52 的固定比较](https://github.com/the-omega-institute/trureturing/compare/d2950bd36448c5d4f6c4a3e5671ef734185145c9...e42edf53c9368a5d53e7e780da2d2244493fdfcc)。
完整差异包含 933 个路径；API 比较列表仅前 300 项，故另用未截断的 1109 项 theory 树核对。
理论正文仅 K-bonacci 与 Lyndon 两篇修改。没有 Quantum Blueprint 新变更。

<a id="ref-v24"></a>

**[3]**
[AURIC Two Basis States, Three Channels, Phase Chirality and Recursive Square Law V24](https://github.com/the-omega-institute/trureturing/blob/e42edf53c9368a5d53e7e780da2d2244493fdfcc/docs/develop/theory/AURIC_TWO_BASIS_STATES_THREE_CHANNELS_PHASE_CHIRALITY_AND_RECURSIVE_SQUARE_LAW_V24.md)。
本轮亲读 176–294 行，含 Hopf 商、相位圆纤维、两读出正负分支与半球稳定性。
标准公式为既有结果；未归一保尺度形式为其直接齐次扩展。

<a id="ref-v37"></a>

**[4]**
[AURIC Binary Relations and Unitary Representation V37](https://github.com/the-omega-institute/trureturing/blob/e42edf53c9368a5d53e7e780da2d2244493fdfcc/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)。
固定原生 $J$、三均值球、同尺度关系与统计读数／相干编码的区别；
本轮来源审计核对 50–88、150–348 行，算子递归沿用既有已读段。

<a id="ref-v44"></a>

**[5]**
[AURIC Boundary Extension and Higher Dimensional Relational Atlas V44](https://github.com/the-omega-institute/trureturing/blob/e42edf53c9368a5d53e7e780da2d2244493fdfcc/docs/develop/theory/AURIC_BOUNDARY_EXTENSION_AND_HIGHER_DIMENSIONAL_RELATIONAL_ATLAS_V44.md)。
本轮亲读 45–100、521–619、996–1035 行，含逆立体投影、纯态图册、$2d-2$、循环条件与稳定维数下界。
全体主块、$W_d$ 与 Schur 条件沿用前轮已核对且本轮未变的第 8–11 节。

<a id="ref-omega"></a>

**[6]**
[AURIC Ω Static Compatibility Fiber Theory](https://github.com/the-omega-institute/trureturing/blob/e42edf53c9368a5d53e7e780da2d2244493fdfcc/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
本轮亲读 125–154 行的响应商；效果表示、内生记录及恢复范围沿用前轮已读段及本轮来源复核。
本文不从静态性单独推导复 Hilbert、正效果或 CP 操作等输入。

<a id="ref-kbonacci"></a>

**[7]**
[KBonacci Endpoint Tomography and Rank-One Relation Boundaries](https://github.com/the-omega-institute/trureturing/blob/e42edf53c9368a5d53e7e780da2d2244493fdfcc/docs/develop/theory/KBONACCI_ENDPOINT_TOMOGRAPHY_AND_RANK_ONE_RELATION_BOUNDARIES.md)。
本轮完整亲读 1–438 行；真正追加的是 250–437 行第 7 节，净增 190 行。
精确同源制备与收费合同、恢复公式、资源下界及正秩一非对称类型均保留。
本文对角相似桥与幂等纯态判据为本轮纸面推导，不声称已入库或给出物理类型桥。

<a id="ref-watrous2"></a>

**[8]**
John Watrous，*The Theory of Quantum Information*，
[第 2 章：Basic Notions of Quantum Information](https://jhwatrous.github.io/TQI.2.pdf)，作者公开章节。
亲读纯态与整体相位、统计混合假设及基本状态定义；用于标准密度态、信道与扩张语言。

<a id="ref-watrous3"></a>

**[9]**
John Watrous，*The Theory of Quantum Information*，
[第 3 章：Similarity and Distance among States and Channels](https://jhwatrous.github.io/TQI.3.pdf)，作者公开章节。
标准迹距离与效果可区分性；本文所用距离、近似与压缩界另给证明。

<a id="ref-hatcher"></a>

**[10]**
Allen Hatcher，*Algebraic Topology*，
[第 2 章，第 2.B 节，定理 2B.3 与推论 2B.4](https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf)，印刷页 172。
亲读域不变定理及紧流形嵌入推论，用于球面不存在单张连续单射平面坐标的标准拓扑前提。

<!-- 原稿文档结束 -->

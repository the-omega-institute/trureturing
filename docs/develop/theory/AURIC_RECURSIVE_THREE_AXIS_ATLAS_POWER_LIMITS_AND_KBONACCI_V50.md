# AURIC：递归三轴图册、幂极限

# 与 K-bonacci

定义、定理与纸面证明　v50.0

2026 年 10 月 31 日　Asia/Singapore

> **版本与归属（编者）**：下文为所供 v50.0 原稿的完整 Markdown 转写。原文“本轮”“本文”及其中的 HEAD 获取、下载、核读、比较、blob、未运行程序和制作行为，均为原作者对其历史工作的陈述；不是转写者声称重做这些行为。单列的“编者核读注”是本版的局部条件说明。纸面论证与来源核读不构成 Lean/kernel、原生实现、物理或经验认证。

## 原稿元数据（作者设置）

PDF 标题：AURIC：递归三轴图册、幂极限与 K-bonacci  
PDF 作者：AURIC research continuation  
PDF 主题：Binary normalization, exact contraction, finite-window limits and collective-spin geometry

<details>
<summary>原稿编译、字体、编号与页眉页脚设置</summary>

原稿使用 XeLaTeX，编译两次；AURICFontPath 可指向 Noto CJK OTF 目录。
文类为 article，11pt、A4；页边距 23mm，页眉高度 16pt。
主字体优先为 Noto Serif CJK SC；指定字体目录时使用 NotoSerifCJKsc-Regular.otf 与 NotoSerifCJKsc-Bold.otf，斜体沿用常规体、粗斜体沿用粗体。
未指定目录时先查同名字体，否则使用 FandolSong-Regular.otf 与 FandolSong-Bold.otf，同样以常规体和粗体代斜体。
等宽字体为 Latin Modern Mono；中文断行 locale 为 zh，断行间距为 0pt plus 1pt。
链接颜色为 auricblue，RGB 为 (24,53,79)，保留 Unicode 链接元数据。
定义、定理、命题、推论与说明按节共用编号；证明、摘要与书目标题分别为“证明”“摘要”“固定来源、归属与阅读范围”。
段首缩进为 1.8em，段间距为 2pt，紧急伸长为 3em；列表无额外间距，左边距为 2em。
原稿左页眉为“AURIC：递归三轴、幂极限与 K-bonacci”，右页眉为“v50 / 2026-10-31”，页脚中间为页码；公式允许的分页等级为 2。
标题两行间距为 7pt，标题与副标题间距为 8pt，副标题与日期间距为 5pt。

</details>

## 摘要
本文继续研究“二元关系归一化后反复提升为三轴表示”。
二阶 Hermitian 正关系经过迹归一化恰为 Bloch 球；其正性和球面纯态条件都在收敛极限下保持。
完整对称幂、逐坐标幂、矩阵幂以及张量 Gram 幂是不同运算：
它们分别增加相干像的余维、形成球面非线性动力学、选择最大特征空间，
或使二元相干关系衰减，不能合称为约束逐渐消失。
正质量可由二叉树上的局部球面点和根尺度精确重建，
一般高维量子关系则需要算子值三轴与跨节点相干块。
对 K-bonacci 给出归一递推、全初值总变差收缩及尺度恢复；
其定态到无限几何分布的距离恰为 $2^{-k}$，从而得到迭代步数与阶数的联合稳定界。
项目已有的有限窗口二进制极限准确支持“可见禁词约束消失”，
但完整未来响应的 Hankel 秩仍随 $k$ 增长。
对称复合的平均自旋又提供另一种严格极限：交换子和最小总方差按 $1/m$ 缩小，
而三轴几何约束保持，内部观察纤维变大。
全文使用纸面证明，区分项目既有结论、本轮推导与仍需供应的物理实现。

## 1　主命题、固定项目与参数分工

本轮可以成立的主命题是：

> 同一个二元归一化接口可以反复使用。阶数增加时，需要增长的是接口之间的连接、
> 被保留的尺度、历史与高阶关系。某些有限预算下的约束可以消失，
> 但局部正性、归一化和全局相容性并不会因此全部消失。

本轮固定项目 `dev` 提交为
`a6ed97ef09691efed393942b6ae694c4a44e5fc9`，
 时间为 2026-10-31 20:48:35（新加坡）。
相对 v49 的
`e168d4bbef773d94df790275d1f4f2a9e373103f`，

完整 theory 树有 1109 项，实际变更四个理论路径。
与本题最直接有关的 K-bonacci 两篇、RRO 有限分辨率及 FIB 关系综合均为既有工具；
量子续卷 III 真正追加的是 §§183–189 的来源熵率与截断误差结果。
新入库的 V46 是历史作者稿，不能把入库时间当成另一份独立证明。[[1]](#ref-head) [[2]](#ref-compare) [[3]](#ref-kboundary) [[4]](#ref-kendpoint) [[5]](#ref-rro) [[6]](#ref-fibsynth) [[7]](#ref-iii) [[8]](#ref-v46)

本文区分以下参数：

| 记号 | 含义 |
| --- | --- |
| $m$ | 对称张量或幂的次数；集体自旋的复合份数 |
| $k$ | K-bonacci 的记忆阶数；禁止连续 $k$ 个一 |
| $t$ | 固定 $k$ 下归一化递推的迭代步数 |
| $n$ | 实际观察的原始二进制词长 |
| $d$ | 二叉分解的深度或已提取的叶子数 |

这些参数可相关，但定义上互不相同；“指数趋于无穷”必须先说明取哪一个极限。

采用用户的内生约定：相位参考、观察者、记录、辅助槽位与调用索引
都属于同一静态整体。下文的时间索引可理解为内部记录之间的顺序。
数学直和、张量或辅助系统不表示存在整体之外的本体；
同时，形式表示不自动证明相应操作、准备和读数可以实际取得。

## 2　平方与受约束三维：精确对象是二元正关系

#### 定义 2.1（二元关系及尺度）

给定

$$
G=\begin{pmatrix}A&C\\\overline C&B\end{pmatrix}\succeq0,
\qquad S=A+B>0,
$$

定义归一关系 $\rho=G/S$，以及三轴

$$
r=(x,y,z)
=\frac{(2\operatorname{Re}C,-2\operatorname{Im}C,A-B)}{S}.
$$

这里 $A,B$ 是两侧权重，$C$ 是复关系，$S$ 是总尺度。

<a id="thm:gram"></a>

#### 定理 2.2（二元正关系与球体的精确对应）

有

$$
\rho=\frac{I+x\sigma_x+y\sigma_y+z\sigma_z}{2},
\qquad
1-\|r\|^2=\frac{4(AB-|C|^2)}{S^2}\ge0.
$$

反之，任意 $r\in\mathbb{R}^3$、$\|r\|\le1$ 唯一确定一个正的迹一二阶矩阵。
非零 $G$ 秩一当且仅当 $\|r\|=1$。

**证明。**

展开 Pauli 矩阵得到所示表示，并计算

$$
S^2-(A-B)^2-4|C|^2=4(AB-|C|^2).
$$

$G\succeq0$ 等价于 $A,B\ge0$ 及 $AB\ge|C|^2$。
给定 $r$ 后，$\rho$ 的两个特征值为 $(1\pm\|r\|)/2$，
故正性恰等价于球体不等式；行列式为零恰为秩一。

□

若 $G=vv^\dagger$、$v=(a,b)^{\mathsf T}\ne0$，则关系是
$C=a\overline b$，球面约束来自

$$
|a|^2|b|^2-|a\overline b|^2=0.
$$

这准确表达“二元振幅、关系、归一化组成受约束三维”。
但三个实坐标不是三个独立的纯态自由度：球面只有两个实自由度。
一般二元混合关系才填满球内三维。

<a id="thm:closed"></a>

#### 定理 2.3（固定二元表示的约束在极限中保留）

若 $\rho_j\succeq0$、$\operatorname{Tr}\rho_j=1$ 且 $\rho_j$ 在矩阵范数下收敛到 $\rho$，
则 $\rho\succeq0$、$\operatorname{Tr}\rho=1$。若每个 $\rho_j$ 还为纯态，则极限也为纯态。

**证明。**

对任意 $u$，$u^\dagger\rho u=\lim_j u^\dagger\rho_j u\ge0$，
迹由连续性保持为一。纯态时 $\operatorname{Tr}(\rho_j^2)=1$，
所以 $\operatorname{Tr}(\rho^2)=1$；迹一正矩阵具有此纯度当且仅当秩一。

□

因此，在同一个二元状态空间中，无限次操作不能把收敛极限送出闭球。
一串纯态直接收敛成混合态也不可能；约化、平均或丢弃记录是额外操作。
此外，归一化与极限未必交换：$G_j=2^{-j}I\to0$，
但 $G_j/\operatorname{Tr} G_j=I/2$。零极限没有可继续使用的归一化分母。

## 3　“平方再平方”至少有四种不同含义

### 完整对称幂：更多线性坐标与更高余维

#### 定义 3.1（完整 $m$ 次特征）

对整数 $m\ge1$ 定义

$$
\Phi_m(a,b)
=\left(\sqrt{\binom mj}\,a^{m-j}b^j\right)_{j=0}^{m}
\in\operatorname{Sym}^m(\mathbb{C}^2).
$$

其范数满足

$$
\|\Phi_m(a,b)\|^2=(|a|^2+|b|^2)^m.
$$

<a id="thm:veronese"></a>

#### 定理 3.2（相干幂像的自由度不随阶数增长）

射影映射 $[a:b]\mapsto[\Phi_m(a,b)]$ 的像始终为一个复维、
两个实维；环境 $\mathbb{CP}^{m}$ 的复维为 $m$，故像的复余维为 $m-1$。
令 $u_j=a^{m-j}b^j$，像恰由非零坐标满足

$$
u_i u_{j+1}=u_{i+1}u_j,\qquad 0\le i<j\le m-1
$$

刻画。

**证明。**

在 $a\ne0$ 的图中，$b/a=w$ 给出 $[1:w:\cdots:w^m]$，
而 $w=u_1/u_0$ 可恢复；另一图覆盖 $a=0$ 的端点。
正向关系由单项式相乘直接成立。
反向若 $u_0\ne0$，使用 $i=0$ 的关系归纳得到 $u_j=u_0w^j$。
若 $u_0=0$，相邻关系 $u_{j-1}u_{j+1}=u_j^2$
依次迫使 $u_1,\ldots,u_{m-1}=0$，只剩射影端点 $u_m\ne0$。

□

二次时有三个特征 $a^2,ab,b^2$，并满足 $u_0u_2=u_1^2$。
四次时完整特征为 $a^4,a^3b,a^2b^2,ab^3,b^4$，
而非只保留三个独立复坐标。把平方完整复合为四次幂不会消除其相干关系。
余维 $m-1$ 也不能误读为全局只需 $m-1$ 条多项式方程；上述二次关系通常有冗余。

### 逐坐标幂：相位可以一直振荡

#### 命题 3.3（同一球面上的幂动力学）

设 $a,b\ne0$，
$\delta=\log(|a|/|b|)$、$\theta=\arg b-\arg a$。
对归一振幅 $(a^m,b^m)/\sqrt{|a|^{2m}+|b|^{2m}}$，

$$
r_m=\bigl(\operatorname{sech}(m\delta)\cos(m\theta),
\operatorname{sech}(m\delta)\sin(m\theta),\tanh(m\delta)\bigr).
$$

每一步均有 $\|r_m\|=1$。

**证明。**

代入定理 [2.2](#thm:gram) 的纯态公式，分子分母同除以 $|ab|^m$。
平方和使用 $\operatorname{sech}^2x+\tanh^2x=1$。

□

若两模不等，则幂极限趋向较大分量的极点。
若两模相等，则在赤道上留下 $e^{im\theta}$，普通整数 $m\to\infty$
收敛当且仅当 $e^{i\theta}=1$：
若相位列收敛到 $L$，相邻项的比值极限为 $L/L=1$。
反复平方对应 $m=2^d$；例如 $\theta=2\pi/3$ 时永远两点交替。
轨道不收敛依然不表示几何约束消失。

### 矩阵幂与张量 Gram 幂可以走向相反极限

#### 命题 3.4（归一化矩阵幂）

若 $\rho=(I+R\,n\cdot\sigma)/2$、$0<R<1$、$\|n\|=1$，则

$$
\frac{\rho^m}{\operatorname{Tr}\rho^m}
=\frac{I+R_m n\cdot\sigma}{2},
\quad
R_m=\frac{(1+R)^m-(1-R)^m}{(1+R)^m+(1-R)^m}
=\tanh(m\,\operatorname{artanh}R).
$$

故 $R_m\to1$。$R=0$ 与 $R=1$ 分别保持原态。

**证明。**

$\rho$ 的特征值为 $(1\pm R)/2$，在同一特征基中取幂并归一化。
双曲表达只是上述比值的重写。

□

一般有限维正态的同一操作趋于最大特征空间上的均匀密度：
将谱分解的全部特征值除以最大值后取幂，严格较小者全部趋零。
这里是谱选择，不能解释为归一化约束消失。

#### 命题 3.5（两个向量的张量 Gram 幂）

若 $G$ 是两向量的 Gram 矩阵，则其 $m$ 份张量后的 Gram 为

$$
G_m=\begin{pmatrix}A^m&C^m\\\overline C^{\,m}&B^m\end{pmatrix}.
$$

当 $A,B>0$，令 $\delta=\frac12\log(A/B)$、
$C/\sqrt{AB}=\gamma=q e^{i\alpha}$、$0\le q\le1$。归一化后的三轴满足

$$
r_m=\bigl(q^m\operatorname{sech}(m\delta)\cos(m\alpha),
-q^m\operatorname{sech}(m\delta)\sin(m\alpha),\tanh(m\delta)\bigr),
$$

$$
1-\|r_m\|^2=(1-q^{2m})\operatorname{sech}^2(m\delta)\ge0.
$$

**证明。**

张量内积相乘，给出 $A^m,B^m,C^m$；
再按定理 [2.2](#thm:gram) 归一化并整理。

□

当 $A=B>0$ 且 $q<1$，该关系趋向 $I/2$；

> **编者核读注**：上式在 $q=0$（即 $C=0$）时可任取相位 $α$，所有含相位的横向分量因 $q^m=0$ 而为零；此时不把 $α$ 解释为可由零复数取得的相位。

当 $A\ne B$ 时趋向一极点；等模且 $q=1$ 时仍可能相位振荡。
特别取 $A=B=1,C=1/2$，同一初始态

$$
\rho_1=\frac12\begin{pmatrix}1&1/2\\1/2&1\end{pmatrix}
$$

有两种相反行为：

$$
\frac{G_m}{\operatorname{Tr} G_m}
=\frac12\begin{pmatrix}1&2^{-m}\\2^{-m}&1\end{pmatrix}
\longrightarrow I/2,\qquad
\frac{\rho_1^m}{\operatorname{Tr}\rho_1^m}\longrightarrow\lvert +\rangle\langle +\rvert.
$$

所以“幂次更高”本身不指定约束、纯度或误差的单调方向。

## 4　持续二元提升：精确对象是一张递归图册

### 正质量的二叉球面参数化

#### 定义 4.1（二元归一化节点）

对 $a,b\ge0$、$a+b>0$，置

$$
\vartheta=\frac{a}{a+b},\qquad
\psi=(\sqrt{\vartheta},\sqrt{1-\vartheta})^{\mathsf T},
$$

$$
r(\vartheta)=
\bigl(2\sqrt{\vartheta(1-\vartheta)},\,0,\,2\vartheta-1\bigr).
$$

节点保存父质量 $a+b$、子分割比例 $\vartheta$ 与所属分支。

这里 $\psi$ 是一种指定的平方根表示：节点位于 $y=0,x\ge0$ 的球面半子午线，
实际上只有一个自由参数。该表示尚未证明概率为何在物理上必须来自振幅平方。
若另给相对相位 $\phi$，可将第二振幅乘 $e^{i\phi}$，得到完整球面坐标；
相位不是由两项经典质量自动确定的。

<a id="thm:tree"></a>

#### 定理 4.2（有限正质量的递归三轴重建）

固定一棵有 $k$ 个叶子的有根完整二叉树。
任意严格正概率 $p_1,\ldots,p_k$ 与其 $k-1$ 个内部节点的分割比例
$\vartheta_v\in(0,1)$ 一一对应。每个比例均可换成上述球面点。
叶子概率为路径上分支比例的乘积：

$$
p_i=\prod_{v\in\operatorname{path}(i)}
\begin{cases}
\vartheta_v,&\text{路径走左支},\\
1-\vartheta_v,&\text{路径走右支}.
\end{cases}
$$

另保存根质量 $S$ 即可恢复任意非零正质量向量 $S(p_i)_i$。

**证明。**

由叶子概率自下而上定义各节点质量，令
$\vartheta_v=S_{v0}/(S_{v0}+S_{v1})$，得到唯一比例。
反过来，从根质量一逐层乘分支比例，子质量之和总等于父质量。
树归纳给总叶质量一，并得路径乘积公式。
两种操作逐节点互逆；球面点中 $\vartheta_v=(1+z_v)/2$，没有额外歧义。

□

若允许零质量，则零节点以下的分割没有可观察作用，应按此等价关系合并。
本定理说明任意多元概率都能由同一种二元接口组成；
同时也说明所需的是 $k-1$ 个节点及连接关系，而非一个固定三轴点。

#### 推论 4.3（递归不会自动把平方指数加倍）

若每条边幅值为 $c_e$，节点满足
$|c_{v0}|^2+|c_{v1}|^2=1$，则叶幅值 $A_i=\prod_{e\in i}c_e$ 满足

$$
|A_i|^2=\prod_{e\in i}|c_e|^2,\qquad
\sum_i|A_i|^2=1.
$$

每条非零路径还满足

$$
\log|A_i|^2=2\sum_{e\in i}\log|c_e|.
$$

**证明。**

模平方保持乘法；局部质量守恒逐层合并即给全树守恒，非零路径再取对数。

□

指数二并未变成 $2^d$。对已得到的概率再次平方并归一化是另一种更新。
这一区分在项目新入库的历史 V46 第 6 节已有明确陈述。[[8]](#ref-v46)

### 高维相干信息需要算子值轴

<a id="thm:opaxes"></a>

#### 定理 4.4（精确的算子值二元分解）

将有限维载体在必要时补零嵌入 $\mathbb{C}^2\otimes\mathcal K$。
写 Hermitian 状态块为

$$
M=\begin{pmatrix}A&C\\C^\dagger&B\end{pmatrix}.
$$

定义

$$
S=A+B,\quad Z=A-B,\quad X=C+C^\dagger,\quad Y=i(C-C^\dagger).
$$

则

$$
M=\frac12\bigl(I\otimes S+\sigma_x\otimes X+
\sigma_y\otimes Y+\sigma_z\otimes Z\bigr).
$$

该分解可逆。若 $M\succeq0,\operatorname{Tr} M=1$，则 $\operatorname{Tr} S=1$；
把四个算子替换为其迹，所得恰为第一因子的约化态。

**证明。**

展开右侧，两个对角块为 $(S\pm Z)/2$，
右上块为 $(X-iY)/2=C$，左下为其伴随。
迹式与偏迹公式直接成立。

□

因此，反复二分高维关系可以精确保真，但三轴一般是**算子值**，
或必须由更多节点与交叉相干块补足。仅保留三项标量期望通常丢失信息。
当这些块不对易时，不能把正性擅自改写成普通标量球体不等式。
这一结论没有给出高维物理状态到一个量子比特的普遍无损压缩。

## 5　Fibonacci 与 K-bonacci：约束阶数和记忆阶数

#### 定义 5.1（项目中的 K-bonacci 语言）

固定 $k\ge2$。令 $\mathcal W_n^{(k)}$ 是长度 $n$、
不含连续禁词 $1^k$ 的二进制词，记 $G_n^{(k)}=|\mathcal W_n^{(k)}|$。
则

$$
G_n^{(k)}=2^n\quad(0\le n<k),\qquad
G_n^{(k)}=\sum_{j=1}^k G_{n-j}^{(k)}\quad(n\ge k).
$$

**证明。**

短于 $k$ 的词没有禁词。若 $n\ge k$，合法词必含零；
按最后一个零后接 $r$ 个一分类，$0\le r<k$，
删去末尾 $01^r$ 后得到长度 $n-r-1$ 的任意合法词，
类别互不相交且覆盖全部合法词。

□

当 $k=2$，有 $G_n^{(2)}=F_{n+2}$（$F_0=0,F_1=1$）。
计数相同之外，项目还证明按指定 K-bonacci 位权计算的整数值映射为双射；
本文不需要把计数证明误当成那一更强值映射结论。[[3]](#ref-kboundary) [[5]](#ref-rro)

若状态记录当前末尾连续一的长度 $s=0,\ldots,k-1$，
读零回到 $0$，读一使 $s$ 增一，越过 $k-1$ 后进入吸收拒绝态。
在列输入约定下，活态矩阵为

$$
L_0=e_0\mathbf1^{\mathsf T},\qquad
L_1 e_s=
\begin{cases}e_{s+1},&s<k-1,\\0,&s=k-1.\end{cases}
$$

其和为

$$
M_k=L_0+L_1=
\begin{pmatrix}
1&1&\cdots&1\\
1&0&\cdots&0\\
0&1&\cdots&0\\
\vdots&\ddots&\ddots&\vdots
\end{pmatrix}.
$$

此处活态转移以零消去拒绝路径；完整任务仍应保留拒绝输出。

<a id="thm:hankel"></a>

#### 定理 5.2（完整未来合法性需要随 $k$ 增长的线性记忆）

对每个固定分块宽度 $b\ge1$，完整逐词合法性响应的 Hankel 秩恰为 $k$，
在任意域上都成立。

**证明。**

$k$ 个活尾状态给出线性实现，故秩至多 $k$。
取 $B\ge k$ 且 $B$ 为 $b$ 的倍数，对 $0\le s,j<k$ 令

$$
u_s=0^{B-s}1^s,\qquad v_j=1^j0^{B-j}.
$$

它们均由完整块组成，拼接合法当且仅当 $s+j<k$。
对应 $k\times k$ 响应矩阵
$H_{s,j}=\mathbf1_{s+j<k}$ 反转列次序后为单位三角矩阵，
行列式为 $\pm1$，在任意域中皆非零。故秩至少 $k$。

□

这是项目命题 4.4 的自足重证。[[3]](#ref-kboundary)
它约束的是指定任务的**线性实现维数**；
不排除将有限状态编码成一个实数的集合论操作，
但该编码不再自动保存同一种线性更新、连续稳定性及读出合同。
因此，单个窗口算子秩一或单个二元接口有三轴，
不能替代整个 K-bonacci 未来任务所需的记忆。

## 6　归一化递推：任意初值的稳定误差定理

本节的总变差收缩、扰动预算、尺度误差，以及下一节的精确分布距离与联合界，
是本轮从已给计数矩阵作出的纸面推导。它们没有被标作仓库已有定理，
也不主张这些数学不等式的全球原创性。

#### 定义 6.1（历史形状与尺度）

取非零非负历史向量 $x_t\in\mathbb{R}_{\ge0}^k$，
$x_{t+1}=M_kx_t$，总尺度 $S_t=\mathbf1^{\mathsf T}x_t>0$，
归一形状 $p_t=x_t/S_t\in\Delta_{k-1}$。
这里坐标为当前值及前 $k-1$ 个历史值。

<a id="prop:normalize"></a>

#### 命题 6.2（归一更新与尺度更新精确分离）

对 $p=(p_1,\ldots,p_k)$，

$$
\boxed{F_k(p)=\frac{(1,p_1,\ldots,p_{k-1})}{2-p_k},}
\qquad
\boxed{S_{t+1}=S_t(2-p_{t,k}).}
$$

**证明。**

$M_kp=(\sum_jp_j,p_1,\ldots,p_{k-1})=(1,p_1,\ldots,p_{k-1})$；
各项之和为 $2-p_k$。乘回总尺度即得第二式。

□

两项公式共同保留原递推。只要初始尺度未丢弃，归一化不是删除总量。
例如 $k\ge4$ 时，只保留前两个历史坐标和总和仍不足以闭合：
保持它们不变，把第三坐标增加 $\varepsilon$、最后坐标减少 $\varepsilon$，
下一步的总尺度 $2S-x_k$ 就改变。
$k=3$ 时前两坐标加总和已能恢复第三坐标，不能用同一反例。

#### 定义 6.3（总变差）

对概率向量 $p,q$，

$$
\operatorname{TV}(p,q)=\frac12\sum_j|p_j-q_j|
=\sum_j(q_j-p_j)_+
=\sup_A|p(A)-q(A)|.
$$

<a id="thm:tv"></a>

#### 定理 6.4（全单纯形的归一化误差界）

对任意 $p,q\in\Delta_{k-1}$，包括边界，

$$
\boxed{
\operatorname{TV}(F_k(p),F_k(q))
\le\frac{\operatorname{TV}(p,q)}{2-\min(p_k,q_k)}.}
$$

**证明。**

先设 $p_k\ge q_k$，记 $a=2-p_k\le b=2-q_k$。
输出第一坐标有 $1/a\ge1/b$，不贡献 $F_k(q)-F_k(p)$ 的正部。
其余坐标满足

$$
\left(\frac{q_j}{b}-\frac{p_j}{a}\right)_+
\le\frac{(q_j-p_j)_+}{b}.
$$

又因输入最后坐标 $q_k-p_k\le0$，
对 $j<k$ 求和恰给全部输入总变差。
故输出至多为 $\operatorname{TV}(p,q)/b$。另一大小关系交换 $p,q$。
分母始终在 $[1,2]$，没有遗漏零坐标或边界。

□

<a id="thm:lambda"></a>

#### 定理 6.5（唯一正增长根与归一定态）

存在唯一 $\lambda_k\in(1,2)$ 使

$$
\sum_{j=1}^k\lambda_k^{-j}=1.
$$

令 $p^{*(k)}_j=\lambda_k^{-j}$，则
$M_kp^{*(k)}=\lambda_kp^{*(k)}$，
$F_k(p^{*(k)})=p^{*(k)}$，且

$$
2-p_k^{*(k)}=\lambda_k.
$$

**证明。**

倒数幂和在 $(1,\infty)$ 严格递减，
在 $1$ 处为 $k>1$，在 $2$ 处为 $1-2^{-k}<1$。
第一坐标的特征方程为 $\sum_j\lambda_k^{-j}=1=\lambda_k p_1^*$，
其余为 $p_{j-1}^*=\lambda_kp_j^*$。
对特征方程求坐标总和并用命题 [6.2](#prop:normalize) 即得最后式。

□

<a id="cor:global"></a>

#### 推论 6.6（任意初值的指数稳定）

对任意 $p_0\in\Delta_{k-1}$ 和整数 $t\ge0$，

$$
\boxed{
\operatorname{TV}(F_k^t(p_0),p^{*(k)})
\le\lambda_k^{-t}\operatorname{TV}(p_0,p^{*(k)}).}
$$

定态在整个闭单纯形中唯一，并且

$$
\left|\frac{S_{t+1}}{S_t}-\lambda_k\right|
\le\lambda_k^{-t}\operatorname{TV}(p_0,p^{*(k)}).
$$

**证明。**

在定理 [6.4](#thm:tv) 中令 $q=p^*$。
因 $\min(p_k,p_k^*)\le p_k^*$，分母至少为 $2-p_k^*=\lambda_k>1$；
迭代给出第一式。若另有定态，令 $t\to\infty$ 就与 $p^*$ 相等。
第二式使用 $S_{t+1}/S_t=2-p_{t,k}$，
以及单个事件概率差不超过总变差。

□

这给出“控制误差使结果稳定”的一条具体定理。
稳定发生在明确的**归一历史形状**与明确误差度量中，
无需把所有演化都预先叫作误差收缩。

<a id="cor:noise"></a>

#### 推论 6.7（有扰动的稳定预算）

设实际归一轨道 $q_t\in\Delta_{k-1}$ 满足
$\operatorname{TV}(q_{t+1},F_k(q_t))\le\varepsilon_t$，则

$$
\operatorname{TV}(q_t,p^*)\le
\lambda_k^{-t}\operatorname{TV}(q_0,p^*)+
\sum_{j=0}^{t-1}\lambda_k^{-(t-1-j)}\varepsilon_j.
$$

若 $\varepsilon_j\le\varepsilon$，则

$$
\limsup_{t\to\infty}\operatorname{TV}(q_t,p^*)
\le\frac{\varepsilon}{1-\lambda_k^{-1}}
\le\varphi^2\varepsilon.
$$

若 $\varepsilon_t\to0$，则 $q_t\to p^*$。

**证明。**

三角不等式与对定态的收缩给
$e_{t+1}\le\varepsilon_t+\lambda_k^{-1}e_t$；
归纳展开即得卷积。常数误差使用几何级数，
再用 $\lambda_k\ge\varphi$ 与 $(1-\varphi^{-1})^{-1}=\varphi^2$。
误差趋零时，有限个早期误差的贡献衰减，
其余项由任意小的统一尾界乘收敛几何级数控制。

□

这份噪声结论以实际更新仍留在概率单纯形中为前提；
它对总误差给界，不假设每一步误差必须单调下降。

<a id="prop:scale"></a>

#### 命题 6.8（总尺度也可精确跟踪）

令

$$
\ell_j=\sum_{r=1}^{k-j+1}\lambda_k^{-r},
\qquad
C_0=\frac{\ell^{\mathsf T}x_0}{\ell^{\mathsf T}p^{*(k)}}>0.
$$

则

$$
\frac{S_t}{\lambda_k^t}
=\frac{\ell^{\mathsf T}x_0}{\ell^{\mathsf T}p_t},
\qquad
\left|\frac{S_t}{C_0\lambda_k^t}-1\right|
\le(\lambda_k-1)\lambda_k^{-t}\operatorname{TV}(p_0,p^{*(k)}).
$$

**证明。**

直接代入矩阵列可验 $\ell^{\mathsf T}M_k=\lambda_k\ell^{\mathsf T}$，
且 $\ell_1=1,\ell_k=\lambda_k^{-1}$。
所以 $\ell^{\mathsf T}x_t=\lambda_k^t\ell^{\mathsf T}x_0$，
代入 $x_t=S_tp_t$ 得第一式。
对任意实函数 $f$，概率期望差至多为
$(\max f-\min f)\operatorname{TV}$：从 $f$ 减去最小值后，分别按正负部估计即可。
应用于 $\ell$ 并使用 $\ell^{\mathsf T}p_t\ge1/\lambda_k$，得到

$$
\left|\frac{\ell^{\mathsf T}p^*}{\ell^{\mathsf T}p_t}-1\right|
\le(\lambda_k-1)\operatorname{TV}(p_t,p^*).
$$

再用推论 [6.6](#cor:global)。

□

## 7　从黄金比例到无限二分：精确联合极限

<a id="thm:rootlimit"></a>

#### 定理 7.1（增长根单调趋于二）

有

$$
\lambda_2=\varphi,\qquad
\lambda_{k+1}>\lambda_k,\qquad
2-\lambda_k=\lambda_k^{-k}\le\varphi^{-k},
$$

从而 $\lambda_k\uparrow2$。

**证明。**

$k=2$ 时根方程为 $\lambda^2=\lambda+1$，给黄金比例。
在 $\lambda_k$ 处增加一个正的倒数幂，使 $k+1$ 项和大于一；
因其严格递减，下一根必须更大。
有限等比和给
$\lambda_k-1=1-\lambda_k^{-k}$，即缺口恒等式。
再用 $\lambda_k\ge\varphi>1$。

□

根极限与固定窗口二进制极限在项目 RRO 第 1.2.13 节已经给出；
这里保留其严格量词并重证。[[5]](#ref-rro)
Fibonacci 在归一历史中对应
$p^{*(2)}=(\varphi^{-1},\varphi^{-2})$，
满足黄金分割的两项和一；这是一份经典正权重，
可用其平方根作为二元振幅表示，但不由此自动获得物理相干相位。

<a id="thm:geometric"></a>

#### 定理 7.2（定态分布的精确总变差）

把 $p^{*(k)}$ 在 $j>k$ 处补零，并令 $g_j=2^{-j}$（$j\ge1$）。
则

$$
\boxed{\operatorname{TV}(p^{*(k)},g)=2^{-k}.}
$$

进一步，对每个阶数任取初值 $p_0^{(k)}$，

$$
\boxed{
\operatorname{TV}\!\left(\widetilde{F_k^t(p_0^{(k)})},g\right)
\le\varphi^{-t}+2^{-k}.}
$$

因此沿任意同时满足 $t\to\infty,k\to\infty$ 的路径都收敛到同一几何分布。

**证明。**

因为 $\lambda_k<2$，在 $j\le k$ 上 $p_j^*>2^{-j}$。
前 $k$ 项的总超额为
$1-\sum_{j=1}^k2^{-j}=2^{-k}$；
后续缺失尾质量也为 $2^{-k}$。
两项绝对差之和为 $2^{1-k}$，取一半即得精确值。
三角不等式、推论 [6.6](#cor:global)、
$\lambda_k\ge\varphi$ 以及概率间总变差至多一给联合界。

□

#### 说明 7.3（量词）

联合界允许每个 $k$ 有不同初值，但同一条 $F_k^t$ 轨道在这 $t$ 步内阶数固定。
若每一步都改变阶数，需另定嵌入及更新规则，不能直接套用本式。
这里收敛的是归一历史分布；它不是下一节的合法词比例，也不是完整量子历史律。

<a id="prop:tail"></a>

#### 命题 7.4（几何定态的连续二元提取）

对整数 $0\le d\le k$ 定义

$$
R_{k,d}=\sum_{j=d+1}^k\lambda_k^{-j}
=\frac{\lambda_k^{-d}-\lambda_k^{-k}}{\lambda_k-1}.
$$

当 $0\le d<k$ 时，从余量中提取下一项的条件比例为

$$
\vartheta_{k,d}
=\frac{\lambda_k^{-(d+1)}}{R_{k,d}}
=\frac{1-\lambda_k^{-1}}{1-\lambda_k^{-(k-d)}}.
$$

对每个固定 $d$，$k\to\infty$ 时
$R_{k,d}\to2^{-d}$、$\vartheta_{k,d}\to1/2$。
并且对 $0\le d\le k$，

$$
0\le 2^{-d}-R_{k,d}\le2^{-k}.
$$

**证明。**

前两式由等比和。固定 $d$ 时使用 $\lambda_k\to2$。
最后一式改写为

$$
2^{-d}-R_{k,d}
=\sum_{j=1}^{d}(\lambda_k^{-j}-2^{-j}),
$$

各项非负，部分和不超过 $d=k$ 时的总超额 $2^{-k}$。

□

所以无限极限可以由每层相同的二元比例
$\vartheta=1/2$ 生成，局部球面点均为 $(1,0,0)$；
第 $j$ 个叶子的质量却仍为 $2^{-j}$，区别保存在深度及连接中。
有限树最后一步 $\vartheta_{k,k-1}=1$ 是终止叶，
不是又一个非平凡二分。靠近终端，比例趋于 $1/2$ 也不一致：
固定 $r\ge1$、$d=k-r$ 时，分母极限为 $1-2^{-r}$。
绝对尾误差小不等于每个末端相对误差都小。

动态状态也有同样的观察深度边界。记
$R_{t,k,d}=\sum_{j>d}\widetilde p_{t,j}$，则总变差控制尾事件给

$$
|R_{t,k,d}-2^{-d}|\le\varphi^{-t}+2^{-k},
\qquad
\frac{|R_{t,k,d}-2^{-d}|}{2^{-d}}
\le2^d\varphi^{-t}+2^{d-k}.
$$

因此一个充分的相对精度条件为
$2^d\varphi^{-t}\to0$ 且 $k-d\to\infty$。
不能仅凭整体总变差小，就断言任意极深节点的条件概率也准确；
零质量子树还须停止分割。

## 8　约束何时真的消失：观察窗口决定答案

<a id="thm:finitewindow"></a>

#### 定理 8.1（有限窗口中的精确解禁）

对每个固定词长 $n$，

$$
k>n\quad\Longrightarrow\quad
\mathcal W_n^{(k)}=\{0,1\}^n,\quad G_n^{(k)}=2^n.
$$

但任意固定有限 $k$ 的足够长窗口仍存在非法词。

**证明。**

长度小于 $k$ 的词不能容纳禁词 $1^k$；
而长度至少 $k$ 时，全一前缀已经违反该约束。

□

这是用户“阶数增加，约束减少”最直接且精确的成立版本。
它已经由项目 RRO 的式 TM.415 给出。[[5]](#ref-rro)
其中 $k>n$ 不能换成 $k\ge n$：在 $k=n$ 时全一词仍被排除。

<a id="thm:double"></a>

#### 定理 8.2（观察深度与阶数的两个极限不交换）

对 iid 公平位的长度 $n$ 词定义
$P_{n,k}=G_n^{(k)}/2^n$。则

$$
P_{n,k}\ge1-(n-k+1)_+2^{-k},
\qquad
P_{n,k}\le(1-2^{-k})^{\lfloor n/k\rfloor},
$$

并有

$$
\lim_{n\to\infty}\lim_{k\to\infty}P_{n,k}=1,
\qquad
\lim_{k\to\infty}\lim_{n\to\infty}P_{n,k}=0.
$$

**证明。**

非法至少意味着某个长 $k$ 的窗口全一，窗口数至多 $(n-k+1)_+$，
每个事件的公平概率为 $2^{-k}$；并界给下界。
取 $\lfloor n/k\rfloor$ 个互不相交长块，合法要求每块均非全一，
独立性给上界。固定 $n$ 增大 $k$ 时第一极限为一；
固定 $k$ 增大 $n$ 时上界趋零。

□

当窗口也增长，关键标度是 $n2^{-k}$，并非单看 $k$ 大小。
项目 K-bonacci 第 10 节已有精确的公平位长串估计；
附录给不依赖数值计算的自足临界极限证明。[[3]](#ref-kboundary)

$$
\begin{array}{c|c}
n2^{-k}\text{ 的极限} & P_{n,k}\text{ 的极限}\\
\hline
0&1\\
\tau\in(0,\infty)&e^{-\tau/2}\\
\infty&0
\end{array}
$$

这些式子中的 $2^n$ 来自二字母表计数；它与振幅平方的指数二属于不同数学位置。
临界区还可有整数格点造成的子列相位，不能忽略后直接宣称单一极限。

#### 命题 8.3（无限语言之并仍不是全空间）

令 $\mathcal K_k$ 为全部不含 $1^k$ 的无限二进制词。
则 $\bigcup_{k\ge2}\mathcal K_k$ 在全部二进制词的前缀拓扑中稠密，
但不是全空间。

**证明。**

任意有限前缀后接全零，就得到具有有界一游程的词，属于某一有限层；
因此每个柱邻域都与该并相交。
词 $10\,110\,1110\cdots$ 具有任意长的一游程，不属于任何有限层。

□

### 相同语言扩张也不唯一决定概率极限

按回返块 $B_j=1^{j-1}0$（$1\le j\le k$）分解，
项目 Perron 根律给独立回返块权
$p_j=\lambda_k^{-j}$。
它与本文归一历史定态具有相同数值公式，但前者是回返随机模型，
后者是确定递推的项目化形状，应分别说明其来源。
该回返根律不是一般位置开始的平稳 Parry 律。[[5]](#ref-rro)

#### 命题 8.4（两种归一化的不同极限）

从回返边界开始独立拼接块：
若对 $k$ 个块赋均匀概率 $1/k$，原始位律弱收敛到全一序列的点质量；
若赋 Perron 权 $\lambda_k^{-j}$，固定有限原始词的概率趋于公平二进制概率。

**证明。**

均匀块时，对固定 $n<k$，
$\Pr([1^n])=(k-n)/k\to1$。
因此每个固定前缀都趋向全一。
Perron 权时，固定长度 $n$ 的词 $w$，对充分大的 $k>n$ 它必合法；
将其写成完整块及最后 $s$ 个一；
各完整块的概率相乘，再乘未完块的尾概率，得

$$
\Pr([w])=\lambda_k^{-n}h_s,\qquad
h_s=\sum_{\ell=1}^{k-s}\lambda_k^{-\ell}.
$$

固定 $w$ 后，$\lambda_k\to2,h_s\to1$，
所以极限为 $2^{-n}$。有限柱决定这里的弱收敛。

□

无限完整回返块只能覆盖有无限多个零的词。
均匀块的极限点 $1^\infty$ 恰离开该解析域；
公平位律则给这个缺失集合零质量。两个结果说明，
“可归一化”和“约束放宽”还不足以选择唯一概率模型。

## 9　另一种准确的约束减弱：三轴集体读出的经典极限

#### 定义 9.1（对称复合的平均自旋）

令 $\mathcal H_m=\operatorname{Sym}^m(\mathbb{C}^2)$，维数 $D=m+1$；
在该空间定义

$$
X_i=\frac1m\sum_{a=1}^{m}\sigma_i^{(a)},\qquad
r_i=\operatorname{Tr}(\rho X_i).
$$

这里 $X_i$ 是平均算子，整体态 $\rho$ 的支持限于完全对称子空间。

<a id="thm:spin"></a>

#### 定理 9.2（交换子与最小总方差的精确缩放）

有

$$
[X_i,X_j]=\frac{2i}{m}\varepsilon_{ijk}X_k,
\qquad
\sum_{i=1}^3 X_i^2=\left(1+\frac2m\right)I.
$$

因此

$$
\boxed{
\sum_{i=1}^{3}\operatorname{Var}_\rho(X_i)
=1+\frac2m-\|r\|^2\ge\frac2m.}
$$

相干积态 $\lvert \psi\rangle^{\otimes m}$ 达到等号；
并且 $\|[X_i,X_j]\|\le2/m\to0$。

**证明。**

不同槽位的算子交换，同槽位的 Pauli 关系给

$$
[X_i,X_j]
=m^{-2}\sum_a[\sigma_i^{(a)},\sigma_j^{(a)}]
=\frac{2i}{m}\varepsilon_{ijk}X_k.
$$

若 $a\ne b$ 且 $F_{ab}$ 交换槽位 $a,b$，则
$\sum_i\sigma_i^{(a)}\sigma_i^{(b)}=2F_{ab}-I$。
在完全对称子空间上，$F_{ab}=I$，所以

$$
\sum_iX_i^2
=\frac{3m+m(m-1)}{m^2}I
=\left(1+\frac2m\right)I.
$$

三轴 $r$ 是任一单份约化态的 Bloch 向量，故 $\|r\|\le1$；
相干积态的约化态纯，故 $\|r\|=1$。
最后 $\|X_i\|\le1$，得到交换子范数界。

□

这里确实有随着阶数增长而减弱的约束：
归一化后的非交换程度和可达到的最小量子噪声趋零。
但 $\|r\|\le1$ 始终保持；一般态的方差也不必趋零，
例如每阶都取 $r=0$ 时总方差趋一。
该 Casimir 等式依赖对称子空间支持，不能仅由整个张量积密度矩阵置换不变推出。

高自旋的经典极限属于既有数学物理主题，Lieb 的原研究处理了量子自旋系统的
自由能与热力学极限。本文只证明上述有限维算子恒等式及其缩放后果，
不将它们扩充成该热力学定理。[[11]](#ref-lieb)

<a id="thm:fiber"></a>

#### 定理 9.3（三轴读出内部的隐藏关系维数）

映射

$$
\Gamma_m:\mathcal D(\mathcal H_m)\longrightarrow\mathcal D(\mathbb{C}^2),
\qquad \Gamma_m(\rho)=\frac{I+r\cdot\sigma}{2}
$$

为仿射满射。每个 $\|r\|<1$ 的纤维实维数恰为

$$
\boxed{D^2-4=m^2+2m-3.}
$$

每个 $\|r\|=1$ 的纤维恰有一个态，即对应的相干积态。

**证明。**

球面纯态均由相干积态达到，其凸包是整个球体，故满射。
Hermitian 矩阵实维数为 $D^2$；固定迹和三个读出给四个独立实线性条件。
独立性可由相干态验证：
若 $cI+a\cdot X=0$，在所有方向的相干态取期望得到
$c+a\cdot n=0$ 对全部单位 $n$ 成立，故全部系数为零。
对称空间的最大混合态 $I_D/D$ 在共同旋转下不变，故三个读出均为零。
对任意内部向量 $r=s n$、$0\le s<1$，状态

$$
\rho=(1-s)I_D/D+s(\lvert n\rangle\langle n\rvert)^{\otimes m}
$$

严格正且读出为 $r$；所以正性未降低该仿射纤维的局部维数。
边界情形下，令 $P$ 为纯的单份约化投影。
正性与 $\operatorname{Tr}(((I-P)\otimes I)\rho)=0$ 迫使态支持在第一槽位的 $P$ 上。
对称性对每槽位给同样结论，整体支持只能在一维的 $P^{\otimes m}$。

□

最小反例已在 $m=2$ 出现：

$$
\lvert \Psi^+\rangle=\frac{\lvert 01\rangle+\lvert 10\rangle}{\sqrt2},
\qquad
\lvert \Phi^+\rangle=\frac{\lvert 00\rangle+\lvert 11\rangle}{\sqrt2}.
$$

两态均在对称子空间，且三轴均为零，但彼此正交。
它们的 $\langle X_z^2\rangle$ 分别为 $0$ 与 $1$。
因此三轴读出相同不代表完整关系相同；
所谓高阶“更自由”可精确表现为观察纤维扩大，而不是正性消失。
边界纤维反而唯一，这给出一个可证明的边界与体差别。

## 10　与项目原生关系、酉性及最新增量的连接

### 原生五模式与量子三轴的具体桥

项目 V42 先明确逻辑标签 $(N,1,2,3,13)$ 与数量标签
$(0,2,3,5,25)$ 的对应。原占位读口为

$$
\xi=e_1+e_{13},\qquad
\eta=e_3+e_{13},\qquad
\zeta=e_2,\qquad e_{13}=\xi\eta.
$$

令 $X=\omega(\xi),Y=\omega(\eta),Z=\omega(\zeta)$、
$\kappa=\omega(\xi\eta)$，则完整五态律按逻辑标签次序为

$$
p=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa).
$$

正性给
$\max(0,X+Y+Z-1)\le\kappa\le\min(X,Y)$。
因此一般的归一化五态律仍有四个自由度；
原三轴金字塔是它在 $(X,Y,Z)$ 上的投影。
在该纤维上另供一个关系律，才可能获得完整的三维模型。[[9]](#ref-v42) [[10]](#ref-foundation)

这里
$e_N=I-\xi-\eta-\zeta+\xi\eta$ 是特定事件，
归一化则为 $\omega(I)=1$。所以 $F[\mathrm{null}]$
并不是归一化本身；若要让它承担参考或观察者角色，须另外给出标定。

项目确实已有具体操作桥。Foundational 第 14 节选择有序来源代表后给出

$$
F[1]\mapsto-i\sigma_x,\qquad
F[3]\mapsto+i\sigma_z,\qquad
F[2]\mapsto-i\sigma_y.
$$

这是所选来源树的操作表示，不是 $(X,Y,Z)$ 与某个态的 Bloch 向量相等。
联合模式的相位依赖代表次序；空选择的单位贡献也不等于原生 null 动作。[[10]](#ref-foundation)

另一方面，V42 第 7 节明确另供非平行 qubit 反射
$A=a\cdot\sigma,B=b\cdot\sigma$，令
$c=a\cdot b,\ s=\sqrt{1-c^2}>0,\ N=(a\times b)\cdot\sigma/s$。
按语义标签取
$x_1=\omega(A),x_3=\omega(B),x_2=\omega(N)$，
实际正交坐标及正性域为

$$
r_{\mathrm B}=\left(x_1,\frac{x_3-cx_1}{s},x_2\right),
\qquad
\frac{x_1^2-2cx_1x_3+x_3^2}{1-c^2}+x_2^2\le1.
$$

证明只须在正交框架
$(A,(B-cA)/s,N)$ 中应用定理 [2.2](#thm:gram)。
仅当 $c=0$ 时，不换尺的三轴平方和才直接适用。
原中位占据 $\zeta$ 与量子法向 $N$ 是不同读口，
其跨接口同一性还需指定编码；原生对易事件
$2\xi-I,2\eta-I$ 并未自动供应这份非退化量子接口。[[9]](#ref-v42)

还有一种精确且不同的 Gram 闭包：Foundational 第 42 节把纯占位
$(x,y,z)$ 送到 $(x,y,z+xy)$，联合项补上三点相关的传递缺边。
对同一原律混合后，

$$
C(p)=\begin{pmatrix}
1&X&Y\\X&1&Z+\kappa\\Y&Z+\kappa&1
\end{pmatrix}\succeq0.
$$

按从一开始的行列编号，仍须保留原 $Z$，才能用 $C(p)_{23}-Z$ 恢复 $\kappa$。
三条 Gram 边单独没有恢复完整四维概率律。
这提供了实际的“关系补足几何”实例，同时保留信息维数。[[10]](#ref-foundation)

### 关系矩阵类型必须保留

K-bonacci 端点文稿对宽度 $k+1$ 的合法零含窗口给
$E_{p,t}=e_t r_p^{\mathsf T}$，其中
$r_p(s)=\mathbf1_{s+p<k}$。
单窗口端点满足 $0\le p,t<k,p+t\le k$；
对应任意矩阵的迹读出核维数为

$$
\frac{(k-1)(k-2)}2.
$$

严格逐元正的秩一实矩阵 $c\ell^{\mathsf T}$ 可由该读出族唯一识别，
而因子保留 $(c,\ell)\sim(ac,a^{-1}\ell)$ 的尺度规范。[[4]](#ref-kendpoint)

这些矩阵一般不对称，**逐元正不等于 Hermitian 正半定**。
所以不能未经映射就把 $c\ell^{\mathsf T}$ 放入定理 [2.2](#thm:gram) 的密度球。
原文也保留 K-bonacci 到 FIB 的载体、允许操作、实际读数和目标等价桥；
本报告的二叉归一化是明确的数学表示，不把这座物理与任务桥视为自动完成。

FIB 关系综合又给出另一个直接提醒：固定 Fibonacci 矩阵满足
$M^2=M+I$，因此全部 $\operatorname{Tr}(M^nR)$ 都由前两项读数决定。
增加次数可能完全没有增加独立关系信息。
来源允许加入标签交换 $J$ 后，四个累计操作
$I,M,JM,MJM$ 才给一般二阶关系矩阵的完整重建。[[6]](#ref-fibsynth)
该文常用的 $M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$
与本文 $M_2=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ 置换相似；
不能混用字面坐标公式。

### 归一化稳定并不等于整体酉性

#### 命题 10.1（K-bonacci 计数矩阵不是酉门）

$M_k$ 不可能在任何正定内积下为酉算子。

**证明。**

由定理 [6.5](#thm:lambda)，$M_kp^*=\lambda_kp^*$ 且 $\lambda_k>1$。
任何正定范数下都有
$\|M_kp^*\|=\lambda_k\|p^*\|>\|p^*\|$，与酉等距矛盾。

□

归一化的 $F_k$ 本身也不是通常意义的线性量子门。
它是保留尺度后的项目化递推，定理 [6.4](#thm:tv) 测量的是概率形状的距离。
对完整量子态的共同酉演化，内积与迹距离保持，
不具有这种自动收缩。若要把递推作为一个整体酉装置的内部读出，
必须给出承载尺度、历史、分支及剩余信息的内部记录，以及实际输入输出映射。
这与唯一本体图景相容：记录可全部位于整体内部；
相容不等于已经构造了来源特定的量子门实现。

### 本轮真正新加的来源结果

量子续卷 III 新增 §§183–189，直接相关的是两种资源关系。[[7]](#ref-iii)
第一，在原完整路径模型下，另选原 FIB 完成源 $(K,\delta)$，
以一个 $\delta$ 不变概率作为初态，使用同一固定解码器，
每十个原调用推进固定有限 $r$ 次 $\delta$，要求精确生成全部有限联合历史。
同一初始来源供应各段，段间不重新抽样。
对任意整数分位精度 $q\ge1$，必要条件为

$$
r\log\varphi\ge3[h_{\rm bin}(a)+2a\log q],
\quad h_{\rm bin}(a)=-a\log a-(1-a)\log(1-a).
$$

其中 $a=4\varphi^{-3}\in(0,1)$ 是原地址一块的固定常数。
令精度无界便排除该固定有限速率模型。
该结果消费既有 FIB 完成源的熵率桥；
本文没有重新独立证明该大篇上游来源。
它不排除变速、非平稳、近似、有限总时长或其他来源类。

第二，对同一个原四调用程序，按原定义将反跳率截为 $\min(\gamma,L)$，
并令 $L$ 高于原前跳率上界。当 $L\to\infty$ 时，
完整路径总变差具有 $\Theta(L^{-2})$ 误差阶，并有严格节点与终端残差。
这是指定近似结构的倒平方误差，不是新的 Born 指数选择或三轴维数证明。
这两项新增都强调：一个内部来源拥有丰富静态信息，
仍须满足实际推进率、读出与保留联合关系的条件。

## 11　统一结论：局部三轴、全局连接和有条件的极限

综合本文，可以给 AURIC 的递归用法一个精确定义：
#### 定义 11.1（递归二元关系图册）

一张递归二元关系图册由以下资料构成：
节点的二元归一化关系；节点之间的连接和有序分支；
必要的根尺度或各层尺度运输；相位参考、记录及跨节点相干关系；
以及所声明任务下的更新与解码。
纯经典质量情形可用定理 [4.2](#thm:tree) 的标量节点；
一般高维相干情形使用定理 [4.4](#thm:opaxes) 的算子值关系或等价完整资料。

#### 定理 11.2（本文范围内的递归闭合）

在正质量树上，保留根尺度及全部非平凡二元节点即可精确恢复原数据；
在固定 $k$ 的 K-bonacci 历史上，归一更新与尺度更新联合精确保持原递推，
且形状误差满足推论 [6.6](#cor:global)。
增加阶数后，只要同时增加所需节点和连接，
便得到定理 [7.2](#thm:geometric) 的无限几何极限。

> **编者核读注**：这里沿用定理 [7.2](#thm:geometric) 的联合极限条件：同一轨道内固定 $k$，并令 $t→∞$ 与 $k→∞$ 同时成立；仅增加节点或阶数不单独保证任意初值轨道已达到该分布极限。

这些结论均不要求局部 Bloch 球解除其正性约束。

**证明。**

分别组合定理 [4.2](#thm:tree)、命题 [6.2](#prop:normalize)、
推论 [6.6](#cor:global) 与定理 [7.2](#thm:geometric)。
局部球面或球体约束由定理 [2.2](#thm:gram) 持续保持。

□

由此，用户的直觉可以分成三条成立但不同的路线：

1. 固定有限观察窗口内，$k$ 超过窗口长度后，禁词约束精确消失；
2. 归一化集体自旋中，非交换程度与最小相干噪声按 $1/m$ 减弱；
3. 仅保留高维状态的三轴读出时，更多关系进入观察纤维。

它们都容许持续使用同一种二元归一化接口。
但无限阶不是“没有任何约束的三维空间”：
它可能是一棵无限深的相容关系树、一族有限预算观察、
或带有闭正性几何的经典极限。
哪一种描述适用，由保留的数据、实际操作和极限量词决定。

## A　公平位临界标度的自足纸面证明

本附录重证项目 K-bonacci 第 10 节已有的极限，
不将其作为新发现的 Poisson 定律。
采用 iid 公平原始位；合法词条件律本身并不具有同样独立性。

#### 定理 A.1（三种增长区间）

当 $n\to\infty$、$k=k(n)\ge2$ 时，

$$
n2^{-k}\to0\Rightarrow P_{n,k}\to1,\qquad
n2^{-k}\to\tau\in(0,\infty)\Rightarrow P_{n,k}\to e^{-\tau/2},
$$

$$
n2^{-k}\to\infty\Rightarrow P_{n,k}\to0.
$$

**证明。**

稀疏情形直接用定理 [8.2](#thm:double) 的并界。
其余考虑词内模式 $01^k$ 的出现次数 $X$。
可能起点有 $(n-k)_+$ 个，均值
$\mu=(n-k)_+2^{-(k+1)}$。
两起点距离至多 $k$ 时模式互斥；
距离大于 $k$ 时使用不相交位集合而独立。
所以
$\mathbb E X^2\le\mu+\mu^2$。
$\mu=0$ 时 $P_{n,k}\le1/(1+\mu)=1$ 平凡成立。
对 $\mu>0$，Cauchy--Schwarz 给
$\Pr(X>0)\ge(\mathbb EX)^2/\mathbb EX^2\ge\mu/(1+\mu)$。
合法事件包含于 $X=0$，故 $P_{n,k}\le1/(1+\mu)$。
稠密条件 $n2^{-k}\to\infty$ 蕴含 $k/n\to0$：
最终 $2^k<n$，故 $k<\log_2n$。
于是 $\mu\to\infty$，得到稠密极限。

临界条件迫使 $k\to\infty$、$k/n\to0$。
固定整数 $r\ge0$，互相距离至少 $k+1$ 的 $r$ 个起点集合数为
$\binom{n-kr}{r}$；不足容纳时按零处理。
每个这样的模式集合概率为 $2^{-(k+1)r}$，因此

$$
\mathbb E\binom Xr
=\binom{n-kr}{r}\,2^{-(k+1)r}
\longrightarrow\frac{(\tau/2)^r}{r!}.
$$

对任意固定截断阶，有限容斥的 Bonferroni 上下界把
$\Pr(X=0)$ 夹在上述阶乘矩的交替部分和之间。
先令 $n\to\infty$，再令截断阶趋于无穷，得到
$\Pr(X=0)\to e^{-\tau/2}$。
禁词 $1^k$ 出现而 $01^k$ 从未出现，只可能由开头长度至少 $k$ 的一游程造成，
其概率至多 $2^{-k}\to0$。
故 $P_{n,k}$ 与 $\Pr(X=0)$ 的差趋零，临界结论成立。

□

该证明同时说明系数 $1/2$ 的来源：
去除同一长串一中的重叠计数后，一次内部新游程由一个零和后续 $k$ 个一开始，
公平概率为 $2^{-(k+1)}$。这不是振幅平方指数的另一份推导。

## 固定来源、归属与阅读范围

<a id="ref-head"></a>

**[1]**
[固定项目提交 a6ed97ef0969](https://github.com/the-omega-institute/trureturing/commit/a6ed97ef09691efed393942b6ae694c4a44e5fc9)。
2026-10-31 20:48:35，新加坡。只取得一次活动 HEAD 后固定取源。

<a id="ref-compare"></a>

**[2]**
[v49 至 v50 的固定比较](https://github.com/the-omega-institute/trureturing/compare/e168d4bbef773d94df790275d1f4f2a9e373103f...a6ed97ef09691efed393942b6ae694c4a44e5fc9)。
完整 theory 树 1109 项；四个理论路径变化。只对文中列明来源承担内容核读。

<a id="ref-kboundary"></a>

**[3]**
[K-bonacci Self-calibrating Boundaries](https://github.com/the-omega-institute/trureturing/blob/a6ed97ef09691efed393942b6ae694c4a44e5fc9/docs/develop/theory/KBONACCI_SELF_CALIBRATING_BOUNDARIES.md)，
§§2–4、10.1–10.3。
本轮核读计数、尾状态、固定块宽 Hankel 秩与公平位长串极限；
其余大篇内容不视为全部认证。Hankel 与临界概率结果均为项目既有工具。

<a id="ref-kendpoint"></a>

**[4]**
[K-bonacci Endpoint Tomography and Rank-one Relation Boundaries](https://github.com/the-omega-institute/trureturing/blob/a6ed97ef09691efed393942b6ae694c4a44e5fc9/docs/develop/theory/KBONACCI_ENDPOINT_TOMOGRAPHY_AND_RANK_ONE_RELATION_BOUNDARIES.md)，全文。
当前 blob 为 `4fd7efaf0872ce0d3eb577cc9322a4dc936ca489`。
逐元正秩一与正半定矩阵的区别、观察核及开放桥均予保留。

<a id="ref-rro"></a>

**[5]**
[Recursive Relational Observation: Effective Resolution](https://github.com/the-omega-institute/trureturing/blob/a6ed97ef09691efed393942b6ae694c4a44e5fc9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md)，
§§1.2.13–1.2.14、1.4.8–1.4.9。
完整固定文件 757028 字节，blob 为
`39aee6a1073d77a18c4fe4ea8d887f34ca19d49b`。
本轮实际核读所引段落；固定窗口与概率极限不是本轮新增。

<a id="ref-fibsynth"></a>

**[6]**
[FIB Self-calibrating Relation Mathematics Synthesis](https://github.com/the-omega-institute/trureturing/blob/a6ed97ef09691efed393942b6ae694c4a44e5fc9/docs/develop/theory/FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_SYNTHESIS.md)，全文，尤其 §25.10。
纯幂读数只给两项线性信息，额外标签交换才能完成所述四读重建。

<a id="ref-iii"></a>

**[7]**
[AURIC FIB Atom Quantum Principles and Coherent Reconstruction, Continuation III](https://github.com/the-omega-institute/trureturing/blob/a6ed97ef09691efed393942b6ae694c4a44e5fc9/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md)，
本轮新增 §§183–189。
核读该新增段；熵率论证消费旧 FIB 完成源结果，
未在本报告中重新独立核证其全部上游依赖。

<a id="ref-v46"></a>

**[8]**
[AURIC：log 递归、平方概率与内生观察者的误差几何，V46](https://github.com/the-omega-institute/trureturing/blob/a6ed97ef09691efed393942b6ae694c4a44e5fc9/docs/develop/theory/AURIC_LOG_RECURSION_SQUARED_PROBABILITIES_AND_ENDOGENOUS_ERROR_GEOMETRY_V46.md)，
原稿身份说明与第 6 节。
新入库的历史作者稿，内部“最新”描述属于其旧固定来源；
本文不把转录或入库作为新的独立数学证明。

<a id="ref-v42"></a>

**[9]**
[AURIC：F[13] 关系语义、量子三轴与递归相容，V42](https://github.com/the-omega-institute/trureturing/blob/a6ed97ef09691efed393942b6ae694c4a44e5fc9/docs/develop/theory/AURIC_F13_RELATIONAL_SEMANTICS_QUANTUM_THREE_AXES_AND_RECURSIVE_COMPATIBILITY_V42.md)，
§§1、3、6.1、7.2、12 的相关段落。
本轮固定下载且 blob 与树匹配；相对 v49 未变。
历史稿内部元数据仍属其原快照，本文只沿用所读的接口公式与限定。

<a id="ref-foundation"></a>

**[10]**
[AURIC FIB Atom Pyramid: Foundational Formulas and Relations](https://github.com/the-omega-institute/trureturing/blob/a6ed97ef09691efed393942b6ae694c4a44e5fc9/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)，
§§4、14、42.1–42.2。
本轮核对原五态纤维、所选 Pauli 操作代表及混合划分 Gram。
相对 v49 未变；未把占位、操作、量子态及三阶 Gram 的坐标混同。

<a id="ref-lieb"></a>

**[11]**
Elliott H. Lieb.
[The classical limit of quantum spin systems](https://doi.org/10.1007/BF01646493).
*Communications in Mathematical Physics* **31**(4), 327–340, 1973。
本轮核对
[Princeton 原作者机构书目及摘要](https://collaborate.princeton.edu/en/publications/the-classical-limit-of-quantum-spin-systems/)；
只用于经典极限主题归属，本文平均自旋公式另给完整代数证明，
不声称重证论文的热力学结论。

<!-- 原稿文档结束：\end{document} -->

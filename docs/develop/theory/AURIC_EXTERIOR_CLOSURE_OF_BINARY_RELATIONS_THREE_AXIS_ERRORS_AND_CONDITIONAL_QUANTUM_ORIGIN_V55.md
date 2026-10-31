# AURIC：二元线性关系的外代数闭合

# 三轴误差与条件量子起源

定义、定理与纸面证明　v55.0

项目快照：2026 年 10 月 31 日 23:59:17　Asia/Singapore

> **版本与归属（编者）**：下文完整转写所供 v55.0 原稿。原文“本轮”“本文”以及 HEAD 获取、取得时刻、比较、来源席阅读、未运行程序和制作行为，均为原作者的历史陈述；不是本版转写者声称重做这些行为。另列“编者核读注”仅说明局部条件或来源约定；原有断言仍保留。全文是条件性的纸面论证，不构成 Lean/kernel、原生实现、物理、经验或完整量子起源认证。

## 原稿元数据（作者设置）

PDF 标题：AURIC：二元关系的外代数闭合、三轴误差与条件量子起源  
PDF 作者：AURIC research continuation  
PDF 主题：Binary linear relations, exterior residuals, Bloch atlases, graph stability and conditional quantum reconstruction

<details>
<summary>原稿编译、字体、编号与页眉页脚设置</summary>

原稿指定 XeLaTeX，编译两次；AURICFontPath 可指定 Noto CJK 字体目录。
文类为 article，11pt、A4；页边距 23mm，页眉高度 16pt。
主字体优先为 Noto Serif CJK SC；指定目录时使用 NotoSerifCJKsc-Regular.otf 与 NotoSerifCJKsc-Bold.otf，斜体沿用常规体、粗斜体沿用粗体；未指定目录且该字体不存在时，使用 FandolSong-Regular.otf 与 FandolSong-Bold.otf，斜体和粗斜体同样代用。
等宽字体为 Latin Modern Mono；中文断行 locale 为 zh，断行间距为 0pt plus 1pt。
原稿加载 geometry、fontspec、amsmath、amssymb、amsthm、mathtools、bm、mathrsfs、booktabs、array、tabularx、enumitem、fancyhdr、xcolor、needspace 与 hyperref。
链接颜色为 auricblue，RGB 为 (24,53,79)，保留 Unicode 元数据及彩色链接、URL 与引文。
定义、定理、命题、推论与说明按节共用编号；证明、摘要与书目标题分别为“证明”“摘要”“固定来源、已知结构与阅读范围”。
段首缩进为 1.8em，段间距为 2pt，紧急伸长为 3em；列表无额外间距，左边距为 2em。
左页眉为“AURIC：二元关系、外代数与三轴误差”，右页眉为“v55 / 快照 2026-10-31”，页脚中间为页码；公式允许的分页等级为 2。
标题两行间距为 7pt，标题与副标题间距为 8pt，副标题与快照间距为 5pt。

</details>

## 摘要

本文继续二元复线性关系的正平方残差与三轴归一化，采用标准复内积外代数作为统一结构。
二元目标重合振幅和行列式残差恰组成一个 $SU(2)$ 基变换；
高维时，复 Lagrange 恒等式给出结果与全部二元关系残差的等距分解。
由此把全局纯态迹距离平方精确写成各二元球面弦长平方的质量加权和，
并把混态目标误差分为局部方向偏离与纯度缺额。
完整残差在整体共同酉演化下按外平方酉传导；稀疏关系则需要质量加权图的谱隙，
并得到路径下界、零支撑条件及扰动预算。
外乘与伴随收缩满足标准反对易关系，在完整分次空间上产生 Pauli 表示，
使“关系之关系”的递归具有精确代数闭合。
可逆二元复线性变换归一化后，在纯态图上对应 Möbius 作用；
保留质量时对应 Lorentz 正锥，
只有保持全部转移概率的子类为射影酉变换。
条件正残差滤波给出方差控制的下降律及成功质量，线性酉演化的比值坐标则满足二次 Riccati 方程。
项目新 Quantum 续卷 IV 的实际关系一致性与全菜单非负性，
以及 RRO 新稀有分支恢复界，分别接入概率表示和归一化稳定性的来源问题。
全部证明为纸面推导；数学载体、相位参照、记录与辅助结构均可内生于同一个整体，
但其实际准备、时钟、复合规则与概率标定仍保留明确前提。

<a id="section-1"></a>

## 1. 固定项目、前一轮接口与本轮推进

本轮唯一一次成功取得的活动 HEAD 随后固定为

<code>74d3fbdb768819e31f73<wbr>6d1e2e5686e3f03f6a12</code>。

 提交时间为 2026-10-31 23:59:17，新加坡；取得于 23:59:56。
相对 v54 基线

<code>c7e66ea1741441b39a6f<wbr>4c6239dbd20471c378cf</code>，

 比较报告 63 次提交。API 文件列表截在 300 项，完整 diff 有 302 路径；
完整新旧 theory 树另核对出 9 个变更路径，和 diff 中 theory 集合一致。
新 theory 树 1118 项，未截断。该审计仅保证来源范围，不等于数学认证。[[1]](#bib-head) [[2]](#bib-compare)

> **编者核读注（固定来源与历史归属）**：固定对象可核对提交时间、63 次提交、302 个 diff 路径、9 个 theory 变更及新树 1118 项。API 当时截在 300 项、仅一次成功的 live HEAD 获取及 23:59:56 的取得时刻仍属原作者历史记录，本版不把固定对象核对当作这些在线行为的重演。

直接相关变更中，V50、V51、V52 是历史稿新入库；真正新来源是 Quantum 续卷 IV
第 195–200 节，以及 RRO 原生终端认证追加第 44–48 节。
其他 theory 变化与 Quantum/Magic Blueprint 只分类，没有作为本轮证明或测试证据。[[3]](#bib-v50) [[4]](#bib-v51) [[5]](#bib-v52) [[9]](#bib-qiv) [[10]](#bib-rro)

V44 已有二元图册、闭路相容及全局正性；V51 已有共同核、抽象谱隙误差和有限历史态；
V52 已有二次不变量生成、保尺度 Hopf 坐标、纯态二叉树图册及其物理化限制。
v54 已将线性关系写成正零残差，并联系正矩阵与有限操作重构。
本文继续发展结果–外积残差等距、全部二元三轴误差恒等式和具体图稳定性，
再将标准外代数的递归闭合接入这些对象。标准 Lagrange、CAR、Pauli 与 Lorentz 结构
均不作数学史新发现声明。[[6]](#bib-v44) [[4]](#bib-v51) [[5]](#bib-v52) [[12]](#bib-clifford) [[11]](#bib-lorentz)

全文使用有限维复内积空间，内积对第二变量线性。
密度矩阵满足 $\rho\succeq0,\operatorname{Tr}\rho=1$；
$P_a=aa^\dagger$ 表示单位向量 $a$ 的纯态；迹距离为
$T(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$。
二元通道是选定正交基中的两个振幅坐标，不自动是两个空间局域子系统。
内部参考、记录和标签属于同一整体；数学表示的存在不自动供应原生操作权限或成本。

<a id="section-2"></a>

## 2. 二元线性关系的受限三维几何

#### 定义 2.1（线性关系与正残差）

在 $\mathbb{C}^2$ 中，对 $z\in\mathbb{C}$ 令

$$
\begin{gathered}\ell_z=(-z,1),\\Q_z=\ell_z^\dagger\ell_z\succeq0.\end{gathered}
$$

振幅关系 $\beta=z\alpha$ 等价于 $\ell_z\psi=0$，
亦等价于 $\psi^\dagger Q_z\psi=|\beta-z\alpha|^2=0$。

#### 定理 2.2（零残差纯态及球面图）

对密度矩阵 $\rho$，

$$
\begin{gathered}\operatorname{Tr}(Q_z\rho)=0\quad\Longleftrightarrow\quad\\\rho=P_z=\frac1{1+|z|^2}\begin{pmatrix}1&\bar z\\z&|z|^2\end{pmatrix}.\end{gathered}
$$

写 $z=x+iy$，则

$$
\begin{gathered}P_z=\frac{I+r(z)\cdot\sigma}{2},\\\boxed{r(z)=\frac{(2x,2y,1-x^2-y^2)}{1+x^2+y^2}},\\\|r(z)\|=1.\end{gathered}
$$

**证明。**

$\operatorname{Tr}(Q_z\rho)=\|\ell_z\rho^{1/2}\|_F^2$。
零响应要求 $\operatorname{Ran}\rho\subseteq\ker\ell_z=\operatorname{span}(1,z)^{\mathsf T}$，
迹一性选出唯一投影。展开 Pauli 矩阵给三坐标，
$4x^2+4y^2+(1-x^2-y^2)^2=(1+x^2+y^2)^2$ 给球面式。

∎

固定关系给一个纯态；关系参数连同 $z=\infty$ 的补图变化，
给出整个 $\mathbb{CP}^1\cong S^2$。
三个实坐标满足一个等式，内在自由度仍为二。
反图 $z=(r_x+ir_y)/(1+r_z)$ 在南极失效；用 $\alpha/\beta$ 可覆盖。
某张比值图的极点和零质量块的不可归一化，是不同现象。[[5]](#bib-v52) [[6]](#bib-v44)

#### 定理 2.3（保质量的二元正锥）

设 $M=\left(\begin{smallmatrix}p&c\\\bar c&q\end{smallmatrix}\right)$ Hermitian，
置

$$
\begin{gathered}t=p+q,\\x=(2\Re c,-2\Im c,p-q).\end{gathered}
$$

则

$$
\begin{gathered}M=\frac12(tI+x\cdot\sigma),\\4\det M=t^2-\|x\|^2,\\M\succeq0\Longleftrightarrow t\ge\|x\|.\end{gathered}
$$

非零正矩阵有 $t>0$；归一化 $r=x/t$ 满足

$$
\boxed{\begin{gathered}\|r\|\le1,\\1-\|r\|^2=\frac{4\det M}{t^2}.\end{gathered}}
$$

**证明。**

由 $(x\cdot\sigma)^2=\|x\|^2I$，两个特征值为
$(t\pm\|x\|)/2$，故所有结论立即成立。

∎

这给出未来 Lorentz 锥的代数模型；它是状态正锥的几何，
尚未把其四坐标识别为物理时空坐标。
保留 $t$ 才能恢复原始 $M$。
归一纯态为球面，混态为球内；单独归一化不保证距离收缩或酉性。

<a id="section-3"></a>

## 3. 结果与误差组成一个完整二元酉门

#### 定义 3.1（结果与关系残差）

给定单位目标 $a=(a_1,a_2)^{\mathsf T}$，对任意 $\psi$ 令

$$
\begin{gathered}c=a^\dagger\psi,\\\eta=a_1\psi_2-a_2\psi_1,\\U_a=\begin{pmatrix}\bar a_1&\bar a_2\\-a_2&a_1\end{pmatrix}.\end{gathered}
$$

$c$ 为目标方向振幅；$\eta$ 为偏离线性依赖的行列式残差。

#### 定理 3.2（完整的 $SU(2)$ 结果–残差分解）

$$
\begin{gathered}U_a\in SU(2),\\U_aa=(1,0)^{\mathsf T},\\U_a\psi=(c,\eta)^{\mathsf T},\end{gathered}
$$

并且

$$
\boxed{|c|^2+|\eta|^2=\|\psi\|^2.}
$$

单位向量 $a\in S^3$ 与这样的 $U_a\in SU(2)$ 一一对应。

**证明。**

两行均为单位向量且正交，行列式为 $|a_1|^2+|a_2|^2=1$。
反向，任意 $SU(2)$ 矩阵可唯一写为
$\left(\begin{smallmatrix}u&v\\-\bar v&\bar u\end{smallmatrix}\right)$，
取 $a=(\bar u,\bar v)^{\mathsf T}$ 即得。

∎

对 $a=(1,z)^{\mathsf T}/\sqrt{1+|z|^2}$，此式成为

$$
\begin{gathered}|\psi_1|^2+|\psi_2|^2\\=\frac{|\psi_1+\bar z\psi_2|^2+|\psi_2-z\psi_1|^2}{1+|z|^2}.\end{gathered}
$$

归一输入的输出三轴为

$$
(2\Re(\bar c\eta),\,2\Im(\bar c\eta),\,|c|^2-|\eta|^2)\in S^2.
$$

因此结果和误差的相对相位也在三轴中；只保存两个平方强度会丢掉横向相干量。

若 $a\mapsto e^{i\theta}a$，

$$
U_{e^{i\theta}a}=\operatorname{diag}(e^{-i\theta},e^{i\theta})U_a.
$$

所以目标射线仅确定一族门；定义相干门还要给输出相位约定。
上述参数化涵盖全部单 qubit $SU(2)$，不等于某一个固定门或未经核对的有限原生门集已经普适。

#### 命题 3.3（固定酉门不能全态严格改善同一个目标）

若固定投影 $P$ 与酉矩阵 $U$ 满足
$\operatorname{Tr}(PU\rho U^\dagger)\ge\operatorname{Tr}(P\rho)$ 对所有密度矩阵成立，
则 $U^\dagger PU=P$，所有输入的目标响应均保持。

**证明。**

对全部纯态检验给 $U^\dagger PU-P\succeq0$；其迹为零，所以该差为零。

∎

已知单个输入可以被酉门转向目标；局部复位也可把信息转移到内部辅助部分。
这里排除的是同一个封闭酉门对全部输入均不变坏且有些严格变好。

<a id="section-4"></a>

## 4. 高维结果–残差：标准外代数的等距闭合

#### 定义 4.1（外积残差算子）

令 $\mathcal{H}=\mathbb{C}^d$，$d\ge1$，$a$ 单位。
在 $\Lambda^2\mathcal{H}$ 上采用 $e_i\wedge e_j$（$i<j$）为正交单位基的诱导内积。
定义

$$
\begin{gathered}D_a\psi=a\wedge\psi,\\(D_a\psi)_{ij}=a_i\psi_j-a_j\psi_i,\\\mathcal W_a\psi=(a^\dagger\psi,D_a\psi).\end{gathered}
$$

$d=1$ 时 $\Lambda^2\mathcal{H}=\{0\}$。

#### 定理 4.2（复 Lagrange 恒等式与无损等距）

$$
\begin{gathered}\boxed{D_a^\dagger D_a=I-P_a,}\\\boxed{\begin{gathered}|a^\dagger\psi|^2+\\\sum_{i<j}|a_i\psi_j-a_j\psi_i|^2=\|\psi\|^2.\end{gathered}}\end{gathered}
$$

故 $\mathcal W_a:\mathcal{H}\to\mathbb{C}\oplus\Lambda^2\mathcal{H}$ 等距，
并在像上有逆式

$$
\psi=ac+D_a^\dagger\eta.
$$

**证明。**

展开并对有序对求和：

$$
\begin{gathered}\frac12\sum_{i,j}|a_i\psi_j-a_j\psi_i|^2\\=\left(\sum_i|a_i|^2\right)\left(\sum_j|\psi_j|^2\right)\\-\left|\sum_i\bar a_i\psi_i\right|^2.\end{gathered}
$$

由 $\|a\|=1$ 得二次型恒等式，从而得算子式及
$\mathcal W_a^\dagger\mathcal W_a=P_a+D_a^\dagger D_a=I$。
逆式就是伴随作用在像上的结果。

∎

#### 命题 4.3（残差的相容空间）

$$
\begin{gathered}\operatorname{Ran} D_a=\{\eta\in\Lambda^2\mathcal{H}:a\wedge\eta=0\},\\\dim_{\mathbb{C}}\operatorname{Ran} D_a=d-1.\end{gathered}
$$

**证明。**

取以 $a$ 为第一个向量的正交基。$a\wedge\eta=0$ 恰排除所有不含 $a$ 的楔基项；
留下 $a\wedge e_j$，$j=2,\ldots,d$，即为 $D_a$ 的像。

∎

因此 $\binom d2$ 个关系残差不是互相独立的通道。
例如 $d=3$ 时，
$a_1\eta_{23}-a_2\eta_{13}+a_3\eta_{12}=0$。
全部残差仍受线性相容关系限制。
对混态，完整等距编码为

$$
\mathcal W_a\rho\mathcal W_a^\dagger=
 \begin{pmatrix}
 a^\dagger\rho a&a^\dagger\rho D_a^\dagger\\
 D_a\rho a&D_a\rho D_a^\dagger
 \end{pmatrix}.
$$

删去结果与残差之间的非对角块，是另加的去相干操作。
这里只产生一个保留相干的向量或矩阵，不产生所有归一二元节点态的独立张量包，
因而与 V52 的节点物理化障碍相容。[[5]](#bib-v52)

#### 定理 4.4（误差关系的酉协变）

对 $U\in U(d)$，

$$
\boxed{\begin{gathered}D_{Ua}U=(\Lambda^2U)D_a,\\\mathcal W_{Ua}U=(1\oplus\Lambda^2U)\mathcal W_a.\end{gathered}}
$$

$\Lambda^2U$ 为酉算子。令 $R_a(\rho)=D_a\rho D_a^\dagger$，则

$$
\begin{gathered}\operatorname{Tr}R_a(\rho)=1-a^\dagger\rho a,\\R_{Ua}(U\rho U^\dagger)\\=(\Lambda^2U)R_a(\rho)(\Lambda^2U)^\dagger.\end{gathered}
$$

**证明。**

$(Ua)\wedge(U\psi)=(\Lambda^2U)(a\wedge\psi)$，
且 $(Ua)^\dagger U\psi=a^\dagger\psi$。
$U$ 保持正交基，外平方遂保持正交楔基；密度矩阵公式由两侧取伴随及迹得到。

∎

坐标残差按二阶子式变换：

$$
\eta'_{ij}=\sum_{k<\ell}
 (U_{ik}U_{j\ell}-U_{i\ell}U_{jk})\eta_{k\ell}.
$$

这给“误差也酉”一个精确含义：状态和内部参照共同演化时，完整残差按酉规则传导。
固定参照的误差不必保持；共同演化也不自动缩小相对误差。
稀疏截取的残差一般不在任意整体酉变换下封闭。

<a id="section-5"></a>

## 5. 所有局部三轴怎样精确重组全局误差

#### 定义 5.1（带质量的二元图册）

对 $i<j$ 令 $\iota_{ij}:\mathbb{C}^2\to\mathbb{C}^d$ 为相应坐标嵌入，

$$
\begin{gathered}N^a_{ij}=|a_i|^2+|a_j|^2,\\B^\rho_{ij}=\iota_{ij}^\dagger\rho\iota_{ij},\\N^\rho_{ij}=\operatorname{Tr} B^\rho_{ij}.\end{gathered}
$$

正质量时定义

$$
\begin{gathered}P^a_{ij}=\frac1{N^a_{ij}}\begin{pmatrix}a_i\\a_j\end{pmatrix}\begin{pmatrix}\bar a_i&\bar a_j\end{pmatrix}\\=\frac{I+n^a_{ij}\cdot\sigma}{2},\\\frac{B^\rho_{ij}}{N^\rho_{ij}}=\frac{I+r^\rho_{ij}\cdot\sigma}{2}.\end{gathered}
$$

有 $\|n^a_{ij}\|=1,\ \|r^\rho_{ij}\|\le1$。
零质量时仅保存零标记，不定义相应轴。

<a id="thm:globalerror"></a>

#### 定理 5.2（完整二元关系的混态误差恒等式）

记 $e_a(\rho)=1-a^\dagger\rho a$。则

$$
\boxed{
 e_a(\rho)=\frac12\sum_{i<j}
 N^a_{ij}N^\rho_{ij}(1-n^a_{ij}\cdot r^\rho_{ij}).
 }
$$

等价地，

$$
\boxed{\begin{gathered}e_a(\rho)=\frac14\sum_{i<j}N^a_{ij}N^\rho_{ij}\\\left(\|n^a_{ij}-r^\rho_{ij}\|^2+1-\|r^\rho_{ij}\|^2\right).\end{gathered}}
$$

任一质量为零时该项规定为零。

**证明。**

令 $\ell_{ij}=a_i e_j^{\mathsf T}-a_j e_i^{\mathsf T}$。
前节恒等式给

$$
\sum_{i<j}\ell_{ij}^\dagger\ell_{ij}=I-P_a.
$$

当 $N^a_{ij}>0$ 时，
$\ell_{ij}^\dagger\ell_{ij} =N^a_{ij}\iota_{ij}(I-P^a_{ij})\iota_{ij}^\dagger$。
Pauli 迹公式给

$$
\operatorname{Tr}(\ell_{ij}^\dagger\ell_{ij}\rho)
 =\frac{N^a_{ij}N^\rho_{ij}}2(1-n^a_{ij}\cdot r^\rho_{ij}).
$$

再用 $2(1-n\cdot r)=\|n-r\|^2+1-\|r\|^2$。
目标质量零时 $\ell_{ij}=0$；实际质量零时正块 $B^\rho_{ij}=0$，
故上述零项约定精确符合未归一化公式。

∎

#### 推论 5.3（全局纯态距离是二元球面弦差的质量加权和）

对单位 $a,b$，

$$
\boxed{\begin{gathered}T(P_a,P_b)^2=1-|a^\dagger b|^2\\=\frac14\sum_{i<j}N^a_{ij}N^b_{ij}\|n^a_{ij}-n^b_{ij}\|^2.\end{gathered}}
$$

**证明。**

若 $P_a=P_b$，两边均为零。否则两射线张成二维空间，
$P_a-P_b$ 在其正交补上为零，在该二维空间的特征值为
$\pm\sqrt{1-|a^\dagger b|^2}$。纯态的每个非零主块仍秩一，
故定理 [5.2](#thm:globalerror) 的纯度缺额项全部消失。

∎

该加权和不是任意独立三轴点的平均；各项有共同全局来源，且权重总和一般不等于一。
它保留所有标签及两侧质量。混态中的第二项 $1-\|r\|^2$ 是局部纯度缺额，
与方向误差一起贡献整体目标误差。
一般混态满足

$$
e_a(\rho)\le T(\rho,P_a)\le\sqrt{e_a(\rho)}.
$$

下界由效果 $I-P_a$ 的期望差得到；上界把 $\rho$ 谱分解，
用迹范数凸性、纯态公式与 Cauchy 不等式即得。

另有精确效果分解

$$
\boxed{P_a+\sum_{i<j}\ell_{ij}^\dagger\ell_{ij}=I.}
$$

所以在采用正效果读出的条件下，目标事件与全部二元关系残差构成一个完整 POVM。
这条完备关系本身是代数结论；实际概率如何遵守这些效果关系，在第 [11](#sec:probability) 节单独处理。

<a id="section-6"></a>

## 6. 关系之关系：外乘、收缩与 Pauli 三轴

#### 定义 6.1（完整外代数上的两个互为伴随的操作）

令 $\Lambda\mathcal{H}=\bigoplus_{k=0}^d\Lambda^k\mathcal{H}$，各次数正交，
每层采用标准诱导内积。对单位 $a$ 定义

$$
\begin{gathered}\varepsilon_a\omega=a\wedge\omega,\\\iota_a=\varepsilon_a^\dagger.\end{gathered}
$$

边界约定 $\Lambda^{-1}\mathcal{H}=\Lambda^{d+1}\mathcal{H}=\{0\}$。

<a id="thm:car"></a>

#### 定理 6.2（标准反对易关系与逐层平方分解）

$$
\boxed{\begin{gathered}\varepsilon_a^2=\iota_a^2=0,\\\iota_a\varepsilon_a+\varepsilon_a\iota_a=I.\end{gathered}}
$$

令 $P=\varepsilon_a\iota_a$、$Q=\iota_a\varepsilon_a$，则
$P,Q$ 为互补正交投影，每层有

$$
\begin{gathered}\omega=P\omega+Q\omega,\\\boxed{\|\omega\|^2=\|\iota_a\omega\|^2+\|\varepsilon_a\omega\|^2.}\end{gathered}
$$

且每一次数的序列满足
$\ker(\varepsilon_a|_{\Lambda^k\mathcal{H}}) =\operatorname{Ran}(\varepsilon_a|_{\Lambda^{k-1}\mathcal{H}})$。

**证明。**

对可分解楔积，

$$
\begin{gathered}\iota_a(v_1\wedge\cdots\wedge v_k)\\=\sum_{j=1}^k(-1)^{j-1}\langle a,v_j\rangle\,\\v_1\wedge\cdots\widehat{v_j}\cdots\wedge v_k.\end{gathered}
$$

于是 $\iota_a(a\wedge\omega)=\omega-a\wedge\iota_a\omega$。
$a\wedge a=0$ 给 $\varepsilon_a^2=0$，取伴随给 $\iota_a^2=0$。
从反对易式得 $P^2=P,\ Q^2=Q,\ PQ=0,\ P+Q=I$；
取内积得范数恒等式。
若 $\varepsilon_a\omega=0$，则
$\omega=\varepsilon_a\iota_a\omega$，故核包含于前一像；
反向由平方为零立即成立。

∎

在一次空间 $\mathcal{H}$ 上，

$$
\begin{gathered}\varepsilon_a\iota_a=P_a,\\\iota_a\varepsilon_a=I-P_a,\end{gathered}
$$

因此前节结果–残差分解是这个逐层恒等式的最低非平凡实例。
这提供关系继续展开和收缩的精确递归；该递归中平方质量保持。
同一方向连续外乘满足 $\varepsilon_a^2=0$；
继续分解剩余信息时，应在 $a^\perp$ 中选择后续方向。

#### 推论 6.3（完整分次空间中的 Pauli 表示）

定义

$$
\begin{gathered}\Gamma_1=\varepsilon_a+\iota_a,\\\Gamma_2=i(\varepsilon_a-\iota_a),\\\Gamma_3=\iota_a\varepsilon_a-\varepsilon_a\iota_a.\end{gathered}
$$

它们自伴，并满足

$$
\begin{gathered}\Gamma_j\Gamma_k+\Gamma_k\Gamma_j=2\delta_{jk}I,\\\Gamma_1\Gamma_2=i\Gamma_3.\end{gathered}
$$

在将 $a$ 方向放在前面的酉识别

$$
\Lambda\mathcal{H}\cong
 \Lambda(\mathbb{C} a)\otimes\Lambda(a^\perp)
 \cong\mathbb{C}^2\otimes\Lambda(a^\perp)
$$

下，$\Gamma_j=\sigma_j\otimes I$。

**证明。**

由定理 [6.2](#thm:car) 直接相乘即得全部关系。
任意 $\omega$ 唯一写为 $\omega_0+a\wedge\omega_1$，
$\omega_0,\omega_1\in\Lambda(a^\perp)$。
在对应列向量 $(\omega_0,\omega_1)^{\mathsf T}$ 上，
$\varepsilon_a=\left(\begin{smallmatrix}0&0\\I&0\end{smallmatrix}\right)$，
$\iota_a=\left(\begin{smallmatrix}0&I\\0&0\end{smallmatrix}\right)$，
从而得到三矩阵。

∎

这里 $\Gamma_1,\Gamma_2$ 改变外次数，不能说在每个固定次数空间内都构成三轴。
若内部因子没有固定为同一个方向，取其局部三轴可得到混态球；
“两个正交分支”仍可能携带各自的内部方向。
完整载体的维数是 $2^d$，不是将任意高维信息免费压成一个 qubit。
这些是标准外代数与 CAR 表示，作者原文可见 Lundholm–Svensson
第 4.3、8.2 节；本文给出所用有限证明。[[12]](#bib-clifford)
该代数联系本身不选择现实粒子的统计或物理时空，它也没有从无前提中产生已采用的复内积。

> **编者核读注（CAR 来源约定）**：所引作者修订稿 §§4.3、8.2 采用几何代数的外乘、左收缩、reverse 与标量积记号，并区分实基及其复化。本文以对第二变量线性的 Hermitian 内积和伴随定义收缩；复向量的共轭约定须按本文定义理解。源文的 Fock 表示是代数接口，不能替代本段保留的物理统计前提。

<a id="section-7"></a>

## 7. 稀疏关系的图稳定性与零支撑

先设目标全部分量非零，$p_i=|a_i|^2>0$、$\sum_ip_i=1$，$d\ge2$。
对无向正权图 $G=(\{1,\ldots,d\},E)$，令

$$
\begin{gathered}q_{ij}=\frac{a_i e_j^{\mathsf T}-a_j e_i^{\mathsf T}}{\sqrt{p_i+p_j}},\\L_{ij}=q_{ij}^\dagger q_{ij},\\Q_G=\sum_{\{i,j\}\in E}w_{ij}L_{ij},\\w_{ij}>0.\end{gathered}
$$

$L_{ij}$ 是嵌在全空间中的秩一投影。

#### 定理 7.1（关系能量等于质量加权图能量）

写 $\psi_i=a_i f_i$，则

$$
\begin{gathered}\langle\psi,Q_G\psi\rangle
 =\sum_{\{i,j\}\in E}c_{ij}|f_i-f_j|^2,\\c_{ij}=w_{ij}\frac{p_ip_j}{p_i+p_j},\end{gathered}
$$

$$
\begin{gathered}\|\psi\|^2=\sum_ip_i|f_i|^2,\\\langle a,\psi\rangle=\sum_ip_if_i.\end{gathered}
$$

图连通当且仅当 $\ker Q_G=\mathbb{C} a$。此时

$$
\begin{gathered}\Delta_G=
 \inf_{\substack{\sum_ip_if_i=0\\f\ne0}}
 \frac{\sum_Ec_{ij}|f_i-f_j|^2}{\sum_ip_i|f_i|^2}>0,\\Q_G\succeq\Delta_G(I-P_a).\end{gathered}
$$

**证明。**

代入 $q_{ij}\psi$ 即得能量公式。零能量要求 $f$ 在每个连通分量上常量，
所以核维数等于连通分量数。连通时，有限维单位球上的正交补没有零能量，
紧性给正下界。变分式就是限制于 $a^\perp$ 的最低特征值。

∎

#### 定理 7.2（路径下界与瓶颈上界）

为每对 $i<j$ 选择一条连接路径 $\gamma_{ij}$，令

$$
K_G=\sum_{i<j}p_ip_j\sum_{e\in\gamma_{ij}}c_e^{-1}.
$$

则 $\Delta_G\ge K_G^{-1}$。
对任意非平凡顶点集 $A$，记 $s=\sum_{i\in A}p_i$，
另有

$$
\Delta_G\le\frac{\sum_{e\in\partial A}c_e}{s(1-s)}.
$$

**证明。**

均值零时
$\sum_ip_i|f_i|^2=\sum_{i<j}p_ip_j|f_i-f_j|^2$。
路径 Cauchy 不等式给
$|f_i-f_j|^2\le(\sum_{\gamma_{ij}}c_e^{-1}) (\sum_{\gamma_{ij}}c_e|df_e|^2)$；
各路径能量至多为总能量，求和即得下界。
上界取 $f=1-s$ 于 $A$、$f=-s$ 于补集，直接代入 Rayleigh 商。

∎

#### 推论 7.3（局部三轴残差控制全局距离）

在上述图连通的情形，

$$
\operatorname{Tr}(Q_G\rho)=\frac12\sum_{e\in E}
 w_eN^\rho_e(1-n^a_e\cdot r^\rho_e),
$$

$$
\boxed{\begin{gathered}e_a(\rho)\le\frac{\operatorname{Tr}(Q_G\rho)}{\Delta_G},\\T(\rho,P_a)\le\min\left\{1,\sqrt{\frac{\operatorname{Tr}(Q_G\rho)}{\Delta_G}}\right\}.\end{gathered}}
$$

**证明。**

第一式由局部 Pauli 配对；第二式由谱隙算子不等式取迹，
再用 $T\le\sqrt e$。

∎

一般谱隙误差界已见 V51；这里把其能量与常数具体化到带质量的二元图。
对完整图取 $w_{ij}=p_i+p_j$，精确有 $Q_G=I-P_a$、$\Delta_G=1$。
但总边权为 $d-1$；若按概率随机选边，须除以 $d-1$，
验证算子的谱隙相应变成 $1/(d-1)$。残差尺度与谱隙必须一起改变。[[4]](#bib-v51)

#### 命题 7.4（零支撑的正确处理）

令 $S=\{i:a_i\ne0\}$。在 $S$ 上取连通正权关系图，并加入
$\sum_{i\notin S}\tau_i\lvert i\rangle\langle i\rvert$、$\tau_i>0$ 的零坐标钉定项，
则共同核恰为 $\mathbb{C} a$。若 $|S|\ge2$，谱隙至少为
$\min\{\Delta_S,\min_{i\notin S}\tau_i\}$，不存在的部分忽略；
单点支持只需零坐标钉定，$d=1$ 时不存在非零正交误差。

**证明。**

钉定项使支持外分量为零；支持内应用上面的连通定理。
算子在两个正交部分分块，谱隙取各块正谱下界的最小值。

∎

原图连通不能代替正支撑连通。例如路径 $1-2-3$ 与
$a=(1,0,1)^{\mathsf T}/\sqrt2$，两条关系都只要求 $\psi_2=0$，
共同核为 $\operatorname{span}(e_1,e_3)$，没有确定端点的相对关系。
完整外积公式无需除以任何目标分量，因此自动处理此边界。
任意二元齐次线性关系也可分为非零比率边、单坐标零钉定和平凡关系；
非零比率分量中，闭路不平衡或一个零钉定都会迫使整分量为零。
其余每个平衡分量贡献一维核。这复用 V44/V51 的树传播原则，
并不将同一态分量比值闭路混同于不同态之间的 Berry 输运。[[6]](#bib-v44) [[4]](#bib-v51)

<a id="section-8"></a>

## 8. 关系自身有误差时的稳定预算

#### 定理 8.1（测量残差与参考误差的共同控制）

设 $Q\succeq\Delta(I-P_a)$，$\ker Q=\mathbb{C} a$，$\Delta>0$。
令 $\widetilde Q\succeq0$，$\delta=\|\widetilde Q-Q\|$。
若 $\operatorname{Tr}(\widetilde Q\rho)\le\varepsilon$，则

$$
\begin{gathered}e_a(\rho)\le\frac{\varepsilon+\delta}{\Delta},\\\boxed{
 T(\rho,P_a)\le\min\{1,\sqrt{(\varepsilon+\delta)/\Delta}\}.
 }\end{gathered}
$$

**证明。**

$\operatorname{Tr}(Q\rho)\le\operatorname{Tr}(\widetilde Q\rho)+\delta\operatorname{Tr}\rho \le\varepsilon+\delta$，再应用原谱隙界。

∎

#### 定理 8.2（关系扰动后的最低态）

若 $d\ge2$ 且 $\delta<\Delta/2$，
$\widetilde Q$ 的最低特征态唯一，最低谱隙至少 $\Delta-2\delta$。
其单位向量 $b$ 满足

$$
\boxed{T(P_b,P_a)\le\frac{\delta}{\Delta-\delta}.}
$$

**证明。**

变分原理给最低特征值 $\lambda_0\le\delta$，第二特征值至少 $\Delta-\delta$。
令 $E=\widetilde Q-Q$、$u=(I-P_a)b$，投影特征方程得

$$
(Q|_{a^\perp}-\lambda_0I)u=-(I-P_a)Eb.
$$

左侧算子的最小特征值至少 $\Delta-\delta$，所以
$\|u\|\le\delta/(\Delta-\delta)$。纯态距离等于 $\|u\|$。

∎

对同一二元边，

$$
\|L_e-\widetilde L_e\|=\tfrac12\|n_e-\widetilde n_e\|.
$$

固定权重时 $\delta\le\frac12\sum_ew_e\|n_e-\widetilde n_e\|$。
权重也改变时，三角不等式给

$$
\begin{gathered}\delta\le\sum_e\left[\begin{gathered}|w_e-\widetilde w_e|\\+\frac{\min(w_e,\widetilde w_e)}2\|n_e-\widetilde n_e\|\end{gathered}\right].\end{gathered}
$$

零权项不要求给未定义的轴。
若一个关系图有很弱的连接，谱隙可很小；此时纯态唯一性仍成立，
但同样的局部读出误差会对应很差的全局控制。

<a id="section-9"></a>

## 9. 归一化线性关系的 Möbius 与 Lorentz 作用

#### 定义 9.1（保质量的射影线性更新）

对 $A\in GL(2,\mathbb{C})$ 令

$$
\begin{gathered}m_A(\rho)=\operatorname{Tr}(A\rho A^\dagger)>0,\\F_A(\rho)=A\rho A^\dagger/m_A(\rho).\end{gathered}
$$

若 $A=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)$，
则在复图上

$$
\begin{gathered}f_A(z)=\frac{c+dz}{a+bz},\\m_A(P_z)=\frac{|a+bz|^2+|c+dz|^2}{1+|z|^2}.\end{gathered}
$$

分母为零时换到无穷远图；可逆性保证分子分母不同时为零。
任意这样的 $A$ 都将纯态球面双射到自身，但一般改变球面距离。

#### 定理 9.2（质量与误差的精确传导）

$$
\begin{gathered}F_B\circ F_A=F_{BA},\\m_{BA}(\rho)=m_A(\rho)m_B(F_A(\rho)).\end{gathered}
$$

对纯态 $P,Q$，

$$
\boxed{\begin{gathered}T(F_A(P),F_A(Q))\\=\frac{|\det A|}{\sqrt{m_A(P)m_A(Q)}}T(P,Q).\end{gathered}}
$$

**证明。**

前两式直接代入定义。二元纯态距离为
$T(P_\psi,P_\phi)=|\det[\psi,\phi]|$；
两向量经 $A$ 后分别除以范数，行列式乘以
$\det A/\sqrt{m_A(P)m_A(Q)}$，取模即得。

∎

令 $\kappa(A)$ 为最大与最小奇异值之比，则

$$
\begin{gathered}\kappa(A)^{-1}T(P,Q)\le T(F_A(P),F_A(Q))\\\le\kappa(A)T(P,Q).\end{gathered}
$$

可逆性给有限常数；接近秩亏时该常数可以发散。
若使用 $ds_{\rm FS}^2=|dz|^2/(1+|z|^2)^2$ 的约定，
由 $f'_A(z)=\det A/(a+bz)^2$ 还有

$$
f_A^*ds_{\rm FS}^2=\frac{|\det A|^2}{m_A(P_z)^2}ds_{\rm FS}^2.
$$

全部可逆复线性射影作用保角；球面圆度量是上述度量的四倍。

#### 定理 9.3（酉性的几何筛选）

对可逆 $A$，以下等价：
$m_A$ 在全部态上恒定；
$A^\dagger A=cI$（$c>0$）；
$A=\sqrt c\,U$ 且 $U$ 酉；
$F_A$ 保持全部纯态转移概率；
$F_A$ 保持全部纯态迹距离。
此时其三轴作用是正向旋转。

**证明。**

全部纯态上二次型恒定等价于 $A^\dagger A=cI$，
并等价于缩放酉。酉性保持内积，给距离及转移概率保持。
反向，取 $A^\dagger A$ 的正交特征向量 $e_1,e_2$，
特征值 $\lambda_1,\lambda_2>0$；
$(e_1+e_2)/\sqrt2$ 与 $(e_1-e_2)/\sqrt2$ 原来正交，
变换后归一内积为 $(\lambda_1-\lambda_2)/(\lambda_1+\lambda_2)$，
距离保持迫使两特征值相等。
酉共轭保持 Pauli 迹内积，给三维正交变换；
酉群连通使其行列式为正。

∎

质量恒定的代数判据和质量乘积已见 V41；这里把它们接到精确距离律。
若要把 $A$ 当作实际单分支矩阵，需 $A^\dagger A\preceq I$；
一般 $A$ 可缩放为满足此式的 $K$，射影作用不变，成功质量改变。
第二个分支 $\sqrt{I-K^\dagger K}$ 补成完整记录等距。[[7]](#bib-v41)

保质量坐标的变换 $M'=AMA^\dagger$ 为实线性，满足

$$
\boxed{t'^2-\|x'\|^2=|\det A|^2(t^2-\|x\|^2).}
$$

当 $\det A=1$ 时保持 Lorentz 二次型及正锥。
例如对实数 $\eta$，$A_\eta=\operatorname{diag}(e^{\eta/2},e^{-\eta/2})$ 给

$$
\begin{gathered}t'=\cosh\eta\,t+\sinh\eta\,x_3,\\x'_3=\sinh\eta\,t+\cosh\eta\,x_3,\\x'_{1,2}=x_{1,2}.\end{gathered}
$$

在复图中 $z'=e^{-\eta}z$，通常不是酉旋转。
该联系是已知 spinor/Lorentz 与滤波结构；本文只证明所需二元式，
没有把它宣称为物理时空或引力的推导。[[11]](#bib-lorentz)

> **编者核读注（滤波文献的对象）**：Verstraete–Dehaene–De Moor 开篇及定理 2 处理两 qubit 的局部分支，要求两个二阶分支矩阵可逆且各自的伴随乘积不超过单位阵；其四乘四相关矩阵在忽略归一化时按左右正向、保时向 Lorentz 变换更新，并带行列式尺度。这里的单个二元正矩阵变换由正文独立证明，不将论文的两体分类或相关矩阵归一约定直接搬入。

<a id="section-10"></a>

## 10. 误差下降、分支质量与二次演化方程

#### 定理 10.1（正残差的条件下降）

对有限维 $Q\succeq0$，令

$$
\begin{gathered}K_\tau=e^{-\tau Q},\\Z_\tau=\operatorname{Tr}(K_\tau\rho K_\tau),\\\rho_\tau=K_\tau\rho K_\tau/Z_\tau,\\q_\tau=\operatorname{Tr}(Q\rho_\tau),\\\tau\ge0.\end{gathered}
$$

有限 $\tau$ 时 $Z_\tau>0$，且

$$
\begin{gathered}\dot\rho_\tau=-\{Q,\rho_\tau\}+2q_\tau\rho_\tau,\\\dot Z_\tau=-2q_\tau Z_\tau,\end{gathered}
$$

$$
\boxed{\begin{gathered}\dot q_\tau=-2\left[\operatorname{Tr}(Q^2\rho_\tau)-q_\tau^2\right]\\=-2\operatorname{Var}_{\rho_\tau}(Q)\le0.\end{gathered}}
$$

**证明。**

$\dot K_\tau=-QK_\tau=-K_\tau Q$，对分子和迹微分，
再用商法则即得。非负性来自
$\operatorname{Tr}[(Q-q_\tau I)^2\rho_\tau]\ge0$。

∎

若 $P_0$ 为 $\ker Q$ 的投影，$Q\succeq\Delta(I-P_0)$、$\Delta>0$，
初始质量 $p=\operatorname{Tr}(P_0\rho)>0$，则

$$
\boxed{
 \operatorname{Tr}[(I-P_0)\rho_\tau]\le
 \frac{e^{-2\tau\Delta}(1-p)}
 {p+e^{-2\tau\Delta}(1-p)}.
 }
$$

证明是把未归一化总质量写为 $p+R_\tau$，
$0\le R_\tau\le e^{-2\tau\Delta}(1-p)$，再对递增函数
$R\mapsto R/(p+R)$ 使用上界。
$Z_\tau\to p$；若 $p=0$，此滤波不能产生原先没有的核成分。

对 $Q=I-P_a$，在结果–残差坐标中就是
$(c,\eta)\mapsto(c,e^{-\tau}\eta)$ 后归一化，
上述界成为精确式

$$
\begin{gathered}Z_\tau=p+(1-p)e^{-2\tau},\\e_\tau=\frac{(1-p)e^{-2\tau}}{p+(1-p)e^{-2\tau}}.\end{gathered}
$$

因为 $K_\tau^\dagger K_\tau\preceq I$，
取内部正交单位记录 $\lvert s\rangle,\lvert f\rangle$，则
$K_\tau\psi\otimes\lvert s\rangle+\sqrt{I-K_\tau^\dagger K_\tau}\psi\otimes\lvert f\rangle$
给保留成功与失败记录的整体等距。
只取成功分支才产生该条件下降；$\tau$ 是过滤强度参数，尚未被识别为物理时钟。

对归一纯态，令 $q=\langle\psi,Q\psi\rangle$、$v=(Q-q)\psi$。
采用与上述 Fubini–Study 约定相容的水平切空间度量
$g(u,w)=\Re\langle u,w\rangle$，
有 $dq(w)=2\Re\langle v,w\rangle$，所以 $\operatorname{grad}q=2v$。
归一化条件滤波的速度为 $-v=-\frac12\operatorname{grad}q$；
在 $\hbar=1$ 单位下，由 $Q$ 生成的酉运动之水平切向速度为 $-iv$，
并保持该期望。
这把变分与酉运动联系在同一个复内积结构中，也保留二者操作语义的差别。

#### 定理 10.2（线性演化的射影坐标是二次 Riccati 关系）

> **编者核读注（演化参数）**：本定理中的 $\hbar$ 取非零实常数，通常取正；Bloch 方程中的 $h_0$ 与 $h$ 是 Hermitian 分解的实系数。除法和可微比值仅在所声明的非零图域内使用。

给定 Hermitian $H(t)$ 与可微方程
$i\hbar\dot\psi=H(t)\psi$，$\psi=(\alpha,\beta)^{\mathsf T}$，
在 $\alpha\ne0$ 的图上令 $z=\beta/\alpha$。则

$$
\boxed{
 i\hbar\dot z
 =H_{10}+(H_{11}-H_{00})z-H_{01}z^2.
 }
$$

若 $H=h_0I+h\cdot\sigma$，其 Bloch 向量满足
$\dot r=(2/\hbar)h\times r$。

**证明。**

把线性方程代入
$\dot z=(\dot\beta\alpha-\beta\dot\alpha)/\alpha^2$。
再由 $\dot\rho=-i[H,\rho]/\hbar$ 和
$[h\cdot\sigma,r\cdot\sigma]=2i(h\times r)\cdot\sigma$ 得三轴式。

∎

因此高次形式可以来自线性振幅经比值坐标投影，并不表示独立自由度增多。
$\alpha=0$ 时换图即可，球面运动没有发散。
这里输入了具体生成元与可微参数；静态关系图本身没有选出实际 Hamiltonian 或钟的标定。

<a id="section-11"></a>

## 11. 从实际关系一致性到密度态与平方概率

<a id="sec:probability"></a>

前述等距恒等式确定平方质量，但将质量解释为实际概率仍需读出相容条件。
本轮 Quantum 续卷 IV 提供了比直接假设全正锥正泛函更贴原生菜单的接口。
以下先给其有限维结构原理，再保留实际来源的可测条件。[[9]](#bib-qiv)

#### 定义 11.1（实际效果的实关系一致性）

设 $\mathcal{A}=\bigoplus_sM_{d_s}(\mathbb{C})$ 为非零有限直和，$d_s\ge1$，
$V=\operatorname{Herm}(\mathcal{A})$。
给定可数实际效果族 $\{E_q\}\subset V_+$，实张成 $V$；
另给非空菜单族，每个菜单是有限索引集合，其效果和为 $I$，
且菜单的并覆盖全部 $q$。因而每个 $E_q\preceq I$。
赋予每个 $E_q$ 非负响应 $k_q$，逐菜单归一。
关系一致性 RC 指每个有限实线性关系满足

$$
\begin{gathered}\sum_jc_jE_{q_j}=0
 \ \Longrightarrow\
 \sum_jc_jk_{q_j}=0,\\c_j\in\mathbb{R}.\end{gathered}
$$

另假设每一字面块的全部秩一投影均可由该块内的实际效果逼近。

#### 定理 11.2（密集实际效果上的关系闭合给正密度表示）

在上述条件下，存在唯一正迹一块矩阵 $\sigma$，使

$$
\boxed{\begin{gathered}k_q=\operatorname{Tr}(\sigma E_q)\\\text{对全部 }q.\end{gathered}}
$$

**证明。**

选一个由实际效果组成的有限实基 $B_1,\ldots,B_n$，
定义 $\ell(\sum_rx_rB_r)=\sum_rx_rk_{B_r}$。
RC 保证它与每个实际效果的已给响应一致。
一个完整菜单的归一化给 $\ell(I)=1$。
有限维线性泛函连续；每块秩一投影 $P$ 是实际效果极限，
故 $\ell(P)\ge0$。谱分解推出 $\ell$ 在整个块正锥上非负。
实迹内积给唯一 Hermitian 代表 $\sigma$；
$\langle v,\sigma v\rangle=\ell(\lvert v\rangle\langle v\rvert)\ge0$ 和 $\operatorname{Tr}\sigma=1$ 给正密度。
反向，正迹一块矩阵的迹配对显然满足全部条件。

∎

对单个完整矩阵块的纯态 $\sigma=P_a$ 和秩一效果 $P_b$，
得到 $\operatorname{Tr}(P_aP_b)=|a^\dagger b|^2$。
对直和代数，纯态只位于一个简单块，不能把任意跨扇区射线当作其极端态。
二元特例中，若 $\ell(I)=1$、$\ell(\sigma_j)=r_j$，

$$
\ell(P_n)=\frac{1+r\cdot n}{2}.
$$

所有球面方向上的非负性，等价于 $\|r\|\le1$；
取 $n=-r/\|r\|$ 可证必要性，Cauchy 不等式给充分性。
因此三轴平方约束也可从完整方向族的线性正响应闭合得到。

#### 命题 11.3（有限三轴非负不等于全方向正性）

> **编者核读注（方向的规范）**：这里的有限方向均取单位向量 $n_k\in S^2$，与前文秩一投影 $P_n$ 的球面方向一致；空集按证明中的 $m=0$ 约定处理。

只检查 $x,y,z$ 三组投影，只能得到 $|r_j|\le1$。
$r=(1,1,1)$ 的三组二元响应都非负且归一，
但 $(I+r\cdot\sigma)/2$ 有负特征值。
更一般地，对任意有限方向集 $\{n_k\}$，
存在 $\|r\|>1$ 却满足 $|r\cdot n_k|\le1$ 的 $r$。

**证明。**

三轴例直接代入。一般选单位 $v$ 不平行于任何 $\pm n_k$，
则 $m=\max_k|v\cdot n_k|<1$；空方向集约定 $m=0$。
取 $R>1$ 且 $Rm\le1$（$m=0$ 时任取 $R>1$），令 $r=Rv$。

∎

这不妨碍用有限完备数据先重建一个矩阵再检验其正性；
它说明有限菜单的各列非负本身不是全锥正性证明。
Quantum IV 定理 199.1 在原菜单和全部旧标签上给出更一般的
$T=(I-cP_v)/(d-c)$ 带符号比较表，正是同一界限。[[9]](#bib-qiv)

### 原生可测切口的准确接口

Quantum IV 保持原 $\mathbb{C}^{89}$ 来源，在记录 $i=0,1$ 后使用维数 $55,34$ 的载体，
其字面块 Hermitian 空间实维数为 $1051,610$。
效果索引是七地址有限未来及全部 $1024$ 旧标签；块内秩一密度复用 III151.2。
共同实际切口、真实历史到该切口的映射，以及实际非负归一可测核均先已给出。

RC 起初逐关系几乎处处成立。只取每个实际效果相对于一个有限实际基的可数坐标关系，
合并它们与行非负归一性的可数例外集，便得到一个共同满测集。
在其每一点按上面证明构造线性泛函；它的基值可测，所以代表矩阵场可测。
对不可数实系数关系的一致性由已构造的线性性给出，无需交不可数个满测集。
这就是 IV 定理 196.1 约减独立全锥正性前件的要点。[[9]](#bib-qiv)

该结果没有自行供应 RC 或共同实际切口，也没有决定实际记录质量。
IV 第 197 节所用粗 Born 行仍是独立前件。
标量终端核有相同效果表示，不等于其完整程序历史相同。
因此这里推进了“换公理”的明确位置，尚未从原门矩阵单独推出现实概率。

<a id="section-12"></a>

## 12. 项目新稀有分支定理与归一化稳定性

对非零正矩阵，$M/\operatorname{Tr} M$ 是条件化。
若存在两个不同密度矩阵 $\rho_1,\rho_2$，则
$t\rho_1,t\rho_2\to0$，归一化后却保持不同，
故归一化不能连续延拓到零质量。
若 $\operatorname{Tr} M,\operatorname{Tr} N\ge m>0$，则

$$
\left\|\frac M{\operatorname{Tr} M}-\frac N{\operatorname{Tr} N}\right\|_1
 \le\frac{2}{m}\|M-N\|_1.
$$

证明是加减 $N/\operatorname{Tr} M$，并使用
$|\operatorname{Tr}(M-N)|\le\|M-N\|_1$。
这解释了本轮二元误差恒等式为何必须保留每个 $N_{ij}$。

RRO 新第 44–48 节进一步给出原生的定量分离。
在同一原 $89$ 维、十一地址连续密度类中，固定记录 $i$、
另一记录 $j$、$0<\epsilon<1$，以

$$
\begin{gathered}\psi(r)=\max\{0,\min\{1,2-r\}\},\\H_n(z)=h(z)\psi(nt_i(z)),\\\Pi_n=b+\epsilon H_nc\end{gathered}
$$

构造截断族；整数 $n\ge1+a_i/a_j$，$a_i,a_j>0$ 为原来源固定常数。
定理 44.2 保持全部原生静态分量方程；定理 45.1 精确给

$$
\boxed{\begin{gathered}\delta_n=\epsilon a_i/n,\\\sup_{z\ne0}\operatorname{TV}(\Pi_n(z),b(z))\\=16\delta_n\longrightarrow0.\end{gathered}}
$$

数学极值的全支撑父源满足 $t_i=1/n$；实际有限 ready 字提供相同上确界，
没有给精确有限字达到者。[[10]](#bib-rro)

在 RRO30.1 已给读取前律、字面报告、配置保留及空未来的单切口语义下，
条件修正系数是 $\gamma=\epsilon H_n/t_i$，仅在 $t_i>0$ 定义。
定理 46.3 证明遗忘质量与父源后的系数像为
$[0,\epsilon L_i(p)]$，与 $n$ 无关。
令 $\chi_\ell$ 为原 ready 经实际有限前缀 $\ell$ 后的向量，
$K_{i,n}(\chi_\ell)$ 为上述条件旧标签行，并置

$$
\begin{gathered}\mathcal X_i=\{[M_i\chi_\ell]:t_i(\chi_\ell)>0\},\\E_{i,n}(R)=\sup_{\ell:\,t_i(\chi_\ell)>0}\\\operatorname{TV}\!\left(R([M_i\chi_\ell]),K_{i,n}(\chi_\ell)\right).\end{gathered}
$$

定理 47.1 在实际后射线域 $\mathcal X_i$ 上、
只读该射线的连续解码器类中证明；具体取
$R:\mathcal X_i\to\mathcal{D}_{\rm cl}(\Omega_{10})$，
$\Omega_{10}=\{0,1\}^{10}$，其中 $\mathcal{D}_{\rm cl}$ 表示标签概率单纯形。
连续性只在 $\mathcal X_i$ 的子空间拓扑下要求；
$R$ 可依赖 $i,n,\epsilon$，不另读取父源或前缀。其精确结论为

$$
\boxed{\inf_R E_{i,n}(R)=4\epsilon a_i>0.}
$$

若另有共同下界 $t_k\ge\tau>0$，命题 48.1 则给

$$
\operatorname{TV}(K_{k,n},B_k)\le8\delta_n/\tau\longrightarrow0.
$$

因此全局误差趋零与所有稀有条件分支的统一恢复，是不同的量词命题。
每个固定有限正质量前缀套件最终甚至恰好给 Born 行，
恒正统一风险来自随 $n$ 移动的 $1/n$ 分支。[[10]](#bib-rro)

这些是已声明单切口前件下的标量赋值与恢复界。
源文没有构造满足全部历史合同的共同非 Born 过程，
没有证明任意不连续解码器的障碍，也没有给实际字精确碰撞或统一取得速率。
本轮仅用其明确结论支持质量必须保留的稳定性分析。

<a id="section-13"></a>

## 13. 接回五模式、总命题与起源问题的剩余输入

项目 V37 的固定等距 $J_F:\mathbb{C}^2\to\mathbb{C}^5$ 满足 $J_F^\dagger J_F=I$。
每个正质量二元接口可接到同一编码；对数学酉门 $U$，

$$
\widetilde U=J_FUJ_F^\dagger+(I_5-J_FJ_F^\dagger)
$$

为酉矩阵，并满足 $\widetilde UJ_F=J_FU$。
证明是将编码空间及其正交补分块；前者执行 $U$，后者恒等。
本轮 $U_a$ 可以这样接入；带标签的完整图册还须保存每个接口质量和相干关系。
归一化由单位元期望或完整质量承担，不能凭名称把某一个原生模式指定成总归一化量。
原生制备、门菜单及成本仍须独立核对。[[8]](#bib-v37) [[5]](#bib-v52)

#### 定理 13.1（有限二元正关系的外代数闭合与条件重构）

在有限复内积空间、标准诱导外代数及明确正效果读出结构中：

1. 非零二元齐次复线性关系的零正残差选出纯态，归一图册为 $\mathbb{CP}^1\cong S^2$。
2. 目标重合振幅与完整二元外积残差构成等距分解；二元时恰为 $SU(2)$。
3. 全局纯态距离平方是全部局部球面弦差的精确质量加权和；
混态另有局部纯度缺额。
4. 结果与残差共同保质量，整体共同酉演化使残差按外平方酉传导。
5. 外乘与收缩给逐次数平方分解和精确递归，在完整分次空间产生 Pauli 表示。
6. 稀疏关系的全局误差受质量加权图谱隙控制；零支持及关系扰动须计入。
7. 一般归一复线性变换是射影条件变换；全部转移概率保持选出缩放酉子类。
8. 正残差可通过带成功质量的条件滤波下降，满足负二倍方差律。
9. 实际效果的 RC、全菜单非负归一和所需秩一密度，
推出正迹一密度表示；在纯态和秩一效果上给平方响应。

**证明。**

分别应用第 2–11 节的有限定理。每一条都保留其明列前件；
第 9 条的实际可测版本还需要共同实际切口及原核。

∎

| 研究直觉 | 本轮可证明的准确形式 |
| --- | --- |
| 二元关系提升三轴 | 非零二元正块给质量和 Bloch 球；纯态位于球面 |
| 结果与误差也酉 | 二元 $U_a$、高维 $\mathcal W_a$ 等距及 $\Lambda^2U$ 协变 |
| 关系继续递归 | 外乘–收缩的正交平方分解；相容坐标和内部方向保留 |
| 三轴局部拼成整体 | 完整误差恒等式；稀疏图另需支撑相容与正谱隙 |
| 归一化使误差下降 | 指定条件滤波后有方差下降律，同时记录成功质量 |
| 量子起源是换公理 | 复内积外代数、正效果关系与内部复合成为明确结构输入 |

本轮不是把三维态参数识别为物理三维空间，也没有推出现实 Hamiltonian、
实际费米统计或一个唯一的内部时钟。复线性载体、标准内积、整体如何分接口、
哪些效果实际可用、如何实现共同切口与 RC，以及经验概率标定，
是仍需由项目原生来源提供的部分。
“本体唯一”与把所有参照及记录放在同一整体相容；
它本身不替代这些可检验的代数和来源条件。

全文未执行数学程序、CAS、数值评估、候选枚举、Lean 或门搜索。
工具只用于公开固定来源阅读与身份审计、文稿编译和版式检查；
这些操作不充当纸面证明。

## 固定来源、已知结构与阅读范围

<a id="bib-head"></a>

**[1]** 
the-omega-institute/trureturing,
[固定提交 74d3fbdb768819e31f736<wbr>d1e2e5686e3f03f6a12](https://github.com/the-omega-institute/trureturing/commit/74d3fbdb768819e31f736d1e2e5686e3f03f6a12)，
2026-10-31 23:59:17 SGT。本轮仅一次成功的 live HEAD 获取。

<a id="bib-compare"></a>

**[2]** 
[v54 到 v55 固定比较](https://github.com/the-omega-institute/trureturing/compare/c7e66ea1741441b39a6f4c6239dbd20471c378cf...74d3fbdb768819e31f736d1e2e5686e3f03f6a12)。
完整 diff 与新旧完整 theory 树交叉核对；302 路径只分类，9 个 theory 变更中按本文范围阅读。

<a id="bib-v50"></a>

**[3]** 
[AURIC Recursive Three-Axis Atlas, Power Limits and K-bonacci V50](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_RECURSIVE_THREE_AXIS_ATLAS_POWER_LIMITS_AND_KBONACCI_V50.md)。
历史 v50.0 稿新入库；本轮核历史归属及相关定位，未重认证全文。

<a id="bib-v51"></a>

**[4]** 
[AURIC Constraint Recursion, Pure-State Duality and Endogenous Static History V51](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_CONSTRAINT_RECURSION_PURE_STATE_DUALITY_AND_ENDOGENOUS_STATIC_HISTORY_V51.md)。
历史稿新入库；第 8、10、11 节已有闭路相容、抽象谱隙误差及内生历史。

<a id="bib-v52"></a>

**[5]** 
[AURIC Pure-State Quotient Geometry, Quadratic Relation Generators and Lossless Recursion V52](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)。
历史稿新入库；核第 2、5、7 节保尺度图册、二次生成与纯态树递归及物理化边界。

<a id="bib-v44"></a>

**[6]** 
[AURIC Boundary Extension and Higher-Dimensional Relational Atlas V44](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_BOUNDARY_EXTENSION_AND_HIGHER_DIMENSIONAL_RELATIONAL_ATLAS_V44.md)。
本轮未改；复用图册、支撑比值闭路、全局正性及零边界。

<a id="bib-v41"></a>

**[7]** 
[AURIC Normalization, Units, Observer Origins and Quadratic Invariants V41](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_NORMALIZATION_UNITS_OBSERVER_ORIGINS_AND_QUADRATIC_INVARIANTS_V41.md)。
本轮未改；第 9.3–9.4 节已有分支质量乘积及质量恒定的缩放酉判据。

<a id="bib-v37"></a>

**[8]** 
[AURIC Binary Relations, Unitary Representation and Golden-Gate Universality V37](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)。
本轮未改；固定五模式编码与数学酉扩张。

<a id="bib-qiv"></a>

**[9]** 
[AURIC 原生全菜单的正性前件约减与有限菜单边界，续卷 IV](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md)。
本轮真正新卷，第 195–200 节；全文由来源核对席阅读，
主文核第 195–196、199–200 节及其必要边界。
旧 III151 的控制密度作为源定理复用，未重证全部上游控制。

<a id="bib-rro"></a>

**[10]** 
[Recursive Relational Observation: Fibonacci Native Terminal Certification](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)。
本轮真正追加第 44–48 节，连续阅读；条件前律、空未来、连续解码器及正质量范围均保留。

<a id="bib-lorentz"></a>

**[11]** 
F. Verstraete, J. Dehaene, B. De Moor,
*Local filtering operations on two qubits*,
Physical Review A 64, 010101(R) (2001),
[doi:10.1103/PhysRevA.64.010101](https://doi.org/10.1103/PhysRevA.64.010101)，
[arXiv:quant-ph/0011111](https://arxiv.org/abs/quant-ph/0011111)。
核原文开篇及定理 2 的 Lorentz/filtering 对应；
本文二元证明独立展开，不认证该文全部分类。

<a id="bib-clifford"></a>

**[12]** 
D. Lundholm, L. Svensson,
*Clifford algebra, geometric algebra, and applications*,
[作者公开修订稿，2016-06-07](https://www.math.lmu.de/~lundholm/clifford.pdf)，
[arXiv:0907.5356](https://arxiv.org/abs/0907.5356)。
核第 4.3 节外乘、收缩与 CAR，以及第 8.2 节 Clifford 表示接口；
本文给有限复内积版本的自足证明。

> **编者核读注（外部版本）**：Lundholm–Svensson 的机构公开 PDF 首页明列修订日 2016-06-07，本版实际核读其 §§4.3、8.2（印刷页 48–49、98–99）；arXiv:0907.5356 是同题条目，不能将不同版本默认为相同字节。滤波文献实际核读的是 arXiv:quant-ph/0011111v1 的开篇与定理 2（PDF 页 1–2）；该服务的 PDF 重生成版页眉保留 v1 的 2000-11-28 标识，但正文排版日期为 2024-11-26。原书目中的 PRA 64, 010101(R) (2001) 为期刊出版身份，两种日期不混同，也不据此认证论文全部分类。

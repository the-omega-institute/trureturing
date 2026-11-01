<a id="auric-v23"></a>

# 非周期单原型瓦片与 AURIC

**高维酉投影、三角心及递归变分**

**定义、定理与纸面证明**

**v23.0 · 2026 年 10 月 30 日 · Asia/Singapore**

> **转换说明（编者）。** 本文完整转写原作者提供的 v23.0 XeLaTeX 稿件；正文的快照计数、源码核对、文献结论、项目机器证明状态及研究推进均保留为原作者报告。本次转换不构成新的数学认证。字体、页眉、分页与目录排版由 Markdown 替代，数学宏展开为独立表达。各节陈述共享源稿编号，说明 2.3、8.3 计入；自动公式按源稿全局编号 (1)–(7)，含 `align` 中未单独设置标签的行，矩阵换行不另编号。图 1 的字符网格与符号替代另有明确编者说明，原图题和 TikZ 原文均保留。
<a id="sec-abstract"></a>

## 摘要

本文把“非周期瓦片是高维量子门结构的投影”推进为一个可核查的条件构造。已有 Hat 控制点重投影是
$x+Dx^\star$，其中 $D=\frac1{16}\bigl(\begin{smallmatrix}-11&3\sqrt{15}\\3\sqrt{15}&11\end{smallmatrix}\bigr)$。
本文给出其四维正交完成，并进一步构造单比特门 $M_D=(I-iD)/\sqrt2$，使真实 Hat 重投影恰为跨空间复编码后的实部读出。该门本身八阶，但在同一基底下另可主动调用其 $60^\circ$ 朝向共轭时，两者生成稠密的 $\mathrm{SU}(2)$；这是具有明确控制前件的单比特近似普适性。有限补丁还具有保留径向信息的归一化编码。格点窗口、类型和局部重构仍是独立数据；少振幅编码不能免费完成确定性的窗口判别。几何部分列出 Hat 全部十三个角点、边、角度与十一三角剖分，计算各种心的不同变分目标，并给出负重心系数的精确实例。关系部分在三角复形上放置 AURIC 五模式酉连接。正二次能量的 Schur 消元严格实现同一问题中的递归、变分和最优化。原生黄金门另外给出 $K^5$ 的并联投影和单位边权三角能隙 $\varphi^{-2}$。全文保留几何、编码、窗口和量子读出的不同前件，不将条件表示定理当作全部量子公理的起源证明。

**结果身份与验证方式。**
Hat/Spectre 的全局非周期定理和四维模型集表示作为原作者文献输入。
本稿给出相应矩阵、几何、连接与变分联结的自足纸面证明，不运行数学数值程序、CAS、门枚举、瓦片生成或 Lean。
原项目报告的机器证明状态不等于本轮重新执行；经典线性代数与离散几何结果不主张原创优先权。
图形仅按文中的精确坐标排版，不能替代证明。

## 目录

1. [研究快照、对象及最先要澄清的酉性](#sec-1)
2. [Hat 的真实四维重投影与一个精确酉完成](#sec-2)
3. [单原型瓦片、非周期性与全部 Hat 角点](#sec-3)
4. [各种“心”是不同关系的最优解](#sec-4)
5. [AURIC 金字塔：空间坐标、五模式与三读出](#sec-5)
6. [在三角复形上定义相容的 AURIC 关系](#sec-6)
7. [递归、最优化与变分：一个严格闭合的模型](#sec-7)
8. [黄金门在三角关系中的两个精确结果](#sec-8)
9. [三角几何怎样确定权重，以及对角线怎样被变分选择](#sec-9)
10. [递归增长、有限门循环与项目的完整返回坐标](#sec-10)
11. [理论的闭合部分与仍需证明的接口](#sec-11)

[附录 A：来源、定义与证明范围的核查索引](#sec-a)

[文献与固定项目来源](#sec-bibliography)

<a id="sec-1"></a>

## 1. 研究快照、对象及最先要澄清的酉性

项目研究分支 `dev` 本轮固定于

`ae864ac4ae3d01dc2e589a21fde123c4d5ca92f7`。

该提交于 2026-10-30 05:14:35 UTC，即新加坡 13:14:35，合并 PR #24038，主题是加性斜积中周期提升轨道的坐标。相对 v22 快照有 572 个提交；完整理论子树由 1022 项变为 1034 项，26 条路径变化，其中新增 12、修改 14。全仓递归树与比较列表触及接口截断，故不把列表长度冒充全仓变更总数。定向核对了 28 个当前源码 blob。v19–v22 先前研究稿新收入仓库属于转录，不是其结论的独立验证。（[1](#ref-snapshot)）

本稿实际衔接四条项目线索：金字塔的五点凸几何与概率纤维；有锚边相位和闭路关系；周期基底与完整提升状态的返回差别；量子重构续卷 II 对 Born 条件及其未解决前件的明确区分。（[12](#ref-pyramid)、[16](#ref-phaseclass)、[17](#ref-skew)、[18](#ref-continuation)）
前稿 v22 的相对门 $V^\dagger U$ 和观察商在这里成为边上的关系算符，而几何本身并不预先决定这些算符。（[15](#ref-v22)）

<a id="statement-1-1"></a>

#### 定义 1.1（酉、实正交与投影）

复线性 $U:\mathbb{C}^d\to\mathbb{C}^d$ 满足 $U^\dagger U=I$ 称为酉。实线性 $R:\mathbb{R}^d\to\mathbb{R}^d$ 满足 $R^TR=I$ 称为正交。指定子空间后的正交投影为 $\Pi=\Pi^\dagger=\Pi^2$。三者的定义涉及不同载体，不能省略载体后只用“旋转、镜像、不缩放”识别。

酉保持的是完整振幅内积、范数和相对转移概率，并不要求每个读出分量的大小不变。实平面上的反射若写在一个复坐标 $z=x+iy$ 上，是 $z\mapsto e^{i\theta}\bar z$，通常反线性；若把两个实坐标分别装入 $\mathbb{C}^2$ 的两个振幅，实正交反射矩阵又确实是复酉。这是不同编码。Bloch 球上一般的空间镜像也不能不加区分地当作量子比特酉共轭。

<a id="statement-1-2"></a>

#### 命题 1.2（总体保范数与局部收缩）

若 $J_{\mathrm{in}},J_{\mathrm{out}}$ 为等距嵌入，$U$ 酉，则
$A=J_{\mathrm{out}}^\dagger UJ_{\mathrm{in}}$ 为收缩，且

$$
\left\lVert \psi\right\rVert ^2-\left\lVert A\psi\right\rVert ^2
 =\left\lVert (I-J_{\mathrm{out}}J_{\mathrm{out}}^\dagger)UJ_{\mathrm{in}}\psi\right\rVert ^2.
$$

**证明。**

将 $UJ_{\mathrm{in}}\psi$ 正交分解为输出子空间内外两部分，再用勾股等式与等距性。

∎

因此一个切面的长度、振幅或有效权重可以变小，剩余范数保存在被该接口省略的分量中。反过来，单有一个收缩或几何缩短也不能确定其唯一的高维酉来源。

<a id="sec-2"></a>

## 2. Hat 的真实四维重投影与一个精确酉完成

<a id="sec-2-1"></a>

### 2.1. 已有文献提供什么

Smith、Myers、Kaplan 与 Goodman-Strauss 的 Hat 和 Spectre 给出了单原型强制非周期铺砌的具体对象。（[2](#ref-hat)、[3](#ref-spectre)）
后续研究将 Hat/Spectre 的长程结构联系到四维格点、二维内部窗口和重投影；2026 年综述 Theorem 3.1 对 Hat 写出了下述精确矩阵。（[5](#ref-diffraction)、[6](#ref-survey)）
Spectre 最新 arXiv v3（2026-10-07）的 Theorem 9 与 Corollary 11 则谨慎使用五色模型集的全密度子集及其重投影。原模型与重投影之间一般是拓扑共轭，不能一概说成由有限局部完全互相恢复。（[8](#ref-spectreorder)）

<a id="statement-2-1"></a>

#### 定义 2.1（有类型的截取与投影数据）

取格 $\mathcal L\subset\mathbb{R}^2_{\mathrm{phys}}\oplus\mathbb{R}^2_{\mathrm{int}}$，格点写作 $q=(x,x^\star)$；取类型窗口 $W_i$ 以及窗口边界的取舍规则。由 $x^\star\in W_i$ 选出的点再通过

$$
\pi_D(q)=x+Dx^\star
$$

成为类型 $i$ 的控制点。重构瓦片还需指定控制点类型与邻域的对应。这里 $x^\star$ 是格点的内部坐标，不是量子共轭振幅。

对文献选定的 Hat/CAP 控制点与坐标约定，

<a id="eq-d"></a>

$$
\Lambda_i^{\mathrm{Hat}}
 =\{x+Dx^\star:x\in\Lambda_i^{\mathrm{CAP}}\},\qquad
 D=\frac1{16}\begin{pmatrix}-11&3\sqrt{15}\\3\sqrt{15}&11\end{pmatrix}.
\tag{1}
$$

CAP 表示保留 24 个形状／朝向类型。特殊窗口相位可能涉及边界点的零密度差异，故不可把所有情形都无条件写成同一闭窗的精确等号。上述 Hat 控制点特意选在反手性 Hat 上，颜色决定邻域；它们不是每片 Hat 的十三个角点。第 [3](#sec-3) 节角点坐标的尺子也与此控制点约定不同。（[5](#ref-diffraction)、[6](#ref-survey)、[7](#ref-hatdynamics)）

<a id="statement-2-2"></a>

#### 定理 2.2（Hat 重投影的正交完成）

令 $D$ 如 [(1)](#eq-d)，并定义

$$
U_D=\frac1{\sqrt2}\begin{pmatrix}I_2&D\\I_2&-D\end{pmatrix}.
$$

则 $D^T=D$、$D^2=I_2$、$\det D=-1$，且

<a id="eq-2"></a>

$$
\begin{aligned}
 U_D&\in O(4),&
 U_D&=(H_2\otimes I_2)\operatorname{diag}(I_2,D),\end{aligned}
\tag{2}
$$

<a id="eq-completion"></a>

$$
\begin{aligned}
 U_D(x,x^\star)
 &=\frac1{\sqrt2}\bigl(x+Dx^\star,\ x-Dx^\star\bigr),&
 H_2&=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.

\end{aligned}
\tag{3}
$$

将四个实坐标分别作为四个复振幅后，同一矩阵属于 $\operatorname{U}(4)$。其阶恰为八，且

$$
\operatorname{spec}(U_D)=\{1,-1,e^{i\pi/4},e^{-i\pi/4}\}.
$$

**证明。**

$121+(3\sqrt{15})^2=256$，交叉项为零，直接得 $D^2=I$；行列式为 $-256/256=-1$。分块相乘得
$U_DU_D^T=\frac12\operatorname{diag}(2I_2,2I_2)=I_4$，另一个乘积同理。右侧因子分解直接成立。
在 $D$ 的 $+1$ 本征方向对应的两个副本上，$U_D$ 限制为 $H_2$，谱为 $\pm1$；在 $-1$ 本征方向上限制为
$2^{-1/2}\bigl(\begin{smallmatrix}1&-1\\1&1\end{smallmatrix}\bigr)$，谱为 $e^{\pm i\pi/4}$。含原始八次单位根而全部本征值八次方为一，故阶恰八。实矩阵的复化仍满足 $U_D^\dagger U_D=I$。

∎

完整范数守恒具体为

$$
\left\lVert x+Dx^\star\right\rVert ^2+\left\lVert x-Dx^\star\right\rVert ^2
 =2\bigl(\left\lVert x\right\rVert ^2+\left\lVert x^\star\right\rVert ^2\bigr).
$$

Hat 可见坐标是前两分量再乘固定标尺 $\sqrt2$；隐藏的互补分量使信息没有因取二维切面而在完整线性变换中消失。这是本文对高维投影直觉最直接的肯定性结果。

<a id="statement-2-3"></a>

#### 说明 2.3（几何 $\mathbb{C}^2$ 与四模式 $\mathbb{C}^4$）

原几何也可把两个实平面各记成一个复数，从而写 $\mathbb{R}^4\simeq\mathbb{C}^2$。但是实反射 $D$ 满足 $DJ=-JD$，其中 $J=\bigl(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\bigr)$。
所以 $U_D$ 不与 $\operatorname{diag}(J,J)$ 对易，不是该天然 $\mathbb{C}^2$ 编码上的复线性门。更强地，$\det_{\mathbb{R}}U_D=-1$，而任何可逆复线性映射的实行列式为 $\left|\det_{\mathbb{C}}\right| ^2>0$，故它在任何复结构下都不能直接成为二维复线性门。定理 [2.2](#statement-2-2) 的量子实现使用另行声明的四振幅复化。下面通过换一种互补通道，得到真正的二维复酉完成。

<a id="statement-2-4"></a>

#### 定理 2.4（真实 Hat 重投影的二维复酉表示）

将四个实坐标跨物理／内部空间配对为
$z=x+i x^\star\in\mathbb{C}^2$，定义

$$
M_D=\frac{I_2-iD}{\sqrt2}=e^{-i\pi D/4}\in\mathrm{SU}(2).
$$

则

$$
\boxed{\operatorname{Re}\bigl(M_D(x+i x^\star)\bigr)
 =\frac{x+Dx^\star}{\sqrt2}.}
$$

其实四维表示为

$$
W_D=\frac1{\sqrt2}\begin{pmatrix}I_2&D\\-D&I_2\end{pmatrix}\in SO(4),
$$

并有 $M_D^4=-I_2$、$M_D^8=I_2$。

**证明。**

$D=D^\dagger$、$D^2=I$ 给
$M_D^\dagger M_D=(I+iD)(I-iD)/2=I$。
$D$ 的本征值为 $+1,-1$，故 $M_D$ 的谱为 $e^{-i\pi/4},e^{i\pi/4}$，行列式为一，指数式及幂式随即成立。
直接展开
$M_D(x+i x^\star)=2^{-1/2}[(x+Dx^\star)+i(x^\star-Dx)]$
给实部和实矩阵表示。

∎

这是一条更直接的单量子比特门矩阵接口，但复结构是明确指定的跨空间配对；实部也不是 Born 概率。$U_D$ 与 $W_D$ 具有同一个可见前两行而不同的互补通道，说明可见投影并不唯一确定本体的可逆完成。
对非零坐标可先归一化为 $z/\left\lVert z\right\rVert$，此时还须保留标尺及相位参考，才可恢复原来的 Hat 坐标。仅有单比特射线与标尺不够：$z$ 与 $iz$ 范数、射线相同，但输出实部一般不同。下述额外参考模式给出一种明确解决方式。

<a id="statement-2-5"></a>

#### 命题 2.5（重投影没有在整个格上保持单射）

文献的 CAP 格基提升 $\widetilde u_j=(u_j,u_j^\star)$ 与 Hat 返回格基 $v_1,v_2$ 满足

$$
\pi_D(\widetilde u_1)=3v_1-v_2,\quad
 \pi_D(\widetilde u_2)=v_1,\quad
 \pi_D(\widetilde u_3)=v_1+2v_2,\quad
 \pi_D(\widetilde u_4)=v_2.
$$

因此其格核是秩二群，由
$\widetilde u_1-3\widetilde u_2+\widetilde u_4$ 和
$\widetilde u_3-\widetilde u_2-2\widetilde u_4$ 生成。

**证明。**

系数 $(a,b,c,d)\in\mathbb{Z}^4$ 在核内当且仅当 $3a+b+c=0$、$-a+2c+d=0$。
解为 $(a,-3a-c,c,a-2c)$，恰为所列两向量的整数线性组合；独立性由格基保证。

∎

这一计算使用原论文 §3.2 的返回向量映射。（[5](#ref-diffraction)）
它说明格点索引、窗口和类型不能被裸二维位置替代；同时也不否定带窗口、类型及邻域的合法控制点仍能局部重构 Hat 铺砌。

<a id="sec-2-2"></a>

### 2.2. 接到五模式：可实现的编码与窗口障碍

<a id="statement-2-6"></a>

#### 定理 2.6（有限补丁的归一化五模式编码）

设 $Q\subset\mathbb{R}^4$ 非空有限，$R>\max_{q\in Q}\left\lVert q\right\rVert$，在开球 $\left\lVert q\right\rVert <R$ 上定义

$$
\Psi_R(q)=\left(\frac qR,\sqrt{1-\frac{\left\lVert q\right\rVert ^2}{R^2}}\right)\in\mathbb{R}^5\subset\mathbb{C}^5,
 \qquad \widehat U_D=U_D\oplus1 .
$$

则 $\left\lVert \Psi_R(q)\right\rVert =1$、该编码单射，且

$$
\widehat U_D\Psi_R(q)=\Psi_R(U_Dq).
$$

其前两个输出振幅等于 $\pi_D(q)/(\sqrt2R)$。

**证明。**

范数式由定义给出；前四坐标恢复 $q$，故单射。正交性使 $\left\lVert U_Dq\right\rVert =\left\lVert q\right\rVert$，所以第五分量保持不变，前四分量线性输运，再用 [(3)](#eq-completion)。

∎

同一个门处理整个有限补丁，径向信息也未被归一化抹去。不过有符号坐标位于振幅中，计算基概率只给平方；恢复符号需要相位参考及相干读出。整个无界铺砌没有一个有限 $R$ 满足该编码条件；无限位置寄存器或额外尺度、地址记录是不同模型。

定理 [2.4](#statement-2-4) 还允许更紧的三复模式编码

$$
\widetilde\Psi_R(q)=
 \left(\frac{x+i x^\star}{R},
       \sqrt{1-\frac{\left\lVert q\right\rVert ^2}{R^2}}\right)\in\mathbb{C}^3.
$$

$M_D\oplus1$ 使前两复振幅的实部给 $\pi_D(q)/(\sqrt2R)$，第三分量不变，证明与定理 [2.6](#statement-2-6) 相同。
它可以放入 AURIC 五模式中的三个模式，剩余两个模式置零；这种嵌入仍不证明原生 $K$ 能执行该门。

<a id="statement-2-7"></a>

#### 命题 2.7（参考模式上的实际期望读出）

在 $\widetilde\Psi_R(q)$ 中记第三个参考振幅为 $r>0$，参考模式为 $\lvert a\rangle$。经过 $M_D\oplus1$ 后，设前两振幅为 $w_1,w_2$。
定义 Hermitian 观察量
$X_j=\lvert j\rangle \langle a\rvert +\lvert a\rangle \langle j\rvert$，$j=1,2$，则

$$
p_a=r^2,\qquad
 (\pi_D(q))_j=\frac{R}{\sqrt{2p_a}}\,\langle X_j\rangle.
$$

故在具备同源重复制备及这些相干观察量的接口时，有限补丁的 Hat 坐标可由 Born 期望恢复。

**证明。**

$\langle X_j\rangle=2r\,\operatorname{Re}w_j$，而定理 [2.4](#statement-2-4) 给
$\operatorname{Re}w_j=(\pi_D(q))_j/(\sqrt2R)$，代入即可。
参考振幅严格正使分母非零，也固定了前两模式相对于参考的相位。此处的 $j=1,2$ 是三模式编码索引，不是前文的几何角点编号。

∎

式中是统计期望，不是一次测量同时精确读出全部坐标。正实参考分量使该编码在射线意义下也单射；单独两个振幅没有这项性质。

<a id="statement-2-8"></a>

#### 命题 2.8（少振幅编码的确定性窗口障碍）

若 $0\le E\le I$、$\psi,\phi$ 为单位态且
$\langle\psi,E\psi\rangle=1$、$\langle\phi,E\phi\rangle=0$，则 $\langle\psi,\phi\rangle=0$。
因此对跨窗口边界的非正交编码态，不能用同一个效果确定性地读出接受／拒绝。

**证明。**

由正性，$(I-E)^{1/2}\psi=0$、$E^{1/2}\phi=0$，故 $E\psi=\psi$、$E\phi=0$，内积为
$\langle E\psi,\phi\rangle=\langle\psi,E\phi\rangle=0$。
对有限补丁编码还能直接量化：置 $M=\max_{q\in Q}\left\lVert q\right\rVert$，若 $R>\sqrt2M$，则任意 $q,r\in Q$ 满足

$$
\langle\Psi_R(q),\Psi_R(r)\rangle
 \ge-\frac{M^2}{R^2}+1-\frac{M^2}{R^2}>0.
$$

因此只要补丁同时包含接受点与拒绝点，就无法确定性二分。此论证不假设四维格点可以任意接近。

∎

若改用正交位置基 $\{\lvert q\rangle \}$，窗口投影可以定义成
$\Pi_W=\sum_{q:q^\star\in W}\lvert q\rangle \langle q\rvert$，完整记录等距映射为

$$
\psi\longmapsto\lvert \mathrm{in}\rangle \Pi_W\psi+
 \lvert \mathrm{out}\rangle (I-\Pi_W)\psi.
$$

这在另一个位置 Hilbert 空间中确实保范数，但不是前述四／五振幅编码上免费的额外能力。文献给出的是几何表示；本文添加并注明了量子编码与读出接口。

<a id="sec-3"></a>

## 3. 单原型瓦片、非周期性与全部 Hat 角点

<a id="statement-3-1"></a>

#### 定义 3.1（单原型非周期铺砌）

在指定的允许等距群中，原型 $T$ 的全平面铺砌是具有不交内部且并集为 $\mathbb{R}^2$ 的刚性副本族。若至少存在一个铺砌，且每个合法铺砌都没有非零平移周期，则 $T$ 是该规则下的非周期单原型瓦片（aperiodic monotile）。

一个有限补丁看起来不重复不足以满足这个定义。Hat 的全平面铺砌必须混用两种手性；$\mathrm{Tile}(1,1)$ 若禁止混用镜像则非周期，允许镜像时存在周期铺砌；严格 Spectre 通过边界改造排除混合手性，允许反射也只产生同手性非周期铺砌。（[2](#ref-hat)、[3](#ref-spectre)）
严格 Spectre 的边界可以弯曲；保留端点而用弦替代曲线可能丢失匹配限制。本文的精确有限直线三角剖分选择 Hat，不把它直接套到任意曲边 Spectre。

<a id="sec-3-1"></a>

### 3.1. 十三角点、十三条原生边与十一三角剖分

取精确三角格基

$$
e_1=(1,0),\qquad e_2=(1/2,\sqrt3/2),\qquad
 (u,v)_{\mathrm h}=ue_1+ve_2 .
$$

作者公开绘图源码在固定版本 `4bb9d01999e4e84accc2a78d0fa279ef20b47263` 给出下表整数格标签；本文用精确的 $\sqrt3/2$ 代替仅供画图的小数。（[4](#ref-hatcode)）
$d_i=p_{i+1}-p_i$，下标模十三。

| $i$ | $p_i$ 的格坐标 | $d_i$ 的格坐标 | $\left\lVert d_i\right\rVert$ | 内角 |
| --- | --- | --- | --- | --- |
| 0 | (0,0) | (-1,-1) | $\sqrt3$ | $240^\circ$ |
| 1 | (-1,-1) | (1,-1) | 1 | $90^\circ$ |
| 2 | (0,-2) | (2,0) | 2 | $120^\circ$ |
| 3 | (2,-2) | (0,1) | 1 | $120^\circ$ |
| 4 | (2,-1) | (2,-1) | $\sqrt3$ | $270^\circ$ |
| 5 | (4,-2) | (1,1) | $\sqrt3$ | $120^\circ$ |
| 6 | (5,-1) | (-1,1) | 1 | $90^\circ$ |
| 7 | (4,0) | (-1,0) | 1 | $120^\circ$ |
| 8 | (3,0) | (-1,2) | $\sqrt3$ | $270^\circ$ |
| 9 | (2,2) | (-2,1) | $\sqrt3$ | $120^\circ$ |
| 10 | (0,3) | (0,-1) | 1 | $90^\circ$ |
| 11 | (0,2) | (-1,0) | 1 | $240^\circ$ |
| 12 | (-1,2) | (1,-2) | $\sqrt3$ | $90^\circ$ |

<a id="statement-3-2"></a>

#### 命题 3.2（边界与剖分的精确数据）

该 Hat 的周长 $L=8+6\sqrt3$，面积 $A=8\sqrt3$。以下三角形无重叠地剖分该多边形：

$$
012,\ 023,\ 034,\ 456,\ 046,\ 678,\ 068,\ 089,\  (9,10,11),\ (0,9,11),\ (0,11,12).
$$

这些三角形的两倍有向格面积依次为
$2,4,2,3,3,1,3,6,2,4,2$。

**证明。**

格向量 $(a,b)$ 的平方长度为 $a^2+ab+b^2$，逐边得表内长度；边方向为 $30^\circ$ 的整数倍，给出所列角度。鞋带交叉和为
$0+2+4+2+0+6+4+0+6+6+0+2+0=32$，乘格基行列式 $\sqrt3/2$ 再除二即得面积；边长求和得周长。
剖分按耳序 $1,2,3,5,4,7,6,8,10,9$ 删除，最后剩 $0,11,12$。各耳的边由表中坐标给出的半平面包含在当前多边形内，其内部无剩余顶点；第三侧为内部弦。依次所得三角形正是上述列表，各行列式正且总和为 32。耳删除使内部分离且完整覆盖，而面积和提供独立一致性检查。

∎

<a id="fig-hat"></a>

> **图形转写说明（编者）。** 下图为依据原稿坐标放置的等宽字符网格近似图，不是精确比例的 TikZ 执行结果。横向位置对应 $x=u+v/2$，纵向位置对应 $y=\sqrt3v/2$；网格列与行分别等分这两个坐标方向，字符自身的宽高影响视觉比例。`o` 标记十三个原生角点，粗边以 `=`、`/`、`\` 表示，内部线段表示十条对角线。原稿蓝色底改为留白，橙色三角形 $046$ 改用 `:` 标记，红色面积重心改用 `@ C_area` 标记；这些仅是编者的符号替代。原始精确坐标表见上，原图题与完整 TikZ 源码保留在下方；GitHub 不执行该源码。

```text

                                        10

                                         o\
                                        /  \\\
                                       /      \\\
                                      /          \\\
                              11     /              \\\
                                    /                  \\\
                 12    o===========o----------------------\o 9
                       \          .                    ... \
                       \         .                  ...    \
                       \        .                ...       \
                       \       .              ...          \
                       \      .            ...             \
                       \     .          ...                \
                       \    .        ...                   \
                       \   .      ...                      \
                       \  .    ...                         \
                       \ .  ...                        8   \
                  0    \....                               \            7
                      /o++++-------------@-----------------o===========o
                   ///. .............   C_area               ...        \
                ///  .   .  ...::::::.........                  ...      \
             ///    .     .    ...::::::::::::.........            ...    \
          ///      .       .      ...::4:::::::::::::::.........      ...  \
       ///        .         .        ...::::::::::::::::::::::::............\
1    o/          .           .          .o\------------------------------+++/o 6
      \         .             .         /  \\\                           ///
       \       .               .       /      \\\                     ///
        \     .                 .     /          \\\               ///
         \   .                   .   /              \\\         ///
          \ .                     . /                  \\\   ///
           o=======================o                      \o/

         2                         3                       5

          ^ e2
         /
   o-----------> e1
```

**图 1：** 精确 Hat 角点与一组十一三角剖分。橙色为三角形 $046$，其外心和垂心均在整个 Hat 外；红点是区域面积重心。图按精确坐标排版。

图中内部线段：$02,03,04,46,06,68,08,09,(9,11),(0,11)$；对应的十一三角形完整列表见命题 [3.2](#statement-3-2)。$e_1,e_2$ 的箭头表示原稿的三角格方向。

**原始 TikZ 图（完整源文披露；代码不执行）。**

```latex
\begin{figure}[htbp]
\centering
\begin{tikzpicture}[scale=1.15,line join=round]
\coordinate (p0) at (0,0);
\coordinate (p1) at (-1.5,{-sqrt(3)/2});
\coordinate (p2) at (-1,{-sqrt(3)});
\coordinate (p3) at (1,{-sqrt(3)});
\coordinate (p4) at (1.5,{-sqrt(3)/2});
\coordinate (p5) at (3,{-sqrt(3)});
\coordinate (p6) at (4.5,{-sqrt(3)/2});
\coordinate (p7) at (4,0);
\coordinate (p8) at (3,0);
\coordinate (p9) at (3,{sqrt(3)});
\coordinate (p10) at (1.5,{3*sqrt(3)/2});
\coordinate (p11) at (1,{sqrt(3)});
\coordinate (p12) at (0,{sqrt(3)});
\fill[blue!7] (p0)--(p1)--(p2)--(p3)--(p4)--(p5)--(p6)--(p7)--(p8)--(p9)--(p10)--(p11)--(p12)--cycle;
\fill[orange!22] (p0)--(p4)--(p6)--cycle;
\foreach \a/\b in {0/2,0/3,0/4,4/6,0/6,6/8,0/8,0/9,9/11,0/11}
 \draw[blue!50!black,thin] (p\a)--(p\b);
\draw[very thick] (p0)--(p1)--(p2)--(p3)--(p4)--(p5)--(p6)--(p7)--(p8)--(p9)--(p10)--(p11)--(p12)--cycle;
\foreach \i in {0,...,12}\fill (p\i) circle (1.6pt);
\node[above left] at (p0) {$0$}; \node[left] at (p1) {$1$};
\node[below left] at (p2) {$2$}; \node[below] at (p3) {$3$};
\node[above] at (p4) {$4$}; \node[below] at (p5) {$5$};
\node[right] at (p6) {$6$}; \node[above right] at (p7) {$7$};
\node[above left] at (p8) {$8$}; \node[right] at (p9) {$9$};
\node[above] at (p10) {$10$}; \node[above left] at (p11) {$11$};
\node[left] at (p12) {$12$};
\fill[red!70!black] (1.5,0) circle (2pt);
\node[below right,text=red!70!black] at (1.5,0) {$C_{\rm area}$};
\draw[-{Stealth},gray] (-1.8,-2.2)--(-.8,-2.2) node[right] {$e_1$};
\draw[-{Stealth},gray] (-1.8,-2.2)--(-1.3,{-2.2+sqrt(3)/2}) node[left] {$e_2$};
\end{tikzpicture}
\caption{精确 Hat 角点与一组十一三角剖分。橙色为三角形 $046$，其外心和垂心均在整个 Hat 外；红点是区域面积重心。图按精确坐标排版。}
\end{figure}
```

长边 $p_2p_3$ 的格中点 $(1,-2)$ 可加入一个 $180^\circ$ 标记点，使边界成为十四段：八条单位段、六条 $\sqrt3$ 段。这不增加原生拐角。整个铺砌的复形顶点还可能来自相邻瓦片的边界接点，应先统一细分这些接点，再剖分每块瓦片以消除 T 形接合。
Hat 的八个标准 kite 又可各沿对称轴分成两个 $30^\circ$–$60^\circ$–$90^\circ$ 三角形，得到十六三角剖分；数目不同来自明确的细分规则，不是新的本体原子数。（[2](#ref-hat)）

<a id="statement-3-3"></a>

#### 定理 3.3（被迫层级的非周期判据）

假设铺砌自身唯一决定一个平移协变的逐层超瓦片划分。每层超瓦片有界、内部两两不交，且某些超瓦片所含圆盘半径随层级趋于无穷。则该铺砌无非零平移周期。

**证明。**

若 $t\ne0$ 是周期，唯一性与平移协变性使 $t$ 置换每一层超瓦片。
取含半径大于 $\left\lVert t\right\rVert$ 圆盘的超瓦片 $C$，则 $C$ 与 $C+t$ 内部相交，故它们必须是同一块。于是 $C=C+t$，迭代平移与有界性矛盾。

∎

普通周期方格也可以人为选择原点后划成越来越大的二进方块；其层级并非由裸图案唯一决定，所以不满足前件。保留三角细分却遗忘父瓦片、边界类型或所有权，也可能增加对称性；有色非周期方格遗忘颜色就成为周期方格。非周期性不是任意观察商都保持的不变量。

<a id="sec-4"></a>

## 4. 各种“心”是不同关系的最优解

<a id="statement-4-1"></a>

#### 定义 4.1（三角心）

对非退化三角形 $A,B,C$，置 $a=\left\lVert B-C\right\rVert$、$b=\left\lVert C-A\right\rVert$、$c=\left\lVert A-B\right\rVert$、面积 $\Delta$。所有优化变量限制在三角形的仿射平面中。定义

$$
G=\frac{A+B+C}{3},\qquad I=\frac{aA+bB+cC}{a+b+c},
$$

外心 $O$ 为平面内等距于三顶点的点，垂心 $H=A+B+C-2O$，九点心 $N=(O+H)/2$。以下 $d(x,AB)$ 表示到边 $AB$ 所在直线的垂距。

<a id="statement-4-2"></a>

#### 定理 4.2（四种心的明确变分问题）

下列解均唯一：

$$
\begin{aligned}

 G&=\arg\min_x\sum_{P=A,B,C}\left\lVert x-P\right\rVert ^2,\\
 I&=\arg\max_{x\in\triangle ABC}\min\{d(x,AB),d(x,BC),d(x,CA)\},\\
 O&=\arg\min_x\sum_{\{P,Q\}\subset\{A,B,C\}}
       \bigl(\left\lVert x-P\right\rVert ^2-\left\lVert x-Q\right\rVert ^2\bigr)^2,\\
 H&=\arg\min_x\sum_{\mathrm{cyc}}
       \bigl((x-A)\cdot(B-C)\bigr)^2.

\end{aligned}
$$

外心、垂心两式的最小值为零；内心式的最大值为 $r=2\Delta/(a+b+c)$。

**证明。**

第一式配方为常数加 $3\left\lVert x-G\right\rVert ^2$。若三角形内一点到对边距离为 $d_a,d_b,d_c$，则 $2\Delta=ad_a+bd_b+cd_c$，故最小距离不超过 $r$。内心的正重心系数使三个子三角面积分别为 $a,b,c$ 的比例，故三距离均为 $r$；两条独立内偏移线保证唯一性。
平方距离差为 $x$ 的仿射函数，两条独立边使其残差平方和在平面上严格凸，垂直平分线交点给零残差。
最后，$O$ 等距于 $B,C$ 意味着 $(B+C-2O)\cdot(B-C)=0$，故 $H-A$ 垂直 $BC$，其余循环同理。边方向张成平面，残差平方和严格凸，零点唯一。

∎

<a id="statement-4-3"></a>

#### 命题 4.3（协变、测度与剖分独立性）

上述五种心对欧氏等距与相似变换协变；重心还对任意仿射映射协变。区域 $P$ 的面积重心满足

$$
C_P=\frac{\sum_{T\in\mathcal T}\operatorname{Area}(T)G_T}{\operatorname{Area}(P)}
$$

并与三角剖分 $\mathcal T$ 无关。Hat 的面积重心和均匀角点均值分别为

$$
C_{\mathrm{area}}=(3/2,0)_{\mathrm h},\qquad
 C_{\mathrm{vertices}}=(20/13,0)_{\mathrm h}.
$$

**证明。**

相似变换保持角度、距离比和垂直关系，直接保持各定义；$G$ 的仿射公式给更强结论。
每个三角形满足 $\int_Tx\,dA=\operatorname{Area}(T)G_T$，积分可加性给剖分独立。
Hat 格坐标的顶点和为 $(20,0)$。鞋带交叉和为 32，而重心公式分子的两坐标分别为 144、0，因此区域重心为 $(144,0)/(3\cdot32)$。两种均值相差 $(1/26,0)_{\mathrm h}$。

∎

不加面积权重的三角心平均一般随剖分变化。一个非凸多边形也没有自动给定的“外心”或“垂心”，必须先说明是某个三角形的心、拟合圆的中心，还是另一种整体优化。

<a id="statement-4-4"></a>

#### 命题 4.4（实际 Hat 三角形的有符号中心）

取剖分内的 $A=p_0$、$B=p_4$、$C=p_6$。则

$$
\begin{aligned}

 O&=(1,4)_{\mathrm h}=5A-7B+3C,\\
 H&=(5,-10)_{\mathrm h}=-9A+15B-5C,\\
 G&=(7/3,-2/3)_{\mathrm h},\\
 I&=\frac{3A+\sqrt{21}\,B+\sqrt3\,C}{3+\sqrt{21}+\sqrt3}.

\end{aligned}
$$

$O,H$ 均在整个 Hat 外；该 Hat 十三个角点不共圆。

**证明。**

直角坐标中 $B=(3/2,-\sqrt3/2)$、$C=(9/2,-\sqrt3/2)$。
$O=(x,y)$ 的等距条件给 $3x-\sqrt3y=3$ 和 $9x-\sqrt3y=21$，故 $O=(3,2\sqrt3)$，即所列格坐标；其仿射系数为 $5,-7,3$。
代入 $H=A+B+C-2O$ 及其他定义得到全部式子。
Hat 格坐标第二分量介于 $-2$ 与 $3$，而两心为 $4,-10$，故在外部。
这三个点到 $O$ 的平方距离均为 21，而 $p_1$ 到 $O$ 的平方距离为 39，故全十三点不共圆。

∎

<a id="statement-4-5"></a>

#### 定理 4.5（投影与中心一般不交换）

仿射映射总与重心交换；正交投影一般不与外心、内心、垂心交换。
若其在三角形平面上的限制为非退化相似变换，则这些心均交换。

**证明。**

重心及相似情形已证。反例取原平面三点 $(0,0),(2,0),(1,1)$，外心为 $(1,0)$。
先等距嵌入 $\mathbb{R}^3$ 为 $(x,y)\mapsto(x,y/2,\sqrt3y/2)$，再投影到前两坐标。新三角形为 $(0,0),(2,0),(1,1/2)$，其外心 $(1,-3/4)$ 不等于原外心的投影 $(1,0)$。
原垂心为 $(1,1)$，新垂心由 $A+B+C-2O$ 得 $(1,2)$，也不交换。
原内心纵坐标为 $1/(1+\sqrt2)$，投影后为 $1/[2(1+\sqrt2)]$；新内心纵坐标为 $1/(2+\sqrt5)$，两者不等。

∎

因而高维图形的心、该心的投影、投影图形重新计算的心是三个明确对象。对任意投影都把它们视为同一个“最优点”会丢掉度量与目标函数。

<a id="sec-5"></a>

## 5. AURIC 金字塔：空间坐标、五模式与三读出

<a id="statement-5-1"></a>

#### 定义 5.1（五模式与占位凸体）

取 $H_A=\mathbb{C}^5$，带正交基 $\lvert 0\rangle ,\lvert 1\rangle ,\lvert 2\rangle ,\lvert 3\rangle ,\lvert 13\rangle$。几何占位点为

$$
f_0=(0,0,0),\ f_1=(1,0,0),\ f_2=(0,0,1),\  f_3=(0,1,0),\ f_{13}=(1,1,0).
$$

这对应项目旧标签 $(0,2,3,5,25)$ 的重标记 $(0,1,2,3,13)$。几何点 $f_s$ 与 Hilbert 基 $\lvert s\rangle$ 是不同对象。

项目的三均值体为

$$
\mathcal P_A=\operatorname{conv}\{f_s\}
 =\{X,Y,Z\ge0:X+Z\le1,\ Y+Z\le1\}.
$$

给定 $(X,Y,Z)$，完整五模式律仍有一个纤维参数 $\kappa$：

$$
\begin{aligned}

 p_0&=1-Z-X-Y+\kappa,&p_1&=X-\kappa,&p_2&=Z,\\
 p_3&=Y-\kappa,&p_{13}&=\kappa,&
 \max(0,X+Y+Z-1)&\le\kappa\le\min(X,Y).

\end{aligned}
$$

这些式子只是 $X=p_1+p_{13}$、$Y=p_3+p_{13}$、$Z=p_2$ 和概率归一化的线性解；非负性给上下界。它们不会自动补足相位。
均匀体积重心 $(3/8,3/8,1/4)$ 与均匀五点均值 $(2/5,2/5,1/5)$ 也不同：前者由截面面积 $(1-Z)^2$ 积分，后者直接平均顶点。（[12](#ref-pyramid)）

<a id="statement-5-2"></a>

#### 定理 5.2（三点对角读出的凸包界）

在三模式切面上，取对角坐标算符

$$
X=\operatorname{diag}(A_x,B_x,C_x),\qquad Y=\operatorname{diag}(A_y,B_y,C_y).
$$

任意密度态的 $(\operatorname{Tr}\rho X,\operatorname{Tr}\rho Y)$ 都在 $\operatorname{conv}\{A,B,C\}$ 内，且每个凸组合都可实现。
故重心与内心可由该接口实现，命题 [4.4](#statement-4-4) 的外心与垂心不能。

**证明。**

对角元 $\rho_{jj}\ge0$ 且和为一，两个期望值即同一组正权的三点均值。
反向对权重 $\lambda_j$ 取纯态 $\sum_j\sqrt{\lambda_j}e^{i\theta_j}\lvert j\rangle$。
$G$ 对应权重 $1/3$，$I$ 对应 $a,b,c$ 归一化；$O,H$ 在凸包外，故不可能。

∎

这不禁止量子系统参与外心或垂心计算；它只说明在同一三个顶点的对角概率读口里，有符号仿射系数不能冒充概率。
另外，任意有限平面点集都能包在某个大三角形中，再按其重心坐标构造上述三模式态。因此“存在高维态编码该点集”本身很弱：周期点云、任意点云同样能做。第 [2](#sec-2) 节的推进在于使用了 Hat 已有的实际重投影，而非这种普遍编码存在性。

<a id="statement-5-3"></a>

#### 定义 5.3（原生黄金门）

令 $\varphi=(1+\sqrt5)/2$、$\omega=e^{3\pi i/5}$，

$$
g=\varphi^{-1/2}\lvert 0\rangle +\varphi^{-1}\lvert 2\rangle ,\qquad
 P=\lvert g\rangle \langle g\rvert +\lvert 13\rangle \langle 13\rvert ,\qquad
 K=\omega[I+(\omega-1)P].
$$

$\varphi^{-1}+\varphi^{-2}=1$，故 $P$ 为秩二正交投影；这是项目三位置原生门在五种合法配置上的限制。（[14](#ref-v20)）

<a id="statement-5-4"></a>

#### 命题 5.4（八阶投影门与十阶黄金门的精确区别）

原生 $K$ 满足

$$
K^n=\omega^n(I-P)+\omega^{2n}P,\qquad K^{10}=I,\qquad K^5=2P-I.
$$

五模式 $\widehat U_D$ 不是单地址 $K$ 的任何幂，即使允许整体相位与固定酉共轭也不行。

**证明。**

投影的两个正交扇区上直接计算。任意 $K^n$ 至多有两个不同本征值，整体相位和共轭不增加其数目；$\widehat U_D$ 有四个不同本征值，矛盾。

∎

因此 $\widehat U_D\in\operatorname{U}(5)$ 提供了同维数的具体接口，却不等于已经在原生黄金菜单中完成编译。多地址原生调用的精确／近似实现是另一项需给出编码和接线的任务；本命题只排除单地址取幂。

<a id="sec-5-1"></a>

### 5.1. 一个新增的条件结果：同一单比特构件的两朝向普适性

<a id="statement-5-5"></a>

#### 定理 5.5（两种主动朝向生成稠密单比特门集）

令

$$
R_\theta=\begin{pmatrix}\cos\theta&-\sin\theta\\
 \sin\theta&\cos\theta\end{pmatrix},\quad
 D_0=D,\quad D_1=R_{\pi/3}DR_{\pi/3}^T,\quad
 M_j=\frac{I-iD_j}{\sqrt2}.
$$

若在同一固定复振幅编码中，$M_0$ 与 $M_1$ 都可主动调用，则它们的正向有限门字在 $\mathrm{SU}(2)$ 中稠密。

**证明。**

写 $\sigma_x=\bigl(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\bigr)$、
$\sigma_y=\bigl(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\bigr)$、
$\sigma_z=\operatorname{diag}(1,-1)$。
任意实对称二阶反射可写成 $D=a\sigma_x+b\sigma_z$，$a^2+b^2=1$。
对本矩阵 $a=3\sqrt{15}/16$、$b=-11/16$。
实平面旋转共轭使该 Pauli 轴旋转两倍角，直接相乘给

$$
\operatorname{Tr}(D_0D_1)=2\cos(2\pi/3)=-1,\qquad [D_0,D_1]\ne0.
$$

两门因此不对易，且

$$
\operatorname{Tr}(M_0M_1)=1-\frac12\operatorname{Tr}(D_0D_1)=\frac32.
$$

若 $C=M_0M_1$ 有限阶，其本征值是单位根，迹是代数整数。
有理代数整数必为整数：将既约分数代入首一整系数多项式，分母整除分子幂，只能为一。$3/2$ 不是整数，矛盾。

于是 $C\in\mathrm{SU}(2)$ 的本征角是 $\pi$ 的无理倍数，其幂闭包包含绕某个 Pauli 轴 $n$ 的完整圆群 $T_n$。
令 $G$ 为两门生成群的闭包，故 $T_n\subset G$，且 $M_0T_nM_0^\dagger=T_m\subset G$。
若 $m=\pm n$，则 $M_0$ 的伴随作用保持实直线 $\mathbb{R} n$。但该伴随作用是绕 $D_0$ 轴的 $\pi/2$ 旋转，唯一不变实直线就是其旋转轴。所以 $n$ 与 $D_0$ 共轴，$C$ 与 $M_0$ 对易，进而 $M_1=M_0^{-1}C$ 与 $M_0$ 对易，矛盾。故 $n,m$ 不平行。

由绕 $n$ 的一个适当小角度旋转共轭 $T_m$，可得到第三个轴 $\ell$，使 $n,m,\ell$ 线性独立；其初始偏移方向为非零的 $n\times m$。
三个圆群均包含在 $G$。映射

$$
(s,t,u)\longmapsto
 e^{-is\,n\cdot\sigma}e^{-it\,m\cdot\sigma}e^{-iu\,\ell\cdot\sigma}
$$

在原点的微分满秩，故由局部逆函数定理，其像含 $\mathrm{SU}(2)$ 单位元邻域。于是 $G$ 为开子群；$\mathrm{SU}(2)$ 连通，故 $G=\mathrm{SU}(2)$。
最后每个 $M_j^8=I$，逆可由七次正调用实现，因此正向有限字与含逆字生成同一个群，其闭包也为全群。

∎

这给出了一个具有精确矩阵及完整证明的候选：**同一种四分之一转动构件，在两个指定的主动朝向下，足以近似任意 $\mathrm{SU}(2)$ 门。**单独使用时，这等价于模整体相位的任意单比特门；带外部相干控制时不能省略相位接口。
但被动地同时转动门和读口的坐标系，不会新增一个可调用控制。CPS 的星映射也未必让物理与内部平面同向旋转，故不能仅由 Hat 图案含 $60^\circ$ 朝向就声称这两个算子已被供应。
该证明对任意实平面反射 $D$ 都成立，没有使用非周期性，因此不是 Hat 独有的普适性。它也没有提供纠缠资源，尚不能宣称任意多比特计算普适，更不能与原生黄金 $K$ 的既有多地址接口直接等同。

<a id="sec-6"></a>

## 6. 在三角复形上定义相容的 AURIC 关系

<a id="statement-6-1"></a>

#### 定义 6.1（AURIC 酉关系复形）

给一个有边界的有限共形三角复形 $\mathcal K$。其几何顶点集记作 $V$，每点配置纤维 $H_v\simeq\mathbb{C}^5$；几何顶点与纤维内五个模式的标签不能混同。
每条有向几何边 $u\to v$ 给出 $U_{vu}:H_u\to H_v$，满足
$U_{vu}^\dagger U_{vu}=I$、$U_{uv}=U_{vu}^\dagger$。
选择严格正权 $w_e>0$。截面空间及相容能量为

$$
\mathcal H_{\mathcal K}=\bigoplus_{v\in V}H_v,\qquad
 \mathcal E(\psi)=\sum_{e:u\to v}w_e\left\lVert \psi_v-U_{vu}\psi_u\right\rVert ^2 .
$$

每条无向边只选一个方向求和。

这里采用的是单截面直和，维数为 $5|V|$；若每个顶点是独立的多体量子系统，则应使用张量积，维数为 $5^{|V|}$，动力学和相容能量必须另行定义。
图上的向量丛、连接与相应 Laplacian 有标准数学背景。（[9](#ref-kenyon)）
此外，本定义中反向边的伴随是关系记账规则，不自动授予物理上执行所有逆程序的权限。

<a id="statement-6-2"></a>

#### 定理 6.2（规范协变与闭路相容）

令局部坐标变换 $G_v\in\operatorname{U}(5)$，同时变换

$$
\psi_v'=G_v\psi_v,\qquad U_{vu}'=G_vU_{vu}G_u^\dagger.
$$

则 $\mathcal E$ 不变。若图连通，取根 $r$ 和一棵生成树，其根到 $v$ 的输运为 $S_v$。
记非树边的根闭路矩阵 $H_e=S_v^\dagger U_{vu}S_u$。有

$$
\ker L\ \simeq\ \bigcap_{e\notin T}\operatorname{Fix}(H_e),\qquad
 L=d_U^\dagger d_U,
$$

其中 $(d_U\psi)_e=\sqrt{w_e}(\psi_v-U_{vu}\psi_u)$。

**证明。**

每项残差变为 $G_v(\psi_v-U_{vu}\psi_u)$，范数不变，且因平方和有 $\mathcal E=\langle\psi,L\psi\rangle$。
零能量使每条边残差为零；树边依次强制 $\psi_v=S_v\xi$，$\xi=\psi_r$。
其余边等价于 $\xi=H_e\xi$。反向由任意共同固定向量构造该截面即得零能量；两种映射互逆。

∎

非平凡闭路矩阵可以仍有固定向量，所以“存在一致状态”弱于“全部闭路矩阵为单位阵”。若每个三角面闭路矩阵均为 $I$，且复形单连通，则任何闭路可通过删除逆向边、跨越三角面缩到一点，其输运为 $I$。这里采用静态的闭路逻辑，不必先赋予一个外部线性时钟。

<a id="statement-6-3"></a>

#### 命题 6.3（一条对角线何时由边关系锁定）

凸四边形边界按 $a\to b\to c\to d\to a$ 给定酉关系。两三角都平坦的对角线 $a\to c$ 存在，当且仅当

$$
U_{ad}U_{dc}U_{cb}U_{ba}=I.
$$

存在时唯一，并为 $U_{ca}=U_{cb}U_{ba}$。

**证明。**

三角 $abc$ 平坦要求 $U_{ca}=U_{cb}U_{ba}$，三角 $acd$ 平坦要求 $U_{ad}U_{dc}U_{ca}=I$。代入即得充要条件，也给唯一性。

∎

这就是“边决定隐藏对角关系”的一个严格版本。若边界 holonomy 非平凡，不能通过随意选择对角线让两个三角都平坦。
但是即使两种剖分都平坦，增加不同对角边的平方残差也会改变能量；平坦性与剖分能量不变是不同要求。

项目的有锚 $U(1)$ 相位分类进一步说明：有限连通有名有向多重图含 $n$ 个顶点、$m$ 条有名边及 $k\ge1$ 个锚，且选定生成树和其中一个根锚时，锚固定的规范商有 $m+k-n$ 个独立圆相位坐标，即 $m-n+1$ 个闭路坐标与 $k-1$ 个锚相对坐标。（[16](#ref-phaseclass)）
若把各种心加入为新的锚，需给出它们真实的相位读口和新增边；几何中心的存在不供应这些相位。正反两条独立命名的边也不应因画在同一直线上就被误删。

<a id="sec-7"></a>

## 7. 递归、最优化与变分：一个严格闭合的模型

<a id="sec-7-1"></a>

### 7.1. 边界观察与 Schur 消元

<a id="statement-7-1"></a>

#### 定义 7.1（边界响应）

将顶点分为可见边界 $B$ 与隐藏内部 $I$，每个连通分支都接触 $B$。
给边界振幅 $g$，定义

$$
\mathcal E_{\mathrm{eff}}(g)=\min_{\psi_I}\mathcal E(g,\psi_I).
$$

内部振幅在全部复向量上优化，不施加逐点范数约束；极小解可以是次归一化的振幅。

<a id="statement-7-2"></a>

#### 定理 7.2（递归消元与整体变分等价）

将 $L$ 按边界、内部写成块矩阵，则 $L_{II}>0$，

$$
\psi_I^\ast=-L_{II}^{-1}L_{IB}g,\qquad
 \mathcal E_{\mathrm{eff}}(g)=g^\dagger Sg,\qquad
 S=L_{BB}-L_{BI}L_{II}^{-1}L_{IB}\ge0.
$$

将内部任意分层后逐层消元，与一次消掉全部内部得到同一个 $S$。

**证明。**

若零边界截面的能量为零，酉边关系沿连通路径将边界零值传播到全部顶点，因此该截面为零；有限维中即得 $L_{II}$ 正定。
配方给

$$
\mathcal E(g,\psi_I)
 =(\psi_I-\psi_I^\ast)^\dagger L_{II}(\psi_I-\psi_I^\ast)
   +g^\dagger Sg .
$$

唯一极小元、最小值和 $S\ge0$ 随即成立。任意有限分块满足

$$
\min_{x,y}E(x,y)=\min_x\min_yE(x,y).
$$

严格凸性使每层的极小元唯一，最小二次型对所有 $g$ 相等，故 Schur 消元结合。

∎

在这个模型中，“预测”被具体定义为给定边界后求内部相容振幅；递归是分层消元；变分是内部 Euler–Lagrange 方程；最优化是同一个正二次型的极小化。这四者确实一致，前件也清楚。
一般的预测任务未指定损失与载体时，不能由名称直接得出相等。

逐点归一化会改变问题。例如边界为单位向量 $u,-u$，内点 $z$ 的能量
$\left\lVert z-u\right\rVert ^2+\left\lVert z+u\right\rVert ^2=2\left\lVert z\right\rVert ^2+2$。
自由振幅的唯一解为 $z=0$；若强制 $\left\lVert z\right\rVert =1$，所有单位向量都成为同能量解，线性 Schur 唯一性不再适用。

<a id="sec-7-2"></a>

### 7.2. 中心消元、边细分与并联

<a id="statement-7-3"></a>

#### 定理 7.3（一个“心”产生的精确边关系）

设每个 $V_i:H_i\to H_z$ 为酉，隐藏中心 $z\in H_z$ 接收输运后的边界向量 $y_i=V_i x_i$，权 $a_i>0$，$W=\sum_i a_i$。则

$$
z^\ast=\frac{\sum_i a_i y_i}{W},\qquad
 \min_z\sum_i a_i\left\lVert z-y_i\right\rVert ^2
 =\frac1W\sum_{i<j}a_i a_j\left\lVert y_i-y_j\right\rVert ^2.
$$

有效 $i\to j$ 关系为 $V_j^\dagger V_i$，任意有效三角闭路为 $I$。

**证明。**

配方得到中心均值，最小值为
$\sum_i a_i\left\lVert y_i\right\rVert ^2-W^{-1}\left\lVert \sum_i a_i y_i\right\rVert ^2$。
展开两两差的平方即得所列式。
左乘 $V_j^\dagger$ 得有效边；三角乘积
$V_i^\dagger V_kV_k^\dagger V_jV_j^\dagger V_i=I$。

∎

取三角位置向量和 $V_i=I$，等权给重心，按对边长加权给内心。由此中心、边权和变分可以在一个模型中联结。
但一个只有共同中心且没有额外记忆的星图消元只产生平坦关系，不能自动产生任意非平凡三角 holonomy。量子相干闭路需要额外的边数据或内部结构。

<a id="statement-7-4"></a>

#### 命题 7.4（细分权重的尺度律）

将一条边替成 $m$ 段酉输运 $U_m\cdots U_1=U$，各段权为 $w_j>0$，消去中间振幅后得到

$$
\mathcal E_{\mathrm{eff}}(a,b)
 =w_{\mathrm{eff}}\left\lVert b-Ua\right\rVert ^2,\qquad
 w_{\mathrm{eff}}=\left(\sum_{j=1}^m w_j^{-1}\right)^{-1}.
$$

**证明。**

沿路径把每个变量输运回起点坐标，问题变成端点差固定的增量 $d_j$，且 $\sum_jd_j=U^\dagger b-a$。
加权 Cauchy–Schwarz 给
$\left\lVert \sum_jd_j\right\rVert ^2\le(\sum_j w_j^{-1})\sum_jw_j\left\lVert d_j\right\rVert ^2$。
取 $d_j=(U^\dagger b-a)/(w_j\sum_\ell w_\ell^{-1})$ 达到等号。

∎

因此每段照搬原权 $w$ 会把有效权降为 $w/m$；要保留原边的能量，应给每段权 $mw$。
项目 v20 的链残差最小值 $\left\lVert V-U_w\right\rVert _F^2/(L+1)$ 正体现这项效应：增加恒等步骤可以降低未重标定的残差，却没有改善端点门近似。（[14](#ref-v20)）

<a id="statement-7-5"></a>

#### 定理 7.5（并联相容的有效收缩）

给酉路径 $V_j$、权 $w_j>0$，令

$$
W=\sum_jw_j,\qquad M=W^{-1}\sum_jw_jV_j .
$$

则

<a id="eq-4"></a>

$$
\begin{aligned}
 \sum_jw_j\left\lVert b-V_ja\right\rVert ^2
 &=W\left\lVert b-Ma\right\rVert ^2+W a^\dagger(I-M^\dagger M)a,\end{aligned}
\tag{4}
$$

<a id="eq-parallel"></a>

$$
\begin{aligned}
 I-M^\dagger M
 &=\frac1{2W^2}\sum_{j,k}w_jw_k(V_j-V_k)^\dagger(V_j-V_k)\ge0.

\end{aligned}
\tag{5}
$$

$M$ 酉当且仅当所有 $V_j$ 相同。

**证明。**

展开第一式，交叉项相同，利用 $V_j^\dagger V_j=I$ 得常数差。
展开第二式的双和，其两个对角乘积各为 $W^2I$，其余项为 $2W^2M^\dagger M$。
所有权严格正，所以缺陷为零当且仅当所有矩阵差均为零。

∎

这解释了为什么总体边关系都酉，而遗忘隐藏路径后的有效观察仍可能收缩。递归消元自然闭合在正半定边界二次型中，一般不闭合在“只含单条酉边、没有额外势项”的狭窄形式中。

<a id="sec-8"></a>

## 8. 黄金门在三角关系中的两个精确结果

<a id="statement-8-1"></a>

#### 定理 8.1（两条酉路径产生黄金投影）

令 $R_P=K^5=2P-I$。两条等权路径 $I,R_P$ 的相容能量为

$$
\left\lVert b-a\right\rVert ^2+\left\lVert b-R_Pa\right\rVert ^2
 =2\left\lVert b-Pa\right\rVert ^2+2\left\lVert (I-P)a\right\rVert ^2.
$$

对自由输出振幅 $b$，唯一极小元为 $b^\ast=Pa$。
对 $a=\lvert 2\rangle$，有 $\left\lVert Pa\right\rVert ^2=\varphi^{-2}$，最小能量为 $2\varphi^{-1}$。

**证明。**

在定理 [7.5](#statement-7-5) 中取 $M=(I+R_P)/2=P$。由于 $P$ 是正交投影，缺陷为 $I-P$，得到恒等式和极小元。
$\langle 2\rvert P\lvert 2\rangle =\varphi^{-2}$，且 $1-\varphi^{-2}=\varphi^{-1}$。

∎

在相干控制与 Hadamard 操作另被提供时，辅助比特上的干涉可以实现保留完整记录的映射

$$
\lvert 0\rangle  a\longmapsto \lvert 0\rangle  Pa+\lvert 1\rangle (I-P)a .
$$

其两支总范数仍为 $\left\lVert a\right\rVert ^2$；选择第一支才得到次归一化的 $Pa$。
原生 $K$ 的存在不自动提供受控 $K^5$、辅助位和相位参考，故这是明确接口下的实现式。

<a id="statement-8-2"></a>

#### 定理 8.2（单位边权黄金三角的精确谱隙）

在三个几何顶点上取输运 $I,I,K$，定义

$$
\mathcal E_\triangle
 =\left\lVert \psi_1-\psi_0\right\rVert ^2+\left\lVert \psi_2-\psi_1\right\rVert ^2
  +\left\lVert \psi_0-K\psi_2\right\rVert ^2.
$$

在总归一化 $\sum_{j=0}^2\left\lVert \psi_j\right\rVert ^2=1$ 下，

$$
\boxed{\min\mathcal E_\triangle=2-\varphi=\varphi^{-2}.}
$$

全部极小截面恰为

$$
\psi_j=\frac{e^{-ij\pi/5}}{\sqrt3}u,\qquad
 u\in\ker P,\quad \left\lVert u\right\rVert =1.
$$

最低本征空间的复维数为三。

**证明。**

在 $H_A^{\oplus3}$ 上定义
$T(\psi_0,\psi_1,\psi_2)=(K\psi_2,\psi_0,\psi_1)$。
它酉，$T^3=\operatorname{diag}(K,K,K)$，而能量对应 $L_\triangle=2I-T-T^\dagger$。
若 $Ku=e^{i\theta}u$，取
$\zeta_m=e^{i(\theta+2\pi m)/3}$，$m=0,1,2$，则

$$
\frac1{\sqrt3}(u,\zeta_m^{-1}u,\zeta_m^{-2}u)
$$

是 $T$ 的本征向量，本征值为 $\zeta_m$；这三向量正交，遍历 $K$ 的本征基后给完整基。因此
$L_\triangle$ 对应本征值为 $2-2\cos((\theta+2\pi m)/3)$。

在 $\ker P$ 上主角 $\theta=3\pi/5$，最近于一的立方根唯一为 $e^{i\pi/5}$，给 $2-2\cos(\pi/5)=2-\varphi$。
在 $\operatorname{im} P$ 上取主角 $\theta=-4\pi/5$，最近根角的绝对值为 $4\pi/15>\pi/5$，其最小值严格更大。
在该正交本征基展开总单位截面，能量是各本征值的非负加权平均，得到最小值及全部等号情形。最后 $\dim\ker P=5-2=3$。

∎

这里的“三”来自该具体五模式投影的秩，并不证明物理空间必须三维。该能隙不使用非周期性，同样可出现在周期底图上；所有边权为一及全局而非逐顶点归一化均是前件。

<a id="statement-8-3"></a>

#### 说明 8.3（闭路相位要有实际比较接口）

上述能量使用 $K$ 的完整边相位。若仅给出量子通道 $\rho\mapsto K\rho K^\dagger$，则 $K$ 与 $\omega^{-1}K$ 表示同一通道，但后者在 $\ker P$ 上为 $I$，相应三角存在零能量截面。因此 $\varphi^{-2}$ 不是仅由这条无干涉通道决定的物理能量；它属于保留路径相干和参考相位的关系模型。闭路谱与黄金数的精确联系成立，但相位读口不能省略。

<a id="sec-9"></a>

## 9. 三角几何怎样确定权重，以及对角线怎样被变分选择

<a id="statement-9-1"></a>

#### 定理 9.1（三角形的余切能量）

在欧氏三角形上，以顶点值 $z_1,z_2,z_3$ 作分片线性插值 $z$，角 $\theta_i$ 对边为 $jk$。则

<a id="eq-cot"></a>

$$
E_D(z)=\frac12\int_T\left\lVert \nabla z\right\rVert ^2\,dA
 =\frac14\sum_{i=1}^3\cot\theta_i\,\left\lVert z_j-z_k\right\rVert ^2 .
\tag{6}
$$

向量或复数值逐分量成立。若有平坦酉连接，可先把三顶点输运到同一坐标框再用此式。

**证明。**

写 $z=\sum_i\lambda_i z_i$，其中 $\lambda_i$ 为重心基函数。
$\nabla\lambda_i$ 垂直于对边且长度为该边长除以 $2\Delta$。
对 $i\ne j$，两梯度的夹角是 $\pi-\theta_k$，于是
$\int_T\nabla\lambda_i\cdot\nabla\lambda_j=-\frac12\cot\theta_k$。
再用 $\sum_i\nabla\lambda_i=0$ 确定对角项，将梯度平方展开并重组为两两差平方，得到 [(6)](#eq-cot)。
酉换框保持范数；面平坦使三次换框一致。

∎

这是离散 Dirichlet 能量的标准余切公式，系数随能量是否带 $1/2$ 而变；这里与 Pinkall–Polthier 的约定一致。（[10](#ref-pinkall)）
一个内边对应权为 $(\cot\alpha+\cot\beta)/4$。当 $\alpha+\beta\le\pi$ 时该权非负，因为
$\cot\alpha+\cot\beta=\sin(\alpha+\beta)/(\sin\alpha\sin\beta)$。
钝角的单个余切可以为负，边界边也未必非负。标量 FEM 的整体能量仍由积分保证非负，但不能把负余切当概率，或在任意非平坦边酉矩阵上照搬后声称仍是正边权模型。

<a id="statement-9-2"></a>

#### 定理 9.2（凸四边形的精确翻边能量差）

取 $A=(0,0)$、$C=(1,0)$、$B=(p,q)$、$D=(r,-s)$，四边形凸且 $q,s>0$。
令

$$
J=ps+qr>0,\quad L=q+s-J>0,\quad
 Q=s(p^2-p+q^2)+q(r^2-r+s^2).
$$

给四顶点实数数据，减去经过 $A,B,C$ 三数据的仿射函数后，剩余数据记作 $(0,0,0,t)$。则两种分片线性插值满足

<a id="eq-flip"></a>

$$
E_{BD}-E_{AC}=\frac{t^2qQ}{4sJL}.
\tag{7}
$$

$D$ 对圆 $ABC$ 的幂为 $Q/q$，故局部 Delaunay 对角线 $AC$ 对所有数据都不增加 Dirichlet 能量；四点共圆时两能量完全相等。

**证明。**

两种插值在四边形边界相同，所以两者梯度积分之差为零；减去同一仿射函数不改变能量差。
对残余数据，$AC$ 剖分只有三角 $ACD$ 有非零梯度，直接积分得 $E_{AC}=t^2/(4s)$。
$BD$ 剖分两三角分别给

$$
E_{BD}=\frac{t^2}{4}
 \left(\frac{p^2+q^2}{J}+\frac{(1-p)^2+q^2}{L}\right).
$$

通分并用 $J+L=q+s$ 得 [(7)](#eq-flip)。
圆 $ABC$ 的方程为
$x^2+y^2-x+\frac{p-p^2-q^2}{q}y=0$，代入 $D$ 得 $Q/q$。
圆外／圆上对应 $Q\ge0$，因分母正，能量比较随即成立。

∎

这与 Delaunay 的最小粗糙度背景一致。（[11](#ref-rippa)）
在 $t=0$ 的仿射数据情形，非共圆时也不能凭这份能量唯一选择对角线。
对非凸 Hat，只允许在内部凸相邻四边形中合法翻边，并保留原边界约束。
因此三角剖分选择可以是一个定义清楚的变分步骤；它仍未指定量子仪器、分支概率或测后态，不能直接命名为塌缩。

<a id="sec-10"></a>

## 10. 递归增长、有限门循环与项目的完整返回坐标

<a id="sec-10-1"></a>

### 10.1. 层级替代与有限酉重复的差别

Hat 原论文的初始 metatile 超瓦片一般不是同一形状的相似放大；经归一化后的极限形状才给出膨胀因子 $\varphi^2$ 的几何替代。（[2](#ref-hat)）
复制刚性瓦片、增加瓦片数量、改变层级尺子和在固定 Hilbert 空间上酉旋转，是四种不同操作。

<a id="statement-10-1"></a>

#### 命题 10.1（Fibonacci 频率不唯一决定黄金量子门）

经典替代 $A\mapsto AB$、$B\mapsto A$ 的计数矩阵
$S=\bigl(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\bigr)$
有归一化正本征向量 $p=(\varphi^{-1},\varphi^{-2})^T$，满足 $Sp=\varphi p$。
它允许整个相位族

$$
g_\chi=\sqrt{\varphi^{-1}}\lvert 0\rangle +
 e^{i\chi}\sqrt{\varphi^{-2}}\lvert 2\rangle
$$

具有相同基底概率，因而不唯一确定 $P$ 的交叉相位，也不确定 $K$ 的 $\omega$。

**证明。**

利用 $\varphi^2=\varphi+1$ 代入即可验证本征等式与归一化。所有 $g_\chi$ 的振幅模方相同，而其非对角投影元随 $\chi$ 变化。

∎

这给黄金权重一个清楚的经典频率骨架，但它不是 Hat 替代系统与 AURIC 门之间已经证明的交织映射。
若把替代粗暴写成
$\lvert A\rangle \mapsto(\lvert A\rangle +\lvert B\rangle )/\sqrt2$、
$\lvert B\rangle \mapsto\lvert A\rangle$，两像内积为 $1/\sqrt2$，不保持原来的零内积。
改用明确的词、地址和父类型寄存器可保留记录并建立等距扩展；必须写出这些空间与映射。

<a id="statement-10-2"></a>

#### 定理 10.2（固定有限门的连续有限字母读出必周期）

设 $U\in\operatorname{U}(d)$、单位态 $\psi$，$q$ 为单位球上的连续映射，值在某个度量空间。
若实际序列 $\{q(U^n\psi):n\ge0\}$ 只取有限多个值，则该序列周期。

**证明。**

若只有一个值结论显然；否则这些值之间有最小正距离 $\delta$。
单位球紧，$q$ 一致连续，故存在 $\eta>0$，使输入距离小于 $\eta$ 时输出距离小于 $\delta$。
紧群 $\operatorname{U}(d)$ 中正幂序列有两个不同幂 $U^m,U^n$ 距离小于 $\eta$；置 $p=m-n>0$，则 $\left\lVert U^p-I\right\rVert <\eta$。
于是所有 $k$ 都有 $\left\lVert U^{k+p}\psi-U^k\psi\right\rVert <\eta$，故两个读出值相距小于 $\delta$，只能相等。$p$ 是周期。

∎

该定理不限制变化程序、无限 Hilbert 空间、增加的记录、随机测量样本或不连续窗口编码。作为区别，若 $0<\alpha<1$ 无理，
$s_n=\lfloor(n+1)\alpha\rfloor-\lfloor n\alpha\rfloor$
是一个二值非周期序列：前 $N$ 项平均趋于无理数 $\alpha$，而周期二值序列平均必有理。它由圆周旋转的不连续分窗得到，不能当作连续确定性量子概率读出的反例。

本稿的 $U_D$ 和 $M_D$ 都只有八阶，原生单地址 $K$ 只有十阶。非周期整体来自允许的输入族、窗口、层级与关系约束，不来自其中一个有限阶矩阵在同一状态上无限取幂。定理 [5.5](#statement-5-5) 使用两个不对易的主动控制，其无限阶乘积说明有限阶生成元仍可产生无限且稠密的群，两者没有矛盾。

<a id="sec-10-2"></a>

### 10.2. 最新项目：周期基底仍须保留闭路增量

<a id="statement-10-3"></a>

#### 定义 10.3（加性斜积）

令 $f:X\to X$，$A$ 为加法交换群，$c:X\to A$，定义

$$
T(x,a)=(f(x),a+c(x)),\qquad
 S_n(x)=\sum_{j=0}^{n-1}c(f^jx).
$$

若 $x$ 的最小正周期为 $p$，定义一轮增量 $h=S_p(x)$。

<a id="statement-10-4"></a>

#### 定理 10.4（提升轨道的周期与坐标）

有 $T^n(x,a)=(f^nx,a+S_n(x))$。
若 $h$ 的加法阶为有限 $q$，则提升轨道最小周期为 $pq$，且映射

$$
\{0,\ldots,p-1\}\times\langle h\rangle
 \longrightarrow \operatorname{Orb}_T(x,a),\qquad
 (i,s)\longmapsto(f^ix,a+S_i(x)+s)
$$

是双射。若 $h$ 无限阶，则无正返回时间。

**证明。**

第一式归纳即得。若基点返回，$n$ 必为 $kp$；此时由周期性 $S_{kp}(x)=kh$，所以完整返回当且仅当 $kh=0$。
有限阶时最小正 $k=q$，无限阶时不存在。
任意 $n=i+kp$ 给 $S_n=S_i+kh$，故所有轨道点在所列像中；有限阶使 $\langle h\rangle$ 的每个元素可由非负倍数取得。
不同余数 $i$ 对应不同基点；同余数时第二坐标确定 $s$，故单射。

∎

该坐标结论是本轮最新合并模块的主题，其返回条件依赖已有 `SkewAdditiveReturn`。（[17](#ref-skew)）
纤维群可无限，且不需 $f$ 在全空间可逆。
若基底周期为 $p$，每个完整基底周期的纤维增量为 $K^q$，则完整算子返回周期为
$p\,10/\gcd(10,q)$。这要求固定的周期驱动与记录模型；对一个本征态的射线读出，整体相位还可能不可见。
一个指定轨道不返回与单原型瓦片的“所有合法全平面铺砌都不周期”具有不同量词，不能相互替代。

<a id="sec-10-3"></a>

### 10.3. 从递归等距数据得到静态 Hilbert 极限

<a id="statement-10-5"></a>

#### 定理 10.5（一致等距递归的 Hilbert 极限）

给 Hilbert 空间 $H_n$ 和等距嵌入 $J_n:H_n\to H_{n+1}$。
把向量 $(n,\psi)$ 与 $(m,\phi)$ 在某个共同更高层级像相同时识别，其线性直极限上的内积由任意共同层级计算，良定义；完成后得到 Hilbert 空间 $H_\infty$。
若另有酉 $U_n$ 满足 $U_{n+1}J_n=J_nU_n$，则它们诱导 $H_\infty$ 上唯一的酉 $U_\infty$。

**证明。**

等距性保证共同层级升高不改变内积，也保证等价代表给相同内积。将各层嵌入像并起来形成内积空间，取完成即得第一结论。
交织等式保证 $[(n,\psi)]\mapsto[(n,U_n\psi)]$ 与代表无关并保持内积。
由酉性同样有 $U_{n+1}^\dagger J_n=J_nU_n^\dagger$，故逆映射也一致；两者延拓到完成互逆，因而酉且唯一。

∎

这让层级索引表示细化程度而不必表示外部时间。观察者可建模为该静态载体中的一个有记录、边界读口和继续规则的子系统；内部预测就是指定数据下的条件延拓或边界消元。
不过裸静态图不自行指定复数域、内积、测度或可执行门；这些等距前件正是定理所使用的结构，不能在结论后反说已由“图”一词无条件推导。

<a id="sec-11"></a>

## 11. 理论的闭合部分与仍需证明的接口

目前可定义一个完整的条件研究对象：

$$
\mathfrak A=
 (\mathcal K,\text{父瓦片与类型记录},H_v,U_e,w_e,
 B,\text{读出接口},\text{层级嵌入}).
$$

几何层给出合法邻接、三角剖分与可选度量；相干关系层给出纤维和边输运；观察层指定保留的边界与记录；变分层用同一能量进行递归消元。其规范变换、零能量相容、中心消元、串并联、细分重标定与边界响应均已在本文证明。

这组结果支持三个具体方向。第一，真正的 Hat 重投影已经有明确的保范数完成，两主动朝向还给出单比特近似普适性；下一步应给它与原生多地址 AURIC 菜单的编译映射、纠缠资源及误差合同。第二，三角心可提供几何权重或局部锚，但需另给把角度、窗口类型或边界关系转成物理相位的规则。第三，若递归观察要在任意尺度保持同一预测意义，必须同时保留 Schur 边界响应、归一化方式及必要的路径和层级记录。

一种非周期底图可以取所有 $U_e=I$；一种周期底图也可以赋予非平凡 holonomy。故空间非周期性与量子相干受挫在目前定义中是独立自由度。只有新增并检验具体耦合规则，才能断言某类瓦片必然强迫某个门谱。

项目新续卷 II 已给出一条有实质内容的条件 Born 刚性路线：在指定十站点、七地址、十三维复扇区及全终端标签的来源中，低的全未来响应秩配合连续射线充分性与基底校准，能够确定 Born 终端律；同时也证明已给的复载体、可逆门与旧校准并不自动提供所需容量上限。（[18](#ref-continuation)）
其第 84.4 节仍将复结构、共同源相干、相位参考、真实仪器与组合、动力学的起源列为未解决接口。第 83.3 节还保留同一完整终端合同的经典群点／射线点表示。因而“所有观测已被证明只可能来自量子本体”不是本轮源码支持的结论。

本稿的肯定性结论更具体：**真实非周期几何的控制点重投影可以嵌入保范数变换；三角关系可以承担酉输运；有记录的边界预测可以通过同一正二次型实现递归变分；黄金门在该关系模型中给出可精确证明的投影与谱隙。**
这些构造为进一步检验基础假设提供了明确接口和反例，而不是用同一个“预测”名称覆盖所有尚未取得的结构。

<a id="sec-a"></a>

## A. 来源、定义与证明范围的核查索引

| 条目 | 本文采用的范围 |
| --- | --- |
| Hat / Spectre | 原作者的非周期性与手性定理作为输入；本稿未重新证明其全部强制层级论证。 |
| Hat 几何 | 作者固定源码的整数格标签；精确长度、面积、角点均值、三角心和本文所列剖分以纸面坐标核对；图不参与证明。 |
| 四维模型集 | 文献提供格点、内部窗口及有色控制点重投影。矩阵 $D$ 针对指定 Hat 规范，不直接代替 Spectre 矩阵或十三角点坐标。 |
| 正交／酉完成 | 本文对文献 $D$ 的直接代数推论。编码、归一化、读出与窗口判别分别声明。 |
| 图连接与余切能量 | 采用已有向量丛 Laplacian 与离散 Dirichlet 背景；本文给出所需有限维证明，未调用其余森林计数或最小曲面结论。 |
| AURIC 模块 | 金字塔坐标、原生 $K$、锚相位与最新斜积来自固定项目来源；正文对所用公式另给纸面推导。 |
| 量子基础 | 复 Hilbert、正内积、Born 接口和可执行控制在使用处保留为前件；不声称已从非周期性单独推出。 |
| 验证 | 文献与源码只读获取、文本／版本核对；数学不运行数值程序、CAS 或 Lean。PDF 编译与图形排版仅用于交付质量检查。 |

<a id="sec-bibliography"></a>

## 文献与固定项目来源

<a id="ref-snapshot"></a>

**[1]** 
the-omega-institute/trureturing，[固定研究快照](https://github.com/the-omega-institute/trureturing/tree/ae864ac4ae3d01dc2e589a21fde123c4d5ca92f7)，2026-10-30。
完整 SHA 见第 [1](#sec-1) 节；合并 PR #24038。

<a id="ref-hat"></a>

**[2]** 
D. Smith, J. S. Myers, C. S. Kaplan, C. Goodman-Strauss.
*An aperiodic monotile*.
Combinatorial Theory 4(1), #6 (2024).
[arXiv:2303.10798v3](https://arxiv.org/abs/2303.10798)；
[作者项目页](https://cs.uwaterloo.ca/~csk/hat/)。
本文定向使用定义、§2 的 metatile 层级及极限形状、§3 的格坐标背景。

<a id="ref-spectre"></a>

**[3]** 
D. Smith, J. S. Myers, C. S. Kaplan, C. Goodman-Strauss.
*A chiral aperiodic monotile*.
Combinatorial Theory 4(2), #13 (2024).
[arXiv:2305.17743v2](https://arxiv.org/html/2305.17743v2)，§§1–3。

<a id="ref-hatcode"></a>

**[4]** 
原作者 `isohedral/hatviz`，[固定版 geometry.js](https://github.com/isohedral/hatviz/blob/4bb9d01999e4e84accc2a78d0fa279ef20b47263/geometry.js)，
`hexPt` 与 `hat_outline`。
仅读取整数格标签，未执行绘图或铺砌生成程序。

<a id="ref-diffraction"></a>

**[5]** 
M. Baake, F. Gähler, J. Mazáč, A. Mitchell.
*Diffraction of the Hat and Spectre tilings and some of their relatives*.
Journal of Mathematical Physics 66, 092707 (2025).
[doi:10.1063/5.0264955](https://doi.org/10.1063/5.0264955)；
[arXiv:2502.03268v2](https://arxiv.org/html/2502.03268v2)，尤其 §§3.1–3.2。

<a id="ref-survey"></a>

**[6]** 
M. Baake, F. Gähler, A. Klick, N. Mañibo, J. Mazáč.
*Renormalization techniques for inflation systems and some of their applications*.
Acta Crystallographica A82, 294–304 (2026).
[正文及 Theorem 3.1](https://journals.iucr.org/a/issues/2026/04/00/gau5007/)；
doi:10.1107/S2053273326003918。

<a id="ref-hatdynamics"></a>

**[7]** 
M. Baake, F. Gähler, L. Sadun.
*Dynamics and topology of the Hat family of tilings*.
Israel Journal of Mathematics 270, 449–485 (2025).
[doi:10.1007/s11856-025-2780-8](https://doi.org/10.1007/s11856-025-2780-8)。
尤其窗口边界、类型信息与重投影的说明。

<a id="ref-spectreorder"></a>

**[8]** 
M. Baake, F. Gähler, J. Mazáč, L. Sadun.
*On the long-range order of the Spectre tilings*.
Discrete & Computational Geometry 76, 739–762 (2026).
[arXiv:2411.15503v3，2026-10-07](https://arxiv.org/abs/2411.15503)，
Theorem 9、§6 与 Corollary 11；
doi:10.1007/s00454-025-00756-z。

<a id="ref-kenyon"></a>

**[9]** 
R. Kenyon.
*Spanning forests and the vector bundle Laplacian*.
Annals of Probability 39(5), 1983–2017 (2011).
[arXiv:1001.4028](https://arxiv.org/pdf/1001.4028)，§§3.1–3.3；
doi:10.1214/10-AOP596。

<a id="ref-pinkall"></a>

**[10]** 
U. Pinkall, K. Polthier.
*Computing Discrete Minimal Surfaces and Their Conjugates* (1993).
[作者原文](https://page.mi.fu-berlin.de/polthier/articles/diri/diri_jem.pdf)，
§3、Lemma 1、式 (2)–(3)。

<a id="ref-rippa"></a>

**[11]** 
S. Rippa.
*Minimal roughness property of the Delaunay triangulation*.
Computer Aided Geometric Design 7(6), 489–497 (1990).
[doi:10.1016/0167-8396(90)90011-F](https://doi.org/10.1016/0167-8396(90)90011-F)。
出版摘要用于背景归属；本文式 [(7)](#eq-flip) 给出独立的局部纸面计算。

<a id="ref-pyramid"></a>

**[12]** 
[AURIC 金字塔基础公式与关系卷](https://github.com/the-omega-institute/trureturing/blob/ae864ac4ae3d01dc2e589a21fde123c4d5ca92f7/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)，
固定快照，尤其 §§2–4。旧模式标签与本文标签的映射见第 [5](#sec-5) 节。

<a id="ref-v18"></a>

**[13]** 
[三角剖分、塌缩与递归酉门，v18](https://github.com/the-omega-institute/trureturing/blob/ae864ac4ae3d01dc2e589a21fde123c4d5ca92f7/docs/develop/theory/AURIC_TRIANGULATION_COLLAPSE_AND_RECURSIVE_UNITARY_GATES_V18.md)。
先前作者手稿的项目转录，尤其对角线概率纤维与酉扩张的条件。

<a id="ref-v20"></a>

**[14]** 
[黄金选择器门、递归编译与变分原理，v20](https://github.com/the-omega-institute/trureturing/blob/ae864ac4ae3d01dc2e589a21fde123c4d5ca92f7/docs/develop/theory/AURIC_GOLDEN_SELECTOR_GATES_RECURSIVE_COMPILATION_AND_VARIATIONAL_PRINCIPLES_V20.md)。
先前作者手稿的项目转录，尤其原生门定义和链残差归一化。

<a id="ref-v22"></a>

**[15]** 
[相对门历史、观察商与递归闭合，v22](https://github.com/the-omega-institute/trureturing/blob/ae864ac4ae3d01dc2e589a21fde123c4d5ca92f7/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)。
先前作者手稿的项目转录；共同参考消去与完整未来闭合不能混同。

<a id="ref-phaseclass"></a>

**[16]** 
[Complete Anchored Phase Classification](https://github.com/the-omega-institute/trureturing/blob/ae864ac4ae3d01dc2e589a21fde123c4d5ca92f7/Blueprint/D5/S3/Observer/AgencyHolonomy/AnchoredPhaseClassification.md)，
固定快照 Blueprint；声明保留有名平行边、独立命名的反边、锚及执行权限边界。

<a id="ref-skew"></a>

**[17]** 
[Coordinates on a lifted periodic orbit](https://github.com/the-omega-institute/trureturing/blob/ae864ac4ae3d01dc2e589a21fde123c4d5ca92f7/Blueprint/D5/S1/Dynamics/PeriodicOrbits/SkewOrbitCoordinates.md)；
[SkewAdditiveReturn](https://github.com/the-omega-institute/trureturing/blob/ae864ac4ae3d01dc2e589a21fde123c4d5ca92f7/Blueprint/D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.md)，
固定快照 Blueprint 及对应 Lean 源码。本文给出所用有限阶坐标与返回结论的纸面证明，未重跑 Lean。

<a id="ref-continuation"></a>

**[18]** 
[AURIC 量子原则与相干重构续卷 II](https://github.com/the-omega-institute/trureturing/blob/ae864ac4ae3d01dc2e589a21fde123c4d5ca92f7/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)，
固定快照，尤其 §§77–79、82–84：来源特定的低容量 Born 刚性、经典点表示及仍未取得的基础接口。

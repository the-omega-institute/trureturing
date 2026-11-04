<details data-production="preamble"><summary>原始 XeLaTeX 制作设置与元数据（原样保留）</summary>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

```tex
% !TeX program = xelatex
% Compile twice with XeLaTeX. Optional: \def\AURICFontPath{/absolute/font/path/}
% All mathematical arguments are paper proofs. Code only produces documents and source records.
\documentclass[11pt,a4paper]{article}
\usepackage[margin=23mm,headheight=16pt]{geometry}
\usepackage{fontspec}
\ifdefined\AURICFontPath
 \setmainfont[Path=\AURICFontPath,BoldFont=NotoSerifCJKsc-Bold.otf,
 ItalicFont=NotoSerifCJKsc-Regular.otf,BoldItalicFont=NotoSerifCJKsc-Bold.otf]{NotoSerifCJKsc-Regular.otf}
\else
 \IfFontExistsTF{Noto Serif CJK SC}{
 \setmainfont[ItalicFont=Noto Serif CJK SC,BoldItalicFont=Noto Serif CJK SC Bold]{Noto Serif CJK SC}
 }{\setmainfont[BoldFont=FandolSong-Bold.otf,ItalicFont=FandolSong-Regular.otf,
 BoldItalicFont=FandolSong-Bold.otf]{FandolSong-Regular.otf}}
\fi
\setmonofont{Latin Modern Mono}
\XeTeXlinebreaklocale "zh"
\XeTeXlinebreakskip=0pt plus 1pt
\usepackage{amsmath,amssymb,amsthm,mathtools,bm}
\usepackage{booktabs,array,tabularx,enumitem,fancyhdr,xcolor,needspace,tikz}
\usetikzlibrary{arrows.meta,positioning}
\definecolor{auricblue}{RGB}{24,53,79}
\definecolor{auricgold}{RGB}{153,105,29}
\usepackage[unicode,colorlinks=true,linkcolor=auricblue,urlcolor=auricblue,citecolor=auricblue]{hyperref}
\hypersetup{pdftitle={AURIC v73：从前缀态到最小闭合关系体},
pdfauthor={AURIC research continuation},
pdfsubject={Relational rigidity, coherent prefix histories, finite closure and quantum reconstruction}}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\HH}{\mathcal H}
\newcommand{\Aalg}{\mathcal A}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\spanof}{\operatorname{span}}
\newcommand{\Herm}{\operatorname{Herm}}
\newcommand{\ket}[1]{|#1\rangle}
\newcommand{\bra}[1]{\langle#1|}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/#1}{#2}}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{remark}[definition]{说明}
\renewcommand{\proofname}{证明}
\renewcommand{\abstractname}{摘要}
\renewcommand{\refname}{固定来源与参考文献}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{2pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC：前缀态与最小闭合关系体}
\fancyhead[R]{\small v73 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
\begin{center}
{\LARGE\bfseries\color{auricblue} 从前缀态到最小闭合关系体}\\[9pt]
{\large 用整组已知关系确定维数、门与递归}\\[7pt]
AURIC 量子起源研究\quad 定义、定理与纸面证明\quad v73.0\\[4pt]
2026 年 11 月 1 日\quad Asia/Singapore
\end{center}
```

</div>
</details>

> **转换者归属说明。** 正文、日期、版本、来源和方法报告来自用户提供的 V73 原稿。19:34:53 的 HEAD GET 预 HTTP 权限拒绝、没有重试或备用活动端点、十份 blob 核对等均为原作者的历史陈述，不是本次执行或自动审批拒绝报告。本转换仅承担纸面、固定来源与本地呈现范围；不构成形式核验、原生控制、物理经验、全上游、无条件起源、全局最小性或优先权认证。

# 从前缀态到最小闭合关系体
用整组已知关系确定维数、门与递归
AURIC 量子起源研究　 定义、定理与纸面证明　 v73.0
2026 年 11 月 1 日　 Asia/Singapore


## 摘要

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

本轮把门历史明确表示为全部带顺序的前缀态及其相干关系，而非只有终端态。
核心结果是有限闭合历史体重建：给定 $d+1$ 个归一标签的正 Gram 表，
若前 $d$ 个标签独立、新标签的 Schur 余量为零，且共同一步接续保持全部交叉关系，
则关系表唯一确定一个 $d$ 维最小循环酉实现及全部后续递推。
维数由秩确定，数学可逆性由有限闭合与保内积导出。
二能级实例的闭合式为 $|b-a^2|=1-|a|^2$，将三个前缀态的三角关系变成整个单门轨迹的确定条件。
进一步证明：相干生成帧固定完整门；射线探针则在张成与非正交图连通时固定门通道。
三角闭路相位、正交余核、三轴 Clifford 关系、共同复定向以及完整效果响应
依次说明如何将看似额外的输入改写为可认证的内部相容条件。
四面体读出给出最少四结果的 qubit 层析实例及精确误差界。
最小性始终相对于明确任务；有限关系闭合可以锁定声明的生成部分，
并不独自决定任意未来控制或实际宇宙的全部数值关系。

</div>



<a id="section-1"></a>

## 1. 本轮改变：研究整条前缀态族的关系闭合

**“把关系放在一起，直到剩余自由度被锁定”可以成为一条精确研究路线。**
相同关系数据若只容许共同坐标变换，就已经确定了同一个相对对象；
无需再挑一个本体外的绝对坐标。
本轮进一步问：哪些有限关系能确定一条历史的全部未来？
答案需要包含同名操作的复用、生成帧、交叉关系及闭合条件。

本轮唯一实时 HEAD GET 于新加坡时间 2026-11-01 19:34:53
在收到 HTTP 响应前遇到网络权限拒绝。没有重试、备用活动端点或新提交。
承接十份重新核对 Git blob 的固定快照：
`5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b`。
不声称核实了该提交之后的最新进展。“v73”为本对话稿件编号。




<div tabindex="0" role="region" aria-label="原稿表格；可横向滚动" style="overflow-x:auto;max-width:100%">

| 项目已存在的结果 | 本轮具体承接 |
| --- | --- |
| V22 §§6--8 | 最小 Gram 实现、三角行列式、闭路相位重建与未来稳定观察商。 |
| V28 §6 | 全部 qubit 转移概率表的 Gram 正性、秩与手性判据。 |
| $\Omega$ 静态纤维 §§5、7 | 全部前缀的静态传播核；明确运输、时钟、数据态的不同作用。 |
| V58 §3 | 三个反对易锐分类器在实关系代数内生成中心复单位。 |
| V59 §§2--3 | 完整局部乘积关系锁定共同复定向；关系一致性与方向覆盖给正态。 |

</div>

<details><summary>原始表格制作设置与内容（原样保留）</summary>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

```tex
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.24\textwidth}X@{}}
\toprule
项目已存在的结果 & 本轮具体承接\\
\midrule
V22 §§6--8 & 最小 Gram 实现、三角行列式、闭路相位重建与未来稳定观察商。\\
V28 §6 & 全部 qubit 转移概率表的 Gram 正性、秩与手性判据。\\
$\Omega$ 静态纤维 §§5、7 & 全部前缀的静态传播核；明确运输、时钟、数据态的不同作用。\\
V58 §3 & 三个反对易锐分类器在实关系代数内生成中心复单位。\\
V59 §§2--3 & 完整局部乘积关系锁定共同复定向；关系一致性与方向覆盖给正态。\\
\bottomrule
\end{tabularx}
```

</div>
</details>




全文只作纸面证明，没有运行 CAS、数学数值计算、模拟、候选枚举或门搜索。
标准 Gram、Schur、Clifford、层析及刚性结果不作原创优先权声明。
默认内积对第一变量共轭线性、第二变量线性。
“已知”指同一准备与参考约定下的精确关系；估计误差另以稳定性界处理。


<a id="section-2"></a>

## 2. 唯一来源与每一段前缀态


#### 定义 2.1（完整前缀态族）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

固定唯一单位来源 $\Omega$。对有序门字 $(G_1,\ldots,G_n)$，定义

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
U_0=I,\quad U_k=G_k\cdots G_1,\qquad
\psi_k=U_k\Omega\quad(0\le k\le n).
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


完整前缀轨迹为带标签有序族 $(\psi_0,\ldots,\psi_n)$，
相干关系表为 $K_{jk}=\langle\psi_j,\psi_k\rangle$。

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 本节的归一历史采用同一复 Hilbert 数据空间、单位来源以及酉门（或沿所声明轨迹保范数的线性门）；整数 $n\ge0$，乘积从右向左作用，空前缀为 $I$。子段指标满足 $0\le a\le b\le n$，空子段取 $I$。这不把一般有损、选择后归一化或非线性过程作为同一种酉门。

</div>



<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


这正面保留了“门序列每一段都有对应态”的含义。
对子段 $W_{b:a}=G_b\cdots G_{a+1}$，实际轨迹满足

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\psi_b=W_{b:a}\psi_a.
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


若把该子段重新从来源运行，得到
$\chi_{b:a}=W_{b:a}\Omega$；它也是同源态，但一般不同于 $\psi_b$。
例如先施 $X$ 再施 $I$，从 $|0\rangle$ 得到的实际终态为 $|1\rangle$，
而单独从 $|0\rangle$ 运行第二段 $I$ 得到 $|0\rangle$。
前缀与重新启动的子段都可内生；必须保留其输入上下文。

</div>

项目的静态历史编码已经保留全部前缀 [3](#bib-omega)：


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
|\Xi_n\rangle=\frac1{\sqrt{n+1}}
\sum_{k=0}^n|k\rangle\otimes|\psi_k\rangle.
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


它是一种内部记录表示，不另设第二个本体。
其传播约束
$\mathcal D(x_0,\ldots,x_n)=(x_1-G_1x_0,\ldots,x_n-G_nx_{n-1})$
满足 $\mathcal D^\dagger\mathcal D\ge0$，零空间恰是整条相容轨迹。
这个已知构造把 $G_k$ 当作输入；本轮要研究怎样反过来由关系确定它们。

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 这里 $\mathcal D:\mathcal H^{\oplus(n+1)}\to\mathcal H^{\oplus n}$ 是有限个有界线性门定义的算子，$\ker(\mathcal D^\dagger\mathcal D)=\ker\mathcal D$。其核包含任意初值的相容轨迹；选定本文来源还须另加 $x_0=\Omega$（归一静态向量对应 $x_0=\Omega/\sqrt{n+1}$）。$n=0$ 时约束为空。时钟维数与所需记录、制备和比较容量仍是表示前件。

</div>



若时钟记录永久正交，则完整记录态的关系为


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\langle j\otimes\psi_j,k\otimes\psi_k\rangle
=\delta_{jk}\langle\psi_j,\psi_k\rangle.
$$

</div>


所以数据态的非零跨时刻 Gram 关系，需要声明数据因子或受控相干比较接口。
不能把保留全部档案的完整核与删去时钟标签的数据核混同。
这一接口区别在 V22 §7.6 已明示 [1](#bib-v22)。


<a id="section-3"></a>

## 3. 三条边怎样锁定三角关系


#### 定义 3.1（三态闭路量）

对三个单位态，记


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
K_{ij}=\langle\psi_i,\psi_j\rangle,\qquad
p_{ij}=|K_{ij}|^2,\qquad
\mathcal B=K_{01}K_{12}K_{20}.
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


$\mathcal B$ 是有向三角闭路量；顶点相位重选及共同酉都保持它。

</div>



<a id="thm:triangle"></a>

#### 定理 3.2（三边、秩与手性）



<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
|\mathcal B|^2=p_{01}p_{12}p_{20},\qquad
\det K=1-p_{01}-p_{12}-p_{20}+2\Re\mathcal B\ge0.
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


若三个态的复张成维数至多二，令
$s=(p_{01}+p_{12}+p_{20}-1)/2$，则

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{\mathcal B=s\pm i\sqrt{p_{01}p_{12}p_{20}-s^2}.}
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


对于已实现且三条边非零的非退化情形，三边概率加一个
$\operatorname{sgn}\Im\mathcal B$ 确定整个三态构型到顶点相位与共同酉。

</div>


**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

第一式逐项取模；展开三阶 Gram 行列式得第二式。
秩至多二使行列式为零，从而确定实部，再由模长确定虚部绝对值。
选顶点相位使 $K_{01},K_{02}>0$，则
$K_{12}=\mathcal B/(|K_{01}||K_{02}|)$。
其余项由共轭与归一化确定。共同 Gram 的实现唯一性由下一节证明。

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 本定理最后的“三边概率加符号”是在前述复张成维数至多二的分支内；实现保证根号内非负。虚部为零时符号为零、两根重合，不另产生二选一手性。射线相位作为表示规范时，相干程序系数也须作相反重相位。

</div>



∎


这正是项目 V22 命题 7.5、定理 7.7 的整体相容结构 [1](#bib-v22)。
例如三态


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
|0\rangle,\qquad\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
\frac{|0\rangle\pm i|1\rangle}{\sqrt2}
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


的三边概率都为 $1/2$，闭路量却分别为 $(1\pm i)/4$。
**边关系锁定形状，闭路关系补足朝向。**
相对于已声明内部手性参考固定朝向即可；共同改变全部表示约定不是另一个物理自由参数。

</div>


#### 命题 3.3（闭路拼接重建全图）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

对有限标签上的两个归一 Hermitian 核，若零边模式和非零边模长相同，
则它们相差顶点相位，当且仅当所有非零有向闭路乘积相同。
若存在与全部标签非正交的锚点 $0$，三角量已经足够，且在 $K_{0i}>0$ 的规范中

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{K_{ij}=\frac{\mathcal B(0,i,j)}{|K_{0i}|\,|K_{0j}|}.}
$$

</div>




**证明。**

顶点相位沿闭路相消。反向在每个连通分量选生成树，
沿树调相使两个核的树边相同；每条非树边与树路径构成闭路，
闭路相同及树边非零强制该边相同。锚点情形即一张星形生成树。

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


零边是实际边界。四环若两条弦为零，所有三角乘积都可为零，而四环相位仍可自由。
例如对角一、四环边模长 $0<t<1/2$、仅一边带相位的矩阵满足
$x^\dagger Kx\ge(1-2t)\|x\|^2>0$。

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 严格大于零针对 $x\ne0$；零向量时两端均为零。这里“所有三角”指三个不同顶点，四环非零闭路仍须单独保留。Pauli 公式以下采用 $\sigma_x\sigma_y=i\sigma_z$、右手叉积与本文第二变量线性的内积约定。

</div>


所以不能把“每段可画成三角形”升级为“没有非零弦也已知道全部闭路”。

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

在已知 qubit 表示中，$P_j=(I+r_j\cdot\sigma)/2$，Pauli 乘法给

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\operatorname{Tr}(P_1P_2P_3)=\frac14\bigl(
1+r_1\cdot r_2+r_2\cdot r_3+r_3\cdot r_1
+i\,r_1\cdot(r_2\times r_3)\bigr).
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


因此虚部是有向体积的四分之一。
对实对称候选转移概率表 $p$，设 $p_{ii}=1$。
它来自同一 qubit 空间内一族纯态的充要条件是

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
G_{ij}=2p_{ij}-1\succeq0,\qquad\operatorname{rank} G\le3.
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


证明只需把 $G$ 看作单位 Bloch 向量的实 Gram 矩阵；反向作实 Gram 实现。
这也是项目 V28 定理 6.1 [2](#bib-v28)。

</div>


<a id="section-4"></a>

## 4. 最小参考关系体与零余核


<a id="thm:gram"></a>

#### 定理 4.1（完整相干关系确定最小实现）

两族向量有相同 Gram 表，当且仅当它们的张成空间间存在
保持各标签的满等距。最小实现的维数等于 Gram 秩。


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 本节的矩阵秩、列映射伴随与后续逆矩阵证明用于有限标签、有限参考维数。任意无限标签族仍有有限线性组合上的唯一满等距，并延拓到闭张成空间；完备 Hilbert 维数不能无说明地等同于无限矩阵的代数秩。

</div>




**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

定义 $\sum c_i\psi_i\mapsto\sum c_i\phi_i$。
两边范数平方由同一个 Gram 二次型给出，故零关系一致，映射良定义且保内积。
标签张成给满射与唯一性。
若列映射为 $A$，则 $\ker A^\dagger A=\ker A$，所以
$\operatorname{rank} K=\operatorname{rank} A$ 等于张成维数。

</div>

∎



#### 定义 4.2（参考关系体与余核）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

取 $d$ 个独立内部参考态 $b_1,\ldots,b_d$，令列映射 $A e_i=b_i$，
$H=A^\dagger A>0$。对任意标签态 $x$，定义

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
c(x)=A^\dagger x,\qquad
\widehat x=AH^{-1}c(x),\qquad r_x=x-\widehat x.
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


$\widehat x$ 为在 $M=\operatorname{span}\{b_i\}$ 上的投影，$r_x\perp M$。

</div>



<a id="thm:schur"></a>

#### 定理 4.3（已知关系何时完全锁定新对象）



<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{K(x,y)=c(x)^\dagger H^{-1}c(y)+R(x,y),
\qquad R(x,y)=\langle r_x,r_y\rangle.}
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


$R$ 为正核。以下条件等价：全部声明对象属于 $M$；
每个对角余量 $R(x,x)$ 为零；整个余核为零。
此时全部关系唯一由 $H$ 与参考重叠 $c(x)$ 决定。
对有限标签集，包含参考态的完整矩阵满足

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{\operatorname{rank} K_{\rm full}=d+\operatorname{rank} R.}
$$

</div>




**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

$A^\dagger r_x=0$，所以交叉项消失，给分解。
正性来自 $\sum\bar z_iR(x_i,x_j)z_j=\|\sum z_ir_{x_i}\|^2$。
对角零使各 $r_x=0$；反向立即成立。
分块矩阵 $\left(\begin{smallmatrix}H&C\\mathbb C^\dagger&B\end{smallmatrix}\right)$
以可逆合同变为 $H\oplus(B-C^\dagger H^{-1}C)$，后块正是 $R$，故得秩式。

</div>

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


这给“锁死”一个实际判据：**余量为零，已有关系完全决定对象；
余量非零，其秩精确指出仍缺多少独立方向。**
这些方向属于同一整体内部，不是本体之外的输入。
在“完整复重叠恢复任意向量”的任务中，$d$ 个独立参考也是最少的：
少于 $d$ 个留下非零正交补，不能分离该补空间中的向量。

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 此处任意向量恢复的目标是已声明的 $d$ 维生成空间 $M$，观测是相对于这些参考的完整复重叠；若目标还包含更大的正交补，已有 $d$ 个参考同样不足。

</div>




#### 命题 4.4（关系认证与稳定性）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

若 $b_i$ 张成 $M$，则线性算符 $F$ 在 $M$ 上为零，当且仅当 $Fb_i=0$ 对所有 $i$ 成立。
若 $U,V$ 满足 $\|(U-V)b_i\|\le\varepsilon_i$，则

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 此误差式沿用前述独立的有限参考基，$U,V$ 为在 $M$ 上定义、取值于同一 Hilbert 空间的线性算符，$\varepsilon_i\ge0$；$A^{-1}$ 的域是 $M$。若只给相关的生成族，$H$ 不可逆，不能直接使用所列分母。

</div>




<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{\|U-V\|_{M\to\mathcal H}
\le\frac{\sqrt{\sum_i\varepsilon_i^2}}{\sqrt{\lambda_{\min}(H)}}.}
$$

</div>




**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

零关系由线性性传播。对一般误差令 $E=(U-V)A$，
则 $U-V=EA^{-1}$ 于 $M$，
$\|E\|_{\rm op}\le\|E\|_{\rm HS}\le\sqrt{\sum_i\varepsilon_i^2}$，
$\|A^{-1}\|=1/\sqrt{\lambda_{\min}(H)}$。

</div>

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


已知量若是有限精度估计，结论是上述误差界；
参考态几乎线性相关时，误差会放大。精确刚性与稳健估计需要分别说明。
若 $H$ 也由估计获得，应用此界需要认证真实 $\lambda_{\min}(H)$ 的正下界，
不能直接代入未经误差校正的估计值。

</div>


<a id="section-5"></a>

## 5. 主定理：有限闭合历史体决定酉门和全部未来


<a id="def:body"></a>

#### 定义 5.1（单门闭合历史关系体）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

给 $d+1$ 个标签 $0,\ldots,d$ 的 Hermitian 关系表 $G$。

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 本定义取整数 $d\ge1$。主证明的 $T^\dagger$ 是坐标矩阵的通常共轭转置；相对于 $H$ 内积的 Hilbert 伴随为 $H^{-1}T^\dagger H$，故 $T^\dagger HT=H$ 正是 $H$ 酉性。最小性和全部后续只针对这里反复使用的同一门及其循环生成部分。

</div>


令


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
H=(G_{jk})_{0\le j,k<d},\qquad
y=(G_{0d},\ldots,G_{d-1,d})^{\mathsf T}.
$$

</div>


要求：

1. $G\succeq0$、$G_{jj}=1$、$H>0$；
2. 新标签无额外方向：$1-y^\dagger H^{-1}y=0$；
3. 同一步接续保持全部交叉关系：
$G_{j+1,k+1}=G_{jk}$，$0\le j,k<d$。

把同一个操作标签继续用于后续各步，是本关系体声明的递归语义。



<a id="thm:closed"></a>

#### 定理 5.2（最小闭合历史体重建）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

定义 [5.1](#def:body) 的数据唯一确定一个 $d$ 维最小实现
$(\mathcal H_G,U,\Omega)$，到保持历史标签的共同酉同构为止，使

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\psi_j=U^j\Omega\ (0\le j\le d),\qquad
\langle\psi_j,\psi_k\rangle=G_{jk}.
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


若 $c=H^{-1}y$，则同门的全部后续历史满足

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{\psi_{n+d}=\sum_{j=0}^{d-1}c_j\psi_{n+j}\qquad(n\ge0).}
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


其最小维数是 $\operatorname{rank} G=d$，且 $U$ 的数学逆自动存在。

</div>


**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

在 $\mathbb C^d$ 上定义内积 $\langle x,z\rangle_H=x^\dagger Hz$。
令 $\Omega=e_0$、$\psi_j=e_j$（$j<d$）、$\psi_d=c$。
$Hc=y$ 给新标签与参考标签的全部重叠；零余量给 $c^\dagger Hc=1$。
所以这些向量的 Gram 恰为 $G$。

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

定义线性 $T$ 使 $Te_j=\psi_{j+1}$。
共同接续关系给

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{T^\dagger HT=H.}
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


故 $T$ 保内积。有限等维的等距为单射及满射，因此 $U=T$ 为酉，
无需预先把逆操作作为另一公理。
首 $d$ 个标签张成全部空间，Gram 唯一性及基上的作用唯一性给实现唯一。
$\psi_d=\sum c_j\psi_j$ 上作用 $U^n$，得到全部递推。
Schur 秩式给 $\operatorname{rank} G=d$。

</div>

∎



#### 推论 5.3（较大本体中的来源生成部分仍被锁定）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

若这些数据在更大空间中由同一个酉 $U$ 实现，令
$M=\operatorname{span}\{\psi_0,\ldots,\psi_{d-1}\}$，则 $U(M)=M$。
因此该来源在此单门下的全部正反历史都留在 $M$。

</div>


**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

零 Schur 余量使 $\psi_d\in M$。
移位后 $d$ 个态的 Gram 仍为正定 $H$，所以它们也张成 $M$。
故 $U(M)=M$，并有 $U^{-1}(M)=M$。

</div>

∎


这里确实消去了一项看似额外的输入：*最小维数不必先由外部给出，而由闭合关系的秩得到。*
有限闭合还将保内积升级为可逆；无限维时单边移位说明这一步不能省略有限闭合。
数学逆存在不自动供应原生逆门的物理控制。


### 三个前缀态：最小非平凡闭合实例


<a id="cor:three"></a>

#### 推论 5.4（相干三角形锁定二能级递推）

设


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
G=\begin{pmatrix}
1&a&b\\\bar a&1&a\\\bar b&\bar a&1
\end{pmatrix},\qquad |a|<1.
$$

</div>


它半正定且秩二，当且仅当


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{|b-a^2|=1-|a|^2.}
$$

</div>


此时唯一最小循环实现满足


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{\psi_{n+2}=c_0\psi_n+c_1\psi_{n+1},}
\qquad
c_0=\frac{b-a^2}{1-|a|^2},\quad
c_1=\frac{a-\bar a b}{1-|a|^2},\quad |c_0|=1.
$$

</div>




**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

首二态 Gram 为
$H=\left(\begin{smallmatrix}1&a\\\bar a&1\end{smallmatrix}\right)>0$，
$y=(b,a)^{\mathsf T}$。

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
H^{-1}=\frac1{1-|a|^2}
\begin{pmatrix}1&-a\\-\bar a&1\end{pmatrix}
$$

</div>


给出所列系数。Schur 余量整理为


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
1-y^\dagger H^{-1}y
=\frac{(1-|a|^2)^2-|b-a^2|^2}{1-|a|^2}.
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


零余量与所列等式等价；$H>0$ 加零余量充分保证 $G\succeq0$、秩二。
相邻重叠同为 $a$ 已给移位关系，应用主定理。

</div>

∎



<div tabindex="0" role="region" aria-label="三个前缀态闭合关系图；可横向滚动" style="overflow-x:auto;max-width:100%">
<svg xmlns="http://www.w3.org/2000/svg" width="900" height="270" viewBox="-70 -10 900 270" role="img" aria-label="ψ₀、ψ₁、ψ₂ 三角形；两条同一 U 重叠 a 的有向边，底边跨两步关系 b；右方三行闭合说明" style="min-width:900px">
<defs><marker id="v73-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="rgb(24,53,79)"/></marker></defs>
<g fill="none" stroke-width="2"><path d="M 87 159 L 189 81" stroke="rgb(24,53,79)" marker-end="url(#v73-arrow)"/><path d="M 243 81 L 345 159" stroke="rgb(24,53,79)" marker-end="url(#v73-arrow)"/><path d="M 93 180 L 339 180" stroke="rgb(153,105,29)"/></g>
<g fill="white" stroke="rgb(24,53,79)" stroke-width="2"><circle cx="60" cy="180" r="33"/><circle cx="216" cy="60" r="33"/><circle cx="372" cy="180" r="33"/></g>
<g font-family="sans-serif" font-size="16" fill="rgb(24,53,79)"><text x="60" y="186" text-anchor="middle">ψ₀</text><text x="216" y="66" text-anchor="middle">ψ₁</text><text x="372" y="186" text-anchor="middle">ψ₂</text><text x="127" y="96" text-anchor="end">同一 U；重叠 a</text><text x="305" y="96">同一 U；重叠 a</text></g>
<text x="216" y="218" text-anchor="middle" font-family="sans-serif" font-size="16" fill="rgb(153,105,29)">跨两步关系 b</text>
<g font-family="sans-serif" font-size="16" fill="black"><text x="504" y="92">零余量锁定闭包。</text><text x="504" y="128">相同交叉关系锁定酉作用。</text><text x="504" y="164">同一规则决定全部后续。</text></g></svg>
</div>

<details><summary>原始 TikZ 图形、坐标与标签（原样保留）</summary>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

```tex
\begin{tikzpicture}[>=Stealth,font=\small]
\node[circle,draw=auricblue,thick,minimum size=11mm] (p0) at (0,0) {$\psi_0$};
\node[circle,draw=auricblue,thick,minimum size=11mm] (p1) at (2.6,2) {$\psi_1$};
\node[circle,draw=auricblue,thick,minimum size=11mm] (p2) at (5.2,0) {$\psi_2$};
\draw[->,thick,auricblue] (p0)--node[above left] {同一 $U$；重叠 $a$}(p1);
\draw[->,thick,auricblue] (p1)--node[above right] {同一 $U$；重叠 $a$}(p2);
\draw[thick,auricgold] (p0)--node[below=3pt] {跨两步关系 $b$}(p2);
\node[align=left,text width=4.8cm] at (9.8,1)
{零余量锁定闭包。\\[4pt]
相同交叉关系锁定酉作用。\\[4pt]
同一规则决定全部后续。};
\end{tikzpicture}
```

</div>
</details>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


取 $a=1/\sqrt2$、$b=0$，可实现为

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\psi_0=|0\rangle,\qquad
\psi_1=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad\psi_2=|1\rangle.
$$

</div>


这三点锁定


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
U=\frac1{\sqrt2}\begin{pmatrix}1&-1\\1&1\end{pmatrix},
\qquad
\boxed{\psi_{n+2}=\sqrt2\,\psi_{n+1}-\psi_n.}
$$

</div>


验证前两次输入输出即可，唯一性由主定理给出，不需要枚举后续历史。
无限递归可以由有限关系决定；历史长度增长不等于独立自由度必然增长。

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

对一般 $a,b$，若另给 $\det U=1$，则伴随矩阵行列式 $-c_0$ 强制
$c_0=-1$、$c_1=2\Re a$。
这说明新加入的整体关系如何继续收紧允许结构。
若只知道 $|a|,|b|$，则不能省略相干相位并直接使用本推论。

</div>


<a id="section-6"></a>

## 6. 多个门怎样由同一关系体锁定


<a id="thm:framegate"></a>

#### 定理 6.1（相干输入输出帧确定完整门）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

给同一个 $d$ 维空间中的独立输入 $a_1,\ldots,a_d$ 和输出 $b_1,\ldots,b_d$。
存在唯一酉 $U$ 满足 $Ua_j=b_j$，当且仅当两组 Gram 完全相同。
若 $A,B$ 是列映射，则

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{U=BA^{-1}=B(A^\dagger A)^{-1}A^\dagger.}
$$

</div>




**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

酉保内积给必要性。反向定义 $U(Ac)=Bc$；Gram 相同使范数保持，
正定 Gram 使输出也为基，所以 $U$ 满等距。基上的值给唯一性。

</div>

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


因此，历史图中具有同一门名的边若共享一套操作语义，
并且其输入态共同张成空间，就能用整组边约束锁定该门。
所有这些输入都可以是不同前缀从同一个 $\Omega$ 制备的态。

</div>

若每一步都是独立未知门，则即使知道整个前缀态族，也可以作


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
G_k\longmapsto G_kS_k,\qquad S_k\psi_{k-1}=\psi_{k-1},
$$

</div>


而保持所有前缀不变。


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 保持酉门类时，$S_k$ 也取酉且固定该输入向量；这是右乘稳定子自由度。$U(M^\perp)$ 以下表示余空间上的整个酉群，不是一个已经指定的门。

</div>


**补足决定性关系的方法是同名操作跨输入上下文的复用，
而不是仅增加同一输入输出对的重复标签。**


#### 命题 6.2（完整门的最小输入张成）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

若受约束输入只张成 $r<d$ 维子空间 $M$，且存在一个酉解 $U_0$，
则全部解为

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
U_0\bigl(I_M\oplus U(M^\perp)\bigr).
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


故在不另给行列式的 $U(d)$ 内，满张成是唯一确定完整门的必要充分条件。

</div>


**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

$U_0^\dagger U$ 在 $M$ 上逐点恒等，酉性使其保持 $M^\perp$，
后者上的酉任意；反向直接成立。

</div>

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


一条同门轨迹需要 $d$ 次独立输入约束，即 $d+1$ 个相干前缀标签，
达到上述任务的界。若行列式已经固定，$d-1$ 个独立输入可能足够；
这与上一轮固定 $SU(2)$ 中一列决定整个门的结论相容。

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 所承接的 V72 原始稿“单位二元对与特殊酉门”证明固定有序正交二元基底，并以行列式一消除第二列相位。在本节一般 $U(d)$ 的相干输入输出任务中，$d+1$ 前缀的界还要求前 $d$ 个输入确实独立；它不声称每个来源对任意门都具有 $d$ 维循环轨道。

</div>




<a id="thm:ray"></a>

#### 定理 6.3（射线关系的连通性锁定相对相位）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

在维数 $d\ge2$ 的空间中给有限非空探针族，其输入态 $a_j$ 均非零，
在 $\langle a_j,a_k\rangle\ne0$ 时连边。
若两酉 $U,V$ 在每个输入上给同一个输出射线，则

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
V^\dagger U=
\left(\bigoplus_{\ell}e^{i\theta_\ell}I_{M_\ell}\right)\oplus W_{M^\perp},
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


其中 $M_\ell$ 为各连通分量的张成空间，$M=\bigoplus M_\ell$。
所以输入满张成且非正交图连通，当且仅当这些探针确定门通道到整体相位。

</div>


**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

令 $W=V^\dagger U$，有 $Wa_j=\lambda_ja_j$、$|\lambda_j|=1$。
酉性给

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\langle a_j,a_k\rangle
=\bar\lambda_j\lambda_k\langle a_j,a_k\rangle.
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


非零边强制 $\lambda_j=\lambda_k$，连通性传播到整个分量。
不同分量两两正交，故得到所列直和；余空间不受约束。
反向任选各分量相位及余空间酉，都保持探针的输出射线。

</div>

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


正交基探针彼此没有边，留下独立列相位。
加入一个已知全支撑叠加态即可把它们连起来；
也可以直接用 $d$ 个独立且非正交图连通的输入，如
$a_1=e_1$、$a_j=(e_1+e_j)/\sqrt2$（$j>1$）。
这是“关系拼起来”在门辨识中的精确形式。

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

仅增加前缀射线的长度未必补足相位。
$X$ 与 $V_\phi=\left(\begin{smallmatrix}0&e^{i\phi}\\1&0\end{smallmatrix}\right)$
从 $|0\rangle$ 出发的全部前缀射线都在 $[|0\rangle]$、$[|1\rangle]$ 间交替，
但一般对应不同通道。$V_\phi^2=e^{i\phi}I$ 的相干关系能够辨别这个差别。

</div>


<a id="section-7"></a>

## 7. 把复结构和共同相位变成内部关系的结论


### 在生成帧上认证算子关系

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

若 $b_i$ 张成已声明的生成部分，则

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
F(X,Y,Z)b_i=0\quad\text{对所有 }i
\quad\Longrightarrow\quad F(X,Y,Z)=0.
$$

</div>


因此需要的反射、相容及反对易关系，可以作为整组已知响应能够认证的条件，
无需永远停留在不可追问的外部名称上。
这里要求向量残差为零，或等价地其平方范数为零；单个期望值为零一般不够。


<a id="thm:complex"></a>

#### 定理 7.1（三轴关系在实代数内产生复单位）

在实含幺伴随代数的有界表示中，若


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
X^*=X,\ Y^*=Y,\ Z^*=Z,\qquad X^2=Y^2=Z^2=I,
$$

</div>




<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
XY=-YX,\qquad YZ=-ZY,\qquad ZX=-XZ,
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


则 $J=XYZ$ 满足

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{J^2=-I,\qquad J^*=-J,\qquad [J,X]=[J,Y]=[J,Z]=0.}
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


相应普遍实代数为 $\operatorname{Cl}_{3,0}\cong M_2(\mathbb C)_{\mathbb R}$。

</div>


**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

逆序交换三次给 $J^*=-J$、$J^2=-I$；
任一生成元穿过另两个只产生两次负号，所以 $J$ 中心。

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 中心性限于 $X,Y,Z$ 生成的关系代数；不推出它与任意外加算符或任意声明控制对易。普遍代数同构不表示任一载体表示没有重数，也不由此确定表示 Hilbert 空间的维数。

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


所有词归约到 $I,X,Y,Z,XY,YZ,ZX,J$ 的实张成。
Pauli 表示将它们送到 $I,\sigma_x,\sigma_y,\sigma_z, i\sigma_z,i\sigma_x,i\sigma_y,iI$，八者实线性独立并张成 $M_2(\mathbb C)$，
故恰为同构。

</div>

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


这是项目 V58 §3 的既有定理 [4](#bib-v58)。
它把复单位写成关系乘积；其上游条件仍是三轴、实线性、锐性及特定复合律。
例如若整个方向族满足
$B(n)=n_1X+n_2Y+n_3Z$、$B(n)^2=\|n\|^2I$，
对 $n=e_i+e_j$ 展开即可认证反对易关系。
单纯的三个标签没有这些代数信息。

</div>


<a id="prop:central"></a>

#### 命题 7.2（一个中心确定值传播到全部历史）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

设 $c\in\mathbb R$，有界自伴 $C$ 与全部声明门 $U_g$ 对易，
且门字轨道 $\operatorname{span}\{U_w\Omega:w\text{ 为声明门字}\}$ 稠密。
若

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\langle\Omega,(C-cI)^2\Omega\rangle=0,
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


则 $C=cI$ 于整个生成空间。

</div>


**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

平方范数为零给 $(C-cI)\Omega=0$。
中心性给 $(C-cI)U_w\Omega=U_w(C-cI)\Omega=0$。
线性稠密性与有界性将恒等式扩到全空间。

</div>

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


这是一种直接用“已知量”锁定全局关系的机制。
对两个相互对易的三轴原子，令 $J_1,J_2$ 为各自复单位，
$s=-J_1J_2$ 为中心自伴对合。
若内部中心读数
$\langle\Omega,(I+s)\Omega/2\rangle$ 为 $0$ 或 $1$，
且满足上命题的循环生成条件，则上式强制 $s=\pm I$，所以 $J_2=\pm J_1$。
重标局部手性后即共享同一个复单位。

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 应用上一命题还须 $s$ 与全部声明门对易，不能仅由它在这两个原子生成代数的中心内推出该条件。读数 $q=\langle\Omega,(I+s)\Omega/2\rangle$ 为一给 $s=I$、$J_2=J_1$，为零给 $s=-I$、$J_2=-J_1$；使用投影方差为零及稠密循环性传播。

</div>




<a id="thm:orientation"></a>

#### 定理 7.3（全部局部乘积关系锁定共同复定向）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

对 $N$ 个彼此对易的三轴原子，取其普遍实代数的非零含幺伴随商。

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 这里 $N\ge1$ 是有限整数，不同原子的全部生成元彼此对易；每个原子效果采用其完整有限矩阵正锥中的 $0\le E\le I$。局部效果的线性张成含 $I,X,Y,Z$，所以乘积张成数确为 $4^N$。单块结论属于这个有限实代数商类，不是任意系统、任意复合或物理控制的无条件分类。

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


若局部效果乘积的实线性张成等于全部自伴关系空间，
则该商只保留一个相对复定向扇区，且同构于 $M_{2^N}(\mathbb C)_{\mathbb R}$。
反向，单扇区中局部乘积关系完备。

</div>


**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

令 $s_r=-J_1J_r$（$r\ge2$），它们为对易中心自伴对合。
中心投影
$e_\epsilon=2^{1-N}\prod_{r=2}^N(I+\epsilon_rs_r)$
把普遍代数分解为 $2^{N-1}$ 个块。
在第 $\epsilon$ 块中以 $J_1=iI$，约定 $\epsilon_1=1$，取
$X_r=\sigma_x^{(r)}$、$Z_r=\sigma_z^{(r)}$、
$Y_r=\epsilon_r\sigma_y^{(r)}$。
块内 $J_r=\epsilon_rJ_1$，所有词由 $D^2$ 个 Pauli 型自伴词及其 $J_1$ 倍实线性张成，
其中 $D=2^N$。上述表示中这些 $2D^2$ 个词实线性独立，
所以每块恰为 $M_D(\mathbb C)_{\mathbb R}$。

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

每块为简单实代数，所以非零商只保留 $m\ge1$ 个完整块，
自伴部实维数为 $mD^2$。
局部效果乘积由 $4^N=D^2$ 个 Pauli 型词张成，
投影到任一保留块都线性独立，故其张成恰为 $D^2$ 维。
完备性因此当且仅当 $m=1$。

</div>

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


这是项目 V59 定理 2.4 的证明核心 [5](#bib-v59)。
它要求完整关系空间的覆盖；唯一 $\Omega$ 及某条受限轨道上的读出充分性并不自动给此覆盖。
单个共同坐标规范不必被物理区分，真正要锁定的是不同内部因子之间的相对定向。

</div>

一般量子重建也使用系统、复合与层析的联合条件。
Barnum--Wilce 的路线在齐性自对偶或相应 Jordan 结构、局部层析、适当复合与自对偶结构的因子化条件、
以及一个 qubit 存在等前件下得到复量子结构；
它没有仅由“存在二元分类”推出量子论 [7](#bib-barnum)。
本节的具体有限代数证明不依赖该一般分类定理。


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** Barnum–Wilce v2 引言的命题 1 用有限维 factorizably HSD 理论、每对系统在同一理论中存在局部层析复合，以及至少一个 qubit；自对偶内积在复合上可因子化。其 Hanche-Olsen 条件是与 qubit 的向量空间张量积上 Jordan 乘法的两个相容恒等式。这里仅援引这条路线的明确前件，不重证该分类及其全部上游。

</div>




<a id="section-8"></a>

## 8. 归一化、正性和概率怎样由完整读出关系确定


#### 定义 8.1（共同响应的关系一致性）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

在已确定的 $M_d(\mathbb C)$ 关系代数中，实际效果菜单 $\mathcal E$
含 $I$ 并实线性张成 $\operatorname{Herm}_d$。
同一来源响应 $p:\mathcal E\to\mathbb R$ 满足 $p(I)=1$，且

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{\sum_j c_jE_j=0\quad\Longrightarrow\quad
\sum_j c_jp(E_j)=0\qquad(c_j\in\mathbb R).}
$$

</div>


所有项须属于同一个准备与条件化约定。



<a id="thm:rho"></a>

#### 定理 8.2（整体关系确定唯一状态矩阵）

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

上述条件给出唯一 Hermitian 矩阵 $W$，满足
$\operatorname{Tr} W=1$、$p(E)=\operatorname{Tr}(WE)$。
若 $\mathcal E$ 含一组稠密覆盖全部秩一投影的声明方向，
且同一个响应 $p$ 在这些方向上非负，则 $W\succeq0$。

</div>


**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

定义 $\ell(\sum c_jE_j)=\sum c_jp(E_j)$。
关系一致性使其良定义，菜单张成给整个 Hermitian 空间上的唯一实线性泛函。
非退化迹配对给唯一 $W$，$p(I)=1$ 给迹一。
对声明方向 $P_\phi$ 有 $\operatorname{Tr}(WP_\phi)\ge0$；
有限维连续性将它传到所有秩一方向，所以全部二次型非负，即 $W\succeq0$。

</div>

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


因此完整相容的响应锁定 $\rho=W$，而纯态
$\rho=|\psi\rangle\langle\psi|$ 对秩一读口给

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{p(P_\phi)=\operatorname{Tr}(\rho P_\phi)=|\langle\phi,\psi\rangle|^2.}
$$

</div>


这是项目 V59 §§3 的关系路线 [5](#bib-v59)。


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 迹平方律中 $\psi,\phi$ 为同一复 Hilbert 空间中的单位向量，$P_\phi=|\phi\rangle\langle\phi|$。若实际校准读口是正增益 $cP_\phi$，须先保留同一准备的增益 $c>0$ 再除以它；零增益不提供该正性信息。

</div>


正性可以由一个校准秩一读口的充分实际控制轨道认证，
不必把每个数学效果都作为独立硬件输入。
但抽象可达不等于某条实际前缀已经取得所有这些响应。
推导的实际前件是响应的线性相容、非负性及上述矩阵关系结构；
二次几何已进入 Gram 正性与锐三轴条件，所以这是一种量子公理的重组与条件重建。


### 一个具体最小读出体：四面体

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

在已知 qubit 中取四个单位方向 $n_i$，满足
$n_i\cdot n_j=-1/3$（$i\ne j$）。它们可取正四面体的四个顶点方向。
定义

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
E_i=\frac{I+n_i\cdot\sigma}{4},\qquad
\rho=\frac{I+r\cdot\sigma}{2}.
$$

</div>



<a id="thm:tetra"></a>

#### 定理 8.3（四结果的归一三维关系体）

这些效果构成 POVM，且


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{p_i=\frac{1+n_i\cdot r}{4},\qquad
r=3\sum_{i=1}^4p_i n_i.}
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


对归一实四元组 $\sum p_i=1$，

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{\|r\|^2=12\sum_i p_i^2-3.}
$$

</div>


所以合法 qubit 分布恰满足


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{\sum_i p_i=1,\quad p_i\ge0,\quad
\sum_i p_i^2\le\frac13,}
$$

</div>


纯态恰在平方等号上。


**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

四向量 Gram 为 $\frac43I_4-\frac13\mathbf1\mathbf1^{\mathsf T}$，秩三，
且 $\sum n_i=0$。
对每个 $n_j$ 作用可知 $\sum_i n_in_i^{\mathsf T}=\frac43I_3$。
$E_i$ 的特征值为 $0,1/2$，总和为 $I$。
迹配对给 $p_i$，上述两项向量恒等式给逆。
再用点积关系得到

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\left\|3\sum_i p_i n_i\right\|^2
=9\left[\sum_i p_i^2-\frac13\sum_{i\ne j}p_ip_j\right]
=12\sum_i p_i^2-3.
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


反向，重建的 $r$ 满足 $n_i\cdot r=4p_i-1$；
平方界给 $\|r\|\le1$，因此 $\rho\succeq0$ 并恢复原分布。
秩一与 $\|r\|=1$ 等价。

</div>

∎



#### 定理 8.4（最小结果数与误差界）

在“单个固定仿射测量完整辨认全部 qubit 密度态”的任务中，结果数至少为四。
上述四面体达到此界。对两个合法分布，


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 下方原式按原稿保留了换行后的字面 $ho\prime$，它不是已定义的第二个密度算符。紧随的原证明使用 $\rho-\rho\prime$；所支持的距离恒等式为 $\tfrac12\|\rho-\rho\prime\|_1=\sqrt3\,\|p-p\prime\|_2$，其中两个归一合法分布以同一四面体逆式对应 $\rho,\rho\prime$。这是明确的记号勘误说明，不替换原式。

</div>




<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{\frac12\|\rho-
ho'\|_1
=\sqrt3\,\|p-p'\|_2.}
$$

</div>




**证明。**

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

$m$ 结果归一分布只有 $m-1$ 个独立实坐标。
当 $m-1<3$，从 Bloch 球的三维内部到该空间的仿射映射有非零核方向，
在内部取两个足够小的相反偏移就不可区分。
四面体的显式逆给可达性。
对 $\delta p$ 有 $\sum\delta p_i=0$，点积公式给
$\|\delta r\|^2=12\sum\delta p_i^2$。
$\rho-\rho'=(\delta r\cdot\sigma)/2$ 的特征值为
$\pm\|\delta r\|/2$，故迹距离为 $\|\delta r\|/2$。

</div>

∎

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


这就是二能级 SIC 测量的正四面体实例；对称信息完备测量已有标准文献 [6](#bib-sic)。
合法概率集合为
$\sum_i(p_i-1/4)^2\le1/12$ 的三维球，
它与四个探针方向组成的四面体是不同对象。
$p=(1,0,0,0)$ 虽是普通归一分布，却重建出 $r=3n_1$，不是量子合法态。

</div>

这项四结果最小性不意味着一次样本就能层析，也不证明原生控制成本最少。
AURIC 原生五模式仍按其固定编码与标签运行；
本节提供一个用于比较“归一三维读出最少需要多少结果”的数学参照，
没有把原五模式直接删成四模式。


<a id="section-9"></a>

## 9. 更紧凑的公理结构与准确的最小性

本轮可以用三个清楚的原则组织已有结果。


#### 定义 9.1（闭合关系重建原则）

**C1：完整关系相容。**
同一来源的声明概念、参考、前缀态及程序具有共同相干关系；
所有有限复合组合满足正性，关系的不同表达给同一响应。
在固定矩阵模型中，可用 Gram 表、闭路相位与生成帧表达。

**C2：生成关系闭合。**
选定的最小参考关系体对声明操作闭合：后继的正交余量为零，
同名操作保持全部交叉关系。
有限闭合部分由此重建酉门；若新的方向确实出现，则保留非零余核并扩大关系体。

**C3：记录和复合覆盖。**
整体关系须由声明的内部读出及局部乘积关系完整区分，
并保留同一准备、相位和条件化约定。
概率响应归一、非负且保持效果关系。
三轴锐关系及共同复定向，可按第七节的关系认证给出具体上游条件。

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


这些标题不是省略前件的许可。
它们把“复结构、酉性、归一化和概率”分别落在可以证明或证伪的关系上。
对有限闭合体，给出 $H>0$、各同名动作的坐标矩阵 $T_a$，
并认证 $T_a^\dagger HT_a=H$，所有门词 $w$ 的关系便由

</div>


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{K(w,v)=e_0^\dagger T_w^\dagger H T_v e_0}
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


确定。这里 $\Omega=e_0$ 为该内部帧中的同一来源；

</div>


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** 这里仍需 $e_0^\dagger H e_0=1$、整数有限维数、处处合法的相同坐标动作与一致的门词乘法顺序。正核来自共同实现的有限线性组合范数，不把只知道各个单独概率当作已取得全部交叉关系。

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


每段前缀都保留为 $T_w e_0$，整个脚本记录另在需要时保留。

</div>




<div tabindex="0" role="region" aria-label="原稿表格；可横向滚动" style="overflow-x:auto;max-width:100%">

| 要锁定的对象 | 充分关系 | 本文的最小性范围 |
| --- | --- | --- |
| 有限态族 | 完整 Gram 或边模长加足够闭路 | 最小维数为 Gram 秩 |
| 任意向量的相干坐标 | $d$ 个独立参考重叠 | 任意向量恢复需满张成 |
| 一般 $U(d)$ 门 | 同名动作在完整输入帧上的输出 | 不另固定行列式时需 $d$ 个独立输入 |
| 单门的闭合未来 | 零 Schur 余量与移位关系 | $d+1$ 个相干前缀标签 |
| 酉通道的射线辨识 | 满张成且非正交图连通 | 只保留不可观测整体门相位 |
| 单 qubit 全态读出 | 四面体效果与合法概率球 | 单个固定仿射 POVM 至少四结果 |
| 共同复结构 | 锐三轴关系及完整复合相容 | 明确的有限实代数商类 |

</div>

<details><summary>原始表格制作设置与内容（原样保留）</summary>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

```tex
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.26\textwidth}XX@{}}
\toprule
要锁定的对象 & 充分关系 & 本文的最小性范围\\
\midrule
有限态族 & 完整 Gram 或边模长加足够闭路 & 最小维数为 Gram 秩\\
任意向量的相干坐标 & $d$ 个独立参考重叠 & 任意向量恢复需满张成\\
一般 $U(d)$ 门 & 同名动作在完整输入帧上的输出 & 不另固定行列式时需 $d$ 个独立输入\\
单门的闭合未来 & 零 Schur 余量与移位关系 & $d+1$ 个相干前缀标签\\
酉通道的射线辨识 & 满张成且非正交图连通 & 只保留不可观测整体门相位\\
单 qubit 全态读出 & 四面体效果与合法概率球 & 单个固定仿射 POVM 至少四结果\\
共同复结构 & 锐三轴关系及完整复合相容 & 明确的有限实代数商类\\
\bottomrule
\end{tabularx}
```

</div>
</details>




所以“最小关系体”不是无条件的一个节点数，而是**在指定任务下，
删去任何决定性关系就会留下可区分自由度的关系集合**。
仅按实现维数最小、按实验结果数最小和按原生门成本最小，是不同优化目标。


<div tabindex="0" role="region" aria-label="转换者注；可横向滚动" style="overflow-x:auto;max-width:100%">

> **转换者注。** “删去任何决定性关系”说明指定任务中的不可冗余性目标；本文所证明的维数、独立输入数和固定仿射读出结果数下界，并未逐一证明全文列出的每个关系集合都按删除包含关系最小。表中充分条件应连同各节全部前件使用。

</div>




### 无限递归的含义

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

一个有限闭合单门体已经可以产生无限前缀。
若整个观察者还不断吸收新的独立关系，则其参考体可按
$M_1\subseteq M_2\subseteq\cdots$ 增长，非零余核记录新增方向。
每次扩展须与旧核和旧操作一致；若声称极限仍为酉，还需正反接续在稠密生成部分均闭合。
单纯保范数的无限移位只给等距，不能跳过满射条件。

</div>

有限数据总可嵌入更大的内部空间而保持原读数。
主定理通过同门闭合把这种自由限制在不会影响该来源单门未来的部分；
要覆盖更多门，需要逐个补上它们的闭合关系。
这不是添加本体之外的环境，而是明确“全部”量词到底覆盖哪些内部关系。


<a id="section-10"></a>

## 10. 本轮结论：从直观图像到可核查的锁定机制

现在可以严谨地说：


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{
\text{参考关系}\ +\ \text{零余量闭合}\ +\ \text{共同接续相容}
\ \Longrightarrow\ \text{唯一最小酉递归实现}.
}
$$

</div>


三角形实例不是修辞，而有精确方程


<div tabindex="0" role="region" aria-label="公式；可横向滚动" style="overflow-x:auto;max-width:100%">

$$
\boxed{|b-a^2|=1-|a|^2.}
$$

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">


它把三个相干前缀态锁定成二能级循环结构，
并决定全部 $\psi_{n+2}=c_0\psi_n+c_1\psi_{n+1}$。

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

更上游的复结构与概率也不必永远作为互不相关的外加名称：
三轴乘法关系产生 $J$，中心确定性或完整乘积关系统一各局部 $J$；
效果关系一致性确定唯一响应矩阵，完整方向非负性确定正性，纯态迹配对给平方律。
这是一条明确的依赖链，每一步都有自己的可认证条件。

</div>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

“用全部关系锁定结构”的研究路线由此成立。
它还没有证明一般逻辑必然选择同一组锐性、复合及覆盖条件，也没有从未提供的观测数值恢复实际宇宙的完整 $K$。
下一项实质研究目标应是给这些上游条件更弱的操作表述，
或从项目原生接口证明它们在声明的完整上下文中成立。
共同坐标变换留下的自由则已被识别为表示规范，无须当作物理缺口继续追赶。

</div>



```tex
\clearpage
```

## 固定来源与参考文献


<a id="bib-v22"></a>

[1] 项目固定快照。
[V22：相对门历史与观察商](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)，§§6--8。

<a id="bib-v28"></a>

[2] 项目固定快照。
[V28：二元读出、完整框架相容与黄金门桥](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_BINARY_READOUT_FULL_FRAME_COMPATIBILITY_AND_E8_GOLDEN_GATE_BRIDGE_V28.md)，§6。

<a id="bib-omega"></a>

<div tabindex="0" role="region" style="overflow-x:auto;max-width:100%">

[3] 项目固定快照。
[$\Omega$ 静态相融纤维理论](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，§§5、7。

</div>

<a id="bib-v58"></a>

[4] 项目固定快照。
[V58：关系公理、共同复相位与条件量子重建](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md)，§3。

<a id="bib-v59"></a>

[5] 项目固定快照。
[V59：局部层析、相干读出轨道与量子正性起源](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md)，§§2--3。

<a id="bib-sic"></a>

[6] J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves.
*Symmetric Informationally Complete Quantum Measurements*.
[arXiv:quant-ph/0310075](https://arxiv.org/abs/quant-ph/0310075)。
本文仅用对称信息完备测量及二能级实例的背景；四面体各式另给完整纸面证明。

<a id="bib-barnum"></a>

[7] H. Barnum and A. Wilce.
*Local tomography and the Jordan structure of quantum theory*.
[arXiv:1202.4513](https://arxiv.org/abs/1202.4513)，v2，
引言的 Hanche-Olsen 条件及 §3 的复合、局部层析定义。
本文不把该路线的全部分类依赖声称为本轮重新证明。

```tex
\end{thebibliography}
\end{document}
```

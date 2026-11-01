<details data-production="preamble">
<summary>原始 XeLaTeX 制作设置、元数据与题页（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="原始制作设置">

```tex
% !TeX program = xelatex
% Compile twice with XeLaTeX; optional \def\AURICFontPath{/absolute/font/path/}
% Paper proofs only. Code is used for retrieval, files and PDF production.
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
\usepackage{booktabs,array,tabularx,enumitem,fancyhdr,xcolor,needspace}
\definecolor{auricblue}{RGB}{24,53,79}
\usepackage[unicode,colorlinks=true,linkcolor=auricblue,urlcolor=auricblue,citecolor=auricblue]{hyperref}
\hypersetup{pdftitle={AURIC v68：可见关系的秩、相容约束与量子公理},
pdfauthor={AURIC research continuation},
pdfsubject={Two-level projections, compatible constraints, internal records and conditional quantum reconstruction}}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\HH}{\mathcal H}
\newcommand{\BB}{\mathcal B}
\newcommand{\DD}{\mathcal D}
\newcommand{\Aalg}{\mathcal A}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\supp}{\operatorname{supp}}
\newcommand{\ran}{\operatorname{ran}}
\newcommand{\spanof}{\operatorname{span}}
\newcommand{\Var}{\operatorname{Var}}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/#1}{#2}}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{remark}[definition]{说明}
\renewcommand{\proofname}{证明}
\renewcommand{\abstractname}{摘要}
\renewcommand{\refname}{固定来源与文献}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{2pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC：可见关系、相容约束与量子公理}
\fancyhead[R]{\small v68 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
\begin{center}
{\LARGE\bfseries\color{auricblue} 可见关系的秩、相容约束与量子公理}\\[9pt]
{\large 两层投影、唯一状态与三条关系公理}\\[7pt]
AURIC 量子起源研究\quad 定义、定理与纸面证明\quad v68.0\\[4pt]
2026 年 11 月 1 日\quad Asia/Singapore
\end{center}
\begin{abstract}
本文将“退相干是关系降秩、两个线性关系锁定更明确的关系”的直觉分解为可证明的命题。
完全纯退相干是 Hilbert--Schmidt 算符空间到可见块代数的正交投影；
其线性像可以降维，而约化密度矩阵的秩不减。与此不同，正关系残差的共同零空间
限制条件态支持；共同核一维才锁定唯一纯态。
本文用同一个有限维交替投影定理统一两种机制，给出精确几何收敛率：
在振幅空间中，输入有非零共同支撑时，指定结果的条件序列收敛到共同允许子空间；
在算符空间中，非选择读出收敛到共同可见代数，其唯一归一状态可能是最大混态。
两投影的一维／二维分块定理给 AURIC 二元三轴模块一个严格入口，也揭示两条二值关系
尚不足以强制复相位结构。最后以复正历史核、完整关系守恒及正交细化权重三组前提，
重构 Hilbert 表示、酉续接、仪器、平方权重与记录条件化。
三组前提是可审查的结构压缩，不宣称逻辑最小或从唯一本体单独推尽全部量子公理。
全部数学采用纸面证明；没有运行数学程序、数值模拟、枚举或数学测试。
\end{abstract}
```

</div>
</details>

> **编者限定（原稿归属与转换范围）。** 以下正文、前导、制作设置、来源报告、参考文献与结尾均逐字来自用户提供的 V68 原稿；本转换只把 TeX 载体变为可读 Markdown，未把原稿历史报告当作本次执行证明。本文的范围是纸面数学、固定来源与本地阅读呈现，不构成形式核验、原生控制取得、物理或经验认证、全上游认证、无条件起源、最小性或优先权证明。

# 可见关系的秩、相容约束与量子公理

两层投影、唯一状态与三条关系公理

AURIC 量子起源研究　定义、定理与纸面证明　v68.0

2026 年 11 月 1 日　Asia/Singapore

## 摘要

本文将“退相干是关系降秩、两个线性关系锁定更明确的关系”的直觉分解为可证明的命题。
完全纯退相干是 Hilbert--Schmidt 算符空间到可见块代数的正交投影；
其线性像可以降维，而约化密度矩阵的秩不减。与此不同，正关系残差的共同零空间
限制条件态支持；共同核一维才锁定唯一纯态。
本文用同一个有限维交替投影定理统一两种机制，给出精确几何收敛率：
在振幅空间中，输入有非零共同支撑时，指定结果的条件序列收敛到共同允许子空间；
在算符空间中，非选择读出收敛到共同可见代数，其唯一归一状态可能是最大混态。
两投影的一维／二维分块定理给 AURIC 二元三轴模块一个严格入口，也揭示两条二值关系
尚不足以强制复相位结构。最后以复正历史核、完整关系守恒及正交细化权重三组前提，
重构 Hilbert 表示、酉续接、仪器、平方权重与记录条件化。
三组前提是可审查的结构压缩，不宣称逻辑最小或从唯一本体单独推尽全部量子公理。
全部数学采用纸面证明；没有运行数学程序、数值模拟、枚举或数学测试。

## 目录

1. [本轮结论与项目承接](#section-1)
2. [唯一本体、内部记录与三个测量描述](#section-2)
3. [退相干究竟降低哪一种秩？](#section-3)
4. [“两个关系锁定纯态”的正确条件](#section-4)
5. [统一主定理：两个关系保留共同结构](#section-5)
6. [为什么两个二值关系天然进入二元三轴模块？](#section-6)
7. [一个更紧凑、但不隐藏前提的公理候选](#section-7)
8. [经典记录的来源与仍然开放的量子起源问题](#section-8)

<div data-layout="paper-viewport" style="overflow-x:hidden;max-width:100%;width:100%;box-sizing:border-box">

<a id="section-1"></a>

## 1. 本轮结论与项目承接

**可以提出更简洁的统一原则：完整过程保持全部相干关系；
限制读口保留一个可见关系空间；读得记录后，状态受该记录所给的支持约束。
“两个关系锁定什么”由作用空间、相容性及记录处理方式决定。**

在这里至少有三个不同对象：

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\text{完整振幅向量}\quad\longrightarrow\quad
\text{约化密度矩阵}\quad\longrightarrow\quad
\text{指定读口的可见算符代数}.
$$

</div>

不能仅用一个不带对象的“秩”代替这三层。特别地，
唯一概率描述、唯一纯态、某一问题的确定答案，也不是同一个命题。

<a id="section-1-1"></a>

### 1.1. 固定来源与本轮查读范围

本轮唯一一次活动 HEAD 请求于新加坡时间 2026-11-01 17:07:01 发生本地 socket 权限拒绝，
未收到 HTTP 响应；没有重试，也没有取得更新提交。以下项目论证固定于

`5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b`。

本轮重新核对八份保留原文的 Git blob 身份，匹配保留的固定理论树。
重点查读 V38 §§3、7 的过程与记录段落；V52 定理 4.1–4.2 与命题 8.5；
V55 §§2、7.1、10.1；V56 §6.1；
V18 定义 4.1、定理 8.1、命题 8.2–8.3 及定理 9.1；
V58 公理组、局部 Clifford 结构与总定理；
V59 的 RC 定义、定理 3.2–3.3、推论 3.4 及总定理；
V22 定义 6.1、定理 6.2–6.4。另复用并重读已核对 V37 的 §§3–4。
V58、V59 总定理的全部历史依赖未在本轮逐一重审。
因此本文不能声称核验了该提交以后的最新进展。

| 已有项目结构 | 本轮如何承接 |
| --- | --- |
| V18、V38 | 区分内部记录、非选择通道、已读记录条件态，以及线性秩与 Choi 秩。 |
| V52、V56 | 完整等距保持态秩；同一纯整体的内部约化态仍可混合。 |
| V55 | 固定二元线性关系的零残差锁定纯态；关系图共同核与谱隙控制稳定性。 |
| V37 | 固定五模式等距编码把二元正关系的 Bloch 球放入原三轴。 |
| V22 | 完整复正核重构 Hilbert 空间；全交叉项守恒使分支递归成为等距仪器。 |
| V58、V59 | 已有条件重构公理；共同复结构、正性及充分读口供应仍有独立职责。 |

本文给出这些结构的自足组合证明，不主张标准投影、核表示或量子通道定理的原创优先权。
实质推进是把两种“关系锁定”放在同一投影定理下，并说明它们何时产生不同结果。

<a id="section-2"></a>

## 2. 唯一本体、内部记录与三个测量描述

<a id="statement-2-1"></a>

#### 定义 2.1（唯一实际来源与内部接口）

固定一个单位向量 $\Omega$ 及一条实际增长的历史前缀链

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
h_0\prec h_1\prec\cdots,\qquad
\Psi_k=G_k\Omega,\qquad G_k=U_k\cdots U_1.
$$

</div>

程序、观察者、记录、参考和所谓环境均属于此完整载体内部。
有限维接口 $\mathcal{H}$ 及记录角色 $R$ 是其中已声明的子空间或张量端口。
对接口输入的全称量词描述同一操作的作用规律，不引入多个实际本体。

> **Markdown 编者注。** 第 2 节的记录公式采用有限结果菜单、正交单位记录及同一有限内部联合空间。$M_r$ 是已声明输入到输出接口的线性算子；要把同一局部通道用于全部输入及保留参考，ready 记录须独立纯准备，参考上作用须为恒等。这些统一接口条件不是从单个实际 $\Omega$ 自动得到；命题的条件向量只在 $p_r>0$ 时有定义。这里不以有限维补基论证无条件的无限维酉扩张。

<a id="statement-2-2"></a>

#### 定义 2.2（记录、非选择读出与条件读出）

给 $\sum_rM_r^\dagger M_r=I$。在内部就绪记录子空间上定义

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
V\psi=\sum_rM_r\psi\otimes|r\rangle_R .
$$

</div>

则完整记录态、忽略记录的系统态、已读得 $r$ 后的系统态分别是

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
V\rho V^\dagger,\qquad
\Phi(\rho)=\sum_rM_r\rho M_r^\dagger,\qquad
\rho_r=\frac{M_r\rho M_r^\dagger}{p_r},\quad
p_r=\operatorname{Tr}(M_r\rho M_r^\dagger)>0 .
$$

</div>

若一个记录标签仍包含未读的细指标 $\mu$，其仪器为
$\mathcal I_r(\rho)=\sum_\mu M_{r\mu}\rho M_{r\mu}^\dagger$；
此时不能把它当作单 Kraus 的细分支。

<a id="statement-2-3"></a>

#### 命题 2.3（完整测量可内生酉实现）

$V^\dagger V=I$。有足够的内部就绪容量时，$V$ 可扩充为联合空间上的酉 $U_m$。
若实际准备满足 $G\Omega=\psi\otimes|0\rangle_R$，令
$Q_r=I\otimes|r\rangle\langle r|$，则

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\Psi_{\rm after}=U_mG\Omega,\qquad
p_r=\|Q_rU_mG\Omega\|^2,\qquad
\Psi_{|r}=\frac{Q_rU_mG\Omega}{\sqrt{p_r}}.
$$

</div>

**证明。**

正交记录使 $V^\dagger V=\sum_rM_r^\dagger M_r=I$。
把就绪输入子空间的正交基及其等距像分别补齐为同一联合空间的基，即得酉扩张。
投影记录后只剩 $M_r\psi\otimes|r\rangle$，给出三式。

∎

完整酉态没有被条件表达替换；条件态是以已读记录为条件的预测对象。
这与项目 V18 的测量定义及 V38 的完整记录／经典记录区分一致。[[1](#ref-v18), [4](#ref-v38)]
上述公式表明“塌缩”如何用同一 $\Omega$ 和门历史表达，但公式本身不证明
为什么一个特定记录必须成为实际经验；后文会把实际记录条件化明确列为解释输入。

<a id="section-3"></a>

## 3. 退相干究竟降低哪一种秩？

<a id="section-3-1"></a>

### 3.1. 完全纯退相干是可见算符空间的投影

<a id="statement-3-1"></a>

#### 定义 3.1（块读口与可见代数）

设 $\mathbf P=\{P_r\}$ 为有限投影分解：
$P_rP_s=\delta_{rs}P_r$、$\sum_rP_r=I$，令 $d_r=\operatorname{rank} P_r$。
定义

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\mathcal{D}_{\mathbf P}(X)=\sum_rP_rXP_r,\qquad
\mathcal{A}_{\mathbf P}=\bigoplus_r\mathcal{B}(P_r\mathcal{H})=\{P_r:r\}' .
$$

</div>

算符空间 $\mathcal{B}(\mathcal{H})$ 使用 Hilbert–Schmidt 内积
$\langle X,Y\rangle_2=\operatorname{Tr}(X^\dagger Y)$。
$\mathcal{A}_{\mathbf P}$ 中的效果恰是不访问跨块相干的效果。

> **Markdown 编者注。** 第 3–6 节的矩阵、线性维数、归一 Choi 矩阵及归一态均取 $1\le d<\infty$；PVM 的结果菜单有限，可保留零投影。效果指 $0\le E\le I$。支持在包含关系中指支持子空间，在取迹或算子不等式中指其正交投影；一般保秩结论的输入、输出是同一个矩阵空间。记录 Gram 的指标是系统的有限正交基，$D_\alpha$ 只在非零振幅支撑上可逆。qubit 行列式及表格使用归一、两个振幅均非零的纯输入；“完整纯态”指连同纯记录准备的完整等距输出，混合记录若有参考须一并保留。

<a id="thm-pinching"></a>

#### 定理 3.2（可见投影、线性秩与纯度）

设 $d=\dim\mathcal{H}$。则

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\mathcal{D}_{\mathbf P}^2=\mathcal{D}_{\mathbf P},\qquad
\mathcal{D}_{\mathbf P}^*=\mathcal{D}_{\mathbf P},\qquad
\operatorname{im}\mathcal{D}_{\mathbf P}=\mathcal{A}_{\mathbf P},
$$

</div>

并有

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\boxed{\operatorname{rank}_{\rm lin}\mathcal{D}_{\mathbf P}=\sum_rd_r^2.}
$$

</div>

其 Hermitian 迹一像的实仿射维数为 $\sum_rd_r^2-1$。
对任意密度矩阵，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\boxed{\operatorname{Tr}\rho^2-\operatorname{Tr}\mathcal{D}_{\mathbf P}(\rho)^2
=\|\rho-\mathcal{D}_{\mathbf P}(\rho)\|_2^2\ge0.}
$$

</div>

**证明。**

由投影正交性，
$\mathcal{D}^2(X)=\sum_{r,s}P_rP_sXP_sP_r=\sum_rP_rXP_r$。
迹循环给
$\langle Y,\mathcal{D} X\rangle_2=\sum_r\operatorname{Tr}(P_rY^\dagger P_rX) =\langle\mathcal{D} Y,X\rangle_2$。
像恰为块对角矩阵；第 $r$ 块有 $d_r^2$ 个复矩阵单位，
Hermitian 块也有 $d_r^2$ 个实自由度，迹一去掉一维。
最后 $\mathcal{D}\rho$ 与 $\rho-\mathcal{D}\rho$ 正交，Pythagoras 恒等式给纯度公式。

∎

所以完全纯退相干可以叫作“可见关系映射降秩”。
若块大小 $d_r>1$，块内仍有非交换量子信息；仅当所有 $d_r=1$ 时，
整个像代数才是经典的交换代数。该映射是通常所称的 pinching 通道。[[10](#ref-watrous)]

> **编者资格说明（PVM 零结果；保留原断言）。** 原稿的有限 PVM 菜单允许零投影，因此“仅当所有 $d_r=1$”应按非零块理解；若保留零结果标签，等价表述是所有块满足 $\operatorname{rank}P_r\le1$。供核对的边界例为 $\mathcal H=\mathbb C$、$P_1=I$、$P_2=0$：像代数仍交换而 $d_2=0$。本节的迹一 Hermitian 仿射维数和归一密度矩阵秩讨论以非零有限维载体为范围。此说明只资格化适用范围，不改写原文断言。

<a id="thm-state-rank"></a>

#### 定理 3.3（纯退相干不降低密度矩阵秩）

对任意 $\rho\ge0$，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\ker\mathcal{D}_{\mathbf P}(\rho)\subseteq\ker\rho,\qquad
\boxed{\operatorname{rank}\mathcal{D}_{\mathbf P}(\rho)\ge\operatorname{rank}\rho.}
$$

</div>

更一般地，在同一有限维矩阵空间上，任意正、保迹、保单位的线性映射
$\Phi$ 均满足 $\operatorname{rank}\Phi(\rho)\ge\operatorname{rank}\rho$。

**证明。**

若 $x\in\ker\mathcal{D}(\rho)$，则

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
0=\langle x,\mathcal{D}(\rho)x\rangle
=\sum_r\|\sqrt\rho\,P_rx\|^2.
$$

</div>

各项非负，故 $\sqrt\rho P_rx=0$；求和给 $\sqrt\rho x=0$，得到核包含。

对一般情形，取 $P=\operatorname{supp}\rho$、$Q=\operatorname{supp}\Phi(\rho)$。
存在 $\epsilon>0$ 使 $\rho\ge\epsilon P$，因而
$\operatorname{supp}\Phi(P)\subseteq Q$。正性与保单位给 $0\le\Phi(P)\le I$，
所以

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\operatorname{rank} P=\operatorname{Tr}\Phi(P)\le\operatorname{Tr} Q=\operatorname{rank} Q .
$$

</div>

零输入情形平凡。

∎

此结论针对保单位的退相干；非保单位的冷却或重置不能据此处理。
最小例子已经显示三种方向：

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
|+\rangle\langle+|
=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}
\ \xrightarrow{\ \mathcal{D}_z\ }\ \frac I2.
$$

</div>

约化态秩 $1\to2$；通道线性秩由恒等通道的 $4$ 变成 $2$；
完整内部实现 $|+\rangle|0\rangle\mapsto(|00\rangle+|11\rangle)/\sqrt2$
仍是秩一纯态。V52 命题 8.5 的完整等距保秩与此完全一致。[[5](#ref-v52)]

<a id="section-3-2"></a>

### 3.2. 内部记录 Gram：另一种秩反而上升

<a id="thm-schur"></a>

#### 定理 3.4（记录重叠控制三种秩）

设内部记录等距 $V|i\rangle=|i\rangle|e_i\rangle$，$\|e_i\|=1$。
置 $\Gamma_{ij}=\langle e_j|e_i\rangle$，则 $\Gamma\ge0$、$\Gamma_{ii}=1$，且

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\Phi_\Gamma(\rho)=\Gamma\circ\rho .
$$

</div>

这里 $\circ$ 是逐元素乘法。其线性秩、归一 Choi 矩阵的秩为

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\operatorname{rank}_{\rm lin}\Phi_\Gamma
=\#\{(i,j):\Gamma_{ij}\ne0\},\qquad
\operatorname{rank} C_{\Phi_\Gamma}=\operatorname{rank}\Gamma .
$$

</div>

若纯输入 $\psi=\sum_i\alpha_i|i\rangle$ 的非零支撑为 $S$，则

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\operatorname{rank}\Phi_\Gamma(|\psi\rangle\langle\psi|)
=\operatorname{rank}\Gamma_S
=\dim\operatorname{span}\{e_i:i\in S\}.
$$

</div>

**证明。**

对记录端口取迹，交叉项乘以 $\langle e_j|e_i\rangle$。
$\Gamma$ 是通常 Gram 矩阵的转置，仍正半定。
每个矩阵单位 $E_{ij}$ 被乘以 $\Gamma_{ij}$，故线性像维数由非零系数计数。
归一 Choi 矩阵为

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
C_{\Phi_\Gamma}
=\frac1d\sum_{i,j}\Gamma_{ij}|ii\rangle\langle jj|,
$$

</div>

即 $\Gamma/d$ 经 $|i\rangle\mapsto|ii\rangle$ 等距后的像。
纯输入的输出在 $S$ 上为
$D_\alpha\Gamma_SD_\alpha^\dagger$，$D_\alpha$ 可逆，故秩等于记录 Gram 秩。

∎

对于 $\psi=\alpha|0\rangle+\beta|1\rangle$，
V56 的内部二分公式在这里化为

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
1-\|r\|^2
=4|\alpha|^2|\beta|^2(1-|\langle e_1|e_0\rangle|^2).
$$

</div>

记录越可区分，局部纯度越低；相关关系仍在同一个完整态中。[[7](#ref-v56)]

<a id="section-3-3"></a>

### 3.3. 有限误差通常是小奇异值，不是精确降秩

定义 $|\gamma|\le1$ 的 qubit 通道

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\Phi_\gamma
\begin{pmatrix}a&b\\c&d\end{pmatrix}
=\begin{pmatrix}a&\gamma b\\\bar\gamma c&d\end{pmatrix}.
$$

</div>

对两个振幅均非零的纯输入，令 $p=|\alpha|^2\in(0,1)$，则

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\det\Phi_\gamma(|\psi\rangle\langle\psi|)
=p(1-p)(1-|\gamma|^2).
$$

</div>

| 对象 | $\vert\gamma\vert=1$ | $0<\vert\gamma\vert<1$ | $\gamma=0$ |
| --- | --- | --- | --- |
| 完整纯态的秩 | 1 | 1 | 1 |
| 约化密度矩阵的秩 | 1 | 2 | 2 |
| 记录 Gram／通道 Choi 秩 | 1 | 2 | 2 |
| 通道的线性秩 | 4 | 4 | 2 |
| Bloch 线性部分的秩 | 3 | 3 | 1 |

<a id="prop-partial"></a>

#### 命题 3.5（有效低秩与误差界）

假定每一步确实实施同一个 $\Phi_\gamma$，例如使用新的内部就绪记录且不再访问旧记录；
取整数 $n\ge1$。
则

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\Phi_\gamma^n=\Phi_{\gamma^n},\qquad
\|\Phi_\gamma^n-\mathcal{D}_z\|_{2\to2}=|\gamma|^n.
$$

</div>

以 $D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$ 表示迹距离，有

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
D(\Phi_\gamma^n(\rho),\mathcal{D}_z(\rho))
=|\gamma|^n|\rho_{01}|
\le\frac{|\gamma|^n}{2}.
$$

</div>

若 $0<|\gamma|<1$，每个有限 $n$ 的线性秩仍为 $4$。

**证明。**

复合逐次相乘两个非对角系数。
在 Hilbert–Schmidt 正交矩阵单位基中，差映射只保留两个交叉方向，
模长均为 $|\gamma|^n$，故诱导范数等于此值。
态差为 $\bigl(\begin{smallmatrix}0&z\\\bar z&0\end{smallmatrix}\bigr)$，
特征值为 $\pm|z|$，其中 $|z|=|\gamma|^n|\rho_{01}|$。
正性给 $|\rho_{01}|\le\sqrt{\rho_{00}\rho_{11}}\le1/2$。
非零 $\gamma^n$ 不消去任何矩阵单位，故仍满线性秩。

∎

通道的四个 Hilbert–Schmidt 奇异值是 $1,1,|\gamma|^n,|\gamma|^n$。
因此分辨阈值 $\epsilon$ 下可以说后两方向不可见，
而精确降秩只在 $\gamma=0$ 或收敛极限发生。
一个线性满秩通道也未必有物理逆：
$\Phi_\gamma^{-1}$ 将 $|+\rangle\langle+|$ 送到非对角元为 $1/(2\gamma)$ 的矩阵，
其行列式在 $0<|\gamma|<1$ 时为负。

若重新耦合旧记录，后续约化演化可能依赖旧记忆，不能直接写成 $\Phi_\gamma^n$。
同一受控记录操作的逆可以恢复相干；项目 V18 已明确要求独立新记录或完整记忆接口。[[1](#ref-v18)]

<a id="section-4"></a>

## 4. “两个关系锁定纯态”的正确条件

<a id="section-4-1"></a>

### 4.1. 正残差与共同零空间

<a id="statement-4-1"></a>

#### 定义 4.1（关系残差）

在有限维 $\mathcal{H}$ 上，给线性映射
$L_j:\mathcal{H}\to\mathcal K_j$，定义

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
Q=\sum_jL_j^\dagger L_j,\qquad
\mathcal K=\bigcap_j\ker L_j,\qquad
L\psi=(L_1\psi,\ldots,L_m\psi).
$$

</div>

$L_j\psi=0$ 是振幅约束；$Q$ 是非负关系残差。

<a id="thm-constraint"></a>

#### 定理 4.2（关系锁定与唯一性）

对密度矩阵 $\rho$，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\boxed{\operatorname{Tr}(Q\rho)=0
\iff\operatorname{supp}\rho\subseteq\mathcal K
\iff L\sqrt\rho=0.}
$$

</div>

因此有归一解当且仅当 $\dim\mathcal K\ge1$；
归一解唯一当且仅当 $\dim\mathcal K=1$，此时它是纯态投影。
若 $\dim\mathcal{H}=d$，唯一性等价于 $\operatorname{rank} L=d-1$。

**证明。**

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\operatorname{Tr}(Q\rho)=\sum_j\operatorname{Tr}(L_j\rho L_j^\dagger)
=\sum_j\|L_j\sqrt\rho\|_2^2.
$$

</div>

非负和为零当且仅当各项为零，等价于 $\sqrt\rho$ 的像落入共同核。
共同核零维时没有非零态，一维时迹一正矩阵只能是该射线的投影。
核维数至少二时，两条正交单位向量已经给两个不同归一解。
最后由秩零度定理得结论。

∎

在 qubit 上，固定一条复线性关系

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\ell_z=(-z,1),\qquad \ell_z\binom{\alpha}{\beta}=0
$$

</div>

已经给 $\beta=z\alpha$，因而

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\rho_z=\frac1{1+|z|^2}
\begin{pmatrix}1&\bar z\\z&|z|^2\end{pmatrix}.
$$

</div>

这是项目 V55 定理 2.2 的已有正向结果。[[6](#ref-v55)]
固定 $z$ 锁定一个纯态；允许 $z$ 变化仍遍历一族纯态，另加 $z=\infty$ 才覆盖完整球面。
在 $\mathbb{C}^2$ 中再增加一条独立复标量零约束，通常使共同核变成零。
所以应数的是*独立约束的秩与共同核维数*，不是机械地数“两个”。
增加独立约束时，$\operatorname{rank} L$ 上升，候选支持维数下降。

<a id="cor-gap"></a>

#### 推论 4.3（近似关系的稳定性）

设 $R$ 为共同核投影，且
$Q\ge\Delta(I-R)$，$\Delta>0$。若 $\operatorname{Tr}(Q\rho)\le\epsilon$，则

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\operatorname{Tr}((I-R)\rho)\le\frac{\epsilon}{\Delta}.
$$

</div>

若 $R=|\phi\rangle\langle\phi|$，则

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
D(\rho,R)\le\sqrt{\frac{\epsilon}{\Delta}}.
$$

</div>

**证明。**

第一式直接取迹。记 $f=\langle\phi|\rho|\phi\rangle$。
取 $\rho$ 的任意纯化 $|\Psi\rangle$；
当 $f>0$ 时，向量
$|\eta\rangle=(\langle\phi|\otimes I)|\Psi\rangle/\sqrt f$ 为单位向量，
且 $|\langle\phi,\eta|\Psi\rangle|^2=f$。
两个纯态的迹距离是 $\sqrt{1-f}$；对辅助端口取迹不增加迹距离，
故 $D(\rho,R)\le\sqrt{1-f}$。$f=0$ 时用 $D\le1$。
纯态距离式可由两向量张成的二维矩阵直接求得；
取迹收缩则由 Hermitian 迹范数的效果上确界及效果回拉立即得到。

> **Markdown 编者注。** 这里比较的两态之差为无迹 Hermitian 算子，迹距离等于效果 $0\le E\le I$ 上期望差绝对值的上确界；一般 Hermitian 算子的迹范数则用 $-I\le A\le I$ 的对偶上确界。$\phi$ 是单位向量，$\epsilon\ge0$；共同核可以为零，此时第一界仍成立，第二界只适用于一维共同核。

∎

这把“结果稳定”具体化为关系残差与谱隙的比值。
V55 的关系图共同核与条件滤波已经有这一机制。[[6](#ref-v55)]
条件滤波 $K_\tau=e^{-\tau Q}$ 的残差下降
$\dot q_\tau=-2\operatorname{Var}_{\rho_\tau}(Q)$ 必须同时保留成功质量；
不能把选定成功分支的结论改称无条件退相干。

> **Markdown 编者注。** 此处沿用 V55 定理 10.1 的定义：$\tau\ge0$，$Z_\tau=\operatorname{Tr}(K_\tau\rho K_\tau)>0$，$\rho_\tau=K_\tau\rho K_\tau/Z_\tau$，$q_\tau=\operatorname{Tr}(Q\rho_\tau)$；有限参数下 $K_\tau$ 可逆。$\dot Z_\tau=-2q_\tau Z_\tau$ 与残差导数同时成立，不能丢掉成功质量。

<a id="section-4-2"></a>

### 4.2. 相容结果、顺序结果与平均值是三种数据

<a id="statement-4-4"></a>

#### 命题 4.4（两次确定记录何时共同锁定）

设 $P,Q$ 为两个所读结果的投影，按理想 Lüders 细分支 $M=P$、$N=Q$ 实施。
同时要求 $P\psi=\psi$、$Q\psi=\psi$，允许空间为
$\mathcal K=\operatorname{ran} P\cap\operatorname{ran} Q$。
若 $[P,Q]=0$，则其投影 $R=PQ$；实际读得这两个结果后的状态为

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\rho_{PQ}=\frac{R\rho R}{\operatorname{Tr}(R\rho)},\qquad \operatorname{Tr}(R\rho)>0 .
$$

</div>

该记录组合锁定一个与输入无关的纯态，当且仅当 $\operatorname{rank} R=1$。

> **Markdown 编者注。** 此处“锁定”要求至少存在一个正概率输入，并对所有正概率输入得到同一纯态；$R=0$ 时记录组合不可能发生，不以空量词算作锁定。以下例子中的 $U$ 取酉（更一般可取输出等距），$a,b$ 是各 $Z$ 本征向量的标签；若使用计算位 $0,1$，对应本征值为 $(-1)^a,(-1)^b$。

**证明。**

对易使 $(PQ)^\dagger=PQ$、$(PQ)^2=PQ$，像恰为交集。
顺序细分支的 Kraus 算子 $QP=PQ=R$，得到条件态公式。
唯一性由定理 [4.2](#thm-constraint)，或取 $R$ 内不同纯输入直接判断。

∎

同一个投影效果可以有不同测后仪器，例如 Kraus 算子 $UP$ 仍有
$(UP)^\dagger(UP)=P$；若不声明 Lüders 实现，就不能直接用 $QP$ 计算末态。

例如两个内部 qubit 上的 $Z_A=a$、$Z_B=b$ 相容；
共同投影是 $|ab\rangle\langle ab|$，因此联合记录锁定一条射线。
重复同一个投影只有 $P^2=P$，不会自动增加独立约束。

若要求第二次选择 $Q$ 对所有 $P$ 支持的输入都不破坏第一个确定结果，
精确条件是

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
(I-P)QP=0\iff[P,Q]=0.
$$

</div>

正向由 $QP=PQP$ 及取伴随得到 $PQ=PQP$；反向显然。
但某个特定输入可以在非对易情形下恰好满足额外特殊条件。

非相容的顺序读出不同。取

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
P=|0\rangle\langle0|,\qquad Q=|+\rangle\langle+|.
$$

</div>

共同像为零，然而
$QP|0\rangle=|+\rangle/\sqrt2\ne0$。
先读 $Z=+$ 再读 $X=+$ 是合法的记录序列，末态为 $|+\rangle$；
再读 $Z$ 仍有两个可能结果。过去两次记录确实发生，不表示末态同时是两个本征态。

若数据仅是两个均值
$n_1\cdot r=s_1$、$n_2\cdot r=s_2$，而 $n_1,n_2$ 独立，
则 $r=r_0+\lambda t$，其中 $r_0\perp t$、$|t|=1$。
Bloch 正性给 $\lambda^2\le1-|r_0|^2$；
通常留下线段，另知纯态才通常剩下两个端点。
这延续 v67 的仿射约束分类，不与振幅零残差混用。

> **Markdown 编者注。** $r_0$ 是该仿射直线上与单位方向 $t$ 正交的唯一点。$|r_0|<1$ 时可行集为非退化闭线段，另加纯性给两个端点；$|r_0|=1$ 时只有一个切点，$|r_0|>1$ 时没有密度态解。“通常”不包括这两种边界。

<a id="statement-4-5"></a>

#### 命题 4.5（细分支的秩）

对单 Kraus 非零条件分支，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\operatorname{rank}\rho_M
\le\min(\operatorname{rank}\rho,\operatorname{rank} M).
$$

</div>

若 $M$ 可逆，则秩保持；纯输入的每个非零细分支始终是秩一。

**证明。**

$M\rho M^\dagger=(M\sqrt\rho)(M\sqrt\rho)^\dagger$，
其秩等于 $\operatorname{rank}(M\sqrt\rho)$；非零标量归一化不改秩。

∎

因此条件预测越来越集中，也不要求每一有限步都精确降秩。

<a id="section-5"></a>

## 5. 统一主定理：两个关系保留共同结构

<a id="section-5-1"></a>

### 5.1. 一个有限维投影定理

<a id="thm-alternating"></a>

#### 定理 5.1（交替投影的精确收敛率）

在有限维 Hilbert 空间 $\mathcal V$ 上，设 $E,F$ 是正交投影，
$R$ 投影到 $\operatorname{ran} E\cap\operatorname{ran} F$。令

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
T=FE-R,\qquad c=\|T\|.
$$

</div>

则 $0\le c<1$，并对每个 $n\ge1$ 有

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\boxed{\|(FE)^n-R\|=c^{\,2n-1}.}
$$

</div>

**证明。**

因 $ER=RE=FR=RF=R$，
$E'=E-R$、$F'=F-R$ 仍为正交投影，且没有非零共同像。
有 $T=F'E'$，并令
$A=E'F'E'=T^\dagger T$。直接归纳得

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
(FE)^n-R=(F'E')^n=T A^{n-1},\qquad \|A\|=c^2.
$$

</div>

若 $c=1$，有限维紧致性给单位向量 $x$ 满足
$\|F'E'x\|=\|x\|$。投影的范数收缩链均取等，迫使
$x=E'x=F'x$，与共同像为零矛盾，故 $c<1$。
上式给上界 $c^{2n-1}$。
若 $c>0$，取 $A$ 的最大本征值 $c^2$ 对应单位向量 $u$，
则 $\|Tu\|=c$ 且
$\|TA^{n-1}u\|=c^{2n-1}$，达到上界。
$c=0$ 时两边均为零。

∎

这是经典交替投影结果的有限维自足证明；
精确范数率在标准文献中归属于 Aronszajn 的上界及 Kayalar–Weinert 的等式。[[11](#ref-alternating)]
本轮利用的是*同一定理在振幅空间与算符空间中的两个不同解释*。

<a id="section-5-2"></a>

### 5.2. 第一层：指定结果的条件过滤

<a id="thm-amplitude-lock"></a>

#### 定理 5.2（共同允许态的条件锁定）

取 $\mathcal V=\mathcal{H}$、$E=P$、$F=Q$。
每一步按对应的理想 Lüders 投影实施。
设单位输入 $\psi$ 在共同空间有质量
$s=\|R\psi\|^2>0$，定义

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\chi_n=(QP)^n\psi,\qquad p_n=\|\chi_n\|^2,\qquad
\phi=\frac{R\psi}{\sqrt s}.
$$

</div>

$p_n$ 是连续 $2n$ 次均取得所指定结果的联合概率。并有

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
s\le p_n\le s+c^{4n-2}(1-s),
$$

</div>

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\boxed{
D\left(\frac{|\chi_n\rangle\langle\chi_n|}{p_n},
|\phi\rangle\langle\phi|\right)
\le c^{2n-1}\sqrt{\frac{1-s}{s}}.}
$$

</div>

若 $\operatorname{rank} R=1$，所有 $s>0$ 的输入趋于同一纯态射线。

**证明。**

由定理 [5.1](#thm-alternating)，
$\chi_n=R\psi+b_n$，其中 $b_n\perp\operatorname{ran} R$，
$\|b_n\|\le c^{2n-1}\sqrt{1-s}$。
因此 $p_n=s+\|b_n\|^2$，得成功概率界。
归一向量与 $\phi$ 的内积模平方为 $s/(s+\|b_n\|^2)$；
纯态迹距离为
$\|b_n\|/\sqrt{s+\|b_n\|^2}$，再用分母不小于 $\sqrt s$。
联合概率公式由各次条件概率的分母逐次抵消得到。

∎

当 $s=0$，不会凭此序列创造原来没有的共同核分量；
$p_n\to0$，不能宣称无条件地准备了目标。
失败分支也仍属于完整 $\Omega$ 的内部记录历史。
这是“关系越来越明确”对应纯态时需要保留的成功质量。

> **Markdown 编者注。** 定理 5.2 的目标向量及显示误差界针对单位纯输入。对混合输入，若 $s=\operatorname{Tr}(R\rho)>0$，相同未归一算子极限给条件态趋于 $R\rho R/s$；其一般不纯，只有共同空间一维才统一成为该射线。$s=0$ 时成功质量趋零，零质量步骤的条件态不定义。

<a id="section-5-3"></a>

### 5.3. 第二层：不选结果的可见代数收缩

<a id="thm-operator-lock"></a>

#### 定理 5.3（共同可见代数的非选择锁定）

给两组 PVM $\mathbf P,\mathbf Q$，令

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\mathcal M=\mathcal{A}_{\mathbf P}\cap\mathcal{A}_{\mathbf Q}
=\{P_r,Q_s:r,s\}' .
$$

</div>

用 $\mathcal E_{\mathcal M}$ 表示到 $\mathcal M$ 的 Hilbert–Schmidt 正交投影，
令 $c_{\rm rel}=\|\mathcal{D}_{\mathbf Q}\mathcal{D}_{\mathbf P}-\mathcal E_{\mathcal M}\|_{2\to2}$。
则

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\boxed{
(\mathcal{D}_{\mathbf Q}\mathcal{D}_{\mathbf P})^n\longrightarrow
\mathcal E_{\mathcal M},\qquad
\|(\mathcal{D}_{\mathbf Q}\mathcal{D}_{\mathbf P})^n-\mathcal E_{\mathcal M}\|_{2\to2}
=c_{\rm rel}^{\,2n-1},}
$$

</div>

其中 $0\le c_{\rm rel}<1$。
极限是保迹、保单位、完全正的条件期望。并且

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
D\bigl((\mathcal{D}_{\mathbf Q}\mathcal{D}_{\mathbf P})^n(\rho),
\mathcal E_{\mathcal M}(\rho)\bigr)
\le\frac{\sqrt d}{2}\,
c_{\rm rel}^{2n-1}\|\rho-\mathcal E_{\mathcal M}(\rho)\|_2 .
$$

</div>

**证明。**

由定理 [3.2](#thm-pinching)，两个 $\mathcal{D}$ 是 $\mathcal{B}(\mathcal{H})$ 上的正交投影。
应用定理 [5.1](#thm-alternating) 得极限与精确范数率。
每个有限乘积都是保迹、保单位、完全正映射；
有限维范数极限保留这些性质，完全正性也可由 Choi 正锥闭性得到。
对 $A,B\in\mathcal M$，每次 pinching 都满足
$\mathcal{D}(AXB)=A\mathcal{D}(X)B$；极限继承此双模性质且固定 $\mathcal M$，
所以是其保迹条件期望。
最后在正交余空间应用范数率，再用
$\|X\|_1\le\sqrt d\|X\|_2$。

∎

条件期望与 Hilbert–Schmidt 投影的对应是有限维算符代数的标准结构。[[12](#ref-conditional)]
这里同样要求重复读口的局部通道确实闭合；历史相关记忆必须纳入接口。

<a id="cor-maxmixed"></a>

#### 推论 5.4（唯一可见状态可以是最大混态）

共同固定密度矩阵唯一，当且仅当 $\mathcal M=\mathbb{C} I$。
在此情形，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\boxed{\mathcal E_{\mathcal M}(X)=\frac{\operatorname{Tr} X}{d}I,\qquad
\rho_n\longrightarrow\frac Id.}
$$

</div>

**证明。**

到 $\mathbb{C} I$ 的正交投影系数是
$\langle I,X\rangle_2/\langle I,I\rangle_2=\operatorname{Tr} X/d$。
反过来，若 $\mathcal M$ 不止标量，则有非零无迹 Hermitian 元 $H\in\mathcal M$。
充分小的 $\delta>0$ 使 $I/d\pm\delta H$ 都是不同固定密度态。

∎

对 qubit 单位轴 $a,b$，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\mathcal{D}_a:\ r\mapsto(a\cdot r)a,\qquad
(\mathcal{D}_b\mathcal{D}_a)^n:\ r\mapsto b(a\cdot r)(a\cdot b)^{2n-1}.
$$

</div>

若 $|a\cdot b|<1$，则 $r\to0$。尤其两轴正交时，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\boxed{\mathcal{D}_x\mathcal{D}_z(X)=\operatorname{Tr}(X)\frac I2.}
$$

</div>

累计通道 $\mathrm{id},\mathcal{D}_z,\mathcal{D}_x\mathcal{D}_z$ 的线性秩 $4\to2\to1$，归一输出只剩唯一值，
但该值是密度秩为 $2$ 的最大混态。
这里的 $\mathcal{D}_x,\mathcal{D}_z$ 作为超算符可以对易，
不意味着其底层尖锐投影 $P_x,P_z$ 对易。

| 作用空间 | 保留对象 | 唯一性的含义 |
| --- | --- | --- |
| 振幅空间 $\mathcal{H}$ | $\operatorname{ran} P\cap\operatorname{ran} Q$ | 交集一维且输入有非零支撑时，条件序列锁定纯态。 |
| 算符空间 $\mathcal{B}(\mathcal{H})$ | $\mathcal{A}_{\mathbf P}\cap\mathcal{A}_{\mathbf Q}$ | 交集只有标量时，非选择序列锁定最大混态。 |

<a id="section-6"></a>

## 6. 为什么两个二值关系天然进入二元三轴模块？

<a id="section-6-1"></a>

### 6.1. 两投影的分块定理

<a id="thm-jordan"></a>

#### 定理 6.1（两个二值问题的一维／二维分解）

有限维复 Hilbert 空间上的任意两个正交投影 $P,Q$，
都存在共同不变的正交直和分解，每块维数至多为 $2$。
每个非平凡二维块可选基使

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
Q=\begin{pmatrix}
\lambda&\sqrt{\lambda(1-\lambda)}\\
\sqrt{\lambda(1-\lambda)}&1-\lambda
\end{pmatrix},\quad 0<\lambda<1.
$$

</div>

**证明。**

在 $\operatorname{ran} P$ 上对 Hermitian 压缩 $PQP$ 取正交本征基。
若 $PQP u=\lambda u$、$\|u\|=1$，则
$0\le\lambda=\langle u,Qu\rangle\le1$。
$\lambda=0$ 时 $Qu=0$；$\lambda=1$ 时 $Qu=u$，均给一维块。
对 $0<\lambda<1$，置 $s=\sqrt{\lambda(1-\lambda)}$、

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
v=\frac{Qu-\lambda u}{s}.
$$

</div>

则 $Pv=0$，且
$\|Qu-\lambda u\|^2=\lambda-\lambda^2=s^2$，
所以 $v$ 是与 $u$ 正交的单位向量。
由 $Q^2=Q$ 得 $Qu=\lambda u+sv$、
$Qv=su+(1-\lambda)v$，即所示二维块。
不同正交本征向量对应的 $v$ 彼此正交，因为
$\langle Qu_i,Qu_j\rangle=\langle u_i,Q u_j\rangle =\lambda_j\delta_{ij}$。
这些块的正交补位于 $\ker P$，且因 $Q$ 自伴而对 $Q$ 不变；
在余空间再将 $Q$ 对角化，给出剩余一维块。

∎

这是通常所称的两投影 Jordan 引理；原始研究文献中有明确的二值测量用途和证明。[[13](#ref-jordan)]

> **编者来源角色说明（保留原引用）。** 实际查读的 Nagaj–Wocjan–Zhang，arXiv:0904.1549，第 4 页将两投影分解列为 §2.1 的事实；附录 A 第 13 页的 Lemma 2 明确给出一维／二维不变分解，并注明短证明见 Regev [20]。该文第 13–14 页随后用这个 lemma 证明反射乘积的谱／旋转定理。V68 在此处保留自己的完整构造与证明；该来源承担分解与历史归属说明，不被新增为本文证明的必要依赖。

在二维块中，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
P=\frac{I+\sigma_z}{2},\qquad
Q=\frac{I+n\cdot\sigma}{2},\qquad
n=(2\sqrt{\lambda(1-\lambda)},0,2\lambda-1),\quad |n|=1.
$$

</div>

所以“两个二值关系可分解为二元三轴模块”有精确数学含义。
但这是*一族带块标签的模块*；一般态还可能有跨块相干。
若保留的读口只有这两个投影生成的代数，跨块项可能不影响这些读口；
若允许以后使用连接不同块的门或效果，就必须保留它们。
一个全局 Bloch 三元组不能无损表示任意高维态。

<a id="section-6-2"></a>

### 6.2. 三轴、线性关系与 AURIC 原五模式

任一二维归一正关系写为

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\rho=\frac12(I+x\sigma_x+y\sigma_y+z\sigma_z)
=\frac12\begin{pmatrix}1+z&x-iy\\x+iy&1-z\end{pmatrix}.
$$

</div>

由 $(r\cdot\sigma)^2=|r|^2I$，特征值为 $(1\pm|r|)/2$，
故正性恰为 $x^2+y^2+z^2\le1$；纯态恰在球面。
对 $\psi=(\alpha,\beta)^T$，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
x=2\Re(\bar\alpha\beta),\qquad
y=2\Im(\bar\alpha\beta),\qquad
z=|\alpha|^2-|\beta|^2.
$$

</div>

固定 $\beta=\zeta\alpha$ 给

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
r_\zeta=
\frac{(2\Re\zeta,\ 2\Im\zeta,\ 1-|\zeta|^2)}
{1+|\zeta|^2}.
$$

</div>

这才是“固定线性关系加归一化锁定三轴纯态”的明确公式。
三轴平方约束来自二阶正矩阵的特征值与行列式；
复线性关系确定的向量，其二次读出自然落在球面。

项目 V37 已构造固定等距 $J:\mathbb{C}^2\to\mathbb{C}^5$，保留原五模式及原占据读口。
定义

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\nu=\frac1{1+2\sqrt3+\sqrt{11}},\qquad
a_\nu=\frac{\nu(\sqrt3+\sqrt{11})}{2},\qquad
u_0=(a_\nu,a_\nu,\nu).
$$

</div>

该编码的原三均值满足

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
u(\rho)=u_0+\nu r,\qquad
D(\rho,\widetilde\rho)=\frac{|u(\rho)-u(\widetilde\rho)|}{2\nu}.
$$

</div>

而任意块内酉 $U$ 有忠实五模式提升

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\widetilde U=JUJ^\dagger+(I-JJ^\dagger).
$$

</div>

因为它在编码像上作用为 $U$、在正交补上作用为恒等，所以酉且保持乘法。
这些是已有编码结论，不把整个五模式金字塔与 Bloch 球等同。[[3](#ref-v37)]
因此前节的每个二维块可以接到同一型 AURIC 编码；
块标签与跨块相干仍是完整高维信息的一部分。

<a id="section-6-3"></a>

### 6.3. 两条二值关系为什么还没有强制复数？

<a id="prop-real"></a>

#### 命题 6.2（两个实投影读口的共轭盲区）

在定理 [6.1](#thm-jordan) 的共同基中，$P,Q$ 及其补投影都是实矩阵。
若只允许由这些投影构成的 Lüders 顺序词 $K_w$，则对任意密度态 $\rho$，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\operatorname{Tr}(K_w\rho K_w^\dagger)
=\operatorname{Tr}(K_w\bar\rho K_w^\dagger).
$$

</div>

因此这组序列读出不能区分 $\rho$ 与该基下的 $\bar\rho$。

**证明。**

每个 $K_w$ 实，效果 $K_w^\dagger K_w=K_w^TK_w$ 实对称。
Hermitian $\rho$ 的实部实对称、虚部纯虚反对称；
实对称矩阵与反对称矩阵相乘的迹为零。
效果期望只依赖 $\Re\rho$，故对复共轭不变。

∎

事实上 $\rho_{\mathbb{R}}=(\rho+\bar\rho)/2$ 仍正且迹一，
可在同维实模型中重现这些有限记录的全部统计；它不必保留原态的纯性。
经典自适应与结果粗粒化仍只组合这些实效果。
这里限定的是实际 Lüders 词效果菜单；
复代数 $C^*(P,Q)$ 可以包含 $i[P,Q]$，非平凡二维块上甚至可为整个 $M_2(\mathbb{C})$，
不能因此把该完整复代数也说成只有实对称矩阵。

所以两条二值关系的分块几何尚不能单独解释为何必须采用完整复相位或选定相位定向。
若再加入具有相对相位的控制门、其他投影或复合相容性，它们就是额外的声明结构。
V58 以三轴 Clifford 关系及共同复定向处理这一入口；V59 以完整关系响应与可逆读口轨道
处理正性的供应条件。[[8](#ref-v58), [9](#ref-v59)]
这里只证明两个既定 Lüders 读口的盲区，不排除更丰富复理论，也不声称已分类所有实模拟模型。

<a id="section-6-4"></a>

### 6.4. 复结构的另一个入口：三轴 Clifford 关系

<a id="prop-clifford"></a>

#### 命题 6.3（三条反对易实轴生成复二元代数）

在实含幺 $*$ 代数中声明自伴元 $X,Y,Z$ 满足

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
X^2=Y^2=Z^2=I,\qquad XY=-YX,\quad YZ=-ZY,\quad ZX=-XZ.
$$

</div>

令 $J=XYZ$，则 $J$ 与三个生成元对易，$J^\dagger=-J$、$J^2=-I$。
这些关系的通用实代数同构于作为实代数的 $M_2(\mathbb{C})$。

**证明。**

把 $X$、$Y$ 或 $Z$ 穿过另外两个生成元，需要两次换号，
所以 $J$ 与它们对易。反转三个因子顺序需要三次换号，
得 $J^\dagger=-J$；同样 $J^2=(-1)^3X^2Y^2Z^2=-I$。
每个单词利用平方和反对易关系，化为
$I,X,Y,Z,XY,YZ,ZX,XYZ$ 的实线性组合，故通用代数实维数至多八。
将 $X,Y,Z$ 分别送到三个 Pauli 矩阵，这八个像张成
$I,\sigma_x,\sigma_y,\sigma_z,iI,i\sigma_x,i\sigma_y,i\sigma_z$，
它们实线性独立，恰为 $M_2(\mathbb{C})$ 的实基。因此映射为同构。

∎

于是 $J$ 可作为“乘以 $i$”的内部实现，
$e^{\theta J}=\cos\theta\,I+\sin\theta\,J$ 给相位旋转。
这承接项目 V58 的已有三轴重构，提供了替换“直接给复数域”的已知数学结构。[[8](#ref-v58)]
但是三轴反对易关系本身仍须说明物理根据；
多个内部模块怎样共享同一个复结构、实际供应哪些非交换读口，
仍属于组合与控制的相容条件。两投影引理没有自动证明这些更强条件。

<a id="section-7"></a>

## 7. 一个更紧凑、但不隐藏前提的公理候选

<a id="section-7-1"></a>

### 7.1. 三组结构前提

以下给历史入口的三组公理候选，承接 V22 的正核路线。[[2](#ref-v22)]
“三组”表示组织更简洁，并不证明独立假设只有三个或已经逻辑最小。
完整关系对象、允许过程族及可访问读口必须一起声明。

<a id="statement-7-1"></a>

#### 定义 7.1（R：复正关系及内部组合）

对声明的历史表达集 $\mathsf H$ 给 Hermitian 复核
$K:\mathsf H\times\mathsf H\to\mathbb{C}$。对任意有限历史族及复系数，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\sum_{i,j}\bar c_i c_jK(h_i,h_j)\ge0.
$$

</div>

指定空历史 $e$ 满足 $K(e,e)=1$。
完整归一历史可要求 $K(h,h)=1$；分支表达允许小于一或等于零。
若声明两个独立准备端口，组合规则明确给出

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
K_{AB}((a,b),(a',b'))=K_A(a,a')K_B(b,b').
$$

</div>

此积核条件只针对声明的独立准备，不能套用于所有相关整体态。

R 明确输入复数域、任意有限族的整体正性与独立端口的组合规则。
两两正性不足以保证整个核正；“唯一本体”也没有自动供应这些数学性质。
例如对 $1/2<a\le1$，矩阵

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
G=\begin{pmatrix}1&-a&-a\\-a&1&-a\\-a&-a&1\end{pmatrix}
$$

</div>

每个二阶主块均正半定，但
$(1,1,1)G(1,1,1)^T=3-6a<0$。
二元模块要全局闭合，必须连同这些更大历史族的相容条件一起保留。

<a id="statement-7-2"></a>

#### 定义 7.2（C：完整关系守恒与续接）

每个允许过程给有限结果集 $O$、后继分支符号 $r_oh$、一个后继正核 $K_+$，并满足

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\boxed{K(v,w)=\sum_oK_+(r_ov,r_ow)\qquad
\text{对所有输入历史 }v,w.}\qquad\text{(C)}
$$

</div>

后继分支可以次归一或为零，不要求每个 $K_+(r_oh,r_oh)=1$。
被声明为可逆的完整续接有相容逆续接；内部物理实现须声明所需的就绪记录容量。

式 (C) 不只保存每个输入的归一化，也保存任意两条输入之间的交叉关系。
它是本文建议作为中心的*完整关系守恒律*。
每个历史单独归一，无法保证线性关系在叠加输入及递归后继中仍成立。

<a id="statement-7-3"></a>

#### 定义 7.3（W：正交细化的权重与记录条件化）

一个分支的非负权重只依赖其重构向量的长度，记为 $F(\|\xi\|)$；
单位向量权重为一。
当一个记录分解为若干互斥、正交的细记录时，总权重等于细权重之和，
并对保持范数的细化一致。
这里要求该规则覆盖全部实质量 $s,t\ge0$、$s+t\le1$ 的细化；
若实际只声明一个离散菜单，须另证其覆盖或适当延拓，不能直接使用全区间结论。
实际读得非零权重记录后，以该记录分支的归一条件态预测其后读出。

“只依赖长度”是明确的响应相容假设；实际记录条件化是明确的操作解释。
它们不能仅从式 (C) 的代数等号里读出来。

<a id="section-7-2"></a>

### 7.2. 从关系核到 Hilbert、酉门与仪器

<a id="thm-reconstruct"></a>

#### 定理 7.4（三组前提的条件重构）

在 R、C、W 下，声明的历史与过程具有如下表示：

1. 存在最小复 Hilbert 空间、向量 $\xi_h$ 及单位来源
   $\Omega_K=\xi_e$，满足 $\langle\xi_v,\xi_w\rangle=K(v,w)$；
   该表示在生成闭包上唯一到酉等价。

2. 每个完整分支过程给线性算子
   $M_o:\mathcal{H}_K\to\mathcal{H}_{K_+}$，满足
   $\sum_oM_o^\dagger M_o=I$；
   完整记录映射 $V\xi=\sum_oM_o\xi\otimes|o\rangle$ 为等距。
   可逆单分支续接为酉。

3. 分支权重唯一为平方范数，
   $p_o=\|M_o\psi\|^2$；归一条件态为
   $M_o\psi/\|M_o\psi\|$。
   忽略记录得到完全正保迹通道
   $\Phi(\rho)=\sum_oM_o\rho M_o^\dagger$。

4. 在 R 声明的独立准备积核上，最小组合表示为相应 Hilbert 空间的张量积。

> **Markdown 编者注。** 本定理的 $\psi$ 为单位输入，归一分支公式仅在 $p_o>0$ 时使用。历史集不要求有限或可数；每个过程的结果集有限，$M_o:\mathcal H_K\to\mathcal H_{K_+}$ 是有界压缩；若这些 Hilbert 空间无限维，密度输入指正迹一的迹类算子，Kraus 和是其上的通道，完全正性指所有有限参考扩张。单分支的“相容逆”须在两个最小生成空间上互为双边逆，才得满射酉。独立组合项使用全部已声明的历史对及积核，其代数张成在 Hilbert 张量积中稠密。W 只确定单位区间内的径向权重；离散细化菜单不能代替其全实区间前提。

**证明。**

**第一步：核表示。**
令 $\mathcal F$ 为历史符号的有限复线性组合空间，
定义半内积

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\left\langle\sum_ic_i[h_i],\sum_jd_j[k_j]\right\rangle
=\sum_{i,j}\bar c_i d_jK(h_i,k_j).
$$

</div>

R 给非负性。其零范数空间 $\mathcal N$ 与全部向量正交，
因为半内积的 Cauchy–Schwarz 不等式可由
$\|x+ty\|^2\ge0$ 对任意复 $t$ 得到。
商 $\mathcal F/\mathcal N$ 后完成，得到 Hilbert 空间；
$\xi_h=[h]+\mathcal N$，$\|\Omega_K\|^2=K(e,e)=1$。
另一最小实现中，$\xi_h\mapsto\widetilde\xi_h$ 保持一切有限 Gram 和，
故下降为稠密子空间上的等距并延拓成满射酉。

**第二步：守恒律使递归良定。**
先在形式线性组合上置

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
M_o\sum_ic_i\xi_{h_i}=\sum_ic_i\xi^+_{r_oh_i}.
$$

</div>

由 (C)，

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\sum_o\left\|\sum_ic_i\xi^+_{r_oh_i}\right\|^2
=\left\|\sum_ic_i\xi_{h_i}\right\|^2.
$$

</div>

若输入代表零，则每个非负输出范数为零，
所以 $M_o$ 与输入表示方式无关，线性关系确实下降到商空间。
每个 $M_o$ 是压缩，可连续延拓；极化给
$\sum_oM_o^\dagger M_o=I$。
把所有分支保存在正交内部记录中即得等距 $V$。
单分支有相容逆时既等距又满射，所以酉；
对声明的有限内部接口，就绪子空间的酉扩张依第 2 节构造；
此处未把该有限容量论证无条件推广到任意无限维实现。

**第三步：平方权重。**
置 $w(t)=F(\sqrt t)$，$0\le t\le1$。
正交分解的范数几何和 W 给
$w(s+t)=w(s)+w(t)$，$s,t\ge0$、$s+t\le1$；
$w\ge0$、$w(1)=1$。
于是 $w(1/n)=1/n$，进而 $w(m/n)=m/n$。
非负可加性还给单调性；对任意实 $t$ 用有理数上下逼近，得到 $w(t)=t$。
因此

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
F(r)=r^2\quad(0\le r\le1),\qquad p_o=\|M_o\psi\|^2.
$$

</div>

这不是将概率预先定义为平方后再证明；输入的是范数依赖与正交细化可加性。
平方指数由正内积的 Pythagoras 结构和这种权重相容共同确定。
条件态按 W 归一。对密度输入作线性延伸给 Kraus 和；
任意内部参考上也有 $(M_o\otimes I)X(M_o^\dagger\otimes I)\ge0$，
故完全正；完备式给保迹。

**第四步：独立端口。**
映射
$\xi_{(a,b)}\mapsto\xi_a\otimes\xi_b$
由积核规则保持内积，故在最小生成闭包上为酉同构。
这证明声明的组合规则如何产生张量表示，未从无组合前提的唯一 $\Omega$ 推导张量积。

∎

该定理表示*给定关系数据后的表示唯一性*，并不从公理中唯一计算出实际宇宙态的全部内容。
只有声明为允许的过程被重构；不能仅因写出了全部数学酉群便声称具体物理门菜单已经普适。
复 Hilbert 形式也容纳只访问交换读口的经典模型；量子非经典性还需要实际允许的非交换读口与控制。

<a id="section-7-3"></a>

### 7.3. 平方律、三轴球与全交叉项的真正联系

R 给复二次型，C 保持其全部交叉项，W 把正交分支的几何质量解释成可加权重。
在二维接口上，这三层可以写成

<div style="display:block;width:100%;min-width:0;box-sizing:border-box;overflow-x:auto;max-width:100%;overflow-y:hidden">

$$
\psi=(\alpha,\beta)
\ \longmapsto\
\rho=\psi\psi^\dagger
\ \longmapsto\
r=(2\Re\bar\alpha\beta,\ 2\Im\bar\alpha\beta,\
|\alpha|^2-|\beta|^2).
$$

</div>

关系 $\bar\alpha\beta$ 的实部和虚部提供横向两轴；
归一化与对角差提供纵向坐标；秩一给球面约束。
这里出现的平方有一致来源，但不能仅凭“二元”或“加法乘法”排除其他数学理论。

对于一个固定复线性 $T$，若对所有 $\psi$ 有
$\|T\psi\|=\|\psi\|$，极化给 $T^\dagger T=I$；
有限等维时才推出酉。
若每次把任意输出除以自身范数，则一般是非线性操作，
既不自动保存交叉项，也不能替代 (C)。
这也是“归一化”与“酉性”之间必须保留的量词条件。

<a id="section-8"></a>

## 8. 经典记录的来源与仍然开放的量子起源问题

<a id="statement-8-1"></a>

#### 命题 8.1（记录代数上的经典概率与重复确定性）

正交记录投影 $R_o=|o\rangle\langle o|$ 生成交换代数
$\mathcal C_R=\{\sum_oa_oR_o\}$。
完整记录态在此代数上的限制由普通概率向量 $p_o$ 唯一描述。
条件于已经读得 $o$ 后，记录代数上的响应为
$\langle\sum_ja_jR_j\rangle_o=a_o$；
立即重复同一非破坏的理想 Lüders 记录读出，结果仍为 $o$。

**证明。**

$R_oR_j=\delta_{oj}R_o$，所以效果可同时对角化，
响应为 $\sum_op_oa_o$，其中 $p_o\ge0$、$\sum_op_o=1$。
条件记录投影 $R_o$ 令所有其他对角分量为零，得到点质量与重复性。

∎

这说明经典性来自所访问的交换记录代数及其稳定读法。
整体仍可能是相干纠缠态；对退相干像中的高维块，量子自由度仍存在。
在已读记录上没有其他答案，不等于所有不相容问题都没有其他可能。
指针的长期稳定还要求后续作用不把它重新混合；
一次投影的幂等性不是任意未来动力学下永远稳定的保证。

| 可由本文证明的结构 | 明确承担推导的前提 |
| --- | --- |
| Hilbert 表示 | 任意有限族的复正历史核。 |
| 酉续接与关系传导 | 全交叉项守恒、线性商的良定性及可逆闭合。 |
| 平方概率与 Born 形式 | 正内积几何、范数依赖、非负正交细化可加及单位标定。 |
| 局部通道与退相干 | 内部记录等距，加上所声明的读口限制／忽略记录。 |
| 条件锁定唯一纯态 | 正关系残差的共同核一维，且实际条件分支非零。 |
| 非选择锁定唯一混态 | 共同可见代数只有 $\mathbb{C} I$。 |
| 二元三轴模块 | 二维正矩阵；两投影的共同一维／二维分块。 |
| 独立端口的张量积 | 显式积核组合规则，不能由唯一来源单独推出。 |

仍不能从本文独自推出：为何自然选择这套复正关系而非所有其他概率模型；
为何特定 Clifford 关系、允许控制族及复合规则是物理的；
为何实际经验对应某一记录；
以及局域性、具体时空、动力学、质量或基本常数。
V58、V59 提供了其中若干问题的条件重构入口，不能把其前提再隐去。[[8](#ref-v58), [9](#ref-v59)]

因此，下一步最有价值的简化是比较*独立前提*：
哪一项能被更弱、可操作的关系条件替代，并给出等价证明或反模型。
把多个要求并入同一个编号，只降低文本长度，不自动降低理论假设强度。

**本轮的精确命题。**
*两个读口通过重复投影保留共同结构。
在振幅空间上，共同结构一维且输入在共同空间上有非零质量时，
指定结果的条件序列趋于唯一纯态；
在算符空间上，共同结构只有标量时，非选择态锁定为最大混态。
完整相干关系在内部等距记录中守恒，局部可见性与条件支持分别受不同约束。*
这个表述同时保留了唯一本体、历史内生性、AURIC 二元模块和用户关于关系锁定的直觉，
并给出每一部分可检验的数学条件。

## 固定来源与文献

<a id="ref-v18"></a>

**[1]** trureturing 固定提交，
[V18：Triangulation, Collapse and Recursive Unitary Gates](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_TRIANGULATION_COLLAPSE_AND_RECURSIVE_UNITARY_GATES_V18.md)。
使用定义 4.1、定理 8.1、命题 8.2–8.3 及定理 9.1。

<a id="ref-v22"></a>

**[2]** trureturing 固定提交，
[V22：Relative Gate Histories, Observation Quotients and Recursive Closure](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)，
定义 6.1、定理 6.2–6.4，完整正核及全交叉项完备式。

<a id="ref-v37"></a>

**[3]** trureturing 固定提交，
[V37：Binary Relations, Unitary Representation and Golden Gate Universality](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)，
§§3–4。复用此前核对来源并重读所用编码部分。

<a id="ref-v38"></a>

**[4]** trureturing 固定提交，
[V38：Complete Quantum Processes, Internal Memory and Rank Boundary Stability](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_COMPLETE_QUANTUM_PROCESSES_INTERNAL_MEMORY_AND_RANK_BOUNDARY_STABILITY_V38.md)，
§§3、7，过程秩及内部记录。

<a id="ref-v52"></a>

**[5]** trureturing 固定提交，
[V52：Pure-State Quotient Geometry, Quadratic Relation Generators and Lossless Recursion](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)，
定理 4.1–4.2、命题 8.5。

<a id="ref-v55"></a>

**[6]** trureturing 固定提交，
[V55：Exterior Closure of Binary Relations, Three-Axis Errors and Conditional Quantum Origin](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md)，
§§2、7.1、10.1。

<a id="ref-v56"></a>

**[7]** trureturing 固定提交，
[V56：Universal Internal Binary Cuts, Operator Three-Axis Purity and Endogenous Recursion](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md)，
§6.1。

<a id="ref-v58"></a>

**[8]** trureturing 固定提交，
[V58：Relational Axioms, Common Complex Phase and Conditional Quantum Reconstruction](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md)，
公理 R/P/C/G、局部 Clifford 结构及总重构定理。

<a id="ref-v59"></a>

**[9]** trureturing 固定提交，
[V59：Local Tomography, Coherent Readout Orbits and Quantum Positivity Origin](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md)，
RC 定义、定理 3.2–3.3、推论 3.4 及总定理 8.3，关系响应相容与正性供应。

<a id="ref-watrous"></a>

**[10]** John Watrous,
*The Theory of Quantum Information*, Chapter 4, Definition 4.4.
[作者公开教材原文](https://cs.uwaterloo.ca/~watrous/TQI/TQI.4.pdf)。
使用 pinching 的定义与非选择测量解释；本文秩及范数证明自足。

<a id="ref-alternating"></a>

**[11]** Cătălin Badea, Sophie Grivaux, Vladimir Müller,
*The Rate of Convergence in the Method of Alternating Projections*,
St. Petersburg Mathematical Journal 23 (2012), 413–434.
[作者论文版本](https://arxiv.org/pdf/1006.2047)；
[DOI](https://doi.org/10.1090/S1061-0022-2012-01202-1)。
查读引言的经典两子空间结果及精确范数率归属；本文提供有限维证明。

<a id="ref-conditional"></a>

**[12]** David W. Kribs, Jeremy Levick, Rajesh Pereira, Mizanur Rahaman,
*Operator Algebra Generalization of a Theorem of Watrous and Mixed Unitary Quantum Channels* (2023),
[arXiv:2306.04077](https://arxiv.org/pdf/2306.04077)。
使用 §2 有限维保迹条件期望与 Hilbert–Schmidt 投影的对应。

<a id="ref-jordan"></a>

**[13]** Daniel Nagaj, Pawel Wocjan, Yong Zhang,
*Fast Amplification of QMA*,
Quantum Information and Computation 9 (2009), 1053–1068.
[arXiv:0904.1549](https://arxiv.org/pdf/0904.1549)；
[DOI](https://doi.org/10.26421/QIC9.11-12-8)。
使用 §2.1 及附录 A 的两投影一维／二维分解。


</div>


<details data-production="ending">
<summary>原稿结束标记（原样保留）</summary>

```tex
\end{thebibliography}
\end{document}
```

</details>

<details>
<summary>原稿 TeX 前导、编译说明与制作元数据（作者原文）</summary>
<textarea readonly cols="24" rows="16" aria-label="作者原始 TeX 前导">% !TeX program = xelatex
% Compile twice with XeLaTeX. Optional:
% \def\AURICFontPath{/absolute/path/to/CJK/fonts/}
% This is a research continuation, not a change to the upstream repository.
% Mathematical arguments are on paper; no CAS, numerics, simulation or testing.
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
\XeTeXlinebreaklocale &quot;zh&quot;
\XeTeXlinebreakskip=0pt plus 1pt
\usepackage{amsmath,amssymb,amsthm,mathtools,bm,mathrsfs}
\usepackage{booktabs,array,tabularx,enumitem,fancyhdr,xcolor,needspace}
\definecolor{auricblue}{RGB}{24,53,79}
\usepackage[unicode,colorlinks=true,linkcolor=auricblue,urlcolor=auricblue,citecolor=auricblue]{hyperref}
\hypersetup{pdftitle={AURIC v70：固定读口、关系递归与平方起源},
pdfauthor={AURIC research continuation},
pdfsubject={Fixed readout tomography, Gram uncertainty, recursive probability and a positive relational core}}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\HH}{\mathcal H}
\renewcommand{\AA}{\mathcal A}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\Var}{\operatorname{Var}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\spanof}{\operatorname{span}}
\newcommand{\Herm}{\operatorname{Herm}}
\newcommand{\supp}{\operatorname{supp}}
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
\renewcommand{\refname}{固定来源与文献}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{2pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC：固定读口、关系递归与平方起源}
\fancyhead[R]{\small v70 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}</textarea>
</details>

# 固定读口、关系递归与平方起源

从 AURIC 五模式层析到正关系公理

AURIC 量子起源研究　 定义、定理与纸面证明　 v70.0

2026 年 11 月 1 日　 Asia/Singapore

## 摘要

本文把“同一基底反复读出、关系之上还有关系、平方是最低关系层”的直觉
整理成六个可证明的结论。固定的 AURIC 五模式投影测量，在一个明确的二元编码上
信息完备；同一模板的多端口联合概率又可完整恢复高维态，但各端口的局部三轴并不充分。
母空间读口的对易性与逻辑三轴的不对易性相容，因为压缩不保持乘法。
不确定性可写成中心化关系 Gram 矩阵的正性；达到等号恰好意味着涨落向量精确线性相关，
并不意味着两个量都没有涨落。共同相位等价下，全域多项式不变量的最低非恒定次数是二；
在既定正交振幅几何中，持久记录、递归概率链律与同一径向响应进一步唯一确定平方概率。
最后给出一个紧凑的关系公理候选：复 $C^*$ 关系代数、固定实际来源的一个归一正响应、
以及已声明的内部控制和记录协议。GNS 构造从中重建源向量、Hilbert 表示、
酉历史与平方读出。这个压缩明确保留复数性、正性、复合与实际控制的前提，
不把符号上的简洁当作已经完成量子物理的无条件起源证明。

## 1. 本轮结论、来源与范围

**可以把这轮直觉收紧为：
一个固定的读出模板可以递归使用；需要保留的是完整的正关系结构，
它的最低共同相位不变多项式层是二次，概率则是这个层上的正线性响应。**
这使“三维读口、线性关系、平方律、关系递归”进入同一条证明链，
同时保留各自的适用条件。

本轮唯一活动 HEAD 请求于新加坡时间 2026-11-01 18:03:40
遇到本地 socket 权限拒绝，未收到 HTTP 响应；没有重试或取得更新提交。
本文使用已保留并核对八份 Git blob 身份的固定提交

<span>5cf95e1a<wbr>e01f7ed8<wbr>6735c04a<wbr>d8d752cb<wbr>19b1a58b</span>。

因此本文是结合已核验快照的研究续篇，不声称核验了该提交以后的最新进展；
“v70”是本对话稿件编号。

<aside data-v70-note="scope">

> **整理者核读注（全文范围与行为归属；非作者原文）。** 本文作为 LOCAL V70 稿件保留；原稿明言这是研究续篇，并非上游仓库变更。原稿中的 HEAD、socket、八份 blob、阅读与方法报告均归属于原作者所述写作情境，不是本地整理者本轮实施行为，也不是自动批准审查拒绝。这里的纸面与来源核读不构成 Lean/kernel、原生控制、物理或经验认证，不构成无条件起源、最小性或优先权认证；单独的 V66–V69 工作不因本稿改变。

</aside>

| 项目结果  |  本轮作用 |
| --- | --- |
| V37 §§3–4、12  |  原生五模式码、三轴反演、统计完备与物理可逆性的区别、五标签随机更新边界。 |
| V52 §5  |  共同相位不变多项式由二次关系生成；最低非恒定次数是二。 |
| V55 §§2、4、6  |  二元正关系、外积闭合、线性零残差与读出边界。 |
| V56 §§5、9  |  任意内部二元切分的算子三轴、纯度缺陷和递归闭合。 |
| V59 §§3、6–7  |  同域响应一致性、递归权重定理、固定五模式读口。 |
| V22 §8  |  全部允许未来实验定义的预测商。 |
| 仪器与控制卷  |  五标签字典、条件仪器、控制资源与稳定性条件。 |

上述结果按所需段落复核，没有重审整个仓库的全部依赖。
GNS、Pauli 层析和 Schrödinger–Robertson 不等式是标准数学。
本轮的推进在于连接这些结果，并明确“固定读口递归”需要怎样保留关系。
全文数学均为纸面论证；程序只用于来源处理、文档编译和版面检查。

## 2. “每个位置唯一读出”的严格含义

#### 定义 2.1（固定来源、完整历史与内部接口）

固定唯一实际源向量 $\Omega$，$\|\Omega\|=1$。
观察者、程序、记录和环境均包含在完整载体中。
门历史 $h=(g_1,\ldots,g_m)$ 的每个字母已指定作用地址和酉解释，

$$
U_h=U_{g_m}\cdots U_{g_1},\qquad \Psi_h=U_h\Omega.
$$

内部接口 $S$ 的态是
$\rho_h^S=\operatorname{Tr}_{S^c}|\Psi_h\rangle\langle \Psi_h|$。
接口地址 $x$ 与仪器 $\{\mathcal I_{x,s}\}_s$ 给出

$$
p(s\mid h,x)=\operatorname{Tr}\mathcal I_{x,s}(\rho_h^S).
$$

这里每个 $\mathcal I_{x,s}$ 完全正，且总和保迹。

<aside data-v70-note="instrument-domain">

> **整理者核读注（张量接口与仪器的定义域；非作者原文）。** 偏迹表达式以已声明的 Hilbert 张量分解 $\mathcal H=\mathcal H_S\otimes\mathcal H_{S^c}$ 为前提；一般内部子代数并不自动给出这样的因子分解。态为正迹类且迹一，酉与所用观测算符为有界算符。离散仪器作用在迹类上：有限结果时求和直接成立，可数结果时须在迹范数意义给出总和与保迹条件；连续结果须另给可测仪器，不能只用单标签公式替代。条件态只在所列正概率事件上定义。

</aside>

#### 命题 2.2（单值性分三层）

完整的 $\Omega,h,S,x,\mathcal I$ 单值确定概率律；
若实际记录为 $s$ 且概率非零，则单值确定条件态

$$
\rho_{h,x;s}=
\frac{\mathcal I_{x,s}(\rho_h^S)}
{\operatorname{Tr}\mathcal I_{x,s}(\rho_h^S)}.
$$

若解码函数 $d(s)$ 已给定，它也单值确定该记录的数据。
这三个单值性不推出一次记录等于完整概率律。

**证明。**

分别是给定映射的求值、非零标量归一化和函数求值。
不同概率律可以对同一个标签赋予正概率，因此一个标签一般不能反推出唯一概率律。

∎

若把 $x$ 解释成物理位置 $x\in\mathbb{R}^3$，空间模型已经另行给入。
二元关系恰有三个实 Bloch 坐标，不等于证明了物理空间恰有三维。
全局历史唯一也不把所有约化态的演化变成局部酉。
与内部环境耦合后，要仅以局部态给出完全正保迹更新，
须声明相应的制备和记忆条件，或把相关部分纳入接口；
一般的系统与环境相关可能使局部边缘不足以预测下一步。
历史字串单增表示记录的前缀关系，不自动表示 Hilbert 维数或可用控制不断增加。

## 3. 同一五模式基底真的能读出完整二元态

### 3.1. 原生标签与固定编码

沿用项目标签字典及模式顺序 $(0,2,3,5,25)$ ［[7](#ref-instrument)，[8](#ref-control)］：

$$
\begin{gathered}F[\mathrm{null}]\leftrightarrow0,\\F[1]\leftrightarrow2,\quad F[2]\leftrightarrow3,\\F[3]\leftrightarrow5,\quad F[1,3]\leftrightarrow25.\end{gathered}
$$

三轴按 $F[1],F[3],F[2]$ 排列，定义

$$
\begin{aligned}
N_x&=\operatorname{diag}(0,1,0,0,1),\\
N_y&=\operatorname{diag}(0,0,0,1,1),\\
N_z&=\operatorname{diag}(0,0,1,0,0).
\end{aligned}
$$

它们是母空间 $\mathbb{C}^5$ 中彼此对易的占据投影。
令 $\sigma_x,\sigma_y,\sigma_z$ 为标准 Pauli 矩阵，记

$$
\begin{gathered}\nu=\frac1{1+2\sqrt3+\sqrt{11}},\\a_\nu=\frac{\nu(\sqrt3+\sqrt{11})}{2},\\u_0=(a_\nu,a_\nu,\nu).\end{gathered}
$$

V37 给出以下固定效果 ［[1](#ref-v37)，[5](#ref-v59)］：

<a id="eq:five-effects"></a>

$$
\begin{gathered}E_{25}=\frac{\nu}{2}(\sqrt3 I-\sigma_x-\sigma_y-\sigma_z),\\E_0=3E_{25},\\E_2=\frac{\nu}{2}(\sqrt{11}I+3\sigma_x+\sigma_y+\sigma_z),\\E_5=\frac{\nu}{2}(\sqrt{11}I+\sigma_x+3\sigma_y+\sigma_z),\\E_3=\nu(I+\sigma_z).\end{gathered}
$$

（1）

#### 定理 3.1（固定读口的三轴层析）

<a id="thm:fixed"></a>

存在一个固定等距嵌入 $J:\mathbb{C}^2\to\mathbb{C}^5$，使

$$
J^\dagger|s\rangle\langle s|J=E_s.
$$

对任意逻辑态 $\rho=(I+r\cdot\sigma)/2$，在同一个母空间基底测量编码态
$J\rho J^\dagger$，所得概率满足

<a id="eq:u-affine"></a>

$$
\begin{gathered}p_s=\operatorname{Tr}(\rho E_s),\\u=(p_2+p_{25},p_5+p_{25},p_3)\\=u_0+\nu r.\end{gathered}
$$

（2）

于是

$$
\begin{gathered}\boxed{\rho=\frac12\left[I+\frac{u-u_0}{\nu}\cdot\sigma\right]},\\\|u-u_0\|\le\nu.\end{gathered}
$$

并且以 $D(\rho,\tilde\rho)=\frac12\|\rho-\tilde\rho\|_1$ 表示迹距离时，

$$
D(\rho,\tilde\rho)=\frac{\|u-\tilde u\|}{2\nu}.
$$

**证明。**

$tI+v\cdot\sigma$ 的特征值为 $t\pm\|v\|$。
式 [（1）](#eq:five-effects) 的各标量系数恰等于对应向量的长度，
所以各 $E_s$ 正且秩一；相加时 Pauli 系数消去，恒等项系数为
$\nu(1+2\sqrt3+\sqrt{11})=1$。
写 $E_s=|\eta_s\rangle\langle \eta_s|$，定义

$$
J\psi=\sum_s|s\rangle\langle\eta_s,\psi\rangle.
$$

由 $\sum_s E_s=I$ 得 $J^\dagger J=I$ 及所需压缩公式。
直接相加效果给出

$$
\begin{gathered}E_2+E_{25}=a_\nu I+\nu\sigma_x,\\E_5+E_{25}=a_\nu I+\nu\sigma_y,\\E_3=\nu I+\nu\sigma_z.\end{gathered}
$$

取期望便得 [（2）](#eq:u-affine)。正性等价于 $\|r\|\le1$。
最后 $\rho-\tilde\rho=(r-\tilde r)\cdot\sigma/2$
的特征值为 $\pm\|r-\tilde r\|/2$，故迹距离公式成立。

∎

这给“同一个基底持续测量”一个明确的正向实例。
一般 POVM 的投影扩张及信息完备性属于标准测量理论 ［[9](#ref-watrous)］；
这里的五效果和三轴反演是项目的特定构造。
结论只量化固定编码态族，不声称任意五维态都能由一个基底的对角概率恢复。

#### 推论 3.2（关系坐标与归一化的位置）

在上述编码族内，令 $\kappa=p_{25}$，则

$$
\begin{gathered}\kappa=\frac{1-u_x-u_y-u_z}{2},\quad p_0=3\kappa,\\p_2=u_x-\kappa,\quad p_5=u_y-\kappa,\quad p_3=u_z.\end{gathered}
$$

$F[\mathrm{null}]$ 是结果标签；归一化是 $\sum_s E_s=I$ 与 $\operatorname{Tr}\rho=1$。

**证明。**

$E_0=3E_{25}$ 给 $p_0=3\kappa$，其余等式由三轴定义及总概率一解出。

∎

若没有固定编码约束，一般五概率的同样三轴 $(X,Y,Z)$ 只给

$$
\begin{gathered}p_\kappa=(1-X-Y-Z+\kappa,\\\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),\end{gathered}
$$

$$
\begin{gathered}\max(0,X+Y+Z-1)\\\le\kappa\le\min(X,Y).\end{gathered}
$$

所以“四推一”确实成立于声明的关系族；不能略掉这个关系族再推广到所有分布。

### 3.2. 同一母基底为什么仍容许不确定性

#### 定理 3.3（压缩不保持乘法）

<a id="thm:compression"></a>

令 $P=JJ^\dagger$，$A_j=J^\dagger N_jJ$。虽然 $[N_x,N_y]=0$，
却有

$$
\boxed{\begin{gathered}[A_x,A_y]\\=J^\dagger(N_xPN_y-N_yPN_x)J\\=2i\nu^2\sigma_z.\end{gathered}}
$$

更一般地，对实对角读出 $D_f,D_g$，

$$
\begin{gathered}J^\dagger D_fD_gJ-(J^\dagger D_fJ)(J^\dagger D_gJ)\\=J^\dagger D_f(I-P)D_gJ.\end{gathered}
$$

**证明。**

在两个压缩算符的乘积中插入 $JJ^\dagger=P$ 即得两式。
再用 $A_x=a_\nu I+\nu\sigma_x$、$A_y=a_\nu I+\nu\sigma_y$
和 $[\sigma_x,\sigma_y]=2i\sigma_z$。

∎

这解释了“固定终端指针”与“逻辑关系不对易”如何共存。
编码 $J$ 和投影 $P$ 已承担相干结构；不能把这一步当作从纯经典对易代数中
不加条件地产生量子性。同一经典标签函数的点乘，也不等于压缩后算符的乘法。

#### 命题 3.4（读口噪声与逻辑涨落分离）

若 $N=N^\dagger$，$A=J^\dagger NJ$，则

$$
J^\dagger N^2J-A^2=J^\dagger N(I-P)NJ\succeq0,
$$

$$
\begin{gathered}\operatorname{Var}_{J\rho J^\dagger}(N)\\=\operatorname{Var}_\rho(A)+\operatorname{Tr}[\rho J^\dagger N(I-P)NJ].\end{gathered}
$$

**证明。**

第一式右边是 $B^\dagger B$，其中 $B=(I-P)NJ$。
编码前后的均值相同，二阶矩相减即得第二式。

∎

### 3.3. 一次标签、完整概率与后续递归

每次标签确实可以解码成一个三元数据：

$$
\begin{gathered}n(s)=\bigl(\mathbf1_{\{2,25\}}(s),\mathbf1_{\{5,25\}}(s),\mathbf1_{\{3\}}(s)\bigr),\\u=\mathbb E[n(s)].\end{gathered}
$$

但 $n(s)$ 是一次样本，$u$ 是均值。
层析讨论的是概率律的可辨识性；要从实际记录估计它，还需稳定制备、
重复记录或另外声明的统计条件。固定唯一宇宙来源并不自动提供这些资源。

#### 命题 3.5（尖锐读出后不能无条件沿用原码）

<aside data-v70-note="luders">

> **整理者核读注（尖锐模式的测后约定；非作者原文）。** 此命题的测后态采用模式投影 $P_s=|s\rangle\langle s|$ 的 Lüders 仪器 $\mathcal I_s(\tau)=P_s\tau P_s$。仅给同一 PVM 的效果并不强迫任意实现都采用这个更新；带重制备的仪器可有不同测后态。这一约定不改变后文关于经典测量通道无通用物理左逆的独立论证。

</aside>

母空间的尖锐模式测量，在正概率结果 $s$ 上给出 $|s\rangle\langle s|$，
而每个 $|s\rangle$ 都不属于 $J\mathbb{C}^2$。

**证明。**

$\|P|s\rangle\|^2=\operatorname{Tr} E_s$。
五个迹依次为
$(3\nu\sqrt3,\nu\sqrt{11},2\nu,\nu\sqrt{11},\nu\sqrt3)$，
每个都小于一，因此 $P|s\rangle\ne|s\rangle$。

∎

这不禁止递归，而是要求明确测后仪器、返回逻辑端口的处理，
或把完整相干记录保留在更大的内部系统中。
统计信息完备也不等于存在恢复所有未知态的物理逆通道：
若测量标签能经通道恢复 $|0\rangle\langle 0|$ 与 $|1\rangle\langle 1|$，
则每个正权标签的输出态必须分别等于相应纯态。
但两输入在 $s=25$ 上都有正概率，同一标签不可能同时恢复两个不同纯态。
这给出 V37 不可逆性结论的一个直接证明。

## 4. 递归保留完整关系，才能保留完整信息

### 4.1. 同一固定模板的联合层析

定义固定的实重构权重

$$
\begin{gathered}f_0(s)=1,\\f_x(s)=\frac{\mathbf1_{\{2,25\}}(s)-a_\nu}{\nu},\\f_y(s)=\frac{\mathbf1_{\{5,25\}}(s)-a_\nu}{\nu},\\f_z(s)=\frac{\mathbf1_{\{3\}}(s)-\nu}{\nu}.\end{gathered}
$$

这里下标 $0$ 表示 $\sigma_0=I$，并非结果模式 $s=0$。
定理 [3.1](#thm:fixed) 给
$\sum_s f_\alpha(s)E_s=\sigma_\alpha$。

#### 定理 4.1（固定读口的递归信息完备）

<a id="thm:joint"></a>

对 $n$ 个已声明的逻辑二元端口及其联合态 $R$，使用同一编码
$J^{\otimes n}$ 和同一联合模式基底。若保留全部联合概率

$$
p(s_1,\ldots,s_n)=
\operatorname{Tr}[R(E_{s_1}\otimes\cdots\otimes E_{s_n})],
$$

则可唯一恢复

$$
\begin{aligned}r_{\alpha_1\ldots\alpha_n}&=\sum_{\mathbf s}p(\mathbf s)\prod_{j=1}^n f_{\alpha_j}(s_j),\\R&=2^{-n}\sum_{\alpha\in\{0,x,y,z\}^n}\\&\quad r_\alpha\,\sigma_{\alpha_1}\otimes\cdots\otimes\sigma_{\alpha_n}.\end{aligned}
$$

**证明。**

单端口重构恒等式张量相乘，取 $R$ 的期望，得到第一式。
Pauli 字串 $P_\alpha=\bigotimes_j\sigma_{\alpha_j}$ 迹正交，且
$\operatorname{Tr}(P_\alpha P_\beta)=2^n\delta_{\alpha\beta}$，
所以第二式是完整算符基展开。

∎

重构权重可为负，它们是统计反演系数，不是事件概率。
乘积权重用于不同端口的张量积；对同一端口，经典函数相乘不代表算符相乘。
完整联合律可以写成所有正概率前缀上的条件律之积；
只保存每个端口的边缘三轴，或一棵只含计算基分支质量的树，并不等价。

#### 命题 4.2（局部三轴与标量分支树会遗漏关系）

$$
\Phi^\pm=\frac{|00\rangle\pm|11\rangle}{\sqrt2}
$$

有相同的单端口态 $I/2$，也有相同的计算基联合分布和条件分支质量，
但它们的完整联合态不同；其 $XX$ 相关分别为 $+1$ 和 $-1$。

**证明。**

偏迹消去交叉项，计算基概率只看振幅模平方，而
$(\sigma_x\otimes\sigma_x)\Phi^\pm=\pm\Phi^\pm$。

∎

因此二元分解可以无损递归，但必须保留交叉关系。
信息存储量、估计样本数和实际控制成本没有因使用同一模板而自动消失。

### 4.2. 高维三轴是算子，而不是三个普通数

在任意已声明切分 $\mathbb{C}^2\otimes K$ 上，将正迹一算符写为

<a id="eq:block"></a>

$$
\begin{aligned}R&=\begin{pmatrix}A&C\\C^\dagger&B\end{pmatrix}\\&=\frac12(I\otimes S+\sigma_x\otimes X+\\&\qquad\sigma_y\otimes Y+\sigma_z\otimes Z),\end{aligned}
$$

（3）

其中

$$
\begin{gathered}S=A+B,\quad X=C+C^\dagger,\\Y=i(C-C^\dagger),\quad Z=A-B.\end{gathered}
$$

这保留了全部高维上下文 ［[4](#ref-v56)］。
$X,Y,Z$ 是 Hermitian 算子，通常不是正态，不能分别直接归一化成密度算符。

<aside data-v70-note="normality">

> **整理者核读注（source.tex:398 术语与迹类定义域；非作者原文）。** 上句“通常不是正态”保留为作者原文；按算子论术语 normal（正规／正态），每个有界 Hermitian 算子都满足 $T^\dagger T=TT^\dagger$，因而必为 normal。这里需要的区别是“未必为正，未必能归一为密度态”，不是“不 normal”。固定来源 V56 §5 的原命题也表述为不必为正。此处对任意 Hilbert 空间 $K$，正迹一的 $R$ 取正迹类算子：块压缩、$S,X,Y,Z$ 及其有限乘积均为有界迹类，$\operatorname{Tr}_2$ 是两个对角块之和，正且保迹。$0\le R\le I$、正迹类迹零即零保证后面的缺陷与纯性论证，不需要把 $K$ 偷换成有限维。

</aside>

继续二元展开是线性算符分解；若要解释成新物理态，需要额外的正性与实现说明。

#### 定理 4.3（算子三轴的纯度缺陷）

对正迹一的 $R$，有

<a id="eq:defect"></a>

$$
\begin{gathered}\mathcal D=2S-S^2-X^2-Y^2-Z^2\\=2\operatorname{Tr}_2(R-R^2)\succeq0.\end{gathered}
$$

（4）

$\mathcal D=0$ 当且仅当 $R$ 为纯态。
纯态时还满足

$$
\{S,X\}+i[Y,Z]=2X
$$

以及 $X,Y,Z$ 的循环两式。

**证明。**

由 $0\le R\le I$ 得 $R-R^2\ge0$。
展开 [（3）](#eq:block) 的平方，并对二元因子取偏迹，
得到 [（4）](#eq:defect)。
若 $\mathcal D=0$，则 $\operatorname{Tr}(R-R^2)=0$；
一个正算符迹为零必为零，所以 $R^2=R$，再由迹一得秩一。
反向显然。最后比较 $R^2=R$ 的 $\sigma_x$ 系数：
平方中的该系数为
$[\{S,X\}+i(YZ-ZY)]/4$，即得所述关系。

∎

这是一种严格的“关系的关系”：三轴之间仍由算子乘法和对易子相连。
标量 Bloch 球是 $K$ 一维时的特例；高维信息没有被强行塞进三个实数。

## 5. 不确定性就是一个关系 Gram 矩阵的正性

### 5.1. 精确线性关系与非零涨落可以共存

以下内积取第二变量线性。固定完整纯态
$\Psi=U_h\Omega$ 和有界 Hermitian 算符 $A,B$；
内部接口的算符可以提升为完整空间上的 $A\otimes I$、$B\otimes I$。
记

$$
\begin{gathered}\Delta A=A-\langle A\rangle I,\quad\Delta B=B-\langle B\rangle I,\\u=\Delta A\Psi,\quad v=\Delta B\Psi.\end{gathered}
$$

再令

$$
\begin{gathered}a=\operatorname{Var} A,\quad b=\operatorname{Var} B,\\C_{AB}=\tfrac12\langle\{\Delta A,\Delta B\}\rangle,\\\mathcal J_{AB}=\tfrac1{2i}\langle[A,B]\rangle.\end{gathered}
$$

二者均为实数，且
$\kappa=\langle u,v\rangle=C_{AB}+i\mathcal J_{AB}$。

#### 定理 5.1（不确定性、关系秩与线性残差）

<a id="thm:uncertainty"></a>

中心化 Gram 矩阵

$$
G=\begin{pmatrix}a&\kappa\\\bar\kappa&b\end{pmatrix}
$$

正半定，因此

<a id="eq:sr"></a>

$$
ab\ge C_{AB}^2+\mathcal J_{AB}^2.
$$

（5）

若 $a>0$，则

<a id="eq:residual"></a>

$$
\min_{\lambda\in\mathbb{C}}\|v-\lambda u\|^2
=b-\frac{|\kappa|^2}{a}
=\frac{\det G}{a}.
$$

（6）

因此 [（5）](#eq:sr) 达到等号，当且仅当
$v=(\kappa/a)u$；这并不要求 $a=b=0$。

**证明。**

对任意复数 $c_1,c_2$，
$c^\dagger Gc=\|c_1u+c_2v\|^2\ge0$，
故行列式非负，得到 [（5）](#eq:sr)。
而

$$
\|v-\lambda u\|^2
=a\left|\lambda-\frac{\kappa}{a}\right|^2
+b-\frac{|\kappa|^2}{a}.
$$

完成平方即得全部结论。

∎

式 [（5）](#eq:sr) 是 Schrödinger–Robertson 不等式；
Schrödinger 原论文的式 (9) 已包含协方差项 ［[10](#ref-schrodinger)］。
这里用它连接 AURIC 的二元关系几何，不声称这是新的不确定性原理。
这些方差描述给定制备中的统计涨落，不能直接等同于仪器误差或估计误差。

#### 推论 5.2（不确定性关系本身落在一个 Bloch 球中）

若 $T=a+b>0$，则

$$
\begin{gathered}\frac GT=\frac12(I+r_G\cdot\sigma),\\r_G=\left(\frac{2C_{AB}}T,\frac{-2\mathcal J_{AB}}T,\frac{a-b}T\right),\end{gathered}
$$

$$
\boxed{1-\|r_G\|^2=\frac{4\det G}{T^2}.}
$$

所以关系球面的边界，恰好表示中心化二元关系的秩一；
在 $a>0$ 时，它也恰好表示最佳线性预测残差为零。

**证明。**

比较矩阵条目，并使用任意迹一二阶 Hermitian 矩阵的
$\det(G/T)=(1-\|r_G\|^2)/4$。

∎

$r_G$ 的第二坐标负号来自所用的 Gram 与 Pauli 约定。
$T=0$ 时没有此归一化；$a=0$ 时也不能使用含 $1/a$ 的残差式。
关系矩阵的秩一，不等于断言原系统必为纯态。

#### 命题 5.3（关系精确而局部量不精确的两个实例）

1.  对 $\Psi=|0\rangle$、$A=\sigma_x$、$B=\sigma_y$，
有 $u=|1\rangle$、$v=i|1\rangle$。所以关系 $v=iu$ 精确，
但 $\operatorname{Var} A=\operatorname{Var} B=1$。

2.  在两比特上，关系算符 $Z\otimes Z$ 与 $X\otimes X$ 对易，
共同的 $+1$ 本征条件唯一选出 $\Phi^+$。
其每个局部 Pauli 分量仍有均值零、方差一。

**证明。**

第一项直接由 Pauli 作用得到。
第二项的 $ZZ=+1$ 子空间为
$\operatorname{span}\{|00\rangle,|11\rangle\}$；
再施加 $XX=+1$，要求两系数相等。
局部态为 $I/2$，故三个局部方差均为一。

∎

这支持“量可以不确定而关系确定”的直觉。
但并非每一种关系都确定，也并非每一种量都不确定：
例如 $|0\rangle$ 上的 $Z$ 方差就是零。
需要由具体算符、状态及其 Gram 矩阵判断。

## 6. 关系的关系不必另立无穷多条公理

### 6.1. 共同酉共轭一次保持所有有限层关系

#### 定理 6.1（非交换关系的协变闭合）

<aside data-v70-note="cov-domain">

> **整理者核读注（共同共轭的算子范围；非作者原文）。** 本段 $U$ 为同一载体上的酉，有限非交换 $*$-多项式的变量为有界算符；有限维矩阵是其特例。期望公式用迹类态配有界读口；“对全部态”的实验室守恒判据取 Hermitian 读口 $C$。本段不处理无界算子乘积的定义域，也不把共同坐标变换认作固定读口守恒。

</aside>

<a id="thm:covariance"></a>

若 $P$ 是有限非交换 $*$-多项式，则

$$
\begin{gathered}P(UA_1U^\dagger,\ldots,UA_mU^\dagger)\\=UP(A_1,\ldots,A_m)U^\dagger.\end{gathered}
$$

因此零恒等式、谱与正性在共同共轭下保持；
若状态也变为 $U\rho U^\dagger$，相应期望值保持。

**证明。**

共轭保持加法、标量乘法、乘法和伴随，例如
$(UAU^\dagger)(UBU^\dagger)=UABU^\dagger$。
对多项式的构造层数归纳即得公式。
其余结论由酉相似及迹的循环性成立。

∎

这里“保持”是共同变换下的关系协变。
若只演化态、固定实验室读口 $C$，期望一般会改变。
对全部 $\rho$ 都有
$\operatorname{Tr}(U\rho U^\dagger C)=\operatorname{Tr}(\rho C)$
的充要条件是 $U^\dagger CU=C$：
两者相减并用 Hermitian 空间迹配对的非退化性即可证明。
因此，不能把任意“关系的关系”自动称为物理守恒量。

### 6.2. 固定有限接口的未来预测关系会闭合

#### 定理 6.2（有限维未来关系闭合）

<aside data-v70-note="future-domain">

> **整理者核读注（有限未来空间的合法性与词序；非作者原文）。** 该递推使用一个固定有限维接口以及处处合法、可在任意有限前缀后重复使用的同一门菜单，初始空间是实际初始效果与 $I$ 的 Hermitian 实线性包。若历史采用 $U_h=U_{g_m}\cdots U_{g_1}$，回拉则为 $U_{g_1}^\dagger\cdots U_{g_m}^\dagger A U_{g_m}\cdots U_{g_1}$；递推覆盖所有有限字。门菜单本身可无限，有限的是 $\operatorname{Herm}(\mathbb C^d)$ 的维数。带条件合法域、适应性仪器或扩容记忆须另保留相应信息，不能直接套用此固定菜单结论。

</aside>

固定 $d$ 维接口、在该接口上合法的固定酉门菜单 $\mathscr U$，
以及包含 $I$ 的初始效果实线性空间 $\mathscr S_0$。
令

$$
\begin{aligned}\mathscr S_{k+1}&=\operatorname{span}_{\mathbb{R}}\bigl(\mathscr S_k\cup\\&\{U^\dagger AU:A\in\mathscr S_k,\ U\in\mathscr U\}\bigr).\end{aligned}
$$

该序列至多经历 $d^2-\dim\mathscr S_0$ 次严格增长便稳定。
稳定空间 $\mathscr S_*$ 是全部允许门字串回拉效果的实线性包。
两态的全部允许未来概率相同，当且仅当

$$
\operatorname{Tr}[(\rho-\tilde\rho)A]=0\qquad(A\in\mathscr S_*).
$$

**证明。**

$\operatorname{Herm}(\mathbb{C}^d)$ 的实维数为 $d^2$，每次严格包含至少增一维。
一旦相邻空间相等，定义中的回拉已闭合，后续不再增长。
归纳可知第 $k$ 层恰包含长度至多 $k$ 的回拉效果的线性包，
因而得到稳定空间的说明。概率等价再由线性性得出。

∎

这是对 V22 未来预测商的有限维线性整理 ［[6](#ref-v22)］。
若观察者接口和记忆不断扩容，不能套用一个固定 $d$ 的上界；
此定理也不是样本复杂度或计算成本保证。

## 7. 平方是最低相位不变多项式层，而不是“没有关系”

#### 定义 7.1（全域多项式关系读出）

已给复线性振幅 $z\in\mathbb{C}^d$，并把 $z$ 与 $e^{i\theta}z$ 视为同一共同相位类。
考察全域多项式 $P(z,\bar z)$，要求
$P(e^{i\theta}z,e^{-i\theta}\bar z)=P(z,\bar z)$。

#### 定理 7.2（最低二次关系层，V52）

<a id="thm:quadratic"></a>

上述不变量环由

$$
G_{ij}=z_i\bar z_j
$$

生成。每个非恒定不变量的总次数至少为二。
实值齐次二次不变量恰是

$$
q_E(z)=z^\dagger Ez,\qquad E=E^\dagger;
$$

它处处非负当且仅当 $E\succeq0$。

**证明。**

单项式 $z^\alpha\bar z^\beta$ 在共同相位下乘上
$e^{i(|\alpha|-|\beta|)\theta}$。
不同相位权重的有限 Fourier 系数独立，所以不变多项式只含
$|\alpha|=|\beta|$ 的项。
每个此类单项式都可把一个 $z_i$ 与一个 $\bar z_j$ 配对，
写成 $G_{ij}$ 的乘积。非恒定项至少各有一个，故次数至少为二。
齐次二次式的一般系数矩阵，在实值条件下为 Hermitian；
处处非负恰是正半定的定义。

∎

这个结果已见项目 V52 §5 ［[2](#ref-v52)］。
它不适用于所有函数：局部比值 $z_j/z_k$ 是有理函数，
$\|z\|^p$ 对一般 $p$ 也不属于这里的多项式类别。
所以“最低二次层”必须连同复线性、共同相位和全域多项式条件一起陈述。

#### 命题 7.3（二次关系矩阵保留了什么）

$G=zz^\dagger$ 分离共同相位轨道，且满足

$$
\begin{gathered}G\succeq0,\quad\operatorname{rank} G\le1,\\G_{ij}G_{kl}=G_{il}G_{kj}.\end{gathered}
$$

在线性酉传导 $z'=Uz$ 下，

$$
G'=UGU^\dagger,\qquad q_E(z)=\operatorname{Tr}(EG).
$$

**证明。**

外积直接给出正性、秩与二阶子式关系。
若 $zz^\dagger=ww^\dagger\ne0$，两者像空间相同，故 $w=cz$；
比较外积得 $|c|=1$。零向量的情况单独成立。
后两式由矩阵乘法和迹循环性得到。

∎

**因此，平方不是关系退化成无关系；
它是共同相位被消去以后，仍能保留方向、相干和相对相位的最低多项式关系层。**
振幅上的二次读出，在关系矩阵上恰是线性的。
“更高次”也未必代表新的基本维度：这里每个更高次不变量都由二次生成元相乘形成。
这不意味着高次函数都线性于 $G$；例如 $|z_1|^4=G_{11}^2$ 仍是二次于 $G$ 的函数。

#### 命题 7.4（一个线性关系可由平方零残差锁定）

给定 $\zeta\in\mathbb{C}$，令

$$
L_\zeta=
\begin{pmatrix}|\zeta|^2&-\bar\zeta\\-\zeta&1\end{pmatrix}\succeq0.
$$

则对 $z=(\alpha,\beta)^T$，

$$
z^\dagger L_\zeta z=|\beta-\zeta\alpha|^2.
$$

若 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，则
$\operatorname{Tr}(\rho L_\zeta)=0$ 当且仅当

$$
\rho=\frac{(1,\zeta)^T(1,\bar\zeta)}{1+|\zeta|^2}.
$$

**证明。**

展开即得平方残差，$L_\zeta$ 是行向量 $(-\zeta,1)$ 的
伴随外积。由
$\operatorname{Tr}(\rho L_\zeta)=\|L_\zeta^{1/2}\rho^{1/2}\|_2^2$
知零残差等价于 $\rho$ 的支撑包含于
$\ker L_\zeta=\operatorname{span}\{(1,\zeta)^T\}$。
迹一给出唯一的秩一投影。未被该有限 $\zeta$ 图覆盖的
$\alpha=0$ 射线需使用另一坐标图。

∎

这正是“线性关系被精确锁定”的数学版本 ［[3](#ref-v55)］。
它需要一个具体约束及零残差条件；不能从一般退相干自动推出。

## 8. 递归概率如何唯一选出平方标定

上一节说明可观测关系为何最早出现在二次。
现在处理另一个问题：在既定正交振幅几何中，为何概率采用模平方而非任意函数？
以下是项目 V59 §6 的递归权重定理的自足形式 ［[5](#ref-v59)］。

#### 定义 8.1（同一递归响应与持久记录）

设归一化二元分解中每个分支的振幅模为 $r\in[0,1]$，
由同一个函数 $h:[0,1]\to[0,1]$ 赋予概率。要求：

1.  $h(0)=0$，$h(1)=1$，正交互补归一化满足

$$
h(r)+h(\sqrt{1-r^2})=1.
$$

2.  父分支振幅模为 $r$，其中一次条件细分的振幅模为 $s$，
则终端分支振幅模为 $rs$；终端权重只依赖此模，不依赖分解方式。

3.  同层不同分支的记录正交，父记录在后续细分中持久保留，
子事件包含于相应父事件。
正概率父事件遵守概率链律，并在条件细分中使用同一个 $h$。
零概率父事件的所有子事件联合概率为零。

以上条件量化所讨论的全部 $r,s$；若实际控制只支持其中一部分，
结论也只能先约束该可达部分。

#### 定理 8.2（递归一致性唯一给出平方）

<a id="thm:born"></a>

在上述条件下，不另加连续性假设也有

$$
\boxed{h(r)=r^2\quad(0\le r\le1).}
$$

**证明。**

若 $h(r)>0$，链律与终端模充分性给
$h(rs)=h(r)h(s)$。
若 $h(r)=0$，子事件包含于父事件而权重非负，
仍得 $h(rs)=0=h(r)h(s)$，没有对零概率事件定义条件概率。

令 $F(t)=h(\sqrt t)$，则

$$
\begin{gathered}F(ts)=F(t)F(s),\\F(t)+F(1-t)=1,\\F(0)=0,\quad F(1)=1.\end{gathered}
$$

若 $x,y\ge0$、$a=x+y\le1$ 且 $a>0$，有

$$
\begin{gathered}F(x)+F(y)\\=F(a)\left[F(x/a)+F(y/a)\right]\\=F(a).\end{gathered}
$$

$a=0$ 时也成立。所以 $F$ 在 $[0,1]$ 上非负且可加。
若 $x\le y$，$F(y)-F(x)=F(y-x)\ge0$，故 $F$ 单调。
把一分为 $n$ 等份得 $F(1/n)=1/n$，从而 $F(m/n)=m/n$。
任意实数 $t\in[0,1]$ 可用有理数从两侧夹逼，
单调性给 $F(t)=t$，于是 $h(r)=r^2$。

∎

这里确实把“递归”变成了平方概率的唯一性证明，
但输入已经包括二次正交几何 $\sqrt{1-r^2}$ 和线性路径幅度相乘。
它证明的是**既定振幅几何中唯一相容的概率标定**，
不是从无几何假设推出二次几何。
若父记录被相干擦除、不同分支重新干涉，
就不能继续把末端事件当作原父事件的经典子集使用该链律。

## 9. 更简洁的量子关系公理候选

### 9.1. 把唯一来源放在响应中

可以将可逆量子结构组织为以下三项。
“唯一”修饰实际本体的选择，不是说一个代数在数学上只有一个状态。

#### 定义 9.1（有限接口的正关系核心）

1.  **关系可组合。**
给定有限维复含单位 $C^*$ 代数 $\mathcal{A}$。
加法描述线性合成，乘法描述有序组合，伴随描述反向关系。

2.  **实际来源有一个相容的正响应。**
固定与唯一实际来源对应的一个线性泛函
$\omega:\mathcal{A}\to\mathbb{C}$，满足

$$
\omega(1)=1,\qquad \omega(a^\dagger a)\ge0\quad(a\in\mathcal{A}).
$$

将效果 $0\le E\le1$ 的 $\omega(E)$ 解释为响应概率，
是此核心的明确物理输入。

3.  **控制与记录有声明的实现。**
允许的可逆门是指定的 $u\in\mathcal{A}$，满足 $u^\dagger u=uu^\dagger=1$；
固定读口、复合接口、仪器及其记录协议明确给出。
它们属于同一完整描述，不能由“存在一种表示”自动推成实际可实现。

$C^*$ 表示范数满足 $\|a^\dagger a\|=\|a\|^2$，
并有相应的正锥与平方根；这个结构本身承担了相当多的数学内容。
以下是标准 GNS 构造的有限维版本 ［[11](#ref-gns)］。

#### 定理 9.2（从正关系重建源向量与酉历史）

<aside data-v70-note="gns-convention">

> **整理者核读注（GNS 来源的内积约定与前提；非作者原文）。** 所引 MIT §4 用第一变量线性的 $\langle a,b\rangle=\phi(b^*a)$，本文用第二变量线性的 $\langle a,b\rangle_\omega=\omega(a^\dagger b)$，两者互换变量，响应公式相应互换两槽；并无符号矛盾。这里复含单位有限维 $C^*$ 代数与归一正泛函是前提。正性经极化给 Hermitian 性；完成平方的非零范数情形给 Cauchy–Schwarz，零范数情形由任意复标量的正性直接迫使交叉项为零。零空间的左理想性质用正文所列 $C^*$ 正锥不等式，不能把它当成双边理想或自动忠实表示。

</aside>

<a id="thm:gns"></a>

对上述 $(\mathcal{A},\omega)$，存在 Hilbert 空间 $\mathcal{H}_\omega$、
$*$-表示 $\pi$ 与单位循环向量 $\Omega$，满足

$$
\omega(a)=\langle\Omega,\pi(a)\Omega\rangle.
$$

循环三元组在保持 $\mathcal{A}$ 作用与源向量的意义下，酉等价唯一。
每个声明门 $u$ 表示成酉算符 $\pi(u)$。
对历史 $u_h=u_m\cdots u_1$ 和效果 $E$，

<a id="eq:gns-born"></a>

$$
\boxed{\begin{gathered}p_h(E)=\omega(u_h^\dagger Eu_h)\\=\|\pi(E^{1/2})\pi(u_h)\Omega\|^2.\end{gathered}}
$$

（7）

**证明。**

在 $\mathcal{A}$ 上定义半内积
$\langle a,b\rangle_\omega=\omega(a^\dagger b)$。
正性首先给 Hermitian 性，并由
$\omega((a+\lambda b)^\dagger(a+\lambda b))\ge0$
对复 $\lambda$ 完成平方，得 Cauchy–Schwarz 不等式。
故

$$
\mathcal N=\{a:\omega(a^\dagger a)=0\}
$$

是半内积的零空间及线性子空间。
$c^\dagger c\le\|c\|^2 1$ 蕴含
$a^\dagger c^\dagger ca\le\|c\|^2a^\dagger a$，
所以 $a\in\mathcal N$ 时 $ca\in\mathcal N$。
因此 $\mathcal N$ 是左理想，
$\mathcal{H}_\omega=\mathcal{A}/\mathcal N$ 具有良好定义的内积；
有限维时它已经完备。

令 $\pi(c)[a]=[ca]$。左理想性质保证良定义，
上述不等式保证有界，内积恒等式保证
$\pi(c^\dagger)=\pi(c)^\dagger$。
取 $\Omega=[1]$，则范数为一，
$\pi(a)\Omega=[a]$ 给出循环性和响应公式。
若另有循环实现，映射
$[a]\mapsto\pi'(a)\Omega'$
由同一半内积保持范数，故延伸为所需酉等价。
门的酉性由 $*$-表示保持乘法直接得到。
最后将 $E=(E^{1/2})^\dagger E^{1/2}$ 代入响应公式，
即得 [（7）](#eq:gns-born)。

∎

当 $E=P$ 是投影时，平方根就是 $P$，从而得到通常的投影模平方。
这个证明从关系响应出发重建了向量语言，
并没有从“唯一来源”单独推出正性、复数性或概率解释。
表示中的 $\Omega$ 是一个向量，也不要求 $\omega$
在原代数全部状态的凸集中为纯状态；表示未必忠实。
同样，定理量化的各种效果并不等于实际单一历史已采得其全部统计值。
循环性只给代数作用所张成的表示空间，不保证其中每个向量都能由
实际允许的一条酉历史制备。

### 9.2. 测量更新与关系递归

<aside data-v70-note="instrument-sums">

> **整理者核读注（记录容量与 Kraus 求和；非作者原文）。** 本节 $M_{r\alpha}\in\mathcal A$，效果与更新均在同一个已给有限维代数和同一响应中计算。有限指标族的求和直接适用；若使用可数族，须声明正效果和及相应 CP 更新的收敛（在此有限维可用范数收敛），再保证总和为单位。连续记录另需可测仪器与积分。有限接口并不自行给出无限记录容量，本文没有据这些有限公式构造无限相干历史极限。

</aside>

若一组内部仪器算符满足
$\sum_{r,\alpha}M_{r\alpha}^\dagger M_{r\alpha}=1$，
则记录概率及条件响应为

$$
\begin{gathered}p_r=\sum_\alpha\omega(M_{r\alpha}^\dagger M_{r\alpha}),\\\omega_r(a)=\frac{\sum_\alpha\omega(M_{r\alpha}^\dagger aM_{r\alpha})}{p_r}\\(p_r>0).\end{gathered}
$$

正性与归一化由公式立即保持。
但相同效果 $\sum_\alpha M_{r\alpha}^\dagger M_{r\alpha}$
可以对应不同的测后更新，所以只给概率并未给出整个仪器。

对任意两种关系 $a_1,a_2\in\mathcal{A}$，

$$
G_{ij}=\omega(a_i^\dagger a_j)
$$

正半定，因为
$c^\dagger Gc=\omega((\sum_i c_i a_i)^\dagger(\sum_j c_j a_j))\ge0$。
只要 $\operatorname{Tr} G>0$，它又可以归一化为一个二元 Bloch 球内的点。
这里 $a_i$ 也可以是“关系的关系”的任意有限多项式，
所以同一个代数与同一个正性条件已容纳递归。

这是一种**关系索引的三轴表示**，不自动是某个物理子系统的约化态，
也不声称两个关系的 Gram 矩阵保留了所有其他关系。
尤其两个归一化酉历史向量的 Gram 对角元都为一，
其归一化三轴必在 $r_z=0$ 的截面；完整球需要一般关系或不同分支权重。

### 9.3. 仍待解释的物理输入

| 已由条件推出  |  尚未因此推出 |
| --- | --- |
| 正响应的 Hilbert 表示  |  为什么物理选择复 $C^*$ 关系结构、实际响应 $\omega$ 的具体值。 |
| 内部门的酉表示  |  哪些数学酉实际可控制、有限资源和误差界。 |
| 正效果的平方读出  |  概率解释本身、实际记录选择及可重复统计条件。 |
| 二元关系的三轴坐标  |  物理空间三维、张量局域性、时钟和时空动力学。 |
| 所有有限代数关系协变  |  任意固定实验室关系都守恒，或所有局部信息均可无损压缩成三个数。 |

经典对易 $C^*$ 代数也满足正响应公理；
若要选择特有的量子结构，还须说明非对易关系与物理复合规则为何出现。
因此该核心是紧凑而可审查的重建起点，
尚不是已证明的最少、逻辑独立或唯一的量子起源公理系。

## 10. 与注意力机制的类比，以及测量稳定性的边界

### 10.1. 类比在“上下文关系读出”，不在算符完全相同

标准缩放点积注意力采用 ［[12](#ref-attention)］

$$
\begin{gathered}\operatorname{Attention}(Q,K,V)\\=\operatorname{softmax}(QK^T/\sqrt{d_k})V.\end{gathered}
$$

<aside data-v70-note="attention-domain">

> **整理者核读注（注意力矩阵的类型；非作者原文）。** 此公式取有限实矩阵 $Q\in\mathbb R^{n_q\times d_k}$、$K\in\mathbb R^{n_k\times d_k}$、$V\in\mathbb R^{n_k\times d_v}$，$d_k\ge1$，softmax 沿键的行内归一化。随后“酉当且仅当置换”的命题针对方阵 $n_q=n_k$；矩形权重本来就不是同空间酉门。严格正性要求有限实 logits、未掩码且键数大于一，不包括以负无穷实施的掩码。

</aside>

它与本轮结构的相似点在于使用同一规则，根据上下文关系给出新的读出，
再进入下一层。这个类比可以启发固定接口与递归路由的设计，
但没有证明普通注意力就是量子测量。

#### 命题 10.1（一般 softmax 注意力权重不是酉矩阵）

若一个实方阵 $T$ 元素非负、每行和为一，则它是酉矩阵
当且仅当它是置换矩阵。

**证明。**

若它酉，则每行平方和也为一，所以

$$
\begin{gathered}1=\left(\sum_jT_{ij}\right)^2\\=\sum_jT_{ij}^2+2\sum_{j<k}T_{ij}T_{ik}\\=1+2\sum_{j<k}T_{ij}T_{ik}.\end{gathered}
$$

非负性迫使每行仅有一个非零元素，且等于一；
行正交性要求各行的一位于不同列。反向显然。

∎

有限、未掩码、长度大于一的 softmax 权重严格为正，
因而不属于该酉特例。
实际注意力权重还随输入变化，不能因为含有内积和归一化就直接等同于酉门。

### 10.2. 退相干不等于关系普遍降秩

以内部记录模型

$$
\alpha|0\rangle|e_0\rangle+\beta|1\rangle|e_1\rangle
$$

为例，忽略记录后的系统态为

$$
\rho_S=
\begin{pmatrix}
|\alpha|^2&\alpha\bar\beta\langle e_1,e_0\rangle\\
\bar\alpha\beta\langle e_0,e_1\rangle&|\beta|^2
\end{pmatrix}.
$$

<aside data-v70-note="records">

> **整理者核读注（记录模型的归一与条件化；非作者原文）。** 所示记录向量 $e_0,e_1$ 取单位向量，$|\alpha|^2+|\beta|^2=1$，系统基 $|0\rangle,|1\rangle$ 正交；偏迹遂给所列交叉项。比较记录平行的相干纯态与记录正交且两分支非零的情形，约化秩可从一增至二；该比较不声称每次退相干都严格增秩。按记录选枝还须采用已声明的、能区分该记录的仪器，并在正概率结果上条件化。

</aside>

当记录正交时，非对角项消失；
若两个分支都非零，约化态从可能的秩一变成秩二，而不是降秩。
若再给定一个实际记录并条件化，系统才变成相应的条件态。
固定关系、稳定记录、忽略环境和条件选枝是不同步骤。
本轮 Gram 矩阵的秩一结论描述的是*涨落关系的线性依赖*，
不能拿来替代一般退相干机制。

## 11. 可以保留下来的最简结论

本轮证明链可以压缩为

$$
\begin{gathered}\text{复线性关系}+\text{共同相位等价}\\\ \Longrightarrow\ \text{最低二次多项式关系 }zz^\dagger,\\\text{复 }C^*\text{ 关系代数}+\text{归一正线性响应}\\\ \Longrightarrow\ \text{Hilbert 表示与平方读出},\\\text{固定 AURIC 编码}+\text{完整联合概率}\\\ \Longrightarrow\ \text{固定读口的递归信息完备}.\end{gathered}
$$

不确定性在这条链中的位置也很清楚：

$$
\boxed{\begin{gathered}\text{中心化关系正性}\\\ \Longrightarrow\ \det G\ge0,\\\det G=0\ \Longleftrightarrow\\\text{中心化向量线性相关}.\end{gathered}}
$$

最后一个等价包含零向量的退化情况；
用某一向量预测另一向量的带除法公式，则仍需对应方差非零。

因此，最值得继续保留的表述是：
**同一个本体的可组合关系，在内生读口上表现为概率；
二次结构是共同相位消去后的最低多项式关系层；
递归的一致性由同一个正关系结构维护。**
下一步真正未闭合的任务，是从更弱、可操作的条件选择这个复正关系结构，
并说明实际控制、物理复合及空间为何具有我们观察到的形式。

## 附录 A. 为什么完整五概率仍不能充当自主经典门状态

这段补充 V37 §12 的一个容易混淆的边界 ［[1](#ref-v37)］。

#### 定理 A.1（五标签随机更新的限制）

设一个固定的非负列随机矩阵 $T$ 对所有逻辑 qubit 态都满足

$$
Tp(\rho)=p(U\rho U^\dagger).
$$

则 $U=e^{i\gamma}I$。反向存在平凡实现 $T=I$。

**证明。**

对所有 $\rho$ 的等式等价于

$$
U^\dagger E_sU=\sum_tT_{st}E_t.
$$

右边若为非零秩一正算符，所有正权加项都必须具有同一支撑：
对目标支撑的正交补取期望，各非负项只能同时为零。
所以酉共轭必须置换效果的四条不同支撑射线。
每列和为一又要求各射线上的效果总迹在置换下相同。

四条射线的 Bloch 方向及总迹为

$$
\begin{array}{c|c}
(-1,-1,-1)/\sqrt3&4\nu\sqrt3\\
(3,1,1)/\sqrt{11}&\nu\sqrt{11}\\
(0,0,1)&2\nu\\
(1,3,1)/\sqrt{11}&\nu\sqrt{11}.
\end{array}
$$

第一条和第三条具有不同于其他射线的总迹，故各自固定。
qubit 酉的 Bloch 作用是正交且定向保持的旋转；
固定两个不共线方向只能是恒等旋转。
于是 $U$ 与所有 Pauli 矩阵对易，只能是标量相位。

∎

这不否定码上概率坐标的信息完备性：
$p$ 的反演确实定义了码像上的唯一仿射更新
$F_U=p\circ\operatorname{Ad}_U\circ p^{-1}$。
定理排除的是把该更新延拓成一个对所有五标签分布均有效的固定经典随机门。
因此，递归保存完整概率律与让单个已采样标签自主演化，具有不同的数学要求。

## 固定来源与文献

<a id="ref-v37"></a>

[1] 
The Omega Institute，
[AURIC V37：二元关系、酉表示与黄金门普适性](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)，
固定提交，§§3–4、12。五模式码、迹距离标尺及经典随机提升限制。

<a id="ref-v52"></a>

[2] 
The Omega Institute，
[AURIC V52：纯态商几何、二次关系生成元与无损递归](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)，
固定提交，§5。共同相位不变量的二次生成定理。

<a id="ref-v55"></a>

[3] 
The Omega Institute，
[AURIC V55：二元关系外部闭合、三轴误差与条件量子起源](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md)，
固定提交，§§2、4、6。

<a id="ref-v56"></a>

[4] 
The Omega Institute，
[AURIC V56：内部二元切分、算子三轴纯度与内生递归](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md)，
固定提交，§§5、9。

<a id="ref-v59"></a>

[5] 
The Omega Institute，
[AURIC V59：局部层析、相干读口轨道与量子正性起源](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md)，
固定提交，§§3、6–7。递归概率标定、关系一致响应及原生读口。

<a id="ref-v22"></a>

[6] 
The Omega Institute，
[AURIC V22：相对门历史、观察商与递归闭合](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)，
固定提交，§8。

<a id="ref-instrument"></a>

[7] 
The Omega Institute，
[AURIC 原生原子的输出分辨仪器闭包](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)，
固定提交，标签字典、§§13、15。

<a id="ref-control"></a>

[8] 
The Omega Institute，
[递归关系观察的原始控制与仪器稳定性](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md)，
固定提交，§§1、5。

<a id="ref-watrous"></a>

[9] 
John Watrous，
[The Theory of Quantum Information，第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，
Theorem 2.42、Corollary 2.43、Proposition 2.44；
投影扩张与信息完备测量。

<a id="ref-schrodinger"></a>

[10] 
Erwin Schrödinger，
[About Heisenberg Uncertainty Relation](https://arxiv.org/pdf/quant-ph/9903100)，
1930 年原文的英译，A. Angelow 与 M.-C. Batoni，式 (9)；
arXiv:quant-ph/9903100。

<a id="ref-gns"></a>

[11] 
Kobi Kremnizer，
[MIT 18.238, Lecture 3: Gelfand–Naimark–Segal Construction](https://math.mit.edu/classes/18.238/lec100208.pdf)，
2008，§4、Theorem 4.1。

<a id="ref-attention"></a>

[12] 
Ashish Vaswani 等，
[Attention Is All You Need](https://arxiv.org/pdf/1706.03762)，
2017，§3.2.1、式 (1)；arXiv:1706.03762。

<details>
<summary>原稿结束标记（作者原文）</summary>
<textarea readonly cols="24" rows="1" aria-label="作者原始结束标记">\end{document}</textarea>
</details>
> **来源与转换归属。** 本文为用户提供的 AI AURIC continuation 原稿的 Markdown 转换，来源会话 `01a15590-6264-7c80-8c48-21290deed496`（2026-11-01）。原文是参考输入，不是 Lean 数学真值。下文“本轮”“重新核对”“读取”“未重试”及无数学程序等历史报告均属原作者的文献性陈述；不作为 Markdown 转换者的现场行为报告。Markdown 转换者的必要补注另行标明归属。原稿的生产配置保留如下；它们描述 XeLaTeX 生产，并不声称此 Markdown 以 XeLaTeX 排版。

<details style="max-width:100%;overflow-x:auto">
<summary>原稿前言与完整生产配置（原顺序、原字节）</summary>

```tex
% !TeX program = xelatex
% Compile twice. Optional: \def\AURICFontPath{/absolute/path/to/fonts/}
% All mathematical arguments are paper proofs; no mathematical programs were used.
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
\definecolor{auricred}{RGB}{155,48,48}
\usepackage[unicode,colorlinks=true,linkcolor=auricblue,urlcolor=auricblue,citecolor=auricblue]{hyperref}
\hypersetup{pdftitle={AURIC v78：门流形与可积关系},
pdfauthor={AURIC research continuation},
pdfsubject={Tangent binary kernels, phase transport, integrability and recursive error}}
\newcommand{\R}{\mathbb R}
\newcommand{\C}{\mathbb C}
\newcommand{\HH}{\mathcal H}
\newcommand{\CP}{\mathbb{CP}}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\Ran}{\operatorname{Ran}}
\newcommand{\Var}{\operatorname{Var}}
\newcommand{\id}{\operatorname{id}}
\newcommand{\ket}[1]{|#1\rangle}
\newcommand{\bra}[1]{\langle#1|}
\newcommand{\plain}[1]{\par\smallskip\noindent\textbf{\color{auricblue}白话图景。}#1\par\smallskip}
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
\fancyhead[L]{\small AURIC：门流形与可积关系}
\fancyhead[R]{\small v78 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
```

</details>

<details style="max-width:100%;overflow-x:auto">
<summary>原稿封面生产设置</summary>

```tex
\begin{center}
{\LARGE\bfseries\color{auricblue} 门流形与可积关系}\\[8pt]
{\large 二元三维核、曲率与误差递归}\\[7pt]
定义、定理与纸面证明\quad v78.0\\[4pt]
2026 年 11 月 1 日\quad Asia/Singapore
\end{center}
```

</details>

# 门流形与可积关系

## 二元三维核、曲率与误差递归

定义、定理与纸面证明　v78.0

2026 年 11 月 1 日　Asia/Singapore

## 摘要

把离散门历史提升为连续描述，需要区分门的流形、流形上的路径，以及路径产生的状态或射线。
本文从同一 $\Omega$ 的相邻历史比较出发，以三态 Gram 矩阵的 Schur 余量取得量子几何张量；
将两个切向变化归一成三轴标签，得到
$1-|\mathbf r|^2=4(\det g-F_{12}^2/4)/s^2$。
球面等号表示复线性依赖，并不表示实流形分岔。
项目的五模式相位运输提供一个精确例子：两类原生控制的有序积分生成第三方向，
但该方向具有二阶成本，三维当前态流形没有因此成为三维各向同性空间。
完整酉框架的分块 Maurer–Cartan 方程把度量、相位曲率和补空间关系约束在一起，
并在局部给出反向重建。一般路径运输可以有合法 holonomy；仅在“终点决定全门”的要求下，平坦性才是必要条件。
进一步证明积分递归的酉余项界、闭路比较的四次阶暗口读数、整体保距与局部误差收缩的区别，
以及光滑整体中新记录概率的短时二次律。
最后由完整正核与保核的可逆重标重构连续酉历史，说明哪些公理可改写为内部关系相容，
哪些关于复数、正性、实际控制、时钟与记录的前件仍须明确。

## 1. 本轮推进的对象与项目依据

本轮把用户的直觉组织成三个可分别证明的命题：
连续变化使二元关系具有切向几何；变化的先后次序可留下第三个量；
递归积分可以逼近一个流，但误差趋零需要另有收敛条件。
这三件事相互连接，却不由“都是同一 $\Omega$”自动等同。

全文固定唯一归一来源 $\Omega$。讨论不同数学候选，是比较同一个实际关系系统的可能描述，
不引入多个本体。参考、记录和时钟均可属于这一整体。
证明先在有限维复 Hilbert 接口 $\mathcal H=\mathbb C^d$ 内进行；这不把整个宇宙断言为有限维。
内积对第二槽线性，取 $\hbar=1$；恢复单位时 $H=i\hbar\dot U U^\dagger$。

本轮唯一远端 HEAD 请求于新加坡时间 2026-11-01 22:19:18，
在取得 HTTP 响应前因网络权限失败，未重试。以下使用重新核对原始 Git blob 的固定提交

`5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b`。

不能把它称为本轮已经确认的最新 HEAD。v78 为本对话稿件编号。

<details style="max-width:100%;overflow-x:auto">
<summary>原稿表格生产设置与正文</summary>

```tex
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.22\textwidth}X@{}}
\toprule
项目来源 & 本轮直接使用的内容与范围\\
\midrule
Phase §§2、8--10.4 & 正五模式纤维、相位运输、当前态流形、路径接续、双墙控制场及二阶主符号。\\
V22 §§1、6--7 & 历史复正核、共同续接、相干比较与永久记录的区别。\\
V52 §§2--3、7.2 & 射线商、两张复图、三维球与支持及相位的递归条件。\\
V37 §9；V57 §§2、5、8、10.1 & 相对酉误差、稳定读口、记录资源、内部钟与归一化误差。\\
V58 §§2--3、10、14；$\Omega$ §§5、7、12 & 条件重构、有限矩阵接口、静态相容和剩余前件。\\
Clock V31 §§8--11 & 时钟、细分误差及物理几何需要额外接口。\\
\bottomrule
\end{tabularx}
```

</details>

<div role="region" tabindex="0" aria-label="原稿表格" style="overflow-x:auto">

| 项目来源 | 本轮直接使用的内容与范围 |
| --- | --- |
| Phase §§2、8–10.4 | 正五模式纤维、相位运输、当前态流形、路径接续、双墙控制场及二阶主符号。 |
| V22 §§1、6–7 | 历史复正核、共同续接、相干比较与永久记录的区别。 |
| V52 §§2–3、7.2 | 射线商、两张复图、三维球与支持及相位的递归条件。 |
| V37 §9；V57 §§2、5、8、10.1 | 相对酉误差、稳定读口、记录资源、内部钟与归一化误差。 |
| V58 §§2–3、10、14；$\Omega$ §§5、7、12 | 条件重构、有限矩阵接口、静态相容和剩余前件。 |
| Clock V31 §§8–11 | 时钟、细分误差及物理几何需要额外接口。 |

</div>

本稿不认证全部仓库及全部上游依赖。一般非完整几何的外部 ball-box 定理没有在本轮重读；
下文只对双墙模型给显式路径证明。数学全部采用纸面推导及纸面复核，
没有数学程序、数值求值、CAS、仿真、枚举或机器证明。
文献中的标准几何结果与本稿把它们接入二元比较的组织方式分别标注。

## 2. 门的流形、历史路径与状态射线

#### 定义 2.1（连续同源历史）

门的参数族为 $U:M\to U(d)$；历史为参数路径 $\gamma:I\to M$，
其状态为 $\psi(t)=U(\gamma(t))\Omega$。
另一个更一般的描述先给沿路径的运输规则，再由整条路径定义 $U_\gamma$；
此时相同参数终点未必决定相同门。

流形是可能门或控制参数的空间，流是其上的运动规律，路径是一次具体历史。
三者具有不同的信息量。有限门序列可作为某条路径的采样，
但不会唯一选定采样之间的路径、速度或能量。

#### 定理 2.2（完整门投影本身没有分岔）

<a id="thm:quotient"></a>

固定 $\|\Omega\|=1$，映射

$$

U(d)\longrightarrow S^{2d-1},\quad U\longmapsto U\Omega,
\qquad
U(d)\longrightarrow\mathbb{CP}^{d-1},\quad U\longmapsto[U\Omega]

$$

均为光滑满秩投影。其纤维分别为 $U(d-1)$ 及 $U(1)\times U(d-1)$；
三个空间的实维数依次为 $d^2,\,2d-1,\,2d-2$。

**证明。**

任一单位向量均可补成正交基，故可由酉矩阵送达。
固定向量的酉矩阵在正交补上自由作用；固定射线还允许该向量的共同相位，得到所列纤维。
在 $\psi=U\Omega$ 处，单位球切向量可写为 $\delta\psi=ia\psi+u$，其中 $a\in\mathbb R,u\perp\psi$。
反 Hermitian 矩阵

$$

B=ia|\psi\rangle\langle\psi|+|u\rangle\langle\psi|-|\psi\rangle\langle u|

$$

满足 $B\psi=\delta\psi$，故每个球面切向量都能提升。
再商去 $i\psi$ 的相位方向即得射线投影满秩。维数由纤维维数相减得到。

**证毕。**

在 qubit 情形，$U(2)$ 是四维，$SU(2)$ 和单位向量球 $S^3$ 是三维，射线球 $S^2$ 是二维。
它们不能仅因彼此关联就当成同一对象。
实际可用控制若只占其中一个子集，限制后的映射则可能失去满秩。

#### 命题 2.3（离散样本不锁定连续历史）

任意有限有序酉端点可由许多 $C^\infty$ 酉路径插值。
但无限端点若在有限时刻聚集，未必容许连续延拓。

**证明。**

相邻端点取 Hermitian 对数 $U_{j+1}U_j^\dagger=e^{-iA_j}$，
以端点所有阶导数为零的光滑递增函数 $\chi$ 插值得
$e^{-i\chi A_j}U_j$，各段光滑拼接。
对数支、$\chi$ 和插入闭路皆不唯一。
若 $t_n\to T$，而状态在两正交向量间交替，则没有同一极限，故不存在连续延拓。

**证毕。**

例如 $U(t)=e^{-i|t|\sigma_z}$ 连续且每点酉，却在零点不可微。
“每个门酉”不独自推出光滑性。
单条状态历史也不足以决定整个门：$\Omega=|0\rangle$ 时，
$I$ 与 $\operatorname{diag}(1,e^{i\theta(t)})$ 给同一状态而在补空间作用不同。

**白话图景。** 门流形像所有可行变化的地图，门历史像地图上的一条路。
知道起点、终点，甚至知道一路上某一个读出的样子，仍可能不知道整扇门对其他内部关系做了什么。
“同一点对应许多门”常常是投影留下的自由，并不是道路在这里突然断开。

## 3. 相邻历史的三维比较，如何变成微分几何

### 3.1 从有限比较到局部长度

对同源的两个归一向量 $a,b$，保留内部相干标签

$$

|\Phi\rangle=\frac{|0\rangle a+|1\rangle b}{\sqrt2},\qquad c=\langle a,b\rangle .

$$

标签态及其三轴为

$$

\rho_{\rm lab}=\frac12
\begin{pmatrix}1&\overline c\\c&1\end{pmatrix},
\qquad \mathbf r_{\rm lab}=(\Re c,\Im c,0).

$$

在 $|-\rangle=(|0\rangle-|1\rangle)/\sqrt2$ 读口，

<a id="eq:binary"></a>

$$
p_-=\frac{1-\Re c}{2}=\frac{\|a-b\|^2}{4}.
$$

方程 (1)。

这是前稿 v77 的有限二元比较恒等式；本轮研究其连续极限。

令 $\psi(\lambda)$ 为 $C^2$ 归一族，$P=|\psi\rangle\langle\psi|$，定义

$$

D_\mu\psi=(I-P)\partial_\mu\psi,\quad
\mathcal Q_{\mu\nu}=\langle D_\mu\psi,D_\nu\psi\rangle,\quad
g_{\mu\nu}=\Re\mathcal Q_{\mu\nu}.

$$

本稿使用未额外倍乘的 Fubini–Study 度量 $ds^2=g_{\mu\nu}d\lambda^\mu d\lambda^\nu$。
Phase 原文的度量为本稿的两倍，不能混用其常数。

#### 定理 3.1（邻近比较的微分极限）

<a id="thm:metric"></a>

令 $c_\delta=\langle\psi(\lambda),\psi(\lambda+\delta)\rangle$。则

$$

1-|c_\delta|^2
=\|(I-P)\psi(\lambda+\delta)\|^2
=g_{\mu\nu}\delta^\mu\delta^\nu+o(|\delta|^2).

$$

若先对齐共同相位，再作二元比较，则

$$

p_-^{\rm align}=\frac{1-|c_\delta|}{2}
=\frac14g_{\mu\nu}\delta^\mu\delta^\nu+o(|\delta|^2).

$$

**证明。**

第一式由正交分解精确成立。Taylor 展开给
$(I-P)\psi(\lambda+\delta)=D_\mu\psi\,\delta^\mu+o(|\delta|)$。
平方范数后，反对称虚部不贡献实二次型。
最后使用 $1-|c|=(1-|c|^2)/(1+|c|)$ 且 $|c_\delta|\to1$。

**证毕。**

原始相位保持的时间比较则为

$$

p_-(h)=\tfrac14h^2\|\dot\psi\|^2+o(h^2)
=\tfrac14h^2\bigl(g_{tt}+\mathcal A_t^2\bigr)+o(h^2),
\quad \mathcal A=-i\langle\psi,d\psi\rangle .

$$

在 $i\dot\psi=H\psi$ 下，
$g_{tt}=\operatorname{Var}_\psi(H)$、$\mathcal A_t=-\langle H\rangle$。
因此相位对齐与保留相干参考，是两个不同接口。
能量不确定度与射线长度的关联是标准结果 [[9](#ref-aa)]，这里给出与有限标签读口的直接连接。

### 3.2 三个近邻历史的 Schur 余量

#### 定理 3.2（二元切向核的三维约束）

<a id="thm:qgt"></a>

在两个实参数方向取 $u=D_1\psi,v=D_2\psi$，且
$s=\|u\|^2+\|v\|^2>0$。本定理及下一命题的 $g,\mathcal Q$ 均指所选两方向的 $2\times2$ 限制。
令 $F=d\mathcal A$，则 $F_{12}=2\Im\langle u,v\rangle$。
把 $u,v$ 当作二元比较的两个分支，其标签三轴为

$$

x=\frac{2g_{12}}s,\qquad y=\frac{F_{12}}s,\qquad
z=\frac{g_{11}-g_{22}}s .

$$

它们满足精确恒等式

<a id="eq:metriccurv"></a>

$$
\boxed{
1-x^2-y^2-z^2
=\frac4{s^2}\left(\det g-\frac{F_{12}^2}{4}\right)\ge0 .
}
$$

方程 (2)。

这个切向核是三个近邻历史完整 Gram 矩阵的 Schur 余量极限。

**证明。**

取 $\psi_0=\psi(\lambda)$、$\psi_i=\psi(\lambda+he_i)$。
消去归一根节点后，Schur 余量为

$$

R_{ij}(h)=\langle\psi_i,\psi_j\rangle
-\langle\psi_i,\psi_0\rangle\langle\psi_0,\psi_j\rangle
=\langle(I-P)\psi_i,(I-P)\psi_j\rangle .

$$

故 $R(h)\succeq0$ 且 $h^{-2}R(h)\to\mathcal Q$。
又因

$$

d\mathcal A=-i\,d\psi^\dagger\wedge d\psi,\qquad
F_{12}=2\Im\mathcal Q_{12},

$$

有
$\det\mathcal Q=g_{11}g_{22}-g_{12}^2-F_{12}^2/4\ge0$。
二元标签的密度矩阵是 $\mathcal Q$ 的转置除以 $s$，
行列式为 $(1-|\mathbf r|^2)/4$，即得结果。

**证毕。**

不等式 $\det g\ge F_{12}^2/4$ 属于已知量子几何约束 [[10](#ref-roy)]。
本稿的推进是把它作为三历史 Schur 余量与 AURIC 二元三轴的同一恒等式，
并用于区分复秩与实分岔。具体三轴依赖所选两方向及其尺度；张量约束不依赖这种记号选择。

> **Markdown 转换者来源注（不属原稿）。** Roy v1 第 2 页式 (1) 定义曲率，第 3 页定义量子度量，并在式 (9)–(12) 给出所引约束。式 (11) 写出的可逆各向同性化直接适用于正定度量；本文正半定及秩退化边界由上方 Schur 余量和 Gram 行列式证明承担，不以该坐标变换作为前件。

#### 命题 3.3（球面等号不等于分岔）

<a id="prop:notbranch"></a>

在式 [(2)](#eq:metriccurv) 中，$|\mathbf r|=1$ 表示 $u,v$ 复线性依赖；
两个实参数的射线映射微分降秩，则要求 $\det g=0$。两者不同。

**证明。**

Gram 行列式为零等价复线性依赖。
实微分的 Gram 矩阵是 $g$，故实秩下降等价其行列式为零。
具体取

$$

\psi(\xi,\eta)=\frac{(1,\xi+i\eta)^{\mathsf T}}
{\sqrt{1+\xi^2+\eta^2}} .

$$

在原点有 $u=|1\rangle,v=i|1\rangle$，于是
$g=I_2,F_{12}=2,s=2,\mathbf r=(0,1,0)$。
两个实方向独立，映射光滑满秩，却恰落在标签球面。

**证毕。**

反向看，若候选 $g=I_2,F_{12}=3$，则 $y=3/2$，落到球外，
没有任何正 Hilbert 切向核能实现它。
而 $s=0$ 只表示两方向在该点均未改变射线，此时不可继续除以 $s$。

**白话图景。** 两种变化可能只是同一个复方向的“实向”和“虚向”，所以二元核已经纯了，
但观察者仍能沿两个独立的实方向移动。球面上的纯，不等于道路合并成一条，
更不等于系统发生了塌缩。真正被锁在一起的是局部长度、夹角和有向相位面积。

## 4. 项目中的精确实例：先后次序生成第三方向

### 4.1 五模式正纤维与连续相位运输

Phase 原文 [[1](#ref-phase)] 按 $(0,1,2,3,13)$ 排列五模式。固定
$r=1-Z$、$0<Z<1$、$0<X,Y<r$，其正概率纤维为

$$

p_\kappa=(r-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\quad
\kappa\in J=(\max(0,X+Y-r),\min(X,Y)).

$$

$F[0]$ 是空占据基事件，不是零向量；归一化是五概率和为一的整体条件。
令 $d=(1,-1,0,-1,1)$、
$I=\sum_{s\ne2}p_s^{-1}$、$w_s=d_s/(p_sI)$，
相位运输为

$$

\psi_s=\sqrt{p_s}e^{-i\theta_s},\qquad
d\theta=w(\kappa)d\chi .

$$

这是项目明确声明的连续控制，不是由有限门字母表单独推出。

在双墙 $X=Y=r/2$，$J=(0,r/2)$，从固定准备相位 $\theta^0$ 出发，
相位增量 $h=\theta-\theta^0$ 满足
$h_0=h_{13}=u,h_1=h_3=v,h_2=0$，因而

$$

du=(\tfrac12-\kappa/r)d\chi,\qquad dv=-(\kappa/r)d\chi .

$$

两类原生控制场为

<a id="eq:sourcefields"></a>

$$
P=\partial_\kappa,\qquad
Q=(\tfrac12-\kappa/r)\partial_u-(\kappa/r)\partial_v .
$$

方程 (3)。

#### 定理 4.1（接续必须保留有序面积）

<a id="thm:heis"></a>

对紧区间上从零出发的绝对连续控制路径 $\gamma=(a,b)$（也可取分段 $C^1$），令

$$

A=a(T),\quad B=b(T),\quad K=\int a\,db .

$$

从 $(k,u,v)$ 出发，设全过程 $k+a(t)\in(0,r/2)$，则端点精确为

$$

T_\gamma(k,u,v)=
\left(k+A,\ u+\frac B2-\frac{kB+K}{r},\
v-\frac{kB+K}{r}\right).

$$

先执行 $\gamma$ 再执行 $\delta$ 的三元组满足

<a id="eq:chen"></a>

$$
\boxed{(A,B,K)\star(A',B',K')
=(A+A',B+B',K+K'+AB').}
$$

方程 (4)。

**证明。**

沿路 $\kappa=k+a,\ d\chi=db$，对式 [(3)](#eq:sourcefields) 积分即得端点。
后一段相对路径的绝对第一坐标为 $A+a'$，故
$\int(A+a')db'=AB'+K'$；其余两量直接相加。

**证毕。**

有序积分与路径接续的关系也是 Chen 结构及积分递归的标准主题 [[11](#ref-chen)]。
这里项目已给出特殊模型的直接证明，不需把所有路径先编码成无限门字。

<div role="region" aria-label="有序面积路径图" tabindex="0" style="overflow-x:auto">
<svg xmlns="http://www.w3.org/2000/svg" width="430" height="310" style="min-width:430px" viewBox="0 0 430 310" role="img" aria-labelledby="v78-diagram-title v78-diagram-description">
<title id="v78-diagram-title">同终点的两条有序控制路径</title>
<desc id="v78-diagram-description">横轴 a，纵轴 b。蓝色先 a 后 b，K=st；红色先 b 后 a，K=0；终点 (s,t)，矩形有向面积差 ΔK=st。原始点和比例见紧邻的 TikZ 原文。</desc>
<defs><marker id="v78-gray-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0 0L10 5L0 10Z" fill="gray"/></marker><marker id="v78-blue-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0 0L10 5L0 10Z" fill="rgb(24,53,79)"/></marker><marker id="v78-red-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0 0L10 5L0 10Z" fill="rgb(155,48,48)"/></marker></defs>
<g transform="translate(40 240) scale(65 -65)">
<path d="M-.3625 0H5.365" fill="none" stroke="gray" stroke-width=".012" marker-end="url(#v78-gray-arrow)"/>
<path d="M0 -.27V3.3075" fill="none" stroke="gray" stroke-width=".012" marker-end="url(#v78-gray-arrow)"/>
<path d="M0 0H3.915V2.3625H0Z" fill="rgb(241,243,244)"/>
<path d="M0 0H3.915" fill="none" stroke="rgb(24,53,79)" stroke-width=".0256" marker-end="url(#v78-blue-arrow)"/>
<path d="M3.915 0V2.3625" fill="none" stroke="rgb(24,53,79)" stroke-width=".0256" marker-end="url(#v78-blue-arrow)"/>
<path d="M0 0V2.3625" fill="none" stroke="rgb(155,48,48)" stroke-width=".0256" marker-end="url(#v78-red-arrow)"/>
<path d="M0 2.3625H3.915" fill="none" stroke="rgb(155,48,48)" stroke-width=".0256" marker-end="url(#v78-red-arrow)"/>
<circle cx="3.915" cy="2.3625" r=".0456901038"/>
</g>
<g font-family="system-ui, PingFang SC, sans-serif" font-size="16" fill="black">
<text x="398" y="245" font-style="italic">a</text><text x="35" y="14" font-style="italic">b</text>
<text x="300" y="78">(s,t)</text>
<text x="167.2375" y="266" text-anchor="middle">先 a 后 b：K=st</text>
<text x="167.2375" y="70" text-anchor="middle">先 b 后 a：K=0</text>
<text x="167.2375" y="165.4125" text-anchor="middle">ΔK=st</text>
</g></svg>
</div>

<details style="max-width:100%;overflow-x:auto">
<summary>原稿 TikZ 图源：比例、带符号点、路径及标签</summary>

```tex
\begin{tikzpicture}[x=1.45cm,y=1.35cm,>=Stealth]
\draw[->,gray] (-.25,0)--(3.7,0) node[right] {$a$};
\draw[->,gray] (0,-.2)--(0,2.45) node[above] {$b$};
\fill[auricblue!6] (0,0) rectangle (2.7,1.75);
\draw[very thick,auricblue,->] (0,0)--(2.7,0);
\draw[very thick,auricblue,->] (2.7,0)--(2.7,1.75);
\draw[very thick,auricred,->] (0,0)--(0,1.75);
\draw[very thick,auricred,->] (0,1.75)--(2.7,1.75);
\fill (2.7,1.75) circle(1.3pt);
\node[above right] at (2.7,1.75) {$(s,t)$};
\node[below] at (1.35,-.08) {\small 先 $a$ 后 $b$：$K=st$};
\node[above] at (1.35,1.82) {\small 先 $b$ 后 $a$：$K=0$};
\node at (1.35,.85) {$\Delta K=st$};
\end{tikzpicture}
```

</details>

上图两条路有相同 $A=s,B=t$，同样的允许起点区间，
却有不同 $K$，从而在内部参考下留下不同相位。
这表示二维端点漏掉了顺序信息。

完整合法域也必须保留。令 $m=\min a,M=\max a$，则

$$

D_\gamma=(-m,r/2-M).

$$

只记录 $(A,B,K)$ 不决定这个域：常值路径与
$b=0,\ a:0\to s\to0$（$0<s<r/2$）都给 $(0,0,0)$，
后一条却要求 $k+s<r/2$。历史的积分描述不能删除全过程约束。
相位模 $2\pi$ 后还需保留相位格；这里的实公式只在指定提升与图册中直接使用。

### 4.2 一个有限闭路的可见读数

Phase 命题 2.7 给出完全在正域内的闭路。
当 $X=Y=2/5,Z=1/5$，从 $\kappa_0=1/5$ 到 $\kappa_1=1/10$
再以相位宽度 $4\pi$ 完成矩形，输入、输出分别为

$$

\psi_{\rm in}=\frac{(1,1,1,1,1)}{\sqrt5},\qquad
\psi_{\rm out}=\frac{(-i,-i,1,-i,-i)}{\sqrt5}.

$$

约化端点相同；在另给二路相干标签及受控相对历史接口时，比较得到

$$

c=\frac{1-4i}{5},\quad
\mathbf r_{\rm lab}=(1/5,-4/5,0),\quad
p_-=\frac25,\quad
\|\psi_{\rm out}-\psi_{\rm in}\|^2=\frac85 .

$$

这是原生相位结果与式 [(1)](#eq:binary) 的直接合并。
原命题自身给出的固定参考读口为 $A_{02}$，其期待值由 $2/5$ 变为零；
上述标签比较不是由该单一读口自动供应。
比较核在球内，所有状态合法；残差揭示约化端点遗漏了历史，
不能把这个闭路称为归一化失败。

**白话图景。** 先横走再竖走，与先竖走再横走，可以到同一张平面地图的同一个点，
但内部相位已经不同。第三个量记住了两种变化怎样穿过彼此。
这个“关系的关系”是可观测的历史面积，不是分岔点，也不是多加一个本体。

## 5. 三维当前态不自动给出三维各向同性

#### 命题 5.1（双墙的局部标准形）

在式 [(3)](#eq:sourcefields) 的任意正内点 $(k_0,u_0,v_0)$，令

$$

\alpha=u-v,\quad\beta=u,\quad c_0=\tfrac12-k_0/r,
\qquad
x=\kappa-k_0,\ y=2(\alpha-\alpha_0),\
z=-r[(\beta-\beta_0)-c_0y].

$$

在足够小的单相位图内精确有

<a id="eq:contact"></a>

$$
P=\partial_x,\qquad Q=\partial_y+x\partial_z,\qquad
[P,Q]=\partial_z .
$$

方程 (5)。

**证明。**

分别对 $x,y,z$ 施以 $P,Q$：
$P(x,y,z)=(1,0,0)$，
$Qx=0,Qy=1,Qz=-r[(1/2-\kappa/r)-c_0]=x$。
再求交换子即得第三式。

**证毕。**

第三方向由原两方向的顺序生成，不是第三个可直接施加的控制。
本节 $(x,y,z)$ 是局部控制坐标，与标签球的三轴及五模式均值 $(X,Y,Z)$ 分别使用。
这里是状态源上的向量场和部分路径作用，不能据此认定存在有限维忠实 Heisenberg 酉矩阵群。
例如有限矩阵的交换子迹为零，不可能满足 $[B_1,B_2]=iI$。

#### 定理 5.2（二阶方向与小球体积）

<a id="thm:volume"></a>

额外指定控制长度

$$

L=\int\sqrt{\dot a^2+\dot b^2}\,dt .

$$

在固定正内点和单相位图附近，原生可达距离的小球具有坐标尺度
$(\varepsilon,\varepsilon,\varepsilon^2)$。
对任意光滑正密度，其体积在足够小时满足
$c\varepsilon^4\le\mu(B_\varepsilon)\le C\varepsilon^4$，
其中 $c,C>0$ 依赖所固定的局部图与成本。

**证明。**

从原点出发，水平曲线满足
$dx=da,dy=db,dz=x\,db$。
长度为 $L$ 时，$|x|,|y|\le L$ 且
$|z|\le\sup|x|\int|db|\le L^2$，故小球包含在所述尺度的盒中。

反过来，先沿 $x$ 再沿 $y$ 达到 $(x,y,xy)$，再作面积为 $z-xy$ 的平面矩形闭路。
边长取 $\sqrt{|z-xy|}$、方向按面积符号选择，附加长度为 $4\sqrt{|z-xy|}$，
且最终 $x,y$ 不变。因此

$$

d(0,(x,y,z))\le |x|+|y|+4\sqrt{|z-xy|}.

$$

在 $|x|,|y|\le c_0'\varepsilon,\ |z|\le(c_0')^2\varepsilon^2$ 的盒内，
选择充分小的固定 $c_0'>0$，右侧不超过 $\varepsilon$。
当 $\varepsilon$ 足够小，构造的全路径都留在原正域及单相位图。
同样，任何足够短的路径由上述坐标变化界不能先离图再绕相位返回。
两盒体积均为常数乘 $\varepsilon^4$，光滑正密度在闭小邻域内有上下正界，结论成立。

**证毕。**

这是三维流形上规定两控制后的体积尺度，不是四维流形，也没有推出物理四维时空。
项目一般墙型的更高增长结果不在此以同一证明推广。

#### 定理 5.3（第三可达方向不等于第三瞬时二阶方向）

<a id="thm:symbol"></a>

另给光滑正定 $2\times2$ 矩阵 $A=(a^{ij})$，考虑

$$

\mathcal G=\sum_{i,j=1}^2a^{ij}X_iX_j+\sum_i b^iX_i,
\quad X_1=P,\ X_2=Q .

$$

其主符号矩阵秩为二。光滑可逆坐标变换、漂移改变及正时钟倍率，
均不能把它变成三维各向同性 Laplace 算子。

**证明。**

令 $B$ 的两列为 $P,Q$ 的坐标向量，则主符号为 $BAB^{\mathsf T}$。
$B$ 满列秩、$A$ 正定，故秩恰为二。
非零余切向量 $dz-x\,dy$ 同时消去 $P,Q$。
可逆坐标变换给可逆合同变换，正时间倍率只乘正数，漂移不改变二阶部分，
所以均不改变该秩。

**证毕。**

加入 $[P,Q]^2$ 可以供应第三个主方向，正因为它改变了原二阶定律。
这里的成本与二阶算子均是明确附加的模型，未把噪声起源归给 $\Omega$。

**白话图景。** 两个按钮能靠先后配合把系统送到三维中的任意附近位置，
不等于已经有三个同等的按钮。第三个方向要绕一小圈才能产生，
所以它的成本和短时变化都不同。要得到各向同性，还需要能在内部关系中指认额外对称性或控制。

## 6. 完整关系框架的微分闭合与反向重建

### 6.1 度量、相位和补空间由同一个方程连接

在以 $\Omega$ 为首向量的固定正交参考基中，局部把 $C^2$ 状态族 $\psi$
作 $C^2$ 酉补全 $U=(\psi,E)$，其中 $E$ 的列张成 $\psi^\perp$。
定义

$$

\Theta=U^\dagger dU=
\begin{pmatrix}
i\mathcal A&-\beta^\dagger\\
\beta&C
\end{pmatrix},
\quad
\beta=E^\dagger d\psi,\quad C=E^\dagger dE,\quad C^\dagger=-C .

$$

$\beta$ 记录该状态向补空间的变化，$C$ 记录补空间自身怎样变化。
这正好把“关系本身也要有关系”写成可检验的矩阵式。

#### 定理 6.1（完整框架的闭合条件）

<a id="thm:mc"></a>

上述数据满足

<a id="eq:mc"></a>

$$
\boxed{\Theta^\dagger=-\Theta,\qquad d\Theta+\Theta\wedge\Theta=0,}
$$

方程 (6)。

其分块形式为

<a id="eq:block1"></a>

$$
\begin{aligned}
d\mathcal A&=-i\,\beta^\dagger\wedge\beta,&
\mathcal Q_{\mu\nu}&=\beta_\mu^\dagger\beta_\nu,
\end{aligned}
$$

方程 (7)。

<a id="eq:block2"></a>

$$
\begin{aligned}
d\beta+C\wedge\beta+\beta\wedge i\mathcal A&=0,&
dC+C\wedge C&=\beta\wedge\beta^\dagger.
\end{aligned}
$$

方程 (8)。

反之，在含原点的星形域上，$C^1$ 反 Hermitian 矩阵一形式 $\Theta$
若满足式 [(6)](#eq:mc)，则给定任意初始酉 $U_0$ 后，
存在唯一 $C^2$ 酉函数 $U$ 使 $dU=U\Theta,\ U(0)=U_0$。

**证明。**

由 $dU^\dagger=-U^\dagger dU\,U^\dagger$，
直接微分 $U^\dagger dU$ 得 Maurer–Cartan 式；
分块相乘给 [(7)](#eq:block1)–[(8)](#eq:block2)。
又 $D_\mu\psi=E\beta_\mu$，得 $\mathcal Q=\beta^\dagger\beta$。

反向证明不预设路径独立。沿径向定义

$$

\partial_tY(t,x)=Y(t,x)B(t,x),\quad
B(t,x)=x^j\Theta_j(tx),\quad Y(0,x)=U_0.

$$

连续反 Hermitian 系数的线性 ODE 给唯一酉解。
令 $E_i=\partial_iY-tY\Theta_i(tx)$，微分并用平坦性得到

$$

\partial_tE_i
=E_iB+tYx^j(\partial_i\Theta_j-\partial_j\Theta_i+
[\Theta_i,\Theta_j])(tx)=E_iB,\qquad E_i(0,x)=0.

$$

故 $E_i=0$。取 $U(x)=Y(1,x)$，即得 $\partial_iU=U\Theta_i$；
右侧 $C^1$，故 $U$ 为 $C^2$。
任意两解满足 $d(VU^\dagger)=0$，由初值相同知唯一。

**证毕。**

只给 $g,F$ 并不供应完整 $\beta,C$；只知道一个 $\Omega$ 的轨迹也不能消去补空间的自由。
上述反向重建明确要求完整关系框架。

### 6.2 平坦性究竟约束什么

式 [(6)](#eq:mc) 的平坦性属于已经给出的全门坐标函数 $U(x)$。
它不意味着射线的 Berry 曲率 $F=d\mathcal A$ 为零，
也不意味着状态度量的 Riemann 曲率为零。
例如

$$

\psi(\vartheta,\varphi)=
(\cos(\vartheta/2),e^{i\varphi}\sin(\vartheta/2))^{\mathsf T}

$$

给

$$

g=\tfrac14(d\vartheta^2+\sin^2\vartheta\,d\varphi^2),\qquad
\mathcal A=\tfrac{1-\cos\vartheta}{2}d\varphi,\qquad
F=\tfrac12\sin\vartheta\,d\vartheta\wedge d\varphi .

$$

它能局部补成酉矩阵，因此完整框架平坦与射线曲率非零可以同时成立。

若先给一般路径连接 $dU_\gamma=U_\gamma\Theta$，
则

$$

\mathcal K=d\Theta+\Theta\wedge\Theta

$$

可以非零。这表示路径次序不能从终点信息中删除，而不是酉演化不合法。
仅在额外要求“这一组终点坐标唯一决定整个门”时，$\mathcal K=0$ 才是必要条件。
非单连通域还须检查大闭路：
$\Theta=-i\alpha\sigma_z\,d\varphi$ 在穿孔平面处处平坦，
一圈运输却为 $e^{-2\pi i\alpha\sigma_z}$，未必恒等。

**白话图景。** 把状态、相位、补空间一起拿来比较，它们不能各走各的；
完整框架要求这些变化能拼成同一扇门。若只看一部分坐标，绕路留下相位仍然合法。
补回历史的作用，是说明留下了什么，而不是强行把一切曲率都消掉。

## 7. 把“不满足可积条件”送回二元三维读口

#### 定理 7.1（小环曲率的四次阶暗口见证）

<a id="thm:loop"></a>

设 $\Theta$ 为 $C^1$ 反 Hermitian 连接，在固定基点 $\lambda_0$ 以 $I$ 为初始运输，
沿 $+1,+2,-1,-2$ 的边长 $\epsilon$ 正向小矩形作右乘运输，结果为 $W_\epsilon$。
令
$\mathcal K_{12}=\partial_1\Theta_2-\partial_2\Theta_1+[\Theta_1,\Theta_2]$，
以下在 $\lambda_0$ 取值。
则

$$

W_\epsilon=I+\epsilon^2\mathcal K_{12}+o(\epsilon^2).

$$

对同源归一锚 $\xi$，以 $\xi,W_\epsilon\xi$ 作式 [(1)](#eq:binary) 的比较：

<a id="eq:loop"></a>

$$
\boxed{
p_-(\epsilon)=\frac{\epsilon^4}{4}\|\mathcal K_{12}\xi\|^2+o(\epsilon^4),
\quad
x=1-\frac{\epsilon^4}{2}\|\mathcal K_{12}\xi\|^2+o(\epsilon^4).
}
$$

方程 (9)。

**证明。**

各边积分保留二阶项，一阶项因闭路相消；
系数变化给 $\partial_1\Theta_2-\partial_2\Theta_1$，
有序乘积给交换子。于是得到第一式。
精确的 $4p_-=\|(W_\epsilon-I)\xi\|^2=2(1-x)$ 给后两式。

**证毕。**

相干虚轴还给
$y=\epsilon^2\Im\langle\xi,\mathcal K_{12}\xi\rangle+o(\epsilon^2)$。
这区分面积阶的相位变化与四次阶的暗口概率。

对一组张成 $\mathcal H$ 的同源锚，全部
$\lim_{\epsilon\to0}p_-/\epsilon^4=0$ 当且仅当 $\mathcal K_{12}=0$。
单个 $\Omega$ 可能处于其核内，故一个读数不能认证整扇门。
这些比较保留了受控相对相位；若先把共同相位商去，标量相位方向会失明。
若实际读取带绝对误差 $\eta(\epsilon)$，直接用
$p_-/\epsilon^4$ 取极限需要 $\eta=o(\epsilon^4)$；
环缩小并不自动提高认证精度。

**白话图景。** 反向检查公理现在有了一个具体画面：让两种变化交换先后次序，再比较回来后的结果。
如果声称“终点已经说完一切”，闭路残差就必须消失；
如果历史本来就是信息的一部分，残差就是它的读数。两种任务不能用同一个判错标准。

## 8. 递归何时是积分，积分何时控制误差

#### 定理 8.1（连续保酉与 Hermitian 生成元）

<a id="thm:h"></a>

设 $U(t)$ 为 $C^1$ 方阵曲线，且 $U(t_0)$ 酉。则下列条件等价：
每个 $U(t)$ 酉；$H=i\dot U U^\dagger$ 始终 Hermitian；
存在连续 Hermitian $H(t)$ 满足 $\dot U=-iHU$。
成立时生成元唯一。

**证明。**

微分 $UU^\dagger=I$ 得
$\dot U U^\dagger+U\dot U^\dagger=0$，故 $i\dot U U^\dagger$ Hermitian。
反向若这一矩阵 Hermitian，同一等式说明 $UU^\dagger$ 恒定，初值使其为 $I$。
给定 $\dot U=-iHU$ 则 $\frac d{dt}(U^\dagger U)=0$。
有限方阵因此酉，右乘 $U^\dagger$ 给生成元唯一。

**证毕。**

初始条件不可省：常值 $2I$ 给 $i\dot U U^\dagger=0$ 却非酉。
一条连续门路径也不必满足自治群律 $U(t+s)=U(t)U(s)$；
该群律另使生成元为常数。一般时变传播只有两时接续律。

#### 定理 8.2（积分递归及保酉余项界）

<a id="thm:dyson"></a>

设 $H$ 在 $[t_0,T]$ 连续 Hermitian，定义

$$

P_0(t)=I,\quad P_{n+1}(t)=I-i\int_{t_0}^tH(s)P_n(s)\,ds,\qquad
A(t)=\int_{t_0}^t\|H(s)\|\,ds .

$$

则 $P_n$ 一致收敛到唯一酉解 $U$，且

<a id="eq:dyson"></a>

$$
\boxed{\|U(t)-P_n(t)\|\le\frac{A(t)^{n+1}}{(n+1)!}.}
$$

方程 (10)。

> **Markdown 转换者校核注（不属原稿）。** 本节门、生成元、余项及 Duhamel 界中的矩阵范数取 Hilbert 范数诱导的算子范数，故酉矩阵的范数为 1。若使用 Hilbert–Schmidt 范数，不能照搬这一步。Dyson 和式的 `j=0` 项按空积 I 理解，末项的 `ds` 表示全部有序积分变量的乘积微分。

**证明。**

逐次代入给有序 Dyson 项

$$

P_n=\sum_{j=0}^n(-i)^j
\int_{t_0\le s_j\le\cdots\le s_1\le t}
H(s_1)\cdots H(s_j)\,ds_j\cdots ds_1 .

$$

第 $j$ 项范数至多 $A(t)^j/j!$，故在紧区间一致收敛。
极限满足积分式，连续 $H$ 给 $C^1$ 解；定理 [8.1](#thm:h) 给酉性。
两解之差反复代入齐次积分式，范数至多
$\sup\|D\|A(T)^n/n!$，极限为零，故唯一。

保留精确未展开的最后一个 $U(s_{n+1})$，余项为

$$

(-i)^{n+1}\!
\int_{t_0\le s_{n+1}\le\cdots\le s_1\le t}
H(s_1)\cdots H(s_{n+1})U(s_{n+1})\,ds .

$$

由于 $\|U(s)\|=1$，取范数即得 [(10)](#eq:dyson)，不需要额外 $e^{A(t)}$。

**证毕。**

有限 $P_n$ 一般不酉：
$P_1^\dagger P_1=I+t^2H^2$（常 $H,t_0=0$）。
实际误差也未必逐阶单调；$H=\sigma_z,t=2\pi$ 时，
$U=P_0=I$，而 $P_1-I=-2\pi i\sigma_z\ne0$。
“逼近序列收敛”与“每步物理状态都合法且更准确”是不同要求。

#### 命题 8.3（生成元误差的积分预算）

<a id="prop:duhamel"></a>

两连续 Hermitian 生成元 $H,K$ 从同一初始门 $I$ 出发，有

$$

\boxed{\|U_H(t)-U_K(t)\|\le\int_{t_0}^t\|H(s)-K(s)\|\,ds.}

$$

**证明。**

对 $U_H(t,s)U_K(s,t_0)$ 关于 $s$ 微分并积分，得到

$$

U_H(t)-U_K(t)
=-i\int_{t_0}^t U_H(t,s)(H-K)(s)U_K(s,t_0)\,ds .

$$

前后传播均酉，直接取范数。

**证毕。**

冻结每小段的 $H$ 并用指数乘积近似，可使每步精确保酉。
若网格宽度不超过 $h$，$H$ 的连续模为 $\omega_H(h)$，
则全段误差不超过 $(T-t_0)\omega_H(h)\to0$。
这是一种有条件的保酉积分近似；没有说任意递归都会缩小误差。
对一般控制路径，右乘连接与左作用生成元还须按
$H_{\rm lab}=iU_\gamma\Theta(\dot\gamma)U_\gamma^\dagger$ 转换。

**白话图景。** 递归可以是一层层把之前的结果代回积分方程，越来越完整地恢复同一条连续历史。
但迭代次数不是物理时间，近似公式也不是每一项都能直接当量子门。
控制误差的关键是有界的累计余量与明确的逼近规则，保酉只负责保存整体比较关系。

## 9. 误差怎样下降，整体关系又怎样保持

#### 定理 9.1（共同酉不能吸引所有候选态）

<a id="thm:nocontract"></a>

同一个酉 $U$ 保持

$$

\|U\psi-U\phi\|=\|\psi-\phi\|,\quad
\langle U\psi,U\phi\rangle=\langle\psi,\phi\rangle ,

$$

以及密度矩阵迹距离。因此不存在仅靠同一封闭酉流、把所有未知输入持续收向同一目标的机制。

**证明。**

前两式由 $U^\dagger U=I$，迹距离由酉共轭保持奇异值。
若两个不同输入同时收向同一目标，其距离趋零，与保距矛盾。

**证毕。**

这不排除指定状态到指定固定目标的距离在一段控制过程中减少；
它排除的是同一可逆流对全部未知态的共同吸引。

### 9.1 局部稳定可以把差异转到内部记录

取 $0<q<1$，在系统与记录两个 qubit 上定义

$$

V|00\rangle=|00\rangle,\qquad V|11\rangle=|11\rangle,

$$

$$

V|10\rangle=q|10\rangle+\sqrt{1-q^2}|01\rangle,\qquad
V|01\rangle=-\sqrt{1-q^2}|10\rangle+q|01\rangle .

$$

这是中间二维子空间的旋转，故整体酉。
记录以 $|0\rangle$ 准备时，局部系统的 Kraus 算符为
$K_0=\operatorname{diag}(1,q),K_1=\sqrt{1-q^2}|0\rangle\langle1|$。
局部激发概率乘 $q^2$，相干项乘 $q$。
每步供应新的内部 ready 记录位，$n$ 步后激发概率乘 $q^{2n}\to0$；
整体系统加全部相干记录仍保距。
新的记录位属于同一 $\Omega$，但它的独立准备条件不能被省去。
重复使用已相关的有限记录位，一般会产生回流或复现。

一般正保迹通道收缩迹距离：
由 $D(\rho,\sigma)=\max_{0\le E\le I}\operatorname{Tr} E(\rho-\sigma)$，
其对偶把效果送回效果，即有 $D(\Lambda\rho,\Lambda\sigma)\le D(\rho,\sigma)$。
完整内部参考还要求完全正性。
逐支归一的条件态不享有一般收缩定理，成功权重不能删除。

### 9.2 最优化需要指定余量与下降律

#### 定理 9.2（关系余量的归一梯度流）

<a id="thm:gradient"></a>

令 $A=\sum_j D_j^\dagger D_j\succeq0$，
$E(\psi)=\langle\psi,A\psi\rangle$，$\|\psi\|=1$。
对 $\tau\ge0$，归一流

$$

\dot\psi=-(A-E(\psi))\psi,\qquad
\psi(\tau)=\frac{e^{-\tau A}\psi_0}{\|e^{-\tau A}\psi_0\|}

$$

保持范数且满足

$$

\boxed{\dot E=-2\operatorname{Var}_\psi(A)\le0.}

$$

若 $p_0=\|P_{\ker A}\psi_0\|^2>0$，非零谱下界为 $\Delta>0$、上界为 $M$，
则

$$

E(\tau)\le M\frac{1-p_0}{p_0}e^{-2\Delta\tau}.

$$

**证明。**

直接微分范数和 $E$ 得
$\frac d{d\tau}\|\psi\|^2=-2(E-E)=0$、
$\dot E=-2\langle A^2\rangle+2E^2$。
归一指数式满足该微分式。
谱分解中归一分母至少 $p_0$，分子至多 $M(1-p_0)e^{-2\Delta\tau}$，给出界。

**证毕。**

$p_0>0$ 不可省：正本征态在该归一流下不动，误差可永久为正。
共同酉流 $\dot\psi=-iA\psi$ 则保持 $E$，并不执行上述下降律。
归一梯度流一般非线性；可把收缩 $e^{-\tau A}$ 作为仪器成功分支，
再补上 $(I-e^{-2\tau A})^{1/2}$、结果权重和失败记录，嵌入完整过程。
如此才保持与整体酉描述相容。

项目 V37 的可求和门误差给相对酉 $A_n^\dagger B_n$ 收敛，
不保证其极限等于 $I$；V57 的稳定读口也不要求全部永久记录态范数收敛 [[4](#ref-v37), [5](#ref-v57)]。
因此稳定、可逆与偏差为零仍须分别证明。

**白话图景。** 观察者可以越来越稳定，而整体没有丢信息：差异被送进了其他内部记录。
如果要主动把某项关系误差压小，还得说明优化的到底是什么、按什么规则压小，
以及代价和失败分支记录在哪里。把这些角色补齐，才是“全部在同一个 Ω 内”的完整表达。

## 10. 短时平方、内部钟与递归时间

#### 定理 10.1（新记录概率从二次阶开始）

<a id="thm:quadratic"></a>

设 $U(t)$ 为 $C^1$ 酉曲线，$U(0)=I$，
固定归一联合初态 $\Psi_0$ 与正交投影 $Q$，且 $Q\Psi_0=0$。
采用 Born 读口 $p_Q(t)=\|QU(t)\Psi_0\|^2$，则

$$

\boxed{p_Q(t)=t^2\|QH(0)\Psi_0\|^2+o(t^2),\qquad p_Q'(0)=0.}

$$

**证明。**

$C^1$ 给 $U(t)=I-itH(0)+o(t)$。
投影后常数项因 $Q\Psi_0=0$ 消失，取范数平方即可。

**证毕。**

若系数为零，可以从更高阶开始。这个结果使用了既有平方读口，
并没有从光滑性重新推导 Born 公理。
它却精确限制局部有效模型：严格
$p(t)=1-e^{-\gamma t}=\gamma t+o(t)$、$\gamma>0$，
不能同时来自上述有限、光滑、固定初态及固定零初始记录模型。
需说明开放极限、粗时间描述、持续新增记录的非一致极限或端点不正则性。
有限个新 ready 位本身仍受上述定理约束。
例如强行把前节旋转的 $q(t)$ 取为 $e^{-\gamma t/2}$，
其转角在零点为平方根阶，所得整体扩张不再是零点 $C^1$ 曲线。

内生钟也须区分参数规范与实际计时关系。
若 $t=f(\tau)$、$f'>0$ 为正则重标，

$$

\widetilde H(\tau)=f'(\tau)H(f(\tau)),\qquad
\widetilde H\,d\tau=H\,dt,\qquad
\int\|\widetilde H\|d\tau=\int\|H\|dt .

$$

有序积分、同一路径的门及积分范数预算相容不变。
正则重标不会把整体保距变成收缩，也不会把初始零概率斜率变成非零。
迭代阶数、梯度虚时间与实际观察者钟，只有通过明确的内部记录关系才可对应。
单有一条射线曲线不会决定它以何种速率被经历 [[8](#ref-clock), [5](#ref-v57)]。

**白话图景。** 短时间内，一个原来完全没有的记录先获得一阶振幅，再由平方读口变成二阶概率。
这能把连续性和平方联系起来，但平方读口已经在前提中。
时钟给变化标速率，递归给描述或校正排次序；二者可以关联，却不能因为都用一个参数就直接相同。

## 11. “分歧”需要在哪个映射上检查

二元关系并不普遍对应分歧点。下面列出五种不同情况。

<details style="max-width:100%;overflow-x:auto">
<summary>原稿表格生产设置与正文</summary>

```tex
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.19\textwidth}XX@{}}
\toprule
现象 & 明确例子 & 应检查的关系\\
\midrule
坐标图失效 & 射线比值 $\beta/\alpha$ 在 $\alpha=0$ 不可用 & 换用另一张图；状态可仍光滑。\\
投影漏信息 & 球面投影 $(x,y,z)\mapsto(x,y)$ 的两半球 & 保留 $z$ 符号或切换图册；赤道逆映射退化。\\
限制映射临界 & $z\mapsto[1:z^2]$ 在 $z=0$ & 实微分降秩，局部逆有 $\pm$ 支。\\
闭路留历史 & 同终点、不同 $K=\int a\,db$ & 路径运输、参考相位及终点信息是否完整。\\
动力学不唯一 & $\dot x=2\sqrt{|x|},\,x(0)=0$ & 向量场缺少保证初值唯一的局部 Lipschitz 条件。\\
\bottomrule
\end{tabularx}
```

</details>

<div role="region" tabindex="0" aria-label="原稿表格" style="overflow-x:auto">

| 现象 | 明确例子 | 应检查的关系 |
| --- | --- | --- |
| 坐标图失效 | 射线比值 $\beta/\alpha$ 在 $\alpha=0$ 不可用 | 换用另一张图；状态可仍光滑。 |
| 投影漏信息 | 球面投影 $(x,y,z)\mapsto(x,y)$ 的两半球 | 保留 $z$ 符号或切换图册；赤道逆映射退化。 |
| 限制映射临界 | $z\mapsto[1:z^2]$ 在 $z=0$ | 实微分降秩，局部逆有 $\pm$ 支。 |
| 闭路留历史 | 同终点、不同 $K=\int a\,db$ | 路径运输、参考相位及终点信息是否完整。 |
| 动力学不唯一 | $\dot x=2\sqrt{\vert x\vert },\,x(0)=0$ | 向量场缺少保证初值唯一的局部 Lipschitz 条件。 |

</div>

第三行可由完全光滑酉族实现：

$$

U(z)=\frac1{\sqrt{1+|z|^4}}
\begin{pmatrix}1&-\overline z^{\,2}\\z^2&1\end{pmatrix},
\qquad [U(z)|0\rangle]=[1:z^2].

$$

因此门族光滑不排除限制读口的临界点。
最后一行则有等待任意 $T\ge0$ 后再取 $x(t)=(t-T)^2$ 的不同解。
相反，连续线性 Schrödinger 方程在给定初值时唯一，前面已由积分递归证明。

谱简并、条件测量分支和正概率支持边界还可产生其他现象，
不应全部合并成“线性关系降秩”。尤其式 [(2)](#eq:metriccurv) 的球面等号
既可能有满实秩，也不是退相干或结果唯一性的证明。

## 12. 更紧凑的条件重构：从完整关系表到连续门

前面在已给复 Hilbert 接口内推导；现在说明如何把其中一部分结构重新放回关系表。
这延续项目 V22 的正核构造 [[2](#ref-v22)]，并明确连续性的新增条件。

#### 定义 12.1（完整历史关系与可逆重标）

设历史标签集为 $S$，有根 $o$。
归一复正核 $K:S\times S\to\mathbb C$ 满足
$K(h,k)=\overline{K(k,h)}$、$K(h,h)=1$，以及任意有限复系数

$$

\sum_{i,j}\overline{c_i}c_jK(h_i,h_j)\ge0 .

$$

允许重标为保持全部交叉核的双射 $T:S\to S$：
$K(Th,Tk)=K(h,k)$。
这些重标在接续与逆下闭合，且每个标签可由根通过允许重标到达。

#### 定理 12.2（平滑关系核的有限维量子历史重构）

<a id="thm:reconstruct"></a>

设上述核有限秩为 $d$。则存在 $d$ 维复 Hilbert 空间、唯一根向量 $\Omega$ 的指定表示，
及每个允许 $T$ 对应的酉 $U_T$，满足

$$

K(h,k)=\langle\psi_h,\psi_k\rangle,\qquad
\psi_h=U_{T_h}\Omega,\qquad T_ho=h .

$$

该最小表示在共同酉同构意义下唯一。
若 $T_t$ 为含零连通实区间上的允许重标族、$T_0=\operatorname{id}$，
并存在 $d$ 个独立锚 $h_j$，使全部 $K(h_i,T_th_j)$ 为 $C^1$，
则 $U_t$ 为 $C^1$ 酉曲线，具有 Hermitian 生成元。

**证明。**

在有限形式组合 $\sum c_h[h]$ 上用 $K$ 定义半正内积，商掉零范数向量。
正性给 Cauchy–Schwarz，故零范数子空间与全部向量正交，商内积良定。
有限秩使商空间恰为 $d$ 维。取 $\psi_h=[h]$、$\Omega=[o]$。

定义 $U_T[h]=[Th]$。保全部核保证它保持形式组合的范数，
从而保持零空间、在商空间上良定且等距；
$T$ 双射给满射，故为酉。根的可达性给 $\psi_h=U_{T_h}\Omega$。
任意另一最小实现都由 $[h]\mapsto\psi_h'$ 给等距满射，故唯一到共同酉。

令 $G_{ij}=K(h_i,h_j)$，独立性给 $G$ 可逆。
$U_t$ 在这组基下的矩阵为 $G^{-1}M(t)$，
其中 $M_{ij}(t)=K(h_i,T_th_j)$。
故其矩阵元为 $C^1$，定理 [8.1](#thm:h) 给 Hermitian 生成元。

**证毕。**

这里 $\Omega$ 是根标签的同一实际来源的表示，唯一性是给定完整核后最小表示的唯一性，
不是从条件中唯一算出了实际宇宙全部数据。
保持每个标签的范数不够：必须保持全部交叉关系。
原始两两块正也不够：必须有全部有限组合的正性，或前稿 v77 的等价完整二元合成检验。
在非正交锚基中生成矩阵 $L$ 的自伴条件为 $L^\dagger G=GL$；
通常的 Hermitian 矩阵式是在正交坐标中书写。

#### 推论 12.3（可数门字不能独自承载非平凡连续标签流）

<a id="cor:countable"></a>

若上述 $S$ 可数、参数区间连通，且全部 $T_t$ 始终把标签映回 $S$，
则连续 $U_t$ 必为常值；当 $T_0=\operatorname{id}$ 时 $U_t=I$。

**证明。**

每个连续锚轨迹 $U_t[h_j]$ 都落在可数集 $\{[h]:h\in S\}$。
若某个实坐标非恒定，连续性使其像包含一个非退化实区间，
与可数性矛盾。因此全部锚轨迹恒定，张成性给整个 $U_t$ 恒定。

**证毕。**

这不排除离散门字对连续门的稠密近似。
它说明精确的非平凡连续历史需要连续参数标签、适当闭包或极限历史；
也可保留离散标签，再另行指定采样之间的连续路径。
前面的核重构没有自动完成这一步。

#### 命题 12.4（效果读出还须绑定同一来源）

<a id="prop:born"></a>

另给完整矩阵效果域 $0\le E\le I$ 上的根响应 $p_o$，
要求它正、归一、仿射并对效果细分相容。
则有唯一密度矩阵 $\rho_o$ 使 $p_o(E)=\operatorname{Tr}(\rho_o E)$。
若再要求内部重复校准
$p_o(P_\Omega)=1$，其中 $P_\Omega=|\Omega\rangle\langle\Omega|$，
则 $\rho_o=P_\Omega$，故
$p_o(E)=\langle\Omega,E\Omega\rangle$。
若各准备还满足
$p_h(E)=p_o(U_{T_h}^\dagger E U_{T_h})$，
则 $p_h(E)=\langle\psi_h,E\psi_h\rangle$。

**证明。**

细分相容给 $p_o(0)=0$，正仿射响应扩张为 Hermitian 矩阵上的正实线性泛函。
有限维迹对偶给唯一 $\rho_o$；正性与单位归一分别给
$\rho_o\succeq0$、$\operatorname{Tr}\rho_o=1$。
校准使 $\operatorname{Tr}[\rho_o(I-P_\Omega)]=0$。
正性于是强制 $\rho_o$ 的支撑包含于一维的 $\operatorname{Ran} P_\Omega$，
再由迹为一得到 $\rho_o=P_\Omega$。
最后代入准备协变式即可。

**证毕。**

若没有根校准，$p_o(E)=\operatorname{Tr}(E)/d$ 也是正归一仿射响应，却通常不等于根纯态响应。
对投影 $E=P$，上述有前件的结果给 $\|P\psi_h\|^2$。
这些读出相容与校准条件不能由流形光滑性代替。

**白话图景。** 可以先把同一个 Ω 的所有历史相互比较所得的关系放在一张表里。
若这张表允许所有组合一致成立，又允许整体可逆地换标签而不破坏交叉关系，
向量空间和酉门就从这张表的表示中出现。平滑性再把门变成微分方程。
这缩短了表述，但“哪些关系真的成立”仍是需要说明和检验的内容。

## 13. 反向定位公理与本轮的整体结论

一项公理能被改写为更大结构的相容条件，
需要给出明确等价或必要性证明。仅举出一个违反后失败的例子，
不能证明所有其他方案都失败。
本轮得到以下可逐项检查的对应。

<details style="max-width:100%;overflow-x:auto">
<summary>原稿表格生产设置与正文</summary>

```tex
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.19\textwidth}XX@{}}
\toprule
待解释条件 & 受约束的二元关系 & 更大整体及撤去后的后果\\
\midrule
完整正性 & 任意两种合成历史的比较 & 完整 Gram 核；球外切向候选没有正 Hilbert 实现。\\
保酉 & 变化前后的全部交叉关系 & 可逆等距；只保个别范数不能锁定全门。\\
平滑性 & 相邻历史差与其极限 & 切丛及有限生成元；连续但非 $C^1$ 的门不满足该要求。\\
终点决定门 & 两条同端点路径 & 局部平坦及全局 holonomy；非零残差说明须保留历史。\\
三维各向同性 & 方向的成本与二阶响应 & 额外对称性；两场生成三维仍可仅有秩二主符号。\\
误差下降 & 当前读出与目标关系 & 下降律或局部记录；共同整体酉不提供共同吸引。\\
Born 读出 & 效果合并、根校准与准备协变 & 正仿射完整效果响应与同源绑定；光滑性只给已有平方律的短时阶。\\
\bottomrule
\end{tabularx}
```

</details>

<div role="region" tabindex="0" aria-label="原稿表格" style="overflow-x:auto">

| 待解释条件 | 受约束的二元关系 | 更大整体及撤去后的后果 |
| --- | --- | --- |
| 完整正性 | 任意两种合成历史的比较 | 完整 Gram 核；球外切向候选没有正 Hilbert 实现。 |
| 保酉 | 变化前后的全部交叉关系 | 可逆等距；只保个别范数不能锁定全门。 |
| 平滑性 | 相邻历史差与其极限 | 切丛及有限生成元；连续但非 $C^1$ 的门不满足该要求。 |
| 终点决定门 | 两条同端点路径 | 局部平坦及全局 holonomy；非零残差说明须保留历史。 |
| 三维各向同性 | 方向的成本与二阶响应 | 额外对称性；两场生成三维仍可仅有秩二主符号。 |
| 误差下降 | 当前读出与目标关系 | 下降律或局部记录；共同整体酉不提供共同吸引。 |
| Born 读出 | 效果合并、根校准与准备协变 | 正仿射完整效果响应与同源绑定；光滑性只给已有平方律的短时阶。 |

</div>

因此，适合作为下一步工作核心的不是把全部原理塞进“平滑”一词，
而是下列有前件的关系闭合结构：

$$

\boxed{
\text{完整复正核}
\ +\ \text{保核的可逆平滑接续}
\ +\ \text{内部效果与记录相容}.
}

$$

在本文有限接口条件下，它依次供应 Hilbert 表示、酉流与 Hermitian 生成元；
三维二元比较把其有限余量变成读数；
Schur 余量把局部长度与曲率放在同一个正核中；
可积条件说明何时终点能代表整条路径。
测量、稳定、优化和时钟仍需说明实际读口、记录与成本，才成为物理命题。

复数结构、完整正性、可达控制和读出组合条件并未从“本体唯一”四字单独推出。
可把它们写成同一整体内部的关系，但定义本身不能替代它们在实际系统中成立的证据。
相反，已证明的等价能减少独立假设：
给定完整正核就不必再独立指定一个任意 Hilbert 表示；
给定平滑保核可逆接续就不必另独立猜测 Hermitian 生成元。
这正是内生化公理的可执行含义。

**白话图景。** 整个系统可以这样看：只有一个 Ω，观察者、参考和记录都是它内部的关系。
门序列是沿这些关系取的离散刻度；连续描述把它展开成路径。
比较两个邻近变化，会读出长度、夹角和有向相位；交换变化顺序，还可能留下一个第三方向的历史量。
把所有方向和补空间一起拼起来，就必须满足同一套微分相容条件。
观察者越来越稳定，可以是差异转移到了内部记录，也可以是指定的校正规则在收敛；
完整可逆历史本身仍保存区别。我们要锁定的，是这些角色怎样同时成立，
而不是先把每一种变化都称作同一种递归。

## 固定来源与参考文献

<a id="ref-phase"></a>

**[1]**
The Omega Institute.
[AURIC 五模式概率、相位运输与 holonomy](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)。
固定提交同正文。本文消费 §§2、8、9 及 §§10.1–10.4 中相应定义与证明；
未消费后续扩散、Green 供应。特别使用命题 2.7、定理 9.3、定理 10.4–10.5。

<a id="ref-v22"></a>

**[2]**
The Omega Institute.
[V22：相对门历史、观测商与递归闭合](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)，§§1、6–7。

<a id="ref-v52"></a>

**[3]**
The Omega Institute.
[V52：纯态商几何、二次关系生成元与无损递归](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)，§§2–3、定理 7.2。

<a id="ref-v37"></a>

**[4]**
The Omega Institute.
[V37：二元关系、酉表示与黄金门通用性](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)，§9 的相对酉稳定结果。

<a id="ref-v57"></a>

**[5]**
The Omega Institute.
[V57：固定本体、增长观察者、稳定自我与相对钟](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_FIXED_ONTIC_STATE_GROWING_OBSERVER_STABLE_SELF_INTERNAL_PREDICTION_AND_RELATIVE_CLOCKS_V57.md)，
命题 2.4、§5、§8、命题 10.1。

<a id="ref-v58"></a>

**[6]**
The Omega Institute.
[V58：关系公理、共同复相位与条件量子重构](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md)，§§2–3、10、14。

<a id="ref-omega"></a>

**[7]**
The Omega Institute.
[$\Omega$ 静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，§§5、7、12 的指定段落。

<a id="ref-clock"></a>

**[8]**
The Omega Institute.
[Clock V31：内部记录、长期稳定与钟几何重构](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_INTERNAL_RECORDS_LONG_TERM_STABILITY_AND_CLOCK_GEOMETRY_RECONSTRUCTION_V31.md)，§§8–11；
物理四维与 Lorentz 二次钟律在该部分为前件。

<a id="ref-aa"></a>

**[9]**
J. Anandan and Y. Aharonov.
Geometry of quantum evolution.
*Physical Review Letters* 65, 1697–1700 (1990).
[doi:10.1103/PhysRevLett.65.1697](https://doi.org/10.1103/PhysRevLett.65.1697)。
本轮读取出版社摘要；本文度量约定与局部公式自行证明。

<a id="ref-roy"></a>

**[10]**
R. Roy.
Band geometry of fractional topological insulators.
[arXiv:1208.2055](https://arxiv.org/abs/1208.2055)。
本轮读取返回的 v1 正文中量子度量、曲率及式 (12) 的证明段；
不把该标准不等式作为本稿新发现。

<a id="ref-chen"></a>

**[11]**
I. Chevyrev and A. Kormilitzin.
A Primer on the Signature Method in Machine Learning.
[arXiv:1603.03788v2 (2025-01-17)](https://arxiv.org/html/1603.03788v2)。
本轮读取线性控制 ODE 的 Picard 讨论与 Chen identity 定理及证明；
不消费其中应用实验。

<a id="ref-dialogue"></a>

**[12]**
AURIC 本对话前稿 v74（连续历史与相位几何）、v77
（反向定位公理、二元比较与内部闭合），2026。
它们是本次讨论的延续稿，不是上述仓库提交中的文件。

---

原稿结束：`\end{document}`。

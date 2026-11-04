> **转换说明（V74 文稿实施者）。** 下文保留原稿正文、顺序、公式与来源陈述；原始制作设置及 TikZ 指令可展开读取。自定义数学命令仅作等价展开，图以保留原几何与标签的 SVG 呈现。署名“核读注”的文字为相邻附注，不替换原文。原稿中“本轮”“本文核对”“重新核对”等报告均归属于原稿作者的历史记述，不等于本次转换已实施相同动作。

<details>
<summary>原始制作设置、前导、元数据与排版命令（原样保留）</summary>
<div style="overflow-x:auto" tabindex="0" role="region" aria-label="原始制作设置">

```tex
% !TeX program = xelatex
% Compile twice with XeLaTeX. Optional: \def\AURICFontPath{/absolute/font/path/}
% Paper proofs only; no numerical mathematics or simulations were used.
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
\hypersetup{pdftitle={AURIC v74：平滑量子历史、余切与内生运动},
pdfauthor={AURIC research continuation},
pdfsubject={Smooth relational kernels, cotangent dynamics, internal frames and quantum reconstruction}}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\HH}{\mathcal H}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\Var}{\operatorname{Var}}
\newcommand{\spanof}{\operatorname{span}}
\newcommand{\grad}{\operatorname{grad}}
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
\fancyhead[L]{\small AURIC：平滑历史、余切与内生运动}
\fancyhead[R]{\small v74 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
```

</div>
</details>



# 平滑量子历史、余切与内生运动<br>

从关系的微小变化重建量子动力学<br>

AURIC 量子起源研究　 定义、定理与纸面证明　 v74.0<br>

2026 年 11 月 1 日　 Asia/Singapore


## 摘要

本轮把“球面上的门历史”和“余切产生运动”分成可证明的相容结构。
有限离散酉历史总有光滑插值，但插值与时钟不唯一；完整平滑相干关系及零余量闭合，
则唯一重建最小酉曲线。进一步，平移不变的光滑正历史核直接给单一来源的自治
Schrödinger 演化。读出的微分是余切；相容辛结构将其转成 Hamiltonian 方向。
单条射线轨迹确定水平生成元，却允许沿未探及方向的附加作用。
在矩阵期望函数类内，一点的一阶和二阶响应已确定整个算符到标量，
零阶值再固定共同相位生成项。
归一复二元态的三维球面具有非可积水平二平面；有向闭路产生第三个相位方向，
其局部形式与项目双墙控制的 Heisenberg 图相同。
同一正核的二阶水平余量同时给距离、辛面积、不确定性与闭路相位。
最后用内生移动参考和一个完整酉测量模型区分相对运动、局部退相干及条件稳定。
各主要推导均附白话说明；连续性、相位接口、实际控制与模型覆盖条件始终保留。



## 1 来源、问题与固定约定

本轮承接 v73 的“完整前缀态、参考关系体、零余核及共同接续”。
研究目标是把整体关系进一步微分化：怎样由邻近态的关系确定方向、速度和整个门？

本轮唯一实时 HEAD GET 于新加坡时间 2026-11-01 20:01:36
在收到 HTTP 响应前遇到网络权限拒绝；没有重试或备用活动端点。
以下基于六份重新核对 Git blob 的固定快照


`5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b`。


不声称取得该提交之后的新进展；“v74”为本对话稿件编号。

> **核读注（V74 文稿实施者，史料归属）。** 上述 20:01:36 的 HEAD GET、HTTP 响应前权限拒绝、未重试、无备用活动端点及六 blob 核对，是原作者记载的历史事件；本次未追查活动 HEAD，也未将其称作本次自动批准审查拒绝。下文原作者的来源与方法报告按同一归属读取。




<div style="overflow-x:auto" tabindex="0" role="region" aria-label="原稿表格">

| 固定项目来源 | 本轮实际承接 |
| --- | --- |
| V52 §§2--4 | 单位振幅球面、Hopf 商、Bloch 球面与高维纯态维数。 |
| V22 §§6--7 | 正历史核、共同接续、有向闭路与正交记录的接口区别。 |
| V58 §§3、10 | 三轴关系生成复单位；连续自同构保持相对复定向。 |
| $\Omega$ 静态纤维 §7 | 前缀传播核、内部记录及另给可微酉群后的连续生成元。 |
| Phase §§2.3、2.16、10.3--10.4 | 度量标度、声明连续控制、双墙两控制及余切主符号。 |
| Clock V31 §§9--11 | 内部单位、方向钟及纤维几何与事件位置的对应条件。 |

</div>



本文在有限维复生成扇区 $\mathcal H=\mathbb C^D$ 中证明，内积对第一变量共轭线性，
对第二变量线性，取 $\hbar>0$。所有来源、参考、效果和记录均可属于同一整体内部。
用连续参数并不另设外部观察者，但仍须说明它的内部校准。
无限维的强连续性、共同定义域和无界生成元不由本稿有限维证明自动覆盖。
全文只作纸面数学；程序仅用于文件、来源身份和排版。

> **核读注（V74 文稿实施者，定义域）。** 全文的单位来源与非空标签域取 $D\ge1$。有限插值的 $N=0$ 情形取常值酉曲线，并可在最外端常值延拓；可数拼接仅针对在实时间轴无有限聚点的样本集。一般无限秩核若要求 Hilbert 实现须取完备化，本稿有限秩证明不涉及无界生成元或无限维定义域结论。


本文的归一复正核是满足 $K(x,x)=1$、$K(y,x)=\overline{K(x,y)}$，且对任意有限标签和复系数均有

$$
\sum_{i,j}\overline{c_i}K(x_i,x_j)c_j\ge0
$$

的关系表。其核秩是全部有限 Gram 块秩的上确界。
在形式线性组合上用该二次型定义半内积，再商去零范数向量，便得最小 Gram 实现；
标签向量张成该实现，且共同内积表使任意两个最小实现酉同构。

为避免常数混淆，定义未加倍射线线元

$$
ds_0^2=\langle d\psi,d\psi\rangle-
|\langle\psi,d\psi\rangle|^2.
$$

本文相容几何取 $g=2\hbar ds_0^2$。项目 Phase 卷的 $g_{FS}=2ds_0^2$，
所以本稿 $g=\hbar g_{FS}$。同卷使用负指数相位；本稿各处另明定相位符号。
标准几何量子力学与能量方差速度关系已有文献 [[7](#ref-ashtekar)、[8](#ref-anandan)]；
以下有限维公式均另给证明，不作原创优先权声明。


**白话图景。** 同一个来源可以给许多内部读出。我们沿用整张关系图，再看这些关系怎样随小变化改变。
球面、方向和速度各有具体对象；把它们的接法说清楚，图像就能成为定理。



## 2 离散门历史怎样成为平滑轨迹


#### 定义 2.1（前缀与三种空间）

固定单位来源 $\Omega$。令
$U_k=G_k\cdots G_1$、$\psi_k=U_k\Omega$。
归一向量位于 $S^{2D-1}$；去整体相位的纯态位于 $\mathbb C P^{D-1}$。
只有 $D=2$ 时 $\mathbb C P^1\cong S^2$，即 Bloch 球面。
门自身位于 $U(D)$；$SU(2)\cong S^3$，其门曲线不能直接等同某个输入的 Bloch 曲线。



二元态 $\psi=(a,b)^{\mathsf T}$ 的三轴为

$$
r=(2\Re\bar ab,\ 2\Im\bar ab,\ |a|^2-|b|^2),\qquad |r|=1.
$$

这里归一化与共同相位商给 $S^3/U(1)\cong S^2$，不是将任意高维态无损塞进一个普通三维球。
项目 V52 已给完整图册和类型区别 [[1](#ref-v52)]。
若只读内部子系统的约化态，即使整体纯，它也可能位于 Bloch 球内。


#### 定理 2.2（有限离散历史的光滑酉插值）

给有限时刻 $t_0<\cdots<t_N$ 和酉前缀 $U_0,\ldots,U_N$，
存在 $C^\infty$ 酉曲线 $U(t)$ 通过这些值。因此 $\psi(t)=U(t)\Omega$ 是归一光滑插值。



**证明。**

每段增量 $V_j=U_{j+1}U_j^\dagger$ 由谱分解写成 $e^{-iA_j}$，其中 $A_j$ 自伴。
取光滑阶跃 $\chi:[0,1]\to[0,1]$，两端分别为零、一，所有正阶导数在两端均为零。
例如用正内部函数 $b(u)=e^{-1/[u(1-u)]}$、端点取零，
令 $\chi(s)=\int_0^sb(u)\,du/\int_0^1b(u)\,du$。
在第 $j$ 段定义

$$
U(t)=\exp\!\left[-i\chi\!\left(\frac{t-t_j}{t_{j+1}-t_j}\right)A_j\right]U_j.
$$

端值正确且接缝处所有导数相容。各段均酉，故得全局光滑插值。

□


插值并不唯一：阶跃速度、谱对数分支和段内闭合酉环都可改变。
这些连续操作也未必属于给定原生门菜单。
可数时刻若无有限聚点，可逐段作局部有限拼接；
若 $t_n\to T<\infty$ 而态在 $|0\rangle,|1\rangle$ 间交替，就不存在经过全部样本并连续延拓到 $T$ 的曲线。


**白话图景。** 门序列像一串有顺序的照片。有限照片能接成平滑动画，但中间怎样绕、走多快，
照片本身没有唯一规定。要让动画成为确定的动力学，还要保留跨时刻关系和共同操作规则。



## 3 完整平滑关系怎样锁定量子动力学


#### 定理 3.1（平滑相干帧重建）

设 $A=(a_1,\ldots,a_D)$ 为内部参考基，$B(t)=(b_1(t),\ldots,b_D(t))$ 为 $C^1$ 帧，
且 $B(t)^\dagger B(t)=A^\dagger A$。则唯一 $C^1$ 酉曲线为

$$
\boxed{U(t)=B(t)A^{-1},\qquad H(t)=i\hbar\dot U(t)U(t)^\dagger.}
$$

$H(t)$ 自伴，并满足 $i\hbar\dot U=HU$。



**证明。**

Gram 相同使 $U$ 保内积，满帧使它满射，基上的值给唯一性。
微分 $UU^\dagger=I$ 得 $\dot UU^\dagger$ 反厄米，故所列 $H$ 自伴。

□


仅知道每时刻帧内 Gram 恒定并不确定运动；上式的输出帧须在共同图表中给定。
只使用关系数据时，令 $K(s,t)$ 为两个时刻帧之间的交叉 Gram 块，取

$$
S=K(0,0)>0,\qquad C(t)=K(0,t).
$$

在联合正核下，若

$$
K(t,t)=S,\qquad C(t)^\dagger S^{-1}C(t)=S,
$$

则相对初始帧的正交余核为零，从而

$$
\boxed{K(s,t)=C(s)^\dagger S^{-1}C(t),\qquad T(t)=S^{-1}C(t).}
$$

证明是将各态投影到初始帧：对角余量为零使全部余向量为零。
于是 $T^\dagger ST=S$；$C^1$ 的 $C(t)$ 给 $C^1$ 的最小酉实现。
坐标生成矩阵 $L=i\hbar\dot TT^{-1}$ 满足 $L^\dagger S=SL$。
这正是 v73 零余量机制的连续版本。


#### 定理 3.2（单一来源的平移不变正核给自治演化）

<a id="thm:stationary"></a>

设 $K:\mathbb R\times\mathbb R\to\mathbb C$ 是归一 $C^1$ 正核，在整个声明时间域的核秩为有限 $D$，
且

$$
\boxed{K(s+a,t+a)=K(s,t)\qquad(s,t,a\in\mathbb R).}
$$

则其最小实现中存在唯一自伴 $H$，到标签保持共同酉同构为止，使

$$
\psi_t=e^{-itH/\hbar}\Omega,\qquad
K(s,t)=\langle\Omega,e^{-i(t-s)H/\hbar}\Omega\rangle.
$$




**证明。**

先作正核的最小 Gram 实现，令 $\Omega=\psi_0$。
定义 $U(a)\psi_t=\psi_{t+a}$。平移不变保持任意有限线性组合的范数，
因此保持全部线性零关系，$U(a)$ 良定义且等距。
$U(-a)$ 给逆，故酉；标签上的共同接续给 $U(a+b)=U(a)U(b)$。
取有限时间锚点 $t_j$ 构成基。它们的 Gram 为 $S>0$，
$U(a)$ 的基坐标为 $S^{-1}(K(t_i,t_j+a))_{ij}$，故为 $C^1$。
令 $A=U'(0)$，酉性给 $A^\dagger=-A$，群律给 $U'(a)=AU(a)$。
因此 $H=i\hbar A$ 自伴，$U(a)=e^{-iaH/\hbar}$。
所有标签张成且接续已给，故最小实现及其生成元唯一。

□


这里连续参数、全域秩覆盖和共同平移相容是前件；
已知有限样本不能自动提供它们。项目 $\Omega$ §7 原先从可微酉群推出生成元，
本定理把酉群进一步由正核及平移关系重建 [[4](#ref-omega)、[2](#ref-v22)]。


**白话图景。** 一根箭头的轨迹只说明它怎样走；完整参考架及跨时刻的连接，能确定整个门怎样转。
如果全部历史关系还只依赖两时刻的间隔，就得到同一条不随时刻改变的演化规则。
静态关系表因此能够编码动态方程，连续时钟的刻度仍须明确。



## 4 一条球面曲线能确定门的哪一部分

对 $C^1$ 单位曲线 $\psi(t)$，令

$$
P=|\psi\rangle\langle{\psi}|,\quad Q=I-P,\quad v=Q\dot\psi,\quad
E_\psi=i\hbar\langle\psi,\dot\psi\rangle\in\mathbb R.
$$

归一化使沿 $\psi$ 的速度纯为相位；$v$ 才改变射线。


#### 定理 4.1（给定轨迹的全部自伴生成元）

固定完整向量曲线时，$i\hbar\dot\psi=H\psi$ 的全部自伴解为

$$
\boxed{H=E_\psi P+i\hbar
(|v\rangle\langle{\psi}|-|\psi\rangle\langle{v}|)+QBQ,\qquad B=B^\dagger.}
$$

只固定射线曲线 $P(t)$ 时，全部解为

$$
\boxed{H=i\hbar[\dot P,P]+D,\qquad D=D^\dagger,\quad[D,P]=0.}
$$




**证明。**

向量方程固定 $H\psi=E_\psi\psi+i\hbar v$，即固定首列；
自伴性固定首行，余空间自伴块任意。
投影方程为 $i\hbar\dot P=[H,P]$。
由 $P^2=P$ 微分可得 $[[\dot P,P],P]=\dot P$，
故水平项满足方程，任意两解之差恰与 $P$ 对易。

□



#### 推论 4.2（水平最小范数与速度）

在全部实现同一射线速度的自伴算符中，唯一最小 Hilbert--Schmidt 范数者是

$$
H_{\rm hor}=i\hbar[\dot P,P],\qquad
\|H_{\rm hor}\|_{\rm HS}^2=2\hbar^2\|v\|^2.
$$

所有兼容生成元则具有同一方差

$$
\boxed{\operatorname{Var}_\psi(H)=\hbar^2\|v\|^2,\qquad \frac{ds_0}{dt}=\frac{\Delta H}{\hbar}.}
$$




**证明。**

水平项相对 $\mathbb C\psi\oplus\psi^\perp$ 为非对角块，对易项 $D$ 为对角块，
两者 HS 正交；所以添加非零 $D$ 严格增加范数平方。
另一方面 $QH\psi=i\hbar v$，故方差固定为 $\hbar^2\|v\|^2$。
线元定义给最后一式。

□


因此“最小方差”不能选出唯一门：这些门的方差相同。
最小 HS 准则是明定的数学选择，不等于未经给出的原生硬件成本。
能量方差与射影速度的关系是 Anandan--Aharonov 几何关系的该标度形式 [[8](#ref-anandan)]。

对 qubit 写

$$
P=\frac{I+r\cdot\sigma}{2},\quad |r|=1,\qquad
H=h_0I+\frac{\hbar}{2}h\cdot\sigma.
$$

Pauli 对易关系给

$$
\boxed{\dot r=h\times r,\qquad h=r\times\dot r+\lambda r.}
$$

第一式来自 $i\hbar\dot P=[H,P]$；第二式用
$(r\times\dot r)\times r=\dot r$，余自由度必平行于 $r$。
于是

$$
H_{\rm hor}=\frac{\hbar}{2}(r\times\dot r)\cdot\sigma,
\qquad \operatorname{Var}(H)=\frac{\hbar^2}{4}|\dot r|^2.
$$

若完整二元旋量连相位都给定，且限制 $\operatorname{Tr} H=0$，
则 $h_0=0$、$\lambda=2E_\psi/\hbar$，生成元唯一。
这保留“固定 $SU(2)$ 时完整单位旋量决定门”的特殊情形。


**白话图景。** 球面点怎样走，决定转轴横着推动它的部分。
再绕这个点自身方向转一下，眼前这个点不会移动，别的输入却可能改变。
完整相位、参考架或后面的二阶关系，可以把这份额外转动也确定下来。



## 5 由关系核的二阶变化得到距离、面积与手性


#### 定义 5.1（光滑关系核与水平二阶关系）

设实开参数域 $M\subset\mathbb R^m$ 上的 $K(x,y)$ 为 $C^2$ 归一正核，
在整个声明区域的核秩为有限 $D$。
选 $D$ 个独立锚点 $b_i$，令 $S_{ij}=K(b_i,b_j)$、
$c(x)_i=K(b_i,x)$。




#### 定理 5.2（光滑关系核生成几何张量）

<a id="thm:qgt"></a>

存在 $C^2$ 归一特征实现

$$
\psi(x)=S^{-1/2}c(x),\qquad
K(x,y)=\langle\psi(x),\psi(y)\rangle.
$$

定义

$$
\boxed{\mathcal Q_{ab}=
\left[\partial_{x^a}\partial_{y^b}K
-(\partial_{x^a}K)(\partial_{y^b}K)\right]_{y=x}.}
$$

则

$$
\mathcal Q_{ab}=\langle D_a\psi,D_b\psi\rangle,\qquad
D_a\psi=(I-P)\partial_a\psi.
$$

特别地 $\mathcal Q\succeq0$，且

$$
\boxed{1-|K(x,x+\delta)|^2
=\Re\mathcal Q_{ab}\,\delta^a\delta^b+o(\|\delta\|^2).}
$$




**证明。**

锚定 Schur 余核为 $R(x,y)=K(x,y)-c(x)^\dagger S^{-1}c(y)\succeq0$。
任何非零有限余块都会使完整 Gram 秩超过 $D$，故 $R=0$；
于是所列特征实现成立，归一化和光滑性直接得到。
分别对两个参数槽微分，二阶项为
$\langle\partial_a\psi,\partial_b\psi\rangle$，
两个一阶项的乘积恰为被扣去的垂直分量，故得水平 Gram 公式。
最后，左侧精确等于
$\|(I-P_{\psi(x)})\psi(x+\delta)\|^2$；
对后一个向量作一阶展开再取范数平方即得。

□


在水平切空间 $\psi^\perp$ 上定义

$$
g(u,v)=2\hbar\Re\langle u,v\rangle,\qquad
\omega(u,v)=2\hbar\Im\langle u,v\rangle,\qquad Ju=iu.
$$

则 $J^2=-I$，$\omega(u,v)=g(Ju,v)$，且
$\omega(u,Ju)=2\hbar\|u\|^2>0$（$u\ne0$）。
它们下降到完整射影态空间；闭性将在第八节由连接曲率直接得到。
参数拉回可能退化：一条实参数曲线上的二形式恒为零。
要读出局部有向面积，须有两个变化方向且 $\Im\langle u,v\rangle\ne0$；
完整射影图才保证所需的全切空间非退化性。

> **核读注（V74 文稿实施者，曲率指向）。** 此处“第八节”对应连接曲率的计算；第九节的局部截面等式 $d\mathcal A=\omega/\hbar$ 明列其下降及 $d\omega=0$ 的结论。$g,\omega$ 的非退化性属于完整射影切空间，任意参数拉回不继承该性质。



#### 命题 5.3（度量面积与相位面积的共同余量）


$$
\boxed{\det(g|_{u,v})-\omega(u,v)^2
=(2\hbar)^2\bigl(\|u\|^2\|v\|^2-|\langle u,v\rangle|^2\bigr)\ge0.}
$$

等号当且仅当 $u,v$ 复线性相关；qubit 的水平复维数为一，所以总取等号。



**证明。**

将 $\langle u,v\rangle$ 的实部、虚部分别代入度量行列式和辛项平方，
相减即得公式，非负性及等号条件来自 Cauchy--Schwarz。

□



**白话图景。** 相邻态关系的一阶变化告诉我们读数怎样变；扣掉共同相位以后，
二阶关系同时给出距离和有向面积。平方项来自正交微小位移的范数平方。
这把平方几何和相位几何接起来；概率的统计意义仍承接既有响应相容条件。



## 6 读出的余切怎样变成量子运动


#### 定义 6.1（读出余切与 Hamiltonian 方向）

对实函数 $f$，$df$ 是作用在切向 $v$ 上给变化率 $df(v)$ 的线性泛函。
本稿固定

$$
\boxed{\iota_{X_f}\omega=df,\qquad \omega(X_f,v)=df(v).}
$$

若 $g(\operatorname{grad} f,v)=df(v)$，则

$$
\boxed{X_f=-J\operatorname{grad} f.}
$$





#### 定理 6.2（矩阵读出的余切给 Schrödinger 方向）

设 $A=A^\dagger$，$f_A([\psi])=\langle\psi,A\psi\rangle$，
$A_0=A-f_AI$。对水平 $v$，

$$
(df_A)(v)=2\Re\langle A_0\psi,v\rangle,
$$


$$
\boxed{\operatorname{grad} f_A=\frac{A_0\psi}{\hbar},\qquad
X_A=-\frac{i}{\hbar}A_0\psi.}
$$

后者正是酉流 $e^{-itA/\hbar}$ 的射线速度。



**证明。**

微分期望值，利用 $A$ 自伴得到两共轭项之和；
水平性允许减去 $f_A\psi$。代入 $g$ 得梯度。
由 $\omega(u,v)=g(Ju,v)$，$JX_A=\operatorname{grad} f_A$，给所列方向。
直接微分酉流并水平投影，也给同一结果。

□


故“余切产生运动”的精确表达是
$df\stackrel{\omega}{\longmapsto}X_f$；其中转换结构不可省略。
$df$、正交余向量 $(I-P)\eta$ 和三角函数 $\cot\theta$ 不是同一类型。
同一读出的酉流沿其等值线运动，因为 $df_A(X_A)=0$。
沿另一个生成元 $H$，投影概率 $p=\langle P\rangle$ 才一般有

$$
\dot p=\frac{i}{\hbar}\langle[H,P]\rangle.
$$


在 Bloch 切平面 $u,v\perp r$ 上，

$$
g_r(u,v)=\frac{\hbar}{2}u\cdot v,\qquad
\omega_r(u,v)=\frac{\hbar}{2}r\cdot(u\times v),\qquad J_ru=r\times u.
$$

对于 $p_n=(1+n\cdot r)/2$，

$$
dp_n(u)=\frac12n\cdot u,\quad
\operatorname{grad} p_n=\frac{n-(n\cdot r)r}{\hbar},\quad
X_{p_n}=\frac{n\times r}{\hbar}.
$$

可在北极以 $d r=(2\Re d\psi_1,2\Im d\psi_1,0)$ 验证尺度，再用共同酉旋转推广。
若 $p_n$ 无量纲，物理生成作用还需要耦合强度及时间单位。

> **核读注（V74 文稿实施者，方向与效果类型）。** 此处 $n$ 是单位 Bloch 方向，$P_n=(I+n\cdot\sigma)/2$ 为秩一投影，$p_n$ 为其期望；任意实向量的相同代数公式不自动具有该投影类型。



#### 命题 6.3（保持球面与辛形式还不够）

球面函数 $f(r)=z^2$ 给

$$
X_f=\frac{4z}{\hbar}e_z\times r.
$$

它光滑、保持球面和辛形式，但不是所有输入上的共同线性酉作用。



**证明。**

由 $X_f=(2/\hbar)\nabla f\times r$ 得公式。
$z$ 沿流固定，所以各纬度角速度不同。
$r_0=(1,0,0)$ 固定，而 $s_0=(\sqrt{1-a^2},0,a)$（$0<a<1$）给

$$
\frac{1+r_0\cdot s(t)}2
=\frac{1+\sqrt{1-a^2}\cos(4at/\hbar)}2,
$$

其转移概率不恒定。共同酉必保持此概率，故不可能。
辛形式保持来自 $\mathcal L_{X_f}\omega=d(\iota_{X_f}\omega)=d^2f=0$。

□


相反，若 $F:S^2\to S^2$ 保持所有点积，令 $n_i=F(e_i)$，
则 $n_i$ 正交且 $F(r)\cdot n_i=r_i$，所以 $F(r)=Or$、$O\in O(3)$。
从恒等连续出发强制 $\det O=1$；轴角形式由
$e^{-i\theta n\cdot\sigma/2}$ 实现。
这是二元情形中“整体关系保持锁定酉运动”的直接证明。


**白话图景。** 余切像一张说明书：往每个方向微动，读数会怎样变。
度量把它变成朝读数增加处的梯度；共同复结构再转一次方向，得到沿等值线的 Hamiltonian 运动。
对于矩阵期望类读出，这个运动正是酉转动。
一条曲线好看且归一还不够，所有输入之间的关系必须一起保持。



## 7 余切及其变化怎样锁定整个门


#### 定理 7.1（一点的二阶响应确定矩阵读出）

<a id="thm:jet"></a>

固定参考 $\psi_0=e_0$ 及局部图

$$
\psi(z)=\frac{(1,z)^{\mathsf T}}{\sqrt{1+z^\dagger z}},
\qquad z\in\mathbb C^{D-1}.
$$

对 Hermitian 算符
$A=\left(\begin{smallmatrix}a&b^\dagger\\b&C\end{smallmatrix}\right)$，
其期望函数满足

$$
f_A(z)=\frac{a+2\Re(b^\dagger z)+z^\dagger Cz}{1+z^\dagger z}.
$$

在原点，

$$
\boxed{\begin{aligned}
f_A(0)&=a,\\
df_{A,0}(v)&=2\Re(b^\dagger v),\\
D^2f_{A,0}(u,v)&=2\Re\bigl[u^\dagger(C-aI)v\bigr].
\end{aligned}}
$$

因此 $f_A(0),df_{A,0},D^2f_{A,0}$ 唯一确定 $A$。
仅一阶、二阶资料则确定 $A$ 到标量倍恒等。



**证明。**

直接展开分子和 $(1+z^\dagger z)^{-1}$ 到二阶即可。
零阶给 $a$；以 $v=e_j,ie_j$ 检验一阶式，恢复 $b$ 的实、虚部。
令 $M=C-aI$，用 $u=e_j$、$v=e_k,ie_k$ 检验二阶式恢复全部 $M_{jk}$。
具体为

$$
b_j=\frac{df(e_j)+i\,df(ie_j)}2,\qquad
M_{jk}=\frac{D^2f(e_j,e_k)-iD^2f(e_j,ie_k)}2.
$$

若零阶未给，唯一剩余自由是同时改变 $a$ 与 $C$ 的共同标量，
即 $A\mapsto A+cI$。反向加标量只改函数常数，显然保持一、二阶资料。

□


这里 Hessian 是指定实坐标图上的二阶导数。
资料总量为 $1+2(D-1)+(D-1)^2=D^2$ 个独立实参数。
若 $A=H$，标量部分只改变整体门相位；
所以余切与其变化已经确定该时刻的完整酉通道生成元。
时间依赖的 $H(t)$ 需要沿时间取得相应资料，不能从某一时刻推定任意未来控制。

在二能级球面上，本段 $\nabla_S$ 与 $\operatorname{Hess}_S$ 采用单位球的普通圆球度量；
前文全局度量则为 $g=(\hbar/2)g_{\rm round}$。
若 $A=a_0I+h\cdot\sigma$，

$$
f_A(r)=a_0+h\cdot r,\qquad
\nabla_S f_A=h-(h\cdot r)r,
$$


$$
\boxed{\operatorname{Hess}_S f_A(u,v)=-(h\cdot r)\,u\cdot v.}
$$

最后一式可沿球面测地线二次微分得出，再极化。
所以梯度确定转轴横向，Hessian 确定纵向，函数值确定标量。

本定理限于已认证的矩阵期望函数类；任意光滑函数可加上 $\|z\|^4$ 而不改原点二阶资料。
同源邻域的全部方向响应也是实际接口前提，不是单份未知态的一次读出。

> **核读注（V74 文稿实施者，作者来源与边界）。** Ashtekar–Schilling §II.C.1（作者稿印页 13–14）已陈述可观察期望函数由一点的函数值及前两阶导数确定；本节给有限维指定实坐标中的直接恢复公式，不主张该思想的优先权。$D=1$ 时一、二阶资料为空，算符全为标量，零阶即确定其唯一参数；$D>1$ 时任意光滑函数的四阶加项反例适用。



**白话图景。** 当前的读数告诉我们站在哪里，一阶变化告诉我们现在朝哪里受推动，
再看这个变化率向周围怎样改变，就能补全门对其他方向的作用。
“关系的关系”在这里恰好是二阶响应；在已确定的矩阵模型里，它足以把整个门锁定到共同相位。



## 8 二元水平关系怎样产生第三个相位方向


#### 定义 8.1（归一二元态的连接一形式）

在 $S^3=\{\psi\in\mathbb C^2:\|\psi\|=1\}$ 上取

$$
\alpha=-i\langle\psi,d\psi\rangle.
$$

它是实一形式；$\alpha(i\psi)=1$，$\ker\alpha=\psi^\perp$ 是实二维水平面。




#### 定理 8.2（非可积水平面与内生手性）

对于水平 $u,v$，

$$
d\alpha(u,v)=2\Im\langle u,v\rangle=\omega(u,v)/\hbar.
$$

特别地 $d\alpha(u,iu)=2\|u\|^2$，从而 $\alpha\wedge d\alpha\ne0$。
若水平向量场 $X,Y$ 满足 $\alpha(X)=\alpha(Y)=0$，则

$$
\boxed{\alpha([X,Y])=-d\alpha(X,Y).}
$$

因此两个水平变化的顺序可以生成相位方向。



**证明。**

直接微分 $\alpha$ 得
$d\alpha(u,v)=-i(\langle u,v\rangle-\langle v,u\rangle)$。
在三元组 $(i\psi,u,iu)$ 上，$\alpha\wedge d\alpha$ 的值为 $2\|u\|^2>0$。
外微分定义给
$d\alpha(X,Y)=X\alpha(Y)-Y\alpha(X)-\alpha([X,Y])$，
代入水平条件即得。

□


这是一种接触结构。$\alpha$ 与上一节读出微分 $df$ 都是余切一形式，但用途不同。
$df$ 精确且 $d(df)=0$；任意 $\mu df$ 都满足
$(\mu df)\wedge d(\mu df)=0$，所以不能把它直接等同这里的 $\alpha$。


### 可以直接画出的局部形式

在全支撑局部图取

$$
\psi=e^{i\chi}\bigl(\sqrt{1-p},\sqrt p\,e^{i\phi}\bigr)^{\mathsf T},
\qquad 0<p<1.
$$

则

$$
\alpha=d\chi+p\,d\phi.
$$

以 $x=-p,\ y=\phi,\ z=\chi$ 为局部实提升坐标，得到

$$
\boxed{\alpha=dz-x\,dy,\qquad
X=\partial_x,\qquad Y=\partial_y+x\partial_z,\qquad[X,Y]=\partial_z.}
$$

沿水平路径 $\alpha(\dot\gamma)=0$，即 $\dot z=x\dot y$。
依次执行 $X$ 方向 $a$、$Y$ 方向 $b$、$X$ 方向 $-a$、$Y$ 方向 $-b$，
只要全程留在图内，就有

$$
\boxed{\Delta x=\Delta y=0,\qquad \Delta z=ab.}
$$

证明只需逐段代入：两段 $Y$ 的贡献分别为 $(x+a)b$ 与 $-xb$。
反向绕圈改变符号。



<div style="overflow-x:auto" tabindex="0" role="region" aria-label="原稿水平矩形闭路图，可横向滚动">
<div style="width:900px">
<svg xmlns="http://www.w3.org/2000/svg" width="900" height="255" viewBox="0 0 900 255" role="img" aria-label="依次 X 正 a、Y 正 b、X 负 a、Y 负 b，控制平面回到起点，有向面积 ab；水平约束 dz=x dy，总相位位移 Δz=ab；第三方向来自两次变化的顺序。">
<defs><marker id="v74-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="rgb(24,53,79)"/></marker></defs>
<g fill="none" stroke="rgb(24,53,79)" stroke-width="2.2" marker-end="url(#v74-arrow)"><path d="M 65 210 H 321"/><path d="M 321 210 V 50"/><path d="M 321 50 H 65"/><path d="M 65 50 V 210"/></g>
<g font-family="system-ui, sans-serif" font-size="18" fill="#20252b"><text x="193" y="240" text-anchor="middle">X: +a</text><text x="334" y="136">Y: +b</text><text x="193" y="32" text-anchor="middle">X: −a</text><text x="4" y="136">Y: −b</text><text x="193" y="120" text-anchor="middle">控制平面回到起点</text><text x="193" y="150" text-anchor="middle">有向面积 ab</text><text x="450" y="90">水平约束：dz=x dy。</text><text x="450" y="138">总相位位移：Δz=ab。</text><text x="450" y="186">第三方向来自两次变化的顺序。</text></g>
</svg>
</div>
</div>

<details>
<summary>原始 TikZ 图指令（原样保留）</summary>
<div style="overflow-x:auto" tabindex="0" role="region" aria-label="原始 TikZ 指令">

```tex
\begin{tikzpicture}[>=Stealth,font=\small]
\coordinate (a) at (0,0);\coordinate (b) at (3.2,0);
\coordinate (c) at (3.2,2.0);\coordinate (d) at (0,2.0);
\draw[->,thick,auricblue] (a)--node[below] {$X:\ +a$}(b);
\draw[->,thick,auricblue] (b)--node[right] {$Y:\ +b$}(c);
\draw[->,thick,auricblue] (c)--node[above] {$X:\ -a$}(d);
\draw[->,thick,auricblue] (d)--node[left] {$Y:\ -b$}(a);
\node[align=center] at (1.6,1) {控制平面回到起点\\有向面积 $ab$};
\node[align=left,text width=6cm] at (7.8,1)
{水平约束：$dz=x\,dy$。\\[5pt]
总相位位移：$\Delta z=ab$。\\[5pt]
第三方向来自两次变化的顺序。};
\end{tikzpicture}
```

</div>
</details>



项目 Phase §10.3 的原生双墙控制在受保护局部图中也精确具有
$\partial_x,\partial_y+x\partial_z$ 形式 [[5](#ref-phase)]。
这里对应的是局部控制与连接结构；不把两模型的 Hilbert 嵌入、全局拓扑、
度量和原生费用一并视为相同。指定态的水平路径有酉提升，
但这些坐标场不自动给所有未知输入上的同一个线性酉门。

同卷 §10.4 还有一个重要约束：若瞬时二阶控制只有 $X,Y$，
且控制协方差 $A=(a^{ij})$ 正定，则余切主符号为

$$
\sigma(\xi)=\sum_{i,j=1}^2a^{ij}\xi(X_i)\xi(X_j),\qquad (X_1,X_2)=(X,Y).
$$

它的秩为二，$\alpha$ 在其核内。
证明是映射 $\xi\mapsto(\xi(X),\xi(Y))$ 的秩为二，正定 $A$ 不改变该秩。
若 $A$ 仅半正定，则只能保证秩不超过二。
所以闭路可以达到第三方向，不表示它已有同一时钟下的独立瞬时方差。


**白话图景。** 每一步都被限制在一个二元水平面里，然而这个平面会随位置改变。
沿两个方向绕一圈，底下的读出回来了，上面的相位却能多转一点。
绕圈的方向就是手性，留下的相位就是这段历史的关系。
这里的第三方向是相位或控制历史方向，尚不能直接叫作第三个物理空间坐标。



## 9 三态闭路、不确定性与平方来自同一二元正关系


#### 定理 9.1（小三态闭路的精确关系）

给水平 $u,v\perp\psi$ 和实参数 $\epsilon,\delta\in\mathbb R$，取

$$
\psi_u=\frac{\psi+\epsilon u}{\sqrt{1+\epsilon^2\|u\|^2}},
\qquad
\psi_v=\frac{\psi+\delta v}{\sqrt{1+\delta^2\|v\|^2}}.
$$

则有向 Bargmann 量为

$$
\boxed{\mathcal B
=\frac{1+\epsilon\delta\langle u,v\rangle}
{(1+\epsilon^2\|u\|^2)(1+\delta^2\|v\|^2)}.}
$$

因此在零附近连续相位支上

$$
\arg\mathcal B=\epsilon\delta\Im\langle u,v\rangle
+O((\epsilon\delta)^2).
$$




**证明。**

按顺序乘

$$
\langle\psi,\psi_u\rangle\langle\psi_u,\psi_v\rangle
\langle\psi_v,\psi\rangle
$$
，水平性使交叉项消失，给精确分式。
分母为正实数，对分子的局部对数取虚部即得展开。

□


三角的首阶辛面积为 $\omega(u,v)\epsilon\delta/2$，
故上述相位首项等于面积除以 $\hbar$。
对局部截面连接 $\mathcal A=-i\langle\psi,d\psi\rangle$，
$d\mathcal A=\omega/\hbar$，也给 $\omega$ 的闭性。
相位重选使 $\mathcal A\mapsto\mathcal A+d\chi$。
包含回到首态闭合因子的顺序内积乘积，其细分闭路相位为 $+\oint\mathcal A$；
水平提升的回路相位为 $-\oint\mathcal A$。
第八节矩形中 $\mathcal A=-xdy$，故两者分别为 $-ab$ 与 $+ab$。
此处沿实际矩形路径的内积乘积取细分极限；只乘四个角点的有限 Bargmann 量一般没有这个精确面积等式。
整体相位不可单独读出；与内部参考分支比较的相对相位可影响干涉。
永久正交时钟记录的完整核则没有这些跨时交叉项，
须明确选择数据因子或相干比较接口 [[2](#ref-v22)]。


#### 定理 9.2（不确定性是同一个水平 Gram 正性）

设 $A=A^\dagger$、$B=B^\dagger$，令 $A_0=A-\langle A\rangle I$、$B_0=B-\langle B\rangle I$，

$$
C_{AB}=\tfrac12\langle A_0B_0+B_0A_0\rangle,\qquad
D_{AB}=\tfrac1{2i}\langle[A,B]\rangle.
$$

则

$$
\boxed{\operatorname{Var}(A)\operatorname{Var}(B)\ge C_{AB}^2+D_{AB}^2.}
$$




**证明。**

两个水平向量 $A_0\psi,B_0\psi$ 的平方范数为方差，
交叉内积为 $C_{AB}+iD_{AB}$。
其二阶 Gram 行列式非负即为所列不等式。

□


若两个方差都非零，可归一化为

$$
x=\frac{C_{AB}}{\Delta A\,\Delta B},\quad
y=\frac{D_{AB}}{\Delta A\,\Delta B},\quad
z=\sqrt{1-x^2-y^2},
\qquad x^2+y^2+z^2=1.
$$

这是明确的“两个读出加正余量归一”关系；不把这组新坐标未经接口映射直接等同原生五模式标签。
纯 qubit 中两个水平向量处于同一复一维空间，上述强化不确定性取等号，故 $z=0$。


**白话图景。** 距离看关系的实部，绕圈相位看关系的虚部，测不准看同一对方向的正性余量。
它们来自同一张二元关系表。平方在这里承担范数和正性的角色；
其概率解释仍使用先前已经明确的响应一致性。



## 10 内生观察者怎样读到运动与时间


#### 定理 10.1（移动内部参考的相对生成元）

设 $i\hbar\dot\Psi=H\Psi$，内部参考为 $C^1$ 酉 $R(t)$。
定义 $\psi=R^\dagger\Psi$，则

$$
\boxed{i\hbar\dot\psi=H_{\rm rel}\psi,\qquad
H_{\rm rel}=R^\dagger HR-i\hbar R^\dagger\dot R.}
$$




**证明。**

对 $R^\dagger R=I$ 微分得
$\dot R^\dagger R=-R^\dagger\dot R$。
再微分相对态并代入源方程即得；$R^\dagger\dot R$ 反厄米，故第二项自伴。

□


如果来源代表固定为 $\Psi=\Omega$，取 $H=0$，便有

$$
\psi=R^\dagger\Omega,\qquad H_{\rm rel}=-i\hbar R^\dagger\dot R.
$$

对随观察者固定的内部效果 $E_0$，

$$
p(t)=\langle\psi,E_0\psi\rangle
=\langle\Omega,R(t)E_0R(t)^\dagger\Omega\rangle.
$$

这与 $\psi=U\Omega$ 相容，只需取 $U=R^\dagger$。
如果态与效果同时作纯坐标换写，概率不变；可见运动来自实际相对读口关系。
三轴 Clifford 关系给共同 $J$ 后，从恒等连续连接的关系自同构不能把 $J$ 跳成 $-J$，
因为两种中心像离散 [[3](#ref-v58)]。这固定相对定向，不推出绝对宇称破缺。

> **核读注（V74 文稿实施者，代数扇区）。** 这里使用 V58 §10 的同一有限复矩阵扇区上的含幺实 $*$ 自同构及恒等连通路径；中心复单位的可选像为 $\pm J$。这不是任意有重数表示、任意无限代数或全部物理变换的实现定理。



### 时钟重标和离散采样

若 $\tau=f(t)$、$f'(t)>0$，同一路径的生成元变为

$$
H_\tau=\frac{dt}{d\tau}H_t.
$$

所以几何路径本身不固定物理速度标尺。
即使知道全部整数采样，也可能遗漏整周：
给非零真投影 $P$ 和步长 $\Delta>0$，

$$
H_m=\frac{2\pi\hbar m}{\Delta}P,\qquad
e^{-in\Delta H_m/\hbar}=I\quad(m,n\in\mathbb Z).
$$

这些自治生成元在采样点完全相同，点间一般不同。
若另认证自治 $H$ 的谱严格位于 $(-\pi\hbar/\Delta,\pi\hbar/\Delta)$，
单步门无分支歧义，主对数才唯一给出 $H$。
证明来自该区间上实谱相位映射单射及有限维谱分解。

位置估计也不自动控制速度误差。对固定非标量自伴 $A$ 和 $\epsilon>0$，

$$
U_\epsilon(t)=e^{-i\epsilon\sin(t/\epsilon^2)A}
$$

满足 $\|U_\epsilon-I\|\le\epsilon\|A\|$，而
$H_\epsilon(0)=(\hbar/\epsilon)A$。
前界由自伴谱分解及 $|e^{ix}-1|\le|x|$ 得到，后式直接微分。
稳定恢复生成元因此需要导数或带宽控制。


**白话图景。** 本体可以在整体表示中保持静态，观察者自己的参考关系不断变化，
于是它读到相对运动。沿轨迹走了多远与内部钟走了多久是两个量：
要谈速度、能量或局域钟快慢，必须把二者的对应关系也保留下来。



## 11 测量怎样兼容整体酉轨迹与条件稳定


#### 定理 11.1（内部记录的平滑酉测量模型）

设 $P$ 为正交投影、$Q=I-P$，内部记录初态为 $|0\rangle$。
取 $0\le\theta\le\pi/2$，

$$
R_\theta=e^{-i\theta\sigma_y},\qquad
U_\theta=P\otimes I+Q\otimes R_\theta.
$$

则 $U_\theta$ 平滑且酉，两个记录分支算子为

$$
K_0=P+\cos\theta\,Q,\qquad K_1=\sin\theta\,Q.
$$

忽略记录结果时

$$
\boxed{\mathcal E_\theta(\rho)=
P\rho P+Q\rho Q+\cos\theta(P\rho Q+Q\rho P).}
$$




**证明。**

$P,Q$ 正交且和为一，所以 $U_\theta=e^{-i\theta Q\otimes\sigma_y}$。
对记录 $|0\rangle$ 展开旋转即得 $K_0,K_1$；
$K_0^\dagger K_0+K_1^\dagger K_1=I$。
求和 $K_j\rho K_j^\dagger$ 得通道。

□


在 qubit 取 $P=(I+\sigma_z)/2$，该通道为

$$
(r_x,r_y,r_z)\longmapsto
(\cos\theta\,r_x,\cos\theta\,r_y,r_z).
$$

初始纯态若 $0<\langle P\rangle<1$，$\theta>0$ 时约化态严格进入球内。
整体包含记录的态仍纯且归一。

记初始 $p=\langle\psi,P\psi\rangle$。记录零的概率为
$q_0=p+(1-p)\cos^2\theta$；
仅在 $q_0>0$ 时定义条件态

$$
\boxed{\psi_{0,\theta}=\frac{(P+\cos\theta Q)\psi}{\sqrt{q_0}},
\qquad p_{0,\theta}=\frac p{p+(1-p)\cos^2\theta}.}
$$

当 $\theta\to\pi/2$ 且 $p>0$，它趋于 $P\psi/\sqrt p$。
另一个分支仅在 $\theta>0,p<1$ 时有正概率，条件态已精确为
$Q\psi/\sqrt{1-p}$。若投影退化，稳定的是对应扇区，不会消去扇区内部自由度。

在 $\theta<\pi/2$ 令 $s=-\log\cos\theta$，则零分支可写为

$$
\psi_s=\frac{e^{sP}\psi}{\|e^{sP}\psi\|},\qquad
\frac{d\psi_s}{ds}=(P-p_sI)\psi_s,\qquad
\boxed{\frac{dp_s}{ds}=2p_s(1-p_s).}
$$

直接微分归一指数即得两式。相对于本文度量，这是 $\hbar\operatorname{grad} p$ 的流；
相应酉方向则多乘 $-i$，沿 $p$ 的等值线运动。
$s$ 是滤波参数，终点为 $s\to\infty$，不是已证明的无限物理时间。
整体 $U_\theta$ 对 $\theta$ 光滑，但 $\theta(s)=\arccos(e^{-s})$ 在 $s=0$ 导数发散，
不能把条件态对 $s$ 的光滑性直接传给全部联合态。

> **核读注（V74 文稿实施者，滤波与酉流标度）。** 精确地，滤波水平速度为 $(P-pI)\psi=\hbar\operatorname{grad}p$；乘 $-i$ 后为 $-i(P-pI)\psi=\hbar X_p$。若使用本稿按 $p$ 定义的 Hamiltonian 场 $X_p$，还须除以 $\hbar$；以同一无量纲参数写该酉流则相当于生成元 $\hbar P$。此处不据滤波参数给出物理时间标定。$p=0,1$ 的滤波态各自不动；$q_0=0$ 的端点仍不定义零分支条件态。



**白话图景。** 观察发生在同一个整体内部：系统和记录一起酉演化。
只看系统会读到退相干；再按已经读到的记录选支，条件态可以逐渐稳定到一个结果扇区。
转动、忽略记录和按记录条件化各有清楚的公式。
这个模型说明它们如何相容，并未另行解决单个结果为何被唯一体验的本体论选择。



## 12 更简洁的关系公理组织

在前轮已声明的有限正关系模型中，可以把本轮动力学组织为三个条件。


#### 定义 12.1（平滑关系重建条件）

**S1：共同正关系及微分覆盖。**
同源标签有归一复正核，所声明邻域具有足够光滑性和有限秩覆盖；
相位参考与内部比较接口保留。其二阶水平关系给 $g,\omega$。

**S2：共同接续保持完整关系。**
所有声明输入的关系由同一步共同保持，生成部分闭合。
平滑满帧确定酉曲线；额外的时间平移相容确定自治群。

**S3：读出及复合相容。**
同一准备的效果响应归一、非负并保持线性关系；
三轴与复合定向条件提供共同复结构。
实际测量须包含其内部记录及条件化合同。



S1 中的复结构可以沿项目 V58 的实三轴关系
$X^2=Y^2=Z^2=I$、两两反对易及结合乘法来提供：
$J=XYZ$ 满足 $J^2=-I$。
这仍要求那些上游关系；三个标题不把它们自动省去。
S3 承接前轮的迹响应重建，纯态效果因而给
$p(P_\phi)=|\langle\phi,\psi\rangle|^2$。
本文没有从一般二元逻辑重新推出复正性、连续性或全部实际控制。

> **核读注（V74 文稿实施者，前轮响应前提）。** 所承接的 V73 第八节要求同一准备、同一条件化下的效果菜单含 $I$、实线性张成 Hermitian 空间并保持全部实线性关系，且在稠密覆盖全部秩一方向的同一响应上非负，才得到正迹一矩阵。上式平方律还取该准备为 $\rho=|\psi\rangle\langle\psi|$，读口 $\phi$ 归一；只对有限不完备菜单非负不能替代这些条件。




<div style="overflow-x:auto" tabindex="0" role="region" aria-label="原稿表格">

| 本轮被确定的结构 | 决定它的关系 |
| --- | --- |
| 平滑最小态族 | 有限秩、光滑、归一正核及全域覆盖 |
| 酉曲线和生成元 | 完整跨时刻关系、零余量及共同接续 |
| 自治 Schrödinger 律 | 再加整张历史核的时间平移相容 |
| 瞬时射线速度 | 水平切向，或读出余切与相容辛结构 |
| 完整门的其余作用 | 完整相干帧，或矩阵期望类内的一阶、二阶邻域响应 |
| 第三相位方向 | 非可积水平约束及有向闭路 |
| 不确定性与相位面积 | 同一二元水平 Gram 的实部、虚部和正性 |
| 条件稳定与退相干 | 明定的内部酉记录耦合、读口和条件分支 |

</div>



最有用的三条本轮链为

$$
\boxed{\text{光滑正关系核}
\ \Longrightarrow\ \text{水平二阶关系}
\ \Longrightarrow\ \text{度量与定向面积}.}
$$


$$
\boxed{df+\text{非退化辛结构}\ \Longrightarrow\ \text{Hamiltonian 方向}.}
$$


$$
\boxed{\text{余切}+\text{余切的变化}
\ \Longrightarrow\ \text{完整酉通道生成元}}
$$

最后一条限于已认证的矩阵期望函数类；一般 Hamiltonian 方向并不自动保持所有态之间的转移关系。
前两条的非退化几何须在完整相关切空间上理解。
空间位置、质量与引力还需要项目所要求的内部钟和物理方向对应，
不能把态空间曲率或相位方向直接换名成这些量 [[6](#ref-clock)]。



**白话图景。** 在这套条件模型中，只有同一个 $\Omega$，每段门历史都是它的一种内部读出。
当这些关系可以平滑细分时，读出在态空间里连成轨迹；观察者自己的参考也在这张图里变化。
一次读出先告诉我们各个微小变化会怎样改变量，这就是余切；
共同复定向把这种变化率转成相容的旋转方向。
两个允许方向绕一圈可以留下相位，所以历史即使回到同一个球面点，仍可能保留可比较的关系。
继续读“变化率怎样变化”，便能补全门对其他方向的作用。
时间记录接续，测量记录分支；完整关系始终放在同一个整体中检查。




## 固定来源与参考文献


<a id="ref-v52"></a>

**[1]** 项目固定快照。
[V52：纯态商几何、二次关系生成元与无损递归](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)，§§2--4。

<a id="ref-v22"></a>

**[2]** 项目固定快照。
[V22：相对门历史、观察商与递归闭合](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)，§§6--7。

<a id="ref-v58"></a>

**[3]** 项目固定快照。
[V58：关系公理、共同复相位与条件量子重建](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md)，§§3、10。

<a id="ref-omega"></a>

**[4]** 项目固定快照。
[$\Omega$ 静态相融纤维理论](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，§7。

<a id="ref-phase"></a>

**[5]** 项目固定快照。
[AURIC FIB-ATOM：概率、相位运输与闭路](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)，
§§2.3、2.16、10.3--10.4。本文使用已声明局部场及其自足符号秩论证，
不把该卷全部先行供应链声称为本轮重新认证。

<a id="ref-clock"></a>

**[6]** 项目固定快照。
[Clock V31：内生记录、长期稳定与时钟几何重建](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_INTERNAL_RECORDS_LONG_TERM_STABILITY_AND_CLOCK_GEOMETRY_RECONSTRUCTION_V31.md)，§§9--11。

<a id="ref-ashtekar"></a>

**[7]** A. Ashtekar and T. A. Schilling.
*Geometrical Formulation of Quantum Mechanics*.
[arXiv:gr-qc/9706069](https://arxiv.org/abs/gr-qc/9706069)，1997，§II。
本文核对其几何约定、Hamiltonian 期望值与方差速度表述；有限维证明另行给出。

> **核读注（V74 文稿实施者，外部作者原文范围）。** 本次直接核读公开作者稿 arXiv:gr-qc/9706069 的完整 §II（印页 6–21 的本节范围）：式 (2.1)–(2.5)、(2.16)、(2.22)–(2.26) 给本稿的几何、Hamiltonian 符号与方差速度对照，§II.C.1 给二阶资料的已有背景。该稿含无限维讨论；本稿不把那些额外结论并入有限维证明的保证。


<a id="ref-anandan"></a>

**[8]** J. Anandan and Y. Aharonov.
*Geometry of quantum evolution*.
Phys. Rev. Lett. 65, 1697--1700 (1990).
[doi:10.1103/PhysRevLett.65.1697](https://doi.org/10.1103/PhysRevLett.65.1697)。
本轮核对出版社摘要的归属与表述；未把原论文全文冒称为重新逐式审阅。

> **核读注（V74 文稿实施者，出版社摘要范围）。** 本次直接读取 APS 的该论文元数据与摘要：摘要将沿给定射影曲线的能量不确定度时间积分联系于 Fubini–Study 路长，并说明不依赖实现这条曲线的特定 Hamiltonian。公开页的全文入口要求授权；此处不消费其全文前提，不声称全文逐式核读，本文的常数与有限维公式由所列纸面证明承担。



`\end{document}`
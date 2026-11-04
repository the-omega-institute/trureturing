<!-- AURIC V64 faithful Markdown conversion. Generated from immutable source.tex; source SHA-256: 6840e861340ca3cf0d7d84759b0b46365206ec049d0dde4c38cc555c4564f8e1. -->

<details>
<summary>原始 XeLaTeX 文档设置（逐字保留）</summary>

<textarea readonly cols="32" rows="66" wrap="off" aria-label="原始 XeLaTeX 文档设置">
% !TeX program = xelatex
% Compile twice with XeLaTeX. Optional font directory: \def\AURICFontPath{/absolute/path/}
% Paper mathematics only; no mathematical program, CAS, numerical test or enumeration was run.
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
\hypersetup{pdftitle={AURIC v64：近似关系的刚性、平方标定与量子读出稳定性},
pdfauthor={AURIC research continuation},
pdfsubject={Approximate multiplicative weights, coherent return calibration, orientation rigidity, positive readout orbits, and internal records}}
\newcommand{\R}{\mathbb R}
\newcommand{\C}{\mathbb C}
\newcommand{\Q}{\mathbb Q}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\Herm}{\operatorname{Herm}}
\newcommand{\Ran}{\operatorname{Ran}}
\newcommand{\op}{\mathrm{op}}
\newcommand{\calJ}{\mathcal J}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/#1}{#2}}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{lemma}[definition]{引理}
\newtheorem{remark}[definition]{说明}
\renewcommand{\proofname}{证明}
\renewcommand{\abstractname}{摘要}
\renewcommand{\refname}{固定来源与文献}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{2pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC：近似关系与量子起源}
\fancyhead[R]{\small v64 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]

\newcommand{\diag}{\operatorname{diag}}
\newcommand{\logit}{\operatorname{logit}}
\newcommand{\TV}{d_{\mathrm{TV}}}
</textarea>
</details>

# 近似关系的刚性、平方标定

## 与量子读出稳定性

**共同虚单位、相干旁观分支、可达正性与完整记录**

AURIC 量子起源研究  定义、定理与纸面证明  v64.0

2026 年 11 月 1 日  Asia/Singapore

> **摘要**
> 本轮固定项目新增入库 V57--V59，并在 V49 追加同源三端口的有限平方标定。
> 本文承接其关系正性与指数标定结论，再补出三条条件性稳定桥。
> 第一，全域对数乘性缺陷与未归一权重有界性，经 Hyers 倍增方法给唯一邻近幂律；
> 非零旁观分支把射影回返误差转为相干系数误差，与同一粗事件读数合成指数区间。
> 第二，原生实二维响应的小守恒缺陷与非退化根钟，能锁定精确共同复定向，
> 并给邻近酉模型及有限门字误差。
> 第三，实际秩一读口的方向偏差、增益和关系残差共同控制负谱质量，
> 不需候选矩阵的先验范数界。
> 最后证明保留精确波动坐标的完整历史在总变差下可能不连续，
> 并给守卫横截、配置路径和连续档案读出的适当稳定条件。
> 全篇保留一个固定本体 $\Omega$ 与完整内生观察者；表示存在、实际取得和物理必然性分开陈述。
> 没有从裸二元逻辑、唯一性或有限观测无条件推出全部量子公理。

## 固定项目进展与本轮问题

> **编者归属说明（原稿写作轮次）。** 本节及摘要中“本轮”“上一轮”的项目取得、变化计数、目录树、核读范围和 V14 链接勘误，均为 V64 原作者对原稿所载写作轮次的历史报告。包括取得时刻、提交时刻、26 个提交、39 个路径、1125 项及各来源的核读陈述；这些报告不表示 Markdown 整理者重新实施或独立认证了相同行为。

本轮唯一活动 HEAD 取得固定为
`5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b`。
取得完成于新加坡时间 2026-11-01 04:53:44.991702；提交时间为 04:53:30。
相对 v63 的 `a42f32e9a2a54ec0b01748c96a6af312f941c853`，
前进 26 个提交、39 个变化路径；固定比较 JSON 与完整 diff 新侧路径相同。
四层目录树未截断，theory 共 1125 项。
此后只按固定身份读取，不声称写作结束时仍为活动 HEAD。[来源：head]

直接相关的进展是：

1. V59 新入库，给局部乘积关系完备、共同复中心扇区、秩一轨道正性，
以及无需候选范数上界的有限正性界。本轮连续核读全部 1400 行。[来源：v59]
1. V49 真正追加 §§13--16，原文 1279--1715 行全部核读。
两次三端口相干回返与一次粗事件守恒，在全域权重正则类中选择平方；
其末尾仍留下全域近似乘性及相干误差桥。[来源：v49]
1. V57、V58 为此前研究稿转换入库，本轮来源审查全文核读。
固定本体、记录稳定与中心胶合的已有结论不重计为本轮发现。
文中旧 HEAD、制作和审读报告属于原作者历史行为。[来源：v57, v58]
1. Quantum IV §§209--213 固定身份未变，是本文原生复结构部分的起点。
RRO 新 §§68--70 只作标题及首尾范围定位，不认证全部新证明，也不以其作为稳定性前提。[来源：qiv]

上一轮聊天 V14 链接误写了提交字符串；上一轮 PDF 与 `.tex` 的固定宏正确，
旧文件保持不变。本轮链接均用上述完整固定 SHA。

全篇始终固定同一个实际 $\Omega$；完整观察者的酉前缀为
$$
\Psi_k=U_k\cdots U_1\Omega.
$$
环境、参考、记录、控制、预测与自我都在其中。
以下实纤维、三端口、矩阵读出和历史空间是内部关系接口。
不同参数模型是误差比较对象，不是为每个读口另选一个宇宙。
同源、共同切口、实际读口、相干比较、持久记录与失败合同均须按接口取得；
把不同数学模型放在一起，不自动供应其物理实现桥。

## 项目已有的平方标定：旁观分支固定相对尺度

#### 定义 2.1（精确乘性权重及三端口）

设有限值 $w:\mathbb{C}\to[0,\infty)$ 满足
$$
w(0)=0,\quad w(1)=1,\quad w(zz')=w(z)w(z'),
\quad \sup_{|z|\le1}w(z)<\infty.
$$
对非零端口向量 $v$，定义已声明的互斥端口响应
$$
\Pi_w(C\mid v)=\frac{\sum_{j\in C}w(v_j)}{\sum_jw(v_j)}.
$$
在同一幅度标定下给
$$
\psi=(a,0,b)^{\mathsf T},\quad ab\ne0,\quad
H_0=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\quad
G_\lambda=(\lambda H_0)\oplus1,\quad \lambda\ne0.
$$
第三端口保持系数一，粗事件固定为 $C=\{1,2\}$；
两次调用之间不重标相对幅度。
若 $\Pi_w$ 解释为实际概率，另给端口报告、同一事件与相干比较的实际对应。

<a id="thm:exact-square"></a>
#### 定理 2.2（项目 V49 定理 13.3 的有限标定）

若上述来源满足
$$
[G_\lambda^2\psi]=[\psi],
\qquad
\Pi_w(C\mid G_\lambda\psi)=\Pi_w(C\mid\psi),
$$
则 $\lambda=\pm1/\sqrt2$、$w(z)=|z|^2$，且 $G_\lambda^\dagger G_\lambda=I_3$。

**证明。**

非零输入上 $w$ 严格正，因为 $w(z)w(z^{-1})=1$。
盘内若 $w(z)>1$，乘性使 $w(z^n)$ 无界，矛盾。
单位圆上 $w(u),w(u^{-1})\le1$ 且乘积为一，故均等于一。
于是权重径向，且 $r\le s$ 时 $w(r)=w(s)w(r/s)\le w(s)$。
$F(t)=\log w(e^t)$ 为单调可加函数，有理夹逼给 $F(t)=pt$、$p\ge0$；
故非零处 $w(z)=|z|^p$，零点独立规定为零。
$H_0^2=2I_2$ 给 $G_\lambda^2\psi=(2\lambda^2a,0,b)^{\mathsf T}$。
射线比例由 $b\ne0$ 固定为一，再由 $a\ne0$ 得 $2\lambda^2=1$。
置 $A=w(a)>0$、$B=w(b)>0$、$k=2w(\lambda)$，
粗事件守恒成为 $kA/(kA+B)=A/(A+B)$，故 $k=1$。
乘性给 $w(2)w(\lambda)^2=1$，即 $w(2)=4$，幂分类遂给 $p=2$。
复方程给 $\lambda=\pm1/\sqrt2$，直接计算即得酉性。

只有两个活动端口时，共同缩放被归一化隐藏；
非零旁观分支使活动块相对参考块的尺度可辨。
$a=0$ 或 $b=0$ 时指数不再确定。
仅要求端口概率返回也不够：$\lambda=i/\sqrt2$ 会在两次作用后翻转活动块相位，
概率返回而射线不返回。[来源：v49]

未归一盘有界性不能由归一概率的值域替代。
V49 命题 13.5 的 Hamel 构造满足
$w(2)=4$、$w(1/\sqrt2)=1/2$、$w(3)=27$，
精确通过有限合同却不是平方。
有限标定的全域结论仍以全域函数类条件为基础。[来源：v49]

## 近似乘性、相干回返与平方指数的稳定性

<a id="def:approx-weight"></a>
#### 定义 3.1（全域对数乘性缺陷）

设 $w:\mathbb{C}\to[0,\infty)$，$w(0)=0$、$w(1)=1$，
且 $0<w(z)<\infty$ 对 $z\ne0$ 成立。
未归一权重在闭单位盘有统一有限上界。
给有限 $\epsilon_w\ge0$，要求
$$
|\log w(zz')-\log w(z)-\log w(z')|\le\epsilon_w
\qquad(z,z'\ne0).
$$
量词是全部非零复数，不是从有限测试自动得到的合同。

<a id="thm:hyers"></a>
#### 定理 3.2（邻近幂律，Hyers 方法的群版本）

定义 [定义（全域对数乘性缺陷）](#def:approx-weight) 蕴含存在唯一 $p\ge0$，使
$$
\boxed{|\log w(z)-p\log|z||\le\epsilon_w\qquad(z\ne0).}
$$

**证明。**

置 $f(z)=\log w(z)$，$a_n(z)=2^{-n}f(z^{2^n})$。
缺陷界给
$|a_{n+1}(z)-a_n(z)|\le2^{-n-1}\epsilon_w$。
故 $A(z)=\lim_na_n(z)$ 存在，且 $|A(z)-f(z)|\le\epsilon_w$。
乘群交换，因而
$|a_n(zz')-a_n(z)-a_n(z')|\le2^{-n}\epsilon_w$；
取极限得 $A(zz')=A(z)+A(z')$。
设盘内 $w\le M_w$，则盘内 $a_n(z)\le2^{-n}\log M_w$，
所以 $A(z)\le0$。
单位圆上的 $u,u^{-1}$ 均在盘内，且 $A(u)+A(u^{-1})=0$，故 $A(u)=0$。
因此 $A$ 只依赖模长，且 $r\le s$ 时
$A(r)-A(s)=A(r/s)\le0$。
$t\mapsto A(e^t)$ 是单调可加函数，有理夹逼给
$A(z)=p\log|z|$、$p\ge0$。
若另有 $p'$ 满足统一有限误差，则令 $|\log|z||\to\infty$ 可知 $p=p'$。

倍增同质化沿用 Hyers 稳定性方法，原论文 Theorem 1 给出其近可加机制。
本文在交换乘群上完整证明所需版本，不声称工具的新颖性。[来源：hyers]
证明的无限极限不是观察者实际完成无限门序列。

<a id="prop:gauge"></a>
#### 命题 3.3（近似乘性不再给精确射线不变性）

对固定端口向量 $v$、非零缩放 $c_0$ 及两边质量皆正的粗事件 $C$，
$$
|\operatorname{logit}\Pi_w(C\mid c_0v)-\operatorname{logit}\Pi_w(C\mid v)|
\le2\epsilon_w,\qquad \operatorname{logit} q=\log\frac q{1-q}.
$$
零质量或全质量事件仍保持为零或一，但不对其取 logit。

**证明。**

每个非零叶子满足
$w(c_0v_j)=w(c_0)w(v_j)e^{e_j}$、$|e_j|\le\epsilon_w$。
事件与补事件权重和除共同因子后，各在原和的 $e^{\pm\epsilon_w}$ 倍以内；
赔率之比遂在 $e^{\pm2\epsilon_w}$ 之间。

所以以下保留字面幅度标定，不能把精确乘性时的射线不变性偷带进近似模型。
射影距离是相干几何比较，不等于未经标定的报告概率。

<a id="lem:ray"></a>
#### 引理 3.4（非零旁观分支的射影条件数）

保持同一 $\psi=(a,0,b)^{\mathsf T}$、$ab\ne0$，置
$$
r=\frac{|a|^2}{|a|^2+|b|^2},\quad s=1-r,\quad z=2\lambda^2.
$$
对非零 $v$ 记 $P_v=vv^\dagger/\|v\|^2$。
相干射影距离 $e=\|P_{G_\lambda^2\psi}-P_\psi\|$ 满足
$$
\boxed{e^2=\frac{rs|z-1|^2}{r|z|^2+s}.}
$$
若已取得 $e\le e_0<\sqrt s$，则
$$
\boxed{|2\lambda^2-1|\le
d_r:=\frac{e_0}{\sqrt r(\sqrt s-e_0)}.}
$$
后续指数界还要求 $d_r<1$，等价于
$e_0<\sqrt{rs}/(1+\sqrt r)$。

**证明。**

秩一投影距离平方为一减去归一重叠平方：
$$
e^2=1-\frac{|rz+s|^2}{r|z|^2+s}
=\frac{rs|z-1|^2}{r|z|^2+s}.
$$
令 $u=|z-1|$，有 $\sqrt{r|z|^2+s}\le1+\sqrt r\,u$，
故 $\sqrt{rs}\,u\le e_0(1+\sqrt r\,u)$。在正分母域整理即得。

$r,s$ 只用于几何距离；概率公式仍使用原始标定的 $a,b$。
$r$ 或 $s$ 趋零时条件数退化；$z\to+\infty$ 时 $e\to\sqrt s$ 而系数缺陷无界。
本引理要求相干欧氏度量和比较的取得，不从待证 Born 概率倒推出该度量。

<a id="thm:pinterval"></a>
#### 定理 3.5（近似关系的平方指数区间）

沿用前述 $\psi,G_\lambda,C$、$ab\ne0$ 及同源幅度与报告合同，
以定义 [定义（全域对数乘性缺陷）](#def:approx-weight) 替代精确乘性。令
$q_0=\Pi_w(C\mid\psi)$、$q_1=\Pi_w(C\mid G_\lambda\psi)$。
它们严格介于零与一。设有限 $\eta\ge0$、$0\le d_r<1$，若
$$
|2\lambda^2-1|\le d_r<1,\qquad
|\operatorname{logit} q_1-\operatorname{logit} q_0|\le\eta,
$$
置 $b_w=\eta+2\epsilon_w$。当 $b_w<\log2$ 时，
$$
\boxed{
\frac{2(\log2-b_w)}{\log(2/(1-d_r))}
\le p\le
\frac{2(\log2+b_w)}{\log(2/(1+d_r))}.
}
$$
无需 $b_w<\log2$ 的对称界为
$$
\boxed{
|p-2|\le
\frac{2[-\log(1-d_r)+\eta+2\epsilon_w]}
{\log(2/(1+d_r))}.}
$$

**证明。**

写 $f(z)=p\log|z|+e(z)$，$|e(z)|\le\epsilon_w$。
第三端口未变，赔率相除精确给
$$
v:=\operatorname{logit} q_1-\operatorname{logit} q_0
=\log2+f(\lambda a)-f(a)
=\log2+p\log|\lambda|+\xi,\quad |\xi|\le2\epsilon_w.
$$
令 $u=\log(2|\lambda|^2)$，则
$$
\log(1-d_r)\le u\le\log(1+d_r),\qquad
p=2\frac{\log2-v+\xi}{\log2-u}.
$$
分母为正；$b_w<\log2$ 时分子有正下界，取端点得区间。
再用 $p-2=2(u-v+\xi)/(\log2-u)$ 及
$|u|\le-\log(1-d_r)$ 得对称界。

若只有 $|q_1-q_0|\le d_q$，还须
$q_0,q_1\in[\vartheta,1-\vartheta]$、$0<\vartheta<1/2$，
才能取 $\eta=d_q/[\vartheta(1-\vartheta)]$。
近零、近一处绝对概率误差不统一控制 logit。
系数缺陷可由引理 [引理（非零旁观分支的射影条件数）](#lem:ray) 取得，但普通概率回返不能替代相干回返。
这些是必要区间，不反称区间内每个指数都满足原复相干缺陷。

<a id="cor:depth"></a>
#### 推论 3.6（有限深度的指数可辨识性）

在定义 [定义（全域对数乘性缺陷）](#def:approx-weight)、同一三端口及 $ab\ne0$ 条件下，
假定同一已标定 $|\lambda|=1/\sqrt2$，整数深度 $n\ge1$ 的活动事件含
$2^n$ 个幅度为 $a\lambda^n$ 的互斥持久叶，旁观幅度仍为 $b\ne0$，
终叶全部用同一个 $w$。则
$$
\left|\operatorname{logit} q_n-\operatorname{logit} q_0-
n\left(1-\frac p2\right)\log2\right|\le2\epsilon_w.
$$
若 $|\operatorname{logit} q_n-\operatorname{logit} q_0|\le\eta_n$，则
$$
\boxed{|p-2|\le\frac{2(\eta_n+2\epsilon_w)}{n\log2}.}
$$

**证明。**

精确赔率差为 $n\log2+f(a\lambda^n)-f(a)$；
同一个全域幂近似在两个端点的残差差不超过 $2\epsilon_w$。

误差不写成 $n\epsilon_w$，因为使用的是全域端点近似。
只有逐层局部缺陷、逐层独立归一或换用不同权重时，此结论无保证。
深度需实际记录容量、空端口、共同标定和事件持久性，不给免费无限树或多项式资源。
常数 $2\epsilon_w$ 一般不能减半：
非零处 $w(z)=|z|^p\exp(\epsilon_w\operatorname{sgn}\log|z|)$ 满足缺陷界，
两端跨过单位圆时残差差可达到 $2\epsilon_w$。
指数接近二也不等于全域相对平方误差小：只直接得到
$$
|\log w(z)-2\log|z||\le
\epsilon_w+|p-2|\,|\log|z||.
$$
统一相对误差还需限制幅度动态范围或另外取得归一端口误差合同。

## 近似守恒仍能锁定精确共同复方向

承接 Quantum IV §§209--210，保持有限连通配置图、实际根 $q_*$、
实二维正内积纤维 $V_q$、实响应 $L_q$ 和精确等距边 $T_{qr}$；
$T_{rq}=T_{qr}^{-1}=T_{qr}^\dagger$。
令 $x+x^2=1$、$x>0$、$c=x\sqrt x$、$\alpha=3\pi/5$。
原正交投影 $B_j$ 在可翻转块为
$$
B_j=\begin{pmatrix}xI&cT_{qr}\\cT_{qr}^\dagger&x^2I\end{pmatrix},
\qquad A_j=\alpha\mathcal L(I+B_j),\quad
\mathcal L=\bigoplus_qL_q,
$$
其余块保留原 $0/1$ 阻塞和边界条件。[来源：qiv]

#### 定义 4.1（无穷小守恒缺陷与根钟）

假定 $\delta,\tau\ge0$，且
$$
\|A_j+A_j^\dagger\|\le\delta,\qquad
\left|\frac12\operatorname{Tr}(L_{q_*}^\dagger L_{q_*})-1\right|\le\tau.
$$
置
$$
S_q=\frac{L_q+L_q^\dagger}{2},\quad
K_q=\frac{L_q-L_q^\dagger}{2},\quad
s=\frac{\delta}{2\alpha},\quad b=\frac{\delta}{\alpha c}.
$$
记 $\nu_q=\|K_q\|$；根图半径为 $R=\max_q\operatorname{dist}(q_*,q)$。

缺陷描述有限响应模型或几何标定的近似，
不宣称唯一 $\Omega$ 的本体演化真实违反酉性。
邻近精确模型是数学比较，不代表实际执行归一过滤、后选择或删除记录。

<a id="lem:local-defects"></a>
#### 引理 4.2（局部缺陷与根非退化）

有
$$
\|S_q\|\le s,\qquad
\|K_q-T_{qr}K_rT_{qr}^\dagger\|\le b.
$$
若 $a_0=\sqrt{1-\tau-s^2}>0$、$a_1=\sqrt{1+\tau}$，
则 $a_0\le\nu_*:=\|K_{q_*}\|\le a_1$。

**证明。**

$A_j+A_j^\dagger$ 的对角块为 $2\alpha(1+p_j(q))S_q$，
其中 $p_j(q)\in\{0,1,x,x^2\}$，故压缩范数给第一界。
非对角块右乘 $T_{qr}^\dagger$ 并除 $\alpha c$，
得到范数不超过 $b$ 的 $L_q+T_{qr}L_r^\dagger T_{qr}^\dagger$。
取反自伴部分在算子范数下不增，恰给第二界，无须再加 $2s$。
实二维反自伴 $K_q$ 满足 $K_q^\dagger K_q=\|K_q\|^2I$。
对称与反对称部分迹正交，因而
$$
\tfrac12\operatorname{Tr}(L_*^\dagger L_*)=\nu_*^2+\tfrac12\operatorname{Tr}(S_*^2),
\qquad 0\le\tfrac12\operatorname{Tr}(S_*^2)\le s^2.
$$
结合根钟上下界即得。

<a id="thm:rigidity"></a>
#### 定理 4.3（二维定向刚性）

若
$$
\boxed{a_0>0,\qquad (2R+1)b<2a_0,}
$$
则每个 $K_q\ne0$，并且
$$
J_q=\frac{K_q}{\|K_q\|},\quad \mathcal{J}=\bigoplus_qJ_q
$$
满足精确等式
$$
\boxed{J_q^2=-I,\quad J_q^\dagger=-J_q,\quad
J_qT_{qr}=T_{qr}J_r.}
$$
原边 $T_{qr}$ 不需要修复，且 $[\mathcal{J},B_j]=0$。

**证明。**

沿根路径反复使用引理 [引理（局部缺陷与根非退化）](#lem:local-defects)，
$|\nu_q-\nu_*|\le Rb$，所以 $\nu_q\ge a_0-Rb>b/2\ge0$。
在实二维正内积空间内，正交复结构只有两种：
任意正交基中其矩阵为
$\left(\begin{smallmatrix}0&-k\\k&0\end{smallmatrix}\right)$，
平方负一迫使 $k=\pm1$。
故 $J_q$ 与 $T_{qr}J_rT_{qr}^\dagger$ 要么相同，要么相反。
若相反，则
$$
\|K_q-T_{qr}K_rT_{qr}^\dagger\|
=\nu_q+\nu_r\ge2(a_0-Rb)>b,
$$
矛盾。边交织精确成立；其余结论由定义和 $B_j$ 的块形式得到。

项目无相邻占据位图中，先删 $q_*\setminus q$、再加 $q\setminus q_*$
始终合法，给 $R\le m$，无需枚举。
若直接给 $\nu_q\ge\nu_{\min}>0$，条件可缩为 $b<2\nu_{\min}$。
严格性有两点反例：$K_q=aJ_0$、$K_r=-aJ_0$、$T=I$
的边缺陷为 $2a$，归一后方向仍相反。
单顶点无边时只需 $a_0>0$，不需要边阈值。

本定理锁定离散定向分支，没有清除连续相位曲率。
即使所有守恒缺陷为零，合法方块一条边取 $-I$，
仍可保持共同 $J$ 而有非平凡闭路运输。
整数门交换继续独立承担相位装配条件。

<a id="thm:word"></a>
#### 定理 4.4（邻近酉模型与有限门字）

在定理 [定理（二维定向刚性）](#thm:rigidity) 的前提下，对全部内部时长 $t\ge0$，
令
$$
\ell=s+\max\{1-a_0,a_1-1\}+Rb,\quad a=2\alpha\ell,\quad
A_j^0=\alpha\mathcal{J}(I+B_j),
$$
$$
g_\delta(t)=
\begin{cases}
(e^{\delta t/2}-1)/(\delta/2),&\delta>0,\\
t,&\delta=0.
\end{cases}
$$
则 $A_j^0$ 精确复线性反自伴，且
$$
\|\mathcal L-\mathcal{J}\|\le\ell,\quad
\|A_j-A_j^0\|\le a,\quad
\|e^{tA_j}-e^{tA_j^0}\|\le a g_\delta(t),\quad
\|e^{tA_j}\|\le e^{\delta t/2}.
$$
置 $\kappa=e^{\delta/2}$、$q=a g_\delta(1)$。
若整数端点 $\mathsf K_j=e^{A_j}$ 满足远地址交换界
$\|[\mathsf K_j,\mathsf K_k]\|\le\varepsilon$，
修复酉门的交换界可取
$$
\varepsilon_{\rm eff}=\varepsilon+2q(\kappa+1).
$$
对原 $m=9,13$ 来源中一个已允许的长度 $L$ 门字，
在固定根标架中与平坦原规范酉门字 $U_w$ 比较，有
$$
\boxed{\|\mathsf K_w-U_w\|\le Q_L
:=a g_\delta(L)+\frac{Lh_m}{\gamma}\varepsilon_{\rm eff},}
\quad h_m=\lceil m/2\rceil-1,\quad
\gamma=2c|\sin(\alpha/2)|.
$$

**证明。**

根频率区间及边频率差给
$\|L_q-J_q\|\le s+|\nu_q-1|\le\ell$。
$[\mathcal{J},B_j]=0$ 给 $A_j^0$ 的性质，
$\|I+B_j\|\le2$ 给生成元界。
范数平方微分及 $A_j+A_j^\dagger\le\delta I$ 给增长界。
Duhamel 恒等式为
$$
e^{tA_j}-e^{tA_j^0}
=\int_0^t e^{(t-u)A_j}(A_j-A_j^0)e^{uA_j^0}\,du;
$$
积分范数即 $a g_\delta(t)$。
两个有序乘积各相差至多 $q(\kappa+1)$，故交换子界成立。
修复模型的翻转块仍为 $R_qT_{qr}$，其中
$R_q=c e^{\alpha J_q}(e^{\alpha J_q}-I)$、
$R_q^\dagger R_q=\gamma^2I$。
合法方块的对角交换块是
$R_t^2(T_{ta}T_{as}-T_{tb}T_{bs})$，
故方块运输差不超过 $\varepsilon_{\rm eff}/\gamma^2$。
固定升序添加路径，每条新边最多经过 $h_m$ 次合法交换，
给边标架差 $h_m\varepsilon_{\rm eff}/\gamma^2$。
投影脉冲 $e^{i\alpha}[I+(e^{i\alpha}-1)B_j]$
遂给每门到平坦规范门的距离至多 $h_m\varepsilon_{\rm eff}/\gamma$；
酉乘积差望远镜给长度 $L$ 的第二项。
原响应到修复酉门字的差至多
$q\sum_{r=0}^{L-1}\kappa^r=a g_\delta(L)$，
包括 $\delta=0$ 的连续值。两项相加；$L=0$ 时均为零。

这里原 $A_j,\mathsf K_w$ 一般仅为实线性，因为 $S_q$ 未必与 $J_q$ 对易；
修复 $A_j^0,U_w$ 才保证复线性。所有比较范数先在同一个实载体上计算。
因此 $\mathsf K_w^\dagger E\mathsf K_w$ 不仅未必小于 $I$，
也未必与 $\mathcal{J}$ 对易，不能未经桥接当作下一节的复效果，
更不能用条件归一化直接取得复密度矩阵或 Born 读出。

<a id="lem:bandwidth"></a>
#### 引理 4.5（有带宽的有限内部时刻证书）

若 $\|A\|\le M$、$0<h\le1$、$Mh\le1/8$，
且 $\|e^{hA^\dagger}e^{hA}-I\|\le\epsilon_h$，则
$$
\|A+A^\dagger\|\le\frac{3\epsilon_h}{2h}.
$$

**证明。**

置 $S=A+A^\dagger$，$F(t)=e^{tA^\dagger}e^{tA}-I$。
有 $F'(t)=e^{tA^\dagger}Se^{tA}$，
且 $\|F'(t)-S\|\le\|S\|(e^{2Mt}-1)$。
当 $z=2Mh\le1/4$ 时，$e^z\le(1-z)^{-1}$，所以
$$
\|F(h)-hS\|\le
\|S\|\left(\frac{e^{2Mh}-1}{2M}-h\right)
\le\frac h3\|S\|.
$$
吸收得到结论；$M=0$ 时直接成立。

这仍是全输入算子证书，不授予分数调用或任意准备。
无带宽时，取 $D=\operatorname{diag}(1+\xi,1)$、
$J_0=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$、
$A=D(\omega J_0)D^{-1}$。
整个脉冲近等距缺陷由 $(1+\xi)^2-1$ 控制，与 $\omega$ 无关；
但 $\|A+A^\dagger\|=|\omega|[(1+\xi)-(1+\xi)^{-1}]$ 可无界。
这是一般响应反例，不声称满足原根钟与全部原生门前件。

> **编者限定（带宽反例的参数域）。** 上段相似变换反例取实数 ξ>0、实数 ω。固定任意足够小的正 ξ，再让 |ω| 无界；在此域内 D 可逆，所写缺陷上界与范数等式的右端非负。该限定只补足本段反例的参数域。

## 由实际相干轨道取得稳定正性

V59 的链条是：关系一致性给 Hermitian 迹一候选，
足够丰富的非零秩一轨道非负性再给正性。
在其有限实 Clifford 商类中，局部乘积效果完备当且仅当保留一个相对复定向中心扇区。
这些是特定代数中的结论，不由唯一 $\Omega$ 或一般局部层析单独推出。
一般量子重构的局部层析路线同样使用额外系统与复合条件。[来源：v59, barnum]

#### 定义 5.1（固定候选与实际秩一探针）

在已声明的 $d$ 维复矩阵接口上，选实际效果实基
$F_0=I,F_1,\ldots,F_{d^2-1}$，以同一切口读数 $b_0=1,b_1,\ldots$
拟合唯一 $H=H^\dagger$、$\operatorname{Tr} H=1$。
若 $D_j$ 为迹对偶基，则 $H=\sum_jb_jD_j$。
另有有限非空组实际效果
$$
F_\nu=c_\nu Q_\nu,\quad 0<c_*\le c_\nu\le1,\quad
Q_\nu=Q_\nu^\dagger=Q_\nu^2,\quad \operatorname{rank}_{\mathbb{C}}Q_\nu=1,
$$
以及同一候选的读数和关系证书
$$
y_\nu\ge-\eta_\nu,\qquad
|y_\nu-\operatorname{Tr}(HF_\nu)|\le\tau_\nu,\quad \eta_\nu,\tau_\nu\ge0.
$$
置 $\zeta_*=\max_\nu(\eta_\nu+\tau_\nu)/c_\nu$。

有限基只给候选，不自动给 $H\ge0$。
关系残差可以通过两棵正细化树、实际缩放和同根比较取得，
但叶身份、实际操作和共同切口仍须供应。

<a id="thm:positive"></a>
#### 定理 5.2（带控制误差与异增益的有限正性）

设理想秩一方向 $P_\nu$ 构成 infidelity $\theta_0$ 覆盖：
每个单位 $u$ 都有某个 $\nu$ 使 $\operatorname{Tr}(P_uP_\nu)\ge1-\theta_0$，
其中 $0\le\theta_0\le1$。
实际方向满足 $\|Q_\nu-P_\nu\|\le r_{\rm ctrl}$，$r_{\rm ctrl}\ge0$。
置
$$
\theta=\min\{1,(\sqrt{\theta_0}+r_{\rm ctrl})^2\}.
$$
若 $d\theta<1$，则
$$
\boxed{\lambda_{\min}(H)\ge-a_p,\qquad
a_p=\frac{\zeta_*+\theta}{1-d\theta}.}
$$
令 $t=\operatorname{Tr} H_-$、$\rho=H_+/(1+t)$，则
$$
\rho\ge0,\quad\operatorname{Tr}\rho=1,\quad
\tfrac12\|H-\rho\|_1=t\le(d-1)a_p.
$$
对任何另有目标关系证书
$|y_E-\operatorname{Tr}(HE)|\le\zeta_E$ 的实际效果 $0\le E\le I$，
$$
\boxed{|y_E-\operatorname{Tr}(\rho E)|\le\zeta_E+(d-1)a_p.}
$$

**证明。**

秩一投影距离是 $\|P_u-P_v\|=\sqrt{1-|\langle u,v\rangle|^2}$；
三角不等式使实际方向成为 $\theta$ 覆盖。
除正增益得 $\operatorname{Tr}(HQ_\nu)\ge-\zeta_*$。
记最小、最大特征值为 $m,M$，迹一给 $M\le1-(d-1)m$。
在最小本征向量附近选实际覆盖方向，沿该本征向量分解，交叉项消失：
$$
-\zeta_*\le\operatorname{Tr}(HQ_\nu)
\le m+\theta(M-m)\le(1-d\theta)m+\theta.
$$
整理得最小特征值界。
至少一个特征值为正，所以 $t\le(d-1)a_p$。
$H-\rho=\frac{t}{1+t}H_+-H_-$ 的两部分支撑正交、迹均为 $t$，
故迹范数为 $2t$，所有效果上的差不超过 $t$。
最后加目标关系残差。

无需先验 $\|H\|$ 的谱步骤已在 V59 定理 5.2 中证明；
本轮接入理想到实际的方向误差、异增益和原生控制预算。
若精确关系一致性成立、一个非零秩一读口的实际轨道稠密且非负，
则全部纯方向二次型非负，得到精确 $H=\rho\ge0$。
有限菜单仍只能给上述误差或另付结构；
V59 定理 5.4 已给任意有限菜单的非正反例。[来源：v59]

<a id="lem:direction"></a>
#### 引理 5.3（模型方向误差与效果身份须分开）

在已取得 $\mathcal{J}$ 的同一实载体上，给单位 $u_0$、复酉 $U$ 和可逆实线性
$\mathsf K$。$\dagger$ 此处为实伴随；$P_v$ 表示 $\mathcal{J}$ 所定义的复射线投影。
若实算子范数满足 $\|\mathsf K-U\|\le Q$，则
$$
\|P_{\mathsf K^\dagger u_0}-P_{U^\dagger u_0}\|\le Q.
$$

**证明。**

令 $a=\mathsf K^\dagger u_0\ne0$、$b=U^\dagger u_0$，则 $\|b\|=1$，
且秩一投影距离为 $\|(I-P_a)b\|=\|(I-P_a)(b-a)\|\le Q$。

若实际来源另提供
$\|Q_\nu-P_{\mathsf K_{w_\nu}^\dagger u_0}\|\le r_{\rm cal}$
以及效果身份、正增益和同一报告对应，
可以取统一上界 $r_{\rm ctrl}=\max_\nu Q_{|w_\nu|}+r_{\rm cal}$。
不能仅由 $\mathsf K^\dagger P\mathsf K$ 的表达免费取得这些合同。

若实际目标效果 $\widetilde E_w$ 与理想效果 $E_w$ 满足
$\|\widetilde E_w-E_w\|\le\xi_w$，
且 $|y_w-\operatorname{Tr}(H\widetilde E_w)|\le\zeta_w$，同一个 $\rho$ 给
$$
\boxed{|y_w-\operatorname{Tr}(\rho E_w)|
\le\zeta_w+(d-1)\frac{\zeta_*+\theta}{1-d\theta}+\xi_w.}
$$
同一实载体上的形式回拉差满足
$\|\mathsf K_w^\dagger E\mathsf K_w-U_w^\dagger EU_w\| \le(\kappa^L+1)Q_L$；
它通常不是复效果。只有另行取得实际复效果及其与该实形式回拉的误差桥时，
才能把此预算连同桥误差并入 $\xi_w$。

### AURIC 三轴、归一化与实际增益

V59 沿用 V37 固定五模式编码。令
$$
\nu=\frac1{1+2\sqrt3+\sqrt{11}},\qquad
a_\nu=\frac{\nu(\sqrt3+\sqrt{11})}{2}.
$$
占据读出的固定标定是
$$
(X_{\rm occ},Y_{\rm occ},Z_{\rm occ})
=(a_\nu,a_\nu,\nu)+\nu\boldsymbol r,
$$
合法区域为
$$
(X_{\rm occ}-a_\nu)^2+
(Y_{\rm occ}-a_\nu)^2+
(Z_{\rm occ}-\nu)^2\le\nu^2.
$$
原秩一读口 $E_3=2\nu P_z$ 的误差必须除以实际增益 $2\nu$；
联合 $N$ 原子的乘积事件若确已取得，其增益为 $(2\nu)^N$。
$N\ge2$ 时，单个局部读口张量 $I$ 是全局高秩，不能冒充全局秩一。[来源：v59, v37]
归一化由 $\sum_sE_s=I$ 与 $p(I)=1$ 承担。
$F[\mathrm{null}]$ 的效果、完整观察者 $\Omega$ 与效果单位 $I$
不可未经类型桥认同。
三轴是特定接口的坐标；全 89 复维来源不是 qubit，
两配置角落的 Pauli 轴平方为角落投影。
原生 $d=89,610$ 载体与 $N$ 原子 $d=2^N$ 逻辑块不自动等同；
总预算须在同一载体、同一切口成立，不能以局部 qubit 标定替代全来源正性。

## 完整记录应采用什么稳定性

Quantum IV §208 保留向量、射线、跳时、垃圾与失败坐标；
§212 给固定来源的精确实复历史对应。
它们没有给跨参数完整历史的总变差连续性。[来源：qiv]

<a id="thm:graphTV"></a>
#### 定理 6.1（图测度的精确总变差）

设 $\mathcal H,\mathcal Z$ 为标准 Borel 空间，
$\mu$ 为 $\mathcal H$ 上概率，$F,G:\mathcal H\to\mathcal Z$ 可测。
保留共同基历史的增强律
$$
P_F(dh,dz)=\mu(dh)\delta_{F(h)}(dz),\quad
P_G(dh,dz)=\mu(dh)\delta_{G(h)}(dz)
$$
满足
$$
\boxed{d_{\mathrm{TV}}(P_F,P_G)=\mu\{F\ne G\},}
\qquad d_{\mathrm{TV}}(P,Q)=\sup_A|P(A)-Q(A)|.
$$

**证明。**

$F$ 的图可测，在 $P_F$ 下质量一，在 $P_G$ 下质量 $\mu(F=G)$，给下界。
共同抽取同一个 $h$ 时，两个事件指示函数只有在 $F(h)\ne G(h)$ 时才可能不同，
故任何事件的质量差不超过 $\mu(F\ne G)$。

即使两个确定向量任意接近，只要不同，保留这个精确向量坐标的两条历史律
就可由“该坐标恰等于第一向量”的事件完全区分，TV 等于一。
这不依赖守卫相切，也不需要事件数改变。
因此完整坐标继续保留，但近似比较应声明路径度量或读出类。

<a id="lem:hit"></a>
#### 引理 6.2（横截首次命中的稳定界）

设 $g,\widetilde g$ 在 $[a,b]$ 连续，
参考首次非正命中 $\tau\in(a,b)$ 满足 $g(\tau)=0$。
给 $r>0$、$[\tau-r,\tau+r]\subset(a,b)$，并假定
$$
g\ge m>0\ \text{于 }[a,\tau-r],\qquad
g'\le-\upsilon<0\ \text{于命中窗口},
$$
$$
\|\widetilde g-g\|_\infty\le\eta<\min\{m,\upsilon r\}.
$$
则扰动首次命中存在，且 $|\widetilde\tau-\tau|\le\eta/\upsilon$。

**证明。**

窗口前 $\widetilde g>0$。
窗口中在 $\tau-\eta/\upsilon$ 之前严格有 $g>\eta$，
在 $\tau+\eta/\upsilon$ 处有 $g\le-\eta$。
加扰动界及连续性，首次非正时刻只能位于这两个端点之间。

对一个有限参考事件列 $\tau_1<\cdots<\tau_K$，
要求各窗口分离且避开入口和出口，每个窗口分别满足引理 [引理（横截首次命中的稳定界）](#lem:hit)
的横截条件与误差门槛。
初配置守卫在首窗口之前有统一正裕量；
第 $k$ 次跳后配置的守卫，从第 $k$ 个窗口左端一直到下一窗口左端均有该正裕量，
末次则覆盖到脉冲终点。
再要求唯一跳边与目的守卫条件保持，逐事件归纳便给相同有序配置列和各跳时界。
这些范围保证扰动提前跳动时也不会在前一窗口内反跳或额外产生尾跳；
无事件时要求整个脉冲的当前守卫有正裕量。
用分段线性递增时间映射 $\lambda$ 对齐对应跳时，
$\|\lambda-\mathrm{id}\|_\infty\le\max_k\eta/\upsilon_k$。
若参考波动时间 Lipschitz 常数为 $M$、同刻波动误差至多 $e$，
则对齐后的波动误差至多 $e+M\max_k\eta/\upsilon_k$。

原 §207 在精确因子族 $\Psi(q,z)=\chi(q)\theta_i(z)$ 中用归一化消去同一个非零
$\chi(q)$。若归一 $\theta_i,\widetilde\theta_i$ 的距离不超过 $e$，
辅助权重差至多 $2e$；已有脉冲估计可取 $e\le12|\lambda-\alpha|$。
但横截性、接缝分离与无额外命中裕量仍需另给；
原来源允许相切和端点命中，不能把这些条件说成全来源已有。[来源：qiv]

<a id="thm:archive"></a>
#### 定理 6.3（度量误差到实际档案与报告）

给完整历史空间有界可测度量 $d_{\mathcal H}\le1$。
若两历史有共同实现满足 $\mathbb E d_{\mathcal H}(H,\widetilde H)\le e$，
每个 $L$-Lipschitz 读出 $f$ 的期望差不超过 $Le$。
若实际档案核满足
$$
d_{\mathrm{TV}}(\kappa(h,\cdot),\widetilde\kappa(\widetilde h,\cdot))
\le Ld_{\mathcal H}(h,\widetilde h)+\epsilon,
$$
输出边缘 TV 不超过 $Le+\epsilon$。
若离散报告 $R$ 有可测裕量 $\rho(h)\ge0$，且
$d_{\mathcal H}(h,\widetilde h)<\rho(h)$ 蕴含 $R(h)=R(\widetilde h)$，
则对任意 $r>0$，
$$
\boxed{d_{\mathrm{TV}}(R_*P,R_*\widetilde P)\le
P\{\rho\le r\}+\frac er.}
$$

**证明。**

前两项分别积分 Lipschitz 界和条件核的事件差。
在 $\rho(H)>r$ 且 $d_{\mathcal H}(H,\widetilde H)\le r$ 时报告相同；
失配概率至多 $P\{\rho\le r\}+P\{d_{\mathcal H}>r\}$，
再用 Markov 不等式。

因果性和可测性本身不提供这些连续性合同。
同一档案核在输入逐样本相同时可共用；输入仅近时须另给连续性。
V57 的可求和身份翻转定理对已取得持久交换记录给尾风险界，
预先保留平方概率标定，不由门前缀增长自动取得。[来源：v57]

### 已给平方最小率后的配置路径界

以下是既有概率律的扰动消费者，不参与上游平方起源证明。
Bell 型最小率的标准来源以 Hilbert 结构、Hamiltonian、配置读出及平方分布为输入。
单位取 $\hbar=1$ 时，
$$
\lambda_{\psi,H}(q\mid r)
=\frac{[2\operatorname{Im}(\overline{\psi_q}H_{qr}\psi_r)]_+}{|\psi_r|^2}.
$$
该率的物理来源和本文误差估计不能倒置成概率平方的无前提证明。[来源：bell]

<a id="prop:rates"></a>
#### 命题 6.4（安全域的率误差）

给归一 $\psi,\phi$、自伴 $H,G$，满足
$\|H\|,\|G\|\le h$、$\|\psi-\phi\|\le e_\psi$、
$\|H-G\|\le e_H$。
当前配置 $r$ 的两个分母均至少 $m>0$ 时，每条允许边满足
$$
|\lambda_{\psi,H}(q\mid r)-\lambda_{\phi,G}(q\mid r)|
\le
\frac{4he_\psi+2e_H}{m}+\frac{4he_\psi}{m^2}.
$$

**证明。**

分三项展开
$\overline{\psi_q}H_{qr}\psi_r-\overline{\phi_q}G_{qr}\phi_r$；
两个波幅项各不超过 $he_\psi$，Hamiltonian 项不超过 $e_H$，
故电流分子差至多 $4he_\psi+2e_H$。
正部函数为 1-Lipschitz，分母差至多 $2e_\psi$，另一分子至多 $2h$。
对两个商加减同一中间项即得。

无分母裕量时，取 $H=G=\sigma_x$、
$\psi_a=(a,\sqrt{1-a^2})$、
$\phi_a=(ae^{ia},\sqrt{1-a^2})$，$0<a<1$。
向量距离趋零，但从第一配置到第二配置的率差
$2\sqrt{1-a^2}\sin(a)/a$ 趋于二。
辅助相对阈值不能替代全来源绝对分母下界。

#### 命题 6.5（配置路径与有限核的误差）

对同一有限状态集合上的可测、非爆炸时变跳率，若
$$
\sup_r\sum_{q\ne r}
|\lambda_t(q\mid r)-\widetilde\lambda_t(q\mid r)|\le a(t),
$$
$a$ 可积，初始配置律 TV 为 $\delta_0$，
则保留全部配置跳时的路径律满足
$$
d_{\mathrm{TV}}(P_{\rm path},\widetilde P_{\rm path})
\le1-(1-\delta_0)e^{-\int_0^T a(t)\,dt}
\le\delta_0+\int_0^T a(t)\,dt.
$$
对标准 Borel 历史与输出空间上的有限阶段概率核，
若同一历史输入上每步 TV 差不超过 $0\le\epsilon_k\le1$，
则完整阶段输出联合律满足
$$
d_{\mathrm{TV}}(P_n,\widetilde P_n)
\le1-(1-\delta_0)\prod_{k=1}^n(1-\epsilon_k)
\le\delta_0+\sum_{k=1}^n\epsilon_k.
$$

**证明。**

先最大耦合初态。在两跳过程仍相同时，对每条边以两率的最小值共同跳，
剩余率只让一侧跳；失配风险至多 $a(t)$。
始终匹配的条件概率至少为指数因子，给第一式。
对阶段核，设此前两历史律为 $\mu,\widetilde\mu$，
其共同部分 $\rho=\mu\wedge\widetilde\mu$ 的质量为 $1-d$，
$d=d_{\mathrm{TV}}(\mu,\widetilde\mu)$。
将联合律之差分成共同部分的核差与两剩余部分。
共同部分对任意联合事件的贡献至多 $(1-d)\epsilon_k$，
剩余部分的贡献至多 $d$，故新 TV 至多 $d+(1-d)\epsilon_k$。
迭代即得乘积界，无需额外的最大耦合可测选择。

若率界只在安全域成立，还须加双方退出安全域的概率预算。
配置路径不是完整本体；加入不同的精确波动坐标后不能保留小 TV 结论，
应使用定理 [定理（图测度的精确总变差）](#thm:graphTV)--[定理（度量误差到实际档案与报告）](#thm:archive)。
失败、拒绝、垃圾、停止和缺席标签均应保留在实际输出中。

## 本轮量子起源命题与未闭合部分

本轮给不同层次的相容增加了可核查条件：
| 问题 | 本轮可证明的推进 | 仍保留的前件 |
| --- | --- | --- |
| 平方指数 | 近乘性邻近幂律；相干回返及粗事件给指数区间 | 全域对数缺陷、未归一有界、同源标定、非零旁观 |
| 共同复方向 | 小守恒缺陷锁定精确 $J$ | 实二维容量、正度量、精确等距边、根钟与阈值 |
| 相位与门字 | 邻近酉模型、整数交换及有限字预算 | 原响应形式、允许门字、相位装配条件 |
| 正量子读出 | 控制覆盖、增益和关系残差给负谱界 | 实际秩一效果、共同切口、目标报告桥 |
| 记录稳定 | 度量、横截、率或核条件给报告界 | 守卫非退化、分母安全域、档案连续性 |

平方标定得到的幂律，与轨道正性得到的矩阵读出，
须有同一实际来源的共同标定和报告对应才能作为同一物理概率。
精确极限 $\epsilon_w=d_r=\eta=0$ 在声明函数类内恢复平方；
$\delta=\tau=0$ 恢复原生精确 $J$；
稠密实际轨道与精确关系一致性恢复正密度矩阵。
数学极限不表示有限观察者已取得全部极限操作。

共同复方向、复合系统共同中心扇区、局部两配置 Pauli 三轴是不同层次。
二维定向刚性不自动证明一般张量复合、CP 仪器、物理三维空间、
Hamiltonian 内容或钟率与引力的关系。
唯一 $\Omega$ 不强迫记录秩一，也不强迫每个有限接口纯；
相同酉变换保持完整态距离，不自动使预测误差收缩。
本轮未证明候选前件的逻辑最小性、独立性或自然界必然性。

可以准确提出的命题是：
> 在一个固定本体的内部关系接口上，非退化和共同标定使近似关系具有刚性。
> 二维实守恒缺陷可锁定共同虚单位；乘性缺陷与相干旁观比较可稳定约束平方指数；
> 足够可达的非负秩一读出可认证同一个近正矩阵响应。
> 配合适当的守卫、率或读出合同，可将相应误差传到已声明的档案和报告。

## 固定来源与文献

> **编者归属说明（来源报告）。** 以下文献条目中的“本轮”“上轮”“此前核读”、取得时刻、固定身份、公开扫描及审查范围，均保留为 V64 原作者在原稿写作轮次的报告；它们不转化为 Markdown 整理者的取得、阅读或全来源认证声明。

<a id="bib-head"></a>
### 来源 `head`
The Omega Institute, *trureturing*,
[本轮固定提交](https://github.com/the-omega-institute/trureturing/commit/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b)。
唯一活动 HEAD 取得于 2026-11-01 04:53:44.991702 Asia/Singapore。
来源下载与身份核对不是全库数学认证。

<a id="bib-v49"></a>
### 来源 `v49`
The Omega Institute,
[V49: Sum--Product Powers, Quadratic Relation Closure and Normalized Lifting](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md)，
新 §§13--16 全部追加原文核读。精确标定沿用其定理 13.3；
近似乘性及射影条件数为本文补出的条件连接。

<a id="bib-v59"></a>
### 来源 `v59`
The Omega Institute,
[V59: Local Tomography, Coherent Readout Orbits and Quantum Positivity Origin](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md)，
本轮连续核读全部 1400 行，保留历史报告归属。
定理 3.3、5.2--5.4 与第 7 节是本文主要接口。

<a id="bib-qiv"></a>
### 来源 `qiv`
The Omega Institute,
[Quantum Principles and Coherent Reconstruction, Continuation IV](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md)，
固定身份相对 v63 未变。§§209--213 承接上轮核读；
本轮历史伴随审查核读 §§206--208、212--213。
原平方率、归一守卫、创新及报告合同不由稳定估计消除。

<a id="bib-v57"></a>
### 来源 `v57`
The Omega Institute,
[V57: Fixed Ontic State, Growing Observer, Stable Self, Internal Prediction and Relative Clocks](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_FIXED_ONTIC_STATE_GROWING_OBSERVER_STABLE_SELF_INTERNAL_PREDICTION_AND_RELATIVE_CLOCKS_V57.md)，
本轮来源审查全文，正文采用定义 5.2、定理 5.3 的持久记录条件。

<a id="bib-v58"></a>
### 来源 `v58`
The Omega Institute,
[V58: Relational Axioms, Common Complex Phase and Conditional Quantum Reconstruction](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md)，
本轮来源审查全文。其中心胶合预给精确 Clifford 结构，
不等于本文近守恒的二维定向刚性。

<a id="bib-v37"></a>
### 来源 `v37`
The Omega Institute,
[V37: Binary Relations, Unitary Representation and Golden Gate Universality](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)，
固定五模式编码沿用此前核读，并由本轮 V59 §7 交叉核对。

<a id="bib-hyers"></a>
### 来源 `hyers`
D. H. Hyers, *On the Stability of the Linear Functional Equation*,
Proceedings of the National Academy of Sciences **27**(4), 222--224 (1941).
[doi:10.1073/pnas.27.4.222](https://doi.org/10.1073/pnas.27.4.222).
本轮在 PMC 公开扫描逐页核读 222--224，特别是 Theorem 1 的倍增极限。
本文乘群版本自行完整证明，不把标准工具作为新发现。

<a id="bib-barnum"></a>
### 来源 `barnum`
H. Barnum and A. Wilce,
*Local tomography and the Jordan structure of quantum theory*,
[arXiv:1202.4513v2](https://arxiv.org/abs/1202.4513).
本轮核对官方摘要的 Jordan、复合、局部层析与 qubit 前件，
不以摘要代替全文证明。

<a id="bib-bell"></a>
### 来源 `bell`
D. Dürr, S. Goldstein, R. Tumulka, N. Zanghì,
*Bell-Type Quantum Field Theories*,
Journal of Physics A **38**, R1--R43 (2005),
[doi:10.1088/0305-4470/38/4/R01](https://doi.org/10.1088/0305-4470/38/4/R01).
本轮核读作者公开稿 §2.6 式 (22) 与 §2.7 的输入；
用于最小率定位。本文扰动界自足，不用该率反证其自身平方概率前提。

**方法说明。**
数学均为纸面推导和反例检查，未运行数学程序、CAS、数值实验、枚举、
Lean 或门搜索。程序仅用于来源取得、文本及身份核对、文档编译和版面检查。
本轮未修改项目仓库、PR 或外部消息；
表示存在、有限证书、实际取得与自然界适用性分别陈述。

> **编者归属说明（方法报告）。** 上述未运行数学程序、未修改项目仓库、PR 或外部消息等陈述，归属于 V64 原作者的原稿写作轮次；它们不是 Markdown 整理工作的行为报告。

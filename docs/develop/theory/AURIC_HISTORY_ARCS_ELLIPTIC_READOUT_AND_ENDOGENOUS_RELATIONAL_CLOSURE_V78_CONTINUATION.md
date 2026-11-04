# 历史圆弧、椭圆读出与内生关系闭合

**AURIC v78 续推：定义、定理与证明**

研究续稿

2026 年 11 月 1 日

<details>
<summary>原始 TeX 前导、生产设置与题名元数据（逐字保留）</summary>

```latex
% !TEX program = xelatex
% Compile twice with XeLaTeX. Uses ctex when installed; otherwise Noto Serif CJK SC.
% Font fallback: fonts/NotoSerifCJKsc-Regular.otf from https://github.com/notofonts/noto-cjk
\documentclass[11pt,a4paper]{article}
\usepackage[margin=24mm,headheight=16pt]{geometry}
\IfFileExists{ctex.sty}{\usepackage[UTF8,fontset=auto]{ctex}}{
  \usepackage{fontspec}
  \IfFontExistsTF{Noto Serif CJK SC}{\setmainfont{Noto Serif CJK SC}[AutoFakeBold=1.7]}{\setmainfont{NotoSerifCJKsc-Regular.otf}[Path=fonts/,AutoFakeBold=1.7,AutoFakeSlant=.15]}
  \XeTeXlinebreaklocale "zh"
  \XeTeXlinebreakskip=0pt plus 1pt
}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{graphicx,tikz,xcolor,booktabs,array,tabularx,longtable}
\usepackage{fancyhdr,enumitem,hyperref}
\definecolor{ink}{HTML}{17384A}
\definecolor{accent}{HTML}{007D86}
\hypersetup{colorlinks=true,linkcolor=ink,urlcolor=accent,citecolor=ink,pdftitle={AURIC v78 续推：历史圆弧、椭圆读出与内生关系闭合}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC / v78 续推研究稿}
\fancyhead[R]{\small 历史、几何与关系闭合}
\fancyfoot[C]{\thepage}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{4pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\renewcommand{\baselinestretch}{1.12}
\renewcommand{\contentsname}{目录}
\renewcommand{\abstractname}{摘要}
\renewcommand{\refname}{资料与可复核位置}
\renewcommand{\proofname}{证明}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{remark}[definition]{说明}
\newcommand{\ip}[2]{\langle #1,#2\rangle}
\newcommand{\norm}[1]{\left\lVert #1\right\rVert}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\id}{I}
\newcommand{\tr}{\operatorname{Tr}}
\newcommand{\Span}{\operatorname{span}}
\newcommand{\FS}{\mathrm{FS}}
\newcommand{\sgn}{\operatorname{sgn}}
\newcommand{\plain}[1]{\par\noindent\textbf{白话图景。}#1\par}
\title{\color{ink}\bfseries 历史圆弧、椭圆读出\protect\\与内生关系闭合\protect\\[5pt]\large AURIC v78 续推：定义、定理与证明}
\author{研究续稿}
\date{2026 年 11 月 1 日}
\begin{document}
\maketitle
```

</details>



## 摘要

本稿以已实际读取的 v78 原对话为基线，保留其完整历史复正核、可逆保核接续、完整标架相容，以及 Born 读数的同根校准与准备协变条件。新增结果分为三条相互接续的链：第一，历史切向与目标切向的二元失配，其积分精确等于路径超出最短距离的长度；第二，恒测地曲率给球面圆，历史平面读出给椭圆，变曲率则给可稳定接续的局部椭圆族；第三，三段近邻历史的二阶 Schur 余量判定二态载体闭合，恒定生成元分支中进一步得到两能级条件与椭圆偏心率的谱矩表达。

在项目的原生双壁模型中，另证明底部二态球面的水平提升由现有控制律给出；完整圆周的参考相位等于半个有向立体角，并由椭圆的带符号偏心参数确定。这使“历史仍在同一个整体内部”成为已有读口可检测的关系。本稿作为 v78 的后续研究，给出新增定理的解析证明；相应的项目形式化工作仍待完成。

<details>
<summary>原始目录与分页设置（逐字保留）</summary>

```latex
\setcounter{tocdepth}{1}
{\small\setlength{\parskip}{0pt}\tableofcontents}
\newpage
```

</details>

**目录**

1. [基线、记号与本轮真正增加的内容](#section-1)
2. [当前方向与目标方向：多走的路来自哪里](#section-2)
3. [圆弧与椭圆：直观怎样变成准确命题](#section-3)
4. [平滑延续：为什么需要一族移动的椭圆](#section-4)
5. [二阶历史余量：这个球为什么能一直用](#section-5)
6. [恒定内部门流：椭圆偏心率由谱关系决定](#section-6)
7. [回到项目：原生双壁模型的球面与历史相位](#section-7)
8. [反着推公理：撤去哪个条件，哪一对关系先失配](#section-8)
9. [更简洁的量子约束：可压缩到哪里](#section-9)

<a id="section-1"></a>

## 1. 基线、记号与本轮真正增加的内容

原对话 v78 的文件名为



`AURIC_v78_Gate_Manifolds_Tangent_Kernels_Integrable_Recursion_ZH.tex`。

本稿已读取该轮完整正文，继承其中以下事实：近邻历史的一阶 Schur 余量产生切向复核；完整门标架满足 Maurer--Cartan 相容；有序积分保存先后次序；完整正核与可逆保核接续重构 Hilbert 表示；效果仿射性本身只选出某个密度矩阵，必须再用同根校准和准备协变绑定到同一个 $\Omega$。

本轮核对的项目固定提交为

`7878c7ff9b75b9cb49dd84f440e15fd65f2dc665`。

直接使用 Phase 原稿与 continuation 中的双壁源、原生命令、合法域和未来商；其确切位置列在文末。项目原有公式与本稿新推导分开陈述。新增定理采用通常数学证明，未执行相应 Lean 形式化验证。

全文内积对第二变量线性。球面几何使用单位 Bloch 球 $S^2$；常用 Fubini--Study 约定为

$$
ds_{\mathrm{FS}}^2=\left\lVert d\psi\right\rVert^2-|\langle \psi,d\psi\rangle|^2=\tfrac14\left\lVert dr\right\rVert^2.
$$

因此球面长度等于相应二态 FS 长度的两倍。项目的控制成本另有定义，不与此混同。为避免符号冲突，球面曲率记 $k$，项目原来的概率坐标 $\kappa$ 改记 $\lambda$，相位中间变量记 $\alpha,\beta$。

**定义 1.1（二态载体与状态球）**

在已经重构的复 Hilbert 空间中，取固定二维复子空间 $L$。其归一向量除去共同相位后形成 $\mathbb{CP}^1$。选定正交基后，纯态投影写为

$$
\rho=\tfrac12(I+r\cdot\sigma),\qquad r\in S^2.
$$

这就是本文的状态球。它描述一个二态关系载体，不预先限制整个 $\Omega$ 的维数。

任意两个非共线纯态确实张成一个这样的载体，但整段历史未必留在其中。第 [5](#sec-schur)节给出可以直接从历史核检验的闭合条件。

<a id="section-2"></a>

## 2. 当前方向与目标方向：多走的路来自哪里

**定义 2.1（历史标架与目标方向）**

设 $r(s)$ 为单位速 $C^2$ 球面曲线。定义

$$
u=r',\qquad b=r\times u,\qquad F=(r,u,b)\in SO(3).
$$

固定目标 $q\in S^2$。在 $r\ne\pm q$ 时，定义

$$
d=\arccos(r\cdot q),\qquad
w=\frac{q-(q\cdot r)r}{\sin d}.
$$

$w$ 是从当前点朝目标走最短路的单位切向。令

$$
w=\cos\eta\,u+\sin\eta\,b.
$$

于是 $\eta$ 比较的是“历史当前怎么走”和“现在最短该怎么走”。

<a id="thm-excess"></a>

**定理 2.2（长度超额的精确二元表达）**

设 $r:[0,\ell]\to S^2$ 单位速，$r(0)=p,r(\ell)=q$，内部点避开 $q,-q$。则

$$
\boxed{
\ell-d(p,q)=\int_0^\ell(1-\cos\eta)\,ds
=\frac12\int_0^\ell\left\lVert u-w\right\rVert^2\,ds.}
\tag{1}
$$

**证明。**

在内部求导得到

$$
d'=-\frac{r'\cdot q}{\sqrt{1-(r\cdot q)^2}}=-u\cdot w=-\cos\eta.
$$

球面距离沿单位速曲线是 $1$-Lipschitz 函数，故绝对连续。积分并令端点趋于 $0,\ell$，利用 $d(\ell)=0$，得 $d(p,q)=\int_0^\ell\cos\eta\,ds$。再由两个向量均为单位向量，$\left\lVert u-w\right\rVert^2=2-2u\cdot w$，即得结论。

∎

途中经过奇点时，可以分段讨论。这里的失配成本不要求任何额外的经验概率假设。若历史初始方向与唯一的目标最短方向不同，连续性使初始一段的失配积分严格为正。历史造成的绕行不是一句定性判断，而是可累积的精确余量。

**命题 2.3（方向关系的三轴读出）**

切平面使用复结构 $J_rx=r\times x$，定义

$$
h_r(v,w)=v\cdot w+i\,r\cdot(v\times w).
$$

则 $h_r(u,w)=e^{i\eta}$。将对应二元 Gram 矩阵按 v78 的交叉项约定归一，得到

$$
(X,Y,Z)=(\cos\eta,\sin\eta,0),\qquad X^2+Y^2+Z^2=1.
$$

因此定理 [2.2](#thm-excess)也写成 $\ell-d(p,q)=\int(1-X)ds$。

**证明。**

$b=r\times u$，故 $u\cdot w=\cos\eta$，$r\cdot(u\times w)=\sin\eta$。二元复 Gram 的迹为二、秩为一，直接归一即可。若改用标准 Pauli 密度矩阵约定，则对该 Gram 取复共轭以保持 $Y=+\sin\eta$；$X$ 和长度恒等式均不受影响。

∎

此处复结构来自已建立的二态量子几何，不从长度公式重新推出复数或 Born 法则。

<a id="prop-target"></a>

**命题 2.4（目标、方向与转向的共同方程）**

定义有向测地曲率 $k=u'\cdot b$。则

$$
r'=u,\qquad u'=-r+kb,\qquad b'=-ku,
$$

而目标关系满足

$$
\boxed{d'=-\cos\eta,\qquad \eta'=\cot d\,\sin\eta-k.}
\tag{2}
$$

**证明。**

对 $\left\lVert r\right\rVert=\left\lVert u\right\rVert=1,r\cdot u=0$ 求导，得 $u'\cdot r=-1,u'\cdot u=0$，于是 $u'=-r+kb$；对 $b=r\times u$ 求导得第三式。令 $x=q\cdot r,y=q\cdot u,z=q\cdot b$，便有 $x'=y,y'=-x+kz,z'=-ky$。代入 $x=\cos d,y=\sin d\cos\eta,z=\sin d\sin\eta$，即得目标方程。

∎

**白话图景。**位置说明离目标多远，历史切向说明现在朝哪里走，曲率说明方向怎样转。这三个量互相约束。实际轨迹仍需由内部控制或动力学选定；这组几何恒等式不会自动替系统选择一条未来。

<a id="section-3"></a>

## 3. 圆弧与椭圆：直观怎样变成准确命题

欧氏切线 $p+tu$ 与单位球仅交于 $p$。因此“目标在历史切线上”应精确改成“目标在历史测地平面 $\operatorname{span}_{\mathbb{R}}\{p,u\}$ 内”，并另外区分正向与反向。

<a id="thm-circle"></a>

**定理 3.1（经过目标的唯一有向历史圆）**

给定 $p,q\in S^2$、$q\ne p$，以及历史单位切向 $u\perp p$。令 $b=p\times u$。在球面圆这一类曲线中，经过 $p,q$ 且在 $p$ 处以 $u$ 为正向的圆唯一，其有向测地曲率为

$$
\boxed{k=\frac{b\cdot q}{1-p\cdot q}.}
\tag{3}
$$

该圆所在平面为

$$
(b+kp)\cdot r=k.
\tag{4}
$$

若记 $h=\sqrt{1+k^2}$，单位速参数式为

<a id="eq-circle"></a>

$$
r(s)=\frac{k^2+\cos(hs)}{h^2}p+
\frac{\sin(hs)}h u+
\frac{k(1-\cos(hs))}{h^2}b.
\tag{5}
$$

**证明。**

圆平面的法向与初始切向 $u$ 正交，所以可写为 $ap+cb$。由于平面通过 $p$，方程为 $a(p\cdot r)+c(b\cdot r)=a$。若 $c=0$，该平面与球只交于 $p$，不能经过 $q\ne p$。因此可除以 $c$ 并令 $k=a/c$，得到 $b\cdot r=k(1-p\cdot r)$。代入 $q$ 给出唯一 $k$。式 [(5)](#eq-circle)直接满足该平面、单位球和 $r(0)=p,r'(0)=u,\left\lVert r'\right\rVert=1$。再代入标架方程即验证曲率为 $k$。

∎

对 $q\ne\pm p$，若目标方位角为 $\eta_0$，则

$$
q=\cos d_0\,p+\sin d_0(\cos\eta_0\,u+\sin\eta_0\,b),
\qquad k=\cot(d_0/2)\sin\eta_0.
$$

这是目标偏离历史方向与所需弯曲量之间的直接关系。

**推论 3.2（首次到达、长弧与退化情形）**

记 $x=p\cdot q,y=u\cdot q$，取 $\phi\in(0,2\pi)$ 满足

$$
\cos\phi=(1+k^2)x-k^2,\qquad \sin\phi=\sqrt{1+k^2}\,y.
$$

沿指定方向首次到达的长度为 $\ell=\phi/\sqrt{1+k^2}$。

若 $q=-p$，则 $k=0,\ell=\pi$；若 $q=p$，则不能唯一确定圆。

当 $b\cdot q=0$ 时圆为大圆，但只有 $u\cdot q>0$ 时是朝目标的短弧；$u\cdot q<0$ 时顺着历史方向到达的是长弧。额外绕圈还会增加整周长度。

<a id="thm-ellipse"></a>

**定理 3.3（历史平面中的椭圆）**

在固定历史平面中读出 $X=p\cdot r,Y=u\cdot r$。定理 [3.1](#thm-circle)的球面圆满足

$$
\boxed{X^2+Y^2+k^2(1-X)^2=1.}
\tag{6}
$$

令 $c=k/\sqrt{1+k^2}\in(-1,1)$，则椭圆中心、半短轴、半长轴、偏心率分别为

$$
\boxed{(c^2,0),\quad 1-c^2,\quad \sqrt{1-c^2},\quad e=|c|.}
\tag{7}
$$

**证明。**

第三个正交分量为 $b\cdot r=k(1-X)$。三个分量平方和为一，得到椭圆方程。完成平方得

$$
\frac{(X-c^2)^2}{(1-c^2)^2}+\frac{Y^2}{1-c^2}=1.
$$

由半轴定义直接得到偏心率 $e^2=1-(1-c^2)=c^2$。

∎

**白话图景。**球上保持恒定转弯量，走的是一个圆。把它从历史平面看过去，才读出椭圆。目标偏出历史测地平面时，这个圆是小圆；目标在平面内时，它退化为大圆，投影成为正圆。这里“恒定转弯量”和“采用历史平面读出”都是命题的一部分。

```latex
\begin{center}
\begin{tikzpicture}[scale=2]
\draw[gray!45] (0,0) circle (1);
\draw[gray!60,dashed,domain=0:360,samples=140] plot ({.819152*cos(\x)+.573576*sin(\x)},{-.286788*cos(\x)+.409576*sin(\x)});
\draw[accent,thick,domain=0:360,samples=160] plot ({.819152*(.81+cos(\x))/1.81+.573576*sin(\x)/sqrt(1.81)},{-.286788*(.81+cos(\x))/1.81+.409576*sin(\x)/sqrt(1.81)+.866025*.9*(1-cos(\x))/1.81});
\fill[ink] (.819152,-.286788) circle (.025);
\node[below right,font=\small] at (.819152,-.286788) {$p$};
\node[font=\small] at (0,-1.3) {球面圆：$k=0.9$};
\begin{scope}[shift={(2.7,0)}]
\draw[gray!45,->] (-1.08,0)--(1.15,0) node[right,font=\small] {$X$};
\draw[gray!45,->] (0,-1.08)--(0,1.15) node[above,font=\small] {$Y$};
\draw[gray!60,dashed] (0,0) circle(1);
\draw[accent,thick,domain=0:360,samples=160] plot ({(.81+cos(\x))/1.81},{sin(\x)/sqrt(1.81)});
\fill[ink] (1,0) circle(.025);
\node[below right,font=\small] at (1,0) {$p$};
\node[font=\small] at (0,-1.3) {同一圆在历史平面的椭圆读出};
\end{scope}
\end{tikzpicture}
\end{center}
```

普通偏心率只给 $|c|$。要重建转向，须保留 $c$ 的符号，因为 $k=c/\sqrt{1-c^2}$。$k$ 与 $-k$ 具有相同的无向椭圆方程，却代表不同的有向历史。

**椭圆积分与两种弧长。**

令 $a=\sqrt{1-c^2}$，以圆周角 $\phi$ 表示投影：$X=c^2+a^2\cos\phi,Y=a\sin\phi$。则在递增角区间上

$$
\ell_{\mathrm{proj}}=a\int_{\phi_0}^{\phi_1}\sqrt{1-e^2\sin^2\phi}\,d\phi
=a\{E(\phi_1,e)-E(\phi_0,e)\},\quad e=|c|,
$$

其中 $E$ 是第二类不完全椭圆积分 [7](#ref-dlmf)。同一段的球面弧长为 $\ell_{S^2}=a(\phi_1-\phi_0)$。这些公式由两条参数曲线直接求速率得到，显示二维椭圆读出的长度一般小于球面路径长度。

<a id="section-4"></a>

## 4. 平滑延续：为什么需要一族移动的椭圆

**定理 4.1（二阶接续条件与局部圆轴）**

两段单位速球面曲线在接点已有相同位置与切向，则它们 $C^2$ 接续当且仅当测地曲率相同。若曲率 $k$ 为 $C^1$，一般轨迹的局部圆轴 $a=b+kr$ 满足

$$
\boxed{a'=k'r,\qquad
\left\lVert\left(\frac{a}{\sqrt{1+k^2}}\right)'\right\rVert
=\frac{|k'|}{1+k^2}.}
\tag{8}
$$

因此 $k$ 恒定恰好意味着圆轴固定。

**证明。**

接点处二阶导数为 $r''=-r+kb$，故结论成立。又 $b'=-ku,r'=u$，于是 $(b+kr)'=k'r$。归一后求导为 $k'(r-kb)/(1+k^2)^{3/2}$，取范数得到第二式。

∎

给定目标、当前点和历史切向，只在“选恒曲率圆”这一类中确定唯一连接。若目标要求的 $k$ 不等于过去末端的曲率，直接接该圆只能保持 $C^1$。要求加速度也连续时，需要曲率过渡段。有限段不同曲率圆的简单拼接，不能同时是 $C^2$。

<a id="thm-stability"></a>

**定理 4.2（带符号椭圆族的重构与稳定性）**

给定初始标架 $F_0\in SO(3)$ 和连续函数 $k(s)$，方程

$$
F'=F A_k,\qquad
A_k=\begin{pmatrix}0&-1&0\\1&0&-k\\0&k&0\end{pmatrix}
$$

唯一重构单位速 $C^2$ 球面轨迹。对相同初始标架和相同弧长区间上的两条曲率函数，

$$
\boxed{d_{SO(3)}(F_1(S),F_2(S))
\le\int_0^S|k_1-k_2|\,ds.}
\tag{9}
$$

其中 $d_{SO(3)}$ 为旋转角距离。若 $k$ 为 $M$-Lipschitz，用冻结曲率 $k(0)$ 的圆 $r_c$ 局部逼近，则

$$
\boxed{\left\lVert r(h)-r_c(h)\right\rVert\le\frac{Mh^3}{6}.}
\tag{10}
$$

**证明。**

线性 ODE 给唯一解。$A_k$ 反对称，故 $F$ 始终正交且行列式保持一。其第一列满足标架方程。

设 $Q=F_2F_1^{\mathsf T}$。则

$$
Q'=Q(k_2-k_1)[r_1]_\times,
$$

故相对旋转角速度为 $|k_2-k_1|$。旋转距离不超过路径长度，得到稳定界。

冻结曲率时，在 $s$ 处的标架轴差不超过 $\int_0^s|k(t)-k(0)|dt\le Ms^2/2$。对 $r'=u$ 再积分，得 $Mh^3/6$。

∎

若使用带符号偏心参数 $c(s)$，在 $`|c|\le c_*<1`$ 的区间上，

$$
d_{SO(3)}(F_1(S),F_2(S))
\le (1-c_*^2)^{-3/2}\int_0^S|c_1-c_2|ds.
$$

这来自 $k(c)=c/\sqrt{1-c^2}$ 的导数。因而“初始标架、带符号椭圆参数、弧长、次序”是该几何模型的一组充分历史资料。椭圆形状单独不足。

**命题 4.3（交换两段圆弧会产生第三方向）**

设两段小弧长度均为 $h$，曲率分别为 $k_1,k_2$，每段传递整个标架。则

$$
[A_{k_1},A_{k_2}]=(k_2-k_1)[e_2]_\times,
$$

$$
r_{12}-r_{21}=-(k_2-k_1)h^2b_0+O(h^3).
$$

**证明。**

由 $A_k=[(k,0,1)]_\times$ 及 $[[a]_\times,[b]_\times]=[a\times b]_\times$ 得第一式。展开两个指数乘积到二阶，再作用于初始第一列 $e_1$，得到第二式。

∎

这与 v78 “先后次序留下第三方向”的机制一致。这里比较的是传递完整历史标架的圆弧接续，不能把标架每次重置成相同坐标。

**说明 4.4（平滑本身不决定未来）**

取 $k_1(s)=0$，而 $k_2(s)=0$ 对 $s\le0$、$k_2(s)=e^{-1/s^2}$ 对 $s>0$。两者具有完全相同的过去和接点全部阶导数，却给不同未来。若要唯一预测未来，仍须指定内部记忆如何决定后续控制。还须把几何弧长与实际内部钟区分：物理时间的生成律另含 $v=ds/dt$。

<a id="sec-schur"></a>

<a id="section-5"></a>

## 5. 二阶历史余量：这个球为什么能一直用

本节把 v78 的一阶切向 Schur 余量推进到二阶。新增正则性要求为重构历史路径 $\psi\in C^2$；仅有 $C^1$ 不够。

**定义 5.1（二态载体之外的二阶余量）**

设 $\left\lVert \psi(t)\right\rVert=1$，

$$
v^2=\left\lVert \psi'\right\rVert^2-|\langle \psi,\psi'\rangle|^2>0,
\quad L_t=\operatorname{span}_{\mathbb{C}}\{\psi,\psi'\},\quad P_t=\operatorname{proj}_{L_t}.
$$

定义 $\eta=(I-P_t)\psi''$ 和 $R=\left\lVert \eta\right\rVert^2$。这里 $v$ 是射线速度；$R$ 测量加速度离开当前二态载体的部分。

**定理 5.2（二阶 Gram--Schur 等式）**

令 $A=\operatorname{Gram}(\psi,\psi')$，

$z=(\langle \psi,\psi''\rangle,\langle \psi',\psi''\rangle)^{\mathsf T}$。则

$$
\boxed{R=\left\lVert \psi''\right\rVert^2-z^*A^{-1}z\ge0,\qquad
\det\operatorname{Gram}(\psi,\psi',\psi'')=v^2R.}
\tag{11}
$$

**证明。**

令 $E$ 的两列为 $\psi,\psi'$，则 $`P=E(E^*E)^{-1}E^*=EA^{-1}E^*`$。代入 $\left\lVert (I-P)\psi''\right\rVert^2$ 即得第一式；第二式为块行列式公式，且 $\det A=v^2$。

∎

**定理 5.3（三段有限历史的四阶余量）**

令 $\psi_j=\psi(t+jh)$，$A_h=\operatorname{Gram}(\psi_0,\psi_1)$，

$$
b_h=(\langle \psi_0,\psi_2\rangle,\langle \psi_1,\psi_2\rangle)^{\mathsf T},
\qquad S_h=1-b_h^*A_h^{-1}b_h.
$$

对充分小的非零 $h$，$A_h$ 可逆，而且

$$
\boxed{S_h/h^4\longrightarrow R(t),\qquad
\det\operatorname{Gram}(\psi_0,\psi_1,\psi_2)/h^6\longrightarrow v^2R.}
\tag{12}
$$

**证明。**

记 $P_h$ 为前两态张成空间的投影。差商 $(\psi_1-\psi_0)/h\to\psi'$ 与 $v>0$ 保证 $P_h\to P$，并有 $\det A_h/h^2\to v^2$。又

$$
D_h=(\psi_2-2\psi_1+\psi_0)/h^2\to\psi'',
\quad S_h/h^4=\left\lVert (I-P_h)D_h\right\rVert^2.
$$

取极限即得首式；再用块行列式公式得次式。

∎

所有输入均为三个历史的交叉核。小 $h$ 时直接相减会有数值消减，估计精度并不会因 $h$ 缩小而自动提高。

**定理 5.4（固定二态球的充要条件与漂移预算）**

在连通区间上假定 $v>0$，令

$e_1=(\psi'-\langle \psi,\psi'\rangle\psi)/v$。则

$$
P'=(|\eta\rangle\langle e_1|+|e_1\rangle\langle\eta|)/v,
\quad \left\lVert P'\right\rVert_{\mathrm{op}}=\sqrt R/v.
$$

因此

$$
\boxed{R\equiv0\ \Longleftrightarrow\ L_t\text{ 固定},\qquad
\left\lVert P_t-P_s\right\rVert_{\mathrm{op}}\le\int_s^t\frac{\sqrt R}{v}\,d\tau.}
\tag{13}
$$

**证明。**

以 $(\psi,e_1)$ 为 $L_t$ 的正交标架。第一列导数没有载体外分量，第二列导数的载体外分量为 $\eta/v$。对 $P=|\psi\rangle\langle\psi|+|e_1\rangle\langle e_1|$ 求导，内部反 Hermitian 连接的贡献相消，剩余上述算子。其非零特征值为 $\pm\left\lVert \eta\right\rVert/v$。积分即可。

∎

单点 $R=0$ 通常只给该点二阶闭合。零速点也必须单列：一条无限阶平坦路径可在零速点从 $\operatorname{span}(e_0,e_1)$ 光滑换到 $\operatorname{span}(e_0,e_2)$。所以不能删去全区间和正则速度条件。

**白话图景。**先用当前态和当前变化建立一个二态球，再问下一阶变化是否长出了球外的新方向。长出的部分恰好就是 $R$。它为零才说明这一个球能继续完整承载历史；它不为零就必须扩大载体或显式保留球的移动。

<a id="section-6"></a>

## 6. 恒定内部门流：椭圆偏心率由谱关系决定

<a id="thm-spectral"></a>

**定理 6.1（二阶闭合与两能级支持）**

设 $\psi'=-iH\psi$，$H$ 为固定有限维自伴矩阵，采用 $\hbar=1$，且 $v>0$。则以下条件等价：

1. $R=0$；

2. $H^2\psi\in\operatorname{span}\{\psi,H\psi\}$；

3. $\operatorname{span}\{\psi,H\psi\}$ 为 $H$-不变子空间；

4. $\psi$ 恰好支持在两个不同能级上。

因此固定 $H$ 时，单点二阶闭合足以保证整条轨道处于固定二态球。

**证明。**

$\psi''=-H^2\psi$ 给出前两个条件等价。$H\psi$ 已在二态载体内，故第二、第三条件等价。若第二条件成立，则某个二次多项式 $f$ 满足 $f(H)\psi=0$；在 $\psi$ 有非零分量的每个谱点上，$f$ 必须为零，所以谱支持至多两个。$v>0$ 排除单一能级。反之，若支持于 $E_+,E_-$，则 $(H-E_+I)(H-E_-I)\psi=0$，得到闭合。$H$-不变性又保证全部指数 $e^{-itH}$ 保持此空间。

∎

<a id="thm-moments"></a>

**定理 6.2（闭合条件与椭圆的内生矩表达）**

令 $M=H-\langle \psi,H\psi\rangle I$，$\mu_j=\langle \psi,M^j\psi\rangle$，$\mu_2>0$。则

$$
\boxed{R=\mu_4-\mu_2^2-\frac{\mu_3^2}{\mu_2}\ge0.}
\tag{14}
$$

当等号成立时，沿正时间定向的历史圆曲率和投影椭圆偏心率为

$$
\boxed{k=-\frac{\mu_3}{2\mu_2^{3/2}},\qquad
e=\frac{|\mu_3|}{\sqrt{\mu_3^2+4\mu_2^3}}.}
\tag{15}
$$

**证明。**

$\psi$ 与 $M\psi$ 正交，而 $P(M^2\psi)=\mu_2\psi+(\mu_3/\mu_2)M\psi$。平方范数相减得到 $R$。

等号成立时应用定理 [6.1](#thm-spectral)。设高、低能级权重为 $p,q>0$，$p+q=1$，能隙为 $\Delta>0$。则

$$
\mu_2=pq\Delta^2,\qquad \mu_3=pq(q-p)\Delta^3.
$$

以高能级方向为 Bloch 轴 $n$，轨道满足 $n\cdot r=c=p-q$；其半径为 $a=2\sqrt{pq}$，单位速切向为 $u=n\times r/a$。于是 $b=(n-cr)/a$，故 $n=a(b+kr)$、$k=c/a$。定理 [3.3](#thm-ellipse)给 $e=|c|$。代入中心矩即得所述公式。

∎

还可恢复

$$
\Delta=\frac{\sqrt{\mu_3^2+4\mu_2^3}}{\mu_2},\quad
p=\frac12\left(1-\frac{\mu_3}{\sqrt{\mu_3^2+4\mu_2^3}}\right),\quad q=1-p.
$$

椭圆的半长轴为 $2\sqrt{pq}$，半短轴为 $4pq$，偏心率为 $|p-q|$。

这些权重首先是重构空间中的谱投影平方范数；调用 v78 的同根校准与准备协变后，它们才同时获得对应谱效果的实验概率解释。

**白话图景。**这一分支中，椭圆不用再作为外加公理：完整核重构内部门流，二阶余量确认只涉及两个能级，这两个分量的不平衡就决定椭圆有多扁。等权时是大圆；极端单能级时射线静止，不能继续使用除以速度的公式。

<a id="sec-native"></a>

<a id="section-7"></a>

## 7. 回到项目：原生双壁模型的球面与历史相位

本节源模型与命令公式来自固定项目 Phase 文档；从该模型识别二态球、水平提升及椭圆相位关系，是本稿的进一步推导。

### 7.1 同一个原生源中，球面与参考相位各在哪里

项目双壁条件为 $X=Y=r/2$，其中 $r=1-Z$、$0<Z<1$，记 $L=r/2$。去掉固定准备相位后，原生五模态为

$$
\Psi=(\sqrt\lambda e^{-iu},\sqrt{L-\lambda}e^{-iv},\sqrt Z,
\sqrt{L-\lambda}e^{-iv},\sqrt\lambda e^{-iu}),\quad 0<\lambda<L.
$$

令 $|a\rangle=(|0\rangle+|13\rangle)/\sqrt2$、$|b\rangle=(|1\rangle+|3\rangle)/\sqrt2$、$|m\rangle=|2\rangle$，则

$$
\Psi=\sqrt r\,z+\sqrt Z\,|m\rangle,
\quad z=e^{-i\beta}\bigl(\sqrt p\,|a\rangle+\sqrt{1-p}e^{i\alpha}|b\rangle\bigr),
$$

其中 $p=\lambda/L,\alpha=u-v,\beta=u$。归一子态 $z$ 的 Bloch 球坐标为

$$
\boxed{
R_B=(2\sqrt{p(1-p)}\cos\alpha,
2\sqrt{p(1-p)}\sin\alpha,2p-1).}
\tag{16}
$$

这是固定二维底部编码子空间的精确纯态表示。它不是一般张量子系统的偏迹，也未单独证明相应投影操作属于原生菜单。底部未来商忘掉 $\beta$，但完整源的 $02$ 相干

$C_{02}=\sqrt{Z\lambda}\,e^{i\beta}$ 仍读出它。

### 7.2 现有控制律已经给出水平提升

项目的两个原生速度场为

$$
P=\partial_\lambda,\qquad
Q=\left(\frac12-\frac\lambda r\right)\partial_u-
\frac\lambda r\partial_v.
$$

对相对命令 $(a(t),b(t))$，

$$
\dot\lambda=\dot a,\quad \dot\alpha=\dot b/2,\quad
\dot\beta=(1-p)\dot\alpha.
$$

<a id="thm-lift"></a>

**定理 7.1（原生球面路径的唯一水平提升）**

给定完整初态和一条 $C^1$ 基球曲线，若整段避开 $R_{B,z}=\pm1$，则有唯一满足原生控制律的水平提升。该提升满足

$$
\boxed{\langle z,dz\rangle=-i[d\beta-(1-p)d\alpha]=0.}
\tag{17}
$$

**证明。**

用 $\lambda=L(1+R_{B,z})/2$ 恢复高度，沿时间区间选择方位角 $\alpha$ 的连续实提升。定义 $a=\lambda-\lambda_0,b=2(\alpha-\alpha_0)$，再积分 $\beta=\beta_0+\int(1-p)d\alpha$。这些量满足原生 ODE，且由初态与积分唯一确定。对 $z$ 直接求导得到显示的内积公式。紧区间上避开极点使 $0<\lambda<L$ 有严格余量，故路径合法。

∎

该结论不额外假设 Berry 水平连接，而是从项目已有控制律得到它。同一命令用于未知起点族时，仍须保留

$$
\lambda_0+\min a>0,\qquad \lambda_0+\max a<L.
$$

穿过极点违反 full-support 条件，改换球面坐标图不能消除这个物理域边界。

### 7.3 闭环历史、椭圆手性与原生读口

<a id="thm-phase"></a>

**定理 7.2（半立体角与完整圆的椭圆相位）**

原生基球闭环的参考相位为

$$
\boxed{
\Delta\beta=\frac12\oint(1-R_{B,z})\,d\alpha
=\tfrac12\Omega_{\mathrm{solid}}\pmod{2\pi}.}
\tag{18}
$$

若基曲线为有向恒曲率 $k$ 的完整圆，且整圆避开原生极点，则

$$
\boxed{
\Delta\beta=\pi\left(1-\frac{k}{\sqrt{1+k^2}}\right)
=\pi(1-c)\pmod{2\pi},\qquad e=|c|.}
\tag{19}
$$

**证明。**

第一式由原生水平提升积分得到。标准外向球面面积形式为

$\omega=-dR_{B,z}\wedge d\alpha$，而

$d[(1-R_{B,z})d\alpha]/2=\omega/2$。Stokes 定理给半立体角，跨图的面积歧义为 $4\pi$，相位歧义为 $2\pi$。

恒曲率圆的轴 $n=(b+kr)/\sqrt{1+k^2}$ 固定，$n\cdot r=c$。按已有切向绕行，左侧球冠面积为 $2\pi(1-c)$；代入即可。

∎

注意相位符号：$z(T)=e^{-i\Delta\beta}z(0)$，故子态的几何相位为 $-\Delta\beta$；原生 $02$ 相干的转角为 $+\Delta\beta$。$k$ 和 $-k$ 给同一无向椭圆，但对应相位互为负数模 $2\pi$。开放弧还依赖轴的安放与起止位置，不能仅凭偏心率确定相位。

为与 v78 有序面积严格对齐，记

$$
A=a(T),\ B=b(T),\ K=\int a\,db.
$$

项目已有公式为

$$
\Delta\beta=B/2-(\lambda_0B+K)/r.
$$

零绕数闭合控制中 $A=B=0$，故 $\Delta\beta=-K/r$。另一方面

$\omega=-2\,da\wedge db/r$，给 $\Omega_{\mathrm{solid}}=-2K/r$，两条推导一致。

闭环后底部读口复原，但 $02$ 读口变化的欧氏范数为

$$
\boxed{\left\lVert \Delta y_{02}\right\rVert=4\sqrt{Z\lambda_0}\left|\sin\frac{\Delta\beta}{2}\right|.}
\tag{20}
$$

这是“位置回来了，历史仍在整体里”的一个具体可读关系。有方向的二维相干读出保留相位符号，单独范数可能丢失该符号。

### 7.4 度量和操作范围不能省去

置 $h=d\beta-(1-p)d\alpha$，直接计算

$$
g_{\mathrm{FS},z}=\frac{dp^2}{4p(1-p)}+p(1-p)d\alpha^2=\tfrac14|dR_B|^2,
$$

$$
g_{\mathrm{FS},\Psi}=r\,g_{\mathrm{FS},z}+rZ\,h^2.
$$

原生水平路径 $h=0$ 上，完整态长度是球面长度乘 $\sqrt r/2$。但控制坐标的拉回度量为

$$
g_{\mathrm{FS},z}=\frac{da^2}{4\lambda(L-\lambda)}+
\frac{\lambda(L-\lambda)}{4L^2}\,db^2,
$$

一般不同于项目某分支声明的控制成本 $da^2+db^2$。因此最短控制路径不自动等于 FS 大圆。

此外，概率方向 $P=\partial_\lambda$ 在球面上不是一个对所有输入统一作用的旋转。定理 [7.1](#thm-lift)证明给定起点的原生路径提升，没有证明每个原生命令都是同一个线性酉门或 CPTP 通道。要得到后者，必须另核验所有输入间的交叉关系守恒。

<a id="section-8"></a>

## 8. 反着推公理：撤去哪个条件，哪一对关系先失配

“把公理变为定义间约束”可以通过可检测的残差做到；“一切都在 $\Omega$”本身却不能选择哪个约束成立。

<a id="thm-completion"></a>

**定理 8.1（逐次相容的 Schur 判据）**

设新历史与旧历史整体的候选 Gram 块为

$$
G_{n+1}=\begin{pmatrix}G_n&b\\b^*&d\end{pmatrix}.
$$

则 $G_{n+1}\succeq0$ 当且仅当

$$
\boxed{G_n\succeq0,\quad b\in\operatorname{ran}G_n,\quad
S=d-b^*G_n^+b\ge0.}
\tag{21}
$$

并且 $\operatorname{rank}G_{n+1}=\operatorname{rank}G_n+\mathbf1_{\{S>0\}}$。

**证明。**

若整体正，对任意 $z\in\ker G_n$ 考察 $(tz,1)$ 的二次型，改变复数 $t$ 迫使 $`z^*b=0`$，从而 $b\in\operatorname{ran}G_n$。随后配方：

$$
\begin{aligned}
(z,w)^*G_{n+1}(z,w)
={}&(z+G_n^+bw)^*G_n(z+G_n^+bw)\\
&+(d-b^*G_n^+b)|w|^2.
\end{aligned}
$$

由此得充要性；同一可逆合同变换化为 $\operatorname{diag}(G_n,S)$，给出秩公式。

∎

这里二元关系的两个对象是“新历史”和“此前所有历史形成的整体载体”。整体载体的内容没有因被称作一个对象而消失。每个正余量都可能增长一个独立方向。

**命题 8.2（全部三元相容仍不足以保证整体相容）**

矩阵 $G=\frac32I_4-\frac12\mathbf1\mathbf1^{\mathsf T}$ 的每个三阶主块均半正定，但 $G$ 本身不半正定。

**证明。**

三阶主块在全一方向上的特征值为 $3/2-3/2=0$，其余为 $3/2$。四阶矩阵在全一方向上的特征值为 $3/2-2=-1/2$，所以整体失败。

∎

因此不能以“每一对或每三个节点都通过检查”替代全体有限历史正性。定理 [8.1](#thm-completion)是合法的逐次表述，但保留了累积的旧关系整体。

| 撤去的约束 | 可构造的后果或见证 | 更大结构 |
| --- | --- | --- |
| 全体有限核正性 | 所有三元都合法，四元组合出现负平方范数 | 共同 Gram 结构 |
| 完整交叉核守恒 | 单条路径各自归一，两个输入的距离仍可改变 | 共同线性可逆表示 |
| 二阶载体闭合 | $R>0$，新方向离开当前二态球 | 高阶历史 Gram |
| 二阶平滑接续 | $k$ 跳变，$r''$ 跳变 | 标架微分方程 |
| 手性与历史相位 | 无向椭圆相同，完整闭环相位不同 | 有向圆与水平提升 |
| 原生合法域 | 相同 $(A,B,K)$ 可有不同允许起点 | 部分命令与边界守卫 |
| 同根效果校准 | 概率可由另一个 $\rho$ 给出 | 历史根与效果的共同绑定 |

<details>
<summary>原始表格与列宽设置（逐字保留）</summary>

```latex
\begin{center}\small
\begin{tabularx}{\textwidth}{>{\raggedright\arraybackslash}p{.19\textwidth}>{\raggedright\arraybackslash}X>{\raggedright\arraybackslash}p{.24\textwidth}}
\toprule
撤去的约束 & 可构造的后果或见证 & 更大结构 \\
\midrule
全体有限核正性 & 所有三元都合法，四元组合出现负平方范数 & 共同 Gram 结构 \\
完整交叉核守恒 & 单条路径各自归一，两个输入的距离仍可改变 & 共同线性可逆表示 \\
二阶载体闭合 & $R>0$，新方向离开当前二态球 & 高阶历史 Gram \\
二阶平滑接续 & $k$ 跳变，$r''$ 跳变 & 标架微分方程 \\
手性与历史相位 & 无向椭圆相同，完整闭环相位不同 & 有向圆与水平提升 \\
原生合法域 & 相同 $(A,B,K)$ 可有不同允许起点 & 部分命令与边界守卫 \\
同根效果校准 & 概率可由另一个 $\rho$ 给出 & 历史根与效果的共同绑定 \\
\bottomrule
\end{tabularx}
\end{center}
```

</details>

<a id="section-9"></a>

## 9. 更简洁的量子约束：可压缩到哪里

将本轮接回 v78，可以使用以下三组约束，而不用重新把 Hilbert 空间、酉性、Hermitian 生成元、球面和椭圆逐项列为独立公理。

**整体与根态的类型。**

“一切在 $\Omega$ 内”中的整体，应包含它的历史、接续、参考与读出关系；v78 中表示为 $[o]$ 的根向量，是这个整体在重构空间中的表示成分。单个归一向量本身不能独自确定 $K$、$H$ 或允许的效果。内生化意味着把这些选择也纳入同一内部关系对象，并验证相容条件，避免在两种含义之间跳换。

**定义 9.1（同源量子关系结构）**

取根历史 $o$、历史集 $\mathcal H$、完整复核 $K$、允许接续及内部效果响应。

1. **共同相容。**归一纯态历史满足 $K(h,h)=1$，特别是 $K(o,o)=1$；任意有限历史的 Gram 矩阵正半定。重叠片段使用相同交叉核，可用定理 [8.1](#thm-completion)逐次检验。

2. **同源接续。**允许接续保持其共同定义域内的全部交叉核；全空间可逆门要求接续在所讨论历史载体上全域且双射。连续历史的固定锚点坐标具有相应正则性，时间标定、顺序、合法域和所需记录均属于同一个关系结构。

3. **同源读出。**效果响应正、归一、仿射且细分相容；根效果校准到同一个 $\Omega=[o]$，不同准备按同一接续协变。

这是一组研究对象的约束定义，不声称三组之间逻辑独立，也不声称它们是已证明的绝对最小公理。

**命题 9.2（保留 v78 的同根校准）**

有限维完整效果的正、归一、仿射且细分相容的响应满足 $p_o(0)=0$，并写为 $p_o(E)=\operatorname{Tr}(\rho_oE)$。若另有

$$
p_o(P_\Omega)=1,\quad P_\Omega=|\Omega\rangle\langle\Omega|,
\quad p_h(E)=p_o(U_h^*EU_h),
$$

则 $\rho_o=P_\Omega$，从而 $p_h(E)=\langle U_h\Omega,EU_h\Omega\rangle$。

**证明。**

$\operatorname{Tr}\rho_o(I-P_\Omega)=0$ 与正性意味着 $\rho_o$ 的支撑包含于 $\mathbb{C}\Omega$；迹一迫使 $\rho_o=P_\Omega$。代入准备协变即得结论。

∎

若撤去根校准，可选 $\rho_o=I/d$，它仍给正、归一、仿射效果响应，却通常不等于根纯态的读出。故不能把同根绑定删掉后再以“所有信息都在 $\Omega$”补上逻辑缺口。

**哪些现在是定理。**

完整正核构造内积空间；商去零范数关系后得到 Hilbert 表示。全域双射保核接续给酉算子；平滑性给 Hermitian 生成元。部分合法域上的保核接续先给定义域张成空间到像空间的等距同构，共同全空间延拓还需另证。一阶历史余量给局部度量，二阶余量给载体闭合。固定二态载体加恒定生成元给球面圆，历史投影给椭圆；原生双壁连接把完整圆的有向面积变为可见参考相位。

**哪些仍是输入条件。**

采用复核、允许什么线性组合、全体有限正性、控制可达范围、实际内部钟与效果接口，并未从“全在整体内部”这一句话中证明。经典状态空间也能把状态、记忆和规则全部放入一个整体，所以内生性本身不能排除经典模型。要论证量子的唯一性，需要继续给出可区分这些模型的内部关系或经验约束。

**关于有限三维。**

每个二元归一比较可有三轴坐标，单位切向标架的状态空间也恰好为三维流形 $SO(3)$；它们不是同一个对象，$SO(3)$ 也不全局等同 $\mathbb{R}^3$。为保持二阶历史还需曲率，为预测未来还可能需额外记忆。任何有限三维的局部编码，都不能无条件装下整个历史核的任意秩。

**白话图景。**较简洁的目标可以明确写为：所有历史比较、接续和读出，都必须能作为同一个整体的相容限制。圆、椭圆、相位和概率各自出现在这套关系的不同读口；让它们彼此对得上，才是在把独立输入压缩成约束。这里已经证明了多条这样的压缩，但还没有证明“无条件、无剩余输入地唯一导出整个量子世界”。

```latex
\clearpage
\begin{thebibliography}{9}
```

## 资料与可复核位置

<a id="ref-v78"></a>

1. 原对话《量子关系定理证明》，v78 完整正文。[原对话链接](https://chatgpt.com/c/6ae4bcb2-634c-83ec-b4d2-eb3d932f590a)。本稿沿用其同根校准修正及完整历史核框架。

<a id="ref-phase"></a>

2. The Omega Institute，*AURIC FIB-ATOM: Probability, Phase Transport and Holonomy*，固定提交 `7878c7f`，§§8.5、9、10。[固定版本原稿](https://github.com/the-omega-institute/trureturing/blob/7878c7ff9b75b9cb49dd84f440e15fd65f2dc665/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)。

<a id="ref-continuation"></a>

3. 同项目，*Observation graphs, purity certification and stable future response -- continuation*，§§10.4--10.6，公式(10.7)--(10.14)。[固定版本 continuation](https://github.com/the-omega-institute/trureturing/blob/7878c7ff9b75b9cb49dd84f440e15fd65f2dc665/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY_CONTINUATION.md)。

<a id="ref-recovery"></a>

4. 同项目，`D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean`。恢复目标当且仅当目标在观察纤维上为常数。[固定版本源码](https://github.com/the-omega-institute/trureturing/blob/7878c7ff9b75b9cb49dd84f440e15fd65f2dc665/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)。

<a id="ref-busch"></a>

5. P. Busch，*Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem*，[arXiv:quant-ph/9909073](https://arxiv.org/abs/quant-ph/9909073)。用于完整效果响应的标准背景；本稿另外保留根校准。

<a id="ref-bargmann"></a>

6. E. M. Rabei, Arvind, R. Simon, N. Mukunda，*Bargmann invariants and geometric phases -- A generalized connection*，[arXiv:quant-ph/9907080](https://arxiv.org/abs/quant-ph/9907080)。历史相位的相关原始研究。

<a id="ref-dlmf"></a>

7. NIST Digital Library of Mathematical Functions，§19.2，特别是公式 19.2.5，[第二类不完全椭圆积分的定义](https://dlmf.nist.gov/19.2)。

```latex
\end{thebibliography}
\end{document}
```

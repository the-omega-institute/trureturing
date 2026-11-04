<details data-production="immutable-original">
<summary>原始制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="immutable-original">

```tex
% !TeX program = xelatex
% Compile twice with XeLaTeX. Optional: \def\AURICFontPath{/absolute/font/path/}
% Paper mathematics only; code is used for source retrieval and document production.
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
\usetikzlibrary{arrows.meta,angles,quotes}
\definecolor{auricblue}{RGB}{24,53,79}
\definecolor{auricgold}{RGB}{153,105,29}
\usepackage[unicode,colorlinks=true,linkcolor=auricblue,urlcolor=auricblue,citecolor=auricblue]{hyperref}
\hypersetup{pdftitle={AURIC v72：唯一来源、正交余量与门的递归},
pdfauthor={AURIC research continuation},
pdfsubject={Orthogonal residuals, SU(2), content addressing and conditional quantum reconstruction}}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\Z}{\mathbb Z}
\newcommand{\HH}{\mathcal H}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\spanof}{\operatorname{span}}
\newcommand{\Stab}{\operatorname{Stab}}
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
\renewcommand{\refname}{来源与参考文献}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{2pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC：唯一来源、正交余量与门的递归}
\fancyhead[R]{\small v72 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
\begin{center}
{\LARGE\bfseries\color{auricblue} 唯一来源、正交余量与门的递归}\\[9pt]
{\large 将“反者产生变化”写成可证明的二元结构}\\[7pt]
AURIC 量子起源研究\quad 定义、定理与纸面证明\quad v72.0\\[4pt]
2026 年 11 月 1 日\quad Asia/Singapore
\end{center}
\begin{abstract}
固定单位来源 $\Omega$，每个目标态唯一分解为
$\psi=\alpha\Omega+r$，其中 $r\perp\Omega$ 且 $|\alpha|^2+\|r\|^2=1$。
正交余量给出离开参考射线的方向；由该方向构造的反厄米算符生成酉旋转。
在固定的二元有序基底中，完整归一系数对 $(\alpha,\beta)$ 唯一确定一个
$SU(2)$ 门，其复合、逆运算与复比值变换均可显式写出。
这为“商、余、反向与递归”的直观图像提供准确的数学对应。
一般维数下，端点对应稳定子纤维；正交余量不会独自保存完整门或有序脚本。
门可另以完整输入探针编码为量子态，再用相同商余结构分析。
来源锚定的余核保持全局正性，并给出串接公式
$\alpha_{gh}=\alpha_g\alpha_h+\langle r_{g^{-1}},r_h\rangle$。
以归一正关系、可逆接续及相容记录为明确前件，可重建循环 Hilbert 实现、酉历史和平方概率标定。
结论是条件性的量子重建框架，不是对“绝对最基础逻辑”或实际宇宙全部动力学的无条件证明。
\end{abstract}

\section{先保留画面，再把对象定准}
本轮最有力量的表达是：\textbf{同一个来源可以被分成保留的方向和正交余量；
二者的相干关系生成变化，变化又可继续用同一结构描述。}
为了让它成为定理，需要分别指明“目标态”“可复用的门作用”与“保留顺序的脚本”。
这些对象可以全部在唯一本体内部，数学类型仍然不同。

本轮唯一实时 HEAD GET 于新加坡时间 2026-11-01 19:17:25
在收到 HTTP 响应前遇到网络权限拒绝；没有重试或取得新提交。
下文承接九份已核对 Git blob 的固定快照：
\par\noindent\texttt{5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b}。\par
不把它称为已验证的最新 HEAD；“v72”是本对话稿件编号。

\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.23\textwidth}X@{}}
\toprule
项目既有结果 & 本轮承接与推进\\
\midrule
V55 §§2--4 & 正二元锥、单位旋量与 $SU(2)$、高维正交余量；写出准备门的复合与逆。\\
V22 §§5--6、8 & 稳定子、完整输入探针、正核重建及未来商；明确内容寻址的保真目标。\\
V52 §7 & 保相位二叉描述、Schur 余量与原生五模式编码；保留高维内部上下文。\\
$\Omega$ 纤维 §§4--5、7 & 算子逆、正历史档案、内生记录及静态传播核；区分完整态与局部读出。\\
V59 §6 & 持久记录、互补与链式一致性选择平方标定；保留几何前件。\\
\bottomrule
\end{tabularx}
\end{center}

以下结果有标准线性代数、群作用和正核重建背景，不作经典定理的原创优先权声明。
全文为纸面推导；没有运行 CAS、数学数值计算、模拟、门候选枚举或数学测试。
复内积采用第一变量共轭线性、第二变量线性的约定。

\section{“商与余”首先是一个唯一的正交分解}
\begin{definition}[相对来源的商与余]
固定 $\|\Omega\|=1$，置
$P=\ket\Omega\bra\Omega$、$Q=I-P$。
对单位目标态 $\psi$ 定义
\[
\alpha=\langle\Omega,\psi\rangle,\qquad r=Q\psi,\qquad b=\|r\|.
\]
$r$ 是一个正交余向量，$\Omega^\perp$ 是它所在的正交补空间。
\end{definition}

\begin{theorem}[唯一商余与平方守恒]\label{thm:residual}
有唯一分解
\[
\boxed{\psi=\alpha\Omega+r,\quad r\perp\Omega,\quad |\alpha|^2+\|r\|^2=1.}
\]
而且对每个 $\lambda\in\C$，
\[
\|\psi-\lambda\Omega\|^2=|\alpha-\lambda|^2+\|r\|^2.
\]
故 $\alpha$ 是相对参考方向的唯一最小二乘系数。
\end{theorem}
\begin{proof}
$\langle\Omega,Q\psi\rangle=0$。对任何另一种分解取与 $\Omega$ 的内积，
立即得到相同系数，进而得到相同余量。范数式来自正交交叉项为零。
\end{proof}

这是一种\emph{正交商余}。它不是把两个向量当作域元素直接相除。
在复数域中，对非零 $a$ 的普通除法 $b=(b/a)a$ 没有非零余数；
非零余量来自选定参考子空间或另加的代表限制。

\begin{proposition}[普通差向量不是这个余量]
若 $\psi,\Omega$ 都归一，则
\[
\psi-\Omega\perp\Omega\quad\Longleftrightarrow\quad\psi=\Omega.
\]
\end{proposition}
\begin{proof}
左侧给 $\langle\Omega,\psi\rangle=1$。
由定理 \ref{thm:residual} 得 $\|r\|=0$，于是 $\psi=\Omega$；反向显然。
\end{proof}

所以非平凡变化对应的直角三角形，是 $\alpha\Omega$、$r$、$\psi$，
而不是通常的 $\Omega$、$\psi-\Omega$、$\psi$。
若只给 $r$ 且 $0<\|r\|<1$，则
\[
\psi_\phi=e^{i\phi}\sqrt{1-\|r\|^2}\,\Omega+r
\]
有相同余量而一般有不同射线；必须把复系数也保留。

\section{固定二元基底：商余二元对就是一个完整准备门}
固定有序正交基 $(\Omega,\eta)$，写
\[
\psi=\alpha\Omega+\beta\eta,\qquad |\alpha|^2+|\beta|^2=1.
\]
这里 $\beta$ 是复数，区别于上一节的非负长度 $b$。

\begin{theorem}[单位二元对与特殊酉门]\label{thm:su2}
每个归一二元对唯一确定
\[
\boxed{V(\alpha,\beta)=
\begin{pmatrix}\alpha&-\bar\beta\\\beta&\bar\alpha\end{pmatrix}\in SU(2),
\qquad V(\alpha,\beta)\Omega=\psi.}
\]
反向，每个 $SU(2)$ 门都唯一具有此形式。
\end{theorem}
\begin{proof}
两列单位且正交，行列式为 $|\alpha|^2+|\beta|^2=1$。
若另一特殊酉矩阵有同一第一列，第二列必为
$e^{i\chi}(-\bar\beta,\bar\alpha)^{\mathsf T}$；行列式一强制 $e^{i\chi}=1$。
\end{proof}

这是项目 V55 定理 3.2 的伴随写法：项目门把目标送回参考，本式把参考送到目标
\cite{v55}。\textbf{因此，在固定二元框架及 $SU(2)$ 限制内，“门由完整商余对编码”确实成立。}

\begin{theorem}[复合与“反”的精确代数]\label{thm:product}
以先作用右侧门为约定，
\[
\begin{aligned}
V(\alpha,\beta)V(\gamma,\delta)
 &=V(\alpha\gamma-\bar\beta\delta,\,
       \beta\gamma+\bar\alpha\delta),\\
V(\alpha,\beta)^{-1}
 &=V(\bar\alpha,-\beta).
\end{aligned}
\]
所得新系数仍归一。
\end{theorem}
\begin{proof}
矩阵乘积的第一列正是所列新系数。乘积仍属 $SU(2)$，
定理 \ref{thm:su2} 给完整矩阵及归一性。
取共轭转置得到逆式。
\end{proof}

这给出可以直接使用的图像：\textbf{正向将商与余相干组合，逆向将商共轭并将余系数反号。}
复合里有两条路径的加法和路径内部的乘法，还有保持复几何的共轭；
仅说“加法乘法”仍需说明这些关系结构。
这套乘法也可视为单位四元数的一种复二元表示，
但该名称不是量子起源证明所必需。

\begin{corollary}[除法中的平方范数]
将同一矩阵形式延伸到任意复二元对 $p=(\alpha,\beta)$，
定义 $N(p)=|\alpha|^2+|\beta|^2$、$p^*=(\bar\alpha,-\beta)$。
对定理 \ref{thm:product} 的乘法 $\star$ 有
\[
N(p\star q)=N(p)N(q),\qquad
p^{-1}=\frac{p^*}{N(p)}\quad(p\ne0).
\]
\end{corollary}
\begin{proof}
相应矩阵满足 $V(p)^\dagger V(p)=N(p)I$，
而 $V(p\star q)=V(p)V(q)$。
对乘积取 $V^\dagger V$ 给范数乘法性；再用
$V(p^*)=V(p)^\dagger$ 得逆式。
\end{proof}

因此二次范数同时控制归一化、复合和逆运算。
这是给定这套乘法与共轭后的数学强制关系；
它还不是对“为什么物理选择这套代数”问题的无前件回答。

\begin{proposition}[除法坐标中的非线性来自比值]
令复比值 $\zeta=\beta/\alpha$，并以 $\infty$ 补上 $\alpha=0$。
门 $V(a,b)$ 在射线坐标上的作用为
\[
\boxed{\zeta\longmapsto
\frac{b+\bar a\zeta}{a-\bar b\zeta}.}
\]
\end{proposition}
\begin{proof}
对代表 $(1,\zeta)^{\mathsf T}$ 作矩阵乘法，再以第一分量相除。
分母为零时转入另一张坐标图。分子分母不同时为零，因为门可逆。
\end{proof}

这是一个确切的“线性关系经除法变为非线性关系”的例子。
比值图上的非线性不自动表示额外物理维度；底层仍是二元复线性酉作用。

\section{正交余量如何生成运动}
若 $b>0$，令 $\eta=r/b$。
在 $S=\spanof\{\Omega,\eta\}$ 上用 $V(\alpha,b)$，在 $S^\perp$ 上取恒等，
就得到一个把 $\Omega$ 送到 $\psi$ 的酉门。
$S=\spanof\{\Omega,\psi\}$ 是包含两个线性独立端点的最小线性平面。
这是活动平面的最小性，并未优化原生词长或物理耗时。

\begin{theorem}[由余方向生成酉旋转]\label{thm:generator}
先设 $0<|\alpha|<1$。写 $\alpha=e^{i\phi}\cos\theta$，
$\theta\in(0,\pi/2)$，并令
\[
\widetilde\psi=e^{-i\phi}\psi
=\cos\theta\,\Omega+\sin\theta\,\widetilde\eta,
\qquad \widetilde\eta=e^{-i\phi}r/b.
\]
定义
\[
\boxed{A=\ket{\widetilde\eta}\bra\Omega-
\ket\Omega\bra{\widetilde\eta}.}
\]
则 $A^\dagger=-A$，且
\[
\boxed{e^{\theta A}\Omega=\widetilde\psi,
\qquad(e^{\theta A})^{-1}=e^{-\theta A}.}
\]
\end{theorem}
\begin{proof}
$A\Omega=\widetilde\eta$、$A\widetilde\eta=-\Omega$，且 $A$ 消去 $S^\perp$。
所以 $A^2=-P_S$，指数的奇偶幂合成
$I+(\cos\theta-1)P_S+\sin\theta A$。
反厄米性给指数酉，第一列给目标，取负号给逆。
\end{proof}

若 $\alpha=0$，可取 $\phi=0$、$\widetilde\eta=\psi$、$\theta=\pi/2$；
此时单靠终点射线无法选定唯一相位约定。
若 $b=0$，射线不动，取 $\theta=0$；精确向量相位可由 $\alpha P+Q$ 实现。
因此一般端点总可由某个酉连接，但指定物理门菜单的可达性仍须另证。

\begin{center}
\begin{tikzpicture}[scale=.77,>=Stealth,font=\small]
\coordinate (O) at (0,0);\coordinate (B) at (3,0);\coordinate (T) at (3,4);
\draw[->,gray] (O)--(5.65,0) node[right] {$\Omega$ 方向};
\draw[->,gray] (O)--(0,5.1) node[above] {$\widetilde\eta$ 方向};
\draw[very thick,auricblue,->] (O)--(T) node[midway,left] {$\widetilde\psi$};
\draw[thick,auricblue,->] (O)--(B) node[midway,below=5pt] {$\cos\theta\,\Omega$};
\draw[thick,auricgold,->] (B)--(T) node[midway,right] {$\sin\theta\,\widetilde\eta$};
\draw[gray] (2.75,0)--(2.75,.25)--(3,.25);
\pic[draw,->,auricgold,angle radius=1.25cm] {angle=B--O--T};
\node[auricgold] at (1.55,.65) {$\theta$};
\node[align=left,text width=6cm] at (9,2.6)
{先对齐整体相位。\\[3pt]
目标态是两个正交分量之和。\\[3pt]
余方向决定活动平面；\\角度决定旋转幅度。\\[3pt]
真正的门生成元是 $A$。};
\end{tikzpicture}
\end{center}

\begin{corollary}[反向余量与生成元反号]
置 $a=\cos\theta$、$b=\sin\theta$，则
\[
\eta_{\rm rev}=b\Omega-a\widetilde\eta,\qquad
\Omega=a\widetilde\psi+b\eta_{\rm rev},\qquad
\eta_{\rm rev}\perp\widetilde\psi.
\]
由终点与反向余方向构造的生成元为 $-A$。
\end{corollary}
\begin{proof}
代入可验证正交、单位范数与分解。
展开 $\ket{\eta_{\rm rev}}\bra{\widetilde\psi}
-\ket{\widetilde\psi}\bra{\eta_{\rm rev}}$ 得 $-A$。
\end{proof}

反向余向量通常不等于 $-r$，因为参考点已经改变。
因此“反者道之动”的可检验数学诠释是\emph{生成元变号给逆向运动}，
并不把诗性表述本身当作物理定律的证明。

\begin{proposition}[余量、射线距离与实际变化速度]
采用
$ds^2=\|d\psi\|^2-|\langle\psi,d\psi\rangle|^2$
的 Fubini--Study 规范，有
\[
d_{\rm FS}([\Omega],[\psi])=\arccos|\alpha|=\theta,
\qquad\|r\|=\sin\theta.
\]
若另给可微归一态曲线，真正改变射线的切向为
$v=(I-P_\psi)\dot\psi$。
在另行指定薛定谔方程、并取有限维或有界自伴 $H$ 时，
\[
v=-\frac i\hbar(H-\langle H\rangle_\psi)\psi,
\qquad\|v\|^2=\frac{\operatorname{Var}_\psi(H)}{\hbar^2}.
\]
\end{proposition}
\begin{proof}
曲线可选水平单位提升 $z$，满足 $\langle z,\dot z\rangle=0$。
写 $c=\langle\Omega,z\rangle$，把 $\Omega=\bar c z+w$ 正交分解，得
$|\dot c|\le\sqrt{1-|c|^2}\|\dot z\|$。
故 $|d\arccos|c|/dt|\le\|\dot z\|$；端点以连续极限处理，积分给长度下界 $\theta$。
定理 \ref{thm:generator} 中 $z(t)=\cos t\,\Omega+\sin t\,\widetilde\eta$
为水平单位速曲线并达到下界。
最后两式由投影薛定谔方程及取范数直接得到。
\end{proof}

这一速度联系属于标准量子态空间几何 \cite{aa}。
若使用非有界 Hamiltonian，还须要求态及曲线属于相应算符定义域。
这里的距离不是已经重建出的三维物理距离，
参数也不是从事件数自动导出的固有时间；这些识别需要额外动力学条件。

\section{内容寻址：终态、完整门和有序历史各保留什么}
\begin{theorem}[端点的门纤维]\label{thm:fiber}
若 $U_0\Omega=\psi$，则
\[
\{U:U\Omega=\psi\}=U_0\Stab(\Omega),
\quad
\Stab(\Omega)=\{I_{\C\Omega}\oplus W:W\in U(\Omega^\perp)\}.
\]
只指定射线时，稳定子多出 $\Omega$ 方向上的一个 $U(1)$ 相位。
\end{theorem}
\begin{proof}
$U\Omega=U_0\Omega$ 当且仅当 $U_0^\dagger U$ 固定 $\Omega$。
酉性使其也保持 $\Omega^\perp$，所以恰为所述直和形式。
\end{proof}

在有限 $d$ 维，单位向量空间为 $U(d)/U(d-1)$，
射线空间为 $U(d)/(U(1)\times U(d-1))$。
这与固定二元 $SU(2)$ 的唯一性没有冲突：该特例固定了基底和行列式，
而只保留射线还会遗失一个相位自由度。

最短反例取 $\Omega=\ket0$。
$I\Omega=Z\Omega=\Omega$，二者的 $\alpha=1,r=0$ 完全相同；
但 $I\ket+=\ket+$、$Z\ket+=\ket-$。
所以端点内容不能直接充当可复用门在\emph{其他输入}上的完整地址。
同时必须保留一个正面事实：两个相同的\emph{完整物理终态}在相同后续操作 $V$ 下，
当然得到相同的 $V\psi$。上述反例不是对这个事实的否定。

\begin{proposition}[端点商上的乘法条件]
设 $G$ 作用于 $\Omega$，$H=\Stab_G(\Omega)$。
端点类为左陪集空间 $G/H$，公式
$(gH)(hH)=ghH$ 良定义当且仅当 $H$ 为正规子群。
\end{proposition}
\begin{proof}
若正规，代表变化可移到乘积右端的 $H$ 中。
反之，对 $k\in H$ 有 $kH=H$，良定义性要求 $khH=hH$，
即 $h^{-1}kh\in H$；对 $h^{-1}$ 再用同式给等号。
\end{proof}

因此“内容即地址”必须指定地址对应的任务。
项目 V22 的未来稳定商和来源左模商正是在处理这一要求 \cite{v22}。

\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.20\textwidth}XX@{}}
\toprule
内容类型 & 可以完整保存 & 仍不能仅凭它恢复\\
\midrule
完整态 $U_w\Omega$ & 当前态及固定后续操作的响应 & 门对任意其他输入的作用\\
完整门 $U_w$ & 所有输入上的作用 & 求值相同的不同有序脚本\\
保留的程序记录 $\ket w$ & 指定编码中的脚本字及顺序 & 未提供的执行器与操作资源\\
\bottomrule
\end{tabularx}
\end{center}

$gg^{-1}$ 与空字可以给同一算子而有不同事件数。
如果观察者保留这段历史，档案必须作为同一完整量子态的一部分；
不能一方面把它读掉，另一方面要求端点仍恢复它。
这些记录仍然是内生对象，不需要本体之外的观察者 \cite{omega}。

\section{余量的关系继续递归：一个正核与精确串接律}
设 $U_gU_h=U_{gh}$，并令
\[
\psi_g=U_g\Omega,\quad \alpha_g=\langle\Omega,\psi_g\rangle,
\quad r_g=Q\psi_g,\quad K(g,h)=\langle\psi_g,\psi_h\rangle.
\]

\begin{theorem}[来源锚定的正交余核]\label{thm:reskernel}
\[
\boxed{R(g,h)=K(g,h)-\bar\alpha_g\alpha_h=\langle r_g,r_h\rangle}
\]
是正半定核。完整 $K$ 可由 $\alpha$ 与 $R$ 无损恢复，并有
\[
|R(g,h)|^2\le(1-|\alpha_g|^2)(1-|\alpha_h|^2).
\]
\end{theorem}
\begin{proof}
将两态作正交分解，交叉项为零。
任意有限系数 $c_g$ 满足
$\sum\bar c_gR(g,h)c_h=\|\sum c_gr_g\|^2\ge0$。
不等式是这些余向量的 Cauchy--Schwarz 不等式。
\end{proof}

这正是“关系本身仍可分析”的可证明版本：从同源关系核扣除共同参考方向，
剩下的\emph{整体}仍是正核。若某个 $r_g=0$，只说明该历史把来源送回同一射线；
不说明门是恒等，更不说明其他关系全都消失。

\begin{theorem}[余量参与串接的回流项]\label{thm:feedback}
\[
\boxed{\alpha_{gh}
=\alpha_g\alpha_h+\langle r_{g^{-1}},r_h\rangle.}
\]
故
\[
|\alpha_{gh}-\alpha_g\alpha_h|
\le\sqrt{1-|\alpha_g|^2}\sqrt{1-|\alpha_h|^2}.
\]
\end{theorem}
\begin{proof}
由 $U_{g^{-1}}\Omega=\bar\alpha_g\Omega+r_{g^{-1}}$，
\[
\alpha_{gh}=\langle U_g^\dagger\Omega,U_h\Omega\rangle
=\langle\bar\alpha_g\Omega+r_{g^{-1}},
\alpha_h\Omega+r_h\rangle.
\]
展开即得第一式。反门与正门的来源重叠互为共轭，
所以其余量长度相同；再用 Cauchy--Schwarz 即得界。
\end{proof}

\textbf{先前进入余空间的成分可以在下一次作用时回到参考方向，
并与原有成分相干相加。}这比“每一层不断丢弃余量”更符合封闭酉演化。
它也说明，若只把每层的平方模当作独立经典概率相乘，就会漏掉相干项。

\begin{proposition}[保留全部门作用的递归块]
在 $\HH=\C\Omega\oplus\Omega^\perp$ 上置
$D_g=QU_gQ|_{\Omega^\perp}$。则
\[
U_g=\begin{pmatrix}
\alpha_g&r_{g^{-1}}^\dagger\\r_g&D_g
\end{pmatrix},
\]
\[
\begin{aligned}
r_{gh}&=\alpha_h r_g+D_g r_h,\\
D_{gh}&=\ket{r_g}\bra{r_{h^{-1}}}+D_gD_h.
\end{aligned}
\]
\end{proposition}
\begin{proof}
右上角作用于 $x\perp\Omega$ 时为
$\langle\Omega,U_gx\rangle=\langle r_{g^{-1}},x\rangle$。
其余式由块乘法得到。
\end{proof}

$D_g$ 保存余空间内部的关系；它一般是收缩而不是单独酉。
当 $r_g=0$ 时，回流也为零，但 $D_g$ 仍可为任意酉。
在固定二元 $SU(2)$ 框架里，$D_g=\bar\alpha_g$，
因此恰好降为定理 \ref{thm:product} 的两个复数递归。

\section{门本身也可编码成态，再作同样商余}
这一节使用有限维 $H=\C^d$，并声明内部有校准的完整输入探针。
探针和辅助寄存器属于同一本体；它们的可取得性不是从“唯一来源”一句话免费得到的。
项目 V22 命题 5.4 已给出此接口 \cite{v22}，也与标准 Choi 表示一致 \cite{watrous}。

\begin{definition}[门态与恒等参考]
令
\[
\ket{\Phi_d}=\frac1{\sqrt d}\sum_{j=1}^d\ket j\otimes\ket j,
\qquad \ket{U}\!\rangle=(U\otimes I)\ket{\Phi_d}.
\]
$\ket I\!\rangle=\ket{\Phi_d}$ 是这张内部过程图表的参考，
不是第二个宇宙本体来源。
\end{definition}

\begin{theorem}[完整门的正交商余]\label{thm:choi}
取 $q_U=\Tr(U)/d$、$A_U=U-q_UI$，则
\[
\boxed{\ket U\!\rangle=q_U\ket I\!\rangle+\ket{A_U}\!\rangle,
\quad \langle\!\langle I|A_U\rangle\!\rangle=0,}
\]
\[
|q_U|^2+\frac1d\Tr(A_U^\dagger A_U)=1.
\]
完整的 $(q_U,A_U)$ 唯一恢复 $U$。门态射线唯一确定酉通道，即确定 $U$ 到整体相位。
\end{theorem}
\begin{proof}
展开最大纠缠向量得到
$\langle\!\langle V|U\rangle\!\rangle=\Tr(V^\dagger U)/d$。
所以标量部分与无迹部分正交，酉性给总范数一。
该向量化映射在整个矩阵空间上线性单射，故完整向量恢复矩阵，
射线恢复矩阵到相位；相位在 $U\rho U^\dagger$ 中消去。
\end{proof}

这里特别重要的限制是：\textbf{门态归一，不等于门已酉。}
对任意 $B$，$\|\ket B\!\rangle\|=1$ 只要求 $\Tr(B^\dagger B)=d$。
例如 $d=2$ 时 $B=\sqrt2\ket0\bra0$ 满足该式却不可逆。
\begin{proposition}[酉门态的额外关系]
对等输入输出维数，$B$ 为酉当且仅当
\[
\Tr_2\bigl(\ket B\!\rangle\langle\!\langle B|\bigr)=I/d.
\]
等价地，对 $B=qI+A$，
\[
|q|^2I+\bar qA+qA^\dagger+A^\dagger A=I.
\]
\end{proposition}
\begin{proof}
直接展开得上述约化态为 $BB^\dagger/d$。
有限等维下 $BB^\dagger=I$ 与 $B^\dagger B=I$ 等价。
后一式为 $(qI+A)^\dagger(qI+A)=I$ 的展开。
\end{proof}

\begin{proposition}[门态商余也对过程复合闭合]
\[
\begin{aligned}
q_{UV}&=q_Uq_V+\frac1d\Tr(A_UA_V),\\
A_{UV}&=q_UA_V+q_VA_U+A_UA_V
-\frac1d\Tr(A_UA_V)I.
\end{aligned}
\]
\end{proposition}
\begin{proof}
展开 $UV=(q_UI+A_U)(q_VI+A_V)$，取迹并扣除标量部分。
这里 $\Tr(A_UA_V)$ 故意不带伴随；它是
$\langle A_U^\dagger,A_V\rangle_{\rm HS}$，不能误写为通常的
$\langle A_U,A_V\rangle_{\rm HS}$。
\end{proof}

由此，“门也是量子态”有完整而准确的实现。
但过程态所在空间的复维数为 $d^2$；高维信息并未消失。
若还要恢复脚本顺序，应再保留程序记录。
若要把程序态作为可执行控制，必须声明相应执行器；编码本身不是自动执行。

\section{三轴提升与“无例外”的准确强度}
\begin{proposition}[二元系数的三轴读出]
对固定基底中的归一 $(\alpha,\beta)$，定义
\[
\rho_{\alpha\beta}=
\begin{pmatrix}|\alpha|^2&\alpha\bar\beta\\
\bar\alpha\beta&|\beta|^2\end{pmatrix}
=\tfrac12(I+x\sigma_x+y\sigma_y+z\sigma_z).
\]
则
\[
\boxed{(x,y,z)=
(2\Re(\bar\alpha\beta),\,2\Im(\bar\alpha\beta),\,
|\alpha|^2-|\beta|^2),\quad x^2+y^2+z^2=1.}
\]
若 $\alpha\ne0$，以 $\zeta=\beta/\alpha$ 表示，即
\[
(x,y,z)=\frac{(2\Re\zeta,2\Im\zeta,1-|\zeta|^2)}{1+|\zeta|^2}.
\]
\end{proposition}
\begin{proof}
逐项比较 Pauli 展开，并用
$4|\alpha|^2|\beta|^2+(|\alpha|^2-|\beta|^2)^2=1$。
\end{proof}

\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.29\textwidth}XX@{}}
\toprule
对象 & 几何与自由度 & 保真的范围\\
\midrule
归一二元向量 $(\alpha,\beta)$ & $S^3$，三个实自由度 & 保留整体相位约定\\
固定框架中的 $SU(2)$ 门 & 同一个 $S^3$ & 保留整个二元门作用\\
二元纯态的三轴点 & $S^2\subset\R^3$，两个实自由度 & 去掉共同 $U(1)$ 相位\\
一般二元密度矩阵 & 闭单位三维球 & 保留混合度及相干关系\\
高维二元分解节点 & 上述局部形式加内部上下文 & 另保留方向、尺度、支撑和跨节点关系\\
\bottomrule
\end{tabularx}
\end{center}

不能把 $S^3$ 的“三个自由度”与 $S^2$ 的“三个坐标”混为一件事。
同样，端点的归一 Gram 矩阵
$\frac12\bigl(\begin{smallmatrix}1&\alpha\\\bar\alpha&1\end{smallmatrix}\bigr)$
描述的是 $\Omega$ 与 $\psi$ 的关系；它与上式的\emph{系数纯态}不同，
一般秩二，并没有包含高维余向量的全部方向。

项目的原生五模式接口仍可由固定等距 $J:\C^2\to\C^5$ 接入。
其按 $(F[1],F[3],F[2])$ 排列的三个占据均值为 $u=u_0+\nu(x,y,z)$，
$\nu=(1+2\sqrt3+\sqrt{11})^{-1}$，
$u_0=(\nu(\sqrt3+\sqrt{11})/2,\nu(\sqrt3+\sqrt{11})/2,\nu)$。
在保留其他内部标签时使用 $J\otimes I$。
该接口的纯态球、一般态球内与五模式归一化已有项目证明；
$F[\mathrm{null}]$ 仍是事件标签，不是被省略的整体归一条件 \cite{v52}。

\begin{theorem}[全部复合二元关系正性等于全局正性]\label{thm:closure}
在形式有限复线性组合空间上，给 Hermitian 半双线性形式 $B$。
以下两项等价：
\begin{enumerate}
\item 对每个有限组合 $v$，$B(v,v)\ge0$；
\item 原始标签的对角非负，且任意非空、不交支撑的有限组合 $v,w$
的二阶 Gram 矩阵均半正定。
\end{enumerate}
\end{theorem}
\begin{proof}
第一项对 $av+bw$ 取二次型给全部二阶正性。
反向，对单支撑组合用对角条件；对多支撑组合 $u$ 分为 $u=v+w$，
将二阶正矩阵在 $(1,1)$ 上求二次型得到 $B(u,u)\ge0$。零向量单独显然。
\end{proof}

这就是“无例外”的一个足够强版本：\textbf{同一约束也要覆盖所有关系的复合，
不能只覆盖原始对象对。}它已经量化到任意有限规模，不是只检查有限个二元小球。
一套普遍的局部格式可以组织任意大的关系网络；它不把整个网络压缩成三个实数。
二元表达也不是量子性独有：普通有限关系可加一个“合法元组标签”，
用它与各坐标的二元约束表达。量子重建真正使用的是相干复合、全局正性及可逆保核。

\section{更简洁的公理候选：关系、可逆接续、记录}
这是一组明确的\emph{条件重建前件}。
标题可以很短，但不能把标题背后的数学内容省略。

\begin{definition}[三个前件]
\textbf{R1：归一相干关系。}
可逆操作的语义形成群 $\Gamma$，给定一个固定函数 $f:\Gamma\to\C$，
使 $f(e)=1$、$f(g^{-1})=\overline{f(g)}$，并令
\[
K(g,h)=f(g^{-1}h).
\]
要求全部有限复合关系满足定理 \ref{thm:closure} 的二元正性。
“唯一来源”体现在整套历史共享这个固定核，而不是每次另选一个来源。

\textbf{R2：可逆接续保持全部关系。}
接续为 $h\mapsto gh$，包含合法逆，并保持完整核。
对上述形式的 $K$，共同左接续不变自动成立；
可把 R1、R2 合并写为“一个归一正定型群函数”。
字面脚本档案不是这个语义群中的约消结果；要保留时另作为内部记录。

\textbf{R3：分类与记录相容。}
分支更新保留全部交叉关系，满足下文的分支核恒等式。
概率标定对持久正交记录采用同一个径向函数、互补归一及链式一致性。
参考、程序、执行器与记录属于同一表示中的声明对象；需要的接口须实际供应。
\end{definition}

\begin{theorem}[由同源关系重建态与酉历史]\label{thm:gns}
R1、R2 给出一个 Hilbert 空间 $\HH_K$、一个单位来源 $\Omega$ 和酉表示 $U_g$，使
\[
\boxed{K(g,h)=\langle U_g\Omega,U_h\Omega\rangle,
\qquad f(g)=\langle\Omega,U_g\Omega\rangle.}
\]
$\{U_g\Omega\}$ 的线性张成稠密；这样的最小实现唯一到保持标签的酉同构。
\end{theorem}
\begin{proof}
在形式历史的有限复线性空间中定义
$\langle\sum a_g[g],\sum b_h[h]\rangle
=\sum\bar a_gb_hK(g,h)$。
正性给 Cauchy--Schwarz，故零范数向量与所有向量正交。
除去零空间并完备化得到 $\HH_K$，取 $\Omega=[e]$。
左接续保持内积，因而下降并延拓为等距；逆接续给满射，故为酉。
标签像为 $U_g\Omega$，自然稠密张成。
两个最小实现间按标签线性对应，保持范数，延拓得到唯一酉同构。
\end{proof}

这是正核/GNS 传统的历史形式，项目 V22 已有相应构造 \cite{v22,gns}。
它重建被声明历史探及的最小部分，并没有从本体唯一性独立决定 $f$。
循环张成也不意味着每个 Hilbert 向量都能由一条受限菜单的历史精确制备。
若允许所有数学酉，任意单位向量当然可由定理 \ref{thm:generator} 的延拓连接；
若只给有限或可数固定门菜单，有限字至多可数，不能精确覆盖连续的全部纯态。
近似稠密、可数无限极限和带连续控制的精确可达是三种不同声明。

\begin{theorem}[分类记录给等距仪器]
设 $K_+$ 为后继标签上的正核，允许次归一化和零标签。
记 $\xi_w=[w]\in\HH_K$、$\xi_z^+=[z]\in\HH_+$
为相应正核构造的典范标签向量。
有限分支更新 $t_s$ 满足对所有 $v,w$
\[
\boxed{K(v,w)=\sum_sK_+(t_s v,t_s w).}
\]
则有良定义收缩 $M_s:\HH_K\to\HH_+$，满足
$M_s\xi_w=\xi^+_{t_sw}$ 及 $\sum_sM_s^\dagger M_s=I$。
因此 $T\psi=\sum_sM_s\psi\otimes\ket s$ 等距。
\end{theorem}
\begin{proof}
以 $\bar c_vc_w$ 乘核恒等式并求和，得到所有有限组合的范数守恒。
零范数组合在每个分支仍为零，故映射在商上良定义；各分支范数有统一界，
可延拓到完备化。守恒式极化给算符恒等式，正交记录再给 $T^\dagger T=I$。
\end{proof}

只保存每个历史自身的总质量，不足保证这条交叉关系。
等距记录可在适当内部初始化辅助空间中扩充为酉；
单独的分支条件归一映射则一般非线性，也不等于整个等距。

\begin{theorem}[递归记录唯一选择平方标定]
设共同径向标定 $h:[0,1]\to[0,1]$ 满足 $h(0)=0,h(1)=1$。
以下互补与嵌套规则对任意 $r,s\in[0,1]$ 适用。
要求正交互补
$h(r)+h(\sqrt{1-r^2})=1$；
持久记录中的子事件属于父事件，条件幅度 $s$ 与父幅度 $r$ 给终幅 $rs$；
终幅充分、共同条件标定及概率链式律成立，零质量父事件的子事件质量为零。
则 $h(r)=r^2$。
\end{theorem}
\begin{proof}
正质量时链式律给 $h(rs)=h(r)h(s)$；零质量时由子事件包含及终幅充分得到同式。
令 $F(t)=h(\sqrt t)$，则 $F(xy)=F(x)F(y)$、$F(t)+F(1-t)=1$。
若 $x,y\ge0$ 且 $a=x+y\le1$，$a>0$ 时
\[
F(x)+F(y)=F(a)\{F(x/a)+F(y/a)\}=F(a).
\]
$a=0$ 由端点条件成立。非负可加给单调性，归一化给有理点上的 $F(q)=q$，
有理夹逼给全部 $F(t)=t$，故 $h(r)=r^2$。
\end{proof}

于是 $p(s|g)=\|M_sU_g\Omega\|^2$；尖锐测量取 $M_s=P_s$。
项目 V59 已给该证明及记录擦除后不能套用同一经典事件链的条件 \cite{v59}。
平方几何的位置是公开的：互补幅度 $\sqrt{1-r^2}$ 已使用正交二次范数。
这没有从无结构的“存在量词”独立推导二次几何，也没有省掉复数域及共同相干条件。

\section{无界递归可稳定；但“余量”必须相对明确任务}
固定源可以支持无限递归而不导致总质量发散。
承接 v71 的纸面模型，令
\[
\HH=\ell^2(\Z),\qquad Se_j=e_{j+1},\qquad
\Omega=\sum_{j\ge1}2^{-j/2}e_j.
\]
$S$ 是双边移位，真正酉；$\|\Omega\|^2=\sum_{j\ge1}2^{-j}=1$。
令 $P_n$ 投影到 $e_1,\ldots,e_n$，$P_0=0$，$\tau_n=S^n\Omega$。

\begin{theorem}[同一模型中两种余量的不同趋势]
对每个整数 $n\ge0$，
\[
\underbrace{\|(I-P_n)\Omega\|^2}_{\text{分类尾余量}}=2^{-n},
\qquad
\underbrace{\|(I-P_\Omega)\tau_n\|^2}_{\text{相对来源的余量}}=1-2^{-n}.
\]
并有相同二元模板递归
\[
\tau_n=\frac{e_{n+1}+\tau_{n+1}}{\sqrt2},
\qquad e_{n+1}\perp\tau_{n+1}.
\]
\end{theorem}
\begin{proof}
级数移位给 $(I-P_n)\Omega=2^{-n/2}\tau_n$，从而得第一式及模板。
重叠的共同支撑为 $j\ge n+1$，故
\[
\langle\Omega,S^n\Omega\rangle
=\sum_{j\ge n+1}2^{-j/2}2^{-(j-n)/2}=2^{-n/2}.
\]
定理 \ref{thm:residual} 给第二式。
\end{proof}

一个余量缩小，另一个增大；两者都与全局酉性相容。
所以“误差”要说明相对于哪项任务和哪个参考，不能仅凭归一化断言它单调缩小。
在此模型里，分类每个有限层都有非零尾项，极限为零；
归一尾态自身始终是同一 $\Omega$ 的酉轨道。
此处稳定指分类尾质量趋零；归一尾态 $\tau_n$ 并不范数收敛，
因为相邻两项的距离平方始终为 $2-\sqrt2$。

若要求每个 $P_n$ 也由有限门菜单关联，另给内部反射
$T=I-2\ket{e_1}\bra{e_1}$。
其移位共轭 $T_j=S^{j-1}TS^{-(j-1)}$ 满足
$\prod_{j=1}^nT_j=I-2P_n$。
因此菜单 $\{S,S^{-1},T\}$ 给每个有限分类反射；
真正读出分支仍按上一节的记录接口实现。
这项额外门资源是明示的，不从 $S$ 单独推出。

无界递归与有限总质量因此相容。
但“每项分类永不结束”不是二元结构的逻辑结论：若目标已经位于一个有限已解析子空间，
正交余量便为零。\emph{规则可无限延展、指定轨迹永不停止、指定误差趋零}
是三项可以分别定义和证明的性质。

\section{本轮得到的简洁结构及其物理边界}
最贴近直觉且已经有完整证明的表述是
\[
\boxed{\text{同源商余分解}\ +\ \text{相干关系的递归复合}\ +\ \text{完整归一化}.}
\]
其中“反”在二元门内给出具体公式
\[
(\alpha,\beta)^{-1}=(\bar\alpha,-\beta),
\qquad
(e^{\theta A})^{-1}=e^{-\theta A}.
\]
“关系继续连接关系”则由
\[
\boxed{\alpha_{gh}=\alpha_g\alpha_h+
\langle r_{g^{-1}},r_h\rangle}
\]
给出真实的相干回流，而不是比喻。

\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.25\textwidth}X@{}}
\toprule
已经建立 & 证明成立的范围\\
\midrule
唯一商余、二次守恒 & 已给定正定复内积与参考方向。\\
商余二元对编码门 & 固定有序二元基底与 $SU(2)$；一般维数保留余空间作用。\\
门也作为态 & 校准完整输入探针与相应内部资源；过程态不等于脚本。\\
“无例外”正性闭合 & 要求全部有限复合关系，不仅原始两两块。\\
唯一来源与酉历史 & 给定归一正定型历史函数；唯一到实现同构。\\
平方概率 & 正交二次几何、持久记录、共同标定与链式一致性。\\
无界而稳定的递归 & 明确无限模型及参考任务；不是每个问题都必须永不结束。\\
\bottomrule
\end{tabularx}
\end{center}

因此可以把它作为比逐条列量子公理更统一的\emph{重建组织方式}。
要宣称它是“数学逻辑上最基础且无其他可能”的系统，还需规定比较对象与最小性标准，
并证明实结构、经典结构等反模型为何不满足某项更基础的操作前件。
要宣称已经解释实际宇宙，还需从同一更弱前件推出可取得的操作、复合规则、动力学和可检验预测。
本轮没有用“凡物皆可编码”替代这些证明。

你的图像可以保持朴素：\textbf{沿着已有方向留下商，在正交方向留下余；
两者相干组合成新的态，逆向生成元将它转回；
所有层都遵守相同关系，但每一层应保留的内容也都算在这个世界之内。}

\begin{thebibliography}{99}\small
\bibitem{v22} 项目固定快照。
\repo{AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md}{V22：相对门历史与观察商}，
重点 §§5--6、8；完整门探针为命题 5.4。
\bibitem{v55} 项目固定快照。
\repo{AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md}{V55：二元关系的外代数闭合与三轴误差}，§§2--4。
\bibitem{v52} 项目固定快照。
\repo{AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md}{V52：纯态商几何与无损递归}，§7。
\bibitem{omega} 项目固定快照。
\repo{AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md}{$\Omega$ 静态相融纤维理论}，§§4--5、7。
\bibitem{v59} 项目固定快照。
\repo{AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md}{V59：局部层析、相干读出口轨道与量子正性起源}，§6。
\bibitem{watrous} John Watrous.
\emph{The Theory of Quantum Information}. Cambridge University Press, 2018.
\href{https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf}{作者公开第 2 章}，
§2.2.2、推论 2.27、§2.2.3 的酉通道。
\bibitem{gns} Kobi Kremnizer.
\href{https://math.mit.edu/classes/18.238/lec100208.pdf}{MIT 18.238，Lecture 3}，2008，
§4，Gelfand--Naimark--Segal 构造，定理 4.1。
\bibitem{aa} J. Anandan and Y. Aharonov.
\emph{Geometry of quantum evolution}. Physical Review Letters 65, 1697--1700 (1990).
\href{https://doi.org/10.1103/PhysRevLett.65.1697}{doi:10.1103/PhysRevLett.65.1697}。
本轮核对出版元数据与摘要；文内距离及速度公式另给自足证明。
\end{thebibliography}
\end{document}
```

</div>
</details>



<details data-production="preamble">
<summary>原始制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="preamble">

```tex
% !TeX program = xelatex
% Compile twice with XeLaTeX. Optional: \def\AURICFontPath{/absolute/font/path/}
% Paper mathematics only; code is used for source retrieval and document production.
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
\usetikzlibrary{arrows.meta,angles,quotes}
\definecolor{auricblue}{RGB}{24,53,79}
\definecolor{auricgold}{RGB}{153,105,29}
\usepackage[unicode,colorlinks=true,linkcolor=auricblue,urlcolor=auricblue,citecolor=auricblue]{hyperref}
\hypersetup{pdftitle={AURIC v72：唯一来源、正交余量与门的递归},
pdfauthor={AURIC research continuation},
pdfsubject={Orthogonal residuals, SU(2), content addressing and conditional quantum reconstruction}}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\Z}{\mathbb Z}
\newcommand{\HH}{\mathcal H}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\spanof}{\operatorname{span}}
\newcommand{\Stab}{\operatorname{Stab}}
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
\renewcommand{\refname}{来源与参考文献}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{2pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC：唯一来源、正交余量与门的递归}
\fancyhead[R]{\small v72 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
```

</div>
</details>



<details data-production="title">
<summary>原始制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="title">

```tex

\begin{center}
{\LARGE\bfseries\color{auricblue} 唯一来源、正交余量与门的递归}\\[9pt]
{\large 将“反者产生变化”写成可证明的二元结构}\\[7pt]
AURIC 量子起源研究\quad 定义、定理与纸面证明\quad v72.0\\[4pt]
2026 年 11 月 1 日\quad Asia/Singapore
\end{center}
```

</div>
</details>



# <span data-prose="0">唯一来源、正交余量与门的递归</span>



<span data-prose="1">将“反者产生变化”写成可证明的二元结构</span>

 <span data-prose="2">AURIC 量子起源研究</span>  <span data-prose="3">定义、定理与纸面证明</span>  <span data-prose="4">v72.0</span>

 <span data-prose="5">2026 年 11 月 1 日</span>  <span data-prose="6">Asia/Singapore</span>




## <span data-prose="7">摘要</span>



 <span data-prose="8">固定单位来源</span> <span data-formula="0">$\Omega$</span><span data-prose="9">，每个目标态唯一分解为</span> <span data-formula="1">$\psi=\alpha\Omega+r$</span><span data-prose="10">，其中</span> <span data-formula="2">$r\perp\Omega$</span> <span data-prose="11">且</span> <span data-formula="3">$|\alpha|^2+\|r\|^2=1$</span><span data-prose="12">。 正交余量给出离开参考射线的方向；由该方向构造的反厄米算符生成酉旋转。 在固定的二元有序基底中，完整归一系数对</span> <span data-formula="4">$(\alpha,\beta)$</span> <span data-prose="13">唯一确定一个</span> <span data-formula="5">$SU(2)$</span> <span data-prose="14">门，其复合、逆运算与复比值变换均可显式写出。 这为“商、余、反向与递归”的直观图像提供准确的数学对应。 一般维数下，端点对应稳定子纤维；正交余量不会独自保存完整门或有序脚本。 门可另以完整输入探针编码为量子态，再用相同商余结构分析。 来源锚定的余核保持全局正性，并给出串接公式</span> <span data-formula="6">$\alpha_{gh}=\alpha_g\alpha_h+\langle r_{g^{-1}},r_h\rangle$</span><span data-prose="15">。 以归一正关系、可逆接续及相容记录为明确前件，可重建循环 Hilbert 实现、酉历史和平方概率标定。 结论是条件性的量子重建框架，不是对“绝对最基础逻辑”或实际宇宙全部动力学的无条件证明。</span> 







## 1. <span data-prose="16">先保留画面，再把对象定准</span>



 <span data-prose="17">本轮最有力量的表达是：</span>**<span data-prose="18">同一个来源可以被分成保留的方向和正交余量； 二者的相干关系生成变化，变化又可继续用同一结构描述。</span>** <span data-prose="19">为了让它成为定理，需要分别指明“目标态”“可复用的门作用”与“保留顺序的脚本”。 这些对象可以全部在唯一本体内部，数学类型仍然不同。</span>

<span data-prose="20">本轮唯一实时 HEAD GET 于新加坡时间 2026-11-01 19:17:25 在收到 HTTP 响应前遇到网络权限拒绝；没有重试或取得新提交。 下文承接九份已核对 Git blob 的固定快照：</span> 

<span class="katex-display"><code><span data-prose="21">5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b</span></code></span><span data-prose="22">。</span>

 <span data-prose="23">不把它称为已验证的最新 HEAD；“v72”是本对话稿件编号。</span>




<blockquote data-editor-note="史料归属">

**编者限定（Markdown 编者；不属原稿）。** 关于 19:17:25 的实时 HEAD GET、HTTP 前网络权限拒绝、未重试、未取得新提交、九份 blob、查读范围及纸面方法的表述，均为原作者的历史报告，不表示本次编者重演了这些操作。固定提交保持为原文所标快照，不追索新的活动 HEAD。

</blockquote>



<details data-production="table-1">
<summary>原始制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="table-1">

```tex
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.23\textwidth}X@{}}
\toprule
项目既有结果 & 本轮承接与推进\\
\midrule
V55 §§2--4 & 正二元锥、单位旋量与 $SU(2)$、高维正交余量；写出准备门的复合与逆。\\
V22 §§5--6、8 & 稳定子、完整输入探针、正核重建及未来商；明确内容寻址的保真目标。\\
V52 §7 & 保相位二叉描述、Schur 余量与原生五模式编码；保留高维内部上下文。\\
$\Omega$ 纤维 §§4--5、7 & 算子逆、正历史档案、内生记录及静态传播核；区分完整态与局部读出。\\
V59 §6 & 持久记录、互补与链式一致性选择平方标定；保留几何前件。\\
\bottomrule
\end{tabularx}
```

</div>
</details>

<div class="katex-display" tabindex="0" role="region" aria-label="原表 1">

| <span data-prose="24">项目既有结果</span> | <span data-prose="25">本轮承接与推进</span> |
| --- | --- |
| <span data-prose="26">V55 §§2--4</span> | <span data-prose="27">正二元锥、单位旋量与</span> <span data-formula="7">$SU(2)$</span><span data-prose="28">、高维正交余量；写出准备门的复合与逆。</span> |
| <span data-prose="29">V22 §§5--6、8</span> | <span data-prose="30">稳定子、完整输入探针、正核重建及未来商；明确内容寻址的保真目标。</span> |
| <span data-prose="31">V52 §7</span> | <span data-prose="32">保相位二叉描述、Schur 余量与原生五模式编码；保留高维内部上下文。</span> |
| <span data-formula="8">$\Omega$</span> <span data-prose="33">纤维 §§4--5、7</span> | <span data-prose="34">算子逆、正历史档案、内生记录及静态传播核；区分完整态与局部读出。</span> |
| <span data-prose="35">V59 §6</span> | <span data-prose="36">持久记录、互补与链式一致性选择平方标定；保留几何前件。</span> |

</div>






<span data-prose="37">以下结果有标准线性代数、群作用和正核重建背景，不作经典定理的原创优先权声明。 全文为纸面推导；没有运行 CAS、数学数值计算、模拟、门候选枚举或数学测试。 复内积采用第一变量共轭线性、第二变量线性的约定。</span>



<blockquote data-editor-note="对象与内积">

**编者限定（Markdown 编者；不属原稿）。** 全文使用复 Hilbert 空间、单位来源及单位目标态；摘要中的平方和一也在该单位态条件下。外积 $|u\rangle\langle v|$ 表示 $x\mapsto u\langle v,x\rangle$。各门符号在其所声明空间上表示酉算子，群表示满足 $U_e=I$、$U_{g^{-1}}=U_g^\dagger$；这不是任意线性算子的结论。

</blockquote>



## 2. <span data-prose="38">“商与余”首先是一个唯一的正交分解</span>






#### 定义 2.1（<span data-prose="39">相对来源的商与余</span>）



 <span data-prose="40">固定</span> <span data-formula="9">$\|\Omega\|=1$</span><span data-prose="41">，置</span> <span data-formula="10">$P=|\Omega\rangle\langle{\Omega}|$</span><span data-prose="42">、</span><span data-formula="11">$Q=I-P$</span><span data-prose="43">。 对单位目标态</span> <span data-formula="12">$\psi$</span> <span data-prose="44">定义</span> 



<div data-formula="13">

$$
\alpha=\langle\Omega,\psi\rangle,\qquad r=Q\psi,\qquad b=\|r\|.
$$

</div>




<span data-formula="14">$r$</span> <span data-prose="45">是一个正交余向量，</span><span data-formula="15">$\Omega^\perp$</span> <span data-prose="46">是它所在的正交补空间。</span> 







<a id="thm-residual"></a>

#### 定理 2.2（<span data-prose="47">唯一商余与平方守恒</span>）



 <span data-prose="48">有唯一分解</span> 



<div data-formula="16">

$$
\boxed{\psi=\alpha\Omega+r,\quad r\perp\Omega,\quad |\alpha|^2+\|r\|^2=1.}
$$

</div>



 <span data-prose="49">而且对每个</span> <span data-formula="17">$\lambda\in\mathbb C$</span><span data-prose="50">，</span> 



<div data-formula="18">

$$
\|\psi-\lambda\Omega\|^2=|\alpha-\lambda|^2+\|r\|^2.
$$

</div>



 <span data-prose="51">故</span> <span data-formula="19">$\alpha$</span> <span data-prose="52">是相对参考方向的唯一最小二乘系数。</span> 






**证明。**




<span data-formula="20">$\langle\Omega,Q\psi\rangle=0$</span><span data-prose="53">。对任何另一种分解取与</span> <span data-formula="21">$\Omega$</span> <span data-prose="54">的内积， 立即得到相同系数，进而得到相同余量。范数式来自正交交叉项为零。</span> 



∎





<span data-prose="55">这是一种</span>*<span data-prose="56">正交商余</span>*<span data-prose="57">。它不是把两个向量当作域元素直接相除。 在复数域中，对非零</span> <span data-formula="22">$a$</span> <span data-prose="58">的普通除法</span> <span data-formula="23">$b=(b/a)a$</span> <span data-prose="59">没有非零余数； 非零余量来自选定参考子空间或另加的代表限制。</span>



#### 命题 2.3（<span data-prose="60">普通差向量不是这个余量</span>）



 <span data-prose="61">若</span> <span data-formula="24">$\psi,\Omega$</span> <span data-prose="62">都归一，则</span> 



<div data-formula="25">

$$
\psi-\Omega\perp\Omega\quad\Longleftrightarrow\quad\psi=\Omega.
$$

</div>











**证明。**



 <span data-prose="63">左侧给</span> <span data-formula="26">$\langle\Omega,\psi\rangle=1$</span><span data-prose="64">。 由定理</span> [2.2](#thm-residual) <span data-prose="65">得</span> <span data-formula="27">$\|r\|=0$</span><span data-prose="66">，于是</span> <span data-formula="28">$\psi=\Omega$</span><span data-prose="67">；反向显然。</span> 



∎





<span data-prose="68">所以非平凡变化对应的直角三角形，是</span> <span data-formula="29">$\alpha\Omega$</span><span data-prose="69">、</span><span data-formula="30">$r$</span><span data-prose="70">、</span><span data-formula="31">$\psi$</span><span data-prose="71">， 而不是通常的</span> <span data-formula="32">$\Omega$</span><span data-prose="72">、</span><span data-formula="33">$\psi-\Omega$</span><span data-prose="73">、</span><span data-formula="34">$\psi$</span><span data-prose="74">。 若只给</span> <span data-formula="35">$r$</span> <span data-prose="75">且</span> <span data-formula="36">$0<\|r\|<1$</span><span data-prose="76">，则</span> 



<div data-formula="37">

$$
\psi_\phi=e^{i\phi}\sqrt{1-\|r\|^2}\,\Omega+r
$$

</div>



 <span data-prose="77">有相同余量而一般有不同射线；必须把复系数也保留。</span>



## 3. <span data-prose="78">固定二元基底：商余二元对就是一个完整准备门</span>



 <span data-prose="79">固定有序正交基</span> <span data-formula="38">$(\Omega,\eta)$</span><span data-prose="80">，写</span> 



<div data-formula="39">

$$
\psi=\alpha\Omega+\beta\eta,\qquad |\alpha|^2+|\beta|^2=1.
$$

</div>



 <span data-prose="81">这里</span> <span data-formula="40">$\beta$</span> <span data-prose="82">是复数，区别于上一节的非负长度</span> <span data-formula="41">$b$</span><span data-prose="83">。</span>



<a id="thm-su2"></a>

#### 定理 3.1（<span data-prose="84">单位二元对与特殊酉门</span>）



 <span data-prose="85">每个归一二元对唯一确定</span> 



<div data-formula="42">

$$
\boxed{V(\alpha,\beta)=
\begin{pmatrix}\alpha&-\bar\beta\\\beta&\bar\alpha\end{pmatrix}\in SU(2),
\qquad V(\alpha,\beta)\Omega=\psi.}
$$

</div>



 <span data-prose="86">反向，每个</span> <span data-formula="43">$SU(2)$</span> <span data-prose="87">门都唯一具有此形式。</span> 






**证明。**



 <span data-prose="88">两列单位且正交，行列式为</span> <span data-formula="44">$|\alpha|^2+|\beta|^2=1$</span><span data-prose="89">。 若另一特殊酉矩阵有同一第一列，第二列必为</span> <span data-formula="45">$e^{i\chi}(-\bar\beta,\bar\alpha)^{\mathsf T}$</span><span data-prose="90">；行列式一强制</span> <span data-formula="46">$e^{i\chi}=1$</span><span data-prose="91">。</span> 



∎





<span data-prose="92">这是项目 V55 定理 3.2 的伴随写法：项目门把目标送回参考，本式把参考送到目标</span> [[2](#ref-v55)]<span data-prose="93">。</span>**<span data-prose="94">因此，在固定二元框架及</span> <span data-formula="47">$SU(2)$</span> <span data-prose="95">限制内，“门由完整商余对编码”确实成立。</span>**



<blockquote data-editor-note="V55 方向对应">

**编者限定（Markdown 编者；不属原稿）。** 在原有序基中令 V55 的目标列 $a=(\alpha,\beta)^{\mathsf T}$，其 $U_a=\bigl(\begin{smallmatrix}\bar\alpha&\bar\beta\\-\beta&\alpha\end{smallmatrix}\bigr)$ 满足 $U_a a=(1,0)^{\mathsf T}$；本节 $V(\alpha,\beta)=U_a^\dagger$。该伴随对应保留精确向量相位，并不把目标射线唯一性扩大到任意维数。

</blockquote>



<a id="thm-product"></a>

#### 定理 3.2（<span data-prose="96">复合与“反”的精确代数</span>）



 <span data-prose="97">以先作用右侧门为约定，</span> 



<div data-formula="48">

$$
\begin{aligned}
V(\alpha,\beta)V(\gamma,\delta)
 &=V(\alpha\gamma-\bar\beta\delta,\,
       \beta\gamma+\bar\alpha\delta),\\
V(\alpha,\beta)^{-1}
 &=V(\bar\alpha,-\beta).
\end{aligned}
$$

</div>



 <span data-prose="98">所得新系数仍归一。</span> 






**证明。**



 <span data-prose="99">矩阵乘积的第一列正是所列新系数。乘积仍属</span> <span data-formula="49">$SU(2)$</span><span data-prose="100">， 定理</span> [3.1](#thm-su2) <span data-prose="101">给完整矩阵及归一性。 取共轭转置得到逆式。</span> 



∎





<span data-prose="102">这给出可以直接使用的图像：</span>**<span data-prose="103">正向将商与余相干组合，逆向将商共轭并将余系数反号。</span>** <span data-prose="104">复合里有两条路径的加法和路径内部的乘法，还有保持复几何的共轭； 仅说“加法乘法”仍需说明这些关系结构。 这套乘法也可视为单位四元数的一种复二元表示， 但该名称不是量子起源证明所必需。</span>



#### 推论 3.3（<span data-prose="105">除法中的平方范数</span>）



 <span data-prose="106">将同一矩阵形式延伸到任意复二元对</span> <span data-formula="50">$p=(\alpha,\beta)$</span><span data-prose="107">， 定义</span> <span data-formula="51">$N(p)=|\alpha|^2+|\beta|^2$</span><span data-prose="108">、</span><span data-formula="52">$p^*=(\bar\alpha,-\beta)$</span><span data-prose="109">。 对定理</span> [3.2](#thm-product) <span data-prose="110">的乘法</span> <span data-formula="53">$\star$</span> <span data-prose="111">有</span> 



<div data-formula="54">

$$
N(p\star q)=N(p)N(q),\qquad
p^{-1}=\frac{p^*}{N(p)}\quad(p\ne0).
$$

</div>











**证明。**



 <span data-prose="112">相应矩阵满足</span> <span data-formula="55">$V(p)^\dagger V(p)=N(p)I$</span><span data-prose="113">， 而</span> <span data-formula="56">$V(p\star q)=V(p)V(q)$</span><span data-prose="114">。 对乘积取</span> <span data-formula="57">$V^\dagger V$</span> <span data-prose="115">给范数乘法性；再用</span> <span data-formula="58">$V(p^*)=V(p)^\dagger$</span> <span data-prose="116">得逆式。</span> 



∎





<span data-prose="117">因此二次范数同时控制归一化、复合和逆运算。 这是给定这套乘法与共轭后的数学强制关系； 它还不是对“为什么物理选择这套代数”问题的无前件回答。</span>



#### 命题 3.4（<span data-prose="118">除法坐标中的非线性来自比值</span>）



 <span data-prose="119">令复比值</span> <span data-formula="59">$\zeta=\beta/\alpha$</span><span data-prose="120">，并以</span> <span data-formula="60">$\infty$</span> <span data-prose="121">补上</span> <span data-formula="61">$\alpha=0$</span><span data-prose="122">。 门</span> <span data-formula="62">$V(a,b)$</span> <span data-prose="123">在射线坐标上的作用为</span> 



<div data-formula="63">

$$
\boxed{\zeta\longmapsto
\frac{b+\bar a\zeta}{a-\bar b\zeta}.}
$$

</div>











**证明。**



 <span data-prose="124">对代表</span> <span data-formula="64">$(1,\zeta)^{\mathsf T}$</span> <span data-prose="125">作矩阵乘法，再以第一分量相除。 分母为零时转入另一张坐标图。分子分母不同时为零，因为门可逆。</span> 



∎





<span data-prose="126">这是一个确切的“线性关系经除法变为非线性关系”的例子。 比值图上的非线性不自动表示额外物理维度；底层仍是二元复线性酉作用。</span>



## 4. <span data-prose="127">正交余量如何生成运动</span>



 <span data-prose="128">若</span> <span data-formula="65">$b>0$</span><span data-prose="129">，令</span> <span data-formula="66">$\eta=r/b$</span><span data-prose="130">。 在</span> <span data-formula="67">$S=\operatorname{span}\{\Omega,\eta\}$</span> <span data-prose="131">上用</span> <span data-formula="68">$V(\alpha,b)$</span><span data-prose="132">，在</span> <span data-formula="69">$S^\perp$</span> <span data-prose="133">上取恒等， 就得到一个把</span> <span data-formula="70">$\Omega$</span> <span data-prose="134">送到</span> <span data-formula="71">$\psi$</span> <span data-prose="135">的酉门。</span> <span data-formula="72">$S=\operatorname{span}\{\Omega,\psi\}$</span> <span data-prose="136">是包含两个线性独立端点的最小线性平面。 这是活动平面的最小性，并未优化原生词长或物理耗时。</span>



<a id="thm-generator"></a>

#### 定理 4.1（<span data-prose="137">由余方向生成酉旋转</span>）



 <span data-prose="138">先设</span> <span data-formula="73">$0<|\alpha|<1$</span><span data-prose="139">。写</span> <span data-formula="74">$\alpha=e^{i\phi}\cos\theta$</span><span data-prose="140">，</span> <span data-formula="75">$\theta\in(0,\pi/2)$</span><span data-prose="141">，并令</span> 



<div data-formula="76">

$$
\widetilde\psi=e^{-i\phi}\psi
=\cos\theta\,\Omega+\sin\theta\,\widetilde\eta,
\qquad \widetilde\eta=e^{-i\phi}r/b.
$$

</div>



 <span data-prose="142">定义</span> 



<div data-formula="77">

$$
\boxed{A=|\widetilde\eta\rangle\langle{\Omega}|-
|\Omega\rangle\langle{\widetilde\eta}|.}
$$

</div>



 <span data-prose="143">则</span> <span data-formula="78">$A^\dagger=-A$</span><span data-prose="144">，且</span> 



<div data-formula="79">

$$
\boxed{e^{\theta A}\Omega=\widetilde\psi,
\qquad(e^{\theta A})^{-1}=e^{-\theta A}.}
$$

</div>











**证明。**




<span data-formula="80">$A\Omega=\widetilde\eta$</span><span data-prose="145">、</span><span data-formula="81">$A\widetilde\eta=-\Omega$</span><span data-prose="146">，且</span> <span data-formula="82">$A$</span> <span data-prose="147">消去</span> <span data-formula="83">$S^\perp$</span><span data-prose="148">。 所以</span> <span data-formula="84">$A^2=-P_S$</span><span data-prose="149">，指数的奇偶幂合成</span> <span data-formula="85">$I+(\cos\theta-1)P_S+\sin\theta A$</span><span data-prose="150">。 反厄米性给指数酉，第一列给目标，取负号给逆。</span> 



∎





<span data-prose="151">若</span> <span data-formula="86">$\alpha=0$</span><span data-prose="152">，可取</span> <span data-formula="87">$\phi=0$</span><span data-prose="153">、</span><span data-formula="88">$\widetilde\eta=\psi$</span><span data-prose="154">、</span><span data-formula="89">$\theta=\pi/2$</span><span data-prose="155">； 此时单靠终点射线无法选定唯一相位约定。 若</span> <span data-formula="90">$b=0$</span><span data-prose="156">，射线不动，取</span> <span data-formula="91">$\theta=0$</span><span data-prose="157">；精确向量相位可由</span> <span data-formula="92">$\alpha P+Q$</span> <span data-prose="158">实现。 因此一般端点总可由某个酉连接，但指定物理门菜单的可达性仍须另证。</span>




<details data-production="tikz">
<summary>原始制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="tikz">

```tex
\begin{tikzpicture}[scale=.77,>=Stealth,font=\small]
\coordinate (O) at (0,0);\coordinate (B) at (3,0);\coordinate (T) at (3,4);
\draw[->,gray] (O)--(5.65,0) node[right] {$\Omega$ 方向};
\draw[->,gray] (O)--(0,5.1) node[above] {$\widetilde\eta$ 方向};
\draw[very thick,auricblue,->] (O)--(T) node[midway,left] {$\widetilde\psi$};
\draw[thick,auricblue,->] (O)--(B) node[midway,below=5pt] {$\cos\theta\,\Omega$};
\draw[thick,auricgold,->] (B)--(T) node[midway,right] {$\sin\theta\,\widetilde\eta$};
\draw[gray] (2.75,0)--(2.75,.25)--(3,.25);
\pic[draw,->,auricgold,angle radius=1.25cm] {angle=B--O--T};
\node[auricgold] at (1.55,.65) {$\theta$};
\node[align=left,text width=6cm] at (9,2.6)
{先对齐整体相位。\\[3pt]
目标态是两个正交分量之和。\\[3pt]
余方向决定活动平面；\\角度决定旋转幅度。\\[3pt]
真正的门生成元是 $A$。};
\end{tikzpicture}
```

</div>
</details>

<div class="katex-display" tabindex="0" role="region" aria-label="原图：相位对齐后的正交分量与生成元">
<img width="880" height="430" alt="原图：Ω 与 η̃ 轴、ψ̃、cos θ Ω、sin θ η̃、直角、θ 角弧，以及右侧相位对齐和生成元 A 的全部原文" src="data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSI4ODAiIGhlaWdodD0iNDMwIiB2aWV3Qm94PSIwIDAgODgwIDQzMCIgcm9sZT0iaW1nIiBhcmlhLWxhYmVsPSLljp8gVGlrWiDlm77nmoTlkIzlnZDmoIfnn6Lph4/ovazlhpkiPgo8dGl0bGU+55u45L2N5a+56b2Q5ZCO55qE5q2j5Lqk5YiG6YeP5LiO5peL6L2s55Sf5oiQ5YWDPC90aXRsZT4KPGRlZnM+PG1hcmtlciBpZD0idjcyLWdyYXktYXJyb3ciIG1hcmtlcldpZHRoPSI4IiBtYXJrZXJIZWlnaHQ9IjgiIHJlZlg9IjciIHJlZlk9IjQiIG9yaWVudD0iYXV0byI+PHBhdGggZD0iTTAsMCBMOCw0IEwwLDgiIGZpbGw9ImdyYXkiLz48L21hcmtlcj48bWFya2VyIGlkPSJ2NzItYmx1ZS1hcnJvdyIgbWFya2VyV2lkdGg9IjgiIG1hcmtlckhlaWdodD0iOCIgcmVmWD0iNyIgcmVmWT0iNCIgb3JpZW50PSJhdXRvIj48cGF0aCBkPSJNMCwwIEw4LDQgTDAsOCIgZmlsbD0iIzE4MzU0ZiIvPjwvbWFya2VyPjxtYXJrZXIgaWQ9InY3Mi1nb2xkLWFycm93IiBtYXJrZXJXaWR0aD0iOCIgbWFya2VySGVpZ2h0PSI4IiByZWZYPSI3IiByZWZZPSI0IiBvcmllbnQ9ImF1dG8iPjxwYXRoIGQ9Ik0wLDAgTDgsNCBMMCw4IiBmaWxsPSIjOTk2OTFkIi8+PC9tYXJrZXI+PC9kZWZzPgo8ZyBmb250LWZhbWlseT0ic3lzdGVtLXVpLCBQaW5nRmFuZyBTQywgc2Fucy1zZXJpZiIgZm9udC1zaXplPSIxOCI+CjxsaW5lIHgxPSI2NSIgeTE9IjM0NSIgeDI9IjM0Ny41IiB5Mj0iMzQ1IiBzdHJva2U9ImdyYXkiIG1hcmtlci1lbmQ9InVybCgjdjcyLWdyYXktYXJyb3cpIi8+PHRleHQgeD0iMzYwIiB5PSIzNTEiPs6pIOaWueWQkTwvdGV4dD4KPGxpbmUgeDE9IjY1IiB5MT0iMzQ1IiB4Mj0iNjUiIHkyPSI5MCIgc3Ryb2tlPSJncmF5IiBtYXJrZXItZW5kPSJ1cmwoI3Y3Mi1ncmF5LWFycm93KSIvPjx0ZXh0IHg9IjY1IiB5PSI2NSIgdGV4dC1hbmNob3I9Im1pZGRsZSI+zrfMgyDmlrnlkJE8L3RleHQ+CjxsaW5lIHgxPSI2NSIgeTE9IjM0NSIgeDI9IjIxNSIgeTI9IjE0NSIgc3Ryb2tlPSIjMTgzNTRmIiBzdHJva2Utd2lkdGg9IjMiIG1hcmtlci1lbmQ9InVybCgjdjcyLWJsdWUtYXJyb3cpIi8+PHRleHQgeD0iMTE2IiB5PSIyNDIiIGZpbGw9IiMxODM1NGYiPs+IzIM8L3RleHQ+CjxsaW5lIHgxPSI2NSIgeTE9IjM0NSIgeDI9IjIxNSIgeTI9IjM0NSIgc3Ryb2tlPSIjMTgzNTRmIiBzdHJva2Utd2lkdGg9IjIiIG1hcmtlci1lbmQ9InVybCgjdjcyLWJsdWUtYXJyb3cpIi8+PHRleHQgeD0iMTQwIiB5PSIzNzUiIGZpbGw9IiMxODM1NGYiIHRleHQtYW5jaG9yPSJtaWRkbGUiPmNvcyDOuCDOqTwvdGV4dD4KPGxpbmUgeDE9IjIxNSIgeTE9IjM0NSIgeDI9IjIxNSIgeTI9IjE0NSIgc3Ryb2tlPSIjOTk2OTFkIiBzdHJva2Utd2lkdGg9IjIiIG1hcmtlci1lbmQ9InVybCgjdjcyLWdvbGQtYXJyb3cpIi8+PHRleHQgeD0iMjMwIiB5PSIyNTAiIGZpbGw9IiM5OTY5MWQiPnNpbiDOuCDOt8yDPC90ZXh0Pgo8cGF0aCBkPSJNMjAyLjUsMzQ1IEwyMDIuNSwzMzIuNSBMMjE1LDMzMi41IiBmaWxsPSJub25lIiBzdHJva2U9ImdyYXkiLz4KPHBhdGggZD0iTTEyNy41LDM0NSBBNjIuNSw2Mi41IDAgMCAwIDEwMi41LDI5NSIgZmlsbD0ibm9uZSIgc3Ryb2tlPSIjOTk2OTFkIiBtYXJrZXItZW5kPSJ1cmwoI3Y3Mi1nb2xkLWFycm93KSIvPjx0ZXh0IHg9IjE0Mi41IiB5PSIzMTIuNSIgZmlsbD0iIzk5NjkxZCI+zrg8L3RleHQ+Cjx0ZXh0IHg9IjM2NSIgeT0iMTU0Ij48dHNwYW4geD0iMzY1Ij7lhYjlr7npvZDmlbTkvZPnm7jkvY3jgII8L3RzcGFuPjx0c3BhbiB4PSIzNjUiIGR5PSIzNSI+55uu5qCH5oCB5piv5Lik5Liq5q2j5Lqk5YiG6YeP5LmL5ZKM44CCPC90c3Bhbj48dHNwYW4geD0iMzY1IiBkeT0iMzUiPuS9meaWueWQkeWGs+Wumua0u+WKqOW5s+mdou+8mzwvdHNwYW4+PHRzcGFuIHg9IjM2NSIgZHk9IjI5Ij7op5LluqblhrPlrprml4vovazluYXluqbjgII8L3RzcGFuPjx0c3BhbiB4PSIzNjUiIGR5PSIzNSI+55yf5q2j55qE6Zeo55Sf5oiQ5YWD5pivIEHjgII8L3RzcGFuPjwvdGV4dD4KPC9nPjwvc3ZnPg=="/>
</div>




<blockquote data-editor-note="原图的文档转写">

**编者限定（Markdown 编者；不属原稿）。** 图形按原 TikZ 坐标保持 $O=(0,0)$、$B=(3,0)$、$T=(3,4)$，两轴端点 $(5.65,0)$、$(0,5.1)$，直角折线 $(2.75,0)\to(2.75,.25)\to(3,.25)$，原角弧及 $\theta$ 标签位置 $(1.55,.65)$。图中五条有向线段、中文与数学标签逐项保留；$\widetilde\psi$、$\cos\theta\,\Omega$、$\sin\theta\,\widetilde\eta$ 为示意标签，坐标长度 $3,4,5$ 不另作归一态数值。右侧原文位于 $(9,2.6)$，宽 $6\,\mathrm{cm}$；转写保留该布局关系和原文字。

</blockquote>








#### 推论 4.2（<span data-prose="159">反向余量与生成元反号</span>）



 <span data-prose="160">置</span> <span data-formula="93">$a=\cos\theta$</span><span data-prose="161">、</span><span data-formula="94">$b=\sin\theta$</span><span data-prose="162">，则</span> 



<div data-formula="95">

$$
\eta_{\rm rev}=b\Omega-a\widetilde\eta,\qquad
\Omega=a\widetilde\psi+b\eta_{\rm rev},\qquad
\eta_{\rm rev}\perp\widetilde\psi.
$$

</div>



 <span data-prose="163">由终点与反向余方向构造的生成元为</span> <span data-formula="96">$-A$</span><span data-prose="164">。</span> 






**证明。**



 <span data-prose="165">代入可验证正交、单位范数与分解。 展开</span> <span data-formula="97">$|\eta_{\rm rev}\rangle\langle{\widetilde\psi}| -|\widetilde\psi\rangle\langle{\eta_{\rm rev}}|$</span> <span data-prose="166">得</span> <span data-formula="98">$-A$</span><span data-prose="167">。</span> 



∎





<blockquote data-editor-note="反向公式的端点框架">

**编者限定（Markdown 编者；不属原稿）。** 该推论沿用已选的正交单位二元框架。若 $b=0$，原先的 $r/b$ 未定义；只有另给 $\Omega^\perp$ 中的单位方向后，才可将二元公式以 $a=1,b=0$ 延拓。复维数一时没有这样的方向，只保留前述相位门与常射线，不能在该情形断言存在反向单位余方向。

</blockquote>



<span data-prose="168">反向余向量通常不等于</span> <span data-formula="99">$-r$</span><span data-prose="169">，因为参考点已经改变。 因此“反者道之动”的可检验数学诠释是</span>*<span data-prose="170">生成元变号给逆向运动</span>*<span data-prose="171">， 并不把诗性表述本身当作物理定律的证明。</span>



#### 命题 4.3（<span data-prose="172">余量、射线距离与实际变化速度</span>）



 <span data-prose="173">采用</span> <span data-formula="100">$ds^2=\|d\psi\|^2-|\langle\psi,d\psi\rangle|^2$</span> <span data-prose="174">的 Fubini--Study 规范，有</span> 



<div data-formula="101">

$$
d_{\rm FS}([\Omega],[\psi])=\arccos|\alpha|=\theta,
\qquad\|r\|=\sin\theta.
$$

</div>



 <span data-prose="175">若另给可微归一态曲线，真正改变射线的切向为</span> <span data-formula="102">$v=(I-P_\psi)\dot\psi$</span><span data-prose="176">。 在另行指定薛定谔方程、并取有限维或有界自伴</span> <span data-formula="103">$H$</span> <span data-prose="177">时，</span> 



<div data-formula="104">

$$
v=-\frac i\hbar(H-\langle H\rangle_\psi)\psi,
\qquad\|v\|^2=\frac{\operatorname{Var}_\psi(H)}{\hbar^2}.
$$

</div>











**证明。**



 <span data-prose="178">曲线可选水平单位提升</span> <span data-formula="105">$z$</span><span data-prose="179">，满足</span> <span data-formula="106">$\langle z,\dot z\rangle=0$</span><span data-prose="180">。 写</span> <span data-formula="107">$c=\langle\Omega,z\rangle$</span><span data-prose="181">，把</span> <span data-formula="108">$\Omega=\bar c z+w$</span> <span data-prose="182">正交分解，得</span> <span data-formula="109">$|\dot c|\le\sqrt{1-|c|^2}\|\dot z\|$</span><span data-prose="183">。 故</span> <span data-formula="110">$|d\arccos|c|/dt|\le\|\dot z\|$</span><span data-prose="184">；端点以连续极限处理，积分给长度下界</span> <span data-formula="111">$\theta$</span><span data-prose="185">。 定理</span> [4.1](#thm-generator) <span data-prose="186">中</span> <span data-formula="112">$z(t)=\cos t\,\Omega+\sin t\,\widetilde\eta$</span> <span data-prose="187">为水平单位速曲线并达到下界。 最后两式由投影薛定谔方程及取范数直接得到。</span> 



∎





<span data-prose="188">这一速度联系属于标准量子态空间几何</span> [[8](#ref-aa)]<span data-prose="189">。 若使用非有界 Hamiltonian，还须要求态及曲线属于相应算符定义域。 这里的距离不是已经重建出的三维物理距离， 参数也不是从事件数自动导出的固有时间；这些识别需要额外动力学条件。</span>



<blockquote data-editor-note="距离与速度的适用条件">

**编者限定（Markdown 编者；不属原稿）。** 这里取沿实区间的分段 $C^1$ 归一曲线及其水平提升，并取 $\hbar\in\mathbb R\setminus\{0\}$；$P_\psi=|\psi\rangle\langle\psi|$、$\langle H\rangle_\psi=\langle\psi,H\psi\rangle$。$|c|$ 在零点的导数按几乎处处理解；可在 $0<|c|<1$ 上积分并用连续极限处理两端，得到距离下界。最小路径在 $\alpha=0$ 时用所列正交端点延拓，在 $b=0$ 时为常射线；不把未定义的 $r/b$ 带入端点。非有界 $H$ 的范数方差至少要求 $\psi\in D(H)$ 及强微分方程有意义；若将方差写成 $\langle H^2\rangle-\langle H\rangle^2$，还须 $\psi\in D(H^2)$。AA 文献只承担本稿明示的元数据、摘要及背景归属，本文的距离常数和证明不借用未读全文。

</blockquote>



## 5. <span data-prose="190">内容寻址：终态、完整门和有序历史各保留什么</span>






<a id="thm-fiber"></a>

#### 定理 5.1（<span data-prose="191">端点的门纤维</span>）



 <span data-prose="192">若</span> <span data-formula="113">$U_0\Omega=\psi$</span><span data-prose="193">，则</span> 



<div data-formula="114">

$$
\{U:U\Omega=\psi\}=U_0\operatorname{Stab}(\Omega),
\quad
\operatorname{Stab}(\Omega)=\{I_{\mathbb C\Omega}\oplus W:W\in U(\Omega^\perp)\}.
$$

</div>



 <span data-prose="194">只指定射线时，稳定子多出</span> <span data-formula="115">$\Omega$</span> <span data-prose="195">方向上的一个</span> <span data-formula="116">$U(1)$</span> <span data-prose="196">相位。</span> 






**证明。**




<span data-formula="117">$U\Omega=U_0\Omega$</span> <span data-prose="197">当且仅当</span> <span data-formula="118">$U_0^\dagger U$</span> <span data-prose="198">固定</span> <span data-formula="119">$\Omega$</span><span data-prose="199">。 酉性使其也保持</span> <span data-formula="120">$\Omega^\perp$</span><span data-prose="200">，所以恰为所述直和形式。</span> 



∎





<span data-prose="201">在有限</span> <span data-formula="121">$d$</span> <span data-prose="202">维，单位向量空间为</span> <span data-formula="122">$U(d)/U(d-1)$</span><span data-prose="203">， 射线空间为</span> <span data-formula="123">$U(d)/(U(1)\times U(d-1))$</span><span data-prose="204">。 这与固定二元</span> <span data-formula="124">$SU(2)$</span> <span data-prose="205">的唯一性没有冲突：该特例固定了基底和行列式， 而只保留射线还会遗失一个相位自由度。</span>

<span data-prose="206">最短反例取</span> <span data-formula="125">$\Omega=|0\rangle$</span><span data-prose="207">。</span> <span data-formula="126">$I\Omega=Z\Omega=\Omega$</span><span data-prose="208">，二者的</span> <span data-formula="127">$\alpha=1,r=0$</span> <span data-prose="209">完全相同； 但</span> <span data-formula="128">$I|+\rangle=|+\rangle$</span><span data-prose="210">、</span><span data-formula="129">$Z|+\rangle=|-\rangle$</span><span data-prose="211">。 所以端点内容不能直接充当可复用门在</span>*<span data-prose="212">其他输入</span>*<span data-prose="213">上的完整地址。 同时必须保留一个正面事实：两个相同的</span>*<span data-prose="214">完整物理终态</span>*<span data-prose="215">在相同后续操作</span> <span data-formula="130">$V$</span> <span data-prose="216">下， 当然得到相同的</span> <span data-formula="131">$V\psi$</span><span data-prose="217">。上述反例不是对这个事实的否定。</span>



<blockquote data-editor-note="纤维与维数">

**编者限定（Markdown 编者；不属原稿）。** 纤维集合的量词限于同一载体上的酉算子；有限维商空间式取整数 $d\ge1$，$U(0)$ 为平凡群。$gH$ 是左陪集，$U_0H$ 也是按右乘稳定子描述的纤维，二者术语相容。

</blockquote>



#### 命题 5.2（<span data-prose="218">端点商上的乘法条件</span>）



 <span data-prose="219">设</span> <span data-formula="132">$G$</span> <span data-prose="220">作用于</span> <span data-formula="133">$\Omega$</span><span data-prose="221">，</span><span data-formula="134">$H=\operatorname{Stab}_G(\Omega)$</span><span data-prose="222">。 端点类为左陪集空间</span> <span data-formula="135">$G/H$</span><span data-prose="223">，公式</span> <span data-formula="136">$(gH)(hH)=ghH$</span> <span data-prose="224">良定义当且仅当</span> <span data-formula="137">$H$</span> <span data-prose="225">为正规子群。</span> 






**证明。**



 <span data-prose="226">若正规，代表变化可移到乘积右端的</span> <span data-formula="138">$H$</span> <span data-prose="227">中。 反之，对</span> <span data-formula="139">$k\in H$</span> <span data-prose="228">有</span> <span data-formula="140">$kH=H$</span><span data-prose="229">，良定义性要求</span> <span data-formula="141">$khH=hH$</span><span data-prose="230">， 即</span> <span data-formula="142">$h^{-1}kh\in H$</span><span data-prose="231">；对</span> <span data-formula="143">$h^{-1}$</span> <span data-prose="232">再用同式给等号。</span> 



∎





<span data-prose="233">因此“内容即地址”必须指定地址对应的任务。 项目 V22 的未来稳定商和来源左模商正是在处理这一要求</span> [[1](#ref-v22)]<span data-prose="234">。</span>




<details data-production="table-2">
<summary>原始制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="table-2">

```tex
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.20\textwidth}XX@{}}
\toprule
内容类型 & 可以完整保存 & 仍不能仅凭它恢复\\
\midrule
完整态 $U_w\Omega$ & 当前态及固定后续操作的响应 & 门对任意其他输入的作用\\
完整门 $U_w$ & 所有输入上的作用 & 求值相同的不同有序脚本\\
保留的程序记录 $\ket w$ & 指定编码中的脚本字及顺序 & 未提供的执行器与操作资源\\
\bottomrule
\end{tabularx}
```

</div>
</details>

<div class="katex-display" tabindex="0" role="region" aria-label="原表 2">

| <span data-prose="235">内容类型</span> | <span data-prose="236">可以完整保存</span> | <span data-prose="237">仍不能仅凭它恢复</span> |
| --- | --- | --- |
| <span data-prose="238">完整态</span> <span data-formula="144">$U_w\Omega$</span> | <span data-prose="239">当前态及固定后续操作的响应</span> | <span data-prose="240">门对任意其他输入的作用</span> |
| <span data-prose="241">完整门</span> <span data-formula="145">$U_w$</span> | <span data-prose="242">所有输入上的作用</span> | <span data-prose="243">求值相同的不同有序脚本</span> |
| <span data-prose="244">保留的程序记录</span> <span data-formula="146">$\vert w\rangle$</span> | <span data-prose="245">指定编码中的脚本字及顺序</span> | <span data-prose="246">未提供的执行器与操作资源</span> |

</div>






<span data-formula="147">$gg^{-1}$</span> <span data-prose="247">与空字可以给同一算子而有不同事件数。 如果观察者保留这段历史，档案必须作为同一完整量子态的一部分； 不能一方面把它读掉，另一方面要求端点仍恢复它。 这些记录仍然是内生对象，不需要本体之外的观察者</span> [[4](#ref-omega)]<span data-prose="248">。</span>



## 6. <span data-prose="249">余量的关系继续递归：一个正核与精确串接律</span>



 <span data-prose="250">设</span> <span data-formula="148">$U_gU_h=U_{gh}$</span><span data-prose="251">，并令</span> 



<div data-formula="149">

$$
\psi_g=U_g\Omega,\quad \alpha_g=\langle\Omega,\psi_g\rangle,
\quad r_g=Q\psi_g,\quad K(g,h)=\langle\psi_g,\psi_h\rangle.
$$

</div>







<a id="thm-reskernel"></a>

#### 定理 6.1（<span data-prose="252">来源锚定的正交余核</span>）








<div data-formula="150">

$$
\boxed{R(g,h)=K(g,h)-\bar\alpha_g\alpha_h=\langle r_g,r_h\rangle}
$$

</div>



 <span data-prose="253">是正半定核。完整</span> <span data-formula="151">$K$</span> <span data-prose="254">可由</span> <span data-formula="152">$\alpha$</span> <span data-prose="255">与</span> <span data-formula="153">$R$</span> <span data-prose="256">无损恢复，并有</span> 



<div data-formula="154">

$$
|R(g,h)|^2\le(1-|\alpha_g|^2)(1-|\alpha_h|^2).
$$

</div>











**证明。**



 <span data-prose="257">将两态作正交分解，交叉项为零。 任意有限系数</span> <span data-formula="155">$c_g$</span> <span data-prose="258">满足</span> <span data-formula="156">$\sum\bar c_gR(g,h)c_h=\|\sum c_gr_g\|^2\ge0$</span><span data-prose="259">。 不等式是这些余向量的 Cauchy--Schwarz 不等式。</span> 



∎





<span data-prose="260">这正是“关系本身仍可分析”的可证明版本：从同源关系核扣除共同参考方向， 剩下的</span>*<span data-prose="261">整体</span>*<span data-prose="262">仍是正核。若某个</span> <span data-formula="157">$r_g=0$</span><span data-prose="263">，只说明该历史把来源送回同一射线； 不说明门是恒等，更不说明其他关系全都消失。</span>



<a id="thm-feedback"></a>

#### 定理 6.2（<span data-prose="264">余量参与串接的回流项</span>）








<div data-formula="158">

$$
\boxed{\alpha_{gh}
=\alpha_g\alpha_h+\langle r_{g^{-1}},r_h\rangle.}
$$

</div>



 <span data-prose="265">故</span> 



<div data-formula="159">

$$
|\alpha_{gh}-\alpha_g\alpha_h|
\le\sqrt{1-|\alpha_g|^2}\sqrt{1-|\alpha_h|^2}.
$$

</div>











**证明。**



 <span data-prose="266">由</span> <span data-formula="160">$U_{g^{-1}}\Omega=\bar\alpha_g\Omega+r_{g^{-1}}$</span><span data-prose="267">，</span> 



<div data-formula="161">

$$
\alpha_{gh}=\langle U_g^\dagger\Omega,U_h\Omega\rangle
=\langle\bar\alpha_g\Omega+r_{g^{-1}},
\alpha_h\Omega+r_h\rangle.
$$

</div>



 <span data-prose="268">展开即得第一式。反门与正门的来源重叠互为共轭， 所以其余量长度相同；再用 Cauchy--Schwarz 即得界。</span> 



∎





**<span data-prose="269">先前进入余空间的成分可以在下一次作用时回到参考方向， 并与原有成分相干相加。</span>**<span data-prose="270">这比“每一层不断丢弃余量”更符合封闭酉演化。 它也说明，若只把每层的平方模当作独立经典概率相乘，就会漏掉相干项。</span>



#### 命题 6.3（<span data-prose="271">保留全部门作用的递归块</span>）



 <span data-prose="272">在</span> <span data-formula="162">$\mathcal H=\mathbb C\Omega\oplus\Omega^\perp$</span> <span data-prose="273">上置</span> <span data-formula="163">$D_g=QU_gQ|_{\Omega^\perp}$</span><span data-prose="274">。则</span> 



<div data-formula="164">

$$
U_g=\begin{pmatrix}
\alpha_g&r_{g^{-1}}^\dagger\\r_g&D_g
\end{pmatrix},
$$

</div>








<div data-formula="165">

$$
\begin{aligned}
r_{gh}&=\alpha_h r_g+D_g r_h,\\
D_{gh}&=|r_g\rangle\langle{r_{h^{-1}}}|+D_gD_h.
\end{aligned}
$$

</div>











**证明。**



 <span data-prose="275">右上角作用于</span> <span data-formula="166">$x\perp\Omega$</span> <span data-prose="276">时为</span> <span data-formula="167">$\langle\Omega,U_gx\rangle=\langle r_{g^{-1}},x\rangle$</span><span data-prose="277">。 其余式由块乘法得到。</span> 



∎





<span data-formula="168">$D_g$</span> <span data-prose="278">保存余空间内部的关系；它一般是收缩而不是单独酉。 当</span> <span data-formula="169">$r_g=0$</span> <span data-prose="279">时，回流也为零，但</span> <span data-formula="170">$D_g$</span> <span data-prose="280">仍可为任意酉。 在固定二元</span> <span data-formula="171">$SU(2)$</span> <span data-prose="281">框架里，</span><span data-formula="172">$D_g=\bar\alpha_g$</span><span data-prose="282">， 因此恰好降为定理</span> [3.2](#thm-product) <span data-prose="283">的两个复数递归。</span>



## 7. <span data-prose="284">门本身也可编码成态，再作同样商余</span>



 <span data-prose="285">这一节使用有限维</span> <span data-formula="173">$H=\mathbb C^d$</span><span data-prose="286">，并声明内部有校准的完整输入探针。 探针和辅助寄存器属于同一本体；它们的可取得性不是从“唯一来源”一句话免费得到的。 项目 V22 命题 5.4 已给出此接口</span> [[1](#ref-v22)]<span data-prose="287">，也与标准 Choi 表示一致</span> [[6](#ref-watrous)]<span data-prose="288">。</span>



<blockquote data-editor-note="向量化与 Choi 约定">

**编者限定（Markdown 编者；不属原稿）。** 本节取正整数 $d$ 及固定校准正交基，$|B\rangle\!\rangle=\operatorname{vec}(B)/\sqrt d$。Watrous 的 $J(\Phi_B)=\operatorname{vec}(B)\operatorname{vec}(B)^\dagger=d|B\rangle\!\rangle\langle\!\langle B|$ 对 $\Phi_B(X)=BXB^\dagger$ 未归一化。其保迹条件迹掉输出因子，给 $(B^\dagger B)^{\mathsf T}=I$；本文 $\operatorname{Tr}_2$ 迹掉第二个输入参考因子，给 $BB^\dagger/d$。两条件只在本节有限、等输入输出维数下同为酉性判据。本文未缩放的 Hilbert--Schmidt 内积为 $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}(X^\dagger Y)$；所以无伴随的 $\operatorname{Tr}(A_UA_V)$ 与所写 HS 配对一致。

</blockquote>



#### 定义 7.1（<span data-prose="289">门态与恒等参考</span>）



 <span data-prose="290">令</span> 



<div data-formula="174">

$$
|\Phi_d\rangle=\frac1{\sqrt d}\sum_{j=1}^d|j\rangle\otimes|j\rangle,
\qquad |U\rangle\!\rangle=(U\otimes I)|\Phi_d\rangle.
$$

</div>




<span data-formula="175">$|I\rangle\!\rangle=|\Phi_d\rangle$</span> <span data-prose="291">是这张内部过程图表的参考， 不是第二个宇宙本体来源。</span> 







<a id="thm-choi"></a>

#### 定理 7.2（<span data-prose="292">完整门的正交商余</span>）



 <span data-prose="293">取</span> <span data-formula="176">$q_U=\operatorname{Tr}(U)/d$</span><span data-prose="294">、</span><span data-formula="177">$A_U=U-q_UI$</span><span data-prose="295">，则</span> 



<div data-formula="178">

$$
\boxed{|U\rangle\!\rangle=q_U|I\rangle\!\rangle+|A_U\rangle\!\rangle,
\quad \langle\!\langle I|A_U\rangle\!\rangle=0,}
$$

</div>








<div data-formula="179">

$$
|q_U|^2+\frac1d\operatorname{Tr}(A_U^\dagger A_U)=1.
$$

</div>



 <span data-prose="296">完整的</span> <span data-formula="180">$(q_U,A_U)$</span> <span data-prose="297">唯一恢复</span> <span data-formula="181">$U$</span><span data-prose="298">。门态射线唯一确定酉通道，即确定</span> <span data-formula="182">$U$</span> <span data-prose="299">到整体相位。</span> 






**证明。**



 <span data-prose="300">展开最大纠缠向量得到</span> <span data-formula="183">$\langle\!\langle V|U\rangle\!\rangle=\operatorname{Tr}(V^\dagger U)/d$</span><span data-prose="301">。 所以标量部分与无迹部分正交，酉性给总范数一。 该向量化映射在整个矩阵空间上线性单射，故完整向量恢复矩阵， 射线恢复矩阵到相位；相位在</span> <span data-formula="184">$U\rho U^\dagger$</span> <span data-prose="302">中消去。</span> 



∎





<span data-prose="303">这里特别重要的限制是：</span>**<span data-prose="304">门态归一，不等于门已酉。</span>** <span data-prose="305">对任意</span> <span data-formula="185">$B$</span><span data-prose="306">，</span><span data-formula="186">$\||B\rangle\!\rangle\|=1$</span> <span data-prose="307">只要求</span> <span data-formula="187">$\operatorname{Tr}(B^\dagger B)=d$</span><span data-prose="308">。 例如</span> <span data-formula="188">$d=2$</span> <span data-prose="309">时</span> <span data-formula="189">$B=\sqrt2|0\rangle\langle{0}|$</span> <span data-prose="310">满足该式却不可逆。</span> 

#### 命题 7.3（<span data-prose="311">酉门态的额外关系</span>）



 <span data-prose="312">对等输入输出维数，</span><span data-formula="190">$B$</span> <span data-prose="313">为酉当且仅当</span> 



<div data-formula="191">

$$
\operatorname{Tr}_2\bigl(|B\rangle\!\rangle\langle\!\langle B|\bigr)=I/d.
$$

</div>



 <span data-prose="314">等价地，对</span> <span data-formula="192">$B=qI+A$</span><span data-prose="315">，</span> 



<div data-formula="193">

$$
|q|^2I+\bar qA+qA^\dagger+A^\dagger A=I.
$$

</div>











**证明。**



 <span data-prose="316">直接展开得上述约化态为</span> <span data-formula="194">$BB^\dagger/d$</span><span data-prose="317">。 有限等维下</span> <span data-formula="195">$BB^\dagger=I$</span> <span data-prose="318">与</span> <span data-formula="196">$B^\dagger B=I$</span> <span data-prose="319">等价。 后一式为</span> <span data-formula="197">$(qI+A)^\dagger(qI+A)=I$</span> <span data-prose="320">的展开。</span> 



∎







#### 命题 7.4（<span data-prose="321">门态商余也对过程复合闭合</span>）








<div data-formula="198">

$$
\begin{aligned}
q_{UV}&=q_Uq_V+\frac1d\operatorname{Tr}(A_UA_V),\\
A_{UV}&=q_UA_V+q_VA_U+A_UA_V
-\frac1d\operatorname{Tr}(A_UA_V)I.
\end{aligned}
$$

</div>











**证明。**



 <span data-prose="322">展开</span> <span data-formula="199">$UV=(q_UI+A_U)(q_VI+A_V)$</span><span data-prose="323">，取迹并扣除标量部分。 这里</span> <span data-formula="200">$\operatorname{Tr}(A_UA_V)$</span> <span data-prose="324">故意不带伴随；它是</span> <span data-formula="201">$\langle A_U^\dagger,A_V\rangle_{\rm HS}$</span><span data-prose="325">，不能误写为通常的</span> <span data-formula="202">$\langle A_U,A_V\rangle_{\rm HS}$</span><span data-prose="326">。</span> 



∎





<span data-prose="327">由此，“门也是量子态”有完整而准确的实现。 但过程态所在空间的复维数为</span> <span data-formula="203">$d^2$</span><span data-prose="328">；高维信息并未消失。 若还要恢复脚本顺序，应再保留程序记录。 若要把程序态作为可执行控制，必须声明相应执行器；编码本身不是自动执行。</span>



## 8. <span data-prose="329">三轴提升与“无例外”的准确强度</span>






#### 命题 8.1（<span data-prose="330">二元系数的三轴读出</span>）



 <span data-prose="331">对固定基底中的归一</span> <span data-formula="204">$(\alpha,\beta)$</span><span data-prose="332">，定义</span> 



<div data-formula="205">

$$
\rho_{\alpha\beta}=
\begin{pmatrix}|\alpha|^2&\alpha\bar\beta\\
\bar\alpha\beta&|\beta|^2\end{pmatrix}
=\tfrac12(I+x\sigma_x+y\sigma_y+z\sigma_z).
$$

</div>



 <span data-prose="333">则</span> 



<div data-formula="206">

$$
\boxed{(x,y,z)=
(2\Re(\bar\alpha\beta),\,2\Im(\bar\alpha\beta),\,
|\alpha|^2-|\beta|^2),\quad x^2+y^2+z^2=1.}
$$

</div>



 <span data-prose="334">若</span> <span data-formula="207">$\alpha\ne0$</span><span data-prose="335">，以</span> <span data-formula="208">$\zeta=\beta/\alpha$</span> <span data-prose="336">表示，即</span> 



<div data-formula="209">

$$
(x,y,z)=\frac{(2\Re\zeta,2\Im\zeta,1-|\zeta|^2)}{1+|\zeta|^2}.
$$

</div>











**证明。**



 <span data-prose="337">逐项比较 Pauli 展开，并用</span> <span data-formula="210">$4|\alpha|^2|\beta|^2+(|\alpha|^2-|\beta|^2)^2=1$</span><span data-prose="338">。</span> 



∎








<details data-production="table-3">
<summary>原始制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="table-3">

```tex
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.29\textwidth}XX@{}}
\toprule
对象 & 几何与自由度 & 保真的范围\\
\midrule
归一二元向量 $(\alpha,\beta)$ & $S^3$，三个实自由度 & 保留整体相位约定\\
固定框架中的 $SU(2)$ 门 & 同一个 $S^3$ & 保留整个二元门作用\\
二元纯态的三轴点 & $S^2\subset\R^3$，两个实自由度 & 去掉共同 $U(1)$ 相位\\
一般二元密度矩阵 & 闭单位三维球 & 保留混合度及相干关系\\
高维二元分解节点 & 上述局部形式加内部上下文 & 另保留方向、尺度、支撑和跨节点关系\\
\bottomrule
\end{tabularx}
```

</div>
</details>

<div class="katex-display" tabindex="0" role="region" aria-label="原表 3">

| <span data-prose="339">对象</span> | <span data-prose="340">几何与自由度</span> | <span data-prose="341">保真的范围</span> |
| --- | --- | --- |
| <span data-prose="342">归一二元向量</span> <span data-formula="211">$(\alpha,\beta)$</span> | <span data-formula="212">$S^3$</span><span data-prose="343">，三个实自由度</span> | <span data-prose="344">保留整体相位约定</span> |
| <span data-prose="345">固定框架中的</span> <span data-formula="213">$SU(2)$</span> <span data-prose="346">门</span> | <span data-prose="347">同一个</span> <span data-formula="214">$S^3$</span> | <span data-prose="348">保留整个二元门作用</span> |
| <span data-prose="349">二元纯态的三轴点</span> | <span data-formula="215">$S^2\subset\mathbb R^3$</span><span data-prose="350">，两个实自由度</span> | <span data-prose="351">去掉共同</span> <span data-formula="216">$U(1)$</span> <span data-prose="352">相位</span> |
| <span data-prose="353">一般二元密度矩阵</span> | <span data-prose="354">闭单位三维球</span> | <span data-prose="355">保留混合度及相干关系</span> |
| <span data-prose="356">高维二元分解节点</span> | <span data-prose="357">上述局部形式加内部上下文</span> | <span data-prose="358">另保留方向、尺度、支撑和跨节点关系</span> |

</div>






<span data-prose="359">不能把</span> <span data-formula="217">$S^3$</span> <span data-prose="360">的“三个自由度”与</span> <span data-formula="218">$S^2$</span> <span data-prose="361">的“三个坐标”混为一件事。 同样，端点的归一 Gram 矩阵</span> <span data-formula="219">$\frac12\bigl(\begin{smallmatrix}1&\alpha\\\bar\alpha&1\end{smallmatrix}\bigr)$</span> <span data-prose="362">描述的是</span> <span data-formula="220">$\Omega$</span> <span data-prose="363">与</span> <span data-formula="221">$\psi$</span> <span data-prose="364">的关系；它与上式的</span>*<span data-prose="365">系数纯态</span>*<span data-prose="366">不同， 一般秩二，并没有包含高维余向量的全部方向。</span>

<span data-prose="367">项目的原生五模式接口仍可由固定等距</span> <span data-formula="222">$J:\mathbb C^2\to\mathbb C^5$</span> <span data-prose="368">接入。 其按</span> <span data-formula="223">$(F[1],F[3],F[2])$</span> <span data-prose="369">排列的三个占据均值为</span> <span data-formula="224">$u=u_0+\nu(x,y,z)$</span><span data-prose="370">，</span> <span data-formula="225">$\nu=(1+2\sqrt3+\sqrt{11})^{-1}$</span><span data-prose="371">，</span> <span data-formula="226">$u_0=(\nu(\sqrt3+\sqrt{11})/2,\nu(\sqrt3+\sqrt{11})/2,\nu)$</span><span data-prose="372">。 在保留其他内部标签时使用</span> <span data-formula="227">$J\otimes I$</span><span data-prose="373">。 该接口的纯态球、一般态球内与五模式归一化已有项目证明；</span> <span data-formula="228">$F[\mathrm{null}]$</span> <span data-prose="374">仍是事件标签，不是被省略的整体归一条件</span> [[3](#ref-v52)]<span data-prose="375">。</span>



<blockquote data-editor-note="五模式来源对应">

**编者限定（Markdown 编者；不属原稿）。** V52 §7 所用固定码来自同一快照 V37 §3（定义 3.1、定理 3.2 及证明）；V44 §§8--11 给奇异支撑、相干标签和算子上下文接口。V37 数值模式 $(0,2,3,5,25)$ 对应位置模式 $(\mathrm{null},1,2,3,13)$，故占据轴顺序为 $(F[1],F[3],F[2])$。$J\otimes I$ 只在所声明二元因子与其内部上下文上使用；不声称把所有节点同时变成独立可取得态。

</blockquote>



<a id="thm-closure"></a>

#### 定理 8.2（<span data-prose="376">全部复合二元关系正性等于全局正性</span>）



 <span data-prose="377">在形式有限复线性组合空间上，给 Hermitian 半双线性形式</span> <span data-formula="229">$B$</span><span data-prose="378">。 以下两项等价：</span> 






1.  <span data-prose="379">对每个有限组合</span> <span data-formula="230">$v$</span><span data-prose="380">，</span><span data-formula="231">$B(v,v)\ge0$</span><span data-prose="381">；</span> 
1.  <span data-prose="382">原始标签的对角非负，且任意非空、不交支撑的有限组合</span> <span data-formula="232">$v,w$</span> <span data-prose="383">的二阶 Gram 矩阵均半正定。</span> 












**证明。**



 <span data-prose="384">第一项对</span> <span data-formula="233">$av+bw$</span> <span data-prose="385">取二次型给全部二阶正性。 反向，对单支撑组合用对角条件；对多支撑组合</span> <span data-formula="234">$u$</span> <span data-prose="386">分为</span> <span data-formula="235">$u=v+w$</span><span data-prose="387">， 将二阶正矩阵在</span> <span data-formula="236">$(1,1)$</span> <span data-prose="388">上求二次型得到</span> <span data-formula="237">$B(u,u)\ge0$</span><span data-prose="389">。零向量单独显然。</span> 



∎





<span data-prose="390">这就是“无例外”的一个足够强版本：</span>**<span data-prose="391">同一约束也要覆盖所有关系的复合， 不能只覆盖原始对象对。</span>**<span data-prose="392">它已经量化到任意有限规模，不是只检查有限个二元小球。 一套普遍的局部格式可以组织任意大的关系网络；它不把整个网络压缩成三个实数。 二元表达也不是量子性独有：普通有限关系可加一个“合法元组标签”， 用它与各坐标的二元约束表达。量子重建真正使用的是相干复合、全局正性及可逆保核。</span>



## 9. <span data-prose="393">更简洁的公理候选：关系、可逆接续、记录</span>



 <span data-prose="394">这是一组明确的</span>*<span data-prose="395">条件重建前件</span>*<span data-prose="396">。 标题可以很短，但不能把标题背后的数学内容省略。</span>



#### 定义 9.1（<span data-prose="397">三个前件</span>）




**<span data-prose="398">R1：归一相干关系。</span>** <span data-prose="399">可逆操作的语义形成群</span> <span data-formula="238">$\Gamma$</span><span data-prose="400">，给定一个固定函数</span> <span data-formula="239">$f:\Gamma\to\mathbb C$</span><span data-prose="401">， 使</span> <span data-formula="240">$f(e)=1$</span><span data-prose="402">、</span><span data-formula="241">$f(g^{-1})=\overline{f(g)}$</span><span data-prose="403">，并令</span> 



<div data-formula="242">

$$
K(g,h)=f(g^{-1}h).
$$

</div>



 <span data-prose="404">要求全部有限复合关系满足定理</span> [8.2](#thm-closure) <span data-prose="405">的二元正性。 “唯一来源”体现在整套历史共享这个固定核，而不是每次另选一个来源。</span>

**<span data-prose="406">R2：可逆接续保持全部关系。</span>** <span data-prose="407">接续为</span> <span data-formula="243">$h\mapsto gh$</span><span data-prose="408">，包含合法逆，并保持完整核。 对上述形式的</span> <span data-formula="244">$K$</span><span data-prose="409">，共同左接续不变自动成立； 可把 R1、R2 合并写为“一个归一正定型群函数”。 字面脚本档案不是这个语义群中的约消结果；要保留时另作为内部记录。</span>

**<span data-prose="410">R3：分类与记录相容。</span>** <span data-prose="411">分支更新保留全部交叉关系，满足下文的分支核恒等式。 概率标定对持久正交记录采用同一个径向函数、互补归一及链式一致性。 参考、程序、执行器与记录属于同一表示中的声明对象；需要的接口须实际供应。</span> 







<a id="thm-gns"></a>

#### 定理 9.2（<span data-prose="412">由同源关系重建态与酉历史</span>）



 <span data-prose="413">R1、R2 给出一个 Hilbert 空间</span> <span data-formula="245">$\mathcal H_K$</span><span data-prose="414">、一个单位来源</span> <span data-formula="246">$\Omega$</span> <span data-prose="415">和酉表示</span> <span data-formula="247">$U_g$</span><span data-prose="416">，使</span> 



<div data-formula="248">

$$
\boxed{K(g,h)=\langle U_g\Omega,U_h\Omega\rangle,
\qquad f(g)=\langle\Omega,U_g\Omega\rangle.}
$$

</div>




<span data-formula="249">$\{U_g\Omega\}$</span> <span data-prose="417">的线性张成稠密；这样的最小实现唯一到保持标签的酉同构。</span> 






**证明。**



 <span data-prose="418">在形式历史的有限复线性空间中定义</span> <span data-formula="250">$\langle\sum a_g[g],\sum b_h[h]\rangle =\sum\bar a_gb_hK(g,h)$</span><span data-prose="419">。 正性给 Cauchy--Schwarz，故零范数向量与所有向量正交。 除去零空间并完备化得到</span> <span data-formula="251">$\mathcal H_K$</span><span data-prose="420">，取</span> <span data-formula="252">$\Omega=[e]$</span><span data-prose="421">。 左接续保持内积，因而下降并延拓为等距；逆接续给满射，故为酉。 标签像为</span> <span data-formula="253">$U_g\Omega$</span><span data-prose="422">，自然稠密张成。 两个最小实现间按标签线性对应，保持范数，延拓得到唯一酉同构。</span> 



∎





<span data-prose="423">这是正核/GNS 传统的历史形式，项目 V22 已有相应构造</span> [[1](#ref-v22), [7](#ref-gns)]<span data-prose="424">。 它重建被声明历史探及的最小部分，并没有从本体唯一性独立决定</span> <span data-formula="254">$f$</span><span data-prose="425">。 循环张成也不意味着每个 Hilbert 向量都能由一条受限菜单的历史精确制备。 若允许所有数学酉，任意单位向量当然可由定理</span> [4.1](#thm-generator) <span data-prose="426">的延拓连接； 若只给有限或可数固定门菜单，有限字至多可数，不能精确覆盖连续的全部纯态。 近似稠密、可数无限极限和带连续控制的精确可达是三种不同声明。</span>



<blockquote data-editor-note="GNS 约定与可达性">

**编者限定（Markdown 编者；不属原稿）。** MIT 讲义定理 4.1 使用含单位 $C^*$ 代数的态及第一变量线性的 $\langle a,b\rangle=\varphi(b^*a)$；交换内积参数后为本稿第二变量线性的 $\varphi(a^*b)$。本稿直接在群的形式有限和上用正定核构造商与完备化，左乘群元已保范数，故无需把一个尚未供应的 $C^*$ 范数当前提。最小循环实现唯一不意味着表示忠实、$f$ 唯一或拓扑强连续。有限字可数排除覆盖全部纯态射线的结论，须在目标纯态集不可数时使用，例如复维数至少二；一维只有一个纯态射线，是该措辞的退化例外。

</blockquote>



#### 定理 9.3（<span data-prose="427">分类记录给等距仪器</span>）



 <span data-prose="428">设</span> <span data-formula="255">$K_+$</span> <span data-prose="429">为后继标签上的正核，允许次归一化和零标签。 记</span> <span data-formula="256">$\xi_w=[w]\in\mathcal H_K$</span><span data-prose="430">、</span><span data-formula="257">$\xi_z^+=[z]\in\mathcal H_+$</span> <span data-prose="431">为相应正核构造的典范标签向量。 有限分支更新</span> <span data-formula="258">$t_s$</span> <span data-prose="432">满足对所有</span> <span data-formula="259">$v,w$</span>




<div data-formula="260">

$$
\boxed{K(v,w)=\sum_sK_+(t_s v,t_s w).}
$$

</div>



 <span data-prose="433">则有良定义收缩</span> <span data-formula="261">$M_s:\mathcal H_K\to\mathcal H_+$</span><span data-prose="434">，满足</span> <span data-formula="262">$M_s\xi_w=\xi^+_{t_sw}$</span> <span data-prose="435">及</span> <span data-formula="263">$\sum_sM_s^\dagger M_s=I$</span><span data-prose="436">。 因此</span> <span data-formula="264">$T\psi=\sum_sM_s\psi\otimes|s\rangle$</span> <span data-prose="437">等距。</span> 






**证明。**



 <span data-prose="438">以</span> <span data-formula="265">$\bar c_vc_w$</span> <span data-prose="439">乘核恒等式并求和，得到所有有限组合的范数守恒。 零范数组合在每个分支仍为零，故映射在商上良定义；各分支范数有统一界， 可延拓到完备化。守恒式极化给算符恒等式，正交记录再给</span> <span data-formula="266">$T^\dagger T=I$</span><span data-prose="440">。</span> 



∎





<span data-prose="441">只保存每个历史自身的总质量，不足保证这条交叉关系。 等距记录可在适当内部初始化辅助空间中扩充为酉； 单独的分支条件归一映射则一般非线性，也不等于整个等距。</span>



<blockquote data-editor-note="酉扩张的载体容量">

**编者限定（Markdown 编者；不属原稿）。** 有限分支求和给 $T:\mathcal H_K\to\mathcal H_+\otimes\mathbb C^{|S|}$。要把它写作同一整体上的酉作用，须先给定初始化嵌入，并使初始化子空间的正交补与 $\operatorname{Ran}T$ 的正交补具有相同 Hilbert 维数；必要时扩大两侧辅助载体。有限维时可通过补齐两边正交基完成；无限维时等距本身不保证在原空间上可扩成酉。该辅助容量和初始化是另给的内部资源。

</blockquote>



#### 定理 9.4（<span data-prose="442">递归记录唯一选择平方标定</span>）



 <span data-prose="443">设共同径向标定</span> <span data-formula="267">$h:[0,1]\to[0,1]$</span> <span data-prose="444">满足</span> <span data-formula="268">$h(0)=0,h(1)=1$</span><span data-prose="445">。 以下互补与嵌套规则对任意</span> <span data-formula="269">$r,s\in[0,1]$</span> <span data-prose="446">适用。 要求正交互补</span> <span data-formula="270">$h(r)+h(\sqrt{1-r^2})=1$</span><span data-prose="447">； 持久记录中的子事件属于父事件，条件幅度</span> <span data-formula="271">$s$</span> <span data-prose="448">与父幅度</span> <span data-formula="272">$r$</span> <span data-prose="449">给终幅</span> <span data-formula="273">$rs$</span><span data-prose="450">； 终幅充分、共同条件标定及概率链式律成立，零质量父事件的子事件质量为零。 则</span> <span data-formula="274">$h(r)=r^2$</span><span data-prose="451">。</span> 






**证明。**



 <span data-prose="452">正质量时链式律给</span> <span data-formula="275">$h(rs)=h(r)h(s)$</span><span data-prose="453">；零质量时由子事件包含及终幅充分得到同式。 令</span> <span data-formula="276">$F(t)=h(\sqrt t)$</span><span data-prose="454">，则</span> <span data-formula="277">$F(xy)=F(x)F(y)$</span><span data-prose="455">、</span><span data-formula="278">$F(t)+F(1-t)=1$</span><span data-prose="456">。 若</span> <span data-formula="279">$x,y\ge0$</span> <span data-prose="457">且</span> <span data-formula="280">$a=x+y\le1$</span><span data-prose="458">，</span><span data-formula="281">$a>0$</span> <span data-prose="459">时</span> 



<div data-formula="282">

$$
F(x)+F(y)=F(a)\{F(x/a)+F(y/a)\}=F(a).
$$

</div>




<span data-formula="283">$a=0$</span> <span data-prose="460">由端点条件成立。非负可加给单调性，归一化给有理点上的</span> <span data-formula="284">$F(q)=q$</span><span data-prose="461">， 有理夹逼给全部</span> <span data-formula="285">$F(t)=t$</span><span data-prose="462">，故</span> <span data-formula="286">$h(r)=r^2$</span><span data-prose="463">。</span> 



∎





<span data-prose="464">于是</span> <span data-formula="287">$p(s|g)=\|M_sU_g\Omega\|^2$</span><span data-prose="465">；尖锐测量取</span> <span data-formula="288">$M_s=P_s$</span><span data-prose="466">。 项目 V59 已给该证明及记录擦除后不能套用同一经典事件链的条件</span> [[5](#ref-v59)]<span data-prose="467">。 平方几何的位置是公开的：互补幅度</span> <span data-formula="289">$\sqrt{1-r^2}$</span> <span data-prose="468">已使用正交二次范数。 这没有从无结构的“存在量词”独立推导二次几何，也没有省掉复数域及共同相干条件。</span>



<blockquote data-editor-note="记录概率与尖锐测量">

**编者限定（Markdown 编者；不属原稿）。** $p(s|g)$ 是单位输入历史的分支概率，不在零概率事件上定义条件概率。写 $M_s=P_s$ 时须将输入输出载体识别，并给彼此正交且和为 $I$ 的有限投影族；一般 $M_s$ 的输入、输出空间可不同。任意实 $r,s$ 的共同标定、持久记录与互补几何都是原定理全称前件，不能从个别可用读口推得。

</blockquote>



## 10. <span data-prose="469">无界递归可稳定；但“余量”必须相对明确任务</span>



 <span data-prose="470">固定源可以支持无限递归而不导致总质量发散。 承接 v71 的纸面模型，令</span> 

<blockquote data-editor-note="V71 前身来源">

**编者限定（Markdown 编者；不属原稿）。** 此处前身为作者提供的 v71.0 原稿《通用二元关系核、商余与无界递归》中的双边移位、分类尾态、历史核及额外反射模型。其模型与证明按原始 TeX 核对；这项归属不引用同轮在制 Markdown，也不把前身的过程报告当作本次操作。以下级数与投影等式均为本节纸面论证范围。

</blockquote>





<div data-formula="290">

$$
\mathcal H=\ell^2(\mathbb Z),\qquad Se_j=e_{j+1},\qquad
\Omega=\sum_{j\ge1}2^{-j/2}e_j.
$$

</div>




<span data-formula="291">$S$</span> <span data-prose="471">是双边移位，真正酉；</span><span data-formula="292">$\|\Omega\|^2=\sum_{j\ge1}2^{-j}=1$</span><span data-prose="472">。 令</span> <span data-formula="293">$P_n$</span> <span data-prose="473">投影到</span> <span data-formula="294">$e_1,\ldots,e_n$</span><span data-prose="474">，</span><span data-formula="295">$P_0=0$</span><span data-prose="475">，</span><span data-formula="296">$\tau_n=S^n\Omega$</span><span data-prose="476">。</span>



#### 定理 10.1（<span data-prose="477">同一模型中两种余量的不同趋势</span>）



 <span data-prose="478">对每个整数</span> <span data-formula="297">$n\ge0$</span><span data-prose="479">，</span> 



<div data-formula="298">

$$
\underbrace{\|(I-P_n)\Omega\|^2}_{\text{分类尾余量}}=2^{-n},
\qquad
\underbrace{\|(I-P_\Omega)\tau_n\|^2}_{\text{相对来源的余量}}=1-2^{-n}.
$$

</div>



 <span data-prose="480">并有相同二元模板递归</span> 



<div data-formula="299">

$$
\tau_n=\frac{e_{n+1}+\tau_{n+1}}{\sqrt2},
\qquad e_{n+1}\perp\tau_{n+1}.
$$

</div>











**证明。**



 <span data-prose="481">级数移位给</span> <span data-formula="300">$(I-P_n)\Omega=2^{-n/2}\tau_n$</span><span data-prose="482">，从而得第一式及模板。 重叠的共同支撑为</span> <span data-formula="301">$j\ge n+1$</span><span data-prose="483">，故</span> 



<div data-formula="302">

$$
\langle\Omega,S^n\Omega\rangle
=\sum_{j\ge n+1}2^{-j/2}2^{-(j-n)/2}=2^{-n/2}.
$$

</div>



 <span data-prose="484">定理</span> [2.2](#thm-residual) <span data-prose="485">给第二式。</span> 



∎





<span data-prose="486">一个余量缩小，另一个增大；两者都与全局酉性相容。 所以“误差”要说明相对于哪项任务和哪个参考，不能仅凭归一化断言它单调缩小。 在此模型里，分类每个有限层都有非零尾项，极限为零； 归一尾态自身始终是同一</span> <span data-formula="303">$\Omega$</span> <span data-prose="487">的酉轨道。 此处稳定指分类尾质量趋零；归一尾态</span> <span data-formula="304">$\tau_n$</span> <span data-prose="488">并不范数收敛， 因为相邻两项的距离平方始终为</span> <span data-formula="305">$2-\sqrt2$</span><span data-prose="489">。</span>

<span data-prose="490">若要求每个</span> <span data-formula="306">$P_n$</span> <span data-prose="491">也由有限门菜单关联，另给内部反射</span> <span data-formula="307">$T=I-2|e_1\rangle\langle{e_1}|$</span><span data-prose="492">。 其移位共轭</span> <span data-formula="308">$T_j=S^{j-1}TS^{-(j-1)}$</span> <span data-prose="493">满足</span> <span data-formula="309">$\prod_{j=1}^nT_j=I-2P_n$</span><span data-prose="494">。 因此菜单</span> <span data-formula="310">$\{S,S^{-1},T\}$</span> <span data-prose="495">给每个有限分类反射； 真正读出分支仍按上一节的记录接口实现。 这项额外门资源是明示的，不从</span> <span data-formula="311">$S$</span> <span data-prose="496">单独推出。</span>

<span data-prose="497">无界递归与有限总质量因此相容。 但“每项分类永不结束”不是二元结构的逻辑结论：若目标已经位于一个有限已解析子空间， 正交余量便为零。</span>*<span data-prose="498">规则可无限延展、指定轨迹永不停止、指定误差趋零</span>* <span data-prose="499">是三项可以分别定义和证明的性质。</span>



## 11. <span data-prose="500">本轮得到的简洁结构及其物理边界</span>



 <span data-prose="501">最贴近直觉且已经有完整证明的表述是</span> 



<div data-formula="312">

$$
\boxed{\text{同源商余分解}\ +\ \text{相干关系的递归复合}\ +\ \text{完整归一化}.}
$$

</div>



 <span data-prose="502">其中“反”在二元门内给出具体公式</span> 



<div data-formula="313">

$$
(\alpha,\beta)^{-1}=(\bar\alpha,-\beta),
\qquad
(e^{\theta A})^{-1}=e^{-\theta A}.
$$

</div>



 <span data-prose="503">“关系继续连接关系”则由</span> 



<div data-formula="314">

$$
\boxed{\alpha_{gh}=\alpha_g\alpha_h+
\langle r_{g^{-1}},r_h\rangle}
$$

</div>



 <span data-prose="504">给出真实的相干回流，而不是比喻。</span>




<details data-production="table-4">
<summary>原始制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="table-4">

```tex
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.25\textwidth}X@{}}
\toprule
已经建立 & 证明成立的范围\\
\midrule
唯一商余、二次守恒 & 已给定正定复内积与参考方向。\\
商余二元对编码门 & 固定有序二元基底与 $SU(2)$；一般维数保留余空间作用。\\
门也作为态 & 校准完整输入探针与相应内部资源；过程态不等于脚本。\\
“无例外”正性闭合 & 要求全部有限复合关系，不仅原始两两块。\\
唯一来源与酉历史 & 给定归一正定型历史函数；唯一到实现同构。\\
平方概率 & 正交二次几何、持久记录、共同标定与链式一致性。\\
无界而稳定的递归 & 明确无限模型及参考任务；不是每个问题都必须永不结束。\\
\bottomrule
\end{tabularx}
```

</div>
</details>

<div class="katex-display" tabindex="0" role="region" aria-label="原表 4">

| <span data-prose="505">已经建立</span> | <span data-prose="506">证明成立的范围</span> |
| --- | --- |
| <span data-prose="507">唯一商余、二次守恒</span> | <span data-prose="508">已给定正定复内积与参考方向。</span> |
| <span data-prose="509">商余二元对编码门</span> | <span data-prose="510">固定有序二元基底与</span> <span data-formula="315">$SU(2)$</span><span data-prose="511">；一般维数保留余空间作用。</span> |
| <span data-prose="512">门也作为态</span> | <span data-prose="513">校准完整输入探针与相应内部资源；过程态不等于脚本。</span> |
| <span data-prose="514">“无例外”正性闭合</span> | <span data-prose="515">要求全部有限复合关系，不仅原始两两块。</span> |
| <span data-prose="516">唯一来源与酉历史</span> | <span data-prose="517">给定归一正定型历史函数；唯一到实现同构。</span> |
| <span data-prose="518">平方概率</span> | <span data-prose="519">正交二次几何、持久记录、共同标定与链式一致性。</span> |
| <span data-prose="520">无界而稳定的递归</span> | <span data-prose="521">明确无限模型及参考任务；不是每个问题都必须永不结束。</span> |

</div>






<span data-prose="522">因此可以把它作为比逐条列量子公理更统一的</span>*<span data-prose="523">重建组织方式</span>*<span data-prose="524">。 要宣称它是“数学逻辑上最基础且无其他可能”的系统，还需规定比较对象与最小性标准， 并证明实结构、经典结构等反模型为何不满足某项更基础的操作前件。 要宣称已经解释实际宇宙，还需从同一更弱前件推出可取得的操作、复合规则、动力学和可检验预测。 本轮没有用“凡物皆可编码”替代这些证明。</span>

<span data-prose="525">你的图像可以保持朴素：</span>**<span data-prose="526">沿着已有方向留下商，在正交方向留下余； 两者相干组合成新的态，逆向生成元将它转回； 所有层都遵守相同关系，但每一层应保留的内容也都算在这个世界之内。</span>**



## <span data-prose="527">来源与参考文献</span>



<a id="ref-v22"></a>

**[1]**  <span data-prose="528">项目固定快照。</span> [<span data-prose="529">V22：相对门历史与观察商</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)<span data-prose="530">， 重点 §§5--6、8；完整门探针为命题 5.4。</span> 



<a id="ref-v55"></a>

**[2]**  <span data-prose="531">项目固定快照。</span> [<span data-prose="532">V55：二元关系的外代数闭合与三轴误差</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md)<span data-prose="533">，§§2--4。</span> 



<a id="ref-v52"></a>

**[3]**  <span data-prose="534">项目固定快照。</span> [<span data-prose="535">V52：纯态商几何与无损递归</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)<span data-prose="536">，§7。</span> 



<a id="ref-omega"></a>

**[4]**  <span data-prose="537">项目固定快照。</span> [<span data-formula="316">$\Omega$</span> <span data-prose="538">静态相融纤维理论</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)<span data-prose="539">，§§4--5、7。</span> 



<a id="ref-v59"></a>

**[5]**  <span data-prose="540">项目固定快照。</span> [<span data-prose="541">V59：局部层析、相干读出口轨道与量子正性起源</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md)<span data-prose="542">，§6。</span> 



<a id="ref-watrous"></a>

**[6]**  <span data-prose="543">John Watrous.</span> *<span data-prose="544">The Theory of Quantum Information</span>*<span data-prose="545">. Cambridge University Press, 2018.</span> [<span data-prose="546">作者公开第 2 章</span>](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)<span data-prose="547">， §2.2.2、推论 2.27、§2.2.3 的酉通道。</span> 



<a id="ref-gns"></a>

**[7]**  <span data-prose="548">Kobi Kremnizer.</span> [<span data-prose="549">MIT 18.238，Lecture 3</span>](https://math.mit.edu/classes/18.238/lec100208.pdf)<span data-prose="550">，2008， §4，Gelfand--Naimark--Segal 构造，定理 4.1。</span> 



<a id="ref-aa"></a>

**[8]**  <span data-prose="551">J. Anandan and Y. Aharonov.</span> *<span data-prose="552">Geometry of quantum evolution</span>*<span data-prose="553">. Physical Review Letters 65, 1697--1700 (1990).</span> [<span data-prose="554">doi:10.1103/PhysRevLett.65.1697</span>](https://doi.org/10.1103/PhysRevLett.65.1697)<span data-prose="555">。 本轮核对出版元数据与摘要；文内距离及速度公式另给自足证明。</span> 



<details data-production="ending">
<summary>原始制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="ending">

```tex
\end{thebibliography}
\end{document}
```

</div>
</details>


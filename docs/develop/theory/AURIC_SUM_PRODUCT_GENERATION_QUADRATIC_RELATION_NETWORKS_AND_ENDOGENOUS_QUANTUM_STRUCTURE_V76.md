# 加乘生成、二次关系网与内生量子结构

> **来源与文献属性。** AI AURIC research continuation 原稿，由用户在会话 `01a15590-6264-7c80-8c48-21290deed496` 于 2026-11-01 提供。本文为完整作者稿的 Markdown 参考输入，不是 Lean 数学真值或新的物理认证。原稿的历史访问、阅读与方法报告均为作者署名的文献陈述；本次编者没有执行其中所述实时 HEAD 请求。下文“编者注”由本次 Markdown 实施者负责，和原文分开。

<details>
<summary>原稿的完整前置设置（逐行保留；正文采用 Markdown 排版）</summary>

<div>
<code>% !TeX progr<wbr>am = xelatex<wbr></code><br>
<code>% Compile tw<wbr>ice. Optiona<wbr>l: \def\AURI<wbr>CFontPath{/a<wbr>bsolute/path<wbr>/to/fonts/}<wbr></code><br>
<code>% Paper math<wbr>ematics only<wbr>; no mathema<wbr>tical progra<wbr>ms or numeri<wbr>cal verifica<wbr>tion.<wbr></code><br>
<code>\documentcla<wbr>ss[11pt,a4pa<wbr>per]{article<wbr>}<wbr></code><br>
<code>\usepackage[<wbr>margin=23mm,<wbr>headheight=1<wbr>6pt]{geometr<wbr>y}<wbr></code><br>
<code>\usepackage{<wbr>fontspec}<wbr></code><br>
<code>\ifdefined\A<wbr>URICFontPath<wbr></code><br>
<code> \setmainfon<wbr>t[Path=\AURI<wbr>CFontPath,Bo<wbr>ldFont=NotoS<wbr>erifCJKsc-Bo<wbr>ld.otf,<wbr></code><br>
<code> ItalicFont=<wbr>NotoSerifCJK<wbr>sc-Regular.o<wbr>tf,BoldItali<wbr>cFont=NotoSe<wbr>rifCJKsc-Bol<wbr>d.otf]{NotoS<wbr>erifCJKsc-Re<wbr>gular.otf}<wbr></code><br>
<code>\else<wbr></code><br>
<code> \IfFontExis<wbr>tsTF{Noto Se<wbr>rif CJK SC}{<wbr></code><br>
<code> \setmainfon<wbr>t[ItalicFont<wbr>=Noto Serif <wbr>CJK SC,BoldI<wbr>talicFont=No<wbr>to Serif CJK<wbr> SC Bold]{No<wbr>to Serif CJK<wbr> SC}<wbr></code><br>
<code> }{\setmainf<wbr>ont[BoldFont<wbr>=FandolSong-<wbr>Bold.otf,Ita<wbr>licFont=Fand<wbr>olSong-Regul<wbr>ar.otf,<wbr></code><br>
<code> BoldItalicF<wbr>ont=FandolSo<wbr>ng-Bold.otf]<wbr>{FandolSong-<wbr>Regular.otf}<wbr>}<wbr></code><br>
<code>\fi<wbr></code><br>
<code>\setmonofont<wbr>{Latin Moder<wbr>n Mono}<wbr></code><br>
<code>\XeTeXlinebr<wbr>eaklocale &quot;z<wbr>h&quot;<wbr></code><br>
<code>\XeTeXlinebr<wbr>eakskip=0pt <wbr>plus 1pt<wbr></code><br>
<code>\usepackage{<wbr>amsmath,amss<wbr>ymb,amsthm,m<wbr>athtools,bm}<wbr></code><br>
<code>\usepackage{<wbr>booktabs,arr<wbr>ay,tabularx,<wbr>enumitem,fan<wbr>cyhdr,xcolor<wbr>,needspace,t<wbr>ikz}<wbr></code><br>
<code>\usetikzlibr<wbr>ary{arrows.m<wbr>eta,position<wbr>ing}<wbr></code><br>
<code>\definecolor<wbr>{auricblue}{<wbr>RGB}{24,53,7<wbr>9}<wbr></code><br>
<code>\usepackage[<wbr>unicode,colo<wbr>rlinks=true,<wbr>linkcolor=au<wbr>ricblue,urlc<wbr>olor=auricbl<wbr>ue,citecolor<wbr>=auricblue]{<wbr>hyperref}<wbr></code><br>
<code>\hypersetup{<wbr>pdftitle={AU<wbr>RIC v76：加乘生成<wbr>、二次关系网与内生量子结<wbr>构},<wbr></code><br>
<code>pdfauthor={A<wbr>URIC researc<wbr>h continuati<wbr>on},<wbr></code><br>
<code>pdfsubject={<wbr>Conservative<wbr> quadratic p<wbr>resentations<wbr>, positive r<wbr>esponses, co<wbr>mmon-source <wbr>quantum prot<wbr>ocols}}<wbr></code><br>
<code>\newcommand{<wbr>\R}{\mathbb <wbr>R}<wbr></code><br>
<code>\newcommand{<wbr>\C}{\mathbb <wbr>C}<wbr></code><br>
<code>\newcommand{<wbr>\F}{\mathbb <wbr>F}<wbr></code><br>
<code>\newcommand{<wbr>\HH}{\mathca<wbr>l H}<wbr></code><br>
<code>\newcommand{<wbr>\Alg}{\mathc<wbr>al A}<wbr></code><br>
<code>\newcommand{<wbr>\Tr}{\operat<wbr>orname{Tr}}<wbr></code><br>
<code>\newcommand{<wbr>\rank}{\oper<wbr>atorname{ran<wbr>k}}<wbr></code><br>
<code>\newcommand{<wbr>\id}{\operat<wbr>orname{id}}<wbr></code><br>
<code>\newcommand{<wbr>\ket}[1]{|#1<wbr>\rangle}<wbr></code><br>
<code>\newcommand{<wbr>\bra}[1]{\la<wbr>ngle#1|}<wbr></code><br>
<code>\newcommand{<wbr>\plain}[1]{\<wbr>par\smallski<wbr>p\noindent\t<wbr>extbf{\color<wbr>{auricblue}白<wbr>话图景。}#1\par\<wbr>smallskip}<wbr></code><br>
<code>\newcommand{<wbr>\repo}[2]{\h<wbr>ref{https://<wbr>github.com/t<wbr>he-omega-ins<wbr>titute/trure<wbr>turing/blob/<wbr>5cf95e1ae01f<wbr>7ed86735c04a<wbr>d8d752cb19b1<wbr>a58b/docs/de<wbr>velop/theory<wbr>/#1}{#2}}<wbr></code><br>
<code>\theoremstyl<wbr>e{definition<wbr>}<wbr></code><br>
<code>\newtheorem{<wbr>definition}{<wbr>定义}[section]<wbr></code><br>
<code>\newtheorem{<wbr>theorem}[def<wbr>inition]{定理}<wbr></code><br>
<code>\newtheorem{<wbr>proposition}<wbr>[definition]<wbr>{命题}<wbr></code><br>
<code>\newtheorem{<wbr>corollary}[d<wbr>efinition]{推<wbr>论}<wbr></code><br>
<code>\newtheorem{<wbr>remark}[defi<wbr>nition]{说明}<wbr></code><br>
<code>\renewcomman<wbr>d{\proofname<wbr>}{证明}<wbr></code><br>
<code>\renewcomman<wbr>d{\abstractn<wbr>ame}{摘要}<wbr></code><br>
<code>\renewcomman<wbr>d{\refname}{<wbr>固定来源与参考文献}<wbr></code><br>
<code>\setlength{\<wbr>parindent}{1<wbr>.8em}<wbr></code><br>
<code>\setlength{\<wbr>parskip}{2pt<wbr>}<wbr></code><br>
<code>\setlength{\<wbr>emergencystr<wbr>etch}{3em}<wbr></code><br>
<code>\setlist{nos<wbr>ep,leftmargi<wbr>n=2em}<wbr></code><br>
<code>\pagestyle{f<wbr>ancy}\fancyh<wbr>f{}<wbr></code><br>
<code>\fancyhead[L<wbr>]{\small AUR<wbr>IC：加乘生成与内生量子<wbr>结构}<wbr></code><br>
<code>\fancyhead[R<wbr>]{\small v76<wbr> / 2026-11-0<wbr>1}<wbr></code><br>
<code>\fancyfoot[C<wbr>]{\thepage}<wbr></code><br>
<code>\allowdispla<wbr>ybreaks[2]<wbr></code><br>
</div>

</details>

<!-- AURIC-V76-IMMUTABLE-SOURCE-BEGIN
```latex
% !TeX program = xelatex
% Compile twice. Optional: \def\AURICFontPath{/absolute/path/to/fonts/}
% Paper mathematics only; no mathematical programs or numerical verification.
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
\usepackage[unicode,colorlinks=true,linkcolor=auricblue,urlcolor=auricblue,citecolor=auricblue]{hyperref}
\hypersetup{pdftitle={AURIC v76：加乘生成、二次关系网与内生量子结构},
pdfauthor={AURIC research continuation},
pdfsubject={Conservative quadratic presentations, positive responses, common-source quantum protocols}}
\newcommand{\R}{\mathbb R}
\newcommand{\C}{\mathbb C}
\newcommand{\F}{\mathbb F}
\newcommand{\HH}{\mathcal H}
\newcommand{\Alg}{\mathcal A}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\rank}{\operatorname{rank}}
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
\fancyhead[L]{\small AURIC：加乘生成与内生量子结构}
\fancyhead[R]{\small v76 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
\begin{center}
{\LARGE\bfseries\color{auricblue} 加乘生成、二次关系网}\\[7pt]
{\LARGE\bfseries\color{auricblue} 与内生量子结构}\\[8pt]
{\large 从统一表达语言到整体相容约束}\\[6pt]
定义、定理与纸面证明\quad v76.0\\[4pt]
2026 年 11 月 1 日\quad Asia/Singapore
\end{center}
\begin{abstract}
本稿把研究目标从“寻找绝对最少的公理条数”转为“统一表达、保守展开与约束完备性”。
任意集合关系都能在自由线性空间中精确读出，但其完整系数仍承载原关系信息。
有限加乘脚本恰生成多项式；每个有限代数关系体都能通过辅助结点改写成总次数至多二的约束。
证明该展开在交换、非交换及带伴随代数中均保守：原商代数、全部旧关系、正响应与同一来源的最小循环表示保持。
进一步，全部二次标量约束可转成提升矩阵上的线性读出，合法像由一个共同秩一约束限定。
量子方面，承接项目既有的双线性权重闭合与共同相位二次生成，
给出有限维、有限历史量子协议的精确实二次约束表示，保留正性、完全正性、同标签过程复用及零概率分支。
其内部记录实现仍可写成一个固定 $\Omega$ 的整体酉历史。
全文区分关系表示、关系推导与物理实现，并给出递归逼近和误差条件。
\end{abstract}

\section{本轮方向与固定项目依据}
可以把问题改为：用统一的加乘关系语言表达对象，
再由整个网络必须共同满足的条件确定量子结构。
不必先解决“所有可能形式语言中究竟几条公理最少”。
真正需要证明的是表达是否完整、展开是否保留信息、哪些约束选择了量子模型。

本轮唯一实时 HEAD GET 于新加坡时间 2026-11-01 21:09:47
在收到 HTTP 响应前遭遇网络权限拒绝；没有重试、重定向、备用活动端点或升级。
以下采用重新核对六份 Git blob 的固定提交
\par\noindent\texttt{5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b}。\par
不声称取得该提交之后的新仓库进展；v76 为本对话稿件编号。

\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.22\textwidth}X@{}}
\toprule
固定来源 & 实际承接内容\\
\midrule
V17 §2、§8 & 加乘 DAG；直和、张量及相干叠加的区别。\\
V49 §§2--8 & 有限加乘范围、双线性闭合、二次权重与提升像。\\
V52 §§5--7 & 相位不变量的二次生成、正效果读出与递归相容。\\
V58 §§2--8、10--14 & 实关系代数、复定向、正响应、GNS、酉与内部仪器。\\
V59 §§1--6、10 的所用段 & 完整线性关系、正性覆盖和实际读数之间的接口。\\
$\Omega$ §§1--8、12 & 静态关系、全局相容、固定门传播及有限内部协议。\\
\bottomrule
\end{tabularx}
\end{center}

V49 与 V52 的既有定理不列作本轮新发现。
一般电路的辅助变量二次化属于标准关系编码；
本稿给出其非交换 $*$ 代数及同源正响应版本的自足证明。
只消费所列实际相关段落，不认证全部仓库或全部原生控制供应链。
所有数学均为纸面推导与独立纸面复核；没有数学程序、CAS、数值、枚举、仿真或机器证明。

\plain{不必给每一种复杂关系另取一个基础原理。
先统一它们的写法，再检查这些写法怎样互相约束、怎样共同成立。
“都在同一个整体里”可以具体落实为：同一对象在各处复用，
同一来源的响应在各种拆法中一致。}

\section{“线性足够表达关系”的两种准确含义}
\begin{definition}[固定系数线性与双线性复合]
$T$ 线性是指 $T(\alpha x+\beta y)=\alpha T(x)+\beta T(y)$。
乘法 $\mu(x,y)=xy$ 在含幺结合代数中对每一槽分别线性，称为双线性。
它通常不对联合输入 $(x,y)$ 线性。
\end{definition}

例如 $\mu(2x,2y)=4xy$；联合线性则会要求 $2xy$。
线性映射的有限和与复合仍线性，不能因此产生 $x\mapsto x^2$。
另一方面，对固定 $H$，$e^{iH}$ 仍是固定线性算子；
“表达式是否出现指数符号”不能判定它对所谈变量是否线性。
项目 V17、V49 已作这些对象层的区分 \cite{v17,v49}。

\begin{theorem}[任意集合关系的自由线性表示]\label{thm:allrelations}
给任意集合 $X,Y$ 及任意关系 $R\subseteq X\times Y$。
取有限支撑自由向量空间
$V_X=\R^{(X)}$、$V_Y=\R^{(Y)}$。
存在唯一线性泛函
\[
\boxed{L_R:V_X\otimes V_Y\longrightarrow\R,\qquad
L_R(e_x\otimes e_y)=1_R(x,y).}
\]
且 $R\mapsto L_R$ 为单射。
\end{theorem}
\begin{proof}
张量基为 $\{e_x\otimes e_y\}$。对唯一的有限展开定义
$L_R(\sum c_{xy}e_x\otimes e_y)=\sum c_{xy}1_R(x,y)$，
即得良定义、线性及唯一性。
不同关系在某个基张量上的值不同，故该对应单射。
\end{proof}

因此“任意关系有线性表示”确有一个不要求有限集合的严格版本。
它保留全部关系信息。原始输入对编码为基张量，
任意叠加不一定仍是一个原始输入，其读数也不一定是零或一。
无限系数表与无限维自由空间没有自动给有限脚本、有效算法、Hilbert 范数或量子概率。

\begin{theorem}[双线性的张量线性化]
任意双线性映射 $B:V\times W\to Z$ 唯一因子化为
\[
\widehat B:V\otimes W\to Z,\qquad
\widehat B(u\otimes v)=B(u,v),
\]
其中 $\widehat B$ 线性。
\end{theorem}
\begin{proof}
在形式对的自由线性空间上令 $(u,v)\mapsto B(u,v)$。
双线性保证该映射消去张量积定义中的双线性关系，故下降到商。
纯张量张成商空间，故唯一。
\end{proof}
这是张量积的通用性质 \cite{tensor}。
在矩阵坐标中，一个输入对 $u,v$ 对应 $Z_{ij}=u_iv_j$，
其矩阵秩至多一；一般张量不再代表一个单独的输入对。

\plain{可以把关系搬到足够大的坐标空间，让读出成为线性的。
但坐标的合法取值仍要反映它们来自同一个输入。
线性读出负责读取；输入一致性负责说明读到的究竟是哪一种关系。}

\section{有限加乘关系的精确二次化}
\begin{definition}[有限算术脚本]
输入为域 $\F=\R$ 或 $\C$ 中的常数及变量。
内部结点为两个已有量的加法或乘法，依赖图有限且无环。
允许共享子表达式；负号可由常数 $-1$ 给出。
\end{definition}

\begin{proposition}[加乘的表达范围]
交换输入的有限脚本恰生成 $\F[x_1,\ldots,x_n]$；
非交换输入的形式脚本恰生成自由结合代数
$\F\langle x_1,\ldots,x_n\rangle$。
\end{proposition}
\begin{proof}
按拓扑顺序归纳，每个输出仍为多项式或有限词的线性组合。
反向逐个相乘形成单项式或词，再有限相加即得脚本。
\end{proof}

这是项目 V49 命题 2.3 的直接延伸 \cite{v49}。
固定自然数幂已在语言内；一般变量指数与对数还须其他关系或极限。

\begin{theorem}[二次约束网的唯一中间量]\label{thm:compile}
按门顺序引入中间变量 $z_i$，加入
\[
\boxed{q_i=z_i-u_i-v_i=0
\quad\text{或}\quad q_i=z_i-u_iv_i=0.}
\]
其中 $u_i,v_i$ 只使用原输入、常数与编号更小的中间量。
对每个原输入，全部 $z_i$ 存在且唯一，
并恰等于原脚本相应结点的值。
原输出图是该二次约束集的坐标投影。
\end{theorem}
\begin{proof}
第一结点由输入唯一确定；后续结点依次由已确定的前驱唯一确定。
原脚本求值给存在性，逐结点代入给反向等价。
同一证明适用于任意含幺结合代数，并保留乘法顺序。
\end{proof}

例如
\[
p(x,y)=(x+y)^2+xy
\]
可写为
\[
a=x+y,\qquad b=aa,\qquad c=xy,\qquad p=b+c.
\]
\begin{center}
\begin{tikzpicture}[>=Stealth,font=\small,
 nodebox/.style={draw=auricblue,rounded corners,minimum height=.6cm,minimum width=1.5cm}]
\node[nodebox] (x) at (0,1) {$x$};
\node[nodebox] (y) at (0,-1) {$y$};
\node[nodebox] (a) at (3,1) {$a=x+y$};
\node[nodebox] (c) at (3,-1) {$c=xy$};
\node[nodebox] (b) at (6,1) {$b=aa$};
\node[nodebox] (p) at (9,0) {$p=b+c$};
\draw[->] (x)--(a);
\draw[->] (y)--(a);
\draw[->] (x)--(c);
\draw[->] (y)--(c);
\draw[->] (a)--(b);
\draw[->] (b)--(p);
\draw[->] (c)--(p);
\end{tikzpicture}
\end{center}
图中复用是同一数学值的复用；没有声明这是从未知单份量子态实施复制的门。
所有结点约束的总次数至多二，并不都是齐次二次。
算术电路的乘法约束与线性一致性关系是标准编码 \cite{arithmetic}。

\subsection*{更强的结论：原关系代数完全保持}
令 $A=\F\langle x\rangle$、$B=\F\langle x,z\rangle$；
交换情形换成通常多项式代数。
记 $J$ 为全部门缺陷 $q_i$ 生成的双边理想，
令 $p_i(x)$ 为原脚本的各中间表达式。

\begin{theorem}[保守二次呈示]\label{thm:conservative}
代入同态 $\Phi:B\to A$ 由
$\Phi(x_j)=x_j$、$\Phi(z_i)=p_i(x)$ 给出。
则
\[
\boxed{\ker\Phi=J,\qquad B/J\cong A.}
\]
若再给原关系理想 $I=\langle r_1,\ldots,r_s\rangle$，
将每个 $r_j$ 编译并令对应输出为零，得到 $\widetilde I$，则
\[
\boxed{B/\widetilde I\cong A/I,\qquad
\widetilde I\cap A=I.}
\]
\end{theorem}
\begin{proof}
所有门缺陷代入为零，故 $\Phi$ 下降为 $\bar\Phi:B/J\to A$。
原输入包含给 $\iota:A\to B/J$，且 $\bar\Phi\iota=\id_A$。
依门顺序归纳，商中 $[z_i]=p_i([x])$，
所以 $\iota\bar\Phi$ 固定全部生成元，也为恒等映射。
这证明第一个同构及核等式。
在该同构下，输出零约束正好变成 $r_j=0$，
再取商即得第二组等式。
\end{proof}

带伴随版本给每个中间符号配形式伴随，
把 $q_i$ 和 $q_i^*$ 纳入 $*$ 理想，上述同构成为 $*$ 同构。
若 $u,v$ 自伴而不交换，$uv$ 通常不自伴；
不能额外要求新符号 $z=uv$ 自伴，否则会加入原来没有的约束。
定理保留的是代数呈示及全部表示，没有用未证明的代数几何零点定理。

\plain{高次关系能拆成很多只做一步的小结点。
更强的是，拆完以后原来能推出哪些关系、不能推出哪些关系，都保持不变。
这些中间结点只是把原脚本展开，不增加本体的自由度。}

\section{正响应与同一个 \texorpdfstring{$\Omega$}{Omega} 也在展开中保持}
\begin{definition}[共同正响应]
在实或复 $*$ 代数上，$\ell$ 为线性泛函，
\[
\ell(1)=1,\qquad
\ell(a^*)=\overline{\ell(a)},\qquad
\ell(a^*a)\ge0.
\]
实数情形同样明确要求伴随对称。
取
$N_\ell=\{a:\ell(a^*a)=0\}$，
以 $[1]$ 为来源，并以左乘作用于 $\Alg/N_\ell$。
\end{definition}

正性的 Cauchy--Schwarz 保证 $N_\ell$ 为左理想：
若 $p\in N_\ell$，则 $\ell(p^*q)=0$；
取 $q=a^*ap$ 得 $ap\in N_\ell$。
因此商内积与左乘良定义，这给最小循环表示
$(\pi,\HH_\ell,\Omega)$。
一般先在代数共同定义域工作，不无条件声称所有算子有界。

\begin{theorem}[正响应的保守扩展]\label{thm:positive}
在定理 \ref{thm:conservative} 的 $*$ 版本中，
$A$ 上的正归一 Hermitian 响应与 $B$ 上满足
\[
\widetilde\ell(w^*q_i^*q_iw)=0
\quad\text{对全部门 }i\text{ 及全部词 }w
\]
的正归一 Hermitian 响应一一对应：
\[
\boxed{\widetilde\ell=\ell\circ\Phi.}
\]
两者的最小循环表示等距同构，且固定同一个 $\Omega$。
\end{theorem}
\begin{proof}
$*$ 同态拉回显然保持正性、伴随对称和归一，并使所有门缺陷为零。
反向在 $\widetilde\ell$ 的循环表示中，所列数是
$\|\pi(q_i)\pi(w)\Omega\|^2$。
全部为零说明 $\pi(q_i)$ 消去所有生成词向量，
故表示商去整个 $*$ 理想 $J$。
由 $B/J\cong A$ 唯一下降到 $A$。
显式等距同构为
\[
[b]_{\widetilde\ell}\longmapsto[\Phi(b)]_\ell,
\]
因为双方内积同为 $\ell(\Phi(b)^*\Phi(c))$。
原输入包含保证满射，$1\mapsto1$ 保持来源。
\end{proof}

如果新符号只是旧表达式的定义，等式由保守展开保证。
如果它代表另一台实际未知装置，则仍须认证它在全部声明上下文中执行同一关系。
单有 $q_i\Omega=0$ 一般不足；
v75 的完整锚覆盖或关系族接续闭合，给可缩减检验的具体条件。
代数和 $U+V$ 也通常不是酉门，表达式合法与实际控制可用是两个明确问题。

\plain{给已有关系加一个新名字，不会产生另一个来源。
只要新名字在所有用法里都指向原表达式，正响应和同一个 $\Omega$ 也不变。
观察者自己记录、展开和检验这些关系，仍可属于同一整体。}

\section{把全部二次方程再变成线性读出：共同来源约束在哪里}
\begin{theorem}[二次关系的整体秩一提升]\label{thm:ranklift}
给实变量 $z\in\R^N$ 和有限个次数至多二的实多项式 $q_\alpha(z)$。
令 $v=(1,z_1,\ldots,z_N)^{\mathsf T}$。
存在实对称矩阵 $A_\alpha$ 使
$q_\alpha(z)=v^{\mathsf T}A_\alpha v$。
以实对称矩阵 $Y\in\mathbb S^{N+1}(\R)$ 为未知量，原方程组等价于
\[
\boxed{
\Tr(A_\alpha Y)=0\ \forall\alpha,\qquad
Y\succeq0,\quad Y_{00}=1,\quad\rank Y=1.
}
\]
恢复公式为 $z_i=Y_{i0}$。
\end{theorem}
\begin{proof}
常数项置于 $A_{00}$；一次项与非对角二次项在对称位置各分一半，
平方项置于相应对角，便得所述 $A_\alpha$。
正向取 $Y=vv^{\mathsf T}$。
反向由秩一正性写 $Y=uu^{\mathsf T}$。
$Y_{00}=1$ 给 $u_0=\pm1$；取 $z_i=u_i u_0=Y_{i0}$，
则 $Y=(1,z)(1,z)^{\mathsf T}$，还原所有方程。
\end{proof}

于是有限代数关系具有一条完整链：
\[
\boxed{
\text{高次关系}\ \longrightarrow\
\text{局部二次约束}\ \longrightarrow\
\text{线性读出与共同秩一一致性}.}
\]
这一“秩一”是所有标量变量来自同一次确定赋值的条件；
它不等于局部物理密度矩阵必须纯。
若原协议里有混态 $\rho$，$\rho$ 的各条目仍是 $z$ 中的确定数，
与这个形式提升矩阵 $Y$ 秩一并不冲突。

不能删去 $Y$ 的合法像条件。例如原方程
$x^2-1=0$ 与 $x=0$ 无共同解；
在 $v=(1,x)$ 的提升中，它们要求
$Y_{11}=Y_{00}=1$、$Y_{01}=0$。
$Y=I_2$ 为正且满足这些线性式，却秩二，并非一个原输入。
去掉秩条件会增加原问题没有的解。

\begin{proposition}[不是每组二元正关系都能拼成整体]
取三阶实对称矩阵，所有对角为一、所有非对角为 $-3/4$。
每个二阶主块均正定，但整矩阵不是半正定。
\end{proposition}
\begin{proof}
每个二阶块的本征值为 $1\pm3/4>0$。
而全一向量的二次型值为
\mbox{$3+6(-3/4)=-3/2<0$}。
\end{proof}

项目 V58 命题 12.2 与 V17 的 Gram 闭路分析已指出同类整体约束 \cite{v58,v17}。
二元结点可作表达积木，整体正性仍须在同一个共同实现中成立。

\plain{可以让最后的读取都成为线性的。
真正把这些坐标绑在一起的，是“它们来自同一个输入、同一个来源”的条件。
每两块分别能拼起来，还须检查三块乃至整张网能否同时拼成一个整体。}

\section{平方的特殊性：关系闭合，而不只是表达式的次数}
\subsection*{非负权重的双线性叠加修正}
\begin{theorem}[双线性闭合选择二次型]\label{thm:quadraticweight}
设实向量空间上 $Q\ge0$、$Q(0)=0$，并令
\[
C_Q(u,v)=\frac{Q(u+v)-Q(u)-Q(v)}2.
\]
若 $C_Q$ 实双线性，则 $Q(v)=C_Q(v,v)$，
且 $C_Q$ 对称半正定。反向成立。
\end{theorem}
\begin{proof}
记 $B=C_Q$。定义使 $B$ 对称，且
$L(v)=Q(v)-B(v,v)$ 可加。
对每个正整数 $n$，
\[
0\le Q(\pm v/n)=B(v,v)/n^2\pm L(v)/n.
\]
故 $B(v,v)\ge n|L(v)|$ 对全部 $n$ 成立，只能 $L(v)=0$。
反向展开二次型即可。
\end{proof}

这是项目 V49 定理 4.2 的既有结果 \cite{v49}。
它不用预设 $Q$ 连续或偶。
实双线性是所用相容条件；“两个输入”单独不保证它。
例如 $x^4$ 也可用两个平方结点表示，
所以“可编译成二次网”本身不选定 Born 指数。

\subsection*{共同相位关系的二次生成}
\begin{theorem}[共同相位不变量由外积生成]\label{thm:invariant}
在已给 $\C^d$ 上，关于 $z,\bar z$ 的多项式若满足
$P(e^{i\theta}z,e^{-i\theta}\bar z)=P(z,\bar z)$，
则它由 $G_{ij}=z_i\bar z_j$ 加乘生成。
最低非恒定总次数为二。
\end{theorem}
\begin{proof}
单项式 $z^\alpha\bar z^\beta$ 在相位作用下乘
$e^{i(|\alpha|-|\beta|)\theta}$。
不同整数频率线性独立，故不变项须满足 $|\alpha|=|\beta|$。
把振幅因子与共轭因子逐个配对，即成若干 $G_{ij}$ 的乘积。
\end{proof}

这承接项目 V52 定理 5.2 \cite{v52}。
$G=zz^\dagger$ 分离共同相位轨道，并保留 $\Tr G=\|z\|^2$。
其合法像满足
\[
G=G^\dagger,\quad G\succeq0,\quad\rank G\le1,\quad
G_{ij}G_{kl}=G_{il}G_{kj}.
\]
非零后再作迹归一，才同时消去正尺度。
局部相位若相对于整体其他部分可测，不能直接当作全局共同相位删去。

\subsection*{为何二元块有三轴}
对归一 $\psi=(a,b)^{\mathsf T}$，定义
\[
x=2\Re(\bar a b),\quad y=2\Im(\bar a b),\quad z=|a|^2-|b|^2.
\]
直接展开得
\[
\boxed{x^2+y^2+z^2=(|a|^2+|b|^2)^2=1.}
\]
等价地 $\rho=\psi\psi^\dagger=(I+x\sigma_x+y\sigma_y+z\sigma_z)/2$。
一般正迹一二阶 Hermitian 矩阵给 $x^2+y^2+z^2\le1$，
因为本征值为 $(1\pm\sqrt{x^2+y^2+z^2})/2$。
这解释已声明二元块的三轴，不把任意高维整体无损压成三个实数。
与原 AURIC 五模式标签对应时，仍须采用实际读口编码。

\plain{平方可以是最低的相位不变关系，也可以由非负权重的双线性闭合强迫出来。
复杂关系再由这些二次量继续加乘。
二元复块归一后出现三条读出轴，而三轴之间的球面条件继续保留它们来自同一个纯态的事实。}

\section{从整体读出相容到 Born 形式}
二次生成说明可以用哪些关系坐标，概率还须满足同一效果在不同分解下的响应一致。

\begin{theorem}[完整正效果响应的迹表示]\label{thm:born}
在有限维复矩阵效果域 $\mathcal E=\{E:0\preceq E\preceq I\}$ 上，
设 $p:\mathcal E\to[0,1]$，
$p(I)=1$，并且
\[
p(E+F)=p(E)+p(F)\qquad(E,F,E+F\in\mathcal E).
\]
则存在唯一 $\rho\succeq0$、$\Tr\rho=1$，使
\[
\boxed{p(E)=\Tr(\rho E).}
\]
若 $\rho=\ket\psi\bra\psi$，则对单位向量 $\phi$，
$p(\ket\phi\bra\phi)=|\langle\phi,\psi\rangle|^2$。
\end{theorem}
\begin{proof}
对正矩阵 $A$，选正整数 $m$ 使 $A/m\le I$，
定义 $\widetilde p(A)=m p(A/m)$。
用共同倍数和有限可加性证明与 $m$ 无关，并在正锥上可加。
以差延拓到 Hermitian 空间；两种差分解由交叉相加保证一致。
可加性先给有理齐次性；正性使泛函序保持。
对任意有理数 $r>\|X\|$，有 $-rI\le X\le rI$，
故 $|\widetilde p(X)|\le r$，进而不超过 $\|X\|$。
这给连续性，再以有理数逼近任意实数，得到实线性。
有限维迹配对给唯一 Hermitian $\rho$，
所有秩一效果上的非负性给 $\rho\ge0$，单位响应给迹一。
最后对两个秩一投影作迹配对即得模平方。
\end{proof}

这是项目 V52、V58 与标准完整效果定理的共同内容 \cite{v52,v58,busch}。
有限维只需所列有限可加性；没有援引无限维正态性。
如果只给几个读口，完整正性和分解相容必须另由实际关系覆盖认证；
V59 命题 5.3、定理 5.4 明确保留这一点 \cite{v59}。

\begin{proposition}[共同正交权重也唯一选择平方]
在实维数至少二的内积空间上，有限非负权重 $W$ 只依赖范数，
对正交向量可加，并使单位向量权重为一，则 $W(v)=\|v\|^2$。
\end{proposition}
\begin{proof}
取正交单位向量 $e_1,e_2$，令 $F(t)=W(\sqrt t\,e_1)$。
径向性和正交可加性给 $F(s+t)=F(s)+F(t)$。
非负性使 $F$ 单调；有理数上 $F(q)=q$，上下有理夹逼给全部 $t\ge0$。
\end{proof}

这条项目 V17、V52 已有的路线不另需连续性 \cite{v17,v52}。
它明确使用内积正交及同一未归一权重；仅给逐表归一可允许其他幂。
平方权重同时满足
\[
\|u\oplus v\|^2=\|u\|^2+\|v\|^2,\qquad
\|u\otimes v\|^2=\|u\|^2\|v\|^2,
\]
而相干叠加保留 $2\Re\langle u,v\rangle$。

\plain{概率读数不能因为换一种分拆方法就改变。
同一效果的各种拆法都要给同一个数，这种整体相容把读出锁成迹配对。
纯来源与纯读口相配时，它就是振幅平方。
存在某个分支说明它可能发生，具体权重还由这套正响应确定。}

\section{核心量子定理：有限协议的精确二次关系表示}
\begin{definition}[实二次关系网与声明协议]
实二次关系网由有限实变量和总次数至多二的实多项式等式组成。
允许辅助变量，原模型取解集的可见坐标投影。
固定有限维端口、有限准备/效果/操作标签和有限展开的分支历史。
相同操作标签在所有位置表示同一个过程。
预先固定要求报告条件态的历史集合 $H_{\rm cond}$；
该部分模型域要求各 $p_h>0$，其他历史统一保留未归一态。
允许有限代数校准条件；不在此假定任意连续函数族都有有限精确代数描述。
\end{definition}

\begin{theorem}[有限量子协议二次表示]\label{thm:protocol}
在上述固定维数和接口中，合法量子准备、效果、通道、仪器、
未归一联合分支权重与正权分支条件态的集合，
恰为一个有限实二次关系网的可见投影。
\end{theorem}
\begin{proof}
每个复条目拆为实部、虚部；共轭实线性，复乘法实双线性。
以下分别给可靠性与完备性所需的构造。

\textbf{态与效果。}
用
\[
\rho=BB^\dagger,\quad\Tr\rho=1,\qquad
E=CC^\dagger,\quad I-E=DD^\dagger
\]
精确表示正态和效果；POVM 再加 $\sum_kE_k=I$。
正矩阵谱分解保证因子存在，反向因子式保证正性。
每个正因子可取与被分解矩阵同阶的方阵，故变量数事先有限。
若声明准备纯态，则取 $\rho=\psi\psi^\dagger$、$\psi^\dagger\psi=1$。
这些条目等式均至多二次。

\textbf{过程。}
采用本节特定的\emph{未归一} Choi 约定
\[
J_\Lambda=\sum_{i,j}\Lambda(\ket i\bra j)\otimes\ket i\bra j,
\qquad
(J_\Lambda)_{\mu i,\nu j}
=[\Lambda(\ket i\bra j)]_{\mu\nu}.
\]
要求 $J_\Lambda=FF^\dagger$。
每个 $F$ 的列重排为 $(K_\alpha)_{\mu i}=F_{\mu i,\alpha}$，
比较矩阵块给
$\Lambda(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger$。
该式在任意参考扩展上保持正性，故给完全正性。
反向，若 $\Lambda$ 完全正，则
$J_\Lambda=(\Lambda\otimes\id)(\ket\omega\bra\omega)\succeq0$，
其中 $\ket\omega=\sum_i\ket i\ket i$，再取其正因子即可。
通道再加线性条件
\[
\Tr_{\rm out}J_\Lambda=I_{\rm in};
\]
仪器则为各 $J_k=F_kF_k^\dagger$ 和
$\sum_k\Tr_{\rm out}J_k=I_{\rm in}$。
单独迹不增分支可再把
$I-\Tr_{\rm out}J$ 写成正因子。
注意该偏迹条目是 $(\sum K_\alpha^\dagger K_\alpha)_{ji}$，
等于单位矩阵与 Kraus 归一相同。

\textbf{同一对象的接口粘合。}
若同一仪器结果又以效果 $E_k$ 表示，必须加入
\[
\boxed{\Tr_{\rm out}J_k=E_k^{\mathsf T}.}
\]
若同一酉门同时出现为 $U$ 和 $J_U$，则加入
\[
U^\dagger U=I,\qquad
\boxed{J_U=\operatorname{vec}(U)\operatorname{vec}(U)^\dagger,}
\]
其中 $\operatorname{vec}(U)_{\mu i}=U_{\mu i}$，没有 $1/d$ 因子。
若另给标签 $C=B\circ A$，则要求
\[
(J_C)_{\mu i,\nu j}
=\sum_{r,s}(J_B)_{\mu r,\nu s}(J_A)_{ri,sj}.
\]
这些等式保留同一对象的多种坐标及所有输入上的组合一致性，均至多二次。

\textbf{同一历史接续。}
令 $\sigma_\varnothing=\rho$。每次实际使用标签 $k$ 时，
复用同一个 $J_k$，并要求
\[
\boxed{
(\sigma_{h\to k})_{\mu\nu}
=\sum_{i,j}(J_k)_{\mu i,\nu j}(\sigma_h)_{ij}.}
\]
该式对未知 $J_k,\sigma_h$ 为二次；
不再对 $\sigma_{ij}$ 额外共轭或转置。
其矩阵形式为
$\Tr_{\rm in}[J_k(I\otimes\sigma_h^{\mathsf T})]$。
令 $p_h=\Tr\sigma_h$，终端效果读数为
$p_{h,E}=\Tr(E\sigma_h)$。
初始正性与完全正接续给 $\sigma_h\ge0$；
仪器完整性给 $\sum_kp_{hk}=p_h$。
有限反馈使用历史所指定的后续标签，仍共用相应过程变量。

\textbf{条件化与守卫。}
只对预先声明的 $h\in H_{\rm cond}$ 引入
\[
\sigma_h=p_h\rho_h,\qquad
\rho_h=B_hB_h^\dagger,\quad\Tr\rho_h=1,\quad p_hq_h=1.
\]
$p_h\ge0$ 已成立，最后一式恰排除 $p_h=0$。
零权分支只保留 $\sigma_h=0$，不人为指定条件态。
当 $H_{\rm cond}$ 为空时，全部零权模式均自然保留。
若预先声明纯分支及秩一投影读口，则先以
\[
\sigma_h=\psi_h\psi_h^\dagger,\qquad
E=\phi\phi^\dagger,\qquad \phi^\dagger\phi=1
\]
粘合振幅与已有矩阵，再用
$z=\langle\phi,\psi_h\rangle$、
$p_{h,E}=(\Re z)^2+(\Im z)^2$ 两个二次结点。
这里 $\|\psi_h\|^2=p_h$；若振幅代表已归一准备或条件态，另有单位范数条件。

\textbf{额外关系。}
有限多项式校准条件由定理 \ref{thm:compile} 编译。
$f\ge0$ 可用 $f=s^2$ 的存在辅助量表示；
$f>0$ 再加 $ft=1$。若 $f$ 高次，先编译其输出。
因此所有条件均可保持局部次数至多二。

每个合法协议用实际矩阵、正因子及分支态填入，给一个解。
每个解反向给正态、合法效果、共同 CP 过程及正确的全部分支组合，
故可见投影恰等于原协议模型。
\end{proof}

此处 $J$ 的迹保留约定与 v75 以归一 $\Phi_d$ 定义的 Choi 矩阵相差输入维数，
不能混用尺度。
正因子 $B,C,F$ 可以不唯一；它们是相同可见矩阵的辅助描述自由。
定理不把已给正性、CP 和共同接口当作从裸加乘自动产生的结论。
实际有记忆的过程应将记忆纳入端口，否则不能假定同一无记忆 $J_k$ 足够。

\begin{corollary}[同一纯来源与内部酉历史]
固定上述端口和有限历史规模后，可以先固定一个共同有限载体及单位来源 $\Omega$。
每个合法协议实现均可在其上选择内部准备与整体酉序列，
使全部声明联合概率保持，并满足
\[
\Psi_0=\Omega,\qquad
\Psi_{j+1}=\mathcal U_j\Psi_j,\qquad
\mathcal U_j^\dagger\mathcal U_j=I.
\]
把这些量一同作为未知数，仍得到实二次关系。
\end{corollary}
\begin{proof}
每个过程最多需 $d_{\rm in}d_{\rm out}$ 个 Kraus 列，
不足者补零，因此可预先统一全部有限记录和辅助载体的尺寸。
由 $\rho=BB^\dagger$ 构造归一纯化
$\sum_{a,k}B_{ak}\ket a\ket k$。
任一固定单位参考向量可经一个整体酉到达它，方法是分别扩成正交基后逐基映射。
有限多个准备标签可在共同载体上采用相应内部准备门。
对每个仪器，Kraus 完整性使
\[
V\psi=\sum_{k,\alpha}K_{k,\alpha}\psi\otimes\ket{k,\alpha}
\]
等距，并可在足够大的内部 ready 载体上补成酉。
若与原协议矩阵联合求解，须把
\[
\mathcal U(\psi\otimes\ket{\mathrm{ready}})
=\sum_{k,\alpha}K_{k,\alpha}\psi\otimes\ket{k,\alpha}
\]
在固定输入基上逐列加入关系网，且各 $K_{k,\alpha}$ 正是上述 $F_k$ 的列重排。
不同端口先作共同载体内的固定嵌入；该等式认证全部输入，而非只认证实际 $\Omega$。
记录基上的受控酉实现有限反馈；有限展开仅需有限记录容量。
最后读取记录事件的投影，得到原来的联合概率。
相应未归一分支与整体历史以
$\sigma_h=\Tr_{\rm aux}(P_h\ket{\Psi_t}\bra{\Psi_t}P_h)$ 粘合，
其中 $P_h$ 是所声明内部记录事件的投影，保留所需输出端口。
以上矩阵与幅度关系均由本节结点表达。
\end{proof}

来源、记录、辅助因子与环境皆可内生；该结论给表示存在性，
不认证具体原生控制或整个宇宙有限维，也不从有限统计唯一确定不可见环境。
项目 V58 的 ready 条件与 $\Omega$ 的有限协议对应仍保留明确接口 \cite{v58,omega}。

\begin{proposition}[二次归一关系不自动成为单输入量子门]
在 $\dim\HH\ge2$ 时，关系
$\|\psi\|=1$、$\chi_{ij}=\psi_i\psi_j$、$\|\chi\|=1$
可以写成实二次网，却不能由一个确定性通道对每个未知 $\psi$ 实现。
\end{proposition}
\begin{proof}
若存在，等距记录实现必须为
$V\psi=\psi\otimes\psi\otimes e_\psi$，
因为两份输出联合态为纯态。
对两态重叠 $c=\langle\psi,\phi\rangle$，保持内积给
$c=c^2\langle e_\psi,e_\phi\rangle$。
取 $0<|c|<1$，得 $|c|\le|c|^2$，矛盾。
\end{proof}

\plain{准备、门、读出、分支和归一可以放在同一张二次关系网中共同确定。
每处出现同一台门，就必须用同一个过程变量。
记录和环境可以一起留在 $\Omega$ 内部，整体历史继续保持酉性。
关系图能怎样写，与未知输入实际能被怎样操作，也由网中的过程约束分清。}

\section{约束自身继续展开：闭路、归一和误差}
\begin{proposition}[闭路约束可以精确接入保守展开]
若无环脚本定义 $z=p(x)$，再加任意多项式关系 $h_j(x,z)=0$
（非交换情形取自由多项式），
则整体关系商等价于原输入上的 $h_j(x,p(x))=0$。
\end{proposition}
\begin{proof}
在 $B/J\cong A$ 下，$[h_j]$ 恰映为 $h_j(x,p(x))$，
再取生成理想的商即可。
\end{proof}

因此计算一条关系的表达图可以无环，而许多未知量共同满足的约束图可以有环。
若 $z=F(x,z)$，应先把 $z$ 当原未知量，
编译右侧，再把输出等于 $z$ 作为闭路条件。
$z=z^2$ 有两个实解，$z=z+1$ 无解，$z=xz$ 在 $x=1$ 时有任意解。
二次语法本身不保证唯一；闭路的共同固定空间可像 v75 那样选定来源或保留自由。

\begin{proposition}[归一化也能由内部二次关系表达]
对非零实向量 $x$，引入正尺度 $r$、单位方向 $n$，
以
\[
x_i=rn_i,\qquad \sum_i n_i^2=1,\qquad r>0
\]
表达归一化。则 $r=\|x\|$、$n=x/\|x\|$ 唯一。
$r>0$ 等价于存在实 $s,t$ 使 $r=s^2$、$rt=1$。
\end{proposition}
\begin{proof}
对 $x_i=rn_i$ 平方求和得 $\|x\|^2=r^2$；
正支决定 $r$，随后决定 $n$。反向代入成立。
\end{proof}
只保留 $n$ 会消去尺度；保留 $(r,n)$ 则不丢失非零 $x$。
辅助量 $s$ 有正负两支；上述唯一性指可见的 $r,n$。
零向量须单列，不存在唯一方向。
正性、尺度和分支条件都可以是整体约束，不能因叫作归一就删掉它们。

\begin{proposition}[局部残差的递推控制]
在赋范代数中，设真值及近似操作数范数均不超过 $M$，
局部门残差为 $e_i$，各结点误差为 $d_i$。则
\[
d_i\le\|e_i\|+d_u+d_v\quad\text{（加法）},
\qquad
d_i\le\|e_i\|+Md_u+Md_v\quad\text{（乘法）}.
\]
\end{proposition}
\begin{proof}
加法用三角不等式。乘法用
$\widetilde u\widetilde v-uv
 =(\widetilde u-u)\widetilde v+u(\widetilde v-v)$。
\end{proof}
在原输入与常数精确共享时，沿有限 DAG 代入给各局部残差的路径增益和；
若输入也有扰动，还须加入各输入误差沿路径传播的项。
这证明怎样预算误差，不保证任意长乘法链天然稳定。
观察者希望持续缩小误差，还须合适的反馈或收缩关系。

\plain{每条约束都能继续拆成同类小关系；不同路径再次相遇时，闭路筛选能同时成立的值。
归一化也在其中，但方向和尺度各有位置。
误差沿这些连接传播，稳定性取决于连接怎样放大或抑制余量。}

\section{无限递归与精确表达的范围}
\subsection*{有限域与极限不能混为一个结论}
有理式 $y=P(x)/Q(x)$ 可以写作
$Q(x)t=1$、$y=P(x)t$，因此在非零分母域内有唯一辅助解。
实平方根关系 $z^2=x$ 还须选择正支。
非交换逆元一般应同时保留左右逆条件。

有限实多项式方程、不等式及有限实量词仍描述半代数集合；
这是实代数消元的标准范围 \cite{realalg}。
这里不把该定理混用于整数算术或任意无限逻辑。
特别地，存在辅助变量不会自动把所有连续关系都变成有限代数关系。

\begin{proposition}[全正域的对数不是代数函数]
不存在非零多项式 $P(X,Y)$ 使 $P(x,\log x)=0$ 对全部 $x>0$ 成立。
\end{proposition}
\begin{proof}
写 $P(X,Y)=\sum_{j=0}^dX^jq_j(Y)$，其中 $q_d\ne0$。
令 $x=e^t$，除以 $e^{dt}$，得到
$q_d(t)+\sum_{j<d}e^{-(d-j)t}q_j(t)=0$。
令 $t\to+\infty$，每个后项趋零，迫使非零多项式 $q_d(t)\to0$，矛盾。
\end{proof}

这个自足反证排除对数满足非零全域代数方程。
若用 $e^y=x$ 定义它，指数关系已经进入语言；
若取级数或积分，则收敛、域和分支也属于关系内容。

\begin{theorem}[连续读出的二次网一致逼近]\label{thm:bernstein}
若 $f:[0,1]\to\R$ 或 $\C$ 连续，令 $M=\sup|f|$，对整数 $n\ge1$ 取
\[
B_nf(x)=\sum_{k=0}^n f(k/n)\binom nkx^k(1-x)^{n-k}.
\]
每个 $B_nf$ 可编译为有限二次网，且对任意 $\delta>0$，
\[
\boxed{
\sup_x|B_nf(x)-f(x)|
\le\omega_f(\delta)+\frac{M}{2n\delta^2},}
\]
其中 $\omega_f$ 是连续模。因此 $B_nf\to f$ 一致收敛。
\end{theorem}
\begin{proof}
记非负二项权重为 $w_k$。
由二项式恒等式及其一、二阶形式，
$\sum w_k=1$，
$\sum w_k(k/n-x)^2=x(1-x)/n\le1/(4n)$。
在 $|k/n-x|\le\delta$ 的部分，误差至多 $\omega_f(\delta)$；
补集总权重至多 $1/(4n\delta^2)$，每项差至多 $2M$。
相加得界。一致连续性允许先取小 $\delta$、再取大 $n$。
有限多项式由定理 \ref{thm:compile} 编译。
\end{proof}

系数 $f(k/n)$ 仍需由已知函数或内部数据供应；定理不产生未知函数值。
更高维紧立方体可用乘积权重作同样证明。
无限量子整体还需相容有限端口、正性与所用完备化条件，
不是一张固定有限网已经装下任意无限信息。

\plain{有限脚本负责一层精度，递归延长可以继续逼近。
“可以无限继续”能成为一个有误差界的结论；
每一层所用的关系值、误差和适用范围仍保留在整体描述中。}

\section{更简洁的结构起点：一个正关系呈示}
\begin{definition}[同源正关系体]
取带伴随的关系符号 $S$、由具体约束生成的 $*$ 理想 $\mathcal I$，
及其商代数上的共同正归一 Hermitian 响应 $\ell$：
\[
\boxed{
\mathfrak R=(\Alg,\ell),\qquad
\Alg=\R\langle S,S^*\rangle/\mathcal I.}
\]
来源为正关系商中的 $\Omega=[1]$；
状态、历史、读口和比较程序以同一代数及其声明的内部复合接口表示。
实际有限菜单及其覆盖另列为可认证的关系条件。
\end{definition}

这把“基础操作”和“结构约束”分开组织：
线性词展开与双线性复合给统一语言；
哪些词相等、哪些组合正、哪些读数相容，决定具体关系体。
新关系若只是旧表达式的定义性展开，定理 \ref{thm:positive} 保证
不需新的独立状态假设。

量子选择条件可以明确写在该结构内部。例如项目 V58 的实三轴关系
\[
X^*=X,\ Y^*=Y,\ Z^*=Z,\quad X^2=Y^2=Z^2=1,\quad
XY=-YX,\ YZ=-ZY,\ ZX=-XZ
\]
给 $J=XYZ$、$J^2=-1$ 和局部 $M_2(\C)$ 实代数。
不同原子对易，再施加共同中心 $J_a=J_b$，给共同复矩阵复合。
这些均可保守二次化；有限复合下每个字母的乘法次序保留。
取得中心复结构后，正确响应为
\[
\ell_{\C}(a)=\ell_{\R}(a)-i\ell_{\R}(Ja),
\]
而非把实值函数原样改称复线性 \cite{v58}。
完整效果分解相容给定理 \ref{thm:born}；
有限矩阵块上保持完整乘法、伴随和复结构的可逆自同构有酉实现；
同一目标线性规则在已校准完整参考上有正的关联输出，
并满足仪器归一，再结合内部 ready 接口，得到 CP 仪器及其酉记录实现。
这里须认证该参考输出确由同一 $\Lambda\otimes\id$ 产生。
本稿采用上述条件结论，不声称已推导全部动力学及实际控制。

\begin{proposition}[约束可以打包，但内容不会因此消失]
对有限个实标量残差 $r_j$，
\[
\forall j,\ r_j=0
\quad\Longleftrightarrow\quad
\sum_jr_j^2=0.
\]
对有界算子残差，
$\sum_jr_j^\dagger r_j=0$ 等价于全部 $r_j=0$；
仅有其在一个 $\Omega$ 上的期望为零，只推出全部 $r_j\Omega=0$。
\end{proposition}
\begin{proof}
标量式各项非负。算子式对任意向量取二次型，得到
$\sum_j\|r_jv\|^2=0$；只代入 $\Omega$ 时结论相应受限。
\end{proof}
无界情形须在共同稠密定义域上以该二次型恒等式表述，
不能省略乘积与伴随的定义域条件。

所以一条还是多条“公理”的数目容易随写法改变。
可以直接研究这个整体是否有解、是否唯一到共同表示、是否稳定，
而不把绝对最少条数作为本轮目标。

同一加乘语言也容纳经典交换模型。
例如 $\R\oplus\R$ 上
$\ell_p(a,b)=pa+(1-p)b$（$0\le p\le1$）全部正且归一。
这些是对结构选择的比较，不要求实际本体可以更换。
它们说明量子内容由上述非交换、复定向、正性和复合约束承担。
所有参考和数据可以内生，但实际约束值仍须由内部关系确定。

存在量词也能参与这个表达：
$\rho\succeq0\iff\exists B:\rho=BB^\dagger$。
它回答合法实现是否存在；对于
$\rho_p=\operatorname{diag}(p,1-p)$，所有 $0<p<1$ 都使两事件可能，
却给不同权重。因此存在性本身不选择实际概率数值。

\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.30\textwidth}X@{}}
\toprule
用户直觉的严格版本 & 本轮证明的内容\\
\midrule
任意关系可以线性表达 & 自由空间与张量上的精确线性表示；系数保留全部原信息。\\
高次关系只需加乘 & 有限脚本恰生成多项式；任意有限代数呈示可二次化。\\
关系本身还能继续拆解 & 保守商同构、正响应对应与同一 $\Omega$ 保持。\\
提升后剩下的是约束 & 二次方程线性提升，配共同秩一与正性像条件。\\
平方是最低关系层 & 在双线性非负闭合或共同相位多项式类中有明确二次定理。\\
所有量子对象都在整体内 & 固定有限协议有共同二次表示及内部纯来源酉实现。\\
公理可写成内部关系 & 可把具体结构条件组织为同一个正关系呈示；须保留其实际内容。\\
\bottomrule
\end{tabularx}
\end{center}

因此本轮的凝练表述是
\[
\boxed{\text{线性承载}+\text{双线性复合}
+\text{同源正性与整体相容约束}.}
\]
这是一个可证明、可逐步认证的量子关系重建方案，
尚未从无前件确定实际宇宙的全部约束或其唯一物理实现。

\Needspace{9\baselineskip}
\plain{在这套条件图景里，同一个 $\Omega$ 经过历史，产生所有内部读出。
复杂关系可以展开成加法与乘法的小结点；每个中间名字都要能接回它所代表的那段历史。
把关系搬到更大的坐标空间后，读出可以变得线性，
但这些坐标必须同时来自同一个来源，不能各自随意取值。
正性、归一、共同复定向、门的接续和记录的一致性，就在整张网里约束它们。
观察者的预测、校准和推理也使用这同一种关系语言。
研究量子起源于是可以集中为：证明这张整体关系网怎样允许叠加、怎样保持相干，
怎样产生平方读出，以及哪些条件把它锁定成量子结构。}

\clearpage
\begin{thebibliography}{99}\small
\bibitem{v17} 项目固定提交。
\repo{AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md}{V17：加乘、对数与量子勾股几何}，
定义 1.1、§2、§8，以及 §13 的所用一般结论。
\bibitem{v49} 项目固定提交。
\repo{AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md}{V49：加乘指数、二次关系闭合与归一化升维}，§§2--8。
\bibitem{v52} 项目固定提交。
\repo{AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md}{V52：纯态商几何、二次关系生成与无损递归}，§§1--2、5--7 的所用结论。
\bibitem{v58} 项目固定提交。
\repo{AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md}{V58：关系公理、共同复相位与条件量子重建}，§§2--8、10--14。
\bibitem{v59} 项目固定提交。
\repo{AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md}{V59：局部层析、相干读出轨道与正性起源}，
§1.2、§§2--6 的相关条件及 §10；包括命题 5.3、定理 5.4。
\bibitem{omega} 项目固定提交。
\repo{AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md}{$\Omega$ 静态相容纤维理论}，
§§1--8、12 的有限关系与协议接口；不认证全部后续供应链。
\bibitem{tensor} Keith Conrad.
\href{https://kconrad.math.uconn.edu/blurbs/linmultialg/tensorprod.pdf}{\emph{Tensor Products}}，
本轮核对 §§2--3 的双线性、外积像及通用性质相关段落。
\bibitem{arithmetic} J. Bootle, A. Cerulli, P. Chaidos, J. Groth, C. Petit.
\emph{Efficient Zero-Knowledge Arguments for Arithmetic Circuits in the Discrete Log Setting}.
EUROCRYPT 2016.
\href{https://discovery.ucl.ac.uk/id/eprint/10090338/1/263.pdf}{作者完整版}，
本轮仅消费 §5 乘法/线性约束表示及附录 A 的相应电路转换段落，
不消费安全性或复杂度证明。
\bibitem{busch} P. Busch.
\emph{Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem}.
Phys. Rev. Lett. 91, 120403 (2003).
\href{https://arxiv.org/pdf/quant-ph/9909073}{arXiv:quant-ph/9909073v3}，
本轮核对完整效果条件、主定理证明及二维说明；本文使用有限维版本。
\bibitem{realalg} S. Basu.
\emph{Algorithms in Real Algebraic Geometry: A Survey}.
\href{https://www.math.purdue.edu/~sbasu/raag_survey2011_final.pdf}{作者公开稿}，
本轮核对 §2.1 定理 2.1 的实量词消元陈述及前件，
不声称重证一般消元算法。
\end{thebibliography}
\end{document}
```
AURIC-V76-IMMUTABLE-SOURCE-END -->

**加乘生成、二次关系网**  
**与内生量子结构**

从统一表达语言到整体相容约束

定义、定理与纸面证明　v76.0

2026 年 11 月 1 日　Asia/Singapore

## 摘要

本稿把研究目标从“寻找绝对最少的公理条数”转为“统一表达、保守展开与约束完备性”。
任意集合关系都能在自由线性空间中精确读出，但其完整系数仍承载原关系信息。
有限加乘脚本恰生成多项式；每个有限代数关系体都能通过辅助结点改写成总次数至多二的约束。
证明该展开在交换、非交换及带伴随代数中均保守：原商代数、全部旧关系、正响应与同一来源的最小循环表示保持。
进一步，全部二次标量约束可转成提升矩阵上的线性读出，合法像由一个共同秩一约束限定。
量子方面，承接项目既有的双线性权重闭合与共同相位二次生成，
给出有限维、有限历史量子协议的精确实二次约束表示，保留正性、完全正性、同标签过程复用及零概率分支。
其内部记录实现仍可写成一个固定 $\Omega$ 的整体酉历史。
全文区分关系表示、关系推导与物理实现，并给出递归逼近和误差条件。

## 1 本轮方向与固定项目依据

可以把问题改为：用统一的加乘关系语言表达对象，
再由整个网络必须共同满足的条件确定量子结构。
不必先解决“所有可能形式语言中究竟几条公理最少”。
真正需要证明的是表达是否完整、展开是否保留信息、哪些约束选择了量子模型。

本轮唯一实时 HEAD GET 于新加坡时间 2026-11-01 21:09:47
在收到 HTTP 响应前遭遇网络权限拒绝；没有重试、重定向、备用活动端点或升级。
以下采用重新核对六份 Git blob 的固定提交

`5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b`。

不声称取得该提交之后的新仓库进展；v76 为本对话稿件编号。

> **编者注（Markdown 实施者）：历史报告的归属。** 本段的 21:09:47 拒绝、未重试、六 blob 复核及下文“独立纸面复核”等均逐字保留为作者的历史报告，不构成本次实施者重新取得活动 HEAD 或完成独立评审的主张。文献末各“本轮核对”亦沿用该作者归属。


| 固定来源 | 实际承接内容 |
| --- | --- |
| V17 §2、§8 | 加乘 DAG；直和、张量及相干叠加的区别。 |
| V49 §§2--8 | 有限加乘范围、双线性闭合、二次权重与提升像。 |
| V52 §§5--7 | 相位不变量的二次生成、正效果读出与递归相容。 |
| V58 §§2--8、10--14 | 实关系代数、复定向、正响应、GNS、酉与内部仪器。 |
| V59 §§1--6、10 的所用段 | 完整线性关系、正性覆盖和实际读数之间的接口。 |
| $\Omega$ §§1--8、12 | 静态关系、全局相容、固定门传播及有限内部协议。 |

V49 与 V52 的既有定理不列作本轮新发现。
一般电路的辅助变量二次化属于标准关系编码；
本稿给出其非交换 $*$ 代数及同源正响应版本的自足证明。
只消费所列实际相关段落，不认证全部仓库或全部原生控制供应链。
所有数学均为纸面推导与独立纸面复核；没有数学程序、CAS、数值、枚举、仿真或机器证明。

**白话图景。** 不必给每一种复杂关系另取一个基础原理。
先统一它们的写法，再检查这些写法怎样互相约束、怎样共同成立。
“都在同一个整体里”可以具体落实为：同一对象在各处复用，
同一来源的响应在各种拆法中一致。

## 2 “线性足够表达关系”的两种准确含义

#### 定义 2.1（固定系数线性与双线性复合）

$T$ 线性是指 $T(\alpha x+\beta y)=\alpha T(x)+\beta T(y)$。
乘法 $\mu(x,y)=xy$ 在含幺结合代数中对每一槽分别线性，称为双线性。
它通常不对联合输入 $(x,y)$ 线性。

例如 $\mu(2x,2y)=4xy$；联合线性则会要求 $2xy$。
线性映射的有限和与复合仍线性，不能因此产生 $x\mapsto x^2$。
另一方面，对固定 $H$，$e^{iH}$ 仍是固定线性算子；
“表达式是否出现指数符号”不能判定它对所谈变量是否线性。

> **编者注（Markdown 实施者）：变量与定义域。** 这里的反例使用实或复标量，且需选取 $xy\ne0$ 才区分 $4xy$ 与 $2xy$；零乘积处的等式不构成联合线性的证明。固定 $e^{iH}$ 的表述按已定义的有限维矩阵指数理解；无界 $H$ 时须另给相应算子与定义域条件。

项目 V17、V49 已作这些对象层的区分 [1](#ref-v17)、[2](#ref-v49)。

<a id="thm:allrelations"></a>

#### 定理 2.2（任意集合关系的自由线性表示）

给任意集合 $X,Y$ 及任意关系 $R\subseteq X\times Y$。
取有限支撑自由向量空间
$V_X=\mathbb{R}^{(X)}$、$V_Y=\mathbb{R}^{(Y)}$。
存在唯一线性泛函

$$
\boxed{L_R:V_X\otimes V_Y\longrightarrow\mathbb{R},\qquad
L_R(e_x\otimes e_y)=1_R(x,y).}
$$

且 $R\mapsto L_R$ 为单射。

**证明。**

张量基为 $\{e_x\otimes e_y\}$。对唯一的有限展开定义
$L_R(\sum c_{xy}e_x\otimes e_y)=\sum c_{xy}1_R(x,y)$，
即得良定义、线性及唯一性。
不同关系在某个基张量上的值不同，故该对应单射。

∎

因此“任意关系有线性表示”确有一个不要求有限集合的严格版本。
它保留全部关系信息。原始输入对编码为基张量，
任意叠加不一定仍是一个原始输入，其读数也不一定是零或一。
无限系数表与无限维自由空间没有自动给有限脚本、有效算法、Hilbert 范数或量子概率。

#### 定理 2.3（双线性的张量线性化）

任意双线性映射 $B:V\times W\to Z$ 唯一因子化为

$$
\widehat B:V\otimes W\to Z,\qquad
\widehat B(u\otimes v)=B(u,v),
$$

其中 $\widehat B$ 线性。

**证明。**

在形式对的自由线性空间上令 $(u,v)\mapsto B(u,v)$。
双线性保证该映射消去张量积定义中的双线性关系，故下降到商。
纯张量张成商空间，故唯一。

∎

这是张量积的通用性质 [7](#ref-tensor)。
在矩阵坐标中，一个输入对 $u,v$ 对应 $Z_{ij}=u_iv_j$，
其矩阵秩至多一；一般张量不再代表一个单独的输入对。

> **编者注（Markdown 实施者）：张量与自由空间的域。** 张量积及双线性均在同一标量域上；文中的矩阵坐标读法先用于有限维。任意集合的自由空间使用有限支撑，空集合给零空间，唯一零泛函仍满足定理 2.2。没有赋予拓扑便没有连续或有界性的结论，也没有由无限系数表取得有效算法的结论。


**白话图景。** 可以把关系搬到足够大的坐标空间，让读出成为线性的。
但坐标的合法取值仍要反映它们来自同一个输入。
线性读出负责读取；输入一致性负责说明读到的究竟是哪一种关系。

## 3 有限加乘关系的精确二次化

#### 定义 3.1（有限算术脚本）

输入为域 $\mathbb{F}=\mathbb{R}$ 或 $\mathbb{C}$ 中的常数及变量。
内部结点为两个已有量的加法或乘法，依赖图有限且无环。
允许共享子表达式；负号可由常数 $-1$ 给出。

#### 命题 3.2（加乘的表达范围）

交换输入的有限脚本恰生成 $\mathbb{F}[x_1,\ldots,x_n]$；
非交换输入的形式脚本恰生成自由结合代数
$\mathbb{F}\langle x_1,\ldots,x_n\rangle$。

**证明。**

按拓扑顺序归纳，每个输出仍为多项式或有限词的线性组合。
反向逐个相乘形成单项式或词，再有限相加即得脚本。

∎

这是项目 V49 命题 2.3 的直接延伸 [2](#ref-v49)。
固定自然数幂已在语言内；一般变量指数与对数还须其他关系或极限。

<a id="thm:compile"></a>

#### 定理 3.3（二次约束网的唯一中间量）

按门顺序引入中间变量 $z_i$，加入

$$
\boxed{q_i=z_i-u_i-v_i=0
\quad\text{或}\quad q_i=z_i-u_iv_i=0.}
$$

其中 $u_i,v_i$ 只使用原输入、常数与编号更小的中间量。
对每个原输入，全部 $z_i$ 存在且唯一，
并恰等于原脚本相应结点的值。
原输出图是该二次约束集的坐标投影。

> **编者注（Markdown 实施者）：二次门的操作数。** 这里每个 $u_i,v_i$ 是一条输入线上的单个已有量，即原变量、常数或先前门变量；不能把未编译的任意高次表达式直接放进这两个位置再称总次数至多二。原关系输出所需的全部门变量均并入 $B$；理想与交集结论以自然嵌入的旧生成元子代数识别 $A$。


**证明。**

第一结点由输入唯一确定；后续结点依次由已确定的前驱唯一确定。
原脚本求值给存在性，逐结点代入给反向等价。
同一证明适用于任意含幺结合代数，并保留乘法顺序。

∎

例如

$$
p(x,y)=(x+y)^2+xy
$$

可写为

$$
a=x+y,\qquad b=aa,\qquad c=xy,\qquad p=b+c.
$$

<iframe title="原稿加乘 DAG（窄屏可在图内横向滚动）" width="99%" height="330" srcdoc="&lt;svg width=&quot;1100&quot; height=&quot;300&quot; viewBox=&quot;0 0 1100 300&quot; role=&quot;img&quot; aria-label=&quot;加乘 DAG：x、y 同时指向 a=x+y 与 c=xy；a 指向 b=aa；b、c 指向 p=b+c&quot; xmlns=&quot;http://www.w3.org/2000/svg&quot;&gt;
&lt;defs&gt;&lt;marker id=&quot;v76-arrow&quot; viewBox=&quot;0 0 10 10&quot; refX=&quot;9&quot; refY=&quot;5&quot; markerWidth=&quot;7&quot; markerHeight=&quot;7&quot; orient=&quot;auto-start-reverse&quot;&gt;&lt;path d=&quot;M 0 0 L 10 5 L 0 10 z&quot; fill=&quot;#18354f&quot;/&gt;&lt;/marker&gt;&lt;/defs&gt;
&lt;g fill=&quot;none&quot; stroke=&quot;#18354f&quot; marker-end=&quot;url(#v76-arrow)&quot;&gt;
&lt;path d=&quot;M175 50 L325 50&quot;/&gt;&lt;path d=&quot;M145 220 L355 80&quot;/&gt;
&lt;path d=&quot;M145 80 L355 220&quot;/&gt;&lt;path d=&quot;M175 250 L325 250&quot;/&gt;
&lt;path d=&quot;M475 50 L625 50&quot;/&gt;&lt;path d=&quot;M775 75 L925 125&quot;/&gt;&lt;path d=&quot;M475 237.5 L925 162.5&quot;/&gt;
&lt;/g&gt;
&lt;g fill=&quot;white&quot; stroke=&quot;#18354f&quot;&gt;&lt;rect x=&quot;25&quot; y=&quot;20&quot; width=&quot;150&quot; height=&quot;60&quot; rx=&quot;6&quot;/&gt;&lt;rect x=&quot;25&quot; y=&quot;220&quot; width=&quot;150&quot; height=&quot;60&quot; rx=&quot;6&quot;/&gt;&lt;rect x=&quot;325&quot; y=&quot;20&quot; width=&quot;150&quot; height=&quot;60&quot; rx=&quot;6&quot;/&gt;&lt;rect x=&quot;325&quot; y=&quot;220&quot; width=&quot;150&quot; height=&quot;60&quot; rx=&quot;6&quot;/&gt;&lt;rect x=&quot;625&quot; y=&quot;20&quot; width=&quot;150&quot; height=&quot;60&quot; rx=&quot;6&quot;/&gt;&lt;rect x=&quot;925&quot; y=&quot;120&quot; width=&quot;150&quot; height=&quot;60&quot; rx=&quot;6&quot;/&gt;&lt;/g&gt;
&lt;g fill=&quot;#18354f&quot; text-anchor=&quot;middle&quot; font-size=&quot;24&quot;&gt;&lt;text x=&quot;100&quot; y=&quot;59&quot;&gt;x&lt;/text&gt;&lt;text x=&quot;100&quot; y=&quot;259&quot;&gt;y&lt;/text&gt;&lt;text x=&quot;400&quot; y=&quot;59&quot;&gt;a=x+y&lt;/text&gt;&lt;text x=&quot;400&quot; y=&quot;259&quot;&gt;c=xy&lt;/text&gt;&lt;text x=&quot;700&quot; y=&quot;59&quot;&gt;b=aa&lt;/text&gt;&lt;text x=&quot;1000&quot; y=&quot;159&quot;&gt;p=b+c&lt;/text&gt;&lt;/g&gt;
&lt;/svg&gt;"></iframe>

> **编者图形转录说明。** 原图的坐标为 $x:(0,1)$、$y:(0,-1)$、$a:(3,1)$、$c:(3,-1)$、$b:(6,1)$、$p:(9,0)$；箭头为 $x\to a$、$y\to a$、$x\to c$、$y\to c$、$a\to b$、$b\to p$、$c\to p$。

图中复用是同一数学值的复用；没有声明这是从未知单份量子态实施复制的门。
所有结点约束的总次数至多二，并不都是齐次二次。
算术电路的乘法约束与线性一致性关系是标准编码 [8](#ref-arithmetic)。

### 更强的结论：原关系代数完全保持

令 $A=\mathbb{F}\langle x\rangle$、$B=\mathbb{F}\langle x,z\rangle$；
交换情形换成通常多项式代数。
记 $J$ 为全部门缺陷 $q_i$ 生成的双边理想，
令 $p_i(x)$ 为原脚本的各中间表达式。

<a id="thm:conservative"></a>

#### 定理 3.4（保守二次呈示）

代入同态 $\Phi:B\to A$ 由
$\Phi(x_j)=x_j$、$\Phi(z_i)=p_i(x)$ 给出。
则

$$
\boxed{\ker\Phi=J,\qquad B/J\cong A.}
$$

若再给原关系理想 $I=\langle r_1,\ldots,r_s\rangle$，
将每个 $r_j$ 编译并令对应输出为零，得到 $\widetilde I$，则

$$
\boxed{B/\widetilde I\cong A/I,\qquad
\widetilde I\cap A=I.}
$$

**证明。**

所有门缺陷代入为零，故 $\Phi$ 下降为 $\bar\Phi:B/J\to A$。
原输入包含给 $\iota:A\to B/J$，且 $\bar\Phi\iota=\operatorname{id}_A$。
依门顺序归纳，商中 $[z_i]=p_i([x])$，
所以 $\iota\bar\Phi$ 固定全部生成元，也为恒等映射。
这证明第一个同构及核等式。
在该同构下，输出零约束正好变成 $r_j=0$，
再取商即得第二组等式。

∎

带伴随版本给每个中间符号配形式伴随，
把 $q_i$ 和 $q_i^*$ 纳入 $*$ 理想，上述同构成为 $*$ 同构。
若 $u,v$ 自伴而不交换，$uv$ 通常不自伴；
不能额外要求新符号 $z=uv$ 自伴，否则会加入原来没有的约束。
定理保留的是代数呈示及全部表示，没有用未证明的代数几何零点定理。

> **编者注（Markdown 实施者）：带伴随呈示。** 星版本使用自由含幺实或复星代数，复数上的星共轭标量；门的星关系同时消去形式伴随变量。旧关系若也要求星呈示，$I$ 须为星理想。对有限给定关系的二次呈示不意味着任意无限关系族自动具有有限呈示。


**白话图景。** 高次关系能拆成很多只做一步的小结点。
更强的是，拆完以后原来能推出哪些关系、不能推出哪些关系，都保持不变。
这些中间结点只是把原脚本展开，不增加本体的自由度。

## 4 正响应与同一个 $\Omega$ 也在展开中保持

#### 定义 4.1（共同正响应）

在实或复 $*$ 代数上，$\ell$ 为线性泛函，

$$
\ell(1)=1,\qquad
\ell(a^*)=\overline{\ell(a)},\qquad
\ell(a^*a)\ge0.
$$

实数情形同样明确要求伴随对称。
取
$N_\ell=\{a:\ell(a^*a)=0\}$，
以 $[1]$ 为来源，并以左乘作用于 $\mathcal{A}/N_\ell$。

正性的 Cauchy--Schwarz 保证 $N_\ell$ 为左理想：
若 $p\in N_\ell$，则 $\ell(p^*q)=0$；
取 $q=a^*ap$ 得 $ap\in N_\ell$。
因此商内积与左乘良定义，这给最小循环表示
$(\pi,\mathcal{H}_\ell,\Omega)$。
一般先在代数共同定义域工作，不无条件声称所有算子有界。

> **编者注（Markdown 实施者）：零空间、稠密域与伴随。** 由 Cauchy–Schwarz，$\ell(p^*q)=0$ 对所有 $q$；令 $q=a^*ap$ 即得 $\ell((ap)^*ap)=0$。左乘表示先作用于前 Hilbert 空间 $\mathcal A/N_\ell$，完成后以其为共同稠密不变域；此处的星表示指域上的内积伴随恒等式，不把每个对称算子宣称为自伴或有界。


<a id="thm:positive"></a>

#### 定理 4.2（正响应的保守扩展）

在定理 [3.4](#thm:conservative) 的 $*$ 版本中，
$A$ 上的正归一 Hermitian 响应与 $B$ 上满足

$$
\widetilde\ell(w^*q_i^*q_iw)=0
\quad\text{对全部门 }i\text{ 及全部词 }w
$$

的正归一 Hermitian 响应一一对应：

$$
\boxed{\widetilde\ell=\ell\circ\Phi.}
$$

两者的最小循环表示等距同构，且固定同一个 $\Omega$。

**证明。**

$*$ 同态拉回显然保持正性、伴随对称和归一，并使所有门缺陷为零。
反向在 $\widetilde\ell$ 的循环表示中，所列数是
$\|\pi(q_i)\pi(w)\Omega\|^2$。
全部为零说明 $\pi(q_i)$ 消去所有生成词向量，
故表示商去整个 $*$ 理想 $J$。
由 $B/J\cong A$ 唯一下降到 $A$。
显式等距同构为

$$
[b]_{\widetilde\ell}\longmapsto[\Phi(b)]_\ell,
$$

因为双方内积同为 $\ell(\Phi(b)^*\Phi(c))$。
原输入包含保证满射，$1\mapsto1$ 保持来源。

> **编者注（Markdown 实施者）：全上下文如何消去星理想。** “全部词”含空词及全部星字母，有限线性组合张成共同域。$\pi(q_i)$ 在该域上为零后，对任意域向量 $\xi,\eta$，$\langle\pi(q_i^*)\xi,\eta\rangle=\langle\xi,\pi(q_i)\eta\rangle=0$，故 $\pi(q_i^*)$ 也为零。域不变性遂使整个双边星理想作用为零。显示的等距映射在前 Hilbert 空间满射，完成后为保持循环向量的酉等价（实域为正交等价）；它不新增另一份独立来源。


∎

如果新符号只是旧表达式的定义，等式由保守展开保证。
如果它代表另一台实际未知装置，则仍须认证它在全部声明上下文中执行同一关系。
单有 $q_i\Omega=0$ 一般不足；
v75 的完整锚覆盖或关系族接续闭合，给可缩减检验的具体条件。
代数和 $U+V$ 也通常不是酉门，表达式合法与实际控制可用是两个明确问题。

**白话图景。** 给已有关系加一个新名字，不会产生另一个来源。
只要新名字在所有用法里都指向原表达式，正响应和同一个 $\Omega$ 也不变。
观察者自己记录、展开和检验这些关系，仍可属于同一整体。

## 5 把全部二次方程再变成线性读出：共同来源约束在哪里

<a id="thm:ranklift"></a>

#### 定理 5.1（二次关系的整体秩一提升）

给实变量 $z\in\mathbb{R}^N$ 和有限个次数至多二的实多项式 $q_\alpha(z)$。
令 $v=(1,z_1,\ldots,z_N)^{\mathsf T}$。
存在实对称矩阵 $A_\alpha$ 使
$q_\alpha(z)=v^{\mathsf T}A_\alpha v$。
以实对称矩阵 $Y\in\mathbb S^{N+1}(\mathbb{R})$ 为未知量，原方程组等价于

$$
\boxed{
\operatorname{Tr}(A_\alpha Y)=0\ \forall\alpha,\qquad
Y\succeq0,\quad Y_{00}=1,\quad\operatorname{rank} Y=1.
}
$$

恢复公式为 $z_i=Y_{i0}$。

**证明。**

常数项置于 $A_{00}$；一次项与非对角二次项在对称位置各分一半，
平方项置于相应对角，便得所述 $A_\alpha$。
正向取 $Y=vv^{\mathsf T}$。
反向由秩一正性写 $Y=uu^{\mathsf T}$。
$Y_{00}=1$ 给 $u_0=\pm1$；取 $z_i=u_i u_0=Y_{i0}$，
则 $Y=(1,z)(1,z)^{\mathsf T}$，还原所有方程。

> **编者注（Markdown 实施者）：提升边界。** $Y_{00}=1$ 排除秩零；$N=0$ 时仅有 $Y=[1]$，结论仍成立。对称化一次项和交叉项各分一半，依赖于实标量的交换性；本节是标量坐标提升，不把非交换算子乘积直接替换为这个实对称矩阵乘积。


∎

于是有限代数关系具有一条完整链：

$$
\boxed{
\text{高次关系}\ \longrightarrow\
\text{局部二次约束}\ \longrightarrow\
\text{线性读出与共同秩一一致性}.}
$$

这一“秩一”是所有标量变量来自同一次确定赋值的条件；
它不等于局部物理密度矩阵必须纯。
若原协议里有混态 $\rho$，$\rho$ 的各条目仍是 $z$ 中的确定数，
与这个形式提升矩阵 $Y$ 秩一并不冲突。

不能删去 $Y$ 的合法像条件。例如原方程
$x^2-1=0$ 与 $x=0$ 无共同解；
在 $v=(1,x)$ 的提升中，它们要求
$Y_{11}=Y_{00}=1$、$Y_{01}=0$。
$Y=I_2$ 为正且满足这些线性式，却秩二，并非一个原输入。
去掉秩条件会增加原问题没有的解。

#### 命题 5.2（不是每组二元正关系都能拼成整体）

取三阶实对称矩阵，所有对角为一、所有非对角为 $-3/4$。
每个二阶主块均正定，但整矩阵不是半正定。

**证明。**

每个二阶块的本征值为 $1\pm3/4>0$。
而全一向量的二次型值为
$3+6(-3/4)=-3/2<0$。

∎

项目 V58 命题 12.2 与 V17 的 Gram 闭路分析已指出同类整体约束 [4](#ref-v58)、[1](#ref-v17)。
二元结点可作表达积木，整体正性仍须在同一个共同实现中成立。

**白话图景。** 可以让最后的读取都成为线性的。
真正把这些坐标绑在一起的，是“它们来自同一个输入、同一个来源”的条件。
每两块分别能拼起来，还须检查三块乃至整张网能否同时拼成一个整体。

## 6 平方的特殊性：关系闭合，而不只是表达式的次数

### 非负权重的双线性叠加修正

<a id="thm:quadraticweight"></a>

#### 定理 6.1（双线性闭合选择二次型）

设实向量空间上 $Q\ge0$、$Q(0)=0$，并令

$$
C_Q(u,v)=\frac{Q(u+v)-Q(u)-Q(v)}2.
$$

若 $C_Q$ 实双线性，则 $Q(v)=C_Q(v,v)$，
且 $C_Q$ 对称半正定。反向成立。

**证明。**

记 $B=C_Q$。定义使 $B$ 对称，且
$L(v)=Q(v)-B(v,v)$ 可加。
对每个正整数 $n$，

$$
0\le Q(\pm v/n)=B(v,v)/n^2\pm L(v)/n.
$$

故 $B(v,v)\ge n|L(v)|$ 对全部 $n$ 成立，只能 $L(v)=0$。
反向展开二次型即可。

∎

这是项目 V49 定理 4.2 的既有结果 [2](#ref-v49)。
它不用预设 $Q$ 连续或偶。
实双线性是所用相容条件；“两个输入”单独不保证它。
例如 $x^4$ 也可用两个平方结点表示，
所以“可编译成二次网”本身不选定 Born 指数。

### 共同相位关系的二次生成

<a id="thm:invariant"></a>

#### 定理 6.2（共同相位不变量由外积生成）

在已给 $\mathbb{C}^d$ 上，关于 $z,\bar z$ 的多项式若满足
$P(e^{i\theta}z,e^{-i\theta}\bar z)=P(z,\bar z)$，
则它由 $G_{ij}=z_i\bar z_j$ 加乘生成。
最低非恒定总次数为二。

> **编者注（Markdown 实施者）：零维边界及不变性量词。** “最低非恒定总次数为二”要求 $d\ge1$；$d=0$ 时只有常数，不存在最低非恒定次数。相位不变性对所有 $z$ 和所有实 $\theta$ 成立；先按频率分组，再用全域单项式独立性排除非零频率，不能仅在某个固定 $z$ 上逐项断言。


**证明。**

单项式 $z^\alpha\bar z^\beta$ 在相位作用下乘
$e^{i(|\alpha|-|\beta|)\theta}$。
不同整数频率线性独立，故不变项须满足 $|\alpha|=|\beta|$。
把振幅因子与共轭因子逐个配对，即成若干 $G_{ij}$ 的乘积。

∎

这承接项目 V52 定理 5.2 [3](#ref-v52)。
$G=zz^\dagger$ 分离共同相位轨道，并保留 $\operatorname{Tr} G=\|z\|^2$。
其合法像满足

$$
G=G^\dagger,\quad G\succeq0,\quad\operatorname{rank} G\le1,\quad
G_{ij}G_{kl}=G_{il}G_{kj}.
$$

非零后再作迹归一，才同时消去正尺度。
局部相位若相对于整体其他部分可测，不能直接当作全局共同相位删去。

### 为何二元块有三轴

对归一 $\psi=(a,b)^{\mathsf T}$，定义

$$
x=2\Re(\bar a b),\quad y=2\Im(\bar a b),\quad z=|a|^2-|b|^2.
$$

直接展开得

$$
\boxed{x^2+y^2+z^2=(|a|^2+|b|^2)^2=1.}
$$

等价地 $\rho=\psi\psi^\dagger=(I+x\sigma_x+y\sigma_y+z\sigma_z)/2$。
一般正迹一二阶 Hermitian 矩阵给 $x^2+y^2+z^2\le1$，
因为本征值为 $(1\pm\sqrt{x^2+y^2+z^2})/2$。
这解释已声明二元块的三轴，不把任意高维整体无损压成三个实数。
与原 AURIC 五模式标签对应时，仍须采用实际读口编码。

> **编者注（Markdown 实施者）：Pauli 符号。** 采用 $\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix}$、$\sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$、$\sigma_z=\operatorname{diag}(1,-1)$。因 $\rho_{12}=a\bar b=(x-iy)/2$，原文 $y=2\Im(\bar a b)$ 的正号与该约定一致。三轴解释限于已给的二阶复 Hermitian 块。


**白话图景。** 平方可以是最低的相位不变关系，也可以由非负权重的双线性闭合强迫出来。
复杂关系再由这些二次量继续加乘。
二元复块归一后出现三条读出轴，而三轴之间的球面条件继续保留它们来自同一个纯态的事实。

## 7 从整体读出相容到 Born 形式

二次生成说明可以用哪些关系坐标，概率还须满足同一效果在不同分解下的响应一致。

<a id="thm:born"></a>

#### 定理 7.1（完整正效果响应的迹表示）

在有限维复矩阵效果域 $\mathcal E=\{E:0\preceq E\preceq I\}$ 上，
设 $p:\mathcal E\to[0,1]$，
$p(I)=1$，并且

$$
p(E+F)=p(E)+p(F)\qquad(E,F,E+F\in\mathcal E).
$$

则存在唯一 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，使

$$
\boxed{p(E)=\operatorname{Tr}(\rho E).}
$$

若 $\rho=\ket\psi\bra\psi$，则对单位向量 $\phi$，
$p(\ket\phi\bra\phi)=|\langle\phi,\psi\rangle|^2$。

**证明。**

对正矩阵 $A$，选正整数 $m$ 使 $A/m\le I$，
定义 $\widetilde p(A)=m p(A/m)$。
用共同倍数和有限可加性证明与 $m$ 无关，并在正锥上可加。
以差延拓到 Hermitian 空间；两种差分解由交叉相加保证一致。
可加性先给有理齐次性；正性使泛函序保持。
对任意有理数 $r>\|X\|$，有 $-rI\le X\le rI$，
故 $|\widetilde p(X)|\le r$，进而不超过 $\|X\|$。
这给连续性，再以有理数逼近任意实数，得到实线性。
有限维迹配对给唯一 Hermitian $\rho$，
所有秩一效果上的非负性给 $\rho\ge0$，单位响应给迹一。
最后对两个秩一投影作迹配对即得模平方。

> **编者注（Markdown 实施者）：有限效果证明的中间步骤。** 先由 $p(0)=2p(0)$ 得 $p(0)=0$。若 $A/m,A/n$ 是效果，$A/(mn)$ 的至多 $n$ 或 $m$ 个部分和仍是效果，所以 $mp(A/m)=mnp(A/(mn))=np(A/n)$。对 $A,B$ 选共同大分母使 $(A+B)/m\le I$，即得正锥可加性；若 $A-B=A^\prime-B^\prime$，则 $A+B^\prime=A^\prime+B$ 保证差延拓无歧义。加法性给有理齐次性，序界给加性差 $|L(X)-L(Y)|\le\|X-Y\|$，故连续并实线性；有限维 Hermitian 空间的实迹配对非退化。所有单位秩一投影上的非负性等价于 $\langle v,\rho v\rangle\ge0$。$p(I)=1$ 同时要求非零维效果域；零维时这些假设不相容。此证明无需可数可加或无限维正态性。


∎

这是项目 V52、V58 与标准完整效果定理的共同内容 [3](#ref-v52)、[4](#ref-v58)、[9](#ref-busch)。
有限维只需所列有限可加性；没有援引无限维正态性。
如果只给几个读口，完整正性和分解相容必须另由实际关系覆盖认证；
V59 命题 5.3、定理 5.4 明确保留这一点 [5](#ref-v59)。

#### 命题 7.2（共同正交权重也唯一选择平方）

在实维数至少二的内积空间上，有限非负权重 $W$ 只依赖范数，
对正交向量可加，并使单位向量权重为一，则 $W(v)=\|v\|^2$。

**证明。**

取正交单位向量 $e_1,e_2$，令 $F(t)=W(\sqrt t\,e_1)$。
径向性和正交可加性给 $F(s+t)=F(s)+F(t)$。
非负性使 $F$ 单调；有理数上 $F(q)=q$，上下有理夹逼给全部 $t\ge0$。

∎

这条项目 V17、V52 已有的路线不另需连续性 [1](#ref-v17)、[3](#ref-v52)。
它明确使用内积正交及同一未归一权重；仅给逐表归一可允许其他幂。
平方权重同时满足

$$
\|u\oplus v\|^2=\|u\|^2+\|v\|^2,\qquad
\|u\otimes v\|^2=\|u\|^2\|v\|^2,
$$

而相干叠加保留 $2\Re\langle u,v\rangle$。

**白话图景。** 概率读数不能因为换一种分拆方法就改变。
同一效果的各种拆法都要给同一个数，这种整体相容把读出锁成迹配对。
纯来源与纯读口相配时，它就是振幅平方。
存在某个分支说明它可能发生，具体权重还由这套正响应确定。

## 8 核心量子定理：有限协议的精确二次关系表示

#### 定义 8.1（实二次关系网与声明协议）

实二次关系网由有限实变量和总次数至多二的实多项式等式组成。
允许辅助变量，原模型取解集的可见坐标投影。
固定有限维端口、有限准备/效果/操作标签和有限展开的分支历史。
相同操作标签在所有位置表示同一个过程。
预先固定要求报告条件态的历史集合 $H_{\rm cond}$；
该部分模型域要求各 $p_h>0$，其他历史统一保留未归一态。
允许有限代数校准条件；不在此假定任意连续函数族都有有限精确代数描述。

<a id="thm:protocol"></a>

#### 定理 8.2（有限量子协议二次表示）

在上述固定维数和接口中，合法量子准备、效果、通道、仪器、
未归一联合分支权重与正权分支条件态的集合，
恰为一个有限实二次关系网的可见投影。

**证明。**

每个复条目拆为实部、虚部；共轭实线性，复乘法实双线性。
以下分别给可靠性与完备性所需的构造。

**态与效果。**
用

$$
\rho=BB^\dagger,\quad\operatorname{Tr}\rho=1,\qquad
E=CC^\dagger,\quad I-E=DD^\dagger
$$

精确表示正态和效果；POVM 再加 $\sum_kE_k=I$。
正矩阵谱分解保证因子存在，反向因子式保证正性。
每个正因子可取与被分解矩阵同阶的方阵，故变量数事先有限。
若声明准备纯态，则取 $\rho=\psi\psi^\dagger$、$\psi^\dagger\psi=1$。
这些条目等式均至多二次。

**过程。**
采用本节特定的*未归一* Choi 约定

$$
J_\Lambda=\sum_{i,j}\Lambda(\ket i\bra j)\otimes\ket i\bra j,
\qquad
(J_\Lambda)_{\mu i,\nu j}
=[\Lambda(\ket i\bra j)]_{\mu\nu}.
$$

要求 $J_\Lambda=FF^\dagger$。
每个 $F$ 的列重排为 $(K_\alpha)_{\mu i}=F_{\mu i,\alpha}$，
比较矩阵块给
$\Lambda(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger$。
该式在任意参考扩展上保持正性，故给完全正性。
反向，若 $\Lambda$ 完全正，则
$J_\Lambda=(\Lambda\otimes\operatorname{id})(\ket\omega\bra\omega)\succeq0$，
其中 $\ket\omega=\sum_i\ket i\ket i$，再取其正因子即可。
通道再加线性条件

$$
\operatorname{Tr}_{\rm out}J_\Lambda=I_{\rm in};
$$

仪器则为各 $J_k=F_kF_k^\dagger$ 和
$\sum_k\operatorname{Tr}_{\rm out}J_k=I_{\rm in}$。
单独迹不增分支可再把
$I-\operatorname{Tr}_{\rm out}J$ 写成正因子。
注意该偏迹条目是 $(\sum K_\alpha^\dagger K_\alpha)_{ji}$，
等于单位矩阵与 Kraus 归一相同。

> **编者注（Markdown 实施者）：Choi 的标量域与方向。** 过程是固定端口间的复线性矩阵映射；$J_{\mu i,\nu j}$ 的因子列给 $K_{\alpha,\mu i}\overline{K_{\alpha,\nu j}}$。偏迹为 $\sum_{\mu,\alpha}K_{\alpha,\mu i}\overline{K_{\alpha,\mu j}}=(\sum_\alpha K_\alpha^\dagger K_\alpha)_{ji}$；转置保持正性，故 $I-\operatorname{Tr}_{\rm out}J\succeq0$ 恰对应迹不增。仪器每个结果可各取 $d_{\rm in}d_{\rm out}$ 列，再在有限结果指标上求和；不是把整台多结果仪器的总列数误限为这个数。


**同一对象的接口粘合。**
若同一仪器结果又以效果 $E_k$ 表示，必须加入

$$
\boxed{\operatorname{Tr}_{\rm out}J_k=E_k^{\mathsf T}.}
$$

若同一酉门同时出现为 $U$ 和 $J_U$，则加入

$$
U^\dagger U=I,\qquad
\boxed{J_U=\operatorname{vec}(U)\operatorname{vec}(U)^\dagger,}
$$

其中 $\operatorname{vec}(U)_{\mu i}=U_{\mu i}$，没有 $1/d$ 因子。
若另给标签 $C=B\circ A$，则要求

$$
(J_C)_{\mu i,\nu j}
=\sum_{r,s}(J_B)_{\mu r,\nu s}(J_A)_{ri,sj}.
$$

这些等式保留同一对象的多种坐标及所有输入上的组合一致性，均至多二次。

**同一历史接续。**
令 $\sigma_\varnothing=\rho$。每次实际使用标签 $k$ 时，
复用同一个 $J_k$，并要求

$$
\boxed{
(\sigma_{h\to k})_{\mu\nu}
=\sum_{i,j}(J_k)_{\mu i,\nu j}(\sigma_h)_{ij}.}
$$

该式对未知 $J_k,\sigma_h$ 为二次；
不再对 $\sigma_{ij}$ 额外共轭或转置。
其矩阵形式为
$\operatorname{Tr}_{\rm in}[J_k(I\otimes\sigma_h^{\mathsf T})]$。

> **编者注（Markdown 实施者）：接口与历史的收缩。** 按原文的输出优先指标，偏迹中的 $(\sigma^{\mathsf T})_{ji}=\sigma_{ij}$，因此递推式不再转置条目。效果接口的转置、酉向量化的无 $1/d$ 约定及组合式的 $ri,sj$ 收缩均由同一约定给出。同一标签仅在类型相同的输入输出端口复用；不同端口以已声明嵌入或另立类型标签处理。酉 $U$ 为方阵时 $U^\dagger U=I$ 才推出 $UU^\dagger=I$，矩形情形只给等距映射。

令 $p_h=\operatorname{Tr}\sigma_h$，终端效果读数为
$p_{h,E}=\operatorname{Tr}(E\sigma_h)$。
初始正性与完全正接续给 $\sigma_h\ge0$；
仪器完整性给 $\sum_kp_{hk}=p_h$。
有限反馈使用历史所指定的后续标签，仍共用相应过程变量。

**条件化与守卫。**
只对预先声明的 $h\in H_{\rm cond}$ 引入

$$
\sigma_h=p_h\rho_h,\qquad
\rho_h=B_hB_h^\dagger,\quad\operatorname{Tr}\rho_h=1,\quad p_hq_h=1.
$$

$p_h\ge0$ 已成立，最后一式恰排除 $p_h=0$。
零权分支只保留 $\sigma_h=0$，不人为指定条件态。
当 $H_{\rm cond}$ 为空时，全部零权模式均自然保留。
若预先声明纯分支及秩一投影读口，则先以

$$
\sigma_h=\psi_h\psi_h^\dagger,\qquad
E=\phi\phi^\dagger,\qquad \phi^\dagger\phi=1
$$

粘合振幅与已有矩阵，再用
$z=\langle\phi,\psi_h\rangle$、
$p_{h,E}=(\Re z)^2+(\Im z)^2$ 两个二次结点。
这里 $\|\psi_h\|^2=p_h$；若振幅代表已归一准备或条件态，另有单位范数条件。

> **编者注（Markdown 实施者）：零支与振幅粘合。** 正半定矩阵的迹为零即矩阵为零；未声明条件态的零支因此自然保留。$p_hq_h=1$ 和已推得的 $p_h\ge0$ 共同选出正支，不能单独由逆元方程排除负数。$z=\langle\phi,\psi_h\rangle$ 的实、虚部分别是一条实双线性等式，随后模平方为另一组二次等式；没有把未知振幅和其矩阵描述当作互不相关的对象。


**额外关系。**
有限多项式校准条件由定理 [3.3](#thm:compile) 编译。
$f\ge0$ 可用 $f=s^2$ 的存在辅助量表示；
$f>0$ 再加 $ft=1$。若 $f$ 高次，先编译其输出。
因此所有条件均可保持局部次数至多二。

每个合法协议用实际矩阵、正因子及分支态填入，给一个解。
每个解反向给正态、合法效果、共同 CP 过程及正确的全部分支组合，
故可见投影恰等于原协议模型。

∎

此处 $J$ 的迹保留约定与 v75 以归一 $\Phi_d$ 定义的 Choi 矩阵相差输入维数，
不能混用尺度。

> **编者注（Markdown 实施者）：前稿归一尺度。** 若前稿以单位向量 $|\Phi_d\rangle=d^{-1/2}\sum_i|i i\rangle$ 定义 $J^{\rm norm}=(\Lambda\otimes\operatorname{id})(|\Phi_d\rangle\langle\Phi_d|)$，则本节 $J=d\,J^{\rm norm}$，通道的归一偏迹相应为 $I/d$。这只使用 v75 不可变原稿的具名前提，不认证其他稿件或未读取的 Choi 原文。

正因子 $B,C,F$ 可以不唯一；它们是相同可见矩阵的辅助描述自由。
定理不把已给正性、CP 和共同接口当作从裸加乘自动产生的结论。
实际有记忆的过程应将记忆纳入端口，否则不能假定同一无记忆 $J_k$ 足够。

#### 推论 8.3（同一纯来源与内部酉历史）

固定上述端口和有限历史规模后，可以先固定一个共同有限载体及单位来源 $\Omega$。
每个合法协议实现均可在其上选择内部准备与整体酉序列，
使全部声明联合概率保持，并满足

$$
\Psi_0=\Omega,\qquad
\Psi_{j+1}=\mathcal U_j\Psi_j,\qquad
\mathcal U_j^\dagger\mathcal U_j=I.
$$

把这些量一同作为未知数，仍得到实二次关系。

**证明。**

每个过程最多需 $d_{\rm in}d_{\rm out}$ 个 Kraus 列，
不足者补零，因此可预先统一全部有限记录和辅助载体的尺寸。
由 $\rho=BB^\dagger$ 构造归一纯化
$\sum_{a,k}B_{ak}\ket a\ket k$。
任一固定单位参考向量可经一个整体酉到达它，方法是分别扩成正交基后逐基映射。
有限多个准备标签可在共同载体上采用相应内部准备门。
对每个仪器，Kraus 完整性使

$$
V\psi=\sum_{k,\alpha}K_{k,\alpha}\psi\otimes|k,\alpha\rangle
$$

等距，并可在足够大的内部 ready 载体上补成酉。
若与原协议矩阵联合求解，须把

$$
\mathcal U(\psi\otimes|\mathrm{ready}\rangle)
=\sum_{k,\alpha}K_{k,\alpha}\psi\otimes|k,\alpha\rangle
$$

在固定输入基上逐列加入关系网，且各 $K_{k,\alpha}$ 正是上述 $F_k$ 的列重排。
不同端口先作共同载体内的固定嵌入；该等式认证全部输入，而非只认证实际 $\Omega$。
记录基上的受控酉实现有限反馈；有限展开仅需有限记录容量。
最后读取记录事件的投影，得到原来的联合概率。
相应未归一分支与整体历史以
$\sigma_h=\operatorname{Tr}_{\rm aux}(P_h|\Psi_t\rangle\langle\Psi_t|P_h)$ 粘合，
其中 $P_h$ 是所声明内部记录事件的投影，保留所需输出端口。
以上矩阵与幅度关系均由本节结点表达。

> **编者注（Markdown 实施者）：共同载体、全输入与取边缘的时点。** 有限端口、结果和历史预先界定所需载体：各结果的 Kraus 列、准备纯化因子以及每次调用的新 ready 记录均可补零并嵌入一个足够大的固定有限空间。输入 ready 子空间与输出等距像维数相同，分别补成共同空间的正交基，即把等距列延拓为方形酉；该构造对全部输入并在任意参考张量上成立。反复使用同一过程可用同一局部酉在新 ready 因子上调用，过往记录和环境不抹去。反馈以保留的正交记录为控制；不同历史所需操作先补成共同载体上的酉。显示的 $P_h$ 边缘式应在历史 $h$ 刚完成、所需输出端口仍保留的时点 $t$ 使用；若移到更晚时点，须把以后传播一同计入，不能把已改变的端口误认作旧 $\sigma_h$。投影或边缘粘合若出现高次乘积，先引入中间结点再应用定理 3.3，不宣称未拆开的高次式本身就是二次。


∎

来源、记录、辅助因子与环境皆可内生；该结论给表示存在性，
不认证具体原生控制或整个宇宙有限维，也不从有限统计唯一确定不可见环境。
项目 V58 的 ready 条件与 $\Omega$ 的有限协议对应仍保留明确接口 [4](#ref-v58)、[6](#ref-omega)。

#### 命题 8.4（二次归一关系不自动成为单输入量子门）

在 $\dim\mathcal{H}\ge2$ 时，关系
$\|\psi\|=1$、$\chi_{ij}=\psi_i\psi_j$、$\|\chi\|=1$
可以写成实二次网，却不能由一个确定性通道对每个未知 $\psi$ 实现。

**证明。**

若存在，等距记录实现必须为
$V\psi=\psi\otimes\psi\otimes e_\psi$，
因为两份输出联合态为纯态。
对两态重叠 $c=\langle\psi,\phi\rangle$，保持内积给
$c=c^2\langle e_\psi,e_\phi\rangle$。
取 $0<|c|<1$，得 $|c|\le|c|^2$，矛盾。

> **编者注（Markdown 实施者）：纯输出与相位。** 把确定性通道作有限维等距记录实现后，纯约化输出强制全态为该纯向量与单位环境向量的张量积；代表相位可吸收到 $e_\psi$。采用第一变量共轭线性内积，保存的是 $c=c^2\langle e_\psi,e_\phi\rangle$，再用环境重叠模至多一。它是对所有未知射线要求同一通道时的障碍，不否定描述赋值或供应多份已制备输入。


∎

**白话图景。** 准备、门、读出、分支和归一可以放在同一张二次关系网中共同确定。
每处出现同一台门，就必须用同一个过程变量。
记录和环境可以一起留在 $\Omega$ 内部，整体历史继续保持酉性。
关系图能怎样写，与未知输入实际能被怎样操作，也由网中的过程约束分清。

## 9 约束自身继续展开：闭路、归一和误差

#### 命题 9.1（闭路约束可以精确接入保守展开）

若无环脚本定义 $z=p(x)$，再加任意多项式关系 $h_j(x,z)=0$
（非交换情形取自由多项式），
则整体关系商等价于原输入上的 $h_j(x,p(x))=0$。

**证明。**

在 $B/J\cong A$ 下，$[h_j]$ 恰映为 $h_j(x,p(x))$，
再取生成理想的商即可。

∎

因此计算一条关系的表达图可以无环，而许多未知量共同满足的约束图可以有环。
若 $z=F(x,z)$，应先把 $z$ 当原未知量，
编译右侧，再把输出等于 $z$ 作为闭路条件。
$z=z^2$ 有两个实解，$z=z+1$ 无解，$z=xz$ 在 $x=1$ 时有任意解。
二次语法本身不保证唯一；闭路的共同固定空间可像 v75 那样选定来源或保留自由。

> **编者注（Markdown 实施者）：闭路类比的前提。** 这里的闭路先把待定 $z$ 当输入再加回等式；无环门变量的唯一延拓不等于闭路方程唯一有解。v75 的共同固定空间结论以其酉运输、路径及闭路相容条件为前提，不把一般非线性固定点方程认作同一种线性 holonomy 定理。


#### 命题 9.2（归一化也能由内部二次关系表达）

对非零实向量 $x$，引入正尺度 $r$、单位方向 $n$，
以

$$
x_i=rn_i,\qquad \sum_i n_i^2=1,\qquad r>0
$$

表达归一化。则 $r=\|x\|$、$n=x/\|x\|$ 唯一。
$r>0$ 等价于存在实 $s,t$ 使 $r=s^2$、$rt=1$。

**证明。**

对 $x_i=rn_i$ 平方求和得 $\|x\|^2=r^2$；
正支决定 $r$，随后决定 $n$。反向代入成立。

∎

只保留 $n$ 会消去尺度；保留 $(r,n)$ 则不丢失非零 $x$。
辅助量 $s$ 有正负两支；上述唯一性指可见的 $r,n$。
零向量须单列，不存在唯一方向。
正性、尺度和分支条件都可以是整体约束，不能因叫作归一就删掉它们。

#### 命题 9.3（局部残差的递推控制）

在赋范代数中，设真值及近似操作数范数均不超过 $M$，
局部门残差为 $e_i$，各结点误差为 $d_i$。则

$$
d_i\le\|e_i\|+d_u+d_v\quad\text{（加法）},
\qquad
d_i\le\|e_i\|+Md_u+Md_v\quad\text{（乘法）}.
$$

**证明。**

加法用三角不等式。乘法用
$\widetilde u\widetilde v-uv  =(\widetilde u-u)\widetilde v+u(\widetilde v-v)$。

∎

在原输入与常数精确共享时，沿有限 DAG 代入给各局部残差的路径增益和；
若输入也有扰动，还须加入各输入误差沿路径传播的项。
这证明怎样预算误差，不保证任意长乘法链天然稳定。
观察者希望持续缩小误差，还须合适的反馈或收缩关系。

> **编者注（Markdown 实施者）：残差范数约定。** 赋范代数采用次乘性 $\|uv\|\le\|u\|\|v\|$；$d_u=\|\widetilde u-u\|$、$e_i=\widetilde z_i-\widetilde u\widetilde v$（加法同理）。原文同时界定真值及近似操作数，才可分别以 $M$ 控制两项。有限 DAG 的路径和按边出现计重，合并共享节点只避免重复定义，不自动消去误差的多条传播路径。


**白话图景。** 每条约束都能继续拆成同类小关系；不同路径再次相遇时，闭路筛选能同时成立的值。
归一化也在其中，但方向和尺度各有位置。
误差沿这些连接传播，稳定性取决于连接怎样放大或抑制余量。

## 10 无限递归与精确表达的范围

### 有限域与极限不能混为一个结论

有理式 $y=P(x)/Q(x)$ 可以写作
$Q(x)t=1$、$y=P(x)t$，因此在非零分母域内有唯一辅助解。
实平方根关系 $z^2=x$ 还须选择正支。
非交换逆元一般应同时保留左右逆条件。

> **编者注（Markdown 实施者）：平方根与逆的端点。** 实平方根的主支是 $z\ge0$（$x\ge0$），当 $x=0$ 时只有 $z=0$；若严格写成“正支”则只能覆盖 $x>0$。有理式的非零分母保证可逆及唯一解限于这里的实或复标量域；一般非交换代数中非零并不保证可逆，须显式要求左右逆。


有限实多项式方程、不等式及有限实量词仍描述半代数集合；
这是实代数消元的标准范围 [10](#ref-realalg)。
这里不把该定理混用于整数算术或任意无限逻辑。
特别地，存在辅助变量不会自动把所有连续关系都变成有限代数关系。

#### 命题 10.1（全正域的对数不是代数函数）

不存在非零多项式 $P(X,Y)$ 使 $P(x,\log x)=0$ 对全部 $x>0$ 成立。

**证明。**

写 $P(X,Y)=\sum_{j=0}^dX^jq_j(Y)$，其中 $q_d\ne0$。
令 $x=e^t$，除以 $e^{dt}$，得到
$q_d(t)+\sum_{j<d}e^{-(d-j)t}q_j(t)=0$。
令 $t\to+\infty$，每个后项趋零，迫使非零多项式 $q_d(t)\to0$，矛盾。

∎

这个自足反证排除对数满足非零全域代数方程。

> **编者注（Markdown 实施者）：对数反证的范围。** 多项式系数取实或复数；$d$ 是最高非零 $X$ 次数。$d=0$ 时余项为空，同样强制 $q_0(t)=0$ 对全部实 $t$ 成立，矛盾。非零实或复多项式不可能在 $t\to+\infty$ 时趋零。本反证本身不额外证明任何关于任意无限量词、整数算术或非代数语言的消元结论。

若用 $e^y=x$ 定义它，指数关系已经进入语言；
若取级数或积分，则收敛、域和分支也属于关系内容。

<a id="thm:bernstein"></a>

#### 定理 10.2（连续读出的二次网一致逼近）

若 $f:[0,1]\to\mathbb{R}$ 或 $\mathbb{C}$ 连续，令 $M=\sup|f|$，对整数 $n\ge1$ 取

$$
B_nf(x)=\sum_{k=0}^n f(k/n)\binom nkx^k(1-x)^{n-k}.
$$

每个 $B_nf$ 可编译为有限二次网，且对任意 $\delta>0$，

$$
\boxed{
\sup_x|B_nf(x)-f(x)|
\le\omega_f(\delta)+\frac{M}{2n\delta^2},}
$$

其中 $\omega_f$ 是连续模。因此 $B_nf\to f$ 一致收敛。

> **编者注（Markdown 实施者）：连续模与逼近端点。** 取 $\omega_f(\delta)=\sup\{|f(u)-f(v)|:u,v\in[0,1],|u-v|\le\delta\}$；复值时使用复模。二项权重在 $x=0,1$ 也按多项式恒等式成立（零次幂为空积），尾界对任意 $\delta>0$、$n\ge1$ 成立。$M=0$ 时 $f=0$，界仍成立。乘积权重给紧立方体版本时，须选定多维距离与相应连续模，并相应使用各坐标方差之和的尾界，不能照抄一维常数。


**证明。**

记非负二项权重为 $w_k$。
由二项式恒等式及其一、二阶形式，
$\sum w_k=1$，
$\sum w_k(k/n-x)^2=x(1-x)/n\le1/(4n)$。
在 $|k/n-x|\le\delta$ 的部分，误差至多 $\omega_f(\delta)$；
补集总权重至多 $1/(4n\delta^2)$，每项差至多 $2M$。
相加得界。一致连续性允许先取小 $\delta$、再取大 $n$。
有限多项式由定理 [3.3](#thm:compile) 编译。

∎

系数 $f(k/n)$ 仍需由已知函数或内部数据供应；定理不产生未知函数值。
更高维紧立方体可用乘积权重作同样证明。
无限量子整体还需相容有限端口、正性与所用完备化条件，
不是一张固定有限网已经装下任意无限信息。

**白话图景。** 有限脚本负责一层精度，递归延长可以继续逼近。
“可以无限继续”能成为一个有误差界的结论；
每一层所用的关系值、误差和适用范围仍保留在整体描述中。

## 11 更简洁的结构起点：一个正关系呈示

#### 定义 11.1（同源正关系体）

取带伴随的关系符号 $S$、由具体约束生成的 $*$ 理想 $\mathcal I$，
及其商代数上的共同正归一 Hermitian 响应 $\ell$：

$$
\boxed{
\mathfrak R=(\mathcal{A},\ell),\qquad
\mathcal{A}=\mathbb{R}\langle S,S^*\rangle/\mathcal I.}
$$

来源为正关系商中的 $\Omega=[1]$；
状态、历史、读口和比较程序以同一代数及其声明的内部复合接口表示。
实际有限菜单及其覆盖另列为可认证的关系条件。

这把“基础操作”和“结构约束”分开组织：
线性词展开与双线性复合给统一语言；
哪些词相等、哪些组合正、哪些读数相容，决定具体关系体。
新关系若只是旧表达式的定义性展开，定理 [4.2](#thm:positive) 保证
不需新的独立状态假设。

量子选择条件可以明确写在该结构内部。例如项目 V58 的实三轴关系

$$
X^*=X,\ Y^*=Y,\ Z^*=Z,\quad X^2=Y^2=Z^2=1,\quad
XY=-YX,\ YZ=-ZY,\ ZX=-XZ
$$

给 $J=XYZ$、$J^2=-1$ 和局部 $M_2(\mathbb{C})$ 实代数。

> **编者注（Markdown 实施者）：所呈示代数与表示重数。** 局部结论指由所列三个生成元及其完整关系生成的非零含幺实代数：通用 Clifford 呈示先张成 $1,X,Y,Z,XY,YZ,ZX,XYZ$，Pauli 实表示给八个独立实矩阵，故为 $M_2(\mathbb C)$。其简单性使非零含幺商不再缩小。实际表示可有重数，且其他未声明生成元可形成更大代数；不把任意含有这三元组的整个装置代数都认作单个二阶块。共同中心的有限复合按固定的对易原子接口取商。

不同原子对易，再施加共同中心 $J_a=J_b$，给共同复矩阵复合。
这些均可保守二次化；有限复合下每个字母的乘法次序保留。
取得中心复结构后，正确响应为

$$
\ell_{\mathbb{C}}(a)=\ell_{\mathbb{R}}(a)-i\ell_{\mathbb{R}}(Ja),
$$

而非把实值函数原样改称复线性 [4](#ref-v58)。
完整效果分解相容给定理 [7.1](#thm:born)；
有限矩阵块上保持完整乘法、伴随和复结构的可逆自同构有酉实现；
同一目标线性规则在已校准完整参考上有正的关联输出，
并满足仪器归一，再结合内部 ready 接口，得到 CP 仪器及其酉记录实现。
这里须认证该参考输出确由同一 $\Lambda\otimes\operatorname{id}$ 产生。
本稿采用上述条件结论，不声称已推导全部动力学及实际控制。

> **编者注（Markdown 实施者）：复响应、自同构与关联参考。** $J$ 为中心且 $J^*=-J$，Hermitian 实响应使 $\ell_{\mathbb R}(Ja^*a)=0$，从而所写 $\ell_{\mathbb C}$ 为正且复线性。自同构结论要求整个有限复矩阵块上保持单位、乘法、伴随和选定复标量；只保实结构会容许共轭型作用，不能直接称复线性内酉。参考正性判 CP 还要求参考态为完整纠缠校准输入且输出来自同一线性 $\Lambda\otimes\operatorname{id}$；任意未知装置给出的某个正关联态不够。


#### 命题 11.2（约束可以打包，但内容不会因此消失）

对有限个实标量残差 $r_j$，

$$
\forall j,\ r_j=0
\quad\Longleftrightarrow\quad
\sum_jr_j^2=0.
$$

对有界算子残差，
$\sum_jr_j^\dagger r_j=0$ 等价于全部 $r_j=0$；
仅有其在一个 $\Omega$ 上的期望为零，只推出全部 $r_j\Omega=0$。

**证明。**

标量式各项非负。算子式对任意向量取二次型，得到
$\sum_j\|r_jv\|^2=0$；只代入 $\Omega$ 时结论相应受限。

∎

无界情形须在共同稠密定义域上以该二次型恒等式表述，
不能省略乘积与伴随的定义域条件。

所以一条还是多条“公理”的数目容易随写法改变。
可以直接研究这个整体是否有解、是否唯一到共同表示、是否稳定，
而不把绝对最少条数作为本轮目标。

同一加乘语言也容纳经典交换模型。
例如 $\mathbb{R}\oplus\mathbb{R}$ 上
$\ell_p(a,b)=pa+(1-p)b$（$0\le p\le1$）全部正且归一。
这些是对结构选择的比较，不要求实际本体可以更换。
它们说明量子内容由上述非交换、复定向、正性和复合约束承担。
所有参考和数据可以内生，但实际约束值仍须由内部关系确定。

存在量词也能参与这个表达：
$\rho\succeq0\iff\exists B:\rho=BB^\dagger$。
它回答合法实现是否存在；对于
$\rho_p=\operatorname{diag}(p,1-p)$，所有 $0<p<1$ 都使两事件可能，
却给不同权重。因此存在性本身不选择实际概率数值。

| 用户直觉的严格版本 | 本轮证明的内容 |
| --- | --- |
| 任意关系可以线性表达 | 自由空间与张量上的精确线性表示；系数保留全部原信息。 |
| 高次关系只需加乘 | 有限脚本恰生成多项式；任意有限代数呈示可二次化。 |
| 关系本身还能继续拆解 | 保守商同构、正响应对应与同一 $\Omega$ 保持。 |
| 提升后剩下的是约束 | 二次方程线性提升，配共同秩一与正性像条件。 |
| 平方是最低关系层 | 在双线性非负闭合或共同相位多项式类中有明确二次定理。 |
| 所有量子对象都在整体内 | 固定有限协议有共同二次表示及内部纯来源酉实现。 |
| 公理可写成内部关系 | 可把具体结构条件组织为同一个正关系呈示；须保留其实际内容。 |

因此本轮的凝练表述是

$$
\boxed{\text{线性承载}+\text{双线性复合}
+\text{同源正性与整体相容约束}.}
$$

这是一个可证明、可逐步认证的量子关系重建方案，
尚未从无前件确定实际宇宙的全部约束或其唯一物理实现。

**白话图景。** 在这套条件图景里，同一个 $\Omega$ 经过历史，产生所有内部读出。
复杂关系可以展开成加法与乘法的小结点；每个中间名字都要能接回它所代表的那段历史。
把关系搬到更大的坐标空间后，读出可以变得线性，
但这些坐标必须同时来自同一个来源，不能各自随意取值。
正性、归一、共同复定向、门的接续和记录的一致性，就在整张网里约束它们。
观察者的预测、校准和推理也使用这同一种关系语言。
研究量子起源于是可以集中为：证明这张整体关系网怎样允许叠加、怎样保持相干，
怎样产生平方读出，以及哪些条件把它锁定成量子结构。

## 固定来源与参考文献

<a id="ref-v17"></a>

**[1]** 项目固定提交。
[V17：加乘、对数与量子勾股几何](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)，
定义 1.1、§2、§8，以及 §13 的所用一般结论。

<a id="ref-v49"></a>

**[2]** 项目固定提交。
[V49：加乘指数、二次关系闭合与归一化升维](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md)，§§2--8。

<a id="ref-v52"></a>

**[3]** 项目固定提交。
[V52：纯态商几何、二次关系生成与无损递归](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)，§§1--2、5--7 的所用结论。

<a id="ref-v58"></a>

**[4]** 项目固定提交。
[V58：关系公理、共同复相位与条件量子重建](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md)，§§2--8、10--14。

<a id="ref-v59"></a>

**[5]** 项目固定提交。
[V59：局部层析、相干读出轨道与正性起源](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md)，
§1.2、§§2--6 的相关条件及 §10；包括命题 5.3、定理 5.4。

<a id="ref-omega"></a>

**[6]** 项目固定提交。
[$\Omega$ 静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，
§§1--8、12 的有限关系与协议接口；不认证全部后续供应链。

<a id="ref-tensor"></a>

**[7]** Keith Conrad.
[*Tensor Products*](https://kconrad.math.uconn.edu/blurbs/linmultialg/tensorprod.pdf)，
本轮核对 §§2--3 的双线性、外积像及通用性质相关段落。

<a id="ref-arithmetic"></a>

**[8]** J. Bootle, A. Cerulli, P. Chaidos, J. Groth, C. Petit.
*Efficient Zero-Knowledge Arguments for Arithmetic Circuits in the Discrete Log Setting*.
EUROCRYPT 2016.
[作者完整版](https://discovery.ucl.ac.uk/id/eprint/10090338/1/263.pdf)，
本轮仅消费 §5 乘法/线性约束表示及附录 A 的相应电路转换段落，
不消费安全性或复杂度证明。

<a id="ref-busch"></a>

**[9]** P. Busch.
*Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem*.
Phys. Rev. Lett. 91, 120403 (2003).
[arXiv:quant-ph/9909073v3](https://arxiv.org/pdf/quant-ph/9909073)，
本轮核对完整效果条件、主定理证明及二维说明；本文使用有限维版本。

<a id="ref-realalg"></a>

**[10]** S. Basu.
*Algorithms in Real Algebraic Geometry: A Survey*.
[作者公开稿](https://www.math.purdue.edu/~sbasu/raag_survey2011_final.pdf)，
本轮核对 §2.1 定理 2.1 的实量词消元陈述及前件，
不声称重证一般消元算法。

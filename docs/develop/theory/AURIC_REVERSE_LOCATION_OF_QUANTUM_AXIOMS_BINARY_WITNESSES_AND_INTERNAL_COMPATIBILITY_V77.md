<a id="auric-v77"></a>

# 反向定位量子公理

**二元见证、三维比较与内部整体相容**

**定义、定理与纸面证明 · v77.0 · 2026 年 11 月 1 日 · Asia/Singapore**

> **来源与转换说明（编者）。** 本文忠实转换用户在会话 `01a15590-6264-7c80-8c48-21290deed496` 于 2026-11-01 提供的 AI AURIC 续稿。原作者的历史访问、固定提交、阅读与方法报告保留为作者署名的文献陈述；本次进行纸面、固定原始来源、本地字节、文本与渲染核对，不把它们升级为最新 HEAD、全库、Lean、物理或经验认证。原稿所有断言、公式、证明、生产设置、表格、参考文献、图形几何和结尾均在下方保留；Markdown、KaTeX、原生表格和内联 SVG 是可见排版等价物。

<details>
<summary>原稿完整前置设置（逐行保留）</summary>

<pre style="white-space:pre-wrap;overflow-wrap:anywhere;max-width:100%;"><code>% !TeX program = xelatex
% Compile twice. Optional: \def\AURICFontPath{/absolute/path/to/fonts/}
% Mathematics in this manuscript is proved on paper; no mathematical programs were used.
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
\usepackage{amsmath,amssymb,amsthm,mathtools,bm}
\usepackage{booktabs,array,tabularx,enumitem,fancyhdr,xcolor,needspace,tikz}
\usetikzlibrary{arrows.meta,positioning}
\definecolor{auricblue}{RGB}{24,53,79}
\definecolor{auricred}{RGB}{155,48,48}
\usepackage[unicode,colorlinks=true,linkcolor=auricblue,urlcolor=auricblue,citecolor=auricblue]{hyperref}
\hypersetup{pdftitle={AURIC v77：反向定位量子公理},
pdfauthor={AURIC research continuation},
pdfsubject={Binary witnesses, Bloch comparisons, internal reference positivity and relational closure}}
\newcommand{\R}{\mathbb R}
\newcommand{\C}{\mathbb C}
\newcommand{\HH}{\mathcal H}
\newcommand{\Alg}{\mathcal A}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\Ran}{\operatorname{Ran}}
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
\fancyhead[L]{\small AURIC：反向定位量子公理}
\fancyhead[R]{\small v77 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
</code></pre>

</details>

<!-- AURIC-V77-IMMUTABLE-SOURCE-BEGIN
```latex
% !TeX program = xelatex
% Compile twice. Optional: \def\AURICFontPath{/absolute/path/to/fonts/}
% Mathematics in this manuscript is proved on paper; no mathematical programs were used.
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
\hypersetup{pdftitle={AURIC v77：反向定位量子公理},
pdfauthor={AURIC research continuation},
pdfsubject={Binary witnesses, Bloch comparisons, internal reference positivity and relational closure}}
\newcommand{\R}{\mathbb R}
\newcommand{\C}{\mathbb C}
\newcommand{\HH}{\mathcal H}
\newcommand{\Alg}{\mathcal A}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\Ran}{\operatorname{Ran}}
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
\fancyhead[L]{\small AURIC：反向定位量子公理}
\fancyhead[R]{\small v77 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
\begin{center}
{\LARGE\bfseries\color{auricblue} 反向定位量子公理}\\[8pt]
{\large 二元见证、三维比较与内部整体相容}\\[7pt]
定义、定理与纸面证明\quad v77.0\\[4pt]
2026 年 11 月 1 日\quad Asia/Singapore
\end{center}
\begin{abstract}
本稿把“撤去公理、寻找后果、定位两个元、作三维提升”组织为有明确前件的反向研究方法。
对同一来源的两条历史，构造二元比较标签态，证明关系余量精确等于
$s(1-x)$；对仅有 Hermitian 与单位归一的候选响应，证明全部合成二元正迹块的球内条件等价于整体正性。
全局负性可以有有限二元见证，但只检查原始两两关系不足；Schur 支持与递归余量保存整体约束。
证明收缩分支恰可补成内部等距记录，完整参考正性等价完全正性，且在已给 qubit 球与复合接口中排除反射、选择酉旋转。
效果细分相容、复定向闭路及固定五模式编码分别给另一类内部约束与精确反例。
最后以满锚覆盖将有限三维读出连接到整体算符误差界。
球外候选表、球内关系残差、漏失的分支与离散取向障碍分别处理；不把一切失效都叫作同一种物理态，也不声称从无前件选择实际宇宙。
\end{abstract}

\section{反向研究的逻辑与固定项目依据}
用户提出的方法可以具体化为：固定已经取得的关系，撤去一项待解释条件，
找出新增候选在哪里不再满足所要求的整体相容，再决定是补回条件、补入内部角色，还是承认另一种模型仍未被排除。
本轮不以绝对最少公理条数为目标。

\begin{definition}[相对于背景的反向见证]
固定背景条件 $\mathcal B$、待解释条件 $A$ 与明确的整体合同 $C$。
一个完整的反向定位要求证明
\[
\mathcal B\land\neg A\ \Longrightarrow\ \exists w\;D(w),
\qquad C\ \Longrightarrow\ \forall w\;\neg D(w).
\]
若还证明 $\mathcal B\land A\Rightarrow C$，便在该背景中得到 $A$ 与 $C$ 的等价。
仅找到一个 $\neg A$ 的坏模型，只证明失效可能发生，不证明所有撤去 $A$ 的模型都会失效。
\end{definition}

后果也有不同类型：某个局部分支可以在更大仪器中合法；某张完整负关系表却不能靠增加正 Hilbert 维数修复。
“在同一个 $\Omega$ 内”允许共同描述全部角色，并不自动保证任意局部表有共同实现。
本文的有限三维见证适用于所声明的二次形式与算符关系；连续性或任意逻辑命题的失败仍需自己的证据。

本轮唯一实时 HEAD GET 于新加坡时间 2026-11-01 21:42:05，
在取得 HTTP 响应前因网络权限失败；没有重试、重定向、备用活动端点或提权。
以下采用七份原始 Markdown 重新核对 Git blob 的固定提交
\par\noindent\texttt{5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b}。\par
v77 是本对话稿件编号，不是已取得的仓库最新版本。

\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.20\textwidth}X@{}}
\toprule
项目来源 & 本轮消费的关系及边界\\
\midrule
V17 §§3--4、9；命题 13.3 & 一般五概率的关系纤维、相位与三态 Gram。\\
V37 §§1--6、12 & 二元球、指定五模式码、算子值递归、完整 Gram 与五标签随机更新。\\
V49 §§3--5；V52 §§2--7 & 平方的附加闭合、完整效果、相位不变量与 Schur 余量。\\
V58 §§2--8、10--14 & 内部复单位、正响应、同源表示、酉与 CP 的条件。\\
V59 §§1.2--5、10 的相关段 & 完整关系、实际覆盖、有限菜单与参考层级。\\
$\Omega$ §§1--8、12 & 静态相容、完整支撑粘合、内部参考与有限协议。\\
\bottomrule
\end{tabularx}
\end{center}
不据此认证全部仓库、后续原生供应链或源文所报告的程序证明。
本稿所有数学采用纸面推导与独立纸面复核，没有数学程序、CAS、数值求值、枚举、仿真或机器证明。
前稿 v76 的保守加乘展开继续作为表达背景；辅助名字不增加独立来源 \cite{v76}。

\plain{反过来问公理为什么需要，就要看它保护哪一种“一起成立”。
有时缺的是一个被漏掉的内部角色；有时已有关系本身互相冲突。
把这两种情况分开，才能知道扩大结构究竟补回了什么。}

\section{同源关系等式的二元三维比较核}
以下内积对第二槽线性。固定同一来源 $\Omega$，历史 $w$ 给输入
$\psi_w=\pi(w)\Omega$。关系等式的两端 $L,R$ 在该输入上给
\[
a=L\psi_w,\qquad b=R\psi_w,\qquad s=\|a\|^2+\|b\|^2.
\]
这里 $L,R$ 可以代表两条不同表达或历史；把它们当实际装置时须保留共同输入与相干比较接口。

\begin{theorem}[法则余量的精确三轴读出]\label{thm:comparison}
当 $s>0$ 时，定义内部标签比较向量
\[
\ket\Phi=\frac{\ket0\otimes a+\ket1\otimes b}{\sqrt s}.
\]
其标签约化态及三轴为
\[
\rho=\frac1s\begin{pmatrix}\|a\|^2&\langle b,a\rangle\\
\langle a,b\rangle&\|b\|^2\end{pmatrix}
=\frac12(I+x\sigma_x+y\sigma_y+z\sigma_z),
\]
\[
x=\frac{2\Re\langle a,b\rangle}{s},\quad
y=\frac{2\Im\langle a,b\rangle}{s},\quad
z=\frac{\|a\|^2-\|b\|^2}{s}.
\]
于是
\[
\boxed{\|(L-R)\psi_w\|^2=s(1-x),\qquad
p_-:=\langle-|\rho|-\rangle=\frac{1-x}{2}.}
\]
特别地，$L\psi_w=R\psi_w$ 当且仅当 $(x,y,z)=(1,0,0)$。
若 $s=0$，两端均为零，关系成立，但没有归一标签态。
\end{theorem}
\begin{proof}
对原载体取偏迹得到矩阵。展开差的范数给
$\|a-b\|^2=s-2\Re\langle a,b\rangle$。
投影到 $\ket-=(\ket0-\ket1)/\sqrt2$ 后，原载体向量为
$(a-b)/\sqrt{2s}$，故得概率式。
两端相等且非零时标签为 $\ket+$；反向 $x=1$ 使差的范数为零。
\end{proof}

标签矩阵是通常 Gram 矩阵
$\left(\begin{smallmatrix}\|a\|^2&\langle a,b\rangle\\\langle b,a\rangle&\|b\|^2\end{smallmatrix}\right)$
的转置除以 $s$，所以 $y$ 的符号不能与直接归一通常 Gram 的公式混用。

\begin{proposition}[保存范围与相位范围]
保留 $s$ 和三个标签坐标，恰保留有序向量对的完整 Gram。
它确定该向量对到其张成空间之间的共同等距，未确定相对于整个环境的嵌入。
对于非零两端，若只比较相位商，则
\[
\min_\theta\|a-e^{i\theta}b\|^2
=s-2|\langle a,b\rangle|
=s\bigl(1-\sqrt{x^2+y^2}\bigr).
\]
\end{proposition}
\begin{proof}
从 $s,x,y,z$ 直接恢复两对角与复交叉项。
若两对向量 Gram 相同，映射 $\alpha a+\beta b\mapsto\alpha a'+\beta b'$
保持所有范数，因此良定义且等距。相位式由选择交叉项的最大实部得到。
\end{proof}

若输入归一且 $L,R$ 为酉，具有受控相干接口时，
对 $\ket+\otimes\psi_w$ 施加
$\ket0\bra0\otimes L+\ket1\bra1\otimes R$ 即实现比较，此时 $s=2$。
对归一输入，一般有界 $L,R$ 可选共同 $c_0>0$，使
$c_0^2(L^\dagger L+R^\dagger R)\preceq I$；
相干成功分支为 $c_0(\ket0L\psi+\ket1R\psi)$，
成功概率 $c_0^2s$，并须保留失败分支。
单独拥有两个未受控通道不自动供应其共同相位或受控比较。

\plain{同一个输入沿两条关系走，比较最后是否真得到同一向量。
关系完全相同，对应球上的一个指定点；关系有余量，就偏离这个点。
尺度 $s$ 把球中偏移换成真实误差。
比较使用同一个来源，不需要复制一个未知输入态。}

\section{撤去正性：哪些三维候选会失败}
\begin{proposition}[正迹二元形式与三球]\label{prop:ball}
设 $H=\left(\begin{smallmatrix}a&\bar c\\c&b\end{smallmatrix}\right)$ Hermitian，
$t=a+b>0$。令
\[
\mathbf r=\frac1t(2\Re c,2\Im c,a-b).
\]
则
\[
H=\frac t2(I+\mathbf r\cdot\boldsymbol\sigma),\qquad
\lambda_\pm(H)=\frac t2(1\pm|\mathbf r|),
\]
因而 $H\succeq0$ 当且仅当 $|\mathbf r|\le1$。
$t<0$ 时已有负方向；$t=0$ 时仅 $H=0$ 可正。
\end{proposition}
\begin{proof}
比较矩阵条目，并解二阶特征方程；判别式为
$(a-b)^2+4|c|^2=t^2|\mathbf r|^2$。
零迹正矩阵的所有非负本征值之和为零，故为零。
\end{proof}

不能除以负迹掩盖负性，例如 $-I/\Tr(-I)=I/2$。
在 $t>0$ 分支，恢复完整形式须保留 $t$ 与三个坐标；$t\le0$ 按上述边界另处理。
归一点本身没有保存尺度。
球外是被反证的候选形式，不是可以实际制备的量子态。

\begin{theorem}[整体正性等价于全部合成二元球条件]\label{thm:binarypositive}
设含幺复 $*$ 代数上 $\ell$ Hermitian、线性，$\ell(1)=1$，不预设正性。
对任意代数元 $a,b$ 定义
\[
H_{a,b}=\begin{pmatrix}
\ell(a^*a)&\ell(b^*a)\\
\ell(a^*b)&\ell(b^*b)
\end{pmatrix}.
\]
以下条件等价：
\begin{enumerate}
\item $\ell(p^*p)\ge0$ 对所有 $p$ 成立；
\item 所有正迹 $H_{a,b}$ 归一后的 Bloch 向量均在单位球内；
\item 第二项只对 $a=1$、$b$ 为任意可缩放代数元成立。
\end{enumerate}
\end{theorem}
\begin{proof}
正性使每个二元 Gram 正，转置仍正，故第一项推出第二项；第二项推出第三项显然。
若第一项失败，取 $\ell(p^*p)=-d<0$，令 $b=p/\sqrt{2d}$。
$H_{1,b}$ 的对角为 $(1,-1/2)$、迹为 $1/2$；
归一后对角为 $(2,-1)$，故 $z=3$，与第三项矛盾。
\end{proof}

这里 $p$ 必须包括历史词的有限线性组合。
例如在 $\C[\mathbb Z_3]$ 中设
\[
g^3=1,\quad g^*=g^2,\quad
\ell(1)=1,\quad\ell(g)=\ell(g^2)=-3/4.
\]
任意两个群词的关系块对角为一、交叉为一或 $-3/4$，均正。
但 $p=1+g+g^2$ 满足 $p^*p=3p$，从而
\[
\boxed{\ell(p^*p)=3(1-3/4-3/4)=-3/2<0.}
\]
所以全部原始两两检查仍不足；线性合成与整体相容在此承担实质内容。
定理 \ref{thm:binarypositive} 是正性的一种等价关系表达，不是从更弱内容免费得到正性。

\begin{theorem}[有限负性具有真正的二维压缩见证]\label{thm:compression}
若有限维 Hermitian $W$ 满足 $\Tr W>0$ 而 $W\not\succeq0$，
则存在二维等距 $V$，使 $C=V^\dagger WV$ 的迹为正且有负本征值。
于是 $C/\Tr C$ 的三轴在球外。
\end{theorem}
\begin{proof}
取负本征值 $-b<0$ 的单位向量 $n$。
若有正本征值 $a>b$，其单位向量与 $n$ 组成所需压缩。
否则取最大正本征值 $a\le b$ 及向量 $p$；
正总迹迫使另有正本征值 $c>0$ 及与 $p,n$ 正交的向量 $q$。
取 $0<\epsilon<\min(c,b)$、$\tau=(a+\epsilon)/(a+b)$，令
\[
u=q,\qquad v=\sqrt\tau\,n+\sqrt{1-\tau}\,p.
\]
两者正交归一，压缩为 $\operatorname{diag}(c,-\epsilon)$，迹为正。
再用命题 \ref{prop:ball}。
\end{proof}

二维方向可以含许多原始历史，不能据此消去构造它们所需的相干资源或参考维数。
固定完整负 Gram 表无法在任何更大正 Hilbert 空间实现：
实际向量列的 Gram 必为 $T^\dagger T\succeq0$。
增加维数可容纳合法表的新秩，不能改变同一表的负方向 \cite{v37}。

\plain{关系可以在原来的每一对上看起来正常，却在几段历史合成以后冲突。
把这个冲突集中到两个合成方向，便能用一个三维球外候选看见它。
这个球外点说明原来的解释不能成立；它不是一种新的量子态。}

\section{更大结构中的关系余量：支持、Schur 递归与新维数}
\begin{theorem}[整体正性的支持与余量条件]\label{thm:schur}
给有限 Hermitian 块矩阵
\[
M=\begin{pmatrix}A&C\\C^\dagger&B\end{pmatrix}.
\]
当 $A\succeq0$ 时，$A^+$ 在正特征方向取倒数、零方向取零。
则
\[
\boxed{M\succeq0\iff
A\succeq0,\quad AA^+C=C,\quad
S:=B-C^\dagger A^+C\succeq0.}
\]
条件成立时 $\rank M=\rank A+\rank S$。
\end{theorem}
\begin{proof}
若 $M\succeq0$，其主块 $A\succeq0$。
若 $u\in\ker A$ 而 $d=u^\dagger Cv\ne0$，则向量 $(tu,v)$ 的二次型为
$2\Re(\bar t d)+v^\dagger Bv$；取 $t=-Td$、$T$ 足够大得到负值，矛盾。
因此 $\Ran C\subseteq\Ran A$，等价于 $AA^+C=C$。
在此支持条件下，完成平方给
\[
\begin{pmatrix}x\\y\end{pmatrix}^{\!\dagger}
M\begin{pmatrix}x\\y\end{pmatrix}
=(x+A^+Cy)^\dagger A(x+A^+Cy)+y^\dagger Sy.
\]
取 $x=-A^+Cy$ 得余量必要性；反向由两项非负得到充分性。
该换元可逆，故与 $\operatorname{diag}(A,S)$ 合同，秩相加。
\end{proof}

这是广义 Schur 判据，项目 V52 已用于精确递归；标准文献亦明确保留奇异支持条件
\cite{v52,schur}。例如 $A=0,C=1,B=1$ 给正的形式余量 $S=1$，
但整矩阵行列式为 $-1$；支持条件不能省略。

若 $A=V^\dagger V$、$C=V^\dagger W$、$B=W^\dagger W$ 已来自真实向量，
则 $P=VA^+V^\dagger$ 是旧锚空间投影，且
\[
\boxed{S=W^\dagger(I-P)W.}
\]
$S=0$ 表示新关系已在旧空间内；$S\succeq0$ 非零表示需要新的相容方向；
负余量或支持失败则表示原完整表无共同正实现。

\begin{corollary}[有限递归的完整见证]
对当前矩阵 $M=\left(\begin{smallmatrix}a&r^\dagger\\r&B\end{smallmatrix}\right)$：
$a<0$ 给负方向；$a=0,r\ne0$ 给一个负的二阶块；
$a=0,r=0$ 可删除零行列；$a>0$ 则递归余量 $B-rr^\dagger/a$。
若余量的负向量为 $y$，原矩阵的负向量为
\[
\boxed{\begin{pmatrix}-r^\dagger y/a\\y\end{pmatrix}.}
\]
有限步后得到非负模平方分解，或原坐标中的负见证。
\end{corollary}
\begin{proof}
逐步使用定理 \ref{thm:schur} 的单主元情形。
正主元的恒等式为
$q_M(s,y)=a|s+r^\dagger y/a|^2+y^\dagger(B-rr^\dagger/a)y$，
既保存正性也给负见证回传。每步维数降低。
\end{proof}

这种递归不是只检查原始二阶主块；后续余量已携带前面关系的信息。
若需保持完整内部上下文，项目的二元递归采用算子值三轴
\[
\rho=\tfrac12(I\otimes S+\sigma_x\otimes X+\sigma_y\otimes Y+\sigma_z\otimes Z).
\]
这里 $S,X,Y,Z$ 是上下文算子，整体块 PSD 与 $\Tr S=1$ 才是相容条件。
三个标量均值不保存全部关联；也不能一般替换为
$X^2+Y^2+Z^2\preceq S^2$。Bell 态给左侧 $3I/4$、右侧 $I/4$，
但整体完全合法 \cite{v37,v52}。

\plain{先用已有关系解释新关系，再看剩下的部分。
正的余量可以成为新方向；零余量表示已经解释完；负余量表示这些说法不能共同成立。
更大结构增加的是相容的上下文与方向，而不是把负关系藏到更高维里。}

\section{撤去酉性以后：哪些归一化缺口可以内部补全}
\begin{theorem}[收缩分支的二元补全]\label{thm:completion}
对有限维复线性 $A:\HH\to\HH$，存在某个 $B$ 使
\[
V\psi=A\psi\otimes\ket0+B\psi\otimes\ket1
\]
等距，当且仅当 $A^\dagger A\preceq I$。
可取 $B=(I-A^\dagger A)^{1/2}$，且该等距可在内部 ready 载体上补成酉。
\end{theorem}
\begin{proof}
标签正交使 $V^\dagger V=A^\dagger A+B^\dagger B$。
等距因此要求 $I-A^\dagger A=B^\dagger B\succeq0$。
反向取正平方根便得到等距，再补全输入、输出正交基即可酉扩张。
\end{proof}

对单位输入，成功与余量权重满足
\[
\|A\psi\|^2+\|B\psi\|^2=1.
\]
若 $I-A^\dagger A$ 有负方向，则保持这个 $A$ 和输入尺度的正余量补全不存在。
若另行缩放 $A$ 或改变对象的定义，已经是另一份关系合同。

\begin{theorem}[共同线性、完整范数关系与酉性]
对复线性 $T:\C^d\to\C^e$，
全部输入范数保持、全部两输入内积保持、$T^\dagger T=I$ 三者等价。
当 $d=e<\infty$ 时等价于酉性。
在已校准正交基上，只需检验
\[
e_i,\qquad (e_i+e_j)/\sqrt2,\qquad(e_i+ie_j)/\sqrt2\quad(i<j)
\]
这 $d^2$ 个输入的范数，即可认证等距。
\end{theorem}
\begin{proof}
范数通过复极化恢复内积，内积条件给矩阵式。
有限检验中，基向量给 Gram 对角为一；实叠加给交叉实部为零；
虚叠加的输出范数平方为 $1-\Im\langle Te_i,Te_j\rangle$，给虚部为零。
方阵等距为满射，故酉。
\end{proof}

仅检查 $\Omega=\ket0$，矩阵 $A=\operatorname{diag}(1,2)$ 看起来保范数，
却不保全部输入。强行逐态归一的
$F_A(\psi)=A\psi/\|A\psi\|$ 也把 $\ket0,\ket+$ 的转移概率从 $1/2$ 改为 $1/5$。
但取 $K_s=A/2$、$K_f=\operatorname{diag}(\sqrt3/2,0)$，
便有 $K_s^\dagger K_s+K_f^\dagger K_f=I$；
成功分支归一后正是 $F_A$。它是带输入相关权重与失败记录的条件过程，不能删去这些量后改称确定性酉门。

\plain{一个局部读出少了一部分，不一定是整个世界失去归一化。
若它是收缩的，可以把缺的部分作为另一个内部结果补回。
两部分一起保持关系，才得到整体等距与酉实现。
如果原作用已放大某个输入范数，就不能再用正的遗漏部分补成同一个守恒关系。}

\section{内部参考把局部正性接到完全正性，并选择酉旋转}
\begin{definition}[固定共同参考接口]
对同一复线性目标过程 $\Lambda:M_d(\C)\to M_e(\C)$，
内部参考的作用被校准为恒等，联合规则为同一个 $\Lambda\otimes\id$。
若它对任意有限参考保持正性，称 $\Lambda$ 完全正（CP）。
参考可以全部在同一 $\Omega$ 内；其独立端口、准备和目标作用仍须由关系认证。
\end{definition}

\begin{theorem}[参考正性的有限完整证书]\label{thm:choi}
采用未归一 Choi 矩阵
\[
J_\Lambda=\sum_{i,j}\Lambda(\ket i\bra j)\otimes\ket i\bra j.
\]
则 $\Lambda$ CP 当且仅当 $J_\Lambda\succeq0$。
输入维数 $d$ 的内部参考已经足够。
\end{theorem}
\begin{proof}
若 CP，作用于 $\ket\omega\bra\omega$，其中 $\ket\omega=\sum_i\ket{ii}$，
即得 $J_\Lambda\succeq0$。
反向分解 $J_\Lambda=\sum_\alpha f_\alpha f_\alpha^\dagger$，
按 $(K_\alpha)_{\mu i}=(f_\alpha)_{\mu i}$ 重排，比较矩阵块得
$\Lambda(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger$。
在任意参考上，每一项仍为正共轭，故完全正。
\end{proof}
保迹另要求 $\Tr_{\rm out}J_\Lambda=I_d$。
这是有限维的标准等价，项目 V58、$\Omega$ 与 Watrous 定理 2.22 均保留完整参考条件
\cite{v58,omega,watrous}。

\subsection*{撤去参考条件的明确后果}
转置 $T(X)=X^{\mathsf T}$ 在单系统上正、保迹、可逆，
并在纯态上保持射线转移概率。对内部 Bell 态
\[
\ket\Phi=(\ket{00}+\ket{11})/\sqrt2
\]
却有
\[
\boxed{(T\otimes\id)(\ket\Phi\bra\Phi)=F/2,}
\]
其中 $F$ 交换两个因子。对 $\ket{\psi_-}=(\ket{01}-\ket{10})/\sqrt2$ 的期望为 $-1/2$。
这证明单系统正性没有保护与内部参考的共同关系。

若要作正迹三维定位，取正交单位向量
\[
u=\ket{00},\qquad
v=\frac{\sqrt3}{2}\ket{\psi_-}+\frac12\ket{\psi_+},
\qquad \ket{\psi_+}=(\ket{01}+\ket{10})/\sqrt2.
\]
以 $u,v$ 为列的等距 $V$ 给
\[
V^\dagger(F/2)V=\begin{pmatrix}1/2&0\\0&-1/4\end{pmatrix},
\qquad
\frac{V^\dagger(F/2)V}{\Tr[V^\dagger(F/2)V]}
=\begin{pmatrix}2&0\\0&-1\end{pmatrix}
=\frac12(I+3\sigma_z).
\]
所以此候选的三轴为 $(0,0,3)$。这正是被否定的候选表，不能称为一种物理量子态。
原来的 $\ket{01},\ket{10}$ 二阶块迹为零，不能直接除迹；上述选择已处理这个边界。

\begin{center}
\begin{tikzpicture}[>=Stealth,scale=.95,font=\small]
\fill[auricblue!5] (0,0) circle (1);
\draw[auricblue,thick] (0,0) circle (1);
\draw[->] (-1.5,0)--(2,0) node[right] {$x$};
\draw[->] (0,-1.4)--(0,3.5) node[above] {$z$};
\fill[auricblue] (1,0) circle (2pt) node[below right] {$(1,0,0)$};
\fill[gray] (0,0) circle (2pt);
\fill[auricred] (0,3) circle (2pt) node[right] {$(0,0,3)$};
\node[align=left,anchor=west] at (3,2.2) {图为 $y=0$ 剖面。\\[4pt]
球内：合法标签比较。\\[4pt]
右端点：两端向量完全相同。\\[4pt]
球外：候选正性被反证。};
\end{tikzpicture}
\end{center}

\begin{theorem}[内部参考从三维对称中选出酉分支]\label{thm:so3}
在已给 qubit Bloch 态域上，对 $O\in O(3)$ 定义唯一复线性、保自伴延拓
\[
\Lambda_O(I)=I,\qquad
\Lambda_O(\sigma_j)=\sum_iO_{ij}\sigma_i.
\]
则
\[
\boxed{\begin{aligned}
\Lambda_O\text{ 为 CP}&\iff\det O=+1\\
&\iff\Lambda_O=\operatorname{Ad}_U\quad\text{对某个 }U\in U(2).
\end{aligned}}
\]
这里不需要连续时间前提，也不需先假定逆过程 CP。
\end{theorem}
\begin{proof}
若 $\det O=+1$，三维正交矩阵有固定轴，限制在垂直平面上是角度 $\theta$ 的旋转。
取单位轴 $n$，令
\[
U=\cos(\theta/2)I-i\sin(\theta/2)n\cdot\boldsymbol\sigma.
\]
由 $(a\cdot\sigma)(b\cdot\sigma)=(a\cdot b)I+i(a\times b)\cdot\sigma$ 展开，得
\[
r'=\cos\theta\,r+\sin\theta(n\times r)
 +(1-\cos\theta)(n\cdot r)n.
\]
故 $\Lambda_O=\operatorname{Ad}_U$，于是 CP。
若 $\det O=-1$，令 $S=\operatorname{diag}(1,-1,1)$、$R=OS\in SO(3)$。
$S$ 对应转置，所以 $\Lambda_O=\operatorname{Ad}_U\circ T$。
若其 CP，复合 $\operatorname{Ad}_{U^\dagger}$ 就会使 $T$ CP，与 Bell 见证矛盾。
最后酉共轭给正向旋转，或由上述两分支排除得到所列等价。
\end{proof}

为何 $O(3)$ 是自然候选？已给的纯态射线重叠为 $\Tr(P_rP_s)=(1+r\cdot s)/2$，
其概率解释使用下一节的读出相容条件。
若全部射线重叠保持，三个正交轴的像仍正交；任意像对这些轴的三个分量等于原来的分量，
故必为 $r\mapsto Or$。单看球允许旋转与镜像；同一局域规则对参考的正扩展排除镜像。
全体表示同时复共轭仍可作为规范，不能与在固定参考下对一个子系统实施转置混为一谈。

\subsection*{二元最终见证没有消去较高参考资源}
三维图可以定位最终负性，但准备检验它的关系可能需要更大的参考。
例如 $d=3$ 时
\[
\Lambda(X)=\frac{2\Tr(X)I_3-X}{5}
\]
保迹，且对二维参考保持正性，却不是 CP。
证明如下：写 Schmidt 分解 $\psi=\sum_{i=1}^r\sqrt{\lambda_i}\,a_i\otimes b_i$，$r\le2$，
其参考约化为 $\rho_R$。对任意 $z$，Cauchy--Schwarz 给
\[
|\langle\psi,z\rangle|^2
\le r\sum_i\lambda_i|\langle a_i\otimes b_i,z\rangle|^2
\le r\langle z,(I\otimes\rho_R)z\rangle.
\]
所以 $\ket\psi\bra\psi\preceq r(I\otimes\rho_R)$。
故 $(\Lambda\otimes\id_2)(\ket\psi\bra\psi)
=[2I\otimes\rho_R-\ket\psi\bra\psi]/5\succeq0$；
纯态生成正锥，得到二维参考正性。
而三维最大纠缠输入沿自身的输出期望为
$(2/3-1)/5=-1/15<0$。
因此不能把最终的两维压缩误读为所有过程只须 qubit 参考检验；项目 V59 也保留该层级 \cite{v59}。

\plain{单看一个三维球，镜像也能保留所有夹角。
把这个候选操作与同一个内部参考一起检查，才发现它不能保护共同正性。
这使“选择酉旋转”成为更大系统相容性的结论，而不是单靠球面形状作出的决定。}

\section{撤去读出加性：同一事件会因拆法不同而改变}
\begin{definition}[完整效果粗粒化合同]
固定一次准备，效果域为 $0\preceq E\preceq I$。
一个完整上下文是有限列表 $(E_1,\ldots,E_n)$，其和为 $I$。
每个完整上下文的响应之和为一。
同一效果在不同上下文有同一响应；合并互斥结果时，效果与概率各自相加。
这里比较事件概率，不要求两台仪器有相同的条件态更新。
\end{definition}

\begin{theorem}[粗粒化与有限加性等价]\label{thm:coarse}
完整效果上的非负响应满足上述合同，当且仅当
\[
p(I)=1,\qquad p(E+F)=p(E)+p(F)\quad(E,F\succeq0,\ E+F\preceq I).
\]
任何加性失败都有两个效果及共同余效果的有限见证。
\end{theorem}
\begin{proof}
比较 $(E,F,I-E-F)$ 与 $(E+F,I-E-F)$ 得必要性。
反向有限次合并给所有上下文的归一与粗粒化关系。
\end{proof}

\subsection*{逐表归一的幂规则反例}
令 $t_i\ge0$、$\sum_i t_i=1$，逐表指定
$P_\beta(i)=t_i^\beta/\sum_jt_j^\beta$，$\beta>0$。
每张表都归一。但从 $(I/2,I/2)$ 变成 $(I/2,I/4,I/4)$ 后，
同一个未改变的效果 $I/2$ 的读数从 $1/2$ 变成
\[
\boxed{\frac1{1+2^{1-\beta}}.}
\]
两者相等当且仅当 $\beta=1$；例如 $\beta=2$ 给 $2/3$。
若原 $t$ 是振幅平方，额外振幅幂对应 $\beta=p/2$，故该合同只保留 $p=2$。
这个反例首先是事件细分问题，甚至不需相干叠加。

\subsection*{所有二结果都合法，仍可能在关系的关系处失败}
对 qubit 效果 $E=aI+b\cdot\sigma$，定义
\[
p(E)=\begin{cases}a+b_z^3/|b|^2,&b\ne0,\\a,&b=0.\end{cases}
\]
合法效果满足 $|b|\le\min(a,1-a)$，所以 $p(E)\in[0,1]$。
该规则还有 $p(I-E)=1-p(E)$ 及合法正比例齐次性；故所有二结果 POVM 都归一。
在投影 $P_n=(I+n\cdot\sigma)/2$ 上，它就是项目 V52 的三次反例
$p(P_n)=(1+n_z^3)/2$ \cite{v52}。
取
\[
n=(\sqrt3/2,0,1/2),\quad m=(-\sqrt3/2,0,1/2),\quad
E_1=P_n/2,\ E_2=P_m/2.
\]
则 $E=E_1+E_2=I/2+\sigma_z/4$，且
\[
\boxed{p(E_1)+p(E_2)=9/16\ne3/4=p(E).}
\]
共同余效果的读数为 $1/4$，所以三结果表总读数为 $13/16$。
这表明二元语法不等于只检查二结果互补归一。

\begin{theorem}[完整响应与平方读出]
在有限维复效果域上，非负、单位归一、有限可加响应唯一具有
\[
p(E)=\Tr(\rho E),\qquad \rho\succeq0,\quad\Tr\rho=1.
\]
纯准备与秩一投影给 $p=|\langle\phi,\psi\rangle|^2$。
\end{theorem}
\begin{proof}
对正 $A$ 取整数 $m$ 使 $A/m\le I$，定义 $\ell(A)=mp(A/m)$。
共同整数倍与有限加性给良定义及正锥可加，正负差给 Hermitian 空间上的加性延拓。
对有理 $r>\|X\|$，序界 $-rI\le X\le rI$ 给 $|\ell(X)|\le r$，
进而有连续性与实线性。迹配对给唯一 Hermitian $\rho$，秩一非负性给 PSD，单位响应给迹一。
对两个秩一矩阵作迹配对即得平方。
\end{proof}
这是完整效果重建的有限维版本 \cite{v52,v58,busch}。
以正算子值记录
$V\psi=\sum_i\sqrt{E_i}\psi\otimes\ket i$ 实现一个完整测量时，
$V^\dagger V=\sum_iE_i=I$；合并记录投影直接给上述加性。
因此更大的内部记录结构为粗粒化相容提供明确的实现。

在维数至少二的已给内积空间中，若非负径向权重对正交合并可加且单位权重为一，
令 $F(t)=W(\sqrt t\,e)$，即有 $F(s+t)=F(s)+F(t)$。
非负性给单调性，有理夹逼给 $F(t)=t$，所以 $W(v)=\|v\|^2$。
平方由这项关系闭合选出；一般加乘语法或逐表归一单独不承担同样工作 \cite{v49,v52}。

\plain{一个事件没有变，只把旁边的结果拆得更细，它的概率不应改变。
若改变，就说明那些概率表没有组成同一套读出关系。
把记录合并、细分和同一效果的辨认一起放进整体，才能把概率形式锁定。}

\section{共同复定向属于怎样的更大结构：闭路与双覆盖}
项目 V58 的局部实关系代数先由三轴 Clifford 关系锁成 $M_2(\C)$。
在这个中心内，平方为 $-1$ 的元素只有 $\pm J$。
因此以下符号模型适用于已作这种局部识别的定向比较，
不适用于任意实内积空间中的全部可能复结构 \cite{v58,v59}。

\begin{definition}[半线性内部比较图]
连通图顶点 $v$ 带正交复结构 $J_v$。
每条边 $e:v\to w$ 有实等距可逆比较 $T_e$，满足
\[
T_eJ_v=\varepsilon_eJ_wT_e,\qquad \varepsilon_e\in\{+1,-1\}.
\]
反向边取逆，符号相同。这里比较接口不自动是固定复编码上的可实施局域量子门。
\end{definition}

\begin{theorem}[共同定向的闭路判据]\label{thm:orientation}
重标记 $J'_v=\eta_vJ_v$，$\eta_v=\pm1$，使全部边成为复线性，
当且仅当每个闭路 $C$ 满足
\[
\boxed{\prod_{e\in C}\varepsilon_e=+1.}
\]
连通图的定向选择只差全体同时翻转。
\end{theorem}
\begin{proof}
边符号变为 $\varepsilon'_e=\eta_v\varepsilon_e\eta_w$。
若全部为正，沿闭路的端点符号相消，得必要性。
反向选根，在一棵生成树上用路径符号积定义 $\eta_v$；
闭路条件使非树边也相容。两组解之比沿每条边恒定，连通性给整体 $\pm1$。
\end{proof}

奇符号闭路给 $T_CJ_v=-J_vT_C$。
它首先表示绕路后留下反线性取向，不是无条件矛盾。
若又要求这个同历史闭路 $T_C=I$，或要求它复线性且可逆，才发生冲突。
全体共同翻转是表示规范；与对固定参考下单个子系统施加转置是不同问题。

\begin{proposition}[记录一位取向的内部扩张]
把顶点扩为 $(v,s)$，$s=\pm1$，令 $J_{(v,s)}=sJ_v$；
把边提升为
\[
(v,s)\longrightarrow(w,\varepsilon_es).
\]
沿边仍用 $T_e$，则所有提升边均与复结构相容。
\end{proposition}
\begin{proof}
$T_eJ_{(v,s)}=s\varepsilon_eJ_wT_e
=J_{(w,\varepsilon_es)}T_e$。
\end{proof}

这是取向双覆盖。奇闭路从 $(v,s)$ 走到 $(v,-s)$，
不再被误认成同一提升顶点的返回。
该扩张明确保留了原标签省略的一位信息，
不证明宇宙有两层，也不把反酉自动变成原系统的确定性 CP 门。

\plain{每一处都能选自己的左右手约定，但沿不同路径比较，最终必须知道是否回到同一约定。
共同复结构要求闭路上这些选择能够接起来。
若绕一圈翻了方向，可以先把被遗漏的取向记录补入更大结构，再判断原来的“同一个点”是否确实应该等同。}

\section{把反向见证接到项目原生 AURIC 五模式}
以下直接采用 V37 定义 3.1 的固定码，模式顺序为 $(0,2,3,5,25)$。
令
\[
\nu=(1+2\sqrt3+\sqrt{11})^{-1},\qquad
a_\nu=\nu(\sqrt3+\sqrt{11})/2,\qquad u_0=(a_\nu,a_\nu,\nu).
\]
该码的固定五效果为
\begin{align*}
E_{25}&=\tfrac\nu2(\sqrt3 I-\sigma_x-\sigma_y-\sigma_z),&E_0&=3E_{25},\\
E_2&=\tfrac\nu2(\sqrt{11}I+3\sigma_x+\sigma_y+\sigma_z),\\
E_5&=\tfrac\nu2(\sqrt{11}I+\sigma_x+3\sigma_y+\sigma_z),&E_3&=\nu(I+\sigma_z).
\end{align*}
各效果正且秩一，和为 $I$。
对归一态 $\rho=(I+r\cdot\sigma)/2$，令 $p_s=\Tr(\rho E_s)$，
$X=p_2+p_{25}$、$Y=p_5+p_{25}$、$Z=p_3$。
等距编码将这些原占据均值标定为
\[
\boxed{(X,Y,Z)=u_0+\nu(x,y,z).}
\]
这是原金字塔内的指定球族，三个占据读口仍是同一个五结果测量的兼容读数，
不是三个同时尖锐 Pauli 测量 \cite{v37}。

\begin{corollary}[关系余量直接进入原三轴]
将定理 \ref{thm:comparison} 的标签态送入上述固定码，则
\[
\boxed{\|(L-R)\psi_w\|^2
=s\left(1-\frac{X-a_\nu}{\nu}\right),\qquad
p_-=\frac12\left(1-\frac{X-a_\nu}{\nu}\right).}
\]
完整比较关系仍由三个标定均值与尺度 $s$ 保存。
\end{corollary}
\begin{proof}
代入 $x=(X-a_\nu)/\nu$；其余坐标由同一仿射式恢复。
\end{proof}

对未归一 Hermitian 候选 $G$，令
\[
w_s=\Tr(GE_s),\quad N=\Tr G,\quad
X=w_2+w_{25},\quad Y=w_5+w_{25},\quad Z=w_3,\quad \kappa=w_{25}.
\]
这些同尺度矩对任意 Hermitian $G$ 都满足项目的线性恒等式
\[
\boxed{N-X-Y-Z-2\kappa=0,}
\]
而候选 $G$ 正半定，当且仅当还满足球锥条件
\[
\|(X-a_\nu N,Y-a_\nu N,Z-\nu N)\|_2\le\nu N,\qquad N\ge0.
\]
线性式给指定码内的四推一，球锥则另行承担正性。
一般五事件族没有自动满足这个码条件，三个均值之外仍有 $\kappa$ 纤维 \cite{v17,v37}。

\begin{proposition}[五概率与四推一都合法，仍可能不在量子球内]\label{prop:fivecounter}
取 Hermitian 候选
\[
W=\tfrac12(I+\tfrac32\sigma_z)
=\operatorname{diag}(5/4,-1/4).
\]
令 $p_s=\Tr(WE_s)$。则
\begin{align*}
p_{25}&=\tfrac\nu2(\sqrt3-3/2)>0,&p_0&=3p_{25},\\
p_2&=p_5=\tfrac\nu2(\sqrt{11}+3/2)>0,&p_3&=5\nu/2>0.
\end{align*}
全部五概率非负、和为一，四推一线性式成立，但不存在具有这些码内三轴的正 qubit 态。
\end{proposition}
\begin{proof}
直接作 Pauli 迹配对得到所列数；其和为
$\nu(1+2\sqrt3+\sqrt{11})=1$。
由 $p_0=3p_{25}$ 得线性式。
三轴反演却唯一给 $r=(0,0,3/2)$，球条件失败；
额外效果 $\ket1\bra1$ 在 $W$ 上给 $-1/4$。
\end{proof}

这组五标签经典分布本身合法；失败的是将它解释为同一指定 qubit 接口的完整正响应。
它具体体现 V59 的区分：有限读数可以重建已知模型内的态，
但有限菜单的逐项非负并不单独认证整个正态类 \cite{v59}。
同样，V37 §12 证明：本码内每个酉都有可逆仿射概率更新；
若另要求同一个非负随机矩阵作用于整个五标签单纯形，则只有标量相位门满足。
因此反向研究也可能识别一个应当放弃的额外经典闭合要求，而不是增添一个量子公理。

\plain{AURIC 的三轴可以成为精确比较工具，但必须使用同一个码和同一把尺度。
五个数都正、总和为一、还满足四推一，仍不代表它们已通过整个量子关系网的检查。
球面约束、相干关系和后续读口规定它们属于哪一种共同结构。}

\section{从有限三维比较到整体法则：同源覆盖与稳定界}
设 $r=L-R$ 为有界算符差，在所声明的循环生成空间上工作。
若 $r\pi(w)\Omega=0$ 对全部历史词成立，则线性性与连续性使它在该闭包上为零。
因此法则失败有某个同源上下文见证，而不需要更换本体。
一般无界表示只在声明的共同代数定义域上作同样结论。

\begin{theorem}[满锚覆盖的三维余量界]\label{thm:stability}
设 $\xi_j=\pi(b_j)\Omega$ 构成有限声明空间 $\mathcal K$ 的一个基，
Gram 为 $G\succ0$，$\gamma=\lambda_{\min}(G)>0$。
对 $L\xi_j,R\xi_j$ 的比较得尺度 $s_j$ 与坐标 $x_j$，零尺度贡献取零。
则限制在 $\mathcal K$ 上有
\[
\boxed{\|(L-R)|_{\mathcal K}\|^2
\le\frac{\sum_j s_j(1-x_j)}\gamma
=\frac{2\sum_j s_jp_{-,j}}\gamma.}
\]
若 $F_{ij}=\langle r\xi_i,r\xi_j\rangle$，更精确地
\[
\|r|_{\mathcal K}\|^2=\sup_{c\ne0}\frac{c^\dagger Fc}{c^\dagger Gc}.
\]
\end{theorem}
\begin{proof}
输入 $\sum_jc_j\xi_j$ 及输出的范数平方分别为 $c^\dagger Gc$、$c^\dagger Fc$。
由 $F\succeq0$ 和 $G\succeq\gamma I$，最大比值不超过 $\Tr F/\gamma$。
而定理 \ref{thm:comparison} 给 $F_{jj}=s_j(1-x_j)=2s_jp_{-,j}$。
\end{proof}

所以整个声明空间上的等式成立，当且仅当每个锚满足：
两端同为零，或 $s_j>0$ 且比较点为 $(1,0,0)$。
只有根检验不够：$\Omega=\ket0$、$r=\ket1\bra1$ 时 $r\Omega=0$，
但 $r\sigma_x\Omega=\ket1$。
没有满覆盖，结论只控制已覆盖子空间；丢掉尺度不能控制绝对误差；
锚近线性相关使 $\gamma$ 小，认证会变差。

负性也有简单稳健界：若 $\|M-\widehat M\|\le\delta$，
单位 $w$ 满足 $w^\dagger\widehat Mw=-\eta$，则
$w^\dagger Mw\le-\eta+\delta$。
只有 $\eta>\delta$ 才保证真表负性。小正主元的 Schur 消元可能病态，
精确关系与噪声稳定性不能互相替代。

\plain{每次三维比较只检查一个方向。
若内部参考已覆盖全部声明方向，这些比较就能合成一个整体误差界。
参考是否足够分开、尺度是否保留，决定“看起来差不多”能否提升为可靠的整体结论。}

\section{更简洁的关系形式，以及本轮真正锁定了什么}
保留前稿的同源正关系体
\[
\mathfrak R=(\Alg,\ell),\qquad
\Alg=\R\langle S,S^*\rangle/\mathcal I,
\]
其中 $\ell(1)=1$、$\ell(a^*a)\ge0$，
并在项目明确的局部 Clifford 与共同复定向条件下使用相应复表示。
所有准备、参考、记录和比较程序都属于该同一结构；来源为其循环表示的 $\Omega=[1]$。
内部比较的数学存在、实际菜单供应与经验识别须使用同一份接口合同。

\begin{theorem}[本轮的反向定位与关系闭合]
在上述各节声明的对象类和接口下，有以下条件结论：
\begin{enumerate}
\item Hermitian 单位响应的整体正性，等价于全部可缩放合成二元正迹表的球内条件。
\item 一个算符等式在有限声明空间成立，等价于覆盖该空间的每个同源锚，其两端同为零，或其非零尺度比较达到相等目标点；误差受定理 \ref{thm:stability} 控制。
\item 局部线性分支可由正的内部余量补成等距，当且仅当它是收缩；同维完整线性范数保持给酉。
\item 完整参考下的正作用等价 CP；对 Bloch 正交候选，它进一步等价于正向旋转及酉共轭。
\item 效果的细分／合并相容给完整有限加性，进而给 Born 迹响应；已校准复定向的全局粘合则由闭路符号判定。
\end{enumerate}
\end{theorem}
\begin{proof}
依次由定理 \ref{thm:binarypositive}、\ref{thm:comparison} 与 \ref{thm:stability}、
\ref{thm:completion}、\ref{thm:choi} 与 \ref{thm:so3}、
\ref{thm:coarse} 及 \ref{thm:orientation} 得到。
各结论保留其前件，不能将某节的候选对象自动当成另一节已经合法的物理态。
\end{proof}

\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.18\textwidth}>{\raggedright\arraybackslash}p{.32\textwidth}X@{}}
\toprule
待解释条件 & 撤去后的明确见证 & 所属的更大关系\\
\midrule
整体正性 & 合成二元块球外、Schur 支持或余量失败 & 全部历史组合的共同正核。\\
封闭门的酉性 & 交叉关系改变或范数缺口 & 共同线性输入与全部内部记录的等距关系。\\
完全正性 & 内部关联参考上的负权重 & 同一目标规则对保留参考的正扩展。\\
平方读出 & 同一效果因细分而改值 & 效果分解、合并与正响应的共同闭合。\\
共同复定向 & 负符号闭路 & 局部中心、比较路径和取向记录的一致性。\\
全局法则认证 & 根检验通过、后续历史失败 & 同源锚覆盖、接续闭合及条件数。\\
\bottomrule
\end{tabularx}
\end{center}

于是可用下面一句话组织量子关系重建：
\[
\boxed{\text{同源关系在合成、细分、比较及内部参考扩展中保持正归一相容。}}
\]
这是一种结构化表述，不是仅凭字面便确定模型的单一无前件公理。
局部代数、共同复结构、复合方式、完整响应与实际覆盖的内容仍须明确。
把这些要求内生化，不等于已经从更弱背景证明它们全部必然成立；
本轮给出了哪些要求等价、哪些失败可定位、哪些缺口可以补全的精确边界。
同一个实际 $\Omega$ 可以始终固定；多种满足部分约束的数学模型表示当前描述尚未锁定的部分，
不要求另设多个实际本体。

\Needspace{9\baselineskip}
\plain{整个图景始终围绕同一个 $\Omega$。
我们让它生成两段可以比较的内部历史，看看本来声称相同的东西是否真的相同。
局部比较能放到受限三维中，尺度和偏移说明余量；把参考、记录与相干关系补齐，再检查整张网是否共同成立。
少了一条分支，可以在条件允许时把它补回；负的完整关系不能靠升维掩盖；绕路翻了定向，就要记录取向或重新检查路径等同。
观察者自己的预测与校准也在这张网中。
公理因此逐步显出它保护的整体关系：线性怎样与归一共同成立、为什么完整相容读出为平方、为什么局部门必须能与其他内部角色共同存在。}

\clearpage
\begin{thebibliography}{99}\small
\bibitem{v17} 项目固定提交。
\repo{AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md}{V17：加乘、对数与量子勾股几何}，
本轮使用 §§3--4、9 与命题 13.3 的相关定义、证明及范围。
\bibitem{v37} 项目固定提交。
\repo{AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md}{V37：二元关系的酉表示与黄金门通用性}，
本轮完整读取 §§1--6、12；不认证后续全部原生控制供应链。
\bibitem{v49} 项目固定提交。
\repo{AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md}{V49：加乘指数、二次关系闭合与归一化升维}，§§3--5。
\bibitem{v52} 项目固定提交。
\repo{AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md}{V52：纯态商几何、二次关系生成与无损递归}，§§2--7。
\bibitem{v58} 项目固定提交。
\repo{AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md}{V58：关系公理、共同复相位与条件量子重建}，§§2--8、10--14。
\bibitem{v59} 项目固定提交。
\repo{AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md}{V59：局部层析、相干读出轨道与正性起源}，
§1.2、§§2--5、§10 的所用段；未认证后续全部实际菜单供应。
\bibitem{omega} 项目固定提交。
\repo{AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md}{$\Omega$ 静态相容纤维理论}，
§§1--8、12 的共同实现与有限协议条件。
\bibitem{v76} 本对话前稿。
\emph{加乘生成、二次关系网与内生量子结构}，v76.0，2026 年 11 月 1 日。
对话交付稿，不冒称仓库原生文件。
\bibitem{watrous} John Watrous.
\emph{The Theory of Quantum Information}. Cambridge University Press, 2018.
\href{https://jhwatrous.github.io/TQI.2.pdf}{作者公开第 2 章}，
本轮核对定理 2.22、保迹／等距条件及转置例的相关段落；不声称阅读全书。
\bibitem{schur} Jean Gallier.
\href{https://www.cis.upenn.edu/~jean/schur-comp.pdf}{\emph{The Schur Complement and Symmetric Positive Semidefinite (and Definite) Matrices}},
2019 年 8 月 24 日稿，定理 4.3 及其支持条件、完成平方的相关段落。
本文给出复 Hermitian 有限维证明。
\bibitem{busch} Paul Busch.
\emph{Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem}.
Phys. Rev. Lett. 91, 120403 (2003).
\href{https://arxiv.org/pdf/quant-ph/9909073}{arXiv:quant-ph/9909073}。
前轮已核完整效果条件与证明；本稿给有限维自足版本。
\end{thebibliography}
\end{document}
```
AURIC-V77-IMMUTABLE-SOURCE-END -->

## 摘要

本稿把“撤去公理、寻找后果、定位两个元、作三维提升”组织为有明确前件的反向研究方法。
对同一来源的两条历史，构造二元比较标签态，证明关系余量精确等于
$s(1-x)$；对仅有 Hermitian 与单位归一的候选响应，证明全部合成二元正迹块的球内条件等价于整体正性。
全局负性可以有有限二元见证，但只检查原始两两关系不足；Schur 支持与递归余量保存整体约束。
证明收缩分支恰可补成内部等距记录，完整参考正性等价完全正性，且在已给 qubit 球与复合接口中排除反射、选择酉旋转。
效果细分相容、复定向闭路及固定五模式编码分别给另一类内部约束与精确反例。
最后以满锚覆盖将有限三维读出连接到整体算符误差界。
球外候选表、球内关系残差、漏失的分支与离散取向障碍分别处理；不把一切失效都叫作同一种物理态，也不声称从无前件选择实际宇宙。

<a id="sec-1"></a>

## 1. 反向研究的逻辑与固定项目依据

用户提出的方法可以具体化为：固定已经取得的关系，撤去一项待解释条件，
找出新增候选在哪里不再满足所要求的整体相容，再决定是补回条件、补入内部角色，还是承认另一种模型仍未被排除。
本轮不以绝对最少公理条数为目标。

#### 定义 1.1（相对于背景的反向见证）

固定背景条件 $\mathcal B$、待解释条件 $A$ 与明确的整体合同 $C$。
一个完整的反向定位要求证明

$$

\mathcal B\land\neg A\ \Longrightarrow\ \exists w\;D(w),
\qquad C\ \Longrightarrow\ \forall w\;\neg D(w).

$$

若还证明 $\mathcal B\land A\Rightarrow C$，便在该背景中得到 $A$ 与 $C$ 的等价。
仅找到一个 $\neg A$ 的坏模型，只证明失效可能发生，不证明所有撤去 $A$ 的模型都会失效。

后果也有不同类型：某个局部分支可以在更大仪器中合法；某张完整负关系表却不能靠增加正 Hilbert 维数修复。
“在同一个 $\Omega$ 内”允许共同描述全部角色，并不自动保证任意局部表有共同实现。
本文的有限三维见证适用于所声明的二次形式与算符关系；连续性或任意逻辑命题的失败仍需自己的证据。

本轮唯一实时 HEAD GET 于新加坡时间 2026-11-01 21:42:05，
在取得 HTTP 响应前因网络权限失败；没有重试、重定向、备用活动端点或提权。
以下采用七份原始 Markdown 重新核对 Git blob 的固定提交
`5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b`。
v77 是本对话稿件编号，不是已取得的仓库最新版本。

<div tabindex="0" role="region" aria-label="原稿表格" style="overflow-x:auto;max-width:100%;">

|项目来源|本轮消费的关系及边界|
|---|---|
|V17 §§3--4、9；命题 13.3|一般五概率的关系纤维、相位与三态 Gram。|
|V37 §§1--6、12|二元球、指定五模式码、算子值递归、完整 Gram 与五标签随机更新。|
|V49 §§3--5；V52 §§2--7|平方的附加闭合、完整效果、相位不变量与 Schur 余量。|
|V58 §§2--8、10--14|内部复单位、正响应、同源表示、酉与 CP 的条件。|
|V59 §§1.2--5、10 的相关段|完整关系、实际覆盖、有限菜单与参考层级。|
|$\Omega$ §§1--8、12|静态相容、完整支撑粘合、内部参考与有限协议。|

</div>

不据此认证全部仓库、后续原生供应链或源文所报告的程序证明。
本稿所有数学采用纸面推导与独立纸面复核，没有数学程序、CAS、数值求值、枚举、仿真或机器证明。
前稿 v76 的保守加乘展开继续作为表达背景；辅助名字不增加独立来源 [[8](#ref-v76)]。

> **白话图景。** 反过来问公理为什么需要，就要看它保护哪一种“一起成立”。 有时缺的是一个被漏掉的内部角色；有时已有关系本身互相冲突。 把这两种情况分开，才能知道扩大结构究竟补回了什么。

<a id="sec-2"></a>

## 2. 同源关系等式的二元三维比较核

以下内积对第二槽线性。固定同一来源 $\Omega$，历史 $w$ 给输入
$\psi_w=\pi(w)\Omega$。关系等式的两端 $L,R$ 在该输入上给

$$

a=L\psi_w,\qquad b=R\psi_w,\qquad s=\|a\|^2+\|b\|^2.

$$

这里 $L,R$ 可以代表两条不同表达或历史；把它们当实际装置时须保留共同输入与相干比较接口。

<a id="thm:comparison"></a>

#### 定理 2.1（法则余量的精确三轴读出）

当 $s>0$ 时，定义内部标签比较向量

$$

\lvert \Phi\rangle{}=\frac{\lvert 0\rangle{}\otimes a+\lvert 1\rangle{}\otimes b}{\sqrt s}.

$$

其标签约化态及三轴为

$$

\rho=\frac1s\begin{pmatrix}\|a\|^2&\langle b,a\rangle\\
\langle a,b\rangle&\|b\|^2\end{pmatrix}
=\frac12(I+x\sigma_x+y\sigma_y+z\sigma_z),

$$

$$

x=\frac{2\Re\langle a,b\rangle}{s},\quad
y=\frac{2\Im\langle a,b\rangle}{s},\quad
z=\frac{\|a\|^2-\|b\|^2}{s}.

$$

于是

$$

\boxed{\|(L-R)\psi_w\|^2=s(1-x),\qquad
p_-:=\langle-|\rho|-\rangle=\frac{1-x}{2}.}

$$

特别地，$L\psi_w=R\psi_w$ 当且仅当 $(x,y,z)=(1,0,0)$。
若 $s=0$，两端均为零，关系成立，但没有归一标签态。

**证明。**

对原载体取偏迹得到矩阵。展开差的范数给
$\|a-b\|^2=s-2\Re\langle a,b\rangle$。
投影到 $\lvert -\rangle{}=(\lvert 0\rangle{}-\lvert 1\rangle{})/\sqrt2$ 后，原载体向量为
$(a-b)/\sqrt{2s}$，故得概率式。
两端相等且非零时标签为 $\lvert +\rangle{}$；反向 $x=1$ 使差的范数为零。

∎

标签矩阵是通常 Gram 矩阵
$\left(\begin{smallmatrix}\|a\|^2&\langle a,b\rangle\\\langle b,a\rangle&\|b\|^2\end{smallmatrix}\right)$
的转置除以 $s$，所以 $y$ 的符号不能与直接归一通常 Gram 的公式混用。

#### 命题 2.2（保存范围与相位范围）

保留 $s$ 和三个标签坐标，恰保留有序向量对的完整 Gram。
它确定该向量对到其张成空间之间的共同等距，未确定相对于整个环境的嵌入。
对于非零两端，若只比较相位商，则

$$

\min_\theta\|a-e^{i\theta}b\|^2
=s-2|\langle a,b\rangle|
=s\bigl(1-\sqrt{x^2+y^2}\bigr).

$$

**证明。**

从 $s,x,y,z$ 直接恢复两对角与复交叉项。
若两对向量 Gram 相同，映射 $\alpha a+\beta b\mapsto\alpha a'+\beta b'$
保持所有范数，因此良定义且等距。相位式由选择交叉项的最大实部得到。

∎

若输入归一且 $L,R$ 为酉，具有受控相干接口时，
对 $\lvert +\rangle{}\otimes\psi_w$ 施加
$\lvert 0\rangle{}\langle 0\rvert{}\otimes L+\lvert 1\rangle{}\langle 1\rvert{}\otimes R$ 即实现比较，此时 $s=2$。
对归一输入，一般有界 $L,R$ 可选共同 $c_0>0$，使
$c_0^2(L^\dagger L+R^\dagger R)\preceq I$；
相干成功分支为 $c_0(\lvert 0\rangle{}L\psi+\lvert 1\rangle{}R\psi)$，
成功概率 $c_0^2s$，并须保留失败分支。
单独拥有两个未受控通道不自动供应其共同相位或受控比较。

> **白话图景。** 同一个输入沿两条关系走，比较最后是否真得到同一向量。 关系完全相同，对应球上的一个指定点；关系有余量，就偏离这个点。 尺度 $s$ 把球中偏移换成真实误差。 比较使用同一个来源，不需要复制一个未知输入态。

<a id="sec-3"></a>

## 3. 撤去正性：哪些三维候选会失败

<a id="prop:ball"></a>

#### 命题 3.1（正迹二元形式与三球）

设 $H=\left(\begin{smallmatrix}a&\bar c\\c&b\end{smallmatrix}\right)$ Hermitian，
$t=a+b>0$。令

$$

\mathbf r=\frac1t(2\Re c,2\Im c,a-b).

$$

则

$$

H=\frac t2(I+\mathbf r\cdot\boldsymbol\sigma),\qquad
\lambda_\pm(H)=\frac t2(1\pm|\mathbf r|),

$$

因而 $H\succeq0$ 当且仅当 $|\mathbf r|\le1$。
$t<0$ 时已有负方向；$t=0$ 时仅 $H=0$ 可正。

**证明。**

比较矩阵条目，并解二阶特征方程；判别式为
$(a-b)^2+4|c|^2=t^2|\mathbf r|^2$。
零迹正矩阵的所有非负本征值之和为零，故为零。

∎

不能除以负迹掩盖负性，例如 $-I/\operatorname{Tr}(-I)=I/2$。
在 $t>0$ 分支，恢复完整形式须保留 $t$ 与三个坐标；$t\le0$ 按上述边界另处理。
归一点本身没有保存尺度。
球外是被反证的候选形式，不是可以实际制备的量子态。

<a id="thm:binarypositive"></a>

#### 定理 3.2（整体正性等价于全部合成二元球条件）

设含幺复 $*$ 代数上 $\ell$ Hermitian、线性，$\ell(1)=1$，不预设正性。
对任意代数元 $a,b$ 定义

$$

H_{a,b}=\begin{pmatrix}
\ell(a^*a)&\ell(b^*a)\\
\ell(a^*b)&\ell(b^*b)
\end{pmatrix}.

$$

以下条件等价：

1. $\ell(p^*p)\ge0$ 对所有 $p$ 成立；
2. 所有正迹 $H_{a,b}$ 归一后的 Bloch 向量均在单位球内；
3. 第二项只对 $a=1$、$b$ 为任意可缩放代数元成立。

**证明。**

正性使每个二元 Gram 正，转置仍正，故第一项推出第二项；第二项推出第三项显然。
若第一项失败，取 $\ell(p^*p)=-d<0$，令 $b=p/\sqrt{2d}$。
$H_{1,b}$ 的对角为 $(1,-1/2)$、迹为 $1/2$；
归一后对角为 $(2,-1)$，故 $z=3$，与第三项矛盾。

∎

这里 $p$ 必须包括历史词的有限线性组合。
例如在 $\mathbb C[\mathbb Z_3]$ 中设

$$

g^3=1,\quad g^*=g^2,\quad
\ell(1)=1,\quad\ell(g)=\ell(g^2)=-3/4.

$$

任意两个群词的关系块对角为一、交叉为一或 $-3/4$，均正。
但 $p=1+g+g^2$ 满足 $p^*p=3p$，从而

$$

\boxed{\ell(p^*p)=3(1-3/4-3/4)=-3/2<0.}

$$

所以全部原始两两检查仍不足；线性合成与整体相容在此承担实质内容。
定理 [3.2](#thm:binarypositive) 是正性的一种等价关系表达，不是从更弱内容免费得到正性。

<a id="thm:compression"></a>

#### 定理 3.3（有限负性具有真正的二维压缩见证）

若有限维 Hermitian $W$ 满足 $\operatorname{Tr} W>0$ 而 $W\not\succeq0$，
则存在二维等距 $V$，使 $C=V^\dagger WV$ 的迹为正且有负本征值。
于是 $C/\operatorname{Tr} C$ 的三轴在球外。

**证明。**

取负本征值 $-b<0$ 的单位向量 $n$。
若有正本征值 $a>b$，其单位向量与 $n$ 组成所需压缩。
否则取最大正本征值 $a\le b$ 及向量 $p$；
正总迹迫使另有正本征值 $c>0$ 及与 $p,n$ 正交的向量 $q$。
取 $0<\epsilon<\min(c,b)$、$\tau=(a+\epsilon)/(a+b)$，令

$$

u=q,\qquad v=\sqrt\tau\,n+\sqrt{1-\tau}\,p.

$$

两者正交归一，压缩为 $\operatorname{diag}(c,-\epsilon)$，迹为正。
再用命题 [3.1](#prop:ball)。

∎

二维方向可以含许多原始历史，不能据此消去构造它们所需的相干资源或参考维数。
固定完整负 Gram 表无法在任何更大正 Hilbert 空间实现：
实际向量列的 Gram 必为 $T^\dagger T\succeq0$。
增加维数可容纳合法表的新秩，不能改变同一表的负方向 [[2](#ref-v37)]。

> **白话图景。** 关系可以在原来的每一对上看起来正常，却在几段历史合成以后冲突。 把这个冲突集中到两个合成方向，便能用一个三维球外候选看见它。 这个球外点说明原来的解释不能成立；它不是一种新的量子态。

<a id="sec-4"></a>

## 4. 更大结构中的关系余量：支持、Schur 递归与新维数

<a id="thm:schur"></a>

#### 定理 4.1（整体正性的支持与余量条件）

给有限 Hermitian 块矩阵

$$

M=\begin{pmatrix}A&C\\C^\dagger&B\end{pmatrix}.

$$

当 $A\succeq0$ 时，$A^+$ 在正特征方向取倒数、零方向取零。
则

$$

\boxed{M\succeq0\iff
A\succeq0,\quad AA^+C=C,\quad
S:=B-C^\dagger A^+C\succeq0.}

$$

条件成立时 $\operatorname{rank} M=\operatorname{rank} A+\operatorname{rank} S$。

**证明。**

若 $M\succeq0$，其主块 $A\succeq0$。
若 $u\in\ker A$ 而 $d=u^\dagger Cv\ne0$，则向量 $(tu,v)$ 的二次型为
$2\Re(\bar t d)+v^\dagger Bv$；取 $t=-Td$、$T$ 足够大得到负值，矛盾。
因此 $\operatorname{Ran} C\subseteq\operatorname{Ran} A$，等价于 $AA^+C=C$。
在此支持条件下，完成平方给

$$

\begin{pmatrix}x\\y\end{pmatrix}^{\!\dagger}
M\begin{pmatrix}x\\y\end{pmatrix}
=(x+A^+Cy)^\dagger A(x+A^+Cy)+y^\dagger Sy.

$$

取 $x=-A^+Cy$ 得余量必要性；反向由两项非负得到充分性。
该换元可逆，故与 $\operatorname{diag}(A,S)$ 合同，秩相加。

∎

这是广义 Schur 判据，项目 V52 已用于精确递归；标准文献亦明确保留奇异支持条件
[[4](#ref-v52), [10](#ref-schur)]。例如 $A=0,C=1,B=1$ 给正的形式余量 $S=1$，
但整矩阵行列式为 $-1$；支持条件不能省略。

若 $A=V^\dagger V$、$C=V^\dagger W$、$B=W^\dagger W$ 已来自真实向量，
则 $P=VA^+V^\dagger$ 是旧锚空间投影，且

$$

\boxed{S=W^\dagger(I-P)W.}

$$

$S=0$ 表示新关系已在旧空间内；$S\succeq0$ 非零表示需要新的相容方向；
负余量或支持失败则表示原完整表无共同正实现。

#### 推论 4.2（有限递归的完整见证）

对当前矩阵 $M=\left(\begin{smallmatrix}a&r^\dagger\\r&B\end{smallmatrix}\right)$：
$a<0$ 给负方向；$a=0,r\ne0$ 给一个负的二阶块；
$a=0,r=0$ 可删除零行列；$a>0$ 则递归余量 $B-rr^\dagger/a$。
若余量的负向量为 $y$，原矩阵的负向量为

$$

\boxed{\begin{pmatrix}-r^\dagger y/a\\y\end{pmatrix}.}

$$

有限步后得到非负模平方分解，或原坐标中的负见证。

**证明。**

逐步使用定理 [4.1](#thm:schur) 的单主元情形。
正主元的恒等式为
$q_M(s,y)=a|s+r^\dagger y/a|^2+y^\dagger(B-rr^\dagger/a)y$，
既保存正性也给负见证回传。每步维数降低。

∎

这种递归不是只检查原始二阶主块；后续余量已携带前面关系的信息。
若需保持完整内部上下文，项目的二元递归采用算子值三轴

$$

\rho=\tfrac12(I\otimes S+\sigma_x\otimes X+\sigma_y\otimes Y+\sigma_z\otimes Z).

$$

这里 $S,X,Y,Z$ 是上下文算子，整体块 PSD 与 $\operatorname{Tr} S=1$ 才是相容条件。
三个标量均值不保存全部关联；也不能一般替换为
$X^2+Y^2+Z^2\preceq S^2$。Bell 态给左侧 $3I/4$、右侧 $I/4$，
但整体完全合法 [[2](#ref-v37), [4](#ref-v52)]。

> **白话图景。** 先用已有关系解释新关系，再看剩下的部分。 正的余量可以成为新方向；零余量表示已经解释完；负余量表示这些说法不能共同成立。 更大结构增加的是相容的上下文与方向，而不是把负关系藏到更高维里。

<a id="sec-5"></a>

## 5. 撤去酉性以后：哪些归一化缺口可以内部补全

<a id="thm:completion"></a>

#### 定理 5.1（收缩分支的二元补全）

对有限维复线性 $A:\mathcal H\to\mathcal H$，存在某个 $B$ 使

$$

V\psi=A\psi\otimes\lvert 0\rangle{}+B\psi\otimes\lvert 1\rangle{}

$$

等距，当且仅当 $A^\dagger A\preceq I$。
可取 $B=(I-A^\dagger A)^{1/2}$，且该等距可在内部 ready 载体上补成酉。

**证明。**

标签正交使 $V^\dagger V=A^\dagger A+B^\dagger B$。
等距因此要求 $I-A^\dagger A=B^\dagger B\succeq0$。
反向取正平方根便得到等距，再补全输入、输出正交基即可酉扩张。

∎

对单位输入，成功与余量权重满足

$$

\|A\psi\|^2+\|B\psi\|^2=1.

$$

若 $I-A^\dagger A$ 有负方向，则保持这个 $A$ 和输入尺度的正余量补全不存在。
若另行缩放 $A$ 或改变对象的定义，已经是另一份关系合同。

#### 定理 5.2（共同线性、完整范数关系与酉性）

对复线性 $T:\mathbb C^d\to\mathbb C^e$，
全部输入范数保持、全部两输入内积保持、$T^\dagger T=I$ 三者等价。
当 $d=e<\infty$ 时等价于酉性。
在已校准正交基上，只需检验

$$

e_i,\qquad (e_i+e_j)/\sqrt2,\qquad(e_i+ie_j)/\sqrt2\quad(i<j)

$$

这 $d^2$ 个输入的范数，即可认证等距。

**证明。**

范数通过复极化恢复内积，内积条件给矩阵式。
有限检验中，基向量给 Gram 对角为一；实叠加给交叉实部为零；
虚叠加的输出范数平方为 $1-\Im\langle Te_i,Te_j\rangle$，给虚部为零。
方阵等距为满射，故酉。

∎

仅检查 $\Omega=\lvert 0\rangle{}$，矩阵 $A=\operatorname{diag}(1,2)$ 看起来保范数，
却不保全部输入。强行逐态归一的
$F_A(\psi)=A\psi/\|A\psi\|$ 也把 $\lvert 0\rangle{},\lvert +\rangle{}$ 的转移概率从 $1/2$ 改为 $1/5$。
但取 $K_s=A/2$、$K_f=\operatorname{diag}(\sqrt3/2,0)$，
便有 $K_s^\dagger K_s+K_f^\dagger K_f=I$；
成功分支归一后正是 $F_A$。它是带输入相关权重与失败记录的条件过程，不能删去这些量后改称确定性酉门。

> **白话图景。** 一个局部读出少了一部分，不一定是整个世界失去归一化。 若它是收缩的，可以把缺的部分作为另一个内部结果补回。 两部分一起保持关系，才得到整体等距与酉实现。 如果原作用已放大某个输入范数，就不能再用正的遗漏部分补成同一个守恒关系。

<a id="sec-6"></a>

## 6. 内部参考把局部正性接到完全正性，并选择酉旋转

#### 定义 6.1（固定共同参考接口）

对同一复线性目标过程 $\Lambda:M_d(\mathbb C)\to M_e(\mathbb C)$，
内部参考的作用被校准为恒等，联合规则为同一个 $\Lambda\otimes\operatorname{id}$。
若它对任意有限参考保持正性，称 $\Lambda$ 完全正（CP）。
参考可以全部在同一 $\Omega$ 内；其独立端口、准备和目标作用仍须由关系认证。

<a id="thm:choi"></a>

#### 定理 6.2（参考正性的有限完整证书）

采用未归一 Choi 矩阵

$$

J_\Lambda=\sum_{i,j}\Lambda(\lvert i\rangle{}\langle j\rvert{})\otimes\lvert i\rangle{}\langle j\rvert{}.

$$

则 $\Lambda$ CP 当且仅当 $J_\Lambda\succeq0$。
输入维数 $d$ 的内部参考已经足够。

**证明。**

若 CP，作用于 $\lvert \omega\rangle{}\langle \omega\rvert{}$，其中 $\lvert \omega\rangle{}=\sum_i\lvert ii\rangle{}$，
即得 $J_\Lambda\succeq0$。
反向分解 $J_\Lambda=\sum_\alpha f_\alpha f_\alpha^\dagger$，
按 $(K_\alpha)_{\mu i}=(f_\alpha)_{\mu i}$ 重排，比较矩阵块得
$\Lambda(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger$。
在任意参考上，每一项仍为正共轭，故完全正。

∎

保迹另要求 $\operatorname{Tr}_{\rm out}J_\Lambda=I_d$。
这是有限维的标准等价，项目 V58、$\Omega$ 与 Watrous 定理 2.22 均保留完整参考条件
[[5](#ref-v58), [7](#ref-omega), [9](#ref-watrous)]。

### 撤去参考条件的明确后果

转置 $T(X)=X^{\mathsf T}$ 在单系统上正、保迹、可逆，
并在纯态上保持射线转移概率。对内部 Bell 态

$$

\lvert \Phi\rangle{}=(\lvert 00\rangle{}+\lvert 11\rangle{})/\sqrt2

$$

却有

$$

\boxed{(T\otimes\operatorname{id})(\lvert \Phi\rangle{}\langle \Phi\rvert{})=F/2,}

$$

其中 $F$ 交换两个因子。对 $\lvert \psi_-\rangle{}=(\lvert 01\rangle{}-\lvert 10\rangle{})/\sqrt2$ 的期望为 $-1/2$。
这证明单系统正性没有保护与内部参考的共同关系。

若要作正迹三维定位，取正交单位向量

$$

u=\lvert 00\rangle{},\qquad
v=\frac{\sqrt3}{2}\lvert \psi_-\rangle{}+\frac12\lvert \psi_+\rangle{},
\qquad \lvert \psi_+\rangle{}=(\lvert 01\rangle{}+\lvert 10\rangle{})/\sqrt2.

$$

以 $u,v$ 为列的等距 $V$ 给

$$

V^\dagger(F/2)V=\begin{pmatrix}1/2&0\\0&-1/4\end{pmatrix},
\qquad
\frac{V^\dagger(F/2)V}{\operatorname{Tr}[V^\dagger(F/2)V]}
=\begin{pmatrix}2&0\\0&-1\end{pmatrix}
=\frac12(I+3\sigma_z).

$$

所以此候选的三轴为 $(0,0,3)$。这正是被否定的候选表，不能称为一种物理量子态。
原来的 $\lvert 01\rangle{},\lvert 10\rangle{}$ 二阶块迹为零，不能直接除迹；上述选择已处理这个边界。

<div tabindex="0" role="region" aria-label="可横向滚动的原稿比较图" style="overflow-x:auto;max-width:100%;">
<figure style="margin:16px 0;width:820px;">
<svg width="820" height="460" viewBox="0 0 820 460" role="img" aria-labelledby="bloch-title bloch-desc" style="max-width:none;font-size:16px;">
<title id="bloch-title">Bloch 球的 y=0 剖面</title>
<desc id="bloch-desc">原稿坐标：单位圆；x 轴从 −1.5 到 2；z 轴从 −1.4 到 3.5；点 (1,0,0)、原点、(0,0,3)；说明锚定于 (3,2.2)。每单位统一映为 82 像素。</desc>
<defs><marker id="bloch-arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0,0 L8,4 L0,8 Z" fill="#18354f"/></marker></defs>
<circle cx="180" cy="320" r="82" fill="#f3f5f6" stroke="#18354f" stroke-width="2"/>
<line x1="57" y1="320" x2="344" y2="320" stroke="#18354f" marker-end="url(#bloch-arrow)"/>
<line x1="180" y1="434.8" x2="180" y2="33" stroke="#18354f" marker-end="url(#bloch-arrow)"/>
<circle cx="262" cy="320" r="3" fill="#18354f"/><text x="270" y="340" fill="#18354f">(1,0,0)</text>
<circle cx="180" cy="320" r="3" fill="gray"/>
<circle cx="180" cy="74" r="3" fill="#9b3030"/><text x="190" y="80" fill="#9b3030">(0,0,3)</text>
<text x="355" y="326" font-style="italic">x</text><text x="176" y="20" font-style="italic">z</text>
<text x="426" y="139.6">图为 <tspan font-style="italic">y</tspan>=0 剖面。</text>
<text x="426" y="169.6">球内：合法标签比较。</text>
<text x="426" y="199.6">右端点：两端向量完全相同。</text>
<text x="426" y="229.6">球外：候选正性被反证。</text>
</svg>
</figure>
</div>

<a id="thm:so3"></a>

#### 定理 6.3（内部参考从三维对称中选出酉分支）

在已给 qubit Bloch 态域上，对 $O\in O(3)$ 定义唯一复线性、保自伴延拓

$$

\Lambda_O(I)=I,\qquad
\Lambda_O(\sigma_j)=\sum_iO_{ij}\sigma_i.

$$

则

$$

\boxed{\begin{aligned}
\Lambda_O\text{ 为 CP}&\iff\det O=+1\\
&\iff\Lambda_O=\operatorname{Ad}_U\quad\text{对某个 }U\in U(2).
\end{aligned}}

$$

这里不需要连续时间前提，也不需先假定逆过程 CP。

**证明。**

若 $\det O=+1$，三维正交矩阵有固定轴，限制在垂直平面上是角度 $\theta$ 的旋转。
取单位轴 $n$，令

$$

U=\cos(\theta/2)I-i\sin(\theta/2)n\cdot\boldsymbol\sigma.

$$

由 $(a\cdot\sigma)(b\cdot\sigma)=(a\cdot b)I+i(a\times b)\cdot\sigma$ 展开，得

$$

r'=\cos\theta\,r+\sin\theta(n\times r)
 +(1-\cos\theta)(n\cdot r)n.

$$

故 $\Lambda_O=\operatorname{Ad}_U$，于是 CP。
若 $\det O=-1$，令 $S=\operatorname{diag}(1,-1,1)$、$R=OS\in SO(3)$。
$S$ 对应转置，所以 $\Lambda_O=\operatorname{Ad}_U\circ T$。
若其 CP，复合 $\operatorname{Ad}_{U^\dagger}$ 就会使 $T$ CP，与 Bell 见证矛盾。
最后酉共轭给正向旋转，或由上述两分支排除得到所列等价。

∎

为何 $O(3)$ 是自然候选？已给的纯态射线重叠为 $\operatorname{Tr}(P_rP_s)=(1+r\cdot s)/2$，
其概率解释使用下一节的读出相容条件。
若全部射线重叠保持，三个正交轴的像仍正交；任意像对这些轴的三个分量等于原来的分量，
故必为 $r\mapsto Or$。单看球允许旋转与镜像；同一局域规则对参考的正扩展排除镜像。
全体表示同时复共轭仍可作为规范，不能与在固定参考下对一个子系统实施转置混为一谈。

### 二元最终见证没有消去较高参考资源

三维图可以定位最终负性，但准备检验它的关系可能需要更大的参考。
例如 $d=3$ 时

$$

\Lambda(X)=\frac{2\operatorname{Tr}(X)I_3-X}{5}

$$

保迹，且对二维参考保持正性，却不是 CP。
证明如下：写 Schmidt 分解 $\psi=\sum_{i=1}^r\sqrt{\lambda_i}\,a_i\otimes b_i$，$r\le2$，
其参考约化为 $\rho_R$。对任意 $z$，Cauchy--Schwarz 给

$$

|\langle\psi,z\rangle|^2
\le r\sum_i\lambda_i|\langle a_i\otimes b_i,z\rangle|^2
\le r\langle z,(I\otimes\rho_R)z\rangle.

$$

所以 $\lvert \psi\rangle{}\langle \psi\rvert{}\preceq r(I\otimes\rho_R)$。
故 $(\Lambda\otimes\operatorname{id}_2)(\lvert \psi\rangle{}\langle \psi\rvert{}) =[2I\otimes\rho_R-\lvert \psi\rangle{}\langle \psi\rvert{}]/5\succeq0$；
纯态生成正锥，得到二维参考正性。
而三维最大纠缠输入沿自身的输出期望为
$(2/3-1)/5=-1/15<0$。
因此不能把最终的两维压缩误读为所有过程只须 qubit 参考检验；项目 V59 也保留该层级 [[6](#ref-v59)]。

> **白话图景。** 单看一个三维球，镜像也能保留所有夹角。 把这个候选操作与同一个内部参考一起检查，才发现它不能保护共同正性。 这使“选择酉旋转”成为更大系统相容性的结论，而不是单靠球面形状作出的决定。

<a id="sec-7"></a>

## 7. 撤去读出加性：同一事件会因拆法不同而改变

#### 定义 7.1（完整效果粗粒化合同）

固定一次准备，效果域为 $0\preceq E\preceq I$。
一个完整上下文是有限列表 $(E_1,\ldots,E_n)$，其和为 $I$。
每个完整上下文的响应之和为一。
同一效果在不同上下文有同一响应；合并互斥结果时，效果与概率各自相加。
这里比较事件概率，不要求两台仪器有相同的条件态更新。

<a id="thm:coarse"></a>

#### 定理 7.2（粗粒化与有限加性等价）

完整效果上的非负响应满足上述合同，当且仅当

$$

p(I)=1,\qquad p(E+F)=p(E)+p(F)\quad(E,F\succeq0,\ E+F\preceq I).

$$

任何加性失败都有两个效果及共同余效果的有限见证。

**证明。**

比较 $(E,F,I-E-F)$ 与 $(E+F,I-E-F)$ 得必要性。
反向有限次合并给所有上下文的归一与粗粒化关系。

∎

### 逐表归一的幂规则反例

令 $t_i\ge0$、$\sum_i t_i=1$，逐表指定
$P_\beta(i)=t_i^\beta/\sum_jt_j^\beta$，$\beta>0$。
每张表都归一。但从 $(I/2,I/2)$ 变成 $(I/2,I/4,I/4)$ 后，
同一个未改变的效果 $I/2$ 的读数从 $1/2$ 变成

$$

\boxed{\frac1{1+2^{1-\beta}}.}

$$

两者相等当且仅当 $\beta=1$；例如 $\beta=2$ 给 $2/3$。
若原 $t$ 是振幅平方，额外振幅幂对应 $\beta=p/2$，故该合同只保留 $p=2$。
这个反例首先是事件细分问题，甚至不需相干叠加。

### 所有二结果都合法，仍可能在关系的关系处失败

对 qubit 效果 $E=aI+b\cdot\sigma$，定义

$$

p(E)=\begin{cases}a+b_z^3/|b|^2,&b\ne0,\\a,&b=0.\end{cases}

$$

合法效果满足 $|b|\le\min(a,1-a)$，所以 $p(E)\in[0,1]$。
该规则还有 $p(I-E)=1-p(E)$ 及合法正比例齐次性；故所有二结果 POVM 都归一。
在投影 $P_n=(I+n\cdot\sigma)/2$ 上，它就是项目 V52 的三次反例
$p(P_n)=(1+n_z^3)/2$ [[4](#ref-v52)]。
取

$$

n=(\sqrt3/2,0,1/2),\quad m=(-\sqrt3/2,0,1/2),\quad
E_1=P_n/2,\ E_2=P_m/2.

$$

则 $E=E_1+E_2=I/2+\sigma_z/4$，且

$$

\boxed{p(E_1)+p(E_2)=9/16\ne3/4=p(E).}

$$

共同余效果的读数为 $1/4$，所以三结果表总读数为 $13/16$。
这表明二元语法不等于只检查二结果互补归一。

#### 定理 7.3（完整响应与平方读出）

在有限维复效果域上，非负、单位归一、有限可加响应唯一具有

$$

p(E)=\operatorname{Tr}(\rho E),\qquad \rho\succeq0,\quad\operatorname{Tr}\rho=1.

$$

纯准备与秩一投影给 $p=|\langle\phi,\psi\rangle|^2$。

**证明。**

对正 $A$ 取整数 $m$ 使 $A/m\le I$，定义 $\ell(A)=mp(A/m)$。
共同整数倍与有限加性给良定义及正锥可加，正负差给 Hermitian 空间上的加性延拓。
对有理 $r>\|X\|$，序界 $-rI\le X\le rI$ 给 $|\ell(X)|\le r$，
进而有连续性与实线性。迹配对给唯一 Hermitian $\rho$，秩一非负性给 PSD，单位响应给迹一。
对两个秩一矩阵作迹配对即得平方。

∎

这是完整效果重建的有限维版本 [[4](#ref-v52), [5](#ref-v58), [11](#ref-busch)]。
以正算子值记录
$V\psi=\sum_i\sqrt{E_i}\psi\otimes\lvert i\rangle{}$ 实现一个完整测量时，
$V^\dagger V=\sum_iE_i=I$；合并记录投影直接给上述加性。
因此更大的内部记录结构为粗粒化相容提供明确的实现。

在维数至少二的已给内积空间中，若非负径向权重对正交合并可加且单位权重为一，
令 $F(t)=W(\sqrt t\,e)$，即有 $F(s+t)=F(s)+F(t)$。
非负性给单调性，有理夹逼给 $F(t)=t$，所以 $W(v)=\|v\|^2$。
平方由这项关系闭合选出；一般加乘语法或逐表归一单独不承担同样工作 [[3](#ref-v49), [4](#ref-v52)]。

> **白话图景。** 一个事件没有变，只把旁边的结果拆得更细，它的概率不应改变。 若改变，就说明那些概率表没有组成同一套读出关系。 把记录合并、细分和同一效果的辨认一起放进整体，才能把概率形式锁定。

<a id="sec-8"></a>

## 8. 共同复定向属于怎样的更大结构：闭路与双覆盖

项目 V58 的局部实关系代数先由三轴 Clifford 关系锁成 $M_2(\mathbb C)$。
在这个中心内，平方为 $-1$ 的元素只有 $\pm J$。
因此以下符号模型适用于已作这种局部识别的定向比较，
不适用于任意实内积空间中的全部可能复结构 [[5](#ref-v58), [6](#ref-v59)]。

#### 定义 8.1（半线性内部比较图）

连通图顶点 $v$ 带正交复结构 $J_v$。
每条边 $e:v\to w$ 有实等距可逆比较 $T_e$，满足

$$

T_eJ_v=\varepsilon_eJ_wT_e,\qquad \varepsilon_e\in\{+1,-1\}.

$$

反向边取逆，符号相同。这里比较接口不自动是固定复编码上的可实施局域量子门。

<a id="thm:orientation"></a>

#### 定理 8.2（共同定向的闭路判据）

重标记 $J'_v=\eta_vJ_v$，$\eta_v=\pm1$，使全部边成为复线性，
当且仅当每个闭路 $C$ 满足

$$

\boxed{\prod_{e\in C}\varepsilon_e=+1.}

$$

连通图的定向选择只差全体同时翻转。

**证明。**

边符号变为 $\varepsilon'_e=\eta_v\varepsilon_e\eta_w$。
若全部为正，沿闭路的端点符号相消，得必要性。
反向选根，在一棵生成树上用路径符号积定义 $\eta_v$；
闭路条件使非树边也相容。两组解之比沿每条边恒定，连通性给整体 $\pm1$。

∎

奇符号闭路给 $T_CJ_v=-J_vT_C$。
它首先表示绕路后留下反线性取向，不是无条件矛盾。
若又要求这个同历史闭路 $T_C=I$，或要求它复线性且可逆，才发生冲突。
全体共同翻转是表示规范；与对固定参考下单个子系统施加转置是不同问题。

#### 命题 8.3（记录一位取向的内部扩张）

把顶点扩为 $(v,s)$，$s=\pm1$，令 $J_{(v,s)}=sJ_v$；
把边提升为

$$

(v,s)\longrightarrow(w,\varepsilon_es).

$$

沿边仍用 $T_e$，则所有提升边均与复结构相容。

**证明。**

$T_eJ_{(v,s)}=s\varepsilon_eJ_wT_e =J_{(w,\varepsilon_es)}T_e$。

∎

这是取向双覆盖。奇闭路从 $(v,s)$ 走到 $(v,-s)$，
不再被误认成同一提升顶点的返回。
该扩张明确保留了原标签省略的一位信息，
不证明宇宙有两层，也不把反酉自动变成原系统的确定性 CP 门。

> **白话图景。** 每一处都能选自己的左右手约定，但沿不同路径比较，最终必须知道是否回到同一约定。 共同复结构要求闭路上这些选择能够接起来。 若绕一圈翻了方向，可以先把被遗漏的取向记录补入更大结构，再判断原来的“同一个点”是否确实应该等同。

<a id="sec-9"></a>

## 9. 把反向见证接到项目原生 AURIC 五模式

以下直接采用 V37 定义 3.1 的固定码，模式顺序为 $(0,2,3,5,25)$。
令

$$

\nu=(1+2\sqrt3+\sqrt{11})^{-1},\qquad
a_\nu=\nu(\sqrt3+\sqrt{11})/2,\qquad u_0=(a_\nu,a_\nu,\nu).

$$

该码的固定五效果为

$$
\begin{aligned}
E_{25}&=\tfrac\nu2(\sqrt3 I-\sigma_x-\sigma_y-\sigma_z),&E_0&=3E_{25},\\
E_2&=\tfrac\nu2(\sqrt{11}I+3\sigma_x+\sigma_y+\sigma_z),\\
E_5&=\tfrac\nu2(\sqrt{11}I+\sigma_x+3\sigma_y+\sigma_z),&E_3&=\nu(I+\sigma_z).
\end{aligned}
$$

各效果正且秩一，和为 $I$。
对归一态 $\rho=(I+r\cdot\sigma)/2$，令 $p_s=\operatorname{Tr}(\rho E_s)$，
$X=p_2+p_{25}$、$Y=p_5+p_{25}$、$Z=p_3$。
等距编码将这些原占据均值标定为

$$

\boxed{(X,Y,Z)=u_0+\nu(x,y,z).}

$$

这是原金字塔内的指定球族，三个占据读口仍是同一个五结果测量的兼容读数，
不是三个同时尖锐 Pauli 测量 [[2](#ref-v37)]。

#### 推论 9.1（关系余量直接进入原三轴）

将定理 [2.1](#thm:comparison) 的标签态送入上述固定码，则

$$

\boxed{\|(L-R)\psi_w\|^2
=s\left(1-\frac{X-a_\nu}{\nu}\right),\qquad
p_-=\frac12\left(1-\frac{X-a_\nu}{\nu}\right).}

$$

完整比较关系仍由三个标定均值与尺度 $s$ 保存。

**证明。**

代入 $x=(X-a_\nu)/\nu$；其余坐标由同一仿射式恢复。

∎

对未归一 Hermitian 候选 $G$，令

$$

w_s=\operatorname{Tr}(GE_s),\quad N=\operatorname{Tr} G,\quad
X=w_2+w_{25},\quad Y=w_5+w_{25},\quad Z=w_3,\quad \kappa=w_{25}.

$$

这些同尺度矩对任意 Hermitian $G$ 都满足项目的线性恒等式

$$

\boxed{N-X-Y-Z-2\kappa=0,}

$$

而候选 $G$ 正半定，当且仅当还满足球锥条件

$$

\|(X-a_\nu N,Y-a_\nu N,Z-\nu N)\|_2\le\nu N,\qquad N\ge0.

$$

线性式给指定码内的四推一，球锥则另行承担正性。
一般五事件族没有自动满足这个码条件，三个均值之外仍有 $\kappa$ 纤维 [[1](#ref-v17), [2](#ref-v37)]。

<a id="prop:fivecounter"></a>

#### 命题 9.2（五概率与四推一都合法，仍可能不在量子球内）

取 Hermitian 候选

$$

W=\tfrac12(I+\tfrac32\sigma_z)
=\operatorname{diag}(5/4,-1/4).

$$

令 $p_s=\operatorname{Tr}(WE_s)$。则

$$
\begin{aligned}
p_{25}&=\tfrac\nu2(\sqrt3-3/2)>0,&p_0&=3p_{25},\\
p_2&=p_5=\tfrac\nu2(\sqrt{11}+3/2)>0,&p_3&=5\nu/2>0.
\end{aligned}
$$

全部五概率非负、和为一，四推一线性式成立，但不存在具有这些码内三轴的正 qubit 态。

**证明。**

直接作 Pauli 迹配对得到所列数；其和为
$\nu(1+2\sqrt3+\sqrt{11})=1$。
由 $p_0=3p_{25}$ 得线性式。
三轴反演却唯一给 $r=(0,0,3/2)$，球条件失败；
额外效果 $\lvert 1\rangle{}\langle 1\rvert{}$ 在 $W$ 上给 $-1/4$。

∎

这组五标签经典分布本身合法；失败的是将它解释为同一指定 qubit 接口的完整正响应。
它具体体现 V59 的区分：有限读数可以重建已知模型内的态，
但有限菜单的逐项非负并不单独认证整个正态类 [[6](#ref-v59)]。
同样，V37 §12 证明：本码内每个酉都有可逆仿射概率更新；
若另要求同一个非负随机矩阵作用于整个五标签单纯形，则只有标量相位门满足。
因此反向研究也可能识别一个应当放弃的额外经典闭合要求，而不是增添一个量子公理。

> **白话图景。** AURIC 的三轴可以成为精确比较工具，但必须使用同一个码和同一把尺度。 五个数都正、总和为一、还满足四推一，仍不代表它们已通过整个量子关系网的检查。 球面约束、相干关系和后续读口规定它们属于哪一种共同结构。

<a id="sec-10"></a>

## 10. 从有限三维比较到整体法则：同源覆盖与稳定界

设 $r=L-R$ 为有界算符差，在所声明的循环生成空间上工作。
若 $r\pi(w)\Omega=0$ 对全部历史词成立，则线性性与连续性使它在该闭包上为零。
因此法则失败有某个同源上下文见证，而不需要更换本体。
一般无界表示只在声明的共同代数定义域上作同样结论。

<a id="thm:stability"></a>

#### 定理 10.1（满锚覆盖的三维余量界）

设 $\xi_j=\pi(b_j)\Omega$ 构成有限声明空间 $\mathcal K$ 的一个基，
Gram 为 $G\succ0$，$\gamma=\lambda_{\min}(G)>0$。
对 $L\xi_j,R\xi_j$ 的比较得尺度 $s_j$ 与坐标 $x_j$，零尺度贡献取零。
则限制在 $\mathcal K$ 上有

$$

\boxed{\|(L-R)|_{\mathcal K}\|^2
\le\frac{\sum_j s_j(1-x_j)}\gamma
=\frac{2\sum_j s_jp_{-,j}}\gamma.}

$$

若 $F_{ij}=\langle r\xi_i,r\xi_j\rangle$，更精确地

$$

\|r|_{\mathcal K}\|^2=\sup_{c\ne0}\frac{c^\dagger Fc}{c^\dagger Gc}.

$$

**证明。**

输入 $\sum_jc_j\xi_j$ 及输出的范数平方分别为 $c^\dagger Gc$、$c^\dagger Fc$。
由 $F\succeq0$ 和 $G\succeq\gamma I$，最大比值不超过 $\operatorname{Tr} F/\gamma$。
而定理 [2.1](#thm:comparison) 给 $F_{jj}=s_j(1-x_j)=2s_jp_{-,j}$。

∎

所以整个声明空间上的等式成立，当且仅当每个锚满足：
两端同为零，或 $s_j>0$ 且比较点为 $(1,0,0)$。
只有根检验不够：$\Omega=\lvert 0\rangle{}$、$r=\lvert 1\rangle{}\langle 1\rvert{}$ 时 $r\Omega=0$，
但 $r\sigma_x\Omega=\lvert 1\rangle{}$。
没有满覆盖，结论只控制已覆盖子空间；丢掉尺度不能控制绝对误差；
锚近线性相关使 $\gamma$ 小，认证会变差。

负性也有简单稳健界：若 $\|M-\widehat M\|\le\delta$，
单位 $w$ 满足 $w^\dagger\widehat Mw=-\eta$，则
$w^\dagger Mw\le-\eta+\delta$。
只有 $\eta>\delta$ 才保证真表负性。小正主元的 Schur 消元可能病态，
精确关系与噪声稳定性不能互相替代。

> **白话图景。** 每次三维比较只检查一个方向。 若内部参考已覆盖全部声明方向，这些比较就能合成一个整体误差界。 参考是否足够分开、尺度是否保留，决定“看起来差不多”能否提升为可靠的整体结论。

<a id="sec-11"></a>

## 11. 更简洁的关系形式，以及本轮真正锁定了什么

保留前稿的同源正关系体

$$

\mathfrak R=(\mathcal A,\ell),\qquad
\mathcal A=\mathbb R\langle S,S^*\rangle/\mathcal I,

$$

其中 $\ell(1)=1$、$\ell(a^*a)\ge0$，
并在项目明确的局部 Clifford 与共同复定向条件下使用相应复表示。
所有准备、参考、记录和比较程序都属于该同一结构；来源为其循环表示的 $\Omega=[1]$。
内部比较的数学存在、实际菜单供应与经验识别须使用同一份接口合同。

> **编者纸面校核注（实正响应与循环表示）。** 此处沿用不可变 v76 原稿“共同正响应”的完整定义：实数情形还要求 $\ell(a^*)=\ell(a)$。仅有实线性、$\ell(1)=1$ 与 $\ell(a^*a)\ge0$ 并不保证伴随对称；V58 §5 命题 5.2 后的原例为实代数 $\mathbb C$ 上 $f(x+iy)=x+cy$，$c\ne0$。因此本段的循环内积与来源 $\Omega=[1]$ 使用该 Hermitian 条件；一般代数的左乘表示先在共同代数定义域上成立，有界延拓须另有有界性条件。原段落及其正性式完整保留。依据：不可变 v76 原稿“共同正响应”定义与正响应保守扩展证明，以及固定 V58 §§5、7。

#### 定理 11.1（本轮的反向定位与关系闭合）

在上述各节声明的对象类和接口下，有以下条件结论：

1. Hermitian 单位响应的整体正性，等价于全部可缩放合成二元正迹表的球内条件。
2. 一个算符等式在有限声明空间成立，等价于覆盖该空间的每个同源锚，其两端同为零，或其非零尺度比较达到相等目标点；误差受定理 [10.1](#thm:stability) 控制。
3. 局部线性分支可由正的内部余量补成等距，当且仅当它是收缩；同维完整线性范数保持给酉。
4. 完整参考下的正作用等价 CP；对 Bloch 正交候选，它进一步等价于正向旋转及酉共轭。
5. 效果的细分／合并相容给完整有限加性，进而给 Born 迹响应；已校准复定向的全局粘合则由闭路符号判定。

**证明。**

依次由定理 [3.2](#thm:binarypositive)、[2.1](#thm:comparison) 与 [10.1](#thm:stability)、
[5.1](#thm:completion)、[6.2](#thm:choi) 与 [6.3](#thm:so3)、
[7.2](#thm:coarse) 及 [8.2](#thm:orientation) 得到。
各结论保留其前件，不能将某节的候选对象自动当成另一节已经合法的物理态。

∎

<div tabindex="0" role="region" aria-label="原稿表格" style="overflow-x:auto;max-width:100%;">

|待解释条件|撤去后的明确见证|所属的更大关系|
|---|---|---|
|整体正性|合成二元块球外、Schur 支持或余量失败|全部历史组合的共同正核。|
|封闭门的酉性|交叉关系改变或范数缺口|共同线性输入与全部内部记录的等距关系。|
|完全正性|内部关联参考上的负权重|同一目标规则对保留参考的正扩展。|
|平方读出|同一效果因细分而改值|效果分解、合并与正响应的共同闭合。|
|共同复定向|负符号闭路|局部中心、比较路径和取向记录的一致性。|
|全局法则认证|根检验通过、后续历史失败|同源锚覆盖、接续闭合及条件数。|

</div>

于是可用下面一句话组织量子关系重建：

$$

\boxed{\text{同源关系在合成、细分、比较及内部参考扩展中保持正归一相容。}}

$$

这是一种结构化表述，不是仅凭字面便确定模型的单一无前件公理。
局部代数、共同复结构、复合方式、完整响应与实际覆盖的内容仍须明确。
把这些要求内生化，不等于已经从更弱背景证明它们全部必然成立；
本轮给出了哪些要求等价、哪些失败可定位、哪些缺口可以补全的精确边界。
同一个实际 $\Omega$ 可以始终固定；多种满足部分约束的数学模型表示当前描述尚未锁定的部分，
不要求另设多个实际本体。

> **白话图景。** 整个图景始终围绕同一个 $\Omega$。 我们让它生成两段可以比较的内部历史，看看本来声称相同的东西是否真的相同。 局部比较能放到受限三维中，尺度和偏移说明余量；把参考、记录与相干关系补齐，再检查整张网是否共同成立。 少了一条分支，可以在条件允许时把它补回；负的完整关系不能靠升维掩盖；绕路翻了定向，就要记录取向或重新检查路径等同。 观察者自己的预测与校准也在这张网中。 公理因此逐步显出它保护的整体关系：线性怎样与归一共同成立、为什么完整相容读出为平方、为什么局部门必须能与其他内部角色共同存在。

## 固定来源与参考文献

<a id="ref-v17"></a>

**[1]**  项目固定提交。
[V17：加乘、对数与量子勾股几何](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)，
本轮使用 §§3--4、9 与命题 13.3 的相关定义、证明及范围。

<a id="ref-v37"></a>

**[2]**  项目固定提交。
[V37：二元关系的酉表示与黄金门通用性](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)，
本轮完整读取 §§1--6、12；不认证后续全部原生控制供应链。

<a id="ref-v49"></a>

**[3]**  项目固定提交。
[V49：加乘指数、二次关系闭合与归一化升维](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md)，§§3--5。

<a id="ref-v52"></a>

**[4]**  项目固定提交。
[V52：纯态商几何、二次关系生成与无损递归](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)，§§2--7。

<a id="ref-v58"></a>

**[5]**  项目固定提交。
[V58：关系公理、共同复相位与条件量子重建](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md)，§§2--8、10--14。

<a id="ref-v59"></a>

**[6]**  项目固定提交。
[V59：局部层析、相干读出轨道与正性起源](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md)，
§1.2、§§2--5、§10 的所用段；未认证后续全部实际菜单供应。

<a id="ref-omega"></a>

**[7]**  项目固定提交。
[$\Omega$ 静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，
§§1--8、12 的共同实现与有限协议条件。

<a id="ref-v76"></a>

**[8]**  本对话前稿。
*加乘生成、二次关系网与内生量子结构*，v76.0，2026 年 11 月 1 日。
对话交付稿，不冒称仓库原生文件。

<a id="ref-watrous"></a>

**[9]**  John Watrous.
*The Theory of Quantum Information*. Cambridge University Press, 2018.
[作者公开第 2 章](https://jhwatrous.github.io/TQI.2.pdf)，
本轮核对定理 2.22、保迹／等距条件及转置例的相关段落；不声称阅读全书。

<a id="ref-schur"></a>

**[10]**  Jean Gallier.
[*The Schur Complement and Symmetric Positive Semidefinite (and Definite) Matrices*](https://www.cis.upenn.edu/~jean/schur-comp.pdf),
2019 年 8 月 24 日稿，定理 4.3 及其支持条件、完成平方的相关段落。
本文给出复 Hermitian 有限维证明。

<a id="ref-busch"></a>

**[11]**  Paul Busch.
*Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem*.
Phys. Rev. Lett. 91, 120403 (2003).
[arXiv:quant-ph/9909073](https://arxiv.org/pdf/quant-ph/9909073)。
前轮已核完整效果条件与证明；本稿给有限维自足版本。

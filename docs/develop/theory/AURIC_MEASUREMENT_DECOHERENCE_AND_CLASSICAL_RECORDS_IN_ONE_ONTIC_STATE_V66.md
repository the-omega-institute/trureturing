<details>
<summary>原稿前导、生产设置与元数据（逐字保留）</summary>

<div style="overflow-x:auto;max-width:100%">

```latex
% !TeX program = xelatex
% Compile twice with XeLaTeX. Optional: \def\AURICFontPath{/absolute/font/path/}
% Paper mathematics only. Programs were used only for sources, authoring and PDF QA.
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
\hypersetup{pdftitle={AURIC v66：同一本体中的测量、退相干与经典记录},
pdfauthor={AURIC research continuation},
pdfsubject={One ontic state, endogenous gates, conditional collapse, classical records and conditional quantum reconstruction}}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\id}{\operatorname{id}}
\newcommand{\Ad}{\operatorname{Ad}}
\newcommand{\Var}{\operatorname{Var}}
\newcommand{\supp}{\operatorname{supp}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\TV}{d_{\mathrm{TV}}}
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
\fancyhead[L]{\small AURIC：测量、退相干与经典记录}
\fancyhead[R]{\small v66 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
```

</div>

</details>


> **原稿归属与转换范围（Markdown 编者；不属原稿）。** 前导中“Programs were used only for sources, authoring and PDF QA”以及正文和文献中的“本轮”“实际核读”、源码请求、方法与阅读报告均保留为原作者的历史记述；这些话不表示本次转换者执行了相同活动。本稿只作纸面数学、来源与本地阅读呈现的核对，不构成形式核验、原生控制取得、物理或经验认证、全上游认证、无条件起源、最小性或优先权证明。


<details>
<summary>原稿标题生产设置（逐字保留）</summary>

<div style="overflow-x:auto;max-width:100%">

```latex
\begin{center}
{\LARGE\bfseries\color{auricblue} 同一本体中的测量、退相干}\\[6pt]
{\LARGE\bfseries\color{auricblue} 与经典记录}\\[8pt]
{\large 从 $\Omega$ 的内生门序列到条件确定性与量子公理的结构来源}\\[6pt]
AURIC 量子起源研究\quad 定义、定理与纸面证明\quad v66.0\\[4pt]
2026 年 11 月 1 日\quad Asia/Singapore
\end{center}
```

</div>

</details>

# 同一本体中的测量、退相干<br>与经典记录

从 $\Omega$ 的内生门序列到条件确定性与量子公理的结构来源

AURIC 量子起源研究　 定义、定理与纸面证明　 v66.0

2026 年 11 月 1 日　 Asia/Singapore
## 摘要
本文把用户提出的“每一个门也是同一本体的读出”和“测量使关系稳定到唯一值”
分别写成内部记录控制的整体酉与交换记录代数上的条件求值。
对唯一固定 $\Omega$，测量权重、投影、完整记录历史及条件态都可由实际门积和记录投影表达，
无需增加本体外的观察者。校准耦合、完整酉扩张与条件归一化给出一般仪器，
无扰信息复制要求所区分的稳定态正交。
退相干通过内部环境重叠压低局部交叉块；已知记录后的条件态在记录代数上具有零方差，
但完整观察者仍可保留非交换自由度。
在重复非破坏测量中，本文给出同一有限深度上界，同时控制局部退相干距离与后验判别误差；
再以相位型读口证明完全退相干可以伴随零标签信息。
通过项目固定五效果编码，非选择退相干对应 AURIC 球内横向相干收缩，条件选支对应指针极点。
最后区分平方权重的细化相容前提、正关系代数的 GNS 表示，以及尚未由这些定理给出的全局单结果选择。
这是一组条件性重构与定量补充；标准测量理论和项目已有结果均予以归属，不作新颖性优先权主张。


<a id="section-1"></a>

## 1 来源范围与本轮研究判断


> **历史来源报告归属（Markdown 编者；不属原稿）。** 本节的 2026-11-01 15:52:15 socket 权限拒绝、未取得新提交、未重试活动 HEAD、30 份 Git blob 身份及重点阅读范围，是原作者报告；其中 socket 权限拒绝既不是 HTTP 403，也不是自动审批拒绝。本次转换不把这些历史报告计作自己的访问、阅读或验证。


本轮唯一活动源码请求于新加坡时间 2026-11-01 15:52:15 因网络 socket 权限被拒绝，
未取得新提交；这不是上一轮的 HTTP 403，也不是自动审批拒绝。
未重试活动 HEAD，以下全部项目引用固定于已核验提交


<code>5cf95e1a<wbr>e01f7ed8<wbr>6735c04a<wbr>d8d752cb<wbr>19b1a58b</code>。


本轮核对 30 份保留原文的 Git blob 身份，不将字节核对称为全库数学认证。
实际重点阅读 V18 §§4、8.1–8.3、9；V30 §§2–3、6、12 的相关段落；
稳定记录 V31 §§5–8；V37 §3；V42 的模式字典；V58 §11；V59 §7.1。
仅据这些固定原文陈述项目承接，不宣称验证了该提交以后的进展。[[1](#bib-head)]

项目已有三条可接合的链：V18 给出条件塌缩、环境谱矩和新记录乘积退相干；
V30 给出同一 $\omega$ 的关系化读出、内生程序、记录充分辨识的二值极限判据及 QND 的 KL 率；
稳定记录 V31 给出完整仪器误差下的长期条件极化。[[2](#bib-v18), [4](#bib-v30), [5](#bib-v31)]
v65 已进一步区分忠实过程表示、实际共同过程与必须保留的量子记忆。

> **V65 引用身份（Markdown 编者；不属原稿）。** 此处及 §8.2 的 v65 指已发表的 [《忠实内部关系与量子过程重构》原 Markdown](https://github.com/the-omega-institute/trureturing/blob/7e7589190a69e0fb071e54dc79292c055709e579/docs/develop/theory/AURIC_FAITHFUL_INTERNAL_RELATIONS_AND_QUANTUM_PROCESS_RECONSTRUCTION_V65.md)，固定提交 <code>7e758919<wbr>0a69e0fb<wbr>071e54dc<wbr>79292c05<wbr>5709e579</code>，尤其 §§9–10 的共同记忆、完整报告及半 diamond 组合界。它是独立于上列固定项目快照的前稿来源；原文献表十六项保持原样。


本轮将这些结构接成一条完整测量解释，并补明有限深度的共同误差界。

本文的主要判断为：<strong>测量后的“唯一值”可以严格成立于已知记录的相容读出上；
单靠局部退相干或记录稳定性，不能把同一个完整酉态中的所有其他记录分量判为消失。</strong>
这里没有预先选择多世界、隐变量或客观塌缩解释；所有分量首先只是同一个向量的数学分解。


<a id="section-2"></a>

## 2 唯一 $\Omega$、内生程序与门的关系态


#### 定义 2.1（固定本体与完整门积）


固定一个单位向量 $\Omega\in\mathcal H$，定义实际门积和完整观察者态


$$
G_k=U_k\cdots U_1,\qquad \Psi_k=G_k\Omega.
$$


全部程序、环境、参考、记忆、工作区和读口都属于同一完整载体。
以下张量因子是已经声明的内部接口，约化态只表示其中一组可访问读出。
对门的全部接口输入作校准量化，不意味着另选一个实际宇宙。


#### 定理 2.2（记录读出驱动的整体酉）


设程序接口的非零投影 $Q_r$ 两两正交、和为单位，数据接口上的 $V_r$ 均为酉。
则


$$
\mathcal U=\sum_rQ_r\otimes V_r
$$


是整体酉，并保持每个程序投影 $Q_r\otimes I$。
因此门标签 $g(r)$ 可以是此前内部记录的函数，实际执行关系可写成此类相干控制。


**证明。**


正交性给


$$
\mathcal U^\dagger\mathcal U
=\sum_{r,s}Q_rQ_s\otimes V_r^\dagger V_s
=\sum_rQ_r\otimes I=I,
$$


反向乘积相同。与程序投影的对易性逐项成立。
在程序叠加上，作用为 $\sum_rc_r|r\rangle V_r\psi$，仍是线性的完整态。


∎


这是 V30 §6 与 V57 §2 的内部控制语义。

> **控制和的拓扑与接口范围（Markdown 编者；不属原稿）。** 定理 2.2 的有限程序分割按有限和计算。若另取可数完备正交分割，和为单位及受控算子和按强算子拓扑（等价地，正交直和）理解；对每个向量，其正交分量的平方范数可求和，逐块逆为相应伴随，故仍得到酉。非零正交块的尾部一般不在算子范数中趋零。该数学扩张不供应无限程序、准备或记录的物理容量；有限维数据、有限 Kraus/记录与有限轮公式仍按各段声明使用。

[[4](#bib-v30), [9](#bib-v57)]
它精确保留了“门的选择来自 $\Omega$ 的此前读出”的含义。
但标签、门的关系态表示与执行算符有不同类型；只给出一个实际末态也不唯一确定门字。
例如所有 $\operatorname{diag}(1,e^{i\theta})$ 都固定 $|0\rangle$。
固定处理器的耦合及程序译码规则仍是模型结构，不能从本体唯一性独自读出。


#### 命题 2.3（可表示门不等于可直接执行门）


令 $D=\operatorname{diag}(s_i)>0$、$\operatorname{Tr} D=1$，
$|\gamma_D\rangle=\sum_i\sqrt{s_i}|ii\rangle$。
忠实关系态 $|V\rangle_D=(I\otimes V)|\gamma_D\rangle$ 可表示酉通道，
但通常不能充当同一固定处理器的精确确定性程序。


**证明。**


若一个固定等距处理器对所有数据输入满足
$W(\psi\otimes p_j)=V_j\psi\otimes q_j$，保存交叉内积给


$$
\langle p_j,p_l\rangle I
=\langle q_j,q_l\rangle V_j^\dagger V_l.
$$


若 $V_j,V_l$ 不只相差整体相位，右侧重叠必须为零，输入程序也正交。
即使起初只要求数据的纯输出为 $V_j\psi$，整体纯性先给乘积输出；
对基向量叠加使用线性性，残余 $q_j$ 便与 $\psi$ 无关。
另一方面，$\langle U|V\rangle_D=\operatorname{Tr}(DU^\dagger V)$ 通常不为零。
取 $D=I/2$、$U=I$、$V=e^{i\theta\sigma_z}$、$0<\theta<\pi/2$，
两关系态重叠为 $\cos\theta\ne0$，但通道不同。


∎


程序正交性是标准 Nielsen–Chuang 定理，项目 V30 已有相应证明。[[13](#bib-nielsen), [4](#bib-v30)]
它要求精确、确定性、共同处理器和全部数据输入；不禁止近似门集或可报告失败的方案。
单份关系态也不提供一次读出即可完成层析的能力。


<a id="section-3"></a>

## 3 把投影、条件塌缩与一般测量全部写回 $\Omega$


#### 定义 3.1（记录相对态）


设 $\{Q_r\}$ 是时刻 $k$ 的实际完整记录投影分割。令


<a id="eq:omegaweight"></a>


$$
\begin{aligned}

\widehat Q_{k,r}&=G_k^\dagger Q_rG_k,\\
p_k(r)&=\|Q_rG_k\Omega\|^2
=\langle\Omega,\widehat Q_{k,r}\Omega\rangle.

\end{aligned}
$$


（2）


对 $p_k(r)>0$ 定义


<a id="eq:collapse"></a>


$$
\boxed{
\Psi_{k\mid r}=\frac{Q_rG_k\Omega}{\sqrt{p_k(r)}},\qquad
\omega_{k\mid r}(A)=
\frac{\langle\Omega,G_k^\dagger Q_r A Q_rG_k\Omega\rangle}{p_k(r)}.}
$$


（3）


零质量分支不作归一化。

> **条件读出的算子域（Markdown 编者；不属原稿）。** 式（3）中的 $A$ 及正性检验中的 $B$ 取完整 Hilbert 接口上的有界算符；这里没有为任意无界算符补入定义域、可积性或条件期望结论。完整载体可以无限维，有限记录分割的酉拉回和向量态公式仍成立；若另用可数记录分割，完备和按强算子拓扑理解，概率和由向量态的单调连续性取得。

这里先使用既有平方权重接口；第 [9](#sec:born) 节说明可替换的权重前提。


#### 命题 3.2（条件归一化与同一本体）


$\{\widehat Q_{k,r}\}$ 仍是完整正交投影分割，$p_k(r)\ge0$、$\sum_rp_k(r)=1$，
而 $\omega_{k\mid r}$ 是正归一态。式 [（3）](#eq:collapse) 不需要 $\Omega$ 的内部因子独立。


**证明。**


酉共轭保持投影、正交性与和。平方范数正性及分割给归一化。
对任意 $A=B^\dagger B$，式 [（3）](#eq:collapse) 的分子是
$\|BQ_rG_k\Omega\|^2$；取 $A=I$ 给一。


∎


式 [（3）](#eq:collapse) 是明确的条件塌缩公式。
完整态仍由 $G_k\Omega$ 描述；分母把“已知记录 $r$”的相对描述重新归一化。
在记录的对易读出上，这是普通条件概率；对不对易的后续量，它对应指定投影后的条件状态。
不能把该状态用于替代需要重新干涉不同记录的完整相干过程。


<a id="section-3.1"></a>

### 3.1 基底怎样进入门序列


若实际基底 $|b_a\rangle=B|a\rangle$ 由内部程序指定，
其投影为 $P_a=B|a\rangle\langle a|B^\dagger$。对纯系统输入 $\psi$，


$$
p(a)=\|P_a\psi\|^2=|\langle a|B^\dagger\psi\rangle|^2,
\qquad
\psi_{\mid a}=\frac{P_a\psi}{\sqrt{p(a)}}.
$$


可先实施 $B^\dagger$，把计算标签复制到内部记录，再实施 $B$ 恢复基底约定。
若系统与其余完整观察者纠缠，使用 $(P_a\otimes I)\Psi_k$ 即可；
不能总把该内部系统写成一个独立纯 $\psi$。


#### 定理 3.3（测量耦合与 Kraus 完整性）


在实际有限维共同接口上，假设辅助记录确已准备为与输入独立的 $|0\rangle_M$，
且整体耦合 $W$ 对保留的内部参考实行同一个局域过程。
取辅助正交基 $|r,\alpha\rangle$，定义


$$
K_{r\alpha}=(I\otimes\langle r,\alpha|)W(I\otimes|0\rangle).
$$


则


<a id="eq:complete"></a>


$$
\begin{aligned}

W(\psi\otimes|0\rangle)
 &=\sum_{r,\alpha}K_{r\alpha}\psi\otimes|r,\alpha\rangle,\\
\sum_{r,\alpha}K_{r\alpha}^\dagger K_{r\alpha}&=I,\\
\mathcal I_r(\rho)&=\sum_\alpha K_{r\alpha}\rho K_{r\alpha}^\dagger,\qquad
\rho_{\mid r}=\frac{\mathcal I_r(\rho)}{\operatorname{Tr}\mathcal I_r(\rho)}
\quad\bigl(\operatorname{Tr}\mathcal I_r(\rho)>0\bigr).

\end{aligned}
$$


（5）


每支完全正，和保持迹；反之，满足式 [（5）](#eq:complete) 的族给出一个等距扩张，
在足够的实际内部 ready 容量上可以延拓为整体酉。


**证明。**


将 $W$ 沿辅助完整基展开，内积守恒给式 [（5）](#eq:complete)。
对任何保留参考 $R$，每项 $(I_R\otimes K)X(I_R\otimes K^\dagger)$ 保持正性，
所以完全正；迹循环性给总保迹。
反向令 $V\psi=\sum_{r,\alpha}K_{r\alpha}\psi\otimes|r,\alpha\rangle$，
则 $V^\dagger V=I$；补齐有限维正交基可在共同足够载体上延拓为酉。


∎


归一化在这里是算子恒等式 [（5）](#eq:complete)，不只是一份实际数据的标量和为一。
未归一分支对 $\rho$ 线性，除以分支质量的条件更新通常非线性；
后者不把完整门变成非线性动力学。
V58 §11 已明确上述 ready 和共同参考条件，不能由 $\|\Omega\|=1$ 自动补齐。[[10](#bib-v58), [12](#bib-omega)]
若内部记忆与输入已有相关且将来重新参与，须保留它；实际条件公式 [（3）](#eq:collapse)
仍成立，但不能无条件压成同一个系统单独的通道。


<a id="section-3.2"></a>

### 3.2 一段能逐门写出的测量


在同一个 $\Omega$ 的某已准备切面，设


$$
G_k\Omega=(\alpha|0\rangle+\beta|1\rangle)_S|0\rangle_M|0\rangle_E,
\qquad |\alpha|^2+|\beta|^2=1.
$$


省略的其余因子在此例中固定。依次实施


$$
W=\mathrm{CNOT}_{M\to E}\,\mathrm{CNOT}_{S\to M},
\qquad WG_k\Omega=\alpha|000\rangle+\beta|111\rangle.
$$


读记录 $M$ 得到 $p(0)=|\alpha|^2$、$p(1)=|\beta|^2$；
条件态分别为 $|000\rangle$ 与 $|111\rangle$，相差整体相位无关。
只读 $S$ 或 $SM$ 而不作联合相干访问时，约化描述是相应的对角混合。
若对所有相关记录实行 $W^\dagger$，则原相干恢复；已有转存记录若未一并逆转，此结论不适用。


<a id="section-4"></a>

## 4 哪些稳定关系可以成为测量基底


#### 定理 4.1（有区别的无扰复制要求正交）


设同一等距耦合满足


$$
W(|u\rangle|0\rangle)=|u\rangle|m_u\rangle,\qquad
W(|v\rangle|0\rangle)=|v\rangle|m_v\rangle,
$$


各向量归一。若两记录物理上不同，特别是可区分，则 $\langle u|v\rangle=0$。


**证明。**


内积守恒给


$$
\langle u|v\rangle\bigl(1-\langle m_u|m_v\rangle\bigr)=0.
$$


非零输入重叠迫使记录向量相同，因而无法留下区别。


∎


这是 Zurek 关于可重复信息传递的标准正交性论证。[[14](#bib-zurek2007)]
它使用 Hilbert 内积、张量接口和等距性，没有使用 Born 概率来完成这个内积推理。
它约束被无扰复制的稳定态；一般 POVM 可以有非正交效果，也可改变被测系统。


#### 定义 4.2（指针扇区与保持条件）


一组和为单位的正交投影 $P_a$ 表示所测标签，令 $B_a$ 为辅助上的自伴算符。
在有限维接口上，对该标签非破坏的相互作用可取


$$
H_{\rm int}=\sum_aP_a\otimes B_a,
\qquad
U(t)=\sum_aP_a\otimes e^{-itB_a}.
$$


其与所有 $P_a\otimes I$ 对易。各 $B_a$ 若对 ready 状态产生不同记录，才传递标签信息。


因此基底由实际耦合、程序与保留记录的方式指定。
若所有 $B_a$ 相同，虽然保持所有标签，却没有测得标签。
若两个扇区有完全相同的实际读出分布，当前读口只能辨认更粗的等价类。
系统自身若有混合这些扇区的后续动力学，稳定性须另行证明。


#### 命题 4.3（复测同值与泄漏界）


对 Lüders 仪器 $\mathcal I_a(\rho)=P_a\rho P_a$，正质量结果 $a$ 后立即复测同一 PVM，
必仍得 $a$。若中间作用为酉 $V$，则对任意支撑在 $P_a$ 内的归一态，


$$
\Pr(\text{离开 }a)\le
\|(I-P_a)VP_a\|_\infty^2.
$$


特别 $[V,P_a]=0$ 时该概率为零。


**证明。**


$P_bP_a=\delta_{ab}P_a$ 给第一结论。
第二式的左侧为
$\operatorname{Tr}[(I-P_a)V\rho_aV^\dagger]$，
等于 $\operatorname{Tr}(A\rho_aA^\dagger)$，其中 $A=(I-P_a)VP_a$；由 $A^\dagger A\le\|A\|_\infty^2I$ 得界。


∎


#### 说明 4.4（复测不唯一规定整个测量）


即使效果为 $P_a$，块内酉 $K_a=V_aP_a$ 仍能复测同值，却改变简并扇区内部状态。
更强地，复测本身也不迫使初始效果是投影：在三维空间取


$$
E_1=|1\rangle\langle1|+\tfrac12|3\rangle\langle3|,\qquad
E_2=|2\rangle\langle2|+\tfrac12|3\rangle\langle3|,
$$


以及 $\mathcal J_r(\rho)=\operatorname{Tr}(E_r\rho)|r\rangle\langle r|$。
两效果和为单位，测量后重准备为 $|r\rangle$，复测必同值，但 $E_r^2\ne E_r$。
所以“无扰复制”“同值复测”“Lüders 更新”应分别声明。


<a id="section-5"></a>

## 5 退相干：局部交叉块怎样衰减


#### 定理 5.1（内部环境的重叠与局部干涉）


在已声明的 ready 条件下，设一个非破坏耦合使


$$
\psi\otimes|e_*\rangle\longmapsto
\sum_aP_a\psi\otimes|e_a\rangle,
\qquad \|e_a\|=1.
$$


对纯或混合系统输入 $\rho$，系统接口的输出为


<a id="eq:decoh"></a>


$$
\rho'=\sum_{a,b}\gamma_{ab}P_a\rho P_b,
\qquad \gamma_{ab}=\langle e_b|e_a\rangle.
$$


（7）


若条件总环境为真正的新片段乘积
$|E_a^{[n]}\rangle=\bigotimes_{j=1}^n|e_a^{(j)}\rangle$，则


$$
\gamma_{ab}^{(n)}=\prod_{j=1}^n\langle e_b^{(j)}|e_a^{(j)}\rangle.
$$


**证明。**


展开联合密度矩阵，对环境接口取偏迹时
$\operatorname{Tr}(|e_a\rangle\langle e_b|)=\langle e_b|e_a\rangle$。
张量乘积的内积相乘，得到第二式。


∎


所有环境仍在完整观察者内；取偏迹只限制当前讨论的读出。
对角权重 $p_a=\operatorname{Tr}(P_a\rho)$ 不变。
当 $a\ne b$ 的重叠趋零时，局部态趋于非选择 Lüders 态
$\mathcal D(\rho)=\sum_aP_a\rho P_a$。
记录新准备、条件独立与旧片段不再被相干访问，都是乘积衰减的实际前件；
复用同一环境时应计算相应完整内积，不能照搬乘积。项目 V18 §9 已有精确复归反例。[[2](#bib-v18)]


#### 命题 5.2（二元精确距离）


对 $P_0+P_1=I$，记 $B=P_0\rho P_1$、$\gamma=\gamma_{01}$。
则


$$
D(\rho',\mathcal D(\rho))
:=\tfrac12\|\rho'-\mathcal D(\rho)\|_1
=|\gamma|\|B\|_1.
$$


若输入为 $\alpha|0\rangle+\beta|1\rangle$，右侧为 $|\alpha\beta\gamma|$。


**证明。**


差矩阵仅有互为伴随的非对角块 $\gamma B$ 和 $\bar\gamma B^\dagger$。
每个 $B$ 的奇异值在差矩阵中产生一对正负特征值，故迹范数为 $2|\gamma|\|B\|_1$。


∎


#### 命题 5.3（保持记录的稳定性保存全部分支质量）


若后续完整酉 $V$ 满足 $V^\dagger Q_rV=Q_r$，则


$$
\|Q_rV\Psi\|^2=\|Q_r\Psi\|^2.
$$


更一般，CPTP 过程满足 $\Phi^\dagger(Q_r)=Q_r$ 时也保持该记录质量。
因此这种记录稳定过程不会使原先多个正质量只剩一个。


**证明。**


分别把 $Q_r$ 拉回酉或使用迹对偶，即得恒等式。


∎


同一测量门若已校准为
$|a\rangle|0\rangle\mapsto|B_a\rangle$，各 $B_a$ 属于不同正交记录扇区，
线性性使实际叠加 $\sum_ac_a|a\rangle|0\rangle$ 的输出为 $\sum_ac_a|B_a\rangle$。
多个 $c_a\ne0$ 时，这个输出不等于其中任何一支。
这一结论针对校准测量和保留记录；<strong>对一个已知固定态，当然可以另选酉把它旋到一个基态</strong>，
但该旋转不再是保持上述测量记录的同一过程。
退相干的操作意义与全局单结果选择之间的区别，也是标准测量理论的重要边界。[[16](#bib-schlosshauer), [14](#bib-zurek2007)]


<a id="section-6"></a>

## 6 经典结果的严格含义：记录代数上的唯一求值


#### 定义 6.1（记录代数）


对实际记录分割 $\{Q_r\}$ 定义


$$
\mathcal C=\left\{\sum_ra_rQ_r:a_r\in\mathbb C\right\}\cong\mathbb C^m.
$$


其元素是记录的函数。

> **记录代数的有限范围（Markdown 编者；不属原稿）。** 定义 6.1 的同构使用有限个非零记录投影，$m$ 是其个数；后续任意系数、有限谱值及零方差论证按这个有限记录代数理解。可数投影分割若取有界函数代数，应要求系数有界并按强算子和得到 $\ell^\infty$；它不是有限 $\mathbb C^m$，也不是不加收敛条件的任意系数和。无限记录路径的事件须在所声明相容记录生成的交换 von Neumann 代数或相应概率空间中处理，不由有限代数自动提供。

两个记录事件的交、并、补分别为
$PQ$、$P+Q-PQ$、$I-P$；互斥事件的并简化为正交和。


#### 定理 6.2（条件经典性与零方差）


任意态 $\rho$ 在 $\mathcal C$ 上的限制是普通概率分布
$p_r=\operatorname{Tr}(\rho Q_r)$。对正质量记录 $r$，令
$\rho_r=Q_r\rho Q_r/p_r$。则对 $A=\sum_sa_sQ_s$、$B=\sum_sb_sQ_s$，


<a id="eq:character"></a>


$$
\boxed{\omega_r(A)=a_r,\qquad
\omega_r(AB)=\omega_r(A)\omega_r(B),\qquad
\operatorname{Var}_r(A)=0\quad(A=A^\dagger).}
$$


（8）


所以条件态在记录代数上成为单点求值，即字符。


**证明。**


$Q_rAQ_r=a_rQ_r$ 给第一式；乘法在各正交块上逐坐标进行，给第二式。
自伴时 $a_r$ 为实数，方差为 $a_r^2-a_r^2=0$。
一般限制为 $\omega(A)=\sum_rp_ra_r$，其正性及归一性正好是 $p_r\ge0$、$\sum_rp_r=1$。


∎


这给用户直觉一个准确表述：<strong>取得记录 $r$ 后，所有由该记录定义的相容问题都有唯一值。</strong>
这不仅是线性期望已给定，还在该交换代数上满足乘法相容和零方差。
但完整观察者代数通常更大。
若 $\operatorname{rank} Q_r>1$，块内还可有相干、纠缠与持续变化；即使系统已在 $|0\rangle$，
下一次改测 $\sigma_x$ 仍有两个等权结果，$\operatorname{Var}_{|0\rangle}(\sigma_x)=1$。
“态已知”与“所有测量都确定”不等同。


#### 推论 6.3（标签确定的充要条件）


设 $A=\sum_ra_rQ_r$ 的实数 $a_r$ 两两不同，则
$\operatorname{Var}_\rho(A)=0$ 当且仅当 $\rho$ 的支撑落在某一个 $Q_r\mathcal H$ 内。


**证明。**


令 $m=\sum_rp_ra_r$，方差为 $\sum_rp_r(a_r-m)^2$。
非负项和为零，只能有一个不同谱值承载正质量。
$\operatorname{Tr}(\rho Q_r)=1$ 对正态等价于支撑在该块内。


∎


<a id="section-6.1"></a>

### 6.1 持久记录与完整门历史


对有限自适应仪器，节点 $h$ 的 Kraus 族满足
$\sum_{r,\alpha}K_{r\alpha\mid h}^\dagger K_{r\alpha\mid h}=I$。
每步 $K$ 的共同输入、输出接口已包含以后会重新参与作用的全部量子记忆。
另将当前协议时间窗内不再参与后续耦合的辅助指标 $\alpha$ 外提到保留寄存器 $G$，
并提供所需 ready 容量，逐层等距扩张给


<a id="eq:history"></a>


$$
\Psi_n=\sum_{h,\boldsymbol\alpha}|h\rangle_R|\boldsymbol\alpha\rangle_G
\otimes K_{h,\boldsymbol\alpha}\psi_0,\qquad
K_{h,\boldsymbol\alpha}=K_{r_n\alpha_n\mid h_{n-1}}\cdots K_{r_1\alpha_1}.
$$


（9）


这是在所声明扩张合同下同一 $\Omega$ 的门积展开；被外提的 $G$ 仍在完整观察者内。
若旧 $\alpha$ 将重新参与耦合，须把对应量子记忆重新计入完整过程，
不能直接沿用把它消去后的简单乘积。每层正交历史控制保证整体等距，
补齐 ready 载体即可整体酉实现。
本段按完整测量轮次编号，$G_n$ 表示完成 $n$ 轮所包含的全部实际门积。
在这个共同终端切面，$Q_h$ 对完整历史为记录原子，对较短前缀为其所有延伸的柱事件。于是


$$
p(h)=\|Q_hG_n\Omega\|^2,\qquad
Q_h=\sum_rQ_{hr},\qquad p(h)=\sum_rp(hr).
$$


因此实际保留的历史构成一个经典概率树。任意相互不对易的未测问题并不因此具有共同值表。
无限链还须有相容嵌入和足够容量；有限公式不自动供应无限内存。
这些完整记录条件承接 $\Omega$ 主文 §6、V30 §3 和 V31 §8。[[12](#bib-omega), [4](#bib-v30), [5](#bib-v31)]


<a id="section-7"></a>

## 7 AURIC 三轴：退相干与条件选支的不同几何


#### 命题 7.1（二分支三轴恒等式）


设初始逻辑 qubit 为 $c_0|0\rangle+c_1|1\rangle$，$p=|c_0|^2$，
条件环境重叠为 $\gamma$。其约化态为


$$
\rho_\gamma=
\begin{pmatrix}
p&c_0\bar c_1\gamma\\
\bar c_0c_1\bar\gamma&1-p
\end{pmatrix}
=\frac{I+x\sigma_x+y\sigma_y+z\sigma_z}{2},
$$


其中 $x=2\Re(c_0\bar c_1\gamma)$、$y=-2\Im(c_0\bar c_1\gamma)$、$z=2p-1$。
于是


<a id="eq:bloch"></a>


$$
\boxed{x^2+y^2+z^2=z^2+(1-z^2)|\gamma|^2,\qquad
1-\|\mathbf r\|^2=4p(1-p)(1-|\gamma|^2).}
$$


（10）


**证明。**


$x^2+y^2=4p(1-p)|\gamma|^2$，而 $4p(1-p)=1-z^2$，直接代入。


∎


当 $\gamma\to0$，横向相干消失而 $z$ 不变。
完全退相干是 $(x,y,z)\mapsto(0,0,z)$；整条 $z$ 轴都是不动点。
只有给定对应的理想尖锐记录后，逻辑条件态才是 $(0,0,+1)$ 或 $(0,0,-1)$。
例如初始 $|+\rangle$ 在非选择退相干后成为 $I/2$，即球心；
它对该退相干通道完全稳定，仍没有唯一的 $z$ 结果。
这里球半径的损失描述局部纯度损失；完整联合态仍可纯。


<a id="section-7.1"></a>

### 7.1 接回项目的原五模式，而非任意改名


V37 §3 给出一个固定等距 $J:\mathbb C^2\to\mathbb C^5$。令


$$
\nu=\frac1{1+2\sqrt3+\sqrt{11}},\qquad
a_\nu=\frac{\nu(\sqrt3+\sqrt{11})}{2}.
$$


其五效果满足


$$
\begin{aligned}

E_{25}&=\tfrac\nu2(\sqrt3I-\sigma_x-\sigma_y-\sigma_z),&E_0&=3E_{25},\\
E_2&=\tfrac\nu2(\sqrt{11}I+3\sigma_x+\sigma_y+\sigma_z),\\
E_5&=\tfrac\nu2(\sqrt{11}I+\sigma_x+3\sigma_y+\sigma_z),&E_3&=\nu(I+\sigma_z).

\end{aligned}
$$


原三占据均值在这个编码类上满足


<a id="eq:auric"></a>


$$
(X_{\rm occ},Y_{\rm occ},Z_{\rm occ})
=(a_\nu,a_\nu,\nu)+\nu(x,y,z).
$$


（11）


V59 §7.1 明确它们按低端、高端、中位对应用户的 $F[1],F[3],F[2]$。
它们来自一个有偏、不尖锐的共同五结果读口，不能解释成三次同时尖锐 Pauli 测量。[[6](#bib-v37), [11](#bib-v59)]

因此在测量基底与此逻辑 $z$ 轴对齐时，非选择退相干在金字塔内给


$$
(X_{\rm occ},Y_{\rm occ},Z_{\rm occ})
\longrightarrow(a_\nu,a_\nu,\nu(1+z)),
$$


而条件指针态的坐标为 $(a_\nu,a_\nu,2\nu)$ 或 $(a_\nu,a_\nu,0)$。
若测量轴不同，应先声明对应的逻辑旋转，不能套同一 $z$ 公式。

模式关系在该固定编码上是


$$
\kappa=w_{25}=\tfrac\nu2(\sqrt3-x-y-z),\qquad w_0=3\kappa,
\qquad 1-X_{\rm occ}-Y_{\rm occ}-Z_{\rm occ}-2\kappa=0.
$$


原逻辑模式 $(N,1,2,3,13)$ 对应数值 $(0,2,3,5,25)$。
关系事件 $e_{13}=(e_1+e_{13})(e_3+e_{13})$，而独占事件 $e_1e_3=0$。
$F[\mathrm{null}]$ 对应空模式事件 $e_N$；归一化是 $\omega(I)=1$。[[7](#bib-v42)]
三轴仿射标定、$w_0=3\kappa$ 及由此得到的四推一等式需要固定 $J$ 编码。
原五模式的事件恒等式及概率和为一不需要该编码；
不能把编码新增的约束推广成任意五模式状态的恒等式。


<a id="section-8"></a>

## 8 递归测量怎样把指定问题变得确定


#### 定义 8.1（固定重复 QND 读口）


设有限分割 $\{P_a\}_{a=1}^d$ 表示不被此次协议混合的标签，有限结果集为 $\mathcal R$。
取条件分布 $q_a(r)\ge0$、$\sum_rq_a(r)=1$ 与实相位 $\theta_{ra}$，定义


$$
M_r=\sum_a\sqrt{q_a(r)}e^{i\theta_{ra}}P_a.
$$


每轮使用同一准备、同一仪器，保留旧记录并只接入新 ready 槽位；不在轮间混合 $P_a$。
允许 $P_a$ 简并及 $\rho_0$ 混合。记 $p_a=\operatorname{Tr}(P_a\rho_0)$，删去零先验扇区。


#### 定理 8.2（同一 $\Omega$ 内的后验递归）


对记录 $h=(r_1,\ldots,r_n)$，令
$L_a(h)=\prod_{j=1}^nq_a(r_j)$。则


<a id="eq:posterior"></a>


$$
\begin{aligned}

p(h)&=\sum_ap_aL_a(h),\\
p_n(a\mid h)&=\frac{p_aL_a(h)}{\sum_bp_bL_b(h)},\\
p_{n+1}(a\mid h,r)
&=\frac{p_n(a\mid h)q_a(r)}{\sum_bp_n(b\mid h)q_b(r)}.

\end{aligned}
$$


（13）


以上除法限于正质量历史。记


$$
K_h=M_{r_n}\cdots M_{r_1},\qquad
\rho_h=\frac{K_h\rho_0K_h^\dagger}{p(h)},\qquad \rho_n=\rho_{h_n}.
$$


这里 $p_n(a\mid h)$ 正是条件量子态 $\rho_h$ 的 $P_a$ 权重。


**证明。**


由 $P_aP_b=\delta_{ab}P_a$，


$$
M_{r_n}\cdots M_{r_1}
=\sum_a\sqrt{L_a(h)}e^{i\sum_j\theta_{r_ja}}P_a.
$$


对 $K_h\rho_0K_h^\dagger$ 取迹只保留对角块；再读 $P_a$，得到相应分子。
逐步更新是将最后一个因子提出。这些都是式 [（9）](#eq:history) 的实际记录质量。


∎


若全部 $q_a(r)>0$ 且先验均正，任何有限记录后所有 $p_n(a\mid h)$ 仍正。
因此有限次弱测量通常只使候选越来越不等权；精确零概率不由“已经很小”推出。


#### 定义 8.3（相干重叠与读口分辨系数）


对全部 $a,b$ 置


$$
\gamma_{ab}=\sum_r\sqrt{q_a(r)q_b(r)}e^{i(\theta_{ra}-\theta_{rb})},
\qquad
B_{ab}=\sum_r\sqrt{q_a(r)q_b(r)}.
$$


$\gamma_{ab}$ 是条件探针的复内积；$B_{ab}$ 是当前记录分布的 Hellinger 亲和度。
三角不等式给 $|\gamma_{ab}|\le B_{ab}\le1$。
特别 $\gamma_{aa}=B_{aa}=1$。
由 Cauchy–Schwarz 的等号条件，$B_{ab}=1$ 当且仅当 $q_a=q_b$。


#### 定理 8.4（退相干与后验误差的共同界）


<a id="thm:commonbound"></a>


在上述固定协议中，定义非选择态与目标对角态


$$
\bar\rho_n=\sum_hK_h\rho_0K_h^\dagger,\qquad
\rho_{\rm diag}=\sum_aP_a\rho_0P_a.
$$


再定义平均后验模糊度


$$
e_n=\mathbb E_h[1-\max_ap_n(a\mid h)].
$$


则对每个 $n\ge1$，


<a id="eq:decohbound"></a>


<a id="eq:bayesbound"></a>


$$
\begin{aligned}

\bar\rho_n&=\sum_{a,b}\gamma_{ab}^{\,n}P_a\rho_0P_b,\\
D(\bar\rho_n,\rho_{\rm diag})
&\le\sum_{a<b}\sqrt{p_ap_b}\,|\gamma_{ab}|^n
\le\sum_{a<b}\sqrt{p_ap_b}\,B_{ab}^{\,n},\\
e_n&\le\sum_{a<b}\sqrt{p_ap_b}\,B_{ab}^{\,n}.

\end{aligned}
$$


（16）、（17）


若全部有先验质量的标签分布两两不同，则 $B_*:=\max_{a<b}B_{ab}<1$，
右侧至多为 $C_0B_*^n$，其中 $C_0=\sum_{a<b}\sqrt{p_ap_b}\le(d-1)/2$。
只有一个正质量标签时，两种误差均为零。


**证明。**


单轮非选择仪器对块 $P_a\rho P_b$ 的乘数正是 $\gamma_{ab}$，迭代给第一式。
由 Schatten 范数乘积不等式，


$$
\|P_a\rho_0P_b\|_1
\le\|P_a\sqrt{\rho_0}\|_2\|\sqrt{\rho_0}P_b\|_2
=\sqrt{p_ap_b}.
$$


对非对角块使用三角不等式，配对 $a,b$ 并除以二，得到式 [（16）](#eq:decohbound)。

对每个历史置 $x_a(h)=p_aL_a(h)$。选择最大项的指标 $a_*$，则


$$
\sum_ax_a-\max_ax_a
=\sum_{a\ne a_*}\min(x_a,x_{a_*})
\le\sum_{a<b}\min(x_a,x_b)
\le\sum_{a<b}\sqrt{x_ax_b}.
$$


左侧对历史求和就是 $e_n$。右侧利用有限乘积求和给


$$
\sum_h\sqrt{L_a(h)L_b(h)}
=\left(\sum_r\sqrt{q_a(r)q_b(r)}\right)^n=B_{ab}^{\,n}.
$$


最后 $2C_0=(\sum_a\sqrt{p_a})^2-1\le d-1$。


∎


这是两种不同量的共同上界，不把局部迹距离直接等同后验错误概率。
它适用于混态和简并块；相位只进入 $\gamma$，不进入当前标签读口的 $B$。
若 $0<B_*<1$、$C_0>0$，达到共同容差 $\epsilon$ 的一个充分深度条件是


$$
n\ge\frac{\log(C_0/\epsilon)}{-\log B_*},\qquad n\ge1,
$$


取满足不等式的整数即可。若 $B_*=0$，一步已经完全分辨。

> **共同深度界的全部端点（Markdown 编者；不属原稿）。** 上述对数式要求正容差 $\epsilon>0$、至少两个正先验标签及 $0<B_*<1$、$C_0>0$。当 $\epsilon\ge C_0$ 时任何整数 $n\ge1$ 已满足共同上界；当 $0<\epsilon<C_0$ 时取满足原不等式的整数。若只有一个正先验标签，$C_0=0$，两种误差均为零，不对空成对集合取最大值，也不用该对数。若至少两个正先验标签而 $B_*=0$，各对读口支撑互斥，$n\ge1$ 两误差均为零。若 $B_*=1$，该统一几何上界不给随深度趋零保证；非信息性读口也可能仅靠相位使局部相干消失。$\epsilon=0$ 不进入对数式，$0<B_*<1$ 的正上界不保证任何有限深度精确为零；负数不是误差容差。


这是一条解析资源关系，不声称实际项目已供应任意多层的准备与记录容量。


#### 推论 8.5（条件态的稳定极化）


在一致无限延伸、有限标签及两两不同读口分布的条件下，存在记录可测标签 $A$，使


$$
p_n(a)\longrightarrow\mathbf1_{\{A=a\}}\quad\text{几乎必然},
\qquad \Pr(A=a)=p_a.
$$


在本节标量块 QND 模型内，条件态趋于
$P_A\rho_0P_A/p_A$；若 $P_A$ 为秩一，则为相应纯指针态。


**证明。**


由更新式和下一读数的条件概率，


$$
\mathbb E[p_{n+1}(a)\mid h]
=\sum_{r:p(r\mid h)>0}
p(r\mid h)\frac{p_n(a)q_a(r)}{p(r\mid h)}=p_n(a).
$$


零概率项的相应分子也为零。因此每个 $p_n(a)$ 为有界鞅，几乎必然且在 $L^1$ 收敛。
式 [（17）](#eq:bayesbound) 及有界收敛给
$\mathbb E[1-\max_ap_\infty(a)]=0$；极限概率向量必为一个顶点。
各坐标已收敛，排除了只靠最大值趋一而仍更换标签的漏洞。
鞅保均值给选择质量。
本模型中，当 $p_n(a)>0$ 时，
$P_a\rho_nP_a/p_n(a)=P_a\rho_0P_a/p_a$。
在事件 $A=a$ 上该条件最终满足。
对 $\rho_n$ 作纯化并正规化投影，纯化内积为 $\sqrt{p_n(a)}$；
纯态迹距离和偏迹收缩给
$D(\rho_n,P_a\rho_nP_a/p_n(a))\le\sqrt{1-p_n(a)}$，故得态收敛。


∎


有限深度还有一个状态层面的结论。令 $\widehat a_n(h)$ 为最大后验标签，
$\rho_a=P_a\rho_0P_a/p_a$，则同一投影界和平方根的凹性给


$$
\mathbb E_hD(\rho_h,\rho_{\widehat a_n(h)})
\le\sqrt{e_n}
\le\left(\sum_{a<b}\sqrt{p_ap_b}\,B_{ab}^{\,n}\right)^{1/2}.
$$


一次取得的报告 $r$ 在其记录代数上已经确定；本节逐渐确定的是被测目标 $a$。
简并块内的 $\rho_a$ 仍可混合。固定块态的结论使用了本节 Kraus 算符在各块内为标量的条件；
若另有块内旋转，只能先主张标签稳定，不能直接主张整个条件态收敛。

有界鞅收敛是这里使用的标准概率定理，项目 V30 §3 给出基于 $L^2$ 增量与最大不等式的证明。
非破坏后验极化及信息相对熵率是已有标准理论，项目 V30、V31 已承接它们。[[15](#bib-bauer), [4](#bib-v30), [5](#bib-v31)]
若额外假设全部 $q_a(r)>0$，在联合记录律的分量 $a$ 上，


$$
\frac1n\log\frac{p_n(b)}{p_n(a)}
=\frac1n\log\frac{p_b}{p_a}
+\frac1n\sum_{j=1}^n\log\frac{q_b(r_j)}{q_a(r_j)}
\longrightarrow-D_{\rm KL}(q_a\Vert q_b)<0.
$$


这里的分量分解只是同一交换记录律的概率表示，不是给全部不相容量安置外部隐藏值。

> **相对熵率的标签与概率律（Markdown 编者；不属原稿）。** 严格负号针对不同的正先验标签 $b\ne a$，并沿用本节两两不同分布的条件；$b=a$ 时两边为零。给定联合律的分量 $a$，固定新准备协议产生独立同分布的读数律 $q_a$。有限结果集及全部 $q_a(r)>0$ 保证所用 log 比可积，强大数定律才给该极限；它不适用于任意带未保留记忆的自适应读口。


$\log$ 将证据的乘积转成可加累积；它与振幅平方有不同数学职责。


<a id="section-8.1"></a>

### 8.1 完全退相干却没有学到标签：一个明确反例


#### 命题 8.6（相位记录与标签记录不同）


对 qubit 取


$$
M_0=\frac{I}{\sqrt2},\qquad M_1=\frac{\sigma_z}{\sqrt2}.
$$


则非选择通道一步完全 $z$ 退相干，但任意历史都不改变 $z$ 标签的后验权重。


**证明。**


两标签的读口分布都为 $(1/2,1/2)$，故 $B_{01}=1$，
$p_n(a\mid h)=p_a$。但相位差使 $\gamma_{01}=1/2-1/2=0$，
且


$$
\sum_rM_r\rho M_r^\dagger
=\tfrac12(\rho+\sigma_z\rho\sigma_z)=\mathcal D_z(\rho).
$$


条件探针可取 $e_0=|+\rangle$、$e_1=|-\rangle$；它们正交，
但当前计算基读口对二者给相同分布。若在尚未计算基读出的探针上先作 $H$ 再读出，
则两支的新 Kraus 算符为 $(M_0+M_1)/\sqrt2=P_0$ 与
$(M_0-M_1)/\sqrt2=P_1$，可直接分辨。
这是更换实际量子读口，不能通过对已取得的无信息经典比特作后处理来实现。


∎


所以 $|\gamma|<1$ 只保证交叉块衰减，$B<1$ 才保证这个读口提供标签信息。
V18 §8.2 另有混态辅助反例：$\sigma=I/2,W=\sigma_z$ 时父系统退相干，
辅助的两个条件边缘却相同；信息需在含内部纯化的更大接口中寻找。[[2](#bib-v18)]


<a id="section-8.2"></a>

### 8.2 误差如何进入递归而不破坏含义


上述共同界针对精确固定 QND 模型。对真实仪器，必须比较完整记录和全部保留记忆。
若实际与理想每步完整报告通道在共同接口上满足半 diamond 距离至多 $\epsilon_k$，
则相同初态下终端完整记录态的半迹距离至多 $\sum_{k\le n}\epsilon_k$。
证明是逐步插入比较通道并使用 CPTP 收缩；这是 v65 的组合界。
任何一个已经固定的终端判别事件的概率偏差也受此界控制。
它不自动比较两套协议各自重新拟合出来的条件后验，尤其不保证稀有记录的条件误差小。

稳定记录 V31 定理 6.4 在信息性二元 QND 比较仪器下，
若实际完整旗标误差可求和，则实际条件权重仍几乎必然极化，
极限选择质量的偏差不超过总误差。
定理 6.5 另证明精确平均权重守恒时可弱化为误差趋零。
这些是有明确前件的已有鲁棒性定理；“门越来越准”而未控制完整后继及漂移，不足以替代它们。[[5](#bib-v31)]


<a id="section-9"></a>

## 9 平方权重从哪来：稳定性之外的细化相容


<a id="sec:born"></a>


指针正交、可复制与固定点结构并不单独决定概率。
在一份固定分支分解上，形式赋值
$p_a\propto|c_a|^\beta$（$\beta>0$）不改变任何门或记录的几何稳定性。
要排除 $\beta\ne2$，必须加入跨分解的读出相容前提。


#### 定理 9.1（粗标签不变的正交细化迫使平方概率）


假设理想有限维 Hilbert 接口中的每个分支强度为 $t=\|v\|^2$，
当前分解满足 $t_a\ge0$、$\sum_at_a=1$。
原始权重由同一个函数 $w$ 给出，$w(0)=0$、$w(t)>0$ 对 $0<t\le1$，
概率为 $w(t_a)/\sum_bw(t_b)$。
共同 $w$ 的标签、上下文和历史独立性是额外前提。
再要求：对全部 $s,t>0$、$s+t<1$，可以在保留正强度旁观分支的情况下，
把同一粗标签的强度 $s+t$ 酉拆成两条正交细记录 $s,t$，并且粗标签概率不变。
则存在 $c>0$ 使


$$
w(t)=ct\quad(0<t<1),\qquad
\boxed{p_a=t_a=\|v_a\|^2.}
$$


不需要额外连续性假设。


**证明。**


令旁观强度为 $b=1-s-t>0$，比较细化前后粗标签相对于旁观标签的赔率：


$$
\frac{w(s+t)}{w(b)}=\frac{w(s)+w(t)}{w(b)}.
$$


故 $w(s+t)=w(s)+w(t)$。正性使 $w$ 在 $(0,1)$ 单调。
置 $c=2w(1/2)$，把 $1/2$ 分成 $n$ 等份得到
$w(1/(2n))=c/(2n)$，相加给所有 $0<m/(2n)<1$ 的有理点。
上下有理数夹逼任意实数 $t$，得到 $w(t)=ct$。
若归一态有至少两条非零分支，各 $t_a<1$，归一化时 $c$ 消去；
若只有一条非零分支，其概率本来为一。


∎


旁观分支前提本身不固定 $w(1)$ 的原始标度；这不影响概率结论。
若想写包括端点的原始权重恒等式，应另要求端点可加或相应标定。
对于 $w(t)=t^{\beta/2}$，一次二等分即给
$t^{\beta/2}=2(t/2)^{\beta/2}$，从而 $\beta=2$。

这里使用了 Hilbert 的正交平方几何；共同权重与粗细相容又是读出公理。
因而本定理是替换概率公理的一种条件表达，不是从稳定性单独推出整个 Hilbert 结构。
分支内部酉等价只在指定标签和接口内给径向依赖，不能自动排除跨标签或历史的权重变化。
实际有限原生门词若只取得有限细化，不能冒充本定理覆盖全部 $s,t$ 的理想前提。
项目 V49 的相干标定、V58 的完整效果可加性提供不同的条件桥，须按各自取得范围使用。[[8](#bib-v49), [10](#bib-v58)]


<a id="section-10"></a>

## 10 较基础的数学公理：正关系代数及其表示


用户提出“通过已知数学结构换公理”，可以采用与 V30 一致的路线。


#### 定义 10.1（正关系代数模型）


给定复含单位 $C^*$ 代数 $\mathcal A$ 和一个固定正归一线性泛函 $\omega$：


$$
\omega(I)=1,\qquad \omega(a^\dagger a)\ge0.
$$


内部可逆作用由选定的酉元表示，实际读口与程序是同一代数中的元素或子代数。
可读经典记录另要求完整正交投影及相应保留、复制关系。


#### 定理 10.2（标准 GNS 表示与平方结构）


上述对象有循环 Hilbert 表示 $(\pi,\mathcal H_\omega,\Omega)$，满足


$$
\omega(a)=\langle\Omega,\pi(a)\Omega\rangle,
\qquad
\omega(a^\dagger a)=\|\pi(a)\Omega\|^2.
$$


内部酉元被表示为酉算符；正质量记录 $m$ 的条件态为


$$
\omega_m(a)=\frac{\omega(m^\dagger am)}{\omega(m^\dagger m)}.
$$


**证明。**


正性给 Cauchy–Schwarz 不等式。取零空间
$\mathcal N=\{a:\omega(a^\dagger a)=0\}$，在商空间上定义
$\langle[a],[b]\rangle=\omega(a^\dagger b)$。
由 $\omega(a^\dagger b^\dagger ba)\le\|b\|^2\omega(a^\dagger a)$，
$\mathcal N$ 是左理想，左乘 $\pi(b)[a]=[ba]$ 有界且与伴随相容。
完成商空间得 Hilbert 空间，取 $\Omega=[I]$，立即得到两式。
若 $u^\dagger u=uu^\dagger=I$，则 $\pi(u)^\dagger\pi(u)=\pi(u)\pi(u)^\dagger=I$。
条件式的分子对 $a=b^\dagger b$ 非负，对单位的值经归一化为一。


∎


这是标准 GNS 构造，项目 V30 定理 2.2 已有自足证明。[[4](#bib-v30)]
它展示平方范数、向量本体表示与条件压缩怎样来自一个共同正关系对象。
但复代数、正性、线性、所允许的效果和将这些权重解释为实际概率的桥仍是输入。
循环表示在酉交织意义下的唯一性，也不是“物理宇宙只有一个本体”的独立证明。


<a id="section-10.1"></a>

### 10.1 本轮可证明的公理依赖关系


<details>
<summary>原稿表格生产设置（逐字保留）</summary>

<div style="overflow-x:auto;max-width:100%">

```latex
\renewcommand{\arraystretch}{1.22}
\begin{tabularx}{\textwidth}{@{}p{0.23\textwidth}XX@{}}
\toprule
目标结构 & 足够的明确前提 & 得到的结论与范围\\
\midrule
Hilbert 向量与平方范数 & 复 $C^*$ 代数、正归一线性态 & GNS 表示；复性与正性仍是前提\\
全局酉演化 & 指定代数中的酉元，或已给同一载体的酉实现 & 内积保持；只归一一个实际向量不够\\
一般测量仪器 & 同一完整酉、独立 ready、共同参考接口 & CP 分支和算子完整性 $\sum K^\dagger K=I$\\
条件投影更新 & 已指定记录事件及正权重 & $QG\Omega/\|QG\Omega\|$ 的相对态\\
正交可读标签 & 信息性无扰复制或明确稳定记录子空间 & 可区分稳定态正交；不要求所有 POVM 为 PVM\\
经典唯一值 & 正交记录代数并给定某记录 & 求值字符、零条件方差\\
后验渐近确定 & 持久记录、非破坏结构、读口能辨识标签 & 条件权重极化；有限精度需完整误差控制\\
Born 平方概率 & 共同强度权重与完整粗细相容，或正态效果桥 & 指定接口上的平方赋权\\
全局只余一个实际分量 & 本文前提没有供应该机制 & 需另行说明本体选择语义或修改动力学\\
\bottomrule
\end{tabularx}
```

</div>

</details>
<div style="overflow-x:auto;max-width:100%">

| 目标结构 | 足够的明确前提 | 得到的结论与范围 |
| --- | --- | --- |
| Hilbert 向量与平方范数 | 复 $C^*$ 代数、正归一线性态 | GNS 表示；复性与正性仍是前提 |
| 全局酉演化 | 指定代数中的酉元，或已给同一载体的酉实现 | 内积保持；只归一一个实际向量不够 |
| 一般测量仪器 | 同一完整酉、独立 ready、共同参考接口 | CP 分支和算子完整性 $\sum K^\dagger K=I$ |
| 条件投影更新 | 已指定记录事件及正权重 | $QG\Omega/\Vert QG\Omega\Vert$ 的相对态 |
| 正交可读标签 | 信息性无扰复制或明确稳定记录子空间 | 可区分稳定态正交；不要求所有 POVM 为 PVM |
| 经典唯一值 | 正交记录代数并给定某记录 | 求值字符、零条件方差 |
| 后验渐近确定 | 持久记录、非破坏结构、读口能辨识标签 | 条件权重极化；有限精度需完整误差控制 |
| Born 平方概率 | 共同强度权重与完整粗细相容，或正态效果桥 | 指定接口上的平方赋权 |
| 全局只余一个实际分量 | 本文前提没有供应该机制 | 需另行说明本体选择语义或修改动力学 |

</div>


<a id="section-11"></a>

## 11 本轮结论：测量是同一本体中的关系分辨与条件化

> **依赖表的前提范围（Markdown 编者；不属原稿）。** 上表“明确稳定记录子空间”承接已声明的可读、互斥正交记录投影及保持条件；动力学固定点本身不推出可区分性、信息性或所有稳定态正交。表中正态效果桥在所述有限接口上使用全部效果、同一正归一响应与粗粒化相容，不能把有限菜单上的归一化读数替代这些前件。


把本轮结果连在一起，测量的可证明结构为


$$
\begin{gathered}
\Psi_k=G_k\Omega
\quad\xrightarrow{\text{内部程序与校准耦合}}\quad
\sum_r Q_r\Psi_{k+1},\\
\text{记录重叠控制局部干涉，读口分辨控制条件推断},\\
\Psi_{k+1\mid r}=Q_r\Psi_{k+1}/\|Q_r\Psi_{k+1}\|
\quad\Longrightarrow\quad
\omega_{\mid r}|_{\mathcal C}\text{ 是单点求值。}
\end{gathered}
$$


环境、程序和记录始终在完整观察者内。局部退相干、记录中相对确定与完整本体的描述，
是同一结构的三种不同读法。

用户直觉中可以保留并严格加强的部分是：
<strong>持续、可辨识、保留目标的记录积累，能把该目标的条件残差压到零；
在给定记录的相容代数上，关系确实成为唯一值。</strong>

> **结论中渐近确定的适用条件（Markdown 编者；不属原稿）。** “条件残差压到零”在本文由 §8 的固定标量块 QND、有限标签、两两不同的同一读口分布、一致无限延伸及所需容量保证；采用 V31 的实际仪器版本时，还须保留其完整误差与漂移条件。它不把每轮均有微小差异的一般变动读口自动判为渐近可辨识，也不推出完整本体只剩一个实际记录分量。


其几何并非所有三轴一起“冻结”为一个普适点：非选择退相干压低横向相干，
条件选支给指针极点，简并块内与非交换读口仍保留量子结构。

若坚持完整层面始终酉，式 [（3）](#eq:collapse) 提供无需第二本体的操作性塌缩表达。
若进一步主张所有其他记录分量在整个本体中实际不存在，须另给选择原则；
唯一 $\Omega$ 本身并不包含这个推论。
本轮因此推进的是测量公理的条件结构来源，以及稳定性何时真正转化为可读确定性的判据。


<details>
<summary>原稿文献环境生产设置（逐字保留）</summary>

```latex
\begin{thebibliography}{99}
```

</details>

## 固定来源与文献


<a id="bib-head"></a>

**[1]**


trureturing，固定提交
[<code>5cf95e1a<wbr>e01f7ed8<wbr>6735c04a<wbr>d8d752cb<wbr>19b1a58b</code>](https://github.com/the-omega-institute/trureturing/tree/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b)。
本轮活动源码请求未成功；引用固定原文，不主张更新提交已核实。


<a id="bib-v18"></a>

**[2]**


项目 V18，[三角剖分、条件塌缩与递归酉门](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_TRIANGULATION_COLLAPSE_AND_RECURSIVE_UNITARY_GATES_V18.md)，§§4、8–9。


<a id="bib-v21"></a>

**[3]**


项目 V21，[静态量子历史、内生观察者与关系时钟](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_STATIC_QUANTUM_HISTORIES_ENDOGENOUS_OBSERVERS_AND_RELATIONAL_CLOCKS_V21.md)，§§2、4。


<a id="bib-v30"></a>

**[4]**


项目 V30，[唯一静态本体、内生观察者与黄金递归时钟](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_UNIQUE_STATIC_ONTOLOGY_ENDOGENOUS_OBSERVERS_AND_GOLDEN_RECURSIVE_CLOCKS_V30.md)，§§2–3、6、12。


<a id="bib-v31"></a>

**[5]**


项目稳定记录 V31，[内部记录、长期稳定与时钟几何重建](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_INTERNAL_RECORDS_LONG_TERM_STABILITY_AND_CLOCK_GEOMETRY_RECONSTRUCTION_V31.md)，§§5–8。


<a id="bib-v37"></a>

**[6]**


项目 V37，[二元关系、酉表示与黄金门普适性](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)，§3。


<a id="bib-v42"></a>

**[7]**


项目 V42，[$F[13]$ 关系语义、量子三轴与递归相容](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_F13_RELATIONAL_SEMANTICS_QUANTUM_THREE_AXES_AND_RECURSIVE_COMPATIBILITY_V42.md)，§§1、3、12。


<a id="bib-v49"></a>

**[8]**


项目 V49，[加法、乘法、幂、二次关系闭合与归一化提升](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md)。


<a id="bib-v57"></a>

**[9]**


项目 V57，[固定本体态、增长观察者与稳定自我](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_FIXED_ONTIC_STATE_GROWING_OBSERVER_STABLE_SELF_INTERNAL_PREDICTION_AND_RELATIVE_CLOCKS_V57.md)，§§2、5。


<a id="bib-v58"></a>

**[10]**


项目 V58，[关系公理、共同复相位与条件量子重构](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md)，§§5、11。


<a id="bib-v59"></a>

**[11]**


项目 V59，[局域层析、相干读出轨道与量子正性起源](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md)，§7.1。


<a id="bib-omega"></a>

**[12]**


项目主文，[$\Omega$ 静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，§6。


<a id="bib-nielsen"></a>

**[13]**


M. A. Nielsen and I. L. Chuang,
<em>Programmable quantum gate arrays</em>, Phys. Rev. Lett. 79, 321–324 (1997).
[doi:10.1103/PhysRevLett.79.321](https://doi.org/10.1103/PhysRevLett.79.321);
[作者预印本](https://arxiv.org/pdf/quant-ph/9703032)。
实际核读确定性程序正交定理及证明。


<a id="bib-zurek2007"></a>

**[14]**


W. H. Zurek,
<em>Quantum origin of quantum jumps: Breaking of unitary symmetry induced by information transfer in the transition from quantum to classical</em>,
Phys. Rev. A 76, 052110 (2007).
[doi:10.1103/PhysRevA.76.052110](https://doi.org/10.1103/PhysRevA.76.052110);
[作者预印本](https://arxiv.org/pdf/quant-ph/0703160)。
实际核读正交性推导与非酉塌缩边界。


<a id="bib-bauer"></a>

**[15]**


M. Bauer and D. Bernard,
<em>Convergence of repeated quantum nondemolition measurements and wave-function collapse</em>,
Phys. Rev. A 84, 044103 (2011).
[doi:10.1103/PhysRevA.84.044103](https://doi.org/10.1103/PhysRevA.84.044103);
[作者预印本](https://arxiv.org/pdf/1106.4953)。
实际核读 QND 模型、后验鞅、极化与相对熵率。


<a id="bib-schlosshauer"></a>

**[16]**


M. Schlosshauer,
<em>Decoherence, the measurement problem, and interpretations of quantum mechanics</em>,
Rev. Mod. Phys. 76, 1267–1305 (2005).
[doi:10.1103/RevModPhys.76.1267](https://doi.org/10.1103/RevModPhys.76.1267);
[作者预印本](https://arxiv.org/pdf/quant-ph/0312059)。
实际核读测量问题、局部干涉抑制与结果解释的相关部分，未声称通读全文。


```latex
\end{thebibliography}

\end{document}
```

<details>
<summary>原始 XeLaTeX 前言、生产设置与元数据（逐字保留）</summary>

<div tabindex="0" role="region" aria-label="原始前言" style="overflow-x:auto">

```tex
% !TeX program = xelatex
% Compile twice with XeLaTeX.
% Optional: \def\AURICFontPath{/absolute/path/to/CJK/fonts/}
% All mathematics is proved on paper. Code is used only for source handling
% and document production, not mathematical computation or testing.
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
\usepackage{amsmath,amssymb,amsthm,mathtools,bm,mathrsfs}
\usepackage{booktabs,array,tabularx,enumitem,fancyhdr,xcolor,needspace}
\definecolor{auricblue}{RGB}{24,53,79}
\usepackage[unicode,colorlinks=true,linkcolor=auricblue,urlcolor=auricblue,citecolor=auricblue]{hyperref}
\hypersetup{pdftitle={AURIC v69：共同历史、投影三角形与概率闭包},
pdfauthor={AURIC research continuation},
pdfsubject={Unique source, shared histories, positive-type functions and conditional quantum reconstruction}}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\HH}{\mathcal H}
\newcommand{\Tr}{\operatorname{Tr}}
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
\fancyhead[L]{\small AURIC：共同历史、投影三角形与概率闭包}
\fancyhead[R]{\small v69 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
```

</div>

</details>

# 共同历史、投影三角形与概率闭包

 从唯一本体门脚本到正型关系公理

AURIC 量子起源研究　 定义、定理与纸面证明　 v69.0

2026 年 11 月 1 日　 Asia/Singapore

## 摘要

固定唯一来源 $\Omega$ 与完整门历史，确实单值确定末态。
本文把“共享历史、差向量、球面三角形、纠缠、锁定概率”的直觉组织为一条条件定理链。
两纯态的投影残差平方 $1-|\langle\psi,\phi\rangle|^2$，
等于它们的迹距离平方；在明确的内部相干标签准备下，
它还决定标签约化态的纯度亏损与纠缠。共同相互作用准备所产生的纠缠，
在后续局部酉下保持，但字面共同前缀长度不是纠缠不变量。
两个已标定的相干读出概率可以恢复完整复重叠；当前一个观察面的概率
只确定当前任务等价类，全部允许未来实验概率则确定最粗稳定预测商。
最后把可逆核心压缩为一个群 $\Gamma$ 及其归一正型函数 $f$：
它们与最小循环酉表示精确等价；正交细化的权重条件进一步唯一给出平方概率。
复数正型、实际控制与内部切分仍是有职责的前提，不能因公理写得短就当作已经消除。
DNA 的共同序列适合作为继承记录的类比，不能仅凭共同序列统计认定量子纠缠。
全文为纸面推理，没有运行数学程序、数值计算、模拟、枚举或数学测试。

<!-- v69-note:N1 -->

> **编者注（Markdown 编者，N1）。** 摘要中的“全文”“本轮”及后文关于请求、blob 核对和查读范围的第一人称报告，均属于原作者的原稿记录；转换不把这些历史报告改作编者当前执行记录。原始前言的排版、字体和生产指令逐字保留在上方展开栏，Markdown 本身使用其宿主排版。本文保留纸面条件推论的范围，不把它表述为 kernel、原生控制、物理实现、经验事实、全部上游依赖或无条件量子起源的认证。

<!-- /v69-note -->

## 1. 这一步真正可以推进到哪里

**可以形成更简洁的可逆量子结构表述：
历史有组合，历史之间有一个全局相容的复关系；Hilbert 空间、源向量和酉作用是它的表示。**
但是，“有一个共同来源”本身没有指定这个复关系；
“共享一段脚本”也没有指定哪个内部切分发生了不可分性。

本轮最集中的公式是
<a id="eq:main-chain"></a>

$$
\boxed{
1-q
=\|(I-P_\psi)\phi\|^2
=D(\rho_\psi,\rho_\phi)^2
=\frac{1-\|r_C\|^2}{4p(1-p)} ,
}
$$

(1)

最后一项仅在 $0<p<1$ 且已经准备
$\sqrt p\,\lvert 0\rangle_C\psi_B+\sqrt{1-p}\,\lvert 1\rangle_C\phi_B$ 时成立。
前三项描述两个向量；最后一项描述一个联合态相对于 $C|B$ 的关系。
把这两个类型接起来，需要实际的内部准备，而不是在公式外另加一个观察者。

### 1.1 项目来源和本轮增量

本轮唯一活动 HEAD 请求于新加坡时间 2026-11-01 17:35:10
发生本地 socket 权限拒绝，未收到 HTTP 响应。没有重试或取得更新提交。
下文固定使用已保留并重新核对六份 Git blob 身份的提交
<code>5cf95e1ae01f7ed86735c<wbr>04ad8d752cb19b1a58b</code>。
因此，本文不声称核验了该提交以后的最新进展。

<!-- v69-note:N2 -->

> **编者注（Markdown 编者，N2）。** 17:35:10 的 socket 权限拒绝、未收到 HTTP 响应、未重试及六份 blob 核对，是原作者对原研究时点的报告；它不是本次转换中的网络请求，也不是自动审批拒绝。固定提交是这里项目引用的版本地址，不能由此推断该提交之后的 HEAD 或全部历史依赖已获核验。

<!-- /v69-note -->

<div tabindex="0" role="region" aria-label="原文表格" style="overflow-x:auto">

| 已有项目结果 | 本轮承接方式 |
| --- | --- |
| V22 §§2--8 | 相对门读出、共同先行／后接历史、当前概率商、复历史核、闭路相位及未来概率闭包。 |
| V52 §§2--3 | 两态射线几何、纯态 Bloch 球与投影平方概率。 |
| V56 定理 6.1 | 内部二元切分的三轴纯度亏损；本轮代入两历史相干准备。 |
| V59 §3 | 同域关系一致响应 RC、充分读口轨道及量子正性。 |
| 历史记录卷 §§116--120 | 共同纯档案因子可以任意增长而不改变分支可辨识度。 |
| 静态相融卷 §§3--4、7 | 区别单增历史与可逆执行；目标是合法协议的记录概率。 |

</div>

V22 的核重构、闭路恢复及未来商已经是项目内容；本文不把它们重新命名为首次发现。
新增组织是把投影残差、内生比较器、二元纠缠和正型函数放在同一条证明链中。
GNS、Schmidt 分解及迹距离等均为标准数学；后文给出所用版本的自足证明。
本轮未重审上述各卷的全部历史依赖。

## 2. 唯一来源、历史求值与观察面

#### 定义 2.1（唯一来源与执行约定）

固定一个单位向量 $\Omega$，程序、观察者、记忆、相位参照和环境均在该完整载体内。
门字母 $a$ 已有明确作用地址与酉解释 $U_a$。
按执行先后写历史 $h=a_1\cdots a_n$，约定

$$
U_h=U_{a_n}\cdots U_{a_1},\qquad
\Psi_h=U_h\Omega,\qquad U_{hw}=U_wU_h.
$$

数学上考察不同可允许历史，不表示存在多个实际本体。
实际发生的历史可以仍是一条单增前缀链。

#### 命题 2.2（正向确定性）

给定 $\Omega$、门解释和完整历史 $h$，$\Psi_h$ 唯一且归一。
末态一般不能唯一反解字面门历史。

**证明。**

函数复合单值，且 $\|U_h\Omega\|=\|\Omega\|=1$。
不同执行词可以表示同一个算符；例如完整作用确为恒等的逆门对不改变末态。
如果另有不回滚档案，则档案也须计入完整作用，不能只对工作寄存器消去逆门对。

∎

所以，“无论 $\Omega$ 是什么，固定它和门序列就确定一个态”是正确的。
这不等于概率与该固定来源无关，也不等于我们已经知道 $\Omega$ 的数值表示。
若只给含测量反馈但未指定记录处理的经典脚本，还须给出完整内部控制实现
或明确实际分支，才能把它当作一个已确定的执行。

#### 定义 2.3（相对历史关系）

$$
K(h,k)=\langle\Psi_h,\Psi_k\rangle
=\langle\Omega,U_h^\dagger U_k\Omega\rangle,\qquad
q(h,k)=|K(h,k)|^2.
$$

在后文平方权重条件下，$q$ 是投影到另一条历史所定义射线的概率。

#### 定理 2.4（共同后续保持关系，共同过去制备输入）

<a id="thm:prefix"></a>

共同后接 $w$ 满足

$$
K(hw,kw)=K(h,k).
$$

若两历史从 $\Omega$ 出发先共同执行 $s$，然后分为 $a,b$，令 $\eta=U_s\Omega$，
则

$$
K(sa,sb)=\langle\eta,U_a^\dagger U_b\eta\rangle,\qquad
\Psi_{sb}-\Psi_{sa}=(U_b-U_a)\eta.
$$

共同早期历史一般不能从关系中消去；差算符一般不酉。

**证明。**

第一式消去 $U_w^\dagger U_w=I$。第二式把 $U_{sa}=U_aU_s$、
$U_{sb}=U_bU_s$ 代入。差向量公式是分配律；
当 $U_a=U_b$ 时差算符为零，已足以否定它必为酉。
固定 $\Omega=\lvert 0\rangle$、$U_a=I$、$U_b=Z$：共同准备为 $I$ 时重叠为一，
改为 Hadamard 时共同输入为 $\lvert +\rangle$，重叠为零。
这是固定来源下不同准备的比较。

∎

项目 V22 定理 3.2、命题 3.3 已表达这一区别。[[1](#bib-v22)]
历史记录卷使用的词乘序不同，引用“前缀”时必须先转换成物理执行先后。
真正可保持的对象是关系核；字面公共字符串的长度不是表示无关的物理量。

#### 命题 2.5（观察面可以由门表示，但表示不唯一）

在一个已声明的 $d$ 维内部接口 $S$ 上，固定标准有标签投影 $\Pi_i=\lvert i\rangle\langle i\rvert$。
若完整酉控制已供应，每个有标签正交基观察面均可写为

$$
P_i(V)=V\Pi_iV^\dagger.
$$

给同一完整历史的约化态
$\rho_h^S=\operatorname{Tr} _{S^c}\lvert U_h\Omega\rangle\langle U_h\Omega\rvert$，局部读出为

$$
p_i(h,V)=\operatorname{Tr} _S\!\left(\Pi_iV^\dagger\rho_h^S V\right).
$$

$V$ 与 $VD$ 表示同一观察面，其中 $D$ 为对角相位酉；
反过来，同一完整有标签秩一观察面的两个酉恰相差这种右乘。

**证明。**

把观察基向量作为 $V$ 的列即可。保持每个有标签一维投影的酉只能在每列上乘相位；
反向显然。概率式由迹循环得到。

∎

独立给定若干 $V_i\Omega$ 并不自动得到正交基。
受限门菜单只能实现其中实际可达的观察面；存在一个数学酉不等于已有相应程序。
若 $S$ 本身就是所讨论的完整有限载体，置
$\rho_\Omega=\lvert \Omega\rangle\langle \Omega\rvert$，公式化为项目 V22 的相对门读出：

$$
p_i(h,V)=\operatorname{Tr} \!\left(\Pi_iV^\dagger U_h\rho_\Omega U_h^\dagger V\right).
$$

若 $S$ 是严格内部接口，则只有在实际历史对它确为局部酉时，
才能进一步写 $\rho_h^S=\widetilde U_h\rho_\Omega^S\widetilde U_h^\dagger$。
全局耦合历史一般没有这种局部酉表示。

<!-- v69-note:N3 -->

> **编者注（Markdown 编者，N3）。** 此处内部接口需要一个已指定的张量因子或等价子代数及相应偏迹；写出同一完整态不自动给任意接口一个封闭局部动力学。观察面的唯一性是完整、固定标签、秩一 PVM 的列相位规范；不包括标签置换、高秩块内自由酉或未供应的控制。给定门对所有输入的作用规律、标定一个读口、知道实际来源向量，是三项不同资料。

<!-- /v69-note -->

## 3. 两态的直角三角形与稳定概率

#### 定义 3.1（两态几何）

以下 $\psi,\phi$ 是同一 Hilbert 空间中的单位向量，内积对第二变量线性。
令

$$
c=\langle\psi,\phi\rangle,\quad q=|c|^2,\quad
P_\psi=\lvert \psi\rangle\langle \psi\rvert,\quad \theta=\arccos|c|\in[0,\pi/2].
$$

两向量张成至多二维复子空间；其射线几何可用一个 qubit Bloch 球表示。
这不意味着任意高维态族的全部关系都能无损放入同一个三实维球。

<!-- v69-note:N4 -->

> **编者注（Markdown 编者，N4）。** 当两条射线相同，跨度是一维；可嵌入一个二元载体表示同一个 Bloch 点，不能凭空增加可用端口。投影三角形在 $q=0$ 或 $q=1$ 时允许退化。相位对齐在 $c=0$ 时任取相位；若 $\phi=-\psi$，未对齐的中点为零，实正交恒等式仍成立。下述二维行列式论证的所列正交基只在 $q<1$ 时使用，$q=1$ 已单独处理；$q=0$ 给 $D=1$、射线角 $\pi/2$，$q=1$ 给 $D=0$、射线角零。

<!-- /v69-note -->

#### 定理 3.2（投影三角形）

<a id="thm:triangle"></a>

设 $\eta_\perp=(I-P_\psi)\phi$，则

$$
\boxed{\phi=c\psi+\eta_\perp,\qquad
\langle\psi,\eta_\perp\rangle=0,\qquad
|c|^2+\|\eta_\perp\|^2=1.}
$$

因而顶点 $0,c\psi,\phi$ 构成正交投影三角形，两条直角边平方为 $q,1-q$。
原始差向量则为

$$
\phi-\psi=(c-1)\psi+\eta_\perp,\qquad
\Re\langle\psi,\phi-\psi\rangle=-\tfrac12\|\phi-\psi\|^2.
$$

除两向量相同外，原始差不垂直于原向量。

**证明。**

$P_\psi\phi=c\psi$，所以正交性直接成立。
Pythagoras 给范数分解。又
$\|\phi-\psi\|^2=2-2\Re c$，而
$\Re\langle\psi,\phi-\psi\rangle=\Re c-1$，得到最后一式。

∎

#### 命题 3.3（球面弦的另一种直角三角形）

令 $m=(\psi+\phi)/2$、$d=(\phi-\psi)/2$。则

$$
\Re\langle m,d\rangle=0,\qquad \|m\|^2+\|d\|^2=1.
$$

选整体相位使 $\langle\psi,\phi'\rangle=|c|$ 后，相应 $m',d'$ 还满足复正交
$\langle m',d'\rangle=0$。

**证明。**

展开得 $\langle m,d\rangle=(c-\bar c)/4$；
范数和由平行四边形恒等式得到。相位对齐后 $c$ 为实，复内积也为零。

∎

所以球面弦的中点、原点和弦端点确实给直角三角形，
但它与“原点、两个原始单位向量端点”的三角形不是同一组顶点。

#### 定理 3.4（投影残差等于最大读出差）

<a id="thm:distance"></a>

记 $\rho_\psi=\lvert \psi\rangle\langle \psi\rvert$、$\rho_\phi=\lvert \phi\rangle\langle \phi\rvert$。
则

$$
\boxed{
D(\rho_\psi,\rho_\phi)
 :=\tfrac12\|\rho_\psi-\rho_\phi\|_1
 =\sqrt{1-q}
 =\sup_{0\le E\le I}|\operatorname{Tr}  E(\rho_\psi-\rho_\phi)|.
}
$$

此外

$$
\min_\alpha\|\psi-e^{i\alpha}\phi\|
=\sqrt{2-2|c|}=2\sin(\theta/2).
$$

若在两态所在 qubit 空间使用纯态 Bloch 向量 $r_\psi,r_\phi$，则

$$
r_\psi\cdot r_\phi=2q-1=\cos(2\theta),\qquad
\|r_\psi-r_\phi\|=2\sqrt{1-q}.
$$

**证明。**

令 $\Delta=\rho_\psi-\rho_\phi$。在 $\operatorname{span} \{\psi,\phi\}$ 内，
$\operatorname{Tr} \Delta=0$，以 $\psi,\eta_\perp/\sqrt{1-q}$ 为基可得
$\det\Delta=-(1-q)$；故两个非零候选特征值是 $\pm\sqrt{1-q}$。
$q=1$ 时 $\Delta=0$，结论同样成立。
设正负特征向量为 $u_+,u_-$，则
$\operatorname{Tr}  E\Delta=\sqrt{1-q}(\langle u_+,Eu_+\rangle-\langle u_-,Eu_-\rangle)$，
绝对值不超过 $\sqrt{1-q}$；取正谱投影达到上界。
相位优化使 $\Re(e^{i\alpha}c)=|c|$，给弦长公式。
最后 $\rho=(I+r\cdot\sigma)/2$ 与 Pauli 迹恒等式给
$\operatorname{Tr} (\rho_\psi\rho_\phi)=(1+r_\psi\cdot r_\phi)/2=q$，
纯态 $\|r\|=1$，即得余式。

∎

<div tabindex="0" role="region" aria-label="原文表格" style="overflow-x:auto">

| 几何量 | 精确表达 |
| --- | --- |
| 射线角（本文约定） | $\theta=\arccos\sqrt q$ |
| 单位 Hilbert 球上的相位最优弦长 | $2\sin(\theta/2)$ |
| 投影残差／全部效果的最大概率差 | $\sin\theta=\sqrt{1-q}$ |
| qubit Bloch 球上的中心角 | $2\theta$ |
| qubit Bloch 球上的弦长 | $2\sin\theta$ |

</div>

这是“锁定一个概率”确实能给出的强结论：锁定 $q$ 就锁定全部效果下的最大概率差。
但固定 $0<q<1$ 并不确定完整态；例如
$\sqrt q\,\lvert 0\rangle+e^{i\alpha}\sqrt{1-q}\,\lvert 1\rangle$
对所有 $\alpha$ 都给同一 $\lvert 0\rangle$ 投影概率。
迹距离的操作意义是标准 Holevo--Helstrom 结构的纯态情形。[[8](#bib-watrous)]
项目 V52 已有相应 Bloch--射线关系。[[2](#bib-v52)]

<!-- v69-note:N5 -->

> **编者注（Markdown 编者，N5）。** “全部效果”指同一载体上所有有界算子效果 $0\le E\le I$ 的数学上确界，正谱投影达到它；受限实际读口族的最大差可以更小。任意 Hilbert 空间中这两个纯态投影的差仍至多秩二，所以该迹范数与效果论证有效。Bloch 中心角为射线角的两倍，不能把两种球的弦长相混。

<!-- /v69-note -->

## 4. 共同历史何时真正对应纠缠？

#### 定义 4.1（内部切分与纠缠）

纠缠属于一个联合态相对于已声明内部切分 $A|B$ 的性质。
联合纯态不可写成 $\alpha_A\otimes\beta_B$ 时，称其在该切分纠缠。
两个备选的全局历史末态 $\Psi_h,\Psi_k$，尚不是一个已经定义的联合态。
声明内部切分并不引入第二本体；它是在同一完整载体内指定哪些读口属于哪一侧。

#### 定理 4.2（共同准备的纠缠继承）

若实际共同准备为 $\Xi=S\Omega$，且其后只有内部局部门 $U_A\otimes U_B$，
则所有 Schmidt 系数保持。因此当前纠缠完全继承该共同准备。

**证明。**

写 Schmidt 分解
$\Xi=\sum_j\sqrt{\lambda_j}\lvert a_j\rangle\lvert b_j\rangle$。
两个局部酉分别保持两组基的正交性，故

$$
(U_A\otimes U_B)\Xi=\sum_j\sqrt{\lambda_j}
U_A\lvert a_j\rangle\otimes U_B\lvert b_j\rangle
$$

仍为相同系数的 Schmidt 分解。

∎

<!-- v69-note:N6 -->

> **编者注（Markdown 编者，N6）。** 这里讨论 Hilbert 张量积中的单位向量；有限维是有限 Schmidt 和，一般 Hilbert 因子中的单个向量也只有至多可数个非零 Schmidt 系数，其和按范数收敛。理由是该向量对应的 Hilbert–Schmidt 算子是紧算子，其非零奇异值至多可数；局部酉保留这些奇异值。此论证不把混合态、一般代数态或未指定张量切分纳入“纯态 Schmidt 分解”。

<!-- /v69-note -->

这是“共同过去承载关系”的准确版本。
共同准备可能产生乘积态，也可能产生纠缠态；决定因素是准备在指定切分上的作用。
若后来有跨切分相互作用，它也能改变纠缠，不能继续套用局部继承结论。

#### 定义 4.3（内生两历史相干准备）

<a id="def:internal"></a>

在同一完整载体内声明 $C|B$，其中 $\mathcal{H} _C\simeq\mathbb{C} ^2$。
取 $0\le p\le1$、$\|\eta\|=1$、$V_0,V_1\in U(\mathcal{H} _B)$，
并明确供应准备和控制操作：

$$
G_{\rm prep}\Omega
=(\sqrt p\,\lvert 0\rangle+\sqrt{1-p}\,\lvert 1\rangle)_C\otimes\lvert \eta\rangle_B,
$$

$$
W=\lvert 0\rangle\langle 0\rvert_C\otimes V_0+\lvert 1\rangle\langle 1\rvert_C\otimes V_1 .
$$

令 $\psi=V_0\eta$、$\phi=V_1\eta$、$c=\langle\psi,\phi\rangle$。执行后

$$
\Xi=W G_{\rm prep}\Omega
=\sqrt p\,\lvert 0\rangle_C\psi_B+\sqrt{1-p}\,\lvert 1\rangle_C\phi_B .
$$

这里 $\psi,\phi$ 是内容端口 $B$ 上的纯分支；没有把完整宇宙 $\Omega$
再复制为免费的外部 $\lvert +\rangle\otimes\Omega$。
若存在未清除的程序或历史残余，它们须并入 $B$，并计入分支重叠。

<!-- v69-note:N7 -->

> **编者注（Markdown 编者，N7）。** 所写 $G_{\rm prep}$、受控 $W$、标签的相位参照和后文 $X,Y,H$ 读口，都是同一完整载体中已经供应的操作；数学上存在送一个单位向量到另一个的酉，不能证明受限原生菜单可以实现它。准备式要求标签与内容端口处于所写乘积就绪态，且所有剩余端口均已计入；若残余含分支信息，不能只计算较小内容系统的重叠。

<!-- /v69-note -->

#### 定理 4.4（投影残差与内部纠缠的桥梁）

<a id="thm:entanglement"></a>

在定义 [4.3](#def:internal) 中，令 $q=|c|^2$。则

$$
\rho_C=
\begin{pmatrix}
p&\sqrt{p(1-p)}\,\bar c\\
\sqrt{p(1-p)}\,c&1-p
\end{pmatrix},
$$

$$
\boxed{\det\rho_C=p(1-p)(1-q),\qquad
1-\operatorname{Tr} \rho_C^2=2p(1-p)(1-q).}
$$

写 $\rho_C=(I+r_C\cdot\sigma)/2$，有

$$
r_C=\bigl(2\sqrt{p(1-p)}\Re c,\;
2\sqrt{p(1-p)}\Im c,\;2p-1\bigr),
$$

$$
\boxed{1-\|r_C\|^2=4p(1-p)(1-q).}
$$

联合纯态纠缠当且仅当 $0<p<1$ 且 $q<1$。

**证明。**

对 $B$ 取偏迹，直接得到 $\rho_C$；其行列式为上述表达。
任意迹一二阶矩阵满足
$\operatorname{Tr} \rho_C^2=(\operatorname{Tr} \rho_C)^2-2\det\rho_C=1-2\det\rho_C$。
Pauli 表示给 $\operatorname{Tr} \rho_C^2=(1+\|r_C\|^2)/2$，得到三轴公式。
纯联合态可分当且仅当约化态秩一；在非零两分支下这等价于行列式为零，
也等价于 Cauchy--Schwarz 等号 $\phi=e^{i\alpha}\psi$。

∎

<!-- v69-note:N8 -->

> **编者注（Markdown 编者，N8）。** 采用标准 $\sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$ 与第二变量线性内积，$01$ 元是 $\sqrt{p(1-p)}\,\bar c$，故 $y$ 轴是正号 $2\sqrt{p(1-p)}\operatorname{Im}c$。$p=0,1$ 时约化标签纯且联合态为乘积，公式的亏损都为零，不得在式 (1) 的分母中代入这些端点；$q=1$ 时两内容射线共线，$q=0$ 且 $0<p<1$ 时两非零 Schmidt 权重为 $p,1-p$。

<!-- /v69-note -->

这正是项目 V56 定理 6.1 对
$u=\sqrt p\,\psi$、$v=\sqrt{1-p}\,\phi$ 的特例。[[3](#bib-v56)]
其三轴属于所声明的二元接口；若要把它写成原 AURIC 五模式的具体读出，
还须使用明确的编码映射，不能把任意三轴数值直接改名为原模式坐标。

当 $p=1/2$ 时，

$$
\|r_C\|^2=q,\qquad D(\rho_\psi,\rho_\phi)^2+\|r_C\|^2=1.
$$

标签可见相干与内容分支可辨识度由同一关系约束。
这是一条有明确切分与准备的恒等式，而不是从共同前缀的字面长度计算纠缠。

#### 命题 4.5（共同纯记录因子消去）

若两分支为 $\psi=\gamma\otimes a$、$\phi=\gamma\otimes b$，
其中 $\|\gamma\|=1$，则 $\langle\psi,\phi\rangle=\langle a,b\rangle$。
在上述相干标签准备中，添加任意长的相同纯记录因子，不改变 $\rho_C$
及 $C|B$ 的 Schmidt 系数。

**证明。**

张量内积给第一式，代入定理 [4.4](#thm:entanglement) 得第二结论；
更直接地，联合态只是原联合态再乘一个纯因子。

∎

历史记录卷定理 118.2--118.3 已给共同档案增长而区分统计不变的具体结构。[[5](#bib-history)]
若共同前缀中有跨切分相互作用，或记录并非共同纯因子，则要重新计算，不能省略。

## 5. “锁定概率”需要锁定哪一组概率？

### 5.1 两个经过标定的概率恢复一个复关系

#### 定理 5.1（内部比较器与差向量的实现）

<a id="thm:comparator"></a>

在定义 [4.3](#def:internal) 中取 $p=1/2$，并供应相位已标定的 $X,Y$ 标签读口。
则

$$
p_X^+=\frac{1+\Re c}{2},\qquad
p_Y^+=\frac{1+\Im c}{2},\qquad
\boxed{c=(2p_X^+-1)+i(2p_Y^+-1).}
$$

对标签施 Hadamard 后，

$$
(H_C\otimes I_B)\Xi
=\lvert 0\rangle_C\frac{\psi+\phi}{2}
 +\lvert 1\rangle_C\frac{\psi-\phi}{2}.
$$

因此差向量可以作为相干比较器的未归一条件分支出现。

**证明。**

定理 [4.4](#thm:entanglement) 给
$\rho_C=\tfrac12\left(\begin{smallmatrix}1&\bar c\\c&1\end{smallmatrix}\right)$。
与 $(I+\sigma_x)/2$、$(I+\sigma_y)/2$ 配对即得两个概率。
Hadamard 的两列是 $(1,1)^T/\sqrt2$ 和 $(1,-1)^T/\sqrt2$，
代入即可。两个分支权重分别为 $(1+\Re c)/2$ 与 $(1-\Re c)/2$。

∎

**所以概率本身不缺少相位；缺少相位的是某些过小的概率表。**
相干读口把复关系转换成普通二元概率。
此实验恢复的是已声明内容端口的核，不自动供应对包含比较器自身的任意全宇宙历史的相干控制。
受控 $e^{i\alpha}V_1$ 与受控 $V_1$ 可以有不同统计；
因此只知道无控制通道 $\rho\mapsto V_1\rho V_1^\dagger$，
不足以指定受控实现中的相对相位。

<!-- v69-note:N9 -->

> **编者注（Markdown 编者，N9）。** 比较器恢复的是该准备中固定相位约定下的内容重叠。Hadamard 的两条件分支未归一，减支为 $\psi-\phi$ 而不是原几何中 $\phi-\psi$，两者差整体负号；权重为 $(1\pm\operatorname{Re}c)/2$，为零的分支没有归一条件态。受控支路上的相位是相对相位；未受控通道消去的整体相位不能决定它。

<!-- /v69-note -->

### 5.2 当前观察面的精确充分性

#### 命题 5.2（固定基概率是当前读出商）

对一套固定有标签正交基，两个纯向量
$z=\sum_i z_i\lvert i\rangle$、$z'=\sum_i z'_i\lvert i\rangle$
有相同当前概率向量，当且仅当存在对角相位酉 $D$ 使 $z'=Dz$。

**证明。**

相同概率等价于 $|z_i|=|z'_i|$。
对非零分量逐个选择 $e^{i\alpha_i}=z'_i/z_i$；零分量相位任意。
反向由模长不变成立。

∎

这就是项目 V22 当前观察商的具体形式。[[1](#bib-v22)]
它对这个当前任务完全足够；但逐坐标相位可能被后续门读出。
例如 $\lvert +\rangle$ 与 $\lvert -\rangle$ 在 $Z$ 基概率相同，追加同一 Hadamard 后，
再测 $Z$ 分别确定得到 $0,1$。
V22 定理 8.3 已有原生黄金门版本：
同一来源的 $K$ 与 $K^9$ 历史当前五模式人口相同，
共同追加 $K$ 后某模式概率分别为 $\varphi^{-4}$ 与 $1$；
这里引用其结论，不把本轮当作该原生门推导的首次证明。

<!-- v69-note:N10 -->

> **编者注（Markdown 编者，N10）。** 固定 V22 定理 8.3 的来源是模式 $|2\rangle$，两历史分别为 $K|2\rangle$ 与 $K^9|2\rangle$，共同再施 $K$ 后比较模式 2：分别是 $\varphi^{-4}$ 与一。其引理 7.2 在所声明完整五模式门上给 $K^{10}=I$ 和 $K^{-1}=K^9$。这些算符身份不适用于另附不回滚时钟的完整门，也不声称任意相干接口都有免费的精确原生编译。

<!-- /v69-note -->

### 5.3 全部两两投影概率仍可能遗漏闭路相位

#### 定义 5.3（历史闭路量）

对单位向量族 $\psi_i$，置
$K_{ij}=\langle\psi_i,\psi_j\rangle$，
$t_{ij}=|K_{ij}|^2$，
$B_{ijk}=K_{ij}K_{jk}K_{ki}$。
共同酉及逐态整体相位重选均保持 $B_{ijk}$。

#### 命题 5.4（相同两两概率不唯一确定相干历史族）

取 $\psi_0=\lvert 0\rangle$、$\psi_1=\lvert +\rangle$、$\psi_2=\lvert +i\rangle$，
其中 $\lvert +i\rangle=(\lvert 0\rangle+i\lvert 1\rangle)/\sqrt2$。
三个非对角 $t_{ij}$ 均为 $1/2$，而

$$
B_{012}=(1+i)/4.
$$

把第三态改为 $\lvert -i\rangle$，全部这些概率不变，却有
$B_{012}=(1-i)/4$。两个有标签族不能由共同酉加逐态相位联系。

**证明。**

三个顺向内积分别是 $1/\sqrt2$、$(1+i)/2$、$1/\sqrt2$；
相乘即得。复共轭改变闭路量但不改模平方。
若两族由共同酉加顶点相位联系，闭路量必须相同，矛盾。

∎

项目 V22 §7 已给原生黄金例子及修复方案。[[1](#bib-v22)]
对于非零边图，边模长加全部有向闭路乘积，决定 Gram 核的逐顶点相位规范类。
证明可逐连通分量选生成树，用顶点相位使两核的树边相同；
每条非树边再由它与树路径构成的闭路确定。
若某锚点 $0$ 与所有点重叠非零，选规范 $K_{0i}>0$，
只需三角闭路便有

$$
K_{ij}=\frac{B_{0ij}}{|K_{0i}|\,|K_{0j}|}.
$$

存在零边时，不能假定三角闭路总足够，须保留实际图上的全部必要闭路。
这说明关系的取向也有数据内容，但不构成物理宇称破缺的证明。

<!-- v69-note:N11 -->

> **编者注（Markdown 编者，N11）。** 两个核须具有同一标签、零边模式和边模长，才能作这个规范类比较。V22 定理 7.7 明列有限标签；对于更大图，若选择各连通分量的生成森林，同一论证逐有限树路径与有限闭路成立，不涉及无限闭路乘积或无条件有限数据重构。锚点分母须非零；顶点相位的常数自由度逐连通分量保留。若标签处于受控叠加，规范变换还须补偿程序系数，不能物理删去可干涉相位。

<!-- /v69-note -->

### 5.4 全部未来实验概率给最粗稳定预测商

#### 定义 5.5（未来效果闭包）

把影响未来的程序、记忆和参照全部纳入同一个有限内部接口。
令结束效果集合 $\mathscr E$ 含 $I$，允许的历史含空历史，
并由处处合法的酉菜单对有限串接封闭。
定义

$$
\mathscr E_\infty=\{U_w^\dagger EU_w:\ E\in\mathscr E,\ w\text{ 为允许历史}\},
\qquad
\mathcal S=\operatorname{span} _{\mathbb{R} }\mathscr E_\infty.
$$

若所有这些效果的响应相同，记为 $\rho\sim_\infty\sigma$。

#### 定理 5.6（预测商与层析完备性）

<a id="thm:future"></a>

$$
\boxed{\rho\sim_\infty\sigma
\iff \rho-\sigma\in\mathcal S^\perp.}
$$

此关系是保留当前读出且对全部共同允许后继稳定的最粗等价关系。
在整个密度态空间上，

$$
\boxed{
(\rho\sim_\infty\sigma\Rightarrow\rho=\sigma)
\iff \mathcal S=\operatorname{Herm} (\mathcal{H} ).
}
$$

**证明。**

效果响应相等对实线性张成保持，故得到第一式。
串接封闭给 $U^\dagger\mathcal S U\subseteq\mathcal S$，于是

$$
\operatorname{Tr} \!\left(U(\rho-\sigma)U^\dagger A\right)
=\operatorname{Tr} \!\left((\rho-\sigma)U^\dagger AU\right)=0
$$

对 $A\in\mathcal S$ 成立。
任何保留当前响应并对每一步稳定的等价关系，按词长归纳都保留全部未来响应，
故其等价类只能更细。

若 $\mathcal S=\operatorname{Herm} (\mathcal{H} )$，差矩阵与自身迹正交，故为零。
若不全张成，取非零 Hermitian $H\in\mathcal S^\perp$。
因 $I\in\mathcal S$，$\operatorname{Tr}  H=0$。对充分小的 $\epsilon>0$，
$\rho_\pm=I/d\pm\epsilon H$ 均为密度态；
它们不同但全部未来响应相同，得到必要性。

∎

<!-- v69-note:N12 -->

> **编者注（Markdown 编者，N12）。** 此定理取有限非零载体 $d\ge1$，正交补是 Hermitian 实空间中迹配对 $\operatorname{Tr}(HA)$ 的正交补。小扰动可明确取 $0<\epsilon<1/(d\|H\|_{\rm op})$；$d=1$ 且含 $I$ 时已全张成，不存在所述非零 $H$。按本文执行词约定，先施 $U$ 再施历史 $w$ 给 $U_wU$，所以回拉为 $U^\dagger U_w^\dagger EU_wU$，正是闭包中的一个效果。无限维时没有这里的 $I/d$ 内点论证，不能照搬必要性的证明。

<!-- /v69-note -->

这承接 V22 定理 8.4 及静态相融卷的合法未来目标族。[[1](#bib-v22), [6](#bib-static)]
若只考虑一个较小可达态族，“全部 Hermitian 张成”仍充分，
但未必必要。若未来包含细粒仪器，则使用记录词与结束事件的联合概率：
$\operatorname{Tr} (\rho K_w^\dagger EK_w)$。
若一个可见记录词 $w$ 还包含未读微指标 $\alpha$，
则用效果 $\sum_\alpha K_{w\alpha}^\dagger EK_{w\alpha}$；
不能把一般粗粒仪器默认为单 Kraus 分支。
这同时保存正概率分支的条件概率；零概率分支不定义归一条件态。
若合法性依赖状态或记忆，合法性本身也须进入接口描述。

<!-- v69-note:N13 -->

> **编者注（Markdown 编者，N13）。** 仪器版本使用每个可见记录词及结束事件的联合概率，微指标是给定可见词的一整串未读细标签；反馈算子也须依赖已读的同一记录。先求各细路径的 $K_{w\alpha}^\dagger E K_{w\alpha}$ 再求和，不能先相加振幅而引入未供应的相干。相同联合概率及记录概率之比给正概率条件分布；零记录概率只保留未归一分支。处处合法与依赖接口状态的部分操作不能混用。

<!-- /v69-note -->

**一个实验的单次 $0/1$ 记录不等于已精确知道该实验的概率。**
这些定理描述理想响应或已给定的数学模型；从有限数据估计它们还需要统计条件。

## 6. 更简洁的可逆核心：一个群和一个正型函数

### 6.1 为何换成相对历史关系

完整门矩阵逐一给定，是一种坐标表达。
若目标只是唯一来源所生成的可逆历史关系，可以改从

$$
\boxed{(\Gamma,f)}
$$

出发。$\Gamma$ 记录已声明可逆执行的组合，$f$ 记录来源相对于相对执行的复关系。
它不会自动记录每次相同门出现的事件身份。
字面脚本、永久历史档案和可逆执行标签是不同层；
原生只有正词的实际菜单，也不能免费扩大为可实现逆元菜单。

#### 定义 6.1（归一正型历史关系）

<a id="def:positive"></a>

给一个离散群 $\Gamma$，约定乘积 $gh$ 表示先执行 $h$，后执行 $g$。
函数 $f:\Gamma\to\mathbb{C}$ 满足

$$
f(e)=1,\qquad
\boxed{[\,f(g_i^{-1}g_j)\,]_{i,j=1}^n\succeq0}
$$

对任意有限历史族成立，称为归一正型函数。
矩阵半正定包含 Hermitian 要求。记
$K(g,h)=f(g^{-1}h)$，则自动有

$$
K(ag,ah)=K(g,h).
$$

这是把“共同后续保持全部复关系”放进相对历史的定义；
不只保持每个态自己的范数，也保持任意历史组合的交叉项。
公理虽短，却包含所有有限历史族的相容条件。

#### 定理 6.2（正型关系与唯一来源的循环酉表示）

<a id="thm:gns"></a>

每个 $(\Gamma,f)$ 产生 Hilbert 空间 $\mathcal{H} _f$、单位来源 $\Omega_f$ 和酉表示
$\pi_f:\Gamma\to U(\mathcal{H} _f)$，满足

$$
\boxed{f(g)=\langle\Omega_f,\pi_f(g)\Omega_f\rangle,\qquad
K(g,h)=\langle\pi_f(g)\Omega_f,\pi_f(h)\Omega_f\rangle,}
$$

$$
\overline{\operatorname{span} }\{\pi_f(g)\Omega_f:g\in\Gamma\}=\mathcal{H} _f.
$$

该循环实现在保持来源和群作用的酉等价意义下唯一。
反过来，每个具有单位循环来源的酉表示都产生这样的正型函数。

**证明。**

**第一步：由关系定义半内积。**
取群标签的有限形式线性组合空间，定义

$$
\left\langle\sum_i a_i[g_i],\sum_j b_j[h_j]\right\rangle_f
=\sum_{i,j}\bar a_i b_j f(g_i^{-1}h_j).
$$

正型保证非负。半内积的 Cauchy--Schwarz 不等式由
$\langle x+ty,x+ty\rangle_f\ge0$ 对所有复数 $t$ 成立得到。
因此零范数向量与所有向量正交，零空间 $N$ 是线性子空间。
商掉 $N$ 再完成，得到 $\mathcal{H} _f$。

**第二步：左平移成为酉。**
令 $L_a[g]=[ag]$。由于
$(ag)^{-1}(ah)=g^{-1}h$，左平移保持半内积，故保持零空间，
下降为商空间等距并延拓到完成。
群中已有逆元 $a^{-1}$ 给出 $L_{a^{-1}}L_a=I$，所以等距满射，确为酉。
且 $L_aL_b=L_{ab}$，令 $\pi_f(a)=L_a$。

**第三步：来源和循环性。**
令 $\Omega_f=[e]+N$，则其范数平方为 $f(e)=1$，
且 $\pi_f(g)\Omega_f=[g]+N$。
这些向量的线性组合按构造稠密，并直接给出两个表示公式。

**第四步：唯一性。**
若 $(\mathcal{H} ',\pi',\Omega')$ 是另一循环实现，定义

$$
T\!\left(\sum_i a_i\pi_f(g_i)\Omega_f\right)
=\sum_i a_i\pi'(g_i)\Omega'.
$$

两侧所有 Gram 矩阵同为 $[f(g_i^{-1}g_j)]$，故 $T$ 良定义并保内积。
循环性使像稠密，等距延拓后像又闭，故 $T$ 为满射酉；
它保持来源并交织群作用，且在稠密循环跨度上已被唯一规定。

**第五步：反向。**
若已有单位来源与酉表示，定义
$f(g)=\langle\Omega,\pi(g)\Omega\rangle$。则

$$
\sum_{i,j}\bar a_i a_j f(g_i^{-1}g_j)
=\left\|\sum_i a_i\pi(g_i)\Omega\right\|^2\ge0,
$$

且 $f(e)=1$。得证。

∎

这是群正型函数的标准 GNS 构造，亦是 V22 历史核重构的可逆齐次特例。[[7](#bib-gns), [1](#bib-v22)]
本轮的压缩在于：不再把每个门的矩阵、Hilbert 坐标和共同后续守恒分别列出；
群结构与正型关系自动提供它们。
但若作用载体还有来源从未生成的正交补，$f$ 并不决定那个补空间。
门表示也不保证忠实；不同执行标签可能有相同表示。

<!-- v69-note:N14 -->

> **编者注（Markdown 编者，N14）。** 此处群是离散群，有限支撑线性组合及所有有限族正性已经覆盖任意群大小；不要求预先有限维或可分，也未声称非离散拓扑下的强连续性。正型的二阶块给 $f(g^{-1})=\overline{f(g)}$；半内积的零范数向量与全部向量正交，故商和左平移同时良定义。逆元使完成后的等距满射；循环性使唯一交织等距的像既稠密又闭，因此是酉。最小性仅为循环生成部分，不是物理资源或实际宇宙的最小性。MIT 讲义定理 4.1 从 C*-代数的态出发，并以第一变量线性的 $\langle a,b\rangle=\varphi(b^*a)$ 写式；这里按第二变量线性的群核自足证明，不能把二者的公式逐字等同。

<!-- /v69-note -->

### 6.2 二元关系必须有全局相容性

#### 命题 6.3（每一对都合法，不保证整体合法）

二历史归一核
$\left(\begin{smallmatrix}1&c\\\bar c&1\end{smallmatrix}\right)$
半正定当且仅当 $|c|\le1$。
但是，对角元全为一、所有非对角元全为 $-3/4$ 的三阶 Hermitian 矩阵，
其每个二阶主块都正定，而整个矩阵不是半正定。

**证明。**

二阶块特征值为 $1\pm|c|$。
三阶例子的任意二阶主块特征值为 $1/4,7/4$；
然而向量 $(1,1,1)^T$ 的二次型为 $3-6(3/4)=-3/2<0$。

∎

<!-- v69-note:N15 -->

> **编者注（Markdown 编者，N15）。** 此二阶示例用 $c$ 表示右上角，左下角为其共轭；若沿用先前 $\rho_C$ 的下左角参数则须交换共轭记法。半正定条件与特征值不受这项参数选择影响。三阶反例只说明成对正性不足，归一正型公理仍要求每个有限阶矩阵，包括重复群标签所给的全部相容约束。

<!-- /v69-note -->

因此“所有关系可逐个二元分析”可以作为分析方法，
但独立满足每个二元三维模块的局部约束，不能替代所有模块合在一起的正型条件。
高维结构在这里由整个 Gram 核的秩和相容关系承载；
它不会因为每一步只有两个输入就自动降成全局三实维。

### 6.3 平方概率从哪一个额外条件推出？

#### 定义 6.4（正交细化权重条件 W）

在所重构空间的归一化分支域中，假定权重仅依赖向量范数：
$w(v)=F(\|v\|^2)$，$F:[0,1]\to[0,\infty)$，且 $F(1)=1$。
这里用范数平方作自变量尚未指定 $F$；任意仅依赖范数的权重都可这样改写。
对于任意 $x,y\ge0$、$x+y\le1$，允许的正交细化满足

$$
F(x+y)=F(x)+F(y).
$$

这要求相应正交分支的供应足够；只给少数离散分支不自动满足这个全域前提。

#### 定理 6.5（平方权重的唯一性）

<a id="thm:born"></a>

条件 W 强制 $F(x)=x$。故

$$
\boxed{w(v)=\|v\|^2,\qquad
p_i(\psi)=\|P_i\psi\|^2,\qquad
\sum_i p_i=1}
$$

对任意已供应的正交投影分解成立。

**证明。**

可加性给 $F(0)=0$，非负性给单调性：
若 $y\ge x$，则 $F(y)-F(x)=F(y-x)\ge0$。
由 $nF(1/n)=F(1)=1$ 得 $F(m/n)=m/n$。
用有理数从下、上夹任意实数 $x\in[0,1]$，单调性强制 $F(x)=x$。
投影分量正交，故平方范数和为 $\|\psi\|^2=1$。

∎

<!-- v69-note:N16 -->

> **编者注（Markdown 编者，N16）。** W 的可加性是对整个实区间的假设；空间或实际制备若不能供应相应正交细分，就不能仅凭有限离散菜单声称已满足 W。归一分支域含零向量及平方范数不超过一的向量；夹逼使用的是 $F$ 的非负性所推出的单调性，不另需连续性。有限 PVM 的和按普通求和；可数 PVM 须以强算子和为 $I$，则 $P_i\psi$ 的正交范数和按 Parseval 收敛为一。更大正交族对固定向量仅至多可数项非零，可用有限部分和的上确界解释；连续谱 PVM 则应使用谱测度，不把本文离散和直接当作积分。

<!-- /v69-note -->

这里平方几何已由复正型关系承担；定理证明的是在正交细化与方向无关的权重条件下，
这种几何如何唯一成为概率。它不是从“二元”或“归一化”两个词单独推导指数二。
若不要求这些相容条件，当然可以写
$|\psi_i|^p/\sum_j|\psi_j|^p$ 等归一表达，只是它们一般不满足上述同一内积几何下的正交细化与酉相容性。

<!-- v69-note:N17 -->

> **编者注（Markdown 编者，N17）。** 此处的 $p$ 是另取的幂指数，不是相干准备的分支先验。作为明确的归一表达，可在有限基、非零输入和实指数 $p>0$ 下使用；可数基还须分母有限且非零。$p=2$ 给本文的平方权重，其他幂通常改变正交合并后的权重；零振幅上的零次或负次幂不能无定义地代入。

<!-- /v69-note -->

### 6.4 与项目 V59 的响应公理对应

另一路径是先给同一内部关系代数 $M_d(\mathbb{C} )$，再规定概率响应。
设效果域实线性张成全部 Hermitian 空间，含 $I$，并满足同域 RC：

$$
\sum_j a_jE_j=0\quad\Longrightarrow\quad\sum_j a_jp(E_j)=0,
\qquad p(I)=1.
$$

则 $p$ 唯一延拓为实线性泛函；非退化迹配对给唯一 Hermitian $R$，
使 $p(E)=\operatorname{Tr} (RE)$、$\operatorname{Tr}  R=1$。
若一个非零秩一读口的允许回拉轨道覆盖或稠密于全部纯方向，并且响应非负，
则 $\langle\phi,R\phi\rangle\ge0$ 对所有方向成立，从而 $R\ge0$。
因此 $R$ 是密度矩阵。这就是项目 V59 定理 3.2--3.3 的职责。[[4](#bib-v59)]

W 是从向量几何到分支权重的桥；RC 加充分正性读口是从相容响应到密度态的桥。
二者都是有条件的表述，不能混成“测得一个概率数值就确定整个理论”。
对 qubit，三个已标定轴概率确定
$r_a=2p_a^+-1$；三个概率分别在 $[0,1]$ 只给一个立方体，
整体正性另要求 $\|r\|\le1$。

<!-- v69-note:N18 -->

> **编者注（Markdown 编者，N18）。** RC 仅比较同一 $M_d(\mathbb{C})$、同一准备与同一条件化域上的有限实线性关系；差表示的零关系给泛函良定义，有限维非退化迹配对给 Hermitian 代表。秩一读口必须是固定正增益乘秩一投影，回拉效果须属于该实际域，覆盖或稠密的拓扑为有限维投影拓扑；连续迹泛函才把轨道上的非负性推广到全部方向。高秩信息完备读口能分离候选矩阵，却未必认证其正性，如 V59 命题 3.5 所区分。

<!-- /v69-note -->

## 7. 记录、经典结果与 DNA 类比的准确层次

### 7.1 同一来源下的测量和条件读出

在内部准备容量与记录读口已供应的条件下，一般有限仪器可由

$$
V\psi=\sum_{r,\alpha}M_{r\alpha}\psi\otimes\lvert r\rangle_R\otimes\lvert \alpha\rangle_J,
\qquad \sum_{r,\alpha}M_{r\alpha}^\dagger M_{r\alpha}=I
$$

等距表示，并在足够的内部就绪空间中扩充为酉 $U_{\rm m}$。
$R$ 是可见记录，$J$ 是同一整体内未读的细指标。
令 $Q_r=I_S\otimes\lvert r\rangle\langle r\rvert_R\otimes I_J$，在其余端口上也取恒等。
若前史 $G$ 已准备该输入与记录，则

$$
\Psi_{\rm after}=U_{\rm m}G\Omega,\qquad
p_r=\|Q_rU_{\rm m}G\Omega\|^2,\qquad
\Psi_{|r}=\frac{Q_rU_{\rm m}G\Omega}{\sqrt{p_r}}\quad(p_r>0).
$$

完整测量仍由同一来源和门历史表达；条件态是已读记录下的预测对象。
系统约化条件态为
$\rho_{S|r}=\sum_\alpha M_{r\alpha}\rho_S M_{r\alpha}^\dagger/p_r$，
未必是纯态。
等距性来自正交记录及完备式，酉扩张通过补齐输入、输出正交基得到。[[6](#bib-static)]
这些表示式不独自证明为何某个特定结果成为唯一实际经验。

<!-- v69-note:N19 -->

> **编者注（Markdown 编者，N19）。** 类型上可写 $M_{r\alpha}:\mathcal{H}_{\rm in}\to\mathcal{H}_{\rm out}$，完备式的恒等在输入端，$V$ 的值域是输出端与 $R,J$ 的张量积；正文以同一系统端口 $S$ 简写输入输出时，$Q_r$ 的恒等实际作用在输出端及所有未读参考。有限结果和有限细标签可取共同字母表，缺项补零。对有限维内部载体，把就绪输入子空间和等距像放入同一个足够大的空间，且两正交补维数匹配，补基才给全空间酉；任意无限维等距不自动有同空间酉扩张，须另供匹配的补空间或更大载体。若系统输入与其余端口关联，就把纯化参考留在整体中并在算子上张量恒等；只用 $\rho_S$ 计算系统条件态仍要求记录端口已独立就绪。标量总范数对少数输入守恒不能替代算符完备式。

<!-- /v69-note -->

若两内容分支又附带内部记录 $e_0,e_1$，完整分支重叠变为

$$
c_{\rm full}=\langle\psi,\phi\rangle\langle e_0,e_1\rangle.
$$

当记录正交且读口不访问它们时，标签的交叉项不可见，留下经典对角概率
$p,1-p$；这不强制 $p$ 变成零或一。
完全退相干降低的是可见相干关系，而约化密度矩阵的秩可能增加。
当实际读取了某条记录，再按该记录条件化，才得到对应分支。
这一层与前轮 v68 的“可见关系降维／条件支持缩小”保持一致。

<!-- v69-note:N20 -->

> **编者注（Markdown 编者，N20）。** 乘积重叠公式要求每条完整分支确为所写内容向量与记录向量的张量积；相关或混合记录须计算实际联合态，不能仅乘边缘重叠。正交记录在限制读口或取偏迹后隐藏标签交叉项，而非选出一个确定人口；非选择遗忘与按已读记录条件化是两种操作。这里 V68 的承接限于其原文关于可见算符投影、非选择密度秩和正概率条件支持的区别。

<!-- /v69-note -->

### 7.2 DNA：共同历史更像可继承的记录

生物学上，DNA 承载生物信息，复制通过互补链模板传递序列；
比较基因组学利用保守与差异序列研究进化关系，
同源重组又会交换 DNA 片段并产生新的组合。[[9](#bib-dna), [10](#bib-comparative), [11](#bib-recombination)]
因此共同祖先与可复制记录是有根据的类比，
但继承关系通常不是所有对象只共享同一个连续字符串前缀的模型。

<!-- v69-note:N21 -->

> **编者注（Markdown 编者，N21）。** NHGRI 的 DNA 说明书正文支持 DNA 传递生物信息与互补链模板复制；比较基因组学说明书支持利用保守和差异序列研究进化；同源重组词条支持相似或相同 DNA 间交换序列。这些是此段实际使用的背景，不是量子态制备、相干寿命或生物纠缠的实验报告。序列的经典标签化是读出理想化，不能把原文背景扩成分子复制的单门机制。

<!-- /v69-note -->

#### 命题 7.1（复制经典标签，不等于复制任意未知量子态）

若 $\{\lvert z\rangle\}$ 是一组正交标签，映射
$\lvert z\rangle\lvert 0\rangle\mapsto\lvert z\rangle\lvert z\rangle$
在就绪子空间上是等距，因而可扩充为酉。
相反，一个统一等距不能对所有未知纯态执行
$\lvert \psi\rangle\lvert 0\rangle\mapsto\lvert \psi\rangle\lvert \psi\rangle$。

**证明。**

正交标签的输入、输出内积都是 $\delta_{zz'}$，故可补齐成酉。
若任意态都可复制，两个输入的内积 $c$ 必须满足 $c=c^2$；
取 $0<|c|<1$ 即矛盾。

∎

<!-- v69-note:N22 -->

> **编者注（Markdown 编者，N22）。** 非克隆论证的输入域须含两个非正交的不同射线，特别是至少二维载体；一维纯态族或一组互相正交标签没有这个反例。精确矢量复制合同下内积为 $c=c^2$；若仅指定输出射线并容许态依赖整体相位，取模仍给 $|c|=|c|^2$，同样排除非正交不同射线。正交经典标签的有限就绪子空间补基有效；可数标签上的线性等距按范数延拓，但同空间酉扩张仍须补空间维数匹配或增添足够容量，不能从“可数”单独推出。

<!-- /v69-note -->

把不同 DNA 序列当作可区分经典标签，是一个读出层面的理想化；
它不声称实际分子复制只由上述一个门完成。
但它解释了为什么“信息可复制”无需违反全局酉性。

#### 定理 7.2（共同序列统计不能认证纠缠）

<a id="thm:dna"></a>

给 $p_z\ge0$、$\sum_zp_z=1$，考虑

$$
\rho_{\rm cl}=\sum_zp_z\lvert z,z\rangle\langle z,z\rvert,
\qquad
\lvert \Psi_{\rm coh}\rangle=\sum_z\sqrt{p_z}\lvert z,z\rangle.
$$

两者对全部在 $\lvert x,y\rangle$ 基中对角的效果给相同概率；
$\rho_{\rm cl}$ 可分，而若至少两个 $p_z$ 非零，$\Psi_{\rm coh}$ 在两记录切分纠缠。

**证明。**

两态的对角元都是 $p_z$（位于 $x=y=z$），故所有对角效果的迹配对相同。
$\rho_{\rm cl}$ 已写成乘积态的凸组合；
$\Psi_{\rm coh}$ 的 Schmidt 系数是 $\sqrt{p_z}$，
至少两个非零时不可能为乘积。

∎

<!-- v69-note:N23 -->

> **编者注（Markdown 编者，N23）。** 求和可取有限或可数正交标签：$\sum_zp_z=1$ 使相干向量按 Hilbert 范数收敛、经典混合按迹范数收敛。一般离散概率族的正质量支撑至多可数；此处不把连续标签密度当作可归一正交向量和。对角效果为有界 $0\le E\le I$，故相同对角元给相同迹配对；可数经典混合属于有限可分混合的迹范数闭包。单个非零 $p_z$ 时两者均为乘积，至少两个时只有相干纯态具所列 Schmidt 非可分性。

<!-- /v69-note -->

所以共享 DNA、共享祖先或共享地球历史，可以给共同来源与相关记录的证据；
仅凭这些经典资料，不能在上述两类状态之间作出选择。
如果要进一步提出“某些生物功能使用特定量子相干”的经验命题，
还须指定可测的非对角关系、切分、相干保持机制及与经典模型可区分的实验。
本文不把它们当作已经证明的事实。

## 8. 候选公理结构及其物理边界

对本轮讨论，最紧凑而又可审查的组织是：

1.  **H：可逆历史合成。** 已声明执行形成群 $\Gamma$；实际档案身份另外保留。

1.  **R：归一正型复关系。** 给 $f(e)=1$ 与全部有限矩阵
$[f(g_i^{-1}g_j)]\succeq0$。

1.  **W：正交细化权重。** 方向无关、非负、归一，并与足够丰富的正交细化相容。

H 与 R 精确重构可逆循环表示，W 给平方权重。
已声明的内部切分、控制器、记录和读口把这个核心连接到具体实验；
具体仪器及已读记录的条件化规则另行声明，不能由 H/R/W 单独指定 Lüders 更新。
若采用 V59 路径，则可用同域 RC 与充分读口正性来组织概率响应部分。
这两种组织应各自保留其前提，不能只数公理条数来比较“更基础”。

<div tabindex="0" role="region" aria-label="原文表格" style="overflow-x:auto">

| 可以证明／重构的内容 | 尚未被这些条件独自确定的内容 |
| --- | --- |
| 唯一来源的循环 Hilbert 表示 | 具体宇宙的 $f$、相互作用与参数取值 |
| 共同后续的酉实现 | 哪些逆元和相干控制实际可实施 |
| 正交分支的平方权重 | 复数结构本身为何被物理选择 |
| 当前及未来概率的充分商 | 具体空间局域性、张量接口与观测资源 |
| 给定切分的纠缠；给定仪器及条件化规则下的记录预测 | 单次实际经验的唯一性及其本体解释 |
| 每一步历史关系的离散组合 | 连续时间、Hamiltonian、时空与质量规律 |

</div>

若另给可微单参数酉群，才可进一步以生成元得到 Schrödinger 形式；
单增事件计数本身不自动供应这种连续参数。

<!-- v69-note:N24 -->

> **编者注（Markdown 编者，N24）。** 有限维可微单参数酉群给反自伴生成元；另定非零实常数 $\hbar$ 后，可写 $H=i\hbar U^{\prime}(0)$ 与 $i\hbar\dot\psi=H\psi$。无限维通常使用强连续单参数群及自伴生成元，微分只在其稠密生成元定义域内成立；不能把无界生成元当作全空间有界矩阵。参数的物理时间校准、$\hbar$ 和实际动力学仍是附加资料。

<!-- /v69-note -->
若只允许置换执行及共同对角读口，经典模型也可以包含在上述表示中；
非经典物理内容还要由实际相干读口、相容复合和实验响应体现。

**本轮可用的统一表述是：
唯一来源生成历史；完整复关系保证历史可相干组合；
观察面选择可读效果；全部合法未来概率定义预测等价；
纠缠则是同一完整态在已声明内部切分上的不可分关系。**
这一表述保留了共同历史的实质作用，也把“什么由什么推出”写成了可检查的数学条件。

## 附录 A. 可保护的共同内容：比共同字符串更强的定理

#### 定理 A.1（共同保护分量及稳定上界）

令 $\xi=U_s\Omega$，$P$ 为正交投影。
若两个后缀酉 $A,B$ 在 $P\mathcal{H}$ 上逐点恒等，置
$\psi=A\xi$、$\phi=B\xi$、$c_0=P\xi$，则

$$
\psi=c_0+a,\qquad \phi=c_0+b,\qquad a,b\perp P\mathcal{H}  .
$$

所有效果 $0\le E\le P$ 的两态概率相同。
令 $q_0=\|c_0\|^2$，则

$$
|\langle\psi,\phi\rangle|\ge\max(0,2q_0-1),
$$

$$
D(\rho_\psi,\rho_\phi)
\le\sqrt{1-\max(0,2q_0-1)^2}.
$$

**证明。**

酉在 $P\mathcal{H}$ 上逐点恒等，故其伴随也如此，且保持正交补。
因此 $A\xi=P\xi+A(I-P)\xi$，$B$ 同理。
$E=PEP$ 只读共同分量，故响应相同。
又 $\|a\|^2=\|b\|^2=1-q_0$，所以

$$
|\langle\psi,\phi\rangle|
=|q_0+\langle a,b\rangle|
\ge q_0-|\langle a,b\rangle|
\ge2q_0-1.
$$

结合非负性及定理 [3.4](#thm:distance) 即得。

∎

<!-- v69-note:N25 -->

> **编者注（Markdown 编者，N25）。** 投影的像是闭子空间。酉逐点固定它，逆酉与伴随也固定它，故其正交补不变；$0\le E\le P$ 使正算子 $E$ 在 $\ker P$ 上为零（由其平方根的零二次型可见），于是 $E=PEP$。$q_0=0$ 的距离上界是一，$q_0=1$ 时两向量相同、上界为零，$q_0=1/2$ 时下界为零；这些是稳定上界，不是声称每个给定维数都达到等号，也不由字面共享前缀自动供应保护子空间。

<!-- /v69-note -->

这个保护条件可以表达“共同内容的全部相关读口保持稳定”。
它是关于实际子空间和后续作用的条件，因此比词语上共享一个前缀更接近可测物理。
若没有这个条件，共同早期准备仍可能被不同后续完全改写。

## 固定来源与文献

<!-- v69-note:N26 -->

> **编者注（Markdown 编者，N26）。** 此节“本轮查读／读取”的范围是原作者的原稿陈述，保留其限定；固定版本与外部来源的角色不能替换为当前全部上游或最新版本的认证。

<!-- /v69-note -->

<a id="bib-v22"></a>

**[1]** 
trureturing，固定提交，
[V22：相对门历史、观察商与递归闭包](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)。
本轮查读 §§1--9 的相关定义、证明；未重审其后所有依赖。

<a id="bib-v52"></a>

**[2]** 
trureturing，固定提交，
[V52：纯态商几何、二次关系生成元与无损递归](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)。
本轮重点 §§2--3 及定理 4.1--4.2。

<a id="bib-v56"></a>

**[3]** 
trureturing，固定提交，
[V56：内部二元切分、算符三轴与纯度](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md)，定理 6.1 及相邻定义。

<a id="bib-v59"></a>

**[4]** 
trureturing，固定提交，
[V59：局部层析、相干读口轨道与量子正性](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md)，
RC、定理 3.2--3.3、推论 3.4 及命题 3.5。

<a id="bib-history"></a>

**[5]** 
trureturing，固定提交，
[Fibonacci 历史记录与时间箭头](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md)，§§116--120，尤其定理 118.2--118.3。

<a id="bib-static"></a>

**[6]** 
trureturing，固定提交，
[$\Omega$ 静态相融纤维理论](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，定义、合法未来目标族及 §7 的历史、记录表示。

<a id="bib-gns"></a>

**[7]** 
Kobi Kremnizer，MIT 18.238，Lecture 3，2008-02-10，
[GNS construction，§4，Theorem 4.1](https://math.mit.edu/classes/18.238/lec100208.pdf)。
本轮读取两页。本文所证群正型版本是该类构造的标准特例，不宣称讲义逐字给出同一陈述。

<a id="bib-watrous"></a>

**[8]** 
John Watrous，*The Theory of Quantum Information*，Chapter 3，
[Theorem 3.4（Holevo--Helstrom）及 Proposition 3.5](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf)。
本轮读取相关陈述与证明；本文给纯态二维自足证明。

<a id="bib-dna"></a>

**[9]** 
National Human Genome Research Institute，
[Deoxyribonucleic Acid (DNA) Fact Sheet](https://www.genome.gov/about-genomics/fact-sheets/Deoxyribonucleic-Acid-Fact-Sheet)。
用于 DNA 信息传递与模板复制的生物学背景。

<a id="bib-comparative"></a>

**[10]** 
National Human Genome Research Institute，
[Comparative Genomics Fact Sheet](https://www.genome.gov/about-genomics/fact-sheets/Comparative-Genomics-Fact-Sheet)。
用于保守序列比较与进化研究的背景。

<a id="bib-recombination"></a>

**[11]** 
National Human Genome Research Institute，
[Homologous Recombination](https://www.genome.gov/genetics-glossary/homologous-recombination)。
用于序列交换及组合变化的背景。

```tex
\end{document}
```

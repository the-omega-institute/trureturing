<details>
<summary>原始 XeLaTeX 制作设置与标题源码（逐字保留）</summary>

<div class="katex-display">

```tex
% !TeX program = xelatex
% Compile twice with XeLaTeX. Optional: \def\AURICFontPath{/absolute/font/path/}
% Paper mathematics only: no CAS, numerical evaluation, enumeration, or mathematical tests.
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
\hypersetup{pdftitle={AURIC v65：单一本体中的忠实关系与量子过程重构},
pdfauthor={AURIC research continuation},
pdfsubject={Faithful internal probes, complete positivity reflection, marginal repair, approximate unitarity and persistent memory}}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\Herm}{\operatorname{Herm}}
\newcommand{\id}{\operatorname{id}}
\newcommand{\Ad}{\operatorname{Ad}}
\newcommand{\diag}{\operatorname{diag}}
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
\fancyhead[L]{\small AURIC：忠实关系与量子过程}
\fancyhead[R]{\small v65 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
\begin{center}
{\LARGE\bfseries\color{auricblue} 单一本体中的忠实关系}\\[6pt]
{\LARGE\bfseries\color{auricblue} 与量子过程重构}\\[8pt]
{\large 正性反映、边缘修复、近似酉性与增长记录的组合}\\[6pt]
AURIC 量子起源研究\quad 定义、定理与纸面证明\quad v65.0\\[4pt]
2026 年 11 月 1 日\quad Asia/Singapore
\end{center}
```

</div>

</details>

# 单一本体中的忠实关系<br>与量子过程重构

**正性反映、边缘修复、近似酉性与增长记录的组合**

AURIC 量子起源研究　定义、定理与纸面证明　v65.0

2026 年 11 月 1 日　Asia/Singapore

> **原稿身份与范围注（Markdown 编者）。** 本文据提供者给定的完整 v65 原稿转换：UTF-8 源码 42,489 字节，SHA-256 <code>59f2af1d<wbr>740b49cf<wbr>6ebc954b<wbr>36be3344<wbr>305b2446<wbr>f8db1b3b<wbr>32d87cdb<wbr>120147ac</code>。上方逐字保存原稿制作设置；正文保留原断言及纸面证明。核读及本地排版的范围不包含形式核验、原生控制或物理实现认证。


**摘要**

承接 v64 的近似平方标定、共同复方向与有限读出正性，本文研究如何把同一内部接口的
状态约束提升为过程约束。标准 Choi 对应与项目已有单个满 Schmidt 纯化的识别结果，
在固定忠实探针下成为：联合正性等价于完全正性，参考边缘守恒等价于保迹，
在参考边缘守恒下，联合输出秩一则给等距过程。本文进一步证明：对等维 $d$ 接口，
对全部保 Hermitian 候选过程反映完全正性的固定探针，恰为满 Schmidt 秩纯态；
混合的线性忠实探针一般不具有此性质。最小 Schmidt 权重的倒数是可达到的最坏误差放大常数，
由均匀权重唯一最小化。随后给出同时修复负谱与参考边缘的显式 CPTP 构造，
误差仅含一次该条件数，并从联合输出近纯导出近等距、等维近酉的界。
最后以一个固定 $\Omega$ 内的关联反例说明，过程认证还需共同保留记忆才能递归组合；
完整报告的 diamond 误差线性累加，而完整相干观察者另需对齐的等距误差。
这些是有限维复结构内的条件性动力学重构，不是对复数域、张量接口或物理取得的无前提推导。



## 1 源码范围、已有结果与同一本体

> **来源归属注（Markdown 编者）。** 本节及文献表中的活动请求、HTTP 403、未再查询 HEAD、26 份来源字节核对和阅读报告，是原作者原稿的历史记述，不是本次 Markdown 转换者的访问或全库核验行为。固定项目来源的版本为 <code>5cf95e1a<wbr>e01f7ed8<wbr>6735c04a<wbr>d8d752cb<wbr>19b1a58b</code>。

本轮唯一活动源码请求于新加坡时间 2026-11-01 05:36:51 返回 HTTP 403，
没有取得新提交号，也未再次查询活动 HEAD。以下使用此前已核验的固定提交
<code>5cf95e1a<wbr>e01f7ed8<wbr>6735c04a<wbr>d8d752cb<wbr>19b1a58b</code>。

本轮核对的 26 份来源实际字节均与该提交保存的 theory 树身份一致；
这不等于全库数学认证，也不表示已核实该提交之后的增量。[[1](#bib-head)]

本轮直接承接的已有结果为：

1. $\Omega$ 主文 §6 已有标准 Choi--Kraus--Stinespring 结构和完整反馈记录归一；
V38 §§3--4 已有 qubit Choi 正性、秩一酉性、四输入过程层析及 diamond 稳定界。[[2](#bib-omega), [3](#bib-v38)]
2. V52 推论 8.4 已证明：精确恢复单个满 Schmidt 纯化，
即恢复其支持上的全部矩阵单位。单个固定关联态携带整个线性过程信息这一思想已有明确前件。[[4](#bib-v52)]
3. V58 §11 明列统一内部 ready、保留参考、实际局域作用与完整记录条件；
V59 §§3--5 区分关系相容的 Hermitian 候选、实际相干方向覆盖与量子正性。[[5](#bib-v58), [6](#bib-v59)]
4. v64 给出近似乘性到幂律、相干回返到平方指数区间、近守恒到共同复方向，
并把增益、方向误差与读出残差接入 V59 的负谱界。本轮只消费所需结论，不重新计为发现。

> **前稿身份注（Markdown 编者）。** 此处 v64 指提供者给定的未发表、不可变前稿：UTF-8 源码 42,308 字节，SHA-256 <code>6840e861<wbr>340ca3cf<wbr>0d7d8475<wbr>9b0b4636<wbr>5206ec04<wbr>9d0dde4c<wbr>38cc555c<wbr>4564f8e1</code>；不将其归入上述固定项目提交，也不据此声称核验了活动 v64 工作树。

标准 CP 判据与忠实态理论分别承接 Choi 和 D'Ariano--Lo Presti；
本轮新增重点是正性反映的分类、条件数、保边缘修复及其与实际接口的组合。
所述分类是标准结构的自足组合推论，不作全球优先权主张。[[7](#bib-choi), [8](#bib-faithful), [9](#bib-watrous2)]

始终固定同一个实际本体 $\Omega$ 与完整观察者
$$
\Psi_k=U_k\cdots U_1\Omega.
$$
参考、环境、记录、控制与预测都属于这个完整载体。以下 $R,A,B$ 是其中已指定的
有限内部接口，不把某个约化系统改称完整观察者。对候选线性映射的全域量词，
是同一接口的结构性陈述，不是另选实际宇宙。若某内部联合接口被假设为纯态，
其与其余角色的因子关系也是额外接口条件，不能由完整 $\Psi_k$ 纯性代替。


## 2 一个固定探针中的过程信息与矩阵归一化


#### 定义 2.1（固定忠实纯探针与约定）

令 $R\simeq A\simeq\mathbb C^d$、$B\simeq\mathbb C^m$，固定同标号正交基，
$$
D=\operatorname{diag}(s_1,\ldots,s_d)>0,\qquad \sum_i s_i=1,\qquad
\mu=\min_i s_i>0.
$$
给定一个固定内部输入
$$
|\gamma_D\rangle=\sum_i\sqrt{s_i}|i\rangle_R|i\rangle_A,\qquad
P_D=|\gamma_D\rangle\langle\gamma_D|.
$$
对复线性映射 $\Phi:M_d(\mathbb C)\to M_m(\mathbb C)$ 定义
$$
X_\Phi=(\operatorname{id}_R\otimes\Phi)(P_D),\qquad
C_\Phi=\sum_{i,j}E_{ij}\otimes\Phi(E_{ij}).
$$
参考位于第一因子；$C_\Phi$ 使用未归一 $\Gamma_d=\sum_i|ii\rangle$。
保 Hermitian 简称 HP，完全正简称 CP，完全正且保迹简称 CPTP。

“一个固定输入”指一个探针态类型及其联合响应接口，不是一次结果就返回全部矩阵元。
把候选 $\Phi$ 解释为实际过程，还需同一操作在保留参考上满足
$\operatorname{id}_R\otimes\Phi$ 的关系契约；校准分支与应用分支的记忆条件须相同或被显式保留。


<a id="thm:exact"></a>

#### 定理 2.2（标准 Choi 判据的固定非最大纠缠形式）

固定上述 $D$。映射 $\Phi\mapsto X_\Phi$ 是线性双射，其逆由块矩阵 $X=(X_{ij})$ 给出：
$$
\Phi_X(E_{ij})=\frac{X_{ij}}{\sqrt{s_i s_j}}.
$$
此外
$$
\begin{aligned}
\Phi\text{ 为 HP}&\iff X_\Phi=X_\Phi^\dagger,\\
\Phi\text{ 为 CP}&\iff X_\Phi\ge0,\\
\Phi\text{ 保迹}&\iff \operatorname{Tr}_B X_\Phi=D.
\end{aligned}
$$
若后两项成立，则 $\Phi$ 的最小 Kraus 数为 $\operatorname{rank} X_\Phi$。
它为一，当且仅当 $\Phi=\operatorname{Ad}_V$、$V^\dagger V=I_d$；当 $m=d$ 时 $V$ 酉。


**证明。**

展开 $P_D$ 即给逆公式及 HP 对应。又有可逆合同变换
$$
X_\Phi=(D^{1/2}\otimes I_m)C_\Phi(D^{1/2}\otimes I_m).
$$
若 $C_\Phi\ge0$，谱分解写成
$C_\Phi=\sum_a|v_a\rangle\langle v_a|$，并唯一定义
$v_a=\sum_i|i\rangle\otimes K_a|i\rangle$。
逐矩阵单位比较得 $\Phi(Z)=\sum_aK_a ZK_a^\dagger$。
张量任意有限参考后，各项仍是正矩阵的共轭，故 CP。
反向 CP 显然给 $C_\Phi\ge0$，合同变换又使它等价于 $X_\Phi\ge0$。

参考边缘的 $(i,j)$ 元为 $\sqrt{s_i s_j}\operatorname{Tr}\Phi(E_{ij})$；
由于所有权重非零，等于 $D$ 恰是 $\operatorname{Tr}\Phi(E_{ij})=\delta_{ij}$。
按线性张成，这等价于保迹，亦等价于 $\sum_aK_a^\dagger K_a=I$。
任何 $r$ 项 Kraus 分解给至多 $r$ 个秩一 Choi 项，谱分解达到最小数；
可逆合同保持秩。秩一时只需一个 $V$，保迹给 $V^\dagger V=I$。
反向一个等距 Kraus 算子显然产生秩一。证毕。

□

这是标准有限维结构的直接证明，亦与项目 V38 及 V52 的前件相容。[[3](#bib-v38), [4](#bib-v52), [9](#bib-watrous2), [8](#bib-faithful)]


#### 命题 2.3（一个标量归一化不足以给过程保迹）

令 $d=m=2$、$D=I_2/2$，
$K=\operatorname{diag}(\sqrt2,0)$、$\Phi=\operatorname{Ad}_K$。
则 $X_\Phi=|00\rangle\langle00|$ 正、纯、迹一，但 $\Phi$ 不保迹。


**证明。**

直接作用于 $(|00\rangle+|11\rangle)/\sqrt2$ 得 $|00\rangle$。
然而 $K^\dagger K=\operatorname{diag}(2,0)\ne I$，
并且 $\operatorname{Tr}_B X_\Phi=|0\rangle\langle0|\ne D$。

□

因此过程归一化在忠实参考表示中的准确位置是矩阵等式
$\operatorname{Tr}_BX=D$，它保留了旁观参考的全部矩阵关系。
总质量 $\operatorname{Tr} X=1$ 只是其一个标量后果。


#### 命题 2.4（零 Schmidt 权重留下未受检验的方向）

若某个 $s_j=0$，则该探针不能识别全部线性过程，也不能单独以输出正性判 CP。


**证明。**

探针展开中所有含指标 $j$ 的块均消失。更明确地，取 $d=m\ge2$，
$D$ 的支持投影为 $P$，选 $|j\rangle\in\ker P$ 和任意 $k\ne j$。
令 $H=|k\rangle\langle k|-|j\rangle\langle j|$，
$$
\Phi(Z)=Z+\lambda\langle j|Z|j\rangle H,\qquad \lambda>1.
$$
此映射 HP、保迹，在整个受检验支持上恒等，
但 

$$
\Phi(|j\rangle\langle j|)=\lambda|k\rangle\langle k|+(1-\lambda)|j\rangle\langle j|
$$


非正。它与恒等映射给相同探针输出。

□



## 3 纯性为何特殊：识别忠实与正性反映


#### 定义 3.1（两种不同的探针性质）

对固定密度矩阵 $\sigma$ 于 $\mathbb C^d\otimes\mathbb C^d$：

1. 线性识别忠实，意为 $\Phi\mapsto(\operatorname{id}\otimes\Phi)(\sigma)$ 对复线性过程单射。
2. 完全正性反映，意为对每个复线性 HP 候选 $\Phi:M_d\to M_d$，
$$
\begin{gathered}
(\operatorname{id}\otimes\Phi)(\sigma)\ge0\quad\\
\Longleftrightarrow\quad\Phi\text{ 为 CP}.
\end{gathered}
\tag{OR}
$$

第二项的量词覆盖全部 HP 锥，不只覆盖保迹切片或实际已执行的有限操作。



<a id="thm:order"></a>

#### 定理 3.2（等维单探针的完全正性反映）

参考、输入与被检验过程的输出均为 $d$ 维时，
固定探针具有性质 (OR)，当且仅当它是满 Schmidt 秩纯态。


**证明。**

写
$$
\sigma=(\mathcal R\otimes\operatorname{id})(|\Gamma_d\rangle\langle\Gamma_d|).
$$
Choi 对应唯一给出 $\mathcal R$；$\sigma\ge0$ 保证 $\mathcal R$ 为 CP。
这里 $\mathcal R$ 是表示探针的滤波，不假定保迹。
两因子上的映射交换作用，所以
$$
(\operatorname{id}\otimes\Phi)(\sigma)=(\mathcal R\otimes\operatorname{id})(C_\Phi).
$$
全部 HP 映射与全部 Hermitian 联合矩阵双射：给 $H=(H_{ij})$，
令 $\Phi_H(E_{ij})=H_{ij}$，而 $H_{ji}=H_{ij}^\dagger$ 正是 HP 条件。
故 (OR) 等价于
$$
(\mathcal R\otimes\operatorname{id})(H)\ge0\iff H\ge0
\quad\text{对全部 Hermitian }H.
$$
若 $H$ 在其核中，则对 $H$ 和 $-H$ 使用反映性，得 $H=0$；
再分解任意复核元的 Hermitian 实虚部，可知该映射可逆，进而 $\mathcal R$ 可逆。
逆也 HP，因为 $\mathcal R(X^\dagger)=\mathcal R(X)^\dagger$ 及单射性。
对任意 $Y\ge0$，取 $H=(\mathcal R^{-1}\otimes\operatorname{id})(Y)$，
反映性给 $H\ge0$。特别地，$\mathcal R^{-1}$ 的 Choi 矩阵为正，
故逆映射亦 CP。

写 $\mathcal R(Z)=\sum_iA_iZA_i^\dagger$、
$\mathcal R^{-1}(Z)=\sum_jB_jZB_j^\dagger$。
恒等复合的 Choi 矩阵秩一，所以其每个 Kraus 向量共线，即
$$
B_jA_i=c_{ji}I.
$$
至少一个系数非零；相应 $B_{j_0}$ 可逆，并迫使全部
$A_i=c_{j_0i}B_{j_0}^{-1}$。因此 $\mathcal R=\operatorname{Ad}_A$，$A$ 可逆。
于是 

$$
\sigma=(A\otimes I)|\Gamma_d\rangle\langle\Gamma_d|(A^\dagger\otimes I)
$$


为归一纯态，Schmidt 秩等于 $\operatorname{rank} A=d$。

反向，任何这样的纯态都具有上述可逆滤波形式，
其探针输出为 $C_\Phi$ 的可逆合同变换，双向保持正锥，
由定理 [2.2](#thm:exact) 得 (OR)。

□



<a id="prop:mixed"></a>

#### 命题 3.3（混合探针可以识别过程而不反映 CP）

令 $d\ge2$、$0<q<1$，
$$
\sigma_q=(1-q)\frac{I_{d^2}}{d^2}
+q\frac{|\Gamma_d\rangle\langle\Gamma_d|}{d}.
$$
则 $\sigma_q$ 线性识别忠实，但不具有 (OR)。


**证明。**

对 $X=(\operatorname{id}\otimes\Phi)(\sigma_q)$，
$$
X=\frac qd C_\Phi+\frac{1-q}{d^2}I_d\otimes\Phi(I_d),
\qquad \operatorname{Tr}_R X=\frac{\Phi(I_d)}d.
$$
故
$$
C_\Phi=\frac dqX-\frac{1-q}{q}I_d\otimes\operatorname{Tr}_R X,
$$
给出线性逆。为展示正性不能反映 CP，令
$\mathcal D(Z)=\operatorname{Tr}(Z)I_d/d$、$T(Z)=Z^{\mathsf T}$，
并取
$$
\frac1{d+1}<s\le\min\left\{1,\frac1{q(d+1)}\right\},
\qquad \Phi_s=sT+(1-s)\mathcal D.
$$
因 $q<1$，区间非空。$\Phi_s$ 正、保迹、保单位，
但 $C_{\Phi_s}=sF+(1-s)I/d$ 在反对称空间上的特征值为
$[1-(d+1)s]/d<0$，其中 $F$ 为交换算子。
另一方面
$$
(\operatorname{id}\otimes\Phi_s)(\sigma_q)
=(1-qs)\frac I{d^2}+qs\frac Fd\ge0,
$$
因为其最小特征值为 $[1-(d+1)qs]/d^2$。

□

此例允许 $q$ 任意接近一；精确反映与近似稳定须分别陈述。
忠实混合态及逆映射条件的既有研究见 [[8](#bib-faithful)]。


#### 说明 3.4（等维、纯性与本体的边界）

若参考更大，$P_{\max}^{R_0A}\otimes\tau_S$ 对混合 $\tau_S$ 仍反映 CP，
因为输出为 $C_\Phi/d\otimes\tau_S$；因此定理的等维条件不可删。
该定理刻画指定探针的关系结构，不声称完整本体纯性强迫每个接口纯，
也不从它推出空间物理维数为三。



## 4 各向同性的一个精确意义：最优最坏条件数

用 $\|\cdot\|_1$ 表示迹范数、$\|\cdot\|_\infty$ 表示算子范数。
定义 diamond 范数为张量任意有限参考后的诱导迹范数上确界；
它对 CPTP 映射取一，并对复合次乘。[[10](#bib-watrous3)]


<a id="thm:condition"></a>

#### 定理 4.1（忠实探针的条件数与达到性）

对任意复线性差映射 $\Delta:M_d\to M_m$，
$$
\boxed{
\|X_\Delta\|_1\le\|\Delta\|_\diamond
\le\frac1\mu\|X_\Delta\|_1.
}
$$
当 $m\ge2$ 时，右侧常数 $1/\mu$ 在两条 CPTP 映射之差上可达到。


**证明。**

左边以归一输入 $P_D$ 代入定义即得。
对任意有限参考 $Z$，其与 $A$ 上的单位向量可写
$u=(F\otimes I)\Gamma_d$、$v=(G\otimes I)\Gamma_d$，
其中 Hilbert--Schmidt 范数满足 $\|F\|_{\rm HS}=\|G\|_{\rm HS}=1$，
故其算子范数不超过一。
于是
$$
(\operatorname{id}_Z\otimes\Delta)(|u\rangle\langle v|)
=(F\otimes I)C_\Delta(G^\dagger\otimes I),
$$
迹范数不超过 $\|C_\Delta\|_1$。
任意输入矩阵的奇异值分解将此界延伸到整个单位迹范数球。
最后用
$C_\Delta=(D^{-1/2}\otimes I)X_\Delta(D^{-1/2}\otimes I)$，
得 $\|C_\Delta\|_1\le\mu^{-1}\|X_\Delta\|_1$。

取 $s_j=\mu$，输出两个正交纯态 $\tau_0,\tau_1$。
令
$$
\begin{aligned}
\Phi_0(Z)&=\operatorname{Tr}(Z)\tau_0,\\
\Phi_1(Z)&=[\operatorname{Tr}(Z)-Z_{jj}]\tau_0+Z_{jj}\tau_1.
\end{aligned}
$$
两者均为测量制备通道，差映射在输入 $|j\rangle\langle j|$ 上达到迹范数二，
故 diamond 范数为二。加权 Choi 差为
$\mu|j\rangle\langle j|\otimes(\tau_1-\tau_0)$，迹范数为 $2\mu$。

□



#### 推论 4.2（均匀权重的最坏情形最优性）

固定 $d$ 和输出维数 $m\ge2$，上述在 CPTP 差映射上的最佳统一常数满足
$$
\frac1\mu\ge d,
$$
且等号当且仅当 $D=I_d/d$。


**证明。**

最小权重不超过平均权重 $1/d$；等号迫使所有权重均等。
定理 [4.1](#thm:condition) 的达到性表明这是实际最坏常数的优化。

□

因此纯满 Schmidt 性供应精确正锥反映，均匀 Schmidt 权重供应最优最坏稳定性。
$D=I_d/d$ 在每个内部基变换下不变，是这里的各向同性。
它没有消除联合关联：最大纠缠探针的两个边缘均为 $I_d/d$，联合态仍纯。
若原生准备无法取得均匀探针，该数学最优性不自动给其取得权限。


## 5 从实际方向读出到联合输出的负谱预算

以下承接项目 V59 的谱论证及 v64 的实际增益、控制误差形式。
取联合输出维数 $N=dm$，同一响应的层析候选为
$X=X^\dagger$、$\operatorname{Tr} X=1$。
实际效果
$F_\nu=c_\nu Q_\nu$ 中 $0<c_\nu\le1$，
$Q_\nu$ 为实际复秩一投影；给定 $\eta_\nu,\tau_\nu\ge0$，读数满足
$$
y_\nu\ge-\eta_\nu,\qquad
|y_\nu-\operatorname{Tr}(XF_\nu)|\le\tau_\nu,\qquad
\zeta=\max_\nu\frac{\eta_\nu+\tau_\nu}{c_\nu}.
$$
其中 $0\le\theta\le1$，每个纯方向均与某个 $Q_\nu$ 的平方重叠至少 $1-\theta$。
理想覆盖失配 $0\le\theta_0\le1$ 与投影控制误差 $r_{\rm ctrl}\ge0$ 可给
$\theta=\min\{1,(\sqrt{\theta_0}+r_{\rm ctrl})^2\}$。

> **前提释义注（Markdown 编者）。** 此处“投影控制误差”沿用所引 v64 的实际合同：同一复接口内的理想秩一投影 $P_\nu$ 与实际秩一投影 $Q_\nu$ 满足 $\|Q_\nu-P_\nu\|_\infty\le r_{\rm ctrl}$。理想方向构成所声明的 $\theta_0$ 覆盖；这不是只从门算子接近便取得效果身份或读数权限。



<a id="prop:positive"></a>

#### 命题 5.1（联合维数上的有限正性界）

若 $N\theta<1$，则
$$
\boxed{
X\ge-aI_N,\qquad
a=\frac{\zeta+\theta}{1-N\theta},
\qquad t_X:=\operatorname{Tr} X_-\le(N-1)a.
}
$$


**证明。**

令 $\lambda=\lambda_{\min}X$、$M=\lambda_{\max}X$。
取靠近最小特征方向的实际投影，得到
$-\zeta\le\operatorname{Tr}(XQ_\nu)\le\lambda+\theta(M-\lambda)$。
迹一给 $M\le1-(N-1)\lambda$，故
$-\zeta\le(1-N\theta)\lambda+\theta$。
因迹一，至少一个特征值为正，负特征值至多 $N-1$ 个，给负谱质量界。

□

这里必须使用参考与输出的联合维数 $N$。输入探针的满 Schmidt 性负责识别过程，
输出读口的充分覆盖负责正性认证；它们是两项不同的条件。
V59 已证明有限菜单不能无条件认证精确正性，且局部酉轨道保留 Schmidt 系数，
因此不能自动当作所有联合方向。[[6](#bib-v59)]
原生实线性控制若仅接近某个复酉模型，实际效果的复类型仍须有独立接口对应。
本节的候选矩阵和后续的修复矩阵均属于同一个已确定的复接口。


<a id="sec:repair"></a>

## 6 同时修复负谱与参考边缘


<a id="lem:functional"></a>

#### 引理 6.1（边缘校正的准确过程范数）

对 Hermitian $Z$ 和密度矩阵 $\tau$，映射
$\mathcal F_Z(H)=\operatorname{Tr}(Z^{\mathsf T}H)\tau$ 满足
$$
\|\mathcal F_Z\|_\diamond=\|Z\|_\infty.
$$


**证明。**

对任意参考输入 $W$，先在系统因子上按 $Z^{\mathsf T}$ 的谱基去相干。
此 CPTP 操作不增加迹范数，所得正交块的迹范数之和不超过 $\|W\|_1$。
对各块乘相应特征值并求和，再张量 $\tau$，由三角不等式得到上界
$\|Z\|_\infty\|W\|_1$。输入绝对特征值最大的单位特征向量投影达到下界。

□



<a id="thm:repair"></a>

#### 定理 6.2（保持共同参考的显式 CPTP 修复）

设 $X=X^\dagger$、$\operatorname{Tr} X=1$，沿用已标定 Schmidt 基中的
$D=\operatorname{diag}(s_i)>0$、$\operatorname{Tr} D=1$，
输出维数 $m$，并令
$$
\begin{gathered}
M=\operatorname{Tr}_BX-D,\qquad \tau=I_m/m,\qquad X_0=X-M\otimes\tau,\\
E=(X_0)_-,\quad R_-=\operatorname{Tr}_BE,\quad
\varepsilon=\|D^{-1/2}R_-D^{-1/2}\|_\infty,\\
Z_{\rm c}=E+(\varepsilon D-R_-)\otimes\tau,\qquad
Y=\frac{X_0+Z_{\rm c}}{1+\varepsilon}.
\end{gathered}
$$
则 $Y\ge0$、$\operatorname{Tr}_BY=D$，因而对应唯一 CPTP 映射 $\Psi$。
记 $b=\|D^{-1/2}MD^{-1/2}\|_\infty$，有
$$
\boxed{\|\Phi_X-\Psi\|_\diamond\le b+2\varepsilon.}
$$
若 $a\ge0$、$X\ge-aI$、$t_X=\operatorname{Tr} X_-$，则
$$
\boxed{
\varepsilon\le\frac1\mu
\min\left\{
t_X+\frac12\|M\|_1,\,
ma+\|M\|_\infty
\right\},\qquad
b\le\frac{\|M\|_\infty}{\mu}.
}
$$


**证明。**

由定义 $\operatorname{Tr}_BX_0=D$，且 $\operatorname{Tr} M=0$、$\operatorname{Tr} X_0=1$。
$R_-\le\varepsilon D$，故 $Z_{\rm c}\ge0$，
$\operatorname{Tr}_B Z_{\rm c}=\varepsilon D$，
并且
$$
X_0+Z_{\rm c}=(X_0)_++(\varepsilon D-R_-)\otimes\tau\ge0.
$$
于是 $Y$ 满足定理 [2.2](#thm:exact) 的 CP 与保迹条件。

若 $\varepsilon>0$，$Z_{\rm c}/\varepsilon$ 也正且参考边缘为 $D$，
对应某个 CPTP 映射 $\Gamma$。线性识别给
$$
\Phi_{X_0}=(1+\varepsilon)\Psi-\varepsilon\Gamma,
\qquad
\|\Phi_{X_0}-\Psi\|_\diamond
=\varepsilon\|\Psi-\Gamma\|_\diamond\le2\varepsilon.
$$
若 $\varepsilon=0$，正矩阵 $R_-$ 迹为零，故 $E=0$，
此时直接取 $\Psi=\Phi_{X_0}$。另一方面，$X-X_0=M\otimes\tau$
对应引理 [6.1](#lem:functional) 中
$Z=D^{-1/2}MD^{-1/2}$ 的校正映射，其范数恰为 $b$，给总界。

最后，
$$
\operatorname{Tr} E=\frac{\|X_0\|_1-1}{2}
\le t_X+\frac12\|M\|_1.
$$
又有 $X_0\ge-[a+\|M\|_\infty/m]I$，
故 $E\le[a+\|M\|_\infty/m]I$，从而
$R_-\le[ma+\|M\|_\infty]I_d$。
分别使用 $R_-\le(\operatorname{Tr} E)I_d$ 和该算子上界，得到 $\varepsilon$ 的两项界。

□



#### 推论 6.3（精确参考边缘与一次条件数）

若 $M=0$，则
$$
\|\Phi_X-\Psi\|_\diamond
\le2\varepsilon
\le\frac{2\min\{t_X,ma\}}{\mu}.
$$
这个构造直接在过程层比较两条 CPTP 映射，只引入一次 $1/\mu$。

> **对象释义注（Markdown 编者）。** 上句“两条 CPTP 映射”指证明中的 $\Psi$ 与 $\Gamma$（$\varepsilon>0$ 时）；原候选 $\Phi_X$ 在 $M=0$ 时只保证 HP、保迹，仍可非 CP。$\varepsilon=0$ 时修复已是通道，无需定义 $\Gamma=\Phi_{Z_{\rm c}/\varepsilon}$。




#### 命题 6.4（所声明补偿类中的最小质量）

在要求 $Z\ge E$、$\operatorname{Tr}_B Z=eD$ 的正补偿类中，
最小可取的 $e$ 恰为 $\varepsilon$。


**证明。**

偏迹正性给 $eD\ge R_-$，即 $e\ge\varepsilon$。
定理中的 $Z_{\rm c}$ 达到这个值。

□

这是该补偿类的最小性，不是所有 CPTP 拟合的最优 diamond 距离。
数据映射 $X\mapsto Y$ 使用负谱部分，通常非线性，是数学重构而非对 $X$ 实施的物理信道。
式 $\Phi_{X_0}=(1+\varepsilon)\Psi-\varepsilon\Gamma$
给“结果与误差均有归一化关系”一个精确版本：
$\Psi,\Gamma$ 均为归一通道，系数之和为一；负系数是误差表示，
不是负概率或实际随机分支。修复是邻近模型的数学构造，不自动供应原生门编译。


#### 推论 6.5（同一实际读口的共同解释）

若实际效果 $0\le F\le I$ 满足 $|y_F-\operatorname{Tr}(XF)|\le\tau_F$，则同一个 $Y$ 满足
$$
|y_F-\operatorname{Tr}(YF)|\le\tau_F+\frac b2+\varepsilon.
$$


**证明。**

探针输入归一给 $\|X-Y\|_1\le\|\Phi_X-\Psi\|_\diamond$。
又 $\operatorname{Tr}(X-Y)=0$，故效果对它的读数绝对值不超过一半迹范数。

□

这里 $D$ 是已知、共同标定的探针边缘。若实际制备连 $D$ 或其纯性也不确定，
须另给输入误差模型；上述边缘缺陷 $M$ 不能自动吸收所有未知制备变化。


#### 推论 6.6（完整报告的共同修复）

若输出载体为全部报告扇区的直和 $B=\bigoplus_r B_r$，
且候选 $X=\bigoplus_r X_r$ 已按这些扇区块对角，
则上述修复仍给 $Y=\bigoplus_rY_r$，每个 $Y_r\ge0$，
且 $\sum_r\operatorname{Tr}_{B_r}Y_r=D$。故它定义一组 CP 分支，其和保迹。


**证明。**

$\tau=I_B/m$ 块对角，边缘校正保持块结构；
块对角 Hermitian 矩阵的正负谱部分仍块对角，后续补偿和归一化亦然。
对每个 $Y_r$ 使用固定探针对应即可。

□

应修复带全部标签的总过程，再取其分支；不能把每个迹递减分支分别修成保迹通道。
这里的负谱预算可由全矩阵界或各块检验供应，块对角前提须来自已声明的报告接口。


#### 推论 6.7（同一过程的消失误差极限）

在固定输入输出接口上，若同一个 HP 映射 $\Phi$ 有 CPTP 近似 $\Psi_n$，
且 $\|\Phi-\Psi_n\|_\diamond\to0$，则 $\Phi$ 本身 CPTP。


**证明。**

Choi 矩阵连续依赖映射；正半定锥与保迹边缘等式在有限维中闭。
将定理 [2.2](#thm:exact) 的条件传到极限即可。

□

此结论要求同一映射和固定接口上的误差消失；不同上下文的拟合不能直接组成该极限。


## 7 近纯联合输出给近等距或近酉过程


<a id="thm:unitary"></a>

#### 定理 7.1（主 Kraus 分支的近酉界）

设 $\Psi:M_d\to M_m$ 为 CPTP，固定探针输出 $Y$ 满足
$\lambda_{\max}(Y)=1-\ell$。存在主 Kraus 算子 $K_0$ 及剩余 CP 映射
$\mathcal N$，使 $\Psi=\operatorname{Ad}_{K_0}+\mathcal N$。
令
$$
Q=\mathcal N^\dagger(I)=I-K_0^\dagger K_0,\qquad q=\|Q\|_\infty.
$$
则 $q\le\ell/\mu$。若 $q<1$，存在等距 $V:\mathbb C^d\to\mathbb C^m$，满足
$$
\boxed{
\|\Psi-\operatorname{Ad}_V\|_\diamond
\le q+2(1-\sqrt{1-q})\le3q.
}
$$
若 $m=d$，$V$ 为酉。


**证明。**

把 $Y$ 的主特征向量乘 $\sqrt{1-\ell}$ 后，经固定探针向量化取得 $K_0$。
剩余正部分是 $\mathcal N$ 的探针输出，迹为 $\ell$，所以
$\ell=\operatorname{Tr}(DQ)\ge\mu\operatorname{Tr} Q\ge\mu q$。
CP 映射的 diamond 范数等于 $\|\mathcal N^\dagger(I)\|_\infty=q$：
写 Kraus 叠加算子 $W\psi=\sum_aK_a\psi\otimes|a\rangle$，则
$W^\dagger W=Q$；偏迹收缩和左右乘的迹范数界给上界 $\|W\|^2=q$，
在 $Q$ 最大特征向量上的正输入给同值输出迹，达到下界。

$K_0^\dagger K_0=I-Q>0$，极分解给
$K_0=V\sqrt{I-Q}$、$V^\dagger V=I$。
因此 $\|K_0-V\|_\infty=1-\sqrt{1-q}$，且 $\|K_0\|_\infty\le1$。
把 $K_0HK_0^\dagger-VHV^\dagger$ 展开为两项，
连同任意参考应用迹范数理想性，得


$$
\|\operatorname{Ad}_{K_0}-\operatorname{Ad}_V\|_\diamond\le2\|K_0-V\|_\infty
$$

。
与剩余 CP 部分相加，得到结论。

□

若 $m<d$，条件 $q<1$ 不可能成立，因为它会强迫 $K_0$ 单射。
精确 $\ell=0$ 回到项目已有的秩一 Choi 等距／酉结构。


#### 推论 7.2（从原始近纯读数合成误差）

在定理 [6.2](#thm:repair) 中，若另有实际已标定秩一方向 $P$，
使 $\operatorname{Tr}(XP)\ge1-\beta$、$\beta\ge0$，则可取
$$
\bar\ell=\min\left\{1,
\frac{\beta+\|M\|_\infty/m+\varepsilon}{1+\varepsilon}
\right\},\qquad \bar q=\frac{\bar\ell}{\mu}.
$$
若 $\bar q<1$，存在上述 $V$，满足
$$
\|\Phi_X-\operatorname{Ad}_V\|_\diamond
\le b+2\varepsilon+\bar q+2(1-\sqrt{1-\bar q})
\le b+2\varepsilon+3\bar q.
$$


**证明。**

$Z_{\rm c}\ge0$，而
$|\operatorname{Tr}[P(M\otimes I_m/m)]|\le\|M\|_\infty/m$，故
$\operatorname{Tr}(PY)\ge[1-\beta-\|M\|_\infty/m]/(1+\varepsilon)$。
于是 $\ell\le\bar\ell$，结合前两定理及所用函数的单调性。

□



#### 命题 7.3（完整纯性与局部过程纯性不同）

给定 $P_D$ 和内部 ready 记录 $|0\rangle_E$，
整体等距
$|i\rangle_A|0\rangle_E\mapsto|i\rangle_B|i\rangle_E$
给纯输出
$$
|\Xi\rangle=\sum_i\sqrt{s_i}|i\rangle_R|i\rangle_B|i\rangle_E.
$$
但 $RB$ 读口为
$X_{RB}=\sum_i s_i|ii\rangle\langle ii|$，秩为 $d$。


**证明。**

按正交 $E$ 标签取偏迹，所有不同指标的交叉项消失。

□

$E$ 仍在完整观察者内；偏迹规定的是所读接口。
所以完整 $\Omega$ 纯不能替代近酉定理的联合输出近纯前提。


## 8 AURIC 三轴、过程方向与相干相位

对一个已确定的二能级接口，
$\rho=(I+\bm r\cdot\bm\sigma)/2$，
正性为 $\|\bm r\|\le1$，纯性为 $\|\bm r\|=1$。
项目 V38 已把 AURIC 五矩的仿射坐标与过程的 $(T,t)$ 参数对应，
并明确该五维实关系矩阵不是 $\mathbb C^5$ 振幅上的酉矩阵。[[3](#bib-v38)]
一个态的三实坐标，与作用于所有输入的过程参数承担不同角色。

对本段的 qubit 到 qubit 过程，明确取 $R\simeq A\simeq B\simeq\mathbb C^2$，
固定探针可写为
$$
|\gamma_s\rangle=\sqrt{s}|00\rangle+\sqrt{1-s}|11\rangle,\quad
0<s<1,\quad \mu=\min(s,1-s).
$$
一般联合态不能由单体三轴读数识别：例如
$\sqrt{s}|00\rangle+e^{i\varphi}\sqrt{1-s}|11\rangle$ 的单体边缘与 $\varphi$ 无关。
本探针的联合式来自已声明的相干标定；全部矩阵单位信息保存在展开中的
$\sqrt{s_i s_j}E_{ij}\otimes\Phi(E_{ij})$。
最坏稳定性在 $s=1/2$ 时最佳，但联合过程正性须在四维 $RB$ 上检验；
不能把维数继续取作二。


#### 命题 8.1（通道不能识别相干受控程序的门相位）

$U$ 和 $-U$ 给同一个状态通道 $\operatorname{Ad}_U$，
但其共同控制实现可产生正交输出。


**证明。**

取 $U=I$，控制为 $|+\rangle$。
受控 $I$ 保持 $|+\rangle$，受控 $-I$
等于控制上的 $Z$，把它送到 $|-\rangle$。
两个目标状态通道完全相同，控制输出却正交。

□

所以近酉过程的存在只确定通道及其相位等价类；
若过程还进入相干受控门序列，控制相位与保留记录的共同标定须另行给出。
这一边界亦已在 V38 §4 明确，本轮保留而不以通道误差替代它。[[3](#bib-v38)]


## 9 唯一 $\Omega$ 内的记忆与过程组合


<a id="thm:memory"></a>

#### 定理 9.1（相同局部边缘不能决定未来关联响应）

令 $R,S,M$ 为同一整体中的三个 qubit，
$$
|\Phi_\pm\rangle=\frac{|00\rangle\pm|11\rangle}{\sqrt2},\qquad
|\Omega\rangle=
\frac{|0\rangle_R|\Phi_+\rangle_{SM}
+|1\rangle_R|\Phi_-\rangle_{SM}}{\sqrt2}.
$$
条件于内部记录 $R=0,1$，两支均有
$\rho_S=\rho_M=I/2$。
但同一个 $U=(H_S\otimes I_M)\mathrm{CNOT}_{S\to M}$ 给不同的系统后继
$|0\rangle\langle0|$ 与 $|1\rangle\langle1|$。
因而不存在只依赖当前 $S$ 边缘、且不依赖历史的单一更新，能拟合两支。


**证明。**

CNOT 把 $\Phi_\pm$ 分别送到 $|\pm\rangle_S|0\rangle_M$，
随后 $H$ 给 $|0\rangle_S|0\rangle_M$ 和 $|1\rangle_S|0\rangle_M$。
单一更新必须把相同输入 $I/2$ 送到两个不同输出，矛盾。
这个矛盾甚至不需要预先假定更新线性。

□

此处只有一个固定本体与同一个联合酉；差别完全在内部关联中。
它不排除对无条件的单个输入输出对拟合一个替换通道，
只排除用该拟合同时预测两种实际内部条件响应。


#### 定义 9.2（共同记忆上的完整仪器）

对完整既有报告 $h$，指定保留记忆空间 $\mathcal M_h$。
每一步给 CP 分支


$$
\mathcal I_{k,r|h}:\mathcal B(\mathcal M_h)\to\mathcal B(\mathcal M_{hr})
$$

，
包含所有失败、停止与缺席标签，且
$$
\sum_r\mathcal I_{k,r|h}^\dagger(I)=I.
$$
下一步必须在同一个已识别的后继记忆接口上作用。
以后会再次影响响应的内部角色，须保留在该记忆中。

> **算子域注（Markdown 编者）。** 下述矩阵仪器递归按全文有限维复接口理解：每个实际比较阶段的共同记忆与报告直和均已指定。若另取可数报告或无限维记忆，密度算子须在迹类中，分支和及整体更新须另满足相应收敛与正规性条件；这些推广不由有限矩阵式自动认证。后文同一完整 Hilbert 载体上的酉算子级数定理则按其自身所述算子范数前提使用。




#### 定理 9.3（完整报告的归一递归）

令 $\rho_\varnothing=\rho_0$ 为密度矩阵，
$\rho_{hr}=\mathcal I_{k,r|h}(\rho_h)$、$p(h)=\operatorname{Tr}\rho_h$。
则
$$
\rho_h\ge0,\quad
\sum_rp(hr)=p(h),\quad
\Xi_n:=\bigoplus_{|h|=n}\rho_h\ge0,\quad
\operatorname{Tr}\Xi_n=1.
$$


**证明。**

CP 保持每支正性，仪器完备式给逐父节点质量守恒；按层归纳。
终止历史可用固定停止标签延长，故全部深度记录均被保留。

□

该结构在 $\Omega$ 主文 §6 已有；本轮把重构出的 CPTP 模型接入它时，
必须同时识别这些记忆与报告接口。[[2](#bib-omega), [5](#bib-v58)]
只把各阶段的正矩阵并列起来，不供应其共同过程或共同中间接口。
在已识别的中间空间上，未归一 Choi 复合准确满足
$$
C_{\Psi\circ\Phi}=(\operatorname{id}\otimes\Psi)(C_\Phi);
$$
展开矩阵单位便可验证。带权探针先按定理 [2.2](#thm:exact) 转回相同约定。


## 10 递归误差：报告接口与完整相干载体


<a id="thm:history"></a>

#### 定理 10.1（保留报告与量子记忆的自适应误差界）

将每组仪器打包为
$\mathcal C_{k|h}(Z)=\bigoplus_r\mathcal I_{k,r|h}(Z)$。
两套协议具有共同载体、报告标签和后继识别，且
$$
\epsilon_k=\sup_h\frac12
\|\mathcal C_{k|h}-\widetilde{\mathcal C}_{k|h}\|_\diamond.
$$
若初始半迹距离为 $D_0$，则
$$
\boxed{
\frac12\|\Xi_n-\widetilde\Xi_n\|_1
\le\min\left\{1,D_0+\sum_{k=1}^n\epsilon_k\right\}.
}
$$
全部报告字符串及其任意共同经典后处理的总变差也受此界控制。


**证明。**

把下一步写成按历史分块的 CPTP 映射 $\mathcal T_k$。
用三角不等式及 CPTP 收缩，得到
$$
D_k\le D_{k-1}
+\frac12\|(\mathcal T_k-\widetilde{\mathcal T}_k)
(\widetilde\Xi_{k-1})\|_1.
$$
第二项在正交历史块上求和。每个正质量块归一后至多产生 $\epsilon_k$，
再按原质量求和仍不超过 $\epsilon_k$；零质量块贡献零。
归纳即得。读取报告是共同 CPTP 操作，故不增半迹距离。

□



#### 命题 10.2（经典核的乘积界不能直接移用于相干记忆）

即使每步半 diamond 距离为 $\epsilon_k$，
最终误差也未必小于 $1-\prod_k(1-\epsilon_k)$。


**证明。**

比较恒等过程与两次 $U=e^{-i\pi\sigma_y/6}$。
对任意含参考的纯输入，单次输出重叠为
$\cos(\pi/6)-i\sin(\pi/6)\langle I\otimes\sigma_y\rangle$，
其模至少为 $\cos(\pi/6)$，故输出迹距离至多 $1/2$；
输入 $|0\rangle$ 达到，因而半 diamond 距离恰为 $1/2$。
两次后该输入的迹距离为 $\sin(\pi/3)=\sqrt3/2>3/4$，
超过所称乘积界。共同最优二结果测量还可把此差别转成报告总变差。

□

> **证明接口注（Markdown 编者）。** 从含参考的归一纯输入距离界转到半 diamond 距离，使用保 Hermitian 差映射的纯参考输入最优化：Watrous 作者公开稿第 3 章定理 3.51，文献 [10](#bib-watrous3)。这里比较的是两条通道；所用纯态半迹距离公式可由两向量张成空间上的谱分解得到。

因此 v64 的经典核乘积界保留其经典前提。
本节的线性累加界允许相干量子记忆，适用域不同。[[10](#bib-watrous3)]


#### 命题 10.3（未修复候选的组合需要保留范数增长）

若只知 HP 候选 $\Phi_k$ 与 CPTP 模型 $\Psi_k$ 具有共同可组合接口，
且 $\|\Phi_k-\Psi_k\|_\diamond\le\delta_k$，则
$$
\boxed{
\|\Phi_n\cdots\Phi_1-\Psi_n\cdots\Psi_1\|_\diamond
\le\prod_{k=1}^n(1+\delta_k)-1.
}
$$


**证明。**

$\|\Phi_k\|_\diamond\le1+\delta_k$。
从复合差的望远镜展开，或递推
$e_k\le(1+\delta_k)e_{k-1}+\delta_k$、$e_0=0$，得到所述乘积界。

□

这里是一般代数范数界，未修复的复合输出未必为密度矩阵。
定理 [10.1](#thm:history) 的加性界要求两套比较更新都为 CPTP；
不能只凭每个 HP 候选接近一个通道，就对该候选使用通道收缩性。


#### 定理 10.4（完整相干观察者的对齐等距界）

设实际与比较模型在逐步共同识别的完整载体上采用等距 $V_k,W_k$，
$\|V_k-W_k\|_\infty\le a_k$，两个初始向量均归一，距离为 $e_0$。
则
$$
\boxed{
\|\Psi_n-\widetilde\Psi_n\|
\le e_0+\sum_{k=1}^n a_k.
}
$$
完整纯态的迹距离及其共同实际测量的总变差，不超过该界与一的最小值。


**证明。**

每步用
$$
\|V_k\Psi-W_k\widetilde\Psi\|
\le\|\Psi-\widetilde\Psi\|+\|V_k-W_k\|_\infty
$$
，
再归纳。归一纯态满足


$$
\sqrt{1-|\langle\Psi,\widetilde\Psi\rangle|^2}\le\|\Psi-\widetilde\Psi\|
$$

。

□

仪器的 Kraus 完备式给相干等距


$$
V(|h\rangle|\psi\rangle)=\sum_{r,a}|hr\rangle K_{r,a|h}|\psi\rangle|a\rangle
$$

；
保留记录与内部垃圾可继续在同一完整载体上演化。
实际比较仍需对齐这些角色与相位。
例如 $V_0\psi=\psi\otimes|0\rangle$、
$V_1\psi=\psi\otimes|1\rangle$ 都在系统上实现恒等通道，
但完整输出正交。局部 diamond 距离为零，不决定完整本体表示中的距离。

以上界控制声明的物理记录与共同读出。
若另行把精确波函数坐标作为确定性的经典标签附加，仍适用 v64 的图测度反例，
其总变差可为一。实际记录应进入协议；数学状态标签不是自动取得的记录。


<a id="thm:series"></a>

#### 定理 10.5（可求和门误差给相对酉关系的极限）

在同一个完整 Hilbert 载体上，给两列酉算子 $U_k,V_k$，
$\|U_k-V_k\|_\infty\le a_k$，且 $\sum_{k\ge1}a_k<\infty$。
定义
$$
A_n=U_n\cdots U_1,\qquad B_n=V_n\cdots V_1,\qquad
R_n=B_n^\dagger A_n.
$$
则 $R_n$ 在算子范数下收敛到一个酉算子 $R_\infty$，且
$$
\boxed{\|R_\infty-R_n\|_\infty\le\sum_{k>n}a_k.}
$$


**证明。**

$$
R_{n+1}-R_n
=B_n^\dagger(V_{n+1}^\dagger U_{n+1}-I)A_n,
$$
范数至多 $a_{n+1}$。可求和性给范数 Cauchy 性与尾界。
每个 $R_n$ 酉，取范数极限于
$R_n^\dagger R_n=R_nR_n^\dagger=I$，得到极限亦酉。

□

该极限描述同一个固定 $\Omega$ 上相对于比较门序列的误差关系；
不要求实际 $\Psi_n=A_n\Omega$ 趋于静止。
对逐步扩张的有限接口应用它，需先给与完整载体相容的同一嵌入。
可求和性在此是充分条件，不声称必要。


#### 命题 10.6（单步误差趋零不足以给整体收敛）

取 $V_k=I_2$、$U_k=\operatorname{diag}(1,e^{i/k})$、同一个初态 $\Omega=|+\rangle$。
每步均酉，且 $\|U_k-V_k\|_\infty\le1/k\to0$，
但实际态及其射线不收敛。


**证明。**

积累相位为 $h_n=\sum_{k=1}^n1/k$，它递增无界，且步长趋零。
首次跨越 $2\pi j$ 与 $(2j+1)\pi$ 的指标分别趋于无穷，
其越界量均至多对应步长而趋零。
因此输出分别沿两子列趋于 $|+\rangle$ 和 $|-\rangle$，二者正交。

□

这给递归与级数的直觉一个准确结论：酉性控制范数，
可求和的对齐误差则足以控制相对关系的收敛；仅有归一化或单步趋零还没有这个结论。


## 11 合成命题与量子起源的准确推进


#### 推论 11.1（同一接口上的有限过程重构）

若同一完整观察者中已经给出：

1. 固定有限复接口与同一 HP 线性响应、已标定的纯满 Schmidt 内部探针；
2. 同一联合响应的关系相容、实际方向覆盖与增益，满足
$N\theta<1$，从而有命题 [5.1](#prop:positive) 的负谱预算；
3. 已识别的参考边缘残差 $M$；

则存在同一个 CPTP 模型 $\Psi$，满足定理 [6.2](#thm:repair) 的
$b+2\varepsilon$ 过程界与全部已给残差读口的共同读出界。
若另有充分小的联合输出近纯预算，则可进一步取邻近等距模型，等维时取邻近酉模型。
若各阶段还具有同一保留记忆与完整报告的实际契约，
应修复整个带报告标签的通道，所重构模型可按完整仪器递归组合。
若两套被比较协议均满足完整 CPTP 仪器条件，并有该定理要求的每步实际差界，
则适用定理 [10.1](#thm:history) 的线性累加。


**证明。**

依次应用命题 [5.1](#prop:positive)、定理 [6.2](#thm:repair)、
定理 [7.1](#thm:unitary) 及完整报告修复推论，再使用相应的归一递归与误差定理。
实际过程的跨阶段应用使用声明的同一过程和记忆条件；
这些条件不是前几个矩阵不等式的自动后果。

□


本轮因此给出三个不同而相容的数学角色：
$$
\begin{aligned}
\text{纯满 Schmidt 关系}&\quad\Longleftrightarrow\quad
\text{等维单探针的全 HP 正性反映},\\
\text{均匀 Schmidt 权重}&\quad\Longleftrightarrow\quad
\text{最优最坏识别条件数},\\
\text{参考边缘守恒}&\quad\Longleftrightarrow\quad
\text{整个线性过程保迹}.
\end{aligned}
$$
与 v64 的平方指数选择结合时，必须保留共同复结构、共同标定及实际概率接口。
本轮没有再从裸加法乘法或 $\log$ 推出平方；它研究的是已有复线性、平方读出层次上的
动力学公理怎样改写为一个固定内部关联接口的正性、边缘与纯性条件。
复数域、实际张量分解、忠实制备、充分联合读出、同一过程及共同记忆，
仍是完整起源理论需取得的条件。唯一 $\Omega$ 使这些角色全部内生；
数学证明则说明一旦关系条件成立，它们如何共同限制允许的过程与递归误差。


**固定来源与文献**

> **来源归属注（Markdown 编者）。** 下列“本轮”“前轮”及“来源席位”的阅读与访问报告均引自原作者原稿；Choi 1975 在原稿中的报告仅为出版社元数据与摘要，未取得全文。这里的证明依据是本文纸面证明与所引 Watrous 作者公开稿，不将该历史报告改称全文核读，也不解除另案 V54 的实际 Choi 原文缺口。


<a id="bib-head"></a>

**[1]**

[trureturing 固定提交 5cf95e1a<wbr>e01f7ed8<wbr>6735c04a<wbr>d8d752cb<wbr>19b1a58b](https://github.com/the-omega-institute/trureturing/tree/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b)。
本轮活动请求失败，固定来源来自前轮取得；本文不声称核实了之后的增量。

<a id="bib-omega"></a>

**[2]**

[AURIC $\Omega$ 静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，
本轮核读 §§6、8；其中 Choi、反馈仪器与边缘拼接界限为已有内容。

<a id="bib-v38"></a>

**[3]**

[AURIC V38：完整量子过程、内部记忆与秩边界稳定性](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_COMPLETE_QUANTUM_PROCESSES_INTERNAL_MEMORY_AND_RANK_BOUNDARY_STABILITY_V38.md)，
本轮核读 §§3--4、7--8，来源席位另核读 §11。

<a id="bib-v52"></a>

**[4]**

[AURIC V52：纯态、商几何、二次关系生成元与无损递归](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)，
本轮核读 §8 后半，特别是推论 8.4。

<a id="bib-v58"></a>

**[5]**

[AURIC V58：关系公理、共同复相位与条件量子重构](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md)，
本轮核读 §§10--11。

<a id="bib-v59"></a>

**[6]**

[AURIC V59：局部层析、相干读出轨道与量子正性起源](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_LOCAL_TOMOGRAPHY_COHERENT_READOUT_ORBITS_AND_QUANTUM_POSITIVITY_ORIGIN_V59.md)，
前轮主文全读；本轮来源席位重读 §§3--5、7--10。

<a id="bib-choi"></a>

**[7]**

M.-D. Choi, Completely positive linear maps on complex matrices,
*Linear Algebra and its Applications* 10(3), 285--290 (1975),
[doi:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795%2875%2990075-0)。
本轮确认出版社元数据与摘要；全文取得失败，本文所需证明自足并核读下列作者教材。

<a id="bib-faithful"></a>

**[8]**

G. M. D'Ariano and P. Lo Presti,
Imprinting Complete Information about a Quantum Channel on Its Output State,
*Physical Review Letters* 91, 047902 (2003),
[arXiv:quant-ph/0211133](https://arxiv.org/abs/quant-ph/0211133)。
本轮核读原始预印本的固定探针、纯态满 Schmidt 性、混合忠实性与逆映射误差讨论。

<a id="bib-watrous2"></a>

**[9]**

J. Watrous, *The Theory of Quantum Information*, Cambridge University Press (2018),
[作者公开稿第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，
本轮核读 Theorems 2.22、2.25 的相关证明与 2.26 的保迹条件。

<a id="bib-watrous3"></a>

**[10]**

J. Watrous, 同上，
[作者公开稿第 3 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf)，
本轮核读 diamond 范数定义、Proposition 3.44 与 Proposition 3.48 的复合界。

```tex
\end{document}
```

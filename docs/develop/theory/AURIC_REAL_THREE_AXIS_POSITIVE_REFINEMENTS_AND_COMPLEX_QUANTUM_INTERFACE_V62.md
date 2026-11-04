> **作者原稿声明。** 下列编译、字体、PDF 元数据与版式声明，以及正文关于历史 HEAD、取得时点、比较、来源阅读和未运行数学程序的陈述，均按作者报告保留；它们不表示本 Markdown 转写者重新执行了这些历史操作。

**作者原稿的编译与版式声明（LaTeX 字面文本）**

<p><code>% !TeX program = xelatex</code></p>
<p><code>% Compile twice with XeL<wbr>aTeX. Optional: \def\AUR<wbr>ICFontPath{/absolute/fon<wbr>t/path/}</code></p>
<p><code>% All mathematics below <wbr>consists of paper proofs<wbr>; no mathematical progra<wbr>m was run.</code></p>
<p><code>\documentclass[11pt,a4pa<wbr>per]{article}</code></p>
<p><code>\usepackage[margin=23mm,<wbr>headheight=16pt]{geometr<wbr>y}</code></p>
<p><code>\usepackage{fontspec}</code></p>
<p><code>\ifdefined\AURICFontPath</code></p>
<p><code> \setmainfont[Path=\AURI<wbr>CFontPath,BoldFont=NotoS<wbr>erifCJKsc-Bold.otf,</code></p>
<p><code> ItalicFont=NotoSerifCJK<wbr>sc-Regular.otf,BoldItali<wbr>cFont=NotoSerifCJKsc-Bol<wbr>d.otf]{NotoSerifCJKsc-Re<wbr>gular.otf}</code></p>
<p><code>\else</code></p>
<p><code> \IfFontExistsTF{Noto Se<wbr>rif CJK SC}{</code></p>
<p><code> \setmainfont[ItalicFont<wbr>=Noto Serif CJK SC,BoldI<wbr>talicFont=Noto Serif CJK<wbr> SC Bold]{Noto Serif CJK<wbr> SC}</code></p>
<p><code> }{\setmainfont[BoldFont<wbr>=FandolSong-Bold.otf,Ita<wbr>licFont=FandolSong-Regul<wbr>ar.otf,</code></p>
<p><code> BoldItalicFont=FandolSo<wbr>ng-Bold.otf]{FandolSong-<wbr>Regular.otf}}</code></p>
<p><code>\fi</code></p>
<p><code>\setmonofont{Latin Moder<wbr>n Mono}</code></p>
<p><code>\XeTeXlinebreaklocale &quot;z<wbr>h&quot;</code></p>
<p><code>\XeTeXlinebreakskip=0pt <wbr>plus 1pt</code></p>
<p><code>\usepackage{amsmath,amss<wbr>ymb,amsthm,mathtools,bm}</code></p>
<p><code>\usepackage{booktabs,arr<wbr>ay,tabularx,enumitem,fan<wbr>cyhdr,xcolor,needspace}</code></p>
<p><code>\definecolor{auricblue}{<wbr>RGB}{24,53,79}</code></p>
<p><code>\usepackage[unicode,colo<wbr>rlinks=true,linkcolor=au<wbr>ricblue,urlcolor=auricbl<wbr>ue,citecolor=auricblue]{<wbr>hyperref}</code></p>
<p><code>\hypersetup{pdftitle={AU<wbr>RIC v62：从实三轴与正细化关系重构复量子接<wbr>口},</code></p>
<p><code> pdfauthor={AURIC resear<wbr>ch continuation},</code></p>
<p><code> pdfsubject={Faithful fi<wbr>nite calibration, stable<wbr> Clifford structure, cou<wbr>ntable effect refinement<wbr>s, Born representation, <wbr>and common-phase compati<wbr>bility}}</code></p>
<p><code>\newcommand{\R}{\mathbb <wbr>R}</code></p>
<p><code>\newcommand{\C}{\mathbb <wbr>C}</code></p>
<p><code>\newcommand{\Q}{\mathbb <wbr>Q}</code></p>
<p><code>\newcommand{\HH}{\mathca<wbr>l H}</code></p>
<p><code>\newcommand{\Tr}{\operat<wbr>orname{Tr}}</code></p>
<p><code>\newcommand{\rank}{\oper<wbr>atorname{rank}}</code></p>
<p><code>\newcommand{\Sym}{\opera<wbr>torname{Sym}}</code></p>
<p><code>\newcommand{\Herm}{\oper<wbr>atorname{Herm}}</code></p>
<p><code>\newcommand{\Eff}{\opera<wbr>torname{Eff}}</code></p>
<p><code>\newcommand{\sgn}{\opera<wbr>torname{sgn}}</code></p>
<p><code>\newcommand{\Ran}{\opera<wbr>torname{Ran}}</code></p>
<p><code>\newcommand{\op}{\mathrm<wbr>{op}}</code></p>
<p><code>\newcommand{\calA}{\math<wbr>cal A}</code></p>
<p><code>\newcommand{\repo}[2]{\h<wbr>ref{https://github.com/t<wbr>he-omega-institute/trure<wbr>turing/blob/b9087e51948f<wbr>a40e487ce8039c2b126d0dff<wbr>7a66/docs/develop/theory<wbr>/#1}{#2}}</code></p>
<p><code>\theoremstyle{definition<wbr>}</code></p>
<p><code>\newtheorem{definition}{<wbr>定义}[section]</code></p>
<p><code>\newtheorem{theorem}[def<wbr>inition]{定理}</code></p>
<p><code>\newtheorem{proposition}<wbr>[definition]{命题}</code></p>
<p><code>\newtheorem{corollary}[d<wbr>efinition]{推论}</code></p>
<p><code>\newtheorem{lemma}[defin<wbr>ition]{引理}</code></p>
<p><code>\newtheorem{remark}[defi<wbr>nition]{说明}</code></p>
<p><code>\renewcommand{\proofname<wbr>}{证明}</code></p>
<p><code>\renewcommand{\abstractn<wbr>ame}{摘要}</code></p>
<p><code>\renewcommand{\refname}{<wbr>固定来源与文献}</code></p>
<p><code>\setlength{\parindent}{1<wbr>.8em}</code></p>
<p><code>\setlength{\parskip}{2pt<wbr>}</code></p>
<p><code>\setlength{\emergencystr<wbr>etch}{3em}</code></p>
<p><code>\setlist{nosep,leftmargi<wbr>n=2em}</code></p>
<p><code>\pagestyle{fancy}\fancyh<wbr>f{}</code></p>
<p><code>\fancyhead[L]{\small AUR<wbr>IC：实三轴、正细化与复量子接口}</code></p>
<p><code>\fancyhead[R]{\small v62<wbr> / 2026-11-01}</code></p>
<p><code>\fancyfoot[C]{\thepage}</code></p>
<p><code>\allowdisplaybreaks[2]</code></p>

# 从实三轴与正细化关系重构复量子接口

## 忠实有限校准、平方读出与共同相位的稳定传导

AURIC 量子起源研究　定义、定理与纸面证明　v62.0

2026 年 11 月 1 日　Asia/Singapore

### 摘要

本文在唯一固定本体与完整内生观察者的图景内，继续削减量子接口重构中彼此混用的假设。
在已给实正内积、方向线性算子及同源忠实二次校准的条件下，六个有理方向的锐性缺陷为零，
即推出三轴 Clifford 关系及中心正交复结构 $J$；小缺陷还给同一载体上的邻近精确模型和明确常数。
在所生成的复矩阵接口上，可数有理效果域中的同一效果身份与二、三结果菜单归一，
推出正可加、自动范数连续、全部实关系一致性及唯一 Born 密度表示，无需另设振幅权重乘性。
无理秩一边界不能被有理效果直接上下序逼近；本文给半尺度与单位缓冲的实际读出桥及误差界。
递归细化误差具有逐节点可加预算。复合接口的共同虚单位还须满足闭路符号相容，
其固定来源缺陷控制共同扇区质量及条件投影误差。
实正几何、实际菜单取得、忠实校准、共同切口、复合因子及门的定向相容仍是前件。
所得是可逐项检查的条件重构，不是从本体唯一性单独推出全部物理规律。

## 1　本轮推进及固定项目来源

上一轮 v61 在有界乘性权重类中，用一个固定三端口来源、指定二元控制的完整回返及粗事件守恒选择了指数二。
该结论解释了平方作为递归内部细分的零漂移权重，但仍预设复线性接口、权重函数及实际比较合同。
本轮沿两条不同方向进一步组织前件：

$$
\boxed{\begin{gathered}
\text{实正几何}+\text{六方向忠实锐性校准}
\Longrightarrow\text{中心复结构 }J;\\
\text{可数有理效果}+\text{二、三菜单正细化相容}
\Longrightarrow\text{唯一 Born 表示}.
\end{gathered}}
$$

第一条解释指定三轴读出代数中的共同虚单位；第二条选择该有序效果几何上的概率赋值。
两者的实际来源条件均将在正文列明。

### 1.1　本轮唯一活动快照及真实增量

本轮唯一实际活动 HEAD 响应固定提交为
<code>b9087e51948fa40e<wbr>487ce8039c2b126d<wbr>0dff7a66</code>。

取得完成于新加坡时间 2026-11-01 03:53:48.698036，提交时间为 03:44:47。
相对 v61 的 <code>e45f5aa2928bfa0d<wbr>3239246268831d37<wbr>a4146425</code>，前进 12 个提交、涉及 32 个变化路径。
固定比较 JSON 与 diff 的路径集相同；四层来源树均未截断，理论目录仍为 1122 项。
后续读取全部按固定提交或固定树身份进行；此快照不声称在写作完成时仍为活动 HEAD。[[head](#bib-head)]

理论增量只有两份：CDSO 连接成本文稿增加 502 行，K-bonacci 端点关系文稿增加 241 行。
本轮没有新增项目量子起源定理；V53、无序相容原子、V47/V49/V52/V55/V56、Quantum IV 与 RRO 的相关文本均属已存在接口。
字节身份核对不等于独立认证全部历史证明。[[cdso](#bib-cdso)，[kbonacci](#bib-kbonacci)]

K-bonacci 新 §11 在未知 $c>0$、未知非负非零量具 $\ell$、目标 $R=c\ell^{\mathsf T}$、
精确同源重制备及所有初读和完整窗口均收费的合同中，证明同一个固定非自适应安排可共同取得

$$
(P,W,N)=
\begin{cases}(2,3,5),&k=2,\\(k,k(k-1),k^2),&k\ge3.
\end{cases}
$$

末端解码用已读正锚与乘积关系，取得与停止不依读数。
该结论没有给噪声稳定、有限精度或 FIB 类型桥；其中 $k^2$ 是特定取得合同的成本，不是概率平方的推导。
CDSO 的新连接成本估计没有给到本文量子接口的来源桥，故不移用其图论结论。[[kbonacci](#bib-kbonacci)，[cdso](#bib-cdso)]

### 1.2　已有结果与本轮展开的区别

V53 §§3–4 已证明实度量与相容 $J$ 的关系、三轴锐性极化、Clifford 中心复结构、Pauli 最小载体及定向门；
§§7–8 已有复合相位对齐与运输条件。
本文承接这些结果，展开六方向忠实校准、稳定修复常数及闭路缺陷预算。[[v53](#bib-v53)]

《无序相容原子》定理 6.3 已完整证明全效果域正可加赋值的 Born 表示与自动 Lipschitz 性，
并准确归属 Busch 的效果版 Gleason 论证。
本文展开的是可数有理入口、共同满测切口及实际新菜单的缓冲桥，不重新主张标准表示定理的原创性。[[unordered](#bib-unordered)，[busch](#bib-busch)]

### 1.3　完整本体、有限接口及四种不同的“正”

全篇固定同一个实际本体 $\Omega$。环境、参考、控制、程序、记录、自我与预测均属于完整观察者。
在采用或取得酉实现后仍写

$$
\Psi_k=U_k\cdots U_1\Omega.
$$

有限实载体、正校准矩阵、效果代数及内部张量因子均是该来源中声明的关系接口，不另设宇宙外部对象。

本文区分：实内积的正定性、算子的正半定序、正缺陷校准的实际读出、以及报告概率的非负性。
它们通过明示合同相连，不能仅因都称为“正”而互相替代。
特别地，下节的实内积与二次校准是输入或此前已条件取得的结构；本文不先把它们冒称为从无结构逻辑推出的全部 Born 概率。

## 2　六个有理方向如何产生共同虚单位

<a id="def:axes"></a>

#### 定义 2.1（实三轴关系接口及忠实校准）

给非零有限维实内积空间 $(V,g)$，三个实对称算子 $A_1,A_2,A_3$，以及同一个方向线性规则

$$
A(n)=n_1A_1+n_2A_2+n_3A_3.
$$

只考虑六个单位方向

$$
\mathcal S=\left\{e_1,e_2,e_3,
\frac{3e_1+4e_2}{5},\frac{3e_1+4e_3}{5},\frac{3e_2+4e_3}{5}\right\}.
$$

令 $D_n=A(n)^2-I$。
声明同源正校准矩阵 $\sigma\succeq\mu I$，$\mu>0$，$\operatorname{Tr}_{\mathbb{R}}\sigma=1$，
及实际校准数与 $q_\sigma(D_n)=\operatorname{Tr}_{\mathbb{R}}(\sigma D_n^2)$ 的对应。

这里 $\sigma$ 只是忠实正二次校准的矩阵表示。
若将它实现为内部参考的状态读出，满秩参考关系及相应标定仍须实际供应。
完整来源可以是纯的，有限接口的校准仍可忠实；这不把完整观察者改定义为约化态。
六个期望关系也不意味着六次单次测量足以精确判定其为零。

<a id="lem:faithful"></a>

#### 引理 2.2（忠实缺陷界）

对实对称 $D$，若 $\operatorname{Tr}(\sigma D^2)\le\kappa$，则

$$
\boxed{\|D\|_{\mathrm{op}}\le\sqrt{\kappa/\mu}.}
$$

**证明。**

$D^2\succeq0$ 及 $\sigma\succeq\mu I$ 给
$\operatorname{Tr}(\sigma D^2)\ge\mu\operatorname{Tr}(D^2)\ge\mu\|D\|_{\mathrm{op}}^2$。

□

<a id="thm:six"></a>

#### 定理 2.3（六方向的中心复结构认证）

若定义 [2.1](#def:axes) 中六个 $q_\sigma(D_n)$ 均为零，则

$$
\{A_i,A_j\}:=A_iA_j+A_jA_i=2\delta_{ij}I.
$$

令 $J=A_1A_2A_3$，则

$$
\boxed{J^2=-I,\quad J^{\mathsf T}=-J,\quad J^{\mathsf T}J=I,\quad[J,A_i]=0.}
$$

定义 $(a+ib)v=av+bJv$ 后，$V$ 成为复向量空间，且

$$
h(u,v)=g(u,v)+i\,g(Ju,v)
$$

是第一槽共轭线性的复内积，满足 $h(v,v)=g(v,v)$。

**证明。**

引理 [2.2](#lem:faithful) 给所有 $D_n=0$。
三个轴方向首先给 $A_i^2=I$。
对 $n_{ij}=(3e_i+4e_j)/5$，有

$$
A(n_{ij})^2=\frac{9A_i^2+16A_j^2+12\{A_i,A_j\}}{25}=I,
$$

所以 $\{A_i,A_j\}=0$ 对 $i\ne j$ 成立。

三重乘积的平方需三次交换来配对重复生成元，故 $J^2=-I$。
转置反转顺序也需三次交换，故 $J^{\mathsf T}=-J$。
将 $A_i$ 穿过另外两个因子产生两次变号，故 $[J,A_i]=0$。
这些恒等式给复标量作用的一致性及 $J$ 的正交性。

由 $g(Ju,v)=-g(u,Jv)$ 可验证 $h(v,u)=\overline{h(u,v)}$；
又有 $h(u,Jv)=ih(u,v)$、$h(Ju,v)=-ih(u,v)$。
$g(Jv,v)=0$，所以 $h(v,v)=g(v,v)>0$ 对非零 $v$ 成立。

□

因此本接口中的 $i$ 可以定义为一个实际关系算子 $J$ 的作用。
这是在实正几何与特定锐性关系下的结构结论；单纯画出三个正交方向不供应反对易算子。
Clifford 体积元与复结构的代数联系是已有数学，本文使用正平方生成元的约定。[[v53](#bib-v53)，[clifford](#bib-clifford)]

#### 命题 2.4（三轴的最低中心负平方性质）

对 $n$ 个平方为 $I$、两两反对易的生成元，体积元 $\omega=A_1\cdots A_n$ 满足

$$
\omega^2=(-1)^{n(n-1)/2}I,\qquad
\omega A_i=(-1)^{n-1}A_i\omega.
$$

三是体积元同时中心且平方为 $-I$ 的最小正整数情形。

**证明。**

配对需要 $n(n-1)/2$ 次交换；将一个生成元穿过其余 $n-1$ 项给第二式。
$n=1$ 的平方为正；$n=2$ 平方为负但不中心；$n=3$ 同时满足。

□

这复用 V53 命题 4.3 的最低性。更高的 $n\equiv3\pmod4$ 也满足该性质，
所以它不证明物理位置空间只能有三维。读出方向维数、实振幅维数及代数维数是不同对象。[[v53](#bib-v53)]

<a id="prop:pauli"></a>

#### 命题 2.5（Pauli 接口与重数）

以 $J$ 作为乘 $i$，存在复正交基使

$$
A_1=\sigma_x\otimes I_m,\quad
A_2=\sigma_y\otimes I_m,\quad
A_3=\sigma_z\otimes I_m.
$$

因此 $\dim_{\mathbb{R}}V=4m$，所生成实代数为 $M_2(\mathbb{C})\otimes I_m$；其不可约情况为 $m=1$。

**证明。**

$A_i$ 与 $J$ 对易并实自伴，故为复 Hermitian。
$A_1$ 等距互换 $A_3$ 的正、负复特征空间，两者同维 $m$。
选正空间的复正交基 $e_k$，以 $A_1e_k$ 作负空间基，得到 $A_3=\sigma_z\otimes I_m$ 与 $A_1=\sigma_x\otimes I_m$。
由 $J=A_1A_2A_3=iI$ 得 $A_2=iA_1A_3=\sigma_y\otimes I_m$。
Pauli 矩阵连同 $I$ 及其乘 $i$ 张成全部 $M_2(\mathbb{C})$。

□

其自伴部分是 $I,A_1,A_2,A_3$ 的四维实线性包。
当 $m>1$，这三个读出并不分辨所有重数关系，也不自动取得整个 $M_{2m}(\mathbb{C})$ 的效果域。
原生 FIB 五模式标签与该实 $4m$ 维算子载体的对应，需要另外的类型桥；标签数不能直接当作振幅维数。[[v53](#bib-v53)]

### 2.1　忠实性缺失时的反例

令

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

在 $\mathbb{R}^4$ 上取 $B_1=X\otimes I_2,B_2=J_0\otimes J_0,B_3=Z\otimes I_2$。
它们是实对称反对易对合。
在 $V=\mathbb{R}^4\oplus\mathbb{R}$ 上令 $A_i=B_i\oplus1$，并取单位探针 $\psi=(v,0)$。
六个正缺陷在这个纯探针上的期望全部为零，但最后一维有 $\{A_i,A_j\}=2$。
全实五维空间不可能承载 $J^2=-I$，因为取行列式将给 $(\det J)^2=-1$。

因此一个普通纯探针的零缺陷只控制被它忠实探测到的部分。
同一个完整纯来源若带有充分内部参考，可以供应忠实校准；这需要实际参考关系，不能由“本体唯一”替代。

## 3　小误差是否仍允许共同复结构

<a id="thm:repair"></a>

#### 定理 3.1（近似反对易三轴的显式修复）

设 $A_i$ 为实对称对合，并有

$$
\|\{A_i,A_j\}\|_{\mathrm{op}}\le\epsilon\quad(i\ne j),\qquad0\le\epsilon<\tfrac12.
$$

则同一实载体上存在精确 Clifford 三轴 $X_i$，使

$$
\boxed{\|X_1-A_1\|=0,\quad\|X_2-A_2\|\le\epsilon,\quad\|X_3-A_3\|\le4\epsilon.}
$$

其中心复结构 $J=X_1X_2X_3$ 满足

$$
\boxed{\|J-A_1A_2A_3\|\le5\epsilon.}
$$

本节未标下标的范数均为算子范数。

**证明。**

令 $X_1=A_1$，并定义

$$
B_2=\tfrac12(A_2-X_1A_2X_1).
$$

它对称、与 $X_1$ 反对易，且 $\|B_2-A_2\|\le\epsilon/2=:d$。
因为 $A_2$ 正交，

$$
(1-d)\|v\|\le\|B_2v\|\le(1+d)\|v\|.
$$

故 $B_2$ 可逆，实特征值模长均在 $[1-d,1+d]$ 内。
令 $X_2=\operatorname{sgn}(B_2)$，有限维实谱分解给 $X_2$ 对称、$X_2^2=I$，
且 $\|X_2-B_2\|\le d$。
符号函数为奇函数，所以 $X_1X_2X_1=-X_2$，并有 $\|X_2-A_2\|\le\epsilon$。

对 $i=1,2$ 定义算子空间上的压缩投影

$$
\mathcal P_i(T)=\tfrac12(T-X_iTX_i).
$$

由于 $X_1X_2=-X_2X_1$，两种共轭映射对易，故 $\mathcal P_1\mathcal P_2=\mathcal P_2\mathcal P_1$。
令 $B_3=\mathcal P_1\mathcal P_2(A_3)$，则它对称且同时与 $X_1,X_2$ 反对易。
又有

$$
\|\{X_2,A_3\}\|\le\|\{A_2,A_3\}\|+2\|X_2-A_2\|\le3\epsilon.
$$

所以

$$
\|B_3-A_3\|
\le\|\mathcal P_2(A_3)-A_3\|+\|\mathcal P_1(A_3)-A_3\|
\le2\epsilon<1.
$$

同样的谱论证允许定义 $X_3=\operatorname{sgn}(B_3)$，并给 $\|X_3-A_3\|\le4\epsilon$。
奇函数演算保持与 $X_1,X_2$ 的反对易性，故三轴精确满足 Clifford 关系。
最后按乘积差展开，利用各因子范数为一，得到

$$
\|X_1X_2X_3-A_1A_2A_3\|
\le\|X_2-A_2\|+\|X_3-A_3\|\le5\epsilon.
$$

□

<a id="thm:stable-six"></a>

#### 定理 3.2（六方向全部带误差的稳定认证）

在定义 [2.1](#def:axes) 中，若六个方向均有 $q_\sigma(D_n)\le\kappa$，令

$$
\delta=\sqrt{\kappa/\mu}\le\frac1{40},
$$

则存在精确三轴 $X_i$ 及中心正交复结构 $J=X_1X_2X_3$，满足

$$
\boxed{\|X_1-A_1\|\le\delta,\quad\|X_2-A_2\|\le11\delta,\quad\|X_3-A_3\|\le41\delta,}
$$

$$
\boxed{\|J-A_1A_2A_3\|\le54\delta.}
$$

这些是保守的显式常数，不主张最优。

**证明。**

引理 [2.2](#lem:faithful) 给 $\|D_n\|\le\delta$。
令 $c=\sqrt{1+\delta}$、$a=1-\sqrt{1-\delta}\le\delta$，并置 $S_i=\operatorname{sgn}(A_i)$。
轴缺陷给 $\|A_i\|\le c$、$S_i^2=I$ 及 $\|S_i-A_i\|\le a$。
混合方向满足精确恒等式

$$
12\{A_i,A_j\}=25D_{ij}-9D_i-16D_j,
$$

故 $\|\{A_i,A_j\}\|\le25\delta/6$。
替换为 $S_i$ 后有

$$
\|\{S_i,S_j\}\|
\le\frac{25}{6}\delta+2a(1+c)=:\epsilon\le10\delta\le\tfrac14.
$$

这里用了 $c<3/2$。
对 $S_i$ 应用定理 [3.1](#thm:repair)，再加 $a\le\delta$，得到三个轴的界。
此外

$$
\|J-S_1S_2S_3\|\le50\delta,
\qquad
\|S_1S_2S_3-A_1A_2A_3\|\le a(c^2+c+1)\le4\delta,
$$

最后一步由 $c^2\le41/40$、$c<3/2$ 得到。相加即证。

□

当 $\mu$ 趋零时，同样的期望误差不再提供统一的全算子控制。
本定理给同一载体上的邻近精确模型；符号函数校正是数学构造，没有自动供应实现它的原生门序列、成本或实际控制。
原有其他门也不自动保持新构造的 $J$。

## 4　用二、三结果细化替代预设权重函数

<a id="def:menus"></a>

#### 定义 4.1（同一效果与可数有理菜单）

在已声明的有限维复矩阵接口中，令

$$
V_0=\operatorname{Herm}_d(\mathbb{Q}(i)),\qquad
D=V_0\cap[0,I].
$$

实版本取 $V_0=\operatorname{Sym}_d(\mathbb{Q})$。
这里 $D$ 可数。固定同一实际来源、同一条件切口及同一效果标定，给单一非负函数 $p:D\to[0,\infty)$。
要求对所有带标签的二结果、三结果菜单分别有

<a id="eq:binary"></a>

$$
\begin{gathered}
p(E)+p(F)=1\\\text{若 }E+F=I,\qquad(1)
\end{gathered}
$$

<a id="eq:ternary"></a>

$$
\begin{gathered}
p(E)+p(F)+p(G)=1\\\text{若 }E+F+G=I.\qquad(2)
\end{gathered}
$$

菜单允许零效果及重复效果标签；同一个效果在不同菜单中使用同一个 $p(E)$。

例如 $(I/3,I/3,I/3)$ 是三个不同报告标签，不是只含一个元素的集合。
该定义供应的是所有指定正细化菜单的共同合同；它不表示当前观察者已经执行了无限多次实验。
不同未来读出必须先被对应到同一实际切口，才属于同一个 $p$。

在命题 [2.5](#prop:pauli) 的实际三轴代数中，可直接用 $I,A_1,A_2,A_3$ 的有理系数组合定义 $D$，
通过 Pauli 表示对应到 $d=2$ 的上述域。
这不要求它们在另一个任意实坐标基中有理，也不把重数空间中的全部效果视为已取得。

<a id="lem:add"></a>

#### 引理 4.2（同一补效果推出正可加）

定义 [4.1](#def:menus) 蕴含 $p(0)=0,p(I)=1$，且

$$
\boxed{p(E+F)=p(E)+p(F)\quad(E,F\in D,\ E+F\le I).}
$$

**证明。**

比较 $(I,0)$ 与 $(I,0,0)$ 的归一式得到零与单位的标定。
对一般 $E,F$，置 $G=I-E-F$。
比较菜单 $(E,F,G)$ 与 $(E+F,G)$，同一个 $p(G)$ 相消，得到所需式。

□

这正是上一轮“粗事件守恒”的一个读出关系入口：粗事件 $E+F$ 与其细分保留同一个补效果。
它不从幅度矩阵块对角自动获得；同一效果身份及菜单归一是实际前件。

<a id="thm:born"></a>

#### 定理 4.3（可数有理正细化的 Born 表示）

在定义 [4.1](#def:menus) 下，存在唯一密度矩阵 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，使

$$
\boxed{p(E)=\operatorname{Tr}(\rho E)\quad(E\in D).}
$$

实版本的 $\rho$ 为实对称矩阵，复版本为 Hermitian 矩阵。
而且

$$
\boxed{|p(E)-p(F)|\le\|E-F\|_{\mathrm{op}}.}
$$

因此有唯一连续数学延拓到全部效果域，延拓仍为同一个迹配对。

**证明。**

由引理 [4.2](#lem:add)，若 $E\le F$，则 $p(F)-p(E)=p(F-E)\ge0$，
故 $0\le p(E)\le1$。
把 $E$ 分为 $n$ 个相同部分，再合并 $m$ 份，得到

$$
p((m/n)E)=\frac mn p(E)
$$

对缩放后仍为效果的非负有理系数成立。

对 $A\in V_0$、$A\succeq0$，选正整数 $N\ge\|A\|$，定义

$$
\ell_+(A)=N p(A/N).
$$

两个整数尺度可共同细化到其乘积，前述有理齐次保证定义无关。
对 $A,B\succeq0$，选 $N\ge\|A+B\|$，正可加给 $\ell_+(A+B)=\ell_+(A)+\ell_+(B)$。
它也为非负有理齐次。

每个 $X\in V_0$ 都可写为有理正矩阵之差，例如 $X=(X+NI)-NI$。
定义 $\ell(A-B)=\ell_+(A)-\ell_+(B)$。
若 $A-B=A'-B'$，则 $A+B'=A'+B$，正锥加性保证良定义。
于是 $\ell$ 是有理线性、正且 $\ell(I)=1$ 的泛函。

对有理数 $r>\|X\|$，$-rI\preceq X\preceq rI$ 给 $|\ell(X)|\le r$。
让有理 $r$ 下降到 $\|X\|$，得到

$$
|\ell(X)|\le\|X\|.
$$

故 $\ell$ 在稠密的 $V_0$ 上有界，唯一连续延拓为完整实自伴空间上的实线性泛函 $\bar\ell$。
实线性由有理线性、实系数的有理逼近及连续性得到。

若 $A\succeq0$，取 $X_n\in V_0$ 逼近 $A$，选有理 $\epsilon_n>\|X_n-A\|$ 且趋零。
则 $X_n+\epsilon_nI\succeq0$ 且趋于 $A$，所以 $\bar\ell(A)\ge0$。
有限维迹配对非退化，给唯一自伴矩阵 $\rho$ 表示 $\bar\ell$。
对任意向量 $x$，

$$
x^\dagger\rho x=\bar\ell(xx^\dagger)\ge0,
\qquad\operatorname{Tr}\rho=\bar\ell(I)=1.
$$

最后对 $E-F$ 应用已得范数界，即得 Lipschitz 性。

□

该证明无需预设振幅权重的乘性、相位不变或读数连续性。
它以有序矩阵效果几何和正细化合同为输入；不是从裸逻辑创造了正矩阵锥。
完整效果域上的标准结论已见项目定理 6.3 与 Busch 原论文；本文将入口和实际延拓义务分别显式化。[[unordered](#bib-unordered)，[busch](#bib-busch)]

#### 推论 4.4（全部实关系一致性成为结论）

对数学延拓后的效果，若 $\sum_j c_jE_j=0$，$c_j\in\mathbb{R}$，则

$$
\sum_jc_j\bar p(E_j)=0.
$$

若 $\rho=|\psi\rangle\langle\psi|$ 且 $P$ 为正交投影，则

$$
\bar p(P)=\langle\psi,P\psi\rangle=\|P\psi\|^2.
$$

**证明。**

第一式为迹的实线性，第二式利用 $P=P^\dagger=P^2$。

□

连续性在已给的矩阵范数结构内成为结论；它不反过来证明物理时空连续。
若只使用二进有理系数，可把共同整数尺度换成 $2^k$，同样从二分、有界性与稠密完备化得到此定理。

### 4.1　二元归一、酉不变及无信号仍不足

令 $\tau(E)=\operatorname{Tr}(E)/d$，定义

$$
p(E)=f(\tau(E)),\qquad
f(t)=\frac{t^2}{t^2+(1-t)^2}.
$$

它是单一非负效果函数，满足 $p(0)=0,p(I)=1$、$p(E)+p(I-E)=1$，并在酉共轭下不变。
但 $p(I/3)=1/5$，三标签菜单的总和为 $3/5$。
所以二元互补归一不能替代跨粗细菜单的正细化相容。
若两个内部读出取联合分布 $P(a,b\mid E,F)=r_E(a)r_F(b)$，
其中 $r_E(1)=p(E),r_E(0)=1-p(E)$，则双向无信号仍成立，却保留此非 Born 单边赋值。

仅用 qubit 投影的条件也较弱；项目无序相容原子命题 6.5 已给连续投影赋值
$(1+n_z^3)/2$ 的局部三轴可拟合反例。
本定理使用的是包含非锐效果的正细化域，实际取得这些菜单是额外结构。[[unordered](#bib-unordered)，[busch](#bib-busch)]

## 5　数学延拓怎样成为实际新读数

### 5.1　范数稠密并不等于直接上下序稠密

$D$ 在效果域中范数稠密：对 $E\in[0,I]$，先取有理 $0<\delta<1/2$ 并置
$E_\delta=(1-2\delta)E+\delta I$，再用有理自伴矩阵以小于 $\delta/2$ 的误差逼近它。
近似矩阵仍在 $[0,I]$，且到 $E$ 的距离小于 $3\delta/2$。

然而，不能声称每个边界效果都有 $D$ 内的任意精细上下序夹逼。
例如实二维投影

$$
P=\frac13\begin{pmatrix}1&\sqrt2\\\sqrt2&2\end{pmatrix}
$$

满足：有理 $0\preceq F\preceq P$ 只能是零，有理 $P\preceq G\preceq I$ 只能是 $I$。
证明如下：$F\preceq P$ 使 $F$ 的像包含于 $P$ 的一维像，故 $F=tP$；
同时要求 $t/3$ 与 $t\sqrt2/3$ 有理，迫使 $t=0$。
对 $I-G\preceq I-P$ 同理。因此朴素序夹逼的宽度始终为一。

<a id="thm:buffer"></a>

#### 定理 5.1（半尺度与单位缓冲的实际读出桥）

> **转写者校注（实际读数的定义域）。** 定义 4.1 中的 $p$ 只定义在 $D$ 上。本定理写出的 $p(E/2)$、$p((E+r_nI)/2)$ 指同一实际切口上另外供应的读数；可统一记为 $\widetilde p$，其声明域包含 $D$ 及本定理所用的额外效果，且 $\widetilde p|_D=p$。两个正比较要求这些实际读数满足相应顺序，不能用尚待识别的数学延拓 $\bar p$ 代替实际前件。下文有限误差命题的 $a,b$ 表示对应的辅助实际读数。


设 $\rho$ 为定理 [4.3](#thm:born) 得到的矩阵，$E$ 为额外实际效果，读数为 $x$。
选 $F_n\in D$ 与有理 $r_n\in(0,1]$，满足 $\|F_n-E\|\le r_n\to0$。
假定同一实际切口还供应

$$
p(E/2)=x/2,\qquad
p((E+r_nI)/2)=(x+r_n)/2,
$$

以及下面两项正比较的读数顺序：

$$
E/2\preceq(F_n+r_nI)/2,
\qquad
F_n/2\preceq(E+r_nI)/2.
$$

则 $x=\operatorname{Tr}(\rho E)$。

**证明。**

四个算子都是效果；两个序关系由 $\|F_n-E\|\le r_n$ 得到。
$D$ 内已知有理线性，故序比较给

$$
x\le p(F_n)+r_n,\qquad p(F_n)\le x+r_n.
$$

所以 $|x-p(F_n)|\le r_n$。
又有 $|p(F_n)-\operatorname{Tr}(\rho E)|\le\|F_n-E\|\le r_n$，
故 $|x-\operatorname{Tr}(\rho E)|\le2r_n\to0$。

□

该桥在 $E=0,I$ 等边界仍成立。
半尺度、单位混合与正比较可以由扩大实际域上的二、三菜单合同供应；
它们不是仅凭 $E$ 的矩阵存在就已取得。
特别地，可数域上的唯一数学延拓不能自动命名为未标定菜单的实际概率。

<a id="prop:buffer-error"></a>

#### 命题 5.2（缓冲桥的有限误差）

固定效果 $E$、$F\in D$ 及 $r\in\mathbb{Q}\cap(0,1]$，使 $\|F-E\|\le r$。
令辅助实际读数为 $a,b$，各误差参数非负，并满足

$$
|a-x/2|\le\epsilon_s,\qquad
|b-(x+r)/2|\le\epsilon_m,
$$

$$
a\le p((F+rI)/2)+\epsilon_+,
\qquad p(F/2)\le b+\epsilon_-.
$$

则

$$
\boxed{|x-\operatorname{Tr}(\rho E)|\le2r+\eta,\quad
\eta=2\max\{\epsilon_s+\epsilon_+,\epsilon_m+\epsilon_-\}.}
$$

若四个缺陷均不超过 $\epsilon$，右侧可取 $2r+4\epsilon$。

**证明。**

第一组比较给 $x\le p(F)+r+2(\epsilon_s+\epsilon_+)$；
第二组给 $p(F)\le x+r+2(\epsilon_m+\epsilon_-)$。
再加 $|p(F)-\operatorname{Tr}(\rho E)|\le r$。

□

### 5.2　共同满测切口

若同一来源的记录参数为 $\xi$，每个 $p_\xi(E)$ 可测，而每条二、三菜单关系分别几乎处处成立，
则因 $D$ 及所需菜单族可数，可去掉一个共同零测集，在余下每个切口同时应用定理 [4.3](#thm:born)。
所得 $\rho_\xi$ 可测，无需额外可测选择：选有限有理效果基，矩阵元就是有限个读数的线性组合。
复版本中例如令

$$
P_i=e_ie_i^\dagger,\quad
F_{ij}=\tfrac12(e_i+e_j)(e_i+e_j)^\dagger,\quad
G_{ij}=\tfrac12(e_i+ie_j)(e_i+ie_j)^\dagger,
$$

则

$$
\begin{aligned}
\rho_{ii}&=p(P_i),\\
\Re\rho_{ij}&=p(F_{ij})-\tfrac12[p(P_i)+p(P_j)],\\
\Im\rho_{ij}&=\tfrac12[p(P_i)+p(P_j)]-p(G_{ij}).
\end{aligned}
$$

**作者注（指标域与实际读数记号）。** 为使本节的矩阵元索引与定义 [4.1](#def:menus) 的 $D=V_0\cap[0,I]$ 一致，以上公式按 $P_i=e_ie_i^\dagger$ 处理对角元，并仅对 $i\ne j$（可固定 $i<j$ 以避免重复）使用 $F_{ij}$ 与 $G_{ij}$；不把形式上的 $F_{ii}=2P_i$ 当作 $D$ 中的效果。这里的 $p_\xi$ 在 $D$ 上仍指同一切口的可数有理读数。若本节还读取这些公式之外的实际效果，作者将其记为另行供应的同一来源、同一切口读数 $\tilde p_\xi$，并要求 $\tilde p_\xi|_D=p_\xi$；它是实际缓冲/读出合同的一部分，不是由可数域上的数学延拓自动推出。

这些效果具有有理实虚部。
全部实系数关系随后由线性性统一推出，无需相交不可数个满测集。
新增实际目标若有限或可数，可把它们的缓冲桥并入共同合同；不自动扩大到所有未声明的不可数菜单。

## 6　递归细化与实际粗事件的误差预算

### 6.1　平方选择以前也能提出细化误差

#### 命题 6.1（同一补事件的二、三菜单差）

设 $E,F\succeq0$、$E+F\preceq I$，$G=I-E-F$。
若同一切口上两菜单的归一缺陷满足

$$
|p(E+F)+p(G)-1|\le\epsilon_2,\qquad
|p(E)+p(F)+p(G)-1|\le\epsilon_3,
$$

则

$$
|p(E+F)-p(E)-p(F)|\le\epsilon_2+\epsilon_3.
$$

**证明。**

两式相减并用三角不等式。同一 $G$ 的读数身份是消去补项的关键。

□

<a id="thm:tree"></a>

#### 定理 6.2（有限递归树的细化预算）

给有限二叉细化树，每个内部节点满足 $E_v=E_{v0}+E_{v1}$。
假定所有节点读数在同一来源、同一切口的声明域内，且

$$
|p(E_v)-p(E_{v0})-p(E_{v1})|\le\eta_v.
$$

则

$$
\boxed{\left|p(E_{\rm root})-\sum_{u\text{ 为叶}}p(E_u)\right|
\le\sum_{v\text{ 为内部节点}}\eta_v.}
$$

**证明。**

把全部内部节点的带符号缺陷相加，每个非根内部节点的读数恰好正负各出现一次。
剩下根读数减所有叶读数，再用三角不等式。

□

若有 $L$ 个叶且每节点缺陷不超过 $\eta$，上界是 $(L-1)\eta$。
深度 $n$ 的完整二叉树上界是 $(2^n-1)\eta$。
因此逐步误差各自很小并不推出无限递归稳定；若第 $j$ 层每节点预算为 $\eta_j$，
则 $\sum_{j\ge0}2^j\eta_j<\infty$ 是得到统一有限总预算的一个充分条件。
若要总漂移趋零，还须更强的预算控制或有证明的收缩机制。
这里没有先把读数假定为 Born 权重，也没有用无限极限替代有限记录合同。

### 6.2　记录级的守恒比矩阵块对角更具体

#### 定义 6.3（实际粗事件与不跨类记录更新）

在同一个实际记录空间 $\Xi$ 上给可测分类 $c:\Xi\to\{0,1\}$、固定来源分布 $\nu$，
以及实际记录更新的 Markov 核 $K$。令 $C=\{\xi:c(\xi)=1\}$。
称 $K$ 不跨粗类，若

$$
K(\xi,\{\xi':c(\xi')=c(\xi)\})=1
\quad\text{对 }\nu\text{-几乎处处 }\xi.
$$

<a id="prop:record"></a>

#### 命题 6.4（记录粗类守恒及泄漏界）

不跨粗类时 $\nu K(C)=\nu(C)$。一般情况下

$$
|\nu K(C)-\nu(C)|\le
\int K(\xi,\{\xi':c(\xi')\ne c(\xi)\})\,d\nu(\xi).
$$

**证明。**

当 $c(\xi)=0$ 时，$|K(\xi,C)-1_C(\xi)|=K(\xi,C)$；
当 $c(\xi)=1$ 时，它等于 $1-K(\xi,C)$。
两者恰是跨类概率，对 $\nu$ 积分即得结论。

□

这是 Born 之前的报告层守恒条件。项目 V49 定义 9.1 明确要求不跨块、单点保持，
其定理 9.5 用旁观单点概率守恒选择指数二；本式把不跨类前件与有限泄漏容差直接写出。[[v49](#bib-v49)]
仅说某个振幅矩阵在指定子空间上块对角，并没有给出实际报告的核支撑条件；
要用矩阵结构解释这个核，还须提供振幅读出到实际记录的桥。
该区别也解释了为何“所有门已归一”并不直接证明任意归一化报告规则均为平方。

## 7　纯性、共同虚单位与允许的门

### 7.1　纯性相对于读出代数而言

<a id="prop:twirl"></a>

#### 命题 7.1（相容效果的实表示与复表示）

令 $J$ 为正交复结构，$R\succeq0$、$\operatorname{Tr}_{\mathbb{R}}R=1$ 为实密度矩阵。
定义数学投影

$$
R_J=\frac12(R+JRJ^{\mathsf T}).
$$

则 $R_J$ 为实密度矩阵、与 $J$ 对易；对任意实对称且与 $J$ 对易的效果 $E$，有

$$
\operatorname{Tr}_{\mathbb{R}}(RE)=\operatorname{Tr}_{\mathbb{R}}(R_JE).
$$

在 $J$ 适配坐标中写 $R_J=\mathcal R(A)$，其中 $\mathcal R$ 是复矩阵的实化，
则 $\rho_{\mathbb{C}}=2A$ 是复密度矩阵。对任意复 Hermitian 效果 $B$，有

$$
\operatorname{Tr}_{\mathbb{R}}\bigl(R_J\mathcal R(B)\bigr)=\operatorname{Tr}_{\mathbb{C}}(\rho_{\mathbb{C}}B),
\qquad
\operatorname{rank}_{\mathbb{R}}R_J=2\operatorname{rank}_{\mathbb{C}}\rho_{\mathbb{C}}.
$$

**证明。**

$R$ 与 $JRJ^{\mathsf T}$ 均正、实迹一；用 $J^2=-I$ 验证平均与 $J$ 对易。
$J^{\mathsf T}EJ=E$ 及迹循环性给读数等式。
对易于 $J$ 的实对称矩阵恰是复 Hermitian 矩阵的实化。
实化满足 $\operatorname{Tr}_{\mathbb{R}}\mathcal R(A)=2\Re\operatorname{Tr}_{\mathbb{C}}A$，故 $\operatorname{Tr}_{\mathbb{C}}A=1/2$。
乘积的实迹亦给显示的响应式。每个复本征向量贡献两个实方向，给秩关系。

□

特别地，若 $R=xx^{\mathsf T}$，$\|x\|=1$，则 $x\perp Jx$ 且

$$
R_J=\frac12\bigl(xx^{\mathsf T}+(Jx)(Jx)^{\mathsf T}\bigr)
$$

的实秩为二，对应复秩一纯态。
因此“秩降低”与“没有丢失可读信息”须指定标量域及效果代数。
这里的平均是证明相容读数等价的数学操作，不自动是一项免费物理通道，也不删除完整观察者中的记录。[[v53](#bib-v53)]

还要区分：三轴生成代数是 $M_2(\mathbb{C})\otimes I_m$，而全体与 $J$ 对易的算子代数可能是 $M_{2m}(\mathbb{C})$。
对前者的完整读出只能确定 qubit 接口态，不能独自确定多重度空间的全部关系。
本文上面的表示命题对任何已声明相容效果成立；没有假定全部相容效果都已实际取得。

### 7.2　方向相容才把实正交门变成复酉门

<a id="thm:gate"></a>

#### 定理 7.2（定向门的复线性）

给精确三轴 $A_i$ 与 $J=A_1A_2A_3$。
设实正交变换 $T$ 保持三轴线性张成空间，并满足同一方向作用

$$
T A(n)T^{-1}=A(Qn),\qquad n\in\mathbb{R}^3.
$$

则 $Q\in O(3)$，且

$$
TJT^{-1}=(\det Q)J.
$$

当 $\det Q=1$ 时，$T$ 关于 $J$ 为复酉变换；当 $\det Q=-1$ 时为复反酉变换。

**证明。**

$A$ 由 $A(n)^2=\|n\|^2I$ 可知为单射，共轭线性性使所诱导的 $Q$ 为线性映射。
$A(n)^2=\|n\|^2I$ 给 $\|Qn\|^2=\|n\|^2$，故 $Q$ 正交。
在三个正交列向量上展开 Clifford 乘积，收缩项因列正交而消失，三阶交错项为 $(\det Q)A_1A_2A_3$。
所以 $TJ=JT$ 或 $TJ=-JT$。
前者与实等距性合并给 $h(Tu,Tv)=h(u,v)$；
后者给 $h(Tu,Tv)=\overline{h(u,v)}$，分别为酉与反酉。

□

该定向结论是 V53 已有结构在本轮前件下的应用。[[v53](#bib-v53)]
任意实正交门未必保持这个三轴张成空间，也未必保持取得的 $J$；
增长门序列的表达本身不提供这些相容条件。
如果实际门逐一满足定向相容，则其全部有限前缀均复酉，因而共同 $J$ 沿序列传导。
这时“酉性”可以由实等距加共同复结构相容表达，而非只用每个向量单独归一来代替。

## 8　复合接口的共同相位：闭路与缺陷

项目 V53 已给两因子的对齐扇区和多因子递归对齐。[[v53](#bib-v53)]
下面把它写成可带正反方向标记的有限图，并为同一个固定来源给误差界。
所有因子都属于完整观察者内部；张量分解本身仍是给定的关系接口。

#### 定义 8.1（内部相位约束图）

给有限连通简单图 $G$，其 $n$ 个顶点对应实内积空间 $V_i$，
$\dim_{\mathbb{R}}V_i=2d_i>0$，各有正交复结构 $J_i$。
在 $V=\bigotimes_{i=1}^n{}_{\mathbb{R}} V_i$ 上把 $J_i$ 视为作用于第 $i$ 因子的算子。
每条无向边 $(i,j)$ 给符号 $\eta_{ij}\in\{1,-1\}$，定义

$$
P_{ij}=\frac{I-\eta_{ij}J_iJ_j}{2},\qquad
P_G=\prod_{(i,j)\in E(G)}P_{ij}.
$$

不同因子的 $J_i$ 对易，$J_iJ_j$ 是对称对合，故所有 $P_{ij}$ 是互相对易的正交投影。
在 $P_{ij}$ 的像上，$J_j=\eta_{ij}J_i$。
以下闭路指简单闭路；一般闭步的符号条件可由简单闭路分解得到。

<a id="thm:phase"></a>

#### 定理 8.2（共同复结构的闭路充要条件）

$\operatorname{Ran} P_G\ne\{0\}$ 当且仅当每条闭路的边符号乘积为 $+1$。
条件成立时存在顶点符号 $s_i\in\{\pm1\}$，使 $\eta_{ij}=s_is_j$，且

$$
\boxed{\operatorname{rank}_{\mathbb{R}}P_G=2\prod_{i=1}^n d_i.}
$$

在该扇区，$J_i'=s_iJ_i$ 全部相同，定义一个共同复结构；扇区复维数为 $\prod_i d_i$。

**证明。**

在共同扇区上，每条边有 $J_iJ_j=-\eta_{ij}I$。
对长度 $\ell$ 的闭路相乘，每个顶点的 $J_i$ 恰出现两次，左边为 $(-1)^\ell I$；
右边为 $(-1)^\ell$ 乘该闭路的符号积。非零向量的存在迫使符号积为一。

反之，选一棵生成树和根，令根符号为一，沿树令 $s_j=\eta_{ij}s_i$。
闭路条件使任意额外边也有 $\eta_{ij}=s_is_j$。
换成 $J_i'=s_iJ_i$ 后全部边成为同向约束。
树边相等关系已蕴含所有额外边关系，所以 $P_G$ 等于树边投影的乘积。

展开树的 $n-1$ 个投影。除常数项外，每项对应一个非空树边子集；
其形成的森林必有度数一顶点，所以该项的张量迹包含一个单独 $J_i'$ 的迹，而该迹为零。
只剩常数项，故

$$
\operatorname{Tr}_{\mathbb{R}}P_G=2^{-(n-1)}\dim_{\mathbb{R}}V
=2\prod_i d_i>0.
$$

在共同扇区上 $J_i'$ 相等、平方为 $-I$，给余下结论。

□

此处的负闭路是这项离散相位约束的精确不相容，不直接等同于任意物理曲率、规范场或手性破缺。
单一全局本体也不自动选定各条边的实际符号及其闭路相容。

<a id="thm:phaseerror"></a>

#### 定理 8.3（固定来源的共同扇区误差预算）

给同一个归一向量 $\Psi\in V$，并令

$$
\epsilon_e=\|(I-P_e)\Psi\|^2,\qquad
\epsilon=\sum_{e\in E(G)}\epsilon_e.
$$

则 $p=\|P_G\Psi\|^2\ge1-\epsilon$。
若 $\epsilon<1$，则相位图必满足定理 [8.2](#thm:phase)，且

$$
\Psi_G=\frac{P_G\Psi}{\sqrt p},\qquad
\frac12\bigl\|\Psi\Psi^{\mathsf T}-\Psi_G\Psi_G^{\mathsf T}\bigr\|_1
=\sqrt{1-p}\le\sqrt\epsilon.
$$

因此对任意实效果 $0\preceq E\preceq I$，两态二次读数的差不超过 $\sqrt\epsilon$。
若存在负符号闭路，其上必有 $\sum_{e\text{ 在闭路}}\epsilon_e\ge1$。

**证明。**

对易投影可同时对角化，逐个共同本征向量有

$$
I-\prod_eP_e\preceq\sum_e(I-P_e).
$$

取 $\Psi$ 的二次型给 $1-p\le\epsilon$。
若 $p>0$，共同扇区非零，闭路条件随之成立。
当 $p=1$ 时距离为零；否则把 $\Psi$ 分解为
$\sqrt p\,\Psi_G+\sqrt{1-p}\,\chi$，其中 $\chi\perp\Psi_G$、$\|\chi\|=1$。
两秩一矩阵之差在此二维张成空间的矩阵为

$$
\begin{pmatrix}
-(1-p)&\sqrt{p(1-p)}\\
\sqrt{p(1-p)}&1-p
\end{pmatrix},
$$

本征值为 $\pm\sqrt{1-p}$，给迹距离式。
迹零自伴矩阵 $\Delta$ 对效果的响应绝对值至多其正部迹 $\|\Delta\|_1/2$，所以得到读数界。
负闭路的全部边投影乘积为零；只对该闭路使用第一项算子不等式，给预算下界一。

□

此处使用已给的二次几何；把 $p$ 解释为实际成功概率，还须对应的效果读出与记录桥。
条件归一向量 $\Psi_G$ 不是完整本体的新定义。
若实际供应一个内部记录接口，取两个正交单位记录态 $|s\rangle,|f\rangle$，其理想记录映射为

$$
\mathcal V\Psi=P_G\Psi\otimes|s\rangle+(I-P_G)\Psi\otimes|f\rangle,
$$

则 $\mathcal V^{\mathsf T}\mathcal V=I$，所以它是等距嵌入；成功和失败质量分别为 $p$、$1-p$。
$P_G$ 与 $J_1$ 对易；输出取复结构 $J_1\otimes I_{\rm record}$，则 $\mathcal V$ 还为复线性等距。
因此在适当内部准备子空间上可作相容的酉扩张，但准备、控制及记录的实际取得仍须供应。
完整观察者保留两个分支，不能把丢弃失败分支后的条件归一称为一个无条件酉门。

## 9　可替换的公理组及仍未完成的物理桥

<a id="thm:main"></a>

#### 定理 9.1（有限接口的条件复量子重构）

在唯一实际来源 $\Omega$ 的指定内部接口上，假定下列结构已给出或另有有效取得定理：

1. 有限实正内积载体、同一方向线性三轴、忠实正二次校准，且六方向缺陷为零；
1. 三轴所生成矩阵接口中的可数有理效果，在同一实际切口具有单一非负读数，
并满足全部声明的二、三结果菜单归一；
1. 对同一声明效果代数内要加入的额外实际效果，供应定理 [5.1](#thm:buffer) 的半尺度、单位缓冲和正比较；
1. 所声明实际可逆门为实等距，并相容地保持三轴方向与定向；
1. 若涉及复合接口，则供应内部实张量分解、实际相位边以及闭路一致性。

则第一项给一个共同复结构 $J$ 与 Pauli 三轴读出代数；
第二项给该接口唯一 Born 密度表示，纯态情形给平方投影概率；
第三项把此表示延伸到声明的实际新菜单；
第四项使全部允许有限门前缀成为复酉序列；
第五项给维数正确的共同复相位扇区。
有限缺陷分别受定理 [3.2](#thm:stable-six)、命题 [5.2](#prop:buffer-error)、
定理 [6.2](#thm:tree) 及 [8.3](#thm:phaseerror) 中的预算控制。

**证明。**

依次应用定理 [2.3](#thm:six) 及其 Pauli 表示、定理 [4.3](#thm:born)、
定理 [5.1](#thm:buffer)、定理 [7.2](#thm:gate) 和定理 [8.2](#thm:phase)。
各项在同一声明接口与来源合同内衔接；没有从一个接口的结论跨类型搬到另一个尚未取得的接口。

□

这些误差界分别控制各自声明的对象；它们没有把修复三轴的新效果域自动认作原来的实际菜单，
也没有证明全部菜单近似满足合同时必有统一近邻 Born 赋值。若要合并成一个全流程稳定性定理，
还须给接口转移误差及实际实现误差的共同预算。

### 9.1　每一个结论究竟用了什么

| 所解释结构 | 足够的关系前件 | 尚不能省略的内容 |
| --- | --- | --- |
| 共同虚单位 | 三轴反对易及正平方；六方向忠实认证 | 实正几何、方向线性、忠实二次标定 |
| 概率平方 | 同一正效果在二、三菜单中细化一致 | 效果正序、实际菜单、同源读数身份 |
| 全实关系一致 | 可数有理加性、正性、有界完备化 | 既定矩阵拓扑；实际新菜单另有桥 |
| 复酉门 | 实等距、共同 $J$、定向协变 | 实际门取得；不能只给单点归一 |
| 复合相位 | 内部因子、对齐边、所有闭路正积 | 因子接口及共同扇区取得 |
| 递归稳定 | 节点缺陷预算与相位边预算 | 可求和或收缩条件、实际读出容差 |

这是一组足够条件，没有证明其逻辑独立性或最小性。
相较于直接写“复 Hilbert 空间加 Born 规则”，它把共同虚单位分解为可检验的三轴算子关系，
把概率赋值分解为正细化的一致性。其几何前件仍然很强：实内积已含二次结构，
正效果域已含矩阵序；本文没有用换一种说法把这些输入隐藏掉。

### 9.2　与 AURIC 五模式和本体图景的准确接口

三轴 Pauli 自伴元、共同中心 $J$、单位元 $I$ 与归一化正泛函构成一个明确的数学接口。
但它们不能不经证明就分别重命名为项目原生 $F[1],F[3],F[2],F[13],F[\mathrm{null}]$。
要作这个对应，至少要给原生对象的线性载体、乘法、伴随、正序、实际读出及保持这些结构的映射。
特别地，本定理的完整实载体维数是 $4m$；五个原生模式作为五个标签或五个状态，
不自动就是一个五维的忠实三轴 Clifford 载体。
关系变量也不能仅因在图上与三轴同现，就被等同于中心虚单位或概率归一化。

在这些类型桥取得后，可以保留用户的本体表达：完整观察者包括所有参考和环境，
其酉序列始终作用于唯一固定 $\Omega$。
本文的约化矩阵只表示已声明效果域可读出的关系；
自我稳定读出、环境变化读出、内部预测与记录都可以属于同一完整序列，
但其具体分割、稳定性和动力学仍需要对应模型与定理。

### 9.3　量子起源还剩哪些实质问题

仍须解释或取得：为何实际接口有上述实正内积与正效果几何；为何足够多的菜单能从一个实际来源取得；
为何局部校准忠实；为何实际可逆门保存取得的共同 $J$；以及为何实际复合关系满足相位闭路相容。
这几项都不是“唯一本体”一句话的逻辑推论。

本文也没有从三轴证明物理空间只能三维，没有推出任意多体接口均不可约，
没有只凭局部 Born 读数推出全部实际仪器、完全正性或任意参考扩张，
也没有推出引力、质量、解码时钟速度或具体 Hamiltonian。
先前参考与通道重构中的来源及扩张前件继续保留。

本轮能够精确支持的量子起源命题是：
> 在一个实际取得的正线性关系接口内，方向线性三轴的六方向忠实锐性校准能够内生定义共同虚单位；
> 可数有理效果域中全部声明二、三结果菜单的正细化一致性能够唯一固定 Born 读出，纯态时给平方投影概率；
> 定向相容门与闭路相容复合使这两种关系沿观察者内部序列传导。

这把复数、平方、归一和递归放进同一组可核查的数学条件，同时明确了要从条件重构走向物理起源仍须完成的来源工作。

## 固定来源与文献

<a id="bib-head"></a>

**[head]**
The Omega Institute, *trureturing*, 固定提交：
[<code>b9087e51948fa40e<wbr>487ce8039c2b126d<wbr>0dff7a66</code>](https://github.com/the-omega-institute/trureturing/commit/b9087e51948fa40e487ce8039c2b126d0dff7a66)。
本轮一次活动 HEAD 取得完成于 2026-11-01 03:53:48.698036（Asia/Singapore）。
本地固定来源审计记录保留比较、树、字节身份及实际阅读范围。

<a id="bib-cdso"></a>

**[cdso]**
The Omega Institute, [CDSO Periodic Connection Cost](https://github.com/the-omega-institute/trureturing/blob/b9087e51948fa40e487ce8039c2b126d0dff7a66/docs/develop/theory/CDSO_PERIODIC_CONNECTION_COST.md)，
上述固定提交，新增 §§17–19。来源审计实际连续覆盖全部 502 行增量；未借其推出量子结论。

<a id="bib-kbonacci"></a>

**[kbonacci]**
The Omega Institute,
[K-bonacci Endpoint Tomography and Rank-One Relation Boundaries](https://github.com/the-omega-institute/trureturing/blob/b9087e51948fa40e487ce8039c2b126d0dff7a66/docs/develop/theory/KBONACCI_ENDPOINT_TOMOGRAPHY_AND_RANK_ONE_RELATION_BOUNDARIES.md)，
上述固定提交，新增 §11，定义 11.1、定理 11.2 及其证明与边界。

<a id="bib-v53"></a>

**[v53]**
The Omega Institute,
[AURIC V53: Sharp Three-Axis Readouts, Endogenous Complex Structure and Common-Phase Compatibility](https://github.com/the-omega-institute/trureturing/blob/b9087e51948fa40e487ce8039c2b126d0dff7a66/docs/develop/theory/AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md)，
上述固定提交，§§3–4、6–8：实复表示、Clifford 三轴、定向门及相位对齐。

<a id="bib-unordered"></a>

**[unordered]**
The Omega Institute,
[AURIC Unordered Compatible Atom and Quantum Representation Theory](https://github.com/the-omega-institute/trureturing/blob/b9087e51948fa40e487ce8039c2b126d0dff7a66/docs/develop/theory/AURIC_UNORDERED_COMPATIBLE_ATOM_AND_QUANTUM_REPRESENTATION_THEORY.md)，
上述固定提交，§6：全效果正可加赋值、Born 表示及投影菜单反例。

<a id="bib-v49"></a>

**[v49]**
The Omega Institute,
[AURIC V49: Sum, Product, Powers, Quadratic Relation Closure and Normalized Lifting](https://github.com/the-omega-institute/trureturing/blob/b9087e51948fa40e487ce8039c2b126d0dff7a66/docs/develop/theory/AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md)，
上述固定提交，§9：原生回返、四角赔率相容、旁观单点守恒与条件平方选择。

<a id="bib-busch"></a>

**[busch]**
P. Busch, *Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem*,
Physical Review Letters **91**, 120403 (2003).
[doi:10.1103/PhysRevLett.91.120403](https://doi.org/10.1103/PhysRevLett.91.120403);
[arXiv:quant-ph/9909073](https://arxiv.org/abs/quant-ph/9909073)。
本文使用其效果正可加表示思想；可数入口与实际缓冲读出桥在正文另证。

<a id="bib-clifford"></a>

**[clifford]**
A. Jadczyk, *Notes on Clifford Algebras*, 6 April 2019,
[作者公开讲义](https://www.arkadiusz-jadczyk.eu/docs/clifford.pdf)，§1.3.2.1.6：
正平方约定下 $\mathrm{Cl}_3\simeq M_2(\mathbb{C})$、Pauli 生成元及体积元。

**作者原稿结束。**

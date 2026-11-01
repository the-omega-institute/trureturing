> 编者说明（文献归属）：以下 TeX 编译、字体、PDF 元数据与版式设置，以及“未运行数学程序”等执行陈述，均为所供作者原稿的文献内容；本 Markdown 转换不声称执行过 XeLaTeX 或生成过作者 PDF。

<div>
<code>% !TeX program = xel<wbr>atex<br>
% Compile twice with<wbr> XeLaTeX. Optional f<wbr>ont directory: \def\<wbr>AURICFontPath{/absol<wbr>ute/path/}<br>
% Paper mathematics <wbr>only; no mathematica<wbr>l program, CAS, nume<wbr>rical test or enumer<wbr>ation was run.<br>
\documentclass[11pt,<wbr>a4paper]{article}<br>
\usepackage[margin=2<wbr>3mm,headheight=16pt]<wbr>{geometry}<br>
\usepackage{fontspec<wbr>}<br>
\ifdefined\AURICFont<wbr>Path<br>
 \setmainfont[Path=\<wbr>AURICFontPath,BoldFo<wbr>nt=NotoSerifCJKsc-Bo<wbr>ld.otf,<br>
 ItalicFont=NotoSeri<wbr>fCJKsc-Regular.otf,B<wbr>oldItalicFont=NotoSe<wbr>rifCJKsc-Bold.otf]{N<wbr>otoSerifCJKsc-Regula<wbr>r.otf}<br>
\else<br>
 \IfFontExistsTF{Not<wbr>o Serif CJK SC}{<br>
 \setmainfont[Italic<wbr>Font=Noto Serif CJK <wbr>SC,BoldItalicFont=No<wbr>to Serif CJK SC Bold<wbr>]{Noto Serif CJK SC}<br>
 }{\setmainfont[Bold<wbr>Font=FandolSong-Bold<wbr>.otf,ItalicFont=Fand<wbr>olSong-Regular.otf,<br>
 BoldItalicFont=Fand<wbr>olSong-Bold.otf]{Fan<wbr>dolSong-Regular.otf}<wbr>}<br>
\fi<br>
\setmonofont{Latin M<wbr>odern Mono}<br>
\XeTeXlinebreaklocal<wbr>e &quot;zh&quot;<br>
\XeTeXlinebreakskip=<wbr>0pt plus 1pt<br>
\usepackage{amsmath,<wbr>amssymb,amsthm,matht<wbr>ools,bm}<br>
\usepackage{booktabs<wbr>,array,tabularx,enum<wbr>item,fancyhdr,xcolor<wbr>,needspace}<br>
\definecolor{auricbl<wbr>ue}{RGB}{24,53,79}<br>
\usepackage[unicode,<wbr>colorlinks=true,link<wbr>color=auricblue,urlc<wbr>olor=auricblue,citec<wbr>olor=auricblue]{hype<wbr>rref}<br>
\hypersetup{pdftitle<wbr>={AURIC v63：原生复结构的稳定<wbr>装配与有限 Born 读出证书},<br>
pdfauthor={AURIC res<wbr>earch continuation},<br>
pdfsubject={Native r<wbr>eal-fiber phase asse<wbr>mbly, approximate in<wbr>teger commutation, s<wbr>hared-anchor records<wbr>, finite Born certif<wbr>icates, and composed<wbr> error bounds}}<br>
\newcommand{\R}{\mat<wbr>hbb R}<br>
\newcommand{\C}{\mat<wbr>hbb C}<br>
\newcommand{\Q}{\mat<wbr>hbb Q}<br>
\newcommand{\Tr}{\op<wbr>eratorname{Tr}}<br>
\newcommand{\rank}{\<wbr>operatorname{rank}}<br>
\newcommand{\Herm}{\<wbr>operatorname{Herm}}<br>
\newcommand{\Ran}{\o<wbr>peratorname{Ran}}<br>
\newcommand{\op}{\ma<wbr>thrm{op}}<br>
\newcommand{\calJ}{\<wbr>mathcal J}<br>
\newcommand{\repo}[2<wbr>]{\href{https://gith<wbr>ub.com/the-omega-ins<wbr>titute/trureturing/b<wbr>lob/a42f32e9a2a54ec0<wbr>b01748c96a6af312f941<wbr>c853/docs/develop/th<wbr>eory/#1}{#2}}<br>
\theoremstyle{defini<wbr>tion}<br>
\newtheorem{definiti<wbr>on}{定义}[section]<br>
\newtheorem{theorem}<wbr>[definition]{定理}<br>
\newtheorem{proposit<wbr>ion}[definition]{命题}<br>
\newtheorem{corollar<wbr>y}[definition]{推论}<br>
\newtheorem{lemma}[d<wbr>efinition]{引理}<br>
\newtheorem{remark}[<wbr>definition]{说明}<br>
\renewcommand{\proof<wbr>name}{证明}<br>
\renewcommand{\abstr<wbr>actname}{摘要}<br>
\renewcommand{\refna<wbr>me}{固定来源与文献}<br>
\setlength{\parinden<wbr>t}{1.8em}<br>
\setlength{\parskip}<wbr>{2pt}<br>
\setlength{\emergenc<wbr>ystretch}{3em}<br>
\setlist{nosep,leftm<wbr>argin=2em}<br>
\pagestyle{fancy}\fa<wbr>ncyhf{}<br>
\fancyhead[L]{\small<wbr> AURIC：原生相位装配与有限读出证书<wbr>}<br>
\fancyhead[R]{\small<wbr> v63 / 2026-11-01}<br>
\fancyfoot[C]{\thepa<wbr>ge}<br>
\allowdisplaybreaks[<wbr>2]<br>
<br>
\begin{document}</code>
</div>

# 原生复结构的稳定装配

# 与有限 Born 读出证书

共同虚单位、局部三轴、共享锚与有限门序列误差

AURIC 量子起源研究　定义、定理与纸面证明　v63.0

2026 年 11 月 1 日　Asia/Singapore

> 作者原稿标题版式：居中；主标题两行 `\LARGE\bfseries\color{auricblue}`，间隔 `6pt`、`8pt`；副标题 `\large`，其后 `6pt`；版本行后 `4pt`。
## 摘要

本轮项目 Quantum IV 新 §§209--213 已在原 89/610 配置上，用实二维纤维、局部响应、正质量守恒、根钟标定及原整数远距交换，取得配置相容共同复结构和原规范标架。
本文据此更新 v62 的来源定位，并给精确守恒条件下的稳定扩展：整数交换误差控制合法方块运输差，升序添加标架控制全部边，进而控制原投影脉冲和任意已允许有限门字。
全 89 复维来源具有共同虚单位，却不容全空间 Pauli 三轴；三轴严格存在于两配置角落，其单位是角落投影。
在记录层，共享锚的局部正性与闭合残差给近邻低秩正核，并以有限张成锚控制算子缺陷。
在读出层，有限效果基、有限方向正性覆盖及实际正细化证书给显式近似 Born 表示；最后把该误差与门字误差合并。
有限低阶正性和有限菜单均有反例边界。全部构造位于唯一固定本体的内部接口；实际准备、相干比较、效果菜单、共同切口、守恒及报告对应仍须供应。
所得是具有明确取得条件与误差预算的有限接口重构，不是全部量子公理的无条件起源证明。

<a id="section-1"></a>

## 1. 本轮真实项目增量与研究位置

本轮唯一实际活动 HEAD 取得固定提交为

<code>a42f32e9a2a54ec0b017<wbr>48c96a6af312f941c853</code>。

取得完成于新加坡时间 2026-11-01 04:26:30.197298；提交时间为 04:21:07。
相对 v62 的 <code>b9087e51948fa40e487c<wbr>e8039c2b126d0dff7a66</code>，前进 30 个提交、17 个变化路径。
固定 diff 旧侧与 JSON 新路径的初次差异由两处重命名解释；按新侧路径核对后集合一致。
目标 theory 目录仍为 1122 项，祖先及目标列表均未截断。
这是取得时刻的快照，不声称写作结束时仍为活动 HEAD。[1](#ref-head)

> 编者注（作者历史报告）：上述 HEAD、取得／提交时刻、30 个提交、17 个路径、两处重命名、1122 项及未截断等均保留为作者的取得时快照陈述；本转换没有重新追逐活动 HEAD，也未将这些历史取得行为归给转换者。

真正与本题直接相关的增量是 Quantum IV 新 §§209--213，共 384 行。
其全部新增正文和证明已连续核读。
另外两份理论增量涉及 damped sweep 与 token graph，本轮仅定位及阅读开始、结尾的明确范围，未重审全部证明，也不将它们作为量子起源证据。[2](#ref-quantum)

> 编者注（阅读归属）：本段“连续核读 384 行”及 damped sweep／token graph 的阅读范围是作者的原始报告。转换者的固定来源阅读范围另见外部证据；不据此认证全部早期依赖。

### 1.1. 必须更新的 v62 定位

上一轮把“原生记录和控制怎样取得共同复接口”列为下一项来源工作。
新 §210 已在特定原生实局部模型内补上其中的相位装配桥：

$$

\boxed{\begin{gathered}
\text{实二维局部响应}+\text{整个脉冲正质量守恒}+\text{根钟}\\
\Longrightarrow\text{共同 }\mathcal J;\\
\text{原整数远距交换}\Longrightarrow\text{合法方块平坦}
\Longrightarrow\text{原配置根标架}.
\end{gathered}}

$$

本文不再把这条特定来源桥称为完全缺失。
同时，新 §212 明确保留平方最小电流律、报告、档案、守卫及真实失败合同；相位装配并未推导概率指数。[2](#ref-quantum)

V14 §§9--10 已有记录 Gram、有限正核最小实现和条件平方唯一性；
V30 与 $\Omega$ 纤维文稿也已有给定正归一线性泛函的 GNS 重构。
因此，本文新增展开定位于稳定装配、共享锚认证和有限实际读出证书，不把这些成熟表示定理重新计作发现。[4](#ref-v14) [5](#ref-v30) [6](#ref-omega)

### 1.2. 完整本体与接口

全篇始终固定同一个实际 $\Omega$；环境、参考、程序、记录、自我与预测均属于完整观察者。
在取得酉实现的接口上仍可写 $\Psi_k=U_k\cdots U_1\Omega$。
配置直和、局部两配置角落、记录 Gram 及读出密度矩阵，均是内部关系接口。
它们不替代完整观察者，也不把未读关系或失败分支删除。
实际菜单指同一来源中已取得或有有效取得定理的比较合同；数学上写出一个算子不代表已有该操作权限。

<a id="section-2"></a>

## 2. 原生实纤维怎样强制共同虚单位

本节简化记号重述新 §209--210 的关键数学，以便稳定定理有完整前件；原生成器的代码及完整历史消费者仍按源文保持。[2](#ref-quantum)

<a id="def:native"></a>

#### 定义 2.1（原生局部实来源）

取 $m=9$ 或 $13$，令 $E_m$ 为 $\{1,\ldots,m\}$ 中不含相邻元素的合法位集，
分别有 89、610 个配置。保留源文的固定外边界 $10$ 与 $010$。
对每个 $q\in E_m$ 给实二维正内积空间 $(V_q,g_q)$ 及实线性响应 $L_q$。
对合法翻转边 $r\to q$ 给等距同构 $T_{qr}:V_r\to V_q$，满足

$$

T_{rq}=T_{qr}^{-1}=T_{qr}^{\dagger}.

$$

置 $\mathcal V=\bigoplus_q V_q$、$\mathcal L=\bigoplus_qL_q$。
取 $x>0$、$x+x^2=1$、$y=\sqrt x$、$c=xy$、$\alpha=3\pi/5$。
原地址 $j$ 的算子 $B_j$ 在中心位为 $0,1$ 的可翻转二点块上为

$$

B_j=\begin{pmatrix}xI&cT_{q_0q_1}\\cT_{q_1q_0}&x^2I\end{pmatrix}.

$$

阻塞单点及两个边界使用源文同一 $0/1$ 标量：内部为 $b_{j-1}b_{j+1}$，边界为 $b_1,b_m$。
令

$$

A_j=\alpha\mathcal L(I+B_j),\qquad \mathsf K_j=e^{A_j}.

$$

实际根配置为源文唯一 ready $q_*$，并给单位根准备 $u_*\in V_{q_*}$。

这些定义保留实线性、二维容量、正度量、等距边、黄金实系数及指定响应形式。
开始时不识别不同纤维的相位、方向或频率，也不要求边运输平坦。
直接用 $c^2=x^3$ 与 $x+x^2=1$ 可逐块验证 $B_j^\dagger=B_j^2=B_j$。

<a id="def:conservation"></a>

#### 定义 2.2（精确保范数与根钟条件）

要求

$$

\|e^{sA_j}v\|^2=\|v\|^2
\quad(v\in\mathcal V,\ 0\le s\le1),
\qquad
\operatorname{Tr}(L_{q_*}^{\dagger}L_{q_*})=2.

$$

全输入及全部内部时刻是模型条件，不宣称这些输入均可实际制备，也不开放分数调用。

> 编者注（迹的类型）：这里的根钟取二维实纤维上的实迹；后文复矩阵效果与密度矩阵的迹取所声明复载体上的复迹。源文 Quantum IV (209.5) 的实纤维前件保持不变。

<a id="thm:nativeJ"></a>

#### 定理 2.3（原生共同复结构，承接项目 §210）

定义 [2.1](#def:native)--[2.2](#def:conservation) 推出

$$

L_q^\dagger=-L_q,\qquad L_q^2=-I_q,
\qquad L_qT_{qr}=T_{qr}L_r.

$$

因此 $\mathcal J=\bigoplus_qL_q$ 是正交复结构，且与全部 $B_j,A_j$ 对易。
定义 $(a+ib)v=av+b\mathcal J v$ 后，全部内部演化 $e^{sA_j}$ 都为复酉。
这一结论不需要整数远距交换。

**证明。**

保范数式在 $s=0$ 的右导数给 $g(v,A_jv)=0$，极化给 $A_j^\dagger=-A_j$。
其每个对角块是正实系数 $\alpha(1+p_j(q))$ 乘 $L_q$，所以每个 $L_q$ 反自伴。
对二点块的非对角部分，反自伴条件成为

$$

0=\alpha c(L_qT_{qr}-T_{qr}L_r),

$$

故有交织。
在根的任意实正交基中，$L_{q_*}$ 是
$\left(\begin{smallmatrix}0&-\omega\\\omega&0\end{smallmatrix}\right)$；根钟给 $2\omega^2=2$，所以平方为 $-I$。
删除占据位保持合法，原图连通；沿等距交织传播便得到全部 $L_q^2=-I$。
块计算给 $[\mathcal J,B_j]=0$，故 $A_j$ 为复线性实反自伴算子，其指数复酉。

∎

这解释了本来源中共同虚单位的取得位置：局部二维反自伴响应提供负平方方向，根钟固定其尺度，实际等距边传导该方向。
二维容量、正度量和指定响应仍为输入；没有证明它们由本体唯一性单独推出。
把根响应和正向钟同时反转，得到共轭约定，不能据此宣称物理手性已被唯一选择。

<a id="prop:exactflat"></a>

#### 命题 2.4（整数交换取得原规范平坦性，承接项目 §210）

再要求原整数调用 $[\mathsf K_j,\mathsf K_k]=0$ 对 $|j-k|\ge2$ 成立。
则每条合法翻转闭路运输为恒等；存在唯一根定标架 $F_q:V_{q_*}\to V_q$，满足

$$

F_{q_*}=I,\quad T_{qr}=F_qF_r^{-1},\quad L_qF_q=F_qL_{q_*}.

$$

由根基 $u_*,L_{q_*}u_*$ 传导的坐标，将整个实来源变为原复配置来源及整个内部脉冲。

**证明。**

由上一条定理及 $B_j^2=B_j$，有

$$

e^{sA_j}=e^{\alpha s\mathcal J}
\bigl[I+(e^{\alpha s\mathcal J}-I)B_j\bigr].

$$

在翻转边上，$\mathsf K_j$ 的非对角块为 $R_qT_{qr}$，其中

$$

R_q=c\,e^{\alpha L_q}(e^{\alpha L_q}-I),\qquad
R_q^\dagger R_q=4c^2\sin^2(\alpha/2)I.

$$

取合法方块 $s=S,a=S+j,b=S+k,t=S+j+k$。
两次不同中心各翻一次才能从 $s$ 到达 $t$，每种顺序只有一个中间配置。
整数交换的 $(t,s)$ 块给

$$

R_t^2T_{ta}T_{as}=R_t^2T_{tb}T_{bs}.

$$

$R_t$ 可逆，故两条方块运输相等。
从空集向合法 $q$ 添加其各位，全部中间子集合法；任意两个添加顺序由相邻交换连接，每次交换均在上述合法方块内。
所得运输 $G_q$ 与顺序无关，并满足每条添加边的 $G_{q+j}=T_{q+j,q}G_q$。
删除边取逆，所有路径于是逐边消去为端点运输之比。取 $F_q=G_qG_{q_*}^{-1}$，得根定标架；连通性给唯一性。
在传导的正交基中 $L_q=i$、所有 $T_{qr}=1$，所以逐块恢复原 $\mathcal P_j$ 与全内部脉冲。

∎

相位差在连通图上的根标架恢复是已有同步问题；这里必须先由特定整数控制关系取得方块一致性。
Singer 的角同步论文从已有角差出发，也明确指出沿树累积误差的问题；本文不使用其谱算法、随机噪声模型或数值实验。[9](#ref-singer)

<a id="section-3"></a>

## 3. 三轴的准确位置：局部角落而非整个配置空间

<a id="thm:corner"></a>

#### 定理 3.1（每条原生边的 Pauli 角落）

在定理 [2.3](#thm:nativeJ) 下，取一条翻转边 $q_0\leftrightarrow q_1$，令 $P$ 投影到 $V_{q_0}\oplus V_{q_1}$。
在该角落定义

$$

X=\begin{pmatrix}0&T_{q_0q_1}\\T_{q_1q_0}&0\end{pmatrix},\qquad
Z=\begin{pmatrix}I&0\\0&-I\end{pmatrix},\qquad
Y=\mathcal J XZ,

$$

并在角落外取零。则它们为实对称、复 Hermitian 算子，并满足

$$

X^2=Y^2=Z^2=P,\qquad
\{X,Y\}=\{Y,Z\}=\{Z,X\}=0,\qquad XYZ=\mathcal J P.

$$

原地址的这个块精确为

$$

\boxed{PB_jP=\tfrac12P+cX+\tfrac{x-x^2}{2}Z.}

$$

其局部 Bloch 方向 $n=(2c,0,x-x^2)$ 为单位向量，故此块为复秩一投影。

**证明。**

边等距与逆关系给 $X^2=P$，且 $XZ=-ZX$；$Z^2=P$。
交织给 $[\mathcal J,X]=[\mathcal J,Z]=0$，而 $\mathcal J^\dagger=-\mathcal J$、$\mathcal J^2=-I$。
因此 $Y^\dagger=Y$、$Y^2=P$，并与 $X,Z$ 反对易；直接乘积给 $XYZ=\mathcal J P$。
原块对角之和 $x+x^2=1$、之差 $x-x^2$，非对角系数为 $c$，得到显示式。
最后

$$

4c^2+(x-x^2)^2=(x+x^2)^2=1.

$$

所以 $(2PB_jP-P)^2=P$，且 $PB_jP$ 的复迹为 $x+x^2=1$，故在复二维角落为秩一投影。

∎

#### 命题 3.2（奇数复维的全局三轴障碍）

全 89 配置来源的实维为 178，不可能在整个实载体上有三个实对称反对易对合。

**证明。**

若存在，v62/V53 的 Clifford 论证给其乘积为复结构，并使载体成为 $m$ 份复二维 Pauli 表示，实维必须为 $4m$。
亦可直接在所得复结构下，用第一轴等距交换第三轴的正、负特征空间，得到二者复维相等。
178 不被四整除，矛盾。

∎

因此，共同虚单位存在与全空间 Pauli 三轴存在不是同一命题。
610 配置来源的实维 1220 没有此维数障碍，但源文仍未自动供应任意全局三轴实际读出。
每条边的数学角落也不赋予独立控制该块、任意准备该块或读取 $X,Y,Z$ 的实际权限。
三轴关系中的单位在此为 $P$，不能抹去角落外全部配置。[2](#ref-quantum) [3](#ref-v53)

<a id="section-4"></a>

## 4. 近似整数交换如何控制原生相位与门字

<a id="def:stable"></a>

#### 定义 4.1（本轮稳定前件）

保留定义 [2.1](#def:native)--[2.2](#def:conservation) 的精确前件，只将有关整数远距交换放松为

$$

\|[\mathsf K_j,\mathsf K_k]\|_{\mathrm{op}}\le\varepsilon
\quad\text{对每个可形成合法双添加方块的 }j,k.

$$

置

$$

\gamma=2c|\sin(\alpha/2)|>0,\qquad
\eta_\square=\varepsilon/\gamma^2,\qquad
h_m=\lceil m/2\rceil-1.

$$

这里 $h_9=4,h_{13}=6$。范数及伴随均使用已给实正度量。

共同 $\mathcal J$ 由精确保范数与根钟已经取得；本节的误差影响原规范平坦标架，而不破坏该共同复作用。
对 610 配置来源，某些原语仍限于固定读器内部；上述算子误差是条件，不开放额外程序排列。

<a id="lem:square"></a>

#### 引理 4.2（方块运输误差）

每个合法方块 $s,a,b,t$ 满足

$$

\boxed{\|T_{ta}T_{as}-T_{tb}T_{bs}\|\le\eta_\square.}

$$

**证明。**

用命题 [2.4](#prop:exactflat) 的同一唯一两步路径计算，交换子的 $(t,s)$ 块等于
$R_t^2$ 乘两条运输之差，至多相差一个整体符号。
压缩块的范数不超过全交换子范数。
$R_t^\dagger R_t=\gamma^2I$，所以 $(R_t^2)$ 的最小奇异值为 $\gamma^2$；消去该因子即得结论。

∎

<a id="thm:frame"></a>

#### 定理 4.3（升序标架的全边与闭路预算）

对每个合法 $q$，固定从空集按位号递增添加的运输 $G_q$，并置

$$

F_q=G_qG_{q_*}^{-1}.

$$

这些等距满足 $F_{q_*}=I$、$L_qF_q=F_qL_{q_*}$，且对每条边

$$

\boxed{\|T_{qr}-F_qF_r^{-1}\|\le h_m\eta_\square.}

$$

长度为 $\ell$ 的任意翻转闭步运输 $T_{\rm loop}$ 满足

$$

\|T_{\rm loop}-I\|\le\ell h_m\eta_\square.

$$

**证明。**

对添加边 $r\to r+j$，比较“先升序添加 $r$、最后加 $j$”与升序添加 $r+j$。
把最后的 $j$ 向左移动，至多越过 $|r|$ 个已占据位；这些位与 $j$ 同属合法 $r+j$，所以每次交换的方块合法。
每个交换引起的运输差由引理 [4.2](#lem:square) 控制，左右乘等距不改变范数。
合法集合最多含 $\lceil m/2\rceil$ 个位，故 $|r|\le h_m$。
因此 $\|T_{r+j,r}G_r-G_{r+j}\|\le h_m\eta_\square$。
乘 $G_r^{-1}$ 后，根的共同重标定精确消去，得边界。删除边取逆，范数相同。
各 $G_q$ 由精确交织构成，故给所述 $L_q$ 相容性。
最后把闭步上每条 $T_{qr}$ 替换为平坦运输 $F_qF_r^{-1}$；乘积差逐项展开，每项不超过边预算。
平坦乘积望远镜消去为 $I$，得到闭步界。

∎

更细的非均匀版本可逐个相邻交换累加其实际方块预算，无须先取统一最大值。
这里构造标架是数学比较，不声称实际执行过从空配置出发的制备或控制路径。

<a id="thm:word"></a>

#### 定理 4.4（原投影脉冲及有限门字的稳定性）

用上述 $F_q$ 和实际根基作保配置的复坐标映射 $\mathcal C$。
令 $\widetilde B_j=\mathcal C B_j\mathcal C^{-1}$，$\mathcal P_j$ 为原规范投影。
则

$$

\|\widetilde B_j-\mathcal P_j\|\le c h_m\eta_\square.

$$

对任意给定实标量 $\beta_j$，令

$$

\widetilde U_j=e^{i\beta_j}[I+(e^{i\beta_j}-1)\widetilde B_j],\qquad
U_j=e^{i\beta_j}[I+(e^{i\beta_j}-1)\mathcal P_j].

$$

有

$$

\boxed{\|\widetilde U_j-U_j\|
\le2c h_m\eta_\square|\sin(\beta_j/2)|.}

$$

对同一个已允许门字 $w=(j_1,\ldots,j_L)$，有

$$

\boxed{\|\widetilde U_w-U_w\|\le\Delta_w,
\quad
\Delta_w=2c h_m\eta_\square\sum_{\ell=1}^{L}|\sin(\beta_{j_\ell}/2)|.}

$$

原全部 $\beta_j=\alpha$ 时，简化为

$$

\boxed{\Delta_w\le\frac{Lh_m\varepsilon}{\gamma}.}

$$

若 $0\preceq E\preceq I$，对应 Heisenberg 效果满足

$$

\|\widetilde U_w^\dagger E\widetilde U_w-U_w^\dagger EU_w\|
\le2\Delta_w.

$$

**证明。**

根坐标使全部 $L_q=iI$。每个翻转块的对角项保持原值，边运输与恒等相差至多 $h_m\eta_\square$。
投影差的二点块为 $c\left(\begin{smallmatrix}0&D\\D^\dagger&0\end{smallmatrix}\right)$，其范数为 $c\|D\|$；直和范数取最大值，单点差为零。
两者均为正交投影，所以显示的指数公式精确成立，且

$$

\widetilde U_j-U_j=e^{i\beta_j}(e^{i\beta_j}-1)(\widetilde B_j-\mathcal P_j).

$$

标量模长为 $2|\sin(\beta_j/2)|$，得到单门界。
两组门均酉，对乘积差逐项展开，其余因子范数为一，故总误差不超过单门误差和。
原标量情形利用 $2c|\sin(\alpha/2)|=\gamma$ 化简。
最后在两效果间加减 $U_w^\dagger E\widetilde U_w$，取范数即得 $2\Delta_w$。

∎

> 编者注（控制权限）：定理中的任意实参数 $\beta_j$ 定义数学比较脉冲；实际结论只用于同一个已经允许、参数亦已供应的有限门字，不因此增加原控制菜单。

同一证明将 $\beta_j$ 换成 $s\beta_j$，控制整个内部单位区间，而不赋予实际分数调用权限。
固定每步误差不能据此给无限门前缀统一小误差；需要可求和预算或另有证明的整体结构。
本节保留精确保范数，未将小有限时间范数缺陷自动转为小生成元反自伴缺陷。

<a id="section-5"></a>

## 5. 共享锚怎样取得度量关系并控制缺陷

V14 已证明给定正半定核的最小 Hilbert 商实现。本节研究此前的一层：一张有限关系表在什么共享条件下能够认证为正核，或接近一个低秩正核。[4](#ref-v14)
本节先用实核；把转置换为伴随，同一论证给复版本。

#### 定义 5.1（锚关系与残差核）

给候选对称记录表

$$

\Gamma=\begin{pmatrix}A&B\\B^{\mathsf T}&C\end{pmatrix},\qquad A\succ0,

$$

其中 $A$ 为同一组 $r$ 个锚记录的关系块，另有 $n$ 个新记录。
定义

$$

X=A^{-1}B,\qquad S=C-B^{\mathsf T}A^{-1}B.

$$

开始时不假定整个 $\Gamma$ 正半定。

<a id="thm:schur"></a>

#### 定理 5.2（关系的锚分解、正性与秩）

有

$$

\boxed{\Gamma\succeq0\iff S\succeq0,
\qquad \operatorname{rank}\Gamma=r+\operatorname{rank} S.}

$$

若存在 Gram 实现，$S$ 恰为新记录相对于锚张成空间的正交残差核。

**证明。**

对系数 $a,b$，平方完成给

$$

\begin{pmatrix}a\\b\end{pmatrix}^{\mathsf T}
\Gamma\begin{pmatrix}a\\b\end{pmatrix}
=(a+A^{-1}Bb)^{\mathsf T}A(a+A^{-1}Bb)+b^{\mathsf T}Sb.

$$

相应的可逆三角合同变换把 $\Gamma$ 变为 $\operatorname{diag}(A,S)$，给正性与秩结论。
若锚向量为 $v_a$、新记录为 $w_j$，$b_j$ 为 $B$ 的第 $j$ 列，则
$\widehat w_j=\sum_a(A^{-1}b_j)_av_a$ 是锚空间投影；
直接展开 $\langle w_j-\widehat w_j,w_k-\widehat w_k\rangle$ 得 $S_{jk}$。

∎

因此“关系再分解为关系与误差”可严格写成：锚解释的关系加正交残差之间的关系。
残差秩计数新线性方向；来源唯一性不迫使该秩为零。
例如同一固定 $\Omega=e_1$ 经恒等门和交换门产生记录向量 $e_1,e_2$，其 Gram 为 $I_2$。

<a id="thm:anchor"></a>

#### 定理 5.3（共享锚的有限局部正性与近邻低秩核）

设 $0\le S_{jj}\le\epsilon_j$，且每两个新记录连同同一组全部锚的 $(r+2)$ 阶块均正半定。
令

$$

\Gamma_0=\begin{pmatrix}A&B\\B^{\mathsf T}&B^{\mathsf T}A^{-1}B\end{pmatrix}.

$$

则

$$

\boxed{\Gamma_0\succeq0,\quad\operatorname{rank}\Gamma_0=r,
\quad\|\Gamma-\Gamma_0\|\le\sum_j\epsilon_j.}

$$

特别地，所有残差对角为零时，有限共享锚合同给出 $\Gamma=\Gamma_0$ 的精确正核与秩闭合。

**证明。**

每个 $(r+2)$ 阶正块的 Schur 余项为
$\left(\begin{smallmatrix}S_{jj}&S_{jk}\\S_{kj}&S_{kk}\end{smallmatrix}\right)\succeq0$，
所以 $|S_{jk}|\le\sqrt{\epsilon_j\epsilon_k}$。
对任意 $z$，

$$

|z^{\mathsf T}Sz|
\le\left(\sum_j\sqrt{\epsilon_j}|z_j|\right)^2
\le\left(\sum_j\epsilon_j\right)\|z\|^2.

$$

故 $\|S\|\le\sum_j\epsilon_j$。
$\Gamma_0$ 的 Schur 余项为零，定理 [5.2](#thm:schur) 给其正性与秩；两核的差只有右下块 $S$。

∎

非零误差时，本定理只给一个近邻正核，不自动使原 $\Gamma$ 正半定，也不宣称实际执行了核修复。
取得这些实相干关系、共享锚身份和局部正性仍是前件。

#### 命题 5.4（所有低阶局部核仍可共同失败）

对任意 $N\ge4$，令 $N\times N$ 对称矩阵的对角为一、非对角为 $-1/(N-2)$。
它的全部真主子矩阵正半定，但整个矩阵不是正半定。

**证明。**

记 $\rho=-1/(N-2)$，任意 $k$ 阶主块的二次型为

$$

(1-\rho)\|z\|^2+\rho\left(\sum_i z_i\right)^2
\ge[1+(k-1)\rho]\|z\|^2.

$$

当 $k\le N-1$ 时系数非负。
但全一向量在完整核上的值为 $N[1+(N-1)\rho]=-N/(N-2)<0$。

∎

$N=4$ 时全部三记录核都可实现，四记录全一组合却给负值 $-2$。
所以二元、三元分解还需要共享重叠关系及闭合条件；不能只分别验证各局部可实现。

<a id="lem:anchorcal"></a>

#### 引理 5.5（有限张成锚的忠实缺陷界）

给 $r$ 维实内积空间的张成锚 $u_1,\ldots,u_r$，其 Gram 矩阵至少为 $\lambda I$，$\lambda>0$。
对任意到另一实内积空间的线性映射 $D$，有

$$

\boxed{\|D\|^2\le\lambda^{-1}\sum_{a=1}^{r}\|Du_a\|^2.}

$$

**证明。**

令合成映射 $U$ 的列为这些锚。$U^{\mathsf T}U\succeq\lambda I$ 且 $U$ 可逆，故 $UU^{\mathsf T}\succeq\lambda I$。
于是
$\sum_a\|Du_a\|^2=\operatorname{Tr}(DUU^{\mathsf T}D^{\mathsf T})\ge\lambda\operatorname{Tr}(DD^{\mathsf T})\ge\lambda\|D\|^2$。

∎

#### 推论 5.6（两个实际锚到原生方块预算）

对合法方块 $s,a,b,t$，令 $C_{ts}=P_t[\mathsf K_j,\mathsf K_k]\iota_s$。
若起点纤维的两个实际锚具有 Gram 下界 $\lambda_s I$，并取得相干差记录

$$

\sum_{a=1}^{2}\|C_{ts}u_a\|^2\le\kappa_\square,

$$

则

$$

\|T_{ta}T_{as}-T_{tb}T_{bs}\|
\le\frac{\sqrt{\kappa_\square/\lambda_s}}{\gamma^2}.

$$

**证明。**

先用引理 [5.5](#lem:anchorcal) 控制压缩交换子，再用同一 $R_t^2$ 消去式。

∎

这给全算子缺陷一个有限锚入口，但两个准备、相干差比较和配置读口均须实际供应。
原唯一 ready 不自动提供任意纤维的张成锚。
若锚趋于线性相关，$\lambda_s$ 趋零，同样读数误差会被放大；单纯重新归一化不能消除此条件数。

<a id="section-6"></a>

## 6. 有限正细化合同怎样产生近似 Born 表示

v62 的可数有理全菜单条件给精确 Born 表示。本节改为有限且带误差的证书。
标准全效果表示已有 Busch 与项目定理；此处单独证明有限覆盖与实际目标预算。[8](#ref-busch) [7](#ref-unordered)
新 §212 的平方最小电流律不自动供应本节所有菜单。
这里的读数指已取得或有有效区间界的量，不把单次报告当作精确概率。

<a id="def:finitebasis"></a>

#### 定义 6.1（有限效果基与候选矩阵）

在已声明复矩阵接口 $\operatorname{Herm}_d(\mathbb C)$ 中，取实线性效果基

$$

F_0=I,F_1,\ldots,F_{d^2-1},\qquad0\preceq F_j\preceq I,

$$

及迹对偶基 $D_j$，$\operatorname{Tr}(D_jF_k)=\delta_{jk}$。
同一来源、同一切口给实际标定数 $b_0=1,b_1,\ldots,b_{d^2-1}$。
定义

$$

H=\sum_jb_jD_j.

$$

此时 $H$ 自伴、$\operatorname{Tr} H=1$，但尚未证明 $H\succeq0$。
给已知界 $M\ge\|H\|$，例如可用 $M=\sum_j|b_j|\|D_j\|$。

<a id="def:net"></a>

#### 定义 6.2（有限方向正性证书）

给有限单位向量集 $\mathcal N$ 与 $0\le\theta<1$，满足

$$

\forall\|u\|=1\quad\exists v\in\mathcal N:
|\langle u,v\rangle|^2\ge1-\theta.

$$

每个 $P_v=vv^\dagger$ 有实际非负读数 $y_v$，并有同切口关系证书

$$

|y_v-\operatorname{Tr}(HP_v)|\le\eta_{\rm p}.

$$

所有误差参数均取非负实数。

有限维紧性给正容差的有限几何覆盖；没有由此证明其原生取得成本。
当 $d\ge2$ 时，有限固定方向不可能令 $\theta=0$。

<a id="thm:finiteborn"></a>

#### 定理 6.3（有限覆盖的正性修复及目标误差）

在定义 [6.1](#def:finitebasis)--[6.2](#def:net) 下，置

$$

a_{\rm p}=\frac{\eta_{\rm p}+\theta M}{1-\theta}.

$$

则 $\lambda_{\min}(H)\ge-a_{\rm p}$。
写正负谱分解 $H=H_+-H_-$，令 $t=\operatorname{Tr} H_-$，则

$$

0\le t\le(d-1)a_{\rm p},\qquad
\rho=\frac{H_+}{1+t}

$$

为密度矩阵，并精确满足

$$

\boxed{\tfrac12\|H-\rho\|_1=t.}

$$

任意额外实际效果 $E$ 若具有关系证书
$|y_E-\operatorname{Tr}(HE)|\le\zeta_E$，则

$$

\boxed{|y_E-\operatorname{Tr}(\rho E)|\le\zeta_E+t
\le\zeta_E+(d-1)\frac{\eta_{\rm p}+\theta M}{1-\theta}.}

$$

**证明。**

令 $u$ 是最小特征值 $\lambda$ 的单位特征向量，取覆盖向量 $v=\alpha u+w$，$w\perp u$，$s=\|w\|^2\le\theta$。
交叉项为零，故

$$

v^\dagger Hv=(1-s)\lambda+w^\dagger Hw
\le(1-s)\lambda+sM
\le(1-\theta)\lambda+\theta M.

$$

实际非负读数及证书给 $v^\dagger Hv\ge-\eta_{\rm p}$，整理即得 $\lambda\ge-a_{\rm p}$。
迹一保证至少一个特征值严格正，负特征值至多 $d-1$ 个，所以 $t\le(d-1)a_{\rm p}$。
$\operatorname{Tr} H_+=1+t$，而

$$

H-\rho=\frac{t}{1+t}H_+-H_-.

$$

两项支持正交，正、负部的迹都为 $t$，给迹范数等式。
对效果 $0\preceq E\preceq I$，迹零自伴矩阵的响应绝对值至多其正部迹，故
$|\operatorname{Tr}((H-\rho)E)|\le t$。再加实际关系残差即证。

∎

正部修复是数学重构，不宣称实际执行了过滤、后选或删除记录。
若仅有 $y_v\ge-\epsilon_{\rm pos}$，将 $\eta_{\rm p}$ 换为 $\eta_{\rm p}+\epsilon_{\rm pos}$ 即可。
有限基的条件性通过 $M$ 进入预算，不能把它忽略。

### 6.1. 实际关系证书由两棵正细化树供应

<a id="def:certificate"></a>

#### 定义 6.4（有限正细化证书）

给目标效果的已知实线性关系 $E=\sum_jc_jF_j$，$c_j\in\mathbb R$。置

$$

\Lambda_E=1+\sum_j|c_j|,
\qquad
S_E=E+\sum_{c_j<0}(-c_j)F_j
=\sum_{c_j>0}c_jF_j.

$$

除以 $\Lambda_E$ 后，两侧的全部叶及部分和都是效果。
实际取得两侧各一棵正二叉细化树、全部叶的缩放比较及两根对应同一 $S_E/\Lambda_E$ 的比较。
两树内部加性缺陷总和为 $\Delta_L,\Delta_R$，两根读数差至多 $r_0$。
全部叶缩放缺陷总和记为 $\Sigma_{\rm scale}$，包括

$$

\left|p(E/\Lambda_E)-y_E/\Lambda_E\right|,
\qquad
\left|p(|c_j|F_j/\Lambda_E)-|c_j|b_j/\Lambda_E\right|.

$$

若某侧是空和，以零效果叶表示，并将该叶相对于数值零的实际读数缺陷计入 $\Sigma_{\rm scale}$。

<a id="prop:certificate"></a>

#### 命题 6.5（有限菜单到有限线性关系）

以上证书给

$$

\boxed{|y_E-\operatorname{Tr}(HE)|\le\zeta_E,
\quad\zeta_E=\Lambda_E(\Delta_L+\Delta_R+\Sigma_{\rm scale}+r_0).}

$$

**证明。**

在两棵树分别相加全部节点缺陷，中间节点读数消去，得到各根与叶总和的距离。
比较两根并加入叶缩放误差，得到

$$

\left|\frac{y_E}{\Lambda_E}
+\sum_{c_j<0}\frac{-c_j}{\Lambda_E}b_j
-\sum_{c_j>0}\frac{c_j}{\Lambda_E}b_j\right|
\le\Delta_L+\Delta_R+\Sigma_{\rm scale}+r_0.

$$

乘 $\Lambda_E$，再用 $\operatorname{Tr}(HE)=\sum_jc_jb_j$。

∎

若一个树节点比较使用同一补效果的二菜单及三菜单，其归一缺陷分别为 $\epsilon_2,\epsilon_3$，相减给该节点加性缺陷至多 $\epsilon_2+\epsilon_3$。
有理缩放也可通过实际等分与合并取得：对整数 $1\le m\le n$，若 $G=F/n$ 的 $n$ 份合并及 $m$ 份合并均已取得，每节点缺陷不超过 $\delta$，则

$$

\left|p((m/n)F)-\frac mn p(F)\right|
\le(m-1)\delta+\frac{m(n-1)}n\delta.

$$

这仍要求相同叶的实际身份；零缩放另由零效果标定处理。
矩阵可等分不等于原控制中存在对应制备或读口；任意实缩放须另有实际合同。

### 6.2. 两配置三轴接口的直接几何界

#### 推论 6.6（有限 Bloch 方向证书）

在已取得的局部 qubit 接口上，写候选
$H=(I+r\cdot\sigma)/2$。
给有限单位方向集 $\mathcal D$，令

$$

\chi=\inf_{\|u\|=1}\max_{n\in\mathcal D}|u\cdot n|>0.

$$

若实际 $y_n\in[0,1]$ 满足
$|y_n-(1+r\cdot n)/2|\le\eta_{\rm p}$，则

$$

\|r\|\le\frac{1+2\eta_{\rm p}}\chi.

$$

令 $r_*=r/\max(1,\|r\|)$、$\rho_*=(I+r_*\cdot\sigma)/2$。
目标 $E=aI+b\cdot\sigma$ 若有 $|y_E-(a+b\cdot r)|\le\zeta_E$，则

$$

|y_E-\operatorname{Tr}(\rho_*E)|
\le\zeta_E+\|b\|\left(\frac{1+2\eta_{\rm p}}\chi-1\right).

$$

**证明。**

读数范围给 $|r\cdot n|\le1+2\eta_{\rm p}$；$r=0$ 时范数界平凡，否则对 $r/\|r\|$ 用覆盖常数即得。
径向修复距离为 $\max(0,\|r\|-1)$，再用 $|b\cdot(r-r_*)|\le\|b\|\|r-r_*\|$。

∎

若 $\mathcal D\cup(-\mathcal D)$ 是欧氏距离 $h$ 的球面网，则
$\chi\ge1-h^2/2$，由 $u\cdot n=1-\|u-n\|^2/2$ 得到。
对效果有 $\|b\|\le1/2$。这些方向是数学证书需要的读出，不由原生角落公式自动取得。

<a id="section-7"></a>

## 7. 有限测试能证明什么，不能证明什么

<a id="prop:finite-no-go"></a>

#### 命题 7.1（任意有限固定方向不认证精确全正性）

给任意非空有限方向集 $\mathcal D\subset S^2$，存在迹一 Hermitian 矩阵 $H\not\succeq0$，
却使全部测试投影 $P_n=(I+n\cdot\sigma)/2$ 的值处于 $[0,1]$，并精确保持这些效果之间的所有线性关系。

**证明。**

选单位 $u$ 避开有限个 $\pm n$，令 $a=\max_{n\in\mathcal D}|u\cdot n|<1$。
取 $s>1$ 且 $sa\le1$，置 $H=(I+su\cdot\sigma)/2$。
测试值 $(1+su\cdot n)/2$ 在 $[0,1]$；同一迹泛函自动保持所有线性关系。
但 $H$ 的最小特征值为 $(1-s)/2<0$。

∎

例如 $H=(I+\sigma_x+\sigma_y+\sigma_z)/2$ 对三条正轴给一、三条负轴给零，互补归一精确成立，
却有负特征值 $(1-\sqrt3)/2$。
因此有限覆盖的几何余量不可无条件删去。

<a id="prop:future"></a>

#### 命题 7.2（连续性与有限菜单也不决定全部未来读数）

设有限测试效果集 $S$ 含完整线性标定基，全部已测值为 qubit 最大混态读数 $\tau(E)=\operatorname{Tr}(E)/2$。
存在连续函数 $p:[0,I]\to[0,1]$，满足全部二元互补归一并通过这些有限测试，却不是 Born 赋值。

**证明。**

选秩一投影 $P$，使 $P,I-P\notin S$。
取足够小的 $r<1/4$，使以 $P,I-P$ 为心的两个算子范数球互不相交且避开 $S$。
定义

$$

b(E)=\max\left(0,1-\frac{\|E-P\|}{r}\right),
\qquad
p(E)=\tau(E)+\tfrac18[b(E)-b(I-E)].

$$

连续性及互补归一直接成立；在测试集上两个尖帽均为零。
尖帽非零时，$E$ 距 $P$ 或 $I-P$ 小于 $r$，故 $|\tau(E)-1/2|<r$，
加减至多 $1/8$ 后仍在 $[0,1]$；其他地方等于 $\tau$。
但 $p(P)=5/8$。已测基强迫任何 Born 代表为 $I/2$，其对 $P$ 的值只能为 $1/2$，矛盾。

∎

所以新增目标的实际关系证书 $\zeta_E$ 不能省略。
反之，若额外允许取得候选 $H$ 的最小特征方向投影，并取得该投影相对于同一个 $H$ 的关系证书，
则其非负读数和关系误差 $\eta_{\rm p}$ 直接给
$\lambda_{\min}(H)\ge-\eta_{\rm p}$，可将定理 [6.3](#thm:finiteborn) 的 $a_{\rm p}$ 换为 $\eta_{\rm p}$。
这是自适应最坏方向检验，实际取得可能远强于原固定门权限；数学最优化不自动成为实际测量。

<a id="section-8"></a>

## 8. 把原生门与有限读出合成一个误差定理

<a id="thm:combined"></a>

#### 定理 8.1（同一来源的有限门字--读出总预算）

在定义 [4.1](#def:stable) 的同一来源和根坐标中，取 $d=|E_m|$，在这个共同复载体上给定义 [6.1](#def:finitebasis)--[6.2](#def:net) 的有限读出标定。
取一个实际允许的门字 $w$ 和终端效果 $0\preceq E\preceq I$。
假定该程序的实际报告 $y_w$ 已被对应到同一初切口上的效果

$$

E'_w=\widetilde U_w^\dagger E\widetilde U_w,

$$

且为它实际取得命题 [6.5](#prop:certificate) 的有限关系证书，残差为 $\zeta_w$。
则定理 [6.3](#thm:finiteborn) 所构造的同一个密度矩阵 $\rho$ 满足

$$

\boxed{\left|y_w-\operatorname{Tr}(\rho U_w^\dagger EU_w)\right|
\le\zeta_w+(d-1)\frac{\eta_{\rm p}+\theta M}{1-\theta}+2\Delta_w.}

$$

对原 $\beta_j=\alpha$、长度 $L$ 的门字，最后一项可取
$2Lh_m\varepsilon/\gamma$。

**证明。**

在实际报告与理想目标之间插入 $\operatorname{Tr}(HE'_w)$ 与 $\operatorname{Tr}(\rho E'_w)$。
第一差由实际关系证书控制为 $\zeta_w$；第二差由定理 [6.3](#thm:finiteborn) 控制为
$t\le(d-1)a_{\rm p}$；第三差不超过
$\|E'_w-U_w^\dagger EU_w\|\le2\Delta_w$。
相加即证。

∎

这三项有不同含义：实际关系取得误差、有限正性覆盖误差、原生门字实现误差。
定理不把实际报告与 $E'_w$ 的对应视为免费的 Heisenberg 记号；这项来源桥明确位于前件中。
不同行为、未来菜单或条件切口若未接到同一标定，不属于本总预算。
若另有已取得的共同不变子接口，可在其维数上应用同式；任意局部 qubit 证书不能直接替代全来源的标定。

### 8.1. 算子稳定尚不是完整微历史稳定

新 §212 的精确来源桥保持实际调用、跳时、档案、垃圾与失败坐标。
本文稳定定理只控制门字、声明效果及相应有限读数，不自动给这些微历史的总变差或逐样本稳定。
闭守卫首次命中和相切对小扰动可能不连续：例如在 $[0,1]$ 上，
守卫函数 $f(s)=(s-1/2)^2$ 对闭条件 $f\le0$ 在 $1/2$ 命中，
而 $f(s)+\delta$ 对任意 $\delta>0$ 都不命中，尽管一致距离仅为 $\delta$。
所以要继续推导路径级误差，还须实际守卫裕量、横截条件或明确概率耦合。
该例说明一般连续性障碍，不声称它已构造了违反新源全部专门守卫前件的实例。

同理，本轮没有同时稳定化精确保范数前件。
在一般实生成元中，取 $J_0=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$、
$D=\operatorname{diag}(1+\delta,1)$，其中 $\delta>0$ 固定且很小，并令 $A=D(\omega J_0)D^{-1}$。
则 $e^{sA}=De^{s\omega J_0}D^{-1}$ 的等距缺陷由 $D$ 的条件数控制，
而 $A+A^{\mathsf T}$ 可随 $\omega$ 放大。
所以从有限时间范数小误差到生成元小缺陷，需要额外导数或频率控制；
不能未经证明把本节范围扩大到所有前件同时带误差。

<a id="section-9"></a>

## 9. 量子起源的本轮公理重写与未决部分

> 作者原稿表格版式：`\begin{center}\small`、<code>\begin{tabularx}{\te<wbr>xtwidth}{@{}p{0.20\t<wbr>extwidth}XX@{}}</code>、`\toprule`、`\midrule`、`\bottomrule`，表后结束 `tabularx` 与 `center`。

| 结构 | 本轮可证明的入口 | 保留的前件 |
| --- | --- | --- |
| 原生共同虚单位 | 守恒、根钟、边交织 | 实二维容量、正度量、指定响应 |
| 原规范相位标架 | 整数交换取得合法方块；遗传族拼接 | 原控制关系及装置供应 |
| 局部三轴 | 两配置角落、共同 $\mathcal J$、等距边 | 角落的实际读出另须取得 |
| 稳定门序列 | 方块预算、升序标架、投影脉冲公式 | 精确保范数；允许的有限门字 |
| 正记录核 | 共享锚、局部正性、闭合残差 | 相干关系及锚身份 |
| 近似 Born 读出 | 有限基、方向覆盖、目标细化证书 | 实际菜单、共同切口、报告对应 |

本轮可以准确地说：项目已经在明确的原生实局部来源中，把共同复结构和标架从直接输入改写成其他关系前件的结论。
本文又给出这条装配的有限误差消费者，以及另一套有限正读出证书。
但没有证明这些总前件逻辑独立、最小、严格更弱，或在自然界自动成立。

特别需要区分三个层次：配置直和上的共同复结构、两配置角落中的 Pauli 三轴、不同系统张量复合的共同相位。
本轮前两者有明确原生关系，第三者仍有 v62/V53 的独立组合条件。
原生 $F[1],F[3],F[2],F[13],F[\mathrm{null}]$ 的五模式语义，也不能只按数目与这里的算子一一重命名。
真实类型桥须保留模式、配置、角落、控制和报告之间的具体映射。

对于唯一实际 $\Omega$，完整观察者的门前缀仍可增长。
增长并不使酉全态自动收缩误差：相同酉门保持全态间距离；
缩小的是某个已声明预测、关系估计或读出合同中的误差。
同一固定来源的记录族可以有高秩，新的记录关系也可以增加可分辨方向。
局部纯性、低秩闭合与全部本体信息是不同量词，均须以所用效果域和共同锚说明。

仍未推导的物理内容包括：为何实际局部容量为二、为何该正度量与黄金响应出现、为何足够校准菜单能取得、
概率创新和源／档案独立性的起源、任意 CP 仪器、一般系统组合、物理空间三维性及引力或局域钟速定律。
新 §212 的平方最小电流律仍为输入；本节有限 Born 证书是条件替代接口，不是已证明原来的唯一 ready 与固定读器自动供应这些菜单。

> 作者原稿分页指令：`\needspace{6\baselineskip}`。

本轮可核查的量子起源命题为：

> 
在同一个实际来源中，二维实响应的守恒与根钟能够产生共同虚单位，
原整数控制关系能够装配相位标架；在精确保范数和根钟前提下，整数交换的有限缺陷可以传导为有限门字误差。
若再实际取得有限正细化与正性覆盖证书，则声明的终端读数受到一个共同密度矩阵及明确总预算的约束。

## 固定来源与文献

> 作者原稿文献版式：`\begin{thebibliography}{99}` 与 `\raggedright`；文献项原序保留。

<a id="ref-head"></a>

**[1]**
The Omega Institute, *trureturing*, 固定提交：

[<code>a42f32e9a2a54ec0b017<wbr>48c96a6af312f941c853</code>](https://github.com/the-omega-institute/trureturing/commit/a42f32e9a2a54ec0b01748c96a6af312f941c853)。
唯一活动 HEAD 取得完成于 2026-11-01 04:26:30.197298（Asia/Singapore）；后续按固定身份读取。

<a id="ref-quantum"></a>

**[2]**
The Omega Institute,
[AURIC FIB Atom Quantum Principles and Coherent Reconstruction, Continuation IV](https://github.com/the-omega-institute/trureturing/blob/a42f32e9a2a54ec0b01748c96a6af312f941c853/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md)，
上述固定提交，新 §§209--213：实局部来源、原生相位装配、实际接口、完整历史消费及边界。
本轮连续核读全部新增 384 行；不以此认证全部早期依赖证明。

<a id="ref-v53"></a>

**[3]**
The Omega Institute,
[AURIC V53: Sharp Three-Axis Readouts, Endogenous Complex Structure and Common-Phase Compatibility](https://github.com/the-omega-institute/trureturing/blob/a42f32e9a2a54ec0b01748c96a6af312f941c853/docs/develop/theory/AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md)，
上述固定提交，实复结构、三轴 Pauli 表示、定向门、运输与复合相位。

<a id="ref-v14"></a>

**[4]**
The Omega Institute,
[AURIC V14: Existential Quantifiers, Circuit Semirings and Quantum Records](https://github.com/the-omega-institute/trureturing/blob/a42f32e9a2a54ec0b01748c96a6af312f941c853/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14.md)，
上述固定提交，§§9--10：记录 Gram、正核最小实现、条件平方律与强正性边界。本文件不是本轮新增。

<a id="ref-v30"></a>

**[5]**
The Omega Institute,
[AURIC V30: Unique Static Ontology, Endogenous Observers and Golden Recursive Clocks](https://github.com/the-omega-institute/trureturing/blob/a42f32e9a2a54ec0b01748c96a6af312f941c853/docs/develop/theory/AURIC_UNIQUE_STATIC_ONTOLOGY_ENDOGENOUS_OBSERVERS_AND_GOLDEN_RECURSIVE_CLOCKS_V30.md)，定理 2.2，给定正归一线性泛函的 GNS 构造。

<a id="ref-omega"></a>

**[6]**
The Omega Institute,
[AURIC Omega Static Compatibility Fiber Theory](https://github.com/the-omega-institute/trureturing/blob/a42f32e9a2a54ec0b01748c96a6af312f941c853/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，§12，给定相容正归一线性泛函的共同循环表示。

<a id="ref-unordered"></a>

**[7]**
The Omega Institute,
[AURIC Unordered Compatible Atom and Quantum Representation Theory](https://github.com/the-omega-institute/trureturing/blob/a42f32e9a2a54ec0b01748c96a6af312f941c853/docs/develop/theory/AURIC_UNORDERED_COMPATIBLE_ATOM_AND_QUANTUM_REPRESENTATION_THEORY.md)，§6，全效果正可加 Born 表示及边界。

<a id="ref-busch"></a>

**[8]**
P. Busch, *Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem*,
Physical Review Letters **91**, 120403 (2003).
[doi:10.1103/PhysRevLett.91.120403](https://doi.org/10.1103/PhysRevLett.91.120403);
[arXiv:quant-ph/9909073](https://arxiv.org/abs/quant-ph/9909073)。
本轮有限证书及误差界在正文另证。

<a id="ref-singer"></a>

**[9]**
A. Singer, *Angular Synchronization by Eigenvectors and Semidefinite Programming*,
Applied and Computational Harmonic Analysis **30**(1), 20--36 (2011).
[doi:10.1016/j.acha.2010.02.001](https://doi.org/10.1016/j.acha.2010.02.001);
[作者稿公开全文](https://pmc.ncbi.nlm.nih.gov/articles/PMC3003935/)。
本文引用其 §1 的问题定位、精确树恢复及误差累积背景，不使用其算法或实验结论。

> 作者原稿结束指令：`\end{thebibliography}`、`\end{document}`。

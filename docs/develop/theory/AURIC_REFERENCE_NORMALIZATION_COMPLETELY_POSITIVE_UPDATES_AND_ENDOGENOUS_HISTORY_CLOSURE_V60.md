**原稿编译、字体与版式信息（作者提供）。** 原稿指定 `% !TeX program = xelatex`；用 XeLaTeX 编译两次；可选定义 `AURICFontPath` 为绝对字体路径，例如 `/absolute/font/path/`。原稿声明：“All mathematical arguments are paper proofs. No mathematical program was used.” 这是原作者报告；本 Markdown 不声称执行过 XeLaTeX。

原稿为 11pt、A4 的 article，页边距 23mm，页眉高度 16pt。加载 fontspec；若定义 `AURICFontPath`，从该路径读取 `NotoSerifCJKsc-Regular.otf`，粗体和粗斜体用 `NotoSerifCJKsc-Bold.otf`，斜体用 Regular。未定义时，先检测 Noto Serif CJK SC：若存在，主字体与斜体为 Noto Serif CJK SC，粗斜体为 Noto Serif CJK SC Bold；否则主字体、斜体为 `FandolSong-Regular.otf`，粗体和粗斜体为 `FandolSong-Bold.otf`。等宽字体 Latin Modern Mono；中文断行区域 zh，断行伸缩 0pt plus 1pt。

原稿加载 geometry、fontspec、amsmath、amssymb、amsthm、mathtools、bm、mathrsfs、booktabs、array、tabularx、enumitem、fancyhdr、xcolor、needspace、hyperref。auricblue 为 RGB 24,53,79；链接支持 Unicode，链接、网址和引文均用 auricblue。PDF 标题为“AURIC v60：参考归一化、完全正更新与内生历史闭包”；作者为“AURIC research continuation”；主题为“Fixed ontic source, faithful relation quotients, pure reference probes, complete positivity, unitary dynamics and recursive error stability”。

原稿的数学宏在正文展开：实数、复数、Hilbert 空间、迹、张成、秩、自伴矩阵、恒等、向量化、对角矩阵以及 ket、bra、秩一投影；项目链接固定到提交 `768fe1b81b658f31b1213f9b25cc953baa679ba8`。采用 definition 定理样式；定义、定理、命题、推论、引理、说明按节共享编号。证明名“证明”，摘要名“摘要”，文献名“固定来源、文献与阅读边界”。

原稿首行缩进 1.8em、段间距 2pt、紧急伸缩 3em；列表无额外间距、左缩进 2em；fancy 页眉左为“AURIC：参考关系与内生过程”，右为“v60 / 2026-11-01”，页脚居中页码；显示公式允许分页，级别 2。标题、第二标题和版本行的字号依次为 LARGE、Large、large；前两行用 auricblue 并加粗，版本行用常规字重；其后间距依次为 7pt、8pt、5pt。Markdown 保留内容和编号，版式采用 Markdown 渲染。

# AURIC：量子起源的过程公理再推进

## 参考归一化、完全正更新与内生历史闭包

定义、定理与纸面证明　v60.0

2026 年 11 月 1 日　Asia/Singapore

### 摘要

本文延续唯一固定本体、完整内生观察者与单增门词的图景，将量子态的正性重构推进到更新过程。
一个实际可用的满 Schmidt 秩纯内部参考，在同一复线性局部作用条件下，足以检验完全正性；
过程归一化表现为全部未触及参考关系的边缘守恒，而不只是一个总迹等于一。
未条件化参考输出纯、参考边缘守恒且输入输出等维时，更新必为酉共轭。
在 qubit 球等距族中，参考正性进一步从 $O(3)$ 选出 $SO(3)$，精确连接三轴各向同性与相对取向。
对同一实际来源，预测核空间和效果关系残差空间的双重闭包，连同忠实效果商与单位锚，
推出共同线性更新、实际未归一读出桥及总迹保持，无需另行预设实际态族更新的仿射性。
关系残差缺陷沿实际记录成为非负超鞅；近似实际核给加法累计与有限时域超阈值界。
有限方向覆盖还给同时修复过程正性与矩阵归一化的明确公式，保留全部记录标签及参考条件成本。
这些是明确前件下的数学重构，不将复结构、参考制备、实际控制或历史闭包从本体唯一性中省略。

## 1. 本轮结论与项目进展

本轮的核心关系可以写成

$$
\boxed{\begin{gathered}
\text{共同线性局部作用}+\text{充分参考联合正性}
\Longrightarrow\text{完全正更新};\\
\text{全部参考边缘守恒}
\Longrightarrow\text{过程保迹};\\
\text{未条件化参考输出纯}+\text{保迹}+\text{等维}
\Longrightarrow\text{酉更新};\\
\text{双闭包}+\text{忠实效果商}+\text{单位锚}
\Longrightarrow\text{共同过程及实际历史相容}.
\end{gathered}}
$$

各箭头的前件将在下文完整列出。“归一化”由单个状态的一个标量等式，提升为一个过程必须保持的整组参考关系。
这使用户关于“关系也能递归传导”的直觉得到一个可以证明、可以指出失效位置的版本。

### 1.1 固定来源及准确的增量归属

本轮唯一活动 HEAD 响应固定项目于
`768fe1b81b658f31b1213f9b25cc953baa679ba8`。

取得时间为新加坡时间 2026-11-01 02:43:44.194429，提交时间为 02:42:51。
相对 v59 固定提交 `8558e845c6b6e49b11087733242e5ae386483392`，
前进 57 个提交、涉及 127 个路径；比较 JSON 与完整 diff 路径集一致，
未截断理论树从 1120 份文件增至 1121 份，五份理论文本改变。
这些是来源身份核对，不是全库数学正确性认证。[1](#ref-head)

> **编校注（Markdown 整理者，取得归属）：** 本段的唯一活动 HEAD、取得时刻、比较 JSON、提交／路径／理论文件数及审计记录，均为原作者在原稿中的取得报告；不据此声称整理者另作了一次活动 HEAD 请求或读取了原作者的审计记录。固定提交与前驱仍按原文钉定。

与本文直接相关的是新入库的 V56，以及 K-bonacci 卷新增的 §10。
V56 已在给定复 Hilbert、正态、Born 配对和节点 Kraus 完备式的条件下，证明内部二分、记录等距与有限相干记录树；
它明确保留内部初始化、实际菜单和无限层相容的前件。
因此本文研究的是这类仪器树的上游条件，而不将已有记录树归纳再次称为 CP 起源。[2](#ref-v56)

未变的《无序相容原子》§7.1 已区分单系统正性与任意参考上的完全正性；
未变的 RRO 与 Quantum IV 继续供应实际切口、关系一致性、历史联合失败和读出稳定性边界。
本文不把 v59 的这些增量再次记为本轮新增。[3](#ref-unordered)、[4](#ref-rro)、[5](#ref-qiv)

K-bonacci 的新结果是在 $k\ge2$、未知 $c>0$、未知非负非零量具 $\ell$、
目标 $c\ell^{\mathsf T}$、同源重制备及每次制备和完整窗口都付费的精确合同中，
同一个自适应协议同时达到

$$
p_k=k,\qquad w_k=2k-2,\qquad n_k=\max\{2k,3k-3\}.
$$

两条实际分支的成本是 $(k,k,2k)$ 与 $(k-1,2k-2,3k-3)$；不将分别的最坏值直接相加。
它没有给噪声稳定、有限精度或量子参考制备的费用。
源文也明确其到 FIB 的类型桥尚未建立，本文仅借此强调取得权限和校准资源必须明示。[7](#ref-kbonacci)

### 1.2 唯一完整来源与有限接口

全篇固定同一个本体来源 $\Omega$。完整观察者仍包括环境、参考、程序、记录、预测与自我读出；
在得到或采用酉实现后写为

$$
\Psi_k=U_k\cdots U_1\Omega.
$$

有限矩阵块是这个完整观察者内部的关系接口，绝不将观察者重新定义为环境偏迹后的局部态。
本文出现的偏迹只用于内部关系的边缘读数。
“门词单增”表示实际前缀延长，不意味着范数、熵或计算复杂度必然单调。

为了避免循环，本轮证明从一个尚未假定完全正或酉的线性更新候选出发。
在记录闭包部分，连共同线性更新也由明确的效果商构造得到。
复矩阵接口和相容复合仍是已声明的结构；本文没有声称从字面上的“二元”两字推出复数或张量积。
所有实际条件都施加于同一来源；数学定理中对全部向量或矩阵的量词，不代表多个实际宇宙或免费制备权限。

## 2. 从实际读数得到联合矩阵候选

#### 定义 2.1（关系一致性与充分方向）

在一个固定实际切口，声明自伴效果 $E_a\in\operatorname{Herm}_n$ 和同源实读数 $q_a$。
称读数满足关系一致性 RC，如果

$$
\sum_a c_aE_a=0\quad\Longrightarrow\quad\sum_a c_aq_a=0
$$

对全部有限实关系成立。假定效果实张成 $\operatorname{Herm}_n$，单位读数为 $t$。
另一个方向条件是：实际菜单包含一族 $cP_\phi$，其中 $c>0$ 是保留的读口增益，
$P_\phi=\lvert \phi\rangle\langle \phi\rvert$，方向在全部单位射线中稠密，且这些实际读数非负。

<a id="lem-state"></a>

#### 引理 2.2（固定响应的正表示）

效果张成与 RC 给唯一 $C=C^\dagger$，使

$$
q_a=\operatorname{Tr}(CE_a),\qquad\operatorname{Tr} C=t.
$$

若再有上述充分方向非负性，则 $C\succeq0$。

**证明。**

令 $L(\sum c_aE_a)=\sum c_aq_a$；RC 保证定义不依赖展开，效果张成保证定义域为全部 $\operatorname{Herm}_n$。
实迹配对非退化，故存在唯一 Hermitian 表示 $C$。对单位取值给迹条件。
对实际方向有 $c\langle\phi,C\phi\rangle\ge0$。
矩阵二次型连续，稠密性将此不等式推广到全部单位向量，故 $C\succeq0$。

∎

这里没有把有限菜单信息完备误当成正性：有限方向可以唯一重建 Hermitian 候选，
却仍遗漏一个负方向。上一轮的秩一轨道判据在此应用于*输出与内部参考的完整联合块*。
只检验乘积方向仍不够，V56 的 $\mathrm{Swap}/2$ 已给相应反例。[2](#ref-v56)、[5](#ref-qiv)

## 3. 一份充分内部参考如何推出完全正性

以下取输入矩阵代数 $M_d(\mathbb C)$、输出 $M_m(\mathbb C)$、内部参考 $M_d(\mathbb C)$，全部有限维。
$T$ 是共同的复线性、伴随保持更新候选。
它必须表示所声明局部操作在相同接口上的作用；不能从一份合法输出任意猜测一个适用于所有实际历史的过程。

#### 定义 3.1（归一过程矩阵与固定纯参考）

固定正交基，令

$$
\lvert \Phi_d\rangle=d^{-1/2}\sum_{i=1}^d\lvert i\rangle\lvert i\rangle,\qquad
J(T)=(T\otimes\operatorname{id})(P_{\Phi_d})
=\frac1d\sum_{ij}T(E_{ij})\otimes E_{ij}.
$$

本文始终使用*归一* Choi 约定。任取可逆矩阵 $A$，满足 $\operatorname{Tr}(A^\dagger A)=d$，定义

$$
\lvert \psi_A\rangle=(I\otimes A)\lvert \Phi_d\rangle,\qquad
\rho_R=\operatorname{Tr}_X P_{\psi_A}=\frac{AA^\dagger}{d}>0.
$$

其 Schmidt 秩为 $d$。令

$$
C_A(T)=(T\otimes\operatorname{id})(P_{\psi_A})
=(I_m\otimes A)J(T)(I_m\otimes A^\dagger).
$$

(3.1)

“参考未被触及”在此包含一个共同过程条件：输入与参考的联合读数确实由同一个 $T\otimes\operatorname{id}$ 表示。
仅有参考装置没有直接收到控制指令，不能消除未建模记忆或初始关联造成的接口依赖。
在实际读数语言中，可要求对全部声明乘积效果 $F\otimes G$，

$$
q(F,G)=\operatorname{Tr}\!\left[P_{\psi_A}\bigl(T^*(F)\otimes G\bigr)\right].
$$

(3.2)

乘积效果张成联合自伴空间，故式 (3.2) 与联合 RC 一起确定式 (3.1)。
这就是本轮保留的实际参考相容前件。

<a id="thm-cp"></a>

#### 定理 3.2（一个满 Schmidt 纯参考的完全正性判据）

在上述共同线性局部作用条件下，下列条件等价：

$$
C_A(T)\succeq0\quad\Longleftrightarrow\quad J(T)\succeq0
\quad\Longleftrightarrow\quad T\text{ 完全正}.
$$

因此，若固定参考输出的同源联合读数满足引理 [2.2](#lem-state) 的 RC、张成和充分方向非负条件，
就能推出 $T$ 完全正，而不必逐一实际制备任意参考输入。

**证明。**

式 (3.1) 是可逆合同变换，前两项等价。
若 $T$ 完全正，作用于正矩阵 $P_{\Phi_d}$ 当然给 $J(T)\succeq0$。
反向，写有限谱分解 $J(T)=\sum_\alpha v_\alpha v_\alpha^\dagger$，
按 $\operatorname{vec} K_\alpha=\sqrt d\,v_\alpha$ 将向量重排为 $m\times d$ 矩阵。
对矩阵单位比较可得

$$
T(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger.
$$

(3.3)

更直接，过程矩阵的逆公式为

$$
T(X)=d\,\operatorname{Tr}_R\!\left[J(T)(I_m\otimes X^{\mathsf T})\right].
$$

(3.4)

对任何参考维数 $r$ 和任意 $Z\succeq0$，

$$
(T\otimes\operatorname{id}_r)(Z)=\sum_\alpha(K_\alpha\otimes I_r)Z(K_\alpha^\dagger\otimes I_r)\succeq0.
$$

这正是完全正性的定义。

∎

这是 Choi–Kraus 标准对应的有限维证明；其一般数学事实不作原创声明。
本轮的工作是将它接到固定本体的*实际*联合读数、可用参考和历史闭包上。
Watrous 的作者文本采用未归一 Choi 约定，故其保迹边缘为 $I_d$；本文对应为 $I_d/d$。[8](#ref-choi)、[9](#ref-watrous)

<a id="thm-tp"></a>

#### 定理 3.3（过程归一化等价于参考边缘守恒）

对同一个线性候选 $T$，

$$
\boxed{
\operatorname{Tr}_YC_A(T)=\rho_R
\iff\operatorname{Tr}_YJ(T)=\frac{I_d}{d}
\iff T\text{ 保迹}.
}
$$

**证明。**

式 (3.1) 给 $\operatorname{Tr}_YC_A=A(\operatorname{Tr}_YJ)A^\dagger$，由 $A$ 可逆得到前一等价。
而

$$
\operatorname{Tr}_YJ(T)=\frac1d\sum_{ij}\operatorname{Tr}(T(E_{ij}))E_{ij}.
$$

它等于 $I_d/d$，当且仅当 $\operatorname{Tr}(T(E_{ij}))=\delta_{ij}$。
矩阵单位张成全空间，后者恰等价于对全部 $X$ 有 $\operatorname{Tr} T(X)=\operatorname{Tr} X$。

∎

这把归一化改写为*全部未触及参考效果的读数守恒*：

$$
\operatorname{Tr}\!\bigl[C_A(T)(I_m\otimes G)\bigr]=\operatorname{Tr}(\rho_RG)
\quad(G\in\operatorname{Herm}_d).
$$

只需一个实基上的等式即可推出全体等式，但单个标量 $\operatorname{Tr} C_A=1$ 不够。
例如取 $A=I$、$d\ge2$，$J=P_0\otimes P_0$ 正且迹一，却对应

$$
T(X)=d\langle0|X|0\rangle P_0,
$$

其参考边缘为 $P_0$，并非 $I_d/d$，因而不保迹。

<a id="cor-instrument"></a>

#### 推论 3.4（带完整记录的量子仪器）

设有限结果标签 $j$ 含成功、失败及原来的零标签；各分支属于同一更新接口，
并有 $C_j=C_A(T_j)\succeq0$，满足

$$
\sum_j\operatorname{Tr}_YC_j=\rho_R.
$$

(3.5)

则每个 $T_j$ 完全正，$\sum_jT_j$ 保迹，且每个分支迹不增。
存在 $K_{j\alpha}$ 使

$$
T_j(X)=\sum_\alpha K_{j\alpha}XK_{j\alpha}^\dagger,
\qquad\sum_{j,\alpha}K_{j\alpha}^\dagger K_{j\alpha}=I_d.
$$

(3.6)

**证明。**

逐分支用定理 [3.2](#thm-cp)，对总映射用定理 [3.3](#thm-tp)。
对 $X\succeq0$，每个 $\operatorname{Tr} T_j(X)\ge0$，其和为 $\operatorname{Tr} X$，故每项至多 $\operatorname{Tr} X$。
式 (3.6) 的完备关系由对全部 $X$ 的迹恒等式和迹配对非退化得到。

∎

式 (3.5) 对*全部结果求和*；已选择的条件分支一般会改变参考后验。
要求每个分支单独保持原参考边缘，会排除正常的关联测量。

## 4. 纯过程、酉性与三轴相对取向

<a id="thm-unitary"></a>

#### 定理 4.1（关联纯性与归一化强迫酉性）

设 $T:M_d(\mathbb C)\to M_m(\mathbb C)$ 满足定理 [3.2](#thm-cp)–[3.3](#thm-tp) 的条件。
若其*未条件化的参考–所声明输出* $C_A(T)$ 为纯态，则存在等距 $V:\mathbb C^d\to\mathbb C^m$，使

$$
T(X)=VXV^\dagger,\qquad V^\dagger V=I_d.
$$

当 $m=d$ 时，$V=U$ 为酉矩阵。
反向，任意等距共轭在该参考上输出纯，并保持参考边缘。

**证明。**

可逆合同保持秩，故 $\operatorname{rank} C_A=1$ 等价于 $\operatorname{rank} J(T)=1$。
定理 [3.2](#thm-cp) 的构造只有一个 Kraus 矩阵 $V$，于是 $T(X)=VXV^\dagger$。
保迹给 $V^\dagger V=I_d$；等维方阵的左逆也是右逆，故酉。
反向由 $(V\otimes I)\lvert \psi_A\rangle$ 仍是归一向量及 $V^\dagger V=I$ 直接得到。

∎

这里有三个不能删除的限定。
第一，满 Schmidt 纯参考的某个非零条件输出纯，只能推出该分支为单 Kraus 滤波，
例如 $K=\operatorname{diag}(1,1/2)$，不能推出酉。
第二，通道把每个普通纯输入送到某个纯输出也不够：
$T(X)=\operatorname{Tr}(X)P_0$ 是重置通道，所有输入都变成同一个纯态，但它的 $J=P_0\otimes I_d/d$ 秩为 $d$。
第三，完整本体纯不等于某个内部接口的参考输出纯；若把丢出的信息留在内部记录角色里，重置也可有纯的等距提升。
这些限定不削弱完整观察者图景，而是说明一个局部关系接口何时继承可逆性。

### 4.1 AURIC 三轴上的精确版本

在项目 V37 的固定编码中，原占据均值与 Bloch 坐标满足

$$
u=(X,Y,Z)=u_0+\nu r,
\quad\nu=(1+2\sqrt3+\sqrt{11})^{-1},
\quad u_0=(a_\nu,a_\nu,\nu),
\quad a_\nu=\frac{\nu(\sqrt3+\sqrt{11})}{2}.
$$

(4.1)

这是一份已给编码的标定，不改变原五模式含义；三个压缩读口仍有偏且非尖锐。
其归一化是五效果总和为 $I$，不能把某一个空模式单独改名为归一化算子。[6](#ref-v37)

对 qubit 保迹、伴随保持映射，写

$$
\rho(r)=\frac{I+r\cdot\sigma}{2},\qquad r\longmapsto b+Mr.
$$

其过程矩阵为

$$
J(T)=\frac14\left[I\otimes I+(b\cdot\sigma)\otimes I
+\sum_{a,b=1}^3M_{ab}\sigma_a\otimes\sigma_b^{\mathsf T}\right].
$$

(4.2)

参考边缘 $I/2$ 已编码在式中，完全正性是这个四阶矩阵的正性。
一般过程有 $3+9=12$ 个实仿射参数；不能把任意过程无损压成一个三实数态。
酉过程形成其中一个受限的三参数族。

<a id="thm-chirality"></a>

#### 定理 4.2（球等距族中的参考正性选出正向旋转）

若上述仿射更新对所有 $\|r\|\le1$ 满足

$$
\|b+Mr\|=\|r\|,
$$

则 $b=0$、$M\in O(3)$。在这个等距族内，下列条件等价：

$$
\text{充分内部参考输出非负}
\iff T\text{ 完全正}
\iff M\in SO(3)
\iff T=\operatorname{Ad}_U.
$$

**证明。**

取 $r=0$ 得 $b=0$，再由齐次性与实极化得 $M^{\mathsf T}M=I$。
对酉共轭，$U\sigma_iU^\dagger=v_i\cdot\sigma$；迹配对说明 $v_i$ 正交。
Pauli 交换关系给 $v_x\times v_y=v_z$，故 $\det M=1$。
反向任意 $R\in SO(3)$ 有轴角 $(n,\theta)$，

$$
U=\cos(\theta/2)I-i\sin(\theta/2)n\cdot\sigma
$$

经 Pauli 乘法给相应 Rodrigues 旋转，因而为酉共轭。
若 $\det M=-1$，可写 $M=R\operatorname{diag}(1,-1,1)$。
第二因子对应转置 $\Theta(X)=X^{\mathsf T}$，其

$$
J(\Theta)=\frac{\mathrm{Swap}}2
$$

在反对称方向特征值为 $-1/2$。
左接酉共轭只是对 $J$ 作酉合同，负方向仍在，故不是完全正映射。
定理 [3.2](#thm-cp) 完成其余等价。

∎

因此，各向同性与参考关联共同把三轴的球等距限制为旋转。
这个“取向”是相对于固定内部复参考的取向；同时共轭全部状态、效果和门的全表示变换，仍是另一层取向选择。
该定理不推出宇宙绝对左右手性。
它也不声称所有有噪 CP 过程都保定向：
$T=(\operatorname{Ad}_{\sigma_x}+\operatorname{Ad}_{\sigma_y}+\operatorname{Ad}_{\sigma_z})/3$
给 $M=-I_3/3$，完全正但行列式为负；它不属于等距族。

## 5. 可重建过程与可认证正性并不相同

固定参考的选取不是技术细节。过程信息可唯一反演，与一次正输出就强迫 CP，是两个不同性质。
忠实探针的过程层析及其条件成本已有标准研究；下列例子直接说明本轮需要的序性质。[10](#ref-faithful)

<a id="prop-schmidt"></a>

#### 命题 5.1（缺少 Schmidt 支撑可隐藏非正行为）

若参考输入的输入支撑为真子空间 $S\subsetneq\mathbb C^d$，则仅知道它输出正且参考边缘不变，不能认证 CP，甚至不能认证普通正性。

**证明。**

取单位 $s\in S$、$t\in S^\perp$，$P_\perp$ 为 $S^\perp$ 投影，定义

$$
T(X)=X+2\operatorname{Tr}(P_\perp X)(P_s-P_t).
$$

它复线性、伴随保持、保迹，并对全部支撑在 $S$ 的矩阵等于恒等映射，所以给定参考实验完全不变。
然而 $T(P_t)=2P_s-P_t$ 不是正矩阵。

∎

<a id="prop-mixed"></a>

#### 命题 5.2（混合而线性忠实的探针仍可能漏掉非 CP 更新）

对 $d\ge2$，令

$$
R=\frac{I_{d^2}+dP_{\Phi_d}}{d(d+1)}.
$$

映射 $T\mapsto(T\otimes\operatorname{id})(R)$ 对全部线性过程是单射，
但存在非 CP 的保迹 $T$，其该参考输出正且参考边缘不变。

**证明。**

记 $C_R(T)=(T\otimes\operatorname{id})(R)$，则

$$
C_R(T)=\frac{T(I)\otimes I+dJ(T)}{d(d+1)},
\qquad\operatorname{Tr}_R C_R(T)=\frac{T(I)}d.
$$

先由边缘恢复 $T(I)$，再恢复 $J(T)$，最后由式 (3.4) 恢复 $T$，故单射。
但对转置 $\Theta$，

$$
C_R(\Theta)=\frac{I+\mathrm{Swap}}{d(d+1)}\succeq0,
\qquad\operatorname{Tr}_Y C_R(\Theta)=\frac{I_d}d.
$$

$\Theta$ 的 Choi 矩阵在反对称方向为负，故不是 CP。

∎

满 Schmidt 纯探针的特殊性在于式 (3.1) 是*可逆合同*，同时保留正锥的两个方向。
任意可逆线性层析变换并无此性质。
特别在 $d=2$，上述 $R$ 甚至可写为六个乘积纯态的等权混合

$$
R=\frac16\sum_{n=\pm x,\pm y,\pm z}P_n\otimes\overline{P_n};
$$

由 Pauli 展开可直接检验。这说明“信息完备”不能替代“充分关联的正性检验”。

## 6. 内部仪器如何形成相干记录树

由式 (3.6) 定义

$$
V\psi=\sum_{j,\alpha}K_{j\alpha}\psi\otimes\lvert j,\alpha\rangle.
$$

(6.1)

直接计算得到 $V^\dagger V=I$，所以它是等距。
这里保留 $\alpha$ 为所选数学等距提升的内部索引；Kraus 分解本身不把它变成已经取得的实际记录。
若相应实现由来源供应，记录、索引及其载体都须在完整来源内部。
在一个已存在、容量足够且已初始化的内部 ready 槽上，可通过补全正交基把该等距实现为总载体上的酉作用。
这是数学完成；真实槽位、初始化与可调用程序须由项目的实际合同供应，不能由 $V$ 的写法免费取得。[2](#ref-v56)

<a id="prop-tree"></a>

#### 命题 6.1（有限树的质量归一与相干提升）

若每个实际记录节点 $h$ 的分支映射为满足式 (3.6) 的仪器，且它们与实际未归一读数的桥成立，
则任意有限深度的全部记录路径都有一致的非负质量，兄弟质量之和等于父质量。
保留全部 Kraus 索引时，路径 Kraus 乘积给一个整体等距。

**证明。**

令 $L_\gamma$ 为一条细化路径上 Kraus 矩阵按实际顺序的乘积。
从最后一层使用 $\sum K^\dagger K=I$，逐层消去可得

$$
\sum_{|\gamma|=n}L_\gamma^\dagger L_\gamma=I.
$$

因此，在按细路径标记的正交直和上，$V_n\psi=\bigoplus_{|\gamma|=n}L_\gamma\psi$ 满足 $V_n^\dagger V_n=I$。
各叶工作空间相同时，也可写成通常的 $\sum_\gamma L_\gamma\psi\otimes\lvert \gamma\rangle$。
若初接口为 $\rho_0$，数学细化质量为
$w_\gamma=\operatorname{Tr}(L_\gamma\rho_0L_\gamma^\dagger)$；正性、总和一及前缀求和均由上述完备式得到。
实际仪器桥供应粗记录路径 $h$ 的质量 $p_h=\sum_{\gamma\mapsto h}w_\gamma$。
只有来源另给 $\alpha$ 的实际细记录合同，才将相应 $w_\gamma$ 也称为实际细路径质量。
零质量的实际路径保留为零，不定义其归一条件态。

∎

效果本身不决定未来更新。例如对计算基投影 $P_j$，

$$
T_j(X)=P_jXP_j,\qquad S_j(X)=\operatorname{Tr}(P_jX)P_0
$$

有相同的结果概率，却有不同的后继态。
因此只有二元概率及其归一化，还没有指定一个量子仪器。
相干记录的正交标签也不意味着拉回原工作空间的所有效果彼此对易。
无限门词另需完成空间、嵌入和极限拓扑；有限树归纳不能自动给无限相干极限。[2](#ref-v56)

## 7. 实际记录增长的关系条件

上一节的仪器树需要实际读出桥。本节和下一节研究这条桥何时能够成立、如何递归保持。
所用概率空间描述同一固定来源的实际记录律；它不是另造一族实际本体。

#### 定义 7.1（实际关系残差与安全记录域）

固定同一实际概率空间 $(\Xi,\mathcal F,\mathbb P)$、有限维效果空间及有限或可数未来请求。
请求 $a$ 的声明效果为 $E_a$，同源实际未来核为 $k_a:\Xi\to[0,1]$。
这些核表示来源声明的各未来请求响应，不表示不相容测量都已同时执行。
对 $\sum_a c_aE_a=0$，定义残差 $r_c=\sum_a c_ak_a$，
令 $\mathcal R$ 为这些残差在 $L^2$ 中的闭线性张成。
记录信息域 $\mathcal G$ 的条件读数为 $p_\mathcal G(E_a)=\mathbb E[k_a\mid\mathcal G]$。
称它 RC 安全，如果全部效果关系在这些条件读数上仍成立。

<a id="thm-safe"></a>

#### 定理 7.2（条件正交、联合与递增闭包）

$\mathcal G$ 安全，当且仅当

$$
\mathbb E[r\mid\mathcal G]=0\quad(r\in\mathcal R),
$$

亦即 $\mathbb E[rf]=0$ 对所有有界 $\mathcal G$-可测 $f$ 成立。
两个记录域的联合安全，当且仅当

$$
\mathbb E[rfg]=0\quad
(r\in\mathcal R,\ f\in L^\infty(\mathcal G),\ g\in L^\infty(\mathcal H)).
$$

(7.1)

一条按包含递增的安全记录域链，其生成信息域仍安全。

**证明。**

条件期望的线性性给生成残差的第一判据，其 $L^2$ 连续性推广到 $\mathcal R$。
条件期望的定义和简单函数逼近给有界测试函数判据。
联合必要性显然；反向取 $f=1_A,g=1_B$，得到符号测度
$C\mapsto\mathbb E[r1_C]$ 在生成联合信息域的交集 $A\cap B$ 上为零。
单调类论证将它推广到整个联合域。
对递增链，其并是代数，每个残差在该代数的所有事件上积分为零，
再用同一单调类论证即可。

∎

可数请求与有限效果维数允许选择可数个关系生成元，从而使用共同满测集；
不对不可数实系数分别取零集交。
安全性向更粗信息域传导，也对*已逐步验证安全*的递增链封闭，
但两个分别安全的记录域不一定联合安全。
例如独立公平 $\pm1$ 位 $A,B$ 及残差 $r=AB$，有

$$
\mathbb E[r\mid A]=\mathbb E[r\mid B]=0,
\qquad\mathbb E[r\mid A,B]=AB.
$$

这与 RRO 的来源特定联合历史反例方向一致，不能仅因两个记录各自合法就合并。[4](#ref-rro)

若下一有限记录 $Y$ 的实际似然为 $\kappa_y=\mathbb P(Y=y\mid\mathcal H)$，
$\mathcal H$ 包含残差与当前 $\mathcal G$，则

$$
\mathbb E[r\mid\mathcal G,Y=y]
=\frac{\mathbb E[r\kappa_y\mid\mathcal G]}{\mathbb E[\kappa_y\mid\mathcal G]}
$$

(7.2)

在分母正处成立：将 $r1_{\{Y=y\}}$ 先对 $\mathcal H$ 条件化即可证明。
故新增记录安全恰要求各分子的零条件均值。
这表明新增记录不能暴露原先仅被平均抵消的关系残差。
“给定隐藏坐标后条件独立”不足以替代该条件；上述 $A,B$ 在给定 $(A,B)$ 后甚至都是确定的，联合仍失败。

## 8. 双重闭包怎样推出共同线性更新

本节给一条有限而完全显式的来源条件。有限预测坐标存在是前件，
不把原生五个记录标签擅自当成所有量子过程的自治状态。
不同节点的坐标与核允许不同，控制只依赖已取得的过去。

#### 定义 8.1（节点的形式标签、预测核与单位锚）

在记录节点 $h$，给定有限内部预测坐标 $X_h$、实际条件概率行向量 $\mu_h$，
同一父节点的各结果使用共同输出矩阵接口，其维数可以随父节点变化；
以及形式实标签空间 $L_h$ 与满射

$$
e_h:L_h\twoheadrightarrow V_h=\operatorname{Herm}_{d_h},\qquad
k_h:L_h\twoheadrightarrow K_h\subseteq\mathbb R^{X_h}.
$$

原始请求的核在 $[0,1]^{X_h}$，线性组合可取任意实值。
定义 $R_h=k_h(\ker e_h)\subseteq K_h$，安全性为 $\mu_hR_h=0$。
供应单位标签 $\iota_h$，满足

$$
e_h(\iota_h)=I_h,\qquad k_h(\iota_h)=\mathbf1_{X_h}.
$$

(8.1)

每个节点的结果标签取有限集；实际结果–后继核为非负矩阵 $M_{h,y}$，并保留全部结果，使

$$
\sum_yM_{h,y}\mathbf1_{X_{hy}}=\mathbf1_{X_h}.
$$

(8.2)

实际未归一后继是 $u_{hy}=\mu_hM_{h,y}$，质量 $p(y\mid h)=u_{hy}\mathbf1$；
仅在质量正时取 $\mu_{hy}=u_{hy}/p(y\mid h)$。

<a id="thm-double"></a>

#### 定理 8.2（关系闭包与预测闭包的不同作用）

若

$$
\boxed{M_{h,y}R_{hy}\subseteq R_h,}
$$

(R)

则任何安全父权重的全部正质量后继安全。
若另有

$$
\boxed{M_{h,y}K_{hy}\subseteq K_h,}
$$

(K)

则当前全部预测读数相同的两个权重，对结果 $y$ 后全部未归一预测读数仍相同。
两条件共同给良定义的实线性商映射

$$
\overline M_{h,y}:K_{hy}/R_{hy}\longrightarrow K_h/R_h,
\qquad[g]\longmapsto[M_{h,y}g].
$$

(8.3)

**证明。**

对 $r'\in R_{hy}$，由 (R) 得 $\mu_hM_{h,y}r'=0$，正质量时归一即可。
零质量时非负行向量 $\mu_hM_{h,y}$ 为零，不需条件除法。
若 $(\mu-\nu)K_h=0$，由 (K) 得 $(\mu-\nu)M_{h,y}K_{hy}=0$。
单位核也在 $K_{hy}$，故结果质量相同，正质量后的归一读数也相同。
(K) 保证商映射的像在正确空间，(R) 保证它不依赖代表选择。

∎

只给 (R) 不够预测自治。例如当前只读单位核 $K=\operatorname{span}\{\mathbf1\}$、$R=0$，
下一切口加入一个非常值核，取恒等转移；关系闭包平凡成立，当前读数却不能决定新核读数。

<a id="prop-necessary"></a>

#### 命题 8.3（关系闭包何时也是必要条件）

令 $C_h=\{u\ge0:uR_h=0\}$。
一个结果核把整个安全接口域送到后继安全域，当且仅当

$$
M_yR'\subseteq(\operatorname{span} C_h)^\perp.
$$

若存在严格正的安全概率 $\pi>0$，则 $\operatorname{span} C_h=R_h^\perp$，上述条件恰为 (R)。

**证明。**

第一句只是将 $uM_yr'=0$ 对所有 $u\in C_h,r'\in R'$ 重写。
对 $v\in R_h^\perp$，足够小的 $\epsilon>0$ 使 $\pi\pm\epsilon v\ge0$，两者仍消去 $R_h$。
它们的差为 $2\epsilon v$，故 $R_h^\perp\subseteq\operatorname{span} C_h$；反向包含显然。

∎

唯一实际来源只需充分性；“整个安全域”是接口鲁棒性的数学量词。
不能为取得严格正性而删去原来源的零支撑坐标。

<a id="thm-quotient"></a>

#### 定理 8.4（忠实效果商、实际更新桥与归一化）

自然满射

$$
Q_h:V_h\longrightarrow K_h/R_h,\qquad Q_h(e_h\ell)=[k_h\ell]
$$

满足 $\ker Q_h=e_h(\ker k_h)$。
因此，若明确要求

$$
\boxed{\ker k_h\subseteq\ker e_h,}
$$

(F)

则 $Q_h$ 为实线性同构。
在父子节点均满足 (F)、并有 (R)、(K) 时，存在唯一 Heisenberg 更新

$$
\mathcal I_{h,y}^*=Q_h^{-1}\overline M_{h,y}Q_{hy}:V_{hy}\to V_h.
$$

(8.4)

对每个实际安全权重，定义 $p_\mu(E)=\mu k_h(\ell)$，其中 $e_h\ell=E$。
则它良定义，而且

$$
\boxed{p_{\mu M_{h,y}}(E')=p_\mu(\mathcal I_{h,y}^*E').}
$$

(8.5)

单位锚与完整实际核归一进一步给

$$
\sum_y\mathcal I_{h,y}^*(I_{hy})=I_h.
$$

(8.6)

**证明。**

若 $e\ell=e\ell'$，则核差属于 $k(\ker e)=R$，所以 $Q$ 良定义；由 $k$ 满射可知它满射。
若 $Q(e\ell)=0$，则 $k\ell=k\ell_0$ 对某个 $\ell_0\in\ker e$ 成立，
故 $e\ell=e(\ell-\ell_0)\in e(\ker k)$。
反向 $k\ell=0$ 显然给 $Q(e\ell)=0$，从而得到核公式与 (F) 的等价。

定理 [8.2](#thm-double) 给 $\overline M$，故式 (8.4) 良定义。
安全 $\mu$ 在商上定义 $\bar\mu([g])=\mu g$；于是 $p_\mu=\bar\mu Q_h$。
从定义直接得到

$$
p_{\mu M}(E')=\bar\mu\overline M Q_{hy}(E')
=\bar\mu Q_h\mathcal I^*(E')=p_\mu(\mathcal I^*E').
$$

最后，$Q_h(I_h)=[\mathbf1]$，而

$$
Q_h\!\left(\sum_y\mathcal I_{h,y}^*I_{hy}\right)
=\sum_y[M_{h,y}\mathbf1]=[\mathbf1]=Q_h(I_h).
$$

$Q_h$ 单射给式 (8.6)。

∎

由实迹配对，每个 $p_\mu$ 给唯一 Hermitian 矩阵 $W_\mu$。
令 $T_{h,y}$ 为 $\mathcal I_{h,y}^*$ 的迹对偶，则

$$
\boxed{W_{\mu M_{h,y}}=T_{h,y}(W_\mu),\qquad
\sum_y\operatorname{Tr} T_{h,y}(W)=\operatorname{Tr} W.}
$$

(8.7)

实线性自伴映射通过 $T(A+iB)=T(A)+iT(B)$ 唯一延拓为复线性、伴随保持映射。
这给共同线性过程和实际更新桥，无需再预设实际态族的仿射性。
但它尚未给正性或 CP；实际已可达态上的正输出，也不能替代整个正锥上的性质。
当同一更新满足 §3 的实际参考相容与联合正性时，定理 [3.2](#thm-cp) 才将它升级为量子仪器。
式 (8.6) 已供应总保迹，所以此时参考边缘守恒是推论，而不需重复作为独立公理。

(F) 也是独立条件。若预测坐标只有一点，且 $k(\ell)=p_\Omega(e\ell)$，
则 $K=\mathbb R\mathbf1$、$R=0$，$Q(E)=p_\Omega(E)$ 一般有很大的核。
固定响应本身可以被层析，并不意味着整个效果空间已被预测接口忠实区分。
没有 (F) 时，只能先得到实关系商 $V/e(\ker k)$；
连“商算子系统”的正锥与矩阵层结构也需要另给，不能从线性商名字中取得。

项目 V37 已证明其五个概率可以重建 qubit 态，却不能用同一个对全部 qubit 态成立的五标签自治随机核承载非平凡酉共轭。
本节没有推翻该阻碍：$X_h$ 不能不经证明就取成原五标签，(R)、(K)、(F) 也不是静态信息完备的自动结果。[6](#ref-v37)

## 9. 递归关系误差的收缩与累计

#### 定义 9.1（归一关系残差缺陷）

对概率权重 $\mu$，令

$$
d_h(\mu)=\sup\{\,|\mu r|:r\in R_h,\ \|r\|_\infty\le1\,\}.
$$

它在 $[0,1]$ 内，且为零当且仅当接口安全。
这是实际读出违反关系的缺陷，不将带符号误差误称为一个正概率态或酉门。

<a id="thm-martingale"></a>

#### 定理 9.2（按真实分支质量加权的平均收缩）

若实际核满足 (R)，则

$$
\boxed{\sum_y p(y\mid h)d_{hy}(\mu_{hy})\le d_h(\mu_h).}
$$

(9.1)

故沿同一实际记录过滤，$D_t=d_{H_t}(\mu_{H_t})$ 是非负有界超鞅。

**证明。**

各有限维闭单位球紧，分支可选择 $r_y\in R_{hy}$、$\|r_y\|_\infty\le1$，
并取合适符号使 $\mu_{hy}r_y=d_{hy}(\mu_{hy})$；零质量分支任取零。
令 $g=\sum_yM_{h,y}r_y$。(R) 给 $g\in R_h$，非负核及式 (8.2) 给

$$
|g(x)|\le\sum_{y,x'}M_{h,y}(x,x')|r_y(x')|\le1.
$$

因此

$$
\sum_yp(y\mid h)d_{hy}(\mu_{hy})=\mu_hg\le d_h(\mu_h).
$$

条件化于当前实际节点即为超鞅不等式。

∎

逐分支单调不成立。取 $R=\operatorname{span}\{(1,-1,0)\}$，
$M_A=\operatorname{diag}(1,1,0)$、$M_B=\operatorname{diag}(0,0,1)$，二者都保持 $R$。
若 $\mu=(\epsilon,0,1-\epsilon)$，则 $d(\mu)=\epsilon$；
概率仅 $\epsilon$ 的分支 $A$ 归一后为 $(1,0,0)$，缺陷变为 $1$。
真实加权平均仍为 $\epsilon$。
这给“误差稳定”一个准确含义，也保留罕见条件化放大的实际可能。

<a id="thm-tv"></a>

#### 定理 9.3（近似实际核的加法预算与全过程概率界）

固定实际初始记录节点，故 $D_0$ 为确定量；以下 $\delta_t\ge0$ 为确定预算。
设实际核 $M_{h,y}$ 与保持 (R) 的参考核 $\bar M_{h,y}$ 都非负且总和归一。
若每层所有节点与来源行满足完整联合坐标 $(y,x')$ 上的界

$$
\frac12\sum_{y,x'}|M_{h,y}(x,x')-\bar M_{h,y}(x,x')|\le\delta_t,
$$

(9.2)

则

$$
\mathbb E[D_{t+1}\mid\mathcal G_t]\le D_t+2\delta_t,
\qquad
\mathbb E D_n\le D_0+2\sum_{t<n}\delta_t.
$$

(9.3)

对任意 $u>0$，还有

$$
\boxed{\mathbb P\!\left(\max_{0\le t\le n}D_t\ge u\right)
\le\min\!\left\{1,\frac{D_0+2\sum_{t<n}\delta_t}{u}\right\}.}
$$

(9.4)

**证明。**

沿上一定理选择实际分支的 $r_y$。参考回拉 $\bar g=\sum_y\bar M_{h,y}r_y$ 属于 $R_h$，范数至多一。
由式 (9.2)，实际回拉与参考回拉在任一行的差绝对值至多 $2\delta_t$。
以实际 $\mu_h$ 加权得式 (9.3) 的一步界，迭代条件期望得第二界。
在有限时域 $0\le t\le n$，置

$$
Z_t=D_t+2\sum_{s=t}^{n-1}\delta_s.
$$

它是非负超鞅。令 $\tau$ 为 $Z_t$ 首次达到 $u$ 的时刻与 $n$ 的较小者，则

$$
\mathbb EZ_\tau=\mathbb EZ_0+
\sum_{t<n}\mathbb E\!\left[1_{\{\tau>t\}}(Z_{t+1}-Z_t)\right]\le\mathbb EZ_0.
$$

于是 $u\,\mathbb P(\max Z_t\ge u)\le\mathbb E Z_0$。
由 $Z_t\ge D_t$ 得式 (9.4)。

∎

这里 $\delta_t$ 衡量*实际结果与后继预测坐标的联合核*。
它不能单从 $\|U-\widetilde U\|_{\mathrm{op}}$ 推得；Quantum IV §205 的读出反例正说明还需实际报告桥。[5](#ref-qiv)
若 $\sum_t\delta_t<\infty$，总预算有限；这不自动给 $D_t\to0$。
例如精确恒等核与固定残差空间允许 $D_t$ 恒等于一个正数。
要证明误差被持续消除，必须另给严格收缩、可辨识校准或反馈条件。

## 10. 有限参考检测怎样修复正性与归一化

前面的稠密方向判据是精确数学条件。实际有限覆盖只给有界负谱，不能未经证明称为精确 CP。
本节给显式修复及响应误差预算，所有结果标签保留。

<a id="thm-net"></a>

#### 定理 10.1（有限方向覆盖的分支负谱界）

令 $n=md$。对每个联合分支候选 $C_j=C_j^\dagger$，记已标定的 $t_j=\operatorname{Tr} C_j\ge0$。
假定实际有限探针为 $cP_\phi$，$c>0$；对任意单位方向 $v$，某个探针满足
$|\langle v,\phi\rangle|^2\ge1-\varepsilon$，且 $n\varepsilon<1$。
若读数非负性误差与关系拟合误差合计保证

$$
\operatorname{Tr}(C_jcP_\phi)\ge-\zeta_j,
$$

则

$$
\boxed{C_j\succeq-a_j^\psi I_n,\qquad
a_j^\psi=\frac{\zeta_j/c+\varepsilon t_j}{1-n\varepsilon}.}
$$

(10.1)

**证明。**

设最小、最大特征值分别为 $u,v$。由迹和 $n-1$ 个特征值至少为 $u$，
$v\le t_j-(n-1)u$。
取最小特征向量附近的探针，写实际偏离权重为 $\delta\le\varepsilon$，则

$$
-\zeta_j/c\le\langle\phi,C_j\phi\rangle
\le(1-\delta)u+\delta v
\le u+\varepsilon(t_j-nu).
$$

最后一步使用 $t_j-nu\ge0$。移项即得下界。

∎

令 $s=\lambda_{\min}(\rho_R)>0$。由
$\|A^{-1}\|_{\mathrm{op}}^2=1/(ds)$，

$$
J_j=(I\otimes A^{-1})C_j(I\otimes A^{-\dagger})
\succeq-a_jI_n,\qquad a_j=\frac{a_j^\psi}{ds}.
$$

(10.2)

最小 Schmidt 权重明确进入误差预算；弱关联方向导致条件成本。
推导没有除以分支质量，因而没有隐藏的稀有分支 $1/t_j$ 放大。

<a id="thm-repair"></a>

#### 定理 10.2（精确参考归一化下的 CP 仪器修复）

设 $J_j\succeq-a_jI_n$、$a_j\ge0$，且
$\sum_j\operatorname{Tr}_YJ_j=I_d/d$。
置 $a=\sum_ja_j$、$\beta=md\,a$，则

$$
\boxed{\widetilde J_j=\frac{J_j+a_jI_n}{1+\beta}}
$$

(10.3)

为一组 CP、总保迹仪器的归一 Choi 矩阵。
定义保留全部记录的旗标映射

$$
\mathcal T(X)=\sum_j\lvert j\rangle\langle j\rvert\otimes T_j(X),\qquad
\widetilde{\mathcal T}(X)=\sum_j\lvert j\rangle\langle j\rvert\otimes\widetilde T_j(X).
$$

对任意额外内部参考、任意归一正输入 $\sigma$ 与联合效果 $0\le F\le I$，

$$
\boxed{\left|\operatorname{Tr} F[(\mathcal T-\widetilde{\mathcal T})\otimes\operatorname{id}](\sigma)\right|\le\beta.}
$$

(10.4)

**证明。**

式 (10.3) 逐项非负，参考边缘之和为

$$
\frac{I_d/d+m(\sum_ja_j)I_d}{1+md\sum_ja_j}=I_d/d.
$$

令 $D(X)=\operatorname{Tr}(X)I_m/m$，其归一 Choi 为 $I_n/n$，故
$\widetilde T_j=(T_j+na_jD)/(1+\beta)$。
当 $a>0$，令 $\mathcal D_{\mathrm{flag}}(X)=\sum_j(a_j/a)\lvert j\rangle\langle j\rvert\otimes D(X)$。
于是

$$
\mathcal T-\widetilde{\mathcal T}
=\beta(\widetilde{\mathcal T}-\mathcal D_{\mathrm{flag}}).
$$

右侧括号内是两个合法通道之差。任意参考下两输出均为密度矩阵，
对一个效果的读数差至多一，得到式 (10.4)。$a=0$ 时不需修复。

∎

若 $\sum_jt_j=1$、各分支共享 $c,\varepsilon$，结合式 (10.1)–(10.2) 得

$$
\boxed{\beta=\frac{m}{s}\,
\frac{\sum_j\zeta_j/c+\varepsilon}{1-md\varepsilon}.}
$$

(10.5)

总迹项只出现一次，因为保留的是完整结果族的总质量。
若未标定 $\sum_jt_j=1$，必须保留 $\varepsilon\sum_jt_j$，不能自行替换为 $\varepsilon$。

<a id="thm-approxnorm"></a>

#### 定理 10.3（同时修复近似参考边缘）

允许参考归一化误差

$$
\Delta=\sum_j\operatorname{Tr}_YJ_j-I_d/d,\qquad\kappa=\|\Delta\|_{\mathrm{op}}.
$$

任选固定 $w_j\ge0$、$\sum_jw_j=1$，置

$$
J'_j=J_j-w_j\frac{I_m}{m}\otimes\Delta,\qquad
a'_j=a_j+\frac{w_j\kappa}{m},\qquad
\beta'=md\sum_ja_j+d\kappa.
$$

则 $\widetilde J_j=(J'_j+a'_jI_n)/(1+\beta')$ 是 CP、总保迹仪器，且

$$
\boxed{\left|\operatorname{Tr} F[(\mathcal T-\widetilde{\mathcal T})\otimes\operatorname{id}](\sigma)\right|
\le md\sum_ja_j+2d\kappa.}
$$

(10.6)

该界不要求原候选 $\mathcal T$ 保迹或完全正。

**证明。**

边缘校正给 $\sum_j\operatorname{Tr}_YJ'_j=I_d/d$；又
$\|(I_m/m)\otimes\Delta\|_{\mathrm{op}}=\kappa/m$，故 $J'_j\succeq-a'_jI$。
定理 [10.2](#thm-repair) 给修复与从 $\mathcal T'$ 到 $\widetilde{\mathcal T}$ 的效果误差 $\beta'$。

由式 (3.4)，原映射到边缘校正映射的差为

$$
(T_j-T'_j)(X)=w_jd\operatorname{Tr}(\Delta X^{\mathsf T})\frac{I_m}{m}.
$$

令 $B=d\Delta^{\mathsf T}$、$\tau=I_m/m$。
对任意输入–参考态 $\sigma$，公共替换误差是 $\tau\otimes R_\sigma$，其中
$R_\sigma=\operatorname{Tr}_X[(B\otimes I)\sigma]$ 为 Hermitian。
对任意 Hermitian $H$、$\|H\|_{\mathrm{op}}\le1$，

$$
|\operatorname{Tr}(HR_\sigma)|=|\operatorname{Tr}[(B\otimes H)\sigma]|\le d\kappa.
$$

迹范数对偶给 $\|R_\sigma\|_1\le d\kappa$。
附加概率旗标 $\sum_jw_j\lvert j\rangle\langle j\rvert$ 不改变该界，所以原映射到校正映射的效果误差至多 $d\kappa$。
这段差一般不无迹，不能把该界除以二。
两段相加得 $d\kappa+\beta'=md\sum a_j+2d\kappa$。

∎

若直接测得纯参考输出的边缘误差

$$
\xi=\left\|\sum_j\operatorname{Tr}_YC_j-\rho_R\right\|_{\mathrm{op}},
$$

则 $\kappa\le\xi/(ds)$，式 (10.6) 化为

$$
\boxed{\text{任意额外参考下的联合效果误差}
\le\frac{m\sum_ja_j^\psi+2\xi}{s}.}
$$

(10.7)

若总迹未独立标定，有 $|\sum_jt_j-1|\le d\xi$，因此式 (10.1) 求和时可用 $1+d\xi$ 上界总迹。
修复是一个可审查的数学仪器，不是声称实际设备已经自动更改；实际新读数与拟合过程之间的残差仍需单列。

### 10.1 误差沿过程复合时不能偷用尚未证明的收缩

令 $\|L\|_\diamond$ 表示允许任意有限参考后的稳定迹范数；合法通道范数为一。
定理 [10.2](#thm-repair) 的精确归一情形给
$\mathcal T_k=(1+\beta_k)\mathcal S_k-\beta_k\mathcal D_k$，其中后两者为通道。
因此 $\|\mathcal T_k\|_\diamond\le1+2\beta_k$，
$\|\mathcal T_k-\mathcal S_k\|_\diamond\le2\beta_k$。
按乘积差的望远镜展开并用次乘性，得到

$$
\frac12\|\mathcal T_L\cdots\mathcal T_1-\mathcal S_L\cdots\mathcal S_1\|_\diamond
\le\frac12\left[\prod_{k=1}^L(1+2\beta_k)-1\right].
$$

(10.8)

若每个实际与比较过程都已知 CPTP，才可把两侧中间因子范数都置为一而得到加法界 $\sum_k\beta_k$。
这与 §9 的实际核 TV 预算属于不同层次，不能互相替换。

在 V37 编码的 $N$ 原子输入与 $N$ 原子输出上，联合维数为 $4^N$。
若使用其原秩一效果 $E_3=2\nu P_z$ 的 $2N$ 重积，实际增益为 $c=(2\nu)^{2N}$；
式 (10.1) 的有限覆盖条件为 $\varepsilon<4^{-N}$。
最大纠缠参考有 $s=2^{-N}$。这些因子揭示了覆盖与条件成本，不能将“一个参考态”误说成一次免费读数或维数无关的认证。

## 11. 普适安全记录的一个可解分类

以下结果说明关系保持怎样产生经典记录结构，但不宣称所有实际记录都属于该简化情况。
固定有限预测坐标 $X$，记录只读而不改变它，故 $M_y=D_{\kappa_y}=\operatorname{diag}(\kappa_y)$。

<a id="thm-algebra"></a>

#### 定理 11.1（不扰动记录的关系保持代数）

给定残差空间 $R\subseteq\mathbb R^X$，令

$$
\mathfrak D_R=\{a\in\mathbb R^X:D_aR\subseteq R\}.
$$

它是含单位的实交换代数。
若 $P_R$ 为普通欧氏正交投影，则

$$
\boxed{a\in\mathfrak D_R
\iff(a(x)-a(z))(P_R)_{xz}=0\quad(x,z\in X).}
$$

(11.1)

因此，$\mathfrak D_R$ 恰由在图的每个连通分量上取常数的函数构成，图的边由 $(P_R)_{xz}\ne0$ 定义。

**证明。**

单位、线性组合和乘积都保持 $R$，故构成代数。
$D_a$ 自伴；若它保持 $R$，也保持 $R^\perp$，所以与 $P_R$ 对易。
反向，对易当然保持 $R$。逐项写对易式便得 (11.1)，沿边相等即在每个连通分量上常值。

∎

存在严格正安全权重时，命题 [8.3](#prop-necessary) 使该代数精确分类*对整个安全接口域*都安全的不扰动似然。
若还要求预测自治，则同时保持 $K$，图取 $P_R$ 与 $P_K$ 非零边的并。
各分量标签给这一合同内的最细确定性安全划分。
实际单一来源上偶然安全的记录可以更多，彼此联合仍可能失败；
因此此处的普适划分不与 RRO 的“实际安全域未必存在最大成员”矛盾。
多条随机记录的联合似然仍须保持该空间；只有边缘似然合法，不自动保证其联合合法。

## 12. 可替换的公理组、所得结论与剩余问题

<a id="thm-total"></a>

#### 定理 12.1（固定来源的过程重构总定理）

对同一个固定来源的每个相关有限记录节点，假设：

1. 已给复矩阵效果接口、相容内部复合和单位锚；没有预设更新的 CP 或酉性。
2. 初始实际响应满足引理 [2.2](#lem-state) 的 RC、效果张成、单位读数一和充分秩一方向非负性，
或明确继承上一轮已证的正初态 $\rho_0$。
3. 实际来源供应 §8 的预测核与完整结果核，初接口安全，并满足 (F)、(K)、(R)。
4. 在需要认证的输入接口上，实际可用一个已知满 Schmidt 秩纯内部参考；
所诱导同一更新在联合效果上满足式 (3.2) 的局部参考相容。
5. 每个参考输出分支的实际读数满足联合 RC、实效果张成及充分秩一方向非负性。

则该来源的有限接口具有共同复线性、完全正、总保迹的仪器表示；
其实际条件更新、记录概率与有限树质量递归均由该表示给出。
若某个未条件化过程在充分参考上还保持联合纯性，且输入输出等维，则该过程为酉共轭。
若仅有有限误差版前件，则有 §9–10 所列的实际关系预算和过程修复预算。

**证明。**

初始条件与引理 [2.2](#lem-state) 先给正迹一 $\rho_0$。
定理 [8.2](#thm-double) 归纳给全部正质量历史的 RC。
定理 [8.4](#thm-quotient) 给共同线性更新、实际桥和总迹保持。
引理 [2.2](#lem-state) 给联合参考矩阵的正性；实际参考相容把它识别为同一映射的 $C_A(T_j)$。
定理 [3.2](#thm-cp) 给各分支 CP，推论 [3.4](#cor-instrument) 给仪器；
CP 将该正初态传导为各分支的正矩阵，实际桥与命题 [6.1](#prop-tree) 给有限递归。
定理 [4.1](#thm-unitary) 给纯过程的酉结论。各误差结论已分别在其完整前件下证明。

∎

> **编校注（Markdown 整理者，定理量词）：** 本定理开头“每个相关有限记录节点”的量词统摄各项前件；第 4–5 项须在所需认证的各输入接口及其每个分支上供应同一更新的实际参考相容和联合正性。只检查一个节点或一份分支输出，不能推出其它历史上的过程结论。

这是一组可以替换部分“直接假定量子仪器”的关系前件，尚未证明它在逻辑上最小。
它的价值在于每个量子原则对应一个明确的数学约束，而且缺少约束时有反例定位失败。

| 要解释的性质 | 本文给出的关系条件 | 不能自动替代它的条件 |
| --- | --- | --- |
| 共同线性更新 | 忠实效果商、预测及残差双闭包 | 单个固定态可层析、档案只增不减 |
| 普通态正性 | 联合 RC、完整方向非负性 | 有限信息完备、积方向非负 |
| 完全正性 | 同一局部映射作用于满 Schmidt 纯参考且输出正 | 单系统正性、混合探针线性忠实 |
| 过程归一化 | 全部参考边缘守恒；或忠实单位商上的完整核归一 | 一份输出的总迹为一 |
| 酉性 | 保迹、充分参考的未条件化联合输出纯、等维 | 单分支纯、重置后纯、完整本体纯 |
| 历史相容 | 实际残差后向闭包及记录来源桥 | 名义 CP、分别安全的任意记录联合 |
| 误差稳定 | 真实权重平均收缩与实际核预算 | 每个分支误差必减、算子误差自动控制报告 |

平方律在这条链中的位置也更清楚：正关系具有矩阵表示后，纯态 $P_\psi$ 对秩一效果 $P_\phi$ 的配对为

$$
\operatorname{Tr}(P_\psi P_\phi)=|\langle\phi,\psi\rangle|^2.
$$

复合与递归进一步要求相同的平方配对对参考和记录一致延续。
这解释了已有复内积关系中平方为何出现，但复结构、相容复合和实际方向可取得性仍是承重前件。
“加法与乘法只有两种”或“本体唯一”本身不选择这些前件。

本轮可以进一步聚焦的项目问题，是在原生控制与记录合同中建立 (F)、(K)、(R) 和式 (3.2) 的实际桥，
或者找出它们在哪些历史上失败；再给固定满 Schmidt 参考的具体取得权限与误差预算。
若这些桥已建立，就能把 V56 所用的 Kraus 完备输入放到更上游的关系结构中解释。
如果某个桥失败，正确结论是该接口需要保留更多预测关系或历史，而非将失败读数删去再归一化。
对于唯一完整本体，所有这些扩大后的关系、记录和参考仍在同一条内生门序列里。

## 固定来源、文献与阅读边界

> **编校注（Markdown 整理者，来源报告归属）：** 下列各条“本轮读取”“再次读取”“复用已读”等阅读和取得描述均保留为原作者的历史报告；它们不自动代表本 Markdown 整理者的阅读行为。本文明确限定 Choi 原出版文献为元数据核对、原出版全文访问受限，不作原文全文已读之声明。

<a id="ref-head"></a>

### [1]

[项目固定提交](https://github.com/the-omega-institute/trureturing/commit/768fe1b81b658f31b1213f9b25cc953baa679ba8)
及 [相对 v59 的固定比较](https://github.com/the-omega-institute/trureturing/compare/8558e845c6b6e49b11087733242e5ae386483392...768fe1b81b658f31b1213f9b25cc953baa679ba8)。
本轮仅一次活动 HEAD 请求；后续取得均按固定对象。来源树、完整 diff 与字节身份留有审计记录。

<a id="ref-v56"></a>

### [2]

[V56：普遍内部二元切口、算子三轴纯性与内生递归](https://github.com/the-omega-institute/trureturing/blob/768fe1b81b658f31b1213f9b25cc953baa679ba8/docs/develop/theory/AURIC_UNIVERSAL_INTERNAL_BINARY_CUTS_OPERATOR_THREE_AXIS_PURITY_AND_ENDOGENOUS_RECURSION_V56.md)。
本轮新入库；连续阅读 1–70、182–358、582–618、704–774、819–906 的相关段落。
使用 §§1、3–4、7.1、9.2、11–12 的明确前件与边界；原稿旧 HEAD 失败报告不属于本轮取得事实。

<a id="ref-unordered"></a>

### [3]

[无序相容原子与量子表示](https://github.com/the-omega-institute/trureturing/blob/768fe1b81b658f31b1213f9b25cc953baa679ba8/docs/develop/theory/AURIC_UNORDERED_COMPATIBLE_ATOM_AND_QUANTUM_REPRESENTATION_THEORY.md)，§7.1。
本轮连续阅读 370–405；仿射扩张、任意未触及参考及转置反例为已有内容。

<a id="ref-rro"></a>

### [4]

[RRO：原生终端认证](https://github.com/the-omega-institute/trureturing/blob/768fe1b81b658f31b1213f9b25cc953baa679ba8/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)，特别 §§56–61。
本轮与 v59 字节相同，复用已读固定来源的实际历史联合边界，不记为本轮新增。

<a id="ref-qiv"></a>

### [5]

[Quantum Continuation IV](https://github.com/the-omega-institute/trureturing/blob/768fe1b81b658f31b1213f9b25cc953baa679ba8/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md)，定理 196.1、§205。
本轮字节未变；使用实际 RC/秩一方向正性及实际读出与算子误差分离的既有结论。

<a id="ref-v37"></a>

### [6]

[V37：二元关系、酉表示与黄金门通用性](https://github.com/the-omega-institute/trureturing/blob/768fe1b81b658f31b1213f9b25cc953baa679ba8/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)。
使用 §3 的固定编码与读口增益、§§12–15 的五标签随机更新边界；本轮相关段落再次有界读取，文件本轮未变。

<a id="ref-kbonacci"></a>

### [7]

[K-bonacci：端点层析与秩一关系边界](https://github.com/the-omega-institute/trureturing/blob/768fe1b81b658f31b1213f9b25cc953baa679ba8/docs/develop/theory/KBONACCI_ENDPOINT_TOMOGRAPHY_AND_RANK_ONE_RELATION_BOUNDARIES.md)，新增 §10。
新增段 690–895 连续读取，连同 §5.2、定义 7.1 和定义 8.1 的合同前件；
§10 复用的 §§7–9 旧下界证明未全部重审。
本文不将该精确资源最优移植为量子校准成本。

<a id="ref-choi"></a>

### [8]

Man-Duen Choi.
[Completely positive linear maps on complex matrices](https://doi.org/10.1016/0024-3795(75)90075-0).
*Linear Algebra and its Applications* 10(3), 285–290 (1975)。
本轮核对原出版元数据，原出版全文访问受限；证明依据下条作者文本与本文展开，不声称读过原文全文。

<a id="ref-watrous"></a>

### [9]

John Watrous.
[The Theory of Quantum Information, Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)。
本轮读取作者托管文本中定理 2.22 的 CP/Choi/Kraus 证明、定理 2.26 的保迹边缘证明、推论 2.27 及等距通道段。
本文采用归一 Choi，因子与该来源区分。

<a id="ref-faithful"></a>

### [10]

G. M. D'Ariano and P. Lo Presti.
[Imprinting Complete Information about a Quantum Channel on its Output State](https://arxiv.org/pdf/quant-ph/0211133).
*Physical Review Letters* 91, 047902 (2003)。
本轮读取公开作者稿关于纯态忠实性的可逆条件、混合可分忠实探针与反演条件成本的相关段落。
命题 [5.2](#prop-mixed) 的正性反例在本文完整证明，不以线性忠实性直接冒充序同构。

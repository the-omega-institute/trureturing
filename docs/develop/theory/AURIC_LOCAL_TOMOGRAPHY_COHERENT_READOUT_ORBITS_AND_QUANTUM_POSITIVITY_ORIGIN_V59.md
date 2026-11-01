> **整理者说明（归属与范围）。** 下列正文保留原作者的全部论断、证明和来源表述；“本轮”“前轮”及取得、阅读、比较、制作、未修改仓库等历史报告均为原作者报告，不表示整理者实施或重新认证了这些历史行为。整理者的必要限定均另列为相邻的“整理者注”。数学核对限纸面推理和所列原文，不声称 Lean、内核、全上游、物理或经验认证。

### 原稿编译、字体与 PDF 设置（原作者）

以下逐行保留原稿导言设置；代码中的换行机会仅供窄屏阅读。Markdown 不执行这些 XeLaTeX 设置。

<code>% !TeX progr<wbr>am = xelatex</code>

<code>% Compile tw<wbr>ice with XeL<wbr>aTeX. Option<wbr>al: &#92;def&#92;AUR<wbr>ICFontPath{/<wbr>absolute/fon<wbr>t/path/}</code>

<code>% This is a <wbr>paper deriva<wbr>tion; no mat<wbr>hematical pr<wbr>ogram or num<wbr>erical searc<wbr>h was used.</code>

<code>&#92;documentcla<wbr>ss[11pt,a4pa<wbr>per]{article<wbr>}</code>

<code>&#92;usepackage[<wbr>margin=23mm,<wbr>headheight=1<wbr>6pt]{geometr<wbr>y}</code>

<code>&#92;usepackage{<wbr>fontspec}</code>

<code>&#92;ifdefined&#92;A<wbr>URICFontPath</code>

<code> &#92;setmainfon<wbr>t[Path=&#92;AURI<wbr>CFontPath,Bo<wbr>ldFont=NotoS<wbr>erifCJKsc-Bo<wbr>ld.otf,</code>

<code> ItalicFont=<wbr>NotoSerifCJK<wbr>sc-Regular.o<wbr>tf,BoldItali<wbr>cFont=NotoSe<wbr>rifCJKsc-Bol<wbr>d.otf]{NotoS<wbr>erifCJKsc-Re<wbr>gular.otf}</code>

<code>&#92;else</code>

<code> &#92;IfFontExis<wbr>tsTF{Noto Se<wbr>rif CJK SC}{</code>

<code> &#92;setmainfon<wbr>t[ItalicFont<wbr>=Noto Serif <wbr>CJK SC,BoldI<wbr>talicFont=No<wbr>to Serif CJK<wbr> SC Bold]{No<wbr>to Serif CJK<wbr> SC}</code>

<code> }{&#92;setmainf<wbr>ont[BoldFont<wbr>=FandolSong-<wbr>Bold.otf,Ita<wbr>licFont=Fand<wbr>olSong-Regul<wbr>ar.otf,</code>

<code> BoldItalicF<wbr>ont=FandolSo<wbr>ng-Bold.otf]<wbr>{FandolSong-<wbr>Regular.otf}<wbr>}</code>

<code>&#92;fi</code>

<code>&#92;setmonofont<wbr>{Latin Moder<wbr>n Mono}</code>

<code>&#92;XeTeXlinebr<wbr>eaklocale &quot;z<wbr>h&quot;</code>

<code>&#92;XeTeXlinebr<wbr>eakskip=0pt <wbr>plus 1pt</code>

<code>&#92;usepackage{<wbr>amsmath,amss<wbr>ymb,amsthm,m<wbr>athtools,bm,<wbr>mathrsfs}</code>

<code>&#92;usepackage{<wbr>booktabs,arr<wbr>ay,tabularx,<wbr>enumitem,fan<wbr>cyhdr,xcolor<wbr>,needspace}</code>

<code>&#92;definecolor<wbr>{auricblue}{<wbr>RGB}{24,53,7<wbr>9}</code>

<code>&#92;usepackage[<wbr>unicode,colo<wbr>rlinks=true,<wbr>linkcolor=au<wbr>ricblue,urlc<wbr>olor=auricbl<wbr>ue,citecolor<wbr>=auricblue]{<wbr>hyperref}</code>

<code>&#92;hypersetup{<wbr>pdftitle={AU<wbr>RIC v59：局部层析<wbr>、相干读出轨道与量子正性<wbr>起源},</code>

<code>pdfauthor={A<wbr>URIC researc<wbr>h continuati<wbr>on},</code>

<code>pdfsubject={<wbr>Fixed ontic <wbr>response, re<wbr>al Clifford <wbr>atoms, commo<wbr>n complex st<wbr>ructure, ran<wbr>k-one probe <wbr>positivity, <wbr>finite error<wbr> bounds and <wbr>recursive sq<wbr>uare weights<wbr>}}</code>

<code>&#92;newcommand{<wbr>&#92;R}{&#92;mathbb <wbr>R}</code>

<code>&#92;newcommand{<wbr>&#92;C}{&#92;mathbb <wbr>C}</code>

<code>&#92;newcommand{<wbr>&#92;HH}{&#92;mathca<wbr>l H}</code>

<code>&#92;newcommand{<wbr>&#92;A}{&#92;mathcal<wbr> A}</code>

<code>&#92;newcommand{<wbr>&#92;B}{&#92;mathcal<wbr> B}</code>

<code>&#92;newcommand{<wbr>&#92;E}{&#92;mathcal<wbr> E}</code>

<code>&#92;newcommand{<wbr>&#92;Lcal}{&#92;math<wbr>cal L}</code>

<code>&#92;newcommand{<wbr>&#92;Tr}{&#92;operat<wbr>orname{Tr}}</code>

<code>&#92;newcommand{<wbr>&#92;Span}{&#92;oper<wbr>atorname{spa<wbr>n}}</code>

<code>&#92;newcommand{<wbr>&#92;rank}{&#92;oper<wbr>atorname{ran<wbr>k}}</code>

<code>&#92;newcommand{<wbr>&#92;SR}{&#92;operat<wbr>orname{SR}}</code>

<code>&#92;newcommand{<wbr>&#92;sa}{&#92;mathrm<wbr>{sa}}</code>

<code>&#92;newcommand{<wbr>&#92;Herm}{&#92;oper<wbr>atorname{Her<wbr>m}}</code>

<code>&#92;newcommand{<wbr>&#92;ket}[1]{&#92;lv<wbr>ert#1&#92;rangle<wbr>}</code>

<code>&#92;newcommand{<wbr>&#92;bra}[1]{&#92;la<wbr>ngle#1&#92;rvert<wbr>}</code>

<code>&#92;newcommand{<wbr>&#92;proj}[1]{&#92;k<wbr>et{#1}&#92;bra{#<wbr>1}}</code>

<code>&#92;newcommand{<wbr>&#92;repo}[2]{&#92;h<wbr>ref{https://<wbr>github.com/t<wbr>he-omega-ins<wbr>titute/trure<wbr>turing/blob/<wbr>8558e845c6b6<wbr>e49b11087733<wbr>242e5ae38648<wbr>3392/docs/de<wbr>velop/theory<wbr>/#1}{#2}}</code>

<code>&#92;theoremstyl<wbr>e{definition<wbr>}</code>

<code>&#92;newtheorem{<wbr>definition}{<wbr>定义}[section]</code>

<code>&#92;newtheorem{<wbr>theorem}[def<wbr>inition]{定理}</code>

<code>&#92;newtheorem{<wbr>proposition}<wbr>[definition]<wbr>{命题}</code>

<code>&#92;newtheorem{<wbr>corollary}[d<wbr>efinition]{推<wbr>论}</code>

<code>&#92;newtheorem{<wbr>lemma}[defin<wbr>ition]{引理}</code>

<code>&#92;newtheorem{<wbr>remark}[defi<wbr>nition]{说明}</code>

<code>&#92;renewcomman<wbr>d{&#92;proofname<wbr>}{证明}</code>

<code>&#92;renewcomman<wbr>d{&#92;abstractn<wbr>ame}{摘要}</code>

<code>&#92;renewcomman<wbr>d{&#92;refname}{<wbr>固定来源与阅读边界}</code>

<code>&#92;setlength{&#92;<wbr>parindent}{1<wbr>.8em}</code>

<code>&#92;setlength{&#92;<wbr>parskip}{2pt<wbr>}</code>

<code>&#92;setlength{&#92;<wbr>emergencystr<wbr>etch}{3em}</code>

<code>&#92;setlist{nos<wbr>ep,leftmargi<wbr>n=2em}</code>

<code>&#92;pagestyle{f<wbr>ancy}&#92;fancyh<wbr>f{}</code>

<code>&#92;fancyhead[L<wbr>]{&#92;small AUR<wbr>IC：关系完备与量子正性<wbr>}</code>

<code>&#92;fancyhead[R<wbr>]{&#92;small v59<wbr> / 2026-11-0<wbr>1}</code>

<code>&#92;fancyfoot[C<wbr>]{&#92;thepage}</code>

<code>&#92;allowdispla<wbr>ybreaks[2]</code>

# AURIC：量子起源的关系公理再推进

## 局部层析、相干读出轨道与正性闭包

**定义、定理与纸面证明　v59.0**

2026 年 11 月 1 日　Asia/Singapore

## 摘要

本文延续唯一本体、完整内生观察者和单增门词的框架，把上一轮的两项前件进一步拆开：
共同复结构可改写为关系层面的局部乘积完备；完整效果正性可由一个非零秩一读口的充分可逆轨道及其非负响应推出。
在有限实 Clifford 原子的商类中，局部乘积效果张成全部自伴关系，当且仅当仅保留一个相对复定向中心扇区。
对一个固定响应，实线性关系一致性先给唯一 Hermitian 迹一表示；它尚不保证正性。
秩一轨道的全方向非负性才强迫密度矩阵与 Born 形式。
高秩投影、局部积探针、有限菜单各有明确反例；Schmidt 秩给出严格的正性认证层级。
有限方向覆盖、读数误差和近似关系误差给出统一 Born 近似界，并显式保留读口增益和维数成本。
另以二元互补归一、同源递归细分和终幅充分性证明概率平方律，无需预设连续性。
项目最新的历史联合反例及零幅读器失稳说明：单独相容不保证联合相容，酉算子接近也不自动保证实际报告接近。
全部结果是明确条件下的数学重构；没有从裸二元逻辑或唯一本体本身推出全部物理量子公理。

## 1. 本轮的核心推进与项目增量

本轮最有力的结论是：

$$
\boxed{\begin{gathered}
\text{三轴关系原子}+\text{局部乘积关系完备}
\ \Longrightarrow\ \text{共同复矩阵块};\\
\text{同一响应的关系一致性}
\ \Longrightarrow\ \text{唯一 Hermitian 迹一表示};\\
\text{一个秩一读口的充分轨道}+\text{轨道读数非负}
\ \Longrightarrow\ \text{正密度矩阵与 Born 表示}.
\end{gathered}}
$$

这把“量子态为何必须正”转成了一个关系问题：同一响应能否在所有可逆可达的纯方向上保持非负。
信息可以唯一重建、重建对象必为正、读数能在同一历史中相容，这三件事需要分别证明。

### 1.1. 固定来源及本轮真正变化

项目固定于提交


<code>8558e845c6b6<wbr>e49b11087733<wbr>242e5ae38648<wbr>3392</code>。


唯一实际活动 HEAD 请求完成于新加坡时间 2026-11-01 02:06:31.006470。
相对 v58 的 <code>3d4c9c501554<wbr>6c3d0ea44d3c<wbr>af71ba02b2d0<wbr>d4a9</code>，
固定比较前进 81 个提交、涉及 213 个路径；比较 JSON 与完整 diff 的路径集一致。
未截断理论树从 1119 份文件增至 1120 份，仅三份理论文本改变。
这是来源身份与差异范围核对，不是对全库数学的认证。[head](#bib-head)

> **整理者注（historical）。** 这里的活动 HEAD 请求、时点、81 个提交／213 个路径、1119→1120 文件及三份理论变化均按原作者历史报告保留；整理者未复现当时请求或比较 JSON，不把本次取得固定 Git 对象等同于这些历史行为。

1. <strong>RRO 新增 §§56–61。</strong>
在同一个原生过程与实际十二调用切口中，两个过去细化分别保持全部原终端效果关系，
其联合却违反一条精确等效果关系。因此历史相容不自动对联合封闭。[rro](#bib-rro)

2. <strong>Quantum IV 新增 §205。</strong>
在明确保留的“精确零幅触发”辅助配置律下，辅助酉传播子可任意接近，
而实际报告仍保持固定正质量差。由算子误差到实际概率误差，需要另付读出合同。[qiv](#bib-qiv)

3. <strong>V53 本轮入库。</strong>
它已经包含线性锐读出到 Clifford 复结构、完整相容效果的共同相位纤维、
实张量相对定向，以及正交可加平方权重。其入库不意味着这些内容是本轮新发现。
其中的秩一读口更正尤其相关：$cP$ 的酉轨道是 $cQ$，不能擅自把增益 $c$ 删除。[v53](#bib-v53)

下文给出上述项目结果的进一步连接和独立纸面证明。
维数分类、迹配对、谱变分、GNS 与 Schmidt 秩工具均为通常数学；
本文不声称这些工具或相关通式的全球优先权。

### 1.2. 唯一固定本体与重构的逻辑顺序

全篇固定一个本体来源 $\Omega$ 和它的同一个响应 $p_\Omega$。
完整观察者态仍采用

$$
\Psi_k=U_k\cdots U_1\Omega.
$$

环境、控制、记录、预测与自我读出均在这个完整载体中。
本文的有限关系块只是观察者内部可表达的一类关系，不将观察者重新定义为环境偏迹后的局部态。
“门词单增”指前缀延长，不推出范数、熵或计算复杂度单调。

为避免把待证结论预先放进公理，推导开始时不假设
$p_\Omega(E)=\langle\Omega,E\Omega\rangle$。
先规定关系代数及同一来源的响应，再证明该响应存在正量子表示。
随后得到的向量是同一个固定响应的数学实现，不是另选一个实际宇宙。
即使有限接口的表示为混态，也不表示全局本体有多个实际实例。

## 2. 关系层析为何等价于共同复结构

#### 定义 2.1（实三轴关系原子）

固定整数 $N\ge1$。第 $r$ 个原子有自伴生成元 $X_r,Y_r,Z_r$，满足

$$
X_r^2=Y_r^2=Z_r^2=I,\qquad
X_rY_r=-Y_rX_r,\quad Y_rZ_r=-Z_rY_r,\quad Z_rX_r=-X_rZ_r.
$$

式（R）

不同原子的生成元对易。仅以这些关系生成的含幺实 $*$ 代数记作 $\mathcal A_N$。
“局部”在这里指关系因子，尚不预设物理空间中的邻近性。

等价的锐读出形式为：$B(n)=n_1X+n_2Y+n_3Z$ 实线性，且
$B(n)^2=\|n\|_2^2 I$。对 $n+m$ 极化便得到反对易关系。
因此三轴数目、实线性、正定二次几何和锐性都是明确输入；
仅有三个名称或普通二维正交分解并不自动给出 R。[v53](#bib-v53)

<a id="lem:sectors"></a>

#### 引理 2.2（中心相位与有限扇区分解）

令 $J_r=X_rY_rZ_r$，$D=2^N$。则

$$
J_r^2=-I,\qquad J_r^*=-J_r,\qquad
s_r=-J_1J_r\quad(r\ge2)
$$

为彼此对易的中心自伴 involution，即 $s_r^*=s_r$、$s_r^2=I$，并有

> **整理者注（involution）。** 本句的“自伴 involution”仅修饰 $s_r$；$J_r$ 是中心反自伴元且平方为 $-I$，不是自伴 involution。

$$
\boxed{
\mathcal A_N\cong\bigoplus_{\epsilon\in\{\pm1\}^{N-1}}M_D(\mathbb C)_{\mathbb R}.
}
$$

式（2.1）

第 $\epsilon$ 块满足 $J_r=\epsilon_rJ_1$，约定 $\epsilon_1=1$。

**证明。**

同一原子内交换三次给 $J_r^2=-I$、$J_r^*=-J_r$；
把任一生成元穿过另外两个生成元只产生两次负号，所以 $J_r$ 中心。
不同原子对易，遂得 $s_r$ 的各项性质。

中心投影

$$
e_\epsilon=2^{1-N}\prod_{r=2}^N(I+\epsilon_rs_r)
$$

两两正交且和为 $I$。取 $J_1=iI$，在第 $\epsilon$ 块可令

$$
X_r=\sigma_x^{(r)},\qquad Z_r=\sigma_z^{(r)},\qquad
Y_r=\epsilon_r\sigma_y^{(r)}.
$$

这些矩阵满足原关系并使相应 $e_\epsilon$ 为单位，其余中心投影为零，故每块非零。
在每块中 $Y_r=J_rX_rZ_r$，所以以 $J_1$ 为复数 $i$ 后，
所有词由 $4^N=D^2$ 个 $X_1^{a_1}Z_1^{b_1}\cdots X_N^{a_N}Z_N^{b_N}$ 张成。
它们的 Pauli 张量矩阵像复线性独立并张成 $M_D(\mathbb C)$。
每个块因而恰为 $M_D(\mathbb C)$；对全部中心投影求和得到式 (2.1)。

∎

#### 定义 2.3（关系层面的局部乘积完备，L）

取非零含幺实 $*$ 商 $q:\mathcal A_N\twoheadrightarrow\mathcal B$。
正锥采用这些有限矩阵块中的通常正锥，效果满足 $0\preceq E\preceq I$。
下文的完整正归一响应指自伴部上的正归一实线性泛函限制到效果域；
它也可由完整效果上的正归一粗粒化可加性等价给出。
记

$$
\mathscr P=\{q(E_1\cdots E_N):E_r\text{ 是第 }r\text{ 个原子的效果}\},
\qquad \mathcal L=\operatorname{span}_{\mathbb R}\mathscr P.
$$

要求

$$
\boxed{\mathcal L=\mathcal B_{\mathrm{sa}}.}
$$

式（L）

这是同一关系代数中的算子恒等式要求，其线性组合系数须对内部上下文统一。
它不是仅在固定 $\Omega$ 上匹配某一个期望值。

<a id="thm:lt"></a>

#### 定理 2.4（局部乘积完备与单中心扇区等价）

在上述商类中，以下条件等价：

1. L 成立；

2. $\mathcal B$ 仅保留一个相对定向中心扇区；

3. $\mathcal B\cong M_D(\mathbb C)_{\mathbb R}$，且存在确定符号使 $q(J_r)=\epsilon_rq(J_1)$；

4. 局部乘积效果分离 $\mathcal B$ 上全部正归一的完整效果响应。

重标局部 $Y_r\mapsto\epsilon_rY_r$ 后，所有原子共享同一个复单位。

**证明。**

每个 $M_D(\mathbb C)_{\mathbb R}$ 是简单实代数：实双边理想可乘中心 $iI$，故也是复理想。
所以 $\mathcal B$ 只能保留非空的 $K$ 个完整块，
$\dim_\mathbb R\mathcal B_{\mathrm{sa}}=KD^2$。

单原子自伴部由 $I,X,Y,Z$ 张成，而它们可由局部效果线性表示，例如
$X=(I+X)/2-(I-X)/2$。因此 $\mathcal L$ 由 $4^N=D^2$ 个自伴 Pauli 型乘积词张成。
投影到任意保留块后，这些词只是某些 $Y$ 因子变号的 Pauli 张量基，仍独立。
故 $\dim_\mathbb R\mathcal L=D^2$。于是 L 当且仅当 $K=1$，前面三项等价。

L 成立时，实线性响应由乘积效果值确定。
若 L 不成立，取非零自伴 $H$ 与 $\mathcal L$ 在分块迹配对下正交。
因 $I\in\mathcal L$，有 $\operatorname{Tr} H=0$。对足够小的 $t>0$，

$$
R_\pm=\frac{I}{KD}\pm tH
$$

均正且总迹一；它们定义不同的完整响应，却在全部乘积效果上一致。
故第四项失败，等价得证。这里完整正响应域只是数学测试域，并不声称存在多个实际本体。

∎

#### 推论 2.5（额外中心关系的固定距离）

若 $\mathcal B$ 保留至少两块，任一非平凡中心投影 $e$ 满足

$$
\boxed{\inf_{L\in\mathcal L}\|e-L\|_{\mathrm{op}}=\frac12.}
$$

式（2.2）

**证明。**

在 $e$ 分别取值一、零的两个块中，各取 $\lvert{0}\rangle^{\otimes N}$ 的向量响应。
局部效果写成 $a_0I+a_xX+a_yY+a_zZ$ 后，其 $\lvert{0}\rangle$ 读数为 $a_0+a_z$，
故这两个响应对每个乘积效果、从而每个 $L\in\mathcal L$ 都相同。
它们对 $e$ 的差是一，所以 $1\le2\|e-L\|_{\mathrm{op}}$。
取 $L=I/2$ 达到上界。

∎

这是完整关系算子范数的间隙。某个固定 $\Omega$ 中很小的中心分支，
在该态加权的平均误差中仍可很小；两种误差不能混同。

### 2.1. 同一个循环本体表示中的准确含义

<a id="prop:cyclic"></a>

#### 命题 2.6（固定循环表示中的等价）

设 $(\pi,\mathcal H,\Omega)$ 为以 $J_1$ 作为 $i$ 的复线性循环表示，
$\|\Omega\|=1$，$\mathcal B=\pi(\mathcal A_N)$。
则 L 等价于

$$
\left\langle\Omega,\pi\!\left(\frac{I+s_r}{2}\right)\Omega\right\rangle
\in\{0,1\}\quad(r\ge2).
$$

式（$C_\Omega$）

**证明。**

若右式成立，存在 $\epsilon_r=\pm1$ 使
$(\pi(s_r)-\epsilon_rI)\Omega=0$。
中心性将其传到所有 $\pi(a)\Omega$，循环性再给
$\pi(s_r)=\epsilon_rI$。所以仅保留一个中心块，定理 [2.4](#thm:lt) 给 L。
反向由 L 强迫单块，各 $s_r$ 都是确定标量，遂得右式。

∎

这是一项精确等价重述，未证明 L 比上一轮的中心确定性严格更弱。
像代数单块也不意味着表示不可约；混态 GNS 可有表示重数。
在同一固定响应上，算子完备还可写为：
每个自伴 $B$ 都存在固定 $L\in\mathcal L$，使
$\langle\pi(a)\Omega,(B-L)^2\pi(a)\Omega\rangle=0$ 对全部关系上下文 $a\in\mathcal A_N$ 成立。
只在一个向量上匹配期望，或只沿一个未证明覆盖的轨道测试，并不足够。

> **整理者注（bounded-cyclic）。** 此处表示为保持伴随的有界算子表示；由平方期望为零得 $(B-L)\pi(a)\Omega=0$，再用循环稠密性及有界性推广到整个空间。量词仍为全部 $a\in\mathcal A_N$，不是有限上下文子集。

<a id="prop:restricted"></a>

#### 命题 2.7（受限轨道上的层析不能代替 L）

唯一固定 $\Omega$、门轨道的循环线性张成、以及该轨道响应的局部层析，
可以同时成立而 $C_\Omega$ 失败。

**证明。**

取两个原子，在 $\mathbb C^4\oplus\mathbb C^4$ 上令

$$
\pi_+(a\otimes b)=a\otimes b,\quad
\pi_-(a\otimes b)=a\otimes\bar b,\quad
\Omega=\frac{\lvert{00}\rangle\oplus\lvert{00}\rangle}{\sqrt2}.
$$

允许局部 $SU(2)$ 作用。写 $\psi_A=U_A\lvert{0}\rangle$、$\psi_B=U_B\lvert{0}\rangle$，
完整向量变成

$$
\Psi=\frac{\psi_A\otimes\psi_B\ \oplus\ \psi_A\otimes\bar\psi_B}{\sqrt2}.
$$

每个局部乘积效果的响应为
$\langle\psi_A,E_A\psi_A\rangle\langle\psi_B,E_B\psi_B\rangle$。
这些统计唯一确定 $\rho_A,\rho_B$，继而确定该轨道在两块上的完整响应：
权重各为 $1/2$，块内密度分别为 $\rho_A\otimes\rho_B$ 和
$\rho_A\otimes\bar\rho_B$。所以受限轨道具有局部层析。

然而两个中心块的质量始终为 $1/2$。取 $U_B=iZ$，
轨道还包含 $\bigl((i\lvert{00}\rangle)\oplus(-i\lvert{00}\rangle)\bigr)/\sqrt2$；与原向量作复线性组合可分离两块。
局部旋转再分别张成每个 $\mathbb C^4$，所以轨道的复线性张成是整个表示空间。
这些性质仍没有使中心确定。

∎

共同复结构的来源因而是完整关系层面的相容，而不是“一个向量”这个事实。
一般量子重构中的局部层析还需要额外的系统、复合和有序结构条件；
Barnum–Wilce 的 Jordan 路线同样不以局部层析单独推出量子论。[barnum](#bib-barnum)

## 3. 关系一致性先给矩阵，正性需要另一条证明

#### 定义 3.1（同一来源的实际关系一致性，RC）

在已确定的 $\mathcal B\simeq M_D(\mathbb C)$ 中，令实际声明的效果域 $\mathscr E$
包含 $I$，并实线性张成 $\operatorname{Herm}_D$。
同一个固定来源响应 $p:\mathscr E\to\mathbb R$ 满足 $p(I)=1$。
RC 要求

$$
\boxed{
\sum_j c_jE_j=0\ \Longrightarrow\ \sum_j c_jp(E_j)=0
\quad(c_j\in\mathbb R,\ E_j\in\mathscr E).
}
$$

式（RC）

所有项须属于同一个已声明的响应域；不能混合不同准备或不相容的历史条件化。

<a id="thm:rc"></a>

#### 定理 3.2（唯一 Hermitian 表示）

RC 蕴含存在唯一 $W=W^\dagger$、$\operatorname{Tr} W=1$，使

$$
\boxed{p(E)=\operatorname{Tr}(WE)\qquad(E\in\mathscr E).}
$$

式（3.1）

此处尚不能断言 $W\succeq0$。

**证明。**

对 $A=\sum_jc_jE_j$ 定义 $\ell(A)=\sum_jc_jp(E_j)$。
两种表示之差为 RC 关系，所以定义良好。
它是整个 $\operatorname{Herm}_D$ 上唯一实线性泛函；非退化实迹配对给唯一 Hermitian $W$。
由 $\ell(I)=1$ 得 $\operatorname{Tr} W=1$。证明没有使用完整正锥上的非负性。

∎

RC 是分解相容条件：同一个数学效果无论如何线性表达，都必须给相同响应。
若完整效果域另有所有相容粗粒化、标量细分及非负性，它可由可加性推出；
本轮使用有限或受限菜单时，把 RC 明确列为前件。

<a id="thm:orbit"></a>

#### 定理 3.3（非零秩一轨道强迫完整正性）

固定读口 $E_\star=cP_0$，其中 $P_0$ 为秩一投影、$0<c\le1$。
设声明可用程序的回拉效果 $U^\dagger E_\star U$ 均在同一响应域内。
若 $\{U^\dagger P_0U\}$ 在全部秩一投影中稠密，且其实际响应均非负，
则定理 [3.2](#thm:rc) 的 $W$ 必满足

$$
\boxed{W=\rho\succeq0,\quad\operatorname{Tr}\rho=1,\quad p(E)=\operatorname{Tr}(\rho E).}
$$

式（3.2）

**证明。**

除以固定正数 $c$，得到每个轨道方向 $\phi$ 的
$\langle\phi,W\phi\rangle\ge0$。
给任意单位 $\psi$，取 $P_{\phi_n}\to P_\psi$。
有限维迹泛函连续，故
$\langle\psi,W\psi\rangle=\lim_n\operatorname{Tr}(WP_{\phi_n})\ge0$。
全部二次型非负等价于 $W\succeq0$。

∎

这确实把“所有数学效果均直接可读”缩成“一个带增益的秩一读口具有充分实际控制轨道”。
所得正泛函可延拓到全部数学效果，但不表示所有效果已实际测过。
如果严格只谈唯一已执行前缀，覆盖对象必须改为真实取得的回拉效果集合，
并对这个实际集合证明覆盖及共同 RC。抽象门群稠密不等于历史已经采到稠密读数。

<a id="cor:ball"></a>

#### 推论 3.4（三轴平方约束的正性来源）

写 $W=(I+\boldsymbol r\cdot\boldsymbol\sigma)/2$，其中 $\boldsymbol r\in\mathbb R^3$。
对方向 $n\in S^2$ 的秩一投影 $P_n=(I+n\cdot\boldsymbol\sigma)/2$，RC 的线性延拓满足

$$
\ell(cP_n)=\frac c2(1+\boldsymbol r\cdot n).
$$

实际域内 $\ell=p$；域外的式子只是数学延拓。全部方向延拓非负，当且仅当

$$
\boxed{r_x^2+r_y^2+r_z^2\le1.}
$$

式（3.3）

合法态纯，当且仅当等号成立。

**证明。**

单位方向上 $\min_n\boldsymbol r\cdot n=-\|\boldsymbol r\|_2$。
所以非负等价于 $\|\boldsymbol r\|_2\le1$。
$W$ 的两个特征值为 $(1\pm\|\boldsymbol r\|_2)/2$；
迹一正矩阵秩一当且仅当一个特征值为零。

∎

只测三对轴方向，合法性仅给 $|r_x|,|r_y|,|r_z|\le1$。
例如 $\boldsymbol r=(1,1,1)$ 对三对轴各给合法二元概率，却位于球外。
这精确说明：三个坐标可以完整记录一个候选关系，但球面正性还要求方向间的相容。

### 3.1. 信息完备的高秩读口仍可能漏掉负方向

<a id="prop:rank"></a>

#### 命题 3.5（固定秩轨道：分离与正性不同）

对 $1\le k\le D-1$，全部秩 $k$ 投影实线性张成 $\operatorname{Herm}_D$。
但对 Hermitian $W$，若特征值 $\lambda_1\le\cdots\le\lambda_D$，则

$$
\min_{\operatorname{rank} Q=k}\operatorname{Tr}(WQ)=\sum_{j=1}^k\lambda_j.
$$

式（3.4）

它检查的是最小 $k$ 个特征值的和，未必检查每个特征值。

**证明。**

若 Hermitian $H$ 与所有秩 $k$ 投影迹正交，在其本征基中任意 $k$ 个特征值之和均为零。
比较只交换一个索引的两个集合，可知全部特征值相等；再由和为零得它们全零。
迹正交补为零，故这些投影张成全部自伴部。

在 $W$ 的本征基中记 $q_j=\langle e_j,Qe_j\rangle$，则
$0\le q_j\le1$、$\sum_jq_j=k$，并有

$$
\operatorname{Tr}(WQ)-\sum_{j\le k}\lambda_j
=\sum_{j>k}\lambda_jq_j-\sum_{j\le k}\lambda_j(1-q_j)\ge0.
$$

不等式以 $\lambda_k$ 同时下界右边第一和、上界被减去的第二和；
两组权重相等。取最小 $k$ 个本征方向达到等号。

∎

例如

$$
D=4,\quad k=2,\quad W=\operatorname{diag}(-1/2,1/2,1/2,1/2)
$$

不是正态，但对任意秩二 $Q$ 都有 $0\le\operatorname{Tr}(WQ)\le1$。
所以即便每个二结果菜单 $\{Q,I-Q\}$ 都合法，仍不能推出正性。
$k=1$ 已足够；$k=D-1$ 若同时包含补效果，也间接给所有秩一效果，不能把反例扩大到这两个端点。
项目 $\Omega$ 命题 32.2 的固定秩轨道结论是已给密度态的可分辨性；
本命题准确区分其层析用途与从未知 $W$ 认证正性的用途。[omega](#bib-omega)

## 4. 二元控制如何覆盖全部方向，纠缠探针又增加什么

#### 定义 4.1（基方向上的二元控制图）

令 $\Gamma$ 为 $D$ 个正交基方向上的连通图，指定根 $0$。
每条边允许任意作用于其两个基方向的 $SU(2)$ 门，其他基方向不变。
顶点数为 $D$；这里不是把 $N=\log_2D$ 个物理 qubit 的连接图直接当成 $\Gamma$。

<a id="thm:tree"></a>

#### 定理 4.2（生成树上的秩一轨道覆盖）

在上述明确控制条件下，对任意单位 $\psi\in\mathbb C^D$，
至多 $D-1$ 个二元门即可给 $U\psi=e_0$。
因此根读口的回拉轨道包含全部秩一方向。

**证明。**

取以 $0$ 为根的生成树，自叶向根消元。
当前父、子振幅为 $a,b$，令 $\tau=\sqrt{|a|^2+|b|^2}$。
若 $\tau>0$，使用

$$
G(a,b)=\frac1\tau
\begin{pmatrix}\bar a&\bar b\\-b&a\end{pmatrix}\in SU(2),
\qquad
G(a,b)\binom ab=\binom\tau0 .
$$

其行正交且范数一，行列式为一。若 $\tau=0$，用恒等门。
每步消去一个非根叶坐标，已消去者不再作用。
$D-1$ 步后仅根坐标非零，归一性及正实选择使其为一。
于是 $P_\psi=U^\dagger P_0U$。

∎

这是已给连续二坐标门的控制证明；不免费供应这些门、参数知识或原生编译。
对 $N$ 个二元原子，$D-1=2^N-1$，所以它不是一般高效编译界。
目标方向须已指定；该构造也不是读取未知态全部振幅的无扰算法。

> **整理者注（D1）。** 该消元证明在 $D\ge2$ 时可在最后一条边同时固定根相位。若单独允许 $D=1$，零个二元门不能把任意 $e^{i\theta}e_0$ 变为 $e_0$；秩一投影轨道的结论仍平凡成立。本文三轴复合的原域 $N\ge1$ 给 $D=2^N\ge2$，无需改动该域。

#### 定义 4.3（Schmidt 秩探针与 $k$-块正性）

在 $\mathbb C^d\otimes\mathbb C^d$ 上，称 Hermitian $W$ 为 $k$-块正，
若 $\langle\psi,W\psi\rangle\ge0$ 对全部单位 Schmidt 秩至多 $k$ 的 $\psi$ 成立。
这里 $d\ge2$、$k\in\{1,\ldots,d\}$。
$k=1$ 检查积方向；$k=d$ 才检查全部方向。

#### 引理 4.4（有限 Schmidt 秩的重叠界）

令 $\Phi_d=d^{-1/2}\sum_{j=1}^d\lvert{j,j}\rangle$。
对单位 $\psi$、$\operatorname{SR}(\psi)\le k$，

$$
|\langle\Phi_d,\psi\rangle|^2\le\frac kd,
$$

且上界可达到。

**证明。**

写 $\psi=\sum_{ij}A_{ij}\lvert{i,j}\rangle$，则 $\operatorname{rank} A\le k$、$\|A\|_2=1$，
且 $\langle\Phi_d,\psi\rangle=\operatorname{Tr} A/\sqrt d$。
若 $s_j$ 为非零奇异值，则
$|\operatorname{Tr} A|\le\sum_js_j\le\sqrt{k\sum_js_j^2}=\sqrt k$。
取 $k^{-1/2}\sum_{j=1}^k\lvert{j,j}\rangle$ 达到等号。
这一最大纠缠重叠界也见 Terhal–Horodecki 的 Schmidt 数工作。[terhal](#bib-terhal)

∎

<a id="thm:schmidt"></a>

#### 定理 4.5（严格正性认证层级）

设 $d\ge2$、$0\le t<d^2$，定义迹一 Hermitian 矩阵

$$
W_t=\frac{I-t\lvert{\Phi_d}\rangle\langle{\Phi_d}\rvert}{d^2-t}.
$$

则

$$
\boxed{
W_t\text{ 为 }k\text{-块正}\iff t\le d/k,\qquad
W_t\succeq0\iff t\le1.
}
$$

式（4.1）

对任意 $k<d$，取 $1<t\le d/k$，即得通过全部秩至多 $k$ 探针，
却仍有负特征值的响应。

**证明。**

分母为正。沿 $\Phi_d$ 的特征值为 $(1-t)/(d^2-t)$，
正交补上为 $1/(d^2-t)$，所以完整正性当且仅当 $t\le1$。
对 Schmidt 秩至多 $k$ 的单位方向，最小分子为 $1-tk/d$，
由引理可达。因此 $k$-块正当且仅当 $t\le d/k$。
进一步取 $d/(k+1)<t\le d/k$，便得到 $k$-块正而非 $(k+1)$-块正。

∎

局部乘积效果已经可以线性确定整个 $W$，但它们的非负性只给块正性。
因此，纠缠敏感方向的作用在这里是认证完整正锥。
这不意味着所有联合态层析都需要纠缠门：若接口允许独立局部旋转及完整联合乘积输出，
这些统计本就可以层析联合密度态。[omega](#bib-omega)
一个固定纠缠态的局部酉轨道保持其 Schmidt 系数，亦不可直接冒充全部纠缠方向。

## 5. 有限方向与误差：何时能够稳定接近量子态

#### 定义 5.1（方向覆盖与带增益的实际读数）

设实际探针为 $cP_\phi$，同一个 $0<c\le1$。
若对任意单位 $\psi$，均有实际 $\phi$ 满足

$$
|\langle\psi,\phi\rangle|^2\ge1-\varepsilon,
$$

称实际方向集合构成 infidelity $\varepsilon$-覆盖。
设同一个 RC 表示 $W=W^\dagger$、$\operatorname{Tr} W=1$ 的这些探针响应至少为 $-\eta$，
其中 $\eta\ge0$ 是效果原尺度上的误差。

> **整理者注（epsilon）。** infidelity 误差取 $\varepsilon\ge0$；非空覆盖已排除负 $\varepsilon$。稳定界使用 $0\le\varepsilon<1/D$。$\varepsilon=\eta=0$ 时负谱质量为零；$D=1$ 的迹一 Hermitian 候选本身为 $[1]$，该误差界仍成立。

<a id="thm:stable"></a>

#### 定理 5.2（有限覆盖的正性与统一 Born 近似界）

若 $D\varepsilon<1$，则

$$
\boxed{
\lambda_{\min}(W)\ge-a,\qquad
a=\frac{\eta/c+\varepsilon}{1-D\varepsilon}.
}
$$

式（5.1）

令 $W=W_+-W_-$、$n_-=\operatorname{Tr} W_-$，并取
$\rho=W_+/\operatorname{Tr} W_+$，则

$$
\boxed{
\sup_{0\preceq E\preceq I}|\operatorname{Tr}(WE)-\operatorname{Tr}(\rho E)|
=\tfrac12\|W-\rho\|_1
=n_-
\le(D-1)\frac{\eta/c+\varepsilon}{1-D\varepsilon}.
}
$$

式（5.2）

不需要先验的 $\|W\|_{\mathrm{op}}$ 上界。

**证明。**

记 $m=\lambda_{\min}(W)$、$M=\lambda_{\max}(W)$。
迹一和其余 $D-1$ 个特征值至少为 $m$ 给
$M\le1-(D-1)m$。
取 $m$ 的单位本征向量 $\psi$，并选覆盖方向 $\phi$。
将 $\phi$ 沿 $\psi$ 及正交补分解，交叉项为零，故

$$
-\eta/c\le\langle\phi,W\phi\rangle
\le m+\varepsilon(M-m)
\le(1-D\varepsilon)m+\varepsilon .
$$

移项即得 (5.1)。

迹一使至少一个特征值为正，所以负特征值至多 $D-1$ 个，
从而 $n_-\le(D-1)a$、$\operatorname{Tr} W_+=1+n_-$。
又

$$
W-\rho=\frac{n_-}{1+n_-}W_+-W_-.
$$

两项支撑正交、迹均为 $n_-$，故迹范数为 $2n_-$。
任意效果上的差绝对值至多 $n_-$，负谱支撑投影达到此值，证明 (5.2)。

∎

这里 $\rho$ 是对候选响应的数学修复，不自动等于物理制备或实际更新。
覆盖必须属于已声明的读出域；维数条件 $\varepsilon<1/D$ 和弱读口代价 $\eta/c$ 均不可省略。
如果只知道酉矩阵近似，而不知道实际报告与这些效果保持同一响应合同，则不能应用该定理。

<a id="prop:approxrc"></a>

#### 命题 5.3（近似 RC 的显式接入）

取实际菜单中一个自伴实基 $E_1=I,E_2,\ldots,E_{D^2}$。
读数记为 $q$，满足 $q(I)=1$，以 $q(E_i)$ 唯一拟合 Hermitian 迹一 $W$。
对探针 $F=cP_\phi$，写 $F=\sum_i a_i(F)E_i$。
若

$$
q(F)\ge-\eta,\qquad
\left|q(F)-\sum_i a_i(F)q(E_i)\right|\le\tau,
$$

则定理 [5.2](#thm:stable) 仍成立，只须将 $\eta$ 换成 $\eta+\tau$。
若近似 RC 的准确合同为

$$
\sum_jb_jF_j=0\ \Longrightarrow\
\left|\sum_jb_jq(F_j)\right|\le\delta\sum_j|b_j|,
$$

则可取

$$
\tau=\delta(1+K),\qquad
K=\sup_F\sum_i|a_i(F)|.
$$

式（5.3）

**证明。**

按基拟合给 $\operatorname{Tr}(WF)=\sum_i a_i(F)q(E_i)\ge-(\eta+\tau)$。
此后完全应用上一定理。
对精确关系 $F-\sum_i a_iE_i=0$，系数绝对值和为 $1+\sum_i|a_i|$，
故所声明的近似 RC 合同给 (5.3)。

∎

$K$ 记录所选效果框架的坐标放大；不能在没有误差合同或条件数信息时，把近似 RC 当成精确 RC。
固定有限维基下，坐标映射连续、秩一效果族紧致，所以 $K$ 有限，但不保证很小。
这把用户关心的误差递归具体化为三个可审计量：方向覆盖、原读数误差、关系拟合残差。
式 (5.2) 此时统一控制的是拟合泛函 $\operatorname{Tr}(WE)$，未自动控制所有未检验的实际读数 $q(E)$。
若某个目标效果另有残差
$|q(E)-\sum_i a_i(E)q(E_i)|\le\tau_E$，三角不等式才进一步给

$$
|q(E)-\operatorname{Tr}(\rho E)|\le\tau_E+n_- .
$$

式（5.4）

只在探针集合上给出 $\tau$，不足以把这个实际误差结论推广到其他目标。

<a id="thm:finite"></a>

#### 定理 5.4（有限菜单本身不能强迫完整正性）

设 $D\ge2$，$\mathscr F$ 是有限效果菜单，连同所需补效果。
存在 Hermitian 迹一但非正的 $W$，对每个菜单效果均有
$0\le\operatorname{Tr}(WE)\le1$，且全部真实线性关系 RC 自动成立。

**证明。**

选单位 $\psi$，避开有限菜单及其补效果中所有非零秩一效果的像射线。
令 $W_0=(I-P_\psi)/(D-1)$。
对菜单及补菜单中的任一非零效果 $E$，

$$
\operatorname{Tr}(W_0E)=\frac{\operatorname{Tr} E-\langle\psi,E\psi\rangle}{D-1}>0.
$$

若 $E$ 秩至少二，迹严格大于最大特征值；秩一时由射线避免条件得到严格性。
对非零补效果同理。
现在取

$$
W_\delta=\frac{I-(1+\delta)P_\psi}{D-1-\delta},
\qquad0<\delta<D-1.
$$

其迹为一，在 $\psi$ 方向特征值为负。
有限个非平凡效果和补效果在 $\delta=0$ 的响应均严格正，
所以足够小的 $\delta>0$ 保持所有这些不等式。
零与单位效果仍给零与一；补效果非负保证原效果响应不超过一。
迹表示保证全部 RC。

∎

这不否定有限信息完备测量能够重建一个预先已知合法的量子态。
它说明：在起源重构中，有限读数的逐项合法性不能暗中替代整个正锥的合法性。
有限覆盖可以给明确近似界，严格全正性还需要覆盖极限或其他结构条件。

## 6. 递归为什么选择平方，而不只是任意归一化

#### 定义 6.1（同源二元记录树与径向标定，H）

同一来源有函数 $h:[0,1]\to[0,1]$，以分支振幅模 $r$ 标定其响应，
$h(0)=0$、$h(1)=1$。要求：

1. 二元正交互补满足
$h(r)+h(\sqrt{1-r^2})=1$；

2. 父振幅模 $r$ 的分支可在持久正交记录下继续细分，
条件子幅度模为 $s$，终端模为 $rs$；

3. 同一 $h$ 标定条件分支，终端响应只依赖所声明的终幅模 $rs$，
不依赖产生它的分解树；

4. 对正质量父事件使用概率链式律；零质量父事件的子事件质量为零。

量词中的二元接口及其复合可用性是前件。记录持久性保证子事件仍是父事件的子集，
而不是被擦除记录后重新相干合并的另一类事件。

<a id="thm:square"></a>

#### 定理 6.2（递归与互补归一唯一给平方律）

H 蕴含

$$
\boxed{h(r)=r^2\qquad(0\le r\le1).}
$$

式（6.1）

无需另加连续性。

**证明。**

正质量父事件由链式律及共同条件标定给 $h(rs)=h(r)h(s)$。
若 $h(r)=0$，子事件质量为零，再用终幅充分性识别为 $h(rs)$，
同样得到乘法关系；此步骤没有定义零概率事件上的条件概率。

置 $g(t)=h(\sqrt t)$，则

$$
g(t)+g(1-t)=1,\qquad g(xy)=g(x)g(y),\qquad
g(0)=0,\quad g(1)=1.
$$

对 $x,y\ge0$、$a=x+y\le1$，若 $a>0$，

$$
\begin{aligned}
g(x)+g(y)
&=g(a)g(x/a)+g(a)g(y/a)\\
&=g(a)\bigl[g(x/a)+g(1-x/a)\bigr]
=g(a).
\end{aligned}
$$

$a=0$ 时由端点标定成立。
非负可加性给单调性；单位标定给所有有理 $q\in[0,1]$ 上 $g(q)=q$。
用有理数从两侧夹逼任意实数 $t$，得 $g(t)=t$，即 $h(r)=r^2$。

∎

这里的新组织在于：先由递归乘法和互补归一推出正交可加，
再得到平方。V53 定理 8.3 与 V47 已有“径向非负＋正交可加”路线；
本定理是其上游前件的精化，不把旧的可加函数结论再次当作新发现。[v53](#bib-v53) [v47](#bib-v47)

也必须看见指数二的输入位置。互补振幅
$\sqrt{1-r^2}$ 使用正定二次几何；终幅 $rs$ 使用相干线性复合；
共同 $h$ 和终幅充分性要求递归中的语义稳定。
单独的加法原理、乘法原理或“存在”量词没有决定这些几何与表示条件。
复平面可以定义许多范数；本定理针对已声明的欧氏正交振幅结构。

#### 说明 6.3（为何普通干涉不违反此定理）

持久记录树可用三个正交终端方向说明：
先分成振幅 $r$ 与 $\sqrt{1-r^2}$，
再将前一分支细分成 $rs$ 与 $r\sqrt{1-s^2}$。
第一个父事件对应两个后继方向的直和，记录保持可区分。
若之后擦除父记录并使历史重新干涉，“终端事件是原父事件的子事件”便不再是同一合同；
不能把其干涉幅度代入上述经典事件链式分解。

### 6.1. 项目最新历史反例说明 H 不是免费的

RRO §§56–61 保留原 89 维过程、全部 1024 终端标签及失败坐标、
平方最小源率、源创新、旧档案核和原控制域。
在固定前缀 $a=1^{12}$ 的同一切口，令 $G$ 为完整旧可读档案，
$M$ 为早期真实跳时产生的公平掩码，$Z$ 为时间 11 的隐藏配置位，
$C=M\oplus Z$。则

$$
Y_1=(G,M),\qquad Y_2=(G,C)
$$

分别对全部原可数未来菜单保持 RC，而联合 $Y_\vee=(G,M,C)$ 在质量
$x=\varphi^{-1}$ 的事件上使

$$
E^0_{\epsilon,w_1}=E^0_{1^{10},w_1},
\qquad
k_\vee(\epsilon,w_1)=p_2/A\ne p_2=k_\vee(1^{10},w_1),
$$

式（6.2）

其中 $A=4x^3\in(x,1)$、$p_2=A\sin^2(3\pi/5)>0$。
差为 $p_2(1/A-1)>0$。[rro](#bib-rro)

因此，共同本体和分别安全的二元历史细化没有自动供应联合细化上的相同响应域。
该来源还证明不存在同时支配这两份细化的 RC 安全细化；
这是无 greatest 成员，不是否定 maximal 成员。
隐藏历史函数的数学可条件化也不等于观察者获得了读取隐藏跳时或配置的权限。
本轮 H 必须明确付出持久记录、联合闭包及终幅充分性，才能使用平方律证明。

## 7. 把正性定理接回 AURIC 金字塔的实际读口

### 7.1. 五模式中的秩一探针与三轴

沿用 V37 的五模式顺序 $(0,2,3,5,25)$，置

$$
\nu=\frac1{1+2\sqrt3+\sqrt{11}},\qquad
a_\nu=\frac{\nu(\sqrt3+\sqrt{11})}{2}.
$$

固定效果为

$$
\begin{aligned}
E_{25}&=\frac\nu2(\sqrt3I-X-Y-Z),&E_0&=3E_{25},\\
E_2&=\frac\nu2(\sqrt{11}I+3X+Y+Z),&
E_5&=\frac\nu2(\sqrt{11}I+X+3Y+Z),\\
E_3&=\nu(I+Z)=2\nu P_z .
\end{aligned}
$$

式（7.1）

各效果均非零、秩一且正，和为 $I$；V37 给出其固定五维等距编码。
三个原占据读数满足

$$
u=(X_{\mathrm{occ}},Y_{\mathrm{occ}},Z_{\mathrm{occ}})
=(a_\nu,a_\nu,\nu)+\nu\boldsymbol r.
$$

式（7.2）

它们按项目低端、高端、中位约定对应用户的
$F[1],F[3],F[2]$ 三轴。[v37](#bib-v37)
式 (7.2) 中的占据数与式 (R) 的尖锐关系生成元不同，
五结果读出没有因此变成三次同时尖锐 Pauli 测量。

在这个准确编码中，合法量子区域为

$$
\boxed{
(X_{\mathrm{occ}}-a_\nu)^2+
(Y_{\mathrm{occ}}-a_\nu)^2+
(Z_{\mathrm{occ}}-\nu)^2\le\nu^2.
}
$$

式（7.3）

所以应研究的是经过同一固定标定后的平方半径；
不能把任意未中心化三轴的 $x^2+y^2+z^2$ 都当成同一个守恒量。

本轮定理直接利用 $E_3$ 的秩一性。
它的增益是 $c=2\nu$，全轨道为 $2\nu P_\phi$；
非零增益不妨碍精确正性认证，却会放大绝对读数误差中的 $\eta/(2\nu)$。
这与 V53 的编者更正一致。[v53](#bib-v53)
整个 AURIC 经典概率金字塔大于这个编码球；
固定五模式概率合法性本身不排除定理 [5.4](#thm:finite) 中的伪正候选。

#### 命题 7.1（多原子实际秩一读口及代价）

若 $N$ 个原子的联合乘积事件确实允许取得，则

$$
E_\star^{(N)}
=\bigotimes_{r=1}^N E_3^{(r)}
=(2\nu)^N\lvert{0^{\otimes N}}\rangle\langle{0^{\otimes N}}\rvert
$$

式（7.4）

在逻辑 $D=2^N$ 块上秩一。
若其全局可逆轨道达到所需覆盖，定理 [5.2](#thm:stable) 的 $c$ 应取
$(2\nu)^N$。

**证明。**

秩一投影的张量积仍为秩一，标量因子相乘。
把 $D=2^N$、$c=(2\nu)^N$ 代入已证定理即可。

∎

因此，精确可表示与稳定可取得的成本不同：
同样的绝对误差会被 $(2\nu)^{-N}$ 放大。
若只有单个局部读口 $E_3\otimes I$，它在全局块上的秩为 $2^{N-1}$，
不能当作全局秩一探针使用。这里没有免费增加联合事件、纠缠控制、记录容量或后选择权限。

> **整理者注（localrank）。** “不能当作全局秩一”针对 $N\ge2$；原量词包含的端点 $N=1$ 下 $2^{N-1}=1$，单个局部读口本来就是全局秩一。

### 7.2. 归一化究竟放在哪里

归一化的单位是恒等关系 $I$，由

$$
\sum_sE_s=I,\qquad p(I)=1
$$

实现。某个空模式效果仍是一个效果，不能自动等同于 $I$；
同样，观察者完整状态 $\Omega$ 也不是效果单位。
关系、状态和归一化承担不同数学角色，统一它们需要一个保留这些角色的表示，
而不是把几个符号直接认作同一个对象。
在五模式框架内，三轴、关系坐标与归一关系共同约束读出；
在本轮的正性重构中，它们还必须对可逆方向变换保持一致。

## 8. 酉性、同一本体实现与候选公理总定理

<a id="prop:unitary"></a>

#### 命题 8.1（相位保持的可逆关系变换必为酉实现）

设 $\alpha$ 是 $M_D(\mathbb C)_{\mathbb R}$ 的实 $*$ 自同构，且 $\alpha(J)=J$。
则存在酉 $U$ 使 $\alpha(A)=UAU^\dagger$。
从恒等出发的连续实 $*$ 自同构路径自动保持 $J$。

**证明。**

$\alpha(J)=J$ 使 $\alpha$ 复线性。
它将矩阵单位 $e_{ii}$ 映为两两正交的极小投影，故可选正交单位向量 $v_i$ 张成其像。
由矩阵单位乘法和伴随关系，
$\alpha(e_{ij})=z_{ij}\lvert{v_i}\rangle\langle{v_j}\rvert$，其中
$|z_{ij}|=1$ 且 $z_{ij}=z_{i1}z_{1j}$。
调整各 $v_i$ 相位后，所有 $z_{ij}$ 为一。
令 $Ue_i=v_i$，便得 $\alpha(A)=UAU^\dagger$。

中心中满足 $J^2=-I$ 的复单位只有 $\pm J$。
连续自同构路径不能在这两个值之间跳变，所以从恒等出发保持 $J$。

∎

共同手性在这里明确选择连续可逆变换的复线性分支；
允许翻转 $J$ 时还存在复共轭分支，不能直接称作同一取向内的酉门。
此命题以乘法、伴随和可逆关系结构保持为输入，不由概率归一化单独得到。
每个酉实现只确定到共同 $U(1)$ 相位。本文按门词选定各门代表并依次复合；
整个抽象程序群是否有满足所有群关系的严格酉表示，还需另检查相位提升。

#### 命题 8.2（一个固定响应的一个固定向量实现）

若 $\rho$ 是定理 [3.3](#thm:orbit) 得到的密度矩阵，
取 Hilbert–Schmidt 空间中的

$$
\Omega_{\mathrm{rep}}=\sqrt\rho,\qquad
\mathcal H_{\mathrm{cyc}}=\{A\sqrt\rho:A\in M_D(\mathbb C)\},
\qquad \pi(E)B=EB.
$$

则 $\|\Omega_{\mathrm{rep}}\|=1$，且

$$
p(E)=\langle\Omega_{\mathrm{rep}},\pi(E)\Omega_{\mathrm{rep}}\rangle.
$$

式（8.1）

酉关系程序在这个循环空间上给同一固定向量的酉门序列。

**证明。**

Hilbert–Schmidt 内积为 $\langle A,B\rangle=\operatorname{Tr}(A^\dagger B)$。
故 $\|\sqrt\rho\|^2=\operatorname{Tr}\rho=1$，且
$\langle\sqrt\rho,E\sqrt\rho\rangle=\operatorname{Tr}(\rho E)$。
左乘酉算子保持该内积和循环空间。
所有程序因此作用于同一个 $\Omega_{\mathrm{rep}}$，不需要为每个读口重选本体。

∎

这是固定响应的循环表示，不能将其有限载体自动认定为全部宇宙的物理维数，
也不能仅由“有一个向量”推断该关系代数上的响应为极端纯态。
若有限层通过保持共同复取向的含幺 $*$ 嵌入相容，并给定限制相容的同一归一响应，
其正泛函在代数并上良定义且有界；
范数完备化后可用同一个 GNS 构造实现。[v30](#bib-v30)
这仍要求层间限制相容，不是把每层分别合格就自动接成一个全局历史。

> **整理者注（gns）。** 无限层结论还使用各层的正归一泛函与同一个相容 $C^*$ 范数：含幺 $*$ 嵌入在这些有限矩阵层上等距，因而正泛函在代数并的范数为一，延伸到其 $C^*$ 完备化后适用 GNS。这里没有把层数限制为有限，也未把表示存在升级为实际取得合同。

<a id="thm:main"></a>

#### 定理 8.3（有限关系量子重构的充分条件）

对同一个固定来源，假设：

1. <strong>R：</strong>有限实三轴原子及跨原子对易复合；

2. <strong>L：</strong>其非零商关系代数满足局部乘积自伴完备；

3. <strong>RC：</strong>一个张成实际效果域上的归一响应尊重全部实线性关系；

4. <strong>O：</strong>一个非零秩一读口的声明可用回拉轨道稠密覆盖所有纯方向，
且这些响应非负；

5. <strong>G：</strong>闭合可逆程序保持乘法、伴随和共同复取向。

则该有限接口具有通常复矩阵量子表示：关系代数为 $M_{2^N}(\mathbb C)$，
固定响应为唯一密度矩阵的 Born 形式，可逆程序为酉实现，并有一个固定循环向量表示同一来源。
若另有 H，则持久二元记录树中的径向分支权重唯一为振幅平方。
有限覆盖和近似 RC 时，使用式 (5.1)–(5.4) 得到明确近似版本。

**证明。**

引理 [2.2](#lem:sectors) 与定理 [2.4](#thm:lt) 给共同复矩阵块；
定理 [3.2](#thm:rc) 给唯一 Hermitian 迹一表示；
定理 [3.3](#thm:orbit) 给正性与 Born 表示；
命题 [8.1](#prop:unitary) 给酉实现，上述循环构造给固定向量。
定理 [6.2](#thm:square) 独立给 H 下的递归平方权重。
误差版本已经在定理 [5.2](#thm:stable)、命题 [5.3](#prop:approxrc) 证明。

∎

## 9. 最新项目为何要求保留实际读出桥

Quantum IV §205 在同一原 ready、原源平方最小跳率和旧报告合同下，
明确把辅助“精确零幅才跳”的事件律延拓到固定参数比较族。
它只改变两个辅助地址的脉冲参数 $\alpha=3\pi/5\to\lambda$，得到

$$
\sup_{0\le\tau\le15}
\|\mathcal V^\lambda(\tau)-\mathcal V^\alpha(\tau)\|_{\mathrm{op}}
\le12|\lambda-\alpha|.
$$

式（9.1）

但在 $\alpha$ 的某个穿孔邻域内，原合法准备 $a=(9)$ 和空未来的报告满足

$$
\Pr(J_\alpha=1)=\varphi^{-1},\qquad
\Pr(J_\lambda=1)=0,\qquad
d_{\mathrm{TV}}=\varphi^{-1}.
$$

式（9.2）

所以传播子甚至射影历史可以接近，实际报告仍不接近。[qiv](#bib-qiv)

这是指定事件律与比较族中的条件障碍，不是对所有确定论或所有隐藏变量模型的排除，
也不是物理设备已经发生此种失稳的断言。
其作用是准确指出本轮稳定定理的接口：
式 (5.1)–(5.4) 所需的是同一实际响应的效果对应及残差合同；
不能用式 (9.1) 单独替代该合同、概率连续性或 RC。
原源平方率、ready、控制、读口权限、记录创新和失败合同仍然是该项目过程的独立前件。

## 10. 我们已经解释什么，还缺什么

| 问题 | 本轮得到的证明 | 仍需承担的前件 |
| --- | --- | --- |
| 为何共同复相位 | 有限 Clifford 商中的 L 当且仅当单相对中心扇区 | 三轴锐性、关系乘法、完整关系层析 |
| 为何概率来自正矩阵 | RC 给 $W$，秩一充分轨道非负给 $W\succeq0$ | 同一实际响应域、探针与控制覆盖 |
| 为何三轴有平方约束 | 全方向非负当且仅当 $\Vert\boldsymbol r\Vert_2\le1$ | Pauli/Clifford 几何与方向合同 |
| 为何指数为二 | 二元互补及递归乘法推出正交可加与 $h(r)=r^2$ | 二次振幅几何、共同标定、终幅充分性 |
| 为何闭合门酉 | 保持共同复取向的 $*$ 自同构为内酉 | 可逆关系保持及物理实现 |
| 为何误差可控 | 覆盖、增益、RC 残差给统一效果误差界 | 实际报告桥、资源成本与误差合同 |

这些结果使“量子的起源是关系的一致传导”成为可逐项审查的候选公理化。
最核心的结构不是单独某一个三维图形，而是三种相容：
局部关系能在复合层统一表达，读数能尊重同一关系的不同分解，
这些读数又能沿足够丰富的可逆方向保持非负。
三维球是它在二元接口中的具体表现；高维复合还须保留相位、关联和控制成本。

本轮没有证明 R、L、RC、O、G 的逻辑最小性，也没有证明它们由唯一本体单独强制成立。
相对实/四元数理论的选择、三轴为何恰为三、完整宇宙的初始内容、
实际控制和记录怎样内生可得、空间时钟及物理作用量的来源，仍需新前件或进一步定理。
这里的二次几何及概率响应不能从普通布尔存在逻辑中无条件产生。

下一步最承重的问题可准确表达为：

$$
\boxed{\text{同一原生有限菜单与完整内生记录过程，何时能供应 RC、轨道覆盖及历史联合闭包？}}
$$

它要求把已证的代数表示与项目实际来源、门时间、失败事件和记录权限逐项连接。
如果这一步完成，便可以进一步把当前的充分条件重构推进为更接近物理起源的机制说明；
在完成以前，数学充分性与物理必然性仍须分别陈述。

## 固定来源与阅读边界（原作者）

> **整理者注（书目报告归属）。** 本节的“本轮核读”“前轮已读”“字节一致”等均为原作者报告；整理者实际阅读的固定原文范围与来源身份见本交付的外部证据，不据此宣称复现历史取得、全卷重读或全库认证。

<a id="bib-head"></a>

**[head]**

[trureturing 固定提交 8558e845c6<wbr>b6e49b1108<wbr>7733242e5a<wbr>e386483392](https://github.com/the-omega-institute/trureturing/commit/8558e845c6b6e49b11087733242e5ae386483392)，
提交时间 2026-11-01 02:02:45 Asia/Singapore；
活动引用取得时间 02:06:31.006470。
完整固定比较为
[v58 到本轮提交的比较](https://github.com/the-omega-institute/trureturing/compare/3d4c9c5015546c3d0ea44d3caf71ba02b2d0d4a9...8558e845c6b6e49b11087733242e5ae386483392)。
身份核对不等于数学认证，全文未作全库穷尽阅读。

<a id="bib-rro"></a>

**[rro]**

[RRO：Fibonacci 原生终端认证](https://github.com/the-omega-institute/trureturing/blob/8558e845c6b6e49b11087733242e5ae386483392/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)，
本轮新增并连续阅读 §§56–61，当前源行 3865–4141。
重点为完整实际档案桥、分别 RC 安全、联合失败、早先位恢复及无共同安全上细化。
保留该来源的原过程、平方率、创新与操作权限前件；不以隐藏函数替代可取得记录。

<a id="bib-qiv"></a>

**[qiv]**

[Quantum Principles and Coherent Reconstruction, Continuation IV](https://github.com/the-omega-institute/trureturing/blob/8558e845c6b6e49b11087733242e5ae386483392/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md)，
本轮新增并连续阅读 §205，当前源行 604–808。
辅助零幅事件律的延拓是明确假设；结论只适用于其指定比较族。
所引用上游过程未在本轮全部重新认证。

<a id="bib-v53"></a>

**[v53]**

[V53：锐三轴读出、内生复结构与共同相位相容](https://github.com/the-omega-institute/trureturing/blob/8558e845c6b6e49b11087733242e5ae386483392/docs/develop/theory/AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md)。
本轮核读相关段落包括 §§4.1–4.2、4.6–5.4、7.1–7.5、8.3–8.4：
当前源行 400–469、585–734、819–997、1054–1127。
其中 707–711 的编者更正保留非锐秩一效果的标量增益。
V53 的 $J_1J_2=-I$ 对齐，与本文 $s_2=-J_1J_2=I$ 同义，符号勿混。

<a id="bib-omega"></a>

**[omega]**

[AURIC $\Omega$：静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/8558e845c6b6e49b11087733242e5ae386483392/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，
本轮固定字节与 v58 一致。
重读 §32 附近当前源行 2000–2075，区分固定秩读口的响应分离、
允许门闭包、单读口接口与完整联合乘积读出。
谱极值相关 §60.2 前段另作来源对照；本文命题 [3.5](#prop:rank) 独立给出所需完整证明。

> **整理者注（omega-locator）。** 固定来源中的准确定位是第 40 节内“定理 60.2”，配合定义 60.1（源行 2555–2595）；不是源文件第 60 节。该来源固定 $n\ge3$、$d=F_{n+2}$、$q=F_n$、密度态差及第一位置秩 $q$ 正交投影；有限合法字的共轭轨道闭包来自假设 55.2 和定理 58.1。其谱变分步骤适用于给定 Hermitian 矩阵及固定秩正交投影，并不供应未知响应的正性。原书目“§60.2”措辞保留。

<a id="bib-v37"></a>

**[v37]**

[V37：二元关系、酉表示与黄金门普适性](https://github.com/the-omega-institute/trureturing/blob/8558e845c6b6e49b11087733242e5ae386483392/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)，
本轮固定字节与前轮一致；核读 §3 的实际五效果、固定等距编码与三轴标定，
当前源行 152–244。
本文使用其明确增益和秩一效果，不宣称整个经典金字塔等于 Bloch 球。

<a id="bib-v47"></a>

**[v47]**

[V47：存在量词、平方权重与提示误差关系](https://github.com/the-omega-institute/trureturing/blob/8558e845c6b6e49b11087733242e5ae386483392/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_SQUARE_WEIGHTS_AND_PROMPT_ERROR_RELATIONS_V47.md)。
既有正交权重与平方选择工作；本轮与之的关系通过 V53 §8.3 的明确交叉引用核对，
不声称本轮重新阅读全文。

<a id="bib-v30"></a>

**[v30]**

[V30：唯一静态本体、内生观察者与黄金递归时钟](https://github.com/the-omega-institute/trureturing/blob/8558e845c6b6e49b11087733242e5ae386483392/docs/develop/theory/AURIC_UNIQUE_STATIC_ONTOLOGY_ENDOGENOUS_OBSERVERS_AND_GOLDEN_RECURSIVE_CLOCKS_V30.md)。
前轮已读的 GNS 与固定本体表示背景；本轮文件字节身份核对，
本文所需有限循环实现已在第 8 节独立证明。

<a id="bib-barnum"></a>

**[barnum]**

Howard Barnum and Alexander Wilce,
*Local tomography and the Jordan structure of quantum theory*,
[arXiv:1202.4513](https://arxiv.org/abs/1202.4513)，v2，2013。
用于定位局部层析在重构中的作用及其额外 Jordan、复合和 qubit 等前件，
不将该文概括为局部层析单独推出量子论。

<a id="bib-terhal"></a>

**[terhal]**

Barbara M. Terhal and Pawel Horodecki,
*A Schmidt number for density matrices*,
Physical Review A <strong>61</strong>, 040301(R), 2000，
[doi:10.1103/PhysRevA.61.040301](https://doi.org/10.1103/PhysRevA.61.040301)；
[arXiv:quant-ph/9911117](https://arxiv.org/abs/quant-ph/9911117)。
本轮核读 Lemma 1 的最大纠缠重叠界与相关定义；本文第 4 节给出自足证明。

<strong>方法说明。</strong>
数学部分为纸面推导和反例检查；未运行数学程序、CAS、数值实验、门搜索、枚举或 Lean 编译。
程序仅用于公开来源取得、字节身份／路径差异核对、文档编译及版面检查。
本稿未修改项目仓库，也不把项目声明、哈希一致或排版成功当作形式证明或物理验证。

> **整理者注（ending）。** 上一句“未修改项目仓库”是原作者制作报告；本 Markdown 的整理交付会新增本文件。程序用途及无数学程序声明也保留为原作者报告；整理者本次仅作文本、来源、哈希、PDF、浏览器与版面处理，数学核对为纸面检查。

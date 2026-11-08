# UPPM-RG 002：丢番图定义、关系编译与通用证明的停止边界

内生关系与可核验证明的几何计算理论

丢番图定义、关系编译

与通用证明的停止边界

对“$\mathbb Z$ 在 $\mathbb Q$ 中是丢番图的”最新研究的核验与结合

UPPM-RG 002　版本 1.0　2026年11月8日

**核心结论** 有限多项式和局部三元关系能够表达极丰富的计算内容。表达的有限性、见证的存在性、见证搜索的有效界，以及返回“无解”的停止证据，需要分别证明。把近似提升为精确结论需要可核验的分离条件；本文利用高度界构造相应的离散间隔。

**摘要** 本札记核对了截至2026年11月8日可读的最新公开稿：*$\mathbb Z$ is Diophantine in $\mathbb Q$*, Version 13，稿件日期11月7日。该稿声称构造394总变量的整数系数四次多项式，以及411总变量的完全十进制系数版本。论文按无条件定理陈述；当前公开形式化与审查范围尚不构成完整主定理的独立认证。因此，本文将其主张明确隔离为假设 $\mathsf H_{\mathbb Z/\mathbb Q}$，并证明其与既有计算理论之间的条件性推论。

本文给出整数方程到有理方程的存在性保真编译、固定三元约束网络的条件性不可判定性、可计算见证界与可判定性的等价关系，以及存在性概率读出的有效间隔障碍。另给出可独立核对的高度分离引理、偶数指标 Fibonacci 不变量、带见证长度界的 NP 完全问题与完整候选原则。这些内容承接 UPPM-RG 001 的观察商、有限域拼接、误差控制和完整计算成本框架。经典结论与标准推论不作原创优先权主张。

**核验范围** 本轮阅读了公开定理、版本指南、形式化范围、修订记录和固定提交下的相关证明接口；独立核对了本文写出的基础推导。未逐行复审296页稿件及全部算术几何引用，未重建其 Lean 项目，也未修改或合并用户仓库。

<a id="section-1"></a>

## 1　最新研究：对象、版本与证明状态

### 1.1　最新可读版本

项目仓库当前展示 Version 13，日期2026年11月7日。本文固定其源码于提交

`9c0b3aba60d90fdcac82115f0582a6f52f1054f7`

该提交的时间记录为11月8日05:07:06 UTC。稿件作者栏有意留空，故本文按标题与版本引用，不把协作名单擅自改作正式作者栏。主张如下：[\[1\]](#ref-v13), [\[2\]](#ref-guide)

$$
t\in\mathbb Z\quad\Longleftrightarrow\quad
 \exists\mathbf w\in\mathbb Q^{393}:P_{394}(t,\mathbf w)=0.
$$

其中 $P_{394}$ 为一个固定的整数系数四次多项式。394包括输入变量 $t$。

| 构造 | 总变量 | 见证变量 | 公开数据 |
|:---|:---|:---|:---|
| V13 符号系数 | 394 | 393 | 6338个非零单项式；364个二次残差的平方和。固定整数 $C=3^{2^{25}}$ 不增加变量。 |
| V13 十进制系数 | 411 | 410 | 6388个非零单项式；381个二次残差的平方和；系数绝对值小于 $2^{3247}$。 |

这些数字描述显式四次构造，不是所有次数下变量数最优性的证明。见证变量数固定，也不意味着每个见证数的分子、分母长度有统一小界。

### 1.2　三个相关结果的逻辑层次

2016年 Koenigsmann 已证明 $\mathbb Z$ 在 $\mathbb Q$ 中有全称定义，等价地 $\mathbb Q\setminus\mathbb Z$ 是丢番图集合。全称定义与本次纯存在定义的目标不同。[\[5\]](#ref-koenigsmann)

OpenAI 的9月24日稿及10月6日版本声称证明 $\operatorname{HTP}(\mathbb Q)$ 不可判定；其可读导论采用一列有限检验和 Turing 归约。Sun 的10月19日 arXiv v2 声称把不可判定性限制到86个有理未知数，仍依赖近期算术输入。86不是整数定义的见证数，也不是次数、解高度或时间界。V13 则声称对普通嵌入 $\mathbb Z\subset\mathbb Q$ 本身给出单个存在多项式定义。[\[6\]](#ref-openaiintro), [\[7\]](#ref-openaioct), [\[8\]](#ref-sun)

### 1.3　怎样使用这项新主张

V13 声称其算术接口均在稿件内得到证明，不应把10月11日前稿的“四项算术假设”错误移植给V13。但当前 Lean 说明仅覆盖48个辅助模块；原始大型构造的冻结主目标仍有 `sorry`，且尚不是V13四次构造的完整形式化目标。[\[3\]](#ref-leanstatus)

公开修订记录承认V10在 Kato 应用的索引域和极限类识别之间漏了连接；V11补入了相应论证。记录明确限定修复审查范围，有限检查和内部模型审查也不能替代整条证明链。[\[4\]](#ref-repair)

据此，后文采用明确接口：

#### 定义 1.1：本札记的条件接口

$\mathsf H_{\mathbb Z/\mathbb Q}$ 表示：已给定一个具体有限描述的整数多项式 $P(t,\mathbf w)$，并且对每个 $t\in\mathbb Q$，

$$
t\in\mathbb Z\iff\exists\mathbf w\in\mathbb Q^m\ P(t,\mathbf w)=0.
$$

此处的条件化是本文使用证据的方式；它不把原稿的无条件定理陈述改写成作者自称的条件定理。

<a id="section-2"></a>

## 2　丢番图定义是一种存在性投影

#### 定义 2.1：丢番图关系

关系 $R\subseteq\mathbb Q^k$ 称为丢番图的，若存在一个固定整数系数多项式 $F$，使

$$
R(\mathbf x)\iff\exists\mathbf y\in\mathbb Q^r\ F(\mathbf x,\mathbf y)=0.
$$

允许有理系数时，清除常数分母即得到整数系数版本。

这要求全部辅助变量都在 $\mathbb Q$ 中量化。直接写“存在整数 $a,b$ 且 $t=a/b$”没有消除整数谓词，不能承担这个定义任务。

设 $V_F(\mathbb Q)=\{(\mathbf x,\mathbf y):F(\mathbf x,\mathbf y)=0\}$。上述关系就是坐标投影

$$
R=\pi\bigl(V_F(\mathbb Q)\bigr).
$$

这精确表达“输入纤维中存在一个合法见证”。

#### 说明 2.2：与观察商的区别

UPPM-RG 001 的观察商判据要求既定目标读出在每个观察纤维内恒定。存在性投影要求纤维中至少一个见证成立，二者需要分别验证。例如，在全部候选对组成的环境空间上取 $q:\mathbb Q^2\to\mathbb Q$、$q(t,w)=t$，并令 $C(t,w)$ 为 $w^2=t$。在 $t=1$ 的同一候选纤维内，$w=1$ 满足而 $w=0$ 不满足。因此逐点命题 $C$ 不在该纤维上恒定；$\exists w\,C(t,w)$ 则是另一个目标。这里的环境空间与只包含合法零点的 $V_F(\mathbb Q)$ 不同。

#### 定义 2.3：存在性保真编译

从关系 $R(\mathbf x)$ 到约束系统 $\mathcal C(\mathbf x,\mathbf y)$ 的编译，若满足

$$
R(\mathbf x)\iff\exists\mathbf y\ \mathcal C(\mathbf x,\mathbf y),
$$

则称其对输入存在性保真。健全性与完备性必须分别证明；不同子关系的私有见证在组合时须重命名，共享参数则须保留同一身份。

<a id="section-3"></a>

## 3　整数算术如何进入有理方程

#### 定理 3.1：方程求解的直接编译，依赖 $\mathsf H_{\mathbb Z/\mathbb Q}$

给定 $f\in\mathbb Z[x_1,\ldots,x_n]$，令每个 $x_i$ 使用独立见证块 $\mathbf w_i$，并定义

$$
F_f(\mathbf x,\mathbf w_1,\ldots,\mathbf w_n)
 =f(\mathbf x)^2+\sum_{i=1}^nP(x_i,\mathbf w_i)^2.
$$

则

$$
\exists\mathbf z\in\mathbb Z^n\ f(\mathbf z)=0
 \iff
 \exists(\mathbf x,\mathbf w_1,\ldots,\mathbf w_n)\in\mathbb Q^{n(m+1)}\ F_f=0.
$$

编译过程有效且有限。

**证明。**

有整数解时，为每个整数坐标选取 $P$ 的见证，即得右侧。有理平方均非负；故右侧为零使全部平方项为零。$\mathsf H_{\mathbb Z/\mathbb Q}$ 强制各 $x_i$ 为整数，且 $f(\mathbf x)=0$。固定多项式的替换和平方求和均为有效符号运算。

$\square$

Davis–Putnam–Robinson–Matiyasevich 定理给出每个可枚举整数关系的丢番图表示，整数方程可解性由此不可判定。本文将该经典定理作为已知结果引用。[\[9\]](#ref-matiyasevich)

#### 推论 3.2：通用多项式与归约强度，依赖 $\mathsf H_{\mathbb Z/\mathbb Q}$

存在固定整数系数多项式 $U(e,\mathbf z)$，满足

$$
\exists\mathbf z\in\mathbb Q^s\ U(e,\mathbf z)=0
 \iff \text{第 $e$ 个程序在空输入上停机},\qquad e\in\mathbb N.
$$

因而 $\operatorname{HTP}(\mathbb Q)$ 与停机集 $0'$ 多对一等价。

**证明。**

对停机关系应用DPRM，再按定理3.1编译每个整数见证。自然数见证可用整数四平方和编码，必要时作加一平移。所得 $U$ 固定，只有 $e$ 变化。反方向，给定有理方程，枚举所有有理元组并精确代入；程序恰在有解时停机。

$\square$

这里得到的 $U$ 并不自动继承 $P_{394}$ 的变量数和次数。上述直接多对一归约也应与OpenAI先前声称的 Turing 度结论区分。[\[1\]](#ref-v13), [\[6\]](#ref-openaiintro)

#### 推论 3.3：固定形式系统的可证明性，依赖 $\mathsf H_{\mathbb Z/\mathbb Q}$

对一个固定的有效形式系统 $T$，若其可证明句子编码集合可枚举，则存在固定整数多项式 $W_T(a,\mathbf z)$，使合法句子编码 $a$ 满足

$$
T\vdash A_a\iff\exists\mathbf z\in\mathbb Q^s\ W_T(a,\mathbf z)=0.
$$

**证明。**

对可证明句子编码的可枚举集合应用DPRM，再使用定理3.1的整数见证替换。

$\square$

这给通用证明搜索一个统一的算术表示接口。它表示的是固定系统内的可证明性；若另有语义可靠性，才能推出相应真值。该表示没有把全部数学真理变成一个可枚举集合，也不自行提供更快的证书搜索。

#### 推论 3.4：拓扑后果，依赖 $\mathsf H_{\mathbb Z/\mathbb Q}$

存在定义于 $\mathbb Q$ 的仿射代数集，其有理点在实点中的闭包有无穷多个连通分支。

**证明。**

取 $V=\{P(t,\mathbf w)=0\}$，$C=\overline{V(\mathbb Q)}\subset V(\mathbb R)$，$\pi$ 为 $t$ 坐标投影。因 $\mathbb Z$ 在 $\mathbb R$ 中闭且 $\pi$ 连续，$\pi(C)\subseteq\mathbb Z$；每个整数已由一个有理点实现，故 $\pi(C)=\mathbb Z$。每个连通分支的像是 $\mathbb Z$ 的连通子集，只能是单点。不同整数因此需要不同分支。

$\square$

这是Mazur有限连通分支猜想所遇到的经典投影障碍；V13也明确列出该条件后果。[\[1\]](#ref-v13)

<a id="section-4"></a>

## 4　二元运算、三元约束与四次方程

#### 定理 4.1：局部算术门编译，无需 $\mathsf H_{\mathbb Z/\mathbb Q}$

每个由整数常数、变量、加法和乘法组成的有限算术电路，都能有效变成局部二次方程组。每条门约束至多涉及三个坐标。给定输入后，中间坐标唯一对应电路求值。

**证明。**

对每个门引入其输出坐标 $z$。加法门写为 $z-x-y=0$，乘法门写为 $z-xy=0$，常数门写为 $z-c=0$。按电路拓扑次序归纳即可证明中间值的存在与唯一性。要求输出为零时再加入输出约束。

$\square$

若电路使用除法，必须另加分母守卫 $bu-1=0$，再用 $bz-a=0$ 表示 $z=a/b$；直接消去分母而丢掉 $b\ne0$ 会改变解集。只有代数关系而无拓扑定向的通用约束网络，也不自动具有上述唯一中间值性质。

设各局部残差为 $r_j$，则在 $\mathbb Q$ 上

$$
\bigwedge_j r_j=0\iff\sum_jr_j^2=0.
$$

每个 $r_j$ 次数至多二，平方和次数至多四。这是经典丢番图编译方法，Matiyasevich 1971年论文已明确给出相应四次化思路。[\[9\]](#ref-matiyasevich)

#### 定理 4.2：固定关系网络仍可不可判定，依赖 $\mathsf H_{\mathbb Z/\mathbb Q}$

存在一个固定的局部算术约束网络，其每条方程至多二次、涉及至多三个坐标。仅改变一个整数输入 $e$ 的值，该网络是否有有理解就不可判定。其变量总数、约束图及某个树分解的宽度均为固定有限常数。

**证明。**

对推论3.2的固定多项式 $U(e,\mathbf z)$，固定一个加乘电路并应用定理4.1。可保留参数坐标并增加 $x_e-e=0$，从而使约束图完全固定。该系统有解恰好等价于相应程序停机。图有限，取包含全部变量的单袋即有固定宽度的树分解；这不声称宽度为一。

$\square$

这给上一稿的有限域树形算法补上了关键边界。三元约束、固定维数或固定图宽不保证可判定性；原算法还需要有限、有效可枚举的取值域，以及可实际构造和处理的分隔关系表。在 $\mathbb Q$ 上，一只袋中的允许记录集合可能无限，甚至其非空性本身就编码了困难问题。

<a id="section-5"></a>

## 5　从近似到精确：高度与分离阈值

#### 定义 5.1：有理高度

把 $t=a/b$ 写成最简分数且 $b>0$，定义

$$
H(t)=\max(|a|,b),\qquad h(t)=\log H(t).
$$

#### 引理 5.2：整数目标的精确分离

若 $n\in\mathbb Z$、$t\in\mathbb Q$、$h(t)\le B$ 且

$$
|t-n|<e^{-B},
$$

则 $t=n$。

**证明。**

若 $t\ne n$，整数 $a-nb$ 非零，故

$$
|t-n|=\frac{|a-nb|}{b}\ge\frac1b\ge\frac1{H(t)}
 \ge e^{-B},
$$

矛盾。严格不等号不可省略。

$\square$

对于两个不同的高度至多 $H$ 的有理数，也有 $|a/b-c/d|\ge1/H^2$。因此明确的分母界会产生有限精度下可使用的离散间隔。

#### 引理 5.3：多项式残差的精确间隔

设非零 $f\in\mathbb Z[x_1,\ldots,x_m]$，$d_i=\deg_{x_i}f$，$H\ge1$。若各 $q_i=a_i/b_i$ 为最简分数、$b_i>0$ 且 $H(q_i)\le H$，则

$$
f(\mathbf q)\ne0\quad\Longrightarrow\quad
 |f(\mathbf q)|\ge H^{-\sum_i d_i}.
$$

**证明。**

乘以 $\prod_i b_i^{d_i}$ 后得到一个非零整数，绝对值至少一；分母乘积至多为 $H^{\sum_i d_i}$。

$\square$

因此，带有认证误差的残差计算可以在已知高度范围内产生严格零值证书。零多项式可直接识别并单独处理。 例如若 $|f(\mathbf q)-\widetilde f|\le\varepsilon$，且 $|\widetilde f|+\varepsilon<H^{-\sum_i d_i}$，便可推出 $f(\mathbf q)=0$。

V13 的一个关键接口正采用这个机制：椭圆点先编码整数指标 $n$；局部检验给出 $h(t)\le B(n,\kappa)$；精度关系给出 $|t-n|<e^{-B(n,\kappa)}$；两个关系必须使用同一辅助移位 $\kappa$，私有见证分别保存。于是 $t=n$。原始构造的 $B$ 由明确整数常数与多项式值给出，而其建立依赖稿件深层算术论证。[\[1\]](#ref-v13)

本文独立核对了引理5.2，但这不同时认证稿件如何以纯存在有理方程实现高度检验、精度条件、移位存在性及其组合。

#### 例 5.4：没有高度界时的失效

取 $t_N=n+1/N$。它无限接近 $n$，但每个有限 $N$ 都有 $t_N\ne n$。另取任意趋近 $\sqrt2$ 的有理数列 $q_N$，则 $(q_N^2-2)^2\to0$，而 $x^2-2=0$ 在 $\mathbb Q$ 中无解。实极限与有理解的存在性有不同的对象范围。

#### 例 5.5：约分和射影化的守卫

多项式 $f(x,y)=x^2+1$ 在 $\mathbb Q^2$ 中无零点。二次齐次化为 $X^2+T^2=0$ 后，射影点 $[X:Y:T]=[0:1:0]$ 却是有理点。恢复仿射问题必须保留 $T\ne0$，例如附加 $Ts-1=0$。归一化或引入无穷远点不能自动保留原始可解性。

<a id="section-6"></a>

## 6　见证大小、不可判定性与反证证书

以下固定通常的有限二进制编码。把所有长度至多 $B$ 的有理数表示枚举并约分，可得一个有限可计算集合。方程元数也包含在输入描述内。 对固定模板 $U(e,\mathbf z)$，输入长度包括参数 $e$ 的二进制编码；对固定模板 $P(t,\mathbf w)$，则包括 $t$ 的分数编码。

#### 定理 6.1：有效见证界判据

对一个语法可判定、代入检查可判定的有理方程类 $\mathcal F$，以下等价：

1.  $\mathcal F$ 中的有理解存在性可判定；

2.  存在全可计算函数 $b:\mathbb N\to\mathbb N$，使每个有解的 $f\in\mathcal F$ 都有一个见证元组，各坐标编码长度至多 $b(\operatorname{len}f)$。

**证明。**

由2到1：计算界并穷举有限候选集。由1到2：对长度至多 $n$ 的有限多个合法描述先判定是否有解，再对所有有解者并行枚举见证。每项都终止，取找到的最大坐标长度即得到可计算的 $b(n)$；没有有解项时取零。

$\square$

#### 推论 6.2：通用有理求解没有统一递归见证界，依赖 $\mathsf H_{\mathbb Z/\mathbb Q}$

一般有理多项式可解性，以及固定通用多项式 $U(e,\mathbf z)$ 的参数问题，都不满足定理6.1的第二项。

这不是“界很大”的陈述。对任意给定的全可计算候选界，总有一个有解输入的全部见证超出它。

#### 说明 6.3：不要误用于整数成员多项式

固定谓词 $t\in\mathbb Z$ 本身可判定：最简分数分母为一即可。在 $\mathsf H_{\mathbb Z/\mathbb Q}$ 下，对固定的 $P(t,\mathbf w)$，按有限输入长度枚举所有整数参数并并行搜索其见证，确实可以得到某个可计算的最坏见证界；此论证不提供实用或多项式界。不可计算界结论针对通用求解问题或通用 $U$，不能直接贴到 $P_{394}$ 的整数成员参数问题上。

#### 定理 6.4：完备有限反证系统的障碍，依赖 $\mathsf H_{\mathbb Z/\mathbb Q}$

不存在一个可判定的有限证书检查器，对每个无有理解的整数多项式都接受至少一个反证证书，同时对任何有解多项式都不接受反证。

**证明。**

若存在，并行执行有理零点枚举与有限反证证书枚举。每个输入恰有一边最终成功，从而判定 $\operatorname{HTP}(\mathbb Q)$，与推论3.2矛盾。

$\square$

这明确了通用证明机器的一个边界：正例见证可枚举；可使用可靠但不覆盖所有负例的反证模块；一般输入需要允许未决或持续搜索。把全部答案预装在无限静态图中，会另外要求对该图的有效访问方式。

<a id="section-7"></a>

## 7　存在性可以变成概率正，但仍需要停止间隔

#### 定理 7.1：满支撑概率编码，无需 $\mathsf H_{\mathbb Z/\mathbb Q}$ 构造

对每个元数 $m$ 固定一个无遗漏的可计算有理元组枚举 $\mathbf w_1,\mathbf w_2,\ldots$，令

$$
p(f)=\sum_{j\ge1}2^{-j}\,\mathbf1_{\{f(\mathbf w_j)=0\}}.
$$

则 $p(f)$ 是由 $f$ 一致可计算的实数，并且

$$
p(f)>0\iff f\text{ 有有理零点}.
$$

**证明。**

前 $N$ 项可精确计算，尾和至多 $2^{-N}$，给出有效误差界。若存在一个有理零点，它在某个有限位置出现，贡献一个严格正权重；反方向显然。

$\square$

#### 推论 7.2：可计算概率与不可判定零值，依赖 $\mathsf H_{\mathbb Z/\mathbb Q}$

上述 $p(f)$ 的精确零值判定不可由全算法完成。也不存在全可计算的正有理函数 $g(f)$，保证所有 $p(f)>0$ 的输入都有 $p(f)\ge g(f)$。

**证明。**

精确判零将判定 $\operatorname{HTP}(\mathbb Q)$。若有 $g$，选 $N$ 使 $2^{-N}<g(f)/2$。当 $p=0$ 时部分和为零；当 $p\ge g$ 时部分和大于 $g/2$，又得到判定器。

$\square$

这给“概率表达存在性”一个严格而有条件的实现：人为指定满支撑离散分布，就能让存在等价于正概率。可是概率值可以计算到任意精度，仍不保证能决定它是否恰为零。有限布尔空间中 $2^{-n}$ 的统一离散间隔，在这里已不再成立。这个逻辑构造也不涉及量子 Born 规则的物理推导。

<a id="section-8"></a>

## 8　Fibonacci：趋零残差的下一层关系

Matiyasevich 的经典证明确实使用偶数指标 Fibonacci 关系的丢番图性和指数增长。这是与AURIC FIB研究方向的实质连接，历史上已有清楚的算术机制。[\[9\]](#ref-matiyasevich)

令

$$
u_n=F_{2n},\qquad u_0=0,\quad u_1=1,\quad
 u_{n+1}=3u_n-u_{n-1}\quad(n\ge1).
$$

#### 定理 8.1：精确不变量与归一化残差，无需 $\mathsf H_{\mathbb Z/\mathbb Q}$

对所有 $n\ge0$，

$$
u_{n+1}^2-3u_nu_{n+1}+u_n^2=1.
$$

当 $n\ge1$，令 $r_n=u_{n+1}/u_n$，则

$$
\boxed{\quad u_n^2\bigl(r_n^2-3r_n+1\bigr)=1.\quad}
$$

**证明。**

起始值为 $1$。将下一对 $(u_{n+1},3u_{n+1}-u_n)$ 代入该二次型，展开后仍得 $u_{n+1}^2-3u_nu_{n+1}+u_n^2$，故归纳成立。除以 $u_n^2>0$ 得后一式。

$\square$

设 $\varphi=(1+\sqrt5)/2$。由 Fibonacci 递推的特征根或Binet公式，$r_n\to\varphi^2$，因而

$$
r_n^2-3r_n+1=\frac1{u_n^2}\longrightarrow0.
$$

趋零残差和精确关系并存：保留尺度 $u_n^2$ 后，下一层读出恒等于1；若只保留极限 $\varphi^2$，原先的尺度与索引就不再由这个极限单独区分。

这支持在具体模型中寻找归一化后保留下来的关系。若希望据此改进算法，还需证明该关系能够提供目标所需的见证界、搜索顺序或有效停止阈值。指数增长关系也可以用于编码复杂计算，不能只凭增长或自相似性推出快速求解。

上述二次型的判别式为5，是不定型，不能直接当作正定球面范数。另有 $\log_2F_{2n}=\Theta(n)$：当索引 $n$ 按二进制输入时，仅输出完整整数就可能对输入长度具有指数级位数，算术操作计数需要同时保留这种位成本。

<a id="section-9"></a>

## 9　把问题重新放回 $P/NP$ 的适用范围

$P$ 与 $NP$ 讨论有限字符串上的可判定问题。通用 $\operatorname{HTP}(\mathbb Q)$ 在 $\mathsf H_{\mathbb Z/\mathbb Q}$ 下不可判定，因此它既不在 $P$ 也不在 $NP$；这不回答两类之间是否相等。

#### 定义 9.1：有见证预算的二次约束问题

输入为有限有理算术门约束系统 $\mathcal C$ 与一元编码预算 $1^B$。询问是否存在满足约束的有理赋值，使每个最简分数的分子绝对值和正分母都小于 $2^B$。参数和整数常数按二进制给出。 约束允许加法、乘法、等式和常数关系，变量可以共享；不要求整个约束网络是有向无环的单向求值电路。

#### 定理 9.2：有界二次约束可满足性，无需 $\mathsf H_{\mathbb Z/\mathbb Q}$

上述问题是 NP 完全的。

**证明。**

证书给出每个分子的符号、分子及分母，长度为变量数乘以 $O(B)$。用整数交叉相乘检查加法、乘法与常数约束，位复杂度对输入与证书长度为多项式；预算采用一元编码保证它属于输入规模。

对 NP 困难性，从3-SAT归约。给每个布尔变量加入 $x(x-1)=0$，在域 $\mathbb Q$ 中强制 $x\in\{0,1\}$；用补变量表示否定文字。对子句文字 $\ell_1,\ell_2,\ell_3$，引入 $u=(1-\ell_1)(1-\ell_2)$，再要求 $u(1-\ell_3)=0$。它恰在子句满足时成立。中间值均为0或1，取固定 $B=2$ 足够。全部约束可展开为允许的至多三坐标二次算术门。

$\square$

这个有界版本才适合比较启发式、查表、缓存、树分解和几何搜索。对具体问题族，应同时报告变量数、系数位长、分母预算、图宽、预处理时间、搜索时间和证书检查成本。标准复杂性模型的统一性要求参见Cook。[\[10\]](#ref-cook)

若将预算 $B$ 二进制编码，$O(B)$ 长度的见证可能对输入的 $\log B$ 指数长，上述 NP 成员证明就不能原样沿用。有限门数同样不替代门寄存器数值精度的计费。

#### 定理 9.3：高度界与树分解给出正面的求解结果

对一个有限有理约束问题，假设已获得整数 $H\ge1$，保证原问题有解时必有各坐标高度至多 $H$ 的解。再给定合法树分解，含 $N$ 个袋、最大袋大小 $k$，局部约束在编码长度及输入位长内可多项式时间检查。则存在保守时间界

$$
\operatorname{poly}(|I|,N,k,\log H)\,(3H^2)^{2k}
$$

的求解算法。若高度界和分解可以多项式时间构造、$N$ 为多项式，且

$$
k\log(2H)=O(\log |I|),
$$

则该问题类属于 $P$。

**证明。**

无变量时直接检查常数约束；以下设 $k\ge1$。枚举

$$
D_H=\{a/b:|a|\le H,\ 1\le b\le H,\ \gcd(a,b)=1\}.
$$

其大小至多 $(2H+1)H\le3H^2$。在每只袋上枚举 $D_H$ 赋值，检查所属约束；自底向上保留能与每个子袋相容的记录。运行交集保证回溯拼接正确。逐对匹配至多花费 $|D_H|^{2k}$ 乘以多项式因子，得到上界。完整高度界保证有限域替换保持原问题可解性。最后的条件使指数因子也是输入规模的多项式。

$\square$

这里使用 $\log(2H)$ 保留 $H=1$ 边界：即使 $H=1$，可选值也有 $-1,0,1$，不能误把域大小看成一。上述界一般对数值高度敏感；单有二进制编码的巨大 $H$ 并不保证多项式时间。

<a id="section-10"></a>

## 10　UPPM-RG 002 的完整候选原则与项目接口

下面是适用于本研究框架的定义约束，不宣称由它们唯一推出自然界的量子公理：

1.  **有效载体。** 输入、程序、整数与有理数编码、资源预算均有有限描述；观察者与工作记忆进入模型。

2.  **内生证据。** 新对象保留来源，结论保留证书；未证明的新主张保留为显式依赖，不被编译步骤悄悄视为定理。

3.  **分类型保真。** 分别证明观察商的目标恢复、动作保真，以及存在性编译的健全性与完备性。

4.  **合法组合。** 共享参数保持同一身份，私有见证独立重命名；除法、坐标图和射影回读保留非零守卫及例外分支。

5.  **有效精确化。** 从近似到相等须有高度、误差和严格分离界；归一化须保存目标依赖的尺度或重建信息。

6.  **有界求解与诚实停止。** 分别计量表示、构造、搜索、执行和核验；全算法终止要有独立依据，通用场景允许未决。

### 10.1　与当前仓库的具体连接

本轮固定用户仓库的 `dev` 提交为

`69a777d001b184cfce81bed62bad140fb93706d2`.

读取了该提交的 `docs/VISION.md`，并取得AURIC静态相容纤维理论文档进行相关段落检索。项目明确区分恢复函数存在与算法成本，也区分局部拼接与唯一恢复；这与本文的接口区分一致。[\[11\]](#ref-project)

AURIC稿的定义4.1以目标响应族定义最小响应商；定义5.1给出局部约束赋值，第5节进一步区分“边界读出单射”和“某个边界值可实现”。[\[12\]](#ref-auric) 因此 $\mathsf H_{\mathbb Z/\mathbb Q}$ 可直接写入其语言：令

$$
S_P=\{(t,\mathbf w)\in\mathbb Q^{m+1}:P(t,\mathbf w)=0\},
 \qquad\pi(t,\mathbf w)=t,
$$

则 $\pi(S_P)=\mathbb Z$。也就是：一个有限有理约束系统的可实现边界，恰为普通整数集合。合法见证是否存在、见证是否唯一、如何找到它，以及所需成本，仍是分别陈述的目标。

可直接形成下一轮正式模块的工作是：

1.  形式化有理高度分离引理，覆盖最简分母、零分子与严格边界；

2.  定义加乘电路的局部关系编译，证明输入投影等价、私有见证范围与除法守卫；

3.  为有界见证问题构造可信检查器，再在明确问题类上寻找可证明的高度界和可控分隔关系；

4.  将 $\mathsf H_{\mathbb Z/\mathbb Q}$ 保持为单独依赖接口，直到选定版本的算术主定理经过足够审查或完整形式化。

其中前两项不依赖新预印本的真伪；第三项直接提供可比较的算法问题；第四项确保研究在新结果修订时仍可重建。

### 10.2　白话描述

一串有限的加法和乘法规则，可以把非常复杂的问题装进一个方程。装进去以后，有解就意味着存在一份有限证据；但证据藏得多深、要用多少位数、什么时候能确定没有证据，仍是另外几件事。能把所有关系拆成小块，是一种表达能力；能给小块的数值范围和整个搜索过程设定可靠边界，才开始得到求解能力。归一化时保留那些承载答案的尺度，近似时给出跨不过去的分离间隔，证明机器就能在可处理的范围内严格停止，并对范围之外保留未决状态。

<a id="section-A"></a>

## A　引用与审查的边界

本文对V13的陈述、数字和公开审查状态作来源核对；未对其全部高度定理、Euler-system输入、素数模式论证及最终组合给出独立认证。本文证明的条件性结论只依赖明确接口 $\mathsf H_{\mathbb Z/\mathbb Q}$ 与注明的经典结果。本文所给普通数学证明尚未逐项转写为Lean内核证明。也未据此证明 $P=NP$、$P\ne NP$、黎曼猜想或量子公理的唯一来源。

V13 固定源码的SHA-256为

`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`

主稿日期与仓库提交日期分别记录；前者为11月7日，后者为11月8日。固定提交便于复核，不把某次下载成功视为内容正确性的证据。

## 参考资料与核验范围

<a id="ref-v13"></a>

\[1\] *$\mathbb Z$ is Diophantine in $\mathbb Q$*, Version 13, 2026-11-07. 固定提交下的稿件；本轮阅读摘要、组合接口、六接触高度声明、精确值桥、条件后果和V13编译定理等相关段落。 <https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/manuscripts/quartic_v13.tex>.

<a id="ref-guide"></a>

\[2\] V13 construction guide. 总变量、见证、残差、系数表和检查范围。 <https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/docs/manuscript-revisions/version13/GUIDE.md>.

<a id="ref-leanstatus"></a>

\[3\] Accepted Lean helper snapshot. 本轮读取其形式化覆盖与未关闭义务说明。 <https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/lean/README.md>.

<a id="ref-repair"></a>

\[4\] Version 11: Kato application and review protocol；Issue 2及11月8日作者回复。 <https://github.com/elliotglazer/diophantine-z-q/issues/2>; <https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/docs/manuscript-revisions/version11/README.md>.

<a id="ref-koenigsmann"></a>

\[5\] J. Koenigsmann, Defining $\mathbb Z$ in $\mathbb Q$.  *Annals of Mathematics*  183 (2016), 73–93. 重点核对Theorem 1、Corollary 2和存在定义的历史定位。 <https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n1-p02-p.pdf>.

<a id="ref-openaiintro"></a>

\[6\] OpenAI, Hilbert’s tenth problem over the rational numbers, 2026-09-24. 本轮读取导论的定理、有限检验接口与依赖；未独立核验深层算术证明。 <https://github.com/openai/math/blob/main/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/01-introduction.tex>.

<a id="ref-openaioct"></a>

\[7\] OpenAI, 同题10月6日版本说明：更新到修订稿引用。 <https://github.com/openai/math/blob/main/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/README.md>.

<a id="ref-sun"></a>

\[8\] Zhi-Wei Sun, 86 unknowns for Hilbert’s tenth problem over the rationals. arXiv:2610.20691v2, 2026-10-19. 本轮核对陈述、变量数范围与上游依赖。 <https://arxiv.org/abs/2610.20691v2>.

<a id="ref-matiyasevich"></a>

\[9\] Yu. V. Matiyasevich, Diophantine representation of enumerable predicates.  *Mathematics of the USSR-Izvestiya*  5 (1971), 1–28. 基本定理；第6页四次化；第8页起偶数指标Fibonacci关系。 <https://www.mathnet.ru/php/getFT.phtml?jrnid=im&option_lang=eng&paperid=1910&what=fullteng>.

<a id="ref-cook"></a>

\[10\] S. Cook, The P versus NP Problem. Clay Mathematics Institute. <https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf>.

<a id="ref-project"></a>

\[11\] The Omega Institute, trureturing, `docs/VISION.md`. 固定提交下的恢复、局部整体、证据与成本说明。 <https://github.com/the-omega-institute/trureturing/blob/69a777d001b184cfce81bed62bad140fb93706d2/docs/VISION.md>.

<a id="ref-auric"></a>

\[12\] The Omega Institute, AURIC $\Omega$ 静态相融纤维理论。固定提交下第4–5节的响应商、约束赋值和可实现边界；本轮未审查全篇及全部形式化依赖。 <https://github.com/the-omega-institute/trureturing/blob/69a777d001b184cfce81bed62bad140fb93706d2/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md>.

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
## 11. 实际共轭椭圆点的联合返回与绝对密度

**定义 11.1（固定的共轭点与实归一化）。** 令

$$
\begin{gathered}
K=\mathbb Q(\sqrt2),\qquad \sigma(\sqrt2)=-\sqrt2,\qquad
 d=3-\sqrt2,\quad d'=3+\sqrt2,\\
E:y^2=x^3-d^2x,\qquad E^\sigma:y^2=x^3-(d')^2x,\\
R_0=(1+\sqrt2,2\sqrt2),\qquad
P=2R_0=\left(\frac{57-28\sqrt2}{8},\frac{-660+417\sqrt2}{32}\right),\\
E_0:Y^2=X^3-X.
\end{gathered}
$$

在这两个实嵌入中均取正平方根，定义实椭圆曲线群同构

$$
\begin{aligned}
\phi_d:E(\mathbb R)&\longrightarrow E_0(\mathbb R),&
 (x,y)&\longmapsto\left(\frac{x}{d},\frac{y}{d\sqrt d}\right),\\
\phi_{d'}:E^\sigma(\mathbb R)&\longrightarrow E_0(\mathbb R),&
 (x,y)&\longmapsto\left(\frac{x}{d'},\frac{y}{d'\sqrt{d'}}\right),
\end{aligned}
$$

两者均把无穷远点映到无穷远点 $O$。记

$$
P_1=\phi_d(P),\qquad P_2=\phi_{d'}(P^\sigma),\qquad
Q=(P_1,P_2),\qquad C=E_0(\mathbb R)^0.
$$

$C$ 是以 $O$ 为单位元的实连通分支，即 $X\ge1$ 的无界支连同 $O$；它作为紧群同构于 $\mathbb R/\mathbb Z$。记 $\mu$ 为 $C^2$ 上的归一化 Haar 概率，$[n]Q=([n]P_1,[n]P_2)$。这里的曲线、倍点和归一化映射取自 Brox 的固定源码中 “The quadratic-field elliptic curve” 一节：[aggregate trace height，提交 `61b82ccacfbefdff3d6e7cf986d6e6279afa1372`](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex)。

**定义 11.2（固定的局部条件、同余类与计数对象）。** 取任意固定的有限指标集 $S$，允许 $S=\varnothing$。对每个 $v\in S$，固定一个紧 Hausdorff 交换拓扑群 $K_v$、点 $P_v\in K_v$ 及开子群 $U_v\le K_v$，群运算用加法记号。定义

$$
d_v=\operatorname{ord}_{K_v/U_v}(P_v+U_v),\qquad
D=\operatorname{lcm}_{v\in S}d_v,
$$

空集时约定 $D=1$。再固定整数 $M\ge1$、$a\in\mathbb Z$，并置

$$
g=\gcd(M,D),\qquad L=\operatorname{lcm}(M,D).
$$

对固定的 Borel 集 $W\subseteq C^2$ 和正整数 $N$，定义

$$
A_W(N)=\#\{1\le n\le N: n\equiv a\pmod M,
\ [n]P_v\in U_v\ (v\in S),\ [n]Q\in W\}.
$$

计数中的所有点、群、子群、$M,a,W$ 均先固定，再令 $N\to\infty$；各条件共享同一个整数 $n$。

**定理 11.3（实际共轭点的全环面分布与精确局部相容性）。** 对定义 11.1 的固定点，有

$$
\overline{\{[n]Q:n\in\mathbb Z\}}=C^2.
$$

对每个固定的 $M\ge1$、$a\in\mathbb Z$，序列 $([a+Mk]Q)_{k\ge0}$ 在 $C^2$ 上按 $\mu$ 等分布；确切地，对每个连续函数 $f:C^2\to\mathbb C$，

$$
\lim_{H\to\infty}\frac1H\sum_{k=0}^{H-1}f([a+Mk]Q)
=\int_{C^2}f\,d\mu.
$$

因此若 $G=\overline{\mathbb ZQ}$，则 $G=G^0=C^2$，实际轨道闭包的分支数 $|G/G^0|=1$。

对定义 11.2 的每一组固定局部数据，下列条件等价：

1. $g\mid a$。
2. 存在正整数 $n$，使 $n\equiv a\pmod M$ 且所有 $[n]P_v\in U_v$。
3. 对每个 $T\ge0$ 及每个 $C^2$ 中的开单位元邻域 $B$，存在整数 $n>T$，使 $n\equiv a\pmod M$、所有 $[n]P_v\in U_v$，且 $[n]Q\in B$。

更一般地，若 $g\mid a$，每个固定的非空开集 $V\subseteq C^2$ 都有满足这些同余和局部条件的任意晚返回，即对每个 $T\ge0$ 均有相应的 $n>T$ 使 $[n]Q\in V$。对每个固定的边界满足 $\mu(\partial_{C^2}W)=0$ 的 Borel 集 $W$，有以全部正整数为分母的自然密度公式

$$
\lim_{N\to\infty}\frac{A_W(N)}{N}
=
\begin{cases}
\displaystyle\frac{\mu(W)}{\operatorname{lcm}(M,D)},&\gcd(M,D)\mid a,\\[6pt]
0,&\gcd(M,D)\nmid a.
\end{cases}
$$

上述结论的目标为先固定的集合 $W$ 或非空开集 $V$，局部子群也先固定；它不包含随 $n$ 任意缩小的目标。所给极限不指定首个命中指标、差异度的显式上界或未给定局部群的周期数值，也不指定有效高度比较的加性常数或高度与极点不等式。对一个另有可判定成员检验的固定返回条件，存在性与逐项搜索的终止性可以结合；缺少本条给出的数值首命中界，不表示这种有限搜索不可计算。本条的联合返回结论不包含 $\mathsf H_{\mathbb Z/\mathbb Q}$ 的证明，也不包含 Born 规则或量子理论的重建。

本条是将上述固定点的算术独立性、经典等分布与局部同余组合所得的具体综合推导。所用非挠性与更强的 $\mathbb Z[i]$ 模挠独立性由 Brox 上述一节证明；字符判据与等分布是经典中间结果，不作为新的算术或等分布定理主张优先权。经典来源为 [Kronecker 字符判据，固定修订 47528](https://encyclopediaofmath.org/index.php?title=Kronecker_theorem&oldid=47528) 与 H. Weyl，*Über die Gleichverteilung von Zahlen mod. Eins*，[DOI:10.1007/BF01475864](https://doi.org/10.1007/BF01475864)；字符求和与连续逼近的同类论证亦见本库 [ARITHMETIC_BOUNDARY_QUANTIZATION，第 35.4–35.8 条](ARITHMETIC_BOUNDARY_QUANTIZATION.md)。

**证明。** 首先 $d,d'>0$，故上述正实归一化有定义。代入得 $R_0\in E(K)$；切线斜率为 $3-\sqrt2/4$，倍点公式给出所列 $P$。直接化简归一化横坐标，得到

$$
X(P_1)=\frac{115-27\sqrt2}{56}>1,\qquad
X(P_2)=\frac{115+27\sqrt2}{56}>1.
$$

第一个严格不等式来自 $59>27\sqrt2$，第二个随即成立。因此 $P_1,P_2\in C$，$Q\in C^2$。

使用 Brox “The quadratic-field elliptic curve” 一节已经证明的非挠性与独立性，其所需整数系数特例是

$$
[r]P_1+[s]P_2\text{ 为挠点},\quad (r,s)\in\mathbb Z^2
\quad\Longrightarrow\quad r=s=0.
$$

源文的独立性证明在 $K(i)$ 上利用 $d,d'$ 的平方类独立性：两者的范数均为 $7$，且 $dd'=7$ 在 $K$ 中不是平方；正的 $K$ 元素若在 $K(i)$ 中是平方，则已在 $K$ 中是平方。因此存在固定 $\sqrt d$ 而反转 $\sqrt{d'}$ 符号的自同构，它固定 $P_1$、把 $P_2$ 变为 $-P_2$。对模挠关系作用此自同构并相减，得到 $[2s]P_2$ 为挠点；非挠性迫使 $s=0$，再得 $r=0$。这些平方类与换号步骤均为上述来源中的论证。这里仅复用它们给出的整数独立性，不需要计算完整 Mordell–Weil 群或复乘结构。

选择同一个紧群同构 $\theta:C\to\mathbb R/\mathbb Z$，并选 $\alpha_1,\alpha_2\in\mathbb R$，使 $\theta(P_j)=\alpha_j+\mathbb Z$。对任意非零 $m=(m_1,m_2)\in\mathbb Z^2$，有

$$
m_1\alpha_1+m_2\alpha_2\notin\mathbb Q.
$$

否则乘以一个正分母 $q$，得到 $[qm_1]P_1+[qm_2]P_2=O$，与整数独立性矛盾。特别地，对任意 $M\ge1$，

$$
z_m=\exp\bigl(2\pi i M(m_1\alpha_1+m_2\alpha_2)\bigr)\ne1.
$$

令 $\chi_m$ 为 $C^2$ 上经 $\theta^2$ 对应于 $m$ 的字符。几何级数给出

$$
\begin{aligned}
\frac1H\sum_{k=0}^{H-1}\chi_m([a+Mk]Q)
&=\exp\bigl(2\pi i a(m_1\alpha_1+m_2\alpha_2)\bigr)
\frac{1-z_m^H}{H(1-z_m)},\\
\left|\frac1H\sum_{k=0}^{H-1}\chi_m([a+Mk]Q)\right|
&\le\frac{2}{H|1-z_m|}\longrightarrow0.
\end{aligned}
$$

非平凡字符的 Haar 积分为零：将积分平移一个字符值不为 $1$ 的群元素，即知积分等于自身乘以该字符值。平凡字符的平均与积分均为 $1$。有限字符线性组合构成含常数、对复共轭封闭且分离点的代数，由 Stone–Weierstrass 定理一致稠密于 $C(C^2)$。对连续 $f$ 用这样的组合一致逼近，平均误差和积分误差各不超过一致逼近误差，于是得到所述连续函数等分布。这也说明 $a<0$ 无碍；起始有限多个非正指标不影响任一正尾的极限。

每个非空开集 $V\subseteq C^2$ 有正 Haar 测度：若其测度为零，紧性给出的有限个平移覆盖会使 $\mu(C^2)=0$。在 $V$ 内取一个非负连续函数 $f$，使其支集包含于 $V$，且在某个非空开集上严格为正，则 $\int f\,d\mu>0$。等分布说明任一上述进程有无穷多个落在 $V$ 内的项；删去有限项后仍成立。因此每一进程的正尾均稠密，取 $a=0,M=1$ 即得 $\overline{\mathbb ZQ}=C^2$。$C^2$ 连通，故 $G/G^0$ 平凡。

为从连续函数推广到边界零测的 $W$，注意

$$
W^\circ\subseteq W\subseteq\overline W,\qquad
\mu(W^\circ)=\mu(W)=\mu(\overline W).
$$

紧度量空间上的 Haar 概率为正则 Borel 测度。对 $W^\circ$ 和 $\overline W$ 作内外逼近，并用连续函数分离闭集，可对每个 $\varepsilon>0$ 选择连续 $f_-,f_+$，使

$$
0\le f_-\le\mathbf1_W\le f_+\le1,\qquad
\int(f_+-f_-)\,d\mu<\varepsilon.
$$

对二者应用连续等分布，再夹逼并令 $\varepsilon\downarrow0$，得到沿每个固定进程的 $W$ 访问比例为 $\mu(W)$。$W=\varnothing$ 或 $W=C^2$ 也直接满足此结论。

现在处理局部条件。每个开子群 $U_v$ 的陪集构成开覆盖，紧性给出有限子覆盖，所以 $K_v/U_v$ 有限，$d_v$ 是有限正整数。由元素阶的定义，对任意 $n\in\mathbb Z$，

$$
[n]P_v\in U_v\iff d_v\mid n,
\qquad
\bigl([n]P_v\in U_v\text{ 对所有 }v\in S\bigr)\iff D\mid n.
$$

$S=\varnothing$ 时右侧是 $1\mid n$，恰好对应空合取。于是局部条件与指定同余类合为

$$
n\equiv a\pmod M,\qquad n\equiv0\pmod D.
$$

有解必有 $g\mid a$。反之若 $g\mid a$，写 $n=Dt$，则

$$
(D/g)t\equiv a/g\pmod{M/g}
$$

有解，因为 $D/g$ 与 $M/g$ 互素；模数为 $1$ 时条件自动成立。任取一个解 $n_0$，两解之差同时被 $M,D$ 整除，故全部整数解恰为一个模 $L$ 的类 $n_0+L\mathbb Z$。它包含任意大的正整数。这里得到的是最小公倍数 $L$，不要求各局部周期之间或它们与 $M$ 互素。

若 $g\mid a$，取唯一代表 $b\in\{1,\ldots,L\}$ 满足 $b\equiv n_0\pmod L$；其全部正解为 $b+Lk$，$k\ge0$。在 $1\le n\le N$ 中的解数 $H_N$ 满足

$$
H_N=N/L+O(1),\qquad H_N/N\longrightarrow1/L.
$$

用已经证明的进程等分布，得到

$$
\frac{A_W(N)}{N}
=\frac{H_N}{N}\,
\frac1{H_N}\sum_{k=0}^{H_N-1}\mathbf1_W([b+Lk]Q)
\longrightarrow\frac{\mu(W)}L,
$$

其中只需对足够大、$H_N>0$ 的 $N$ 写此式。不相容时不存在任何满足局部与同余条件的整数，故每个 $A_W(N)=0$。对不要求边界零测的非空开集 $V$，改用上述支撑于 $V$ 的非负连续函数，仍得沿 $b+Lk$ 的无穷多次访问，因此有任意晚返回。取 $V=B$ 证明条件 1 推出条件 3；条件 3 取 $T=0,B=C^2$ 即推出条件 2，而条件 2 已证明推出条件 1。密度公式和全部等价关系成立。

最后，固定源码中实际点的另一写法与本条完全对应。令

$$
\begin{gathered}
u=3-2\sqrt2,\qquad d_0=75-53\sqrt2=u^2d,\\
P_0=\left(\frac{1641-1160\sqrt2}{8},
\frac{-123720+87483\sqrt2}{32}\right)
=\bigl(u^2x(P),u^3y(P)\bigr).
\end{gathered}
$$

由于 $u=3-2\sqrt2>0$ 且 $u^\sigma=3+2\sqrt2>0$，正根满足 $\sqrt{d_0}=u\sqrt d$ 及其共轭等式。因此

$$
\left(\frac{x(P_0)}{d_0},\frac{y(P_0)}{d_0\sqrt{d_0}}\right)=P_1,
$$

共轭归一化则等于 $P_2$。这些恒等式由 $({\sqrt2})^2=2$ 直接展开得到。$d_0,P_0$ 见 [Glazer 固定源码，提交 `9c0b3aba60d90fdcac82115f0582a6f52f1054f7`](https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/manuscripts/quartic_v13.tex) 的固定数据；同稿 `v5:real-progression-bridge` 使用一般轨道闭包 $G$ 及其分支数，后面的实际构造使用 $m_0=|G/G^0|$。这里对上述实际共轭点证明了 $G=C^2$，故该实分支数为 $1$，局部条件的剩余障碍精确为 $\gcd(M,D)\mid a$。此对应与联合返回证明只使用所指明的固定数据和独立性，不以该稿全部算术结论为前提。$\square$

## 追加锚（本行以下为增补区）

## 12. 实际共轭点的显式低频分离、统一差异度与矩形等待界

**定义 12.1（不变微分圆坐标、差异度与弧盒）。** 沿用定义 11.1 的实际点 $P_1,P_2$、单位分支 $C$ 和 $Q=(P_1,P_2)$，固定正实根的选择。在 $E_0:Y^2=X^3-X$ 上取不变微分 $\omega=dX/(2Y)$，并置

$$
\Omega=\int_1^\infty\frac{dx}{\sqrt{x^3-x}},\qquad
\mathbb T=\mathbb R/\mathbb Z,\qquad
\theta(R)=\frac1\Omega\int_O^R\omega\pmod{\mathbb Z}.
$$

积分沿 $C$，定向取 $\omega$ 为正；路径的不同选择只改变整周期。约定 $\theta(O)=0$。$C$ 上不变微分的整周期为 $\Omega$，故 $\theta:C\to\mathbb T$ 是紧群同构。记

$$
\alpha=(\theta(P_1),\theta(P_2)),\qquad
\|u\|_{\mathbb T}=\min_{m\in\mathbb Z}|\widetilde u-m|,
$$

其中 $\widetilde u$ 是 $u\in\mathbb T$ 的任一实代表。所有对数均为自然对数。对整数 $L,H\ge1$ 定义

$$
\lambda_L(H)=
\min_{\substack{h=(h_1,h_2)\in\mathbb Z^2\\0<\|h\|_\infty\le H}}
\|L(h_1\alpha_1+h_2\alpha_2)\|_{\mathbb T}.
$$

零频率 $h=(0,0)$ 不进入此最小值；它在字符平均中恒为 $1$。对任意起点 $\beta\in\mathbb T^2$，令 $z_k=\beta+kL\alpha$，$k\in\mathbb Z$。把 $z_k$ 取为 $[0,1)^2$ 中的代表，定义归一化极端差异度

$$
\mathcal D_N(\beta,L)=
\sup_{\substack{0\le s_j\le t_j\le1\\j=1,2}}
\left|
\frac1N\#\{0\le k<N:z_k\in[s_1,t_1)\times[s_2,t_2)\}
-(t_1-s_1)(t_2-s_2)
\right|,
\qquad N\in\mathbb Z_{\ge1}.
$$

这里的盒子不要求以原点为顶点，空盒也允许。这正是 Dick–Pillichshammer，*Digital Nets and Sequences: Discrepancy Theory and Quasi-Monte Carlo Integration*，[所引预印本](https://web.maths.unsw.edu.au/~josefdick/preprints/DP_book_preprint.pdf) 印刷页 72、定义 3.13 的极端差异度。

令 $q:\mathbb R\to\mathbb T$ 为商映射。长度 $0<\ell\le1$ 的半开弧和开弧分别指 $q([c,c+\ell))$ 与 $q((c,c+\ell))$；跨过坐标切口 $0$ 时仍按这一定义，不把它截成较短的弧。长度 $1$ 的半开弧是全圆，长度 $1$ 的开弧是去掉 $q(c)$ 的圆；全圆本身也允许作为一个弧因子。长度 $0$ 的半开弧与开弧均约定为空集，单点集合的 Haar 测度为 $0$。弧盒 $\mathcal B=I_1\times I_2\subseteq\mathbb T^2$ 的面积是两因子长度的乘积，全圆因子的长度为 $1$。对应的圆坐标目标为 $B_C=(\theta\times\theta)^{-1}(\mathcal B)\subseteq C^2$，其 Haar 面积等于 $|\mathcal B|$。下面的正面积结论也适用于改变弧端点开闭的盒子，因为它们包含面积任意接近自身面积的内部半开弧盒。

高度采用绝对对数射影高度。若数域 $F_*$ 含有 $U,V$，则

$$
h([U:V])=\frac1{[F_*:\mathbb Q]}
\sum_w[F_{*,w}:\mathbb Q_w]\log\max(|U|_w,|V|_w).
$$

有限处的绝对值延拓 $|p|_p=p^{-1}$，实处用通常绝对值，复处用通常模且局部次数为 $2$。此定义与数域和齐次代表的选择无关。对有限 $x$ 写 $h(x)=h([x:1])$，并约定 $x(O)=\infty=[1:0]$、$h(\infty)=0$。典范高度采用 Silverman，*The Arithmetic of Elliptic Curves*，第二版，[VIII.9.1 与 VIII.9.3](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的归一化

$$
\widehat h(R)=\frac12\lim_{m\to\infty}4^{-m}h(x([2^m]R)).
$$

**定理 12.2（实际点的完全显式频率分离与统一起点估计）。** 对定义 12.1 的 $\alpha$，所有整数 $L,H\ge1$ 都满足

$$
\lambda_L(H)\ge\exp(-128L^2H^2).
$$

对所有 $\beta\in\mathbb T^2$ 和整数 $N\ge\exp(256L^2)$，有一致于起点的估计

$$
\mathcal D_N(\beta,L)
<\frac{73L}{\sqrt{\log N}}
\le\frac{128L}{\sqrt{\log N}}.
$$

这是一组固定算术数据的复合显式估计。非挠性与模挠独立性复用 Brox，[固定提交 `61b82ccacfbefdff3d6e7cf986d6e6279afa1372`](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex) 的 “The quadratic-field elliptic curve” 一节，尤其 `lem:independent`；所需的只是其整数系数特例。典范高度的二次性与下述 Erdős–Turán–Koksma 不等式是既有中间结果。显式加性高度常数和它们对本条固定点的组合在证明中给出，不使用未指定常数的聚合迹高度强制性估计。

**证明。** 先核对圆坐标的周期与距离。$C$ 的两条实半支各自贡献

$$
\int_1^\infty\frac{dx}{2\sqrt{x^3-x}}=\frac\Omega2.
$$

因此沿整圆积分为 $\Omega$。不变微分的平移不变性使积分模周期成为群同态；沿正定向走完一圈时积分严格增加一个周期，故它为一一对应的圆群坐标。它把归一化 Haar 测度送到 $\mathbb T$ 的长度测度。代换 $x=t^{-2}$ 给出完全显式的周期上界

$$
\Omega=2\int_0^1\frac{dt}{\sqrt{1-t^4}}
<2\int_0^1\frac{dt}{\sqrt{1-t}}=4.
$$

若 $R\in C$ 且 $X=x(R)>1$，从 $R$ 到 $O$ 的同一半支弧长小于半个周期，所以它就是较短的积分弧。于是

$$
\|\theta(R)\|_{\mathbb T}
=\frac1{2\Omega}\int_X^\infty\frac{dx}{\sqrt{x^3-x}}
>\frac1{\Omega\sqrt X}
>\frac1{4\sqrt X}.
\tag{12.1}
$$

第一个严格不等式使用 $x^3-x<x^3$ 及 $\int_X^\infty x^{-3/2}\,dx=2/\sqrt X$。$O$ 的圆距离为 $0$；另一个端点 $(1,0)$ 的圆距离为 $1/2$，不对这两点使用式 (12.1)。

现在给出高度误差的具体常数。倍点横坐标在射影线上由四次齐次式

$$
A(U,V)=(U^2+V^2)^2,\qquad
B(U,V)=4UV(U^2-V^2),\qquad
x([2]R)=[A(U,V):B(U,V)]
\tag{12.2}
$$

表示，其中 $x(R)=[U:V]$。仿射公式来自 $x([2]R)=(x^2+1)^2/(4x(x^2-1))$；在 $O$ 与二挠点处用同一齐次式延拓。以下整数系数恒等式还保证 $A,B$ 没有共同的射影零点：

$$
\begin{aligned}
16U^7&=(16U^3-12UV^2)A-(5U^2V+3V^3)B,\\
16V^7&=(16V^3-12U^2V)A+(3U^3+5UV^2)B.
\end{aligned}
\tag{12.3}
$$

例如第一式右侧两部分展开为 $16U^7+20U^5V^2-8U^3V^4-12UV^6$ 与 $20U^5V^2-8U^3V^4-12UV^6$ 之差；第二式交换 $U,V$，同时注意 $B(V,U)=-B(U,V)$，即得。

在每个有限处，把坐标除以模最大的非零坐标，归一化为 $\max(|U|_w,|V|_w)=1$。整数系数与超度量不等式给出上界 $\max(|A|_w,|B|_w)\le1$。式 (12.3) 中左侧至少一项的模为 $|2|_w^4$，右侧系数的模不超过 $1$，故

$$
|2|_w^4\le\max(|A|_w,|B|_w)\le1.
\tag{12.4}
$$

在任一实或复嵌入同样归一化。交换坐标后，输出的模为 $|(1+t^2)^2|$ 与 $|4t(1-t^2)|$，其中 $|t|\le1$。它们都不超过 $8$。若第一项小于 $1/4$，则 $|1+t^2|<1/2$，从而 $|t|>1/\sqrt2$ 且 $|1-t^2|>3/2$，第二项大于 $3\sqrt2$。因此在所有无穷处都有

$$
\frac14\le\max(|A|,|B|)\le8.
\tag{12.5}
$$

由齐次性，式 (12.4)–(12.5) 控制 $h(x([2]R))-4h(x(R))$。无穷处的归一化权重之和为 $1$，而乘积公式给出

$$
\frac1{[F_*:\mathbb Q]}\sum_{w\text{ 有限}}[F_{*,w}:\mathbb Q_w]\log|2|_w=-\log2.
$$

故对所有代数点，包括 $O$ 与挠点，都有

$$
4h(x(R))-6\log2
\le h(x([2]R))
\le4h(x(R))+3\log2.
\tag{12.6}
$$

把相邻两项的差乘以 $4^{-m-1}$ 后求和，利用 $\sum_{m\ge0}4^{-m-1}=1/3$，得到

$$
h(x(R))\le2\widehat h(R)+2\log2,\qquad
2\widehat h(R)\le h(x(R))+\log2.
\tag{12.7}
$$

这里极限的归一化与 Silverman 第二版 VIII.9.1（Tate 命题，印刷页 247–248）一致；其 VIII.9.3（印刷页 248–249）在全体代数点上给出非负性、$\widehat h([m]R)=m^2\widehat h(R)$ 及平行四边形恒等式。本证明以式 (12.6)–(12.7) 替换一般高度比较中的未指定加性误差。

定义 11.1 的两点都定义在指定实嵌入的数域

$$
F=\mathbb Q(\sqrt2,\sqrt{3-\sqrt2},\sqrt{3+\sqrt2}),
\qquad e=[F:\mathbb Q]\le8.
$$

它们的横坐标是

$$
X_1=\frac{115-27\sqrt2}{56},\qquad
X_2=\frac{115+27\sqrt2}{56}.
$$

二者均大于 $1$，且其本原不可约整系数多项式为

$$
448T^2-1840T+1681.
$$

事实上两根之和为 $115/28$、积为 $1681/448$；系数互素，判别式为 $2\cdot432^2$，不是有理平方。因此绝对高度的最小多项式公式给出

$$
h(X_1)=h(X_2)
=\frac12\log(448X_1X_2)=\log41.
$$

结合式 (12.7)，得到

$$
\widehat h(P_1)+\widehat h(P_2)\le\log82.
\tag{12.8}
$$

取 $0<\|h\|_\infty\le H$，令

$$
R=[Lh_1]P_1+[Lh_2]P_2,\qquad \Delta=L^2H^2\ge1.
$$

Brox 上述模挠独立性保证 $R$ 非挠，因此 $R\ne O$，也不等于二挠点 $(1,0)$。由于 $C$ 是子群，$R\in C$，故 $X=x(R)>1$，可以使用式 (12.1)。典范高度的平行四边形恒等式与非负性给出

$$
\begin{aligned}
\widehat h(R)
&\le2L^2\bigl(h_1^2\widehat h(P_1)+h_2^2\widehat h(P_2)\bigr)\\
&\le2\Delta\log82.
\end{aligned}
$$

这里没有用分别可达的最优值代替联合值；不等式来自对同一对点 $[Lh_1]P_1,[Lh_2]P_2$ 的平行四边形公式，舍去其差的非负高度。$R\in E_0(F)$，而 $h([X:1])$ 的每一个局部项都非负。指定实嵌入的权重是 $1/e$，于是 $\log X\le e h(X)\le8h(X)$。再用式 (12.7)，得到带有全部加性常数的界

$$
\log X\le32\Delta\log82+16\log2.
\tag{12.9}
$$

将其代入式 (12.1)，并使用 $\theta(R)=L(h_1\alpha_1+h_2\alpha_2)$，得到

$$
\begin{aligned}
\|Lh\cdot\alpha\|_{\mathbb T}
&>\exp(-16\Delta\log82-10\log2)\\
&\ge\exp\bigl(-(16\log41+26\log2)\Delta\bigr)\\
&>\exp(-128\Delta).
\end{aligned}
\tag{12.10}
$$

最后一步只需 $41<2^6$ 与 $\log2<1$：$16\log41+26\log2<122<128$。对有限个非零频率取最小值即得所需分离；无需给出完整 Mordell–Weil 群或重新证明算术独立性。

接着使用 Dick–Pillichshammer 上述预印本印刷页 84、定理 3.26 的极端差异度不等式。在维数 $2$，置 $r(h)=\max(1,|h_1|)\max(1,|h_2|)$，其准确形式为

$$
\mathcal D_N(\beta,L)
\le\frac94\left(
\frac2{H+1}
+\sum_{0<\|h\|_\infty\le H}\frac1{r(h)}
\left|\frac1N\sum_{k=0}^{N-1}\exp(2\pi i h\cdot z_k)\right|
\right).
\tag{12.11}
$$

所有指数均可用任意实代表计算。对于 $u=Lh\cdot\alpha\ne0$ 于 $\mathbb T$，几何级数及 $|\sin(\pi u)|\ge2\|u\|_{\mathbb T}$ 给出

$$
\left|\frac1N\sum_{k=0}^{N-1}\exp(2\pi i h\cdot z_k)\right|
\le\frac2{N|1-\exp(2\pi i u)|}
\le\frac1{2N\|u\|_{\mathbb T}}.
\tag{12.12}
$$

正弦下界来自 $\sin$ 在 $[0,\pi/2]$ 上的凹性；起点 $\beta$ 只贡献模为 $1$ 的因子。故式 (12.11) 为

$$
\mathcal D_N(\beta,L)
\le\frac9{2(H+1)}+\frac{9S_H}{8N\lambda_L(H)},\qquad
S_H=\left(1+2\sum_{j=1}^H\frac1j\right)^2-1\le8H^2.
\tag{12.13}
$$

最后一个不等式由 $\sum_{j=1}^H1/j\le H$ 及 $4H^2+4H\le8H^2$ 得到。令 $t=\log N\ge256L^2$，选

$$
H=\left\lfloor\frac{\sqrt t}{16L}\right\rfloor\ge1.
$$

由频率分离，$N\lambda_L(H)\ge\exp(t-128L^2H^2)\ge\exp(t/2)$。又 $H+1>\sqrt t/(16L)$，且 $e^{t/2}\ge t^2/8$，所以

$$
\begin{aligned}
\frac9{2(H+1)}&<\frac{72L}{\sqrt t},\\
\frac{9S_H}{8N\lambda_L(H)}
&\le\frac{9t}{256L^2}e^{-t/2}
\le\frac9{32L^2t}
\le\frac9{512}\frac L{\sqrt t}.
\end{aligned}
$$

末步使用 $L\ge1$ 与 $\sqrt t\ge16L$。因为 $72+9/512<73$，得到所述严格的 $73$ 界，也得到 $128$ 界。全部估计均与 $\beta$ 无关。$\square$

**定理 12.3（固定正面积弧盒的显式块等待与局部同步）。** 设 $L\ge1$ 为整数，$0<v\le1$，并令

$$
W(L,v)=2^{\left\lceil 2^{15}L^2/v^2\right\rceil}.
$$

对任意 $\beta\in\mathbb T^2$、任意整数 $k_0$ 及每个固定的定义 12.1 弧盒 $\mathcal B$，若 $|\mathcal B|\ge v$，则

$$
\{\beta+(k_0+j)L\alpha:0\le j<W(L,v)\}\cap\mathcal B\ne\varnothing.
\tag{12.14}
$$

因此每个 $W(L,v)$ 项的连续进程块都命中该盒子。这里允许半开、开、跨切口或全圆因子；不要求 $O$ 在目标中。

具体应用于定义 11.2 的固定局部数据，仍置 $g=\gcd(M,D)$、$L=\operatorname{lcm}(M,D)$，其中各 $d_v$ 与 $D$ 取该定义的值。若 $g\nmid a$，不存在任何整数同时满足指定同余和全部局部条件。若 $g\mid a$，令 $b\in\{1,\ldots,L\}$ 为定理 11.3 的唯一允许类代表。对任意 $k_0\ge0$，从第一允许项 $n_*=b+Lk_0$ 开始的 $W=W(L,v)$ 项中，存在同一个正整数

$$
n=n_*+Lj,\qquad 0\le j<W,
$$

使

$$
n\equiv a\pmod M,\qquad
[n]P_v\in U_v\quad(v\in S),\qquad
[n]Q\in B_C,
\qquad
0\le n-n_*\le L(W-1)<LW.
\tag{12.15}
$$

对任意整数阈值 $T\ge0$，还有严格向前的正整数结论

$$
T<n\le T+LW
\tag{12.16}
$$

并同时满足式 (12.15) 的前三组条件。若沿全部整数解 $b+L\mathbb Z$ 考察而不预加正性要求，式 (12.16) 对任意 $T\in\mathbb Z$ 也成立。式 (12.15) 的起点是第一允许项，式 (12.16) 的起点是任意整数阈值，二者端点分别为严格的间隙 $<LW$ 和闭的上界 $\le T+LW$。

**证明。** $\log2>1/2$，因为 $\int_1^2 dx/x>1/2$。由 $W$ 的定义，

$$
\log W\ge2^{15}(\log2)L^2/v^2
\ge2^{14}L^2/v^2\ge256L^2.
$$

定理 12.2 中保留的 $73$ 界因而给出，对每个起点 $\gamma\in\mathbb T^2$，

$$
\mathcal D_W(\gamma,L)
<\frac{73L}{\sqrt{\log W}}
\le\frac{73}{128}v
<\frac34v.
\tag{12.17}
$$

先设两个因子均为半开弧或全圆。将各弧的左端点平移到 $0$ 后，盒子成为 $[0,\ell_1)\times[0,\ell_2)$，全圆对应 $\ell_j=1$；这一次坐标平移同时吸收到起点 $\gamma=\beta+k_0L\alpha-(q(c_1),q(c_2))$ 中。不需要把跨切口盒子分成四块。因此式 (12.17) 直接给出

$$
\#\{0\le j<W:\beta+(k_0+j)L\alpha\in\mathcal B\}
\ge W\bigl(|\mathcal B|-\mathcal D_W(\gamma,L)\bigr)>0.
$$

若有开弧因子，在其参数区间内各缩进一个正数 $\varepsilon$，取内部半开弧；全圆因子保持全圆。长度 $1$ 的去点开弧也可如此缩进。所得半开弧盒包含于原盒，且面积随缩进量趋于 $0$ 而趋于原面积，故可以选择面积大于 $3v/4$ 的内部半开弧盒。对它再次平移并用式 (12.17)，访问数仍严格大于 $0$。任意其他端点开闭约定也由同一内部盒论证得到。面积为零的退化盒不满足 $v>0$ 的前件，未被用来推出命中。由此证明式 (12.14)，且其中任意块的起点已经由 $\beta+k_0L\alpha$ 统一处理。

局部部分直接使用定理 11.3 中已经证明的精确等价

$$
\bigl(n\equiv a\pmod M\ \text{且}\ [n]P_v\in U_v\ (v\in S)\bigr)
\iff n\in b+L\mathbb Z
$$

（相容时），以及不相容时解集为空的结论。正整数允许项恰为 $b+Lk$，$k\ge0$。令 $\beta=n_*\alpha$，对 $k_0=0$ 的式 (12.14) 应用，即有某个 $0\le j<W$ 使 $(n_*+Lj)\alpha\in\mathcal B$。这同一个 $n=n_*+Lj$ 既属于允许类，又使 $[n]Q\in B_C$，从而得到式 (12.15) 的全部联合条件与端点。空局部集 $S=\varnothing$ 时 $D=1$，论证不变。

最后，对任意整数 $T$，第一项严格大于 $T$ 的整数允许项是

$$
n_0=b+L\left(\left\lfloor\frac{T-b}{L}\right\rfloor+1\right),
\qquad T<n_0\le T+L.
$$

从它开始应用 $W$ 项命中结论，所得 $n$ 满足

$$
T<n_0\le n\le n_0+L(W-1)\le T+LW.
$$

当 $T\ge0$ 时 $n_0>0$，其对应允许项指标非负，故得到正整数版本。$\square$

定理 12.2–12.3 的新增综合推导是实际固定共轭点的显式数值链，而不是一般高度理论、Erdős–Turán–Koksma 不等式、CRT 或定性紧群回返的新版本。第 11 节给出实际点的定性分布；[ARITHMETIC_BOUNDARY_QUANTIZATION，第 35.11 条](ARITHMETIC_BOUNDARY_QUANTIZATION.md) 给出依赖旋转的定性向前有界间隙。这些定性结论没有提供本节的数值常数。Glazer 的[固定源码 `9c0b3aba60d90fdcac82115f0582a6f52f1054f7`](https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/manuscripts/quartic_v13.tex) 只在这里承担第 11 节已给出的固定数据对应；本节不以其完整算术构造为前提，也不主张新的算术独立性或文献优先权。

用白话说，这两个实际点每走相同的 $L$ 步，就在两个圆坐标上同时前进一次。显式高度界阻止低频整数关系无限贴近整数，字符平均因而有统一误差；固定的正面积弧盒最终不能在整块进程中一直空着。局部条件先把可用整数筛成一个类，返回定理再在这个类内选中同一个整数，所以不是给不同条件各找一个见证。

上述 $L,v$、弧盒和全部局部条件均先固定。泛指的局部群的周期 $d_v$ 是输入数据，本节没有给未指定群计算周期。$W$ 控制指标长度，不估算表示或检验各项的计算成本。目标是所定义的圆坐标弧盒；一般 Borel 集、任意横坐标矩形、移动或缩小目标以及随 $n$ 加深的局部条件需要各自的额外论证。式 (12.6)–(12.9) 是坐标高度的有效界，不给出聚合迹高度自身的有效加性常数。本节也不给出 $\mathsf H_{\mathbb Z/\mathbb Q}$ 的完整表示与双向正确性证明，不给出无前提的量子起源或 Born 规则推导。

## 追加锚（本行以下为增补区）

## 13. 实际共轭点在增长有限位与加深局部精度下的同整数缩靶返回

**定义 13.1（实际局部子群、精确周期与增长安排）。** 固定定义 11.1 的实际非挠点 $P_1,P_2\in E_0(F)$，其中

$$
E_0:Y^2=X^3-X,\qquad
F=\mathbb Q(\sqrt2,\sqrt{3-\sqrt2},\sqrt{3+\sqrt2}),\qquad
d_F=[F:\mathbb Q]\le8.
$$

正实根及指定实嵌入沿用第 11–12 节；$\theta,\alpha$ 与圆距离沿用定义 12.1。实际点的原始来源是 Brox，[固定源码的 “The quadratic-field elliptic curve” 一节](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex)，这里只复用其所列点、非挠性及第 12 节已使用的整数模挠独立性。

对每个有限位 $v\mid p$，记 $F_v$ 的整数环、极大理想及剩余域为 $\mathcal O_v,\mathfrak m_v,k_v$，固定 $\operatorname{ord}_v(\varpi_v)=1$，并置

$$
e_v=\operatorname{ord}_v(p)\ge1,\qquad
f_v=[k_v:\mathbb F_p],\qquad
\sum_{v\mid p}e_vf_v=d_F.
$$

当 $p$ 为奇素数时，使用原方程 $E_0$。当 $v\mid2$ 时，固定一个极小整 Weierstrass 模型 $\mathcal E_v$ 及保单位元的 $F_v$-同构 $\iota_v:E_0\to\mathcal E_v$；奇素数处记 $\mathcal E_v=E_0$、$\iota_v=\mathrm{id}$。令 $\widehat{\mathcal E}_v$ 为该整模型的形式群，$\psi_v:\widehat{\mathcal E}_v(\mathfrak m_v)\to\mathcal E_{v,1}(F_v)$ 为形式参数给出的群同构，参数为 $t_v=-x_v/y_v$，$t_v(O)=0$。这里 $\mathcal E_{v,1}(F_v)$ 是约化为单位元的点群。对整数 $r\ge1$ 定义

$$
U_v(r)=\iota_v^{-1}
 \bigl(\psi_v(\widehat{\mathcal E}_v(\mathfrak m_v^r))\bigr)
 \ \le E_0(F_v).
\tag{13.1}
$$

这是实际单位元邻域中的形式子群。等价地，先要求 $\iota_v(R)\in\mathcal E_{v,1}(F_v)$，再要求其形式参数属于 $\mathfrak m_v^r$；不把任意仿射点上的坐标比值不等式当作本定义。极小模型与此同构分别使用 Silverman，*The Arithmetic of Elliptic Curves*，第二版，[VII.1.3、VII.2.2 及 IV §3](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)；相关文字澄清见作者的[勘误](https://www.math.brown.edu/johsilve/AEC/AECErrata.pdf)中印刷页 122–124、188–191 的条目。

定义精确有限阶及共同周期

$$
\begin{aligned}
d_{v,j}(r)&=\operatorname{ord}_{E_0(F_v)/U_v(r)}(P_j+U_v(r)),
 &&j=1,2,\\
A_2&=\operatorname{lcm}_{v\mid2,\ j=1,2}d_{v,j}(1),\\
q(B,r;M)&=\operatorname{lcm}
 \bigl(M,\{d_{v,j}(r):p\le B,\ v\mid p,\ j=1,2\}\bigr),
 &&B\in\mathbb R_{\ge2},\quad M,r\in\mathbb Z_{\ge1}.
\end{aligned}
\tag{13.2}
$$

上述商群的有限性在定理 13.2 的证明中给出。素数求和、乘积均只取有理素数，记

$$
\vartheta(B)=\sum_{p\le B}\log p,\qquad
\pi(B)=\#\{p:p\le B\}.
$$

固定 $M\ge1$ 及 $0<\gamma<1/4$。对正整数 $n$ 置

$$
\begin{aligned}
h(n)&=\max\left(2,\left\lfloor(\log\log(n+16))^{1/3}\right\rfloor\right),\\
\rho(n)&=(\log(n+2))^{-\gamma},\\
q_n&=q(h(n),h(n);M),\qquad D_n=q(h(n),h(n);1).
\end{aligned}
\tag{13.3}
$$

所有对数均为自然对数。成功整数集合是

$$
\begin{split}
\mathcal S_{M,\gamma}=\{n\in\mathbb Z_{\ge1}:\
&M\mid n,\quad
\|\theta([n]P_j)\|_{\mathbb T}<\rho(n)\quad(j=1,2),\\
&[n]P_j\in U_v(h(n))
\quad(p\le h(n),\ v\mid p,\ j=1,2)\}.
\end{split}
\tag{13.4}
$$

其中素数截止、局部深度和实半径都取同一个整数 $n$ 自身的值。

**定理 13.2（这对实际点的共享周期整除式及数值包络）。** 定义 13.1 中每个 $U_v(r)$ 都是有限指数开子群，并且对所有 $B\ge2$、整数 $r,M\ge1$ 有真正的整数整除式

$$
q(B,r;M)\ \mid\
 M A_2\,2^{r-1}
 \prod_{3\le p\le B}
 \left[p^{r-1}\prod_{v\mid p}\#E_0(k_v)\right].
\tag{13.5}
$$

由此有数值不等式

$$
\log q(B,r;M)
\le \log(MA_2)+(r-1)\log2
 +(r+7)\vartheta(B)+8(\log4)\pi(B).
\tag{13.6}
$$

特别地，若 $h\ge2$ 为整数，令 $c_0=28+8\log4+\log2$，则

$$
\log q(h,h;M)\le4h^2+c_0h+\log(MA_2).
\tag{13.7}
$$

若 $B\le B'$、$r\le r'$，则 $q(B,r;M)\mid q(B',r';M)$。对任意整数 $m$，精确的同步等价为

$$
\begin{split}
q(B,r;M)\mid m
\quad\Longleftrightarrow\quad
&M\mid m\ \text{且}\\
&[m]P_j\in U_v(r)
 \quad(p\le B,\ v\mid p,\ j=1,2).
\end{split}
\tag{13.8}
$$

**证明。** 先说明定义中的局部群确实存在且指数有限。整模型的形式群律及逆元级数的系数都在 $\mathcal O_v$ 中，因而 $\widehat{\mathcal E}_v(\mathfrak m_v^r)$ 是子群，形式坐标使其成为单位元的开邻域。其像及经 $\iota_v$ 拉回的像也都是开子群。$F_v$ 是有限扩张的 $p$ 进局部紧域，$\mathbb P^2(F_v)$ 紧，故其中闭子集 $E_0(F_v)$ 紧。一个紧群的开子群具有有限指数：其开陪集构成开覆盖，有限子覆盖给出有限个陪集。因此所有 $d_{v,j}(r)$ 及 $A_2$ 都是有限正整数。此处在 $v\mid2$ 不要求好约化，也不把整个商群误认成特殊纤维的非奇异点群；任何实际约化类型均由紧性和固定极小模型处理。

Silverman 上述第二版 IV.2.3(a) 给出整系数乘法级数

$$
[p]_{\widehat{\mathcal E}_v}(T)=pT+\sum_{\nu\ge2}a_\nu T^\nu,
\qquad a_\nu\in\mathcal O_v.
$$

若 $\operatorname{ord}_v(t)\ge s\ge1$，级数收敛，且

$$
\operatorname{ord}_v([p]t)
\ge\min(e_v+s,2s)\ge s+1.
\tag{13.9}
$$

零参数的赋值取 $+\infty$，所以上式也包括乘积为单位元的情形。反复应用得到

$$
[p^{r-1}]U_v(1)\subseteq U_v(r),\qquad
d_{v,j}(r)\mid p^{r-1}d_{v,j}(1).
\tag{13.10}
$$

这只使用 $e_v\ge1$，故分歧无需排除；非线性项若相消只会提高赋值。另一方面 $U_v(r+1)\subseteq U_v(r)$，故商映射给出 $d_{v,j}(r)\mid d_{v,j}(r+1)$。

原曲线 $E_0$ 的判别式为 $64$，故每个奇素数处的原模型在任意 $F_v$ 上均为好约化的极小整模型，包括分歧的有限扩张。由 Silverman VII.2.1 的约化正合列和 VII.2.2 的形式群识别，

$$
E_0(F_v)/U_v(1)\simeq E_0(k_v)\qquad(p\ne2).
$$

因此两个点的 $d_{v,j}(1)$ 都整除同一个整数 $\#E_0(k_v)$，从而

$$
d_{v,j}(r)\mid p^{r-1}\#E_0(k_v)\qquad(p\ne2).
\tag{13.11}
$$

对固定奇素数 $p$，整数 $p^{r-1}\prod_{v\mid p}\#E_0(k_v)$ 同时被所有 $d_{v,j}(r)$ 整除；两个点共享群阶，不需要把群阶平方。对 $p=2$，式 (13.10) 使 $A_2\,2^{r-1}$ 同时被所有相应阶整除。再乘 $M$，式 (13.5) 的右端同时被取最小公倍数的每一项整除，故得到该整除式。不同素数的群阶可以有共同因子，证明只需要它们的乘积是共同倍数。

数值估计另作如下处理。在奇特征域 $k_v$ 上，每个横坐标至多对应两个纵坐标，再加无穷远点，所以

$$
\#E_0(k_v)\le2p^{f_v}+1\le4p^{f_v}.
\tag{13.12}
$$

这是足够的初等点数上界，不需要 Hasse 界。由 $\sum_{v\mid p}e_vf_v=d_F\le8$，有 $\sum_{v\mid p}f_v\le8$ 及 $\#\{v:v\mid p\}\le8$。因此

$$
\begin{aligned}
\sum_{v\mid p}\log\#E_0(k_v)&\le8\log4+8\log p,\\
\log q(B,r;M)
&\le\log(MA_2)+(r-1)\log2
 +\sum_{3\le p\le B}\bigl((r+7)\log p+8\log4\bigr).
\end{aligned}
$$

放大求和范围即为式 (13.6)。式 (13.12) 只用于大小比较；没有把 $4p^{f_v}$ 当成实际群阶的整数倍数。

为给出式 (13.7) 的具体常数，使用经典二项式方法的以下初等估计。对整数 $m\ge2$，每个 $\lceil m/2\rceil<p\le m$ 的素数都整除 $\binom m{\lfloor m/2\rfloor}$，所以

$$
\vartheta(m)\le\vartheta(\lceil m/2\rceil)+m\log2.
$$

由 $\vartheta(1)=0$ 归纳得 $\vartheta(m)\le4m$：归纳步的右端至多 $4\lceil m/2\rceil+m\log2\le4m$，最后一个不等式对所有 $m\ge2$ 成立。又有 $\pi(m)\le m$。将 $B=r=h$ 代入式 (13.6)，便得

$$
\log q(h,h;M)
\le\log(MA_2)+(h-1)\log2+4h(h+7)+8h\log4
\le4h^2+c_0h+\log(MA_2).
$$

最后，子群随深度递减，地方集合随截止增长，故各精确阶及其最小公倍数具有所述整除嵌套。一个元素在商群中的精确阶为 $d$，恰意味着其第 $m$ 倍为零当且仅当 $d\mid m$；对所有地方、两个点及 $M$ 同时应用即得式 (13.8)。$\square$

**定理 13.3（自身阶段的定量缩靶与每个二倍区间的多重命中）。** 对定义 13.1 的任意固定 $M\ge1$、$0<\gamma<1/4$，共同周期是次多对数的：

$$
\lim_{n\to\infty}\frac{\log q_n}{\log\log n}=0,
\qquad
\text{即对每个 }\eta>0,\quad q_n\le(\log n)^\eta
\ \text{最终成立}.
\tag{13.13}
$$

存在依赖于这些固定数据的整数 $X_0$，使每个整数 $X\ge X_0$ 都满足

$$
\#\bigl(\mathcal S_{M,\gamma}\cap(X,2X]\bigr)
\ge \frac{X\,\rho(2X)^2}{4q_{2X}}.
\tag{13.14}
$$

进一步，对每个固定 $\varepsilon>0$，存在整数 $X_\varepsilon$，使所有整数 $X\ge X_\varepsilon$ 都有

$$
\#\bigl(\mathcal S_{M,\gamma}\cap(X,2X]\bigr)
\ge\frac{X}{(\log X)^{2\gamma+\varepsilon}}.
\tag{13.15}
$$

一个明确但未数值求值的充分起点判据如下。置

$$
H=h(2X),\qquad R=\rho(2X),\qquad
Q_X=MA_2\exp(4H^2+c_0H).
$$

若整数 $X$ 满足

$$
0<R\le\tfrac12,\qquad
X\ge4Q_X,\qquad
\log\frac{X}{2Q_X}\ge2^{16}Q_X^2R^{-4},
\tag{13.16}
$$

则式 (13.14) 成立。若此外满足

$$
X\ge3,\qquad
Q_X\le(\log X)^{\varepsilon/2},\qquad
(\log X)^{\varepsilon/2}\ge4\cdot2^{2\gamma},
\tag{13.17}
$$

则式 (13.15) 也成立。所有这些不等式对充分大的 $X$ 均成立。

**证明。** 函数 $h$ 不减且趋于无穷，$\rho$ 递减且趋于零。由式 (13.7) 和 $h(n)=O((\log\log n)^{1/3})$，

$$
0\le\log q_n
\le\log(MA_2)+4h(n)^2+c_0h(n)
=O_{M,A_2}((\log\log n)^{2/3})
=o(\log\log n),
$$

得到式 (13.13)。同时 $q_n\mid q_{n'}$ 当 $n\le n'$。

固定满足式 (13.16) 的 $X$，记 $q=q_{2X}$，于是 $q\le Q_X$。区间 $(X,2X]$ 中全部 $q$ 的倍数恰为

$$
n_k=q\left(\left\lfloor\frac Xq\right\rfloor+1+k\right),
\quad 0\le k<N,\qquad
N=\left\lfloor\frac{2X}q\right\rfloor-\left\lfloor\frac Xq\right\rfloor.
\tag{13.18}
$$

由 $X\ge4Q_X\ge2q$，

$$
N\ge\frac Xq-1\ge\frac{X}{2q},\qquad
\log N\ge\log\frac X{2q}\ge\log\frac X{2Q_X}
\ge2^{16}Q_X^2R^{-4}\ge256q^2.
\tag{13.19}
$$

现在只对这个固定的有限块调用定理 12.2，取其整数步长 $L=q$、项数 $N$ 及起点

$$
\beta=q\left(\left\lfloor\frac Xq\right\rfloor+1\right)\alpha
\quad\text{于 }\mathbb T^2.
$$

式 (13.19) 保证该定理的前件 $N\ge\exp(256L^2)$，并且其一致于 $\beta$ 的差异度界给出

$$
\mathcal D_N(\beta,q)
<\frac{128q}{\sqrt{\log N}}
\le\frac{R^2}{2}.
\tag{13.20}
$$

在定义 12.1 的 $[0,1)^2$ 代表坐标中使用半开盒 $[0,R)\times[0,R)$，其面积是 $R^2$。因为 $R\le1/2$，该盒中的每个圆坐标均具有严格小于 $R$ 的圆距离；零端点也满足严格不等式，右端点被排除。由式 (13.20)，满足两个实端条件的 $n_k$ 数量严格大于

$$
N(R^2-R^2/2)=\frac{NR^2}{2}
\ge\frac{XR^2}{4q}.
\tag{13.21}
$$

这里使用原坐标中的单个盒子，故没有跨切口分割或端点误差。虽然整个对称圆邻域的面积更大，这个内盒已经给出所需下界。

每个被计入的同一个整数 $n=n_k$ 还满足 $q_{2X}\mid n$。由式 (13.8)，它同时满足 $M\mid n$ 以及全部 $p\le H$、$v\mid p$、$j=1,2$ 的 $[n]P_j\in U_v(H)$。又因 $n\le2X$，

$$
h(n)\le H,\qquad
U_v(H)\subseteq U_v(h(n)),\qquad
\|\theta([n]P_j)\|_{\mathbb T}<R\le\rho(n).
\tag{13.22}
$$

所以每个被计入的整数均属于其自身阶段的 $\mathcal S_{M,\gamma}$，包括可能跨过 $h$ 跳跃点的区间。式 (13.21) 于是推出式 (13.14)。没有把不同地方的返回整数拼在一起，也没有把随 $n$ 移动的条件直接代入固定盒的计数定义。

还须验证充分起点确实存在。写 $t=\log X$。由 $H=O((\log t)^{1/3})$，

$$
\log Q_X=O_{M,A_2}((\log t)^{2/3})=o(\log t),
\qquad Q_X=t^{o(1)}.
$$

于是 $X\ge4Q_X$ 最终成立，且

$$
\log\frac X{2Q_X}\sim t,\qquad
2^{16}Q_X^2R^{-4}
=2^{16}Q_X^2(\log(2X+2))^{4\gamma}
=t^{4\gamma+o(1)}=o(t).
\tag{13.23}
$$

最后一步准确使用 $4\gamma<1$。又有 $0<R\le1/2$ 最终成立，故式 (13.16) 的全部条件最终成立；这证明了每个充分大二倍区间的结论，而不只是某个区间子序列。

对固定 $\varepsilon>0$，式 (13.13) 的同一包络给出式 (13.17) 最终成立。$X\ge3$ 时 $\log(2X+2)\le2\log X$，所以在该判据下

$$
\begin{aligned}
4q_{2X}(\log(2X+2))^{2\gamma}
&\le4Q_X(2\log X)^{2\gamma}\\
&\le(\log X)^{2\gamma+\varepsilon}.
\end{aligned}
$$

代入式 (13.14) 即得式 (13.15)。$\square$

**推论 13.4（每个固定地方的最终加入及逐点局部趋零）。** $\mathcal S_{M,\gamma}$ 无界。对每个固定有限位 $v\mid p$ 和每个固定整数 $r_0\ge1$，存在 $N(v,r_0)$，使所有满足 $n\in\mathcal S_{M,\gamma}$、$n\ge N(v,r_0)$ 的整数都满足

$$
p\le h(n),\qquad h(n)\ge r_0,\qquad
[n]P_j\in U_v(r_0)\quad(j=1,2).
\tag{13.24}
$$

因而对任意趋于无穷的成功整数序列 $n_k\in\mathcal S_{M,\gamma}$，同一个序列在指定实嵌入和每个固定有限位上均有

$$
[n_k]P_j\longrightarrow O\quad(j=1,2).
\tag{13.25}
$$

这里的量词是先固定 $v,r_0$，再取足够大的 $k$；不要求一个指标同时越过无限多个地方的全部阈值。任意无界成功集合的递增枚举满足此结论；若仅给一个不趋于无穷的无界序列，则对它的任意趋于无穷子序列有同一结论。没有非零固定整数 $m$ 能使 $[m]P_j$ 在某一个固定有限位属于所有 $U_v(r)$，即使只要求其中一个 $j$。

**证明。** 式 (13.15) 的右端随 $X\to\infty$ 趋于无穷，故成功集合无界。由于 $h(n)\to\infty$，最终有 $h(n)\ge\max(p,r_0)$；定义 (13.4) 和子群嵌套即给出式 (13.24)。形式参数中的 $\mathfrak m_v^r$ 是趋于零的邻域基，故 $U_v(r)$ 是 $O$ 的邻域基且 $\bigcap_{r\ge1}U_v(r)=\{O\}$。实端则由 $\rho(n)\to0$ 和 $\theta$ 为拓扑群同构得到。

最后，$P_j$ 在每个 $E_0(F_v)$ 中仍非挠：域嵌入 $F\hookrightarrow F_v$ 诱导单射 $E_0(F)\hookrightarrow E_0(F_v)$，倍点与域扩张交换；若局部有 $[m]P_j=O$、$m\ne0$，单射会给出全局同一挠关系，违背上述 Brox 固定点的非挠性。因此一个非零固定 $m$ 不可能落入该交集。这也说明式 (13.25) 的整数确实需要随精度改变。$\square$

**定理 13.5（任意固定同余类的最终障碍）。** 对不预加同余约束的实际局部周期 $D_n$，每个固定整数 $M\ge1$ 最终都满足

$$
M\mid D_n.
\tag{13.26}
$$

具体地，对任意固定阶段 $t\ge1$ 及任意 $a\in\mathbb Z$，存在整数 $m$ 满足

$$
m\equiv a\pmod M,\qquad
[m]P_j\in U_v(h(t))
\quad(p\le h(t),\ v\mid p,\ j=1,2)
\tag{13.27}
$$

的充要条件恰为 $\gcd(M,D_t)\mid a$。相容时，整数解是模 $\operatorname{lcm}(M,D_t)$ 的唯一类，且有任意大的正整数解。当 $t$ 充分大时，这一相容条件化为 $M\mid a$。

特别地，若 $M\nmid a$，只有有限多个整数 $n\ge1$ 能同时满足 $n\equiv a\pmod M$ 和其自身阶段的全部局部条件，因此加上实端缩靶后仍至多有限多个。若 $M\mid a$，同余条件就是 $M\mid n$，定理 13.3 的计数下界适用。

**证明。** 固定素数 $\ell$，取任一 $v\mid\ell$ 及 $j=1$。令 $b_r=d_{v,1}(r)$。由式 (13.10) 及嵌套，

$$
b_1\mid b_r\mid b_1\ell^{r-1},\qquad b_r\mid b_{r+1}.
\tag{13.28}
$$

若 $\operatorname{ord}_\ell(b_r)$ 有界，则存在固定 $K\ge0$ 使所有 $b_r\mid b_1\ell^K$。于是同一个非零整数 $b_1\ell^K$ 使

$$
[b_1\ell^K]P_1\in\bigcap_{r\ge1}U_v(r)=\{O\},
$$

与推论 13.4 证明中的局部非挠性矛盾。因此 $\operatorname{ord}_\ell(b_r)\to\infty$；这里使用了其不减性。这一论证也适用于 $\ell=2$ 的固定极小模型，不要求局部对数的精确公式。

对 $M$ 的每个素因子幂 $\ell^a\mid M$，固定一个这样的 $v$ 并选深度 $r_\ell$ 使 $\ell^a\mid d_{v,1}(r_\ell)$。当 $h(n)\ge\max_{\ell\mid M}(\ell,r_\ell)$ 时，所有这些地方均已加入，且深度足够，故各 $\ell^a$ 均整除 $D_n$。这些素因子幂互素，得到式 (13.26)；$M=1$ 时结论直接成立。

对固定阶段 $t$，式 (13.8) 的 $M=1$ 情形把全部局部条件精确化为 $D_t\mid m$。经典整数 CRT 给出

$$
m\equiv a\pmod M,\quad m\equiv0\pmod{D_t}
\quad\text{可解}\quad\Longleftrightarrow\quad
\gcd(M,D_t)\mid a,
$$

以及相容时的唯一允许类；加上该类的正周期即得任意大的正整数解。此处先固定阶段 $t$ 再求 $m$；并未声称任意阶段指标 $t$ 自己就是解。由式 (13.26)，最终 $\gcd(M,D_t)=M$。若再要求自身阶段，即在式 (13.27) 取 $t=m=n$，则充分大的 $n$ 必须满足 $M\mid n$；它与 $n\equiv a\pmod M$ 相容恰需 $M\mid a$。所以非零模类的最终障碍不能由实端等分布消除。$\square$

本节的承重结论是对第 11 节实际点和第 12 节统一差异度的固定数据定量综合：式 (13.5) 的共享整数周期、式 (13.14)–(13.15) 的自身阶段多重命中，以及式 (13.26) 的最终同余障碍。极小模型、形式群过滤、约化正合列和 CRT 均为所引经典中间结果；初等有限域点数与二项式素数估计只承担上界，不作为一般局部理论或分布理论的新结果。$A_2$ 依赖已固定的 $2$ 进模型及实际点，本节未求其数值；充分起点由式 (13.16)–(13.17) 指定而未数值求值，任意同余类达到式 (13.26) 的起点也未求值。这里没有周期最优性、一般理论原创或文献优先权的主张。

用白话说，实端的两个圆像两只同时转动的表盘，有限位则像越来越多、刻度越来越细的局部放大镜。所有放大镜要求的返回整数先通过实际商群的阶合成一个共同步长；在奇素数处，两只表盘对应的点共用同一个有限群阶，坏约化和分歧也被固定模型中的形式群吸收。把一个二倍区间的右端点当作临时标尺，就可以先要求这整个区间中最深的局部精度和最小的实端窗口，再沿共同步长数实端命中。步长只按次多对数速度增长，实端窗口缩小得足够慢，差异度误差最终小于窗口面积，因此区间中仍留下定量多个整数。每个留下的整数同时通过所有检查，而且通过的是比它自身要求更强的条件；随着这些整数走向无穷，每一个固定放大镜最终都会加入并无限加深。这里不断改变的是返回整数，没有一个非零整数被宣称能一次达到全部无限精度；任意固定非零同余类还会被最终的局部整除要求排除。

这些结论的实端目标严格采用定义 12.1 的圆距离，有限端严格采用式 (13.1) 的实际形式子群，增长速度和 $\gamma<1/4$ 是本节所证的充分安排。它们不提供任意更快增长安排或一般移动目标的结论，也不估计表示与检验返回整数的计算成本。结果不包含 $\mathsf H_{\mathbb Z/\mathbb Q}$ 的完整表示与双向证明，不包含 Born 规则或量子理论的重建。

## 追加锚（本行以下为增补区）

## 14. 实际共轭点的全部相容目标、统一命中与完全显式起点

**定义 14.1（共同整数目标与自身阶段）。** 全部算术数据、正实根、指定实嵌入、圆坐标 $\theta$、极小整模型、同构 $\iota_v$、形式子群 $U_v(r)$ 及函数 $h,\rho$ 严格沿用定义 11.1、12.1、13.1。特别地，有限位取数域 $F$ 的全部有限位，实端只取已指定的嵌入。置

$$
\widehat{\mathbb Z}=\varprojlim_{m\ge1}\mathbb Z/m\mathbb Z,
\qquad
\mathcal K_f=\prod_{v\text{ 有限}}E_0(F_v)^2,
\qquad
\nu(n)=\bigl(([n]P_1,[n]P_2)\bigr)_v.
\tag{14.1}
$$

逆极限的指标按整除排序；$\mathcal K_f$ 用普通乘积拓扑，每个因子的单位元均为 $O$，全体单位元记为 $\boldsymbol O$。这里不使用受限乘积拓扑。整数按其全部相容剩余类嵌入 $\widehat{\mathbb Z}$，$u\equiv a\pmod m$ 表示其模 $m$ 坐标为 $a$。经典 profinite CRT 给出

$$
a+m\widehat{\mathbb Z}
=\{u\in\widehat{\mathbb Z}:u\equiv a\pmod m\}.
\tag{14.2}
$$

对 $u\in\widehat{\mathbb Z}$、有限位 $v$ 和 $j=1,2$，令 $b_{v,j,r}$ 为 $u$ 模 $d_{v,j}(r)$ 的任意整数代表，定义

$$
\{\eta_{v,j}(u)\}
=\bigcap_{r\ge1}\bigl([b_{v,j,r}]P_j+U_v(r)\bigr),
\qquad
\eta(u)=\bigl((\eta_{v,1}(u),\eta_{v,2}(u))\bigr)_v,
\qquad H=\eta(\widehat{\mathbb Z}).
\tag{14.3}
$$

交集的非空性、唯一性及代表无关性在下述定理的证明中给出。对正整数 $t$ 定义阶段商与其指定元素

$$
\begin{aligned}
G_t&=\prod_{\substack{p\le h(t),\ v\mid p\\j=1,2}}
 E_0(F_v)/U_v(h(t)),\\
g_t&=(P_j+U_v(h(t)))_{p,v,j},\qquad
C_t=\langle g_t\rangle\le G_t.
\end{aligned}
\tag{14.4}
$$

记 $\pi_t:\mathcal K_f\to G_t$ 为自然投影。$C_t$ 的阶为式 (13.3) 的 $D_t$。对固定整数 $M\ge1$、$a\in\mathbb Z$、$0<\gamma<1/4$、$u\in\widehat{\mathbb Z}$ 和 $z=(z_1,z_2)\in\mathbb T^2$，定义

$$
\begin{split}
\mathcal S(u,z;a,M,\gamma)=\{n\in\mathbb Z_{\ge1}:\
&n\equiv a\pmod M,\qquad
\|\theta([n]P_j)-z_j\|_{\mathbb T}<\rho(n)\quad(j=1,2),\\
&[n]P_j-\eta_{v,j}(u)\in U_v(h(n))
\quad(p\le h(n),\ v\mid p,\ j=1,2)\}.
\end{split}
\tag{14.5}
$$

所有条件都由同一个正整数 $n$ 承担。目标 $u,z$ 在计数时固定，$h(n),\rho(n)$ 则取该整数自身的阶段。

**定理 14.2（全部相容目标上的实际数据定量综合）。** 对定义 14.1 的固定数据，$\eta$ 是延拓 $\nu$ 的唯一连续群同态，且为单射及到 $H$ 的拓扑群同构。有限端的准确目标空间为

$$
H=\overline{\nu(\mathbb Z)}
=\{y\in\mathcal K_f:\pi_t(y)\in C_t\text{ 对每个 }t\ge1\}.
\tag{14.6}
$$

这里“目标”指整数轨道的极限目标。对每个整数 $N\ge1$，指定实两圆和全部有限端的联合正尾闭包满足

$$
\begin{aligned}
\overline{\{(n\alpha,\nu(n)):n\ge N\}}
 &=\mathbb T^2\times H,\\
\overline{\{(n\alpha,\nu(n)):n\ge N,\ n\equiv a\pmod M\}}
 &=\mathbb T^2\times\eta(a+M\widehat{\mathbb Z}).
\end{aligned}
\tag{14.7}
$$

第一行的紧群，其单位连通分支是 $\mathbb T^2\times\{\boldsymbol O\}$，分量群拓扑同构于 $\widehat{\mathbb Z}$。有限阶段的准确相容条件为

$$
\begin{split}
\exists n\in\mathbb Z:\quad n\equiv a\pmod M,
\quad\pi_t(\nu(n))=\pi_t(\eta(u))
\quad\Longleftrightarrow\quad
u\equiv a\pmod{\gcd(M,D_t)}.
\end{split}
\tag{14.8}
$$

相容时，解为模 $q(h(t),h(t);M)=\operatorname{lcm}(M,D_t)$ 的唯一类，有任意大的正整数解。不相容的完整目标，即 $u\not\equiv a\pmod M$，只允许有限多个自身阶段的成功整数。

局部初始常数和共同周期有完全数值的上界

$$
A_2\le2^{40},\qquad
q(h,h;M)\le M\exp(32h^2)\quad(h\in\mathbb Z,\ h\ge2).
\tag{14.9}
$$

取

$$
s=\tfrac12-2\gamma>0,\qquad m=\log M,\qquad
T=\left(\frac{1024}{s}\right)^3+\frac{16m}{s}+16,
\qquad
X_0(M,\gamma)=\left\lceil\exp(\exp T)\right\rceil.
\tag{14.10}
$$

则对每个 $u\equiv a\pmod M$、每个 $z\in\mathbb T^2$ 和每个整数 $X\ge X_0(M,\gamma)$，同时有

$$
\begin{aligned}
\#\bigl(\mathcal S(u,z;a,M,\gamma)\cap(X,2X]\bigr)
&\ge\frac{X\rho(2X)^2}{4q(h(2X),h(2X);M)}\\
&\ge\frac{X}{4M\exp(32h(2X)^2)(\log(2X+2))^{2\gamma}}.
\end{aligned}
\tag{14.11}
$$

对每个 $\varepsilon>0$，存在仅依赖 $M,\gamma,\varepsilon$ 的整数 $X_\varepsilon$，使对所有上述相容 $u,a$、所有 $z$ 和所有整数 $X\ge X_\varepsilon$ 有

$$
\#\bigl(\mathcal S(u,z;a,M,\gamma)\cap(X,2X]\bigr)
\ge\frac{X}{(\log X)^{2\gamma+\varepsilon}}.
\tag{14.12}
$$

这些计数界的起点不依赖目标；允许不同目标使用不同的见证整数。

逆极限与 CRT 在这里是经典中间结构；其拓扑事实可参见 Stacks Project，[Definition 5.22.1、Lemma 5.22.2，tag 08ZW](https://stacks.math.columbia.edu/tag/08ZW)。实际点及其非挠性、整数模挠独立性的来源仍为 Brox，[固定源码 “The quadratic-field elliptic curve” 及 `lem:independent`](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex)。Glazer 的[固定源码 `v5:real-progression-bridge`](https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/manuscripts/quartic_v13.tex)已给出先于后续同余模数选取的定性实安全界；本定理不以该定性结论或其完整算术构造为新增结果。本条在 §§11–13 上增加的综合是实际数据的全部相容目标、目标一致的自身阶段计数，以及式 (14.9)–(14.11) 中不含未求值局部常数的包络和起点；不主张文献优先权。

**证明（共同有限目标的构造）。** 式 (13.10) 的整除嵌套保证 $d_{v,j}(r)\mid d_{v,j}(r+1)$。若改变 $b_{v,j,r}$ 的代表，所加的整数倍恰使 $[b_{v,j,r}]P_j+U_v(r)$ 不变；不同深度的这些非空陪集也相互嵌套。$E_0(F_v)$ 紧，$U_v(r)$ 是开闭子群，故陪集是紧闭集，其交集非空。由于 $U_v(r)$ 是 $O$ 的邻域基且交为 $\{O\}$，交集至多含一个点。这证明式 (14.3) 良定义。

对每个 $v,j,r$，$\eta_{v,j}(u)$ 模 $U_v(r)$ 的值恰为

$$
[u\bmod d_{v,j}(r)]P_j+U_v(r).
\tag{14.13}
$$

此有限商上的映射是连续群同态。子群 $U_v(r)$ 构成邻域基，故 $\eta_{v,j}$ 连续；式 (14.13) 对所有深度成立又保证加法相容，因此 $\eta$ 是到普通乘积的连续群同态。整数 $n$ 的各坐标交集含 $[n]P_j$，所以 $\eta(n)=\nu(n)$。

阶段元 $g_t$ 的阶是其坐标阶的最小公倍数，恰为 $D_t$。于是

$$
\pi_t(\eta(u))=(u\bmod D_t)g_t,\qquad
\ker(\pi_t\circ\eta)=D_t\widehat{\mathbb Z}.
\tag{14.14}
$$

定理 13.5 表明：每个正整数 $b$ 最终整除 $D_t$，并且 $D_t\mid D_{t'}$ 当 $t\le t'$。因此这些阶段周期在全部模数中关于整除关系共尾。若 $\eta(u)=\boldsymbol O$，式 (14.14) 给出 $u\equiv0\pmod{D_t}$ 对所有 $t$ 成立，继而 $u\equiv0\pmod b$ 对每个 $b$ 成立，即 $u=0$。故 $\eta$ 单射。

整数在 $\widehat{\mathbb Z}$ 中稠密：一个基本开条件只规定有限多个相容剩余类，归并到这些模数的最小公倍数后可取一个整数代表。$\widehat{\mathbb Z}$ 是有限离散群的逆极限，因而紧 Hausdorff。连续映射 $\eta$ 的像紧且在 Hausdorff 群 $\mathcal K_f$ 中闭，整数的稠密性遂给出 $H=\overline{\nu(\mathbb Z)}$。两个连续延拓若在整数上相同，则在稠密性和 Hausdorff 性下处处相同；这给出唯一性。紧空间到 Hausdorff 空间的连续单射是到其像的同胚，故 $\eta$ 的逆映射也连续。

还可直接从有限阶段检验一个候选 $y\in\mathcal K_f$。若 $\pi_t(y)\in C_t$ 对所有 $t$ 成立，令 $b_t\pmod{D_t}$ 为使 $\pi_t(y)=b_tg_t$ 的唯一剩余类。阶段之间的自然商映射给出

$$
b_{t'}\equiv b_t\pmod{D_t}\qquad(t\le t').
\tag{14.15}
$$

共尾性把这组剩余类唯一补成 $u\in\widehat{\mathbb Z}$：对任意模数 $b$，选 $b\mid D_t$，取 $b_t$ 的模 $b$ 像即可，嵌套性保证选择无关。于是 $y$ 和 $\eta(u)$ 在所有阶段商中相同。每个有限位和每个固定深度最终进入这些商，故各坐标之差属于所有 $U_v(r)$，从而 $y=\eta(u)$。反向包含由式 (14.14) 直接成立，证明式 (14.6)。

等价的 gcd-CRT 检验还能解释哪些看似独立的局部要求实际上相容。对有限多个三元组 $i=(v,j,r)$，先要求给定目标在商 $E_0(F_v)/U_v(r)$ 中属于 $P_j$ 生成的循环子群，再将其唯一写成 $b_iP_j$，其中 $b_i$ 只在模 $d_i=d_{v,j}(r)$ 下确定。共同整数存在的充要条件是

$$
b_i\equiv b_{i'}\pmod{\gcd(d_i,d_{i'})}\quad\text{对所有 }i,i'\text{ 成立}.
\tag{14.16}
$$

这是一般整数 CRT：将各模数分解成素数幂，同一素数处只须较小幂上的剩余类一致，再用互素 CRT 合并；解是模 $\operatorname{lcm}_i d_i$ 的唯一类。加入 $n\equiv a\pmod M$ 时，把 $(M,a)$ 作为另一项即可。对一个完整阶段，所有局部要求已经合成模 $D_t$ 的类 $u\bmod D_t$，所以加入 $M,a$ 后的充要条件正是式 (14.8)。任意独立指定的局部点即使分别落在各自的循环闭包中，也仍须通过这些共同剩余类检验。

若 $u\not\equiv a\pmod M$，由定理 13.5 取 $t_0$ 使 $M\mid D_t$ 对所有 $t\ge t_0$ 成立。此时式 (14.8) 必不相容。一个自身阶段成功整数 $n\ge t_0$ 会在 $t=n$ 时满足该式左侧，矛盾。因此至多 $n<t_0$ 能成功。这没有求出 $t_0$ 的数值。

**证明（消去局部初始常数）。** 对 $v\mid2$，仍用定义 13.1 中已固定的极小整广义 Weierstrass 模型 $\mathcal E_v$，不另换子群。为避免与曲线名 $E_0$ 混淆，记 $\mathcal E_{v,0}(F_v)$ 为非奇异约化点的逆像，$\mathcal E_{v,1}(F_v)$ 为约化至单位元的点群。Silverman，*The Arithmetic of Elliptic Curves* 第二版，[VII 的章首假设、VII.2.1–2.2 及 VII.6.1（印刷页 200）](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)适用于这里：$F_v$ 是特征零的完备离散赋值域，其剩余域有限且完美。所引 VII.6.1 的结论是，分裂乘法约化时分量群阶为 $-\operatorname{ord}_v(j)$，其余情形阶至多 $4$；该定理没有剩余特征至少 $5$ 的假设。相关形式群和约化记号按作者[印刷页 122–124、188–191 的勘误](https://www.math.brown.edu/johsilve/AEC/AECErrata.pdf)理解。

实际曲线的 $j$ 不变量是 $1728$，在每个 $F_v$ 上均整。若一个极小整模型有乘法约化，VII.5.1 给出 $\operatorname{ord}_v(\Delta)>0$、$\operatorname{ord}_v(c_4)=0$，于是 $j=c_4^3/\Delta$ 有负赋值，与此整性矛盾。因此尤其排除了 VII.6.1 的分裂乘法例外，且

$$
c_v=[\mathcal E_v(F_v):\mathcal E_{v,0}(F_v)]\le4.
\tag{14.17}
$$

由 VII.2.1 的约化正合列、VII.2.2 的形式群识别以及原来固定的 $\iota_v$，有

$$
\begin{aligned}
\mathcal E_{v,0}(F_v)/\mathcal E_{v,1}(F_v)
 &\simeq\widetilde{\mathcal E}_{v,\mathrm{ns}}(k_v),\\
G_v^\circ:=\#(E_0(F_v)/U_v(1))
 &=c_v\,\#\widetilde{\mathcal E}_{v,\mathrm{ns}}(k_v).
\end{aligned}
\tag{14.18}
$$

符号 $G_v^\circ$ 在这里仅是有限群阶的整数记号，不表示连通分支。约化后的广义方程仍是

$$
y^2+\bar a_1xy+\bar a_3y
=x^3+\bar a_2x^2+\bar a_4x+\bar a_6.
$$

对每个 $x\in k_v$，这是关于 $y$ 的首一二次多项式，至多有两个根；这在特征 $2$ 及不可分情形也成立。再加唯一的无穷远点，所有约化点至多 $2\#k_v+1$，非奇异点更不超过此数。因此即使存在 wild 分歧或加法约化，也有

$$
G_v^\circ\le4(2\cdot2^{f_v}+1)\le2^{f_v+4}.
\tag{14.19}
$$

两个点的 $d_{v,j}(1)$ 均整除同一个真实商群阶 $G_v^\circ$。因此

$$
A_2\mid\prod_{v\mid2}G_v^\circ,
\qquad
A_2\le\prod_{v\mid2}G_v^\circ
\le2^{\sum_{v\mid2}f_v+4\#\{v:v\mid2\}}
\le2^{40},
\tag{14.20}
$$

最后使用 $\sum_{v\mid2}e_vf_v=d_F\le8$、$e_v,f_v\ge1$。这里仅第一式是整除式；$A_2\le2^{40}$ 是数值不等式，没有断言 $A_2\mid2^{40}$。同样，数值上界 $2^{f_v+4}$ 不被当作群阶的倍数。

深度增加仍完全复用式 (13.9)–(13.10) 的整系数乘法级数，故式 (13.5) 的共享周期整除式无需改变。将 $A_2$ 的数值上界用于式 (13.7)，并用

$$
\log2<\tfrac7{10},\qquad
c_0=28+17\log2<40,
$$

得到对整数 $h\ge2$ 有

$$
\log q(h,h;M)
<\log M+4h^2+40h+28
\le\log M+32h^2.
\tag{14.21}
$$

第一条对数估计可由 $\exp(7/10)>1+7/10+(7/10)^2/2+(7/10)^3/6>2$ 得到；最后一个不等式来自

$$
28h^2-40h-28=28(h-2)^2+72(h-2)+4\ge0.
$$

这证明式 (14.9)，无需计算实际局部阶，也未对特征 $2$ 的模型作短方程假设。

**证明（完全显式的共同起点）。** 固定整数 $X\ge X_0(M,\gamma)$，置

$$
t=\log\log X,\qquad H_X=h(2X),\qquad
R=\rho(2X),\qquad Q_X=M\exp(32H_X^2).
\tag{14.22}
$$

这里 $t\ge T$，特别地 $t\ge16$、$st\ge16$、$m\le st/16$、$t^{1/3}\ge1024/s$。其中 $st\ge16$ 由 $t\ge(1024/s)^3$ 和 $0<s<1/2$ 即得。$X\ge16$ 时，$2X+16\le3X$ 且 $\log(3X)\le2\log X$，故

$$
\log\log(2X+16)\le t+\log2<t+1,
\qquad H_X^2\le(t+1)^{2/3}\le2t^{2/3}.
\tag{14.23}
$$

最大值中的常数 $2$ 不妨碍该界，因为 $(t+1)^{1/3}>2$。因此

$$
\log Q_X=m+32H_X^2
\le m+64t^{2/3}
\le\frac{st}{16}+\frac{st}{16}
=\frac{st}{8}.
\tag{14.24}
$$

由 $s<1/2$、$t\ge16$，有 $\log(4Q_X)\le2+st/8\le t$，也有 $\log(2Q_X)\le t$。又 $e^t\ge2t$，故

$$
X\ge4Q_X,\qquad
\log\frac{X}{2Q_X}\ge e^t-t\ge\tfrac12e^t.
\tag{14.25}
$$

对 $X\ge3$，$\log(2X+2)\le2\log X=2e^t$，而 $4\gamma=1-2s$，所以

$$
\begin{aligned}
2^{16}Q_X^2R^{-4}
&\le2^{16+4\gamma}\exp\bigl((s/4+4\gamma)t\bigr)\\
&\le2^{17}\exp\bigl((1-7s/4)t\bigr)
\le\tfrac12e^t.
\end{aligned}
\tag{14.26}
$$

末步成立是因为 $7st/4\ge28>18\log2$。结合式 (14.25) 得到无需任何未知常数的充分不等式

$$
0<R<1,\qquad X\ge4Q_X,\qquad
\log\frac{X}{2Q_X}\ge2^{16}Q_X^2R^{-4}.
\tag{14.27}
$$

此处没有声称 $R\le1/2$；对任意小的正 $\gamma$，式 (14.10) 也不需要推出该条件。

**证明（目标一致计数及自身阶段下降）。** 设 $u\equiv a\pmod M$，记

$$
D=D_{2X},\qquad q=\operatorname{lcm}(M,D)
=q(H_X,H_X;M)\le Q_X.
$$

由式 (14.8)，联立 $n\equiv a\pmod M$ 与 $n\equiv u\pmod D$ 给出模 $q$ 的唯一整数类，取其代表 $0\le c<q$。该类在 $(X,2X]$ 中恰为

$$
\begin{aligned}
n_k&=c+q(k_0+k),\qquad
k_0=\left\lfloor\frac{X-c}{q}\right\rfloor+1,\quad 0\le k<K,\\
K&=\left\lfloor\frac{2X-c}{q}\right\rfloor
-\left\lfloor\frac{X-c}{q}\right\rfloor
\ge\frac Xq-1\ge\frac X{2q}.
\end{aligned}
\tag{14.28}
$$

式 (14.27) 保证

$$
\log K\ge\log\frac X{2q}
\ge2^{16}Q_X^2R^{-4}\ge256q^2.
\tag{14.29}
$$

对这个有限块，以 $L=q$、$N=K$ 和 $\beta=(c+qk_0)\alpha$ 直接调用定理 12.2 的极端差异度，得到

$$
\mathcal D_K(\beta,q)
<\frac{128q}{\sqrt{\log K}}
\le\frac{R^2}{2}.
\tag{14.30}
$$

前件 $K\ge\exp(256L^2)$ 已由式 (14.29) 验证，起点 $\beta$ 可任意，未作星差异度转换。

为在所有 $z$ 上保留同一个常数，逐坐标选取一个不跨切口的半开区间 $I_j\subset[0,1)$，长度恰为 $R$，其圆像包含于 $\{x:\|x-z_j\|_{\mathbb T}<R\}$。下面给出包括端点的选择。若 $R>1/2$，该圆邻域为全圆，取 $I_j=[0,R)$。若 $0<R\le1/2$，取 $z_j$ 的代表 $w\in[0,1)$：当 $w+R\le1$ 时取 $[w,w+R)$；否则令

$$
\delta=\min((1-w)/2,R/2)>0,
\qquad I_j=[w-R+\delta,w+\delta).
\tag{14.31}
$$

后一情形 $w>1-R\ge R$，所以区间在 $[0,1)$ 内，且其每一点与 $w$ 的通常距离严格小于 $R$。前一情形的右端点被排除，亦有严格不等式。因此 $I_1\times I_2$ 是定义 12.1 中的单个盒子，面积 $R^2$，并处于所需开目标内；不必把跨切口圆弧分成多个盒子。

由式 (14.30)，在此盒中的整数数量严格大于 $KR^2/2\ge XR^2/(4q)$。这些整数全部满足 $n\equiv u\pmod{D_{2X}}$，所以式 (14.13)–(14.14) 给出

$$
[n]P_j-\eta_{v,j}(u)\in U_v(H_X)
\qquad(p\le H_X,\ v\mid p,\ j=1,2).
\tag{14.32}
$$

对每一个被计入的同一个 $n\le2X$，有 $h(n)\le H_X$、$U_v(H_X)\subseteq U_v(h(n))$、$R\le\rho(n)$。其模 $M$ 的条件也已满足，故它属于式 (14.5) 的自身阶段成功集合。这一步同时减少地方集合和降低深度，包含区间跨过 $h$ 跳点的情形。于是得到式 (14.11) 的第一行，第二行由 $q\le Q_X$ 得到。

对任意固定 $\varepsilon>0$，式 (14.23) 表明

$$
\log(4Q_X)+2\gamma\log2
\le\log4+m+64t^{2/3}+2\gamma\log2
\le\varepsilon t
\quad\text{对充分大的 }t\text{ 成立}.
\tag{14.33}
$$

这个充分大阈值仅含 $M,\gamma,\varepsilon$。故 $4q(\log(2X+2))^{2\gamma}\le(\log X)^{2\gamma+\varepsilon}$，式 (14.12) 随之成立，且对 $u,z,a$ 一致。

**证明（联合闭包与几何含义）。** 式 (14.12) 的右端趋于无穷，每个相容目标都有趋于无穷的成功整数序列。沿任意这样的序列，实端由 $\rho(n)\to0$ 得到 $n\alpha\to z$；对每个固定 $v\mid p$ 和深度 $r$，最终有 $h(n)\ge\max(p,r)$，从而式 (14.5) 给出 $[n]P_j-\eta_{v,j}(u)\in U_v(r)$。由于这些子群为邻域基，有限端在每个固定坐标上趋于 $\eta(u)$，即在普通乘积拓扑中收敛。这证明式 (14.7) 的右侧包含于左侧，且可以删去任意有限的整数前缀。反向包含是因为每个轨道点已在相应的闭集内：$H$ 紧闭，$a+M\widehat{\mathbb Z}$ 紧闭，其 $\eta$ 像也紧闭。第一行取 $M=1$ 即得。

$\widehat{\mathbb Z}$ 完全不连通，故 $H$ 亦然；$\mathbb T^2$ 连通。任一连通子集投影到 $H$ 后只能是单点，反之 $\mathbb T^2\times\{\eta(u)\}$ 连通。因此这些恰为全部连通分支，单位分支和分量群分别如所述；后者的同构由投影到 $H$ 再取 $\eta^{-1}$ 给出。

用白话说，同一个整数驱动两个实表盘，也驱动每个有限位上的离散刻度。实表盘的目标可以在两只圆上连续移动；有限刻度的目标却不是逐个随意挑选的旋钮。一个 profinite 整数是一份对所有模数彼此一致的剩余类说明书，它不是一个额外的普通整数。局部商只能读到说明书的有限一页；两个地方若共同看见某个模数，就必须在那一页给出同一答案。式 (14.16) 正是这项共同整数检查，式 (14.6) 说明通过全部有限阶段检查恰好刻画全部极限目标。

在一个二倍区间中，先按右端点规定最深的有限检查和最小的实窗口。相容性把有限检查并为一个整数类，沿这个类数两只实表盘落入目标盒的次数；统一差异度把目标盒放在哪里都能承受的误差压到面积的一半以下。局部上界保证共同步长增长得足够慢，式 (14.10) 则给出不依赖目标位置的数值充分起点。留下的每个整数通过比自身阶段更强的检查，故也通过自身阶段。随着见证整数增大，每个固定有限放大镜最终加入并不断加深，同时实表盘趋向指定位置；这正是乘积拓扑所要求的无限极限，而不是在某个有限整数上完成无限精度。

一致性指的是同一条计数下界及同一个起点适用于全部相容目标。不同目标可以有不同的见证整数，并不要求一个整数同时落入所有目标。若 $u$ 不可计算，以上存在性证明也没有提供读取其全部剩余类的可计算算法。有限阶段是有限个精确商条件；无限目标是这些条件的相容极限，两者的量词不同。

本定理的数值起点规模极大，不声称可实用计算或给出最优阶，也不计算精确局部阶或不相容类的排除阈值。目标空间只含指定实两圆和 $H$，不是全部实嵌入上的断言，也不是任意独立局部目标、球面或 solenoid 的断言。目标 $u,z$ 固定；结论不涵盖任意逐整数移动目标或更快的局部增长安排。它不包含完整的 $\mathbb Z/\mathbb Q$ 定义、素数模式与高度的额外桥梁，亦不包含量子起源的证明。$\square$

## 追加锚（本行以下为增补区）

## 15. 实际共轭点的二进极小整模型与全部精度的精确共同周期

**定义 15.1（实际局部域及根的固定）。** 沿用定义 11.1、13.1 的 $F,E_0,P_1,P_2$，不改变正实根所确定的全局点。记

$$
a=\sqrt2,\qquad b=\sqrt{3-a},\qquad c=\sqrt{3+a},
\qquad F=\mathbb Q(a,b,c).
\tag{15.1}
$$

先任取 $v\mid2$，将这些全局元素映入 $L=F_v=\mathbb Q_2(a,b,c)$。令 $h$ 是 $\mathbb Q_2$ 中满足 $h^2=-7$、$h\equiv1\pmod4$ 的唯一根，并在 $L$ 中定义

$$
i=\frac{bc}{h},\qquad
\zeta=\frac{1+i}{a},\qquad
\lambda=\zeta-1,\qquad
u=b-\zeta,\qquad
\varpi=\frac{u}{\lambda}.
\tag{15.2}
$$

记 $\mathcal O,\mathfrak m,k$ 为 $L$ 的整数环、极大理想和剩余域；非零元素的赋值取离散整数归一化 $v_L(\mathfrak m)=1$，零的赋值为 $+\infty$。定义中 $h$ 的存在性和 $\varpi$ 的赋值在下面的实际域计算中给出。

**定理 15.2（实际二进域的次数、分歧及全实边界）。** $F$ 的全局次数恰为 $8$，在 $2$ 上只有一个地方 $v$，并且

$$
[L:\mathbb Q_2]=8,\qquad e_v=8,\qquad f_v=1,
\qquad k=\mathbb F_2,\qquad v_L(\varpi)=1.
\tag{15.3}
$$

局部域 $L$ 含有式 (15.2) 的 $i$，满足 $i^2=-1$；全局域 $F$ 却是全实域，因而 $i\notin F$。这里“局部含有 $i$”不改变定义 11.1 的实嵌入。

**证明。** 对 $H(Z)=Z^2+7$，有 $v_2(H(1))=3>2v_2(H'(1))=2$。Hensel 提升给出 $h\in1+4\mathbb Z_2$；另一根为 $-h\in3+4\mathbb Z_2$，所以该根唯一。也可在本项计算内直接用收敛二项式级数

$$
h=\sum_{n\ge0}\binom{1/2}{n}(-8)^n.
$$

对 $n\ge1$，第 $n$ 项的 $2$ 进赋值为 $2n-v_2(n!)\ge n+1$，故该级数收敛、属于 $1+4\mathbb Z_2$，且平方为 $1-8=-7$。这给出所用 Hensel 根的具体指定。

由于 $b^2c^2=7$，式 (15.2) 给出 $i^2=-1$，继而

$$
\zeta^2=i,\qquad \zeta^4=-1,\qquad
\zeta+\zeta^{-1}=a.
$$

令 $M=\mathbb Q_2(\zeta)=\mathbb Q_2(a,i)$。$\lambda=\zeta-1$ 满足

$$
\lambda^4+4\lambda^3+6\lambda^2+4\lambda+2=0.
\tag{15.4}
$$

这是 $2$-Eisenstein 多项式，故 $[M:\mathbb Q_2]=4$，$M$ 全分歧，$\lambda$ 为其素元。以 $v_M(\lambda)=1$ 归一化，有

$$
v_M(2)=4,\qquad v_M(a)=2,\qquad v_M(1-i)=2.
$$

最后一个等式也由 $(1-i)^2=-2i$ 直接得到。因 $c=hi/b$，有 $L=M(b)$，所以 $[L:M]\le2$。为决定这一剩余扩张而不预设分歧，考察

$$
(3-i-a)(3-i+a)=6(1-i),\qquad
(3-i+a)-(3-i-a)=2a.
$$

乘积与差的 $v_M$ 赋值都为 $6$。若两因子的赋值不同，差的赋值等于较小者，即较小者为 $6$，则乘积赋值大于 $12$，矛盾。因此两者赋值相同，均为 $3$，特别地

$$
v_M(3-a-i)=3.
\tag{15.5}
$$

将 $v_M$ 延拓到 $L$，暂仍记为 $w$，使 $w|_M=v_M$。由

$$
(b-\zeta)(b+\zeta)=3-a-i,\qquad
(b+\zeta)-(b-\zeta)=2\zeta
$$

可同样判定两因子的 $w$ 赋值相等：若不等，较小者须为 $4$，而乘积赋值不可能为 $3$。故

$$
w(b-\zeta)=w(b+\zeta)=\frac32.
$$

$M$ 上的值群因此至少扩大两倍，而扩张次数至多为 $2$。于是 $[L:M]=e(L/M)=2$、$f(L/M)=1$，且 $v_L=2w$。从而 $e(L/\mathbb Q_2)=8$、$f(L/\mathbb Q_2)=1$，并且

$$
v_L(u)=3,\qquad v_L(\lambda)=2,\qquad
v_L(u/\lambda)=1.
\tag{15.6}
$$

这已经对任取的 $v\mid2$ 证明了局部次数为 $8$。而定义 13.1 给出的全局上界为 $[F:\mathbb Q]\le8$，故由 $\sum_{v\mid2}[F_v:\mathbb Q_2]=[F:\mathbb Q]$ 可知全局次数恰为 $8$，且只有这一个地方。

任意嵌入 $F\hookrightarrow\mathbb C$ 都将 $a$ 送到 $\pm\sqrt2$，将 $b,c$ 送到正数 $3\mp\sqrt2$ 的某个平方根，所以三个生成元的像均为实数。故 $F$ 全实。$h$ 是完备域 $\mathbb Q_2$ 中选出的元素，表达式 $bc/h$ 只断言属于 $L$，不声称属于 $F$。$\square$

**定义 15.3（完全指定的广义模型）。** 在定理 15.2 的唯一二进域中置

$$
s=\zeta(1+a),\qquad t=1-i.
$$

对 $E_0:Y^2=X^3-X$ 使用保单位元的坐标变换

$$
X=u^2x+i,\qquad
Y=u^3y+u^2sx+t.
\tag{15.7}
$$

记其逆向给出的同构为 $\iota_*:E_0\to\mathcal E_*$，其中

$$
\mathcal E_*:\quad y^2+a_1xy+a_3y
=x^3+a_2x^2+a_4x+a_6,
\tag{15.8}
$$

系数全部指定为

$$
\begin{aligned}
a_1&=\frac{2\zeta(1+a)}u,&
a_2&=\frac{-2ia}{u^2},&
a_3&=\frac{2(1-i)}{u^3},\\
a_4&=\frac{-2a(1+2a)}{u^4},&
a_6&=0.
\end{aligned}
\tag{15.9}
$$

这里 $u,\zeta,i$ 均由式 (15.2) 固定，不需要另外选择单位或素元。

**定理 15.4（该模型整且极小）。** 定义 15.3 的各系数、判别式及不变量满足

$$
\begin{gathered}
(v_L(a_1),v_L(a_2),v_L(a_3),v_L(a_4),v_L(a_6))
=(5,6,3,0,+\infty),\\
\Delta_* =\frac{64}{u^{12}},\qquad v_L(\Delta_*)=12,
\qquad c_{4,*}=\frac{48}{u^4},\quad v_L(c_{4,*})=20,
\qquad c_{6,*}=0.
\end{gathered}
\tag{15.10}
$$

$\mathcal E_*$ 是 $L$ 上的极小整广义 Weierstrass 模型。特别地，不能再经任何保单位元的坐标变换得到判别式赋值更小的整模型。

**证明。** 将式 (15.7) 代入原方程，广义 Weierstrass 变换公式给出

$$
\begin{aligned}
ua_1&=2s,&u^2a_2&=3i-s^2,&u^3a_3&=2t,\\
u^4a_4&=-1+3i^2-2st,&
u^6a_6&=i^3-i-t^2.
\end{aligned}
\tag{15.11}
$$

这些是 Silverman，*The Arithmetic of Elliptic Curves*，第二版，[III §1，Table 3.1（印刷页 45）](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的实际代入。利用

$$
s^2=i(3+2a),\qquad \zeta(1-i)=a,\qquad t^2=-2i
$$

即得式 (15.9)。定理 15.2 给出 $v_L(2)=8$、$v_L(a)=v_L(1-i)=4$、$v_L(u)=3$；$1+a$ 和 $1+2a$ 均为单位。因此系数赋值逐项为式 (15.10) 所列，模型整。原模型的 $\Delta=64,c_4=48,c_6=0$ 及同一张变换表给出其余等式。这里尚未使用极小性。

下面排除全部进一步整缩放。若 $\mathcal E_*$ 非极小，取一个真正使判别式赋值最小的整模型，其存在只用非负整数赋值的良序性。Silverman [VII.1.3(d)（印刷页 187）](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 保证从整模型到该极小模型的变换可写成

$$
x=\eta^2x'+R,\qquad
y=\eta^3y'+\eta^2Sx'+T,
\qquad \eta,R,S,T\in\mathcal O,\quad\eta\ne0.
\tag{15.12}
$$

判别式赋值变为 $12-12v_L(\eta)\ge0$。非极小假设强制 $v_L(\eta)=1$；不存在更大的正整数可选。这一步只对假设存在的较小模型应用该经典命题，没有将待证模型的极小性作前提。

新系数整尤其要求下列三个分子分别属于 $\mathfrak m^2,\mathfrak m^4,\mathfrak m^6$：

$$
\begin{aligned}
N_2&=a_2-Sa_1+3R-S^2,\\
N_4&=a_4-Sa_3+2Ra_2-(T+RS)a_1+3R^2-2ST,\\
N_6&=Ra_4+R^2a_2+R^3-Ta_3-T^2-RTa_1.
\end{aligned}
\tag{15.13}
$$

在 $k=\mathbb F_2$ 中先看 $N_4$：只有 $a_4$ 和 $3R^2$ 可能非零，且 $\bar a_4=1$，所以 $\bar R=1$。再看 $N_2$ 得 $\bar S=1$。最后 $N_6$ 的约化为 $1+1-\bar T^2$，故 $T\in\mathfrak m$。

式 (15.10) 与这些整性给出

$$
a_4+3R^2-Sa_3\in\mathfrak m^4.
\tag{15.14}
$$

事实上，$N_4$ 中被略去的三项赋值分别至少为 $14,5,9$。再用恒等式

$$
N_6-(RSa_3-T^2)
=R(a_4+3R^2-Sa_3)-2R^3+R^2a_2-Ta_3-RTa_1,
\tag{15.15}
$$

右侧各项赋值至少为 $4,8,6,4,6$。由 $N_6\in\mathfrak m^6$ 得到

$$
RSa_3-T^2\in\mathfrak m^4.
\tag{15.16}
$$

然而 $R,S$ 是单位，故 $v_L(RSa_3)=3$；$T^2$ 的赋值为偶数或 $+\infty$。若 $v_L(T)=1$，差的赋值为 $2$；若 $v_L(T)\ge2$ 或 $T=0$，差的赋值为 $3$。两种情形均与式 (15.16) 矛盾。故没有判别式更小的整模型，极小性得证。$\square$

**定理 15.5（正确标号两点的初始深度、全整数倍及模型无关性）。** 对 $j=1,2$，$\iota_*(P_j)$ 都约化至 $O$，并且以 $t_*=-x/y$ 为形式参数时，

$$
v_L(t_*(\iota_*(P_j)))=15.
\tag{15.17}
$$

沿用定义 13.1 已允许的任意极小整模型 $\mathcal E_v$、原来固定的保单位元同构 $\iota_v$ 及其参数 $t_v$。对每个非零整数 $m$，有

$$
\iota_v([m]P_j)\in\mathcal E_{v,1}(L),\qquad
v_L\bigl(t_v(\iota_v([m]P_j))\bigr)
=15+8v_2(m),\qquad j=1,2.
\tag{15.18}
$$

这里 $v_2(m)=v_2(|m|)$；$m=0$ 时两点的倍数都是 $O$，参数赋值为 $+\infty$。对所有整数 $r\ge1$，定义 13.1 的原有子群及精确阶满足

$$
\begin{aligned}
[m]P_j\in U_v(r)
&\quad\Longleftrightarrow\quad
2^{\kappa(r)}\mid m\qquad(m\in\mathbb Z),\\
d_{v,1}(r)=d_{v,2}(r)
&=2^{\kappa(r)},\qquad
\kappa(r)=\max\left(0,\left\lceil\frac{r-15}{8}\right\rceil\right).
\end{aligned}
\tag{15.19}
$$

因此两个点在该二进地方的共同精确返回周期也是 $2^{\kappa(r)}$。这些结论对原先任意极小模型和原同构成立，没有改定义 (13.1) 的过滤。

**证明（先判约化，再求参数）。** 按定义 11.1 的标号，实际坐标是

$$
\begin{aligned}
X(P_1)&=\frac{115-27a}{56},&
Y(P_1)&=\frac{-660+417a}{32b^3},\\
X(P_2)&=\frac{115+27a}{56},&
Y(P_2)&=\frac{-660-417a}{32c^3}.
\end{aligned}
\tag{15.20}
$$

特别地，$P_2$ 的纵坐标含 $-417a$，不是 $P_1$ 的纵坐标只替换分母。$b,c$ 均为单位；$115\pm27a$ 为单位；$v_L(660)=16$、$v_L(417a)=4$。故两个点均有

$$
v_L(X)=-24,\qquad v_L(Y)=-36.
\tag{15.21}
$$

由式 (15.7) 的逆变换

$$
x=\frac{X-i}{u^2},\qquad
y=\frac{Y-s(X-i)-t}{u^3},
$$

因 $i,s$ 为单位、$v_L(t)=4$，分子中最低赋值项分别唯一为 $X,Y$，得到

$$
v_L(x)=-30,\qquad v_L(y)=-45.
\tag{15.22}
$$

将射影坐标 $[x:y:1]$ 乘以 $\varpi^{45}$，三个坐标的赋值依次为 $15,0,45$，所以约化恰为 $[0:1:0]=O$。这先建立了约化核的成员资格，随后才可用 $-x/y$ 作为形式参数，得其赋值 $15$。这里没有用一个仿射比值的正赋值替代约化至 $O$ 的检验。

**证明（全部整数倍的精确深度）。** 在这个整模型的形式群上，Silverman [IV.2.3(a) 及 VII.2.2](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 给出整系数级数及约化核识别

$$
[n](T)=nT+\sum_{\ell\ge2}c_{n,\ell}T^\ell,
\qquad c_{n,\ell}\in\mathcal O,\qquad n\in\mathbb Z.
\tag{15.23}
$$

形式群、形式逆元和约化记号按作者[印刷页 122–124、188–191 的勘误](https://www.math.brown.edu/johsilve/AEC/AECErrata.pdf)理解。若 $v_L(T)=s_0>8$，对倍点而言，线性项赋值为 $8+s_0$，其余各项赋值至少为 $2s_0>8+s_0$；级数收敛且最低项唯一，故

$$
v_L([2](T))=s_0+8.
\tag{15.24}
$$

若 $n$ 为奇整数，包括负奇整数，线性项系数为单位，其赋值为 $s_0$，严格小于其余各项的赋值。因此 $v_L([n](T))=s_0$。将任意 $m\ne0$ 唯一写成 $m=2^kn$，其中 $k=v_2(m)\ge0$、$n$ 为奇整数，从初始 $s_0=15$ 反复应用式 (15.24)，始终留在 $s_0>8$ 的范围内，给出 $15+8k$。每一步参数均非零，且倍点与该形式群的识别交换。

**证明（回到任意原极小模型）。** 比较 $\mathcal E_*$ 与定义 13.1 中已固定的 $\mathcal E_v$，使用的正是 $\iota_*\circ\iota_v^{-1}$，所以也涵盖原同构的任意选择。两者均已证明或已假定为极小整模型；Silverman [VII.1.3(b)](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 此时才给出

$$
x=\varepsilon^2x_v+R_0,\qquad
y=\varepsilon^3y_v+\varepsilon^2S_0x_v+T_0,
\qquad \varepsilon\in\mathcal O^\times,\quad R_0,S_0,T_0\in\mathcal O.
\tag{15.25}
$$

该齐次线性坐标变换及其逆变换的系数都整、行列式均为单位，并固定 $O$。故一个点在某一模型约化至 $O$ 当且仅当它在另一模型约化至 $O$。

还须检查全部深度，而不仅是约化核。令 $Z=t_v$，$W=-1/y_v$。形式展开 $W=W(Z)\in Z^3\mathcal O[[Z]]$ 的首项为 $Z^3$，来自 VII.2.2 所用的 IV.1.1 展开。代入式 (15.25)，得到确切的参数变换

$$
t_*
=\frac{\varepsilon^2Z+R_0W(Z)}
 {\varepsilon^3-\varepsilon^2S_0Z-T_0W(Z)}
=\varepsilon^{-1}Z+Z^2\mathcal O[[Z]].
\tag{15.26}
$$

分母常数项为单位，所以此式具有整系数；逆坐标变换同理给出 $Z=\varepsilon t_*+t_*^2\mathcal O[[t_*]]$。两式均在 $\mathfrak m$ 上收敛，且线性项赋值严格小于其余项，因而两参数的非零赋值完全相同。由此对每个 $r\ge1$，两个极小模型拉回 $\mathfrak m^r$ 所得的子群相同。这证明式 (15.18) 确实使用原来的 $U_v(r)$，而非另设的过滤。

最后，对 $m\ne0$，成员条件就是 $15+8v_2(m)\ge r$，等价于 $v_2(m)\ge\kappa(r)$；$m=0$ 时两边也都成立。商群中 $P_j$ 的阶是满足该条件的最小正整数，故为式 (15.19)。两个点的阶相同，取最小公倍数不再增大周期。特别地，$1\le r\le15$ 时周期为 $1$，$16\le r\le23$ 时为 $2$，$24\le r\le31$ 时为 $4$；边界 $r=15,16,23,24$ 均由同一公式包含。$\square$

**推论 15.6（接回 $A_2$ 与共同整数周期）。** 定义 (13.2) 的实际初始常数为 $A_2=1$。令

$$
D_{\mathrm{odd}}(B,r)
=\operatorname{lcm}\{d_{w,j}(r):3\le p\le B,\ w\mid p,\ j=1,2\},
\tag{15.27}
$$

空集的最小公倍数取 $1$。对所有实数 $B\ge2$ 及整数 $r,M\ge1$，原共同周期精确写成

$$
q(B,r;M)
=\operatorname{lcm}\bigl(M,2^{\kappa(r)},D_{\mathrm{odd}}(B,r)\bigr).
\tag{15.28}
$$

特别地，$2\le B<3$ 时 $q(B,r;M)=\operatorname{lcm}(M,2^{\kappa(r)})$。在任意 $B\ge2$ 时，其 $2$ 进指数满足

$$
v_2(q(B,r;M))
=\max\bigl(v_2(M),\kappa(r),v_2(D_{\mathrm{odd}}(B,r))\bigr).
\tag{15.29}
$$

**证明。** 定理 15.2 给出唯一的 $v\mid2$，定理 15.5 给出 $d_{v,1}(1)=d_{v,2}(1)=1$，故 $A_2=1$。将二进地方的精确阶代入原定义 (13.2)，即得式 (15.28)，其最小公倍数的素数赋值公式给出式 (15.29)。对式 (13.3) 的自身阶段，只需代入 $B=r=h(n)$，二进条目便为 $2^{\kappa(h(n))}$；原来所有地方仍由同一个整数承担。

用白话说，先找对量尺，再读返回精度。原短方程虽然整，却不是这里的极小量尺；式 (15.7) 把它换成已排除进一步整缩放的模型。两个实际点在这把量尺下都已经落入单位元的第 $15$ 层。乘一个奇整数保持所在层数，每多乘一个 $2$ 就准确加深 $8$ 层。因此精度不超过 $15$ 时每个整数倍都合格；要求第 $16$ 层就必须取偶数倍，直到第 $23$ 层仍只须偶数倍；第 $24$ 层才开始要求 $4$ 的倍数。两个点的刻度完全相同，所以共同返回不增加额外因子。

改变极小坐标只把局部参数换成首项系数为单位的整级数，且逆级数同样整；这正是不同极小量尺给出相同层数的原因。它不允许使用非极小模型的层数来替换定义 13.1。式 (15.28) 只求出了二进地方这一条目的全部精确值：奇素数地方的阶仍可含有 $2$ 的幂，所以 $2^{\kappa(r)}$ 不必是 $q$ 的完整 $2$-主部分。

实际点及其标号来自 [Brox 固定源码的 “The quadratic-field elliptic curve”](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex)，变换与形式群工具为上述 Silverman 的经典结果。这里的推导补出该固定数据的局部次数、具体极小模型、初始深度及所有精度的二进阶，不作一般局部理论或文献优先权的主张。它不求奇素数地方的精确阶，不补出完整的 $\mathbb Z/\mathbb Q$ 定义或物理对应；§§13–14 的一般联合返回结论及其余边界继续沿用。$\square$

## 追加锚（本行以下为增补区）

## 16. 实际共同周期的二次对数主阶、交叉因子吸收与加权入口余项

**定义 16.1（共同局部阶与入口）。** 本节保持定义 11.1、13.1 的实际 $F,E_0,P_1,P_2,U_v(r),q(B,r;M)$，赋值仍取 $\operatorname{ord}_v(\mathfrak m_v)=1$。有理数上的 $v_p$ 则取 $v_p(p)=1$，故 $\operatorname{ord}_v|_{\mathbb Q^\times}=e_vv_p$。沿用 $a,b,c$ 的正实根，另记

$$
\begin{gathered}
a^2=2,\quad b^2=3-a,\quad c^2=3+a,\quad bc=\sqrt7,\\
K=F(i),\qquad [i](X,Y)=(-X,iY),\qquad i^2=-1.
\end{gathered}
\tag{16.1}
$$

这里 $K$ 专指本节的复乘扩域，不是定义 11.1 中暂用同一字母的二次域。对每个有理素数 $p$（包括 $2,7$）及整数 $r\ge1$，定义 $\delta_{p,v}(r)=\operatorname{lcm}(d_{v,1}(r),d_{v,2}(r))$（$v\mid p$），并定义 $\delta_p(r)=\operatorname{lcm}_{v\mid p}\delta_{p,v}(r)$。命题 16.2 将证明 $\delta_p(r)=\delta_{p,v}(r)$ 对每个 $v\mid p$ 成立。以下只有入口记号 $n_p,t_p$ 限于 $p\ne2,7$，定义为

$$
\begin{aligned}
n_p&=\operatorname{lcm}\bigl(\operatorname{ord}(\overline P_1),
                         \operatorname{ord}(\overline P_2)\bigr),\\
t_p&=\min_{j=1,2}\operatorname{ord}_v
               \bigl(t([n_p]P_j)\bigr),\qquad t=-X/Y.
\end{aligned}
\tag{16.2}
$$

横线是原好约化模型 $E_0$ 在同一个 $k_v$ 中的约化，$\overline O=O$ 的阶取 $1$；参数在此式中只用于已经约化为 $O$ 的点。所有 $[n_p]P_j$ 非零，故 $t_p$ 是有限正整数。记

$$
\begin{gathered}
\mathcal G_H=\{p\le H:p\ne2,7\},\qquad
h_0=\widehat h(P_1)=\widehat h(P_2),\qquad C_E=2\log2,\\
A=64h_0,\qquad B=8C_E,\qquad
b_p(H)=v_p(\delta_p(H)),\qquad
W(H)=\sum_{p\in\mathcal G_H}(t_p-1)\log p.
\end{gathered}
\tag{16.3}
$$

高度为绝对对数高度及 §12 的典范高度归一化，特别地复用 (12.7) 对所有代数点的 $h(xT)\le2\widehat h(T)+C_E$，不另换比较常数。高度的共轭不变性及 (12.8) 给出 $0<h_0\le\log82/2$。

**命题 16.2（实际符号轨道严格运输原过滤）。** $F/\mathbb Q$ 是次数 $8$ 的 $D_4$ Galois 扩张；每个自同构把有序点对 $(P_1,P_2)$ 变为其带独立符号的排列。若 $g(v)=w$，则完备域同构诱导

$$
g(U_v(r))=U_w(r)\qquad(r\ge1).
\tag{16.4}
$$

因而对每个有理素数 $p$ 及整数 $r\ge1$，$\delta_{p,v}(r)$ 与 $v\mid p$ 无关且等于 $\delta_p(r)$；对所有 $B_0\ge2$、整数 $r,M\ge1$，有原对象的精确接口

$$
\begin{aligned}
q(B_0,r;M)&=\operatorname{lcm}\bigl(M,\{\delta_p(r):p\le B_0\}\bigr),\\
\bigl([m]P_j\in U_v(r)\text{ 对所有 }p\le B_0,v\mid p,j\bigr)
&\ \Longleftrightarrow\ \delta_p(r)\mid m\text{ 对所有 }p\le B_0.
\end{aligned}
\tag{16.5}
$$

第二行对所有 $m\in\mathbb Z$ 成立，包括零和负数。

**证明。** $F$ 是 $Z^4-6Z^2+7$ 的分裂域，根为 $\pm b,\pm c$，且 $a=3-b^2$。§15 已给出 $[F:\mathbb Q]=8$。自同构固定 $a$ 时独立改变 $b,c$ 的符号；反转 $a$ 时交换 $b,c$ 并可独立改变符号。这八个作用给出上述二面体群。由定义 11.1 的坐标，$b$ 或 $c$ 换号恰将相应点取负，$a$ 换号并交换 $b,c$ 则交换两点。Galois 群在 $p$ 上的地方间传递，且完备域同构保整数归一化赋值。

奇素数处原方程在 $\mathbb Q$ 上定义，参数 $t$ 也在 $\mathbb Q$ 上定义，故约化为 $O$ 与 $\operatorname{ord}_v(t)\ge r$ 同时运输。二进处将原先选定的极小模型共轭，仍为极小整模型；它与目标地方原先选定的极小模型之间正是 §15 所用的保单位元整变换。式 (15.25)–(15.26) 表明形式参数互为首项系数为单位的整级数，因而保每个 $\mathfrak m^r$，不是只保第一层。这给出 (16.4)，不改变原同构或原过滤。对子群取负不改变成员条件；排列两点不改变两个阶的最小公倍数。因此共同阶与地方无关。最后在有限商群中 $[m]P_j\in U_v(r)$ 当且仅当 $d_{v,j}(r)\mid m$；代回定义 (13.2) 得证。$\square$

**定理 16.3（非分歧奇素数的全部精确阶）。** 对 $p\ne2,7$，$F$ 及 $K$ 在 $p$ 上均不分歧，$e_v=1$，(16.2) 的 $n_p,t_p$ 与地方无关。对每个 $r\ge1$，

$$
\delta_p(r)=n_p p^{\max(0,r-t_p)}.
\tag{16.6}
$$

更精确地，对非零整数 $m$，两点同时属于 $U_v(r)$ 的充要条件是 $n_p\mid m$ 且

$$
t_p+v_p(m/n_p)\ge r.
\tag{16.7}
$$

$m=0$ 时同时成员条件恒成立。

**证明。** 在 $\mathbb Z[1/14]$ 上先添 $a$，再添 $b,c$；各平方根的被开方元素是单位，其二次方程导数也是单位，因为 $(3-a)(3+a)=7$。这些有限 étale 扩张说明只有 $2,7$ 能分歧；再添 $i$ 不增加奇素数分歧。$E_0$ 的判别式为 $64$，故所有奇素数处好约化。约化阶有限，且倍数约化为 $O$ 当且仅当相应的阶整除该整数。因此两点同时约化为 $O$ 当且仅当 $n_p\mid m$。

对这些地方，$1>e_v/(p-1)=1/(p-1)$。Silverman 的形式对数定理 [IV.6.4](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 在整个第一层给出保赋值的群同构到 $\mathfrak m_v$。保赋值也可直接由对数及逆指数在每个 $\mathfrak m_v^r$ 上互逆得出。若 $s_j=\operatorname{ord}_v(t([n_p]P_j))$，则对任意非零整数 $u$，

$$
\operatorname{ord}_v(t([u n_p]P_j))=s_j+v_p(u).
\tag{16.8}
$$

所有参数非零：否则某个非零整数倍的实际非挠点为 $O$，违背域嵌入的单射性及 Brox 的非挠性。共同最小深度因此是 $t_p+v_p(u)$。命题 16.2 运输约化及深度，给出 $n_p,t_p$ 的地方无关性。式 (16.7) 的最小正解为 (16.6)；取负不改赋值，零倍另行成立。$\square$

**定理 16.4（实际半点、共同 Frobenius 核及下降支持）。** 对每个 $p\ne2,7$，令 $\pi$ 为 $E_0/\mathbb F_p$ 的 $p$ 次 Frobenius，$a_p=p+1-\#E_0(\mathbb F_p)$。置

$$
\begin{aligned}
\varepsilon_p&=-1\quad\Longleftrightarrow\quad
 \left(\frac2p\right)=\left(\frac7p\right)=-1,
 \qquad \varepsilon_p=1\text{ 在其余情形},\\
C_p&=
\begin{cases}
(p+1)^2-a_p^2,&\varepsilon_p=1,\\
(p-1)^2+a_p^2,&\varepsilon_p=-1.
\end{cases}
\end{aligned}
\tag{16.9}
$$

在同一个 $\overline{\mathbb F}_p$ 中，$\overline P_1,[i]\overline P_1,\overline P_2,[i]\overline P_2$ 都属于同一个群

$$
[2]G_p,\qquad
G_p=\ker(\pi^2-[\varepsilon_p]),\qquad
\#G_p=C_p,\quad \#[2]G_p=C_p/4\le p^2.
\tag{16.10}
$$

特别地，这是整数整除式而非大小比较：

$$
n_p\mid C_p/4,\qquad n_p\le p^2.
\tag{16.11}
$$

若 $p\ge11$，$n_p$ 的每个素因子均严格小于 $p$；小素数的实际值为

$$
n_3=2,\qquad n_5=5.
\tag{16.12}
$$

**证明（半点及同一个核）。** 从 Brox 固定源码 “The quadratic-field elliptic curve” 中的 $R_0=(1+a,2a)$ 及其共轭，经原归一化取得一对半点

$$
R_1=\left(\frac{1+a}{b^2},\frac{2a}{b^3}\right),\qquad
R_2=\left(\frac{1-a}{c^2},\frac{-2a}{c^3}\right),\qquad
[2]R_j=P_j.
\tag{16.13}
$$

其合法性也由 $E$ 上的 $R_0$ 代入及定义 11.1 的保群同构直接保证；两点的纵坐标符号同时按共轭运输。这对半点与原点对具有相同的带符号排列作用。

在 $v\mid p$ 取算术 Frobenius $g\in\operatorname{Gal}(F/\mathbb Q)$。若 $g(a)=a$，则 $g$ 分别给 $b,c$ 换号，故 $g^2$ 为恒等。若 $g(a)=-a$，写 $g(b)=u c,g(c)=v b$，其中 $u,v\in\{1,-1\}$；于是 $g^2$ 同时把 $b,c$ 乘以 $uv$，且 $g(bc)=uv\,bc$。在不分歧的二次子域中，$g(a)/a=(2/p)$、$g(bc)/(bc)=(7/p)$。因此 $g^2$ 对两个半点的共同作用恰为 $[\varepsilon_p]$。约化与 Frobenius 相容，故两者的约化都在 $G_p$ 中；这同时处理剩余次数为 $1,2,4$ 的情形，而没有假设所有半点已在 $\mathbb F_{p^2}$ 上。

无论 $p\bmod4$ 如何，$\pi^2$ 与 $[i]$ 交换，因为 $i^{p^2}=i$；故 $G_p$ 及其倍二像均在 $[i]$ 下稳定。Frobenius 特征多项式及 Hasse 界给出 $\deg(\pi^2-[\varepsilon_p])=C_p$。该同源的微分是 $-\varepsilon_p$，非零，故可分，几何核确有 $C_p$ 个点。$E_0[2]=\{O,(0,0),(1,0),(-1,0)\}$ 都在 $\mathbb F_p$ 上，故全在 $G_p$ 中。$p$ 为奇数保证倍二可分且其核正好这四点，因此有限群 $G_p$ 的倍二像的阶为 $C_p/4$。由 Lagrange 定理，两点的阶及其最小公倍数整除这个整数。

这里使用的经典工具仅是 Silverman [III.6、V.2.3.1、V.3–4](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的同源、Frobenius 和普通/超奇异分类；$\varepsilon_p$ 来自实际 $D_4$ 作用，不是普通性的判据。由 $a_p^2\le4p$，两种符号均有 $C_p\le(p+1)^2\le4p^2$，得大小界。

**证明（支持与小素数）。** 对 $\varepsilon_p=1$，$a_p$ 是偶数，因为有理二挠群使 $4\mid\#E_0(\mathbb F_p)$，于是

$$
\frac{C_p}{4}=
 \frac{p+1-a_p}{2}\,\frac{p+1+a_p}{2}.
\tag{16.14}
$$

当 $p\ge7$ 时，两因子均为正整数，且至多 $(p+1+2\sqrt p)/2<p$。若 $\varepsilon_p=-1$ 且 $p\equiv3\pmod4$，则 $(X^3-X)^{(p-1)/2}$ 仅含奇次幂，其 $X^{p-1}$ 系数为零，故由 Silverman V.4.1(a) 知 $E_0$ 超奇异。又因二次特征 $\chi$ 满足 $\chi(-1)=-1$，$x$ 与 $-x$ 对 $\sum_{x\in\mathbb F_p}\chi(x^3-x)$ 的贡献相消，故 $a_p=0$。从而 $C_p/4=((p-1)/2)^2$，仍只有严格较小的素因子。

剩下的分支是 $\varepsilon_p=-1$ 且 $p\equiv1\pmod4$；$\varepsilon_p=1$ 时无论普通或超奇异，均已由 (16.14) 处理。在这个剩余分支，$(X^3-X)^{(p-1)/2}=X^{(p-1)/2}(X^2-1)^{(p-1)/2}$ 的 $X^{p-1}$ 系数为 $(-1)^{(p-1)/4}\binom{(p-1)/2}{(p-1)/4}\not\equiv0\pmod p$，因为所涉阶乘的指标均小于 $p$。因此 Silverman V.4.1(a) 判定这条曲线的约化普通。由 V.3.1(b)，其几何自同源环是某个虚二次域中的序（满秩的 $\mathbb Z$-子环），且包含由 $[i]$ 给出的 $\mathbb Z[i]$，故该虚二次域就是 $\mathbb Q(i)$。$\mathbb Z[i]$ 已是该域的极大整环，故几何自同源环正是 $\mathbb Z[i]$。Frobenius 的迹与范数遂给出 $\pi=u+vi$，其中 $u,v\in\mathbb Z$、$u^2+v^2=p$、$a_p=2u$。又由 $4\mid\#E_0(\mathbb F_p)$，有 $2u\equiv p+1\equiv2\pmod4$，所以 $u$ 为奇数、$v$ 为偶数。在此 $\varepsilon_p=-1$ 的分支中，

$$
\frac{C_p}{4}
=\frac{(p-1)^2+4u^2}{4}
=\frac{(p+1)^2-4v^2}{4}
=\frac{p+1-2v}{2}\,\frac{p+1+2v}{2}.
\tag{16.15}
$$

两因子是正整数，因 $v$ 为偶数且 $p$ 为奇数；由 $|v|\le\sqrt p$，$p\ge7$ 时它们同样严格小于 $p$。这些整数因子分解而非单独的 $n_p\le p^2$，才给出下降支持。

$p=3$ 时 $\varepsilon_3=1,a_3=0$，且实际 $X_j\equiv-1$、$Y_j\equiv0$，两点约化都是非零二挠点，故 $n_3=2$。$p=5$ 时 $(2/5)=(7/5)=-1$；在 $\mathbb F_5$ 逐个 $X$ 的 $X^3-X$ 为 $0,0,1,4,0$，故 $\#E_0(\mathbb F_5)=8,a_5=-2$，得到 $C_5/4=5$。原坐标分母在 $5$ 为单位，两点均为仿射点而非 $O$；它们属于阶 $5$ 的倍二像群，故各自阶为 $5$。这证明两个例外及全部支持声明。$\square$

**命题 16.5（实际七进共同周期）。** $7$ 上有两个地方，均有 $e_v=f_v=2$。原定义的全部共同阶为

$$
\delta_7(r)=2\,7^{\lceil(r-1)/2\rceil}\qquad(r\ge1).
\tag{16.16}
$$

**证明。** 记 $\nu_7$ 为 $\mathbb Q_7$ 上满足 $\nu_7(7)=1$ 的赋值，在 $\mathbb Q_7$ 中选 $a\equiv3\pmod7$ 的平方根。由 $(3-a)(3+a)=7$，有 $\nu_7(3-a)=1$，而 $3+a\equiv6$ 是剩余非平方单位。因而添 $b$ 给出二次全分歧扩张，添 $c$ 给出二次非分歧扩张，合成局部次数 $4$、$e=f=2$；另一个 $a$ 的根给出另一个地方。全局次数 $8$ 保证恰有这两个地方。在选定完备域 $F_v$ 上，将整数归一化的 $\operatorname{ord}_v$ 简写为 $v$，则 $v|_{\mathbb Q_7^\times}=2\nu_7$，从而 $v(7)=v(3-a)=2$、$v(b)=1,v(c)=0$。下文的深度均用这个 $v$。

原坐标为 $X_1=(115-27a)/56,Y_1=(-660+417a)/(32b^3)$ 及其同时共轭 $X_2=(115+27a)/56,Y_2=(-660-417a)/(32c^3)$。在 $a\equiv3$ 的地方，$115-27a$、$-660+417a$ 均为单位，所以

$$
v(X_1)=-2,\qquad v(Y_1)=-3,\qquad v(t(P_1))=1.
\tag{16.17}
$$

这先判定 $P_1$ 约化为 $O$。对另一点使用确切恒等式

$$
X_2+1=\frac{9(19+3a)}{56},\qquad
(19+3a)(19-3a)=7^3,\qquad
(-660+417a)(-660-417a)=87822=2\cdot3^2\cdot7\cdot17\cdot41.
\tag{16.18}
$$

其中 $19-3a$ 与 $-660+417a$ 为单位，故 $v(X_2+1)=4,v(Y_2)=2$；$P_2$ 约化为 $T=(-1,0)$。其倍二斜率 $(3X_2^2-1)/(2Y_2)$ 的赋值为 $-2$，分子模 $7$ 为 $2$；倍二公式遂给出 $v(X([2]P_2))=-4,v(Y([2]P_2))=-6$，所以 $[2]P_2$ 的形式深度为 $2$。$[2]P_1$ 的深度仍为 $1$。

因此共同约化入口整数是 $2$，共同入口深度为 $1$，而两个点的个别深度并不相同。这里 $1>e/(7-1)=1/3$，形式对数在第一层即保赋值。对非零偶整数 $m=2u$，共同最小深度恰为 $1+2v_7(u)$；对奇整数，第二点仍约化为 $T$，不在第一层。另一地方由命题 16.2 运输并交换两点，给出相同条件。零倍自动合格，负倍同样适用。故最小正合格整数为 (16.16)。每乘一个 $7$ 增加的两层来自 $v(7)=2$，不是将形式群高度当作分歧指数。$\square$

**定理 16.6（四个实际方向限制共同过深入口）。** 对所有 $p\ne2,7$，有无条件的同一实际入口界

$$
(t_p-v_p(n_p))\log p\le64h_0p+8C_E=Ap+B.
\tag{16.19}
$$

此式允许 $t_p>1$，不预设单点或同时 Wieferich 素数的稀疏性。

**证明（高度与独立性）。** $F$ 全实且次数 $8$，故 $[K:\mathbb Q]=16$。Brox 固定源码的 `lem:independent` 已证明原 $P_1,P_2$ 在 $\mathbb Z[i]$ 上模挠独立，本节直接复用。于是

$$
T_1=P_1,\quad T_2=[i]P_1,\quad T_3=P_2,\quad T_4=[i]P_2
\tag{16.20}
$$

任何非平凡整数线性组合均非挠。令 $\langle S,T\rangle=(\widehat h(S+T)-\widehat h(S)-\widehat h(T))/2$。典范高度的二次性、双线性及 Galois 不变性使用 Silverman VIII.9.3；$[i]$ 是高度等距，因为它把横坐标乘以 $-1$，并与倍二交换。因而 $\langle P_j,[i]P_j\rangle=\langle[i]P_j,-P_j\rangle=0$。此外，固定 $a,b,i$ 而反转 $c$ 的 $K$-自同构固定前两个方向、反转后两个方向；每个跨两点的配对等于其相反数，也为零。共轭不变性给出四个方向的高度全为 $h_0$。因此对所有整数 $z_k$，

$$
\widehat h\left(\sum_{k=1}^4[z_k]T_k\right)
=h_0\sum_{k=1}^4z_k^2.
\tag{16.21}
$$

由 (12.8) 知 $h_0\le\log82/2$，由非挠性和正定性知 $h_0>0$；不需要重新证明高度比较或计算完整 Mordell–Weil 群。

**证明（同一个有限群中的短关系）。** 对 $K$ 的地方 $w$，以下 $U_w(r)$ 仅指原整方程在 $K_w$ 上约化为 $O$ 且原参数深度至少为 $r$ 的子群；其与 $E_0(F_v)$ 的交仍为原 $U_v(r)$。固定一个 $w\mid v\mid p$ 的 $K$ 地方。$K_w/\mathbb Q_p$ 不分歧，故其整数赋值在 $F_v$ 上仍是原赋值，且 $[K_w:\mathbb Q_p]=f_w\ge1$。在这同一个剩余域的代数闭包中，四个 $T_k$ 的约化由 (16.10) 同属大小至多 $p^2$ 的群 $[2]G_p$。取 $L=\lfloor\sqrt p\rfloor$。$(L+1)^4>p^2$，所以把 $(L+1)^4$ 个向量 $z\in\{0,\ldots,L\}^4$ 映到 $\sum[z_k]\overline T_k$，必有两个不同向量同像。作差取得 $z\ne0$、$|z_k|\le L$，使实际全局点

$$
R=\sum_{k=1}^4[z_k]T_k\in E_0(K)
\tag{16.22}
$$

在 $w$ 约化为 $O$。独立性保证 $R$ 非挠且非零；(16.21) 给出 $\widehat h(R)\le4h_0L^2\le4h_0p$。

**证明（同一关系的局部与全局账）。** 每个 $[n_p]T_k$ 在 $w$ 都属于 $U_w(t_p)$：对原两点是定义，对 $[i]$ 方向由形式群自同构保深度得到。因此同一个 $[n_p]R$ 属于 $U_w(t_p)$。$R$ 自身已经在第一层，可使用保赋值形式对数，得到

$$
s:=\operatorname{ord}_w(t(R))\ge t_p-v_p(n_p).
\tag{16.23}
$$

具体地，$\log([n_p]R)=n_p\log(R)$，所以其赋值为 $s+v_p(n_p)$，不能把 $n_p$ 的 $p$ 因子遗漏。形式展开在这个好整模型上给出 $\operatorname{ord}_w(x(R))=-2s$。在绝对高度公式中取 $|p|_w=p^{-1}$，这一处的权重为 $f_w/16$，故该处非负贡献为 $2s f_w\log p/16$，而其它各处的 $\log\max(1,|x(R)|)$ 均非负。于是

$$
\begin{aligned}
(t_p-v_p(n_p))\log p
&\le s\log p\le8h(x(R))\\
&\le16\widehat h(R)+8C_E
\le64h_0p+8C_E.
\end{aligned}
\tag{16.24}
$$

若左端非正，同一不等式仍成立。这里局部读数、抽屉所得关系及高度估计始终是一个 $R$、一个 $w$ 及原同一对点；没有把不同地方、不同关系的分别最优值拼接。$\square$

**定理 16.7（实际共同周期的有限下界与匹配主阶）。** 对所有整数 $H\ge2,M\ge1$，原共同周期满足

$$
\log q(H,H;M)
\ge H\sum_{p\in\mathcal G_H}\log p
 -64h_0\sum_{p\in\mathcal G_H}p
 -8C_E\,\#\mathcal G_H.
\tag{16.25}
$$

令 $\mathcal P(H)=\prod_{p\le H}p$。对所有整数 $H\ge7$ 及所有 $M\ge1$，还有真正的整除上包络

$$
q(H,H;M)\mid
 \operatorname{lcm}\bigl(M,5\mathcal P(H)^{H-1}\bigr).
\tag{16.26}
$$

因而每个固定 $M$ 都有无条件的

$$
\log q(H,H;M)
=H\vartheta(H)+O\left(\frac{H^2}{\log H}\right)
\sim H^2\qquad(H\to\infty).
\tag{16.27}
$$

误差常数可依赖固定 $M$ 及本节固定点；(16.26) 的阈值 $7$ 与 $M$ 无关。

**证明（下界来自实际自身分量）。** 由 (16.6)，对每个 $p\in\mathcal G_H$，

$$
\begin{aligned}
v_p(q(H,H;M))&\ge b_p(H)
=v_p(n_p)+\max(0,H-t_p)\\
&\ge H-(t_p-v_p(n_p)).
\end{aligned}
\tag{16.28}
$$

把这些不同素数的实际自身指数乘以 $\log p$ 后相加，再用 (16.19)，即得 (16.25)。右侧某一项若为负，只是一个仍有效的下界，不会删掉其原量词。这一步没有使用 $C_p$ 或任何较大消去数的最小公倍数作下界。

**证明（跨地方素因子的整除上界）。** 对 $p\in\mathcal G_H$，$t_p\ge1$，且由下降支持和 (16.12)，$v_p(n_p)=0$，唯一例外为 $v_5(n_5)=1$。因此来自 (16.6) 自身的 $p$ 指数不超过 $H-1$，在 $p=5$ 处不超过 $H$。来自 $n_p$ 的其它素因子均不超过 $H$，而 $n_p\le p^2\le H^2$ 保证每个这样的 $\ell$ 指数至多 $2\log H/\log\ell\le2\log H/\log2\le H-1$，最后一个不等式对 $H\ge7$ 成立。

§15 给出 $\delta_2(H)=2^{\kappa(H)}$，$\kappa(H)=\max(0,\lceil(H-15)/8\rceil)\le H-1$。命题 16.5 给出 $\delta_7(H)=2\cdot7^{\lceil(H-1)/2\rceil}$，其两个指数同样不超过 $H-1$。故每个实际 $\delta_p(H)$ 都整除 $5\mathcal P(H)^{H-1}$；结合 (16.5) 得 (16.26)。共同整数在这里由最小公倍数承担，大小不等式没有被改写为未经证明的整除式。

**证明（闭合主阶）。** 经典素数定理及其分部求和后果给出 $\vartheta(H)\sim H$、$\pi(H)=O(H/\log H)$、$\sum_{p\le H}p=O(H^2/\log H)$。其原始来源是 Hadamard，*Sur la distribution des zéros de la fonction ζ(s) et ses conséquences arithmétiques*，Bull. Soc. Math. France 24，199–220，[DOI:10.24033/bsmf.545](https://doi.org/10.24033/bsmf.545)；以及 de la Vallée Poussin，*Recherches analytiques sur la théorie des nombres premiers*，Ann. Soc. Sci. Bruxelles 20，183–256。这里只用无条件素数定理，不用 RH 或其误差估计。

从 (16.25) 减去 $H\vartheta(H)$，遗漏的 $2,7$ 只产生 $O(H)$；余下损失是 $O(H^2/\log H)$。从 (16.26) 则有 $\log q\le\log M+\log5+(H-1)\vartheta(H)$。两边夹住实际同一个 $q$，得到 (16.27)。$\square$

**定理 16.8（最终自身指数分解与加权次阶的精确身份）。** 可取一个与 $M$ 无关的结构阈值

$$
H_*=82^{128}.
\tag{16.29}
$$

对每个整数 $H\ge H_*$，每一素数的最大指数最终由它自己的地方取得，精确地

$$
q(H,H;M)=\operatorname{lcm}\left(M,\prod_{p\le H}p^{b_p(H)}\right)
\quad\text{对所有 }M\ge1,
\tag{16.30}
$$

其中

$$
\begin{aligned}
b_2(H)&=\kappa(H),&b_7(H)&=\left\lceil\frac{H-1}{2}\right\rceil,\\
b_p(H)&=H-t_p+v_p(n_p)\quad&&(p\in\mathcal G_H).
\end{aligned}
\tag{16.31}
$$

对固定 $M$，还须越过一个依赖 $M$ 的阈值才能删去 (16.30) 的 $M$。例如约定 $P^+(1)=1$、空集最大值为零，取

$$
H_M=\max\left(H_*,P^+(M),8v_2(M)+15,
 2\max_{\ell\text{ 奇素数}}v_\ell(M)+1\right).
\tag{16.32}
$$

则所有整数 $H\ge H_M$ 均有完整的次阶恒等式

$$
\begin{aligned}
\log q(H,H;M)
={}&(H-1)(\vartheta(H)-\log2-\log7)-W(H)\\
 &+\log5+b_2(H)\log2+b_7(H)\log7.
\end{aligned}
\tag{16.33}
$$

特别地，本节证明的加权入口余项范围为

$$
\begin{aligned}
0\le W(H)
&\le A\sum_{p\in\mathcal G_H}p+B\,\#\mathcal G_H
 +\log5-\sum_{p\in\mathcal G_H}\log p\\
&=O(H^2/\log H)\qquad(H\ge H_*).
\end{aligned}
\tag{16.34}
$$

本条不给 $W$ 更强的平均界，尤其不将 $t_p$ 替换为 $1$。

**证明（入口阈值与最终吸收）。** 对 $p\in\mathcal G_H$，由 (16.19) 和 (16.12)、下降支持，$v_p(n_p)\le1$。函数 $x/\log x$ 在 $x\ge3$ 上递增，故

$$
t_p\le\frac{Ap+B}{\log p}+v_p(n_p)
\le\frac{AH}{\log H}+\frac B{\log3}+1.
\tag{16.35}
$$

$A\le32\log82$，而 $H\ge82^{128}$ 保证 $AH/\log H\le H/4$；$B/\log3+1<12\le H/4$。所以每个 $p\in\mathcal G_H$ 的入口都已满足 $t_p\le H/2$，从而 $b_p(H)\ge H/2$，并可在 (16.6) 中去掉截断。这是同时控制所有 $p\le H$ 的量词，不是对每个固定 $p$ 分别取阈值。

跨地方的因子只来自 $n_p$ 及 $\delta_7$ 中的因子 $2$；它们的素数支持在 $H$ 内，指数至多 $2\log H/\log2$。对 $H\ge256$，

$$
\kappa(H)\ge\frac{H-15}{8}\ge\frac{2\log H}{\log2},\qquad
\left\lceil\frac{H-1}{2}\right\rceil
 \ge\frac{2\log H}{\log2},\qquad
\frac H2\ge\frac{2\log H}{\log2}.
\tag{16.36}
$$

这些不等式在 $256$ 处成立，左右差的导数随后为正。因此每个交叉素因子已被相同素数自身的 $b_\ell(H)$ 吸收，包括 $2,7$。另一方面 $p^{b_p(H)}\mid\delta_p(H)$ 本来就是实际阶的自身分量。因此 $\operatorname{lcm}_{p\le H}\delta_p(H)$ 与 $\prod_{p\le H}p^{b_p(H)}$ 相互整除，得 (16.30)。阈值极不锐利，但只依赖原固定数据，完全独立于 $M$。

若 $H\ge H_M$，$M$ 的所有素因子都不超过 $H$；对奇素数，其所需指数由 $b_p(H)\ge H/2$ 或 $b_7(H)\ge(H-1)/2$ 覆盖；对 $2$ 则由 $b_2(H)\ge(H-15)/8$ 覆盖。因此 $M$ 整除自身分量乘积，可以删去最小公倍数中的 $M$。这是固定模数的另一个阈值，不能与结构阈值混同。

**证明（不丢线性项的恒等式）。** 对 $H\ge H_M$，(16.31) 给出

$$
\begin{aligned}
\sum_{p\in\mathcal G_H}b_p(H)\log p
&=(H-1)\sum_{p\in\mathcal G_H}\log p
 -\sum_{p\in\mathcal G_H}(t_p-1)\log p
 +\sum_{p\in\mathcal G_H}v_p(n_p)\log p\\
&=(H-1)(\vartheta(H)-\log2-\log7)-W(H)+\log5.
\end{aligned}
\tag{16.37}
$$

最后一项恰为 $\log5$，因为只有 $n_5$ 含自身素数且 $v_5(n_5)=1$。加上二进、七进自身分量便是 (16.33)。等价地，从二次基线减去实际周期，完整损失为

$$
\begin{aligned}
H\vartheta(H)-\log q(H,H;M)
={}&W(H)+\vartheta(H)+(H-1)(\log2+\log7)\\
&-b_2(H)\log2-b_7(H)\log7-\log5.
\end{aligned}
\tag{16.38}
$$

其中 $\vartheta(H)$ 这一线性主阶项不能省略。对 (16.19) 移项，有 $(t_p-1)\log p\le Ap+B+(v_p(n_p)-1)\log p$；逐个素数相加并用同一个 $\log5$ 恒等式即得 (16.34)，再用素数定理完成其阶估计。

用白话说，原问题要求一把整数钥匙同时打开两个点在全部地方、全部指定深度的锁。Galois 对称使同一有理素数上各把锁的共同条件相同；半点使四个方向落在一个较小的有限群中。四维整数盒比这个群大时，必有一个不长的全局组合落进同一局部单位元邻域。若原点对的共同入口过深，这个组合也被迫过深，而它的全局高度付不起这么大的一个局部贡献。这限制的是两点和复乘方向的同一个实现。

每个好素数自己的地方于是提供约 $H$ 个该素数因子，损失由实际 $t_p$ 精确记录。其它地方夹带的该素数因子只有对数多个，最终被自身分量完全吸收。故所有素数的 $H\log p$ 成本相加，得到二次的 $H\vartheta(H)$；没有将一个较大消去数的增长移植给实际周期。尚未控制得更细的部分正是 $W(H)$：本节只用全局高度支付它的总上界，没有证明入口深度的更强平均规律。

本节的固定数据、半点及 $\mathbb Z[i]$ 模挠独立性引自 [Brox 固定提交 `61b82ccacfbefdff3d6e7cf986d6e6279afa1372` 的原始源码](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex)。所引 Silverman 经典结果按非分歧奇素数、七进 $r>e/(p-1)$、可分核及普通/超奇异条件分别使用；二进原过滤及精确阶只复用 §15。文献重合核对限于该固定源码、Silverman 上述章节及本卷 §§11–15：新增综合是原点对的共同入口界、实际周期上下界闭合和 (16.33) 的精确余项身份，不主张全领域原创优先权。这些结论的对象仅是此处固定数据的实际共同周期，不扩张为完整的 $\mathbb Z/\mathbb Q$ 定义或物理同构。$\square$

## 追加锚（本行以下为增补区）

## 17. 实际共轭 CM 点的多项式频率预算与自身阶段双边计数

**定义 17.1（固定数据、原过滤与完整相容目标）。** 本节固定定义 11.1 的正实根与指定实嵌入，使用同一曲线和点

$$
\begin{gathered}
F=\mathbb Q(\sqrt2,\sqrt{3-\sqrt2},\sqrt{3+\sqrt2}),\qquad
E_0:Y^2=X^3-X,\\
P_1=\left(\frac{115-27\sqrt2}{56},
 \frac{-660+417\sqrt2}{32(3-\sqrt2)^{3/2}}\right),\\
P_2=\left(\frac{115+27\sqrt2}{56},
 \frac{-660-417\sqrt2}{32(3+\sqrt2)^{3/2}}\right).
\end{gathered}
\tag{17.1}
$$

$C=E_0(\mathbb R)^0$、$\omega=dX/(2Y)$、正实周期 $\Omega$、$\theta:C\to\mathbb T=\mathbb R/\mathbb Z$ 及 $\alpha=(\theta(P_1),\theta(P_2))$ 均为定义 12.1 的对象。特别地，$\theta(R)=\Omega^{-1}\int_O^R\omega\pmod{\mathbb Z}$，圆距离记作 $\|\cdot\|_{\mathbb T}$。

有限端始终是 $F$ 的全部有限位。对 $v\mid p$，$\mathfrak m_v$、原极小整模型 $\mathcal E_v$、保单位元同构 $\iota_v$ 和形式参数同构 $\psi_v$ 严格沿用定义 13.1；奇素数处原方程即为该模型。具体的过滤、阶和共同模数为

$$
\begin{aligned}
U_v(r)&=\iota_v^{-1}
 \bigl(\psi_v(\widehat{\mathcal E}_v(\mathfrak m_v^r))\bigr),\\
d_{v,j}(r)&=\operatorname{ord}_{E_0(F_v)/U_v(r)}(P_j+U_v(r)),\\
D_H&=q(H,H;1),\\
q(B,r;M)&=\operatorname{lcm}
 \bigl(M,\{d_{v,j}(r):p\le B,\ v\mid p,\ j=1,2\}\bigr).
\end{aligned}
\tag{17.2}
$$

这里 $r,H,M$ 为正整数且 $H\ge2$。形式深度要求先进入约化至单位元的形式群，再取参数属于 $\mathfrak m_v^r$；不以任意仿射点上的坐标比值替代这一条件。

令 $\widehat{\mathbb Z}=\varprojlim_m\mathbb Z/m\mathbb Z$。对 $u\in\widehat{\mathbb Z}$，原目标 $\eta(u)$ 的坐标由

$$
\{\eta_{v,j}(u)\}
 =\bigcap_{r\ge1}\bigl([b_{v,j,r}]P_j+U_v(r)\bigr),
\qquad b_{v,j,r}\equiv u\pmod{d_{v,j}(r)}
\tag{17.3}
$$

定义，交集的唯一性和代表无关性由定理 14.2 保证。完整有限目标空间为 $\eta(\widehat{\mathbb Z})$，使用普通乘积拓扑。固定 $M\ge1$、$a_0\in\mathbb Z$ 后，本节的全部相容目标指

$$
u\in a_0+M\widehat{\mathbb Z},\qquad z\in\mathbb T^2.
\tag{17.4}
$$

这是同一整数的相容目标族；不允许把不同地方任意独立指定的点自动视为此族中的元素。

**定理 17.2（原实际点的固定 CM 参数桥与增长模数差异度）。** 对 (17.1) 的原点对，存在只依赖这些固定数据的常数 $A>0$、$\mu>0$，使所有整数 $q,J\ge1$ 同时满足

$$
\lambda_q(J):=
\min_{\substack{m\in\mathbb Z^2\\0<\|m\|_\infty\le J}}
 \|q(m_1\alpha_1+m_2\alpha_2)\|_{\mathbb T}
\ge A(qJ)^{-\mu}.
\tag{17.5}
$$

可取 $A\le1/2$。对任意起点 $\xi\in\mathbb T^2$、整数 $N,q,J\ge1$，定义 12.1 的普通半开矩形极端差异度满足

$$
\begin{aligned}
\mathcal D_N(\xi,q)
&\le\frac9{2(J+1)}
 +\frac{9}{8A N}q^\mu J^\mu
 \left[\left(1+2\sum_{j=1}^J\frac1j\right)^2-1\right]\\
&\le\frac9{2(J+1)}+
 \frac9{A N}q^\mu J^{\mu+2}.
\end{aligned}
\tag{17.6}
$$

起点、矩形端点及增长中的 $q$ 均在这些量词之内。这里存在的 $A,\mu$ 未被赋予数值，(17.5)–(17.6) 不宣称数值明确的起点或实际计算效率。

**证明（解析归一化与非零形式）。** 只为调用复解析定理，取一次固定数域

$$
K_{\rm CM}=F(i),\qquad D=[K_{\rm CM}:\mathbb Q]=16.
\tag{17.7}
$$

次数及 $\operatorname{End}_{\overline{\mathbb Q}}(E_0)=\mathbb Z[i]$ 见 §16 及其所引固定源码。写 $W=2Y$，则解析方程为 $W^2=4X^3-4X$，其 Weierstrass 不变量是 $g_2=4,g_3=0$，且 $dX/W=\omega$。经典复一致化给出一个固定周期格 $\Lambda$ 及

$$
z\longmapsto (X,Y)=(\wp(z),\wp'(z)/2).
\tag{17.8}
$$

固定一次定向周期基 $\omega_1,\omega_2$，$\tau=\omega_2/\omega_1$ 的虚部为正。由于复乘域为 $\mathbb Q(i)$，$\tau\in\mathbb Q(i)\subset K_{\rm CM}$。这是经典 CM 一致化的中间输入，参见 Silverman，*The Arithmetic of Elliptic Curves*，第二版，[VI §1 及 VI §4](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)。这里只在复解析坐标中写 $W=2Y$，不对 (17.2) 的有限位模型、地方集合或过滤施加坐标变换。

取 $\alpha_j$ 的唯一代表 $a_j\in(0,1)$，置

$$
\ell_j=\Omega a_j\quad(j=1,2),\qquad \ell_3=\Omega.
\tag{17.9}
$$

$P_j\ne O$，故这些代表存在且非零；(17.8) 的指数映射将 $\ell_j$ 送到 $P_j$，将非零周期 $\Omega\in\Lambda$ 送到 $O$。这使用原 $\omega$ 与 $\theta$ 的周期对应，不把 $\theta(P_j)$ 当作未经缩放的椭圆对数。

给定 $q,J\ge1$ 及 $0<\|m\|_\infty\le J$，取最近整数 $b$，使

$$
\delta=q(m_1a_1+m_2a_2)-b,\qquad
|\delta|=\|q m\cdot\alpha\|_{\mathbb T}\le\tfrac12.
\tag{17.10}
$$

因 $0<a_j<1$，有 $|b|\le2qJ+1/2\le3qJ$。考虑齐次椭圆对数形式

$$
L'(Z_0,Z_1,Z_2,Z_3)=q m_1Z_1+q m_2Z_2-bZ_3,
\qquad u'=(1,\ell_1,\ell_2,\Omega).
\tag{17.11}
$$

于是 $L'(u')=\Omega\delta$。若它为零，(17.8) 的群同态性会给出 $[qm_1]P_1+[qm_2]P_2=O$。Brox，[固定源码](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/61b82ccacfbefdff3d6e7cf986d6e6279afa1372/papers/trace_heights/aggregate_trace_height_20261108_v9.tex) `lem:independent` 对这同一正根归一化点对证明了 $\mathbb Z[i]$ 上模挠独立性；其整数系数特例与 $m\ne0$ 排除该等式。因此 $L'(u')\ne0$，包括最近整数有两个选择时的每一个选择。

**证明（Ably 的全部固定参数与子群分支）。** 所用经典输入为 Ably，*Formes linéaires de logarithmes de points algébriques sur une courbe elliptique de type CM*，[DOI:10.5802/aif.1745，原文 Theorem 2.1，印刷页 3–4](https://www.numdam.org/item/AIF_2000__50_1_1_0.pdf)。对应参数为 $k=3$、数域 (17.7)、非零对数 $(\ell_1,\ell_2,\ell_3)$ 和形式 (17.11)。对前两个对数，$\wp(\ell_j)=X(P_j)\in F$；第三个是原定理明确允许的非零周期。它们的指数点在原文射影坐标中为

$$
\gamma_j=[1:X(P_j):2Y(P_j)]\quad(j=1,2),
\qquad \gamma_3=[0:0:1].
\tag{17.12}
$$

原文的 $h$ 是绝对对数射影 Weil 高度：在含坐标的数域 $L$ 上，

$$
h([x_0:\cdots:x_s])=
\frac1{[L:\mathbb Q]}\sum_w[L_w:\mathbb Q_w]
 \log\max_i|x_i|_w.
\tag{17.13}
$$

绝对值采用乘积公式归一化；复处使用通常模并以局部次数 $2$ 加权。系数族高度是加上坐标 $1$ 后的射影高度；特别地，整数 $t$ 的高度为 $\log\max(1,|t|)$。本证明用 (17.12) 的点高度，不以典范高度、仅横坐标高度或相对数域高度代替它。$h(\gamma_3)=0$，其余两个高度都是固定有限数。

为逐项满足原文 (2.1)–(2.3)，固定

$$
\begin{aligned}
v_j&=e+h(\gamma_j)+|\ell_j|^2/D+1/D,\qquad
 V_j=\exp(v_j)\quad(j=1,2,3),\\
v&=\max_j v_j,\qquad V=\exp(v),\qquad E_{\rm A}=e,\\
B&=3e^e qJ.
\end{aligned}
\tag{17.14}
$$

所有 $V_j,E_{\rm A}$ 均至少为 $e$，且

$$
\begin{gathered}
\log B\ge\max\bigl(e,h(qm_1),h(qm_2),h(-b)\bigr),\\
\log V_j\ge\max\bigl(h(\gamma_j),|\ell_j|^2/D,1/D\bigr),\\
e\le E_{\rm A}\le
 \min_j\frac{e\sqrt{D\log V_j}}{|\ell_j|}.
\end{gathered}
\tag{17.15}
$$

这分别是原文的三个参数条件。$D,k,\omega_1,\omega_2,\ell_j,\gamma_j,V_j,E_{\rm A}$ 均不随 $q,J,m,b$ 改变；只有 $B$ 和线性形式的整数系数变化。

原文下界有代数子群分支，不能省略。其陈述中的两个加法坐标须按该文 §4（印刷页 10）和证明结尾（印刷页 31）的齐次增广理解。具体地，在三个系数 $(qm_1,qm_2,-b)$ 中选绝对值最大的非零系数 $c_*$，令 $c_j$ 为各系数除以 $c_*$，则增广形式和向量为

$$
\widetilde L(Z_{-1},Z_0,Z_1,Z_2,Z_3)
 =-Z_{-1}+Z_0+\sum_{j=1}^3c_j Z_j,
\qquad \widetilde u=(1,1,\ell_1,\ell_2,\Omega).
\tag{17.16}
$$

它们满足 $\widetilde L(\widetilde u)=L'(u')/c_*\ne0$。因而不存在连通代数子群 $G'\le\mathbb G_a^2\times E_0^3$，使 $\widetilde u\in T_{G'}(\mathbb C)\subseteq\ker\widetilde L$：这些包含关系本身即迫使该值为零。等价地，原文印刷页 31 在齐次情形把该分支投到椭圆因子，其切空间既包含 $(\ell_1,\ell_2,\Omega)$ 又包含于 $\ker(qm_1Z_1+qm_2Z_2-bZ_3)$，仍与 (17.11) 的非零性矛盾。这样同时处理了额外加法坐标和周期项，没有把四维 $u'$ 直接放入五维切空间。

于是原文 (2.4) 的下界分支适用。令 $C_{\rm A}>0$ 为该定理仅依赖 $k,\omega_1,\omega_2$ 的常数，置

$$
\kappa=C_{\rm A}D^5\log(De)\,v_1v_2v_3>0.
\tag{17.17}
$$

由于 $\log E_{\rm A}=1$，该下界在本参数下准确地给出

$$
\log|L'(u')|\ge-\kappa\log(BD\log V)
=-\kappa\log(3e^e Dv qJ).
\tag{17.18}
$$

因此可固定

$$
\mu=\kappa,\qquad
A=\min\left(\frac12,\frac{(3e^e Dv)^{-\kappa}}\Omega\right)>0.
\tag{17.19}
$$

除以 $\Omega$ 并对 (17.10) 的全部非零频率取最小值得 (17.5)。这里没有把随 $q$ 增长的点 $[q]P_j$ 当成新的对数输入，也没有把 $\Omega$ 的整数倍藏入一个随频率改变的代数常数项。

**证明（普通矩形与来源范围）。** 复用 (12.11) 的二维 Erdős–Turán–Koksma 不等式及 (12.12) 的几何级数界。非零频率的平均绝对值至多 $1/(2N\lambda_q(J))$，起点只乘以模为 $1$ 的因子；权重和为 $S_J=(1+2\sum_{j\le J}1/j)^2-1\le8J^2$。代入 (17.5) 正好得到 (17.6)，无需重新证明经典 ETK 定理。其矩形版本和系数仍取 Dick–Pillichshammer，[所引预印本](https://web.maths.unsw.edu.au/~josefdick/preprints/DP_book_preprint.pdf) 定义 3.13 与定理 3.26。

文献对应限于 Ably 上述主定理、§4、证明结尾及其所列 Philippon–Waldschmidt 前驱结果，Brox 固定点独立性，以及本卷 §§11–16 的目标与周期结果。Ably 的 CM 对数下界和 ETK 都是文献中间输入；这里的综合是 (17.1) 的原点对、原周期、增长共同模数及后述自身阶段计数的参数对应，不将一般经典定理另称为新增数学。常数 $C_{\rm A}$ 未在这里数值化，故 (17.19) 也不提供数值算法复杂度、最优指数或文献原创优先权的结论。$\square$

**定义 17.3（独立指定的深度、实窗和同整数计数）。** 取全域非递减函数 $h:\mathbb Z_{\ge1}\to\mathbb Z_{\ge2}$，满足 $h(n)\to\infty$，以及全域正的非递增函数 $r:\mathbb Z_{\ge1}\to\mathbb R_{>0}$，满足 $r(n)\to0$。对 (17.4) 的目标定义

$$
\begin{split}
\mathcal S_{h,r}(u,z;a_0,M)=\{n\ge1:\ &n\equiv a_0\pmod M,\\
&\|\theta([n]P_j)-z_j\|_{\mathbb T}<r(n)\quad(j=1,2),\\
&[n]P_j-\eta_{v,j}(u)\in U_v(h(n))\\
&\hspace{20mm}(p\le h(n),\ v\mid p,\ j=1,2)\}.
\end{split}
\tag{17.20}
$$

$n$ 在此始终为正整数。对正整数 $X$，置

$$
\begin{aligned}
C_{h,r}(X;u,z)&=\#\bigl(\mathcal S_{h,r}(u,z;a_0,M)\cap(X,2X]\bigr),\\
T_{h,r}(X;u,z)&=\#\bigl(\mathcal S_{h,r}(u,z;a_0,M)\cap[1,X]\bigr),\\
H_-&=h(X),\qquad H_+=h(2X),\\
q_-&=q(H_-,H_-;M),\qquad q_+=q(H_+,H_+;M),\\
R_-&=r(X),\qquad R_+=r(2X).
\end{aligned}
\tag{17.21}
$$

目标在计数期间固定，阶段使用整数自身的 $h(n),r(n)$。以下所有阈值均允许依赖固定的 $M,h,r$ 及原算术数据，不能依赖 $u,z$。

**定理 17.4（支付同整数误差的单一有限预算）。** 固定定理 17.2 的 $A,\mu$，并定义

$$
p_\mu=2\mu+6,\qquad
K_\mu=4+144A^{-1}37^{\mu+2}.
\tag{17.22}
$$

在定义 17.3 下，若整数 $X\ge1$ 满足

$$
r(X)\le\frac14,\qquad
X\ge K_\mu q_+^{\mu+1}R_+^{-p_\mu},
\tag{17.23}
$$

则对全部 (17.4) 的相容目标一致地有

$$
\frac{X R_+^2}{4q_+}
\le C_{h,r}(X;u,z)
\le\frac{8X R_-^2}{q_-}.
\tag{17.24}
$$

这是一条有限充分预算，不是命中的必要条件。它允许 $[X,2X]$ 内跨过任意多个 $h$ 的跳点，不要求相邻实际周期之比有界。

**证明（固定阶段的准确进程长度）。** 对任一固定 $H\ge2$，$D_H$ 为 (17.2) 的实际共同阶。由 (17.3) 在每个有限商中的像以及定理 14.2 的 CRT 等价，所有 $p\le H,v\mid p,j$ 的深度 $H$ 条件正好等价于 $n\equiv u\pmod{D_H}$。再加模 $M$ 的条件，因 $u\equiv a_0\pmod M$，全部解为

$$
n\equiv b_H\pmod{q(H,H;M)},\qquad
b_H\equiv u\pmod{q(H,H;M)},\quad 0\le b_H<q(H,H;M).
\tag{17.25}
$$

令 $q=q(H,H;M)$、$b=b_H$。在 $(X,2X]$ 内，全部解精确地写成

$$
\begin{aligned}
k_0&=\left\lfloor\frac{X-b}{q}\right\rfloor+1,\\
N&=\left\lfloor\frac{2X-b}{q}\right\rfloor
 -\left\lfloor\frac{X-b}{q}\right\rfloor,\\
n_k&=b+q(k_0+k),\qquad 0\le k<N.
\end{aligned}
\tag{17.26}
$$

因此 $|N-X/q|<1$，起点 $n_0\alpha$ 可任意变化；它不改变 (17.6)。公式处理了严格左端和包含右端，不以 $\lfloor X/q\rfloor$ 代替真实长度。

**证明（面积误差与充分成本）。** 对任意 $0<R\le1/4$，圆靶

$$
\mathcal B(z,R)=\{w\in\mathbb T^2:
 \|w_j-z_j\|_{\mathbb T}<R\ (j=1,2)\}
\tag{17.27}
$$

的面积为 $4R^2$。将两个开圆弧沿 $0$ 切开，得到至多四个互不相交的普通矩形，端点可开可闭。普通半开矩形的差异度界也适用于这些端点约定：在固定有限样本上，用内侧与外侧半开矩形逼近，令端点移量趋于零，面积趋于同一值，分别控制计数的下界和上界。跨切口时把 $0$ 分配给恰好一个区间。因此

$$
\left|\frac1N\#\{0\le k<N:n_k\alpha\in\mathcal B(z,R)\}-4R^2\right|
\le4\mathcal D_N(n_0\alpha,q).
\tag{17.28}
$$

这一步保留严格圆距离条件，不以边界零测为理由忽略有限样本的边界点。

令

$$
J_R=\lceil36R^{-2}\rceil,\qquad
B(q,R)=\max\left(2,
 \left\lceil72A^{-1}q^\mu J_R^{\mu+2}R^{-2}\right\rceil\right).
\tag{17.29}
$$

若 $X\ge2qB(q,R)$，则 $N\ge B(q,R)$，并且 $X/(2q)\le N\le3X/(2q)$。(17.6) 的两项分别至多 $R^2/8$，所以 $\mathcal D_N\le R^2/4$；(17.28) 的计数介于 $3NR^2$ 和 $5NR^2$ 之间。特别地，它介于 $XR^2/q$ 和 $8XR^2/q$ 之间。

对 $R\le1/4$ 有 $J_R\le37R^{-2}$，且由 (17.29)

$$
\begin{aligned}
2qB(q,R)
&\le4q+144A^{-1}q^{\mu+1}J_R^{\mu+2}R^{-2}\\
&\le K_\mu q^{\mu+1}R^{-(2\mu+6)}.
\end{aligned}
\tag{17.30}
$$

所以 (17.23) 支付了右端较强阶段 $(H_+,R_+)$ 的全部进程长度与面积误差。又因 $q_-\mid q_+$、$R_-\ge R_+$，同一预算也支付左端较弱阶段 $(H_-,R_-)$ 的误差，不另要求周期比值的控制。

**证明（回接自身阶段的两次包含）。** 若一个整数在 $(X,2X]$ 内满足较强阶段 (17.25) 及 $n\alpha\in\mathcal B(z,R_+)$，则 $h(n)\le H_+$，而 $r(n)\ge R_+$。原子群的嵌套性使这些条件蕴涵 (17.20) 的全部条件。固定阶段的下界于是给出甚至更强的 $C_{h,r}\ge XR_+^2/q_+$，故得到 (17.24) 所列下界。

反之，每个 (17.20) 的成功整数满足 $h(n)\ge H_-$、$r(n)\le R_-$，因此属于较弱阶段 (17.25) 和 $\mathcal B(z,R_-)$。由已支付的较弱阶段上界，$C_{h,r}\le8XR_-^2/q_-$。这两个包含各使用同一个 $n$ 的两个点、全部所列有限位及实端条件；没有将分别可达的整数拼成一个整数。所有估计与 $b_H,z$ 无关，故量词一致于全部目标。$\square$

**定理 17.5（平方根对数深度、多项式实缩靶与准确幂指数）。** 独立于定义 13.1 的旧参数范围，取

$$
c>0,\qquad \beta,\gamma\ge0,\qquad \beta+\gamma>0,
\tag{17.31}
$$

并在全部正整数上定义

$$
\begin{aligned}
h_c(n)&=\max\left(2,\left\lfloor c\sqrt{\log(n+2)}\right\rfloor\right),\\
\rho(n)&=(n+2)^{-\beta}(\log(n+2))^{-\gamma},\\
R(n)&=\min\bigl(1/4,\rho(n)\bigr).
\end{aligned}
\tag{17.32}
$$

$h_c$ 全域非递减且趋于无穷，$\rho$ 全域正、非递增且趋于零。成功集合使用定义 17.3 中 $h=h_c,r=\rho$，不把实半径改成旧卷的某个参数范围。若

$$
(\mu+1)c^2+(2\mu+6)\beta<1,
\tag{17.33}
$$

则存在只依赖固定原数据及 $M,c,\beta,\gamma$ 的整数 $X_0$，使对每个整数 $X\ge X_0$ 和每个 (17.4) 的目标，

$$
\frac{X R(2X)^2}{4q(h_c(2X),h_c(2X);M)}
\le C_{h_c,\rho}(X;u,z)
\le\frac{8X\rho(X)^2}{q(h_c(X),h_c(X);M)}.
\tag{17.34}
$$

特别地，令 $s=1-c^2-2\beta>0$，则双边计数给出目标一致的极限

$$
\begin{aligned}
\lim_{X\to\infty}
\sup_{\substack{u\in a_0+M\widehat{\mathbb Z}\\z\in\mathbb T^2}}
\left|\frac{\log C_{h_c,\rho}(X;u,z)}{\log X}-s\right|&=0,\\
\lim_{X\to\infty}
\sup_{\substack{u\in a_0+M\widehat{\mathbb Z}\\z\in\mathbb T^2}}
\left|\frac{\log T_{h_c,\rho}(X;u,z)}{\log X}-s\right|&=0.
\end{aligned}
\tag{17.35}
$$

对足够大的 $X$，对数中的计数均为正。不同目标可以由不同整数命中；本定理不主张一个整数同时命中所有 $z$。

**证明（区域核算）。** 定理 16.7 是这里复用的实际周期输入：对每个固定 $M$，$\log q(H,H;M)\sim H^2$。对 $H_-=h_c(X)$ 和 $H_+=h_c(2X)$ 分别使用它，得

$$
\frac{\log q_-}{\log X}\longrightarrow c^2,
\qquad
\frac{\log q_+}{\log X}\longrightarrow c^2.
\tag{17.36}
$$

这是对两端各自的主阶应用，没有估计 $q_+/q_-$ 或相邻阶段周期比。又有

$$
\frac{-\log\rho(X)}{\log X}\longrightarrow\beta,
\qquad
\frac{-\log\rho(2X)}{\log X}\longrightarrow\beta.
\tag{17.37}
$$

所以有限预算右端的指数准确地是

$$
\frac{\log\bigl(K_\mu q_+^{\mu+1}\rho(2X)^{-(2\mu+6)}\bigr)}{\log X}
\longrightarrow(\mu+1)c^2+(2\mu+6)\beta<1.
\tag{17.38}
$$

$\gamma$ 的贡献是 $O(\log\log X)$，在此严格不等式内不增加幂指数。取严格余量后，(17.38) 保证所有足够大整数 $X$ 满足 (17.23)，并同时有 $\rho(X)\le1/4$。这给出共同的 $X_0$；它不含 $u,z,a_0$。定理 17.4 即给出 (17.34)，此时 $R(2X)=\rho(2X)$。$2\mu+6$ 来自 (17.30) 的 $J_R^{\mu+2}R^{-2}$，没有采用未经此预算支付的较小系数。

**证明（下界与上界共同决定指数）。** (17.33) 与 $\mu>0$ 蕴涵 $c^2+2\beta<1$。把 (17.36)–(17.37) 代入 (17.34) 的两端，两端对数除以 $\log X$ 都趋于 $1-c^2-2\beta=s$。其中分母 $q_-$ 的上计数界不可省略；它与 $q_+$ 的下计数界共同夹住实际的 $C_{h_c,\rho}$。两端都独立于目标，因此同时证明第一条一致极限及最终正性。

对累计计数，固定任意 $0<\varepsilon<s$。第一条一致极限给出共同阈值后，每个整数 $Y$ 的块计数介于 $Y^{s-\varepsilon}$ 和 $Y^{s+\varepsilon}$。下界用 $Y=\lfloor X/2\rfloor$ 的整个块，它包含于 $[1,X]$。上界把 $[1,X]$ 包在有限初始段与 $(2^j,2^{j+1}]$ 的并中；其块上界是公比 $2^{s+\varepsilon}>1$ 的几何和，总和为 $O(X^{s+\varepsilon})$，初始段长度也与目标无关。令 $\varepsilon\downarrow0$，得第二条一致极限。

用白话说，有限位的全部锁先把整数筛成一个真实进程，代价由实际共同模数承担；两个实方向再要求这条进程进入面积约为实半径平方的窗口。右端最深、最窄的条件提供一批必然成功的整数，左端最浅、最宽的条件限制全部可能成功的整数。两端的模数未必接近，但它们的对数都有同一主阶，所以足以夹出准确的幂指数。充分区域 (17.33) 说明本面积误差能被支付，不表示区域外没有命中，也不表示该区域或常数最优。

这些是固定算术轨道的同时逼近与计数结论。任一成功整数列趋于无穷时，对每个固定 $v,r$ 最终满足原 $U_v(r)$ 目标，实端同时趋于 $z$，故得到 $\mathbb T^2$ 与 $\eta(a_0+M\widehat{\mathbb Z})$ 中相应目标的联合逼近；这只涉及普通乘积拓扑。它不构成完整的 $\mathbb Z/\mathbb Q$ 丢番图定义，不提供量子物理起源或经验物理同一性的认证。$\square$

**推论 17.6（同一预算的次平方根对数深度与对数实窗）。** 保持 (17.1)–(17.4) 的全部原数据。取任意全域非递减、趋于无穷的整数深度 $g(n)\ge2$，满足

$$
g(n)=o(\sqrt{\log(n+2)}),
\qquad r_\delta(n)=(\log(n+2))^{-\delta},\quad\delta>0.
\tag{17.39}
$$

成功集合在 (17.20) 中独立取 $h=g,r=r_\delta$。则存在共同阈值，使每个足够大的整数 $X$ 及全部 (17.4) 的目标满足

$$
\frac{Xr_\delta(2X)^2}{4q(g(2X),g(2X);M)}
\le C_{g,r_\delta}(X;u,z)
\le\frac{8Xr_\delta(X)^2}{q(g(X),g(X);M)}.
\tag{17.40}
$$

两种计数的目标一致幂指数均为 $1$。特别地，对任意固定 $d_*>0$，全域深度

$$
g_{d_*}(n)=\max\left(2,
 \left\lfloor d_*\sqrt{\log\log(n+e^e)}\right\rfloor\right)
\tag{17.41}
$$

满足本条条件，且目标一致地有更细的对数阶

$$
C_{g_{d_*},r_\delta}(X;u,z)
 =X(\log X)^{-(d_*^2+2\delta)+o(1)}.
\tag{17.42}
$$

这里 $o(1)$ 一致于全部相容目标。对于一般 $g$，对每个 $\varepsilon>0$，最终一致地有

$$
C_{g,r_\delta}(X;u,z)
\ge\frac{X}{(\log X)^{2\delta+\varepsilon}}
\tag{17.43}
$$

的一项充分附加条件是

$$
g(n)^2=o(\log\log(n+2)).
\tag{17.44}
$$

例如 $g(n)=\max(2,\lfloor(\log\log(n+16))^{1/3}\rfloor)$ 满足 (17.44)，而 $g(n)=\max(2,\lfloor(\log(n+2))^a\rfloor)$、$0<a<1/2$ 满足 (17.39)，不据此自动取得 (17.43)。

**证明。** 定理 16.7 给出 $\log q(g(2X),g(2X);M)=o(\log X)$，且 $-\log r_\delta(2X)=O(\log\log X)$。因此同一个 (17.23) 的预算右端为 $X^{o(1)}$，最终小于 $X$；较弱阶段也由它支付。定理 17.4 得 (17.40)，两端的对数除以 $\log X$ 均趋于 $1$。累计计数照定理 17.5 的几何和论证，仍为目标一致的指数 $1$。

对 (17.41)，$g_{d_*}(X)^2\sim d_*^2\log\log X$，$g_{d_*}(2X)^2\sim d_*^2\log\log X$。分别应用实际周期主阶，两个模数的对数除以 $\log\log X$ 均趋于 $d_*^2$；再由 (17.40) 的两边得 (17.42)。该论证也说明一个固定深度系数的对数损失由实际周期支付，不需要相邻周期比有界。

若另有 (17.44)，则 $q(g(2X),g(2X);M)=(\log X)^{o(1)}$，且 $r_\delta(2X)^2=(\log X)^{-2\delta}(1+o(1))$。将其代入 (17.40)，固定的因子 $4$ 可由任意 $\varepsilon$ 的严格余量吸收，得到 (17.43)。所列第一个深度的平方为 $O((\log\log n)^{2/3})$；第二个例子的平方则为 $O((\log n)^{2a})=o(\log n)$。这分别证明两个例子的适用范围。

因而本卷原对数实窗和满足 (17.44) 的高密度情形，是同一有限预算的较弱推论；$\delta$ 在这里可以是任意正数，不沿用旧的 $0<\gamma<1/4$ 限制。一般的次平方根对数深度只保证 $X^{1-o(1)}$ 型计数，不能把它说成具有任意指定对数损失的高密度界。本推导不需要另一个 David 参数桥，也不改动旧高度法已有结论；未满足 (17.39) 的自适应深度或其它缩靶安排不由本条处理。$\square$

## 追加锚（本行以下为增补区）
## 18. 实际自身阶段的移动质量与目标一致相对渐近

**定义 18.1（平方根对数阶段与移动质量）。** 保持定义 17.1 的 $F,E_0,P_1,P_2$、正实嵌入、圆坐标 $\theta$、$\alpha$、全部有限地方的 $U_v$、原过滤及相容目标 (17.4)。固定 $M\ge1$、$a_0\in\mathbb Z$，并取

$$
\begin{aligned}
h(n)&=\max\left(2,\left\lfloor c_0\sqrt{\log(n+2)}\right\rfloor\right),\\
\rho(n)&=(n+2)^{-\beta}(\log(n+2))^{-\gamma},
\end{aligned}
\tag{18.1}
$$

其中 $c_0>0$、$\beta,\gamma\ge0$ 且 $\beta+\gamma>0$。对 $u\in a_0+M\widehat{\mathbb Z}$、$z=(z_1,z_2)\in\mathbb T^2$，令

$$
\begin{aligned}
S_X(u,z)=\#\{n\in\mathbb Z:\;&X<n\le2X,\ n\equiv a_0\pmod M,\\
&\|\theta([n]P_j)-z_j\|_{\mathbb T}<\rho(n)\quad(j=1,2),\\
&[n]P_j-\eta_{v,j}(u)\in U_v(h(n))\\
&\hspace{20mm}(p\le h(n),\ v\mid p,\ j=1,2)\},\\
L_X&=4\sum_{X<n\le2X}
 \frac{\rho(n)^2}{q(h(n),h(n);M)}.
\end{aligned}
\tag{18.2}
$$

这里 $X$ 为正整数，$S_X$ 是每个整数使用自身 $h(n)$ 和自身半径的实际命中数，$L_X$ 使用同一实际模数的移动质量；右端不把任意阶段的模数替换成一个共同的上界。

**定理 18.2（严格充分区域内的移动质量渐近）。** 令 $A,\mu$ 为定理 17.2 中的固定常数，并置

$$
\Delta=1-(\mu+1)c_0^2-(2\mu+2)\beta.
\tag{18.3}
$$

若 $\Delta>0$，则

$$
\lim_{X\to\infty}
\sup_{\substack{u\in a_0+M\widehat{\mathbb Z}\\z\in\mathbb T^2}}
\left|\frac{S_X(u,z)}{L_X}-1\right|=0.
\tag{18.4}
$$

条件 (18.3) 是充分条件；本条不主张其必要性、端点有效性、任何数值效率或常数最优性。

**证明（每个阶段的准确剩余类与固定半径估计）。** 记

$$
q_H=q(H,H;M).
\tag{18.5}
$$

若 $H$ 是 $h(n)$ 在某个整数区间上的值，则 (17.25) 的有限商等价和定义 14.2 的 CRT 给出唯一的剩余类 $b_H\pmod {q_H}$，使该区间内的全部有限地方条件及 $M$-同余恰好等价于 $n\equiv b_H\pmod {q_H}$。这里 $b_H$ 依赖 $u$，但 $q_H$ 不依赖 $u,z$。对任意整数端点 $A_0<B_0$，该区间中的允许项准确地是

$$
N_H(A_0,B_0)=
\left\lfloor\frac{B_0-b_H}{q_H}\right\rfloor-
\left\lfloor\frac{A_0-b_H}{q_H}\right\rfloor,
\qquad
\left|N_H(A_0,B_0)-\frac{B_0-A_0}{q_H}\right|<1.
\tag{18.6}
$$

这保留严格左端、包含右端、任意空剩余类块及真实的 floor 长度。

Dick–Pillichshammer，*Digital Nets and Sequences: Discrepancy Theory and Quasi-Monte Carlo Integration*，定义 3.13（印刷页 72）和定理 3.26（印刷页 84）仍提供 (12.11) 的二维 Erdős–Turán–Koksma 频率权重接口：

$$
r(m)=\max(1,|m_1|)\max(1,|m_2|),
\tag{18.7}
$$

小盒的局部零频误差另由 Faifman–Rudnick，*Statistics of the zeros of zeta functions in families of hyperelliptic curves over a finite field*，Compositio Mathematica **146** (2010)，81–101，[作者公开原文](https://www.math.tau.ac.il/~rudnick/papers/compositio%20offprint.pdf)，[DOI 10.1112/S0010437X09004308](https://doi.org/10.1112/S0010437X09004308)，§4 印刷页 90 的 (4.1)–(4.4) 提供。该处对任意长度 $0<|I|<1$ 及整数 $J\ge1$ 给出实三角多项式的逐点夹逼、准确均值及 Fourier 系数误差；这里不使用随后要求 $J|I|>1$ 的 Proposition 4.1。

对 $0<r\le1/4$ 和整数 $J\ge2$，记 $I_j=\{x\in\mathbb T:\|x-z_j\|_{\mathbb T}<r\}$、$\delta_J=(J+1)^{-1}$、$e(t)=\exp(2\pi it)$，并以 $\widehat f(m)=\int_{\mathbb T}f(x)e(-mx)\,dx$ 归一化 Fourier 系数。将上述长度 $2r$、中心为 $0$ 的多项式平移到 $z_j$，记为 $p_j^\pm=p_{j,r,z_j}^\pm$；平移不改变均值及系数模。它们的次数不超过 $J$，且

$$
\widehat p_j^\pm(0)=2r\pm\delta_J,\qquad
\left|\widehat p_j^\pm(m)-\widehat{\mathbf 1_{I_j}}(m)\right|\le\delta_J
\quad(0<|m|\le J).
$$

原文的闭区间外 $p_j^-\le0$，区间内 $p_j^+\ge1$；连续性使边界也分别满足 $p_j^-\le0$、$p_j^+\ge1$，故同一对多项式对严格开区间仍有 $p_j^-\le\mathbf 1_{I_j}\le p_j^+$ 且 $p_j^+\ge0$。开、闭端点不影响积分；对 $m\ne0$，

$$
\widehat{\mathbf 1_{I_j}}(m)
=e(-mz_j)\frac{\sin(2\pi mr)}{\pi m},\qquad
|\widehat p_j^\pm(m)|
\le\min\left(2r,\frac1{\pi|m|}\right)+\delta_J
\quad(0<|m|\le J).
$$

用它们的乘积和一次 inclusion–exclusion 组合

$$
P_{r,z}^{+}=p_{1}^{+}p_{2}^{+},\qquad
P_{r,z}^{-}=p_{1}^{-}p_{2}^{+}+p_{1}^{+}p_{2}^{-}-p_{1}^{+}p_{2}^{+}
$$

得到每坐标次数不超过 $J$ 的二维上下式，即 Fourier 支撑满足 $\|m\|_\infty\le J$，不要求总次数不超过 $J$。四种点是否属于两个区间的逐项检查给出

$$
P_{r,z}^{-}(x)\le
\mathbf 1_{\{\|x_j-z_j\|_{\mathbb T}<r,\ j=1,2\}}(x)
\le P_{r,z}^{+}(x).
\tag{18.8}
$$

两坐标的积分相乘，给出准确零频

$$
\widehat P_{r,z}^+(0)=4r^2+4r\delta_J+\delta_J^2,\qquad
\widehat P_{r,z}^-(0)=4r^2-4r\delta_J-3\delta_J^2.
$$

由 $\delta_J\le J^{-1}$ 即得下式第一界。存在绝对常数 $C_0$，对两种符号同时有

$$
\left|\widehat P_{r,z}^{\pm}(0)-4r^2\right|
\le C_0\left(\frac rJ+\frac1{J^2}\right),
\qquad
\sum_{0<\|m\|_\infty\le J}
\left|\widehat P_{r,z}^{\pm}(m)\right|
\le C_0(1+\log J)^2.
\tag{18.9}
$$

对第二界，一维零频的绝对值不超过 $2r+\delta_J$，非零系数由上述 $\min(2r,(\pi|m|)^{-1})+\delta_J$ 控制。对 $m_1,m_2$ 取乘积，且 $P_{r,z}^-$ 只有三个乘积项，故 (18.9) 的和由

$$
\left(\,r+\sum_{j=1}^{J}\frac1j+\frac{J}{J}\right)^2
\le C(1+\log J)^2
\tag{18.10}
$$

得到。这里的实际系数界保留 (18.7) 的调和频率权重，而不是把频率数目 $O(J^2)$ 当作系数和。

固定 $H,r$，把区间内的 $N=N_H(A_0,B_0)$ 个允许项写成 $n_k=b_H+q_H(k_0+k)$。对每个非零 $m$，几何和及定理 17.2 的 (17.5) 给出

$$
\left|\sum_{k=0}^{N-1}e^{2\pi i m\cdot(n_k\alpha)}\right|
\le\min\left(N,\frac1{2\|q_Hm\cdot\alpha\|_{\mathbb T}}\right)
\le\frac1{2A}q_H^{\mu}J^{\mu}
\quad(0<\|m\|_\infty\le J).
\tag{18.11}
$$

起点只贡献模为 $1$ 的因子。将 (18.9) 插入 (18.8)，并同时使用 (18.11)，得到对任意起点、中心 $z$ 和任意 $N$（包括 $N=0$）的一致估计

$$
\left|
\#\{0\le k<N:n_k\alpha\in\mathcal B(z,r)\}-4r^2N
\right|
\le C_1\left[
N\left(\frac rJ+\frac1{J^2}\right)
+A^{-1}q_H^{\mu}J^{\mu}(1+\log J)^2
\right],
\tag{18.12}
$$

其中 $\mathcal B(z,r)$ 是两个圆距离都小于 $r$ 的开盒。式 (18.12) 是本节唯一使用的局部估计；它来自上述区间多项式的 (18.8)–(18.10)、(17.5) 的实际频率分离和几何和，不使用相邻 $q_H$ 的比值。

**证明（阶段跳点、变半径和所有短块）。** 取 $X$ 足够大，令 $K=\lceil\log X\rceil\le X$，按整数切点定义

$$
\begin{aligned}
t_k&=\left\lfloor X+\frac{kX}{K}\right\rfloor
\quad(0\le k\le K),\\
I_k&=(t_k,t_{k+1}]\cap\mathbb Z
\quad(0\le k<K).
\end{aligned}
\tag{18.13}
$$

这里 $t_0=X$、$t_K=2X$，各 $I_k$ 不交且并集为 $(X,2X]\cap\mathbb Z$。将每个 $I_k$ 与阶段集合 $\{n\in\mathbb Z:h(n)=H\}$ 相交，丢弃空的整数交集，把所有非空交集编号为 $I_\nu$。由 $h$ 的单调性，每个 $I_\nu$ 仍为连续整数块；明确定义

$$
A_\nu=\min I_\nu-1,\qquad B_\nu=\max I_\nu.
$$

于是 $A_\nu,B_\nu\in\mathbb Z$，$I_\nu=(A_\nu,B_\nu]\cap\mathbb Z$，且对包含该块的 $I_k$ 有

$$
\#I_\nu=B_\nu-A_\nu
\le t_{k+1}-t_k\le\frac XK+1.
$$

由于

$$
\sqrt{\log(2X+2)}-\sqrt{\log(X+2)}\longrightarrow0,
\tag{18.14}
$$

足够大时 $(X,2X]$ 至多遇到一个 $h$ 的跳点，所以所得非空整数块的数目 $m_X$ 满足 $m_X\le2K+2$。跳点可以落在任意一个小区间内；所有非空整数块，包括短阶段块及其中允许剩余类计数 $N_\nu=0$ 的块，都保留在下面的求和中。

在 $(X,2X]$ 上，$\rho$ 的对数导数满足

$$
\left|\frac{d}{dx}\log\rho(x)\right|
\le\frac{\beta+\gamma/\log(X+2)}{X+2}.
\tag{18.15}
$$

每个 $n\in I_\nu$ 满足 $A_\nu+1\le n\le B_\nu$，而 $\rho$ 单调递减，故同一 $I_\nu$ 内的最大、最小半径准确地是

$$
r_\nu^+=\rho(A_\nu+1),\qquad r_\nu^-=\rho(B_\nu)
\tag{18.16}
$$

由 (18.15) 和 $B_\nu-A_\nu\le X/K+1$，它们满足 $r_\nu^+/r_\nu^-=1+O(K^{-1}+X^{-1})=1+O(K^{-1})$，常数只依赖 $\beta,\gamma$。取 $X$ 足够大使 $r_\nu^+\le1/4$。嵌套性给出

$$
\mathcal B(z,r_\nu^-)
\subseteq\mathcal B(z,\rho(n))
\subseteq\mathcal B(z,r_\nu^+)
\quad(n\in I_\nu).
\tag{18.17}
$$

令 $H_\nu$ 为该区间的阶段，$q_\nu=q_{H_\nu}$，$N_\nu=N_{H_\nu}(A_\nu,B_\nu)$，并令 $S_\nu$ 表示 $S_X(u,z)$ 在 $I_\nu$ 内的贡献；再置

$$
L_\nu=4\sum_{n\in I_\nu}\frac{\rho(n)^2}{q_\nu}.
\tag{18.18}
$$

将 (18.12) 对 $r_\nu^-$ 和 $r_\nu^+$ 各用一次，再用 (18.17) 夹住真实的变半径命中数。结合 $\#I_\nu=B_\nu-A_\nu$、(18.6) 及 (18.16)，得到

$$
\begin{aligned}
|S_\nu-L_\nu|\le C_2\bigg(&K^{-1}L_\nu+(r_\nu^+)^2
 +N_\nu\left(\frac{r_\nu^+}{J}+\frac1{J^2}\right)\\
&+A^{-1}q_+^{\mu}J^{\mu}(1+\log J)^2\bigg),
\end{aligned}
\tag{18.19}
$$

其中 $q_+=q(h(2X),h(2X);M)$。第一项支付同一小区间内的真实半径变化；第二项来自 (18.6) 的 $|N_\nu-(B_\nu-A_\nu)/q_\nu|<1$，乘以任一端点面积后不超过 $4(r_\nu^+)^2$；最后一项对短块也成立，因为 (18.11) 使用的是 $\min(N,\cdots)$，没有把长块的相对差异度假定为短块的相对估计。若 $N_\nu=0$，则 $S_\nu=0$ 且 $(B_\nu-A_\nu)/q_\nu<1$，从而 $L_\nu\le4(r_\nu^+)^2$，仍由同一 floor 余项控制。

记 $\underline r=\rho(2X)$、$\overline r=\rho(X+1)$，并取

$$
J=\left\lceil\underline r^{-2}\right\rceil.
\tag{18.20}
$$

这些端点半径之比由 (18.15) 有界。所有 $I_\nu$ 构成 $(X,2X]\cap\mathbb Z$ 的不交分割，故 $\sum_\nu(B_\nu-A_\nu)=X$。又 $q_\nu\mid q_+$，所以

$$
L_X=\sum_\nu L_\nu
\ge\frac{4X\underline r^2}{q_+},
\qquad
N_\nu\le\frac{B_\nu-A_\nu}{q_\nu}+1.
\tag{18.21}
$$

把 (18.19) 对所有 $\nu$ 相加。由 $J\ge\underline r^{-2}$、(18.21)、$m_X\le2K+2$ 及端点半径比的有界性，得到

$$
\frac{|S_X-L_X|}{L_X}
\le C_3\left[
\frac1K+\underline r+\frac{Kq_+}{X}
+\frac{Kq_+^{\mu+1}\underline r^{-(2\mu+2)}
 (1+\log(1/\underline r))^2}{X}
\right].
\tag{18.22}
$$

这里没有丢掉任一阶段的初项：所有 $+1$ 都由 (18.6) 保留，并在 (18.21) 后形成 $Kq_+/X$ 及同阶的更小项；所有短、空剩余类块都在 (18.19) 中以绝对误差计入。特别是 (18.22) 不需要 $q_+/q_-$ 或任何相邻阶段模数比有界。

**证明（严格区域与统一量词）。** 定理 16.7 对固定 $M$ 给出

$$
\frac{\log q_+}{\log X}\longrightarrow c_0^2,
\qquad
-\frac{\log\underline r}{\log X}\longrightarrow\beta.
\tag{18.23}
$$

其中 $h(2X)=c_0\sqrt{\log X}+o(\sqrt{\log X})$；对数因子 $\gamma$ 只贡献 $O(\log\log X)$。因此 (18.3) 蕴涵

$$
\frac1{\log X}\log\left(
\frac{q_+^{\mu+1}\underline r^{-(2\mu+2)}}{X}
\right)
\longrightarrow-\Delta<0.
\tag{18.24}
$$

乘以 $K=\lceil\log X\rceil$ 和 (18.22) 中的调和对数因子不改变这个严格负的幂指数。又由 $\Delta>0$ 得 $c_0^2+2\beta<1$，所以 $q_+/X\to0$、$\underline r\to0$，且 (18.22) 的右端趋于零。估计中的常数只依赖固定的 $M,a_0,c_0,\beta,\gamma,A,\mu$ 及原算术数据，不依赖 $u,z$；故得到 (18.4)。同时 (18.21) 表明 $L_X\to\infty$，其幂指数至少为 $1-c_0^2-2\beta>0$。

用白话说，把二倍区间按阶段跳点和 $\log X$ 个短小片段切开，每片只用一个真实模数和两个相邻的真实半径。经典 ETK 的调和频率权重把一片的非零频率误差压到 $q_H^\mu J^\mu$ 乘对数平方；选 $J$ 为最小半径的平方倒数后，全部片段的总误差正是 (18.24) 所支付的量。一个阶段即使只剩很短的一截，仍按绝对误差处理；真正的 floor 初项也单独留下并由 $Kq_+/X$ 吸收。因此计数的主项是每个整数自身的 $4\rho(n)^2/q(h(n),h(n);M)$ 之和，而不是用最深阶段模数或端点半径偷换出来的粗界。

本条只是在固定的实际共轭点、原有限地方过滤、原共同整数及全部相容目标上作条件性综合；$A,\mu$ 沿用定理 17.2，未求数值。它不声称完整的 $\mathbb Z/\mathbb Q$ 定义、量子物理起源、实际算法效率或必要边界，也不把条件区域外的行为判作失败。$\square$

## 追加锚（本行以下为增补区）

## 19. 三维等体积胞给出的实际移动质量区域与误差率

**定义 19.1（原移动质量的几何预算）。** 保持定义 18.1 的全部实际对象与参数：固定的 $F,E_0,P_1,P_2$、正实嵌入、$\theta,\alpha$、全部有限地方的原过滤 $U_v$、$M,a_0,c_0,\beta,\gamma$、原函数 $h,\rho$ 以及 (18.2) 的 $S_X,L_X$ 均不变。特别地，每个成功条件仍由同一个整数 $n$ 实现，目标仍取遍

$$
u\in a_0+M\widehat{\mathbb Z},\qquad z\in\mathbb T^2.
$$

令 $A>0,\mu>0$ 为定理 17.2 的固定常数。对正整数 $X$ 和任意实数 $r>0$，定义

$$
\begin{aligned}
q_+&=q(h(2X),h(2X);M),\\
r_X&=\rho(2X),\qquad \overline r_X=\rho(X+1),\\
T_X(r)&=\max\left\{\frac1X,
       (AXr^\mu)^{-1/(\mu+1)}\right\},\\
T_X&=T_X(r_X),\qquad \Theta_X=q_+T_X.
\end{aligned}
\tag{19.1}
$$

$T_X(r)$ 随 $r$ 非增。以上仅定义证明所用的预算，不以端点模数或端点半径替换 $L_X$ 中任何一个整数的自身权重。圆上的 Haar 测度仍使 $\mathbb T$ 的总质量为 $1$，故半径 $r\le1/4$ 的二维开窗质量仍为 $4r^2$。

**定理 19.2（原自身阶段的等体积胞相对渐近与幂误差界）。** 对定义 19.1 的固定数据，存在常数 $C>0$ 和整数 $X_0$，只依赖这些固定数据，而不依赖 $u,z$ 或下面的分块数 $K$，使每个整数 $X\ge X_0$、每个整数 $1\le K\le X$ 在 $\Theta_X\le1/3$ 时均满足

$$
\sup_{\substack{u\in a_0+M\widehat{\mathbb Z}\\z\in\mathbb T^2}}
\left|\frac{S_X(u,z)}{L_X}-1\right|
\le C\left[\frac1K+(K+1)\Theta_X\right].
\tag{19.2}
$$

因而，若 $\Theta_X\to0$，则对所有足够大的整数 $X$ 取

$$
K_X=\left\lceil\Theta_X^{-1/2}\right\rceil
\tag{19.3}
$$

可得目标一致的误差上界

$$
\sup_{\substack{u\in a_0+M\widehat{\mathbb Z}\\z\in\mathbb T^2}}
\left|\frac{S_X(u,z)}{L_X}-1\right|
\le C\sqrt{\Theta_X}\longrightarrow0.
\tag{19.4}
$$

这里以及下文的 $C$ 可扩大为另一个只依赖固定数据的常数。特别地，令

$$
\Delta_{\mathrm{geom}}
=1-(\mu+1)c_0^2-\mu\beta.
\tag{19.5}
$$

若 $\Delta_{\mathrm{geom}}>0$，则

$$
\begin{gathered}
\Theta_X=X^{-\Delta_{\mathrm{geom}}/(\mu+1)+o(1)},\\
\sup_{\substack{u\in a_0+M\widehat{\mathbb Z}\\z\in\mathbb T^2}}
\left|\frac{S_X(u,z)}{L_X}-1\right|
\le X^{-\Delta_{\mathrm{geom}}/(2(\mu+1))+o(1)},\\
L_X=X^{1-c_0^2-2\beta+o(1)}\longrightarrow\infty.
\end{gathered}
\tag{19.6}
$$

误差式中的 $o(1)$ 可取为只依赖固定数据的实数序列，不依赖目标；它给出上界，不宣称实际误差具有相等的幂阶。条件 (19.5) 为充分条件，不主张必要性、等号端点或最优性。

**证明（三维格准确保留同一整数与原有限过滤）。** 选定一次 $\alpha\in\mathbb R^2$，作为定义 17.1 中圆坐标向量的实提升；在本证明的格公式中使用此提升。对中心 $z$ 任取实提升，模 $\mathbb Z^2$ 后仍是同一目标。对任意整数 $q\ge1$、$X>0$、$r>0$，取满秩格

$$
\Lambda(q;X,r)=
\left\{\left(\frac{qk}{X},
 \frac{qk\alpha_1-m_1}{r},
 \frac{qk\alpha_2-m_2}{r}\right):
 k,m_1,m_2\in\mathbb Z\right\}.
\tag{19.7}
$$

其基可取 $(q/X,q\alpha_1/r,q\alpha_2/r)$、$(0,-1/r,0)$、$(0,0,-1/r)$，故协体积准确为

$$
d_\Lambda=\det\Lambda=\frac{q}{Xr^2}.
\tag{19.8}
$$

对任意整数 $b$、整数端点 $A_0<B_0$ 及 $0<r\le1/4$，令

$$
\begin{aligned}
\tau&=\left(\frac bX,
       \frac{b\alpha_1-z_1}{r},
       \frac{b\alpha_2-z_2}{r}\right),\\
Q&=(A_0/X,B_0/X]\times(-1,1)^2.
\end{aligned}
$$

则有严格端点的精确等式

$$
\begin{aligned}
&\#\{n\in\mathbb Z:A_0<n\le B_0,\ n\equiv b\pmod q,
        \ \|n\alpha_j-z_j\|_{\mathbb T}<r\ (j=1,2)\}\\
&\hspace{30mm}=\#\bigl((\tau+\Lambda(q;X,r))\cap Q\bigr).
\end{aligned}
\tag{19.9}
$$

事实上，第一坐标给出同一个 $n=b+qk$；后两坐标正好给出 $|n\alpha_j-z_j-m_j|<r$。因 $2r<1$，每个这样的 $n$ 对每个坐标至多有一个 $m_j$，存在性则恰是圆距离条件。没有额外的重数或改变目标的归一化。对实际阶段 $H$，(17.25)、定理 14.2 的 CRT 及 (18.5)–(18.6) 给出真实的 $q=q_H$、$b=b_H$：全部原有限地方条件与 $M$-同余恰好等价于此一个剩余类。于是 (19.9) 计数的是原成功整数的固定半径版本。

**证明（对偶短向量下界与经典覆盖转移）。** 全部长度与对偶均取欧氏约定。由 (19.7) 的三条基向量直接解整数配对条件，得到准确对偶

$$
\Lambda(q;X,r)^*=
\left\{\left(\frac Xq(\ell-q\,m\cdot\alpha),
       rm_1,rm_2\right):\ell\in\mathbb Z,\ m\in\mathbb Z^2\right\}.
\tag{19.10}
$$

后两条基要求后两坐标为 $rm_j$，第一条基再要求 $qx/X+q\,m\cdot\alpha\in\mathbb Z$，这同时证明等式的两个方向。对其中任一非零向量，记其欧氏长度为 $t$。若 $m=0$，则 $\ell\ne0$，所以 $t\ge X/q$。若 $m\ne0$，取整数 $s=\|m\|_\infty\ge1$，由 (17.5) 在 $J=s$ 处的下界有

$$
t\ge rs,\qquad
 t\ge\frac Xq\|q\,m\cdot\alpha\|_{\mathbb T}
 \ge\frac{AX}{q^{\mu+1}s^\mu}.
$$

将第一式取 $\mu$ 次幂，再乘以第二式，得 $t^{\mu+1}\ge AXr^\mu/q^{\mu+1}$。因此最短非零对偶向量长度满足

$$
\lambda_1(\Lambda^*)\ge
\min\left\{\frac Xq,
       \left(\frac{AXr^\mu}{q^{\mu+1}}\right)^{1/(\mu+1)}\right\},
\qquad
\frac1{\lambda_1(\Lambda^*)}\le qT_X(r).
\tag{19.11}
$$

这里直接复用 W. Banaszczyk，*New bounds in some transference theorems in the geometry of numbers*，Math. Ann. **296** (1993)，625–635，[DOI 10.1007/BF01445125](https://doi.org/10.1007/BF01445125)，[原文](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0296/LOG_0038.pdf)，§2 印刷页 632 的 Theorem (2.2)。其准确陈述是：任意满秩欧氏格 $\mathcal L\subset\mathbb R^n$ 满足

$$
\lambda_1(\mathcal L)\,\mu_{\mathrm{cov}}(\mathcal L^*)\le\frac n2.
$$

原文印刷页 625–626 定义 $\mathcal L^*=\{y:\langle y,\mathcal L\rangle\subset\mathbb Z\}$、$\mathcal L^{**}=\mathcal L$，并以欧氏单位球定义 $\lambda_1$ 和覆盖半径 $\mu_{\mathrm{cov}}$；配对没有 $2\pi$ 因子，也不要求整格或协体积为 $1$。在此取 $\mathcal L=\Lambda^*$、$n=3$，恰好得到

$$
\mu_{\mathrm{cov}}(\Lambda)
\le\frac3{2\lambda_1(\Lambda^*)}
\le\frac32qT_X(r).
\tag{19.12}
$$

这是经典转移定理在当前实际格上的代入，不是另一个新转移定理。

**证明（等体积 Voronoi 胞支付所有窗边）。** 以下采用经典的 Voronoi 胞铺砌与边界体积计数法，所需的胞体积和端点事实在此给出完整推导，作为实际移动质量估计的中间步骤。设 $\mathcal L\subset\mathbb R^3$ 满秩，协体积为 $d$，且 $\mu_{\mathrm{cov}}(\mathcal L)\le R\le1$、$R>0$。取闭 Voronoi 胞

$$
V=\{x\in\mathbb R^3:\|x\|_2\le\|x-\lambda\|_2
                \text{ 对所有 }\lambda\in\mathcal L\}.
$$

格的离散性保证每点有最近格点：相对于任一已选格点，只需比较一个有界球内的有限多个格点。因此 $V+\lambda$ 覆盖全空间，且 $V\subset\overline B(0,R)$。两个不同闭胞的交集只能位于到其两个中心等距的平分超平面上。格可数，这些超平面的并为体积零；这里没有声称闭胞作为集合不相交。

取任意半开平行基本域 $P$，则几乎处处有 $\sum_{\lambda\in\mathcal L}\mathbf1_{V+\lambda}=1$。对 $P$ 积分并将非负和换出积分，利用 $P-\lambda$ 不交铺砌全空间，得

$$
\begin{aligned}
d=\operatorname{vol}(P)
&=\sum_{\lambda\in\mathcal L}
       \int_P\mathbf1_V(x-\lambda)\,dx\\
&=\sum_{\lambda\in\mathcal L}
       \int_{P-\lambda}\mathbf1_V(y)\,dy
 =\operatorname{vol}(V).
\end{aligned}
\tag{19.13}
$$

对任意仿射平移 $\tau+\mathcal L$，以其格点为中心的胞仍有同一体积 $d$、同一覆盖及零体积重叠性质。令 $Q$ 为轴平行盒，三条边长为 $(a,2,2)$、$a\ge0$，各端点可任意开闭。选中所有中心属于 $Q$ 的胞，记其有限并为 $U$，则

$$
\operatorname{vol}(U)=d\,\#((\tau+\mathcal L)\cap Q).
$$

选中胞中的每点距其中心至多 $R$。反之，$Q$ 内距边界大于 $R$ 的点所归属的任一最近中心仍在 $Q$ 内，故该点属于 $U$。所以 $U$ 与 $Q$ 的差只可能在边界的闭 $R$ 邻域内；特别地，无论严格端点上是否存在格点，都有上、下包体积

$$
(a-2R)_+(2-2R)_+^2
\le\operatorname{vol}(U)
\le(a+2R)(2+2R)^2,
\tag{19.14}
$$

其中 $x_+=\max(x,0)$。当 $a=0$ 时下包为空，盒本身可以为空或处于一个平面内，上包论证仍然有效。若 $a\ge2R$，两个包体积之差准确为

$$
16aR+16R(1+R^2)\le32(a+1)R.
$$

若 $a<2R$，下包体积为零，上包体积至多 $16(a+2R)\le64R\le64(a+1)R$。盒体积 $4a$ 也介于两包体积之间，因而一并得到

$$
\left|\#((\tau+\mathcal L)\cap Q)-\frac{4a}{d}\right|
\le\frac{64(a+1)R}{d}.
\tag{19.15}
$$

这一步用体积零的胞间重叠作积分，完全没有用“盒边界没有格点”的假设。

将 (19.15) 用于 (19.9)。若 $0<B_0-A_0\le X$ 且 $qT_X(r)\le1/3$，可由 (19.12) 取 $R=3qT_X(r)/2\le1/2$，而 $a=(B_0-A_0)/X\le1$。于是固定半径计数满足

$$
\begin{aligned}
\left|\#((\tau+\Lambda)\cap Q)
       -\frac{4(B_0-A_0)r^2}{q}\right|
&\le64(a+1)\frac{Xr^2}{q}\,
                 \frac32qT_X(r)\\
&\le192Xr^2T_X(r).
\end{aligned}
\tag{19.16}
$$

模数 $q$ 在这一局部绝对误差中准确相消。此处先对每个实际模数完成相消；若先取全局最大覆盖半径再累加 $1/q$，会引入本推导并不需要的模数比。式 (19.16) 对 $1\le B_0-A_0\le X$ 内的任意整数长度均成立，不除以 $B_0-A_0$，也不要求区间内存在允许整数。由 (18.6) 产生的真实 floor 差，以及时间半开端点与空间严格端点的差，均已包含在这次对精确计数 (19.9) 的胞边界估计中，不能再将它理解为忽略了初项。

**证明（任意分块数下的实际自身阶段拼接）。** 沿用 (18.13)–(18.17) 的整数分块与半径夹逼，但本证明任取整数 $1\le K\le X$，切点仍为

$$
t_k=\left\lfloor X+\frac{kX}{K}\right\rfloor
\quad(0\le k\le K).
$$

将 $(t_k,t_{k+1}]\cap\mathbb Z$ 与各实际阶段相交，只丢弃空的整数交集；对每个非空交集 $I_\nu$，按原定义取

$$
\begin{gathered}
A_\nu=\min I_\nu-1,\qquad B_\nu=\max I_\nu,\\
\ell_\nu=B_\nu-A_\nu=\#I_\nu,\qquad
1\le\ell_\nu\le X/K+1,\qquad \ell_\nu\le X.
\end{gathered}
\tag{19.17}
$$

式 (18.14) 乘以固定的 $c_0$ 后仍趋于零，故充分大 $X$ 时 $h$ 在全区间至多有一个阶段跳点。原 $K$ 个非空整数区间因此至多额外分裂一次，非空阶段块的总数满足 $m_X\le K+1$；跳点位置不受限制。每个块，包括只有一个整数的块以及其中允许剩余类计数为零的块，都保留在求和中。

按 (18.16) 置 $r_\nu^+=\rho(A_\nu+1)$、$r_\nu^-=\rho(B_\nu)$。由 (18.15)、$K\le X$ 和 (19.17)，一致地有

$$
\begin{gathered}
r_X\le r_\nu^-\le r_\nu^+\le\overline r_X\le1/4,\\
\frac{r_\nu^+}{r_\nu^-}=1+O(K^{-1}),\qquad
\frac{\overline r_X}{r_X}\longrightarrow2^\beta.
\end{gathered}
\tag{19.18}
$$

这里使用的是每个块的全部整数上的真实最小、最大半径；不把短块的左端 $A_\nu$ 误当成块内整数。令 $H_\nu$ 为该块阶段、$q_\nu=q(H_\nu,H_\nu;M)$，并用 (18.18) 的 $S_\nu,L_\nu$。原有限过滤的嵌套性只需提供 $q_\nu\mid q_+$，从而 $q_\nu\le q_+$。若 $\Theta_X\le1/3$，则两个端点半径同时满足

$$
q_\nu T_X(r_\nu^\pm)\le q_+T_X(r_X)=\Theta_X\le1/3.
$$

分别对 $r_\nu^-$ 与 $r_\nu^+$ 使用 (19.16)。两次局部误差都至多为

$$
192X(r_\nu^\pm)^2T_X(r_\nu^\pm)
\le C Xr_X^2T_X,
\tag{19.19}
$$

因为 $T_X(r_\nu^\pm)\le T_X$，且 (19.18) 给出全区间半径比的固定上界。由 (18.17)，这两次计数夹住同一块内真实变半径计数 $S_\nu$。同时

$$
\frac{4\ell_\nu(r_\nu^-)^2}{q_\nu}
\le L_\nu\le
\frac{4\ell_\nu(r_\nu^+)^2}{q_\nu},
$$

上下体积与 $L_\nu$ 的差均至多 $C K^{-1}L_\nu$，这是 (19.18) 的平方半径比所给出的误差。因此每一块都满足

$$
|S_\nu-L_\nu|
\le C\left[K^{-1}L_\nu+Xr_X^2T_X\right].
\tag{19.20}
$$

这包括没有允许项的块；没有在任何一步除以 $\ell_\nu$ 或其允许项数。

各块不交且覆盖全部 $X$ 个整数，故 $\sum_\nu\ell_\nu=X$、$\sum_\nu L_\nu=L_X$、$\sum_\nu S_\nu=S_X$。又如 (18.21) 一样，原移动质量有不依赖目标的下界

$$
L_X\ge\frac{4Xr_X^2}{q_+}>0.
\tag{19.21}
$$

将 (19.20) 相加，用 $m_X\le K+1$ 后除以 (19.21)，即得

$$
\frac{|S_X-L_X|}{L_X}
\le C\left[\frac1K+
       \frac{(K+1)Xr_X^2T_X}{Xr_X^2/q_+}\right]
=C\left[\frac1K+(K+1)\Theta_X\right].
$$

全部常数均不依赖 $b_{H_\nu},u,z,K$，所以可取全部相容目标的上确界，得到 (19.2)。这里只需要实际整除链提供单边模数界，未估计任何相邻 $q_H$ 之比。

**证明（预算平衡与幂区域）。** 由 (19.1) 有 $\Theta_X\ge q_+/X\ge1/X$。若 $\Theta_X\to0$，则 (19.3) 对充分大 $X$ 满足

$$
1\le K_X\le\sqrt X+1\le X,\qquad
\frac1{K_X}\le\sqrt{\Theta_X},\qquad
(K_X+1)\Theta_X\le\sqrt{\Theta_X}+2\Theta_X.
$$

同时 $\Theta_X\le1/3$ 最终成立，代入 (19.2) 得 (19.4)。平衡的是变半径误差 $K^{-1}$ 与累计胞边界误差 $K\Theta_X$；$K_X$ 只选择证明的分割，完全不改变原 $h,\rho,S_X,L_X$。

还需核实 (19.5) 确实给出 (19.6) 及质量发散。先由 (17.5) 推出所用的 $\mu\ge2$，不额外假设虚拟的指数。对任意正整数 $N$，考虑 $(N+1)^2$ 个数

$$
\{m\cdot\alpha\}\in[0,1),\qquad m\in\{0,\ldots,N\}^2.
$$

将 $[0,1)$ 分成 $N^2$ 个等长半开区间，抽屉原理给出两个不同的指标之差 $m'$，满足 $0<\|m'\|_\infty\le N$ 及 $\|m'\cdot\alpha\|_{\mathbb T}<N^{-2}$。用 (17.5) 的 $q=1,J=N$ 得 $AN^{-\mu}<N^{-2}$ 对所有 $N$ 成立。若 $\mu<2$，则这要求固定的 $A>0$ 小于趋于零的 $N^{\mu-2}$，矛盾。故 $\mu\ge2$。

定理 16.7 的实际周期主阶与 (18.1) 给出

$$
q_+=X^{c_0^2+o(1)},\qquad
r_X=X^{-\beta+o(1)},\qquad
(AXr_X^\mu)^{-1/(\mu+1)}
 =X^{-(1-\mu\beta)/(\mu+1)+o(1)}.
\tag{19.22}
$$

因 $\mu>0$、$\beta\ge0$，后一个幂指数严格大于 $-1$，所以它最终支配 $T_X$ 中的 $X^{-1}$ 项。于是

$$
\Theta_X
=X^{c_0^2-(1-\mu\beta)/(\mu+1)+o(1)}
=X^{-\Delta_{\mathrm{geom}}/(\mu+1)+o(1)}.
\tag{19.23}
$$

当 $\Delta_{\mathrm{geom}}>0$ 时，这趋于零；(19.4) 给出 (19.6) 的目标一致幂误差上界，固定乘法常数可吸收到指数中的 $o(1)$。

为得到移动质量的准确幂阶，再置 $q_-=q(h(X+1),h(X+1);M)$。实际整除链和半径的单调性给出

$$
\frac{4Xr_X^2}{q_+}\le L_X
\le\frac{4X\overline r_X^2}{q_-}.
\tag{19.24}
$$

定理 16.7 同样给出 $q_-=X^{c_0^2+o(1)}$，且 $\overline r_X=X^{-\beta+o(1)}$，所以两端共同证明 (19.6) 的质量幂阶。又因 $\mu\ge2$、$c_0>0$，有

$$
c_0^2+2\beta
< (\mu+1)c_0^2+\mu\beta<1.
$$

质量因此趋于无穷。这里对 $q_-$ 的使用只为夹住 $L_X$ 的幂阶，没有把 $q_+/q_-$ 放入误差预算。

与定理 18.2 已给出的充分区域比较，旧条件左端减去新条件左端为 $(\mu+2)\beta$。因此旧严格区域包含于新严格区域；在 $\beta>0$ 的参数部分，新的充分区域严格扩大。例如任取 $0<\beta<1/(2\mu+2)$，区间

$$
\frac{1-(2\mu+2)\beta}{\mu+1}
\le c_0^2<\frac{1-\mu\beta}{\mu+1}
$$

非空且两端为正，其中每个参数均满足新条件而不满足旧严格条件。当 $\beta=0,\gamma>0$ 时，两条幂区域相同，新估计仍包含该对数缩窗情形；$\gamma$ 的贡献只进入 (19.22)–(19.24) 的 $o(1)$。本证明不改变旧充分结论，也不将任一条件外或等号端点的行为判作失败。

用白话说，把同一个整数和两条实轨迹一起放进一个三维格，有限地方的全部条件决定这条轨迹的真实步长。丢番图下界阻止对偶格出现过短的非零向量，经典覆盖转移再阻止原格留下过大的空洞。每个格点周围的 Voronoi 胞体积相等，把胞的体积加起来就得到主项，计数和体积的差只能出现在窗边。先在每个实际阶段的局部误差中相消模数，再把包括极短块在内的边界误差相加，最后平衡分块细度与窗边误差，就得到对原移动质量的一致相对渐近和明确幂误差上界；不需要改变原钥匙，也不需要强迫相邻周期接近。

文献归属上，欧氏覆盖转移为上述 Banaszczyk 定理的直接复用（literature-attested），Voronoi 等体积铺砌、边界体积计数及抽屉原理均为经典结构；它们只在本定理内部承担中间步骤。本条关于原实际自身阶段、原共同整数与全部相容目标的拼接、局部模数相消及 (19.5)–(19.6) 的充分区域和误差率，是这些输入在本卷对象上的综合推导（repo-derived），不主张全领域原创优先权。本结论限于所列固定算术数据的条件性同时逼近与计数，不构成完整的 $\mathbb Z/\mathbb Q$ 丢番图定义、量子物理起源、数值计算效率或最优性结论。$\square$

## 追加锚（本行以下为增补区）

## 20. 原完整地方目标的零一律、真实相关核与有限精度边界

**定义 20.1（原命中的目标空间事件）。** 保持定义 17.1、18.1 的实际 $F,E_0,P_1,P_2$、正实根、指定实嵌入、圆坐标 $\theta$、$\alpha$、全部有限地方的原过滤 $U_v$ 以及目标同胚 $\eta$。固定整数 $M\ge1,a_0\in\mathbb Z$，令

$$
\begin{gathered}
A=\{n\ge1:n\equiv a_0\pmod M\},\qquad
C_M=a_0+M\widehat{\mathbb Z},\qquad Y=C_M\times\mathbb T^2,\\
\nu=\lambda_{C_M}\otimes m_{\mathbb T^2},\\
h(n)=\max\left(2,\left\lfloor c_0\sqrt{\log(n+2)}\right\rfloor\right),\qquad
\rho_n=\rho(n)=(n+2)^{-\beta}(\log(n+2))^{-\gamma},\\
q_H=q(H,H;M),\qquad q_n=q_{h(n)}.
\end{gathered}
\tag{20.1}
$$

$\lambda_{C_M}$ 是该余类上的归一化 Haar 概率，$m_{\mathbb T^2}$ 是两圆的归一化面积；本节 $\nu$ 表示目标空间概率。$h,\rho$ 始终是 (18.1)：$c_0>0,\beta,\gamma\ge0,\beta+\gamma>0$，不改变其取整或初段。$M\mid q_H$，且 $H\le K$ 时 $q_H\mid q_K$：原过滤的嵌套使每个旧有限商中的阶整除加深后的阶，而增添地方只向最小公倍数增添因子。因此 $m\le n$ 时 $q_m\mid q_n$，同时 $\rho_m\ge\rho_n>0$。

对 $k\ge1,j=1,2$，令 $I_{j,k}=\{z_j\in\mathbb T:\|k\alpha_j-z_j\|_{\mathbb T}<\rho_k\}$。在 $Y$ 中定义

$$
\begin{aligned}
E_n&=
\begin{cases}
(n+q_n\widehat{\mathbb Z})\times I_{1,n}\times I_{2,n},&n\in A,\\
\varnothing,&n\notin A,
\end{cases}\\
R&=\limsup_{n\to\infty}E_n
=\bigcap_{K\ge0}\ \bigcup_{n>K}E_n,\qquad
S_X(u,z)=\sum_{X<n\le2X}\mathbf1_{E_n}(u,z).
\end{aligned}
\tag{20.2}
$$

这里 $S_X$ 恰为 (18.2) 的原计数。事实上，对 $u\in C_M$，式 (17.25) 在 $H=h(n)$ 给出

$$
\begin{split}
(u,z)\in E_n\quad\Longleftrightarrow\quad
&n\in A,\quad \|\theta([n]P_j)-z_j\|_{\mathbb T}<\rho_n\quad(j=1,2),\\
&[n]P_j-\eta_{v,j}(u)\in U_v(h(n))\\
&\hspace{12mm}(p\le h(n),\ v\mid p,\ j=1,2).
\end{split}
\tag{20.3}
$$

故 $R$ 是原全部相容目标中有无限多个成功整数的集合。每次事件中的全部条件仍由同一个 $n$ 承担；$E_n$ 没有以独立模型替换任何地方条件。定理 14.2 已证明 $\eta$ 单射且为到原完整有限目标空间的同胚，因而这里的目标空间和拓扑也保留了全部有限端信息。

**定理 20.2（原目标的共同移位、类别与二阶充分判据）。** 对定义 20.1 的全部固定参数，令

$$
T(u,z)=(u+M,z+M\alpha).
$$

则对每个 $n\ge1$ 有 $T^{-1}E_{n+M}\subseteq E_n$，从而

$$
T^{-1}R\subseteq R,\qquad
\nu(T^{-1}R\mathbin\triangle R)=0,\qquad
\nu(R)\in\{0,1\}.
\tag{20.4}
$$

第一项包含是逐点结论；第二项只是模零相等，不将其加强为原集合的逐点相等。另有 $R$ 为 $Y$ 中的稠密 $G_\delta$。仅就这一类别结论而言，将 $\rho_n$ 换成任意逐项严格正的半径序列，保留同一 $q_n$ 和允许中心，结论仍成立；无须给出缩小速度或单调性。

记 $a_n=\nu(E_n)$。全部指标范围内的准确质量及最终的块平均为

$$
\begin{aligned}
a_n&=\mathbf1_A(n)\frac{M}{q_n}\min(1,2\rho_n)^2,\\
\int_Y S_X\,d\nu
&=4M\sum_{\substack{X<n\le2X\\n\in A}}\frac{\rho_n^2}{q_n}
\quad\text{（所有足够大的整数 }X\text{）}.
\end{aligned}
\tag{20.5}
$$

第二式一般不是 $M L_X$；原 $L_X=4\sum_{X<n\le2X}\rho_n^2/q_n$ 仍对块内全部整数求和。这里没有重定义原移动质量。

对允许的 $m,n\in A$、$m\le n$，真实交集满足

$$
\nu(E_m\cap E_n)
=\mathbf1_{\{q_m\mid n-m\}}\frac{M}{q_n}
 \prod_{j=1}^2|I_{j,m}\cap I_{j,n}|,
\tag{20.6}
$$

其中 $|\cdot|$ 为圆上的归一化弧长；任一指标不在 $A$ 时交集为空。特别地，若 $\rho_m+\rho_n\le1/2$，置 $x_+=\max(x,0)$，则

$$
|I_{j,m}\cap I_{j,n}|
=\min\left\{2\rho_n,
 \bigl(\rho_m+\rho_n-\|(n-m)\alpha_j\|_{\mathbb T}\bigr)_+\right\}.
\tag{20.7}
$$

有限端和两个实端在 (20.6)–(20.7) 中共用同一个差 $n-m$，不拆开为分别最优的交集。

令

$$
A_N=\sum_{n=1}^N a_n,\qquad
Q_N=\sum_{m,n=1}^N\nu(E_m\cap E_n).
$$

若

$$
A_N\longrightarrow\infty,\qquad
\kappa:=\limsup_{N\to\infty}\frac{A_N^2}{Q_N}>0,
\tag{20.8}
$$

则 $\nu(R)=1$。发散前提保证足够大的 $N$ 有 $Q_N\ge A_N^2>0$，故比值在尾部有定义且不超过 $1$。这是使用真实交集核的充分条件，不要求该比值趋于 $1$，也不主张它是必要条件。

**证明（共同中心尾与原平移）。** 首先对任意非空基本窗

$$
V=\bigl((b+d\widehat{\mathbb Z})\cap C_M\bigr)\times W,
\qquad b\in\mathbb Z,\ d\ge1,
$$

其中 $W\subseteq\mathbb T^2$ 为非空开集，证明允许共同中心 $(n,n\alpha)$ 的每条正尾都与 $V$ 相交。有限端非空等价于 $\gcd(M,d)\mid b-a_0$；CRT 给出唯一的共同整数类 $t\pmod\ell$，$\ell=\operatorname{lcm}(M,d)$。定理 11.3 对这条固定等差进程的尾稠密结论，经 $\theta^2$ 运输后保证任意晚的 $n\equiv t\pmod\ell$ 满足 $n\alpha\in W$。这个同一 $n$ 同时落在两个有限余类中。因此

$$
\overline{\{(n,n\alpha):n\in A,\ n>K\}}=Y
\quad(K\ge0).
\tag{20.9}
$$

这是真实联合尾稠密，证明并未用两个投影各自稠密代替联合稠密。

若 $n\notin A$，则 $n+M\notin A$，所需事件包含平凡成立。若 $T(u,z)\in E_{n+M}$，则

$$
u+M\equiv n+M\pmod{q_{n+M}},\qquad
\|(n+M)\alpha_j-(z_j+M\alpha_j)\|_{\mathbb T}<\rho_{n+M}.
$$

由 $q_n\mid q_{n+M}$ 及 $\rho_{n+M}\le\rho_n$，得 $(u,z)\in E_n$。在 limsup 中删去有限个指标、再以 $n+M$ 重编号，便有 $T^{-1}R\subseteq R$。$T$ 是 $Y$ 上的可逆保测平移，因此 $\nu(T^{-1}R)=\nu(R)$，其差集为零测。这只用模数与半径的两种单调性，不需要 $\rho(n+M)/\rho(n)\to1$。

为核对这里所需的遍历性，将 $Y$ 以 $(a_0,a_0\alpha)$ 为原点识别为紧度量群

$$
G=M\widehat{\mathbb Z}\times\mathbb T^2.
$$

$T$ 对应于加 $g=(M,M\alpha)$。由 (20.9)，$g$ 生成的子群在 $G$ 中稠密。设某可测集 $B$ 在加 $g$ 下模零不变，$f=\mathbf1_B\in L^2(G)$。则对每个整数 $k$，$f(\cdot+kg)=f$ 在 $L^2$ 中成立。平移在 $L^2(G)$ 中强连续：连续函数的结论由紧性和一致连续性得到，一般 $L^2$ 函数用连续函数逼近，且平移保持 $L^2$ 范数。由稠密性遂得每个 $h\in G$ 都满足 $f(\cdot+h)=f$。记 $p=\nu(B)$，对 $h$ 积分并用 Haar 不变性和 Fubini，得

$$
0=\int_G\int_G|f(x+h)-f(x)|^2\,d\nu(x)\,d\nu(h)
=2p-2p^2.
$$

所以 $p\in\{0,1\}$。将此结论用于已经模零不变的 $R$，得到 (20.4) 的零一律。此处给出的是稠密生成元平移遍历的经典证明在原共同目标群上的应用。

每个 $E_n$ 都开；对 $n\in A$，它含自身中心 $(n,n\alpha)$。由 (20.9)，每个 $\bigcup_{n>K}E_n$ 开且稠密。$Y$ 是非空紧度量空间，Baire 定理使它们的可数交稠密，即得到 $R$ 的 $G_\delta$ 结论。该段只用了正半径、有限模数与共同中心尾稠密，故也证明了所述任意正半径的类别结论，不能据此推出正测度。

**证明（准确质量与交集）。** $n\in A$ 时，因 $M\mid q_n$，柱集 $n+q_n\widehat{\mathbb Z}$ 在 $C_M$ 中的归一化质量为 $M/q_n$。圆上半径 $\rho_n$ 的严格开球长度为 $\min(1,2\rho_n)$；$\rho_n=1/2$ 时只少一个点，长度仍为 $1$。乘积测度给出第一式 (20.5)。因 $\rho_n\to0$，足够大的整块均有 $\rho_n<1/2$；对有限和积分即得第二式。初段不能一概套用 $4\rho_n^2$。

对 $m\le n$，两个有限柱集相交当且仅当 $q_m\mid n-m$；相交时交集恰为 $n+q_n\widehat{\mathbb Z}$。实两圆上的条件仍分别为原两弧的交，因此得 (20.6)。为证明 (20.7)，令 $a=\rho_m\ge b=\rho_n$、$\delta=\|(n-m)\alpha_j\|_{\mathbb T}$。在 $a+b\le1/2$ 下，除零长度的端点接触外，至多有一对最近的实轴提升相交。若 $\delta\ge a+b$，交长为零；若 $\delta\le a-b$，小弧被大弧包含，交长为 $2b$；余下 $a-b<\delta<a+b$ 时交长为 $a+b-\delta$。三种情形正好是 (20.7)，严格端点不影响弧长。没有此半径和限制时只使用 (20.6) 的圆弧交长，不使用这个实轴单交段公式。

**证明（每个固定尾的二阶矩）。** 对固定整数 $K\ge0$、$N>K$，令

$$
F_{K,N}=\sum_{K<n\le N}\mathbf1_{E_n},\qquad
U_K=\bigcup_{n>K}E_n.
$$

Cauchy–Schwarz 在 $F_{K,N}>0$ 的支集上给出

$$
\begin{aligned}
(A_N-A_K)^2
&=\left(\int F_{K,N}\,d\nu\right)^2\\
&\le\nu\!\left(\bigcup_{K<n\le N}E_n\right)
       \int F_{K,N}^2\,d\nu\\
&\le\nu(U_K)\,Q_N.
\end{aligned}
\tag{20.10}
$$

最后一步只舍去 $Q_N$ 中非负的前缀交集项。由 $A_N\to\infty$，对固定 $K$ 有 $(A_N-A_K)/A_N\to1$，故取上极限得 $\nu(U_K)\ge\kappa$。又 $U_K$ 递减且 $\nu$ 为概率，测度的上连续性给出

$$
\nu(R)=\lim_{K\to\infty}\nu(U_K)\ge\kappa>0.
$$

再由零一律得 $\nu(R)=1$。这个推导针对每一个固定尾，不以有限前缀并集的增长代替尾事件；也没有假设事件独立。

单调缩靶加遍历性得零一律的经典先例见 Fayad，*Two Remarks on the Shrinking Target Property*，[arXiv:math/0501205v1](https://arxiv.org/pdf/math/0501205v1)，Remark 1.4，印刷第 2–3 页。正向中心记法下使用逆平移的表述见 Tseng，*On Circle Rotations and the Shrinking Target Properties*，[arXiv:math/0702853v2](https://arxiv.org/pdf/math/0702853v2)，§3.2 首段，印刷第 6 页。二阶矩下界为 Kochen–Stone 的经典方法（[DOI:10.1215/ijm/1256059668](https://doi.org/10.1215/ijm/1256059668)）；这里所需的尾部估计已由 (20.10) 完整给出，不依赖其原文的特定定理编号。上述一般方法均为 literature-attested 的中间输入；本条关于原全部地方过滤的合法共同移位、联合尾稠密、准确质量和共同差交集核的组合为本卷对象上的综合推导（repo-derived），不主张一般零一或二阶矩理论的原创优先权。$\square$

**定理 20.3（超临界原目标纤维与一致计数的容量边界）。** 对定义 20.1 的固定参数，置

$$
s=c_0^2+2\beta.
$$

若 $s>1$，则 $\sum_n\nu(E_n)<\infty$，$R$ 为 Haar 零测的稠密 $G_\delta$，而 $Y\setminus R$ 为满测、稠密、第一纲的 $F_\sigma$。每个非空基本窗

$$
V=\bigl((b+d\widehat{\mathbb Z})\cap C_M\bigr)\times W
$$

（$d\ge1$，$W\subseteq\mathbb T^2$ 非空开）都有

$$
\nu(V)=\frac{M}{\operatorname{lcm}(M,d)}\operatorname{area}(W)>0,
\qquad V\cap R\ne\varnothing,\qquad V\setminus R\ne\varnothing.
\tag{20.11}
$$

所以在同一个有限余类与实开窗中，既有固定的无限命中目标，也有固定的有限命中目标；$\mathbf1_R:Y\to\{0,1\}$ 处处不连续。这排除用此类有限信息，对窗内所有精确目标给出相同且处处正确的完整二分判别。

另对本节的全部参数，不要求 $s>1$，每个足够大的整数 $X\ge M$ 均有

$$
\sup_{\substack{u\in C_M\\z\in\mathbb T^2}}
\left|\frac{S_X(u,z)}{L_X}-1\right|\ge\frac1{2L_X}.
\tag{20.12}
$$

因而原目标一致相对渐近的必要条件是 $L_X\to\infty$。此下界允许目标随 $X$ 选择，不声称由它找到了一个固定目标的渐近反例，也不声称该必要条件充分。

作为参数范围的对照，若定理 19.2 的常数 $\mu$ 满足

$$
(\mu+1)c_0^2+\mu\beta<1,
\tag{20.13}
$$

则 $R=Y$，是每个相容目标都无限命中的逐点结论。超临界的信息边界不延伸到全部参数。仅由本节的周期主阶与质量公式，在临界 $s=1$ 不裁定一阶级数收敛或发散，也不裁定 $\nu(R)$ 为 $0$ 还是 $1$；零一律本身在临界仍成立。

**证明（超临界的测度与类别）。** 定理 16.7 给出固定 $M$ 下 $\log q(H,H;M)\sim H^2$。原取整函数最终满足

$$
h(n)^2=c_0^2\log(n+2)+O\!\left(\sqrt{\log(n+2)}\right),
$$

所以

$$
q_n=(n+2)^{c_0^2+o(1)},\qquad
\frac{\rho_n^2}{q_n}=(n+2)^{-s+o(1)}.
\tag{20.14}
$$

第二式把固定的对数因子 $(\log(n+2))^{-2\gamma}$ 计入 $o(1)$，不是将其删去。当 $s>1$ 时，取 $0<\varepsilon<s-1$，足够大 $n$ 的质量由 (20.5) 满足

$$
0\le a_n\le4M(n+2)^{-s+\varepsilon}.
$$

右端可求和，初段有限，故 $\sum_n a_n<\infty$。直接对任意尾作并集上界，得

$$
\nu(R)\le\nu\!\left(\bigcup_{n>K}E_n\right)
\le\sum_{n>K}a_n\longrightarrow0.
$$

这是 Borel–Cantelli 收敛部分的直接证明，不依赖独立性。定理 20.2 已给出 $R$ 稠密 $G_\delta$；其补集是各个稠密开尾并集的闭补集之可数并，所以为第一纲 $F_\sigma$。其满测性使之稠密：$Y$ 的任意非空开集都含一个非空基本窗，且这种窗的测度严格为正。

具体地，CRT 将 $(b+d\widehat{\mathbb Z})\cap C_M$ 写成模 $\operatorname{lcm}(M,d)$ 的一个余类。它在 $\widehat{\mathbb Z}$ 中的质量为该模数的倒数，再除以 $C_M$ 的质量 $1/M$，并乘 $\operatorname{area}(W)$，即得 (20.11) 的测度。由 $R$ 稠密和其补集满测，该窗中两类目标都存在。对每一个先固定的窗，可以分别固定其中两个精确目标；随后“无限”或“有限”均针对各自同一个目标的整个原整数序列。由于每个邻域都含两类目标，$\mathbf1_R$ 在每一点都不连续。

若讨论有限输出程序，此处的信息模型严格限定如下：输入为精确的 $(u,z)$；一次完成的有限观察只指定一个包含它的基本窗；该次输出必须对窗内全部精确目标保持相同且正确。在 $s>1$ 下，没有任何非空基本窗能承载这种正确的完整二分输出。等价地，若一个处处终止的判别规则要求每个输入的最终输出在某基本邻域内稳定，则它不能处处等于 $\mathbf1_R$。这是指定有限精度模型中的局部稳定性障碍，不是 Turing 不可判定性，也不是对任意信息表示、任意算法或任意公理系统的否定。

**证明（原移动质量与整数计数容量）。** 对足够大的整数 $X\ge M$，区间 $(X,2X]$ 含一个 $n_X\in A$。选原目标 $u_X=n_X\in C_M$；这个选取允许依赖 $X$。固定此 $u_X$ 后，有限端判据只决定哪些整数保留，于是

$$
S_X(u_X,z)=\sum_{n\in B_X}\mathbf1_{\mathcal B_n}(z),\qquad
B_X=\{X<n\le2X:n\in A,\ u_X\equiv n\pmod{q_n}\},\qquad
\mathcal B_n=I_{1,n}\times I_{2,n}.
$$

$B_X$ 至少含 $n_X$。因 $\rho_n\to0$，可将 $X$ 取得足够大，使全部这些半径小于 $1/4$，每个 $\mathcal B_n$ 都是 $\mathbb T^2$ 的非空真开盒。其指标函数下半连续。

若上述有限和恒为常数 $c$，任选 $n\in B_X$，则

$$
\mathbf1_{\mathcal B_n}
=c-\sum_{\substack{k\in B_X\\k\ne n}}\mathbf1_{\mathcal B_k}
$$

又是上半连续函数，因而连续。但 $\mathbb T^2$ 连通，连续的 $\{0,1\}$ 值函数必为常数，与 $\mathcal B_n$ 非空且为真子集矛盾。因此 $S_X(u_X,\cdot)$ 非恒定且为整数值，有两个函数值至少相差 $1$。它们不可能同时距同一个实数 $L_X$ 小于 $1/2$，故

$$
\sup_z|S_X(u_X,z)-L_X|\ge\tfrac12.
$$

由原定义 $L_X>0$，除以 $L_X$、再放大为全部 $u,z$ 的上确界，得 (20.12)。若左端一致相对误差趋于零，则 $1/(2L_X)\to0$，所以必须 $L_X\to\infty$。

此必要条件直接联系到同一周期主阶。式 (20.14) 在 $X<n\le2X$ 上一致地给出权重为 $X^{-s+o(1)}$；原 $L_X$ 对该区间的全部 $X$ 个整数求和，因而

$$
L_X=X^{1-s+o(1)}.
\tag{20.15}
$$

这里的一致性来自尾部定义：给定任意正误差指数，(20.14) 的上下幂界对所有足够大的 $n$ 同时成立。在 $s>1$ 下，$L_X\to0$，(20.12) 的右端反而趋于无穷；它说明原目标一致相对渐近失败，但所选 $u_X$ 随 $X$ 改变，仍不是单一固定目标反例。在 $s=1$ 时，(20.15) 只是 $L_X=X^{o(1)}$，不能判定其趋向，更不证明临界一致渐近失败。

**证明（充分区域与尚缺的真实相关性估计）。** 若 (20.13) 成立，定理 19.2 给出原 $S_X/L_X\to1$ 对全部目标一致成立且 $L_X\to\infty$。因此对所有足够大的整数 $X$、所有 $(u,z)\in Y$，均有 $S_X(u,z)>0$。在互不相交的区间 $(2^k,2^{k+1}]$ 上应用，便知每个固定目标都被无限多个不同整数命中，即 $R=Y$。这保留的是原全部地方过滤、原自身阶段和全部相容目标，并未由满测替代逐点全体。

当 $s<1$ 时，(20.14) 也给出一阶和发散：选 $0<\varepsilon<1-s$，在 $A$ 的足够大指标上有 $a_n\ge4M(n+2)^{-s-\varepsilon}$，而固定等差进程上的该幂级数发散。但在已证明的逐点充分区域之外，这并不自动给出满测。另一个义务是证明无限尾交 $R$ 具有正测度；(20.8) 通过真实 $Q_N$ 对每条尾并集给出同一个正下界，才完成此义务。实际 $\alpha$ 的 (20.6) 二阶和估计没有在这里被一阶发散替代。

在 $s=1$ 时，当前主阶不足以确定 $\sum_{n\in A}\rho_n^2/q_n$ 的敛散；即使另行证明其发散，仍须提供正测度论证，例如满足 (20.8) 的真实交集估计。Fayad 上引 v1 的 Theorem 2.3 与 §2.4（印刷第 4–5 页）给出了环面旋转中体积和发散不能无条件推出满测的经典边界；这不是本节固定实际 $\alpha$ 的反例，也不把一般旋转中的构造直接移植到这里。

残余而零测的一维固定无理旋转先例见 Schmeling–Troubetzkoy，*Inhomogeneous Diophantine approximation and angular recurrence for polygonal billiards*，[arXiv:math/0105150v2](https://arxiv.org/pdf/math/0105150v2)，Proposition 3.1 及证明，印刷第 5–6 页。Baire、Borel–Cantelli、有限整数值振幅与连通性的上述使用均为经典中间方法；本条从原实际共同周期、完整目标同胚和原计数所得的超临界测度、目标纤维与容量边界是项目综合推导（repo-derived），不将一维先例无条件升级为本联合结论，也不主张一般理论的首次发现。

用白话说，每个整数仍是一把同时应付两条实轨迹和所有指定有限地方的钥匙。把整组目标连同实端一起平移一个允许步长，较晚钥匙能打开的门一定能回退到较早阶段；共同中心在完整目标空间里任意晚都稠密，因而无限命中的目标比例只能是零或一。可是稠密不等于占有正比例：超临界时，每把钥匙能打开的目标总量加起来有限，无限命中的目标虽然在每个精度窗里都存在，仍只占零测；同一窗里也始终有固定的有限命中目标。因此有限窗口信息不足以对窗内每个精确目标统一判别。要在发散区域证明比例为一，还得控制同一整数差在所有端共同造成的真实重叠；一阶总量与正测度是两个不同的证明义务。这里的边界不涉及完整 $\mathbb Z/\mathbb Q$ 丢番图定义、量子起源、最优性或无条件的计算不可判定性。$\square$

## 追加锚（本行以下为增补区）

## 21. 原临界好阶段的一阶发散、准确联合能量与三维非退化接口

**定义 21.1（原临界阶段及其固定半径子事件）。** 保持定义 20.1 的全部实际 CM 点、同一个整数、原有限地方过滤、$M,a_0,Y,\nu,E_n,R$ 与原 $h,\rho,L_X$，只限定参数

$$
c_0^2+2\beta=1.
\tag{21.1}
$$

令 $\vartheta(t)=\sum_{p\le t}\log p$，并定义

$$
\begin{gathered}
\mathcal H_- =\{H\in\mathbb Z:H\ge7,\ \vartheta(H)<H\},\qquad
T_H=\frac{(H+1/2)^2}{c_0^2},\qquad X_H=\lfloor e^{T_H}\rfloor,\\
r_H=\rho(2X_H),\qquad q_H=q(H,H;M),\qquad d_H=q_H/M,\\
J_H=\#\{X_H<n\le2X_H:n\equiv a_0\pmod M\},\qquad
K_H=\frac{J_H}{d_H}=\frac{MJ_H}{q_H},\\
a_H=\lfloor K_H\rfloor,\qquad \tau_H=K_H-a_H.
\end{gathered}
\tag{21.2}
$$

以下阶段均取 $H\in\mathcal H_-$ 的充分大尾部；定理 21.2 将证明该集合无界，整块的 $h(n)=H$，且 $0<r_H<1/4$、$K_H\ge1$。对块内的 $n\in A$ 置

$$
\begin{gathered}
F_{n,H}=(n+q_H\widehat{\mathbb Z})\times
 \{z\in\mathbb T^2:\|n\alpha_j-z_j\|_{\mathbb T}<r_H\ (j=1,2)\},\\
V_H=\sum_{\substack{X_H<n\le2X_H\\n\in A}}\mathbf1_{F_{n,H}},\qquad
B_H=\{V_H>0\},\qquad
m_H=\int_Y V_H\,d\nu,\qquad \mathcal E_H=\int_Y V_H^2\,d\nu.
\end{gathered}
\tag{21.3}
$$

有限端仍是全部原地方条件的准确编码；只将同块的两个实半径统一缩小到 $r_H$。符号 $K_H$ 是对目标平均的允许项数，不是固定 $u$ 的整数项数，也不是 $\lfloor X_H/q_H\rfloor$。

**定理 21.2（临界一阶义务与准确有限纤维分配）。** 存在只依赖固定数据的 $C_0>0$，使所有充分大的 $H\in\mathcal H_-$ 满足

$$
\begin{gathered}
h(n)=H\quad(X_H<n\le2X_H),\qquad F_{n,H}\subseteq E_n,\\
\frac{X_Hr_H^2}{q_H}\ge C_0e^{2H}H^{-4\gamma}\longrightarrow\infty,\\
L_{X_H}\ge\frac{4X_Hr_H^2}{q_H},\qquad
m_H=4r_H^2K_H\ge\frac{2X_Hr_H^2}{q_H}\longrightarrow\infty.
\end{gathered}
\tag{21.4}
$$

特别地，原临界问题无条件满足

$$
\sum_{n\ge1}\nu(E_n)=\infty,\qquad
\limsup_{X\to\infty}L_X=\infty.
\tag{21.5}
$$

对固定 $u\in C_M$，记块内满足有限条件的准确项数为

$$
N_H(u)=\#\{X_H<n\le2X_H:n\in A,\ u\equiv n\pmod{q_H}\}.
$$

它在 $u$ 的归一化 Haar 分布下满足

$$
\lambda_{C_M}(N_H=a_H)=1-\tau_H,\qquad
\lambda_{C_M}(N_H=a_H+1)=\tau_H.
\tag{21.6}
$$

当 $\tau_H=0$ 时第二种情况的概率为零。结论 (21.5) 不加强为全序列 $L_X\to\infty$，也不裁定 $\nu(R)$。

**证明（负振荡与原取整）。** 经典输入是 Littlewood 的
$\psi(x)-x=\Omega_-(\sqrt{x}\log\log\log x)$：存在 $c>0$ 及 $x_j\to\infty$，使 $\psi(x_j)\le x_j-c\sqrt{x_j}\log\log\log x_j$。此版本见 Platt–Trudgian，*On the first sign change of $\theta(x)-x$*，[arXiv:1407.1914v1 原文](https://arxiv.org/pdf/1407.1914v1)，第 1 页式 (2)；第 2 页首段亦明确指出 $\theta(x)-x$ 无限变号。这是 literature-attested 的输入，不在这里重证振荡定理。

取 $H_j=\lfloor x_j\rfloor$。负振荡的绝对幅度最终大于 $1$，而每个 $p\le H_j$ 也在 $\psi(x_j)$ 中出现，故

$$
\vartheta(H_j)\le\psi(x_j)<x_j-1\le H_j.
$$

因此 $\mathcal H_-$ 无界。这里不估计 $\psi-\vartheta$，也不用素数定理把其误差降至线性以下的某个指定尺度。

固定充分大的 $H$。对 $X_H<n\le2X_H$ 有

$$
e^{T_H}<n+2\le2X_H+2\le3e^{T_H},\qquad
(H+1/2)^2\le c_0^2\log(n+2)
 \le(H+1/2)^2+c_0^2\log3<(H+1)^2.
$$

故原取整给出整块 $h(n)=H$。由 $\rho$ 单调，$r_H\le\rho_n$，于是 $F_{n,H}\subseteq E_n$；同时 $r_H\to0$。

由 $X_H\ge e^{T_H}/2$、$2X_H+2\le3e^{T_H}$、$\log(2X_H+2)\ll H^2$ 及 (21.1)，有某个 $C_1>0$ 使

$$
X_Hr_H^2\ge C_1e^{(1-2\beta)T_H}H^{-4\gamma}
 =C_1e^{(H+1/2)^2}H^{-4\gamma}.
$$

原整除上界 (16.26) 保留 $(H-1)$，准确给出

$$
q_H\le5M\exp((H-1)\vartheta(H))
 \le5M\exp(H(H-1))\qquad(H\in\mathcal H_-).
$$

两式相除，指数差为 $(H+1/2)^2-H(H-1)=2H+1/4$，得 (21.4) 的指数下界。这里只需原实际周期的上界，没有把消去数作为实际周期的下界。

**证明（$M$ 与两个相邻的整数长度）。** 写 $u=a_0+Mv$，则 $v$ 在 $\widehat{\mathbb Z}$ 中 Haar 均匀。块内所有 $n\in A$ 可准确写成 $a_0+Mt$，其中 $t$ 遍历连续的 $J_H$ 个整数；条件 $u\equiv n\pmod{q_H}$ 等价于 $v\equiv t\pmod{d_H}$。对 $J_H=a_Hd_H+s_H$ 作欧几里得分解，$0\le s_H<d_H$，这段连续整数在 $s_H$ 个模 $d_H$ 的类中各有 $a_H+1$ 项，在其余类中各有 $a_H$ 项。各类的目标概率均为 $1/d_H$，且 $s_H/d_H=\tau_H$，故得 (21.6)。

每个有限端合格的整数在实端占面积 $4r_H^2$，因此 $m_H=4r_H^2K_H$。准确端点计数亦给出

$$
J_H=\left\lfloor\frac{2X_H-a_0}{M}\right\rfloor-
     \left\lfloor\frac{X_H-a_0}{M}\right\rfloor,\qquad
|MJ_H-X_H|<M.
$$

当 $X_H\ge2M$ 时，$MJ_H\ge X_H/2$，得 $m_H$ 的下界。原 $L_{X_H}$ 对块内全部 $X_H$ 个整数求和，每项的模数恰为 $q_H$、半径至少为 $r_H$，得其下界。又

$$
\sum_{X_H<n\le2X_H}\nu(E_n)\ge m_H\longrightarrow\infty,
$$

故非负的一阶级数发散，并有 (21.5)。最后 $4r_H^2\le1$ 最终成立，故 $K_H=m_H/(4r_H^2)\to\infty$，特别地可统一删去有限个阶段以保证 $K_H\ge1$。$\square$

**定理 21.3（原好阶段的准确联合能量）。** 对定义 21.1 的阶段，令 $e(t)=e^{2\pi it}$，并置

$$
\begin{gathered}
f_r(z)=\mathbf1_{\{\|z_1\|_{\mathbb T}<r,\ \|z_2\|_{\mathbb T}<r\}},\qquad
\widehat f_r(k)=\prod_{j=1}^2
\begin{cases}\dfrac{\sin(2\pi k_jr)}{\pi k_j},&k_j\ne0,\\2r,&k_j=0,\end{cases}\\
D_b(t)=\sum_{\ell=0}^{b-1}e(\ell t)\quad(b\in\mathbb Z_{\ge0}),\qquad D_0=0.
\end{gathered}
$$

则保留真实 $M$ 与 floor 分配的能量恰为

$$
\mathcal E_H=\sum_{k\in\mathbb Z^2}|\widehat f_{r_H}(k)|^2
\left[(1-\tau_H)|D_{a_H}(q_Hk\cdot\alpha)|^2
 +\tau_H|D_{a_H+1}(q_Hk\cdot\alpha)|^2\right].
\tag{21.7}
$$

特别地，若 $\mathcal E_H^{\ne0}$ 表示此和的非零频率部分，则

$$
\frac{\mathcal E_H}{m_H^2}
 =1+\frac{\tau_H(1-\tau_H)}{K_H^2}
    +\frac{\mathcal E_H^{\ne0}}{m_H^2},\qquad
0\le\frac{\tau_H(1-\tau_H)}{K_H^2}\le\frac1{4K_H^2}.
\tag{21.8}
$$

同一能量也有准确的有限差形式。令

$$
w_{H,j}=(1-\tau_H)(a_H-j)_++\tau_H(a_H+1-j)_+,
\qquad x_+=\max(x,0).
$$

则

$$
\mathcal E_H=m_H+2\sum_{j=1}^{\lceil K_H\rceil-1}w_{H,j}
 \prod_{i=1}^2(2r_H-\|jq_H\alpha_i\|_{\mathbb T})_+.
\tag{21.9}
$$

空和取零；有限端和两个实端始终共用 $jq_H$，不拆成两条分别最优的轨道。

**证明。** 固定 $u$ 后，有限端合格的整数恰为
$n_0(u)+q_H\ell$，$0\le\ell<N_H(u)$。最小项 $n_0(u)$ 只依赖 $u\bmod q_H$，因而可测。对 $z$ 的 Fourier 系数为

$$
\widehat f_{r_H}(k)e(-n_0(u)k\cdot\alpha)
 D_{N_H(u)}(-q_Hk\cdot\alpha).
$$

对这个有限和使用经典 $L^2(\mathbb T^2)$ Parseval，取模平方后起始项的相位才消失；$|D_b(-t)|=|D_b(t)|$。再对 $u$ 积分，以 (21.6) 分配 $N_H$，并用非负项的 Tonelli 换序，即得 (21.7)。零频率给出

$$
(4r_H^2)^2\bigl((1-\tau_H)a_H^2+\tau_H(a_H+1)^2\bigr)
 =(4r_H^2)^2\bigl(K_H^2+\tau_H(1-\tau_H)\bigr),
$$

故得 (21.8)。准确实空间展开中对角项的积分是 $m_H$；给定正差指标 $j$，一条长度 $N$ 的纤维有 $(N-j)_+$ 对正向项。两半径相同且 $r_H<1/4$，故 (20.7) 的交长为 $(2r_H-\|jq_H\alpha_i\|_{\mathbb T})_+$。对 $N_H$ 按 (21.6) 平均，再计入反向项，便得 (21.9)。Parseval 和弧长交公式在此只是原联合能量推导的中间输入。$\square$

**定理 21.4（原单阶段能量、覆盖与对偶格的定量对应）。** 固定 $\alpha$ 的一个实提升，定义欧氏满秩格

$$
\begin{gathered}
\Lambda_H=\left\{\left(\frac\ell{K_H},
 \frac{\ell q_H\alpha-b}{r_H}\right):\ell\in\mathbb Z,\ b\in\mathbb Z^2\right\},\qquad
\det\Lambda_H=\frac1{K_Hr_H^2},\\
\Lambda_H^*=\{(K_H(a-q_Hk\cdot\alpha),r_Hk):a\in\mathbb Z,\ k\in\mathbb Z^2\},\\
\sigma_H=\lambda_1(\Lambda_H^*)
 =\min\left\{K_H,\ \min_{k\in\mathbb Z^2\setminus\{0\}}
 \sqrt{K_H^2\|q_Hk\cdot\alpha\|_{\mathbb T}^2+r_H^2\|k\|_2^2}\right\}.
\end{gathered}
\tag{21.10}
$$

该格就是 (19.7) 在尺度 $X'=q_HK_H=MJ_H$ 下的格；这是计数坐标尺度，不改变原整数、事件或地方精度。令

$$
C(\delta)=\frac{(1+3/\delta)(2+3/\delta)^2}{4},\qquad
D=2(1+\sqrt2).
$$

每个阶段均满足下列定量界：

$$
\begin{gathered}
\sigma_H\ge\delta>0\quad\Longrightarrow\quad
 V_H(u,z)\le C(\delta)m_H\ \text{对全部 }(u,z)\in Y,\\
\sigma_H\ge\delta>0\quad\Longrightarrow\quad
 \frac{\mathcal E_H}{m_H^2}\le C(\delta),\qquad
 \nu(B_H)\ge\frac1{C(\delta)},\\
\frac{m_H^2}{\mathcal E_H}\le\nu(B_H)
 \le\min\{1,D\sigma_H\}.
\end{gathered}
\tag{21.11}
$$

因而对任意无界的所选阶段族 $\mathcal H\subseteq\mathcal H_-$，有准确的统一界等价

$$
\inf_{H\in\mathcal H}\sigma_H>0
\quad\Longleftrightarrow\quad
\sup_{H\in\mathcal H}\frac{\mathcal E_H}{m_H^2}<\infty
\quad\Longleftrightarrow\quad
\inf_{H\in\mathcal H}\nu(B_H)>0.
\tag{21.12}
$$

这里均在定义 21.1 的充分大尾部取上下确界。若能量比统一不超过 $C$，则 $\sigma_H\ge1/(DC)$；若覆盖统一至少为 $b>0$，则 $\sigma_H\ge b/D$。

**证明（对偶非退化给出逐点计数上界）。** 由格的三条基向量计算行列式，再解与每条基的整数配对条件，得到 (21.10) 的对偶。$k=0$ 的最短非零向量长为 $K_H$；$k\ne0$ 时选最邻近的整数 $a$，即得所列最短长度。对偶格离散且满秩，所以最小值取得。

复用 Banaszczyk，*New bounds in some transference theorems in the geometry of numbers*，Math. Ann. 296，625–635，[DOI:10.1007/BF01445125](https://doi.org/10.1007/BF01445125)，[原文](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0296/LOG_0038.pdf)，印刷页 632 的 Theorem (2.2)：$\lambda_1(L)\mu_{\mathrm{cov}}(L^*)\le n/2$。原文页 625–626 的对偶是整数内积对偶，长度及覆盖半径均取欧氏约定，不要求协体积为 $1$。应用于 $L=\Lambda_H^*$、$n=3$，若 $\sigma_H\ge\delta$，则

$$
\mu_{\mathrm{cov}}(\Lambda_H)\le R_\delta:=\frac3{2\delta}.
$$

固定 $u,z$，由上一证明把合格整数自最小项 $n_0(u)$ 起编号。每个命中对应于平移格

$$
\left(0,\frac{n_0(u)\alpha-z}{r_H}\right)+\Lambda_H
$$

中第一坐标为 $\ell/K_H$、后两坐标在 $(-1,1)^2$ 的唯一格点；唯一性来自 $2r_H<1$。又

$$
N_H(u)-1\le\lceil K_H\rceil-1\le K_H,
$$

故所有这些点都在闭棱柱 $Q=[0,1]\times[-1,1]^2$ 内。这里只作上包，允许 $Q$ 包含额外格点。

取这些命中格点周围的闭 Voronoi 胞。每胞体积为 $\det\Lambda_H$，胞间交叠只在可数个平分超平面上，体积为零；这些胞的体积等于基本域体积的积分论证见 (19.13)。每胞距中心至多 $R_\delta$，所以选中胞的并包含于
$[-R_\delta,1+R_\delta]\times[-1-R_\delta,1+R_\delta]^2$。因此

$$
\frac{V_H(u,z)}{K_Hr_H^2}
 \le(1+2R_\delta)(2+2R_\delta)^2,
$$

即为逐点上界。这个上包论证对任意 $R_\delta>0$ 成立，不用 §19 为双边误差所加的 $R\le1$。严格盒边、闭胞边及真实 floor 初项均已包含其中。乘以非负 $V_H$ 并积分，得 $\mathcal E_H\le C(\delta)m_H^2$。

**证明（短对偶向量给出联合覆盖的窄带上界）。** 任取非零 $k\in\mathbb Z^2$，置

$$
\varepsilon=\|q_Hk\cdot\alpha\|_{\mathbb T},\qquad
W_H(k)=r_H\|k\|_1+(\lceil K_H\rceil-1)\varepsilon.
$$

在每个固定 $u$ 的纤维中，若 $z$ 属于某个中心 $n_0(u)\alpha+\ell q_H\alpha$ 的半径 $r_H$ 盒，则圆 character $\chi_k(z)=k\cdot z\pmod1$ 与该中心的 character 距离小于 $r_H\|k\|_1$。选 $q_Hk\cdot\alpha$ 的最短带符号实提升，其绝对值为 $\varepsilon$；所有 $0\le\ell<N_H(u)$ 的投影中心与首中心的圆距离均不超过 $(\lceil K_H\rceil-1)\varepsilon$。故该纤维的 $B_H$ 包含于一条圆弧的逆像，弧的半径为 $W_H(k)$，弧长至多 $\min(1,2W_H(k))$。

非零整数 character 将 $\mathbb T^2$ 的 Haar 推为圆 Haar：其为满射紧群同态，因为至少一个非零坐标的整数乘法在圆上满射；Haar 推前仍是归一化平移不变测度。这不要求 $k$ 原始。对 $u$ 再积分，得到

$$
\nu(B_H)\le\min\{1,2W_H(k)\}\qquad(k\ne0).
\tag{21.13}
$$

若 $\sigma_H<K_H$，取得最短向量的 $k$ 必非零，并满足

$$
r_H\|k\|_2\le\sigma_H,\qquad
K_H\varepsilon\le\sigma_H,\qquad
W_H(k)\le(\sqrt2+1)\sigma_H.
$$

于是 (21.13) 给出 (21.11) 的覆盖上界。若 $\sigma_H=K_H\ge1$，该上界由 $\nu(B_H)\le1$ 平凡成立，所以两种情况均已包括。

最后，经典 Cauchy–Schwarz 只在 $V_H$ 的支集上使用：

$$
m_H^2=\left(\int_{B_H}V_H\,d\nu\right)^2
 \le\nu(B_H)\mathcal E_H.
$$

结合已经得到的两个几何方向，即得全部 (21.11)–(21.12) 及所列常数。Voronoi 铺砌、覆盖转移与支集二阶矩均是经典中间方法；新增的综合关系是它们在原临界真实周期、准确纤维分配及联合轨道上的定量闭合（repo-derived），不是新的一般转移或二阶矩定理。$\square$

**定理 21.5（原好阶段的满测充分条件及未证估计的准确位置）。** 若存在 $\delta>0$ 及无界的 $\mathcal H\subseteq\mathcal H_-$，使 $\sigma_H\ge\delta$ 对所有 $H\in\mathcal H$ 成立，则 $\nu(R)=1$。等价地，可用 (21.12) 中任一统一界作为这一所选阶段族的假设。这里的非退化假设准确等于

$$
K_H\ge\delta,\qquad
K_H^2\|q_Hk\cdot\alpha\|_{\mathbb T}^2+r_H^2\|k\|_2^2\ge\delta^2
\quad\text{对每个 }k\in\mathbb Z^2\setminus\{0\},\ H\in\mathcal H.
\tag{21.14}
$$

因 $K_H\to\infty$，尾部只需检查非零 $\|k\|_2<\delta/r_H$ 的频率。条件 (21.14) 对原实际 CM 数据在无穷多个这些好阶段上是否成立，仍是未证估计；(21.7) 的实际能量比统一上界亦未证。

若沿某个无界阶段子族有更强的 $\mathcal E_H^{\ne0}=o(m_H^2)$，则 $\nu(B_H)\to1$。反之，若沿某子族 $\sigma_H\to0$，则 $\nu(B_H)\to0$ 且 $\mathcal E_H/m_H^2\to\infty$。这里没有证明实际非塌缩子族或实际共振子族的存在；(21.12) 只刻画所选阶段族的统一界，不把它作为 $\nu(R)=1$ 的必要条件，也不把阶段覆盖趋零作为 limsup 零测的充分条件。

**证明（只需正测子集包含于原 $R$）。** 由定理 21.4，每个 $H\in\mathcal H$ 都有 $\nu(B_H)\ge b:=1/C(\delta)>0$。对每个整数 $K$，无界性保证尾并集 $\bigcup_{H\in\mathcal H,H\ge K}B_H$ 含至少一个这样的事件，故其测度至少为 $b$。这些尾并集递减，由概率测度的上连续性，

$$
\nu\!\left(\limsup_{\substack{H\to\infty\\H\in\mathcal H}}B_H\right)\ge b.
$$

若目标属于该 limsup，则它在无穷多个 $X_H\to\infty$ 的块中各有原成功整数；这些整数无界，因 $F_{n,H}\subseteq E_n$，所以

$$
\limsup_{\substack{H\to\infty\\H\in\mathcal H}}B_H\subseteq R.
\tag{21.15}
$$

于是 $\nu(R)>0$，只对原 $R$ 使用定理 20.2 的零一律，得到 $\nu(R)=1$。这不要求 $B_H$ 的 limsup 本身平移不变，不使用跨阶段独立或跨阶段二阶矩。

若非零能量为 $o(m_H^2)$，由 (21.8) 及 $K_H\to\infty$ 得 $\mathcal E_H/m_H^2\to1$，再由 (21.11) 得覆盖趋于 $1$。若 $\sigma_H\to0$，同式给出覆盖趋零和能量比发散。这些单阶段极限本身不估计尾并集的上界，因而此处不从中推出任一 limsup 零测结论。

相邻文献 Beresnevich–Datta–Ghosh–Ward，*Rectangular shrinking targets for $\mathbb Z^m$ actions on tori: well and badly approximable systems*，[DOI:10.4064/aa231108-27-8](https://doi.org/10.4064/aa231108-27-8)，[accepted 原文](https://eprints.whiterose.ac.uk/id/eprint/216540/1/RECTANGULAR_SHRINKING_TARGETS.pdf)，Theorem 1.3（印刷页 2–3）与 Theorem 2.4（印刷页 4）均以相应加权非奇异性为前提；§2 的 $S$ 是一个固定有限地方集。本题要求随 $H$ 增加全部 $p\le H$，其共同整数周期也随阶段改变，通向该文固定 $S$ 定理的适用桥并未建立。这里不直接套用该文结论，也不假定原实际 $\alpha$ badly approximable。

用白话说，临界时原钥匙能打开的目标总量确实发散，并在一列原实际阶段中具有很大的平均命中数。但同一批钥匙可能在某个联合方向上重复覆盖窄带；准确能量、正比例覆盖与三维对偶不出现短向量，恰好是这批钥匙上的三个定量接口。只要无穷多这样的原好阶段覆盖固定正比例，已有零一律便将原无限命中集合提升到满测；仍缺的是实际数据在这些阶段上的统一估计。上述结论不主张临界满测、全序列移动质量发散、最优性、完整 $\mathbb Z/\mathbb Q$ 定义或物理起源。$\square$

## 追加锚（本行以下为增补区）

## 22. 保留原有限端的方向度量比较、全目标计数与固定点边界

**定义 22.1（只改变实方向的比较族）。** 固定定义 21.1 的临界参数与原实际数据，保留 $M,a_0,A,Y,\nu$、全部有限地方的原过滤及其目标 $\eta(u)$，并保留原来的 $\mathcal H_-,X_H,q_H,J_H,K_H,r_H,m_H$。以下均在 §21 的充分大阶段尾部取 $H\in\mathcal H_-$。仅以参数 $\omega\in\mathbb T^2$ 替换实端方向 $\alpha$。具体地，沿用原 $q_n=q(h(n),h(n);M)$，定义

$$
\begin{aligned}
\mathcal B_r(w)&=\{z\in\mathbb T^2:\|w_j-z_j\|_{\mathbb T}<r\ (j=1,2)\},\\
E_n(\omega)&=
\begin{cases}
(n+q_n\widehat{\mathbb Z})\times\mathcal B_{\rho_n}(n\omega),&n\in A,\\
\varnothing,&n\notin A,
\end{cases}\\
F_{n,H}(\omega)&=
\begin{cases}
(n+q_H\widehat{\mathbb Z})\times\mathcal B_{r_H}(n\omega),&n\in A,\\
\varnothing,&n\notin A,
\end{cases}
\quad(X_H<n\le2X_H),\\
V_H(u,z;\omega)&=\sum_{X_H<n\le2X_H}\mathbf1_{F_{n,H}(\omega)}(u,z),
\qquad R(\omega)=\limsup_{n\to\infty}E_n(\omega).
\end{aligned}
$$

阶段计数的有限端仍准确要求同一个整数 $n\in A$ 且 $u\equiv n\pmod{q_H}$。再置

$$
\begin{gathered}
\Lambda_H(\omega)=\left\{\left(\frac\ell{K_H},
 \frac{\ell q_H\omega-b}{r_H}\right):\ell\in\mathbb Z,\ b\in\mathbb Z^2\right\},\\
\sigma_H(\omega)=\min\left\{K_H,
 \min_{k\in\mathbb Z^2\setminus\{0\}}
 \sqrt{K_H^2\|q_Hk\cdot\omega\|_{\mathbb T}^2+r_H^2\|k\|_2^2}\right\}.
\end{gathered}
\tag{22.1}
$$

任取实提升得到同一格；其对偶为 (21.10) 中将 $\alpha$ 换成 $\omega$ 的格，故 $\sigma_H(\omega)=\lambda_1(\Lambda_H(\omega)^*)>0$。归一化方向 Haar 概率记为 $m_{\mathrm{dir}}$，与目标概率 $\nu$ 区分。对每个方向，仍有

$$
\int_Y V_H(\cdot;\omega)\,d\nu=m_H=4K_Hr_H^2,\qquad
K_Hr_H^2\ge c e^{2H}H^{-4\gamma},\qquad K_H\to\infty,\quad r_H\to0
\tag{22.2}
$$

其中 $c>0$ 只依赖固定数据，后面可统一缩小它。第一式由每个实窗的面积得到，后三项直接复用定理 21.2。这是确定性有限端上的数学参数比较；$\omega=\alpha$ 才是原实端，其他方向不被解释成原曲线点、实际制备权限或随机物理假设。

**定理 22.2（准确有限纤维与严格窗的一致体积夹逼）。** 固定一个阶段和一个方向，简记 $K=K_H,r=r_H,\sigma=\sigma_H(\omega),m=m_H$。对每个 $u\in C_M$，令 $N=N_H(u)$ 为定理 21.2 的真实整数项数，$L=N/K$。则

$$
N\in\{\lfloor K\rfloor,\lceil K\rceil\},\qquad |L-1|\le K^{-1}.
\tag{22.3}
$$

取 $t=3/(2\sigma)$。对全部 $(u,z)\in Y$，包括实窗边界上存在格点的目标，均有

$$
(L-2t)_+(1-t)_+^2
\le\frac{V_H(u,z;\omega)}m
\le(L+2t)(1+t)^2.
\tag{22.4}
$$

特别地，当 $\sigma\ge3$ 时，

$$
\sup_{(u,z)\in Y}\left|\frac{V_H(u,z;\omega)}{m_H}-1\right|
\le\frac{21}{2\sigma_H(\omega)}+\frac9{4K_H}.
\tag{22.5}
$$

**证明（真实初项与半开时间盒）。** 因 $M\mid q_H$ 且 $u\in C_M$，允许整数构成模 $q_H$ 的一个类，已包含 $n\equiv a_0\pmod M$。令 $n_*(u)$ 为此类中不超过 $X_H$ 的最后一个整数。块内允许项准确为

$$
n_*(u)+\ell q_H\quad(\ell=1,\ldots,N),\qquad
Q=(0,L]\times(-1,1)^2,\qquad
\xi=\left(0,\frac{n_*(u)\omega-z}{r}\right).
\tag{22.6}
$$

§21 的连续 $J_H$ 项在模 $q_H/M$ 各类中的分配逐类给出 (22.3)，并非只给出几乎处处的项数。第一坐标 $\ell/K\in(0,N/K]$ 恰好选出 $\ell=1,\ldots,N$，因此

$$
V_H(u,z;\omega)=\#\bigl((\xi+\Lambda_H(\omega))\cap Q\bigr).
\tag{22.7}
$$

后两坐标准确表示严格实窗；$2r<1$ 保证每个整数至多对应一个 $b\in\mathbb Z^2$。这保留了 $N_H(u)$、窗前初项及两个时间端点，没有用 $K$ 或 $X_H/q_H$ 代替整数项数。

**证明（严格内缩与常数）。** 复用定理 21.4 所引 Banaszczyk 的欧氏覆盖转移，$\mu_{\mathrm{cov}}(\Lambda_H(\omega))\le t$。以 (22.7) 选中点为中心，取闭 Voronoi 胞的有限并 $U$。每胞体积为 $\det\Lambda_H(\omega)=1/(Kr^2)$；不同胞的重叠只在可数个平分超平面上，所以

$$
\operatorname{vol}(U)=\frac{V_H(u,z;\omega)}{Kr^2}.
$$

每个选中胞都在其中心的闭 $t$ 球中，故 $U$ 包含于
$[-t,L+t]\times[-1-t,1+t]^2$。若 $L>2t$ 且 $t<1$，严格内缩盒

$$
Q^-=(t,L-t)\times(-1+t,1-t)^2
$$

中的任一点到任一最近格点的距离至多 $t$，其最近格点因严格内缩而在 $(0,L)\times(-1,1)^2$ 中，必被选中；故 $Q^-\subseteq U$。其他情形取内缩盒为空。两个包体积除以 $4$，用 $m=4Kr^2$ 即得 (22.4)。即使某些格点恰在严格实窗的边上，这个包含关系仍逐点成立；体积零只用于胞间重叠，未用于排除窗边格点。

若 $\sigma\ge3$，则 $0<t\le1/2$。用 (22.3) 展开上包，有

$$
\begin{aligned}
(L+2t)(1+t)^2-1
&\le4t+5t^2+2t^3+\frac{(1+t)^2}{K}
 \le7t+\frac9{4K},\\
1-(L-2t)_+(1-t)^2
&\le1-(1-K^{-1}-2t)(1-t)^2\\
&=4t-5t^2+2t^3+\frac{(1-t)^2}{K}
 \le4t+\frac1K.
\end{aligned}
$$

这里第二个估计即使 $1-K^{-1}-2t<0$ 仍成立，因为取正部只增大下包。代入 $7t=21/(2\sigma)$ 得 (22.5)。证明对每个平移和每个允许项数给出同一个界，故可直接对不可数的全部目标取上确界，无须对目标取测度交集。$\square$

**定理 22.3（方向坏集预算与全部好阶段的全目标计数）。** 对任一阶段和 $0<d\le K_H$，置 $D=d/r_H$。保留全部非零整数频率，包括非原始频率，将 $\pm k$ 成对计数，有

$$
\begin{aligned}
m_{\mathrm{dir}}\{\omega:\sigma_H(\omega)<d\}
&\le\frac{2d}{K_H}\,2\lfloor D\rfloor(\lfloor D\rfloor+1),\\
D\ge1\quad&\Longrightarrow\quad
m_{\mathrm{dir}}\{\omega:\sigma_H(\omega)<d\}
 \le\frac{8d^3}{K_Hr_H^2}.
\end{aligned}
\tag{22.8}
$$

存在一个 $m_{\mathrm{dir}}$-全测集合 $\Omega\subseteq\mathbb T^2$，使对每个 $\omega\in\Omega$ 和每个实数

$$
b>b_0:=\frac{4\gamma+1}{3},\qquad d_H(b)=e^{2H/3}H^{-b},
\tag{22.9}
$$

沿所有充分大的 $H\in\mathcal H_-$ 都有

$$
\begin{gathered}
\sigma_H(\omega)\ge d_H(b)\longrightarrow\infty,\\
\sup_{(u,z)\in Y}\left|\frac{V_H(u,z;\omega)}{m_H}-1\right|
 =O_{\omega,b}\!\left(e^{-2H/3}H^b\right).
\end{gathered}
\tag{22.10}
$$

这里阶段阈值可依赖方向与 $b$，不能依赖目标。特别地，对每个这样的方向，在全部充分大的原好阶段，每个目标均有至少一个允许整数，在该整数上同时满足有限端与比较实端；整数可依赖目标。因此 $R(\omega)=Y$，这是逐目标的集合等式。

**证明（Haar 条带与非原始频率）。** 若 $\sigma_H(\omega)<d\le K_H$，则最短向量不能来自 $k=0$，必有

$$
0<\|k\|_2<D,\qquad \|q_Hk\cdot\omega\|_{\mathbb T}<d/K_H.
\tag{22.11}
$$

对每个非零 $k$，$\omega\mapsto q_Hk\cdot\omega\pmod1$ 是到圆的满射紧群同态：任一非零坐标的整数乘法已在圆上满射。因此它将归一化 Haar 推为圆 Haar，无须 $k$ 原始，条带概率恰为 $\min(1,2d/K_H)$。$k$ 与 $-k$ 给出相同条带。所有可能的 $k$ 在 $[-\lfloor D\rfloor,\lfloor D\rfloor]^2\setminus\{0\}$ 内，该方形中的 $\pm$ 对数为 $2\lfloor D\rfloor(\lfloor D\rfloor+1)$。对这些对作并集界得到第一式；当 $D\ge1$ 时，该对数至多 $4D^2$，即得第二式。不删非原始频率，也不要求不同频率独立。

**证明（可求和阈值与全方向集合）。** 固定 $b>b_0$，记 $\eta_b=3b-4\gamma-1>0$。由 (22.2) 及 $r_H<1$，

$$
\frac{d_H(b)}{K_H}\le c^{-1}e^{-4H/3}H^{4\gamma-b}\to0,
\qquad \frac{d_H(b)}{r_H}\to\infty.
$$

所以 (22.8) 的两项适用条件最终均满足，且

$$
\begin{gathered}
m_{\mathrm{dir}}\{\sigma_H<d_H(b)\}
\le\frac8c H^{4\gamma-3b}=\frac8c H^{-1-\eta_b},\\
m_{\mathrm{dir}}\!\left(\bigcup_{\substack{H\in\mathcal H_-\\H\ge J}}
 \{\sigma_H<d_H(b)\}\right)
\le\frac{8}{c\eta_b}(J-1)^{-\eta_b}\quad(J\text{ 充分大}).
\end{gathered}
\tag{22.12}
$$

第二式将阶段子集的和上包为全体整数的和，再用递减函数的积分界。尾界趋零，故坏阶段无限发生的方向集为零测；这正是经典收敛 Borel–Cantelli 的方向，不需阶段独立。对可数个 $b_j=b_0+1/j$ 的全测集合取交，得同一 $\Omega$。任意 $b>b_0$ 可取 $j$ 使 $b_j<b$，于是 $d_H(b_j)\ge d_H(b)$，得到 (22.10) 的第一式对所有这些 $b$ 成立。

再由 $K_H^{-1}\le c^{-1}e^{-2H}H^{4\gamma}=O(e^{-2H/3}H^b)$，将第一式代入 (22.5)，即得第二式。$m_H\to\infty$ 且统一相对误差趋零，故最终对全部 $(u,z)$ 同时有 $V_H(u,z;\omega)\ge m_H/2\ge1$。又 $F_{n,H}(\omega)\subseteq E_n(\omega)$，且 $X_H\to\infty$，每个目标遂有无界的成功整数，得到 $R(\omega)=Y$。此处不使用原固定 $\alpha$ 的零一律或无理独立性。阈值 $b=b_0$ 仅给 $H^{-1}$ 上包，裸指数端点 $d_H=e^{2H/3}$ 仅给 $H^{4\gamma}$ 上包；两者均不由这项收敛估计认证，也不据此判为失败。$\square$

**定理 22.4（全测比较的残余边界与原 CM 点的保证函数）。** 对同一固定有限端和同一好阶段族，集合

$$
\mathcal G=\bigcap_{j,L\ge1}\ \bigcup_{\substack{H\in\mathcal H_-\\H\ge L}}
 \{\omega:\sigma_H(\omega)<1/j\}
\tag{22.13}
$$

是稠密 $G_\delta$、Haar 零测，且恰有

$$
\omega\in\mathcal G\quad\Longleftrightarrow\quad
\liminf_{\substack{H\to\infty\\H\in\mathcal H_-}}\sigma_H(\omega)=0.
\tag{22.14}
$$

它与 $1,\omega_1,\omega_2$ 有理线性无关的方向集之交仍是稠密 $G_\delta$。这只刻画任意晚阶段中存在短对偶向量，不否定同一方向另有无穷多个 $\sigma_H\ge\delta>0$ 的阶段。

对原固定向量 $\alpha$，令 $A>0,\mu>0$ 是 (17.5) 已有的有限型常数。该下界给出以下明确保证函数，而非 $\sigma_H(\alpha)$ 的等式：

$$
\begin{gathered}
\sigma_H(\alpha)\ge g_H:=\min\left\{K_H,
 \left(\frac{AK_Hr_H^\mu}{q_H^\mu}\right)^{1/(\mu+1)}\right\},\\
g_H=X_H^{\Delta_{\mathrm{geom}}/(\mu+1)+o(1)}\longrightarrow0,\\
\Delta_{\mathrm{geom}}=1-(\mu+1)c_0^2-\mu\beta
 =-\mu c_0^2-(\mu-2)\beta\le-2c_0^2<0.
\end{gathered}
\tag{22.15}
$$

这里的明确值以原有固定 $A,\mu$ 表示，不提供它们的数值。保证函数趋零既不证明实际 $\sigma_H(\alpha)\to0$，也不证明有限型信息在逻辑上绝不够；它只表明这一既有幂下界的直接代入没有支付原临界阶段的统一正下界。

**证明（类别与测度对照）。** 对每个阶段，(22.1) 将 $\{\sigma_H<1/j\}$ 写成连续圆 character 的严格不等式集的并，因而它是开集；$k=0$ 的常数项只会贡献空集或全空间。若 $\omega$ 有共同有理分母 $a\ge1$，取 $k=(a,0)$，则 $q_Hk\cdot\omega\in\mathbb Z$，故 $\sigma_H(\omega)\le ar_H\to0$。$\mathcal H_-$ 无界，所以 (22.13) 中每个尾并集均含全部有理方向，是开稠密集。经典 Baire 定理给出其可数交稠密，定义直接给出 (22.14)。定理 22.3 的全测集合上 $\sigma_H\to\infty$，与 $\mathcal G$ 不交，故 $\mathcal G$ 零测。

对每个 $k\ne0$，闭集 $\{\omega:k\cdot\omega=0\pmod1\}$ 无内点：沿一个非零坐标任意小地移动即可离开它。其开稠密补集对全部非零整数 $k$ 的可数交，正是 $1,\omega_1,\omega_2$ 有理线性无关的方向集。再用 Baire 即得交集声明；这没有赋予这些残余方向任何有限型保证，也未定位原 $\alpha$。

**证明（原有限型保证与未证关系）。** 对原对偶的任一 $k\ne0$，令 $s=\|k\|_\infty\ge1$，向量长度记为 $v$。由 (17.5)，

$$
v\ge r_Hs,\qquad v\ge K_H\|q_Hk\cdot\alpha\|_{\mathbb T}
 \ge\frac{AK_H}{q_H^\mu s^\mu},\qquad
v^{\mu+1}\ge\frac{AK_Hr_H^\mu}{q_H^\mu}.
$$

$k=0$ 的非零向量长至少为 $K_H$，故得到 (22.15) 的第一式。§19 已用二维抽屉原理从同一 (17.5) 推出 $\mu\ge2$；定理 16.7、$\log X_H\sim H^2/c_0^2$ 和准确的 $MJ_H=X_H+O(M)$ 又给出

$$
q_H=X_H^{c_0^2+o(1)},\qquad
K_H=X_H^{1-c_0^2+o(1)},\qquad r_H=X_H^{-\beta+o(1)}.
$$

因此 (22.15) 中第二个候选项的指数为 $\Delta_{\mathrm{geom}}/(\mu+1)$。临界等式和 $\mu\ge2$ 使该指数严格负；该项趋零，而 $K_H\to\infty$，所以最小值最终取第二项，得到其余各式。这是 §19 保证下界在当前阶段的代入，作为与度量结论比较的中间步骤，不另称一般算术新定理。

沿用 §21 的充分路线，原固定点仍缺的关系是：证明某个 $\delta>0$ 及无界的 $\mathcal H\subseteq\mathcal H_-$ 满足

$$
K_H^2\|q_Hk\cdot\alpha\|_{\mathbb T}^2+r_H^2\|k\|_2^2\ge\delta^2
\quad(H\in\mathcal H,\ k\in\mathbb Z^2\setminus\{0\}).
\tag{22.16}
$$

这里只需频率 $0<\|k\|_2<\delta/r_H$，$K_H\ge\delta$ 最终自动成立。定理 21.5 已给出该关系到原 $\nu(R)=1$ 的充分接口；该关系仍只作为充分条件，不声称它是原满测的必要条件。方向全测不保证包含指定的 $\alpha$，残余零测也不保证排除它；本节既未证 $\alpha\in\Omega$，也未证 $\alpha\in\mathcal G$，更未判定实际非塌缩子族或实际共振子族。

文献范围如下。覆盖转移复用 §21 所引 Banaszczyk，*New bounds in some transference theorems in the geometry of numbers*，Math. Ann. 296，625–635，[原文 Theorem (2.2)，印刷页 632](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0296/LOG_0038.pdf)，采用该文的欧氏整数内积对偶版本；Haar 推前、收敛 Borel–Cantelli 与 Baire 是经典中间输入（literature-attested），不作为新的一般理论成果。相邻来源 Nesharim–Rühr–Shi，*Metric Diophantine approximation with congruence conditions*，[arXiv:1902.01381v2 原文](https://arxiv.org/pdf/1902.01381v2)，印刷页 1 的 Theorem 1.2 先固定模数向量 $N$ 和余类向量 $v$；页 2 的 Theorems 1.3–1.4 固定有限多个同余条件，页 3 的 Dani 同余商亦固定 $N$。即使对全部固定模数作可数全测交，也不从该文的无限近似量词得到这里指定增长 $q_H$、指定阶段和窗口上的一致计数；该文只用于标明相邻适用边界，不充当 (22.10) 的直接输入。本节的新增综合是原实际共同模数、临界质量预算、准确整数纤维与方向坏集估计的联结（repo-derived），不主张一般度量逼近、格转移或类别定理的原创性。

用白话说，保留同一批有限端钥匙、同一把钥匙必须同时满足全部条件，只比较它们在两个实圆上前进的方向。坏方向是某个整数联合方向上的窄带，单条窄带的 Haar 宽度与原模数无关，而可能窄带的条数由实窗尺度控制；原好阶段的大质量使这些坏方向的总预算可求和。因此几乎所有比较方向最终在每个好阶段都对所有目标准确均匀计数。但稠密的零测方向仍可在任意晚的某些阶段发生共振，这并不排除它们另有无穷多非塌缩阶段。原 CM 向量是一根指定方向；全测比较和退化的保证下界都没有决定它是否满足 (22.16)，原临界 $R$ 的结论仍未解决。$\square$

## 追加锚（本行以下为增补区）
## 23. 原临界过滤下有限型实方向的完整零测反模型

**定理 23.1（有限型仍容许完整缩靶塌缩）。** 任取 $0<\beta<1/2$、$\gamma\ge0$，令 $c_0^2=1-2\beta$。在定义 22.1 对应的比较族中，保留全部原有限地方、过滤、共同模数、目标空间及原 $h,\rho$。对每个

$$
\mu>\beta^{-1}(\beta^{-1}-1)
\tag{23.1}
$$

都存在实方向 $\omega\in\mathbb T^2$ 及常数 $c_\omega>0$，使 $1,\omega_1,\omega_2$ 有理线性无关（坐标取任一实提升），且

$$
\begin{gathered}
\|k\cdot\omega\|_{\mathbb T}\ge c_\omega\|k\|_\infty^{-\mu}
\quad(0\ne k\in\mathbb Z^2),\\
\nu(R(\omega))=0,\qquad R(\omega)\text{ 是 }Y\text{ 中的稠密 }G_\delta,\\
\sum_{n\ge1}\nu(E_n(\omega))=\infty,\qquad \limsup_{X\to\infty}L_X=\infty.
\end{gathered}
\tag{23.2}
$$

此外，沿全部充分大的真实好阶段 $H\in\mathcal H_-$，有 $\sigma_H(\omega)\to0$。零测结论针对完整的原比较事件序列 $E_n(\omega)$，不是只针对阶段子事件的 limsup。

**证明（严格指数与有限型下界）。** 由 (23.1)，可以依次选取

$$
\beta^{-1}<w<\frac{1+\sqrt{1+4\mu}}2,\qquad
v=w(w-1)<\mu,\qquad
\beta^{-1}<\nu_0<w,\qquad \nu_0^{-1}<a<\beta.
\tag{23.3}
$$

使用 Laurent，*Exponents of Diophantine approximation in dimension two*，[arXiv:math/0611352v1](https://arxiv.org/pdf/math/0611352v1)，Corollary 1（印刷页 3–4）的逆向存在结论：因 $w>2$ 且 $v=w(w-1)$，存在 $\Theta\in\mathbb R^2$，使 $1,\Theta_1,\Theta_2$ 有理线性无关，其行向量 ordinary 指标恰为 $v$，uniform 指标恰为 $w$。取 $\omega=\Theta\pmod{\mathbb Z^2}$。这里用的是线性形式指标，非同时逼近指标。

该文页 1–2 的定义采用整数三元组 $(k_1,k_2,b)\ne0$，条件为

$$
|k\cdot\Theta+b|\le H^{-t},\qquad
\max(|k_1|,|k_2|,|b|)\le H.
\tag{23.4}
$$

ordinary 取此系统在无穷多个整数 $H$ 可解的指数上确界，uniform 则要求每个充分大整数 $H$ 均可解。以下只用严格的 $\nu_0<w$ 和 $\mu>v$，不假定任一上确界端点被达到。

为转换到圆距离与二维范数，置 $D=\max(1,|\Theta_1|+|\Theta_2|+1)$。给定 $s=\|k\|_\infty\ge1$，取最邻近 $-k\cdot\Theta$ 的整数 $b$，则三元组高度至多 $Ds$。令 $H=\lceil Ds\rceil\le(D+1)s$。因 $\mu>v$，(23.4) 在 $t=\mu$ 时对充分大的 $H$ 无非零解，故对充分大的 $s$，

$$
\|k\cdot\omega\|_{\mathbb T}>H^{-\mu}
\ge(D+1)^{-\mu}s^{-\mu}.
$$

剩余有限多个非零小频率的圆距离全为正，否则违背有理独立性。取这些距离乘 $s^\mu$ 的正最小值，再与 $(D+1)^{-\mu}$ 取最小，即得对全部非零频率成立的 $c_\omega>0$。这既处理有限初段，也没有把三元组高度直接等同于 $\|k\|_\infty$。

由 uniform 定义，对每个充分大的实数 $X$，以 $H=\lfloor X^a\rfloor$ 代入 (23.4)，可选一个 $k_X\in\mathbb Z^2$ 满足

$$
0<\|k_X\|_\infty\le X^a,\qquad
\|k_X\cdot\omega\|_{\mathbb T}\le C X^{-a\nu_0},\qquad C=2^{\nu_0}.
\tag{23.5}
$$

确实 $H\ge X^a/2$ 最终成立；而 $k_X=0$ 会使 $|b|<1$，迫使整个三元组为零。整数平移 $\Theta\mapsto\omega$ 不改圆距离，故此处不需假设换提升后仍保留同一个高度界。

**证明（覆盖每个完整 dyadic 块）。** 固定 $X=2^j$，在整个 $(X,2X]$ 只用同一个 $k_X$。若 $(u,z)\in E_n(\omega)$ 且 $X<n\le2X$，则圆距离的三角不等式和原半径的单调性给出

$$
\begin{aligned}
\|k_X\cdot z\|_{\mathbb T}
&\le n\|k_X\cdot\omega\|_{\mathbb T}
 +( |k_{X,1}|+|k_{X,2}|)\rho_n\\
&\le 2C X^{1-a\nu_0}+2X^a\rho(X)=:\delta_X.
\end{aligned}
\tag{23.6}
$$

于是全部有限条件仍由原事件承担，同时有上包

$$
\bigcup_{X<n\le2X}E_n(\omega)
\subseteq S_j:=C_M\times
 \{z\in\mathbb T^2:\|k_{2^j}\cdot z\|_{\mathbb T}\le\delta_{2^j}\}.
\tag{23.7}
$$

上包允许放宽有限端，却没有删掉任何原指标，包括阶段跳点两侧和不属于 $\mathcal H_-$ 的阶段。非零整数 character $z\mapsto k_{2^j}\cdot z$ 将两圆 Haar 推为圆 Haar，即使频率不原始亦然，故 $\nu(S_j)=\min(1,2\delta_{2^j})$。由原 $\rho(X)=(X+2)^{-\beta}(\log(X+2))^{-\gamma}$，有

$$
\delta_X\le 2C X^{-(a\nu_0-1)}+2X^{-(\beta-a)}(\log X)^{-\gamma},
\qquad \sum_{j\text{ 充分大}}\nu(S_j)<\infty.
\tag{23.8}
$$

两项指数均严格为正。完整整数尾被这些相邻 dyadic 块覆盖，因此

$$
\nu(R(\omega))\le
\nu\!\left(\bigcup_{n>2^J}E_n(\omega)\right)
\le\sum_{j\ge J}\nu(S_j)\longrightarrow0.
\tag{23.9}
$$

这是收敛 Borel–Cantelli 的尾并集估计，不需块间独立；尤其没有从 $\limsup B_H(\omega)\subseteq R(\omega)$ 反推 $R(\omega)$ 零测。

**证明（原质量与真实阶段）。** 对充分大的 $n$，
$\nu(E_n(\omega))=4M\mathbf1_A(n)\rho_n^2/q_n$，与方向无关。由 (22.2) 及 $F_{n,H}(\omega)\subseteq E_n(\omega)$，

$$
\sum_{X_H<n\le2X_H}\nu(E_n(\omega))\ge m_H\longrightarrow\infty.
$$

故完整一阶和仍发散；$L_X$ 没有方向参数，其无穷上极限直接沿用定理 21.2。若考察 (22.1) 的最短对偶长度，在每个真实 $X_H$ 使用 (23.5)，利用准确恒等式 $K_Hq_H=MJ_H$ 及 $|MJ_H-X_H|<M$，得到

$$
\begin{aligned}
\sigma_H(\omega)
&\le K_H\|q_Hk_{X_H}\cdot\omega\|_{\mathbb T}
       +r_H\|k_{X_H}\|_2\\
&\le C(X_H+M)X_H^{-a\nu_0}+\sqrt2\,r_H X_H^a
\longrightarrow0.
\end{aligned}
\tag{23.10}
$$

末项使用真实 $r_H=\rho(2X_H)$、$a<\beta$，首项使用 $a\nu_0>1$。这里没有将真实 $K_H$ 偷换成 $X_H/q_H$，也没有从另选尺度推断原阶段。

**证明（新方向的联合尾稠密）。** 任取 $Y$ 的非空基本开窗 $V=((b+d\widehat{\mathbb Z})\cap C_M)\times W$，其中 $d\ge1$，$W\subseteq\mathbb T^2$ 非空开。CRT 将其有限端整数条件写成一个共同类 $t\pmod\ell$，$\ell=\operatorname{lcm}(M,d)$。因 $1,\omega_1,\omega_2$ 有理线性无关，对每个 $k\ne0$ 都有 $\ell k\cdot\omega\notin\mathbb Z$；经典 Kronecker 定理遂给出 $(t+\ell m)\omega$ 的每条正尾在两圆中稠密。因此对每个 $N$ 存在同一个 $n>N$，满足 $n\equiv t\pmod\ell$ 且 $n\omega\in W$。

中心 $(n,n\omega)$ 同时属于 $V$ 和 $E_n(\omega)$：其有限端自身满足 $n\equiv n\pmod{q_n}$，且原半径逐项严格为正。所以每个 $\bigcup_{n>N}E_n(\omega)$ 都开且稠密；$Y$ 紧 Hausdorff，Baire 定理给出它们的交 $R(\omega)$ 稠密且为 $G_\delta$。这段论证核对了新方向和同一整数的联合尾，不调用只针对原 CM 点的定理 11.3。

本条是 Laurent 谱与本项目原半径、全部原有限过滤、临界一阶预算及全块窄带上包的新增综合（repo-derived）。谱定理、Kronecker、Haar 推前、收敛 Borel–Cantelli 和 Baire 均为经典中间输入（literature-attested），不另立一般新定理。相邻先例 Fayad，*Two remarks on the Shrinking Target Property*，[arXiv:math/0501205v1](https://arxiv.org/pdf/math/0501205v1)，Theorem 2.3（印刷页 4）第一项证明环面平移具有 MSTP 当且仅当方向为 constant type，其量词遍历所有递减半径；它不指定本项目的 $\rho_n$、增长模数和临界质量。该定理的非 MSTP 方向不能直接提供这里固定半径的反例，第二项与页 4–5 的构造还允许非单调或零半径。本条不主张一般有限型旋转的缩靶失败现象首次发现。

用白话说，有限型保证每个整数方向的共振不会小于某个统一幂，但仍允许足够强的多项式共振。在每一整块时间里，它把所有实目标窗压进同一条很窄的带；各块窄带的面积总和有限，逐时刻窗的质量却因重复覆盖仍然发散。稠密零测意味着每个开窗都有无限命中目标，而几乎每个目标只命中有限次，两者并不矛盾。

这些方向只替换实端，不是原曲线的新 CM 来源；本条没有认证原指定 $\alpha$ 的具体有限型常数或更小指数，也不主张 (23.1) 的门槛必要或其补范围不可构造。对原 CM 点，$\nu(R(\alpha))$ 仍未解决；若走 §21 的充分路线，其 CM 结构仍需支付原 $q_H$ 与 $\alpha$ 的联合非共振，例如在无界原好阶段证明 (22.16)。这仍是充分接口，不称必要条件。$\square$

## 追加锚（本行以下为增补区）

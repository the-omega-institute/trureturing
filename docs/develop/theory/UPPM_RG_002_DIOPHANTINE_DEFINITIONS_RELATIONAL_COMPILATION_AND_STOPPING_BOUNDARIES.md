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

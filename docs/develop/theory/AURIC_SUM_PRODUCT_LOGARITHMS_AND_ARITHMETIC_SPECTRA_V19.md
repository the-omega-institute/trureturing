<a id="auric-v19"></a>

# 加乘、对数与算术谱

**AURIC 递归量子门通向黎曼猜想的严格接口**

**定义、定理、证明与尚待建立的全局桥梁**

**v19.0 · 2026 年 10 月 30 日 · Asia/Singapore**

> **转换说明（编者）。** 本文完整转换作者提供的同名 XeLaTeX 稿件；原作者保留固定快照、审计、历史报告与研究进展的作者身份，本次转换不重新认证这些报告或主张。正文保留全部纸面证明及其前提；本次仅作内容与本地排版核对，不主张 Lean、数学数值、CAS、模拟、门搜索、硬件或原生托管 MathJax 认证。

## 摘要

加法、乘法、对数与平方确实能把 AURIC 的隐藏关系、素数分解、概率配分函数和量子指针放进同一套精确公式，但这些运算本身尚不等于黎曼猜想。本文先从五模式纤维导出隐藏对数荷，解释 $[2+5]=7$ 与 $[2][5]=10$ 为什么相差一个 $\log(7/10)$；再建立 Dirichlet 卷积、Euler 积、Robin 平方响应、有限 Fibonacci 重编码和算子闭路积之间的桥梁。我们证明平方可积性的临界值确为 $1/2$，同时证明它不能直接供应算术轨道上的点值。真正的酉指针重叠可等于归一化 $\zeta$，但概率平方会使振幅指数加倍。随后给出 Cayley 零点坐标的显式五模式编码，计算其经典隐藏关联和条件纠缠；分析递归门的行列式，证明固定有限相位集不能直接承载全部黎曼零点。最后以局部一致收敛与 Möbius 抵消给出两个完整的条件定理，明确从局部相容到全局零点定位尚需证明的内容。

**结论身份。**截至本轮检索，Clay Mathematics Institute 仍将 RH 列为未解决问题。本文没有证明 RH。经典算术定理、项目已有结果与本轮模型推论分别标明；纸面证明不等于 Lean 内核认证、硬件实验或原生黄金门的精确实现。本文没有运行数学数值程序、CAS、模拟或门搜索。

## 目录

1. [最新项目快照与真正的研究问题](#section-1)
2. [五模式的隐藏对数荷：为什么是 $\log(7/10)$](#section-2)
3. [从加乘电路到真正的 Euler 积](#section-3)
4. [项目的 Robin 路线：平方平均怎样成为 RH 判据](#section-4)
5. [Fibonacci 重编码、闭路 $\zeta$ 与三种不同的圆](#section-5)
6. [平方为什么自然产生 $1/2$](#section-6)
7. [真正的量子指针重叠及双指数定理](#section-7)
8. [黎曼猜想的精确酉谱形式](#section-8)
9. [把 Cayley 缺陷明确装入一个 AURIC 原子](#section-9)
10. [递归黄金门的谱能增长到哪里](#section-10)
11. [真正足以推出 RH 的两条条件定理](#section-11)
12. [哪些条件已经完成，哪些是下一步的承重条件](#section-12)
13. [附录 A：符号与来源界限](#section-13)
[文献与固定项目来源](#bibliography)

<a id="section-1"></a>

## 1. 最新项目快照与真正的研究问题

本轮固定公开 `dev` 快照
`a5a8bcdf56019e58c398f6f6d27a3620b896d001`。
提交时间为 2026-10-30 03:17:38（Asia/Singapore），标题为“theory: separate C12 from invariant fixed-resistance weights”（#23827）。相对 v18 的 `23a4ae6…`，理论目录有七条变化：五新增、两修改；当前目录共 1015 个文件。审计中分支继续推进，本稿以以上最后核对的不可变快照为准，不把移动分支视为固定证据。

本题最直接的项目来源大多是*本轮深入阅读的已有结果*，而非这次提交新增的 RH 突破：

1. [《FIB-ATOM 与 Robin 的约数尺度几何》](https://github.com/the-omega-institute/trureturing/blob/a5a8bcdf56019e58c398f6f6d27a3620b896d001/docs/develop/theory/AURIC_FIB_ROBIN_DIVISOR_SCALE_GEOMETRY.md)，尤其 §§1–6、9、12，已把四块关联、素数指数、独立相位的平方平均和 Robin 判据接在一起。

2. [《算术三角与 RH 管线续篇 II》](https://github.com/the-omega-institute/trureturing/blob/a5a8bcdf56019e58c398f6f6d27a3620b896d001/docs/develop/theory/AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE_CONTINUATION_II.md) §63，已提出条件性的五态概率场、Cayley 圆与 RH 接口；它明确保留自然算术来源与全局谱识别的缺口。

3. [《RH 离线零点与横向谱相变》](https://github.com/the-omega-institute/trureturing/blob/a5a8bcdf56019e58c398f6f6d27a3620b896d001/docs/develop/theory/RH_OFFLINE_ZERO_LEE_YANG_INSTANTANEOUS_PHASE_TRANSITION_THEORY.md)增订一 A3–A4、增订二 B6–B7，已区分局部 Euler 圆与 completed 临界圆，并给出有限 hard-core 多项式的正行列式表示。

最新相关增量是 [《量子原则与相干重构续篇》](https://github.com/the-omega-institute/trureturing/blob/a5a8bcdf56019e58c398f6f6d27a3620b896d001/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md) §68：保留复线性振幅、指定黄金门、完整终端字读出和局部操作接口，在共同有限 $p>0$ 的归一幂律 $|\alpha|^p/\sum|\alpha|^p$ 这一规定族内，一个至多三次原生门调用的检验使所构造两种 Bob 设置的 Alice 边缘相同，当且仅当 $p=2$。这是有明确前提的无信号检验；它没有证明任意概率规则的唯一性，也没有补齐 RH 的全局算术桥。新增的预测状态文件是已有作者稿的保存，编辑明确说明未新增 Lean 认证或全 SAT 算法；终端事件稿另给出了记录与统计实验的新推导。两者均保留预测表达与实际取得的区别。

本轮验证了 35 个选定当前文档和两个旧版本的 Git blob，Git 与 GitHub API 对完整目录树及差异一致。正文使用的来源已按相关章节阅读；不声称审计了全部 1015 个文档的证明。源文保存、转录与本轮阅读均不构成独立认证。

**问题的精确化。**

用户的联系应发展为：

$$
\text{加乘结构} \longrightarrow\
\text{素数或闭路的生成函数} \longrightarrow\
\text{谱与解析延拓} \longrightarrow\
\text{全部零点的定位}.
$$

前三个箭头各需定义与定理，最后一个箭头正是 RH 难度所在。下一节从 AURIC 本身已有的隐藏纤维开始。

<a id="section-2"></a>

## 2. 五模式的隐藏对数荷：为什么是 $\log(7/10)$

<a id="statement-2-1"></a>

#### 定义 2.1（模式、均值与隐藏完成）

按顺序取

$$
\Sigma=(0,1,2,3,13)=(000,100,010,001,101).
$$

位串按左、中、右排列；可见均值按左、右、中记为

$$
X=p_1+p_{13},\quad  Y=p_3+p_{13},\quad  Z=p_2,\quad
R=1-Z,\quad  \kappa=p_{13}.
$$

全部可行完成为

$$
p_\kappa=(R-X-Y+\kappa, X-\kappa, Z, Y-\kappa, \kappa),
\quad
\max(0,X+Y-R)\le\kappa\le\min(X,Y).
$$

该纤维的方向为 $h=(1,-1,0,-1,1)$。

<a id="thm-logcharge"></a>

#### 定理 2.2（隐藏对数荷的下降判据）

为五模式分别指定正数值 $w_s>0$，定义平均对数读出
$L_w(p)=\sum_s p_s\log w_s$。则

<a id="eq-logcharge"></a>

$$
L_w(p_\kappa)
=(R-X-Y)\log w_0+X\log w_1+Z\log w_2+Y\log w_3
+\kappa\log\frac{w_0w_{13}}{w_1w_3}. \tag{1}
$$

因此，该读出在所有非退化纤维上仅由 $(X,Y,Z)$ 决定，当且仅当

$$
w_0w_{13}=w_1w_3.
$$

**证明。**

将五项概率代入 $L_w$ 并收集 $\kappa$ 的系数，即得式
[(1)](#eq-logcharge)。若该系数为零，全部纤维恒定；若非零，任取长度正的可行纤维，其上读出严格变化。正实数上的对数单射给出乘法等式。

∎

项目四类非空块的数值为 $2,3,5,7$。为了定义正值的乘法读出，本篇另将空模式赋为乘法空块值 $1$，从而取

$$
(w_0,w_1,w_2,w_3,w_{13})=(1,2,3,5,7).
$$

这不把原生加性 null 读数改称为 $1$。
隐藏系数正是 $\log(7/10)$。若将对角值改成 $10$，同一个对数读出便看不见隐藏方向。这里“采用加法成块还是乘法组合”会改变可见信息；两种操作不是同一个关系的两种写法。

对整数块计数，令 $u,v,w,k\in\mathbb{N}_0$ 且 $0\le k\le\min(u,w)$，则项目已有的对应为

<a id="eq-blockinteger"></a>

$$
n=2^{u-k}3^v5^{w-k}7^k,\qquad
\log n=u\log2+v\log3+w\log5-k\log(10/7). \tag{2}
$$

这里的 $k$ 是整数计数，上一式的 $\kappa$ 是概率；二者只有在另给总数并归一化后才能对应。最小例子 $(u,v,w)=(1,0,1)$ 的两个完成分别给出 $n=10$ 与 $n=7$。这一例子解释信息区别，不位于 Robin 的 $n>5040$ 范围。

**不应丢失的区分。**

$\log(ab)=\log a+\log b$ 是正实乘法群的同态；
$\log(a+b)$ 是另一种运算。指数、log 能换坐标，却不会把任意加法自动变为同一个乘法。AURIC 的纤维把这种差别压缩成可计算的一个隐藏荷。

<a id="section-3"></a>

## 3. 从加乘电路到真正的 Euler 积

<a id="statement-3-1"></a>

#### 定义 3.1（算术卷积与对数长度）

对有限支撑算术函数 $a,b:\mathbb{N}_{\ge1}\to\mathbb{C}$，定义

$$
(a*_D b)(n)=\sum_{d\mid n}a(d)b(n/d),\qquad
\mathcal D_a(s)=\sum_{n\ge1}a(n)e^{-s\log n}.
$$

另令 $\mu_a=\sum_n a(n)\delta_{\log n}$ 为实轴上的有限复测度。

<a id="statement-3-2"></a>

#### 定理 3.2（乘法卷积的加法长度表示）

有

$$
\mathcal D_{a*_D b}(s)=\mathcal D_a(s)\mathcal D_b(s),
\qquad
\mu_{a*_D b}=\mu_a*\mu_b.
$$

在无限支撑时，只要有关级数绝对收敛，同样成立。

**证明。**

乘积展开为 $\sum_{m,n}a(m)b(n)(mn)^{-s}$，按 $k=mn$ 收集即可。
测度卷积把位置相加，而 $\log(mn)=\log m+\log n$，给出第二式。
绝对收敛是无限情形交换与重排求和的充分条件。

∎

> **编者局部说明（C4）。** 定义中的“有限复测度”指有限支撑。若只在选定的 Dirichlet 参数上要求级数绝对收敛，则无限无权原子测度在 $[0,\infty)$ 上局部有限；每个紧区间内卷积只有有限项。若还要求总变差有限，则必须另加无权系数绝对可和。各级数恒等式仍只在原文所写的绝对收敛域内成立。源 $a(n)=1$ 说明了为何需要这一解释。

<a id="thm-euler"></a>

#### 定理 3.3（Euler 积与本原对象的对数展开）

令 $s=\sigma+it$。在 $\sigma>1$，

<a id="eq-euler"></a>

$$
\begin{aligned}\zeta(s)&=\sum_{n\ge1}e^{-s\log n}
=\prod_{p {\rm prime}}(1-e^{-s\log p})^{-1}, \tag{3}\end{aligned}
$$

<a id="eq-logeuler"></a>

$$
\begin{aligned}\log\zeta(s)&=\sum_p\sum_{k\ge1}\frac{p^{-ks}}{k}, \tag{4}\end{aligned}
$$

<a id="eq-vm"></a>

$$
\begin{aligned}-\frac{\zeta'(s)}{\zeta(s)}
&=\sum_p\sum_{k\ge1}(\log p)p^{-ks}
=\sum_{n\ge1}\Lambda(n)n^{-s}. \tag{5}\end{aligned}
$$

式 [(4)](#eq-logeuler) 指定趋向右端时为零的全纯对数分支；
$\Lambda(p^k)=\log p$，其他 $n$ 上为零。

**证明。**

有限素数集上的各个几何级数相乘，唯一素因子分解保证每个仅使用该素数集的整数恰出现一次。$\sum_n n^{-\sigma}<\infty$ 允许素数集耗尽并得到式 [(3)](#eq-euler)。在任意闭半平面 $\sigma\ge1+\delta$，对数级数和导数级数局部一致绝对收敛；应用
$-\log(1-z)=\sum_{k\ge1}z^k/k$ 并逐项微分，即得余式。

∎

这些是经典恒等式 [3](#ref-dlmfeuler)。其中加法收集整数贡献，乘法使用唯一素数分解，log 分离素数及其重复次数。一般电路、一般递归图并没有自动提供普通自然数的素数分解。

<a id="section-3-1"></a>

### 3.1. 预测、概率、变分的精确算术模型

<a id="thm-gibbs"></a>

#### 定理 3.4（Dirichlet–Gibbs 概率律）

对实数 $\sigma>1$，定义

$$
\Pr_\sigma(N=n)=\frac{n^{-\sigma}}{\zeta(\sigma)}.
$$

不同素数的指数 $\nu_p(N)$ 独立，其有限维联合律是几何律之积：

$$
\Pr_\sigma(\nu_p=k_p, p\in S)
=\prod_{p\in S}(1-p^{-\sigma})p^{-\sigma k_p}.
$$

若 $\Psi(\sigma)=\log\zeta(\sigma)$，则

$$
-\Psi'(\sigma)=\mathbb{E}_\sigma[\log N],\qquad
\Psi''(\sigma)=\operatorname{Var}_\sigma(\log N)
=\sum_p\frac{(\log p)^2p^\sigma}{(p^\sigma-1)^2}>0.
$$

**证明。**

在有限素数集 $S$ 上固定指数后，剩余整数与所有 $p\in S$ 互素。
其权重总和为 $\zeta(\sigma)\prod_{p\in S}(1-p^{-\sigma})$，故得联合律。
所有 $\log N$ 矩均有限，允许微分配分函数；或直接相加几何律的均值与方差。$N=1,2$ 均有正概率而对数不同，故方差严格为正。
此外 $\sum_p\Pr(\nu_p\ge1)=\sum_p p^{-\sigma}<\infty$，无限独立实现几乎必然只有有限个非零指数，确实给出一个普通整数。

∎

对熵和平均 $\log N$ 有限的概率律 $q$，

$$
D(q\Vert\Pr_\sigma)
=-H(q)+\sigma\mathbb{E}_q[\log N]+\log\zeta(\sigma)\ge0.
$$

这给出严格的预测–变分接口：该律唯一最小化 $\sigma\mathbb{E}[\log N]-H$。
其正性在 $\sigma>1$ 已完全成立，并不需要 RH；在 $\sigma=1$，正概率的归一化失效。这个边界与 RH 的 $1/2$ 必须分开。

<a id="section-4"></a>

## 4. 项目的 Robin 路线：平方平均怎样成为 RH 判据

<a id="statement-4-1"></a>

#### 定义 4.1（约数响应）

写 $n=\prod_{p\mid n}p^{a_p}$，定义

$$
Z_{\rm div}(n)=\sum_{d\mid n}\frac1d
=\frac{\sigma_1(n)}n,\qquad
\sigma_1(n)=\sum_{d\mid n}d.
$$

对每个素数方向给独立圆周变量 $\theta_p$，令

$$
A_n(\boldsymbol\theta)=
\prod_{p\mid n}\left(\sum_{k=0}^{a_p}p^{-k/2}e^{ik\theta_p}\right).
$$

<a id="thm-robinparseval"></a>

#### 定理 4.2（乘法约数盒与勾股平方响应）

在归一化乘积 Haar 测度下，

<a id="eq-robinparseval"></a>

$$
Z_{\rm div}(n)
=\prod_{p\mid n}\sum_{k=0}^{a_p}p^{-k}
=\int_{\mathbb{T}^{\{p:p\mid n\}}}|A_n|^2 dm. \tag{6}
$$

**证明。**

约数与指数盒 $0\le k_p\le a_p$ 一一对应，故倒数和因子化。
展开 $|A_n|^2$，不同指数向量的交叉项在至少一个圆周方向上积分为零；保留项为 $\prod_p p^{-k_p}$。有限求和与积分可交换。

∎

这一定理是项目原文 §5 的有限 Fourier 桥。若所有素数共用一个相位，只有总指数差需要为零，额外交叉项一般不会消失。例如 $n=6$ 的独立平均为 $2$，共用相位平均则为 $2+2/\sqrt6$。因此“平方”必须说明在哪个空间、对哪些独立方向取内积。

**经典 Robin 定理作为外部输入。**

Robin 的等价判据为 [6](#ref-choie)

<a id="eq-robin"></a>

$$
\mathrm{RH}\quad \Longleftrightarrow\quad
\forall n>5040,\quad
Z_{\rm div}(n)<e^{\gamma_E}\log\log n, \tag{7}
$$

其中 $\gamma_E$ 为 Euler–Mascheroni 常数。结合式
[(6)](#eq-robinparseval)，RH 确实等价于对所有这些素数相位多项式的平方平均作一个统一上界；*Parseval 恒等式本身没有证明该上界*。

<a id="prop-robindefect"></a>

#### 命题 4.3（同一整数上的完整对数缺口）

令 $P$ 是 $n\ge3$ 的最大素因子，定义

$$
\mathcal M(P)=\prod_{p\le P}(1-p^{-1})^{-1},\qquad
\varepsilon(P)=\log\frac{\mathcal M(P)}{e^{\gamma_E}\log P},
$$

$$
D_{\rm miss}=-\sum_{\substack{p\le P\\p\nmid n}}\log(1-p^{-1}),\qquad
D_{\rm cap}=-\sum_{p\mid n}\log(1-p^{-(a_p+1)}).
$$

则

<a id="eq-robindefect"></a>

$$
-\log\frac{Z_{\rm div}(n)}{e^{\gamma_E}\log\log n}
=D_{\rm miss}+D_{\rm cap}
+\log\frac{\log\log n}{\log P}-\varepsilon(P). \tag{8}
$$

**证明。**

每个局部等比和为
$(1-p^{-(a_p+1)})/(1-p^{-1})$。把实际素数支持嵌入完整前缀 $p\le P$，缺失素数用因子 $(1-p^{-1})$ 删除。取对数，再减去 Robin 分母的对数，即得恒等式。

∎

这是项目 §9 的精确共同来源账。前两个损失非负，第三项可为负，不能把它们统称为三个非负量。Mertens 渐近式使 $\varepsilon(P)\to0$，却没有给出每个整数的式 [(8)](#eq-robindefect) 严格为正。项目已引用针对 $\{2,3,5,7\}$ 支撑的完整 Robin 安全结果；本轮没有重新编译其 Lean 来源。尚待建立的是任意增长素数支持上的统一结论。三维模板不能把独立算术方向数固定为三。

<a id="section-5"></a>

## 5. Fibonacci 重编码、闭路 $\zeta$ 与三种不同的圆

<a id="section-5-1"></a>

### 5.1. 值能量与占位能量是不同读出

令 $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$。长度 $Q$ 的合法二进制词不含相邻的 $1$，其整数值为
$E_Q(\eta)=\sum_{j=1}^Q\eta_jF_{j+1}$。有限 Zeckendorf 双射给出
$E_Q(\Omega_Q)=\{0,\ldots,F_{Q+2}-1\}$，每个值恰一次。

<a id="prop-zeck"></a>

#### 命题 5.1（重编码不改变局部 Euler 因子）

令 $M=F_{Q+2}$，则

$$
Z_Q^{\rm exp}(x)=\sum_{\eta\in\Omega_Q}x^{E_Q(\eta)}
=\frac{1-x^M}{1-x}.
$$

$x=1$ 处按可去延拓取值 $M$。
$Q\ge1$ 时全部零点满足 $x^M=1$ 且 $x\ne1$。在 $|x|<1$ 上，随 $Q\to\infty$，局部一致收敛到 $(1-x)^{-1}$。
若 $x=p^{-s}$，有限零点的圆 $|x|=1$ 对应 $\operatorname{Re} s=0$。

**证明。**

双射使求和成为普通有限等比和。单位根结论由分子与分母的可去因子得到；在 $|x|\le r<1$ 上，尾项至多 $r^M/(1-r)$，故局部一致收敛。最后 $|p^{-s}|=p^{-\operatorname{Re} s}$。

∎

若改用占位数 $|\eta|$，则
$H_Q(z)=\sum_{\eta\in\Omega_Q}z^{|\eta|}$ 满足
$H_Q=H_{Q-1}+zH_{Q-2}$、$H_0=1,H_1=1+z$。项目已有有限根公式

$$
H_Q(z)=\prod_{j=1}^{\lfloor(Q+1)/2\rfloor}
\left(1+4z\cos^2\frac{j\pi}{Q+2}\right)
=\det(I+z\mathsf K_Q),\quad  \mathsf K_Q>0.
$$

这是有限负实根定位；$z$ 是占位活动度，既不是 $p^{-s}$，也不是稍后的 Cayley 零点坐标。本文消费该项目已有公式，不将其命名为 RH。

<a id="section-5-2"></a>

### 5.2. 算子赋权闭路的 Euler 积

<a id="statement-5-2"></a>

#### 定义 5.2（静态关系图的块转移）

取有限有向图，每条边 $e:i\to j$ 携带标量 $w_e\in\mathbb{C}$ 与同一个 $m$ 维内部空间上的酉门 $U_e$。定义

$$
T_{ji}=\sum_{e:i\to j}w_eU_e.
$$

闭路 $c$ 的长度为 $\ell(c)$，标量权重为 $w_c=\prod_{e\in c}w_e$，内部有序门为沿行走顺序作用的乘积 $U_c$。本原闭路指非空闭路，其边序列不是较短闭路的 $k\ge2$ 次重复；起点只计循环等价类。

<a id="thm-cycle"></a>

#### 定理 5.3（算子闭路展开）

在形式幂级数意义及足够小的 $|u|$ 上，

<a id="eq-tracezeta"></a>

$$
\begin{aligned}\mathcal Z_T(u)
&:=\det(I-uT)^{-1}
=\exp\left(\sum_{n\ge1}\frac{u^n}{n}\operatorname{Tr} T^n\right), \tag{9}\end{aligned}
$$

<a id="eq-operatoreuler"></a>

$$
\begin{aligned}\mathcal Z_T(u)
&=\prod_{[c] {\rm primitive}}
\det(I_m-w_cu^{\ell(c)}U_c)^{-1}. \tag{10}\end{aligned}
$$

**证明。**

对矩阵对数的收敛级数取迹，得到
$-\log\det(I-uT)=\sum_{n\ge1}u^n\operatorname{Tr}(T^n)/n$。
$\operatorname{Tr}(T^n)$ 展开成全部长度 $n$ 的带起点闭路的内部迹。
每条闭路唯一为本原闭路 $c$ 的 $k$ 次重复，$n=k\ell(c)$；
$c^k$ 有 $\ell(c)$ 个不同的循环起点贡献，消去分母中的 $\ell(c)$，留下

$$
\sum_{k\ge1}\frac{(w_cu^{\ell(c)})^k}{k}\operatorname{Tr}(U_c^k).
$$

循环移动起点不改变迹。上式正是
$-\log\det(I_m-w_cu^{\ell(c)}U_c)$。
有限图每个固定次数只有有限多条路径，形式重排合法；足够小的 $u$ 下绝对收敛给出解析恒等式。

∎

这是有限型动力系统的经典闭轨方法 [8](#ref-bowenlanford) 的块算子版本与直接证明。它赋予“参数里面还是门”一个严格含义，但不会自动证明全局 $T$ 酉：不同入边之间仍须满足 v18 的交叉列相容条件。

<a id="statement-5-4"></a>

#### 推论 5.4（DAG 与局部门酉性的两个边界）

有限 DAG 的 $T$ 幂零，故 $\mathcal Z_T=1$。非平凡边界电路可以存在，但它不等于非平凡闭路 $\zeta$。另一方面，即使每条边门酉，整体 $\mathcal Z_T$ 的极点也不一定在单位圆。

**证明。**

DAG 上路径长度有有限上界，足够高次的 $T$ 为零，行列式恒为 $1$。
第二项取一维边门全部为 $1$，以及 Fibonacci 邻接矩阵

$$
B=\begin{pmatrix}1&1\\1&0\end{pmatrix}.
$$

此时 $\mathcal Z_B(u)=(1-u-u^2)^{-1}$ 的极点为
$\varphi^{-1},-\varphi$，其中 $\varphi=(1+\sqrt5)/2$；均不在单位圆。
每个单独本原闭路因子 $(1-u^{\ell(c)})^{-1}$ 的极点却都在单位圆。

∎

这个反例说明：无限闭路族的增长及乘积收敛域会产生单个局部因子没有的全局奇点。普通 Euler 因子 $(1-p^{-s})^{-1}$ 各自在 $\operatorname{Re} s=0$ 有极点，整体 $\zeta$ 却在 $s=1$ 有极点；临界带中的零点还依赖解析延拓。逐因子看圆，不能替代全局完成。

<a id="section-6"></a>

## 6. 平方为什么自然产生 $1/2$

<a id="statement-6-1"></a>

#### 定义 6.1（素数相位空间）

在全部素数的乘积圆周 $\mathbb{T}^{\mathcal P}$ 上取 Haar 概率测度。
由唯一素因子分解定义字符

$$
\chi_n(\mathbf z)=\prod_p z_p^{\nu_p(n)}.
$$

每个乘积只有有限个非平凡因子，并且 $\chi_{mn}=\chi_m\chi_n$。

<a id="thm-half"></a>

#### 定理 6.2（乘法字符的勾股定理）

不同 $\chi_n$ 正交归一。因此，对实数 $a$，

$$
F_{a,N}=\sum_{n\le N}n^{-a}\chi_n,\qquad
\left\lVert{F_{a,N}}\right\rVert_2^2=\sum_{n\le N}n^{-2a}.
$$

当且仅当 $a>1/2$，$F_{a,N}$ 存在 $L^2$ 极限，且

<a id="eq-half"></a>

$$
\left\lVert{F_a}\right\rVert_2^2=\zeta(2a). \tag{11}
$$

**证明。**

若 $m\ne n$，至少一个素数指数不同；对该圆周积分使
$\chi_m\overline{\chi_n}$ 的积分为零。相同字符的平方积分为 $1$。
于是任意部分和差的平方范数等于相应数项级数的尾和；
Hilbert 完备性和正项级数判据给出充要条件。

∎

这一结构属于 Bohr 字符空间与 Dirichlet Hilbert 空间的经典背景
[7](#ref-hedenmalm)。此处 $1/2$ 不是任意填入：平方把指数 $a$ 变成 $2a$，普通级数的边界为 $2a=1$。

<a id="prop-pointeval"></a>

#### 命题 6.3（平方平均不控制指定相位的点值）

对任意固定 $\mathbf z_0\in\mathbb{T}^{\mathcal P}$，不存在常数 $C$ 使所有有限字符多项式都满足
$|f(\mathbf z_0)|\le C\left\lVert{f}\right\rVert_2$。

**证明。**

取

$$
g_N(\mathbf z)=N^{-1/2}\sum_{n=1}^N
\overline{\chi_n(\mathbf z_0)}\chi_n(\mathbf z).
$$

正交性给 $\left\lVert{g_N}\right\rVert_2=1$，但 $g_N(\mathbf z_0)=\sqrt N$。

∎

在算术相位 $\mathbf z(t)=(p^{-it})_p$ 上，只有在 $a>1$ 时，以上级数的绝对收敛直接给出
$F_a(\mathbf z(t))=\zeta(a+it)$。
当 $1/2<a\le1$，$L^2$ 等价类不能自动在这条轨道上取值；例如 $\mathbf z=1$ 上的正项和仍发散。
解析延拓、Haar 几乎处处的陈述、指定算术点的读出，是不同的数学任务。

**一个确实存在的 Hilbert 空间。**

对平方可和系数 $b_n$，$f(s)=\sum b_nn^{-s}$ 在 $\operatorname{Re} s>1/2$ 有界点评价，
因为 Cauchy–Schwarz 给
$|f(s)|^2\le\sum|b_n|^2\,\zeta(2\operatorname{Re} s)$。
它的再生核为 $K(s,w)=\zeta(s+\overline w)$。这是精确的谱–Hilbert 联系；此时 $\operatorname{Re}(s+\overline w)>1$，所以核正性没有提前证明临界带内的零点定理。上一命题考察圆周边界点，故与这里的半平面内点评价并不矛盾。

<a id="section-7"></a>

## 7. 真正的量子指针重叠及双指数定理

<a id="statement-7-1"></a>

#### 定义 7.1（算术对数 Hamiltonian）

在 $\ell^2(\mathbb{N}_{\ge1})$ 上取

$$
H\lvert{n}\rangle{}=(\log n)\lvert{n}\rangle{},\qquad
D(H)=\left\{\psi:\sum_n(\log n)^2|\psi_n|^2<\infty\right\}.
$$

这是自伴乘法算子，$W_t=e^{-itH}$ 为酉算子。
$t$ 是对数谱的共轭读出参数，无须解释为外部物理时间。
在 $\sigma>1$，定义

$$
\rho_\sigma=\frac{e^{-\sigma H}}{\zeta(\sigma)},\qquad
\lvert{\psi_\sigma}\rangle{}=\frac{\sum_n n^{-\sigma/2}\lvert{n}\rangle{}}{\sqrt{\zeta(\sigma)}}.
$$

这里的算术 Hamiltonian 和全部整数态是显式新增输入，尚未由一个有限黄金门字实现。

<a id="thm-pointer"></a>

#### 定理 7.2（归一化 $\zeta$ 的酉重叠）

对所有实数 $t$ 和 $\sigma>1$，

<a id="eq-pointer"></a>

$$
m_\sigma(t)=\operatorname{Tr}(\rho_\sigma W_t)
=\langle{\psi_\sigma}\rvert{}W_t\lvert{\psi_\sigma}\rangle{}
=\frac{\zeta(\sigma+it)}{\zeta(\sigma)},
\qquad
1\ge|m_\sigma(t)|\ge
\frac{\zeta(2\sigma)}{\zeta(\sigma)^2}>0. \tag{12}
$$

**证明。**

迹及内积都是绝对收敛的 $\sum_n n^{-\sigma-it}/\zeta(\sigma)$。
上界来自单位相位的概率平均。对下界，Euler 积给

$$
|\zeta(\sigma+it)|
\ge\prod_p(1+p^{-\sigma})^{-1}
=\frac{\zeta(2\sigma)}{\zeta(\sigma)}.
$$

这里所有乘积在 $\sigma>1$ 绝对收敛，因而极限保持不等式。

∎

若父系统有非平凡投影 $P$，受控门
$C_P(W_t)=(I-P)\otimes I+P\otimes W_t$
将纯指针变为 $\lvert{\psi_\sigma}\rangle{}$ 或 $W_t\lvert{\psi_\sigma}\rangle{}$；
其重叠为 $m_\sigma(t)$。故这一特定一次耦合不能给出完全正交的两条记录，也不能对所有父输入产生精确的非选择 Lüders 通道。该结论不限制另备辅助态或使用更多操作的一般测量。

> **编者局部说明（C1）。** 首次使用量子投影时，$P$ 按正交 Hilbert 投影解释，即 $P=P^*=P^2$。仅有一般斜幂等 $P^2=P$ 不能推出这里所声称的酉性；下文分解与行列式公式使用该正交投影解释。

v18 的勾股恒等式在此成为

$$
1=\left|\frac{\zeta(\sigma+it)}{\zeta(\sigma)}\right|^2
+\left\lVert{(W_t-m_\sigma(t)I)\sqrt{\rho_\sigma}}\right\rVert_{\rm HS}^2.
$$

证明只需展开第二项并使用 $\operatorname{Tr}\rho_\sigma=1$、
$\operatorname{Tr}(\rho_\sigma W_t)=m_\sigma(t)$。它是概率和酉重叠的精确关系，不能在 $\sigma\le1$ 继续使用已经失去归一化的 $\rho_\sigma$。

<a id="thm-double"></a>

#### 定理 7.3（振幅平方使实指数加倍）

令 $a>1/2$，则

$$
\lvert{\chi_a}\rangle{}=\frac{\sum_n n^{-a}\lvert{n}\rangle{}}{\sqrt{\zeta(2a)}}
$$

是合法单位态，但其可见酉重叠为

<a id="eq-double"></a>

$$
\langle{\chi_a}\rvert{}W_t\lvert{\chi_a}\rangle{}
=\frac{\zeta(2a+it)}{\zeta(2a)}, \tag{13}
$$

而不是 $\zeta(a+it)$。

**证明。**

范数由 $\sum_n n^{-2a}$ 给出。内积把每个振幅与其共轭相乘，系数变为 $n^{-2a}$，再乘 $n^{-it}$。
直接相加振幅以获得 $\sum_n n^{-a-it}$，相当于与全一向量配对；该向量不属于 $\ell^2$，不是有界 Hilbert 读出。事实上 $N$ 项全一向量的范数为 $\sqrt N$。

∎

因此，平方可积性确实在 $a=1/2$ 改变，但合法 Born 指针的参数仍位于 $\operatorname{Re} s=2a>1$。若试图把它直接当成 RH 临界带上的测量，少了一项不可忽略的指数变化。

<a id="section-8"></a>

## 8. 黎曼猜想的精确酉谱形式

<a id="statement-8-1"></a>

#### 定义 8.1（完成函数与临界圆）

使用经典解析延拓定义

$$
\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s).
$$

$\xi$ 是整函数，$\xi(0)=\xi(1)=1/2$，
$\xi(s)=\xi(1-s)$，并具有共轭对称；它的零点恰是 $\zeta$ 的非平凡零点，保留重数 [4](#ref-dlmfxi) [5](#ref-dlmfzeros)。对 $\rho\ne0$ 定义

$$
z_\rho=\frac{\rho-1}{\rho}=1-\frac1\rho.
$$

<a id="thm-cayley"></a>

#### 定理 8.2（Cayley 临界线判据）

有

<a id="eq-cayley"></a>

$$
|z_\rho|^2-1=\frac{1-2\operatorname{Re}\rho}{|\rho|^2},
\qquad
|z_\rho|=1 \Longleftrightarrow \operatorname{Re}\rho=\frac12. \tag{14}
$$

当 $\rho\ne0,1$，

$$
z_{1-\rho}=z_\rho^{-1},\qquad
z_{1-\overline\rho}=\overline{z_\rho}^{ -1},
\qquad \rho=\frac1{1-z_\rho}.
$$

因此 RH 等价于全部 $\xi$ 零点的 Cayley 像位于单位圆。

**证明。**

$|\rho-1|^2-|\rho|^2=1-2\operatorname{Re}\rho$，除以 $|\rho|^2$ 即得主式。其余等式直接代入，并使用 $\rho\ne0,1$。逆式还表明不同有限 $\rho$ 有不同的 $z_\rho$，且 $z_\rho\ne1$。

∎

> **编者局部表示适配。** 原 TikZ 图在单文件 Markdown 中用围栏等宽文本作双平面坐标示意；坐标轴、临界线、零点标记、变换箭头、单位圆、排除点、面板文字与原图注均保留。字符间距不表示数值比例；`*` 为实心零点标记，`o` 为空心排除点。

<a id="figure-1"></a>

```text
             Im s                                           Im z
               ^                                              ^
               |       |                                 .----|----.
               |     ρ *                               .'     |     '.
               |       |         z = 1 - 1/s          /       |       \
               |       |        ------------>        |        |        |
---------------+-------+------> Re s               --+--------+--------o--> Re z
               |      1/2                            |        |        | 1
               |       |                              \       |       /
               |       |                               '.     |     .'
               |       |                                 '----|----'
               |       |                                      |
          完成函数的临界线                               零点的 Cayley 圆
           Re s = 1/2                                    |z| = 1, z != 1
```

**图 1。** 这是一个精确坐标等价。对照局部 Euler 变量 $x=p^{-s}$，其单位圆对应 $\Re s=0$。图中没有假定任何尚未证明的零点属于临界线。

<a id="prop-symmetry"></a>

#### 命题 8.3（对称、正性和完成仍不自动定位零点）

取 $0<b<1/2$、$c>0$、$u=s-1/2$，则

$$
F(s)=((u-b)^2+c^2)((u+b)^2+c^2)
$$

是满足 $F(s)=F(1-s)$ 和共轭对称的整函数；它在实轴上严格为正，却有四个离开临界线的零点 $1/2\pm b\pm ic$。

**证明。**

$u\mapsto-u$ 交换两个因子；系数为实数。实 $u$ 时两个因子均为正。各因子为零恰给出所列四点。

∎

该反例不保持 Riemann 的精确 Euler 数据，因而不是 RH 反例；它证明的是“有反射、相容或某种正性”这一组较弱条件不足。类似地，正系数自反多项式 $1+3z+z^2$ 的两个根为 $-\varphi^2,-\varphi^{-2}$，互为倒数却不在单位圆。

**自伴算子的正确尺度。**

若 $H=H^*$，则

$$
U=(H+iI/2)(H-iI/2)^{-1}
$$

为酉算子；实本征值 $t$ 对应
$z=(t+i/2)/(t-i/2)=z_{1/2+it}$。
有限维且 $1\notin\operatorname{spec} U$ 时，逆式为

$$
H=-\frac{i}{2}(I+U)(I-U)^{-1}.
$$

无穷维情形须另说明谱、定义域与正则化，不能无条件取普通行列式。

项目管线 II §63.7 有一处尺度笔误：若写
$\rho=1/2+i\gamma/2$，则应有
$z_\rho=(\gamma+i)/(\gamma-i)$；源式的
$(2\gamma+i)/(2\gamma-i)$ 对应 $\rho=1/2+i\gamma$。
本文统一使用 $t=\Im\rho$，保留上式的半单位尺度。此处只更正文稿推导，未修改远端仓库。

<a id="section-9"></a>

## 9. 把 Cayley 缺陷明确装入一个 AURIC 原子

<a id="statement-9-1"></a>

#### 定义 9.1（显式五模式编码）

固定 $\lambda>0$，对 $\rho\in\mathbb{C}\setminus\{0,1\}$ 令
$z=1-1/\rho$、$r=|z|^2$、$D=3+\lambda+r$，定义

$$
\lvert{\Psi_z}\rangle{}=\frac{\lvert{0}\rangle{}+\lvert{1}\rangle{}+\sqrt\lambda\lvert{2}\rangle{}+\lvert{3}\rangle{}+z\lvert{13}\rangle{}}{\sqrt D}.
$$

其模式概率为 $p=(1,1,\lambda,1,r)/D$。定义四角振幅比与经典对数关联

$$
\Omega=\frac{\alpha_0\alpha_{13}}{\alpha_1\alpha_3},\qquad
\eta_\square=\log\frac{p_0p_{13}}{p_1p_3}.
$$

所有分母在本定义中非零。

<a id="thm-encoding"></a>

#### 定理 9.2（临界线、隐藏关联与条件纠缠）

上述编码满足

<a id="eq-eta"></a>

$$
\begin{aligned}\Omega&=z,\qquad \eta_\square=2\log|z|, \tag{15}\end{aligned}
$$

$$
\begin{aligned}X=Y&=\frac{1+r}{D},\quad  Z=\frac{\lambda}{D},\quad
R=\frac{3+r}{D},\quad \kappa=\frac rD,\end{aligned}
$$

<a id="eq-hiddenrho"></a>

$$
\begin{aligned}R\kappa-XY
&=\frac{r-1}{D^2}
=\frac{1-2\operatorname{Re}\rho}{|\rho|^2D^2}. \tag{16}\end{aligned}
$$

所以

$$
\operatorname{Re}\rho=\frac12
\quad \Longleftrightarrow\quad
\eta_\square=0
\quad \Longleftrightarrow\quad
\kappa=\frac{XY}{R}.
$$

在中间位为零的条件分支中，纯两比特态的 concurrence 为

$$
\mathcal C=\frac{2|z-1|}{3+|z|^2}.
$$

若 $\rho=1/2+it$，则

<a id="eq-concurrence"></a>

$$
\mathcal C=\frac1{\sqrt{1+4t^2}}>0. \tag{17}
$$

**证明。**

振幅比与概率比直接消去 $D$。均值由五模式定义读取；
$(3+r)r-(1+r)^2=r-1$，再用定理 [8.2](#thm-cayley) 得式
[(16)](#eq-hiddenrho)。
中间位为零时，归一化的两比特系数矩阵为

$$
M=\frac1{\sqrt{3+r}}
\begin{pmatrix}1&1\\1&z\end{pmatrix}.
$$

纯态 concurrence 定义为 $2|\det M|$，给出第一式。
临界线上 $r=1$，又 $z-1=-1/\rho$，故
$\mathcal C=1/(2|\rho|)=1/\sqrt{1+4t^2}$。

∎

这给出一个具体而可核查的联系：在此编码中，临界线等于经典四角关联消失；但是相位仍可保留量子纠缠。三角剖分选择概率纤维端点、最大熵完成 $\kappa=XY/R$、相干态的相位关系，是三种不同操作。

**为何这还不是 RH 证明。**

定义 $\lvert{\Psi_z}\rangle{}$ 时已经把 $\rho$ 当作输入。它对任意非零非一复数成立，离线点也会得到完全合法的态，只是 $\eta_\square\ne0$。因此不能从“成功编码”推出“全部零点的编码必在 $\eta_\square=0$”。真正需要的是：从独立的素数或门结构构造对应，并证明它自动落在该子流形。

还应避免同名变量混淆。项目管线 II §63.1 的镜像法向量是
$\eta_{\rm mir}=\frac12\log(p_2/p_5)$，交换数值标签 $2,5$ 时变号；
本篇的 $\eta_\square$ 是四角 log-odds。二者不是同一个坐标，本文的显式编码也没有自动继承原文的 $\tau$ 等变条件。

<a id="section-10"></a>

## 10. 递归黄金门的谱能增长到哪里

<a id="statement-10-1"></a>

#### 定义 10.1（两种门参数提升）

父空间维 $d$，投影 $P$ 的秩为 $q$；子空间维 $m$，$W$ 为酉算子。取

$$
C_P(W)=(I-P)\otimes I+P\otimes W,\qquad
L_P(W)=(I-P)\otimes W+P\otimes W^2.
$$

写 $D_W(u)=\det(I-uW)$。

<a id="thm-recursedet"></a>

#### 定理 10.2（递归行列式分解）

有

<a id="eq-dc"></a>

$$
\begin{aligned}D_{C_P(W)}(u)&=(1-u)^{m(d-q)}D_W(u)^q, \tag{18}\end{aligned}
$$

<a id="eq-dl"></a>

$$
\begin{aligned}D_{L_P(W)}(u)&=D_W(u)^{d-q}D_{W^2}(u)^q. \tag{19}\end{aligned}
$$

因而两者都酉；若 $W^{10}=I$，二者的十次幂也为 $I$。

**证明。**

按 $\ker P\oplus\operatorname{ran}P$ 分解父空间，第一门是
$(d-q)$ 份 $I_m$ 与 $q$ 份 $W$ 的直和；
第二门是 $(d-q)$ 份 $W$ 与 $q$ 份 $W^2$ 的直和。
行列式乘法、酉性及幂关系均逐块成立。

∎

<a id="cor-frozen"></a>

#### 推论 10.3（特定固定相位递归的直接 RH 谱障碍）

令 $\omega=e^{3\pi i/5}$，从一维 $W_0=\omega$ 出发，逐层只使用上述某一种提升，且每层投影及补投影均非零。
纯 $C$ 递归的不同谱值始终只有 $\{1,\omega\}$（首层以后）。
纯 $L$ 递归的谱为

$$
\{\omega^{2^k}:0\le k\le n\},
$$

至第四层后固定为
$\{\omega,\omega^2,\omega^4,\omega^8,\omega^6\}$。
它们不能把全部互异的 $\xi$ 零点直接识别为 $z_\rho$。

**证明。**

式 [(18)](#eq-dc) 只新增谱值 $1$；从标量 $\omega$ 出发即得第一项。
式 [(19)](#eq-dl) 使每个已有值可保留或平方，归纳给出指数 $2^k$。
模 $10$ 的序列是 $1,2,4,8,6,2,\ldots$。
另一方面，$\xi$ 有无穷多个互异零点 [5](#ref-dlmfzeros)，而
$\rho\mapsto z_\rho$ 单射且不取 $1$。有限谱值集合不可能容纳它们。

∎

维数和重数的增长不是新相位的增长。这个结论只针对指定的嵌套规则；
不同位置黄金门的任意非交换字可以产生不同的谱，不能用本推论否定项目已有的近似普适性。

<a id="prop-logrank"></a>

#### 命题 10.4（有限固定长度的素数对应障碍）

若一个有限图只有固定实边长 $L_1,\ldots,L_r$，则不可能把全部普通素数逐个对应为闭路，并要求每条对应闭路的总长恰为 $\log p$。

**证明。**

每条闭路总长是边长的非负整数线性组合，属于至多 $r$ 维的
$\mathbb{Q}$-线性空间。任意有限组不同素数的对数都在 $\mathbb{Q}$ 上线性无关：
若 $\sum_j a_j\log p_j=0$、$a_j\in\mathbb{Q}$，清分母后指数化得到
$\prod_jp_j^{b_j}=1$；唯一素因子分解迫使全部 $b_j=0$。
取 $r+1$ 个素数即矛盾。

∎

该命题允许无限图、新增独立边长、参数依赖边长及非逐项的迹公式。
它解释了为什么需要新增*算术独立方向*，而不只是重复同一个黄金尺度。

<a id="prop-clock"></a>

#### 命题 10.5（人工临界线与有限零点密度）

任取实数 $c$、$L>0$ 和固定 $d$ 维酉矩阵 $U$，

$$
F_{U,L,c}(s)=\det(I-e^{-L(s-c)}U)
$$

的全部零点都在 $\operatorname{Re} s=c$，其正高度计数为
$N_F(T)=dLT/(2\pi)+O(d)$，重数计入。
因此固定的这种行列式不可能与 $\xi$ 只相差一个处处非零整函数。

**证明。**

若 $e^{i\theta_j}$ 是 $U$ 的本征值，则零点满足
$e^{-L(s-c)}e^{i\theta_j}=1$，故
$s=c+i(\theta_j-2\pi k)/L$。每条等差序列到高度 $T$ 贡献
$LT/(2\pi)+O(1)$。
Riemann–von Mangoldt 公式无条件给出 [9](#ref-zerocount)

$$
N_\zeta(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}
-\frac{T}{2\pi}+O(\log T).
$$

两种增长阶不同，处处非零因子不改变零点及其重数。

∎

所以仅把参数平移为 $s-1/2$ 会制造一条临界线，却没有解释为何它属于实际 $\xi$。无穷维、不同尺度与正则化必须另有正确的极限定理。

<a id="section-11"></a>

## 11. 真正足以推出 RH 的两条条件定理

<a id="section-11-1"></a>

### 11.1. 自伴近似的局部一致完成

<a id="thm-hurwitz"></a>

#### 定理 11.1（自伴行列式的全局完成判据）

设 $H_N$ 是有限维自伴矩阵，$g_N$ 是处处非零整函数。令

$$
F_N(s)=g_N(s)\det((s-1/2)I-iH_N).
$$

如果 $F_N\to\xi$ 在整个复平面的每个紧集上都一致收敛，则 RH 成立。

**证明。**

每个 $F_N$ 的零点都在 $\operatorname{Re} s=1/2$。
在右开半平面上，$F_N$ 全纯且无零；由 Hurwitz 定理，极限要么处处为零，要么无零。$\xi(2)\ne0$ 排除前者。
左开半平面同理，且 $\xi(-1)=\xi(2)\ne0$。
故 $\xi$ 的全部零点位于分界线上。

也可直接给出局部论证：若离线点是 $\xi$ 的零点，取一个完全位于相应半平面的小圆盘，使边界无零。紧集一致收敛使充分大的 $N$ 在圆周上满足
$|F_N-\xi|<|\xi|$。Rouché 定理迫使 $F_N$ 在圆内有同数目的零点，与自伴性矛盾。

∎

这一条件定理把项目 B7.3 的目标写得完整：需要从素数、Fibonacci 结构和 Gamma 完成构造 $H_N,g_N$，并证明它们逼近*这一个* $\xi$。先按待证明的零点安排行列式，或只证明有限矩阵自伴，都没有完成输入来源与收敛。

<a id="statement-11-2"></a>

#### 命题 11.2（局部门误差不自动控制增长维数的行列式）

令 $U_N=e^{i/N}I_N$。则
$\left\lVert{U_N-I_N}\right\rVert\to0$，但 $\det U_N=e^i\ne1$。

**证明。**

算符范数差为 $|e^{i/N}-1|\le1/N$，行列式是 $N$ 个
$e^{i/N}$ 的乘积。

∎

因此，即便原生门能高精度近似某个有限构件，也须核算总维数、迹与行列式误差；有限窗口验证不能替代所有紧集上的收敛证明。

<a id="section-11-2"></a>

### 11.2. 取反的算术版本：Möbius 抵消

<a id="statement-11-3"></a>

#### 定义 11.3（乘法逆的符号）

令 $\mu(1)=1$；若 $n$ 含平方素因子则 $\mu(n)=0$；否则
$\mu(n)=(-1)^k$，其中 $k$ 是互异素因子数。令
$M(x)=\sum_{n\le x}\mu(n)$。

唯一素数分解给
$\sum_{d\mid n}\mu(d)=\prod_{p\mid n}(1-1)=0$（$n>1$）。
因此 $\mu$ 是常数算术函数 $1$ 的 Dirichlet 卷积逆，在 $\operatorname{Re} s>1$，

$$
\frac1{\zeta(s)}=\sum_{n\ge1}\mu(n)n^{-s}
$$

是经典恒等式 [3](#ref-dlmfeuler)。这是一种有实际算术约束的“取反”，不是任意独立的随机正负号。

<a id="thm-mobius"></a>

#### 定理 11.4（平方根尺度的确定性抵消足以推出 RH）

如果对每个 $\epsilon>0$，存在 $C_\epsilon<\infty$ 使

$$
|M(x)|\le C_\epsilon x^{1/2+\epsilon}\qquad(x\ge1),
$$

则 RH 成立。

**证明。**

对半平面 $\operatorname{Re} s>1/2$ 的任意紧集 $K$，选择
$0<\epsilon<\inf_{s\in K}\operatorname{Re} s-1/2$。
于是

$$
G(s)=s\int_1^\infty M(x)x^{-s-1} dx
$$

在 $K$ 上绝对一致收敛，尾项由常数倍
$\int_A^\infty x^{-1-(\inf_K\operatorname{Re} s-1/2-\epsilon)}dx$
控制。因此 $G$ 在该半平面全纯。
分部求和在 $\operatorname{Re} s>1$ 给
$G(s)=\sum\mu(n)n^{-s}=1/\zeta(s)$。
由亚纯恒等定理，$\zeta(s)G(s)=1$ 在 $\operatorname{Re} s>1/2$ 恒成立，$s=1$ 的可去性包含在该恒等式中。
若此域有 $\zeta$ 零点，则左边在该点为零，矛盾。
函数方程将任意左侧非平凡零点映为右侧零点，故所有非平凡零点都在线上。

∎

本定理给出了从递归符号相消到 RH 的一条明确任务。
难处是证明全体尺度的确定性估计；有限门取反、有限样本或“像随机游走”的解释都没有证明这一前提。本文只证明所写充分方向，不借一个未展开的逆向等价增加结论。

<a id="section-12"></a>

## 12. 哪些条件已经完成，哪些是下一步的承重条件

| 对象 | 已证明或已有的精确联系 | 仍需另给的条件 |
|---|---|---|
| 五模式隐藏纤维 | 对数荷、$\log(7/10)$、Cayley 显式编码 | 编码的独立算术来源与必然零缺陷 |
| 素数 Euler 积 | 加法、乘法、log 的同一算术恒等式 | 临界带内的全局解析控制 |
| 平方与概率 | Parseval 的 $1/2$ 阈值、合法指针重叠 | 指定点值、正确指数及非零估计 |
| 有限 Fibonacci 结构 | 几何级数圆根、占位负实根 | 变量匹配与 completed $\xi$ 收敛 |
| 递归量子门 | 酉性、闭路乘积、行列式递归 | 新谱生成、全部素数及全部零点识别 |
| Robin 路线 | 同一整数的平方响应与缺口恒等式 | 任意素数支持上的统一严格正号 |

本轮最有用的研究目标并不是再找一个“含有加乘和 log”的模型，而是明确选定并补齐一条全局桥：

1. **算术来源。**把所有普通素数及其幂送进同一实际模型，保留唯一分解；新增层级应能提供新的独立对数长度，而非只放大固定相位的重数。

2. **读出一致。**说明对象是概率、振幅、通道、闭路迹还是行列式；平方、求和、取 log、丢弃记录的顺序必须固定。式 [(13)](#eq-double) 是最简单的指数审计。

3. **解析完成。**引入正确 Gamma 因子及函数方程，并建立足以控制零点的局部一致收敛。仅有形式级数相等或有限窗实验不足。

4. **全局符号。**最终必须证明 Robin 缺口对全部 $n>5040$ 为正、Möbius 和具有指定抵消，或给出定理 [11.1](#thm-hurwitz) 的构造与极限。它们是明确而严肃的 RH 研究任务。

用户的直觉在一个精确意义上成立：AURIC 的加乘、对数、隐藏关系与平方，可以进入 RH 的真实数学表达，并且项目已经存在这样的条件接口。本轮进一步证明了哪些局部递归足以生成这些表达、哪些相位递归会停在有限谱，以及怎样把“都在一个谱上”的想法落实为可证伪、可检查的全局完成目标。当前仍未取得使这些条件全部成立的证明。

<a id="section-13"></a>

## 附录 A. 符号与来源界限

| 符号 | 含义 |
|---|---|
| $\zeta(s)$、$\xi(s)$ | Riemann 函数与其标准完成 |
| $\omega=e^{3\pi i/5}$ | 黄金门相位；避免与 Riemann $\zeta$ 同名 |
| $Z_{\rm div}(n)$ | 约数倒数和；不是 $\zeta(s)$ |
| $\mathcal Z_T(u)$ | 闭路行列式的倒数；讨论极点时不称它们为零点 |
| $x=p^{-s}$ | 局部 Euler 变量；$\vert x\vert =1$ 对应 $\Re s=0$ |
| $z_\rho=1-1/\rho$ | 零点 Cayley 变量；$\vert z_\rho\vert =1$ 对应 $\Re\rho=1/2$ |
| $\eta_\square$ | 四角概率 log-odds；与镜像法向 $\eta_{\rm mir}$ 区分 |
| $k$、$\kappa$ | 分别为整数块计数与五模式概率纤维坐标 |

本稿中经典 Euler 恒等式、Robin 定理、完成函数的解析性质、Dirichlet Hilbert 空间、闭轨方法及零点计数均有外部来源；相应结果不主张原创性。各模型命题给出独立纸面证明。项目的有限硬核行列式、四素数支持安全性和 §68 无信号检验按原文已声明范围引用，未转称为本轮的计算或形式化认证。

从“存在一个编码”到“由来源自然得到这个编码”，从“每层酉”到“全局 completed 行列式”，从“均方有限”到“逐点非零”，是本文始终保留的三个接口。它们也解释了为什么本研究可以有具体定理和推进，而仍没有宣告解决 RH。

<a id="bibliography"></a>

## 文献与固定项目来源

<a id="ref-clay"></a>

**[1]** Clay Mathematics Institute.
[Riemann Hypothesis](https://www.claymath.org/millennium/Riemann-Hypothesis/).
本轮检索仍标示 Unsolved，2026-10-30。

<a id="ref-bombieri"></a>

**[2]** E. Bombieri.
[Problems of the Millennium: The Riemann Hypothesis](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf).
Clay 官方问题说明；本文不将该历史文献中的旧计算范围当作当前进展。

<a id="ref-dlmfeuler"></a>

**[3]** NIST Digital Library of Mathematical Functions.
[§25.2: Definition and Expansions](https://dlmf.nist.gov/25.2);
[§27.4: Euler Products and Dirichlet Series](https://dlmf.nist.gov/27.4).
使用收敛域、Euler 积、Möbius 逆与对数导数。

<a id="ref-dlmfxi"></a>

**[4]** NIST DLMF.
[§25.4: Reflection Formulas](https://dlmf.nist.gov/25.4).
标准 $\xi$ 定义与函数方程。

<a id="ref-dlmfzeros"></a>

**[5]** NIST DLMF.
[§25.10: Zeros](https://dlmf.nist.gov/25.10).
临界带、对称性与非平凡零点。

<a id="ref-choie"></a>

**[6]** Y.-J. Choie, N. Lichiardopol, P. Moree, P. Solé.
[On Robin's criterion for the Riemann Hypothesis](https://arxiv.org/pdf/math/0604314).
arXiv:math/0604314v2, 2006。原始 Robin 定理归于
G. Robin, J. Math. Pures Appl. 63 (1984), 187–213；
本稿通过该作者论文的摘要及 §1 核对等价陈述。

<a id="ref-hedenmalm"></a>

**[7]** H. Hedenmalm, P. Lindqvist, K. Seip.
[A Hilbert space of Dirichlet series and systems of dilated functions in $L^2(0,1)$](https://arxiv.org/pdf/math/9512211).
预印本 1995；Duke Math. J. 86 (1997), 1–37。
本文使用引言及 §2 的字符空间与 Hilbert 接口，未借几乎处处结论证明 RH。

<a id="ref-bowenlanford"></a>

**[8]** R. Bowen, O. E. Lanford III.
[Zeta functions of restrictions of the shift transformation](https://people.math.harvard.edu/~knill/history/lanford/papers/BowenLanford.pdf).
Proc. Sympos. Pure Math. 14 (1970), 43–49。
有限型闭轨方法的背景；正文的块算子公式自足证明。

<a id="ref-zerocount"></a>

**[9]** E. Hasanalizade, Q. Shen, P.-J. Wong.
[Counting zeros of the Riemann zeta function](https://arxiv.org/pdf/2107.06506).
arXiv:2107.06506, 2021；Journal of Number Theory 235 (2022), 219–241。
本文只使用摘要及引言给出的无条件零点计数主项与误差阶。

<a id="ref-reporobin"></a>

**[10]** 项目固定快照：
[FIB-ATOM 与 Robin 的约数尺度几何](https://github.com/the-omega-institute/trureturing/blob/a5a8bcdf56019e58c398f6f6d27a3620b896d001/docs/develop/theory/AURIC_FIB_ROBIN_DIVISOR_SCALE_GEOMETRY.md)。
重点 §§1–6、9、12；四素数安全性按该稿的来源供应陈述。

<a id="ref-reporh"></a>

**[11]** 项目固定快照：
[算术三角与 RH 管线续篇 II](https://github.com/the-omega-institute/trureturing/blob/a5a8bcdf56019e58c398f6f6d27a3620b896d001/docs/develop/theory/AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE_CONTINUATION_II.md) §63；
[RH 离线零点与横向谱相变](https://github.com/the-omega-institute/trureturing/blob/a5a8bcdf56019e58c398f6f6d27a3620b896d001/docs/develop/theory/RH_OFFLINE_ZERO_LEE_YANG_INSTANTANEOUS_PHASE_TRANSITION_THEORY.md)增订一 A3–A4、增订二 B6–B7。
前者的 Cayley 尺度笔误在本稿正文更正；两稿均保留全局完成条件。

<a id="ref-repogate"></a>

**[12]** 项目固定快照：
[固定黄金门与编织相容](https://github.com/the-omega-institute/trureturing/blob/a5a8bcdf56019e58c398f6f6d27a3620b896d001/docs/develop/theory/AURIC_FIXED_GOLDEN_GATE_AND_BRAID_COMPATIBILITY_ZH.md)；
[量子原则与相干重构续篇](https://github.com/the-omega-institute/trureturing/blob/a5a8bcdf56019e58c398f6f6d27a3620b896d001/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md) §68。
门递归的直接延续采用本会话 v18 已证明的 $C_P,L_P$ 模型。

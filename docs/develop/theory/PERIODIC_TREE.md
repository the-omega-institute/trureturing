# 元素周期树(Periodic Tree of Mathematical Elements)· 章程与施工册 v1.0
*(**项目第四文档(正典)**,第 335 版记事立;PZG–GICT 项目附属工程;ZFC 内定义,零新公理;账本 27.417,2026-07-20。配套机读注册表:PERIODIC_TREE_registry.jsonl)*

## 0. 名与地契
树干为 **Stern–Brocot / Farey 树**(Stern 1858, Brocot 1861)——$(2,3,\infty)$ 基本直角三角形之反射递归;节点 = $SL_2(\mathbb Z)$ 矩阵,路径 = $L/R$ 词 = 连分数,叶叶既约(树上素性之原型定理)。本工程不植树,只立**挂载协议**:凡具"递归 + 二次"双结构之数学对象,经函子标注入册。

## 1. 挂载协议(四标签)
每个对象登记:**地址**(树路径/典范词——递归坐标);**素性位**(该层不可约判据之输出);**度量荷**(二次型脸:迹 $T$、内容 $g$、判别式 $d=(T^2-1)/g^2$、勾股恒等 $D=3A^2+(A+B)^2$、辐角 $\arg z$);**组合荷**(行走脸:$\Psi$、城色 $m\bmod36$、Jacobi 位)。附加:**流指针**(三明治后继 $T'=6c+7T$)与**核籍**(奇核者附核词与 $j=\mathrm{tr}/12$)。

## 2. 门卫手册(素性三级判据)
- **一级(地址级,线性时间)**:典范词非偶长词之 $k\ge2$ 次幂(奇词平方**豁免**——类-本原判据,GICT E.38)。
- **二级(代数级,完全判定)**:$(T,g)$ 为 Pell $p^2-dq^2=1$ 之**基本解**(本原判定定理,GICT E.45;120/120)。奇核双覆盖判据:$m=x^2$ 且 $2x\mid g$(E.44;114/114)。
- **三级(层际级)**:素性沿商余机之降解指纹(D3)——素在上层未必素在下层,降解模式入册,不视为矛盾。
- **复杂度注记**:二级判据可判但基本解可指数大;一级为快速预筛。

## 3. 周期律(树之"周期"为何是定理)
- **流回归律**:$\Psi\bmod12$ 沿三明治流恰步 $-2$、周期 $6$(恰等传播律,E.42/E.37;正锥无条件)。
- **城色轮转律**:$m\bmod36$ 决定 $\Psi\bmod12$(城同余定理 B,E.27),色沿流按定周期轮转。
- **塔律**:$\Psi$ 之 $2$-adic 逐层由站队/互反位驱动(定理 A 与站队塔,E.23/E.27)。
门捷列夫之"周期"在此非排版,是**模不变量沿流的回归定理**。

## 4. 免检预言制度(周期表之空格传统)
已运行案例:$Z_k$ 之 $k{=}5\Rightarrow m{=}35316$(定理背书);$j$-筛处决表($j\in\{2,5,7,8,12\}$ 无核,范数一行);预言制度战绩:两中一败一尸检(败诉产出第二层楼)。

## 5. 承重三牌与壳层墓志铭
牌一(**平四律国籍检验**):组合荷非勾股(Jordan–von Neumann 判定出界),不得冒充度量荷。牌二(**反例层**):无 D1-长度者(拟同态层)为树之边界批注,非节点。牌三(**王虹条款**):逐尺度归纳为普适问法;结构涌现带维数/测度前提。**墓志铭**:本树周期律多为已证之"是什么";"为什么恰是 12、−2、Pell"之壳层理论未知——残核统计案(基本性频率)为其第一考题。

## 6. 空格册(候认领)
残核统计律;混居城真偶精判;$G$ 全群;$j$-密度;$d$-平方退化员;Markov 树层际字典(W-树3);Herglotz 虚姊妹;scl-刺客。

## 7. 施工日志(v1.0 首期)
注册域 $m\le3000$;**141 类节点**(真偶 136、奇核 5);素性位:141/141 本原(城册按类去重后天然本原);$\Psi{=}0$ 节点 12;城色谱 $\{0{:}30,\ 3{:}45,\ 12{:}45,\ 27{:}21\}$——恰为定理 B 可实现残类 $\{0,3,12,27\}$ 之谱(其余残类 $8,23,32,35$ 于此域未现,与实现性条件一致)。注册表:PERIODIC_TREE_registry.jsonl(逐行 JSON,四标签全字段)。

---

## 附录 R：黄金回归谱、素数平方提升与已发表猜想的局部障碍

### R.1 研究对象、已有基础与开放目标

固定 Fibonacci 矩阵

$$
Q=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad \det Q=-1.
$$

其平方为 Stern–Brocot 两个标准生成矩阵的乘积：

$$
Q^2=
\begin{pmatrix}1&1\\0&1\end{pmatrix}
\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$

因此本附录挂载的是周期树中的黄金二次支，研究其有限模观察的真实回归。
目标对应既有问题卡 `Problems/wall-sun-sun-golden-unit-lift.md`：是否存在素数
$p$ 使 Fibonacci 最小周期满足 $\pi(p^2)=\pi(p)$，以及更强的无穷性问题。

现役 `LucasEvenDescent.companion` 已给出可逆伴随矩阵，
`LucasCompanion.matrixPeriod` 已以元素阶定义最小矩阵周期。
本附录将参数取为 $(1,-1)$，不重新假设周期存在或另设一个无关周期函数。
`GoldenApparition.GoldenMod` 的环定义及 `reduce` 同态适用于全部自然数模数；
其后 Frobenius 定理才额外要求素性。因此模 $p^2$ 的基础载体直接复用该对象。

以下周期与提升规律属于 Wall 及后续文献的经典范围。Guyer–Mbirika [R-ref2]
已经将连续 Fibonacci 和的最大公约数与 Pisano 周期的约束相联，
其公式与本附录的回归内容量相等。这里不宣称重新发现这些定理。
本轮贡献定位为对本库真实对象的连接、可用的局部障碍，以及对新文献一个明确猜想的反驳。
新增 Lean 源附有证明脚本，尚未在本环境执行 Lean/lake 或 Scribe 编译；
本文的普通数学证明与新源文件均不被冒称为新冻结的 kernel 结论。

### R.2 序列周期、矩阵阶与黄金单位阶

对正整数 $q$，定义 $\pi(q)$ 为 $Q$ 在模 $q$ 可逆矩阵群中的阶。
直接归纳给出对全部 $t\ge0$：

$$
Q^t=
\begin{pmatrix}
F_{t+1}&F_t\\F_t&F_{t+1}-F_t
\end{pmatrix}.
\tag{R1}
$$

减法在系数环内进行，因而 $t=0$ 没有负 Fibonacci 下标问题。
由 R1 和矩阵幂加法律：

$$
\boxed{
\pi(q)\mid t
\iff(F_t,F_{t+1})\equiv(0,1)\pmod q
\iff\forall n\ge0,\ F_{n+t}\equiv F_n\pmod q.
}
\tag{R2}
$$

最后一项反向只需取 $n=0,1$。这证明矩阵阶确实是原始整个序列的最小周期，
并非只观察矩阵迹的周期。Lean 声明为 `fibUnit_power`、
`period_dvd_iff_pair`、`period_dvd_iff_sequence`。

现役黄金代数中的 $z=a+b\varphi$ 满足 $\varphi^2=\varphi+1$。
在反序坐标 $(b,a)$ 上，其乘法矩阵是

$$
\mathcal R_q(z)=\begin{pmatrix}a+b&b\\b&a\end{pmatrix}\pmod q.
\tag{R3}
$$

坐标展开证明这是单射环同态，并且 $\mathcal R_q(\varphi)=Q$。
所以对于全部模数，

$$
\boxed{\pi(q)=\operatorname{ord}(\overline\varphi\in\mathrm{GoldenMod}(q)).}
\tag{R4}
$$

`regularRepresentation_mulVec` 将矩阵绑定到实际乘法；
`period_eq_golden_order`、`period_dvd_iff_reduced_phi` 分别识别元素阶和原黄金整数降模。
这里不排除复合模数、模 $p^2$ 或分歧素数5。
源声明保留 `ZMod 0` 的整数环约定，有限正周期只在 $q>0$ 下声明；
模1的最小正周期为1。

### R.3 回归约束与观察尺度的整除对偶

为避免与黄金位权序列重名，本文记

$$
C_t=\gcd(F_t,F_{t+1}-1)=\texttt{returnContent}(t).
$$

由于 $F_{t+1}\ge1$，此处自然数减法与整数减法一致。由 R2，

$$
\boxed{\pi(q)\mid t\iff q\mid C_t.}\tag{R5}
$$

因此一个时间约束 $t$ 所允许的全部正整数模数，恰为 $C_t$ 的约数。
当 $t=0$，$C_0=0$，全部正模数被允许，不能把这一情形放进有限约数计数。
当 $t>0$，$C_t>0$，兼容模数的数量为 $\tau(C_t)$。

R5 在整除偏序上给出两项全称结论：

$$
\boxed{
\pi(\operatorname{lcm}(a,b))=\operatorname{lcm}(\pi(a),\pi(b)),\qquad
C_{\gcd(s,t)}=\gcd(C_s,C_t).
}\tag{R6}
$$

第一式证明：任意 $T$ 同时被 $\pi(a),\pi(b)$ 整除，当且仅当
$a,b$ 同时整除 $C_T$，当且仅当 $\operatorname{lcm}(a,b)\mid C_T$。
第二式同样对任意约数测试：$q\mid C_{\gcd(s,t)}$ 当且仅当
$\pi(q)$ 同时整除 $s,t$，也即 $q$ 同时整除 $C_s,C_t$。
源码通过整除反对称完成两式，没有要求 $a,b$ 互素。

这让“哪些观察尺度在共同时间内恢复”成为一个确切问题。
它没有把现实选择、复制或生物进化作为数学假设。

### R.4 60、64和5040的严格位置

本轮精确整数复算得到

$$
C_{60}=832040=2^3\cdot5\cdot11\cdot31\cdot61,
\qquad \tau(C_{60})=64.
$$

所以恰有64个正模数使最小周期整除60，其中包含退化模数1。
非平凡模数为63个；逐项核验得到最小周期恰好60者为49个。
这两个计数的谓词不同，不能互换。

另有下列有限诊断：

| 模数 $N$ | $\tau(N)$ | $\pi(N)$ |
|---|---:|---:|
| $5040=2^4 3^2 5\cdot7$ | 60 | 240 |
| $7560=2^3 3^3 5\cdot7$ | 64 | 720 |
| $55440=2^4 3^2 5\cdot7\cdot11$ | 120 | 240 |

其中 $\tau$ 是约数容量，$\pi$ 是两坐标递推周期。二者由不同的普遍公式决定。
第60步回归所得的64个模数，不因基数相同就自动等同于六位字或64个密码子。
本轮没有为这些有限数值单独新增正例定理模块；承重结果是 R2–R6 的全称等价。

### R.5 从模 $p$ 到模 $p^2$ 的准确提升

设 $r=\pi(p)$。回归条件保证存在确切整数

$$
a=F_r/p,\qquad b=(F_{r+1}-1)/p.
$$

这是已知整除后的整数商。在模 $p^2$ 的环内，R1 给出实际矩阵：

$$
\boxed{
Q^r=I+pB,\qquad B=\begin{pmatrix}b&a\\a&b-a\end{pmatrix}\pmod{p^2}.
}\tag{R7}
$$

由于 $(pB)^2=0$ 且 $p(pB)=0$，在任意环内归纳得到
$(I+pB)^p=I$。于是

$$
\pi(p)\mid\pi(p^2)\mid p\pi(p).
$$

当 $p$ 为素数，约去正整数 $\pi(p)$ 后的商只能是1或 $p$，故

$$
\boxed{\pi(p^2)=\pi(p)\quad\text{或}\quad\pi(p^2)=p\pi(p).}\tag{R8}
$$

`return_lifts_to_square` 的矩阵论证甚至不要求素性；
`prime_square_period_dichotomy` 在最后一步使用素数的约数分类。
该二分律包含2和5。

R5 还给出

$$
\boxed{
\pi(p^2)=\pi(p)
\iff p^2\mid C_{\pi(p)}
\iff p\mid a\ \text{且}\ p\mid b.
}\tag{R9}
$$

对应 `square_period_eq_iff`、`square_period_eq_iff_quotients`。
此处没有把一次回归时间当作最小周期，双向结论使用了真实元素阶的整除关系。

### R.6 奇素数的首次缺陷只有一个自由标量

当 $p\ne2$ 为素数，$\det Q^r=(-1)^r=1\pmod p$ 强制 $r$ 为偶数。
将 $F_r=pa,F_{r+1}=1+pb$ 代入整数 Cassini 行列式，得到

$$
\boxed{2b-a=-p(b^2-ab-a^2).}\tag{R10}
$$

证明中先在整数环约去非零的 $p$，不会在模 $p^2$ 的环中非法约去零因子。
降模给 $2b=a$，因此

$$
\boxed{\pi(p^2)=\pi(p)\iff p\mid F_{\pi(p)}/p,\qquad p\ne2.}\tag{R11}
$$

这仍包括5。`quotient_trace_identity`、`quotient_trace_zero` 和
`square_period_eq_iff_firstQuotient` 将每一步绑定到实际回归商。
R11 把待证明的算术问题缩到一个明确标量，尚未证明该标量在哪些无穷素数类上为零或非零。

进一步，把 R7 的 $B$ 降到模 $p$，并令

$$
H=\begin{pmatrix}1&2\\2&-1\end{pmatrix},\qquad H^2=5I.
$$

则

$$
\boxed{2B=aH,\qquad (2B)^2=5a^2I.}\tag{R12}
$$

因此 $p\ne2,5$ 且 $a\not\equiv0\pmod p$ 时，$\ker B=0$。
源码 `twice_normalizedDefect`、`scaled_defect_square` 和
`normalizedDefect_kernel_zero` 给出矩阵与坐标证明。
这显示5的例外来自判别式方向的退化。它不是任意添加的特殊数字。

在写作层面，R7与R12还意味着：对于模 $p^2$ 的状态 $v$，
经过旧周期 $r$ 的差为 $pBv$；在上述非退化条件下，若 $v\bmod p\ne0$，
则这个差在模 $p^2$ 下非零。因此旧层的回归不能延续到该具体状态的新层。
这项推论只判断旧周期是否仍回归，不声称仅凭差值恢复任意模 $p^2$ 的完整状态。

### R.7 对2026年文献一个明确猜想的反驳

Shi、Wang、Bouazzaoui、Kim、Solé [R-ref3] 第4.3节将模 $p$ 的
$(X-1)^2$ 因子讨论延伸到模 $p^2$，并猜测提升后的系数可以原样取
$a=-2,b=1$。该文明确说，这个系数猜想并非后续论证的必要前提。

对每个整数 $n>1$，有一个更一般的障碍：

$$
\boxed{(X-1)^2\nmid X^n-1\quad\text{于 }(\mathbb Z/n^2\mathbb Z)[X].}\tag{R13}
$$

证明：若 $X^n-1=(X-1)^2g(X)$，形式求导并代入 $X=1$，
右侧为0，左侧为 $n$。这要求 $n^2\mid n$，与 $n>1$ 矛盾。
该论证适用于有零因子的系数环，不使用域上的重根判定来偷换环境。

`unchanged_double_root_not_dvd` 给出全称反驳；
`conjectured_quadratic_not_dvd` 明确将文献的 $X^2-2X+1$ 绑定到被排除的平方。
因此第4.3节的原样系数猜想为假。
本结果没有排除其它系数的提升，也不否定该文全部定理，更不解决 WSS 素数存在性。

同文引言与第3节关于 $p$-rationality 的等价方向存在措辞冲突；
本附录没有将其中任何一条未经单独核验的数域结论作为 Lean 前提。

### R.8 文献边界、实际产出和下一步

| Lean 模块 | 本轮证明脚本提供的内容 |
|---|---|
| `FibonacciReturnSpectrum` | 真实序列与矩阵周期、回归内容量、整除对偶、gcd/lcm律 |
| `GoldenModReturnBridge` | 现役黄金剩余环的忠实矩阵作用及单位阶等价 |
| `FibonacciPrimeSquareLift` | 实际首次缺陷、平方零提升、最小周期二分律、双商判据 |
| `FibonacciLiftTrace` | 奇素数偶周期、整迹等式、单商判据、判别式5方向及核为零 |
| `PrimeSquareDoubleRootObstruction` | 对指定文献系数猜想的全称多项式反驳 |

路径统一为 `D5/S1/Recurrence/`，每个文件有对应的
`Blueprint/D5/S1/Recurrence/*.scribe.cs`。这些脚本消费真实定义并构造证明，
没有把周期二分、返回等价或缺陷消失作为输入结构字段。

本轮没有证明 `∃p, π(p)=π(p²)`，也没有证明其否定。
经典周期定理的形式化属于建立可核验研究基础；R13则处理了一个具体已发表猜想。
下一条算术研究应继续约束 R11 的标量，而非继续给同一阶定义改名。

首先，结合已有黄金 Frobenius 与分裂/惰性定理，将
$F_{\pi(p)}/p\pmod p$ 与标准索引
$F_{p-(5/p)}/p\pmod p$ 之间的非零比例关系证明出来，明确排除2、5并追踪比例是否可逆。
这能让局部判据直接消费文献关于 Fibonacci 商的算术信息。
其次，对固定奇素数，证明回归缺陷的 $p$-进估值如何随时间倍增，
把全部 $p^e$ 周期统一约化为第一次非零层；该规律本身仍须先库后证并标明经典来源。
最后，真正朝存在性推进的结果需要对跨素数的商值零集合给出新约束，
或者构造并验证一个使其为零的素数，有限小范围未发现例子不完成这一目标。

圆和傅立叶仍有精确的后续接口：有限模状态上的角色函数在 $Q$ 作用下由转置矩阵运输，
周期分解控制有限轨道频率。上述源没有交付新的 Fourier 分解定理，
也没有把有理有限周期与实数黄金旋转的无理相位当作同一动力系统。
5040的约数资源最优性属于另一条已有变分定理，本附录没有据周期关系重宣称其全局计算最优。

### R.9 文献

[R-ref1] D. D. Wall. *Fibonacci Series Modulo m*. American Mathematical Monthly 67 (1960), 525–532.
DOI: https://doi.org/10.2307/2309169 。本附录的周期提升定位参照该经典题目及[R-ref3]的明确引用。

[R-ref2] Dan Guyer and aBa Mbirika. *GCD of sums of k consecutive Fibonacci, Lucas, and generalized Fibonacci numbers*.
Journal of Integer Sequences 24 (2021), Article 21.9.8. arXiv:2104.12262v2, 2021-11-07.
https://arxiv.org/abs/2104.12262v2 。摘要同时列出回归差的gcd与兼容模数的lcm表达式；
对标准Fibonacci初值，其gcd与本文 $C_t$ 由一次欧几里得变换相等。

[R-ref3] Minjia Shi, Xuan Wang, Bouazzaoui Zakariae, Jon-Lark Kim, Patrick Solé.
*Second order Recurrences, quadratic number fields and cyclic codes*. arXiv:2603.25343v1, 2026-03-26.
https://arxiv.org/html/2603.25343v1 。第1、3、4节用于问题定位；
第4.3节的原样双根提升系数猜想是R13的精确反驳对象。

[R-ref4] 仓库 `LucasEvenDescent.lean`、`LucasCompanion.lean`、`GoldenApparition.lean`；
mathlib `Data/ZMod/Basic.lean`、`GroupTheory/OrderOfElement.lean`、
`Algebra/Polynomial/Derivative.lean`，依 `lake-manifest.json` 固定到
`db584cd6d46c92f209a44c0f1c829460d327499d`。


### R.10 Conditional Frobenius-quotient bridge

The next formal interface is now recorded as D5/S1/Recurrence/FibonacciFrobeniusQuotientBridge. For a prime p != 2,5, define Q_p(n)=F_n/p mod p using the repository's natural-number quotient. The existing GoldenApparition.fibonacci_apparition_entry_point proves that p divides F_(p-(5/p)), with the signed Legendre index converted to its natural form, while FibonacciRank proves that the least positive zero divides this index.

The new theorem is deliberately conditional:

$$Q_p(pi(p)) = 1 * Q_p(p-| (5/p) |)$$

under the hypothesis pi(p)=p-| (5/p) |. The proportionality factor is explicitly 1, and quotient_period_eq_frobenius_factor_isUnit proves it is a unit in every ZMod p, including the exceptional characteristics. The hypotheses p != 2,5 belong to the index-identification interface, not to the unit lemma. This separates what is already forced by the current Frobenius/splitting library from the genuinely open step: proving a nontrivial Lucas multiplier for a return period that is only known to divide the Frobenius index. No unconditional equality of the two quotients, and no nonzero-quotient claim, is asserted without that missing period equality.

### R.11 对 R.10 的勘误及两个问题的精确定义

R.10 的绝对值索引及其附带源声明不能承担标准 Frobenius 桥。对惰性素数，标准索引为 $p+1$；$p-| (5/p) |$ 却恒为 $p-1$。例如 $p=3$ 时，错误索引给 $F_2=1$，而标准索引给 $F_4=3$。此外，实际周期通常不等于标准索引；$\pi(3)=8$ 而标准索引为4。R.10 中“return period ... divide the Frobenius index”也不能作为一般事实，正确统一界是 $\pi(p)\mid2(p-(5/p))$。此前源中的 $p\ne2,5\Rightarrow p\ge7$ 同样漏掉3。

本节保留 R.10 作为历史文本，其数学接口由 R.12–R.16 取代。对应 Lean 和 Scribe 已用真实桥接替换条件重写；不再假设两个索引相等，也不再将系数人为置为1。

以下对 $p\ne2,5$ 的素数定义

$$
\epsilon_p=\left(\frac5p\right),\quad n_p=p-\epsilon_p,\quad r_p=\pi(p),\quad
\eta_p=\frac{F_{r_p}}p\bmod p,\quad q_p=\frac{F_{n_p}}p\bmod p.
$$

mathlib 的 `legendreSym 5 p` 采用分母在前的记号，它是 $(p/5)$；对这里的奇素数，二次互反使其等于 $(5/p)$。Lean 定义 `frobeniusIndex p = ((p : Int) - epsilon p).toNat`，并证明该整数为正及回转整数等式。不会先取绝对值。

第二个问题使用真实的首次回归深度

$$
s_p=\nu_p(C_{r_p}),\qquad C_t=\gcd(F_t,F_{t+1}-1).
$$

$C_{r_p}>0$ 且 $p\mid C_{r_p}$，因此 $s_p$ 是有限正整数。它不是自由输入的“平台长度”。

### R.12 第一项：准确比例为负的最小周期

**定理 R14。** 对每个素数 $p\ne2,5$，

$$
\boxed{\eta_p=-r_p q_p\quad\text{于 }\mathbb F_p,\qquad -r_p\in\mathbb F_p^\times.}
\tag{R14}
$$

证明先在现役黄金环内完成。设 $x=a+b\varphi$ 且 $p\mid b$。在模 $p^2$ 下，$b^2=0$，逐次乘法归纳得到

$$
(x^k).a=a^k,\qquad (x^k).b=k a^{k-1}b\pmod{p^2}.
$$

这对全部自然数 $k$ 成立，$k=0$ 时右侧因子 $k$ 为零。若两个黄金整数 $x,y$ 的系数分别为 $pA,pB$，且 $x^k=y^l$，就有

$$
k x.a^{k-1} A=l y.a^{l-1}B\pmod p.
\tag{R15}
$$

约去 $p$ 的步骤在整数整除见证中进行，未把 $p$ 当作模 $p^2$ 的单位。`GoldenFirstOrderTransport` 实现这组一般系数公式。

现役 Frobenius 定理给 $F_{n_p}=0$、$F_p=\epsilon_p\pmod p$，结合递推与原黄金幂坐标式得到

$$
\varphi^{n_p}=\epsilon_p\pmod p,\qquad \varphi^{r_p}=1\pmod p.
$$

比较始终相等的两项

$$
(\varphi^{r_p})^{n_p}=(\varphi^{n_p})^{r_p}
$$

并应用 R15，得到

$$
n_p\eta_p=r_p\epsilon_p^{r_p-1}q_p\pmod p.
$$

由奇素数下的行列式约束，$r_p$ 为偶数，所以 $\epsilon_p^{r_p-1}=\epsilon_p$；又 $n_p=-\epsilon_p\pmod p$。约去 $\epsilon_p=\pm1$，得到 R14 的等式。

单位性也由真实周期证明：$\varphi^{2n_p}=1\pmod p$ 意味着 $r_p\mid2n_p$。由于 $p$ 为奇数且 $n_p\equiv-\epsilon_p\ne0\pmod p$，故 $p\nmid r_p$。不需要假设 $r_p=n_p$，也不需要先分类 $r_p/n_p$。

例如 $p=7$ 时，$n_p=8,r_p=16$，标准商为3，周期商为1，而 $-r_p\equiv5\pmod7$，确有 $5\cdot3=1\pmod7$。这说明系数通常不是1。

结合 R11，得到真正的标准 WSS 判据：

$$
\boxed{\pi(p^2)=\pi(p)\iff q_p=0.}\tag{R16}
$$

对应声明：`quotient_period_eq_frobenius`、`quotient_period_eq_frobenius_factor_isUnit`、`wall_iff_standard_quotient`。它们均排除2和5，不对非单位进行约分。5的高次周期由 R.15 另外处理。

### R.13 第二项的局部引擎：精确缺陷深度

使用既有黄金整数环 $\mathcal O=\mathbb Z[\varphi]$。标量 $p$ 整除一个黄金整数，当且仅当同时整除其两个整数坐标。

**定理 R17。** 设 $p$ 为素数，$s>0$，$s+2\le ps$，$B\in\mathcal O$ 且 $p\nmid B$。则对每个 $j\ge0$，存在 $D_j\in\mathcal O$ 使

$$
\boxed{
(1+p^sB)^{p^j}=1+p^{s+j}(B+pD_j).
}\tag{R17}
$$

因此该差恰被 $p^{s+j}$ 整除，而不被 $p^{s+j+1}$ 整除。

证明复用钉版 mathlib 的 `ZMod.exists_one_add_mul_pow_prime_pow_eq`。尽管名称位于 `ZMod`，该定理的系数类型是任意交换半环，此处实例化为 $\mathcal O$，取 $u=p^s,v=p$。其两个整除前件分别为 $p\mid p^s$ 和 $p^{s+2}\mid p^{sp}$，正是当前假设。该库定理使用素数二项系数的整除性质，包括最高次端点。余项 $B+pD_j$ 模 $p$ 与 $B$ 相同，故仍为原始系数。标量约分通过整数坐标单射性完成。

对奇素数，$s\ge1$ 就满足 $s+2\le ps$；对2，需要 $s\ge2$。这个差异说明不能将深度一的奇素数证明直接应用到二进情形。

由准确深度可得：$1+p^sB$ 模 $p^{s+j}$ 的阶恰为 $p^j$。上界由 R17 给出；$j>0$ 时，低一次的 $p^{j-1}$ 幂仍有非零差，排除全部更小的素数幂阶。对应 `exact_depth_after_prime_power` 和 `reduced_order_at_depth`。

### R.14 完整奇素数周期塔

**定理 R18。** 对任意奇素数 $p$ 与任意 $e\ge1$，

$$
\boxed{\pi(p^e)=r_p\,p^{\max(e-s_p,0)},\qquad s_p=\nu_p(C_{r_p}).}\tag{R18}
$$

证明不假设 $s_p=1$。从 $C_{r_p}$ 的真实估值构造

$$
\varphi^{r_p}=1+p^{s_p}B,\qquad p\nmid B.
$$

该构造由 `actual_initial_seed` 完成：利用 $p^{s_p}\mid C_{r_p}$、$p^{s_p+1}\nmid C_{r_p}$ 与原黄金单位的降模桥，得到两个整数坐标的共同最大 $p$ 幂。

若 $e\le s_p$，原周期已经在模 $p^e$ 下回归，所以新周期整除 $r_p$；降模又给反向整除，故两周期相等。

若 $e=s_p+j$，R17 证明 $\varphi^{r_p}$ 模 $p^e$ 的阶为 $p^j$。设 $T=\pi(p^e)$，降模给 $r_p\mid T$，于是群元素幂的阶公式给

$$
\operatorname{ord}(\varphi^{r_p})
=\frac{T}{\gcd(T,r_p)}=\frac{T}{r_p}=p^j.
$$

这就得到 R18。没有用上界替代最小周期，也没有将初始缺陷不为零当作未证明前件。

将 R16 与估值定义合并：

$$
\boxed{q_p=0\iff s_p\ge2,\qquad p\ne2,5.}\tag{R19}
$$

所以标准商非零会同时确定所有高次周期：

$$
q_p\ne0\Longrightarrow\forall e\ge1,\quad
\pi(p^e)=\pi(p)p^{e-1}.
$$

若未来得到一个 $s_p>1$ 的素数，R18 同样适用：前 $s_p$ 层保持 $r_p$，之后每增加一层都乘 $p$。这不是例外素数存在性证明，而是对任意实际初始深度的统一结论。

### R.15 二进与分歧素数的全部层级

**定理 R20。** 对每个 $e\ge1$，

$$
\boxed{\pi(2^e)=3\cdot2^{e-1},\qquad
\pi(5^e)=20\cdot5^{e-1}.}\tag{R20}
$$

二进证明使用真实种子

$$
\pi(2)=3,\quad\pi(4)=6,\quad
\varphi^6=1+4(1+2\varphi).
$$

$1+2\varphi$ 不被2整除，故从深度2应用 R17。得到 $e\ge2$ 时周期为 $6\cdot2^{e-2}$，与单独验证的 $e=1$ 合并即为第一式。

对5，使用

$$
\pi(5)=20,\qquad
\varphi^{20}=1+5(836+1353\varphi).
$$

括号内两个坐标不同时被5整除，因此是深度1的真实种子；R17 给出全部层级。这里不使用分裂/惰性分类，也不约去模5下为零的 $-\pi(5)$。

有限种子证明直接消费于两个无界指数定理，没有作为独立有限正例模块发布。模数 $p^0=1$ 的周期为1，明确不属于 R18、R20 的 $e\ge1$ 公式。

### R.16 两项成果的依赖、文献边界与剩余算术问题

新增 `GoldenFirstOrderTransport`、`GoldenPrimePowerDepth`、`FibonacciPrimePowerPeriod`，并替换错误的 `FibonacciFrobeniusQuotientBridge`，均位于 `D5/S1/Recurrence/`；每个源都有同名 Blueprint Scribe。

第一条主链是已有 Frobenius、实际黄金幂坐标、模 $p^2$ 一阶输运，再到可逆系数 $-\pi(p)$。第二条主链是实际回归内容量、原始缺陷构造、既有素数幂二项式定理、真实元素阶，最后到全部 $p^e$ 周期。两者由 R19 连接。

本节给出完整普通数学证明及 Lean 证明脚本。当前工作环境未执行 Lean/lake 或 Scribe 编译，故这些新增源不能列为已获 kernel 认证或已冻结结论。独立有限检查与源码复核不能代替该环节。

经典 $p$-进估值与提升规律已见 Wall、Lengyel 及后续研究。本节不将其宣称为新发现。Medina–Rowland [R-ref5] 的定理1.4列出 Lengyel 的 Fibonacci 估值公式，并单独处理2和5；本节以实际回归内容量为初始数据，复用已形式化的通用二项式引理完成另一条与本库载体一致的证明路线。

现在两个约定的桥接问题均已有全称陈述和证明脚本。WSS 存在性剩余的是跨素数的 $q_p$ 零集合，或者等价的实际 $s_p\ge2$ 条件的算术分析。R18 已经说明，高次层级自身不会额外提供一个独立自由参数。下一条有意义的推进应约束初始深度在素数族中的行为，或将标准商与已有数域/局部单位命题建立经过证明的连接，不能把再次写出同一提升公式计作存在性进展。

[R-ref5] Luis A. Medina and Eric Rowland, *p-regularity of the p-adic valuation of the Fibonacci sequence*, The Fibonacci Quarterly 53 (2015), 265–271. arXiv:0910.2907v4, Theorem 1.4 (Lengyel). https://arxiv.org/abs/0910.2907v4

[R-ref6] Mathlib, `Mathlib/RingTheory/ZMod/UnitsCyclic.lean`, `exists_one_add_mul_pow_prime_eq` and `exists_one_add_mul_pow_prime_pow_eq`; `Mathlib/GroupTheory/OrderOfElement.lean`, `orderOf_eq_prime_pow` and `orderOf_pow'`; `Mathlib/NumberTheory/Padics/PadicVal/Defs.lean`, `pow_dvd_iff_le_padicValNat`. Pinned revision: `db584cd6d46c92f209a44c0f1c829460d327499d`. These are imported proof dependencies rather than assumed conclusion fields.

### R.17 任意时间倍数的精确回归深度

R18 还能控制任意时间倍数，超出只考察 $p^j$ 倍时间的局部展开。令 $p$ 为奇素数、$r_p=\pi(p)$、$s_p=\nu_p(C_{r_p})$。对全部 $k\ge0,e\ge1$，有

$$
\boxed{p^e\mid C_{r_pk}\iff p^{\max(e-s_p,0)}\mid k.}\tag{R21}
$$

证明：由 R5，左侧等价于 $\pi(p^e)\mid r_pk$。代入 R18，再在自然数整除见证中约去正整数 $r_p$，得到右侧。对应 `returnContent_multiple_power_dvd`。$k=0$ 时，两侧都成立；没有将零时间误当成有限深度。

对 $k>0$，取 $d=s_p+\nu_p(k)$。R21 在 $e=d$ 时成立，在 $e=d+1$ 时失败，因此

$$
\boxed{\nu_p(C_{r_pk})=s_p+\nu_p(k).}\tag{R22}
$$

对应 `returnContent_multiple_valuation`。源码先证明 $C_{r_pk}\ne0$，再使用两次整除判定界定估值，避免 `padicValNat` 在零点的默认值。该公式包括奇素数5；二进分支仍由 R20 单独处理。

R22 的内容是明确的时间与分辨率交换律：重复旧周期的次数只有其 $p$ 因子数会增加回归深度，与 $p$ 互素的额外重复不改变深度。每个固定素数的全部高次层级，因而被一个实际初始深度控制。这说明继续改变 $e$ 或时间倍数不能凭空增加关于跨素数例外性的独立条件。

实现中，标准商明确写作 `((Nat.fib n / p : Nat) : ZMod p)`，先在自然数中整除，再降模。符号方向另由 `epsilon_eq_standard` 消费钉版 `legendreSym.quadratic_reciprocity_one_mod_four` 证明，故 $(p/5)=(5/p)$ 已是实际声明而非只靠散文约定。

### R.18 向跨素数问题继续推进的文献接口

Jones [R-ref7] 给出 $k$-Wall–Sun–Sun 条件与 $X^{2p}-kX^p-1$ 的非单生成性之间的等价，在 $k\not\equiv0\pmod4$ 且相应判别式平方自由的条件下成立。黄金情形 $k=1$ 的判别式为5，满足这些条件。该结果为当前 $q_p=0$ 判据提供一个有明确原文定理的数域方向。

下一条可核验目标是将本节的标准商零条件，与该文黄金特化中实际多项式、数域整数环及幂整基指标的条件连接。其价值在于引入来自数域整数环的额外算术信息；仅仅复述等价关系本身不证明零集合非空。本附录当前没有交付该整数环指标的 Lean 桥，也没有给 WSS 存在性或无穷性设置解决标记。

[R-ref7] Lenny Jones, *A new condition for k-Wall-Sun-Sun primes*, arXiv:2302.10357v4, 2023-07-15. https://arxiv.org/abs/2302.10357v4 。上述方向引用其实际黄金特化，未把一般 Lucas 参数下的假设删除。

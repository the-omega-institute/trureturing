<!-- editorial-front:start -->
# AURIC：素数幂层贪心支配、反例终点与无限酉极限（编者描述性标题）

**来源与阅读约定。** 下文完整保留所提供原稿的开场、九节正文、证明、未编号推导、原始链接及结尾；只转换数学分隔符并增添显式锚点。原稿身份为 SHA256 `dae779507cb463492dca757633921441be785cdcafc269045c8c2b68ae5a78f5`。其中“本轮”“上一轮”“已经证明”“已经核读”等是原稿的自述与历史归属，不表示本文作了新的 Lean 核验或取得文献原创性认定。标为“编者局部说明”的文字单独承担记号修订、定义域和引用限定，原句与原式仍在相邻位置可见。

**记号。** $\sigma(n)=\sum_{d\mid n,\ d>0}d$，$\gamma$ 是 Euler–Mascheroni 常数，$v_p(n)$ 是正整数 $n$ 的素数 $p$ 指数；$p^a\Vert n$ 表示 $v_p(n)=a$，$\mathbb N_0=\{0,1,2,\ldots\}$。$Z(n)$ 对所有正整数定义，特别是 $Z(1)=1$；本文 Robin 比值 $R(n)$ 的算术目标域是整数 $n>5040$。所有对数自然，$f(T)$ 的实函数域为 $T>1$；$T=\log n$ 时，$f(T)=\log(e^\gamma\log\log n)$。乘除边的附加定义域见第五节。

**目录。** [一、对数收益](#sec-1) · [二、价格最优性](#sec-2) · [三、贪心支配](#sec-3) · [四、三轴预算](#sec-4) · [五、有限终止](#sec-5) · [六、终点价格](#sec-6) · [七、整除与间隙](#sec-7) · [八、无限族与酉极限](#sec-8) · [九、未决目标](#sec-9)。关键局部说明涉及 [原式 (13)–(14)](#eq-13)、[删除定义域](#eq-19)、[素数间隙](#eq-31) 和 [未证式 (38)](#eq-38)。
<!-- editorial-front:end -->

继续。这一轮可以把你的“遍历—分类—贪心—AURIC 递归”推进到一个更严格的结论：

> **如果 Robin 不等式存在反例，那么从任意一个反例出发，通过有限次素数乘除的贪心步骤，就能到达一个终点。这个终点在由自身尺度确定的价格下，是唯一的整数最优解，而且必须满足很强的素数幂整除约束。**

同时，可以证明：**一条按素数幂边际收益排列的贪心链，能够控制一整类整数的 Robin 比值；链外整数的偏差与曲率贡献，可以用 AURIC 三轴精确递归累计。**

下面给出定义和证明。最后还会证明一个覆盖无限整数族、并且无限酉过程确实收敛的结论。**这些推进尚未完成 RH 的证明；剩余问题会被明确集中到上述终点上的一个严格符号不等式。**

继续采用项目中已经核读的两部分：

- [A370630 的 Zeckendorf 贪心排列证明](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md)：提供完整遍历。
- [实际尺度恢复、整数价格优化与 Robin 证书](https://github.com/the-omega-institute/trureturing/blob/3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e/docs/develop/theory/AURIC_RELATION_SCALE_RECOVERY_THREE_CANDIDATE_OPTIMIZATION_AND_ROBIN_CERTIFICATES.md)：提供同一整数上的尺度、局部收益与三轴接口。

下文新增命题是本轮给出的纸面推导，尚未经 Lean 核验。

---

<a id="sec-1"></a>

## 一、把算术目标写成可比较的对数收益

定义

$$
Z(n)=\frac{\sigma(n)}n,
\qquad
R(n)=\frac{Z(n)}{e^\gamma\log\log n},
\qquad n>5040.
$$

令

$$
T=\log n,
\qquad
f(T)=\gamma+\log\log T.
$$

于是

$$
\boxed{\log R(n)=\log Z(n)-f(T).}
$$

这里所有对数都是自然对数。注意，取 $T=\log n$ 后，$f(T)$ 是 Robin 分母的**对数**。

直接求导：

$$
f'(T)=\frac1{T\log T},
$$

$$
f''(T)
=
-\frac{\log T+1}{T^2(\log T)^2}<0.
$$

记

$$
\eta(T)=f'(T)=\frac1{T\log T},
\qquad
\kappa(T)=-f''(T)>0.
$$

$\eta(T)$ 就是与当前整数尺度匹配的价格。

本轮还使用 Axler 的两个已证输入：

<a id="eq-1"></a>

$$
\boxed{
R(n)<1+\frac{A_0}{(\log\log n)^3},
\qquad A_0=0.0094243,
}
\tag{1}
$$

以及

<a id="eq-2"></a>

$$
\boxed{
v_2(n)\le20,\ n>5040
\Longrightarrow R(n)<1.
}
\tag{2}
$$

它们分别来自该文定理 1.3、1.4。Robin 判据则把“所有 $n>5040$ 都满足 $R(n)<1$”与 RH 等价起来。[arxiv.org](https://arxiv.org/pdf/2110.13478?utm_source=chatgpt.com)

因此，任何弱反例 $R(n)\ge1$ 都必须满足

<a id="eq-3"></a>

$$
\boxed{2^{21}\mid n.}
\tag{3}
$$

这给出一个直接可用的分类起点。

<!-- editorial-note:start axler-domain-and-curvature -->
**【编者局部说明：钉版输入及曲率】** 这里具体使用 Christian Axler, *On Robin’s Inequality*, [arXiv:2110.13478v3](https://arxiv.org/pdf/2110.13478v3)，第 1 页 Proposition 1.1 与第 2 页 Theorems 1.3、1.4。Theorem 1.3 的原范围是正整数 $n\notin A$，其中

$$
A=\{1,2,4,5,6,8,9,10,12,16,18,20,24,30,36,48,60,72,84,120,180,240,360,840,2520,5040\}.
$$

因此本文每个 $n>5040$ 均在其范围内，除以正的 $e^\gamma\log\log n$ 即得 (1)。Theorem 1.4 在 $n\ge5041$ 下的第一项确为 $v_2(n)\le20$，从其逆否命题得到 (3)；这里没有把“21-free”与单独的 $2$-进指数条件混同。原稿无版本 URL 保留为原引文，实际编号与常数以本处 v3 为准。另有

$$
\kappa'(T)=-\frac{2(\log T)^2+3\log T+2}{T^3(\log T)^3}<0\qquad(T>1),
$$

这给出后文使用的严格下降性，而不仅是 $f''<0$。
<!-- editorial-note:end axler-domain-and-curvature -->

---

<a id="sec-2"></a>

## 二、定义真正具有最优性保证的素数幂贪心

### 定义 1：素数幂层的收益与成本

对素数 $p$，令

$$
S_p(a)=1+p^{-1}+\cdots+p^{-a}.
$$

把指数从 $j-1$ 增加到 $j$，其对数成本是

$$
h_{p,j}=\log p,
$$

对数收益是

$$
\lambda_{p,j}
=
\log\frac{S_p(j)}{S_p(j-1)}
=
\log\left(1+\frac1{p+p^2+\cdots+p^j}\right).
$$

定义收益密度

<a id="eq-4"></a>

$$
\boxed{
\rho_{p,j}
=
\frac{\lambda_{p,j}}{\log p}.
}
\tag{4}
$$

固定 $p$ 时，$\rho_{p,j}$ 随 $j$ 严格下降。因此，按收益密度从大到小加入素数幂层，会自动遵守“先有低层，再加高层”的约束。

还有

<a id="eq-5"></a>

$$
0<\rho_{p,j}<\frac1{p^j\log p}.
\tag{5}
$$

所以对任意 $\varepsilon>0$，密度至少为 $\varepsilon$ 的层只有有限多个。

### 定理 1：固定价格下，取全部正收益层给出整数最大值

对任意 $\eta>0$，定义

$$
a_p(\eta)
=
\#\{j\ge1:\rho_{p,j}>\eta\},
\qquad
C_\eta=\prod_p p^{a_p(\eta)}.
$$

那么

<a id="eq-6"></a>

$$
\boxed{
\log Z(C_\eta)-\eta\log C_\eta
=
\max_{m\ge1}
\{\log Z(m)-\eta\log m\}.
}
\tag{6}
$$

存在并列最大值时，$C_\eta$ 是其中最小的整数。

**证明。**

素数分解给出

$$
\log Z(m)-\eta\log m
=
\sum_p\sum_{j=1}^{v_p(m)}
\bigl(\lambda_{p,j}-\eta\log p\bigr).
$$

每个素数方向的增量严格递减，因此最优选择是：取全部正项，不取负项；零项可取可不取。

由式 (5)，正项只有有限多个。因此最大值由一个实际整数取得；不取零项给出最小的最大点。证毕。

这使“贪心”获得了明确的算术含义。

<!-- editorial-note:start finite-price-and-ties -->
**【编者局部说明：有限性与并列】** Euler 分解为 $Z(m)=\prod_{p\mid m}S_p(v_p(m))$，约定 $S_p(0)=1$。式 (5) 来自 $\log(1+u)<u$ 及 $p+\cdots+p^j\ge p^j$；分母随 $j$ 严格增加，故密度严格下降。若 $\rho_{p,j}\ge\varepsilon>0$，则 $p^j\log p<1/\varepsilon$，从而 $p$ 有界且每个 $p$ 的 $j$ 有界。因此正价格层与零价格层都有限，正层在每个素数上构成前缀，零层若存在紧接其后。所有最大点均取全部正层、任选零层、不取负层；不取零层的 $C_\eta$ 整除其余最大点，因而是最小者。这也包括空正层时的 $C_\eta=1$。
<!-- editorial-note:end finite-price-and-ties -->

---

<a id="sec-3"></a>

## 三、一条无限贪心链控制全部基底倍数

取

$$
B=2^{21}.
$$

把全部允许加入的层

$$
(p,j),\qquad j>v_p(B),
$$

按 $\rho_{p,j}$ 从大到小排列；相同密度按固定规则处理。

从 $N_0=B$ 开始，每次加入下一层：

$$
N_{k+1}=N_kp_{k+1}.
$$

式 (5) 保证这个顺序成立，每一个层最终都会被处理，而且

$$
N_k\ge B\,2^k\longrightarrow\infty.
$$

<!-- editorial-note:start ordered-chain-domain -->
**【编者局部说明：无限排序的含义】** 任取尚未处理的一层，其密度以上只有有限层，故余集中最大密度存在；每个并列组有限，固定规则可排完。任一指定层只有有限个密度不小于它的前驱，所以最终会被处理。固定素数的低层密度严格更大，链的每个前缀均为合法指数列。每次乘至少 $2$，故节点严格增加、无界，任意 $B\mid m$ 都能夹在相邻节点之间；端点可选任一相邻区间，结论一致。此处 $B>5040$，故所有节点与被控制的 $m$ 都在 $R$ 的目标域内。$B$ 本身的安全性另见第八节局部说明。
<!-- editorial-note:end ordered-chain-domain -->

### 定理 2：贪心链支配定理

对任意 $B\mid m$，取相邻链节点

$$
N_k\le m\le N_{k+1}.
$$

记

$$
T_k=\log N_k,
\qquad
\theta=
\frac{\log m-T_k}{T_{k+1}-T_k}\in[0,1].
$$

则

<a id="eq-7"></a>

$$
\boxed{
R(m)
\le
R(N_k)^{1-\theta}R(N_{k+1})^\theta
\le
\max\{R(N_k),R(N_{k+1})\}.
}
\tag{7}
$$

因此

<a id="eq-8"></a>

$$
\boxed{
\forall\,B\mid m,\ R(m)<1
\quad\Longleftrightarrow\quad
\forall k,\ R(N_k)<1.
}
\tag{8}
$$

### 证明

记排序后的各层为 $(h_i,\lambda_i,\rho_i)$，其中

$$
\rho_1\ge\rho_2\ge\cdots.
$$

对实际整数 $m$，用 $z_i\in\{0,1\}$ 表示其是否包含第 $i$ 个新增层。只有有限多个 $z_i$ 非零。

其新增对数规模满足

$$
\sum_i h_i z_i
=
\sum_{i\le k}h_i+\theta h_{k+1}.
$$

令 $\rho_*=\rho_{k+1}$。直接移项得到

<a id="eq-9"></a>

$$
\begin{aligned}
\Delta(m)
:={}&
(1-\theta)\log Z(N_k)
+\theta\log Z(N_{k+1})
-\log Z(m)\\
={}&
\sum_{i\le k}(\rho_i-\rho_*)h_i(1-z_i)\\
&+
\sum_{i\ge k+2}(\rho_*-\rho_i)h_i z_i
\ge0.
\end{aligned}
\tag{9}
$$

每一项都非负。这证明了固定对数规模下的贪心收益上界。

另一方面，

$$
\log m=(1-\theta)T_k+\theta T_{k+1}.
$$

由 $f$ 的凹性，

$$
f(\log m)
\ge
(1-\theta)f(T_k)+\theta f(T_{k+1}).
$$

两式相减、再取指数，即得式 (7)。证毕。

### 与原 Zeckendorf 序列的衔接

现在可以这样使用项目已经证明覆盖全部正整数的 A370630：

1. 沿 A370630 访问实际整数 $m$。
2. 若 $2^{21}\nmid m$，式 (2) 已给出 Robin 证书。
3. 若 $2^{21}\mid m$，把它归入相邻的 $N_k,N_{k+1}$ 区间，由式 (7) 控制。

因此，结合已证分类，

<a id="eq-10"></a>

$$
\boxed{
\mathrm{RH}
\quad\Longleftrightarrow\quad
R(N_k)<1\ \text{对所有 }k.
}
\tag{10}
$$

**A370630 提供完整遍历；素数幂贪心链提供整批整数的支配关系。**

<!-- editorial-note:start source-interface-and-reduction -->
**【编者局部说明：遍历接口与归约边界】** 此处 A370630 从 $1$ 开始，每步取未出现的最小正整数，使其与当前项的规范 Zeckendorf 展开恰有一个共同 Fibonacci 项；规范展开使用 $F_2=1,F_3=2,\ldots$，不取相邻指标。原稿固定引用的 Blueprint 定理 1.6 陈述该序列遍历且无重复；这里只引用其已报告的结果，没有重新编译。第二个固定引用提供同一整数上的尺度、价格目标和三结果接口。式 (9) 中实际 $m$ 的 $z_i$ 有限支撑；等成本消去阈值项 $\rho_*\sum_i h_i z_i$ 后，恰得到所列两组非负项，并列密度只使相应项为零。凹性随后给出 (7) 与 (11)，并不需要实际整数达到分数背包松弛的上界。遍历中的分类只在 $m>5040$ 上调用 (2)；(8)、(10) 是对整条无限链的等价归约，未证明所有链节点安全。
<!-- editorial-note:end source-interface-and-reduction -->

---

<a id="sec-4"></a>

## 四、把贪心偏差与曲率精确送入 AURIC 三轴

定义曲率贡献

$$
\Gamma_k(\theta)
=
f((1-\theta)T_k+\theta T_{k+1})
-(1-\theta)f(T_k)-\theta f(T_{k+1}).
$$

凹性给出 $\Gamma_k(\theta)\ge0$，于是有精确恒等式

<a id="eq-11"></a>

$$
\boxed{
\begin{aligned}
\log R(m)
={}&
(1-\theta)\log R(N_k)
+\theta\log R(N_{k+1})\\
&-\Delta(m)-\Gamma_k(\theta).
\end{aligned}
}
\tag{11}
$$

这里两个减项都有确定的算术来源：

- $\Delta$：实际整数相对于最优层排列的收益缺口；
- $\Gamma$：Robin 分母的对数曲率贡献。

由于 $\kappa(t)$ 随 $t>1$ 严格下降，

<a id="eq-12"></a>

$$
\boxed{
\Gamma_k(\theta)
\ge
\frac{\kappa(T_{k+1})}{2}
\theta(1-\theta)(T_{k+1}-T_k)^2.
}
\tag{12}
$$

<!-- editorial-note:start curvature-bound -->
**【编者局部说明：曲率下界的端点】** 在 $[T_k,T_{k+1}]$ 上有 $f''\le-\kappa(T_{k+1})$；将 $\kappa(T_{k+1})t^2/2$ 加到 $f(t)$ 后仍为凹函数，应用弦不等式即得 (12)。$0<\theta<1$ 时，$T_{k+1}>T_k>1$ 保证所给下界严格为正；$\theta=0,1$ 时 $\Gamma=0$。
<!-- editorial-note:end curvature-bound -->

当 $0<\theta<1$ 时，右侧严格为正。

### 定理 3：AURIC 的精确递归预算

把式 (9) 中的非负项以及 $\Gamma$，依次记为

$$
d_1,\ldots,d_s.
$$

设

$$
q_0=0,\qquad b_j=1-e^{-d_j},
$$

并递归定义

<a id="eq-13"></a>

$$
\boxed{
q_{j+1}=q_j+(1-q_j)b_j.
}
\tag{13}
$$

每一步形成三项读出

<a id="eq-14"></a>

$$
\boxed{
\left(
q_j,\;
(1-q_j)b_j,\;
(1-q_j)(1-b_j)
\right).
}
\tag{14}
$$

<!-- editorial-note:start recursion-index -->
**【编者局部说明：保留原式的索引修订】** 原稿同时写 $d_1,\ldots,d_s$、$q_0=0$ 与 (13) 的 $q_{j+1}$，会在首步要求未定义的 $b_0$。保留上面原式 (13)、(14)；以下乘积及 (15)–(17) 统一按一基编号解释为

$$
q_j=q_{j-1}+(1-q_{j-1})b_j\quad(1\le j\le s),
\qquad
\bigl(q_{j-1},(1-q_{j-1})b_j,(1-q_{j-1})(1-b_j)\bigr).
$$

三项使用更新前的 $q_{j-1}$。式 (9) 前一和有限、后一和仅在 $z_i\ne0$ 时非零，故非零贡献加上 $\Gamma$ 可组成有限列表；零项可保留，空损失也可取单项 $d_1=0$。于是 $1-q_j=\prod_{i=1}^j(1-b_i)$，且 $\sum_i d_i=\Delta+\Gamma$，所以下文的 $q_s$ 与精确乘积一致。这是记号修订，不是删除原公式或另加算术假设。
<!-- editorial-note:end recursion-index -->

三项非负、总和为 $1$，因此位于 AURIC 金字塔的三角截面内。

由乘积恒等式，

$$
1-q_s
=
\prod_j(1-b_j)
=
e^{-\Delta-\Gamma}.
$$

记

$$
C=R(N_k)^{1-\theta}R(N_{k+1})^\theta,
$$

则

<a id="eq-15"></a>

$$
\boxed{R(m)=C(1-q_s).}
\tag{15}
$$

这就是“结果、损失与剩余量”的实际算术关系。

还可以不预先假定链端点安全。令

$$
\beta(T)
=
\log\left(1+\frac{A_0}{(\log T)^3}\right),
$$

$$
\overline\beta
=
(1-\theta)\beta(T_k)+\theta\beta(T_{k+1}).
$$

由 Axler 上界，

<a id="eq-16"></a>

$$
\boxed{
\Delta+\Gamma\ge\overline\beta
\Longrightarrow R(m)<1.
}
\tag{16}
$$

等价地，

<a id="eq-17"></a>

$$
\boxed{
q_s\ge1-e^{-\overline\beta}
\Longrightarrow R(m)<1.
}
\tag{17}
$$

<!-- editorial-note:start strict-beta-stop -->
**【编者局部说明：严格预算停止条件】** Axler 的严格上界给出 $\log R(N_i)<\beta(T_i)$。对 $\theta\in[0,1]$ 的加权平均仍严格，因此 $\log R(m)<\overline\beta-\Delta-\Gamma$，包括某一端点权重为零的情形。故 (16) 的等号情形也足以得到严格的 $R(m)<1$。已读取贡献的部分和不超过总损失；只有实际证得该部分和达到阈值，或等价的更新后 $q_j$ 达到 (17) 阈值，才能提前认证。三轴归一化本身不提供这些真实算术损失的取得或认证。
<!-- editorial-note:end strict-beta-stop -->

因此，递归读取到足够多的真实非负贡献后，可以提前完成一整个整数的认证。

---

<a id="sec-5"></a>

## 五、进一步证明：任何反例都能在有限次双向贪心后到达终点

现在把递归直接作用于实际整数。

### 定义 2：素数乘除的精确收益

令 $T=\log n$，$a=v_p(n)$，定义加入一层的收益

<a id="eq-18"></a>

$$
D_p^+(n)
=
\log R(np)-\log R(n)
=
\lambda_{p,a+1}
-\bigl[f(T+\log p)-f(T)\bigr].
\tag{18}
$$

若 $p\mid n$，定义删除一层的收益

<a id="eq-19"></a>

$$
D_p^-(n)
=
\log R(n/p)-\log R(n)
=
f(T)-f(T-\log p)-\lambda_{p,a}.
\tag{19}
$$

<!-- editorial-note:start deletion-domain -->
**【编者局部说明：删除边的定义域】** 上面“若 $p\mid n$”是原稿文字。以本文定义的 Robin 比值解释 (19) 时还必须要求 $n/p>5040$；若只把右端当作实函数差，至少要求 $T-\log p>1$。一般整数上不可仅凭 $p\mid n$ 就使用删除边。定理 4 及之后始终处于弱反例轨道，(3) 保证：删 $2$ 后仍有 $2^{20}$，删奇素数后仍有 $2^{21}$，故确实有 $n/p\ge2^{20}>5040$。因此该轨道上的全部素数删除边都合法。
<!-- editorial-note:end deletion-domain -->

每次选择所有正收益方向中收益最大者；相同时按固定规则选择。没有正收益方向时停止。

首先要证明，乘法候选也是有限的。

### 引理：所有正收益乘法方向都满足 $p<T+\log T$

若

$$
p\ge T+\log T,
\qquad h=\log p,
$$

则

$$
p-\log T\ge T,\qquad h\ge\log T,
$$

从而

$$
ph\ge(T+h)\log T.
$$

利用 $\log(1+u)>u/(1+u)$，

$$
\log(1+h/T)
>
\frac h{T+h}
\ge\frac{\log T}{p}.
$$

因此

$$
\begin{aligned}
f(T+h)-f(T)
&=
\log\left(
1+\frac{\log(1+h/T)}{\log T}
\right)\\
&>\log(1+1/p)
\ge\lambda_{p,a+1}.
\end{aligned}
$$

故

<a id="eq-20"></a>

$$
\boxed{
p\ge T+\log T
\Longrightarrow D_p^+(n)<0.
}
\tag{20}
$$

所以每一步只需在有限多个素数乘法方向和有限多个删除方向中定义最大收益。

### 定理 4：从任何弱反例出发，这个过程必然有限终止

假设

$$
n_0>5040,\qquad R(n_0)\ge1.
$$

每一次移动严格增加 $R$，所以全过程始终满足 $R(n_j)\ge1$。

由式 (3)，每个状态都含 $2^{21}$。因此任意素数删除都留在合法范围：

$$
n_j/p\ge2^{20}>5040.
$$

如果一开始就没有正收益方向，过程已经停止。

否则第一步后有

$$
R(n_1)>1.
$$

令

$$
\delta=R(n_1)-1>0.
$$

此后全部状态满足

$$
R(n_j)\ge1+\delta.
$$

与式 (1) 合并：

$$
\delta<
\frac{A_0}{(\log\log n_j)^3}.
$$

所以

<a id="eq-21"></a>

$$
\boxed{
n_j<
\exp\!\left[
\exp\!\left((A_0/\delta)^{1/3}\right)
\right].
}
\tag{21}
$$

<!-- editorial-note:start finite-ascent-scope -->
**【编者局部说明：有限终止的范围】** 乘法候选截断引理在 $T>1$ 下使用正的 $\log T$，并由 $h\ge\log T$ 得 $T(h-\log T)\ge0$，从而补足原推导中的 $ph\ge(T+h)\log T$。有正收益时最大值在有限候选集中取得；这是精确实数上的定义。式 (21) 只约束第一次严格移动后的状态；初始状态单独加入仍是有限集合。严格增加排除任何重复，故终止。结论只针对弱反例起点，不宣称安全整数上的同一规则也终止，也不提供零收益的有效判定算法。
<!-- editorial-note:end finite-ascent-scope -->

所有后继整数都属于一个有限集合。严格增加的 $R$ 排除了重复访问，因此只能移动有限次。证毕。

**这给出了一个实际的有限终止证明。** 它依赖的是严格收益与无条件上界之间的矛盾。

这里的贪心定义使用精确实数比较；数值实现若要判定零收益边，还需要相应的认证机制。

---

<a id="sec-6"></a>

## 六、终点具有唯一价格最优性，而且存在严格的曲率间隔

设上述过程停止在 $N$，记

$$
T=\log N,\qquad
\eta=\frac1{T\log T}.
$$

对 $p^a\Vert N$，删除不能增加 $R$，所以

$$
\lambda_{p,a}
\ge f(T)-f(T-\log p).
$$

严格凹性给出

$$
f(T)-f(T-\log p)>\eta\log p.
$$

故

<a id="eq-22"></a>

$$
\boxed{\lambda_{p,a}>\eta\log p.}
\tag{22}
$$

对任意素数 $p$，加入一层不能增加 $R$，所以

$$
\lambda_{p,a+1}
\le f(T+\log p)-f(T)
<\eta\log p.
$$

故

<a id="eq-23"></a>

$$
\boxed{\lambda_{p,a+1}<\eta\log p.}
\tag{23}
$$

这说明所有已占用层的价格增益严格为正，所有未占用层严格为负，没有零价格层。

### 定理 5：反例终点是自身匹配价格下的唯一整数最优点

<a id="eq-24"></a>

$$
\boxed{
N
=
\operatorname*{arg\,max}_{m\ge1}
\left\{
\log Z(m)-\frac{\log m}{T\log T}
\right\},
\qquad T=\log N,
}
\tag{24}
$$

且右侧最大点唯一。

**证明。**

式 (22)–(23) 和层收益的严格递减性，确定了每个素数方向上全部正项与负项的分界。

任何不同整数 $m\neq N$，必然至少漏取一个正项，或者加入一个负项。因此其价格目标严格小于 $N$。证毕。

进一步，令 $h=\log p$。利用 $\kappa$ 的严格下降性，还可得到

<a id="eq-25"></a>

$$
\boxed{
\lambda_{p,a}>
\eta h+\frac{\kappa(T)}2h^2,
}
\tag{25}
$$

<a id="eq-26"></a>

$$
\boxed{
\lambda_{p,a+1}<
\eta h-\frac{\kappa(T+h)}2h^2.
}
\tag{26}
$$

<!-- editorial-note:start strict-integral-gaps -->
**【编者局部说明：严格曲率间隔的积分依据】** 对已占用层，合法删除保证 $T-h>1$，且

$$
f(T)-f(T-h)-\eta h
=\int_{T-h}^T\int_t^T\kappa(u)\,du\,dt
>\frac{\kappa(T)}2h^2.
$$

对任一加入方向，

$$
\eta h-[f(T+h)-f(T)]
=\int_T^{T+h}\int_T^t\kappa(u)\,du\,dt
>\frac{\kappa(T+h)}2h^2.
$$

$h>0$ 与 $\kappa$ 严格下降给出严格号；再结合终止时各边收益非正即得 (25)、(26)。层收益严格递减把 (22)、(23) 扩展到全部已取和未取层，任意不同整数的有限层差至少有一个严格损失，故 (24) 是全整数价格目标的唯一最大点。
<!-- editorial-note:end strict-integral-gaps -->

所以，终点不只是落在一个价格分界上；已取层与未取层之间还隔着一个由曲率确定的严格区间。

这类极值归约与已有的 CA、GA 数研究相联系。已有文献也用素数删除、倍数比较与极值整数研究 Robin；这里的终点只保证单素数乘除邻域的极大性，GA2 所要求的全部倍数极大性更强。[arxiv.org](https://arxiv.org/abs/1112.6010?utm_source=chatgpt.com)

<!-- editorial-note:start classical-ca-ga-attribution -->
**【编者局部说明：经典 CA/GA 的准确对应】** 参见 G. Caveney、J.-L. Nicolas、J. Sondow, *On SA, CA, and GA numbers*, [arXiv:1112.6010v1](https://arxiv.org/pdf/1112.6010v1)：第 7–9 页 §2 的 $F(p,j)$ 正是本文 $\rho_{p,j}$；CA 的定义是对某个 $\varepsilon>0$ 最大化 $\sigma(m)/m^{1+\varepsilon}$，即本文指数化的价格目标，参数对应为 $\varepsilon=\eta$。因此定理 1 属于经典 CA 层阈值优化，定理 5 的终点是匹配价格的 CA 最大点，不把改换记号称作新理论。第 4 页定义 GA1 为复合 $N$ 对所有素因子满足 $G(N)\ge G(N/p)$，GA2 为对所有正整数倍满足 $G(N)\ge G(aN)$，其中 $G=e^\gamma R$。本文反例终点确满足 GA1 及单素数加入的局部条件；后者未推出 GA2。该文第 5 页 Theorem 4(ii) 已给出“若存在 Robin 反例，则最大 $G$ 及一个同时为 GA1、GA2 的极值整数存在”的更强存在性背景；本文从任意反例的特定有限上升路径须按自身证明理解，不宣称首次发现极值归约。本文涉及的历史关系以此文及其所引 Ramanujan、Alaoglu–Erdős、Robin 结果为归属，无另行原创性主张。
<!-- editorial-note:end classical-ca-ga-attribution -->

---

<a id="sec-7"></a>

## 七、终点必须包含由自身尺度决定的完整最小公倍数

这一部分进一步加强上一轮的整除分类。

### 定理 6：终点包含每个 $p\le T$ 的素数

假设素数 $p\le T$ 没有出现。

首先，

$$
\begin{aligned}
f(T+\log T)-f(T)
&=
\log\left[
1+\frac{\log(1+(\log T)/T)}{\log T}
\right]\\
&<
\log(1+1/T),
\end{aligned}
$$

其中使用了 $\log(1+u)<u$。

而

$$
\log(1+1/p)\ge\log(1+1/T),
$$

$$
f(T+\log p)-f(T)
\le f(T+\log T)-f(T).
$$

所以

$$
D_p^+(N)>0,
$$

与终止矛盾。证毕。

另一方面，已出现素数由式 (22) 满足

$$
\eta\log p<\lambda_{p,a}\le\log(1+1/p)<1/p,
$$

从而

$$
p\log p<T\log T,
$$

故 $p<T$。

因此终点的素数支持恰好是 $T$ 以下的完整素数段。

<!-- editorial-note:start support-and-prime-powers -->
**【编者局部说明：素数端点及高层条件】** 第一结论是所有素数 $p\le T$ 均出现，第二结论是所有已出现素数均满足 $p<T$；若 $T$ 恰为素数，两者立即矛盾，所以实际终点的 $T$ 不可能是素数。下文对 $j\ge2$ 使用 $p^j\le T\Rightarrow\log p\le(\log T)/j\le(\log T)/2$。并且 $\log(1+u)>u/(1+u)$ 给出 $\lambda_{p,j}>1/(1+p+\cdots+p^j)$。这补足定理 7 的比较；这些层严格越过价格阈值，由 (23) 必须已取。
<!-- editorial-note:end support-and-prime-powers -->

### 定理 7：所有满足 $p^j\le T$ 的素数幂层都必须出现

第一层已由定理 6 处理。

若 $j\ge2$、$p^j\le T$，则

$$
1+p+\cdots+p^j<2p^j\le2T.
$$

因此

$$
\begin{aligned}
\lambda_{p,j}
&>
\frac1{1+p+\cdots+p^j}\\
&>
\frac1{2T}
\ge
\frac{\log p}{T\log T}
=\eta\log p.
\end{aligned}
$$

这一层具有严格正价格增益，必须被终点取入。证毕。

令

$$
\psi(x)=\sum_{p^j\le x}\log p.
$$

于是

<a id="eq-27"></a>

$$
\boxed{
\operatorname{lcm}(1,2,\ldots,\lfloor T\rfloor)\mid N,
\qquad T=\log N,
}
\tag{27}
$$

并且

<a id="eq-28"></a>

$$
\boxed{\psi(T)\le T.}
\tag{28}
$$

这里的最小公倍数尺度已经达到 $\log N$。

### 平方层还能继续加强

当 $T\ge64$ 时，可以证明

<a id="eq-29"></a>

$$
\boxed{
p\le\sqrt{\frac{3T}{2}}
\Longrightarrow v_p(N)\ge2.
}
\tag{29}
$$

事实上，此时

$$
p^2+p+1<\frac{107}{64}T,
\qquad
\log p<\frac9{16}\log T.
$$

所以

$$
(p^2+p+1)\log p
<
\frac{963}{1024}T\log T
<
T\log T.
$$

由此

$$
\lambda_{p,2}>
\frac1{p^2+p+1}
>
\eta\log p,
$$

第二层必须出现。

记

$$
\vartheta(x)=\sum_{p\le x}\log p.
$$

将最小公倍数中的层，与额外的平方层合并，得到

<a id="eq-30"></a>

$$
\boxed{
\psi(T)
+
\vartheta\!\left(\sqrt{3T/2}\right)
-
\vartheta(\sqrt T)
\le T,
\qquad T\ge64.
}
\tag{30}
$$

<!-- editorial-note:start square-constants-and-mass -->
**【编者局部说明：平方常数与不重复计数】** 当 $T\ge64$ 且 $p^2\le3T/2$ 时，

$$
\frac pT\le\sqrt{\frac3{2T}}\le\sqrt{\frac3{128}}<\frac5{32},
\qquad
\frac1T\le\frac1{64},
$$

故 $(p^2+p+1)/T<3/2+5/32+1/64=107/64$。又 $(3/2)^8<64\le T$，所以

$$
\log p\le\tfrac12\log T+\tfrac12\log(3/2)<\tfrac9{16}\log T.
$$

相乘即得 $963/1024<1$，没有数值近似。$\log\operatorname{lcm}(1,\ldots,\lfloor T\rfloor)=\psi(T)$；新增平方层只计 $\sqrt T<p\le\sqrt{3T/2}$，与其中已有的层不重复，所以 (30) 是同一个 $N$ 的强制对数质量下界，不能被读成矛盾或充分存在条件。
<!-- editorial-note:end square-constants-and-mass -->

因此，反例终点的尺度必须位于满足这一强制质量约束的位置。

### 还有一个精确的素数间隙条件

定义 $d(T),a(T)$ 分别为以下方程的唯一实根：

$$
\log(1+1/x)=f(T)-f(T-\log x),
$$

$$
\log(1+1/x)=f(T+\log x)-f(T).
$$

两式左侧严格下降、右侧严格上升，故根唯一。上述比较还给出

$$
d(T)<T<a(T)<T+\log T.
$$

终点的每个已出现素数必须满足 $p\le d(T)$，每个缺失素数必须满足 $p\ge a(T)$：否则分别存在正收益删除或加入。

所以

<a id="eq-31"></a>

$$
\boxed{(d(T),a(T))\text{ 内没有素数。}}
\tag{31}
$$

<!-- editorial-note:start gap-root-domains -->
**【编者局部说明：实根的定义域、存在性与必要性】** 两个原方程均予保留。删除根的域为 $1<x<\exp(T-1)$，加入根的域为 $x>1$；这里 $T>\log5040>2$，故 $T-\log T>1$，特别是 $x=T$ 位于删除域内。左边 $L(x)=\log(1+1/x)$ 严格下降。删除右边的导数为 $f'(T-\log x)/x>0$，从 $x\downarrow1$ 的 $0$ 趋于 $x\uparrow\exp(T-1)$ 时的 $+\infty$；加入右边的导数为 $f'(T+\log x)/x>0$，从 $0$ 趋于 $x\to\infty$ 时的 $+\infty$。左边两域起点的极限为 $\log2>0$，另一端有限或趋零，故连续性和严格单调性分别给出存在且唯一的根。

在 $x=T$ 处，删除右边严格大于 $\eta\log T=1/T>L(T)$，故 $d(T)<T$；定理 6 的比较给出加入右边小于 $L(T)$，而 (20) 的证明在 $x=T+\log T$ 处给出加入右边大于 $L(x)$，故 $T<a(T)<T+\log T$。若 $p\mid N$，合法删除与 $\lambda_{p,a}\le L(p)$ 给出删除右边不超过 $L(p)$，于是 $p\le d(T)$。若 $p\nmid N$，加入收益非正给出 $L(p)$ 不超过加入右边，于是 $p\ge a(T)$。因此开区间内无素数；两端允许等号，尚未得到与素数分布相矛盾的统一结论。
<!-- editorial-note:end gap-root-domains -->

式 (30) 与式 (31) 同时限制终点的素数幂质量和附近素数分布。它们目前还没有形成矛盾。

---

<a id="sec-8"></a>

## 八、可以完全证明的一类无限递归，以及它的酉极限

你的“误差、守恒、归一化、无限递归”设想，在下面这个无限整数类上可以闭合。

取一个已经证明安全的 $B>5040$，记

$$
r=R(B)<1.
$$

例如 $B=2^{21}$ 可以直接使用：$Z(B)<2$，而 $e^\gamma\log\log B>2$。

<!-- editorial-note:start elementary-safe-base -->
**【编者局部说明：安全基底的纸面界】** 有 $0<\gamma$、$e<3$、$\log2>1/2$，故 $\log B=21\log2>21/2>9>e^2$，从而 $\log\log B>2$，而 $Z(2^{21})=2-2^{-21}<2$。这给出严格的 $0<r<1$，不把 (2) 的 $v_2\le20$ 错用于 $B$。上述初等界中 $\log2>1/2$ 直接来自对 $1/t$ 在 $[1,2]$ 的积分，$e<3$ 来自指数级数；$\gamma\ge1-\log2>0$ 可由调和和与对数的积分比较得到。
<!-- editorial-note:end elementary-safe-base -->

选择互异素数 $p_j$，令

$$
b_j=p_j^{-v_{p_j}(B)-1},
\qquad
W=\prod_{j=1}^{\infty}(1-b_j).
$$

### 定理 8：一个乘积预算证明整棵无限分支树安全

如果

<a id="eq-32"></a>

$$
\boxed{W>r,}
\tag{32}
$$

那么对任意有限支撑指数列 $e_j\ge0$，

<a id="eq-33"></a>

$$
\boxed{
R\!\left(B\prod_jp_j^{e_j}\right)
\le\frac rW<1.
}
\tag{33}
$$

**证明。**

每个素数方向的增长满足

$$
\frac{S_{p_j}(v_{p_j}(B)+e_j)}
{S_{p_j}(v_{p_j}(B))}
=
\frac{1-b_jp_j^{-e_j}}{1-b_j}
\le\frac1{1-b_j}.
$$

同时实际整数增大，使 $\log\log n$ 不减。因此所有方向合并后，

$$
R(n)
\le r\prod_{j:e_j>0}(1-b_j)^{-1}
\le r/W<1.
$$

证毕。

这覆盖任意多个素数方向、每个方向任意大的指数。

一个明确的贪心选择是：每次取新的素数

$$
p_j\nmid B,
\qquad
p_j\ge\frac{2^{j+1}}{1-r}.
$$

素数无限性保证可以持续选择。于是

$$
\sum_jb_j\le\frac{1-r}{2},
$$

从而

<a id="eq-34"></a>

$$
W\ge\frac{1+r}{2},
\qquad
\boxed{R(n)\le\frac{2r}{1+r}<1.}
\tag{34}
$$

<!-- editorial-note:start infinite-family-scope -->
**【编者局部说明：无限族的量词与乘积】** 此节重新定义 $b_j$，不再使用第四节的损失参数；互异 $p_j$ 保证 Euler 因子不重复，且 $0<b_j<1$。无限乘积 $W$ 是有限前缀乘积的单调极限，(32) 使其严格为正。式 (33) 只将有限多个非零 $e_j\in\mathbb N_0$ 相乘，所以每个对象仍为实际有限整数；每个指数可任意大，不是把无限乘积当成整数。取 $j=1,2,\ldots$，每步可选不整除 $B$、未用过且达到所给阈值的最小素数，素数无界保证存在。此时 $b_j=1/p_j\le(1-r)2^{-j-1}$；由有限乘积不等式 $\prod(1-b_j)\ge1-\sum b_j$ 再取极限，得到 $W\ge(1+r)/2>r$。这是所选稀疏素数族的安全证书，不是全部整数的安全证书。
<!-- editorial-note:end infinite-family-scope -->

### AURIC 尾误差

令

$$
q_h=1-\prod_{j\le h}(1-b_j).
$$

仍有

$$
q_{h+1}=q_h+(1-q_h)b_{h+1}.
$$

如果尾和有上界

$$
\sum_{j>h}b_j\le\tau_h,
$$

则

<a id="eq-35"></a>

$$
\boxed{
0\le(1-W)-q_h\le(1-q_h)\tau_h.
}
\tag{35}
$$

<!-- editorial-note:start tail-certificate -->
**【编者局部说明：尾证书的严格性】** 记尾乘积为 $P_{>h}$，则 $(1-W)-q_h=(1-q_h)(1-P_{>h})$；有限乘积的 $1-\prod(1-b_j)\le\sum b_j$ 取极限后给出 (35)。因此所列严格有限深度条件蕴含 $W>r$，可覆盖该指定素数族所有尚未展开的有限支撑分支；有限前缀本身没有认证未给出上界的尾部。
<!-- editorial-note:end tail-certificate -->

所以一个有限深度的证书

$$
q_h+(1-q_h)\tau_h<1-r
$$

就已经负责全部未展开分支。

### 同一预算保证无限酉过程收敛

保留全部寄存器，在第 $j$ 个寄存器上定义

$$
U_j=
\begin{pmatrix}
\sqrt{1-b_j}&-\sqrt{b_j}\\
\sqrt{b_j}&\sqrt{1-b_j}
\end{pmatrix}.
$$

每个 $U_j$ 都是酉算子。取以全零状态为基准的无限 qubit 张量积空间，令

$$
V_h=U_1\cdots U_h.
$$

<!-- editorial-note:start incomplete-tensor-space -->
**【编者局部说明：希尔伯特空间与新因子】** 这里具体取相对于零真空的不完全无限张量积

$$
\mathcal H=\overline{\bigcup_{L\ge0}(\mathbb C^2)^{\otimes L}\otimes|0\rangle_{L+1}\otimes|0\rangle_{L+2}\otimes\cdots}.
$$

$U_j$ 仅作用于第 $j$ 个新因子，其余因子取恒等；不同 $j$ 的算子对易。下文“只涉及有限个寄存器的向量”指某个有限前缀中的任意向量（可以纠缠），其后各因子确为 $|0\rangle$；这些向量的并集稠密。上面定义的 $V_h$ 是该空间上的有限乘积酉算子。
<!-- editorial-note:end incomplete-tensor-space -->

式 (32) 自动给出

$$
\sum_jb_j
\le
\sum_j-\log(1-b_j)
=
-\log W<\infty.
$$

对于只涉及有限个寄存器的向量 $\xi$，当 $N>M$ 足够大时，

$$
\begin{aligned}
\|V_N\xi-V_M\xi\|^2
&=
2\|\xi\|^2
\left(
1-\prod_{j=M+1}^{N}\sqrt{1-b_j}
\right)\\
&\le
2\|\xi\|^2\sum_{j>M}b_j
\longrightarrow0.
\end{aligned}
$$

由稠密性与 $\|V_h\|=1$，得到强收敛。对伴随 $V_h^*$ 同样成立，因此极限 $V$ 满足

<a id="eq-36"></a>

$$
\boxed{V^*V=VV^*=I.}
\tag{36}
$$

<!-- editorial-note:start strong-adjoint-limit -->
**【编者局部说明：强极限为何仍为酉】** 若 $M$ 已超过 $\xi$ 的支撑，尾部内积逐因子等于 $\sqrt{1-b_j}$，正好得到原稿的范数等式。再用 $1-\prod\sqrt{1-b_j}\le\sum b_j$ 即得尾界。(32) 经有限前缀取对数再取极限给出 $\sum b_j\le-\log W<\infty$。伴随的尾真空内积仍是同一个实数乘积，因此 $V_h^*$ 也在该稠密集上 Cauchy；两列算子的范数均为 $1$，故均扩张为整个 $\mathcal H$ 上的强收敛。若极限分别为 $V,A$，内积取极限得 $A=V^*$；一致有界性又给出

$$
V_hV_h^*\xrightarrow{\rm strong}VA=I,
\qquad
V_h^*V_h\xrightarrow{\rm strong}AV=I.
$$

于是 (36) 成立。仅有酉算子列的强收敛不足以推出酉性；这里两列同时收敛才是依据。本文没有声称算子范数收敛。
<!-- editorial-note:end strong-adjoint-limit -->

所以这里确实得到了无限酉极限。

每一步的三项读出可以对应三个正交事件子空间：此前已经出现 $1$、此前全零而本位为 $1$、此前及本位均为零。完整寄存器保留了递归历史，三轴读出负责当前的预算。

<!-- editorial-note:start born-readout-boundary -->
**【编者局部说明：事件概率与实现边界】** 对初态为全零真空的 $V_j|0\cdots\rangle$，这三个互相正交且穷尽的事件子空间的 Born 概率依次是 $q_{j-1}$、$(1-q_{j-1})b_j$、$(1-q_{j-1})(1-b_j)$。这是选定辅助张量积载体上的读出，完整态保留全部已用寄存器。无限数学模型的酉极限存在，不自动授予原生算术信息取得、有限资源实现或物理控制能力。
<!-- editorial-note:end born-readout-boundary -->

---

<a id="sec-9"></a>

## 九、现在剩余的 RH 目标可以精确写出来

前面的推导已经建立：

$$
\boxed{
\begin{aligned}
\text{若 Robin 存在反例}
\quad\Longrightarrow\quad
\text{存在反例终点 }N,
\end{aligned}
}
$$

其中这个终点同时满足：

- 所有单素数乘除都不能增加 $R$；
- 在自身价格 $1/(\log N\log\log N)$ 下具有唯一整数最优性；
- 严格曲率间隔；
- $\operatorname{lcm}(1,\ldots,\lfloor\log N\rfloor)\mid N$；
- 平方层质量约束与素数间隙约束。

把终点完全写成一个尺度变量，定义

$$
a_p(T)
=
\#\left\{
j\ge1:
\log\left(1+\frac1{p+\cdots+p^j}\right)
>
\frac{\log p}{T\log T}
\right\}.
$$

它必须满足自洽方程

<a id="eq-37"></a>

$$
\boxed{
T=\sum_p a_p(T)\log p.
}
\tag{37}
$$

<!-- editorial-note:start self-consistency-necessary -->
**【编者局部说明：自洽只是必要条件】** 对每个固定 $T>1$，式 (5) 使 $a_p(T)$ 的非零集合及每个指数有限，故 (37)、(38) 的素数和实际只有有限个非零项。对上述终点，严格价格分界给出 $a_p(T)=v_p(N)$，才得到 (37)。反过来，仅有该尺度等式并未证明乘除边均非正，也未证明整数是反例；不得把自洽解类与实际反例终点类混同。
<!-- editorial-note:end self-consistency-necessary -->

需要继续证明的严格符号目标是

<a id="eq-38"></a>

$$
\boxed{
\sum_p
\log\left(
\frac{1-p^{-a_p(T)-1}}{1-p^{-1}}
\right)
<
\gamma+\log\log T
}
\tag{38}
$$

对所有可能成为上述终点的 $T>\log5040$ 成立。

**式 (38) 一旦在这类终点上完成，有限贪心归约就会把它提升为全部 $n>5040$ 的 Robin 不等式，从而得到 RH。**

<!-- editorial-note:start unresolved-sign-target -->
**【编者局部说明：尚未闭合的符号目标】** 式 (38) 在实际终点上的左边恰为 $\log Z(N)$，所以它若成立便与 $R(N)\ge1$ 矛盾，再由有限归约排除全部弱反例。目前 (30)、(31) 只是必要约束，(37) 只是必要自洽式；本文未给出它们推出 (38) 的统一严格余量。第八节的无限安全子族与辅助酉极限亦不填补这一缺口。下段“已经证明”仍是原稿对其纸面推导的归纳，不是 RH 的证明，也不是本次新增的 Lean 核验。
<!-- editorial-note:end unresolved-sign-target -->

本轮已经证明了“怎样遍历、怎样分类、哪一种贪心有全局支配保证、反例递归为什么有限终止、终点必须具有什么结构”，并完成了一类无限整数族的 Robin 与酉收敛证明。接下来的实质工作，是把式 (30)、式 (31) 的素数分布约束与项目中的实际整数 KL 缺陷结合，给式 (38) 提供统一的严格正余量。
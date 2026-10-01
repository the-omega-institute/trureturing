---
bibkey: fibaffine2026growingmoduli
authors: trureturing research synthesis
year: 2026
title: Growing-modulus interfaces for affine Fibonacci Robin candidates
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: "A parameter comparison of the cited primary sources, including Pascadi's 2025 unconditional exponent 5/8 and Bourgain–Garaev's subpower prime-modulus reciprocal cancellation: finite positive moments and unweighted cancellation do not supply the same-candidate strict Robin budget with the actual low-loss weights."
strata_touched: []
license: citation-only
triage: anchor
---

# FIB 单位位一来源：增长模数的文献适用范围

本笔记保留可以用于后续逐点研究的数学接口和原始文献条件。它不宣称 RH、FIB 本族的逐点 Robin 不等式、完整文献搜索或原创性。所列推导均为纸面数学；不提供 Lean 核验。

## 目标与实际参数

研究

$$
V=F_r,\quad r\text{ 为充分大素数},\quad
\lceil V/10\rceil\le g\le\lfloor V/5\rfloor,\quad N=1+gV.
$$

令 $X=1+V\lfloor V/5\rfloor$、$Y=2r-2$，并取完整赋值核心

$$
C=\prod_{p\le Y}p^{v_p(N)},\qquad H=N/C.
$$

前一份核心推导给：固定 $\kappa>0.0094243/(1-\log\phi)$，每个充分大的潜在 Robin 反例都满足

$$
\log H<\frac{\kappa\log N}{(\log\log N)^2}.
$$

这里可取 $\kappa=1/50$。所以当前的真实文献接口不是常数余因子，而是

$$
V\asymp X^{1/2},\quad
Y\sim\frac{\log X}{\log\phi},\quad
H\le\exp\left((\kappa+o(1))\frac{\log X}{(\log\log X)^2}\right)=X^{o(1)}.
$$

因 $F_r$ 的素因子均不小于 $2r-1$，$C$ 与 $V$ 互素，且

$$
CH-gV=1,\qquad C\equiv H^{-1}\pmod V.
$$

对固定实际 $H$，核心的大小区间为

$$
\frac{1+V\lceil V/10\rceil}{H}
\le C\le\frac{1+V\lfloor V/5\rfloor}{H}.
$$

还必须检查 $C$ 的全部素因子不大于 $Y$、$H$ 的全部素因子大于 $Y$，以及真正的 $Z(CH)$。解出同余只是必要筛选。即使把文献的计数尺度改为 $x=X/H$，仍有

$$
\frac{\log x}{\log V}\longrightarrow2,\qquad
Y\asymp\log x,
$$

一致于上述允许的 $H$ 范围；小余因子不会消除临界光滑度与指定模数误差的障碍。

## 可直接使用：Weingartner 的高正矩

Andreas Weingartner, *The distribution functions of σ(n)/n and n/φ(n), II*,
arXiv:1011.4262v1 (2010).

- 原文：https://arxiv.org/html/1011.4262v1
- PDF：https://arxiv.org/pdf/1011.4262v1
- 对应位置：式（5），Lemma 5，Lemma 6。

其式（5）给 Euler 乘积

$$
W(s)=\prod_p\left(1+\frac{(1-p^{-1})^{-s}-1}{p}\right).
$$

对 $s>0$，令非负乘法函数 $a_s$ 满足
$a_s(p)=(1-p^{-1})^{-s}-1$、$a_s(p^k)=0$（$k\ge2$）。有限展开给

$$
\sum_{n\le X}(n/\varphi(n))^s
=\sum_{d\le X}a_s(d)\lfloor X/d\rfloor\le XW(s).
$$

因此，无需任何变化参数与极限平均的交换，即有

$$
\#\{n\le X:Z(n)\ge t\}\le XW(s)t^{-s}.
$$

Lemma 5 的精确条件为 $s\ge e$、$s=z\log z$、固定整数 $m\ge2$。其 $m=2$ 展开为

$$
\log W(s)=s\log(e^\gamma\log z)-z
+\frac{\pi^2}{6}\frac z{(\log z)^2}
+O\left(\frac z{(\log z)^3}\right).
$$

在 $A\to\infty$、$X/A$ 有界时，显式取
$t=e^\gamma\log\log A$、$z=\log A$、$s=z\log z$，得到

$$
\#\{A\le n\le X:Z(n)\ge e^\gamma\log\log n\}
\le\exp\left(\left(\frac{\pi^2}{6}+o(1)\right)
\frac{\log X}{(\log\log X)^2}\right).
$$

这给实际潜在反例的确定性数量上界，包括等号；它不把完整核心候选集也压到这个数量，更不推出不存在反例。它对整个区间成立，并非 FIB 专有。有限桥梁见 FIB 理论卷 §208 与同目录 `weingartner2010distribution.md`。

Lemma 6 的条件为 $t\ge1$、$y=e^{t e^{-\gamma}}$；它展开
$\min_{s\ge e}W(s)t^{-s}$，前两主项同为 $-y+(\pi^2/6)y/\log^2y$。此处不需要最优化步骤。

该文 Theorem 1 的 $A(t)$、$B(t)$ 是先固定 $t$ 后定义的极限分布尾。单独把其中的 $t$ 置为 $e^\gamma\log\log X$，不能证明本段的有限上界；真正桥梁是上面的非负有限展开。

## Harper：单个剩余类的光滑数均匀分布

Adam J. Harper, *On a paper of K. Soundararajan on smooth numbers in arithmetic progressions*, arXiv:1103.2106v1 (2011).

- 原文：https://arxiv.org/html/1103.2106v1
- 精确位置：Theorem 1、Theorem 2。

Theorem 1：固定 $\delta>0$，$y\le x$，

$$
2\le q\le y^{4\sqrt e-\delta},\quad (a,q)=1,
$$

且 $y$ 充分大（依赖 $\delta$），则在

$$
\log x/\log q\longrightarrow\infty
$$

的极限下，$\Psi(x,y;q,a)\sim\Psi_q(x,y)/\varphi(q)$。

当前取 $q=V$、$y=Y$ 时有两个独立不满足的前提：$q\asymp X^{1/2}$ 超过每个固定 $Y^A$，而 $\log(X/H)/\log q\to2$，不趋于无穷。Theorem 2 的陪集版本仍要求 $q\le y^A$（固定 $A$）及相同对数比极限，因此也不能直接接入。论文讨论的 Soundararajan 猜想原表述仍有这两个前提；仅假设该猜想为真也不足以覆盖当前参数。

## Pascadi：大模数平均与指定模数的误差

### 2023 论文的 2025 版本：模数指数 $66/107$

Alexandru Pascadi, *Smooth numbers in arithmetic progressions to large moduli*, arXiv:2304.11696v3 (2025版)。

- 原文：https://arxiv.org/html/2304.11696v3
- 精确位置：Theorem 1.1。

对固定非零整数 $a$、$A,\varepsilon>0$，存在 $C=C(A,\varepsilon)>0$，当

$$
x>2,\quad(\log x)^C\le y\le x^{1/C},
$$

有

$$
\sum_{\substack{q\le x^{66/107-\varepsilon}\\(q,a)=1}}
\left|\Psi(x,y;a,q)-\Psi_q(x,y)/\varphi(q)\right|
\ll_{a,A,\varepsilon}\Psi(x,y)/(\log x)^A.
$$

模数指数 $1/2$ 确实低于 $66/107$，但这一条指数比较不满足整个定理：

- 当前 $y\asymp\log x$，原文给出的存在性常数 $C$ 不保证允许指数1；不能自行取 $C=1$。
- 结论的绝对误差总和非负，可以合法抽取指定模数 $F_r$ 的一项；但所得上界仍为完整的 $\Psi(x,y)/(\log x)^A$，没有额外的 $1/\varphi(F_r)$ 因子，不能仅凭此界断言已控制这一剩余类的实际命中数。
- 当前剩余类为 $H^{-1}\bmod V$，随实际 $H$ 改变；所引 Theorem 1.1 的 $a$ 固定。

即使另行弥补光滑度和剩余类的一致性，平均误差界本身仍需足够强到能控制这一个模数的实际命中数。不能把平均主项小于1与逐点没有整数命中等同。

### 2025 新论文：无条件模数指数 $5/8$

Alexandru Pascadi, *On the exponents of distribution of primes and smooth numbers*, arXiv:2505.00653v2，2025-06-29。

- 原文：https://arxiv.org/html/2505.00653v2
- 精确位置：[Theorem 1.5 及其后的 Remark](https://arxiv.org/html/2505.00653v2#S1.Thmtheorem5)。

此文与上面的 arXiv:2304.11696v3 是不同论文。Theorem 1.5 无条件推进了光滑数分布的模数指数：对固定 $a\in\mathbb Z\setminus\{0\}$、$A,\varepsilon>0$ 及 $x\ge2$，存在充分大的 $C=C(a,A,\varepsilon)>0$，使得当

$$
(\log x)^C\le y\le x^{1/C},\qquad Q\le x^{5/8-\varepsilon},
$$

有

$$
\sum_{\substack{q\le Q\\(q,a)=1}}
\left|\Psi(x,y;a,q)-\frac{\Psi_q(x,y)}{\varphi(q)}\right|
\ll_{\varepsilon,A,a}\frac{\Psi(x,y)}{(\log x)^A}.
$$

当前 $x=X/H=V^{2-o(1)}$，故 $V=x^{1/2+o(1)}$。固定 $0<\varepsilon<1/8$ 并取充分大规模后，模数大小已在新定理范围内；不能继续把 $66/107$ 当作这条路线最新的无条件指数。临界光滑度 $Y\asymp\log x$ 仍不由定理保证；即使用较宽的 $Y\asymp\log x\log\log x$ 截断，也不能自行把存在性常数 $C$ 取为1。

这里平均的是模数，光滑整数本身没有任意给定系数。定理后的 Remark 指出，可按 Drappeau–Granville–Shao 的方法推广到光滑支撑乘法函数；它没有直接给出本题随规模增长的素数幂增量权的一致估计。对 $s>0$、$Z(n)=\sigma(n)/n$，实际权重为

$$
w_s(d)=\frac{b_s(d)}d,\qquad
b_s(p^j)=Z(p^j)^s-Z(p^{j-1})^s\quad(j\ge1).
$$

它们一般不完全乘法，并且 $w_s(2)=((3/2)^s-1)/2$ 随 $s$ 增长；全源在每个素数处都有非零增量，有限光滑截断必须另计尾项。扩大光滑支撑以满足定理下限，也必须支付改变后的 $\Psi(x,y)$ 和实际权重成本。

即使其余前提成立，从非负总和抽取指定 $q=V$ 仍只得到上述总误差，不会自动得到额外的 $1/\varphi(V)$。固定 $A$ 时，这个误差上界不能被当作相对于单余类主项的小误差，更不等于该余类没有整数命中。原定理还固定 $a$；在除数或核心切面上，$H^{-1}\bmod V$ 随实际余因子改变，其一致性不能由此陈述直接代入。对后续分解 $N_g=dh=1+Vg$，还必须保留同一个乘积的区间 $d\in[(1+V\lceil V/10\rceil)/h,X/h]$ 与同余 $dh\equiv1\pmod V$。新的平均分布定理改进了可复用背景，尚未关闭这一指定模数、真实权重和共同乘积窗口的联合接口。

## Jennings–Pollack–Thompson：丰数分布的量词

Emily Jennings, Paul Pollack, Lola Thompson, *Variations on a theorem of Davenport concerning abundant numbers*, arXiv:1306.0537v1 (2013)。

- 原文：https://arxiv.org/html/1306.0537v1
- 精确位置：Corollary 1.3 后的 Dirichlet 字符应用。

原文明确先固定 $q\in\mathbb N$ 和 $0<u\le1$，然后断言满足 $n/\sigma(n)\le u$ 且与 $q$ 互素的整数，在模 $q$ 的可逆剩余类中渐近均匀分布。

当前 $q=V\asymp X^{1/2}$，同时 $u=(e^\gamma\log\log X)^{-1}\to0$。这两个参数均未固定；所引结果没有给所需的一致性。因此它提供分布问题的正确固定参数基线，不提供本族的移动阈值逐点 Robin 估计。

## Shparlinski：逆元集合的平均与稀疏输入

Igor E. Shparlinski, *Distribution of modular inverses and multiples of small integers and the Sato–Tate conjecture on average*, arXiv:math/0608596v3 (2006)。

- 原文：https://arxiv.org/html/math/0608596v3
- 精确位置：$M_{a,m}$ 定义与 Theorem 1。

令 $M_{a,m}(\mathcal X;Y,Z)$ 按同余解对 $(x,h)$ 计数：$x\in\mathcal X$、$(x,m)=1$、$h\in[Z+1,Z+Y]\cap\mathbb Z$，且 $ax^{-1}\equiv h\pmod m$。当 $Y>m$ 时保留同一个 $x$ 对应多个 $h$ 的重数；不能只检查一个标准余数代表。Theorem 1 对正整数 $m,X,Y$、整数 $Z$、任意 $\mathcal X\subseteq[-X,X]$ 给

$$
\sum_{a=1}^m\left|M_{a,m}(\mathcal X;Y,Z)
-|\mathcal X_m|Y/m\right|^2
\le |\mathcal X|(X+Y)m^{o(1)}.
$$

原文描述的一个非平凡使用范围是足够稠密的 $\mathcal X$，及 $X,Y\ge m^{1/2+\varepsilon}$。

当前 $C H\equiv1\pmod V$ 需要固定 $a=1$，核心集合稀疏，而余因子区间长为 $V^{o(1)}$，远小于 $V^{1/2}$。该均方定理没有因此给出指定 $a=1$ 的无命中结论。也可对每个核心写 $g_C=-V^{-1}\bmod C$，但这样模数 $C$ 随核心改变；不能直接当成一个固定模数逆元分布。逆元映射是单位群置换，只保持整个单位群的计数，并不自动使光滑稀疏子集在短区间均匀分布。

## Bourgain–Garaev：素数模的次幂长度消去与逐点误差

Jean Bourgain, M. Z. Garaev, *Sumsets of reciprocals in prime fields and multilinear Kloosterman sums*, arXiv:1211.4184v1 (2012)。

- 原文：https://arxiv.org/pdf/1211.4184v1
- 精确位置：Theorem 16，第10页；§12.2 的证明从第54页开始。

在素数模 $p$ 下，令 $n^{-1}$ 为模 $p$ 逆元、$e_p(z)=\exp(2\pi iz/p)$。对 $2\le M<p$，所引定理给

$$
\max_{a\not\equiv0\pmod p}
\left|\sum_{n\le M}e_p(an^{-1})\right|
\ll M\frac{(\log\log p)^3\log p}{(\log M)^{3/2}},
$$

隐常数绝对。原文列出的非平凡使用范围包括

$$
M>\exp\bigl((\log p)^{2/3}(\log\log p)^3\bigr).
$$

这里的 $M$ 是从1开始的未加权区间端点；不能把该式当作任意平移区间、任意系数或低亏损子集上的同一估计。素指标 $r$ 也不保证 $F_r$ 为素数。

仅在另外满足 $p=V=F_r$ 为素数时，可以比较旧大除数分支的最大余因子尺度。令 $y=\log(1+V\lceil V/10\rceil)$，固定 $a_0>0$，取整数端点

$$
M=\left\lfloor\exp\left(\frac{a_0y}{(\log y)^2}\right)\right\rfloor.
$$

由于 $y=2\log p+O(1)$，这个端点充分大时在上述消去范围内。写

$$
\varepsilon_p(M)=\frac{(\log\log p)^3\log p}{(\log M)^{3/2}},
$$

则在这个端点尺度有

$$
\varepsilon_p(M)\asymp_{a_0}
\frac{(\log\log p)^6}{\sqrt{\log p}}\longrightarrow0,
\qquad M\varepsilon_p(M)\longrightarrow\infty.
$$

因此，“次幂区间一律太短而没有消去”不是这里的正确障碍。即使以该统一频率界控制一个指定逆元剩余类的未加权计数，误差尺度仍是 $M\varepsilon_p(M)$；主项 $M/p$ 加这个误差的上界不能降到1以下以证明无命中。相对消去不等于指定单点排除。

此外，一个实际余因子 $h\le M$ 未必达到定理的非平凡尺度。实际约束还包括 $d\mid N$、$dh=N=1+Vk$、共同乘积窗口以及 $J_s(d)\le J_0$。定理没有给这个子集的加权消去，更没有给同一个 $N$ 的完整价格损失。以所有 $n\le M$ 的消去替换经过低亏损筛选的部分和，没有可直接引用的支配关系。

Jean Bourgain, M. Z. Garaev, *Kloosterman sums in residue rings*, arXiv:1309.1124v1 (2013)。

- 原文：https://arxiv.org/pdf/1309.1124v1
- 精确位置：Theorem 5，第4页；§6.2 的证明从第14页开始。

其复合模数版本对固定小常数 $c>0$ 和 $M>m^c$ 给

$$
\max_{(a,m)=1}
\left|\sum_{\substack{n\le M\\(n,m)=1}}e_m(an^{-1})\right|
\ll_c M\frac{(\log\log m)^{O(1)}}{\sqrt{\log m}}.
$$

不能令 $c$ 随 $m$ 趋于0来覆盖 $M=m^{o(1)}$，因为定理固定 $c$，且隐常数依赖它。这个版本不弥补上述次幂余因子尺度在一般 $F_r$ 模数下的接口；素数模版本的全部非零频率界也不能直接运输到这里只控制可逆 $a$ 的陈述。

## Garaev–Shparlinski：选择模数产生的逆元聚集

Moubariz Z. Garaev, Igor E. Shparlinski, *On the distribution of modular inverses from short intervals*, arXiv:2304.07953v1 (2023)。

- 原文：https://arxiv.org/pdf/2304.07953v1
- 精确位置：Theorem 1.1，第3页；§3.1，第6—7页。

该定理对任意固定 $A_0>1$ 和充分大的整数 $M$，给出**存在某个素数** $p$，满足

$$
M\asymp(\log p)^{A_0},\qquad D_p(M)\gg1,
$$

其中 $D_p(M)$ 是序列 $n^{-1}/p$（$1\le n\le M$）的归一化 discrepancy。证明先取 $[M,2M]$ 中的 $(2M)^{1/A_0}$-光滑数集合 $\mathcal S$，令 $m=\operatorname{lcm}(\mathcal S)$，再选素数 $p\equiv-1\pmod m$。于是每个 $z\in\mathcal S$ 的标准逆元代表恰好是 $(p+1)/z$，由这份共同模数选择产生聚集；正文在长度 $2M$ 上完成论证。

它反驳的是把所有短逆元区间一律当作均匀分布的外推。它没有把模数限制为 Fibonacci 数，也没有保留实际同价参考 $C_s$、低亏损筛选或 $N=1+F_rk$ 的窗口。因此这是自由选模数下的障碍实例，不能登记为原 FIB 候选的反例，更不能登记为 Robin 反例。其长度范围也不同于前一节已经有非平凡消去的次幂端点，两个结论不矛盾。

## 近期模双曲线与光滑相邻数：共同来源条件

Tsz Ho Chan, *Close Points on a Modular Hyperbola*, INTEGERS 26A (2026), #A5，发表版本 2026-09-28。

- 原文：https://math.colgate.edu/~integers/aap5/aap5.pdf
- 精确位置：Theorem 2，第3页；§4，第5—7页。

令 $p>2$ 为素数、$(c,p)=1$，$\mathcal M$ 是具有正下密度 $\delta$ 的乘法封闭正整数集。该定理对每个固定 $\epsilon>0$ 给常数 $C_{\delta,\epsilon}$，保证模双曲线 $xy\equiv c\pmod p$ 上存在两个点 $(x,y)$、$(x+h,y+k)$，且

$$
h,k\in\mathcal M\cap
\left[1,C_{\delta,\epsilon}p^{1/4}
\exp\bigl((\log p)^{1/2+\epsilon}\bigr)\right].
$$

基点 $(x,y)$ 是存在性结论的一部分，没有固定为实际低亏损除数及其余因子；$h,k$ 是两点之间的增量。定理的方向是存在两点，而当前目标是排除指定的危险共同实现或支付其预算。固定光滑界的光滑数集合虽乘法封闭，下密度却为0；让光滑界随 $p$ 增长也不能忽略所需密度与常数的一致性。对数光滑稀疏核心不由这里的正下密度假设直接覆盖。仅出现同一模双曲线方程，不足以运输结论。

Erik Mulder, Bruno Sterner, Wessel van Woerden, *Large smooth twins from short lattice vectors*, arXiv:2509.17699v3，版本 2026-09-17。

- 原文：https://arxiv.org/pdf/2509.17699v3
- 精确位置：Theorem 1.3，第2页；Heuristic 3.1 及其应用，第5—6页。

论文给出搜索连续 $B$-光滑整数的短格向量算法；Theorem 1.3 的极值渐近明确以 Heuristic 3.1 为前提，不是无条件的相邻光滑数排除界。实际来源 $N=1+Vk$ 没有要求 $N$ 与 $N-1$ 同时 $B$-光滑，且素指标 Fibonacci 模数与低亏损权重也是额外条件。可以复用其候选搜索工具时，仍须另作这些实际来源检查；启发式极值和有限搜索不能支付 §233.5 的统一完整预算。

## Munsch–Shparlinski–Yau：另一个光滑度范围的存在下界

Marc Munsch, Igor E. Shparlinski, Kam Hung Yau,
*Smooth squarefree and square-full integers in arithmetic progressions*, arXiv:1810.02573v2 (2019版)。

- 原文：https://arxiv.org/html/1810.02573v2
- 精确位置：Theorem 1.1。

该定理固定

$$
\beta\in(23/24,1],\quad
\alpha\in(9/2-3\beta,3\beta],
$$

并对素数模数 $p\to\infty$、可逆剩余类 $(a,p)=1$、$x=p^{\alpha+o(1)}$、$y=p^{\beta+o(1)}$ 给平方自由光滑数的下界

$$
\psi^\sharp(x,y;p,a)\ge x^{1+o(1)}/p.
$$

当前 $V=F_r$ 不假设为素数，且 $Y=V^{o(1)}$，相当于光滑度指数趋于0，超出该固定 $\beta$ 范围。它给存在性下界，本来也不是排除 Robin 反例的上界。不能因目标中出现逆元、素指标、光滑核心等相同术语就转移其结论。

## 仍缺的联合关系

在这里列明的原文范围内，未找到可以直接用于当前参数、当前指定模数和当前剩余类的逐点排除定理。这个陈述只针对上述已读原文范围，不能推出不存在适用文献或当前路线原创。

一个可继续检验的精确接口是等差数列的矩分解。对正整数 $V$、非空有限正整数区间 $I$，$T=|I|$、$X=\max_{g\in I}(1+gV)$，

$$
\sum_{g\in I}\left(\frac{1+gV}{\varphi(1+gV)}\right)^s
=
\sum_{\substack{d\le X\\(d,V)=1}}a_s(d)
\#\{g\in I:g\equiv-V^{-1}\pmod d\}.
$$

每个内层计数为 $T/d+\varepsilon_d$，$|\varepsilon_d|\le1$。因此逐项用上界 $T/d+1$ 会留下加权边界项；不能在增长的 $s$ 下把它无条件丢弃。全区间矩法规避了这个边界项并给稀疏性，但没有识别哪个实际核心可以与其逆元小余因子共同实现。

最终需要的排除必须指向同一个 $N=CH=1+gV$：光滑核心的约数和增益、完整赋值截断损失、粗余因子的大小与素数下界、固定 Fibonacci 模数上的逆元同余，以及乘子区间。分别估计这些边缘数量或分别达到各自最优值，仍不足以排除它们共同组成一次 Robin 超界。

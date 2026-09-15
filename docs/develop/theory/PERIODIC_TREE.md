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

## Appendix U. Fibonacci square classes, valuation parity, and prime-square obstructions

### U.1. Definitions and classical arithmetic inputs

Let F_0=0, F_1=1 and F_(n+2)=F_(n+1)+F_n. Let phi be the original golden unit with phi^2=phi+1, and L_n=trace(phi^n). For a positive integer M, define

\[
\operatorname{core}(M)=\prod_{r\ \mathrm{prime},\ v_r(M)\ \mathrm{odd}}r,
\qquad s(n)=\operatorname{core}(F_n)\quad(n\ge1).
\]

The core is the unique positive squarefree d such that M=d*u^2 for a positive integer u. It is distinct from the radical, which retains every prime divisor. Write omega(M) for the number of distinct prime divisors, and Omega(M) for their number counted with multiplicity.

**Classical square-class theorem.** For positive indices, the only nonsingleton square classes of Fibonacci numbers have index sets `{1,2,12}` and `{3,6}`. Thus `s(m)=s(n)` at distinct indices only in one of those two sets. In particular F_n is a square only at n=1,2,12, and distinct positive odd indices always have different cores.

This is the square-class classification in P. Ribenboim, *Square classes of Fibonacci and Lucas numbers*, Portugaliae Mathematica 46(2) (1989), 159-175. An explicit statement by the same author is *FFF: (Favorite Fibonacci Flowers)*, Fibonacci Quarterly 43(1) (2005), 3-14, section 3.4, printed page 8: https://www.fq.math.ca/Papers1/43-1/paper43-1-1.pdf . The classification is an external classical theorem throughout this appendix.

**Classical valuation theorem.** If r is an odd prime, d,k are positive integers, and r divides F_d, then

\[
v_r(F_{dk})=v_r(F_d)+v_r(k).\tag{U.1}
\]

Also `v_5(F_t)=v_5(t)`. For r=2,

\[
v_2(F_t)=
\begin{cases}
0,&3\nmid t,\\
1,&t\equiv3\pmod6,\\
v_2(t)+2,&6\mid t.
\end{cases}\tag{U.2}
\]

These are Lengyel's formulas as recorded in L. A. Medina and E. Rowland, *p-regularity of the p-adic valuation of the Fibonacci sequence*, Fibonacci Quarterly 53 (2015), 265-271, Theorem 1.4, https://arxiv.org/abs/0910.2907 . Formula U.1 follows by applying the rank-based formula twice and subtracting the same initial valuation. It does not require that initial valuation to be one. The rank alpha(r) is the least positive d with r dividing F_d; the same source, Theorem 1.2, gives

\[
\alpha(r)\mid r-\left(\frac5r\right),\qquad r\ne2,5.
\tag{U.3}
\]

### U.2. Support transport under odd square multipliers

**Theorem.** For every m>=1 and every odd t>1,

\[
\boxed{s(m)\mid s(mt^2),\qquad s(m)\ne s(mt^2).}\tag{U.4}
\]

**Proof.** If an odd prime r has odd valuation in F_m, then U.1 changes that valuation by `v_r(t^2)=2v_r(t)`, so r still occurs in the core. For r=2, oddness of t preserves whether m is even and preserves v_2(m). If 3 divides m, U.2 therefore gives the same v_2 for F_m and F_(mt^2). If 3 does not divide m, the prime 2 is absent from s(m), which is sufficient for core divisibility. Thus every prime of s(m) remains in s(mt^2).

Equality would put the distinct indices m and mt^2 in one exceptional square class. The ratios of distinct larger to smaller indices in those classes are 2,6,12, and none is an odd square greater than one. Equality is impossible.

**Corollary.** For fixed m>=1, fixed odd t>1 and j>=0,

\[
\omega(s(mt^{2j}))\ge\omega(s(m))+j.\tag{U.5}
\]

**Proof.** Every step in U.4 is strict divisibility between squarefree integers, hence adds at least one prime divisor. Induction on j proves the bound.

### U.3. A lower bound for odd indices

**Lemma.** Suppose q is an odd prime other than five, and d is a positive integer every prime divisor of which is at least q. Then q does not divide F_d.

**Proof.** Otherwise alpha(q)>1 would divide d and also q-1 or q+1 by U.3. Every prime divisor of either even integer q-1 or q+1 is less than q. Taking a prime divisor of alpha(q) contradicts the hypothesis on d. The case d=1 is also immediate from F_1=1.

**Theorem.** For every positive odd integer m,

\[
\boxed{
\omega(s(m))\ge\Omega(m)-\left\lfloor\frac{v_5(m)}2\right\rfloor.
}\tag{U.6}
\]

**Proof.** Construct an increasing chain of odd divisors from 1 to m as follows. First multiply by all prime factors q>=7, in nonincreasing order and with multiplicity. Write `v_5(m)=2b+delta`, with delta either zero or one. Next multiply once by five if delta=1, then multiply by 25 exactly b times. Finally multiply by three `v_3(m)` times.

At a q>=7 step, or at a q=3 step, the lemma shows q does not divide the current Fibonacci number. Thus the multiplier q contributes no change to the valuation of any old odd prime divisor. Equation U.2 shows that any old factor two also retains its odd valuation, since all indices and multipliers are odd. The existing core therefore divides the next one. At the possible first five step, the current index is coprime to five, so U.1 and `v_5(F_d)=v_5(d)=0` give the same inclusion. At each 25 step the valuation at five changes by two and all other old valuations remain unchanged. Again the old core divides the new one.

All indices in the chain are odd and distinct. The square-class theorem makes every inclusion strict, so every step adds at least one prime divisor. The number of steps is

\[
\sum_{q\ne5}v_q(m)+b+\delta
=\Omega(m)-\left\lfloor v_5(m)/2\right\rfloor.
\]

The chain starts at s(1)=1, whose support is empty. Counting its strict inclusions proves U.6.

**Corollary.** For every positive odd n,

\[
\boxed{\omega(\operatorname{core}(F_{n^2}))\ge2\Omega(n)-v_5(n).}\tag{U.7}
\]

**Proof.** Apply U.6 to m=n^2, using `Omega(n^2)=2Omega(n)` and `v_5(n^2)=2v_5(n)`.

### U.4. Complete prime-value classification for A250093

The sequence OEIS A250093 is

\[
a(n)=\operatorname{core}(F_{n^2}),\qquad n\ge1.
\]

The externally stated conjecture asserts that its only prime values are 3 and 3001. The following gives the exact indices as well.

**Theorem.** For every n>=1,

\[
\boxed{\operatorname{Prime}(a(n))\ \Longleftrightarrow\ n=2\ \lor\ n=5.}\tag{U.8}
\]

**Proof for even n.** Since 4 divides n^2 and F_4=3, U.1 gives

\[
v_3(F_{n^2})=1+v_3(n^2/4)=1+2v_3(n),
\]

which is odd. Hence 3 divides a(n). If a(n) is prime, it equals 3=s(4). The square-class theorem forces n^2=4, because the square class of F_4 is a singleton. Thus n=2.

**Proof for odd n.** The case n=1 gives a(1)=1. For n>1, if a(n) is prime, U.7 gives

\[
1\ge 2\Omega(n)-v_5(n)
=v_5(n)+2\sum_{q\ne5}v_q(n).
\]

Every term on the right is nonnegative. Therefore no prime other than five divides n, and `v_5(n)<=1`. As n>1, necessarily n=5.

Conversely,

\[
F_4=3,\qquad F_{25}=75025=5^2\cdot3001.
\]

The number 3001 is prime: trial division by the primes through sqrt(3001)<55, namely 2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53, gives no divisor. Hence a(2)=3 and a(5)=3001 are prime. This completes both directions of U.8.

**Independent direct proof of the odd necessity.** If 5 divides odd n, the odd valuation of 3001 in F_25 persists in F_(n^2), because

\[
v_{3001}(F_{n^2})=1+v_{3001}(n^2/25)=1+2v_{3001}(n).
\]

Primality forces a(n)=3001=s(25), whence n=5 by square-class uniqueness. If odd n>1 is coprime to five, choose a prime q dividing n. Then q is odd and different from five, and q does not divide F_q. One can use the lemma of U.3 with d=q, or the standard congruence `F_q=(5/q) (mod q)`.

If an odd prime r has odd valuation in F_q, then r!=q and

\[
v_r(F_{n^2})=v_r(F_q)+v_r(n^2/q)
             =v_r(F_q)+2v_r(n),
\]

which is odd. If 2 occurs in s(q), then q=3, and both odd indices q and n^2 have Fibonacci valuation one at two. Consequently s(q) divides a(n). The square theorem ensures s(q)>1. Primality of a(n) therefore forces s(q)=s(n^2), impossible for the distinct positive odd indices q<n^2.

The source of the target is https://oeis.org/A250093 , introduced by Vincenzo Librandi on November 12, 2014. The proof above uses the published classical square-class and valuation theorems explicitly; it requires no assumption on the existence or nonexistence of Wall-Sun-Sun primes.

### U.5. Exact trace depths and the WSS obstruction

Let p be prime with p!=2,5, let `epsilon=(5/p)` and `N=p-epsilon`. The Frobenius identities for the original golden algebra give

\[
p\mid F_N,\qquad \varphi^N\equiv\epsilon\pmod p,
\qquad L_N\equiv2\epsilon\pmod p.
\]

Define the positive depth `s_p=v_p(F_N)`. The signed index N is even and positive.

**Theorem.** The two traces retain different depths:

\[
\boxed{v_p(L_N-2\epsilon)=2s_p,\qquad v_p(L_p-1)=s_p.}\tag{U.9}
\]

**Proof.** The discriminant identity gives

\[
(L_N-2\epsilon)(L_N+2\epsilon)=5F_N^2.
\]

The second factor has residue 4*epsilon, hence is a unit modulo p. All factors whose valuations are taken are nonzero: N>0, F_N>0, and the displayed product is positive. Additivity of the valuation gives the first equality.

The Fibonacci-Lucas addition identity gives `2L_p=epsilon*L_N+5F_N`. Therefore

\[
2(L_p-1)(L_N+2\epsilon)
=5F_N(L_N+2\epsilon+\epsilon F_N).
\]

Both parenthesized factors are units modulo p, and 2 and 5 are units. Also L_p>1 for odd primes p. Taking valuations proves the second equality.

**Corollary.** With the standard definition `WSS(p) iff p^2 divides F_N`,

\[
\mathrm{WSS}(p)
\iff p^4\mid L_N-2\epsilon
\iff p^2\mid L_p-1.\tag{U.10}
\]

At normalized first order, dividing in the integers before reducing gives

\[
2\frac{L_p-1}{p}\equiv5\frac{F_N}{p}\pmod p.\tag{U.11}
\]

At the return index N, the trace already has a second-order zero for every p. Its residue modulo p^2 cannot distinguish the WSS primes. The prime-index trace retains the original depth.

### U.6. Half-index parity localization

Set h=N/2. Then `F_N=F_h*L_h`, and `gcd(F_h,L_h)` divides two. Exactly one of F_h,L_h therefore vanishes modulo p.

**Theorem.** The branch is determined by p modulo four:

\[
\begin{array}{ll}
p\equiv1\pmod4:&p\mid F_h,\ p\nmid L_h,\ v_p(F_h)=s_p;\\
p\equiv3\pmod4:&p\mid L_h,\ p\nmid F_h,\ v_p(L_h)=s_p.
\end{array}\tag{U.12}
\]

**Proof.** In the original golden algebra over F_p, put x=phi^h. It satisfies `x^2=epsilon` and `norm(x)=(-1)^h`. If F_h=0 modulo p, x is scalar and `norm(x)=x^2=epsilon`. If L_h=0 modulo p, its conjugate is -x and `norm(x)=-x^2=-epsilon`. Exactly one alternative occurs. Computing the parity of `(p-epsilon)/2` in the two classes of p modulo four selects the stated alternative. The other factor in `F_N=F_h*L_h` is a unit, which proves the exact valuation statements.

**Corollary.** In the first branch WSS(p) is equivalent to `p^2|F_h`; in the second it is equivalent to `p^2|L_h`. Neither branch is excluded by these identities.

### U.7. A first-derivative obstruction to multiple-root lifting

Let p be prime and R=Z/p^2Z. Let rho:R->F_p be the actual reduction homomorphism.

**Lemma.** If rho(a)=rho(b)=0, then ab=0 in R.

**Proof.** Integer representatives of a and b are multiples of p, so their product is a multiple of p^2.

**Theorem.** Suppose f,g in R[X] reduce to `(X-1)^d,(X-1)^e`, respectively, with d,e>=2. Then

\[
fg\ne X^p-1.\tag{U.13}
\]

**Proof.** Reduction commutes with evaluation and formal differentiation. Thus `f(1),f'(1),g(1),g'(1)` all belong to the kernel of rho. The product rule and the lemma give

\[
(fg)'(1)=f'(1)g(1)+f(1)g'(1)=0.
\]

But `(X^p-1)'(1)=p`, which is nonzero in R. Equality of the polynomials is impossible.

**Theorem.** For `2<=d<=p-2` and every f in R[X] reducing to `(X-1)^d`,

\[
\boxed{f\nmid X^p-1.}\tag{U.14}
\]

**Proof.** If a cofactor g existed, reducing and applying Frobenius gives

\[
(X-1)^d\overline g=(X-1)^p\quad\text{in }\mathbb F_p[X].
\]

Since `(X-1)^d` is nonzero, cancellation gives `bar(g)=(X-1)^(p-d)`. The complementary exponent is at least two, contradicting U.13.

**Corollary and boundary.** For every prime p>=5, no polynomial reducing to `(X-1)^2` divides `X^p-1` over R, for any lifted coefficient choice. At p=3 the endpoint has a factor:

\[
X^3-1=(X-1)(X^2+X+1)\quad\text{in }(\mathbb Z/9\mathbb Z)[X].
\]

Its cofactor reduces to a simple root, so U.13 does not apply.

The excluded quadratic lift is the construction proposed in section 4.3 of M. Shi, X. Wang, J. Bouazzaoui, H. K. Kim and P. Sole, *Second order Recurrences, quadratic number fields and cyclic codes*, arXiv:2603.25343v1, https://arxiv.org/html/2603.25343v1 . The theorem excludes all coefficients in that multiple-root construction. The polynomial X^2-X-1 has discriminant five and is separable modulo p for p!=5, so U.14 is not a WSS nonexistence result for the golden unit.

### U.8. Which arithmetic information the square-class argument supplies

The statements U.4-U.8 control the support of odd prime valuations across different Fibonacci indices. They retain the possibly exceptional initial valuation in U.1 rather than assuming it equals one. In particular they remain valid in the presence of WSS primes.

Oddness of a valuation does not distinguish depth one from depth three, and evenness does not distinguish depth two from depth four. The new support bounds therefore do not decide whether `s_p>=2` at some prime p. The existence assertion

\[
\exists p\text{ prime},\ p\ne2,5:\quad p^2\mid F_{p-(5/p)}
\]

and the stronger assertion that there are infinitely many such primes remain distinct unproved statements here. The trace identities locate precisely where that missing depth information is preserved. A further proof must supply a constraint on these prime-index depths that is not already implied by their valuation parity.


## JP. Jacobsthal 最终周期与不动点

### JP.1 原递推、最终周期与从零时刻开始的周期

**定义。** Jacobsthal 数列由

$$
J_0=0,\qquad J_1=1,\qquad J_{n+2}=J_{n+1}+2J_n
$$

确定。对正整数 $m$、正整数 $t$ 与自然数 $N$，定义

$$
\operatorname{TailPeriod}(m,N,t)
\iff \forall n\ge N,\quad m\mid J_{n+t}-J_n.
$$

称 $t$ 为最终周期，若存在 $N$ 使上述关系成立。令 $\rho(m)$ 为最小正最终周期；令 $\mu(m)$ 为存在某个正周期的最早起始下标。最小值的存在性在下文证明。纯周期特指 $N=0$。

**命题。** 对全部 $n\ge0$，

$$
3J_n=2^n-(-1)^n,\qquad
J_{n+1}+J_n=2^n,\qquad
J_{n+1}-2J_n=(-1)^n.\tag{JP1}
$$

**证明。** 令 $S_n=J_{n+1}+J_n$、$D_n=J_{n+1}-2J_n$。原递推给出 $S_{n+1}=2S_n$ 与 $D_{n+1}=-D_n$，且 $S_0=D_0=1$。因此后两式成立；相减得第一式。

**命题。** 令 $G_L(c)$ 是长度 $L$、字母表 $\{0,\ldots,c\}$ 上无相邻非零字母的词数，则

$$
G_0(c)=1,\quad G_1(c)=c+1,\quad
G_{L+2}(c)=G_{L+1}(c)+cG_L(c).
$$

特别地，

$$
G_L(1)=F_{L+2},\qquad G_L(2)=J_{L+2}.\tag{JP2}
$$

**证明。** 按首字母是否为零分解。非零首字母有 $c$ 种选择，第二个字母被迫为零。取基例后，对 $L$ 作二步归纳即得两项特化。

### JP.2 从暂态中分离准确的最终周期

**定理。** 写 $m=2^a u$，其中 $u$ 为正奇数。若 $m>2$ 且 $t>0$，则

$$
\boxed{
\bigl(\exists N:\operatorname{TailPeriod}(m,N,t)\bigr)
\iff 3u\mid 2^t-1.
}\tag{JP3}
$$

右侧成立时，$\operatorname{TailPeriod}(m,a,t)$ 成立。

**证明，必要性。** 取一个起始下标 $N$。将 $n=N$ 与 $n=N+1$ 的周期同余相减，使用 JP1 的第三式，得到

$$
m\mid (-1)^N\bigl((-1)^t-1\bigr).
$$

若 $t$ 为奇数，则 $m\mid2$，与 $m>2$ 矛盾。因此 $t$ 为偶数。JP1 的第一式遂给出

$$
3(J_{N+t}-J_N)=2^N(2^t-1).
$$

左侧被 $3m$ 整除，所以 $3u\mid2^N(2^t-1)$。由于 $u$ 为奇数，$\gcd(3u,2^N)=1$，可在整数整除关系中约去 $2^N$，得到所需结论。

**证明，充分性。** 若 $3u\mid2^t-1$，则降模到 $3$ 可知 $t$ 为偶数。对任意 $n\ge a$，$2^a\mid2^n$，故

$$
3m=3\cdot2^a u\mid2^n(2^t-1)=3(J_{n+t}-J_n).
$$

在整数中约去 $3$ 即得 $m\mid J_{n+t}-J_n$。此处没有在模 $m$ 的环内对非单位 $3$ 作除法。

**定理。** 对 $m=2^a u>2$，

$$
\boxed{\rho(m)=\operatorname{ord}_{3u}(2).}\tag{JP4}
$$

并且 $\rho(1)=\rho(2)=1$。

**证明。** $2$ 与 $3u$ 互素。Euler 定理使得 $2^{\varphi(3u)}\equiv1\pmod{3u}$，所以正最终周期存在。JP3 使其最小值恰为所述乘法阶。模 $1$ 的数列为常数；模 $2$ 时 $J_0=0$，且 $J_n=1$ 对全部 $n\ge1$ 成立。

### JP.3 暂态长度恰等于二进估值

**定理。** 对全部正整数 $m$，

$$
\boxed{\mu(m)=v_2(m).}\tag{JP5}
$$

因此数列模 $m$ 存在纯周期，当且仅当 $m$ 为奇数。

**证明。** JP3 在 $m>2$ 时提供起始下标 $a=v_2(m)$；$m=1,2$ 的上界由前节直接得到。反之，设某个正周期 $t$ 从 $N$ 开始。JP1 的第二式和相邻两个下标的周期同余给出

$$
m\mid2^{N+t}-2^N=2^N(2^t-1).
$$

因为 $2^t-1$ 为奇数，右侧的二进估值恰为 $N$，故 $v_2(m)\le N$。这证明最小起始下标。对于 $m>1$，纯周期情形没有不动点：奇数模数的最小周期由 JP3 为偶数，而偶数模数没有纯周期。

### JP.4 三的幂上的精确阶

**引理。** 对每个正整数 $h$，

$$
\boxed{v_3(4^h-1)=1+v_3(h).}\tag{JP6}
$$

**证明。** 写 $h=3^r w$，其中 $3\nmid w$。几何和

$$
\frac{4^w-1}{4-1}=1+4+\cdots+4^{w-1}\equiv w\not\equiv0\pmod3
$$

表明 $v_3(4^w-1)=1$。若 $x\equiv1\pmod3$，写 $x=1+3z$，则

$$
x^2+x+1=3(1+3z+3z^2),
$$

该因子的三进估值恰为一。因此从 $x-1$ 到 $x^3-1$ 的估值恰增加一。重复 $r$ 次即得结论。

**定理。** 对每个 $b\ge0$，

$$
\boxed{\operatorname{ord}_{3^{b+1}}(2)=2\cdot3^b.}\tag{JP7}
$$

**证明。** 满足 $2^t\equiv1\pmod3$ 的正整数 $t$ 必为偶数，写成 $2h$。JP6 将 $3^{b+1}\mid2^t-1$ 等价为 $3^b\mid h$，故最小正 $t$ 恰为 $2\cdot3^b$。

### JP.5 Benfield–Lippard 猜想 6.3 的最终周期分类

**定理。** 对每个整数 $m>1$，

$$
\boxed{\rho(m)=m\iff\exists k\ge1:\ m=2\cdot3^k.}\tag{JP8}
$$

**证明，必要性。** $m=2$ 时 $\rho(m)=1$，故可设 $m>2$。由 JP3，$\rho(m)$ 为偶数。于是若 $\rho(m)=m$，可写

$$
m=2^a3^b v,\qquad a\ge1,\qquad \gcd(v,6)=1.
$$

由 JP4 与 Euler 定理，

$$
\begin{aligned}
2^a3^b v
&=\rho(m)\\
&\le\varphi(3^{b+1}v)\\
&=2\cdot3^b\varphi(v)\\
&\le2\cdot3^b v\\
&\le2^a3^b v.
\end{aligned}
$$

每一步必须取等号。由于 $v\ge1$，最后一步迫使 $a=1$。又因 $\varphi(v)=v$ 只在正整数 $v=1$ 成立，故 $v=1$。排除 $m=2$ 后，得到 $b\ge1$。

**证明，充分性。** 若 $m=2\cdot3^k$ 且 $k\ge1$，则 JP4 与 JP7 给出

$$
\rho(m)=\operatorname{ord}_{3^{k+1}}(2)=2\cdot3^k=m.
$$

这完成全部模数上的两个方向。最终周期约定与 JP.3 的纯周期结论必须分开使用。

### JP.6 非不动点的减半律与迭代界

**定理。** 若 $m$ 为正偶数且 $\rho(m)\ne m$，则

$$
\boxed{\rho(m)\le m/2.}\tag{JP9}
$$

若 $m>1$ 为奇数，则 $m=3^b$ 时 $\rho(m)=2m$ 且 $2m$ 已是不动点；否则 $\rho(m)<m$。

**证明。** 写 $m=2^a3^b v$，$\gcd(v,6)=1$。若 $v>1$，Euler 定理和 $\varphi(v)$ 为偶数给出：指数

$$
E=3^b\varphi(v)
$$

同时是 $\operatorname{ord}_{3^{b+1}}(2)=2\cdot3^b$ 与 $\operatorname{ord}_v(2)$ 的倍数。由于两个模数互素，$2^E\equiv1\pmod{3^{b+1}v}$。因此

$$
\rho(m)\le E<3^b v=m/2^a.
$$

这同时处理奇数与偶数模数中的 $v>1$ 情形。若 $v=1$，$m>2$ 时 JP7 给出 $\rho(m)=2\cdot3^b$。在偶数非不动点情形，JP8 迫使 $a\ge2$，故 $\rho(m)\le m/2$。余下的 $m=2$ 直接有 $\rho(m)=1$。当 $a=0,b\ge1$，得到 $\rho(3^b)=2\cdot3^b$，而这个值由 JP8 已是不动点。

**推论。** 每个正整数的 $\rho$ 迭代都到达

$$
\{1\}\cup\{2\cdot3^k:k\ge1\}
$$

中的一个不动点，不存在长度大于一的周期轨道。若 $T(m)$ 为首次到达不动点所需的迭代次数，则

$$
\boxed{T(m)\le1+\lfloor\log_2m\rfloor.}\tag{JP10}
$$

**证明。** 偶数轨道在到达不动点前每一步至少减半，且始终为正整数，故终止并至多经历 $\lfloor\log_2m\rfloor$ 步。奇数 $m>1$ 若是三的幂，一步即达不动点；否则第一步变成小于 $m$ 的偶数，再应用减半律。$m=1$ 时 $T(m)=0$。非平凡周期会包含严格下降的偶数步骤，故不可能存在。


## GP3. 黄金三次幂层与 WSS 的素数间深度约束

### GP3.1 经典三次幂层及其确切内容

对 $j\ge1$，定义

$$
n_j=3^j,\qquad
C_j=L_{n_j}^2+1.
$$

**定理。** 有

$$
\boxed{
F_{3n_j}=F_{n_j}C_j,\qquad
C_j+3=5F_{n_j}^2,\qquad
\gcd(C_j,F_{n_j})=1.
}\tag{GP31}
$$

并且

$$
C_1=17,\qquad C_{j+1}=C_j^3+3C_j^2-3.\tag{GP32}
$$

**证明。** 对奇数 $n$，黄金共轭满足 $\varphi^n\psi^n=-1$。展开三次幂差得

$$
F_{3n}=F_n(L_n^2+1).
$$

判别式恒等式 $L_n^2-5F_n^2=-4$ 给出第二式。两个因子的公因子因而整除三；但 $n$ 为奇数时

$$
\gcd(F_n,3)=\gcd(F_n,F_4)=F_{\gcd(n,4)}=F_1=1.
$$

故其最大公因子为一。三次幂和给出 $L_{3n}=L_n^3+3L_n$，再平方加一，得到

$$
(L_n^3+3L_n)^2+1=(L_n^2+1)^3+3(L_n^2+1)^2-3.
$$

首值来自 $L_3=4$。这也是经典序列 A002814 从第三项开始的部分：若该序列按 $a(0)=1,a(1)=2$ 编号，则 $C_j=a(j+1)$。

**定理。** 每个 $C_j$ 为大于一的奇数、不是完全平方数，并且不同 $C_j$ 两两互素。

**证明。** $L_3=4$ 为正偶数，递推 $L_{3n}=L_n^3+3L_n$ 保持正偶性，所以 $C_j$ 为奇数且

$$
L_{n_j}^2<C_j<(L_{n_j}+1)^2.
$$

若 $i<j$，则 $C_i\mid F_{3^{i+1}}\mid F_{3^j}$。GP31 使 $\gcd(C_i,C_j)=1$。这些性质属于经典三次幂数列的算术结构。

### GP3.2 每一层全部素因子的出现秩

令 $\alpha(p)$ 为素数 $p$ 在 Fibonacci 数列中的最小正零下标。

**定理。** 若 $p\mid C_j$ 为素数，则

$$
\boxed{
p\notin\{2,3,5\},\qquad
\alpha(p)=3^{j+1},\qquad p\equiv1\pmod4.
}\tag{GP33}
$$

**证明。** 奇性排除二；GP31 第二式模五为 $C_j\equiv2\pmod5$，排除五。模三同样可用 GP32：$C_1\equiv2$ 且 $2^3+3\cdot2^2-3\equiv2$，故排除三。

由 GP31，$p\mid F_{3^{j+1}}$ 且 $p\nmid F_{3^j}$。出现秩整除任何零下标，因此 $\alpha(p)\mid3^{j+1}$，却不整除 $3^j$。三的幂的约数只有三的幂，故出现秩恰为 $3^{j+1}$。

此外 $L_{n_j}^2\equiv-1\pmod p$。因为 $p$ 为奇素数，其乘法群中有阶为四的元素，因此 $4\mid p-1$。

### GP3.3 实际 WSS 深度等于该层中的素因子重数

记

$$
\epsilon_p=\left(\frac5p\right),\qquad
N_p=p-\epsilon_p,\qquad
s_p=v_p(F_{N_p}).
$$

使用标准 Fibonacci 出现秩定理和估值定理：$\alpha(p)\mid N_p$，且对 $p\ne2,5$，在 $p\mid F_d$ 时

$$
v_p(F_{dk})=v_p(F_d)+v_p(k).
$$

这里的初始估值不预设为一。

**定理。** 对每个素数 $p\mid C_j$，

$$
\boxed{s_p=v_p(C_j).}\tag{GP34}
$$

因此

$$
\boxed{
p\mid C_j\quad\Longrightarrow\quad
\bigl(\mathrm{WSS}(p)\iff p^2\mid C_j\bigr).
}\tag{GP35}
$$

**证明。** GP31 给出

$$
v_p(F_{3^{j+1}})=v_p(C_j).
$$

又由 GP33，$3^{j+1}=\alpha(p)$。令 $h=N_p/\alpha(p)$。因为 $p\nmid N_p$，故 $p\nmid h$。估值定理于是给出

$$
s_p=v_p(F_{\alpha(p)h})=v_p(F_{\alpha(p)})=v_p(C_j).
$$

标准 WSS 条件为 $s_p\ge2$，由此得到第二式。

### GP3.4 每层强迫一个奇初始深度素数

**定理。** 对每个 $j\ge1$，至少存在一个素数 $p_j$ 满足

$$
\boxed{
p_j\mid C_j,\quad
\alpha(p_j)=3^{j+1},\quad
p_j\equiv1\pmod4,\quad s_{p_j}\text{ 为奇数}.
}\tag{GP36}
$$

这些素数在不同层互不相同。

**证明。** $C_j$ 不是完全平方数。唯一素因子分解中必有至少一个素数的指数为奇数。取这样的 $p_j$，由 GP33–GP34 得到全部结论。两两互素性或者不同的出现秩都保证各层所选素数不同。

**定量推论。** 令 $\varphi=(1+\sqrt5)/2$。对 $X\ge\varphi^6$，至少有

$$
\left\lfloor\log_3\left(\frac{\log X}{2\log\varphi}\right)\right\rfloor
\tag{GP37}
$$

个不超过 $X$ 的不同素数，具有三的纯幂出现秩、模四余一且 WSS 初始深度为奇数。

**证明。** 对奇数 $n$，$L_n=\varphi^n-\varphi^{-n}$，故

$$
C_j=\varphi^{2\cdot3^j}+\varphi^{-2\cdot3^j}-1
<\varphi^{2\cdot3^j}.
$$

令 GP37 中的整数为 $K$。对 $1\le j\le K$，有 $C_j<X$。GP36 在每个这样的层给出一个不同的素数 $p_j\le C_j<X$。

### GP3.5 存在性边界

GP36 强迫的是奇数深度，即 $1,3,5,\ldots$。它没有排除所有被选素数都具有深度一。因此 GP36–GP37 并不证明存在 WSS 素数，也不证明存在无穷多个非 WSS 素数。

对本族有精确的受限存在性等价：

$$
\boxed{
\exists j\ge1:\ C_j\text{ 非平方自由}
\iff
\exists p\text{ 为 WSS 素数}:\ \alpha(p)=3^k\text{ 对某个 }k\ge2.
}\tag{GP38}
$$

**证明。** 左向由 GP35。反向若 $\alpha(p)=3^k$ 且 $k\ge2$，则 $p\mid F_{3^k}$ 且 $p\nmid F_{3^{k-1}}$。GP31 使 $p\mid C_{k-1}$，再由 GP34 与 $s_p\ge2$ 得 $p^2\mid C_{k-1}$。

GP38 只处理纯三幂出现秩的素数，不能替代全部素数上的 WSS 存在问题。这条路线要得到 WSS 实例，仍须证明至少一个 $C_j$ 有重复素因子，或证明另一族的同等深度结论。单纯增加奇偶、平方类或固定素数提升恒等式，不能填补这个存在性步骤。

## FD. Fibonacci 素数幂剩余密度的零聚点与 WSS 定量阈值

### FD.1 剩余像与单调性

对素数 p 和整数 k>=1，定义

\[
S_k(p)=\{F_n\bmod p^k:n\ge0\},\qquad
D_k(p)=|S_k(p)|/p^k,\qquad
\delta(p)=\lim_{k\to\infty}D_k(p).
\]

**引理。** 上述极限存在，并满足

\[
0\le\delta(p)\le D_{k+1}(p)\le D_k(p)\le D_1(p)\le\pi(p)/p.
\tag{FD1}
\]

**证明。** 降模映射 S_(k+1)(p)->S_k(p) 满射，每个纤维至多有 p 个元素。故 |S_(k+1)(p)|<=p|S_k(p)|，得到单调性。数列非负，因而收敛。模 p 的全部 Fibonacci 值都在一个长度 pi(p) 的周期中出现，故最后一个不等式成立。

Bragman 和 Rowland 在 *Limiting density of the Fibonacci sequence modulo powers of a prime*, Research in Number Theory 11, 88 (2025), DOI 10.1007/s40993-025-00667-1 的引言中问，是否存在使 delta(p) 任意小的素数。他们的定理 1 还证明每个 delta(p) 为严格正有理数。以下回答前一个问题，只确定零这个聚点。

### FD.2 明确使用的最大素因子定理

对非零整数 M，令 P(M) 为 |M| 的最大素因子，并约定 P(1)=1。记 Phi_n(A,B) 为齐次分圆多项式。Stewart 的定理断言：若 (A+B)^2 与 AB 为非零整数，且 A/B 不是单位根，则存在有效可计算的常数 n_0，使全部 n>n_0 满足

\[
P(\Phi_n(A,B))>
n\exp\!\left(\frac{\log n}{104\log\log n}\right).
\tag{FD2}
\]

这里使用 C. L. Stewart, *On divisors of Lucas and Lehmer numbers*, Acta Mathematica 211 (2013), 291-314, DOI 10.1007/s11511-013-0105-y；arXiv:1008.1274 的定理 1。FD2 是已有定理，不是下文重新证明的结论。

取 A=phi=(1+sqrt(5))/2、B=psi=(1-sqrt(5))/2，则 (A+B)^2=1，AB=-1，且 |A/B|=phi^2>1。全部假设都成立。对 j>=1 令 r_j=3^(j+1)，GP3 中的 C_j 满足

\[
\Phi_{r_j}(\phi,\psi)
=\frac{\phi^{3^{j+1}}-\psi^{3^{j+1}}}
       {\phi^{3^j}-\psi^{3^j}}
=\frac{F_{3^{j+1}}}{F_{3^j}}
=C_j.
\tag{FD3}
\]

分母非零，因为 phi/psi 不是单位根。第一式也可以由
Phi_(3^(j+1))(A,B)=A^(2*3^j)+A^(3^j)B^(3^j)+B^(2*3^j)
直接验证。

### FD.3 零是一个聚点，且小密度对全部精度同时成立

**定理。** 令 p_j=P(C_j)。这些素数互不相同，并满足

\[
\alpha(p_j)=r_j=3^{j+1},\qquad
p_j\equiv1\pmod4,\qquad \pi(p_j)=4r_j.
\tag{FD4}
\]

对全部充分大的 j 及全部 k>=1，

\[
0<\delta(p_j)\le D_k(p_j)
<4\exp\!\left(-\frac{\log r_j}{104\log\log r_j}\right).
\tag{FD5}
\]

特别地，

\[
\boxed{\inf_{p\ {\rm prime}}\delta(p)=0,
\qquad \lim_{j\to\infty}\delta(p_j)=0.}
\tag{FD6}
\]

**证明。** GP33 给出出现秩与模四条件，GP31 给出不同层的互素性，故 p_j 互不相同。令 r=r_j。模 p_j 时 Q^r=cI，其中 c=F_(r-1)，因为 F_r=0。取行列式得到 c^2=(-1)^r=-1，故 c 的阶为四。若 Q^t=I，则 r|t；写 t=rh 后有 Q^t=c^h I，因此四整除 h。这既证明 pi(p_j)=4r，又不引入新的周期约定。

当 r_j>n_0 时，FD2-FD3 给出
p_j>r_j exp(log r_j/(104 log log r_j))。再用 FD1 的
D_k(p_j)<=pi(p_j)/p_j=4r_j/p_j，得到 FD5 的上界。严格正性来自 Bragman-Rowland 的定理 1。由于 log r_j/log log r_j 趋于无穷，右边趋于零，夹逼得到 FD6。

**量词形式。** 对每个 eta>0 和每个素数界 B，都存在素数 p>B，使

\[
0<\delta(p)<\eta,
\qquad \forall k\ge1,\quad D_k(p)<\eta.
\tag{FD7}
\]

**证明。** FD2 使 p_j 趋于无穷，FD5 对 k 的上界独立于 k，故取足够大的同一个 j 即可。

由于所有 delta(p)>0，零是聚点而不是密度值。证明没有假设存在无穷多个 Fibonacci 素数，没有假设所有 Wall 指数等于一，也没有确定全部聚点。

### FD.4 Wall 指数处的周期与两个数值计数

以下 p>=7 为素数，a=alpha(p)，epsilon=(5/p)，e=v_p(F_(p-epsilon))。由出现秩和 U.1，p 不整除 (p-epsilon)/a，因此

\[
e=v_p(F_a),\qquad e\ge1.\tag{FD8}
\]

在 R=Z/(p^e) 中 Q^a=cI，且 c^2=(-1)^a。若 a 为奇数，则 c^2=-1，所以 Q^(2a)=-I 且 pi(p^e)=pi(p)=4a。若 a=2 mod4，则 c=1 modp；由 (c-1)(c+1)=0 modp^e 及 c+1 为单位，得到 c=1 modp^e，故 pi(p^e)=pi(p)=a。若 4|a，则同理 c=-1 modp^e，故 pi(p^e)=pi(p)=2a。这些模 p 的周期三分律是 Vinson 的经典定理，也见 Bragman-Rowland 定理 7；降模保证所给周期没有进一步缩短。

令 r=pi(p)。在 0<=i<r 中去掉 Lucas 零点 L_i=0 modp，记余下的指标集为 I。定义

\[
N_p=|\{F_i\bmod p^e:i\in I\}|.
\]

令 Z_p 为 Lucas 零点 i 的个数，其 F_i modp^e 没有在 I 中出现。Bragman-Rowland 定理 1 给出

\[
\delta(p)=\frac{N_p}{p^e}
+\frac{Z_p}{2p^{2e-1}(p+1)},\qquad 0\le Z_p\le2.
\tag{FD9}
\]

这里 N_p 计不同的数值，Z_p 按该定理计指标，不能互换。Lucas 零点由其命题 9 分类：a 奇数时没有；a=2 mod4 时只有 a/2；4|a 时有 a/2 与 3a/2。

### FD.5 奇偶配对给出严格的计数上界

**定理。** 对每个素数 p>=7，

\[
1\le N_p\le p-1.\tag{FD10}
\]

**证明。** i=0 是 Lucas 非零点并提供值零，故 N_p>=1。由于 F_1,...,F_6 的素因子都不超过五，a>=7。以下全部数值同余都在 R=Z/(p^e) 中进行。使用整数恒等式 F_(-i)=(-1)^(i+1)F_i，将指标视为相应周期的剩余类。

若 a 为奇数，r=4a 且 F_(i+2a)=-F_i。定义保持数值的对合

\[
T(i)=
\begin{cases}
2a-i\pmod{4a},&i\text{ 偶},\\
-i\pmod{4a},&i\text{ 奇}.
\end{cases}
\]

这个对合没有不动点：第一种固定方程要求 i=a 或 3a，与偶性矛盾；第二种要求 i=0 或 2a，与奇性矛盾。因此有 2a 个二元轨道。零值占据两个不同轨道 {0,2a} 与 {a,3a}；此外 F_1=F_2=1，指标一与二因奇偶不同而属于不同轨道。这是两项不同的数值重合，所以 N_p<=2a-2。又 a 为奇数且 a|(p-epsilon)，故 2a<=p-epsilon<=p+1，得到 N_p<=p-1。

若 a=2 mod4，r=a，仅去掉一个 Lucas 零点 a/2。该点不是一或二，因为 a>=7。集合 I 有 a-1 个指标，其中 F_1=F_2，故 N_p<=a-2<=p-1。

若 4|a，r=2a 且 F_(i+a)=-F_i。在偶指标处令 T(i)=a-i mod2a，在奇指标处令 T(i)=-i mod2a。保持数值的计算与第一种相同。其全部不动点恰为 a/2 和 3a/2，正好是删去的两个 Lucas 零点；所以 I 分成 a-1 个二元轨道。因为 a>=8，指标一与二都在 I 中，位于不同奇偶轨道，却有相同值一。于是 N_p<=a-2<=p-1。三种情形覆盖全部情况。

### FD.6 WSS 与随素数移动的密度门槛

**定理。** 对每个素数 p>=7，

\[
\boxed{\mathrm{WSS}(p)\iff e\ge2
\iff \delta(p)<\frac1p.}\tag{FD11}
\]

**证明。** e=1 时，由 FD9、FD10 得 delta(p)>=N_p/p>=1/p。若 e>=2，则

\[
\delta(p)
\le\frac{p-1}{p^2}+\frac{1}{p^3(p+1)}
<\frac1p.
\]

这证明两方向。p=3 可由 F_4=3 和 delta(3)=1 独立处理，得到同一判断；p=2,5 不纳入这里的标准 WSS 定义。

**推论。** 将 delta(p) 写成既约分数 A_p/B_p，B_p>0。对 p>=7，若 Z_p=0，则 v_p(B_p)=e；若 Z_p>0 且 e>=2，则 v_p(B_p)=2e-1；若 e=1，则 v_p(B_p)<=1。因此

\[
\boxed{\mathrm{WSS}(p)\iff p^2\mid B_p.}\tag{FD12}
\]

**证明。** Z_p=0 时，1<=N_p<p 保证 N_p 与 p 互素。Z_p>0 时，通分后的分子为
2N_p p^(e-1)(p+1)+Z_p。
当 e>=2，该分子模 p 为 Z_p，取值一或二，非零，故约分不移除任何 p 因子。当 e=1，原分母 2p(p+1) 的 p 指数为一，约分后至多为一。这些情形给出最后的等价式。

FD6 的零聚点结论没有给出 FD11 所需的移动阈值：它使 delta(p_j) 趋于零，而 WSS 要求 p_j delta(p_j)<1。两者之间不能交换量词或省去因子 p_j。特别地，Stewart 的大小界没有强迫 C_j 出现重复素因子。WSS 存在性和无穷性没有在本节得到证明。

FD3 的最大素因子选择不必等于 GP36 选出的奇重数素因子。本节不声称所选最大素因子的 Wall 指数为奇数。


### FD.7 从精确剩余密度恢复完整初始估值

**定理。** 设 $p\ge7$ 为素数，沿用 FD.4 中的实际 Fibonacci 密度 $\delta(p)$、初始估值 $e=v_p(F_{p-(5/p)})$ 与计数 $N_p,Z_p$。则

$$
\boxed{p^{-e}\le\delta(p)<p^{1-e}.}\tag{FD13}
$$

因而对每个整数 $h\ge1$，

$$
\boxed{e\ge h+1\iff\delta(p)<p^{-h},\qquad
 e=\left\lceil-\frac{\log\delta(p)}{\log p}\right\rceil.}\tag{FD14}
$$

**证明。** FD9 与 $N_p\ge1$ 给出下界。由 $N_p\le p-1$、$Z_p\le2$，

$$
\delta(p)\le\frac{p-1}{p^e}+
 \frac1{p^{2e-1}(p+1)}<\frac p{p^e},
$$

其中严格不等式等价于 $1<p^{e-1}(p+1)$，由 $e\ge1$ 成立。各半开区间 $[p^{-e},p^{1-e})$ 互不相交，立刻得到阈值等价；取对数得到 $e-1<-\log\delta(p)/\log p\le e$，再取上整得到最后一式。

**定理。** 同一精确密度还恢复两个计数：

$$
\boxed{
 N_p=\lfloor p^e\delta(p)\rfloor,\qquad
 Z_p=2p^{e-1}(p+1)\bigl(p^e\delta(p)-N_p\bigr).
}\tag{FD15}
$$

**证明。** FD9 乘以 $p^e$ 得

$$
p^e\delta(p)=N_p+\frac{Z_p}{2p^{e-1}(p+1)}.
$$

末项属于 $[0,1)$，因为 $0\le Z_p\le2$ 且 $p\ge7$、$e\ge1$。取下整得到第一式，移项得到第二式。

因此在 $e\ge1$、$1\le N\le p-1$、$Z\in\{0,1,2\}$ 的参数域内，FD9 的有理数表达对三元组 $(e,N,Z)$ 为单射。对于已给定的精确有理密度，可以反复乘以 $p$，直到第一次达到或超过一；乘法次数就是 $e$，随后用 FD15 恢复 $N,Z$。这不需要数值计算对数。它要求精确密度作为输入，不声称从未带误差界的近似密度恢复这些整数。

FD14 的 $h=1$ 情形是 FD11，其余情形读取全部初始提升深度。它们都是既有密度公式与 FD10 的后果，没有迫使任何素数满足 $e\ge2$。计算密度本身可能需要未知的初始估值，因此该解码结论也不构成绕过 WSS 算术的独立求解算法。


## FSP. 含一的不同 Fibonacci 数之和与 A339621

### FSP.1 正值只计一次与前缀和

令 $F_0=0,F_1=1,F_{n+2}=F_{n+1}+F_n$，并定义不同的正 Fibonacci 值集合

$$
\mathcal F_+=\{F_n:n\ge2\}=\{1,2,3,5,8,\ldots\}.
$$

下标从二开始使值一只出现一次。$F_n$ 在 $n\ge2$ 上严格递增。

**引理。** 对每个 $n\ge3$，

$$
\sum_{i=2}^{n-2}F_i=F_n-2.\tag{FSP1}
$$

当 $n=3$ 时左侧为空和。**证明。** 首例两侧为零；从 $n$ 到 $n+1$ 的差为 $F_{n-1}$，由 Fibonacci 递推得到归纳步。

### FSP.2 前驱强迫与完整有限集分类

**定理。** 若 $S\subset\mathcal F_+$ 是有限集且 $1\in S$，则

$$
\boxed{
\sum_{x\in S}x\in\mathcal F_+
\iff
\exists r\ge1:\quad
S=\{1\}\cup\{F_{2j+1}:1\le j<r\}.
}\tag{FSP2}
$$

在成立时 $r$ 唯一，且 $\sum_{x\in S}x=F_{2r}$。

**证明。** 设和为 $F_n$，选其唯一下标 $n\ge2$。若 $n=2$，正性迫使 $S=\{1\}$。若 $n>2$，集合不能含 $F_n$ 或更大的值，因为它还含有不同的正值一。若 $F_{n-1}\notin S$，则 $S$ 中每个值都属于 $\{F_2,\ldots,F_{n-2}\}$，故由 FSP1，

$$
\sum_{x\in S}x\le F_n-2<F_n,
$$

矛盾。因此 $F_{n-1}$ 被迫属于 $S$。$n=3$ 时集合只能为 $\{1\}$，其和为一而 $F_3=2$，所以不存在所需表示。$n\ge4$ 时，$F_{n-1}>1$，删去它仍保留一，余下的和为 $F_{n-2}$。按下标强归纳，目标下标必须是偶数，且连续被迫删去的项恰为 $F_{2r-1},F_{2r-3},\ldots,F_3$，最终剩下 $F_2=1$。这证明必要性及集合形状。

反向，由递推逐项相加得

$$
1+F_3+F_5+\cdots+F_{2r-1}=F_{2r}.
$$

因此所示集合确实有该和。严格递增性给出 $r$ 的唯一性。证明允许相邻下标同时出现，例如 $F_2$ 与 $F_3$；它没有假定 Zeckendorf 的非相邻条件。

### FSP.3 全部正整数上的 Fibonacci 约数和

对正整数 $M$，定义实际约数值集合与和

$$
\mathcal D_F(M)=\{d>0:d\mid M,\ d\in\mathcal F_+\},\qquad
\sigma_F(M)=\sum_{d\in\mathcal D_F(M)}d.
$$

**定理。** 对每个 $M>0$，若 $\sigma_F(M)$ 为 Fibonacci 数，则存在唯一 $r\ge1$，使

$$
\boxed{
\sigma_F(M)=F_{2r},\qquad
\mathcal D_F(M)=\{1\}\cup\{F_{2j+1}:1\le j<r\}.
}\tag{FSP3}
$$

**证明。** $\mathcal D_F(M)$ 是有限的不同正 Fibonacci 值集合，并且因 $1\mid M$ 而包含一。其和为正，因此所给 Fibonacci 值属于 $\mathcal F_+$。应用 FSP2 即得。

**推论，OEIS A339621。** 对每个整数 $m\ge0$，令

$$
a(m)=\sigma_F(m^2+1).
$$

若 $a(m)$ 是 Fibonacci 数，则

$$
\boxed{\exists r\ge1:\quad a(m)=F_{2r}.}\tag{FSP4}
$$

**证明。** $m^2+1>0$，应用 FSP3。这是 Michel Lagneau 于 2020 年 12 月 10 日提出、OEIS A339621 COMMENTS 中标为猜想的命题。证明实际上适用于全部正整数 $M$，不需要 $M=m^2+1$ 或 $3\nmid M$。

FSP4 对值一给出 $1=F_2$，并不否认 $1=F_1$；结论是存在偶下标表示。若允许重复一，$1+1=F_3$ 将破坏结论；若删去必须含一的假设，$\{2,3\}$ 的和为 $F_5$，同样破坏结论。FSP3 没有断言每个偶下标 Fibonacci 数都能由某个 $m^2+1$ 的约数和实现。


## 附录 EMW：Fibonacci 平方中心与非 WSS 秩支持

**定义。** 正整数称为强力数，当且仅当每个素数因子均以至少二次幂出现。令 $F_0=0$、$F_1=1$、$F_{n+2}=F_{n+1}+F_n$。对素数 $p\ne2,5$，定义

$$
\rho(p)=\min\{n\ge1:p\mid F_n\},\qquad
q_p=\frac{F_{p-(5/p)}}p\pmod p.
$$

对 $60\mid M$，定义不同秩组成的集合

$$
\mathcal R_1=\{\rho(p):p\ne2,5\text{ 为素数},\ q_p\ne0\},\qquad
\mathcal R_1(M)=\{r\in\mathcal R_1:\gcd(r,M)\le2\}.
$$

同一秩只计一次。令 EMW 表示不存在连续三个正强力数的命题。

### EMW.1 初始商与简单素因子

记

\[
\varphi^2=\varphi+1,\qquad
\mathcal O_K=\mathbb Z[\varphi],\qquad
\operatorname N(\varphi)=-1.
\]

对素数 \(p\)，定义

\[
\rho(p)=\min\{n\ge1:p\mid F_n\}.
\]

存在性、强整除性与黄金 Frobenius 给出

\[
p\mid F_n\iff\rho(p)\mid n,
\qquad
\rho(p)\mid p-\left(\frac5p\right)\quad(p\ne2,5).
\tag{EMW-B1}
\]

此外 \(\rho(p)\ge3\)，且

\[
\rho(2)=3,\qquad\rho(3)=4,\qquad\rho(5)=5.
\tag{EMW-B2}
\]

**引理 1。** 对 \(p\ne2,5\)，

\[
q_p\ne0\iff v_p(F_{\rho(p)})=1.
\tag{EMW-B3}
\]

**证明。** 写 \(r=\rho(p)\)、\(N=p-(5/p)=kr\)，并在黄金整数中写

\[
\varphi^r=a+b\varphi,
\qquad a=F_{r-1},\quad b=F_r.
\]

有 \(p\mid b\)。范数恒等式模 \(p\) 给出
\(a^2\equiv(-1)^r\pmod p\)，所以 \(p\nmid a\)。又因 \(p\nmid N\)，有 \(p\nmid k\)。在自由基 \(1,\varphi\) 上模 \(p^2\) 展开：

\[
\varphi^N=(a+b\varphi)^k
\equiv a^k+ka^{k-1}b\varphi\pmod{p^2\mathcal O_K}.
\]

高于一次的项都含有 \(b^2\)。比较 \(\varphi\) 坐标，得

\[
F_N\equiv ka^{k-1}F_r\pmod{p^2}.
\]

系数 \(ka^{k-1}\) 模 \(p\) 可逆。因此 \(p^2\mid F_N\) 当且仅当 \(p^2\mid F_r\)，从而得到 (EMW-B3)。证毕。

**推论 2。** 若 \(p\ne2,5\) 且 \(p\parallel F_m\)，则 \(q_p\ne0\)，且 \(\rho(p)\mid m\)。

**证明。** 由 (EMW-B1)，\(r=\rho(p)\mid m\)，再由 Fibonacci 整除性有 \(F_r\mid F_m\)。既然 \(p\mid F_r\) 且 \(p^2\nmid F_m\)，必有 \(p\parallel F_r\)。应用引理 1。证毕。

这里 \(p\parallel A\) 表示 \(p\mid A\) 而 \(p^2\nmid A\)。仅仅知道某个素数整除 \(F_m\) 并不足以推出非 WSS；指数恰为一是必要环节。

### EMW.2 四个相邻指标与连续三元组

**引理 3。** 对 \(n\ge3\)，

\[
F_{n-1}F_{n+1}=F_n^2+(-1)^n,
\qquad
F_{n-2}F_{n+2}=F_n^2-(-1)^n.
\tag{EMW-C1}
\]

若 \(4\mid n\)，则

\[
F_n^2-1=F_{n-2}F_{n+2},\qquad
F_n^2+1=F_{n-1}F_{n+1},
\tag{EMW-C2}
\]

并且两个乘积各自的因子互素。

**证明。** 第一式是 Cassini 恒等式。设 \(A=F_{n-1}\)、\(B=F_n\)，则
\(F_{n-2}=B-A\)、\(F_{n+2}=A+2B\)，所以第二个乘积等于
\(2B^2-A(A+B)=B^2-(-1)^n\)。

若 \(4\mid n\)，则 \(\gcd(n-1,n+1)=1\)、\(\gcd(n-2,n+2)=2\)。强整除性和 \(F_1=F_2=1\) 给出因子的互素性。证毕。

两个强力数的乘积仍为强力数；反之，互素乘积是强力数时，每个因子均为强力数。因此，在 \(4\mid n\)、\(n\ge4\) 时，(EMW-C2) 给出精确对应：

\[
\begin{aligned}
&F_n^2-1,F_n^2,F_n^2+1\text{ 均为强力数}\\
&\quad\iff
F_{n-2},F_{n-1},F_{n+1},F_{n+2}\text{ 均为强力数}.
\end{aligned}
\tag{EMW-C3}
\]

中间的 \(F_n^2\) 本身总是正平方。

### EMW.3 有限素数集合的条件性排除

**定理 4，条件于 EMW。** 给定任意有限素数集合 \(S\)，令

\[
M=\operatorname{lcm}\bigl(60,\{\rho(p):p\in S\}\bigr).
\]

则存在素数 \(p\notin S\cup\{2,5\}\)，使

\[
q_p\ne0,\qquad
\gcd(\rho(p),M)\le2,\qquad
p\le F_{M+2}.
\tag{EMW-D1}
\]

**证明。** 对每个 \(p\in S\) 及 \(s\in\{-2,-1,1,2\}\)，\(\rho(p)\mid M\) 且 \(\rho(p)\ge3\)，故 \(\rho(p)\nmid M+s\)。由 (EMW-B1)，\(p\nmid F_{M+s}\)。

EMW 排除中心 \(F_M^2\) 的强力数三元组，故至少一个外侧数不是强力数。由 (EMW-C2)，四个相邻 Fibonacci 数中至少一个有简单素因子 \(p\)。\(M\) 被 60 整除，也排除了秩分别为 3、4、5 的素数 2、3、5。推论 2 给出 \(q_p\ne0\)。

由 \(\rho(p)\mid M+s\) 得 \(\gcd(\rho(p),M)\mid s\)，因此最大公约数不超过 2。最后，\(p\mid F_{M+s}\le F_{M+2}\)。证毕。

### EMW.4 无限周期并集的密度

记 \(\mathcal S=\{-2,-1,1,2\}\)。对 \(60\mid M\)、\(r\ge3\)，定义

\[
E_r(M)=\{k\ge1:\exists s\in\mathcal S,\ r\mid Mk+s\}.
\]

**引理 5，单个秩。** 若 \(g=\gcd(r,M)>2\)，则 \(E_r(M)\) 为空。若 \(g\le2\)，则它是有限个模 \(r/g\) 的剩余类的并，且其自然密度满足

\[
d(E_r(M))\le\frac4r.
\tag{EMW-E1}
\]

**证明。** 线性同余 \(Mk\equiv-s\pmod r\) 有解当且仅当 \(g\mid s\)；有解时，恰对应一个模 \(r/g\) 的剩余类。若 \(g=1\)，至多有四个类，各密度 \(1/r\)。若 \(g=2\)，只有 \(s=\pm2\) 可能，每个类密度 \(2/r\)。若 \(g>2\)，四个同余都无解。证毕。

**引理 6，可求和尾项。** 设 \(D\subseteq\{3,4,\ldots\}\)，且

\[
\sum_{r\in D}\frac1r<\infty.
\]

则 \(E_D(M)=\bigcup_{r\in D}E_r(M)\) 有自然密度，并且

\[
d(E_D(M))\le
4\sum_{\substack{r\in D\\\gcd(r,M)\le2}}\frac1r.
\tag{EMW-E2}
\]

**证明。** 先取任意有限 \(T\subset D\)。有限并 \(E_T(M)\) 是周期集合，故有自然密度；由有限次并集上界及引理 5，满足相应的有限和估计。

不能直接假设自然密度对可数并次可加。为处理尾项，对整数 \(X\ge1\) 使用下面的有限计数：

\[
\#\left(\left(\bigcup_{r\in D\setminus T}E_r(M)\right)\cap[1,X]\right)
\le4(MX+2)\sum_{r\in D\setminus T}\frac1r.
\tag{EMW-E3}
\]

事实上，对固定 \(s\)，映射 \(k\mapsto Mk+s\) 在 \(1\le k\le X\) 上为正且单射，其像包含于 \([1,MX+2]\)。其中被 \(r\) 整除的数至多 \(\lfloor(MX+2)/r\rfloor\) 个。对四个 \(s\) 以及所有尾部 \(r\) 求和即得 (EMW-E3)。在任意固定的 \(X\) 上，\(r>MX+2\) 根本没有贡献。

固定 \(M\) 后，(EMW-E3) 除以 \(X\) 并取上极限，所得误差至多
\(4M\sum_{r\in D\setminus T}1/r\)，它随着有限集合 \(T\) 穷尽 \(D\) 而趋零。因此无限并的上下密度均趋向有限周期并密度的同一极限。自然密度存在；再让有限并中的求和穷尽，得到 (EMW-E2)。证毕。

证明没有使用各个秩、素数或剩余类之间的独立性。选择 \(M\) 与让尾项趋零分属两个步骤：应用引理时，\(M\) 已经固定。

### EMW.5 可求和秩支持的密度放大

定义

\[
\mathcal T=\{n\ge3:F_n^2-1,F_n^2,F_n^2+1\text{ 均为强力数}\}.
\]

对正整数集合 \(A\)，下渐近密度记为

\[
\underline d(A)=\liminf_{X\to\infty}\frac{\#(A\cap[1,X])}{X}.
\]

**定理 7。** 若对某个 \(60\mid M_0\)，

\[
\sum_{r\in\mathcal R_1(M_0)}\frac1r<\infty,
\tag{EMW-F1}
\]

则对每个 \(0<\eta<1\)，存在 \(M_0\mid M\)，使

\[
\underline d\{k\ge1:Mk\in\mathcal T\}\ge1-\eta.
\tag{EMW-F2}
\]

特别地，\(\underline d(\mathcal T)>0\)。

**证明。** 从 (EMW-F1) 选有限 \(T\subset\mathcal R_1(M_0)\)，使

\[
\sum_{r\in\mathcal R_1(M_0)\setminus T}\frac1r<\frac\eta4.
\]

令 \(M=\operatorname{lcm}(M_0,T)\)。若 \(r\in\mathcal R_1(M)\)，则由 \(M_0\mid M\)，有 \(r\in\mathcal R_1(M_0)\)。它不可能属于 \(T\)，因为此时 \(r\mid M\) 且 \(r\ge3\) 会违反 \(\gcd(r,M)\le2\)。所以

\[
\mathcal R_1(M)\subseteq\mathcal R_1(M_0)\setminus T,
\qquad
\sum_{r\in\mathcal R_1(M)}\frac1r<\frac\eta4.
\]

对固定的这个 \(M\)，应用引理 6，得到

\[
d\left(\bigcup_{r\in\mathcal R_1(M)}E_r(M)\right)<\eta.
\]

考虑不属于这个并集的 \(k\)。如果某个 \(F_{Mk+s}\) 不是强力数，则它有简单素因子 \(p\)。由 \(60\mid M\) 与 (EMW-B2)，\(p\) 不会是 2、3、5。由推论 2，\(r=\rho(p)\in\mathcal R_1\)；又因为 \(r\mid Mk+s\)，有 \(\gcd(r,M)\le2\)，从而 \(r\in\mathcal R_1(M)\) 且 \(k\in E_r(M)\)，矛盾。

因此这四个 Fibonacci 数都是强力数，(EMW-C2) 给出 \(Mk\in\mathcal T\)。此类 \(k\) 的下密度至少为 \(1-\eta\)，即 (EMW-F2)。

最后，将等差数列中的计数换回全部指标：

\[
\underline d(\mathcal T)\ge\frac{1-\eta}{M}>0.
\]

证毕。

### EMW.6 条件性秩发散与秩素因子限制

**定理 8。** 若 \(\underline d(\mathcal T)=0\)，则对每个 \(60\mid M\)，

\[
\boxed{\sum_{r\in\mathcal R_1(M)}\frac1r=\infty.}
\tag{EMW-G1}
\]

**证明。** 若有一个这样的级数收敛，定理 7 给出 \(\underline d(\mathcal T)>0\)，矛盾。证毕。

EMW 使 \(\mathcal T\) 为空，故是定理 8 的充分条件。即使允许存在无限多个强力数三元组，只要此 Fibonacci 平方切片的指标集合下密度为零，结论仍然成立。所有整数高度中的零密度并不自动意味着这一指标密度条件。

**推论 9。** 在定理 8 的前提下，对每个 \(60\mid M\)，

\[
\sum_{\substack{p\ne2,5\text{ 素数}\\q_p\ne0\\\gcd(\rho(p),M)\le2}}
\frac1{\rho(p)}=\infty.
\tag{EMW-G2}
\]

**证明。** 为每个 \(r\in\mathcal R_1(M)\) 选择一个支持该秩的素数 \(p_r\)。不同秩必对应不同素数，故左侧至少包含 (EMW-G1) 中的全部项。证毕。

(EMW-G1) 比 (EMW-G2) 更强，因为它没有利用同一秩对应的多个素数来重复增加级数。两式均没有声称 \(\sum1/p\) 发散。

**推论 10，避开任意有限的小素因子。** 给定整数 \(B\ge5\)，令

\[
M_B=\operatorname{lcm}(60,1,2,\ldots,B).
\]

在定理 8 的前提下，存在无限多个非 WSS 素数，其不同秩满足 (EMW-G1)，且每个这样的秩 \(r\) 都有

\[
r>B,\qquad4\nmid r,\qquad
q\mid r,\ q\text{ 为奇素数}\Longrightarrow q>B.
\tag{EMW-G3}
\]

**证明。** 每个 \(q\le B\) 的奇素数都整除 \(M_B\)，而 \(4\mid M_B\)。因此 \(\gcd(r,M_B)\le2\) 排除了这些奇素因子及因子 4。如果 \(3\le r\le B\)，则 \(r\mid M_B\)，同样矛盾。应用定理 8。证毕。

该族允许奇秩及二倍奇秩，未限制秩必须为素数，也未限制素数 \(p\) 在黄金域中惰性或分裂。



## 附录 EMWS：四个线性形式的筛与平方自由的非 WSS 秩

### EMWS.1 线性形式与四维分布

**定义。** 沿用附录 EMW 的 Fibonacci 数列、实际初始商 $q_p$、出现秩 $\rho(p)$、不同非 WSS 秩集合 $\mathcal R_1$ 与强力数三元组指标集合 $\mathcal T$。在本附录中，$\log$ 表示自然对数。令

$$
Q(k)=(60k-1)(60k+1)(30k-1)(30k+1),\qquad k\ge1.
$$

**引理。** 四个线性因子的值两两互素，且均与 $30$ 互素。对每个素数 $t>5$，$Q$ 模 $t$ 恰有四个不同的根，模 $t^2$ 也恰有四个不同的根。

**证明。** 同一斜率的两个值相差二，交叉斜率的整数线性组合为 $1,-1,3,-3$；全部值均为奇数且不被三、五整除，故两两互素。模 $t$ 的根为 $\pm60^{-1},\pm30^{-1}$。同组根重合会使 $t\mid2$；跨组重合会使 $t\mid1$ 或 $t\mid3$，均不可能。每个斜率模 $t^2$ 可逆，故各根唯一提升。模 $t$ 不同保证提升后仍不同。

**引理。** 对平方自由的 $d$ 且 $\gcd(d,30)=1$，有

$$
\#\{1\le k\le X:d\mid Q(k)\}
=\frac{4^{\omega(d)}}dX+R_d(X),\qquad
|R_d(X)|\le4^{\omega(d)}.\tag{EMWS1}
$$

**证明。** 中国剩余定理给出恰好 $4^{\omega(d)}$ 个模 $d$ 的根。每个剩余类在 $[1,X]$ 内的计数与 $X/d$ 相差至多一。对根求和即得。

**定理，四维下界筛的应用。** 令 $a=4/35$。存在 $c_0>0$，使全部充分大的整数 $X$ 满足

$$
\#\{1\le k\le X:t\mid Q(k),\ t\text{ 素数}\Longrightarrow t\ge X^a\}
\ge c_0\frac{X}{(\log X)^4}.\tag{EMWS2}
$$

**证明。** 对素数集合 $t>5$ 使用 C. S. Franze, *Sifting Limits for the $\Lambda^2\Lambda^-$ Sieve*, Theorem 1, arXiv:1012.3809, https://arxiv.org/pdf/1012.3809 。该定理的四维参数为 $8.522$。验证其假设如下：EMWS1 给出 $f(t)=t/4$；Mertens 素数求和式给出

$$
\sum_{5<t<z}\frac{\log t}{f(t)}=4\log z+O(1).
$$

取 $D=X/(\log X)^{40}$。该定理所需的加权余项满足

$$
\sum_{\substack{d<D\ (d,30)=1}}\mu^2(d)7^{\omega(d)}|R_d(X)|
\le\sum_{d<D}\mu^2(d)28^{\omega(d)}
\le\sum_{d<D}\tau_{28}(d)
\ll D(1+\log D)^{27}
\ll\frac{X}{(\log X)^{13}}.\tag{EMWS3}
$$

这里 $\tau_{28}$ 计有序的二十八因子分解；其和的上界可由先固定二十七个因子、再以 $D$ 除以前面因子的乘积控制最后一因子得到。四维所需误差为 $O(X/(\log X)^5)$，故 EMWS3 充分。$Q(k)$ 随正整数 $k$ 严格递增，所以所筛序列恰有 $X$ 项。Franze 定理给出筛界 $z=X^{1/8.522}$；因 $4/35<1/8.522$，减小筛界的单调性得到 EMWS2。素数二、三、五不整除任何 $Q(k)$，无需加入筛集。

### EMWS.2 平方自由与最多八个素因子

**定义。** 对整数 $X\ge2$，令 $y=X^{4/35}$，并定义

$$
\mathcal A_X=\{1\le k\le X:Q(k)\text{ 平方自由，且其全部素因子}\ge y\}.
$$

**定理。** 存在 $c>0$，使全部充分大的 $X$ 满足

$$
|\mathcal A_X|\ge c\frac{X}{(\log X)^4}.\tag{EMWS4}
$$

对每个 $k\in\mathcal A_X$，四个线性因子各自至多包含八个素因子。

**证明。** 在 EMWS2 的集合内，若 $t^2\mid Q(k)$，则 $t\ge y>5$。两两互素性迫使 $t^2$ 整除某一个线性因子，因此 $t\le\sqrt{60X+1}$。每个线性形式模 $t^2$ 只有一个根，故删去的指标数至多

$$
4\sum_{\substack{y\le t\le\sqrt{60X+1}\ t\text{ 素数}}}
\left(\frac{X}{t^2}+1\right)
\ll \frac{X}{y}+\sqrt X
=o\left(\frac{X}{(\log X)^4}\right).\tag{EMWS5}
$$

这证明 EMWS4。若某一个线性因子包含至少九个素因子，则它至少为 $y^9=X^{36/35}$，但它至多为 $60X+1$，对充分大的 $X$ 矛盾。平方自由性使这里的不同素因子数和按重数计的素因子数相同。

### EMWS.3 无条件的关联计数不等式

**定义。** 对正整数 $r$，令 $r_{\rm odd}=r/2^{v_2(r)}$。令 $\mathcal R_8(X)$ 为满足下列条件的不同秩 $r\in\mathcal R_1$ 的集合：

$$
r\le60X+2,\quad r\text{ 平方自由},\quad\gcd(r,60)\le2,\quad
1\le\omega(r_{\rm odd})\le8,
$$

且 $r_{\rm odd}$ 的每个素因子均不小于 $y=X^{4/35}$。记

$$
R_8(X)=|\mathcal R_8(X)|,\qquad
T_X=\#\{k\in\mathcal A_X:60k\in\mathcal T\}.
$$

**定理。** 对全部充分大的 $X$，

$$
\boxed{
T_X+\frac{8X}{y}R_8(X)
\ge |\mathcal A_X|
\ge c\frac{X}{(\log X)^4}.
}\tag{EMWS6}
$$

**证明。** 取 $k\in\mathcal A_X$ 且 $60k\notin\mathcal T$。EMW-C3 给出某个 $s\in\{-2,-1,1,2\}$，使 $F_{60k+s}$ 具有简单素因子 $p$。由于素数二、三、五的出现秩分别为三、四、五，而 $60k+s$ 均不被这些秩整除，所以 $p\notin\{2,3,5\}$。EMW-B3 给出 $q_p\ne0$ 及 $r=\rho(p)\mid60k+s$。

四个指标为 $60k-1,60k+1,2(30k-1),2(30k+1)$。因此 $r$ 平方自由，$\gcd(r,60)\le2$，且其奇部整除一个平方自由的线性因子。秩至少为三，故奇部大于一；EMWS.2 给出其素因子数至多八，且每个素因子均至少为 $y$。故 $r\in\mathcal R_8(X)$，并有 $r\ge y$。

固定一个这样的 $r$，令 $g=\gcd(r,60)$。若 $g=1$，至多四个模 $r$ 的类能满足 $r\mid60k+s$；若 $g=2$，只有两个模 $r/2$ 的类。因而在 $1\le k\le X$ 中，一个秩至多对应

$$
\frac{4X}{r}+4\le\frac{8X}{y}
$$

个指标，其中使用 $r\ge y$ 与 $y\le X$。对每个 $k$ 选择一个见证秩，再按不同秩合并计数，得到 $|\mathcal A_X|-T_X\le(8X/y)R_8(X)$。EMWS4 给出第二个不等式。证明未假设不同秩的剩余类独立或互不重叠。

### EMWS.4 条件性非 WSS 素数族与定量界

**定理。** 若 $T_X=o(X/(\log X)^4)$，则

$$
\boxed{R_8(X)\gg\frac{X^{4/35}}{(\log X)^4}}\tag{EMWS7}
$$

对全部充分大的 $X$ 成立。EMW 是该前提的充分条件。

**证明。** EMWS6 中用 $T_X\le(c/2)X/(\log X)^4$，移项后除以 $8X/y$。EMW 排除所有强力数三元组，故 $T_X=0$。

**推论。** 在同一前提下，存在常数 $c_1>0$，使全部充分大的 $x$ 满足

$$
\#\left\{p\le x:\begin{array}{l}
p\ne2,5\text{ 为素数},\ q_p\ne0,\\
\rho(p)\text{ 平方自由},\ \gcd(\rho(p),60)\le2,\\
1\le\omega(\rho(p)_{\rm odd})\le8
\end{array}\right\}
\ge c_1\frac{(\log x)^{4/35}}{(\log\log x)^4}.\tag{EMWS8}
$$

**证明。** 每个 $r\in\mathcal R_8(X)$ 都有一个实际的非 WSS 素数支持。不同秩的支持素数不同。由于该素数整除 $F_r$，它至多为 $F_{60X+2}\le2^{60X+2}$。取 $X=\lfloor\log x/(120\log2)\rfloor$，则充分大的 $x$ 满足 $2^{60X+2}\le4\sqrt x\le x$。应用 EMWS7 并用 $X\asymp\log x$ 即得。

**推论。** 在同一前提下，可选出无限多个非 WSS 素数，使其出现秩的奇部大于一、平方自由、各至多有八个素因子，并且这些奇部两两互素。

**证明。** 已选有限多个秩后，取 $X$ 足够大，使 $X^{4/35}$ 大于所有先前奇部的素因子。EMWS7 保证新集合非空。其任何秩的奇部全部由更大的素数组成，因此与先前全部奇部互素。递归选择完成证明。

EMWS7 的前提是薄筛集上的相对计数条件。一般集合的下密度为零并不蕴含其计数为 $o(X/(\log X)^4)$，因此附录 EMW 的 $\underline d(\mathcal T)=0$ 不能单独替代本节前提。上述族没有限制出现秩为素数，也没有限制支持素数在黄金域中的分裂类型。


## Appendix FDS. Exact Fibonacci-divisor spectra at square-plus-one values

### FDS.1. A two-factor non-mixing theorem

**Definition.** For a positive integer N, let D_F(N) be the set of distinct positive Fibonacci values dividing N. The value F_1=F_2=1 is included once. Let tau(N) be the number of positive divisors of N.

**Lemma.** For positive K and nonnegative A,B,

$$
K\mid AB\quad\Longleftrightarrow\quad
K\mid\gcd(K,A)\gcd(K,B).\tag{FDS1}
$$

**Proof.** For each prime power p^e exactly dividing K, the right side asserts min(e,v_p(A))+min(e,v_p(B))>=e. This is equivalent to v_p(A)+v_p(B)>=e. If A or B is zero, both divisibility statements hold, so those cases require no valuation at zero.

**Lemma.** For k>=3,

$$
F_{\lfloor k/2\rfloor}^2<F_k.\tag{FDS2}
$$

**Proof.** The case k=3 is 1<2. Otherwise put m=floor(k/2)>=2. Fibonacci addition gives F_(2m)=F_(m-1)F_m+F_mF_(m+1)>F_m^2, using positivity and F_(m+1)>=F_m. Monotonicity and 2m<=k finish the proof.

**Theorem.** For all natural a,b and all k>=3,

$$
\boxed{F_k\mid F_aF_b\quad\Longleftrightarrow\quad k\mid a\ \lor\ k\mid b.}\tag{FDS3}
$$

**Proof.** The reverse implication is Fibonacci divisibility. Suppose the left side holds, but neither index is divisible by k. Put d=gcd(k,a), e=gcd(k,b). These are positive proper divisors of k, hence d,e<=floor(k/2). By FDS1 and strong Fibonacci divisibility, F_k divides F_dF_e. This positive product is at most F_floor(k/2)^2, contradicting FDS2. No coprimality hypothesis is needed.

**Boundary proposition.** FDS3 does not extend to three factors, and its lower bound on k cannot be dropped.

**Proof.** F_6=8=F_3^3, although 6 does not divide 3. Also F_2=1 divides F_1F_1, although 2 does not divide 1.

### FDS.2. The complete A340542 divisor set and count

**Theorem.** For even n>=2 put (u,v)=(n-1,n+1); for odd n>=3 put (u,v)=(n-2,n+2). Then

$$
\boxed{D_F(F_n^2+1)=\{1\}\cup\{F_d:d\ge3,\ d\mid u\text{ or }d\mid v\},}\tag{FDS4}
$$

$$
\boxed{|D_F(F_n^2+1)|=\tau(u)+\tau(v)-1.}\tag{FDS5}
$$

The values at n=0,1 are respectively 1,2.

**Proof.** Cassini and the Fibonacci recurrence give F_(n-1)F_(n+1)=F_n^2+(-1)^n and F_(n-2)F_(n+2)=F_n^2-(-1)^n. Thus F_n^2+1=F_uF_v in the stated cases. Apply FDS3 to every k>=3; the value one is always a divisor. The u,v are positive odd coprime integers, so their positive divisor sets overlap only at one. All their remaining divisors are at least three, where Fibonacci values are distinct. Counting the union proves FDS5. At n=0 the target is one, and at n=1 it is two.

These are explicit formulas for the sequence defined by Michel Lagneau in OEIS A340542, https://oeis.org/A340542 . The definition counts divisor values rather than Fibonacci indices.

### FDS.3. The factor-five rigidity and even Lucas indices

**Theorem.** If u,v are positive odd coprime integers and k>=3, then

$$
\boxed{F_k\mid5F_uF_v\quad\Longleftrightarrow\quad
k=5\ \lor\ k\mid u\ \lor\ k\mid v.}\tag{FDS6}
$$

**Proof.** The reverse implication is immediate. If 5 does not divide F_k, cancel the factor five and apply FDS3. Otherwise the rank-five identity 5|F_k iff 5|k holds. Exclude k=5, so k>=10, and suppose neither u nor v is divisible by k. Set d=gcd(k,u), e=gcd(k,v). They are odd coprime proper divisors of k. Since F_u,F_v are coprime, the elementary prime-exponent formula for a gcd gives

$$
F_k=\gcd(F_k,5F_uF_v)
\le5\gcd(F_k,F_uF_v)=5F_dF_e.\tag{FDS7}
$$

If d=1 or e=1, the remaining proper divisor is at most floor(k/2), so F_dF_e<=F_floor(k/2). Otherwise d,e are distinct odd integers at least three and five. Their product divides k, and 2(d+e-1)<=de<=k. Fibonacci addition yields F_dF_e<=F_(d+e-1)<=F_floor(k/2). Write m=floor(k/2)>=5. Since k>=m+4,

$$
F_k\ge F_{m+4}=3F_m+2F_{m+1}>5F_m,
$$

contradicting FDS7. This proves necessity.

**Theorem.** For every even n>=2,

$$
\boxed{D_F(L_n^2+1)=D_F(F_n^2+1)\cup\{5\},}\tag{FDS8}
$$

$$
\boxed{|D_F(L_n^2+1)|=
\tau(n-1)+\tau(n+1)-1+\mathbf1_{5\nmid(n^2-1)}.}\tag{FDS9}
$$

At n=0 the count is two.

**Proof.** The golden trace-norm identity gives L_n^2-5F_n^2=4 for even n, hence L_n^2+1=5(F_n^2+1). Use FDS6 with u=n-1,v=n+1 and compare with FDS4. The value five is already present exactly when 5 divides u or v, equivalently 5 divides n^2-1. At zero, L_0^2+1=5 has Fibonacci divisor values one and five.

The modulo-five comparison in FDS8 is already recorded in OEIS A340542's comments, together with the comparison to A339669. FDS4-FDS9 give its full divisor-index derivation and explicit counts. The odd-index A339669 formulas proved separately are unchanged.


## Appendix ZBD. Largest-index-prime descent and fully exceptional WSS blocks

### ZBD.1. Preservation of actual initial depth

**Definition.** For primes p other than two and five, let rho(p) be the least positive Fibonacci zero index, h_p=v_p(F_rho(p)), and q_p=F_(p-(5/p))/p modulo p. A prime-index block is the set of prime divisors of F_ell, where ell>=7 is prime. Call the block fully exceptional when every such divisor has q_p=0.

The classical rank and valuation identities, as stated in U.1 and EMW.1, give rho(p)|p-(5/p), q_p=0 iff h_p>=2, and

$$
v_p(F_{dt})=v_p(F_d)+v_p(t)\quad\text{when }p\mid F_d.
$$

They retain the unknown initial depth.

**Theorem.** Let m>1, and suppose its largest prime factor ell is at least seven. For every prime p dividing F_ell,

$$
\boxed{\rho(p)=\ell,\quad p>\ell,\quad p\nmid m,\quad
v_p(F_m)=v_p(F_\ell)=h_p.}\tag{ZBD1}
$$

**Proof.** The prime ell is neither three nor five, so Fibonacci parity and the rank of five exclude p=2,5. Since rho(p)|ell and F_1=1, the rank is ell. The rank bound forces ell|p-1 or ell|p+1. If p<=ell, the first alternative is impossible, and the second forces p=ell-1, an even integer greater than two. Hence p>ell and p does not divide m. Apply the valuation formula to d=ell,t=m/ell. Its last summand vanishes.

**Corollary.** Under ZBD1, if F_m is powerful, then F_ell is powerful and its entire prime-index block is fully exceptional.

**Proof.** Every prime dividing F_ell also divides F_m. Its exponent is unchanged by ZBD1, so it is at least two. The equality with h_p and the standard initial-quotient criterion prove the final assertion.

**Proposition.** Every powerful block F_ell with prime ell>=7 contains a prime p of rank ell and odd initial depth at least three.

**Proof.** The classical Fibonacci square classification gives F_n square only at n=0,1,2,12. In particular F_ell is not square. Its prime factorization has an odd exponent; powerfulness makes that exponent at least three. ZBD1, or the prime-rank argument in its proof, identifies this exponent with h_p. The square theorem is the classical result stated in P. Ribenboim, *FFF: (Favorite Fibonacci Flowers)*, Fibonacci Quarterly 43(1) (2005), section 3.4, https://www.fq.math.ca/Papers1/43-1/paper43-1-1.pdf .

### ZBD.2. Four fully exceptional blocks at a failing window

Retain the definitions Q(k), y=X^(4/35), A_X, T_X and R_8(X) from EMWS. Let

$$
H(X)=\#\{\ell\text{ prime}:y\le\ell\le60X+1,\ F_\ell\text{ powerful}\}.
$$

**Theorem.** For sufficiently large X, each k counted by T_X forces four distinct fully exceptional prime-index blocks, at indices at least y. Each block contains an odd-depth-at-least-three WSS prime; these four witness primes are distinct.

**Proof.** The four adjacent Fibonacci terms are powerful by EMW-C3. Take the largest prime factor of each of 60k-1,60k+1,30k-1,30k+1. The linear forms are pairwise coprime, so their four largest prime factors are distinct. All are at least y>5. For an adjacent even index, its largest prime factor is the largest prime factor of its odd half. Apply ZBD1 to the four adjacent indices and then its corollary. Distinct prime indices give coprime Fibonacci numbers by strong divisibility; alternatively a witness cannot have two different least ranks. The preceding proposition supplies the odd-depth witnesses.

**Theorem.** For sufficiently large X,

$$
\boxed{4T_X\le\frac{8X}{y}H(X),}\tag{ZBD2}
$$

and consequently

$$
\boxed{8R_8(X)+2H(X)\ge\frac yX|\mathcal A_X|
\ge c\frac{X^{4/35}}{(\log X)^4}.}\tag{ZBD3}
$$

**Proof.** Count all four distinct incidences from each failing window. A fixed ell>5 divides one of the four forms at no more than 4X/ell+4<=8X/y values of k. Only the H(X) fully exceptional indices can occur in these incidences. This proves ZBD2. Substitute T_X<=(2X/y)H(X) in EMWS6 and multiply by y/X. The final lower bound is EMWS4, which explicitly uses Franze's established four-dimensional lower-bound sieve.

**Corollary.** If H(X)=o(X^(4/35)/(log X)^4), then R_8(X)>>X^(4/35)/(log X)^4, so the non-WSS prime-family bound EMWS8 follows without assuming EMW.

**Proof.** Absorb 2H(X) in the rightmost lower bound of ZBD3 and apply the same passage from ranks to supporting primes as in EMWS.4.

**Proposition.** Let D_3(X) count distinct prime indices ell in [y,60X+1] for which some p of rank ell has odd h_p>=3. Then H(X)<=D_3(X), and ZBD3 remains true with H(X) replaced by D_3(X).

**Proof.** Each H block supplies such a witness by ZBD.1. This is an inclusion of sets of indices, so no repeated counting of supporting primes is involved.

ZBD3 is a disjunction concerning the actual zero and nonzero initial-quotient supports. It does not assert that either term alone has the displayed order of growth. No estimate on H(X) or D_3(X) is assumed implicitly, and no failing window or WSS witness is asserted to exist by these implications.


## Appendix PBC. Prime-block completeness, depth towers, and exact support partition

### PBC.1. Complete powerful classification on five-smooth indices

**Definition.** A positive integer is powerful when every prime divisor occurs with exponent at least two. In particular one is powerful. Let E={1,2,6,12}. A positive integer is five-smooth when all of its prime divisors belong to {2,3,5}.

**Theorem.** For every positive five-smooth integer m,

$$
\boxed{F_m\text{ powerful}\quad\Longleftrightarrow\quad m\in E.}\tag{PBC1}
$$

**Proof.** Write m=2^a3^b5^c. If c=1, the classical identity v_5(F_m)=v_5(m) gives a simple prime divisor five. If c>=2, use F_25=5^2*3001. The integer 3001 is prime: no integer from two through 54 divides it, while sqrt(3001)<55. Since 3001 does not divide m, the valuation formula U.1 gives v_3001(F_m)=v_3001(F_25)+v_3001(m/25)=1. Thus powerfulness forces c=0.

If b>=2, the identity F_9=2*17 and 17 not dividing m give v_17(F_m)=1. Thus b<=1. If a>=3, the identity F_8=3*7 and seven not dividing m give v_7(F_m)=1. Thus a<=2. The remaining indices are 1,2,3,4,6,12. The values F_3=2 and F_4=3 are not powerful, whereas F_1=F_2=1, F_6=8 and F_12=144 are powerful. This proves both directions. The valuation formula used here is Lengyel's theorem, as stated in Medina and Rowland, *p-regularity of the p-adic valuation of the Fibonacci sequence*, Theorem 1.4, https://arxiv.org/abs/0910.2907 .

### PBC.2. Prime-index completeness and the least counterexample

**Theorem.** The following assertions are equivalent:

$$
\begin{aligned}
\mathrm{(A)}&\quad \forall m\ge1,\quad F_m\text{ powerful}\Longrightarrow m\in E;\\
\mathrm{(B)}&\quad \forall\ell\ge7\text{ prime},\quad F_\ell\text{ is not powerful}.
\end{aligned}\tag{PBC2}
$$

If (A) is false, its least counterexample index is prime and at least seven.

**Proof.** Assertion (A) implies (B), since no prime at least seven belongs to E. Conversely suppose F_m is powerful and m is outside E. By PBC1, m has a prime factor at least seven. Let ell be its largest prime factor. ZBD1 shows that every prime p dividing F_ell has rank ell, exceeds ell, does not divide m, and satisfies v_p(F_m)=v_p(F_ell). Consequently F_ell is powerful. This contradicts (B), proving equivalence. If m is the least counterexample, ell is another counterexample with ell<=m. Minimality forces ell=m.

**Corollary.** Any least counterexample to (A) produces a prime-index block all of whose prime divisors are WSS, and at least one of those divisors has odd initial depth at least three.

**Proof.** The least index ell is prime by PBC2. Each prime divisor p of F_ell has rank ell and initial depth h_p=v_p(F_ell)>=2. Hence q_p=0. The classical Fibonacci square classification excludes F_ell from the squares, so at least one exponent is odd and therefore at least three. Here ell is the index prime; no assertion that q_ell=0 follows.

PBC2 proves an equivalence and the shape of a least counterexample. It does not assert (A) or (B).

### PBC.3. All largest-prime power layers preserve exceptional depth

**Theorem.** Let m>1 have largest prime factor ell>=7, and put a=v_ell(m). For 1<=j<=a define the positive integer

$$
C_j=\frac{F_{\ell^j}}{F_{\ell^{j-1}}}.
$$

Then C_j>1, the C_j are pairwise coprime, C_j is not a square, and every prime p dividing C_j satisfies

$$
\rho(p)=\ell^j,\qquad p>\ell,\qquad
v_p(C_j)=h_p=v_p(F_m).\tag{PBC3}
$$

If F_m is powerful, every C_j is powerful, and there exist a distinct primes p_1,...,p_a such that

$$
\boxed{\rho(p_j)=\ell^j,\qquad h_{p_j}\ge3\text{ is odd},\qquad q_{p_j}=0.}\tag{PBC4}
$$

**Proof.** Fibonacci divisibility and strict growth give integral C_j>1. Every prime p dividing F_(ell^j) is different from two and five, whose ranks are three and five. Its rank divides ell^j and is greater than one, hence equals ell^i for some 1<=i<=j. The rank bound rho(p)|p-(5/p) implies p>rho(p): otherwise p=rho(p)-1 would be even and greater than two. In particular p>ell and p does not divide m. The valuation formula shows that v_p(F_(ell^j))=h_p and that this also equals v_p(F_m).

For j>=2, every old prime divisor of F_(ell^(j-1)) is different from ell. Multiplying its zero index by ell therefore leaves its valuation unchanged. It cannot divide C_j. Thus gcd(C_j,F_(ell^(j-1)))=1, which also proves pairwise coprimality of all layers. Any prime in C_j must have rank ell^j, and the asserted valuation equalities follow. The j=1 case has previous factor F_1=1.

If C_j were square, the distinct positive odd indices ell^(j-1) and ell^j would give Fibonacci numbers in the same square class. The classical square-class theorem excludes this. The theorem is stated by P. Ribenboim in *FFF: (Favorite Fibonacci Flowers)*, Fibonacci Quarterly 43(1) (2005), section 3.4, https://www.fq.math.ca/Papers1/43-1/paper43-1-1.pdf ; its only nonsingleton positive-index classes are {1,2,12} and {3,6}.

Finally, powerful F_m and PBC3 force every exponent in C_j to be at least two. Since C_j is not square, some exponent is odd and at least three. Choose one such prime p_j for each layer. Distinct ranks, or pairwise coprimality, ensure these primes are distinct. No exceptional prime is supplied without the powerfulness antecedent.

### PBC.4. An exact partition dominates the zero-block sieve bound

**Definition.** For real 7<=Y<=L, let H(Y,L) count primes ell in [Y,L] with F_ell powerful. Let G(Y,L) count distinct primes ell in that interval which equal rho(p) for at least one prime p with q_p nonzero. Let Pi(Y,L) count all primes in [Y,L].

**Theorem.** For every such interval,

$$
\boxed{G(Y,L)+H(Y,L)=\operatorname{Pi}(Y,L).}\tag{PBC5}
$$

**Proof.** All prime divisors of F_ell have rank ell when ell>=7 is prime. The integer F_ell is not powerful exactly when one such divisor has exponent one. That exponent is its actual initial depth. This is equivalent to ell being the rank of a non-WSS prime. Thus the two counted classes are disjoint and exhaust the interval's prime indices.

**Proposition, comparison with ZBD3.** Retain the definitions y=X^(4/35), H(X), and R_8(X) of EMWS and ZBD. For sufficiently large X,

$$
\boxed{R_8(X)+H(X)\ge\operatorname{Pi}(y,60X+1).}\tag{PBC6}
$$

If H(X)=o(X/log X), then

$$
G(y,60X+1)\sim\frac{60X}{\log X},\tag{PBC7}
$$

and the number of non-WSS primes p<=x with prime Fibonacci rank is at least a positive constant times log(x)/log(log(x)) for all sufficiently large x.

**Proof.** A prime rank ell in [y,60X+1] is squarefree, is coprime to 60, and has one odd prime factor at least y. Thus each G rank is counted by R_8(X). Apply PBC5 to obtain PBC6. The prime number theorem gives Pi(y,60X+1) asymptotic to 60X/log X; subtract the hypothesized H bound for PBC7.

For each G rank select one supporting non-WSS prime p. Different ranks have different supporting primes, and p divides F_ell<=2^ell. Take X=floor(log(x)/(120 log 2)). Then 2^(60X+1)<=2sqrt(x)<=x for large x. PBC7 therefore supplies the stated lower bound on primes up to x.

Since the right side of PBC6 has order X/log X, this direct partition is stronger than ZBD3's lower bound of order X^(4/35)/(log X)^4. It needs no four-form sieve. It also weakens the sufficient H-smallness assumption used in ZBD.2. No bound on H is proved by this comparison; the separate EMW-based implication in EMWS.4 is unchanged.


## Appendix FDP. Exact parity frequency of the Fibonacci square-plus-one divisor count

**Definition.** Let a(n)=|D_F(F_n^2+1)| for n>=0, as in FDS. For t>=0 let

$$
O(t)=\left\lfloor\frac{\lfloor\sqrt t\rfloor+1}{2}\right\rfloor,
$$

the number of positive odd squares not exceeding t.

**Theorem.** For even n>=2, a(n) is even exactly when n-1 or n+1 is an odd square. For odd n>=3, a(n) is even exactly when n-2 or n+2 is an odd square. Moreover a(0)=1 and a(1)=2.

**Proof.** FDS5 gives a(n)=tau(u)+tau(v)-1, with the indicated u,v. Pairing complementary divisors shows that tau(t) is odd exactly when t is square. Thus a(n) is even exactly when precisely one of u,v is square. These numbers are odd, and their difference is two or four. Distinct positive odd squares differ by at least eight, so they cannot both be square. The two initial values are FDS.2.

**Theorem.** For every integer X>=3,

$$
\boxed{\#\{0\le n\le X:a(n)\text{ even}\}
=O(X-2)+O(X-1)+O(X+1)+O(X+2)-1
=2\sqrt X+O(1).}\tag{FDP1}
$$

**Proof.** The even indices are obtained from positive odd squares s by n=s+1 or n=s-1, excluding s=1 from the second family. They contribute O(X-1)+O(X+1)-1. The odd indices at least three are n=s+2 or n=s-2, excluding s=1 from the second family, contributing O(X-2)+O(X+2)-1. The index n=1 contributes one. These families are disjoint: opposite parities cannot meet, while a same-parity overlap would give odd squares differing by two or four. Summing gives the exact formula. Since O(t)=sqrt(t)/2+O(1), the asymptotic follows with a bounded error.


### FDS.4. Fibonacci-valued divisor sums at Fibonacci centres

**Definition.** For a positive integer N, retain the distinct-value divisor set D_F(N) from FDS.1 and put

$$
\sigma_F(N)=\sum_{d\in D_F(N)}d.
$$

The value one is counted once. Let \(\mathcal F_+=\{F_n:n\ge2\}\).

**Lemma.** If a finite subset S of \(\mathcal F_+\) contains one and has Fibonacci sum, then either S={1}, or for some r>=2,

$$
S=\{1,F_3,F_5,\ldots,F_{2r-1}\},\qquad \sum S=F_{2r}.
\tag{FDS10}
$$

**Proof.** This is the finite-set statement FSP2. A direct proof is as follows. The sum of F_2 through F_(n-2) is F_n-2 for n>=3. Thus an anchored set summing to F_n must contain F_(n-1), since it cannot contain F_n itself along with the additional positive term one. At n=3 such a set is impossible. For n>=4 remove F_(n-1); the remaining set still contains one and sums to F_(n-2). Induction terminates at F_2=1 and forces precisely the stated alternating shape. Conversely its sum telescopes by the recurrence. In the nonsingleton case its largest index is 2r-1.

**Theorem.** For every n>=0,

$$
\boxed{\sigma_F(F_n^2+1)\in\mathcal F_+
\quad\Longleftrightarrow\quad n\in\{0,1,2,4\}.}
\tag{FDS11}
$$

At these indices the sums are respectively 1,3,3,8.

**Proof.** For n>=2 let u,v be the two odd coprime indices from FDS4, with u<v. The divisor set contains F_v and contains no larger Fibonacci value. If its sum is Fibonacci, FDS10 forces all odd indices from 3 through v to occur.

If n is odd, then v=n+2>=5 and u=v-4. The required index v-2 is larger than u and cannot divide v, since it is an odd integer at least three and would have to divide two. This contradicts FDS4.

If n is even and n>=6, then v=n+1>=7 and u=v-2. The required index d=v-4 is an odd integer at least three. It cannot divide u=d+2 or v=d+4, since that would make it divide two or four. Again FDS4 gives a contradiction.

The remaining cases have actual divisor sets {1} at n=0, {1,2} at n=1,2, and {1,2,5} at n=4. Their sums prove sufficiency and the asserted values.

### FDS.5. Fibonacci-valued divisor sums at Lucas centres

**Lemma.** For every odd n>=1,

$$
D_F(L_n^2+1)=
\begin{cases}
\{1\},&3\mid n,\\
\{1,2\},&3\nmid n.
\end{cases}
\tag{FDS12}
$$

**Proof.** Put M=L_n^2+1. The golden identities give F_(3n)=F_n M and M+3=5F_n^2. Any common divisor of F_n and M divides three, while strong divisibility gives gcd(F_n,3)=gcd(F_n,F_4)=F_gcd(n,4)=1. Hence gcd(F_n,M)=1.

If k>=3 and F_k|M, then F_k|F_(3n), so strong divisibility and strict Fibonacci growth give k|3n. Also F_gcd(k,n)=gcd(F_k,F_n)=1. Since n is odd, gcd(k,n) is odd and must be one. Therefore k|3, so k=3 and F_k=2. Finally M+3=5F_n^2 modulo two shows 2|M exactly when F_n is odd, equivalently 3 does not divide n. This rederives the previously established odd-Lucas classification.

**Theorem.** For every n>=0,

$$
\boxed{\sigma_F(L_n^2+1)\in\mathcal F_+
\quad\Longleftrightarrow\quad n\text{ is odd}\ \text{or}\ n\in\{2,4,8\}.}
\tag{FDS13}
$$

For odd n the sum is one when 3|n and three otherwise. At n=2,4,8 the sums are respectively 8,8,55.

**Proof.** FDS12 settles all odd n. At n=0 the actual sum is 1+5=6, not Fibonacci. At n=2,4 the divisor set is {1,2,5}, giving eight. For even n>=6 set v=n+1 and u=v-2. By FDS8 the largest divisor index is v, and the allowed non-unit indices are divisors of u or v together with the additional index five. FDS10 would require the index d=v-4. This odd d>=3 divides neither u nor v, by their differences two and four. Therefore d must equal five, forcing v=9 and n=8. Conversely, at n=8 the divisor set is {1,2,5,13,34}, whose sum is 55=F_10.

FDS11 and FDS13 are consequences of the full divisor spectra and anchored-sum rigidity. They classify the two subsequences obtained by evaluating OEIS A339621 at Fibonacci and Lucas arguments. They do not assert a new solution to its already treated even-index conjecture.

### FDS.6. No Fibonacci divisor-sum at a minus-one Fibonacci square

**Theorem.** For every n>=3,

$$
\boxed{\sigma_F(F_n^2-1)\notin\mathcal F_+.}
\tag{FDS14}
$$

**Proof.** For odd n, Cassini gives F_n^2-1=F_(n-1)F_(n+1); for even n it gives F_n^2-1=F_(n-2)F_(n+2). In both cases the factor indices u<v are positive and even, and v>=4. FDS3 shows that the largest Fibonacci divisor is F_v and that there is no larger Fibonacci divisor. The nonsingleton anchored-set classification FDS10 requires its largest Fibonacci index to be odd if the sum is Fibonacci. This contradicts the evenness of v.

### PBC.5. Collective depths in a fully exceptional prime block

**Theorem.** For every prime ell>=7,

$$
\boxed{\gcd\{h_p:p\mid F_\ell,\ p\text{ prime}\}=1.}\tag{PBC8}
$$

Consequently a powerful F_ell has at least two distinct WSS prime divisors, and at least one has odd initial depth at least three.

**Proof.** All its prime divisors have rank ell, so F_ell=product p^h_p. A common divisor d>=2 of the exponents would make F_ell a perfect d-th power. The established perfect-power theorem of Bugeaud, Mignotte and Siksek excludes this: its only Fibonacci values are 0,1,8,144, occurring at indices 0,1,2,6,12. None occurs at a prime ell>=7. In a powerful block all h_p>=2. A singleton support would then have exponent gcd at least two; all-even exponents would have the same defect. This proves the conclusions. The theorem used is *Classical and modular approaches to exponential Diophantine equations I. Fibonacci and Lucas perfect powers*, Annals of Mathematics 163 (2006), 969-1018, DOI 10.4007/annals.2006.163.969, https://annals.math.princeton.edu/2006/163-3/p05 . It classifies perfect powers, not all powerful Fibonacci integers. Collective gcd one does not assert pairwise coprimality of the depths.

**Corollary.** For every k>=1, if F_(60k)^2-1,F_(60k)^2,F_(60k)^2+1 are powerful, at least eight distinct WSS primes occur in four distinct prime-rank blocks, including at least four primes with odd depth at least three.

**Proof.** EMW-C3 makes all four neighbouring Fibonacci terms powerful. The four positive odd numbers 60k-1,60k+1,30k-1,30k+1 are pairwise coprime and coprime to 30. Their largest prime factors are therefore four distinct primes at least seven. Apply ZBD1 to each neighbouring index, using the same largest prime for an even index and its odd half. This produces four powerful prime-index blocks. Their Fibonacci values are pairwise coprime. Apply PBC8 in each block. No sieve condition on k is needed, and the antecedent is not asserted to hold.

**Corollary.** Let N_0(x) and N_Z(x) count non-WSS and WSS primes p<=x, respectively, whose actual Fibonacci ranks are prime and at least seven. For x>=128,

$$
\boxed{N_0(x)+\tfrac12N_Z(x)\ge\pi(\lfloor\log_2x\rfloor)-3.}\tag{PBC9}
$$

**Proof.** Set Y=floor(log_2 x). Every prime ell in [7,Y] has either a simple prime divisor of F_ell or a powerful block. In the first case choose one non-WSS prime; in the second choose two WSS primes by PBC8. Distinct indices give disjoint prime supports. All chosen primes are at most F_Y<=2^Y<=x. Each index contributes at least one to the weighted left side. This strengthens the counting consequence of PBC5 but does not select the zero or nonzero alternative. No bound on the exceptional-block count follows from this inequality alone.


## Appendix LFO. Powerful residue classes and finite-prime observation at prime ranks

### LFO.1. Exact residue compatibility

**Definition.** For M>=1, let C(M) be the set of residue classes modulo M containing a positive powerful integer. The residue of an integer a is denoted [a]_M. A positive integer is powerful exactly when it has a representation x^2 y^3 with positive integers x,y: in its prime factorization, an even exponent is assigned wholly to the square, and an odd exponent at least three is assigned three to the cube and the remaining even exponent to the square.

**Theorem.** For every integer a and M>=1,

$$
\boxed{[a]_M\in C(M)\quad\Longleftrightarrow\quad
\forall p\text{ prime},\ p^2\mid M\Longrightarrow
(p\nmid a\ \lor\ p^2\mid a).}\tag{LFO1}
$$

In particular every unit residue class belongs to C(M), and every residue class does so when M is squarefree.

**Proof.** If p^2|M and p divides a exactly once, every integer in the residue class has exponent exactly one at p. This proves necessity.

For sufficiency write e_p=v_p(M) for p|M and let t_p be the largest t<=e_p for which p^t|a. Thus t_p=e_p if a is zero modulo p^e_p; no valuation of zero is taken. Choose nu_p=0 when t_p=0, nu_p=t_p when 0<t_p<e_p, and nu_p=max(e_p,2) when t_p=e_p. The hypothesis ensures that every positive nu_p is at least two. Hence D=product_{p|M}p^nu_p is powerful.

There is a unit u modulo M with Du congruent to a. At t_p<e_p, the congruence reduces to

$$
u\equiv(a/p^{t_p})(D/p^{t_p})^{-1}\pmod{p^{e_p-t_p}}.
$$

Both factors on the right are units at p; choose any unit lift modulo p^e_p. At t_p=e_p the original congruence is automatic, and choose u=1 modulo p^e_p. The Chinese remainder theorem combines these unit classes. Choose positive x,y representing u^(-1),u modulo M. Then N=Dx^2y^3 is powerful and N congruent to Du=a modulo M. When M=1 take D=x=y=1.

### LFO.2. Compatibility survives non-perfect-power and finite-support constraints

**Theorem.** Suppose [a]_M belongs to C(M). Given any integer B>=1, the class contains infinitely many positive powerful integers N which are not perfect powers and have no prime divisor p<=B with p not dividing M. At two distinct auxiliary primes r,s>B not dividing M, their exponents may be fixed to be exactly two and three, respectively.

**Proof.** Use the D and unit u from LFO1. Infinitude of primes supplies distinct r,s>B outside the prime support of M. Let R be the product of primes p<=B with p not dividing M. The moduli M,R,r^2,s^2 are pairwise coprime. The Chinese remainder theorem gives positive x,y with

$$
\begin{array}{c|cccc}
 &\bmod M&\bmod R&\bmod r^2&\bmod s^2\\
x&u^{-1}&1&r&1\\
y&u&1&1&s
\end{array}
$$

and N=Dx^2y^3 is powerful, congruent to a modulo M, and divisible by none of the stated small primes. Since r,s do not divide D, its exponents at r,s are exactly two and three. A perfect-power exponent would divide both, which is impossible. Replace x by x+jL for j>=0, where L=MRr^2s^2, to obtain infinitely many distinct examples with all conditions unchanged. Congruences modulo one are vacuous. The elementary construction does not use a theorem on primes in arithmetic progressions.

**Corollary.** Imposing the additional requirement that a powerful integer is not a perfect power does not change its image modulo any positive M.

**Proof.** The preceding theorem gives the reverse inclusion; the other inclusion is immediate. In the constructed examples the collective gcd of the prime exponents is one because exponents two and three occur.

**Proposition.** For fixed compatible a,M,B, there are constants C,T_0>0 such that every real T>=T_0 has one of these examples in [T,T+C sqrt(T)].

**Proof.** Keep D,y,L and the residue of x from the preceding proof. Put A=Dy^3. Select the first positive x_j=x+jL with x_j>=sqrt(T/A). For sufficiently large T this choice has x_j<sqrt(T/A)+L. Thus

$$
T\le Ax_j^2<T+2L\sqrt{AT}+AL^2.
$$

For T>=1 the last two terms are bounded by C sqrt(T), with C=2L sqrt(A)+AL^2. All congruence and exponent conditions remain unchanged. The constants depend on the fixed residue data; no estimate uniform in a growing modulus is asserted.

Squarefull numbers in arithmetic progressions have an extensive classical literature, including M. Munsch, I. E. Shparlinski and K. H. Yau, *Smooth squarefree and squarefull integers in arithmetic progressions*, Mathematika 66 (2020), 56-70, DOI 10.1112/mtk.12012, https://arxiv.org/abs/1810.02573 . The claims here use the explicit elementary construction rather than an unproved distribution assumption.

### LFO.3. The exact proportion of locally admissible residues

**Theorem.** For every M>=1,

$$
\boxed{\frac{|C(M)|}{M}
=\prod_{p^2\mid M}\left(1-\frac1p+\frac1{p^2}\right).}\tag{LFO2}
$$

**Proof.** At a prime power p^e with e=1 all classes are admissible. For e>=2, precisely p^(e-1)-p^(e-2) classes have valuation one. Subtract them from p^e, divide by p^e and multiply over the independent prime-power factors using the Chinese remainder theorem. Empty products equal one, including M=1.

### LFO.4. What fixed value-prime probes can see in a prime-index block

**Theorem.** Let ell>=7 be prime. Every prime divisor p of F_ell satisfies

$$
\rho(p)=\ell,\quad p\equiv1\pmod4,\quad
\begin{cases}
p\ge4\ell+1,&(5/p)=1,\\
p\ge2\ell-1,&(5/p)=-1.
\end{cases}\tag{LFO3}
$$

These are classical rank and golden-norm consequences.

**Proof.** The ranks of two and five exclude them from F_ell. The rank of any other prime divisor divides ell and is greater than one, so it equals ell. At this odd index the norm identity gives L_ell^2-5F_ell^2=-4. Modulo p, L_ell/2 is a square root of minus one, so p=1 modulo four. The rank bound gives ell|p-(5/p). For a split prime, both ell and four divide p-1, giving 4ell|p-1. For an inert prime, the positive integer (p+1)/ell is even, giving p>=2ell-1. More precisely that integer is two modulo four.

**Corollary.** Let P(M) be the largest prime factor of M, with P(1)=1. If 2ell-1>P(M), then gcd(F_ell,M)=1. Thus [F_ell]_M belongs to C(M) and contains the non-perfect powerful examples of LFO.2. Increasing the exponents on the same finite prime support does not alter this assertion.

**Proof.** A common prime divisor would contradict LFO3. Apply LFO1 and LFO.2 to the resulting unit class.

**Definition.** A residue-only rejection rule at modulus M is called sound for nonpowerfulness if it rejects a residue class only when every positive integer in that class is nonpowerful.

**Theorem.** Every such sound rule accepts F_ell whenever ell is prime, ell>=7, and 2ell-1>P(M). A finite collection of residue-only rules can be combined at their least-common-multiple modulus and has the same eventual acceptance property. In particular, on prime indices ell in [Y,2Y] with Y>=7, probes supported only on value primes below 2Y-1 reject no index.

**Proof.** The corollary provides a positive powerful integer in the same class. Rejecting it would violate soundness. Equality modulo the least common multiple preserves all the individual residues. Apply the same corollary once to that modulus.

This theorem concerns the specified residue-only information. It does not assert that every arithmetic argument involving congruences is powerless, nor does it apply to moduli whose prime support is allowed to grow past the stated cutoff. Replacing F_ell by a compatible powerful integer preserves polynomial congruences in the numerical Fibonacci/Lucas coordinates at those fixed moduli. It does not preserve the exact integer norm equation, the actual recurrence value, or exact ranks of the replacement integer's prime factors.

### LFO.5. The exact finite set of exclusions

**Theorem.** For every positive M and prime ell>=7,

$$
\boxed{[F_\ell]_M\notin C(M)
\quad\Longleftrightarrow\quad
\exists p\text{ prime}:\ p^2\mid M,\ \rho(p)=\ell,\ q_p\ne0.}\tag{LFO4}
$$

Consequently the prime indices excluded by M are exactly the distinct prime ranks at least seven of the non-WSS primes whose squares divide M. This is a finite set, contained in [7,(P(M)+1)/2].

**Proof.** By LFO1, exclusion is equivalent to p dividing F_ell exactly once for some p^2|M. Such p is different from two and five and has rank ell by LFO3; its exponent is its initial depth. EMW-B3 makes exponent one equivalent to q_p nonzero. These steps reverse to prove both implications. Finally p<=P(M) and p>=2ell-1 give the bound on ell.

**Proposition.** The integers F_7=13 and N=29^2*37^3=42599173 have the same residue four modulo nine. The latter is powerful, is not a perfect power, and its two prime divisors exceed thirteen and are both one modulo four.

**Proof.** The displayed factorizations and residues are exact integer calculations, and the exponents two and three have gcd one. The primes twenty-nine and thirty-seven do not divide F_7 and are not asserted to have rank seven. This example records the distinction between residue compatibility and membership in an actual prime-index Fibonacci block.

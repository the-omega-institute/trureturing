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

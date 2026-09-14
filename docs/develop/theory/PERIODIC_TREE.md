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
残核统计律;混居城真偶精判;$G$ 全群;$j$-密度;$d$-平方退化员;Markov 树层際字典(W-树3);Herglotz 虚姊妹;scl-刺客。

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

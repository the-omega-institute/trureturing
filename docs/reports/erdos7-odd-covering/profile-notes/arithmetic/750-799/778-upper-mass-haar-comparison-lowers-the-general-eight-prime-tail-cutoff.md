# Upper-mass Haar comparison lowers the general eight-prime tail cutoff

Let a finite family have pairwise-distinct odd numerical moduli greater than one, with one fixed residue per modulus. If at most eight prime divisors of its full original LCM are at most8000, the family is noncovering. There is no bound on the finite number of larger prime divisors, on original prime-power heights, or on the number of coordinates occurring in one modulus. In particular, all of3,5,7,11 may occur. No phase dictionary is prescribed.

The proof gives final distorted survivor mass greater than1/20000000. It improves the general eight-prime cutoff10000 in [734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md), using the same attributed eight-prime uncovered-density premise and the same quartic continuation. The new step is to retain the guaranteed small source mass when bounding its complete fourth query moment. It reuses the full convex-query comparison and upper-quantile principles of [771](771-stop-loss-profiles-preserve-the-ordinary-source-through-thirteen-primes.md) and [773](773-repeated-upper-mass-comparison-lowers-the-fourteen-prime-tail-cutoff.md). This is ordinary mathematics and exact rational arithmetic, not new Lean verification or a resolution of unrestricted Erdős #7.

## 1. One actual eight-prime source at a fixed mass

Collect all original support primes at most $B=8000$ and pad to eight with unused odd primes at most $B$. No original class is added on a padded coordinate. Let the ordered head primes be $r_1<\cdots<r_8$, and take their finite heights large enough to resolve the ENTIRE original family, including head exponents in classes also touching future tail primes. Artificial coordinates may have height one.

The source premise is Schroeder's edition1.0.1, corollary `cor:uncovered-density`, recorded in the [existing source entry](../../../../../../Library/Arith/schroeder2026nine.md) and already used in Chapter33§6: every such family on at most eight odd primes has uncovered natural density at least

$$
m_0=\frac1{1002375}.
$$

This is an attributed theorem. The existing finite source-geometry verification does not constitute a local kernel replay of its entire arbitrary-height proof; the present arithmetic consumer does not supply that replay.

Apply this premise to the actual head-only subfamily. Write $H_R$ for normalized Haar on the complete finite head carrier and $U$ for its actual survivor set. Uniform lifting to the chosen full heights preserves the density, so $v=H_R(U)\ge m_0$. Define ONE measure

$$
\mu=\frac{m_0}{v}\,H_R|_U.
$$

It has exact mass $m_0$, avoids every head-only original, and satisfies $\mu\le H_R$. Its scalar normalization depends on the actual family, but not on any later query or cost function. This is a mathematical existence construction; it gives no internal observer free access to the unknown value of $v$.

## 2. Complete Haar layouts have one convex comparison

For the finite head period $Q$, a complete layout $\Phi$ chooses one residue at every numerical divisor $d\mid Q$, including $d=1$. Put

$$
L_\Phi(x)=\sum_{d\mid Q}\mathbf1_{x\in\Phi_d}.
$$

The layout phases need not be compatible with each other. They are query parameters and do not modify the original forbidden family.

For a prime $p$, let $J_p$ have the capped comparison law of771 at cap one:

$$
\Pr(J_p=j)=\frac{p-1}{p^{j+1}},\qquad j\ge0.
$$

Thus $\Pr(J_p\ge e)=p^{-e}$ for $e\ge1$. For independent auxiliary runs, put

$$
M_R=\prod_{i=1}^8(1+J_{r_i}).
$$

The conditional ordered-increment argument of771, specialized to normalized Haar kernels of cap one, gives for every nonnegative increasing convex $f$,

$$
\int f(L_\Phi)\,dH_R\le\mathbb E f(M_R).
\tag{1}
$$

For clarity, the backward coordinate step still encounters DIFFERENT old layouts at different current depths. At an auxiliary run $j$, their load sum is bounded by Jensen:

$$
f\!\left(\sum_{e=0}^jL_e\right)
\le\frac1{j+1}\sum_{e=0}^jf((j+1)L_e).
$$

Apply the preceding-coordinate comparison separately to every right-hand integrand and then average the same auxiliary run. Starting at the unit layout proves(1). Finite exponent inventories are completed only in the nonnegative comparison; the actual family and carrier stay finite. Geometric auxiliary moments justify the limit.

Every ordered eight-prime tuple dominates

$$
P=(3,5,7,11,13,17,19,23).
$$

Its auxiliary tails $r_i^{-e}$ are at most $P_i^{-e}$. Couple the independent runs coordinatewise, or use first-order stochastic domination, to replace $M_R$ in(1) by $M=\prod_i(1+J_{P_i})$. Write $\Pi$ for this fixed comparison probability law. Together with $\mu\le H_R$, this comparison serves EVERY complete query on the SAME actual source.

## 3. Retain the source mass in the fourth-moment bound

For any threshold $c\ge0$ and any complete layout,

$$
\begin{aligned}
\int L_\Phi^4\,d\mu
&\le c^4m_0+\int(L_\Phi^4-c^4)_+\,d\mu\\
&\le c^4m_0+\int(L_\Phi^4-c^4)_+\,dH_R\\
&\le c^4m_0+\mathbb E_\Pi(M^4-c^4)_+.
\end{aligned}
\tag{2}
$$

The last cost is nonnegative, increasing and convex on nonnegative loads, so(1) applies. No physical point is selected by its query load. Both the actual source and $c$ are fixed uniformly over all layouts.

Choose $c=288$. Exact computation brackets the mass by

$$
\Pi(M>288)\le m_0\le\Pi(M\ge288).
$$

Consequently the right side of(2) is the fourth moment of the largest $m_0$ units of comparison mass, splitting the atom at288. This is the existing upper-quantile operation from773. It does not assert that the actual survivors are the largest-load points or that actual deletions removed the smallest loads.

The complete comparison fourth moment is the same Haar initialization used in734:

$$
\mathbb EM^4
=\prod_{p\in P}\frac{p^4+11p^3+11p^2+p}{(p-1)^4}
=\frac{16379878645983125}{190768545792}.
$$

Writing $\pi_n=\Pi(M=n)$, the exact value in(2) is computed without discarding the infinite auxiliary tail:

$$
K_* =288^4m_0+\mathbb EM^4-288^4
 +\sum_{n<288}(288^4-n^4)\pi_n.
\tag{3}
$$

Finite multiplicative convolution gives every needed $\pi_n$ exactly. The result is

$$
K_*=44066.370201978796\ldots<44100.
$$

Therefore the SAME head law has exact mass $m_0$ and satisfies

$$
\int L_\Phi^4\,d\mu<44100
\qquad\text{for every complete layout }\Phi.
\tag{4}
$$

Hölder on this same finite positive measure then bounds the integral of any product of four complete query loads by44100, as required by734(HM3). This does not select four different source measures.

The number288 bounds stored comparison loads, not original exponents. The complete fourth moment includes the entire infinite auxiliary tail. No estimate is obtained by multiplying independent actual head marginals. The value44100 is a conservative upper bound, not an optimality claim.

## 4. The existing quartic tail from the smaller common-law bound

Start734's arbitrary-head quartic continuation from(4), keeping its eight-prime parameters unchanged:

$$
k=4,\qquad\delta=\frac25,\qquad r=25.
$$

At a new prime $q$, retain every full earlier numerical cofactor and original residue, including the unit cofactor for pure powers. Assign each tail-touching original to its last exposed tail coordinate. Distinct original moduli give at most one forbidden class at each complete exponent-vector label. All finite original heights are retained.

For an old point $x$, let $\beta(x)$ be the actual fraction of its new full Haar fibre removed by the current originals. Use734's live subprobability kernel

$$
R_x(dy)=\frac{\mathbf1_{y\notin B_x}\,H_q(dy)}
 {1-\min(\beta(x),\delta)}.
$$

Its mass is at most one and its row loss is $(\beta-\delta)_+/(1-\delta)$. Even a completely forbidden fibre is defined and has zero new mass. Every positive-depth prefix has mass at most $q^{-e}/(1-\delta)$, while the zero-depth mass is at most one. Thus the actual supported law remains common to all subsequent queries; its old marginal is allowed to decrease.

The inherited fourth-moment estimates are

$$
D_q\le\frac{5625}{2048}\frac{K}{(q-1)^4},
\qquad
K_{\rm new}\le K\left(1+\frac53 A_4(q)\right),
$$

where, with $t=1/(q-1)$,

$$
A_4(q)=15t+50t^2+60t^3+24t^4.
$$

The same coefficientwise inequality as734 gives

$$
1+\frac53 A_4(q)
=1+25t+\frac{250}{3}t^2+100t^3+40t^4
\le(1+t)^{25}.
$$

Complete original exponent sums and all mixed query products are covered by734(HM9)–(HM12); no first-digit or support-only replacement is made. Actual mass losses telescope on the successive live submeasures. Unlike a marginal-preserving formulation that defers deletion, this construction deletes immediately and does not assert unchanged old marginals.

Using the same Rosser–Schoenfeld prime-product premise as734, the total loss for every finite set of tail primes greater than $B$ is at most $K\tau(B,\ell)$, with

$$
\tau(B,\ell)
=\frac{5625}{6144}
\left(\frac{2\ell^2+1}{2\ell^2-1}\right)^{25}
\frac{B}{(B-1)^4}
\sum_{j=0}^{25}\frac{25!}{(25-j)!(3\ell)^j}.
\tag{5}
$$

The inherited domain is $B\ge286$, $\ell\ge4$, $3^\ell\le B$, and $4\ell\ge25$. This is734(HM15) with unchanged moment order, clipping parameter and growth exponent. The sum bounds all larger primes, hence every finite actual tail without a cardinality restriction.

Set $(B,\ell)=(8000,8)$, which satisfies all domain conditions, and use $K=44100$ in(4). The exact rational result gives

$$
m_0-44100\,\tau(8000,8)
=0.00000005184658784864074\ldots
>\frac1{20000000}>0.
$$

The inequality is checked on fractions, not the displayed decimal. Positive mass supplies a survivor in the complete padded CRT carrier. Projecting out the dummy coordinates gives an integer avoiding the original family. The lower mass belongs to the constructed distorted law; it is not asserted to be the final Haar density.

## 5. Verification and the remaining scope

The standalone standard-library [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/eight_head_haar_quantile_tail.py) reconstructs all288 low comparison atoms, the complete geometric fourth moment, the cutoff bracket, the split-atom and threshold-fourth expressions, the polynomial coefficient inequalities, and the rational analytic allowance. The [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/eight_head_haar_quantile_tail.json) retains exact comparison moments, cutoff data and the full rational margin. It records the density and analytic source theorems as premises rather than claiming to rerun them. An unresolved finite cutoff is rejected; no remaining tail is silently dropped.

An independent calculation checks the threshold-fourth expression using divisor convolution and directly accumulated low moments. It agrees on the cutoff, complete retained moment and tail margin. Optimized Python preserves the guards against invalid mass, an unresolved cutoff and an out-of-domain analytic parameter. These checks establish the displayed arithmetic, not a new kernel-verified source theorem.

This class includes all-four-small-prime heads excluded by773's fourteen-prime result. It permits at most eight small primes, whereas773 admits fourteen under its additional missing-prime condition; neither stated restriction subsumes the other. The eight-prime row of734 at cutoff10000 is contained in the new cutoff8000 class; its separate seven-prime result remains available. Arbitrary families with nine or more support primes at most8000 are not settled here. Improving a sufficient cutoff does not establish its optimality or solve unrestricted Erdős #7.

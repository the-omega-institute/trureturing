# The original capped source lowers the general eight-prime tail cutoff to6561

Let a finite family have pairwise-distinct odd numerical moduli greater than one, with one fixed original residue per modulus. If at most eight prime divisors of its entire original LCM are at most6561, the family is noncovering. The number of larger support primes, all original finite prime-power heights and mixed support sizes remain unrestricted. There is no missing-small-prime or prescribed phase-dictionary condition.

The construction gives final distorted survivor mass greater than1/150000. It strengthens the cutoff8000 of [778](778-upper-mass-haar-comparison-lowers-the-general-eight-prime-tail-cutoff.md). The additional input is the conditional-kernel structure of the SAME Schroeder source whose existence supplied the earlier density bound. Retaining its two actual pure-anchor restrictions and six conditional caps keeps the larger guaranteed source mass together with its complete capped query profile before the existing upper-mass operation. The continuation is still the quartic argument of [734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md).

This is ordinary mathematics with a standalone exact arithmetic consumer. It does not provide a new Lean verification, independently replay the attributed source theorem, or settle unrestricted Erdős #7.

## 1. Preserve the actual source construction

Use [Schroeder edition1.0.1](../../../../../../Library/Arith/schroeder2026nine.md), on the reference support

$$
P=(3,5,7,11,13,17,19,23).
$$

Its countable-completion lemma inserts every pure prime power and selected mixed classes. Selected proper-divisor classes are disjoint. In particular, if $P_p$ is the completed pure union at $p$, then

$$
H_p(P_p)=\sum_{e\ge1}p^{-e}=\frac1{p-1}.
$$

Completion can move selected original residues when their old classes are already contained in smaller selected classes. Its guarantee is containment of the ORIGINAL covered set in the completed covered set. We use exactly that guarantee: a measure avoiding the completed family avoids the original family. We do not assert that completion preserves every original residue.

The initial actual anchor is $H|_A$, with

$$
A\subseteq P_3^c\times P_5^c.
$$

The two restricted Haar factors on the right have exact masses1/2 and3/4. Later coordinates use fixed normalized full-coordinate conditional kernels, depending on the original family and earlier actual coordinates, with caps

$$
\begin{array}{c|rrrrrr}
p&7&11&13&17&19&23\\\hline
C_p&3/2&5/3&3/2&2&9/5&11/5.
\end{array}
$$

These are the caps in the paper's conditional-kernel section, not caps inferred from the final product-density bound. Its domination and first-hit lemma states that the same kernels are defined also on deleted histories. Enlarging an initial measure while keeping those kernels and deletions fixed is a positive linear operation.

At7, the paper also enlarges forbidden digits within each actual fibre. This padding is charged in its mass proof and is part of the SAME source construction. The extra digits can depend on the earlier cell and need not be globally fixed congruences. The kernel remains normalized and capped by3/2. We retain this source rather than replacing its padding by an uncharged model.

The paper's final-mass inequality and uncovered-density proof establish, for every finite original family on this reference support, a final source $\nu$ with

$$
v=\nu(X)\ge m=\frac1{33750}.
\tag{1}
$$

There is no covering hypothesis in this source conclusion: the paper uses that hypothesis only for the final contradiction in its rank proof. Let

$$
\mu=\frac{m}{v}\nu.
\tag{2}
$$

This is ONE source of exact mass $m$, chosen from the original family before any query. The scalar is at most one. Its exact value is used as a mathematical existence construction, not as an observer's free measurement of $v$.

For the upper comparison, first omit all later deletions and enlarge only the initial anchor to $P_3^c\times P_5^c$, keeping the same conditional kernels, including their definitions on dead histories. Call the resulting pre-deletion law $\Lambda$. Then $\mu\le\nu\le\Lambda$. This provides the simultaneous source/query relation that is lost if one retains only the final Haar-density lower bound.

## 2. One full convex profile for every complete query

At any chosen finite head heights let $Q$ be the full reference period. A complete query layout $\Phi$ assigns a prefix cylinder to every numerical divisor $d\mid Q$, including $d=1$. Define

$$
L_\Phi(x)=\sum_{d\mid Q}\mathbf1_{x\in\Phi_d}.
$$

Query residues are arbitrary and need not be mutually compatible. They are tests on the already chosen source; they do not alter the original forbidden family or the source construction.

For the anchors use the paper's subprobability comparison factors

$$
\begin{aligned}
\pi_{p,A}(0)&=A-1/p,\\
\pi_{p,A}(j)&=(p-1)/p^{j+1},\qquad j\ge1,
\end{aligned}
$$

at $(p,A)=(3,1/2),(5,3/4)$. For the six later primes use

$$
\begin{aligned}
\pi_{p,C}(0)&=1-C/p,\\
\pi_{p,C}(j)&=C(p-1)/p^{j+1},\qquad j\ge1.
\end{aligned}
$$

Let $\Pi$ be their product submeasure, carrying the comparison load

$$
M=\prod_{p\in P}(1+J_p).
$$

Its total mass is $3/8$. The same-source proof of [771](771-stop-loss-profiles-preserve-the-ordinary-source-through-thirteen-primes.md), now applied to the actual caps above, gives for every complete $\Phi$ and nonnegative increasing convex $f$,

$$
\int f(L_\Phi)\,d\mu
\le \int f(L_\Phi)\,d\Lambda
\le \int f(M)\,d\Pi.
\tag{3}
$$

Here is the required dependence check. Apply ordered increments conditionally at the last actual coordinate and continue backwards. Each depth-$e$ cylinder has conditional mass at most $C_p/p^e$. Different complete numerical labels at the same depth remain separate. At a fixed auxiliary run $j$, different current exponents can induce DIFFERENT earlier layouts $L_0,\ldots,L_j$; they are handled by

$$
f\!\left(\sum_{e=0}^jL_e\right)
\le\frac1{j+1}\sum_{e=0}^j f((j+1)L_e).
$$

The preceding-coordinate comparison applies to each integrand. It does not identify their actual phases. At the first two coordinates, the restricted Haar factors are independent factors of the enlarged initial anchor, have masses1/2 and3/4, and retain depth-$e$ caps $p^{-e}$. The paper's subprobability lemma therefore gives exactly the two anchor laws above. Finite exponent inventories may be enlarged to the infinite auxiliary inventory by nonnegative truncation; the geometric moments used below remain finite.

The auxiliary factorization does not assert independence of the actual later coordinates. The full conditional bounds, normalization on every history and initial product enlargement are its justification. The same $\mu$ works for all query phases and all such costs.

The paper's normalizations permute children in each individual prime-adic coordinate tree. Each permutation is Haar preserving and sends every depth-$e$ prefix cylinder to one of the same depth, including arbitrary deeper digits. Undoing these coordinatewise permutations therefore permutes the whole admissible complete-query family. Formula(3) holds in the original coordinate system as well; it does not require an arithmetic affine map.

## 3. Transfer the entire source/query statement to larger primes

Let $r_1<\cdots<r_8$ be any ordered odd primes, so $r_i\ge P_i$. Fix finite heights resolving the ENTIRE original family, including head exponents in tail-touching originals. For a random prefix-preserving product injection

$$
F:\prod_i\mathbb Z/P_i^{A_i}\mathbb Z
\longrightarrow\prod_i\mathbb Z/r_i^{A_i}\mathbb Z,
$$

pull back the fixed original head-only forbidden family. Every inverse image is empty or a prefix cylinder of the same complete exponent vector. Discard empty originals. Distinct nonzero numerical labels stay distinct.

For each injection choose the source(2) for this pulled-back family and project its prime-adic realization to the chosen finite heights. It has the SAME exact mass $m$, avoids the pulled-back originals and satisfies(3) for all queries. This choice may depend on $F$ and the original family, but not on a later query.

Push it forward and average these measures over the finite injection family. The result is one target source $\mu_R$ of exact mass $m$, avoiding the actual target originals. A fixed target complete layout pulls back to at most one cylinder per complete exponent vector; fill empty query entries with arbitrary source cylinders to bound its nonnegative load. Applying(3) to each injection and then averaging proves(3) for $\mu_R$ with the same reference $\Pi$. Thus the transported statement preserves every later query simultaneously, not just an uncovered-density scalar.

If source construction uses more prime-adic digits than the chosen finite period, finite projection is taken only AFTER construction. Avoidance of the original finite family and all queries at the chosen heights are preserved. Countable pure completion imposes no finite-height restriction on the original family.

## 4. The upper-mass fourth moment and quartic tail

The exact complete fourth moment of a factor of total mass $A$ and positive-depth cap coefficient $C$ is

$$
A+C\left[\frac{p^4+11p^3+11p^2+p}{(p-1)^4}-1\right].
$$

For the anchors $(A,C)=(1/2,1),(3/4,1)$; the other six have $A=1$ and the displayed caps. Therefore

$$
\int M^4\,d\Pi
=\frac{1284839019649471672399}{1788455116800000}
=718407.1926548398\ldots.
$$

The source has exact mass $m$ from(1). The existing upper-mass principle of [773](773-repeated-upper-mass-comparison-lowers-the-fourteen-prime-tail-cutoff.md) gives, uniformly over complete layouts,

$$
\int L_\Phi^4\,d\mu_R
\le c^4m+\int(M^4-c^4)_+\,d\Pi.
\tag{4}
$$

One can also obtain(4) directly from(3), since $z\mapsto(z^4-c^4)_+$ is nonnegative, increasing and convex on nonnegative loads. This operation trims an outer comparison measure; it does not choose physical survivors according to a query.

Exact convolution of the factors gives

$$
\Pi(M>192)\le m\le\Pi(M\ge192).
$$

Writing $\pi_n=\Pi(M=n)$, the full value of(4) at $c=192$ is

$$
K_* =\int M^4\,d\Pi
       +192^4(m-3/8)
       +\sum_{n<192}(192^4-n^4)\pi_n
     =590422.0422477094\ldots <590500.
\tag{5}
$$

The complete infinite fourth moment is retained;192 bounds stored comparison loads, not original prime-power heights. Hölder applied to this same physical measure bounds every product of four complete query loads by590500, giving the full mixed-query premise required by734.

Now collect every original support prime at most $B=6561$, pad the head to eight with unused odd primes at most $B$, and apply the preceding source construction to the actual head-only subfamily. Padding adds no forbidden class. The original full finite heights are retained for future queries.

Use734's unchanged quartic continuation with $\delta=2/5$ and growth exponent25. Every tail-touching original is assigned to its last exposed tail coordinate, keeping its complete earlier cofactor and actual globally fixed residue. Its local live kernel deletes current forbidden points; the old marginal is allowed to decrease. The inherited row-loss and complete mixed-query inequalities yield

$$
D_q\le\frac{5625}{2048}\frac{K}{(q-1)^4},
\qquad
K_{\rm new}\le K\left(1+\frac53 A_4(q)\right),
$$

where, for $t=1/(q-1)$,

$$
A_4(q)=15t+50t^2+60t^3+24t^4,
\qquad
1+\tfrac53 A_4(q)\le(1+t)^{25}.
$$

The same analytic prime-product premise as734 bounds the total loss for EVERY finite set of primes above $B$ by $K\tau(B,\ell)$, with

$$
\tau(B,\ell)=\frac{5625}{6144}
\left(\frac{2\ell^2+1}{2\ell^2-1}\right)^{25}
\frac{B}{(B-1)^4}
\sum_{j=0}^{25}\frac{25!}{(25-j)!(3\ell)^j}.
\tag{6}
$$

The required conditions are $B\ge286$, $\ell\ge4$, $3^\ell\le B$ and $4\ell\ge25$. The choice $(B,\ell)=(6561,8)$ satisfies them, with $3^8=6561$. Using the conservative bound590500 in(5), exact rational arithmetic gives

$$
\frac1{33750}-590500\,\tau(6561,8)
=0.000006669159635489544\ldots
>\frac1{150000}>0.
\tag{7}
$$

This is a distorted-source mass lower bound, not a final Haar-density bound. Positive mass produces a point in the finite padded CRT carrier avoiding every original class. Projecting out the dummy coordinates gives an integer survivor.

## 5. Verification and remaining scope

The standalone standard-library [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/capped_anchor_quantile_tail.py) and [exact result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/capped_anchor_quantile_tail.json) reconstruct all192 low comparison atoms, the complete geometric fourth moment, the upper-mass bracket and split atom, the independent threshold-fourth expression, the coefficientwise growth bound and the rational analytic allowance. An unresolved cutoff is rejected. No infinite auxiliary tail is discarded. The source construction, its mass theorem and the analytic prime-product theorem remain explicitly attributed premises.

The implementation checks the factor domains and rejects zero or oversized target mass, a missing cutoff, a negative atom and invalid analytic parameters. Its guards remain active under Python optimization. These finite checks verify the stated rational consequence, not an independent replay of Schroeder's whole arbitrary-height proof or a Lean theorem.

The cutoff6561 class contains the general eight-prime cutoff8000 class from778. The fourteen-prime result773 has an additional missing-small-prime assumption and remains a different family-level result. Families with nine or more original support primes at most6561 are not settled by this bound. The retained upper-mass comparator has loads at least192, so its first moment $W$ satisfies $W/m\ge192>28$. By773's exact one-step criterion $W<(q-1)m$, no legal constant clipping parameter at $q=29$ gives a positive sufficient ledger from THIS comparator. This is an obstruction to the stated upper bound, not to the actual survivor source or to a different ninth-prime argument. The new ingredient is a stronger common source/query boundary, and the cutoff is a sufficient value rather than an optimality claim.

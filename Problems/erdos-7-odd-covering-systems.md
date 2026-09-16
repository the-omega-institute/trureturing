---
slug: erdos-7-odd-covering-systems
bibkey: bloom2026erdos
doi: null
url: https://www.erdosproblems.com/7
triage: wall
motivation_gids:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
---

# Erdős #7: odd covering systems

## Problem

The [problem page](https://www.erdosproblems.com/7) asks:

> Is there a distinct covering system all of whose moduli are odd?

The negative target is the following unrestricted assertion. For every finite
set `D ⊂ ℕ` with `d > 1` and `d` odd for every `d ∈ D`, and every assignment
`a : D → ℤ`, there exists `z ∈ ℤ` such that

\[
  \forall d\in D,\qquad d\nmid z-a(d).
\]

Divisibility is in the integers. Set membership enforces distinct moduli;
there is no bound on their sizes, exponents, number, or total prime support.
A refutation requires a finite family satisfying exactly these conditions
whose classes cover every integer. The page remained open when read on
16 September 2026. The results below do not settle this unrestricted assertion.

The complete star head defined below **cannot be completed by any odd tail**
whose primes exceed 73, at any positive head heights and without restrictions
on tail support or graph structure. This applies to the specified star residue
assignment, including any subset of the odd head primes through 73 containing
3. Its actual survivor law reaches the BBMST continuation at global prime
index 309 with certified supported `Gamma<4331`; the rational stopping
threshold is greater than 4732. The proof and exact certificate are given in
(US1)--(US12). Arbitrary head assignments remain unresolved.

The pure-head continuation (PH1)--(PH7), sharpened by (AD1)--(AD5), excludes **arbitrary**
`{3,5,7}` head assignments and heights when all other primes are at least
19, with no tail support or graph restrictions. The odd parts 315 and 945
in the frozen 5040 fibre both permit tail cutoff 13, by (AD5).
Thus a hypothetical cover must involve at least one of 11, 13 and 17.
These missing-small-prime hypotheses remain; unrestricted #7 is open.

A further [ordinary noncoverage theorem](../docs/reports/erdos7-odd-covering/marked_head_profile.md#an-actual-full-fibre-old-configuration-with-unrestricted-tails)
allows both 11 and 13 at arbitrary finite heights, arbitrary axis and point
deletions, and unrestricted later primes, for an explicit old geometry.
Let U be the 16-point complement modulo 45 of `(3,0),(9,4),(5,0),(15,11),(45,2)`.
If the full original 3/5/7 part divides 315 and the old survivors contain
`U × {1,...,6}` in CRT coordinates modulo 45 and 7, the family cannot cover.
The same supported law has full-height mean at most `1134400/266709` and
square at most `35754161/1333545`. Keeping this configuration throughout a
3240-step exact tail certificate gives residual greater than 0.04896 at
prime 30011 and supported `Gamma<163516`, below the certified continuation
threshold `>167115`. The finite tail certificate then permits the BBMST
infinite continuation. One complete 315 family realizes the stated 96-point
set with redundant mixed-seven classes; those classes are not moved in this
argument. Thus this theorem is not an automatic elimination of a branch
after making every such class effective, nor a solution of unrestricted #7.

For arbitrary original residues with 3/5/7 part dividing 315, a
[stronger generic head estimate](../docs/reports/erdos7-odd-covering/marked_head_profile.md#actual-deletion-vectors-and-a-common-full-height-law)
retains every actual mixed-seven deletion vector. On one supported law,
with arbitrary finite 11/13 heights and arbitrary axis and point holes,
it gives `Gamma<=591122424341/16497075000` (less than 35.831954),
mean at most `1175795/219961`, and threshold-six hinge at most
`306627/391318`. Two complete enumerations recover all 161375 possible
old deletion vectors; none are discarded for redundancy. The optimized
old convex cost has an exact CRT realization at a globally unused
nonzero seven digit. These ordinary bounds strengthen the general
315-based head estimates, but do not supply its general tail continuation
or remove the original 3/5/7 exponent restriction.

The same uniform complete-survivor law at arbitrary finite3,5,7heights
also satisfies `Gamma<=3849/106` by (SD1)--(SD6), using shared cell parameters
and signed deletion energy. This improves `937/24` by `3473/1272`
without a new tail cutoff.

A [saturated-label transfer](../docs/reports/erdos7-odd-covering/marked_head_profile.md#saturated-low-labels-and-arbitrary-357-heights)
now connects finite315 geometry to arbitrary 3/5/7 heights. It retains
the original exponent labels in seven restricted families and gives
one eight-type moment kernel, a shifted-hinge bound, and conditioning
on the actual higher forbidden classes. For normalized heads, the
effective pure3/pure9 deletions reduce the ambient square error to
`10193/4536`, a saving of `3001/4536` over the preceding truncation
error. Twelve cylinder caps also yield a finite optimization route
for a nonuniform low law, using its own survival bound `1-R_high`.
These are ordinary all-height arguments with an exact rational
certificate; the error saving alone does not improve `3849/106`
or supply the missing generic tail continuation.

The transfer also retains a common weighted low layout at each auxiliary
depth, with exact nonnegative corrections for any finite depth box and
the full omitted geometric moments (SH10)--(SH13). This gives a finite
convex optimization that preserves the joint test geometry. An exact
rational dual obstruction (SH14) explains the need: for one explicit
77-point carrier, every probability constant within each surviving
seven-digit fibre leaves the preceding independent-cylinder/union
formula at least `101816531/2603049`, above `3849/106`. This is a lower
bound for that formula alone, not for actual test moments or arbitrary
77-point probabilities.

For families using only the primes 3, 5 and 7, (CM1)--(CM8) determine the
exact infimum of uniform uncovered density: \(53/432\). Every finite
family has strictly greater uncovered density, and an explicit family
with increasing prime-power heights approaches this value. The
all-height proof has exact CRT certificates; it is not an end-to-end
Lean theorem. The sharp finite minima for the two 5040 odd heads are
74 uncovered residues modulo 315 and 191 modulo 945. More generally,
(CM9)--(CM11) give the exact minimum \(58\cdot3^{H-2}+17\) modulo
\(3^H\cdot35\) for every \(H\ge3\).

## Motivation

The frozen module `D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity` proves
that distinct nontrivial divisors of `L = p^A q^B`, for distinct odd primes
`p,q`, leave at least `L/8` residues modulo `L` uncovered. This excludes
families supported on at most two odd primes, including arbitrary exponents.
It does not settle #7 with arbitrary prime support.

The [main reference](../Library/Arith/bloom2026erdos.md) records the question
and bounded literature search. Schroeder's September preprints claim that a
hypothetical cover needs [at least nine total prime divisors](../Library/Arith/schroeder2026nine.md)
and [some modulus with at least four distinct prime factors](../Library/Arith/schroeder2026noncoverage.md).
These are separate restrictions. The three-factors source rebuild, axiom audits,
and fresh kernel environment replay passed; the nine-prime source has no local
kernel replay. The linked notes give the exact pins and verification boundaries.

An independent public Lean development now proves the finite lcm exclusion
`10000 < lcm(D)` for every finite distinct odd covering family. Its exact
statement, source commit, archive hashes, and trust boundary are recorded in
[Mian--Siddique 2026](../Library/Arith/mian2026lcm10000.md). This is a direct
kernel-checked theorem for the original quantifiers, not a numerical search or
a reformulation of the Gamma estimates below. It pushes the first possible
unresolved lcm values to 10395, 12285, and 17325 in that finite-certificate
route. We reuse it as a citation-only boundary and do not add a bind-only
Lean wrapper.

### Independent finite lcm exclusion through 11486474

The existing common product-law argument below has a finite-height version
that gives an elementary exclusion independently of the external 10000 theorem.
Let \(N\) be odd. Complete any proposed family to one forbidden class for each
nonunit divisor of \(N\); avoiding this completion suffices to avoid the
original family. For every \(p^h\parallel N\), put

\[
 u_p=\sum_{e=1}^h p^{-e},\qquad s_p=\frac{u_p}{1-u_p},\qquad
 M_N=\prod_{p\mid N}(1+s_p)-1-\sum_{p\mid N}s_p.
 \tag{FC1}
\]

First remove the pure \(p\)-power classes in each prime-power coordinate.
The surviving density is at least \(1-u_p>0\). Under the uniform law on
that coordinate's actual survivors, each \(p^e\) cylinder has mass at most
\(p^{-e}/(1-u_p)\). The product of these laws is supported on points
avoiding every pure-power class. A mixed modulus has at least two prime
factors; summing its product cylinder bound over all distinct mixed
moduli gives exactly \(M_N\). Thus \(M_N<1\) excludes a cover and gives

\[
 \frac{\#\{\text{uncovered residues modulo }N\}}{N}
 \ge \prod_{p\mid N}(1-u_p)(1-M_N)>0.
 \tag{FC2}
\]

A two-block refinement also uses the same law. Partition the primes into
nonempty disjoint sets \(A,B\), and let \(a=M_A\), \(b=M_B\) be their
internal mixed-class budgets, computed by (FC1) with the same heights.
When \(0\le a,b<1\), the two internal deletion events are independent,
and their union has mass at most \(a+b-ab\). The remaining, crossing
classes have total mass at most \(M_N-a-b\). Consequently the full
mixed deletion has mass at most \(M_N-ab\). Replacing \(M_N\) by
\(M_N-ab<1\) in (FC2) is valid. This independence concerns disjoint
coordinate blocks; no independence of overlapping mixed classes is assumed.

These tests need only integers. Set
\(P_p=p^h\), \(U_p=(P_p-1)/(p-1)\), \(L_p=P_p-U_p\), and
\(D=\prod_p L_p\). Then

\[
 M_N=\frac{N-D-\sum_p U_pD/L_p}{D}.
 \tag{FC3}
\]

The [exact verifier](../docs/reports/erdos7-odd-covering/verify_lcm_10000_bridge.py)
uses an odd-divisor sieve to enumerate all odd abundant or perfect
\(N\le11486474\), starting at 1. Abundance is necessary because covering
requires \(\sigma(N)/N\ge2\). There are **23758** candidates, all abundant,
and **23757** have \(M_N<1\). The sole remaining candidate is

\[
 N=6891885=3^4\cdot5\cdot7\cdot11\cdot13\cdot17.
\]

Take \(A=\{3,5\}\) and \(B=\{7,11,13,17\}\). Here

\[
 a=\frac{10}{41},\quad b=\frac{149}{2304},\quad
 M_N-ab=\frac{1877957}{1889280}<1.
\]

The resulting uncovered-count lower bound is **11323** per period.
Therefore every hypothetical distinct odd covering system has
**least common multiple greater than 11486474**. The
[fixed certificate](../docs/reports/erdos7-odd-covering/lcm_10000_bridge_certificate.json)
contains the exact exceptional row, candidate count and digest, extremal
successful bound, and next failed criterion.

The first integer not excluded by these two elementary tests is
\(11486475=3^3\cdot5^2\cdot7\cdot11\cdot13\cdot17\); its best two-block
bound is \(1095631/1021440>1\). Failure of a sufficient test does not
establish a cover or exclude other methods. This is an ordinary CRT proof
with exact arithmetic, not a local Lean formalization or a claim of a new
best literature bound. In particular, Schroeder's nine-prime claim would
exclude this six-prime case as well; its verification boundary remains
that of the linked source note. No bind-only Lean declaration is added.

### Reuse of the 5040 and divisor-sum work

The connection to the project's 5040 work is the same finite prime-power
coordinate system and reciprocal-divisor weights. In particular,

\[
 5040=2^4\cdot3^2\cdot5\cdot7=16\cdot315,\qquad
 \sum_{d\mid N}\frac1d=\frac{\sigma(N)}N
   =\prod_{p\mid N}\sum_{e=0}^{v_p(N)}p^{-e}.
\]

Existing frozen declarations provide the following reusable ingredients:

| Existing declaration | Role here |
|---|---|
| [FiniteDivisorEulerProduct.divisor_sum_eq_euler_product](../D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct.lean) | Factor a finite divisor sum into local prime-power geometric sums. |
| [GoldenResourceOptimalInteger.golden_resource_sigma_identity](../D5/S3/Arith/GoldenResourceOptimalInteger.lean) | Identify the project's divisor objective with `log(σ(N)/N)−λ log N`. |
| [RobinExponentSwap.reciprocal_geom_sum_swap_strict](../D5/S3/Arith/RobinExponentSwap.lean) | Compare reciprocal-divisor products when prime exponents are reassigned. |
| [RobinRationalBasis.log_expansion_remainder_bound](../D5/S3/Arith/GoldenResource/RobinRationalBasis.lean) | Bound the remainder of the same positive `atanh` logarithm expansion used by the finite continuation verifier. |
| [GoldenDivisorLanguage.golden_fiber_5040](../D5/S3/Arith/GoldenResource/GoldenDivisorLanguage.lean) | The six integers with golden observation 5040 have exactly the two odd parts 315 and 945. |
| [GoldenDivisorLanguage.full_window_divisor_exponent_equiv](../D5/S3/Arith/GoldenResource/GoldenDivisorLanguage.lean) | Identify divisors with prime-exponent coordinates in Fibonacci-sized windows; its 5040 specialization has 60 divisors. |

These results are reused at their existing statements; no duplicate Lean
wrapper is introduced. The new mathematical arguments in this dossier are
not thereby Lean-verified. For the logarithm calculation, the public remainder
bound treats `1≤y<2` after binary range reduction; the endpoint `log 2`
uses pinned Mathlib's `Real.sum_range_le_log_div` at parameter `1/3`.

The odd part 315 lies just below a simple covering obstruction. For any
family of distinct nonunit divisors of `N`, the union bound on a full period
shows that covering would require `σ(N)/N≥2`. At the two adjacent heights,

\[
 \frac{\sigma(315)}{315}=\frac{208}{105},\qquad
 \sum_{\substack{d\mid315\\d>1}}\frac1d=\frac{103}{105}<1;
\qquad
 \frac{\sigma(945)}{945}=\frac{128}{63},\qquad
 \sum_{\substack{d\mid945\\d>1}}\frac1d=\frac{65}{63}>1.
\]

Thus moduli dividing `315=3²·5·7` leave at least `2/105=6/315` uncovered,
for every residue assignment. Raising only the 3-exponent to obtain
`945=3³·5·7` already makes this reciprocal-sum bound insufficient. It does
not prove coverage at 945. The finite-height CRT criterion (FC1)--(FC2)
gives the stronger bounds:

| Period \(N\) | Mixed budget \(M_N\) | Guaranteed uncovered residues |
|---|---:|---:|
| \(315\) | \(49/120\) | \(71\) |
| \(945\) | \(157/336\) | \(179\) |
| \(45045\) | \(233/320\) | \(3915\) |

The shared-cell argument (CM9)--(CM11) sharpens the first two rows to
**74 and 191**, respectively, and constructs assignments attaining both.
Their sharp mixed budgets under the same pure-product law are
\(23/60\) and \(145/336\).

The existing `golden_fiber_5040` theorem gives exactly
\(\{5040,10080,15120,20160,30240,60480\}\). Removing powers of 2 from
these six integers gives precisely \(\{315,945\}\). Thus the same golden
observation contains both sides of the simple reciprocal-sum threshold;
retaining the exact prime exponents and CRT coordinates supplies the
stronger exclusion. The verifier checks these arithmetic specializations
without duplicating the existing theorem.

The even coordinate also admits a concrete contrast: the five distinct
classes \(0\bmod2,0\bmod3,1\bmod4,5\bmod6,7\bmod12\) cover every integer,
and all five moduli divide 5040. Checking one period of length 12 verifies
this example. This does not settle whether an all-odd cover can exist.
The joint-load and survivor-profile estimates below retain additional
residue intersections for the unrestricted problem.

The prime 2 matters quantitatively. The uniform lower bound for avoiding
one pure class per prime-power modulus is

\[
 1-\sum_{e=1}^H p^{-e}\ge\frac{p-2}{p-1}.
\]

Its right side is positive for odd primes and zero for `p=2`. This is exactly
the positive denominator used in the odd-prime profiles, so 5040's even
coordinate cannot be inserted into that estimate unchanged.

The same coordinates give an exact second-moment connection. Under the
**unconditioned uniform** law `U_N` on a full period, two test classes have
intersection mass zero when their residues disagree modulo `gcd(d,e)`,
and `1/lcm(d,e)` otherwise. The existing
[compatible joint-image theorem](../D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.lean)
and [finite compatible CRT](../D5/S3/Factorization/PrimePowers/FiniteCompatibleCrt.lean)
supply the compatibility and realization statements; uniform counting gives
the mass. Choosing every test residue to be zero attains every pair bound
simultaneously. Consequently, as an ordinary mathematical deduction,

\[
 \Gamma_N(U_N)=\sum_{d,e\mid N}\frac1{\operatorname{lcm}(d,e)}
 =\prod_{p\mid N}\sum_{t=0}^{v_p(N)}\frac{2t+1}{p^t}.
\]

In particular `Γ315(U)=368/63`, `Γ5040(U)=1909/63`, and every finite
`N=3^a5^b7^c` has `Γ_N(U_N)≤35/4`. These concern the full uniform period.
The unconditioned law gives mass to forbidden points, so it is not a
complete-survivor law. Controlling the change caused by removal of actual
classes is precisely the extra obligation addressed by the common-density
and weighted-root arguments below; the numerical product alone does not
supply that obligation. No duplicate Lean declaration is introduced.

The finite-height coordinate law supplies that support obligation for both
odd parts of the 5040 fibre. For an odd head
\(Q=\prod_p p^{H_p}\), retain \(u_p\) and \(M_Q\) from (FC1), and put

\[
 \kappa_p=1+\sum_{e=1}^{H_p}(2e+1)p^{-e},\qquad
 A_Q=\prod_{p\mid Q}\left(1+\frac{\kappa_p-1}{1-u_p}\right).
 \tag{FC4}
\]

In each coordinate remove the **actual** pure-prime-power forbidden
classes, and let \(P_0\) be the product of the uniform laws on their actual
survivors. A cylinder modulo \(p^e\) has probability at most
\(p^{-e}/(1-u_p)\). Two cylinders intersect in either the empty set or a
cylinder at their larger exponent. Expanding any complete test-layout
load \(L=\sum_{d\mid Q}1_{x\equiv b_d\bmod d}\) therefore gives
\(\mathbb E_{P_0}L^2\le A_Q\): there are \(2e+1\) exponent pairs with
maximum \(e\), while the pair of zero exponents contributes 1.

Let \(E\) be avoidance of every actual mixed head class. Distinct original
moduli and (FC1) give \(\lambda=P_0(E)\ge1-M_Q\). If \(M_Q<1\), the law
\(\mu=P_0(\,\cdot\mid E)\) is uniform on the complete actual head survivor
set, because \(P_0\) was uniform on the Cartesian product of pure survivors.
Every complete layout includes the unit divisor, so \(L^2\ge1\) everywhere.
Consequently

\[
 \mathbb E_\mu L^2
 \le\frac{A_Q-(1-\lambda)}{\lambda}
 =1+\frac{A_Q-1}{\lambda}
 \le1+\frac{A_Q-1}{1-M_Q},\qquad
 \Gamma_Q(\mu)\le1+\frac{A_Q-1}{1-M_Q}.
 \tag{FC5}
\]

This holds uniformly over complete layouts, so taking their maximum is
legitimate. Missing forbidden classes, omitted primes and smaller heights
preserve the stated upper bounds. Exact evaluation yields

| Head period bound | \(M_Q\) | \(A_Q\) | Supported-law \(\Gamma\) bound |
|---|---:|---:|---:|
| \(Q\mid315\) | \(49/120\) | \(399/40\) | \(1148/71\) |
| \(Q\mid945\) | \(157/336\) | \(189/16\) | \(3812/179\) |

Substituting these supported-law bounds into the ordered local-kernel
criterion (DG5)--(DG6) below gives two further noncoverage theorems:

| Head | Tail primes | Tail graph | \(\delta\) | Saturated-head mass upper bound |
|---|---|---|---:|---:|
| \(Q\mid315\) | \(q\ge17\) | \(5\)-degenerate, including every planar graph | \(7/20\) | \(<0.808363\) |
| \(Q\mid945\) | \(q\ge19\) | \(5\)-degenerate, including every planar graph | \(9/25\) | \(<0.732710\) |

The tail exponents, prime count, maximum degree and treewidth remain
unbounded. The [exact verifier](../docs/reports/erdos7-odd-covering/verify_star_block_obstruction.py)
recomputes \(M_Q,A_Q,\Gamma\) and both strict rational comparisons in its
[certificate](../docs/reports/erdos7-odd-covering/star_block_obstruction_certificate.json).
This is an ordinary deduction from the actual-survivor construction and
the local-kernel criterion; it adds no Lean binding declaration and does
not settle the unrestricted problem.

More generally, if `mu` is any probability on an odd period `Q` and `u`
is uniform on `Z/2^a Z`, the actual-layout transfer and a product maximizing
layout give the exact identity

\[
 \Gamma_{Q2^a}(\mu\otimes u)
 =\Gamma_Q(\mu)\sum_{j=0}^a(2j+1)2^{-j}.
\]

The case `a=0` is immediate; otherwise the upper bound is (T1) with `delta=0`; for the lower bound choose a
maximizing old layout at every new exponent and nested dyadic cylinders.
At `a=4`, the multiplier is `83/16`, whereas the reciprocal-divisor
multiplier is `31/16`. Thus the exact link through 5040 preserves the
second-moment weights; replacing them by the divisor-sum weights would
change the quantity being bounded. The same argument works for any new
prime. It does not require a new Lean declaration.

The existing unique optimum at 5040 concerns the objective
`log(σ(N)/N)−(1/25)log N`, not an optimization over survivor probabilities.
Similarly, [robin_seven_smooth](../D5/S3/Arith/Robin/SevenSmooth.lean) bounds
`σ(N)/N` for `N=2^a3^b5^c7^d>5040` by Robin's logarithmic right-hand side.
Neither statement controls arbitrary forbidden residues or their conditioned
joint law. They supply arithmetic and coordinate tools; an implication from
those optimization statements cannot imply the proposed universal Γ73 bound:
the complete star family refutes that bound.

Two nearby measure constructions also have explicit limits here.
[Divisor Gibbs factorization](../D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.lean)
constructs probabilities on positive divisors, rather than on surviving
residue classes. [Coarse coupling lift](../D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.lean)
preserves given marginals once a compatible coarse coupling is supplied;
its support must additionally be shown to avoid the actual forbidden
relation. [Finite moment compression](../D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSparseLaw.lean)
retains the constraints of an already feasible law and does not establish
that law's existence. The exact fibre-cap criterion below identifies one
missing support condition, with an actual empty-fibre counterexample.

### Unrestricted tails from the 5040 odd heads

**Theorem.** Let the original family have finitely many distinct odd moduli
larger than one, with arbitrary residues. Let \(Q\) be the
\(\{3,5,7\}\)-part of the least common multiple of the **entire** family.
Each of the following hypotheses implies noncoverage:

| Head period | Every other prime factor | Tail restrictions |
|---|---:|---|
| \(Q\mid315\) | \(\ge13\) | none |
| \(Q\mid945\) | \(\ge13\) | none |
| \(Q=3^a5^b7^c\), arbitrary finite \(a,b,c\ge0\) | \(\ge19\) | none |

In particular the first two rows use precisely the odd parts in the frozen
5040 fibre. There is no bound on tail exponents, the number of prime factors
in one modulus, the total prime count, or the interaction graph. The first
two rows bound the head exponents even in classes ending at later primes.
The absent small primes are genuine hypotheses: the three rows respectively
exclude \(\{11\}\), \(\{11\}\), and \(\{11,13,17\}\).
Thus the third row implies that any hypothetical odd distinct cover must
use at least one prime in \(\{11,13,17\}\). It does not resolve #7.
The initial constant-threshold certificates below establish these rows
from 17, 19 and 23, respectively. The adaptive schedules (AD1)--(AD5)
give the stated cutoffs. In particular, a hypothetical odd cover with
no prime factor 11 must have \(3^4\), \(5^2\), or \(7^2\) dividing
its least common multiple.

**Preserve the pure-head product until the final conditioning.** Use the
actual pure-survivor product law \(P_0\) from (FC4). For a finite endpoint
height \(h_p\), put \(u_p=\sum_{e=1}^{h_p}p^{-e}\); for the third row put
\(u_p=1/(p-1)\). In either case use cylinder cap
\(c_pp^{-e}\), where \(c_p=1/(1-u_p)\). These bounds hold for smaller
physical heights and omitted classes. Before deleting any mixed head class,
their union has \(P_0\)-mass at most
\[
 M=\prod_{p=3,5,7}(1+r_p)-1-\sum_{p=3,5,7}r_p,
 \qquad r_p=\frac{u_p}{1-u_p}.
 \tag{PH1}
\]
This is the original-modulus union bound from (FC1), giving
\(M=49/120,157/336,2/3\) in the three rows.

Run the normalized actual tail kernels (US4) with \(\delta=2/5\), starting
at 17, 19 and 23 respectively for these three constant schedules.
They integrate to one at **every** old
history, including head points lying in a mixed forbidden head class.
Therefore the head marginal stays exactly \(P_0\), and the total probability
of mixed head violations remains at most \(M\) throughout. Tail pure powers
have already been removed in their coordinate base laws. All physical
coordinate heights resolve the entire original family.

For finite head endpoint heights choose independent auxiliary \(K_p\) with
\(\Pr(K_p\ge e)=c_pp^{-e}\) for \(1\le e\le h_p\) and zero thereafter.
For the third row use these tails at all positive depths. At each old tail
prime use \(c_p=(p-1)/((p-2)(1-\delta))\) and the infinite height law.
All caps satisfy \(c_p\le p\). The finite multiplier \(f=1+K_p\) has atoms
\[
 a_1=1-c_p/p,\quad
 a_f=c_p(p-1)p^{-f}\ (2\le f\le h_p),\quad
 a_{h_p+1}=c_pp^{-h_p}.                               \tag{PH2}
\]
The terminal atom includes all remaining mass. Raising a finite endpoint
height increases every old tail probability and adds nonnegative new ones;
thus using the 315 or 945 endpoints bounds every divisor head period.
Missing head primes can likewise be added as auxiliary factors at least one.

Let \(D_q\) be the product of \(1+K_p\) over the head primes and earlier
tail primes. Apply the published conditional comparison exactly as in
(US6)--(US7). Every original label \(dq^e\) retains its own residue and
weight \((q-1)q^{-e}\). Completing the nonunit cofactors, after summing
these weights to one, bounds the actual assigned mixed violation by
\[
 b_q=\frac{\mathbb E(D_q-1-(q-2)\delta)_+}{(q-2)(1-\delta)}.
 \tag{PH3}
\]
The missing unit cofactor is precisely the pure power already removed;
projected cofactors need not be distinct. The actual head law is a product
here, while every tail cap holds conditional on the entire past.

Under this **same** actual law, comparison of every complete-layout squared
load gives \(\Gamma\le J_B=\mathbb E D_B^2\). The mixed head and assigned
tail violations have total mass at most
\[
 C_B=M+\sum_{q_0\le q\le B\atop q\ \mathrm{prime}}b_q.
 \qquad
 \Gamma_{\mathrm{supported}}\le
 1+\frac{J_B-1}{1-C_B}\quad\text{if }C_B<1.             \tag{PH4}
\]
The second inequality follows by conditioning **once** on avoiding all
prefix classes, using \(L^2\ge1\) for every complete load. In particular,
head conditioning does not enlarge each earlier tail charge separately.
The three auxiliary head means and second moments are computed from (PH2)
or its infinite version; the second moments are respectively
\(399/40,189/16,325/18\), with third-row mean \(16/5\).

**Exact finite certificates.** The existing
[verifier](../docs/reports/erdos7-odd-covering/verify_star_block_obstruction.py)
recomputes `pure_head_unrestricted_stoploss` in its
[certificate](../docs/reports/erdos7-odd-covering/star_block_obstruction_certificate.json).
It uses the directed positive-part identity (US10), full means and second
moments, and upward rounding on the grid \(10^{-18}\). It retains 819 low
product states for the first two rows and 3277 for the third. States above
these cutoffs cannot return to a lower product because every multiplier is
at least one; their contributions to the full moments are retained.

| Head | \(B\) | Global \(k=\pi(B)\) | \(C_B\) upper | \(J_B\) upper | Supported \(\Gamma\) upper |
|---|---:|---:|---|---|---|
| \(Q\mid315\) | 2048 | 309 | \(161204797404174493/250000000000000000\) | \(1180711995543371791951/10^{18}\) | \(393355725451251697993/118393603461100676<3323\) |
| \(Q\mid945\) | 2048 | 309 | \(80743815756256021/125000000000000000\) | \(1037847766022931255003/10^{18}\) | \(79784755038221631295/27234574919227064<2930\) |
| arbitrary \(3^a5^b7^c\) | 8192 | 1028 | \(458276998847445589/500000000000000000\) | \(111217368531894713201/40000000000000000\) | \(2779517659299672938847/83446002305108822<33310\) |

At \(k=309\), (US12) gives the sufficient stopping threshold greater than
4732. At \(k=1028\), the existing positive-series logarithm calculation in
`verify_finite_continuation.py:stopping_threshold` gives the lower bound
\[
 \frac{8861473523187882599326452722900980214033}
      {250000000000000000000000000000000000}>35445.    \tag{PH5}
\]
An independent, shorter bound also suffices: \(\log2\ge56/81\) and
\(\log3\ge263/240\) imply, since \(k\ge1024\) and \(\log k>6\),
\[
 k(\log k+\log\log k-3)^2
 \ge1028(36941/6480)^2
 =350711832617/10497600>33400>33310.                   \tag{PH6}
\]
Thus every row reaches BBMST Theorem 6.1 with positive actual survivor mass.
Restart (T1)--(T6) using the supported law from (PH4); the usual uniform-base
continuation covers every later prime without any support restriction.
The global index includes 2 and absent primes, whose physical exponents
can be zero. If the original family ends before the stopping point, its
already positive survivor mass suffices. Finite CRT supplies an uncovered
integer in all cases.

This is an ordinary proof with exact arithmetic certificates. Independent
divisor-convolution implementations reproduce all 303, 302 and 1020 step
charges and the final bounds, with 815 or 3276 retained states. It is not
an end-to-end Lean theorem. Earlier graph and bounded-support rows remain
valid quantitative refinements; their restrictions are unnecessary for
noncoverage under the hypotheses certified in the preceding table.

**Both odd parts of the 5040 fibre permit prime 17.** For \(Q\mid945\),
use the same finite head heights \((3,1,1)\), mixed-head charge
\(157/336\) and head second moment \(189/16\), now processing every
tail prime from 17. Keep \(\delta=2/5\). The additional certificate
`finite_945_tail17_stoploss` uses the complete terminal atoms in (PH2)
and the same directed recurrence through \(B=8192\), where the global
index is \(k=1028\). It gives
\[
 \begin{aligned}
 C_B&\le792001218575786359/10^{18}<1,\\
 J_B&\le3198136266025222684001/10^{18},\\
 \Gamma_{\mathrm{supported}}
 &\le\frac{3197344264806646897642}{207998781424213641}
 <15372<35445.
 \end{aligned}                                     \tag{PH7}
\]
The stopping lower bound (PH5) is greater than 35445. Thus the identical
same-law comparison, final conditioning and BBMST continuation prove
noncoverage for every distinct original family with \(Q\mid945\)
and all other prime factors at least 17. The entire-family head-height
condition is retained; no tail exponent, support, graph or total
prime-count restriction is added. Together with the 315 certificate,
this gives the same tail cutoff for both odd parts of the frozen fibre.
An independent divisor-convolution implementation reproduces all 1022
charges using the complete finite terminal atoms. Independently,
\(\log2>56/81\) and \(k=1028\ge1024\) give
\(k(\log k+\log\log k-3)^2>21021572/729>28835\),
which also suffices for (PH7).

### Adaptive kernels lower the unrestricted cutoff to 19

Keep the same actual pure-head product law \(P_0\), but use the coupled
mixed-head bound \(M=82/135\) proved in (CM1)--(CM2). The full initial
auxiliary product has mean \(16/5\) and second moment \(325/18\).
All physical coordinate heights resolve the entire original family,
including classes whose largest prime has not yet been processed.
Its head caps remain \(2\cdot3^{-e},(4/3)5^{-e},(6/5)7^{-e}\).
For each successive prime \(q\ge19\), choose a deterministic integer
threshold \(1\le t_q\le q-2\), and set
\[
 s_q=q-1-t_q,\qquad
 \delta_q=\frac{t_q-1}{q-2},\qquad c_q=\frac{q-1}{s_q}.
 \tag{AD1}
\]
Then \(s_q\ge1\), \(0\le\delta_q<1\), and \(c_q<q\), so
\(\Pr(K_q\ge e)=c_qq^{-e}\) is a valid auxiliary height law.
The normalized actual kernel preserves every old marginal, including
\(P_0\), and satisfies these caps conditional on the entire history.
At \(t_q=1\), the kernel has \(\delta_q=0\) and equals the identity
density relative to the pure-survivor base law; this endpoint is valid.

Let \(D_q\) be the completed auxiliary product for the earlier primes
under this one fixed schedule, and put \(V_q(t)=\mathbb E(D_q-t)_+\).
The original-label comparison (PH3) and the full moment identities give
\[
 b_q\le\frac{V_q(t_q)}{s_q},\qquad
 \mathbb E D_{\mathrm{new}}=\mathbb E D_q(1+1/s_q),\qquad
 J_{\mathrm{new}}=J_q\left(1+\frac{3q-1}{s_q(q-1)}\right).
 \tag{AD2}
\]
Here \(J_q=\mathbb E D_q^2\) also bounds every complete-layout
second moment under the same actual law. Thus, starting with
\(\lambda=53/135\), each certified step updates
\(\lambda_{\mathrm{new}}=\lambda-V_q(t_q)/s_q\).
One final conditioning bounds the supported parameter by
\[
 \Gamma_{\mathrm{supported}}\le
 1+\frac{J_{\mathrm{new}}-1}{\lambda_{\mathrm{new}}}
 =1+\frac{(J_q-1)s_q+J_q(3q-1)/(q-1)}
              {\lambda s_q-V_q(q-1-s_q)}.
 \tag{AD3}
\]
Only positive denominators are admissible. Every subsequent auxiliary
distribution includes the previously chosen factor \(1+K_q\);
charges and moments from different schedules are never combined.

For finding a schedule, minimizing this one-step potential is a useful
finite search. Since \(D_q\) is integer-valued, \(V_q\) is affine
between integer thresholds, making (AD3) fractional-linear on each such
interval. A zero denominator approaches infinite cost. On the remaining
interval \(0<s<1\), write
\(V_q(q-1-s)=A+Bs\), where \(A\ge0\) and \(B\ge0\).
Feasibility forces \(\lambda>B\), and differentiating (AD3) gives
a negative numerator \(-(J_q-1)A-J_q(3q-1)(\lambda-B)/(q-1)\).
Thus \(s=1\) dominates that interval; integer thresholds suffice for
the local search. This asserts no global schedule optimality.
BBMST Section 6, Lemma 6.2 and equation (25) already use sequential
potential minimization; (AD3) uses the full stop-loss profile in place
of their scalar recurrence. The proof below needs only the admissibility
and exact replay of the selected schedule.

**Exact stopping certificate.** The fixed schedule has 1388 steps, one
for every prime from 19 through 11593. Its largest threshold is 3072.
The existing [verifier](../docs/reports/erdos7-odd-covering/verify_star_block_obstruction.py)
recomputes `adaptive_head_stoploss` in the adjacent
[certificate](../docs/reports/erdos7-odd-covering/star_block_obstruction_certificate.json).
It propagates the full first and second moments separately
and retains all product probabilities needed in
\[
 V_q(t)=\mathbb E D_q-t+
       \sum_{1\le d<t}(t-d)\Pr(D_q=d).
\]
All displayed data coefficients are nonnegative. Upward rounding on
the grid \(10^{-18}\) therefore gives upper bounds for the charges and
moments; discarded larger product states cannot return below a later
threshold, since every factor is at least one. The resulting bounds are
\[
 \begin{aligned}
 C&\le956616008688320979/10^{18}<1,\\
 J&\le2341844006153474338859/10^{18},\\
 \Gamma_{\mathrm{supported}}
 &\le\frac{2340887390144786017880}{43383991311679021}
 <53958
 <\frac{26988288270685431527657582636743677951}{5\cdot10^{32}}
 <k(\log k+\log\log k-3)^2,\qquad k=1395.
 \end{aligned}
 \tag{AD4}
\]
The global index is \(\pi(11593)=1395\), including 2 and all absent
primes. The rational stopping lower bound exceeds 53976 and is produced
by the existing positive-series logarithm bounds. Positive actual
survivor mass and (AD4) satisfy BBMST Theorem 6.1. After the one
conditioning, set \(i_0=k\), \(\mu_{i_0}=1\) and
\(\kappa=\Gamma_{\mathrm{supported}}\); (T1)--(T2) supply its
moment hypothesis for every later standard uniform-base kernel schedule.
No second division by the prefix survivor probability is needed.
The continuation and finite CRT handle all remaining tail primes. No bound on tail support,
exponents or graph structure is introduced. This proves the arbitrary
\(3^a5^b7^c\) row from prime 19. It remains an ordinary mathematical
proof with an exact arithmetic certificate, not an end-to-end Lean proof.
An independent implementation using target-state divisor convolution
reproduces every charge and the full retained-state digest; independent
trial division and positive-series logarithm bounds also give
\(k=1395\) and stopping threshold greater than 53976.

**Adaptive continuation of both 5040 odd heads from prime 13.** The
same argument applies to the finite head laws (PH2), retaining their
terminal atoms. For \(Q\mid315\), use head mean \(21/8\), second
moment \(399/40\) and mixed charge \(49/120\). For \(Q\mid945\),
these are \(45/16\), \(189/16\) and \(157/336\). Process every
tail prime from 13 with a fixed integer-threshold schedule as in (AD1).
The directed certificates give:

| Head bound | Last prime | Global index | Tail steps | Total charge upper | Supported \(\Gamma\) upper |
|---|---:|---:|---:|---|---|
| 315 | 1021 | 172 | 167 | \(808205363366166533/10^{18}\) | \(470837795264907661091/191794636633833467<2455\) |
| 945 | 32141 | 3448 | 3443 | \(243263384072888041/(25\cdot10^{16})\) | \(4873698555453475972051/26946463708447836<180866\) |

For the two rows the exact second-moment upper bounds are respectively
\(58955750078534228453/(125\cdot10^{15})\) and
\(974934321797953504843/(2\cdot10^{17})\). The verified BBMST
stopping lower bounds are
\[
 \begin{aligned}
 k=172:\quad&
 \frac{616354713939123394926331754277098284347}
      {25\cdot10^{34}}>2465>2455,\\
 k=3448:\quad&
 \frac{22610845432447282250071455861855940497071}
      {125\cdot10^{33}}>180886>180866.
 \end{aligned}                                     \tag{AD5}
\]
Both total charges are strictly below one. All comparisons and the
single final conditioning concern the same actual measure, so (AD5)
restarts BBMST and proves noncoverage with unrestricted tails from 13.
The existing verifier reproduces `finite_315_tail13_adaptive` and
`finite_945_tail13_adaptive` in its adjacent certificate, including
every selected threshold and charge.
The certificate retains 192 and 8192 low product states, respectively;
their omitted high-state contributions remain in the full moments.
As in the arbitrary-height case, the schedules are verified directly
without requiring a proof of global control optimality. The head
exponents bound the entire original family, including later-ending
moduli. Independent divisor-convolution implementations reproduce every
step and both full retained-state digests; independent prime counting
and positive-series logarithm bounds verify the displayed stopping
inequalities. These are ordinary proofs with exact certificates.

### Homogeneous cylinder capacities and the extremal comb

**Theorem.** Let \(p\ge2\), \(H\ge0\), and give every node of a full
\(p\)-ary tree at absolute depth \(d\) the same capacity \(\beta_d\ge0\).
A feasible flow is a nonnegative leaf measure whose mass below each
node does not exceed its capacity. A forbidden node has zero mass,
including all its descendants. Forbidden nodes have positive depth,
with at most one at each depth; redundant descendants are allowed. Among all
such forbidden assignments, the smallest maximum root flow is attained
by the comb with forbidden prefixes \((p-1)^{e-1}0\), \(1\le e\le H\).
Repeated digits are meant here. No monotonicity of the capacities is needed.

Let \(F_d\) be the full-subtree maximum and \(C_d\) the comb maximum.
Their recursions, evaluated from depth \(H\) upward, are
\[
 F_H=C_H=\beta_H,\qquad
 F_d=\min(\beta_d,pF_{d+1}),\qquad
 C_d=\min(\beta_d,(p-2)F_{d+1}+C_{d+1}).               \tag{HC1}
\]
Every actual assignment has maximum root flow at least \(C_0\).
In particular, if \(\beta_0=C_0=1\), every actual tree supports a
probability law with all these cylinder caps. The law may depend on
the actual forbidden prefixes and need not be the comb law.

**Proof.** An unblocked node's maximum is the minimum of its capacity
and the sum of its children's maxima. Attainment follows by splitting
any permitted mass among the children within their individual maxima,
then realizing these masses recursively; scaling handles all smaller
masses. This also covers zero capacities. Put
\(s_d=pF_{d+1}-F_d\ge0\). If child \(i\) has deficit \(\ell_i\) from
\(F_{d+1}\), the parent's deficit from \(F_d\) is exactly
\[
 F_d-\min(\beta_d,pF_{d+1}-\sum_i\ell_i)
       =(\sum_i\ell_i-s_d)_+.                        \tag{HC2}
\]
A directly forbidden child has deficit \(F_{d+1}\); its forbidden
descendants have no further effect.

A stronger induction keeps track of allowed absolute depths. For
\(A\subseteq\{d+1,\ldots,H\}\), define \(L_H(\varnothing)=0\) and
\[
 L_d(A)=\left[
 {\bf1}_{d+1\in A}F_{d+1}
 +L_{d+1}(A\cap\{d+2,\ldots,H\})-s_d
 \right]_+.                                         \tag{HC3}
\]
This is the comb deficit when it uses exactly the depths in \(A\).
At a selected depth the spine has one blocked child, \(p-2\) full
children and one continuing child; at an unselected depth it has
\(p-1\) full children and the continuation. The continuing terminal
leaf is allowed, giving the zero base deficit.

Downward induction proves that \(L_d\) is monotone in \(A\) and
superadditive for disjoint sets:
\(L_d(A\cup B)\ge L_d(A)+L_d(B)\).
For the latter, the next-depth indicators add, and the induction
hypothesis bounds the later loss of the union below by the sum.
The final positive-part step uses
\((u+v-s)_+\ge(u-s)_++(v-s)_+\) for \(u,v,s\ge0\):
if both exceed \(s\), the difference is \(s\); if exactly one does,
the other adds a nonnegative amount; otherwise the right side is zero.
Monotonicity follows directly from (HC3).

Now consider any actual nonforbidden node of depth \(d\) whose permitted
forbidden depths are \(A\). Let \(\epsilon\) indicate a directly blocked
child. For each other child let \(A_i\) be the set of deeper forbidden
depths occurring below it. These sets are pairwise disjoint because
globally at most one node is forbidden at each depth; they are contained
in \(A'=A\cap\{d+2,\ldots,H\}\). Discard redundant deletions inside a
directly forbidden child. Induction, superadditivity and monotonicity give
\[
 \sum_i\ell_i
 \le\epsilon F_{d+1}+\sum_i L_{d+1}(A_i)
 \le{\bf1}_{d+1\in A}F_{d+1}+L_{d+1}(A').
\]
Equation (HC2) bounds the parent's deficit by \(L_d(A)\). At the root
with every positive depth allowed, this is \(F_0-C_0\), proving (HC1)'s
extremal assertion. Missing or redundant exclusions cannot worsen it.

The theorem applies to distinct pure prime-power moduli because they
give at most one forbidden prefix at each depth. Homogeneity by depth
and this global multiplicity bound are essential hypotheses of the
argument; arbitrary node-dependent capacities or several exclusions at
one depth are outside its scope. It does not identify the maximum
complete-layout second moment of the resulting measure.

**Sharp scalar-cap boundary for the ternary comb.** At height \(H\ge1\),
forbid \(3^{e-1}-1\bmod3^e\), equivalently prefix \(2^{e-1}0\) in
least-significant-digit order. For any supported probability \(\mu\), put
\(\beta_e=\max_{r\bmod3^e}\mu(r)\) and \(R(\mu)=\sum_{e=1}^H\beta_e\).
Then
\[
 \min_\mu R(\mu)=1-2^{-H}.                            \tag{HC4}
\]
Indeed, let \(b_j\) be the mass escaping the spine through digit 1 at
depth \(j\), and \(S_e=\sum_{j\le e}\beta_j\). Before depth \(e\),
the spine carries \(1-\sum_{j<e}b_j\ge1-S_{e-1}\).
Its two allowed children each have mass at most \(\beta_e\), so
\(2\beta_e\ge1-S_{e-1}\) and \(S_e\ge(1+S_{e-1})/2\).
Starting with \(S_0=0\) yields the claimed lower bound.

For attainment, split each spine mass equally between its digit-1
escape and digit-2 continuation; make escaped suffixes uniform.
Escape \(j\) has mass \(2^{-j}\), and the final spine leaf has mass
\(2^{-H}\). At depth \(e\), a cylinder in an earlier escape \(j<e\)
has mass \(2^{-j}3^{-(e-j)}\le2^{-e}\), while the new escape and
continuing spine each have mass \(2^{-e}\). Thus \(\beta_e=2^{-e}\).
The uniform-survivor law instead has
\(R=(3^H-1)/(3^H+1)\), which is larger when \(H\ge2\).

The optimum in (HC4) tends to one. Consequently no fixed
\(\varepsilon>0\) improves the scalar bound to \(R\le1-\varepsilon\)
for every ternary family and height. With the usual independent 5/7
caps, the mixed-head max-cap envelope \((1+9R)/15\) tends to \(2/3\).
This is a limitation of that envelope; the actual bad mass has the
strictly smaller bound (CM1).

The scalar minimizer does not minimize every quantity used by the tail
argument. Its auxiliary height has \(\Pr(K\ge e)=2^{-e}\),
\(1\le e\le H\), and \(X=1+K\) obeys
\[
 \mathbb EX=2-2^{-H},\qquad
 \mathbb EX^2=6-(2H+5)2^{-H},\qquad
 \mathbb E(X-j)_+=2^{1-j}-2^{-H}\quad(1\le j\le H).
\]
The stop-loss function is linear between integer thresholds, equals
\(\mathbb EX-t\) for \(t\le1\), and is zero for \(t\ge H+1\).
At infinite height its values \(2^{1-j}\) exceed the uniform-survivor
auxiliary values \(3^{1-j}\) for every integer \(j\ge2\), and its second
moment is 6 instead of 5. Optimizing \(R\) alone therefore does not
supply a tail-profile improvement.

These are ordinary all-height proofs. The existing
[verifier](../docs/reports/erdos7-odd-covering/verify_star_block_obstruction.py)
records **homogeneous_comb_capacity** in its
[certificate](../docs/reports/erdos7-odd-covering/star_block_obstruction_certificate.json):
5832 exact flow comparisons over all 729 ternary height-three forbidden
assignments and eight capacity profiles, including nonmonotone and zero
caps, together with the binary-split laws at heights 1 through 6.
The finite checks supplement the proofs and are not Lean kernel proofs.
The general recursive comparison (HC1)--(HC3) is formalized by
[`HomogeneousCombCapacity.comb_le_actual_prefix_flow`](../D5/S3/Arith/Congruence/HomogeneousCombCapacity.lean).
Its Boolean obstacle predicate is on actual finite words; the per-depth
count includes redundant forbidden descendants. It proves the comparison
for arbitrary \(p\ge2\), heights and nonnegative capacity profiles,
without assuming the deficit aggregation inequality. Its formal conclusion
compares the explicit min/sum recursions. The separate constructive theorem
[`PrefixCapacityRealization.exists_comb_capped_probability`](../D5/S3/Arith/Congruence/PrefixCapacityRealization.lean)
now realizes these capacities by actual nonnegative leaf weights with total
mass one. Every forbidden prefix has zero mass, and every depth-\(d\)
prefix has probability at most \(\beta(d)/\mathrm{combFlow}\), provided
the comb flow is positive. Its proof constructs actual child measures and
scales their sums before applying the existing comparison. Both capacity
theorems work over any linearly ordered field, including the rationals;
the normalized rational weights directly form the imported `FiniteLaw`.
The licensed `ThreePrime/DistortionChain` supplies `PhysicalChain`, its
covered-probability bound, and `BaseCaps` propagation without a restriction
on the number of prime factors per modulus. The actual ordinary-cover
connection and residual-cylinder base-cap interface are formalized below;
cofactor completion and numerical stopping still have to be connected
in the end-to-end formalization.

The actual uniform survivor law is supplied by
[`PurePrefixResidualLaw.exists_exact_residual_law`](../D5/S3/Arith/Congruence/PurePrefixResidualLaw.lean).
For every integer alphabet size \(p\ge3\), height \(H\ge0\) and one arbitrary
forbidden prefix at each positive depth, it removes prefixes with forbidden
ancestors, retaining a disjoint set \(R\) with the same forbidden union.
The theorem constructs the rational law on actual surviving words and
proves its positive normalizer
\(Z=1-\sum_{e\in R}p^{-e}\). For every test prefix \(u\) at depth \(d\),
a forbidden ancestor gives zero probability; otherwise its probability is
\[
 \frac{p^{-d}-\sum_{e\in R:\,f_e\text{ extends }u}p^{-e}}{Z}.
\]
The proof derives the disjoint decomposition from the given words, using
shortest forbidden ancestors and prefix nesting. Conditioning, individual
prefix counts and positivity are reused from the licensed development.
The actual ordinary-cover consumer is now formalized by
[`ActualCylinderChain.ordinary_cover_forces_charge_and_caps`](../D5/S3/Arith/Congruence/ActualCylinderChain.lean).
For any finite distinct odd covering system, choose a cut after the first
\(b\) prime coordinates and any rational probability law \(\mu\) on their
full prime-power words. The head coordinates may be correlated. Assume
\(\mu\) gives probability one to avoiding every actual head-only cylinder.
For arbitrary rational tail thresholds \(0\le\delta_i<1\), the theorem
builds the actual full-history tail chain \(P_x\) at each fixed head point
and proves
\[
 1\le\mathbb E_\mu\bigl[\mathrm{totalCharge}(P_x)\bigr].
\]
The licensed CRT and prime-factorization interfaces supply the actual
cylinders and injective original depth labels. All original labels are
retained: different original moduli can have the same tail cofactor after
their head parts are removed. The live support induction proves pure-tail
prefix avoidance with probability one under the same joint law
\(\mu\mathbin{\mathrm{joint}}(x\mapsto P_x.\mathrm{law})\), including
zero-weight ambient points. Gluing the head to the tail diagonal words
transports ordinary coverage to a charged mixed-cylinder hit.
The same theorem derives `BaseCaps` for every \(P_x\) from the explicit
residual-cylinder inequalities
\(\Pr(C_{c,b+i})\le(1-\delta_i)\,\mathrm{survival}_{R_i}(e_{c,b+i})\).
It has no restriction on the number of prime factors per modulus. The
empty-head specialization recovers the pure-coordinate product-base result.

The head input resolves the **full** prime-power heights of the original
family. A finite315 law directly addresses a head dividing315; preserving
its marginal when higher head powers are added requires an additional
argument and is not assumed. Transporting a concrete arithmetic head law
to the full word interface, completing cofactor labels and proving an
average charge below one remain obligations for an end-to-end noncoverage
theorem. No numerical noncoverage endpoint is imported.

#### Sharp tail profiles of maximal cylinder caps

The preceding scalar boundary extends to all positive-part thresholds.
Let \(p\ge3\) be any integer alphabet size, and let \(R_H\) be the actual
survivors of the same comb at height \(H\ge1\). Their number is
\(N_H=((p-2)p^H+1)/(p-1)\). For any probability \(\mu\) on \(R_H\),
let \(\beta_e(\mu)\) be its largest actual depth-\(e\) cylinder mass.
Then
\[
 \min_\mu\sum_{e=1}^H\beta_e(\mu)
     =\frac{1-(p-1)^{-H}}{p-2},\qquad
 \min_\mu\sum_{e=j}^H\beta_e(\mu)
     =\frac{p^{H-j+1}-1}{(p-2)p^H+1}\quad(2\le j\le H).
 \tag{HC5}
\]
The uniform survivor law attains all the second set of objectives
simultaneously. It need not attain the first. The proof of (HC4) extends
to the first identity: at each spine fork there are \(p-2\) escapes and
one continuation, giving
\((p-1)\beta_e\ge1-(p-2)S_{e-1}\), hence
\(S_e\ge(1+S_{e-1})/(p-1)\). Equal splitting between the \(p-1\) allowed
children, followed by uniform escaped suffixes, attains this lower bound.

Here is a matching transport dual for the second identity. Partition
\(R_H\) into its \(p-2\) full escape subtrees at each depth \(d\), each
with \(p^{H-d}\) leaves, plus the terminal spine singleton. Put
\(\lambda=(p^{H-j+1}-1)/((p-2)p^H+1)\). Supply at selected depth \(e\)
is \(p^{H-e}\); each escape group demands \(\lambda\) times its leaf
count, and the terminal singleton demands \(\lambda\). A depth can
supply a group only after its escape, and can supply the terminal only
at \(H\). Total supply equals total demand.

These availability sets are nested. For every \(k\ge j\), the groups
escaping at or after \(k\), together with the terminal, contain
\(((p-2)p^{H-k+1}+1)/(p-1)\) leaves and have available supply
\((p^{H-k+1}-1)/(p-1)\). Their demand fits because, writing
\(x=p^{H-k+1}\ge p\),
\[
 \lambda<\frac{p^{1-j}}{p-2}
 \le\frac1{p(p-2)}\le\frac1{p-1}
 \le\frac{x-1}{(p-2)x+1}.                            \tag{HC6}
\]
The last fraction increases with \(x\) and equals \(1/(p-1)\) at \(p\).
For \(k<j\) all supply is available and the corresponding demand is at
most the total; terminal demand is at most the last supply one. Thus a
greedy allocation, filling latest groups from latest available depths,
meets every demand. The suffix inequalities guarantee that the groups
with fewer available depths cannot exhaust their supply prematurely.

If \(q_{e,g}\) is supply assigned to a group of \(n_g\) leaves, give
each full depth-\(e\) cylinder in it dual weight \(q_{e,g}/n_g\).
Such a cylinder has \(p^{H-e}\) leaves. At every selected depth the
weights sum to one; every survivor leaf receives total weight
\(\lambda\). The terminal singleton is an ordinary depth-\(H\) cylinder
and is included. Therefore
\[
 \lambda=\sum_e\sum_C w_C\mu(C)
 \le\sum_{e=j}^H\beta_e(\mu).
\]
Under the uniform law, full cylinders attain
\(\beta_e=p^{H-e}/N_H\); summing them gives \(\lambda\), completing the
proof of (HC5).

These exact finite minima identify a limitation of the marginal-cap
comparison itself. The sequence \(\beta_e\) decreases, so it defines
an auxiliary \(K_H\) with \(\Pr(K_H\ge e)=\beta_e\) and \(K_H\le H\).
For \(X_H=1+K_H\), its integer positive-part values are
\(\mathbb E(X_H-j)_+=\sum_{e=j}^H\beta_e\). The minima in (HC5) converge
to \(1/(p-2)\) at \(j=1\), and to \(p^{1-j}/(p-2)\) at \(j\ge2\).
These are precisely the values of \(X_\infty=1+K_\infty\), where
\[
 \Pr(K_\infty\ge e)=\frac{p-1}{p-2}p^{-e}.
\]
For every fixed real-valued increasing convex function \(\phi\) on the
positive integers, the discrete expansion
\(\phi(x)=\phi(1)+a(x-1)+\sum_{j\ge2}b_j(x-j)_+\) has
\(a,b_j\ge0\). Applying (HC5) to any finite subset of terms, passing to
the lower limit and then taking the supremum of these partial sums gives
\[
 \liminf_{H\to\infty}\inf_{\mu\text{ on }R_H}
    \mathbb E\phi(X_H)\ge\mathbb E\phi(X_\infty).
\]
The uniform finite comb caps increase pointwise to the displayed infinite
caps, so monotone convergence supplies the reverse upper limit. Hence
\[
 \lim_{H\to\infty}\inf_{\mu\text{ on }R_H}
    \mathbb E\phi(X_H)=\mathbb E\phi(X_\infty),         \tag{HC7}
\]
including an infinite value on the right.

Thus changing a pure-coordinate marginal law while retaining only its
largest cylinder masses cannot give a fixed positive improvement in this
worst-case, unbounded-height comparison for any fixed increasing convex
cost. Multiplication by a fixed independent nonnegative auxiliary factor
preserves the needed convexity in this coordinate. This is not an
optimality claim about actual complete-layout loads, correlated head
laws, mixed-head union bounds, or height-dependent objectives. In
particular (CM1)'s improvement uses additional actual head information.

The certificate entry `comb_stoploss_dual_transport` constructs exact
primal and transport-dual witnesses for 84 objectives: \(p=3,5,7\),
\(2\le H\le8\), \(2\le j\le H\). It checks every depth budget and group
coverage with rational arithmetic. The all-height conclusions (HC5)--(HC7)
are the ordinary proofs above, with no new Lean declaration.

## Gap

The universal joint-load target Γ73 is false. The complete star family,
with ternary height at least 31 and every other height at least 8, has explicit
survivors but forces `Γ_Q(μ)>139.59>138.877` for every survivor probability,
including correlated and nonuniform laws. The unrestricted Erdős #7 problem
remains open. The conditional prime-tail transfer and height-lifting estimates
remain valid, as does the restricted noncoverage theorem; their proposed
universal head input and all eight displayed finite-base targets are refuted.
A proof of #7 therefore needs a sufficient input that this star family does
not contradict, rather than a sharper proof of the same universal inequality.
The finite-height pure-coordinate CRT criterion and its independent two-block
refinement give `lcm > 11486474` for every hypothetical cover, independently
of the external lcm theorem. This is a finite lower
bound and does not control the unrestricted large-lcm branches.

For the specified complete star assignment, (US1)--(US12) now exclude
**every** tail completion by primes above 73, at arbitrary positive head
heights. The actual broad-branch law, conditional convex comparison and an
exact positive-part calculation reach a supported prefix with `Gamma<4331`
at prime 2039. The BBMST stopping threshold there is greater than 4732, so
all later moduli are unrestricted. This resolves the star's noncoverage
without asserting the false universal `Gamma_73` bound. Other head geometries
remain open. The earlier graph and block-saturation estimates retain their
quantitative survivor-mass and crossing-budget conclusions for subclasses;
for example, matching tails leave more than one tenth of the broad-branch
head points with an uncovered tail lift.

For arbitrary `{3,5,7}` heads the same criterion also proves noncoverage
when all other primes are at least 37 and their interaction graph has
maximum degree at most two, or when all other primes are at least 31 and
each interaction component has at most three vertices. These restrictions
allow arbitrary exponents and arbitrarily many primes in total.

The stronger graph criteria also exclude arbitrary `{3,5,7}` heads with
arbitrary forest tails from prime 17, `2`-degenerate tails from prime 19,
and `5`-degenerate tails, including all planar graphs, from prime 23.
The `20`-degenerate star bound additionally gives an explicit saturated-head
mass estimate above 73. These graph estimates allow unbounded maximum degree,
total prime support, exponents, feedback vertex number and treewidth; the
star theorem (US1)--(US12) now removes their graph restrictions entirely.
For the finite heads supplied by the 5040 connection, the stronger
supported-law bounds additionally exclude every planar tail from prime 17
when the head divides 315, and from prime 19 when it divides 945.
For the other heads, the original-modulus support criterion (RK1)--(RK5)
removes all graph restrictions: arbitrary `{3,5,7}` heads permit at most
two tail primes per modulus from 23, and heads dividing 315 or 945 permit
at most three from 17 or 19 respectively. These conditions allow complete
tail graphs of unbounded size. Moreover, (RK6)--(RK8) impose those support
bounds only on moduli with largest prime at most 8192 for 315 and 945,
or 32768 for arbitrary 357. Above those cutoffs, each original modulus may
have arbitrarily many tail prime factors. The unrestricted-tail theorem (PH1)--(PH7) now removes
these support restrictions entirely for the three stated head and prime-gap
hypotheses. Thus every hypothetical cover must involve at least one of
11, 13, 17, 19; their unrestricted interaction is not settled here.
The star row is superseded as a noncoverage result by (US1)--(US12).

**H73 — false**, with its universal candidate statement retained from
[the target preregistration](https://github.com/the-omega-institute/trureturing/issues/8167):
let `Q` be any product of arbitrary finite powers of odd primes at most 73.
Choose one residue `a_d` for every divisor `d > 1` of `Q`, and let
`R = {x ∈ ℤ/Qℤ : x ≢ a_d (mod d) for every such d}` be the complete survivor
set. For a probability `μ` supported on `R`, define

\[
 c_\mu(d)=\max_{b\in\mathbb Z/d\mathbb Z}\mu\{x:x\equiv b\pmod d\},\qquad
 \chi(1)=1,\quad \chi(p^e)=2e+1,
 \qquad \kappa_Q(\mu)=\sum_{d\mid Q}\chi(d)c_\mu(d),
\]

with `χ` multiplicative. H73 asserted that for every `Q` and every such residue
assignment there exists such a probability with `κ_Q(μ) ≤ 138877/1000`.
The height-four instance proved in Evidence has an explicit survivor and forces
`κ_Q(μ) > 1621563/10000 > 138877/1000` for every survivor probability, including
correlated ones. One finite height refutes the arbitrary-exponent assertion.
H73 is therefore unavailable as a sufficient input; it was never an equivalent
restatement of #7.

**Γ73 — false**, preregistered at the same issue: for every
such `Q` and residue family, a probability `μ` on its complete survivor set `R`
satisfies

\[
 \Gamma_Q(\mu)=
 \max_{(b_d)_{d\mid Q}}\mathbb E_\mu
 \left[\left(\sum_{d\mid Q}\mathbf1_{x\equiv b_d\pmod d}\right)^2\right]
 \le\frac{138877}{1000}.
\]

The maximum is over **one joint choice** of residues: each `b_d ∈ ℤ/dℤ` is
chosen once for the whole square. Residues for different divisors need not be
mutually compatible. This candidate replaced the separate-cylinder
cost; it was not a consequence of H73's failure. A lower bound for `κ_Q` gives no lower
bound for `Γ_Q`. The conditional transfer and finite-height calibration below do not establish Γ73.
The stronger demand that this law always be uniform is false: the rectangular
family below has uniform `Γ>142.3789923` but admits a nonuniform law with
`Γ<134.121`. That rectangular example alone does not refute the existential target;
the star family does.

## Route

The joint-load invariant retains actual residue intersections. Its transfer
and the restricted noncoverage results are established below. The star-family
refutation identifies why the proposed universal head input fails. The
positive-part proof (US1)--(US12) nevertheless excludes all tail completions
of that precise head assignment, using a later supported prefix seed.

### A complete star family refutes the unrestricted Gamma-73 bound

Let P be the 20 odd primes at most 73. Choose H_3>=31 and H_p>=8 for
p>=5, and put Q=product_(p in P) p^H_p. There is one actual forbidden
residue for every nonunit divisor of Q, with a nonempty survivor set R,
such that every probability mu supported on R satisfies

    Gamma_Q(mu) > 13959/100 > 138877/1000.                  (1)

Here Gamma_Q(mu) is the maximum over all complete test layouts
b=(b_d mod d)_(d|Q) of the second moment of
L_b(x)=sum_(d|Q) 1[x=b_d mod d], including d=1. The counterexample concerns
this universal arbitrary-prime-power survivor-measure assertion. It does
not refute the odd distinct covering-systems conjecture: the family
below explicitly has survivors. The proof uses only coherent complete
layouts for its lower bound, while mu may have arbitrary correlations.

#### The actual complete forbidden assignment

In the CRT p-coordinate define, for 1<=e<=H_p,

    F_(p,e) = {x_p = p^(e-1)-1 mod p^e},
    C_(p,e) = {x_p = 2p^(e-1)-1 mod p^e},
    S_p = (Z/p^H_p Z) minus union_e F_(p,e),
    C_p = union_e C_(p,e),       D_p = S_p minus C_p.

For each pure-power divisor p^e forbid F_(p,e). For each divisor 3^i p^j
with p>=5 and i,j positive, forbid the unique CRT residue specifying
C_(3,i) and C_(p,j). For every other mixed divisor forbid zero. This
specifies exactly one residue for each distinct nonunit divisor. The
last classes are redundant: a zero mixed residue is already zero modulo
one of its prime factors, and F_(p,1) forbids zero modulo p.

Read digits from least significant to most significant. F_(p,e) has
first e-1 digits p-1 and next digit zero. C_(p,e) has the same prefix
and next digit one. Hence S_p consists of points whose first digit
different from p-1 belongs to {1,...,p-2}, together with the all-(p-1)
point. D_p has allowed first differing digits {2,...,p-2}, together with
that same exceptional point. All C_(p,e) lie in S_p. In particular,

    D_3={-1 mod 3^H_3},       S_3=C_3 disjoint-union D_3.

For each p>=5, the union of all star rectangles is exactly C_3 times C_p.
The actual complete survivor set consequently is

    R = R_a disjoint-union R_b,
    R_a = {-1 mod 3^H_3} times product_(p>=5) S_p,
    R_b = C_3 times product_(p>=5) D_p.                    (2)

There is no additional restriction from the remaining mixed divisors.
The CRT point x_3=1 and x_p=2 for p>=5 lies in R_b, so R is nonempty.

#### A constant-potential coordinate distribution

For x,t modulo p^h, let ell(x,t) be the largest e in {0,...,h} for which
x=t modulo p^e. The coherent coordinate kernel is

    J_(p,h)(x,t)=(1+ell(x,t))^2
      =1+sum_(e=1)^h (2e+1)1[x=t mod p^e].                (3)

For 1<=k<=p-1, let T_(p,k,h) contain points whose first digit different
from p-1 is in {p-k-1,...,p-2}, plus the all-(p-1) point. Define
u_h=v_h=0, and for r=h-1,...,0, with w_r=2r+3, set

    u_r=(w_r+u_(r+1))/p,
    v_r=[k/(w_r+u_(r+1))+1/(w_r+v_(r+1))]^(-1),
    V_(p,k,h)=1+v_0.                                      (4)

At a node on the distinguished all-(p-1) path at depth r, give each of
its k allowed side children probability v_r/(w_r+u_(r+1)); give its
continuing child probability v_r/(w_r+v_(r+1)). These probabilities are
positive and sum to one by (4). After taking a side child, choose all
remaining digits uniformly. Continuing children follow the same rule,
and the depth-h point terminates. This defines a finite probability
lambda_(p,k,h) supported on T_(p,k,h).

The expected remaining contribution of a uniform suffix is u_r. For
any fixed admissible point below a distinguished node, only the matching
child contributes beyond that node. If the point takes a side child,
its contribution is
[v_r/(w_r+u_(r+1))]*(w_r+u_(r+1))=v_r. If it continues along the
distinguished path, induction gives the identical value with v_(r+1)
in place of u_(r+1). Induction from depth h proves

    E_(t~lambda_(p,k,h)) J_(p,h)(x,t)=V_(p,k,h)
      for every x in T_(p,k,h).                           (5)

This is a distribution of test centers, not a chosen survivor law.
The general construction is formalized by
[RestrictedSpineConstantPotential.restricted_spine_constant_potential](../D5/S3/Arith/Congruence/RestrictedSpineConstantPotential.lean).
For any finite alphabet, a distinguished symbol excluded from its side set,
and any finite list of positive real layer weights, the theorem proves
nonnegativity, total mass one, support in the admissible words, and the exact
constant potential of the explicitly recursive test law. Empty words and an
empty side set are included. Taking weights `3,5,...,2h+1` supplies this tree
calculation; the word-to-residue embedding, CRT product, numerical threshold
and full star-family refutation are separate formalization obligations.

#### An exact depth-eight lower certificate

Take h=8 and

    B=V_(3,1,8) product_(p>=5) V_(p,p-3,8).

The ternary factor is for S_3; the other factors are for D_p. To bound
B using short integers, put M=10000 and initialize U_8=W_8=0. For
r=7,...,0 compute

    A_r=M(2r+3)+U_(r+1),   B_r=M(2r+3)+W_(r+1),
    U_r=floor(A_r/p),
    W_r=floor(A_r B_r/(A_r+k B_r)),
    m_p=M+W_0.                                            (6)

The functions a/p and ab/(a+kb) are increasing for positive a,b and
k>=1. Thus induction gives U_r<=M u_r, W_r<=M v_r, and
V_(p,k,8)>=m_p/M. Alternatively, every such inequality in this fixed
certificate is checked directly against the exact fractions from (4).

The integer table is

    p:    3     5     7    11    13    17    19    23    29    31
    m:44425 25593 17916 13925 13125 12215 11932 11539 11178 11092
    p:   37    41    43    47    53    59    61    67    71    73
    m:10897 10801 10761 10691 10607 10541 10522 10473 10445 10432.

Exact integer multiplication gives

    B >= product_p (m_p/10000)
      = 88201253955139641252118098948566841488891779660937472668777730852992559
        /625000000000000000000000000000000000000000000000000000000000000000000
      > 141.                                              (7)

The displayed rational is 141.12200632822342...; the full fraction
recurrence gives B=141.2182001288544... . No floating approximation is
used for any comparison in this proof or its certificate.

#### Two legal complete-layout distributions

A full CRT center t determines one coherent complete layout b_d=t mod d.
For every x,

    L_t(x)^2=product_(p in P) J_(p,H_p)(x_p,t_p).            (8)

This follows by factoring the complete divisor index; each p-coordinate
contributes exactly 1+ell(x_p,t_p). Test centers may be anywhere modulo
Q and are not required to survive the forbidden assignment.

For distribution Pi_a choose t_3=-1 modulo 3^H_3. For each p>=5 choose
t_p independently and uniformly among the integer representatives
1,...,p-1, regarded modulo p^H_p. If x is in R_a then its ternary kernel
is (H_3+1)^2. Also x_p is nonzero modulo p, so

    E_(Pi_a) J_(p,H_p)(x_p,t_p) >= 1+3/(p-1).

Independence of these explicitly chosen test coordinates yields

    E_(Pi_a) L_t(x)^2
      >= (H_3+1)^2 product_(p>=5) (p+2)/(p-1)
      >= 32^2 * 1796039511175/124554051584
      > 14336,                   x in R_a.                (9)

For Pi_b independently choose t_3 modulo 3^8 from lambda_(3,1,8), and
t_p modulo p^8 from lambda_(p,p-3,8) for p>=5; set all higher digits of
t to zero. If x is in R_b, its ternary depth-eight projection is in
T_(3,1,8) and every other depth-eight projection is in T_(p,p-3,8).
This remains true when the first non-(p-1) digit occurs after depth
eight: the projection is the allowed all-(p-1) point. Higher matches
can only increase (3), so (5), (7), and (8) give

    E_(Pi_b) L_t(x)^2 >= B > 141,       x in R_b.            (10)

These factorizations concern the test distributions; they impose no
independence condition on mu.

#### A pointwise dual bound for every survivor probability

Use the one fixed normalized layout distribution

    Pi=(1/100) Pi_a+(99/100) Pi_b.

For x in R_a, (9) gives E_Pi L_t(x)^2>143.36. For x in R_b, (10) gives
E_Pi L_t(x)^2>139.59. Nonnegative contributions from the other mixture
component were only discarded. By the exact decomposition (2), every
x in R satisfies the latter strict lower bound. Therefore for any
probability mu on R, finite sums can be interchanged to obtain

    Gamma_Q(mu) >= E_(t~Pi) E_(x~mu) L_t(x)^2
                = E_(x~mu) E_(t~Pi) L_t(x)^2
                > 13959/100 > 138877/1000.

This proves (1). Keeping the exact rational (7) yields the stronger
uniform certificate lower bound 139.7107862649412... for this same
mixture; no optimization of its weight is necessary.

#### Verification scope

`verify_star_survivor_obstruction.py` uses only the Python standard library and
explicit error checks that remain active under optimization. It
reconstructs all 20 exact fraction recurrences, independently checks
all pinned floor integers, verifies the rational product and both
mixture-branch bounds, and compares its full output with `star_survivor_obstruction_certificate.json`.
It constructs a full height-31/8 CRT witness and checks every pure and star
exclusion, with all remaining mixed-zero exclusions ruled out by its nonzero
prime coordinates. It also exhaustively checks the explicit leaf laws and their equal
potentials for five small trees, and checks actual complete forbidden
assignments against decomposition (2) on 11700 small-modulus points.
Those small checks are regressions; the ordinary induction and CRT
argument above prove the arbitrary-height statement. No full huge
survivor enumeration, numerical optimization, or Lean kernel
certification is claimed.

#### Irredundancy does not repair the universal head target

Delete all redundant mixed-zero classes, retaining only the pure classes and
star rectangles. This family has the same survivors and least common multiple
`Q`, and every retained class has an exclusive witness. For a star rectangle
`C_(3,i) × C_(p,j)`, choose those two coordinates inside the indicated cylinders
and every other coordinate equal to 2, which belongs to `D_q`. For a pure class
`F_(p,j)` with `p>=5`, choose the ternary coordinate equal to -1 and all other
outside coordinates equal to 2. For a pure ternary class choose every outside
coordinate equal to 2. The first-differing-digit descriptions prove that each
point belongs only to its designated retained class. Thus requiring an
irredundant forbidden family does not repair Γ73 when Gamma still indexes all
divisors of its least common multiple.

This irredundant family is not a minimal cover: it does not cover. A genuine
finite irredundant cover has an additional necessary fibre property. If
`p^H` is the full p-part of its period Q and x is an exclusive point of a class
of p-height H, the p points `x+kQ/p`, `0<=k<p`, must all be covered. No class
of smaller p-height can meet this fibre: its membership is invariant on the
fibre and it misses x. Each class of height H meets at most one fibre point,
so at least p distinct such classes must meet the fibre. In the star family,
for any `p>=5`, the pure `p^H` exclusive witness with ternary coordinate -1 gives a fibre
whose other p-1 points are uncovered. This necessary property applies to an
actual cover of the whole period; it cannot be imposed without proof on its
73-smooth head alone. For example, choose a new prime `q>73` and `H_3>=q`.
The q distinct odd moduli `3^i q`, `1<=i<=q`, with CRT residues
`-1 mod 3^i` and `i-1 mod q`, cover the entire exceptional ternary fibre
`x_3=-1 mod 3^H_3` as its q-coordinate varies. This explicitly fills a fibre
missed by the head. It is not a full cover: the ternary root `1 mod 3`
misses every one of these new classes.

The published essential-class constraints are stronger than merely counting
the children in this top fibre. [Lettl--Sun, Theorems 1.3 and
2.1](../Library/Arith/lettlsun2008cosets.md), imply that an essential modulus
`d_t` in a cover by `k` classes satisfies
`k >= 1 + sum_p v_p(d_t)(p-1)`. At a private point `a` of this class,
retain the original labels `j` whose prime-to-p part divides `a_j-a` but
whose whole modulus does not. Their weighted capacity obeys

\[
 \sum_j p^{-(v_p(d_j)-v_p(a_j-a)-1)}
 \ge v_p(d_t)(p-1).
\]

The integer ordinary-cover case of the first bound is attributed to
Znám (1975). These public results require a cover of the full period;
they give no such inequalities for an isolated noncovering head.

### Complete star heads cannot be completed by arbitrary odd tails

**Theorem.** Let `P` be any subset of the odd primes at most 73 containing
3, and let `H_p>=1` for every `p in P`. Put `Q=prod_(p in P) p^H_p` and
use precisely the complete star forbidden assignment defined above on all
nonunit divisors of `Q`. Consider any finite family of additional classes
such that all moduli in the combined family are distinct and odd. Each
additional modulus has head part dividing `Q`, has a nonunit tail part,
and has all tail prime factors greater than 73. The combined family does not cover
the integers. There is no restriction on the number of tail primes in
one modulus, their exponents, the total number of primes, or the tail
interaction graph. The heights `H_p` resolve the entire original family,
including the head parts of classes whose largest prime occurs later.

The proof uses the actual broad-branch survivor law, the conditional convex
comparison in [Schroeder, Section 3](../Library/Arith/schroeder2026noncoverage.md),
a finite exact positive-part calculation, and
[BBMST, Theorem 6.1](../Library/Arith/balister2018covering.md).
It is an ordinary mathematical proof with an exact numerical certificate.
The unrestricted Erdős problem still allows arbitrary head assignments.

#### One actual head law at every positive height

Retain exactly the sets `C_3` and `D_p` in (2), and take

\[
 R_b=C_3\times\prod_{p\in P\setminus\{3\}}D_p,
 \qquad \mu_{\rm head}=\operatorname{Unif}(R_b).
 \tag{US1}
\]

This product law is supported on actual complete head survivors. In
particular, every mixed-zero head class is already excluded by a pure
class. The coordinate densities and resulting cylinder caps are

\[
 s_3=\frac{1-3^{-H_3}}2,\qquad
 s_p=\frac{p-3+2p^{-H_p}}{p-1}\quad(p\ge5),\qquad
 \mu_p\{x_p=b\bmod p^e\}\le\frac{p^{-e}}{s_p}.
 \tag{US2}
\]

All these densities are positive. For `p>=5`, use the height-independent
cap `c_p p^-e`, where `c_p=(p-1)/(p-3)`. The finite ternary cap needs a
separate argument; replacing it pointwise by `2*3^-e` would be invalid.

After applying conditional comparison and completing the divisor labels,
the ternary auxiliary height `K_(3,H)` has tails

\[
 \Pr(K_{3,H}\ge e)=\frac{2\,3^{-e}}{1-3^{-H}}\quad(1\le e\le H),
 \qquad \Pr(K_{3,H}>H)=0.
\]

Let `K_3` instead have tail `Pr(K_3>=e)=2*3^-e` for every `e>=1`.
For an increasing convex function `phi` on the nonnegative integers, its
increments `Delta_e=phi(e)-phi(e-1)` are nonnegative and nondecreasing.
With `w_e=2*3^-e`, the tail-sum identity gives

\[
 \mathbb E\phi(K_{3,H})=\phi(0)+
 \frac{\sum_{e=1}^H w_e\Delta_e}{\sum_{e=1}^H w_e}
 \le\phi(0)+\sum_{e\ge1}w_e\Delta_e
 =\mathbb E\phi(K_3).                                 \tag{US3}
\]

Here `sum_(e>=1) w_e=1`, and the truncated weighted average uses only
the smallest increments. Both heights have mean 1. For any fixed
`z>=1`, both functions `phi(k)=h(z(1+k)-1)` and
`phi(k)=h(z(1+k))` are increasing convex whenever `h` is. This is the
specific convex-order replacement used below, after auxiliary independence
has been established. For other head primes, the finite auxiliary heights
are directly stochastically bounded by independent `K_p` with tails
`Pr(K_p>=e)=c_p p^-e`. Adding omitted head primes as independent factors
`1+K_p>=1` only increases the completed loads.

#### Normalized tail kernels preserve the original labels

Process tail primes in increasing order, with `delta=2/5` through the
finite stopping prime. Each prime-power coordinate has the full height
appearing anywhere in the original family. First let `U_q` be uniform on
the actual survivors of all pure `q`-power classes. Distinct moduli and
`sum_(e>=1) q^-e=1/(q-1)` show that this is a probability, with

\[
 U_q\{y=b\bmod q^e\}\le\frac{q-1}{(q-2)q^e}.
\]

Assign every other class with a nontrivial tail part to its largest tail
prime `q`. Given the entire earlier history, let `B_q` be the actual
union of its active `q`-cylinders, and put `alpha_q=U_q(B_q)`. The BBMST
kernel relative to `U_q` has densities

\[
 \frac{1}{1-\min(\alpha_q,\delta)}\quad\text{off }B_q,
 \qquad
 \frac{(\alpha_q-\delta)_+}{\alpha_q(1-\delta)}
       \quad\text{on }B_q,                            \tag{US4}
\]

with the latter defined to be zero when `alpha_q=0`. Each row integrates
to one and is bounded by `1/(1-delta)`, including a completely forbidden
fibre. Thus future kernels preserve every prefix marginal. The final
probability of this assigned mixed union is exactly
`E(alpha_q-delta)_+/(1-delta)`, and every pure-tail class has probability
zero. There is no conditioning on survival during these steps. The
conditional cylinder caps at each earlier tail prime `p` are consequently
`c_p p^-e`, where

\[
 c_3=2,\qquad c_p=\frac{p-1}{p-3}\ (5\le p\le73),
 \qquad c_p=\frac{p-1}{(p-2)(1-\delta)}\ (p>73).
 \tag{US5}
\]

The value `c_3=2` is only the auxiliary value after (US3). The actual
head law always retains its finite-height cap from (US2). Head coordinates
are initially independent, and all the stated tail caps hold conditional
on the entire earlier history under the same normalized law.

Write each original modulus assigned to `q` as `d q^e`, with `d>1` an
old cofactor, retaining its actual old residue as part of that original
label. Set `w_e=(q-1)/q^e`. The uniform-pure-survivor bound gives

\[
 \alpha_q\le\frac{R_q}{q-2},\qquad
 R_q=\sum_{\text{original labels }d q^e}
        w_e\,\mathbf1_{\text{actual old cylinder}}.     \tag{US6}
\]

At fixed `d` and `e` there is at most one label because the original
moduli are distinct. Different original moduli can have the same projected
cofactor `d`; no distinctness of such projections is asserted.

Schroeder's Section 3 proposition **Conditional comparison**, source label
`prop:comparison`, applies to any finite family of weighted coordinate
rectangles. If their coordinate events `A_(label,p)` have deterministic
caps conditional on the entire past, it bounds the expectation of every
nonnegative increasing convex function of their load by the corresponding
load formed from independent uniforms, one common uniform per coordinate.
The sets and residues may depend on the whole modulus label. Its proof
replaces coordinates in reverse order by increasing supermodular
rearrangement. It does not require the actual events to be nested or the
actual coordinates to be independent.

Apply it to (US6) with `h(u)=(u-(q-2)delta)_+`. In the compared load,
`d=prod p^a_p` is active exactly when `a_p<=K_p` for every old prime.
For each fixed cofactor, `sum_e w_e<=1`. Completing all nonunit cofactor
labels therefore bounds this load by `D_q-1`, where

\[
 D_q=\prod_{3\le p<q\atop p\ \text{prime}}(1+K_p).
\]

First complete within the actual finite heights, then apply (US3) and
extend the other auxiliary heights. Monotone convergence permits this
nonnegative completion; the moments displayed below are finite. The
subtraction of 1 excludes the unit cofactor, whose classes were already
removed as pure powers. Hence the actual mixed-union probability is at most

\[
 b_q=\frac{\mathbb E\bigl(D_q-1-(q-2)\delta\bigr)_+}
              {(q-2)(1-\delta)}.                      \tag{US7}
\]

This is the positive-part estimate in the proof of Schroeder's Section 8
**Unrestricted second-moment charge**, before its quadratic relaxation,
with the head caps supplied by (US1)--(US3). No restriction on a modulus's
tail support was used.

#### A simultaneous complete-layout moment under the same law

For any complete test layout on the enlarged prefix modulus through `B`,
apply the same conditional comparison with `h(u)=u^2`, keeping each test
modulus and its own residue as an individual label. The completed load is
bounded by `D=prod_(3<=p<=B)(1+K_p)`. Formula (US3) applies here with
`phi(k)=(z(1+k))^2`. Consequently every complete layout has second moment
at most

\[
 J_B=\mathbb E D^2
   =\prod_{3\le p\le B\atop p\ \text{prime}}
       \left(1+c_p\frac{3p-1}{(p-1)^2}\right).          \tag{US8}
\]

Indeed, the tail formula gives
`E(1+K_p)^2=1+sum_(e>=1)(2e+1)c_p p^-e` and the displayed geometric sum.
The head product through 73 is exactly the existing `K_0<177` in (BS6).
Auxiliary independence factors `J_B`; no tensorization assertion about
actual-layout `Gamma` is needed.

Put `charge_B=sum_(73<q<=B) b_q`. The actual law constructed by (US4) is
already supported on head survivors and pure-tail survivors. The union
bound and preservation of assigned-event probabilities show that its
event `E` of avoiding every prefix class has mass
`lambda>=1-charge_B`. When `charge_B<1`, condition this law **once** on
`E`. For every complete layout, its load `L` includes the unit divisor,
so `L^2>=1` everywhere. Thus the resulting law is supported on actual
prefix survivors and simultaneously satisfies

\[
 \Gamma\le1+\frac{J_B-1}{\lambda}
          \le G_B:=1+\frac{J_B-1}{1-\operatorname{charge}_B}.
 \tag{US9}
\]

The event bound and `J_B` belong to this same preconditioning law; they
are not combined from separately optimized measures.

#### Exact positive-part certificate and the BBMST stop

Take `B=2048`, whose last prime is 2039 and whose global prime index,
counting 2, is `k=309`. Absent primes can be included as unused coordinates;
this does not change actual noncoverage and only enlarges the nonnegative
auxiliary bounds. There are 288 processed tail primes between 73 and `B`.
The [existing exact verifier](../docs/reports/erdos7-odd-covering/verify_star_block_obstruction.py)
recomputes the entry `unrestricted_star_stoploss` in its
[certificate](../docs/reports/erdos7-odd-covering/star_block_obstruction_certificate.json).

Here is its directed calculation. Use scale `S=10^18` and store the
probabilities of all integer product states `1<=d<=819`. The multiplier
`f=1+K_p` has atom probabilities

\[
 a_1=1-\frac{c_p}{p},\qquad
 a_f=\frac{c_p(p-1)}{p^f}\quad(f\ge2).
\]

Starting with `W_1=S` and all other `W_d=0`, round every `a_f` upward to
`A_f/S`, and update

\[
 W'_d=\left\lceil\frac{\sum_{f\mid d}W_{d/f}A_f}{S}\right\rceil.
\]

Induction gives `W_d/S>=Pr(D=d)`: every coefficient is nonnegative.
Multipliers greater than 819 cannot enter a retained state because all
multipliers are at least 1. Their moments are not discarded. Separately
propagate upper bounds for `E D` and `E D^2` by multiplying, respectively,
by the exact positive factors
`1+c_p/(p-1)` and `1+c_p(3p-1)/(p-1)^2`, rounding each result upward on
the same grid. The independent prime-list check uses trial division.

Before processing `q=p`, put `T=1+(p-2)delta=(2p+1)/5`. The exact identity

\[
 \mathbb E(D-T)_+=\mathbb E D-T+
        \sum_{d\le T}(T-d)\Pr(D=d)                    \tag{US10}
\]

has nonnegative coefficients on the approximated mean and low-state
probabilities. If `M/S` is the stored mean bound, then rounding

\[
 \frac{5M-(2p+1)S+
       \sum_{d\le\lfloor T\rfloor}(2p+1-5d)W_d}{3(p-2)}
\]

upward gives an upper bound for `S b_p`. The largest queried state is
815 at `p=2039`, within the 819 retained states. All 288 step charges,
the final moments and the final low-state digest are recomputed; the
digest is not a mathematical input. Exact arithmetic yields

\[
 \operatorname{charge}_B\le
 \frac{197210774016889569}{500000000000000000}<1,\qquad
 J_B\le\frac{2622709946291465704821}{1000000000000000000},
\]
\[
 G_B\le\frac{2622315524743431925683}{605578451966220862}
       <4331<4732<\frac{10350367}{2187}.                \tag{US11}
\]

For the stopping threshold, the first two positive `atanh` terms give
`log 2>=56/81`. Since `k=309>=256`, this implies
`log k>=448/81>4` and `log log k>=log 4>=112/81`. Therefore

\[
 k(\log k+\log\log k-3)^2
 \ge k\left(\frac{317}{81}\right)^2
 =\frac{10350367}{2187}>G_B.                           \tag{US12}
\]

The exact margin between the final rational threshold and the certified
`G_B` is `532955172528371903287633/1324400074450125025194>0`.

Restart the joint-load transfer (T1)--(T6) from the normalized actual
survivor law in (US9). Its initial budget is at most `G_B`, with positive
survivor mass, and (US12) is precisely the sufficient stopping inequality
of BBMST Theorem 6.1. That theorem's recurrence continues with the standard
uniform-base kernels for all later primes; the earlier pure-survivor base
is not assumed for this continuation. Its prime index is the full global
index `309`, including absent primes and 2. If the family ends before
the stop, its already positive prefix-survivor mass suffices. Otherwise
the BBMST continuation retains positive survivor mass through every
remaining prime. Finite CRT then produces an integer avoiding the whole
original family, proving the theorem.

The conditional comparison and BBMST continuation are published ordinary
proofs; the changed head input, finite-height convex-order argument,
same-law conditioning and exact finite charge are the deductions here.
The audited upstream Lean theorem still assumes at most three prime factors
per modulus and does not certify this extension. The local Lean result
in (DG2) proves the selected-coordinate cylinder step, not this entire
unrestricted-tail star theorem. The graph and bounded-support star bounds
below remain quantitative refinements for their respective subclasses.

### Arbitrary cross-point 11/13 heads and full-height continuation

A further noncoverage theorem permits both 11 and 13 at arbitrary finite
heights. Let the full `{3,5,7}` part of every original modulus divide 315,
and choose the canonical supported 315 law. At every point in its support,
suppose the active classes d·11 forbid at most one first 11-digit and the
active classes d·13 forbid at most one first 13-digit, for d|315. Then the
family cannot cover. All twelve possible d·143 classes may have arbitrary
residues, and the later prime heights and interactions are unrestricted.

The [degree-weighted grid proof](../docs/reports/erdos7-odd-covering/marked_head_profile.md#arbitrary-point-holes-and-a-common-diagonal)
allows arbitrary point-hole patterns in each available 10-by-12 rectangle,
including a whole row deleted by cross classes. The number of actual holes
has mean at most 271/86. Retaining its correlation with old complete test
loads gives the same full-height supported law both a square bound
`51464038499033/2027599359660` and a complete convex comparator of mean
`46851298771/11264440887`. The mean belongs to the comparator and is not
asserted to equal the actual maximum old-load mean.

The fixed 414-step certificate ends at 2903, global prime index 420:

    survivor mass >= 44564898975571389/250000000000000000,
    Gamma <= 1751428432885843299077/178259595902285556
          < 9826 < 9833 < 420(log420 + loglog420 - 3)^2.

AP2–AP6 and the existing BBMST transfer finish every later prime. The
previous single-hole result remains a quantitative refinement with its
258-step certificate. The full-family 315 height restriction and the
first-power axis restrictions remain genuine hypotheses. This is an
ordinary theorem with exact arithmetic, not unrestricted Erdős #7 or
an end-to-end Lean proof.

The unnormalized weighted grid component is formalized by
`D5.S3.Arith.Congruence.ArbitraryHoleGram.degree_reweighted_grid_second_moment_le`
in [ArbitraryHoleGram.lean](../D5/S3/Arith/Congruence/ArbitraryHoleGram.lean),
for arbitrary finite axes of size at least three and arbitrary hole
relations under its small-perturbation hypothesis. The normalization,
arithmetic head integration and tail conclusion remain ordinary proofs;
the zero-perturbation extension to smaller axes below is also an ordinary
Laplacian argument.

### Unrestricted axis deletions: a complete head bound

The [variable-rectangle construction](../docs/reports/erdos7-odd-covering/marked_head_profile.md#unrestricted-axis-deletions-and-the-optimal-scalar-clipped-bound)
removes the preceding axis restrictions at the level of the supported
head bound. For every family of distinct nonunit moduli dividing
`315·11^H·13^J`, with arbitrary finite `H,J≥1`, it constructs one complete
survivor probability satisfying

    Gamma <= 42723250051/1147550665 < 37.230.

No restriction on the number of deleted rows, columns, point holes, or
empty old fibres is imposed. The full `{3,5,7}` part must still divide 315.

If `A,B,D` are the three complete old loads dominating the original axis
and cross-point activation counts, the number of remaining first-digit
cells is at least `S=[(11-A)_+(13-B)-D]_+`. This retains the actual
rectangular overlap. The clipped subprobability law has old row mass
`min(1,C·S_actual/120)` and density at most `C` relative to the uniform
ten-by-twelve reference law. Empty fibres receive zero mass.

At `C=40/31`, the exact marginal-profile bound for the low surviving mass
is `74101/97929`. Uniform higher digits and the distinct original-label
count give higher deleted mass at most `24119/319920`, leaving mass at
least `229510133/336875760`. The weighted old square and the minimum-load
deletion saving yield the displayed complete head bound.

The same supported law has a full increasing-convex comparator: take
the upper `229510133/434678400` quantile of `X·N11·N13`, where `X` is the
published old 315 comparator and the independent auxiliaries have
`Pr(Np=1)=(p-2)/(p-1)` and `Pr(Np=k)=p^(1-k)` for `k≥2`. Its boundary is
at 3 and its exact mean is `1263555626/229510133`. This comparison mean
does not assert equality with the actual maximum head-load mean. At
heights `H=J=1`, the same clipping constant gives the stronger square
bound `99014608/3186343 < 31.075`.
The same law also satisfies the sharper actual first-moment bound
`1242116000/229510133 < 5.413`, by retaining the old marginal cap and
the unit-load saving during deletion. This is distinct from the
comparison distribution’s larger mean.

The certificate also settles the scalar clipping parameter globally.
A linear-fractional transformation gives one linear program with 30
variables and 3458 constraints, using every old marginal hinge bound
and the sharp square bound. Exact primal-dual equality proves that
`C=40/31` minimizes the all-height square certificate over every `C≥1`
with a positive certified denominator. This is optimality within the
specified marginal-information relaxation, not optimality among actual
survivor laws. Further improvement requires information omitted by that
certificate, such as weighted old test energy.

Retaining the [common old shape and actual survivor count](../docs/reports/erdos7-odd-covering/marked_head_profile.md#retaining-the-common-old-shape-and-survivor-count)
sharpens the same construction at the same `C=40/31` to

    Gamma <= 2167128283/58962460 < 36.755,
    sup_test E_nu L <= 24790300/4595881 < 5.395.

All test and activation loads share one of the six canonical 45 shapes
and the same actual 315 survivor count. The verifier recomputes all
27,720 old layouts and 144 common branches. At fixed deletion count,
the original cofactor cylinders lower-bound deleted load energy; the
existing five-term area inequality then applies with that branch's
mean, square and hinge bounds. The actual local rectangle's Gram diagonal
further saves `(9G+19)/496` from the square numerator: its clipping
density and surviving axis counts obey simultaneous coefficient bounds,
and each complete old block load is at least one. The 1372 possible
nonempty rectangle count triples are checked exactly. The square maximum is at the first shape
with 81 survivors. The same law admits the upper `68561/129600` quantile
of `X·N11·N13` as a full increasing-convex comparator, with boundary 3
and mean `1264886009/229953594`. These stronger bounds preserve the
full `315·11^H·13^J` scope and do not assert a new tail continuation.

The [actual rectangle hinge profile](../docs/reports/erdos7-odd-covering/marked_head_profile.md#actual-rectangle-hinge-bounds-on-the-same-law)
additionally bounds the complete test-load hinges on this same law at
all integer thresholds from 4 through 12. With the joint-cost refinement,

    Theta_nu(6) <= 321137/403528 < 4/5.

Convex concentration and the sum of the largest surviving-count cell
loads give a geometric upper envelope with the actual clipping
denominator. Nine rational duals are checked by 26,078,976 integer
inequalities; a point-load endpoint argument covers the full finite
domain, and empty fibres are checked separately. Their averages use
only the existing old-shape and survivor-count bounds. The actual
mixed-hole count is bounded by its old activation load, and the
higher-exponent contribution and normalization retain the same one
of 144 branches. The new `actual_rectangle_hinge_profile` certificate
field stores every dual and the full-height bounds at thresholds
4--12. The entries additionally use the joint-cost refinement below. The
first prime-17 query in (AP2) at threshold 6 therefore costs at most
`321137/4035280`. Adjacent-knot interpolation is a valid
pointwise upper bound; the resulting curve is not asserted to be a
probability comparator. This is an ordinary exact-arithmetic result,
not a new Lean theorem or a completed unrestricted-tail certificate.

These results remove the axis hypothesis for the finite head estimate.
They do not supply the unrestricted-tail stopping certificate needed
to remove that hypothesis for every old configuration. The particular
96-point configuration in (BT1)--(BT8) does have a complete unrestricted-tail
certificate with arbitrary axis and point exclusions.

The fixed-count labelled deletion refinement now closes the finite-head
threshold-six target. On the first 17-point old shape, the five mixed-seven
labels are grouped by their nonzero seven digit; each group deletes a union
of its labelled old-cylinder sets. An anchored partition recurrence over
these unions gives exact deleted-cost lower bounds. Of 4,760 old-45 layouts,
only 72 and 120 require the exact recurrence for the two sharpened costs;
the resulting numerator caps at survivor counts 80, 81 and 82 are
`(1986,1986,1992)` and `(728,728,732)`. Applying those caps to the existing
144 branch transfer gives

    Theta_nu(6) <= 26114497/32685768 < 4/5,

with unique worst branch `root1_same_other_column`, 79 survivors. This is
an ordinary exact finite-head calculation for arbitrary finite 11/13 heights,
not a Lean theorem or an unrestricted-tail conclusion.

Keeping each whole convex cost on a single old layout and its labelled
deletion configuration further improves seven of the nine hinge bounds.
The `joint_cost_hinge_refinement` certificate recomputes 32 normalized costs
on all 27,720 layouts and 144 shape/count branches, yielding the stronger
`Theta_nu(6)<=321137/403528`, with the same worst branch N=79. It uses the
existing cheap deletion lower bounds for the whole cost and retains the
exact three-branch partition caps above. All higher-load and normalization
terms stay on the same branch. The result proof and integer numerator
bounds are retained in the [whole-cost derivation](../docs/reports/erdos7-odd-covering/marked_head_profile.md#whole-convex-costs-on-one-old-layout-and-deletion-configuration).

The [signed-conditioning obstruction](../docs/reports/erdos7-odd-covering/marked_head_profile.md#actual-obstruction-for-uniform-conditioning-and-its-signed-bound)
gives a complementary boundary. An actual family containing all 47
nonunit divisors of 45045 has 6872 survivors and forces
`Γ≥88555/3436` for its uniformly conditioned reference law. Its signed
sufficient criterion cannot certify a value below `192443/6473`.
These are different statements: the second number is not an actual
moment lower bound, and neither excludes other supported laws.

### A continuation criterion for an arbitrary correlated head

Let \(Q\) be a finite odd head period and let \(\mu\) be one fixed
probability supported on its actual survivors. It need not be uniform or a
product law. Every original modulus is a distinct nonunit divisor of
\(Q\prod_p p^{H_p}\), with odd tail primes coprime to \(Q\); all physical
heights resolve the entire original family, including later classes.
A complete head test layout chooses one residue for every divisor of
\(Q\), including the unit divisor. With its load denoted by \(L\), define
\[
 \Theta_\mu(t)=\max_L\mathbb E_\mu(L-t)_+\quad(t\ge0),
 \qquad G\ge\Gamma_Q(\mu)=\max_L\mathbb E_\mu L^2.       \tag{AP1}
\]
The maximum is over finitely many layouts, all fixed before sampling the
head point. The bound \(\Theta_\mu(t)\le G/(4t)\) for \(t>0\) is valid, but
retaining the profile can give a stronger continuation than this relaxation.

At every tail prime \(p\), use the normalized kernel (US4) relative to the
uniform law on its actual pure-power survivors, with \(0<\delta_p<1\).
Assume
\[
 c_p=\frac{p-1}{(p-2)(1-\delta_p)}\le p.
\]
The full-history conditional cylinder cap is \(c_pp^{-e}\). This condition
makes the following unclipped auxiliary height law a probability:
\(\Pr(K_p\ge e)=c_pp^{-e}\) for \(e\ge1\). Choose these heights independently
of each other and of the head point. If \(c_p>p\), clipped tails and their
recomputed moments are needed; the formulas below cannot be retained as stated.
For the current tail prime \(q\), put
\[
 N_q=\prod_{\text{tail }p<q}(1+K_p),\qquad
 T_q=1+(q-2)\delta_q,\qquad d_q=(q-2)(1-\delta_q)>0.
\]
Then its actual assigned mixed-union probability is at most
\[
 b_q=\frac{\mathbb E_K[N_q\Theta_\mu(T_q/N_q)]}{d_q}.    \tag{AP2}
\]

**Original labels and the single missing unit cofactor.** Fix a head point
\(x\). Apply [Schroeder's conditional comparison](../Library/Arith/schroeder2026noncoverage.md)
only to the old tail coordinates. Keep each original modulus
\(m\tau q^e\) as its own label, where \(m\mid Q\) and \(\tau\) is the old
tail cofactor, with weight \(w_e=(q-1)q^{-e}\). Its actual head-cylinder
indicator is a fixed nonnegative coefficient at \(x\). The conditional
tail caps hold for the entire earlier history including \(x\), and do
not depend on \(x\); the auxiliary comparison uniforms may therefore be
chosen independently of \(x\) when integrating against \(\mu\).

For each full tuple \((\tau,e)\), original-modulus distinctness gives at
most one residue for each head divisor \(m\). Complete that partial head
layout to \(L_{\tau,e}\), choosing all missing residues in advance,
independently of \(x\). Fix such completions also for missing tuples and
depths. After comparison, exactly \(N_q\) auxiliary tail tuples are active,
including the unit tuple; tuples beyond a physical height add only
nonnegative completion terms. Index their completed head layouts by \(j\).
Pure \(q\)-power classes were already removed. Thus the pair consisting of
the unit tail tuple and unit head modulus is absent from the mixed load,
and completion of every current depth, using \(\sum_{e\ge1}w_e=1\), gives
\[
 R_q^{\rm compared}\le
       \sum_{j=1}^{N_q}\sum_{e\ge1}w_eL_{j,e}(x)-1.     \tag{AP3}
\]
The subtraction is exactly \(1\), not \(N_q\): a nonunit tail cofactor
with unit head factor is a legitimate original mixed label. Completing
missing current depths is necessary to subtract the full \(1\).

For fixed auxiliary heights the weights \(w_e/N_q\), indexed by \((j,e)\),
sum to one. The head loads are bounded by the divisor count of \(Q\), so
countable Jensen gives
\[
 \begin{aligned}
 \mathbb E_\mu\left(\sum_{j,e}w_eL_{j,e}-T_q\right)_+
 &\le\sum_{j,e}\frac{w_e}{N_q}
                 \mathbb E_\mu(N_qL_{j,e}-T_q)_+\\
 &\le N_q\Theta_\mu(T_q/N_q).
 \end{aligned}                                        \tag{AP4}
\]
The pure-survivor cylinder bound gives
\(\alpha_q\le R_q/(q-2)\). Combining (AP4) with the actual kernel's
violation formula \(\mathbb E(\alpha_q-\delta_q)_+/(1-\delta_q)\)
proves (AP2). No projected-modulus distinctness or actual nestedness is used.

**A moment and survivor bound for the same actual law.** Let \(\nu_B\)
be the law after a finite tail prefix through \(B\), without intermediate
conditioning. Group any complete fine test layout by its full tail
exponent tuple. Each group is a complete head layout fixed before \(x\)
is sampled. Tail-only comparison with the square function bounds its
aligned load by \(\sum_{j=1}^{N_B}L_j(x)\), where
\(N_B=\prod_{\text{tail }p\le B}(1+K_p)\). Jensen yields
\[
 \mathbb E_\mu\left(\sum_jL_j\right)^2
 \le N_B\sum_j\mathbb E_\mu L_j^2\le G N_B^2.
\]
This is uniform over all fine layouts under the same law \(\nu_B\), hence
\[
 \Gamma(\nu_B)\le J_B:=G\mathbb E N_B^2
 =G\prod_{\text{tail }p\le B}
       \left(1+c_p\frac{3p-1}{(p-1)^2}\right).          \tag{AP5}
\]
This follows from comparison and Jensen, without a Gamma tensorization
identity for the correlated head law. If \(C_B=\sum_{\text{tail }q\le B}b_q<1\), the
actual event \(E_B\) avoiding every prefix class has mass
\(\lambda\ge1-C_B>0\). The head and pure-tail classes already have zero
violation probability. Since every complete load has \(L^2\ge1\),
conditioning once gives a supported law satisfying
\[
 \Gamma\bigl(\nu_B(\,\cdot\mid E_B)\bigr)
 \le1+\frac{J_B-1}{1-C_B}.                             \tag{AP6}
\]
For BBMST continuation, require all head primes to be at most \(B\), retain
the full physical heights, and count every prime, including absent primes
and \(2\), in \(k=\pi(B)\). If \(k\ge10\) and the right side of (AP6) is
at most \(k(\log k+\log\log k-3)^2\), (T1)--(T6) and BBMST Theorem 6.1
exclude coverage by the entire family. The supported law may be correlated
and may have a different head marginal after this single conditioning.

**An exact finite low-state identity.** Put
\(M=\Theta_\mu(0)=\max_L\mathbb E_\mu L\), using its exact value.
Because \(L\ge1\), one has \(\Theta_\mu(t)=M-t\) for \(0\le t\le1\);
also \(\Theta_\mu(t)\ge M-t\) for every \(t\ge0\).
For a positive integer-valued \(N\) of finite mean and \(T>1\), splitting
at \(N\ge T\) therefore gives
\[
 \mathbb E[N\Theta_\mu(T/N)]
 =M\mathbb E N-T+
   \sum_{1\le n<T}\Pr(N=n)
      \underbrace{\bigl[n\Theta_\mu(T/n)-Mn+T\bigr]}_{\ge0}.
                                                               \tag{AP7}
\]
The sum is finite. For (AP2),
\(\mathbb E N_q=\prod_{\text{tail }p<q}(1+c_p/(p-1))\).
Thus each finite-prefix charge requires only this mean, finitely many
low-state probabilities and finitely many head-profile values. With the
exact \(M\), certified upper profile values yield nonnegative upper
corrections, so upward mean and probability bounds give a safe directed
bound. An unknown or rounded upper bound for \(M\) cannot be substituted
while retaining either equality (AP7) or its asserted nonnegative
corrections: the negative occurrences of \(M\) must also be justified.

For the complete-star broad law, (US1)--(US3) and conditional comparison
give \(\Theta_\mu(t)\le\mathbb E(D_{\rm head}-t)_+\) and
\(G\le\mathbb E D_{\rm head}^2\). Independence of the head auxiliaries
and \(N_q\) then reduces (AP2) to the positive-part bound for
\(D_{\rm head}N_q\) already certified in (US7)--(US12). That application
is complete. For arbitrary head geometry, constructing a supported law
with a sufficiently small profile to satisfy (AP2), (AP5) and (AP6)
remains a separate obligation. The criterion alone supplies no such
universal law; a lower bound on Gamma alone does not refute its existence.
This is an ordinary continuation proof, not a new Lean theorem.

### Block saturation and the actual crossing budget

Let `D` be a finite set of distinct odd moduli greater than one, with actual
residues `a_d`, and let `N=lcm(D)=QT`, where `gcd(Q,T)=1`. Use the actual
head survivors `R_Q`, obtained by removing exactly the classes with `d|Q`,
and suppose a probability `mu` supported on `R_Q` is given. Partition the
primes of `T` into arbitrary finite nonempty blocks `B`, and set
`T_B=prod_(q in B) q^(v_q(N))`. Empty tail support is allowed: all block
sums are then empty. Write `d=m_d t_d` with `m_d|Q`, `t_d|T`, and put
`h_d(x)=1[x=a_d mod m_d]` (identically one when `m_d=1`).

A tail class is local to `B` when `t_d>1` and its entire prime support
lies in `B`; otherwise it is crossing if it meets two or more blocks.
For each head point, let `U_B(x)` be the union of the actual local tail
cylinders whose head incidence is one. All original labels are retained:
different head labels can have the same projected tail modulus. Define

\[
 \alpha_B(x)=\frac{|U_B(x)|}{T_B},\qquad
 A_B=\mathbb E_\mu\alpha_B^2.
\]

For a crossing class put `t_(d,B)=gcd(t_d,T_B)` and, when this is greater
than one, define the remaining cylinder fraction

\[
 r_{B,d}(x)=\frac{|\{y\bmod T_B:y\equiv a_d\pmod{t_{d,B}}\}
                    \setminus U_B(x)|}{T_B}
 \le\frac1{t_{d,B}}.
\]

For thresholds `0<delta_B<1`, set

\[
 E=\sum_B\frac{A_B}{\delta_B^2},\qquad
 J=\sum_{d\text{ crossing}}\mathbb E_\mu
       \left[h_d\prod_{B:t_{d,B}>1}\frac{r_{B,d}}{1-\delta_B}\right].
 \tag{BS1}
\]

**Block criterion.** If `E+J<1`, the system does not cover. A sufficient
upper bound for `J` is

\[
 J_{\rm raw}=\sum_{d\text{ crossing}}
 \frac{\mu(h_d=1)}{t_d\prod_{B:t_{d,B}>1}(1-\delta_B)}.
 \tag{BS2}
\]

If there are no crossing classes, the stronger endpoint bound is

\[
 \mu\{x:\text{the tail fibre at }x\text{ has an uncovered point}\}
 \ge 1-\sum_B A_B.                                      \tag{BS3}
\]

**Proof.** On `G={x:alpha_B(x)<=delta_B for every B}`, every local
complement is nonempty. Markov's inequality and a union bound give
`mu(G)>=1-E`. For a fixed `x in G`, choose the block coordinates
independently and uniformly on their respective local complements.
The conditional probability of a crossing class is exactly

\[
 h_d(x)\prod_{B:t_{d,B}>1}\frac{r_{B,d}(x)}{1-\alpha_B(x)},
\]

and is bounded by its integrand in (BS1). Keep `mu` restricted to `G`
**unnormalized**; the resulting head-and-tail measure has mass at least
`1-E`. Summing the crossing probabilities leaves uncovered mass at least
`1-E-J`. CRT realizes an uncovered residue as an integer. The cylinder
bound and `prod_B t_(d,B)=t_d` prove (BS2).

Without crossing classes, the tail fibre is covered exactly when at least
one block is saturated. If no block is saturated, choose one point in
each complement and use CRT. Since `1[alpha_B=1]<=alpha_B^2`, the union
bound proves (BS3). No assumption on block cardinality was used.

#### Moment bounds preserve the original labels

Let `F_B=sum_(d local to B) h_d/t_d`, let `mathcal T_B` be the set of
distinct tail parts occurring locally, and set `W_B=sum_(t in mathcal T_B)1/t`.
The two available moment bounds are

\[
 A_B\le\sum_{d,e\text{ local to }B}
       \frac{\mu(h_dh_e=1)}{t_dt_e},\qquad
 A_B\le\Gamma_Q(\mu)W_B^2.                              \tag{BS4}
\]

The first follows from `alpha_B<=F_B` and retains incompatible head
intersections as zero. For the second, fix a tail part `t`. Distinctness
of the **original** moduli implies at most one class for each head label
`m` with `mt in D`. Completing the missing head labels to a complete test
layout shows that `L_t=sum_(mt in D)h_(mt)` satisfies
`||L_t||_2<=sqrt(Gamma_Q(mu))`. Minkowski applied to
`F_B=sum_t L_t/t` gives (BS4). In particular,

\[
 W_B\le\prod_{q\in B}\sum_{e=0}^{v_q(N)}q^{-e}-1
       <\prod_{q\in B}\left(1+\frac1{q-1}\right)-1.
 \tag{BS5}
\]

This is where the existing reciprocal-divisor Euler product enters the
new criterion. The same divisor coordinates used at 5040 supply `W_B`;
the squared block loads in (BS4) additionally account for the actual head
incidences. No two-prime distinct-modulus theorem is applied to a projected
family with repeated tail moduli. No general tensorization of Gamma is used.

#### Arbitrary three-prime heads with sparse tail interactions

The existing common uniform law on the actual complete `{3,5,7}` head
survivors satisfies

\[
 \Gamma_Q(\mu)\le G=\frac{1889}{48},\qquad
 \sum_{m\mid Q}c_\mu(m)\le C=1+\frac{1649}{360}
                         =\frac{2009}{360}.             \tag{BS10}
\]

The Gamma bound is the consequence of (ZG1) displayed after (N9), and the
nonunit cylinder sum is the common-density bound preceding (P14). Both
hold for the same uniform law, arbitrary finite heights, arbitrary actual
head residues, and missing head classes. Unlike the star application,
no particular head assignment is imposed here.

**Degree-two tail theorem.** Distinct odd moduli cannot cover if every
prime factor belongs to `{3,5,7}` or is at least 37, and the actual
interaction graph on primes at least 37 has maximum degree at most two.
There is no exponent bound or bound on the total number of primes.
Arbitrarily long path and cycle components, as well as triangles, are allowed.

To prove this, set `a_q=1/(q-1)`, `S=sum_q a_q^2`, and take singleton
blocks with threshold `delta=2/3`. A tail support must be a clique in the
interaction graph, so it has size at most three. Triangles are pairwise
vertex-disjoint components. The degree bound and `a_q<=1/36` give

\[
 \sum_{\{q,r\}\in\mathcal E}a_qa_r\le S,\qquad
 \sum_{\{q,r,s\}\text{ triangle}}a_qa_ra_s\le\frac{S}{108}.
\]

For the first inequality use `2ab<=a^2+b^2` and count vertex degrees.
For the second, average the three bounds `abc<=(1/36)ab` and use the
same square inequality within each disjoint triangle. For a fixed tail
part `t`, distinct original moduli give
`sum_(d:t_d=t)mu(h_d=1)<=sum_(m|Q)c_mu(m)<=C`. Summing all positive
prime powers on a fixed support then gives the product of its `a_q`.
Consequently (BS1)--(BS2) satisfy

\[
 E+J\le E+J_{\rm raw}
 \le\frac94 GS+C\left(9S+27\frac{S}{108}\right)
 =\frac{403681}{2880}S.                                 \tag{BS11}
\]

The exact prime bound already used above gives

\[
 S<\frac{4976233}{2000000000}
     +\sum_{\substack{37\le q\le73\\q\text{ prime}}}
                 \frac1{(q-1)^2}
  =\frac{469089312556889868097}{72216234108018000000000},
\]

so the right side of (BS11) is less than
`189362442782277858843265057/207982754231091840000000000 < 0.91048 < 1`.
This proves the theorem using (BS1).

**Three-vertex component theorem.** The lower cutoff can instead be 31
if every tail interaction component has at most three vertices. Use each
component as one block; there are no crossing classes. Now `a_q<=1/30`
and (BS5) gives, for each such component,

\[
 W_B\le\frac{2791}{2700}\sum_{q\in B}a_q,\qquad
 W_B^2\le3\left(\frac{2791}{2700}\right)^2
                    \sum_{q\in B}a_q^2.
\]

Indeed the pair terms in the three-variable product sum to at most
`(1/30)sum a_q`, and its triple term to at most
`(1/(3*30^2))sum a_q`. The same coefficient covers smaller components.
Using (BS3)--(BS4) and (BS10), the total loss is strictly below

\[
 3G\left(\frac{2791}{2700}\right)^2
 \left(\frac{4976233}{2000000000}
        +\sum_{\substack{31\le q\le73\\q\text{ prime}}}
                              \frac1{(q-1)^2}\right)
 =\frac{8083223933051729599312138630673}{8423301546359219520000000000000}
 <0.95963<1.                                             \tag{BS12}
\]

Both statements allow a modulus with all three head primes and all three
primes of a tail triangle, hence six distinct prime factors. They allow
arbitrarily many distinct prime factors across the whole family. They are
not direct specializations of the published at-most-three-factors-per-modulus
or at-most-eight-total-primes results, or of (P1)'s cutoff 67. They do not
claim global literature priority.

More generally, for any actual head law with the two bounds `G,C`, a tail
graph of maximum degree `Delta` and `a_q<=a` satisfies the sufficient criterion

\[
 S\left[\frac{G}{\delta^2}
   +C\sum_{k=2}^{\Delta+1}\frac{\binom\Delta{k-1}}{k}
                    \frac{a^{k-2}}{(1-\delta)^k}\right]<1.
 \tag{BS13}
\]

Every tail support is a clique. On a `k`-clique, averaging pairwise products
gives `prod a_q<=a^(k-2)sum a_q^2/k`; each vertex belongs to at most
`binom(Delta,k-1)` such cliques. Grouping original labels as above proves
(BS13), without bounding the number of graph components.

The fixed-constant singleton criterion for degree two cannot reach cutoff
31 merely by changing its common threshold. Let

\[
 L=\frac{2363054-529}{10^9}
       +\sum_{\substack{31\le q\le73\\q\text{ prime}}}\frac1{(q-1)^2}
    <\sum_{q\ge31,\ q\text{ prime}}\frac1{(q-1)^2}.
\]

Exact arithmetic gives `GL>(33/50)^3` and `CL>(17/50)^3`. For every
`0<delta<1`, Hölder's inequality therefore gives
`GL/delta^2+CL/(1-delta)^2 >= ((GL)^(1/3)+(CL)^(1/3))^3 > 1`, even before
the nonnegative triangle term. This limits this scalar certificate with
the constants (BS10); it does not refute noncoverage at cutoff 31 or exclude
estimates retaining the actual graph and residues. All constants in
(BS10)--(BS13) and these strict comparisons are checked by the same fixed
block certificate linked below. The general arguments are ordinary proofs,
not new Lean declarations.

#### Every positive-height star head admits the required broad law

Take the complete star assignment defined above, now at **arbitrary
positive heights** `H_p>=1` on any set `P` of odd primes at most 73
containing 3. This extends the positive result beyond the heights needed
for the earlier lower-bound refutation; that refutation still uses 31/8.
Let `Q` be the full prime-power part of `N` at primes at most 73, with
support exactly `P`, and suppose the actual classes with `d|Q` are this
star assignment at these full heights. All tail primes are greater than 73.

The same exact survivor decomposition holds, and use only its broad branch

\[
 R_b=C_3\times\prod_{p\in P\setminus\{3\}}D_p,\qquad
 \mu_b=\operatorname{Unif}(R_b).
\]

Its coordinate densities are `s_3=(1-3^(-H_3))/2` and
`s_p=(p-3+2p^(-H_p))/(p-1)` for `p>=5`; all are positive.
For every positive exponent, a coordinate cylinder has mass at most
`p^(-e)/s_p`. Expanding any complete layout square bounds its moment by
`sum_(m|Q) chi(m)c_mu(m)`: each intersection is empty or a cylinder modulo
the lcm, and exactly `2e+1` ordered exponent pairs have maximum `e`.
Factoring these cylinder bounds for the explicitly product law yields

\[
 \Gamma_Q(\mu_b)\le
 \prod_{p\in P}\left(1+s_p^{-1}
                 \sum_{e=1}^{H_p}(2e+1)p^{-e}\right)<K_0<177,
 \quad K_0=5\prod_{\substack{5\le p\le73\\p\text{ prime}}}
                   \frac{p^2-p+2}{(p-3)(p-1)}.           \tag{BS6}
\]

The finite ternary factor is exactly `5-2H_3/(3^(H_3)-1)<5`, since its
weighted sum is `2-(H_3+2)3^(-H_3)`. For the other coordinates use
`sum_(e>=1)(2e+1)p^(-e)=(3p-1)/(p-1)^2` and the lower bound on `s_p`.
All omitted-prime factors exceed one. The unweighted cylinder sum similarly
satisfies

\[
 \sum_{m\mid Q}c_{\mu_b}(m)\le C_0<\frac{73}{10},\qquad
 C_0=2\prod_{\substack{5\le p\le73\\p\text{ prime}}}
                \frac{p-2}{p-3}.                       \tag{BS7}
\]

Here the finite ternary factor is exactly 2. These bounds concern the
specific star law; no bound for arbitrary head assignments is asserted.

#### Matching tails cannot complete a star

The actual tail interaction graph has the primes greater than 73 dividing
`N` as vertices, and an edge `{q,r}` when an original modulus contains
both. If this graph is a matching, its components are singleton or pair
blocks, and every tail class is local to one block. All residues, exponents,
numbers of tail primes, and head factors within tail moduli remain arbitrary.

Write `a=1/(q-1)`, `b=1/(r-1)`. Since `q,r>=79`, the pair load satisfies
`W_B<=a+b+ab<=(157/156)(a+b)`. Thus
`W_B^2<=2(157/156)^2(a^2+b^2)`, with the same upper coefficient valid for
singletons. The exact prime-tail bound gives

\[
 \sum_{q>73,\ q\text{ prime}}\frac1{(q-1)^2}<\frac1{400},
 \qquad \sum_B A_B<177\cdot2\left(\frac{157}{156}\right)^2\frac1{400}
       =\frac{1454291}{1622400}<\frac9{10}.
\]

By (BS3), more than `168109/1622400>1/10` of the broad-branch head points
have an uncovered tail lift. This proves noncoverage of every such star
extension. The conclusion also survives removal of redundant mixed-zero
head classes, since that leaves the head survivors unchanged. The numerical
proportion refers to head points under `mu_b`, not to uniform density in
the entire period `N`.

#### Star forests: arbitrarily many centres of unbounded degree

Let `mu` be any actual head survivor law with `Gamma_Q(mu)<=G`. Suppose
the tail interaction graph is a disjoint union of stars, allowing isolated
vertices and edges. There is no bound on the number of stars or their degrees.
For one component choose its centre `r` and write its leaves as `q`.
For fixed head point `x`, let `alpha_r(x)` be the fraction of the `r` coordinate
covered by actual classes with tail part a pure power of `r`. For fixed
`r` coordinate `y`, let `alpha_q(x,y)` be the covered fraction of the `q`
coordinate from all actual classes with tail support `{q}` or `{r,q}`.
Put `beta_q(x)=Pr_y[alpha_q(x,y)=1]`, where `y` is uniform.

If the whole component is saturated above `x`, every `y` outside the central
pure-power union must saturate at least one leaf fibre. Otherwise choose an
uncovered coordinate for every leaf and apply CRT. Hence
`alpha_r+sum_q beta_q>=1` on saturation, and pointwise

\[
 1[\text{component saturated}]
 \le\frac43\left(\alpha_r^2+\sum_q\beta_q\right),
 \qquad \alpha_r^2+1-\alpha_r
       =(\alpha_r-\tfrac12)^2+\tfrac34.                 \tag{SF1}
\]

Set `a_p=1/(p-1)` and `D_p=1+3a_p+2a_p^2`. The original-label bound (BS4)
gives `E_mu alpha_r^2<=G a_r^2`. For a leaf, regard `Qr^(v_r(N))` as the
head, with the unconditioned law `mu` times uniform `r`. At fixed tail
power `q^e`, every original modulus has a distinct enlarged head label;
repeated projected `q^e` moduli are all retained. The uniform-coordinate
transfer (T1), with `delta=0`, gives enlarged Gamma at most `G D_r`.
Applying (BS4) there yields

\[
 \mathbb E_\mu\beta_q
 \le\mathbb E_{\mu\otimes U_r}\alpha_q^2
 \le G D_r a_q^2.
\]

The tail can cover a head fibre only if one of its components is saturated.
Thus (SF1), summed over the disjoint components, proves

\[
 \mu\{x:\text{an uncovered tail lift exists}\}
 \ge 1-\frac{4G}{3}\sum_{\text{stars}}
       \left(a_r^2+D_r\sum_{q\text{ leaf}}a_q^2\right).
 \tag{SF2}
\]

An isolated vertex satisfies the stronger direct bound `G a_r^2`, so it
also satisfies this estimate. No independence of overlapping deletion
events was assumed. Each star's centre may be chosen freely when its degree
is at most one.

For a uniform lower tail-prime cutoff `q0`, (SF2)'s loss is at most
`(4G/3)(1+3/(q0-1)+2/(q0-1)^2) sum_q 1/(q-1)^2`. Exact constants give:

| Head | Tail primes | Saturated-head mass upper bound |
|---|---|---:|
| Arbitrary `{3,5,7}` head, law (BS10) | `q>=19` | `<0.858311` |
| Complete star head at any positive heights, law (BS6) | `q>73` | `<0.588420` |

Both therefore exclude covering systems with any star-forest tail graph.
The first permits arbitrarily many primes in total and original moduli
with all three head primes and two tail primes. The second applies to the
same star geometry that refutes the universal Gamma73 target.

#### Arbitrary forests: a bound independent of depth and degree

The actual tail interaction graph may be any finite forest. Since every
tail support forms a clique, each actual tail modulus then involves at most
two tail primes. There is no bound on the number of vertices, their degrees,
tree depth, or prime-power exponents. Two resulting exclusions are:

| Head | Tail primes | Saturated-head mass upper bound |
|---|---|---:|
| Arbitrary `{3,5,7}` head, law (BS10) | `q>=19` | `<0.965600` |
| Complete star head at any positive heights, law (BS6) | `q>73` | `<0.661972` |

Here is the finite recursive argument, with all probabilities over the
original head law `mu`. Root every tail tree independently of the head point
`x`. Write `Y_v=Z/v^(v_v(N))Z` for a prime coordinate and `U_v` for its
uniform law. Assign every class with tail support `{v}` to `v`, and every
class with tail support `{p,v}`, where `p` is the parent, to its child `v`.
A root receives original moduli `m v^e`, where `m|Q,e>=1`; a nonroot receives
original moduli `m p^f v^e`, where `m|Q,f>=0,e>=1`. Every actual tail class
is assigned exactly once. Original moduli, including their full head labels,
remain distinct labels; repeated projected tail moduli are never deleted.

For fixed `x` and parent value `z`, let `F_v(x,z)` be the union of the actual
forbidden `v` cylinders from the classes assigned to `v` whose head and
parent conditions hold. Put `alpha_v(x,z)=U_v(F_v(x,z))`. Give a root a
one-point parent space, so the same notation covers all vertices. Define

\[
 \epsilon_v(x)=\mathbb E_{z\sim U_{p(v)}}\alpha_v(x,z)^2,
 \qquad
 s_v=\sum_{e=1}^{H_v}v^{-e},\quad
 \kappa_v=1+\sum_{e=1}^{H_v}(2e+1)v^{-e}.
 \tag{AF1}
\]

For a root `epsilon_v=alpha_v^2`. These are actual union fractions, not raw
sums of cylinder measures. Let `V` be the set of head points having an
uncovered tail lift. The general forest bound is

\[
 \mu(V)\ge1-\frac32\sum_v\mathbb E_\mu\epsilon_v
 \ge1-\frac{3G}{2}\left(\sum_{v\text{ root}}s_v^2+
       \sum_{v\text{ nonroot}}\kappa_{p(v)}s_v^2\right).
 \tag{AF2}
\]

**Exact subtree messages.** Fix `x`. Define `B_v` as the set of parent
values for which no assignment to the entire subtree rooted at `v` avoids
all classes assigned to that subtree, including its incoming parent edge.
Write `beta_v=U_(p(v))(B_v)` and `c_v=sum_(w child of v) beta_w`. For a root,
`beta_v` is zero or one; it is one exactly when that component is saturated.
These sets have the exact finite recursion

\[
 z\in B_v\quad\Longleftrightarrow\quad
 F_v(x,z)\ \cup\!\bigcup_{w\text{ child of }v}B_w=Y_v.
 \tag{AF3}
\]

Indeed a `v` value outside the union violates none of its assigned classes
and has an avoiding extension in each child subtree. Those extensions can
be combined because different child subtrees have disjoint tail coordinates
and no classes connecting them. The child sets depend on `x` and the `v`
coordinate, not on the parent value `z`; no probabilistic independence of
the sets is assumed. This proves (AF3) by induction on finite subtree height.
For every `z in B_v`, the union bound gives `1<=alpha_v(x,z)+c_v`, hence

\[
 \epsilon_v\ge\beta_v(1-c_v)_+^2.                     \tag{AF4}
\]

**A potential that cancels along every tree.** Set `Phi(t)=t-t^3/3` for
`0<=t<=1`. For `b,b_i in [0,1]` and `c=sum_i b_i`,

\[
 \Phi(b)\le b(1-c)_+^2+\sum_i\Phi(b_i).               \tag{AF5}
\]

If `c>=1`, then `sum Phi(b_i)>=2c/3>=2/3>=Phi(b)`. These bounds follow
from `Phi(t)>=2t/3` and `2/3-Phi(t)=(1-t)^2(t+2)/3` for `t in [0,1]`.
If `0<=c<=1`, then `sum b_i^3<=c^3`, so `sum Phi(b_i)>=Phi(c)`.
When `b<=c`, monotonicity of `Phi` on `[0,1]` proves (AF5). When `c<=b`,
use the exact identity

\[
 b(1-c)^2+\Phi(c)-\Phi(b)
 =c(1-b)^2+\frac{(b-c)^3}{3}\ge0.                    \tag{AF6}
\]

This proves (AF5). Applying it to `beta_v` and its child messages, then using
(AF4), gives `Phi(beta_v)<=epsilon_v+sum_(w child) Phi(beta_w)`.
Summation over a tree cancels every nonroot potential exactly once:

\[
 \sum_{v\text{ in tree}}\epsilon_v
 \ge\Phi(\beta_{\rm root})
 =\tfrac23\,1[\text{tree saturated}].                 \tag{AF7}
\]

A tail lift exists exactly when every component has an avoiding assignment.
Consequently `1[x not in V]<=(3/2) sum_v epsilon_v`, which proves the first
inequality in (AF2). No fibres are discarded or conditioned on, and there
is no factor accumulating with depth, degree, or component size.

**Moment bound retaining the original labels.** For a root, (T2) gives
`E_mu epsilon_v<=G s_v^2`. For a nonroot `v` with parent `p`, test its actual
assigned family over the enlarged head `Q p^(H_p)` with law `mu times U_p`.
At fixed positive `v` exponent `e`, the old divisor `m p^f` determines the
original modulus `m p^f v^e`; there is at most one original class for that
old divisor. Thus (T2) applies without assuming distinct projected `v^e`
moduli. The unconditioned transfer (T1), with `delta=0`, gives

\[
 \mathbb E_\mu\epsilon_v
 \le\Gamma_{Qp^{H_p}}(\mu\otimes U_p)s_v^2
 \le G\kappa_p s_v^2.                                \tag{AF8}
\]

The coefficient retains both pure and incoming-edge classes: among
nonnegative parent exponent pairs there are `2e+1` pairs with maximum `e`.
The uniform parent law is only the testing law for this moment estimate.
It is not asserted to survive the parent's classes; their effect is already
present in the exact subtree recursion. This proves the second inequality
in (AF2).

For a tail cutoff `q0`, put `a0=1/(q0-1)`,
`kappa0=1+3a0+2a0^2`, and let `S` bound `sum_(q>=q0 prime)1/(q-1)^2`.
Since `s_v<=1/(v-1)` and `kappa_v<=kappa0`, (AF2) yields the sufficient
condition `(3/2) G kappa0 S<1`. It also retains the stronger individual-parent
and root coefficients when a concrete forest is known.

For arbitrary `{3,5,7}` heads, take `q0=19`, `G=1889/48`, and
`kappa0=95/81`. The sharper prime-square estimate (GS1) gives

\[
 S_{19}=\frac{2400198237}{10^{12}}+
       \sum_{\substack{19\le p\le73\\p\text{ prime}}}\frac1{(p-1)^2},
 \qquad
 \frac32G\kappa_0S_{19}
 =\frac{6024840902671133365942778501}
        {6239482626932755200000000000}
 <0.965600<1.                                          \tag{AF9}
\]

For a complete star head, take `q0=79`, `G=177`, `kappa0=1580/1521`, and
`S=2400198237/10^12`. The exact loss is

\[
 \frac32G\kappa_0S=\frac{11187323982657}{16900000000000}
 <0.661972<1.                                         \tag{AF10}
\]

Thus more than `5712676017343/16900000000000>0.338028` of its broad-branch
head points admit an uncovered tail lift. In particular, any full star
completion must contain a cycle in its actual tail interaction graph.
This proportion concerns head points, not uniform density in the full
period. These are arbitrary-finite-forest proofs; the adjacent exact
certificate verifies their scalar constants, not a bounded enumeration of
tree shapes. Proof provenance: the Nyx oracle supplied the exact-message
energy reduction; the cubic potential above is the present refinement.
These are ordinary mathematical proofs, not complete Lean formalizations
of the forest criterion.

The reusable construction in
[ExactForestMessages.exact_forest_message_feasibility](../D5/S3/Arith/Congruence/ExactForestMessages.lean)
formalizes the exact residual-set equations and the equivalence between a
simultaneous avoiding assignment and nonempty root residuals, for arbitrary
finite forests and finite domains. Its two well-founded recursions construct
messages from leaves upward and assignments from roots downward. The scoped
kernel build and source-bound report use only `propext`, `Classical.choice`,
and `Quot.sound`. The congruence embedding, cubic potential, and moment
estimates (AF2) remain outside that Lean theorem.

[ForestConstraintEnergy.unsatisfiable_forest_square_energy](../D5/S3/Arith/Congruence/ForestConstraintEnergy.lean)
also formalizes the actual-constraint energy estimate (AF7). Each vertex may
carry any fixed normalized nonnegative weights. From the original unary and
binary forbidden relations and unsatisfiability, it derives the bound
`sum epsilon_v>=2/3`, using the exact messages, weighted union estimates,
the cubic potential, and cancellation over the forest. It does not assume
the local energy inequalities. Its scoped build and source-bound report
have the same standard axiom closure. The CRT embedding, prime-coordinate
moment bounds, and arithmetic noncoverage consequences remain separate.

#### A bounded number of cycle-breaking vertices in each component

The same argument extends beyond forests. A feedback vertex set is a set
of vertices whose deletion leaves a forest. Its size is measured separately
in each connected component; the number of components remains unrestricted.
For a tail cutoff `q0` put `D=1+3/(q0-1)+2/(q0-1)^2` and define

\[
 C_0=\frac32D,\qquad
 z_k=C_kD,\qquad C_{k+1}=\frac{4z_k^2}{4z_k-1}.
 \tag{FV1}
\]

If every tail component has a feedback vertex set of size at most `k`,
then, for the same actual head law and original distinct moduli,

\[
 \mu\{x:\text{tail fibre is saturated}\}
 \le G C_k\sum_{q\text{ tail}}\frac1{(q-1)^2}.
 \tag{FV2}
\]

The case `k=0` is (AF2). For the induction step, choose a vertex `r` from
a nonempty feedback set in one component `J`, independently of the head
point. Let `alpha_r(x)` be the uniform fraction of its coordinate covered
by actual classes whose tail support is exactly `{r}`. Absorb the full
`r` prime power into the head with the unconditioned law `nu=mu times U_r`.
Each component `J_i` of `J-r` has a feedback set of size at most `k`.
Every remaining class belongs to exactly one `J_i` after this absorption:
its residual support is a clique and is therefore connected. In particular,
a triangle class containing `r` becomes a two-prime class in one residual
component. No such class is omitted or assigned twice.

Let `beta_i(x)` be the uniform probability over `r` that the family assigned
to `J_i` saturates its residual fibre. Saturation of `J` implies
`alpha_r+sum_i beta_i>=1`: otherwise some `r` value avoids its pure classes
and every residual component has an avoiding extension, which combine by
CRT. For any `B>1` and `A=B^2/(4(B-1))`, the identity

\[
 A t^2+B(1-t)-1=A\left(t-\frac{B}{2A}\right)^2
 \tag{FV3}
\]

gives `1[J saturated]<=A alpha_r^2+B sum_i beta_i`. The moment bound gives
`E_mu alpha_r^2<=G a_r^2`. The uniform transfer bounds `Gamma(nu)<=G D_r`,
where `D_r=1+3a_r+2a_r^2<=D`. The inductive forest-deletion estimate for all
the residual components therefore gives

\[
 \mu\{J\text{ saturated}\}
 \le G\left[A a_r^2+B C_kD_r
                        \sum_{q\in J\setminus\{r\}}a_q^2\right].
 \tag{FV4}
\]

There is no requirement that `nu` survive the pure-`r` classes: those were
separately charged through `alpha_r`. The subfamily assigned to each `J_i`
has no class wholly in its enlarged head. At each residual tail divisor
`t`, an enlarged head label `m r^f` determines the original modulus
`m r^f t`; thus distinctness is preserved even when projected moduli repeat.

Now set `z=C_kD`, `B=4z/(4z-1)` and `A=4z^2/(4z-1)=C_(k+1)`.
Here `z>=3/2`, so all denominators are positive, `A=Bz`, and (FV3) applies.
Both terms of (FV4) have coefficient at most `G C_(k+1)`.
Components already having a smaller feedback set obey the same bound,
because `C_(k+1)>=C_kD>=C_k`. Summation over all components proves (FV2).
The argument permits arbitrary degrees, exponents, component counts and
depths of attached trees. A feedback set of size one can break arbitrarily
many cycles sharing a vertex; this is more general than a single-cycle
component.

Two exact consequences of (FV2) and the prime-square bound (GS1) are:

| Head | Tail primes | Feedback vertices per component | Saturated-head mass upper bound |
|---|---|---:|---:|
| Arbitrary `{3,5,7}` head | `q>=23` | at most 1 | `<0.956460` |
| Complete star head | `q>73` | at most 2 | `<0.966288` |

For the first row, `D=138/121`, `C_1=3264065424/1458580343`, and

\[
 \frac{1889}{48}C_1S_{23}
 =\frac{1175604260732733206684398339119}
        {1229120627265994463000000000000}<1.            \tag{FV5}
\]

For the second row, `D=1580/1521`,
`C_2=387820588344395661352960000000000/170508100702446502707449794959279`,
and

\[
 177C_2S_{79}
 =\frac{16950596065609491264623331474432}
        {17541985668975977644799361621325}<1.           \tag{FV6}
\]

Every pseudoforest, meaning at most one cycle in each component, is covered
by the first row. Arbitrarily branching and deep trees may be attached to
each cycle, and a modulus may contain all three tail primes of a triangular
cycle. The second row implies that a full star completion must have a tail
component for which deleting any two vertices still leaves a cycle. Many
cycles in separate components do not suffice. These are ordinary proofs;
the exact recurrence values and inequalities are checked by the same
adjacent certificate as the forest constants.

Tree elimination has public antecedents in
[Csikvari--Nagy, *The Density Turan Problem*, Theorem 3.1 and Algorithm 3.3](https://arxiv.org/abs/1407.7873),
which use prescribed edge densities and a matching-polynomial criterion.
[He--Li--Liu--Wang--Xia, Theorem 6 and Corollary 38](https://arxiv.org/abs/1709.05143)
concern a tree event-dependency graph, a different hypothesis from a tree
of prime variables. Neither supplies the conditional square-energy and
cubic-potential estimate used here. No exact dominating theorem was found
in those searched scopes, and no global priority claim is made.
The verifier also checks all 16384 unary/binary constraint assignments on
a three-vertex binary path against its eight complete assignments, testing
exact-message completeness and the local cubic-potential inequality.
This finite regression checks the implementation against actual feasible
assignments; it does not replace the arbitrary-tree proof above.

#### Ordered local kernels: unbounded feedback sets and treewidth

A tail graph is `d`-degenerate when it admits an ordering in which every
vertex has at most `d` earlier neighbours. This allows unbounded maximum
degree, feedback vertex number, treewidth and component size. The actual
modulus labels and the conditional caps of the BBMST kernel yield:

| Head | Tail primes | Tail graph | Saturated-head mass upper bound |
|---|---|---|---:|
| Arbitrary `{3,5,7}` head | `q>=17` | any forest | `<0.955226` |
| Arbitrary `{3,5,7}` head | `q>=19` | `2`-degenerate | `<0.885762` |
| Arbitrary `{3,5,7}` head | `q>=23` | `5`-degenerate, including every planar graph | `<0.945592` |
| Complete star head | `q>73` | `20`-degenerate | `<0.990060` |

Every finite simple planar graph is `5`-degenerate, by its edge bound on
every subgraph. Thus the third row permits arbitrarily large grids and
arbitrarily many cycles; there is no bound on exponents or total prime
support. The last row means that any full star completion must have a
nonempty subgraph of minimum degree at least 21, equivalently a nonempty
21-core in its actual tail graph.

**Local class assignment and kernels.** Fix an ordering of the tail primes,
write `P_v` for the earlier neighbours of `v`, and assign every actual
class with nontrivial tail part to its latest tail prime `v`. Every other
tail prime in that modulus belongs to `P_v`. The assigned moduli have form
`m v^e product_(p in P_v) p^(f_p)`, where `m|Q`, `e>=1`, and `f_p>=0`.
Distinct original moduli mean at most one class for each full tuple; no
projected-modulus distinctness is presumed. Moduli containing all primes
of any allowed clique are included.

Fix `0<delta<=1/2` and put `K=1/(1-delta)`. Given the head `x` and the
entire earlier tail history, let `F_v` be the actual forbidden union in
`Y_v` from the classes assigned to `v`, and let `alpha_v=U_v(F_v)`. Choose
the new coordinate with the existing BBMST capped kernel (T4). Its density
relative to the uniform coordinate is `0` on `F_v` and `1/(1-alpha_v)`
off `F_v` when `alpha_v<=delta`; otherwise its density is
`(alpha_v-delta)/(alpha_v(1-delta))` on `F_v` and `K` off `F_v`.
This is normalized for every history, including completely forbidden
fibres, and everywhere bounded by `K`. Thus the original head marginal
stays `mu`, and every conditional cylinder obeys

\[
 \Pr(y_v=b\bmod v^e\mid x,\text{entire earlier history})
 \le K v^{-e}\quad(e\ge1).                            \tag{DG1}
\]

Conditional on a fixed `x`, an arbitrary set `J` of queried earlier
coordinates therefore satisfies the simultaneous-cylinder cap

\[
 \Pr\left(\bigcap_{p\in J}\{y_p=b_p\bmod p^{e_p}\}\mid x\right)
 \le\prod_{p\in J}Kp^{-e_p}.                          \tag{DG2}
\]

Remove the latest queried coordinate using (DG1) and the tower law, then
repeat. Unqueried intermediate coordinates integrate out without another
factor. No independence of the sequentially chosen coordinates, and no
conditioning on complete survival, is used.

The selected-coordinate passage in (DG2) now has a Lean proof in
[SequentialKernelCylinder.selected_cylinder_bound](../D5/S3/Arith/Congruence/SequentialKernelCylinder.lean).
For arbitrary measurable alphabets, let `κ_n` be a Markov kernel from the
complete history through `n` to coordinate `n+1`. Fix `a<=b` and a selected
set `S` contained in `{a+1,...,b}`. If, at every complete history, each
selected coordinate event `E_i` has conditional kernel probability at most
`c_i`, then its joint probability under Mathlib's actual partial trajectory
kernel, conditioned on any fixed history through `a`, is at most
`prod_(i in S) c_i`. No independence, joint-cylinder estimate or
prefix-preservation premise is assumed. Induction removes the last
coordinate; selected coordinates use their one-step bound and unselected
coordinates use Mathlib's existing Markov prefix-preservation theorem.
This proves the probability-theoretic passage from the local caps to the
joint selected-cylinder bound. Instantiating the capped residue kernels,
retaining original modulus labels in the second-moment expansion, and the
prime-tail estimates remain separate formalization obligations.

**Only the actual earlier neighbours enter the moment bound.** Put
`s_v=sum_(e=1..H_v) v^(-e)` and `h_p=sum_(j=1..H_p)(2j+1)p^(-j)`.
Bound `alpha_v` by its raw uniform-fibre cylinder load and expand its
square. Group by the two full tail exponent tuples. If parent cylinders
are incompatible the intersection is empty. Otherwise (DG2) contributes
`K p^(-max(f_p,f'_p))` for each positive maximum, and `1` for two zero
exponents. These bounds hold separately at every `x`. What remains for
fixed exponent tuples is the cross moment of two partial head layouts;
completing missing head labels and Cauchy--Schwarz bound it by `G`.
There are exactly `2j+1` nonnegative exponent pairs with maximum `j`, so

\[
 \mathbb E\alpha_v^2
 \le Gs_v^2\prod_{p\in P_v}(1+Kh_p).                  \tag{DG3}
\]

The expectation is under the full sequential prefix law. This estimate
includes no factor for earlier vertices outside `P_v`; it does not bound
the Gamma of the entire accumulated head.

Let `V_v` be the event that the chosen `v` coordinate violates at least one
class assigned to `v`. The already-established capped-kernel bound (T4) gives

\[
 \Pr(V_v)=\frac{\mathbb E(\alpha_v-\delta)_+}{1-\delta}
 \le\frac{Gs_v^2}{4\delta(1-\delta)}
                         \prod_{p\in P_v}(1+Kh_p).    \tag{DG4}
\]

Later normalized kernels preserve the complete prefix marginal, so this
is also the probability of `V_v` in the final joint law. Outside the union
of these events every original tail class is avoided at its assigned
coordinate, and `mu` already avoids every head-only class. CRT supplies
an uncovered integer. A saturated head forces some `V_v` under every tail
sample, so preservation of the head marginal gives
`mu(saturated heads)<=Pr(union_v V_v)`. Consequently the head mass with no
avoiding lift is at most

\[
 \frac{G}{4\delta(1-\delta)}
       \sum_v s_v^2\prod_{p\in P_v}(1+Kh_p).          \tag{DG5}
\]

This formula also applies without any uniform bound on predecessor count,
whenever its actual weighted sum can be controlled.

**Distinct parents sharpen the uniform certificate.** For a lower cutoff
`q0`, list the allowed primes as `p_1<p_2<...`, and write

\[
 a_p=\frac1{p-1},\quad
 T_p=1+\frac{3a_p+2a_p^2}{1-\delta},\quad
 R_d=\prod_{i=1}^dT_{p_i}.
\]

The factors decrease with `p`. A vertex outside the first `d` primes has
parent product at most `R_d`; for `v=p_i` with `i<=d`, the vertex cannot
be its own parent, giving the smaller bound `R_d T_(p_(d+1))/T_(p_i)`.
Completing absent vertices by their nonnegative contributions proves

\[
 \sum_v a_v^2\prod_{p\in P_v}T_p
 \le R_d\left[S_{q0}+\sum_{i=1}^d a_{p_i}^2
                   \left(\frac{T_{p_{d+1}}}{T_{p_i}}-1\right)\right].
 \tag{DG6}
\]

Here `S_q0` is the independently checked prime-square upper bound from
(GS1), with the omitted smaller primes added exactly. Inserting (DG6) in
(DG5) yields the displayed table with, respectively,
`(q0,d,delta)=(17,1,11/25),(19,2,41/100),(23,5,37/100),(79,20,9/25)`.
The head constants are `1889/48` in the first three rows and `177` in the
last. The adjacent certificate recomputes the distinct-prime products,
the negative self-parent corrections and every strict rational comparison.
It also checks eight actual CRT instances modulo 1155, retaining all
15 distinct nonunit divisor labels and a nonuniform law on the two actual
surviving head residues modulo 3. Across 6160 complete assignments and
9200 conditional cylinder queries, the regression checks normalization,
selective-coordinate caps, the actual-load second moment, preservation
of assigned violation probabilities by later kernels, and the final
union bound. This exercises (DG2)--(DG4) with actual arithmetic classes.
The results are ordinary proofs and exact arithmetic, not a complete Lean
formalization of the kernel construction or its graph application.

The capped kernel itself is reused from (T4) and
[BBMST](../Library/Arith/balister2018covering.md); the new point is retaining
only the actual earlier-neighbour coordinates in (DG2)--(DG5). The forest
and feedback-vertex arguments do not imply this bound when treewidth or
feedback vertex number is unbounded. For unrestricted tail support, (DG5)'s weighted predecessor products
still need control without a fixed degeneracy hypothesis. The next
criterion instead bounds the support of each original modulus.

#### Bounded tail support permits arbitrary co-occurrence graphs

A restriction on each **original modulus**, rather than the degree of its
co-occurrence graph, gives a different noncoverage theorem. Suppose the
actual head survivors support a law with `Gamma<=G`, all tail primes are
at least `q0`, and each original modulus contains at most `s` distinct tail
primes. Its head part may be any divisor of the head period. All prime
exponents and the total number of primes are unrestricted. The following
strict bounds exclude coverage:

| Head | Tail primes | Maximum tail primes per original modulus | Threshold `delta` | Saturated-head mass upper bound |
|---|---|---:|---:|---:|
| Complete star through 73 | `q>73` | 2 | `2/5` | `<0.861` |
| Arbitrary `{3,5,7}` head | `q>=23` | 2 | `3/8` | `<0.947` |
| Head period divides 315 | `q>=17` | 3 | `3/10` | `<0.981` |
| Head period divides 945 | `q>=19` | 3 | `7/20` | `<0.989` |

There is **no graph restriction**: complete graphs with arbitrarily many
vertices are allowed. In particular, a covering completion of the full
star head must contain an original modulus with at least three tail prime
factors. For either finite-head row, a covering completion must contain a
modulus with at least four tail prime factors. These conclusions apply to
the named heads and cutoffs, not to an arbitrary odd covering family.

Order tail primes increasingly and use exactly the kernels, latest-prime
assignment and prefix-marginal preservation from (DG1)--(DG4). Put

\[
 a_p=\frac1{p-1},\qquad b_p=a_p+2a_p^2,\qquad
 K=\frac1{1-\delta},\qquad r=s-1,
\]
\[
 B_r(v)=\sum_{i,j=0}^r[x^iy^j]
       \prod_{q_0\le p<v}\bigl(1+Ka_p(x+y)+Kb_pxy\bigr),
 \quad\text{with the product over primes}.             \tag{RK1}
\]

For the two preceding exponent tuples in a squared load, a prime occurring
only on the left or only on the right contributes `K sum_(e>=1) p^-e=Ka_p`.
A prime occurring on both sides contributes
`K sum_(e,f>=1) p^-max(e,f)=Kb_p`: exactly `2j-1` positive exponent pairs
have maximum `j`. Its cap is `K`, not `K^2`, because the two cylinders
intersect in one cylinder. Each exponent tuple has at most `r` positive
entries, which is precisely the coefficient truncation in (RK1).

Distinct original moduli give at most one class per full tuple including
the head divisor. For each pair of tail tuples, complete the two partial
head layouts and apply Cauchy--Schwarz to their cross moment, giving `G`.
Thus (DG2) and the nonnegative exponent-pair expansion prove

\[
 \mathbb E\alpha_v^2\le Ga_v^2B_r(v),\qquad
 \mu(\text{saturated heads})
 \le\frac{G}{4\delta(1-\delta)}
             \sum_{v\ge q_0\atop v\text{ prime}}a_v^2B_r(v).\tag{RK2}
\]

Completing the preceding prime set and all exponent ranges only enlarges
this nonnegative upper bound. No projected-modulus distinctness is used.
For `r=1`, writing `A_v=sum_(q0<=p<v) a_p` and
`C_v=sum_(q0<=p<v) a_p^2`, the coefficient sum is exactly

\[
 B_1(v)=1+K(3A_v+2C_v)+K^2(A_v^2-C_v).                 \tag{RK3}
\]

The first two rows follow by a rational sum through `N=2^20` and an
all-integer dyadic remainder. Let `A_N,C_N` bound the corresponding prefix
sums. In block `(N2^j,N2^(j+1)]`, their bounds are `A_N+j+1` and
`C_N+2/N`, and the sum of `a_v^2` is at most `1/(N2^j)`.
Dropping the negative term in (RK3) yields the explicit tail bound

\[
 \frac1N\left[2+K(6A_N+12+4C_N+8/N)
                  +K^2(2A_N^2+8A_N+12)\right].       \tag{RK3a}
\]

For the finite sum, compute `A_v^2-C_v` as the nonnegative polynomial
`2 sum_(p<q<v) a_p a_q`, so rounding the individual `a_p` upward preserves
every inequality. The certificate retains the prime count, rounding
scale, finite sum and exact infinite-tail bound.

For the two `r=2` rows, a `3 by 3` positive coefficient recurrence computes
(RK1) through `N=2^20`; every arithmetic rounding is upward to the grid
`10^-12`. Let `A_N` and `B_N` be the certified upper bounds for the finite
sums of `a_p` and `b_p`. In the block `(N2^j,N2^(j+1)]`, even summing over
all integers gives

\[
 \sum a_v^2\le\frac1{N2^j},\qquad
 \sum_{q_0\le p<v}a_p\le A_N+j+1,\qquad
 \sum_{q_0\le p<v}b_p\le B_N+j+1+\frac2{N-1}.          \tag{RK4}
\]

The first inequality uses at most `N2^j` terms, each at most
`(N2^j)^-2`. Each earlier dyadic block adds at most one to the `a` sum;
the additional square sum is at most `1/(N-1)` by integral comparison.
Coefficientwise domination of the product in (RK1) by
`exp(A(x+y)+Bxy)` gives

\[
 B_2(v)\le E_2(A,B):=
       (1+A+A^2/2)^2+B(1+A)^2+B^2/2,                 \tag{RK5}
\]

where in block `j` one takes
`A=K(A_N+j+1)` and `B=K(B_N+j+1+2/(N-1))`.
Consequently the infinite remainder is at most
`N^-1 sum_(j>=0) 2^-j E_2(A,B)`. This is an exact degree-four polynomial
sum: `sum_(j>=0) j^k/2^j` equals `2,2,6,26,150` for `k=0,1,2,3,4`.
The resulting loss bounds are `0.9805125417500644...` and
`0.9883284628019068...`. The verifier checks the moment recurrence and
independently compares finite coefficient truncations with direct
exponent-tuple pair enumeration. The arbitrary-prime argument remains
an ordinary proof; the exact computation certifies its numerical premises.

This uses the actual-label pair-moment framework of
[BBMST](../Library/Arith/balister2018covering.md), Theorem 3.2 and Lemma 3.6,
and its charge criterion in Theorem 3.1. The additional deductions here
are the supported-head estimates and explicit support-restricted tail
bounds. [Schroeder's three-prime theorem](../Library/Arith/schroeder2026noncoverage.md)
restricts the total distinct prime factors of each modulus. It does not
directly cover these head-plus-tail hypotheses: the finite-head rows allow
six total factors in one modulus, while the arbitrary-star row permits
more. BBMST's square-free-head theorem covers the subcase where all primes
through 73 have exponent at most one, not arbitrary head heights. No exact
dominating statement was found in the searched sources; no literature
priority is asserted. The complete-star case now has unrestricted tail
support by (US1)--(US12); arbitrary tail support for the other displayed
heads and arbitrary head geometry remain unresolved.

#### The support restriction is needed only below a finite largest prime

The support bounds above can be removed entirely for every modulus with
sufficiently large **largest prime factor**. In the following table, impose
the tail-support bound only on original moduli whose largest prime factor
is at most `B`. Every original modulus with largest prime factor greater
than `B` may contain arbitrarily many tail prime factors. Under each row,
the original distinct odd family cannot cover the integers.

| Head | Allowed tail primes | Tail-support bound when `P+(d)<=B` | `B` | Certified continuation seed upper bound |
|---|---|---:|---:|---:|
| Complete star through 73 | `q>73` | 2 | 8192 | `<34474` |
| Arbitrary `{3,5,7}` head | `q>=23` | 2 | 32768 | `<160112` |
| Head period divides 315 | `q>=17` | 3 | 8192 | `<28830` |
| Head period divides 945 | `q>=19` | 3 | 8192 | `<34675` |

No graph, tail-exponent-height or total-prime-count restriction is imposed;
the two finite-head rows retain their stated head-period bounds.
Thus any hypothetical covering completion of the full star head must
contain a modulus with at least three tail prime factors **and largest
prime factor at most 8192**. For the 315 and 945 rows, the required
obstruction has at least four tail prime factors and largest prime at
most 8192. The head and allowed-prime conditions remain essential.

**Finite prefix and actual survivor mass.** Use the same increasing-prime
kernels as in (RK1)--(RK2), stopping after all primes at most `B`. Each
coordinate height is taken from the entire original family, including
exponents that occur only in moduli with a later largest prime. At this
stage delete only the classes whose latest tail prime has been processed.
This retains the exact earlier-prime factors needed by every later class.

Let `r` be one less than the support bound in the table and let

\[
 L_B=\frac{G}{4\delta(1-\delta)}
       \sum_{q_0\le v\le B\atop v\text{ prime}}a_v^2 B_r(v),
 \qquad
 P_B=\prod_{q_0\le p\le B\atop p\text{ prime}}
           \left(1+\frac{3p-1}{(1-\delta)(p-1)^2}\right).
 \tag{RK6}
\]

The product accounts for the **full** layout moment, without a support
truncation. The prefix law `nu_B` is normalized; (RK2) gives mass at least
`1-L_B` to points avoiding every processed class, while repeated (T1)
gives `Gamma(nu_B)<=G P_B`. The certificate proves `L_B<1` in each row.
Restricting once to the actual prefix survivors and normalizing is
therefore legitimate and gives a survivor law with

\[
 \Gamma\le F_B:=\frac{G P_B}{1-L_B}.                  \tag{RK7}
\]

Equivalently, one can keep the unconditioned prefix law and start (T6)
with the separate bounds `G P_B` and `1-L_B`. No independence is asserted
after conditioning. T1--T3 apply to arbitrary old laws, and every later
modulus keeps its complete expanded-head divisor. In particular, the
future step does not identify moduli whose tail projections coincide.

**Unrestricted continuation.** Put `k=pi(B)`, counting all primes including
2. Omitted primes have unused coordinates and may be padded with exponent
zero. The supplied seed satisfies the exact sufficient condition

\[
 F_B<k(\log k+\log\log k-3)^2,\qquad k\ge10.           \tag{RK8}
\]

At `B=8192`, `k=1028`, and the certificate's rational lower bound for
the right-hand side is greater than `35445`. At `B=32768`, `k=3512`,
and that lower bound is greater than `185296`. These strictly exceed all
corresponding seed bounds in the table. Starting here,
[BBMST](../Library/Arith/balister2018covering.md), Theorem 6.1 and its
Lemma 6.2, continue the same recurrence (T6) with `delta=1/2` for every
later prime. Their proof uses only positive survivor mass, (RK8), the
recurrence and the published lower bound for the indexed primes. Every
finite continuation therefore has positive survivor mass, with no
restriction on the number of prime factors of a later modulus.
If the family has no later primes, the already positive prefix mass
suffices directly.

The [existing exact verifier](../docs/reports/erdos7-odd-covering/verify_star_block_obstruction.py)
recomputes the finite coefficient sums, full-moment products, all four
positive survivor margins and the strict stopping comparisons. It reuses
`verify_finite_continuation.py:stopping_threshold` for the rational lower
logarithm bounds, so no new analytic estimate is assumed. All rounding of
prefix costs and moment products is upward. This is an ordinary proof
using a published continuation theorem with exact numerical premises;
it is not an end-to-end Lean proof or a resolution of unrestricted #7.
The unrestricted remainder is now localized to the stated small-prime
support conditions and the head geometry, not to large-prime support.

#### Why scalar deletion and unrestricted message energy do not suffice

If root elimination keeps only `E alpha^2<=w`, with `0<=w<=1`, and the remaining connected
component's saturation probability `E beta<=L`, its best possible scalar
bound on `Pr(alpha+beta>=1)` is `min(1,F(w,L))`, where

\[
 F(w,L)=L+\frac w2+\sqrt{wL+\frac{w^2}{4}},\qquad
 \sqrt{F(w,L)}\ge\sqrt L+\frac{\sqrt w}{2}.           \tag{DG7}
\]

Minimizing `Aw+BL` subject to (FV3) gives this expression. It is sharp:
if `0<t=F(w,L)<=1`, an event of mass `t` carrying
`alpha=sqrt(w/t), beta=1-alpha`, with both zero outside, attains all three
values; the zero case is immediate. If `F>=1`, constant `alpha=sqrt(w), beta=1-sqrt(w)`
attains saturation within the budgets. This is a relaxed moment extremizer,
not a purported distinct-modulus covering family.

There is also an actual distinct congruence family showing why even exact
scalar root moments cannot give a universal deletion certificate. For any
finite odd-prime set `P`, prescribe `0 mod p` for every `p in P`, and
`1 mod pq` for every pair. Its tail graph is complete. Each class has a
private point in this union: use only the named zero for a prime class,
or only the two named ones for a pair class, and set every other coordinate
to two. All coordinates equal to two avoid the whole family. After any
sequence of uniform root absorptions, each next root still forbids zero,
so its actual squared moment is at least `1/p^2`. A clique requires all
but two vertices to be deleted before becoming a forest. By (DG7), even
with zero terminal loss and all distortion factors replaced by one, the
resulting scalar budget is at least `(sum_deleted 1/p)^2/4`. Euler's
divergence of the sum of prime reciprocals provides a finite `P` above any
fixed cutoff for which this exceeds one in every order. The finite set is
asserted by divergence, not by an unevaluated numerical enumeration.
The obstruction is to this scalar compression; pointwise caps and actual
coordinate correlations, as retained in (DG1)--(DG5), are additional data.

Nor does the forest energy inequality hold on arbitrary abstract constraint
systems. On uniform variables `x_1,...,x_n,y` of cardinality `q`, forbid
`x_i=0` at each `x_i`, and forbid every `y` value exactly when all `x_i`
are nonzero. Every assignment is forbidden, but the sum of uniform-parent
square energies is `n/q^2+(1-1/q)^n`. At `q=n=3` it is `17/27<2/3`, verified
against all 81 assignments. Taking `n=ceil(2q log q)` makes the energy tend
to zero. The final union repeats full-point modulus labels, so this is
**not** an odd distinct covering counterexample. It shows why the original
modulus injectivity and the arithmetic parent caps must stay inside a
general-graph proof; neither boundary refutes the kernel theorem above.

#### A degree-two core with arbitrarily many pendant leaves

For an arbitrary `{3,5,7}` head, tail primes at least 37 also permit the
following larger graph class. Let `K` be a set of tail vertices whose induced
graph has maximum degree two. Require that the remaining vertices are
independent and each has at most one neighbour in `K`. Paths and cycles
of unbounded length with arbitrarily many leaves attached at each vertex
are included. Equivalently, one may take the vertices of original degree
at least two as the core when their induced graph has maximum degree two,
then add one endpoint from each isolated edge. Isolated vertices may remain
outside the core.

For each core vertex remove its actual pure-coordinate local union and
retain head points where every such union fraction is at most `delta=2/3`.
Their discarded mass is at most `(9G/4) sum_(r in K) a_r^2`. At retained
head points take the core coordinates independently and uniformly on their
local complements. Extend each kernel by the uniform law at discarded head
points; this defines a probability with the original old marginal everywhere,
while the argument uses its restriction to retained heads without normalizing.
Each core kernel has cylinder caps at most `3r^(-e)`. Core-core crossing
classes therefore have exactly the edge and triangle bounds used in (BS11).

An outside leaf `q` with neighbour `r` uses only the enlarged head `Qr^H`.
The transfer (T1) for the extended kernel bounds its Gamma by
`G(1+3(3a_r+2a_r^2))`. The original-label moment bound consequently charges
leaf saturation at most this constant times `a_q^2`, even after restriction
to retained head points. A vertex with no neighbour has the smaller constant
`G`. Once core crossing classes and all saturated leaf fibres are avoided,
choose one uncovered point in each leaf coordinate and use CRT.

The two coefficients are

\[
 K_{\rm core}=\frac{403681}{2880},\qquad
 K_{\rm leaf}=G\left(1+3\left(\frac3{36}+\frac2{36^2}\right)\right)
             =\frac{511919}{10368}<K_{\rm core}.
\]

Thus the total bad mass is at most
`K_core sum_(r in K) a_r^2 + K_leaf sum_(q outside K) a_q^2`, and hence
strictly below **0.898149** by the exact prime-square bound below. This proves
noncoverage for the stated graph class. The preceding forest theorem handles
arbitrary trees from prime 19; this degree-two-core result additionally
allows cycle components with attached leaves from prime 37. Such components
are also included in the stronger one-feedback-vertex result from prime 23.

#### Absorbing a finite set of hub primes

A complementary criterion allows arbitrary interactions among a small set
of hubs. Let `R` be any set of tail primes, and let the remaining tail primes
be partitioned into blocks `B`, with no actual modulus meeting two different
blocks outside `R`. Write

\[
 P_R=\prod_{r\in R}(1+a_r),\qquad
 D_R=\prod_{r\in R}(1+3a_r+2a_r^2).
\]

Suppose the same old head law has Gamma at most `G` and complete cylinder
sum at most `C`. Enlarge the head by the full prime powers at `R`, using
`nu=mu` times uniform hub coordinates. The union of the actual classes
whose tail support lies wholly in `R` has `nu` mass at most `C(P_R-1)`.
This follows by grouping distinct original moduli by their hub divisor and
summing the original head cylinder caps. Iterating the unconditioned transfer
(T1) bounds the enlarged Gamma by `G D_R`.

All remaining classes are local to one residual block. Applying (BS4) and
charging its saturation under `nu` gives the sufficient condition

\[
 C(P_R-1)+G D_R\sum_B W_B^2<1,                         \tag{HB1}
\]

where `W_B` is bounded by (BS5). The hub-forbidden union and all block
saturations together then have mass less than one. A remaining enlarged
head point and one uncovered point in each block give an uncovered integer.
The enlarged law is never conditioned on hub survival; no unproved control
of its normalized Gamma is used.

In particular, when `R` is a vertex cover of the tail graph, the residual
blocks are singletons. If `S` bounds the prime-square sum over all allowed
tail primes, (HB1)'s loss is at most

\[
 F_R=C(P_R-1)+G D_R\left(S-\sum_{r\in R}a_r^2\right).
 \tag{HB2}
\]

Uniform cardinality bounds need a comparison over all possible hub primes.
Pad their weights with zeros to `k` coordinates, let `a0=1/(q0-1)`, and
suppose `k a0^2<=S`. On the cube `[0,a0]^k`, differentiating the expression
in (HB2), with `P_(−i)=prod_(j!=i)(1+a_j)`, gives

\[
 \partial_iF\ge P_{(-i)}
       \left[C-2G a_0(1+a_0)(1+2a_0)^k\right].
\]

When the bracket is positive, the maximum is bounded by substituting the
first `k` allowed primes in increasing order: the `i`th actual hub prime
is at least the `i`th allowed prime. Both cube and derivative conditions
are checked exactly in the certificate. If deleting the hubs leaves a
matching instead, use `sum_B W_B^2<=2(1+a0/2)^2 S` in (HB1); this coarser
expression is increasing in every hub weight without subtracting hub squares.
The resulting sufficient cases are:

| Head and tail cutoff | Deleted hubs | Remaining graph | Loss upper bound |
|---|---:|---|---:|
| Complete star head, `q>73` | at most 8 | independent | `<0.983593` |
| Complete star head, `q>73` | at most 1 | matching | `<0.987571` |
| Arbitrary `{3,5,7}` head, `q>=37` | at most 6 | independent | `<0.988959` |
| Arbitrary `{3,5,7}` head, `q>=37` | at most 2 | matching | `<0.903742` |

The hubs can have arbitrarily many neighbours. Internal edges among hubs
are allowed; for example, the first case permits every residual prime to
be adjacent to all eight hubs. These are structural exclusions with no
bound on exponents or total prime support.

**Sharper prime-square certificate.** The same verifier additionally sieves
to 40000 and independently checks the prime list by trial division. The
4182 primes in `(73,40000]` have
`sum ceil(10^12/(q-1)^2)=2387697612`. Bounding the remaining primes by all
odd integers gives

\[
 \sum_{q>73,\ q\text{ prime}}\frac1{(q-1)^2}
 \le\frac{2387697612}{10^{12}}+\frac1{1600000000}+\frac1{80000}
 =\frac{2400198237}{10^{12}}.                           \tag{GS1}
\]

For cutoffs below 73 add the finitely many omitted prime squares exactly.
The earlier 4000 certificate is retained. All new graph comparisons are
ordinary proofs with exact rational constants; they are not new Lean
formalizations. Project search and arXiv searches combining covering systems
with forest, graph, and odd distinct covering found no exact dominating
star-forest or hub result in the searched scope; no literature priority is
claimed. The unrestricted problem still requires arbitrary head geometry and
arbitrary tail interactions.

#### Every full star completion needs positive mixed-tail capacity

Use singleton blocks for arbitrary tails, and choose every threshold to be
`3/4`. By (BS4) and (BS6), `E<59/75`. Hence a full cover must satisfy

\[
 \sum_{\omega(t_d)\ge2}4^{\omega(t_d)}
      \mathbb E_{\mu_b}\left[h_d\prod_{q\mid t_d}r_{q,d}\right]
       >\frac{16}{75}.                                 \tag{BS8}
\]

Replacing each remaining cylinder fraction by `q^(-v_q(t_d))` gives the
weaker necessary inequality
`sum_(omega(t_d)>=2)4^(omega(t_d))mu_b(h_d=1)/t_d > 16/75`.
When every tail part has at most two distinct prime factors, this requires
`sum_(omega(t_d)=2)mu_b(h_d=1)/t_d > 1/75`. Grouping by tail part and
using (BS7) then gives the graph-only necessary condition

\[
 \sum_{\{q,r\}\in\mathcal E}\frac1{(q-1)(r-1)}
       >\frac{2}{1095}.                                \tag{BS9}
\]

These are actual-residue constraints, with single-prime tail classes already
accounted for. They impose no unjustified survival requirement on the
exceptional ternary branch. In particular, any full star completion must
have a tail prime with at least two distinct graph neighbours.

#### Exact constants and the remaining unrestricted obligation

The [standard-library verifier](../docs/reports/erdos7-odd-covering/verify_star_block_obstruction.py)
reconstructs the [fixed rational certificate](../docs/reports/erdos7-odd-covering/star_block_obstruction_certificate.json),
including `176.921<K_0<176.922`, `C_0<73/10`, and all budget comparisons.
For the prime tail it sieves to 4000: the 529 primes in `(73,4000]` give
`sum ceil(10^9/(q-1)^2)=2363054`. Above 4000, overcount by odd integers
`q=2j+1`, `j>=2000`, and use the decreasing integral bound to obtain

\[
 \sum_{q>73,\ q\text{ prime}}\frac1{(q-1)^2}
 \le\frac{2363054}{10^9}+\frac1{16000000}+\frac1{8000}
 =\frac{4976233}{2000000000}<\frac1{400}.
\]

The small crossing-budget condition does not follow from star geometry
alone. Add the 210 classes `0 mod qr` for the 21 primes `79<=q<r<=181`.
This remains a noncover: use any star head survivor and tail coordinates
all equal to one. Yet exact arithmetic gives `sum 1/(qr)>14/1000>1/75`.
There are no single-prime tail classes in this example, so even the actual
singleton-block crossing budget exceeds the sufficient threshold.

Here the exceeded threshold is the uniform simplified bound `16/75`.
The full criterion itself still certifies this example: its actual `E=0`
and `J=16 sum 1/(qr)<1`. The example only excludes imposing the simplified
small-budget condition on every extension.

For unrestricted #7, one must still handle arbitrary heads and interactions
between tail blocks. A minimal hypothetical cover with `T>1` has nonempty
actual head survivors, but this fact supplies neither a controlled head law
nor small `E+J`. When `T=1`, arbitrary 73-smooth covers must separately be
excluded. The present block and star results have ordinary mathematical
proofs and exact numerical certificates; they are not complete Lean theorems.


### Arbitrary-head transfer by the joint-load invariant

Let `Q` be a positive integer, `p` a prime not dividing `Q`, and `H ≥ 1`.
A layout chooses one residue `b_d mod d` for each divisor `d | Q`, including
`d = 1`; write `L_b(x) = ∑_{d | Q} 1_{x ≡ b_d (mod d)}` and
`Γ_Q(μ) = max_b E_μ L_b²`. Different layout residues need not be compatible.
All probability spaces below are finite. No independence of the coordinates
of the old probability `μ` is assumed.

**One-prime estimate.** Put

\[
 S_p(H)=\sum_{e=1}^H p^{-e},\qquad
 A_p(H)=\sum_{e=1}^H(2e+1)p^{-e}.
\]

For `0 ≤ δ < 1`, let `K(y | x)` be a probability kernel from `Z/QZ` to
`Z/p^H Z` with

\[
 K(y\mid x)\le\frac{1}{(1-\delta)p^H}.
\]

The joint probability `ν(x,y) = μ(x)K(y | x)`, interpreted by CRT, satisfies

\[
 \boxed{\Gamma_{Qp^H}(\nu)
 \le\Gamma_Q(\mu)\left(1+\frac{A_p(H)}{1-\delta}\right).}
 \tag{T1}
\]

For any actual family with at most one forbidden residue for each new
modulus `dp^e`, `d | Q`, `1 ≤ e ≤ H`, let `α(x)` be the fraction of the
uniform new-prime fibre covered by these classes. Then

\[
 \boxed{\mathbb E_\mu\alpha^2\le\Gamma_Q(\mu)S_p(H)^2.}
 \tag{T2}
\]

**Proof.** Fix a full layout and group its moduli by `e = v_p(d)`.
Each group gives an old layout load `L_e(x)`, because the map `d ↦ dp^e`
is injective on divisors of `Q`. For any `e,f`, Cauchy–Schwarz gives

\[
 \mathbb E_\mu[L_eL_f]
 \le\sqrt{\mathbb E_\mu L_e^2\,\mathbb E_\mu L_f^2}
 \le\Gamma_Q(\mu).
 \tag{T3}
\]

Expand the full squared load into ordered pairs of classes. When `e=f=0`,
the new coordinate is unrestricted, so normalization of `K` leaves the old
expectation unchanged. Otherwise the intersection of the two new-prime
conditions is empty or a single cylinder modulo `p^{max(e,f)}`. Its conditional
probability is at most `p^{-max(e,f)}/(1−δ)`. This bound holds separately for
every pair, even when their new-prime residues depend on their old moduli.
After applying it, sum the old indicators and use (T3). There are exactly
`2t+1` ordered exponent pairs with maximum `t`. This proves (T1).

The weighted rectangle theorem described after (W1) supplies the more general
formal estimate. A constant prefix cap `M_t=p^{-t}/(1−δ)` recovers this
coefficient; Mathlib's modular interval count supplies that cap from the
pointwise bound on `K`. The divisor-layout embedding by CRT, the maximum
defining `Γ`, and construction of the capped kernel remain separate
formalization obligations.

For the actual forbidden classes, their old conditions give partial loads
`F_e`; distinct moduli ensure at most one class per old divisor in each group.
Complete these partial loads to layouts. A union bound in each uniform fibre
and (T3) then give

\[
 \alpha(x)\le\sum_{e=1}^H p^{-e}F_e(x),\qquad
 \mathbb E_\mu\alpha^2
 \le\sum_{e,f=1}^H p^{-e-f}\mathbb E_\mu[F_eF_f]
 \le S_p(H)^2\Gamma_Q(\mu).
\]

This proves (T2), with all old cofactors and arbitrary exponents retained.

**Capped deletion.** For `0 < δ ≤ 1/2`, use the BBMST kernel. In a fibre
with `α ≤ δ`, give zero weight to forbidden points and multiply uniform
weight at every other point by `1/(1−α)`. In a fibre with `α > δ`, multiply
uniform weight by `(α−δ)/(α(1−δ))` on forbidden points and by `1/(1−δ)`
on other points. Both cases are normalized and obey the cap in (T1).
The first case has `α < 1`, and the second has `α > 0`; no division by zero
is used. Completely forbidden fibres, where `α=1`, keep their original mass.

If `B` is the union of the new forbidden classes, then

\[
 \nu(B)=\frac{\mathbb E_\mu(\alpha-\delta)_+}{1-\delta}
 \le\frac{\mathbb E_\mu\alpha^2}{4\delta(1-\delta)}
 \le\frac{\Gamma_Q(\mu)S_p(H)^2}{4\delta(1-\delta)}.
 \tag{T4}
\]

Here `(t−δ)_+ ≤ t²/(4δ)` follows from `(t−2δ)² ≥ 0` when `t ≥ δ`;
it is immediate otherwise. If `R` denotes the complete old survivor set and
`R'=(R×Z/p^H Z)\B`, preservation of the old marginal gives

\[
 \nu(R')\ge\mu(R)-\nu(B).
 \tag{T5}
\]

The physical probability is **not** conditioned on complete survival at each
step. Its mass on previously forbidden points is permitted; (T5) separately
tracks the mass on the complete survivor set. Thus zero-survival fibres cause
no hidden positivity assumption and do not change the kernel cap.

**Iteration.** Start with any probability on complete head survivors having
`Γ ≤ C`, so its initial survivor mass is one. Index all subsequent primes in
increasing order, padding omitted primes by unused coordinates if needed. Put
`G_0=C`, `s_0=1`, and, at each subsequent prime `p`, define

\[
 a_p=\frac{3p-1}{(p-1)^2},\qquad
 G'=G\left(1+\frac{a_p}{1-\delta}\right),\qquad
 s'=s-\frac{G}{4\delta(1-\delta)(p-1)^2}.
\]

Since `S_p(H) ≤ 1/(p−1)` and `A_p(H) ≤ a_p`, induction using (T1), (T4)
and (T5) gives `Γ ≤ G` and complete survivor mass at least `s`.
If the next `s'` is positive, `F=G/s` obeys the exact scalar recurrence

\[
 \boxed{F'=\frac{(1+a_p/(1-\delta))F}
 {1-F/[4\delta(1-\delta)(p-1)^2]}.}
 \tag{T6}
\]

Every denominator must be strictly positive. This is BBMST's recurrence,
now with an arbitrary correlated head and `C=Γ_head(μ)` as its seed.
The kernel construction and scalar continuation are reused from
[BBMST, §2 and §6](../Library/Arith/balister2018covering.md); (T1)–(T3)
justify using the joint-layout seed in place of a sum of separate cylinder maxima.
The searched project congruence declarations, pinned Mathlib probability and
combinatorics files, and these BBMST papers supplied the component inequalities,
but no exact joint-layout head theorem was identified. This bounded search does
not establish literature priority. The argument here is not a Lean formalization.

### Exact feasibility of a complete-survivor kernel with cylinder caps

Let `X` be a finite old survivor carrier, `Y=Z/p^H Z` with prime `p` and
`H≥1`, and `U` its uniform law. Let `R⊆X×Y` be the actual complete survivor
relation and put `s(x)=U(R_x)`. Fix an old probability `μ` and `C≥1`.
There exists a law supported on `R`, with old marginal `μ` and conditional
cylinder masses at most `C p^{-e}` at every depth `1≤e≤H`, if and only if

\[
 s(x)\ge1/C\quad\text{for every }x\text{ with }\mu(x)>0.
\]

For necessity, sum the depth-`H` singleton caps over `R_x`. For sufficiency,
use the uniform conditional law on `R_x`; a depth-`e` cylinder has ambient
mass `p^{-e}`, and restriction followed by normalization costs at most `C`.
This is a condition on actual fibre survival, not just the new marginal.

If the old marginal may instead be any `μ'≤Dμ`, for `D≥1`, the exact
criterion becomes

\[
 \mu\{x:s(x)\ge1/C\}\ge1/D.
\]

Necessity follows because `μ'` is supported on this set and has total mass
one. For sufficiency, restrict `μ` to this set and normalize, then use the
same conditional construction. These are elementary finite deductions;
no new Lean declaration is required.

The positivity premise can fail in a complete legal `{3,5}` family.
At every common height `H≥4`, forbid residue zero at all pure powers.
For the four mixed moduli `3^i·5`, `1≤i≤4`, forbid the CRT class
`(1 mod 3^i, i mod 5)`; at every other mixed divisor forbid residue zero.
These rules assign one class to every nonunit divisor, without duplication.
The pure ternary survivor set `X` comprises roots `1,2 mod 3`. Above every
`x≡1 mod 81`, the pure-5 class removes root zero and the four special
mixed classes remove roots `1,2,3,4 mod 5`. Thus that entire fibre is empty.
Its uniform `X`-mass is exactly `(1/81)/(2/3)=1/54` at every `H≥4`.
Nevertheless `x≡2 mod 3`, `y≠0 mod 5` always survives, so the complete
family has survivors. Hence a complete-survivor extension preserving the
uniform old marginal need not exist, even without a cylinder cap.

The [exact finite verifier](../docs/reports/erdos7-odd-covering/verify_fibre_coupling_obstruction.py)
checks all 24 nonunit divisors at height four and all relevant pairs in the
period `81·625=50625`, yielding 22000 complete survivors and exactly one
empty old survivor fibre among 54. The all-height assertion follows from
the reductions modulo 81 and 5 above. This result explains why the capped
deletion route (T4) tracks complete survivor mass separately and why a
strict survivor kernel must sometimes change the old marginal. Neither
argument establishes the universal Γ73 bound.

### Transfer retaining the actual forbidden-fibre geometry

Extend `Γ_Q` homogeneously to finite positive measures. For an arbitrary
normalized kernel `K_x` on `Z/p^H Z`, set

\[
 M_t(x)=\max_{b\bmod p^t}K_x(y\equiv b\pmod{p^t}).
\]

The joint-load argument gives the stronger, measure-dependent estimate

\[
 \boxed{\Gamma_{Qp^H}(\mu K)
 \le\Gamma_Q(\mu)+\sum_{t=1}^H(2t+1)\Gamma_Q(M_t\mu).}
 \tag{W1}
\]

Indeed, for exponent groups `(e,f)` with `max(e,f)=t`, each nonempty current
intersection is a depth-`t` prefix and has conditional mass at most `M_t(x)`.
If `A_e,A_f` are their complete old loads, weighted Cauchy–Schwarz gives
`∫M_t A_e A_f dμ≤Γ_Q(M_t μ)`. There are `2t+1` such ordered groups.
The old-old contribution remains at most `Γ_Q(μ)`. All old cofactors,
including 1, remain in these loads.

The finite weighted rectangle estimate is formalized in
[PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le](../D5/S3/Arith/Congruence/PrimeRectangleTransfer.lean).
For arbitrary finite `X,I`, nonnegative old weights `μ(x)` and coefficients
`A(e,i,x)`, it takes a normalized nonnegative kernel `K(x,y)` and bounds
on each actual single-prefix mass by `M_t(x)`. If the zero layer has second
moment at most `G_0`, and each layer `e≤t` has its own second-moment bound `G(t,e)`
under the weighted measure `μ M_t`, then the actual modular rectangle load
has second moment at most

\[
 G_0+\sum_{t=1}^H\left[\sum_{e=0}^tG(t,e)+tG(t,t)\right].
\]

Taking `G(t,0)=D_t` and `G(t,e)=G_t` for positive `e` gives
`D_t+2tG_t` at depth `t`; setting all layer bounds equal recovers (W1).
Keeping the zero layer distinct is the formal ingredient used in (ZG2).

The theorem includes `H=0`, permits correlation between `x` and the kernel,
and does not require normalization of `μ`. It proves intersection bounds
from single-prefix bounds, derives nonnegativity of the prefix envelope,
and counts the exponent pairs by induction. Its compiled axiom closure
contains only `propext`, `Classical.choice` and `Quot.sound`.
It does not define the maximum `Γ`, construct `K`, or supply the CRT
embedding of a divisor layout; those are still outside this Lean theorem.

For the BBMST kernel take the current base law `U` to be uniform on
`Z/p^H Z`, with **all** new forbidden classes, including pure powers, in
the actual union `B_x`. Put

\[
 \alpha(x)=U(B_x),\quad \theta(x)=\min\{\alpha(x),\delta\},\quad
 m_t(x)=\min_{b\bmod p^t}U(B_x\cap\{y\equiv b\pmod{p^t}\}).
\]

The outside density is `1/(1−θ)` and the inside density is
`(α−δ)_+/(α(1−δ))`. Subtracting these densities and summing on a prefix
proves the exact formula

\[
 M_t(x)=\frac{p^{-t}-(\theta/\alpha)m_t(x)}{1-\theta},
 \tag{W2}
\]

where `(θ/α)m_t` is defined as zero at `α=0`. The formula also applies
at `α=1`. In particular, with `c_t=p^{-t}/(1−δ)`,

\[
 c_t-M_t=
 \frac{p^{-t}(\delta-\theta)}{(1-\delta)(1-\theta)}
 +\frac{\theta m_t}{\alpha(1-\theta)}\ge0.
 \tag{W3}
\]

Since every old layout has load at least one,
`Γ_Q(M_t μ)≤c_t Γ_Q(μ)−E_μ(c_t−M_t)`. Consequently

\[
 \Gamma_{Qp^H}(\mu K)
 \le\Gamma_Q(\mu)\left(1+\frac{A_p(H)}{1-\delta}\right)
       -\sum_{t=1}^H(2t+1)\mathbb E_\mu(c_t-M_t).
 \tag{W4}
\]

The second term of (W3) measures forbidden occupancy in every depth-`t`
prefix and can be positive even when `α≥δ`. The weighted estimate (W1)
additionally retains its correlation with the old test loads.
For the actual ending-event charge `b=(μK)(B)`, the first term alone gives
the joint inequality

\[
 \Gamma_{Qp^H}(\mu K)+A_p(H)b
 \le\Gamma_Q(\mu)\left(1+\frac{A_p(H)}{1-\delta}\right)
       +\frac{A_p(H)(\mathbb E_\mu\alpha-\delta)}{1-\delta}.
 \tag{W5}
\]

To obtain it use
`E(δ−α)_+=δ−Eα+(1−δ)b` in (W3)–(W4).

The geometry in (W2) can be computed without counting nested exclusions
twice. Write the actual union as `⋃_j A_j×J_j`, combining equal old
cylinders, and order proper old supersets before subsets. Replacing `J_j`
by `J_j\⋃_{i:A_j⊊A_i}J_i` preserves this union. A point removed from one
rectangle lies in a rectangle with a strictly larger old cylinder, and
this finite ascent terminates. For irredundant full congruence classes,
intersecting current prefixes from these ancestors lie strictly inside the
child prefix; their maximal members are disjoint, so their masses subtract
by finite additivity. This is the local prefix-packing calculation behind
the Kraft inequality.

Both `α` and `m_t` must refer to that same actual union. An upper bound
on `α` supplies no lower bound on `m_t`; a base already conditioned away
from pure-power classes cannot use the numerical `p^{-t}` factors unchanged.
The project’s `CompatibleResidueJointImage` and `FiniteCompatibleCrt`
provide the congruence compatibility statements, and pinned Mathlib's
`InformationTheory/Coding/KraftMcMillan.lean` supplies prefix packing.
The rectangle component of (W1) is formalized as stated above. The exact
clipped-kernel formula (W2), its consequences (W3)–(W5), and the full
divisor-layout embedding have not been formalized in Lean.
A uniform accumulated improvement yielding Γ73 is ruled out by the star family.

### Forced loss on an actual pure-prime forbidden root

Let Q=3^a M with a>=1 and gcd(3,M)=1. Let U be uniform on Z/QZ,
B the actual forbidden union, and s=U(B^c)>0. Suppose B contains an
actual class A=r mod 3. For every complete test layout L, let T be its
subload indexed by the divisors of M, including 1. Then L>=T>=1 and the
law of the M-coordinate conditional on A is uniform.

Write

    Z_M = sum_{d|M} 1/d = product_{p|M}(1+S_p),
    C_M = sum_{d,e|M, gcd(d,e)=1} 1/(de)
        = product_{p|M}(1+2S_p),
    S_p = sum_{j=1}^{v_p(M)} p^(-j).

Every diagonal term in E(T^2) has mass 1/d, and every pair of distinct
coprime test moduli intersects with mass 1/(de), independently of the
chosen residues. All remaining intersections have nonnegative mass.
Therefore every complete cofactor layout satisfies

    E_U(T^2) >= Z_M+C_M-1.                         (1)

This is a lower bound on all complete layouts, not the maximum Gamma.
Since L^2>=1 on B\A as well, the total forbidden loss obeys

    integral_B L^2 dU >= U(B)+(Z_M+C_M-2)/3.       (2)

The ordinary complete-layout uniform maximum is

    K_Q = product_{p|Q}[1+sum_{j=1}^{v_p(Q)}(2j+1)p^(-j)].

Combining (2) with this exact maximum gives a parameterized survivor bound

    Gamma(U conditioned on B^c)
      <= 1+[K_Q-1-(Z_M+C_M-2)/3]/s.               (3)

The extra loss is positive whenever M>1. It strengthens the bound using
only the total deleted mass. It is valid for arbitrary finite exponents
and all test cofactors, with no alignment assumption.

#### Sharpness of the cofactor lower bound

For P=prime support of M, suppose p-1>=2^(|P|-1) for every p in P.
This includes P contained in {5,7,11}. For each p, assign different nonzero
digits c_p(S) in {1,...,p-1} to the supports S contained in P with p in S.
For a divisor d with support S and exponent e>0 at p, choose by CRT

    a_d = c_p(S) p^(e-1) mod p^e.

Two such p-prefixes of different depths are disjoint; prefixes of the same
depth and different support labels are also disjoint. Thus distinct
divisors sharing a prime have disjoint test classes. Coprime pairs have
the forced intersection 1/(de). This constructs a complete layout attaining
(1), so its lower bound is exact for arbitrary heights on {5,7,11}.

#### Comparison with the current head estimates

The existing same-family density bounds imply

    s_357 >= 5/42,   s_35711 >= 1591/30240.

For example s_35>=1/4 follows from the two-root budget; subsequent factors
are (5/6)(1-(15/7)/5) and (9/10)(1-(1649/360)/9).

The numerator of (3) is increasing in every finite height: for an exponent
increment in M, K-local factors dominate both Z-local and C-local factors,
and the K increment has coefficient 2j+1>=3. Hence the infinite-height
values give valid bounds simultaneously, without mixing incompatible maxima.

For support {3,5,7}:

    K_Q <= 35/4, Z_M ->35/24, C_M ->2,
    extra loss ->35/72,
    resulting universal bound from (3): 3721/60.

For support {3,5,7,11}:

    K_Q <=231/20, Z_M ->77/48, C_M ->12/5,
    extra loss ->481/720,
    resulting universal bound from (3): 300421/1591.

These improve the bare deleted-mass bounds 661/10 and 320623/1591,
respectively. They do not improve the existing survivor bounds 481/12
and 4939031/47730. The absent-modulus-3 case uses the already stronger
existing unsplit branch. No new best head constant results.

#### Why this does not automatically improve the pure-survivor base

Suppose the actual family contains 0 mod p for each p in P, and let nu
be the product of the pure-prime survivor laws. Choose every nonunit test
residue to be 0. Every nonunit test cylinder then lies in an actual pure
forbidden root, so the complete test load is identically 1 on nu's support.
For any additional mixed forbidden union D of positive nu-mass,

    integral_D L^2 dnu = nu(D).

Thus no positive extra loss valid for every test layout can be imported
into this already conditioned base. A useful improvement there must
couple the extra loss to how close the test layout is to maximizing its
moment. Such a uniform high-load tradeoff is not established here.

These are ordinary mathematical proofs. No new Lean declaration is supplied.

### Actual forbidden-class projection and its open quantitative input

A second-moment projection retains the actual intersections supplied by CRT.
Let `rho` be any finite positive measure, `B` the union of actual forbidden
classes `A_i`, and `s=rho(B^c)>0`. For a complete test load `L`, define

\[
 G_{ij}=\rho(A_i\cap A_j),\qquad
 c_i=\int L\,1_{A_i}\,d\rho.
\]

For every real vector `z`, integrating
`(L−sum_i z_i 1_{A_i})²≥0` over `B` gives

\[
 \int L^2\,d(\rho|_{B^c}/s)
 \le\frac{\int L^2d\rho-2z^Tc+z^TGz}{s}.
\]

This is ordinary finite least-squares projection. It permits dependent
forbidden classes and either sign of `z`; there is no assumed alignment
between their residues and the test layout. Under a full uniform law,
CRT computes each Gram entry and each test/forbidden intersection as zero
or `1/lcm(d,e)`. Under a weighted root law, the actual weighted intersections
must be retained. The matrix is positive semidefinite because
`z^TGz=integral(sum_i z_i 1_Ai)²≥0`.

Using this identity as a quantitative upper estimate requires control of
the subtraction and the test load's deficit from the unconditioned maximum,
for the actual family and every complete test layout. The star family rules
out obtaining the proposed universal Γ73 bound by this method. These
projection identities are reused as tools; no new Lean wrapper is supplied.

### Exact saturation despite actual mixed deletion

For every integer Q>1, prime p not dividing Q, and H>=1, put N=p^H.
Use the actual old forbidden class 1 mod Q and old survivor law mu=delta_0.
Use the single actual new forbidden mixed class 0 mod QN. These moduli are
distinct and the true combined least common multiple is QN. On the only
old point charged by mu, the forbidden fibre B is the singleton {0} in
Z/NZ. Thus alpha=1/N. Choose any 0<delta<alpha, and use the BBMST clipped
kernel K. Its mass at y is

    K(0)=(alpha-delta)/(1-delta),
    K(y)=1/[N(1-delta)] for y != 0.

The actual mixed ending charge is b=K(0)>0. For every 1<=t<=H a prefix
in root 1 avoids B, so m_t=0 and

    M_t=c_t=1/[p^t(1-delta)].

Consequently Gamma_Q(M_t mu)=c_t Gamma_Q(mu), with Gamma_Q(mu)=tau(Q)^2.
This already excludes a strictly positive universal rebate based only on
positive b, alpha>=delta, or positive distortion, without an additional
old-law or test/forbidden-overlap assumption.

The entire transfer inequality is also sharp. For every divisor d of Q,
choose the exponent-zero test residue to be 0 mod d. For every 1<=e<=H,
choose the residue at divisor d p^e by CRT to be 0 mod d and 1 mod p^e.
All old cofactors occur. On the support of mu the literal test load is

    L(y)=tau(Q) [1+sum_{e=1}^H 1_{y=1 mod p^e}].

The selected prefixes are nested, and their K-masses equal c_e. Expanding
the square assigns coefficient 2t+1 to pairs whose maximum exponent is t.
The concrete layout therefore gives

    Gamma_{QN}(mu K)
      >= tau(Q)^2 [1+sum_{t=1}^H (2t+1)c_t].

W1 gives the reverse inequality, hence equality. This is an ordinary
mathematical proof using the existing transfer theorem, not new Lean.

There is also strictly positive chi-square distortion energy:

    E_U[(dK/dU-1)^2]
      = delta^2(1-alpha)/[alpha(1-delta)^2] > 0.

Relative entropy D(K||U) is strictly positive because K differs from U.
Neither scalar energy nor entropy forces a test-layout penalty here.
The test load is small on the actual forbidden singleton and maximized
along a different p-adic path; alignment must not be assumed.

The old law is a Dirac law supported on actual survivors. It is not uniform
on all old survivors. Thus this does not refute stronger bounds restricted
to a uniform head law, nor bounds requiring quantitative regularity.

For any finite old layout family, c>=w>=0 also gives the exact identity

    c Gamma(mu)-Gamma(w mu)
      = min_lambda {c[Gamma(mu)-E_mu L_lambda^2]
                    +E_mu[(c-w)L_lambda^2]}.

This separates old-layout suboptimality from weighted loss. A positive
improvement needs a lower bound on their sum for every old layout. It is
an algebraic identity, not a proposed new Lean declaration.

#### Verification

[The saturation verifier](../docs/reports/erdos7-odd-covering/verify_actual_union_saturation.py)
uses rational arithmetic and explicit exceptions. It verifies
the prefix masses, common nested layout, full transfer equality, positive
charge and energy for seven choices, with arbitrary old prime-power factors
among the examples. Three H=1 cases exhaust all 891 literal layouts in
total. Finite checks support the displayed construction; the proof above
covers arbitrary Q,p,H.

#### Literature boundary

BBMST, arXiv:1811.03547, Lemma labelled lem:distortion, proves
E_i Delta_i <= 2 sum_{d in D_i} nu(d)/d for
Delta_i=max(0,log(Pr_i/Pr_0)). Its use is a lower bound on uniform uncovered
density. It does not prove positive correlation with arbitrary test loads.
BBMST, arXiv:1901.11465, subsection 'Constructing the measure Pr_5', optimizes
nonuniform survivor masses by linear programming in the squarefree setting.
It provides a route to optimize the old law, not a universal rebate for the
fixed arbitrary law in this example.

### Exact continuation from the conditional 73-head seed

[The finite continuation verifier](../docs/reports/erdos7-odd-covering/verify_finite_continuation.py)
uses Python 3.9+ standard-library integer and rational arithmetic. It starts at
`p_21=73`, `F_21=138877/1000`, checks each rational choice `0<δ≤1/2`,
checks positivity of every denominator in (T6), and rounds each resulting `F`
upward to a grid of `10^−12`. It checks 13,141,979 successive prime steps and
obtains, at `k=13,142,000`, `p_k=239,622,407`,

\[
 F_k\le\frac{860976507525503444783}{250000000000}
 <\frac{430488883362679218496182453443671999019139}
 {125000000000000000000000000000000}
 \le k(\log k+\log\log k-3)^2.
\]

The second rational is a lower bound obtained from positive 24-term `atanh`
series for logarithms, with a checked positive bracket before squaring.
Every finite check is performed afresh; no checkpoint or resume data is used.
Reproduction from the repository root:

```sh
python3 docs/reports/erdos7-odd-covering/verify_finite_continuation.py
```

BBMST Theorem 6.1 continues (T6) from this stopping inequality with `δ=1/2`.
Its proof uses only that recurrence, the positive current survivor mass and the
published lower bound for the `k`th prime. These hypotheses have exactly the
same form here. For any finite number of further primes the survivor mass
therefore stays positive. If the given family ends before the displayed
endpoint, the already checked positive denominators suffice.

Consequently **Γ73 implies the unrestricted negative answer to Erdős #7**.
The finite arithmetic and the general-head transfer are established as stated;
the universal Γ73 existence bound is false by the star family. This conditional result
supplies no covering counterexample and no unrestricted proof by itself.

### Quantitative extension of the old prime powers

Let `P` be a finite prime set and
`Q₀=∏_{p∈P}p^{H_p}`, `Q=∏_{p∈P}p^{K_p}`, where `K_p≥H_p≥1`.
Take any distinct-modulus family of nonunit divisors of `Q`. Suppose `μ`
is a probability avoiding every actual class whose modulus divides `Q₀`,
and `Γ_{Q₀}(μ)≤C`. Write

\[
 n_p=K_p-H_p,\quad k_p=H_p+1,\quad
 u_p=\sum_{t=1}^{n_p}p^{-t},\quad
 v_p=\sum_{t=1}^{n_p}(2t-1)p^{-t},\quad
 D_S=\prod_{p\in S}k_p,
\]
\[
 B=\prod_{p\in P}\left(1+\frac{2u_p}{k_p}+\frac{v_p}{k_p^2}\right),
\qquad
 \lambda=\sum_{\varnothing\ne S\subseteq P}\left(\prod_{p\in S}u_p\right)
 \min\left\{\frac{\sqrt C}{D_S},\frac{C}{D_S^2},
                    \frac{C-1}{D_S^2-1}\right\}.
\]

**Height-lifting theorem.** If `λ<1`, the complete family has a survivor,
and a probability `μ'` on its complete survivors satisfies

\[
 \boxed{\Gamma_Q(\mu')\le\frac{CB-\lambda}{1-\lambda}.}
 \tag{H1}
\]

**Proof.** Fix nonempty `S⊆P`. Let `F_S` be a partial core layout whose
moduli have exponent `H_p` at each `p∈S`. Project each selected class to all
`D_S` divisors obtained by independently lowering these exponents. All projected
moduli are distinct: the outside exponents identify the original modulus and
the inside exponents identify the projection. Complete the resulting selection
to a full core layout. Its load `L` satisfies `L≥D_S F_S` and `L≥1`. Thus

\[
 \mathbb E_\mu F_S^2\le C/D_S^2,\qquad
 \mathbb E_\mu F_S\le
 \min\{\sqrt C/D_S,\ C/D_S^2,\ (C-1)/(D_S^2-1)\}.
 \tag{H2}
\]

The first first-moment bound is Cauchy–Schwarz. The second uses the integral
inequality `F_S≤F_S²`. For the third, if `F_S=0` then `L²−1≥0`, and otherwise
`L²−1≥D_S²F_S²−1≥(D_S²−1)F_S`. For `S=∅` only the second-moment bound is
needed, with `D_∅=1`.

Extend `μ` uniformly over fibres of the reduction `Q→Q₀`, giving `ν`.
Group the actual future moduli by their excess vector
`t_p=max(v_p(d)−H_p,0)`. For fixed `t`, the reduced modulus `gcd(d,Q₀)`
determines `d` uniquely, so the reduced classes form a partial layout of the
kind in (H2), with `S=supp(t)`. Its conditional fibre mass is at most
`(∏p^{−t_p})F_t(x)`. Summing (H2) over nonzero excess vectors bounds the
union of all future excluded classes by a mass `b≤λ`.

For an arbitrary full test layout on `Q`, group its classes by the same
excess vectors, including `t=0`. For two fine moduli `d,e`, a compatible
intersection has modulus `lcm(d,e)` and occupies a fraction

\[
 \frac{\gcd(\operatorname{lcm}(d,e),Q_0)}{\operatorname{lcm}(d,e)}
 =\prod_p p^{-\max(t_p,s_p)}
\]

of a compatible coarse fibre; an incompatible intersection has mass zero.
Consequently (H2) and Cauchy–Schwarz bound the contribution of two groups by

\[
 C\frac{\prod_p p^{-\max(t_p,s_p)}}{D_{\operatorname{supp}(t)}
                                               D_{\operatorname{supp}(s)}}.
\]

Summing factorizes over primes. The pair `(0,0)` contributes one, the two
zero/nonzero cases give `2u_p/k_p`, and the positive/positive cases give
`v_p/k_p²`, because there are `2h−1` positive exponent pairs with maximum `h`.
Hence `Γ_Q(ν)≤CB`. This fibre count does not assume independent old coordinates
or an integer lift independent of the coarse residue.

Finally condition `ν` on avoiding every future forbidden class. The old
forbidden classes already have zero mass. Every full test load is at least
one, so

\[
 \mathbb E_{\mu'}L^2
 \le\frac{CB-b}{1-b}
 \le\frac{CB-\lambda}{1-\lambda}.
\]

The last inequality uses `CB≥1`. The new coarse marginal is proportional to
`μ(x) Pr(future survival | x)`. A completely killed fibre receives mass zero;
no preservation of all coarse fibres is assumed. This proves (H1).

**Finite sufficient targets.** Uniformly over all future heights,
`u_p≤1/(p−1)` and `v_p≤(p+1)/(p−1)²`. Take the twenty odd primes through 73
and common initial height `H`. If `e_j` is the elementary symmetric polynomial
in the twenty numbers `1/(p−1)`, valid majorants are

\[
 B_H=\prod_{p\in P}\left(1+\frac{2}{(H+1)(p-1)}+
                         \frac{p+1}{(H+1)^2(p-1)^2}\right),\qquad
 \lambda_H(C)=(C-1)\sum_{j=1}^{20}\frac{e_j}{(H+1)^{2j}-1}.
\]

The integer-valued estimate in (H2) suffices for this `λ_H`; no claim that it
is always the smallest of the three bounds is needed. Exact rational arithmetic
gives the following sufficient parameters. Display intervals have width
`10^−12` and contain the exact value `(CB_H−λ_H(C))/(1−λ_H(C))`.

| Hypothetical uniform base bound `C` | Exponent cap `H` | Upper display endpoint |
|---:|---:|---:|
| 128 | 71 | 138.742060391592 |
| 130 | 82 | 138.846691940509 |
| 138 | 543 | 138.875287923953 |
| 138.874 | 141476 | 138.876999989088 |

[The calibration verifier](../docs/reports/erdos7-odd-covering/verify_height_lifting_bounds.py)
checks `λ_H<1`, the strict bound below `138877/1000`, and the display intervals
using rational arithmetic. Run it from the repository root:

```sh
python3 docs/reports/erdos7-odd-covering/verify_height_lifting_bounds.py
```

For example, a theorem that **every** distinct-modulus family with moduli
dividing `∏_{3≤p≤73}p^{71}` admits a survivor probability of `Γ≤128` would,
by (H1) and the preceding transfer, prove the negative answer to unrestricted
Erdős #7. Lower heights in an arbitrary target family can be padded to 71
without adding forbidden classes. The same applies to each other row.
**Every universal finite-base bound in this table is false.** Its cap is at
least 31, so the star construction directly applies and forces `Γ>139.59`,
strictly above each proposed `C`. The calibration remains a correct sufficient
implication; it is not a verification of all residue assignments. The height-lifting argument is not formalized in Lean.

### One-stage smoothing of the height lift

Averaging the highest old digits before the final conditioning improves the
height error to `O(H⁻²)`. Fix a finite prime set `P` and
`1≤h_p≤H_p≤K_p`. Put

\[
 Q_h=\prod_p p^{h_p},\quad Q_H=\prod_p p^{H_p},\quad
 Q_K=\prod_p p^{K_p},\qquad r_p=H_p-h_p,\quad k_p=h_p+1,
 \quad D_S=\prod_{p\in S}k_p.
\]

Take a family of distinct nonunit moduli dividing `Q_K`. Suppose a probability
`μ` on `Z/Q_H Z` avoids every actual class whose modulus divides `Q_H`, and
`Γ_{Q_H}(μ)≤C`. For a vector `n` of nonnegative integers define

\[
 u_p(n_p)=\sum_{t=1}^{n_p}p^{-t},\qquad
 v_p(n_p)=\sum_{t=1}^{n_p}(2t-1)p^{-t},\qquad
 B_h(n)=\prod_p\left(1+\frac{2u_p(n_p)}{k_p}
                            +\frac{v_p(n_p)}{k_p^2}\right).
\]

Use `u_p(∞)=1/(p−1)` and `v_p(∞)=(p+1)/(p−1)²` in the infinite-height
expressions, and set

\[
 E_h(r)=B_h(\infty)-B_h(r),\qquad
 \lambda_h(C)=\sum_{\varnothing\ne S\subseteq P}
 \left(\prod_{p\in S}\frac1{p-1}\right)
 \min\left\{\frac{\sqrt C}{D_S},\frac C{D_S^2},
                         \frac{C-1}{D_S^2-1}\right\}.
\]

**Smoothed height-lifting theorem.** If `λ_h(C)<1`, there is a probability
`μ'` on complete survivors of the whole family such that

\[
 \boxed{\Gamma_{Q_K}(\mu')\le
       \frac{C[1+E_h(r)]-\lambda_h(C)}{1-\lambda_h(C)}.}
 \tag{S1}
\]

For finite `K`, replacing every `∞` by `K_p−h_p` in the corresponding local
sums gives the same assertion with smaller bounds. With `r=0`, (S1) is (H1).
No Γ-minimizing property of the initial law is assumed.

**Proof.** Let `η` be the projection of `μ` to `Q_h`; completing a coarse
layout to an old layout gives `Γ_{Q_h}(η)≤C`. Average `μ` over the additive
group `ker(Z/Q_H Z→Z/Q_h Z)`. Its average `ρ` is the uniform extension of `η`
to `Q_H`. Each translation takes a residue class to another class of the
same modulus, so Γ is translation invariant. It is also convex in the law,
being a maximum of linear expectations. Consequently `Γ_{Q_H}(ρ)≤C`.
The average can reintroduce old forbidden classes above the coarse cap;
these are included in the final conditioning. Classes with moduli dividing
`Q_h` remain avoided because the translations fix the coarse residue.

Extend `ρ` uniformly to `Q_K`, giving `ν`, equivalently the uniform extension
of `η` from `Q_h`. In a full test layout, the squared load from moduli dividing
`Q_H` has expectation at most `C`. Group all moduli by their excess vectors
`t_p=max(v_p(d)−h_p,0)`. The coarse modulus and `t` determine `d`, so each
coarse group is a partial layout to which (H2) applies at cap `h`. The same
CRT intersection count and Cauchy–Schwarz bound each ordered pair of groups by

\[
 C\frac{\prod_p p^{-\max(t_p,s_p)}}
        {D_{\operatorname{supp}(t)}D_{\operatorname{supp}(s)}}.
\]

Two groups are both old exactly when `t_p,s_p≤r_p` for every `p`.
The sum of coefficients over all other ordered pairs is
`B_h(K−h)−B_h(r)≤E_h(r)`. Adding the separately bounded old-old expectation
therefore gives `Γ_{Q_K}(ν)≤C[1+E_h(r)]`. This subtracts only explicit
coefficient sums, not an unknown old expectation.

Now group **all** actual excluded classes above `h`, including the old ones
that averaging reintroduced. Uniform fibre counting and the first-moment
part of (H2) give their total union mass `b≤λ_h(C)`. All remaining actual
classes already have zero mass. Condition once outside this union. Every
test squared load is at least one, so the resulting complete survivor law obeys

\[
 \Gamma_{Q_K}(\mu')\le
 \frac{C[1+E_h(r)]-b}{1-b}
 \le\frac{C[1+E_h(r)]-\lambda_h(C)}{1-\lambda_h(C)}.
\]

The last function is increasing in `b` because `C[1+E_h(r)]≥1`.
This proves (S1), without independent old coordinates or positive survival
in every old fibre.

**Two constants.** If the same initial law has the separately available bounds
`Γ_{Q_H}(μ)≤C_H` and `Γ_{Q_h}(η)≤C_h`, with `1≤C_h≤C_H`, only the old-old
term uses `C_H`. Thus, when `λ_h(C_h)<1`, the proof gives

\[
 \boxed{\Gamma_{Q_K}(\mu')\le
 \frac{C_H+C_hE_h(r)-\lambda_h(C_h)}{1-\lambda_h(C_h)}.}
 \tag{S2}
\]

**Rate.** For fixed `P,C`, choose common `H_p=H`,
`r_p=⌈log_p H⌉` and `h_p=H−r_p` for sufficiently large `H`. The exact tails

\[
 u_p(\infty)-u_p(r)=\frac{p^{-r}}{p-1},\qquad
 v_p(\infty)-v_p(r)=p^{-r}
       \left(\frac{2r}{p-1}+\frac{p+1}{(p-1)^2}\right)
\]

give `E_h(r)=O(H⁻²)` and `λ_h(C)=O(H⁻²)`. Hence (S1) is
`Γ_{Q_K}(μ')≤C+O_{P,C}(H⁻²)`, uniformly over all finite future heights.

**Fixed rational parameters.** Put `k_min=min_p k_p` and
`R=k_min²/(k_min²−1)`. Since `1/(D_S²−1)≤R/D_S²` for nonempty `S`, the
following rational product is a valid replacement for `λ_h(C)`:

\[
 \overline\lambda_h(C)=(C-1)R
       \left[\prod_p\left(1+\frac1{(p-1)k_p^2}\right)-1\right].
\]

For the twenty odd primes through 73, use prime order
`(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73)`.
The following fixed widths give sufficient parameters for (S1). Each upper
display endpoint lies less than `10⁻¹²` above the exact rational bound and
is strictly below `138877/1000`.

| Hypothetical uniform base `C` | Common cap `H` | Width vector `r` in prime order | Upper display endpoint |
|---:|---:|---|---:|
| 128 | 52 | `(3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1)` | 138.556342372564 |
| 130 | 58 | `(3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1)` | 138.599521198059 |
| 138 | 185 | `(5,4,3,3,3,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2)` | 138.872506575675 |
| 138.874 | 3118 | `(10,7,6,5,5,4,4,4,4,4,4,4,3,3,3,3,3,3,3,3)` | 138.876998901712 |

[The smoothed calibration verifier](../docs/reports/erdos7-odd-covering/verify_smoothed_height_lifting.py)
uses exact `Fraction` arithmetic to check the geometric tails, the old-old
coefficient boxes, `0≤λ̄_h<1`, the strict target comparisons and these display
intervals. It uses Python 3.9+ standard library only, with explicit failures
that remain active under `-O`:

```sh
python3 docs/reports/erdos7-odd-covering/verify_smoothed_height_lifting.py
python3 -O docs/reports/erdos7-odd-covering/verify_smoothed_height_lifting.py
```

For example, a universal survivor bound `Γ≤128` at common cap 52 would now
suffice for unrestricted #7 through (S1) and the preceding prime-tail transfer.
**Every universal finite-base bound in this table is false.** All caps are
at least 31, so the star construction forces `Γ>139.59` at each of them.
The squarefree `Γ<138.874` result does not supply the cap-3118 hypothesis.
The verifier checks the numerical implications, not all residue assignments;
the smoothing theorem and its two-constant version have not been formalized
in Lean.

### A four-prime head and a restricted noncoverage theorem

**Theorem.** A finite family of residue classes with distinct odd moduli
greater than one cannot cover the integers if every prime divisor of every
modulus belongs to

\[
 \{3,5,7,11\}\ \cup\ \{p:\ p\text{ prime},\ p\ge67\}.
 \tag{P1}
\]

There is no bound on the exponents, the number of large prime divisors, or the
number of prime divisors of a single modulus. Equivalently, any hypothetical
distinct odd covering must use a modulus divisible by at least one of the
primes from 13 through 61. This is a restricted theorem, not the full conjecture.

The head estimate used to prove it is the following uniform statement.
For any finite distinct-modulus family supported on `{3,5,7,11}`, its complete
survivor set is nonempty, and the uniform survivor probability satisfies

\[
 \boxed{\Gamma\le C_4:=\frac{4939031}{47730}<103.478546.}
 \tag{P2}
\]

**Cylinder profiles.** Fix a finite family and restrict it to each prime
subset `S`. Let `μ_S` be the uniform probability on its complete survivor set,
when nonempty. A profile `c_S(T)>0`, `T⊆S`, with `c_S(∅)=1`, bounds every
cylinder supported on `T` by

\[
 \mu_S(x\equiv a\pmod{\prod_{p\in T}p^{e_p}})
 \le\frac{c_S(T)}{\prod_{p\in T}p^{e_p}}\qquad(e_p\ge1).
\]

Projection to sub-divisors yields the stronger envelope, for nonnegative
exponent vectors `e`,

\[
 u_c(e)=\min_{T\subseteq\operatorname{supp}(e)}
           \frac{c(T)}{\prod_{p\in T}p^{e_p}},\qquad
 R(c)=\sum_{e\ne0}u_c(e),\qquad
 K(c)=\sum_e\left(\prod_p(2e_p+1)\right)u_c(e).
 \tag{P3}
\]

These are sums over all finite nonnegative exponent vectors, providing bounds
uniform in the finite height of the given family. They imply
`∑_{1<d|Q} max_a μ_S(a mod d)≤R(c)` and `Γ_Q(μ_S)≤K(c)`.
For the latter, expand a squared layout load. Compatible pairs intersect in
one cylinder modulo their least common multiple; incompatible pairs contribute
zero. For each prime, `2e+1` ordered exponent pairs have maximum `e`.
No independence of `μ_S` is used.

**Construction of profiles.** Start with `c_∅(∅)=1`, `R(c_∅)=0`.
For a prime `p`, the set `X_p` avoiding the pure `p`-power classes has uniform
density at least `(p−2)/(p−1)`. Indeed the sum of the reciprocals of distinct
positive powers of `p` is at most `1/(p−1)`. Its uniform law `ρ_p` therefore
has cylinder caps `C_p p^{−e}`, where `C_p=(p−1)/(p−2)`.

Suppose profiles and nonempty survivors have been established for `A=S\{p}`.
Start with `ν=μ_A×ρ_p`. Every remaining forbidden class has modulus `dp^e`
with `d>1` supported on `A`. There is at most one class for each pair `(d,e)`,
so their total `ν`-mass is at most

\[
 b_{A,p}=\frac{R(c_A)}{p-2}.
\]

If `b_{A,p}<1`, condition on avoiding these remaining classes. The result is
uniform on the complete survivor set for `S`, and has the valid profile

\[
 c^{(p)}_S(T)=\frac{c_A(T\setminus\{p\})}{1-b_{A,p}}
       \begin{cases}C_p,&p\in T,\\1,&p\notin T,\end{cases}
 \qquad T\ne\varnothing.
 \tag{P4}
\]

Every admissible choice of last prime produces **the same** uniform probability
on complete survivors. Thus take `c_S(T)=min_p c^{(p)}_S(T)` separately for
each support, over last primes with `b_{A,p}<1`. This is not a minimum over
different measures. The marginal on `A` is reweighted by its actual conditional
survival fraction; a completely killed fibre receives mass zero. No preservation
of each old fibre is assumed.

Applying (P3)–(P4) to all subsets of `{3,5,7,11}` gives

\[
 R(c_{\{3,5,7,11\}})=\frac{1514}{145},\qquad
 K(c_{\{3,5,7,11\}})=\frac{3885}{29}.
 \tag{P5}
\]

The last-prime deletion bounds for `p=3,5,7,11` are respectively
`34/39`, `215/261`, `137/195`, `77/135`, all strictly below one.
The complete resulting profile is:

| `T` | `c(T)` | `T` | `c(T)` |
|---|---:|---|---:|
| ∅ | 1 | {3,5} | 540/29 |
| {3} | 378/29 | {3,7} | 468/29 |
| {5} | 216/29 | {3,11} | 420/29 |
| {7} | 117/29 | {5,7} | 288/29 |
| {11} | 75/29 | {5,11} | 240/29 |
| {7,11} | 180/29 | {3,5,7} | 648/29 |
| {3,5,11} | 600/29 | {3,7,11} | 540/29 |
| {5,7,11} | 360/29 | {3,5,7,11} | 720/29 |

**Exact evaluation of the infinite sums.** For each prime choose `L_p≥0`
satisfying

\[
 p^{L_p+1}\ge\max_{T\subseteq S\setminus\{p\}}
                         \frac{c(T\cup\{p\})}{c(T)}.
\]

If `e_p>L_p`, including `p` in a candidate support in (P3) cannot increase
its value. Thus a minimizing support can include all such tail coordinates.
Partition each exponent into the individual values `0,…,L_p` and one tail
state `e_p>L_p`. For a cell with tail coordinates `J` and positive bounded
coordinates `I`, its envelope is exactly

\[
 \left(\prod_{p\in J}p^{-e_p}\right)
 \min_{T\subseteq I}\frac{c(J\cup T)}{\prod_{p\in T}p^{e_p}}.
\]

Sum the tail coordinates with the exact identities

\[
 \sum_{e>L}p^{-e}=\frac{1}{p^L(p-1)},\qquad
 \sum_{e>L}(2e+1)p^{-e}
   =\frac{(2L+3)(p-1)+2}{p^L(p-1)^2}.
\]

For the displayed four-prime profile the cutoffs are `(2,1,0,0)`, so only
48 cells are needed. The same construction evaluates each predecessor profile
exactly. The [profile verifier](../docs/reports/erdos7-odd-covering/verify_uniform_head_profile.py)
checks the rational recurrence, existence of an admissible normalization at
every nonempty subset, (P5), and its strict comparison to the tail seed.
It uses Python 3.9+ standard-library arithmetic and no residue enumeration:

```sh
python3 docs/reports/erdos7-odd-covering/verify_uniform_head_profile.py
```

For an independent arithmetic bound, summing (P3) on the box `0≤e_p≤6`
and bounding the complement by the raw support coefficients and exact geometric
tails gives `K<134`, consistent with (P5). The cutoff-cell calculation retains
the sharper exact value. These finite calculations certify the numerical
parameters; the profile induction proves their validity for every residue
assignment and every finite height.

**Refinement using a surviving ternary fibre.** For a two-prime family on
`3^H q^J`, with prime `q≥5`, the same uniform complete-survivor law satisfies

\[
 \mu(x\equiv a\pmod3)\le\frac{2(q-2)}{3q-8}.
 \tag{P6}
\]

To prove this, let `Y` avoid the pure `q`-power classes and write
`z=|Y|/q^J≥1−y`, where `y=1/(q−1)≤1/4`. If the target ternary root
is excluded by the modulus-3 class its mass is zero. Otherwise another root
`r mod 3` is also not excluded by that class. Inside `r`, pure powers
`3^h`, `h≥2`, remove a fraction at most `1/2` of the ternary coordinate.
Classes of modulus `3q^j` remove at most `y` of the `q` coordinate.
These conditions concern separate coordinates, leaving relative density
at least `(z−y)/2`. The remaining mixed classes, of modulus `3^h q^j`
with `h≥2`, have total relative density at most `y/2`. Thus complete
survivors in `r` have relative density at least `z/2−y>0`.

The target root has relative survivor density at most `z`, so its normalized
mass is at most `z/(3z/2−y)`. This expression decreases with `z`, and
substituting `z≥1−y` proves (P6). Missing moduli only improve the estimates.
In particular the `{3,5}` bound is `6/7`; it uses actual survival in another
root, with no assumption that every fibre survives.

For each support `T` containing 3, augment `c(T)` with a coefficient `b(T)`
meaning

\[
 \mu\left(x\equiv a\pmod{3^{e_3}\prod_{q\in T\setminus\{3\}}q^{e_q}}\right)
 \le\frac{b(T)}{3\prod_{q\in T\setminus\{3\}}q^{e_q}}
 \qquad(e_3\ge1).
 \tag{P7}
\]

This follows by projection to exponent one of the ternary coordinate.
The envelope is now the minimum of all projected `c` and `b` bounds.
When adjoining a prime other than 3, propagate both coefficients by (P4),
using the refined predecessor `R`; when adjoining 3, the new `b` candidate
equals the new `c` candidate. Take minima across admissible orders for both
families. At each two-prime subset `{3,q}`, additionally replace `b({3})`
by its minimum with `6(q−2)/(3q−8)`, as justified by (P6).
Every bound concerns the same uniform complete-survivor law.

The finite-cell evaluation above still applies. For a nonternary coordinate
also require `p^{L_p+1}≥b(T∪{p})/b(T)` for supports containing 3 and
omitting `p`. Require `L_3≥1` and
`3^{L_3+1}≥3c(T)/b(T)` for every support containing 3. Above that
ternary cutoff, the full-exponent `c` term dominates its `b` counterpart;
the remaining tails factor geometrically as before. The resulting exact
envelope sums are

| Prime support | `R` | `K`, an upper bound on `Γ` |
|---|---:|---:|
| {3,5} | 33/14 | 429/28 |
| {3,5,7} | 36903/7585 | 336438/7585 |
| {3,5,7,11} | 7621078040639947/773234757691590 | 47039764798810808/386617378845795 |

The last row gives a uniform head bound; the joint budget below strengthens
it first to (B6), then the shared-density argument to (P2).
Its cutoffs remain `(2,1,0,0)`.
The [refined profile verifier](../docs/reports/erdos7-odd-covering/verify_refined_head_profile.py)
checks this recurrence with exact rational arithmetic and an independent
finite-box sum with a geometric bound on the complement. The simpler
support-only estimate (P5) remains valid. Neither calculation enumerates
residue assignments; universality follows from the two profile inductions
and the root-fibre argument.

**Joint deletion budget for the two ternary roots.** Individual cylinder
bounds can be strengthened by bounding their entire weighted sum with the
same family's deletion budget. For a `{3,q}` family let `X,Y` avoid the
pure powers and put

\[
 x=|X|/3^H\ge\tfrac12,\quad z=|Y|/q^J\ge1-y,\quad
 y=\frac1{q-1},\quad a_q=\frac{3q-1}{(q-1)^2},\quad
 s=|S|/(3^Hq^J)\ge xz-y/2>0.
\]

Write `M(a,b)` for the maximum mass of a cylinder modulo `3^a q^b`.
Counting its intersection with `X×Y` gives
`M(a,0)≤z/(3^a s)`, `M(0,b)≤x/(q^b s)` and
`M(a,b)≤1/(3^a q^b s)` for positive exponents. Retain the actual root
maximum `ρ=M(1,0)` separately. Summing all other exponents geometrically
bounds the finite nonunit cylinder sum `R_μ` and the finite weighted
cylinder sum `K_μ` by

\[
 R_\mu\le\rho+\frac{z/6+xy+y/2}{s},\qquad
 K_\mu\le1+3\rho+\frac{z+a_qx+2a_q}{s}.
 \tag{P9}
\]

As before `Γ(μ)≤K_μ`. These sums are over the actual finite divisors;
infinite geometric sums only supply upper bounds.

Suppose first that the pure modulus-3 class is present. Of the other two
roots designate one attaining `ρ` as the target. Let `w,v` be their
relative pure-ternary survivor densities. Since the higher pure powers
have total density at most `1/6` in the full ternary period,

\[
 \tfrac12\le w,v\le1,\quad w+v\ge\tfrac32,\quad x=(w+v)/3.
\]

Let `α,β` be the densities **inside `Y`**, measured against the full
`q` period, of the unions forbidden by first-level mixed moduli `3q^b`
in the two roots. Distinct moduli imply `α,β≥0` and `α+β≤y`.
Let `t_1,t_2` be the actual additional full-period densities removed from
the remaining sets by mixed moduli with ternary exponent at least two.
Then `t_1,t_2≥0` and `t_1+t_2≤y/6`. The actual complete root densities are
exactly

\[
 n=w(z-\alpha)/3-t_1,\quad m=v(z-\beta)/3-t_2,
 \qquad s=n+m,\quad\rho=n/(n+m).
\]

Thus (P9) has numerators `n+C_R` and `3n+C_K`, where
`C_R=z/6+xy+y/2>0` and `C_K=z+a_qx+2a_q>0`; the second fraction has
an additional constant one. Move all `t_1` to the other root. This keeps
the denominator fixed and increases `n`. Next increase the other-root
deletion to `y/6`, keeping the numerators fixed and decreasing the
denominator. Both changes increase the bounds. This is a relaxation of
the actual budgets, with no claim that the altered parameters describe
another residue family. All denominators remain positive: throughout the
allowed region the resulting roots satisfy

\[
 n=w(z-\alpha)/3\ge(1-2y)/6>0,\qquad
 m=v(z-\beta)/3-y/6\ge(1-3y)/6>0.
\]

It remains to maximize the two fractions at these relaxed `n,m`.
With the other variables fixed, each is a ratio of affine functions of
`(α,β)`, then of `(w,v)`, then of `z`, with positive denominator.
The maxima therefore occur among the eighteen choices

\[
 (\alpha,\beta)\in\{(0,0),(y,0),(0,y)\},\quad
 (w,v)\in\{(1/2,1),(1,1/2),(1,1)\},\quad z\in\{1-y,1\}.
 \tag{P10}
\]

For completeness, if affine `N,D` have `D>0` and
`u=∑_i θ_i u_i` is a convex combination of vertices, then
`N(u)/D(u)=∑_i[θ_i D(u_i)/D(u)] [N(u_i)/D(u_i)]`.
These are nonnegative weights summing to one, which proves each vertex
reduction. Applying it successively proves (P10) without a numerical
optimization assumption.

If the modulus-3 class is absent, `x≥5/6`. The unsplit estimates instead give

\[
 R_\mu\le\frac{z/2+xy+y/2}{xz-y/2},\qquad
 K_\mu\le1+\frac{2z+a_qx+2a_q}{xz-y/2}.
 \tag{P11}
\]

Both decrease in `x` and `z`, so use `x=5/6,z=1−y`.
For example, the derivative numerators of the first fraction are
`−(y²+z²+zy)/2` and `−y/4−x²y−xy/2`; those of the second are
`−a_qy/2−2z²−2a_qz` and `−y−a_qx²−2a_qx`, all strictly negative.
The resulting bounds are below those of (P10):

| `q` | Uniform `R_μ` bound | Uniform `K_μ` bound | Bounds if modulus 3 is absent |
|---:|---:|---:|---:|
| 5 | 13/6 | 59/4 | 17/12, 215/24 |
| 7 | 21/13 | 29/3 | 23/22, 208/33 |
| 11 | 33/25 | 29/4 | 5/6, 73/15 |

For `q=5`, both maxima in (P10) occur at
`w=1,v=1/2,z=3/4,α=1/4,β=0`, giving `n=1/6,m=1/12`.
The same eighteen exact evaluations give the other rows.

These are bounds for entire sums of the **same** uniform survivor law.
In the profile recurrence use the smaller of its envelope bound and this
joint `R_μ` bound for the next deletion cost `R/(p−2)`. Retain the
individual `c,b` inequalities and similarly take the smaller valid
whole-`K_μ` bound. The new `R` need not equal the sum of the old envelope.
This strengthened induction gives

\[
 R_{\{3,5,7\}}\le\frac{9937}{2142},\quad
 K_{\{3,5,7\}}\le\frac{179315}{4284},\qquad
 R_{\{3,5,7,11\}}\le\frac{1200449891}{129232735},\quad
 K_{\{3,5,7,11\}}\le\frac{28643873521}{258465470}.
\]

This is an intermediate head estimate. The refined profile verifier checks
the eighteen vertices, the absent-modulus branch, this induction and
continuation from this intermediate seed. Its independent finite-box
calculation brackets that profile envelope. The stronger bounds (B6) and (P2) use
the nine-cell and coupled-density arguments below and their separate verifier.

**Joint budgets for the five surviving modulo-9 cells.** Retain the notation
\(x,z,y,a_q,s,M\) of (P9). Suppose first that the family has a pure
modulus-3 class and a pure modulus-9 class outside that forbidden root.
Exactly five modulo-9 cells remain. Label their roots
\(r(j)=(0,0,1,1,1)\), for \(j=1,\ldots,5\). Let \(w_j\) be the relative
density in cell \(j\) remaining after all pure ternary exclusions. Since
the pure powers \(3^a\), \(a\ge3\), have total ambient density at most
\(1/18\),

\[
 \tfrac12\le w_j\le1,\qquad
 \sum_j(1-w_j)\le\tfrac12,\qquad x=\tfrac19\sum_jw_j\ge\tfrac12.
\]

Let \(Y\) be the pure \(q\)-power survivor set, of density \(z\).
For each good root \(r\), let \(A_r\) be the union of its \(q\)-coordinate
exclusions from moduli \(3q^b\), and let
\(\alpha_r=|A_r\cap Y|/q^J\). For each good modulo-9 cell \(j\), let
\(B_j\) be the union from moduli \(9q^b\), and define the **additional**
removed density
\(\beta_j=|B_j\cap(Y\setminus A_{r(j)})|/q^J\).
Thus the remaining \(q\)-coordinate density in cell \(j\) is exactly
\(z-\alpha_{r(j)}-\beta_j\), and distinct moduli give the shared budgets

\[
 \alpha_r,\beta_j\ge0,\qquad \alpha_0+\alpha_1\le y,\qquad
 \sum_j\beta_j\le y.
\]

Let \(t_j\) be the actual additional ambient density deleted in cell \(j\)
by mixed classes with ternary exponent at least three. Then
\(t_j\ge0\) and \(\sum_jt_j\le y/18\). The complete cell densities are
therefore exactly

\[
 n_j=\frac{w_j(z-\alpha_{r(j)}-\beta_j)}9-t_j,\qquad
 s=\sum_jn_j.
\]

All variables describe the same residue family. In particular the budgets
are shared among cells. Put
\(N_1=\max_r\sum_{j:r(j)=r}n_j\) and \(N_2=\max_jn_j\).
These maxima may occur in different roots. Keeping both actual maxima
and using the ordinary caps only at higher ternary exponents gives

\[
 R_\mu\le\frac{N_1+N_2+z/18+xy+y/2}{s},\qquad
 K_\mu\le1+\frac{3N_1+5N_2+4z/9+a_qx+2a_q}{s}.
 \tag{P12}
\]

Here \(\sum_{a\ge3}3^{-a}=1/18\) and
\(\sum_{a\ge3}(2a+1)3^{-a}=4/9\); the pure-\(q\) and mixed terms are
the same geometric sums as in (P9). This bounds the entire cylinder sums
and hence also \(\Gamma\le K_\mu\).

The relaxed parameter region given by these budgets contains every actual
family. It has nonnegative cells and a uniformly positive denominator:

\[
 n_j\ge\frac{z-3y}{18}\ge\frac{1-4y}{18}\ge0,\qquad
 s\ge xz-\frac y2\ge\frac12-y\ge\frac14.
\]

For the second inequality, first-level mixed deletion is at most \(y/3\),
second-level deletion at most \(y/9\), and the remaining deletion at most
\(y/18\). Their sum is \(y/2\). A cell can be empty when \(q=5\); the
proof never conditions on that cell.

For a fixed target root and target modulo-9 cell, the expressions in (P12)
are linear-fractional separately in the five parameter groups
\((1-w_j)_j\), \(\alpha\), \(\beta\), \(t\), and \(z\), with positive
denominator throughout. The vertex identity used for (P10) therefore
applies successively to each group. Taking maxima over target roots and
cells commutes with taking parameter maxima. The budget simplexes have
respectively \(6,3,6,6\) vertices, and \(z\in[1-y,1]\) has two endpoints,
giving exactly \(6\cdot3\cdot6\cdot6\cdot2=1296\) rational evaluations.

The missing-class cases require a separate bound. If modulus 3 is absent,
\(x\ge5/6\). If it is present but modulus 9 is absent or its class is
contained in the forbidden root, only powers with exponent at least three
can remove more pure ternary mass, so \(x\ge2/3-1/18=11/18\).
Both cases are covered by (P11) with \(x=11/18,z=1-y\), since those
fractions decrease in \(x,z\). The exact bounds are:

| \(q\) | \(R_\mu\) from (P12) | \(K_\mu\) from (P12) | Missing or ineffective pure classes: \(R_\mu,K_\mu\) |
|---:|---:|---:|---:|
| 5 | 15/7 | 173/12 | 47/24, 593/48 |
| 7 | 21/13 | 19/2 | 65/46, 574/69 |
| 11 | 33/25 | 181/25 | 101/90, 1411/225 |

The missing-class bounds are smaller in every row. This also handles
finite heights below two. In the recurrence, retain every individual
\(c,b\) bound and use the smaller of the profile sum and the appropriate
whole-sum bound for the next deletion cost. No identity between the new
\(R_\mu\) bound and the old envelope sum is asserted.

**A sharper mixed-head mass under the pure-survivor product.** For every
finite original family on arbitrary powers of 3, 5 and 7, let \(P_0\)
be the product of uniform laws on its actual pure-prime-power survivors.
The union of its mixed-head classes satisfies
\[
 P_0(B_{\mathrm{mixed},357})\le\frac{82}{135}<\frac23.
 \tag{CM1}
\]
This is the same unconditioned head law as in (PH1)--(PH4). Its tail
conditional cylinder caps and complete-layout second-moment majorant
therefore remain valid. The displayed PH numerical certificates retain
their already sufficient input \(2/3\).

To prove (CM1), let \(x,z\) be the ambient pure survivor densities for
3 and 5, and let \(s,R_{35}\) be the density and uniform nonunit cylinder
sum of the complete actual \(\{3,5\}\)-survivors. The pure-7 cylinder sum
is at most \(1/5\). The probability \(\lambda\) under \(P_0\) of avoiding
all mixed-head classes consequently obeys
\[
 \lambda\ge\frac{s}{xz}\left(1-\frac{R_{35}}5\right).
\]
When both low pure ternary exclusions are effective, use the five cells
of (P12), with root labels \((0,0,1,1,1)\). Their shared budgets specialize to
\[
 \sum_j(1-w_j)\le\tfrac12,\quad
 \sum_r\alpha_r\le\tfrac14,\quad\sum_j\beta_j\le\tfrac14,\quad
 \sum_jt_j\le\tfrac1{72},\qquad \tfrac34\le z\le1,
\]
where all deficits and deletions are nonnegative. Retain the actual
quantities \(x=\sum_jw_j/9\),
\(n_j=w_j(z-\alpha_{r(j)}-\beta_j)/9-t_j\), and \(s=\sum_jn_j\).
The positivity bounds for (P12) give \(n_j\ge0\) and \(s\ge1/4\).
Writing \(N_1=\max_r\sum_{r(j)=r}n_j\), \(N_2=\max_jn_j\), (P12) gives
\[
 sR_{35}\le T:=N_1+N_2+z/18+x/4+1/8,\qquad
 \lambda\ge\frac{s-T/5}{xz}\ge\frac{53}{135}.           \tag{CM2}
\]
For fixed target root and cell, the last quotient has separately affine
numerator and positive denominator in the five groups
\(1-w,\alpha,\beta,t,z\). The denominator-weighted vertex identity used
for (P10) applies successively. Minimizing over target root and cell
produces the two maxima in \(T\); the parameter region therefore reduces
to \(6\cdot3\cdot6\cdot6\cdot2=1296\) rational vertices.
Their exact minimum is \(53/135\), attained in this relaxation at
\[
 1-w=(1/2,0,0,0,0),\quad \alpha=(0,1/4),\quad
 \beta=(0,1/4,0,0,0),\quad t=(1/72,0,0,0,0),\quad z=3/4.
\]
Here \(x=1/2\), \(n=(1/36,1/18,1/18,1/18,1/18)\),
\(s=1/4\), and \(T=37/72\). Attainment by an actual residue family is
not asserted.

If modulus 3 is absent, \(x\ge5/6\); if its class is present but the
pure modulus-9 class is absent or contained in the forbidden root,
\(x\ge11/18\). These cases include physical heights below two.
The unsplit bounds \(s\ge xz-1/8\) and
\(sR_{35}\le z/2+x/4+1/8\) give
\[
 \lambda\ge\frac{xz-1/8-(z/2+x/4+1/8)/5}{xz}.
\]
This expression increases in \(x,z\). At \(z=3/4\), the two lower
values of \(x\) give \(43/75\) and \(73/165\), both above \(53/135\).
This proves (CM2) in every case, and hence (CM1). The existing
[verifier](../docs/reports/erdos7-odd-covering/verify_star_block_obstruction.py)
records the exact vertex minimum and both missing-class branches under
**head_mixed_mass_improvement** in its
[certificate](../docs/reports/erdos7-odd-covering/star_block_obstruction_certificate.json).

**Sharpness of (CM1) for actual pure-survivor product laws.** The constant
\(82/135\) is the supremum over actual finite \(\{3,5,7\}\)-families under
the prescribed law \(P_0\). The following construction realizes every
prime-7 union bound as an equality and approaches that supremum. This is
an ordinary mathematical result; the finite residue checks below are not
an end-to-end Lean proof.

Fix \(H\ge3\) and \(K,L\ge1\). First assign one class to every nonunit
divisor of \(3^H5^K\). The pure ternary classes are
\[
 0\pmod3,\qquad4\pmod9,\qquad
 3^{a-1}-8\pmod{3^a}\quad(3\le a\le H),
\]
and the pure quinary class at depth \(b\) is
\(5^{b-1}-1\pmod{5^b}\). For each \(1\le b\le K\), choose the mixed
classes by these CRT coordinates:

| Modulus | Ternary residue | Quinary residue |
|---|---:|---:|
| \(3\cdot5^b\) | \(2\pmod3\) | \(2\cdot5^{b-1}-1\pmod{5^b}\) |
| \(9\cdot5^b\) | \(2\pmod9\) | \(3\cdot5^{b-1}-1\pmod{5^b}\) |
| \(3^a5^b,\ 3\le a\le H\) | \(2\cdot3^{a-1}-8\pmod{3^a}\) | \(2\cdot5^{b-1}-1\pmod{5^b}\) |

Put
\[
 A=\sum_{a=3}^H3^{-a}=\frac{1-3^{-(H-2)}}{18},\qquad
 r=\sum_{b=1}^K5^{-b}=\frac{1-5^{-K}}4,\qquad
 x=\frac59-A,\quad z=1-r.
\]
Inside the cell \(1\pmod9\), the higher pure ternary classes and the
higher mixed ternary coordinates are the disjoint suffix exits
\(2^k0\) and \(2^k1\), respectively, in least-significant-digit order.
The pure, first mixed, and second mixed quinary coordinates are likewise
the mutually disjoint exits \(4^k0,4^k1,4^k2\). Thus \(x,z\) are exactly
the pure survivor densities. The complete pair-survivor set \(S\) has
the following ambient masses in cells \((1,7,2,5,8)\pmod9\):
\[
 \left(\frac z9-A,\ \frac z9,\ \frac{1-3r}9,
             \frac{1-2r}9,\ \frac{1-2r}9\right),\qquad
 s=\frac{|S|}{3^H5^K}=x-r.                            \tag{CM3}
\]
The largest root and cell masses are
\(N_1=(3-7r)/9\) and \(N_2=z/9\). Indeed, the long root exceeds the
short root by \((1-5r)/9+A\ge1/108\); the clean cell \(7\pmod9\)
is the largest cell.

Write \(C_{a,b}\) for the largest ambient mass of \(S\) in a cylinder
modulo \(3^a5^b\). Every maximum is exactly
\[
 \begin{aligned}
 C_{1,0}&=N_1,& C_{2,0}&=N_2,&
 C_{a,0}&=z3^{-a}&& (a\ge3),\\
 C_{0,b}&=x5^{-b}&& (b\ge1),&
 C_{a,b}&=3^{-a}5^{-b}&& (a,b\ge1).
 \end{aligned}                                      \tag{CM4}
\]
For pure ternary depths at least two, use cylinders in the clean cell
\(7\pmod9\). For pure quinary depths use the clean exits \(4^k3\),
which avoid all three earlier quinary exit families. Their product with
the long ternary root, or with the clean short cell, supplies full mixed
cylinders. These choices may differ between divisors, as the definition
of \(R_{35}\) permits; no common cylinder centre is asserted. Since
\(\sum_{a=1}^H3^{-a}=4/9+A=1-x\), (CM4) gives
\[
 T_{H,K}:=sR_{35}
   =N_1+N_2+zA+xr+(1-x)r
   =\frac{4+r}{9}+(1-r)A.                           \tag{CM5}
\]
In particular, \(s\to1/4\) and \(T_{H,K}\to37/72\).

To attain the subsequent prime-7 deletion bound, choose a maximizing
old cylinder for every \(d=3^a5^b>1\). Its ternary coordinate, when
present, is
\[
 g_1=2\pmod3,\qquad g_2=7\pmod9,\qquad
 g_a=3^{a-1}-2\pmod{3^a}\quad(a\ge3),
\]
and its quinary coordinate is \(f_b=4\cdot5^{b-1}-1\pmod{5^b}\).
The higher \(g_a\) are pairwise disjoint exits inside \(7\pmod9\);
the \(f_b\) are pairwise disjoint clean quinary exits. Partition these
old cylinders into five colours:

| Exponents of \(d\) | Colour |
|---|---:|
| \(b=0,\ a=1,2\) | 1 |
| \(b=0,\ a\ge3\) | 2 |
| \(a=0,\ b\ge1\) | 3 |
| \(a=1,2,\ b\ge1\) | 4 |
| \(a\ge3,\ b\ge1\) | 5 |

Within each colour the old cylinders are pairwise disjoint. Assign
the pure class \(7^{e-1}-1\pmod{7^e}\) for \(1\le e\le L\).
For each old divisor \(d>1\) of colour \(j\), assign to \(d7^e\)
the chosen old cylinder and the septenary coordinate
\[
 (j+1)7^{e-1}-1\pmod{7^e}.                           \tag{CM6}
\]
These are the suffix exits \(6^k j\), while the pure exclusions are
\(6^k0\). Distinct pairs \((j,e)\) have disjoint septenary cylinders;
for equal \((j,e)\), the old cylinders are disjoint. Consequently all
mixed classes ending at 7 are pairwise disjoint and avoid the pure
septenary exclusions. Each \(d7^e\) is a new original modulus, so its
old residue is allowed to differ from the residue assigned to \(d\).
The resulting family contains exactly one class for every nonunit
divisor of \(3^H5^K7^L\).

Let \(r_7=\sum_{e=1}^L7^{-e}=(1-7^{-L})/6\) and \(z_7=1-r_7\).
By disjointness, the mixed prime-7 classes remove exactly ambient mass
\(r_7T_{H,K}\) from \(S\) times the pure-7 survivors. Therefore the
complete actual survivor probability under \(P_0\) is exactly
\[
 \lambda_{H,K,L}
 =\frac{s z_7-r_7T_{H,K}}{xz z_7}
 =\frac{s-T_{H,K}r_7/z_7}{xz}
 \longrightarrow\frac{53}{135}.                    \tag{CM7}
\]
Together with (CM1), this proves that the actual mixed-head mass has
supremum \(82/135\). Thus imposing actual residue compatibility on
(CM2), or requiring overlap among the final prime-7 classes, cannot
uniformly reduce this constant for the prescribed pure-survivor product
law. Other choices of the head law are outside this sharpness statement.

**Exact ambient uncovered-density infimum.** Every finite distinct family
supported on \(\{3,5,7\}\) leaves ordinary uniform density strictly
greater than \(53/432\). Indeed, the product of its three actual pure
survivor densities is strictly greater than
\((1/2)(3/4)(5/6)=5/16\), because each finite geometric exclusion sum is
strictly below its infinite sum. Multiplying by (CM1)'s conditional
survivor bound \(53/135\) proves the claim. For the constructed families,
the exact ambient survivor density is
\[
 s z_7-r_7T_{H,K}
 \longrightarrow\frac14\frac56-\frac16\frac{37}{72}
 =\frac{53}{432}.                                   \tag{CM8}
\]
Thus \(53/432\) is the exact infimum over all such finite families.
The earlier pair recurrence \(\lambda\ge(4/7)\theta_{35}\ge8/21\)
implies only the smaller ambient bound \(5/42\).

The existing verifier records **cm1_actual_head_sharpness** through its
canonical certificate writer. It enumerates nine pair-head families,
checks all 126 divisor-cylinder maxima and the disjoint colour classes,
then enumerates eight complete three-prime families with
\(H=3,4\), \(K,L=1,2\). Direct CRT residue checks confirm the exact
prime-7 deletion and (CM7). The all-height construction and its limiting
sharpness are proved above.

**Exact finite densities for the two 5040 odd heads and all ternary heights.**
Among distinct nonunit divisors of \(315\), the minimum number of uncovered
residues in one period is **74**. Among distinct nonunit divisors of
\(3^H\cdot35\), for every \(H\ge3\), that minimum is
\[
 58\cdot3^{H-2}+17.                                  \tag{CM9}
\]
In particular, the minimum at \(945\) is **191**. These are minima over
all residue assignments and all subsets of the indicated divisor sets;
the constructions attaining them use every nonunit divisor once.
The corresponding sharp mixed-head probabilities under the actual
pure-survivor product are \(23/60\) at 315 and \(145/336\) at 945.
These improve the earlier (FC1)--(FC2) bounds without changing the
already valid tail certificates.

For the lower bounds, retain the actual five-cell parameters from (CM2),
but put
\[
 A=\sum_{a=3}^H3^{-a},\quad u=4/9+A,\qquad
 \sum_j(1-w_j)\le9A,\quad \sum_r\alpha_r\le1/5,\quad
 \sum_j\beta_j\le1/5,\quad\sum_jt_j\le A/5,
 \quad4/5\le z\le1.
\]
The same actual identities give \(x=\sum_jw_j/9\),
\(n_j=w_j(z-\alpha_{r(j)}-\beta_j)/9-t_j\) and
\(s=\sum_jn_j\). Since there is at most one pure septenary class,
its normalized cylinder mass is at most \(1/6\). The complete
\(\{3,5\}\) cylinder sum consequently gives
\[
 T=N_1+N_2+zA+x/5+u/5,\qquad
 \lambda\ge\frac{s-T/6}{xz}.                         \tag{CM10}
\]
Here \(N_1,N_2\) are the actual largest root and cell masses, as before.
The relaxed cells stay positive: \(n_j\ge1/90\), and \(x\ge1/2\),
\(z\ge4/5\). For each fixed \(A\), the denominator-weighted vertex
identity reduces the inequality to the same budget-simplex vertices.
At \(H=2\), the deficit and late-deletion budgets are zero, leaving
36 distinct vertices. Their exact minimum is \(37/60\).

For every \(H\ge3\), one has \(1/27\le A<1/18\), and the uniform
vertex bound is
\[
 \lambda\ge L(A):=\frac{25-102A}{40-72A}.             \tag{CM11}
\]
This is an interval certificate, not sampling of heights. For each of
1296 vertex choices and each of the two target roots and five target
cells, replace \(N_1,N_2\) by those target masses and form
\[
 P(A)=(40-72A)(s-T/6)-(25-102A)xz.
\]
The vertex deficits are either zero or \(9A\) in one coordinate, and
the late deletion is either zero or \(A/5\) in one coordinate. Thus
\(P\) has degree at most two. Write \(a=1/27\), \(b=1/18\) and
\(v=(A-a)/(b-a)\). Its Bernstein representation is
\[
 P(A)=P(a)(1-v)^2+
 2\left(P(a)+\tfrac12(b-a)P'(a)\right)v(1-v)+P(b)v^2.
\]
All three coefficients are nonnegative for every one of the 12960
branches; there are 656 distinct polynomials. Exact rational coefficient
verification therefore proves (CM11) over the whole interval, including
all finite heights. Taking the worst target root and cell recovers both
maxima in (CM10).

If the pure modulus-3 class is absent, use \(x\ge8/9-A\); if the
modulus-9 class is absent or ineffective, use \(x\ge2/3-A\).
The unsplit bound is
\[
 \lambda\ge
 \frac{xz-u/5-(zu+x/5+u/5)/6}{xz}.
\]
It increases with \(x,z\). At their respective lower endpoints,
subtracting \(L(A)\) and multiplying by the positive denominators
gives \(80/27+(148/15)A\) and \(16/27+4A\), respectively.
Both are positive. At \(H=2\), the two unsplit bounds are
\(35/48\) and \(47/72\), both above \(37/60\).
These cases also cover divisor families with smaller physical heights.

Multiplying (CM11) by the pure-density lower bound
\((5/9-A)(4/5)(6/7)\) gives ambient uncovered density at least
\[
 \frac5{21}-\frac{34}{35}A
 =\frac{58+17\cdot3^{-(H-2)}}{315}.
\]
The actual construction (CM3)--(CM7), with \(K=L=1\), attains this
quantity for every \(H\ge3\), proving (CM9). Its densities decrease
to \(58/315\), the exact infimum with arbitrary ternary height and
squarefree 5 and 7.

At 315, the lower pure density is \((5/9)(4/5)(6/7)=8/21\), so
\(\lambda\ge37/60\) leaves at least 74 residues. Equality is attained
by the following explicit \((\text{modulus},\text{residue})\) list:
\[
 (3,0),(9,4),(5,0),(15,11),(45,37),(7,0),
 (21,8),(63,16),(35,3),(105,53),(315,313).
\]
The first five classes leave cell masses \((3,4,3,3,3)/45\) in the
order \((1,7,2,5,8)\pmod9\). Maximizing old cylinders have
\((d,a)=(3,2),(9,7),(5,3),(15,8),(45,43)\); extending them with
distinct septenary residues 1 through 5 makes their deletions disjoint
and avoids the pure septenary class. Their total old cylinder mass is
\(22/45\), so the final survivor count is
\(315[(16/45)(6/7)-(22/45)/7]=74\).

The existing verifier records the vertex and interval certificate and
these attaining constructions under **finite_head_sharp_density**.
This is an ordinary universal proof with an exact polynomial certificate;
the endpoint density statement is not yet an end-to-end Lean theorem.

**Simultaneous sharpness of the mixed mass and the unmarked comparison law.**
The sharp head families also rule out a uniform limiting tradeoff between
mixed-head mass and the unmarked load distribution. In the actual
(CM3)--(CM7) construction, choose the test residue for every divisor by
coherent CRT centres \((5,2,2)\). These test residues are independent of
the forbidden residues assigned to the original moduli. Their three
first-level roots are \((2,2,2)\). All pure ternary forbidden cylinders
lie in roots 0 or 1, all pure quinary cylinders in roots 0 or 4, and all
pure septenary cylinders in roots 0 or 6. Every chosen test cylinder
therefore lies entirely inside its coordinate's pure survivor set.

If \(x_p\) is that pure survivor density and \(N_p\) counts the nested
test cylinders containing the coordinate, then
\[
 P_0(N_p\ge a)=\frac{p^{-a}}{x_p}\quad(1\le a\le h_p),
 \qquad L=\prod_{p=3,5,7}(1+N_p).                    \tag{CM12}
\]
The three counts are independent under the actual law \(P_0\). Thus
this complete test load has exactly the finite canonical auxiliary
product law from (PH2), including the terminal atoms. In particular,
\[
 \mathbb E_{P_0}L=\prod_p x_p^{-1},\qquad
 \mathbb E_{P_0}L^2=\prod_p\left(1+x_p^{-1}
                      \sum_{a=1}^{h_p}(2a+1)p^{-a}\right).
\]
As all three heights increase, these laws increase stochastically to the
infinite comparison law, while the same families satisfy
\[
 P_0(B_{\rm mixed})\longrightarrow82/135,\qquad
 \mathbb E_{P_0}L\longrightarrow16/5,\qquad
 \mathbb E_{P_0}L^2\longrightarrow325/18.
\]
Monotone convergence gives the same simultaneous sharpness for every
nonnegative increasing convex cost with finite comparison expectation,
including every fixed positive-part threshold. Consequently, approaching
the maximal mixed mass does not force a positive uniform deficit in this
unmarked comparison. This statement leaves open estimates involving the
actual mixed-head survivor indicator, such as
\(\mathbb E_{P_0}[\mathbf1_S(L-t)_+]\), and alternative supported laws.
The verifier's **sharp_head_unmarked_comparison** entry checks the exact
coordinate and product laws for the eight existing actual CRT families.

**Finite reduction retaining the survivor geometry.** A candidate bound
for the actual uniform survivor law can be reduced to a finite head
optimization with explicit high-height error. Fix truncation heights
\(h_p\), let \(Q=\prod_{p=3,5,7}p^{h_p}\), and let \(S_h\) be the
residues avoiding all original classes whose moduli divide \(Q\). Set
\[
 R_h=\frac{35}{16}-\prod_p\sum_{a=0}^{h_p}p^{-a},\quad
 K_h=\prod_p\sum_{a=0}^{h_p}(2a+1)p^{-a},\quad
 \Delta_h=\frac{35}{4}-K_h,\qquad
 d_h=\max\left\{\frac{53}{432},\frac{|S_h|}{Q}-R_h\right\}.
\]
For any extension to arbitrary finite heights, its full survivor set
\(S\) has ambient density at least \(d_h>0\): the omitted original
classes have total density at most \(R_h\), and (CM8) gives the other
lower bound. Split a complete test load as \(L=L_h+L_{>h}\), according
to whether its divisor divides \(Q\). Its omitted ambient mean is at
most \(R_h\). Expanding ordered divisor pairs gives
\(\mathbb E(L^2-L_h^2)\le\Delta_h\): a compatible pair has probability
\(1/\operatorname{lcm}(d,e)\), and the number of exponent pairs with
maximum \(a\) is \(2a+1\). Incompatible pairs only lower that sum.
For every real threshold \(t\), it follows that
\[
 \begin{aligned}
 \mathbb E_{\mathrm{Unif}(S)}(L-t)_+
 &\le\frac{\mathbb E_{\mathrm{Unif}(Q)}
                   [\mathbf1_{S_h}(L_h-t)_+]+R_h}{d_h},\\
 \mathbb E_{\mathrm{Unif}(S)}L^2
 &\le\frac{\mathbb E_{\mathrm{Unif}(Q)}
                   [\mathbf1_{S_h}L_h^2]+\Delta_h}{d_h}.
 \end{aligned}                                      \tag{CM13}
\]
Here \(S\subseteq S_h\), and
\((a+b-t)_+\le(a-t)_++b\) for \(b\ge0\). Maximizing the numerators
over the finitely many low-head forbidden assignments and test layouts
therefore gives universal profiles usable in (AP1)--(AP6). This reduction
retains actual shared-cylinder exclusions. It does not assert that the
resulting finite optimization already reaches prime 17 or 11.

**Finite supported laws retaining actual exclusions.** The
[finite head geometry result](../docs/reports/erdos7-odd-covering/finite_head_geometry.md) solves the
complete independent-layout minimax problem for all original families
whose moduli divide 45:
\[
 \sup_F\inf_{\mu\text{ supported on }S_F}
       \max_{(b_d)}\mathbb E_\mu
       \left(\sum_{d\mid45}\mathbf1_{b_d\bmod d}\right)^2
       =\frac{22570}{3361}.                         \tag{CM14}
\]
Completion and symmetry reduce the problem to six actual survivor shapes.
Exact primal and dual probabilities check all 27720 independent test
layouts. Extending the same selected law by a uniform pure-7 coordinate
and conditioning once gives, for every original family with moduli
dividing 315, a supported law with
\(\Gamma\le198583/15619<12.715\). This latter upper bound is not
asserted sharp. For this same chosen law, its full convex profile is
also bounded by the explicit finite comparison law in that note, with
mean at most \(110151471/33504305\). The separate second-moment bound
remains \(198583/15619\); the comparison distribution's larger second
moment need not replace it. The reduction permits shrinking the support because the
conclusion is existence of a law; it does not assert monotonicity of
uniform survivor averages. Both statements are ordinary proofs with exact
certificates, and do not enlarge the prime-13 noncoverage range.

A second [supported-law construction](../docs/reports/erdos7-odd-covering/marked_head_profile.md)
controls the entire convex profile on the 315 head. One common law,
uniform on a possibly smaller actual survivor set, satisfies
\[
 \mathbb E_\mu h(L)\le\mathbb E h(W),\qquad
 \Pr(W=2,3,4,5,6,8,12)
 =\left(\frac37,\frac{15}{77},\frac{18}{77},
          \frac{15}{2849},\frac{79}{814},\frac1{37},\frac1{74}\right)
                                                        \tag{CM15}
\]
for every complete test layout and nonnegative increasing convex cost.
Here \(\mathbb EW=37/11\) and \(\mathbb EW^2=41336/2849\).
Its high-threshold profile is attained by an actual 74-survivor family
for every real threshold at least six. The mean/profile in (CM15) and
the smaller moment in (CM14) belong to different selected laws and may
not be combined as one law. An elementary refinement replaces the nearby
integer atoms by an atom at \(117/22\), preserving the mean and lowering
the comparison second moment to \(909287/62678\). The same note proves,
for every probability law \(\nu\) on the full period,
\[
 \Theta_\nu(t)=(12-t)\|\nu\|_\infty
        \qquad(8\le t\le12).
\]
Thus the exact universal minimax over all supported laws is
\((12-t)/74\) on this interval. The uniform law is the unique minimizer
on each fixed survivor set when \(t<12\); nonuniform laws must improve
other parts of the profile to help. A separate actual 75-survivor family
shows that fixing the old marginal to be uniform can force second moment
\(1427/80\) and upper profile \((12-t)/16\). These statements still do
not close the tail from 11.

Retaining each original mixed-7 deletion in both numerator and denominator
strengthens (CM15) on the **same** uniform pruned-survivor law:
\[
 \Theta_\mu(0),\ldots,\Theta_\mu(5)
 \le\left(\frac{271}{86},\frac{185}{86},\frac{100}{81},
          \frac{61}{81},\frac{16}{39},\frac7{26}\right),
 \qquad \mathbb E_\mu L^2\le\frac{1131}{86}.             \tag{CM16}
\]
The established high-profile values at thresholds 6, 8 and 12 complete
one convex comparator with atoms
\[
\begin{array}{c|rrrrrrrr}
x&1&2&3&4&5&6&8&12\\\hline
\Pr(X=x)&581/6966&3031/6966&146/1053&425/2106&10/1443&45/481&1/37&1/74.
\end{array}
\]
Its mean is \(271/86\) and its second moment is
\(45292361/3350646\); the smaller actual second-moment bound
\(1131/86\) is independently valid under the same law.
The numerator bound keeps the deletion multiplicity of each old cylinder,
rather than replacing the actual survivor count by its minimum alone.
The note proves the universal reduction. The standard-library verifier
checks 194040 exact cap inequalities over all 27720 old layouts, with
no layout-pair optimization needed for this refinement. Retaining signed deletion unions gives the sharper square bound above:
4754 first-shape layouts pass a positive-cap screen and six require an
exact five-label partition calculation; the other shapes have smaller bounds.
An explicit 86-survivor family simultaneously attains mean 271/86 and
second moment 1131/86. Thus both are sharp for this prescribed uniform
law, without a minimax claim over all supported laws. Conditioning globally
after one 11-height also gives a supported 3465 law with mean at most
4816/1215, actual second moment at most 14518/675 and the full comparator
in the note.
This improves supported-head control but does not extend the established
prime-13 noncoverage range.

The same [supported-law note](../docs/reports/erdos7-odd-covering/marked_head_profile.md)
also gives a general two-prime construction for an `m` by `n` survivor
grid with matching holes, where `m,n>=3` and the hole count is below
`min(m,n)`. Its explicit common quadratic coefficients work even when
the row sets, column sets and hole locations vary with the old residue;
the constructed law preserves the old marginal. A variable hole count
gives an additional mean-count subtraction, bounded using the original
cross-modulus cofactor labels. Fixed row, column and point-deletion
budgets also reduce arbitrary hole patterns to the one-hole case by
discarding a controlled number of rows and columns. These are ordinary
symbolic proofs for two new prime coordinates of height one and arbitrary
old heights. They do not provide the missing universal weighted estimate
for arbitrary new-prime heights or a new tail cutoff.

**Coupled densities of the three prime-pair subsystems.** Let \(\sigma_A\)
be the ambient density avoiding the original classes supported on \(A\),
and put \(z_p=\sigma_{\{p\}}\). These are subsets of the same fixed family.
Define

\[
 \theta_{ij}=\frac{\sigma_{\{i,j\}}}{z_i z_j},\qquad
 \lambda=\frac{\sigma_{\{3,5,7\}}}{z_3z_5z_7},\qquad
 r_p=\frac1{(p-1)z_p}\le\frac1{p-2},\qquad
 t=\lambda^{-1},\quad v_{ij}=\theta_{ij}/\lambda.
\]

The preceding recurrence proves positivity. The pair mixed-class union
bound gives \(\theta_{35}\ge1-r_3r_5\ge2/3\).
Adding prime 7 to the same uniform pair-survivor law, using
\(R_{35}\le15/7\), gives
\(\lambda\ge\theta_{35}(1-R_{35}r_7)\ge(4/7)\theta_{35}\).
Consequently

\[
 \tfrac23t-v_{35}\le0,\qquad \tfrac47v_{35}\le1.
\]

Inside the product of pure survivors, the forbidden pair-support union
has density at most
\(\sum_{\{i,j,p\}=\{3,5,7\}}(z_i z_j-\sigma_{\{i,j\}})z_p\),
where each unordered pair is counted once. The classes containing all
three primes have total ambient density at most
\(\prod_p1/(p-1)\). Hence

\[
 \lambda\ge\theta_{35}+\theta_{37}+\theta_{57}-2-r_3r_5r_7
 \ge\theta_{35}+\theta_{37}+\theta_{57}-\tfrac{31}{15},
\]
\[
 v_{35}+v_{37}+v_{57}-\tfrac{31}{15}t\le1.
\]

This uses the actual pair densities and a union bound; it does not assert
independence of the three forbidden pair-support unions. Multiply the
three displayed linear inequalities, in their order, by
\(31/30,\ 49/40,\ 1/3\). The \(t\) and \(v_{35}\) coefficients cancel,
and the nonnegative rational combination gives

\[
 \frac{v_{37}+v_{57}}3\le\frac{49}{40}+\frac13=\frac{187}{120}.
 \tag{P13}
\]

For any cylinder supported on \(T\), survival still requires avoidance
of all outside-only classes. Ambient product independence therefore gives

\[
 \mu_S(a\bmod d_T)\le\frac{\sigma_{S\setminus T}}{\sigma_Sd_T}.
\]

Applying this to pure ternary and quinary cylinders, using
\(z_3\ge1/2,z_5\ge3/4\), yields

\[
 \sum_{e\ge2}\max_a\mu_S(a\bmod3^e)\le v_{57}/3,\qquad
 \sum_{e\ge1}\max_a\mu_S(a\bmod5^e)\le v_{37}/3.
\]

These are disjoint groups of exponent vectors for the same law.
The profile obtained from the nine-cell pair bounds has
\(R_{\mathrm{envelope},357}=1663/360\),
\(c(\{3\})=21/4\), and \(c(\{5\})=26/9\).
On the two groups above its ordinary coefficients are below every
projection cap, and its exact contributions are respectively
\((21/4)\sum_{e\ge2}3^{-e}=7/8\) and
\((26/9)\sum_{e\ge1}5^{-e}=13/18\).
Keep the envelope on all other exponent vectors and replace these two
groups by (P13). This proves

\[
 R_{\mu_{\{3,5,7\}}}\le
 \frac{1663}{360}-\frac78-\frac{13}{18}+\frac{187}{120}
 =\frac{1649}{360}.
\]

Using this whole-sum bound in the next deletion step preserves every
individual cylinder inequality. Exact propagation to four primes gives

\[
 R_{\mu_{\{3,5,7,11\}}}\le\frac{5275731}{574351},\qquad
 \Gamma(\mu_{\{3,5,7,11\}})\le
 K_{\mathrm{envelope},35711}
 =\frac{187719326}{1723053}<108.945765.
 \tag{P14}
\]

This is the intermediate profile bound used by the actual-layout block
argument below, which proves (B6), and the shared-density improvement (P2). The
[independent density verifier](../docs/reports/erdos7-odd-covering/verify_joint_density_certificate.py)
and its
[fixed sparse rational certificate](../docs/reports/erdos7-odd-covering/joint_density_certificate.json)
check all 3888 nine-cell parameter vertices, the missing-class branches,
the three-prime profile and exact infinite sums, the three nonnegative
weights and zero residual in (P13), the four-prime recurrence, and a
two-step continuation at 71 and 73 from this intermediate bound. They use Python 3.9+ standard-library
arithmetic with no solver or residue-family enumeration. The mathematical
arguments establish the meaning and universality of the checked
inequalities; these arithmetic checks do not claim Lean certification.

**Conclusion of (P1).** Apply (P2), proved by the shared-cofactor density refinement below, to
all classes involving only `{3,5,7,11}`. For any missing small prime use an
unused coordinate; this adds no forbidden class. Start (T6) with `G=C_4`
and `s=1`. Take the three steps `p=67,71,73`, with respective thresholds
`δ=1/4,53/200,27/100`. Their exact survivor-fraction lower bounds are

\[
 \frac{150994879}{155933910},\qquad
 \frac{55931291964461}{57643654012161},\qquad
 \frac{138545600701541742901}{142871787094690609776},
\]

all strictly positive. The corresponding ratios are

\[
 F_{67}=\frac{17123620477}{150994879},\qquad
 F_{71}=\frac{6921898229038187}{55931291964461},\qquad
 F_{73}=\frac{18699964911029778700842}{138545600701541742901}
 <\frac{138877}{1000}.
 \tag{P8}
\]

Any absent bridge prime may also be an unused coordinate. Continue at
prime 79, with absolute prime index 22, using the checked upper seed
`F_21=138877/1000`. No prime from 13 through 61 needs to be inserted into
the head: the index specifies where the tail starts, while (T1) allows any
coprime head. The exact continuation and BBMST's analytic termination leave
positive mass on complete survivors. CRT and periodicity supply an integer
avoiding every original congruence.

**Literature boundary.** The searched project has the two-prime density
theorem but no joint-load or cylinder-profile head theorem. The searched pinned
Mathlib congruence, probability and combinatorics files provide counting,
finite sums and Cauchy–Schwarz, with no exact profile result identified.
Hough–Nielsen's necessary factor 2 or 3, BBMST's odd-cover restriction involving
9 or both 3 and 5, BBMST's squarefreeness at primes at most 73, and the
density theorem for LCM `2^a3^b5^c` in [arXiv:2605.18644, Theorem 1.9](https://arxiv.org/abs/2605.18644)
do not directly cover (P1). The separately verified three-factors-per-modulus
theorem also has a different hypothesis: (P1) permits moduli divisible by four
or more primes. No dominating theorem was identified in this searched scope;
this is not a claim of literature priority. The theorem and its proof have
not been formalized in Lean.

### An actual-layout improvement from incompatible ternary roots

For any finite `{3,q}` family as above, the uniform complete-survivor law
satisfies the stronger bounds on the **actual joint-layout maximum**

\[
 \Gamma_{35}\le57/4,\qquad \Gamma_{37}\le123/13,\qquad
 \Gamma_{3,11}\le181/25.
 \tag{G1}
\]

In particular `57/4<59/4`. These bounds retain incompatible choices within
one test layout. They do not lower `R` or the sum of separate cylinder maxima
and are not substituted for either quantity in the profile recurrence.

Suppose first that the actual modulus-3 class is present, leaving two
possible survivor roots `A,B`. Use the same actual densities from the
two-root budget: `n=w(z−α)/3−t_1`, `m=v(z−β)/3−t_2`, `s=n+m`, and
`d_A=z−α,d_B=z−β`. Every depth-`k` ternary cylinder within root `A` has
raw complete-survivor density at most `d_A/3^k`, and likewise for `B`.
Thus the first-level mixed exclusions constrain the correct root even
when bounding higher-depth test classes.

Consider the pure ternary part `1,3,…,3^H` of a complete test layout.
If its modulus-3 test class chooses `A`, its diagonal and its two ordered
intersections with the constant class contribute exactly `3n` before
normalization. At a later depth `k≥2`, let `a,b` count earlier positive
test depths assigned to `A,B`. A class in `A` contributes at most
`(3+2a)d_A/3^k`: its pairs with the other root have zero mass, while
each earlier class in the same root contributes at most twice its own
mass. The corresponding bound in `B` is `(3+2b)d_B/3^k`.

The remaining scaled cost of every finite itinerary is bounded by

\[
 V(a,b)=3\max\{d_A(a+2),d_B(b+2)\}.
 \tag{G2}
\]

Induct on the number of remaining choices. A choice of `A` contributes
`(3+2a)d_A+V(a+1,b)/3`. If the latter maximum chooses `A`, this is
exactly `3d_A(a+2)`. Otherwise it is at most
`2d_A(a+2)+d_B(b+2)≤V(a,b)`. The other choice is symmetric, and the
empty tail has cost zero. Selecting the actual forbidden root contributes
zero and discounts the continuation by `1/3`, also preserving the bound.

For two active choices, this finite-itinerary induction is proved in
[TernaryRootLoadTail.root_load_tail_le](../D5/S3/Arith/Congruence/TernaryRootLoadTail.lean).
The theorem allows arbitrary nonnegative real weights, arbitrary natural
initial counts and any finite Boolean list. Its proof uses only the permitted
`propext`, `Classical.choice` and `Quot.sound` axioms. It is a checked Lean
component. The actual event-to-itinerary inequality is additionally proved in
[TwoRootEventMoment.two_root_event_moment_le](../D5/S3/Arith/Congruence/TwoRootEventMoment.lean).
For any finite weighted space split into two roots, initial load bounded by
`1+a` and `1+b`, and event list with successive root caps
`d_A,d_B`, `(d_A/3,d_B/3)`, and so on, it bounds the actual integrated
square increment by `3 max(d_A(a+2),d_B(b+2))`. Repeated list entries
count repeatedly; neither nesting nor probability normalization is assumed.
Empty events account for zero-mass choices. The proof advances the actual
load and root counts together before applying the itinerary theorem; its
axiom closure is also exactly the permitted three axioms. The congruence
cylinder caps, arithmetic embedding, normalization and remaining parts of
(G1) are not thereby formalized.

The root-switching estimate now extends to any root type and any discount
\(0\le r<1\). The Lean theorem
[ArbitraryRootEventMoment.arbitrary_root_event_moment_le](../D5/S3/Arith/Congruence/ArbitraryRootEventMoment.lean)
allows arbitrary nonnegative weights on a finite carrier, an arbitrary root
map, an initial load at most \(1+a_i\) on root \(i\), and actual events
whose root-specific caps are multiplied by \(r\) after every event. Any
nonnegative common budget

\[
 M\ge d_i\left(\frac{2a_i+3}{1-r}+\frac{2r}{(1-r)^2}\right)
 \quad\text{for every root }i                           \tag{AR1}
\]

bounds the integrated square increment of every finite event list. The
proof updates the actual load and root counts directly. An event in root
\(i\) costs at most \(c=(2a_i+3)d_i\); its updated constant-root cost is
its old cost minus \(c\), while all other root costs are at most \(rM\).
The inequality \(c\le(1-r)M\) closes the induction with budget \(M-c\).
No finiteness assumption on the root type, event nesting, or normalization
of the weights is needed. Zero discount and empty lists are included.

For a prime-power coordinate use \(r=1/p\). If the first test cylinder
selects root \(j\), and higher cylinders in root \(i\) have mass at most
\(C_i p^{-e}\), take \(d_i=C_i/p^2\), \(a_j=1\), and all other counts zero.
The remaining square increment is at most

\[
 \frac{\max\{C_j(5p-3),(3p-1)\max_{i\ne j}C_i\}}
      {p(p-1)^2}.                                     \tag{AR2}
\]

For \(p=3\) this recovers the two-root bound below; for \(p=5\) it retains
four possible surviving roots and gives
\(\max\{11C_j/40,7\max_{i\ne j}C_i/40\}\). This arithmetic specialization
is an ordinary application, not another Lean declaration. The checked
component has only the three permitted axioms; its residue-cylinder caps
and the complete covering argument remain separate obligations.

At depth two the initial counts are `(1,0)`, so (G2), multiplied by `1/9`,
bounds the remaining contribution by `max(d_A,2d_B/3)`. The pure ternary
part, excluding the constant diagonal, is therefore at most
`3n+max(d_A,2d_B/3)`. If the modulus-3 test chooses `B`, swap the roles.
If it chooses the forbidden root, its tail is at most
`(2/3)max(d_A,d_B)`, which is no greater than these two-root upper bounds.

Every other ordered pair in the full test-square expansion has positive
`q` exponent in its least common multiple. Pairs with ternary lcm exponent
zero contribute at most `a_q x`; pairs with both exponents positive
contribute at most `2a_q`, using the complete geometric lcm counts.
These include all crosses between pure ternary and positive-`q` test groups.
No old cofactor or exponent group is omitted. Consequently

\[
 \Gamma(\mu)\le1+
 \frac{\max\{3n+d_A,\ 3n+2d_B/3,\ 3m+d_B,\ 3m+2d_A/3\}
       +a_qx+2a_q}{n+m}.
 \tag{G3}
\]

By symmetry it suffices to maximize the first two branches. Move all actual
higher-depth deletion to the unselected root and then enlarge it to `y/6`,
as in the preceding budget argument. This increases each bound and keeps
the denominator positive throughout. Each remaining branch is a ratio of
affine functions in each parameter group of (P10). The same eighteen
vertices, for each of two branches, suffice. Their exact maxima are (G1).
For `q=5` the maximum occurs in the `d_A` branch at
`w=1/2,v=1,α=0,β=1/4,z=3/4`. No actual residue family attaining this
relaxation maximum is asserted.

If the actual modulus-3 class is absent, the earlier unsplit bounds
`215/24,208/33,73/15` for `q=5,7,11` are smaller than (G1).
The [actual-layout verifier](../docs/reports/erdos7-odd-covering/verify_two_root_gamma.py)
checks all 108 rational vertex values and the three absent-modulus branches,
with explicit checks that remain active under optimized Python. The full
two-prime congruence theorem (G1) is an ordinary mathematical proof with
exact arithmetic verification; only the stated finite-itinerary component
has been checked in Lean.

### Coupling the shared zero-exponent layout

For every finite distinct-modulus family supported on `{3,5}`, its uniform
complete-survivor law satisfies

\[
 \boxed{\Gamma_{35}\le55/4.} \tag{ZG1}
\]

Together with the established bound on the same uniform law, this gives
`(Γ35,R35)≤(55/4,15/7)`. The improvement comes from preserving the identity
of the zero-five-exponent test layout in all its cross terms.

Suppose first that an actual modulus-3 class is present. Use the actual
two-root parameters from the earlier budget argument:

\[
 y=1/4,\quad a=7/8,\quad x=(w+v)/3,\quad
 d=z-\alpha,\quad e=z-\beta,
\]
\[
 n=wd/3-t_A,\qquad m=ve/3-t_B,\qquad s=n+m.
\]

Here `1/2≤w,v≤1`, `w+v≥3/2`, `3/4≤z≤1`, `α,β≥0`, `α+β≤y`, and
`t_A,t_B≥0`, `t_A+t_B≤y/6`. Let `η` be the unnormalized uniform measure
on the pure-ternary survivor set. Its total mass is `x`, its two root masses
are `w/3,v/3`, and its depth-`j` cylinder caps are `3^{-j}` in either
surviving root. Write `μ` for the uniform complete `{3,5}` survivor law.
As positive measures on the full product period,

\[
 \mu\le s^{-1}(\eta\times U_5),
\]

where `U_5` is uniform on the whole finite 5-power coordinate. This
inequality drops the pure-5 and mixed exclusions, and applies whether or
not individual old fibres survive.

Fix one complete test layout. For each 5-exponent `b≥0`, stripping the
5-part of its divisors gives a complete pure-ternary layout with load
`L_b`. These loads include divisor one and every old cofactor. The selected
5-adic residue may depend on the old divisor. Put

\[
 A_0=\int L_0^2\,d\eta,\qquad B=\Gamma(\eta).
\]

The block with both 5-exponents zero contributes exactly
`E_μ L_0²`, since `L_0` depends only on the ternary coordinate. For the
two ordered blocks `(0,b),(b,0)` with `b>0`, each pair of outside cylinders
has uniform intersection mass at most `5^{-b}`. Bound this separately for
every old divisor pair, then sum and integrate the old indicators. The two
blocks together contribute at most

\[
 \frac{2\cdot5^{-b}}s\int L_0L_b\,d\eta
 \le\frac{5^{-b}}s(A_0+B),
\]

by the pointwise square inequality and `∫L_b²dη≤B`. Among pairs of
strictly positive 5-exponents with maximum `b`, there are `2b−1` ordered
pairs. Cauchy–Schwarz bounds each complete old cross moment by `B`.
Summing these nonnegative bounds gives

\[
 E_\mu L^2\le E_\mu L_0^2+
       \frac{yA_0+(a-y)B}s. \tag{ZG2}
\]

Indeed `∑_{b≥1}5^{-b}=y` and
`∑_{b≥1}(2b−1)5^{-b}=a−2y=3/8`. Thus the coefficient of `B` is
`y+(a−2y)=a−y=5/8`. At finite heights, only existing blocks are present;
the infinite series provide upper bounds with nonnegative terms. No old
cofactor, cross term or tail is omitted.

The same `L_0` occurs in both terms of (ZG2). If its modulus-3 test
chooses surviving root `A`, the existing root-labelled Bellman estimate gives

\[
 E_\mu L_0^2\le1+\frac{3n+\max(d,2e/3)}s,
 \qquad A_0\le x+w+1.
\]

For any complete old layout, the same estimate under `η` gives
`B≤x+max(w,v)+1`. Hence an `A`-selected layout satisfies

\[
 E_\mu L^2\le1+
 \frac{3n+\max(d,2e/3)+y(x+w+1)
                +(a-y)(x+\max(w,v)+1)}s.
 \tag{ZG3}
\]

The corresponding `B`-selected bound swaps the two roots. These are
consequences of the same finite-itinerary estimate used earlier: when the
initial root is fixed, the later tail under `η` contributes at most one,
while the initial diagonal and two constant crosses contribute `w` or `v`.
The global `B` permits either initial root; `A_0` retains the actual one.

If the modulus-3 test chooses the actual forbidden root, its event has zero
mass under both measures. The remaining-tail bounds are

\[
 E_\mu L_0^2\le1+\frac{2\max(d,e)}{3s},\qquad
 A_0\le x+2/3.
\]

This case is dominated by one of the surviving-root bounds. If `d≥e`,
choose the bound whose initial root is `B`: its numerator includes
`3m+max(e,2d/3)≥2d/3`, and its `η` cap `x+v+1` is at least `x+2/3`.
If `e≥d`, use root `A` symmetrically. Thus no additional optimization
assumption is needed for the forbidden-root test choice.

To maximize (ZG3), move all deep mixed deletion from the selected root to
the other root. This keeps `s` fixed and increases `n`; every other term
is unchanged. Enlarge the other-root deletion to `y/6`. The numerator is
positive and fixed during this enlargement, while the denominator decreases.
It therefore suffices to take

\[
 n=w(z-\alpha)/3,\qquad
 m=v(z-\beta)/3-y/6.
\]

Both roots remain positive: `n≥1/12`, `m≥1/24`. Expand the two maxima
in (ZG3) into their four affine branches. For each branch, numerator and
denominator are affine in each of `(α,β)`, `(w,v)` and `z` separately.
A ratio of affine functions with positive denominator at a convex
combination is the denominator-weighted average of its vertex ratios.
Applying this successively leaves exactly the eighteen parameter vertices

\[
 (w,v)\in\{(1/2,1),(1,1/2),(1,1)\},\qquad
 (\alpha,\beta)\in\{(0,0),(y,0),(0,y)\},\qquad z\in\{1-y,1\}.
\]

The fixed rational certificate checks all `18×4=72` branches. Their exact
maximum is `55/4`, proving (ZG1) for an actual modulus-3 exclusion. Root
exchange covers either surviving-root test choice. If the actual modulus-3
class is absent, the established unsplit uniform bound is `215/24<55/4`;
its normalization denominator is `1/2>0`. Missing higher pure classes,
missing mixed classes and arbitrary finite prime heights are already allowed
by the budgets and the nonnegative geometric-tail bounds above.

The old extremal parameter point illustrates the gain. At
`w=1/2,v=1,α=0,β=1/4,z=3/4,t_A=0,t_B=1/24`, one has `n=m=1/8`.
The old envelope gave `57/4`. Its pure old contribution selects root `A`,
while its independent positive-five bound can select root `B`. Retaining
that first choice in `A_0≤x+w+1=2`, alongside `B≤5/2`, gives `55/4`.

The parameter point itself is a genuine infinite-height limit, so it cannot
be removed by asserting a forced overlap of pure-ternary and deep mixed
exclusions. An explicit finite family with heights `H≥2,K≥1` is:

- forbid `2 mod 3`;
- for `2≤j≤H`, forbid `3^{j−1} mod 3^j` in root `A=0`;
- for `1≤b≤K`, forbid `5^{b−1} mod 5^b`;
- for each `3·5^b`, choose the CRT class `1 mod 3` and
  `2·5^{b−1} mod 5^b`;
- for each `3^j5^b` with `j≥2`, choose the CRT class
  `1+3^{j−1} mod 3^j` and `3·5^{b−1} mod 5^b`.

Every modulus is distinct. For any fixed prime, the displayed strings with
first nonzero digit at different depths are disjoint. The three 5-adic
colours `1,2,3` are also disjoint; pure higher ternary exclusions lie in
root `A`, while the deep mixed ternary factors lie in root `B`. Therefore,
with `r_H=∑_{j=2}^H3^{-j}` and `u_K=∑_{b=1}^K5^{-b}`, the exact parameters
are `w=1−3r_H`, `v=1`, `z=1−u_K`, `α=0`, `β=u_K`, `t_A=0`,
`t_B=r_Hu_K`. Their limits are exactly the old extremal parameters.
This realizes the budget limit, not equality in the old second-moment
bound; (ZG1) shows that the old bound is not tight for actual layouts.

The [standalone verifier](../docs/reports/erdos7-odd-covering/verify_uniform_gamma_cofactor_coupling.py) checks
all rational branches and missing-modulus normalization against
the [fixed certificate](../docs/reports/erdos7-odd-covering/uniform_gamma_cofactor_certificate.json). The layout correspondence and
continuous reduction above are ordinary mathematical arguments; no full
Lean formalization of (ZG1) is claimed.

### The shared zero-exponent envelope for arbitrary outside prime

Let q>=5 be prime and let mu be the uniform complete-survivor law of any
finite distinct-modulus family supported on {3,q}. Set

    y=1/(q-1),     a=(3q-1)/(q-1)^2=3y+2y^2.

The shared-zero-layout argument gives the uniform bound

    Gamma(mu) <= max{ A(y), B(y) },
    A(y)=(30y^2+28y+15)/(3-5y),
    B(y)=5(2y^2+y+1)/(1-2y).

This is the exact maximum of that argument's parameter relaxation, not a
claim that the actual layout supremum always attains it. Its branch change is

    y_*=(sqrt(1281)-31)/20,
    B(y)-A(y)=y(10y^2+31y-8)/((1-2y)(3-5y)).

Consequently the prime cases simplify to

    q=5:  Gamma(mu)<=55/4;
    q>=7: Gamma(mu)<=(15q^2-2q+17)/((q-1)(3q-8)).

In particular q=7 and q=11 give 123/13 and 181/25. These equal the existing
compatible-layout inputs. The formula also supplies the bound for every larger prime, without
a height restriction.

#### Proof of the envelope

When a modulus-3 forbidden class is present, retain the two actual root
widths w,v in [1/2,1], with w+v>=3/2, pure-q density z in [1-y,1],
first-level deletion unions alpha,beta>=0 with alpha+beta<=y, and total
deep deletion at most y/6. Write x=(w+v)/3, d=z-alpha and e=z-beta.

For a fixed layout whose zero-q layer chooses the first surviving ternary
root, the identical shared-layer proof gives

    E_mu L^2 <= 1+
      [3n+max(d,2e/3)+y(x+w+1)+(a-y)(x+max(w,v)+1)]/(n+m).

Here n=wd/3-t_A and m=ve/3-t_B are the actual complete root densities.
The coefficient of the shared zero layer is sum(q^-b)=y; that of the
remaining old-layout supremum is a-y. Every strictly positive-positive
lcm block has coefficient (2b-1)q^-b, whose sum is a-2y=y+2y^2>=0.
The test residues may depend on their old cofactors; cylinder integration
precedes the old-layout sum, as in the q=5 proof. A test in the forbidden
ternary root is dominated by one of the two surviving-root estimates.

Moving all deep deletion to the unselected root and enlarging it to y/6
increases this bound, so use n=wd/3 and m=ve/3-y/6. Uniformly for
0<=y<=1/4, n>=1/12 and m>=1/24. Expanding both maxima gives four affine
branches. Each is separately linear-fractional in the three parameter
groups, so its maximum lies among

    (w,v)=(1/2,1),(1,1/2),(1,1);
    (alpha,beta)=(0,0),(y,0),(0,y);
    z=1-y,1.

Of these 72 symbolic branches, 69 are <=A(y) throughout [0,1/4]. The
remaining three are <=B(y); their formulas are

    (10y^2+9y+4)/(1-2y),
    B(y),
    (30y^2+23y+13)/(3(1-2y)).

The respective gaps below B are (1-4y)/(1-2y), zero, and
2(1-4y)/(3(1-2y)). Both A and B themselves occur among the branches.
The 69 comparisons are exact polynomial certificates: after cross
multiplying positive denominators, each gap P satisfies

    4^n(1+t)^n P(t/(4(1+t))) has nonnegative rational coefficients,
    n=degree(P).

This proves each inequality over the entire parameter interval, with
continuity at y=1/4. The adjacent verifier reconstructs these polynomial
identities from the parameter formula; its fixed JSON supplies every gap
and coefficient. No numerical sampling or solver is used for this step.

If an actual modulus-3 exclusion is absent, the pure-ternary density is at
least 5/6. The monotone unsplit bound is

    M(y)=(34y^2+31y+17)/(5-8y).

The numerator of A-M after cross multiplication is
24+12y-21y^2-70y^3, at least 691/32>0 on [0,1/4]. Thus this branch is
strictly smaller than A; its q=5,7,11 values are 215/24,208/33,73/15.
Arbitrary finite heights and missing higher moduli remain covered by the
same nonnegative infinite-tail bounds.

The [standard-library verifier](../docs/reports/erdos7-odd-covering/verify_uniform_gamma_prime_parameter.py)
and its [fixed certificate](../docs/reports/erdos7-odd-covering/uniform_gamma_prime_parameter_certificate.json) verify all symbolic
identities and interval signs. Normal, -O and -I runs exit 0. The proof is
an ordinary mathematical generalization; no new Lean statement is delivered.

### Transporting actual layouts through outside lcm blocks

The actual two-prime estimate (G1), together with the common-family density
bounds, improves the four-prime profile bound (P14) to (B6). Set
`A={3,5}`, `B={7,11}`, and let `ρ_p` be uniform on the pure-`p` survivors
of the original family. The same-family conditioning steps give

\[
 1-\frac{R_{35}}{7-2}\ge\frac47,\qquad
 1-\frac{R_{357}}{11-2}\ge\frac{1591}{3240}.
\]

Both denominators are positive. The product probability
`ν=μ_A×ρ_7×ρ_11` therefore dominates the final uniform survivor law
pointwise as

\[
 \mu_{35711}\le D\nu,\qquad
 D=\frac74\frac{3240}{1591}=\frac{5670}{1591}.
 \tag{B1}
\]

This permits completely deleted fibres; it asserts no preservation of
the earlier marginals. Each `ρ_p` has cylinder bound
`ρ_p(r mod p^k)≤C_p/p^k`, where `C_p=(p−1)/(p−2)`.

Fix one full test layout. Group its classes by the outside exponent vector
`e=(e_7,e_11)`. Removing the outside factors gives, for every `e`, one
complete old layout `L_e` on `A`, including divisor one. For a pair of
outside exponent vectors `e,f`, put `b=max(e,f)` coordinatewise. Expand
its contribution over old divisors `d,d′` before integrating the outside
coordinates. The outside test residues may depend arbitrarily on both
old divisors. For each pair their intersection has mass at most

\[
 k_p(b_p)=
 \begin{cases}1,&b_p=0,\\ C_p p^{-b_p},&b_p>0.\end{cases}
\]

This cap is independent of `d,d′`. Summing the old indicators afterwards
and using Cauchy–Schwarz under the same `μ_A` gives

\[
 \int_\nu \text{the ordered }(e,f)\text{ contribution}
 \le\prod_{p\in B}k_p(b_p)\int L_eL_f\,d\mu_A
 \le\prod_{p\in B}k_p(b_p)\,\Gamma_A(\mu_A).
 \tag{B2}
\]

Thus test residues need not be independent of the old divisor, or mutually
compatible across divisors. There are `N_B(b)=(2b_7+1)(2b_11+1)` ordered
outside exponent pairs with maximum `b`. With `G=57/4` from (G1), the
entire block under the final law is bounded by

\[
 T_b=DG\,N_B(b)\prod_{p\in B}k_p(b_p).
 \tag{B3}
\]

The existing profile gives another bound on exactly that block:

\[
 P_b=N_B(b)\sum_{a_3,a_5\ge0}
             (2a_3+1)(2a_5+1)u(a_3,a_5,b_7,b_{11}),
 \tag{B4}
\]

where `u` is the full projection envelope from (P14). For this profile,
the largest adjoining-coordinate ratio among both ordinary and
first-ternary coefficients is `1344/361<7` at prime 7 and
`3600/1591<11` at prime 11. Whenever an outside exponent is positive,
including its coordinate in a projection therefore weakly improves that
envelope term. Applying this to both coordinates shows that `P_b` factors
exactly according to its positive support `J={p∈B:b_p>0}`:

\[
 P_b=C_J\prod_{p\in J}\frac{2b_p+1}{p^{b_p}},\qquad
 T_b=T_J\prod_{p\in J}\frac{2b_p+1}{p^{b_p}},\qquad
 T_J=DG\prod_{p\in J}C_p.
 \tag{B5}
\]

The internal coefficient `C_J` is the exact weighted envelope sum on
`{3,5}`, using ordinary coefficients `c(U∪J)` and first-ternary
coefficients `b(U∪J)`. The finite/tail partition with cutoffs no larger than
`a_3=2,a_5=1` evaluates all internal exponents. All four coefficients
and the complete outside-height sums are:

| Outside support `J` | Profile `C_J` | Actual-layout `T_J` | Height sum | Chosen bound |
|---|---:|---:|---:|---|
| empty | 67971/1591 | 161595/3182 | 1 | profile |
| `{7}` | 37315227/574351 | 96957/1591 | 5/9 | actual layout |
| `{11}` | 85450/1591 | 89775/1591 | 8/25 | profile |
| `{7,11}` | 115830/1591 | 107730/1591 | 8/45 | actual layout |

The height sums use `Σ_{k≥1}(2k+1)p^(−k)=(3p−1)/(p−1)²`.
Summing the profile column with these weights recovers exactly
`187719326/1723053`, providing a check that every old block is accounted
for. For each actual layout take the smaller bound on each block, then
sum. Since all terms are nonnegative, extending any finite heights to
the full geometric sums remains valid, even when some blocks are absent.
Consequently

\[
 \begin{aligned}
 \Gamma_{35711}
 &\le\frac{67971}{1591}
      +\frac59\frac{96957}{1591}
      +\frac8{25}\frac{85450}{1591}
      +\frac8{45}\frac{107730}{1591}\\
 &=\boxed{\frac{168332}{1591}<105.802640.}
 \end{aligned}
 \tag{B6}
\]

This proves the intermediate bound (B6), including arbitrary finite exponents. It bounds the
maximum of a joint layout square, and does not assert the same bound for
the sum of separately maximized cylinders. The
[block verifier](../docs/reports/erdos7-odd-covering/verify_lcm_block_transport.py)
and [fixed certificate](../docs/reports/erdos7-odd-covering/lcm_block_certificate.json)
reconstruct the profile, check the adjoining-coordinate ratios, both
complete geometric sums, and three positive-denominator steps from the
(B6) seed. The stronger seed and bridge in (P2) and (P8) are checked by the
shared-cofactor verifier below. The block argument and its four-prime
conclusion are not Lean formalized.

### Intermediate four-prime bound from shared survivor densities

For every finite distinct-modulus forbidden family supported on
S={3,5,7,11}, let mu_S be its complete uniform survivor law. Then

    Gamma(mu_S) <= 5015891/47730 = 105.08885397024932...

Here Gamma is the maximum second moment of one complete residue layout.
The improvement over 168332/1591 is exactly 34069/47730. The proof retains
actual survivor densities in the compatible-layout transfer; no
independence between different subset-survival events is assumed.

#### One common product law

Let rho_p be the uniform law surviving the original pure p-power classes,
and P=product rho_p. The pure survivor density is at least
(p-2)/(p-1), so a p^e cylinder has rho_p-mass at most
(p-1)/((p-2)p^e).

For A subset S, let E_A be survival of all original mixed forbidden classes
whose prime support is contained in A, and let lambda_A=P(E_A). Empty and
singleton A have lambda_A=1. Define

    t=1/lambda_S,   v_A=lambda_A/lambda_S.

All these numbers concern the same original family. E_S is contained in
E_A, so 1<=v_A<=t. The established same-family bounds R35<=15/7 and
R357<=1649/360 give

    lambda35 >= 2/3,
    lambda357 >= (4/7) lambda35 >= 8/21,
    lambdaS >= (1591/3240) lambda357 >= 1591/8505.

Thus t<=8505/1591. All relevant conditional laws exist because these
lower bounds are positive.

Under P, all forbidden classes of exact support U have total mass at most

    r_U=product_{p in U} 1/(p-2).

Indeed each mixed modulus occurs at most once; summing its pure-coordinate
cylinder cap over positive exponents gives this product. For any collection
C of proper nonsingleton subsets of B, the union bound gives

    lambda_B >= sum_{A in C} lambda_A - (|C|-1) - r,

where r is the sum of r_U over supports U subset B not contained in any
member of C. This is valid even when the events in C overlap.

The shared laws do not satisfy an automatic positive-correlation rule.
For example, take just the actual forbidden classes `0 mod 15` and
`1 mod 21`. They lie in different ternary roots, hence are disjoint.
There are no pure forbidden classes, so `P` is uniform and

    lambda35=14/15, lambda37=20/21, lambda357=31/35
             < lambda35 lambda37=8/9,

with difference `-1/315`. Thus FKG cannot be invoked merely from the
prime-product coordinates: arbitrary forbidden residue events do not
supply its required monotonicity hypotheses. The union bounds above
retain this negative-correlation possibility.

A cylinder C_T restricted to coordinates T is independent of E_(S minus T)
under P. Since E_S is contained in that complement event,

    mu_S(C_T)
      <= v_(S minus T) product_{p in T} (p-1)/((p-2)p^e_p).       (1)

This cylinder bound and all density inequalities therefore use one law.

#### Five strictly improved independent projection coefficients

The common-density inequalities imply the following ordinary c coefficients
in the bound mu_S(C_T)<=c_T/product p^e_p:

| T | previous c_T | new c_T |
|---|---:|---:|
| {3} | 17010/1591 | 16412/1591 |
| {5} | 9360/1591 | 25264/4773 |
| {7} | 1344/361 | 5916/1591 |
| {3,11} | 18900/1591 | 18540/1591 |
| {5,7} | 13608/1591 | 12784/1591 |

For the first three, the missing-support union bounds give respectively

    v5711 <= 1+(7/9)t <= 8206/1591,
    v3711 <= 1+(5/9)t <= 6316/1591,
    v3511 <= 1+(53/135)t <= 4930/1591.

For the fourth, v57<=v357+(3/5)t and v357<=3240/1591 give
v57<=8343/1591. For the fifth, use the overlapping events E311 and E357.
The uncovered-support budget is 2/15, so

    v311+v357-(17/15)t <= 1.

Together with v357>=(8/21)t this gives
v311<=1+(79/105)t<=7990/1591. Applying (1) proves the table. These
coefficients alone improve the compatible-layout head to 1509236/14319;
the stronger result below uses the densities jointly.

#### Retaining v35 in the compatible-layout transfer

The exact pointwise domination is

    mu_S <= v35 (mu35 x rho7 x rho11).

Fix any complete test layout. Group its ordered pairs by their outside
lcm exponents at 7 and 11. For a fixed outside exponent pair, the outside
test residues may depend on both old divisors. Integrating each old pair
first over rho7 x rho11 gives a uniform outside-cylinder bound; only then
sum the old indicators. The remaining cross moment is between two complete
{3,5} layouts, hence is at most Gamma(mu35)<=57/4 by Cauchy--Schwarz.

Summing all blocks with positive 7 exponent, including all 11 exponents,
therefore gives the bound

    (57/4) v35
      * [sum_{e7>=1} (2e7+1)(6/5)7^(-e7)]
      * [1+sum_{e11>=1} (2e11+1)(10/9)11^(-e11)]
     = (57/4)(2/3)(61/45) v35
     = (1159/90) v35.                                  (2)

No positive 7 block is bounded by an independently optimized residue
layout. The complementary e7=0 blocks are bounded by the original c/b
profile and the common-density cylinders (1).

#### Exact e7=0 profile sum and six inequalities

Use the original exact profile cutoffs (2,1,0,0). In a cell label
(s3,s5,s7,s11), values 3,2,1,1 denote the respective positive tail beyond
those cutoffs. The following ten cells use (1) with the displayed
projection support; the other e7=0 cells retain their old profile bound.

| Cell | Projection support |
|---|---|
| (0,0,0,1) | {11} |
| (0,1,0,0) | {5} |
| (0,1,0,1) | {5,11} |
| (0,2,0,0) | {5} |
| (0,2,0,1) | {5,11} |
| (2,0,0,1) | {3,11} |
| (3,0,0,0) | {3} |
| (3,0,0,1) | {3,11} |
| (3,2,0,0) | {3,5} |
| (3,2,0,1) | {3,5,11} |

Each chosen support contains every coordinate in that cell's tail, so its
tail factors exactly. Use

    sum_{e>L} (2e+1)p^(-e)
      = ((2L+3)(p-1)+2)/(p^L(p-1)^2).

The other cells, together with the unit term, sum to 332692/7955. Adding
(2) gives the affine head bound C+L, where C=332692/7955 and

    L = (704/6075)t + (1159/90)v35 + (56/135)v37
        + (32/45)v57 + (44/135)v711 + (16/45)v357
        + (7/6)v3711 + (8/9)v5711.                    (3)

The following six valid inequalities have the stated nonnegative
multipliers:

| Inequality, left side <= right side | Multiplier |
|---|---:|
| (4/7)v35-v357 <= 0 | 2135/108 |
| v57-v357-(3/5)t <= 0 | 1/54 |
| v35+v37+v57-v357-(31/15)t <= 0 | 56/135 |
| (1591/3240)v357 <= 1 | 66606/1591 |
| v35+v57+v3711-(97/45)t <= 1 | 5/18 |
| v35+v3711+v5711-(19/9)t <= 1 | 8/9 |

The first and fourth are the proved prime-adjoining inequalities. The
second uses the missing supports involving 3 in {3,5,7}, of budget 3/5.
The third unions all three pair events, leaving exact support {3,5,7},
whose budget is 1/15. The fifth uses C={{3,5},{5,7},{3,7,11}}, whose
uncovered supports have total budget 7/45. The sixth uses
C={{3,5},{3,7,11},{5,7,11}}, leaving total budget 1/9. Thus every row
follows from the stated common-law union bound or prime-adjoining bound.

The weighted sum of these six left sides differs from L only by

    (21017/6075)t + (44/135)v711.

Both variables are at most 8505/1591, and both coefficients are positive.
The six weighted right sides sum to 66606/1591+7/6. Consequently

    Gamma(mu_S)
      <= 332692/7955 + 66606/1591 + 7/6
         + (21017/6075+44/135)(8505/1591)
       = 5015891/47730.

The finite/tail cells cover all exponent heights. For finite periods,
absent blocks are simply zero and all added bounds are nonnegative.

#### Exact verification and continuation

[The common-density verifier](../docs/reports/erdos7-odd-covering/verify_common_density_head.py)
and its [fixed certificate](../docs/reports/erdos7-odd-covering/common_density_head_certificate.json)
independently reconstruct the original
profile, the ten cell choices, all tail sums, and the six-row rational
identity. Ordinary Python and Python -O both exit 0. It also verifies the
fixed prime-67/71/73 continuation, giving

    F73 = 18990969219984662521362/138335257526567659561
        = 137.2822052710416... < 138877/1000.

The fixed certificate records the ten selected density cells, thirteen remaining
profile cells, six nonnegative density-row multipliers, and two positive
variable-bound corrections. Its six density rows plus ten selected
cylinder inequalities are the sixteen used dual rows; no omitted solver
state is needed to check the result. No Lean kernel certification is
claimed for this mathematical proof.

### Shared-cofactor refinement of the four-prime head (P2)

For a finite distinct-modulus residue family supported on {3,5,7,11}, use
its actual product of pure-prime survivor laws P. Let lambda_A be the
P-probability of avoiding all mixed forbidden classes supported on A,
t=1/lambda_35711, and v_A=lambda_A/lambda_35711. All densities and layout
moments below concern this same family. The analytical two-prime input is
the uniform complete-survivor layout theorem Gamma_35 <= 55/4.

The common-density argument and its original cylinder profile give

    Gamma_35711 <= C + L,        C = 332692/7955,
    L = (704/6075)t + (671/54)v35 + (56/135)v37
        + (32/45)v57 + (44/135)v711 + (16/45)v357
        + (7/6)v3711 + (8/9)v5711.

Indeed, the blocks of positive 7-lcm exponent contribute at most

    (55/4) v35 (2/3)(61/45) = (671/54)v35.

The zero-7-lcm blocks use the common-density cylinder proof's ten
complement-density cells and thirteen remaining original-profile cells,
with the unit term counted separately. Their exact infinite tail sums
are unchanged. The proof of the positive-7 bound integrates the outside
cylinders first and then applies Cauchy--Schwarz to the two complete
{3,5} test layouts under the same mu35.

Use the following six inequalities with nonnegative multipliers:

| Left side <= right side | Multiplier |
|---|---:|
| (4/7)v35-v357 <= 0 | 854/45 |
| v57-v357-(3/5)t <= 0 | 1/54 |
| v35+v37+v57-v357-(31/15)t <= 0 | 56/135 |
| (1591/3240)v357 <= 1 | 64044/1591 |
| v35+v57+v3711-(97/45)t <= 1 | 5/18 |
| v35+v3711+v5711-(19/9)t <= 1 | 8/9 |

The first and fourth rows are the same-law prime-adjoining inequalities;
the others are actual forbidden-union bounds. Their weighted sum has
right side 64044/1591+7/6. Subtracting their weighted left sides from L
leaves exactly

    (21017/6075)t + (44/135)v711.

Both variables lie in [0,8505/1591]. Therefore

    Gamma_35711
      <= 332692/7955 + 64044/1591 + 7/6
         + (21017/6075+44/135)(8505/1591)
       = 4939031/47730 = 103.4785459878483... .

The exact decrease from the 57/4-input certificate is 2562/1591. The
changed coefficients satisfy the two direct identities

    (2135/108-854/45)(4/7) = 1159/90-671/54,
    (66606/1591-64044/1591)(1591/3240) = 2135/108-854/45,

so this refinement introduces no new density inequality.

The fixed recurrence

    F_next = F (1+(3p-1)/((p-1)^2(1-delta)))
                 / (1-F/(4 delta (1-delta)(p-1)^2))

has the following exact continuation, starting at F=4939031/47730:

| p | delta | Positive survival denominator | Output F |
|---:|---:|---:|---:|
| 67 | 1/4 | 150994879/155933910 | 17123620477/150994879 |
| 71 | 53/200 | 55931291964461/57643654012161 | 6921898229038187/55931291964461 |
| 73 | 27/100 | 138545600701541742901/142871787094690609776 | 18699964911029778700842/138545600701541742901 |

The final value is 134.973357626228... < 138877/1000, with positive margin

    540832477598233928020177/138545600701541742901000.

[The coupled-head verifier](../docs/reports/erdos7-odd-covering/verify_common_density_head_coupled.py)
and its [fixed certificate](../docs/reports/erdos7-odd-covering/common_density_head_coupled_certificate.json)
reconstruct the entire original profile, finite/tail cells, six-row
certificate and this continuation using exact standard-library rational
arithmetic. Normal, optimized (-O), and isolated (-I) invocations all
exit 0. These checks certify the arithmetic implication of the stated
analytical inputs; no Lean kernel certification is claimed.

### A positive atomic representation of the extremal three-prime densities

The density coordinates used by the exact R357=1649/360 relaxation
certificate are

    (t,v35,v37,v57)=(21/8,7/4,21/10,103/40).

They admit a genuine positive probability space for the abstract subsystem
survival events. Consequently, adding Gram positivity or higher moment
positivity for those events alone cannot exclude this density point.
This probability space is not asserted to arise from actual residue
classes; it does not rule out an improvement using CRT compatibility or
the actual cylinder indicators.

Let Ω have five atoms. The table gives their probabilities and indicators
of E357, E35, E37, E57:

| Probability | E357 | E35 | E37 | E57 |
|---:|---:|---:|---:|---:|
| 8/21 | 1 | 1 | 1 | 1 |
| 1/15 | 0 | 1 | 1 | 1 |
| 2/105 | 0 | 1 | 1 | 0 |
| 1/5 | 0 | 1 | 0 | 1 |
| 1/3 | 0 | 0 | 1 | 1 |

All probabilities are strictly positive and their sum is one. Direct
summation gives

    λ357=8/21, λ35=2/3, λ37=4/5, λ57=103/105.

Dividing by λ357 gives exactly the displayed density coordinates.
Moreover,

    P(E35∩E37)=49/105,
    P(E35∩E57)=68/105,
    P(E37∩E57)=82/105,
    P(E35∩E37∩E57)=47/105.

Thus the pair-survival failures have disjoint masses 1/3, 1/5, and
2/105<=1/15; the extra failure of full three-prime survival has mass
1/15. These satisfy the exact-support budgets. Every union-of-subsystems
inequality derived only from those budgets is therefore valid on this
atomic model. The three prime-adjoining bounds also hold:

    λ357=(4/7)λ35,
    λ357 >= (6/13)λ37 = 24/65,
    λ357 >= (5/14)λ57 = 103/294.

For a concrete matrix certificate, put Y=(1,1_E357,1_E35,1_E37,1_E57).
The normalized Gram matrix M=E[YYᵀ]/λ357 is

    [ 21/8   1   7/4    21/10   103/40 ]
    [ 1      1   1      1       1      ]
    [ 7/4    1   7/4    49/40   17/10  ]
    [ 21/10  1   49/40  21/10   41/20  ]
    [ 103/40 1   17/10  41/20   103/40 ].

Its positive rank-one decomposition uses the five table vectors, prefixed
by 1, with weights

    1, 7/40, 1/20, 21/40, 7/8.

For every real vector z,

    zᵀMz = sum_ω weight(ω) (z·Y(ω))² >= 0.

In fact M is positive definite: the five vectors span R⁵. Subtracting the
second vector from the first isolates the E357 coordinate; subtracting
each of the last three vectors from the second isolates the other three
event coordinates; the constant coordinate follows. Hence a zero quadratic
form forces z=0. No numerical eigenvalue calculation is needed.

For arbitrary polynomial functions f₁,...,f_m of these indicators, the
same identity shows the moment matrix E[f_i f_j] is positive semidefinite.
All Boolean relations and inclusions E357⊆E35∩E37∩E57 hold pointwise.
The obstruction therefore applies to every order of abstract subsystem
moment positivity, not merely to a second-order PSD relaxation. It does
not apply to matrices that additionally encode realizable congruence
intersections or conditional root-residue profiles.

### Nonuniform two-root survivor laws

The following two-prime constructions remain valid. The uniform law in
(ZG1) now gives the stronger pair `(Γ35,R35)≤(55/4,15/7)`, which dominates
both (N1) and (N2). Their weighted-root method also supplies the different
nonuniform construction for the rectangular obstruction family below.

For every finite family of distinct moduli supported on `{3,5}`, there is a
probability law supported on its complete survivor set satisfying

\[
 \boxed{\Gamma\le14,\qquad R\le15/7.} \tag{N1}
\]

This law is either the uniform survivor law or a specified law constant
within each of the two surviving ternary roots. A single explicit weighting
rule also gives the separate tradeoff

\[
 \boxed{\Gamma\le277/20,\qquad R\le11/5.} \tag{N2}
\]

These are arbitrary-height mathematical bounds with exact rational
verification of the continuous parameter inequalities. They are not Lean
formalizations, and the new law does not inherit uniform-law profile bounds.

#### Complete-survivor parameters and positivity

First suppose an actual modulus-3 class is present. Let `A,B` be the other
two ternary roots, and let `w,v` be their relative pure-ternary survivor
densities. Set `y=1/4`, `a=7/8`. The established distinct-modulus budgets are

\[
 1/2\le w,v\le1,\quad w+v\ge3/2,\quad
 3/4\le z\le1,\quad \alpha,\beta\ge0,\quad\alpha+\beta\le y,
\]
\[
 t,u\ge0,\quad t+u\le y/6,\qquad
 d=z-\alpha,\quad e=z-\beta,\quad
 n=wd/3-t,\quad m=ve/3-u. \tag{N3}
\]

Here `z` is the pure-5 survivor density, `α,β` are the actual first-level
mixed exclusions inside it, and `t,u` are the remaining mixed exclusions in
the two roots. The complete survivor densities `n,m` are exact. Both satisfy

\[
 n,m\ge\tfrac12\frac{1-2y}{3}-\frac y6=\frac1{24}>0. \tag{N4}
\]

Thus an empty surviving root cannot occur for this family class. All
normalizations below are positive. Missing higher powers merely decrease
the actual exclusions and are already included in these inequalities.

For arbitrary `h,k≥0`, not both zero, put `S=hn+km`. Give raw survivor
points in `A,B` the density multipliers `h,k`, respectively, and normalize
by `S`. This defines a complete-survivor probability `μ_{h,k}`. Write

\[
 x_h=(hw+kv)/3,
\]
\[
 P_h=\max\{h(3n+d),\ 3hn+2ke/3,\ k(3m+e),\ 3km+2hd/3\},
\]
\[
 Q_h=\max\{h(w+1),\ hw+2k/3,\ k(v+1),\ kv+2h/3\}. \tag{N5}
\]

#### Weighted layout and cylinder inequalities

The universal weighted-root bounds are

\[
 \Gamma(\mu_{h,k})\le1+\frac{P_h+a(x_h+Q_h)}S, \tag{N6}
\]
\[
 R(\mu_{h,k})\le\frac{\max(hn,km)+\max(hd,ke)/6
       +y\{x_h+\max(hw,kv)/3+\max(h,k)/6\}}S. \tag{N7}
\]

To prove (N6), first consider the pure-ternary part of one complete test
layout. Its root masses before normalization are `hn,km`; its depth-`j`
cylinder caps in the two roots are `hd/3^j,ke/3^j`. The existing two-root
finite-itinerary Bellman inequality, applied to these weighted caps, bounds
its second moment by `S+P_h`. The constant diagonal is `S` and the
modulus-3 diagonal plus its two crosses with the constant give `3hn` or
`3km`. All later choices, including choices in the forbidden root, are
included by that same finite-itinerary argument.

For positive 5 exponents, let `η` be the finite positive measure on the
pure-ternary survivor set with root density multipliers `h,k` and no mixed
exclusions. Its mass is `x_h`, root masses are `hw/3,kv/3`, and depth caps
are `h/3^j,k/3^j`. The same Bellman inequality gives
`Γ(η)≤x_h+Q_h`.

Group ordered test-divisor pairs by their 5-adic least-common-multiple
exponent `b≥1`. For each ordered pair of outside exponents with maximum
`b`, the two old residue choices form complete pure-ternary layouts,
including divisor one and every old cofactor. The selected 5-adic residues
may depend on the old divisor. Pair by pair their intersection has uniform
5-adic mass at most `5^{-b}`. Dropping actual 5 and mixed exclusions only
increases the nonnegative integral. After summing the old indicators,
Cauchy–Schwarz under `η` bounds the cross moment of the two complete old
layouts by `Γ(η)`. There are `2b+1` outside exponent pairs. Finally
`∑_{b≥1}(2b+1)5^{-b}=7/8=a`, proving (N6) after division by `S`.
This whole-layout estimate replaces the weaker maximum-root-density cap.

For (N7), the pure-ternary cylinder sum is bounded by
`max(hn,km)+max(hd,ke)∑_{j≥2}3^{-j}`. For every positive 5 exponent, drop
its exclusions and sum the pure-ternary cylinder maxima of `η`. The
constant term is `x_h`, its depth-one term is `max(hw,kv)/3`, and its
remaining tail is `max(h,k)/6`. Summing `5^{-b}` over `b≥1` contributes
`y`. This proves (N7). Both arguments are upper bounds for every finite
prime height; the infinite series omit no actual test divisor.

#### Explicit balanced law and full continuous-domain certificate

Choose

\[
 h=v+1,\qquad k=w+1. \tag{N8}
\]

The first and third terms of `Q_h` then both equal `(w+1)(v+1)`. Each
cross term is smaller, since `2(w+1)/3≤v+1` and its symmetric inequality
hold throughout (N3). Consequently `Q_h=(w+1)(v+1)`.

For each of the four branches of `P_h`, clear the positive denominator in
(N6) with proposed bound `277/20`. For each of the sixteen choices of the
four maxima in (N7), do the same with proposed bound `11/5`. The resulting
20 polynomial margins are nonnegative throughout (N3), as follows.
They are separately affine in the three parameter groups
`(α,β)`, `z`, and `(t,u)`, so it suffices to use their `3×2×3=18` vertices.
At each such vertex they have the form

\[
 f(w,v)=A_0+B_0w+C_0v+D_0wv.
\]

On the triangle `1/2≤w,v≤1`, `w+v≥3/2`, such a bilinear function has no
strict interior minimum. Its edges `w=1` and `v=1` are affine. On the
remaining edge substitute `v=3/2−w`, `1/2≤w≤1`, and check the quadratic's
endpoints and any interior critical point with positive quadratic
coefficient. This is a complete exact minimum calculation, not a grid.
The accompanying verifier checks all `20×18=360` minima with rational
arithmetic; every margin is nonnegative. This proves (N2).

#### Uniform fallback preserving the R bound

Let `U` denote the right side of (N6) at `h=k=1`. Define the law in (N1):
choose the uniform complete-survivor law when `U≤14`; otherwise choose
(N8). The uniform case has `Γ≤14` by (N6), and its established nine-cell
bound gives `R≤15/7`. It remains to prove the same R bound when `U>14`.

With `h=k=1`, `Q_h=max(w+1,v+1)`. Number the four pure branches in the
order of (N5), starting at zero, and the two mixed branches `w+1,v+1`
also starting at zero. Define the eight uniform margins

\[
 F_i=13(n+m)-P_{\lfloor i/2\rfloor}
                -a\{(w+v)/3+Q_{i\bmod2}\},\qquad0\le i<8.
\]

Then `U>14` means at least one `F_i<0`. Six of these margins, all except
`F_1,F_4`, are nonnegative throughout (N3). Let `E_j`, `0≤j<16`, be the
balanced-law R margins at `15/7`. Their branch order is the lexicographic
order of choices from `(hn,km)`, `(hd,ke)`, `(hw,kv)`, `(h,k)`, with the
last choice varying fastest. For each `i∈{1,4}`, the following nonnegative
multipliers satisfy `E_j+λ_{ij}F_i≥0` throughout (N3):

| `i` | Nonzero multipliers; all others zero |
| --- | --- |
| `1` | `λ_1,4=1/168`, `λ_1,5=1/21`, `λ_1,10=8/21`, `λ_1,11=1/21` |
| `4` | `λ_4,4=1/21`, `λ_4,5=8/21`, `λ_4,10=1/21`, `λ_4,11=1/168` |

The same affine-group and bilinear-triangle method checks the six safe
uniform margins and these 32 combined margins: `38×18=684` exact
continuous minima. Hence if a uniform branch fails, every `E_j≥0`, giving
`R≤15/7` for the balanced choice. Its Gamma is already at most
`277/20<14`. This proves (N1).

If the actual modulus-3 class is absent, choose the established uniform
law, whose unsplit bounds are `Γ≤215/24` and `R≤17/12`; these satisfy
both (N1) and (N2). Thus no choice of a nonexistent pair of roots is needed.

#### Coherent propagation to three primes and its limitation

Keep the chosen two-root multipliers fixed. Form the product of this
complete `{3,5}` law with the uniform pure-7 survivor law, and then condition
away the new mixed classes. This produces a law on the full `{3,5,7}`
survivor set with the same fixed root multipliers. It is generally
nonuniform. No estimate proved only for the uniform `{3,5,7}` law is used.

For an input pair `(G,R)`, the deleted mass `λ` is at most `R/5`. The
pure-7 cylinder caps give a product-layout bound `(5/3)G`, and the product
cylinder sum is at most `(6/5)(R+1)−1`. Every complete layout load is at
least one, so deleting mass `λ` removes at least `λ` from its second
moment. Both normalized upper bounds increase with `λ`, giving

\[
 \Gamma_{357}\le\frac{(5/3)G-R/5}{1-R/5},\qquad
 R_{357}\le\frac{(6/5)(R+1)-1}{1-R/5}. \tag{N9}
\]

For the uniform law from (ZG1), the same construction is again uniform
on the complete three-prime survivors. Substituting `G=55/4`, `R=15/7`
in the first inequality gives

\[
 \Gamma_{357}\le\frac{(5/3)(55/4)-3/7}{1-3/7}=\frac{1889}{48}.
\]

This law also has the established uniform bound `R357≤1649/360`.
Both coordinates improve the following nonuniform propagation bounds;
this is a direct consequence of (ZG1), not a separate Lean theorem.

Thus the balanced law gives `(Γ357,R357)≤(6793/168,71/14)`, while the
hybrid law gives

\[
 \boxed{\Gamma_{357}\le481/12,\qquad R_{357}\le97/20.} \tag{N10}
\]

The Gamma bound is below the earlier `653/16` transport bound. Its R bound
is above the uniform-law `1649/360` bound; those two estimates concern
different laws and cannot be combined. Continuing (N9)'s argument through
prime 11 gives only `Γ35711≤350/3` for the hybrid law, above the established
uniform four-prime bound `4939031/47730`. No four-prime or unrestricted
Erdős #7 improvement follows from the present propagation.

[The nonuniform-law verifier](../docs/reports/erdos7-odd-covering/verify_nonuniform_root_law.py)
and its [fixed certificate](../docs/reports/erdos7-odd-covering/nonuniform_root_certificate.json)
verify the 1,044 continuous polynomial minima, root positivity, absent-modulus
branch, both law bounds, fixed fallback multipliers and exact coherent
propagation. The numerical certificate concerns only these rational
inequalities; the weighted-layout mapping above is an ordinary proof.

#### Search result and reuse boundary

The local project supplies the two-root Bellman theorem and the existing
uniform cylinder bounds. Pinned Mathlib provides `Sion.exists_isSaddlePointOn`
for compact convex minimax; no new minimax wrapper is needed here.
BBMST, arXiv:1901.11465, section 5.3, constructs nonuniform survivor
probabilities by linear programming and controls subsequent deletion and
renormalization. That construction is squarefree and does not directly
supply (N6)–(N10) for arbitrary powers. The new step here is the weighted
complete-layout inequality and its continuous distinct-modulus budget
certificate, not the general linear-programming method.

### A universal nonuniform law below the sharp uniform bound

For every finite family of distinct moduli greater than one supported on
`{3,5}`, with one forbidden residue class per modulus, there is a probability
law `μ` on its complete survivor set such that

\[
 \boxed{\Gamma(\mu)\le687/50<55/4,\qquad
 R(\mu)\le37/17,\qquad
 \frac{d\mu}{dU_S}\le16/15.} \tag{NC1}
\]

Here `U_S` is the uniform law on the same complete survivor set. The last
inequality is pointwise. The law is constant within each surviving ternary
root; its ratio of root multipliers is one of `1`, `11/12`, and `12/11`.
The finite prime heights and the mixed residue choices are arbitrary. The
Gamma bound is strictly below the sharp universal uniform-law bound; the
R bound is higher than the uniform-law `15/7` bound.

As usual, a complete test layout chooses one residue for every divisor of
the finite product period, including divisor one. Its load `L` is the sum
of those indicators, and `Γ(μ)=max_L ∫L² dμ`. Define
`R(μ)=∑_{d>1} max_a μ(a mod d)`, over the same divisors. Neither the
layouts nor the mixed forbidden classes are assumed to have product form.

#### Actual parameters and the law

Suppose first that an actual modulus-3 class is present. Its complement
consists of two ternary roots `A,B`. Set `y=1/4` and `a=7/8`. The actual
pure-ternary survivor densities within these roots are `w,v`; the actual
pure-5 survivor density is `z`. Within the pure-5 survivors, let `α,β` be
the ambient 5-coordinate measures excluded by the union of the `3·5^b` classes whose ternary
root is respectively `A,B`. These unions are constant across their whole
ternary root. Let `t,u` be the further ambient masses removed in `A,B`
by classes `3^i5^b` with `i≥2,b≥1`, after the preceding exclusions.
Distinct moduli give the budgets

\[
 1/2\le w,v\le1,\quad w+v\ge3/2,\qquad
 3/4\le z\le1,\quad \alpha,\beta\ge0,\quad\alpha+\beta\le1/4,
\]
\[
 t,u\ge0,\quad t+u\le1/24,\qquad
 d=z-\alpha,\quad e=z-\beta,\quad
 n=wd/3-t,\quad m=ve/3-u. \tag{NC2}
\]

The last two quantities are the exact ambient densities of complete
survivors in the two roots. Indeed the sum of pure-ternary exclusions at
depth at least two is at most `1/6`; the first mixed layer has total 5-mass
at most `y`; and the deeper mixed classes have total ambient mass at most
`(1/6)y`. Omitting any actual modulus only reduces these budgets. In
particular `d,e≥1/2` and

\[
 n,m\ge(1/2)(1/2)/3-1/24=1/24>0. \tag{NC3}
\]

For positive numbers `h,k`, give each complete survivor in `A` raw density
`h`, and each in `B` raw density `k`, relative to ambient uniform measure.
Normalize this measure by `S=hn+km` to obtain `μ_{h,k}`. This definition
allows old fibres to be partly or entirely removed. It never conditions
on a fibre having positive mass. Both surviving roots themselves have
positive mass by (NC3).

Let `η` be the raw pure-ternary survivor measure with the same root
multipliers `h,k`, and set

\[
 x=(hw+kv)/3,\qquad
 A_A=\max\{h(w+1),hw+2k/3\},\quad
 A_B=\max\{k(v+1),kv+2h/3\},\quad B=\max(A_A,A_B),
\]
\[
 P_A=\max\{3hn+hd,3hn+2ke/3\},\qquad
 P_B=\max\{3km+ke,3km+2hd/3\}. \tag{NC4}
\]

The coupled weighted envelope is

\[
 \Gamma(\mu_{h,k})\le1+
 \frac{\max\{P_A+ax+yA_A+(a-y)B,
                 P_B+ax+yA_B+(a-y)B\}}{S}. \tag{NC5}
\]

#### Preserving the zero-exponent layout

Fix a complete `{3,5}` test layout `L`. For each 5-exponent `b`, let `L_b`
be its complete pure-ternary layout after stripping the 5-parts of the
divisors. Divisor one and every old cofactor remain. The selected 5-adic
residue may depend on the old cofactor. The positive-measure domination

\[
 \mu_{h,k}\le S^{-1}(\eta\times U_5)
\]

holds by dropping pure-5 and mixed exclusions, without requiring any
conditional fibre lower bound. Write `A_0=∫L_0² dη` and `B_0=Γ(η)`.
The zero-zero block is exactly `∫L_0² dμ_{h,k}`. For the ordered blocks
`(0,b),(b,0)` at positive exponent `b`, each pair of outside cylinders
has uniform intersection mass at most `5^{-b}`. Sum this bound over the
old indicators before applying `2L_0L_b≤L_0²+L_b²`. Their joint
contribution is at most `5^{-b}(A_0+B_0)/S`.

There are `2b−1` remaining ordered exponent pairs with both exponents
positive and maximum `b`. Each old-layout cross moment is at most `B_0`
by Cauchy–Schwarz. Since
`∑_{b≥1}5^{-b}=y` and `∑_{b≥1}(2b−1)5^{-b}=a−2y`, it follows that

\[
 \int L^2\,d\mu_{h,k}\le\int L_0^2\,d\mu_{h,k}
               +\frac{yA_0+(a-y)B_0}{S}. \tag{NC6}
\]

All omitted infinite-tail terms are nonnegative, so this holds at every
finite height. It is an inequality for each fixed `L`; the same `L_0`
must occur in both terms on the right.

Apply the established root-labelled finite-itinerary Bellman bound to
this `L_0`. For the raw complete measure the two root masses are `hn,km`
and the depth-`j` cylinder caps are `hd/3^j,ke/3^j`. Under `η` the
corresponding data are `hw/3,kv/3` and `h/3^j,k/3^j`.
If the modulus-3 test chooses root `A`, these bounds give

\[
 \int L_0^2\,d\mu_{h,k}\le1+P_A/S,\quad
 A_0\le x+A_A,\quad B_0\le x+B. \tag{NC7}
\]

For root `B` use `P_B,A_B`. The root-labelled formula accounts for the
constant diagonal, the initial-root diagonal and constant crosses, and
all later choices, including moves between the two surviving roots.
It is the same finite-itinerary inequality underlying
`TernaryRootLoadTail.root_load_tail_le` and
`TwoRootEventMoment.two_root_event_moment_le`; no product-layout
assumption is introduced.

If the modulus-3 test instead chooses the actual forbidden root, its event
has zero mass. The same tail bound gives raw excess at most
`(2/3)max(hd,ke)` and `A_0−x≤(2/3)max(h,k)`. This branch is dominated:
if `hd≥ke`, use the `B` branch, since `P_B≥2hd/3` and
`A_B=max(k(v+1),kv+2h/3)≥(2/3)max(h,k)`. If `ke≥hd`, use `A`
symmetrically. Substitution in (NC6) proves (NC5), including this third
possible initial test root.

The same law also obeys the cylinder envelope

\[
 R(\mu_{h,k})\le
 \frac{\max(hn,km)+\max(hd,ke)/6
       +y\{x+\max(hw,kv)/3+\max(h,k)/6\}}{S}. \tag{NC8}
\]

For pure ternary divisors the first term handles depth one, and the
remaining cap sum is `max(hd,ke)∑_{j≥2}3^{-j}`. For each positive
5-exponent, dropping its exclusions leaves the pure-ternary cylinder
sum of `η`, including the divisor-one mass `x`. Summing `5^{-b}`
gives (NC8). The pointwise relative density is exactly `h(n+m)/S`
on root `A` and `k(n+m)/S` on root `B`; consequently

\[
 \frac{d\mu_{h,k}}{dU_S}\le\frac{(n+m)\max(h,k)}{S}. \tag{NC9}
\]

#### The adaptive rule and its exact certificate

Let `C=687/50`. Expand (NC5)'s maxima into 32 numerators `N_j` in this
order: first choose `(P_A,A_A)` or `(P_B,A_B)`; then one of the two
displayed entries of that `P`; then one of the two entries of that `A`;
finally one of the four entries of `(A_A,A_B)`, with the last choice
varying fastest. Set

\[
 E_j(h,k)=(C-1)(hn+km)-N_j(h,k),\qquad F_i=E_i(1,1). \tag{NC10}
\]

If every `F_i≥0`, choose `h=k=1`. Otherwise let `i` be the least index
with `F_i<0`, and choose weights as in the table. Only its six listed
indices can be negative anywhere in (NC2).
If several are negative, the same proof works for any one of them;
choosing the least index simply makes the law deterministic.

| Trigger `i` | `h`, with `k=1` | Nonzero `λ_ij`; all others zero | `ρ_i` |
| --- | --- | --- | --- |
| 0 | 11/12 | `λ_0,16=97/1764`, `λ_0,18=1135/6264`, `λ_0,26=535/6264` | 5/51 |
| 2 | 11/12 | `λ_2,16=97/6264`, `λ_2,18=1135/1764`, `λ_2,26=535/1764` | 10/1227 |
| 8 | 11/12 | `λ_8,16=97/1764`, `λ_8,18=1135/12264`, `λ_8,26=535/12264` | 5/801 |
| 16 | 12/11 | `λ_16,0=1135/1617`, `λ_16,2=97/5742`, `λ_16,8=535/1617` | 40/4499 |
| 18 | 12/11 | `λ_18,0=1135/5742`, `λ_18,2=97/1617`, `λ_18,8=535/5742` | 20/187 |
| 26 | 12/11 | `λ_26,0=1135/11242`, `λ_26,2=97/1617`, `λ_26,8=535/11242` | 20/2937 |

The fixed rational certificate verifies, throughout the full domain,

\[
 E_j(h_i,1)+\lambda_{ij}F_i\ge0\quad(0\le j<32),
\]
\[
 (16/15)(h_in+m)-\max(h_i,1)(n+m)+\rho_iF_i\ge0. \tag{NC11}
\]

Every multiplier is nonnegative. Hence `F_i<0` implies each required
Gamma margin and the density margin is nonnegative. It also checks all
16 cleared branches of (NC8) at `R=37/17`, globally for each of the two
fixed nonuniform ratios. No trigger restriction is needed for this R
bound. Its exact envelope maximum over the budget domain is `37/17`.
The uniform fallback uses the existing same-law `R≤15/7<37/17`, and
has relative density one.

This verification covers a continuous domain. Every cleared expression
in (NC10)–(NC11) and the fixed-weight R margins is affine in each of the
four groups `(w,v)`, `(α,β)`, `z`, `(t,u)` while the other groups are
fixed. Its value at a convex combination in any one group is the same
convex combination of vertex values. Applying this successively reduces
nonnegativity to exactly the `3·3·2·3=54` product vertices

\[
 (w,v)\in\{(1/2,1),(1,1/2),(1,1)\},\qquad
 (\alpha,\beta)\in\{(0,0),(1/4,0),(0,1/4)\},
\]
\[
 z\in\{3/4,1\},\qquad
 (t,u)\in\{(0,0),(1/24,0),(0,1/24)\}. \tag{NC12}
\]

The verifier checks 1,404 safe-uniform, 10,368 adaptive-Gamma, 1,728
fixed-weight-R, and 324 adaptive-density vertex inequalities: 13,824 in
total. Their minimum margins are respectively `97/1200,0,0,0`.
These checks require only exact rational arithmetic and remain active
under Python optimization. They do not approximate the parameter domain
by a grid or enumerate only selected finite families.

If an actual modulus-3 class is absent, choose the existing uniform law:
its bounds `Γ≤215/24`, `R≤17/12` and relative density one satisfy (NC1).
This includes missing powers and avoids inventing a pair of surviving
roots in that case. Thus (NC1) applies to all finite families under the
stated hypotheses.

#### Downstream use and boundary

The density bound can transfer any nonnegative observable from `U_S`
to this same-family law with factor at most `16/15`. It does not preserve
the uniform law's sharper cylinder profile unchanged, and it does not
state a conditional cap in every old fibre.

One coherent general propagation keeps the chosen root multipliers,
forms the product with the uniform pure-`p` survivor law, and conditions
away the new mixed classes. Given simultaneous bounds `(G,R)`, write
`ℓ=R/(p−2)`. When `ℓ<1`, the resulting law satisfies

\[
 G'\le\frac{\frac{p^2+1}{(p-1)(p-2)}G-\ell}{1-\ell},\qquad
 R'\le\frac{\frac{p-1}{p-2}(R+1)-1}{1-\ell}. \tag{NC13}
\]

The loss bound uses every old cofactor. The subtraction in the first
numerator is valid because each complete layout has load at least one
on the deleted set. Applying (NC13) to (NC1), then to prime 11, gives

\[
 (\Gamma_{357},R_{357})\le(1273/32,239/48),\qquad
 (\Gamma_{35711},R_{35711})\le(230569/1930,2438/193).
\]

The four-prime Gamma bound exceeds the existing uniform bound
`4939031/47730`. Thus the present general repair proves a strict
two-prime Gamma improvement, but this propagation does not improve the
known four-prime bound or establish the existential Gamma-73 target.

The [standalone verifier](../docs/reports/erdos7-odd-covering/verify_nonuniform_coupled_law.py)
and its [fixed certificate](../docs/reports/erdos7-odd-covering/nonuniform_coupled_certificate.json) check the displayed rational
certificate, positivity, fallback comparisons and propagation. The
arbitrary-family layout correspondence and continuous-domain reduction
above are ordinary mathematical proofs. No full Lean formalization of
(NC1) is claimed.

The reused local ingredients are the root-labelled finite-itinerary
estimate and uniform cylinder budgets. The nonuniform-survivor linear
program in [BBMST, section 5.3](../Library/Arith/balister2019erdos.md)
is a squarefree predecessor; it does not supply this arbitrary-power
weighted-envelope certificate.


### A shared-parameter improvement for arbitrary three-prime heights

For every finite family with distinct nonunit moduli supported on
`{3,5,7}`, the uniform law on its complete actual survivor set satisfies

\[
 \boxed{\Gamma_{357}\le\frac{937}{24}<\frac{1889}{48}.} \tag{JG1}
\]

The improvement is `5/16`. It keeps the old square bound and cylinder
sum in the same actual five-cell domain, rather than independently
maximizing the two inputs of (N9). It is an upper bound; sharpness for
actual families and a new tail cutoff are not asserted.

When the pure modulus-3 and modulus-9 exclusions are effective, use the
five cells and budgets of (CM2). Put `r(j)=(0,0,1,1,1)`, and retain

\[
 n_j=\frac{w_j(z-\alpha_{r(j)}-\beta_j)}9-t_j,
 \quad s=\sum_jn_j,\quad x=\frac{\sum_jw_j}9,
 \quad n_r=\sum_{r(j)=r}n_j,\quad
 v_r=\frac{\sum_{r(j)=r}w_j}3,\quad d_r=z-\alpha_r.
\]

Thus `v_r/3` is the actual pure-ternary mass in root `r`, and `n_r`
is its complete two-prime survivor mass. The deeper mixed deletion in
that root is exactly `sum_{r(j)=r}(w_j beta_j/9+t_j)`. Its total over
the two roots is at most `1/36+1/72=1/24`, so these quantities satisfy
the hypotheses of the unshifted (ZG3). In particular, the same law has

\[
 \Gamma_{35}\le U/s,\qquad R_{35}\le T/s,
\]
\[
 \begin{aligned}
 U&=s+\max_{r=0,1}\left\{3n_r+
       \max(d_r,2d_{1-r}/3)+\frac{x+v_r+1}4+
       \frac58(x+\max(v_0,v_1)+1)\right\},\\
 T&=\max(n_0,n_1)+\max_jn_j+z/18+x/4+1/8.
 \end{aligned}
\]

Here (ZG3) is used before moving any deletion between roots. Its actual
zero-exponent layout and the cylinder masses therefore use identical
cell parameters. Form the product with the actual pure-7 survivor law
and condition away the original mixed-7 classes. This produces the
uniform complete three-prime survivor law. Applying (N9) with these
same-parameter bounds gives

\[
 \Gamma_{357}\le
       \frac{(5/3)U-T/5}{s-T/5}.                     \tag{JG2}
\]

For fixed `s,U`, the displayed quotient increases in `T`, since
`U>=s>0`; it also increases in `U`. The maxima may consequently be
expanded into `2*2*2*2*5=80` branches: selected test root, its tail
choice, the pure square-norm root, the cylinder root, and the cylinder
cell. For each branch, both numerator and denominator of (JG2) are
affine separately in each of the five groups `1-w,alpha,beta,t,z`.
Their domain is precisely the product of the four budget simplexes
and the interval used in (CM2).

The denominator-weighted vertex identity therefore reduces each
branch to the same `6*3*6*6*2=1296` vertices. Exact arithmetic checks
all **103680** branch-vertex pairs: every denominator is at least
`53/360`, and every margin

\[
 (937/24)(s-T/5)-((5/3)U-T/5)
\]

is nonnegative. Separate affinity also transports denominator positivity
throughout the continuous domain. The relaxed maximum is `937/24`.
At one maximizing vertex the cell masses are
`(1/72,1/36,1/12,1/12,1/12)`, with

\[
 s=7/24,\quad U=191/48,\quad T=5/8,\quad
 U/s=191/14<55/4,\quad T/s=15/7.
\]

This explains why the independent input maxima lose information.
The maximizer is a parameter-relaxation certificate, not a claim of
attainment by actual residue classes.

If modulus 3 is absent, the established same-law bounds
`Gamma35<=215/24` and `R35<=17/12` give `Gamma357<=5273/258` by (N9).
If modulus 3 is present but modulus 9 is absent or ineffective, use
`Gamma35<=55/4` and `R35<=47/24`, giving `Gamma357<=2703/73`.
Both are strictly below `937/24`; these cases include smaller actual
ternary heights. Arbitrary finite heights at 5 and 7 are already
covered by the geometric sums and missing-class allowances.

The existing [cofactor verifier](../docs/reports/erdos7-odd-covering/verify_uniform_gamma_cofactor_coupling.py)
checks the continuous-domain certificate and both missing-class branches
under `shared_three_prime_parameters`. It preserves the earlier
72-branch square certificate. The transfer and vertex argument above
are ordinary mathematical proofs; this is not an end-to-end Lean
statement or a new unrestricted-tail exclusion.

### Signed deletion with both initial ternary test prefixes

For the same uniform law on complete actual survivors, at arbitrary finite
heights of 3, 5 and 7, the shared-cell argument strengthens to

\[
 \boxed{\Gamma_{357}\le\frac{3849}{106}<\frac{937}{24}.} \tag{SD1}
\]

The improvement over (JG1) is `3473/1272`. This bound retains the actual
zero-seven test layout in both its product cross terms and the energy
removed by the mixed-seven classes. It makes no optimal-law, actual-family
sharpness or new tail-cutoff claim.

First suppose the original pure modulus-3 and modulus-9 exclusions are
effective. Use exactly the five-cell parameters of (CM2), without moving
any deletion between cells, and write

\[
 d_l=z-\alpha_{r(l)}-\beta_l,\qquad
 n_l=w_ld_l/9-t_l,\quad s=\sum_ln_l,\quad
 x=\sum_lw_l/9,\quad
 n_r=\sum_{r(l)=r}n_l,\quad v_r=\sum_{r(l)=r}w_l/3.
\]

Let `A0` be the zero-seven block of a complete test layout; it is itself
a complete `{3,5}` test load. Retain the root `r` and cell `j` chosen by
the modulus-3 and modulus-9 tests in its zero-five block. If either test
is inactive on pure survivors, changing it to any surviving root or cell
increases the whole load pointwise. Thus it suffices to consider these
`2*5` choices. The two choices are independent: the test cell need not
lie in the test root.

Define `c_l=3+2*1[r(l)=r]+2*1[l=j]` and

\[
 \begin{aligned}
 P_{rj}&=s+3n_r+(3+2\mathbf1_{r(j)=r})n_j
       +\frac{\max_l(c_ld_l)+\max_ld_l}{18},\\
 V_{rj}&=x+v_r+(3+2\mathbf1_{r(j)=r})w_j/9
       +\frac{\max_lc_l+1}{18},\\
 U_{rj}&=P_{rj}+V_{rj}/4+
                \frac58(x+\max(v_0,v_1)+1),\qquad
 U=\max_{r,j}U_{rj}.
 \end{aligned} \tag{SD2}
\]

Here `s E_mu35 A0²<=U_rj`, while `s Gamma35<=U`. To verify these
statements, write the zero-five ternary load as
`1+I_root+I_cell+sum_{a>=3} I_a`. The first three terms have exact raw
square `s+3n_r+(3+2*1[r(j)=r])*n_j`. A depth-`a>=3` test cylinder in
cell `l` has raw complete-survivor mass at most `d_l*3^(-a)`: it already
avoids the pure-five exclusions and all first- and second-level mixed
exclusions represented by `alpha,beta`. Its diagonal and cross terms
with the first three tests have coefficient `c_l`. These terms sum to
at most `max_l(c_l*d_l)/18`. The ordered pairs of distinct deeper tests
are bounded by `max_l(d_l)/18`, since

\[
 \sum_{a\ge3}3^{-a}=\frac1{18},\qquad
 2\sum_{b\ge4}(b-3)3^{-b}=\frac1{18}.
\]

This proves `P_rj`. The same expansion under the raw pure-ternary law
has root mass `v_r/3`, cell mass `w_j/9` and depth caps `3^(-a)`, giving
`V_rj`. The already proved (ZG2), with its global pure-ternary norm bound
`x+max(v_0,v_1)+1`, gives `U_rj`. No consistency between distinct test
prefixes has been assumed. Finite sums are bounded by the displayed
nonnegative infinite sums.

The existing Lean theorem
`ArbitraryRootEventMoment.arbitrary_root_event_moment_le` supplies this
tail estimate directly, and even bounds it by the smaller quantity
`max_l((c_l+1)*d_l)/18`. Use the five surviving cells as root labels,
discount `1/3`, initial caps `d_l/27`, and initial counts
`1[r(l)=r]+1[l=j]`. The actual depth-`a` tests restricted to complete
survivors satisfy its geometric caps by the preceding product-count
bound; empty tests remain at their original depths. For the pure-ternary
law, use initial caps `1/27`. This is direct library reuse inside the
ordinary arithmetic argument, not an additional Lean declaration or a
claim that the actual-family extraction has been formalized end to end.

Take a target `C>=9` and let

\[
 k_l=C-(1+\mathbf1_{r(l)=r}+\mathbf1_{l=j})^2\ge0.
\]

The actual complete old load satisfies `(C-A0²)_+<=k_l` in cell `l`.
The raw weighted sum of maximum cylinder masses over all nonunit old
cofactors is at most

\[
 \begin{aligned}
 W_{rj}(C)={}&
 \max_{a=0,1}\sum_{r(l)=a}k_ln_l+\max_lk_ln_l
       +\frac{\max_lk_ld_l}{18}\\
 &+\frac{\sum_lk_lw_l}{36}
       +\frac{\max_{a=0,1}\sum_{r(l)=a}k_lw_l}{36}
       +\frac{\max_lk_lw_l}{36}
       +\frac{C-1}{72}.
 \end{aligned} \tag{SD3}
\]

The seven terms respectively cover cofactors `3`, `9`, `3^a (a>=3)`,
`5^b`, `3*5^b`, `9*5^b`, and `3^a*5^b (a>=3,b>=1)`. The first two
use the actual cell masses. The third uses the residual availability
`d_l` just proved. For the next three, drop all five-coordinate
exclusions and use the weighted pure-ternary masses. The last drops
both sets of exclusions and uses `max_l k_l=C-1`, together with
`sum_{a>=3,b>=1}3^(-a)*5^(-b)=1/72`. This accounts for every old
cofactor without identifying distinct original labels.

Let `nu7` be the uniform actual pure-seven survivor law, and put
`M=mu35 times nu7`. Its positive-depth cylinder caps `a_e` satisfy
`sum a_e<=1/5` and `sum(2e-1)*a_e<=4/15`. For the full test load `L`,
retain `A0` in each zero/positive-seven cross block. The same square
inequality as in (ZG2) gives

\[
 \mathbb E_M L^2\le
       \frac65\mathbb E_{\mu_{35}}A_0^2+
       \frac7{15}\Gamma_{35}
 \le\frac{(6/5)U_{rj}+(7/15)U}{s}. \tag{SD4}
\]

Let `B` be the actual mixed-seven forbidden union. Conditioning `M`
on its complement gives precisely the uniform complete three-prime
survivor law. Since `L>=A0` pointwise, weighted union bounding and (SD3)
give

\[
 \begin{aligned}
 \mathbb E_M[(L^2-C)\mathbf1_{B^c}]
 &\le\mathbb E_M L^2-C+
           \mathbb E_M[(C-A_0^2)_+\mathbf1_B]\\
 &\le\frac{(6/5)U_{rj}+(7/15)U+W_{rj}(C)/5-Cs}{s}.
 \end{aligned} \tag{SD5}
\]

For each fixed positive seven exponent the original mixed moduli have
distinct old cofactors, so (SD3) applies before summing its cap `a_e`.
The complete survivor set is nonempty by (CM2). Therefore a nonpositive
right side proves `Gamma357<=C` on this same law.

For `C=3849/106`, exact rational arithmetic verifies

\[
 Cs-\frac65U_{rj}-\frac7{15}U-\frac15W_{rj}(C)\ge0 \tag{SD6}
\]

at all `1296*2*5=12960` parameter-vertex/test-choice pairs. This is a
continuous-domain certificate, not finite-height sampling. For a fixed
test choice, expand each maximum in `U_rj,U,W` into its finitely many
branches. Each resulting margin is affine separately in every group
`1-w,alpha,beta,t,z`; the full margin is their pointwise minimum and
hence concave in each group separately. Its value throughout each
simplex or interval is at least the convex combination of its vertex
values. Applying this successively to the five groups proves (SD6)
everywhere. Checking the maxima at each vertex already checks the
worst branch there, so a separate enumeration of all branch products
is unnecessary.

The least vertex margin is zero. One equality point in this relaxation
has

\[
 \begin{gathered}
 1-w=(1/2,0,0,0,0),\quad\alpha=(0,1/4),\quad
 \beta=(0,0,1/4,0,0),\\
 t=(1/72,0,0,0,0),\quad z=3/4,\quad(r,j)=(0,1),\\
 (n_l)=(1/36,1/12,1/36,1/18,1/18),\quad
 s=1/4,\quad U_{rj}=U=163/48.
 \end{gathered}
\]

This is not an assertion that an actual residue family attains (SD1).

If modulus 3 is absent, reuse the same-law bounds
`Gamma35<=215/24,R35<=17/12`; (N9) gives `Gamma357<=5273/258`.
If modulus 3 is present but modulus 9 is absent or ineffective, the
already proved (P11)--(P12) give the stronger input
`Gamma35<=K35<=593/48,R35<=47/24`. Substitution in (N9) gives

\[
 \Gamma_{357}\le\frac{14543}{438}<\frac{3849}{106}.
\]

These include ternary heights below two and preserve the complete actual
uniform law. Missing five- or seven-coordinate classes and smaller
heights are already covered by the cap inequalities. Thus (SD1) holds
for every finite original family with these prime supports.

The existing [cofactor verifier](../docs/reports/erdos7-odd-covering/verify_uniform_gamma_cofactor_coupling.py)
recomputes all signed margins and both fallback bounds under
`signed_two_level_three_prime_parameters` in its
[certificate](../docs/reports/erdos7-odd-covering/uniform_gamma_cofactor_certificate.json).
The earlier certificate fields are retained unchanged. Equations
(SD1)--(SD6) are ordinary mathematical proofs with exact arithmetic;
they have not been checked end to end in Lean.

### A uniform-survivor obstruction and sharpness at two primes

Let P be the twenty odd primes from 3 through 73 and H>=1. Set
Q_H=product_{p in P} p^H. Give every nonunit divisor exactly one forbidden
class, according to its support:

* p^e: residue p^(e-1)-1 modulo p^e;
* 3^i 5^j: CRT residues 2*3^(i-1)-1 and 2*5^(j-1)-1;
* all other mixed divisors: residue 0.

These support cases are disjoint and exhaustive, with no duplicate modulus.
The third class lies in 0 mod p for any prime p dividing that modulus;
0 mod p is already the e=1 pure forbidden class. Thus all higher-support
moduli are present but redundant. No antichain or nonredundancy hypothesis
is required by the uniform-head statement being tested.

#### Geometry for every finite height

Write F_{p,e} and C_{p,e} for the cylinders with residues p^(e-1)-1 and
2*p^(e-1)-1. If e<f, either depth-f residue reduces to -1 modulo p^e.
Neither depth-e residue equals -1 modulo p^e for odd p: their differences
from -1 are p^(e-1) and 2*p^(e-1). At equal depth F and C are distinct.
Hence all 2H cylinders are mutually disjoint. Put

    s_p=sum_{e=1}^H p^(-e), lambda_p=1-s_p,
    S_p=(union_e F_{p,e})^c, C_p=union_e C_{p,e}.

Then C_p is contained in S_p, U_p(C_p)=s_p and U_p(S_p)=lambda_p.
The union of all support-{3,5} mixed classes is exactly C_3 x C_5.
Consequently the complete survivor set is exactly

    R_H=[(S_3 x S_5) minus (C_3 x C_5)] x product_{p>=7} S_p.

Let u=3^(-H), v=5^(-H). Its {3,5} block has ambient mass

    D=lambda_3 lambda_5-s_3 s_5=1-s_3-s_5=(1+2u+v)/4>1/4.

The entire survivor density is D product_{p>=7}lambda_p, strictly above
(1/4) product_{p>=7}(p-2)/(p-1)>0. No exceptional thin set or Dirac law is used.

#### One whole test layout and its exact integral

Take beta=2 at the 5-adic coordinate and beta=1 at every other prime,
modulo the full p^H. CRT chooses a single beta_H modulo Q_H. At every
divisor d, including 1, use its reduction beta_H mod d as the test class.
Define ell_p=1+sum_{e=1}^H 1_{x_p=beta mod p^e}. Exact divisor expansion gives

    L=product_p ell_p.

The cylinders in each ell_p are nested. Therefore ell_p^2 equals
1+sum_e(2e+1)1_{x_p=beta mod p^e}. Define W_p=sum_e(2e+1)p^(-e).
Every such test cylinder lies in S_p: its first digit is different from
0 and from -1. All positive-depth 3-adic test cylinders lie in C_{3,1};
the 5-adic test cylinders avoid C_5 entirely. Thus

    integral_{S_p} ell_p^2=lambda_p+W_p,
    integral_{C_3} ell_3^2=s_3+W_3,
    integral_{C_5} ell_5^2=s_5.

Using the actual set difference, rather than independent {3,5} marginals,
the exact block score is

    g_H=[(lambda_3+W_3)(lambda_5+W_5)-(s_3+W_3)s_5]/D.

The full coherent-layout score under the uniform COMPLETE survivor law is

    G_H=g_H product_{p>=7}(1+W_p/lambda_p).

Therefore Gamma(Unif R_H)>=G_H. No maximality of this particular test
layout is assumed or needed.

#### Strict monotonicity: exact positive numerators

Put D'=1+2u+v. Algebra gives

    g_H=1+2 A_H W_3+2 B_H W_5+4 C_H W_3 W_5,
    A_H=(1+v)/D', B_H=(1+u)/D', C_H=1/D'.

At H+1, u becomes u/3 and v becomes v/5. All denominators are positive.
After putting each difference over D'_H D'_{H+1}, the exact numerators are

    A_{H+1}-A_H: 4u(5-v)/15 >0,
    B_{H+1}-B_H: 2u/3+4v/5+2uv/15 >0,
    C_{H+1}-C_H: 4u/3+4v/5 >0.

Here 0<v<=1/5 because H>=1. Also W_p strictly increases and lambda_p
strictly decreases while staying positive. Hence both g_H and G_H strictly
increase for every H>=1. In particular any exact H=5 lower bound persists
for every H>=5; finite tests are not the basis of this assertion.

#### Limit and sharpness of the uniform two-prime constant

As H tends to infinity, W_3->2, W_5->7/8, and A_H,B_H,C_H->1. Therefore

    g_H -> 1+4+7/4+7 =55/4.

Together with the independently proved universal uniform Gamma35<=55/4,
this proves that 55/4 is the sharp constant over finite families: every
smaller proposed uniform constant is exceeded at a sufficiently large
finite height. This does not claim that a finite family attains equality.

The full limiting witness is

    (55/4) product_{7<=p<=73}(1+(3p-1)/((p-1)(p-2))).

Before the mixed rectangle is deleted the limiting {3,5} witness is
5*(13/6)=65/6. The exact amplification ratio is (55/4)/(65/6)=33/26.

For p=3 there is the sharper geometric explanation:
S_3 is the disjoint union of C_3 and the final singleton -1 mod 3^H,
because 2s_3+3^(-H)=1. Thus the mixed cofactors remove C_5 above nearly
all of the pure-3 survivor set; on C_5 the selected 5-load is exactly 1.

#### Scope of the conclusion

At height 5 the exact arithmetic gives

\[
 g_5=\frac{2581475}{191467},\qquad
 142.3789923<G_5<142.3789924.
\]

The uniform survivor density at this height is approximately
`0.11216643572445546`. At every height it exceeds
`36779876601/330712481792>11/100`. The limiting score is approximately
`145.21869889477725`. The [exact verifier](../docs/reports/erdos7-odd-covering/verify_uniform_survivor_obstruction.py)
and its [fixed certificate](../docs/reports/erdos7-odd-covering/uniform_survivor_obstruction_certificate.json)
recompute the finite sums, pairwise CRT disjointness and individual
`3^5` and `5^5` coordinates by direct enumeration.

Thus the universal strengthening requiring the uniform complete-survivor
law to satisfy `Γ≤138877/1000` is false, already at height 5. Strict
monotonicity makes the same family an obstruction at every `H≥5`.
The construction does not refute the existence of a nonuniform survivor
law with small Gamma, and it does not construct an odd covering system.
The separate star family refutes the nonuniform existential Γ73 target.
The present rectangular-family argument and exact arithmetic are not a Lean proof.


### A nonuniform law for the rectangular obstruction family

For the specified rectangular forbidden family on all odd primes through
73, every common height `H≥5` admits a complete-survivor probability law
with

\[
 \boxed{\Gamma\le
 \frac{64245900555623296761826781321804225}
      {479017695593451697408733725605888}
 <134.121<138.877.} \tag{NR1}
\]

This is an existence statement for this family. It does not restore the
uniform-law bound or establish the same existence statement for all
forbidden-residue assignments.

Let `P` be the odd primes at most 73 and `Q_H=∏_{p∈P}p^H`. On the
`p`-power coordinate, with ambient uniform measure `U_p`, define

\[
 F_{p,e}=\{x:x\equiv p^{e-1}-1\pmod{p^e}\},\qquad
 C_{p,e}=\{x:x\equiv2p^{e-1}-1\pmod{p^e}\},
\]
\[
 S_p=(\mathbb Z/p^H)\setminus\bigcup_{e=1}^H F_{p,e},\qquad
 C_p=\bigcup_{e=1}^H C_{p,e},\qquad
 s_p=\sum_{e=1}^H p^{-e}=\frac{1-p^{-H}}{p-1}.
\]

The actual forbidden assignment uses `F_{p,e}` for pure powers, the CRT
rectangle `C_{3,i}×C_{5,j}` for modulus `3^i5^j`, and residue zero for
every other mixed divisor. At different depths the first nonterminal digit
occurs in different positions; at equal depth the `F` and `C` digits are
distinct. Hence these cylinders are pairwise disjoint and `C_p⊆S_p`, with
`U_p(C_p)=s_p` and `U_p(S_p)=1−s_p`. The other mixed classes are redundant,
since each is contained in an already forbidden pure residue `0 mod p`.
Thus the complete survivor set is exactly

\[
 R_H=\bigl((S_3\times S_5)\setminus(C_3\times C_5)\bigr)
             \times\prod_{7\le p\le73} S_p. \tag{NR2}
\]

We use the rectangular subset
`C_3×(S_5\C_5)×∏_{p≥7}S_p` of this actual survivor set.

**The ternary law.** The first cylinder `C_{3,1}` is the entire root
`1 mod 3`, of ambient mass `1/3`. All remaining `C_{3,e}`, `e≥2`, lie
in root `2 mod 3`; their total relative root width is

\[
 w_H=3\sum_{e=2}^H3^{-e}=\frac{1-3^{1-H}}2,
 \qquad \frac{40}{81}\le w_H<\frac12\quad(H\ge5).
\]

Give the raw restricted measure `U_3|C_3` multiplier `h=1` on root 1
and `k=4/3` on root 2. Its mass is

\[
 x_H=\frac{1+(4/3)w_H}{3}\ge\frac{403}{729}>0.
\]

The general weighted two-root event inequality applies to this finite
positive measure: it needs only the two root masses and the depth-wise
cylinder caps `h·3^{-e}`, `k·3^{-e}`. In particular it does not require
`w_H≥1/2`, a condition used in the separate pure-survivor budget problem.
The root masses here are `1/3` and `(4/3)w_H/3`. The root-labelled
finite-itinerary estimate gives

\[
 \Gamma(\text{raw law})\le x_H+
 \max\{2,\ 17/9,\ (4/3)(w_H+1),\ (4/3)w_H+2/3\}
 \le x_H+2.
\]

A modulus-3 test in the zero-mass root contributes no event; its remaining
weighted tail is at most `(2/3)max(h,k)=8/9`, also below 2. All later
root choices, including nonnested choices, are covered by the event bound.
After normalization, the resulting probability `μ_3` satisfies

\[
 \Gamma(\mu_3)\le1+\frac2{x_H}\le\frac{1861}{403}.
 \tag{NR3}
\]

The finite-event inequality is supplied by the existing general weighted
root theorem; the residue identification and normalization here are the
ordinary mathematical application of that component.

**The quinary law.** Let `μ_5` be uniform on `S_5\C_5`. Its ambient
density is

\[
 1-2s_5=\frac{1+5^{-H}}2>\frac12.
\]

Consequently every cylinder modulo `5^e` has `μ_5`-mass at most
`2·5^{-e}`. For completeness, if a probability `ν` on a new `p`-power
coordinate has every depth-`e` cylinder bounded by `C p^{-e}`, then for
any old law `μ`, complete-layout grouping gives

\[
 \Gamma(\mu\times\nu)
 \le\Gamma(\mu)\left(1+C\sum_{e\ge1}(2e+1)p^{-e}\right).
 \tag{NR4}
\]

To see this, group ordered outside exponents by their maximum. Outside
residues may depend on the old divisor, but every old divisor pair has
outside intersection mass at most `C p^{-e}`. Sum the old indicators and
use Cauchy–Schwarz for their two complete old layouts. The count is `2e+1`;
the zero-exponent block has exactly the old bound. Finite-height sums are
bounded by these nonnegative infinite sums. This is the cylinder-cap
transfer; it assumes no general multiplicativity of actual Gamma.

Since `∑_{e≥1}(2e+1)5^{-e}=7/8`, (NR3)–(NR4) give

\[
 \Gamma(\mu_3\times\mu_5)
 \le\frac{1861}{403}\left(1+2\frac78\right)
 =\frac{20471}{1612}. \tag{NR5}
\]

**The remaining primes and support.** For every `p≥7`, take `μ_p` uniform
on `S_p`. Its ambient density is at least `(p−2)/(p−1)`, so its depth-`e`
cylinder cap is `[(p−1)/(p−2)]p^{-e}`. Iterating (NR4), all normalizers
remain positive and the transfer factor at `p` is

\[
 1+\frac{3p-1}{(p-1)(p-2)}
   =\frac{p^2+1}{(p-1)(p-2)}.
\]

The final law `μ_3×μ_5×∏_{p≥7}μ_p` is supported on (NR2): its ternary
coordinate lies in `C_3`, its quinary coordinate avoids `C_5`, and every
coordinate avoids all original pure forbidden classes. Therefore it also
avoids the redundant mixed zero classes. No conditioning or uniform-law
estimate from a different distribution is used.

The exact remaining-prime product is

\[
 \prod_{\substack{7\le p\le73\\p\text{ prime}}}
 \frac{p^2+1}{(p-1)(p-2)}
 =\frac{34522246402806715078896712155725}
        {3268731173404447066684907556864}.
\]

Multiplying by (NR5) proves (NR1). The exact margin below `138877/1000` is

\[
 \frac{284829994413561827400741536145585347}
      {59877211949181462176091715700736000}>0.
\]

The standalone standard-library verifier
[verify_rectangular_family_nonuniform_law.py](../docs/reports/erdos7-odd-covering/verify_rectangular_family_nonuniform_law.py) recomputes the root-width
endpoints, affine weighted-root bounds, every prime and transfer factor,
and the exact final inequality against
[rectangular_family_nonuniform_certificate.json](../docs/reports/erdos7-odd-covering/rectangular_family_nonuniform_certificate.json). The bounds hold uniformly
for all common heights `H≥5`; the program does not enumerate the full
period. No complete Lean formalization of this family result is claimed.

### Exact tensorization for two fixed depth-two tree shapes

Let `p,q` be distinct odd primes. Consider probability laws on residues
modulo `p²` and `q²`, each supported on four leaves in two depth-one roots.
For either of the following two cases, with arbitrary real nonnegative
probability weights on the four leaves, one has

\[
 \Gamma_{p^2q^2}(\mu\times\nu)
   =\Gamma_{p^2}(\mu)\Gamma_{q^2}(\nu).
 \tag{TT}
\]

The two cases are separate: both root partitions are `2+2`, or both are
`3+1`. Leaves may have zero weight. Residues `0,p,1,p+1` realize `2+2`;
residues `0,p,2p,1` realize `3+1`. The analogous choices work modulo `q²`.
These statements do not cover a product of different shapes, additional
roots, higher powers or arbitrary complete-survivor supports. They supply
no new numerical covering-head bound.

A complete one-coordinate test layout contains divisor one, one chosen
root cylinder and one chosen leaf cylinder. Root and leaf choices are
independent; the leaf need not lie in the selected root. Every cylinder
with zero intersection with the support can be replaced by a supported
cylinder without decreasing the load. Hence the two roots and four leaves
give exactly eight relevant one-coordinate choices. If `x` is a probability
vector, write their squared-load vectors as `s_0,…,s_7`. Then

\[
 \Gamma(x)=\max_{0\le i<8}s_i\cdot x.
\]

For `3+1` these vectors, ordered by root and then leaf, are

\[
 (9,4,4,1),\ (4,9,4,1),\ (4,4,9,1),\ (4,4,4,4),
\]
\[
 (4,1,1,4),\ (1,4,1,4),\ (1,1,4,4),\ (1,1,1,9).
\]

In particular the nonnested constant-load branch `(4,4,4,4)` is retained.
For example `(21,21,21,37)/100` has `Γ=4`, attained by selecting the
three-leaf root and the other root's leaf. Its two nested alternatives have
values `197/50` and `99/25`, both strictly smaller. The verifier derives
the corresponding eight vectors directly for each fixed root partition.

For each `i`, let

\[
 P_i=\{x\ge0:\ \textstyle\sum_jx_j=1,
                \ (s_i-s_k)\cdot x\ge0\text{ for every }k\}.
\]

These compact rational polytopes cover the probability simplex, and
`Γ(x)=s_i·x` on `P_i`. A vertex in this three-dimensional normalization
hyperplane has three linearly independent active inequalities. Enumerating
all triples, solving with exact signed minors, normalizing and checking all
inequalities therefore gives every vertex. Empty and lower-dimensional
regions are handled by the same enumeration; a nonempty compact polytope
has a vertex.

A complete product layout chooses one product cylinder independently for
each exponent pair in `{0,1,2}²`. All nine divisors, including old-only and
mixed cofactors, are present. The choices total

\[
 2\cdot4\cdot2\cdot4\cdot8\cdot4\cdot8\cdot16=262144.
\]

For any such layout, let `M` be its squared-load matrix on the sixteen
supported point pairs. Its second moment under `x×y` is `xᵀMy`. On
`P_i×P_j` the proposed upper-bound margin is

\[
 (s_i\cdot x)(s_j\cdot y)-x^{\mathsf T}My,
\]

which is bilinear. Minimizing a linear function on the first polytope and
then on the second proves that its minimum occurs at a pair of vertices.
Thus it suffices to compare every complete layout at every pair from the
union of all local polytope vertices.

The fixed certificate gives these exact counts:

| Root partition | Vertex counts for the eight local regions | Distinct vertices | Vertex pairs | Integer comparisons |
| --- | --- | ---: | ---: | ---: |
| `2+2` | `8,8,0,0,0,0,8,8` | 15 | 225 | 58,982,400 |
| `3+1` | `10,10,10,4,0,0,0,10` | 18 | 324 | 84,934,656 |

The standalone standard-library plus NumPy verifier recomputes every
polytope vertex using rational arithmetic and checks every displayed
integer comparison. For every vertex pair, the maximum layout moment
numerator equals the product of the two local Gamma numerators. These
checks prove the upper bound in (TT). The reverse inequality follows for
all weights by choosing the product of two maximizing one-coordinate
layouts, whose complete product load factors pointwise.

The integer arithmetic has an explicit overflow bound. A full product load
is between one and nine. After clearing each vertex's denominator, the
maximum integer weight sum is 27 for `2+2` and 40 for `3+1`. Consequently
all moment numerators and local-Gamma products are at most
`81·27²=59049` and `81·40²=129600`, respectively. The verifier checks these
bounds before and after the `int64` comparisons. It uses explicit errors,
so optimized Python retains every check.

The [standalone verifier](../docs/reports/erdos7-odd-covering/verify_two_root_tensorization.py)
and [fixed rational certificate](../docs/reports/erdos7-odd-covering/two_root_tensorization_certificate.json)
are the complete runtime artifacts. The default invocation verifies
both fixed shapes; `--shape 2+2` or `--shape 3+1` selects one. This is an
ordinary mathematical polytope reduction with exact integer verification;
no Lean formalization or general tensorization theorem is claimed.

### Coherent constant potential does not bound actual Gamma

The coherent-center potential is not an upper bound for arbitrary test
layouts, even in one prime coordinate. For the ternary `RestrictedSpine`
of height 4, with side digit 1, spine digit 2 and layer weights `3,5,7,9`,
the recurrence law has 41 supported residues modulo 81. Its per-leaf
weights on the disjoint groups `1 mod 3`, `5 mod 9`, `17 mod 27`, `{53}`
and `{80}` are respectively `3671/174309`, `4628/174309`, `5980/174309`,
`2600/58103` and `2600/58103`; their cardinalities are `27,9,3,1,1`.
Every supported center has coherent score `248995/58103`, and every
other center has score at most that value. The nonnested layout with
residues `(2 mod 3, 8 mod 9, 17 mod 27, 53 mod 81)` instead has score
`249255/58103`, exceeding it by `260/58103`. Exact enumeration of all
`2*5*14*41=5740` supported-cylinder layouts proves that this latter score
is the actual `Gamma`. Unsupported cylinders have zero mass, so replacing
them by supported cylinders cannot decrease the load; the enumeration
therefore also determines the unrestricted maximum. The
[existing exact verifier](../docs/reports/erdos7-odd-covering/verify_star_survivor_obstruction.py)
checks all 81 coherent centers and all 5740 layouts against its
[certificate](../docs/reports/erdos7-odd-covering/star_survivor_obstruction_certificate.json).
This refutes only the bridge from a coherent-potential bound to an
actual-`Gamma` upper bound. It does not refute product tensorization or
the existing star-family lower-bound argument, which uses a law of test
centers. The finite computation is an exact certificate, not a Lean
formalization.

### The boundary of scalar fibre reweighting

The conditional-cap criterion alone does not improve the optimized T6
recurrence. Within the scalar certificate described below, arbitrary
reweighting of old fibres and the exact bounded second-moment inequality
reduce to the BBMST clipping rule and its optimized T6 value. This is a
limitation of that certificate, not an impossibility theorem for actual
covering systems or for reweighting that retains joint-layout information.

Moreover, for every prime p>=13 there is an actual distinct-modulus
family and two old survivor laws with identical Gamma, R, exact density
cap 16/15, and first two forbidden-fibre moments, but different feasibility
for the same pair of old-marginal and conditional-density caps. Thus those
scalars do not determine the missing capacity information even for actual
congruence families.

#### 1. The scalar certificate and its optimal weight

Let mu be a probability on a finite old survivor carrier X, let U be
uniform on Y=Z/p^H, and let B_x be the actual new forbidden union in row x.
Write alpha(x)=U(B_x), s(x)=1-alpha(x), and Gamma(mu)<=G. As in T1, set
a=sum_{e=1}^H (2e+1)p^{-e}, or use its infinite-height upper bound.

Choose a nonnegative old-row multiplier h, zero on rows where s=0.
Give each surviving point of row x raw density h(x)/s(x) relative to
mu(x)U(y), and normalize by Z=E_mu h>0. The old marginal of the resulting
complete-survivor law is h mu/Z. For a positive raw measure rho extend
Gamma homogeneously: Gamma(rho)=max_L integral L^2 d rho.

The weighted joint-layout transfer W1 gives

    Gamma(new law) <= [Gamma(h mu)+a Gamma((h/s)mu)]/Z.       (1)

The ratio h/s is defined to be zero on s=0. This follows by bounding each
positive outside-prefix mass by p^{-e}/s(x), then retaining the weighted
old-layout moment until the final step. It includes every old cofactor.
No fibre with s=0 is assigned positive mass.

Consider the scalar certificate that replaces the two weighted moments by

    h<=1, h/s<=C, C>=1
    ==> Gamma(new law) <= G(1+aC)/E h.                     (2)

Here C bounds the raw joint-density multiplier h/s, not the normalized
conditional multiplier 1/s. Clipping can keep a row with s<1/C by
reducing its old mass. A law required to satisfy the conditional cap
must instead remove that row, as in the separate capacity criterion.

At fixed C its pointwise largest feasible h is

    h_C(x)=min(1,C s(x)).                                 (3)

Every competing weight satisfies h<=h_C, so (3) maximizes the denominator
in (2) while preserving its numerator. It therefore gives the best value
certified by (2) at fixed caps. This statement concerns the scalar bound:
another h can have better actual weighted moments in (1).

Write C=1/(1-delta), 0<=delta<1. Then

    E h_C = 1 - E b_delta(alpha),
    b_delta(t)=(t-delta)_+/(1-delta).                      (4)

The raw surviving-point density is 1/(1-alpha) when alpha<=delta,
and 1/(1-delta) otherwise. This is exactly the complete-survivor part
of the BBMST clipped law, followed by normalization. Unlike the full
BBMST law, this restricted law carries no forbidden points.

#### 2. Sharp bounded second-moment loss and optimized T6

Suppose 0<V<1 and E alpha^2<=V, with 0<=alpha<=1. The exact worst value
of E b_delta(alpha) over all such scalar probability distributions is

    q(V,delta) = V/[4delta(1-delta)]
                 if 0<delta<=1/2 and V<=4delta^2;
               = (sqrt(V)-delta)/(1-delta)
                 if 0<=delta<=1/2 and V>=4delta^2;
               = V
                 if 1/2<=delta<1.                        (5)

The formulas agree at their common boundaries, including delta=0.
For delta<=1/2, view b_delta(t) as a function of u=t^2. Its least
concave majorant is the line from (0,0) tangent at u=4delta^2, followed
by (sqrt(u)-delta)/(1-delta). Jensen's inequality gives (5).
For V<=4delta^2 equality is attained by alpha in {0,2delta}, with mass
V/(4delta^2) at 2delta. For V>=4delta^2 equality is attained by the
constant alpha=sqrt(V). For delta>=1/2, b_delta(t)<=t^2 on [0,1], and
the distribution with mass V at alpha=1 and 1-V at zero gives equality.
These extremizers certify the scalar moment problem; no realizability
claim for every extremizer as a congruence family is made.

Consequently the best guarantee from (2) and the bounded second moment is

    inf_{0<=delta<1} G[1+a/(1-delta)]/[1-q(V,delta)].       (6)

For 0<=delta<=sqrt(V)/2, the expression is

    G(1-delta+a)/(1-sqrt(V)),

which decreases as delta increases. For delta>=1/2 its denominator is
1-V and its numerator increases. Hence the optimum is attained in
[sqrt(V)/2,1/2], exactly the region where (5) is the ordinary quadratic
BBMST loss. Thus (6) equals

    min_{0<delta<=1/2}
      G[1+a/(1-delta)]/[1-V/(4delta(1-delta))],             (7)

where only positive denominators are admitted. No smaller threshold
outside the interval can improve it: there the quadratic loss only
overestimates (5), whose best boundary value already occurs inside.

For a>0 the unique minimizing threshold solves

    a delta^2 + (V/2)delta - (1+a)V/4 = 0,

and is

    delta_*=[sqrt(V^2+4a(1+a)V)-V]/(4a).                  (8)

Substitution into the quadratic shows sqrt(V)/2<=delta_*<=1/2.
If a=0 the endpoint delta=1/2 attains the minimum. Taking
V=G/(p-1)^2 and a=(3p-1)/(p-1)^2 recovers optimized T6 exactly.

This rules out a strict improvement merely from using the sharp bounded
second-moment problem instead of t^2/(4delta), or from replacing BBMST
clipping by another h certified only through the two supremum caps in (2).
It does not rule out improvements from the known lower bound L^2>=1,
the actual prefix occupancies, a first-moment constraint, or the weighted
moments in (1). Those additional facts lie outside certificate (2).

#### 3. Hard fibre trimming is dominated

Keeping only rows alpha<=delta and making their conditional law uniform
gives conditional density cap 1/(1-delta). Using only Markov's inequality
from E alpha^2<=V certifies retained mass at least 1-V/delta^2, and hence

    G[1+a/(1-delta)]/[1-V/delta^2].                        (9)

For delta<=1/2, T6 at the same threshold has the same numerator and a
larger denominator, since delta^2<4delta(1-delta). For delta>=1/2,
T6 at threshold 1/2 improves both numerator and denominator: its loss
is V, at most V/delta^2. Thus every positive-denominator hard-trimming
certificate (9) is dominated by a T6 certificate. The result is unchanged
if V came from multiplying a reference-law moment bound by an RN cap.

#### 4. Concrete obstruction to scalar capacity closure

Fix any prime p>=13. The old period is 15 and its only forbidden class
is 0 mod 3. Identify its survivor carrier with {1,2} x Z/5 by CRT.
The two old laws below are uniform on {1,2}; only their 5-coordinate
weights differ.
The 5-coordinate is an unused padded old coordinate: the old actual
modulus lcm is 3. This is an arbitrary finite distinct-modulus family,
not an assignment of a forbidden class to every nonunit divisor of 15.

Let T=p^2+p+1, epsilon=1/(120pT), and define

    v=(1,-T,pT,-p^3),
    nu_+(0)=nu_-(0)=16/75,
    nu_+(j)=59/300+epsilon v_j,
    nu_-(j)=59/300-epsilon v_j,  j=1,2,3,4.               (10)

The identities sum v_j=0 and |epsilon v_j|<=1/120 show that both are
strictly positive probability laws; every j>0 weight is at most
59/300+1/120=41/200<16/75. Hence they have the same maximum weight
16/75, attained at zero.

For the old period 15, the complete layout has the four divisors
1,3,5,15. Every cylinder and every intersection is bounded by the
appropriate product of the maximum ternary and quinary masses. These
individual maxima are attained simultaneously by taking all test
classes through one point of maximum mass. Therefore, for both laws,

    Gamma = (1+3/2)(1+3*(16/75)) = 41/10,
    R = 1/2+16/75+(1/2)(16/75) = 41/50,
    max dmu/dU_old_survivors = 5*(16/75) = 16/15.          (11)

Adjoin a p-coordinate of height four. Forbid 0 mod p, and for each
j=1,2,3,4 forbid the CRT class

    x_5=j mod 5,  y=1 mod p^j,

whose modulus is 5p^j. These moduli and the old modulus 3 are distinct.
The mixed classes are disjoint from the pure p exclusion because their
p-residue is one. Within each old row their forbidden density is exactly

    alpha(0)=1/p,
    alpha(j)=1/p+p^{-j}, j=1,2,3,4.                       (12)

There are no empty fibres; alpha<=2/p<1. The construction neither
assumes nested test layouts nor introduces multiple classes per modulus.

The four-vector in (10) obeys

    sum_j v_j p^{-kj}=0, k=0,1,2.                        (13)

For k=1,2, multiply by p^{4k}; the resulting polynomials vanish by
direct expansion. Consequently both laws have the same E alpha and
E alpha^2 as well as all three scalar invariants in (11). Their common
moments are

    E alpha = 1/p+(59/300)sum_{j=1}^4 p^{-j},
    E alpha^2 = 1/p^2+(59/150p)sum_{j=1}^4 p^{-j}
                       +(59/300)sum_{j=1}^4 p^{-2j}.     (14)

Now require conditional density cap C=2p/(2p-3) at every depth and
old-marginal reweight cap D=300/241. Since 1-1/C=3/(2p), the good set
{s>=1/C} consists of exactly the rows with x_5!=1. Its two masses are

    mu_+(good)=241/300-epsilon < 1/D,
    mu_-(good)=241/300+epsilon > 1/D.                     (15)

The corresponding raw weighted joint-layout moments also differ:

    Gamma(1_good mu_+) = 433/120-(5/2)epsilon,
    Gamma(1_good mu_-) = 433/120+(5/2)epsilon.              (16)

Indeed the maximum quinary point weight remains 16/75, so the raw
product moment is (5/2)[mu(good)+3*(16/75)]. This is a concrete instance
of weighted information required in (1) that the listed scalars omit.

The exact fibre-cap criterion therefore makes the requested law
impossible for mu_+ and feasible for mu_-. In the feasible case restrict
mu_- to good rows, normalize, then use the uniform conditional survivor
law; its old density factor is 1/mu_-(good)<D. In the impossible case
the singleton caps force support inside good, whose available old mass
under the cap D is less than one.

This is an actual-family distinction with identical Gamma, R, RN cap,
and first two forbidden-fibre moments. It does not preclude a universal
upper recurrence using worst-case values of those scalars. It proves
that they cannot determine exact reweighting feasibility or reconstruct
the weighted joint-layout profiles discarded in (2). No assertion is
made that the two laws are the specific NC1 adaptive policy; they share
its stated density bound, showing that this bound alone is insufficient.

#### 5. Consequence at the current four-prime seed

At G=4939031/47730 and p=13 put V=G/144 and a=19/72. Every admissible
T6 value exceeds 256. After multiplying a proposed comparison with 256
by its positive denominator and by 4delta, the excess numerator is

    4(256-G)delta^2 + 4[(G-256)+aG]delta + 256V.

Its global quadratic minimum is strictly positive, verified exactly in
the accompanying certificate. Thus even the optimal scalar-fibre
certificate (6) produces a bound greater than 16^2 at the first new
prime. At the next prime 17 its implied second-moment bound is greater
than one, so this certificate gives no positive universal retained mass.
This failure concerns the supplied seed bound and this proof language,
not the actual optimal measure or the Erdos #7 assertion.

`verify_fibre_scalar_boundary.py`, with `fibre_scalar_boundary_certificate.json`, checks exact extremizing distributions for (5),
the quadratic comparison at p=13, identities (10)-(16) for the requested
primes 13 through 61, and the complete actual p=13 residue assignment.
The continuous arguments and all-prime identities above carry the
universal statements; finite checks are boundary verification, not proofs
by enumeration over a bounded collection of families.

The reusable starting points are the repository's weighted rectangle
transfer W1 and the finite conditional-cap criterion. Public BBMST
1811.03547, section 2, Lemmas 2.1-2.2 and 1901.11465 give the clipping
kernel and its distortion bounds, but no weighted-layout correlation
bound closing (1). Koperberg 2202.02092, Theorem 1, supplies the different
global marginal Hall criterion. No new Lean declaration or full Lean
formalization is asserted here.

### Random tail extensions give pointwise layout certificates

For the explicit complete height-four congruence family specified below,
every probability mu on its actual survivor set satisfies

    Gamma(mu) >= C = 121.54782913540919... .

Here Gamma is the maximum second moment of one complete divisor layout.
The fixed certificate gives C as an exact rational number and verifies a
pointwise lower bound at all 791 coarse survivor residues. The number is
below 138877/1000. It supplies neither an upper bound on Gamma nor a proof
of the Gamma-73 assertion or its negation. The construction below is a
reusable evaluator for finite distributions of layouts; no optimality of
the supplied distribution is required.

#### A random extension of an arbitrary complete layout

Let P be a finite set of distinct primes, choose caps c_p>=1 and heights
H_p>=c_p, and put

    Q_c = product_p p^c_p,       Q_H = product_p p^H_p.

A coarse layout assigns b_d modulo d to EVERY d dividing Q_c, including
one. No compatibility between b_d and b_e is assumed. For D dividing Q_H,
write d=clip(D)=gcd(D,Q_c). Independently for each prime choose a uniform
T_p modulo p^(H_p-c_p). Define a residue for D in its p-coordinate by

    b_d mod p^a                         if a=v_p(D)<=c_p,
    (b_d mod p^c_p)+p^c_p T_p mod p^a  if a>c_p.

CRT gives a unique residue b_D(T) modulo D. Thus each value of T gives
one genuine complete fine layout. It restricts to b on the coarse
divisors. There is no separate random choice for each test modulus or
coarse root: one shared T_p suffices.

For x modulo Q_H let x_0 be its reduction modulo Q_c, and set

    I_d(x_0) = 1{x_0=b_d mod d},
    L_b(x_0) = sum_{d|Q_c} I_d(x_0).

Write L_p=H_p-c_p and

    S_p = sum_{t=0}^{L_p} p^(-t),
    V_p = sum_{t=0}^{L_p} (2t+1)p^(-t).

For coarse divisors d,e define W_de as the product over p of the factor

    1    if neither v_p(d) nor v_p(e) is c_p;
    S_p  if exactly one is c_p;
    V_p  if both are c_p.

Then the exact random-extension identity is

    E_T [L_{b(T)}(x)^2]
       = sum_{d,e|Q_c} W_de I_d(x_0) I_e(x_0).             (1)

To prove it, expand the square over ordered pairs of fine divisors D,E.
If either coarse indicator is zero, the corresponding product is zero
for every T. If both are one, every positive extra p-height t imposes

    T_p = floor(x_p/p^c_p) mod p^t.

The target is the same for both divisors, even though the original coarse
layout was arbitrary. The two conditions have simultaneous probability
p^(-max(t,u)). If only one fine divisor has positive extra height, the
same formula applies with the other height zero. Across primes these
probabilities multiply. Finally, the map from a fine divisor to its
coarse divisor and allowed extra exponents is a bijection. Summing all
extra exponents gives S_p in the one-capped case, and

    sum_{t,u=0}^{L_p} p^(-max(t,u))
       = sum_{t=0}^{L_p} (2t+1)p^(-t) = V_p

in the two-capped case. This proves (1) and accounts for all fine
divisors, all ordered cross terms, and the divisor-one term.

For comparison, if the coarse layout is coherent, its top p-cylinder
coefficient becomes

    2c_p S_p+V_p
      = sum_{e=c_p}^{H_p} (2e+1)p^{-(e-c_p)}.

This recovers direct averaging of a coherent center's finer digits.
Also V_p>=S_p^2: these are the second and first moments of the same
random nested-prefix load. Neither fact assumes that arbitrary layout
suprema tensorize.

#### Exact center probabilities on a pure survivor tree

For an outside prime p>=3, forbid exactly one class at each depth,

    a_(p^e) = (p^(e-1)-1)/(p-1),        1<=e<=H.

Its p-adic digits are e-1 copies of 1 followed by a 0. The forbidden
classes are pairwise disjoint. The surviving tree has at every critical
node one dead child (digit 0), p-2 complete children, and one continuing
critical child (digit 1). Let S_p be the set of surviving leaves.

A coherent center b has load

    ell_b(x) = 1+sum_{e=1}^H 1{x=b mod p^e},

and hence symmetric kernel

    K_p(x,b)=ell_b(x)^2
       =1+sum_{e=1}^H (2e+1)1{x=b mod p^e}.               (2)

The following finite construction gives a probability nu_p supported on
S_p whose potential sum_b nu_p(b)K_p(x,b) is exactly g_p for every x in
S_p and at most g_p on all leaves. It does not assert that g_p is the
minimum of the full, potentially incoherent layout objective.

Let F_e,C_e be the equal-potential costs of complete and critical
subtrees entered at depth e, including that depth's coefficient 2e+1.
Initialize F_H=C_H=2H+1, then for e=H-1,...,1 use

    F_e = (2e+1)+F_(e+1)/p,
    C_e = (2e+1)+[(p-2)/F_(e+1)+1/C_(e+1)]^(-1).        (3)

Finally set

    g_p = 1+[(p-2)/F_1+1/C_1]^(-1).                     (4)

All denominators are positive. The probability construction is explicit:
in a complete node distribute mass equally among its p children; in a
critical node whose live child costs are r_j, give child j the fraction

    alpha_j = (1/r_j)/(sum_k 1/r_k).

There are p-2 children of cost F and one of cost C. Thus the fractions
sum to one and alpha_j r_j is the same number for every live child.
Inductively the potential within each live subtree is constant; adding
the common prefix coefficient proves (3). The root has common
coefficient one and proves (4). A point in a dead branch receives no
further contribution, so its potential is no larger. This proves the
claimed equality on S_p and inequality off it.

The same calculation is the elementary parallel-resistance identity

    min_{alpha_j>=0, sum alpha_j=1} sum_j r_j alpha_j^2
       = (sum_j 1/r_j)^(-1).

Equality holds at the displayed fractions, and weighted Cauchy--Schwarz
proves the lower inequality. Symmetry of (2) consequently shows that
g_p is the exact value of the pure COHERENT-center game: use nu_p as a
distribution of centers for its lower bound, and as the point law for its
upper bound. The present certificate only needs its pointwise lower half.

#### Combining the core and outside potentials

Let R_c be any coarse survivor set. Choose a finite probability
rho=(rho_j) on coarse complete layouts b^(j), and form

    Phi(x_0)=sum_j rho_j sum_{d,e|Q_c}
                    W_de I_d^(j)(x_0) I_e^(j)(x_0).

Suppose Phi(x_0)>=m for every x_0 in R_c. Sample j and the shared tails
T_p, and independently sample each outside center from nu_p. For a full
divisor D=D_core D_out, take the CRT join of its extended core residue
and the outside center residues. This again assigns one residue to every
full divisor. For each realization its load factors exactly as

    L_full(x)=L_core(x_core) product_{p outside} ell_(b_p)(x_p),

because the complete divisor index is the Cartesian product of its core
and outside divisor indices. Squaring and averaging this particular
random construction, using (1)--(4), gives at every point with
x_0 in R_c and x_p in S_p

    E_layout L_full(x)^2 = Phi(x_0) product_{p outside} g_p
                         >= m product_{p outside} g_p.    (5)

The actual full survivor set may be a proper subset of these points;
additional forbidden classes do not invalidate (5). For ANY probability
mu on that actual survivor set, interchange the two finite averages and
bound their layout average by the maximum over complete layouts:

    Gamma(mu) >= E_layout E_mu L_full^2
               >= m product_{p outside} g_p.              (6)

There is no independence assumption on mu. Independence is used only
for the explicitly constructed random layout, whose distribution is
under our control.

#### The fixed rational certificate

The instance uses core caps (3,3),(5,2),(7,1), so Q_c=4725, and common
full height H=4 at all 20 odd primes through 73. The JSON specifies all
23 nonunit coarse forbidden residues. Direct enumeration leaves exactly
791 coarse residues. All outside primes are at least 11 and use the
pure classes in (2)'s construction.

For definiteness this extends to a complete nonempty forbidden family.
Choose w by CRT with w=3 modulo 4725 and w=-1 modulo the product of the
outside fourth powers. Keep the coarse assignments and outside pure
assignments, and for every other nonunit divisor d of the full modulus
forbid (w+1) mod d. The point w survives: it survives the coarse and pure
assignments, while equality with the last residue would imply d divides
1. The verifier constructs and checks such a witness. In particular the
lower bound is about actual probability laws on a nonempty survivor set.

There are 738 listed coarse layouts with positive integer numerators
summing to 10^10. The coherent all-zero layout has numerator 363; it
completes the listed rational probability. All 24 coarse divisors,
including one, appear in every row. The shared-tail random domain has
cardinality 25725. The matrix W has common denominator 25725, and the
verifier reconstructs it in two ways: the three local formulas and direct
summation over all 125^2 ordered fine-core divisor pairs.

`random_tail_layout_certificate.json` contains every coarse potential with common denominator
10^10 times 25725. Exact evaluation gives

    m = 413450618877603/21437500000000
      = 19.28632624501938...,

with the minimum attained at coarse residue 4134. Equations (3)--(4) give

    product_{outside p} g_p = 6.302280050188326... .

Multiplying by m gives

    C = 121.54782913540919... < 138.877.

The full fraction, all 791 potential numerators, every outside recurrence
value and child probability, and the positive comparison margin
138877/1000-C are stored and recomputed in the fixed certificate.

verify_random_tail_layout_certificate.py uses only the Python standard
library. It accepts an optional certificate path so that other coarse
families and layout distributions can use the same evaluator. It reads
no NPZ arrays, saved solver rows, numerical dual values, repository files,
or external libraries. Normal, optimized (-O), and isolated (-I) runs all
exit zero. The layout correspondence and tree induction above are ordinary
mathematical proofs; no Lean kernel certification is claimed.

The existing H73 lower bound exceeding 162.1563 concerns the separate
cylinder-maxima quantity kappa. Since Gamma<=kappa, that result does not
supply or dominate a Gamma lower bound. The existing uniform-survivor
score above 142.3789923 concerns a different family and only its uniform
law. It does not dominate the all-supported-laws conclusion (6). No
stronger same-family Gamma lower bound is used or asserted here.

### Canonical conflict resampling and the exact Shearer query ratio

Let Omega be a finite product probability with strictly positive coordinate
masses. Each bad event B_i fixes one assignment on a set I_i of coordinates.
Join distinct i,j precisely when their required assignments disagree on
I_i intersect I_j. Write V for the bad-event index set, p_i=Omega(B_i), and

    Z_U = sum_{J independent in U} (-1)^|J| product_{j in J} p_j.

The graph used in this polynomial has no loops; the algorithmic causality
neighborhood of a bad event includes itself. Assume Z_U>0 for every U⊆V.
Start from Omega, fix any history-dependent flaw-selection rule, and
resample all coordinates of the selected true bad event independently.
The rule is fixed throughout the conclusions below. Its terminal law is nu.

For every canonical query E, let N(E) be the original bad events whose
assignments conflict with E. Then

    nu(E) <= Omega(E) Z_(V minus N(E)) / Z_V.                 (1)

This is an ordinary mathematical consequence of the public theorem cited
below, with the extension verified here. No Lean kernel certification is
claimed, and (1) is a terminal-law bound, not an asserted exact hit bound.

#### Structural hypotheses

Nonconflicting i,j cannot newly cause one another: while B_i holds, their
shared coordinates already have B_j's prescribed values; coordinates of
B_j outside I_i remain unchanged. Thus the conflict graph with self
neighborhoods is an undirected causality graph.

For the full-coordinate resampling kernel rho_i, the charge is exactly

    max_w [sum_(s in B_i) Omega(s) rho_i(s,w)] / Omega(w)
      = Omega(B_i)=p_i.                                    (2)

Indeed, only s matching w outside I_i contribute, and the factors on I_i
separate. The initial distribution equals the reference distribution, so
lambda_init=1.

For nonconflicting events with coordinate sets I,J, suppose
s --i--> t --j--> w is a valid trajectory. Define t' to equal s outside J,
w on J minus I, and the common required assignment on I intersect J.
Then s --j--> t' --i--> w is valid. Both products of transition
probabilities coincide coordinate by coordinate: on I intersect J they
are the mass of the common required value times the mass of w's value;
on I minus J and J minus I they are the mass of w's value. The swap is
injective since s,w recover t: t equals w on I minus J, the common
required assignment on I intersect J, and s outside I. This verifies
Iliopoulos Definition 2.1. The same proof holds after adjoining any
canonical event on an additional set of product coordinates.

#### Rare-query proof of (1)

[Iliopoulos](../Library/Arith/iliopoulos2017commutative.md), arXiv:1704.02796v6, Theorem 3.2(1) and Remark 3.1, gives

    E[number of addresses of flaw i] <= q_{ {i} } / q_empty

under Shearer's condition. Here
q_S=sum_(J independent, S⊆J) (-1)^(|J|-|S|) product_(j in J) p_j.
Strict positivity of every Z_U implies q_empty=Z_V>0 and
q_S=(product_(i in S)p_i) Z_(V minus N[S])>0 for independent S;
nonindependent S have q_S=0. The theorem therefore applies and implies
finite expected total addresses, hence almost-sure original termination.

Adjoin an independent Bernoulli(epsilon) coordinate and the query flaw
E_epsilon=E intersect {coin=1}, resampling its coordinates and the coin.
Its charge is q=epsilon Omega(E), and its old neighbors are exactly N(E).
For U⊆V, the induced polynomial including the new vertex is

    Z_U - q Z_(U minus N(E)).

All old induced polynomials are positive; finitely many inequalities
therefore remain positive for every sufficiently small epsilon>0.
The extended system satisfies the structural hypotheses just verified.

Use a legal extended rule that first follows the original rule, ignoring
the coin, as long as an original flaw remains. At its first original
termination, address E_epsilon if present, and subsequently use any legal
rule. Before that first termination no action touches the coin. Thus the
expected total number of query addresses is at least epsilon nu(E).
Applying the quoted resampling bound to the extended query vertex gives

    epsilon nu(E)
      <= q Z_(V minus N(E)) / [Z_V-q Z_(V minus N(E))].

Divide by epsilon and let epsilon tend to zero. This proves (1) for the
same original terminal law, independent of the choice of query E.

#### One univariate ray checks every induced subgraph

Set Z_U(t)=sum_(J independent in U)(-t)^|J| product_(j in J)p_j.
If Z_V(t) has no zero on (0,1], then Z_U(1)>0 for every U⊆V.

Public source: [Scott and Sokal](../Library/Arith/scottsokal2003repulsive.md), arXiv:cond-mat/0309352v2, Theorem 2.10(a)
⇔ (b′), hard-core self-repulsion. Condition (a) asks for a positive path
from 0 to -p in the negative orthant; the root-free ray supplies it since
Z_V(0)=1. Condition (b′) is exactly positivity for every induced U.

An elementary finite-polynomial verification is also available. Otherwise
let t* in (0,1] be the earliest zero among all induced polynomials. Every
Z_U(t*) is nonnegative. If Z_U(t*)=0 and v is outside U, deletion gives

    Z_(U union {v})(t*)
      = Z_U(t*) - t* p_v Z_(U minus N(v))(t*) <= 0.

Its nonnegativity forces equality. Adding vertices propagates the zero
to V, contradicting the assumed full-ray condition. Positivity merely at
t=1 is not sufficient; the entire interval condition is essential.

#### Congruence and complete-layout specialization

Encode residues modulo Q=product p^H_p by independent uniform p-adic
digits. A residue class modulo d|Q is a canonical event of probability
1/d. Apply the foregoing construction to the actual forbidden classes.
Every nonempty intersection of test classes C_d(b),C_e(b) from ONE fixed
complete layout b is canonical, with probability 1/lcm(d,e). Thus

    Gamma_Q(nu)
      <= max_b sum_(d,e|Q, C_d(b) intersect C_e(b) nonempty)
           Z_(V minus N(C_d(b) intersect C_e(b)))
           / [lcm(d,e) Z_V].                               (3)

The same nu is used for all pairs and all layouts. In (3), b assigns one
residue for every divisor, including one; do not maximize separate
summands. For a particular forbidden family, strict Shearer feasibility and a useful
bound on (3) are separate requirements. The star calculation below refutes
universal strict feasibility at the uniform-product charges `1/d`. No
unrestricted numerical Gamma_73 bound follows from these conditional estimates.

Before building the graph, remove any bad class contained in another bad
class; the avoided union and survivor set are unchanged. With one class
per distinct modulus, if d divides e then compatible assignments would
imply B_e⊆B_d. Hence every independent set of the reduced conflict graph
has moduli forming a divisor antichain. This connects its independence
polynomial to the divisor poset. It supplies no global signed-polynomial
bound by itself. Z_U uses products 1/d and is not the actual avoidance
probability computed using CRT intersection probabilities 1/lcm.

#### The star family also defeats a universal conflict-Shearer head criterion

Use precisely the pure+star classes from the complete star-family construction above after removing redundant
mixed-zero classes. Let p run over the 20 odd primes through 73 and write

    a_p=sum_(e=1)^H_p p^(-e),
    B(z)=product_(p>=5) (1-z a_p).

For the canonical assignment-conflict graph, the signed independent-set
polynomial with activity z/d at modulus d is exactly

    Z(z)=(1-z a_3)B(z)
         +sum_(i=1)^H_3 [product_(p>=5)(1-z a_p(1+3^(-i)))-B(z)].  (1)

Indeed, independent sets containing no star vertex choose at most one
pure vertex for each prime, giving the first term. Star vertices in an
independent set must all use the same ternary C_(3,i), since different
such cylinders are disjoint. Once i is fixed, at each p>=5 one may choose
a pure p-vertex, a star vertex at p, or neither, but not both; each of the
two vertex groups is internally a clique. Their summed activities are
z a_p and z3^(-i)a_p. Choices at different p are compatible. A star also
conflicts with every pure ternary vertex. The product in the bracket
therefore counts precisely these choices with pure ternary excluded;
subtracting B(z) removes the no-star case. Different i correspond to
disjoint nonempty-star choices, proving (1).

At H_3=31 and H_p=8 for p>=5, exact rational evaluation of (1) gives

    -7/1000 < Z(1) < -69/10000,
    Z(1)=-0.006937138118224894... .

Since Z(0)=1, its real probability ray has a zero in (0,1). In particular
this actual, nonempty star survivor family is outside strict Shearer for
the conflict graph. The conditional commutative-resampling query theorem
remains valid, but its hypothesis cannot be asserted for all smooth
heads. Adding the redundant mixed-zero vertices cannot restore Shearer,
because the displayed failing graph remains an induced subgraph.

[verify_star_conflict_polynomial.py](../docs/reports/erdos7-odd-covering/verify_star_conflict_polynomial.py) uses exact fractions for the numerical
interval and independently compares (1) with all independent subsets of
the directly reconstructed 14-vertex CRT conflict graph at three rational
arguments for the height-two {3,5,7} case. This is an ordinary mathematical
identity and exact arithmetic check, not a Lean kernel result or a new
resolution of the odd covering problem.

#### Exact public source locators

- Fotis Iliopoulos, “Commutative Algorithms Approximate the
  LLL-distribution”, arXiv:1704.02796v6 (2019-06-08; first version 2017).
  Section 2.2 defines causality and charges; Definition 2.1 gives the
  probability-preserving injective swap; Theorem 3.2(1) and Remark 3.1
  give the Shearer resampling-count bound used above.
  https://arxiv.org/html/1704.02796v6
- Alexander D. Scott and Alan D. Sokal, “The repulsive lattice gas, the
  independent-set polynomial, and the Lovász local lemma”,
  arXiv:cond-mat/0309352v2 (2004-09-16; first version 2003),
  Theorem 2.10(a), (b′), and (f).
  https://arxiv.org/html/cond-mat/0309352v2
- [David G. Harris](../Library/Arith/harris2016mosertardos.md), “New bounds for the Moser–Tardos distribution”,
  arXiv:1610.09653v7 (2019-10-10; first version 2016), Proposition 3.4.
  Its improved disjoint-union bound uses the ordinary shared-variable
  graph defined in Section 1.1. Propositions 2.7 and 3.3 retain that graph.
  It is not a cited justification for replacing it by the conflict graph.
  https://arxiv.org/html/1610.09653v7

## Falsifier

The [exact bridge program](../docs/reports/erdos7-odd-covering/bridge_checks.py)
retains two counterexamples to proposed proof steps, not to the conjecture.
Pairs below are `(residue, modulus)`.

1. Pure classes `(0,3),(0,5),(0,7),(0,11)` and mixed classes
   `(1,33),(46,55),(36,77),(136,165),(148,231),(281,385),(106,1155)`
   realize all seven nonempty old cofactors at the actual prefix `1 mod 105`.
   The old prefix has mass `1/48`; auxiliary height `(1,1,1)` has mass `4/105`.
   The quadratic count is `6`, while the aligned beta-load is `70/11 > 6`.
   Seven disjoint terminal hits give bad probability `7/10 > 2/3` and charge
   `11/20 > 1/2`. Every mixed class has an exclusive coverage witness;
   residue `106` makes cubic old cofactor `105` indispensable. Thus the
   quadratic substitution fails when the source's sparsity hypothesis is dropped.
2. History `(1,3),(1,5),(1,7),(2,15)`, current pure class `(10,11)`, and mixed
   classes `(0,33),(45,55),(35,77),(135,165),(147,231),(280,385),(105,1155)`
   leave 48 pure head survivors but 42 complete head survivors modulo 105.
   The source's normalized physical law `μ` retains the earlier mixed event
   at `δ5=0`; it differs from uniform conditioning `ν` on all 42 survivors.
   Conditioning raises the next expected charge from `11/960` to `11/840`
   and gives `ν(r5=0 | r3=2)=1/3 > 4/15`, violating the old cap. The conditioned
   quadratic expectation `1/84` is also below the actual charge `11/840`.
   This family leaves 364 residues uncovered modulo 1155, including `3`.
3. The [H73 verifier](../docs/reports/erdos7-odd-covering/verify_h73.py) and
   [rational certificate](../docs/reports/erdos7-odd-covering/h73_dual.json)
   refute the separate-cylinder head bound. With every odd prime at most 73
   raised to height four, an actual family containing every nonunit divisor
   has an explicit survivor, but every survivor probability has
   `κ_Q(μ) > 1621563/10000 > 138877/1000`. The proof follows below.

## Evidence

The bridge program enumerates full CRT periods and uses exact rational arithmetic.
It checks both families, actual cylinder membership, disjoint hits, exclusive
coverage witnesses, probability laws, charges, and the second uncovered count.
It does not import or execute external Lean or Python sources. Archive SHA
and source-substring comparisons bind formulas to the cited release only.

Reproduction requires Python 3.8+ and its standard library, with no installation
of third-party packages. Download the archive linked by
[schroeder2026noncoverage](../Library/Arith/schroeder2026noncoverage.md), then run
from the repository root, replacing the archive argument with its location:

```sh
python3 docs/reports/erdos7-odd-covering/bridge_checks.py \
  --source-archive three_prime_factors_complete.zip
```

The program requires SHA-256
`5956327277ac47dd6e98a0a38f2a785cd61e647560c7f6ab5c73a63cf49faa51` and exits nonzero
on a mismatch even under `python3 -O`. Its paths can be supplied from any working
directory. Behavior checks ran on macOS with Python 3.14, including isolated
Python execution from a different directory with spaces in both input paths.
Other platforms and the minimum Python 3.8 runtime were not locally tested.
Source versions, pins, attribution, licenses, and completed external Lean checks
are in the Library notes. The bridge program is an original repository
experiment; it is not part of Schroeder's source release.

**H73: family and explicit survivor.** Let `P` be the 20 odd primes at most 73,
`Q = ∏_{p∈P} p⁴`, and `Q₀ = 3³·5²·7 = 4725`. The certificate's `core_residues`
contains 23 **`[modulus, residue]`** pairs, one for every nonunit divisor of
`Q₀`. Exact enumeration leaves 791 core survivors, including `3`.
For each outside prime `p ∈ P \ {3,5,7}` and `1 ≤ e ≤ 4`, assign the pure class

\[
 a_{p^e}=\frac{p^{e-1}-1}{p-1}.
\]

For a fixed prime these classes are pairwise disjoint: when `j > i`,
`a_{p^j} − a_{p^i} = p^{i−1}(1+p+⋯+p^{j−i−1})` is not divisible by `p^i`.
Thus avoiding the classes through level `e` permits exactly

\[
 N_p(e)=p^e-\sum_{i=0}^{e-1}p^i,\qquad N_p(0)=1
\]

residues modulo `p^e`. This follows by subtracting the disjoint lifts, of
sizes `p^{e−1},…,1`. Restrictions from higher levels or mixed classes can only
reduce the supported projections, so `N_p(e)` is an upper bound for them.

Put `M = ∏_{p∈P\{3,5,7}} p⁴`. Since `gcd(M,Q₀)=1`, define the explicit integer

\[
 w=\bigl(M\,((4M^{-1})\bmod Q_0)-1\bigr)\bmod Q.
\]

It satisfies `w ≡ 3 (mod Q₀)` and `w ≡ −1 (mod M)` and avoids every core and
outside pure class. On each remaining nonunit divisor `d | Q`, assign
`a_d = (w+1) mod d`. This cannot contain `w`, since `d > 1` cannot divide `1`.
All `5²⁰−1` moduli are odd, distinct and greater than one. The family includes
`Q`, so its actual least common multiple is `Q`. In particular, its survivor
set is nonempty and it does not cover the integers.

**H73: correlated-measure lifting.** Fix any probability `μ` supported on the
completed family's survivors, and project it to a probability `ν` modulo `Q₀`.
The latter is supported on the 791 core survivors. Write
`M_d(μ) = max_b μ{x : x ≡ b (mod d)}`. For `d | Q`, let `d₀ = gcd(d,Q₀)`,
`f_p = v_p(d)`, and set the core caps `a₃=3, a₅=2, a₇=1`. A fixed `d₀`-coset
meets at most

\[
 B(d)=\prod_{p\in\{3,5,7\}}p^{f_p-\min(f_p,a_p)}
       \prod_{p\in P\setminus\{3,5,7\}}N_p(f_p)
\]

supported `d`-cosets. CRT gives this counting bound on possible refinements;
it requires no independence of their probabilities. A `d₀`-coset attaining
`M_{d₀}(ν)` partitions into at most `B(d)` supported refinements. Pigeonholing
its mass, **separately for each divisor**, gives

\[
 M_d(\mu)\ge\frac{M_{d_0}(\nu)}{B(d)}.
\]

Regrouping the original coefficients `χ(d)/B(d)` by `d₀` therefore yields

\[
 \kappa_Q(\mu)\ge F\sum_{d_0\mid Q_0}\eta(d_0)M_{d_0}(\nu),\qquad
 F=\prod_{p\in P\setminus\{3,5,7\}}
       \left(1+\sum_{e=1}^4\frac{2e+1}{N_p(e)}\right).
\]

Here `η` is multiplicative on core divisors, with local coefficients

\[
 \eta(p^e)=2e+1\quad(0\le e<a_p),\qquad
 \eta(p^{a_p})=\sum_{k=0}^{4-a_p}\frac{2(a_p+k)+1}{p^k}.
\]

The sums include `d=1` and `d=Q` and retain the original `χ(p^e)=2e+1`.
The verifier independently reconstructs all 24 coefficients `η(d₀)` by
enumerating the 125 core exponent tuples in `{0,…,4}³`.

**H73: rational dual.** The certificate's 182 nonzero rational weights
`y_{d,b}` obey

\[
 y_{d,b}\ge0,\qquad \sum_b y_{d,b}\le\eta(d),\qquad
 \sum_{d\mid Q_0}y_{d,z\bmod d}\ge\alpha
 \quad\text{for every core survivor }z,\qquad
 \alpha=\frac{25730979793}{1000000000}.
\]

All omitted weights are zero. The verifier checks all 24 divisor budgets and
all 791 survivor inequalities; their minimum is exactly `α`. Consequently,

\[
 \sum_{d\mid Q_0}\eta(d)M_d(\nu)
 \ge\sum_{d,b}y_{d,b}\nu\{x:x\equiv b\pmod d\}
 =\sum_z\nu(z)\sum_{d\mid Q_0}y_{d,z\bmod d}\ge\alpha.
\]

Exact rational computation gives `α > 25`, `F > 6` and the sharper comparison

\[
 \kappa_Q(\mu)\ge\alpha F>
 \frac{1621563}{10000}>150>\frac{138877}{1000}.
\]

This proves H73 false for an actual finite height-four divisor family, for
every correlated or uncorrelated survivor measure. It is a mathematical proof
using exact finite computation, not a Lean formalization or a covering of `ℤ`.

**H73 reproduction.** The complete runtime inputs are the original repository
program `verify_h73.py` and `h73_dual.json`. The data contains only the 23 core
classes and 182 dual weights. A floating-point LP search supplied a candidate;
rational rounding and exact verification supply the certificate. No solver,
primal solution, numerical tolerance or process snapshot is needed or retained.
From the repository root run either command:

```sh
python3 docs/reports/erdos7-odd-covering/verify_h73.py
python3 -O docs/reports/erdos7-odd-covering/verify_h73.py
```

An optional positional certificate path is accepted; by default the JSON is
found beside the program, independently of the working directory. Python 3.8+
and its standard library suffice. Output includes exact rational `F` and `αF`,
the integer `Q`, family size and explicit integer `w`. Explicit failures remain
active with `-O`. The program checks the exceptional classes and the default
assignment rule; it does not enumerate all `5²⁰−1` full moduli. The passage from
the finite checks to all survivor probabilities is the counting and duality
proof above. Normal, optimized and isolated execution with spaced paths were
checked on macOS/Python 3.14; other platforms and Python 3.8 were not tested.

## Triage

`wall`: user-selected third-tier core research. The unrestricted target remains
open. For the precise complete-star head assignment, arbitrary positive
head heights and completely unrestricted tails above 73 are excluded by
(US1)--(US12). The proof uses the actual broad-branch law, the published
conditional convex comparison, an exact positive-part certificate through
prime 2039 and a supported `Gamma<4331` seed for BBMST continuation.
It remains an ordinary mathematical proof with exact numerical premises,
not a complete Lean theorem. Other head assignments remain unresolved.
The results also include exact obstacles to earlier proof routes, a direct
joint-load transfer into the BBMST continuation, and a quantitative reduction
of the arbitrary-height sufficient condition to a finite exponent cap. A
uniform four-prime head bound additionally proves the restricted noncoverage
theorem (P1), allowing arbitrary prime support at or above 67. The star-family
pointwise layout certificate refutes Γ73 and every displayed universal
finite-base bound, while leaving the unrestricted conjecture open.
The block-saturation criterion gives further noncoverage theorems for
arbitrary `{3,5,7}` heads with sparse tail interactions, and for every
positive-height star head with matching tails. It also gives the actual
mixed-tail budgets (BS8)--(BS9) required of any full star completion.
The new graph arguments additionally permit arbitrary forest tails from
prime 19 for arbitrary three-prime heads,
arbitrary forest tails above 73 for full star heads, a degree-two core with
unrestricted pendant leaves from prime 37, and the stated hub-deletion
structures. The forest bound is independent of both depth and degree.
The feedback-vertex recurrence additionally permits one cycle-breaking
vertex per tail component from prime 23 for arbitrary three-prime heads,
and two per component above 73 for full star heads.
The local-parent capped-kernel criterion extends this to arbitrary
`20`-degenerate tails above 73 for full star heads, and to forests from 17,
`2`-degenerate graphs from 19 and planar graphs from 23 for arbitrary
three-prime heads. Its selective parent moment bound allows unbounded
feedback vertex number and treewidth. Arbitrary graph structure is also
allowed by (RK1)--(RK5) when each original modulus has at most two tail
primes for the full star or three-prime heads, or at most three for the
finite 315/945 heads, at the respective stated cutoffs. The finite
switch (RK6)--(RK8) already removes support restrictions above its cutoffs;
(PH1)--(PH7), sharpened by (AD1)--(AD5), further removes every tail support and graph restriction for
these head classes at the stated prime gaps. The head exponents for the
315/945 rows and the missing primes remain genuine hypotheses. The star
rows retain quantitative bounds, while (US1)--(US12) exclude all star
completions without those restrictions.
The finite supported-law bridge (FC4)--(FC5) sharpens the planar cutoff
to 17 for heads dividing 315 and to 19 for heads dividing 945, the two odd
parts in the frozen 5040 fibre.
The finite-height pure-coordinate CRT criterion and two-block refinement
give the independent finite exclusion `lcm > 11486474`: the verifier
discharges all 23758 odd abundant candidates in the interval from 1.
`TernaryRootLoadTail.root_load_tail_le` formalizes the finite-itinerary
component of the actual-layout improvement, and
`TwoRootEventMoment.two_root_event_moment_le` proves the bound for the
actual weighted event-load increment.
`ArbitraryRootEventMoment.arbitrary_root_event_moment_le` extends that
component to arbitrary root sets and geometric discounts, using an actual
event-chain induction;
`PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le` formalizes
the weighted finite rectangle second-moment estimate underlying (W1),
with individual layer bounds retaining the shared zero layer.
`RestrictedSpineConstantPotential.restricted_spine_constant_potential`
formalizes the explicit constant-potential probability construction on arbitrary
finite restricted prefix trees, including its normalization and support.
`SequentialKernelCylinder.selected_cylinder_bound` formalizes the arbitrary
selected-coordinate cylinder bound for actual history-dependent Markov
kernels, directly reusing Mathlib's prefix-preservation result.
`HomogeneousCombCapacity.comb_le_actual_prefix_flow` formalizes the
all-height comparison between the actual forbidden-prefix flow recursion
and the extremal comb recursion, with arbitrary nonnegative capacities.
`PrefixCapacityRealization.exists_comb_capped_probability` constructs
an actual supported leaf probability from those capacities and derives
all prefix marginal caps after normalization.
No freeze or problem-resolution binding is supplied, and neither (P1) nor
(G1) is a complete Lean theorem.

## ASSUMED-UNVERIFIED

The external nine-prime result has no completed local kernel replay. The
three-factors-per-modulus theorem has the completed checks recorded in its
Library note, but `hThree` remains essential; its paper-only largest-prime-cutoff
extension is outside the Lean theorem. The joint-load transfer, exact finite
recurrence and restricted noncoverage theorem (P1) are proved above;
the universal Γ73 bound and the displayed sufficient finite-base bounds are
refuted by the complete star family.
These residue-level mathematical arguments have not been fully formalized
in Lean. The finite-itinerary and actual-event components are identified in (G2),
and the weighted finite rectangle second-moment component after (W1).
The nonuniform laws (N1)–(N10) and (NC1), sharp uniform bound (ZG1), shared-cofactor
improvement (P2), rectangular uniform-law obstruction and its nonuniform
repair (NR1) have ordinary mathematical proofs and exact rational checks,
not complete Lean proofs. The star-family refutation also has an ordinary
mathematical proof and exact certificate, not a complete Lean formalization;
its general restricted-tree probability construction is the Lean component
identified after (5) in the star-family proof.
H73 is refuted as a separate-cylinder claim. The random-tail layout certificate
additionally gives a true Gamma lower bound above 121.5478 for every law on
that family, below the sufficient threshold 138.877. Scalar-reweighting
optimality and the conditional conflict-graph query bridge also have ordinary
mathematical proofs, not complete Lean formalizations. Universal strict conflict-Shearer feasibility at charges `1/d` is false for
the star family; the conditional query theorem remains valid. No replacement
sufficient bound for unrestricted #7 is established here. These finite checks do not
establish literature priority or an unrestricted proof or covering counterexample.
The block-saturation criterion, its sparse-graph consequences for arbitrary
three-prime heads, and its all-positive-height star consequences also have
ordinary proofs and exact constant certificates, not complete Lean proofs.
The unrestricted-tail complete-star theorem (US1)--(US12) has the ordinary
actual-law, convex-comparison and stopping proof above and an exact directed
finite certificate. It does not extend the audited upstream Lean theorem
beyond its `hThree` hypothesis. The local selected-cylinder theorem proves
only the passage in (DG2); the changed star law, finite-height convex order,
original-label completion, positive-part computation and BBMST application
have not been combined into a Lean proof of the complete-star theorem.
The independent finite lcm exclusion through `11486474` likewise consists
of an ordinary CRT product-law proof and exact integer enumeration; no
local Lean formalization or duplicate declaration is claimed.

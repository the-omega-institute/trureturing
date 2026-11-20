---
bibkey: pascadi2025nonabelianamplification
authors: Alexandru Pascadi
year: 2026
title: Non-abelian amplification and bilinear forms with Kloosterman sums
doi: 10.1007/s00039-026-00746-0
url: https://arxiv.org/abs/2511.08445v2
claim: Conjecture 6.1 gives a uniform upper bound for alternating T,S return words in PSL_2(Z/cZ); Proposition 6.2 gives a weaker q=6 bound and proves the conjecture only in some parameter ranges.
strata_touched:
  - D5/S3/Arith/CharacterSums/PascadiSixWordFiber
  - D5/S3/Arith/CharacterSums/PascadiMinusRows
  - D5/S3/Arith/CharacterSums/PascadiOriginalCoefficients
  - D5/S3/Arith/CharacterSums/PascadiModularZeroPartners
  - D5/S3/Arith/CharacterSums/PascadiSingularResultant
  - D5/S3/Arith/CharacterSums/PascadiSingularFactorCover
  - D5/S3/Arith/CharacterSums/PascadiLocalizedFactor
  - D5/S3/Arith/CharacterSums/PascadiPrimeCubeSingularCover
  - D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount
  - D5/S3/Arith/CharacterSums/PascadiActualQuadraticResultant
  - D5/S3/Arith/CharacterSums/PascadiCubicQuadraticHeight
  - D5/S3/Arith/CharacterSums/PascadiSeventhHeightCover
  - D5/S3/Arith/CharacterSums/PascadiSingularValueEnvelope
  - D5/S3/Arith/CharacterSums/PascadiZeroDQuadratic
  - D5/S3/Arith/CharacterSums/PascadiZeroDCover
  - D5/S3/Arith/CharacterSums/PascadiZeroDBadDegreeAverage
  - D5/S3/Arith/CharacterSums/PascadiRankFourFactor
  - D5/S3/Arith/CharacterSums/PascadiRankFourBadDegreeAverage
  - D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier
  - D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase
  - D5/S3/Arith/CharacterSums/PascadiTorusConductor
  - D5/S3/Arith/CharacterSums/PascadiAffineVariance
license: source-reference
triage: anchor
---

# Pascadi's non-abelian amplification

Pascadi studies alternating return words

$$T^{a_1h_1}ST^{a_2h_2}S\cdots T^{a_1h_{q-1}}ST^{a_2h_q}S=I$$

in $\mathrm{PSL}_2(\mathbb Z/c\mathbb Z)$, for even $q$, units $a_1,a_2$ modulo $c$, and
$1\le H_1\le H_2\ll c$. Conjecture 6.1 predicts the bound

$$c^{o(1)}\left(H_2^{(q-2)/2}+\frac{(H_1H_2)^{q/2}}{c^3}\right).$$

For $q=6$, Proposition 6.2 proves the weaker estimate

$$c^{o(1)}\left(H_2^2+\frac{(H_1H_2)^2}{c}\right),$$

and notes ranges where the conjectured estimate follows. The median-range six-letter case
remains open in the source version.

The repository module `D5/S3/Arith/CharacterSums/PascadiSixWordFiber` formalizes the
entrywise compatibility equations for a fixed central scalar return and proves that each
fixed-middle completion fiber has period
$N=c/\gcd(c,(1-a_1a_2h_2h_3).\mathrm{val})$. For every $c>0$, units $a_1,a_2$ in
$\mathbb Z/c\mathbb Z$, central scalar $\gamma$ with $\gamma^2=1$, fixed
$h_2,h_3,h_5,h_6$ in $\mathbb Z/c\mathbb Z$, and $H\in\mathbb N$, it bounds the
actual return solutions by

$$\#\{(h_1,h_4)\in\{0,\ldots,H-1\}^2:
\mathrm{sixReturnWord}(a_1,a_2,h_1,h_2,h_3,h_4,h_5,h_6)=\gamma I\}
\le (\lfloor H/N\rfloor+1)^2.$$

Here the natural coordinates are reduced modulo $c$ only in the matrix product.
The bound includes $H=0$, arbitrary $H$ beyond $c$, composite moduli, and the
singular stratum $1-a_1a_2h_2h_3=0$, where $N=1$. The period is used to make the
coordinatewise quotient map injective on actual solutions. Summing over middle
coordinates with the strength required by Conjecture 6.1 remains open.

## Verified locator

Source: <https://arxiv.org/abs/2511.08445v2>, Section 6: Conjecture 6.1,
bound (6.2), and Proposition 6.2, weaker $q=6$ bound (6.3), including the
following remark on the parameter ranges where the conjecture follows.

The repository module `PascadiTorusConductor` gives an exact character
decomposition for the prime-cube cubic word associated with Section 6.
The quadratic Cayley transform, on unit denominators, turns
`x+y+z=d*x*y*z` into a product-one equation in the norm-one group.
At an odd prime the reduction of that group from the cube to the square
is onto with kernel of order `p`. The cube word mass therefore equals
the square word mass divided by `p`, plus the signed primitive cubic
character contribution. The quantitative bound for that contribution
remains open.

The repository module `PascadiAffineVariance` gives a centered coverage
bound for complex weights on affine lines over `ZMod p`. If each
nonzero Fourier mode annihilates at most `k` of the allowed directions,
the variance is at most `k*p` times the sum of squared line weights. At
a fixed third physical row the cubic word reduces modulo `p` to
`u₁+u₂+1=D*u₁*u₂`, with `D=g*x₃*y₃`. For `D` a unit and `D ≠ -1`,
the direction set is a nondegenerate hyperbola, yielding `k=2`.
The weighted correlations between different pivot products remain
part of the open fixed-coefficient estimate.

The journal version is *Geometric and Functional Analysis* 36 (2026),
1174–1243, <https://doi.org/10.1007/s00039-026-00746-0>.
For $c=p^3$, Proposition 6.2 gives
$p^{o(1)}Y^2(1+X^2/p^3)$, so it already supplies the desired scale when
$X\ll p^{3/2}$. It does not supply it throughout
$p^{3/2}\le X\le Y$, $XY\le C_0p^{18/5}$, $6Y<p^2$:
at $X=Y=p^{9/5}$ the extra factor is $1+p^{3/5}$.
The 17 November 2026 bounded literature screen covered both arXiv versions,
the journal text, the conjecture's cited results and identifiable citing papers;
no theorem covering this whole prime-cube range was found in that scope.
This does not establish exhaustive novelty or priority. The later repository
prime-cube continuation below proves that precise original-tuple estimate;
the final Shkredov journal-text comparison remains incomplete.

The continuation also checked the current primary texts arXiv:2605.02518v2
(Zhang) and arXiv:2603.14116v2 (Shkredov). Zhang's Theorem 2.4 requires
trace-hyperplane nonconcentration; the natural two-letter unipotent product
here has a fixed lower-right matrix entry, so that theorem does not directly
apply. Its Theorem 3.6 concerns a specified Mobius incidence configuration.
Shkredov's class Z includes sufficiently large prime cubes, but Lemma 14
averages a common shift and Lemma 15 counts a small-N Mobius incidence; neither
is the fixed-coefficient six-return estimate above. These checked distinctions
do not exhaust the citation graph. The final 2021 Journal of Number Theory
text cited by Pascadi was not obtained; Pascadi's published attribution to its
Lemma 15 is explicitly in the prime-modulus case. No exhaustive priority
claim follows from this bounded comparison.

The 18 November primary-text comparison also read Shkredov's
arXiv:1905.00291v1, Lemma 14 and Theorem 4, Chang's author manuscript
*Product theorems in SL2 and SL3*, Theorem 2, and the final 2011
*Partial quotients and equidistribution*, Proposition 1 and Theorems 2–5.
The inspected Shkredov statements require a field or prime field; the
hyperbola reconstruction divides by a derived nonzero element, which need
not be a unit modulo a prime cube. Chang's first theorem concerns product-set
growth in characteristic zero; the second paper's conclusions concern prime
moduli and subgroup averages or typical elements. These specific statements
do not provide the required bound for every fixed pair of units modulo
`p^3`. Shkredov's final JNT 220 (2021), Lemma 15, DOI
`10.1016/j.jnt.2020.06.014`, remains unverified: its arXiv v1 numbering must
not be substituted for the final journal text. This is a bounded comparison,
with no exhaustive novelty or priority conclusion.

## Repository prime-cube continuation (16 November 2026)

The new `PascadiMinusRows` module proves the original literal-box reduction
`Nminus ≤ 3 * Uminus + 8 * (2 * Y + 1)^2` for prime `p`, `X ≤ Y`,
`6 * Y < p^2`, and the same units `a₁,a₂` modulo `p^3`.
Odd letters lie in `[-X,X]`, even letters in `[-Y,Y]`; units are not multiplied
into the intervals. `Uminus` filters those same actual word solutions by
`p ∤ t*w`. The proof includes zero/nonunit rows, all-six-divisible tuples and
repeated endpoints. It uses exact four-equation equivalence for the existing
`sixReturnWord`, all three minors, cyclic charts and a direct finite pivot encoding.
The bound does not need the additional lower bound `p ≤ X`.

`PascadiOriginalCoefficients` constructs physical integer endpoints from lattice
coordinates and forms the literal coefficient functions of `L₀Q−LQ₀`.
Its root identity is derived from the actual original word equation, using
`β=V₁/R₁` and `α=−1/(g*t*R₁)`; it is not supplied as a polynomial-root hypothesis.
Literal coordinate bounds also give coefficient constant `C=3`, actual pencil
height `H=18`, and degree at most three.

The actual lattice construction and modular-zero partner count are now integrated
through [PR #31327](https://github.com/the-omega-institute/trureturing/pull/31327).
`PascadiOriginalLattice` constructs the shortest primitive vector, its Bezout
completion, the centered reduced basis and the literal coordinate bounds.
`PascadiModularZeroFieldPartners`, `PascadiModularZeroPartners`,
`PascadiModularZeroRegularity` and `PascadiOriginalModularPartners` count the
full modular-zero partner set for a nonaligned retained original baseline,
including both dividing directions and the nondividing six-candidate case.
Their explicit coordinate-height and unit hypotheses remain part of the results.

`NumberFieldDivisorSubpower` proves the bounded algebraic-divisor estimate with
one constant uniform over number fields of degree at most three.
`PascadiOriginalSingularPartners` constructs the actual algebraic values and
their nonzero fixed products from the original word. Together with
`PascadiOriginalLinearFibers`, `PascadiOriginalSingularCount` bounds the actual
nonzero singular partner set by
`C_epsilon p^epsilon (1+6H/(p*sigma))`, where sigma is the shortest length of
the actual index-p-squared lattice. The original word determines the second
endpoint, so this physical multiplicity is paid once.

`PascadiOriginalWeightAverage` proves the full finite dyadic average of
`1+H/(p*sigma)` over actual integer `(w,t)` in the literal parameter rectangle.
For `1<=X<=Y`, `Y<p^3`, `A=XY<2p^4`, `H^2=A` and `p<=H`, its bound is
`2048[A+(A/p)(1+log(2p)/log(2))+A^2/p^4]`.
These are explicit sufficient conditions; applying them to the target range
still requires checking that range's hypotheses.

`PascadiPrimeCubeCount.prime_cube_scalar_return_count` now proves the original
prime-cube slice: for every epsilon>0 and C0>=1, one K>0 bounds the total literal
six-letter count, summed over every scalar gamma with gamma^2=1, by
`K*Y^2*p^epsilon`, for every prime p, fixed alternating units modulo p^3,
`p^(3/2)<=X<=Y`, `XY<=C0*p^(18/5)` and `6Y<p^2`. The proof connects the
derivative and exceptional partners, actual record moments, all removed
charts, nonunit rows, all scalar centers and the bounded-prime range without
supplied lattice or counting hypotheses. The exact-root Lean build and scoped
report passed; canonical publication and required CI are separate checks.
The unrestricted arbitrary-modulus conjecture remains open. The supplied
paper proof is an input with the separate provenance below. Source-bound
four-slot escape audits remain unfinished
under [issue #31176](https://github.com/the-omega-institute/trureturing/issues/31176);
no completed registration is claimed for these new modules.

The 18 November continuation strengthens the area restriction to
`XY<=C0*p^alpha` for every fixed real `alpha<26/7`, with the same lower-width,
upper-width, unit and all-center conditions. The constant can depend on
epsilon, C0 and alpha, but remains independent of p, X, Y and the two units.
The old eighteen-fifths statement is retained as a consequence. The exact-root
Lean build and scoped axiom report passed; this statement does not claim that
the new delivery's required remote checks have completed.

The improvement uses the actual pencil structure. The genuine degree-two
branch has seventh weighted resultant height, including zero baseline leading
coefficients. A degree-two factor of a genuine cubic gains an extra J/I in
its coefficient height, giving a sixth-weight mixed resultant. Together with
the existing seventh-weight cubic residual, one common condition is
`C7*(IJ)^7<p^5`. Since `IJ<=32XY/p^3`, every fixed alpha<26/7 satisfies this
condition for all sufficiently large primes. The algebraic value envelope
separates its real height parameter from the modular prime and uses T=p^2;
the physical endpoint multiplicity is still paid once. Actual zero-reduction
counts, bad-degree averaging, retained records, unit-middle counting, nonunit
rows and all scalar centers are assembled into
`prime_cube_scalar_return_count_of_exponent`. The oracle broker suggested
the cofactor elimination route and provided literature leads; Codex derived
and formalized the explicit branches and counting assembly. No priority claim
is inferred from the bounded literature screen. The strict endpoint
alpha=26/7 and the full arbitrary-modulus conjecture remain open here.

## Zero Dixon residuals and the actual bad-degree average

`PascadiZeroDQuadratic` proves the actual constant-baseline identity
`l0*D=-(m1*s2-m2*s1)*Res22(P1,P2)` over every commutative ring when
`m0=s0=0`. It then proves the complete zero-D quadratic elimination under
`6804*I^6*J^4<p^5`, including a zero leading baseline and a primitive
direction with `k0=0`. `PascadiZeroDCover` consumes this elimination to
construct at most three primitive irreducible factors covering every
nonzero-reduction singular pencil. Each factor divides the chosen reference,
vanishes at the modular root and has nonzero reduction. The common gap is
`max(6804,24*(8*Hcoeff)^4)*(IJ)^6<p^5`; rank, baseline-resultant units and a
supplied factor cover are not required.

`PascadiZeroDBadDegreeAverage.actual_long_bad_degree_average_zero_dixon`
connects this cover to the original finite endpoint families. At each actual
middle it requires one baseline attaining the maximum bad-partner degree;
only that baseline's nonzero-reduction bad partners must have pairwise zero
actual Dixon residuals. The empty endpoint family and all zero-reduction
partners are included. Original words, units, literal boxes, genuine reduced
bases and physical anchors remain explicit hypotheses. With `A=XY` and
`C6=10319560704`, the sixth-height gap `C6*(32*A/p^3)^6<p^5` gives

$$\sum_{(w,t)\in s}D_{\mathrm{bad}}(w,t)
\le C_\epsilon p^\epsilon\left(A+\frac Ap
\left(1+\frac{\log(2p)}{\log2}\right)+\frac{A^2}{p^4}\right).$$

The proof derives the actual factor counts and long-chart coordinate bounds,
then applies the existing physical-weight average on that same finite middle
set. It introduces no factor counting the possible baselines and does not
assume an endpoint or weight estimate. The width condition remains `2Y<p^3`;
the later moment condition `3Y<p^2` is not added to this theorem.

These are repository-derived mathematical continuations of the original
problem. Codex derived the constant-baseline elimination, implemented its
cover and actual counting consumer, and checked the retained Lean and Reg
sources with scoped reports. Four-slot registration of all four new public
results remains unfinished under
[issue #31176](https://github.com/the-omega-institute/trureturing/issues/31176);
the compiled positive-law Reg attempts are not completed registration.
This proves the selected zero-D branch average, not a larger total-count
exponent. The delivered unconditional total-count range remains every fixed
`alpha<26/7`; the nonzero-residual average and the full arbitrary-modulus
conjecture remain separate open work. No literature priority is claimed.

## Rank four and its original average

Lemma 2.6 of the repository's
`PASCADI_PRIME_CUBE_PROJECTION_IDEAL_ENDPOINT` volume is formalized in
`PascadiRankFourFactor.rank_four_root_relevant_factor`. For a finite
coefficient family with common value modulo the prime cube and common
derivative modulo the prime, the three inequalities in (2.16) bound rational
row rank by four. In rank four the primitive integer factor has the form
`aT-n` with positive leading coefficient, unit leading reduction and
`a*beta-n=0` modulo the prime. It divides the integer pencil of every row
and its rational root has nonzero baseline linear value.

`PascadiRankFourBadDegreeAverage.actual_long_bad_degree_average_rank_four`
uses that factor on the actual maximizing family. The rank includes the
baseline and all nonzero-reduction derivative-zero partners. At the common
root every selected quadratic value is a common multiple of its linear
value. This gives zero Dixon determinants and yields the original average
above under `C6^2*(32*A/p^3)^13<p^10`. The degree still includes the
zero-reduction partners and is zero for empty endpoint families.

## Quadratic nonzero middle sections

`PascadiQuadraticMiddleCount.quadratic_nonzero_middle_box_count` proves a
geometric ingredient for averaging a fixed physical quadratic kernel.
For an actual reduced basis of the determinant-c congruence lattice, let
an integer-valued degree-two homogeneous Q satisfy q divides Q on the
lattice and `|Q(z)|<=M[(Y/X)z1^2+(X/Y)z2^2]`, with c,q positive and M
nonnegative. A finite literal-box section avoiding Q=0 has at most
`1+4*sqrt(XY)*sqrt(M/q)+24*XY/c` points. The theorem includes split
quadratic forms: when the shortest direction is a null line, every point
of that entire central line is excluded. Other rows are counted with
their nonzero transverse integer coordinate, removing its perimeter term.

The proof reuses the existing actual-lattice reduction and proves the
new count without a counting supplier. Its ordinary geometric proposal
was supplied through the oracle broker, with the Lean proof implemented
by Codex. This is a repository-derived estimate, not an attribution to
Pascadi or a claim of mathematical priority. The proposed arithmetic
substitution c=p^2, q=p^(6-j), M of order (XY)^2/p^(3+j), for j=3 or 4,
would give the common boundary scale (XY)^(3/2)/p^(9/2). The primitive
physical-kernel supplies and two-root cover remain separate from this
formal result. No fixed alpha greater than 26/7 or closure of the
non-split branch follows from the lattice theorem alone. Four-slot audit
registration remains unfinished under issue #31176; the typed Reg
positive law is not completed registration.

The four integrated singular-factor modules retain the proofs from the completed
research archive `pascadi-prime-cube-singular-cover-formalization-20261116`.
Necessary archived helpers are exposed publicly, replacing private-name elaborator
access. The original file identities are:

- `PascadiPrimeCubeSingularCover.lean`: SHA256 `b41d415ccf6f20adf7b23aad0d6ed2dd09bf9628cf2a0eb37faba3ceaa13572e`.
- `PascadiLocalizedFactor.lean`: SHA256 `3f4fdb232cd07f365c10aa8b032bf2f35396742aa6cbc4a51772a83494541b9f`.
- `PascadiSingularFactorCover.lean`: SHA256 `c2325493ea58a5a79ded8c4c26c14dc4813bbeac332f30d515346cb04cb282c4`.
- `PascadiSingularResultant.lean`: SHA256 `eb9f9c502221986f3b7f64263954614829ffd601da25470495669c1b2fcd2d54`.

The completed application proof was supplied as
`pascadi-prime-cube-actual-application-review-20261116/proof.tex`, SHA256
`c6e76b431b78245ce924f62084548f932f524c5908dbcdc3802bf8ef97275e0c`,
with author line “Independent mathematical source review”. This worker implements
the row reduction and starts actual coefficient realization; the supplied paper
proof and archived Lean endpoint have distinct provenance from this implementation.
These repository results are not attributed to Pascadi as published theorems and
do not claim to settle his full uniform conjecture.

## Ordinary endpoint proof and its formal boundary

The complete repository-derived ordinary proof is
[Projection–ideal averages for prime-cube six-letter returns](../../docs/develop/theory/PASCADI_PRIME_CUBE_PROJECTION_IDEAL_ENDPOINT.md).
Its Theorem 1.1 states: for every $\varepsilon>0$ and $C_0\ge1$ there is
$C(\varepsilon,C_0)>0$ such that, for every prime $p$, every fixed pair
$a_1,a_2\in(\mathbb Z/p^3\mathbb Z)^\times$, and real widths

$$
p^{3/2}\le X\le Y,\qquad XY\le C_0p^{15/4},\qquad 6Y<p^2,
$$

the number of literal integer tuples with odd coordinates in $[-X,X]$
and even coordinates in $[-Y,Y]$, summed over every scalar
$\gamma\in\mathbb Z/p^3\mathbb Z$ with $\gamma^2=1$, satisfying

$$
\prod_{i=1}^3
 \begin{pmatrix}a_1h_{2i-1}&-1\\1&0\end{pmatrix}
 \begin{pmatrix}a_2h_{2i}&-1\\1&0\end{pmatrix}
 =\gamma I_2
$$

is at most $C(\varepsilon,C_0)Y^2p^\varepsilon$. The constant is uniform
in the prime, widths and units. The coefficients remain fixed in every
average. The ordinary endpoint includes all strict $\alpha<15/4$ ranges;
it does not assert the arbitrary-modulus conjecture. Earlier statements
above that leave larger total-count exponents open describe the scope of
the corresponding Lean results; the ordinary mathematical range is now
the one stated here.

Sections 1–7 retain the full ordinary proof, including the original
six-chart cover and unconditional retained moment, maximum bad-degree
selection, zero-reduction partners, rank four, zero Dixon residual,
saturation, both coordinate-discriminant strata, all residual layers,
and the retained older ideal-only auxiliary estimate. Rank four has
threshold $49/13$, zero residual has threshold $23/6$, and the $j=4$
contribution has threshold $233/61$ and endpoint saving $p^{-17/36}$
relative to $A=XY$. The $j=4$ branch does not use the $j=3$ identity
$D_L=\pm p^8\kappa$.

For all three $j=3$ cases—unramified nonsplit, rationally split, and
ramified—the proof uses the same selected actual family and the actual
primitive physical lattice. Its indices and principal-ideal norm give
$h\mid\kappa$, $n=|\kappa|/h$, and $|N(E)|=p^8n/(h^2c^3)$.
The unramified fixed ideal factor is $(p)^3\mathfrak p^2$; the ramified
factor is $(p)^4$, also of norm $p^8$. The latter is proved in the single
ramified field with $v(p)=1$, including the local value $v(E)=4$ and
the conductor-order gluing. The raw determinant functional retains the
selected maximum baseline, and its zero layer is counted. With
$K=C_DA^7/p^{26}$, the actual partner bound is
$p^{o(1)}(1+(K/(hn))^{1/3})$. The same actual triple gives
$h\ll T$, $n\ll K/T$ on a height segment $T$.

The affine module keeps $X_*\in J^2$ with its rational coefficients;
no global denominator is cleared. Five unit-safe shears give actual
projection intervals of lengths $O(TX),O(TY)$ and a four-coordinate
inverse graph modulo $p^2$. Original middles remain in their short
integer box with difference lattice $\Gamma_0$. Projections use the
sheared difference lattice $\Gamma_z=S_z\Gamma_0$. The sheared actual
witness need only lie in $O(X)\times O(Y)$, and shortest-vector counting
on the difference lattice handles affine projection cosets. Split null
directions are retained. Long projection intervals are residue existence
indicators; choosing one lift injects their residue support into the
actual integer projection coset. The middle and projection Fourier
slopes are both units and may differ. The fixed-data support bound is

$$
M_T\ll_\eta p^\eta(T^2A^2/p^6+p^{3/2}).
$$

Generator pairs, rather than merely kernels admitting a generator, are
counted using ideal cube classes, unit cubes and index-$p$ subgroups.
The complete gcd-aware Kloosterman bound is the published input in
Pascadi, Lemma 3.3, Section 3.2. The quadratic-order input is
Bhargava–Varma, *The mean number of 3-torsion elements in the class
groups and ideal groups of quadratic orders*, Proceedings of the London
Mathematical Society 112 (2016), 235–266,
[DOI 10.1112/plms/pdv062](https://doi.org/10.1112/plms/pdv062),
[arXiv:1401.5875](https://arxiv.org/abs/1401.5875), Theorem 2(a),(b).
It supplies the ordinary $\operatorname{Pic}(\mathcal O_d)[3]$ mean over
all quadratic orders of each sign, including nonmaximal orders. Local
restrictions are dropped before applying that mean; no average uniform
in varying local specifications is claimed. Rationally split orders have
their own explicit gluing-class and ideal counts in Section 6.9.

The joint summation gives the actual weighted $j=3$ contribution

$$
\mathcal W_{j=3}\ll_\eta Y^2p^\eta
 \left(\frac{A^{12}}{p^{45}}+\frac{A^{10}}{p^{75/2}}\right).
$$

At $A\le C_0p^{15/4}$ both area factors are bounded constants.
Subpower exponents are split among the divisor, layer, ideal, Fourier
and dyadic estimates; no strict area saving absorbs a logarithm.
The retained moment uses $A^4/p^{15}\le C_0^4$. Separate doubling of
the two widths, the factor 64, at most four scalar centers, all removed
charts and the bounded-prime count complete the original theorem.

The current Lean total-count theorem remains
`D5.S3.Arith.CharacterSums.Original.prime_cube_scalar_return_count_of_exponent`
in `D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount.lean`, with
`alpha<26/7`. The manuscript's original-count source reference is
[PR #31391](https://github.com/the-omega-institute/trureturing/pull/31391),
merged commit `1ba767ed7b91862093486b62812d05071ff5a392`.
This preservation adds no Lean declaration and does not
assert enlarged-range Lean, kernel or official acceptance. The four
scoped zero-D results are integrated by
[PR #31431](https://github.com/the-omega-institute/trureturing/pull/31431),
merged as `0997d09`; the supplied publication evidence records successful
required PR CI and a first-dev CI run still running at dispatch. No
successful first-dev result is inferred from that observation. These
four scoped results certify their own statements, not the endpoint
assembly. The unfinished registration boundary under issue #31176 above
is retained.

### Exact locators for the mathematical inputs

In this table `Original` abbreviates
`D5.S3.Arith.CharacterSums.Original` and `PrimeCube` abbreviates
`D5.S3.Arith.CharacterSums.PrimeCube`. These are source locators for
already proved intermediate inputs, not new declarations or a claim
that the endpoint is formalized. Section and equation numbers refer
to the complete theory volume.

| Mathematical clause | Existing exact source locator |
| --- | --- |
| Word and real-box membership, Section 2.1 | `D5.S3.Arith.CharacterSums.returnStep`, `sixReturnWord`, `scalarReturn`; `Original.mem_scalarSolutionsReal` |
| Four minus equations and third minor, Lemma 2.1 | `D5.S3.Arith.CharacterSums.sixReturnWord_minus_iff`, `D5.S3.Arith.CharacterSums.MinusEquations.third_minor` |
| Scalar factor 64 and doubled separate widths, (2.2) | `Original.scalarSolutionsReal_card_le_minus_doubled` |
| Three-width unit-middle reduction, (2.4) | `Original.Nminus_le_three_Uminus_of_three_width` |
| Six-chart cover, Section 2.2 | The partition used inside `Original.actual_unit_middle_tuple_count_seventh`; its old whole-count seventh-height estimate is not applied at the new endpoint. The five individual chart bounds below are combined with the new retained-family estimate. |
| Nonunit shortest and short unit shortest charts | `Original.actual_nonunit_shortest_tuple_count`, `Original.actual_unit_shortest_short_tuple_count` |
| Long nonunit right side, zero endpoint and nonunit endpoint charts | `Original.actual_long_nonunit_rhs_tuple_count`, `Original.actual_zero_endpoint_tuple_count`, `Original.actual_nonunit_endpoint_tuple_count` |
| Pencil and maximum bad degree, Section 2.3 | `Original.endpointL`, `Original.endpointQ`, `Original.pencil`, `Original.recordBeta`, `Original.actualRecordBadPartners`, `Original.actualRecordBadDegree` |
| Retained moments (2.6)–(2.7), Proposition 2.2 | `Original.actual_retained_endpoint_count`, `Original.actual_dyadic_retained_endpoint_count` |
| Good-record second moments and original-row reconstruction | `Original.actual_large_retained_second_moment`, `Original.actual_dyadic_large_second_moment`, `Original.actual_retained_rows_dyadic_count`, `Original.actual_record_product_bounds`, `Original.actual_record_reconstruction` |
| Exact height scales (2.8) | `Original.ReducedMiddleBasis.coordinate_bound`, `Original.ReducedMiddleBasis.anchor_coordinate_bound`, `Original.ReducedMiddleBasis.long_scale_bounds` |
| Endpoint numerical absorption, Corollary 2.3 | `Original.range_error_absorption_of_exponent`, in `PascadiOriginalRangeEstimates.lean`, with `alpha<=15/4` and arbitrary `C0>=1` |
| Original pencil divisibility and modular-zero partners | `Original.original_pencil_dvd`, `Original.actual_zero_reduction_partners_subpower_seventh` |
| Literal row and pencil heights | `Original.actual_coefficient_bounds`, `Original.actual_pencil_coefficient_bounds` |
| Dixon matrix, resultant identity and bounds | `PrimeCube.residualMatrix`, `PrimeCube.residual`, `PrimeCube.actual_residual_resultant`, `PrimeCube.actual_residual_dvd_fifth`, `PrimeCube.actual_residual_height` |
| Nonzero Dixon coordinate saturation and discriminant strata, Lemmas 3.1–3.2 | `PrimeCube.nonzero_dixon_rank_three`, `Original.original_nonzero_dixon_rank_three` |
| Quadratic-direction elimination, Lemma 2.4 | `PrimeCube.quadratic_direction_resultant_zero`; the constant-baseline repair is `PrimeCube.constant_base_dixon_quadratic_identity` and `PrimeCube.zero_dixon_quadratic_resultant_zero` |
| Root-relevant factorization and mixed quadratic branch, Lemma 2.5 | `PrimeCube.localized_factor_cube`, `PrimeCube.cubic_quadratic_mixed_resultant_height`, `PrimeCube.quadratic_resultant_dvd_fifth`; `PrimeCube.actual_zero_dixon_singular_factor_cover` |
| Actual factor-value and singular-partner counts, (2.15) | `Original.actual_fixed_factor_value_pairs_subpower`, `Original.actual_singular_factor_partner_count`, `Original.original_singular_unit_observations` |
| Actual index-$p^2$ physical-weight average | `Original.actual_physical_weight_average` |
| Scoped zero-D bad-degree average | `Original.actual_long_bad_degree_average_zero_dixon` |

The preserved ordinary source is
`pascadi-prime-cube-projection-average.tex`, SHA256
`53c289cd83adeee1cdc34b4d61ac09ae1fbcb045f4985555d3b6314bdfeed30b`.
The theory volume retains that complete 41-page proof, with the explicit
support and lift argument supplied by
`pascadi-endpoint-support-lift-independent.proof.txt`. Neither local
evidence file is needed to fill a proof step in the repository volume.
The problem is Pascadi's; the named Kloosterman and Bhargava–Varma
results remain external inputs. Derivative and global-arithmetic routes
originated in prior Pro proposals and independently derived actual-family
mathematics. The earlier Pro Section 2 error is not used: the retained
proof uses the repaired actual local, ideal, index and correlation
arguments. Native Codex supplied implementation, mathematical derivations
and independent ordinary-proof reviews in a repository-exposed setting.
No model-family diversity or sterile independence is asserted.

The bounded primary-text comparisons recorded above found no covering
theorem in their checked scope. The final JNT 220 (2021), Lemma 15,
DOI `10.1016/j.jnt.2020.06.014`, remains unobtained and unverified;
its arXiv numbering is not a substitute. That result is not an input
to this proof. This is preservation of a repository-derived ordinary
endpoint proof, with no exhaustive literature novelty, global priority,
official acceptance or completion of the main research goal claimed.

## Prime-cube counts beyond the $15/4$ endpoint

Let $A=XY$, $p^{3/2}\le X\le Y$, $6Y<p^2$, and $A\ll p^\alpha$
for a fixed $\alpha<49/13$. The ordinary proof gives the original
scalar six-return bound $O_\varepsilon(Y^2p^\varepsilon)$ for every
prescribed pair of unit coefficients when $A^3\ll Y^2p^{15/2}$.
For $15/4<\alpha<49/13$, the same bound holds simultaneously at all
admissible widths outside an exceptional set of
$O(p^{4\alpha-15}\log(2p))$ lifts modulo $p^3$ of each nonzero residue
class modulo $p$ for the product $g=a_1a_2$. The set can depend on $p$,
the area constant, and $\alpha$. Extending the balanced range to
every prescribed $g$ requires a bound on the concentration of the
last coefficient digit among irreducible simple-root configurations.

The digit calculation uses the map
$(x,s)\mapsto(C/x,Cs/x^2)$ on units modulo $p^2$ and digits modulo
$p$. Completing the two digit sums leaves exactly the phase at each
unit residue $a\bmod p$ satisfying
$\bar A a^2=\bar C\bar B$ and $Da^2=-\bar CE$, with a factor $p^2$.
Here $A,B,D,E$ in the phase denote frequencies. In the unit sector
there are at most two surviving residues and the nonzero Fourier
coefficients lie on paired frequency lines. The ordinary proof sums
the interval weights on those lines using the shortest vector of the
actual index-$p$ lattice. This pays the nonsplit branch at all
admissible aspects. The split branch is controlled by the count of
middles for a fixed kernel. Selecting the largest derivative line at
each middle and applying an additive large sieve to the reducible
relative cubics reduces the coefficient average to the irreducible
simple-root configurations.

`PascadiMixedQuotientFourier` formalizes the exact complete coefficient,
mixed-sector vanishing, and unit-sector bound and support. Its
Lean 4.35 scoped report verifies 45 declarations using
`Classical.choice`, `Quot.sound`, and `propext`. The original lattice
instance, weighted arithmetic estimate, and enlarged counting ranges
are ordinary mathematics. Source-bound four-slot registration for the
three Fourier theorems remains open.

The repository's `PascadiTransverseCriticalPhase` module proves the exact
signed radical identity for the transverse unit chart over `ZMod(p^2)`.
For each nonzero root residue it constructs the unique lift in each pair
of upper digits. Summing the additive character over those two digits
gives zero unless both stationary equations hold modulo `p`. In the
stationary case it gives `p^2` times the character at the base root.
This is an exact local phase identity for the ordinary analysis of
Conjecture 6.1. Estimating the weighted correlations between distinct
stationary phases in the short frequency box remains open.

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
not prove coverage at 945. The joint-load and survivor-profile estimates
below retain the residue intersections that this scalar sum omits.

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
those optimization statements to the universal Γ73 bound has not been proved.

## Gap

The remaining sufficient target is a universal bound on the joint-load
functional for complete survivors of an arbitrary small-prime head. The
one-prime transfer below proves that Γ73 suffices for arbitrary later prime
support. The height-lifting theorem further reduces a sufficient target to
one explicit, but still unproved, finite exponent cap. Higher-support cofactors
and the mass on complete survivors remain in both estimates. Three exact
obstacles below exclude earlier omissions and the separate-cylinder head bound.

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

**Γ73 — unproved candidate**, preregistered at the same issue: for every
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
mutually compatible. This is a proposed replacement for the separate-cylinder
cost, not a consequence of H73's failure. A lower bound for `κ_Q` gives no lower
bound for `Γ_Q`. The conditional transfer and finite-height calibration below do not establish Γ73.
The stronger demand that this law always be uniform is false: the rectangular
family below has uniform `Γ>142.3789923` but admits a nonuniform law with
`Γ<134.121`. Thus it leaves the existential target open.

## Route

The joint-load invariant retains actual residue intersections. Its transfer
and the restricted noncoverage result are established below; a sufficient
unrestricted head bound remains the missing input.

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
A uniform accumulated improvement sufficient for Γ73 remains unproved.

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

The remaining sufficient input is a bound, uniform over the actual family
and all complete test layouts, on the resulting subtraction together with
the test load's deficit from the unconditioned maximum. No such bound
strong enough for the unrestricted head is established here. These
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
the universal Γ73 existence bound is still unproved. This conditional result
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
**None of these universal finite-base bounds has been proved.** In particular,
the calibration is a sufficient implication, not a finite verification of all
residue assignments. The height-lifting argument is not formalized in Lean.

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
**Every universal finite-base bound in this table remains unproved.** The
squarefree `Γ<138.874` result does not supply the cap-3118 hypothesis.
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
The nonuniform existential Γ73 target remains open. The argument and exact
arithmetic are not a Lean proof.


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
open. The results include exact obstacles to earlier proof routes, a direct
joint-load transfer into the BBMST continuation, and a quantitative reduction
of the arbitrary-height sufficient condition to a finite exponent cap. A
uniform four-prime head bound additionally proves the restricted noncoverage
theorem (P1), allowing arbitrary prime support at or above 67. The universal
finite-base bound needed for the full conjecture remains unproved.
`TernaryRootLoadTail.root_load_tail_le` formalizes the finite-itinerary
component of the actual-layout improvement, and
`TwoRootEventMoment.two_root_event_moment_le` proves the bound for the
actual weighted event-load increment;
`PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le` formalizes
the weighted finite rectangle second-moment estimate underlying (W1),
with individual layer bounds retaining the shared zero layer.
No freeze or problem-resolution binding is supplied, and neither (P1) nor
(G1) is a complete Lean theorem.

## ASSUMED-UNVERIFIED

The external nine-prime result has no completed local kernel replay. The
three-factors-per-modulus theorem has the completed checks recorded in its
Library note, but `hThree` remains essential; its paper-only largest-prime-cutoff
extension is outside the Lean theorem. The joint-load transfer, exact finite
recurrence and restricted noncoverage theorem (P1) are proved above;
the universal Γ73 bound and the sufficient finite-base bounds remain unproved.
These residue-level mathematical arguments have not been fully formalized
in Lean. The finite-itinerary and actual-event components are identified in (G2),
and the weighted finite rectangle second-moment component after (W1).
The nonuniform laws (N1)–(N10), sharp uniform bound (ZG1), shared-cofactor
improvement (P2), rectangular uniform-law obstruction and its nonuniform
repair (NR1) have ordinary mathematical proofs and exact rational checks,
not complete Lean proofs.
H73 is refuted and supplies no lower bound for Γ73. These finite checks do not
establish literature priority or an unrestricted proof or covering counterexample.

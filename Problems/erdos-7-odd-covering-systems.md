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

## Reuse of the 5040 and divisor-sum work

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

## Arbitrary-head transfer by the joint-load invariant

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

## Transfer retaining the actual forbidden-fibre geometry

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
These profile-sensitive inequalities have not been formalized in Lean.
A uniform accumulated improvement sufficient for Γ73 remains unproved.

## Exact continuation from the conditional 73-head seed

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

## Quantitative extension of the old prime powers

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

## One-stage smoothing of the height lift

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

## A four-prime head and a restricted noncoverage theorem

**Theorem.** A finite family of residue classes with distinct odd moduli
greater than one cannot cover the integers if every prime divisor of every
modulus belongs to

\[
 \{3,5,7,11\}\ \cup\ \{p:\ p\text{ prime},\ p\ge71\}.
 \tag{P1}
\]

There is no bound on the exponents, the number of large prime divisors, or the
number of prime divisors of a single modulus. Equivalently, any hypothetical
distinct odd covering must use a modulus divisible by at least one of the
primes from 13 through 67. This is a restricted theorem, not the full conjecture.

The head estimate used to prove it is the following uniform statement.
For any finite distinct-modulus family supported on `{3,5,7,11}`, its complete
survivor set is nonempty, and the uniform survivor probability satisfies

\[
 \boxed{\Gamma\le C_4:=\frac{28643873521}{258465470}<110.82283.}
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
it to (P2). Its cutoffs remain `(2,1,0,0)`.
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

The last inequality proves (P2). The refined profile verifier checks
the eighteen vertices, the absent-modulus branch, this induction and
the two-step continuation below. Its independent finite-box calculation
brackets the resulting profile envelope; it does not replace the proof
of the joint deletion budget.

**Conclusion of (P1).** Apply (P2) to the classes involving only `{3,5,7,11}`.
For any missing small prime use an unused coordinate; this does not add a
forbidden class, and the same head bound applies. Apply one step of (T6)
at `p=71`, choosing `δ=53/200` and initial `G=C_4`, `s=1`, and then at
`p=73` with `δ=27/100`. The two successive denominators in (T6) are
`9580713200963/9867151936173` and
`47498911479243786341/48946254183902205216`, both positive. Exactly,

\[
 F_{71}=\frac{11578741637267351}{95807132009630},\qquad
 F_{73}=\frac{31280734730025808371666}{237494557396218931705}
 <\frac{138877}{1000}.
 \tag{P8}
\]

Either absent bridge prime may be an unused coordinate. Continue at prime 79,
with absolute prime index 22, using the checked upper seed
`F_21=138877/1000`. No prime from 13 through 67 needs to be inserted into
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
three-prime density theorem in [arXiv:2605.18644, Theorem 1.9](https://arxiv.org/abs/2605.18644)
do not directly cover (P1). The separately verified three-factors-per-modulus
theorem also has a different hypothesis: (P1) permits moduli divisible by four
or more primes. No dominating theorem was identified in this searched scope;
this is not a claim of literature priority. The theorem and its proof have
not been formalized in Lean.

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
open. The results are three exact obstacles to earlier proof routes, a direct
joint-load transfer into the BBMST continuation, and a quantitative reduction
of the arbitrary-height sufficient condition to a finite exponent cap. A
uniform four-prime head bound additionally proves the restricted noncoverage
theorem (P1), allowing arbitrary prime support at or above 71. The universal
finite-base bound needed for the full conjecture remains unproved. No new
Lean theorem, freeze, or problem-resolution binding is supplied.

## ASSUMED-UNVERIFIED

The external nine-prime result has no completed local kernel replay. The
three-factors-per-modulus theorem has the completed checks recorded in its
Library note, but `hThree` remains essential; its paper-only largest-prime-cutoff
extension is outside the Lean theorem. The joint-load transfer, exact finite
recurrence and restricted noncoverage theorem (P1) are proved above;
the universal Γ73 bound and the sufficient finite-base bounds remain unproved.
These mathematical arguments have not been formalized in Lean.
H73 is refuted and supplies no lower bound for Γ73. These finite checks do not
establish literature priority or an unrestricted proof or covering counterexample.

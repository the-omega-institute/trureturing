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
16 September 2026. This dossier and its finite experiments are not a proof.

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
of the arbitrary-height sufficient condition to a finite exponent cap. The
universal finite-base bound remains unproved. No new Lean theorem, freeze,
or problem-resolution binding is supplied.

## ASSUMED-UNVERIFIED

The external nine-prime result has no completed local kernel replay. The
three-factors-per-modulus theorem has the completed checks recorded in its
Library note, but `hThree` remains essential; its paper-only largest-prime-cutoff
extension is outside the Lean theorem. The joint-load transfer and exact finite recurrence are proved above;
the universal Γ73 bound and the sufficient finite-base bounds remain unproved.
These mathematical arguments have not been formalized in Lean.
H73 is refuted and supplies no lower bound for Γ73. These finite checks do not
establish literature priority or an unrestricted proof or covering counterexample.

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

The missing implication is an exponent-uniform bound that jointly controls
surviving mass and later conditional cylinder loads for an arbitrary
small-prime head. Higher-support cofactors and normalization after removal of
old mixed classes cannot be omitted. Three exact obstacles below exclude those
omissions and the proposed separate-cylinder head bound.

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
bound for `Γ_Q`. No new Γ73 numerical experiment is part of this result.

## Route

The proposed arbitrary-head transfer starts with mass one on **complete** old
survivors and extends each later prime-power coordinate uniformly before capped
distortion. It must first establish domination of the later law on arbitrary
head events times tail cylinders by the initial head measure and the relevant
tail-cylinder factor. For each fixed `(tail cofactor, current exponent)`, group
the actual head congruences into a load `A(x)`: at most one residue for each
head divisor occurs in that group. Completing this nonnegative load to a joint
choice in the definition of `Γ_Q` bounds `Eμ[A²]` by `Γ_Q(μ)`.
Cauchy–Schwarz then bounds cross terms between groups. The retained artifacts
do not certify this general-head transfer, including domination and propagation
of these estimates through every distortion step with total deleted mass
strictly below one.

In [BBMST's squarefree paper](../Library/Arith/balister2019erdos.md), the original
quantity is `f21 = c21(3)/mu21`; its denominator is essential. An arbitrary-head
version is a proposed derivable extension, not literal Corollary 5.2.
The [general distortion paper](../Library/Arith/balister2018covering.md) supplies
the background. Neither a free conditioning step nor finite success verifies
the transfer or the `138877/1000` continuation.

A rational convex mixture of joint residue layouts whose pointwise squared-load
lower bound exceeds `138877/1000` on an actual survivor family, with an explicit
survivor, would refute Γ73 only. Absence of a falsifier in a bounded search proves
no universal upper bound. The missing target is the universal, exponent-uniform
existence of a survivor measure satisfying the Γ73 bound. The refuted H73
condition is not a viable route to retune.

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
open. The mathematical results delivered here are three exact obstacles to
proposed proof routes; neither finite enumeration nor this dossier closes the
goal. No new Lean theorem, freeze, or problem-resolution binding is supplied.

## ASSUMED-UNVERIFIED

The external nine-prime result has no completed local kernel replay. The
three-factors-per-modulus theorem has the completed checks recorded in its
Library note, but `hThree` remains essential; its paper-only largest-prime-cutoff
extension is outside the Lean theorem. These retained artifacts do not certify
the general-head transfer or exact numerical continuation; Γ73 remains unproved.
H73 is refuted and supplies no lower bound for Γ73. These finite checks do not
establish literature priority or an unrestricted proof or covering counterexample.

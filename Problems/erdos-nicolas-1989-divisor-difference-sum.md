---
slug: erdos-nicolas-1989-divisor-difference-sum
bibkey: erdosnicolas1989functions
doi: null
url: https://oeis.org/A330076
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas
---

# Erdős–Nicolas reciprocal divisor differences

## Problem

P. Erdős and J.-L. Nicolas, “On functions connected with prime divisors of an integer”,
NATO ASI Series C **265** (1989), printed p. 390:

> We conjecture that for n > 5040, we have Ĥ(n) < τ(n).

Here `1 = d₁ < ⋯ < dτ(n) = n` are all positive divisors of the positive integer `n`,
and `Ĥ(n) = Σ_{1≤i<j≤τ(n)} 1/(dⱼ−dᵢ)`. The normalized quantity is
`h(n) = Ĥ(n)/τ(n)`. The conjecture concerns the unordered sum, rather than a
sum over consecutive divisors or a sum containing both orientations.

## Motivation

The theorem
`D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas`
has an unconditional type definitionally equal to `ErdosNicolasClaim`. In
`D5/S3/Arith/Divisors/ErdosNicolas/Basic`, that claim quantifies over every natural
`n > 5040`. No restriction on the order of prime exponents, a divisor-count cutoff,
or an unevaluated certificate proposition remains in the theorem's assumptions.

The strengthened induction tracks the exceptional integers themselves. It can
therefore supply strict bounds at the exceptions while retaining the exact source
threshold outside them.

## Gap

A reduction to integers whose prime exponents are nonincreasing would leave a real
gap: the proposed unnormalized canonical domination is false. The proof instead
classifies arbitrary prime factorizations and checks the resulting finite domains.

## Route

For `pᵃ∥n`, put `m=n/pᵃ`, `A=D(m)`, `B=pD(n/p)`, and `t=τ(m)`.
These are disjoint blocks of `D(n)` with sizes `t` and `at`.
The rational kernel `K(L,r)` equals `2/L-r/L²` for `r≤L` and `1/r` for `r>L`.
The nonnegative residual is `w(L,g)=(L-g)₊²/(L²g)` for positive `g`.
Thus `1/g=K(L,g)+w(L,g)`.

`TentKernel.kernel_psd` proves positive semidefiniteness by a finite discrete tent
expansion. Kernel Cauchy–Schwarz bounds the interaction of the two blocks. The
strict criterion `KernelCriterion.kernel_criterion_blocks` combines their internal
sums with a residual bound; it checks positivity of the remaining gap before
squaring. `KernelCriterion.kernel_criterion_prime_power` applies this criterion to
the actual divisor blocks, with no assumed PSD premise.

`Classification.good_of_finite_certificates` performs strong induction on the
positive integer. Its induction inputs are `n/p` and `n/pᵃ`, both positive and
strictly smaller. Two exponent-cutoff tables, maximum-prime cutoffs `677` and
`107`, and short modular chains leave six finite obligations: the base interval,
small exceptional lifts, large exceptional lifts, residue trees, the main exponent
box, and six extras. The imported `Data` modules discharge those obligations.
`Main.erdos_nicolas` supplies all six to the conditional theorem.

## Falsifier

The exact statement would be refuted by a positive `n>5040` with `Ĥ(n)≥τ(n)`.
Changing a strict comparison to a non-strict comparison, replacing all divisor
pairs by consecutive pairs, or restricting to canonical prime exponents changes
the target and cannot count as its resolution.

The failed domination route has an explicit counterexample. Put
`n=2¹⁰3⁴5³7⁴=24,893,568,000` and
`c=2¹⁰3⁴5⁴7³=17,781,120,000`. Both have `1100` divisors, but `Ĥ(n)>Ĥ(c)`. Since `τ(n)=τ(c)=1100`,
`h(n)>h(c)` also holds: domination of the normalized ratio fails as well.
This is a counterexample to that route, not to the Erdős–Nicolas conjecture.

## Evidence

The p. 390 source sentence is:

> We conjecture that for n > 5040, we have Ĥ(n) < τ(n).

The [primary-source note](../Library/QuadraticForms/erdosnicolas1989functions.md)
identifies the title, volume and printed page. Direct scan fidelity is unverified.

[Tenenbaum (1991)](../Library/QuadraticForms/tenenbaum1991hilbert.md),
“Une inégalité de Hilbert pour les diviseurs”, *Indagationes Mathematicae* **2**,
105–114, is related literature. The available attribution identifies Theorems 1
and 2 and §2, Lemma 1. Their exact hypotheses and conclusions have not been
verified against the Lean result; no theorem from that paper is an assumed input.

De la Bretèche (2000) is another literature lead for reciprocal divisor differences.
Its exact title, theorem statement, constants, and bibliographic locator are unverified. No claim of subsumption, prior resolution,
or mathematical dependence on that work is made.

A check through `2·10¹⁰` is attributed to Resta at
[OEIS A330076](https://oeis.org/A330076). This remains an attributed computation:
the OEIS revision, implementation, and coverage are unverified.
It does not serve as a premise or establish the universal theorem.

[Erdős Problem 884](https://www.erdosproblems.com/884) is a separate catalog target.
The proved target in this dossier is exactly the quoted p. 390 strict-threshold
statement. The catalog's complete statement and any stronger extremal or
asymptotic clauses remain unverified; the strict-threshold theorem does not settle
the entire catalog problem by identifying its number with the p. 390 sentence.

The exact checks use rational arithmetic for `h(7560)` and integer floor sums
`J(v)=Σ_{d<e; d,e|v} floor(10¹⁰/(e-d))` for the domination counterexample.

The output triples are `(24893568000, 1100, 1970990491357)` and
`(17781120000, 1100, 1970575235738)`. Each floor sum underestimates `10¹⁰Ĥ` by
less than `C(1100,2)=604450`. Hence
`0.0414651169 < Ĥ(n)-Ĥ(c) < 0.0415860069`.
The `7560` calculation gives `τ(7560)=64` and
`0.99275449 < h(7560) < 0.99275450`.

The experiment program is in the private repository
`the-omega-institute/trureturing-experiments` at
`experiments/erdos-nicolas-1989/h7560_pair_sums.py`
(commit `85d387d4909`, merged into `main`).

## Triage

`theorem`: the strict-threshold conjecture and the conditional exact classification.

### What the settlement shows

- **Proved:** the exact positive exception set is
  `E={12,24,60,120,180,240,360,420,720,840,1260,1680,2520,5040}`.
  `Classification.good_of_finite_certificates`, supplied with the six proved
  certificate propositions used by `Main.erdos_nicolas`, yields `Good(n)` for all
  positive `n`. By `Basic.Good`, its exceptional branch gives
  `1<h(n)<8/7`, and its other branch gives `h(n)<1`. Division is legitimate:
  for positive `n`, the divisor `1` ensures `τ(n)>0`. The displayed set has fourteen
  distinct elements. The conjunction and all six obligations are essential to
  this claim; the type of `Main.erdos_nicolas` alone records only `n>5040`.
- **Computed:** `h(7560)=0.9927544979498981…`, which rounds to `0.9928` at four
  decimal places, by the exact rational and integer-floor calculations in Evidence. This is one value; a claim
  that it is the global maximum outside `E` is **open**.
- **Computed:** canonical domination fails for both the unnormalized sum and
  the normalized ratio at the explicit pair above, since both divisor counts are `1100`. The integer-floor bounds in Evidence certify the positive gap. An extension of that
  counterexample to infinitely many exponents is **open**; it is not inferred
  from one finite counterexample.
- **Proved:** `TentKernel.kernel_psd` allows arbitrary finite indexed integer
  points, repeated points, and signed rational coefficients.
  `TentKernel.energy_sq_le` does not require disjointness. These general forms
  extend beyond divisor sets and can be used without rerunning the certificate
  search.
- **Proved:** `KernelCriterion.kernel_criterion_blocks` applies to arbitrary
  disjoint finite natural-point sets with the stated cardinality relation,
  internal bounds, and residual bound. Its extension to another arithmetic
  family requires those same hypotheses; no such application is claimed here.
- **Open:** sharper uniform bounds outside `E`, an optimum normalized constant,
  and new infinite families require additional estimates or certificates. No
  finite scan is promoted to those unbounded conclusions.
- **Unverified source consequence:** the complete set of statements in the 1989 paper and
  subsequent papers relying on this conjecture has not been verified. Only a statement whose sole missing hypothesis is the exact quoted
  conjecture can now discharge that hypothesis with the theorem; no other
  theorem or question of the source papers is declared settled here.

## ASSUMED-UNVERIFIED

Primary-source scan fidelity, complete literature priority, direct article DOIs,
the precise de la Bretèche result, the Resta computation and its OEIS revision,
and the complete relationship to Erdős Problem 884 require source verification.
The source locators in the Library notes are explicitly distinguished from direct
article retrieval. These limits affect attribution and comparison, not the
statement of the Lean theorem.

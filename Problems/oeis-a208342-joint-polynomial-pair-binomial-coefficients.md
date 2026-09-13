---
slug: oeis-a208342-joint-polynomial-pair-binomial-coefficients
bibkey: schulte2017a208342
doi: null
url: https://oeis.org/A208342
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients
---

# The A208342 coefficient formula for a jointly generated polynomial pair

## Problem

OEIS A208342, NAME:

> Triangle of coefficients of polynomials u(n,x) jointly generated with A208343; see the Formula section.

The defining FORMULA lines are:

> u(n,x) = u(n-1,x) + x*v(n-1,x),
>
> v(n,x) = x*u(n-1,x) + x*v(n-1,x),
>
> where u(1,x) = 1, v(1,x) = 1.

With `T(n,k) = [x^(k-1)] u(n,x)`, the conjecture is:

> T(n,k) = Sum_{j=0..floor((k-1)/2)} binomial(k-1-j,j)*binomial(n-k+j,j) for k,n>0 and k<=n (conjectured). - _Werner Schulte_, Mar 07 2017

## Motivation

The conjecture gives an explicit coefficient formula for every row of a
triangle defined only through a coupled polynomial recursion. Proving it
identifies both the finite support and the exact binomial weights for all
positive indices in the triangle.

## Gap

The preregistration search on 2026-09-13 read all 29 OEIS revisions and
searched arXiv (`all:A208342`), OpenAlex autocomplete, MathOverflow, and
GitHub code and issues. It also checked the exact string
`binomial(k-1-j,j)` and the Google Scholar results for the sequence number.
A proof was not found in the checked surfaces. GitHub code search returned
434 raw matches; only the joeis and loda hits were inspected, and they
implemented the recurrence but supplied no proof. The remaining matches were
not classified; the sampled ones were hexadecimal string coincidences, and no
count of that category was measured. The two Scholar results
were unrelated references rather than proofs of the conjecture.

## Route

Use simultaneous induction on the recursion stage for the coefficient pair
`(u,v)`. Alongside the conjectured closed form for `u`, maintain an explicit
companion closed form for `v`. The `u` step and the `v` step require two
different Pascal summation transformations. Natural binomial coefficients
outside their supported range vanish, which bounds both sums and reduces the
final coefficient sum to the conjectured upper limit.

## Falsifier

A positive pair `k,n` with `k<=n` for which the recursively generated
coefficient `[x^(k-1)] u(n,x)` differs from the stated binomial sum would
refute the theorem. A failure of either simultaneous induction invariant,
either Pascal transformation, or the claimed support cutoff would invalidate
the proof route.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.lean`.
- Main theorem: `schulte_a208342`.
- Public definitions: `coefficientPair`, `u`, `v`, and `T`.
- The theorem's axiom closure is std3: `propext`, `Classical.choice`, and
  `Quot.sound`.
- The orchestrator independently evaluated the exact polynomial recursion at
  every `1<=k<=n` for `n<30`, with zero mismatches.
- The probe evaluated both coefficient closed forms through `n<=200`, covering
  20,100 index pairs for each component, with zero mismatches.

## Triage

`theorem`. The Lean declaration proves the full unbounded coefficient formula
for every natural `n,k` satisfying `0<k<=n`.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish exhaustive coverage or
first-publication priority. The OEIS source text and attribution were checked
directly on 2026-09-13, but the source-to-Lean identification is not itself a
kernel-checked fact. The finite computations support the statement but do not
replace its universal proof.

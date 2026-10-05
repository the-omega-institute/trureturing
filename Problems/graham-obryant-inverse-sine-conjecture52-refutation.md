---
slug: graham-obryant-inverse-sine-conjecture52-refutation
bibkey: grahamobryant2005fourier
doi: 10.4064/aa118-3-4
url: https://mathweb.ucsd.edu/~ronspubs/05_02_fraenkel_tiling.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/GrahamObryantInverseSineRefutation.result
---

# Graham–O'Bryant Conjecture 5.2: ordinary residue-set refutation

## Problem

On printed page 302/PDF page 20, Graham and O'Bryant write:

> Suppose that p₁, …, pₙ are distinct and relatively prime to q > (7/4)ⁿ,
> with ∑ pₖ ≤ q, and for each k ∈ [n],
> 2/sin(π/q) ≤ ∑ᵢ₌₁ⁿ 1/|sin(π pₖ p̄ᵢ/q)|.
> Then q = 2ⁿ − 1 and {p₁, …, pₙ} ≡ {1, 2, …, 2ⁿ⁻¹} (mod q).

The quantifiers range over every positive integer n and q and every n-tuple
of distinct positive integer representatives coprime to q. The last set
contains all n powers 2⁰ through 2ⁿ⁻¹. The barred quantity is a modular
multiplicative inverse, and every complete row includes its diagonal.
The conclusion compares ordinary residue sets, without independent signs.

## Motivation

The source proposes the inverse-sine assertion as an auxiliary step toward
restricting counterexamples to Fraenkel's tiling conjecture. Absolute sine
loses signs of modular products, whereas the proposed ordinary set
conclusion retains them. The positive-lift sum bound is the remaining
constraint on those signs. The exact literal target and all-n family are
preregistered in [issue 13152](https://github.com/the-omega-institute/trureturing/issues/13152).

## Gap

The bounded source, citation, author-version, correction, repository and
all-state exact-target checks recorded in the preregistration found no
earlier settlement of this literal assertion. The inspected citation scope
comprised 18 records in 15 primary-work groups; neighbouring Beatty-covering
and complex-exponential assertions were distinguished by their hypotheses.
This is not an exhaustive semantic search or a claim of worldwide priority.

## Route

For every n>=3, take q=2ⁿ−1 and pᵢ=2ⁱ except for the final entry
pₙ₋₁=2ⁿ⁻¹−1. These are n positive, distinct units strictly below q, their
image has cardinality n, and their sum is q−1. Induction gives the strict
real threshold q>(7/4)ⁿ. The final entry is congruent to −2ⁿ⁻¹; explicit
signed-power inverses avoid any prime-modulus assumption. For every row,
i↦k−i modulo n permutes the exponents, and absolute sine erases the two
signs in each product. With x=π/q, the cotangent doubling identity
1/sin(2t)=cot(t)−cot(2t) telescopes over the shifted orbit; its final sine
is −sin(x). Restoring the first term gives exactly 2/sin(x) in every
complete row. All sine denominators are nonzero. The final positive entry
lies strictly between 2ⁿ⁻² and 2ⁿ⁻¹, hence is not a canonical power.

The complete universal construction is internal to the result proof and
precedes the conjecture assumption. Its n=3 specialization gives q=7 and
the ordinary set {1,2,3}, differing from {1,2,4}. There is one public
refutation, without a separately exported counterfamily or sign theorem.

## Falsifier

A proof of the literal assertion, with its full row and ordinary residue
conclusion, contradicts `D5/S3/Arith/GrahamObryantInverseSineRefutation.result`.
Changing the inverse to a real reciprocal, discarding the diagonal,
restricting q to primes, or quotienting the conclusion by signs changes
the assertion and does not answer this target.

## Evidence

The associated closed definition `claim : Prop` states the complete source
assertion. The closed theorem `result : Not claim` proves its refutation.
The internal all-n construction supplies every hypothesis, exact row
saturation, denominator nonvanishing, cardinality, and ordinary set
inequality before specialization. The axiom closure consists only of
`propext`, `Classical.choice`, and `Quot.sound`; no frozen D5 dependency is
used. The underlying known identities and normalization steps receive no
separate novelty claim. The result's provenance is a repository derivation
relative to the source assertion.

## Triage

`theorem`, with a `Refuted` resolution of the literal conjunction.

### What the settlement shows

- **Proved — GID `D5/S3/Arith/GrahamObryantInverseSineRefutation.result`:** The literal Graham–O'Bryant Conjecture 5.2 conjunction is false; the closed theorem proves `Not claim`.
- **Proved internally in GID `D5/S3/Arith/GrahamObryantInverseSineRefutation.result` — proof-local construction only, with no exported family theorem:** For every integer n≥3, take q=2ⁿ−1 and pᵢ=2ⁱ except pₙ₋₁=2ⁿ⁻¹−1. The construction has n positive, pairwise distinct units strictly below q, cardinality n, sum is q−1, and q>(7/4)ⁿ. For every row, the cyclic exponent permutation and the signed-power inverses give equality with 2/sin(π/q), all sine denominators are nonzero, and the ordinary residue set differs from {1,2,…,2ⁿ⁻¹}. These are proof-local facts used by the displayed GID; they are not a separately addressable counterfamily or sign theorem.
- **Mechanism:** Absolute sine erases the signs of modular products, so the ordinary residue-set conclusion cannot recover the canonical powers. Replacing the final lift 2ⁿ⁻¹ by q−2ⁿ⁻¹=2ⁿ⁻¹−1 lowers the sum by one, allowing the displayed family to satisfy sum=q−1 while violating the ordinary-set conclusion; the cyclic signed-doubling identity supplies the row equalities.
- **Open:** An unrestricted corrected classification with sum=q, a modulus-only conclusion under the original hypotheses, and a general classification up to independent signs remain separate questions; none is asserted as a repaired theorem. The construction is not a Beatty partition, does not refute the main Fraenkel conjecture, and does not settle the proposed modulus bound for genuine Fraenkel counterexamples. Conjecture 5.1 remains a different complex-exponential statement.
- **Source consequence (no additional theorem asserted):** The source's proved Fourier and covering results are unchanged. The auxiliary ordinary-set implication in Conjecture 5.2 fails, so the source's proposed use of the full conjecture requires a replacement argument.

## ASSUMED-UNVERIFIED

Worldwide absence of a previous settlement, exhaustive semantic coverage,
and publication priority are unverified. The original theorem source and
author version establish the statement, not its worldwide open status.
The named neighbouring repairs and the main Fraenkel conjecture remain
unresolved by this result.

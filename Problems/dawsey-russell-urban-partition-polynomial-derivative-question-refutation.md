---
slug: dawsey-russell-urban-partition-polynomial-derivative-question-refutation
bibkey: dawsey2022partitionpolynomial
doi: 10.48550/arXiv.2108.00943
url: https://cs.uwaterloo.ca/journals/JIS/VOL25/Dawsey/dawsey3.pdf
triage: theorem
motivation_gids:
  - D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.result
---

# Refutation of the printed partition-polynomial derivative question

## Problem

Dawsey, Russell, and Urban define the partition polynomial on printed page 2:

> To define this new polynomial, let λ = ⟨1^{m_1}, 2^{m_2}, . . . , k^{m_k}⟩ be a partition written in frequency notation. We define the partition polynomial f_λ by f_λ(x) = Σ_{i=1}^{k} m_i x^i. (1)

Printed page 9 gives the range convention and asks Question 9:

> For the following question, let lg(λ) denote the largest part of the partition λ, and recall that f_λ^{(d)}(x) = 0 for all d > lg(λ).
>
> **Question 9.** If λ, λ′ are any two unequal partitions, is it true that f_λ^{(d)}(1) ≠ f_{λ′}^{(d)}(1) for some positive integer d ≤ min{lg(λ), lg(λ′)}?

The formal `claim` follows these printed quantifiers: the two partitions may
have different sizes and lengths.

## Motivation

The question is a first-tier external open problem preregistered in issue
https://github.com/the-omega-institute/trureturing/issues/9046. Its literal
universal statement has a two-partition counterexample.

## Gap

`dominating_theorem_search: not-found-in-searched-scope`. The cited article
leaves Question 9 unanswered. The bounded literature search recorded in the
library note found no resolution among the article's citing Semantic Scholar
papers, the authors' listed later work, or MathDB searches by title, authors,
and partition-polynomial derivatives. Repository searches found no matching
D5 declaration, frozen owner, problem dossier, or Dawsey partition-polynomial
artifact. Pinned Mathlib supplies partitions and formal polynomial derivatives,
but no theorem settling the printed question was found in the searched scope.

The searched surfaces do not establish exhaustive publication absence, and no
publication-priority claim is made.

## Route

Take `λ = (1,1)` and `λ′ = (2)`. They are unequal partitions of 2, with
largest parts 1 and 2. Hence a positive integer satisfying
`d ≤ min{lg(λ), lg(λ′)}` must be `d = 1`. Definition (1) gives

```text
f_(1,1)(x) = 2x,       f_(2)(x) = x^2.
```

Their first derivatives have the same value at 1:

```text
f_(1,1)'(1) = 2,       f_(2)'(1) = 2.
```

No admissible derivative order distinguishes this pair, so the answer to the
printed Question 9 is no.

## Falsifier

A failure of either partition encoding, either largest-part calculation, or
either first-derivative value would invalidate the counterexample. A proof of
the printed universal claim would contradict the kernel-checked theorem
`result : Not claim`.

## Evidence

The canonical source is
`D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.lean`.
Its public declarations are `partitionPolynomial`, `largestPart`, `claim`, and
`result`. The frozen module state has statement identity
`sha256:e2ef2d0279596aba1483fbdddd69d6186d881d0b419e371a707bc834826c6dfd`.
The result declaration has statement identity
`sha256:5d688730f69eb1bf03cc8281a64af2cda12e91e555d8e7283c27c1fcccc03403`.
The Freeze event is
`sha256:2b777e48f0e2021e7a8a047d4e88b26e4eec25ee90f0867d00b83007ca539518`
and has no project-level frozen prerequisites; both direct imports are pinned
Mathlib modules.

The result is a closed typed refutation of `claim`. Its utility classification
is `certified-instance` with `basis=refutes` directed to that claim. The proof
uses no `sorry`, `native_decide`, or new axiom.

## Triage

`theorem`; resolution `refuted` for the quoted Question 9. The public theorem
has `proof_shape: bind-only` because it instantiates the claim at the two
partitions and closes the finite facts by normalization over pinned Mathlib.
`admission_basis: open-problem-resolution` under preregistration issue #9046;
`escape_witness: none`. There is no atom and no digestion coverage edge.

## ASSUMED-UNVERIFIED

The surrounding prose also discusses partitions having the same length and
size. The formal claim and this refutation do not assert that reading in either
direction. Exhaustive publication coverage and priority are
`ASSUMED-UNVERIFIED` and are not claimed. Source-to-Lean fidelity, proof shape,
and utility classification remain semantic review judgments separate from
kernel type checking.

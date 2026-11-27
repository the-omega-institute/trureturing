---
slug: nathanson-2026-problem-15-prescribed-intervals
bibkey: nathanson2026hbases
doi: null
url: https://arxiv.org/abs/2605.26425v3
triage: theorem
motivation_gids:
  - D5/S3/Arith/Additive/NathansonProblem15.nathanson_problem15
---

# Nathanson Problem 15 on prescribed intervals

## Problem

Melvyn B. Nathanson, *Problems in additive number theory, VII: The structure of additive h-bases for n*, arXiv:2605.26425v3, §5, Problem 15, asks whether for integers `h >= 2`, `q >= 2`, `n >= 1`, and `N_q >= n + 2`, and prescribed integers `c_1 < ... < c_q` with consecutive gaps at least `N_q`, there is a finite integer set `A` such that, for every integer `x`,

`[x, x+n] ⊆ hA` if and only if `x = c_i` for some `i`,

and, for every integer `x`,

`[x, x+1] ⊆ hA` if and only if `[x, x+1] ⊆ [c_i, c_i+n] ⊆ hA` for some `i`.

The question also asks for an estimate of the size of `A`. The settling theorem proves the bound `|A| <= 2*q*(n+1)`.

## Motivation

The source is [arXiv:2605.26425v3](https://arxiv.org/abs/2605.26425v3), §5, Problem 15, located at [Theoremproblem15](https://arxiv.org/html/2605.26425v3#Thmproblem15). The Lean index `i : Fin q` represents the source index `i.val + 1`. Pointwise scalar multiplication is the h-fold sumset with repetitions.

The construction uses two labelled generators for every prescribed point. It scales the signed radix code in base `h^2 + 1` by twice the remainder bound plus two, so sums with unequal codes differ by at least two. Sums differing by one must therefore share a code. They have distinct multiplicity arrays, and the collision forces their common code to be zero. Each zero-code array gives one prescribed point. The resulting finite generator set satisfies `Finset.card A <= 2*q*(n+1)`.

## Gap

The preregistration [issue #34976](https://github.com/the-omega-institute/trureturing/issues/34976) records the literal quantifiers, the source wording, the target cardinal bound, and the bounded pre-probe literature scope. The source's Theorem 7 treats a single prescribed interval for `h = 2`, while Problem 15 asks for both interval equivalences and a uniform finite-set estimate.

## Route

The settling declaration `D5/S3/Arith/Additive/NathansonProblem15.nathanson_problem15` has the exact quantified conclusion. It supplies a finite `A : Finset ℤ` with `A.card <= 2*q*(n+1)` and proves both equivalences over all integer `x`.

The first equivalence is

`∀ x : ℤ, (Set.Icc x (x + (n : ℤ)) ⊆ h • (A : Set ℤ) ↔ ∃ i : Fin q, x = c i)`.

The second equivalence is

`∀ x : ℤ, (Set.Icc x (x + 1) ⊆ h • (A : Set ℤ) ↔ ∃ i : Fin q, Set.Icc x (x + 1) ⊆ Set.Icc (c i) (c i + (n : ℤ)) ∧ Set.Icc (c i) (c i + (n : ℤ)) ⊆ h • (A : Set ℤ))`.

## Falsifier

For an admissible input, failure of either equivalence or of the cardinal bound for the constructed set would defeat that construction. Refuting the existential theorem would require an admissible input for which every finite candidate set violates the bound or at least one equivalence. The frozen Lean declaration is the formal truth anchor for the proposition recorded here.

## Evidence

- Frozen settling declaration: `D5/S3/Arith/Additive/NathansonProblem15.nathanson_problem15`.
- The declaration is kernel-checked with the standard axioms `Classical.choice`, `Quot.sound`, and `propext`.
- The source-bound registration is `Reg/D5/S3/Arith/Additive/NathansonProblem15.registration` through `Reg.D5.S3.Arith.Additive.NathansonProblem15.registration`, using the dependent-family readout for `h • (A : Set ℤ)`.
- The registration supplies the actual realization, equivalence bridge, variation witness, sensitivity, dependence, source selection, and `continuation := .unknown`.

## Triage

`theorem`; resolution `proved` for the full Problem 15 statement consisting of both exact interval equivalences and the bound `|A| <= 2*q*(n+1)`. The signed-radix mechanism and the adjacent-pair argument settle the prescribed-start and contained-unit-interval assertions simultaneously. The theorem does not claim a minimal cardinality, an optimal dependence on `N_q`, or a result outside the stated integer and parameter domain.

## ASSUMED-UNVERIFIED

The literature scope is bounded to the cited arXiv version and §5, the preregistration #34976, repository surfaces, and the cited later-work screens recorded in that issue. Exhaustive worldwide coverage, publication priority, and a minimal-cardinality result remain unverified.

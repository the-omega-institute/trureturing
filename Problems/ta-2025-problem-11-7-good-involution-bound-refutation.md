---
slug: ta-2025-problem-11-7-good-involution-bound-refutation
bibkey: ta2025goodinvolutions
doi: 10.48550/arXiv.2505.08090
url: https://arxiv.org/abs/2505.08090v5
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Groups/TaGoodInvolutionBoundRefutation.result
---

# Ta Problem 11.7: the good-involution bound need not be strict

## Problem

Lực Ta, *Good involutions of conjugation subquandles*, arXiv:2505.08090v5,
Problem 11.7 (printed page 27), asks:

> In the setting of Corollary 6.12, suppose that |Z(H)|, |X/H| ≥ 2 (so, in
> particular, Conj X is not connected). Is the upper bound on |Good(Conj X)|
> in Corollary 6.12 always strict?

Corollary 6.12 gives the bound
`|Good(Conj X)| <= min(|Aut(Conj X)|, |Z(H)|^(|X/H|))`.

## Motivation

The question asks whether the displayed upper bound is always a strict
inequality under the two lower bounds on the center and orbit count. A single
finite conjugation subquandle attaining the bound refutes that universal
strictness reading. Issue #9433 preregistered the verbatim question, its finite
group formal reading, and the literature check before implementation.

## Gap

The cited arXiv version presents Problem 11.7 as an open problem. The source,
its cited references, and the repository's bounded open-problem search did not
identify a prior settlement of this question. This bounded check does not
establish exhaustive publication coverage or priority.

## Route

Take `G = QuaternionGroup 2` and
`X = {QuaternionGroup.a 1, QuaternionGroup.a 3, QuaternionGroup.xa 0,
QuaternionGroup.xa 2}`, the subquandle `{±i, ±j}`. Its generated subgroup is
all of `Q8`, whose center has cardinality two. The two conjugation orbits are
`{a 1, a 3}` and `{xa 0, xa 2}`, so `orbitCount X = 2`. Kernel reduction gives
`Fintype.card (Good X h) = 4` and `Fintype.card (Aut X h) = 8`; hence the
right-hand bound is `min(8, 2^2) = 4`, attained rather than strict.

## Falsifier

The refutation would fail if the displayed finite subset were not closed under
conjugation, did not generate `Q8`, had a center or orbit count different from
two, or had either good-involution or automorphism cardinality different from
the certified values. Each condition is checked in the Lean proof.

## Evidence

`D5/S0/Certificates/Groups/TaGoodInvolutionBoundRefutation.result` is a
kernel-checked theorem of type `¬ claim`. The claim quantifies over finite
groups, finite subsets, closure proofs, and the two lower-bound hypotheses; the
finite witness therefore refutes the unrestricted question as formalized. The
result uses the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Triage

`theorem`; resolution `refuted` for the literal strictness question. The result
does not classify other subquandles, assert a corrected strictness theorem, or
make a claim about infinite cardinal arithmetic.

## ASSUMED-UNVERIFIED

The correspondence between the paper's rack terminology and the finite Lean
encoding is a source-faithfulness judgment, not a kernel theorem. The
literature search was bounded to the cited version, its references, and the
recorded repository search surfaces; exhaustive coverage and publication
priority remain unverified.

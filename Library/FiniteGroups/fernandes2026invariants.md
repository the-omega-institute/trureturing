---
bibkey: fernandes2026invariants
authors: Arthur Fernandes, Claudio Qureshi, Lucas Reis and Sávio Ribas
year: 2026
title: On a class of combinatorial group invariants
doi: 10.48550/arXiv.2609.20516
url: https://arxiv.org/html/2609.20516v1
claim: "Problem 6.2 asks for a partition strictly in one of three displayed intervals; the first is between group isomorphism and simultaneous integer-power equivalence."
strata_touched:
  - D5/S3/FiniteGroups/PowerInvariantRefinement
license: CC-BY-4.0
triage: anchor
---

# An intermediate finite-group invariant

Arthur Fernandes, Claudio Qureshi, Lucas Reis and Sávio Ribas,
*On a class of combinatorial group invariants*, arXiv:2609.20516v1.
The source is licensed under CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/). The quotation retains the
wording with mathematical typography normalized; no endorsement is implied.

## Verified locator

- DOI: 10.48550/arXiv.2609.20516.
- Primary URL: https://arxiv.org/html/2609.20516v1.

Problem 6.2, §6, HTML anchor `S6.Thmtheorem2`:

> Provide additional group invariants and determine their position relative to those presented in this paper. In other words, identify relations ∼ that generate a partition P on the set of finite groups such that P₁<P<P₂, P₂<P<P₅ or P₅<P<P₆.

Definition 1.5(1–2), anchors `S1.I1.i1` and `S1.I1.i2`, identifies P₁ with
group isomorphism and P₂ with existence of one bijection f such that
f(gⁿ)=f(g)ⁿ for every element g and every integer n. Remark 1.6,
`S1.Thmtheorem6`, distinguishes this simultaneous condition from separate
bijections for each exponent. The refinement paragraph `S1.SSx4.p4`
orders partitions by finer-to-coarser implication and passes to isomorphism
classes. The first displayed interval supplies the question's literal OR.
No statement about either other interval or Problems 6.1, 6.3 or 6.4 follows.

## Classical ingredients and the resulting relation

Intersect simultaneous power equivalence with agreement on abelianity.
This common-refinement operation is elementary. Alternating bilinear central
extensions of vector spaces and the center obstruction to isomorphism are
classical group theory. Source Lemma 3.1(i) and §6 (`S6.p6`) already discuss
same-order prime-exponent power equivalence. Matt Larson, *Power maps in
finite groups*, Integers 19 (2019), A58, §5, p.14, likewise gives the
abelian/nonabelian order-27 example, citing Cameron–Ghosh (2011).
These ingredients are reused rather than claimed as new discoveries.

The native construction uses three groups on five copies of ZMod 3. The
alternating forms have ranks zero, two and four. Their powers agree under
the coordinate bijection, while abelianity separates ranks zero and two;
centers of orders 27 and 3 separate the two nonabelian groups. These are
witnesses to strictness of a relation defined on every actual finite group,
not a restriction of the domain to a finite catalog.

## Evidence boundary

The source-domain theorem is
`D5/S3/FiniteGroups/PowerInvariantRefinement.finite_source_endpoint`.
Its carrier bundle contains an arbitrary type, an actual Group structure
and a Finite instance. `isomorphism_invariant` transports the relation in
both arguments. The Blueprint supplies the parameter correspondence.
Global priority and completeness of the current correction/solution search
remain ASSUMED-UNVERIFIED. No worldwide novelty claim is made.

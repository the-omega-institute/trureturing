---
slug: gnp-2025-v4-question-8-20-dicke-extensions
bibkey: gnp2025dickeextensions
doi: 10.48550/arXiv.2509.15201
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.result
---

# GNP arXiv v4 Question 8.20: Dicke extension cones

## Problem

Gulati, Nechita and Park, *Positive maps and extendibility hierarchies from
copositive matrices*, [arXiv:2509.15201v4, Question 8.20](https://arxiv.org/html/2509.15201v4#S8.Thmtheorem20), asks:

> For mixtures of Dicke states, are the following two sets equivalent?

$$
\mathsf{PPTBExt}_{n}^{(\mathcal K_r)}
=\mathsf{PPTBExt}_{n}^{(r-1)},\qquad r\ge2.
$$

The target is exactly this versioned question. For every integer $n\ge1$,
$r\ge2$ and every real upper-triangular family $Y_{ij}\ge0$, put

$$
D_{ii}=e_i\otimes e_i,\qquad
D_{ij}=\frac{e_i\otimes e_j+e_j\otimes e_i}{\sqrt2}\quad(i<j),\qquad
\rho=\sum_{1\le i\le j\le n}Y_{ij}|D_{ij}\rangle\langle D_{ij}|.
$$

The star predicate is existence of $E\succeq0$ on $(\mathbb C^n)^{\otimes r}$
with $(I\otimes\Pi_{r-1})E(I\otimes\Pi_{r-1})=E$, every root-leaf marginal
$\rho$, and $E^{T_S}\succeq0$ for every nonempty proper register subset $S$.
The complete-graph predicate is existence of $F\succeq0$ on the same tensor
power with $\Pi_rF\Pi_r=F$, every two-register marginal $\rho$, and
$F^{T_S}\succeq0$ for every such $S$. Here $\Pi_k$ is the orthogonal projector
onto $\operatorname{Sym}^k(\mathbb C^n)$, marginals are genuine unnormalized
partial traces, and transposes use the standard tensor basis. The assertion is
equivalence of these predicates for every $n,r,Y$, including all-zero weights,
without trace normalization or invertibility.

The [Library note](../Library/Quantum/gnp2025dickeextensions.md) holds the source
identity and bounded source checks. The original
[preregistration](https://github.com/the-omega-institute/trureturing/issues/26251#issuecomment-6617097653)
fixes this event before execution; its tier is the first-tier short complete-proof
unit.

## Motivation

The settling declaration is
`D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.result`.
It equates the full star and complete-graph existence predicates, retaining the
same matrix witness in each implication. Finite tensor indices are functions
`Fin r -> Fin n`; the coefficient array observes only its upper triangle.
The result is relevant to comparing the two hierarchies on the whole Dicke cone,
rather than checking individual dimensions or selected weights.

## Gap

The source poses a star-to-complete implication. The reverse implication follows
from full Bose support and inclusion of the star edges. Full Bose support cannot
be assumed in the forward direction: it must follow from the actual positive
extension and the prescribed Dicke marginals. The bounded source checks found
no full prior resolution in their inspected scope. They do not establish
worldwide absence, priority or current journal wording.

## Route

The two-particle antisymmetric projector annihilates every Dicke vector. On
each root edge its expectation in the prescribed marginal is zero. Actual
partial-trace duality gives zero expectation for the corresponding projector
placed on the $r$-register tensor product. The frozen positive zero-weight support
face theorem implies its one-sided annihilation of $E$. Hence every root
transposition fixes every column of $E$.

Root transpositions generate all register permutations, so these columns lie in
the full symmetric subspace. The actual orthogonal permutation-average projector
and Hermiticity give $\Pi_rE\Pi_r=E$. Reindexing the complement factors of the
partial trace proves that all ordered edge marginals coincide. The complete
graph witness is the original $E$, so each original PPT inequality is retained.
Conversely full symmetric support implies the leaf-projector sandwich, and the
complete edge constraints include the star constraints.

The direct frozen support input is
`D5/S3/QuantumStates/ZeroWeightSupportFace.zero_weight_support_face`
(statement identity
`sha256:c21f5826b1569f02708c19839f076c2ce1484bce1cbb7dbe8279a52fd19c8092`).
The projector inputs are in
`D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor`;
actual marginal and transpose definitions reuse `PartialTraceMutualInformation`
and `SymmetricAbsolutePPTPureBound`. No separate surrogate extension or assumed
support bridge is introduced.

## Falsifier

A mismatch of even one quantifier, Dicke normalization, tensor marginal,
projector or PPT cut would invalidate the claimed correspondence. A proof with
strictly positive or normalized weights, only finitely many dimensions, a full
Bose premise on the star witness, or a restricted set of transpose cuts would
not settle this event. None is part of the public statement. The all-zero
operator, singular witnesses, $n=1$ and $r=2$ remain in scope. The theorem does
not assert that every Dicke operator has either extension.

## Evidence

The mathematical source is
[DickeExtension.lean](../D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.lean),
with its [canonical Blueprint](../Blueprint/D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.md).
The result's statement identity is
`sha256:6b785387e00ba31d45b4abe703cc448050276c1f3b42b619ce0fc8aa78735f68`.
The Scribe's `OpenProblemResolutionClaim` binds exactly this frozen result to
this dossier with kind `Proved`.

Every theorem helper and the result have `proof_shape: bind-only`; there is no
escape witness. The helpers have actual consumers in the result's live proof
closure. The terminal result uses `admission_basis: open-problem-resolution`
under the original preregistration, rather than claiming a new general support
theorem. Definitions express the actual tensor operators. Mathematical truth
comes from the compiled Lean declaration and its accepted axiom closure;
source fidelity and admission semantics also require independent review.

The retained [Reg source](../Reg/D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.lean)
contains the original telescope, actual star observation, source-law bridge,
positive law, rejected-law variation, whole-family sensitivity and observational
dependence. Its source-readout classification remains `declared_unresolved`,
with no certificate: `IE-C050 ClosedTruthReadout`, `unclassified_form`,
`source.dictionary_or_proof_coordinate`. The missing accepted
admissibility/binding classification and the original theorem are disclosed
through the [section 3.9 linked-issue exception](https://github.com/the-omega-institute/trureturing/issues/26251#issuecomment-6618255978).
This evidence is not a completed Reg audit.

## Triage

- **Mechanism — proved in the delivered result.** Positivity converts the zero
  antisymmetric marginal weight into column support. Permutation generation then
  supplies full Bose support. All edge equalities concern the same actual
  matrix, so the argument never combines separately realizable witnesses.
- **Whole event — proved by the compiled statement.** Every $n\ge1$, $r\ge2$
  and nonnegative unnormalized Dicke coefficient family is included, with zero
  and singular cases. No numerical extrapolation is used.
- **PPT preservation — proved in the delivered result.** Both implications keep
  the original witness; every nonempty proper cut inequality passes unchanged.
  The forward support argument itself does not use these inequalities or the
  redundant leaf-support premise. No separately retained generalization is
  asserted.
- **Hierarchy consequence — the exact source question.** The two extension
  cones agree on the specified Dicke cone at each common register count. This
  neither characterizes membership in that cone's extension sets nor makes all
  Dicke operators extendible.
- **Adjacent questions — unresolved here.** The broader comparison for arbitrary
  Bose marginals, Question 8.7, journal question wording and any additional
  theorem depending on those broader questions are outside this settlement.
  No downstream source theorem is claimed beyond the explicit Question 8.20
  equality.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide novelty or priority are unverified;
negative findings have exactly the bounded scope recorded in the Library note.
The current journal DOI is `10.1007/s00023-026-01763-3`. Only metadata, abstract
and a subscription preview were acquired; journal question-body characters
acquired are zero. No claim is made about that journal's question text or
solution status. The source-qualified resolution is exclusively
arXiv:2509.15201v4 Question 8.20. The Reg audit remains unfinished under the
linked exception above; `continuation := .unknown` means only an unknown
residual, not undecidability or inexhaustibility. Final independent reviews,
remote required checks and publication are separate obligations.

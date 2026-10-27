---
slug: gupta-2026-miura-residual-degree-conjecture-83
bibkey: gupta2026miuradegrees
doi: 10.48550/arXiv.2607.05567
url: https://arxiv.org/abs/2607.05567v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/MiuraResolution.result
---

# Gupta's uniform residual degree bound

## Problem

Chakshu Gupta, *One construction for the Miura-ori flip-graph degree sequence*, arXiv:2607.05567v3, Conjecture 8.3 (Degree bound), states: “For d ≥ 5 and every split (a,b) with a+b=d and a≤b, the remainder R_(a,b) has total degree at most d−3.” Lemma 8.2 identifies one bivariate polynomial on all m,n≥2d−1. Section 7, Lemma 7.3 identifies the remainder with the configurations whose minima do not all lie on one common boundary side. The source's splits have positive a and b.

The original question is preregistered in [issue #22211](https://github.com/the-omega-institute/trureturing/issues/22211), [preregistration](https://github.com/the-omega-institute/trureturing/issues/22211#issuecomment-6412152003).

### Statement echo

| Original clause | Formal counterpart |
| --- | --- |
| Every d≥5, positive a+b=d, a≤b | The complete telescope of `MiuraResidualCount.claim` |
| One rational bivariate polynomial before all dimensions | `∃ p : MvPolynomial (Fin 2) ℚ` precedes `∀ m n`; the witness is `MiuraPolynomialCoreSum.corePolynomial a b` |
| Total degree at most d−3 | `p.totalDegree ≤ d - 3` |
| Every m,n≥2d−1 | Both universal dimension binders and their original bounds |
| Every normalized integer unit-edge height function counted once | `Residual` on the complete function `Fin m × Fin n → ℤ`, normalized at the origin; `residualCount` is the cardinality of that proved finite set |
| Exactly a strict minima and b strict maxima | Separate exact cardinalities of `minima` and `maxima`, testing every existing physical neighbour |
| No single common physical side contains all minima | The negation of `∃ sd, AllOnSide ... sd`; corners belong to both incident sides |

No symmetry quotient, identification of orientations, assumed fiber cardinality or replacement counting object enters the claim. Zero-based `Fin` coordinates are sent to the source's one-based physical coordinates by adding one to each coordinate. All subtractions in the formal bounds are natural-number subtractions.

## Motivation

The settling declaration is `D5/S3/Combinatorics/Geometry/MiuraResolution.result : MiuraResidualCount.claim`. The source had already established polynomiality and the separable degree bound; its introduction leaves the nonseparable case open for d≥9. The delivered statement covers every original positive split and every dimension in Lemma 8.2's region.

## Gap

The missing general ingredient is a joint bound on the two actual frozen-run counts. Independent bounds in each variable do not imply the required total-degree bound. The proof supplies the strict joint bound on the same residual arrays used in the exact count and connects it to actual-core uniqueness and complete-function fibers.

## Route

Actual signed frozen-column deletion, and its transpose, preserve normalization, the separate strict extremum counts and membership of all minima on each individual physical side. Legal orthogonal deletions commute; overlapping and separated same-axis deletions satisfy the one-step diamond. `MiuraCanonicalJoint.joint_reduced_core_unique` joins arbitrary deletion choices and proves equality of the dependent pairs containing both dimensions and the entire integer function. No quotient is used.

`MiuraPartitionCore.residual_core_exists` reaches a bounded reduced actual core with both run counts positive. `MiuraPartitionCount.residualCoreEquiv` partitions the original residual class into its unique actual-core fibers, and `residual_count_eq_sum_fibers` gives their exact cardinality sum.

`MiuraFiberEquiv.core_positive_vectors_equiv` identifies each complete-function fiber with the product of positive row-run and column-run length vectors, at the original uniform threshold. Indexed expansion constructs the function, and geometric readback recovers all lengths and the same complete function. `MiuraResolution.fiber_card_eq_positive_vectors` transports these actual cardinalities.

For a core K, let u,v be its occupied row and column counts and r,s its positive frozen-run counts. Its contribution is the product of the positive-composition polynomials in m−u and n−v. `MiuraPolynomialRuns.joint_run_polynomial_eval` proves the exact evaluations, and `joint_run_polynomial_degree_le` bounds total degree by r+s−2. `MiuraEqualityClassification.residual_frozen_runs_strict` gives r+s≤d−1 for these residual cores. Its equality analysis forces all minima onto a common side or the exceptional d=4 case, both excluded by the original assumptions.

The single `corePolynomial a b` is the finite sum over all individual bounded actual cores. `MiuraPolynomialCoreSum.core_polynomial_degree_le` bounds its degree by d−3. `MiuraResolution.core_polynomial_counts_residual` gives every exact evaluation, and `result` combines these conclusions without changing the original count.

## Falsifier

A source-fidelity failure would include choosing a polynomial after the evaluation dimensions, identifying distinct height functions, counting only boundary extrema, assigning a corner to only one side, or replacing “no one common side” by an interior-minimum requirement. None is part of the formal definition. A counterexample to the mathematical claim would require an original positive split and residual counts incompatible with every single rational polynomial of total degree at most d−3 on the whole stated region. No finite enumeration is substituted for the universal proof.

## Evidence

The endpoint is `D5/S3/Combinatorics/Geometry/MiuraResolution.result`, with declaration statement ID `sha256:262f4057ff790e5b47a6e0778cb20e38881935772a92a56f00a9c2459b6e9aa1`. The three public endpoint declarations are bind-only compositions of their actual supporting proofs; they introduce no new escape witness. The live auxiliary uses and exact external endpoint have the authorized open-problem-resolution admission basis. All module headers retain `utility: none`.

The mathematical unit consists of 48 D5 modules with their 48 Blueprint Scribes. Its imported finite suppliers are attributed to Gupta's lab commit `0bf8c67f7f5a2e8d44fb88c19fb80337221bbc11`, subtree `8beb89d4466cb8551abc92d0405972edc2edf116`, under CC-BY-4.0. The retained license and attribution are in `docs/reports/miura-suppliers/`; the existing Library note supplies the verified DOI and exact v3 URL. Compiled axiom closure is confined to `Classical.choice`, `Quot.sound` and `propext`.

Escape registration remains unfinished under [issue #22211](https://github.com/the-omega-institute/trureturing/issues/22211). [The target-specific round 4 and endpoint disclosure](https://github.com/the-omega-institute/trureturing/issues/22211#issuecomment-6420396324) distinguishes the retained typed laws, equivalence bridges and available variation/sensitivity proofs from the missing evidence. [The additional 106 retained-target disclosure](https://github.com/the-omega-institute/trureturing/issues/22211#issuecomment-6425074535) names the remaining target scope. Target-specific whole-family variation/intervention, sensitivity, actual observational dependence, lawful source-bound template applications, source selection and raw-source reconstruction/binding evidence remain incomplete as specified there. The four early Reg roots have no green current Inspector claim because `MiuraSlabExtrema.registration_1` fails `contract.discovery:rigid_universes`. Partial typed attempts are retained; no complete registration or `declared_validated` state is claimed.

## Triage

### What the settlement shows

- **Proved:** the entire original uniform residual-polynomial assertion, including every positive ordered split with d≥5 and all m,n≥2d−1, by `MiuraResolution.result`.
- **Proved:** actual signed contraction and dependent reduced-core uniqueness, by `MiuraCoreResidual.contractAt_residual` and `MiuraCanonicalJoint.joint_reduced_core_unique`; the original functions retain their physical-side data.
- **Proved:** each original array belongs to exactly one actual-core fiber, and the original count is their sum, by `MiuraPartitionCount.residual_core_unique` and `residual_count_eq_sum_fibers` using `residualCoreEquiv`.
- **Proved:** each full-function fiber has the exact positive-vector product cardinality, by `MiuraFiberEquiv.core_positive_vectors_equiv` and `MiuraResolution.fiber_card_eq_positive_vectors`.
- **Proved:** the same finite core sum has the uniform evaluations and total degree at most d−3, by `MiuraResolution.core_polynomial_counts_residual` and `MiuraPolynomialCoreSum.core_polynomial_degree_le`. The strict joint-run estimate, rather than separate axis estimates, supplies the degree improvement.
- **Conditional paper consequence (paper argument):** the premise of the source's Proposition 8.4 is supplied for all d≥5, so its top-degree formula follows subject to the source's separate single-side and total-count results. Those total flip-graph counts and that proposition are not new Lean theorems in this unit.
- **Open in this Lean unit:** the source's sharper high region of Theorem 9.10, the source's thin-region corrections and Baxter-number observations, and external novelty beyond the bounded screen. The delivered uniform region is exactly the original Lemma 8.2 region required for Conjecture 8.3.

### Literature status

The bounded publication screen checks the exact v3 source, the current authenticated `origin/dev` Problems/Library/geometry paths, the branch's PR state and matching issue/PR searches for the source and Conjecture 8.3. It identifies the owning issue #22211 and the separate existing Gupta dispersion dossier; it supplies no global absence assertion. The v3 source itself still labels the nonseparable general case open. Literature completeness is **ASSUMED-UNVERIFIED**.

## ASSUMED-UNVERIFIED

The bounded duplicate/literature screen is not exhaustive. The source's origami correspondence and its separate total-count consequences remain external to this exact height-function theorem. Full registration audits remain unfinished under the linked issue. Canonical frozen membership and the typed resolution claim do not substitute for independent source-fidelity review, exact-head required CI, or merge verification.

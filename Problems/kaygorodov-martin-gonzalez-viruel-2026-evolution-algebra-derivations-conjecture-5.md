---
slug: kaygorodov-martin-gonzalez-viruel-2026-evolution-algebra-derivations-conjecture-5
bibkey: kaygorodov2026evolutionsurvey
doi: 10.48550/arXiv.2610.22248
url: https://arxiv.org/abs/2610.22248v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.result
---

# Kaygorodov–Martín González–Viruel Conjecture 5

## Problem

Kaygorodov, Martín González and Viruel, *Evolution algebras: a survey of results and a list of open problems*, arXiv:2610.22248v1, state Conjecture 5: if an evolution algebra is finite-dimensional over an algebraically closed field of characteristic zero and its derivation algebra is semisimple, then the derivation algebra is a finite direct sum of orthogonal Lie algebras $\mathfrak{so}_{m_i}$ with $m_i\geq 3$. The empty sum is allowed.

The source's Section 1.1 defines an evolution algebra by a natural basis whose distinct basis vectors multiply to zero. Proposition 14 realizes the orthogonal summands; its converse realization assertion is not separately formalized here.

### Statement echo

The public `claim` in `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.lean` preserves the source's field, algebraic-closedness, characteristic-zero, finite-dimensionality, natural-basis, semisimplicity and finite direct-sum clauses. The public `result` proves that literal proposition.

## Motivation

The classification identifies the semisimple derivation algebras that can occur for finite-dimensional evolution algebras and excludes simple factors outside the orthogonal family, including the source's motivating examples $\mathfrak{sl}_3$ and $\mathfrak{g}_2$.

## Gap

Issue #18575 preregistered the conjecture before the Lean delivery. The issue records the source reading, the prior partial block-form result in arXiv:2303.00862v1 §5, the source's open status, and the bounded literature screen. Completeness beyond that inspected scope is `ASSUMED-UNVERIFIED`.

## Route

The proof has four structural steps. The annihilator obstruction shows that semisimplicity forces nonzero natural squares. Proportional-square blocks and the Leibniz equations identify derivations with independent pointwise stabilizers of projected square spaces; perfectness removes the block diagonal scalars. For a nondegenerate symmetric form, restriction to the orthogonal subspace modulo its restricted radical is surjective and has nilpotent kernel. Semisimplicity kills that kernel, leaving a standard orthogonal Lie algebra. Factors of dimension zero or one vanish, while the dimension-two orthogonal algebra is nonzero abelian and therefore cannot occur in a semisimple derivation algebra.

The delivered imports are `DerivationAnnihilatorObstruction`, `OrthogonalPointwiseStabilizers` and `NondegenerateDerivationBlocks`; the settling declaration is `SemisimpleDerivationClassification.result`.

## Falsifier

A counterexample would be a finite-dimensional evolution algebra over an algebraically closed characteristic-zero field whose semisimple derivation algebra has a simple ideal not isomorphic to any $\mathfrak{so}_m$, or a failure of one of the annihilator, block, stabilizer or assembly implications. The formal result is the positive classification under the stated hypotheses.

## Evidence

The canonical source is `D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification.lean`; its public settlement declarations are `claim` and `result`. The four delivered modules have frozen state records under `Golden/Frozen/state/D5/S3/QuadraticForms/`; the settling state records `result` as its motivation GID. The kernel axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The source is cited through `Library/QuadraticForms/kaygorodov2026evolution.md`, which is the existing DOI owner for `10.48550/arXiv.2610.22248`.

The numerical check is published in the experiments repository at commit `8c5c2dac91c0fb8ef0d7f2bd7d1684840643a2bf`, path `docs/reports/kaygorodov-martin-gonzalez-viruel-2026-semisimple-evolution-derivations/check.py`. The command `python3 check.py` exits `0`; the script SHA-256 is `eee00bd480df31d3321b618868b8c6f4106abdb59c26fac674a0008488249dd4`. Its scope is 3,598 valid numerical samples, including 1,911 semisimple samples and 674 nonzero semisimple derivation algebras; no sample with a zero square had a nonzero semisimple derivation. These floating-point SVD readings support the route and are not used in the Lean proof.

## Triage

| Item | Status | Evidence and boundary |
| --- | --- | --- |
| Exact KMV-1 necessity classification. | proved | Kernel-checked by `SemisimpleDerivationClassification.result`, with the full source proposition shown by the Scribe result node. |
| M2 works over every field for finite-dimensional commutative bilinear algebras in its annihilator-or-square form. | proved | Kernel-checked by `DerivationAnnihilatorObstruction.Annihilator.semisimple_ann_or_perfect` and its consumed construction. |
| M3 eliminates diagonals through commutator coordinates and perfectness, without division by block dimensions. | proved | Kernel-checked by `NondegenerateDerivationBlocks.Normalized.semisimple_diagonal_zero` and `Decomposition.productToDerivations_surjective`. |
| M4 needs trivial solvable radical, with a nilpotent restriction kernel and explicit surjective quotient map. | proved | Kernel-checked by `OrthogonalPointwiseStabilizers.Stabilizer.quotientKernel_nilpotent`, `Stabilizer.quotientLieHom_surjective` and `Stabilizer.stabilizer_equiv_of_trivialRadical`. |
| Numerical SVD check. | computed | `python3 check.py`, exit `0`, SHA-256 `eee00bd480df31d3321b618868b8c6f4106abdb59c26fac674a0008488249dd4`, scope 3,598 valid samples, 1,911 semisimple and 674 nonzero semisimple samples. |
| Converse realization assertion from Proposition 14. | open | Read in the source and retained as a boundary; no separate Lean declaration is delivered. |
| Separate non-isomorphism corollaries excluding $\mathfrak{sl}_3$ or $\mathfrak{g}_2$. | open | The classification implies the exclusion, but no separate corollary is formalized. |
| New-to-literature settlement, canonical admission, whole-repository health and completed four-slot escape audit. | open | Literature completeness is `ASSUMED-UNVERIFIED`; the escape audit is unfinished under issue #19944; no whole-repository claim is made. |
| Module split, Scribes and audit work under the authorized tracked scope. | open | The four modules, Scribes, emitted Markdown and four frozen state records are present; the four-slot audit remains unfinished under issue #19944. |
| Attributed and unread literature screens. | open | The bounded screen is recorded in issue #18575; completeness beyond the inspected sources remains `ASSUMED-UNVERIFIED`. |
| Potential non-algebraically-closed forms. | open | They require a new statement and separate normalization analysis; no such extension is claimed. |

### What the settlement shows

The decisive mechanism is the chain from annihilator obstruction to proportional-square block decomposition, perfectness, and the nilpotent stabilizer kernel. Under the source hypotheses this yields exactly the finite direct sums of $\mathfrak{so}_m$ with $m\geq3$. The proof covers the full abstract field and finite-dimensional vector-space formulation used in the source; it does not formalize the converse realization assertion, separate exclusion corollaries, non-algebraically-closed variants or a complete worldwide literature claim.

The source's semisimple part of Question 36 is thereby answered in the necessity direction. Proposition 14 remains the source's realization direction and is outside this module's formalized surface.

## ASSUMED-UNVERIFIED

The Lean kernel verifies the delivered propositions and their standard axiom closure. The source correspondence, the completeness and priority of the bounded literature screen, and the unfinished four-slot escape audit remain `ASSUMED-UNVERIFIED` or open as stated above.

---
slug: koljancic-oblak-2026-question-5-11-even-loop-path
bibkey: koljancic2026nssp
doi: 10.48550/arXiv.2604.21552
url: https://arxiv.org/abs/2604.21552v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.claim
---

# Even double paths with a nonempty loop set allow nSSP

## Problem

Koljančić–Oblak Question 5.11 asks whether every positive even order n and every nonempty loop set L on the double path admit a real nSSP matrix with exactly that pattern. Both orientations of every consecutive path edge occur, and only the loops at vertices in L are added. The final witness has no sign, symmetry, trace, spectrum or genericity restriction. The real test matrix X is unrestricted; the defining equations are entrywise A times X equal to zero and A times transpose X minus transpose X times A equal to zero.

The exact Lean proposition is `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.claim`. Unit #25129, preregistration comment 6554378006, owns this event. The companion `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPathNSSP.result` has this exact proposition as its type. Both mathematical hosts are frozen. The result proves the full event stated here.

The source is Sara Koljančić and Polona Oblak, *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*, arXiv:2604.21552v1, Question 5.11, with Definitions 1.1, 1.3 and 1.5 fixing nSSP, allowing a pattern and double-path loops. The later Electronic Journal of Linear Algebra publication, volume 42, pages 755–779, DOI 10.13001/ela.2026.10523, states Question 5.11 on PDF page 22, printed page 776. The linked Library note owns the source and license correspondence.

For every natural n with 0 < n and Even n, and every nonempty finite set L of vertices in Fin n, there exists a real matrix A indexed by Fin n whose nonzero entries are exactly the two orientations of consecutive path edges and the diagonal entries selected by L. For every real matrix X on the same indices, A ∘ X = 0 together with A * Xᵀ − Xᵀ * A = 0 implies X = 0. Here ∘ is the entrywise product. This includes n = 2 and singleton endpoint loops; no restriction on X or extra premise on A is added to the event.

## Motivation

The frozen recurrence and matrix relations connect local branch information to the unrestricted nSSP test. An exact-support witness for every nonempty loop set requires both a one-loop construction at any vertex and a support enlargement that preserves injectivity.

## Gap

The final result discharges the coprime-branch, spectral, support and openness conditions used inside its proof, so none remains a hypothesis of the full event. The remaining source-owner audit gaps are the nine unfinished registrations detailed in Evidence. Odd orders and empty loop sets lie outside this theorem, and literature priority is not asserted.

## Route

Choose a single loop in L, construct a symmetric weighted path with that loop, and enlarge the exact support after establishing nSSP. The sufficient one-loop construction uses coprime branch characteristic polynomials and an injective coefficient variation. The branch recurrence recovery theorem handles the last step of recovering internal edge variations from two consecutive zero branch variations, including empty and length-one branches.

The zero-diagonal branch characteristic correspondence and the algebraic constant/linear perturbation coefficients are supplied by `weighted_path_charpoly` and `continuant_linearization`. The theorem `coprime_positive_branches` supplies strictly positive squared-edge sequences with coprime continuants for every pair of branch lengths with odd sum, including zero and one lengths. Its parameter resultant is nonzero at zero, and a positive parameter outside its finite root set supplies the branches. The theorem `joined_variation_injective` recovers the central loop variation and every edge variation from the coefficient of the simultaneous algebraic joined perturbation. It uses the complete six-term product rule, reflection parity, strict degree bounds and two coprime separations, then consumes `branch_variation_injective`. The theorem `joined_path_charpoly` supplies the actual central-loop characteristic identity uniformly in all real weights and all natural branch lengths, including empty branches and endpoints. Its literal matrix has the loop at vertex r, left edges in increasing sequence order from the far endpoint, and right edges in decreasing order from the loop. It equals the joined algebraic expression with squared weights. The theorem `joined_path_charpoly_derivative` identifies every evaluated actual characteristic derivative along arbitrary edge and central-loop perturbations with the full joined variation, using squared-edge variations twice the weight times its variation. The owning Blueprint gives a conditional application to every unrestricted real commutant. With nonzero used weights, a nonzero central loop, odd total branch length, coprime branch continuants and a real orthogonal diagonalization with distinct spectral entries, every symmetric support tangent is represented by r+s+1 edge and loop parameters. Its spectral-diagonal readout is injective by the actual evaluated derivative and joined recovery, hence surjective by equality of finite dimensions. An unrestricted commuting test matrix becomes diagonal in that spectral basis; entrywise annihilation makes it orthogonal in trace to every support tangent. Surjectivity then pairs it with its own spectral diagonal, so the trace is a sum of squares and the test matrix vanishes. A separate characteristic-coefficient or adjugate interface is unnecessary for this route. The companion result discharges these intermediate assumptions. The original `GibbsStochasticSimpleSpectrum.jacobi_simple` supplies simple spectrum for the actual Jacobi matrix, and the Hermitian spectral theorem supplies its real orthogonal eigenbasis. Taking positive square roots of the coprime squared-edge parameters yields the real edges. An entrywise proof gives exactly the singleton-loop support, uniformly in both branch lengths.

For arbitrary nonempty L, choose a vertex l in L and use branch lengths l.val and n-1-l.val; even n makes their sum odd. The nSSP test map sends an unrestricted matrix X to the pair of its entrywise product with A and the transpose commutator. It is linear in X and continuous as a family in A. The set of injective continuous linear maps on a finite-dimensional domain is open. Add a sufficiently small positive value at precisely the other loops of L: each new loop is nonzero, the selected loop and every edge are unchanged, and all other entries stay zero. This proves the complete exact-support event. It does not require similarity preservation from the published Superpattern Lemma.

## Falsifier

A counterexample would be a positive even order and nonempty loop set for which no exact-support real witness has nSSP. Failure of a chosen symmetric construction is not such a counterexample. Completion requires a kernel-checked proof of the unchanged full claim with an admissible axiom closure and matching source exposition. A recurrence milestone, finite enumeration, one-loop-only theorem or source citation is insufficient.

## Evidence

### Declaration scope

| Declaration | Proof shape | Mathematical role |
| --- | --- | --- |
| `continuant_linearization` | content | Simultaneous polynomial perturbation, proved by induction with the complete coefficient-one product rule. |
| `branch_variation_injective` | content | Reverse recurrence recovers every edge variation from two consecutive zero observations. |
| `weighted_path_charpoly` | content | Actual weighted-branch characteristic polynomial, using the frozen `ForbiddenNeighbourDeterminant.det_sparse_front` and induction. |
| `joined_variation_injective` | content | Full central-loop perturbation coefficient recovers the loop and both complete branch edge variations; conditional on nonzero parameters, odd total branch length and coprime continuants. |
| `coprime_positive_branches` | content | Uniform positive branch construction by a nonzero parameter resultant and finite root avoidance. |
| `joined_path_charpoly` | content | Actual central-loop matrix characteristic polynomial, uniformly in both branch lengths and all real weights; consumed by `joined_path_charpoly_derivative` and its source-owner audit family. |
| `joined_path_charpoly_derivative` | content | Actual evaluated characteristic derivative under arbitrary edge and loop perturbations, with squared-edge variations `2*b*db`; consumed by the companion unrestricted-commutant proof and its source-owner audit family. |
| `KoljancicOblakEvenPathNSSP.result` | bind-only synthesis relative to the seven retained content relations and pinned/frozen suppliers | Exact all-positive-even/all-nonempty-loop-set event; `open-problem-resolution#25129` admission. |
| private `continuant_coeff` | content | Fixed leading coefficient and upper support bound; consumed by variation recovery. |
| private `variation_coeff` | content | Strict upper support bound for variations; consumed by variation recovery. |

Private `continuant_derivative` is a content inductive differentiation of the branch recurrence, consumed by `joined_path_charpoly_derivative`. Private `continuant_front` is a content recurrence identity consumed by `joined_path_charpoly`. Private `joined_endpoint_charpoly` is a bind-only helper applying the existing sparse determinant and branch characteristic results; it is consumed by `joined_path_charpoly` and supplies no admission basis. The definition `joinedPath` is consumed by that theorem. Private `variation_degree` and `branch_parity` establish the strict variation degree bound and reflection law used by central recovery; both are content. Private `parameter_map` and `even_constant` are content recurrence identities used by the positive coprime construction. Private `positive_coprime_right` is its consumed content construction step. Private `zero_continuant` directly applies `weighted_path_charpoly` to zero weights and normalizes the zero-matrix characteristic polynomial. It is consumed by `positive_coprime_right`. Private `continuant_monic`, `coprime_separation` and `zero_continuant`, together with the public consumed helper `joined_linearization`, are bind-only helpers on the live paths of the new content theorems; they supply no independent admission basis. The definitions introduce the exact event, recurrence, algebraic perturbations and matrix carriers. Their consumers are the proposition `claim`, the seven mathematical declarations and their source-owner audit families. The G module's admission basis is the substantive recurrence and matrix bridges (`escape-witness`). The I companion result has `open-problem-resolution#25129` admission for the unchanged preregistered event. Its synthesis is bind-only relative to the seven retained content relations and pinned/frozen suppliers. All its helper theorems are consumed on the result’s live proof path; the spectral, support and openness assembly supplies no separate escape-witness admission. The results are uniform algebraic statements, not certified finite instances, enumeration, numerical reductions or checkers. The source-owner audit families retain the full telescopes and intervention, sensitivity and observational-dependence obligations. The joined-recovery, coprime, joined-matrix characteristic and tangent registrations lack a compiled source-selection correspondence for their composite/existential states; their registrations are unfinished and no validated binding is asserted. The concrete gaps belong to existing issue #25129 under the registration exception. The new full-event result has its own faithful dependent-family attempt in `Reg/D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPathNSSP.lean`: parameters are every natural order, states are every loop set at that order, and readouts are sets of exact-support matrices. Its Law retains the full event, its actual/rejected variation and sensitivity are proved, and two loop sets give distinct observations. Its source-selection correspondence is absent; this attempt is unfinished and no validated binding is claimed. There are nine newly authored public theorem/lemma audit targets: eight compiled attempts remain `declared_unresolved`, with zero `declared_validated` records for this unit; the ninth target, public consumed helper `joined_linearization`, has no registration attempt, record or template verdict. Its absence is not an executed `source.selection_missing` result. It is used by `joined_variation_injective` and the companion's `joined_path_nssp_of_diagonalization`, and supplies no independent admission basis.

| Public audit target | Current audit evidence |
| --- | --- |
| `continuant_linearization` | Attempt compiled; `source.residual_requires_open`; unfinished. |
| `branch_variation_injective` | Attempt compiled; `source.residual_requires_open`; unfinished. |
| `weighted_path_charpoly` | Attempt compiled; `source.residual_requires_open`; unfinished. |
| `joined_variation_injective` | Attempt compiled; `source.selection_missing`; unfinished. |
| `coprime_positive_branches` | Attempt compiled; `source.selection_missing`; unfinished. |
| `joined_path_charpoly` | Attempt compiled; `source.selection_missing`; unfinished. |
| `joined_path_charpoly_derivative` | Attempt compiled; `source.selection_missing`; unfinished. |
| `KoljancicOblakEvenPathNSSP.result` | Attempt compiled; `source.selection_missing`; unfinished. |
| `joined_linearization` | Missing registration; no attempt, record or template verdict. |

All nine unfinished audits are disclosed under CLAUDE.md §3.9 at https://github.com/the-omega-institute/trureturing/issues/25129#issuecomment-6558078579 . This linked-issue exception permits mathematical delivery and does not assert audit completion.

## Triage

The retained exact result is an existential theorem for every positive even order and every nonempty loop set, with every real test matrix included. The proof selects structured witnesses; the event itself adds no structural assumption. No mathematical bridge remains as a hypothesis of the final theorem. Source-bound audit completion remains outstanding under the linked-issue exception in CLAUDE.md §3.9. The theorem does not settle odd orders or the empty-loop-set question.

## ASSUMED-UNVERIFIED

Source and license correspondence are in `Library/Eigenstructure/koljancic2026nssp.md`. No global priority or exhaustive nonresolution claim is made.

Exhaustive literature completeness, worldwide nonresolution and global priority are not established. The authenticated arXiv source carries CC BY-SA 4.0; the publisher edition’s separate reuse license is unverified. The nine source-bound audits remain unfinished under the linked-issue exception, separately from the frozen mathematical proof. This theorem supplies no conclusion for odd orders or empty loop sets.

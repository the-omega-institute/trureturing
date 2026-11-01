---
slug: koljancic-oblak-2026-question-5-11-even-loop-path
bibkey: koljancic2026nssp
doi: 10.48550/arXiv.2604.21552
url: https://arxiv.org/abs/2604.21552v1
triage: open
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.claim
---

## Exact event

Koljančić–Oblak Question 5.11 asks whether every positive even order n and every nonempty loop set L on the double path admit a real nSSP matrix with exactly that pattern. Both orientations of every consecutive path edge occur, and only the loops at vertices in L are added. The final witness has no sign, symmetry, trace, spectrum or genericity restriction. The real test matrix X is unrestricted; the defining equations are entrywise A times X equal to zero and A times transpose X minus transpose X times A equal to zero.

The exact Lean proposition is `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.claim`. Unit #25129, preregistration comment 6554378006, owns this event. No theorem in this module currently proves the proposition.

## Mathematical route and remaining obligations

Choose a single loop in L, construct a symmetric weighted path with that loop, and enlarge the exact support after establishing nSSP. The sufficient one-loop construction uses coprime branch characteristic polynomials and an injective coefficient variation. The branch recurrence recovery theorem handles the last step of recovering internal edge variations from two consecutive zero branch variations, including empty and length-one branches.

The zero-diagonal branch characteristic correspondence and the algebraic constant/linear perturbation coefficients are supplied by `weighted_path_charpoly` and `continuant_linearization`. The theorem `coprime_positive_branches` supplies strictly positive squared-edge sequences with coprime continuants for every pair of branch lengths with odd sum, including zero and one lengths. Its parameter resultant is nonzero at zero, and a positive parameter outside its finite root set supplies the branches. The theorem `joined_variation_injective` recovers the central loop variation and every edge variation from the coefficient of the simultaneous algebraic joined perturbation. It uses the complete six-term product rule, reflection parity, strict degree bounds and two coprime separations, then consumes `branch_variation_injective`. The central-loop determinant identity for the actual matrix, actual support-tangent correspondence, coefficient/adjugate trace pairing, unrestricted real commutant connection and exact support enlargement remain separate proof obligations. A conditional theorem assuming any of these missing relations does not settle the event.

## Declaration scope

| Declaration | Proof shape | Mathematical role |
| --- | --- | --- |
| `continuant_linearization` | content | Simultaneous polynomial perturbation, proved by induction with the complete coefficient-one product rule. |
| `branch_variation_injective` | content | Reverse recurrence recovers every edge variation from two consecutive zero observations. |
| `weighted_path_charpoly` | content | Actual weighted-branch characteristic polynomial, using the frozen `ForbiddenNeighbourDeterminant.det_sparse_front` and induction. |
| `joined_variation_injective` | content | Full central-loop perturbation coefficient recovers the loop and both complete branch edge variations; conditional on nonzero parameters, odd total branch length and coprime continuants. |
| `coprime_positive_branches` | content | Uniform positive branch construction by a nonzero parameter resultant and finite root avoidance. |
| private `continuant_coeff` | content | Fixed leading coefficient and upper support bound; consumed by variation recovery. |
| private `variation_coeff` | content | Strict upper support bound for variations; consumed by variation recovery. |

Private `variation_degree` and `branch_parity` establish the strict variation degree bound and reflection law used by central recovery; both are content. Private `parameter_map`, `zero_continuant` and `even_constant` are content recurrence identities used by the positive coprime construction. Private `positive_coprime_right` is its consumed construction step. Private `continuant_monic`, `coprime_separation` and `joined_linearization` are bind-only helpers on the live paths of the new content theorems; they supply no independent admission basis. The definitions introduce the exact event, recurrence, algebraic perturbations and matrix carriers. Their consumers are the proposition `claim`, the five mathematical declarations and their source-owner audit families. The module's proposed admission basis is the substantive recurrence and matrix bridges (`escape-witness`), subject to independent full-unit assessment. It does not claim an `open-problem-resolution` settlement of #25129. The results are uniform algebraic statements, not certified finite instances, enumeration, numerical reductions or checkers. The source-owner audit families retain the full telescopes and intervention, sensitivity and observational-dependence obligations. The joined and coprime registrations lack a compiled source-selection correspondence for their composite/existential states; their registrations are unfinished and no validated binding is asserted. The concrete gaps belong to existing issue #25129 under the registration exception.

## Falsifier and acceptance boundary

A counterexample would be a positive even order and nonempty loop set for which no exact-support real witness has nSSP. Failure of a chosen symmetric construction is not such a counterexample. Completion requires a kernel-checked proof of the unchanged full claim with an admissible axiom closure and matching source exposition. A recurrence milestone, finite enumeration, one-loop-only theorem or source citation is insufficient.

Source and license correspondence are in `Library/Eigenstructure/koljancic2026nssp.md`. No global priority or exhaustive nonresolution claim is made.

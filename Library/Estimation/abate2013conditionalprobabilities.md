---
bibkey: abate2013conditionalprobabilities
authors: Alessandro Abate; Frank Redig; Ilya Tkachev
year: 2013
title: On the effect of perturbation of conditional probabilities in total variation
doi: 10.1016/j.spl.2014.01.009
url: https://arxiv.org/abs/1311.3066v1
claim: The common-part and residual-product maximal coupling, including measurable kernel families in Section 3.2.
strata_touched: []
license: citation-only
triage: anchor
---

# Measurable maximal coupling

## Verified locator

- URL: https://arxiv.org/abs/1311.3066v1
- DOI: 10.1016/j.spl.2014.01.009
- Version: arXiv:1311.3066v1, math.PR.
- Title: On the effect of perturbation of conditional probabilities in total variation.
- Authors: Alessandro Abate, Frank Redig and Ilya Tkachev.
- Mathematical locator: Section 3.2, Definition 1 and the proof of Lemma 2.

The arXiv abstract page identifies this title, these authors and this version.
The versioned full text supplies the construction and the measurable-family step.

## Coupling construction and convention

Section 3.2, Definition 1 gives the coupling consisting of the diagonal image of
the common part and the normalized product of the two residual measures. The
proof of Lemma 2 explains that measurability of the family follows from measurable
positive and negative parts in a kernel Hahn--Jordan decomposition. For two
equal laws the residual has zero mass and the coupling is diagonal.

The paper's total-variation norm of the difference of two probability measures is
twice their event-supremum distance. The mismatch probability of a maximal
coupling is the event-supremum distance, which is the convention used by
`measurableTotalVariation`.

The private individual-law Lean proofs used by `MeasurableMaximalCoupling` follow
Jiyuan Tan's `TotalVariation.lean`, `Scheffe.lean` and `OverlapCoupling.lean` at
https://github.com/Jiyuan-Tan/CausalSmith/tree/a7085d88d2e4b30003db7097ca374f4718da0f01/Causalean/Stat/Minimax.
Their Apache-2.0 license, copyright and NOTICE are retained under
`docs/reports/licenses/causalsmith-maximal-coupling/`. Those individual-law proofs
are distinct from the measurable-family assembly and the conversion to the
repository's ENNReal event distance.

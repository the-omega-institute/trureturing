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

The actual weighted-path characteristic correspondence, uniform coprime branch construction, full central product-rule separation, support-tangent correspondence, coefficient/adjugate trace pairing, unrestricted real commutant connection and exact support enlargement remain separate proof obligations. A conditional theorem assuming any of these missing relations does not settle the event.

## Falsifier and acceptance boundary

A counterexample would be a positive even order and nonempty loop set for which no exact-support real witness has nSSP. Failure of a chosen symmetric construction is not such a counterexample. Completion requires a kernel-checked proof of the unchanged full claim with an admissible axiom closure and matching source exposition. A recurrence milestone, finite enumeration, one-loop-only theorem or source citation is insufficient.

Source and license correspondence are in `Library/Eigenstructure/koljancic2026nssp.md`. No global priority or exhaustive nonresolution claim is made.

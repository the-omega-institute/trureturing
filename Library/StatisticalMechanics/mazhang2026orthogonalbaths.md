---
bibkey: mazhang2026orthogonalbaths
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "Five Bose-selected modes with orthogonal bath projectors"
doi: null
url: "https://github.com/the-omega-institute/trureturing/issues/29093"
claim: "The supplied note constructs fixed orthogonal coordinate baths with five selected modes in every finite dimension at least five and proves open matrix sets; its actual GOE/GUE probability bridge remains outside the prepared Lean source."
strata_touched:
  - D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths
license: "CC BY 4.0 for the Ma–Zhang note; cited works retain their own terms."
triage: anchor
---
<!-- GID: D5/L/StatisticalMechanics/mazhang2026orthogonalbaths -->
# Fixed orthogonal bath projectors

Haobo Ma (ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National University
of Singapore; ChronoAI Pte Ltd, Singapore), 10 November 2026. This is a
continuation in the existing Schnell–Ketzmerick–Eckardt research family,
not a new counted paper or an independently established priority claim.
The URL locates the receiving issue, not a publication or acceptance record.

The complete three-page supplied PDF has SHA256
`846e57fdd424798b9f1e83d03e49bdc1e2c250f54111ce839f8982fc1d00b7c5`;
its TeX has SHA256
`0022ec412fa55d49a4f8a4381e72de348d765c063d61f2ed187eb8b84ca611d2`.
Source release 440890785 also supplies an exact finite checker. Its examples
in dimensions 6, 7, 8 and 20 do not prove the arbitrary-dimension theorem.

The model and strict selection condition are Schnell, Ketzmerick and
Eckardt, Physical Review E 97, 032136 (2018),
[arXiv:1802.04088v2](https://arxiv.org/abs/1802.04088v2), equations (11),
(49)–(55), Section V and Figure 7. The signed principal-Pfaffian method is
Knebel, Weber, Krüger and Frey, Nature Communications 6, 6977 (2015),
[arXiv:1504.07816v1](https://arxiv.org/abs/1504.07816v1), Methods equation (19).
The orthogonal witness and its finite-dimension extension belong to the
Ma–Zhang source, licensed [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

The actual canonical proof candidate covers all finite M≥5 over the real
and complex fields, rank-four selected blocks, global normalized uniqueness,
the intrinsic spectral-rate bridge, nonempty open matrix sets at exponent
three and a matrix-dependent local exponent neighborhood. It does not
identify the actual GOE or GUE laws, prove their full support, or formalize
the separate common interval |d−3|≤1/128 from the supplied uniform certificate.
The written probability argument and that interval must not be reported as
current Lean conclusions. No dimension-uniform neighborhood size, uniform
probability lower bound, seven-mode result or other physical-model result
is inferred. The earlier BS1–BS8 source record remains in scope with its
original domains and unresolved obligations.

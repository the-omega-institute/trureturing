---
bibkey: chiribella2009networks
authors: Giulio Chiribella; Giacomo M. D'Ariano; Paolo Perinotti
year: 2009
title: "Theoretical framework for quantum networks"
doi: 10.1103/PhysRevA.80.022339
url: https://arxiv.org/abs/0904.4483v2
claim: "Finite-dimensional quantum networks compose linearly in their channel slots, and quantum testers evaluate whole network outcome probabilities."
strata_touched: []
license: citation-only
triage: anchor
---

# Specified channel slots and adaptive output experiments

Sources: https://arxiv.org/abs/0904.4483v2 and
https://doi.org/10.1103/PhysRevA.80.022339.
Section II.A, PDF p. 2, explicitly fixes finite-dimensional Hilbert
spaces. Its linear-map/Choi correspondence and the link-product
composition in §II.B, Theorem 1, PDF p. 3, give the multilinear slot description. Section
IV.E, Definition 11, equation (66), PDF p. 17, defines testers through
$p(i\mid R)=\operatorname{Tr}(P_i^T R)$; Theorem 11 describes their
realization as a network followed by measurement.

[LocalClock, §十四, 假设25与定理26](../../docs/develop/theory/AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md)
uses this as the finite-dimensional precedent for a fixed adaptive
experiment. Its conditional memoryless-call contract is supplied
separately. The direct trace-class, operator-valued event-measure
induction there carries its stated separable-reference and measurable
outcome scope; the finite-dimensional theorem alone does not establish
that extension. A channel slot supplies neither an environment log nor
a coherently controlled dilation, and the citation supplies no native
FIB physical realization.

## Locator

- DOI: https://doi.org/10.1103/PhysRevA.80.022339
- arXiv v2 record: https://arxiv.org/abs/0904.4483v2

Scope: finite-dimensional channel-slot composition and quantum tester
probabilities, with the source locations and extension boundaries stated above.

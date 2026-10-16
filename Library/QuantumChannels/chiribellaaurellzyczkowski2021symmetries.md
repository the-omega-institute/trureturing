---
bibkey: chiribellaaurellzyczkowski2021symmetries
authors: Giulio Chiribella and Erik Aurell and Karol Życzkowski
year: 2021
title: Symmetries of quantum evolutions
doi: 10.1103/PhysRevResearch.3.033028
url: https://arxiv.org/abs/2101.04962
claim: "Section V.B conjectures that no symmetry of the full set of quantum channels reverses every unitary channel, without assuming reversal of composition order."
strata_touched:
  - D5/S3/QuantumChannels/ChannelTimeReversalNoGo
license: citation-only
triage: anchor
---

# Symmetries of quantum evolutions

## Verified locator

DOI: https://doi.org/10.1103/PhysRevResearch.3.033028

Source: https://arxiv.org/abs/2101.04962

The arXiv v5 PDF, Section V.B, page 7, states:

> An interesting open question is whether our no-go theorem remains valid for the subset of quantum channels. A no-go theorem for time reversal symmetries of quantum channels has been recently proven in Ref. [56], under the additional assumption that time reversal should reverse the order in which processes take place in any time sequence. We conjecture that this assumption can be lifted, and that the no-go theorem to time reversal applies also to symmetries of the set of quantum channels.

Definition 3, page 5, states:

> A symmetry transformation from the operation space Op(Hin , Hout ) to the operation space Op(Kin , Kout ) (an operation space symmetry, for short) is a bijective transformation S : Op(Hin , Hout ) → Op(Kin , Kout )

Its first requirement reads:

> is consistent with randomisations, namely S(p Q + (1−p) R) = p S(Q)+(1−p) S(R), for every pair of quantum operations Q and R, and for every probability p ∈ [0, 1]

The channel-set question uses this randomisation identity. The null-operation
requirement of Definition 3 has no instance among trace-preserving channels
in positive dimension.

Theorem 4 excludes both adjoint and transpose reversal for the full operation
set. Section V.A gives the positive time-symmetry result for bistochastic
channels; the conjecture concerns the full channel set.

The finite-dimensional encoding uses complex-linear matrix maps, the existing
IsCPTP predicate, conjugation X ↦ UXU†, and every dimension d ≥ 2.

---
bibkey: yang2018coherencebreaking
authors: Long-Mei Yang; Bin Chen; Tao Li; Shao-Ming Fei; Zhi-Xi Wang
year: 2018
title: "Amending Coherence-Breaking Channels via Unitary Operations"
doi: 10.1007/s10773-018-3890-4
url: https://arxiv.org/abs/1810.09642v1
claim: "A coherence-breaking channel maps every state to an incoherent state, and the coherence-breaking index n(Φ) is the least k with Φ^k coherence-breaking; the paper amends qubit channels with n(Φ) = 1, 2 by Λα ◦ Φ and Φ ◦ Λα ◦ Φ for unitary Λα, and conjectures that every d-dimensional channel with n(Φ) ≥ 2 is amended by Φ ◦ Λα ◦ ⋯ ◦ Λα ◦ Φ with n copies of Φ."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment
license: citation-only
triage: anchor
---

# Yang, Chen, Li, Fei and Wang, amending coherence-breaking channels

L.-M. Yang, B. Chen, T. Li, S.-M. Fei and Z.-X. Wang, *Amending Coherence-Breaking Channels via Unitary Operations*, Int. J. Theor. Phys. 57, 3776–3784 (2018), DOI 10.1007/s10773-018-3890-4; arXiv:1810.09642 [quant-ph] (v1, 23 October 2018, the only version).

## Verified locator

DOI: 10.1007/s10773-018-3890-4

Source: https://arxiv.org/abs/1810.09642v1. The text was read from the PDF.
- Page 2: incoherent channels, coherence-breaking channels and the index (1).
- Pages 4–6: Section 4, Lemmas 4.1–4.5 and Examples 4.1–4.2.
- Page 7: Section 5, the conjecture.

A later version with the same title appears as MiS Preprint 7/2019 (Max Planck Institute for Mathematics in the Sciences; authors Yang, Chen, Fei and Wang), https://www.mis.mpg.de/preprints/2019/preprint2019_7.pdf.

## Source statements

Section 2: "Any quantum channel Φ is called an incoherent channel if there exists a Kraus decomposition Φ(·) = Σ_i K_i(·)K_i† such that ρ_i = K_i(ρ)K_i†/Tr(K_i(ρ)K_i†) is incoherent for any incoherent state ρ. We call incoherent channel Φ a coherence-breaking channel (CBC) if Φ(ρ) is an incoherent state for any state ρ".

Eq. (1): "n(Φ) = min{k ≥ 1 : Φ^k is a coherence-breaking channel}."

Section 4: "Λα ◦ Φ is not a CBC, i.e., the channel Φ is amended."

Section 5: "In addition, for a d-dimensional quantum channel Φ with n(Φ) ≥ 2, one may conjecture that the channel Φ can also be amended by Φ ◦ Λα ◦ Φ ◦ · · · ◦ Φ ◦ Λα ◦ Φ [n Φ] with proper unitary operations Λα."

MiS Preprint 7/2019, Conclusions: "In addition, for a qudit quantum channel Φ, the channel Φ can be amended by Φ ◦ Λα ◦ · · · ◦ Λα ◦ Φ [n Φ] with proper unitary operations Λα when n(Φ) = n with n a positive integer." The preprint's proofs treat qubit channels only.

## Reading used by the repository

**Definitions.**
- An incoherent channel is given by Kraus operators, each mapping every basis vector to a multiple of a basis vector, which is the source's condition on basis states. The channel is trace preserving.
- A channel is coherence-breaking when it maps every density matrix to a diagonal one.

**The theorem.** For every such channel with n(Φ) = n ≥ 2, the repository proves that some unitary U makes Φ ◦ (Λ_U ◦ Φ)^{n−1} not coherence-breaking, with the same U in every slot. The proof gives one permutation unitary with fourth-root phases, and the same U works at every composition length.

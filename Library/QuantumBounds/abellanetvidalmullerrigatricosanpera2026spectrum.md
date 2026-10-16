---
bibkey: abellanetvidalmullerrigatricosanpera2026spectrum
authors: Jofre Abellanet-Vidal; Guillem Müller-Rigat; Albert Rico; Anna Sanpera
year: 2026
title: "Bounding the entanglement of a state from its spectrum"
doi: null
url: https://arxiv.org/abs/2604.02420v2
claim: "The negativity is N(ρ) = (||ρ^Γ||_1 − 1)/2 (Definition 2, Eq. (7)), and the reduction map is RED_κ(ρ) = Tr(ρ)1 − ρ/κ (Eq. (35)). Schmidt number at most χ implies N(ρ) ≤ (χ − 1)/2 (Lemma 3), and [1 ⊗ RED_κ](ρ) ≱ 0 implies Schmidt number greater than κ (Theorem 7). §5.4 leaves open whether NEGFS_{(χ−1)/2} ⊂ PREDFS_χ, and states that the inclusion is also unknown for the non-FS case."
strata_touched:
  - D5/S3/QuantumBounds/NegativityReductionInclusionRefutation
license: citation-only
triage: anchor
---

# Abellanet-Vidal, Müller-Rigat, Rico and Sanpera, bounding the entanglement of a state from its spectrum

J. Abellanet-Vidal, G. Müller-Rigat, A. Rico and A. Sanpera, *Bounding the entanglement of a state from its spectrum*, arXiv:2604.02420 [quant-ph] (v2 of 9 July 2026; v1 of 2 April 2026).

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2604.02420v2

No DOI or journal reference is listed in the arXiv metadata. The text was read from the PDF https://arxiv.org/pdf/2604.02420v2:
- p. 4: Definition 2, Eq. (7);
- p. 6: Definition 6;
- p. 10: Lemma 3;
- p. 11: §5.3, Eq. (35), Theorem 7, Definition 9;
- p. 12: §5.4, the open inclusion.

## Source statements

Definition 2 (p. 4): "The negativity N of a bipartite mixed state ρ ∈ B(C^N ⊗ C^M) is given by N(ρ) = (||ρ^Γ||_1 − 1)/2, (7) where ||A||_1 = Tr(√(A†A)) is the trace norm and Γ denotes the partial transpose of ρ with respect to any of the subsystems."

Lemma 3 (p. 10): "For any state ρ ∈ B(C^N ⊗ C^M) of Schmidt number at most χ, N(ρ) ≤ (χ − 1)/2."

§5.3 (p. 11): "Another useful tool to bound the SN is the reduction map: RED_κ(ρ) = Tr(ρ)1 − (1/κ)ρ (35) which is known to be a κ-positive but (κ + 1)-negative map". Theorem 7: "Given a state ρ ∈ B(C^N ⊗ C^M), if [1 ⊗ RED_κ](ρ) ≱ 0, (36) then SN(ρ) > κ."

§5.4 (p. 12): "Moreover, the complete inclusions of the considered EFS_γ sets is only pending for the unknown case NEGFS_{(χ−1)/2} ?⊂ PREDFS_χ, which is also unknown for the non-FS case."

## Reading used by the repository

The non-FS case compares the states ρ on C^N ⊗ C^M with N(ρ) = (χ − 1)/2 against those with [1 ⊗ RED_χ](ρ) = ρ_A ⊗ 1 − ρ/χ ≥ 0, for integers 1 ≤ χ ≤ min(N, M). The attained value makes the hypothesis stronger than the sublevel set N(ρ) ≤ (χ − 1)/2 of Lemma 3, so a counterexample at the attained value settles both readings. The FS sets of Definitions 6 and 9 add a quantifier over global unitaries, which is not used here.

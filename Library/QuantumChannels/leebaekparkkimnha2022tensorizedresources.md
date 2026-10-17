---
bibkey: leebaekparkkimnha2022tensorizedresources
authors: Jaehak Lee; Kyunghyun Baek; Jiyong Park; Jaewan Kim; Hyunchul Nha
year: 2022
title: "Fundamental limits on concentrating and preserving tensorized quantum resources"
doi: 10.1103/PhysRevResearch.4.043070
url: https://arxiv.org/abs/2104.12307v2
claim: "With the maximal coherence η(ρ) = max_{i≠j} |ρ_ij|/√(ρ_ii ρ_jj) of Eq. (15) and the output maximal coherence η̃(Φ) = max_ρ η(Φ(ρ)) of Eq. (28), the authors conjecture the tensorization property η̃(Φ₁ ⊗ Φ₂) = max{η̃(Φ₁), η̃(Φ₂)} (Conjecture 1, Eq. (29))."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation
license: citation-only
triage: anchor
---

# Lee, Baek, Park, Kim and Nha, limits on concentrating and preserving tensorized quantum resources

J. Lee, K. Baek, J. Park, J. Kim and H. Nha, *Fundamental limits on concentrating and preserving tensorized quantum resources*, Phys. Rev. Research **4**, 043070 (2022), DOI 10.1103/PhysRevResearch.4.043070; arXiv:2104.12307 [quant-ph] (v1 26 April 2021; v2 2 January 2024).

## Verified locator

DOI: 10.1103/PhysRevResearch.4.043070 (Crossref: Physical Review Research 4, article 043070, published 31 October 2022).
Primary version read: https://arxiv.org/abs/2104.12307v2; the text was read from the PDF.
- pages 5–6, §III.D: Eq. (15), the maximal coherence, with Theorem 4 on SIO distillation;
- page 6, §IV: Eq. (19), the output resource of a channel;
- page 7, §IV.B: Eqs. (28)–(29) and Conjecture 1;
- page 8: the numerical evidence of Fig. 3 and Conjecture 2.

The journal typesetting was not compared line by line.

## Source statements

§III.D: "Lami et al. introduced a measure called the maximal coherence [23], defined as η(ρ) = max_{i≠j} |ρ_ij| / √(ρ_ii ρ_jj), (15) which satisfies the monotonicity (C2c) under SIO. Also it obeys the tensorization property (C4)".

§IV.B: "We define the output maximal coherence of channels as η̃(Φ) = max_ρ {η(Φ(ρ))}. (28) We here make a conjecture on the tensorization property of η̃. Conjecture 1. The output maximal coherence of channels τ̃_m satisfies the tensorization property, that is, η̃(Φ₁ ⊗ Φ₂) = max{η̃(Φ₁), η̃(Φ₂)}. (29)"

Page 8: "Whether this conjecture holds true is not straightforward to see due to the optimization over all input states. However, we find a strong evidence to support this conjecture by conducting numerical calculations. For this purpose, we have generated pairs of random dynamical matrix (Choi matrix) … with the dimension of Hilbert space set as {d_A, d_B} = (a){2, 2}, (b){2, 3}".

## Reading used by the repository

The symbol τ̃_m in Conjecture 1 is a typo for η̃, as Eq. (29) shows. Channels are finite-dimensional completely positive trace-preserving maps, given by finite Kraus families, and Φ₁ ⊗ Φ₂ has the Kraus operators K ⊗ L. The maximum in Eq. (28) ranges over all density matrices, including entangled inputs of the product channel, and is read as a supremum. η is computed in the fixed computational basis over pairs i ≠ j with positive diagonal product, and is 0 when no such pair exists.

---
bibkey: salazar2025dephasing
authors: R. Salazar; F. Shahbeigi
year: 2025
title: "Dephasing noise simulation for coherence-generating devices"
doi: 10.1088/1402-4896/adda94
url: https://arxiv.org/abs/2403.19247v1
claim: "A dephasing superchannel multiplies Choi matrices entrywise by a Gram matrix C. The paper calls an implementation's memory passive when its marginal after encoding does not depend on the input. It proves that for qubit channels a passive memory realizes exactly the classical Gram matrices Σ q_i C₁⁽ⁱ⁾ ⊗ C₂⁽ⁱ⁾, and leaves open whether a passive memory is equivalent to a classical memory in every dimension."
strata_touched:
  - D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation
license: citation-only
triage: anchor
---

# Salazar and Shahbeigi, dephasing noise simulation for coherence-generating devices

R. Salazar and F. Shahbeigi, *Dephasing noise simulation for coherence-generating devices*, Phys. Scr. **100** (2025) 085110; arXiv:2403.19247v1 (28 March 2024; quant-ph).

## Verified locator

DOI: 10.1088/1402-4896/adda94 (open access; received 21 August 2024, published 31 July 2025).
Primary versions read: https://arxiv.org/abs/2403.19247v1 (the only arXiv version) and the journal PDF.
Source: https://arxiv.org/pdf/2403.19247v1 (text read from the PDF):
- Eq. (9), the implementation;
- Definition 2, passive memory;
- Proposition 1;
- §V.C, the open question;
- §V.D, the incoherent-memory argument.

## Source statements

Definition 2: "Whenever a superchannel implemented as in (9), has a memory: σ := Tr₁[N_en(ϱ ⊗ τ)], such that σ is always independent of the system's input ϱ, we say the superchannel's memory is passive and otherwise active."

Proposition 1: "Let Ξ_C be a dephasing superchannel acting on qubit channels with C being its associated 4 × 4 Gram matrix … Then, the following are equivalent: (i) Ξ_C can be realized employing some passive memory. (ii) C = Σ q_i C₁^{(i)} ⊗ C₂^{(i)}. (iii) C₀₁ has a fixed diagonal entry."

§V.C: "The above proposition proves that the noise imposed by a passive memory in the qubit case is realizable by applying some dephasing channels as pre- and post-processing chosen according to some classical memory. It remains open to prove if the same holds in higher dimensions as well, i.e., whether a passive memory in any dimension is equivalent to a classical memory."

§V.D: "Note, that taking ρ incoherent in (29), since N_en is MIO, the subsequent memory σ is also incoherent. Because σ is passive, the above holds for any ρ, and then the simulation must be equivalent to that of a classical memory i.e. C = Σ q_i C₁^{(i)} ⊗ C₂^{(i)}."

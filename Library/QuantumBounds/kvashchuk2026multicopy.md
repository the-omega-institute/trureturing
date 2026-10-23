---
bibkey: kvashchuk2026multicopy
authors: M. Kvashchuk, P. Chernyshova, L. E. A. Porto, T.-A. Ohst, L. B. Vieira, M. T. Quintino
year: 2026
title: "The most discriminable quantum states in the multicopy regime"
doi: null
url: https://arxiv.org/abs/2604.26927v3
claim: "Weighted state k-designs on N′(d,k) states, the smallest size admitting one, are used to build k-copy discriminable ensembles; with one extra state the paper adjoins the maximally mixed state. It asks (§12, question 4) whether this construction is optimal for N = N′(d,k) + 1 in every dimension, citing numerical evidence for qubits."
strata_touched:
  - D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation
license: citation-only
triage: anchor
---

# Kvashchuk et al., the most discriminable quantum states in the multicopy regime

M. Kvashchuk, P. Chernyshova, L. E. A. Porto, T.-A. Ohst, L. B. Vieira and M. T. Quintino, *The most discriminable quantum states in the multicopy regime*, arXiv:2604.26927v3 [quant-ph] (5 October 2026; v1 29 April 2026).

## Verified locator

Primary version read: https://arxiv.org/abs/2604.26927v3.
Source: https://arxiv.org/pdf/2604.26927v3 (text read from the PDF):
- §3.3, Definition 6 and the definition of N′(d,k) with bound (16);
- §11.2, the mixed-state construction;
- §12, open question 4;
- Figure 10, the value Ω^q(2,7,3) = 0.6429.

## Source statements

Definition 6: "We say that a set of N qudit states {ρ_i}_{i=1}^N is a weighted state k-design if there exists a probability distribution {p_i}_{i=1}^N such that Σ_{i=1}^N p_i ρ_i^{⊗k} = … = Π_sym(d,k)/Tr(Π_sym(d,k)), where ∀i p_i ≥ 0 is weight of a corresponding state, and when p_i > 0, ρ_i is a pure state."

§3.3: "Let us denote by N′(d,k) the smallest N such that a qudit state k-design exists."

§11.2: "While we do not have proof that this construction is optimal, for the qubit case we have numerical evidence that it is. We expect that, at least for d = 2, this construction may be optimal when N = N′(d,k) + 1, so it is large enough to contain a state k-design on N′(d,k) and one extra state."

§12, question 4: "For mixed states and N large enough to exactly contain a state k-design and only one more state, is the construction of the most discriminable k-copy states from a state k-design combined with the maximally mixed state optimal for any dimension? We have numerical evidence that it is true for qubits, but we do not have a proof of this fact."

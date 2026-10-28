---
bibkey: divincenzo2000exchange
authors: D. P. DiVincenzo; D. Bacon; J. Kempe; G. Burkard; K. B. Whaley
year: 2000
title: "Universal Quantum Computation with the Exchange Interaction"
doi: 10.1038/35042541
url: https://arxiv.org/abs/quant-ph/0005116
claim: "Exchange-only encoded quantum control is established background; a specified HS4 chirality readout is derived separately."
strata_touched:
  - D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum
license: citation-only
triage: anchor
---

## Source and scope

The [publisher abstract](https://www.nature.com/articles/35042541) and [arXiv abstract](https://arxiv.org/abs/quant-ph/0005116) describe universal encoded computation using the isotropic Heisenberg exchange interaction. The journal publication is Nature 408, 339-342, published 16 November 2000. The displayed interaction is pairwise. Encoding and circuit overhead are part of that result.

The [HS4 observable-closure companion](../../docs/develop/theory/HIGUCHI_SUDBERY_AURIC_NETWORK_CLOSURE.md) uses this as historical attribution for exchange-only control. Its own equations explicitly derive the four-qubit singlet restriction, signed control G=(S_AD-S_AC)/sqrt(3), one-pulse probability, and recorded-versus-averaged response. These formulas are not asserted to be the source paper's circuit, a new universal gate construction, or a hardware implementation.

Two independent issues must remain separate: a static two-local Hamiltonian cannot have the two-body-indistinguishable HS endpoint as a unique ground state; a controlled two-local evolution followed by a pair measurement can distinguish the endpoints. The static obstruction does not prohibit the latter task.

The reference does not identify FIB occupancy pulses with exchange edges or supply a quantum-network source decomposition. Those bridges require the separately declared carriers and exact hypotheses in the companion. Its new statements remain ordinary written proofs with Lean formalization open.

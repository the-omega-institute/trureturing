---
bibkey: marquezgonzalez2026feasibility
authors: Samuel A. Márquez González
year: 2026
title: "Feasibility Ordering of Entanglement-Source Placement for Qubit Channels"
doi: 10.48550/arXiv.2609.18803
url: https://arxiv.org/abs/2609.18803v1
claim: "Section VI, Eq. (47), asks whether every unital qudit channel is CP-filter equivalent to its channel transpose with CP inverses."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation
license: citation-only
triage: anchor
---

## Verified locator

- DOI: 10.48550/arXiv.2609.18803
- URL: https://arxiv.org/abs/2609.18803v1

# Feasibility Ordering of Entanglement-Source Placement for Qubit Channels

Samuel A. Márquez González, arXiv:2609.18803v1. Page numbers refer to the
printed PDF.

Page 2, Section II.A:

> Consider completely positive trace-preserving (CPTP) maps
> $\Lambda:\mathcal B(\mathbb C^2)\rightarrow\mathcal B(\mathbb C^2)$.

Pages 2–3, Section II.D, Eqs. (15)–(16):

> Fix a qubit basis. If a CP map has Kraus representation
> $\Lambda(X)=\sum_i K_i X K_i^\dagger$,
> its channel transpose is the CP map
> $\Lambda^T(X)=\sum_i K_i^T X\overline{K_i}$.

> This definition is independent of the chosen Kraus representation, although
> it depends on the underlying basis.

Page 5, Section VI, Eq. (47):

> This separates the higher-dimensional problem into two levels. The strong
> question is whether every unital qudit channel $\Upsilon$ is CP-filter
> equivalent to its transpose, i.e., whether there exist invertible CP maps
> $\mathcal L$ and $\mathcal R$, with CP inverses, such that
> $\Upsilon^T=\mathcal L\circ\Upsilon\circ\mathcal R$.

The dimension-three encoding uses complex linear maps on
`Matrix (Fin 3) (Fin 3) ℂ`. Complete positivity means positivity under every
finite matrix amplification. A CP inverse satisfies both composition
identities on every matrix. The standard-basis coefficient transpose agrees
with Eq. (16) for every finite Kraus representation. Trace duality and the
nondegenerate matrix trace pairing identify the Heisenberg map across Kraus
representations; transposing its value on $X^T$ identifies the channel
transpose. Trace preservation and
unitality mean preservation of matrix trace and of the identity matrix.

The strong question fails for a unital qutrit measure-and-prepare channel.
Its transpose has diagonal range, while its range contains two noncommuting
trace-one matrices. CP-invertible maps are invertible congruences; such a
congruence cannot make the entire unital noncommuting range diagonal.
The weaker positive/CP factorization in Eq. (48) remains open. The qubit
theorems and the source's feasibility conclusion are unaffected.

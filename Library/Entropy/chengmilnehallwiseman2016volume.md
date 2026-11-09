---
bibkey: chengmilnehallwiseman2016volume
authors: Shuming Cheng, Antony Milne, Michael J. W. Hall, Howard M. Wiseman
year: 2016
title: "Volume monogamy of quantum steering ellipsoids for multi-qubit systems"
doi: 10.1103/PhysRevA.94.042105
url: https://arxiv.org/abs/1606.02390v2
claim: "The paper proves volume monogamy relations for quantum steering ellipsoids of pure three- and four-qubit states and conjectures (Eq. (36)) that for all pure four-qubit states the squared Frobenius norms of the two-qubit correlation matrices of qubit A with B, C and D sum to at most 3."
strata_touched:
  - D5/S3/QuantumStates/FourQubitCorrelationMonogamy
license: citation-only
triage: anchor
---

# Cheng–Milne–Hall–Wiseman, volume monogamy of quantum steering ellipsoids

## Verified locator

DOI: 10.1103/PhysRevA.94.042105

Source: https://arxiv.org/abs/1606.02390v2

Phys. Rev. A 94, 042105 (2016).

S. Cheng, A. Milne, M. J. W. Hall and H. M. Wiseman, arXiv:1606.02390v2 [quant-ph] (7 October 2016, the latest version).

## Statement

The correlation matrix of a two-qubit state is $T_{jk}:=\operatorname{tr}[\rho_{AB}\,\sigma_j\otimes\sigma_k]$ for $j,k=1,2,3$, with $\boldsymbol\sigma=(\sigma_1,\sigma_2,\sigma_3)$ the Pauli matrices. After its inequality (35) the paper states:

> Finally, we conjecture that inequality (35) generalises to

$$\operatorname{Tr}[T_{AB}T_{AB}^{\top}]+\operatorname{Tr}[T_{AC}T_{AC}^{\top}]+\operatorname{Tr}[T_{AD}T_{AD}^{\top}]\le 3$$

> for all pure 4-qubit states.

## Encoding and boundary

Each correlation entry $\operatorname{tr}[\rho_{AX}\,\sigma_i\otimes\sigma_j]$ of the reduced state equals the expectation in the four-qubit state of the Pauli word with $\sigma_i$ on $A$, $\sigma_j$ on $X$ and identities elsewhere; the repository encodes the entries this way for normalized vectors in $(\mathbb C^2)^{\otimes4}$. The repository proves the conjectured bound by partitioning the 27 two-body Pauli words into three families of pairwise anticommuting involutions, each bounded by one through a variance argument. The volume monogamy relations of the source, extensions to more qubits and tightness statements are outside this conclusion.

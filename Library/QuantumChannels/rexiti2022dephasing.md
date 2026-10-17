---
bibkey: rexiti2022dephasing
authors: M. Rexiti; L. Memarzadeh; S. Mancini
year: 2022
title: "Discrimination of dephasing channels"
doi: 10.1088/1751-8121/ac6d2c
url: https://arxiv.org/abs/2201.00388
claim: "Section 7 conjectures that Kraus operators with identity polar unitaries give no benefit from side entanglement."
strata_touched:
  - D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation
license: citation-only
triage: anchor
---

# Discrimination of dephasing channels

Section 7, Concluding remarks, arXiv v2, printed pages 16–17:

> About the discrimination with side entanglement, it is worth observing the following: i) Side entanglement is very useful for Pauli channels [16]; ii) Side entanglement is partially useful for amplitude damping [6]; iii) Side entanglement is not useful for phase damping channel (present work). Then, we are led to conjecture that side entanglement is useful in channel discrimination if the Kraus operators of the channel admit a polar decomposition with non-trivial unitaries (i.e., not identities). Actually, if the Kraus operators are unitaries, then there is maximal benefit from side entanglement. In contrast, if all Kraus operators have simply the identity as unitary part in the polar decomposition, there is no benefit from side entanglement.

The formal claim isolates the negative clause for qubit channels, equal priors,
and a qubit ancilla. Strictly positive-definite Kraus operators have the identity
as their unique polar unitary. Kraus sums, positive-semidefinite effect conditions,
and success probabilities use the expressions recorded in issue #16535.

The counterexample has four positive tetrahedral Kraus operators for each of
parameters a=2 and a=3. Its unassisted success is at most 47/84, whereas the
Bell-assisted strategy achieves 33/56. This concerns the general extrapolation,
not the paper's theorem for its dephasing family.

## Verified locator

DOI: 10.1088/1751-8121/ac6d2c

Source: https://arxiv.org/abs/2201.00388

Version: https://arxiv.org/abs/2201.00388v2

Section 7, Concluding remarks, printed pages 16–17; J. Phys. A 55, 245301.

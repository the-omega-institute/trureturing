---
bibkey: mitrabadhanighosh2023switch
authors: A. Mitra; H. Badhani; S. Ghosh
year: 2023
title: "Improvement in quantum communication using quantum switch"
doi: 10.1088/1402-4896/acbcf7
url: https://arxiv.org/abs/2108.14001
claim: "Section III.B, Conjecture 1 asserts that concatenation of two completely useless channels is always completely useless."
strata_touched:
  - D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1088/1402-4896/acbcf7

Source: https://arxiv.org/abs/2108.14001

## Source statements

The arXiv v6 text, Section III.B, PDF p. 8, states:

> A useless channel is completely useless if under both C+ and C− it remains useless.

Conjecture 1, on the same page:

> Concatenation of two completely useless channels is always completely useless.

Section II.C, Eq. (8), PDF p. 4, decomposes the switched channel into
the anticommutator and commutator branches C₊ and C₋. Each branch has
Kraus operators (AₓAᵧ ± AᵧAₓ)/2, hence coefficient 1/4 in its action.
The branches are completely positive maps and need not preserve trace.
For entanglement transfer, uselessness means entanglement breaking.

## Encoding and scope

Qubit operators are complex matrices indexed by Fin 2. A finite Kraus
family is a channel when its sum of KᵢᴴKᵢ is the identity. Complete
uselessness requires entanglement breaking of the original map and both
switch branches. The concatenation places LⱼKᵢ at the index (i,j).
Entanglement breaking means that every positive amplified input has
separable output, using the repository's matrix-map predicate IsEB.

Two tilted dephasing–depolarizing channels at eta = 24/25 refute this
assertion: all six factor maps are entanglement breaking, but the minus
branch of their concatenation has a negative partial-transpose quadratic
value. This conclusion concerns entanglement transfer and does not assert
positive classical capacity or perfect deterministic transmission.

## Literature boundary

No answer was found in the six retrieved citing full texts and two
later-author full texts screened for this problem. Three other citing
full texts were unavailable after direct requests and Firecrawl HTTP 402.
Literature completeness and priority remain ASSUMED-UNVERIFIED.

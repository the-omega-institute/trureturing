---
bibkey: bravyi2026identitycheck
authors: Sergey Bravyi, Natalie Parham and Minh Tran
year: 2026
title: Identity Check Problem for Shallow Quantum Circuits
doi: 10.4230/LIPIcs.ITCS.2026.27
url: https://doi.org/10.4230/LIPIcs.ITCS.2026.27
claim: "Lemma 4 bounds unitary-channel diamond distance by the sum of amplified SWAP commutator norms up to a factor of 2/sqrt(3). The factor is one when the unitary-channel diamond distance is less than two."
strata_touched:
  - D5/S3/Quantum/ProcessReconstruction/RobustDiamond
  - D5/S3/Quantum/ProcessReconstruction/ExactConstantOne
  - D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry
license: citation-only
triage: anchor
---

# Identity Check Problem for Shallow Quantum Circuits

## Verified locator

LIPIcs 362, Article 27, §2, printed pp. 27:6–27:8.
[DOI](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). The proceedings PDF was read at
https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/LIPIcs.ITCS.2026.27/LIPIcs.ITCS.2026.27.pdf .

Lemma 4, Eqs. (6)–(8), uses the sum of amplified SWAP commutator norms
for a partition of qubit sites. Its proof in Eqs. (9)–(19) compares
that sum to the spectral diameter of the relative unitary. Below
diamond distance two, the diameter is the diamond distance. In the
remaining case, the spectral polygon contains the origin and includes
two points with chord length at least the square root of three.

The unscaled SWAP statistic can fall below the global diamond distance.
Take a partition with one two-qubit block and a unitary acting on that
block with eigenvalues 1, ω, ω² and 1, where ω is a
primitive cube root of unity. The spectral polygon contains zero and
its diameter is √3. Equation (6) gives √3 for this
partition and the global diamond distance is 2.

The formal reduced-output comparison applies the reference-amplified
dual test to each SWAP and bounds its operator-norm error by the
complete reduced-channel diamond error. Each tested channel accepts
the full input register. The site dimensions may differ.

Section 1.2, printed p. 27:5, asks for an efficient algorithm with
approximation ratio one plus any positive constant epsilon. The
algorithmic question concerns the identity check problem for shallow
circuits. The deterministic comparison using complete output
marginals addresses access to the reduced channels.

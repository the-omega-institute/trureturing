---
bibkey: tavakolibengtssongisinrenes2020siccompounds
authors: Armin Tavakoli; Ingemar Bengtsson; Nicolas Gisin; Joseph M. Renes
year: 2020
title: "Compounds of symmetric informationally complete measurements and their application in quantum key distribution"
doi: 10.1103/PhysRevResearch.2.043122
url: https://arxiv.org/abs/2007.01007v1
claim: "A SIC-compound is a set of d³ unit vectors in ℂ^d that splits into d SICs and into d² orthonormal bases; one exists for d = 2 and d = 4 and none for d = 3 with the Weyl–Heisenberg group, the introduction reports evidence against existence for d = 5, 6, 7, 8, and whether one can be formed from the exceptional (Hoggar) SICs of dimension 8 is left open."
strata_touched:
  - D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation
license: citation-only
triage: anchor
---

# Tavakoli, Bengtsson, Gisin and Renes, compounds of SICs

A. Tavakoli, I. Bengtsson, N. Gisin and J. M. Renes, *Compounds of symmetric informationally complete measurements and their application in quantum key distribution*, Phys. Rev. Research 2, 043122 (2020), DOI 10.1103/PhysRevResearch.2.043122; arXiv:2007.01007 [quant-ph] (v1 2 July 2020, the only version).

## Verified locator

DOI: 10.1103/PhysRevResearch.2.043122

Source: https://arxiv.org/abs/2007.01007v1; the text was read from the PDF.
- page 1: the abstract and the introduction, with Eq. (1) and properties I and II of a SIC-compound;
- pages 2–3: the paragraph "On existence in d = 5, 6, 7, 8", with the open question on the exceptional SICs of dimension 8.

## Source statements

Abstract: "A SIC-compound is defined to be a collection of d³ vectors in d-dimensional Hilbert space that can be partitioned in two different ways: into d SICs and into d² orthonormal bases. While a priori their existence may appear unlikely when d > 2, we surprisingly answer it in the positive through an explicit construction for d = 4."

Introduction: "We address the existence of SIC-compounds for d = 3, . . . , 8. For d = 3 we prove that no SIC-compound exists and for d = 5, 6, 7, 8 we give evidence in support of the same conclusion."

Eq. (1): "A SIC is a maximal set (size d²) of d-dimensional states, {|φ_k⟩}, with the property that the overlap between any pair of states has the same magnitude: |⟨φ_k|φ_l⟩|² = (dδ_{k,l} + 1)/(d + 1)".

Properties: "The resulting SIC-compound is a set of d³ pure d-dimensional quantum states, denoted {|ψ_jk⟩}_jk for j ∈ [d²] and k ∈ [d] … with the following two properties: I For every k, the states {|ψ_jk⟩}_j form a SIC. II For every j, the states {|ψ_jk⟩}_k form an orthonormal (ON) basis of Hilbert space."

On existence in d = 5, 6, 7, 8: "We find that the number of orthogonal SICs varies (2, 4, 2 and 5 respectively) and that no SIC-compound can be constructed. … However, as previously mentioned, dimension 8 also houses SICs that are not based on the WH group [3, 51, 52]. Whether a SIC-compound can be formed from these exceptional SICs is left as an open question."

References [3], [51] and [52] are S. G. Hoggar's construction, A. Szymusiak and W. Słomczyński on the informational power of the Hoggar SIC-POVM, and B. C. Stacey on sporadic SICs.

## Reading used by the repository

The exceptional SICs of dimension 8 are the Hoggar SICs, the orbits of a fiducial vector under the three-qubit Pauli group; the different fiducials give SICs equivalent up to unitary or antiunitary transformations (Stacey, arXiv:1609.03075). A compound formed from these SICs is given by eight vectors whose Pauli orbits are SICs and whose images under each Pauli operator form an orthonormal basis. The repository states the negative answer to the open question as a claim and refutes it.

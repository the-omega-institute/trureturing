---
bibkey: allen2017polynomialmonogamy
authors: Grant W. Allen; David A. Meyer
year: 2017
title: "Polynomial Monogamy Relations for Entanglement Negativity"
doi: 10.1103/PhysRevLett.118.080402
url: https://arxiv.org/abs/1502.04807v2
claim: "For three qubits the paper determines the region of achievable triples of squared negativities (N²_A|C, N²_A|B, N²_A|BC), with N(ρ) = ‖ρ^{T_A}‖₁ − 1, and describes it by the states d|000⟩ + a|101⟩ + b|110⟩ + c|111⟩; it generalizes them to the family (13) for D-dimensional qudits and conjectures that this family gives the entire achievable set for D > 2."
strata_touched:
  - D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation
license: citation-only
triage: anchor
---

# Allen and Meyer, polynomial monogamy relations for entanglement negativity

G. W. Allen and D. A. Meyer, *Polynomial Monogamy Relations for Entanglement Negativity*, Phys. Rev. Lett. 118, 080402 (2017), DOI 10.1103/PhysRevLett.118.080402; arXiv:1502.04807 [quant-ph] (v2).

## Verified locator

DOI: 10.1103/PhysRevLett.118.080402

Source: https://arxiv.org/abs/1502.04807v2; the text was read from the PDF.
- The negativity N(ρ) = ‖ρ^{T_A}‖₁ − 1.
- Eq. (13) and the following paragraph: the qudit family, its partial-transpose blocks and the conjecture.

## Source statements

Eq. (13): "|Ψ⟩ = d|000⟩ + Σ_{j=1}^{D−1} a|j0j⟩ + b|jj0⟩ + c|jjj⟩".

After Eq. (13): "Since this is a natural extension of the achievable region we found for D = 2, we conjecture that it is the entire achievable set of negativities, (N²_A|C, N²_A|B, N²_A|BC), for D > 2 as well."

## Reading used by the repository

For three qutrits, the repository takes the triple of negativities of the reduced states on AB and AC and of the pure state across A|BC. Negativities are nonnegative, so the squares in the source's triple do not affect equality of triples.

It refutes the claim that every unit vector has the triple of some normalized state of the family (13) with D = 3. The witness is (5|000⟩ + 3|101⟩ + |202⟩ + t|110⟩ + 5t|220⟩)/√(35 + 26t²) with t = 1/100.

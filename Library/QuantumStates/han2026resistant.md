---
bibkey: han2026resistant
authors: Zicheng Han; Wanchen Zhang; Xiande Zhang
year: 2026
title: "A five-qubit 1-resistant graph state and stabilizer marginal certificates"
doi: null
url: https://arxiv.org/abs/2606.08561v1
claim: "The Discussion asks whether C5 and C6 are strongly m-resistant for m=1 and m=2 respectively."
strata_touched:
  - D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation
license: citation-only
triage: anchor
---

# A five-qubit 1-resistant graph state and stabilizer marginal certificates

Page 8, Discussion:

> Several open problems remain. First, do C₅ and C₆ give strongly m-resistant graph states for m = 1 and m = 2, respectively? Here, “strong” means genuine multipartite entanglement rather than mere entanglement.

The two clauses concern genuine multipartite entanglement after every loss of
one and two qubits, respectively. The C₆ clause uses the strong-resistance
definition of Zhang et al., arXiv:2505.06567. On zero-based labels, its
amplitudes are (-1) raised to the sum of x_i x_(i+1 mod 6), divided by 8.
The C₅ clause remains open here.

Page 2, Section II.A:

> A mixed state ρ on H₁ ⊗ · · · ⊗ H_N is called fully separable if it can be written as

the displayed convex sum of products,

> where p_α ≥ 0, ∑_α p_α = 1, and each ρ_i^(α) is a one-particle density operator

Page 2, Section II.B:

> The graph state |G⟩ is obtained by preparing each qubit in

|+⟩ = (|0⟩ + |1⟩)/√2

> and applying a controlled-Z gate along each edge:

|G⟩ = (∏_{{u,v} ∈ E} CZ_uv)|+⟩^⊗N.

## Verified locator

- URL: https://arxiv.org/abs/2606.08561v1
- PDF: https://arxiv.org/pdf/2606.08561v1, page 8, Discussion;
  graph-state definition in Section II.B.

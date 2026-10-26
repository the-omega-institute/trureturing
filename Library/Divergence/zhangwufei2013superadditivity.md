---
bibkey: zhangwufei2013superadditivity
authors: Lin Zhang, Junde Wu, and Shao-Ming Fei
year: 2013
title: "Comment on 'Convergence of macrostates under reproducible processes' [Phys. Lett. A 374: 3715–3717 (2010)]"
doi: 10.1016/j.physleta.2013.05.047
url: https://arxiv.org/abs/1210.4720v4
claim: "Section 4, conjecture (4.2), asserts relative-entropy superadditivity after independent joint and local unitary conjugations for every full-ranked reference state."
strata_touched:
  - D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation
license: citation-only
triage: anchor
---

# Relative-entropy superadditivity after unitary conjugation

## Verified locator

DOI: https://doi.org/10.1016/j.physleta.2013.05.047

Source: https://arxiv.org/abs/1210.4720v4

Phys. Lett. A 377 (2013), 1794–1796. Section 4, p. 6 of the arXiv version,
states:

> Based on the above result, we propose the following conjecture: There exist unitary operators U_A ∈ U(H_A), U_B ∈ U(H_B) and U_AB ∈ U(H_A ⊗ H_B) such that S(U_AB ρ_AB U_AB† ‖ σ_AB) ⩾ S(U_A ρ_A U_A† ‖ σ_A) + S(U_B ρ_B U_B† ‖ σ_B), (4.2) where the reference state σ_AB is required to be full-ranked state. Indeed, our numerical calculations show that inequality (4.2) is true.

Here ρ_A and ρ_B are the actual partial traces of ρ_AB, and likewise for σ.
The Lean claim uses all finite dimensions and positive trace-one complex
matrices, with positive definiteness of σ_AB and three existential unitaries.
The relative entropy is the natural-logarithm trace expression.

The counterexample uses ρ = I/4 and σ = diag(61,1,1,1)/64. Its marginals are
I/2 and diag(31,1)/32. The input and its marginals are fixed by every unitary,
and the joint relative entropy minus the sum of the marginal relative entropies
is strictly negative.

---
bibkey: saied2025photondistillation
authors: Jason Saied, Jeffrey Marshall, Namit Anand, Eleanor G. Rieffel
year: 2025
title: "General protocols for the efficient distillation of indistinguishable photons"
doi: 10.1103/PhysRevApplied.23.034079
url: https://arxiv.org/abs/2404.14217v4
claim: "For n-photon distillation protocols built from an n × n unitary whose first row is identically 1/√n (for example the discrete Fourier transform), the ideal heralding rate is h_n(0) = (−1/n)^{n−1}(n − 1)! Σ_{t=0}^{n−1} (n − t)(−n)^t/t! (Theorem III.5, Eq. (III.9)), with lim h_n(0) = 1/4; the authors conjecture that for n ≥ 5 the sequence h_n(0) decreases monotonically to 1/4 (Conjecture III.7)."
strata_touched:
  - D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity
license: citation-only
triage: anchor
---

# Saied–Marshall–Anand–Rieffel, efficient distillation of indistinguishable photons

J. Saied, J. Marshall, N. Anand and E. G. Rieffel, *General protocols for the efficient distillation of indistinguishable photons*, Phys. Rev. Applied **23**, 034079 (2025), DOI 10.1103/PhysRevApplied.23.034079; arXiv:2404.14217 [quant-ph] (v4 26 March 2025).

## Verified locator

DOI: 10.1103/PhysRevApplied.23.034079 (as listed on the arXiv abstract page).
Primary version read: https://arxiv.org/abs/2404.14217v4 (the latest of versions v1–v4; the conjecture is numbered III.6 in v1–v3).
Source: https://arxiv.org/pdf/2404.14217v4 (text read from the PDF):
- §III.2, Theorems III.4 and III.5 with Eqs. (III.8)–(III.10), the heralding rate and its ideal value;
- Remark III.6 (the integer sequence n^{n−1}h_n(0), OEIS A277458), the first values, Figure 4 and Conjecture III.7.

## Source statements

Theorem III.5: "Let U = F(n₁, …, n_ℓ), where n = n₁⋯n_ℓ > 2. More generally, we may take U to be any n × n unitary with entries in the first row identically equal to 1/√n. 1. The ideal heralding rate has the following equivalent expressions: h_n(0) = (−1/n)^{n−1}(n − 1)! Σ_{t=0}^{n−1} (n − t)(−n)^t/t! (III.9) = ₂F₀(−(n − 1), 2; 1/n), (III.10) … 2. lim_{n→∞} h_n(0) = 1/4."

After Remark III.6: "The first few values are h₃(0) = 1/3, h₄(0) = 1/4, h₅(0) ≈ 0.264. In Figure 4, we plot the difference h_n(0) − 1/4 and numerically observe that h_n(0) quickly approaches 1/4, with asymptotic h_n(0) − 1/4 ∼ 1/(16n). In particular, we conjecture Conjecture III.7. For n ≥ 5, the sequence h_n(0) monotonically decreases to 1/4."

Figure 4 evaluates h_n(0) − 1/4 for every n from 5 to 10⁵ and for selected larger n up to 10⁷.

## Reading used by the repository

The conjecture is the statement about the sequence of Eq. (III.9): for every n ≥ 5, h_{n+1}(0) < h_n(0), and h_n(0) → 1/4. The repository takes Eq. (III.9) as the definition of the sequence, as the source's Theorem III.5 establishes it for every n > 2; it does not re-derive the formula from linear optics.

---
bibkey: lin2026rcqc
authors: Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang
year: 2026
title: "Nonclassicality of a delayed remote-controlled quantum computing model"
doi: 10.48550/arXiv.2606.31103
url: https://arxiv.org/abs/2606.31103v1
claim: "A delayed 1-U-M remote-controlled quantum computing circuit (a Bell pair on program and remote-control qubits, controlled gates A = diag(1, e^{i(β+δ)}) and B = [[0, −1], [e^{i(β−δ)}, 0]] on the data qubit, a Hadamard and computational measurement on the program qubit) is mapped to a prepare-and-measure scenario. Simulated annealing on a 30 × 30 grid of initial data qubits finds violations of the dimension witness S ≤ 4 (Eq. (2)) at all 900 points, and the authors conjecture that every initial data qubit admits parameters and a data measurement violating S ≤ 4."
strata_touched:
  - D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness
license: citation-only
triage: anchor
---

# Lin–Wang–Liu–Huang, nonclassicality of a delayed remote-controlled quantum computing model

P. Lin, D. Wang, Y. Liu and A. Huang, *Nonclassicality of a delayed remote-controlled quantum computing model*, arXiv:2606.31103 [quant-ph] (v1 30 June 2026), DOI 10.48550/arXiv.2606.31103.

## Verified locator

DOI: 10.48550/arXiv.2606.31103 (the arXiv DOI; no journal version is listed on the abstract page).
Primary version read: https://arxiv.org/abs/2606.31103v1 (the only arXiv version).
Source: https://arxiv.org/pdf/2606.31103v1 (text read from the PDF):
- §II, Eq. (2), the dimension witness S for four preparations and two binary measurements;
- §III, Eq. (3) and Fig. 3, the circuit and its remote-control measurements;
- the final paragraph of §III, the conjecture.

## Source statements

§II, Eq. (2): "S = E₀₀ − E₀₁ − E₁₀ + E₁₁ − E₂₀ − E₂₁ + E₃₀ + E₃₁ ≤ 4, (2) where E_xy = p(0|x,y) − p(1|x,y). If an experiment admits this classical causal explanation, then the value of S satisfies the bound shown in Eq. (2), regardless of how the preparations are relabeled".

§III: "once the parameters β and δ in the controlled-A and controlled-B gates of the programmable gate array E are configured, the same parameters β and δ should be consistently applied to the coefficients a₀ and a₁ in the projective measurement of the remote-control qubit."

§III, final paragraph: "As shown in Fig. 4(c), all 900 data points strictly exceed the value of 4. … It is reasonable to conjecture that for any arbitrary initial data qubit |d⟩, there exists a measurement on the data qubit and specific parameter values for β, δ, γ₀ and γ₁, such that, under an appropriate labeling strategy, violating the dimension witness S ≤ 4 and exhibiting its nonclassical behaviors."

---
bibkey: reda2026dynamiccooling
authors: Mattia Reda, Massimiliano Sacchi, Chiara Macchiavello, Giacomo Guarnieri
year: 2026
title: "Optimal Dynamic Cooling of Multiple Qubits"
doi: 10.48550/arXiv.2607.23641
url: https://arxiv.org/abs/2607.23641v1
claim: "Cooling M of N identical thermal qubits by one global unitary to the lowest common local temperature is solved: the optimum with identical diagonal one-qubit target marginals equals the unconstrained passive minimum for every N > M (Theorem 1). §IX compares it with a parallel benchmark of M groups of ⌊N/M⌋ qubits, each running the optimal single-target protocol: the global optimum is never worse, strictly better for M + 2 ≤ N ≤ 3M − 1, ties at (N, M) = (6, 2), and the uniqueness of that tie is left as a conjecture."
strata_touched:
  - D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness
license: citation-only
triage: anchor
---

# Reda–Sacchi–Macchiavello–Guarnieri, optimal dynamic cooling of multiple qubits

M. Reda, M. Sacchi, C. Macchiavello and G. Guarnieri, *Optimal Dynamic Cooling of Multiple Qubits*, arXiv:2607.23641 [quant-ph] (v1 26 July 2026), DOI 10.48550/arXiv.2607.23641.

## Verified locator

DOI: 10.48550/arXiv.2607.23641 (the arXiv DOI; no journal version is listed on the abstract page).
Primary version read: https://arxiv.org/abs/2607.23641v1 (the only arXiv version).
Source: https://arxiv.org/pdf/2607.23641v1 (text read from the PDF):
- §I, the two requirements of the optimization;
- §II, Eqs. (1)–(9), the register, its thermal state and the target sectors;
- §IX, Eqs. (88)–(92), the global and parallel protocols and the conjecture.

## Source statements

§I: "2. all target qubits must have the same diagonal marginal and hence the same local temperature."

§II: "Consider N identical, noninteracting qubits … each qubit is in the Gibbs state τ_β = P₀|0⟩⟨0| + P₁|1⟩⟨1|, (2) … and the initial register state is ρ(P₁) = τ_β^{⊗N}. (4) We choose the first M < N qubits as targets".

§IX: "We consider M disjoint groups, one target per group, constrained to produce the same final target population. The natural temperature-independent benchmark uses equal group size n = ⌊N/M⌋, (88) and leaves the remaining N − Mn qubits unused. Each group implements the optimal n-qubit single-target protocol. Denoting its population by p★(n, 1; P₁), we set p_par(N, M; P₁) = p★(n, 1; P₁). (89) … the unrestricted global optimum obeys p_glob(N, M; P₁) = p★(N, M; P₁) ≤ p_par(N, M; P₁) (90) pointwise. The inequality is strict throughout M + 2 ≤ N ≤ 3M − 1. (91) … For example, p_glob(6, 2; P₁) = p_par(6, 2; P₁) = 3P₁² − 2P₁³. (92) … It ties the parallel benchmark for the exceptional pair (N, M) = (6, 2). Exact symbolic checks over the finite range investigated revealed no other equality, although the uniqueness of this tie remains a conjecture."

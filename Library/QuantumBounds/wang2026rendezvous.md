---
bibkey: wang2026rendezvous
authors: C. Wang
year: 2026
title: "Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach"
doi: null
url: https://arxiv.org/abs/2610.12949v1
claim: "In balanced one-step rendezvous on the d-dimensional hypercube with Hamming step t, the no-signalling value is C(2t,t)/C(d,t) (Lemma 5.1), and no finite-dimensional quantum strategy attains it when t ≥ 2 and d > 2t (Theorems 5.5 and 6.4). The paper leaves open whether the quantum value, the supremum over finite-dimensional strategies, is then strictly below the no-signalling value."
strata_touched:
  - D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap
  - D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap
license: citation-only
triage: anchor
---

# Wang, quantum-assisted rendezvous on hypercubes

C. Wang, *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*, arXiv:2610.12949v1 (9 October 2026; quant-ph, cross-listed math-ph).

## Verified locator

Primary version read: https://arxiv.org/abs/2610.12949v1 (the only version).
Source: https://arxiv.org/pdf/2610.12949v1 (text read from the PDF):
- §2, Eqs. (2.4)–(2.10);
- §5, Lemma 5.1 and Theorem 5.5;
- §7, the open question;
- Appendix A, the proof of Lemma 5.1.

## Source statements

Eq. (2.5): the winning condition is "A∩B=∅, A∪B=η", where η = σ △ τ, |η| = 2t and |A| = |B| = t.

Eq. (2.7): "ω_{d,t}(P) := 1/|I_{d,t}| Σ_{σ∈Γ_{d−1}} Σ_{η∈Ω_{2t}} Σ_{A,B∈Ω_t} χ_{d,t}(η;A,B) P(A,B|σ,σ△η)", with "|I_{d,t}| = 2^d C(d,2t)".

Eq. (2.8): "ω_C(d,t) := max_{P∈C_{d,t}} ω_{d,t}(P), ω_Q(d,t) := sup_{P∈Q_{d,t}} ω_{d,t}(P), ω_NS(d,t) := max_{P∈NS_{d,t}} ω_{d,t}(P)", where "C_{d,t}, Q_{d,t}, NS_{d,t} denote the sets of conditional joint distributions induced by classical, finite-dimensional quantum, and no-signalling strategies, respectively."

Lemma 5.1: "For 1 ≤ t ≤ d/2, ω_NS(d,t) = C(d−t,t)/C(d,2t) = C(2t,t)/C(d,t)."

Theorem 5.5: "Assume d > 2t. If a finite-dimensional quantum strategy attains ω_NS(d,t), then a finite-dimensional projective t-sphere resolution exists."

§7: "For t ≥ 2 and d > 2t, a rank obstruction rules out finite-dimensional projective t-sphere resolutions. … It remains open whether ω_Q(d,t) is then strictly below ω_NS(d,t), and whether a strict quantum advantage over classical strategies persists in this regime."

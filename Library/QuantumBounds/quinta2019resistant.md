---
bibkey: quinta2019resistant
authors: G. M. Quinta; R. André; A. Burchardt; K. Życzkowski
year: 2019
title: "Cut-resistant links and multipartite entanglement resistant to particle loss"
doi: 10.1103/PhysRevA.100.062329
url: https://arxiv.org/abs/1908.10390v1
claim: "For any N and m, there exists an m-resistant N-qudit state in some local dimension d."
strata_touched:
  - D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction
  - D5/S3/Quantum/Entanglement/MResistantQuditExistence
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1103/PhysRevA.100.062329

Publisher: https://doi.org/10.1103/PhysRevA.100.062329

Source: https://arxiv.org/abs/1908.10390v1

## Definition

Section III, page 3:

> Definition: (m-resistance) An entangled state of N parties is called m-resistant if:
> - It remains entangled as any m of its N subsystems are traced away;
> - It becomes separable if a partial trace is performed over an arbitrary set of m + 1 subsystems.

## Conjecture

Section V, page 10:

> Conjecture 1. For any N and m, there exists an m-resistant N-qudit state in some local dimension d.

The pure-state reading uses full separability as the separability predicate.
The admissible range is N ≥ 3 and 0 ≤ m ≤ N − 2; a one-party marginal cannot
be entangled. A qudit configuration is a function Fin N → Fin d, the pure
density matrix has entries ψ(x) conjugate(ψ(y)), and normalization is the sum
of the squared absolute values of the amplitudes. The same lost configuration
is summed in the row and column of each partial trace.

Zhang et al., arXiv:2505.06567v1, Section II, page 2, equation (1):

> A state is fully separable if it can be written as a convex combination of product states,

In finite local bases this is a finite convex sum of products of positive
trace-one local matrices. Mixture weights are nonnegative real numbers whose
sum is one. The local-basis type can be any finite type, including Fin d.

The later restatement and the previously known range m ≤ (N − 2)/2 are
recorded in [Zhang et al.](../QuantumStates/zhang2025resistant.md) and
[Han et al.](../QuantumStates/han2026resistant.md). Ordinary entanglement here
means failure of full separability; genuine multipartite entanglement is a
stronger condition and is not the conjecture settled by this construction.

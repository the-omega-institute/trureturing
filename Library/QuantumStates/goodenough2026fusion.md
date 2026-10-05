---
bibkey: goodenough2026fusion
authors: Kenneth Goodenough, Andrew Landahl, Joon Lee, Antonio Russo and Kevin Thompson
year: 2026
title: "Optimal Fusion Strategies for Quantum Computation"
doi: null
url: https://arxiv.org/abs/2609.02559
claim: "For an [[n,1,d]] stabilizer code, fusion failures on a set W of qubits cause a logical failure iff the substrings of the failure-axis Pauli string on W contain a non-trivial logical operator (Proposition 3.1); the fusion distance equals the size of the largest minimal logical operator, and for graph codes it is the maximum LC-degree of the encoding vertex of the progenitor graph; the Discussion conjectures that every [[n,1,d]] code with a connected progenitor graph has a perfect adaptive strategy."
strata_touched:
  - D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion
license: citation-only
triage: anchor
---

# Optimal fusion strategies for quantum computation

arXiv:2609.02559v2 (primary quant-ph; versions v1 and v2). A logical fusion
teleports a state encoded in an $[[n,1,d]]$ code through an encoded Bell pair by
physical fusions on pairs of qubits; a failed physical fusion measures both
qubits in its failure axis. Proposition 3.1 reads:

> Let $\mathcal{C}$ be an $[[n, k, d]]$ stabilizer code, and let $Q$ be a
> fusion strategy. Then fusion failures on a subset $W$ of qubits lead to a
> logical failure if and only if $\hat{Q}[W]$ contains a non-trivial logical
> operator of $\mathcal{C}$.

Section 4 describes an $[[n,1,d]]$ code by a progenitor stabilizer state on
$n+1$ qubits with an encoding qubit $e$ incident to at least one edge; the
logical operators are the physical parts $s_{\mathrm{phys}}$ of its
stabilizers $s=s_{\log}\otimes s_{\mathrm{phys}}$, acting as $s_{\log}$, and up
to local Cliffords the progenitor state is a graph state. A strategy is perfect
when a single successful fusion guarantees a successful logical fusion
(Introduction). Section 6 (Discussion) reads:

> Early on in this project we formulated the conjecture that for $k=1$ a
> connected progenitor graph $G'$ indicated the existence of a perfect
> strategy.  This was false and the example of the code given in
> \Cref{sec:examples} is such an example.  However, this code does have a
> perfect adaptive strategy.  So, a natural conjecture and direction of future
> work is that all $[[n, 1, d]]$ codes with connected progenitor graphs have
> perfect adaptive strategies.

## Verified locator

- URL: https://arxiv.org/abs/2609.02559 (v2; source file `arxiv_v2.tex`, md5
  `aeae388c3964f292d0911e80481b730c`).
- Related: Reiß and van Loock, arXiv:2601.08820. Their Theorem 1 bounds the
  success probability of a logical Bell measurement by
  $1-(1-P_B)^{\min(n_1,n_2)}$. Their Theorem 2 gives general sufficient
  conditions for reaching it: a failure-axis sequence used before the first
  success, a sequence of stabilizer generators, and for each position a pair
  of logical operators that anticommute only there and commute with the
  earlier failure axes. They construct such sequences for the quantum parity,
  five-qubit, standard and rotated planar surface, tree and Steane codes.

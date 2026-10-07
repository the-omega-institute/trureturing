---
bibkey: markovshi2008tensorcontraction
authors: Igor L. Markov; Yaoyun Shi
year: 2008
title: Simulating Quantum Computation by Contracting Tensor Networks
doi: 10.1137/050644756
url: https://arxiv.org/abs/quant-ph/0511069v7
claim: Theorem 1.1 and its precise version Theorem 4.6 bound deterministic quantum-circuit simulation in terms of circuit size and the treewidth of the underlying circuit graph.
strata_touched: []
license: citation-only
triage: anchor
---

# Treewidth controls the specified contraction task

Markov and Shi, *Simulating Quantum Computation by Contracting Tensor Networks*, SIAM Journal on Computing 38(3), 963–981. Crossref confirms the title, authors, journal metadata, publication year and DOI; the primary preprint is https://arxiv.org/pdf/quant-ph/0511069v7.

Theorem 1.1 gives deterministic simulation time T^{O(1)} exp[O(tw(G_C))] for a circuit with T gates. Theorem 4.6 specifies an input state and measurement scenario and computes its probability. The contraction argument uses the corresponding tensor network and contraction complexity; bounded degree relates this complexity to the circuit graph's treewidth.

The FIB boundary volume §12 uses this as a classical intermediate comparison. Its q^m boundary table count is a separate direct calculation for a finite nearest-neighbour local constraint network. Neither the circuit result nor a three-dimensional drawing proves the same runtime for an arbitrary FIB native graph, arbitrary semiring semantics or an unspecified algorithm.

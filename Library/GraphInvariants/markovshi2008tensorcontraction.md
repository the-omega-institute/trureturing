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

## Complete probability networks and observer-generated control

Proposition 3.5 constructs the network for the specified measurement
probability. This is the density-operator network, or equivalently a ket
network joined to its conjugate and the input and output tensors. A bound
on one amplitude, one realized branch, or one local component does not by
itself bound contraction of the complete acceptance probability.

Theorem 4.6 includes construction of a suitable tree decomposition and
contraction order. In a direct order-supplied application, let there be
$T$ bounded-arity tensors with index dimensions at most a constant $d$.
If every intermediate tensor has at most $w$ open indices, each has at
most $d^w$ entries. A pairwise contraction enumerates at most
$d^{O(w)}$ index combinations, including the bounded-rank initial tensors.
The total arithmetic work is $T^{O(1)}d^{O(w)}$. The cost of obtaining the
order must either be supplied by the cited graph algorithm in its stated
scope or counted separately.

For a bit-complexity consequence, all tensor entries must have effective
representations with controlled precision and growth. A sufficient exact
case is a fixed finite algebraic gate set, fixed product input and output
tensors in its fixed number field, and polynomial circuit size. Intermediate
coefficients have polynomial bit length: their monomials use only disjoint
sets of the original tensors, so degree, denominator exponent and logarithm
of the number of summands are polynomially bounded. Arithmetic in the
fixed field then has polynomial bit cost. Thus polynomial $T$ and
$w=O(\log n)$ give a deterministic polynomial algorithm for a task with
a fixed positive acceptance gap. Arbitrary exact real entries are not
covered by this representation argument.

An internally generated program, intermediate measurements and feedback
must be included in the computational object whose probability is
contracted. Uniform polynomial generation and execution can be compiled
with explicit control and record registers, but this does not preserve
small width automatically. A low-width circuit obtained only after
conditioning on a particular outcome history does not compute the
unconditioned answer. Postselection also requires control of the denominator
and the precision needed for the conditional probability.

Consequently a uniform polynomial quantum SAT solver plus a uniformly
obtainable logarithmic-width contraction of its complete acceptance network
would give SAT in P. A quantum SAT solver alone gives NP contained in BQP.
These are conditional applications of the cited simulation theorem; no
such full-input-family width construction for AURIC FIB is supplied here.

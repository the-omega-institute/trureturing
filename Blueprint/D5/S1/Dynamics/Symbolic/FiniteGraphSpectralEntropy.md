# Finite Graph Walk Growth and Spectral Entropy

## Abstract

For a finite simple graph, the total number of length-`n` walks is the sum of
the entries of the `n`th adjacency-matrix power.  In the regular case this
mass is exactly `|V| d^n`.  These identities are the algebraic counting layer
for the native symbolic-dynamics entropy bridge; they do not assume
irreducibility and do not claim the full spectral-radius theorem.

**Definition 1.1 (Total walk mass).**

Lean statement: `D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy.walkMass`

*Formalization.* `D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy.walkMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

`walkMass G n` sums `(G.adjMatrix ℕ ^ n) u v` over both endpoints.  The
matrix entries count finite graph walks, so this quantity is the finite-word
growth observable consumed by the entropy development.

**Theorem 1.2 (Regular walk growth).**

Lean statement: `D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy.walkMass_eq_card_mul_pow`

*Formalization.* `D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy.walkMass_eq_card_mul_pow` (`✓ std3`).

*Source.* Repository-derived, using Mathlib's regular-graph adjacency action.

*Commentary.*

If every vertex has degree `d`, the all-ones vector is an eigenvector of the
adjacency matrix with eigenvalue `d`.  Iterating that identity and summing the
rows gives `walkMass G n = Fintype.card V * d ^ n`.  No connectedness or
aperiodicity hypothesis is used.

**Theorem 1.3 (Walk-fibre interpretation).**

Lean statement: `D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy.walkMass_eq_sum_walk_cards`

*Formalization.* `D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy.walkMass_eq_sum_walk_cards` (`✓ std3`).

*Source.* Repository-derived wrapper around Mathlib's
`SimpleGraph.adjMatrix_pow_apply_eq_card_walk`.

*Commentary.*

The total matrix mass is the sum of the finite cardinalities of the endpoint
fibres `{p : G.Walk u v | p.length = n}`.  This exposes the precise finite
combinatorial object that will later be compared with realized prefixes of a
one-sided graph shift.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy.walkMass`
- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy.walkMass_eq_card_mul_pow`
- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy.walkMass_eq_sum_walk_cards`
- Dependency: [D5/S1/Dynamics/Symbolic/FiniteGraphEntropy](FiniteGraphEntropy.md)
- Dependency: Mathlib `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`

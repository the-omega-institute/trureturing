# Dyson and McKay's cycle-clique optimality

## Abstract

The cycle-clique unions of Dyson and McKay attain the largest possible order without a regular induced subgraph of prime order p for every prime p at least thirteen.

**Theorem 1.1 (The exact optimum for every prime at least thirteen).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKay.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RegularInduced/DysonMcKay.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

For every prime p at least thirteen, every finite disjoint union of lexicographic products C_r[K_s], with cycle lengths r at least three and clique sizes s at least one, that has no regular induced subgraph on exactly p vertices has at most 9(p-1)^2/8 vertices when p is congruent to one or five modulo twelve, at most (p-1)(9p-7)/8 when p is congruent to seven, and at most (p-1)(9p-11)/8 when p is congruent to eleven. For every such prime, the explicit unions of Theorem 4.2 attain this bound. This establishes the optimality assertion following Theorem 4.2 in Section 4 of Dyson and McKay's paper. The exact component spectra describe clique packets and period-three full-support selections at one common degree. The explicit constructions avoid all regular p-selections, and independence budgets, clique bounds and triangle reserves give the matching upper bound. Products C_3[K_s] and disconnected regular selections are included.

## References

- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKay.result`
- Dependency: [D5/S3/Combinatorics/RegularInduced/DysonMcKayLower](DysonMcKayLower.md)
- Dependency: [D5/S3/Combinatorics/RegularInduced/DysonMcKayUpper](DysonMcKayUpper.md)

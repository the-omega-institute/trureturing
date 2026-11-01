# The local ordinary cherry in the true graph quotient

## Abstract

The local ordinary cherry in the true graph quotient

**Definition 1.1 (An actual terminal cherry socket).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/CherryReduction.Cherry`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/CherryReduction.Cherry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Cherry G is a literal six-flag X socket in G whose two selected ports are paired to two distinct ordinary leaf flags. The stem joins the other selected trivalent vertex. The leaf colors may differ, and all exterior pairings, loops and parallel edges remain unrestricted.

**Theorem 1.2 (A terminal ordinary cherry is zero).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/CherryReduction.cherry_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/CherryReduction.cherry_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite flag type and every actual Cherry G, the class of G in the actual AS, IHX and ordinary CL quotient is zero. In the corresponding I branch the two ordinary legs are consecutive. CL exchanges their colors. A concrete flag permutation swaps the two central flags, the two leaf ports and their leaf mates; it identifies the exchanged I graph with the H graph after reversal of both local trivalent rotors. The two AS signs multiply to plus one, so I equals H, and the literal I minus H plus X relation kills X. No assumption of compatibility with an abstract normalization map is used.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/CherryReduction.Cherry`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/CherryReduction.cherry_zero`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram](CyclicFlagDiagram.md)

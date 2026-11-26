# Finite unary Moore separation and effective synthesis

## Abstract

Two autonomous unary Moore sources of at most K states cannot agree for the first 2K−1 output observations and then diverge. An authentic prefix of that exact length determines an executable generator for its behavior.

**Theorem 1.1 (Separation at 2K−1 observations and first-match synthesis).**

$$K\ge 1\quad s_{i}=g(f^{i}(q_{0}))\quad (\forall i<2K-1, s_{i}=t_{i}) \implies (\forall i, s_{i}=t_{i})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSeparation.unary_moore_separation_and_synthesis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The start is an actual state in a nonempty carrier of cardinality at most K. The binary output of that state counts at index zero; each later index applies one more iteration of the single autonomous transition. Transient paths, singular transitions, unreachable states and constant outputs are allowed.

In the disjoint union, group states by finite output signatures. Truncation maps each next partition onto the previous one. Equal counts force words with equal truncations to agree. The unary head-and-tail recurrence then gives equality at every later index. Continued strict splitting would exceed the number of states.

For an authentic word of the stated length, enumerate the labelled transition, output and start tables of sizes 1 through K in a fixed order. The authentic machine is isomorphic to one of these tables, so the search returns a first match. Its whole output stream equals the authentic stream, and all earlier tables fail the prefix test. The exact count of candidates before any deduplication is $\sum_{1\le a\le K} a^{a+1}2^{a}$.

This identifies the output behavior, not a private state naming or presentation. It makes no claim about acquisition cost, running time optimality, or a lower bound on the comparison length.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSeparation.unary_moore_separation_and_synthesis`

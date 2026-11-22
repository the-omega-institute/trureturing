# Physical birth clock of the fixed locally wired source

## Abstract

The fixed source stream advances once at each actual beta split. The birth clock records those events in the physical order of the old leaves, not the order of semantic occurrences or a physical duration.

**Theorem 1.1 (Ordered physical births and their Fibonacci clock).**

$$B_{n}=\sum_{t=2}^{n}F_{t-1}=F_{n+1}-1\quad v_{n}=B_{n-1}=F_{n}-1\quad B_{n}-v_{n}=F_{n-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LocalWiring/PhysicalBirthClock.physical_birth_clock` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start at the actual known alpha leaf with cursor zero. A round recursively visits only the old physical children, left before right. An old alpha turns into beta without requesting a bit. An old beta requests exactly the next source bit and places beta at a for true and at b for false. The two new leaves are not visited by that round.

Each event records its one-based serial birth, its actual completed update number, its physical parent word, and its consumed bit. A round visits each old beta site just once, and the produced subtree has exactly the recorded orientation at that site. The accumulated list is strictly ordered by completed update, then by physical lexicographic address.

The displayed mature and newest-batch identities apply for n≥2. The older restriction is exactly the previous cut's complete list. At the first two cuts, before the second update, no source bit has been consumed. The finite run including its tree, cursor and events depends only on its used prefix, not on a future source bit.

The source stream and its start alignment are supplied premises. The event list is not a new observer read port. No prediction of the generator, incidence inverse, timing bound or physical-time claim is made.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LocalWiring/PhysicalBirthClock.physical_birth_clock`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LocalWiring/KnownSeedCurrentFibers](KnownSeedCurrentFibers.md)

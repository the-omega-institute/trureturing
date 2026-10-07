# The exact weighted cycle for the Frid digit family

## Abstract

The exact weighted cycle for the Frid digit family

**Theorem 1.1 (a_seed_cycle).**

$$\forall k \in \mathbb{N},\; \forall z \in \mathbb{N},\; chunkScore\left(rankA, append\left(append\left(replicate\left(z, 0\right), replicate\left(k, 36\right)\right), singleton\left(37\right)\right)\right) = 2 \cdot int\left(k\right) + 3$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/RankCyclesA.a_seed_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Numeric chunks 36 and 37 are the six-bit words 100100 and 100101. Initial zero chunks have zero weight. The repeated 36 cycle supplies weight two per repetition; the final chunk supplies the offset three.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/RankCyclesA.a_seed_cycle`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/RankA](RankA.md)

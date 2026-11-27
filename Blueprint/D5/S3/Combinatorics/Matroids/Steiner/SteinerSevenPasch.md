# A seven-Pasch counterexample in fibre dimension two

## Abstract

Seven Pasches in a centreless Steiner loop can obstruct every two-dimensional labelling.

**Theorem 1.1 (Seven Pasches can prevent a common maximum).**

Lean statement: `D5/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A 19-point Steiner triple system gives a twenty-element centreless Steiner loop. Its seven Pasches are exactly the Pasches of an embedded Fano plane. The multiplication and block-incidence tables determine the Steiner laws, the trivial centre, and the complete list of unordered Pasches.

For each normalized label table into a binary fibre of dimension two, take three generating Pasch returns. The seven returns consist of the three generators, their three pairwise sums and their triple sum. Some nonempty sum of the three is zero in dimension two. The corresponding outside square misses successful starts. The fixed-pair return construction yields a second table with a strictly larger count for that pair.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch.result`
- Dependency: [D5/S3/Combinatorics/Matroids/Steiner/SteinerRamseyObstruction](SteinerRamseyObstruction.md)

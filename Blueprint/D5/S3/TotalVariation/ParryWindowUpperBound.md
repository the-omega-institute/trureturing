# Finite Parry window upper bounds

## Abstract

Fixed minimizer tables for actual finite-k Parry windows.

**Theorem 1.1 (Fixed word orders and endpoint labels).**

Lean statement: `D5/S3/TotalVariation/ParryWindowUpperBound.parry_window_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryWindowUpperBound.parry_window_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k >= 2 and 1 <= m <= R, let N = R-m+2 and p = parryParameter k. For either fixed tie convention, there are a permutation rho of all binary length-m words and a fixed binary label table beta such that the actual stationaryDefect of windowTable is at most 1/N + choose(N,2) p^(m-1). If beta is required to be identically zero, a fixed rho still attains 2/N + choose(N,2) p^(m-1). False chooses the existing FairWindowMinimizer.table with leftmost ties; true chooses its rightmost variant, selecting the maximum position among the minimum-rank occurrences. The two constructions agree whenever the candidate words are distinct.

The Bool/Fin 2 correspondence preserves the relation bits, while transport uses their complements. Both adjacent windows call the same deterministic table. On a collision-free context, the finite average over fixed word orders and label tables is exactly 1/N. For zero labels it is at most 2/N. A union bound over pairs of starts uses the actual overlapping Parry collision estimate, giving the stated correction. Finite averaging then selects fixed tables, which may depend on k, R and m. This construction introduces no online randomness or independent priorities for occurrences.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryWindowUpperBound.parry_window_upper_bound`
- Dependency: [D5/S3/Combinatorics/FairWindowMinimizer](../Combinatorics/FairWindowMinimizer.md)
- Dependency: [D5/S3/TotalVariation/ParryTwistedComparison](ParryTwistedComparison.md)
- Dependency: [D5/S3/TotalVariation/ParryWordCollision](ParryWordCollision.md)

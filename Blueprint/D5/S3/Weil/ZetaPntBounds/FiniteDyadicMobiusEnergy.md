# Finite dyadic Möbius energy and the Riemann hypothesis

## Abstract

Finite dyadic Möbius energy and the Riemann hypothesis

**Theorem 1.1 (The finite banded identity).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy.energy_eq_banded_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy.energy_eq_banded_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural cutoff P, set a(n) = μ(n)/n in the rationals and let d(j) be the sum of a(n) over j/2 < n ≤ j, with j/2 rounded down. The energy E(P) is the sum of d(j)² over 1 ≤ j < P.

Expanding the squares gives a double sum over 1 ≤ m,n < P of a(m)a(n) times the number of cells containing both m and n. These cells are exactly the integers from max(m,n), inclusive, to min(P,2 min(m,n)), exclusive. Their number is the truncated natural difference of those endpoints. In particular the weight vanishes when 2 min(m,n) ≤ max(m,n).

On the unit cell with left endpoint j, the real reciprocal Möbius shell equals d(j). Its absolute integral from 1 to an integer P ≥ 1 is therefore the sum of |d(j)|. By Cauchy–Schwarz its square is at most (P − 1)E(P).

**Theorem 1.2 (The real exponent criterion).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy.riemannHypothesis_iff_cofinal_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy.riemannHypothesis_iff_cofinal_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Riemann hypothesis is equivalent to the following statement. For every real ε > 0 and every natural threshold N, there is a natural P ≥ N for which the real coercion of E(P) is at most P^ε.

Under RH, the zero-free half-plane bounds the ordinary Möbius prefix by a constant times N^(1/2+δ) for any positive δ. Finite Abel summation gives a bound of order j^(δ−1/2) on |d(j)|. Summing the squares gives order P^(2δ), so choosing 2δ < ε absorbs the constant for all sufficiently large P.

Conversely, a zero with real part β > 1/2 in the critical strip gives a positive lower bound of order P^β on one plus the absolute shell mass at every cutoff P ≥ 1. At the cofinal cutoffs with ε = β − 1/2, Cauchy–Schwarz gives an upper exponent (1+ε)/2 < β. This excludes such a zero. The zeta functional equation excludes zeros in the left half of the strip by reflection.

**Theorem 1.3 (The rational power criterion).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy.riemannHypothesis_iff_cofinal_energy_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy.riemannHypothesis_iff_cofinal_energy_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Riemann hypothesis holds exactly when for every positive natural k and every natural threshold N, there is a natural P ≥ N with E(P)^k ≤ P in the rationals. Each fixed-cutoff inequality uses finite rational sums and an integer power.

Taking ε = 1/k in the real criterion and raising the nonnegative sides to the kth power gives the rational inequality. For the reverse implication choose k with 1/k ≤ ε and use threshold max(N,1). Taking the kth root bounds E(P) by P^(1/k) ≤ P^ε.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy.energy_eq_banded_sum`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy.riemannHypothesis_iff_cofinal_energy`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy.riemannHypothesis_iff_cofinal_energy_pow`
- Dependency: [D5/S3/Weil/Mertens/Cryptids/VonMangoldtCount/Foundation](../Mertens/Cryptids/VonMangoldtCount/Foundation.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusShortAverage](MobiusShortAverage.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/ReciprocalMoebiusDyadicShell](ReciprocalMoebiusDyadicShell.md)

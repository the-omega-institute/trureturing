# Odd exponents of even powers with a self-conjugate CMP

## Abstract

A lower bound for Question 5.12 of Dietz, Flowers and Lockard.

**Theorem 1.1 (Lower bound on the exponent).**

$$\forall m \in \mathbb{N},\; ((2 \le m) \Rightarrow ((\operatorname{Even}\left(m\right)) \Rightarrow (\forall e \in \mathbb{N},\; ((\operatorname{Odd}\left(e\right)) \Rightarrow (\forall mu \in \operatorname{YoungDiagram},\; ((\operatorname{card}\left(mu\right) = m^{e}) \Rightarrow ((\operatorname{IsCMP}\left(m, mu\right)) \Rightarrow ((\operatorname{transpose}\left(mu\right) = mu) \Rightarrow (m + 1 \le e)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Geoffrey D. Dietz, Timothy B. Flowers, and Shannon R. Lockard (2026). *A study of m-ary partitions whose conjugates are q-ary*. DOI: [10.13069/jacodesmath.v13i3.393](https://doi.org/10.13069/jacodesmath.v13i3.393). URL: <https://jacodesmath.com/index.php/jacodesmath/article/download/393/304>.

*Commentary.*

Let L be the first row length and N the number of cells. The first row and first column meet in one cell and the diagram fits in an L by L square, so 2L − 1 ≤ N ≤ L². Since the positive parts are powers of m, write L = m^K. The area bounds and the oddness of e give 0 < 2K − e ≤ e − 2.

The square congruence gives (m − 1)² dividing N − (2L − 1). Expanding the two powers to first order modulo (m − 1)² shows that m − 1 divides 2K − e. This positive multiple is at least m − 1, hence e ≥ m + 1.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.lower_bound`
- Dependency: [D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP](OddPowerSelfConjugateCMP.md)

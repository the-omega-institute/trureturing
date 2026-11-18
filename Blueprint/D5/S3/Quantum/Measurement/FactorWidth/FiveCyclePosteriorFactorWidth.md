# Factor width of the five-cycle posterior moment

## Abstract

The rational five-cycle posterior moment belongs to the complex width-three cone and lies outside the width-two cone.

**Definition 1.1 (The cycle moment at the uniform prior).**

$$\forall (i: \operatorname{Fin}(5)), \forall (j: \operatorname{Fin}(5)), M(i, j) = \frac{5 \cdot I(i, j) + 3 \cdot W(i, j)}{55}$$

*Formalization.* `D5/S3/Quantum/Measurement/FactorWidth/FiveCyclePosteriorFactorWidth.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity matrix has entries delta(i,j). The adjacency matrix W has entry one if i and j differ by one modulo five and entry zero otherwise.

**Theorem 1.2 (Exact complex factor width).**

$$\operatorname{IsKIncoherentSum}(3, \operatorname{complex}(M)) \land \neg \operatorname{IsKIncoherentSum}(2, \operatorname{complex}(M))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FactorWidth/FiveCyclePosteriorFactorWidth.cycle_moment_width_exactly_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the five cyclic shifts of (1,2,1,0,0) and (2,2,0,-1,0). Scale these columns by the square roots of 12/1100 and 3/1100. Add the five coordinate columns scaled by the square root of 1/1100. The two shifted families cancel on every nonedge and add up to 3/55 on every edge. The coordinate columns complete the diagonal to 5/55.

Every complex outer product of a vector with at most two nonzero entries has a sum of diagonal entries at least twice the sum of real edge entries. A single vector with both ends of one edge in its support gives the squared norm of their difference after subtraction. The displayed cycle moment violates the resulting inequality by 5/55.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidth/FiveCyclePosteriorFactorWidth.cycle_moment_width_exactly_three`
- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidth/FiveCyclePosteriorFactorWidth.moment`
- Dependency: [D5/S3/Quantum/Measurement/FactorWidthTwoCone](../FactorWidthTwoCone.md)

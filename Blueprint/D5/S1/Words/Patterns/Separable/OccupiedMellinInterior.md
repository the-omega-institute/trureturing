# Regular blocks of the Mellin mesh

## Abstract

An explicit error estimate compares regularized Mellin samples with their unshifted integral.

**Definition 1.1 (Paired regularized power sample).**

$$\operatorname{sample}\left(\beta, a, s\right)=(s)^{-\frac{3}{2}}\cdot((a+1+s)^{-\beta}+(a+\left\lvert1-s\right\rvert)^{-\beta}-2\cdot(a+1)^{-\beta})$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedMellinInterior.sample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parameters beta, a, and s are real. The opposite directions are paired about one before subtraction of the two central values.

**Theorem 1.2 (Exact lattice comparison on either regular component).**

$$\left\lvert\int_{u}^{v}\operatorname{sample}\left(\beta, 0, s\right)\,ds-\frac{1}{n}\sum_{i\in \operatorname{range}\left(N\right)}\operatorname{sample}\left(\beta, \frac{2}{n}, \frac{L+i}{n}\right)\right\rvert\le\frac{16\cdot(\delta)^{-\frac{17}{4}}}{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedMellinInterior.normalized_lattice_interior_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n, L, and N be natural numbers with n positive, and put u=L/n and v=(L+N)/n in the reals. Assume 0 <= beta <= 3/4, 0 < delta <= 1, delta <= u, and N/n <= 1/delta. Require either v <= 1-delta or 1+delta <= u. The sum runs over 0 <= i < N, and is empty when N=0.

On a regular component, the paired derivative is uniformly bounded by a constant times delta to the power -13/4. The mean-value estimate bounds each unshifted left-sampled cell, and a separate comparison in the shift parameter controls replacing zero shift by the exact value 2/n. The interval length bound gives the displayed error.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinInterior.normalized_lattice_interior_error`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinInterior.sample`

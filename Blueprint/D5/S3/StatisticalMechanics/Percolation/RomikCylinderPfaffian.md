# Rational cylinder Pfaffians and their boundary

## Abstract

The explicit nested-arch cylinder Pfaffian is regular on the closed integer range and reduces by a unit pair at its boundary.

**Definition 1.1 (Explicit cylinder matrix).**

Lean statement: `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.cylinderMatrix`

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.cylinderMatrix` (`✓ std3`).

*Citation.* Melda Akyazi-Zavadski, Nathanaël Berestycki, Sunil Chhita (2026). *On Romik’s rationality conjectures for critical percolation*. URL: <https://arxiv.org/html/2611.26570v1>.

*Commentary.*

For every natural m and rational x, cylinderMatrix(m,x) is a rational matrix on Fin(2m). The endpoints are in alternating white, black order, with block indices r,s from 0 through m-1. The four entries are the expressions (4.8), (4.10), (4.11), and (4.9) in that order across the two rows of the block. They use (4.12) for the signed p term and (5.1), (5.2), (5.3) for H, extended by antisymmetry and a zero diagonal. The source identifies these blocks with inverse Kasteleyn entries for integer x>m≥1.

The white summation indices run from r+2 to 2r+2 and the black indices from 1 to 2r+2, with the corresponding bounds for s. The white weight is the binomial coefficient with upper index c-1 and lower index 2r-c+2. The black weight sums the binomial coefficient with upper index c and lower index 2r-c-j+2 over j from 0 through 2r-c+2. Negative lower binomial indices contribute zero. The signed integer products in (5.1) use inclusive endpoints, including zero factors and empty products. The rational paired factors have numerator x²-a² and denominator 4x²-a².

**Theorem 1.2 (Boundary unit pair).**

$$\forall n \in \mathbb{N},\; \operatorname{pfaffian}\left(\operatorname{cylinderMatrix}\left(n + 1, n + 1\right)\right) = \operatorname{pfaffian}\left(\operatorname{cylinderMatrix}\left(n, n + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.cylinder_pfaffian_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Melda Akyazi-Zavadski, Nathanaël Berestycki, Sunil Chhita (2026). *On Romik’s rationality conjectures for critical percolation*. URL: <https://arxiv.org/html/2611.26570v1>.

*Commentary.*

For every natural n, specialize at x=n+1. Every white index c for the last block r=n satisfies n+2≤c≤2(n+1). The product in (4.12) and the outer product in (5.1) then contain a vanishing numerator at a=n+1, with all variable denominator factors nonzero. Hence the last white row vanishes against earlier endpoints and has entry one to its paired black endpoint by the delta term of (4.10). Skew symmetry in the white-white and white-black entries gives a zero penultimate column above the diagonal. Restriction to the first 2n indices is cylinderMatrix(n,n+1), and forced-pair reduction gives the stated equality.

**Definition 1.3 (Regular rational functions).**

Lean statement: `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.regularAt`

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.regularAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each rational x, regularAt(x) is the subring of RatFunc over the rationals consisting of functions whose reduced denominator has nonzero evaluation at x. Divisibility of the reduced denominators for sums and products proves closure. Canonical evaluation on this subring is a ring homomorphism.

**Definition 1.4 (Rational cylinder function).**

Lean statement: `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.rationalCylinder`

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.rationalCylinder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Melda Akyazi-Zavadski, Nathanaël Berestycki, Sunil Chhita (2026). *On Romik’s rationality conjectures for critical percolation*. URL: <https://arxiv.org/html/2611.26570v1>.

*Commentary.*

For every natural m, rationalCylinder(m) is the normalized Pfaffian over RatFunc of the same explicit 2m by 2m matrix expressions, interpreted in the rational-function field with x the indeterminate. The formula uses the same signed products, finite sums, and coefficients as cylinderMatrix.

**Theorem 1.5 (Closed integer range specialization).**

$$\forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; m \le k \Rightarrow \left(\operatorname{rationalCylinder}\left(m\right) \in \operatorname{regularAt}\left(k\right) \land \operatorname{eval}\left(k, \operatorname{rationalCylinder}\left(m\right)\right) = \operatorname{pfaffian}\left(\operatorname{cylinderMatrix}\left(m, k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.evaluate_rationalCylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Melda Akyazi-Zavadski, Nathanaël Berestycki, Sunil Chhita (2026). *On Romik’s rationality conjectures for critical percolation*. URL: <https://arxiv.org/html/2611.26570v1>.

*Commentary.*

For all natural m,k with m≤k, including m=k and m=0, the rationalCylinder(m) function belongs to regularAt(k) and its canonical RatFunc.eval with the identity ring homomorphism on the rationals at the rational cast of k equals the normalized Pfaffian of cylinderMatrix(m,k). Every paired-product or summand denominator 4k²-t² has t<2k for a matrix entry, so the entries belong to the regular subring. Evaluation commutes with sums, products and the normalized Pfaffian there. The matrix of evaluated entries equals cylinderMatrix(m,k). This proves both conjuncts without assuming a boundary probability identity.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.cylinderMatrix`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.cylinder_pfaffian_boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.evaluate_rationalCylinder`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.rationalCylinder`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.regularAt`
- Dependency: [D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian](../../../S0/Certificates/Combinatorics/ForcedLastPairPfaffian.md)

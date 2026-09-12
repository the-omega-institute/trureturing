# Stationary Occupation Rank Nullity

## Abstract

PSD occupation recurrence gives a rank bound through factorial polynomial coordinates.

Let sigma be a finite type and let a assign a natural number to each coordinate. TailBox(a) is the product of the intervals Fin(a(i)+1), including their zero endpoints. The map lower decreases coordinate i by one using natural subtraction. The linear operator lowering sends a coordinate vector at r to the vector at lower(a,i,r) when r(i) is positive, and to zero otherwise. All matrices and vectors below are complex.

**Theorem 1.1 (recurrence_quadratic_identity).**

$$\forall sigma \in Type,\; Fintype\left(sigma\right) \Rightarrow \left(\forall a \in sigma \to \mathbb{N},\; \forall B \in Matrix\left(TailBox\left(a\right), TailBox\left(a\right), \mathbb{C}\right),\; \left(\forall r \in TailBox\left(a\right),\; \forall s \in TailBox\left(a\right),\; \left(r \ne 0 \land s \ne 0\right) \Rightarrow B\left(r, s\right) = \sum_{i:sigma}{ite\left(0 < val\left(r\left(i\right)\right) \land 0 < val\left(s\left(i\right)\right), B\left(lower\left(a, i, r\right), lower\left(a, i, s\right)\right), 0\right)}\right) \Rightarrow \left(\forall u \in TailBox\left(a\right) \to \mathbb{C},\; u\left(0\right) = 0 \Rightarrow dotProduct\left(star\left(u\right), mulVec\left(B, u\right)\right) = \sum_{i:sigma}{dotProduct\left(star\left(lowering\left(a, i, u\right)\right), mulVec\left(B, lowering\left(a, i, u\right)\right)\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.recurrence_quadratic_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a vector whose zero coordinate vanishes, the nonzero-index recurrence gives the sum of the lowered quadratic forms. The star is complex conjugation; dotProduct and mulVec give the sesquilinear expression.

**Theorem 1.2 (lowering_mem_kernel).**

$$\forall sigma \in Type,\; Fintype\left(sigma\right) \Rightarrow \left(\forall a \in sigma \to \mathbb{N},\; \forall B \in Matrix\left(TailBox\left(a\right), TailBox\left(a\right), \mathbb{C}\right),\; \left(PosSemidef\left(B\right) \land \left(\forall r \in TailBox\left(a\right),\; \forall s \in TailBox\left(a\right),\; \left(r \ne 0 \land s \ne 0\right) \Rightarrow B\left(r, s\right) = \sum_{i:sigma}{ite\left(0 < val\left(r\left(i\right)\right) \land 0 < val\left(s\left(i\right)\right), B\left(lower\left(a, i, r\right), lower\left(a, i, s\right)\right), 0\right)}\right)\right) \Rightarrow \left(\forall u \in TailBox\left(a\right) \to \mathbb{C},\; \left(u \in ker\left(mulVecLin\left(B\right)\right) \land u\left(0\right) = 0\right) \Rightarrow \left(\forall i \in sigma,\; lowering\left(a, i, u\right) \in ker\left(mulVecLin\left(B\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.lowering_mem_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive semidefiniteness makes every term in that sum nonnegative. If the original vector lies in the kernel, their sum is zero, so each lowered quadratic form vanishes and each lowered vector lies in the same kernel.

The exponent of r is the finitely supported function with value r(i). The factorialProduct is the product of the factorials of these values. It never vanishes. Scaling the monomial basis by its inverse defines a linear equivalence coordinateEquiv onto the polynomials supported in the rectangle; polynomialMap is its inclusion into the full multivariate polynomial ring.

**Theorem 1.3 (polynomialMap_single).**

$$\forall sigma \in Type,\; Fintype\left(sigma\right) \Rightarrow \left(\forall a \in sigma \to \mathbb{N},\; \forall r \in TailBox\left(a\right),\; \forall c \in \mathbb{C},\; polynomialMap\left(a, PiSingle\left(r, c\right)\right) = monomial\left(exponent\left(a, r\right), \frac{c}{factorialProduct\left(a, r\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.polynomialMap_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single coefficient c at r becomes the monomial with coefficient c divided by the product of coordinate factorials.

**Theorem 1.4 (polynomialMap_injective).**

$$\forall sigma \in Type,\; Fintype\left(sigma\right) \Rightarrow \left(\forall a \in sigma \to \mathbb{N},\; Injective\left(polynomialMap\left(a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.polynomialMap_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scaled monomial coordinates are unique, so this polynomial map is injective.

**Theorem 1.5 (pderiv_polynomialMap).**

$$\forall sigma \in Type,\; Fintype\left(sigma\right) \Rightarrow \left(\forall a \in sigma \to \mathbb{N},\; \forall i \in sigma,\; \forall u \in TailBox\left(a\right) \to \mathbb{C},\; pderiv\left(i, polynomialMap\left(a, u\right)\right) = polynomialMap\left(a, lowering\left(a, i, u\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.pderiv_polynomialMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorial scaling cancels the exponent introduced by differentiation. Consequently lowering and partial differentiation intertwine on every vector.

**Theorem 1.6 (constantCoeff_polynomialMap).**

$$\forall sigma \in Type,\; Fintype\left(sigma\right) \Rightarrow \left(\forall a \in sigma \to \mathbb{N},\; \forall u \in TailBox\left(a\right) \to \mathbb{C},\; constantCoeff\left(polynomialMap\left(a, u\right)\right) = u\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.constantCoeff_polynomialMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant coefficient is exactly the zero coordinate of the coefficient vector.

**Theorem 1.7 (stationary_gram_rank_lower_bound).**

$$\forall sigma \in Type,\; Fintype\left(sigma\right) \Rightarrow \left(\forall a \in sigma \to \mathbb{N},\; \forall B \in Matrix\left(TailBox\left(a\right), TailBox\left(a\right), \mathbb{C}\right),\; \left(PosSemidef\left(B\right) \land \left(B\left(0, 0\right) = 1 \land \left(\forall r \in TailBox\left(a\right),\; \forall s \in TailBox\left(a\right),\; \left(r \ne 0 \land s \ne 0\right) \Rightarrow B\left(r, s\right) = \sum_{i:sigma}{ite\left(0 < val\left(r\left(i\right)\right) \land 0 < val\left(s\left(i\right)\right), B\left(lower\left(a, i, r\right), lower\left(a, i, s\right)\right), 0\right)}\right)\right)\right) \Rightarrow \prod_{i:sigma}{a\left(i\right) + 1} - FinsetSup\left(univ\left(sigma\right), a\right) \le rank\left(B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.stationary_gram_rank_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Map the matrix kernel into the rectangular polynomial subspace. The unit zero entry excludes nonzero constants, and the lowering identity gives conditional derivative closure. The rectangular polynomial dimension bound then bounds nullity by the finite supremum of a. Rank-nullity and the product cardinality give the displayed inequality, including the all-zero box and an empty coordinate type.

## References

- Truth anchor: `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.constantCoeff_polynomialMap`
- Truth anchor: `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.lowering_mem_kernel`
- Truth anchor: `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.pderiv_polynomialMap`
- Truth anchor: `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.polynomialMap_injective`
- Truth anchor: `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.polynomialMap_single`
- Truth anchor: `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.recurrence_quadratic_identity`
- Truth anchor: `D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity.stationary_gram_rank_lower_bound`
- Dependency: [D5/S1/Ledger/BoundedTimeSlice](../../../S1/Ledger/BoundedTimeSlice.md)
- Dependency: [D5/S3/Quantum/Algebra/RectangularPolynomialNullity](../Algebra/RectangularPolynomialNullity.md)

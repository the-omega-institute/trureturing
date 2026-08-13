# Minimum of the Basic Discriminant Class

## Abstract

Five is the least member of the explicit positive odd squarefree discriminant class.

**Theorem 1.1 (Five is a basic discriminant).**

$$BasicDiscriminant(5)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/BasicDiscriminantMinimum.five_basic_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number five is greater than one, squarefree, and congruent to one modulo four, so it belongs to the explicit basic-discriminant class.

**Theorem 1.2 (Every basic discriminant is at least five).**

$$\forall d\in \mathbb{N}, BasicDiscriminant(d) \Rightarrow 5 \leq d$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/BasicDiscriminantMinimum.basic_discriminant_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A basic discriminant is a natural number d satisfying 1 < d, squarefreeness, and d congruent to 1 modulo 4. The elementary arithmetic inequalities force every such d to satisfy 5 <= d.

Together with the preceding witness at d = 5, this proves that five is the least positive member of the stated odd squarefree discriminant class. No broader claim about fundamental discriminants is made.

## References

- Truth anchor: `D5/S3/Factorization/BasicDiscriminantMinimum.basic_discriminant_minimum`
- Truth anchor: `D5/S3/Factorization/BasicDiscriminantMinimum.five_basic_discriminant`

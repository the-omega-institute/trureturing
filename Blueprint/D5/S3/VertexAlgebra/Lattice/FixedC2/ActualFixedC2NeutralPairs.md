# Two-Oscillator Reduction in the Fixed Lattice C2 Quotient

## Abstract

Translation and fixed quadratic modes bound the surviving neutral two-oscillator classes.

The lattice data consist of a natural-number rank and a symmetric integral Gram matrix with even diagonal. The actual complex carrier consists of finitely supported charge families of oscillator polynomials.

**Definition 1.1 (Neutral oscillator pairs).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.neutralPair`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.neutralPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The charge-zero state with polynomial X(i,a) X(j,b) is fixed by the sign involution. The oscillator indices start at zero, so X(i,a) represents the current mode numbered -a-1. Write pairClass for the image of this state in the intrinsic fixed C2 quotient.

**Theorem 1.2 (Translation moves the indices to one oscillator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.pair_class_normalize`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.pair_class_normalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation of a fixed state is its (-2)-product with the vacuum. Translating a pair therefore gives a zero class, with the two terms of the Leibniz rule weighted by a+1 and b+1. Iterating this relation expresses the class at (a,b) as (-1)^a times the binomial coefficient choosing a from a+b times the class at (0,a+b).

**Theorem 1.3 (Same-basis pairs vanish at odd total index).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.diagonal_pair_class_odd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.diagonal_pair_class_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the two basis indices are equal and a+b is odd, the pair class is zero. Exchanging the two oscillators and using the translation relation identifies the normalized class with its negative.

**Theorem 1.4 (Cancellation of the four-oscillator terms).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.fixed_quadratic_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.fixed_quadratic_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take twice the (-2)-product of X(i,0)^2 with X(i,2) X(j,b) and subtract the (-2)-product of X(i,1)^2 with X(i,0) X(j,b). Both products are intrinsic C2 generators. The four-oscillator terms cancel in the mode expansion. The resulting relation in the quotient is the sum of three classes, equal to zero. The (i,j) pair at (5,b) has coefficient 32 G(i,i). The (i,i) pair at (0,b+5) has coefficient 4 G(j,i) binom(-b-1,2)(b+5), with the generalized binomial coefficient. The (i,i) pair at (2,b+3) has coefficient 4(b+1) G(i,j).

**Theorem 1.5 (High pairs with equal basis indices vanish).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.diagonal_pair_class_high`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.diagonal_pair_class_high` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When j=i, normalization puts every term of the cancellation relation on the same class of total index n+5. Its combined coefficient is -(4/15) G(i,i) (n+5)(n+1)(n+3)(n+7)(n-1). For n at least two and G(i,i) nonzero, this forces the class to vanish.

**Theorem 1.6 (All neutral pair classes of total index at least seven vanish).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.neutral_pair_class_high`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.neutral_pair_class_high` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary j, the same-basis terms in the cancellation relation already vanish at total index at least seven. The remaining coefficient is nonzero after normalization when G(i,i) is nonzero. Thus every pair reduces to a multiple of one of the normalized pairs of total index zero through six, or to zero.

**Theorem 1.7 (A positive-definite Gram matrix has nonzero diagonal).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.gram_diagonal_ne`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.gram_diagonal_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the real cast of the Gram matrix is positive definite, every Gram diagonal entry is nonzero. Testing the positive quadratic form on the corresponding coordinate vector gives strict positivity of the real cast of that entry.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.diagonal_pair_class_high`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.diagonal_pair_class_odd`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.fixed_quadratic_cancellation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.gram_diagonal_ne`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.neutralPair`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.neutral_pair_class_high`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.pair_class_normalize`
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2](ActualFixedC2.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../../LatticeActualConformalState.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateDerivative](../../LatticeActualStateDerivative.md)

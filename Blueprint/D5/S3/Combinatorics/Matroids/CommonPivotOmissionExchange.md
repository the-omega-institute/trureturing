# Exchange at a Common Pivot

## Abstract

Integral exchange of sparse omission constraints on alternating forms.

**Definition 1.1 (Constrained alternating forms).**

Lean statement: `D5/S3/Combinatorics/Matroids/CommonPivotOmissionExchange.kernel`

*Formalization.* `D5/S3/Combinatorics/Matroids/CommonPivotOmissionExchange.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The module consists of alternating forms whose insertions with the pivot vector and the weighted vector both vanish, and whose values are killed by the modulus.

**Theorem 1.2 (Exchange of disjoint omission constraints).**

Lean statement: `D5/S3/Combinatorics/Matroids/CommonPivotOmissionExchange.common_pivot_omission_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CommonPivotOmissionExchange.common_pivot_omission_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a common pivot and a nonzero off-pivot weight in a finite ordered basis. Take a positive modulus. Suppose the new omitted coordinate set meets each prior set in at most its size minus two indices. The product of the unrestricted and jointly restricted form modules is integrally linearly equivalent to the product of the two individually restricted modules. At every prime power, a basis change localizes the insertion and the new constraint can be exchanged inside its disjoint coordinate support. Coprime decomposition then gives the integral equivalence.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CommonPivotOmissionExchange.common_pivot_omission_exchange`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CommonPivotOmissionExchange.kernel`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitReplacementSupport](CircuitReplacementSupport.md)
- Dependency: [D5/S3/Combinatorics/Matroids/PrimePowerPivotBasis](PrimePowerPivotBasis.md)

# Translation of Actual Opposite Coefficients

## Abstract

The finite opposite coefficients satisfy the actual state-translation derivative identity.

D is unrestricted integral even lattice data. H satisfies both inverse-Gram equations. The state a has actual integer grade h, which need not be nonnegative. Translation is the original operator T=L(-1). Every sum uses the actual L1 iterates and the native finite oscillator bound; no opposite family is treated as a native creative field.

**Theorem 1.1 (Exact powers on a translated homogeneous state).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeDerivative.one_pow_translation_succ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeDerivative.one_pow_translation_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

L1^(j+1)(T a)=T L1^(j+1)a+(j+1)(2h-j)L1^j a. The actual Virasoro commutator [L1,T]=2L0 and the actual grade h-j give the recurrence. Complex and integer differences retain their signs.

**Theorem 1.2 (Actual opposite derivative coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeDerivative.opposite_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeDerivative.opposite_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

O_(T a)(n)=-n O_a(n-1), where T a is assigned grade h+1. A single finite cutoff covers a and T a. The true state derivative law is applied to every actual descendant, then the factorial-normalized successor terms are reindexed. The last descendant term vanishes by actual local nilpotence. This identity is the derivative interface for every negative-current opposite insertion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeDerivative.one_pow_translation_succ`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeDerivative.opposite_translation`
- Dependency: [D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion](LatticeOppositeCurrentInsertion.md)

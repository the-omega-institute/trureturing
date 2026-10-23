# ActualNestedQIterate

## Abstract

Original complete nested residue iterate

**Theorem 1.1 (actual_nested_q_iterate).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/ActualNestedQIterate.actual_nested_q_iterate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/ActualNestedQIterate.actual_nested_q_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The supplied Laurent polynomial P and cutoff K are arbitrary. The universal coefficient equation is the original actual three-field numerator equation for every integer exponent. The first complete-field locality H1, the function H2 over range((K-r).toNat), and H3 over range(vectorFrequencyBound b+1) are independent. All signed lifts, modes, input vectors and algebraic duals are retained. The three exact actual outer-residue/Taylor identifications share one numerator. Their finite collision balance gives the actual nested-Q iterate, including negative total degree and empty support ranges. This helper is consumed by the native first-source current step.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/ActualNestedQIterate.actual_nested_q_iterate`
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor](LatticeHalfFockABOuterTaylor.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockFirstOuterTaylor](LatticeHalfFockFirstOuterTaylor.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor](LatticeHalfFockSecondSourceTaylor.md)

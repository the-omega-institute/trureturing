# The rational inner field and its ordered coefficients

## Abstract

Signed current/second-source local residues

The current/second-source diagonal is expanded over the rational field of the two remaining labelled variables v and z. Signed Laurent exponents, the independent spectator pole and both Hahn orders are retained. Local coefficients have finite support on the antidiagonals used by the outer residue.

**Theorem 1.1 (Both actual local coefficient maps come from the same rational field).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The fractional shift is multiplied into the rational field before expansion. The v,z and z,v coefficient maps then give the two complete lastSourceLocalQ values with their exact shifted mode indices.

**Theorem 1.2 (Finite Laurent evaluation of the inner rational field).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_rational_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_rational_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Each supported numerator monomial is evaluated with its original signed exponent. Summing these local residues gives the explicit finite Taylor rational field at the supplied cutoff K.

**Theorem 1.3 (Finite support for both ordered outer sums).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.rational_joint_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.rational_joint_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Hahn antidiagonals give finite mode fibers in both orders. A finite union over the fractional outer index gives joint finite support at every natural outer cutoff H and all signed r,n. This does not impose a complete-field locality order on an ordered half.

**Theorem 1.4 (Signed complete residue of a Laurent monomial times the diagonal).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.source_monomial_complete_residue`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.source_monomial_complete_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The difference of the two ordered residues is evaluated for arbitrary signed p,q,t,r,n. The r+t<0 branch gives the exact finite binomial coefficient subject to the degree equation; the complementary branch cancels. Both branches enter the later monomial outer readout.

**Theorem 1.5 (The original inner Taylor summand as a finite signed Laurent sum).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.source_inner_monomial_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.source_inner_monomial_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The local Taylor index h is kept explicit. Reversing z-v to v-z contributes the exact epsilon factor before the outer coefficient map is applied; all source exponents and the independent spectator pole remain in the expression.

**Definition 1.6 (The signed inner Taylor summand).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.secondSourceInnerTaylorTerm`

*Formalization.* `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.secondSourceInnerTaylorTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

This finite coefficient-field term records the complete signed Laurent factors after the J/B local residue and before either outer Hahn order.

**Theorem 1.7 (The finite local Taylor index).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_monomial_taylor_index`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_monomial_taylor_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The actual signed monomial residue equals its explicit finite local Taylor expansion on every alpha in range M-j.

**Theorem 1.8 (The complete signed inner Taylor expansion).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_taylor_inner_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_taylor_inner_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every alpha in the actual finite range, secondSourceTerm is expanded over the local Taylor index u < M-j-alpha. The expansion retains signed numerator exponents, both pair poles, the spectator factor and the fractional z^(-alpha) shift. The complete G_j is the finite sum over alpha and the actual coefficient support.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.rational_joint_support`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.secondSourceInnerTaylorTerm`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_monomial_taylor_index`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_rational_evaluation`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_taylor_inner_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.source_inner_monomial_normal_form`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.source_monomial_complete_residue`
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction](../ContextualKernelExtraction.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues](../LatticeHalfFockABOuterTaylor/LocalResidues.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockOuterTaylorEvaluation](../LatticeHalfFockOuterTaylorEvaluation.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient](../LatticeHalfFockSliceQuotient.md)

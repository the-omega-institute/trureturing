# The rational inner field and its two supported orders

## Abstract

The complete current/second-source rational field in the original nested-Q telescope.

**Theorem 1.1 (One rational G_j retains both complete J/B residues and every original label).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_current_second_source_rational_field`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_current_second_source_rational_field` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For the supplied actual homogeneous numerator P at arbitrary natural cutoff K, the theorem constructs G_j(v,z) in the rational field of the two remaining labelled Laurent variables. With M equal to the current/B locality bound, it is the finite sum over alpha<M-j of z^(-alpha) choose(-1/2,alpha) times the local J/B residue of (y-z)^(j+alpha) P/Q_K. No source/source locality witness is required for the caller's K.

Each numerator monomial is evaluated with its original signed exponents. In the local coordinate h=y-z it has factors (z+h)^e0, h^(j+alpha-M), (z-v+h)^(-L), and the unchanged spectator factor c v^e1 z^e2 (v-z)^(-K). The translated signed powers have nonnegative local Taylor support because z and z-v are nonzero in the coefficient field. The finite binomial coefficient formula is applied to the actual local residue, then summed over the finite support of P.

The fused residue square identifies both complete inner coefficient maps with the v,z and z,v Hahn expansions of this same G_j. Multiplication by z^(-alpha) precedes expansion and produces the exact shifted mode indices of lastSourceLocalQ. The original four full word orders remain AJB, ABJ, JBA, BJA. Neither remaining variable is specialized to a scalar.

The contextual Hahn antidiagonal supplies finite support of every outer mode fiber. A finite union over the fractional outer index proves joint finite support of the two actual mode-index summands, and both ordered mode fibers have finite support for every finite outer cutoff. This support comes from the full Hahn expansions and does not assert that an ordered half or a numerator monomial has the complete field's locality cutoff.

Before distributing the outer readout over the finite numerator expansion, the proof establishes joint finite support over alpha, the numerator exponent, the fractional outer offset and the mode-convolution index for each of the two full orders. The finite-support hypotheses of mathlib's finsum_sum_comm then justify both interchanges. The actual scalar nested-Q value is consequently the explicit finite sum of the complete outer rational readouts of these terms. The local Taylor index inside each signed monomial residue is still in its finite binomial sum.

For the actual fields A and Bj and their supplied independent locality order H, the complete field is first padded to max(H,L+M+K). The arbitrary-cutoff slice quotient theorem then transports the actual readout to the original P/Q_K. Only after that padding does the finite rational evaluation enter the proof. The theorem retains arbitrary input tensor, functional, signed indices and lifts, zero numerator and empty inner sums; it also transports the complete OuterQCompletion law at H.

The subsequent actual_second_source_third theorem evaluates these original rational readouts through both ordered Hahn maps. It derives the sharp inner and outer Taylor support, contracts both finite Vandermonde sums and consumes the finite reverse Taylor convolution at t=M-1. The full sameNumeratorCollisionBridge also requires its independent first and middle conjuncts.

The signed Laurent proof adapts the J/A calculation in LatticeHalfFockOuterTaylorEvaluation to J/B; the Hahn, Laurent and binomial infrastructure is from mathlib under Apache 2.0. The actual supplier closure is inherited research source, including the six additional owners and four modified older owners disclosed with the slice quotient checkpoint. It is not asserted to be an independently integrated dev API. The matching Reg source reconstructs the whole theorem and its positive actual law; the remaining family variation, sensitivity, observational dependence and final registration are unfinished.

**Theorem 1.2 (The original reverse third nested-Q identity).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_second_source_third`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_second_source_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every original lattice, nondegenerate Gram matrix, current label, original source states, natural K, signed lifts and modes, tensor input, linear functional and supplied original homogeneous numerator P, the theorem proves the third equality of sameNumeratorCollisionBridge. The only locality inputs are the original complete A/Bj field orders H3(j). No source/source locality is imposed on K, and no compatible-module or Jacobi premise is added.

Each actual inner Taylor term is normalized in its unchanged rational coefficient field to signed monomials times (v-z)^(-K-L-k). Its two coefficient maps are the genuine v,z and z,v Hahn expansions. The contextual kernel extraction theorem converts their supported mode convolutions to ordinary binary kernel coefficients. For negative diagonal degree, signed_kernel_choose combines the two origin-mode branches into the integer Laurent binomial coefficient; for nonnegative degree their difference is zero.

The finite inner index gives alpha+a+k=M-j-1. The original numerator coefficient equation gives e0+e1+e2=degree-n-1, so the surviving outer Taylor index satisfies alpha+a+beta+b=degree and leaves final z exponent -n-1. The full algebraic pole bound fits the padded cutoff max(H3(j),L+M+K). The outer beta/b sum and the inner alpha/a triangle then contract by the two Vandermonde identities, producing exactly epsilon(-L) times the finite collisionTaylor sum for every j. Substitution into the original third telescope and the finite reverse Taylor convolution gives its requested orderedResidueWeight expression.

Signed numerator exponents, negative signed degree, zero P and all empty finite ranges remain in scope. This is the THIRD conjunct only: the complete sameNumeratorCollisionBridge, VOA program, string theory and AdS/CFT bridges are not established by this theorem. The matching Reg source reconstructs the exact quantified theorem and its actual positive law; four-slot registration remains unfinished under issue 20510.

**Definition 1.3 (The signed inner Taylor summand).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.secondSourceInnerTaylorTerm`

*Formalization.* `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.secondSourceInnerTaylorTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

This finite coefficient-field term records the complete signed Laurent factors after the J/B local residue and before either outer Hahn order.

**Theorem 1.4 (The finite local Taylor index).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_monomial_taylor_index`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_monomial_taylor_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The actual signed monomial residue equals its explicit finite local Taylor expansion on every alpha in range M-j.

**Theorem 1.5 (The complete signed inner Taylor expansion).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_taylor_inner_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_taylor_inner_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every alpha in the actual finite range, secondSourceTerm is expanded over the local Taylor index u < M-j-alpha. The expansion retains signed numerator exponents, both pair poles, the spectator factor and the fractional z^(-alpha) shift. The complete G_j is the finite sum over alpha and the actual coefficient support.

**Theorem 1.6 (The complete actual signed outer collision).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_second_source_outer_collision`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_second_source_outer_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For the original three-label numerator and arbitrary supplied cutoff K, the two complete outer Laurent orders satisfy the inherited unrestricted collision identity coefficientwise. Signed numerator exponents and origin-pole cancellation are retained, with no locality assumption on an ordered half. The actual_second_source_third proof computes both ordered coefficients of the expanded G_j terms and combines their signed origin modes before restricting the complete residue support.

**Theorem 1.7 (Reverse outer contraction after complete local evaluation).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_reverse_outer_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_reverse_outer_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For M>0, the theorem consumes the complete signed local evaluation for every original j, applies the finite reverse Taylor convolution at t=M-1, and combines the two epsilon factors. It preserves the signed degree, negative-degree empty branch and ordered residue weight. The actual_second_source_third theorem supplies this local evaluation from the original coefficient-field terms.

**Theorem 1.8 (Sharp inner Taylor support).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_inner_sharp_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_inner_sharp_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Every nonempty inner Taylor index satisfies alpha+a+k=M-j-1, including arbitrary signed Laurent numerator exponents.

**Theorem 1.9 (Inner fractional Vandermonde contraction).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_inner_vandermonde`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_inner_vandermonde` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The finite -1/2 contraction is proved for every integer Laurent exponent, so negative and zero numerator powers remain in scope.

**Theorem 1.10 (Outer fractional Vandermonde contraction).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_outer_vandermonde`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_outer_vandermonde` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The finite -gamma/2 contraction is proved for every integer Laurent exponent and is the outer contraction needed after sharp support.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_current_second_source_rational_field`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_second_source_outer_collision`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_second_source_third`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.secondSourceInnerTaylorTerm`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_inner_sharp_support`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_inner_vandermonde`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_monomial_taylor_index`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_outer_vandermonde`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_reverse_outer_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_taylor_inner_expansion`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation](../LatticeHalfFockOuterTaylorEvaluation.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction](ContextualKernelExtraction.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues](LatticeHalfFockABOuterTaylor/LocalResidues.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient](LatticeHalfFockSliceQuotient.md)

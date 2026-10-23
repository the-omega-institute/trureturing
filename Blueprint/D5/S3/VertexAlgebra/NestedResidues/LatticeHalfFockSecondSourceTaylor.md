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

The contextual Hahn antidiagonal supplies finite support of every outer mode fiber. A finite union over the fractional outer index proves joint finite support of the two actual mode-index summands, and QReadoutSupported holds for every finite outer cutoff. This support comes from the full Hahn expansions and does not assert that an ordered half or a numerator monomial has the complete field's locality cutoff.

Before distributing the outer readout over the finite numerator expansion, the proof establishes joint finite support over alpha, the numerator exponent, the fractional outer offset and the mode-convolution index for each of the two full orders. The finite-support hypotheses of mathlib's finsum_sum_comm then justify both interchanges. The actual scalar nested-Q value is consequently the explicit finite sum of the complete outer rational readouts of these terms. The local Taylor index inside each signed monomial residue is still in its finite binomial sum.

For the actual fields A and Bj and their supplied independent locality order H, the complete field is first padded to max(H,L+M+K). The arbitrary-cutoff slice quotient theorem then transports the actual readout to the original P/Q_K. Only after that padding does the finite rational evaluation enter the proof. The theorem retains arbitrary input tensor, functional, signed indices and lifts, zero numerator and empty inner sums; it also transports the complete OuterQCompletion law at H.

The sharp joint local Taylor support alpha+a+k=M-j-1 and alpha+a+beta+b=degree, its final z exponent -n-1, the complete outer Laurent collision and the two Vandermonde contractions remain to be established. In particular this result does not yet prove current_second_source_local_taylor, the reverse third conjunct, the full forward equality or sameNumeratorCollisionBridge. finite_reverse_outer_taylor at t=M-1 is the later finite algebra consumer.

The signed Laurent proof adapts the J/A calculation in LatticeHalfFockOuterTaylorEvaluation to J/B; the Hahn, Laurent and binomial infrastructure is from mathlib under Apache 2.0. The actual supplier closure is inherited research source, including the six additional owners and four modified older owners disclosed with the slice quotient checkpoint. It is not asserted to be an independently integrated dev API. The matching Reg source reconstructs the whole theorem and its positive actual law; the remaining family variation, sensitivity, observational dependence and final registration are unfinished.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_current_second_source_rational_field`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation](../LatticeHalfFockOuterTaylorEvaluation.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction](ContextualKernelExtraction.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient](LatticeHalfFockSliceQuotient.md)

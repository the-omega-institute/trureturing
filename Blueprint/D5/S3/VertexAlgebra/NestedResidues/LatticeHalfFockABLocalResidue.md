# Complete A/B Laurent residues

## Abstract

Complete source/source local residues in the original nested-Q coordinates.

The original variable labels are y=J, v=A, z=B. The finite ternary Laurent numerator is P and its denominator is (y-v)^L (y-z)^M (v-z)^K. All numerator exponents and collision weights are signed. The source/source local coordinate is v=z+t; y remains a spectator. Complete local rational residues are formed before the finite monomial expansion. These results establish local rational dependencies of the middle actual-Q equation; the actual finite-qField identification, complete joint outer support and final same-numerator Taylor equation remain additional obligations.

**Theorem 1.1 (Signed A/B residue and both complete remaining orders).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.ab_complete_remaining_orders`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.ab_complete_remaining_orders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

A signed monomial has local factors (z+t)^b and (y-z-t)^(-L), together with the unchanged independent pole (y-z)^(-M) and local power t^(w-K). The existing signed Laurent-pair residue theorem evaluates its complete residue on the finite antidiagonal u+v=K-w-1. For w at least K the residue is zero. Summing the original finite numerator support retains zero polynomials, negative total degrees and all signed spectators.

The complete binary rational G is the finite fractional sum of these ordinary residues, each multiplied by the original Laurent mode shift z^(-ell). Its two remaining Hahn orders are [y,z] and [z,y]. Their exact coefficients give the two source/source lastSourceLocalQ values, with independent fractional cutoff I. No unsupported infinite interchange or locality assertion on a monomial is used.

**Theorem 1.2 (Compatibility of complete local fractional cutoffs).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.actual_ab_local_cutoff_compat`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.actual_ab_local_cutoff_compat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Arbitrary supplied actual homogeneous numerators P,K and P1,K1 define the same rational quotient by actual_slice_quotient_compat. Each complete A/B rational residue has zero tail at its own denominator order. Padding both finite local fractional sums to max K K1 therefore proves equality of their complete local truncations. The actual input, covector, all signed indices and the original homogeneous coefficient equation remain in scope. This compares local rational truncations; it does not by itself compare actual finite qFields.

**Theorem 1.3 (A binary Laurent numerator at the original pole bound).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.ab_complete_pole_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.ab_complete_pole_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For the same P,K and any I, G is a binary Laurent numerator divided by (y-z)^(L+M+(K-w-1).toNat). At w=r+j this is the required L+M+(K-r-j-1).toNat bound. Each local antidiagonal term has an additional pole of order at most K-w-1; multiplying by the stated power leaves a Laurent polynomial on the unchanged remaining labels. Finite numerator and fractional sums preserve this property. No replacement numerator or global caller-K locality premise is assumed.

The faithful dependent source reconstructions in the Reg mirror compile, but the four-slot audits remain unfinished at issue #20163. Whole-family variation, sensitivity, observational dependence and the final sourceSelection/escapeFrom binding are not supplied; no declared_validated registration is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.ab_complete_pole_bound`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.ab_complete_remaining_orders`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.actual_ab_local_cutoff_compat`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation](../LatticeHalfFockOuterTaylorEvaluation.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient](LatticeHalfFockSliceQuotient.md)

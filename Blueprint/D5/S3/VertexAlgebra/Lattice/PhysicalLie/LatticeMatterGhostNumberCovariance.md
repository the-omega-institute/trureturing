# All-state number covariance of the original matter-ghost modes

## Abstract

All-state number covariance of the original matter-ghost modes

The operators are the original bc occupation ghostNumber and the tensor operator N = tensorNumber D, acting on State D. The field is the original occupation-word state-field map, and mu_n = originalMode D n. Write B_j = ghostB D j, P for the actual parity, and K(x,y) = mu_0(B_(-1)x,y). All five public statements retain their original telescopes; no H, inverse-Gram or rank-26 hypothesis occurs.

LatticeData retains exactly its rank, integral symmetric Gram matrix and even diagonal. The signed site weight is the original odd-minus-even occupation count, not a replacement number convention. Pointwise finite ghost words and tensor convolutions prove statements for every integer mode and every actual state; no uniform truncation, positivity, nonzero-rank or fixed-charge premise is assumed.

Source-specific four-slot Reg audits for the public theorems remain unfinished: https://github.com/the-omega-institute/trureturing/issues/29596. Adjacent templates do not supply the complete original telescopes, source selections and checked escape coordinates for these owners. No declared_validated registration is claimed; this delivery uses the explicit linked-issue exception.

**Theorem 1.1 (Number covariance for every original ghost field).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.ghost_number_field`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.ghost_number_field` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any a in the original bc occupation Fock space and integer n, ghostNumber * (Y(a)[[n]]) - (Y(a)[[n]]) * ghostNumber = Y(ghostNumber a)[[n]]. Signed normal products add the original occupation weights; divided derivatives retain each generator weight. Induction through the actual sorted occupation word, then linear extension from ket states, covers all ghost states. No homogeneous a is assumed.

**Theorem 1.2 (Full-state covariance at every integer tensor mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.number_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.number_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData, x,y : State D and integer n, N(mu_n(x,y)) = mu_n(Nx,y) + mu_n(x,Ny). Here N = tensorNumber D and mu_n = originalMode D n. The ghost-field commutator passes through the actual matter/ghost tensor coefficient and its pointwise finite convolution. Both inputs may mix ghost numbers, momenta and energies; there is no matrix, critical-rank, Gram-inverse or parity hypothesis.

**Theorem 1.3 (The original lowering law on actual tensor states).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.number_b_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.number_b_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, integer m and x : State D, N(B_m x) = B_m(Nx) - B_m x. This directly reuses the native N_b operator relation from the original relative BRST module. Its live consumer current_number uses it together with number_mode; no new grading axiom is assumed.

**Theorem 1.4 (The unsigned current has integer degree minus one).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.current_number`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.current_number` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, x,y : State D and p,q : Int, if Nx = (p : Complex) times x and Ny = (q : Complex) times y, then N(K(x,y)) = ((p+q-1 : Int) : Complex) times K(x,y). The exact original lowering relation for B_(-1) and all-integer number_mode give the result. Negative degrees, zero states and all original lattice charges remain included.

**Theorem 1.5 (Ghost number one implies actual odd parity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.number_one_parity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.number_one_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and original state x, Nx = x implies Px = -x. In the finite support of fullBasis.repr x, each nonzero coefficient has integer ghost charge one. The original odd-minus-even occupation count forces odd total occupation cardinality, hence actual parity -1. Matter states may be mixed; no restriction to a pure tensor, a charge sector, a positive Gram form or nonzero rank is made.

Attribution remains with the original ghost construction, Scott Carnahan's signed residue calculus and Mathlib. The result supplies actual number covariance and number-one parity for later current arguments. It does not provide a positive physical form, a no-ghost theorem, a complete string model, spacetime reconstruction, AdS/CFT or a literature novelty claim.

Direct mathematical suppliers: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading`; `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder`

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.current_number`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.ghost_number_field`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.number_b_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.number_mode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance.number_one_parity`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder](../LatticeBRSTCohomologyBVSecondOrder.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading](../LatticeBRSTCohomologyGhostGrading.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder](../LatticeBRSTCohomologyBVSecondOrder.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading](../LatticeBRSTCohomologyGhostGrading.md)

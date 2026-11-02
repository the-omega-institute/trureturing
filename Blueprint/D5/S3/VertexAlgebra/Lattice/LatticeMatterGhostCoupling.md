# The native algebraic lattice matter-ghost coupling

## Abstract

The native algebraic lattice matter-ghost coupling

The carrier is the original all-charge lattice carrier tensor over the complex numbers with the original countable occupation ghost Fock space. The quadratic matter modes are the actual Sugawara field coefficients at m+1. No inverse-Gram equations are needed for construction or the two Ward identities. This is the classical matter term of the algebraic BRST construction; no mathematical or physical novelty is asserted.

**Definition 1.1 (The original algebraic tensor carrier).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.State`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every lattice data D, State D is Carrier D tensor over the complex numbers with the original countable occupation Fock carrier. No charge sector, finite prefix or completed tensor product replaces either factor.

**Definition 1.2 (The original b lift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostB`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D and integer r, ghostB D r is the tensor map id tensor BcGhostFock.b r on State D.

**Definition 1.3 (The original c lift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostC`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D and integer r, ghostC D r is the tensor map id tensor BcGhostFock.c r on State D.

**Definition 1.4 (The actual Sugawara lift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.matterMode`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.matterMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D, complex matrix H and integer r, matterMode D H r is sugawaraMode D H r tensor id on State D. The original matter field coefficient is taken at r+1.

**Definition 1.5 (The original ghost Virasoro lift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostVirasoro`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostVirasoro` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D and integer r, ghostVirasoro D r is id tensor BcGhostVirasoro.L r. L is the original pointwise locally finite normal ordered ghost action.

**Definition 1.6 (The original matter-c action family).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.summand`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.summand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,H and integer m, summand D H m is sugawaraMode D H m tensor BcGhostFock.c (-m), equivalently the product M_m C_{-m}. Its action on each state is proved finitely supported before T is defined.

**Definition 1.7 (The actual integer field cutoff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.upper`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.upper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,H and matter state v, upper D H v is max(0,-order(sugawaraField D H applied to v)-2), after the canonical HahnModule identification. The order is integer-valued. The exponent -m-2 comes from the original vertex coefficient m+1.

**Definition 1.8 (The pointwise locally finite coupling).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary lattice data D and complex matrix H, T acts on x as the finite-support sum over integers m of the tensor map L_m tensor c_{-m}. The endomorphism family itself is never finitely summed. Additivity and scalar compatibility follow from pointwise finite supports.

**Theorem 1.9 (Finiteness on every algebraic tensor state).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.summand_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.summand_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H,x, the action family m maps to (L_m tensor c_{-m})x has finite support. On a simple tensor v tensor w in ghost radius A, its support lies in [-A,U(v)]. U(v)=max(0,-order(Y_H(v))-2) comes from actual VertexOperator truncation at coefficient m+1. Tensor induction extends the result to every algebraic tensor state.

**Theorem 1.10 (Equality with the actual operator-product local sum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every tensor state x, T x equals the pointwise finite sum of (M_m C_{-m})x, with M and C the original tensor lifts. This is a formula for a linear map already constructed from state actions.

**Theorem 1.11 (Cutoff independence).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.finite_capture`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.finite_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite set containing the support of the state-action family, its finite sum equals T x. Two valid captures consequently compute the same vector.

**Theorem 1.12 (Joint capture of all prescribed intermediates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.common_capture`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.common_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite collection X of tensor states has one finite mode set containing every summand support on X. Taking the finite union also handles sums, scalar multiples and intermediate ghost and matter actions.

**Theorem 1.13 (The actual simple-tensor finite formula).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lattice state v and ghost state w in radius A at least two, T(v tensor w) is the sum over m in [-A,U(v)] of L_m v tensor c_{-m}w. Both endpoints are proved from the original operators.

**Theorem 1.14 (All-integer b Ward identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ward_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ward_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary D,H and every integer r, T B_r+B_r T=M_r. The CAR contraction is at the matter index m=r. The summation passes through B_r using the genuine finite supports on x and B_r x.

**Theorem 1.15 (All-integer c Ward identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ward_c`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ward_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary D,H and every integer r, T C_r+C_r T=0. The proof uses the original c CAR and finite support on x and C_r x, with no desired identity assumed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.State`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.common_capture`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.finite_capture`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostB`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostC`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostVirasoro`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.matterMode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.summand`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.summand_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.upper`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ward_b`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ward_c`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostOccupationRadius](../../Quantum/Fermionic/BcGhostOccupationRadius.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraVirasoro](../LatticeSugawaraVirasoro.md)

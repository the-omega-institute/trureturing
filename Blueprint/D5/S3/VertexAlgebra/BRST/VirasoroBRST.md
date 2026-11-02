# General Virasoro matter and the original bc BRST charge

## Abstract

The signed original bc BRST anomaly for lower-truncated Virasoro matter

MatterDatum has exactly the original mode family, central charge, integer Virasoro commutator and statewise positive-mode truncation. V is any complex module and State V is exactly V tensor the original countable bc occupation Fock space. No Ward identity, covariance, degree, square, support, positivity or vacuum conclusion is assumed. The charge Q is T plus the identity tensor the native ghost cubic Qg; N is the native ghost number.

T sums matterMode m times c(-m) only after evaluation on a state. Genuine matter lower truncation and the native ghost occupation radius give finite support. Translated paired finite sums have coefficients k-2r and 2r-k; the original Virasoro central singleton at -r survives their cancellation. The finite pure-c Ward operator R commutes with T using a common capture of x and R x. The remaining square residual has degree two and commutes with all original b and c modes, so the charged tensor commutant annihilates it.

The twenty public theorem source-family audits remain unfinished; see https://github.com/the-omega-institute/trureturing/issues/25671 for the exact targets and native statement identities. Empty registration inventory and empty error arrays do not validate an audit. The missing evidence is a lawful enrolled readout and exact polymorphic realization bridge, with actual-positive law, whole-family variation, fixed-other sensitivity and observational dependence proofs.

**Theorem 1.1 (summand finite).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.summand_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.summand_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, summand_finite (x : State V) : Function.HasFiniteSupport (fun m : ℤ => summand A m x).

**Theorem 1.2 (T apply).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.T_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.T_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, T_apply (x : State V) : T A x = ∑ᶠ m : ℤ, (matterMode A m * ghostC A (-m)) x.

**Theorem 1.3 (finite capture).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.finite_capture`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.finite_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, finite_capture (x : State V) (s : Finset ℤ) (hs : Function.support (fun m : ℤ => summand A m x) ⊆ (s : Set ℤ)) : T A x = ∑ m ∈ s, summand A m x.

**Theorem 1.4 (common capture).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.common_capture`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.common_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, common_capture (X : Finset (State V)) : ∃ s : Finset ℤ, ∀ x ∈ X, Function.support (fun m : ℤ => summand A m x) ⊆ (s : Set ℤ).

**Theorem 1.5 (number T).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.number_T`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.number_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, number_T : number (V := V) * T A - T A * number (V := V) = T A.

**Theorem 1.6 (ward b).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.ward_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.ward_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, ward_b (r : ℤ) : T A * ghostB A r + ghostB A r * T A = matterMode A r.

**Theorem 1.7 (ward c).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.ward_c`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.ward_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, ward_c (r : ℤ) : T A * ghostC A r + ghostC A r * T A = 0.

**Theorem 1.8 (matter covariance apply).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.matter_covariance_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.matter_covariance_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, matter_covariance_apply (r : ℤ) (x : State V) : (T A * matterMode A r - matterMode A r * T A) x = (∑ᶠ k : ℤ, ((k-2*r : ℤ) : ℂ) • paired A r k x) + (-((A.centralCharge / 12) * ((r : ℂ)^3-r))) • ghostC A r x.

**Theorem 1.9 (ghost covariance apply).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.ghost_covariance_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.ghost_covariance_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, ghost_covariance_apply (r : ℤ) (x : State V) : (T A * ghostVirasoro A r - ghostVirasoro A r * T A) x = ∑ᶠ k : ℤ, ((2*r-k : ℤ) : ℂ) • paired A r k x.

**Theorem 1.10 (covariance).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, covariance (r : ℤ) : T A * (matterMode A r + ghostVirasoro A r) - (matterMode A r + ghostVirasoro A r) * T A = (-((A.centralCharge / 12) * ((r : ℂ)^3-r))) • ghostC A r.

**Theorem 1.11 (Q ward b).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_ward_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_ward_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, Q_ward_b (r : ℤ) : Q A * ghostB A r + ghostB A r * Q A = Ltotal A r.

**Theorem 1.12 (Q ward c).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_ward_c`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_ward_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, Q_ward_c (r : ℤ) : Q A * ghostC A r + ghostC A r * Q A = ghostR A r.

**Theorem 1.13 (Q R).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_R`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, Q_R (r : ℤ) : Q A * ghostR A r - ghostR A r * Q A = 0.

**Theorem 1.14 (Q Ltotal).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_Ltotal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_Ltotal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, Q_Ltotal (r : ℤ) : Q A * Ltotal A r - Ltotal A r * Q A = (((26-A.centralCharge) / 12) * ((r : ℂ)^3-r)) • ghostC A r.

**Theorem 1.15 (N Q).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.N_Q`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.N_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, N_Q : N A * Q A - Q A * N A = Q A.

**Theorem 1.16 (residual b).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.residual_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.residual_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, residual_b (r : ℤ) : residual A * ghostB A r = ghostB A r * residual A.

**Theorem 1.17 (residual c).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.residual_c`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.residual_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, residual_c (r : ℤ) : residual A * ghostC A r = ghostC A r * residual A.

**Theorem 1.18 (square anomaly).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.square_anomaly`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.square_anomaly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, square_anomaly : Q A ^ 2 = ((26-A.centralCharge) / 26) • ghostSquareAnomaly A.

**Theorem 1.19 (square finite).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.square_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.square_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, square_finite (x : State V) : Function.HasFiniteSupport (fun n : ℤ => (((A.centralCharge-26) / 24) * ((n : ℂ)^3-n)) • ((ghostC A (-n) * ghostC A n) x)).

**Theorem 1.20 (square apply).**

Lean statement: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.square_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/VirasoroBRST.square_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V : Type u, [AddCommGroup V], [Module Complex V], and A : MatterDatum V, square_apply (x : State V) : (Q A ^ 2) x = ∑ᶠ n : ℤ, (((A.centralCharge-26) / 24) * ((n : ℂ)^3-n)) • ((ghostC A (-n) * ghostC A n) x).

The operator formula scales the native ghost square by (26-centralCharge)/26. Its pointwise form retains all signed integer n and the coefficient (centralCharge-26)/24 times (n cubed minus n) multiplying c(-n)c(n). An anonymous transient check instantiates arbitrary lattice rank using both inverse-Gram identities and the accepted Hahn-order truncation, identifies the actual original lattice T and Q, and applies this general square formula. Critical central charge 26 is checked transiently and introduces no retained specialization. This is algebraic BRST mathematics; it does not complete Monster moonshine, construct BRST cohomology or establish a physical VOA/CFT, string model or AdS/CFT correspondence.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.N_Q`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_Ltotal`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_R`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_ward_b`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.Q_ward_c`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.T_apply`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.common_capture`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.covariance`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.finite_capture`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.ghost_covariance_apply`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.matter_covariance_apply`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.number_T`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.residual_b`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.residual_c`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.square_anomaly`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.square_apply`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.square_finite`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.summand_finite`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.ward_b`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/VirasoroBRST.ward_c`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostBRSTDegree](../../Quantum/Fermionic/BcGhostBRSTDegree.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostChargeTensor](../../Quantum/Fermionic/BcGhostChargeTensor.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostOccupationRadius](../../Quantum/Fermionic/BcGhostOccupationRadius.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostSquare](../../Quantum/Fermionic/BcGhostSquare.md)

# Exact Conditioning Certificate

## Abstract

The matrix defect of finite record conditioning vanishes exactly, without a tolerance term.

**Theorem 1.1 (The conditioning certificate defect vanishes exactly).**

$$\forall n,\kappa\ [\operatorname{Fintype}(n)]\ [\operatorname{Fintype}(\kappa)],\\\forall P: \kappa\to M_{n}(\mathbb{C}),\ \rho\in M_{n}(\mathbb{C}),\\\operatorname{Record}(P) \land \operatorname{PosSemidef}(\rho) \Rightarrow\\d_{P}(\rho)=0,\quad d_{P}(\rho):=U_{P}(\rho)-\sum_{k\in\kappa}w_{k}(\rho)\cdot \rho_{k}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ConditioningCertificate.certificate_identity_zero_tolerance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a finite complete family of pairwise orthogonal self-adjoint projections and let rho be positive semidefinite. Define the certificate defect as the unread matrix minus the record-weighted ensemble of the totalized conditional branches. Zero-weight branches cause no residual because their positive compressed blocks vanish. The established weighted-ensemble identity therefore makes the matrix-valued defect exactly zero; no norm, error bound, or approximation parameter is introduced.

## References

- Truth anchor: `D5/S3/Observer/ConditioningCertificate.certificate_identity_zero_tolerance`
- Dependency: [D5/S3/Observer/Conditioning](Conditioning.md)

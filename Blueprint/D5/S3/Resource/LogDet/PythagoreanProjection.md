# Pythagorean Projection Certificates for Log-Det Divergence

## Abstract

A first-order certificate yields the log-determinant Pythagorean inequality, characterizes equality, and is invariant under invertible congruence.

The certificate is shaped like a first-order optimality condition. It records that sigma is a positive-definite member of the feasible set and that its inverse-difference pairing with every positive-definite feasible tau is nonpositive. This module uses that algebraic condition directly; it does not claim that an optimizer exists or is unique.

**Definition 1.1 (A log-det projection certificate is a feasible first-order certificate).**

$$\begin{gathered}\operatorname{IsLogDetProjectionCertificate}(C, \rho, \sigma) \Leftrightarrow \\ \sigma \in C \land \operatorname{PosDef}(\sigma) \land \\ \forall \tau \in C, \operatorname{PosDef}(\tau) \Rightarrow \Re{\operatorname{tr}((\sigma^{-1} - \tau^{-1}) (\rho - \sigma))} \le 0.\end{gathered}$$

*Formalization.* `D5/S3/Resource/LogDet/PythagoreanProjection.IsLogDetProjectionCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The universal inequality is exactly the remainder in the frozen three-point identity. Positive definiteness is required only for feasible comparison points used by the certificate.

**Definition 1.2 (The congruence image transforms every feasible matrix).**

$$\operatorname{congruenceImage}(T, C) = \{T A T^{H} \mid A \in C\}$$

*Formalization.* `D5/S3/Resource/LogDet/PythagoreanProjection.congruenceImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image set consists precisely of matrices T A T conjugate-transpose with A in the original feasible set.

**Theorem 1.3 (A log-det projection certificate implies the Pythagorean inequality).**

$$\begin{gathered}\operatorname{IsLogDetProjectionCertificate}(C, \rho, \sigma) \land \operatorname{PosDef}(\rho) \Rightarrow \\ \forall \tau \in C, \operatorname{PosDef}(\tau) \Rightarrow \\ \operatorname{logDetDivergence}(\rho, \sigma) + \operatorname{logDetDivergence}(\sigma, \tau) \le \operatorname{logDetDivergence}(\rho, \tau).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDet/PythagoreanProjection.pythagorean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen three-point identity rewrites the difference between the two sides as the certificate pairing. Its nonpositivity is exactly the stated Pythagorean inequality.

**Theorem 1.4 (Equality in the log-det Pythagorean law is orthogonality).**

$$\begin{gathered}\operatorname{PosDef}(\rho) \land \operatorname{PosDef}(\sigma) \land \operatorname{PosDef}(\tau) \Rightarrow \\ (\operatorname{logDetDivergence}(\rho, \sigma) + \operatorname{logDetDivergence}(\sigma, \tau) = \operatorname{logDetDivergence}(\rho, \tau)) \Leftrightarrow \\ \Re{\operatorname{tr}((\sigma^{-1} - \tau^{-1}) (\rho - \sigma))} = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDet/PythagoreanProjection.logDetDivergence_pythagorean_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rearranging the same three-point identity shows that equality holds exactly when the inverse-difference pairing vanishes. No optimizer interpretation is needed for this equivalence.

**Theorem 1.5 (Log-det projection certificates are invariant under invertible congruence).**

$$\begin{gathered}\operatorname{IsLogDetProjectionCertificate}(C, \rho, \sigma) \land \operatorname{IsUnit}(\operatorname{det}(T)) \Rightarrow \\ \operatorname{IsLogDetProjectionCertificate}(\operatorname{congruenceImage}(T, C), T \rho T^{H}, T \sigma T^{H}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDet/PythagoreanProjection.congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Invertible congruence preserves positive definiteness and feasible-set membership. Reversing the congruence products under inversion, cancelling T inverse times T, and cycling the trace show that the transformed pairing equals the original pairing, so the certificate inequality transports.

## References

- Truth anchor: `D5/S3/Resource/LogDet/PythagoreanProjection.IsLogDetProjectionCertificate`
- Truth anchor: `D5/S3/Resource/LogDet/PythagoreanProjection.congruence`
- Truth anchor: `D5/S3/Resource/LogDet/PythagoreanProjection.congruenceImage`
- Truth anchor: `D5/S3/Resource/LogDet/PythagoreanProjection.logDetDivergence_pythagorean_eq_iff`
- Truth anchor: `D5/S3/Resource/LogDet/PythagoreanProjection.pythagorean`
- Dependency: [D5/S3/Resource/LogDet/CongruenceGeometry](CongruenceGeometry.md)

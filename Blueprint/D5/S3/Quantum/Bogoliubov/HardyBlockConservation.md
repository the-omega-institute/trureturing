# Hardy Block Conservation

## Abstract

Hardy compression and leakage conserve the projected input norm.

**Theorem 1.1 (Hardy blocks conserve the input projection).**

$$T = PUP, H = {I - P}UP,\ P^{*} = P \land P^{2} = P \land U^{*}U = I \Rightarrow T^{*}T + H^{*}H = P.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Bogoliubov/HardyBlockConservation.hardy_block_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a finite-dimensional Hermitian idempotent and U an isometry. The compressed block T = PUP and complementary leakage block H = (I-P)UP satisfy the exact Gram identity T* T + H* H = P.

The proof uses the conjugate-transpose product, subtraction, and identity laws from Mathlib, then the projection and isometry hypotheses.

The source writes I on the right while displaying the blocks as ambient operators. In that ambient representation the correct right side is P; I is recovered only after restricting inputs to the range of P.

**Theorem 1.2 (Conservation is the identity on projected inputs).**

$$Pv = v \Rightarrow {T^{*}T + H^{*}H}v = v.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Bogoliubov/HardyBlockConservation.hardy_block_conservation_on_projected_input` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Pv = v, applying the ambient Gram sum to v gives v. This is the precise finite-dimensional version of the source identity on the selected Hardy input sector.

**Theorem 1.3 (A proper projection refutes the ambient identity).**

$$\exists P, T, H \in \mathcal{M}_{2}(\mathbb{C}),\ P \neq 0 \land P \neq I \land P^{*} = P \land P^{2} = P \land T = PIP \land H = {I - P}IP \land T^{*}T + H^{*}H = P \land T^{*}T + H^{*}H \neq I.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Bogoliubov/HardyBlockConservation.ambient_identity_rhs_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first-coordinate projection on C^2 is nonzero, differs from I, is Hermitian and idempotent, and with U = I makes the Gram sum equal P rather than I. This is a concrete counterexample to the unqualified ambient formulation.

## References

- Truth anchor: `D5/S3/Quantum/Bogoliubov/HardyBlockConservation.ambient_identity_rhs_counterexample`
- Truth anchor: `D5/S3/Quantum/Bogoliubov/HardyBlockConservation.hardy_block_conservation`
- Truth anchor: `D5/S3/Quantum/Bogoliubov/HardyBlockConservation.hardy_block_conservation_on_projected_input`

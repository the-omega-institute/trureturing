# The joint minus sector of commuting involutions

## Abstract

Independent sign reversals give a joint minus projector with exact trace.

Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.

**Theorem 1.1 (Exact trace and simultaneous minus eigenvalues).**

$$\forall I \in \mathit{Type},\; \forall Omega \in \mathit{Type},\; [\mathrm{Fintype}\left(I\right)] [\mathrm{Fintype}\left(\mathit{Omega}\right)] [\mathrm{DecidableEq}\left(\mathit{Omega}\right)] \forall B \in I \to \operatorname{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right),\; \forall U \in I \to \operatorname{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right),\; ((\forall i \in I,\; (\operatorname{Matrix}.\operatorname{IsHermitian}\left(\mathrm{val}\left(B, i\right)\right)) \land (\mathrm{val}\left(B, i\right) \cdot \mathrm{val}\left(B, i\right) = (1:\operatorname{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right)))) \land ((\forall i \in I,\; \forall j \in I,\; \mathrm{Commute}\left(\mathrm{val}\left(B, i\right), \mathrm{val}\left(B, j\right)\right)) \land ((\forall i \in I,\; \mathrm{val}\left(U, i\right) \cdot \mathrm{val}\left(U, i\right) = (1:\operatorname{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right))) \land ((\forall i \in I,\; \mathrm{val}\left(U, i\right) \cdot \mathrm{val}\left(B, i\right) = -\left(\mathrm{val}\left(B, i\right) \cdot \mathrm{val}\left(U, i\right)\right)) \land (\forall i \in I,\; \forall j \in I,\; (i \ne j) \Rightarrow (\mathrm{Commute}\left(\mathrm{val}\left(U, i\right), \mathrm{val}\left(B, j\right)\right))))))) \Rightarrow (\exists P \in \operatorname{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right),\; (\mathrm{IsStarProjection}\left(P\right)) \land ((\operatorname{Matrix}.\operatorname{trace}\left(P\right) = \frac{(\operatorname{Fintype}.\operatorname{card}\left(\mathit{Omega}\right):\mathit{Complex})}{(2:\mathit{Complex})^{\operatorname{Fintype}.\operatorname{card}\left(I\right)}}) \land ((\forall i \in I,\; \mathrm{val}\left(B, i\right) \cdot P = -P) \land (\forall Q \in \operatorname{Matrix}\left(\mathit{Omega}, \mathit{Omega}, \mathit{Complex}\right),\; (\forall i \in I,\; \mathrm{Commute}\left(Q, \mathrm{val}\left(B, i\right)\right)) \Rightarrow (\mathrm{Commute}\left(Q, P\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/JointSignProjectors.joint_sign_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The B operators are commuting Hermitian involutions. For each i, the involution U(i) reverses B(i) and commutes with every other B(j). The joint minus projection has trace card(Omega)/2^card(I). In particular it is nonzero when Omega is nonempty. It commutes with every matrix which commutes with all the B operators. The construction multiplies the commuting projections (1−B(i))/2. Induction inserts one factor at a time; conjugation by its sign reversal cancels the mixed trace, so each inserted factor halves the trace.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/JointSignProjectors.joint_sign_projection`

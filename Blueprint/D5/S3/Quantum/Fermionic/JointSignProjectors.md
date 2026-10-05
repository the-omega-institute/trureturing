# The joint minus sector of commuting involutions

## Abstract

Independent sign reversals give a joint minus projector with exact trace.

Type denotes an arbitrary type, Fintype its finite enumeration, and DecidableEq decidable equality. Complex denotes complex numbers. M(Omega) is Matrix Omega Omega Complex, Fun(I,M) is the function type I → M, and val applies a function. Matrix multiplication is written as a product. Matrix one is the identity and matrix zero is the zero matrix; neg is additive negation. IsHermitian means equality to the conjugate transpose, Commute(A,B) means AB=BA, and IsStarProjection(P) means P²=P and P*=P. trace is the matrix trace, card is finite-type cardinality, and asComplex displays the natural-to-complex cast. The division displayed below is division in Complex.

**Theorem 1.1 (Exact trace and simultaneous minus eigenvalues).**

$$\forall I \in \mathit{Type},\; \forall Omega \in \mathit{Type},\; [\mathrm{Fintype}\left(I\right)] [\mathrm{Fintype}\left(\mathit{Omega}\right)] [\mathrm{DecidableEq}\left(\mathit{Omega}\right)] \forall B \in \mathrm{Fun}\left(I, \mathrm{M}\left(\mathit{Omega}\right)\right),\; \forall U \in \mathrm{Fun}\left(I, \mathrm{M}\left(\mathit{Omega}\right)\right),\; ((\forall i \in I,\; (\mathrm{IsHermitian}\left(\mathrm{val}\left(B, i\right)\right)) \land (\mathrm{val}\left(B, i\right) \cdot \mathrm{val}\left(B, i\right) = (1:\mathrm{M}\left(\mathit{Omega}\right)))) \land ((\forall i \in I,\; \forall j \in I,\; \mathrm{Commute}\left(\mathrm{val}\left(B, i\right), \mathrm{val}\left(B, j\right)\right)) \land ((\forall i \in I,\; \mathrm{val}\left(U, i\right) \cdot \mathrm{val}\left(U, i\right) = (1:\mathrm{M}\left(\mathit{Omega}\right))) \land ((\forall i \in I,\; \mathrm{val}\left(U, i\right) \cdot \mathrm{val}\left(B, i\right) = \mathrm{neg}\left(\mathrm{val}\left(B, i\right) \cdot \mathrm{val}\left(U, i\right)\right)) \land (\forall i \in I,\; \forall j \in I,\; (i \ne j) \Rightarrow (\mathrm{Commute}\left(\mathrm{val}\left(U, i\right), \mathrm{val}\left(B, j\right)\right))))))) \Rightarrow (\exists P \in \mathrm{M}\left(\mathit{Omega}\right),\; (\mathrm{IsStarProjection}\left(P\right)) \land ((\mathrm{trace}\left(P\right) = \frac{\mathrm{asComplex}\left(\mathrm{card}\left(\mathit{Omega}\right)\right)}{\mathrm{asComplex}\left(2\right)^{\mathrm{card}\left(I\right)}}) \land ((\forall i \in I,\; \mathrm{val}\left(B, i\right) \cdot P = \mathrm{neg}\left(P\right)) \land (\forall Q \in \mathrm{M}\left(\mathit{Omega}\right),\; (\forall i \in I,\; \mathrm{Commute}\left(Q, \mathrm{val}\left(B, i\right)\right)) \Rightarrow (\mathrm{Commute}\left(Q, P\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/JointSignProjectors.joint_sign_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The B operators are commuting Hermitian involutions. For each i, the involution U(i) reverses B(i) and commutes with every other B(j). The joint minus projection has trace card(Omega)/2^card(I). In particular it is nonzero when Omega is nonempty. It commutes with every matrix which commutes with all the B operators. The construction multiplies the commuting projections (1−B(i))/2. Induction inserts one factor at a time; conjugation by its sign reversal cancels the mixed trace, so each inserted factor halves the trace.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/JointSignProjectors.joint_sign_projection`

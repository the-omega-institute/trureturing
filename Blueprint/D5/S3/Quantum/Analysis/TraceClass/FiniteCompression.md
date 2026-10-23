# Compression and discarded mass

## Abstract

Finite orthogonal compression in the trace-class Banach space.

**Definition 1.1 (Two-sided trace-class compression).**

$$\forall H \in CompleteComplexHilbertSpace, P \in \operatorname{BoundedComplexOperator}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{underlyingOperator}\left(\operatorname{compress}\left(P, rho\right)\right) = \operatorname{multiply}\left(\operatorname{multiply}\left(P, \operatorname{underlyingOperator}\left(rho\right)\right), P\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.compress` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

Compression sends rho to P rho P. The trace-ideal inequality bounds its trace norm by the square of the operator norm of P times the trace norm of rho. This constructs a continuous complex-linear map on the genuine trace-norm space.

**Definition 1.2 (Finite basis span).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, Complex, H\right), F \in \operatorname{Finset}\left(w\right),\; \operatorname{finiteSpan}\left(b, F\right) = \operatorname{span}\left(\operatorname{image}\left(b, F\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.finiteSpan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

The subspace is the complex span of the finite image of F under the full Hilbert basis b. It is finite dimensional even when the ambient space and basis index are arbitrary.

**Definition 1.3 (Discarded diagonal mass).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, Complex, H\right), F \in \operatorname{Finset}\left(w\right),\; \forall rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{tailMass}\left(b, F, rho\right) = \operatorname{sumOutside}\left(F, \operatorname{diagonal}\left(b, rho\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.tailMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

The real diagonal sum outside F retains all basis indices. For positive rho each summand is nonnegative, and the full diagonal has sum equal to the real trace.

**Theorem 1.4 (Finite-dimensional compression range).**

$$\forall H \in CompleteComplexHilbertSpace, U \in \operatorname{ComplexSubmodule}\left(H\right),\; \operatorname{FiniteDimensional}\left(U\right) \Rightarrow \operatorname{FiniteDimensional}\left(\operatorname{linearRange}\left(\operatorname{compress}\left(\operatorname{starProjection}\left(U\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.finiteDimensional_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

Every operator in the compression range is fixed by P on both sides. Restriction to U gives a linear map from this range into the endomorphisms of U. If the restriction is zero, x(y)=x(P y)=0 for every ambient vector y. Thus the restriction is injective and the range is finite dimensional with its inherited trace norm.

**Theorem 1.5 (One compact set of compressed unit-ball elements).**

$$\forall H \in CompleteComplexHilbertSpace, U \in \operatorname{ComplexSubmodule}\left(H\right),\; \operatorname{FiniteDimensional}\left(U\right) \Rightarrow \left(\exists K \in \operatorname{Set}\left(\operatorname{TraceClass}\left(H\right)\right),\; \operatorname{IsCompact}\left(K\right) \land \left(\forall rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{norm}\left(rho\right) \le 1 \Rightarrow \operatorname{member}\left(\operatorname{compress}\left(\operatorname{starProjection}\left(U\right), rho\right), K\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.exists_compact_compressions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

Take the image of the closed unit ball of the finite-dimensional compression range under its continuous inclusion into the trace-class space. Orthogonal projection has operator norm at most one, so every compressed trace-norm unit-ball element belongs to this compact image.

**Theorem 1.6 (Noncommuting trace-norm compression error).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, Complex, H\right), F \in \operatorname{Finset}\left(w\right),\; \forall rho \in \operatorname{TraceClass}\left(H\right),\; \left(0 \le \operatorname{underlyingOperator}\left(rho\right) \land \operatorname{Re}\left(\operatorname{trace}\left(rho\right)\right) = 1\right) \Rightarrow \operatorname{norm}\left(\operatorname{subtract}\left(rho, \operatorname{compress}\left(\operatorname{starProjection}\left(\operatorname{finiteSpan}\left(b, F\right)\right), rho\right)\right)\right) \le \operatorname{multiply}\left(2, \operatorname{sqrt}\left(\operatorname{tailMass}\left(b, F, rho\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.norm_sub_compress_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

For R equal to sqrt rho and Q equal to I-P, the column square sum of RQ is the discarded diagonal mass q. The adjoint column identity gives the same sum for QR, while the sum for PR is at most one. The operator identity rho-P rho P=(QR)R+(PR)(RQ), the Hilbert-Schmidt product trace-norm bound and the trace-norm triangle inequality give the bound 2 sqrt q. R is used as a Hilbert-Schmidt operator, with no assumption that it is trace class. P need not commute with rho.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.compress`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.exists_compact_compressions`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.finiteDimensional_range`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.finiteSpan`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.norm_sub_compress_le`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.tailMass`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy](SpectralEnergy.md)

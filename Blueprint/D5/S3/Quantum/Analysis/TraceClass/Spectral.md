# Full spectrum and faithful finite or Nat reference bases

## Abstract

Complete spectral representation of the original positive trace-class operator.

**Theorem 1.1 (Full nonnegative trace spectrum).**

$$\forall H \in \operatorname{CompleteComplexHilbertSpace}\left(\right),\; \forall T \in \operatorname{BoundedComplexOperator}\left(H\right),\; \left(0 \le T \land \operatorname{IsTraceClass}\left(T\right)\right) \Rightarrow \left(\exists w \in \operatorname{Set}\left(H\right),\; \exists b \in \operatorname{HilbertBasis}\left(w, \operatorname{Complex}\left(\right), H\right),\; \exists s \in \operatorname{Function}\left(w, \operatorname{Real}\left(\right)\right),\; \left(\forall i \in w,\; 0 \le s\left(i\right)\right) \land \left(\left(\forall i \in w,\; T\left(b\left(i\right)\right) = \operatorname{smul}\left(\operatorname{complexCast}\left(s\left(i\right)\right), b\left(i\right)\right)\right) \land \left(\operatorname{Summable}\left(s\right) \land \left(\operatorname{HasSum}\left(s, \operatorname{re}\left(\operatorname{trace}\left(T\right)\right)\right) \land \left(\operatorname{HasSum}\left(\operatorname{complexCastFamily}\left(s\right), \operatorname{trace}\left(T\right)\right) \land \left(\forall x \in H,\; \operatorname{HasSum}\left(\operatorname{weightedBasisTerms}\left(b, s, x\right), T\left(x\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Spectral.exists_nonneg_trace_spectral_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Compact self-adjoint spectral theorem and full Hilbert bases*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/Spectrum.lean>.

*Commentary.*

H is an arbitrary complete complex Hilbert space, T is its actual bounded complex-linear operator, and trace is the analytic trace with its genuine IsTraceClass proof. The conclusion constructs w as a set of vectors in H, a full Hilbert basis b indexed by w, and real eigenvalues s. Every eigenspace is retained, including zero. The real eigenvalues are summable, have sum Re(trace T), and their complex casts have sum trace T. For each x, the weighted terms are (b.repr x i * (s i : Complex)) smul b i and have actual sum T(x). No basis, compactness, spectral carrier, separability or countability assumption is an input.

**Theorem 1.2 (Faithful normalized reference).**

$$\forall H \in \operatorname{CompleteComplexHilbertSpace}\left(\right),\; \forall T \in \operatorname{BoundedComplexOperator}\left(H\right),\; \left(0 \le T \land \left(\operatorname{IsTraceClass}\left(T\right) \land \left(\operatorname{kernel}\left(T\right) = \operatorname{bottom}\left(\right) \land \operatorname{trace}\left(T\right) = 1\right)\right)\right) \Rightarrow \left(\exists w \in \operatorname{Set}\left(H\right),\; \exists b \in \operatorname{HilbertBasis}\left(w, \operatorname{Complex}\left(\right), H\right),\; \exists s \in \operatorname{Function}\left(w, \operatorname{Real}\left(\right)\right),\; \left(\left(\forall i \in w,\; 0 < s\left(i\right)\right) \land \left(\left(\forall i \in w,\; T\left(b\left(i\right)\right) = \operatorname{smul}\left(\operatorname{complexCast}\left(s\left(i\right)\right), b\left(i\right)\right)\right) \land \left(\operatorname{Summable}\left(s\right) \land \left(\operatorname{HasSum}\left(s, 1\right) \land \left(\operatorname{HasSum}\left(\operatorname{complexCastFamily}\left(s\right), 1\right) \land \left(\forall x \in H,\; \operatorname{HasSum}\left(\operatorname{weightedBasisTerms}\left(b, s, x\right), T\left(x\right)\right)\right)\right)\right)\right)\right)\right) \land \operatorname{Countable}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Spectral.exists_faithful_reference_spectral_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Compact self-adjoint spectral theorem and full Hilbert bases*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/Spectrum.lean>.

*Commentary.*

The kernel is the actual linear-map kernel. Strictly positive weights follow because a zero eigenvalue would put a norm-one basis vector in that trivial kernel. Real summability and positivity then make the full index countable. Both the real and complex sums equal one, and the weighted expansion converges to the original sigma(x). Faithfulness gives no bounded inverse or uniform spectral gap.

**Theorem 1.3 (Actual finite or Nat basis).**

$$\forall H \in \operatorname{CompleteComplexHilbertSpace}\left(\right),\; \forall T \in \operatorname{BoundedComplexOperator}\left(H\right),\; \left(0 \le T \land \left(\operatorname{IsTraceClass}\left(T\right) \land \left(\operatorname{kernel}\left(T\right) = \operatorname{bottom}\left(\right) \land \operatorname{trace}\left(T\right) = 1\right)\right)\right) \Rightarrow \left(\left(\exists n \in \operatorname{Nat}\left(\right),\; \exists b \in \operatorname{HilbertBasis}\left(\operatorname{Fin}\left(n\right), \operatorname{Complex}\left(\right), H\right),\; \exists s \in \operatorname{Function}\left(\operatorname{Fin}\left(n\right), \operatorname{Real}\left(\right)\right),\; \operatorname{FiniteDimensional}\left(\operatorname{Complex}\left(\right), H\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; 0 < s\left(i\right)\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; T\left(b\left(i\right)\right) = \operatorname{smul}\left(\operatorname{complexCast}\left(s\left(i\right)\right), b\left(i\right)\right)\right) \land \left(\operatorname{Summable}\left(s\right) \land \left(\operatorname{HasSum}\left(s, 1\right) \land \left(\operatorname{HasSum}\left(\operatorname{complexCastFamily}\left(s\right), 1\right) \land \left(\forall x \in H,\; \operatorname{HasSum}\left(\operatorname{weightedBasisTerms}\left(b, s, x\right), T\left(x\right)\right)\right)\right)\right)\right)\right)\right)\right) \lor \left(\exists w \in \operatorname{Set}\left(H\right),\; \exists c \in \operatorname{HilbertBasis}\left(w, \operatorname{Complex}\left(\right), H\right),\; \exists e \in \operatorname{Equiv}\left(w, \operatorname{Nat}\left(\right)\right),\; \exists b \in \operatorname{HilbertBasis}\left(\operatorname{Nat}\left(\right), \operatorname{Complex}\left(\right), H\right),\; \exists s \in \operatorname{Function}\left(\operatorname{Nat}\left(\right), \operatorname{Real}\left(\right)\right),\; \left(\forall i \in \operatorname{Nat}\left(\right),\; b\left(i\right) = c\left(\operatorname{inverseApply}\left(e, i\right)\right)\right) \land \left(\left(\forall i \in \operatorname{Nat}\left(\right),\; 0 < s\left(i\right)\right) \land \left(\left(\forall i \in \operatorname{Nat}\left(\right),\; T\left(b\left(i\right)\right) = \operatorname{smul}\left(\operatorname{complexCast}\left(s\left(i\right)\right), b\left(i\right)\right)\right) \land \left(\operatorname{Summable}\left(s\right) \land \left(\operatorname{HasSum}\left(s, 1\right) \land \left(\operatorname{HasSum}\left(\operatorname{complexCastFamily}\left(s\right), 1\right) \land \left(\forall x \in H,\; \operatorname{HasSum}\left(\operatorname{weightedBasisTerms}\left(b, s, x\right), T\left(x\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Spectral.faithful_reference_finite_or_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Compact self-adjoint spectral theorem and full Hilbert bases*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/Spectrum.lean>.

*Commentary.*

The finite branch returns a natural number n, an actual Hilbert basis indexed by Fin n, positive weights, finite-dimensionality, both trace sums and the original-operator vector series. In the infinite branch a genuine equivalence from the source full index to Nat transports a full Hilbert basis and all scalar sums; the transported basis has the same weighted operator representation. A finite basis is never padded by zero vectors.

Construction: choose a Hilbert basis in each closed complex eigenspace. Mathlib's orthogonal sigma-family theorem gives orthonormality. An ambient vector orthogonal to all these vectors is orthogonal to each full eigenspace by density; the compact symmetric spectral theorem makes it zero. HilbertBasis.mkOfOrthogonalEqBot therefore yields a full basis. Symmetry makes its eigenvalues real, and the nonnegative quadratic form makes them nonnegative. The accepted trace-class compactness theorem supplies compactness from the operator itself.

The analytic diagonal summability and positive trace-basis identity are the attributed Physlib suppliers in Library/QuantumBounds/diem2026traceclass.md. Rewriting the actual diagonal first establishes Summable s; only then is its real sum identified with the trace. Mapping b.hasSum_repr x through T proves the weighted series. This is a formal composition of standard spectral theory, not a new analytic spectral theorem or a solution of the entropy-continuity conjecture.

Boundary cases: zero on a nonseparable space retains its full zero eigenspace without a countability conclusion. A nonfaithful rank-one state does not satisfy the faithful adapter's kernel premise. Positive summable eigenvalues may tend to zero. These endpoints do not assert logarithmic energy, entropy identities, heat-trace finiteness or an unbounded Hamiltonian.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Spectral.exists_faithful_reference_spectral_data`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Spectral.exists_nonneg_trace_spectral_data`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Spectral.faithful_reference_finite_or_nat`
- Dependency: [D5/S3/Quantum/Analysis/CompactEigenbasis](../CompactEigenbasis.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Compact](Compact.md)

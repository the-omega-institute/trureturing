# Compact Symmetric Eigenbasis

## Abstract

Full real eigenbases of compact symmetric Hilbert operators over real or complex scalars.

**Theorem 1.1 (A full set-indexed eigenbasis with real eigenvalues).**

$$\forall k \in \operatorname{RCLikeScalar}\left(\right),\; \forall E \in \operatorname{CompleteHilbertSpace}\left(k\right),\; \forall T \in \operatorname{ContinuousLinearEnd}\left(k, E\right),\; \left(\operatorname{IsCompactOperator}\left(T\right) \land \operatorname{IsSymmetric}\left(T\right)\right) \Rightarrow \left(\exists w \in \operatorname{Set}\left(E\right),\; \exists b \in \operatorname{HilbertBasis}\left(w, k, E\right),\; \exists s \in \operatorname{Function}\left(w, \operatorname{Real}\left(\right)\right),\; \forall i \in w,\; T\left(b\left(i\right)\right) = \operatorname{smul}\left(\operatorname{scalarCast}\left(k, s\left(i\right)\right), b\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CompactEigenbasis.exists_setIndex_real_eigenbasis_rclike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Compact self-adjoint spectral theorem and full Hilbert bases*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/Spectrum.lean>.

*Commentary.*

For either real or complex scalars, let E be an arbitrary complete Hilbert space and T its actual compact symmetric continuous linear endomorphism. There exist a subset w of E, a full Hilbert basis b indexed by w, and a real family s such that T(b(i)) is the scalar cast of s(i) times b(i). Zero eigenspaces are retained. No positivity, trace-class, separability, countability or finite-dimensional hypothesis is imposed.

Choose a Hilbert basis in each closed eigenspace, including eigenvalue zero. Distinct eigenspaces are orthogonal. If a vector is orthogonal to the combined basis, density makes it orthogonal to each full eigenspace; the compact symmetric spectral theorem then makes it zero. This constructs a full Hilbert basis. Symmetry makes every eigenvalue real, and the actual range of that basis supplies the subset index.

The complex trace-class spectral representation uses the complex specialization. The real mean-zero boundary covariance uses the real specialization before deriving positivity, ordered infinite modes and multiplicities from its own hypotheses. These applications share the same complete eigenbasis construction.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CompactEigenbasis.exists_setIndex_real_eigenbasis_rclike`

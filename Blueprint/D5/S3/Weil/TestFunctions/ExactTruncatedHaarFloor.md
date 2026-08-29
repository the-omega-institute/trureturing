# Exact Truncated Haar Floor

## Abstract

A represented Hermitian truncated circle moment vector has exact normalized-Haar floor equal to its least Toeplitz eigenvalue.

**Theorem 1.1 (Exact truncated Haar floor).**

$$\forall N \in \mathbb{N}, m \in \mathbb{Z} \to \mathbb{C}, R \in \mathbb{R},\; \left(\left(\left(\left(\left(\left(\left(\left(\forall ell \in \mathbb{Z},\; m\left(\operatorname{neg}\left(ell\right)\right) = \operatorname{star}\left(m\left(ell\right)\right)\right) \land m\left(0\right) = \operatorname{toComplex}\left(R\right)\right) \land 0 < R\right) \land \left(\exists mu \in \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right),\; \forall ell \in \mathbb{Z},\; \operatorname{natAbs}\left(ell\right) \le N \Rightarrow \operatorname{integral}\left(z, \operatorname{Circle}\left(\right), \operatorname{zpow}\left(z, \operatorname{neg}\left(ell\right)\right), mu\right) = m\left(ell\right)\right)\right) \land \operatorname{let} T = \operatorname{Matrix}\left((j,k\in\operatorname{Fin}\left(N + 1\right) \mapsto m\left(\operatorname{toInt}\left(j\right) - \operatorname{toInt}\left(k\right)\right))\right)\right) \land \operatorname{let} hT = \operatorname{hermitianToeplitz}\left(m, \forall ell \in \mathbb{Z},\; m\left(\operatorname{neg}\left(ell\right)\right) = \operatorname{star}\left(m\left(ell\right)\right)\right): \operatorname{IsHermitian}\left(T\right)\right) \land \operatorname{let} A = \left\{\exists mu \in \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right),\; \left(\forall ell \in \mathbb{Z},\; \operatorname{natAbs}\left(ell\right) \le N \Rightarrow \operatorname{integral}\left(z, \operatorname{Circle}\left(\right), \operatorname{zpow}\left(z, \operatorname{neg}\left(ell\right)\right), mu\right) = m\left(ell\right)\right) \land \operatorname{toMeasure}\left(\operatorname{smul}\left(alpha, \operatorname{normalizedCircleHaar}\left(\right)\right)\right) \le \operatorname{toMeasure}\left(mu\right) \mid alpha \in \operatorname{NonnegativeReal}\left(\right)\right\}\right) \land \operatorname{let} alphaN = \operatorname{sSup}\left(A\right)\right) \Rightarrow \operatorname{toReal}\left(alphaN\right) = \operatorname{lambdaMin}\left(T, hT\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/ExactTruncatedHaarFloor.exact_truncated_haar_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Toeplitz matrix and feasible floor set are constructed directly from the supplied truncated moment data and normalized circle Haar measure.

The forward bound subtracts any dominated Haar component and uses positivity of the residual Toeplitz matrix. For the reverse bound, a local finite trigonometric-moment proof constructs a positive atomic circle measure from the positive semidefinite shifted Toeplitz matrix.

The positive zeroth moment bounds the feasible floors, so their supremum is well-defined and equals the least ordered Hermitian eigenvalue.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/ExactTruncatedHaarFloor.exact_truncated_haar_floor`
- Dependency: [D5/S3/Weil/TestFunctions/ToeplitzContactSupport](ToeplitzContactSupport.md)
- Dependency: [D5/S3/Weil/TestFunctions/TruncatedCircleMomentBridge](TruncatedCircleMomentBridge.md)

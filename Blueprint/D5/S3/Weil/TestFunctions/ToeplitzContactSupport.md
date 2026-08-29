# Toeplitz Contact Support

## Abstract

A contact eigenvector localizes a Toeplitz residual on finitely many polynomial zeros.

**Theorem 1.1 (Toeplitz contact support).**

$$\forall N \in \mathbb{N}, mu \in \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right), sigma \in \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right), alpha \in \operatorname{NonnegativeReal}\left(\right), v \in \operatorname{Fin}\left(N + 1\right) \to \mathbb{C},\; \left(\left(\left(\left(\left(mu = \operatorname{smul}\left(alpha, \operatorname{normalizedCircleHaar}\left(\right)\right) + sigma \land \operatorname{let} m = (ell:\mathbb{Z} \mapsto \operatorname{integral}\left(z, \operatorname{Circle}\left(\right), \operatorname{zpow}\left(z, \operatorname{neg}\left(ell\right)\right), mu\right))\right) \land \operatorname{let} T = \operatorname{Matrix}\left((j,k\in\operatorname{Fin}\left(N + 1\right) \mapsto m\left(j - k\right))\right)\right) \land \operatorname{let} q = \operatorname{sum}\left(j, \operatorname{Fin}\left(N + 1\right), \operatorname{monomial}\left(v\left(j\right), j\right)\right)\right) \land \operatorname{dotProduct}\left(\operatorname{star}\left(v\right), v\right) = 1\right) \land \operatorname{mulVec}\left(T, v\right) = \operatorname{smul}\left(\operatorname{toComplex}\left(alpha\right), v\right)\right) \Rightarrow \left(\left(\operatorname{support}\left(sigma\right) \subseteq \left\{\operatorname{eval}\left(q, z\right) = 0 \mid z \in \operatorname{Circle}\left(\right)\right\} \land \operatorname{natDegree}\left(q\right) \le N\right) \land \left(\exists M \in \mathbb{N}, point \in \operatorname{Fin}\left(M\right) \to \operatorname{Circle}\left(\right), weight \in \operatorname{Fin}\left(M\right) \to \operatorname{ExtendedNonnegativeReal}\left(\right),\; \left(\left(\left(M \le \operatorname{natDegree}\left(q\right) \land \left(\forall r \in \operatorname{Fin}\left(M\right),\; \operatorname{eval}\left(q, point\left(r\right)\right) = 0\right)\right) \land \left(\forall r \in \operatorname{Fin}\left(M\right),\; weight\left(r\right) \ne \operatorname{infinity}\left(\right)\right)\right) \land sigma = \operatorname{sum}\left(r, \operatorname{Fin}\left(M\right), \operatorname{smul}\left(weight\left(r\right), \operatorname{dirac}\left(point\left(r\right)\right)\right)\right)\right) \land mu = \operatorname{smul}\left(alpha, \operatorname{normalizedCircleHaar}\left(\right)\right) + \operatorname{sum}\left(r, \operatorname{Fin}\left(M\right), \operatorname{smul}\left(weight\left(r\right), \operatorname{dirac}\left(point\left(r\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/ToeplitzContactSupport.toeplitz_contact_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fourier moments, Toeplitz matrix, and analytic contact polynomial are constructed from the supplied completion measure and coefficient vector.

Normalized-Haar monomial orthogonality turns the contact eigenvector equation into a zero residual quadratic integral. The residual support is therefore contained in the contact zero set.

The polynomial is nonzero because the coefficient vector is unit. Its circle roots are finite, have cardinality at most its degree, and enumerate both the residual Dirac sum and the full optimizer decomposition.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/ToeplitzContactSupport.toeplitz_contact_support`
- Dependency: [D5/S3/Weil/Budget/FullCirclePrimalAttainment](../Budget/FullCirclePrimalAttainment.md)

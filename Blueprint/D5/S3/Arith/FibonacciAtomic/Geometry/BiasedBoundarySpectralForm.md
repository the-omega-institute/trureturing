# The Actual Boundary Spectral Form

## Abstract

The actual paired real Hilbert bases identify the original free-root energy on every vector of its form domain.

**Theorem 1.1 (Weighted Energy and Spectral Support on the Original Form Domain).**

$$\exists b: \operatorname{HilbertBasis}\left(\operatorname{Nat}\left(\right), \operatorname{Real}\left(\right), G_0\right), (\exists k: \operatorname{HilbertBasis}\left(\operatorname{Nat}\left(\right), \operatorname{Real}\left(\right), \operatorname{K}\left(\right)\right), (\exists mu: \operatorname{Nat}\left(\right)\to\operatorname{Real}\left(\right), ((\forall i: \operatorname{Nat}\left(\right), (0< \operatorname{apply}\left(mu, i\right)))\land (\operatorname{Antitone}\left(mu\right))\land (\operatorname{Tendsto}\left(mu, \operatorname{atTop}\left(\right), \operatorname{nhds}\left(0\right)\right))\land (\operatorname{Monotone}\left(\lambda i: \operatorname{Nat}\left(\right), (\operatorname{apply}\left(mu, i\right))^{-1}\right))\land (\operatorname{Tendsto}\left(\lambda i: \operatorname{Nat}\left(\right), (\operatorname{apply}\left(mu, i\right))^{-1}, \operatorname{atTop}\left(\right), \operatorname{atTop}\left(\right)\right))\land (\forall i: \operatorname{Nat}\left(\right), (\operatorname{pair}\left(\operatorname{val}\left(\operatorname{apply}\left(b, i\right)\right), \operatorname{smul}\left((\operatorname{apply}\left(mu, i\right))^{-1}, \operatorname{val}\left(\operatorname{apply}\left(b, i\right)\right)\right)\right)\in \operatorname{graph}\left(\operatorname{boundaryOperator}\left(\right)\right)))\land (\forall i: \operatorname{Nat}\left(\right), (\operatorname{Sigma}\left(\operatorname{val}\left(\operatorname{apply}\left(k, i\right)\right)\right)=\operatorname{smul}\left(\operatorname{apply}\left(mu, i\right), \operatorname{val}\left(\operatorname{apply}\left(k, i\right)\right)\right)))\land (\forall i: \operatorname{Nat}\left(\right), (\operatorname{C}\left(\operatorname{val}\left(\operatorname{apply}\left(k, i\right)\right)\right)=\operatorname{smul}\left(\operatorname{sqrt}\left(\operatorname{apply}\left(mu, i\right)\right), \operatorname{val}\left(\operatorname{apply}\left(b, i\right)\right)\right)))\land (\forall eps: \operatorname{Real}\left(\right), (0< eps\implies \operatorname{Finite}\left(\operatorname{setOf}\left(\lambda i: \operatorname{Nat}\left(\right), eps\leq \operatorname{apply}\left(mu, i\right)\right)\right)))\land (\forall F: \operatorname{D}\left(\right), (\operatorname{HasSum}\left(\lambda i: \operatorname{Nat}\left(\right), (\operatorname{apply}\left(\operatorname{repr}\left(b, \operatorname{centeredSubtype}\left(\operatorname{Pi}\left(\operatorname{val}\left(F\right)\right)\right)\right), i\right))^{2}/\operatorname{apply}\left(mu, i\right), \operatorname{energy}\left(\operatorname{val}\left(F\right)\right)\right)))\land (\forall lam: \operatorname{Real}\left(\right), (\forall F: \operatorname{D}\left(\right), ((\forall i: \operatorname{Nat}\left(\right), ((\operatorname{apply}\left(mu, i\right))^{-1}< lam\implies \operatorname{apply}\left(\operatorname{repr}\left(b, \operatorname{centeredSubtype}\left(\operatorname{Pi}\left(\operatorname{val}\left(F\right)\right)\right)\right), i\right)=0))\implies lam\cdot (\Vert \operatorname{Pi}\left(\operatorname{val}\left(F\right)\right) \Vert)^{2}\leq \operatorname{energy}\left(\operatorname{val}\left(F\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySpectralForm.actual_spectral_form_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist paired Hilbert bases b of the actual centered boundary space G0 and k of the actual effective increment space K. Their positive covariance eigenvalues mu decrease to zero, their reciprocals increase to infinity, and every positive covariance cutoff has only finitely many indices. The original boundary operator graph contains each pair consisting of b(i) and its reciprocal-eigenvalue multiple. The original Sigma and C send k(i) respectively to mu(i) times k(i) and sqrt(mu(i)) times b(i).

For every F in the original free-root form domain D, let z be its attained least increment lift in K and let f(i) be the b coefficient of Pi(F). Applying the original adjoint to the paired basis identity gives C-adjoint(b(i))=sqrt(mu(i))*k(i). Consequently f(i)=sqrt(mu(i)) times the k coefficient of z. This statement concerns every form-domain vector, without assuming membership in the operator domain.

Parseval in K identifies the sum of the squared increment coefficients with the squared norm of z, which is the original minimum energy. Positivity of each mu(i) then gives the summable energy series f(i) squared divided by mu(i). HasSum records both summability and equality with the original energy.

Fix any real threshold lam. If every coefficient with reciprocal mu(i) strictly less than lam vanishes, each remaining weighted energy term is at least lam times f(i) squared. Parseval in G0 and comparison of these convergent series therefore give energy(F) at least lam times the squared norm of Pi(F). Equality at the spectral threshold is included in the retained support, and repeated eigenvalues are unrestricted.

The bases and eigenvalues are obtained from the actual positive spectral exhaustion of the original biased boundary operator. J, Pi, C, Sigma, K, D and the free-root minimum energy retain their original meanings. This representation supplies the form-support estimate for the lower variational counting argument; it does not itself identify all finite spectral cutoff dimensions or assert the global counting bounds.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySpectralForm.actual_spectral_form_energy`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator](BiasedBoundaryOperator.md)

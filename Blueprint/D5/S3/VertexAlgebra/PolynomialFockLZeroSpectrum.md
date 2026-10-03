# Polynomial Fock Zero-Mode Spectrum

## Abstract

The concrete polynomial Fock zero mode has finite energy fibers and exact finite-dimensional eigenspaces.

The operator is the pointwise finite Sugawara L_0 on the complex polynomial Fock space from Polynomial Fock Sugawara Support. A monomial has energy equal to the sum of its exponents weighted by variable index plus one. The result concerns nonnegative integer eigenvalues; it does not construct state fields or a conformal character.

**Theorem 1.1 (Each weighted-monomial energy fiber is finite).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum.energyFiber_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum.energyFiber_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At energy N, every occupied variable index is below N and each exponent is at most N. Thus exponent vectors of energy N embed in a finite product of finite intervals, including N = 0.

**Theorem 1.2 (The zero-mode eigenspace has the weighted-monomial basis).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum.lZero_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum.lZero_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yanjun Chu and Zongzhu Lin (2018). *Moduli spaces of conformal structures on Heisenberg vertex algebras*. URL: <https://arxiv.org/abs/1812.11378v1>.

*Commentary.*

For every natural N, the kernel of L_0 minus N times the identity is precisely the span of monomials of energy N, and its complex dimension is the number of those monomials. The proof uses the concrete Sugawara-current commutator and coefficient uniqueness; it does not establish the full Virasoro commutator.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum.energyFiber_finite`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum.lZero_spectrum`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators](PolynomialFockSugawaraCommutators.md)

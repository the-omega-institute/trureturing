# Polynomial Fock Power-State Coefficients

## Abstract

Every integer mode of a power-state field has an explicit polynomial output.

The complex polynomial Fock space is C[X_0,X_1,...], with the actual state-field map Y defined by the monomial basis and right-nested normal products. Define A(z)=sum_{j>=0} X_j z^j as a formal power series. B(r,d) is the coefficient of z^d in A(z)^r for d>=0 and is zero for d<0. In particular B(0,0)=1 and B(0,d)=0 for d different from zero.

**Theorem 1.1 (The actual field output at every integer mode).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockPowerOPE.power_state_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockPowerOPE.power_state_coefficients` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

For all natural p,q and integer n, Y(X_0^p)_n applied to X_0^q is the sum over 0<=k<=min(p,q) of binomial(p,k) times the falling factorial q(q-1)...(q-k+1) times B(p-k,2k-n-1) X_0^(q-k). The falling factorial at k=0 and every zeroth power are one. The equality includes vacuum inputs, zero powers, negative modes, and both singular and regular coefficients.

The actual minus-one normal product splits into creation and annihilation branches. On X_0^q only current mode one contributes to annihilation, and its coefficient is q. The creation branch has finite support for each fixed input and mode. Its convolution is the coefficient of A^(r+1); Pascal's identity combines the two branches. No Wick identity or desired recurrence is assumed.

These are formal algebraic coefficients in the unit-normalized rank-one Heisenberg vacuum representation. They do not assert analytic convergence, module fusion, a Monster realization, a complete boundary conformal field theory, or spacetime dynamics.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockPowerOPE.power_state_coefficients`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockStateField](PolynomialFockStateField.md)

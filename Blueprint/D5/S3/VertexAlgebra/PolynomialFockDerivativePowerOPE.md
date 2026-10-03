# Derivative-Labelled Polynomial Fock Coefficients

## Abstract

Every integer mode of a derivative-labelled Fock power-state field has an explicit polynomial output.

The complex polynomial Fock space is C[X_0,X_1,...]. The current modes are multiplication by X_j at mode -j-1, zero at mode zero, and (j+1) times differentiation in X_j at mode j+1. The actual state-field map Y is defined by the monomial basis and right-nested normal products. The field of X_a is the divided derivative of order a of the current, using 1/a! times the ordinary derivative.

Independently of Y, define A(a,z) as the formal power series with coefficient binomial(j+a,a) X_(j+a) at every natural j. B(a,r,d) is the coefficient of z^d in A(a,z)^r when d>=0 and is zero when d<0. Define c(a,b)=(-1)^a (b+1) binomial(a+b+1,a). Thus B(a,0,0)=1 and B(a,0,d)=0 for every nonzero integer d.

**Theorem 1.1 (The actual two-labelled field output at every integer mode).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockDerivativePowerOPE.derivative_power_state_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockDerivativePowerOPE.derivative_power_state_coefficients` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *A Note on Free Bosonic Vertex Algebra and its Conformal Vectors*. URL: <https://arxiv.org/abs/hep-th/9704060v1>.

*Commentary.*

For every natural a,b,p,q and integer n, Y(X_a^p)_n applied to X_b^q equals the sum over 0<=k<=min(p,q) of binomial(p,k) times the falling factorial q(q-1)...(q-k+1), times c(a,b)^k, times B(a,p-k,(a+b+2)k-n-1) X_b^(q-k). Scalar factors are complex numbers. There are no extra hypotheses on the labels, powers or mode sign.

Every zeroth power, including c(a,b)^0, and the falling factorial at k=0 is one. When p=0 the output is X_b^q at mode -1 and zero elsewhere. When q=0 the output is B(a,p,-n-1). When a=b=0 the formula specializes to the unlabelled power-state coefficient relation.

The divided-current mode at -j-1 creates binomial(j+a,a) X_(j+a). On X_b^q its nonnegative modes vanish except at a+b+1, where its output is q c(a,b) X_b^(q-1). The actual minus-one normal product therefore has a creation convolution and one annihilation contribution. A finite support cutoff identifies the first branch with A(a)^(r+1). Pascal's identity and falling factorials combine the branches through induction on the left power.

The free-boson reference supplies the classical divided-derivative contraction and polynomial Fock normalization; it does not state this exact all-integer output formula. These are formal algebraic coefficients. They do not establish analytic convergence, module fusion, a Monster realization, complete boundary conformal field theory or spacetime dynamics.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockDerivativePowerOPE.derivative_power_state_coefficients`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockStateField](PolynomialFockStateField.md)

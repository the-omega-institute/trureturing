# Native Half-Fock Creation Transport

## Abstract

Actual odd-weight exponential coefficients and their two-factor contraction

D has arbitrary natural rank, an integral symmetric Gram matrix and even diagonal. No positivity, unimodularity, inverse Gram matrix, rank 24 or locality is assumed. The oscillator carrier remains the infinite algebra P=MvPolynomial(Fin(D.rank) times N,C). Each individual polynomial has finite support; the carrier has no occupation cutoff. A variable X(i,k) has cover weight omega(i,k)=2k+1.

For charge b, the actual halfCreationSeries S_b has zero even coefficients. Its coefficient at 2k+1 is 2/(2k+1) times sum_i b_i X(i,k). halfCreationExponential is the native PowerSeries.exp(P) substituted in this zero-constant series. Write C_b[n]=0 for negative integer n and otherwise take its n.toNat coefficient. The finite polynomial translation Q_a:P->P[x] substitutes X(i,k)->X(i,k)-B(a,e_i)x^(2k+1). There is no additional factor 2 in this shift.

**Theorem 1.1 (Actual odd-weight grading).**

$$\forall D,b, n\in\mathbb{Z}, \operatorname{Hom}\left(omega, \operatorname{C}\left(b, n\right), \operatorname{toNat}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_creation_coefficient_grading` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Differentiating the actual exponential gives a finite antidiagonal recurrence. The coefficient at derivative index m of S_b' is 2 sum_i b_i X(i,m/2) if m is even, and zero otherwise. Strong induction proves that C_b[n] has omega-weight n for n>=0. The negative-index coefficient is zero and is homogeneous in its stated truncated degree. This grading is consumed by the transport theorem: evaluation of each supported monomial has polynomial degree at most its omega-weight, so coefficients of Q_a(C_b[n]) above n vanish.

**Theorem 1.2 (Universal integer-index coefficient transport).**

$$\forall D,a,b,n\in\mathbb{Z},d\in\mathbb{N}, \operatorname{coeff}\left(d, \operatorname{Q}\left(a, \operatorname{C}\left(b, n\right)\right)\right)=\operatorname{kappa}\left(\operatorname{B}\left(a, b\right), d\right) \operatorname{C}\left(b, n-d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_creation_coefficient_transport` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Define halfContraction K_g as rescale(-1)(binomialSeries(C,g)) times binomialSeries(C,-g), with parameter ring explicitly Z and g=B(a,b). The native convention is binomialSeries(g)=(1+s)^g; hence K_g(s)=((1-s)/(1+s))^g, interpreted as a formal series at s=0. kappa_g(d) is its actual d-th coefficient, not an assumed BCH factor.

Map the creation series and its exponential into P[x] by the actual translation. The translated logarithmic derivative differs from the coefficient embedding by -2g*x^(m+1) at even m and zero at odd m. Multiplication by 1-x^2*u^2 therefore gives -2g*x. The integer descending-Pochhammer recurrence proves the exact derivative identity for each rescaled binomial factor. The product satisfies (1-x^2*u^2)K_g(xu)'=-2g*x*K_g(xu). The denominator is a unit. The translated exponential and the embedded exponential times K_g(xu) consequently satisfy the same first-order formal recurrence and have constant coefficient 1. Strong-induction uniqueness identifies them. Finite coefficient convolution and polynomial coefficient extraction give the stated universal law.

The negative source index gives zero on both sides. For n>=0 and d>n, the actual weighted-degree bound proves the left side zero and the negative-index creation convention proves the right side zero. All coefficient sums are finite in their selected degree; no convergence premise or operator BCH axiom enters.

This is classical half-lattice mathematics with zero novelty. The literature anchor is the reflection-twisted lattice construction of Frenkel-Lepowsky-Meurman and the lattice-module account in Bakalov-Kac. The Library note does not claim that this worker inspected the full FLM book. The coefficient theorem is independently proved in Lean on the given native carrier.

The next actual charged oscillator coefficient must use the finite support of Q_a(p): 2^(-q_a) times sum_d Q_a(p)[d] C_a[e+q_a+d], with q_a=B(a,a) and integer zpow. The cover prefactor is t^(-q_a); the physical coordinate is z=t^2. The ground operator must come from actual_twisted_ground_representation D hu and its representation multiplication and central sign, not an assumed action. Pointwise field support, nonzero leading ground action and L0 covariance remain separate future consumers of this coefficient theorem.

Both cover branches are mandatory: for positive g the pole is at t=-u, and for negative g it is at t=u. The future branch exponents are p=max(0,-g) and q=max(0,g); the physical two-step bound is abs(g). No one-sided native delta locality bound is asserted. The original untwisted locality theorem is unchanged. This module does not establish twisted Jacobi, the all-state twisted module, orbifold, Leech specialization, Monster action, full CFT, string theory or AdS/CFT. Those original goals remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_creation_coefficient_grading`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_creation_coefficient_transport`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentNormal](LatticeHalfFockCurrentNormal.md)

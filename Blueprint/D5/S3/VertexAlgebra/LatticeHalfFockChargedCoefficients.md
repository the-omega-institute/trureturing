# Native Half-Fock Creation Transport

## Abstract

Actual odd-weight exponential coefficients and their two-factor contraction

D has arbitrary natural rank, an integral symmetric Gram matrix and even diagonal. No positivity, unimodularity, inverse Gram matrix, rank 24 or locality is assumed. The oscillator carrier remains the infinite algebra P=MvPolynomial(Fin(D.rank) times N,C). Each individual polynomial has finite support; the carrier has no occupation cutoff. A variable X(i,k) has cover weight omega(i,k)=2k+1.

For charge b, the actual halfCreationSeries S_b has zero even coefficients. Its coefficient at 2k+1 is 2/(2k+1) times sum_i b_i X(i,k). halfCreationExponential is the native PowerSeries.exp(P) substituted in this zero-constant series. Write C_b[n]=0 for negative integer n and otherwise take its n.toNat coefficient. The finite polynomial translation Q_a:P->P[x] substitutes X(i,k)->X(i,k)-B(a,e_i)x^(2k+1). There is no additional factor 2 in this shift.

**Theorem 1.1 (Native formal exponential differential equation).**

$$\forall D,b, \operatorname{derivative}\left(\operatorname{E}\left(b\right)\right)=\operatorname{E}\left(b\right) \operatorname{derivative}\left(\operatorname{S}\left(b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.exponential_derivative` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

E_b is halfCreationExponential and S_b is halfCreationSeries. The zero constant coefficient of S_b makes formal substitution admissible. The power-series chain rule and derivative of exp give E_b'=E_b S_b'. This is a directly reused formal-series identity, consumed in the grading induction, transport differential equations and annihilation chain rule.

**Theorem 1.2 (Native exponential initial coefficient).**

$$\forall D,b, \operatorname{coeff}\left(0, \operatorname{E}\left(b\right)\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.exponential_constant` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Only the zeroth summand contributes to the constant coefficient of exp(S_b), because S_b has constant coefficient zero. This initial value is consumed by the grading induction, uniqueness in transport and the zero-initial-residual argument for annihilation.

**Theorem 1.3 (Parity and normalization of the logarithmic derivative).**

$$\forall D,b,n\in\mathbb{N}, \operatorname{coeff}\left(n, \operatorname{derivative}\left(\operatorname{S}\left(b\right)\right)\right)=\operatorname{T}\left(b, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.series_derivative_coeff` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

T_b(n) denotes 2 sum_i b_i X(i,n/2) for even n, and zero for odd n. Formal differentiation multiplies the coefficient at n+1 by n+1; this cancels its denominator when n is even. For odd n the source coefficient vanishes. The formula includes n=0, zero charge and rank zero. Both grading and transport consume this exact parity formula.

**Theorem 1.4 (Actual odd-weight grading).**

$$\forall D,b, n\in\mathbb{Z}, \operatorname{Hom}\left(omega, \operatorname{C}\left(b, n\right), \operatorname{toNat}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_creation_coefficient_grading` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Differentiating the actual exponential gives a finite antidiagonal recurrence. The coefficient at derivative index m of S_b' is 2 sum_i b_i X(i,m/2) if m is even, and zero otherwise. Strong induction proves that C_b[n] has omega-weight n for n>=0. The negative-index coefficient is zero and is homogeneous in its stated truncated degree. This grading is consumed by the transport theorem: evaluation of each supported monomial has polynomial degree at most its omega-weight, so coefficients of Q_a(C_b[n]) above n vanish.

**Theorem 1.5 (Universal integer-index coefficient transport).**

$$\forall D,a,b,n\in\mathbb{Z},d\in\mathbb{N}, \operatorname{coeff}\left(d, \operatorname{Q}\left(a, \operatorname{C}\left(b, n\right)\right)\right)=\operatorname{kappa}\left(\operatorname{B}\left(a, b\right), d\right) \operatorname{C}\left(b, n-d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_creation_coefficient_transport` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Define halfContraction K_g as rescale(-1)(binomialSeries(C,g)) times binomialSeries(C,-g), with parameter ring explicitly Z and g=B(a,b). The native convention is binomialSeries(g)=(1+s)^g; hence K_g(s)=((1-s)/(1+s))^g, interpreted as a formal series at s=0. kappa_g(d) is its actual d-th coefficient, not an assumed BCH factor.

Map the creation series and its exponential into P[x] by the actual translation. The translated logarithmic derivative differs from the coefficient embedding by -2g*x^(m+1) at even m and zero at odd m. Multiplication by 1-x^2*u^2 therefore gives -2g*x. The integer descending-Pochhammer recurrence proves the exact derivative identity for each rescaled binomial factor. The product satisfies (1-x^2*u^2)K_g(xu)'=-2g*x*K_g(xu). The denominator is a unit. The translated exponential and the embedded exponential times K_g(xu) consequently satisfy the same first-order formal recurrence and have constant coefficient 1. Strong-induction uniqueness identifies them. Finite coefficient convolution and polynomial coefficient extraction give the stated universal law.

The negative source index gives zero on both sides. For n>=0 and d>n, the actual weighted-degree bound proves the left side zero and the negative-index creation convention proves the right side zero. All coefficient sums are finite in their selected degree; no convergence premise or operator BCH axiom enters.

This is classical half-lattice mathematics with zero novelty. The literature anchor is the reflection-twisted lattice construction of Frenkel-Lepowsky-Meurman and the lattice-module account in Bakalov-Kac. The argument here uses the native formal exponential, finite polynomial translation and integer binomial series.

The charged oscillator coefficient uses the finite support of Q_a(p): 2^(-q_a) times sum_d Q_a(p)[d] C_a[e+q_a+d], with q_a=B(a,a) and integer zpow. The cover prefactor is t^(-q_a); the physical coordinate is z=t^2. The ground operator must come from actual_twisted_ground_representation D hu and its representation multiplication and central sign, not an assumed action. Transport supplies the constant-input step of the ordered-product expansion; grading supplies the creation-energy calculation. These applications require their own field support, ground action and conformal-operator arguments.

Both cover branches are mandatory: for positive g the pole is at t=-u, and for negative g it is at t=u. The scalar denominator exponents are p=max(0,-g) and q=max(0,g), with p+q=abs(g). Passing to a locality statement in z=t^2 requires the actual operator product identity. No one-sided native delta locality bound is asserted. The original untwisted locality theorem uses its own normalization. These coefficient identities do not establish twisted Jacobi, the all-state twisted module, orbifold, Leech specialization, Monster action, full CFT, string theory or AdS/CFT.

**Theorem 1.6 (Actual annihilation on integer creation coefficients).**

$$\forall D,i,k\in\mathbb{N},b,n\in\mathbb{Z}, \operatorname{A}\left(i, k, \operatorname{C}\left(b, n\right)\right)=\operatorname{lambda}\left(i, k, b\right) \operatorname{C}\left(b, n-{2k+1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_annihilation_creation` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Here i ranges over Fin(D.rank), k over every natural mode, b over every integral charge and n over every integer. A(i,k) is the actual Gram-weighted annihilation derivation, and lambda(i,k,b)=(2/(2k+1))*B(e_i,b). There is no inverse Gram matrix or nonzero-charge premise.

Coefficientwise derivation commutes with the formal series derivative. Applying A(i,k) coefficientwise to E_b and subtracting E_b A(i,k)S_b gives a residual satisfying a homogeneous first-order formal differential equation with initial coefficient zero. Formal coefficient uniqueness makes this residual zero. Annihilation of S_b is the single monomial lambda(i,k,b)*u^(2k+1), giving the coefficient shift. Negative source indices and negative shifted indices retain their zero convention. The charged tensor coefficient current law consumes this identity.

**Theorem 1.7 (Annihilation commutes with finite polynomial translation).**

$$\forall D,i,k\in\mathbb{N},b,p, \operatorname{Q}\left(b, \operatorname{A}\left(i, k, p\right)\right)=\operatorname{Apoly}\left(i, k, \operatorname{Q}\left(b, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_translated_derivation` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The parameters have the same unrestricted lattice, colour, mode and charge ranges as above, and p is an arbitrary oscillator polynomial. Apoly acts coefficientwise on P[x]; it does not differentiate the cover variable x. The translation of each generator is X(i,k) minus a scalar monomial in x, which coefficientwise annihilation kills. The variable law extends to every polynomial by addition and Leibniz induction. This commutation is consumed with the creation identity in the charged oscillator current Ward calculation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.exponential_constant`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.exponential_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_annihilation_creation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_creation_coefficient_grading`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_creation_coefficient_transport`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.half_translated_derivation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.series_derivative_coeff`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentNormal](LatticeHalfFockCurrentNormal.md)

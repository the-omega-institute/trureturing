# Actual Charged Tensor Laurent Coefficients

## Abstract

Native charged coefficients on the actual twisted ground module

Let D be an integral symmetric even-diagonal lattice datum of arbitrary finite rank. Assume IsUnit D.G.det only to obtain the actual twisted ground representation. The oscillator algebra is the full native polynomial algebra P=MvPolynomial(Fin(D.rank) times N,C), with no occupation cutoff and no positivity assumption. groundRank and groundRepresentation choose the witnesses of actual_twisted_ground_representation D hu. The ground module is the supplier's function space Ground(groundRank D hu), not an arbitrary substitute. groundAction(a) is the actual representation of the quotient-group lift of (0,a). Its invertibility follows from the group representation; it is not an added hypothesis.

Write q_a=B(a,a), s_a=2^(-q_a), C_a[k]=halfCreationCoeff D a k, and Q_a(p)=halfTranslatedPolynomial D a p. The cover variable is t with physical z=t^2. The cover prefactor is t^(-q_a). The coefficient at t^e on p tensor v is exactly s_a times (sum_d coeff_d(Q_a(p)) C_a[e+q_a+d]) tensor groundAction(a)v. The positive d offset arises because the native translation variable represents t^(-1), not t. Q_a substitutes X(i,k)-B(a,e_i)x^(2k+1), with no spurious factor 2.

oscillatorTerm has support contained in the finite native Polynomial.support of Q_a(p). The endomorphism oscillatorCoefficient uses a finsum whose finite support is proved for each input. Additivity and scalar compatibility follow from native polynomial translation and finite-sum distribution. chargedCoefficient is s_a times the tensor product of that actual endomorphism with groundAction(a). charged_native_expansion identifies it with the finite Polynomial.support sum. This is finiteness of the internal coefficient sum, not a claim that the entire Laurent series has finite support.

**Theorem 1.1 (All-polynomial Laurent lower bound).**

$$\forall D,hu,a,p,v,e, e<-\operatorname{q}\left(a\right)-\operatorname{W}\left(p\right)\implies\operatorname{A}\left(a, e, ptensorv\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_polynomial_lower_bound` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

W(p)=nativeOddWeightedDegree D p is the maximum native odd weight of a supported monomial, with W(0)=0. Every translated variable has polynomial degree at most its odd weight 2k+1. For each supported monomial, degree bounds for multiplication, powers and finite products give degree at most its weight. Taking the finite support supremum yields natDegree(Q_a(p))<=W(p). A supported translation index d therefore satisfies d<=W(p). If e<-q_a-W(p), then e+q_a+d<0 and the native creation coefficient is zero. Every summand vanishes.

No homogeneity of p is required. The zero polynomial is covered by its empty support. At rank zero all oscillator polynomials are constants and W(p)=0. A negative q_a is allowed and simply moves the stated lower bound to positive cover exponent; q_a=0 leaves prefactor and scalar equal to one. No case changes the physical energy convention. Tensor induction gives a lower bound for every finite sum of simple tensors. chargedField is then a native HVertexOperator on the actual tensor carrier; no field truncation axiom is assumed.

**Theorem 1.2 (Nonzero actual ground leading coefficient).**

$$\forall D,hu,a,v, v\neq0\implies\operatorname{A}\left(a, -\operatorname{q}\left(a\right), 1tensorv\right)\neq0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_ground_leading` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Native translation of one is one. Thus the complete vacuum coefficient formula is A_a[e](1 tensor v)=s_a C_a[e+q_a] tensor groundAction(a)v. The zero coefficient of the actual substituted exponential is one, by its zero constant logarithm and the native PowerSeries coefficient substitution theorem. At e=-q_a the coefficient is exactly s_a (1 tensor groundAction(a)v); every lower coefficient vanishes by the polynomial theorem.

The scalar s_a is nonzero for every integer q_a. The monomial tensor-basis equivalence recovers groundAction(a)v as the coordinate at monomial zero of 1 tensor groundAction(a)v. If that tensor vanished, so would its coordinate. Applying the actual representation of the inverse quotient-group lift then gives v=0, contradicting precisely the stated nonzero-v hypothesis. This neither assumes a nonzero action nor reconstructs a duplicate projective representation.

The native universal half_creation_coefficient_transport remains the exact source for the next charged coefficient products: translating C_b[n] gives kappa_g(d) C_b[n-d], where kappa_g is the coefficient of ((1-s)/(1+s))^g and g=B(a,b). Both cover branches must be retained. Their pole bounds are p=max(0,-g), q=max(0,g), and the physical two-step order is abs(g); positive g can have an opposite-cover pole. No one-sided delta identity, pair-locality or twisted Jacobi conclusion is asserted.

There is also a precise termwise native cover-energy application. For H satisfying BOTH H*gramComplex(D)=1 and gramComplex(D)*H=1, use the actual half-Fock L0. If the input polynomial is C_b[n], the degree-d summand is T_d=kappa_g(d) C_b[n-d] C_a[e+q_a+d]. Universal transport gives this equality from the actual translation, not from an assumed field commutator. The native creation coefficient grading makes the two nonzero factors homogeneous of weights (n-d).toNat and (e+q_a+d).toNat. If either integer index is negative the term is zero. Otherwise their sum of weights is n+e+q_a. The actual L_zero_monomial_coeff supplier and finite monomial decomposition therefore give L0(T_d)=(D.rank/16+(n+e+q_a)/2) T_d, for all integer n and e. This is an application of the existing weight and transport suppliers, not a separately retained theorem. The ground shift remains D.rank/16 and physical z=t^2. Lifting the termwise identity to a complete charged tensor coefficient covariance is a distinct remaining endpoint.

All-mode current and energy covariance, full charged products and two-branch locality remain distinct obligations. The actual native spectrum keeps ground shift D.rank/16 and variable z=t^2. Leech realization, orbifold extension, Monster symmetry, full VOA and CFT, anomalies, fusion, string theory and AdS/CFT remain open. The classical construction and these native supplier applications carry no literature-novelty claim.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_ground_leading`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_polynomial_lower_bound`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients](LatticeHalfFockChargedCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockTensorFields](LatticeHalfFockTensorFields.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](LatticeTwistedGroundRealization.md)

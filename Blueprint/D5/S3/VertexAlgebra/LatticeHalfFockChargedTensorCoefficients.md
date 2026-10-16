# Actual Charged Tensor Laurent Coefficients

## Abstract

Native charged coefficients on the actual twisted ground module

Let D be an integral symmetric even-diagonal lattice datum of arbitrary finite rank. Assume IsUnit D.G.det only to obtain the actual twisted ground representation. The oscillator algebra is the full native polynomial algebra P=MvPolynomial(Fin(D.rank) times N,C), with no occupation cutoff and no positivity assumption. groundRank and groundRepresentation choose the witnesses of actual_twisted_ground_representation D hu. The ground module is the supplier's function space Ground(groundRank D hu), not an arbitrary substitute. groundAction(a) is the actual representation of the quotient-group lift of (0,a). Its invertibility follows from the group representation; it is not an added hypothesis.

Write q_a=B(a,a), s_a=2^(-q_a), C_a[k]=halfCreationCoeff D a k, and Q_a(p)=halfTranslatedPolynomial D a p. The cover variable is t with physical z=t^2. The cover prefactor is t^(-q_a). The coefficient at t^e on p tensor v is exactly s_a times (sum_d coeff_d(Q_a(p)) C_a[e+q_a+d]) tensor groundAction(a)v. The positive d offset arises because the native translation variable represents t^(-1), not t. Q_a substitutes X(i,k)-B(a,e_i)x^(2k+1), with no spurious factor 2.

oscillatorTerm has support contained in the finite native Polynomial.support of Q_a(p). The endomorphism oscillatorCoefficient uses a finsum whose finite support is proved for each input. Additivity and scalar compatibility follow from native polynomial translation and finite-sum distribution. chargedCoefficient is s_a times the tensor product of that actual endomorphism with groundAction(a). charged_native_expansion identifies it with the finite Polynomial.support sum. This is finiteness of the internal coefficient sum, not a claim that the entire Laurent series has finite support.

**Theorem 1.1 (Support of the exact native coefficient summand).**

$$\forall D:LatticeData, a:\operatorname{Charge}\left(D\right), e:\mathbb{Z}, p:\operatorname{Oscillator}\left(D\right), \operatorname{support}\left(\operatorname{oscillatorTerm}\left(D, a, e, p\right)\right)\subseteq\operatorname{support}\left(\operatorname{Q}\left(a, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.term_support` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D:LatticeData, a:Charge(D), e:Integer and p:Oscillator(D), oscillatorTerm(D,a,e,p,d)=coeff_d(Q_a(p)) C_a[e+q_a+d]. A nonzero term requires a nonzero translated polynomial coefficient, so its function support is contained in Q_a(p).support. No determinant hypothesis is used. This support helper is consumed by charged_term_finite_support, charged_native_expansion and oscillatorCoefficient_as_sum; it is not a separate content advance.

**Theorem 1.2 (Finite internal coefficient sum on each polynomial).**

$$\forall D:LatticeData, a:\operatorname{Charge}\left(D\right), e:\mathbb{Z}, p:\operatorname{Oscillator}\left(D\right), \operatorname{HasFiniteSupport}\left(\operatorname{oscillatorTerm}\left(D, a, e, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_term_finite_support` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The complete parameter group is D:LatticeData, a:Charge(D), e:Integer and p:Oscillator(D), without hu. The finite native polynomial support and term_support give finite function support for the natural summation degree. This consumed helper justifies finsum additivity and scalar compatibility in oscillatorCoefficient. It imposes no occupation cutoff and says nothing about finiteness of support in the external Laurent exponent e.

**Theorem 1.3 (All-polynomial Laurent lower bound).**

$$\forall D:LatticeData, hu:\operatorname{IsUnit}\left(\operatorname{det}\left(\operatorname{G}\left(D\right)\right)\right), a:\operatorname{Charge}\left(D\right), p:\operatorname{Oscillator}\left(D\right), v:\operatorname{ActualGround}\left(D, hu\right), e:\mathbb{Z}, e<-\operatorname{q}\left(a\right)-\operatorname{W}\left(p\right)\implies\operatorname{A}\left(a, e, ptensorv\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_polynomial_lower_bound` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

W(p)=nativeOddWeightedDegree D p is the maximum native odd weight of a supported monomial, with W(0)=0. Every translated variable has polynomial degree at most its odd weight 2k+1. For each supported monomial, degree bounds for multiplication, powers and finite products give degree at most its weight. Taking the finite support supremum yields natDegree(Q_a(p))<=W(p). A supported translation index d therefore satisfies d<=W(p). If e<-q_a-W(p), then e+q_a+d<0 and the native creation coefficient is zero. Every summand vanishes.

No homogeneity of p is required. The zero polynomial is covered by its empty support. At rank zero all oscillator polynomials are constants and W(p)=0. A negative q_a is allowed and simply moves the stated lower bound to positive cover exponent; q_a=0 leaves prefactor and scalar equal to one. No case changes the physical energy convention. Tensor induction gives a lower bound for every finite sum of simple tensors. chargedField is then a native HVertexOperator on the actual tensor carrier; no field truncation axiom is assumed.

**Theorem 1.4 (Exact vacuum coefficient with the original normalization).**

$$\forall D:LatticeData, hu:\operatorname{IsUnit}\left(\operatorname{det}\left(\operatorname{G}\left(D\right)\right)\right), a:\operatorname{Charge}\left(D\right), e:\mathbb{Z}, v:\operatorname{ActualGround}\left(D, hu\right), \operatorname{A}\left(a, e, 1tensorv\right)=\operatorname{s}\left(a\right) \operatorname{C}\left(a, e+\operatorname{q}\left(a\right)\right)tensor\operatorname{groundAction}\left(a, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_vacuum_coefficient` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The source telescope is D:LatticeData, hu:IsUnit(det(G(D))), a:Charge(D), e:Integer and v:ActualGround(D,hu), including the zero vector. Translation of the oscillator unit is the constant polynomial one, whose support is {0}. The coefficient is therefore exactly s_a times C_a[e+q_a] tensor groundAction(a)v. The scalar stays 2^(-B(a,a)); no factor, sign or exponent is absorbed into groundAction. This evaluation helper is consumed by charged_ground_leading.

**Theorem 1.5 (Nonzero actual ground leading coefficient).**

$$\forall D:LatticeData, hu:\operatorname{IsUnit}\left(\operatorname{det}\left(\operatorname{G}\left(D\right)\right)\right), a:\operatorname{Charge}\left(D\right), v:\operatorname{ActualGround}\left(D, hu\right), v\neq0\implies\operatorname{A}\left(a, -\operatorname{q}\left(a\right), 1tensorv\right)\neq0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_ground_leading` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Native translation of one is one. Thus the complete vacuum coefficient formula is A_a[e](1 tensor v)=s_a C_a[e+q_a] tensor groundAction(a)v. The zero coefficient of the actual substituted exponential is one, by its zero constant logarithm and the native PowerSeries coefficient substitution theorem. At e=-q_a the coefficient is exactly s_a (1 tensor groundAction(a)v); every lower coefficient vanishes by the polynomial theorem.

The scalar s_a is nonzero for every integer q_a. The monomial tensor-basis equivalence recovers groundAction(a)v as the coordinate at monomial zero of 1 tensor groundAction(a)v. If that tensor vanished, so would its coordinate. Applying the actual representation of the inverse quotient-group lift then gives v=0, contradicting precisely the stated nonzero-v hypothesis. This neither assumes a nonzero action nor reconstructs a duplicate projective representation.

**Theorem 1.6 (Full integer-mode tensor current Ward identity).**

$$\forall D:LatticeData, hu:\operatorname{IsUnit}\left(\operatorname{det}\left(\operatorname{G}\left(D\right)\right)\right), i:\operatorname{Fin}\left(\operatorname{rank}\left(D\right)\right), a:\operatorname{Charge}\left(D\right), m:\mathbb{Z}, e:\mathbb{Z}, \operatorname{J}\left(i, m\right)\operatorname{A}\left(a, e\right)-\operatorname{A}\left(a, e\right)\operatorname{J}\left(i, m\right)=\operatorname{B}\left(\operatorname{unitCharge}\left(D, i\right), a\right) \operatorname{A}\left(a, e-(2m+1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_tensor_current_ward` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D:LatticeData, hu:IsUnit(det(G(D))), i:Fin(D.rank), a:Charge(D) and m,e:Integer, J_i[m] is tensorCurrent(D,ActualGround(D,hu),i,m). Multiplication in the formula is composition of endomorphisms on the full actual tensor carrier. The commutator is B(unitCharge(D,i),a) times A_a[e-(2m+1)]. Both m and e range over all integers, with the same shift on the creation and annihilation branches.

For negative m, the native multiplication-current branch and the exact translated-variable identity give the positive odd-weight offset. For nonnegative m, the polynomial derivation commutes with translation and differentiates the actual creation coefficient; the frequency normalization cancels 2/(2m+1). The finite native coefficient map combines these two branches. Tensor-product extensionality then transports the oscillator commutator through the actual ground action and the original scalar. No current commutator or charged action law is assumed. This current covariance is distinct from energy covariance and charged-field pair locality.

**Theorem 1.7 (Native polynomial coefficient functional).**

$$\forall D:LatticeData, a:\operatorname{Charge}\left(D\right), e:\mathbb{Z}, p:\operatorname{Oscillator}\left(D\right), \operatorname{oscillatorCoefficient}\left(D, a, e, p\right)=\operatorname{nativeCoefficientMap}\left(D, a, e, \operatorname{Q}\left(a, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.oscillatorCoefficient_as_sum` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D,a,e,p, the actual oscillator coefficient is the native coefficient functional applied to Q_a(p). The functional sends the degree-d coefficient c to c C_a[e+q_a+d]. Finite translated polynomial support identifies the finsum with this polynomial-linear functional.

**Theorem 1.8 (Native oscillator creator recurrence).**

$$\forall D:LatticeData, a:\operatorname{Charge}\left(D\right), e:\mathbb{Z}, i:\operatorname{Index}\left(D\right), p:\operatorname{Oscillator}\left(D\right), \operatorname{oscillatorCoefficient}\left(D, a, e, \operatorname{X}\left(i\right)p\right)=\operatorname{X}\left(i\right)\operatorname{oscillatorCoefficient}\left(D, a, e, p\right)-\operatorname{B}\left(a, \operatorname{unitCharge}\left(D, \operatorname{fst}\left(i\right)\right)\right) \operatorname{oscillatorCoefficient}\left(D, a, e+\operatorname{omega}\left(D, i\right), p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.oscillatorCoefficient_X_mul` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The complete domain is D:LatticeData, a:Charge(D), e:Integer, i:Index(D), p:Oscillator(D). The shift is omega(D,i)=2*i.snd+1, and the pairing acts by complex scalar multiplication. Polynomial translation and its coefficient functional give this recurrence without a field commutator hypothesis.

nativeCoefficientMap is the oscillator-linear polynomial coefficient functional with weight C_a[e+q_a+d]. oscillatorCoefficient_as_sum identifies the actual endomorphism with this functional applied to Q_a(p). oscillatorCoefficient_X_mul holds for every integer e and every polynomial p: A_a[e](X(i)p)=X(i)A_a[e]p-B(a,e_i)A_a[e+omega(i)]p. The full forward ordered-product identity uses these interfaces with the original odd weight; no ordinary-frequency substitution is involved.

The native universal half_creation_coefficient_transport remains the exact source for the next charged coefficient products: translating C_b[n] gives kappa_g(d) C_b[n-d], where kappa_g is the coefficient of ((1-s)/(1+s))^g and g=B(a,b). Both cover branches must be retained. Their pole bounds are p=max(0,-g), q=max(0,g), and the physical two-step order is abs(g); positive g can have an opposite-cover pole. No one-sided delta identity, pair-locality or twisted Jacobi conclusion is asserted.

The precise termwise native cover-energy application remains a mathematical endpoint. For H satisfying BOTH H*gramComplex(D)=1 and gramComplex(D)*H=1, use the actual half-Fock L0. If the input polynomial is C_b[n], the degree-d summand is T_d=kappa_g(d) C_b[n-d] C_a[e+q_a+d]. Universal transport gives this equality from the actual translation, not from an assumed field commutator. The native creation coefficient grading makes the two nonzero factors homogeneous of weights (n-d).toNat and (e+q_a+d).toNat. If either integer index is negative the term is zero. Otherwise their sum of weights is n+e+q_a. The exact remaining application is L0(T_d)=(D.rank/16+(n+e+q_a)/2) T_d, for all integer n and e, using the actual L_zero_monomial_coeff supplier and finite monomial decomposition. This termwise identity remains open pending its exact Lean application under the two stated inverse-Gram hypotheses. The ground shift remains D.rank/16 and physical z=t^2. Lifting the termwise identity to a complete charged tensor coefficient covariance is a distinct remaining endpoint.

Energy covariance, full charged products and two-branch locality remain distinct obligations. The actual native spectrum keeps ground shift D.rank/16 and variable z=t^2. Leech realization, orbifold extension, Monster symmetry, full VOA and CFT, anomalies, fusion, string theory and AdS/CFT remain open. The classical construction and these native supplier applications carry no literature-novelty claim.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_ground_leading`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_polynomial_lower_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_tensor_current_ward`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_term_finite_support`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_vacuum_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.oscillatorCoefficient_X_mul`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.oscillatorCoefficient_as_sum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.term_support`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients](LatticeHalfFockChargedCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockTensorFields](LatticeHalfFockTensorFields.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](LatticeTwistedGroundRealization.md)

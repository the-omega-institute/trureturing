# Actual Charged Tensor Laurent Coefficients

## Abstract

Native charged coefficients on the actual twisted ground module

Let D be an integral symmetric even-diagonal lattice datum of arbitrary finite rank. Assume IsUnit D.G.det only to obtain the actual twisted ground representation. The oscillator algebra is the full native polynomial algebra P=MvPolynomial(Fin(D.rank) times N,C), with no occupation cutoff and no positivity assumption. groundRank and groundRepresentation choose the witnesses of actual_twisted_ground_representation D hu. The ground module is the supplier's function space Ground(groundRank D hu), not an arbitrary substitute. groundAction(a) is the actual representation of the quotient-group lift of (0,a). Its invertibility follows from the group representation; it is not an added hypothesis.

Write q_a=B(a,a), s_a=2^(-q_a), C_a[k]=halfCreationCoeff D a k, and Q_a(p)=halfTranslatedPolynomial D a p. The cover variable is t with physical z=t^2. The cover prefactor is t^(-q_a). The coefficient at t^e on p tensor v is exactly s_a times (sum_d coeff_d(Q_a(p)) C_a[e+q_a+d]) tensor groundAction(a)v. The positive d offset arises because the native translation variable represents t^(-1), not t. Q_a substitutes X(i,k)-B(a,e_i)x^(2k+1), with no spurious factor 2.

oscillatorTerm has support contained in the finite native Polynomial.support of Q_a(p). The endomorphism oscillatorCoefficient uses a finsum whose finite support is proved for each input. Additivity and scalar compatibility follow from native polynomial translation and finite-sum distribution. chargedCoefficient is s_a times the tensor product of that actual endomorphism with groundAction(a). charged_native_expansion identifies it with the finite Polynomial.support sum. This is finiteness of the internal coefficient sum, not a claim that the entire Laurent series has finite support.

The full half-Fock character is obtained on this same actual ground module. For arbitrary D and hu:IsUnit D.G.det, put H=(D.G inverse).map(Int.castRingHom C), so H is exactly the mapped integral inverse, and the nonsingular-inverse identities give H*gramComplex(D)=gramComplex(D)*H=1. For an exponent d on Fin(D.rank) times N, define oddEnergy(d)=sum_(i,n) d(i,n)*(2*n+1), and define halfEigenvalue(N)=D.rank/16+N/2. The supplied native monomial law says L(D,H,0) sends the monomial d to halfEigenvalue(oddEnergy(d)) times that monomial; the label halfEigenvalue is injective. There is no replacement Gram matrix, positivity premise or change to the vacuum shift.

Apply D5/S1/Eigenstructure/DiagonalTensorEigenspace.gradedEigenspaceEquiv with K=C, I the full exponent type (Fin(D.rank) times N)->finitely-supported N, M the native oscillator polynomial algebra, b=basisMonomials, A=L(D,H,0), degree=oddEnergy, value=halfEigenvalue, and T=ActualGround(D,hu). The tensor extension is the existing tensorL(D,T,H,0). Thus its whole eigenspace at D.rank/16+N/2 is linearly equivalent to finitely supported ActualGround(D,hu)-valued coefficients indexed by all exponents of oddEnergy N. This identifies every eigenvector through its coefficients; it does not merely list monomial eigenvectors. The tensor theorem also allows zero or infinite-dimensional ground spaces and infinitely many basis vectors.

OddEnergy is exactly colouredEnergy(Fin(D.rank)) in D5/S3/Combinatorics/Partitions/ColouredOddOccupation: the existing omega(i,n) is 2*n+1. Its colouredOddFiberEquivSigma identifies the same exponent fibre with a dependent sum over e:Fin(D.rank)->N with sum e=N, whose fibre is the product of odd-part partitions of e(i). The odd-part inverse sends j to j/2. Transport to the finite finsupp antidiagonal proves the exponent fibre genuinely finite. Since the actual ground is finite-dimensional, the full degree-N eigenspace is finite-dimensional and its dimension is card(oddEnergy fibre N)*finrank(ActualGround(D,hu)). The supplied actual twisted-ground theorem gives finrank(ActualGround(D,hu))=2^(D.rank/2).

Define the normalized character chi_D,hu(X) by giving degree N coefficient equal to the complex cast of that full eigenspace dimension, and define F_D(X) by giving degree N coefficient card(oddEnergy fibre N). Coefficientwise dimension transport yields chi_D,hu=C(finrank(ActualGround(D,hu)))*F_D. The exact finite antidiagonal cardinal formula and PowerSeries.coeff_prod identify F_D with the D.rank-th power of the odd-part partition series. The canonical hasProd_colouredFiberSeries theorem, specialized to C and Fin(D.rank), proves HasProd of n -> ((1-X^(2*n+1)) inverse)^D.rank with target F_D. This proves explicit Multipliable for that family; only then its tprod equals F_D. Consequently chi_D,hu=C(2^(D.rank/2))*tprod_n ((1-X^(2*n+1)) inverse)^D.rank.

The coefficient at N=0 is exactly the actual-ground dimension because the zero-energy occupation is unique. With no colours the entire oscillator series is one, and a rank-zero D has chi_D,hu=1 at every degree, not merely constant coefficient one. Even the indefinite hyperbolic Gram matrix [[0,1],[1,0]] is allowed: its determinant is -1, its quadratic form takes both signs, and its actual ground and degree-zero eigenspace have dimension two. The generic tensor coefficient equivalence remains valid for a zero ground or an infinite-dimensional ground; finite-dimensionality of the latter is not inferred from a default finrank value.

Here X counts twice the oscillator energy: N records the offset N/2 from rank/16. The normalized series has no fractional vacuum prefactor. The product uses PowerSeries.WithPiTopology, the formal coefficient topology; no substitution of a numerical X, ordinary analytic convergence, eta identity, modular transformation or physical completion follows from it.

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

The corrected all-state application in `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection` uses this actual T_D and chargedField, with its original normalization and ground action. Its state-field map Ytw is injective for every D and hu:IsUnit D.G.det. The argument below uses the nonnegative current residue identity of the constructed fields; kernel stability is a consequence, not a hypothesis, and source simplicity is not assumed.

Let K=ker(Ytw), and write J_i(n)=neutralMode D i n on the ordinary source. For b in K, set B=vectorFrequencyBound D b, so J_i(n)b=0 for n>B by `D5/S3/VertexAlgebra/LatticeFiniteNegativeGeneration`. For every d>=0, the actual nonnegative current residue equals sum_{n=d}^B choose(1/2,n-d) I_(1+gamma)(Ytw(J_i(n)b))[[ell+d-n]]x. Its other side is the ordinary d-th product of the actual current with I_gamma(Ytw(b)), hence zero. Descending extraction in d removes the terms n>d; the diagonal coefficient is choose(1/2,0)=1. Taking ell=0 and gamma=-e-3 reads native exponent e, for every integer e. Thus Ytw(J_i(n)b)=0 for every n>=0, including the zero modes. The arbitrary integerization label here tests all native coefficients and adds no parity premise on b.

Suppose K is nonzero and choose a nonzero b in it. The zero currents act diagonally: (J_i(0)b)(a)=B(e_i,a)b(a). Form the finite-dimensional invariant envelope V=span{[a,b(a)]:a in b.support} and T=K intersect V. The commuting zero currents restrict to T. The simultaneous generalized-eigenspace theorem over C gives a nonzero common generalized eigenvector there. On each nonzero charge coordinate its weights must equal B(e_i,a); scalar cancellation in the generalized-eigenvector equations proves this directly. Since the integral Gram matrix is invertible under hu, these weights separate charges. The vector is therefore [a,p] with p nonzero. Only V and T are finite-dimensional; neither the full carrier nor its charge sectors acquire that hypothesis.

In this sector put L={p:[a,p] in K}. Positive source modes give J_i(k+1)[a,p]=(k+1)[a,sum_j G_ij partial_(j,k)p]. The scalar k+1 is nonzero over C. Let H be the integral inverse Gram matrix mapped into C, so H gramComplex(D)=1. Then partial_(j,k)p=sum_i H_ji (sum_l G_il partial_(l,k)p), which belongs to L by kernel stability. The source mode normalization is k+1; it is not the target half-Fock frequency. The existing actual current formulas in `D5/S3/VertexAlgebra/LatticeSugawaraCurrents` supply the weighted derivatives, and the minimum-degree and zero-partial rigidity results of `D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity` apply to L without any finite-dimensionality assumption. A nonzero element of least total degree has every partial zero, hence is a nonzero constant. Rescaling shows [a,1] in K.

Take the actual ground vector g(t)=1. It is nonzero by evaluation at t=0, including when D.rank=0. Since Ytw([a,1])=chargedField(a), its coefficient at e=-B(a,a) on 1 tensor g is exactly 2^(-B(a,a)) (1 tensor groundAction(a)g). charged_ground_leading makes this nonzero: the scalar is nonzero, the actual group action is invertible, and the tensor coordinate at the unit monomial detects the ground vector. This contradicts [a,1] in K, so K=0 and Ytw is injective. The argument uses no arbitrary Nontrivial parameter, positive rank, positive norm, positivity or unitary structure. Indefinite unimodular forms are included; singular Gram matrices are outside this faithfulness telescope, even though their finite Corr construction is defined.

Faithfulness here means that equality of all native endomorphism coefficients of Ytw(u) and Ytw(w) forces u=w. It is not surjectivity onto all Laurent fields, simplicity of a completed VOA, positive-energy grading or a physical realization. This combines the classical twisted ground coefficient with current residues and ordinary polynomial rigidity; it makes no literature-novelty claim.

The native universal half_creation_coefficient_transport is the exact source for charged coefficient products: translating C_b[n] gives kappa_g(d) C_b[n-d], where kappa_g is the coefficient of ((1-s)/(1+s))^g and g=B(a,b). Both cover branches must be retained. Their pole bounds are p=max(0,-g), q=max(0,g), and the physical two-step order is abs(g); positive g can have an opposite-cover pole. This coefficient transport statement alone supplies no one-sided delta identity, pair-locality or twisted Jacobi conclusion.

The original charged energy-covariance theorem is proved in `D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero`. For every D, hu:IsUnit D.G.det, charge a, integer e and v:ActualTensor D hu, the original commutator L0(A_a[e]v)-A_a[e](L0(v)) equals ((e+B(a,a))/2) A_a[e]v. L0 uses the integral inverse Gram matrix mapped into C; both inverse laws follow from hu. Weighted substitution gives signed translated coefficient weight N-d, and the original creation index e+q_a+d gives total weight N+e+q_a. Existing finite support and the actual L_zero_monomial_coeff then give the full polynomial and tensor statement, including the former C_b[n] termwise application. Negative creation indices give literal zero. The scalar 2^(-q_a), original groundAction, ground shift D.rank/16 and physical z=t^2 are retained. Rank zero and indefinite Gram data are included; no metric or positivity is assumed. Full conformal twisted-module structure and the further VOA/CFT programme still require additional identities.

Full Virasoro covariance, including the nonzero modes, and a full conformal twisted-module structure require further identities beyond the local product and faithfulness application. The actual native spectrum keeps ground shift D.rank/16 and variable z=t^2. Leech realization, orbifold extension, Monster symmetry, full VOA and CFT, anomalies, fusion, string theory and AdS/CFT remain open. The classical construction and these native supplier applications carry no literature-novelty claim.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_ground_leading`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_polynomial_lower_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_tensor_current_ward`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_term_finite_support`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.charged_vacuum_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.term_support`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients](LatticeHalfFockChargedCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockTensorFields](LatticeHalfFockTensorFields.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](LatticeTwistedGroundRealization.md)
- Narrative reference: [D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity](../Quantum/Algebra/ConditionalPolynomialRigidity.md)
- Narrative reference: [D5/S3/VertexAlgebra/LatticeFiniteNegativeGeneration](LatticeFiniteNegativeGeneration.md)
- Narrative reference: [D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero](LatticeHalfFockChargedLZero.md)
- Narrative reference: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](LatticeHalfFockFiniteCorrection.md)
- Narrative reference: [D5/S3/VertexAlgebra/LatticeSugawaraCurrents](LatticeSugawaraCurrents.md)

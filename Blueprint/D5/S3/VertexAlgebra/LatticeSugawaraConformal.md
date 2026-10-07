# Actual All-Charge Matrix Sugawara Modes

## Abstract

The actual matrix Sugawara coefficients satisfy Virasoro and generate charge-sensitive translation.

The actual quadratic field is one half the finite double sum of H(i,j) times normalMinusOne(neutralField(i),neutralField(j)). Its mode L(m) is the normalized coefficient at m+1. Let Gc be the complex cast of the integral Gram matrix and assume H Gc=Gc H=1. These are the only additional hypotheses for the conformal laws; the rank may be zero and every integral charge is included.

For a polynomial p, R is the largest frequency j+1 among the variables X(i,j) occurring in p, or zero when p is constant. For a finite-charge vector v, take the maximum over its sector support. Positive currents above R kill v. The normal summand N(i,j;k,m-k)v is supported in [min(0,m-R),R]. Each input, including each intermediate current image, has its own bound.

**Theorem 1.1 (exponential constant).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.exponential_constant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraConformal.exponential_constant` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every ordinary D and integral charge alpha, the degree-zero coefficient of the actual creationExponential(D,alpha) is one. The creation series has zero constant coefficient.

**Theorem 1.2 (translated smul).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.translated_smul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraConformal.translated_smul` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every ordinary D, integral charge alpha, complex scalar c and oscillator polynomial p, translatedPolynomial(D,alpha,c*p)=c*translatedPolynomial(D,alpha,p). This is the original algebra-homomorphism scalar action.

**Theorem 1.3 (Zero mode equals frequency Euler plus the lattice norm).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.sugawaraMode_zero_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraConformal.sugawaraMode_zero_single` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

On single(beta,p), L(0) is the oscillator frequency Euler derivation plus B(beta,beta)/2 times p. The inverse-Gram quadratic charge scalar equals this original lattice norm. The identity holds for every polynomial p. For an oscillator polynomial homogeneous of frequency degree r, the same mode acts by r+B(beta,beta)/2. This follows from the actual Euler derivation and is included in the generator contract.

**Theorem 1.4 (The Virasoro minus-one mode translates the genuine lattice generators).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.actual_conformal_generators`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraConformal.actual_conformal_generators` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The actual coefficient L(-1) equals T on all finite-charge vectors. On each charged ground state its value is single(beta,B_beta); its current commutators then determine its action on every oscillator polynomial. The contract combines the full Virasoro law and zero-mode formula with the actual T formula, vacuum annihilation, charged actualField covariance and neutral-current covariance, all for the same actual carrier and coefficients. Its final clause consumes sugawaraMode_weighted_homogeneous to give the eigenvalue r+B(beta,beta)/2 at every oscillator frequency degree r.

Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), gives the classical charged generators, translation and conformal construction. The finite normal-ordering and commutator architecture also follows Kalle Kytola's Apache-2.0 Sugawara.lean at revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The polynomial Fock carrier is not used to transfer these lattice identities.

The current-law helper in LatticeSugawaraCurrents directly reuses the frozen private declaration D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity.partials_commute. Its run_tac resolves that declaration's existing private Lean name and applies it inside the finite Gram-weighted sums; it does not reprove polynomial partial-derivative commutation. The sector scalar commutant proof in LatticeSugawaraVirasoro also directly uses the same frozen module's private eq_constant_of_partials_zero through run_tac.

These are conformal mode and generator identities. All-state field reconstruction and its vertex-algebra axioms remain separate obligations. Positive energy and finite-dimensional weight spaces require further lattice hypotheses and are not asserted.

Let D be any existing LatticeData: its rank is any natural number, its Gram matrix G is integral and symmetric, and its diagonal is even. Write L for the integral charge group Fin(rank) to Z, P for the complex polynomial algebra on variables X(i,j), and V for the finite-support functions L to P. The translation construction itself uses no positivity, nondegeneracy, unimodularity or positive-rank hypothesis. The Sugawara laws use the inverse-Gram hypotheses above.

The actual polynomial derivation D_osc sends X(i,j) to (j+1) X(i,j+1) and kills constants. Put B_beta=sum_i beta_i X(i,0). The endomorphism T sends single(beta,p) to single(beta,D_osc(p)+B_beta p), extending linearly over finite charge support. The vacuum single(0,1) is killed by T. In particular the multiplication term uses the charge of the sector on which T acts.

**Theorem 1.5 (The actual charged lattice fields satisfy translation covariance).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.actual_lattice_translation_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraConformal.actual_lattice_translation_covariance` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D, charge alpha and integer ordinary mode n, [T,Y_alpha[n]]=-n Y_alpha[n-1], as an equality of complex endomorphisms of V. The field is the existing actualField, with its lower-triangular cocycle, actual creation exponential and annihilation substitution. Arbitrary input charges and arbitrary oscillator polynomials remain quantified.

The raw coefficient theorem rawCoeff_translation proves [T,R_alpha(k)]=(k+1) R_alpha(k+1) for every integer exponent k. Ordinary modes are obtained from the actual field constructor by k=-n-1. This distinguishes the exponent and ordinary-mode shifts.

Coefficientwise oscillator derivation of the actual creation exponential is E'_alpha-B_alpha E_alpha. The proof uses its formal differential equation, coefficientwise Leibniz and zero constant term for the difference. Strong induction on the finite antidiagonal recurrence kills that difference. Thus D_osc C_t=(t+1) C_(t+1)-B_alpha C_t. For t=-1 the multiplier is zero, and for t<-1 both creation coefficients vanish; these integer cases are explicit.

Let Q_alpha(p;u) be the existing annihilation substitution X(i,j) to X(i,j)-B(alpha,e_i)u^(j+1). Polynomial induction proves Q_alpha(D_osc p)= D_osc Q_alpha(p)+u^2 partial_u Q_alpha(p) for every p. The charge transport is Q_alpha(B_beta)= B_beta-B(alpha,beta)u, and B_(alpha+beta)=B_alpha+B_beta.

A finite coefficient convolution applied to each polynomial separately includes its whole support. Its linearity uses zero coefficients outside the finite support; it imposes no bound from p on D_osc p or B_beta p. Monomial induction gives the reindexing d to d+1, including the zero derivative boundary. For b=B(alpha,beta) the annihilation term contributes -d, the changed charge contributes b, and the creation derivative contributes k-b+d+1. Their sum is k+1. This cancellation proves covariance on the actual carrier; a fixed-charge Fock operator cannot supply it.

The arbitrary-polynomial coefficient identity actual_creation_coefficient_transport identifies rawCoeff on every single(beta,p) with the prescribed rawSingle formula. The same cocycle scalar factors from both compositions. Extensionality on finitely supported charge functions extends the result to every actual carrier vector.

**Theorem 1.6 (The vacuum and both generating families share the constructed translation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.actual_translation_generators`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraConformal.actual_translation_generators` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D, the conjunction records the action on every single(beta,p), the zero vacuum action, all charged ordinary-mode commutators and all neutral-mode commutators. All statements concern the same actual T and V; the conjunction makes no all-state reconstruction claim.

**Theorem 1.7 (Every actual neutral current mode has the matching covariance).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.neutral_translation_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraConformal.neutral_translation_covariance` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every i in Fin(rank) and every integer m, [T,neutralMode(i,m)]=-m neutralMode(i,m-1), on all of V. Negative modes use the oscillator derivation of the multiplication variable. The zero mode is a scalar on each charge sector. Positive modes use the commutator of D_osc with polynomial partial derivatives. At m=1 the oscillator contribution is zero and differentiation of B_beta supplies exactly the zero-mode charge scalar. For m>1 the charge derivative vanishes and the oscillator commutator supplies the lower positive mode.

Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1, section 4.1, printed pages 8-9, equation (4.15), specifies the translation operator through the neutral commutator and charged ground-state action. Equation (4.12) supplies the lattice generator formula. This formalization verifies those generator translation identities on the existing actual polynomial and all-charge carrier. The degenerate and indefinite cases use no inverse Gram matrix.

These covariance laws supply the input required by the carrier-generic normalMinusOne_translation theorem and by a future all-charge state-field construction. They do not supply an all-state vertex algebra or Jacobi, the Monster realization, Moonshine, CFT, string theory or an AdS/CFT bridge.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.actual_conformal_generators`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.actual_lattice_translation_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.actual_translation_generators`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.exponential_constant`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.neutral_translation_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.sugawaraMode_zero_single`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraConformal.translated_smul`
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraVirasoro](LatticeSugawaraVirasoro.md)
